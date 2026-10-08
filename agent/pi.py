#!/usr/bin/env python3
import ctypes, fnmatch, functools, hashlib, json, os, re, selectors, shlex, shutil, signal, socket, stat, struct, subprocess, sys, tempfile, time, traceback, urllib.request
from pathlib import Path

HERE = Path(__file__).resolve().parent
RESULTS = HERE / "results"
_provider = lambda env: env.get("PI_PROVIDER", "neuralwatt")
_model_name = lambda env: env.get("PI_MODEL", {"anthropic": "claude-sonnet-5-5", "openai": "gpt-6-luna", "neuralwatt": "deepseek-v4.1-flash-flex",
                                          "local": env.get("PI_LOCAL_MODEL", "")}.get(_provider(env), ""))
_effort = lambda env: env.get("PI_EFFORT", "").strip()
_slc = lambda env: env.get("PI_SLC", str(HERE.parent / "_build/release/slc"))
_first_error = lambda env: env.get("PI_FIRST_ERROR", "yes")
PROVIDER, MODEL, EFFORT, SLC, FIRST_ERROR = _provider(os.environ), _model_name(os.environ), _effort(os.environ), _slc(os.environ), _first_error(os.environ)
MAX_TOKENS = int(os.environ["PI_MAX_TOKENS"]) if os.environ.get("PI_MAX_TOKENS") else None
_out_cap = lambda limit: min(c for c in (MAX_TOKENS, limit) if c) if MAX_TOKENS or limit else None
HTTP_TIMEOUT = int(os.environ.get("PI_HTTP_TIMEOUT", "1800"))
STREAM = os.environ.get("PI_STREAM", "1") not in ("0", "false", "")
MAX_TURNS = int(os.environ.get("PI_MAX_TURNS", "0"))
MAX_EMPTY = int(os.environ.get("PI_MAX_EMPTY", "3"))
CONTEXT = int(os.environ.get("PI_CONTEXT", "0"))
CONTEXT_STOP = float(os.environ.get("PI_CONTEXT_STOP", "20"))
REWRITE_STOP = float(os.environ.get("PI_REWRITE_STOP") or CONTEXT_STOP)
SESSION_TRIES = int(os.environ.get("PI_SESSION_TRIES", "3"))
REQUESTS_LOG = os.environ.get("PI_REQUESTS_LOG", "0") not in ("0", "false", "")
RUN_STATS = os.environ.get("PI_RUN_STATS", "1") not in ("0", "false", "")
SLC_TIMEOUT, BUILD_TIMEOUT, RUN_TIMEOUT = 60, 120, int(os.environ.get("PI_RUN_TIMEOUT", "10"))
GATE_PORT = int(os.environ.get("PI_GATE_PORT", "47219"))
MEM_MB = max(2048, os.sysconf("SC_PHYS_PAGES") * os.sysconf("SC_PAGE_SIZE") // 4 // 2**20)
MAX_WRITE, MAX_OUT, MAX_READ, MAX_RESULT = 8 * 1024 * 1024, 20000, 200000, 256 * 1024
MAX_KEPT_FAILURE, MAX_PROGRAM_OUTPUT = 1024 * 1024, 1024 * 1024
RUN_DIR = SANDBOX_ROOT = ROOT_FD = LOG_PATH = TRANSCRIPT = SESSION_ID = COMPILER = None
KEEP = {}
CARRY = []
SPENT = {}
_LOG_N = 0

SYSTEM = """You are an expert programmer working inside a sandbox directory. You read, write and edit files, and
compile and run programs with the `sl` tool. There is no shell; the only way to execute code is the `sl` tool.

All paths are relative to the sandbox root."""


class PathEscape(Exception):
    pass

_NOFOLLOW = os.O_RDONLY | os.O_NOFOLLOW | getattr(os, "O_CLOEXEC", 0)
_DIRFLAGS = _NOFOLLOW | os.O_DIRECTORY


def _rel_parts(user_path):
    if not user_path or os.path.isabs(user_path):
        raise PathEscape(f"{user_path!r}: absolute paths are not allowed")
    parts = [c for c in Path(user_path).parts if c not in ("", os.sep, ".")]
    if any(c == ".." or "\x00" in c for c in parts):
        raise PathEscape(f"{user_path!r}: '..' / NUL not allowed")
    return parts


def _walk_to_dir(dir_parts, *, create):
    dir_fd = os.open(".", _DIRFLAGS, dir_fd=ROOT_FD)
    try:
        for comp in dir_parts:
            try:
                nfd = os.open(comp, _DIRFLAGS, dir_fd=dir_fd)
            except FileNotFoundError:
                if not create:
                    raise
                os.mkdir(comp, 0o777, dir_fd=dir_fd)
                nfd = os.open(comp, _DIRFLAGS, dir_fd=dir_fd)
            except OSError as e:
                raise PathEscape(f"cannot enter {comp!r}: {e.strerror}") from None
            os.close(dir_fd)
            dir_fd = nfd
        return dir_fd
    except Exception:
        os.close(dir_fd)
        raise


def _open_in(user_path, flags, *, create):
    *dirs, name = _rel_parts(user_path) or [""]
    if not name:
        raise PathEscape("empty path")
    dfd = _walk_to_dir(dirs, create=create)
    try:
        return os.open(name, flags, 0o666, dir_fd=dfd)
    except OSError as e:
        raise PathEscape(f"{user_path!r}: {e.strerror}") from None
    finally:
        os.close(dfd)


def read_bytes(user_path):
    with os.fdopen(_open_in(user_path, _NOFOLLOW, create=False), "rb") as f:
        return f.read()


def write_bytes(user_path, data):
    if len(data) > MAX_WRITE:
        raise PathEscape(f"write of {len(data)} bytes exceeds cap ({MAX_WRITE})")
    name, old = os.path.normpath(user_path), _size(user_path)
    if KEEP.get(name) and len(data) > KEEP[name] and len(data) > old:
        raise ValueError(f"{name} would go from {old} to {len(data)} bytes{_cap(name)}")
    flags = os.O_WRONLY | os.O_CREAT | os.O_TRUNC | os.O_NOFOLLOW | getattr(os, "O_CLOEXEC", 0)
    with os.fdopen(_open_in(user_path, flags, create=True), "wb") as f:
        return f"{user_path}: {old} -> {f.write(data)} bytes{_cap(name)}"


def _cap(path):
    return f" (at most {KEEP[os.path.normpath(path)]})" if KEEP.get(os.path.normpath(path)) else ""


def _size(path):
    try:
        return len(read_bytes(path))
    except (OSError, PathEscape):
        return 0


def _sized(path, label=None):
    return f"{label or path}  {len(read_bytes(path))} bytes{_cap(path)}"


def list_dir(user_path="."):
    dfd = _walk_to_dir(_rel_parts(user_path), create=False)
    try:
        def suffix(nm):
            try:
                m = os.stat(nm, dir_fd=dfd, follow_symlinks=False).st_mode
            except OSError:
                return ""
            return "@" if stat.S_ISLNK(m) else "/" if stat.S_ISDIR(m) else ""
        return sorted((nm, suffix(nm)) for nm in os.listdir(dfd))
    finally:
        os.close(dfd)


def _tree(dfd, rel=""):
    for e in sorted(os.scandir(dfd), key=lambda e: e.name):
        r = os.path.join(rel, e.name)
        yield r, functools.partial(_read_at, dfd, e.name) if e.is_file(follow_symlinks=False) else None
        if e.is_dir(follow_symlinks=False):
            sub = os.open(e.name, _DIRFLAGS, dir_fd=dfd)
            try:
                yield from _tree(sub, r)
            finally:
                os.close(sub)


def _read_at(dfd, name):
    with os.fdopen(os.open(name, _NOFOLLOW, dir_fd=dfd), "rb") as f:
        return f.read()


def _walk(path):
    try:
        dfd = _walk_to_dir(_rel_parts(path or "."), create=False)
    except PathEscape:
        yield os.path.normpath(path), functools.partial(read_bytes, path)
        return
    try:
        yield from ((os.path.normpath(os.path.join(path, r)), read) for r, read in _tree(dfd))
    finally:
        os.close(dfd)


def _glob_match(pat, parts):
    if not pat:
        return not parts
    if pat[0] == "**":
        return any(_glob_match(pat[1:], parts[i:]) for i in range(len(parts) + 1))
    return bool(parts) and fnmatch.fnmatchcase(parts[0], pat[0]) and _glob_match(pat[1:], parts[1:])


def clip(s, cap=MAX_OUT):
    return s if len(s) <= cap else s[:cap] + f"\n... ({len(s) - cap} more chars cut)"


def read(path, offset=1, limit=2000):
    lines = read_bytes(path).decode("utf-8", "replace").splitlines()
    start, shown, room = max(offset, 1) - 1, [], MAX_READ
    for i, l in enumerate(lines[start:start + max(limit, 0)], start + 1):
        s = f"{i:6}\t{l}"
        if shown and len(s) > room:
            break
        shown.append(s if len(s) <= room else s[:room] + f" ... ({len(s) - room} more chars of line {i} cut)")
        room -= len(s) + 1
    rest = len(lines) - start - len(shown)
    return ("\n".join(shown) or f"(no lines; the file has {len(lines)})") + (
        f"\n... ({rest} more lines; read again with offset={start + len(shown) + 1})" if rest > 0 else "")


def write(path, content):
    return f"wrote {write_bytes(path, content.encode())}"


def edit(path, old_string, new_string, replace_all=False):
    if old_string == new_string:
        return "error: old_string and new_string are the same"
    text = read_bytes(path).decode("utf-8", "replace")
    if not old_string and text:
        return "error: an empty old_string only matches an empty file"
    n = text.count(old_string)
    if n == 0 or n > 1 and not replace_all:
        return f"error: found {n} matches, need {'at least' if replace_all else 'exactly'} 1" + (
            "; add more context to pick one, or pass replace_all to replace them all" if n else "")
    return f"edited {write_bytes(path, text.replace(old_string, new_string).encode())}" + (f" ({n} replacements)" if n > 1 else "")


def delete(path):
    *dirs, name = _rel_parts(path) or [""]
    if not name:
        raise PathEscape("the sandbox root cannot be deleted")
    if (rel := os.path.normpath(path)) in KEEP:
        raise ValueError(f"`{rel}` is a kept file and cannot be deleted")
    dfd = _walk_to_dir(dirs, create=False)
    try:
        if stat.S_ISDIR(os.stat(name, dir_fd=dfd, follow_symlinks=False).st_mode):
            os.rmdir(name, dir_fd=dfd)
        else:
            os.unlink(name, dir_fd=dfd)
    except OSError as e:
        raise PathEscape(f"{path!r}: {e.strerror}") from None
    finally:
        os.close(dfd)
    return f"deleted {rel}"


def ls(path=".", within=None):
    path = path or "."
    try:
        entries = list_dir(path)
    except PathEscape:
        return _sized(path)
    rel = lambda nm: os.path.normpath(os.path.join(path, nm))
    return "\n".join(nm + suffix if suffix else _sized(rel(nm), nm)
                     for nm, suffix in entries if within is None or rel(nm) in within) or "(empty)"


def grep(pattern, path=".", within=None):
    rx, hits = re.compile(pattern), []
    for rel, read in _walk(path):
        if read and (within is None or rel in within):
            try:
                hits += [f"{rel}:{n}: {l[:200]}" for n, l in enumerate(read().decode("utf-8", "replace").splitlines(), 1) if rx.search(l)]
            except (OSError, PathEscape):
                pass
    return "\n".join(hits[:200]) or "(no matches)"


def find(glob, path="."):
    top = len(_rel_parts(path or "."))
    return "\n".join([rel for rel, _ in _walk(path) if _glob_match(["**", *Path(glob).parts], Path(rel).parts[top:])][:200]) or "(none)"


@functools.cache
def _ocamlopt():
    show = ["ocamlfind", "ocamlopt", "-only-show", "-package", "zarith,unix", "-linkpkg", "p.ml", "-o", "p"]
    return shlex.split(subprocess.run(show, capture_output=True, text=True, check=True).stdout)


def _spawn_exec_limited(cmd, env):
    libc = ctypes.CDLL(None, use_errno=True)
    strs = lambda xs: (ctypes.c_char_p * (len(xs) + 1))(*[str(x).encode() for x in xs], None)
    argv, envp = strs(cmd), strs([f"{k}={v}" for k, v in env.items()])
    attr, acts = ctypes.c_void_p(), ctypes.c_void_p()

    def exec_():
        libc.posix_spawnattr_init(ctypes.byref(attr))
        libc.posix_spawnattr_setflags(ctypes.byref(attr), ctypes.c_short(0x0040 | 0x4000))
        libc.posix_spawnattr_setjetsam_ext(ctypes.byref(attr), ctypes.c_short(0x800C - 0x10000), 0, MEM_MB, MEM_MB)
        libc.posix_spawn_file_actions_init(ctypes.byref(acts))
        for fd in (0, 1, 2):
            libc.posix_spawn_file_actions_addinherit_np(ctypes.byref(acts), fd)
        e = libc.posix_spawnp(None, argv[0], ctypes.byref(acts), ctypes.byref(attr), argv, envp)
        os.write(2, f"posix_spawnp {cmd[0]}: {os.strerror(e)}\n".encode())
        os._exit(127)
    return exec_


def _group_mb_darwin(pgid):
    libc, pids = ctypes.CDLL(None), (ctypes.c_int * 4096)()
    n = libc.proc_listpids(2, pgid, pids, ctypes.sizeof(pids)) // ctypes.sizeof(ctypes.c_int)
    usage, total = ctypes.create_string_buffer(256), 0
    for pid in pids[:n]:
        if pid and libc.proc_pid_rusage(pid, 0, usage) == 0:
            total += struct.unpack_from("Q", usage, 72)[0]
    return total >> 20


def _group_mb_linux(pgid):
    total = 0
    for p in Path("/proc").glob("[0-9]*/stat"):
        try:
            fields = p.read_text().rsplit(")", 1)[1].split()
            total += int(fields[21]) * os.sysconf("SC_PAGE_SIZE") if int(fields[2]) == pgid else 0
        except (OSError, IndexError, ValueError):
            pass
    return total >> 20


def _limited_linux(cmd, env):
    scope = ["/usr/bin/systemd-run", "--user", "--scope", "--quiet", "--collect", "-p", f"MemoryMax={MEM_MB}M", "-p", "MemorySwapMax=0", "--"]
    return [*scope, "/usr/bin/env", "-i", *(f"{k}={v}" for k, v in env.items()), *cmd], \
        {k: os.environ[k] for k in ("XDG_RUNTIME_DIR", "DBUS_SESSION_BUS_ADDRESS") if k in os.environ}, None


LINUX = sys.platform == "linux"
_group_mb = _group_mb_linux if LINUX else _group_mb_darwin
_limited = _limited_linux if LINUX else lambda cmd, env: (cmd, env, _spawn_exec_limited(cmd, env))


# HACK: a Popen whose reaping of the child also records the child's resource usage, which `_stats` reports.
# Popen exposes no rusage, so this overrides `Popen._try_wait`, a private method of CPython's subprocess module
# (POSIX only); as far as we can tell, CPython 3.12 calls it from `wait()`, including the `wait()` inside
# `communicate()`, and it returns the same (pid, status) as `os.waitpid`, which `os.wait4` also returns.
# If a Python upgrade renames this method, or reaps the child some other way (as `Popen.poll()` already does,
# bypassing it), the override is silently skipped: `rusage` stays None and `sl` just stops printing the
# "(... s wall clock, ... s CPU, ... MB peak memory)" stats, with no error. If those stats vanish, look here
# first, and compare against the `_try_wait` in the installed Python's Lib/subprocess.py.
class _Popen(subprocess.Popen):
    rusage = None

    def _try_wait(self, wait_flags):
        try:
            pid, sts, rusage = os.wait4(self.pid, wait_flags)
        except ChildProcessError:
            return self.pid, 0
        self.rusage = rusage if pid else None
        return pid, sts


def _proc(cmd, cwd, timeout, stdin="", env=None):
    cmd, env, preexec = _limited(cmd, os.environ if env is None else env)
    with _Popen(cmd, cwd=cwd, env=env, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                start_new_session=True, preexec_fn=preexec) as p:
        deadline, data, why = time.monotonic() + timeout, stdin.encode(), None
        try:
            while why is None:
                try:
                    out, err = p.communicate(data, timeout=min(1, max(0, deadline - time.monotonic())))
                    break
                except subprocess.TimeoutExpired:
                    data = None
                    if time.monotonic() >= deadline:
                        why = f"timed out after {timeout}s"
                    elif (mb := _group_mb(p.pid)) > MEM_MB:
                        why = f"was killed after its processes used {mb} MB, over the {MEM_MB} MB memory limit"
            else:
                _killpg(p.pid)
                try:
                    out, err = p.communicate(timeout=1)
                except subprocess.TimeoutExpired as e:
                    out, err = e.output or b"", e.stderr or b""
            if why is None and p.returncode == -signal.SIGKILL:
                why = f"was killed (SIGKILL); the memory limit is {MEM_MB} MB"
            done = subprocess.CompletedProcess(cmd, p.returncode, out, err)
            done.rusage = p.rusage
            return why, done
        finally:
            _killpg(p.pid)


def _killpg(pgid):
    try:
        os.killpg(pgid, signal.SIGKILL)
    except ProcessLookupError:
        pass


def _text(b):
    return b.decode("utf-8", "replace")


def _shown(capture, ext, data):
    if not capture:
        return clip(_text(data))
    name = f"{capture}.{ext}"
    write_bytes(name, data)
    lines = _text(data).splitlines()
    shown = lines if len(lines) <= 10 else lines[:5] + [f"... ({len(lines) - 10} more lines)"] + lines[-5:]
    return clip("\n".join([f"({name}, {len(data)} bytes)", *shown]))


def sl(paths, stdin="", args=(), capture=None, gc_stats=False, first_error=FIRST_ERROR == "yes"):
    if isinstance(paths, str):
        paths = [paths] if paths else []
    if not paths:
        raise ValueError("`paths` must name at least one file")
    if capture and any(os.path.normpath(f"{capture}.{ext}") in KEEP for ext in ("slc.err", "out", "err")):
        raise ValueError("`capture` cannot name a kept file")
    with _turn(), tempfile.TemporaryDirectory(prefix="pi-sl-") as tmp:
        src = Path(tmp, "src")
        names = []
        for p in paths:
            name = "/".join(_rel_parts(p))
            if name.startswith("-"):
                raise PathEscape(f"{p!r}: a path given to `sl` cannot start with '-'")
            (src / name).parent.mkdir(parents=True, exist_ok=True)
            (src / name).write_bytes(read_bytes(p))
            names.append(name)
        why, c = _proc([COMPILER, *(["--first-error"] if first_error else []), "--confine-dir", ".", "--confine-output-bytes", str(MAX_PROGRAM_OUTPUT), "--no-env", "--no-shape-note", *names], src, SLC_TIMEOUT, env={})
        warnings = _shown(capture, "slc.err", c.stderr)
        if why or c.returncode:
            return f"compile: {why or f'failed (exit {c.returncode})'}\n{warnings}"
        Path(tmp, "p.ml").write_bytes(c.stdout)
        why, b = _proc(_ocamlopt(), tmp, BUILD_TIMEOUT, env={"PATH": os.environ["PATH"], "TMPDIR": tmp})
        if why or b.returncode:
            why = why or f"exited {b.returncode}"
            ml = Path(tmp, "p.ml")
            kept = RUN_DIR / f"build-failure-{time.time():.0f}.ml"
            if ml.stat().st_size <= MAX_KEPT_FAILURE:
                shutil.copy(ml, kept)
            with open(RUN_DIR / "build-failures.log", "a") as f:
                f.write(f"ocamlopt {why}; p.ml was {ml.stat().st_size} bytes, "
                        + (f"kept as {kept.name}\n" if kept.exists() else "not kept\n")
                        + _text(b.stdout + b.stderr))
            return f"internal error: building the compiler's output: ocamlopt {why}; this is not your program's fault"
        t0 = time.monotonic()
        why, r = _proc([str(Path(tmp, "p")), *map(str, args)], SANDBOX_ROOT, RUN_TIMEOUT, stdin,
                       env={"OCAMLRUNPARAM": "v=0x400"} if gc_stats else {})
        head = f"compile: ok, with warnings\n{warnings}" if c.stderr.strip() else "compile: ok, no warnings"
        return f"{head}\nrun: {why or f'exit {r.returncode}'}{_stats(time.monotonic() - t0, r.rusage)}\n--- stdout ---\n{_shown(capture, "out", r.stdout)}\n--- stderr ---\n{_shown(capture, "err", r.stderr)}"


def _turn():
    for _ in range(50):
        try:
            s = socket.create_connection(("127.0.0.1", GATE_PORT))
            s.sendall(f"{RUN_DIR.parent.name}\n".encode())
            if s.recv(1) == b"g":
                return s
            s.close()
        except ConnectionError:
            subprocess.Popen([sys.executable, __file__, "--gate"], start_new_session=True,
                             stdin=subprocess.DEVNULL, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
            time.sleep(0.2)
    sys.exit(f"cannot reach or start the `sl` organizer on port {GATE_PORT}")


def gate():
    srv, sel, ids, last, holder = socket.create_server(("127.0.0.1", GATE_PORT)), selectors.DefaultSelector(), {}, {}, None
    sel.register(srv, selectors.EVENT_READ)
    while True:
        for key, _ in sel.select():
            if (s := key.fileobj) is srv:
                sel.register(srv.accept()[0], selectors.EVENT_READ)
            elif data := s.recv(4096):
                ids[s] = ids.get(s, b"") + data
            else:
                sel.unregister(s)
                s.close()
                ids.pop(s, None)
                holder = None if s is holder else holder
        if holder is None and (waiting := [s for s, i in ids.items() if i.endswith(b"\n")]):
            holder = min(waiting, key=lambda s: last.get(ids[s], 0))
            last[ids[holder]] = time.monotonic()
            try:
                holder.send(b"g")
            except OSError:
                pass


def _stats(wall, ru):
    if not RUN_STATS or ru is None:
        return ""
    # ru_maxrss is in KiB on Linux but in bytes on macOS (see getrusage(2) on each).
    # The figures are the program's only if `_proc`'s direct child is the program itself, i.e. if everything
    # `_limited` puts in front of it (systemd-run --scope, env, or the macOS posix_spawn exec) replaces itself
    # with the program in place; we believe it does, but this is unchecked on Linux. If a wrapper ever forks
    # and waits instead, these numbers become the wrapper's (likely still including the reaped program's CPU).
    peak = ru.ru_maxrss << 10 if LINUX else ru.ru_maxrss
    return f" ({wall:.2f} s wall clock, {ru.ru_utime + ru.ru_stime:.2f} s CPU, {peak >> 20} MB peak memory)"


def done(summary=""):
    return summary or "done"


FIRST_ERROR_NOTES = {
    "yes": "The compiler reports only its first error.",
    "no": "The compiler reports every error it finds; errors after the first are best-effort and may be unreliable.",
    "choose": "By default the compiler reports every error it finds; with `first_error` set to true, only its first. "
              "Errors after the first are best-effort and may be unreliable.",
}
STR, STRS, INT, BOOL = {"type": "string"}, {"type": "array", "items": {"type": "string"}}, {"type": "integer"}, {"type": "boolean"}
TOOLS = {
    "read": (read, "Read a file, with line numbers. `offset` is the first line to show (from 1), `limit` how many (default 2000).",
             {"path": STR, "offset": INT, "limit": INT}, ["path"]),
    "write": (write, "Write a file", {"path": STR, "content": STR}, ["path", "content"]),
    "edit": (edit, "Replace exactly one occurrence of old_string with new_string, or every occurrence with `replace_all`",
             {"path": STR, "old_string": STR, "new_string": STR, "replace_all": BOOL}, ["path", "old_string", "new_string"]),
    "delete": (delete, "Delete a file or an empty directory. Kept files cannot be deleted.",
               {"path": STR}, ["path"]),
    "ls": (ls, "List a directory, or a single file, with each file's size in bytes (and its cap, for a kept file); "
               "a trailing `/` marks a directory, `@` a symlink", {"path": STR}, []),
    "grep": (grep, "Regex search file contents", {"pattern": STR, "path": STR}, ["pattern"]),
    "find": (find, "Find files by glob", {"glob": STR, "path": STR}, ["glob"]),
    "sl": (sl, "Compile the SL source files at `paths` (read in order, sharing one scope) and, if they compile, "
               "run the program with the sandbox as its working directory, feeding it `stdin` and passing it `args`. "
               "Returns the compiler's messages, then the program's exit code, stdout and stderr. With `capture`, these go to "
               "`{capture}.slc.err`, `{capture}.out` and `{capture}.err`, and only their sizes and first and last lines are shown. "
               "With `gc_stats`, a program that exits normally ends its stderr with the OCaml runtime's garbage collector totals, "
               "among them `allocated_words`: the words (8 bytes each) it allocated over the whole run. " + FIRST_ERROR_NOTES.get(FIRST_ERROR, ""),
           {"paths": STRS, "stdin": STR, "args": STRS, "capture": STR, "gc_stats": BOOL}
           | ({"first_error": BOOL} if FIRST_ERROR == "choose" else {}), ["paths"]),
    "done": (done, "The experiment phase ends when its budget runs out or when you call `done`. Then the rewrite phase continues this conversation with a fresh "
                   "budget of its own, allowing only {allowed}, and `done`; calling `done` there ends the session. Pass a one-line summary.",
             {"summary": STR}, []),
}
PARAMS = {n: {"type": "object", "properties": props, "required": req} for n, (_, _, props, req) in TOOLS.items()}


def _check(name, args):
    if name not in TOOLS:
        raise ValueError(f"there is no tool `{name}`; the tools are {', '.join(TOOLS)}")
    props, req = TOOLS[name][2], TOOLS[name][3]
    if set(args) - set(props) or set(req) - set(args):
        raise ValueError(f"`{name}` takes {', '.join(props)}" + (f" ({', '.join(req)} required)" if req and req != list(props) else "")
                         + f", but got {', '.join(args) or 'no arguments'}, so the call was not run")
    for k, v in args.items():
        if props[k] is BOOL and not isinstance(v, bool):
            raise ValueError(f"`{k}` must be true or false")


def _ts():
    return time.strftime('%H:%M:%S')


def _iso(t):
    return time.strftime("%Y-%m-%dT%H:%M:%S", time.gmtime(t)) + f".{int(t % 1 * 1000):03}Z"


def _say(text):
    print(f"{_ts()} {text}", file=sys.stderr)


def _log(path, text):
    if path is None:
        return
    try:
        with open(path, "a", encoding="utf-8") as f:
            f.write(text)
    except Exception:
        pass


def _banner(extra=""):
    return f"\n{'=' * 78}\n#{_LOG_N}  {time.strftime('%Y-%m-%d %H:%M:%S')}  provider={PROVIDER} model={MODEL}{extra}\n{'=' * 78}\n"


class ThinkLog:
    def __init__(self):
        self.f, self.chars, self.flushed = None, 0, 0.0

    def write(self, text):
        if not text:
            return
        try:
            if self.f is None:
                self.f = open(TRANSCRIPT, "a", encoding="utf-8")
                self.f.write(f"\n--- thinking (request #{_LOG_N}) {_ts()} ---\n")
            self.f.write(text)
            self.chars += len(text)
            if time.time() - self.flushed >= 1.0:
                self.f.flush()
                self.flushed = time.time()
        except Exception:
            self.f = None

    def close(self):
        try:
            if self.f is not None:
                self.f.write(f"\n--- end of thinking ({self.chars} chars) {_ts()} ---\n")
                self.f.close()
        except Exception:
            pass
        self.f = None


RUNAWAY_WINDOW, RUNAWAY_PERIOD = 4000, 64


def _streamed_text(d):
    if (d.get("type") or "").endswith("_text.delta"):
        return d.get("delta") or ""
    return "".join((ch.get("delta") or {}).get(k) or "" for ch in d.get("choices") or [] for k in ("content", "reasoning", "reasoning_content"))


def _sse(r):
    tail, chars = "", 0
    for raw in r:
        line = raw.decode("utf-8", "replace").strip()
        if line.startswith((": cost ", ": energy ")):
            key, _, rest = line[2:].partition(" ")
            try:
                yield {key: json.loads(rest)}
            except ValueError:
                pass
            continue
        if not line.startswith("data: "):
            continue
        if line[6:] == "[DONE]":
            return
        try:
            d = json.loads(line[6:])
        except ValueError:
            continue
        piece = _streamed_text(d)
        tail, chars = (tail + piece)[-RUNAWAY_WINDOW:], chars + len(piece)
        if piece and len(tail) == RUNAWAY_WINDOW and any(tail[p:] == tail[:-p] for p in range(1, RUNAWAY_PERIOD + 1)):
            note = f"[runaway repetition: the reply was cut off after {chars:,} characters]"
            _say(note)
            _log(TRANSCRIPT, f"\n{note}\n")
            yield {"type": "runaway"}
            return
        yield d


def assemble_responses(r):
    think, reply = ThinkLog(), None
    try:
        for d in _sse(r):
            if d.get("type") == "response.reasoning_summary_text.delta":
                think.write(d.get("delta"))
            elif d.get("type") in ("response.completed", "response.incomplete", "response.failed"):
                reply = d["response"]
            elif d.get("type") == "runaway":
                reply = {"output": [], "status": "incomplete", "incomplete_details": {"reason": "runaway repetition"}}
    finally:
        think.close()
    if reply is None:
        raise ConnectionError("the response stream ended without a final response")
    return reply


def assemble_sse(r):
    content, reasoning, calls = [], [], {}
    finish, extra = None, {}
    think = ThinkLog()
    try:
        for d in _sse(r):
            extra.update({k: d[k] for k in ("usage", "cost", "energy") if d.get(k)})
            finish = "runaway repetition" if d.get("type") == "runaway" else finish
            for ch in d.get("choices") or []:
                finish = ch.get("finish_reason") or finish
                delta = ch.get("delta") or {}
                if delta.get("content"):
                    content.append(delta["content"])
                for key in ("reasoning", "reasoning_content"):
                    if delta.get(key):
                        reasoning.append(delta[key])
                        think.write(delta[key])
                for tc in delta.get("tool_calls") or []:
                    slot = calls.setdefault(tc.get("index", 0), {"id": None, "type": "function", "function": {"name": "", "arguments": ""}})
                    slot["id"] = tc.get("id") or slot["id"]
                    fn = tc.get("function") or {}
                    slot["function"]["name"] = fn.get("name") or slot["function"]["name"]
                    slot["function"]["arguments"] += fn.get("arguments") or ""
    finally:
        think.close()
    msg = {"role": "assistant", "content": "".join(content)}
    if reasoning:
        msg["reasoning"] = "".join(reasoning)
    if calls:
        msg["tool_calls"] = [dict(calls[k], id=calls[k]["id"] or f"call_{i}") for i, k in enumerate(sorted(calls))]
    return {"choices": [{"message": msg, "finish_reason": finish}], **extra}


def post(url, body, headers, tries=int(os.environ.get("PI_HTTP_TRIES", "6")), stream=None):
    global _LOG_N
    for attempt in range(tries):
        req = urllib.request.Request(url, data=json.dumps(body).encode(), headers={"content-type": "application/json", **headers})
        _LOG_N += 1
        _log(LOG_PATH, _banner(f"  (retry {attempt})" if attempt else "") + f"{url}\n---- request ----\n{json.dumps(body, indent=2, ensure_ascii=False)}\n")
        t0 = time.time()
        try:
            with urllib.request.urlopen(req, timeout=HTTP_TIMEOUT) as r:
                reply = stream(r) if stream else json.loads(r.read())
            _log(LOG_PATH, f"---- response {_ts()} ({time.time() - t0:.1f}s) ----\n{json.dumps(reply, indent=2, ensure_ascii=False)}\n")
            return reply
        except urllib.error.HTTPError as e:
            detail = e.read().decode()[:500]
            _log(LOG_PATH, f"---- error {_ts()} ({time.time() - t0:.1f}s) ----\nHTTP {e.code} {e.reason}: {detail}\n")
            if e.code not in (408, 409, 429, 500, 502, 503, 504, 520, 522, 524) or attempt == tries - 1:
                sys.exit(f"{e.code} {e.reason}: {detail}")
        except (urllib.error.URLError, TimeoutError, ConnectionError) as e:
            _log(LOG_PATH, f"---- error {_ts()} ({time.time() - t0:.1f}s) ----\nnetwork: {e}\n")
            if attempt == tries - 1:
                sys.exit(f"network error after {tries} tries: {e}")
        _say(f"[retry {attempt + 1}/{tries - 1} in {2 ** attempt}s]")
        time.sleep(2 ** attempt)


def _fetch(url, headers):
    try:
        with urllib.request.urlopen(urllib.request.Request(url, headers=headers), timeout=30) as r:
            return json.load(r)
    except Exception:
        return {}


class Anthropic:
    base = "https://api.anthropic.com/v1"
    _model = None

    def auth(self):
        return {"x-api-key": os.environ["ANTHROPIC_API_KEY"], "anthropic-version": "2023-06-01"}

    def model(self):
        if self._model is None:
            self.__class__._model = _fetch(f"{self.base}/models/{MODEL}", self.auth())
        return self._model

    def window(self):
        return self.model().get("max_input_tokens")

    def cap(self):
        return _out_cap(self.model().get("max_tokens")) or 65536

    def truncated(self, reply):
        return reply.get("stop_reason") == "max_tokens"

    def send(self, messages):
        return post(self.base + "/messages", {
            "model": MODEL, "max_tokens": self.cap(), "system": SYSTEM,
            "tools": [{"name": n, "description": d.replace("{allowed}", _allowed(caps=True)), "input_schema": PARAMS[n]} for n, (_, d, _, _) in TOOLS.items()],
            "messages": messages, "cache_control": {"type": "ephemeral"},
            **({"thinking": {"type": "adaptive", "display": "summarized"}}
               if ((self.model().get("capabilities") or {}).get("thinking") or {}).get("types", {}).get("adaptive", {}).get("supported") else {}),
            **({"output_config": {"effort": EFFORT}} if EFFORT else {}),
        }, self.auth())

    def parse(self, reply):
        blocks, think = reply["content"], ThinkLog()
        for b in blocks:
            think.write(b.get("thinking"))
        think.close()
        calls = [{"id": b["id"], "name": b["name"], "input": b["input"]} for b in blocks if b["type"] == "tool_use"]
        return {"role": "assistant", "content": blocks}, "".join(b["text"] for b in blocks if b["type"] == "text"), calls

    def results(self, calls, outs):
        return [{"role": "user", "content": [{"type": "tool_result", "tool_use_id": c["id"], "content": o} for c, o in zip(calls, outs)]}]


class OpenAICompat:
    base = "https://api.neuralwatt.com/v1"
    key_env = "NEURALWATT_API_KEY"
    _model = None

    def auth(self):
        return {"authorization": f"Bearer {os.environ[self.key_env]}"}

    def model(self):
        if self._model is None:
            self.__class__._model = next((m for m in _fetch(self.base + "/models", self.auth()).get("data") or [] if m.get("id") == MODEL), {})
        return self._model

    def limit(self, key):
        return ((self.model().get("metadata") or {}).get("limits") or {}).get(key)

    def cap(self):
        return _out_cap(self.limit("max_output_tokens"))

    def truncated(self, reply):
        return reply["choices"][0].get("finish_reason") == "length"

    def window(self):
        return self.limit("max_context_length") or self.model().get("max_model_len")

    def send(self, messages):
        body = {
            "model": MODEL, **({"max_tokens": self.cap()} if self.cap() else {}),
            "tools": [{"type": "function", "function": {"name": n, "description": d.replace("{allowed}", _allowed(caps=True)), "parameters": PARAMS[n]}} for n, (_, d, _, _) in TOOLS.items()],
            "messages": [{"role": "system", "content": SYSTEM}] + messages,
            "user": SESSION_ID,
        }
        if EFFORT:
            body["reasoning_effort"] = EFFORT
        if STREAM:
            body.update(stream=True, stream_options={"include_usage": True})
        return post(self.base + "/chat/completions", body, {**self.auth(), "x-nw-conversation-id": SESSION_ID}, stream=assemble_sse if STREAM else None)

    def parse(self, reply):
        msg = reply["choices"][0]["message"]
        return msg, msg.get("content") or "", [_call(c["id"], c["function"]) for c in msg.get("tool_calls") or []]

    def results(self, calls, outs):
        return [{"role": "tool", "tool_call_id": c["id"], "content": o} for c, o in zip(calls, outs)]


def _call(call_id, fn):
    try:
        return {"id": call_id, "name": fn["name"], "input": json.loads(fn["arguments"] or "{}")}
    except ValueError:
        bad, fn["arguments"] = fn["arguments"], "{}"
        return {"id": call_id, "name": fn["name"], "input": {}, "bad": bad}


class OpenAI(OpenAICompat):
    base, key_env, _model = "https://api.openai.com/v1", "OPENAI_API_KEY", None
    windows = {"gpt-6-astra": 1_050_000, "gpt-6-sol": 1_050_000, "gpt-6-luna": 1_050_000, "gpt-6.1-sol": 1_050_000}

    def window(self):
        return self.windows.get(MODEL)

    def cap(self):
        return MAX_TOKENS

    def truncated(self, reply):
        return reply.get("status") == "incomplete" and (reply.get("incomplete_details") or {}).get("reason") == "max_output_tokens"

    def send(self, messages):
        return post(self.base + "/responses", {
            "model": MODEL, **({"max_output_tokens": MAX_TOKENS} if MAX_TOKENS else {}), "instructions": SYSTEM,
            "tools": [{"type": "function", "name": n, "description": d.replace("{allowed}", _allowed(caps=True)), "parameters": PARAMS[n]} for n, (_, d, _, _) in TOOLS.items()],
            "input": [item for m in messages for item in (m if isinstance(m, list) else [m])],
            "reasoning": {"summary": "auto", **({"effort": EFFORT} if EFFORT else {})},
            "store": False, "include": ["reasoning.encrypted_content"], "stream": STREAM,
        }, self.auth(), stream=assemble_responses if STREAM else None)

    def parse(self, reply):
        items = reply["output"]
        text = "".join(p.get("text", "") for i in items if i["type"] == "message" for p in i["content"])
        return items, text, [_call(i["call_id"], i) for i in items if i["type"] == "function_call"]

    def results(self, calls, outs):
        return [{"type": "function_call_output", "call_id": c["id"], "output": o} for c, o in zip(calls, outs)]


class Local(OpenAICompat):
    base = os.environ.get("PI_LOCAL_URL", "http://localhost:8080/v1").rstrip("/")
    key_env = "PI_LOCAL_API_KEY"
    _model = None

    def auth(self):
        key = os.environ.get(self.key_env)
        return {"authorization": f"Bearer {key}"} if key else {}

    def parse(self, reply):
        msg, text, calls = super().parse(reply)
        return dict({k: v for k, v in msg.items() if v is not None}, role="assistant", content=text or ""), text, calls


ADAPTERS = {"anthropic": Anthropic, "openai": OpenAI, "neuralwatt": OpenAICompat, "local": Local}
CACHE_MIN = 4096
GPT_LONG, HAIKU_LONG = (272_000, 2, 1.5), (100_000, 5, 5)
PRICES = {  # $/MTok: input, cached read, 5-minute cache write, output[, (prompt tokens above which, input and output multipliers)]
    "gpt-6-luna": (0.10, 0.01, 0.125, 0.50, GPT_LONG), "gpt-6-sol": (2.00, 0.20, 2.50, 10.00, GPT_LONG),
    "gpt-6.1-sol": (2.00, 0.10, 2.50, 10.00, GPT_LONG), "gpt-6-astra": (10.00, 1.00, 12.50, 50.00, GPT_LONG),
    "claude-fable-5-1": (10.00, 0.25, 12.50, 50.00), "claude-opus-5-5": (4.00, 0.20, 5.00, 20.00),
    "claude-sonnet-5-5": (2.00, 0.10, 2.50, 10.00), "claude-haiku-5-5": (0.10, 0.01, 0.125, 0.50, HAIKU_LONG),
    "claude-haiku-4-5": (1.00, 0.10, 1.25, 5.00),
}


def _prompt(usage):
    details = usage.get("prompt_tokens_details") or usage.get("input_tokens_details") or {}
    cached = details.get("cached_tokens", usage.get("cache_read_input_tokens"))
    total = usage.get("prompt_tokens") or sum(usage.get(k) or 0 for k in ("input_tokens", "cache_read_input_tokens", "cache_creation_input_tokens"))
    return total, cached


def _priced(usage):
    p, (total, _) = PRICES[MODEL], _prompt(usage)
    details = usage.get("input_tokens_details") or {}
    read = details.get("cached_tokens", usage.get("cache_read_input_tokens")) or 0
    write = details.get("cache_write_tokens", usage.get("cache_creation_input_tokens")) or 0
    above, i, o = p[4] if len(p) > 4 else (0, 1, 1)
    i, o = (i, o) if total > above else (1, 1)
    return (((total - read - write) * p[0] + read * p[1] + write * p[2]) * i + (usage.get("output_tokens") or 0) * p[3] * o) / 1e6


def _spend(reply):
    cost = (reply.get("cost") or {}).get("request_cost_usd")
    if cost is None and MODEL in PRICES and reply.get("usage"):
        cost = _priced(reply["usage"])
    for key, value in (("cost", cost), ("energy", (reply.get("energy") or {}).get("energy_joules"))):
        if value is not None:
            SPENT[key] = SPENT.get(key, 0) + value
    return (f", ${SPENT['cost']:.6f}" if "cost" in SPENT else "") + (f", {SPENT['energy']:,.0f} J" if "energy" in SPENT else "")


def _context(reply, window, prev_prompt, prev_used):
    usage, spent = reply.get("usage"), _spend(reply)
    if not usage:
        return prev_used, prev_prompt
    n = usage.get("total_tokens") or sum(usage.get(k) or 0 for k in
                                         ("input_tokens", "cache_read_input_tokens", "cache_creation_input_tokens", "output_tokens"))
    prompt, cached = _prompt(usage)
    _log(TRANSCRIPT, f"\n[usage: {json.dumps(usage)}]\n")
    lines = [f"[context: {n:,}" + (f" / {window:,} ({100 * n / window:.1f}%)" if window else "")
             + (f", {100 * cached / prompt:.0f}% of the prompt cached" if cached is not None and prompt else "")
             + (f"{spent} spent this session]" if spent else "]")]
    if cached is None and prev_prompt == 0:
        lines.append("[cache warning: the provider reports no cached-token count, so caching cannot be checked]")
    elif cached is not None and prev_prompt >= CACHE_MIN and cached < prev_prompt / 2:
        lines.append(f"[cache warning: only {cached:,} of {prompt:,} prompt tokens were cached, "
                     f"though the previous request's {prev_prompt:,}-token prompt could have been]")
    for line in lines:
        _say(line)
        _log(TRANSCRIPT, f"\n{line}\n")
    return n, prompt


REWRITE_TOOLS, SCOPED_TOOLS = ("read", "write", "edit", "grep", "ls"), ("grep", "ls")
REWRITE_NAMES = ", ".join(f"`{t}`" for t in REWRITE_TOOLS[:-1]) + f" and `{REWRITE_TOOLS[-1]}`"


def _allowed(caps=False):
    return f"{REWRITE_NAMES} on " + ", ".join(k + (_cap(k) if caps else "") for k in sorted(KEEP))


def _over():
    return [(k, cap, size) for k, cap in sorted(KEEP.items()) if cap and (size := _size(k)) > cap]


def _kept_sizes():
    return ", ".join(f"{k} ({_size(k)} bytes" + (f", at most {cap})" if cap else ")") for k, cap in sorted(KEEP.items()))


def run(prompt):
    api = ADAPTERS[PROVIDER]()
    messages, empty, prompt_tokens = [{"role": "user", "content": prompt}], 0, 0
    window = CONTEXT or api.window()
    turns, budget = MAX_TURNS or (1000 if window else 200), lambda stop: int(window * stop / 100) if window else None
    tokens = budget(CONTEXT_STOP)
    phase, turn, start, used = "experiment", 0, 0, 0
    ok = lambda c: c["name"] == "done" or c["name"] in REWRITE_TOOLS and (
        "path" not in c["input"] or os.path.normpath(str(c["input"]["path"])) in KEEP)

    def rewrite():
        nonlocal phase, turn, start, tokens
        phase, turn, start, tokens = "rewrite", 0, used, budget(REWRITE_STOP)
        return f"[Now entering the rewrite phase, where only {REWRITE_NAMES} on {_kept_sizes()} and `done` are allowed.]"

    while True:
        sent = time.time()
        reply = api.send(messages)
        received = time.time()
        used, prompt_tokens = _context(reply, window, prompt_tokens, used)
        _log(RUN_DIR / "requests.jsonl", json.dumps({
            "sent": _iso(sent), "received": _iso(received), "seconds": round(received - sent, 3), "phase": phase, "context": used,
            "usage": reply.get("usage"), "cost": (reply.get("cost") or {}).get("request_cost_usd"),
            "energy": (reply.get("energy") or {}).get("energy_joules")}) + "\n")
        turn += 1
        assistant, text, calls = api.parse(reply)
        if text.strip() or calls:
            messages.append(assistant)
        _log(TRANSCRIPT, f"\n--- says {_ts()} ---\n{text}\n" if text.strip() else "")
        if not calls:
            empty += 1
            nudge = (f"[Your last reply reached the {f'{api.cap():,}-token ' if api.cap() else ''}output limit before it made a tool call, "
                     "so it was cut off and discarded. You cannot see any of that reasoning now. To avoid losing work again, think in "
                     "shorter steps: work out one part of the problem, then save your conclusion with a tool call, for example by "
                     "writing it to a file, before going further.]" if api.truncated(reply) and not text.strip() else
                     f"[Your reply {'had no tool call' if text.strip() else 'was empty'}. Continue with a tool call, or call `done` if you are finished.]")
            _say(f"[no tool call {empty}/{MAX_EMPTY}]")
            if empty >= MAX_EMPTY:
                if phase == "rewrite":
                    return f"(gave up after {empty} replies in a row without a tool call)"
                empty, nudge = 0, f"[{MAX_EMPTY} replies in a row had no tool call, so the experiment phase is over.]\n" + rewrite()
            _log(TRANSCRIPT, f"\n{nudge}\n")
            messages.append({"role": "user", "content": nudge})
            continue
        empty = 0
        outs = []
        for c in calls:
            _log(TRANSCRIPT, f"\n>>> {_ts()} {c['name']}" + "".join(
                f"\n  {k}:\n{v}" if isinstance(v, str) and "\n" in v else f" {k}={json.dumps(v, ensure_ascii=False)}"
                for k, v in c["input"].items()) + (f"\n  (invalid arguments) {c['bad']}" if "bad" in c else "") + "\n")
            before = {k: _size(k) for k in KEEP}
            try:
                if "bad" in c:
                    raise ValueError(f"the arguments were not valid JSON, so the call was not run: {c['bad'][:300]}")
                _check(c["name"], c["input"])
                if phase == "rewrite" and not ok(c):
                    raise ValueError(f"only {_allowed()}, and `done`, are allowed now")
                out = clip(TOOLS[c["name"]][0](**dict(c["input"], **({"within": KEEP} if phase == "rewrite" and c["name"] in SCOPED_TOOLS else {}))), MAX_RESULT)
            except Exception as e:
                out = f"error: {e}"
            _say(f"[{c['name']}] {str(c['input'])[:70]}")
            _log(TRANSCRIPT, f"<<< {_ts()}\n{out}\n")
            for k in KEEP:
                if c["name"] not in ("write", "edit") and (size := _size(k)) != before[k]:
                    _say(line := f"{k} changed outside write/edit: {before[k]} -> {size} bytes")
                    _log(TRANSCRIPT, f"{line}\n")
            outs.append(out)
        finished = any(c["name"] == "done" and "bad" not in c for c in calls)
        if finished and phase == "rewrite":
            return next(o for c, o in zip(calls, outs) if c["name"] == "done")
        exhausted = turn >= turns or tokens is not None and used - start >= tokens
        if exhausted and phase == "rewrite":
            return f"(the rewrite phase's budget ran out after {turn} turns)"
        note = ("" if finished else f"[The {phase} phase's budget ran out.]\n") + rewrite() if finished or exhausted else ""
        note += "".join(f"\n[Warning: {k}: {size} bytes (at most {cap}). It will be truncated at session end; "
                        "currently only shrinking edits are allowed.]" for k, cap, size in _over())
        note += f"\n[{phase} phase: {turns - turn} turn{'s' * (turns - turn != 1)}" + (f" and {tokens - (used - start)} tokens" if tokens else "") + " left]"
        _log(TRANSCRIPT, f"\n{note.strip()}\n")
        outs[-1] += "\n\n" + note.strip()
        messages += api.results(calls, outs)


def _copy(src, dst):
    if dst.is_dir() and not dst.is_symlink():
        shutil.rmtree(dst)
    dst.parent.mkdir(parents=True, exist_ok=True)
    shutil.copytree(src, dst) if src.is_dir() else shutil.copy(src, dst)


def session(run_dir, prompt, seeds):
    global RUN_DIR, SANDBOX_ROOT, ROOT_FD, LOG_PATH, TRANSCRIPT, SESSION_ID, COMPILER
    RUN_DIR = run_dir
    SPENT.clear()
    attempt = 1 + len(list(RUN_DIR.parent.glob(f"{RUN_DIR.name}.*")))
    SESSION_ID = re.sub(r"[^A-Za-z0-9._-]", "-", f"{RUN_DIR.relative_to(RESULTS)}-attempt{attempt}")
    RUN_DIR.mkdir(parents=True)
    tmp = RESULTS / f".latest-{os.getpid()}"
    tmp.unlink(missing_ok=True)
    tmp.symlink_to(RUN_DIR.relative_to(RESULTS))
    os.replace(tmp, RESULTS / "latest")
    COMPILER = Path(tempfile.mkdtemp(prefix="slc-")) / "slc"
    shutil.copy(SLC, COMPILER)
    (RUN_DIR / "session.json").write_text(json.dumps(
        {"commit": _commit(), "slc_sha256": hashlib.sha256(COMPILER.read_bytes()).hexdigest(), "seeds": [str(src) for src, _ in seeds],
         "keep": KEEP, "carry": CARRY, "env": _settings(os.environ)}, indent=1) + "\n")
    SANDBOX_ROOT = Path(tempfile.mkdtemp(prefix="sandbox-")).resolve()
    ROOT_FD = os.open(SANDBOX_ROOT, os.O_RDONLY | os.O_DIRECTORY)
    (RUN_DIR / "sandbox").symlink_to(SANDBOX_ROOT)
    for k in KEEP:
        (RUN_DIR / f"sandbox-{k.replace('/', '-')}").symlink_to(Path("sandbox", k))
    LOG_PATH, TRANSCRIPT = RUN_DIR / "requests.log" if REQUESTS_LOG else None, RUN_DIR / "transcript.log"
    (RUN_DIR / "prompt.txt").write_text(prompt)
    _log(TRANSCRIPT, f"=== {PROVIDER}/{MODEL} {time.strftime('%Y-%m-%d %H:%M:%S')}\n"
                     + "".join(f"--- seed {src} -> {rel} ---\n" for src, rel in seeds) + "".join(f"--- keep {k}" + (f", at most {cap} bytes" if cap else "") + " ---\n" for k, cap in sorted(KEEP.items()))
                     + "".join(f"--- carry {c} ---\n" for c in CARRY) + f"--- prompt ---\n{prompt}\n")
    _say(f"run dir: {RUN_DIR}")
    t0 = time.time()
    try:
        for c in CARRY:
            os.close(_walk_to_dir(_rel_parts(c), create=True))
        for src, rel in seeds:
            _copy(src, SANDBOX_ROOT / rel)
        answer = run(prompt)
        (RUN_DIR / "answer.txt").write_text(f"{answer}\n\n({time.time() - t0:.0f}s{_spend({})})\n")
        print(answer)
    finally:
        for k, cap, size in _over():
            data, cut = read_bytes(k), cap
            while cut and data[cut] & 0xC0 == 0x80:
                cut -= 1
            write_bytes(k, data[:cut])
            _say(line := f"{k} truncated at session end: {size} -> {cut} bytes")
            _log(TRANSCRIPT, f"\n{line}\n")
        (RUN_DIR / "sandbox").unlink()
        shutil.copytree(SANDBOX_ROOT, RUN_DIR / "sandbox", symlinks=True)
        shutil.rmtree(SANDBOX_ROOT)
        shutil.rmtree(COMPILER.parent)
        os.close(ROOT_FD)


def _commit():
    r = subprocess.run(["git", "-C", str(HERE), "rev-parse", "HEAD"], capture_output=True, text=True)
    return r.stdout.strip() or None


def _settings(env):
    return {k: v for k, v in env.items() if k.startswith("PI_") and "KEY" not in k}


def _exec(args, env):
    os.execve(sys.executable, [sys.executable, __file__, *args], {k: v for k, v in os.environ.items() if k not in _settings(os.environ)} | env)


HEADER, HEADER_FLAGS = "#!pi", ("-f", "-k", "-c", "-n")


def _keep_path(k):
    return os.path.normpath(k.rsplit(":", 1)[0] if re.fullmatch(r".+:\d+", k) else k)


def _task_lines(path):
    text = Path(path).read_text()
    first, _, rest = text.partition("\n")
    return (first[len(HEADER):], rest) if first.startswith(HEADER) and first[len(HEADER):][:1] in ("", " ", "\t") else ("", text)


def _config(rec):
    layers, env = [], {}
    for a in [] if rec.get("no_header") else rec["prompts"]:
        words, pairs = shlex.split(_task_lines(a)[0]), []
        while words:
            w = words.pop(0)
            if re.fullmatch(r"PI_\w+=.*", w):
                name, _, value = w.partition("=")
                env[name] = (value, a)
            elif w in HEADER_FLAGS and words:
                v = words.pop(0)
                pairs.append((w, str(Path(a).parent / v) if w == "-f" else v))
            else:
                sys.exit(f"{a}: cannot read {w!r} in its {HEADER} line")
        layers.append((a, pairs))
    layers.append(("command line", [tuple(p) for p in (rec["flags"] if "flags" in rec else [("-f", f) for f in rec["seeds"]]
                                    + [("-k", k) for k in rec["keep"]] + [("-c", c) for c in rec.get("carry", [])])]))
    for name, value in rec["env"].items():
        env[name] = (value, f"environment, over {env[name][0]} from {env[name][1]}" if name in env else "environment")
    key = {"-f": lambda v: Path(v).resolve().name, "-k": _keep_path, "-c": os.path.normpath, "-n": lambda v: None}
    merged = [(f, v, src) for i, (src, pairs) in enumerate(layers) for f, v in pairs
              if not any(g == f and key[f](w) == key[f](v) for _, later in layers[i + 1:] for g, w in later)]
    return merged, env


def _problem(pairs, env):
    seeds, keep = [Path(v) for f, v in pairs if f == "-f"], [v for f, v in pairs if f == "-k"]
    return next((m for bad, m in (
        (not keep, "at least one -k is needed"),
        (any(not s.exists() for s in seeds), f"no such file: {next((s for s in seeds if not s.exists()), '')}"),
        (any(s.is_dir() and s.resolve().name in map(_keep_path, keep) for s in seeds), "-k cannot name a directory; carry one with -c"),
        (len({s.resolve().name for s in seeds}) < len(seeds), "two -f paths share a name"),
        (_first_error(env) not in FIRST_ERROR_NOTES, f"PI_FIRST_ERROR must be one of {', '.join(FIRST_ERROR_NOTES)}"),
        (_provider(env) not in ADAPTERS, f"unknown provider {_provider(env)!r}; try: {', '.join(ADAPTERS)}"),
        (not os.access(_slc(env), os.X_OK), f"no slc at {_slc(env)}; build it with self/release.sh")) if bad), None)


def _stop(loop, message):
    (loop / "pid").unlink(missing_ok=True)
    sys.exit(message)


def _carried(prev, c):
    d = prev / "sandbox" / c
    if d.is_dir() and not d.is_symlink():
        return [(d, c)]
    _say(f"-c {c}: session {prev.name} left no directory there, so the next session starts with an empty one")
    return []


def _claim(loop):
    pid_file = loop / "pid"
    pid = pid_file.read_text().strip() if pid_file.exists() else ""
    if pid.isdigit() and int(pid) != os.getpid() and "pi.py" in subprocess.run(["ps", "-p", pid, "-o", "command="], capture_output=True, text=True).stdout:
        sys.exit(f"{loop} is still being run by process {pid}")
    pid_file.write_text(str(os.getpid()))


def _set_aside(d):
    kind = "superseded" if (d / "answer.txt").exists() else "stalled"
    k = 1
    while d.with_name(f"{d.name}.{kind}-{k}").exists():
        k += 1
    sandbox = d / "sandbox"
    if sandbox.is_symlink() and sandbox.resolve().is_dir():
        target = sandbox.resolve()
        sandbox.unlink()
        shutil.copytree(target, sandbox, symlinks=True)
        shutil.rmtree(target)
    d.rename(d.with_name(f"{d.name}.{kind}-{k}"))
    _say(f"set {d.name} aside as {d.name}.{kind}-{k}")


def _next(loop):
    _claim(loop)
    rec = json.loads((loop / "run.json").read_text())
    n = rec["n"]
    first = next((i for i in range(1, n + 1) if not (loop / f"{i:02}" / "answer.txt").exists()), n + 1)
    for d in sorted(d for d in loop.iterdir() if d.name.isdigit() and int(d.name) >= first):
        _set_aside(d)
    if first > n:
        _say(f"{loop.name}: {n} session{'s' * (n != 1)} done")
        _stop(loop, None)
    try:
        merged, env = _config(rec)
    except (OSError, SystemExit) as e:
        _stop(loop, f"{loop.name}: cannot read its settings: {e}")
    for f, v, src in merged:
        _say(f"{f} {v}  ({src})")
    for name, (value, src) in env.items():
        _say(f"{name}={value}  ({src})")
    _exec(["--session", str(loop), str(first), *[a for f, v, _ in merged if f != "-n" for a in (f, v)]], {k: v for k, (v, _) in env.items()})


def _session(loop, i, pairs):
    if problem := _problem(pairs, os.environ):
        _stop(loop, problem)
    for k in (v for f, v in pairs if f == "-k"):
        KEEP[_keep_path(k)] = int(k.rsplit(":", 1)[1]) if re.fullmatch(r".+:\d+", k) else 0
    CARRY[:] = [os.path.normpath(v) for f, v in pairs if f == "-c"]
    rec = json.loads((loop / "run.json").read_text())
    prompt = "\n\n".join(t for a in rec["prompts"] if (t := _task_lines(a)[1].strip()))
    prev = loop / f"{i - 1:02}" if i > 1 else None
    seeds = [(Path(v), Path(v).resolve().name) for f, v in pairs if f == "-f"] + [
        (prev / "sandbox" / k, k) for k in KEEP if prev and (prev / "sandbox" / k).exists()] + [x for c in CARRY if prev for x in _carried(prev, c)]
    for attempt in range(1, SESSION_TRIES + 1):
        _say(f"session {i}/{rec['n']}, attempt {attempt}/{SESSION_TRIES}")
        try:
            session(loop / f"{i:02}", prompt, seeds)
            break
        except (Exception, SystemExit):
            traceback.print_exc()
            if attempt == SESSION_TRIES:
                _stop(loop, f"session {i}/{rec['n']} failed {SESSION_TRIES} times; stopping (resume with -r {loop})")
            if (loop / f"{i:02}").exists():
                _set_aside(loop / f"{i:02}")
    _exec(["-r", str(loop)], {})


USAGE = ("usage: pi.py [--no-header] [-f PATH]... -k PATH[:BYTES]... [-c DIR]... [-n N] PROMPT-FILE ...   (the prompt files are joined into one prompt)\n"
         "       pi.py -r RUN-DIR [-n N]\n"
         f"  a prompt file whose first line starts with `{HEADER}` sets flags and PI_NAME=value settings there, which are not part\n"
         "           of the prompt; -f paths are relative to the file. A later file overrides an earlier one, and the environment\n"
         "           and command line override both: a later -n, PI_ setting, or -f, -k or -c on the same path replaces an earlier one.\n"
         "           Each session starts a fresh pi.py and re-reads the prompt files, their headers and the compiler; the command\n"
         "           line's flags and PI_ settings, recorded in run.json, stay with the run\n"
         "  --no-header  ignore the prompt files' header settings (the header lines still stay out of the prompt)\n"
         "  -f PATH  copy this file or directory into the sandbox root under its own name\n"
         "  -k PATH[:BYTES]  carry PATH from each session's sandbox into the next, and allow only\n"
         "           read/write/edit/grep/ls on it once experimenting ends; BYTES caps its size (0: no cap)\n"
         "  -c DIR   carry the directory DIR from each session's sandbox into the next; no tool may use it\n"
         "           once experimenting ends\n"
         "  -n N     run N sessions in a row (default 1); fixed when the run starts, then changed only by -r's -n or run.json\n"
         "  -r DIR   continue the run in DIR from its first session without an answer.txt, setting that session and the\n"
         "           ones after it aside; -n sets a new total\n"
         "environment (defaults in brackets):\n"
         "  PI_PROVIDER       neuralwatt, anthropic, openai or local [neuralwatt]\n"
         "  PI_MODEL          [deepseek-v4.1-flash-flex, claude-sonnet-5-5, gpt-6-luna, or PI_LOCAL_MODEL, by provider]\n"
         "  NEURALWATT_API_KEY, ANTHROPIC_API_KEY, OPENAI_API_KEY, PI_LOCAL_API_KEY   the provider's key\n"
         "  PI_LOCAL_URL      [http://localhost:8080/v1]\n"
         "  PI_MAX_TURNS      turns per phase [1000 if the context window is known, else 200]\n"
         "  PI_CONTEXT_STOP   context for the experiment phase, in % of the window [20]\n"
         "  PI_REWRITE_STOP   context for the rewrite phase, in % of the window [PI_CONTEXT_STOP]\n"
         "  PI_CONTEXT        the context window, overriding the provider's [0: ask the provider]\n"
         "  PI_MAX_TOKENS     output tokens per reply [the model's maximum]\n"
         "  PI_EFFORT         reasoning effort [unset]\n"
         "  PI_STREAM         stream replies [1]\n"
         "  PI_HTTP_TIMEOUT, PI_HTTP_TRIES   per request [1800 s, 6 tries]\n"
         "  PI_MAX_EMPTY      replies in a row without a tool call before giving up [3]\n"
         "  PI_SESSION_TRIES  attempts at a session before stopping [3]\n"
         "  PI_REQUESTS_LOG   keep every request and response in requests.log, which grows quadratically [0]\n"
         "  PI_RUN_TIMEOUT    seconds each program may run [10]\n"
         "  PI_RUN_STATS      report each program's wall-clock time, CPU time and peak memory [1]\n"
         "  PI_FIRST_ERROR    yes: the compiler stops at the first error; no: it reports every error; choose: the `sl` tool's\n"
         "                    `first_error` decides, defaulting to every error [yes]\n"
         "  PI_SLC            the compiler, copied at the start of each session [../_build/release/slc]\n"
         "  PI_GATE_PORT      the localhost port of the organizer that lets one `sl` call run at a time, fairest to the run\n"
         "                    served least recently; the first pi.py to need it starts it [47219]")


def main(argv):
    if argv[:1] == ["--gate"]:
        return gate()
    if argv[:1] == ["--session"] and len(argv) >= 3:
        return _session(Path(argv[1]), int(argv[2]), list(zip(argv[3::2], argv[4::2])))
    pairs, no_header = [], False
    while argv[:1] == ["--no-header"] or argv[:1] and argv[0] in (*HEADER_FLAGS, "-r") and len(argv) > 1:
        no_header, pairs, argv = (True, pairs, argv[1:]) if argv[0] == "--no-header" else (no_header, pairs + [tuple(argv[:2])], argv[2:])
    n = int(next((v for f, v in reversed(pairs) if f == "-n"), "0"))
    if resume := next((Path(v).resolve() for f, v in reversed(pairs) if f == "-r"), None):
        if argv:
            sys.exit(USAGE)
        if n:
            f = resume / "run.json"
            tmp = f.with_name("run.json.tmp")
            tmp.write_text(json.dumps(json.loads(f.read_text()) | {"n": n}, indent=1) + "\n")
            os.replace(tmp, f)
        return _next(resume)
    if not argv:
        sys.exit(USAGE)
    rec = {"n": 0, "prompts": [str(Path(a).resolve()) for a in argv], "no_header": no_header,
           "flags": [(f, str(Path(v).resolve()) if f == "-f" else v) for f, v in pairs if f in ("-f", "-k", "-c")],
           "env": _settings(os.environ), "commit": _commit()}
    merged, env = _config(rec)
    env = {k: v for k, (v, _) in env.items()}
    if problem := _problem([(f, v) for f, v, _ in merged], env):
        sys.exit(f"{problem}\n\n{USAGE}")
    rec["n"] = n or int(next((v for f, v, _ in reversed(merged) if f == "-n"), "1"))
    tag = "+".join(Path(a).stem for a in argv)
    base, k = f"{time.strftime('%Y%m%d-%H%M')}-{_model_name(env).replace('/', '_')}{'-' + _effort(env) if _effort(env) else ''}-{tag}", 1
    while True:
        loop = RESULTS / (base if k == 1 else f"{base}-{k}")
        try:
            loop.mkdir(parents=True)
            break
        except FileExistsError:
            k += 1
    (loop / "run.json").write_text(json.dumps(rec, indent=1) + "\n")
    _next(loop)


if __name__ == "__main__":
    main(sys.argv[1:])
