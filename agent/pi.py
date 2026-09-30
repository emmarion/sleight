#!/usr/bin/env python3
import ctypes, functools, hashlib, json, os, re, shlex, shutil, signal, stat, struct, subprocess, sys, tempfile, time, traceback, urllib.request
from pathlib import Path

HERE = Path(__file__).resolve().parent
RESULTS = HERE / "results"
PROVIDER = os.environ.get("PI_PROVIDER", "neuralwatt")
DEFAULT_MODELS = {"anthropic": "claude-haiku-4-5", "neuralwatt": "glm-5.3", "local": os.environ.get("PI_LOCAL_MODEL", "")}
MODEL = os.environ.get("PI_MODEL", DEFAULT_MODELS.get(PROVIDER, ""))
MAX_TOKENS = int(os.environ.get("PI_MAX_TOKENS", "65536"))
HTTP_TIMEOUT = int(os.environ.get("PI_HTTP_TIMEOUT", "600"))
STREAM = os.environ.get("PI_STREAM", "1") not in ("0", "false", "")
EFFORT = os.environ.get("PI_EFFORT", "").strip()
MAX_TURNS = int(os.environ.get("PI_MAX_TURNS", "0"))
MAX_EMPTY = int(os.environ.get("PI_MAX_EMPTY", "3"))
CONTEXT = int(os.environ.get("PI_CONTEXT", "0"))
CONTEXT_STOP = float(os.environ.get("PI_CONTEXT_STOP", "20"))
SESSION_TRIES = int(os.environ.get("PI_SESSION_TRIES", "3"))
SLC = os.environ.get("PI_SLC", str(HERE.parent / "_build/release/slc"))
SLC_TIMEOUT, BUILD_TIMEOUT, RUN_TIMEOUT = 60, 120, int(os.environ.get("PI_RUN_TIMEOUT", "10"))
MEM_MB = os.sysconf("SC_PHYS_PAGES") * os.sysconf("SC_PAGE_SIZE") // 4 // 2**20
MAX_WRITE, MAX_OUT, MAX_KEPT_FAILURE, MAX_PROGRAM_OUTPUT = 8 * 1024 * 1024, 20000, 1024 * 1024, 1024 * 1024
RUN_DIR = SANDBOX_ROOT = ROOT_FD = LOG_PATH = TRANSCRIPT = SESSION_ID = None
KEEP = {}
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
    name = os.path.normpath(user_path)
    if KEEP.get(name) and len(data) > KEEP[name] and len(data) > _size(name):
        raise ValueError(f"{name} would be {len(data)} bytes; the cap is {KEEP[name]}")
    flags = os.O_WRONLY | os.O_CREAT | os.O_TRUNC | os.O_NOFOLLOW | getattr(os, "O_CLOEXEC", 0)
    with os.fdopen(_open_in(user_path, flags, create=True), "wb") as f:
        return f.write(data)


def _size(path):
    try:
        return len(read_bytes(path))
    except (OSError, PathEscape):
        return 0


def list_dir(user_path="."):
    dfd = _walk_to_dir(_rel_parts(user_path), create=False)
    try:
        def suffix(nm):
            try:
                m = os.stat(nm, dir_fd=dfd, follow_symlinks=False).st_mode
            except OSError:
                return ""
            return "@" if stat.S_ISLNK(m) else "/" if stat.S_ISDIR(m) else ""
        return sorted(nm + suffix(nm) for nm in os.listdir(dfd))
    finally:
        os.close(dfd)


def _base(path):
    return SANDBOX_ROOT.joinpath(*(_rel_parts(path) if path not in (".", "") else []))


def _walk_files(path):
    for dirpath, dirnames, filenames in os.walk(_base(path), followlinks=False):
        for fn in filenames:
            p = Path(dirpath) / fn
            if not p.is_symlink():
                yield str(p.relative_to(SANDBOX_ROOT)), p


def clip(s):
    return s if len(s) <= MAX_OUT else s[:MAX_OUT] + f"\n... ({len(s) - MAX_OUT} more chars cut)"


def read(path, offset=1, limit=2000):
    lines = read_bytes(path).decode("utf-8", "replace").splitlines()
    start = max(offset, 1) - 1
    shown = lines[start:start + max(limit, 0)]
    rest = len(lines) - start - len(shown)
    return ("\n".join(f"{i:6}\t{l}" for i, l in enumerate(shown, start + 1)) or f"(no lines; the file has {len(lines)})") + (
        f"\n... ({rest} more lines; read again with offset={start + len(shown) + 1})" if rest > 0 else "")


def write(path, content):
    return f"wrote {write_bytes(path, content.encode())} bytes to {path}"


def edit(path, old, new):
    text = read_bytes(path).decode("utf-8", "replace")
    if text.count(old) != 1:
        return f"error: found {text.count(old)} matches, need exactly 1"
    write_bytes(path, text.replace(old, new).encode())
    return f"edited {path}"


def ls(path="."):
    return "\n".join(list_dir(path)) or "(empty)"


def grep(pattern, path="."):
    rx, hits = re.compile(pattern), []
    for rel, p in _walk_files(path):
        try:
            hits += [f"{rel}:{n}: {l[:200]}" for n, l in enumerate(p.read_text(errors="replace").splitlines(), 1) if rx.search(l)]
        except OSError:
            pass
    return "\n".join(hits[:200]) or "(no matches)"


def find(glob, path="."):
    return "\n".join(str(p.relative_to(SANDBOX_ROOT)) for p in list(_base(path).rglob(glob))[:200]) or "(none)"


@functools.cache
def _ocamlopt():
    show = ["ocamlfind", "ocamlopt", "-only-show", "-package", "zarith,unix", "-linkpkg", "p.ml", "-o", "p"]
    return shlex.split(subprocess.run(show, capture_output=True, text=True, check=True).stdout)


def _spawn_exec_limited(cmd, env):
    libc = ctypes.CDLL(None, use_errno=True)
    strs = lambda xs: (ctypes.c_char_p * (len(xs) + 1))(*[x.encode() for x in xs], None)
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


def _group_mb(pgid):
    libc, pids = ctypes.CDLL(None), (ctypes.c_int * 4096)()
    n = libc.proc_listpids(2, pgid, pids, ctypes.sizeof(pids)) // ctypes.sizeof(ctypes.c_int)
    usage, total = ctypes.create_string_buffer(256), 0
    for pid in pids[:n]:
        if pid and libc.proc_pid_rusage(pid, 0, usage) == 0:
            total += struct.unpack_from("Q", usage, 72)[0]
    return total >> 20


def _proc(cmd, cwd, timeout, stdin="", env=None):
    env = os.environ if env is None else env
    with subprocess.Popen(cmd, cwd=cwd, env=env, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                          start_new_session=True, preexec_fn=_spawn_exec_limited(cmd, env)) as p:
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
            return why, subprocess.CompletedProcess(cmd, p.returncode, out, err)
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


def sl(paths, stdin="", args=(), capture=None):
    if isinstance(paths, str):
        paths = [paths]
    if capture and any(os.path.normpath(f"{capture}.{ext}") in KEEP for ext in ("slc.err", "out", "err")):
        raise ValueError("`capture` cannot name a kept file")
    with tempfile.TemporaryDirectory(prefix="pi-sl-") as tmp:
        src = Path(tmp, "src")
        names = []
        for p in paths:
            name = "/".join(_rel_parts(p))
            (src / name).parent.mkdir(parents=True, exist_ok=True)
            (src / name).write_bytes(read_bytes(p))
            names.append(name)
        why, c = _proc([SLC, "--confine-dir", ".", "--confine-output-bytes", str(MAX_PROGRAM_OUTPUT), "--no-env", *names], src, SLC_TIMEOUT, env={})
        warnings = _shown(capture, "slc.err", c.stderr)
        if why or c.returncode:
            return f"compile: {why or f'failed (exit {c.returncode})'}\n{warnings}"
        Path(tmp, "p.ml").write_bytes(c.stdout)
        why, b = _proc(_ocamlopt(), tmp, BUILD_TIMEOUT, env={**os.environ, "TMPDIR": tmp})
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
        why, r = _proc([str(Path(tmp, "p")), *map(str, args)], SANDBOX_ROOT, RUN_TIMEOUT, stdin, env={})
        head = f"compile: ok\n{warnings}" if warnings else "compile: ok"
        return f"{head}\nrun: {why or f'exit {r.returncode}'}\n--- stdout ---\n{_shown(capture, "out", r.stdout)}\n--- stderr ---\n{_shown(capture, "err", r.stderr)}"


def done(summary=""):
    return summary or "done"


STR, STRS, INT = {"type": "string"}, {"type": "array", "items": {"type": "string"}}, {"type": "integer"}
TOOLS = {
    "read": (read, "Read a file, with line numbers. `offset` is the first line to show (from 1), `limit` how many (default 2000).",
             {"path": STR, "offset": INT, "limit": INT}, ["path"]),
    "write": (write, "Write a file", {"path": STR, "content": STR}, ["path", "content"]),
    "edit": (edit, "Replace exactly one occurrence of old with new", {"path": STR, "old": STR, "new": STR}, ["path", "old", "new"]),
    "ls": (ls, "List a directory", {"path": STR}, []),
    "grep": (grep, "Regex search file contents", {"pattern": STR, "path": STR}, ["pattern"]),
    "find": (find, "Find files by glob", {"glob": STR, "path": STR}, ["glob"]),
    "sl": (sl, "Compile the SL source files at `paths` (read in order, sharing one scope) and, if they compile, "
               "run the program with the sandbox as its working directory, feeding it `stdin` and passing it `args`. "
               "Returns the compiler's messages, then the program's exit code, stdout and stderr. With `capture`, these go to "
               "`{capture}.slc.err`, `{capture}.out` and `{capture}.err`, and only their sizes and first and last lines are shown.",
           {"paths": STRS, "stdin": STR, "args": STRS, "capture": STR}, ["paths"]),
    "done": (done, "The first call ends the experiment phase and starts the rewrite phase, which has a fresh budget of the same size "
                   "and allows only {allowed}, and `done`. The second call ends the session. Pass a one-line summary.",
             {"summary": STR}, []),
}
PARAMS = {n: {"type": "object", "properties": props, "required": req} for n, (_, _, props, req) in TOOLS.items()}


def _ts():
    return time.strftime('%H:%M:%S')


def _say(text):
    print(f"{_ts()} {text}", file=sys.stderr)


def _log(path, text):
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


def assemble_sse(r):
    content, reasoning, calls = [], [], {}
    finish = usage = None
    think = ThinkLog()
    try:
        for raw in r:
            line = raw.decode("utf-8", "replace").strip()
            if not line.startswith("data: "):
                continue
            if line[6:] == "[DONE]":
                break
            try:
                d = json.loads(line[6:])
            except ValueError:
                continue
            usage = d.get("usage") or usage
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
    return {"choices": [{"message": msg, "finish_reason": finish}], **({"usage": usage} if usage else {})}


def post(url, body, headers, tries=int(os.environ.get("PI_HTTP_TRIES", "6")), stream=False):
    global _LOG_N
    for attempt in range(tries):
        req = urllib.request.Request(url, data=json.dumps(body).encode(), headers={"content-type": "application/json", **headers})
        _LOG_N += 1
        _log(LOG_PATH, _banner(f"  (retry {attempt})" if attempt else "") + f"{url}\n---- request ----\n{json.dumps(body, indent=2, ensure_ascii=False)}\n")
        t0 = time.time()
        try:
            with urllib.request.urlopen(req, timeout=HTTP_TIMEOUT) as r:
                reply = assemble_sse(r) if stream else json.loads(r.read())
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


class Anthropic:
    url = "https://api.anthropic.com/v1/messages"

    def send(self, messages):
        return post(self.url, {
            "model": MODEL, "max_tokens": MAX_TOKENS, "system": SYSTEM,
            "tools": [{"name": n, "description": d.replace("{allowed}", _allowed(caps=True)), "input_schema": PARAMS[n]} for n, (_, d, _, _) in TOOLS.items()],
            "messages": messages,
        }, {"x-api-key": os.environ["ANTHROPIC_API_KEY"], "anthropic-version": "2023-06-01"})

    def parse(self, reply):
        blocks = reply["content"]
        calls = [{"id": b["id"], "name": b["name"], "input": b["input"]} for b in blocks if b["type"] == "tool_use"]
        return {"role": "assistant", "content": blocks}, "".join(b["text"] for b in blocks if b["type"] == "text"), calls

    def window(self):
        return None

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
            self.__class__._model = {}
            try:
                with urllib.request.urlopen(urllib.request.Request(self.base + "/models", headers=self.auth()), timeout=30) as r:
                    self.__class__._model = next((m for m in json.load(r)["data"] if m["id"] == MODEL), {})
            except Exception:
                pass
        return self._model

    def limit(self, key):
        return ((self.model().get("metadata") or {}).get("limits") or {}).get(key)

    def cap(self):
        return min(MAX_TOKENS, self.limit("max_output_tokens") or MAX_TOKENS)

    def window(self):
        return self.limit("max_context_length") or self.model().get("max_model_len")

    def send(self, messages):
        body = {
            "model": MODEL, "max_tokens": self.cap(),
            "tools": [{"type": "function", "function": {"name": n, "description": d.replace("{allowed}", _allowed(caps=True)), "parameters": PARAMS[n]}} for n, (_, d, _, _) in TOOLS.items()],
            "messages": [{"role": "system", "content": SYSTEM}] + messages,
            "user": SESSION_ID,
        }
        if EFFORT:
            body["reasoning_effort"] = EFFORT
        if STREAM:
            body.update(stream=True, stream_options={"include_usage": True})
        return post(self.base + "/chat/completions", body, {**self.auth(), "x-nw-conversation-id": SESSION_ID}, stream=STREAM)

    def parse(self, reply):
        msg = reply["choices"][0]["message"]
        calls = []
        for c in msg.get("tool_calls") or []:
            try:
                calls.append({"id": c["id"], "name": c["function"]["name"], "input": json.loads(c["function"]["arguments"] or "{}")})
            except ValueError:
                calls.append({"id": c["id"], "name": c["function"]["name"], "input": {}, "bad": c["function"]["arguments"]})
                c["function"]["arguments"] = "{}"
        return msg, msg.get("content") or "", calls

    def results(self, calls, outs):
        return [{"role": "tool", "tool_call_id": c["id"], "content": o} for c, o in zip(calls, outs)]


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


ADAPTERS = {"anthropic": Anthropic, "neuralwatt": OpenAICompat, "local": Local}


def _context(usage, window):
    if not usage:
        return 0
    n = usage.get("total_tokens") or sum(usage.get(k) or 0 for k in
                                         ("input_tokens", "cache_read_input_tokens", "cache_creation_input_tokens", "output_tokens"))
    line = f"[context: {n:,}" + (f" / {window:,} ({100 * n / window:.1f}%)]" if window else "]")
    _say(line)
    _log(TRANSCRIPT, f"\n{line}\n")
    return n


def _allowed(caps=False):
    return f"`read`, `write` and `edit` on " + ", ".join(k + (f" (at most {cap} bytes)" if caps and cap else "") for k, cap in sorted(KEEP.items()))


def _kept_sizes():
    return ", ".join(f"{k} ({_size(k)} bytes" + (f", at most {cap})" if cap else ")") for k, cap in sorted(KEEP.items()))


def run(prompt):
    api = ADAPTERS[PROVIDER]()
    messages, empty = [{"role": "user", "content": prompt}], 0
    window = CONTEXT or api.window()
    turns, tokens = MAX_TURNS or (1000 if window else 200), int(window * CONTEXT_STOP / 100) if window else None
    phase, turn, start = "experiment", 0, 0
    ok = lambda c: c["name"] == "done" or c["name"] in ("read", "write", "edit") and os.path.normpath(str(c["input"].get("path", ""))) in KEEP

    def rewrite():
        nonlocal phase, turn, start
        phase, turn, start = "rewrite", 0, used
        return f"[Now entering the rewrite phase, where only `read`, `write` and `edit` on {_kept_sizes()} and `done` are allowed.]"

    while True:
        reply = api.send(messages)
        used = _context(reply.get("usage"), window)
        turn += 1
        assistant, text, calls = api.parse(reply)
        if not calls and not text.strip():
            empty += 1
            if empty >= MAX_EMPTY:
                return f"(gave up after {empty} empty replies in a row)"
            nudge = "[Your reply was empty. Continue with a tool call, or call `done` if you are finished.]"
            _say(f"[empty reply {empty}/{MAX_EMPTY}]")
            _log(TRANSCRIPT, f"\n{nudge}\n")
            messages.append({"role": "user", "content": nudge})
            continue
        empty = 0
        messages.append(assistant)
        _log(TRANSCRIPT, f"\n--- says {_ts()} ---\n{text}\n" if text.strip() else "")
        outs = []
        for c in calls:
            _log(TRANSCRIPT, f"\n>>> {_ts()} {c['name']}" + "".join(
                f"\n  {k}:\n{v}" if isinstance(v, str) and "\n" in v else f" {k}={json.dumps(v, ensure_ascii=False)}"
                for k, v in c["input"].items()) + (f"\n  (invalid arguments) {c['bad']}" if "bad" in c else "") + "\n")
            try:
                if "bad" in c:
                    raise ValueError(f"the arguments were not valid JSON, so the call was not run: {c['bad'][:300]}")
                if phase == "rewrite" and not ok(c):
                    raise ValueError(f"only {_allowed()}, and `done`, are allowed now")
                out = TOOLS[c["name"]][0](**c["input"])
            except Exception as e:
                out = f"error: {e}"
            _say(f"[{c['name']}] {str(c['input'])[:70]}")
            _log(TRANSCRIPT, f"<<< {_ts()}\n{out}\n")
            outs.append(out)
        finished = not calls or any(c["name"] == "done" and "bad" not in c for c in calls)
        if finished and phase == "rewrite":
            return next((o for c, o in zip(calls, outs) if c["name"] == "done"), text)
        exhausted = turn >= turns or tokens is not None and used - start >= tokens
        if exhausted and phase == "rewrite":
            return f"(the rewrite phase's budget ran out after {turn} turns)"
        note = ("" if finished else f"[The {phase} phase's budget ran out.]\n") + rewrite() if finished or exhausted else ""
        note += f"\n[{phase} phase: {turns - turn} turn{'s' * (turns - turn != 1)}" + (f" and {tokens - (used - start)} tokens" if tokens else "") + " left]"
        _log(TRANSCRIPT, f"\n{note.strip()}\n")
        if calls:
            outs[-1] += "\n\n" + note.strip()
            messages += api.results(calls, outs)
        else:
            messages.append({"role": "user", "content": note.strip()})


def _copy(src, dst):
    dst.parent.mkdir(parents=True, exist_ok=True)
    shutil.copytree(src, dst) if src.is_dir() else shutil.copy(src, dst)


def session(run_dir, prompt, seeds):
    global RUN_DIR, SANDBOX_ROOT, ROOT_FD, LOG_PATH, TRANSCRIPT, SESSION_ID
    RUN_DIR = run_dir
    attempt = 1 + len(list(RUN_DIR.parent.glob(f"{RUN_DIR.name}.*")))
    SESSION_ID = re.sub(r"[^A-Za-z0-9._-]", "-", f"{RUN_DIR.relative_to(RESULTS)}-attempt{attempt}")
    RUN_DIR.mkdir(parents=True)
    latest = RESULTS / "latest"
    latest.unlink(missing_ok=True)
    latest.symlink_to(RUN_DIR.relative_to(RESULTS))
    SANDBOX_ROOT = Path(tempfile.mkdtemp(prefix="sandbox-")).resolve()
    ROOT_FD = os.open(SANDBOX_ROOT, os.O_RDONLY | os.O_DIRECTORY)
    (RUN_DIR / "sandbox").symlink_to(SANDBOX_ROOT)
    LOG_PATH, TRANSCRIPT = RUN_DIR / "requests.log", RUN_DIR / "transcript.log"
    (RUN_DIR / "prompt.txt").write_text(prompt)
    _log(TRANSCRIPT, f"=== {PROVIDER}/{MODEL} {time.strftime('%Y-%m-%d %H:%M:%S')}\n"
                     + "".join(f"--- seed {src} -> {rel} ---\n" for src, rel in seeds) + "".join(f"--- keep {k}" + (f", at most {cap} bytes" if cap else "") + " ---\n" for k, cap in sorted(KEEP.items()))
                     + f"--- prompt ---\n{prompt}\n")
    _say(f"run dir: {RUN_DIR}")
    t0 = time.time()
    try:
        for src, rel in seeds:
            _copy(src, SANDBOX_ROOT / rel)
        answer = run(prompt)
        (RUN_DIR / "answer.txt").write_text(f"{answer}\n\n({time.time() - t0:.0f}s)\n")
        print(answer)
    finally:
        (RUN_DIR / "sandbox").unlink()
        shutil.copytree(SANDBOX_ROOT, RUN_DIR / "sandbox", symlinks=True)
        shutil.rmtree(SANDBOX_ROOT)
        os.close(ROOT_FD)


def _commit():
    r = subprocess.run(["git", "-C", str(HERE), "rev-parse", "HEAD"], capture_output=True, text=True)
    return r.stdout.strip() or None


def _resume(loop, n):
    rec = json.loads((loop / "run.json").read_text())
    env = {k: v for k, v in os.environ.items() if not k.startswith("PI_")} | rec["env"]
    args = [a for f in rec["seeds"] for a in ("-f", f)] + [a for k in rec["keep"] for a in ("-k", k)]
    os.execve(sys.executable, [sys.executable, __file__, *args, "-n", str(n or rec["n"]), "-r", str(loop), *rec["prompts"]], env)


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


def main(argv):
    flags = {"-f": [], "-k": [], "-n": [], "-r": []}
    while argv[:1] and argv[0] in flags and len(argv) > 1:
        flags[argv[0]].append(argv[1])
        argv = argv[2:]
    seeds, keep, n = [Path(f) for f in flags["-f"]], flags["-k"], int((flags["-n"] or ["0"])[-1])
    for k in keep:
        path, cap = (k.rsplit(":", 1) if re.fullmatch(r".+:\d+", k) else (k, "0"))
        KEEP[os.path.normpath(path)] = int(cap)
    resume = Path(flags["-r"][-1]).resolve() if flags["-r"] else None
    if resume and not argv:
        _resume(resume, n)
    n = n or 1
    if not argv or not keep:
        sys.exit("usage: pi.py [-f PATH]... -k PATH[:BYTES]... [-n N] PROMPT-FILE ...   (the prompt files are joined into one prompt)\n"
                 "       pi.py -r RUN-DIR [-n N]\n"
                 "  -f PATH  copy this file or directory into the sandbox root under its own name\n"
                 "  -k PATH[:BYTES]  carry PATH from each session's sandbox into the next, and allow only\n"
                 "           read/write/edit on it once experimenting ends; BYTES caps its size (0: no cap)\n"
                 "  -n N     run N sessions in a row (default 1)\n"
                 "  -r DIR   resume the run in DIR with the settings its run.json records, from its first session\n"
                 "           without an answer.txt, setting that session and the ones after it aside; -n sets a new total\n"
                 "environment (defaults in brackets):\n"
                 "  PI_PROVIDER       neuralwatt, anthropic or local [neuralwatt]\n"
                 "  PI_MODEL          [glm-5.3, claude-haiku-4-5, or PI_LOCAL_MODEL, by provider]\n"
                 "  NEURALWATT_API_KEY, ANTHROPIC_API_KEY, PI_LOCAL_API_KEY   the provider's key\n"
                 "  PI_LOCAL_URL      [http://localhost:8080/v1]\n"
                 "  PI_MAX_TURNS      turns per phase [1000 if the context window is known, else 200]\n"
                 "  PI_CONTEXT_STOP   context per phase, in % of the window [20]\n"
                 "  PI_CONTEXT        the context window, overriding the provider's [0: ask the provider]\n"
                 "  PI_MAX_TOKENS     output tokens per reply [65536]\n"
                 "  PI_EFFORT         reasoning effort [unset]\n"
                 "  PI_STREAM         stream replies [1]\n"
                 "  PI_HTTP_TIMEOUT, PI_HTTP_TRIES   per request [600 s, 6 tries]\n"
                 "  PI_MAX_EMPTY      empty replies in a row before giving up [3]\n"
                 "  PI_SESSION_TRIES  attempts at a session before stopping [3]\n"
                 "  PI_RUN_TIMEOUT    seconds each program may run [10]\n"
                 "  PI_SLC            the compiler [../_build/release/slc]")
    for s in seeds:
        if not s.exists():
            sys.exit(f"no such file: {s}")
    if len({s.resolve().name for s in seeds}) < len(seeds):
        sys.exit("two -f paths share a name")
    if PROVIDER not in ADAPTERS:
        sys.exit(f"unknown provider {PROVIDER!r}; try: {', '.join(ADAPTERS)}")
    if not os.access(SLC, os.X_OK):
        sys.exit(f"no slc at {SLC}; build it with self/release.sh")
    prompt = "\n\n".join(Path(a).read_text().strip() for a in argv)
    tag = "+".join(Path(a).stem for a in argv)
    loop = resume or RESULTS / f"{time.strftime('%Y%m%d-%H%M%S')}-{MODEL.replace('/', '_')}-{tag}"
    loop.mkdir(parents=True, exist_ok=True)
    _claim(loop)
    record = {"n": n, "seeds": [str(s.resolve()) for s in seeds], "keep": keep, "prompts": [str(Path(a).resolve()) for a in argv],
              "env": {k: v for k, v in os.environ.items() if k.startswith("PI_") and "KEY" not in k},
              "commit": _commit(), "slc_sha256": hashlib.sha256(Path(SLC).read_bytes()).hexdigest()}
    if resume:
        old = json.loads((loop / "run.json").read_text())
        if old.get("commit") != record["commit"]:
            _say(f"warning: resuming at commit {record['commit']}, but the run started at {old.get('commit')}")
        record = old | {"n": n}
    (loop / "run.json").write_text(json.dumps(record, indent=1) + "\n")
    first = next((i for i in range(1, n + 1) if not (loop / f"{i:02}" / "answer.txt").exists()), n + 1)
    for d in sorted(d for d in loop.iterdir() if d.name.isdigit() and int(d.name) >= first):
        _set_aside(d)
    prev = loop / f"{first - 1:02}" if first > 1 else None
    try:
        for i in range(first, n + 1):
            carried = [(prev / "sandbox" / k, k) for k in KEEP if prev and (prev / "sandbox" / k).exists()]
            for attempt in range(1, SESSION_TRIES + 1):
                _say(f"session {i}/{n}, attempt {attempt}/{SESSION_TRIES}")
                try:
                    session(loop / f"{i:02}", prompt, [(s, s.resolve().name) for s in seeds] + carried)
                    break
                except (Exception, SystemExit):
                    traceback.print_exc()
                    if attempt == SESSION_TRIES:
                        sys.exit(f"session {i}/{n} failed {SESSION_TRIES} times; stopping (resume with -r {loop})")
                    if (loop / f"{i:02}").exists():
                        _set_aside(loop / f"{i:02}")
            prev = loop / f"{i:02}"
    finally:
        (loop / "pid").unlink(missing_ok=True)


if __name__ == "__main__":
    main(sys.argv[1:])
