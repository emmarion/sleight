#!/usr/bin/env python3
import json, os, re, shutil, stat, subprocess, sys, tempfile, time, urllib.request
from pathlib import Path

HERE = Path(__file__).resolve().parent
PROVIDER = os.environ.get("PI_PROVIDER", "neuralwatt")
DEFAULT_MODELS = {"anthropic": "claude-haiku-4-5", "neuralwatt": "glm-5.3", "local": os.environ.get("PI_LOCAL_MODEL", "")}
MODEL = os.environ.get("PI_MODEL", DEFAULT_MODELS.get(PROVIDER, ""))
MAX_TOKENS = int(os.environ.get("PI_MAX_TOKENS", "65536"))
HTTP_TIMEOUT = int(os.environ.get("PI_HTTP_TIMEOUT", "600"))
STREAM = os.environ.get("PI_STREAM", "1") not in ("0", "false", "")
EFFORT = os.environ.get("PI_EFFORT", "").strip()
MAX_TURNS = int(os.environ.get("PI_MAX_TURNS", "200"))
MAX_EMPTY = int(os.environ.get("PI_MAX_EMPTY", "3"))
CONTEXT = int(os.environ.get("PI_CONTEXT", "0"))
WARN_TURNS = int(os.environ.get("PI_WARN_TURNS", "5"))
SLC = os.environ.get("PI_SLC", str(HERE.parent / "_build/self/slc"))
OCAMLOPT = ["ocamlfind", "ocamlopt", "-package", "zarith,unix", "-linkpkg"]
SLC_TIMEOUT, BUILD_TIMEOUT, RUN_TIMEOUT = 60, 120, int(os.environ.get("PI_RUN_TIMEOUT", "10"))
MAX_WRITE, MAX_OUT = 8 * 1024 * 1024, 20000
RUN_DIR = SANDBOX_ROOT = ROOT_FD = LOG_PATH = TRANSCRIPT = None
_LOG_N = 0

SYSTEM = """You are an expert programmer working inside a sandbox directory.
You read, write and edit files, and compile and run programs with the `sl` tool.

- Be concise. Prefer doing over explaining.
- Use the tools to verify claims rather than guessing; never report success you have not checked.
- There is no shell. The only way to execute code is the `sl` tool.
- When the task is complete, call `done` with a short summary. If you get stuck and cannot
  make progress, call `done` anyway and say what is wrong.

All paths are relative to the sandbox root. This directory is your whole world: paths that
leave it (absolute paths, .., symlinks) are rejected, and files outside it do not exist for you."""


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
    flags = os.O_WRONLY | os.O_CREAT | os.O_TRUNC | os.O_NOFOLLOW | getattr(os, "O_CLOEXEC", 0)
    with os.fdopen(_open_in(user_path, flags, create=True), "wb") as f:
        return f.write(data)


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


def _proc(cmd, cwd, timeout, stdin="", env=None):
    try:
        return subprocess.run(cmd, cwd=cwd, input=stdin.encode(), capture_output=True, timeout=timeout, env=env)
    except subprocess.TimeoutExpired:
        return None


def _text(b):
    return b.decode("utf-8", "replace")


def sl(paths, stdin="", args=()):
    if isinstance(paths, str):
        paths = [paths]
    with tempfile.TemporaryDirectory(prefix="pi-sl-") as tmp:
        src = Path(tmp, "src")
        names = []
        for p in paths:
            name = "/".join(_rel_parts(p))
            (src / name).parent.mkdir(parents=True, exist_ok=True)
            (src / name).write_bytes(read_bytes(p))
            names.append(name)
        c = _proc([SLC, "--confine-dir", ".", "--no-env", *names], src, SLC_TIMEOUT, env={})
        if c is None:
            return f"compile: timed out after {SLC_TIMEOUT}s"
        warnings = clip(_text(c.stderr))
        if c.returncode:
            return f"compile: failed (exit {c.returncode})\n{warnings}"
        Path(tmp, "p.ml").write_bytes(c.stdout)
        b = _proc(OCAMLOPT + ["p.ml", "-o", "p"], tmp, BUILD_TIMEOUT)
        if b is None or b.returncode:
            shutil.copy(Path(tmp, "p.ml"), RUN_DIR / f"build-failure-{time.time():.0f}.ml")
            with open(RUN_DIR / "build-failures.log", "ab") as f:
                f.write(b"timeout\n" if b is None else b.stdout + b.stderr)
            return "internal error: the compiler's output failed to build; this is not your program's fault"
        r = _proc([str(Path(tmp, "p")), *map(str, args)], SANDBOX_ROOT, RUN_TIMEOUT, stdin, env={})
        head = f"compile: ok\n{warnings}" if warnings else "compile: ok"
        if r is None:
            return f"{head}\nrun: timed out after {RUN_TIMEOUT}s"
        return f"{head}\nrun: exit {r.returncode}\n--- stdout ---\n{clip(_text(r.stdout))}\n--- stderr ---\n{clip(_text(r.stderr))}"


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
               "Returns the compiler's messages, then the program's exit code, stdout and stderr.",
           {"paths": STRS, "stdin": STR, "args": STRS}, ["paths"]),
    "done": (done, "Call this when the task is complete, or when you cannot make further progress. "
                   "Pass a one-line summary. This ends the session, so verify your work before calling it.",
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
            "tools": [{"name": n, "description": d, "input_schema": PARAMS[n]} for n, (_, d, _, _) in TOOLS.items()],
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
            "tools": [{"type": "function", "function": {"name": n, "description": d, "parameters": PARAMS[n]}} for n, (_, d, _, _) in TOOLS.items()],
            "messages": [{"role": "system", "content": SYSTEM}] + messages,
            "user": RUN_DIR.name,
        }
        if EFFORT:
            body["reasoning_effort"] = EFFORT
        if STREAM:
            body.update(stream=True, stream_options={"include_usage": True})
        return post(self.base + "/chat/completions", body, {**self.auth(), "x-nw-conversation-id": RUN_DIR.name}, stream=STREAM)

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
        return
    n = usage.get("total_tokens") or sum(usage.get(k) or 0 for k in
                                         ("input_tokens", "cache_read_input_tokens", "cache_creation_input_tokens", "output_tokens"))
    line = f"[context: {n:,}" + (f" / {window:,} ({100 * n / window:.1f}%)]" if window else "]")
    _say(line)
    _log(TRANSCRIPT, f"\n{line}\n")


def run(prompt):
    api = ADAPTERS[PROVIDER]()
    messages, empty = [{"role": "user", "content": prompt}], 0
    for turn in range(MAX_TURNS):
        reply = api.send(messages)
        _context(reply.get("usage"), CONTEXT or api.window())
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
        if not calls:
            return text
        outs = []
        for c in calls:
            _log(TRANSCRIPT, f"\n>>> {_ts()} {c['name']}" + "".join(
                f"\n  {k}:\n{v}" if isinstance(v, str) and "\n" in v else f" {k}={json.dumps(v, ensure_ascii=False)}"
                for k, v in c["input"].items()) + (f"\n  (invalid arguments) {c['bad']}" if "bad" in c else "") + "\n")
            try:
                if "bad" in c:
                    raise ValueError(f"the arguments were not valid JSON, so the call was not run: {c['bad'][:300]}")
                out = TOOLS[c["name"]][0](**c["input"])
            except Exception as e:
                out = f"error: {e}"
            _say(f"[{c['name']}] {str(c['input'])[:70]}")
            _log(TRANSCRIPT, f"<<< {_ts()}\n{out}\n")
            outs.append(out)
        for c, out in zip(calls, outs):
            if c["name"] == "done" and "bad" not in c:
                return out
        left = MAX_TURNS - turn - 1
        if 0 < left <= WARN_TURNS:
            note = f"\n\n[{left} turn{'s' * (left != 1)} left: make sure your results are written to files, then call `done`.]"
            outs[-1] += note
            _log(TRANSCRIPT, note.lstrip() + "\n")
        messages += api.results(calls, outs)
    return f"(stopped after {MAX_TURNS} turns)"


def main(argv):
    global RUN_DIR, SANDBOX_ROOT, ROOT_FD, LOG_PATH, TRANSCRIPT
    seeds = []
    while argv[:1] == ["-f"] and len(argv) > 1:
        seeds.append(Path(argv[1]))
        argv = argv[2:]
    if not argv:
        sys.exit("usage: pi.py [-f PATH]... PROMPT-FILE ...   (the prompt files are joined into one prompt;\n"
                 "        each -f file or directory is copied into the sandbox root under its own name)")
    for s in seeds:
        if not s.exists():
            sys.exit(f"no such file: {s}")
    if len({s.resolve().name for s in seeds}) < len(seeds):
        sys.exit("two -f paths share a name")
    if PROVIDER not in ADAPTERS:
        sys.exit(f"unknown provider {PROVIDER!r}; try: {', '.join(ADAPTERS)}")
    if not os.access(SLC, os.X_OK):
        sys.exit(f"no slc at {SLC}; build it with the first step of self/bootstrap.sh")
    prompt = "\n\n".join(Path(a).read_text().strip() for a in argv)
    tag = "+".join(Path(a).stem for a in argv)
    RUN_DIR = HERE / "results" / f"{time.strftime('%Y%m%d-%H%M%S')}-{MODEL.replace('/', '_')}-{tag}"
    RUN_DIR.mkdir(parents=True)
    latest = RUN_DIR.parent / "latest"
    latest.unlink(missing_ok=True)
    latest.symlink_to(RUN_DIR.name)
    SANDBOX_ROOT = Path(tempfile.mkdtemp(prefix="sandbox-")).resolve()
    ROOT_FD = os.open(SANDBOX_ROOT, os.O_RDONLY | os.O_DIRECTORY)
    (RUN_DIR / "sandbox").symlink_to(SANDBOX_ROOT)
    LOG_PATH, TRANSCRIPT = RUN_DIR / "requests.log", RUN_DIR / "transcript.log"
    (RUN_DIR / "prompt.txt").write_text(prompt)
    _log(TRANSCRIPT, f"=== {PROVIDER}/{MODEL} {time.strftime('%Y-%m-%d %H:%M:%S')}\n"
                     + "".join(f"--- seed {s} ---\n" for s in seeds) + f"--- prompt ---\n{prompt}\n")
    _say(f"run dir: {RUN_DIR}")
    t0 = time.time()
    try:
        for s in seeds:
            dst = SANDBOX_ROOT / s.resolve().name
            shutil.copytree(s, dst) if s.is_dir() else shutil.copy(s, dst)
        answer = run(prompt)
        (RUN_DIR / "answer.txt").write_text(f"{answer}\n\n({time.time() - t0:.0f}s)\n")
        print(answer)
    finally:
        (RUN_DIR / "sandbox").unlink()
        shutil.copytree(SANDBOX_ROOT, RUN_DIR / "sandbox", symlinks=True)
        shutil.rmtree(SANDBOX_ROOT)


if __name__ == "__main__":
    main(sys.argv[1:])
