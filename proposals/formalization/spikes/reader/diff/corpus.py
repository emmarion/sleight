import glob, os, re, subprocess, sys, tempfile
from concurrent.futures import ThreadPoolExecutor
here = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(here, '..', '..', '..', '..', '..'))
MAIN = os.environ.get('REF', os.path.join(ROOT, '_build/default/bin/main.exe'))
SLC = os.environ.get('SLC', os.path.join(ROOT, '_build/release/slc'))
S4 = os.path.dirname(here)
jobs = int(sys.argv[1]) if len(sys.argv) > 1 else 2
tmp = tempfile.mkdtemp(prefix='reader-corpus.')
proto = os.path.join(tmp, 'reader')
subprocess.run([SLC] + [os.path.join(S4, f) for f in ['syntax.sl', 'read.sl', 'show.sl', 'cli.sl']] + ['--build', proto], check=True, capture_output=True)
def unliteral(out):
    m = re.search(rb'^"(.*)"$', out, re.M | re.S)
    if not m:
        return None
    s, r, i = m.group(1), bytearray(), 0
    while i < len(s):
        if s[i:i + 1] == b'\\':
            e = s[i + 1:i + 2]
            if e == b'x':
                r.append(int(s[i + 2:i + 4], 16)); i += 4
            else:
                r += {b'n': b'\n', b't': b'\t'}.get(e, e); i += 2
        else:
            r.append(s[i]); i += 1
    return bytes(r)
def real(cmd, path):
    p = subprocess.run(cmd + ['--no-shape-note', os.path.join(here, 'showargs.sl'), path], capture_output=True)
    shown = unliteral(p.stdout)
    if shown is not None:
        return b'(show-args' + (b' ' + shown if shown else b'') + b')'
    m = re.search(rb'syntax error: (.*)', p.stderr)
    return b'error: ' + m.group(1) if m else b'OTHER: ' + (p.stderr + p.stdout)[:200]
def mine(text):
    out = subprocess.run([proto], input=text, capture_output=True).stdout.rstrip(b'\n')
    if out.startswith(b'error: '):
        return out
    return re.sub(rb'(?<![^ ()])(0|[1-9][0-9]*)(?![^ ()])', b'<literal>', out)
def check(path):
    content = open(path, 'rb').read()
    if b'"' in content or b'#\\' in content or b';!' in content:
        return (path, 'skipped', None)
    text = b'(show-args\n' + content + b'\n)'
    case = os.path.join(tmp, os.path.basename(path) + '.case.sl')
    open(case, 'wb').write(text)
    m, r, s = mine(text), real([MAIN], case), real([SLC, '--interpret'], case)
    os.remove(case)
    kind = 'rejected' if m.startswith(b'error: ') else 'accepted'
    return (path, kind if m == r == s else 'DIFFER', (m, r, s))
files = sorted(f for pat in ['tests/*.sl', 'mini/*.sl', 'std/*.sl', 'stlc/*.sl'] for f in glob.glob(os.path.join(ROOT, pat)))
counts = {}
with ThreadPoolExecutor(jobs) as pool:
    for path, verdict, detail in pool.map(check, files):
        counts[verdict] = counts.get(verdict, 0) + 1
        if verdict == 'DIFFER':
            print('DIFFER', path)
            for who, v in zip(['prototype', 'main.exe ', 'slc      '], detail):
                print('  ', who, v[:300])
        elif verdict == 'rejected':
            print('rejected by all three:', path, detail[0].decode())
os.remove(proto)
os.rmdir(tmp)
print('files:', len(files), counts)
