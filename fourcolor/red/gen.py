import re, sys

src = open(sys.argv[1]).read()
defs = re.findall(r'Definition cf(\d+) := Config(\*?)([^.]*)\.', src)

def step(t):
    return {'H': 1, 'Y': 2}.get(t) or int(t) + 3

def config(star, body):
    toks = body.split()
    k = next(i for i, t in enumerate(toks) if not t.isdigit())
    return [1 if star else 0] + [int(t) + 1 for t in toks[:k]] + [0] + [step(t) for t in toks[k:]] + [0]

def literal(bs):
    return '"%s"' % ''.join(chr(b) if 32 <= b < 127 and chr(b) not in '"\\' else '\\x%02x' % b for b in bs)

print('(let ((many config-srcs)) $ %sNil _)' % ''.join('Cons _ %s\n  $ ' % literal(config(star, body)) for _, star, body in defs))
