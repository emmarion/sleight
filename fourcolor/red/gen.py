import re, sys

src = open(sys.argv[1]).read()
defs = re.findall(r'Definition cf(\d+) := Config(\*?)([^.]*)\.', src)

def step(t):
    return {'H': '(SH)', 'Y': '(SY)'}.get(t, '(SR %s)' % t)

def seq(xs):
    return ''.join('Cons _ %s $ ' % x for x in xs) + 'Nil _'

out = []
for num, star, body in defs:
    toks = body.split()
    k = next(i for i, t in enumerate(toks) if not t.isdigit())
    out.append('(def-fns _ $ (many cf%s : -> (many (Config) c)) (MkConfig %s (%s) $ %s))' % (
        num, '(BTrue)' if star else '(BFalse)', seq(toks[:k]), seq(map(step, toks[k:]))))
names = ['(cf%s)' % n for n, _, _ in defs]
chunks = [names[i:i + 20] for i in range(0, len(names), 20)]
for i, c in enumerate(chunks):
    out.append('(def-fns _ $ (many cfs%02d : -> (many (List (Config)) cs)) (%s))' % (i, seq(c)))
out.append('(def-fns _ $ (many config-chunks : -> (many (List (List (Config))) css)) (%s))'
           % seq('(cfs%02d)' % i for i in range(len(chunks))))
print('\n'.join(out))
