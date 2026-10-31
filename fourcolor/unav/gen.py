import re, sys

coq, out = sys.argv[1], sys.argv[2]

def rng(t):
    if t == '*':
        return 5, 9
    m = re.fullmatch(r'(\d)([+-]?)(?:\?(\d))?', t)
    a, sign, b = int(m.group(1)), m.group(2), m.group(3)
    return {'+': (a, 9), '-': (5, a)}.get(sign, (a, int(b) if b else a))

def rg(t):
    return '(MkRg %d %d)' % rng(t)

def seq(xs):
    return ''.join('Cons _ %s $ ' % x for x in xs) + 'Nil _'

def part(text):
    toks = re.findall(r'\$\[[^\]]*\]|\$|[^\s$]+', text)
    subs, i = [], 0
    assert toks[-1] == '$'
    while i < len(toks) - 1:
        head, s = toks[i], toks[i + 1]
        inner = head[2:-1].split() if head != '$' else ['*']
        subs.append('(pc %s %s)' % (rg(s), rg(inner[0])) if len(inner) == 1
                    else '(pf %s (%s))' % (rg(inner[0]), seq(map(rg, inner[1:]))))
        i += 2
    return '(%s)' % seq(subs)

dis = open(coq + '/discharge.v').read()
rules = dict(re.findall(r"Definition (drule\d+'?)\s*:= Part (.*?) \.", dis.replace('$.', '$ .')))
names = re.search(r'@seqn part 38(.*?)\.', dis, re.S).group(1).split()
lines = ['(def-fns _ $ (many base-drules : -> (many (List (List (Sub))) rs)) (%s))' % seq(part(rules[n]) for n in names)]

TAC = re.compile(r"Pcase\s*(\w*)\s*:\s*(s|h|f1|f2|f3)\[(\d+)\]\s*(<=|>)\s*(\d+)\.|(Reducible)\.|Hubcap\s+(.*?)\$\.|Similar to (\*?)(\w+)\[(\d+)\]\.", re.S)
LOC = {'s': 0, 'h': 1, 'f1': 2, 'f2': 3, 'f3': 4}

def hubcap(text):
    out = []
    cs = re.findall(r'\$\[(\d+)(?:,(\d+))?\]<=\(?(-?\d+)\)?', text)
    for i, j, b in cs:
        z = [max(int(b), 0), max(-int(b), 0)]
        out += ([2, int(i) - 1, int(j) - 1] if j else [1, int(i) - 1]) + z
    return [2, len(cs)] + out

def script(n):
    src = open('%s/present%d.v' % (coq, n)).read()
    body = src[src.index('Presentation red.') + len('Presentation red.'):src.index('Qed.')]
    toks = list(TAC.finditer(body))
    assert TAC.sub('', body).strip() == '', 'unparsed text in present%d.v' % n
    pos = [0]
    def goal(env):
        m = toks[pos[0]]
        pos[0] += 1
        if m.group(2):
            lab, loc, j, op, k = m.group(1, 2, 3, 4, 5)
            left = goal(env)
            right = goal(env + [lab] if lab else env)
            return [0, LOC[loc], int(j) - 1, int(k), int(op == '<='), int(bool(lab))] + left + right
        if m.group(6):
            return [1]
        if m.group(7) is not None:
            return hubcap(m.group(7))
        mir, lab, k = m.group(8, 9, 10)
        return [3, env[::-1].index(lab), int(mir == '*'), int(k)]
    nums = goal([])
    assert pos[0] == len(toks)
    return nums

def spell(nums):
    assert all(0 <= x <= 61 for x in nums)
    return ''.join('\\x5c' if x == 27 else chr(65 + x) for x in nums)

for n in range(5, 12):
    lines.append('(def-fns _ $ (many script%d : -> (many (Script) s)) (script-of "%s"))' % (n, spell(script(n))))
open(out, 'w').write('\n'.join(lines) + '\n')
