import re, sys

src = open(sys.argv[1]).read()
R = ['Pr%d%d' % (a, b) for a in range(5, 10) for b in range(a, 10)]

def table(name):
    body = re.search(r"Definition %s r r' :=\s*match r', r with(.*?)end\." % name, src, re.S).group(1)
    rows = re.findall(r"\|\s*(\w+)\s*,\s*(\w+)\s*=>\s*([\w']+)", body)
    def look(r, r2):
        for a, b, c in rows:
            if a in (r2, '_') and b in (r, '_'):
                return {'r': r, "r'": r2}.get(c, c)
    return look

lo, hi = (lambda r: int(r[2])), (lambda r: int(r[3]))

def cmp(r, r2):
    if lo(r2) <= lo(r) and hi(r) <= hi(r2):
        return 'Psubset'
    if hi(r) < lo(r2) or hi(r2) < lo(r):
        return 'Pdisjoint'
    return 'Pstraddle'

cr, mr = table('cmp_range'), table('meet_range')
bad = [(r, r2) for r in R for r2 in R if cr(r, r2) != cmp(r, r2)]
bad += [(r, r2) for r in R for r2 in R if cmp(r, r2) != 'Pdisjoint'
        and mr(r, r2) != 'Pr%d%d' % (max(lo(r), lo(r2)), min(hi(r), hi(r2)))]
print('mismatches:', bad)
