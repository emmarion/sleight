import sys
d = sys.argv[1]
def rd(f):
    t = open(f"{d}/{f}.txt").read().split()
    q, h = t[0], t[1]; n = int(t[2]); L = t[3:3 + 2 * n]; i = 3 + 2 * n
    m = int(t[i]); R = t[i + 1:i + 1 + 2 * m]
    return q, h, L, R
def runs(xs):
    s = "(Nil (Rn))"
    for i in range(len(xs) - 2, -1, -2):
        s = f"(Cons _ (MkRn {'(BTrue)' if xs[i] == '1' else '(BFalse)'} {xs[i + 1]}) {s})"
    return s
def rq(f):
    q, h, L, R = rd(f)
    return f"(MkRq {q} {'(BTrue)' if h == '1' else '(BFalse)'} {runs(L)} {runs(R)})".replace(f"(MkRq {q} ", f"(MkRq {q} ", 1)
def rqv(f):
    q, h, L, R = rd(f)
    return f"(MkRq {q} {runs(L)} {'(BTrue)' if h == '1' else '(BFalse)'} {runs(R)})"
out = []
for nm, i, o in [("l0b", "l0bin", "preA"), ("l0a", "l0ain", "l0aout"), ("ax", "axin", "axout"),
                 ("f0", "fin0", "fout0"), ("f1", "fin1", "fout1"), ("f2", "fin2", "fout2")]:
    out.append(f"(let ((many fe-{nm}-in)) {rqv(i)})")
    out.append(f"(let ((many fe-{nm}-out)) {rqv(o)})")
    out.append(f"(def-fns _ $ (many chk-{nm} : -> (many (ErasedMaybe (FSq fe-{nm}-in fe-{nm}-out)) r))\n"
               f"  (let ((many ok) (many _) (many _)) (f-run 200000 fe-{nm}-in fe-{nm}-in (FsN fe-{nm}-in) fe-{nm}-out))\n  ok)")
    out.append(f"(let ((many ok-{nm})) (native-compute chk-{nm}))")
    out.append(f"(comptime-match many ok-{nm} (ESome _ cert-{nm}))")
    out.append(f"(let ((many fe-{nm})) (MkFE fe-{nm}-in fe-{nm}-out cert-{nm}))\n")
out.append("(let ((many tbl-l0)) (Cons _ fe-l0b $ Cons _ fe-l0a $ Nil (FE)))")
out.append("(let ((many tbl-ax)) (Cons _ fe-ax $ Nil (FE)))")
out.append("(let ((many tbl-frame)) (Cons _ fe-f0 $ Cons _ fe-f1 $ Cons _ fe-f2 $ Nil (FE)))")
print("\n".join(out))
