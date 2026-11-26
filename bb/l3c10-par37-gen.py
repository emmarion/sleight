import sys,os,importlib.util
sys.set_int_max_str_digits(0); sys.setrecursionlimit(1000000)
spec=importlib.util.spec_from_file_location('pg',os.path.join(os.path.dirname(os.path.abspath(__file__)),'l3c10-par-gen.py'))
pg=importlib.util.module_from_spec(spec); spec.loader.exec_module(pg)
B=64; CH=1500
def expand(t):
    if t[0]=='lit': return t[1]
    if t[0]=='rep': return t[2]*t[1]
    return ev(pg.parse(pg.emit([t])))
def dig(xs,s):
    cut=len(xs)%CH or CH
    for c in reversed([xs[:cut]]+[xs[i:i+CH] for i in range(cut,len(xs),CH)]):
        b=max(c)+1; n=0
        for d in reversed(c): n=n*b+d
        s=f"(PDig {len(c)} {b} {n} {s})"
    return s
def emit(terms,s="(PNil)"):
    out=[]
    for t in terms:
        xs=expand(t) if t[0]!='trn' or t[2]<B else None
        if xs is None or not all(x<B for x in xs):
            xs=[t] if t[0]!='lit' else [('big',x) if x>=B else x for x in t[1]]
        for x in xs:
            kind='flat' if isinstance(x,int) else 'old'
            if out and out[-1][0]==kind: out[-1][1].append(x)
            else: out.append((kind,[x]))
    for kind,xs in reversed(out):
        if kind=='flat' and len(xs)>8: s=dig(xs,s)
        else:
            ts=[('lit',[x if isinstance(x,int) else x[1]]) if isinstance(x,int) or x[0]=='big' else x for x in xs]
            s=f"(PG {pg.emit(pg.merge(ts))} {s})"
    return s
def ev(e):
    if isinstance(e,str): return int(e)
    h=e[0]
    if h=='GNil': return []
    if h=='GCons': return [ev(e[1])]+ev(e[2])
    if h=='PNil': return []
    if h=='PG': return ev(e[1])+ev(e[2])
    if h=='PDig':
        k,b,n=[ev(x) for x in e[1:4]]; out=[]
        for _ in range(k): n,r=divmod(n,b); out.append(r)
        return out+ev(e[4])
    if h=='GRep': return ev(e[2])*ev(e[1])+ev(e[3])
    if h=='GTrn':
        k,v,a,c,s=[ev(x) for x in e[1:6]]; pre,post=ev(e[6][1]),ev(e[6][2]); acc=ev(e[7])
        for _ in range(k): acc=pre+[v]+post+acc; w=a*v+c; assert w>=s; v=w-s
        return acc
    if h=='MkPQ':
        alt=lambda b,ns:[((b+i)%2,n) for i,n in enumerate(ns)]
        return (ev(e[1]),'BTrue' if e[2][0]=='BTrue' else 'BFalse',alt(e[3][0]=='BTrue',ev(e[4])),alt(e[5][0]=='BTrue',ev(e[6])))
    raise Exception(h)
def gen(cfg):
    q,h,L,R=cfg
    hb='(BTrue)' if h=='BTrue' else '(BFalse)'
    bl='(BTrue)' if L and L[0][0] else '(BFalse)'
    br='(BTrue)' if R and R[0][0] else '(BFalse)'
    for S in (L,R): assert all(S[i][0]!=S[i+1][0] for i in range(len(S)-1))
    tl=pg.merge(pg.fit([n for b,n in L])); tr=pg.merge(pg.fit([n for b,n in R]))
    return f"(MkPQ {q} {hb} {bl} {emit(tl)} {br} {emit(tr)})"
def side(t):
    a=t.split(); return [(int(a[2*j+1]),int(a[2*j+2])) for j in range(int(a[0]))]
def read(path):
    with open(path) as f:
        if f.read(1)=='(':
            import ast; f.seek(0); return ast.literal_eval(f.read())
        f.seek(0)
        q,h=map(int,f.readline().split()); L=side(f.readline()); R=side(f.readline())
    return (q,'BTrue' if h else 'BFalse',L,R)
def goal(exp,last,cks):
    bl="(MkConf (Zero) (Nil (Bool)) (BFalse) (Nil (Bool)))"; N="1"+"0"*exp
    mv=[0]+[m for m,_ in cks]; k=len(cks)
    out=["(let ((many g0)) (MkPQ 0 (BFalse) (BFalse) (PNil) (BFalse) (PNil)))"]
    for i,(m,path) in enumerate(cks):
        cfg=read(path); g=gen(cfg); assert ev(pg.parse(g))==cfg
        out.append(f"(let ((many g{i+1})) {g})")
    for i in range(k): out.append(f"(def-fns _ $ (many piece{i} : -> (many (Res (ReachP l3 g{i} g{i+1})) r)) (rp-run {mv[i+1]-mv[i]} g{i} g{i+1}))")
    out.append(f"(def-fns _ $ (many piece{k} : -> (many (Res (SpanP l3 g{k} {N})) r)) (rp-span {last-mv[k]} {N} g{k}))")
    out.append(f"(let ({' '.join(f'(many r{i})' for i in range(k+1))}) (native-compute {' '.join(f'piece{i}' for i in range(k+1))}))")
    out+= [f"(comptime-match many r{i} (ROk _ q{i}))" for i in range(k+1)]
    out.append(f"(let-match erased q{k} (MkSpanP _ _ _ lv span-last))")
    ch="(rchp0)"
    for i in range(k): ch=f"(rchp-cat l3 _ g{i} g{i+1} {ch} q{i})"
    out.append(f"(let ((erased span)) (span-last {ch}))")
    out.append(f"""
(def-fns _ $ (erased bound : (erased (Nat) k) (erased (HaltsAt l3 {bl} k) h) -> (erased (Lt {N} k) p))
  (span-bound l3 _ {N} k span h))

(goal erased (NoHaltBelow l3 {bl} {N}))
(qed (MkNHB l3 _ {N} (level-of bound) bound))""")
    return "\n".join(out)+"\n"
if __name__=='__main__' and sys.argv[1]=='--goal':
    cks=[(int(m),p) for m,p in (a.split('=') for a in sys.argv[4:])]
    sys.stdout.write(goal(int(sys.argv[2]),int(sys.argv[3]),cks))
elif __name__=='__main__':
    for arg in sys.argv[1:]:
        name,path=arg.split('=')
        cfg=read(path); s=gen(cfg)
        assert ev(pg.parse(s))==cfg
        print(f"(let ((many {name})) {s})")
