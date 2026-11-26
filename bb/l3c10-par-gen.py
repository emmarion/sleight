import sys,re
sys.set_int_max_str_digits(0); sys.setrecursionlimit(1000000)
def fit(xs):
    terms=[];i=0;n=len(xs)
    while i<n:
        best=(1,('lit',[xs[i]]))
        for p in range(1,13):
            k=1
            while i+(k+1)*p<=n and xs[i+k*p:i+(k+1)*p]==xs[i:i+p]: k+=1
            if k>1 and k*p>best[0]: best=(k*p,('rep',k,xs[i:i+p]))
        big=[t for t in range(i,min(n,i+2000)) if xs[t]>10**6][:2]
        cands=[(p,j) for p in range(1,7) for j in range(p)]
        if len(big)==2 and big[1]-big[0]>=7 and big[0]-i<big[1]-big[0]: cands.append((big[1]-big[0],big[0]-i))
        for p,j in cands:
            if True:
                if i+3*p>n: break
                b0=xs[i:i+p]
                def blk(t): return xs[i+t*p:i+(t+1)*p]
                def same(t):
                    bt=blk(t); return len(bt)==p and bt[:j]==b0[:j] and bt[j+1:]==b0[j+1:]
                if not (same(1) and same(2)): continue
                w=lambda t: blk(t)[j]
                e1=w(0)-w(1); e2=w(1)-w(2)
                if e2<=0 or e1%e2 or e1//e2<2: continue
                a=e1//e2; k=3
                while i+(k+1)*p<=n and same(k) and (w(k-2)-w(k-1))==a*(w(k-1)-w(k)) : k+=1
                v0=w(k-1); o=w(k-2)-a*v0
                if k*p>best[0]:
                    best=(k*p,('trn',k,v0,a,max(o,0),max(-o,0),b0[:j],b0[j+1:]))
        terms.append(best[1]); i+=best[0]
    return terms
def lst(xs,acc):
    s=acc
    for x in reversed(xs): s=f"(GCons {x} {s})"
    return s
def emit(terms,s="(GNil)"):
    for t in reversed(terms):
        if t[0]=='lit': s=lst(t[1],s)
        elif t[0]=='rep': s=f"(GRep {t[1]} {lst(t[2],'(GNil)')} {s})"
        else:
            k,d,a,c,sb,pre,post=t[1:]
            s=f"(GTrn {k} {d} {a} {c} {sb} (MkGBlk {emit(merge(fit(pre)))} {emit(merge(fit(post)))}) {s})"
    return s
def merge(terms):
    out=[]
    for t in terms:
        if t[0]=='lit' and out and out[-1][0]=='lit': out[-1]=('lit',out[-1][1]+t[1])
        else: out.append(t)
    return out
def gen(cfg):
    q,h,L,R=cfg
    hb='(BTrue)' if h=='BTrue' else '(BFalse)'
    bl='(BTrue)' if L and L[0][0] else '(BFalse)'
    br='(BTrue)' if R and R[0][0] else '(BFalse)'
    tl=merge(fit([n for b,n in L])); tr=merge(fit([n for b,n in R]))
    for S in (L,R):
        assert all(S[i][0]!=S[i+1][0] for i in range(len(S)-1))
    return f"(MkQGen {q} {hb} {bl} {emit(tl)} {br} {emit(tr)})", tl, tr
def parse(s):
    toks=re.findall(r'\(|\)|[^\s()]+',s); pos=0
    def rd():
        nonlocal pos
        t=toks[pos]; pos+=1
        if t=='(':
            out=[]
            while toks[pos]!=')': out.append(rd())
            pos+=1; return out
        return t
    return rd()
def ev(e):
    if isinstance(e,str): return int(e)
    h=e[0]
    if h=='GNil': return []
    if h=='GCons': return [ev(e[1])]+ev(e[2])
    if h=='MkGBlk': return (ev(e[1]),ev(e[2]))
    if h=='BTrue': return 1
    if h=='BFalse': return 0
    if h=='GRep': return ev(e[2])*ev(e[1])+ev(e[3])
    if h=='GTrn':
        k,v,a,c,s=[ev(x) for x in e[1:6]]; pre,post=ev(e[6]);acc=ev(e[7])
        for _ in range(k): acc=pre+[v]+post+acc; w=a*v+c; assert w>=s; v=w-s
        return acc
    if h=='MkQGen':
        q=ev(e[1]);hh=ev(e[2]);bl=ev(e[3]);L=ev(e[4]);br=ev(e[5]);R=ev(e[6])
        alt=lambda b,ns:[((b+i)%2,n) for i,n in enumerate(ns)]
        return (q,'BTrue' if hh else 'BFalse',alt(bl,L),alt(br,R))
    raise Exception(h)
def configs(path):
    lines=open(path).read().split('\n'); out={}
    for i,l in enumerate(lines):
        if l.startswith('C '):
            q,h=map(int,lines[i+1].split())
            side=lambda t:(lambda a:[(a[2*j+1],a[2*j+2]) for j in range(a[0])])(list(map(int,t.split())))
            out[int(l.split()[1])]=(q,'BTrue' if h else 'BFalse',side(lines[i+2]),side(lines[i+3]))
    return out
if __name__=='__main__':
    cfgs=configs(sys.argv[1])
    for arg in sys.argv[2:]:
        name,mv=arg.split('=')
        s,_,_=gen(cfgs[int(mv)])
        assert ev(parse(s))==cfgs[int(mv)]
        print(f"(let ((many {name})) {s})")
