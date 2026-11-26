import sys,os,importlib.util
sys.set_int_max_str_digits(0); sys.setrecursionlimit(1000000)
def load(name,file):
    spec=importlib.util.spec_from_file_location(name,os.path.join(os.path.dirname(os.path.abspath(__file__)),file))
    m=importlib.util.module_from_spec(spec); spec.loader.exec_module(m); return m
p110=load('p110','l3c10-par110-gen.py'); pg=p110.pg
TAGS={'PNil':0,'PDig':1,'PG':2,'GNil':0,'GCons':1,'GRep':2,'GTrn':3}
def bnum(n,out):
    while n: n,d=divmod(n,255); out.append(d+1)
    out.append(0)
def benc(e):
    out=bytearray(); st=[e]
    while st:
        x=st.pop()
        if isinstance(x,str): bnum(int(x),out); continue
        h=x[0]
        if h in('BTrue','BFalse'): out.append(int(h=='BTrue')); continue
        if h=='MkGBlk': st+=[x[2],x[1]]; continue
        if h=='MkPQ': st+=x[:0:-1]; continue
        out.append(TAGS[h]); st+=x[:0:-1]
    return bytes(out)
def bdec(b):
    pos=0
    def byte():
        nonlocal pos
        pos+=1; return b[pos-1]
    def num():
        ds=[]
        while (d:=byte()): ds.append(d-1)
        n=0
        for d in reversed(ds): n=n*255+d
        return str(n)
    def bit(): return ['BTrue' if byte() else 'BFalse']
    def gen(p):
        t=byte(); hs=(['PNil','PDig','PG'] if p else ['GNil','GCons','GRep','GTrn'])[t]
        if hs=='PDig': return [hs,num(),num(),num(),gen(1)]
        if hs=='PG': return [hs,gen(0),gen(1)]
        if hs=='GCons': return [hs,num(),gen(0)]
        if hs=='GRep': return [hs,num(),gen(0),gen(0)]
        if hs=='GTrn': ns=[num() for _ in range(5)]; bf=gen(0); af=gen(0); return [hs]+ns+[['MkGBlk',bf,af],gen(0)]
        return [hs]
    q=num(); h=bit(); bl=bit(); gl=gen(1); br=bit(); gr=gen(1)
    assert pos==len(b)
    return ['MkPQ',q,h,bl,gl,br,gr]
def lit(b):
    return '"'+''.join(chr(c) if 32<=c<127 and c not in (34,92) else '\\x%02x'%c for c in b)+'"'
def ckbytes(src):
    g=p110.ckgen(src); e=pg.parse(g); b=benc(e); assert bdec(b)==e,src; return b
def fastfit(xs):
    import bisect
    big=[t for t,x in enumerate(xs) if x>10**6]; terms=[];i=0;n=len(xs)
    while i<n:
        best=(1,('lit',[xs[i]]))
        for p in range(1,13):
            k=1
            while i+(k+1)*p<=n and xs[i+k*p:i+(k+1)*p]==xs[i:i+p]: k+=1
            if k>1 and k*p>best[0]: best=(k*p,('rep',k,xs[i:i+p]))
        b=bisect.bisect_left(big,i); bg=[t for t in big[b:b+2] if t<i+2000]
        cands=[(p,j) for p in range(1,7) for j in range(p)]
        if len(bg)==2 and bg[1]-bg[0]>=7 and bg[0]-i<bg[1]-bg[0]: cands.append((bg[1]-bg[0],bg[0]-i))
        for p,j in cands:
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
            while i+(k+1)*p<=n and same(k) and (w(k-2)-w(k-1))==a*(w(k-1)-w(k)): k+=1
            v0=w(k-1); o=w(k-2)-a*v0
            if k*p>best[0]: best=(k*p,('trn',k,v0,a,max(o,0),max(-o,0),b0[:j],b0[j+1:]))
        terms.append(best[1]); i+=best[0]
    return terms
pg.fit=fastfit
def segs(t):
    if t[0]=='lit': return [t[1]]
    if t[0]=='rep': return [t[2]]*t[1]
    k,v,a,c,s,pre,post=t[1:]; out=[]
    for _ in range(k): out.append(pre+[(post[0][0],v)]+post[1:]); v=a*v+c-s
    return out
def refit(items,b0,V):
    pos=len(V); kept=[]
    def match(sg):
        return len(sg)<=pos and all(V[pos-len(sg)+i]==n and (b0+pos-len(sg)+i)%2==b for i,(b,n) in enumerate(sg))
    for t in reversed(items):
        sg=segs(t); j=0
        while j<len(sg) and match(sg[j]): pos-=len(sg[j]); j+=1
        if j==len(sg): kept.append(t); continue
        if j and t[0]=='rep': kept.append(('rep',j,t[2]))
        if j and t[0]=='trn': kept.append(('trn',j)+t[2:])
        break
    print('refit kept',len(kept),'of',len(items),'head',pos,file=sys.stderr)
    return ([('lit',[((b0+i)%2,V[i]) for i in range(pos)])] if pos else [])+kept[::-1]
def side_vals(f):
    rest=b''; V=[]; n=None; b0=0; i=0
    while True:
        at=f.tell(); c=f.read(1<<26); nl=c.find(b'\n')
        if nl>=0: f.seek(at+nl+1); c=c[:nl]
        ws=(rest+c).split(b' ')
        rest=ws.pop() if nl<0 else b''
        for w in ws:
            if not w: continue
            if n is None: n=int(w)
            elif i%2==0: b0=int(w) if i==0 else b0; i+=1
            else: V.append(int(w)); i+=1
        if nl>=0: assert len(V)==n; return b0,V
def dump(path,mv):
    with open(path,'rb') as f:
        for l in f:
            if l==b'C %d\n'%mv: break
        q,h=map(int,f.readline().split())
        return q,h,side_vals(f),side_vals(f)
def fitq(path,mv,tmpl):
    q,h,L,R=dump(path,mv); _,_,TL,TR=p110.coq(tmpl); out=[]
    for items,(b0,V) in ((TL,L),(TR,R)):
        out.append(('(BTrue)' if V and b0 else '(BFalse)',p110.emit(p110.terms(refit(items,b0,V)))))
    (bl,gl),(br,gr)=out
    return f"(let ((many g)) (MkPQ {q} ({'BTrue' if h else 'BFalse'}) {bl} {gl} {br} {gr}))"
BL="(MkConf (Zero) (Nil (Bool)) (BFalse) (Nil (Bool)))"
def goal(exp,script,cks,order=None):
    N="1"+"0"*exp; sc=open(script).read().split()
    pts=[(0,0,None)]+[tuple(map(int,c.split('=')[0].split(':')))+(c.split('=')[1] if '=' in c else None,) for c in cks]
    k=len(pts)-1; out=[]
    for i,(_,_,src) in enumerate(pts):
        if src: out.append(f"(let ((many g{i})) {lit(ckbytes(src))})")
    for i in range(k):
        (m0,s0,_),(m1,s1,_)=pts[i],pts[i+1]; assert s0==0 or m1==m0
        xs=sc[s0:s1]; scr=f'(rd-nats {len(xs)} "{" ".join(xs)}")' if xs else "(values (Nil (Nat)) \"\")"
        if i==0: call,ty=f"(rb-first {m1-m0} sc g1)",f"(RchB l3 {BL} g1)"
        elif i<k-1: call,ty=f"(rb-run {m1-m0} sc g{i} g{i+1})",f"(ReachB l3 g{i} g{i+1})"
        else: call,ty=f"(rb-span {m1-m0} sc {N} g{i})",f"(SpanB l3 g{i} {N})"
        out.append(f"(def-fns _ $ (many piece{i} : -> (many (Res {ty}) r))\n  (let ((many sc) (many _)) {scr})\n  {call})")
    od=order or list(range(k)); assert sorted(od)==list(range(k))
    out.append(f"(let ({' '.join(f'(many r{i})' for i in od)}) (native-compute {' '.join(f'piece{i}' for i in od)}))")
    out+=[f"(comptime-match many r{i} (ROk _ q{i}))" for i in range(k)]
    out.append(f"(let-match erased q{k-1} (MkSpanB _ _ _ lv span-last))")
    ch="q0"
    for i in range(1,k-1): ch=f"(rchb-cat l3 _ g{i} g{i+1} {ch} q{i})"
    out.append(f"(let ((erased span)) (span-last {ch}))")
    out.append(f"""
(def-fns _ $ (erased bound : (erased (Nat) k) (erased (HaltsAt l3 {BL} k) h) -> (erased (Lt {N} k) p))
  (span-bound l3 _ {N} k span h))

(goal erased (NoHaltBelow l3 {BL} {N}))
(qed (MkNHB l3 _ {N} (level-of bound) bound))""")
    return "\n".join(out)+"\n"
if __name__=='__main__' and sys.argv[1]=='--fit':
    print(fitq(sys.argv[2],int(sys.argv[3]),sys.argv[4]))
elif __name__=='__main__' and sys.argv[1]=='--goal':
    a=sys.argv[4:]; od=[int(x) for x in a.pop(0)[8:].split(',')] if a[0].startswith('--order=') else None
    sys.stdout.write(goal(int(sys.argv[2]),sys.argv[3],a,od))
elif __name__=='__main__':
    for arg in sys.argv[1:]:
        name,src=arg.split('=')
        print(f"(let ((many {name})) {lit(ckbytes(src))})")
