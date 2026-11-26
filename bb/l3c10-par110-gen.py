import sys,os,re,importlib.util
sys.set_int_max_str_digits(0); sys.setrecursionlimit(1000000)
def load(name,file):
    spec=importlib.util.spec_from_file_location(name,os.path.join(os.path.dirname(os.path.abspath(__file__)),file))
    m=importlib.util.module_from_spec(spec); spec.loader.exec_module(m); return m
pg=load('pg','l3c10-par-gen.py'); p37=load('p37','l3c10-par37-gen.py')
B=64; FLAT=16
def coq(path):
    s=re.sub(r'\(\*.*?\*\)','',open(path).read(),flags=re.S)
    toks=re.findall(r'\+\+|:=|:|\(|\)|\[|\]|;|,|\.(?=\s|$)|[A-Za-z_][\w.]*|0x[0-9a-f]+|\d+',s); pos=0
    def peek(): return toks[pos]
    def eat(t=None):
        nonlocal pos
        x=toks[pos]; assert t is None or x==t,(x,t); pos+=1; return x
    def num():
        if peek()=='(': eat('('); v=num(); eat(')'); return v
        if peek()=='N.to_nat': eat(); return num()
        if peek()=='catN':
            eat(); eat('['); xs=[]
            while peek()!=']':
                if peek()==';': eat()
                else: xs.append(num())
            eat(']'); v=0
            for x in reversed(xs): v=x+(v<<32768)
            return v
        return int(eat(),0)
    def lst():
        eat('['); out=[]
        while peek()!=']':
            if peek()==';': eat(); continue
            if peek()=='(': eat('('); b=eat(); eat(','); n=num(); eat(')'); out.append((int(b=='S1'),n))
            else: out.append(eat()=='true')
        eat(']'); return out
    defs={}
    def atom():
        t=peek()
        if t=='(': eat('('); v=expr(); eat(')'); return v
        if t=='[': return [('lit',lst())]
        if t=='repL': eat(); k=num(); b=lst(); return [('rep',k,b)]+atom()
        if t=='trnD':
            eat(); j=num(); eat('('); f=eat(); m=num(); eat(')'); o=2**(m+1)-1 if f=='onesP' else 2**m
            z=eat()=='true'; sg=int(eat()=='S1'); lb=lst(); M=lst()
            k=len(lb); base=sum(1<<i for i,b in enumerate(lb) if b)
            st=lambda o:4*o if z else 4*o+3
            d=(0 if z else 3<<k)-3*base
            return [('trn',j,st(o)*2**k+base,4,max(d,0),max(-d,0),[],[(sg,None)]+M)]+atom()
        assert t not in ('trnU',),t
        eat(); return defs[t]
    def expr():
        v=atom()
        while peek()=='++': eat(); v=v+atom()
        return v
    while True:
        if peek()!='Definition': eat(); continue
        eat(); name=eat(); eat(':')
        if peek()=='rcfg':
            eat(); eat(':='); eat('('); q=eat(); eat(','); L=expr(); eat(','); h=eat(); eat(','); R=expr(); eat(')')
            return ("ABCDEF".index(q),'BTrue' if h=='S1' else 'BFalse',L,R)
        while peek()!=':=': eat()
        eat(':='); defs[name]=expr()
def flat(items):
    out=[]
    for t in items:
        if t[0]=='lit': out+=t[1]
        elif t[0]=='rep': out+=t[2]*t[1]
        else:
            k,v,a,c,s,pre,post=t[1:]; segs=[]
            for _ in range(k): segs.append(pre+[(post[0][0],v)]+post[1:]); v=a*v+c-s
            for sg in reversed(segs): out+=sg
    return out
def terms(items):
    out=[]; lit=[]
    def flush():
        if lit: out.extend(pg.merge(pg.fit(lit))); lit.clear()
    for t in items:
        if t[0]=='lit': lit.extend(n for b,n in t[1]); continue
        flush()
        if t[0]=='rep': out.append(('rep',t[1],[n for b,n in t[2]]))
        else: out.append(t[:6]+([n for b,n in t[6]],[n for b,n in t[7][1:]]))
    flush(); return out
def small(t):
    if t[0]=='lit': return t[1] if all(x<B for x in t[1]) else None
    if t[0]=='rep': xs=t[2]*t[1]
    else:
        if t[1]*(len(t[6])+len(t[7])+1)>FLAT: return None
        xs=ev(pg.parse(pg.emit([t])),[])[::-1]
    return xs if len(xs)<=FLAT and all(x<B for x in xs) else None
def emit(ts,s="(PNil)"):
    out=[]
    for t in ts:
        xs=small(t)
        if xs is None and t[0]=='lit': xs=[x if x<B else ('lit',[x]) for x in t[1]]
        for x in ([t] if xs is None else xs):
            kind='flat' if isinstance(x,int) else 'old'
            if out and out[-1][0]==kind: out[-1][1].append(x)
            else: out.append((kind,[x]))
    for kind,xs in reversed(out):
        s=p37.dig(xs,s) if kind=='flat' and len(xs)>8 else f"(PG {pg.emit(pg.merge([('lit',[x]) if isinstance(x,int) else x for x in xs]))} {s})"
    return s
def side_gen(items):
    S=flat(items); bits=[b for b,n in S]
    assert all(bits[i]!=bits[i+1] for i in range(len(bits)-1))
    return ('(BTrue)' if S and S[0][0] else '(BFalse)'), emit(terms(items)), S
def ev(e,racc):
    if isinstance(e,str): return int(e)
    h=e[0]
    if h in('GNil','PNil'): return racc
    if h=='GCons': r=ev(e[2],racc); r.append(ev(e[1],None)); return r
    if h=='PG': return ev(e[1],ev(e[2],racc))
    if h=='PDig':
        k,b,n=[ev(x,None) for x in e[1:4]]; out=[]
        for _ in range(k): n,r=divmod(n,b); out.append(r)
        r=ev(e[4],racc); r.extend(out[::-1]); return r
    if h=='GRep':
        r=ev(e[3],racc); blk=ev(e[2],[])
        for _ in range(ev(e[1],None)): r+=blk
        return r
    if h=='GTrn':
        k,v,a,c,s=[ev(x,None) for x in e[1:6]]; pre,post=ev(e[6][1],[]),ev(e[6][2],[]); r=ev(e[7],racc)
        for _ in range(k): r+=post; r.append(v); r+=pre; w=a*v+c; assert w>=s; v=w-s
        return r
    raise Exception(h)
def side_ev(b,g):
    xs=ev(g,[])[::-1]; return [((b+i)%2,n) for i,n in enumerate(xs)]
def hh(l):
    a=0
    for b,n in l: a=(a*1000003+2*n+b)%2305843009213693951
    return a
def gen(path):
    q,h,L,R=coq(path)
    bl,gl,SL=side_gen(L); br,gr,SR=side_gen(R)
    g=f"(MkPQ {q} ({h}) {bl} {gl} {br} {gr})"
    e=pg.parse(g); assert side_ev(e[3][0]=='BTrue',e[4])==SL and side_ev(e[5][0]=='BTrue',e[6])==SR
    print(q,int(h=='BTrue'),len(SL),len(SR),hh(SL),hh(SR),file=sys.stderr)
    return g
def ckgen(src):
    if src.endswith('.v'): return gen(src)
    t=open(src).read().strip()
    if t.startswith('(let'): return t[t.index('(MkPQ'):-1]
    cfg=p37.read(src); g=p37.gen(cfg); assert p37.ev(pg.parse(g))==cfg; return g
def goal(exp,script,cks):
    bl="(MkConf (Zero) (Nil (Bool)) (BFalse) (Nil (Bool)))"; N="1"+"0"*exp; sc=open(script).read().split()
    pts=[(0,0,None)]+[tuple(map(int,c.split('=')[0].split(':')))+(c.split('=')[1] if '=' in c else None,) for c in cks]
    k=len(pts)-2; out=["(let ((many g0)) (MkPQ 0 (BFalse) (BFalse) (PNil) (BFalse) (PNil)))"]
    out+=[f"(let ((many g{i})) {ckgen(src)})" for i,(_,_,src) in enumerate(pts) if src]
    for i in range(k+1):
        (m0,s0,_),(m1,s1,_)=pts[i],pts[i+1]; assert s0==0 or m1==m0
        xs=sc[s0:s1]; scr=f'(rd-nats {len(xs)} "{" ".join(xs)}")' if xs else "(values (Nil (Nat)) \"\")"
        call=f"(rp5-run {m1-m0} sc g{i} g{i+1})" if i<k else f"(rp5-span {m1-m0} sc {N} g{k})"
        ty=f"(ReachP l3 g{i} g{i+1})" if i<k else f"(SpanP l3 g{k} {N})"
        out.append(f"(def-fns _ $ (many piece{i} : -> (many (Res {ty}) r))\n  (let ((many sc) (many _)) {scr})\n  {call})")
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
    sys.stdout.write(goal(int(sys.argv[2]),sys.argv[3],sys.argv[4:]))
elif __name__=='__main__':
    for arg in sys.argv[1:]:
        name,path=arg.split('=')
        print(f"(let ((many {name})) {gen(path)})")
