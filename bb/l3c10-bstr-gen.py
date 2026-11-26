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
BL="(MkConf (Zero) (Nil (Bool)) (BFalse) (Nil (Bool)))"
def goal(exp,script,cks):
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
    out.append(f"(let ({' '.join(f'(many r{i})' for i in range(k))}) (native-compute {' '.join(f'piece{i}' for i in range(k))}))")
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
if __name__=='__main__' and sys.argv[1]=='--goal':
    sys.stdout.write(goal(int(sys.argv[2]),sys.argv[3],sys.argv[4:]))
elif __name__=='__main__':
    for arg in sys.argv[1:]:
        name,src=arg.split('=')
        print(f"(let ((many {name})) {lit(ckbytes(src))})")
