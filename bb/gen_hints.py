import sys
n=int(sys.argv[1]); LIM=30
opts=[(w,d,q) for q in reversed(range(n)) for w in (0,1) for d in (0,1)]+['H']
def run(M,lim):
    tape={}; pos=0; q=0
    for t in range(lim):
        b=tape.get(pos,0); tr=M[2*q+b]
        if tr is None: return ('undef',2*q+b,t)
        if tr=='H': return ('halt',None,t+1)
        w,d,q2=tr; tape[pos]=w; pos+=1 if d else -1; q=q2
    return ('run',None,lim)
def ngram(M,k,H,cap=100000):
    B=(0,()); Z=(B,)*k; G=[{Z},{Z}]; S={(0,Z,B,Z)}; ch=True; choice={}
    while ch:
        ch=False
        for cfg in list(S):
            q,l,h,r=cfg
            t=M[2*q+h[0]]
            if t is None or t=='H': return None
            w,d,q2=t; P,O=(1,0) if d else (0,1)
            sides=[l,r]; o=sides[O]; p=sides[P]
            sym=(w,((q,)+h[1])[:H]); no=(sym,)+o[:-1]; choice[cfg]=(sym,no,O)
            if no not in G[O]: G[O].add(no); ch=True
            for g in list(G[P]):
                if g[:-1]==p[1:]:
                    c=(q2,no,p[0],g) if d else (q2,g,p[0],no)
                    if c not in S: S.add(c); ch=True
            if len(S)>cap: return None
    syms={}
    def sid(s):
        if s not in syms: syms[s]=len(syms)
        return syms[s]
    sid(B)
    st={}
    def gid(side,g):
        if (side,g) not in st: st[(side,g)]=len(st)
        return st[(side,g)]
    gid(0,Z); gid(1,Z)
    edges=[]
    for side in (0,1):
        for g in G[side]:
            for g2 in G[side]:
                if g2[:-1]==g[1:]: edges.append((gid(side,g),sid(g[0]),gid(side,g2)))
    for cfg in S:
            sid(cfg[2])
    cfgs=[]
    for cfg in S:
        q,l,h,r=cfg; sym,no,O=choice[cfg]
        cfgs.append((q,gid(0,l),sid(h),gid(1,r),sid(sym),gid(O,no)))
    sy=[0]*len(syms)
    for s,i in syms.items(): sy[i]=s[0]
    acc=[gid(0,Z),gid(1,Z)]
    a0=(0,gid(0,Z),sid(B),gid(1,Z))
    return sy,edges,acc,cfgs,a0
certs=[]
def rec(M):
    kind,idx,t=run(M,LIM)
    if kind=='halt': return
    if kind=='undef':
        for o in opts:
            M2=list(M); M2[idx]=o; rec(M2)
        return
    for H,k in ((0,1),(0,2),(0,3),(0,4),(1,4),(2,2)):
        c=ngram(M,k,H)
        if c: certs.append(c); return
    raise Exception('holdout')
rec([None]*(2*n))
def enc(c):
    sy,edges,acc,cfgs,a0=c
    parts=[len(sy)]+sy+[len(edges)]+[x for e in edges for x in e]+[len(acc)]+acc+[len(cfgs)]+[x for cf in cfgs for x in cf]+list(a0)
    return ' '.join(map(str,parts))
sys.stdout.write('(let ((many hints)) "'+'\\n'.join(enc(c) for c in certs)+'\\n")\n')
