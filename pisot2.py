"""Exact game at two new Pisot parameters, in Z[lambda] with doubled numerators
x = (A + B*lam + C*lam^2)/2.

tribonacci:  lam^3 = lam^2+lam+1  (~1.83929),  1/lam = lam^2-lam-1
supergolden: lam^3 = lam^2+1      (~1.46557),  1/lam = lam^2-lam
Both Pisot.  Orbit closure of 1/2, then configuration closure, exact max."""
import mpmath as mp
mp.mp.dps=60
def make(name):
    if name=='tribonacci':
        lam=mp.findroot(lambda t:t**3-t**2-t-1, 1.84)
        mulL=lambda A,B,C:(C, A+C, B+C)
        tests={'ltr':lambda A,B,C:(A+2,B+2,C-2),'gtg':lambda A,B,C:(A-4,B-2,C+2),
               'lth':lambda A,B,C:(A+1,B+1,C-1),'gth':lambda A,B,C:(A-3,B-1,C+1)}
    else:
        lam=mp.findroot(lambda t:t**3-t**2-1, 1.47)
        mulL=lambda A,B,C:(C, A, B+C)
        tests={'ltr':lambda A,B,C:(A,B+2,C-2),'gtg':lambda A,B,C:(A-2,B-2,C+2),
               'lth':lambda A,B,C:(A,B+1,C-1),'gth':lambda A,B,C:(A-2,B-1,C+1)}
    def sgn(t):
        A,B,C=t
        if A==0 and B==0 and C==0: return 0
        v=A+B*lam+C*lam*lam
        assert abs(v)>mp.mpf(10)**-30, "precision guard tripped"
        return 1 if v>0 else -1
    def f0(p): return mulL(*p)
    def f1(p):
        A,B,C=mulL(*p); return (A+2,B-2,C) if name=='tribonacci' else (A+2,B-2,C)
    # careful: f1 = lam*x - (lam-1); doubled: subtract 2lam-2 from numerator
    def f1(p):
        A,B,C=mulL(*p); return (A+2, B-2, C)
    T=tests
    def moves(p):
        out={}
        if sgn(T['gtg'](*p))>0: out['L']=f1(p)
        if sgn(T['ltr'](*p))<0: out['R']=f0(p)
        if sgn(T['lth'](*p))<0: out['M']=f0(p)
        elif sgn(T['gth'](*p))>0: out['M']=f1(p)
        return out
    return lam,moves
for name in ('tribonacci','supergolden'):
    lam,moves=make(name)
    # orbit closure
    half=(1,0,0); O={half}; front={half}
    while front:
        nf=set()
        for p in front:
            for q in moves(p).values():
                if q not in O: O.add(q); nf.add(q)
        front=nf
        assert len(O)<10000
    pts=sorted(O, key=lambda t:float(t[0]+t[1]*lam+t[2]*lam*lam))
    idx={p:i for i,p in enumerate(pts)}
    vals=[float((p[0]+p[1]*lam+p[2]*lam*lam)/2) for p in pts]
    mind=min(vals[i+1]-vals[i] for i in range(len(vals)-1))
    # transition tables
    TL=[];TR=[];TM=[]
    for p in pts:
        mv=moves(p)
        TL.append(idx[mv['L']] if 'L' in mv else -1)
        TR.append(idx[mv['R']] if 'R' in mv else -1)
        TM.append(idx[mv['M']] if 'M' in mv else -1)
    born=1<<idx[half]
    def stepmask(mask,tab,add):
        m=0; i=0; mm=mask
        while mm:
            if mm&1 and tab[i]>=0: m|=1<<tab[i]
            mm>>=1; i+=1
        return m|add
    seen={0}; layer={0}; rec={}; depth=0
    while layer:
        b=max(bin(s).count('1') for s in layer)
        if b not in rec: rec[b]=depth
        nxt=set()
        for s in layer:
            for t in (stepmask(s,TL,0), stepmask(s,TR,0), stepmask(s,TM,born)):
                if t not in seen: seen.add(t); nxt.add(t)
        layer=nxt; depth+=1
        assert len(seen)<3_000_000
    mx=max(bin(s).count('1') for s in seen)
    print(f"{name}: orbit {len(O)} points (min gap {mind:.5f}), "
          f"{len(seen)} reachable configurations, MAX = {mx}")
    print(f"   d(k) first attained: {dict(sorted(rec.items()))}")
    import math
    W=math.ceil(math.log(1/mind)/math.log(float(lam)))
    print(f"   scheduling bound: W={W}, N <= {W+ (W+1)//2 +1}")
