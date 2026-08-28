"""Centered-form branch and bound.  Partial polynomial tracked at the cell
midpoint EXACTLY (gm, pm); variation over the cell bounded by
(w/2)*sum_j |j x^{j-1}| and (w/2)*sum_j |j(j-1) x^{j-2}|, which are
sign-independent and precomputable.  Adaptive bisection of x-cells."""
import sys
def cell(xa, xb, delta, D, pad=1e-12, cap=1_500_000):
    m=(xa+xb)/2; w=xb-xa
    X=[m**i for i in range(D+2)]
    Dg=[sum(j*xb**(j-1) for j in range(1,i)) for i in range(D+3)]
    DD=[sum(j*(j-1)*xb**(j-2) for j in range(2,i)) for i in range(D+3)]
    T1=[xb**i/(1-xb)+pad for i in range(D+2)]
    T2=[(i*xb**(max(i-1,0))*(1-xb)+xb**i)/(1-xb)**2+pad for i in range(D+2)]
    stack=[(1,1.0,0.0)]; nodes=0; leaks=0
    while stack:
        i,gm,pm=stack.pop(); nodes+=1
        if nodes>cap: return None
        vg=(w/2)*Dg[i]+pad; vp=(w/2)*DD[i]+pad
        if abs(gm) > delta+vg+T1[i]: continue
        if pm+vp+T2[i] < -delta: continue
        if i>D: leaks+=1; continue
        for c in (-1,0,1):
            stack.append((i+1, gm+c*X[i], pm+c*i*X[i-1]))
    return nodes,leaks
def adaptive(xa,xb,delta,D,minw=2e-7):
    todo=[(xa,xb)]; tot=0; leaks=0; ncells=0; unresolved=[]
    while todo:
        a,b=todo.pop()
        r=cell(a,b,delta,D)
        if r is None:
            if b-a<minw: unresolved.append((a,b)); continue
            mid=(a+b)/2; todo+=[(a,mid),(mid,b)]; continue
        n,l=r; tot+=n; leaks+=l; ncells+=1
    return tot,leaks,ncells,unresolved
if __name__=='__main__':
    delta=float(sys.argv[1]); D=48
    segs=[(0.50,0.64,'coarse'),(0.64,0.66,'mid'),(0.66,0.667,'critical')]
    T=0;L=0;C=0;U=[]
    for a,b,nm in segs:
        t,l,c,u=adaptive(a,b,delta,D)
        print(f"  [{a},{b}] ({nm}): nodes {t:,}, cells {c}, leaks {l}, unresolved {len(u)}")
        T+=t;L+=l;C+=c;U+=u
    print(f"TOTAL: nodes {T:,}, cells {C}, leaks {L}, unresolved {U[:3]}{'...' if len(U)>3 else ''}")
