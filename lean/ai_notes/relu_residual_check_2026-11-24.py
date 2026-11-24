# Checks for the skips paper in Lean (24 November 2026), activation positively homogeneous of degree k (ReLU k=1, ReLU^2 k=2):
#  (1) Theorem 4.6 (i): one residual block, no normalization: rank of the Jacobian on a batch with no unit at its kink
#      is P - d^2 - q, and the skipless one is P - 2 d^2 - q (difference d^2).
#  (2) Theorem 4.2 with identity skips, L blocks: rank <= P - d^2 - s (s = sum of q); also under pre-RMSNorm: <= P - d(d-1)/2 - s.
import numpy as np
rng=np.random.default_rng(5)
def run(k,d,din,dout,qs,skip,rms=False,T=2,nb=40,eps=0.3):
    act=(lambda z: np.maximum(z,0)**k); dact=(lambda z: k*np.maximum(z,0)**(k-1) if k>1 else (z>0).astype(float))
    L=len(qs)
    E=rng.normal(size=(din,d)); D=rng.normal(size=(d,dout)); Rs=[rng.normal(size=(d,q)) for q in qs]; Ws=[rng.normal(size=(q,d)) for q in qs]
    def N(h): return h/np.sqrt((h**2).sum(axis=1,keepdims=True)/d+eps) if rms else h
    def F(par,x):
        E,Rs,Ws,D=par; h=x@E
        for R,W in zip(Rs,Ws): h=skip*h+act(N(h)@R)@W
        return N(h)@D
    par=(E,Rs,Ws,D)
    flat=lambda p: np.concatenate([p[0].ravel()]+[r.ravel() for r in p[1]]+[w.ravel() for w in p[2]]+[p[3].ravel()])
    def unflat(v):
        i=0; E2=v[i:i+E.size].reshape(E.shape); i+=E.size
        R2=[]; 
        for R in Rs: R2.append(v[i:i+R.size].reshape(R.shape)); i+=R.size
        W2=[]
        for W in Ws: W2.append(v[i:i+W.size].reshape(W.shape)); i+=W.size
        return (E2,R2,W2,v[i:].reshape(D.shape))
    v0=flat(par); P=v0.size
    xs=[rng.normal(size=(T,din)) for _ in range(nb)]
    h=1e-6
    J=np.array([np.concatenate([(F(unflat(v0+h*e),x)-F(unflat(v0-h*e),x)).ravel()/(2*h) for x in xs]) for e in np.eye(P)]).T
    sv=np.linalg.svd(J,compute_uv=False); rank=int((sv>1e-6*sv[0]).sum())
    return P,rank,sv[rank-1]/max(sv[rank],1e-300) if rank<len(sv) else np.inf
for k in (1,2):
    d,din,dout,q=2,3,3,3
    P,r1,g1=run(k,d,din,dout,[q],1); P,r0,g0=run(k,d,din,dout,[q],0)
    print(f"k={k} one block: P={P}; residual rank={r1} (P-d^2-q={P-d*d-q}, gap {g1:.1e}); skipless rank={r0} (P-2d^2-q={P-2*d*d-q}, gap {g0:.1e})")
    P,r,g=run(k,2,3,3,[3,3],1); print(f"k={k} two residual blocks: P={P}, rank={r} <= P-d^2-s={P-4-6} (gap {g:.1e})")
    P,r,g=run(k,3,4,4,[4,4],1,rms=True); print(f"k={k} two residual blocks, pre-RMSNorm: P={P}, rank={r} <= P-d(d-1)/2-s={P-3-8} (gap {g:.1e})")
