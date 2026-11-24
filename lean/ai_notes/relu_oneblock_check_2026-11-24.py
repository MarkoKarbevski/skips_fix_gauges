# Check of the statements of Dimension/RescalingMlp.lean and OneBlock/Rescale.lean (24 November 2026):
# one block, no normalization, activation sigma positively homogeneous of degree k (ReLU k=1, ReLU^2 k=2).
#  (1) the rescaling (c_i, a_i) -> (lam c_i, a_i / lam^k) keeps the function;
#  (2) rescaleDirMlp k theta alpha and cobDir theta X are in the kernel of the Jacobian;
#  (3) the rank of the Jacobian on a batch with no unit at its kink is P - 2 d^2 - q.
import numpy as np, mpmath as mp
rng=np.random.default_rng(0)
def run(k,d,din,dout,q,T=2,nb=60):
    act=(lambda z: np.maximum(z,0)**k); dact=(lambda z: k*np.maximum(z,0)**(k-1) if k>1 else (z>0).astype(float))
    E=rng.normal(size=(din,d)); R=rng.normal(size=(d,q)); W=rng.normal(size=(q,d)); D=rng.normal(size=(d,dout))
    F=lambda E,R,W,D,x: act(x@E@R)@W@D
    xs=[rng.normal(size=(T,din)) for _ in range(nb)]
    assert all(np.abs(x@E@R).min()>1e-6 for x in xs)
    # (1)
    lam=np.exp(rng.normal(size=q)); R2=R*lam; W2=W/(lam**k)[:,None]
    e1=max(np.abs(F(E,R2,W2,D,x)-F(E,R,W,D,x)).max() for x in xs)
    # Jacobian, analytic, along a direction (eE,eR,eW,eD)
    def dF(x,eE,eR,eW,eD):
        z=x@E@R
        return (dact(z)*(x@eE@R+x@E@eR))@W@D + act(z)@eW@D + act(z)@W@eD
    P=E.size+R.size+W.size+D.size
    basis=[]
    for M in (E,R,W,D):
        for idx in np.ndindex(M.shape):
            basis.append(idx)
    cols=[]
    shapes=[E.shape,R.shape,W.shape,D.shape]
    for s,sh in enumerate(shapes):
        for idx in np.ndindex(sh):
            dirs=[np.zeros(t) for t in shapes]; dirs[s][idx]=1.0
            cols.append(np.concatenate([dF(x,*dirs).ravel() for x in xs]))
    J=np.array(cols).T
    sv=np.linalg.svd(J,compute_uv=False)
    rank=int((sv>1e-9*sv[0]).sum())
    # (2)
    al=rng.normal(size=q); X0=rng.normal(size=(d,d)); X1=rng.normal(size=(d,d))
    resc=(np.zeros_like(E), R*al, -(k*al)[:,None]*W, np.zeros_like(D))
    cob=(E@X0, -X0@R, W@X1, -X1@D)
    e2=max(np.abs(dF(x,*resc)).max() for x in xs); e3=max(np.abs(dF(x,*cob)).max() for x in xs)
    print(f"k={k} d={d} din={din} dout={dout} q={q} T={T}: P={P}, rank={rank}, P-2d^2-q={P-2*d*d-q}, gap sv[rank-1]/sv[rank]={sv[rank-1]/max(sv[rank],1e-300) if rank<len(sv) else float('inf'):.2e}; rescale err={e1:.1e}; rescaleDir in kernel={e2:.1e}; cobDir in kernel={e3:.1e}")
for k in (1,2):
    run(k,2,3,3,3); run(k,2,2,2,4); run(k,3,4,3,5,T=1)
