# ReGLU block (gate ReLU), one block, no normalization: rank of the exact Jacobian in the parameters on 400 random inputs.
# Expected: skipless P - 2 d^2 - 2 q, residual P - d^2 - 2 q (dimension paper Theorem 5.1, skips paper Theorem 4.6 (i)).
# Result (24 Nov 2026): the expected rank at all nine sizes, both seeds, gaps above 1e11.
# An earlier version with finite differences, 40 inputs and the threshold 1e-6 gave 14 and 16 at (d, d_in, d_out, q) = (2, 2, 2, 4): an artefact of the threshold.
import numpy as np
def run(d,din,dout,q,skip,seed,T=1,nb=400):
    rng=np.random.default_rng(seed)
    E=rng.normal(size=(din,d)); G=rng.normal(size=(d,q)); V=rng.normal(size=(d,q)); W=rng.normal(size=(q,d)); D=rng.normal(size=(d,dout))
    shapes=[E.shape,G.shape,V.shape,W.shape,D.shape]
    def dF(x,dE,dG,dV,dW,dD):
        h=x@E; dh=x@dE
        z=h@G; w=h@V; g=(z>0).astype(float)
        dz=dh@G+h@dG; dw=dh@V+h@dV
        u=np.maximum(z,0)*w; du=g*dz*w+np.maximum(z,0)*dw
        return (skip*dh+du@W+u@dW)@D+(skip*h+u@W)@dD
    xs=[rng.normal(size=(T,din)) for _ in range(nb)]
    cols=[]
    for s,sh in enumerate(shapes):
        for idx in np.ndindex(sh):
            dirs=[np.zeros(t) for t in shapes]; dirs[s][idx]=1.0
            cols.append(np.concatenate([dF(x,*dirs).ravel() for x in xs]))
    J=np.array(cols).T; P=J.shape[1]
    sv=np.linalg.svd(J,compute_uv=False); r=int((sv>1e-9*sv[0]).sum())
    return P,r,(sv[r-1]/sv[r] if r<len(sv) and sv[r]>0 else np.inf)
for (d,din,dout,q) in [(2,2,2,4),(2,2,2,3),(2,2,2,5),(2,3,2,4),(2,2,3,4),(2,3,3,4),(3,3,3,6),(3,3,3,5),(3,4,4,6)]:
    for skip in (0,1):
        res=[run(d,din,dout,q,skip,s) for s in (1,2)]
        P=res[0][0]; exp=P-(2-skip)*d*d-2*q
        print(f"d={d} din={din} dout={dout} q={q} skip={skip}: P={P} expected={exp} ranks={[r for _,r,_ in res]} gaps={['%.0e'%g for *_,g in res]}")
