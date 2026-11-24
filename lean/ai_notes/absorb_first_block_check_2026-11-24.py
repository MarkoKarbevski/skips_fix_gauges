# Checks for Absorb/FirstBlock.lean (absorb paper, Theorem 4.5), 24 November 2026.
# (1) GELU networks along rays: F_gelu(t X)/t -> F_relu(X), same weights, residual (S = 1) and skipless (S = 0).
# (2) ReLU: near a generic input the residual network is linear with Jacobian E Theta D of rank d;
#     a skipless network whose first block has m' < 2d units is constant, near x0 or near -x0, along a
#     subspace of dimension > d_in - d: its Jacobian there has rank < d.
import numpy as np
from math import erf, sqrt
rng=np.random.default_rng(3)
gelu=np.vectorize(lambda z: z*0.5*(1+erf(z/sqrt(2)))); relu=lambda z: np.maximum(z,0)
def net(act,E,Rs,Ws,D,x,skip):
    h=x@E
    for R,W in zip(Rs,Ws): h=skip*h+act(h@R)@W
    return h@D
d,din,dout,q,L=3,4,4,5,3
E=rng.normal(size=(din,d)); D=rng.normal(size=(d,dout)); Rs=[rng.normal(size=(d,q)) for _ in range(L)]; Ws=[rng.normal(size=(q,d)) for _ in range(L)]
X=rng.normal(size=(2,din))
for skip in (1,0):
    errs=[np.abs(net(gelu,E,Rs,Ws,D,t*X,skip)/t-net(relu,E,Rs,Ws,D,X,skip)).max() for t in (1e1,1e2,1e3,1e4)]
    print("skip",skip,"ray errors at t=10..1e4:",["%.1e"%e for e in errs])
def jac(f,x,eps=1e-6):
    return np.array([(f(x+eps*e)-f(x-eps*e))/(2*eps) for e in np.eye(len(x))])
F=lambda x: net(relu,E,Rs,Ws,D,x[None,:],1)[0]
x0=rng.normal(size=din)
print("residual: rank of the Jacobian at x0, -x0:",np.linalg.matrix_rank(jac(F,x0),tol=1e-5),np.linalg.matrix_rank(jac(F,-x0),tol=1e-5),"(d =",d,")")
for m1 in (2*d-1,2*d):
    dp=4; E2=rng.normal(size=(din,dp)); D2=rng.normal(size=(dp,dout)); R2=[rng.normal(size=(dp,m1)),rng.normal(size=(dp,9))]; W2=[rng.normal(size=(m1,dp)),rng.normal(size=(9,dp))]
    G=lambda x: net(relu,E2,R2,W2,D2,x[None,:],0)[0]
    r=[np.linalg.matrix_rank(jac(G,s*x0),tol=1e-5) for s in (1,-1)]
    act=[(s*x0@E2@R2[0]>0).sum() for s in (1,-1)]
    print(f"skipless, first block {m1} units: active at x0, -x0: {act}; rank of the Jacobian: {r}; min = {min(r)}", "< d" if min(r)<d else ">= d")
