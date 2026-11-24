# Absorb paper, Theorem 4.3 (pre-RMSNorm): rates along rays t X, and the condition "turn" of the Lean statement.
# Residual network: F(tX) = N_0(XE) D + rho(X)/t + O(1/t^2), rho(X) = DN_0(XE)[beta] D, beta = sum_l f_l(nbar W_read^l) W_write^l.
# Skipless network: S(tX) = G(X) + O(1/t^2), G(X) = the network with N_0 at the first normalization and N_eps after it.
import numpy as np
rng=np.random.default_rng(3)
T,din,d,dout,q,L,eps=2,4,3,4,5,3,0.3
def N(h,e): return h/np.sqrt((h*h).sum(1,keepdims=True)/h.shape[1]+e)
def net(X,E,R,W,D,skip,e,act,e0=None):
    # e0: the constant of the first normalization only (the limit G of the skipless network has e0 = 0 there)
    h=X@E
    for l in range(len(R)): h=skip*h+act(N(h,e if (l>0 or e0 is None) else e0)@R[l])@W[l]
    return N(h,e)@D
for name,act in [("tanh",np.tanh),("relu",lambda z:np.maximum(z,0))]:
    E=rng.normal(size=(din,d)); D=rng.normal(size=(d,dout)); R=[rng.normal(size=(d,q)) for _ in range(L)]; W=[rng.normal(size=(q,d)) for _ in range(L)]
    X=rng.normal(size=(T,din)); nbar=N(X@E,0.0)
    beta=sum(act(nbar@R[l])@W[l] for l in range(L))
    w=X@E; nw=np.sqrt((w*w).sum(1,keepdims=True)); u=w/nw
    rho=(np.sqrt(d)*(beta-(beta*u).sum(1,keepdims=True)*u)/nw)@D
    # "turn": some row of beta is not a multiple of the same row of nbar
    resid=[np.linalg.norm(beta[t]-(beta[t]@nbar[t])/(nbar[t]@nbar[t])*nbar[t]) for t in range(T)]
    print(name,"turn residuals per row:",np.round(resid,3),"|rho| =",round(float(np.abs(rho).max()),4))
    for t in [1e2,1e3,1e4]:
        Fres=net(t*X,E,R,W,D,1.0,eps,act); Sk=net(t*X,E,R,W,D,0.0,eps,act); G=net(X,E,R,W,D,0.0,eps,act,e0=0.0)
        print(f"  t={t:.0e}: |t(F(tX)-N0(XE)D)-rho|={np.abs(t*(Fres-nbar@D)-rho).max():.2e}   t|S(tX)-G|={t*np.abs(Sk-G).max():.2e}   t^2|S(tX)-G|={t*t*np.abs(Sk-G).max():.3f}")
