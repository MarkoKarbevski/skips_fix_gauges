# sigma(z) = z/2 + |z|^3 (Remark A.8 of the absorb paper): sigma(z) - sigma(-z) = z.
# (a) rescaling a unit (c, a) -> (lam c, a / lam^3) changes the block by the linear term ((lam^-2 - 1)/2) (x c) a:
#     so a block of the SAME width absorbs x M for many M (the "only if" of Theorem 3.1 (i) fails for this sigma).
# (b) d more units suffice (Proposition 4.4 / A.11 (i)) for this sigma as for every sigma with the identity.
import numpy as np
rng=np.random.default_rng(1)
s=lambda z: z/2+np.abs(z)**3
d,m=3,5
Wr=rng.normal(size=(d,m)); Ww=rng.normal(size=(m,d)); X=rng.normal(size=(200,d))
B=lambda Wr,Ww,x: s(x@Wr)@Ww
print("identity:", np.abs(s(X)-s(-X)-X).max())
lam=np.exp(rng.normal(size=m)*0.3)
M=Wr@np.diag((lam**-2-1)/2)@Ww
print("(a) same width, x M + B(x) = B'(x), max error:", np.abs(X@M+B(Wr,Ww,X)-B(Wr*lam,Ww/(lam**3)[:,None],X)).max(), " |M| =", np.abs(M).max())
# (b) absorb the identity with d more units
e=[0,1,2]; K=Wr[:,e]; N=np.linalg.inv(K)+Ww[e,:]          # x = (xK) K^-1 ; N' = K^-1 M + A_e with M = I
Wr2=np.concatenate([Wr.copy(),K],axis=1); Wr2[:,e]=-K        # flip the reads of the units e, add d units reading K
Ww2=np.concatenate([Ww.copy(),N],axis=0); Ww2[e,:]=Ww[e,:]-N
print("(b) d more units, x + B(x) = B'(x), max error:", np.abs(X+B(Wr,Ww,X)-B(Wr2,Ww2,X)).max(), " widths", m, "->", Wr2.shape[1])
