import numpy as np
rng=np.random.default_rng(0)
T,dIn,d,dOut,L,m=3,4,3,2,3,5
E=rng.normal(size=(dIn,d)); D=rng.normal(size=(d,dOut))
R=[rng.normal(size=(d,m)) for _ in range(L)]; W=[rng.normal(size=(m,d)) for _ in range(L)]
f=lambda M: np.maximum(M,0)+np.tanh(M)   # locally Lipschitz
def rms0(h):
    n=np.linalg.norm(h,axis=1,keepdims=True); return np.where(n>0, np.sqrt(d)*h/np.where(n>0,n,1), 0)
def ev(chi,S,E,R,W,D,X):
    h=X@E
    for l in range(L): h=h@S[l]+f(chi(h)@R[l])@W[l]
    return chi(h)@D
I=[np.eye(d)]*L; Z=[np.zeros((d,d))]*L
X=rng.normal(size=(T,dIn))
print("(i) no normalization: t, t*err")
for t in [1,10,100,1000,10000]:
    Rt=[R[l]/t**l for l in range(L)]; Wt=[t**(l+1)*W[l] for l in range(L)]
    err=np.abs(ev(lambda h:h,I,E,Rt,Wt,D/t**L,X)-ev(lambda h:h,Z,E,R,W,D,X)).max()
    print(t, t*err)
print("(ii) pre-RMSNorm eps=0: t, t*err")
for t in [1,10,100,1000,10000]:
    Wt=[t**(l+1)*W[l] for l in range(L)]
    err=np.abs(ev(rms0,I,E,R,Wt,D,X)-ev(rms0,Z,E,R,W,D,X)).max()
    print(t, t*err)
