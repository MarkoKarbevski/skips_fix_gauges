# Dimension paper, Appendix D.5: eq. (24), (25) and Lemma D.8 for real z, checked on a grid in 400-digit arithmetic
# (24 November 2026). Two earlier versions "failed" only by cancellation: in double precision at z = 8.3 (z - GELU(z)),
# and with 60 digits at z = 15.4 (1 - Phi(z)).
from mpmath import mp, mpf, exp, sqrt, pi, erfc
mp.dps = 400
def phi(z): return exp(-z*z/2)/sqrt(2*pi)
def Phi(z): return erfc(-z/sqrt(2))/2
def mr(z): return erfc(z/sqrt(2))/2/phi(z)   # = (1 - Phi(z))/phi(z), without the cancellation in 1 - Phi
def gelu(z): return z*Phi(z)
def dgelu(z): return Phi(z)+z*phi(z)
def silu(z): return z/(1+exp(-z))
def dsilu(z): return (1+exp(-z)+z*exp(-z))/(1+exp(-z))**2
def df(n): return 1 if n<=0 else n*df(n-2)
tol=mpf(10)**(-150); bad=[]
for k in range(1,600):
    z=mpf(k)/20
    c=[]
    c.append(abs(gelu(z)-(z-phi(z)*z*mr(z)))<tol and abs(dgelu(z)-(1-phi(z)*(mr(z)-z)))<tol)       # D.8 (i), z > 0
    c.append(abs(gelu(-z)-(-z-phi(-z)*(-z)*mr(-z)))<tol and abs(dgelu(-z)-(1-phi(-z)*(mr(-z)+z)))<tol) # D.8 (i), z < 0
    for m in range(6):                                                                                # D.8 (ii)
        s=sum((-1)**l*mpf(df(2*l-1))/z**(2*l+1) for l in range(m))
        c.append(abs(mr(z)-s)<=mpf(df(2*m-1))/z**(2*m+1))
    c.append(abs(gelu(-z)+(z-gelu(z)))<tol and abs(dgelu(-z)-(1-dgelu(z)))<tol)                       # (24)
    c.append(abs(silu(-z)+(z-silu(z)))<tol and abs(dsilu(-z)-(1-dsilu(z)))<tol)
    c.append(abs((z-gelu(z))-phi(z)*z*mr(z))<tol and abs((1-dgelu(z))-phi(z)*(mr(z)-z))<tol)          # delta, delta' for GELU
    c.append(abs((z-silu(z))-z/(1+exp(z)))<tol and abs((1-dsilu(z))-(1+exp(z)-z*exp(z))/(1+exp(z))**2)<tol)  # for SiLU
    if z>=2:
        for (d,dp,p) in [(z-gelu(z),1-dgelu(z),2),(z-silu(z),1-dsilu(z),1)]:                          # (25)
            e=exp(-z**p/p); c.append(e/6<=d and d<=z*e and abs(dp)<=4*z*d)
        c.append(mpf(3)/4<=z*mr(z)<=1 and abs(mr(z)-z)<=2*z and mr(z)<=1/z and abs(mr(z)-1/z)<=1/z**3)
        c.append(z*exp(-z)/2<=z-silu(z)<=z*exp(-z) and abs(1-dsilu(z))<=(2+z)*exp(-z))
    if not all(c): bad.append((float(z),[i for i,x in enumerate(c) if not x]))
print('grid z = 0.05 .. 29.95; failures:',bad[:5] if bad else 'none')
