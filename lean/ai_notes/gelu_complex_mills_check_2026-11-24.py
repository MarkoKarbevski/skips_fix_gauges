# Numeric check of the statements of Activations/MillsC.lean, MillsCExpansion.lean and
# GeluOnPath.lean (24 November 2026).  mpmath, 30 digits.
import mpmath as mp, random
mp.mp.dps = 30
random.seed(1)
def phi(z): return mp.e**(-z**2/2)/mp.sqrt(2*mp.pi)
def mr(z):  return mp.quad(lambda u: mp.e**(-z*u-u**2/2), [0, 5, 20, mp.inf])
def mr_erf(z): return mp.sqrt(mp.pi/2)*mp.e**(z**2/2)*mp.erfc(z/mp.sqrt(2))
def gelu(z): return z/2*(1+mp.erf(z/mp.sqrt(2)))
def geluC(z): return z - phi(z)*z*mr(z)
def dgelu(z): return (1+mp.erf(z/mp.sqrt(2)))/2 + z*phi(z)
def df2(n):
    r = mp.mpf(1)
    while n > 1: r *= n; n -= 2
    return r
worst = {k: mp.mpf(0) for k in ["mr=erf form","geluC=gelu","mr'","gelu'","D8ii slack<0","path |delta|","path |delta'|","|phi| on path","Re z^2"]}
for _ in range(40):
    z = mp.mpc(random.uniform(-3,3), random.uniform(-3,3))
    worst["mr=erf form"] = max(worst["mr=erf form"], abs(mr(z)-mr_erf(z))/(1+abs(mr_erf(z))))
    worst["geluC=gelu"] = max(worst["geluC=gelu"], abs(geluC(z)-gelu(z))/(1+abs(gelu(z))))
    h = mp.mpf(10)**(-10)
    d = (mr(z+h)-mr(z-h))/(2*h)
    worst["mr'"] = max(worst["mr'"], abs(d-(z*mr(z)-1))/(1+abs(d)))
    worst["gelu'"] = max(worst["gelu'"], abs(dgelu(z)-(1-phi(z)*(mr(z)-z))))
for _ in range(60):
    z = mp.mpc(random.uniform(0.05,4), random.uniform(-6,6))
    for m in range(0,6):
        s = sum((-1)**l*df2(2*l-1)/z**(2*l+1) for l in range(m))
        lhs = abs(mr(z)-s); rhs = df2(2*m-1)/z.real**(2*m+1)
        worst["D8ii slack<0"] = max(worst["D8ii slack<0"], lhs-rhs)
for _ in range(60):
    a = random.uniform(0.05,2.5); b = random.uniform(-a,a)*0.999
    om = mp.mpc(a,b); t = mp.mpf(random.uniform(1,4))
    z = om*t + mp.conj(om)/t
    rho = a*a-b*b; u = (t-1/t)**2
    worst["Re z^2"] = max(worst["Re z^2"], abs((z**2).real-(4*a*a+rho*u)))
    worst["|phi| on path"] = max(worst["|phi| on path"], abs(abs(phi(z)) - mp.e**(-2*a*a)*mp.e**(-rho*u/2)/mp.sqrt(2*mp.pi)))
    worst["path |delta|"] = max(worst["path |delta|"], abs(z-gelu(z)) - mp.e**(-2*a*a)*mp.e**(-rho*u/2))
    worst["path |delta'|"] = max(worst["path |delta'|"], abs(1-dgelu(z)) - (1/(2*a)+2*a)*t*mp.e**(-rho*u/2))
for k,v in worst.items(): print(f"{k:16s} {mp.nstr(v,5)}")
print("identities: errors must be ~1e-20 or less (mr' is a finite difference: ~1e-9); inequalities: the numbers must be <= 0")
