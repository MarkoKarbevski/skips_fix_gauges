# Numeric check of Proposition E.1 of the dimension paper (inactive hidden units), exact Jacobians.
# Skipless networks, one token, no normalization. Rank of the Jacobian on a batch, in float64,
# with the singular values printed around the claimed bound.
import numpy as np
rng = np.random.default_rng(0)

def relu(z): return np.maximum(z, 0.0)
def drelu(z): return (z > 0).astype(float)

def make(kind, d, qs, dIn, dOut):
    th = {'E': rng.normal(size=(dIn, d)), 'D': rng.normal(size=(d, dOut)), 'R': [], 'W': []}
    for q in qs:
        th['R'].append(rng.normal(size=(d, 2*q if kind == 'reglu' else q)))
        th['W'].append(rng.normal(size=(q, d)))
    return th

def act(kind, z, q):
    if kind == 'relu': return relu(z), None
    if kind == 'relusq': return relu(z)**2, None
    g, v = z[:q], z[q:]
    return relu(g)*v, None

def dact(kind, z, dz, q):
    if kind == 'relu': return drelu(z)*dz
    if kind == 'relusq': return 2*relu(z)*dz
    g, v = z[:q], z[q:]
    return drelu(g)*dz[:q]*v + relu(g)*dz[q:]

def forward_jvp(kind, th, eta, x):
    h = x @ th['E']; dh = x @ eta['E']
    for R, W, dR, dW in zip(th['R'], th['W'], eta['R'], eta['W']):
        q = W.shape[0]
        z = h @ R; dz = dh @ R + h @ dR
        s, _ = act(kind, z, q); ds = dact(kind, z, dz, q)
        h, dh = s @ W, ds @ W + s @ dW
    return h @ th['D'], dh @ th['D'] + h @ eta['D']

def basis(th):
    out = []
    def zero():
        return {'E': np.zeros_like(th['E']), 'D': np.zeros_like(th['D']),
                'R': [np.zeros_like(a) for a in th['R']], 'W': [np.zeros_like(a) for a in th['W']]}
    for key in ['E', 'D']:
        for idx in np.ndindex(th[key].shape):
            e = zero(); e[key][idx] = 1.0; out.append(e)
    for key in ['R', 'W']:
        for b in range(len(th[key])):
            for idx in np.ndindex(th[key][b].shape):
                e = zero(); e[key][b][idx] = 1.0; out.append(e)
    return out

def jac_rank(kind, th, n=400):
    B = basis(th); P = len(B)
    X = rng.normal(size=(n, th['E'].shape[0]))
    J = np.zeros((n*th['D'].shape[1], P))
    for c, e in enumerate(B):
        J[:, c] = np.concatenate([forward_jvp(kind, th, e, x)[1] for x in X])
    sv = np.linalg.svd(J, compute_uv=False)
    return P, sv

def max_preact(kind, th, j, n=20000):
    X = rng.normal(size=(n, th['E'].shape[0])); m = -np.inf
    for x in X:
        h = x @ th['E']
        q = th['W'][0].shape[0]
        s, _ = act(kind, h @ th['R'][0], q)
        h1 = s @ th['W'][0]
        m = max(m, (h1 @ th['R'][1])[j])
    return m


def gen_bound(kind, d, qs):
    L = len(qs); P = 2*d*d + sum((3 if kind == 'reglu' else 2)*d*q for q in qs)
    s = (2 if kind == 'reglu' else 1)*sum(qs)
    return P, P - (L + 1)*d*d - s

print("Columns: kind, d, widths, P, the largest number the unit reads over 5000 inputs, the numeric rank "
      "(threshold 1e-8 relative, with the gap after it), the bound of Proposition E.1, "
      "and the singular value number bound+1 relative to the largest (zero means: rank <= bound).")
for kind in ['relu', 'relusq', 'reglu']:
    for d, qs in [(2, [4, 4]), (2, [5, 5]), (3, [5, 5]), (3, [6, 6]), (2, [4, 4, 4]), (3, [5, 5, 5])]:
        for trial in range(2):
            th = make(kind, d, qs, d, d); j = 0; q0 = qs[0]; L = len(qs)
            if kind != 'reglu':
                r = th['R'][1][:, j]            # read column of unit j of block 2
                for k in range(q0):             # a_k r < 0 for every unit k of block 1
                    a = th['W'][0][k]
                    th['W'][0][k] = a - (a @ r)/(r @ r)*r - (0.05 + 0.1*rng.random())*r/(r @ r)
                extra = 2*d - 1
            else:
                delta = 0.5/(q0*d)              # the weights of the proof, then a small perturbation
                for k in range(q0):
                    i = k % d; c = np.zeros(d); c[i] = 1.0; e = -delta*np.ones(d); e[i] = 1.0
                    th['R'][0][:, k] = c; th['R'][0][:, q0 + k] = e
                r = th['R'][1][:, j]            # gate column of unit j of block 2
                for k in range(q0):
                    a = th['W'][0][k]; th['W'][0][k] = a - (a @ r)/(r @ r)*r - r/(r @ r)
                th['R'][0] += 1e-3*rng.normal(size=th['R'][0].shape)
                th['W'][0] += 1e-3*rng.normal(size=th['W'][0].shape)
                extra = 3*d - 2
            X = rng.normal(size=(5000, d)); mx = -1e9
            for x in X:
                h = x @ th['E']; s, _ = act(kind, h @ th['R'][0], q0); h1 = s @ th['W'][0]
                mx = max(mx, (h1 @ th['R'][1])[j])
            P, sv = jac_rank(kind, th, n=300)
            P2, gb = gen_bound(kind, d, qs); assert P == P2
            bound = gb - extra
            if sv[0] == 0:
                print(f"{kind:7s} d={d} widths={qs}: the network is constant at this parameter"); continue
            rank = int((sv > 1e-8*sv[0]).sum())
            gap = sv[rank-1]/sv[rank] if rank < len(sv) and sv[rank] > 0 else float('inf')
            print(f"{kind:7s} d={d} widths={qs}: P={P}  reads at most {mx:+.1e}  rank={rank} (gap {gap:.0e})  "
                  f"bound={bound}  sv[bound+1]/sv[1]={sv[bound]/sv[0]:.1e}")
