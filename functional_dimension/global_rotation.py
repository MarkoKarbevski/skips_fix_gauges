# A pre-LN transformer (LayerNorm with gain and bias, attention with biases, GELU FFN with biases,
# trainable embedding and unembedding). One orthogonal Q that fixes the all-ones vector is applied to
# the whole residual stream; every weight matrix that reads a LayerNorm absorbs it.
# Claim to test: the function does not change, although Q couples all layers.
# For the paper "On the Functional Dimension of a Family of Analytic Neural Networks": the numbers of its appendix
# "With skip connections: where the reduction stops". The last two lines check the rescalings inside a ReLU and a
# SwiGLU feed-forward block.
# Run, from the repository root:  python3 functional_dimension/global_rotation.py   (a few seconds)
import numpy as np
from scipy.special import erf
from scipy.stats import ortho_group
rng = np.random.default_rng(0)
d, h, dk, dff, din, dout, n, L = 6, 2, 3, 10, 7, 5, 4, 3
gelu = lambda z: 0.5 * z * (1 + erf(z / np.sqrt(2)))
def LN(x, g, b):
    c = x - x.mean(-1, keepdims=True)
    return g * c / np.sqrt((c ** 2).mean(-1, keepdims=True)) + b
def softmax(s):
    s = s - s.max(-1, keepdims=True); e = np.exp(s); return e / e.sum(-1, keepdims=True)
def init():
    p = {'E': rng.normal(size=(din, d)), 'WU': rng.normal(size=(d, dout)), 'bU': rng.normal(size=dout),
         'gf': rng.normal(size=d) + 2, 'bf': rng.normal(size=d), 'layers': []}
    for _ in range(L):
        p['layers'].append({
            'g1': rng.normal(size=d) + 2, 'b1': rng.normal(size=d),
            'WQ': rng.normal(size=(h, d, dk)), 'bQ': rng.normal(size=(h, dk)),
            'WK': rng.normal(size=(h, d, dk)), 'bK': rng.normal(size=(h, dk)),
            'WV': rng.normal(size=(h, d, dk)), 'bV': rng.normal(size=(h, dk)),
            'WO': rng.normal(size=(h, dk, d)), 'bO': rng.normal(size=d),
            'g2': rng.normal(size=d) + 2, 'b2': rng.normal(size=d),
            'W1': rng.normal(size=(d, dff)), 'c1': rng.normal(size=dff),
            'W2': rng.normal(size=(dff, d)), 'c2': rng.normal(size=d)})
    return p
def forward(p, x):
    X = x @ p['E']
    for l in p['layers']:
        Z = LN(X, l['g1'], l['b1']); out = l['bO'].copy()
        for i in range(h):
            q = Z @ l['WQ'][i] + l['bQ'][i]; k = Z @ l['WK'][i] + l['bK'][i]; v = Z @ l['WV'][i] + l['bV'][i]
            out = out + softmax(q @ k.T / np.sqrt(dk)) @ v @ l['WO'][i]
        X = X + out
        Z = LN(X, l['g2'], l['b2'])
        X = X + gelu(Z @ l['W1'] + l['c1']) @ l['W2'] + l['c2']
    return LN(X, p['gf'], p['bf']) @ p['WU'] + p['bU']
def reader(W, b, g, beta, Q):          # a weight matrix W with bias b that reads LN_{g,beta}
    W2 = np.diag(1 / g) @ Q.T @ np.diag(g) @ W
    return W2, b + beta @ (W - W2)
def transform(p, Q):
    q = {'E': p['E'] @ Q, 'gf': p['gf'], 'bf': p['bf'], 'layers': []}
    q['WU'], q['bU'] = reader(p['WU'], p['bU'], p['gf'], p['bf'], Q)
    for l in p['layers']:
        m = dict(l)
        for W, b in (('WQ', 'bQ'), ('WK', 'bK'), ('WV', 'bV')):
            pairs = [reader(l[W][i], l[b][i], l['g1'], l['b1'], Q) for i in range(h)]
            m[W] = np.stack([a for a, _ in pairs]); m[b] = np.stack([c for _, c in pairs])
        m['WO'] = l['WO'] @ Q; m['bO'] = l['bO'] @ Q
        m['W1'], m['c1'] = reader(l['W1'], l['c1'], l['g2'], l['b2'], Q)
        m['W2'] = l['W2'] @ Q; m['c2'] = l['c2'] @ Q
        q['layers'].append(m)
    return q
# an orthogonal Q with 1 Q = 1: identity on the all-ones direction, a random rotation on its complement
B = np.linalg.qr(np.column_stack([np.ones(d), rng.normal(size=(d, d - 1))]))[0]   # first column ∝ 1
R = np.eye(d); R[1:, 1:] = ortho_group.rvs(d - 1, random_state=1)
Q = B @ R @ B.T
assert np.allclose(Q @ Q.T, np.eye(d)) and np.allclose(np.ones(d) @ Q, np.ones(d))
p = init(); x = rng.normal(size=(n, din))
y0 = forward(p, x); y1 = forward(transform(p, Q), x)
print('||Q - I|| =', np.linalg.norm(Q - np.eye(d)))
print('output change under the global rotation:', np.abs(y0 - y1).max(), ' (scale of outputs', np.abs(y0).max(), ')')
# the same Q applied at one layer only (the coupling that the paper considers) does change the function
p2 = transform(p, Q); p2['layers'][0] = p['layers'][0]
print('output change when one layer is left out:', np.abs(y0 - forward(p2, x)).max())
# ReLU and SwiGLU feed-forward blocks: a continuous rescaling of each hidden unit preserves the block
lam = np.exp(rng.normal(size=dff)); Z = rng.normal(size=(n, d)); W1 = rng.normal(size=(d, dff)); W2 = rng.normal(size=(dff, d)); c1 = rng.normal(size=dff)
relu = lambda z: np.maximum(z, 0)
print('ReLU FFN, unit rescaling:', np.abs(relu(Z @ W1 + c1) @ W2 - relu(Z @ (W1 * lam) + c1 * lam) @ (W2 / lam[:, None])).max())
W3 = rng.normal(size=(d, dff)); silu = lambda z: z / (1 + np.exp(-z))
print('SwiGLU FFN, value rescaling:', np.abs((silu(Z @ W1) * (Z @ W3)) @ W2 - (silu(Z @ W1) * (Z @ (W3 * lam))) @ (W2 / lam[:, None])).max())
