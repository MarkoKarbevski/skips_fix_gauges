"""Check of the statements of lean/SkipsLean/Dimension/UpperBoundRMSNormZero.lean (dimension paper, Theorem 4.3
for eps = 0 with the group CO(d), and the values of Theorem 5.2 (i), (ii) for eps = 0), 24 November 2026.

Skipless network x -> x E, h -> f(N_0(h) W_read) W_write, -> N_0(h) D, with N_0 RMSNorm with eps = 0.
(1) The directions of the symmetries are in the kernel of the Jacobian on a batch: cobDir(Y) with antisymmetric
    Y_0..Y_L, and scaleDir(beta) = (beta_0 E, 0, beta_{l} W_write^l, 0) (the rescalings of gated units are
    not tested here).
(2) The rank on a batch at random parameters is at most P - (L+1)(d(d-1)/2 + 1) - s, with equality for tanh and
    GELU blocks of at least d hidden units (Theorem 5.2 (i), (ii) for eps = 0).
The functions are those of different_classes_check_2026-11-24.py, with eps = 0.
"""
import sys, os
src = open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'different_classes_check_2026-11-24.py')).read()
exec(src[:src.index("ok = True")])
EPS = mp.mpf(0)
random.seed(3)
ok = True
for kind, cases in [('tanh', [(2, 2, 2, [2]), (3, 2, 2, [2, 3]), (3, 3, 3, [3])]),
                    ('gelu', [(2, 2, 2, [2]), (2, 2, 3, [3, 2]), (3, 3, 3, [3])]),
                    ('swiglu', [(2, 2, 2, [2]), (3, 2, 2, [2, 2])])]:
    g = 2 if kind == 'swiglu' else 1
    for (dIn, d, dOut, hid) in cases:
        L = len(hid)
        P = dIn * d + sum((g + 1) * d * q for q in hid) + d * dOut
        s = sum(hid) if kind == 'swiglu' else 0
        bound = P - (L + 1) * (d * (d - 1) // 2 + 1) - s
        B = basis(((dIn, d), hid, dOut), g)
        xs = [rnd(1, dIn) for _ in range(P + 6)]
        th = (rnd(dIn, d), [rnd(d, g * q) for q in hid], [rnd(q, d) for q in hid], rnd(d, dOut))
        r0, g0 = rank(kind, True, 0, th, xs, B)
        # the symmetry directions: one antisymmetric Y and one beta at each hidden state
        E, R, W, D = th
        worst = mp.mpf(0)
        for l in range(L + 1):
            Y = rnd(d, d); Y = Y - Y.T
            for (X, scale) in [(Y, False), (mp.eye(d), True)]:
                eE = E * X if l == 0 else mp.zeros(dIn, d)
                eR = [(-X * R[i] if (i == l and not scale) else mp.zeros(d, g * hid[i])) for i in range(L)]
                eW = [(W[i] * X if i + 1 == l else mp.zeros(hid[i], d)) for i in range(L)]
                eD = (-X * D if (l == L and not scale) else mp.zeros(d, dOut))
                for x in xs[:6]:
                    y = forward(kind, True, 0, th, x, (eE, eR, eW, eD))
                    worst = max(worst, max(abs(y[0, j]) for j in range(y.cols)))
        good = (r0 <= bound) and (kind == 'swiglu' or r0 == bound) and worst < mp.mpf(10) ** (-30)
        print(f"eps=0 {kind} dIn={dIn} d={d} dOut={dOut} hid={hid} P={P} s={s}: skipless rank {r0} (gap {mp.nstr(g0[0], 3)} / {mp.nstr(g0[1], 3)}); "
              f"bound P-(L+1)(d(d-1)/2+1)-s={bound}; largest derivative along the symmetry directions {mp.nstr(worst, 3)}", 'OK' if good else 'MISMATCH')
        sys.stdout.flush()
        ok = ok and good
print('ALL AS EXPECTED' if ok else 'SOME MISMATCH')
