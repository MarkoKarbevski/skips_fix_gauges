"""Check of the statements of lean/SkipsLean/Residual/FewerHiddenUnits.lean (skips paper, Theorem 4.11 (ii)
and Theorem A.28 (iii) for skipless blocks of at least d hidden units; GELU, no normalization), 24 November 2026.

Residual GELU network with widths hid (P parameters): rank P - d^2 on a batch at random parameters.
Skipless GELU network with widths m, every m_l >= d (P' = P + 2 d (sum m - sum hid) parameters): rank at most
P' - (L+1) d^2 on the same batch, at random parameters and at special ones. The first exceeds the second
exactly when 2 (sum m - sum hid) < L d. The functions are those of different_classes_check_2026-11-24.py.
"""
import sys, os
src = open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'different_classes_check_2026-11-24.py')).read()
exec(src[:src.index("ok = True")])
random.seed(5)
ok = True
for (dIn, d, dOut, hid, m) in [(2, 2, 2, [2, 2], [3, 2]), (2, 2, 2, [2, 2], [2, 2]), (3, 2, 2, [3, 2], [2, 2]),
                               (2, 2, 2, [2, 2], [3, 3]), (3, 3, 3, [3, 3], [4, 3]), (2, 2, 2, [2], [3])]:
    L = len(hid)
    P = dIn * d + sum(2 * d * q for q in hid) + d * dOut
    P2 = dIn * d + sum(2 * d * q for q in m) + d * dOut
    B, B2 = basis(((dIn, d), hid, dOut), 1), basis(((dIn, d), m, dOut), 1)
    xs = [rnd(1, dIn) for _ in range(max(P, P2) + 6)]
    draw = lambda w: (rnd(dIn, d), [rnd(d, q) for q in w], [rnd(q, d) for q in w], rnd(d, dOut))
    r_res, g_res = rank('gelu', False, 1, draw(hid), xs, B)
    e = draw(m)
    pts = {'random': draw(m), 'E of rank 1': (rnd(dIn, 1) * rnd(1, d), e[1], e[2], e[3]),
           'first write of rank 1': (e[0], e[1], [rnd(m[0], 1) * rnd(1, d)] + e[2][1:], e[3])}
    hyp = 2 * (sum(m) - sum(hid)) < L * d
    line = (f"gelu dIn={dIn} d={d} dOut={dOut} hid={hid} m={m}: P={P}, P'={P2}; residual rank {r_res} (P-d^2={P - d * d}, "
            f"gap {mp.nstr(g_res[0], 3)} / {mp.nstr(g_res[1], 3)}); skipless bound P'-(L+1)d^2={P2 - (L + 1) * d * d}; "
            f"hypothesis 2(sum m - sum hid) < L d: {hyp};")
    good = (r_res == P - d * d) and (hyp == (P - d * d > P2 - (L + 1) * d * d))
    for name, eta in pts.items():
        r0, g0 = rank('gelu', False, 0, eta, xs, B2)
        line += f" {name} {r0} (gap {mp.nstr(g0[0], 3)} / {mp.nstr(g0[1], 3)});"
        good = good and (r0 <= P2 - (L + 1) * d * d)
    print(line, 'OK' if good else 'MISMATCH'); sys.stdout.flush()
    ok = ok and good
print('ALL AS EXPECTED' if ok else 'SOME MISMATCH')
