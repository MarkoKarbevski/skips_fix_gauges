"""Check for the statements on an upper triangular learned skip (skips paper, Theorem B.1 (iii)),
24 November 2026: at a point (theta, R) with R invertible upper triangular, the rank of the Jacobian
of the triangular family equals that of the full family; also at R = I and at a singular R.
Uses the functions of learned_skip_oneblock_check_2026-11-24.py (exact derivatives, 40 digits)."""
import mpmath as mp, random, sys
src = open('/home/claude/proj_up/learned_skip_oneblock_check_2026-11-24.py', encoding='utf8').read()
exec(src.split("ok = True")[0])
random.seed(8)
for kind, din, d, dout, q, eps in (('tanh', 2, 2, 2, 2, '0.5'), ('gated', 3, 3, 3, 3, '0.3')):
    eps = mp.mpf(eps); r = q if kind == 'tanh' else 2 * q
    P = din * d + d * r + q * d + d * dout; s = 0 if kind == 'tanh' else q
    th = [rnd(din, d), rnd(d, r), rnd(q, d), rnd(d, dout)]
    R = rnd(d, d); R = mp.matrix([[R[i, j] if j >= i else 0 for j in range(d)] for i in range(d)])
    Rs = R.copy(); Rs[0, 0] = 0
    print(f"{kind} d_in={din} d={d} d_out={dout} hidden={q}: P={P}, s={s}, P+d-s={P + d - s}")
    for name, A in (('R generic triangular', R), ('R = I', mp.eye(d)), ('R triangular with R_00 = 0 (singular)', Rs)):
        t = rank_gap(kind, th + [A], basis(din, d, r, q, dout, 'tri'), din, dout, eps, None)
        f = rank_gap(kind, th + [A], basis(din, d, r, q, dout, 'full'), din, dout, eps, None)
        print(f"    {name}: triangular family rank {t[0]} (gap {t[1]} / {t[2]}), full family rank {f[0]} (gap {f[1]} / {f[2]})")
    sys.stdout.flush()
