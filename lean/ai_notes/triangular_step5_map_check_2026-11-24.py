# Step 5 of the proof of S Theorem B.1 (iii): "for generic A the map from antisymmetric Y to the
# entries of A Y below the diagonal is invertible".  For an upper triangular A with symbolic
# entries: the determinant of this map, and of the map X -> entries of X A below the diagonal
# (the rotation of h_0, which the Lean proof uses).  Exact (sympy).
import sympy as sp
for d in (2, 3, 4):
    A = sp.zeros(d, d)
    for i in range(d):
        for j in range(i, d):
            A[i, j] = sp.Symbol(f"a{i+1}{j+1}")
    pairs = [(i, j) for i in range(d) for j in range(i)]          # entries below the diagonal
    def basis(k):
        i, j = pairs[k]; Y = sp.zeros(d, d); Y[i, j] = 1; Y[j, i] = -1; return Y
    M1 = sp.Matrix([[(A * basis(k))[p] for k in range(len(pairs))] for p in pairs])
    M2 = sp.Matrix([[(basis(k) * A)[p] for k in range(len(pairs))] for p in pairs])
    print(f"d={d}: det of Y -> (A Y) below the diagonal: {sp.factor(M1.det())};  "
          f"det of X -> (X A) below the diagonal: {sp.factor(M2.det())}")
