STATUS: complete

# Thirty-fifth audit, part A: S Theorem B.1 (iv) for one ReLU² block of width at least `d` (25 November 2026)

Commits of `/home/claude/lp` (branch `lean-plus`) read: `6ca72ca` at the start (three of the four files with `sorry`: `QuadraticResultant.lean`, `UnitsParallelAtSq.lean`, `SkiplessReluSqWideRMSZero.lean`; `UnitsGeneralPositionSq.lean` without `sorry` of its own, resting on `reluSq_unitsParallelAt_of_generic`); `7de96aa` (11:49 UTC, two statements changed, all four files proved: compared in the last section of Part 1); `2d68d1d` at the end (no change to the four files or to the definitions they use since `7de96aa`). Scratch work in `/home/claude/audit35a/`; papers in `<scratchpad>/skips.txt`.

## Part 1

### 1. Two quadratics (`OneBlock/QuadraticResultant.lean`)

**1a. Is `quadRes` the resultant (by reading).** Lean:

```
def quadRes (p₀ p₁ p₂ r₀ r₁ r₂ : ℝ) : ℝ :=
  (p₀ * r₂ - p₂ * r₀) ^ 2 - (p₀ * r₁ - p₁ * r₀) * (p₁ * r₂ - p₂ * r₁)
```

The classical resultant of `p₂ t² + p₁ t + p₀` and `r₂ t² + r₁ t + r₀` (the 4×4 Sylvester determinant) is `(p₂ r₀ − p₀ r₂)² − (p₂ r₁ − p₁ r₂)(p₁ r₀ − p₀ r₁)`. The first square is the same; the product is the same, since `(p₀ r₁ − p₁ r₀)(p₁ r₂ − p₂ r₁) = (p₁ r₀ − p₀ r₁)(p₂ r₁ − p₁ r₂)`. So `quadRes` is the Sylvester resultant with the formal degree two for both (no sign change). Vanishing leading coefficients: if `p₂ = r₂ = 0` then `quadRes = 0` (a common root at infinity); if `p₂ = 0 ≠ r₂`, `quadRes = r₂ (p₀² r₂ − p₀ p₁ r₁ + p₁² r₀)`, which is `r₂ p₁² r(−p₀/p₁)` when `p₁ ≠ 0` and `r₂² p₀²` when `p₁ = 0`. So `quadRes ≠ 0` says exactly that the binary quadratic forms `p₀ s² + p₁ s t + p₂ t²` and `r₀ s² + r₁ s t + r₂ t²` have no common zero in the complex projective line, as the docstring says. Verdict: the definition is right. (Exact symbolic confirmation below, 1c.)

**1b. The two statements (by reading, then exact computation).**

```
theorem quad_proportional_of_quadRes_ne_zero … (hres : quadRes p₀ p₁ p₂ r₀ r₁ r₂ ≠ 0) (hδ : 0 < δ)
    (h : ∀ t : ℝ, |t| < δ → (j₀ + j₁ * t + j₂ * t ^ 2) * (r₀ + r₁ * t + r₂ * t ^ 2)
      = (k₀ + k₁ * t + k₂ * t ^ 2) * (p₀ + p₁ * t + p₂ * t ^ 2)) :
    ∃ c : ℝ, j₀ = c * p₀ ∧ j₁ = c * p₁ ∧ j₂ = c * p₂ ∧ k₀ = c * r₀ ∧ k₁ = c * r₁ ∧ k₂ = c * r₂
```

True. The identity on `|t| < δ` is an identity of polynomials of degree at most four (two polynomials that agree on an interval are equal), hence an identity `J R = K P` of binary forms of degree four, where `P, R, J, K` are the binary quadratic forms of the coefficient triples. `quadRes ≠ 0` makes `P` and `R` coprime (1a), so `P | J`, and as both have degree two, `J = c P`; then `K P = c P R` and `K = c R` (`P ≠ 0`, since `quadRes(0,0,0,…) = 0`). The degree bound "at most two" on `j`, `k` is used: for `p = 1`, `r = t²` (`quadRes = 1`) the pair `j = t`, `k = t³` satisfies `j r = k p` and is not proportional, and the statement excludes it only because `k` has degree three.

```
theorem quad_vec_proportional_of_quadRes_ne_zero {m : Type*} {P₀ P₁ P₂ J₀ J₁ J₂ : m → ℝ} {e f : m} {δ : ℝ}
    (hres : quadRes (P₀ e) (P₁ e) (P₂ e) (P₀ f) (P₁ f) (P₂ f) ≠ 0) (hδ : 0 < δ)
    (h : ∀ t : ℝ, |t| < δ → ∃ μ : ℝ, J₀ + t • J₁ + t ^ 2 • J₂ = μ • (P₀ + t • P₁ + t ^ 2 • P₂)) :
    ∃ c : ℝ, J₀ = c • P₀ ∧ J₁ = c • P₁ ∧ J₂ = c • P₂
```

True. From `J(t) = μ(t) h(t)`: `J_g(t) h_e(t) = J_e(t) h_g(t)` for every entry `g` and `|t| < δ`. The first statement at `(e, f)` gives `J_e = c h_e`, `J_f = c h_f`; for any other `g`, `h_e (J_g − c h_g) = 0` as polynomials, and `h_e` is not the zero polynomial (else `quadRes = 0`), so `J_g = c h_g`. "Also where `h(t) = 0`": with `quadRes ≠ 0` the entries `h_e`, `h_f` have no common real root, so `h(t) ≠ 0` for every `t`; the case never arises, and the hypothesis `h` there would in any case force `J(t) = 0`. `m` needs no `Fintype` (the vectors are functions). `e = f` gives `quadRes = 0`, so the hypothesis excludes it.

**1c. Exact checks (computation, sympy 1.14, `/home/claude/audit35a/q1.py`).**
- The 4×4 Sylvester determinant minus `quadRes` expands to `0`.
- 300 random integer pairs `(p, r)` with coefficients in `[−3, 3]` (a third with `p₂ = 0`, a fifth with `r₂ = 0`): at every pair with `quadRes ≠ 0`, the solutions `(j, k)` of the five coefficient equations of `j r − k p = 0` form a space of dimension exactly one, spanned by `(p, r)`. No exception.
- 40 random integer triples `(P₀, P₁, P₂)` of vectors of length 3 (every fourth with one entry identically zero): whenever some pair of entries has `quadRes ≠ 0`, the solutions `(J₀, J₁, J₂)` of `J(t) ∧ h(t) ≡ 0` form a space of dimension one (`J = c h`). No exception.
- With `quadRes = 0` the conclusion fails: `p = 1`, `r = t` (`p₂ = r₂ = 0`, common root at infinity, `quadRes = 0`), `j = t`, `k = t²`: `j r = t² = k p` for all `t`, but `j = c p` would need `t = c`. The same pair gives the vector counterexample `h = (1, t)`, `J = (t, t²) = t · h`.

Verdict check 1: `quadRes` is the resultant; both statements SAME as the paper's step "From `J_a h_b = J_b h_a`, `h_a` divides `J_a`, so `J = c h_1`" restricted to one line and `k = 2`, and true.

### 2. The vector statement for ReLU² units (`reluSq_unitsParallelAt_of_generic`)

Lean (hypotheses abbreviated; full text in the file):

```
theorem reluSq_unitsParallelAt_of_generic {n m q : Type*} [Fintype n] [Fintype m] [Fintype q]
    (c : q → n → ℝ) (a : q → m → ℝ)
    (hcc : ∀ i j, i ≠ j → ∀ r : ℝ, c i ≠ r • c j) (ha : ∀ i, a i ≠ 0)
    (hne : ∀ x : n → ℝ, (∃ i, 0 < x ⬝ᵥ c i) → ∑ i, reluSq (x ⬝ᵥ c i) • a i ≠ 0)
    (hkink : ∀ i, ∃ x₀ : n → ℝ, x₀ ⬝ᵥ c i = 0 ∧ (∀ j, j ≠ i → x₀ ⬝ᵥ c j ≠ 0) ∧
      ∀ r : ℝ, ∑ j, reluSq (x₀ ⬝ᵥ c j) • a j ≠ r • a i)
    (hres : ∀ S : Finset q, 2 ≤ S.card → ∃ (u v : n → ℝ) (e f : m), quadRes (…S, u, v, e…) (…f…) ≠ 0) :
    UnitsParallelAt reluSq reluSqDeriv 2 c a
```

with `UnitsParallelAt σ σ' k c a :=  ∀ ψc β, (∀ x, (∀ i, x ⬝ᵥ c i ≠ 0) → ∑ i, σ (x ⬝ᵥ c i) • a i ≠ 0 → ∃ μ, ∑ i, (σ (x ⬝ᵥ c i) • β i + (σ' (x ⬝ᵥ c i) * (x ⬝ᵥ ψc i)) • a i) = μ • ∑ i, σ (x ⬝ᵥ c i) • a i) → ∃ c₀ lam, ∀ i, ψc i = lam i • c i ∧ β i = (c₀ − k * lam i) • a i`, and `reluSq z = max(z,0)²`, `reluSqDeriv z = 2 max(z,0)` (`Activations/ReLU.lean`).

**2a. The conclusion against the paper (reading).** With `β_i = ψa_i − a_i Y` the hypothesis is equation (18) at the inputs off the kinks with `h_1 ≠ 0`, `σ' (z) = 2 max(z, 0)` is the paper's `σ'` for `k = 2`. The paper ends "One scale" with `J = c h_1` on `Ω`, i.e. `∑_i σ(x c_i) (b_i − c a_i) = 0` with `b_i = ψa_i − a_i Y + 2 λ_i a_i`; Lean concludes `b_i = c₀ a_i` for every unit, i.e. `β_i = (c₀ − 2 λ_i) a_i`. That is one step further than the paper's sentence (the paper takes the step later, in "Counting", through Lemma B.3), and it is true here: the functions `x ↦ max(x c_i, 0)²` of pairwise non-collinear, nonzero `c_i` are linearly independent (at a point of the hyperplane of `c_i` on no other hyperplane only the `i`-th term fails to be twice differentiable), so `∑_i σ(x c_i)(b_i − c a_i) ≡ 0` gives each `b_i = c a_i`. Verdict on the conclusion: SAME as "`ψc_i = λ_i c_i`" and "`J = c h_1`", in the form the counting uses.

**2b. Is the statement true (reading, a proof sketch, and exact computations).** I read the argument through for these hypotheses and found it sound:
- "The kinks stay": at the point `x₀` of `hkink`, `h_1(x₀) ≠ 0`, so the hypothesis of `UnitsParallelAt` holds on open sets on both sides of the hyperplane near `x₀`, where `J ∧ h_1 = 0` is a polynomial identity. The difference of the two identities, divided by `x c_i`, gives `2 (x ψc_i) a_i ∧ h_1(x) = 0` on the hyperplane, and `a_i ∧ h_1(x₀) ≠ 0`, so `x ψc_i = 0` on the hyperplane and `ψc_i = λ_i c_i`. (This is the docstring's Lean route; it is right.)
- "One scale": on a cell with active set `S`, `|S| ≥ 2`, the entries of `h^S = ∑_{i∈S} (x c_i)² a_i` and of `J^S` are quadratic forms in `x`, and `J^S ∧ h^S ≡ 0`. `hres` for `S` says that the restrictions of `h^S_e` and `h^S_f` to the plane spanned by `u`, `v` are binary quadratic forms with no common zero (the three Lean coefficients `∑ (u c_i)² a_{ie}`, `2 ∑ (u c_i)(v c_i) a_{ie}`, `∑ (v c_i)² a_{ie}` are exactly those of `t ↦ h^S_e(u + t v)`). A nonconstant common factor of `h^S_e` and `h^S_f` in `ℝ[x]` would restrict to a common factor on that plane (or to `0`); so `h^S_e`, `h^S_f` are coprime, and `J^S = c_S h^S` on the cell. Across a facet between two cells, `c_S = c_{S'}`, since `h^S` does not vanish identically on a hyperplane (that would again make `quadRes = 0`). `Ω` is connected and stays connected without the faces of codimension two, so one `c` serves all cells.
- Exact computation, independent code (`/home/claude/audit35a/up2.py`, sympy, `n = 2`): the cells of the arrangement are enumerated exactly, the identities `J^S ∧ h^S ≡ 0` are written as polynomial identities (all coefficients), the rank is exact over `ℚ`, and all five hypotheses are tested exactly. Random integer units, `(m, q) = (2,2), (2,3), (2,4), (2,5), (2,6), (3,3), (3,5), (2,8)`, two each: at every case where all five hypotheses hold, the solutions `(ψc, β)` have dimension exactly `q + 1` and are the claimed ones (11 cases); where a hypothesis fails the count is sometimes higher (`q = 2`, opposite columns: 6 against 3; `q = 4` with a zero row and two collinear columns: 6 against 5). Output: `/home/claude/audit35a/up2_rerun.out` (a first run had a bug in the enumeration of sectors of angle `π`, which only arise with collinear columns or one unit; the run quoted here is after the fix).
- The coordinator's script `units_parallel_relusq_wide_check_2026-11-25.py` (copy run in `/home/claude/audit35a/`, 33 s): 28 cases, `n, m ≤ 4`, `q ≤ 8`, all `solutions <= q + 1` with the `q + 1` claimed solutions exact. Its rank is modulo `2^61 − 1` at sampled points, an upper bound on the solutions, so it is a valid check of the conclusion; it does not test the hypotheses (it only excludes collinear columns and zero rows).

Verdict: true.

**2c. Is each hypothesis needed (reading, exact computation).**
- `hcc` **follows from `hkink`.** If `c_i = r c_j` with `c_j ≠ 0`, `r ≠ 0`, the two hyperplanes coincide and the point `x₀` of `hkink` for `i` lies on the hyperplane of `j`; if `c_i = 0` (the case `r = 0`), every point lies on its hyperplane, and `hkink` for any other unit fails. With one unit `hkink` itself fails (`h_1(x₀) = σ(0) a = 0 = 0 • a`). So `hcc` is redundant (harmless). It is the same remark as the twenty-fifth audit's for the ReLU twin.
- `ha` **follows from `hres`.** If `a_i = 0`, take `S = {i, j}`: both entries of `∑_{k∈S} (x c_k)² a_k = (x c_j)² a_j` are multiples of one binary form, and `quadRes(α p, β p) = α²β² quadRes(p, p) = 0`. Redundant (harmless).
- `hne` **is implied by `ha` and `hres` when `n = 2`** (two input coordinates): `hres` at `S` then says that `h^S` has no real zero other than `0` in the whole plane, and on a cell with one active unit `h = (x c_j)² a_j ≠ 0`; points on the kinks take the value of a neighbouring cell. For `n ≥ 3` it is not implied, but the argument of 2b does not use it: there `hres` already makes `h^S` nonzero on a dense open part of every cell and not identically zero on any facet, which is all the argument needs. I found no example where `hne` fails, the other four hold, and the conclusion fails, and I believe there is none. It is still needed downstream (the network is defined on `Ω` only if `h_1 ≠ 0` there), so it belongs in `UnitsGeneralPositionSq`. It is redundant only here.
- `hkink` **is needed**, and the paper has it ("`h_1(x_0)` is not parallel to `a_i`", with "at which another unit is active"). Exact counts (`up2.py`): one unit, `c = (2, 1)`, `a = (1, 3)` (`hcc`, `ha`, `hne`, `hres` hold, `hkink` fails): 3 solutions against 2, `ψc` is not forced to be a multiple of `c`; two opposite columns `c = (2,1), (−4,−2)`: 6 against 3.
- `hres`: see 2d.

**2d. Is `hres` needed (exact computation, `n = 2`).** I looked for units with `hcc`, `ha`, `hne`, `hkink` and without `hres` at some `S` where `UnitsParallelAt` fails, and found none.
- A hand-made example: `c = (1,0), (0,1), (1,1)`, `a = (1,−1), (−1,1), (1,1)`. On the cell where all three units are active, `h = 2 (x₁ + x₂)(x₁, x₂)`: the two entries share the factor `x₁ + x₂` (whose zero line misses the closed cell), so `hres` fails for `{1,2,3}` (and for `{1,2}`, which is the active set of no input). `hcc`, `ha`, `hne`, `hkink` hold (exactly checked). The solutions still have dimension `q + 1 = 4` and are the claimed ones: the neighbouring cells `{1,3}` and `{2,3}`, which share unit 3, fix one scale on both sides of the bad cell.
- Random constructions (`/home/claude/audit35a/up2_search2.py`, `up2_search3.py`): integer columns, 3 to 6 units, and rows `a` solved from linear equations that force a common real root (outside the closed cell) or proportional entries on 1 to `q − 1` chosen cells with at least two active units. 1150 constructions in all; in the last 350, 64 had all four other hypotheses and failed `hres`: in every one the solutions had dimension exactly `q + 1`. No candidate in the earlier 800 either.
- In `n = 2` the reason appears to be that the cells form a chain in which consecutive cells differ by one unit, each unit is active on a half-turn, and the scale is carried across a bad cell by the units it shares with its good neighbours. I did not prove that `hres` is redundant, and in `n ≥ 3` I did not search. So: `hres` is a sufficient generic condition; whether it can be dropped is open; it does no harm, since it holds at almost every parameter (4b).

Verdict check 2: `reluSq_unitsParallelAt_of_generic` is true (now proved, 7de96aa); SAME as "The kinks stay" (`k = 2`) and "One scale" with the paper's generic conditions made explicit; `hcc` and `ha` are redundant, `hne` is not needed for this statement (it is for the network), `hkink` is needed, and `hres` is sufficient, with no example found where it is needed. The paper proves only `h_1 ≠ 0` of its generic conditions for `k = 2` (check 6).

### 3. The six conditions (`UnitsGeneralPositionSq`) and the three theorems from them

**3a. The clauses against the paper (reading).** `UnitsGeneralPositionSq Wr Ww` (columns `w_i = Wrᵀ i`, rows `a_i = Ww i`, all in `ℝ^d`):
1. `∀ i j, i ≠ j → ∀ r, Wrᵀ i ≠ r • Wrᵀ j`: the paper's "the `c_i` are pairwise non-collinear" (used for "`Ω` is connected"), at `h₀`-coordinates. Generic iff `d ≥ 2` (for `d = 1` all columns are collinear).
2. `∀ i, Ww i ≠ 0`: not in the paper's words; generic for every size.
3. `∀ u, (∃ i, 0 < u ⬝ᵥ Wrᵀ i) → ∑ i, reluSq (u ⬝ᵥ Wrᵀ i) • Ww i ≠ 0`: "for generic parameters `h_1 ≠ 0` there", for real `u` only. The paper's proof excludes complex common zeros as well; only real `u` is needed (the network and the hypothesis of `UnitsParallelAt` are about real inputs), so the clause is weaker than what the paper proves and is what it uses. Generic for every size (4b).
4. For every unit a point `u₀` of its hyperplane, on no other, with `h(u₀)` not a multiple of `a_i`: the paper's "For generic parameters and `x_0` in an open dense set of such points, `h_1(x_0)` is not parallel to `a_i`", weakened from an open dense set to one point, which is all "The kinks stay" needs (the polynomial route of 2b). Generic for `d ≥ 2` and at least two units (4b). The paper's "at which another unit is active" is implied (`h(u₀)` would otherwise be `0 = 0 • a_i`).
5. For every `S` with at least two units a line and two entries with `quadRes ≠ 0`: in place of "two entries `h_a` and `h_b` of `h_1` have no common factor". It is stronger than coprimality on the region of `S` only in that it asks it for every `S`, also sets that are the active set of no `u`; it is still generic for `d ≥ 2`, because the witness of 4b (two units at `w = e₁, e₂`, `a = e₁ᵀ, e₂ᵀ`) does not need `S` to be a cell. As 2b shows, `quadRes ≠ 0` on one plane implies that `h^S_e`, `h^S_f` are coprime in `ℝ[x]`, so the clause implies the paper's condition for every `S`. (Whether the paper's coprimality alone implies the clause, i.e. whether coprime entries always have a plane without a common zero, I did not examine; at generic weights both hold.)
6. `∃ u, (∀ i, u ⬝ᵥ Wrᵀ i ≠ 0) ∧ IsUnit (∑ i, reluSqDeriv (u ⬝ᵥ Wrᵀ i) • vecMulVec (Wrᵀ i) (Ww i)).det`: one point off the kinks where the derivative `v ↦ v M` of `u ↦ ∑ max(u w_i, 0)² a_i` is invertible (`vecMul v (vecMulVec w a) = (v ⬝ᵥ w) • a`, so `M` is the Jacobian in the row convention). This is the input to "since `h_1` takes all values in an open set" through the inverse function theorem. Generic for `1 ≤ d ≤` width (4b); it needs at least `d` units, which is where the width enters.

All six are true for almost every `(W_read, W_write)` when `d ≥ 2` and there are at least `d` units (4b, 4c). Verdict: the definition is a correct (and slightly stronger in clause 5, slightly weaker in clauses 3 and 4) set of the paper's generic conditions; each departure is in the direction the proof needs, and the stronger one is still generic.

**3b. The three theorems (reading; proved at `6ca72ca`, resting there on the `sorry` of `reluSq_unitsParallelAt_of_generic`; all proved at `7de96aa`).**
- `rank_of_unitsGeneralPositionSq (hd : 2 ≤ card d) (hG)`: `Wr.rank = d`, `Ww.rank = d`, no zero column of `Wr`. Correct: `M = W_read · diag · W_write` is invertible (clause 6), so both factors have rank `d`; then the width is at least `d ≥ 2` and clause 1 excludes a zero column.
- `reluSq_unitsParallelAt_of_unitsGeneralPositionSq E (hd) (hE : E.rank = card d) hG : UnitsParallelAt reluSq reluSqDeriv 2 (fun i => (E * Wr)ᵀ i) (fun i => Ww i)`. Correct bridge: `x ⬝ᵥ (E W_read)ᵀ i = (x E) ⬝ᵥ w_i` (`dot_c_ugq`, from `vecMul_vecMul`), and `x ↦ x E` is onto `ℝ^d` because `E` has rank `d`, so each clause at `u` is pulled back to an `x` with `x E = u`, and non-collinearity of the `c_i` follows from that of the `w_i` (if `c_i = r c_j` then `u ⬝ᵥ w_i = r u ⬝ᵥ w_j` for all `u`). The columns `c_i ∈ ℝ^{d_in}` and the rows `a_i ∈ ℝ^d` are the paper's `c_i` (columns of `C = E W_read`) and `a_i`. **Without `hd`** the statement is still true and still the right one: for `d ≤ 1`, `hG` forces the block to have no unit (clause 5 for two units needs two entries; with one unit clause 4 fails), and `UnitsParallelAt` with no unit holds trivially; the proof does not use `hd`. Removing it loses nothing.
- `exists_open_reluSq_of_unitsGeneralPositionSq E (hE) hG`: a nonempty open `O ⊆ ℝ^d` every point of which is `∑ max(x c_i, 0)² a_i` at some `x` with `x c_i ≠ 0` for all `i`. Correct: inverse function theorem at the point of clause 6 (`HasStrictFDerivAt.map_nhds_eq_of_surj`), image of a neighbourhood off the hyperplanes, interior; `E` onto. This is "`h_1` takes all values in an open set" on the paper's inputs (no unit at its kink).

Verdict check 3: the six clauses are generic under the stated sizes; the three theorems are correct bridges.

### 4. At almost every parameter (the four statements and `ae_unitsGeneralPositionSq`)

**4a. The measure and the shape (reading, compiling).** Each statement is `∀ᵐ θ ∂μ, …` for every `μ : Measure (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)` with `[μ.IsAddHaarMeasure]`, any activation `σ` (the conditions read only `θ.read 0` and `θ.write 0`), `hid : Fin 1 → Type` with `Fintype`; `Params` carries the Borel σ-algebra (`Generic/Params.lean`). That is the paper's "generic" as "for almost every". Compiled a copy (`/home/claude/audit35a/ChkD0.lean`, `lake env lean` from `/home/claude/lp/lean`, no `lake build` running): the statement `ae_exists_isUnit_det_reluSqDeriv` applies at the concrete measure `Measure.addHaar` with `T = Fin 1`, `d = Fin 0`, `d_in = d_out = Fin 1`, one hidden unit.

**4b. The sizes (reading; one statement refuted by compiling).**

| statement | size hypotheses in Lean | true under exactly these? |
|---|---|---|
| `ae_forall_sum_reluSq_ne_zero` | none | Yes. `d = 0`: no unit is ever active (`u ⬝ᵥ w = 0`), vacuous. No unit: vacuous. One unit: `max(u w, 0)² a ≠ 0` where `u w > 0` as soon as `a ≠ 0`. `d = 1`: for `u > 0` the output is `u² ∑_{w_i > 0} w_i² a_i`, nonzero for almost every weight when the sum is not empty, and the same for `u < 0`. In general: at `u` with active set `S`, a zero is a common zero of the `d` forms `∑_{i∈S} (u w_i)² a_i`; for `|S| < d` the rows `a_i` are independent for almost every weight, for `|S| ≥ d` the paper's resultant argument applies. |
| `ae_exists_kink_point_reluSq` | `2 ≤ card d`, `2 ≤ card (hid 0)` | Yes, and both are needed: with one unit `h(u₀) = 0 = 0 • a_i`; with `d = 1` the hyperplane is `{0}`, which lies on every other hyperplane. With `d ≥ 2` and two units, the hyperplane of `w_i` contains points where another unit is active (the `w_j` are not collinear with `w_i` almost surely), and `h(u₀) ∥ a_i` is one polynomial condition. |
| `ae_exists_quadRes_ne_zero` | `2 ≤ card d` | Yes; needed when there are two units (`d = 1` leaves only `e = f`, and `quadRes(p, p) = 0`). For each `S` the resultant is a polynomial in `(W, u, v)`, not identically zero (`w = e₁, e₂`, `a = e₁ᵀ, e₂ᵀ` for two units of `S`, `a = 0` for the others, `u = e₁`, `v = e₂` give `quadRes(1,0,0,0,0,1) = 1`); this uses no cell, so it holds for sets `S` that are the active set of no `u` as well. |
| `ae_exists_isUnit_det_reluSqDeriv` | `card d ≤ card (hid 0)` | **No, for `d = 0` with at least one unit:** the only `u : Fin 0 → ℝ` has `u ⬝ᵥ w_i = 0`, so `∀ i, u ⬝ᵥ (θ.read 0)ᵀ i ≠ 0` fails at every `θ`, and a Haar measure is not zero. Compiled: `d0_false : False` from the statement at `Measure.addHaar`, `d = Fin 0`, one unit (axioms: `propext, sorryAx, Classical.choice, Quot.sound`, the `sorryAx` being the statement's own `sorry`). True for `1 ≤ card d ≤ card (hid 0)`: pick `d` units with independent `w_i`, a `u` with `u w_i = 1` there; by Cauchy–Binet the determinant is a nonzero polynomial in `W_write`. Repair: add `(hd : 1 ≤ Fintype.card d)` (or the `2 ≤` that `ae_unitsGeneralPositionSq` passes anyway). The combined statement and the network statements are not affected (they have `hd`). |
| `ae_unitsGeneralPositionSq` | `2 ≤ card d`, `card d ≤ card (hid 0)` | Yes (its proof calls the four with these sizes and `ae_unitsGeneralPosition`, which gives clauses 1 and 2). |

**4c. Numerical tests at random Gaussian weights (computation, `/home/claude/audit35a/ae4.py`, `ae4b.py`; outputs `ae4.out`, `ae4b.out`).**
- Clause 3 ("`h_1 ≠ 0` where a unit is active"), `d = 2`, 2 to 6 units, 400 parameters each: on 20000 directions of the circle, at those in `Ω`, the smallest `|h(u)| / ∑_i max(u w_i,0)² |a_i|` is `1.3e−3, 1.9e−3, 9.4e−4, 1.2e−3, 4.9e−4` for `q = 2, …, 6`: no real zero on `Ω`. (The relative resultants over active sets of two or more units printed beside it in `ae4.out` are normalized badly and are not used.)
- Clause 4 (a kink point), `d = 2, 3`, 2 to 6 units, 60 parameters each, 40 points of each hyperplane: the worst unit still has a point with `|h(u₀) − proj_{a_i} h(u₀)| / |h(u₀)| ≥ 2.4e−2` (`d = 2`) and `≥ 1.2e−1` (`d = 3`).
- Clause 5 (the resultant on a line), `d = 2, 3`, 2 to 5 units, 100 parameters, every set of at least two units, 5 random lines: the scale-free distance of the two entries to a common complex projective root is at least `1.7e−7` (`d = 2`, `q = 5`, 2600 sets) and `2e−4` (`d = 3`); it decreases with the number of sets tried, as the tail of a continuous distribution does, and is never `0`.
- Clause 6 (an invertible derivative), `d = 2, 3`, `d` to `d + 3` units, 200 parameters, at points `u` with `u w_i = 1` on `d` chosen units: the worst parameter still has `σ_min/σ_max ≥ 6.7e−5`. (A first version drew `u` at random and found parameters with no `u` among 50 at which `d` units are active; that was the sampling, not the clause.)
- The first statement for one unit or `d = 1`: by reading (4b), true; nothing to compute.

Verdict check 4: generic means almost every, for every Haar measure; `ae_forall_sum_reluSq_ne_zero`, `ae_exists_kink_point_reluSq`, `ae_exists_quadRes_ne_zero`, `ae_unitsGeneralPositionSq` are true under exactly their hypotheses; **`ae_exists_isUnit_det_reluSqDeriv` is FALSE at `card d = 0` with at least one hidden unit** (compiled), true for `card d ≥ 1`; nothing downstream is affected. **Repaired in `7de96aa`** (`[Nonempty d]`; see the last section of Part 1).

### 5. The value, the batch and the gain: ranks (computation; reading in 5b below)

Script `/home/claude/audit35a/rank5.py` (numpy, double precision). The network is Lean's `eval` for `Arch.mlp reluSq (rmsNorm 0) hid` with `L = 1`: `h₀ = x E`, `h₁ = h₀ S + max(N(h₀) W_read, 0)² W_write`, output `N(h₁) D`, `N(h) = √d h/|h|` row by row, `S = 0` (skipless) or `S = 1` (residual). Exact derivative in the parameters by complex step (step `1e−30`; the active set is read from the real part, `N` is written with `∑ h²`, which is analytic). Batch: `8 P` inputs per parameter, spread over the directions of `h₀` (`x = u E⁺ + z`, `u` Gaussian in `ℝ^d`, `z` Gaussian in the kernel of `x ↦ x E`), each in the paper's domain (no unit within `1e−6` of its kink, no row of `h₁` of norm below `1e−6`), and a second batch drawn the same way. Rank at the largest gap of the singular values (normalized by the largest).

| `d` | units | `d_in` | `d_out` | `T` | `P` | skipless (two batches, at each of two parameters) | want `P − d² − d(d−1)/2 − 1 − s` | residual (two batches) | want `P − d(d−1)/2 − 1 − s` | smallest gap (decades) |
|---|---|---|---|---|---|---|---|---|---|---|
| 2 | 3 | 2 | 2 | 1 | 20 | 11, 11 | 11 | 15, 15 | 15 | 10.2 |
| 2 | 5 | 2 | 2 | 1 | 28 | 17, 17 | 17 | 21, 21 | 21 | 12.3 |
| 3 | 4 | 3 | 3 | 1 | 42 | 25, 25 | 25 | 34, 34 | 34 | 12.7 |
| 3 | 5 | 3 | 3 | 1 | 48 | 30, 30 | 30 | 39, 39 | 39 | 13.3 |
| 2 | 5 | 3 | 4 | 2 | 34 | 23, 23 | 23 | 27, 27 | 27 | 11.0 |
| 3 | 5 | 4 | 3 | 2 | 51 | 33, 33 | 33 | 42, 42 | 42 | 13.7 |
| 2 | 2 (width `d`) | 2 | 2 | 1 | 16 | 8, 8 | 8 | 12, 12 | 12 | 12.8 |
| 3 | 3 (width `d`) | 3 | 3 | 1 | 36 | 20, 20 | 20 | 29, 29 | 29 | 11.9 |

Every rank (2 parameters × 2 batches × 2 networks per row) equals the value of the statements, and the residual minus the skipless rank is `d²` (4 or 9) in every row. Output in `/home/claude/audit35a/rank5.out`.

One warning about the method, which cost a false alarm: in a first run with inputs drawn Gaussian in `x` (not spread over the directions of `h₀`), one parameter (`d = 2`, 3 units, seed 230) gave skipless rank 9 instead of 11, with the last kept singular value at `2e−9`. Its embedding has condition number `4·10³`, so the rows `x E` cluster near one direction; with 2000 inputs, or with inputs spread over the directions of `h₀`, the rank there is 11 (gap 10.2 decades), and small perturbations of that parameter also give 11. It was a batch that did not reach the cells, not a counterexample.

**5b. The three network statements against Theorem B.1 (iv) (reading).**
- `ae_funDim_reluSq_oneBlock_skipless_rmsNorm_zero_of_le`: `∀ᵐ θ ∂μ, funDim (Arch.mlp reluSq (rmsNorm 0) hid) 0 θ + (card d ^ 2 + (card d * (card d - 1) / 2 + 1) + card (hid 0)) = finrank ℝ (Params …)`. The value `P − d² − d(d−1)/2 − 1 − s` written additively (no truncated subtraction; `d(d−1)` is even, so `/ 2` is exact), `P = finrank` of the parameters (`E`, `W_read`, `W_write`, `D`, no biases), `s = card (hid 0)` the number of hidden units (one rescaling per ReLU² unit), stream matrix `0` (skipless), `ε = 0`. Hypotheses: `2 ≤ card d`, `card d ≤ card dIn`, `card d ≤ card dOut`, `card d ≤ card (hid 0)`: the theorem's "`d_model ≥ 2`, the input and output dimensions at least `d_model`", "of width at least `d_model`". Nothing extra. `T` is any nonempty finite type of tokens (the theorem asks at least two tokens only for attention). SAME (with `funDim`, see check 6).
- `ae_exists_jacobianRank_reluSq_oneBlock_skipless_rmsNorm_zero_of_le`: a finite batch in `skiplessZeroDomain θ ∩ noKinkRMS θ` (no zero row of `x E`, no zero row of the block's output, which is `h₁` for the skipless network; no zero entry of `x E W_read`, the same kinks as `N(x E) W_read` since `N` scales rows by positive numbers) with the same rank. These are the paper's inputs. SAME.
- `ae_funDim_reluSq_oneBlock_residual_rmsNorm_zero_eq_add_of_le`: `funDim … 1 θ = funDim … 0 θ + card d ^ 2`, the paper's "by exactly `d_model²` for ReLU² blocks", proved from the residual value `ae_funDim_reluSq_oneBlock_residual_rmsNorm_zero` (proved earlier, twenty-first audit) and the skipless value (`omega`). Its `[Nonempty (hid 0)]` is obtained from `hcard` and `hd`. SAME.
- Numerically (5, the table): both values and the gain hold at every parameter tried.

**5c. Is part (iv) stated in full (reading `STATEMENTS.md`, rows 1108 to 1132).**

| sentence of (iv) | ReLU | ReLU² | ReGLU |
|---|---|---|---|
| residual value `P − d(d−1)/2 − 1 − s` (with a batch of the paper's inputs) | `OneBlock/ResidualRMSZeroRescaleGeneric.lean` (row 1118) | same file (row 1118) | rows 1119, 1120 |
| skipless "at most `P − d² − d(d−1)/2 − 1 − s`" | `ae_…` in row 1108 (width ≥ `d`) | row 1108 | row 1109 |
| "with equality", width exactly `d` | `OneBlock/SkiplessHomogeneousRMSZeroEq.lean` (row 1132) | row 1132 | not claimed by the paper |
| "with equality", width at least `d` | `OneBlock/SkiplessReluWideRMSZero.lean` (row 1127) | **these files** (row 1131) | not claimed |
| "by at least `d_model²`" | row 1121 | row 1121 | row 1121 |
| "by exactly `d_model²`" | rows 1127, 1132 | rows 1131, 1132 | not claimed |
| "The redundancy is then that of the symmetries" | flat directions at one parameter: `flatOn_le_mlp_rescale_skipless_rmsNorm_zero_of_unitsParallelAt` (row 1125) and `flatOn_noKink_le_mlp_rescale_residual_rmsNorm_zero` (row 1117), at the parameters where the generic conditions hold; at almost every parameter only through the counts | same | the residual one (row 1119); the skipless network has only the bound |

So with these four files every numerical claim of part (iv) is stated, for all three kinds of block, at almost every parameter; once their `sorry`s are proved, part (iv) is complete for its counts. The last sentence ("The redundancy is then that of the symmetries") has no statement at almost every parameter; it follows from the counts together with the flat directions the symmetries give, but no row puts the two together.

Verdict check 5: SAME for the value, the batch and the gain; the ranks agree with them in every case computed.

### 6. Drift checks (reading)

- **"Generic" is "for almost every".** All five `ae_…` conditions and the three network statements are `∀ᵐ θ ∂μ` for an arbitrary `[μ.IsAddHaarMeasure]` on the full parameter space (4a). The pointwise theorems (`reluSq_unitsParallelAt_of_generic`, the three of `UnitsGeneralPositionSq.lean`) take the generic conditions as explicit hypotheses, which is the right shape. No drift.
- **The functional dimension.** `funDim` is the supremum over all finite batches of all inputs (`Dimension/Functional.lean`) of the rank of the Jacobian, with Mathlib's convention `fderiv = 0` where `θ ↦ F_θ(x)` is not differentiable (for ReLU², `σ` is `C¹`, so this happens only at inputs where a normalized row vanishes) and `N₀(0) = 0`. The paper's functional dimension is the largest rank over its own inputs (no normalized row vanishes, no unit at its kink). The batch statement gives "at least" on the paper's inputs, `funDim` gives "at most" (the paper's inputs are among all inputs), so the pair is the paper's statement. No drift.
- **Hypotheses not in the paper.** In the pointwise theorems: `hres` replaces "no common factor" and is stronger by asking it for every set of at least two units (generic, 3a); clause 6 and clause 2 make explicit what the paper uses. Redundant ones: `hcc` (from `hkink`) and `ha` (from `hres`) in `reluSq_unitsParallelAt_of_generic`, `hd` in `reluSq_unitsParallelAt_of_unitsGeneralPositionSq` (to be removed). In the network statements: none beyond the theorem's. The one statement whose size hypotheses are too weak is `ae_exists_isUnit_det_reluSqDeriv` (4b).
- **What the paper proves for `k = 2` and more units than coordinates.** "for generic parameters `h_1 ≠ 0` there. Indeed, […] If `|S| ≥ d_model` and `k = 2`, the entries of `h1` are `d_model` quadratic forms in `xE`. A common zero other than `0`, real or complex, makes their resultant vanish. The resultant is a polynomial in the weights, and it is nonzero at `w_i = e_i`, `a_i = e_iᵀ` for `d_model` units of `S` and `a_i = 0` for the others": proved. "For generic parameters and `x_0` in an open dense set of such points, `h_1(x_0)` is not parallel to `a_i`": asserted, no argument. "for generic parameters two entries `h_a` and `h_b` of `h_1` have no common factor": asserted, no argument. "since `h_1` takes all values in an open set": asserted (it needs a point with an invertible derivative, hence at least `d` units active somewhere). So of the conditions of "The kinks stay" and "One scale" the paper proves only `h_1 ≠ 0`; the coordinator's header says so correctly.

### 7. The index rows (reading `STATEMENTS.md` at the commit read)

- Row of `OneBlock/QuadraticResultant.lean` (line 1128): true of the statements. "Symbolic check of the first (the five coefficient equations have rank five where the resultant is not zero)": confirmed (1c: solution space of dimension one in six unknowns at every one of the random pairs with `quadRes ≠ 0`).
- Row of `OneBlock/UnitsParallelAtSq.lean` (line 1129): true of the statement; the five conditions are listed correctly, and "The last condition replaces the paper's 'no common factor', which the paper does not show to hold for generic parameters" is right. It omits that the first condition follows from the fourth and the second from the fifth (2c), as the ReLU row (line 1124) says for its twin.
- Row of `OneBlock/UnitsGeneralPositionSq.lean` (line 1130): true. "for `E` of rank `d ≥ 2`" describes the hypothesis `hd` that is to be removed; after that, "`d ≥ 2`" should go from the sentence on `UnitsParallelAt` (it stays for `rank_of_unitsGeneralPositionSq`).
- Row of `OneBlock/SkiplessReluSqWideRMSZero.lean` (line 1131): the sentence "for `ε = 0`, `d_in, d_out ≥ d ≥ 2` and at least `d` hidden units: at almost every parameter each of the four conditions … holds (one statement each)" is true of the conditions under those sizes, but the statements carry other sizes: none for the first, `d ≥ 2` and two units for the second, `d ≥ 2` for the third, and only `d ≤` width for the fourth, which is false at `d = 0` (4b). "The paper proves '`h_1 ≠ 0`' with the resultant of `d_model` quadratic forms and does not show its condition on two entries for generic parameters": true; it does not show the condition on kink points (`h_1(x_0)` not parallel to `a_i`) or the open set of values either.
- Line 393 lists the four files as "Not yet compared": to be updated with this audit.
- No registrations or axioms checked (three of the four files have `sorry`; `UnitsGeneralPositionSq.lean` has none of its own but rests on `reluSq_unitsParallelAt_of_generic`).

## The change at 11:49 UTC (commit `7de96aa`), compared on request

During this audit the coordinator reported that two statements changed in `7de96aa` (after `6ca72ca`, where I began) and that all four files are now proved. I compared the new commit (copies of the four files at both commits in `/home/claude/audit35a/old/`, `/home/claude/audit35a/new/`; statement texts extracted and compared by `/home/claude/audit35a/stmts.py` and `diff`; a compiled check `/home/claude/audit35a/ChkNew.lean` against the build of `/home/claude/lp/lean`, whose `.olean` files are newer than the sources, with no `lake build` running).

- **Only two public statements changed**; `quadRes`, `UnitsGeneralPositionSq`, the two resultant statements, `reluSq_unitsParallelAt_of_generic`, `rank_of_unitsGeneralPositionSq`, `exists_open_reluSq_of_unitsGeneralPositionSq` and the other seven statements of `SkiplessReluSqWideRMSZero.lean` have the same text, and the `variable` lines are unchanged. Nothing outside the four files, `STATEMENTS.md` and `checks/Axioms.lean` changed between the commits.
- **`ae_exists_isUnit_det_reluSqDeriv` now has `[Nonempty d]`.** This is the repair of the falsehood of 4b (my compiled `d0_false` at `6ca72ca`; the prover found the same case). With `card d ≥ 1` and `card d ≤ card (hid 0)` the statement is true (4b: `d` units with independent `w_i`, a `u` with `u w_i = 1` on them moved off the other hyperplanes, Cauchy–Binet), and it is now proved. Compiled: `isUnit_concrete35`, the statement at `Measure.addHaar` with `d = Fin 2` and two units, so it is not vacuous. Its one call site `ae_unitsGeneralPositionSq` (with `hd : 2 ≤ card d`) is unchanged as a statement. Verdict: right.
- **`reluSq_unitsParallelAt_of_unitsGeneralPositionSq` has lost `hd`.** Signature now `(E) {Wr Ww} (hE : E.rank = card d) (hG : UnitsGeneralPositionSq Wr Ww)`. As said in 3b, it is still true and the right statement (for `d ≤ 1`, `hG` forces no hidden unit, where the conclusion is trivial); it is proved.
- **Degenerate cases** (`d` empty, `hid 0` empty, `T` empty). All fourteen theorems are now proved with the axioms `propext, Classical.choice, Quot.sound` only (compiled `#print axioms` for each), so none is false in any case; what is left is whether a case makes one vacuous or makes it say something other than the paper:
  - `d` empty: `ae_forall_sum_reluSq_ne_zero` holds vacuously (no unit is ever active); `ae_exists_kink_point_reluSq`, `ae_exists_quadRes_ne_zero`, `ae_unitsGeneralPositionSq` and the three network statements exclude it by `2 ≤ card d`; `ae_exists_isUnit_det_reluSqDeriv` by `[Nonempty d]`. In the pointwise theorems `hG` (or `hkink` with `ha`) forces no hidden unit, and the conclusions are then trivial.
  - `hid 0` empty: `ae_forall_sum_reluSq_ne_zero` and `ae_exists_quadRes_ne_zero` hold vacuously, which is right (nothing to say); `ae_exists_kink_point_reluSq` excludes it (`2 ≤ card (hid 0)`); `ae_exists_isUnit_det_reluSqDeriv` with `[Nonempty d]` and `card d ≤ 0` is vacuous; the network statements exclude it (`card d ≤ card (hid 0)`).
  - `T` empty: the conditions do not involve `T` (the parameters have no index `T`; the five condition statements `omit [Fintype T] [Nonempty T]`); the three network statements carry `[Nonempty T]` (compiled `#check`), and they need it (with no token the output is empty and `funDim = 0`).
  - `d_in` or `d_out` smaller than `d`: excluded by `hdIn`, `hdOut` in the network statements, where they are the theorem's hypotheses.
  Compiled `gain_concrete35`: `ae_funDim_reluSq_oneBlock_residual_rmsNorm_zero_eq_add_of_le` at `Measure.addHaar`, one token, `d = d_in = d_out = 2`, three units, reading `funDim … 1 θ = funDim … 0 θ + 4` almost everywhere.
- **Registrations.** `checks/Axioms.lean` gained the fourteen public theorems of the four files (the two definitions `quadRes`, `UnitsGeneralPositionSq` need none).
- **Index rows at `7de96aa`.** The rows of `QuadraticResultant`, `UnitsParallelAtSq`, `UnitsGeneralPositionSq`, `SkiplessReluSqWideRMSZero` (now "proved") are true of the statements. The `UnitsGeneralPositionSq` row now reads "for `E` of rank `d`: `UnitsParallelAt` … and a nonempty open set …; for `d ≥ 2`, the ranks", which is right. The `SkiplessReluSqWideRMSZero` row now states the `d ≥ 1` of the derivative statement and why; its opening "for `ε = 0`, `d_in, d_out ≥ d ≥ 2` and at least `d` hidden units" is still a blanket over statements that ask less each (none for the first; `d ≥ 2` and two units for the second; `d ≥ 2` for the third; `1 ≤ d ≤` width for the fourth), which is harmless but could say so. The `UnitsParallelAtSq` row still does not say that its first condition follows from the fourth and its second from the fifth. The line on audits ("with the thirty-fifth reader, part A, since 11:27; two statements changed at 11:49 UTC …") is accurate.

## Part 2: the statements, file by file (texts at `7de96aa`)

| Lean | paper sentence | verdict | note |
|---|---|---|---|
| `quadRes` | (the resultant in "no common factor", one variable) | SAME | the Sylvester resultant of two quadratics with formal degree two; zero exactly at a common complex projective root, also at infinity (1a) |
| `quad_proportional_of_quadRes_ne_zero` | "From `J_a h_b = J_b h_a`, `h_a` divides `J_a`, so `J = c h_1`" (two entries, degree two, one variable) | SAME | identity asked only for `|t| < δ`; true; fails with `quadRes = 0` (`p = 1`, `r = t`, `j = t`, `k = t²`) |
| `quad_vec_proportional_of_quadRes_ne_zero` | "so `J = c h_1` for a number `c`" (on a line) | SAME | `h(t) ≠ 0` for all `t` once two entries have `quadRes ≠ 0`; true |
| `reluSq_unitsParallelAt_of_generic` | "The kinks stay" (`k = 2`) and "One scale", with the paper's "for generic parameters" as hypotheses | SAME (with the paper's step to `b_i = c a_i` taken) | `hcc` follows from `hkink`, `ha` from `hres`; `hne` not needed here; `hkink` needed; `hres` sufficient, no case found where it is needed (2c, 2d); exact counts `q + 1` (2b) |
| `UnitsGeneralPositionSq` | the four "for generic parameters" of the skipless equality, `k = 2` | SAME in substance | clause 3 for real `u` only (all the proof uses); clause 4 one point instead of an open dense set; clause 5 stronger (every `S`), still generic; clause 6 makes "takes all values in an open set" a hypothesis at one point (3a) |
| `rank_of_unitsGeneralPositionSq` | (used: `W_read`, `W_write` of rank `d`) | SAME | from clause 6 |
| `reluSq_unitsParallelAt_of_unitsGeneralPositionSq` | bridge to `c_i` = columns of `E W_read` | SAME | `hd` removed in `7de96aa`; right without it (3b) |
| `exists_open_reluSq_of_unitsGeneralPositionSq` | "since `h_1` takes all values in an open set" | SAME | at rows off the kinks |
| `ae_forall_sum_reluSq_ne_zero` | "for generic parameters `h_1 ≠ 0` there" | SAME (real zeros only) | no size hypothesis, none needed |
| `ae_exists_kink_point_reluSq` | "For generic parameters … `h_1(x_0)` is not parallel to `a_i`" | SAME (one point) | `d ≥ 2`, two units: both needed |
| `ae_exists_quadRes_ne_zero` | "for generic parameters two entries `h_a` and `h_b` of `h_1` have no common factor" | LEAN STRONGER (implies it, for every set of two or more units) | generic for `d ≥ 2`; the paper gives no proof of its own condition |
| `ae_exists_isUnit_det_reluSqDeriv` | "since `h_1` takes all values in an open set" (generic) | at `6ca72ca`: FALSE for `d = 0` with a unit (compiled); at `7de96aa`, with `[Nonempty d]`: SAME | width `≥ d` is where the width enters |
| `ae_unitsGeneralPositionSq` | all of the above together | SAME | `d ≥ 2`, width `≥ d` |
| `ae_funDim_reluSq_oneBlock_skipless_rmsNorm_zero_of_le` | (iv): skipless "equality for … ReLU² blocks", width `≥ d` | SAME | Lean's `funDim`; ranks agree (5) |
| `ae_exists_jacobianRank_reluSq_oneBlock_skipless_rmsNorm_zero_of_le` | the same on the paper's inputs | SAME | with the previous row, the paper's functional dimension |
| `ae_funDim_reluSq_oneBlock_residual_rmsNorm_zero_eq_add_of_le` | (iv): "by exactly `d_model²` for … ReLU² blocks" | SAME | ranks: difference `d²` in every case (5) |

## For the authors of the papers

Nothing false, vacuous or drifted remains at `7de96aa`. At `6ca72ca`, one statement was false in a degenerate case (`ae_exists_isUnit_det_reluSqDeriv` at `d = 0` with one hidden unit). It is repaired, and nothing in the paper depends on it.

What the paper's proof of Theorem B.1 (iv), "The skipless network: equality", needs for ReLU² blocks wider than `d_model` and does not write:
1. Of its generic conditions it proves only "`h_1 ≠ 0` on `Ω`" (the resultant of `d_model` quadratic forms). Three are asserted without an argument: "`h_1(x_0)` is not parallel to `a_i`" (for `x_0` in an open dense set of the hyperplane), "two entries `h_a` and `h_b` of `h_1` have no common factor" on a region with two or more active units, and "`h_1` takes all values in an open set". Each is true for generic weights. Short arguments: for the second, a nonzero value of the polynomial (two units at `w = e_1, e_2`, `a = e_1^T, e_2^T`, the others `a = 0`); for the third, a point where `d_model` units are active and Cauchy–Binet; for the first, one polynomial condition on a ray of the hyperplane where another unit is active. A sentence each would close the gap.
2. "Two entries have no common factor" is used on each region with its own pair of entries; it is enough to ask it of every set of at least two units, and that stronger form is still generic. The step from "`J = c_S h_1` on each region" to one `c` uses that `h_1` does not vanish identically on any facet between regions; this follows from the coprimality (a common linear factor would be a common factor).
3. "One scale" ends with `J = c h_1` on `Ω`. That each `b_i = c a_i` follows from the linear independence of the functions `max(x c_i, 0)^k` for pairwise non-collinear `c_i`, which the paper uses implicitly in "Counting".
4. For `d_model = 2`, Lean's condition on two entries (a nonzero resultant on one line) also gives `h_1 ≠ 0` on `Ω`, and none of my exact searches (2d) needed it beyond `h_1(x_0)` not parallel to `a_i`. The paper's conditions are sufficient as stated. Whether the condition on two entries can be dropped I leave open.

## Corrections for `STATEMENTS.md` (at `7de96aa`)

- Row of `OneBlock/UnitsParallelAtSq.lean`: add, as the ReLU row does for its twin, "(the first condition follows from the fourth and the second from the fifth; the third is not used for this statement, and for two coordinates it follows from the second and the fifth: thirty-fifth audit, part A)". Optionally: "no example was found where the fifth is needed beyond the others (exact search, two coordinates)".
- Row of `OneBlock/SkiplessReluSqWideRMSZero.lean`: replace the blanket "for `ε = 0`, `d_in, d_out ≥ d ≥ 2` and at least `d` hidden units: at almost every parameter each of the four conditions … holds (one statement each)" by the sizes each statement asks: none for "`h_1 ≠ 0`"; `d ≥ 2` and two units for the kink point; `d ≥ 2` for the resultant; `1 ≤ d ≤` width for the invertible derivative. Add that the paper does not show the kink-point condition or the open set of values either, not only the condition on two entries.
- The line on audits ("Not yet compared … with the thirty-fifth reader, part A, since 11:27 …"): replace by a sentence that this audit compared the four files at `6ca72ca` and `7de96aa` (16 statements and definitions) and found one statement false at `6ca72ca` in a degenerate case (`d = 0`), repaired in `7de96aa`, nothing false, vacuous or drifted at `7de96aa`, with a pointer to `ai_notes/lean-statement-audit-thirtyfifth-a-2026-11-25.md`.
- No other correction. The rows of `QuadraticResultant.lean` and `UnitsGeneralPositionSq.lean` are true as they stand at `7de96aa`.

## What I could not check

- I did not prove that `hres` is needed or redundant in `reluSq_unitsParallelAt_of_generic`. The search was exact but random, in two input coordinates only. For three or more coordinates I have only the argument of 2b and the coordinator's script (which does not test the hypotheses).
- "`hne` is not needed for `reluSq_unitsParallelAt_of_generic`" rests on my reading of the argument (2c), not on a computation in three or more coordinates.
- I did not read the proofs (all fourteen now compile with the standard axioms; that is checked, the route is not).
- The ranks of check 5 are in double precision with the complex-step derivative. The gaps are 10 to 14 decades, but they are not certified bounds as ball arithmetic would give. No ReGLU network was computed (ReGLU was not among this audit's files).
- The header of `SkiplessReluSqWideRMSZero.lean` describes the route of the proof of "`h_1 ≠ 0`". I did not compare it with the proof.
