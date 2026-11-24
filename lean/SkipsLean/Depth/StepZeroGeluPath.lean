import SkipsLean.Depth.GeluPathSeparation
import SkipsLean.Depth.SuffixCongr
import SkipsLean.Depth.CondP
import SkipsLean.Activations.Analytic

/-!
# The step for GELU on the path: what one pair `ξ, ξ'` gives

Paper (dimension paper): Appendix D.6 (the case `ε = 0`), proof of Lemma D.19 (the step for GELU
on the path), its parts "The path", "The expansion", "Step 1" and the analytic part of "Step 2" and
"Step 4", for one pair of rows.

"The path. Fix `ξ ∈ P` and a unit row `ξ'` orthogonal to `ξ`, let `n(t)` be the path (41), and
`z_j(t) = n(t) c_j`, `r_j = (ξc_j)² − (ξ'c_j)² > 0`, `δ_j(t) = z_j − σ(z_j)`,
`δ'_j(t) = 1 − σ'(z_j)`. […] The real and the imaginary part of `n(t) W V` are
`√d ((t + t⁻¹)/2) ξ W V` and `√d ((t − t⁻¹)/2) ξ' W V`. By (P2), the second is shorter than `κ/2`
times the first, and by (45) `‖δ(t) V‖ ≤ ∑_j |δ_j| ‖a_j‖` is at most `κ/8` times the norm of the
first. Let `ϱ = κ √d ‖ξ W V‖ / (16 ∑_j ‖a_j‖)`. For a row `δ ∈ ℂ^{1×q}`,

  `|δ_j| ≤ ϱ t` for all `j`, or `δ = δ(t)`  ⟹  `(z(t) − δ) V = n(t) W V − δ V ∈ C_κ`,   (46)

[…]. As `σ(z) = z − δ(t)` and `σ'(z) = 1 − δ'(t)` on the path, Lemma D.15 applies:
`𝓛(z(t) − δ(t), 1 − δ'(t); n(t)) = 0` for all `t ≥ 1` (47)."

"Step 1: […] `𝓛_0(t) = 0` for large `t`, and then for all `t ≥ 1`, because it is holomorphic near
`[1, ∞)`. At `t = 1`, where `n(t)` is the row `n = √d ξ`, this reads […]
`0 = 𝓛(nW, 1; n)`." "Step 2: […] `𝓛'_j(t) = 0` and `𝓛_j(t) = 0` for large `t`, hence for all
`t ≥ 1` (50). By (21), with `ż_j` the entry `j` of `ż`, `𝓛'_j(t) = ż_j(n(t)) 𝐃𝓑(n(t) W V) a_j`."
"Step 4: […] So in the expansion (48) of `𝓛°` every term has a factor `δ_l(t)` or `δ'_l(t)` of a
unit `l` other than `j_1, …, j_{i−1}`. […] we get (50) as in Step 2."

**Stated here,** for one orthonormal pair `ξ, ξ'` with the three inequalities of (P2)
(`PathP2`, `Depth/CondP.lean`), a regular `θ`, a cone `C_κ`, `0 < κ ≤ 1`, on which `𝓑_{>k+1}` is
holomorphic, and a pair `Z, η` with the identity (16) before block `k`; the path has the same row
at every token, `n = √d ξ` is its row at `t = 1`, and `ż(n)` is (20):

* `gelu_path_step_zero` (Step 1): `𝓛(n(t)W, 1; n(t)) = 0` for all `t ≥ 1`, at complex arguments;
  `gelu_path_step_zero_real` is its case `t = 1` with the real `𝓛` (`blockLHS`).
* `gelu_path_step_unit` (Steps 2 and 4, (50) at `t = 1`): let `A` be a set of hidden units such
  that `𝓛(z(t) − δ, 1 − δ'; n(t)) = 0` for all `t ≥ 1` and all complex rows `δ, δ'` whose entries
  outside `A` vanish (for `A = ∅` this is Step 1; in Step 4, `A = {j_1, …, j_{i−1}}`), and let the
  unit `j ∉ A` have a smaller rate `r_j` than every other unit outside `A`. Then `𝓛_j(1) = 0`,
  stated as: the derivative at `τ = 0` of `τ ↦ 𝓛(nW − τ e_j, 1; n)` vanishes; and `𝓛'_j(1) = 0`,
  stated as `𝐃𝓑(n W V)(ż_j(n) a_j) = 0`.

The proof goes through the map `Ψ` of `Depth/GeluPathSeparation.lean`: with `s = 1/t`,
`m(s) = (1 + s²) ξ + i (1 − s²) ξ'` and `λ = √d t/2`, so that `n(t) = λ m(s)`, the homogeneity of
`𝓛` (`blockLHSC_smul`) gives `𝓛(λw, w'; ż(λm)) = t² Ψ(s, (x, y))` for `w = m(s)W − x`,
`w' = 1 − y`, with `Ψ = s² 𝓛(w, w'; m(ZW + η_W)) − (1/4) ⟨mZ, m⟩ 𝐃𝓑(wV)((w' ⊙ mW)V)`.
Numbering as in `Depth/StepTanh.lean`: the block is `k : Fin L`, the paper's block `k + 1`.
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut] {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]

/-! ### Euclidean norms of real rows -/

/-- Helper: the Euclidean norm `√(v ⬝ᵥ v)` is the norm of `v` in `EuclideanSpace`. -/
private theorem sqrt_dot_gzp {ι : Type*} [Fintype ι] (v : ι → ℝ) :
    Real.sqrt (v ⬝ᵥ v) = ‖(WithLp.toLp 2 v : EuclideanSpace ℝ ι)‖ := by
  rw [EuclideanSpace.norm_eq]
  congr 1
  simp only [dotProduct, Real.norm_eq_abs, sq, abs_mul_abs_self]

/-- Helper: `√(v ⬝ᵥ v)² = v ⬝ᵥ v`. -/
private theorem sqrt_dot_sq_gzp {ι : Type*} [Fintype ι] (v : ι → ℝ) :
    Real.sqrt (v ⬝ᵥ v) ^ 2 = v ⬝ᵥ v :=
  Real.sq_sqrt (Finset.sum_nonneg fun j _ => mul_self_nonneg (v j))

/-- Helper: `‖x V‖ ≤ ∑_j |x_j| ‖a_j‖` for the rows `a_j` of `V` (Euclidean norms). -/
private theorem sqrt_dot_vecMul_le_gzp {ι m : Type*} [Fintype ι] [Fintype m] (x : ι → ℝ)
    (V : Matrix ι m ℝ) :
    Real.sqrt ((x ᵥ* V) ⬝ᵥ (x ᵥ* V)) ≤ ∑ j, |x j| * Real.sqrt (V j ⬝ᵥ V j) := by
  rw [sqrt_dot_gzp, vecMul_eq_sum, WithLp.toLp_sum]
  refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun j _ => ?_))
  rw [WithLp.toLp_smul, norm_smul, Real.norm_eq_abs, sqrt_dot_gzp]

/-- Helper: `‖c u − e‖ ≥ c ‖u‖ − ‖e‖` for `c ≥ 0`. -/
private theorem sqrt_dot_sub_ge_gzp {ι : Type*} [Fintype ι] (u e : ι → ℝ) {c : ℝ} (hc : 0 ≤ c) :
    c * Real.sqrt (u ⬝ᵥ u) - Real.sqrt (e ⬝ᵥ e) ≤ Real.sqrt ((c • u - e) ⬝ᵥ (c • u - e)) := by
  rw [sqrt_dot_gzp, sqrt_dot_gzp, sqrt_dot_gzp, WithLp.toLp_sub, WithLp.toLp_smul]
  have h := norm_sub_norm_le (c • (WithLp.toLp 2 u : EuclideanSpace ℝ ι))
    (WithLp.toLp 2 e : EuclideanSpace ℝ ι)
  rwa [norm_smul, Real.norm_of_nonneg hc] at h

/-- Helper: `‖c u − e‖ ≤ c ‖u‖ + ‖e‖` for `c ≥ 0`. -/
private theorem sqrt_dot_sub_le_gzp {ι : Type*} [Fintype ι] (u e : ι → ℝ) {c : ℝ} (hc : 0 ≤ c) :
    Real.sqrt ((c • u - e) ⬝ᵥ (c • u - e)) ≤ c * Real.sqrt (u ⬝ᵥ u) + Real.sqrt (e ⬝ᵥ e) := by
  rw [sqrt_dot_gzp, sqrt_dot_gzp, sqrt_dot_gzp, WithLp.toLp_sub, WithLp.toLp_smul]
  refine (norm_sub_le _ _).trans (le_of_eq ?_)
  rw [norm_smul, Real.norm_of_nonneg hc]

/-- Step 2, the real inequality: with `U = ‖u‖ > 0`, `‖u'‖ < (κ/2) U`, `‖e‖, ‖f‖ ≤ β` and
`β ≤ (κ/4)(s + 1/2) U`, the rows `A = (1 + s²) u − e`, `B = (1 − s²) u' − f` satisfy
`‖B‖² < κ² ‖A‖²`. -/
private theorem cone_real_gzp {ι : Type*} [Fintype ι] (u u' e f : ι → ℝ) {κ s β : ℝ}
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hu' : Real.sqrt (u' ⬝ᵥ u') < κ / 2 * Real.sqrt (u ⬝ᵥ u))
    (he : Real.sqrt (e ⬝ᵥ e) ≤ β) (hf : Real.sqrt (f ⬝ᵥ f) ≤ β)
    (hβ : β ≤ κ / 4 * (s + 1 / 2) * Real.sqrt (u ⬝ᵥ u)) :
    ((1 - s ^ 2) • u' - f) ⬝ᵥ ((1 - s ^ 2) • u' - f)
      < κ ^ 2 * (((1 + s ^ 2) • u - e) ⬝ᵥ ((1 + s ^ 2) • u - e)) := by
  have hU : 0 < Real.sqrt (u ⬝ᵥ u) := by
    have := Real.sqrt_nonneg (u' ⬝ᵥ u')
    by_contra h
    push Not at h
    nlinarith
  have hA := sqrt_dot_sub_ge_gzp u e (c := 1 + s ^ 2) (by positivity)
  have hB := sqrt_dot_sub_le_gzp u' f (c := 1 - s ^ 2) (by nlinarith)
  have hu'0 := Real.sqrt_nonneg (u' ⬝ᵥ u')
  have hs2 : 0 ≤ 1 - s ^ 2 := by nlinarith
  -- `‖B‖ < κ ‖A‖`
  have hBA : Real.sqrt (((1 - s ^ 2) • u' - f) ⬝ᵥ ((1 - s ^ 2) • u' - f))
      < κ * Real.sqrt (((1 + s ^ 2) • u - e) ⬝ᵥ ((1 + s ^ 2) • u - e)) := by
    have h1 : (1 - s ^ 2) * Real.sqrt (u' ⬝ᵥ u')
        ≤ (1 - s ^ 2) * (κ / 2 * Real.sqrt (u ⬝ᵥ u)) :=
      mul_le_mul_of_nonneg_left hu'.le hs2
    have h2 : κ * β ≤ κ * (1 / 4 * (s + 1 / 2) * Real.sqrt (u ⬝ᵥ u)) := by
      have h5 := mul_le_mul_of_nonneg_right hκ1
        (by positivity : 0 ≤ (s + 1 / 2) * Real.sqrt (u ⬝ᵥ u) / 4)
      have : β ≤ 1 / 4 * (s + 1 / 2) * Real.sqrt (u ⬝ᵥ u) := by linarith
      exact mul_le_mul_of_nonneg_left this hκ.le
    have h3 : κ * ((1 + s ^ 2) * Real.sqrt (u ⬝ᵥ u) - β)
        ≤ κ * Real.sqrt (((1 + s ^ 2) • u - e) ⬝ᵥ ((1 + s ^ 2) • u - e)) :=
      mul_le_mul_of_nonneg_left (by linarith) hκ.le
    have h4 : 0 < κ * Real.sqrt (u ⬝ᵥ u) * (1 / 4 - s / 2 + 3 / 2 * s ^ 2) := by
      have : 0 < 1 / 4 - s / 2 + 3 / 2 * s ^ 2 := by nlinarith [sq_nonneg (s - 1 / 6)]
      positivity
    nlinarith
  have h0 := Real.sqrt_nonneg (((1 - s ^ 2) • u' - f) ⬝ᵥ ((1 - s ^ 2) • u' - f))
  rw [← sqrt_dot_sq_gzp ((1 - s ^ 2) • u' - f), ← sqrt_dot_sq_gzp ((1 + s ^ 2) • u - e)]
  nlinarith

/-! ### The row `m(s)`, the matrices of `Ψ`, and the cone -/

/-- The row `m(s) = (1 + s²) ξ + i (1 − s²) ξ'`, so that `n(t) = λ m(1/t)`, `λ = √d t/2`. -/
private noncomputable def mrow_gzp (ξ ξ' : d → ℝ) (s : ℂ) : d → ℂ :=
  fun i => (1 + s ^ 2) * (ξ i : ℂ) + Complex.I * ((1 - s ^ 2) * (ξ' i : ℂ))

/-- The matrix with the row `v` at every token. -/
private def rowM_gzp (T' : Type*) {ι : Type*} (v : ι → ℂ) : Matrix T' ι ℂ :=
  Matrix.of fun _ => v

omit [Fintype d] [DecidableEq d] in
/-- Helper: the rows of `rowM_gzp`. -/
private theorem rowM_apply_gzp (T' : Type*) {ι : Type*} (v : ι → ℂ) (τ : T') :
    rowM_gzp T' v τ = v := rfl

/-- The matrix `w = m(s) W − x` (the same row at every token). -/
private noncomputable def wM_gzp (T' : Type*) {ι : Type*} (WC : Matrix d ι ℂ) (ξ ξ' : d → ℝ)
    (s : ℂ) (x : ι → ℂ) : Matrix T' ι ℂ :=
  Matrix.of fun _ i => (mrow_gzp ξ ξ' s ᵥ* WC) i - x i

/-- The matrix `w' = 1 − y` (the same row at every token). -/
private def wpM_gzp (T' : Type*) {ι : Type*} (y : ι → ℂ) : Matrix T' ι ℂ :=
  Matrix.of fun _ i => 1 - y i

omit [DecidableEq d] in
/-- Helper: the entries of `wM_gzp`. -/
private theorem wM_apply_gzp (T' : Type*) {ι : Type*} (WC : Matrix d ι ℂ) (ξ ξ' : d → ℝ)
    (s : ℂ) (x : ι → ℂ) (τ : T') (i : ι) :
    wM_gzp T' WC ξ ξ' s x τ i = (mrow_gzp ξ ξ' s ᵥ* WC) i - x i := rfl

/-- Helper: `(ρ + i ρ') M = ρM + i ρ'M` for real rows `ρ, ρ'` and a real matrix `M`. -/
private theorem cvec_gzp {ι m : Type*} [Fintype ι] (ρ ρ' : ι → ℝ) (M : Matrix ι m ℝ) :
    (fun i => (ρ i : ℂ) + Complex.I * (ρ' i : ℂ)) ᵥ* M.map (fun x : ℝ => (x : ℂ))
      = fun l => ((ρ ᵥ* M) l : ℂ) + Complex.I * ((ρ' ᵥ* M) l : ℂ) := by
  funext l
  simp only [vecMul, dotProduct, Matrix.map_apply, Complex.ofReal_sum, Complex.ofReal_mul,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

omit [Fintype d] [DecidableEq d] in
/-- Helper: at a real `s`, `m(s)` has the real part `(1 + s²) ξ` and the imaginary part
`(1 − s²) ξ'`. -/
private theorem mrow_ofReal_gzp (ξ ξ' : d → ℝ) (s : ℝ) :
    mrow_gzp ξ ξ' (s : ℂ) = fun i => ((((1 + s ^ 2) • ξ) i : ℝ) : ℂ)
      + Complex.I * ((((1 - s ^ 2) • ξ') i : ℝ) : ℂ) := by
  funext i
  simp only [mrow_gzp, Pi.smul_apply, smul_eq_mul]
  push_cast
  ring

omit [DecidableEq d] in
/-- Step 2: at a real `s`, the row `(m(s) W − x) V` has the real part `(1 + s²) ξWV − (Re x) V`
and the imaginary part `(1 − s²) ξ'WV − (Im x) V`. -/
private theorem row_eq_gzp {ι : Type*} [Fintype ι] (W : Matrix d ι ℝ) (V : Matrix ι d ℝ)
    (ξ ξ' : d → ℝ) (s : ℝ) (x : ι → ℂ) :
    (mrow_gzp ξ ξ' (s : ℂ) ᵥ* W.map (fun x : ℝ => (x : ℂ)) - x) ᵥ* V.map (fun x : ℝ => (x : ℂ))
      = fun l => ((((1 + s ^ 2) • (ξ ᵥ* (W * V)) - (fun j => (x j).re) ᵥ* V) l : ℝ) : ℂ)
        + Complex.I * ((((1 - s ^ 2) • (ξ' ᵥ* (W * V)) - (fun j => (x j).im) ᵥ* V) l : ℝ)
          : ℂ) := by
  have h1 : mrow_gzp ξ ξ' (s : ℂ) ᵥ* W.map (fun x : ℝ => (x : ℂ)) - x
      = fun j => ((((1 + s ^ 2) • (ξ ᵥ* W) - fun j => (x j).re) j : ℝ) : ℂ)
        + Complex.I * ((((1 - s ^ 2) • (ξ' ᵥ* W) - fun j => (x j).im) j : ℝ) : ℂ) := by
    rw [mrow_ofReal_gzp, cvec_gzp]
    funext j
    simp only [Pi.sub_apply, smul_vecMul, Pi.smul_apply, smul_eq_mul]
    apply Complex.ext <;> simp <;> ring
  rw [h1, cvec_gzp, sub_vecMul, sub_vecMul, smul_vecMul, smul_vecMul, vecMul_vecMul,
    vecMul_vecMul]

/-- Helper: the row with the real part `A` and the imaginary part `B` is in `C_κ` when
`‖B‖² < κ² ‖A‖²`. -/
private theorem mem_cone_gzp {ι : Type*} [Fintype ι] {κ : ℝ} (A B : ι → ℝ)
    (h : B ⬝ᵥ B < κ ^ 2 * (A ⬝ᵥ A)) :
    (fun l => (A l : ℂ) + Complex.I * (B l : ℂ)) ∈ complexCone κ := by
  show (fun i => ((A i : ℂ) + Complex.I * (B i : ℂ)).im)
      ⬝ᵥ (fun i => ((A i : ℂ) + Complex.I * (B i : ℂ)).im)
    < κ ^ 2 * ((fun i => ((A i : ℂ) + Complex.I * (B i : ℂ)).re)
      ⬝ᵥ (fun i => ((A i : ℂ) + Complex.I * (B i : ℂ)).re))
  simpa using h

omit [DecidableEq d] in
/-- **Step 2, the cone:** for a real `s ∈ [0, 1]` and a complex row `x` with
`∑_j ‖x_j‖ ‖a_j‖ ≤ (κ/4)(s + 1/2) ‖ξWV‖`, the row `(m(s) W − x) V` is in `C_κ`. -/
private theorem cone_gzp {ι : Type*} [Fintype ι] (W : Matrix d ι ℝ) (V : Matrix ι d ℝ) {κ : ℝ}
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) (ξ ξ' : d → ℝ)
    (h2 : Real.sqrt ((ξ' ᵥ* (W * V)) ⬝ᵥ (ξ' ᵥ* (W * V)))
      < κ / 2 * Real.sqrt ((ξ ᵥ* (W * V)) ⬝ᵥ (ξ ᵥ* (W * V))))
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (x : ι → ℂ)
    (hB : ∑ j, ‖x j‖ * Real.sqrt (V j ⬝ᵥ V j)
      ≤ κ / 4 * (s + 1 / 2) * Real.sqrt ((ξ ᵥ* (W * V)) ⬝ᵥ (ξ ᵥ* (W * V)))) :
    (mrow_gzp ξ ξ' (s : ℂ) ᵥ* W.map (fun x : ℝ => (x : ℂ)) - x) ᵥ* V.map (fun x : ℝ => (x : ℂ))
      ∈ complexCone κ := by
  rw [row_eq_gzp]
  refine mem_cone_gzp _ _ (cone_real_gzp _ _ _ _ hκ hκ1 hs0 hs1 h2 ?_ ?_ hB)
  · exact (sqrt_dot_vecMul_le_gzp _ V).trans (Finset.sum_le_sum fun j _ =>
      mul_le_mul_of_nonneg_right (Complex.abs_re_le_norm _) (Real.sqrt_nonneg _))
  · exact (sqrt_dot_vecMul_le_gzp _ V).trans (Finset.sum_le_sum fun j _ =>
      mul_le_mul_of_nonneg_right (Complex.abs_im_le_norm _) (Real.sqrt_nonneg _))

/-! ### The path -/

/-- The numbers `ω_j = (√d/2)(ξc_j + i ξ'c_j)`, so that `n(t) c_j = ω_j t + ω̄_j/t`. -/
private noncomputable def omega_gzp {ι : Type*} (W : Matrix d ι ℝ) (ξ ξ' : d → ℝ) : ι → ℂ :=
  fun j => ⟨Real.sqrt (Fintype.card d) / 2 * (ξ ᵥ* W) j,
    Real.sqrt (Fintype.card d) / 2 * (ξ' ᵥ* W) j⟩

omit [DecidableEq d] in
/-- Step 1: for real `t > 0`, `n(t) = λ m(1/t)` with `λ = √d t/2`. -/
private theorem pathRow_eq_gzp (ξ ξ' : d → ℝ) {t : ℝ} (ht : 0 < t) :
    pathRow ξ ξ' (t : ℂ)
      = ((Real.sqrt (Fintype.card d) * t / 2 : ℝ) : ℂ) • mrow_gzp ξ ξ' ((t⁻¹ : ℝ) : ℂ) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ht.ne'
  funext i
  simp only [pathRow, mrow_gzp, Pi.smul_apply, smul_eq_mul]
  push_cast
  field_simp
  ring

omit [Fintype T] [DecidableEq d] in
/-- Step 1: the path at every token is `λ` times the matrix with the row `m(1/t)`. -/
private theorem pathMatrix_eq_gzp (ξ ξ' : d → ℝ) {t : ℝ} (ht : 0 < t) :
    pathMatrix (Matrix.of fun _ : T => ξ) (Matrix.of fun _ : T => ξ') (t : ℂ)
      = ((Real.sqrt (Fintype.card d) * t / 2 : ℝ) : ℂ)
        • rowM_gzp T (mrow_gzp ξ ξ' ((t⁻¹ : ℝ) : ℂ)) := by
  ext τ i
  show pathRow ξ ξ' (t : ℂ) i = _
  rw [pathRow_eq_gzp ξ ξ' ht]
  rfl

omit [Fintype T] [DecidableEq d] in
/-- Step 1: `λ (m(1/t) W − x) = n(t) W − λ x`. -/
private theorem smul_wM_gzp {ι : Type*} (WC : Matrix d ι ℂ) (ξ ξ' : d → ℝ) {t : ℝ} (ht : 0 < t)
    (x : ι → ℂ) :
    ((Real.sqrt (Fintype.card d) * t / 2 : ℝ) : ℂ) • wM_gzp T WC ξ ξ' ((t⁻¹ : ℝ) : ℂ) x
      = Matrix.of fun τ i =>
        (pathMatrix (Matrix.of fun _ : T => ξ) (Matrix.of fun _ : T => ξ') (t : ℂ) * WC) τ i
          - ((Real.sqrt (Fintype.card d) * t / 2 : ℝ) : ℂ) * x i := by
  rw [pathMatrix_eq_gzp ξ ξ' ht, Matrix.smul_mul]
  ext τ i
  simp only [wM_apply_gzp, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul,
    Matrix.mul_apply_eq_vecMul, rowM_apply_gzp]
  ring

omit [Fintype T] [DecidableEq d] in
/-- Step 1: the hidden units on the path are `z_j(t) = ω_j t + ω̄_j/t`. -/
private theorem path_entry_gzp {ι : Type*} (W : Matrix d ι ℝ) (ξ ξ' : d → ℝ) {t : ℝ} (ht : 0 < t)
    (τ : T) (j : ι) :
    (pathMatrix (Matrix.of fun _ : T => ξ) (Matrix.of fun _ : T => ξ') (t : ℂ)
        * W.map (fun x : ℝ => (x : ℂ))) τ j = unitPath (omega_gzp W ξ ξ' j) t := by
  have e : (pathMatrix (Matrix.of fun _ : T => ξ) (Matrix.of fun _ : T => ξ') (t : ℂ)
        * W.map (fun x : ℝ => (x : ℂ))) τ j
      = ((Real.sqrt (Fintype.card d) * ((t + t⁻¹) / 2 * (ξ ᵥ* W) j) : ℝ) : ℂ)
        + Complex.I * ((Real.sqrt (Fintype.card d) * ((t - t⁻¹) / 2 * (ξ' ᵥ* W) j) : ℝ)
          : ℂ) := by
    rw [Matrix.mul_apply]
    simp only [pathMatrix, Matrix.of_apply, pathRow_ofReal, Matrix.map_apply, vecMul, dotProduct]
    push_cast
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [e]
  apply Complex.ext
  · rw [unitPath_re _ ht]
    simp [omega_gzp]
    ring
  · rw [unitPath_im _ ht]
    simp [omega_gzp]
    ring

/-! ### `ż` on the path, and `𝓛` affine in `w' ⊙ ż` -/

omit [Fintype T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Step 3: `ż(cM) = c (m(ZW + η_W) − (c² ⟨mZ, m⟩/d) mW)` for the matrix `M` with the row `m` at
every token. -/
private theorem zdotC_rowM_gzp
    (θ : Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm 0) hid) dIn dOut) (k : Fin L)
    (Z : Matrix d d ℝ) (η : Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm 0) hid) dIn dOut)
    (c : ℂ) (m : d → ℂ) :
    zdotC θ k Z η (c • rowM_gzp T m)
      = c • rowM_gzp T (m ᵥ* (Z.map (fun x : ℝ => (x : ℂ)) * θ.toC.1 k + η.toC.1 k)
        - (c ^ 2 * ((m ᵥ* Z.map (fun x : ℝ => (x : ℂ))) ⬝ᵥ m) / (Fintype.card d : ℂ))
          • (m ᵥ* θ.toC.1 k)) := by
  ext τ i
  have e : zdotC θ k Z η (c • rowM_gzp T m) τ
      = ((c • m) ᵥ* Z.map (fun x : ℝ => (x : ℂ))
          - ((((c • m) ᵥ* Z.map (fun x : ℝ => (x : ℂ))) ⬝ᵥ (c • m)) / (Fintype.card d : ℂ))
            • (c • m)) ᵥ* θ.toC.1 k
        + (c • m) ᵥ* η.toC.1 k := rfl
  rw [congrFun e i]
  simp only [Matrix.smul_apply, rowM_apply_gzp, smul_eq_mul, smul_vecMul, smul_dotProduct,
    dotProduct_smul, sub_vecMul, vecMul_add, vecMul_vecMul, Pi.add_apply, Pi.sub_apply,
    Pi.smul_apply]
  ring

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the zero matrix written entrywise. -/
private theorem of_zero_gzp {m n R : Type*} [Zero R] :
    (Matrix.of fun (_ : m) (_ : n) => (0 : R)) = 0 := rfl

omit [Fintype T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: `𝓛(w, w'; ż) = 𝐃𝓑(wV)((w' ⊙ ż)V) + 𝓛(w, 0; 0)`. -/
private theorem blockLHSC_split_gzp
    (θ : Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm 0) hid) dIn dOut) (k : Fin L)
    (η : Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm 0) hid) dIn dOut)
    (w w' z : Matrix T (hid k) ℂ) :
    blockLHSC geluC θ k η w w' z
      = fderiv ℂ (fun h' : Matrix T d ℂ => suffixC geluC θ.toC k.succ h') (w * θ.toC.2.1 k)
          ((Matrix.of fun t j => w' t j * z t j) * θ.toC.2.1 k)
        + blockLHSC geluC θ k η w 0 0 := by
  unfold blockLHSC
  simp only [map_add, Matrix.zero_apply, mul_zero, of_zero_gzp, Matrix.zero_mul, zero_add]
  abel

omit [Fintype T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Step 3: `𝓛` is affine in `ż`:
`𝓛(w, w'; a − c b) = 𝓛(w, w'; a) − c (𝓛(w, w'; b) − 𝓛(w, w'; 0))`. -/
private theorem blockLHSC_sub_smul_gzp
    (θ : Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm 0) hid) dIn dOut) (k : Fin L)
    (η : Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm 0) hid) dIn dOut)
    (w w' a b : Matrix T (hid k) ℂ) (c : ℂ) :
    blockLHSC geluC θ k η w w' (a - c • b)
      = blockLHSC geluC θ k η w w' a
        - c • (blockLHSC geluC θ k η w w' b - blockLHSC geluC θ k η w w' 0) := by
  rw [blockLHSC_split_gzp θ k η w w' (a - c • b), blockLHSC_split_gzp θ k η w w' a,
    blockLHSC_split_gzp θ k η w w' b, blockLHSC_split_gzp θ k η w w' 0]
  have e1 : (Matrix.of fun t j => w' t j * (a - c • b) t j) * θ.toC.2.1 k
      = (Matrix.of fun t j => w' t j * a t j) * θ.toC.2.1 k
        - c • ((Matrix.of fun t j => w' t j * b t j) * θ.toC.2.1 k) := by
    rw [← Matrix.smul_mul, ← Matrix.sub_mul]
    congr 1
    ext t j
    simp only [Matrix.of_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  have e0 : (Matrix.of fun t j => w' t j * (0 : Matrix T (hid k) ℂ) t j) * θ.toC.2.1 k = 0 := by
    simp only [Matrix.zero_apply, mul_zero, of_zero_gzp, Matrix.zero_mul]
  rw [e1, e0, map_sub, map_smul, map_zero]
  module

omit [Fintype T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Step 7: `𝓛` is affine in `w'`: `𝓛(w, 1 − y; ż) = 𝓛(w, 1; ż) − 𝐃𝓑(wV)((y ⊙ ż)V)`. -/
private theorem blockLHSC_wpM_gzp
    (θ : Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm 0) hid) dIn dOut) (k : Fin L)
    (η : Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm 0) hid) dIn dOut)
    (w z : Matrix T (hid k) ℂ) (y : hid k → ℂ) :
    blockLHSC geluC θ k η w (wpM_gzp T y) z
      = blockLHSC geluC θ k η w (wpM_gzp T 0) z
        - fderiv ℂ (fun h' : Matrix T d ℂ => suffixC geluC θ.toC k.succ h') (w * θ.toC.2.1 k)
          ((Matrix.of fun t j => y j * z t j) * θ.toC.2.1 k) := by
  rw [blockLHSC_split_gzp θ k η w (wpM_gzp T y) z, blockLHSC_split_gzp θ k η w (wpM_gzp T 0) z]
  have e : (Matrix.of fun t j => wpM_gzp T y t j * z t j) * θ.toC.2.1 k
      = (Matrix.of fun t j => wpM_gzp T 0 t j * z t j) * θ.toC.2.1 k
        - (Matrix.of fun t j => y j * z t j) * θ.toC.2.1 k := by
    rw [← Matrix.sub_mul]
    congr 1
    ext t j
    simp only [wpM_gzp, Matrix.of_apply, Matrix.sub_apply, Pi.zero_apply]
    ring
  rw [e, map_sub]
  abel

/-! ### The map `Ψ` -/

/-- The map `Ψ(s, (x, y)) = s² 𝓛(w, w'; a) − (q/4)(𝓛(w, w'; b) − 𝓛(w, w'; 0))` with
`w = m(s)W − x`, `w' = 1 − y`, `a = m(s)(ZW + η_W)`, `b = m(s)W` and `q = ⟨m(s)Z, m(s)⟩`. -/
private noncomputable def psi_gzp
    (θ : Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm 0) hid) dIn dOut) (k : Fin L)
    (η : Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm 0) hid) dIn dOut) (Z : Matrix d d ℝ)
    (ξ ξ' : d → ℝ) (p : ℂ × ((hid k → ℂ) × (hid k → ℂ))) : Matrix T dOut ℂ :=
  p.1 ^ 2 • blockLHSC geluC θ k η (wM_gzp T (θ.toC.1 k) ξ ξ' p.1 p.2.1) (wpM_gzp T p.2.2)
      (rowM_gzp T (mrow_gzp ξ ξ' p.1
        ᵥ* (Z.map (fun x : ℝ => (x : ℂ)) * θ.toC.1 k + η.toC.1 k)))
    - ((mrow_gzp ξ ξ' p.1 ᵥ* Z.map (fun x : ℝ => (x : ℂ))) ⬝ᵥ mrow_gzp ξ ξ' p.1 / 4)
      • (blockLHSC geluC θ k η (wM_gzp T (θ.toC.1 k) ξ ξ' p.1 p.2.1) (wpM_gzp T p.2.2)
          (rowM_gzp T (mrow_gzp ξ ξ' p.1 ᵥ* θ.toC.1 k))
        - blockLHSC geluC θ k η (wM_gzp T (θ.toC.1 k) ξ ξ' p.1 p.2.1) (wpM_gzp T p.2.2) 0)

/-- **Step 3, the identity:** for real `t > 0`, `s = 1/t`, `λ = √d t/2` and `(x, y)` such that the
rows of `(m(s)W − x)V` lie in `C_κ`: `t² Ψ(s, (x, y)) = 𝓛(λ(m(s)W − x), 1 − y; ż(n(t)))`. -/
private theorem psi_identity_gzp
    (θ : Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm 0) hid) dIn dOut) (k : Fin L)
    {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hhol : HolomorphicOnCone geluC θ k.succ κ)
    (Z : Matrix d d ℝ) (η : Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm 0) hid) dIn dOut)
    (ξ ξ' : d → ℝ) (hd : 0 < Fintype.card d) {t : ℝ} (ht : 0 < t) (x y : hid k → ℂ)
    (hcone : ∀ τ, (wM_gzp T (θ.toC.1 k) ξ ξ' ((t⁻¹ : ℝ) : ℂ) x * θ.toC.2.1 k) τ
      ∈ complexCone κ) :
    ((t : ℂ) ^ 2) • psi_gzp θ k η Z ξ ξ' (((t⁻¹ : ℝ) : ℂ), (x, y))
      = blockLHSC geluC θ k η (((Real.sqrt (Fintype.card d) * t / 2 : ℝ) : ℂ)
          • wM_gzp T (θ.toC.1 k) ξ ξ' ((t⁻¹ : ℝ) : ℂ) x) (wpM_gzp T y)
        (zdotC θ k Z η
          (pathMatrix (Matrix.of fun _ : T => ξ) (Matrix.of fun _ : T => ξ') (t : ℂ))) := by
  have hsd : 0 < Real.sqrt (Fintype.card d) := Real.sqrt_pos.2 (by exact_mod_cast hd)
  have hlam : 0 < Real.sqrt (Fintype.card d) * t / 2 := by positivity
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ht.ne'
  have hd' : (Fintype.card d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  -- `λ² / d = t²/4`
  have hc : ((Real.sqrt (Fintype.card d) * t / 2 : ℝ) : ℂ) ^ 2 / (Fintype.card d : ℂ)
      = (t : ℂ) ^ 2 / 4 := by
    have h2 : ((Real.sqrt (Fintype.card d) : ℝ) : ℂ) ^ 2 = (Fintype.card d : ℂ) := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]; push_cast; rfl
    push_cast
    rw [div_pow, mul_pow, h2]
    field_simp
    norm_num
  rw [pathMatrix_eq_gzp ξ ξ' ht, zdotC_rowM_gzp]
  set m := mrow_gzp ξ ξ' ((t⁻¹ : ℝ) : ℂ) with hm
  have hrow : rowM_gzp T (m ᵥ* (Z.map (fun x : ℝ => (x : ℂ)) * θ.toC.1 k + η.toC.1 k)
        - (((Real.sqrt (Fintype.card d) * t / 2 : ℝ) : ℂ) ^ 2
          * ((m ᵥ* Z.map (fun x : ℝ => (x : ℂ))) ⬝ᵥ m) / (Fintype.card d : ℂ))
          • (m ᵥ* θ.toC.1 k))
      = rowM_gzp T (m ᵥ* (Z.map (fun x : ℝ => (x : ℂ)) * θ.toC.1 k + η.toC.1 k))
        - ((t : ℂ) ^ 2 * ((m ᵥ* Z.map (fun x : ℝ => (x : ℂ))) ⬝ᵥ m / 4))
          • rowM_gzp T (m ᵥ* θ.toC.1 k) := by
    ext τ i
    simp only [rowM_apply_gzp, Matrix.sub_apply, Matrix.smul_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul]
    rw [mul_comm (((Real.sqrt (Fintype.card d) * t / 2 : ℝ) : ℂ) ^ 2), mul_div_assoc, hc]
    ring
  rw [hrow, blockLHSC_smul θ k hκ hκ1 hhol η _ _ _ hcone hlam, blockLHSC_sub_smul_gzp]
  have hts : (t : ℂ) ^ 2 * ((t⁻¹ : ℝ) : ℂ) ^ 2 = 1 := by
    push_cast
    field_simp
  simp only [psi_gzp, smul_sub, smul_smul, hts, one_smul]
  rfl

/-- **Lemma D.19, Step 1, on the path:** `𝓛(n(t)W, 1; n(t)) = 0` for all `t ≥ 1` ("`𝓛_0(t) = 0`
for large `t`, and then for all `t ≥ 1`"). -/
theorem gelu_path_step_zero [Nonempty T]
    (θ : Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm 0) hid) dIn dOut)
    (hθ : RegularZero (Arch.mlp gelu (rmsNorm 0) hid) θ) (k : Fin L)
    {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hhol : HolomorphicOnCone geluC θ k.succ κ)
    (Z : Matrix d d ℝ) (η : Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm 0) hid) dIn dOut)
    (h16 : SuffixFlatZero (Arch.mlp gelu (rmsNorm 0) hid) θ k.castSucc Z η)
    (ξ ξ' : d → ℝ) (hξ : ξ ⬝ᵥ ξ = 1) (hξ' : ξ' ⬝ᵥ ξ' = 1) (hξξ' : ξ ⬝ᵥ ξ' = 0)
    (hP2 : PathP2 (θ.read k) (θ.write k) κ ξ ξ') :
    ∀ t : ℝ, 1 ≤ t →
      blockLHSC geluC θ k η
        (pathMatrix (Matrix.of fun _ : T => ξ) (Matrix.of fun _ : T => ξ') (t : ℂ) * θ.toC.1 k)
        (fun _ _ => 1)
        (zdotC θ k Z η
          (pathMatrix (Matrix.of fun _ : T => ξ) (Matrix.of fun _ : T => ξ') (t : ℂ))) = 0 := by
  sorry

/-- **Lemma D.19, Step 1, at `t = 1`:** "At `t = 1`, where `n(t)` is the row `n = √d ξ`, this reads
`0 = 𝓛(nW, 1; n)`", with the real `𝓛` and `ż(n)` of (20). -/
theorem gelu_path_step_zero_real [Nonempty T]
    (θ : Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm 0) hid) dIn dOut)
    (hθ : RegularZero (Arch.mlp gelu (rmsNorm 0) hid) θ) (k : Fin L)
    {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hhol : HolomorphicOnCone geluC θ k.succ κ)
    (Z : Matrix d d ℝ) (η : Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm 0) hid) dIn dOut)
    (h16 : SuffixFlatZero (Arch.mlp gelu (rmsNorm 0) hid) θ k.castSucc Z η)
    (ξ ξ' : d → ℝ) (hξ : ξ ⬝ᵥ ξ = 1) (hξ' : ξ' ⬝ᵥ ξ' = 1) (hξξ' : ξ ⬝ᵥ ξ' = 0)
    (hP2 : PathP2 (θ.read k) (θ.write k) κ ξ ξ') :
    blockLHS θ k η
      ((Matrix.of fun _ : T => Real.sqrt (Fintype.card d) • ξ) * θ.read k) (fun _ _ => 1)
      (tangentRMS Z (Matrix.of fun _ : T => Real.sqrt (Fintype.card d) • ξ) * θ.read k
        + (Matrix.of fun _ : T => Real.sqrt (Fintype.card d) • ξ) * η.read k) = 0 := by
  sorry

/-- **Lemma D.19, Steps 2 and 4, (50) at `t = 1`:** let `𝓛(z(t) − δ, 1 − δ'; n(t)) = 0` for all
`t ≥ 1` and all complex rows `δ, δ'` whose entries outside the set `A` of hidden units vanish, and
let the unit `j ∉ A` have a smaller rate `r_j = (ξc_j)² − (ξ'c_j)²` than every other unit outside
`A`. Then, at `n = √d ξ`: the derivative at `τ = 0` of `τ ↦ 𝓛(nW − τ e_j, 1; n)` vanishes
(`𝓛_j(1) = 0`), and `𝐃𝓑(n W V)(ż_j(n) a_j) = 0` (`𝓛'_j(1) = 0`). -/
theorem gelu_path_step_unit [Nonempty T]
    (θ : Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm 0) hid) dIn dOut)
    (hθ : RegularZero (Arch.mlp gelu (rmsNorm 0) hid) θ) (k : Fin L) [DecidableEq (hid k)]
    {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hhol : HolomorphicOnCone geluC θ k.succ κ)
    (Z : Matrix d d ℝ) (η : Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm 0) hid) dIn dOut)
    (h16 : SuffixFlatZero (Arch.mlp gelu (rmsNorm 0) hid) θ k.castSucc Z η)
    (ξ ξ' : d → ℝ) (hξ : ξ ⬝ᵥ ξ = 1) (hξ' : ξ' ⬝ᵥ ξ' = 1) (hξξ' : ξ ⬝ᵥ ξ' = 0)
    (hP2 : PathP2 (θ.read k) (θ.write k) κ ξ ξ')
    (A : Set (hid k)) (j : hid k) (hjA : j ∉ A)
    (hrate : ∀ i : hid k, i ∉ A → i ≠ j →
      ((ξ ᵥ* θ.read k) j) ^ 2 - ((ξ' ᵥ* θ.read k) j) ^ 2
        < ((ξ ᵥ* θ.read k) i) ^ 2 - ((ξ' ᵥ* θ.read k) i) ^ 2)
    (hA : ∀ t : ℝ, 1 ≤ t → ∀ δ δ' : hid k → ℂ, (∀ i, i ∉ A → δ i = 0 ∧ δ' i = 0) →
      blockLHSC geluC θ k η
        (Matrix.of fun τ i =>
          (pathMatrix (Matrix.of fun _ : T => ξ) (Matrix.of fun _ : T => ξ') (t : ℂ)
            * θ.toC.1 k) τ i - δ i)
        (Matrix.of fun _ i => 1 - δ' i)
        (zdotC θ k Z η
          (pathMatrix (Matrix.of fun _ : T => ξ) (Matrix.of fun _ : T => ξ') (t : ℂ))) = 0) :
    deriv (fun τ : ℝ =>
        blockLHS θ k η
          ((Matrix.of fun _ : T => Real.sqrt (Fintype.card d) • ξ) * θ.read k
            - τ • Matrix.of fun _ : T => (Pi.single j 1 : hid k → ℝ))
          (fun _ _ => 1)
          (tangentRMS Z (Matrix.of fun _ : T => Real.sqrt (Fintype.card d) • ξ) * θ.read k
            + (Matrix.of fun _ : T => Real.sqrt (Fintype.card d) • ξ) * η.read k)) 0 = 0 ∧
      fderiv ℝ (fun h' : Matrix T d ℝ => suffix (Arch.mlp gelu (rmsNorm 0) hid) 0 θ k.succ h')
        ((Matrix.of fun _ : T => Real.sqrt (Fintype.card d) • ξ) * θ.read k * θ.write k)
        (Matrix.of fun t =>
          (tangentRMS Z (Matrix.of fun _ : T => Real.sqrt (Fintype.card d) • ξ) * θ.read k
            + (Matrix.of fun _ : T => Real.sqrt (Fintype.card d) • ξ) * η.read k) t j
            • θ.write k j) = 0 := by
  sorry

end Skips
