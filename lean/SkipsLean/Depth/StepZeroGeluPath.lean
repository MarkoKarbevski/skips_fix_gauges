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

/-! ### `Ψ` is holomorphic near `[0, 1] × {‖x‖ ≤ r}`, and (47) -/

omit [Fintype d] [DecidableEq d] in
/-- Helper: `s ↦ m(s)_l` is a polynomial. -/
private theorem analyticAt_mrow_gzp (ξ ξ' : d → ℝ) (l : d) (s₀ : ℂ) :
    AnalyticAt ℂ (fun s => mrow_gzp ξ ξ' s l) s₀ := by
  unfold mrow_gzp
  fun_prop

omit [DecidableEq d] in
/-- Helper: `s ↦ (m(s) M)_i` is a polynomial. -/
private theorem analyticAt_mrow_vecMul_gzp {ι : Type*} (ξ ξ' : d → ℝ) (M : Matrix d ι ℂ) (i : ι)
    (s₀ : ℂ) : AnalyticAt ℂ (fun s => (mrow_gzp ξ ξ' s ᵥ* M) i) s₀ := by
  show AnalyticAt ℂ (fun s => ∑ l, mrow_gzp ξ ξ' s l * M l i) s₀
  exact Finset.analyticAt_fun_sum _ fun l _ =>
    (analyticAt_mrow_gzp ξ ξ' l s₀).mul analyticAt_const

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: a matrix with the same analytic row at every token is analytic. -/
private theorem analyticAt_of_gzp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (T' : Type*) [Fintype T'] {ι : Type*} [Fintype ι] {f : E → ι → ℂ} {x : E}
    (hf : ∀ i, AnalyticAt ℂ (fun y => f y i) x) :
    AnalyticAt ℂ (fun y => (Matrix.of fun (_ : T') i => f y i : Matrix T' ι ℂ)) x := by
  show AnalyticAt ℂ (fun y => fun (_ : T') => fun i => f y i) x
  exact AnalyticAt.pi fun _ => AnalyticAt.pi fun i => hf i

/-- Helper: `y ↦ 𝓛(f₁(y), f₂(y); f₃(y))` is analytic where the rows of `f₁(y) V` are in the cone
(`analyticAt_blockLHSC`). -/
private theorem analyticAt_blockLHSC_comp_gzp
    (θ : Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm 0) hid) dIn dOut) (k : Fin L)
    {κ : ℝ} (hhol : HolomorphicOnCone geluC θ k.succ κ)
    (η : Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm 0) hid) dIn dOut)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f₁ f₂ f₃ : E → Matrix T (hid k) ℂ}
    {x : E} (h₁ : AnalyticAt ℂ f₁ x) (h₂ : AnalyticAt ℂ f₂ x) (h₃ : AnalyticAt ℂ f₃ x)
    (hcone : ∀ τ, (f₁ x * θ.toC.2.1 k) τ ∈ complexCone κ) :
    AnalyticAt ℂ (fun y => blockLHSC geluC θ k η (f₁ y) (f₂ y) (f₃ y)) x := by
  have hG := analyticAt_blockLHSC θ k hhol η (f₁ x) (f₂ x) (f₃ x) hcone
  have hP : AnalyticAt ℂ (fun y => (f₁ y, f₂ y, f₃ y)) x := h₁.prod (h₂.prod h₃)
  exact AnalyticAt.comp (f := fun y => (f₁ y, f₂ y, f₃ y)) hG hP

/-- **Step 3, `Ψ` is holomorphic** at every point `(s, (x, y))` where the rows of `(m(s)W − x)V`
lie in the cone. -/
private theorem analyticAt_psi_gzp
    (θ : Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm 0) hid) dIn dOut) (k : Fin L)
    {κ : ℝ} (hhol : HolomorphicOnCone geluC θ k.succ κ)
    (η : Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm 0) hid) dIn dOut) (Z : Matrix d d ℝ)
    (ξ ξ' : d → ℝ) (p₀ : ℂ × ((hid k → ℂ) × (hid k → ℂ)))
    (hcone : ∀ τ, (wM_gzp T (θ.toC.1 k) ξ ξ' p₀.1 p₀.2.1 * θ.toC.2.1 k) τ ∈ complexCone κ) :
    AnalyticAt ℂ (psi_gzp θ k η Z ξ ξ') p₀ := by
  -- the coordinates `s`, `x_i`, `y_i`
  have hs : AnalyticAt ℂ (fun p : ℂ × ((hid k → ℂ) × (hid k → ℂ)) => p.1) p₀ := analyticAt_fst
  have hx : ∀ i, AnalyticAt ℂ (fun p : ℂ × ((hid k → ℂ) × (hid k → ℂ)) => p.2.1 i) p₀ :=
    fun i => ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : hid k => ℂ) i).comp
      ((ContinuousLinearMap.fst ℂ _ _).comp (ContinuousLinearMap.snd ℂ _ _))).analyticAt p₀
  have hy : ∀ i, AnalyticAt ℂ (fun p : ℂ × ((hid k → ℂ) × (hid k → ℂ)) => p.2.2 i) p₀ :=
    fun i => ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : hid k => ℂ) i).comp
      ((ContinuousLinearMap.snd ℂ _ _).comp (ContinuousLinearMap.snd ℂ _ _))).analyticAt p₀
  have hm : ∀ (M : Matrix d (hid k) ℂ) i, AnalyticAt ℂ
      (fun p : ℂ × ((hid k → ℂ) × (hid k → ℂ)) => (mrow_gzp ξ ξ' p.1 ᵥ* M) i) p₀ :=
    fun M i => (analyticAt_mrow_vecMul_gzp ξ ξ' M i p₀.1).comp hs
  -- the matrices `w`, `w'`, `a`, `b` and the number `q/4`
  have hw : AnalyticAt ℂ (fun p : ℂ × ((hid k → ℂ) × (hid k → ℂ)) =>
      wM_gzp T (θ.toC.1 k) ξ ξ' p.1 p.2.1) p₀ :=
    analyticAt_of_gzp T fun i => (hm _ i).sub (hx i)
  have hwp : AnalyticAt ℂ (fun p : ℂ × ((hid k → ℂ) × (hid k → ℂ)) => wpM_gzp T p.2.2) p₀ :=
    analyticAt_of_gzp T fun i => analyticAt_const.sub (hy i)
  have ha : AnalyticAt ℂ (fun p : ℂ × ((hid k → ℂ) × (hid k → ℂ)) => rowM_gzp T
      (mrow_gzp ξ ξ' p.1 ᵥ* (Z.map (fun x : ℝ => (x : ℂ)) * θ.toC.1 k + η.toC.1 k))) p₀ :=
    analyticAt_of_gzp T fun i => hm _ i
  have hb : AnalyticAt ℂ (fun p : ℂ × ((hid k → ℂ) × (hid k → ℂ)) =>
      rowM_gzp T (mrow_gzp ξ ξ' p.1 ᵥ* θ.toC.1 k)) p₀ :=
    analyticAt_of_gzp T fun i => hm _ i
  have hq : AnalyticAt ℂ (fun p : ℂ × ((hid k → ℂ) × (hid k → ℂ)) =>
      (mrow_gzp ξ ξ' p.1 ᵥ* Z.map (fun x : ℝ => (x : ℂ))) ⬝ᵥ mrow_gzp ξ ξ' p.1 / 4) p₀ := by
    refine AnalyticAt.div_const ?_
    show AnalyticAt ℂ (fun p : ℂ × ((hid k → ℂ) × (hid k → ℂ)) =>
      ∑ i, (mrow_gzp ξ ξ' p.1 ᵥ* Z.map (fun x : ℝ => (x : ℂ))) i * mrow_gzp ξ ξ' p.1 i) p₀
    exact Finset.analyticAt_fun_sum _ fun i _ =>
      ((analyticAt_mrow_vecMul_gzp ξ ξ' _ i p₀.1).comp hs).mul
        ((analyticAt_mrow_gzp ξ ξ' i p₀.1).comp hs)
  -- the three values of `𝓛`
  have hA := analyticAt_blockLHSC_comp_gzp θ k hhol η hw hwp ha hcone
  have hB := analyticAt_blockLHSC_comp_gzp θ k hhol η hw hwp hb hcone
  have hC := analyticAt_blockLHSC_comp_gzp θ k hhol η hw hwp
    (analyticAt_const (v := (0 : Matrix T (hid k) ℂ))) hcone
  exact ((hs.pow 2).fun_smul hA).fun_sub (hq.fun_smul (hB.fun_sub hC))

omit [DecidableEq d] in
/-- Step 2: `‖ξWV‖ > 0`, from the second inequality of (P2). -/
private theorem sqrt_u_pos_gzp {ι : Type*} [Fintype ι] (W : Matrix d ι ℝ) (V : Matrix ι d ℝ)
    {κ : ℝ} (hκ : 0 < κ) (ξ ξ' : d → ℝ)
    (h2 : Real.sqrt ((ξ' ᵥ* (W * V)) ⬝ᵥ (ξ' ᵥ* (W * V)))
      < κ / 2 * Real.sqrt ((ξ ᵥ* (W * V)) ⬝ᵥ (ξ ᵥ* (W * V)))) :
    0 < Real.sqrt ((ξ ᵥ* (W * V)) ⬝ᵥ (ξ ᵥ* (W * V))) := by
  have := Real.sqrt_nonneg ((ξ' ᵥ* (W * V)) ⬝ᵥ (ξ' ᵥ* (W * V)))
  by_contra h
  push Not at h
  nlinarith

/-- The radius `r = κ ‖ξWV‖ / (8 (1 + ∑_j ‖a_j‖))` of the polydisc. -/
private noncomputable def rad_gzp {ι : Type*} [Fintype ι] (W : Matrix d ι ℝ) (V : Matrix ι d ℝ)
    (ξ : d → ℝ) (κ : ℝ) : ℝ :=
  κ * Real.sqrt ((ξ ᵥ* (W * V)) ⬝ᵥ (ξ ᵥ* (W * V))) / (8 * (1 + ∑ j, Real.sqrt (V j ⬝ᵥ V j)))

omit [DecidableEq d] in
/-- Step 2: `r > 0`. -/
private theorem rad_pos_gzp {ι : Type*} [Fintype ι] (W : Matrix d ι ℝ) (V : Matrix ι d ℝ)
    {κ : ℝ} (hκ : 0 < κ) (ξ ξ' : d → ℝ)
    (h2 : Real.sqrt ((ξ' ᵥ* (W * V)) ⬝ᵥ (ξ' ᵥ* (W * V)))
      < κ / 2 * Real.sqrt ((ξ ᵥ* (W * V)) ⬝ᵥ (ξ ᵥ* (W * V)))) :
    0 < rad_gzp W V ξ κ := by
  have hU := sqrt_u_pos_gzp W V hκ ξ ξ' h2
  have hS : 0 ≤ ∑ j, Real.sqrt (V j ⬝ᵥ V j) := Finset.sum_nonneg fun j _ => Real.sqrt_nonneg _
  unfold rad_gzp
  positivity

omit [Fintype T] [DecidableEq d] in
/-- **Step 2, the polydisc:** for real `s ∈ [0, 1]` and `‖(x, y)‖ ≤ r`, the rows of `(m(s)W − x)V`
lie in `C_κ`. -/
private theorem cone_poly_gzp {ι : Type*} [Fintype ι] (W : Matrix d ι ℝ) (V : Matrix ι d ℝ)
    {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) (ξ ξ' : d → ℝ)
    (h2 : Real.sqrt ((ξ' ᵥ* (W * V)) ⬝ᵥ (ξ' ᵥ* (W * V)))
      < κ / 2 * Real.sqrt ((ξ ᵥ* (W * V)) ⬝ᵥ (ξ ᵥ* (W * V))))
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (x : (ι → ℂ) × (ι → ℂ)) (hx : ‖x‖ ≤ rad_gzp W V ξ κ)
    (τ : T) :
    (wM_gzp T (W.map (fun x : ℝ => (x : ℂ))) ξ ξ' (s : ℂ) x.1 * V.map (fun x : ℝ => (x : ℂ))) τ
      ∈ complexCone κ := by
  refine cone_gzp W V hκ hκ1 ξ ξ' h2 hs0 hs1 x.1 ?_
  have hU := sqrt_u_pos_gzp W V hκ ξ ξ' h2
  have hr0 := (rad_pos_gzp W V hκ ξ ξ' h2).le
  have hS : 0 ≤ ∑ j, Real.sqrt (V j ⬝ᵥ V j) := Finset.sum_nonneg fun j _ => Real.sqrt_nonneg _
  have hxj : ∀ j, ‖x.1 j‖ ≤ rad_gzp W V ξ κ := fun j =>
    (norm_le_pi_norm x.1 j).trans ((norm_fst_le x).trans hx)
  have hrS : rad_gzp W V ξ κ * (1 + ∑ j, Real.sqrt (V j ⬝ᵥ V j))
      = κ * Real.sqrt ((ξ ᵥ* (W * V)) ⬝ᵥ (ξ ᵥ* (W * V))) / 8 := by
    unfold rad_gzp
    field_simp
  calc ∑ j, ‖x.1 j‖ * Real.sqrt (V j ⬝ᵥ V j)
      ≤ ∑ j, rad_gzp W V ξ κ * Real.sqrt (V j ⬝ᵥ V j) :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hxj j) (Real.sqrt_nonneg _)
    _ = rad_gzp W V ξ κ * ∑ j, Real.sqrt (V j ⬝ᵥ V j) := (Finset.mul_sum _ _ _).symm
    _ ≤ rad_gzp W V ξ κ * (1 + ∑ j, Real.sqrt (V j ⬝ᵥ V j)) :=
        mul_le_mul_of_nonneg_left (by linarith) hr0
    _ = κ * Real.sqrt ((ξ ᵥ* (W * V)) ⬝ᵥ (ξ ᵥ* (W * V))) / 8 := hrS
    _ ≤ κ / 4 * (s + 1 / 2) * Real.sqrt ((ξ ᵥ* (W * V)) ⬝ᵥ (ξ ᵥ* (W * V))) := by
        nlinarith [mul_nonneg (mul_nonneg hκ.le hs0) hU.le]

omit [DecidableEq d] in
/-- Step 1: `|Im ω_j| < Re ω_j`, from the first inequality of (P2). -/
private theorem omega_im_lt_gzp {ι : Type*} (W : Matrix d ι ℝ) (ξ ξ' : d → ℝ)
    (h1 : ∀ j, |(ξ' ᵥ* W) j| < (ξ ᵥ* W) j) (hd : 0 < Fintype.card d) (j : ι) :
    |(omega_gzp W ξ ξ' j).im| < (omega_gzp W ξ ξ' j).re := by
  have hsd : 0 < Real.sqrt (Fintype.card d) / 2 :=
    div_pos (Real.sqrt_pos.2 (by exact_mod_cast hd)) two_pos
  show |Real.sqrt (Fintype.card d) / 2 * (ξ' ᵥ* W) j| < Real.sqrt (Fintype.card d) / 2 * (ξ ᵥ* W) j
  rw [abs_mul, abs_of_pos hsd]
  exact mul_lt_mul_of_pos_left (h1 j) hsd

omit [Fintype T] [DecidableEq d] in
/-- **Step 2, the path:** for `t ≥ 1`, the rows of `(m(1/t)W − c₀δ(t)/t)V` lie in `C_κ`
(`c₀ = 2/√d`; by (45) and the third inequality of (P2)). -/
private theorem cone_path_gzp {ι : Type*} [Fintype ι] (W : Matrix d ι ℝ) (V : Matrix ι d ℝ)
    {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) (ξ ξ' : d → ℝ) (hP2 : PathP2 W V κ ξ ξ')
    (hd : 0 < Fintype.card d) {t : ℝ} (ht : 1 ≤ t) (τ : T) :
    (wM_gzp T (W.map (fun x : ℝ => (x : ℂ))) ξ ξ' ((t⁻¹ : ℝ) : ℂ)
        (geluGap (2 / Real.sqrt (Fintype.card d)) (omega_gzp W ξ ξ') t).1
      * V.map (fun x : ℝ => (x : ℂ))) τ ∈ complexCone κ := by
  obtain ⟨h1, h2, h3⟩ := hP2
  have ht0 : 0 < t := by linarith
  have hsd : 0 < Real.sqrt (Fintype.card d) := Real.sqrt_pos.2 (by exact_mod_cast hd)
  refine cone_gzp W V hκ hκ1 ξ ξ' h2 (inv_nonneg.2 ht0.le) (inv_le_one_of_one_le₀ ht) _ ?_
  -- `‖c₀ δ_j(t)/t‖ ≤ (c₀/t) e^{−d (ξc_j)²/2}`
  have hxj : ∀ j, ‖(geluGap (2 / Real.sqrt (Fintype.card d)) (omega_gzp W ξ ξ') t).1 j‖
      * Real.sqrt (V j ⬝ᵥ V j)
      ≤ 2 / Real.sqrt (Fintype.card d) / t
        * (Real.exp (-((Fintype.card d : ℝ) * ((ξ ᵥ* W) j) ^ 2 / 2)) * Real.sqrt (V j ⬝ᵥ V j)) := by
    intro j
    have hω := omega_im_lt_gzp W ξ ξ' h1 hd j
    have h := norm_sub_geluC_unitPath_le hω ht
    have hrate : 0 ≤ (omega_gzp W ξ ξ' j).re ^ 2 - (omega_gzp W ξ ξ' j).im ^ 2 := by
      obtain ⟨ha, hb⟩ := abs_lt.1 hω
      nlinarith
    have he1 : Real.exp (-(((omega_gzp W ξ ξ' j).re ^ 2 - (omega_gzp W ξ ξ' j).im ^ 2)
        * (t - 1 / t) ^ 2 / 2)) ≤ 1 :=
      Real.exp_le_one_iff.2 (by have := sq_nonneg (t - 1 / t); nlinarith)
    have hre : Real.exp (-(2 * (omega_gzp W ξ ξ' j).re ^ 2))
        = Real.exp (-((Fintype.card d : ℝ) * ((ξ ᵥ* W) j) ^ 2 / 2)) := by
      congr 1
      show -(2 * (Real.sqrt (Fintype.card d) / 2 * (ξ ᵥ* W) j) ^ 2) = _
      rw [mul_pow, div_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
      ring
    have hgap : (geluGap (2 / Real.sqrt (Fintype.card d)) (omega_gzp W ξ ξ') t).1 j
        = ((2 / Real.sqrt (Fintype.card d) / t : ℝ) : ℂ)
          * (unitPath (omega_gzp W ξ ξ' j) t - geluC (unitPath (omega_gzp W ξ ξ' j) t)) := rfl
    rw [hgap, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity), mul_assoc]
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _))
      (by positivity)
    rw [← hre]
    calc _ ≤ _ := h
      _ ≤ Real.exp (-(2 * (omega_gzp W ξ ξ' j).re ^ 2)) * 1 :=
          mul_le_mul_of_nonneg_left he1 (Real.exp_pos _).le
      _ = _ := mul_one _
  have hU := sqrt_u_pos_gzp W V hκ ξ ξ' h2
  calc _ ≤ ∑ j, 2 / Real.sqrt (Fintype.card d) / t
        * (Real.exp (-((Fintype.card d : ℝ) * ((ξ ᵥ* W) j) ^ 2 / 2))
          * Real.sqrt (V j ⬝ᵥ V j)) := Finset.sum_le_sum fun j _ => hxj j
    _ = 2 / Real.sqrt (Fintype.card d) / t
        * ∑ j, Real.exp (-((Fintype.card d : ℝ) * ((ξ ᵥ* W) j) ^ 2 / 2))
          * Real.sqrt (V j ⬝ᵥ V j) := (Finset.mul_sum _ _ _).symm
    _ ≤ 2 / Real.sqrt (Fintype.card d) / t
        * (κ * Real.sqrt (Fintype.card d) / 8 * Real.sqrt ((ξ ᵥ* (W * V)) ⬝ᵥ (ξ ᵥ* (W * V)))) :=
        mul_le_mul_of_nonneg_left h3.le (by positivity)
    _ = κ / 4 * t⁻¹ * Real.sqrt ((ξ ᵥ* (W * V)) ⬝ᵥ (ξ ᵥ* (W * V))) := by
        field_simp
        ring
    _ ≤ κ / 4 * (t⁻¹ + 1 / 2) * Real.sqrt ((ξ ᵥ* (W * V)) ⬝ᵥ (ξ ᵥ* (W * V))) := by
        nlinarith [mul_pos hκ hU]

omit [Fintype T] [DecidableEq d] in
/-- Step 4: on the path, `σ(n(t)W) = λ (m(1/t)W − c₀δ(t)/t)` (as `λ c₀/t = 1`) and
`σ'(n(t)W) = 1 − δ'(t)`. -/
private theorem path_gelu_gzp {ι : Type*} (W : Matrix d ι ℝ) (ξ ξ' : d → ℝ) {t : ℝ} (ht : 0 < t)
    (hd : 0 < Fintype.card d) :
    (pathMatrix (Matrix.of fun _ : T => ξ) (Matrix.of fun _ : T => ξ') (t : ℂ)
        * W.map (fun x : ℝ => (x : ℂ))).map geluC
      = ((Real.sqrt (Fintype.card d) * t / 2 : ℝ) : ℂ)
        • wM_gzp T (W.map (fun x : ℝ => (x : ℂ))) ξ ξ' ((t⁻¹ : ℝ) : ℂ)
          (geluGap (2 / Real.sqrt (Fintype.card d)) (omega_gzp W ξ ξ') t).1 ∧
    (pathMatrix (Matrix.of fun _ : T => ξ) (Matrix.of fun _ : T => ξ') (t : ℂ)
        * W.map (fun x : ℝ => (x : ℂ))).map (deriv geluC)
      = wpM_gzp T (geluGap (2 / Real.sqrt (Fintype.card d)) (omega_gzp W ξ ξ') t).2 := by
  have hsd : 0 < Real.sqrt (Fintype.card d) := Real.sqrt_pos.2 (by exact_mod_cast hd)
  have hc : ((Real.sqrt (Fintype.card d) * t / 2 : ℝ) : ℂ)
      * ((2 / Real.sqrt (Fintype.card d) / t : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_one]
    congr 1
    field_simp
  refine ⟨?_, ?_⟩
  · rw [smul_wM_gzp _ ξ ξ' ht]
    ext τ j
    simp only [Matrix.map_apply, Matrix.of_apply, geluGap, path_entry_gzp W ξ ξ' ht τ j]
    linear_combination (unitPath (omega_gzp W ξ ξ' j) t
      - geluC (unitPath (omega_gzp W ξ ξ' j) t)) * hc
  · ext τ j
    simp only [Matrix.map_apply, wpM_gzp, Matrix.of_apply, geluGap, path_entry_gzp W ξ ξ' ht τ j]
    ring

/-- **(47):** for `t ≥ 1`, `Ψ(1/t, (c₀δ(t)/t, δ'(t))) = 0` (Lemma D.15 and the identity). -/
private theorem psi_path_gzp [Nonempty T]
    (θ : Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm 0) hid) dIn dOut)
    (hθ : RegularZero (Arch.mlp gelu (rmsNorm 0) hid) θ) (k : Fin L)
    {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hhol : HolomorphicOnCone geluC θ k.succ κ)
    (Z : Matrix d d ℝ) (η : Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm 0) hid) dIn dOut)
    (h16 : SuffixFlatZero (Arch.mlp gelu (rmsNorm 0) hid) θ k.castSucc Z η)
    (ξ ξ' : d → ℝ) (hξ : ξ ⬝ᵥ ξ = 1) (hξ' : ξ' ⬝ᵥ ξ' = 1) (hξξ' : ξ ⬝ᵥ ξ' = 0)
    (hP2 : PathP2 (θ.read k) (θ.write k) κ ξ ξ') (hd : 0 < Fintype.card d) {t : ℝ}
    (ht : 1 ≤ t) :
    psi_gzp θ k η Z ξ ξ' (((t : ℂ))⁻¹,
      geluGap (2 / Real.sqrt (Fintype.card d)) (omega_gzp (θ.read k) ξ ξ') t) = 0 := by
  have : Nonempty d := Fintype.card_pos_iff.1 hd
  have ht0 : 0 < t := by linarith
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ht0.ne'
  -- the hypothesis of Lemma D.15: `σ` is holomorphic, and the rows of `σ(n(t)W)V` are in `C_κ`
  have hpath : ∀ t' : ℝ, 1 ≤ t' →
      (∀ τ j, AnalyticAt ℂ geluC ((pathMatrix (Matrix.of fun _ : T => ξ)
        (Matrix.of fun _ : T => ξ') (t' : ℂ) * θ.toC.1 k) τ j)) ∧
      ∀ τ, ((pathMatrix (Matrix.of fun _ : T => ξ) (Matrix.of fun _ : T => ξ') (t' : ℂ)
        * θ.toC.1 k).map geluC * θ.toC.2.1 k) τ ∈ complexCone κ := by
    intro t' ht'
    refine ⟨fun _ _ => analyticAt_geluC _, fun τ => ?_⟩
    have e : (pathMatrix (Matrix.of fun _ : T => ξ) (Matrix.of fun _ : T => ξ') (t' : ℂ)
        * θ.toC.1 k).map geluC
        = ((Real.sqrt (Fintype.card d) * t' / 2 : ℝ) : ℂ)
          • wM_gzp T (θ.toC.1 k) ξ ξ' ((t'⁻¹ : ℝ) : ℂ)
            (geluGap (2 / Real.sqrt (Fintype.card d)) (omega_gzp (θ.read k) ξ ξ') t').1 :=
      (path_gelu_gzp (θ.read k) ξ ξ' (by linarith) hd).1
    rw [e, Matrix.smul_mul]
    exact smul_mem_complexCone (cone_path_gzp (θ.read k) (θ.write k) hκ hκ1 ξ ξ' hP2 hd ht' τ)
      _ (by have := Real.sqrt_pos.2 (show (0 : ℝ) < Fintype.card d by exact_mod_cast hd)
            positivity)
  -- (47) in the form of Lemma D.15, then the identity
  have h := blockLHSC_pathMatrix_eq_zero hasDerivAt_gelu analyticOnNhd_gelu geluC_ofReal
    (fun x => analyticAt_geluC _) θ hθ k hκ hhol Z η h16 (Matrix.of fun _ : T => ξ)
    (Matrix.of fun _ : T => ξ') (fun _ => hξ) (fun _ => hξ') (fun _ => hξξ') hpath t ht
  have e1' : (pathMatrix (Matrix.of fun _ : T => ξ) (Matrix.of fun _ : T => ξ') (t : ℂ)
      * θ.toC.1 k).map geluC
      = ((Real.sqrt (Fintype.card d) * t / 2 : ℝ) : ℂ)
        • wM_gzp T (θ.toC.1 k) ξ ξ' ((t⁻¹ : ℝ) : ℂ)
          (geluGap (2 / Real.sqrt (Fintype.card d)) (omega_gzp (θ.read k) ξ ξ') t).1 :=
    (path_gelu_gzp (θ.read k) ξ ξ' ht0 hd).1
  have e2' : (pathMatrix (Matrix.of fun _ : T => ξ) (Matrix.of fun _ : T => ξ') (t : ℂ)
      * θ.toC.1 k).map (deriv geluC)
      = wpM_gzp T (geluGap (2 / Real.sqrt (Fintype.card d)) (omega_gzp (θ.read k) ξ ξ') t).2 :=
    (path_gelu_gzp (θ.read k) ξ ξ' ht0 hd).2
  rw [e1', e2', ← psi_identity_gzp θ k hκ hκ1 hhol Z η ξ ξ' hd ht0 _ _
    (cone_path_gzp (θ.read k) (θ.write k) hκ hκ1 ξ ξ' hP2 hd ht)] at h
  have h3 := (smul_eq_zero.1 h).resolve_left (pow_ne_zero 2 ht')
  rw [Complex.ofReal_inv] at h3
  exact h3

/-- Step 3: `Ψ` is holomorphic at the points `(s, x)` with `s ∈ [0, 1]` and `‖x‖ ≤ r`. -/
private theorem analyticAt_psi_poly_gzp
    (θ : Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm 0) hid) dIn dOut) (k : Fin L)
    {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hhol : HolomorphicOnCone geluC θ k.succ κ)
    (Z : Matrix d d ℝ) (η : Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm 0) hid) dIn dOut)
    (ξ ξ' : d → ℝ) (hP2 : PathP2 (θ.read k) (θ.write k) κ ξ ξ') :
    ∀ s : ℝ, 0 ≤ s → s ≤ 1 → ∀ x : (hid k → ℂ) × (hid k → ℂ),
      ‖x‖ ≤ rad_gzp (θ.read k) (θ.write k) ξ κ →
        AnalyticAt ℂ (psi_gzp θ k η Z ξ ξ') ((s : ℂ), x) :=
  fun _ hs0 hs1 x hx => analyticAt_psi_gzp θ k hhol η Z ξ ξ' _
    (cone_poly_gzp (θ.read k) (θ.write k) hκ hκ1 ξ ξ' hP2.2.1 hs0 hs1 x hx)

/-- **Step 5 (Step 1 of the paper):** `Ψ(s, 0) = 0` for `s ∈ (0, 1]` (`gelu_path_zero`). -/
private theorem psi_zero_gzp [Nonempty T]
    (θ : Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm 0) hid) dIn dOut)
    (hθ : RegularZero (Arch.mlp gelu (rmsNorm 0) hid) θ) (k : Fin L)
    {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hhol : HolomorphicOnCone geluC θ k.succ κ)
    (Z : Matrix d d ℝ) (η : Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm 0) hid) dIn dOut)
    (h16 : SuffixFlatZero (Arch.mlp gelu (rmsNorm 0) hid) θ k.castSucc Z η)
    (ξ ξ' : d → ℝ) (hξ : ξ ⬝ᵥ ξ = 1) (hξ' : ξ' ⬝ᵥ ξ' = 1) (hξξ' : ξ ⬝ᵥ ξ' = 0)
    (hP2 : PathP2 (θ.read k) (θ.write k) κ ξ ξ') (hd : 0 < Fintype.card d) :
    ∀ s : ℝ, 0 < s → s ≤ 1 → psi_gzp θ k η Z ξ ξ' ((s : ℂ), 0) = 0 :=
  gelu_path_zero (omega_gzp (θ.read k) ξ ξ') (omega_im_lt_gzp _ ξ ξ' hP2.1 hd)
    (2 / Real.sqrt (Fintype.card d)) (psi_gzp θ k η Z ξ ξ')
    (rad_pos_gzp (θ.read k) (θ.write k) hκ ξ ξ' hP2.2.1)
    (analyticAt_psi_poly_gzp θ k hκ hκ1 hhol Z η ξ ξ' hP2)
    (Filter.eventually_atTop.2 ⟨1, fun _ ht =>
      psi_path_gzp θ hθ k hκ hκ1 hhol Z η h16 ξ ξ' hξ hξ' hξξ' hP2 hd ht⟩)

/-! ### At `t = 1`: the real objects -/

omit [Fintype T] [DecidableEq d] in
/-- Helper: the cast of a product of real matrices is the product of the casts. -/
private theorem map_mul_gzp {m n p : Type*} [Fintype n] (A : Matrix m n ℝ) (B : Matrix n p ℝ) :
    (A * B).map (fun x : ℝ => (x : ℂ))
      = A.map (fun x : ℝ => (x : ℂ)) * B.map (fun x : ℝ => (x : ℂ)) :=
  Matrix.map_mul (f := Complex.ofRealHom)

omit [Fintype T] [DecidableEq d] in
/-- Helper: `d > 0`, as `ξ ⬝ᵥ ξ = 1`. -/
private theorem card_pos_gzp (ξ : d → ℝ) (hξ : ξ ⬝ᵥ ξ = 1) : 0 < Fintype.card d := by
  by_contra h
  have h0 : Fintype.card d = 0 := by omega
  have : IsEmpty d := Fintype.card_eq_zero_iff.1 h0
  simp [dotProduct] at hξ

omit [Fintype T] [DecidableEq d] in
/-- Step 6: `n(1) = n = √d ξ` at every token. -/
private theorem pathMatrix_one_gzp (ξ ξ' : d → ℝ) :
    pathMatrix (Matrix.of fun _ : T => ξ) (Matrix.of fun _ : T => ξ') ((1 : ℝ) : ℂ)
      = (Matrix.of fun _ : T => Real.sqrt (Fintype.card d) • ξ).map (fun x : ℝ => (x : ℂ)) := by
  ext τ i
  rw [Complex.ofReal_one]
  show pathRow ξ ξ' 1 i = (((Real.sqrt (Fintype.card d) • ξ) i : ℝ) : ℂ)
  rw [pathRow_one]
  rfl

omit [Fintype T] [DecidableEq d] in
/-- Step 6: the rows of `n W V = √d ξWV` do not vanish. -/
private theorem rows_ne_zero_gzp {ι : Type*} [Fintype ι] (W : Matrix d ι ℝ) (V : Matrix ι d ℝ)
    (ξ : d → ℝ) (hU : 0 < Real.sqrt ((ξ ᵥ* (W * V)) ⬝ᵥ (ξ ᵥ* (W * V))))
    (hd : 0 < Fintype.card d) (τ : T) :
    ((Matrix.of fun _ : T => Real.sqrt (Fintype.card d) • ξ) * W * V) τ ≠ 0 := by
  intro h
  have e : ((Matrix.of fun _ : T => Real.sqrt (Fintype.card d) • ξ) * W * V) τ
      = Real.sqrt (Fintype.card d) • (ξ ᵥ* (W * V)) := by
    rw [Matrix.mul_assoc, Matrix.mul_apply_eq_vecMul, ← smul_vecMul]
    rfl
  rw [e] at h
  have hu : ξ ᵥ* (W * V) = 0 :=
    (smul_eq_zero.1 h).resolve_left (Real.sqrt_pos.2 (by exact_mod_cast hd)).ne'
  rw [hu] at hU
  simp at hU

omit [Fintype T] [DecidableEq d] in
/-- Step 6: the rows of `n W V` (cast to `ℂ`) are in the cone. -/
private theorem rows_mem_cone_gzp {ι : Type*} [Fintype ι] (W : Matrix d ι ℝ) (V : Matrix ι d ℝ)
    (ξ : d → ℝ) {κ : ℝ} (hκ : 0 < κ) (hU : 0 < Real.sqrt ((ξ ᵥ* (W * V)) ⬝ᵥ (ξ ᵥ* (W * V))))
    (hd : 0 < Fintype.card d) (τ : T) :
    (((Matrix.of fun _ : T => Real.sqrt (Fintype.card d) • ξ) * W).map (fun x : ℝ => (x : ℂ))
      * V.map (fun x : ℝ => (x : ℂ))) τ ∈ complexCone κ := by
  rw [← map_mul_gzp]
  exact ofReal_mem_complexCone hκ _ (rows_ne_zero_gzp W V ξ hU hd τ)

/-- **Step 6, the identity at `t = s = 1`:** for `‖(x, y)‖ ≤ r`,
`Ψ(1, (x, y)) = 𝓛(nW − (√d/2) x, 1 − y; ż(n))`, with the real `nW` and `ż(n)` cast to `ℂ`. -/
private theorem psi_one_gzp
    (θ : Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm 0) hid) dIn dOut) (k : Fin L)
    {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hhol : HolomorphicOnCone geluC θ k.succ κ)
    (Z : Matrix d d ℝ) (η : Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm 0) hid) dIn dOut)
    (ξ ξ' : d → ℝ) (hP2 : PathP2 (θ.read k) (θ.write k) κ ξ ξ') (hd : 0 < Fintype.card d)
    (x : (hid k → ℂ) × (hid k → ℂ)) (hx : ‖x‖ ≤ rad_gzp (θ.read k) (θ.write k) ξ κ) :
    psi_gzp θ k η Z ξ ξ' (((1 : ℝ) : ℂ), x)
      = blockLHSC geluC θ k η
        (((Matrix.of fun _ : T => Real.sqrt (Fintype.card d) • ξ) * θ.read k).map
            (fun x : ℝ => (x : ℂ))
          - ((Real.sqrt (Fintype.card d) / 2 : ℝ) : ℂ) • rowM_gzp T x.1)
        (wpM_gzp T x.2)
        ((tangentRMS Z (Matrix.of fun _ : T => Real.sqrt (Fintype.card d) • ξ) * θ.read k
          + (Matrix.of fun _ : T => Real.sqrt (Fintype.card d) • ξ) * η.read k).map
            (fun x : ℝ => (x : ℂ))) := by
  have hcone : ∀ τ, (wM_gzp T (θ.toC.1 k) ξ ξ' (((1 : ℝ)⁻¹ : ℝ) : ℂ) x.1 * θ.toC.2.1 k) τ
      ∈ complexCone κ := by
    rw [inv_one]
    exact cone_poly_gzp (θ.read k) (θ.write k) hκ hκ1 ξ ξ' hP2.2.1 zero_le_one le_rfl x hx
  have h := psi_identity_gzp θ k hκ hκ1 hhol Z η ξ ξ' hd one_pos x.1 x.2 hcone
  have e0 : ((1 : ℝ) : ℂ) ^ 2 = 1 := by simp
  rw [smul_wM_gzp _ ξ ξ' one_pos, e0, one_smul, inv_one, pathMatrix_one_gzp, zdotC_ofReal] at h
  refine h.trans ?_
  congr 1
  have hW : θ.toC.1 k = (θ.read k).map (fun x : ℝ => (x : ℂ)) := rfl
  ext τ i
  rw [hW, map_mul_gzp]
  simp only [Matrix.of_apply, Matrix.sub_apply, Matrix.smul_apply, rowM_apply_gzp, smul_eq_mul]
  push_cast
  ring

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the real part of complex matrices, as a real continuous linear map. -/
private noncomputable def reCLM_gzp (m n : Type*) [Fintype m] [Fintype n] :
    Matrix m n ℂ →L[ℝ] Matrix m n ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => M.map Complex.re
      map_add' := fun A B => by ext i j; simp
      map_smul' := fun c A => by ext i j; simp [Complex.real_smul] }

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the real part of the cast is the matrix. -/
private theorem reCLM_ofReal_gzp {m n : Type*} [Fintype m] [Fintype n] (M : Matrix m n ℝ) :
    reCLM_gzp m n (M.map (fun x : ℝ => (x : ℂ))) = M := by
  ext i j
  simp [reCLM_gzp]

omit [Fintype d] [DecidableEq d] in
/-- Helper: `rowM_gzp` of `0`. -/
private theorem rowM_zero_gzp (T' : Type*) {ι : Type*} :
    rowM_gzp T' (0 : ι → ℂ) = 0 := rfl

omit [Fintype d] [DecidableEq d] in
/-- Helper: `rowM_gzp` of `c v`. -/
private theorem rowM_smul_gzp (T' : Type*) {ι : Type*} (c : ℂ) (v : ι → ℂ) :
    rowM_gzp T' (c • v) = c • rowM_gzp T' v := rfl

/-- **Step 7, `𝓛'_j(1) = 0`:** if the derivative of `Ψ(1, ·)` at `0` along `(0, e_j)` vanishes,
then `𝐃𝓑(nWV)(ż_j(n) a_j) = 0`. Near `0`, `Ψ(1, (0, σ e_j)) = 𝓛(nW, 1; ż) − σ 𝐃𝓑(nWV)((e_j ⊙ ż)V)`
(the identity at `t = 1`, and `𝓛` affine in `w'`). -/
private theorem unit_write_gzp
    (θ : Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm 0) hid) dIn dOut) (k : Fin L)
    [DecidableEq (hid k)] {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hhol : HolomorphicOnCone geluC θ k.succ κ)
    (Z : Matrix d d ℝ) (η : Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm 0) hid) dIn dOut)
    (ξ ξ' : d → ℝ) (hP2 : PathP2 (θ.read k) (θ.write k) κ ξ ξ') (hd : 0 < Fintype.card d)
    (j : hid k)
    (hu : fderiv ℂ (fun x : (hid k → ℂ) × (hid k → ℂ) => psi_gzp θ k η Z ξ ξ' (((1 : ℝ) : ℂ), x))
      0 ((0 : hid k → ℂ), (Pi.single j 1 : hid k → ℂ)) = 0) :
    fderiv ℝ (fun h' : Matrix T d ℝ => suffix (Arch.mlp gelu (rmsNorm 0) hid) 0 θ k.succ h')
        ((Matrix.of fun _ : T => Real.sqrt (Fintype.card d) • ξ) * θ.read k * θ.write k)
        (Matrix.of fun t =>
          (tangentRMS Z (Matrix.of fun _ : T => Real.sqrt (Fintype.card d) • ξ) * θ.read k
            + (Matrix.of fun _ : T => Real.sqrt (Fintype.card d) • ξ) * η.read k) t j
            • θ.write k j) = 0 := by
  have hU := sqrt_u_pos_gzp (θ.read k) (θ.write k) hκ ξ ξ' hP2.2.1
  have hr := rad_pos_gzp (θ.read k) (θ.write k) hκ ξ ξ' hP2.2.1
  have hrow := rows_ne_zero_gzp (T := T) (θ.read k) (θ.write k) ξ hU hd
  have hone := psi_one_gzp θ k hκ hκ1 hhol Z η ξ ξ' hP2 hd
  obtain ⟨n, hn⟩ : ∃ n : Matrix T d ℝ, n = Matrix.of fun _ : T => Real.sqrt (Fintype.card d) • ξ :=
    ⟨_, rfl⟩
  rw [← hn] at hone hrow ⊢
  obtain ⟨zd, hzd⟩ : ∃ zd : Matrix T (hid k) ℝ, zd = tangentRMS Z n * θ.read k + n * η.read k :=
    ⟨_, rfl⟩
  rw [← hzd] at hone ⊢
  -- the line `σ ↦ σ v`, `v = (0, e_j)`: its derivative at `0` is `𝐃Ψ(1, ·)(0) v = 0`
  obtain ⟨v, hv⟩ : ∃ v : (hid k → ℂ) × (hid k → ℂ),
      v = ((0 : hid k → ℂ), (Pi.single j 1 : hid k → ℂ)) := ⟨_, rfl⟩
  rw [← hv] at hu
  have hf : DifferentiableAt ℂ
      (fun x : (hid k → ℂ) × (hid k → ℂ) => psi_gzp θ k η Z ξ ξ' (((1 : ℝ) : ℂ), x)) 0 :=
    ((analyticAt_psi_poly_gzp θ k hκ hκ1 hhol Z η ξ ξ' hP2 1 zero_le_one le_rfl 0
      (by rw [norm_zero]; exact hr.le)).comp₂ analyticAt_const analyticAt_id).differentiableAt
  have hline : HasDerivAt (fun σ : ℂ => psi_gzp θ k η Z ξ ξ' (((1 : ℝ) : ℂ), σ • v)) 0 0 := by
    have h1 : HasDerivAt (fun σ : ℂ => σ • v) ((1 : ℂ) • v) 0 := (hasDerivAt_id' 0).smul_const v
    have h2 := hf.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℂ) h1 (by rw [zero_smul])
    have e : fderiv ℂ (fun x : (hid k → ℂ) × (hid k → ℂ) =>
        psi_gzp θ k η Z ξ ξ' (((1 : ℝ) : ℂ), x)) 0 ((1 : ℂ) • v) = 0 := by
      rw [one_smul]
      exact hu
    exact h2.congr_deriv e
  -- near `0`, `Ψ(1, σ v) = 𝓛(nW, 1; ż) − σ K`
  obtain ⟨K, hK⟩ : ∃ K, K = fderiv ℂ (fun h' : Matrix T d ℂ => suffixC geluC θ.toC k.succ h')
      ((n * θ.read k).map (fun x : ℝ => (x : ℂ)) * θ.toC.2.1 k)
      ((Matrix.of fun t i => (Pi.single j 1 : hid k → ℂ) i * zd.map (fun x : ℝ => (x : ℂ)) t i)
        * θ.toC.2.1 k) := ⟨_, rfl⟩
  have hev : (fun σ : ℂ => psi_gzp θ k η Z ξ ξ' (((1 : ℝ) : ℂ), σ • v))
      =ᶠ[nhds 0] fun σ => blockLHSC geluC θ k η ((n * θ.read k).map (fun x : ℝ => (x : ℂ)))
          (wpM_gzp T 0) (zd.map (fun x : ℝ => (x : ℂ))) - σ • K := by
    have hc : Continuous fun σ : ℂ => σ • v := continuous_id.smul continuous_const
    have h0 := hc.tendsto 0
    rw [zero_smul] at h0
    filter_upwards [h0 (Metric.closedBall_mem_nhds 0 hr)] with σ hσ
    rw [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right] at hσ
    rw [hone _ hσ, hv]
    simp only [Prod.smul_mk, smul_zero, rowM_zero_gzp, sub_zero]
    rw [blockLHSC_wpM_gzp, hK, ← map_smul, ← Matrix.smul_mul]
    congr 3
    ext t i
    simp only [Matrix.of_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hg : HasDerivAt (fun σ : ℂ => blockLHSC geluC θ k η
      ((n * θ.read k).map (fun x : ℝ => (x : ℂ))) (wpM_gzp T 0)
        (zd.map (fun x : ℝ => (x : ℂ))) - σ • K) (-((1 : ℂ) • K)) 0 :=
    ((hasDerivAt_id' 0).smul_const K).const_sub _
  have hK0 : K = 0 := by
    have h := (hline.congr_of_eventuallyEq hev.symm).unique hg
    rw [one_smul] at h
    exact neg_eq_zero.1 h.symm
  -- `K` is the cast of the real derivative
  have e1 : (n * θ.read k).map (fun x : ℝ => (x : ℂ)) * θ.toC.2.1 k
      = (n * θ.read k * θ.write k).map (fun x : ℝ => (x : ℂ)) := by
    rw [map_mul_gzp (n * θ.read k)]
    rfl
  have e2 : (Matrix.of fun t i => (Pi.single j 1 : hid k → ℂ) i * zd.map (fun x : ℝ => (x : ℂ)) t i)
        * θ.toC.2.1 k
      = (Matrix.of fun t => zd t j • θ.write k j).map (fun x : ℝ => (x : ℂ)) := by
    ext t l
    simp [Matrix.mul_apply, Pi.single_apply, Params.toC]
  rw [hK, e1, e2, fderiv_suffixC_ofReal geluC_ofReal θ k.succ hκ hhol _ _ hrow] at hK0
  ext t l
  have := congrFun (congrFun hK0 t) l
  simpa using this

/-- **Step 7, `𝓛_j(1) = 0`:** if the derivative of `Ψ(1, ·)` at `0` along `(e_j, 0)` vanishes,
then the derivative at `τ = 0` of `τ ↦ 𝓛(nW − τ e_j, 1; ż(n))` (real) vanishes. Near `0`,
`Ψ(1, (σ e_j, 0)) = G((√d/2) σ)` with `G(c) = 𝓛(nW − c e_j, 1; ż)` holomorphic; at real `τ` near
`0`, `G(τ)` is the cast of the real `𝓛`. -/
private theorem unit_read_gzp
    (θ : Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm 0) hid) dIn dOut) (k : Fin L)
    [DecidableEq (hid k)] {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hhol : HolomorphicOnCone geluC θ k.succ κ)
    (Z : Matrix d d ℝ) (η : Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm 0) hid) dIn dOut)
    (ξ ξ' : d → ℝ) (hP2 : PathP2 (θ.read k) (θ.write k) κ ξ ξ') (hd : 0 < Fintype.card d)
    (j : hid k)
    (hu : fderiv ℂ (fun x : (hid k → ℂ) × (hid k → ℂ) => psi_gzp θ k η Z ξ ξ' (((1 : ℝ) : ℂ), x))
      0 ((Pi.single j 1 : hid k → ℂ), (0 : hid k → ℂ)) = 0) :
    deriv (fun τ : ℝ =>
        blockLHS θ k η
          ((Matrix.of fun _ : T => Real.sqrt (Fintype.card d) • ξ) * θ.read k
            - τ • Matrix.of fun _ : T => (Pi.single j 1 : hid k → ℝ))
          (fun _ _ => 1)
          (tangentRMS Z (Matrix.of fun _ : T => Real.sqrt (Fintype.card d) • ξ) * θ.read k
            + (Matrix.of fun _ : T => Real.sqrt (Fintype.card d) • ξ) * η.read k)) 0 = 0 := by
  have hsd : 0 < Real.sqrt (Fintype.card d) := Real.sqrt_pos.2 (by exact_mod_cast hd)
  have hU := sqrt_u_pos_gzp (θ.read k) (θ.write k) hκ ξ ξ' hP2.2.1
  have hr := rad_pos_gzp (θ.read k) (θ.write k) hκ ξ ξ' hP2.2.1
  have hrow := rows_ne_zero_gzp (T := T) (θ.read k) (θ.write k) ξ hU hd
  have hcone := rows_mem_cone_gzp (T := T) (θ.read k) (θ.write k) ξ hκ hU hd
  have hone := psi_one_gzp θ k hκ hκ1 hhol Z η ξ ξ' hP2 hd
  obtain ⟨n, hn⟩ : ∃ n : Matrix T d ℝ, n = Matrix.of fun _ : T => Real.sqrt (Fintype.card d) • ξ :=
    ⟨_, rfl⟩
  rw [← hn] at hone hrow hcone ⊢
  obtain ⟨zd, hzd⟩ : ∃ zd : Matrix T (hid k) ℝ, zd = tangentRMS Z n * θ.read k + n * η.read k :=
    ⟨_, rfl⟩
  rw [← hzd] at hone ⊢
  -- `G(c) = 𝓛(nW − c E_j, 1; ż)` is holomorphic at `0`
  obtain ⟨E, hE⟩ : ∃ E : Matrix T (hid k) ℂ, E = rowM_gzp T (Pi.single j 1 : hid k → ℂ) :=
    ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G : ℂ → Matrix T dOut ℂ, ∀ c, G c = blockLHSC geluC θ k η
      ((n * θ.read k).map (fun x : ℝ => (x : ℂ)) - c • E) (wpM_gzp T 0)
        (zd.map (fun x : ℝ => (x : ℂ))) := ⟨_, fun _ => rfl⟩
  have hGa : AnalyticAt ℂ G 0 := by
    have h := analyticAt_blockLHSC_comp_gzp θ k hhol η
      (f₁ := fun c : ℂ => (n * θ.read k).map (fun x : ℝ => (x : ℂ)) - c • E)
      (f₂ := fun _ => wpM_gzp T 0) (f₃ := fun _ => zd.map (fun x : ℝ => (x : ℂ))) (x := 0)
      (analyticAt_const.sub (analyticAt_id.smul analyticAt_const)) analyticAt_const
      analyticAt_const (fun τ => by
        show (((n * θ.read k).map (fun x : ℝ => (x : ℂ)) - (0 : ℂ) • E) * θ.toC.2.1 k) τ
          ∈ complexCone κ
        rw [zero_smul, sub_zero]
        exact hcone τ)
    exact h.congr (Filter.Eventually.of_forall fun c => (hG c).symm)
  have hGd := hGa.differentiableAt.hasDerivAt
  -- the line `σ ↦ σ v`, `v = (e_j, 0)`: its derivative at `0` is `𝐃Ψ(1, ·)(0) v = 0`
  obtain ⟨v, hv⟩ : ∃ v : (hid k → ℂ) × (hid k → ℂ),
      v = ((Pi.single j 1 : hid k → ℂ), (0 : hid k → ℂ)) := ⟨_, rfl⟩
  rw [← hv] at hu
  have hf : DifferentiableAt ℂ
      (fun x : (hid k → ℂ) × (hid k → ℂ) => psi_gzp θ k η Z ξ ξ' (((1 : ℝ) : ℂ), x)) 0 :=
    ((analyticAt_psi_poly_gzp θ k hκ hκ1 hhol Z η ξ ξ' hP2 1 zero_le_one le_rfl 0
      (by rw [norm_zero]; exact hr.le)).comp₂ analyticAt_const analyticAt_id).differentiableAt
  have hline : HasDerivAt (fun σ : ℂ => psi_gzp θ k η Z ξ ξ' (((1 : ℝ) : ℂ), σ • v)) 0 0 := by
    have h1 : HasDerivAt (fun σ : ℂ => σ • v) ((1 : ℂ) • v) 0 := (hasDerivAt_id' 0).smul_const v
    have h2 := hf.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℂ) h1 (by rw [zero_smul])
    have e : fderiv ℂ (fun x : (hid k → ℂ) × (hid k → ℂ) =>
        psi_gzp θ k η Z ξ ξ' (((1 : ℝ) : ℂ), x)) 0 ((1 : ℂ) • v) = 0 := by
      rw [one_smul]
      exact hu
    exact h2.congr_deriv e
  -- near `0`, `Ψ(1, σ v) = G(c σ)` with `c = √d/2`
  have hev : (fun σ : ℂ => psi_gzp θ k η Z ξ ξ' (((1 : ℝ) : ℂ), σ • v))
      =ᶠ[nhds 0] fun σ => G (((Real.sqrt (Fintype.card d) / 2 : ℝ) : ℂ) * σ) := by
    have hc : Continuous fun σ : ℂ => σ • v := continuous_id.smul continuous_const
    have h0 := hc.tendsto 0
    rw [zero_smul] at h0
    filter_upwards [h0 (Metric.closedBall_mem_nhds 0 hr)] with σ hσ
    rw [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right] at hσ
    rw [hone _ hσ, hG, hv, hE]
    simp only [Prod.smul_mk, smul_zero, rowM_smul_gzp, smul_smul]
  have hcomp : HasDerivAt (G ∘ fun σ : ℂ => ((Real.sqrt (Fintype.card d) / 2 : ℝ) : ℂ) * σ)
      (((Real.sqrt (Fintype.card d) / 2 : ℝ) : ℂ) • deriv G 0) 0 := by
    have h1 : HasDerivAt (fun σ : ℂ => ((Real.sqrt (Fintype.card d) / 2 : ℝ) : ℂ) * σ)
        ((Real.sqrt (Fintype.card d) / 2 : ℝ) : ℂ) 0 := by
      simpa using (hasDerivAt_id' (0 : ℂ)).const_mul ((Real.sqrt (Fintype.card d) / 2 : ℝ) : ℂ)
    exact hGd.scomp_of_eq 0 h1 (by rw [mul_zero])
  have hG0 : deriv G 0 = 0 := by
    have h := (hline.congr_of_eventuallyEq hev.symm).unique hcomp
    have hc0 : ((Real.sqrt (Fintype.card d) / 2 : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.2 (by positivity)
    exact (smul_eq_zero.1 h.symm).resolve_left hc0
  -- at real `τ`: `G(τ)` has the derivative `0`, and so has its real part
  have hGr : HasDerivAt (fun τ : ℝ => G (τ : ℂ)) 0 0 := by
    have h1 : HasDerivAt (fun τ : ℝ => (τ : ℂ)) 1 0 := by
      simpa using (hasDerivAt_id' (0 : ℝ)).ofReal_comp
    have hGd0 : HasDerivAt G 0 0 := by
      rw [← hG0]
      exact hGd
    have h2 := hGd0.scomp_of_eq (0 : ℝ) h1 (by rw [Complex.ofReal_zero])
    exact h2.congr_deriv (smul_zero _)
  have hre : HasDerivAt (fun τ : ℝ => reCLM_gzp T dOut (G (τ : ℂ))) 0 0 := by
    have h := (reCLM_gzp T dOut).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hGr
    exact h.congr_deriv (map_zero _)
  -- near `0` the rows of `(nW − τ E_j) V` do not vanish, and `G(τ)` is the cast of the real `𝓛`
  have hrows : ∀ᶠ τ in nhds (0 : ℝ), ∀ τ', ((n * θ.read k
      - τ • Matrix.of fun _ : T => (Pi.single j 1 : hid k → ℝ)) * θ.write k) τ' ≠ 0 := by
    refine Filter.eventually_all.2 fun τ' => ?_
    have e : (fun τ : ℝ => ((n * θ.read k
        - τ • Matrix.of fun _ : T => (Pi.single j 1 : hid k → ℝ)) * θ.write k) τ')
        = fun τ => (n * θ.read k * θ.write k) τ'
          - τ • ((Matrix.of fun _ : T => (Pi.single j 1 : hid k → ℝ)) * θ.write k) τ' := by
      funext τ
      rw [Matrix.sub_mul, Matrix.smul_mul]
      rfl
    have hc : Continuous fun τ : ℝ => ((n * θ.read k
        - τ • Matrix.of fun _ : T => (Pi.single j 1 : hid k → ℝ)) * θ.write k) τ' := by
      rw [e]
      fun_prop
    have h0 : ((n * θ.read k - (0 : ℝ) • Matrix.of fun _ : T => (Pi.single j 1 : hid k → ℝ))
        * θ.write k) τ' ≠ 0 := by
      rw [zero_smul, sub_zero]
      exact hrow τ'
    exact hc.continuousAt.eventually_ne h0
  have hev2 : (fun τ : ℝ => blockLHS θ k η
      (n * θ.read k - τ • Matrix.of fun _ : T => (Pi.single j 1 : hid k → ℝ)) (fun _ _ => 1) zd)
      =ᶠ[nhds 0] fun τ => reCLM_gzp T dOut (G (τ : ℂ)) := by
    filter_upwards [hrows] with τ hτ
    have h := blockLHSC_ofReal geluC_ofReal θ k hκ hhol η _ (fun _ _ => 1) zd hτ
    have e1 : (n * θ.read k - τ • Matrix.of fun _ : T => (Pi.single j 1 : hid k → ℝ)).map
        (fun x : ℝ => (x : ℂ)) = (n * θ.read k).map (fun x : ℝ => (x : ℂ)) - (τ : ℂ) • E := by
      rw [hE]
      ext a b
      simp only [Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply,
        rowM_apply_gzp, Pi.single_apply, smul_eq_mul]
      split_ifs <;> simp
    have e2 : Matrix.map (fun _ _ => (1 : ℝ) : Matrix T (hid k) ℝ) (fun x : ℝ => (x : ℂ))
        = wpM_gzp T 0 := by
      ext a b
      show ((1 : ℝ) : ℂ) = 1 - (0 : hid k → ℂ) b
      simp
    rw [e1, e2, ← hG] at h
    rw [h, reCLM_ofReal_gzp]
  exact (hre.congr_of_eventuallyEq hev2).deriv

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
  have hd := card_pos_gzp ξ hξ
  intro t ht
  have ht0 : 0 < t := by linarith
  have hs0 : 0 < t⁻¹ := inv_pos.2 ht0
  have hs1 : t⁻¹ ≤ 1 := inv_le_one_of_one_le₀ ht
  -- Step 1 of the paper: `Ψ(1/t, 0) = 0`
  have h0 : psi_gzp θ k η Z ξ ξ' (((t⁻¹ : ℝ) : ℂ), ((0 : hid k → ℂ), (0 : hid k → ℂ))) = 0 :=
    psi_zero_gzp θ hθ k hκ hκ1 hhol Z η h16 ξ ξ' hξ hξ' hξξ' hP2 hd t⁻¹ hs0 hs1
  -- the identity at `x = y = 0`: `t² Ψ(1/t, 0) = 𝓛(n(t)W, 1; n(t))`
  have hcone : ∀ τ, (wM_gzp T (θ.toC.1 k) ξ ξ' ((t⁻¹ : ℝ) : ℂ) 0 * θ.toC.2.1 k) τ
      ∈ complexCone κ :=
    cone_poly_gzp (θ.read k) (θ.write k) hκ hκ1 ξ ξ' hP2.2.1 hs0.le hs1 0
      (by rw [norm_zero]; exact (rad_pos_gzp _ _ hκ ξ ξ' hP2.2.1).le)
  have h := psi_identity_gzp θ k hκ hκ1 hhol Z η ξ ξ' hd ht0 0 0 hcone
  rw [h0, smul_zero, smul_wM_gzp _ ξ ξ' ht0] at h
  have e1 : (Matrix.of fun τ i =>
      (pathMatrix (Matrix.of fun _ : T => ξ) (Matrix.of fun _ : T => ξ') (t : ℂ) * θ.toC.1 k) τ i
        - ((Real.sqrt (Fintype.card d) * t / 2 : ℝ) : ℂ) * (0 : hid k → ℂ) i)
      = pathMatrix (Matrix.of fun _ : T => ξ) (Matrix.of fun _ : T => ξ') (t : ℂ)
        * θ.toC.1 k := by
    ext τ i
    simp
  have e2 : wpM_gzp T (0 : hid k → ℂ) = fun _ _ => 1 := by
    ext τ i
    simp [wpM_gzp]
  rw [e1, e2] at h
  exact h.symm

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
  have hd := card_pos_gzp ξ hξ
  have hU := sqrt_u_pos_gzp (θ.read k) (θ.write k) hκ ξ ξ' hP2.2.1
  -- the case `t = 1` of `gelu_path_step_zero`, with `n(1) = n` real
  have h := gelu_path_step_zero θ hθ k hκ hκ1 hhol Z η h16 ξ ξ' hξ hξ' hξξ' hP2 1 le_rfl
  have hW : θ.toC.1 k = (θ.read k).map (fun x : ℝ => (x : ℂ)) := rfl
  rw [pathMatrix_one_gzp, zdotC_ofReal, hW, ← map_mul_gzp] at h
  have e1 : (fun _ _ => 1 : Matrix T (hid k) ℂ)
      = (Matrix.of fun _ _ => (1 : ℝ) : Matrix T (hid k) ℝ).map (fun x : ℝ => (x : ℂ)) := by
    ext τ i
    show (1 : ℂ) = ((1 : ℝ) : ℂ)
    simp
  rw [e1, blockLHSC_ofReal geluC_ofReal θ k hκ hhol η _ _ _
    (rows_ne_zero_gzp (θ.read k) (θ.write k) ξ hU hd)] at h
  have h' : blockLHS θ k η
      ((Matrix.of fun _ : T => Real.sqrt (Fintype.card d) • ξ) * θ.read k)
      (Matrix.of fun _ _ => (1 : ℝ))
      (tangentRMS Z (Matrix.of fun _ : T => Real.sqrt (Fintype.card d) • ξ) * θ.read k
        + (Matrix.of fun _ : T => Real.sqrt (Fintype.card d) • ξ) * η.read k) = 0 := by
    ext τ l
    have := congrFun (congrFun h τ) l
    simpa using this
  exact h'

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
  have hd := card_pos_gzp ξ hξ
  have hsd : 0 < Real.sqrt (Fintype.card d) := Real.sqrt_pos.2 (by exact_mod_cast hd)
  have hr := rad_pos_gzp (θ.read k) (θ.write k) hκ ξ ξ' hP2.2.1
  -- the hypothesis on `A` for `Ψ`: `Ψ(s, x) = 0` by the identity at `t = 1/s` and `hA`
  have hA' : ∀ s : ℝ, 0 < s → s ≤ 1 → ∀ x : (hid k → ℂ) × (hid k → ℂ),
      ‖x‖ ≤ rad_gzp (θ.read k) (θ.write k) ξ κ → (∀ i, i ∉ A → x.1 i = 0 ∧ x.2 i = 0) →
        psi_gzp θ k η Z ξ ξ' ((s : ℂ), x) = 0 := by
    intro s hs0 hs1 x hx hxA
    have ht0 : 0 < s⁻¹ := inv_pos.2 hs0
    have ht1 : 1 ≤ s⁻¹ := (one_le_inv₀ hs0).2 hs1
    have hcone : ∀ τ, (wM_gzp T (θ.toC.1 k) ξ ξ' ((s⁻¹⁻¹ : ℝ) : ℂ) x.1 * θ.toC.2.1 k) τ
        ∈ complexCone κ := by
      rw [inv_inv]
      exact cone_poly_gzp (θ.read k) (θ.write k) hκ hκ1 ξ ξ' hP2.2.1 hs0.le hs1 x hx
    have h := psi_identity_gzp θ k hκ hκ1 hhol Z η ξ ξ' hd ht0 x.1 x.2 hcone
    rw [smul_wM_gzp _ ξ ξ' ht0] at h
    have hz := hA s⁻¹ ht1
      (fun i => ((Real.sqrt (Fintype.card d) * s⁻¹ / 2 : ℝ) : ℂ) * x.1 i) x.2
      (fun i hi => ⟨by rw [(hxA i hi).1, mul_zero], (hxA i hi).2⟩)
    have h2 : ((s⁻¹ : ℝ) : ℂ) ^ 2 • psi_gzp θ k η Z ξ ξ' (((s⁻¹⁻¹ : ℝ) : ℂ), (x.1, x.2)) = 0 :=
      h.trans hz
    rw [inv_inv] at h2
    exact (smul_eq_zero.1 h2).resolve_left (pow_ne_zero 2 (Complex.ofReal_ne_zero.2 ht0.ne'))
  -- the rates: `(Re ω)² − (Im ω)² = (d/4) r`
  have hrate' : ∀ i, i ∉ A → i ≠ j →
      (omega_gzp (θ.read k) ξ ξ' j).re ^ 2 - (omega_gzp (θ.read k) ξ ξ' j).im ^ 2
        < (omega_gzp (θ.read k) ξ ξ' i).re ^ 2 - (omega_gzp (θ.read k) ξ ξ' i).im ^ 2 := by
    intro i hi hij
    have h := mul_lt_mul_of_pos_left (hrate i hi hij)
      (by positivity : (0 : ℝ) < (Real.sqrt (Fintype.card d) / 2) ^ 2)
    show (Real.sqrt (Fintype.card d) / 2 * (ξ ᵥ* θ.read k) j) ^ 2
        - (Real.sqrt (Fintype.card d) / 2 * (ξ' ᵥ* θ.read k) j) ^ 2
      < (Real.sqrt (Fintype.card d) / 2 * (ξ ᵥ* θ.read k) i) ^ 2
        - (Real.sqrt (Fintype.card d) / 2 * (ξ' ᵥ* θ.read k) i) ^ 2
    nlinarith [h]
  -- Steps 2 and 4 of the paper (`gelu_path_unit`) at `s = 1`, then Step 7
  obtain ⟨hu1, hu2⟩ := gelu_path_unit (omega_gzp (θ.read k) ξ ξ')
    (omega_im_lt_gzp _ ξ ξ' hP2.1 hd) (c₀ := 2 / Real.sqrt (Fintype.card d))
    (div_ne_zero two_ne_zero hsd.ne') (psi_gzp θ k η Z ξ ξ') hr
    (analyticAt_psi_poly_gzp θ k hκ hκ1 hhol Z η ξ ξ' hP2)
    (Filter.eventually_atTop.2 ⟨1, fun _ ht =>
      psi_path_gzp θ hθ k hκ hκ1 hhol Z η h16 ξ ξ' hξ hξ' hξξ' hP2 hd ht⟩)
    A j hjA hrate' hA' 1 one_pos le_rfl
  exact ⟨unit_read_gzp θ k hκ hκ1 hhol Z η ξ ξ' hP2 hd j hu1,
    unit_write_gzp θ k hκ hκ1 hhol Z η ξ ξ' hP2 hd j hu2⟩

end Skips
