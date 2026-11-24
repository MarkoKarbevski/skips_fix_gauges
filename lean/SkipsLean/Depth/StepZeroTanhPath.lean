import SkipsLean.Depth.ComplexOneSubSq
import SkipsLean.Depth.PathSeparation

/-!
# The step for `tanh` on the path: what one pair `ξ, ξ'` gives

Paper (dimension paper): Appendix D.6 (the case `ε = 0`), proof of Lemma D.18 (the step for `tanh`
on the path), its parts "The path" and "The powers of `t`", for one pair of rows.

"Fix `ξ ∈ P'` and a unit row `ξ'` orthogonal to `ξ`, and let `n(t)` be the path (41). Let

  `ζ_j(t) = e^{−2 s_j n(t) c_j} = exp(−(t + t⁻¹) √d |ξc_j| − i (t − t⁻¹) √d s_j ξ'c_j)`,

so that `|ζ_j(t)| < ρ/3` for `t ≥ 1`, and `tanh(n(t) c_j) = s_j (1 − ζ_j(t))/(1 + ζ_j(t))`,
`tanh'(n(t) c_j) = 1 − tanh²(n(t) c_j)`. For `ζ` in the polydisc `D = {|ζ_j| < ρ/3}` let `w̃(ζ)` be
the row with the entries `s_j (1 − ζ_j)/(1 + ζ_j)`. As `|w̃_j(ζ) − s_j| = 2|ζ_j|/|1 + ζ_j| ≤ 3|ζ_j|
< ρ`, (S3) gives `w̃(ζ) V ∈ C_κ`. The function `tanh` is holomorphic at `n(t) c_j`, as
`ζ_j(t) ≠ −1`. So Lemma D.15 applies:

  `𝓛(w̃(ζ(t)), 1 − w̃(ζ(t))²; n(t)) = 0` for all `t ≥ 1`.   (42)

By (20), `ż(n(t)) = t³ ż⁽³⁾ + t ż⁽¹⁾ + t⁻¹ ż⁽⁻¹⁾ + t⁻³ ż⁽⁻³⁾` with rows `ż⁽ⁱ⁾ ∈ ℂ^{1×q}` that do not
depend on `t`, and

  `ż⁽³⁾ = −(√d/8) ⟨νZ, ν⟩ νW`,
  `ż⁽¹⁾ = (√d/2) (ν (ZW + η_W) − (1/4) ((⟨νZ, ν̄⟩ + ⟨ν̄Z, ν⟩) ν + ⟨νZ, ν⟩ ν̄) W)`.   (43)

`𝓛` is affine in `ż`, so (42) reads `∑_i t^i 𝒯_i(ζ(t)) = 0` with the maps
`𝒯_i(ζ) = 𝐃𝓑(w̃(ζ)V) (((1 − w̃(ζ)²) ⊙ ż⁽ⁱ⁾) V)` (`i = ±1, ±3`),
`𝒯_0(ζ) = 𝐃𝓑(w̃(ζ)V) (w̃(ζ) η_V) + 𝐃_θ𝓑(w̃(ζ)V) η'`, which are holomorphic on `D`. By Lemma D.16,
with `u_j = √d |ξc_j|` and `ρ₀ = ρ/3`, every `𝒯_i` vanishes on `D`. For real `ζ ∈ D` the rows
`w̃(ζ)` fill a neighborhood of `s̄` in `ℝ^{1×q}`."

Then `𝒯_3 = 0` and Lemma D.17 give `⟨νZ, ν⟩ = 0` (the row `νW` is not zero); `𝒯_1 = 0` and
Lemma D.17 give `ż⁽¹⁾ = 0`; and `𝒯_0 = 0` is the identity of part (c) for real `w̃` near `s̄`.

The statement below is this, for one pair `ξ, ξ'`, in real terms. With `ν = ξ + iξ'`:
`⟨νZ, ν⟩ = (ξZξᵀ − ξ'Zξ'ᵀ) + i (ξZξ'ᵀ + ξ'Zξᵀ)`, so `⟨νZ, ν⟩ = 0` is the first pair of
equations; then `⟨νZ, ν̄⟩ + ⟨ν̄Z, ν⟩ = 2 (ξZξᵀ + ξ'Zξ'ᵀ) = 4 ξZξᵀ`, and `ż⁽¹⁾ = 0` is
`ν (ZW + η_W) = (ξZξᵀ) νW`, the second pair (its real and its imaginary part). The paper's sign
row `s̄`, the number `ρ` and the cone condition of (S3) are hypotheses on `s`, `ρ` and `ξ` here
(Lemma D.18 takes them from (S3) for the rows `ξ` near `ξ₀`). The path has the same row at every
token. Numbering as in `Depth/StepTanh.lean`: the block is `k : Fin L`, the paper's block `k + 1`.
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut] {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]

/-- The row `w̃(ζ)` with the entries `s_j (1 − ζ_j)/(1 + ζ_j)`. -/
private noncomputable def wt_tps {ι : Type*} (s : ι → ℝ) (ζ : ι → ℂ) : ι → ℂ :=
  fun j => (s j : ℂ) * (1 - ζ j) / (1 + ζ j)

/-- Helper: `1 + ζ ≠ 0` for `‖ζ‖ < 1`. -/
private theorem one_add_ne_zero_tps {ζ : ℂ} (hζ : ‖ζ‖ < 1) : 1 + ζ ≠ 0 := by
  intro h
  have : ζ = -1 := by linear_combination h
  rw [this, norm_neg, norm_one] at hζ
  exact lt_irrefl _ hζ

/-- Step 1: with `ζ = exp(−2 s z)`, `‖ζ‖ < 1`: `cosh z ≠ 0` and `tanh z = s (1 − ζ)/(1 + ζ)`. -/
private theorem tanh_eq_tps (z : ℂ) (s : ℝ) (hs : s = 1 ∨ s = -1)
    (hζ : ‖Complex.exp (-2 * (s : ℂ) * z)‖ < 1) :
    Complex.cosh z ≠ 0 ∧ Complex.tanh z
      = (s : ℂ) * (1 - Complex.exp (-2 * (s : ℂ) * z)) / (1 + Complex.exp (-2 * (s : ℂ) * z)) := by
  have h1 := one_add_ne_zero_tps hζ
  set a := Complex.exp z with ha
  set b := Complex.exp (-z) with hb
  have hab : a * b = 1 := by rw [ha, hb, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  have ha0 : a ≠ 0 := Complex.exp_ne_zero z
  have hb0 : b ≠ 0 := Complex.exp_ne_zero (-z)
  have hcosh : Complex.cosh z = (a + b) / 2 := by
    rw [ha, hb, ← Complex.two_cosh]; ring
  have hsinh : Complex.sinh z = (a - b) / 2 := by
    rw [ha, hb, ← Complex.two_sinh]; ring
  rcases hs with hs | hs
  · -- `s = 1`: `ζ = b²`
    have hz : Complex.exp (-2 * (s : ℂ) * z) = b * b := by
      rw [hs, hb, ← Complex.exp_add]; congr 1; push_cast; ring
    rw [hz] at h1 ⊢
    have hab' : a + b ≠ 0 := by
      intro h; apply h1; linear_combination b * h - hab
    refine ⟨by rw [hcosh]; exact div_ne_zero hab' two_ne_zero, ?_⟩
    rw [Complex.tanh_eq_sinh_div_cosh, hsinh, hcosh, hs]
    rw [div_div_div_cancel_right₀ two_ne_zero, div_eq_div_iff hab' h1]
    push_cast
    linear_combination (2 * b) * hab
  · -- `s = −1`: `ζ = a²`
    have hz : Complex.exp (-2 * (s : ℂ) * z) = a * a := by
      rw [hs, ha, ← Complex.exp_add]; congr 1; push_cast; ring
    rw [hz] at h1 ⊢
    have hab' : a + b ≠ 0 := by
      intro h; apply h1; linear_combination a * h - hab
    refine ⟨by rw [hcosh]; exact div_ne_zero hab' two_ne_zero, ?_⟩
    rw [Complex.tanh_eq_sinh_div_cosh, hsinh, hcosh, hs]
    rw [div_div_div_cancel_right₀ two_ne_zero, div_eq_div_iff hab' h1]
    push_cast
    linear_combination (-2 * a) * hab

/-- Step 1: `tanh' = 1 − tanh²` where `cosh ≠ 0`. -/
private theorem hasDerivAt_ctanh_tps {z : ℂ} (hc : Complex.cosh z ≠ 0) :
    HasDerivAt Complex.tanh (1 - Complex.tanh z ^ 2) z := by
  have hfun : Complex.tanh = fun x => Complex.sinh x / Complex.cosh x := by
    funext x; exact Complex.tanh_eq_sinh_div_cosh x
  have h := (Complex.hasDerivAt_sinh z).div (Complex.hasDerivAt_cosh z) hc
  have heq : 1 - Complex.tanh z ^ 2
      = (Complex.cosh z * Complex.cosh z - Complex.sinh z * Complex.sinh z)
        / Complex.cosh z ^ 2 := by
    rw [Complex.tanh_eq_sinh_div_cosh]
    field_simp
  rw [heq, hfun]
  exact h

/-- Step 1: `tanh` is holomorphic where `cosh ≠ 0`. -/
private theorem analyticAt_ctanh_tps {z : ℂ} (hc : Complex.cosh z ≠ 0) :
    AnalyticAt ℂ Complex.tanh z := by
  have hfun : Complex.tanh = fun x => Complex.sinh x / Complex.cosh x := by
    funext x; exact Complex.tanh_eq_sinh_div_cosh x
  rw [hfun]
  exact (Complex.differentiable_sinh.analyticAt z).div
    (Complex.differentiable_cosh.analyticAt z) hc

/-- Step 1: `‖w̃_j − s_j‖ = 2‖ζ_j‖/‖1 + ζ_j‖ ≤ 3‖ζ_j‖` for `‖ζ_j‖ ≤ 1/3`. -/
private theorem norm_wt_sub_tps (s : ℝ) (hs : s = 1 ∨ s = -1) (ζ : ℂ) (hζ : ‖ζ‖ ≤ 1 / 3) :
    ‖(s : ℂ) * (1 - ζ) / (1 + ζ) - s‖ ≤ 3 * ‖ζ‖ := by
  have h1 : 1 + ζ ≠ 0 := one_add_ne_zero_tps (by linarith)
  have e : (s : ℂ) * (1 - ζ) / (1 + ζ) - s = (-2 * s * ζ) / (1 + ζ) := by
    field_simp; ring
  have hsn : ‖(s : ℂ)‖ = 1 := by
    rcases hs with hs | hs <;> simp [hs]
  have hlow : 1 - ‖ζ‖ ≤ ‖1 + ζ‖ := by
    have := norm_sub_norm_le (1 : ℂ) (-ζ)
    rw [norm_neg, norm_one, sub_neg_eq_add] at this
    exact this
  have hpos : 0 < ‖1 + ζ‖ := norm_pos_iff.2 h1
  rw [e, norm_div, norm_mul, norm_mul, hsn, div_le_iff₀ hpos]
  have : ‖(-2 : ℂ)‖ = 2 := by simp
  rw [this]
  nlinarith [norm_nonneg ζ]

/-- Step 5: a real row `r` near `s` is `w̃(ζ)` for a real `ζ` in the polydisc. -/
private theorem exists_wt_eq_tps {ι : Type*} (s r : ι → ℝ) (hs : ∀ j, s j = 1 ∨ s j = -1)
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hr : ∀ j, |r j - s j| < ρ / 4) :
    ∃ ζ : ι → ℂ, (∀ j, ‖ζ j‖ < ρ / 3) ∧ ∀ j, wt_tps s ζ j = (r j : ℂ) := by
  refine ⟨fun j => (((s j - r j) / (s j + r j) : ℝ) : ℂ), fun j => ?_, fun j => ?_⟩
  · have hrj := hr j
    rw [abs_lt] at hrj
    rw [Complex.norm_real, Real.norm_eq_abs, abs_div]
    rcases hs j with h | h <;> rw [h] at hrj ⊢
    · have hp : 0 < 1 + r j := by linarith
      rw [abs_of_pos hp, div_lt_iff₀ hp, abs_lt]
      constructor <;> nlinarith
    · have hn : -1 + r j < 0 := by linarith
      rw [abs_of_neg hn, div_lt_iff₀ (by linarith), abs_lt]
      constructor <;> nlinarith
  · have hrj := hr j
    rw [abs_lt] at hrj
    simp only [wt_tps]
    rcases hs j with h | h <;> rw [h] at hrj ⊢
    · have hp : (1 : ℝ) + r j ≠ 0 := by linarith
      have hp' : (1 : ℂ) + r j ≠ 0 := by exact_mod_cast hp
      push_cast
      field_simp
      ring
    · have hn : (-1 : ℝ) + r j ≠ 0 := by linarith
      have hn' : (-1 : ℂ) + r j ≠ 0 := by exact_mod_cast hn
      push_cast
      field_simp
      ring

/-- Step 4 (Lemma D.16's hypothesis): `u_j = c |x_j|` is linearly independent over `ℚ`. -/
private theorem linearIndependent_abs_tps {ι : Type*} [Fintype ι] (x s : ι → ℝ)
    (hs : ∀ j, s j = 1 ∨ s j = -1) (hx : ∀ j, 0 < s j * x j) (c : ℝ) (hc : 0 < c)
    (hind : LinearIndependent ℚ x) : LinearIndependent ℚ (fun j => c * |x j|) := by
  classical
  -- the rational signs
  let σ : ι → ℚ := fun j => if s j = 1 then 1 else -1
  have hσ : ∀ j, ((σ j : ℚ) : ℝ) = s j := by
    intro j
    rcases hs j with h | h
    · simp [σ, h]
    · have : s j ≠ 1 := by rw [h]; norm_num
      simp only [σ, ite_eq_right this]
      rw [h]; norm_num
  have habs : ∀ j, |x j| = s j * x j := by
    intro j
    rcases hs j with h | h
    · have := hx j; rw [h] at this ⊢; rw [one_mul] at this ⊢; exact abs_of_pos this
    · rw [h]; have := hx j; rw [h] at this; rw [abs_of_neg (by linarith)]; ring
  rw [Fintype.linearIndependent_iff] at hind ⊢
  intro g hg i
  have key := hind (fun j => g j * σ j) ?_ i
  · have hσi : σ i ≠ 0 := by simp only [σ]; split_ifs <;> norm_num
    exact (mul_eq_zero.1 key).resolve_right hσi
  · -- `∑ g_j σ_j x_j = c⁻¹ ∑ g_j (c |x_j|) = 0`
    have hg' : ∑ j, (g j : ℝ) * (c * |x j|) = 0 := by
      rw [← hg]; refine Finset.sum_congr rfl fun j _ => ?_; rw [Rat.smul_def]
    have : ∑ j, ((g j * σ j : ℚ) : ℝ) * x j = c⁻¹ * ∑ j, (g j : ℝ) * (c * |x j|) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [habs j]; push_cast; rw [hσ j]; field_simp
    simp only [Rat.smul_def]
    rw [this, hg', mul_zero]

/-- The coefficient `c₃ = −(α/4) ⟨aZ, a⟩ aW` of `t³` in `ż` on the path `α (t a + t⁻¹ b)` (and, with
`b` for `a`, the coefficient `c₋₃` of `t⁻³`); `α = √d/2`, `a = ν`, `b = ν̄` in the paper. -/
private noncomputable def cCube_tps {m : Type*} (ZC : Matrix d d ℂ) (WC : Matrix d m ℂ)
    (a : d → ℂ) (α : ℂ) : m → ℂ :=
  (-(α / 4) * ((a ᵥ* ZC) ⬝ᵥ a)) • (a ᵥ* WC)

/-- The coefficient `c₁ = α (a (ZW + η_W) − (1/4) ((⟨aZ, b⟩ + ⟨bZ, a⟩) a + ⟨aZ, a⟩ b) W)` of `t`
in `ż` on the path `α (t a + t⁻¹ b)` (and, with `a, b` exchanged, the coefficient `c₋₁` of
`t⁻¹`). -/
private noncomputable def cPlus_tps {m : Type*} (ZC : Matrix d d ℂ)
    (WC EW : Matrix d m ℂ) (a b : d → ℂ) (α : ℂ) : m → ℂ :=
  α • (a ᵥ* (ZC * WC + EW) - (1 / 4 : ℂ) • ((((a ᵥ* ZC) ⬝ᵥ b + (b ᵥ* ZC) ⬝ᵥ a) • a
    + ((a ᵥ* ZC) ⬝ᵥ a) • b) ᵥ* WC))

omit [DecidableEq d] in
/-- Step 2: the row of `ż(n)` on the path `n = α (t a + t⁻¹ b)`, with `α² = d/4`, is
`t³ c₃ + t c₁ + t⁻¹ c₋₁ + t⁻³ c₋₃`. -/
private theorem zdot_row_tps {m : Type*} [Fintype m] (ZC : Matrix d d ℂ) (WC EW : Matrix d m ℂ)
    (a b : d → ℂ) (α t : ℂ) (ht : t ≠ 0) (hα0 : α ≠ 0)
    (hα : (Fintype.card d : ℂ) = 4 * α ^ 2) :
    ((α • (t • a + t⁻¹ • b)) ᵥ* ZC
        - ((((α • (t • a + t⁻¹ • b)) ᵥ* ZC) ⬝ᵥ (α • (t • a + t⁻¹ • b)))
          / (Fintype.card d : ℂ)) • (α • (t • a + t⁻¹ • b))) ᵥ* WC
        + (α • (t • a + t⁻¹ • b)) ᵥ* EW
      = t ^ 3 • cCube_tps ZC WC a α + t • cPlus_tps ZC WC EW a b α
        + t⁻¹ • cPlus_tps ZC WC EW b a α + t⁻¹ ^ 3 • cCube_tps ZC WC b α := by
  simp only [cCube_tps, cPlus_tps]
  -- `⟨n Z, n⟩ = α² (t² q(a,a) + q(a,b) + q(b,a) + t⁻² q(b,b))`
  have hdot : ((α • (t • a + t⁻¹ • b)) ᵥ* ZC) ⬝ᵥ (α • (t • a + t⁻¹ • b))
      = α ^ 2 * (t ^ 2 * ((a ᵥ* ZC) ⬝ᵥ a) + ((a ᵥ* ZC) ⬝ᵥ b) + ((b ᵥ* ZC) ⬝ᵥ a)
        + t⁻¹ ^ 2 * ((b ᵥ* ZC) ⬝ᵥ b)) := by
    simp only [smul_vecMul, add_vecMul, smul_dotProduct, dotProduct_smul, add_dotProduct,
      dotProduct_add, smul_eq_mul]
    field_simp
    ring
  rw [hdot]
  simp only [vecMul_add, ← vecMul_vecMul, smul_vecMul, add_vecMul, sub_vecMul]
  funext j
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [hα]
  field_simp
  ring

omit [DecidableEq d] in
/-- Helper: the cast of `v M` for a real row `v` and a real matrix `M`. -/
private theorem vecMul_ofReal_tps {m : Type*} (v : d → ℝ) (M : Matrix d m ℝ) :
    (fun i => (v i : ℂ)) ᵥ* M.map (fun x : ℝ => (x : ℂ)) = fun j => ((v ᵥ* M) j : ℂ) := by
  funext j
  exact (RingHom.map_vecMul Complex.ofRealHom M v j).symm

omit [DecidableEq d] in
/-- Helper: `(ξ + μ ξ') M = ξM + μ ξ'M` for real `ξ, ξ', M`. -/
private theorem nu_vecMul_tps {m : Type*} (ξ ξ' : d → ℝ) (μ : ℂ) (M : Matrix d m ℝ) :
    (fun i => (ξ i : ℂ) + μ * (ξ' i : ℂ)) ᵥ* M.map (fun x : ℝ => (x : ℂ))
      = fun j => ((ξ ᵥ* M) j : ℂ) + μ * ((ξ' ᵥ* M) j : ℂ) := by
  have h : (fun i => (ξ i : ℂ) + μ * (ξ' i : ℂ))
      = (fun i => (ξ i : ℂ)) + μ • (fun i => (ξ' i : ℂ)) := by
    funext i; simp
  rw [h, add_vecMul, smul_vecMul, vecMul_ofReal_tps, vecMul_ofReal_tps]
  funext j
  simp

omit [DecidableEq d] in
/-- Helper: `⟨(ξ + μ ξ') Z, ξ + μ' ξ'⟩` in terms of the four real numbers `⟨xZ, y⟩`. -/
private theorem q_nu_tps (Z : Matrix d d ℝ) (ξ ξ' : d → ℝ) (μ μ' : ℂ) :
    ((fun i => (ξ i : ℂ) + μ * (ξ' i : ℂ)) ᵥ* Z.map (fun x : ℝ => (x : ℂ)))
        ⬝ᵥ (fun i => (ξ i : ℂ) + μ' * (ξ' i : ℂ))
      = (((ξ ᵥ* Z) ⬝ᵥ ξ : ℝ) : ℂ) + μ' * (((ξ ᵥ* Z) ⬝ᵥ ξ' : ℝ) : ℂ)
        + μ * (((ξ' ᵥ* Z) ⬝ᵥ ξ : ℝ) : ℂ) + μ * μ' * (((ξ' ᵥ* Z) ⬝ᵥ ξ' : ℝ) : ℂ) := by
  rw [nu_vecMul_tps]
  simp only [dotProduct, Complex.ofReal_sum, Complex.ofReal_mul, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the matrix product of two analytic matrix-valued maps is analytic. -/
private theorem analyticAt_matrix_mul_tps {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
    {f : E → Matrix m n ℂ} {g : E → Matrix n p ℂ} {x : E}
    (hf : AnalyticAt ℂ f x) (hg : AnalyticAt ℂ g x) :
    AnalyticAt ℂ (fun y => f y * g y) x := by
  -- matrix multiplication as a bilinear map
  let B : Matrix m n ℂ →ₗ[ℂ] Matrix n p ℂ →ₗ[ℂ] Matrix m p ℂ :=
    LinearMap.mk₂ ℂ (fun a b => a * b) Matrix.add_mul (fun c a b => Matrix.smul_mul c a b)
      Matrix.mul_add (fun c a b => Matrix.mul_smul a c b)
  -- the same map with continuous linear maps (all spaces are finite-dimensional)
  let B' : Matrix m n ℂ →L[ℂ] Matrix n p ℂ →L[ℂ] Matrix m p ℂ :=
    LinearMap.toContinuousLinearMap
      ((LinearMap.toContinuousLinearMap :
        (Matrix n p ℂ →ₗ[ℂ] Matrix m p ℂ) ≃ₗ[ℂ] (Matrix n p ℂ →L[ℂ] Matrix m p ℂ)).toLinearMap ∘ₗ B)
  have hB : (fun y => f y * g y) = fun y => B' (f y) (g y) := rfl
  rw [hB]
  exact (B'.analyticAt_bilinear (f x, g x)).comp₂ hf hg

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: `y ↦ (the matrix with the row f(y) at every token) * M` is analytic. -/
private theorem analyticAt_rows_mul_tps [Fintype T] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {m n : Type*} [Fintype m] [Fintype n] {f : E → m → ℂ} {x : E}
    (hf : ∀ j, AnalyticAt ℂ (fun y => f y j) x) (M : Matrix m n ℂ) :
    AnalyticAt ℂ (fun y => (Matrix.of fun (_ : T) j => f y j) * M) x := by
  have hF : AnalyticAt ℂ (fun y => (Matrix.of fun (_ : T) j => f y j : Matrix T m ℂ)) x := by
    show AnalyticAt ℂ (fun y => fun (_ : T) => fun j => f y j) x
    exact AnalyticAt.pi fun _ => AnalyticAt.pi fun j => hf j
  exact analyticAt_matrix_mul_tps hF analyticAt_const

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: `ζ ↦ w̃(ζ)_j` is holomorphic where `‖ζ_j‖ < 1`. -/
private theorem analyticAt_wt_tps {ι : Type*} [Fintype ι] (s : ι → ℝ) (ζ₀ : ι → ℂ) (j : ι)
    (h : ‖ζ₀ j‖ < 1) : AnalyticAt ℂ (fun ζ => wt_tps s ζ j) ζ₀ := by
  have hp : AnalyticAt ℂ (fun ζ : ι → ℂ => ζ j) ζ₀ :=
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι => ℂ) j).analyticAt _
  exact (analyticAt_const.mul (analyticAt_const.sub hp)).div (analyticAt_const.add hp)
    (one_add_ne_zero_tps h)

/-- The maps `𝒯_i` of the paper, for a row `c` (the coefficient of `t^i` in `ż`) and a number
`δ` (`1` for `i = 0`, else `0`): the derivative of the joint map `(ω, h) ↦ suffixC tanh ω k.succ h`
at `(θ, w̃(ζ)V)`, in the direction `(δ η, ((1 − w̃²) ⊙ c) V + δ w̃ η_V)`. -/
private noncomputable def bigT_tps
    (θ : Params (Arch.mlp (T := T) (d := d) Real.tanh (rmsNorm 0) hid) dIn dOut) (k : Fin L)
    (η : Params (Arch.mlp (T := T) (d := d) Real.tanh (rmsNorm 0) hid) dIn dOut)
    (s : hid k → ℝ) (c : hid k → ℂ) (δ : ℂ) (ζ : hid k → ℂ) : Matrix T dOut ℂ :=
  fderiv ℂ (fun p : CWeights d dOut hid × Matrix T d ℂ => suffixC Complex.tanh p.1 k.succ p.2)
    (θ.toC, (Matrix.of fun (_ : T) j => wt_tps s ζ j) * θ.toC.2.1 k)
    (δ • η.toC, (Matrix.of fun (_ : T) j => (1 - wt_tps s ζ j ^ 2) * c j) * θ.toC.2.1 k
      + δ • ((Matrix.of fun (_ : T) j => wt_tps s ζ j) * η.toC.2.1 k))

omit [Fintype T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Step 1: for `ζ` in the polydisc, every row of `w̃(ζ) V` is in the cone. -/
private theorem rows_mem_cone_tps
    (θ : Params (Arch.mlp (T := T) (d := d) Real.tanh (rmsNorm 0) hid) dIn dOut) (k : Fin L)
    (s : hid k → ℝ) (hs : ∀ j, s j = 1 ∨ s j = -1) {ρ κ : ℝ} (hρ1 : ρ ≤ 1)
    (hcone : ∀ w : hid k → ℂ, (∀ j, ‖w j - (s j : ℂ)‖ ≤ ρ) →
      w ᵥ* θ.toC.2.1 k ∈ complexCone κ)
    (ζ : hid k → ℂ) (hζ : ∀ j, ‖ζ j‖ < ρ / 3) (τ : T) :
    ((Matrix.of fun (_ : T) j => wt_tps s ζ j) * θ.toC.2.1 k) τ ∈ complexCone κ := by
  refine hcone (wt_tps s ζ) fun j => ?_
  have h1 := norm_wt_sub_tps (s j) (hs j) (ζ j) (by linarith [hζ j])
  have h2 := hζ j
  simp only [wt_tps]
  linarith

omit [DecidableEq d] [Fintype dIn] in
/-- Step 3: every `𝒯_i` is holomorphic on the polydisc `D = {‖ζ_j‖ < ρ/3}`. -/
private theorem analyticOnNhd_bigT_tps
    (θ : Params (Arch.mlp (T := T) (d := d) Real.tanh (rmsNorm 0) hid) dIn dOut) (k : Fin L)
    {κ : ℝ} (hhol : HolomorphicOnCone Complex.tanh θ k.succ κ)
    (η : Params (Arch.mlp (T := T) (d := d) Real.tanh (rmsNorm 0) hid) dIn dOut)
    (s : hid k → ℝ) (hs : ∀ j, s j = 1 ∨ s j = -1) {ρ : ℝ} (hρ1 : ρ ≤ 1)
    (hcone : ∀ w : hid k → ℂ, (∀ j, ‖w j - (s j : ℂ)‖ ≤ ρ) →
      w ᵥ* θ.toC.2.1 k ∈ complexCone κ) (c : hid k → ℂ) (δ : ℂ) :
    AnalyticOnNhd ℂ (bigT_tps θ k η s c δ) {ζ | ∀ j, ‖ζ j‖ < ρ / 3} := by
  intro ζ₀ hζ₀
  have hζ1 : ∀ j, ‖ζ₀ j‖ < 1 := fun j => by have := hζ₀ j; linarith
  have hw : ∀ j, AnalyticAt ℂ (fun ζ => wt_tps s ζ j) ζ₀ :=
    fun j => analyticAt_wt_tps s ζ₀ j (hζ1 j)
  -- the joint map is holomorphic at `(θ, w̃(ζ₀) V)`, so is its derivative
  have hA := (hhol _ (rows_mem_cone_tps θ k s hs hρ1 hcone ζ₀ hζ₀)).fderiv
  have hH : AnalyticAt ℂ (fun ζ => (Matrix.of fun (_ : T) j => wt_tps s ζ j) * θ.toC.2.1 k) ζ₀ :=
    analyticAt_rows_mul_tps hw _
  have hP : AnalyticAt ℂ
      (fun ζ => (θ.toC, (Matrix.of fun (_ : T) j => wt_tps s ζ j) * θ.toC.2.1 k)) ζ₀ :=
    analyticAt_const.prod hH
  have hAP := AnalyticAt.comp
    (f := fun ζ => (θ.toC, (Matrix.of fun (_ : T) j => wt_tps s ζ j) * θ.toC.2.1 k)) hA hP
  -- the direction is holomorphic in `ζ`
  have hX1 : AnalyticAt ℂ
      (fun ζ => (Matrix.of fun (_ : T) j => (1 - wt_tps s ζ j ^ 2) * c j) * θ.toC.2.1 k) ζ₀ :=
    analyticAt_rows_mul_tps
      (fun j => ((analyticAt_const.sub ((hw j).pow 2)).mul analyticAt_const)) _
  have hX2 : AnalyticAt ℂ
      (fun ζ => δ • ((Matrix.of fun (_ : T) j => wt_tps s ζ j) * η.toC.2.1 k)) ζ₀ :=
    (analyticAt_rows_mul_tps hw _).fun_const_smul
  have hE : AnalyticAt ℂ (fun ζ => (δ • η.toC,
      (Matrix.of fun (_ : T) j => (1 - wt_tps s ζ j ^ 2) * c j) * θ.toC.2.1 k
        + δ • ((Matrix.of fun (_ : T) j => wt_tps s ζ j) * η.toC.2.1 k))) ζ₀ :=
    analyticAt_const.prod (hX1.add hX2)
  have hc := (ContinuousLinearMap.id ℂ _).analyticAt_bilinear _ |>.comp₂ hAP hE
  exact hc

omit [DecidableEq d] in
/-- Helper (chain rule): the derivative in the hidden state is the joint derivative at `(0, v)`. -/
private theorem fderiv_right_tps (ω : CWeights d dOut hid) (k : Fin (L + 1)) (h v : Matrix T d ℂ)
    (hdiff : DifferentiableAt ℂ
      (fun p : CWeights d dOut hid × Matrix T d ℂ => suffixC Complex.tanh p.1 k p.2) (ω, h)) :
    fderiv ℂ (fun h' : Matrix T d ℂ => suffixC Complex.tanh ω k h') h v
      = fderiv ℂ (fun p : CWeights d dOut hid × Matrix T d ℂ => suffixC Complex.tanh p.1 k p.2)
          (ω, h) (0, v) := by
  have h1 := (hdiff.hasFDerivAt.comp h (hasFDerivAt_prodMk_right ω h)).fderiv
  exact DFunLike.congr_fun h1 v

omit [DecidableEq d] in
/-- Helper (chain rule): the derivative in the weights is the joint derivative at `(η, 0)`. -/
private theorem fderiv_left_tps (ω η : CWeights d dOut hid) (k : Fin (L + 1)) (h : Matrix T d ℂ)
    (hdiff : DifferentiableAt ℂ
      (fun p : CWeights d dOut hid × Matrix T d ℂ => suffixC Complex.tanh p.1 k p.2) (ω, h)) :
    fderiv ℂ (fun ω' : CWeights d dOut hid => suffixC Complex.tanh ω' k h) ω η
      = fderiv ℂ (fun p : CWeights d dOut hid × Matrix T d ℂ => suffixC Complex.tanh p.1 k p.2)
          (ω, h) (η, 0) := by
  have h1 := (hdiff.hasFDerivAt.comp ω (hasFDerivAt_prodMk_left (𝕜 := ℂ) ω h)).fderiv
  exact DFunLike.congr_fun h1 η

omit [DecidableEq d] [Fintype dIn] in
/-- Helper: `𝓛 = 𝐃(ω, h)𝓑 (η, (w' ⊙ ż) V + w η_V)`, with the joint derivative. -/
private theorem blockLHSC_eq_tps
    (θ : Params (Arch.mlp (T := T) (d := d) Real.tanh (rmsNorm 0) hid) dIn dOut) (k : Fin L)
    (η : Params (Arch.mlp (T := T) (d := d) Real.tanh (rmsNorm 0) hid) dIn dOut)
    (w w' zdot : Matrix T (hid k) ℂ)
    (hdiff : DifferentiableAt ℂ
      (fun p : CWeights d dOut hid × Matrix T d ℂ => suffixC Complex.tanh p.1 k.succ p.2)
      (θ.toC, w * θ.toC.2.1 k)) :
    blockLHSC Complex.tanh θ k η w w' zdot
      = fderiv ℂ (fun p : CWeights d dOut hid × Matrix T d ℂ => suffixC Complex.tanh p.1 k.succ p.2)
          (θ.toC, w * θ.toC.2.1 k)
          (η.toC, (Matrix.of fun t j => w' t j * zdot t j) * θ.toC.2.1 k + w * η.toC.2.1 k) := by
  unfold blockLHSC
  rw [fderiv_right_tps _ _ _ _ hdiff, fderiv_left_tps _ _ _ _ hdiff, ← map_add]
  congr 1
  simp

omit [Fintype T] [DecidableEq d] in
/-- Step 1: the hidden units on the path,
`z_j(t) = √d ((t + t⁻¹)/2 ξc_j + i (t − t⁻¹)/2 ξ'c_j)`. -/
private theorem path_entry_tps {m : Type*} (ξ ξ' : d → ℝ) (W : Matrix d m ℝ) (t : ℝ) (τ : T)
    (j : m) :
    (pathMatrix (Matrix.of fun (_ : T) => ξ) (Matrix.of fun (_ : T) => ξ') (t : ℂ)
        * W.map (fun x : ℝ => (x : ℂ))) τ j
      = ((Real.sqrt (Fintype.card d) * ((t + t⁻¹) / 2 * (ξ ᵥ* W) j) : ℝ) : ℂ)
        + Complex.I * ((Real.sqrt (Fintype.card d) * ((t - t⁻¹) / 2 * (ξ' ᵥ* W) j) : ℝ) : ℂ) := by
  rw [Matrix.mul_apply]
  simp only [pathMatrix, Matrix.of_apply, pathRow_ofReal, Matrix.map_apply, vecMul, dotProduct]
  push_cast
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- Step 1: `ζ_j(t) = exp(−2 s_j z_j(t))`. -/
private theorem exp_path_tps (sd t x x' s : ℝ) (habs : |x| = s * x) :
    Complex.exp (-2 * (s : ℂ) * (((sd * ((t + t⁻¹) / 2 * x) : ℝ) : ℂ)
        + Complex.I * ((sd * ((t - t⁻¹) / 2 * x') : ℝ) : ℂ)))
      = Complex.exp (-(((t + t⁻¹) * (sd * |x|) : ℝ) : ℂ)
        - Complex.I * (((t - t⁻¹) * (sd * s * x') : ℝ) : ℂ)) := by
  congr 1
  rw [habs]
  push_cast
  ring

/-- Step 1: `‖ζ_j(t)‖ = exp(−(t + t⁻¹) u_j) ≤ exp(−2 u_j)` for `t ≥ 1`. -/
private theorem norm_zeta_tps (t u u' : ℝ) (ht : 1 ≤ t) (hu : 0 < u) :
    ‖Complex.exp (-(((t + t⁻¹) * u : ℝ) : ℂ) - Complex.I * (((t - t⁻¹) * u' : ℝ) : ℂ))‖
      ≤ Real.exp (-(2 * u)) := by
  rw [Complex.norm_exp]
  have hre : (-(((t + t⁻¹) * u : ℝ) : ℂ) - Complex.I * (((t - t⁻¹) * u' : ℝ) : ℂ)).re
      = -((t + t⁻¹) * u) := by simp
  rw [hre, Real.exp_le_exp]
  have ht0 : 0 < t := by linarith
  have h2 : 2 ≤ t + t⁻¹ := by
    have : t + t⁻¹ - 2 = (t - 1) ^ 2 / t := by field_simp; ring
    have : 0 ≤ (t - 1) ^ 2 / t := by positivity
    linarith
  nlinarith

/-- Helper: the sum of `path_separation` for `K = 3`, term by term. -/
private theorem sum_seven_tps {M : Type*} [AddCommMonoid M] [Module ℂ M] (t : ℂ) (f : Fin 7 → M) :
    ∑ i : Fin (2 * 3 + 1), t ^ (((i : ℕ) : ℤ) - ((3 : ℕ) : ℤ)) • f i
      = t⁻¹ ^ 3 • f 0 + t⁻¹ ^ 2 • f 1 + t⁻¹ • f 2 + f 3 + t • f 4 + t ^ 2 • f 5 + t ^ 3 • f 6 := by
  rw [Fin.sum_univ_seven]
  norm_num [_root_.zpow_neg, inv_pow]


omit [Fintype T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Step 1 on the path, at one real `t ≥ 1`: with `ζ_j(t) = exp(−(t + t⁻¹) u_j − i (t − t⁻¹) u'_j)`,
`‖ζ_j(t)‖ < ρ/3`, `tanh` is holomorphic at every hidden unit `z_j(t)`, and
`tanh(z_j(t)) = w̃(ζ(t))_j`, `tanh'(z_j(t)) = 1 − w̃(ζ(t))_j²`. -/
private theorem path_facts_tps
    (θ : Params (Arch.mlp (T := T) (d := d) Real.tanh (rmsNorm 0) hid) dIn dOut) (k : Fin L)
    (s : hid k → ℝ) (hs : ∀ j, s j = 1 ∨ s j = -1) {ρ : ℝ} (hρ1 : ρ ≤ 1) (ξ ξ' : d → ℝ)
    (hsd : 0 < Real.sqrt (Fintype.card d))
    (hsign : ∀ j : hid k, 0 < s j * (ξ ᵥ* θ.read k) j)
    (hdecay : ∀ j : hid k,
      Real.exp (-(2 * (Real.sqrt (Fintype.card d) * |(ξ ᵥ* θ.read k) j|))) < ρ / 3)
    (t : ℝ) (ht : 1 ≤ t) (ζ : hid k → ℂ)
    (hζ : ζ = fun j => Complex.exp
      (-(((t + t⁻¹) * (Real.sqrt (Fintype.card d) * |(ξ ᵥ* θ.read k) j|) : ℝ) : ℂ)
        - Complex.I * (((t - t⁻¹) * (Real.sqrt (Fintype.card d) * s j * (ξ' ᵥ* θ.read k) j) : ℝ)
          : ℂ))) :
    (∀ j, ‖ζ j‖ < ρ / 3) ∧
    (∀ τ j, AnalyticAt ℂ Complex.tanh
      ((pathMatrix (Matrix.of fun (_ : T) => ξ) (Matrix.of fun (_ : T) => ξ') (t : ℂ)
        * θ.toC.1 k) τ j)) ∧
    (pathMatrix (Matrix.of fun (_ : T) => ξ) (Matrix.of fun (_ : T) => ξ') (t : ℂ)
        * θ.toC.1 k).map Complex.tanh = (Matrix.of fun (_ : T) j => wt_tps s ζ j) ∧
    (pathMatrix (Matrix.of fun (_ : T) => ξ) (Matrix.of fun (_ : T) => ξ') (t : ℂ)
        * θ.toC.1 k).map (deriv Complex.tanh)
      = (Matrix.of fun (_ : T) j => 1 - wt_tps s ζ j ^ 2) := by
  -- `|ξc_j| = s_j ξc_j` and `u_j = √d |ξc_j| > 0`
  have habs : ∀ j, |(ξ ᵥ* θ.read k) j| = s j * (ξ ᵥ* θ.read k) j := by
    intro j
    have h := hsign j
    rcases hs j with h1 | h1 <;> rw [h1] at h ⊢
    · rw [one_mul] at h ⊢; exact abs_of_pos h
    · rw [abs_of_neg (by linarith)]; ring
  have hu : ∀ j, 0 < Real.sqrt (Fintype.card d) * |(ξ ᵥ* θ.read k) j| := by
    intro j
    refine mul_pos hsd (abs_pos.2 fun h0 => ?_)
    have := hsign j
    rw [h0, mul_zero] at this
    exact lt_irrefl _ this
  have hn : ∀ j, ‖ζ j‖ < ρ / 3 := fun j => by
    rw [hζ]; exact (norm_zeta_tps t _ _ ht (hu j)).trans_lt (hdecay j)
  -- the hidden units `z_j(t)` on the path
  obtain ⟨z, hz⟩ : ∃ z : hid k → ℂ, ∀ j, z j
      = ((Real.sqrt (Fintype.card d) * ((t + t⁻¹) / 2 * (ξ ᵥ* θ.read k) j) : ℝ) : ℂ)
        + Complex.I * ((Real.sqrt (Fintype.card d) * ((t - t⁻¹) / 2 * (ξ' ᵥ* θ.read k) j) : ℝ)
          : ℂ) := ⟨_, fun j => rfl⟩
  have hent : ∀ τ j, (pathMatrix (Matrix.of fun (_ : T) => ξ) (Matrix.of fun (_ : T) => ξ')
      (t : ℂ) * θ.toC.1 k) τ j = z j := by
    intro τ j; rw [hz]; exact path_entry_tps ξ ξ' (θ.read k) t τ j
  -- `ζ_j(t) = exp(−2 s_j z_j(t))`, so `tanh(z_j(t)) = s_j (1 − ζ_j)/(1 + ζ_j)`
  have hexp : ∀ j, Complex.exp (-2 * (s j : ℂ) * z j) = ζ j := fun j => by
    rw [hζ, hz]; exact exp_path_tps _ _ _ _ _ (habs j)
  have htanh : ∀ j, Complex.cosh (z j) ≠ 0 ∧ Complex.tanh (z j) = wt_tps s ζ j := fun j => by
    have h1 : ‖Complex.exp (-2 * (s j : ℂ) * z j)‖ < 1 := by rw [hexp]; linarith [hn j]
    obtain ⟨hc, ht'⟩ := tanh_eq_tps (z j) (s j) (hs j) h1
    refine ⟨hc, ?_⟩
    rw [ht', hexp]
    rfl
  refine ⟨hn, fun τ j => ?_, ?_, ?_⟩
  · rw [hent]; exact analyticAt_ctanh_tps (htanh j).1
  · ext τ j; rw [Matrix.map_apply, hent, (htanh j).2]; rfl
  · ext τ j
    rw [Matrix.map_apply, hent, (hasDerivAt_ctanh_tps (htanh j).1).deriv, (htanh j).2]
    rfl

omit [Fintype T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Step 2: every row of `ż(n(t))` is `t³ c₃ + t c₁ + t⁻¹ c₋₁ + t⁻³ c₋₃`. -/
private theorem zdotC_path_tps
    (θ : Params (Arch.mlp (T := T) (d := d) Real.tanh (rmsNorm 0) hid) dIn dOut) (k : Fin L)
    (Z : Matrix d d ℝ)
    (η : Params (Arch.mlp (T := T) (d := d) Real.tanh (rmsNorm 0) hid) dIn dOut)
    (ξ ξ' : d → ℝ) (hd0 : 0 < Fintype.card d) (t : ℂ) (ht : t ≠ 0) (τ : T) :
    zdotC θ k Z η (pathMatrix (Matrix.of fun (_ : T) => ξ) (Matrix.of fun (_ : T) => ξ') t) τ
      = t ^ 3 • cCube_tps (Z.map (fun x : ℝ => (x : ℂ))) (θ.toC.1 k)
          (fun i => (ξ i : ℂ) + Complex.I * (ξ' i : ℂ)) (((Real.sqrt (Fintype.card d) : ℝ) : ℂ) / 2)
        + t • cPlus_tps (Z.map (fun x : ℝ => (x : ℂ))) (θ.toC.1 k) (η.toC.1 k)
          (fun i => (ξ i : ℂ) + Complex.I * (ξ' i : ℂ))
          (fun i => (ξ i : ℂ) + (-Complex.I) * (ξ' i : ℂ))
          (((Real.sqrt (Fintype.card d) : ℝ) : ℂ) / 2)
        + t⁻¹ • cPlus_tps (Z.map (fun x : ℝ => (x : ℂ))) (θ.toC.1 k) (η.toC.1 k)
          (fun i => (ξ i : ℂ) + (-Complex.I) * (ξ' i : ℂ))
          (fun i => (ξ i : ℂ) + Complex.I * (ξ' i : ℂ)) (((Real.sqrt (Fintype.card d) : ℝ) : ℂ) / 2)
        + t⁻¹ ^ 3 • cCube_tps (Z.map (fun x : ℝ => (x : ℂ))) (θ.toC.1 k)
          (fun i => (ξ i : ℂ) + (-Complex.I) * (ξ' i : ℂ))
          (((Real.sqrt (Fintype.card d) : ℝ) : ℂ) / 2) := by
  -- the row of the path is `α (t ν + t⁻¹ ν̄)` with `α = √d/2`
  have hrow : pathMatrix (Matrix.of fun (_ : T) => ξ) (Matrix.of fun (_ : T) => ξ') t τ
      = (((Real.sqrt (Fintype.card d) : ℝ) : ℂ) / 2)
        • (t • (fun i => (ξ i : ℂ) + Complex.I * (ξ' i : ℂ))
        + t⁻¹ • (fun i => (ξ i : ℂ) + (-Complex.I) * (ξ' i : ℂ))) := by
    funext i
    simp only [pathMatrix, Matrix.of_apply, pathRow, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    ring
  have hsd : (0 : ℝ) < Real.sqrt (Fintype.card d) := Real.sqrt_pos.2 (by exact_mod_cast hd0)
  have hα0 : (((Real.sqrt (Fintype.card d) : ℝ) : ℂ) / 2) ≠ 0 := by
    have : ((Real.sqrt (Fintype.card d) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hsd.ne'
    exact div_ne_zero this two_ne_zero
  have hα : (Fintype.card d : ℂ) = 4 * (((Real.sqrt (Fintype.card d) : ℝ) : ℂ) / 2) ^ 2 := by
    have h2 : ((Real.sqrt (Fintype.card d) : ℝ) : ℂ) ^ 2 = (Fintype.card d : ℂ) := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]; push_cast; rfl
    rw [div_pow, h2]; ring
  -- `ż_τ = (n Z − (⟨nZ, n⟩/d) n) W + n η_W` with `n = n(t)`
  have e : zdotC θ k Z η (pathMatrix (Matrix.of fun (_ : T) => ξ) (Matrix.of fun (_ : T) => ξ') t) τ
      = ((pathMatrix (Matrix.of fun (_ : T) => ξ) (Matrix.of fun (_ : T) => ξ') t τ)
            ᵥ* Z.map (fun x : ℝ => (x : ℂ))
          - ((((pathMatrix (Matrix.of fun (_ : T) => ξ) (Matrix.of fun (_ : T) => ξ') t τ)
            ᵥ* Z.map (fun x : ℝ => (x : ℂ)))
            ⬝ᵥ (pathMatrix (Matrix.of fun (_ : T) => ξ) (Matrix.of fun (_ : T) => ξ') t τ))
              / (Fintype.card d : ℂ))
            • (pathMatrix (Matrix.of fun (_ : T) => ξ) (Matrix.of fun (_ : T) => ξ') t τ))
          ᵥ* θ.toC.1 k
        + (pathMatrix (Matrix.of fun (_ : T) => ξ) (Matrix.of fun (_ : T) => ξ') t τ)
          ᵥ* η.toC.1 k := rfl
  rw [e, hrow]
  exact zdot_row_tps _ _ _ _ _ _ t ht hα0 hα


/-- Steps 1 and 2: the identity (42) of Lemma D.15 on the path is `∑_i t^i 𝒯_i(ζ(t)) = 0`, in the
form of `path_separation` with `K = 3`. -/
private theorem path_sum_tps [Nonempty d] [Nonempty T]
    (θ : Params (Arch.mlp (T := T) (d := d) Real.tanh (rmsNorm 0) hid) dIn dOut)
    (hθ : RegularZero (Arch.mlp Real.tanh (rmsNorm 0) hid) θ) (k : Fin L)
    {κ : ℝ} (hκ : 0 < κ) (hhol : HolomorphicOnCone Complex.tanh θ k.succ κ)
    (s : hid k → ℝ) (hs : ∀ j, s j = 1 ∨ s j = -1) {ρ : ℝ} (hρ1 : ρ ≤ 1)
    (hcone : ∀ w : hid k → ℂ, (∀ j, ‖w j - (s j : ℂ)‖ ≤ ρ) →
      w ᵥ* θ.toC.2.1 k ∈ complexCone κ)
    (Z : Matrix d d ℝ)
    (η : Params (Arch.mlp (T := T) (d := d) Real.tanh (rmsNorm 0) hid) dIn dOut)
    (h16 : SuffixFlatZero (Arch.mlp Real.tanh (rmsNorm 0) hid) θ k.castSucc Z η)
    (ξ ξ' : d → ℝ) (hξ : ξ ⬝ᵥ ξ = 1) (hξ' : ξ' ⬝ᵥ ξ' = 1) (hξξ' : ξ ⬝ᵥ ξ' = 0)
    (hsd : 0 < Real.sqrt (Fintype.card d))
    (hsign : ∀ j : hid k, 0 < s j * (ξ ᵥ* θ.read k) j)
    (hdecay : ∀ j : hid k,
      Real.exp (-(2 * (Real.sqrt (Fintype.card d) * |(ξ ᵥ* θ.read k) j|))) < ρ / 3)
    (c3 c1 cm1 cm3 : hid k → ℂ)
    (hz : ∀ t : ℝ, 1 ≤ t → ∀ τ j, zdotC θ k Z η (pathMatrix (Matrix.of fun (_ : T) => ξ)
      (Matrix.of fun (_ : T) => ξ') (t : ℂ)) τ j
        = (t : ℂ) ^ 3 * c3 j + (t : ℂ) * c1 j + (t : ℂ)⁻¹ * cm1 j + (t : ℂ)⁻¹ ^ 3 * cm3 j)
    (t : ℝ) (ht : 1 ≤ t) :
    ∑ i : Fin (2 * 3 + 1), (t : ℂ) ^ (((i : ℕ) : ℤ) - ((3 : ℕ) : ℤ)) •
      bigT_tps θ k η s (![cm3, 0, cm1, 0, c1, 0, c3] i) (![0, 0, 0, 1, 0, 0, 0] i)
        (fun j => Complex.exp
          (-(((t + t⁻¹) * (Real.sqrt (Fintype.card d) * |(ξ ᵥ* θ.read k) j|) : ℝ) : ℂ)
            - Complex.I * (((t - t⁻¹) * (Real.sqrt (Fintype.card d) * s j * (ξ' ᵥ* θ.read k) j)
              : ℝ) : ℂ))) = 0 := by
  obtain ⟨ζ, hζ⟩ : ∃ ζ : hid k → ℂ, ζ = fun j => Complex.exp
      (-(((t + t⁻¹) * (Real.sqrt (Fintype.card d) * |(ξ ᵥ* θ.read k) j|) : ℝ) : ℂ)
        - Complex.I * (((t - t⁻¹) * (Real.sqrt (Fintype.card d) * s j * (ξ' ᵥ* θ.read k) j) : ℝ)
          : ℂ)) := ⟨_, rfl⟩
  rw [← hζ]
  obtain ⟨hn, -, hw, hw'⟩ := path_facts_tps θ k s hs hρ1 ξ ξ' hsd hsign hdecay t ht ζ hζ
  -- the hypothesis of Lemma D.15, for every `t' ≥ 1`
  have hpath : ∀ t' : ℝ, 1 ≤ t' →
      (∀ τ j, AnalyticAt ℂ Complex.tanh ((pathMatrix (Matrix.of fun (_ : T) => ξ)
        (Matrix.of fun (_ : T) => ξ') (t' : ℂ) * θ.toC.1 k) τ j)) ∧
      ∀ τ, ((pathMatrix (Matrix.of fun (_ : T) => ξ) (Matrix.of fun (_ : T) => ξ') (t' : ℂ)
        * θ.toC.1 k).map Complex.tanh * θ.toC.2.1 k) τ ∈ complexCone κ := by
    intro t' ht'
    obtain ⟨hn', han', hw2, -⟩ := path_facts_tps θ k s hs hρ1 ξ ξ' hsd hsign hdecay t' ht' _ rfl
    refine ⟨han', fun τ => ?_⟩
    rw [hw2]
    exact rows_mem_cone_tps θ k s hs hρ1 hcone _ hn' τ
  have hσC : ∀ x : ℝ, AnalyticAt ℂ Complex.tanh (x : ℂ) := fun x => by
    refine analyticAt_ctanh_tps ?_
    rw [← Complex.ofReal_cosh]
    exact_mod_cast (Real.cosh_pos x).ne'
  -- (42)
  have h42 := blockLHSC_pathMatrix_eq_zero (σ' := fun z => 1 - Real.tanh z ^ 2) hasDerivAt_tanh
    analyticOnNhd_tanh (fun x => (Complex.ofReal_tanh x).symm) hσC θ hθ k hκ hhol Z η h16
    (Matrix.of fun (_ : T) => ξ) (Matrix.of fun (_ : T) => ξ')
    (fun _ => hξ) (fun _ => hξ') (fun _ => hξξ') hpath t ht
  rw [hw, hw', blockLHSC_eq_tps θ k η _ _ _
    (hhol _ (rows_mem_cone_tps θ k s hs hρ1 hcone ζ hn)).differentiableAt] at h42
  -- the seven terms
  refine (sum_seven_tps (t : ℂ) _).trans ?_
  show (t : ℂ)⁻¹ ^ 3 • bigT_tps θ k η s cm3 0 ζ + (t : ℂ)⁻¹ ^ 2 • bigT_tps θ k η s 0 0 ζ
      + (t : ℂ)⁻¹ • bigT_tps θ k η s cm1 0 ζ + bigT_tps θ k η s 0 1 ζ
      + (t : ℂ) • bigT_tps θ k η s c1 0 ζ + (t : ℂ) ^ 2 • bigT_tps θ k η s 0 0 ζ
      + (t : ℂ) ^ 3 • bigT_tps θ k η s c3 0 ζ = 0
  rw [← h42]
  unfold bigT_tps
  simp only [← map_smul, ← map_add]
  congr 1
  -- the directions agree: `∑_i t^i (1 − w̃²) ⊙ c_i = (1 − w̃²) ⊙ ż` row by row
  simp only [Prod.smul_mk, Prod.mk_add_mk, zero_smul, one_smul, smul_zero, zero_add, add_zero,
    Prod.mk.injEq]
  refine ⟨trivial, ?_⟩
  ext τ l
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply, Matrix.of_apply, smul_eq_mul,
    Pi.zero_apply, mul_zero, zero_mul, Finset.sum_const_zero, hz t ht, Finset.mul_sum,
    add_zero, zero_add, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- **Proof of Lemma D.18, the path and the powers of `t`, for one pair `ξ, ξ'`.** Let `σ = tanh`,
in the case (0), `d ≥ 2`, `θ` regular with (S1) for block `k`, `𝓑_{>k+1}` holomorphic on `C_κ`, and
let the identity (16) hold before block `k` for `Z` and `η`. Let `s_j = ±1` and `ρ ∈ (0, 1]` be such
that the rows `w̃V` with `|w̃_j − s_j| ≤ ρ` lie in `C_κ`. Let `ξ, ξ'` be orthonormal rows such that
`ξc_j` has the sign `s_j`, `e^{−2√d |ξc_j|} < ρ/3`, and `ξc_1, …, ξc_q` are linearly independent
over `ℚ`. Then:

* `ξZξ'ᵀ + ξ'Zξᵀ = 0` and `ξZξᵀ = ξ'Zξ'ᵀ` (this is `⟨νZ, ν⟩ = 0`, from `𝒯_3 = 0`);
* `ξ (ZW + η_W) = (ξZξᵀ) ξW` and `ξ' (ZW + η_W) = (ξZξᵀ) ξ'W` (this is `ż⁽¹⁾ = 0`, from
  `𝒯_1 = 0`);
* `𝐃𝓑(w̃V)(w̃ η_V) + 𝐃_θ𝓑(w̃V) η = 0` for every real row `w̃` with `|w̃_j − s_j| < ρ/4` (from
  `𝒯_0 = 0`), at the hidden state with the row `w̃V` at every token. -/
theorem tanh_path_step [Nonempty T]
    (θ : Params (Arch.mlp (T := T) (d := d) Real.tanh (rmsNorm 0) hid) dIn dOut)
    (hθ : RegularZero (Arch.mlp Real.tanh (rmsNorm 0) hid) θ) (hd : 2 ≤ Fintype.card d)
    (k : Fin L)
    (hS1 : ∀ i j : hid k, i ≠ j → ∀ a c : ℝ, a • θ.write k i + c • θ.write k j = 0 →
      a = 0 ∧ c = 0)
    {κ : ℝ} (hκ : 0 < κ) (hhol : HolomorphicOnCone Complex.tanh θ k.succ κ)
    (s : hid k → ℝ) (hs : ∀ j, s j = 1 ∨ s j = -1) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hcone : ∀ w : hid k → ℂ, (∀ j, ‖w j - (s j : ℂ)‖ ≤ ρ) →
      w ᵥ* θ.toC.2.1 k ∈ complexCone κ)
    (Z : Matrix d d ℝ)
    (η : Params (Arch.mlp (T := T) (d := d) Real.tanh (rmsNorm 0) hid) dIn dOut)
    (h16 : SuffixFlatZero (Arch.mlp Real.tanh (rmsNorm 0) hid) θ k.castSucc Z η)
    (ξ ξ' : d → ℝ) (hξ : ξ ⬝ᵥ ξ = 1) (hξ' : ξ' ⬝ᵥ ξ' = 1) (hξξ' : ξ ⬝ᵥ ξ' = 0)
    (hsign : ∀ j : hid k, 0 < s j * (ξ ᵥ* θ.read k) j)
    (hdecay : ∀ j : hid k,
      Real.exp (-(2 * (Real.sqrt (Fintype.card d) * |(ξ ᵥ* θ.read k) j|))) < ρ / 3)
    (hind : LinearIndependent ℚ (fun j : hid k => (ξ ᵥ* θ.read k) j)) :
    ((ξ ᵥ* Z) ⬝ᵥ ξ' + (ξ' ᵥ* Z) ⬝ᵥ ξ = 0 ∧ (ξ ᵥ* Z) ⬝ᵥ ξ = (ξ' ᵥ* Z) ⬝ᵥ ξ') ∧
    (ξ ᵥ* (Z * θ.read k + η.read k) = ((ξ ᵥ* Z) ⬝ᵥ ξ) • (ξ ᵥ* θ.read k) ∧
      ξ' ᵥ* (Z * θ.read k + η.read k) = ((ξ ᵥ* Z) ⬝ᵥ ξ) • (ξ' ᵥ* θ.read k)) ∧
    ∀ r : hid k → ℝ, (∀ j, |r j - s j| < ρ / 4) →
      fderiv ℝ
          (fun h' : Matrix T d ℝ => suffix (Arch.mlp Real.tanh (rmsNorm 0) hid) 0 θ k.succ h')
          ((Matrix.of fun (_ : T) => r) * θ.write k) ((Matrix.of fun (_ : T) => r) * η.write k)
        + fderiv ℝ
            (fun θ' : Params (Arch.mlp (T := T) (d := d) Real.tanh (rmsNorm 0) hid) dIn dOut =>
              suffix (Arch.mlp Real.tanh (rmsNorm 0) hid) 0 θ' k.succ
                ((Matrix.of fun (_ : T) => r) * θ.write k)) θ η = 0 := by
  sorry

end Skips
