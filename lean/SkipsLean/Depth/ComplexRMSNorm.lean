import SkipsLean.Depth.SuffixZero

/-!
# RMSNorm at complex rows, complex cones, and the great circle at complex angles

Paper (dimension paper): Appendix D.6 (the case `ε = 0`), "RMSNorm at complex rows" and "The path".

"For `h ∈ ℂ^{1 × d}` with `Re⟨h, h⟩ > 0` let `N(h) = √d h / √⟨h, h⟩`, with the principal square
root. It is holomorphic, `N(λh) = N(h)` for `λ > 0`, and

  `⟨n, n⟩ = d ⟹ N(n) = n, 𝐃N(n) v = v − (⟨v, n⟩/d) n`.   (40)

For `κ ∈ (0, 1]` let `C_κ = {u + iu' : u, u' ∈ ℝ^{1 × d}, ‖u'‖ < κ‖u‖}`, an open cone in
`ℂ^{1 × d}` that contains every real row `h ≠ 0`. On `C_1`, `Re⟨h, h⟩ = ‖u‖² − ‖u'‖² > 0`."

"For orthonormal rows `ξ, ξ' ∈ ℝ^{1 × d}` let `ν = ξ + iξ'`, `ν̄ = ξ − iξ'` and
`n(t) = (√d/2)(t ν + ν̄/t)`, `t ∈ ℂ ∖ {0}`. As `⟨ν, ν⟩ = ⟨ν̄, ν̄⟩ = 0` and `⟨ν, ν̄⟩ = 2`, we have
`⟨n(t), n(t)⟩ = d` for all `t`. For `|t| = 1` the row `n(t)` is real and runs through the great
circle of `ξ` and `ξ'` in `S`, with `n(1) = √d ξ`. For real `t ≥ 1`,

  `n(t) = √d ((t + t⁻¹)/2 ξ + i (t − t⁻¹)/2 ξ')`.   (41)"

Here `⟨u, v⟩ = u vᵀ` without complex conjugation is `u ⬝ᵥ v`; the norms of real rows in the cone are
Euclidean, written with `⬝ᵥ`; and `1/√z` is `exp(−(log z)/2)` with the principal logarithm.
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise

variable {T d : Type*} [Fintype T] [Fintype d]

/-- RMSNorm with `ε = 0` at a complex row: `N(h) = √d h / √⟨h, h⟩`, with the principal square
root, written as `exp(−log(⟨h, h⟩/d)/2) • h`. -/
noncomputable def rmsRowC (v : d → ℂ) : d → ℂ :=
  Complex.exp (-(Complex.log ((v ⬝ᵥ v) / (Fintype.card d : ℂ)) / 2)) • v

/-- RMSNorm with `ε = 0` at a complex hidden state: every row (token) is normalized. -/
noncomputable def rmsNormC (h : Matrix T d ℂ) : Matrix T d ℂ :=
  Matrix.of fun t => rmsRowC (h t)

omit [Fintype T] in
private theorem dotProduct_self_div_pos_crn {v : d → ℝ} (hv : v ≠ 0) :
    0 < (v ⬝ᵥ v) / (Fintype.card d : ℝ) := by
  have h1 : 0 < v ⬝ᵥ v :=
    lt_of_le_of_ne (Finset.sum_nonneg fun j _ => mul_self_nonneg (v j))
      (fun h => hv (dotProduct_self_eq_zero.1 h.symm))
  obtain ⟨j, -⟩ := Function.ne_iff.1 hv
  have h2 : (0 : ℝ) < Fintype.card d := Nat.cast_pos.2 (Fintype.card_pos_iff.2 ⟨j⟩)
  exact div_pos h1 h2

/-- The complex RMSNorm extends RMSNorm with `ε = 0`: at a real row `v ≠ 0` its value is the real
row `rmsRow 0 v`. -/
theorem rmsRowC_ofReal (v : d → ℝ) (hv : v ≠ 0) :
    rmsRowC (fun i => (v i : ℂ)) = fun i => ((rmsRow 0 v i : ℝ) : ℂ) := by
  -- the complex dot product of the casts is the cast of the real one
  have hdot : (fun i => (v i : ℂ)) ⬝ᵥ (fun i => (v i : ℂ)) = ((v ⬝ᵥ v : ℝ) : ℂ) := by
    simp only [dotProduct]; push_cast; rfl
  have hpos := dotProduct_self_div_pos_crn hv
  -- `log x` is real for `x > 0`, and `exp (-(log x)/2) = (√x)⁻¹`
  have hlog : Complex.log ((fun i => (v i : ℂ)) ⬝ᵥ (fun i => (v i : ℂ)) / (Fintype.card d : ℂ))
      = (Real.log ((v ⬝ᵥ v) / (Fintype.card d : ℝ)) : ℂ) := by
    rw [hdot, Complex.ofReal_log hpos.le]; push_cast; rfl
  have hexp : Real.exp (-(Real.log ((v ⬝ᵥ v) / (Fintype.card d : ℝ))) / 2)
      = (Real.sqrt ((v ⬝ᵥ v) / (Fintype.card d : ℝ)))⁻¹ := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hpos.le, Real.rpow_def_of_pos hpos]
    ring_nf
  funext i
  simp only [rmsRowC, rmsRow, hlog, Pi.smul_apply, smul_eq_mul, add_zero]
  rw [← hexp]
  push_cast
  rw [neg_div]

omit [Fintype T] in
private theorem card_pos_of_re_pos_crn {v : d → ℂ} (hv : 0 < (v ⬝ᵥ v).re) :
    0 < Fintype.card d := by
  rcases Nat.eq_zero_or_pos (Fintype.card d) with h | h
  · have := Fintype.card_eq_zero_iff.1 h
    simp [dotProduct] at hv
  · exact h

omit [Fintype T] in
private theorem mem_slitPlane_crn {v : d → ℂ} (hv : 0 < (v ⬝ᵥ v).re) :
    (v ⬝ᵥ v) / (Fintype.card d : ℂ) ∈ Complex.slitPlane := by
  refine Complex.mem_slitPlane_iff.2 (Or.inl ?_)
  rw [Complex.div_natCast_re]
  exact div_pos hv (Nat.cast_pos.2 (card_pos_of_re_pos_crn hv))

omit [Fintype T] in
private theorem analyticAt_apply_crn (j : d) (v : d → ℂ) :
    AnalyticAt ℂ (fun h : d → ℂ => h j) v :=
  (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : d => ℂ) j).analyticAt v

/-- "It is holomorphic": the complex RMSNorm is analytic at every row `h` with `Re⟨h, h⟩ > 0`. -/
theorem analyticAt_rmsRowC (v : d → ℂ) (hv : 0 < (v ⬝ᵥ v).re) :
    AnalyticAt ℂ (rmsRowC : (d → ℂ) → d → ℂ) v := by
  have hq : AnalyticAt ℂ (fun h : d → ℂ => (h ⬝ᵥ h) / (Fintype.card d : ℂ)) v :=
    (Finset.analyticAt_fun_sum _ fun j _ =>
      (analyticAt_apply_crn j v).mul (analyticAt_apply_crn j v)).div_const
  have hφ : AnalyticAt ℂ (fun h : d → ℂ =>
      Complex.exp (-(Complex.log ((h ⬝ᵥ h) / (Fintype.card d : ℂ)) / 2))) v :=
    ((hq.clog (mem_slitPlane_crn hv)).div_const.neg).cexp'
  show AnalyticAt ℂ (fun h : d → ℂ =>
    Complex.exp (-(Complex.log ((h ⬝ᵥ h) / (Fintype.card d : ℂ)) / 2)) • h) v
  exact hφ.fun_smul analyticAt_id

omit [Fintype T] in
private theorem ne_zero_of_re_pos_crn {v : d → ℂ} (hv : 0 < (v ⬝ᵥ v).re) :
    (v ⬝ᵥ v) / (Fintype.card d : ℂ) ≠ 0 :=
  Complex.slitPlane_ne_zero (mem_slitPlane_crn hv)

/-- "`N(λh) = N(h)` for `λ > 0`", at rows with `Re⟨h, h⟩ > 0`. -/
theorem rmsRowC_smul (c : ℝ) (hc : 0 < c) (v : d → ℂ) (hv : 0 < (v ⬝ᵥ v).re) :
    rmsRowC ((c : ℂ) • v) = rmsRowC v := by
  have hdot : ((c : ℂ) • v) ⬝ᵥ ((c : ℂ) • v) = ((c ^ 2 : ℝ) : ℂ) * (v ⬝ᵥ v) := by
    rw [smul_dotProduct, dotProduct_smul]; simp only [smul_eq_mul]; push_cast; ring
  have hlog : Complex.log ((((c : ℂ) • v) ⬝ᵥ ((c : ℂ) • v)) / (Fintype.card d : ℂ))
      = (Real.log (c ^ 2) : ℂ) + Complex.log ((v ⬝ᵥ v) / (Fintype.card d : ℂ)) := by
    rw [hdot, mul_div_assoc, Complex.log_ofReal_mul (by positivity) (ne_zero_of_re_pos_crn hv)]
  unfold rmsRowC
  rw [hlog, smul_smul]
  congr 1
  generalize Complex.log ((v ⬝ᵥ v) / (Fintype.card d : ℂ)) = L
  have hc' : Complex.exp (-(Real.log c : ℂ)) = ((c : ℂ))⁻¹ := by
    rw [← Complex.ofReal_neg, ← Complex.ofReal_exp, Real.exp_neg, Real.exp_log hc]; push_cast; rfl
  rw [Real.log_pow, show -(((((2 : ℕ) * Real.log c : ℝ) : ℂ) + L) / 2)
      = -(Real.log c : ℂ) + -(L / 2) by push_cast; ring, Complex.exp_add, hc']
  have : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hc.ne'
  field_simp

/-- **Equation (40), first part:** `⟨n, n⟩ = d ⟹ N(n) = n`. -/
theorem rmsRowC_eq_self (n : d → ℂ) (hn : n ⬝ᵥ n = (Fintype.card d : ℂ)) : rmsRowC n = n := by
  rcases isEmpty_or_nonempty d with hd | hd
  · funext i; exact isEmptyElim i
  · have hc : (Fintype.card d : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
    unfold rmsRowC
    rw [hn, div_self hc, Complex.log_one, zero_div, neg_zero, Complex.exp_zero, one_smul]

omit [Fintype T] in
/-- Helper: a polynomial `a + τ b + τ² c` in one complex variable has the derivative `b` at
`τ = 0` (the complex copy of `hasDerivAt_quad`). -/
private theorem hasDerivAt_quad_crn (a b c : ℂ) :
    HasDerivAt (fun τ : ℂ => a + τ * b + τ * τ * c) b 0 := by
  have h := ((hasDerivAt_id' (x := (0 : ℂ))).mul_const b).const_add a |>.add
    (((hasDerivAt_id' (x := (0 : ℂ))).mul (hasDerivAt_id' (x := (0 : ℂ)))).mul_const c)
  convert h using 1
  ring

/-- **Equation (40), second part:** `⟨n, n⟩ = d ⟹ 𝐃N(n) v = v − (⟨v, n⟩/d) n`. -/
theorem fderiv_rmsRowC_apply (n v : d → ℂ) (hn : n ⬝ᵥ n = (Fintype.card d : ℂ)) :
    fderiv ℂ (rmsRowC : (d → ℂ) → d → ℂ) n v = v - ((v ⬝ᵥ n) / (Fintype.card d : ℂ)) • n := by
  -- with `d` empty both sides are functions on an empty type
  rcases isEmpty_or_nonempty d with hd | hd
  · exact Subsingleton.elim _ _
  have hc : (Fintype.card d : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  -- `Re⟨n, n⟩ = d > 0`, so `N` is analytic at `n`
  have hre : 0 < (n ⬝ᵥ n).re := by
    rw [hn, Complex.natCast_re]; exact Nat.cast_pos.2 Fintype.card_pos
  -- the chain rule along the line `τ ↦ n + τ v`: `τ ↦ N(n + τ v)` has the derivative `𝐃N(n) v`
  have hline : HasDerivAt (fun τ : ℂ => n + τ • v) v 0 := by
    have h1 := ((hasDerivAt_id (0 : ℂ)).smul_const v).const_add n
    rw [one_smul] at h1
    exact h1
  have h0 : n = n + (0 : ℂ) • v := by rw [zero_smul, add_zero]
  have hF := (analyticAt_rmsRowC n hre).differentiableAt.hasFDerivAt.comp_hasDerivAt_of_eq
    (0 : ℂ) hline h0
  -- the same derivative, entry by entry: entry `i` is `exp(-(log q(τ))/2) (n_i + τ v_i)`
  refine hF.unique (hasDerivAt_pi.2 fun i => ?_)
  -- `q(τ) = ⟨n + τv, n + τv⟩/d = ⟨n, n⟩/d + τ 2⟨n, v⟩/d + τ² ⟨v, v⟩/d`, with `q(0) = 1`
  have hq : HasDerivAt (fun τ : ℂ => ((n + τ • v) ⬝ᵥ (n + τ • v)) / (Fintype.card d : ℂ))
      (2 * (n ⬝ᵥ v) / (Fintype.card d : ℂ)) 0 := by
    have e : (fun τ : ℂ => ((n + τ • v) ⬝ᵥ (n + τ • v)) / (Fintype.card d : ℂ))
        = fun τ => (n ⬝ᵥ n) / (Fintype.card d : ℂ) + τ * (2 * (n ⬝ᵥ v) / (Fintype.card d : ℂ))
          + τ * τ * ((v ⬝ᵥ v) / (Fintype.card d : ℂ)) := by
      funext τ
      simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul,
        dotProduct_comm v n]
      ring
    rw [e]
    exact hasDerivAt_quad_crn _ _ _
  have hq0 : ((n + (0 : ℂ) • v) ⬝ᵥ (n + (0 : ℂ) • v)) / (Fintype.card d : ℂ) = 1 := by
    rw [zero_smul, add_zero, hn, div_self hc]
  -- `log` at `q(0) = 1`, then `exp(-(·)/2)`, then the product with `n_i + τ v_i`
  have hφ := ((hq.clog (by rw [hq0]; exact Complex.one_mem_slitPlane)).div_const 2).fun_neg.cexp
  have hent : HasDerivAt (fun τ : ℂ => n i + τ * v i) (v i) 0 := by
    have h1 := ((hasDerivAt_id (0 : ℂ)).mul_const (v i)).const_add (n i)
    rw [one_mul] at h1
    exact h1
  show HasDerivAt (fun τ : ℂ => Complex.exp (-(Complex.log (((n + τ • v) ⬝ᵥ (n + τ • v))
      / (Fintype.card d : ℂ)) / 2)) * (n i + τ * v i))
    (v i - (v ⬝ᵥ n) / (Fintype.card d : ℂ) * n i) 0
  refine (hφ.mul hent).congr_deriv ?_
  simp only [zero_smul, add_zero, hn, div_self hc, Complex.log_one, zero_div, neg_zero,
    Complex.exp_zero, div_one, one_mul, zero_mul, dotProduct_comm n v]
  ring

/-- The cone `C_κ = {u + iu' : ‖u'‖ < κ‖u‖}` of complex rows, with Euclidean norms (written with
squares: `‖u'‖² < κ² ‖u‖²`, for `κ > 0`). -/
def complexCone (κ : ℝ) : Set (d → ℂ) :=
  {h | (fun i => (h i).im) ⬝ᵥ (fun i => (h i).im)
      < κ ^ 2 * ((fun i => (h i).re) ⬝ᵥ (fun i => (h i).re))}

/-- "an open cone": `C_κ` is open. -/
theorem isOpen_complexCone (κ : ℝ) : IsOpen (complexCone (d := d) κ) := by
  refine isOpen_lt ?_ ?_
  · exact continuous_finsetSum _ fun i _ =>
      (Complex.continuous_im.comp (continuous_apply i)).mul
        (Complex.continuous_im.comp (continuous_apply i))
  · exact continuous_const.mul (continuous_finsetSum _ fun i _ =>
      (Complex.continuous_re.comp (continuous_apply i)).mul
        (Complex.continuous_re.comp (continuous_apply i)))

/-- "an open cone": `C_κ` is closed under multiplication by positive numbers. -/
theorem smul_mem_complexCone {κ : ℝ} {h : d → ℂ} (hh : h ∈ complexCone κ) (c : ℝ) (hc : 0 < c) :
    (c : ℂ) • h ∈ complexCone κ := by
  have him : (fun i => (((c : ℂ) • h) i).im) = c • fun i => (h i).im := by
    funext i; simp only [Pi.smul_apply, smul_eq_mul, Complex.im_ofReal_mul]
  have hre : (fun i => (((c : ℂ) • h) i).re) = c • fun i => (h i).re := by
    funext i; simp only [Pi.smul_apply, smul_eq_mul, Complex.re_ofReal_mul]
  have hh' : (fun i => (h i).im) ⬝ᵥ (fun i => (h i).im)
      < κ ^ 2 * ((fun i => (h i).re) ⬝ᵥ (fun i => (h i).re)) := hh
  show (fun i => (((c : ℂ) • h) i).im) ⬝ᵥ (fun i => (((c : ℂ) • h) i).im)
      < κ ^ 2 * ((fun i => (((c : ℂ) • h) i).re) ⬝ᵥ (fun i => (((c : ℂ) • h) i).re))
  rw [him, hre]
  simp only [smul_dotProduct, dotProduct_smul, smul_eq_mul]
  nlinarith [mul_lt_mul_of_pos_left hh' (mul_pos hc hc)]

/-- "that contains every real row `h ≠ 0`", for `κ > 0`. -/
theorem ofReal_mem_complexCone {κ : ℝ} (hκ : 0 < κ) (v : d → ℝ) (hv : v ≠ 0) :
    (fun i => (v i : ℂ)) ∈ complexCone κ := by
  have h1 : 0 < v ⬝ᵥ v :=
    lt_of_le_of_ne (Finset.sum_nonneg fun j _ => mul_self_nonneg (v j))
      (fun h => hv (dotProduct_self_eq_zero.1 h.symm))
  show (fun i => ((v i : ℂ)).im) ⬝ᵥ (fun i => ((v i : ℂ)).im)
      < κ ^ 2 * ((fun i => ((v i : ℂ)).re) ⬝ᵥ (fun i => ((v i : ℂ)).re))
  simp only [Complex.ofReal_im, Complex.ofReal_re]
  have h0 : ((fun _ : d => (0 : ℝ)) ⬝ᵥ fun _ => 0) = 0 := zero_dotProduct _
  rw [h0]
  exact mul_pos (pow_pos hκ 2) h1

/-- The cones decrease with `κ`: `C_κ ⊆ C_κ'` for `0 ≤ κ ≤ κ'`. -/
theorem complexCone_mono {κ κ' : ℝ} (hκ : 0 ≤ κ) (h : κ ≤ κ') :
    complexCone (d := d) κ ⊆ complexCone κ' := by
  intro u hu
  have hu' : (fun i => (u i).im) ⬝ᵥ (fun i => (u i).im)
      < κ ^ 2 * ((fun i => (u i).re) ⬝ᵥ (fun i => (u i).re)) := hu
  have hB : 0 ≤ (fun i => (u i).re) ⬝ᵥ (fun i => (u i).re) :=
    Finset.sum_nonneg fun j _ => mul_self_nonneg _
  have hk : κ ^ 2 ≤ κ' ^ 2 := pow_le_pow_left₀ hκ h 2
  exact lt_of_lt_of_le hu' (mul_le_mul_of_nonneg_right hk hB)

/-- "On `C_1`, `Re⟨h, h⟩ = ‖u‖² − ‖u'‖² > 0`", for every `C_κ` with `0 ≤ κ ≤ 1`. -/
theorem re_dotProduct_self_pos_of_mem_complexCone {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ : κ ≤ 1) {h : d → ℂ}
    (hh : h ∈ complexCone κ) : 0 < (h ⬝ᵥ h).re := by
  have hh' : (fun i => (h i).im) ⬝ᵥ (fun i => (h i).im)
      < κ ^ 2 * ((fun i => (h i).re) ⬝ᵥ (fun i => (h i).re)) := hh
  have hB : 0 ≤ (fun i => (h i).re) ⬝ᵥ (fun i => (h i).re) :=
    Finset.sum_nonneg fun j _ => mul_self_nonneg _
  have hre : (h ⬝ᵥ h).re = (fun i => (h i).re) ⬝ᵥ (fun i => (h i).re)
      - (fun i => (h i).im) ⬝ᵥ (fun i => (h i).im) := by
    simp only [dotProduct, Complex.re_sum, Complex.mul_re, Finset.sum_sub_distrib]
  have hk : κ ^ 2 ≤ 1 := pow_le_one₀ hκ0 hκ
  have := mul_le_mul_of_nonneg_right hk hB
  rw [hre]
  linarith

/-- **The path:** `n(t) = (√d/2)(t ν + ν̄/t)` with `ν = ξ + iξ'`, `ν̄ = ξ − iξ'`. -/
noncomputable def pathRow (ξ ξ' : d → ℝ) (t : ℂ) : d → ℂ :=
  fun i => ((Real.sqrt (Fintype.card d) : ℝ) : ℂ) / 2
    * (t * ((ξ i : ℂ) + Complex.I * (ξ' i : ℂ)) + t⁻¹ * ((ξ i : ℂ) - Complex.I * (ξ' i : ℂ)))

/-- "`⟨n(t), n(t)⟩ = d` for all `t`", for orthonormal `ξ, ξ'` and `t ≠ 0`. -/
theorem pathRow_dotProduct_self (ξ ξ' : d → ℝ) (hξ : ξ ⬝ᵥ ξ = 1) (hξ' : ξ' ⬝ᵥ ξ' = 1)
    (hξξ' : ξ ⬝ᵥ ξ' = 0) (t : ℂ) (ht : t ≠ 0) :
    pathRow ξ ξ' t ⬝ᵥ pathRow ξ ξ' t = (Fintype.card d : ℂ) := by
  have hA : ∑ i, (ξ i : ℂ) * ξ i = 1 := by
    have h := congrArg (fun x : ℝ => (x : ℂ)) hξ
    simp only [dotProduct] at h; push_cast at h; exact h
  have hB : ∑ i, (ξ' i : ℂ) * ξ' i = 1 := by
    have h := congrArg (fun x : ℝ => (x : ℂ)) hξ'
    simp only [dotProduct] at h; push_cast at h; exact h
  have hC : ∑ i, (ξ i : ℂ) * ξ' i = 0 := by
    have h := congrArg (fun x : ℝ => (x : ℂ)) hξξ'
    simp only [dotProduct] at h; push_cast at h; exact h
  have hs : ((Real.sqrt (Fintype.card d) : ℝ) : ℂ) ^ 2 = (Fintype.card d : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]; push_cast; rfl
  have htt : t * t⁻¹ = 1 := mul_inv_cancel₀ ht
  set s : ℂ := ((Real.sqrt (Fintype.card d) : ℝ) : ℂ) with hs_def
  have key : pathRow ξ ξ' t ⬝ᵥ pathRow ξ ξ' t
      = (s / 2) ^ 2 * ((t + t⁻¹) ^ 2 * ∑ i, (ξ i : ℂ) * ξ i
        + 2 * Complex.I * (t + t⁻¹) * (t - t⁻¹) * ∑ i, (ξ i : ℂ) * ξ' i
        + Complex.I ^ 2 * (t - t⁻¹) ^ 2 * ∑ i, (ξ' i : ℂ) * ξ' i) := by
    simp only [pathRow, dotProduct, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [key, hA, hB, hC]
  linear_combination (s ^ 2 / 4 * (t - t⁻¹) ^ 2) * Complex.I_sq + s ^ 2 * htt + hs

/-- **Equation (41):** for real `t ≠ 0`,
`n(t) = √d ((t + t⁻¹)/2 ξ + i (t − t⁻¹)/2 ξ')`. -/
theorem pathRow_ofReal (ξ ξ' : d → ℝ) (t : ℝ) (ht : t ≠ 0) (i : d) :
    pathRow ξ ξ' (t : ℂ) i
      = ((Real.sqrt (Fintype.card d) * ((t + t⁻¹) / 2 * ξ i) : ℝ) : ℂ)
        + Complex.I * ((Real.sqrt (Fintype.card d) * ((t - t⁻¹) / 2 * ξ' i) : ℝ) : ℂ) := by
  simp only [pathRow]
  push_cast
  ring

/-- "For `|t| = 1` the row `n(t)` is real and runs through the great circle of `ξ` and `ξ'`":
`n(e^{iφ}) = √d (cos φ ξ − sin φ ξ')`. -/
theorem pathRow_exp_mul_I (ξ ξ' : d → ℝ) (φ : ℝ) (i : d) :
    pathRow ξ ξ' (Complex.exp (φ * Complex.I)) i
      = ((Real.sqrt (Fintype.card d) * (Real.cos φ * ξ i - Real.sin φ * ξ' i) : ℝ) : ℂ) := by
  have h2 : (Complex.exp (φ * Complex.I))⁻¹ = Complex.cos φ - Complex.sin φ * Complex.I := by
    rw [← Complex.exp_neg, show -((φ : ℂ) * Complex.I) = ((-φ : ℝ) : ℂ) * Complex.I by
      push_cast; ring, Complex.exp_mul_I]
    push_cast
    rw [Complex.cos_neg, Complex.sin_neg]
    ring
  simp only [pathRow]
  rw [h2, Complex.exp_mul_I]
  push_cast
  linear_combination ((Real.sqrt (Fintype.card d) : ℂ) * Complex.sin φ * (ξ' i : ℂ)) * Complex.I_sq

/-- "with `n(1) = √d ξ`". -/
theorem pathRow_one (ξ ξ' : d → ℝ) (i : d) :
    pathRow ξ ξ' 1 i = ((Real.sqrt (Fintype.card d) * ξ i : ℝ) : ℂ) := by
  simp only [pathRow, inv_one, one_mul]
  push_cast
  ring

end Skips
