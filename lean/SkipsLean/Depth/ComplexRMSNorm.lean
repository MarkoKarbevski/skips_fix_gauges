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

/-- The complex RMSNorm extends RMSNorm with `ε = 0`: at a real row `v ≠ 0` its value is the real
row `rmsRow 0 v`. -/
theorem rmsRowC_ofReal (v : d → ℝ) (hv : v ≠ 0) :
    rmsRowC (fun i => (v i : ℂ)) = fun i => ((rmsRow 0 v i : ℝ) : ℂ) := by
  sorry

/-- "It is holomorphic": the complex RMSNorm is analytic at every row `h` with `Re⟨h, h⟩ > 0`. -/
theorem analyticAt_rmsRowC (v : d → ℂ) (hv : 0 < (v ⬝ᵥ v).re) :
    AnalyticAt ℂ (rmsRowC : (d → ℂ) → d → ℂ) v := by
  sorry

/-- "`N(λh) = N(h)` for `λ > 0`", at rows with `Re⟨h, h⟩ > 0`. -/
theorem rmsRowC_smul (c : ℝ) (hc : 0 < c) (v : d → ℂ) (hv : 0 < (v ⬝ᵥ v).re) :
    rmsRowC ((c : ℂ) • v) = rmsRowC v := by
  sorry

/-- **Equation (40), first part:** `⟨n, n⟩ = d ⟹ N(n) = n`. -/
theorem rmsRowC_eq_self (n : d → ℂ) (hn : n ⬝ᵥ n = (Fintype.card d : ℂ)) : rmsRowC n = n := by
  sorry

/-- **Equation (40), second part:** `⟨n, n⟩ = d ⟹ 𝐃N(n) v = v − (⟨v, n⟩/d) n`. -/
theorem fderiv_rmsRowC_apply (n v : d → ℂ) (hn : n ⬝ᵥ n = (Fintype.card d : ℂ)) :
    fderiv ℂ (rmsRowC : (d → ℂ) → d → ℂ) n v = v - ((v ⬝ᵥ n) / (Fintype.card d : ℂ)) • n := by
  sorry

/-- The cone `C_κ = {u + iu' : ‖u'‖ < κ‖u‖}` of complex rows, with Euclidean norms (written with
squares: `‖u'‖² < κ² ‖u‖²`, for `κ > 0`). -/
def complexCone (κ : ℝ) : Set (d → ℂ) :=
  {h | (fun i => (h i).im) ⬝ᵥ (fun i => (h i).im)
      < κ ^ 2 * ((fun i => (h i).re) ⬝ᵥ (fun i => (h i).re))}

/-- "an open cone": `C_κ` is open. -/
theorem isOpen_complexCone (κ : ℝ) : IsOpen (complexCone (d := d) κ) := by
  sorry

/-- "an open cone": `C_κ` is closed under multiplication by positive numbers. -/
theorem smul_mem_complexCone {κ : ℝ} {h : d → ℂ} (hh : h ∈ complexCone κ) (c : ℝ) (hc : 0 < c) :
    (c : ℂ) • h ∈ complexCone κ := by
  sorry

/-- "that contains every real row `h ≠ 0`", for `κ > 0`. -/
theorem ofReal_mem_complexCone {κ : ℝ} (hκ : 0 < κ) (v : d → ℝ) (hv : v ≠ 0) :
    (fun i => (v i : ℂ)) ∈ complexCone κ := by
  sorry

/-- The cones decrease with `κ`: `C_κ ⊆ C_κ'` for `0 ≤ κ ≤ κ'`. -/
theorem complexCone_mono {κ κ' : ℝ} (hκ : 0 ≤ κ) (h : κ ≤ κ') :
    complexCone (d := d) κ ⊆ complexCone κ' := by
  sorry

/-- "On `C_1`, `Re⟨h, h⟩ = ‖u‖² − ‖u'‖² > 0`", for every `C_κ` with `0 ≤ κ ≤ 1`. -/
theorem re_dotProduct_self_pos_of_mem_complexCone {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ : κ ≤ 1) {h : d → ℂ}
    (hh : h ∈ complexCone κ) : 0 < (h ⬝ᵥ h).re := by
  sorry

/-- **The path:** `n(t) = (√d/2)(t ν + ν̄/t)` with `ν = ξ + iξ'`, `ν̄ = ξ − iξ'`. -/
noncomputable def pathRow (ξ ξ' : d → ℝ) (t : ℂ) : d → ℂ :=
  fun i => ((Real.sqrt (Fintype.card d) : ℝ) : ℂ) / 2
    * (t * ((ξ i : ℂ) + Complex.I * (ξ' i : ℂ)) + t⁻¹ * ((ξ i : ℂ) - Complex.I * (ξ' i : ℂ)))

/-- "`⟨n(t), n(t)⟩ = d` for all `t`", for orthonormal `ξ, ξ'` and `t ≠ 0`. -/
theorem pathRow_dotProduct_self (ξ ξ' : d → ℝ) (hξ : ξ ⬝ᵥ ξ = 1) (hξ' : ξ' ⬝ᵥ ξ' = 1)
    (hξξ' : ξ ⬝ᵥ ξ' = 0) (t : ℂ) (ht : t ≠ 0) :
    pathRow ξ ξ' t ⬝ᵥ pathRow ξ ξ' t = (Fintype.card d : ℂ) := by
  sorry

/-- **Equation (41):** for real `t ≠ 0`,
`n(t) = √d ((t + t⁻¹)/2 ξ + i (t − t⁻¹)/2 ξ')`. -/
theorem pathRow_ofReal (ξ ξ' : d → ℝ) (t : ℝ) (ht : t ≠ 0) (i : d) :
    pathRow ξ ξ' (t : ℂ) i
      = ((Real.sqrt (Fintype.card d) * ((t + t⁻¹) / 2 * ξ i) : ℝ) : ℂ)
        + Complex.I * ((Real.sqrt (Fintype.card d) * ((t - t⁻¹) / 2 * ξ' i) : ℝ) : ℂ) := by
  sorry

/-- "For `|t| = 1` the row `n(t)` is real and runs through the great circle of `ξ` and `ξ'`":
`n(e^{iφ}) = √d (cos φ ξ − sin φ ξ')`. -/
theorem pathRow_exp_mul_I (ξ ξ' : d → ℝ) (φ : ℝ) (i : d) :
    pathRow ξ ξ' (Complex.exp (φ * Complex.I)) i
      = ((Real.sqrt (Fintype.card d) * (Real.cos φ * ξ i - Real.sin φ * ξ' i) : ℝ) : ℂ) := by
  sorry

/-- "with `n(1) = √d ξ`". -/
theorem pathRow_one (ξ ξ' : d → ℝ) (i : d) :
    pathRow ξ ξ' 1 i = ((Real.sqrt (Fintype.card d) * ξ i : ℝ) : ℂ) := by
  sorry

end Skips
