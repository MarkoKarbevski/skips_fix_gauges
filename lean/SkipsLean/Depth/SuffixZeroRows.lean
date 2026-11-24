import SkipsLean.Depth.SuffixRows
import SkipsLean.Depth.SuffixZeroClaim

/-!
# Homogeneity of `𝓑_{>k}` in the case `ε = 0`, and a direction that `𝐃𝓑_{>k}` kills on an open set

Paper (dimension paper): Appendix D.3 in the case (0) and Appendix D.6. Under pre-RMSNorm with
`ε = 0`, `𝓑_{>k}(λh) = 𝓑_{>k}(h)` for `λ > 0`; so `𝐃𝓑_{>k}(h) h = 0` (the source of (15)) and "a
derivative of order `i` of `𝓑` is homogeneous of degree `−i`" (proof of Lemma D.19). The proof of
Lemma D.19 then uses Lemma D.2 in this form (Steps 2 and 4): "By (P1), `a_j ≠ 0`, so by Lemma D.2
`𝐃𝓑(n W V) a_j ≠ 0` on an open dense set of `n`", and "`η°a_j` is a multiple of `n W V` for an open
set of rows `n`, so `η°a_j = 0`".

Stated here, for regular `θ` and hidden states without a zero row: `𝐃𝓑_{>j}(ch)(cv) = 𝐃𝓑_{>j}(h)v`
and `𝐃_θ𝓑_{>j}(ch) = 𝐃_θ𝓑_{>j}(h)` for `c > 0`; `𝐃𝓑_{>j}(h) h = 0`; and, for MLP blocks, `d ≥ 2`
and an invertible matrix `M`: if `𝐃𝓑_{>j}(xM)(a) = 0` for the rows `x` of a nonempty open set (the
same rows `xM` and `a` at every token), then `a = 0`.
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]

section General

variable (A : Arch T d L) (θ : Params A dIn dOut)

/-- **"A derivative of order `1` of `𝓑` is homogeneous of degree `−1`":**
`𝐃𝓑_{>j}(ch)(cv) = 𝐃𝓑_{>j}(h)v` for `c > 0`, regular `θ` and `h` without a zero row. -/
theorem fderiv_suffix_zero_smul (hχ : A.χ = rmsNorm 0)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (hθ : RegularZero A θ) (j : Fin (L + 1))
    (h v : Matrix T d ℝ) (hh : ∀ t, h t ≠ 0) {c : ℝ} (hc : 0 < c) :
    fderiv ℝ (fun h' : Matrix T d ℝ => suffix A 0 θ j h') (c • h) (c • v)
      = fderiv ℝ (fun h' : Matrix T d ℝ => suffix A 0 θ j h') h v := by
  sorry

/-- **`𝐃𝓑_{>j}(h) h = 0`** for regular `θ` and `h` without a zero row (the derivative at `c = 1` of
`𝓑_{>j}(ch) = 𝓑_{>j}(h)`). -/
theorem fderiv_suffix_zero_apply_self (hχ : A.χ = rmsNorm 0)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (hθ : RegularZero A θ) (j : Fin (L + 1))
    (h : Matrix T d ℝ) (hh : ∀ t, h t ≠ 0) :
    fderiv ℝ (fun h' : Matrix T d ℝ => suffix A 0 θ j h') h h = 0 := by
  sorry

/-- **`𝐃_θ𝓑_{>j}(ch) = 𝐃_θ𝓑_{>j}(h)`** for `c > 0`. -/
theorem fderiv_param_suffix_zero_smul (hχ : A.χ = rmsNorm 0) (j : Fin (L + 1))
    (h : Matrix T d ℝ) (η : Params A dIn dOut) {c : ℝ} (hc : 0 < c) :
    fderiv ℝ (fun θ' : Params A dIn dOut => suffix A 0 θ' j (c • h)) θ η
      = fderiv ℝ (fun θ' : Params A dIn dOut => suffix A 0 θ' j h) θ η := by
  sorry

end General

variable {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)] {σ : ℝ → ℝ}

/-- **Lemma D.2 on an open set of rows:** for real-analytic MLP blocks in the case (0), `d ≥ 2`,
regular `θ` and an invertible matrix `M`: if `𝐃𝓑_{>j}(xM)(a) = 0` for every row `x` of a nonempty
open set (the row `xM` and the row `a` at every token), then `a = 0`. -/
theorem eq_zero_of_fderiv_suffix_zero_eq_zero_rows [Nonempty T]
    (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
    (hθ : RegularZero (Arch.mlp σ (rmsNorm 0) hid) θ) (hd : 2 ≤ Fintype.card d)
    (j : Fin (L + 1)) (M : Matrix d d ℝ) (hM : IsUnit M.det)
    (N : Set (d → ℝ)) (hN : IsOpen N) (hNne : N.Nonempty) (a : d → ℝ)
    (h : ∀ x ∈ N,
      fderiv ℝ (fun h' : Matrix T d ℝ => suffix (Arch.mlp σ (rmsNorm 0) hid) 0 θ j h')
        ((Matrix.of fun (_ : T) => x) * M) (Matrix.of fun (_ : T) => a) = 0) :
    a = 0 := by
  sorry

/-- **From `ż_j(n) = 0` on an open set to `Z`** (proof of Lemma D.19, Step 2: "that is, by (20),
`‖n‖² n (Z c_j + η_{c_j}) = ⟨nZ, n⟩ n c_j` on an open cone of rows `n`, hence for all `n`. For
`n` orthogonal to `c_j` this gives `n (Z c_j + η_{c_j}) = 0`, so `Z c_j + η_{c_j} = β_k c_j` for a
number `β_k`, and then `⟨nZ, n⟩ = β_k ‖n‖²` for all `n`. So `Z = Y_k + β_k I` with `Y_k`
antisymmetric"): if
`(x ⬝ x)(x ⬝ u) = (x Z xᵀ)(x ⬝ c)` for the rows `x` of a nonempty open set and `c ≠ 0`, then
`u = β c` and `Z − β I` is antisymmetric, for a number `β`. -/
theorem exists_smul_of_quadratic_rows (Z : Matrix d d ℝ) (u c : d → ℝ) (hc : c ≠ 0)
    (N : Set (d → ℝ)) (hN : IsOpen N) (hNne : N.Nonempty)
    (h : ∀ x ∈ N, (x ⬝ᵥ x) * (x ⬝ᵥ u) = ((x ᵥ* Z) ⬝ᵥ x) * (x ⬝ᵥ c)) :
    ∃ β : ℝ, u = β • c ∧ Z - β • (1 : Matrix d d ℝ) ∈ antisymmetric d := by
  sorry

end Skips
