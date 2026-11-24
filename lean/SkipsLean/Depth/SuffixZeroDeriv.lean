import SkipsLean.Depth.SuffixZero

/-!
# The case (0): regular parameters and the derivative of `𝓑_{>k}`

Paper (dimension paper): Appendix D.3 in the case (0), pre-RMSNorm with `ε = 0`. "We call `θ`
regular if (R1) `E`, `D` and every `W_write^ℓ` have rank `d`; (R2) in the case (0), for every `ℓ`
and every `n ∈ S`: `g_ℓ(n) ≠ 0`; (R3) for every `ℓ`: […] in the case (0), there is an `n ∈ S` such
that no row `v ≠ 0` with `⟨v, n⟩ = 0` has `𝐃g_ℓ(n) v ∈ ℝ g_ℓ(n)`. […] In the case (0), by (R2),
[`𝓑_{>k}`] is defined and real-analytic on all rows `h ≠ 0`."

Lemma D.2 (The derivative of `𝓑_{>k}`), the case (0): "Let `θ` be regular. For every `k` there is
an open dense set `U_k` of rows such that, for `h ∈ U_k`, `𝐃𝓑_{>k}(h) v = 0` only if […]
`v ∈ ℝ h`, in the case (0). In the case (0), `U_k` consists of rows `h ≠ 0` and is closed under
multiplication by positive numbers."

Here `S` is the sphere `‖n‖² = d`, `g_ℓ(n) = f_ℓ(n W_read^ℓ) W_write^ℓ` is block `ℓ`, and a hidden
state has the rows `T` (tokens): "`h ≠ 0`" is "no row of `h` vanishes", "`n ∈ S`" is "every row of
`n` is on `S`", "`v ∈ ℝ h`" is "every row of `v` is a multiple of the same row of `h`", and the
positive numbers multiply the rows one by one. For blocks that act on every token alone (MLP
blocks) these are the paper's statements for one token, at every token.
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable (A : Arch T d L) (θ : Params A dIn dOut)

/-- "`θ` is regular", in the case (0): (R1) `E`, `D` and every write have rank `d`; (R2) no row of
`g_ℓ(n)` vanishes when every row of `n` is on the sphere `‖n‖² = d`; (R3) for every block there is
such an `n` at which a `v` whose rows are orthogonal to the rows of `n`, and for which every row of
`𝐃g_ℓ(n) v` is a multiple of the same row of `g_ℓ(n)`, is `0`. -/
structure RegularZero : Prop where
  rank_E : θ.E.rank = Fintype.card d
  rank_D : θ.D.rank = Fintype.card d
  rank_write : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d
  block_ne_zero : ∀ (ℓ : Fin L) (n : Matrix T d ℝ),
    (∀ t, n t ⬝ᵥ n t = (Fintype.card d : ℝ)) →
      ∀ t, (A.f ℓ (n * θ.read ℓ) * θ.write ℓ) t ≠ 0
  deriv_block : ∀ ℓ : Fin L, ∃ n : Matrix T d ℝ, (∀ t, n t ⬝ᵥ n t = (Fintype.card d : ℝ)) ∧
    ∀ v : Matrix T d ℝ, (∀ t, v t ⬝ᵥ n t = 0) →
      (∀ t, ∃ a : ℝ,
        fderiv ℝ (fun n' : Matrix T d ℝ => A.f ℓ (n' * θ.read ℓ) * θ.write ℓ) n v t
          = a • (A.f ℓ (n * θ.read ℓ) * θ.write ℓ) t) →
      v = 0

omit [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- RMSNorm with `ε = 0` maps a nonzero row to the sphere `‖n‖² = d`. -/
theorem rmsNorm_zero_dotProduct_self (h : Matrix T d ℝ) (t : T) (ht : h t ≠ 0) :
    (rmsNorm 0 h) t ⬝ᵥ (rmsNorm 0 h) t = (Fintype.card d : ℝ) := by
  sorry

/-- **Appendix D.3, the case (0): "by (R2), it is defined and real-analytic on all rows `h ≠ 0`".**
For real-analytic blocks under pre-RMSNorm with `ε = 0`, at parameters with (R2), the map
`(θ', h') ↦ 𝓑_{>k}(h')` at the weights `θ'` is real-analytic at `(θ, h)` for every `h` without a
zero row. -/
theorem analyticAt_suffix_prod_zero (hχ : A.χ = rmsNorm 0)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (hθ : RegularZero A θ) (k : Fin (L + 1))
    (h : Matrix T d ℝ) (hh : ∀ t, h t ≠ 0) :
    AnalyticAt ℝ
      (fun p : Params A dIn dOut × Matrix T d ℝ => suffix A 0 p.1 k p.2) (θ, h) := by
  sorry

/-- **Appendix D.3, the case (0), "`𝓑_{>k}(λh) = 𝓑_{>k}(h)` for `λ > 0`":** under pre-RMSNorm with
`ε = 0`, multiplying the rows of `h` by positive numbers does not change `𝓑_{>k}(h)`. -/
theorem suffix_zero_smul_rows (hχ : A.χ = rmsNorm 0) (k : Fin (L + 1)) (h : Matrix T d ℝ)
    (c : T → ℝ) (hc : ∀ t, 0 < c t) :
    suffix A 0 θ k (Matrix.of fun t => c t • h t) = suffix A 0 θ k h := by
  sorry

/-- **Lemma D.2 of the dimension paper (the derivative of `𝓑_{>k}`), the case (0):** let the
blocks be real-analytic, `d ≥ 2`, and `θ` regular. For every `k` there is an open dense set `U_k`
of matrices without a zero row, closed under multiplication of the rows by positive numbers, such
that for `h ∈ U_k`, `𝐃𝓑_{>k}(h) v = 0` only if every row of `v` is a multiple of the same row of
`h`. -/
theorem exists_open_dense_fderiv_suffix_zero (hχ : A.χ = rmsNorm 0)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (hθ : RegularZero A θ)
    (hd : 2 ≤ Fintype.card d) (k : Fin (L + 1)) :
    ∃ U : Set (Matrix T d ℝ), IsOpen U ∧ Dense U ∧ (∀ h ∈ U, ∀ t, h t ≠ 0) ∧
      (∀ h ∈ U, ∀ c : T → ℝ, (∀ t, 0 < c t) → (Matrix.of fun t => c t • h t) ∈ U) ∧
      ∀ h ∈ U, ∀ v : Matrix T d ℝ,
        fderiv ℝ (fun h' : Matrix T d ℝ => suffix A 0 θ k h') h v = 0 →
          ∀ t, ∃ a : ℝ, v t = a • h t := by
  sorry

end Skips
