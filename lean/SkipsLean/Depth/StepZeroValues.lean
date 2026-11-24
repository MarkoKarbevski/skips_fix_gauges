import SkipsLean.Depth.StepTanhRMS
import SkipsLean.Depth.SuffixZeroClaim

/-!
# The identity for one block in the case (0), and Lemma D.17

Paper (dimension paper): Appendix D.3, equations (14) and (20) to (22), in the case (0)
(pre-RMSNorm with `ε = 0`), and Appendix D.6, Lemma D.17.

Equation (14): "In the cases (+) and (0), for a `d × d` matrix `Z` and `n = χ(h)`,
`𝐃χ(h)(hZ) = nZ − (⟨nZ, n⟩/d) n`." The identity for one block: with
`ż(n) = (nZ − (⟨nZ, n⟩/d) n) W + n η_W` (20) and
`𝓛(w̃, w̃'; n) = 𝐃𝓑(w̃V)((w̃' ⊙ ż(n)) V + w̃ η_V) + 𝐃_θ𝓑(w̃V) η'` (21), "(16) for `k` is
equivalent to `𝓛(σ(nW), σ'(nW); n) = 0` for all values `n` of `χ`, (22), that is, […] for `n ∈ S`
in the case (0)."

Lemma D.17 (A change of the reads moves the output): "In the case (0), let `θ` be regular with (S1)
for block `k + 1`, let `V = W_write^{k+1}` have the rows `a_1, …, a_q`, and let `b ∈ ℂ^{1 × q}`. If
`𝐃𝓑_{>k+1}(w̃V)(((1 − w̃²) ⊙ b) V) = 0` for all `w̃` in a nonempty open subset of `ℝ^{1 × q}`, […]
then `b = 0`." (S1): "any two rows of `V` are linearly independent". Here it is stated for a real
`b`, the case to which the paper's proof reduces ("At real `w̃` the derivative is a real linear
map, so the real and the imaginary part of `b` satisfy the hypothesis: let `b` be real").

Numbering and tokens are as in `Depth/StepTanh.lean`: the block is `k : Fin L`, the hidden state
before it `k.castSucc` and after it `k.succ`, a hidden state has the rows `T`, and `S` is "every
row on the sphere `‖n‖² = d`". `blockLHS` (`Depth/StepTanh.lean`) is `𝓛`, and `tangentRMS Z n`
(`Depth/StepTanhRMS.lean`) is `nZ − (⟨nZ, n⟩/d) n`.
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut] {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)] {σ σ' : ℝ → ℝ}

omit [Fintype T] [DecidableEq d] in
/-- Helper: a row of `N(h)`, `N` RMSNorm with `ε = 0`, is `ρ⁻¹ h_t` with `ρ = √(‖h_t‖² / d)`. -/
private theorem rmsNorm_zero_row_szv (h : Matrix T d ℝ) (t : T) :
    rmsNorm 0 h t = (Real.sqrt ((h t ⬝ᵥ h t) / (Fintype.card d : ℝ)))⁻¹ • h t := by
  show rmsRow 0 (h t) = _
  unfold rmsRow
  rw [add_zero]

omit [Fintype T] [DecidableEq d] in
/-- Helper: a row of `N(h) Z` is `ρ⁻¹ (h Z)_t`. -/
private theorem rmsNorm_zero_mul_row_szv (Z : Matrix d d ℝ) (h : Matrix T d ℝ) (t : T) :
    (rmsNorm 0 h * Z) t = (Real.sqrt ((h t ⬝ᵥ h t) / (Fintype.card d : ℝ)))⁻¹ • (h * Z) t := by
  rw [Matrix.mul_apply_eq_vecMul, Matrix.mul_apply_eq_vecMul, rmsNorm_zero_row_szv]
  exact Matrix.smul_vecMul (R := ℝ) _ (h t) Z

omit [DecidableEq d] in
/-- **Equation (14) in the case (0):** `𝐃N(h)(hZ) = nZ − (⟨nZ, n⟩/d) n` at `n = N(h)`, for `N`
RMSNorm with `ε = 0` and `h` without a zero row. -/
theorem fderiv_rmsNorm_zero_mul (Z : Matrix d d ℝ) (h : Matrix T d ℝ) (hh : ∀ t, h t ≠ 0) :
    fderiv ℝ (rmsNorm 0 : Matrix T d ℝ → Matrix T d ℝ) h (h * Z)
      = tangentRMS Z (rmsNorm 0 h) := by
  rw [fderiv_rmsNorm_zero_apply h (h * Z) hh]
  ext t i
  -- with `ρ = √(‖h_t‖² / d)`: `n_t = ρ⁻¹ h_t` and `(n Z)_t = ρ⁻¹ (h Z)_t`
  show (Real.sqrt ((h t ⬝ᵥ h t) / (Fintype.card d : ℝ)))⁻¹ * (h * Z) t i
      - ((h t ⬝ᵥ (h * Z) t) / (Fintype.card d : ℝ)
        * (Real.sqrt ((h t ⬝ᵥ h t) / (Fintype.card d : ℝ)))⁻¹ ^ 3) * h t i
    = (rmsNorm 0 h * Z) t i
      - ((rmsNorm 0 h * Z) t ⬝ᵥ rmsNorm 0 h t) / (Fintype.card d : ℝ) * rmsNorm 0 h t i
  rw [rmsNorm_zero_mul_row_szv, rmsNorm_zero_row_szv, smul_dotProduct, dotProduct_smul,
    Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul,
    dotProduct_comm ((h * Z) t) (h t)]
  ring

/-- **The identity for one block, case (0)** (equation (22), by the chain rule and (14)): for an
MLP block with a real-analytic activation `σ` with derivative `σ'`, and regular `θ`, the identity
(16) for the hidden state before block `k` holds for `Z` and `η` if and only if
`𝓛(σ(n W), σ'(n W); n) = 0` at every value `n = N(h)`, `h` without a zero row, with
`ż(n) = (n Z − (⟨n Z, n⟩/d) n) W + n η_W`. -/
theorem suffixFlatZero_castSucc_iff_mlp_values (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
    (hθ : RegularZero (Arch.mlp σ (rmsNorm 0) hid) θ) (k : Fin L)
    (Z : Matrix d d ℝ) (η : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) :
    SuffixFlatZero (Arch.mlp σ (rmsNorm 0) hid) θ k.castSucc Z η ↔
      ∀ h : Matrix T d ℝ, (∀ t, h t ≠ 0) →
        blockLHS θ k η ((rmsNorm 0 h * θ.read k).map σ) ((rmsNorm 0 h * θ.read k).map σ')
          (tangentRMS Z (rmsNorm 0 h) * θ.read k + rmsNorm 0 h * η.read k) = 0 := by
  sorry

/-- **Equation (22) in the case (0), on the sphere:** under the same hypotheses and `d ≥ 1`, the
identity (16) before block `k` holds if and only if `𝓛(σ(n W), σ'(n W); n) = 0` for every `n` with
all rows on the sphere `‖n‖² = d`. -/
theorem suffixFlatZero_castSucc_iff_mlp_sphere [Nonempty d] (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
    (hθ : RegularZero (Arch.mlp σ (rmsNorm 0) hid) θ) (k : Fin L)
    (Z : Matrix d d ℝ) (η : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) :
    SuffixFlatZero (Arch.mlp σ (rmsNorm 0) hid) θ k.castSucc Z η ↔
      ∀ n : Matrix T d ℝ, (∀ t, n t ⬝ᵥ n t = (Fintype.card d : ℝ)) →
        blockLHS θ k η ((n * θ.read k).map σ) ((n * θ.read k).map σ')
          (tangentRMS Z n * θ.read k + n * η.read k) = 0 := by
  sorry

/-- **Lemma D.17 of the dimension paper (a change of the reads moves the output), for a real `b`.**
In the case (0), let the blocks be real-analytic MLP blocks, `d ≥ 2`, `θ` regular, and let any two
rows of the write `V` of block `k` be linearly independent (S1). If
`𝐃𝓑(w̃ V)(((1 − w̃²) ⊙ b) V) = 0` for all `w̃` in a nonempty open set, then `b = 0`. -/
theorem eq_zero_of_fderiv_suffix_one_sub_sq_zero (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
    (hθ : RegularZero (Arch.mlp σ (rmsNorm 0) hid) θ) (hd : 2 ≤ Fintype.card d) (k : Fin L)
    (hS1 : ∀ i j : hid k, i ≠ j → ∀ a c : ℝ, a • θ.write k i + c • θ.write k j = 0 →
      a = 0 ∧ c = 0)
    (b : Matrix T (hid k) ℝ) (O : Set (Matrix T (hid k) ℝ)) (hO : IsOpen O) (hne : O.Nonempty)
    (h : ∀ w ∈ O,
      fderiv ℝ
        (fun h' : Matrix T d ℝ => suffix (Arch.mlp σ (rmsNorm 0) hid) 0 θ k.succ h')
        (w * θ.write k) ((Matrix.of fun t j => (1 - w t j ^ 2) * b t j) * θ.write k) = 0) :
    b = 0 := by
  sorry

end Skips
