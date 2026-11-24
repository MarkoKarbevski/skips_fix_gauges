import SkipsLean.Depth.SuffixRMS
import SkipsLean.Depth.StepTanh

/-!
# The step from `(D_{k+1})` to `(D_k)` for a `tanh` block under pre-RMSNorm with `ε > 0`

Paper (dimension paper): Appendix D.3, equations (14) and (20) to (23) with Lemma D.6 ("The
identity at every real row"), and Appendix D.4, Lemma D.7 ("The step for tanh on rays"), in the
case (+).

Under pre-RMSNorm a block reads `n = N_ε(h)`. For a matrix `Z`, equation (14) is
`𝐃N_ε(h)(h Z) = n Z - ⟨n Z, n⟩ n / d`, row by row, so in the identity for one block

  `ż(n) = (n Z - ⟨n Z, n⟩ n / d) W + n η_W`   (equation (20)).

The identity (16) before the block is `𝓛(σ(n W), σ'(n W); n) = 0` for the values `n` of `N_ε`, the
rows of the ball `‖n‖² < d` (equation (22)); its left side is real-analytic in `n`, so it holds at
every row `n` (Lemma D.6). On a ray `n = t ξ` this reads `t³ 𝒯_3 + t 𝒯_1 + 𝒯_0 = 0`, and `𝒯_3 = 0`
says that `Z` is antisymmetric.

Numbering and tokens are as in `Depth/StepTanh.lean`: the block is `k : Fin L`, the hidden state
before it `k.castSucc` and after it `k.succ`, and a hidden state has the rows `T`.
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise Topology

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]
variable {σ σ' : ℝ → ℝ} {ε : ℝ}

/-- The right side of equation (14), row by row: `n Z - ⟨n Z, n⟩ n / d`. -/
noncomputable def tangentRMS (Z : Matrix d d ℝ) (n : Matrix T d ℝ) : Matrix T d ℝ :=
  Matrix.of fun t => (n * Z) t - (((n * Z) t ⬝ᵥ n t) / (Fintype.card d : ℝ)) • n t

omit [DecidableEq d] in
/-- **Equation (14):** for `ε > 0`, `𝐃N_ε(h)(h Z) = n Z - ⟨n Z, n⟩ n / d` at `n = N_ε(h)`. -/
theorem fderiv_rmsNorm_mul (hε : 0 < ε) (Z : Matrix d d ℝ) (h : Matrix T d ℝ) :
    fderiv ℝ (rmsNorm ε : Matrix T d ℝ → Matrix T d ℝ) h (h * Z)
      = tangentRMS Z (rmsNorm ε h) := by
  sorry

/-- **The identity for one block, case (+)** (equation (22), by the chain rule and (14)): for an
MLP block whose activation `σ` has the derivative `σ'`, the identity (16) for the hidden state
before block `k` holds for `Z` and `η` if and only if `𝓛(σ(n W), σ'(n W); n) = 0` at every value
`n = N_ε(h)`, with `ż(n) = (n Z - ⟨n Z, n⟩ n / d) W + n η_W`. -/
theorem suffixFlat_castSucc_iff_mlp_rmsNorm_values (hε : 0 < ε)
    (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut) (k : Fin L)
    (Z : Matrix d d ℝ) (η : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut) :
    SuffixFlat (Arch.mlp σ (rmsNorm ε) hid) θ k.castSucc Z η ↔
      ∀ h : Matrix T d ℝ,
        blockLHS θ k η ((rmsNorm ε h * θ.read k).map σ) ((rmsNorm ε h * θ.read k).map σ')
          (tangentRMS Z (rmsNorm ε h) * θ.read k + rmsNorm ε h * η.read k) = 0 := by
  sorry

/-- **Lemma D.6 (the identity at every real row), case (+):** for a real-analytic activation, the
identity (16) before block `k` holds if and only if `𝓛(σ(n W), σ'(n W); n) = 0` for every
`n` (equation (23)): the left side is real-analytic in `n`, and the values of `N_ε` form an open
set. -/
theorem suffixFlat_castSucc_iff_mlp_rmsNorm (hε : 0 < ε) (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut) (k : Fin L)
    (Z : Matrix d d ℝ) (η : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut) :
    SuffixFlat (Arch.mlp σ (rmsNorm ε) hid) θ k.castSucc Z η ↔
      ∀ n : Matrix T d ℝ,
        blockLHS θ k η ((n * θ.read k).map σ) ((n * θ.read k).map σ')
          (tangentRMS Z n * θ.read k + n * η.read k) = 0 := by
  sorry

variable (θ : Params (Arch.mlp (T := T) (d := d) Real.tanh (rmsNorm ε) hid) dIn dOut)

/-- **The fact in the proof of Lemma D.7, case (+).** Let `θ` be regular and let no row of the
write `V` of block `k` vanish (T1). If `𝐃𝓑(w̃ V) (((1 - w̃²) ⊙ b) V) = 0` for all `w̃`, then
`b = 0`. -/
theorem eq_zero_of_fderiv_suffix_one_sub_sq_rmsNorm (hε : 0 < ε)
    (hθ : Regular (Arch.mlp Real.tanh (rmsNorm ε) hid) θ) (k : Fin L)
    (hT1 : ∀ i : hid k, θ.write k i ≠ 0) (b : Matrix T (hid k) ℝ)
    (h : ∀ w : Matrix T (hid k) ℝ,
      fderiv ℝ
        (fun h' : Matrix T d ℝ => suffix (Arch.mlp Real.tanh (rmsNorm ε) hid) 0 θ k.succ h')
        (w * θ.write k) ((Matrix.of fun t j => (1 - w t j ^ 2) * b t j) * θ.write k) = 0) :
    b = 0 := by
  sorry

/-- **Lemma D.7 (the step for `tanh` on rays), case (+).** Let `ε > 0`, let `θ` be regular, and let
block `k` satisfy (T1), no row of its write vanishes, and (T2), the columns of its read are linearly
independent over `ℚ`. Then `(D_{k+1})` implies `(D_k)`. -/
theorem claimRMS_castSucc_tanh [Nonempty T] (hε : 0 < ε)
    (hθ : Regular (Arch.mlp Real.tanh (rmsNorm ε) hid) θ) (k : Fin L)
    (hT1 : ∀ i : hid k, θ.write k i ≠ 0)
    (hT2 : LinearIndependent ℚ (fun j : hid k => fun i : d => θ.read k i j))
    (hk : ClaimRMS (Arch.mlp Real.tanh (rmsNorm ε) hid) θ k.succ) :
    ClaimRMS (Arch.mlp Real.tanh (rmsNorm ε) hid) θ k.castSucc := by
  sorry

end Skips
