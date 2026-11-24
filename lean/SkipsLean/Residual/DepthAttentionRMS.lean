import SkipsLean.OneBlock.AttentionFamily
import SkipsLean.Residual.SmallWritesRMSSteps
import SkipsLean.Dimension.UpperBoundAttention
import SkipsLean.Network.AttentionAnalytic

/-!
# Residual networks of attention blocks at any depth under pre-RMSNorm: small writes

Paper (skips paper): Lemma A.27 (Small writes), its second value, for attention blocks: "For all
small `τ ≠ 0`, the residual network has […] `fd(θ_τ) = P − d_model (d_model − 1)/2 − s`
(pre-RMSNorm with `ε > 0`, no biases)". Its proof, "Under pre-RMSNorm": with `h = x E`,
`n = N_ε(h)` and the limit `(J_0 η)(x) = 𝐃N_ε(h) (x η_E + D_θ g(n) η) D + N_ε(h) η_D`, "this is
the equation of the proof of Theorem B.1 (ii) with `h_1 = x E` and
`D_θ h_1 η = x η_E + D_θ g(n) η`, and its Steps 1 to 5 go through"; Steps 1 to 3
(`Residual/SmallWritesRMSSteps.lean`, for any continuously differentiable blocks) give an
antisymmetric `Y` with `η_E = E Y`, `η_D = −Y D`, and `D_θ g(n) η = 0` at every `n = N_ε(x E)`.
For attention blocks `g` is the sum of the heads of all blocks with the matrices
`Γ_j = W_Q W_K^⊤/√d_h` and `W_V W_O` ("with `E` and `D` replaced by the identity"), the identity
`D_θ g(n) η = 0` extends from the rows of norm less than `√d` to all rows because its left side is
real-analytic in `n`, and Step 2 for a family of heads (`OneBlock/AttentionFamily.lean`) gives
that the derivatives of every `Γ_j` and every `W_V W_O` along `η` vanish.

Here, for `Arch.attention sees (rmsNorm ε) H dh` with `L` blocks, `ε > 0`, and a token `t₂` that
sees itself and another token `t₁`:

* `headScoreModel θ ℓ i`, `headValueModel θ ℓ i`: the matrices `W_Q W_K^⊤/√d_h` and `W_V W_O` of
  head `i` of block `ℓ`, on the model space.
* `SmallWritesGenericAttentionRMS θ`: the conditions on `θ` that the proof uses.
* `smallWritesLimitNorm_eq_zero_attention_rmsNorm`: a direction that is flat for `J_0` has
  `η_E = E Y`, `η_D = −Y D` with `Y` antisymmetric, and in every block the reads and writes of
  the directions of the changes of basis inside the heads.
* `eventually_funDim_smallWrites_attention_rmsNorm`:
  `fd(θ_τ) = P − d(d−1)/2 − 2 ∑_ℓ H_ℓ d_{h,ℓ}²` for all small `τ ≠ 0`.
-/

namespace Skips

open Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {sees : T → T → Prop} [DecidableRel sees] {χ : Matrix T d ℝ → Matrix T d ℝ}
variable {H dh : Fin L → Type} [∀ ℓ, Fintype (H ℓ)] [∀ ℓ, Fintype (dh ℓ)] {ε : ℝ}

/-- **The matrix `W_Q W_K^⊤ / √d_h`** of head `i` of block `ℓ`, on the model space. -/
noncomputable def headScoreModel (θ : Params (Arch.attention sees χ H dh) dIn dOut) (ℓ : Fin L)
    (i : H ℓ) : Matrix d d ℝ :=
  (Real.sqrt (Fintype.card (dh ℓ)))⁻¹ •
    (((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k))
      * ((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inl k)))ᵀ)

/-- **The matrix `W_V W_O`** of head `i` of block `ℓ`, on the model space. -/
def headValueModel (θ : Params (Arch.attention sees χ H dh) dIn dOut) (ℓ : Fin L) (i : H ℓ) :
    Matrix d d ℝ :=
  ((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k)))
    * ((θ.write ℓ).submatrix (fun k : dh ℓ => (i, k)) id)

/-- **The conditions on `θ` in Lemma A.27 under pre-RMSNorm, for attention blocks:** `E` and `D`
have rank `d`; the query, key, value and output matrices of every head of every block have rank
`d_h`; and, "with `E` and `D` replaced by the identity", some `v` has the columns
`W_Q W_K^⊤ v^⊤` of the heads of all blocks together nonzero and pairwise non-collinear, and every
row `v W_V W_O` nonzero. -/
structure SmallWritesGenericAttentionRMS
    (θ : Params (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut) : Prop where
  rank_E : θ.E.rank = Fintype.card d
  rank_D : θ.D.rank = Fintype.card d
  rank_Q : ∀ ℓ (i : H ℓ), ((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k)).rank
    = Fintype.card (dh ℓ)
  rank_K : ∀ ℓ (i : H ℓ),
    ((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inl k))).rank
      = Fintype.card (dh ℓ)
  rank_V : ∀ ℓ (i : H ℓ),
    ((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))).rank
      = Fintype.card (dh ℓ)
  rank_O : ∀ ℓ (i : H ℓ), ((θ.write ℓ).submatrix (fun k : dh ℓ => (i, k)) id).rank
    = Fintype.card (dh ℓ)
  /-- some `v` has the `W_Q W_K^⊤ v^⊤` of all heads nonzero and pairwise non-collinear and every
  `v W_V W_O` nonzero -/
  exists_v : ∃ v : d → ℝ, (∀ p : (Σ ℓ, H ℓ), headScoreModel θ p.1 p.2 *ᵥ v ≠ 0)
    ∧ (∀ p q : (Σ ℓ, H ℓ), p ≠ q → ∀ r : ℝ,
        headScoreModel θ p.1 p.2 *ᵥ v ≠ r • (headScoreModel θ q.1 q.2 *ᵥ v))
    ∧ (∀ p : (Σ ℓ, H ℓ), v ᵥ* headValueModel θ p.1 p.2 ≠ 0)

/-- **Proof of Lemma A.27 under pre-RMSNorm, attention blocks, the flat directions of `J_0`:**
let `ε > 0` and let token `t₂` see itself and another token `t₁`. Under the conditions of the
lemma, a direction `η` with `(J_0 η)(x) = 0` at every input `x` has `η_E = E Y` and
`η_D = −Y D` for one antisymmetric matrix `Y`, and in every block its reads and its writes are
those of the directions of the changes of basis inside the heads. -/
theorem smallWritesLimitNorm_eq_zero_attention_rmsNorm (hε : 0 < ε) (t₁ t₂ : T) (h12 : t₁ ≠ t₂)
    (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁)
    (θ : Params (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut)
    (hθ : SmallWritesGenericAttentionRMS θ)
    (η : Params (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut)
    (hη : ∀ x, smallWritesLimitNorm (Arch.attention sees (rmsNorm ε) H dh) θ η x = 0) :
    ∃ (Y : Matrix d d ℝ) (Γ Γ' : ∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ),
      Yᵀ = -Y ∧ η.E = θ.E * Y ∧ η.D = -(Y * θ.D)
        ∧ (∀ ℓ, η.read ℓ = (headDirQK θ Γ + headDirVO θ Γ').read ℓ)
        ∧ (∀ ℓ, η.write ℓ = (headDirQK θ Γ + headDirVO θ Γ').write ℓ) := by
  sorry

/-- **Lemma A.27 (Small writes), second value, for attention blocks, under the conditions of its
proof:** under pre-RMSNorm with `ε > 0`, with a token that sees itself and another token, for all
small `τ ≠ 0` the residual network has `fd(θ_τ) = P − d(d−1)/2 − 2 ∑_ℓ H_ℓ d_{h,ℓ}²`. -/
theorem eventually_funDim_smallWrites_attention_rmsNorm (hε : 0 < ε) (t₁ t₂ : T)
    (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁)
    (θ : Params (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut)
    (hθ : SmallWritesGenericAttentionRMS θ) :
    ∀ᶠ τ in 𝓝[≠] (0 : ℝ),
      funDim (Arch.attention sees (rmsNorm ε) H dh) 1 (θ.smallWrites τ)
          + (Fintype.card d * (Fintype.card d - 1) / 2
            + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
        = Module.finrank ℝ
            (Params (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut) := by
  sorry

end Skips
