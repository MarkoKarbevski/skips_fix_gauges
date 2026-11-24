import SkipsLean.Dimension.LocalIdentifiabilityAttention
import SkipsLean.Residual.DepthAttentionRMSDim
import SkipsLean.Residual.LearnedSkips
import SkipsLean.Symmetry.Normalized

/-!
# Attention networks under pre-RMSNorm are locally identifiable up to their symmetries

Paper (dimension paper): Proposition 4.6; paper (skips paper): Proposition 4.5 and Corollary 4.9,
quoted in `Dimension/LocalIdentifiabilityAttention.lean` ("with or without pre-RMSNorm"). Under
pre-RMSNorm with `ε > 0` the changes of basis of the hidden states are orthogonal (`G = O(d)`,
of dimension `d(d−1)/2`), and the symmetries inside the blocks are the changes of basis inside the
heads.

Here, for attention blocks under pre-RMSNorm with `ε > 0`:

* the direction from the equality condition to local identifiability, at one parameter, for
  skipless networks (`fd(θ) = P − (L + 1) d(d−1)/2 − s`) and for residual networks
  (`fd(θ) = P − d(d−1)/2 − s`), `s = 2 ∑_ℓ H_ℓ d_{h,ℓ}²`;
* Corollary 4.9 of the skips paper for attention blocks under pre-RMSNorm: at almost every
  parameter of the residual network (Theorem 4.7 gives its functional dimension).

The twin without normalization is `Dimension/LocalIdentifiabilityAttention.lean`; the twins for
gated blocks are `Dimension/LocalIdentifiabilityGated.lean` and
`Residual/LocalIdentifiabilityGated.lean`. Not stated here: the converse direction; `ε = 0`.
-/

namespace Skips

open Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {sees : T → T → Prop} [DecidableRel sees]
variable {H dh : Fin L → Type} [∀ ℓ, Fintype (H ℓ)] [∀ ℓ, Fintype (dh ℓ)]
  [∀ ℓ, DecidableEq (dh ℓ)] {ε : ℝ}

/-- **Proposition 4.6 of the dimension paper for attention blocks, from the equality condition to
local identifiability, under pre-RMSNorm with `ε > 0`:** if `E` and the writes have rank `d`, the
query and value matrices of every head have rank `d_h` and `fd(θ) = P − (L + 1) d(d−1)/2 − s`,
then every `θ'` near `θ` with the same function is `θ` after changes of basis inside the heads,
near the identity, and a change of basis by orthogonal `Q_0, …, Q_L` near the identity. -/
theorem exists_cob_heads_of_eval_eq_skipless_attention_rmsNorm (hε : 0 < ε)
    (θ : Params (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut)
    (hE : θ.E.rank = Fintype.card d) (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d)
    (hQ : ∀ ℓ (i : H ℓ), ((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k)).rank
      = Fintype.card (dh ℓ))
    (hV : ∀ ℓ (i : H ℓ),
      ((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))).rank
        = Fintype.card (dh ℓ))
    (hfd : funDim (Arch.attention sees (rmsNorm ε) H dh) 0 θ
        + ((L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2)
          + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
      = Module.finrank ℝ
          (Params (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut)) :
    ∀ V ∈ 𝓝 (1 : Fin (L + 1) → Matrix d d ℝ),
      ∀ W ∈ 𝓝 (1 : ∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ), ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.attention sees (rmsNorm ε) H dh) 0 θ' x
        = eval (Arch.attention sees (rmsNorm ε) H dh) 0 θ x) →
        ∃ (Q : Fin (L + 1) → GL d ℝ) (K K' : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ),
          (∀ ℓ, (Q ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ)
            ∧ (fun ℓ => (Q ℓ : Matrix d d ℝ)) ∈ V
            ∧ (fun ℓ i => (K ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)) ∈ W
            ∧ (fun ℓ i => (K' ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)) ∈ W
            ∧ θ' = ((θ.headsQK K).headsVO K').cob Q Q := by
  sorry

/-- **Proposition 4.5 of the skips paper for residual networks of attention blocks, from the
equality condition to local identifiability, under pre-RMSNorm with `ε > 0`:** if `E` has rank
`d`, the query and value matrices of every head have rank `d_h` and
`fd(θ) = P − d(d−1)/2 − s`, then every `θ'` near `θ` with the same function is `θ` after changes
of basis inside the heads, near the identity, and the change of basis by one orthogonal `Q` near
the identity at all hidden states. -/
theorem exists_cob_heads_of_eval_eq_residual_attention_rmsNorm (hε : 0 < ε)
    (θ : Params (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut)
    (hE : θ.E.rank = Fintype.card d)
    (hQ : ∀ ℓ (i : H ℓ), ((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k)).rank
      = Fintype.card (dh ℓ))
    (hV : ∀ ℓ (i : H ℓ),
      ((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))).rank
        = Fintype.card (dh ℓ))
    (hfd : funDim (Arch.attention sees (rmsNorm ε) H dh) 1 θ
        + (Fintype.card d * (Fintype.card d - 1) / 2
          + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
      = Module.finrank ℝ
          (Params (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut)) :
    ∀ V ∈ 𝓝 (1 : Matrix d d ℝ), ∀ W ∈ 𝓝 (1 : ∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ),
      ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.attention sees (rmsNorm ε) H dh) 1 θ' x
        = eval (Arch.attention sees (rmsNorm ε) H dh) 1 θ x) →
        ∃ (Q : GL d ℝ) (K K' : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ),
          (Q : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ ∧ (Q : Matrix d d ℝ) ∈ V
            ∧ (fun ℓ i => (K ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)) ∈ W
            ∧ (fun ℓ i => (K' ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)) ∈ W
            ∧ θ' = ((θ.headsQK K).headsVO K').cob (fun _ => Q) (fun _ => Q) := by
  sorry

/-- **Corollary 4.9 of the skips paper for attention blocks under pre-RMSNorm with `ε > 0`:** for
`d_in, d_out ≥ d ≥ 2`, heads of width `1 ≤ d_h ≤ d` and a mask with a token that sees itself and
another token, at almost every parameter `θ` of the residual network, every `θ'` near `θ` with
the same function is `θ` after changes of basis inside the heads, near the identity, and the
change of basis by one orthogonal `Q` near the identity at all hidden states. -/
theorem ae_exists_cob_heads_of_eval_eq_attention_residual_rmsNorm (hε : 0 < ε)
    (μ : Measure (Params (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ θ ∂μ, ∀ V ∈ 𝓝 (1 : Matrix d d ℝ), ∀ W ∈ 𝓝 (1 : ∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ),
      ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.attention sees (rmsNorm ε) H dh) 1 θ' x
        = eval (Arch.attention sees (rmsNorm ε) H dh) 1 θ x) →
        ∃ (Q : GL d ℝ) (K K' : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ),
          (Q : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ ∧ (Q : Matrix d d ℝ) ∈ V
            ∧ (fun ℓ i => (K ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)) ∈ W
            ∧ (fun ℓ i => (K' ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)) ∈ W
            ∧ θ' = ((θ.headsQK K).headsVO K').cob (fun _ => Q) (fun _ => Q) := by
  sorry

end Skips
