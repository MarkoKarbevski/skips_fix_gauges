import SkipsLean.Dimension.LocalIdentifiabilityAttention
import SkipsLean.Residual.LocalIdentifiabilityAttentionRMS
import SkipsLean.Residual.LocalIdentifiabilityGated
import SkipsLean.Residual.DepthTransformer
import SkipsLean.Residual.DepthTransformerGated
import SkipsLean.Residual.DepthTransformerRMS
import SkipsLean.Residual.DepthTransformerGatedRMS

/-!
# Residual networks of attention blocks and MLP blocks are locally identifiable

Paper (skips paper): Corollary 4.9 (Residual networks are locally identifiable): "Let the blocks
be analytic, with or without pre-RMSNorm, and let `θ` be generic parameters of the residual
network. Every `θ′` near `θ` with the same function is obtained from `θ` by symmetries inside the
blocks and by one matrix `G ∈ G`, all close to the identity. The matrix `G` is the same at all
hidden states". Proposition 4.5 (The equality condition and local identifiability), the direction
from the equality condition to local identifiability, at one parameter.

Here for the residual networks of `Network/Transformer.lean`, whose blocks are attention blocks
and MLP blocks (`Arch.attentionMlp`), or attention blocks and gated blocks
(`Arch.attentionGated`), in any order; the twins of `Dimension/LocalIdentifiabilityAttention.lean`
(attention blocks) and `Residual/LocalIdentifiability.lean`, `LocalIdentifiabilityGated.lean`
(MLP and gated blocks).

* `Params.sumOf a b`: the parameters of a network of `A.sum B` with the parts `a` and `b` (the
  embedding and the readout of `a`). The symmetries of a transformer `θ` are written with it:
  the changes of basis inside the heads act on the first part `θ.sumFst`
  (`Params.headsQK`, `Params.headsVO`), the rescalings of the values of gated units on the second
  part `θ.sumSnd` (`Params.rescale`), and the change of basis of the hidden states on the whole
  (`Params.cob`).
* At one parameter with the functional dimension of Theorem 4.7 (Proposition 4.5), without
  normalization and under pre-RMSNorm (`ε > 0`; then `G` is orthogonal).
* At almost every parameter (Corollary 4.9), for every activation with the conclusion of
  Lemma B.3, and named for tanh, GELU, SwiGLU and GeGLU blocks.

No permutation of heads or of hidden units is needed: the symmetries of the conclusion are near
the identity.
-/

namespace Skips

open Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ}

/-- **The parameters of a network of `A.sum B` with the two parts `a` and `b`:** the embedding
and the readout of `a`, and in every block the read columns and the write rows of `a` beside
those of `b`. -/
def Params.sumOf {A B : Arch T d L} (a : Params A dIn dOut) (b : Params B dIn dOut) :
    Params (A.sum B) dIn dOut where
  E := a.E
  read ℓ := Matrix.of fun k p => Sum.elim (fun j => a.read ℓ k j) (fun j => b.read ℓ k j) p
  write ℓ := Matrix.of fun p k => Sum.elim (fun i => a.write ℓ i k) (fun i => b.write ℓ i k) p
  D := a.D

/-- A network of `A.sum B` is made of its two parts. -/
theorem Params.sumOf_sumFst_sumSnd {A B : Arch T d L} (θ : Params (A.sum B) dIn dOut) :
    Params.sumOf θ.sumFst θ.sumSnd = θ := by
  sorry

variable [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut]
variable {sees : T → T → Prop} [DecidableRel sees]
variable {H dh hid : Fin L → Type} [∀ ℓ, Fintype (H ℓ)] [∀ ℓ, Fintype (dh ℓ)]
  [∀ ℓ, DecidableEq (dh ℓ)] [∀ ℓ, Fintype (hid ℓ)] {σ σ' : ℝ → ℝ} {ε : ℝ}


/-! ### Attention blocks and MLP blocks -/

/-- **Proposition 4.5 of the skips paper, from the equality condition to local identifiability,
for a residual network of attention blocks and MLP blocks, without normalization:** if `E` has
rank `d`, the query and value matrices of every head have rank `d_h` and `θ` has the functional
dimension of Theorem 4.7, then every `θ'` near `θ` with the same function is `θ` after changes of
basis inside the heads, near the identity, and the change of basis by one invertible `G` near the
identity at all hidden states. -/
theorem exists_cob_heads_of_eval_eq_residual_attentionMlp
    (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (θ : Params
      (Arch.attentionMlp (T := T) (d := d) sees σ id H dh hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d)
    (hQ : ∀ ℓ (i : H ℓ),
      ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k)).rank
        = Fintype.card (dh ℓ))
    (hV : ∀ ℓ (i : H ℓ),
      ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))).rank
        = Fintype.card (dh ℓ))
    (hfd : funDim (Arch.attentionMlp sees σ id H dh hid) 1 θ
        + (Fintype.card d ^ 2
          + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
      = Module.finrank ℝ (Params
          (Arch.attentionMlp (T := T) (d := d) sees σ id H dh hid) dIn dOut)) :
    ∀ V ∈ 𝓝 (1 : Matrix d d ℝ), ∀ W ∈ 𝓝 (1 : ∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ),
      ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.attentionMlp sees σ id H dh hid) 1 θ' x
        = eval (Arch.attentionMlp sees σ id H dh hid) 1 θ x) →
        ∃ (G : GL d ℝ) (K K' : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ),
          (G : Matrix d d ℝ) ∈ V
            ∧ (fun ℓ i => (K ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)) ∈ W
            ∧ (fun ℓ i => (K' ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)) ∈ W
            ∧ θ' = (Params.sumOf ((θ.sumFst.headsQK K).headsVO K') θ.sumSnd).cob
                (fun _ => G) (fun _ => G) := by
  sorry

/-- **Proposition 4.5 of the skips paper, from the equality condition to local identifiability,
for a residual network of attention blocks and MLP blocks, under pre-RMSNorm (`ε > 0`):** if `E`
has rank `d`, the query and value matrices of every head have rank `d_h` and `θ` has the
functional dimension of Theorem 4.7, then every `θ'` near `θ` with the same function is `θ` after
changes of basis inside the heads, near the identity, and the change of basis by one orthogonal
`Q` near the identity at all hidden states. -/
theorem exists_cob_heads_of_eval_eq_residual_attentionMlp_rmsNorm (hε : 0 < ε)
    (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (θ : Params
      (Arch.attentionMlp (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d)
    (hQ : ∀ ℓ (i : H ℓ),
      ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k)).rank
        = Fintype.card (dh ℓ))
    (hV : ∀ ℓ (i : H ℓ),
      ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))).rank
        = Fintype.card (dh ℓ))
    (hfd : funDim (Arch.attentionMlp sees σ (rmsNorm ε) H dh hid) 1 θ
        + (Fintype.card d * (Fintype.card d - 1) / 2
          + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
      = Module.finrank ℝ (Params
          (Arch.attentionMlp (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut)) :
    ∀ V ∈ 𝓝 (1 : Matrix d d ℝ), ∀ W ∈ 𝓝 (1 : ∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ),
      ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.attentionMlp sees σ (rmsNorm ε) H dh hid) 1 θ' x
        = eval (Arch.attentionMlp sees σ (rmsNorm ε) H dh hid) 1 θ x) →
        ∃ (Q : GL d ℝ) (K K' : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ),
          (Q : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ ∧ (Q : Matrix d d ℝ) ∈ V
            ∧ (fun ℓ i => (K ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)) ∈ W
            ∧ (fun ℓ i => (K' ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)) ∈ W
            ∧ θ' = (Params.sumOf ((θ.sumFst.headsQK K).headsVO K') θ.sumSnd).cob
                (fun _ => Q) (fun _ => Q) := by
  sorry

/-- **Corollary 4.9 of the skips paper for attention blocks and MLP blocks, without
normalization:** for `d_in, d_out ≥ d ≥ 2`, heads of width `1 ≤ d_h ≤ d`, blocks of any widths and
a mask with a token that sees itself and another token, at almost every parameter `θ` of the
residual network, every `θ'` near `θ` with the same function is `θ` after changes of basis inside
the heads, near the identity, and the change of basis by one invertible `G` near the identity at
all hidden states. -/
theorem ae_exists_cob_heads_of_eval_eq_attentionMlp_residual
    (hσ : ∀ z, HasDerivAt σ (σ' z) z) (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (hU : UnitsRigid σ σ' dIn dOut (Σ ℓ, hid ℓ))
    (μ : Measure (Params
      (Arch.attentionMlp (T := T) (d := d) sees σ id H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ θ ∂μ, ∀ V ∈ 𝓝 (1 : Matrix d d ℝ), ∀ W ∈ 𝓝 (1 : ∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ),
      ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.attentionMlp sees σ id H dh hid) 1 θ' x
        = eval (Arch.attentionMlp sees σ id H dh hid) 1 θ x) →
        ∃ (G : GL d ℝ) (K K' : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ),
          (G : Matrix d d ℝ) ∈ V
            ∧ (fun ℓ i => (K ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)) ∈ W
            ∧ (fun ℓ i => (K' ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)) ∈ W
            ∧ θ' = (Params.sumOf ((θ.sumFst.headsQK K).headsVO K') θ.sumSnd).cob
                (fun _ => G) (fun _ => G) := by
  sorry

/-- **Corollary 4.9 of the skips paper for attention blocks and MLP blocks, under pre-RMSNorm (`ε
> 0`):** for `d_in, d_out ≥ d ≥ 2`, heads of width `1 ≤ d_h ≤ d`, blocks of any widths and a mask
with a token that sees itself and another token, at almost every parameter `θ` of the residual
network, every `θ'` near `θ` with the same function is `θ` after changes of basis inside the
heads, near the identity, and the change of basis by one orthogonal `Q` near the identity at all
hidden states. -/
theorem ae_exists_cob_heads_of_eval_eq_attentionMlp_residual_rmsNorm (hε : 0 < ε)
    (hσ : ∀ z, HasDerivAt σ (σ' z) z) (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (hU : UnitsRigid σ σ' d d (Σ ℓ, hid ℓ))
    (μ : Measure (Params
      (Arch.attentionMlp (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ θ ∂μ, ∀ V ∈ 𝓝 (1 : Matrix d d ℝ), ∀ W ∈ 𝓝 (1 : ∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ),
      ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.attentionMlp sees σ (rmsNorm ε) H dh hid) 1 θ' x
        = eval (Arch.attentionMlp sees σ (rmsNorm ε) H dh hid) 1 θ x) →
        ∃ (Q : GL d ℝ) (K K' : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ),
          (Q : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ ∧ (Q : Matrix d d ℝ) ∈ V
            ∧ (fun ℓ i => (K ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)) ∈ W
            ∧ (fun ℓ i => (K' ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)) ∈ W
            ∧ θ' = (Params.sumOf ((θ.sumFst.headsQK K).headsVO K') θ.sumSnd).cob
                (fun _ => Q) (fun _ => Q) := by
  sorry

/-- **Corollary 4.9 of the skips paper for attention blocks and tanh blocks, without
normalization:** for `d_in, d_out ≥ d ≥ 2`, heads of width `1 ≤ d_h ≤ d`, blocks of any widths and
a mask with a token that sees itself and another token, at almost every parameter `θ` of the
residual network, every `θ'` near `θ` with the same function is `θ` after changes of basis inside
the heads, near the identity, and the change of basis by one invertible `G` near the identity at
all hidden states. -/
theorem ae_exists_cob_heads_of_eval_eq_attention_tanh_residual
    (μ : Measure (Params
      (Arch.attentionMlp (T := T) (d := d) sees Real.tanh id H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ θ ∂μ, ∀ V ∈ 𝓝 (1 : Matrix d d ℝ), ∀ W ∈ 𝓝 (1 : ∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ),
      ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.attentionMlp sees Real.tanh id H dh hid) 1 θ' x
        = eval (Arch.attentionMlp sees Real.tanh id H dh hid) 1 θ x) →
        ∃ (G : GL d ℝ) (K K' : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ),
          (G : Matrix d d ℝ) ∈ V
            ∧ (fun ℓ i => (K ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)) ∈ W
            ∧ (fun ℓ i => (K' ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)) ∈ W
            ∧ θ' = (Params.sumOf ((θ.sumFst.headsQK K).headsVO K') θ.sumSnd).cob
                (fun _ => G) (fun _ => G) := by
  sorry

/-- **Corollary 4.9 of the skips paper for attention blocks and tanh blocks, under pre-RMSNorm (`ε
> 0`):** for `d_in, d_out ≥ d ≥ 2`, heads of width `1 ≤ d_h ≤ d`, blocks of any widths and a mask
with a token that sees itself and another token, at almost every parameter `θ` of the residual
network, every `θ'` near `θ` with the same function is `θ` after changes of basis inside the
heads, near the identity, and the change of basis by one orthogonal `Q` near the identity at all
hidden states. -/
theorem ae_exists_cob_heads_of_eval_eq_attention_tanh_residual_rmsNorm (hε : 0 < ε)
    (μ : Measure (Params
      (Arch.attentionMlp (T := T) (d := d) sees Real.tanh (rmsNorm ε) H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ θ ∂μ, ∀ V ∈ 𝓝 (1 : Matrix d d ℝ), ∀ W ∈ 𝓝 (1 : ∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ),
      ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.attentionMlp sees Real.tanh (rmsNorm ε) H dh hid) 1 θ' x
        = eval (Arch.attentionMlp sees Real.tanh (rmsNorm ε) H dh hid) 1 θ x) →
        ∃ (Q : GL d ℝ) (K K' : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ),
          (Q : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ ∧ (Q : Matrix d d ℝ) ∈ V
            ∧ (fun ℓ i => (K ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)) ∈ W
            ∧ (fun ℓ i => (K' ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)) ∈ W
            ∧ θ' = (Params.sumOf ((θ.sumFst.headsQK K).headsVO K') θ.sumSnd).cob
                (fun _ => Q) (fun _ => Q) := by
  sorry

/-- **Corollary 4.9 of the skips paper for attention blocks and GELU blocks, without
normalization:** for `d_in, d_out ≥ d ≥ 2`, heads of width `1 ≤ d_h ≤ d`, blocks of any widths and
a mask with a token that sees itself and another token, at almost every parameter `θ` of the
residual network, every `θ'` near `θ` with the same function is `θ` after changes of basis inside
the heads, near the identity, and the change of basis by one invertible `G` near the identity at
all hidden states. -/
theorem ae_exists_cob_heads_of_eval_eq_attention_gelu_residual
    (μ : Measure (Params
      (Arch.attentionMlp (T := T) (d := d) sees gelu id H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ θ ∂μ, ∀ V ∈ 𝓝 (1 : Matrix d d ℝ), ∀ W ∈ 𝓝 (1 : ∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ),
      ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.attentionMlp sees gelu id H dh hid) 1 θ' x
        = eval (Arch.attentionMlp sees gelu id H dh hid) 1 θ x) →
        ∃ (G : GL d ℝ) (K K' : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ),
          (G : Matrix d d ℝ) ∈ V
            ∧ (fun ℓ i => (K ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)) ∈ W
            ∧ (fun ℓ i => (K' ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)) ∈ W
            ∧ θ' = (Params.sumOf ((θ.sumFst.headsQK K).headsVO K') θ.sumSnd).cob
                (fun _ => G) (fun _ => G) := by
  sorry

/-- **Corollary 4.9 of the skips paper for attention blocks and GELU blocks, under pre-RMSNorm (`ε
> 0`):** for `d_in, d_out ≥ d ≥ 2`, heads of width `1 ≤ d_h ≤ d`, blocks of any widths and a mask
with a token that sees itself and another token, at almost every parameter `θ` of the residual
network, every `θ'` near `θ` with the same function is `θ` after changes of basis inside the
heads, near the identity, and the change of basis by one orthogonal `Q` near the identity at all
hidden states. -/
theorem ae_exists_cob_heads_of_eval_eq_attention_gelu_residual_rmsNorm (hε : 0 < ε)
    (μ : Measure (Params
      (Arch.attentionMlp (T := T) (d := d) sees gelu (rmsNorm ε) H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ θ ∂μ, ∀ V ∈ 𝓝 (1 : Matrix d d ℝ), ∀ W ∈ 𝓝 (1 : ∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ),
      ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.attentionMlp sees gelu (rmsNorm ε) H dh hid) 1 θ' x
        = eval (Arch.attentionMlp sees gelu (rmsNorm ε) H dh hid) 1 θ x) →
        ∃ (Q : GL d ℝ) (K K' : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ),
          (Q : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ ∧ (Q : Matrix d d ℝ) ∈ V
            ∧ (fun ℓ i => (K ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)) ∈ W
            ∧ (fun ℓ i => (K' ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)) ∈ W
            ∧ θ' = (Params.sumOf ((θ.sumFst.headsQK K).headsVO K') θ.sumSnd).cob
                (fun _ => Q) (fun _ => Q) := by
  sorry


/-! ### Attention blocks and gated blocks -/

/-- **Proposition 4.5 of the skips paper, from the equality condition to local identifiability,
for a residual network of attention blocks and gated blocks, without normalization:** if `E` has
rank `d`, the query and value matrices of every head have rank `d_h`, no value column of a gated
unit vanishes and `θ` has the functional dimension of Theorem 4.7, then every `θ'` near `θ` with
the same function is `θ` after changes of basis inside the heads and rescalings of the values of
the gated units, near the identity, and the change of basis by one invertible `G` near the
identity at all hidden states. -/
theorem exists_cob_heads_of_eval_eq_residual_attentionGated
    (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (θ : Params
      (Arch.attentionGated (T := T) (d := d) sees σ id H dh hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d)
    (hQ : ∀ ℓ (i : H ℓ),
      ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k)).rank
        = Fintype.card (dh ℓ))
    (hV : ∀ ℓ (i : H ℓ),
      ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))).rank
        = Fintype.card (dh ℓ))
    (hv : ∀ ℓ i, (fun k => θ.sumSnd.read ℓ k (Sum.inr i)) ≠ 0)
    (hfd : funDim (Arch.attentionGated sees σ id H dh hid) 1 θ
        + (Fintype.card d ^ 2
          + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
            + ∑ ℓ, Fintype.card (hid ℓ)))
      = Module.finrank ℝ (Params
          (Arch.attentionGated (T := T) (d := d) sees σ id H dh hid) dIn dOut)) :
    ∀ V ∈ 𝓝 (1 : Matrix d d ℝ), ∀ W ∈ 𝓝 (1 : ∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ),
      ∀ Wc ∈ 𝓝 (1 : ∀ ℓ, hid ℓ → ℝ), ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.attentionGated sees σ id H dh hid) 1 θ' x
        = eval (Arch.attentionGated sees σ id H dh hid) 1 θ x) →
        ∃ (G : GL d ℝ) (K K' : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ) (c : ∀ ℓ, hid ℓ → ℝ),
          (G : Matrix d d ℝ) ∈ V
            ∧ (fun ℓ i => (K ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)) ∈ W
            ∧ (fun ℓ i => (K' ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)) ∈ W
            ∧ c ∈ Wc ∧ (∀ ℓ i, 0 < c ℓ i)
            ∧ θ' = (Params.sumOf ((θ.sumFst.headsQK K).headsVO K') (θ.sumSnd.rescale c)).cob
                (fun _ => G) (fun _ => G) := by
  sorry

/-- **Proposition 4.5 of the skips paper, from the equality condition to local identifiability,
for a residual network of attention blocks and gated blocks, under pre-RMSNorm (`ε > 0`):** if `E`
has rank `d`, the query and value matrices of every head have rank `d_h`, no value column of a
gated unit vanishes and `θ` has the functional dimension of Theorem 4.7, then every `θ'` near `θ`
with the same function is `θ` after changes of basis inside the heads and rescalings of the values
of the gated units, near the identity, and the change of basis by one orthogonal `Q` near the
identity at all hidden states. -/
theorem exists_cob_heads_of_eval_eq_residual_attentionGated_rmsNorm (hε : 0 < ε)
    (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (θ : Params
      (Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d)
    (hQ : ∀ ℓ (i : H ℓ),
      ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k)).rank
        = Fintype.card (dh ℓ))
    (hV : ∀ ℓ (i : H ℓ),
      ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))).rank
        = Fintype.card (dh ℓ))
    (hv : ∀ ℓ i, (fun k => θ.sumSnd.read ℓ k (Sum.inr i)) ≠ 0)
    (hfd : funDim (Arch.attentionGated sees σ (rmsNorm ε) H dh hid) 1 θ
        + (Fintype.card d * (Fintype.card d - 1) / 2
          + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
            + ∑ ℓ, Fintype.card (hid ℓ)))
      = Module.finrank ℝ (Params
          (Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut)) :
    ∀ V ∈ 𝓝 (1 : Matrix d d ℝ), ∀ W ∈ 𝓝 (1 : ∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ),
      ∀ Wc ∈ 𝓝 (1 : ∀ ℓ, hid ℓ → ℝ), ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.attentionGated sees σ (rmsNorm ε) H dh hid) 1 θ' x
        = eval (Arch.attentionGated sees σ (rmsNorm ε) H dh hid) 1 θ x) →
        ∃ (Q : GL d ℝ) (K K' : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ) (c : ∀ ℓ, hid ℓ → ℝ),
          (Q : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ ∧ (Q : Matrix d d ℝ) ∈ V
            ∧ (fun ℓ i => (K ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)) ∈ W
            ∧ (fun ℓ i => (K' ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)) ∈ W
            ∧ c ∈ Wc ∧ (∀ ℓ i, 0 < c ℓ i)
            ∧ θ' = (Params.sumOf ((θ.sumFst.headsQK K).headsVO K') (θ.sumSnd.rescale c)).cob
                (fun _ => Q) (fun _ => Q) := by
  sorry

/-- **Corollary 4.9 of the skips paper for attention blocks and gated blocks, without
normalization:** for `d_in, d_out ≥ d ≥ 2`, heads of width `1 ≤ d_h ≤ d`, blocks of any widths and
a mask with a token that sees itself and another token, at almost every parameter `θ` of the
residual network, every `θ'` near `θ` with the same function is `θ` after changes of basis inside
the heads and rescalings of the values of the gated units, near the identity, and the change of
basis by one invertible `G` near the identity at all hidden states. -/
theorem ae_exists_cob_heads_of_eval_eq_attentionGated_residual
    (hσ : ∀ z, HasDerivAt σ (σ' z) z) (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (hU : GatedUnitsRescale σ σ' dIn dOut (Σ ℓ, hid ℓ))
    (μ : Measure (Params
      (Arch.attentionGated (T := T) (d := d) sees σ id H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ θ ∂μ, ∀ V ∈ 𝓝 (1 : Matrix d d ℝ), ∀ W ∈ 𝓝 (1 : ∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ),
      ∀ Wc ∈ 𝓝 (1 : ∀ ℓ, hid ℓ → ℝ), ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.attentionGated sees σ id H dh hid) 1 θ' x
        = eval (Arch.attentionGated sees σ id H dh hid) 1 θ x) →
        ∃ (G : GL d ℝ) (K K' : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ) (c : ∀ ℓ, hid ℓ → ℝ),
          (G : Matrix d d ℝ) ∈ V
            ∧ (fun ℓ i => (K ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)) ∈ W
            ∧ (fun ℓ i => (K' ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)) ∈ W
            ∧ c ∈ Wc ∧ (∀ ℓ i, 0 < c ℓ i)
            ∧ θ' = (Params.sumOf ((θ.sumFst.headsQK K).headsVO K') (θ.sumSnd.rescale c)).cob
                (fun _ => G) (fun _ => G) := by
  sorry

/-- **Corollary 4.9 of the skips paper for attention blocks and gated blocks, under pre-RMSNorm
(`ε > 0`):** for `d_in, d_out ≥ d ≥ 2`, heads of width `1 ≤ d_h ≤ d`, blocks of any widths and a
mask with a token that sees itself and another token, at almost every parameter `θ` of the
residual network, every `θ'` near `θ` with the same function is `θ` after changes of basis inside
the heads and rescalings of the values of the gated units, near the identity, and the change of
basis by one orthogonal `Q` near the identity at all hidden states. -/
theorem ae_exists_cob_heads_of_eval_eq_attentionGated_residual_rmsNorm (hε : 0 < ε)
    (hσ : ∀ z, HasDerivAt σ (σ' z) z) (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (hU : GatedUnitsRescale σ σ' d d (Σ ℓ, hid ℓ))
    (μ : Measure (Params
      (Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ θ ∂μ, ∀ V ∈ 𝓝 (1 : Matrix d d ℝ), ∀ W ∈ 𝓝 (1 : ∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ),
      ∀ Wc ∈ 𝓝 (1 : ∀ ℓ, hid ℓ → ℝ), ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.attentionGated sees σ (rmsNorm ε) H dh hid) 1 θ' x
        = eval (Arch.attentionGated sees σ (rmsNorm ε) H dh hid) 1 θ x) →
        ∃ (Q : GL d ℝ) (K K' : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ) (c : ∀ ℓ, hid ℓ → ℝ),
          (Q : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ ∧ (Q : Matrix d d ℝ) ∈ V
            ∧ (fun ℓ i => (K ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)) ∈ W
            ∧ (fun ℓ i => (K' ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)) ∈ W
            ∧ c ∈ Wc ∧ (∀ ℓ i, 0 < c ℓ i)
            ∧ θ' = (Params.sumOf ((θ.sumFst.headsQK K).headsVO K') (θ.sumSnd.rescale c)).cob
                (fun _ => Q) (fun _ => Q) := by
  sorry

/-- **Corollary 4.9 of the skips paper for attention blocks and SwiGLU blocks, without
normalization:** for `d_in, d_out ≥ d ≥ 2`, heads of width `1 ≤ d_h ≤ d`, blocks of any widths and
a mask with a token that sees itself and another token, at almost every parameter `θ` of the
residual network, every `θ'` near `θ` with the same function is `θ` after changes of basis inside
the heads and rescalings of the values of the gated units, near the identity, and the change of
basis by one invertible `G` near the identity at all hidden states. -/
theorem ae_exists_cob_heads_of_eval_eq_attention_swiglu_residual
    (μ : Measure (Params
      (Arch.attentionGated (T := T) (d := d) sees silu id H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ θ ∂μ, ∀ V ∈ 𝓝 (1 : Matrix d d ℝ), ∀ W ∈ 𝓝 (1 : ∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ),
      ∀ Wc ∈ 𝓝 (1 : ∀ ℓ, hid ℓ → ℝ), ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.attentionGated sees silu id H dh hid) 1 θ' x
        = eval (Arch.attentionGated sees silu id H dh hid) 1 θ x) →
        ∃ (G : GL d ℝ) (K K' : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ) (c : ∀ ℓ, hid ℓ → ℝ),
          (G : Matrix d d ℝ) ∈ V
            ∧ (fun ℓ i => (K ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)) ∈ W
            ∧ (fun ℓ i => (K' ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)) ∈ W
            ∧ c ∈ Wc ∧ (∀ ℓ i, 0 < c ℓ i)
            ∧ θ' = (Params.sumOf ((θ.sumFst.headsQK K).headsVO K') (θ.sumSnd.rescale c)).cob
                (fun _ => G) (fun _ => G) := by
  sorry

/-- **Corollary 4.9 of the skips paper for attention blocks and SwiGLU blocks, under pre-RMSNorm
(`ε > 0`):** for `d_in, d_out ≥ d ≥ 2`, heads of width `1 ≤ d_h ≤ d`, blocks of any widths and a
mask with a token that sees itself and another token, at almost every parameter `θ` of the
residual network, every `θ'` near `θ` with the same function is `θ` after changes of basis inside
the heads and rescalings of the values of the gated units, near the identity, and the change of
basis by one orthogonal `Q` near the identity at all hidden states. -/
theorem ae_exists_cob_heads_of_eval_eq_attention_swiglu_residual_rmsNorm (hε : 0 < ε)
    (μ : Measure (Params
      (Arch.attentionGated (T := T) (d := d) sees silu (rmsNorm ε) H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ θ ∂μ, ∀ V ∈ 𝓝 (1 : Matrix d d ℝ), ∀ W ∈ 𝓝 (1 : ∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ),
      ∀ Wc ∈ 𝓝 (1 : ∀ ℓ, hid ℓ → ℝ), ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.attentionGated sees silu (rmsNorm ε) H dh hid) 1 θ' x
        = eval (Arch.attentionGated sees silu (rmsNorm ε) H dh hid) 1 θ x) →
        ∃ (Q : GL d ℝ) (K K' : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ) (c : ∀ ℓ, hid ℓ → ℝ),
          (Q : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ ∧ (Q : Matrix d d ℝ) ∈ V
            ∧ (fun ℓ i => (K ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)) ∈ W
            ∧ (fun ℓ i => (K' ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)) ∈ W
            ∧ c ∈ Wc ∧ (∀ ℓ i, 0 < c ℓ i)
            ∧ θ' = (Params.sumOf ((θ.sumFst.headsQK K).headsVO K') (θ.sumSnd.rescale c)).cob
                (fun _ => Q) (fun _ => Q) := by
  sorry

/-- **Corollary 4.9 of the skips paper for attention blocks and GeGLU blocks, without
normalization:** for `d_in, d_out ≥ d ≥ 2`, heads of width `1 ≤ d_h ≤ d`, blocks of any widths and
a mask with a token that sees itself and another token, at almost every parameter `θ` of the
residual network, every `θ'` near `θ` with the same function is `θ` after changes of basis inside
the heads and rescalings of the values of the gated units, near the identity, and the change of
basis by one invertible `G` near the identity at all hidden states. -/
theorem ae_exists_cob_heads_of_eval_eq_attention_geglu_residual
    (μ : Measure (Params
      (Arch.attentionGated (T := T) (d := d) sees gelu id H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ θ ∂μ, ∀ V ∈ 𝓝 (1 : Matrix d d ℝ), ∀ W ∈ 𝓝 (1 : ∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ),
      ∀ Wc ∈ 𝓝 (1 : ∀ ℓ, hid ℓ → ℝ), ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.attentionGated sees gelu id H dh hid) 1 θ' x
        = eval (Arch.attentionGated sees gelu id H dh hid) 1 θ x) →
        ∃ (G : GL d ℝ) (K K' : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ) (c : ∀ ℓ, hid ℓ → ℝ),
          (G : Matrix d d ℝ) ∈ V
            ∧ (fun ℓ i => (K ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)) ∈ W
            ∧ (fun ℓ i => (K' ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)) ∈ W
            ∧ c ∈ Wc ∧ (∀ ℓ i, 0 < c ℓ i)
            ∧ θ' = (Params.sumOf ((θ.sumFst.headsQK K).headsVO K') (θ.sumSnd.rescale c)).cob
                (fun _ => G) (fun _ => G) := by
  sorry

/-- **Corollary 4.9 of the skips paper for attention blocks and GeGLU blocks, under pre-RMSNorm
(`ε > 0`):** for `d_in, d_out ≥ d ≥ 2`, heads of width `1 ≤ d_h ≤ d`, blocks of any widths and a
mask with a token that sees itself and another token, at almost every parameter `θ` of the
residual network, every `θ'` near `θ` with the same function is `θ` after changes of basis inside
the heads and rescalings of the values of the gated units, near the identity, and the change of
basis by one orthogonal `Q` near the identity at all hidden states. -/
theorem ae_exists_cob_heads_of_eval_eq_attention_geglu_residual_rmsNorm (hε : 0 < ε)
    (μ : Measure (Params
      (Arch.attentionGated (T := T) (d := d) sees gelu (rmsNorm ε) H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ θ ∂μ, ∀ V ∈ 𝓝 (1 : Matrix d d ℝ), ∀ W ∈ 𝓝 (1 : ∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ),
      ∀ Wc ∈ 𝓝 (1 : ∀ ℓ, hid ℓ → ℝ), ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.attentionGated sees gelu (rmsNorm ε) H dh hid) 1 θ' x
        = eval (Arch.attentionGated sees gelu (rmsNorm ε) H dh hid) 1 θ x) →
        ∃ (Q : GL d ℝ) (K K' : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ) (c : ∀ ℓ, hid ℓ → ℝ),
          (Q : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ ∧ (Q : Matrix d d ℝ) ∈ V
            ∧ (fun ℓ i => (K ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)) ∈ W
            ∧ (fun ℓ i => (K' ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)) ∈ W
            ∧ c ∈ Wc ∧ (∀ ℓ i, 0 < c ℓ i)
            ∧ θ' = (Params.sumOf ((θ.sumFst.headsQK K).headsVO K') (θ.sumSnd.rescale c)).cob
                (fun _ => Q) (fun _ => Q) := by
  sorry

end Skips
