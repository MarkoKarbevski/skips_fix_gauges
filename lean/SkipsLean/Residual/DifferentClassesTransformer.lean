import SkipsLean.Residual.SkiplessEndsTransformer
import SkipsLean.Residual.DifferentClassesCriterion
import SkipsLean.Residual.DepthTransformer
import SkipsLean.Residual.DepthTransformerGated
import SkipsLean.Residual.DepthTransformerRMS
import SkipsLean.Residual.DepthTransformerGatedRMS

/-!
# Residual and skipless transformers: different function classes

Paper (skips paper): Theorem 4.11 (Different function classes), part (i): "For analytic blocks,
with or without pre-RMSNorm, a residual network at generic parameters equals no skipless network
of the same widths, and is not a pointwise limit of such networks." Theorem A.28 (ii): "With an
embedding and a readout, the same holds for networks of analytic blocks of any depth `L ≥ 1`, also
under pre-RMSNorm with `ε > 0`." Theorem A.28 (iv): "almost every choice of weights of the
residual network `F` has a finite set `X` of inputs and a `δ > 0` such that every such skipless
network `G` has `‖G(x) − F(x)‖ ≥ δ` at some `x ∈ X`."

Here for the networks of `Network/Transformer.lean`: `L ≥ 1` blocks that are attention blocks
and MLP blocks (`Arch.attentionMlp`), or attention blocks and gated blocks
(`Arch.attentionGated`), in any order, heads of width `1 ≤ d_h ≤ d`, blocks of any widths,
`d_in, d_out ≥ d ≥ 2`, a mask with a token that sees itself and another token; for every
activation with the conclusion of Lemma B.3, and named for tanh, GELU, SwiGLU and GeGLU blocks.
The skipless network has the same architecture; its parameters `η` are any. The twins:
`Residual/DifferentClasses.lean`, `DifferentClassesRMS.lean` (MLP and gated blocks),
`Residual/DifferentClassesAttention.lean` (attention blocks). Sard's theorem and the property of
definable sets are hypotheses from the literature (`Literature/Sard.lean`,
`Literature/OMinimal.lean`).
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {sees : T → T → Prop} [DecidableRel sees]
variable {H dh hid : Fin L → Type} [∀ ℓ, Fintype (H ℓ)] [∀ ℓ, Fintype (dh ℓ)]
  [∀ ℓ, Fintype (hid ℓ)] {σ σ' : ℝ → ℝ} {ε : ℝ}


/-! ### Attention blocks and MLP blocks -/

/-- **Theorem 4.11 (i) of the skips paper, "equals no skipless network of the same widths", for
attention blocks and MLP blocks, without normalization, given Sard's theorem** (Theorem A.28
(ii)): at generic parameters the residual network computes a function that no skipless network of
the same widths computes. -/
theorem ae_forall_eval_residual_ne_skipless_attentionMlp
    (hSard : ∀ r : ℕ, SardCriticalValues (Params
      (Arch.attentionMlp (T := T) (d := d) sees σ id H dh hid) dIn dOut) (Fin r → ℝ))
    (hσ : ∀ z, HasDerivAt σ (σ' z) z) (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (hU : UnitsRigid σ σ' dIn dOut (Σ ℓ, hid ℓ))
    (μ : Measure (Params
      (Arch.attentionMlp (T := T) (d := d) sees σ id H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (hL : 0 < L) (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ θ ∂μ, ∀ η : Params
        (Arch.attentionMlp (T := T) (d := d) sees σ id H dh hid) dIn dOut,
      eval (Arch.attentionMlp sees σ id H dh hid) 1 θ
        ≠ eval (Arch.attentionMlp sees σ id H dh hid) 0 η := by
  sorry

/-- **Theorem A.28 (iv) of the skips paper for attention blocks and MLP blocks, without
normalization, given Sard's theorem and the property of definable sets:** there is a finite batch
`X` such that for almost every `θ` some `δ > 0` has, for every skipless network `η` of the same
widths, `‖F_θ(x) − G_η(x)‖ ≥ δ` at some `x ∈ X`. -/
theorem exists_batch_ae_exists_pos_le_norm_sub_skipless_attentionMlp
    (hSard : ∀ r : ℕ, SardCriticalValues (Params
      (Arch.attentionMlp (T := T) (d := d) sees σ id H dh hid) dIn dOut) (Fin r → ℝ))
    (hOmin : ∀ (n : ℕ) (X : Fin n → Matrix T dIn ℝ),
      ClosureNullOfNull (Set.range (evalBatch (dOut := dOut)
        (Arch.attentionMlp (T := T) (d := d) sees σ id H dh hid) 0 X)))
    (hσ : ∀ z, HasDerivAt σ (σ' z) z) (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (hU : UnitsRigid σ σ' dIn dOut (Σ ℓ, hid ℓ))
    (μ : Measure (Params
      (Arch.attentionMlp (T := T) (d := d) sees σ id H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (hL : 0 < L) (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), ∀ᵐ θ ∂μ, ∃ δ : ℝ, 0 < δ ∧
      ∀ η : Params
          (Arch.attentionMlp (T := T) (d := d) sees σ id H dh hid) dIn dOut,
        ∃ i, δ ≤ ‖eval (Arch.attentionMlp sees σ id H dh hid) 1 θ (X i)
          - eval (Arch.attentionMlp sees σ id H dh hid) 0 η (X i)‖ := by
  sorry

/-- **Theorem 4.11 (i) of the skips paper, "is not a pointwise limit of such networks", for
attention blocks and MLP blocks, without normalization, given Sard's theorem and the property of
definable sets** (Theorem A.28 (iv), Definition A.29). -/
theorem ae_not_isPointwiseLimit_skipless_attentionMlp
    (hSard : ∀ r : ℕ, SardCriticalValues (Params
      (Arch.attentionMlp (T := T) (d := d) sees σ id H dh hid) dIn dOut) (Fin r → ℝ))
    (hOmin : ∀ (n : ℕ) (X : Fin n → Matrix T dIn ℝ),
      ClosureNullOfNull (Set.range (evalBatch (dOut := dOut)
        (Arch.attentionMlp (T := T) (d := d) sees σ id H dh hid) 0 X)))
    (hσ : ∀ z, HasDerivAt σ (σ' z) z) (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (hU : UnitsRigid σ σ' dIn dOut (Σ ℓ, hid ℓ))
    (μ : Measure (Params
      (Arch.attentionMlp (T := T) (d := d) sees σ id H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (hL : 0 < L) (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ θ ∂μ, ¬ IsPointwiseLimit
      (Set.range (eval (Arch.attentionMlp (T := T) (d := d) sees σ id H dh hid) 0 :
        Params (Arch.attentionMlp (T := T) (d := d) sees σ id H dh hid) dIn dOut →
          Matrix T dIn ℝ → Matrix T dOut ℝ))
      (eval (Arch.attentionMlp sees σ id H dh hid) 1 θ) := by
  sorry

/-- **Theorem 4.11 (i) of the skips paper, "equals no skipless network of the same widths", for
attention blocks and MLP blocks, under pre-RMSNorm with `ε > 0`, given Sard's theorem** (Theorem
A.28 (ii)): at generic parameters the residual network computes a function that no skipless
network of the same widths computes. -/
theorem ae_forall_eval_residual_ne_skipless_attentionMlp_rmsNorm (hε : 0 < ε)
    (hSard : ∀ r : ℕ, SardCriticalValues (Params
      (Arch.attentionMlp (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut) (Fin r → ℝ))
    (hσ : ∀ z, HasDerivAt σ (σ' z) z) (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (hU : UnitsRigid σ σ' d d (Σ ℓ, hid ℓ))
    (μ : Measure (Params
      (Arch.attentionMlp (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (hL : 0 < L) (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ θ ∂μ, ∀ η : Params
        (Arch.attentionMlp (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut,
      eval (Arch.attentionMlp sees σ (rmsNorm ε) H dh hid) 1 θ
        ≠ eval (Arch.attentionMlp sees σ (rmsNorm ε) H dh hid) 0 η := by
  sorry

/-- **Theorem A.28 (iv) of the skips paper for attention blocks and MLP blocks, under pre-RMSNorm
with `ε > 0`, given Sard's theorem and the property of definable sets:** there is a finite batch
`X` such that for almost every `θ` some `δ > 0` has, for every skipless network `η` of the same
widths, `‖F_θ(x) − G_η(x)‖ ≥ δ` at some `x ∈ X`. -/
theorem exists_batch_ae_exists_pos_le_norm_sub_skipless_attentionMlp_rmsNorm (hε : 0 < ε)
    (hSard : ∀ r : ℕ, SardCriticalValues (Params
      (Arch.attentionMlp (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut) (Fin r → ℝ))
    (hOmin : ∀ (n : ℕ) (X : Fin n → Matrix T dIn ℝ),
      ClosureNullOfNull (Set.range (evalBatch (dOut := dOut)
        (Arch.attentionMlp (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) 0 X)))
    (hσ : ∀ z, HasDerivAt σ (σ' z) z) (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (hU : UnitsRigid σ σ' d d (Σ ℓ, hid ℓ))
    (μ : Measure (Params
      (Arch.attentionMlp (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (hL : 0 < L) (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), ∀ᵐ θ ∂μ, ∃ δ : ℝ, 0 < δ ∧
      ∀ η : Params
          (Arch.attentionMlp (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut,
        ∃ i, δ ≤ ‖eval (Arch.attentionMlp sees σ (rmsNorm ε) H dh hid) 1 θ (X i)
          - eval (Arch.attentionMlp sees σ (rmsNorm ε) H dh hid) 0 η (X i)‖ := by
  sorry

/-- **Theorem 4.11 (i) of the skips paper, "is not a pointwise limit of such networks", for
attention blocks and MLP blocks, under pre-RMSNorm with `ε > 0`, given Sard's theorem and the
property of definable sets** (Theorem A.28 (iv), Definition A.29). -/
theorem ae_not_isPointwiseLimit_skipless_attentionMlp_rmsNorm (hε : 0 < ε)
    (hSard : ∀ r : ℕ, SardCriticalValues (Params
      (Arch.attentionMlp (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut) (Fin r → ℝ))
    (hOmin : ∀ (n : ℕ) (X : Fin n → Matrix T dIn ℝ),
      ClosureNullOfNull (Set.range (evalBatch (dOut := dOut)
        (Arch.attentionMlp (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) 0 X)))
    (hσ : ∀ z, HasDerivAt σ (σ' z) z) (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (hU : UnitsRigid σ σ' d d (Σ ℓ, hid ℓ))
    (μ : Measure (Params
      (Arch.attentionMlp (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (hL : 0 < L) (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ θ ∂μ, ¬ IsPointwiseLimit
      (Set.range (eval (Arch.attentionMlp (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) 0 :
        Params (Arch.attentionMlp (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut →
          Matrix T dIn ℝ → Matrix T dOut ℝ))
      (eval (Arch.attentionMlp sees σ (rmsNorm ε) H dh hid) 1 θ) := by
  sorry

/-- **Theorem 4.11 (i) of the skips paper, "equals no skipless network of the same widths", for
attention blocks and tanh blocks, without normalization, given Sard's theorem** (Theorem A.28
(ii)): at generic parameters the residual network computes a function that no skipless network of
the same widths computes. -/
theorem ae_forall_eval_residual_ne_skipless_attention_tanh
    (hSard : ∀ r : ℕ, SardCriticalValues (Params
      (Arch.attentionMlp (T := T) (d := d) sees Real.tanh id H dh hid) dIn dOut) (Fin r → ℝ))
    (μ : Measure (Params
      (Arch.attentionMlp (T := T) (d := d) sees Real.tanh id H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (hL : 0 < L) (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ θ ∂μ, ∀ η : Params
        (Arch.attentionMlp (T := T) (d := d) sees Real.tanh id H dh hid) dIn dOut,
      eval (Arch.attentionMlp sees Real.tanh id H dh hid) 1 θ
        ≠ eval (Arch.attentionMlp sees Real.tanh id H dh hid) 0 η := by
  sorry

/-- **Theorem 4.11 (i) of the skips paper, "is not a pointwise limit of such networks", for
attention blocks and tanh blocks, without normalization, given Sard's theorem and the property of
definable sets** (Theorem A.28 (iv), Definition A.29). -/
theorem ae_not_isPointwiseLimit_skipless_attention_tanh
    (hSard : ∀ r : ℕ, SardCriticalValues (Params
      (Arch.attentionMlp (T := T) (d := d) sees Real.tanh id H dh hid) dIn dOut) (Fin r → ℝ))
    (hOmin : ∀ (n : ℕ) (X : Fin n → Matrix T dIn ℝ),
      ClosureNullOfNull (Set.range (evalBatch (dOut := dOut)
        (Arch.attentionMlp (T := T) (d := d) sees Real.tanh id H dh hid) 0 X)))
    (μ : Measure (Params
      (Arch.attentionMlp (T := T) (d := d) sees Real.tanh id H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (hL : 0 < L) (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ θ ∂μ, ¬ IsPointwiseLimit
      (Set.range (eval (Arch.attentionMlp (T := T) (d := d) sees Real.tanh id H dh hid) 0 :
        Params (Arch.attentionMlp (T := T) (d := d) sees Real.tanh id H dh hid) dIn dOut →
          Matrix T dIn ℝ → Matrix T dOut ℝ))
      (eval (Arch.attentionMlp sees Real.tanh id H dh hid) 1 θ) := by
  sorry

/-- **Theorem 4.11 (i) of the skips paper, "equals no skipless network of the same widths", for
attention blocks and tanh blocks, under pre-RMSNorm with `ε > 0`, given Sard's theorem** (Theorem
A.28 (ii)): at generic parameters the residual network computes a function that no skipless
network of the same widths computes. -/
theorem ae_forall_eval_residual_ne_skipless_attention_tanh_rmsNorm (hε : 0 < ε)
    (hSard : ∀ r : ℕ, SardCriticalValues (Params
      (Arch.attentionMlp (T := T) (d := d) sees Real.tanh (rmsNorm ε) H dh hid) dIn dOut)
      (Fin r → ℝ))
    (μ : Measure (Params
      (Arch.attentionMlp (T := T) (d := d) sees Real.tanh (rmsNorm ε) H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (hL : 0 < L) (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ θ ∂μ, ∀ η : Params
        (Arch.attentionMlp (T := T) (d := d) sees Real.tanh (rmsNorm ε) H dh hid) dIn dOut,
      eval (Arch.attentionMlp sees Real.tanh (rmsNorm ε) H dh hid) 1 θ
        ≠ eval (Arch.attentionMlp sees Real.tanh (rmsNorm ε) H dh hid) 0 η := by
  sorry

/-- **Theorem 4.11 (i) of the skips paper, "is not a pointwise limit of such networks", for
attention blocks and tanh blocks, under pre-RMSNorm with `ε > 0`, given Sard's theorem and the
property of definable sets** (Theorem A.28 (iv), Definition A.29). -/
theorem ae_not_isPointwiseLimit_skipless_attention_tanh_rmsNorm (hε : 0 < ε)
    (hSard : ∀ r : ℕ, SardCriticalValues (Params
      (Arch.attentionMlp (T := T) (d := d) sees Real.tanh (rmsNorm ε) H dh hid) dIn dOut)
      (Fin r → ℝ))
    (hOmin : ∀ (n : ℕ) (X : Fin n → Matrix T dIn ℝ),
      ClosureNullOfNull (Set.range (evalBatch (dOut := dOut)
        (Arch.attentionMlp (T := T) (d := d) sees Real.tanh (rmsNorm ε) H dh hid) 0 X)))
    (μ : Measure (Params
      (Arch.attentionMlp (T := T) (d := d) sees Real.tanh (rmsNorm ε) H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (hL : 0 < L) (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ θ ∂μ, ¬ IsPointwiseLimit
      (Set.range (eval (Arch.attentionMlp (T := T) (d := d) sees Real.tanh (rmsNorm ε) H dh hid) 0 :
        Params (Arch.attentionMlp (T := T) (d := d) sees Real.tanh (rmsNorm ε) H dh hid) dIn dOut →
          Matrix T dIn ℝ → Matrix T dOut ℝ))
      (eval (Arch.attentionMlp sees Real.tanh (rmsNorm ε) H dh hid) 1 θ) := by
  sorry

/-- **Theorem 4.11 (i) of the skips paper, "equals no skipless network of the same widths", for
attention blocks and GELU blocks, without normalization, given Sard's theorem** (Theorem A.28
(ii)): at generic parameters the residual network computes a function that no skipless network of
the same widths computes. -/
theorem ae_forall_eval_residual_ne_skipless_attention_gelu
    (hSard : ∀ r : ℕ, SardCriticalValues (Params
      (Arch.attentionMlp (T := T) (d := d) sees gelu id H dh hid) dIn dOut) (Fin r → ℝ))
    (μ : Measure (Params
      (Arch.attentionMlp (T := T) (d := d) sees gelu id H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (hL : 0 < L) (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ θ ∂μ, ∀ η : Params
        (Arch.attentionMlp (T := T) (d := d) sees gelu id H dh hid) dIn dOut,
      eval (Arch.attentionMlp sees gelu id H dh hid) 1 θ
        ≠ eval (Arch.attentionMlp sees gelu id H dh hid) 0 η := by
  sorry

/-- **Theorem 4.11 (i) of the skips paper, "is not a pointwise limit of such networks", for
attention blocks and GELU blocks, without normalization, given Sard's theorem and the property of
definable sets** (Theorem A.28 (iv), Definition A.29). -/
theorem ae_not_isPointwiseLimit_skipless_attention_gelu
    (hSard : ∀ r : ℕ, SardCriticalValues (Params
      (Arch.attentionMlp (T := T) (d := d) sees gelu id H dh hid) dIn dOut) (Fin r → ℝ))
    (hOmin : ∀ (n : ℕ) (X : Fin n → Matrix T dIn ℝ),
      ClosureNullOfNull (Set.range (evalBatch (dOut := dOut)
        (Arch.attentionMlp (T := T) (d := d) sees gelu id H dh hid) 0 X)))
    (μ : Measure (Params
      (Arch.attentionMlp (T := T) (d := d) sees gelu id H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (hL : 0 < L) (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ θ ∂μ, ¬ IsPointwiseLimit
      (Set.range (eval (Arch.attentionMlp (T := T) (d := d) sees gelu id H dh hid) 0 :
        Params (Arch.attentionMlp (T := T) (d := d) sees gelu id H dh hid) dIn dOut →
          Matrix T dIn ℝ → Matrix T dOut ℝ))
      (eval (Arch.attentionMlp sees gelu id H dh hid) 1 θ) := by
  sorry

/-- **Theorem 4.11 (i) of the skips paper, "equals no skipless network of the same widths", for
attention blocks and GELU blocks, under pre-RMSNorm with `ε > 0`, given Sard's theorem** (Theorem
A.28 (ii)): at generic parameters the residual network computes a function that no skipless
network of the same widths computes. -/
theorem ae_forall_eval_residual_ne_skipless_attention_gelu_rmsNorm (hε : 0 < ε)
    (hSard : ∀ r : ℕ, SardCriticalValues (Params
      (Arch.attentionMlp (T := T) (d := d) sees gelu (rmsNorm ε) H dh hid) dIn dOut) (Fin r → ℝ))
    (μ : Measure (Params
      (Arch.attentionMlp (T := T) (d := d) sees gelu (rmsNorm ε) H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (hL : 0 < L) (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ θ ∂μ, ∀ η : Params
        (Arch.attentionMlp (T := T) (d := d) sees gelu (rmsNorm ε) H dh hid) dIn dOut,
      eval (Arch.attentionMlp sees gelu (rmsNorm ε) H dh hid) 1 θ
        ≠ eval (Arch.attentionMlp sees gelu (rmsNorm ε) H dh hid) 0 η := by
  sorry

/-- **Theorem 4.11 (i) of the skips paper, "is not a pointwise limit of such networks", for
attention blocks and GELU blocks, under pre-RMSNorm with `ε > 0`, given Sard's theorem and the
property of definable sets** (Theorem A.28 (iv), Definition A.29). -/
theorem ae_not_isPointwiseLimit_skipless_attention_gelu_rmsNorm (hε : 0 < ε)
    (hSard : ∀ r : ℕ, SardCriticalValues (Params
      (Arch.attentionMlp (T := T) (d := d) sees gelu (rmsNorm ε) H dh hid) dIn dOut) (Fin r → ℝ))
    (hOmin : ∀ (n : ℕ) (X : Fin n → Matrix T dIn ℝ),
      ClosureNullOfNull (Set.range (evalBatch (dOut := dOut)
        (Arch.attentionMlp (T := T) (d := d) sees gelu (rmsNorm ε) H dh hid) 0 X)))
    (μ : Measure (Params
      (Arch.attentionMlp (T := T) (d := d) sees gelu (rmsNorm ε) H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (hL : 0 < L) (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ θ ∂μ, ¬ IsPointwiseLimit
      (Set.range (eval (Arch.attentionMlp (T := T) (d := d) sees gelu (rmsNorm ε) H dh hid) 0 :
        Params (Arch.attentionMlp (T := T) (d := d) sees gelu (rmsNorm ε) H dh hid) dIn dOut →
          Matrix T dIn ℝ → Matrix T dOut ℝ))
      (eval (Arch.attentionMlp sees gelu (rmsNorm ε) H dh hid) 1 θ) := by
  sorry


/-! ### Attention blocks and gated blocks -/

/-- **Theorem 4.11 (i) of the skips paper, "equals no skipless network of the same widths", for
attention blocks and gated blocks, without normalization, given Sard's theorem** (Theorem A.28
(ii)): at generic parameters the residual network computes a function that no skipless network of
the same widths computes. -/
theorem ae_forall_eval_residual_ne_skipless_attentionGated
    (hSard : ∀ r : ℕ, SardCriticalValues (Params
      (Arch.attentionGated (T := T) (d := d) sees σ id H dh hid) dIn dOut) (Fin r → ℝ))
    (hσ : ∀ z, HasDerivAt σ (σ' z) z) (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (hU : GatedUnitsRescale σ σ' dIn dOut (Σ ℓ, hid ℓ))
    (μ : Measure (Params
      (Arch.attentionGated (T := T) (d := d) sees σ id H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (hL : 0 < L) (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ θ ∂μ, ∀ η : Params
        (Arch.attentionGated (T := T) (d := d) sees σ id H dh hid) dIn dOut,
      eval (Arch.attentionGated sees σ id H dh hid) 1 θ
        ≠ eval (Arch.attentionGated sees σ id H dh hid) 0 η := by
  sorry

/-- **Theorem A.28 (iv) of the skips paper for attention blocks and gated blocks, without
normalization, given Sard's theorem and the property of definable sets:** there is a finite batch
`X` such that for almost every `θ` some `δ > 0` has, for every skipless network `η` of the same
widths, `‖F_θ(x) − G_η(x)‖ ≥ δ` at some `x ∈ X`. -/
theorem exists_batch_ae_exists_pos_le_norm_sub_skipless_attentionGated
    (hSard : ∀ r : ℕ, SardCriticalValues (Params
      (Arch.attentionGated (T := T) (d := d) sees σ id H dh hid) dIn dOut) (Fin r → ℝ))
    (hOmin : ∀ (n : ℕ) (X : Fin n → Matrix T dIn ℝ),
      ClosureNullOfNull (Set.range (evalBatch (dOut := dOut)
        (Arch.attentionGated (T := T) (d := d) sees σ id H dh hid) 0 X)))
    (hσ : ∀ z, HasDerivAt σ (σ' z) z) (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (hU : GatedUnitsRescale σ σ' dIn dOut (Σ ℓ, hid ℓ))
    (μ : Measure (Params
      (Arch.attentionGated (T := T) (d := d) sees σ id H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (hL : 0 < L) (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), ∀ᵐ θ ∂μ, ∃ δ : ℝ, 0 < δ ∧
      ∀ η : Params
          (Arch.attentionGated (T := T) (d := d) sees σ id H dh hid) dIn dOut,
        ∃ i, δ ≤ ‖eval (Arch.attentionGated sees σ id H dh hid) 1 θ (X i)
          - eval (Arch.attentionGated sees σ id H dh hid) 0 η (X i)‖ := by
  sorry

/-- **Theorem 4.11 (i) of the skips paper, "is not a pointwise limit of such networks", for
attention blocks and gated blocks, without normalization, given Sard's theorem and the property of
definable sets** (Theorem A.28 (iv), Definition A.29). -/
theorem ae_not_isPointwiseLimit_skipless_attentionGated
    (hSard : ∀ r : ℕ, SardCriticalValues (Params
      (Arch.attentionGated (T := T) (d := d) sees σ id H dh hid) dIn dOut) (Fin r → ℝ))
    (hOmin : ∀ (n : ℕ) (X : Fin n → Matrix T dIn ℝ),
      ClosureNullOfNull (Set.range (evalBatch (dOut := dOut)
        (Arch.attentionGated (T := T) (d := d) sees σ id H dh hid) 0 X)))
    (hσ : ∀ z, HasDerivAt σ (σ' z) z) (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (hU : GatedUnitsRescale σ σ' dIn dOut (Σ ℓ, hid ℓ))
    (μ : Measure (Params
      (Arch.attentionGated (T := T) (d := d) sees σ id H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (hL : 0 < L) (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ θ ∂μ, ¬ IsPointwiseLimit
      (Set.range (eval (Arch.attentionGated (T := T) (d := d) sees σ id H dh hid) 0 :
        Params (Arch.attentionGated (T := T) (d := d) sees σ id H dh hid) dIn dOut →
          Matrix T dIn ℝ → Matrix T dOut ℝ))
      (eval (Arch.attentionGated sees σ id H dh hid) 1 θ) := by
  sorry

/-- **Theorem 4.11 (i) of the skips paper, "equals no skipless network of the same widths", for
attention blocks and gated blocks, under pre-RMSNorm with `ε > 0`, given Sard's theorem** (Theorem
A.28 (ii)): at generic parameters the residual network computes a function that no skipless
network of the same widths computes. -/
theorem ae_forall_eval_residual_ne_skipless_attentionGated_rmsNorm (hε : 0 < ε)
    (hSard : ∀ r : ℕ, SardCriticalValues (Params
      (Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut) (Fin r → ℝ))
    (hσ : ∀ z, HasDerivAt σ (σ' z) z) (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (hU : GatedUnitsRescale σ σ' d d (Σ ℓ, hid ℓ))
    (μ : Measure (Params
      (Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (hL : 0 < L) (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ θ ∂μ, ∀ η : Params
        (Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut,
      eval (Arch.attentionGated sees σ (rmsNorm ε) H dh hid) 1 θ
        ≠ eval (Arch.attentionGated sees σ (rmsNorm ε) H dh hid) 0 η := by
  sorry

/-- **Theorem A.28 (iv) of the skips paper for attention blocks and gated blocks, under
pre-RMSNorm with `ε > 0`, given Sard's theorem and the property of definable sets:** there is a
finite batch `X` such that for almost every `θ` some `δ > 0` has, for every skipless network `η`
of the same widths, `‖F_θ(x) − G_η(x)‖ ≥ δ` at some `x ∈ X`. -/
theorem exists_batch_ae_exists_pos_le_norm_sub_skipless_attentionGated_rmsNorm (hε : 0 < ε)
    (hSard : ∀ r : ℕ, SardCriticalValues (Params
      (Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut) (Fin r → ℝ))
    (hOmin : ∀ (n : ℕ) (X : Fin n → Matrix T dIn ℝ),
      ClosureNullOfNull (Set.range (evalBatch (dOut := dOut)
        (Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) 0 X)))
    (hσ : ∀ z, HasDerivAt σ (σ' z) z) (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (hU : GatedUnitsRescale σ σ' d d (Σ ℓ, hid ℓ))
    (μ : Measure (Params
      (Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (hL : 0 < L) (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), ∀ᵐ θ ∂μ, ∃ δ : ℝ, 0 < δ ∧
      ∀ η : Params
          (Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut,
        ∃ i, δ ≤ ‖eval (Arch.attentionGated sees σ (rmsNorm ε) H dh hid) 1 θ (X i)
          - eval (Arch.attentionGated sees σ (rmsNorm ε) H dh hid) 0 η (X i)‖ := by
  sorry

/-- **Theorem 4.11 (i) of the skips paper, "is not a pointwise limit of such networks", for
attention blocks and gated blocks, under pre-RMSNorm with `ε > 0`, given Sard's theorem and the
property of definable sets** (Theorem A.28 (iv), Definition A.29). -/
theorem ae_not_isPointwiseLimit_skipless_attentionGated_rmsNorm (hε : 0 < ε)
    (hSard : ∀ r : ℕ, SardCriticalValues (Params
      (Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut) (Fin r → ℝ))
    (hOmin : ∀ (n : ℕ) (X : Fin n → Matrix T dIn ℝ),
      ClosureNullOfNull (Set.range (evalBatch (dOut := dOut)
        (Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) 0 X)))
    (hσ : ∀ z, HasDerivAt σ (σ' z) z) (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (hU : GatedUnitsRescale σ σ' d d (Σ ℓ, hid ℓ))
    (μ : Measure (Params
      (Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (hL : 0 < L) (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ θ ∂μ, ¬ IsPointwiseLimit
      (Set.range (eval (Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) 0 :
        Params (Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut →
          Matrix T dIn ℝ → Matrix T dOut ℝ))
      (eval (Arch.attentionGated sees σ (rmsNorm ε) H dh hid) 1 θ) := by
  sorry

/-- **Theorem 4.11 (i) of the skips paper, "equals no skipless network of the same widths", for
attention blocks and SwiGLU blocks, without normalization, given Sard's theorem** (Theorem A.28
(ii)): at generic parameters the residual network computes a function that no skipless network of
the same widths computes. -/
theorem ae_forall_eval_residual_ne_skipless_attention_swiglu
    (hSard : ∀ r : ℕ, SardCriticalValues (Params
      (Arch.attentionGated (T := T) (d := d) sees silu id H dh hid) dIn dOut) (Fin r → ℝ))
    (μ : Measure (Params
      (Arch.attentionGated (T := T) (d := d) sees silu id H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (hL : 0 < L) (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ θ ∂μ, ∀ η : Params
        (Arch.attentionGated (T := T) (d := d) sees silu id H dh hid) dIn dOut,
      eval (Arch.attentionGated sees silu id H dh hid) 1 θ
        ≠ eval (Arch.attentionGated sees silu id H dh hid) 0 η := by
  sorry

/-- **Theorem 4.11 (i) of the skips paper, "is not a pointwise limit of such networks", for
attention blocks and SwiGLU blocks, without normalization, given Sard's theorem and the property
of definable sets** (Theorem A.28 (iv), Definition A.29). -/
theorem ae_not_isPointwiseLimit_skipless_attention_swiglu
    (hSard : ∀ r : ℕ, SardCriticalValues (Params
      (Arch.attentionGated (T := T) (d := d) sees silu id H dh hid) dIn dOut) (Fin r → ℝ))
    (hOmin : ∀ (n : ℕ) (X : Fin n → Matrix T dIn ℝ),
      ClosureNullOfNull (Set.range (evalBatch (dOut := dOut)
        (Arch.attentionGated (T := T) (d := d) sees silu id H dh hid) 0 X)))
    (μ : Measure (Params
      (Arch.attentionGated (T := T) (d := d) sees silu id H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (hL : 0 < L) (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ θ ∂μ, ¬ IsPointwiseLimit
      (Set.range (eval (Arch.attentionGated (T := T) (d := d) sees silu id H dh hid) 0 :
        Params (Arch.attentionGated (T := T) (d := d) sees silu id H dh hid) dIn dOut →
          Matrix T dIn ℝ → Matrix T dOut ℝ))
      (eval (Arch.attentionGated sees silu id H dh hid) 1 θ) := by
  sorry

/-- **Theorem 4.11 (i) of the skips paper, "equals no skipless network of the same widths", for
attention blocks and SwiGLU blocks, under pre-RMSNorm with `ε > 0`, given Sard's theorem**
(Theorem A.28 (ii)): at generic parameters the residual network computes a function that no
skipless network of the same widths computes. -/
theorem ae_forall_eval_residual_ne_skipless_attention_swiglu_rmsNorm (hε : 0 < ε)
    (hSard : ∀ r : ℕ, SardCriticalValues (Params
      (Arch.attentionGated (T := T) (d := d) sees silu (rmsNorm ε) H dh hid) dIn dOut) (Fin r → ℝ))
    (μ : Measure (Params
      (Arch.attentionGated (T := T) (d := d) sees silu (rmsNorm ε) H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (hL : 0 < L) (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ θ ∂μ, ∀ η : Params
        (Arch.attentionGated (T := T) (d := d) sees silu (rmsNorm ε) H dh hid) dIn dOut,
      eval (Arch.attentionGated sees silu (rmsNorm ε) H dh hid) 1 θ
        ≠ eval (Arch.attentionGated sees silu (rmsNorm ε) H dh hid) 0 η := by
  sorry

/-- **Theorem 4.11 (i) of the skips paper, "is not a pointwise limit of such networks", for
attention blocks and SwiGLU blocks, under pre-RMSNorm with `ε > 0`, given Sard's theorem and the
property of definable sets** (Theorem A.28 (iv), Definition A.29). -/
theorem ae_not_isPointwiseLimit_skipless_attention_swiglu_rmsNorm (hε : 0 < ε)
    (hSard : ∀ r : ℕ, SardCriticalValues (Params
      (Arch.attentionGated (T := T) (d := d) sees silu (rmsNorm ε) H dh hid) dIn dOut) (Fin r → ℝ))
    (hOmin : ∀ (n : ℕ) (X : Fin n → Matrix T dIn ℝ),
      ClosureNullOfNull (Set.range (evalBatch (dOut := dOut)
        (Arch.attentionGated (T := T) (d := d) sees silu (rmsNorm ε) H dh hid) 0 X)))
    (μ : Measure (Params
      (Arch.attentionGated (T := T) (d := d) sees silu (rmsNorm ε) H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (hL : 0 < L) (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ θ ∂μ, ¬ IsPointwiseLimit
      (Set.range (eval (Arch.attentionGated (T := T) (d := d) sees silu (rmsNorm ε) H dh hid) 0 :
        Params (Arch.attentionGated (T := T) (d := d) sees silu (rmsNorm ε) H dh hid) dIn dOut →
          Matrix T dIn ℝ → Matrix T dOut ℝ))
      (eval (Arch.attentionGated sees silu (rmsNorm ε) H dh hid) 1 θ) := by
  sorry

/-- **Theorem 4.11 (i) of the skips paper, "equals no skipless network of the same widths", for
attention blocks and GeGLU blocks, without normalization, given Sard's theorem** (Theorem A.28
(ii)): at generic parameters the residual network computes a function that no skipless network of
the same widths computes. -/
theorem ae_forall_eval_residual_ne_skipless_attention_geglu
    (hSard : ∀ r : ℕ, SardCriticalValues (Params
      (Arch.attentionGated (T := T) (d := d) sees gelu id H dh hid) dIn dOut) (Fin r → ℝ))
    (μ : Measure (Params
      (Arch.attentionGated (T := T) (d := d) sees gelu id H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (hL : 0 < L) (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ θ ∂μ, ∀ η : Params
        (Arch.attentionGated (T := T) (d := d) sees gelu id H dh hid) dIn dOut,
      eval (Arch.attentionGated sees gelu id H dh hid) 1 θ
        ≠ eval (Arch.attentionGated sees gelu id H dh hid) 0 η := by
  sorry

/-- **Theorem 4.11 (i) of the skips paper, "is not a pointwise limit of such networks", for
attention blocks and GeGLU blocks, without normalization, given Sard's theorem and the property of
definable sets** (Theorem A.28 (iv), Definition A.29). -/
theorem ae_not_isPointwiseLimit_skipless_attention_geglu
    (hSard : ∀ r : ℕ, SardCriticalValues (Params
      (Arch.attentionGated (T := T) (d := d) sees gelu id H dh hid) dIn dOut) (Fin r → ℝ))
    (hOmin : ∀ (n : ℕ) (X : Fin n → Matrix T dIn ℝ),
      ClosureNullOfNull (Set.range (evalBatch (dOut := dOut)
        (Arch.attentionGated (T := T) (d := d) sees gelu id H dh hid) 0 X)))
    (μ : Measure (Params
      (Arch.attentionGated (T := T) (d := d) sees gelu id H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (hL : 0 < L) (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ θ ∂μ, ¬ IsPointwiseLimit
      (Set.range (eval (Arch.attentionGated (T := T) (d := d) sees gelu id H dh hid) 0 :
        Params (Arch.attentionGated (T := T) (d := d) sees gelu id H dh hid) dIn dOut →
          Matrix T dIn ℝ → Matrix T dOut ℝ))
      (eval (Arch.attentionGated sees gelu id H dh hid) 1 θ) := by
  sorry

/-- **Theorem 4.11 (i) of the skips paper, "equals no skipless network of the same widths", for
attention blocks and GeGLU blocks, under pre-RMSNorm with `ε > 0`, given Sard's theorem** (Theorem
A.28 (ii)): at generic parameters the residual network computes a function that no skipless
network of the same widths computes. -/
theorem ae_forall_eval_residual_ne_skipless_attention_geglu_rmsNorm (hε : 0 < ε)
    (hSard : ∀ r : ℕ, SardCriticalValues (Params
      (Arch.attentionGated (T := T) (d := d) sees gelu (rmsNorm ε) H dh hid) dIn dOut) (Fin r → ℝ))
    (μ : Measure (Params
      (Arch.attentionGated (T := T) (d := d) sees gelu (rmsNorm ε) H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (hL : 0 < L) (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ θ ∂μ, ∀ η : Params
        (Arch.attentionGated (T := T) (d := d) sees gelu (rmsNorm ε) H dh hid) dIn dOut,
      eval (Arch.attentionGated sees gelu (rmsNorm ε) H dh hid) 1 θ
        ≠ eval (Arch.attentionGated sees gelu (rmsNorm ε) H dh hid) 0 η := by
  sorry

/-- **Theorem 4.11 (i) of the skips paper, "is not a pointwise limit of such networks", for
attention blocks and GeGLU blocks, under pre-RMSNorm with `ε > 0`, given Sard's theorem and the
property of definable sets** (Theorem A.28 (iv), Definition A.29). -/
theorem ae_not_isPointwiseLimit_skipless_attention_geglu_rmsNorm (hε : 0 < ε)
    (hSard : ∀ r : ℕ, SardCriticalValues (Params
      (Arch.attentionGated (T := T) (d := d) sees gelu (rmsNorm ε) H dh hid) dIn dOut) (Fin r → ℝ))
    (hOmin : ∀ (n : ℕ) (X : Fin n → Matrix T dIn ℝ),
      ClosureNullOfNull (Set.range (evalBatch (dOut := dOut)
        (Arch.attentionGated (T := T) (d := d) sees gelu (rmsNorm ε) H dh hid) 0 X)))
    (μ : Measure (Params
      (Arch.attentionGated (T := T) (d := d) sees gelu (rmsNorm ε) H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (hL : 0 < L) (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ θ ∂μ, ¬ IsPointwiseLimit
      (Set.range (eval (Arch.attentionGated (T := T) (d := d) sees gelu (rmsNorm ε) H dh hid) 0 :
        Params (Arch.attentionGated (T := T) (d := d) sees gelu (rmsNorm ε) H dh hid) dIn dOut →
          Matrix T dIn ℝ → Matrix T dOut ℝ))
      (eval (Arch.attentionGated sees gelu (rmsNorm ε) H dh hid) 1 θ) := by
  sorry

end Skips
