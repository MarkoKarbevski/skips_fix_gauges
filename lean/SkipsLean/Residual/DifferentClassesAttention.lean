import SkipsLean.Residual.SkiplessEndsAttention
import SkipsLean.Residual.DifferentClassesCriterion
import SkipsLean.Residual.DepthAttentionDim
import SkipsLean.Residual.DepthAttentionRMSDim

/-!
# Residual and skipless networks of attention blocks: different function classes

Paper (skips paper): Theorem 4.11 (Different function classes), part (i): "For analytic blocks,
with or without pre-RMSNorm, a residual network at generic parameters equals no skipless network
of the same widths, and is not a pointwise limit of such networks." Theorem A.28 (ii): "With an
embedding and a readout, the same holds for networks of analytic blocks of any depth `L ≥ 1`, also
under pre-RMSNorm with `ε > 0`." Theorem A.28 (iv): "almost every choice of weights of the
residual network `F` has a finite set `X` of inputs and a `δ > 0` such that every such skipless
network `G` has `‖G(x) − F(x)‖ ≥ δ` at some `x ∈ X`."

Here for networks of attention blocks (`Arch.attention`), the twin of
`Residual/DifferentClasses.lean` and `Residual/DifferentClassesRMS.lean` (MLP and gated blocks):
`L ≥ 1` attention blocks with heads of width `1 ≤ d_h ≤ d` (any numbers of heads),
`d_in, d_out ≥ d ≥ 2`, and a mask with a token that sees itself and another token. The skipless
network has the same architecture (the same heads, widths and mask); its parameters `η` are any.

The proof of Theorem A.28 (ii): the residual network has functional dimension `P − d² − s` at
some parameters (`Residual/DepthAttentionDim.lean`), resp. `P − d(d−1)/2 − s` under pre-RMSNorm
(`Residual/DepthAttentionRMSDim.lean`); the skipless network has rank at most `P − 2 d² − s`,
resp. `P − d(d−1) − s`, at every parameter (`Residual/SkiplessEndsAttention.lean`); Lemma A.26
(`Residual/DifferentClassesCriterion.lean`). Sard's theorem and the property of definable sets
are hypotheses from the literature (`Literature/Sard.lean`, `Literature/OMinimal.lean`).
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {sees : T → T → Prop} [DecidableRel sees]
variable {H dh : Fin L → Type} [∀ ℓ, Fintype (H ℓ)] [∀ ℓ, Fintype (dh ℓ)] {ε : ℝ}

/-! ### Without normalization -/

/-- **Theorem 4.11 (i) of the skips paper, "equals no skipless network of the same widths", for
attention blocks without normalization, given Sard's theorem** (Theorem A.28 (ii)): with
`d_in, d_out ≥ d ≥ 2`, `L ≥ 1` attention blocks with heads of width `1 ≤ d_h ≤ d` and a token
that sees itself and another token, at generic parameters the residual network computes a
function that no skipless network of the same widths computes. -/
theorem ae_forall_eval_residual_ne_skipless_attention
    (hSard : ∀ r : ℕ, SardCriticalValues
      (Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut) (Fin r → ℝ))
    (μ : Measure (Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (hL : 0 < L) (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ θ ∂μ, ∀ η : Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut,
      eval (Arch.attention sees id H dh) 1 θ ≠ eval (Arch.attention sees id H dh) 0 η := by
  sorry

/-- **Theorem A.28 (iv) of the skips paper for attention blocks without normalization, given
Sard's theorem and the property of definable sets:** there is a finite batch `X` such that for
almost every `θ` some `δ > 0` has, for every skipless network `η` of the same widths,
`‖F_θ(x) − G_η(x)‖ ≥ δ` at some `x ∈ X`. -/
theorem exists_batch_ae_exists_pos_le_norm_sub_skipless_attention
    (hSard : ∀ r : ℕ, SardCriticalValues
      (Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut) (Fin r → ℝ))
    (hOmin : ∀ (n : ℕ) (X : Fin n → Matrix T dIn ℝ),
      ClosureNullOfNull (Set.range
        (evalBatch (dOut := dOut) (Arch.attention (T := T) (d := d) sees id H dh) 0 X)))
    (μ : Measure (Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (hL : 0 < L) (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), ∀ᵐ θ ∂μ, ∃ δ : ℝ, 0 < δ ∧
      ∀ η : Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut,
        ∃ i, δ ≤ ‖eval (Arch.attention sees id H dh) 1 θ (X i)
          - eval (Arch.attention sees id H dh) 0 η (X i)‖ := by
  sorry

/-- **Theorem 4.11 (i) of the skips paper, "is not a pointwise limit of such networks", for
attention blocks without normalization, given Sard's theorem and the property of definable sets**
(Theorem A.28 (iv), Definition A.29): at generic parameters the residual network is not a
pointwise limit of the skipless networks of the same widths. -/
theorem ae_not_isPointwiseLimit_skipless_attention
    (hSard : ∀ r : ℕ, SardCriticalValues
      (Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut) (Fin r → ℝ))
    (hOmin : ∀ (n : ℕ) (X : Fin n → Matrix T dIn ℝ),
      ClosureNullOfNull (Set.range
        (evalBatch (dOut := dOut) (Arch.attention (T := T) (d := d) sees id H dh) 0 X)))
    (μ : Measure (Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (hL : 0 < L) (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ θ ∂μ, ¬ IsPointwiseLimit
      (Set.range (eval (Arch.attention (T := T) (d := d) sees id H dh) 0 :
        Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut →
          Matrix T dIn ℝ → Matrix T dOut ℝ))
      (eval (Arch.attention sees id H dh) 1 θ) := by
  sorry

/-! ### Under pre-RMSNorm with `ε > 0` -/

/-- **Theorem 4.11 (i) of the skips paper, "equals no skipless network of the same widths", for
attention blocks under pre-RMSNorm with `ε > 0`, given Sard's theorem** (Theorem A.28 (ii)). -/
theorem ae_forall_eval_residual_ne_skipless_attention_rmsNorm (hε : 0 < ε)
    (hSard : ∀ r : ℕ, SardCriticalValues
      (Params (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut) (Fin r → ℝ))
    (μ : Measure (Params (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (hL : 0 < L) (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ θ ∂μ, ∀ η : Params (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut,
      eval (Arch.attention sees (rmsNorm ε) H dh) 1 θ
        ≠ eval (Arch.attention sees (rmsNorm ε) H dh) 0 η := by
  sorry

/-- **Theorem A.28 (iv) of the skips paper for attention blocks under pre-RMSNorm with `ε > 0`,
given Sard's theorem and the property of definable sets.** -/
theorem exists_batch_ae_exists_pos_le_norm_sub_skipless_attention_rmsNorm (hε : 0 < ε)
    (hSard : ∀ r : ℕ, SardCriticalValues
      (Params (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut) (Fin r → ℝ))
    (hOmin : ∀ (n : ℕ) (X : Fin n → Matrix T dIn ℝ),
      ClosureNullOfNull (Set.range
        (evalBatch (dOut := dOut) (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) 0 X)))
    (μ : Measure (Params (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (hL : 0 < L) (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), ∀ᵐ θ ∂μ, ∃ δ : ℝ, 0 < δ ∧
      ∀ η : Params (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut,
        ∃ i, δ ≤ ‖eval (Arch.attention sees (rmsNorm ε) H dh) 1 θ (X i)
          - eval (Arch.attention sees (rmsNorm ε) H dh) 0 η (X i)‖ := by
  sorry

/-- **Theorem 4.11 (i) of the skips paper, "is not a pointwise limit of such networks", for
attention blocks under pre-RMSNorm with `ε > 0`, given Sard's theorem and the property of
definable sets** (Theorem A.28 (iv), Definition A.29). -/
theorem ae_not_isPointwiseLimit_skipless_attention_rmsNorm (hε : 0 < ε)
    (hSard : ∀ r : ℕ, SardCriticalValues
      (Params (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut) (Fin r → ℝ))
    (hOmin : ∀ (n : ℕ) (X : Fin n → Matrix T dIn ℝ),
      ClosureNullOfNull (Set.range
        (evalBatch (dOut := dOut) (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) 0 X)))
    (μ : Measure (Params (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (hL : 0 < L) (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ θ ∂μ, ¬ IsPointwiseLimit
      (Set.range (eval (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) 0 :
        Params (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut →
          Matrix T dIn ℝ → Matrix T dOut ℝ))
      (eval (Arch.attention sees (rmsNorm ε) H dh) 1 θ) := by
  sorry

end Skips
