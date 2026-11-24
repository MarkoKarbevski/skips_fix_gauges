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

/-- The two ingredients of Lemma A.26 for attention blocks without normalization (proof of
Theorem A.28 (ii)): a bound `r₀ = P − 2 d² − s` on the rank of the Jacobian of the skipless
network at every parameter and on every batch, and one residual parameter `θ₀` whose functional
dimension `P − d² − s` exceeds it (as `d ≥ 2`). -/
private theorem exists_rank_gap_attention_dca
    (μ : Measure (Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (hL : 0 < L) (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∃ r₀ : ℕ, (∀ (n : ℕ) (X : Fin n → Matrix T dIn ℝ)
        (η : Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut),
        jacobianRank (Arch.attention sees id H dh) 0 X η ≤ r₀) ∧
      ∃ θ₀ : Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut,
        r₀ < funDim (Arch.attention sees id H dh) 1 θ₀ := by
  classical
  -- one residual parameter `θ₀` of functional dimension `P − d² − s` (Theorem 4.7)
  obtain ⟨θ₀, hθ₀⟩ :=
    (ae_funDim_attention_residual μ hd hdIn hdOut hdh hdh0 t₁ t₂ h12 hs2 hs1).exists
  -- the skipless network has rank at most `P − 2 d² − s` at every parameter, on every batch
  have hbound := fun (n : ℕ) (X : Fin n → Matrix T dIn ℝ)
      (η : Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut) =>
    jacobianRank_add_le_skipless_ends_attention hL hdIn hdOut hdh η X
  have h0 := hbound 0 (fun i => i.elim0) θ₀
  -- `k = d² ≥ 1`, so `P − 2 k − s < P − k − s`
  have hk : 1 ≤ Fintype.card d ^ 2 := Nat.one_le_pow _ _ (by omega)
  refine ⟨Module.finrank ℝ (Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut)
    - (2 * Fintype.card d ^ 2 + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2),
    fun n X η => ?_, θ₀, ?_⟩
  · have := hbound n X η
    omega
  · generalize Fintype.card d ^ 2 = k at hθ₀ h0 hk ⊢
    omega

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
  -- Lemma A.26 (i) with `F` the residual and `G` the skipless networks of the same widths
  obtain ⟨r₀, hr₀, θ₀, hθ₀⟩ :=
    exists_rank_gap_attention_dca μ hd hdIn hdOut hdh hdh0 hL t₁ t₂ h12 hs2 hs1
  exact ae_forall_eval_ne_of_jacobianRank_lt
    (Arch.attention sees id H dh) 1 (Arch.attention sees id H dh) 0 hSard
    (fun ℓ => analyticOnNhd_f_attention sees id H dh ℓ) analyticOnNhd_id
    (fun ℓ => analyticOnNhd_f_attention sees id H dh ℓ) analyticOnNhd_id r₀ hr₀ θ₀ hθ₀ μ

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
  -- Lemma A.26 (ii) with `F` the residual and `G` the skipless networks of the same widths
  obtain ⟨r₀, hr₀, θ₀, hθ₀⟩ :=
    exists_rank_gap_attention_dca μ hd hdIn hdOut hdh hdh0 hL t₁ t₂ h12 hs2 hs1
  exact exists_batch_ae_exists_pos_le_norm_sub_of_jacobianRank_lt
    (Arch.attention sees id H dh) 1 (Arch.attention sees id H dh) 0 hSard hOmin
    (fun ℓ => analyticOnNhd_f_attention sees id H dh ℓ) analyticOnNhd_id
    (fun ℓ => analyticOnNhd_f_attention sees id H dh ℓ) analyticOnNhd_id r₀ hr₀ θ₀ hθ₀ μ

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
  -- Theorem A.28 (iv) with `F` the residual and `G` the skipless networks of the same widths
  obtain ⟨r₀, hr₀, θ₀, hθ₀⟩ :=
    exists_rank_gap_attention_dca μ hd hdIn hdOut hdh hdh0 hL t₁ t₂ h12 hs2 hs1
  exact ae_not_isPointwiseLimit_of_jacobianRank_lt
    (Arch.attention sees id H dh) 1 (Arch.attention sees id H dh) 0 hSard hOmin
    (fun ℓ => analyticOnNhd_f_attention sees id H dh ℓ) analyticOnNhd_id
    (fun ℓ => analyticOnNhd_f_attention sees id H dh ℓ) analyticOnNhd_id r₀ hr₀ θ₀ hθ₀ μ

/-! ### Under pre-RMSNorm with `ε > 0` -/

/-- The two ingredients of Lemma A.26 for attention blocks under pre-RMSNorm with `ε > 0` (proof
of Theorem A.28 (ii)): a bound `r₀ = P − d (d − 1) − s` on the rank of the Jacobian of the
skipless network at every parameter and on every batch, and one residual parameter `θ₀` whose
functional dimension `P − d (d − 1) / 2 − s` exceeds it (as `d ≥ 2`). -/
private theorem exists_rank_gap_attention_rmsNorm_dca (hε : 0 < ε)
    (μ : Measure (Params (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (hL : 0 < L) (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∃ r₀ : ℕ, (∀ (n : ℕ) (X : Fin n → Matrix T dIn ℝ)
        (η : Params (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut),
        jacobianRank (Arch.attention sees (rmsNorm ε) H dh) 0 X η ≤ r₀) ∧
      ∃ θ₀ : Params (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut,
        r₀ < funDim (Arch.attention sees (rmsNorm ε) H dh) 1 θ₀ := by
  classical
  -- one residual parameter `θ₀` of functional dimension `P − d (d − 1) / 2 − s` (Theorem 4.7)
  obtain ⟨θ₀, hθ₀⟩ :=
    (ae_funDim_attention_residual_rmsNorm hε μ hd hdIn hdOut hdh hdh0 t₁ t₂ h12 hs2 hs1).exists
  -- the skipless network has rank at most `P − d (d − 1) − s` at every parameter, on every batch
  have hbound := fun (n : ℕ) (X : Fin n → Matrix T dIn ℝ)
      (η : Params (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut) =>
    jacobianRank_add_le_skipless_ends_attention_rmsNorm hε hL hdIn hdOut hdh η X
  have h0 := hbound 0 (fun i => i.elim0) θ₀
  -- `k = d (d − 1) ≥ 2`, so `k / 2 < k`
  have hk : 2 ≤ Fintype.card d * (Fintype.card d - 1) :=
    le_trans (by norm_num) (Nat.mul_le_mul hd (by omega : 1 ≤ Fintype.card d - 1))
  refine ⟨Module.finrank ℝ
      (Params (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut)
    - (Fintype.card d * (Fintype.card d - 1)
      + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2), fun n X η => ?_, θ₀, ?_⟩
  · have := hbound n X η
    omega
  · generalize Fintype.card d * (Fintype.card d - 1) = k at hθ₀ h0 hk ⊢
    omega

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
  -- Lemma A.26 (i) with `F` the residual and `G` the skipless networks of the same widths
  obtain ⟨r₀, hr₀, θ₀, hθ₀⟩ :=
    exists_rank_gap_attention_rmsNorm_dca hε μ hd hdIn hdOut hdh hdh0 hL t₁ t₂ h12 hs2 hs1
  exact ae_forall_eval_ne_of_jacobianRank_lt
    (Arch.attention sees (rmsNorm ε) H dh) 1 (Arch.attention sees (rmsNorm ε) H dh) 0 hSard
    (fun ℓ => analyticOnNhd_f_attention sees (rmsNorm ε) H dh ℓ) (analyticOnNhd_rmsNorm hε)
    (fun ℓ => analyticOnNhd_f_attention sees (rmsNorm ε) H dh ℓ) (analyticOnNhd_rmsNorm hε)
    r₀ hr₀ θ₀ hθ₀ μ

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
  -- Lemma A.26 (ii) with `F` the residual and `G` the skipless networks of the same widths
  obtain ⟨r₀, hr₀, θ₀, hθ₀⟩ :=
    exists_rank_gap_attention_rmsNorm_dca hε μ hd hdIn hdOut hdh hdh0 hL t₁ t₂ h12 hs2 hs1
  exact exists_batch_ae_exists_pos_le_norm_sub_of_jacobianRank_lt
    (Arch.attention sees (rmsNorm ε) H dh) 1 (Arch.attention sees (rmsNorm ε) H dh) 0 hSard hOmin
    (fun ℓ => analyticOnNhd_f_attention sees (rmsNorm ε) H dh ℓ) (analyticOnNhd_rmsNorm hε)
    (fun ℓ => analyticOnNhd_f_attention sees (rmsNorm ε) H dh ℓ) (analyticOnNhd_rmsNorm hε)
    r₀ hr₀ θ₀ hθ₀ μ

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
  -- Theorem A.28 (iv) with `F` the residual and `G` the skipless networks of the same widths
  obtain ⟨r₀, hr₀, θ₀, hθ₀⟩ :=
    exists_rank_gap_attention_rmsNorm_dca hε μ hd hdIn hdOut hdh hdh0 hL t₁ t₂ h12 hs2 hs1
  exact ae_not_isPointwiseLimit_of_jacobianRank_lt
    (Arch.attention sees (rmsNorm ε) H dh) 1 (Arch.attention sees (rmsNorm ε) H dh) 0 hSard hOmin
    (fun ℓ => analyticOnNhd_f_attention sees (rmsNorm ε) H dh ℓ) (analyticOnNhd_rmsNorm hε)
    (fun ℓ => analyticOnNhd_f_attention sees (rmsNorm ε) H dh ℓ) (analyticOnNhd_rmsNorm hε)
    r₀ hr₀ θ₀ hθ₀ μ

end Skips
