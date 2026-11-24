import SkipsLean.Residual.SmallWrites
import SkipsLean.Residual.UpperBoundSymmetries
import SkipsLean.OneBlock.SwiGLU
import SkipsLean.OneBlock.GeGLU
import SkipsLean.Activations.Analytic

/-!
# Residual networks of SwiGLU and GeGLU blocks at any depth

Paper (skips paper): Lemma A.27 (Small writes), its first value `fd(θ_τ) = P - d² - s`, and
Theorem 4.7 (Equality for residual networks at any depth), both without normalization and without
biases, for gated blocks: SwiGLU and GeGLU. Here `s` is the number of hidden units of all blocks
(one rescaling per hidden unit). The blocks may have any widths.

As in `Residual/DepthMlp.lean`, with Lemma B.3 for gated units (`GatedUnitsRescale`) applied to the
hidden units of all blocks together: "the read of a unit has a gate and a value", and a direction
`η` that is flat for the limit `J_0` has `η_E = E X`, `η_D = -X D`, no component at the gates, and
rescales every hidden unit: its value column is multiplied by `-α_{ℓ,i}` and its row of the write
by `α_{ℓ,i}`. These directions form a space of dimension `d² + s`.
-/

namespace Skips

open Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d]
  [Fintype dIn] [Fintype dOut]
variable {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]
variable {σ σ' : ℝ → ℝ}

/-- **The conditions on `θ` in Lemma A.27, for gated blocks without normalization:** `E` and `D`
have rank `d`, and the hypotheses of Lemma B.3 hold for the units of all blocks together: with
`c_{ℓ,i}` the gate columns and `e_{ℓ,i}` the value columns of `E W_read^ℓ`, and `a_{ℓ,i}` the rows
of `W_write^ℓ D`, every `a_{ℓ,i}` and every `e_{ℓ,i}` is nonzero, and the `c_{ℓ,i}`, over all blocks
`ℓ` and hidden units `i`, are nonzero and pairwise non-collinear. -/
structure SmallWritesGenericGated
    (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) : Prop where
  rank_E : θ.E.rank = Fintype.card d
  rank_D : θ.D.rank = Fintype.card d
  /-- every row `a_{ℓ,i}` of `W_write^ℓ D` is nonzero -/
  row_ne_zero : ∀ ℓ i, (θ.write ℓ * θ.D) i ≠ 0
  /-- every gate column `c_{ℓ,i}` of `E W_read^ℓ` is nonzero -/
  gate_ne_zero : ∀ ℓ (i : hid ℓ), (θ.E * θ.read ℓ)ᵀ (Sum.inl i) ≠ 0
  /-- the gate columns of all blocks together are pairwise non-collinear -/
  gate_not_collinear : ∀ p q : (Σ ℓ, hid ℓ), p ≠ q → ∀ r : ℝ,
    (θ.E * θ.read p.1)ᵀ (Sum.inl p.2) ≠ r • (θ.E * θ.read q.1)ᵀ (Sum.inl q.2)
  /-- every value column `e_{ℓ,i}` of `E W_read^ℓ` is nonzero -/
  value_ne_zero : ∀ ℓ (i : hid ℓ), (θ.E * θ.read ℓ)ᵀ (Sum.inr i) ≠ 0

/-- **Proof of Lemma A.27, gated blocks without normalization, the flat directions of `J_0`:**
under the conditions of the lemma, a direction `η` with `(J_0 η)(x) = 0` at every input `x` has
`η_E = E X` and `η_D = -X D` for one matrix `X`, vanishes at every gate column of a read, and
rescales every hidden unit: for numbers `α_{ℓ,i}`, the value column of unit `i` of block `ℓ` in
`η_read^ℓ` is `-α_{ℓ,i}` times that of `W_read^ℓ`, and its row in `η_write^ℓ` is `α_{ℓ,i}` times that
of `W_write^ℓ`. Stated for every gate that satisfies the conclusion of Lemma B.3
(`GatedUnitsRescale`) for the hidden units of all blocks together. -/
theorem smallWritesLimit_eq_zero_gated (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hU : GatedUnitsRescale σ σ' dIn dOut (Σ ℓ, hid ℓ))
    (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (hθ : SmallWritesGenericGated θ)
    (η : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (hη : ∀ x, smallWritesLimit (Arch.gated σ id hid) θ η x = 0) :
    ∃ (X : Matrix d d ℝ) (α : ∀ ℓ, hid ℓ → ℝ), η.E = θ.E * X ∧ η.D = -(X * θ.D)
      ∧ (∀ ℓ (i : hid ℓ) a, η.read ℓ a (Sum.inl i) = 0)
      ∧ (∀ ℓ (i : hid ℓ) a, η.read ℓ a (Sum.inr i) = -(α ℓ i) * θ.read ℓ a (Sum.inr i))
      ∧ (∀ ℓ (i : hid ℓ) a, η.write ℓ i a = α ℓ i * θ.write ℓ i a) := by
  sorry

/-- **Lemma A.27 (Small writes), first value, for gated blocks, under the conditions of its
proof:** for all small `τ ≠ 0` the residual network has `fd(θ_τ) = P - d² - s`, with `s` the number
of hidden units. -/
theorem eventually_funDim_smallWrites_gated (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hσa : AnalyticOnNhd ℝ σ Set.univ) (hU : GatedUnitsRescale σ σ' dIn dOut (Σ ℓ, hid ℓ))
    (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (hθ : SmallWritesGenericGated θ) :
    ∀ᶠ τ in 𝓝[≠] (0 : ℝ),
      funDim (Arch.gated σ id hid) 1 (θ.smallWrites τ)
          + (Fintype.card d ^ 2 + ∑ ℓ, Fintype.card (hid ℓ))
        = Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) := by
  sorry

/-- The conditions of Lemma A.27 for gated blocks hold at generic parameters, for
`d_in, d_out ≥ d ≥ 2` and blocks of any widths. -/
theorem ae_smallWritesGenericGated
    (μ : Measure (Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)) [μ.IsAddHaarMeasure]
    (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, SmallWritesGenericGated θ := by
  sorry

/-- **Lemma A.27 (Small writes), first value, for gated blocks:** with `d_in, d_out ≥ d ≥ 2` and
blocks of any widths, for generic parameters `θ` and all small `τ ≠ 0`, the residual network has
`fd(θ_τ) = P - d² - s`. -/
theorem ae_eventually_funDim_smallWrites_gated (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hσa : AnalyticOnNhd ℝ σ Set.univ) (hU : GatedUnitsRescale σ σ' dIn dOut (Σ ℓ, hid ℓ))
    (μ : Measure (Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)) [μ.IsAddHaarMeasure]
    (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, ∀ᶠ τ in 𝓝[≠] (0 : ℝ),
      funDim (Arch.gated σ id hid) 1 (θ.smallWrites τ)
          + (Fintype.card d ^ 2 + ∑ ℓ, Fintype.card (hid ℓ))
        = Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) := by
  sorry

/-- **Theorem 4.7 of the skips paper for gated blocks, without normalization:** with
`d_in, d_out ≥ d ≥ 2` and `L` blocks of any widths, at generic parameters the residual network has
the functional dimension `P - d² - s`, with `s` the number of hidden units. -/
theorem ae_funDim_gated_residual (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hσa : AnalyticOnNhd ℝ σ Set.univ) (hU : GatedUnitsRescale σ σ' dIn dOut (Σ ℓ, hid ℓ))
    (μ : Measure (Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)) [μ.IsAddHaarMeasure]
    (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, funDim (Arch.gated σ id hid) 1 θ
        + (Fintype.card d ^ 2 + ∑ ℓ, Fintype.card (hid ℓ))
      = Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) := by
  sorry

/-! ### The two kinds of block -/

/-- **Lemma A.27 (Small writes) for SwiGLU blocks, without normalization and without biases.** -/
theorem ae_eventually_funDim_smallWrites_swiglu
    (μ : Measure (Params (Arch.gated (T := T) (d := d) silu id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, ∀ᶠ τ in 𝓝[≠] (0 : ℝ),
      funDim (Arch.gated silu id hid) 1 (θ.smallWrites τ)
          + (Fintype.card d ^ 2 + ∑ ℓ, Fintype.card (hid ℓ))
        = Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) silu id hid) dIn dOut) := by
  sorry

/-- **Lemma A.27 (Small writes) for GeGLU blocks, without normalization and without biases.** -/
theorem ae_eventually_funDim_smallWrites_geglu
    (μ : Measure (Params (Arch.gated (T := T) (d := d) gelu id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, ∀ᶠ τ in 𝓝[≠] (0 : ℝ),
      funDim (Arch.gated gelu id hid) 1 (θ.smallWrites τ)
          + (Fintype.card d ^ 2 + ∑ ℓ, Fintype.card (hid ℓ))
        = Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) gelu id hid) dIn dOut) := by
  sorry

/-- **Theorem 4.7 of the skips paper for SwiGLU blocks, without normalization:** at generic
parameters the residual network of `L` blocks has the functional dimension `P - d² - s`. -/
theorem ae_funDim_swiglu_residual
    (μ : Measure (Params (Arch.gated (T := T) (d := d) silu id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, funDim (Arch.gated silu id hid) 1 θ
        + (Fintype.card d ^ 2 + ∑ ℓ, Fintype.card (hid ℓ))
      = Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) silu id hid) dIn dOut) := by
  sorry

/-- **Theorem 4.7 of the skips paper for GeGLU blocks, without normalization:** at generic
parameters the residual network of `L` blocks has the functional dimension `P - d² - s`. -/
theorem ae_funDim_geglu_residual
    (μ : Measure (Params (Arch.gated (T := T) (d := d) gelu id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, funDim (Arch.gated gelu id hid) 1 θ
        + (Fintype.card d ^ 2 + ∑ ℓ, Fintype.card (hid ℓ))
      = Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) gelu id hid) dIn dOut) := by
  sorry

end Skips
