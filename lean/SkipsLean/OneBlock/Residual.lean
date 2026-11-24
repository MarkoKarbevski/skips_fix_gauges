import SkipsLean.OneBlock.Tanh
import SkipsLean.OneBlock.GELU
import SkipsLean.OneBlock.SwiGLU
import SkipsLean.OneBlock.GeGLU

/-!
# The one-block theorem with a skip connection

Paper (skips paper): Theorem 4.6 (i) (Theorem B.1 (i) in the appendix), without normalization and
without biases, for the `tanh`, GELU, SwiGLU and GeGLU blocks: with one block of width at least
`d`, at generic parameters the residual network `x ↦ (x E + f(x E W_read) W_write) D` has the
functional dimension `P - d² - s`, and the skip raises the functional dimension by exactly `d²`.

With `M = E D`, `C = E W_read` and `A = W_write D` the residual network computes
`x ↦ x M + f(x C) A`. Lemma C.3 of the dimension paper is stated with a linear term `x M`, so a
flat direction keeps `M`, `C` and `A` to first order, up to the rescalings inside the block. The
directions that keep `C` and `A` are those of two changes of basis `X` at `h_0` and `Y` at `h_1`
(Lemma C.2), and such a direction keeps `M` only if `E (X - Y) D = 0`, that is, `X = Y`
(Lemma B.2 of the skips paper): one change of basis is left.

As for the networks without skips, the theorem is stated for every activation that satisfies the
conclusion of Lemma C.3 (`UnitsRigid`, `GatedUnitsRescale`), under the conditions of
`OneBlockGeneric` and `OneBlockGenericGated`; the four kinds of block follow.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {hid : Fin 1 → Type} [∀ ℓ, Fintype (hid ℓ)]
variable {σ σ' : ℝ → ℝ}

/-! ### MLP blocks without symmetries inside the hidden units -/

/-- Under the conditions, every flat direction of one residual MLP block whose activation
satisfies Lemma C.3 without rescalings is the direction of one change of basis, the same at `h_0`
and at `h_1`. -/
theorem flat_le_range_cobDir_const_mlp_residual (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hU : UnitsRigid σ σ' dIn dOut (hid 0))
    (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) (hθ : OneBlockGeneric θ)
    (η : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)
    (hη : η ∈ flat (Arch.mlp σ id hid) 1 θ) :
    ∃ X : Matrix d d ℝ, η = cobDir θ (fun _ => X) := by
  sorry

/-- **Theorem 4.6 (i) of the skips paper for a residual MLP block with `s = 0`, under the
conditions of its proof:** the functional dimension is `P - d²`. -/
theorem funDim_mlp_oneBlock_residual (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hU : UnitsRigid σ σ' dIn dOut (hid 0))
    (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) (hθ : OneBlockGeneric θ) :
    funDim (Arch.mlp σ id hid) 1 θ + Fintype.card d ^ 2
      = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) := by
  sorry

/-- **Theorem 4.6 (i) of the skips paper for an MLP block with `s = 0`:** with
`d_in, d_out, d_hidden ≥ d ≥ 2`, at generic parameters the residual network has the functional
dimension `P - d²`. -/
theorem ae_funDim_mlp_oneBlock_residual (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hU : UnitsRigid σ σ' dIn dOut (hid 0))
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ θ ∂μ, funDim (Arch.mlp σ id hid) 1 θ + Fintype.card d ^ 2
      = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) :=
  (ae_oneBlockGeneric μ hd hdIn hdOut hhid).mono fun θ hθ =>
    funDim_mlp_oneBlock_residual hσ hU θ hθ

/-- **The skip raises the functional dimension by exactly `d²`** (Theorem 4.6 (i) of the skips
paper), for one MLP block with `s = 0`, at generic parameters. -/
theorem ae_funDim_mlp_oneBlock_residual_eq_add (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hU : UnitsRigid σ σ' dIn dOut (hid 0))
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ θ ∂μ, funDim (Arch.mlp σ id hid) 1 θ
      = funDim (Arch.mlp σ id hid) 0 θ + Fintype.card d ^ 2 := by
  sorry

/-! ### Gated blocks -/

/-- Under the conditions, every flat direction of one residual gated block whose gate activation
satisfies Lemma C.3 is the sum of the direction of one change of basis and of the direction of a
rescaling of the values of the hidden units. -/
theorem flat_le_cobDir_const_add_rescaleDir_gated_residual (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hU : GatedUnitsRescale σ σ' dIn dOut (hid 0))
    (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) (hθ : OneBlockGenericGated θ)
    (η : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (hη : η ∈ flat (Arch.gated σ id hid) 1 θ) :
    ∃ (X : Matrix d d ℝ) (α : ∀ ℓ, hid ℓ → ℝ), η = cobDir θ (fun _ => X) + rescaleDir θ α := by
  sorry

/-- **Theorem 4.6 (i) of the skips paper for a residual SwiGLU or GeGLU block, under the
conditions of its proof:** the functional dimension is `P - d² - d_hidden`. -/
theorem funDim_gated_oneBlock_residual (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hU : GatedUnitsRescale σ σ' dIn dOut (hid 0))
    (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) (hθ : OneBlockGenericGated θ) :
    funDim (Arch.gated σ id hid) 1 θ + (Fintype.card d ^ 2 + Fintype.card (hid 0))
      = Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) := by
  sorry

/-- **Theorem 4.6 (i) of the skips paper for a SwiGLU or GeGLU block:** with
`d_in, d_out, d_hidden ≥ d ≥ 2`, at generic parameters the residual network has the functional
dimension `P - d² - d_hidden`. -/
theorem ae_funDim_gated_oneBlock_residual (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hU : GatedUnitsRescale σ σ' dIn dOut (hid 0))
    (μ : Measure (Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ θ ∂μ, funDim (Arch.gated σ id hid) 1 θ + (Fintype.card d ^ 2 + Fintype.card (hid 0))
      = Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) :=
  (ae_oneBlockGenericGated μ hd hdIn hdOut hhid).mono fun θ hθ =>
    funDim_gated_oneBlock_residual hσ hU θ hθ

/-- **The skip raises the functional dimension by exactly `d²`** (Theorem 4.6 (i) of the skips
paper), for one SwiGLU or GeGLU block, at generic parameters. -/
theorem ae_funDim_gated_oneBlock_residual_eq_add (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hU : GatedUnitsRescale σ σ' dIn dOut (hid 0))
    (μ : Measure (Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ θ ∂μ, funDim (Arch.gated σ id hid) 1 θ
      = funDim (Arch.gated σ id hid) 0 θ + Fintype.card d ^ 2 := by
  sorry

/-! ### The four kinds of block -/

/-- **Theorem 4.6 (i) of the skips paper for a `tanh` block:** the skip raises the functional
dimension by exactly `d²`, at generic parameters. -/
theorem ae_funDim_tanh_oneBlock_residual_eq_add
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) Real.tanh id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ θ ∂μ, funDim (Arch.mlp Real.tanh id hid) 1 θ
      = funDim (Arch.mlp Real.tanh id hid) 0 θ + Fintype.card d ^ 2 :=
  ae_funDim_mlp_oneBlock_residual_eq_add hasDerivAt_tanh (tanh_unitsRigid _ _ _) μ hd hdIn hdOut
    hhid

/-- **Theorem 4.6 (i) of the skips paper for a GELU block.** -/
theorem ae_funDim_gelu_oneBlock_residual_eq_add
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) gelu id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ θ ∂μ, funDim (Arch.mlp gelu id hid) 1 θ
      = funDim (Arch.mlp gelu id hid) 0 θ + Fintype.card d ^ 2 :=
  ae_funDim_mlp_oneBlock_residual_eq_add hasDerivAt_gelu (gelu_unitsRigid _ _ _) μ hd hdIn hdOut
    hhid

/-- **Theorem 4.6 (i) of the skips paper for a SwiGLU block.** -/
theorem ae_funDim_swiglu_oneBlock_residual_eq_add
    (μ : Measure (Params (Arch.gated (T := T) (d := d) silu id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ θ ∂μ, funDim (Arch.gated silu id hid) 1 θ
      = funDim (Arch.gated silu id hid) 0 θ + Fintype.card d ^ 2 :=
  ae_funDim_gated_oneBlock_residual_eq_add hasDerivAt_silu (silu_gatedUnitsRescale _ _ _) μ hd
    hdIn hdOut hhid

/-- **Theorem 4.6 (i) of the skips paper for a GeGLU block.** -/
theorem ae_funDim_geglu_oneBlock_residual_eq_add
    (μ : Measure (Params (Arch.gated (T := T) (d := d) gelu id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ θ ∂μ, funDim (Arch.gated gelu id hid) 1 θ
      = funDim (Arch.gated gelu id hid) 0 θ + Fintype.card d ^ 2 :=
  ae_funDim_gated_oneBlock_residual_eq_add hasDerivAt_gelu (gelu_gatedUnitsRescale _ _ _) μ hd
    hdIn hdOut hhid

end Skips
