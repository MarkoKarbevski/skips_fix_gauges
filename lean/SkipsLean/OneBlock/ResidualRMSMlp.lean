import SkipsLean.OneBlock.ResidualRMSSteps
import SkipsLean.OneBlock.Tanh
import SkipsLean.OneBlock.GELU
import SkipsLean.Activations.Analytic

/-!
# One residual `tanh` or GELU block under pre-RMSNorm

Paper (skips paper): Theorem 4.6 (ii), first sentence (Theorem B.1 (ii) in the appendix), for
`ε > 0` and no biases, for MLP blocks whose hidden units have no symmetry of their own (`s = 0`):
`tanh` blocks and GELU blocks. At generic parameters the residual network of one block has the
functional dimension `P - d(d-1)/2`. The block may have any width.

Steps 1 to 3 of the proof are in `OneBlock/ResidualRMSSteps.lean`. Here:

* Step 4 (the block): the derivative of `n ↦ f(n W_read) W_write` along the entries of `η'`
  vanishes for every `n` in the image of `x ↦ N_ε(x E)`, an open set of hidden states (the open
  ball of radius `√d` in the paper), since `E` has rank `d`. For a real-analytic activation it then
  vanishes for all `n`. "So Lemma B.3, with `E` and `D` replaced by the identity and `M = 0`",
  gives `η'_read = 0` and `η'_write = 0` (`UnitsRigid` with the columns of `W_read` and the rows of
  `W_write`).
* Step 5 (counting): the flat directions are those of the orthogonal change of basis,
  `cobDir θ (fun _ => Y)` with `Y` antisymmetric; "an antisymmetric `Y` with `E Y = 0` vanishes",
  so `dim K(θ) = d(d-1)/2`.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {hid : Fin 1 → Type} [∀ ℓ, Fintype (hid ℓ)]
variable {σ σ' : ℝ → ℝ} {ε : ℝ}

/-- **The conditions on `θ` in the proof of Theorem B.1 (ii), for one MLP block:** `E` and `D`
have rank `d`, and the hypotheses of Lemma B.3 hold "with `E` and `D` replaced by the identity":
every row of `W_write` is nonzero, and the columns of `W_read` are nonzero and pairwise
non-collinear. -/
structure OneBlockGenericRMS
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut) : Prop where
  rank_E : θ.E.rank = Fintype.card d
  rank_D : θ.D.rank = Fintype.card d
  /-- every row of `W_write` is nonzero -/
  row_ne_zero : ∀ i, θ.write 0 i ≠ 0
  /-- every column of `W_read` is nonzero -/
  col_ne_zero : ∀ i, (θ.read 0)ᵀ i ≠ 0
  /-- the columns of `W_read` are pairwise non-collinear -/
  col_not_collinear : ∀ i j, i ≠ j → ∀ r : ℝ, (θ.read 0)ᵀ i ≠ r • (θ.read 0)ᵀ j

/-- **Proof of Theorem B.1 (ii), Steps 1 to 4, for one MLP block with `s = 0`:** under the
conditions of the proof, every flat direction of the residual network under pre-RMSNorm
(`ε > 0`) is the direction of one antisymmetric `Y` at both hidden states. -/
theorem flat_le_cobDir_const_mlp_residual_rmsNorm (hε : 0 < ε)
    (hσ : ∀ z, HasDerivAt σ (σ' z) z) (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (hU : UnitsRigid σ σ' d d (hid 0))
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)
    (hθ : OneBlockGenericRMS θ)
    (η : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)
    (hη : η ∈ flat (Arch.mlp σ (rmsNorm ε) hid) 1 θ) :
    ∃ Y : Matrix d d ℝ, Yᵀ = -Y ∧ η = cobDir θ (fun _ => Y) := by
  sorry

/-- **Theorem 4.6 (ii) of the skips paper, first sentence, for one MLP block with `s = 0`, under
the conditions of its proof:** under pre-RMSNorm with `ε > 0` the residual network has the
functional dimension `P - d(d-1)/2`. -/
theorem funDim_mlp_oneBlock_residual_rmsNorm (hε : 0 < ε)
    (hσ : ∀ z, HasDerivAt σ (σ' z) z) (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (hU : UnitsRigid σ σ' d d (hid 0))
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)
    (hθ : OneBlockGenericRMS θ) :
    funDim (Arch.mlp σ (rmsNorm ε) hid) 1 θ + Fintype.card d * (Fintype.card d - 1) / 2
      = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut) := by
  sorry

/-- The conditions of the proof hold at generic parameters, for `d_in, d_out ≥ d ≥ 2` and a block
of any width. -/
theorem ae_oneBlockGenericRMS
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, OneBlockGenericRMS θ := by
  sorry

/-- **Theorem 4.6 (ii) of the skips paper, first sentence, for one MLP block with `s = 0`:** with
`d_in, d_out ≥ d ≥ 2` and a block of any width, under pre-RMSNorm with `ε > 0`, at generic
parameters the residual network has the functional dimension `P - d(d-1)/2`. -/
theorem ae_funDim_mlp_oneBlock_residual_rmsNorm (hε : 0 < ε)
    (hσ : ∀ z, HasDerivAt σ (σ' z) z) (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (hU : UnitsRigid σ σ' d d (hid 0))
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, funDim (Arch.mlp σ (rmsNorm ε) hid) 1 θ
        + Fintype.card d * (Fintype.card d - 1) / 2
      = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut) := by
  sorry

/-! ### The two kinds of block -/

/-- **Theorem 4.6 (ii) of the skips paper, first sentence, for a `tanh` block:** under pre-RMSNorm
with `ε > 0`, at generic parameters the residual network of one block has the functional
dimension `P - d(d-1)/2`. -/
theorem ae_funDim_tanh_oneBlock_residual_rmsNorm (hε : 0 < ε)
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) Real.tanh (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, funDim (Arch.mlp Real.tanh (rmsNorm ε) hid) 1 θ
        + Fintype.card d * (Fintype.card d - 1) / 2
      = Module.finrank ℝ
          (Params (Arch.mlp (T := T) (d := d) Real.tanh (rmsNorm ε) hid) dIn dOut) := by
  sorry

/-- **Theorem 4.6 (ii) of the skips paper, first sentence, for a GELU block.** -/
theorem ae_funDim_gelu_oneBlock_residual_rmsNorm (hε : 0 < ε)
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, funDim (Arch.mlp gelu (rmsNorm ε) hid) 1 θ
        + Fintype.card d * (Fintype.card d - 1) / 2
      = Module.finrank ℝ
          (Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm ε) hid) dIn dOut) := by
  sorry

end Skips
