import SkipsLean.OneBlock.ResidualRMSZeroReGLU

/-!
# One residual ReGLU block under pre-RMSNorm with `ε = 0`: generic parameters

Paper (skips paper), Theorem B.1 (iv): "Let the network be pre-RMSNorm with `ε = 0`, without
biases, with a ReLU, ReLU² or ReGLU block of width at least `d_model`. For generic parameters the
residual network has functional dimension `P − d_model (d_model − 1)/2 − 1 − s`". For ReGLU
`s = 2 d_hidden`.

`OneBlock/ResidualRMSZeroReGLU.lean` has this value at one parameter under the conditions of the
proof, among them: the block turns a dense set of the rows at which some gate is active
(`TurnsActiveRowsGated`), and it turns some row off the kinks of the gates. Here: these two
conditions at almost every parameter for a ReGLU block with `d ≥ 2` (for every nonempty set `S` of
hidden units, the map `v ↦ ∑_{i ∈ S} (v g_i) (v c_i) a_i`, with `g_i` and `c_i` the gate column
and the value column of unit `i` and `a_i` its row of `W_write`, is at almost every parameter not
parallel to `v` for all `v`, and a nonzero polynomial does not vanish on an open set); and
Theorem B.1 (iv) for the residual network at almost every parameter, as the value of Lean's
`funDim` and as a batch of the paper's inputs with this rank. Twin of
`OneBlock/ResidualRMSZeroRescaleGeneric.lean` (ReLU and ReLU² blocks). No width of the block is
asked; for the batch and the value the block has at least one hidden unit.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {hid : Fin 1 → Type} [∀ ℓ, Fintype (hid ℓ)]

/-- **A ReGLU block turns a dense set of the rows with an active gate at almost every
parameter,** for `d ≥ 2`. -/
theorem ae_turnsActiveRowsGated_reglu
    (μ : Measure (Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) :
    ∀ᵐ θ ∂μ, TurnsActiveRowsGated θ := by
  sorry

/-- **A ReGLU block with a hidden unit turns some row off the kinks of the gates at almost every
parameter,** for `d ≥ 2`. -/
theorem ae_exists_turned_row_reglu [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) :
    ∀ᵐ θ ∂μ, ∃ v : d → ℝ, (∀ i, (v ᵥ* θ.read 0) (Sum.inl i) ≠ 0) ∧
      LinearIndependent ℝ ![v, gatedBlock relu ((θ.read 0).submatrix id Sum.inl)
        ((θ.read 0).submatrix id Sum.inr) (θ.write 0) v] := by
  sorry

/-- **Theorem B.1 (iv) of the skips paper, the residual network, for one ReGLU block:** for
`ε = 0` and `d_in, d_out ≥ d ≥ 2`, at almost every parameter the residual network of one ReGLU
block of any width with at least one hidden unit has `funDim = P − d(d−1)/2 − 1 − 2 d_hidden`. -/
theorem ae_funDim_reglu_oneBlock_residual_rmsNorm_zero [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, funDim (Arch.gated relu (rmsNorm 0) hid) 1 θ
        + ((Fintype.card d * (Fintype.card d - 1) / 2 + 1) + 2 * Fintype.card (hid 0))
      = Module.finrank ℝ
          (Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut) := by
  -- the conditions of the proof hold at generic parameters
  filter_upwards [ae_oneBlockGenericReGLURMS μ hd hdIn hdOut, ae_turnsActiveRowsGated_reglu μ hd,
    ae_exists_turned_row_reglu μ hd] with θ hθ hturn hw
  exact funDim_reglu_oneBlock_residual_rmsNorm_zero θ hθ hd hturn hw

/-- **Theorem B.1 (iv) of the skips paper, the residual network, in the paper's own sense, for
one ReGLU block:** at almost every parameter there is a finite batch of inputs at which no
normalized row vanishes and no gate sits at its kink, on which the Jacobian has the rank
`P − d(d−1)/2 − 1 − 2 d_hidden`. -/
theorem ae_exists_jacobianRank_reglu_oneBlock_residual_rmsNorm_zero [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ),
      (∀ i, X i ∈ residualZeroDomain (Arch.gated relu (rmsNorm 0) hid) θ ∩ noKinkGateRMS θ) ∧
      jacobianRank (Arch.gated relu (rmsNorm 0) hid) 1 X θ
          + ((Fintype.card d * (Fintype.card d - 1) / 2 + 1) + 2 * Fintype.card (hid 0))
        = Module.finrank ℝ
            (Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut) := by
  -- the conditions of the proof hold at generic parameters
  filter_upwards [ae_oneBlockGenericReGLURMS μ hd hdIn hdOut, ae_turnsActiveRowsGated_reglu μ hd,
    ae_exists_turned_row_reglu μ hd] with θ hθ hturn hw
  exact exists_jacobianRank_reglu_oneBlock_residual_rmsNorm_zero θ hθ hd hturn hw

end Skips
