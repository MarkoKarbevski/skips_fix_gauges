import SkipsLean.OneBlock.ResidualRMSStepsOn
import SkipsLean.OneBlock.ResidualRMSGated
import SkipsLean.OneBlock.ReGLU

/-!
# One residual ReGLU block under pre-RMSNorm

Paper (skips paper): Theorem 4.6 (ii), first sentence (Theorem B.1 (ii) in the appendix), for
`ε > 0` and no biases, for a ReGLU block: "For generic parameters the residual network has
functional dimension `P − d_model (d_model − 1)/2 − s`, which is the equality condition. If the
block has width at least `d_model`, the skip raises the functional dimension by at least
`d_model (d_model − 1)/2`." For ReGLU `s = 2 d_hidden`: one rescaling of the gate and one of the
value for each hidden unit.

Its proof, Step 4: "For the ReLU-type activations without biases the kinks lie on hyperplanes
through the center of the ball, and the arguments of Lemma B.3 are local. So Lemma B.3, with `E`
and `D` replaced by the identity and `M = 0`, makes the entries of `η'` at each hidden unit a
rescaling." Step 5: "The flat directions are thus those of the orthogonal change of basis and of
the symmetries inside the block. […] so `dim K(θ) = d_model (d_model − 1)/2 + s`."

Stated here as in `OneBlock/ReGLU.lean` (the same block without normalization),
`OneBlock/ResidualRMSGated.lean` (SwiGLU and GeGLU blocks under pre-RMSNorm) and
`OneBlock/ResidualRMSRescale.lean` (ReLU and ReLU² blocks under pre-RMSNorm):

* `OneBlockGenericReGLURMS θ`: the conditions of the other gated blocks under pre-RMSNorm, and
  no value column of `W_read` is proportional to the gate column of the same hidden unit (the
  hypothesis of Lemma B.3 that only ReGLU uses, "with `E` and `D` replaced by the identity").
* `noKinkGateRMS θ`: the inputs at which no gate sits at its kink (every entry of the gate
  columns of `x E W_read` is nonzero; under pre-RMSNorm with `ε > 0` the block reads a positive
  multiple of each row of `x E`).
* A direction that is flat at these inputs is
  `cobDir θ (fun _ => Y) + rescaleDir θ α + rescaleDirGate 1 θ β` with `Y` antisymmetric.
* The value: `funDim + d(d−1)/2 + 2 d_hidden = P`, and a batch of inputs of `noKinkGateRMS θ`
  with this rank (the paper's functional dimension for these blocks), under the conditions
  `OneBlockGenericReGLURMS` and at almost every parameter, for a block of any width.
* The gain: for a block of at least `d` hidden units the skip raises `funDim` by at least
  `d(d−1)/2`.

Steps 1 to 3 at the inputs of `noKinkGateRMS θ` are `exists_antisymm_of_flatOn_residual_rmsNorm`
(`OneBlock/ResidualRMSStepsOn.lean`); Lemma B.3 for ReGLU is `relu_gated_units_flat`
(`OneBlock/UnitsReGLU.lean`).
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {hid : Fin 1 → Type} [∀ ℓ, Fintype (hid ℓ)]
variable {σ : ℝ → ℝ} {ε : ℝ}

/-- **The conditions on `θ` in the proof of Theorem B.1 (ii), for one ReGLU block:** those of
the other gated blocks under pre-RMSNorm, and no value column of `W_read` is proportional to the
gate column of the same hidden unit. They do not involve the gate activation. -/
structure OneBlockGenericReGLURMS
    (θ : Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut) : Prop where
  /-- the conditions of the other gated blocks under pre-RMSNorm -/
  gated : OneBlockGenericGatedRMS θ
  /-- no value column of `W_read` is proportional to the gate column of the same unit -/
  value_not_gate : ∀ (i : hid 0) (r : ℝ),
    (θ.read 0)ᵀ (Sum.inr i) ≠ r • (θ.read 0)ᵀ (Sum.inl i)

/-- The inputs at which no gate of the block sits at its kink, under pre-RMSNorm: every entry of
the gate columns of `x E W_read` (one per token and hidden unit) is nonzero. -/
def noKinkGateRMS (θ : Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut) :
    Set (Matrix T dIn ℝ) :=
  {x | ∀ (t : T) (i : hid 0), (x * θ.E * θ.read 0) t (Sum.inl i) ≠ 0}

/-- The conditions of the proof hold at generic parameters, for `d_in, d_out ≥ d ≥ 2` and a
block of any width: each is the nonvanishing of polynomials in the weights that do not vanish
identically. -/
theorem ae_oneBlockGenericReGLURMS
    (μ : Measure (Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, OneBlockGenericReGLURMS θ := by
  sorry

/-- **Proof of Theorem B.1 (ii), Steps 1 to 4, for a ReGLU block:** under the conditions
`OneBlockGenericReGLURMS`, a direction that is flat at every input with no gate at its kink is
the direction of an orthogonal change of basis shared by `h_0` and `h_1` plus a rescaling of the
values and a rescaling of the gates of the hidden units. -/
theorem flatOn_noKinkGateRMS_le_reglu_residual_rmsNorm (hε : 0 < ε)
    (θ : Params (Arch.gated (T := T) (d := d) relu (rmsNorm ε) hid) dIn dOut)
    (hθ : OneBlockGenericReGLURMS θ)
    (η : Params (Arch.gated (T := T) (d := d) relu (rmsNorm ε) hid) dIn dOut)
    (hη : η ∈ flatOn (Arch.gated relu (rmsNorm ε) hid) 1 θ (noKinkGateRMS θ)) :
    ∃ (Y : Matrix d d ℝ) (α β : ∀ ℓ, hid ℓ → ℝ), Yᵀ = -Y ∧
      η = cobDir θ (fun _ => Y) + rescaleDir θ α + rescaleDirGate 1 θ β := by
  sorry

/-- **Theorem B.1 (ii), first sentence, for a ReGLU block, at one parameter:** under the
conditions `OneBlockGenericReGLURMS`, `funDim = P − d(d−1)/2 − 2 d_hidden`. -/
theorem funDim_reglu_oneBlock_residual_rmsNorm (hε : 0 < ε)
    (θ : Params (Arch.gated (T := T) (d := d) relu (rmsNorm ε) hid) dIn dOut)
    (hθ : OneBlockGenericReGLURMS θ) :
    funDim (Arch.gated relu (rmsNorm ε) hid) 1 θ
        + (Fintype.card d * (Fintype.card d - 1) / 2 + 2 * Fintype.card (hid 0))
      = Module.finrank ℝ
          (Params (Arch.gated (T := T) (d := d) relu (rmsNorm ε) hid) dIn dOut) := by
  sorry

/-- **Theorem B.1 (ii) in the paper's own sense, for a ReGLU block, at one parameter:** a
finite batch of inputs with no gate at its kink on which the Jacobian has the rank
`P − d(d−1)/2 − 2 d_hidden`. -/
theorem exists_jacobianRank_reglu_oneBlock_residual_rmsNorm (hε : 0 < ε)
    (θ : Params (Arch.gated (T := T) (d := d) relu (rmsNorm ε) hid) dIn dOut)
    (hθ : OneBlockGenericReGLURMS θ) :
    ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i, X i ∈ noKinkGateRMS θ) ∧
      jacobianRank (Arch.gated relu (rmsNorm ε) hid) 1 X θ
          + (Fintype.card d * (Fintype.card d - 1) / 2 + 2 * Fintype.card (hid 0))
        = Module.finrank ℝ
            (Params (Arch.gated (T := T) (d := d) relu (rmsNorm ε) hid) dIn dOut) := by
  sorry

/-- **Theorem B.1 (ii), first sentence, for one ReGLU block:** for `ε > 0` and
`d_in, d_out ≥ d ≥ 2`, at almost every parameter the residual network of one ReGLU block of any
width has `funDim = P − d(d−1)/2 − 2 d_hidden`. -/
theorem ae_funDim_reglu_oneBlock_residual_rmsNorm (hε : 0 < ε)
    (μ : Measure (Params (Arch.gated (T := T) (d := d) relu (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, funDim (Arch.gated relu (rmsNorm ε) hid) 1 θ
        + (Fintype.card d * (Fintype.card d - 1) / 2 + 2 * Fintype.card (hid 0))
      = Module.finrank ℝ
          (Params (Arch.gated (T := T) (d := d) relu (rmsNorm ε) hid) dIn dOut) := by
  sorry

/-- **Theorem B.1 (ii) in the paper's own sense, for one ReGLU block:** at almost every
parameter there is a finite batch of inputs with no gate at its kink on which the Jacobian has
the rank `P − d(d−1)/2 − 2 d_hidden`. -/
theorem ae_exists_jacobianRank_reglu_oneBlock_residual_rmsNorm (hε : 0 < ε)
    (μ : Measure (Params (Arch.gated (T := T) (d := d) relu (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i, X i ∈ noKinkGateRMS θ) ∧
      jacobianRank (Arch.gated relu (rmsNorm ε) hid) 1 X θ
          + (Fintype.card d * (Fintype.card d - 1) / 2 + 2 * Fintype.card (hid 0))
        = Module.finrank ℝ
            (Params (Arch.gated (T := T) (d := d) relu (rmsNorm ε) hid) dIn dOut) := by
  sorry

/-- **Theorem B.1 (ii), second sentence, for one ReGLU block:** if the block has at least `d`
hidden units, at almost every parameter the skip raises `funDim` by at least `d(d−1)/2`. -/
theorem ae_funDim_skipless_add_le_reglu_oneBlock_residual_rmsNorm (hε : 0 < ε)
    (μ : Measure (Params (Arch.gated (T := T) (d := d) relu (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, funDim (Arch.gated relu (rmsNorm ε) hid) 0 θ
        + Fintype.card d * (Fintype.card d - 1) / 2
      ≤ funDim (Arch.gated relu (rmsNorm ε) hid) 1 θ := by
  sorry

end Skips
