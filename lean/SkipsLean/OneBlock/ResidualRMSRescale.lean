import SkipsLean.OneBlock.ResidualRMSStepsOn
import SkipsLean.OneBlock.ResidualRMSMlp
import SkipsLean.OneBlock.ResidualRescale

/-!
# One residual ReLU or ReLU² block under pre-RMSNorm

Paper (skips paper): Theorem 4.6 (ii), first sentence (Theorem B.1 (ii) in the appendix), for
`ε > 0` and no biases, for ReLU and ReLU² blocks: "For generic parameters the residual network has
functional dimension `P − d_model (d_model − 1)/2 − s`, which is the equality condition. If the
block has width at least `d_model`, the skip raises the functional dimension by at least
`d_model (d_model − 1)/2`." Here `s` is the number of hidden units.

Its proof, Step 4: "For the ReLU-type activations without biases the kinks lie on hyperplanes
through the center of the ball, and the arguments of Lemma B.3 are local. So Lemma B.3, with `E`
and `D` replaced by the identity and `M = 0`, makes the entries of `η'` at each hidden unit a
rescaling." Step 5: "The flat directions are thus those of the orthogonal change of basis and of
the symmetries inside the block. […] so `dim K(θ) = d_model (d_model − 1)/2 + s`."

Stated here, as in `OneBlock/ResidualRescale.lean` (the same block without normalization) and
`OneBlock/ResidualRMSMlp.lean` (tanh and GELU blocks under pre-RMSNorm), for an activation that is
differentiable away from `0`, positively homogeneous of degree `k`, and satisfies Lemma B.3 in the
form `UnitsRescale`:

* `noKinkRMS θ`: the inputs at which no hidden unit sits at its kink (every entry of
  `x E W_read` is nonzero; under pre-RMSNorm with `ε > 0` the block reads a positive multiple of
  each row of `x E`).
* A direction that is flat at these inputs is `cobDir θ (fun _ => Y) + rescaleDirMlp k θ α` with
  `Y` antisymmetric.
* The value: `funDim + d(d−1)/2 + s = P`, and a batch of inputs of `noKinkRMS θ` with this rank
  (the paper's functional dimension for these blocks), under the conditions `OneBlockGenericRMS`
  and at almost every parameter, for ReLU and ReLU² blocks of any width.
* The gain: for a block of at least `d` hidden units the skip raises `funDim` by at least
  `d(d−1)/2`.

Steps 1 to 3 at the inputs of `noKinkRMS θ` are `exists_antisymm_of_flatOn_residual_rmsNorm`
(`OneBlock/ResidualRMSStepsOn.lean`). ReGLU blocks are not stated here.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {hid : Fin 1 → Type} [∀ ℓ, Fintype (hid ℓ)]
variable {σ σ' : ℝ → ℝ} {ε : ℝ}

/-- The inputs at which no hidden unit of the block sits at its kink, under pre-RMSNorm: every
entry of `x E W_read` (one per token and hidden unit) is nonzero. -/
def noKinkRMS (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut) :
    Set (Matrix T dIn ℝ) :=
  {x | ∀ (t : T) (i : hid 0), (x * θ.E * θ.read 0) t i ≠ 0}

/-- **Proof of Theorem B.1 (ii), Steps 1 to 4, for ReLU-type MLP blocks:** under the conditions
`OneBlockGenericRMS`, a direction that is flat at every input with no hidden unit at its kink is
the direction of an orthogonal change of basis shared by `h_0` and `h_1` plus a rescaling of the
hidden units. -/
theorem flatOn_noKinkRMS_le_mlp_rescale_residual_rmsNorm {k : ℕ} (hε : 0 < ε)
    (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (hhom : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (hU : UnitsRescale σ σ' k d d (hid 0))
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)
    (hθ : OneBlockGenericRMS θ)
    (η : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)
    (hη : η ∈ flatOn (Arch.mlp σ (rmsNorm ε) hid) 1 θ (noKinkRMS θ)) :
    ∃ (Y : Matrix d d ℝ) (α : ∀ ℓ, hid ℓ → ℝ), Yᵀ = -Y ∧
      η = cobDir θ (fun _ => Y) + rescaleDirMlp k θ α := by
  sorry

/-- **Theorem B.1 (ii), first sentence, for ReLU-type MLP blocks, at one parameter:** under the
conditions `OneBlockGenericRMS`, `funDim = P − d(d−1)/2 − s`, with `s` the number of hidden
units. -/
theorem funDim_mlp_oneBlock_rescale_residual_rmsNorm {k : ℕ} (hε : 0 < ε)
    (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (hhom : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (hU : UnitsRescale σ σ' k d d (hid 0))
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)
    (hθ : OneBlockGenericRMS θ) :
    funDim (Arch.mlp σ (rmsNorm ε) hid) 1 θ
        + (Fintype.card d * (Fintype.card d - 1) / 2 + Fintype.card (hid 0))
      = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut) := by
  sorry

/-- **Theorem B.1 (ii) in the paper's own sense, for ReLU-type MLP blocks, at one parameter:** a
finite batch of inputs with no hidden unit at its kink on which the Jacobian has the rank
`P − d(d−1)/2 − s`. -/
theorem exists_jacobianRank_mlp_oneBlock_rescale_residual_rmsNorm {k : ℕ} (hε : 0 < ε)
    (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (hhom : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (hU : UnitsRescale σ σ' k d d (hid 0))
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)
    (hθ : OneBlockGenericRMS θ) :
    ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i, X i ∈ noKinkRMS θ) ∧
      jacobianRank (Arch.mlp σ (rmsNorm ε) hid) 1 X θ
          + (Fintype.card d * (Fintype.card d - 1) / 2 + Fintype.card (hid 0))
        = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut) := by
  sorry

/-- **Theorem B.1 (ii), first sentence, for one ReLU block:** for `ε > 0` and
`d_in, d_out ≥ d ≥ 2`, at almost every parameter the residual network of one ReLU block of any
width has `funDim = P − d(d−1)/2 − s`. -/
theorem ae_funDim_relu_oneBlock_residual_rmsNorm (hε : 0 < ε)
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, funDim (Arch.mlp relu (rmsNorm ε) hid) 1 θ
        + (Fintype.card d * (Fintype.card d - 1) / 2 + Fintype.card (hid 0))
      = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm ε) hid) dIn dOut) := by
  sorry

/-- **Theorem B.1 (ii) in the paper's own sense, for one ReLU block:** at almost every
parameter there is a finite batch of inputs with no hidden unit at its kink on which the Jacobian
has the rank `P − d(d−1)/2 − s`. -/
theorem ae_exists_jacobianRank_relu_oneBlock_residual_rmsNorm (hε : 0 < ε)
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i, X i ∈ noKinkRMS θ) ∧
      jacobianRank (Arch.mlp relu (rmsNorm ε) hid) 1 X θ
          + (Fintype.card d * (Fintype.card d - 1) / 2 + Fintype.card (hid 0))
        = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm ε) hid) dIn dOut) := by
  sorry

/-- **Theorem B.1 (ii), second sentence, for one ReLU block:** if the block has at least
`d` hidden units, at almost every parameter the skip raises `funDim` by at least `d(d−1)/2`. -/
theorem ae_funDim_skipless_add_le_relu_oneBlock_residual_rmsNorm (hε : 0 < ε)
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, funDim (Arch.mlp relu (rmsNorm ε) hid) 0 θ
        + Fintype.card d * (Fintype.card d - 1) / 2
      ≤ funDim (Arch.mlp relu (rmsNorm ε) hid) 1 θ := by
  sorry

/-- **Theorem B.1 (ii), first sentence, for one ReLU² block:** for `ε > 0` and
`d_in, d_out ≥ d ≥ 2`, at almost every parameter the residual network of one ReLU² block of
any width has `funDim = P − d(d−1)/2 − s`. -/
theorem ae_funDim_reluSq_oneBlock_residual_rmsNorm (hε : 0 < ε)
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) reluSq (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, funDim (Arch.mlp reluSq (rmsNorm ε) hid) 1 θ
        + (Fintype.card d * (Fintype.card d - 1) / 2 + Fintype.card (hid 0))
      = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) reluSq (rmsNorm ε) hid) dIn dOut) := by
  sorry

/-- **Theorem B.1 (ii) in the paper's own sense, for one ReLU² block:** at almost every
parameter there is a finite batch of inputs with no hidden unit at its kink on which the Jacobian
has the rank `P − d(d−1)/2 − s`. -/
theorem ae_exists_jacobianRank_reluSq_oneBlock_residual_rmsNorm (hε : 0 < ε)
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) reluSq (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i, X i ∈ noKinkRMS θ) ∧
      jacobianRank (Arch.mlp reluSq (rmsNorm ε) hid) 1 X θ
          + (Fintype.card d * (Fintype.card d - 1) / 2 + Fintype.card (hid 0))
        = Module.finrank ℝ
            (Params (Arch.mlp (T := T) (d := d) reluSq (rmsNorm ε) hid) dIn dOut) := by
  sorry

/-- **Theorem B.1 (ii), second sentence, for one ReLU² block:** if the block has at least
`d` hidden units, at almost every parameter the skip raises `funDim` by at least `d(d−1)/2`. -/
theorem ae_funDim_skipless_add_le_reluSq_oneBlock_residual_rmsNorm (hε : 0 < ε)
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) reluSq (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, funDim (Arch.mlp reluSq (rmsNorm ε) hid) 0 θ
        + Fintype.card d * (Fintype.card d - 1) / 2
      ≤ funDim (Arch.mlp reluSq (rmsNorm ε) hid) 1 θ := by
  sorry

end Skips
