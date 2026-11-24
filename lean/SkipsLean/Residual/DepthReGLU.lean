import SkipsLean.Residual.DepthGated
import SkipsLean.Residual.SmallWritesOn
import SkipsLean.Residual.UpperBoundSymmetries
import SkipsLean.OneBlock.UnitsReGLU
import SkipsLean.Dimension.RescalingGate

/-!
# Residual networks of ReGLU blocks with small writes

Paper (skips paper): Lemma A.30 (ReLU-type blocks with small writes), for ReGLU blocks: "Let the
blocks be ReLU, ReLU² or ReGLU blocks, without normalization or biases, let `E` and `D` have rank
`d_model`, and let inputs range over all of `ℝ^{1×d_in}`, or over an open set that contains `0`.
For generic parameters `θ`, let `θ_τ` be the parameters `θ` with every `W_write^ℓ` replaced by
`τ W_write^ℓ`, as in Lemma A.27. For all small `τ ≠ 0`, the Jacobian of the residual network at
`θ_τ` has rank `P − d_model² − s` on some finite batch on which no pre-activation vanishes. So
the residual network has functional dimension `P − d_model² − s` on an open set of weights that
contains these, and at almost every point of this set the skips add at least `L d_model²` when
every block has width at least `d_model`." For ReGLU `s = 2 ∑_ℓ d_hidden^ℓ`: one rescaling of the
gate and one of the value for each hidden unit.

Stated here as in `Residual/DepthRescale.lean` (ReLU and ReLU² blocks), with Lemma B.3 for ReGLU
(`relu_gated_units_flat`, `OneBlock/UnitsReGLU.lean`) for the hidden units of all blocks together,
all inputs (`T × d_in` matrices):

* `SmallWritesGenericReGLU θ`: the conditions `SmallWritesGenericGated` of
  `Residual/DepthGated.lean` (those of Lemma A.27 for gated blocks) and the hypothesis of
  Lemma B.3 that only ReGLU uses: no value column of `E W_read^ℓ` is proportional to the gate
  column of the same hidden unit. They hold at generic parameters.
* `noKinkGateAll θ`: the inputs at which no limit pre-activation of a gate, an entry of a gate
  column of `x E W_read^ℓ`, vanishes.
* The kernel of `J_0` at these inputs: `η_E = E X`, `η_D = −X D`, and the reads and the writes
  of `η` are those of a rescaling of the values plus a rescaling of the gates, a space of
  dimension `d² + s`.
* The first sentence: a finite batch in `noKinkGateAll θ` such that for all small `τ ≠ 0` no gate
  pre-activation on the batch vanishes at `θ_τ` and the Jacobian on the batch at `θ_τ` has rank
  `P − d² − s`; hence `funDim (θ_τ) = P − d² − s`.
* The second sentence: `funDim = P − d² − s` at every parameter near `θ_τ`; an open set `U` on
  which `funDim = P − d² − s` and which contains `θ_τ` for generic `θ` and all small `τ ≠ 0`; and
  the gain `≥ L d²` at almost every point of `U` when every block has at least `d` hidden units.
-/

namespace Skips

open Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d]
  [Fintype dIn] [Fintype dOut]
variable {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]
variable {σ : ℝ → ℝ}

/-- **The conditions on `θ` in Lemma A.30, for ReGLU blocks:** those of Lemma A.27 for gated
blocks, and no value column `e_{ℓ,i}` of `E W_read^ℓ` is proportional to the gate column
`c_{ℓ,i}` of the same hidden unit. They do not involve the gate activation. -/
structure SmallWritesGenericReGLU
    (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) : Prop where
  /-- the conditions of Lemma A.27 for gated blocks -/
  gated : SmallWritesGenericGated θ
  /-- no value column of `E W_read^ℓ` is proportional to the gate column of the same unit -/
  value_not_gate : ∀ (ℓ : Fin L) (i : hid ℓ) (r : ℝ),
    (θ.E * θ.read ℓ)ᵀ (Sum.inr i) ≠ r • (θ.E * θ.read ℓ)ᵀ (Sum.inl i)

/-- The inputs at which no limit pre-activation of a gate vanishes: every entry of the gate
columns of `x E W_read^ℓ`, for every block `ℓ`, token and hidden unit, is nonzero. -/
def noKinkGateAll (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) :
    Set (Matrix T dIn ℝ) :=
  {x | ∀ (ℓ : Fin L) (t : T) (i : hid ℓ), (x * θ.E * θ.read ℓ) t (Sum.inl i) ≠ 0}

/-- The conditions of Lemma A.30 for ReGLU blocks hold at generic parameters, for
`d_in, d_out ≥ d ≥ 2` and blocks of any widths. -/
theorem ae_smallWritesGenericReGLU
    (μ : Measure (Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)) [μ.IsAddHaarMeasure]
    (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, SmallWritesGenericReGLU θ := by
  sorry

/-- **Proof of Lemma A.30, the kernel of `J_0`, for ReGLU blocks:** under the conditions
`SmallWritesGenericReGLU`, a direction `η` with `(J_0 η)(x) = 0` at every input at which no limit
pre-activation of a gate vanishes has `η_E = E X` and `η_D = −X D` for one matrix `X`, and its
reads and writes are those of a rescaling of the values plus a rescaling of the gates of the
hidden units (Lemma B.3 for the units of all blocks together). -/
theorem smallWritesLimit_eq_zero_reglu
    (θ : Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut)
    (hθ : SmallWritesGenericReGLU θ)
    (η : Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut)
    (hη : ∀ x ∈ noKinkGateAll θ, smallWritesLimit (Arch.gated relu id hid) θ η x = 0) :
    ∃ (X : Matrix d d ℝ) (α β : ∀ ℓ, hid ℓ → ℝ), η.E = θ.E * X ∧ η.D = -(X * θ.D)
      ∧ (∀ ℓ, η.read ℓ = (rescaleDir θ α + rescaleDirGate 1 θ β).read ℓ)
      ∧ (∀ ℓ, η.write ℓ = (rescaleDir θ α + rescaleDirGate 1 θ β).write ℓ) := by
  sorry

/-- **Lemma A.30 for ReGLU blocks, first sentence, at one parameter:** under the conditions
`SmallWritesGenericReGLU` there is a finite batch of inputs at which no limit pre-activation of a
gate vanishes such that, for all small `τ ≠ 0`, no gate pre-activation on the batch vanishes at
`θ_τ` and the Jacobian of the residual network on the batch at `θ_τ` has rank
`P − d² − 2 ∑_ℓ d_hidden^ℓ`. -/
theorem exists_eventually_jacobianRank_smallWrites_reglu
    (θ : Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut)
    (hθ : SmallWritesGenericReGLU θ) :
    ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i, X i ∈ noKinkGateAll θ) ∧
      ∀ᶠ τ in 𝓝[≠] (0 : ℝ),
        (∀ (i : Fin n) (ℓ : Fin L) (t : T) (j : hid ℓ),
          (hidden (Arch.gated relu id hid) 1 (θ.smallWrites τ) (X i) ℓ.castSucc * θ.read ℓ) t
            (Sum.inl j) ≠ 0) ∧
        jacobianRank (Arch.gated relu id hid) 1 X (θ.smallWrites τ)
            + (Fintype.card d ^ 2 + 2 * ∑ ℓ, Fintype.card (hid ℓ))
          = Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut) := by
  sorry

/-- **Lemma A.30 for ReGLU blocks, the functional dimension at `θ_τ`:** under the conditions
`SmallWritesGenericReGLU`, for all small `τ ≠ 0` the residual network has
`fd(θ_τ) = P − d² − 2 ∑_ℓ d_hidden^ℓ`. -/
theorem eventually_funDim_smallWrites_reglu
    (θ : Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut)
    (hθ : SmallWritesGenericReGLU θ) :
    ∀ᶠ τ in 𝓝[≠] (0 : ℝ),
      funDim (Arch.gated relu id hid) 1 (θ.smallWrites τ)
          + (Fintype.card d ^ 2 + 2 * ∑ ℓ, Fintype.card (hid ℓ))
        = Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut) := by
  sorry

/-- **Lemma A.30 for ReGLU blocks, second sentence, near `θ_τ`:** under the conditions
`SmallWritesGenericReGLU`, for all small `τ ≠ 0` the residual network has
`fd = P − d² − 2 ∑_ℓ d_hidden^ℓ` at every parameter near `θ_τ`. -/
theorem eventually_eventually_funDim_smallWrites_reglu
    (θ : Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut)
    (hθ : SmallWritesGenericReGLU θ) :
    ∀ᶠ τ in 𝓝[≠] (0 : ℝ), ∀ᶠ θ' in 𝓝 (θ.smallWrites τ),
      funDim (Arch.gated relu id hid) 1 θ'
          + (Fintype.card d ^ 2 + 2 * ∑ ℓ, Fintype.card (hid ℓ))
        = Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut) := by
  sorry

/-- **Lemma A.30 for ReGLU blocks, first sentence:** with `d_in, d_out ≥ d ≥ 2` and blocks of
any widths, for generic parameters `θ` there is a finite batch of inputs at which no limit
pre-activation of a gate vanishes such that, for all small `τ ≠ 0`, no gate pre-activation on
the batch vanishes at `θ_τ` and the Jacobian of the residual network on the batch at `θ_τ` has
rank `P − d² − 2 ∑_ℓ d_hidden^ℓ`. -/
theorem ae_exists_eventually_jacobianRank_smallWrites_reglu
    (μ : Measure (Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut))
    [μ.IsAddHaarMeasure]
    (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i, X i ∈ noKinkGateAll θ) ∧
      ∀ᶠ τ in 𝓝[≠] (0 : ℝ),
        (∀ (i : Fin n) (ℓ : Fin L) (t : T) (j : hid ℓ),
          (hidden (Arch.gated relu id hid) 1 (θ.smallWrites τ) (X i) ℓ.castSucc * θ.read ℓ) t
            (Sum.inl j) ≠ 0) ∧
        jacobianRank (Arch.gated relu id hid) 1 X (θ.smallWrites τ)
            + (Fintype.card d ^ 2 + 2 * ∑ ℓ, Fintype.card (hid ℓ))
          = Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut) := by
  sorry

/-- **Lemma A.30 for ReGLU blocks, second sentence:** with `d_in, d_out ≥ d ≥ 2` and blocks of
any widths, there is an open set `U` of weights on which the residual network has
`fd = P − d² − 2 ∑_ℓ d_hidden^ℓ`, which contains `θ_τ` for generic `θ` and all small `τ ≠ 0`,
and at almost every point of which the skips add at least `L d²` when every block has at least
`d` hidden units. -/
theorem exists_isOpen_funDim_smallWrites_reglu
    (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∃ U : Set (Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut), IsOpen U ∧
      (∀ θ ∈ U, funDim (Arch.gated relu id hid) 1 θ
          + (Fintype.card d ^ 2 + 2 * ∑ ℓ, Fintype.card (hid ℓ))
        = Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut)) ∧
      (∀ (μ : Measure (Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut))
        [μ.IsAddHaarMeasure], ∀ᵐ θ ∂μ, ∀ᶠ τ in 𝓝[≠] (0 : ℝ), θ.smallWrites τ ∈ U) ∧
      (∀ (μ : Measure (Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut))
        [μ.IsAddHaarMeasure], (∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) →
        ∀ᵐ θ ∂μ, θ ∈ U → funDim (Arch.gated relu id hid) 0 θ + L * Fintype.card d ^ 2
          ≤ funDim (Arch.gated relu id hid) 1 θ) := by
  sorry

end Skips
