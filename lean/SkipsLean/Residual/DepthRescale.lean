import SkipsLean.Residual.DepthMlp
import SkipsLean.Residual.SmallWritesOn
import SkipsLean.Residual.UpperBoundSymmetries
import SkipsLean.OneBlock.Rescale

/-!
# Residual networks of ReLU and ReLU² blocks with small writes

Paper (skips paper): Lemma A.30 (ReLU-type blocks with small writes), for ReLU and ReLU² blocks:
"Let the blocks be ReLU, ReLU² or ReGLU blocks, without normalization or biases, let `E` and `D`
have rank `d_model`, and let inputs range over all of `ℝ^{1×d_in}`, or over an open set that
contains `0`. For generic parameters `θ`, let `θ_τ` be the parameters `θ` with every `W_write^ℓ`
replaced by `τ W_write^ℓ`, as in Lemma A.27. For all small `τ ≠ 0`, the Jacobian of the residual
network at `θ_τ` has rank `P − d_model² − s` on some finite batch on which no pre-activation
vanishes. So the residual network has functional dimension `P − d_model² − s` on an open set of
weights that contains these, and at almost every point of this set the skips add at least
`L d_model²` when every block has width at least `d_model`."

Its proof: "The limit `J_0` is again the derivative of the one-block function `G` of Lemma B.3,
whose units are those of all blocks, with the pre-activations `x E W_read^ℓ`. […] a direction
that is flat on a neighborhood of `0` is flat at every input at which no pre-activation vanishes,
and by Lemma B.3, which covers these units, the flat directions form a space of dimension
`d_model² + s`, as in Lemma A.27. Fix a finite batch of such inputs, inside the set of inputs, on
which the kernel of `J_0` is this space".

Stated here for an activation `σ` that is differentiable away from `0`, positively homogeneous
of degree `k`, and satisfies Lemma B.3 in the form `UnitsRescale` for the hidden units of all
blocks together (ReLU with `k = 1`, ReLU² with `k = 2`), under the conditions `SmallWritesGeneric`
of `Residual/DepthMlp.lean` (the conditions of Lemma A.27; they hold at generic parameters), with
all inputs (`T × d_in` matrices), `s = ∑_ℓ d_hidden^ℓ`:

* `noKinkAll θ`: the inputs at which no limit pre-activation `x E W_read^ℓ` vanishes.
* The kernel of `J_0` at these inputs: `η_E = E X`, `η_D = −X D`, and the reads and the writes
  of `η` are those of a rescaling of the hidden units, a space of dimension `d² + s`.
* The first sentence: a finite batch in `noKinkAll θ` such that for all small `τ ≠ 0` no
  pre-activation on the batch vanishes at `θ_τ` and the Jacobian on the batch at `θ_τ` has rank
  `P − d² − s`; hence `funDim (θ_τ) = P − d² − s`.
* The second sentence: `funDim = P − d² − s` at every parameter near `θ_τ`; an open set `U` on
  which `funDim = P − d² − s` and which contains `θ_τ` for generic `θ` and all small `τ ≠ 0`; and
  the gain `≥ L d²` at almost every point of `U` when every block has at least `d` hidden units.

ReGLU blocks are not stated here.
-/

namespace Skips

open Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d]
  [Fintype dIn] [Fintype dOut]
variable {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]
variable {σ σ' : ℝ → ℝ}

/-- The inputs at which no limit pre-activation vanishes: every entry of `x E W_read^ℓ`, for
every block `ℓ`, token and hidden unit, is nonzero. -/
def noKinkAll (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) :
    Set (Matrix T dIn ℝ) :=
  {x | ∀ (ℓ : Fin L) (t : T) (i : hid ℓ), (x * θ.E * θ.read ℓ) t i ≠ 0}

/-- **Proof of Lemma A.30, the kernel of `J_0`:** under the conditions `SmallWritesGeneric`, a
direction `η` with `(J_0 η)(x) = 0` at every input at which no limit pre-activation vanishes has
`η_E = E X` and `η_D = −X D` for one matrix `X`, and its reads and writes are those of a
rescaling of the hidden units (Lemma B.3 for the units of all blocks together). -/
theorem smallWritesLimit_eq_zero_mlp_rescale {k : ℕ} (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (hU : UnitsRescale σ σ' k dIn dOut (Σ ℓ, hid ℓ))
    (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) (hθ : SmallWritesGeneric θ)
    (η : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)
    (hη : ∀ x ∈ noKinkAll θ, smallWritesLimit (Arch.mlp σ id hid) θ η x = 0) :
    ∃ (X : Matrix d d ℝ) (α : ∀ ℓ, hid ℓ → ℝ), η.E = θ.E * X ∧ η.D = -(X * θ.D)
      ∧ (∀ ℓ, η.read ℓ = (rescaleDirMlp k θ α).read ℓ)
      ∧ (∀ ℓ, η.write ℓ = (rescaleDirMlp k θ α).write ℓ) := by
  sorry

/-- **Lemma A.30, first sentence, at one parameter:** under the conditions `SmallWritesGeneric`
there is a finite batch of inputs at which no limit pre-activation vanishes such that, for all
small `τ ≠ 0`, no pre-activation on the batch vanishes at `θ_τ` and the Jacobian of the residual
network on the batch at `θ_τ` has rank `P − d² − s`. -/
theorem exists_eventually_jacobianRank_smallWrites_mlp_rescale {k : ℕ}
    (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (hhom : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (hU : UnitsRescale σ σ' k dIn dOut (Σ ℓ, hid ℓ))
    (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) (hθ : SmallWritesGeneric θ) :
    ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i, X i ∈ noKinkAll θ) ∧
      ∀ᶠ τ in 𝓝[≠] (0 : ℝ),
        (∀ (i : Fin n) (ℓ : Fin L) (t : T) (j : hid ℓ),
          (hidden (Arch.mlp σ id hid) 1 (θ.smallWrites τ) (X i) ℓ.castSucc * θ.read ℓ) t j ≠ 0) ∧
        jacobianRank (Arch.mlp σ id hid) 1 X (θ.smallWrites τ)
            + (Fintype.card d ^ 2 + ∑ ℓ, Fintype.card (hid ℓ))
          = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) := by
  sorry

/-- **Lemma A.30, the functional dimension at `θ_τ`:** under the conditions
`SmallWritesGeneric`, for all small `τ ≠ 0` the residual network has `fd(θ_τ) = P − d² − s`. -/
theorem eventually_funDim_smallWrites_mlp_rescale {k : ℕ}
    (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (hhom : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (hU : UnitsRescale σ σ' k dIn dOut (Σ ℓ, hid ℓ))
    (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) (hθ : SmallWritesGeneric θ) :
    ∀ᶠ τ in 𝓝[≠] (0 : ℝ),
      funDim (Arch.mlp σ id hid) 1 (θ.smallWrites τ)
          + (Fintype.card d ^ 2 + ∑ ℓ, Fintype.card (hid ℓ))
        = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) := by
  sorry

/-- **Lemma A.30, second sentence, near `θ_τ`:** under the conditions `SmallWritesGeneric`, for
all small `τ ≠ 0` the residual network has `fd = P − d² − s` at every parameter near `θ_τ`. -/
theorem eventually_eventually_funDim_smallWrites_mlp_rescale {k : ℕ}
    (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (hhom : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (hU : UnitsRescale σ σ' k dIn dOut (Σ ℓ, hid ℓ))
    (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) (hθ : SmallWritesGeneric θ) :
    ∀ᶠ τ in 𝓝[≠] (0 : ℝ), ∀ᶠ θ' in 𝓝 (θ.smallWrites τ),
      funDim (Arch.mlp σ id hid) 1 θ' + (Fintype.card d ^ 2 + ∑ ℓ, Fintype.card (hid ℓ))
        = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) := by
  sorry

/-- **Lemma A.30 for ReLU blocks, first sentence:** with `d_in, d_out ≥ d ≥ 2` and blocks of any
widths, for generic parameters `θ` there is a finite batch of inputs at which no limit
pre-activation vanishes such that, for all small `τ ≠ 0`, no pre-activation on the batch vanishes
at `θ_τ` and the Jacobian of the residual network on the batch at `θ_τ` has rank
`P − d² − s`. -/
theorem ae_exists_eventually_jacobianRank_smallWrites_relu
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut)) [μ.IsAddHaarMeasure]
    (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i, X i ∈ noKinkAll θ) ∧
      ∀ᶠ τ in 𝓝[≠] (0 : ℝ),
        (∀ (i : Fin n) (ℓ : Fin L) (t : T) (j : hid ℓ),
          (hidden (Arch.mlp relu id hid) 1 (θ.smallWrites τ) (X i) ℓ.castSucc * θ.read ℓ) t j
            ≠ 0) ∧
        jacobianRank (Arch.mlp relu id hid) 1 X (θ.smallWrites τ)
            + (Fintype.card d ^ 2 + ∑ ℓ, Fintype.card (hid ℓ))
          = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut) := by
  sorry

/-- **Lemma A.30 for ReLU blocks, second sentence:** with `d_in, d_out ≥ d ≥ 2` and blocks of
any widths, there is an open set `U` of weights on which the residual network has
`fd = P − d² − s`, which contains `θ_τ` for generic `θ` and all small `τ ≠ 0`, and at almost
every point of which the skips add at least `L d²` when every block has at least `d` hidden
units. -/
theorem exists_isOpen_funDim_smallWrites_relu
    (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∃ U : Set (Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut), IsOpen U ∧
      (∀ θ ∈ U, funDim (Arch.mlp relu id hid) 1 θ
          + (Fintype.card d ^ 2 + ∑ ℓ, Fintype.card (hid ℓ))
        = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut)) ∧
      (∀ (μ : Measure (Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut))
        [μ.IsAddHaarMeasure], ∀ᵐ θ ∂μ, ∀ᶠ τ in 𝓝[≠] (0 : ℝ), θ.smallWrites τ ∈ U) ∧
      (∀ (μ : Measure (Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut))
        [μ.IsAddHaarMeasure], (∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) →
        ∀ᵐ θ ∂μ, θ ∈ U → funDim (Arch.mlp relu id hid) 0 θ + L * Fintype.card d ^ 2
          ≤ funDim (Arch.mlp relu id hid) 1 θ) := by
  sorry

/-- **Lemma A.30 for ReLU² blocks, first sentence.** -/
theorem ae_exists_eventually_jacobianRank_smallWrites_reluSq
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) reluSq id hid) dIn dOut))
    [μ.IsAddHaarMeasure]
    (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i, X i ∈ noKinkAll θ) ∧
      ∀ᶠ τ in 𝓝[≠] (0 : ℝ),
        (∀ (i : Fin n) (ℓ : Fin L) (t : T) (j : hid ℓ),
          (hidden (Arch.mlp reluSq id hid) 1 (θ.smallWrites τ) (X i) ℓ.castSucc * θ.read ℓ) t j
            ≠ 0) ∧
        jacobianRank (Arch.mlp reluSq id hid) 1 X (θ.smallWrites τ)
            + (Fintype.card d ^ 2 + ∑ ℓ, Fintype.card (hid ℓ))
          = Module.finrank ℝ
              (Params (Arch.mlp (T := T) (d := d) reluSq id hid) dIn dOut) := by
  sorry

/-- **Lemma A.30 for ReLU² blocks, second sentence.** -/
theorem exists_isOpen_funDim_smallWrites_reluSq
    (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∃ U : Set (Params (Arch.mlp (T := T) (d := d) reluSq id hid) dIn dOut), IsOpen U ∧
      (∀ θ ∈ U, funDim (Arch.mlp reluSq id hid) 1 θ
          + (Fintype.card d ^ 2 + ∑ ℓ, Fintype.card (hid ℓ))
        = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) reluSq id hid) dIn dOut)) ∧
      (∀ (μ : Measure (Params (Arch.mlp (T := T) (d := d) reluSq id hid) dIn dOut))
        [μ.IsAddHaarMeasure], ∀ᵐ θ ∂μ, ∀ᶠ τ in 𝓝[≠] (0 : ℝ), θ.smallWrites τ ∈ U) ∧
      (∀ (μ : Measure (Params (Arch.mlp (T := T) (d := d) reluSq id hid) dIn dOut))
        [μ.IsAddHaarMeasure], (∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) →
        ∀ᵐ θ ∂μ, θ ∈ U → funDim (Arch.mlp reluSq id hid) 0 θ + L * Fintype.card d ^ 2
          ≤ funDim (Arch.mlp reluSq id hid) 1 θ) := by
  sorry

end Skips
