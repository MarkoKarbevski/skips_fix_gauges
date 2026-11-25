import SkipsLean.Residual.DepthRescale

/-!
# Lemma A.30 with inputs in an open set that contains `0`

Paper (skips paper), Lemma A.30 (ReLU-type blocks with small writes): "Let the blocks be ReLU,
ReLU² or ReGLU blocks, without normalization or biases, let `E` and `D` have rank `d_model`, and
let inputs range over all of `ℝ^{1×d_in}`, or over an open set that contains `0`. […] For all small
`τ ≠ 0`, the Jacobian of the residual network at `θ_τ` has rank `P − d_model² − s` on some finite
batch on which no pre-activation vanishes. So the residual network has functional dimension
`P − d_model² − s` on an open set of weights that contains these, and at almost every point of
this set the skips add at least `L d_model²` when every block has width at least `d_model`."

Its proof: "On each region of inputs on which these pre-activations keep their signs, `J_0 η` is a
polynomial in `x`, and the regions are cones with apex `0`. So a direction that is flat on a
neighborhood of `0` is flat at every input at which no pre-activation vanishes […]. Fix a finite
batch of such inputs, inside the set of inputs, on which the kernel of `J_0` is this space".

`Residual/DepthRescale.lean` has the lemma for inputs in all of `ℝ^{T×d_in}`, for MLP blocks with
a positively homogeneous activation (ReLU, ReLU²). Here the second case, for an open set `Ω` of
inputs with `0 ∈ Ω`:

* `smallWritesLimit_eq_zero_of_forall_mem_isOpen_mlp_rescale`: a direction that is flat for `J_0`
  at the inputs of `Ω` at which no limit pre-activation vanishes is flat at every such input. For
  `c > 0`, `(J_0 η)(c x) = c · x (η_E D + E η_D) + c^k · (the terms of the units)`, the inputs at
  which no pre-activation vanishes form a cone, and `c x ∈ Ω` for all small `c > 0`.
* `exists_eventually_jacobianRank_smallWrites_mlp_rescale_of_isOpen`: the first sentence of the
  lemma with the batch inside `Ω`.
* `exists_eventually_eventually_jacobianRank_smallWrites_mlp_rescale_of_isOpen`: near `θ_τ` the
  rank on this batch stays `P − d² − s` and no pre-activation on it vanishes. With
  `eventually_eventually_funDim_smallWrites_mlp_rescale` (the rank on every batch is at most this
  number near `θ_τ`), the functional dimension with inputs in `Ω` is `P − d² − s` near `θ_τ`.
* The statements for ReLU and ReLU² blocks at generic parameters, and the open set of weights.

ReGLU blocks: `Residual/DepthReGLUOpen.lean`.
-/

namespace Skips

open Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d]
  [Fintype dIn] [Fintype dOut]
variable {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]
variable {σ σ' : ℝ → ℝ}

/-- **Proof of Lemma A.30, "a direction that is flat on a neighborhood of `0` is flat at every
input at which no pre-activation vanishes", for MLP blocks with an activation that is positively
homogeneous of degree `k`:** let `Ω` be an open set of inputs that contains `0`. If
`(J_0 η)(x) = 0` at every input of `Ω` at which no limit pre-activation vanishes, then
`(J_0 η)(x) = 0` at every input at which no limit pre-activation vanishes. -/
theorem smallWritesLimit_eq_zero_of_forall_mem_isOpen_mlp_rescale {k : ℕ}
    (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (hhom : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (θ η : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)
    {Ω : Set (Matrix T dIn ℝ)} (hΩ : IsOpen Ω) (h0 : (0 : Matrix T dIn ℝ) ∈ Ω)
    (hη : ∀ x ∈ Ω, x ∈ noKinkAll θ → smallWritesLimit (Arch.mlp σ id hid) θ η x = 0) :
    ∀ x ∈ noKinkAll θ, smallWritesLimit (Arch.mlp σ id hid) θ η x = 0 := by
  sorry

/-- **Lemma A.30, first sentence, with inputs in an open set that contains `0`, at one
parameter:** under the conditions `SmallWritesGeneric`, for an open set `Ω` of inputs with
`0 ∈ Ω` there is a finite batch of inputs of `Ω` at which no limit pre-activation vanishes such
that, for all small `τ ≠ 0`, no pre-activation on the batch vanishes at `θ_τ` and the Jacobian of
the residual network on the batch at `θ_τ` has rank `P − d² − s`. -/
theorem exists_eventually_jacobianRank_smallWrites_mlp_rescale_of_isOpen {k : ℕ}
    (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (hhom : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (hU : UnitsRescale σ σ' k dIn dOut (Σ ℓ, hid ℓ))
    (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) (hθ : SmallWritesGeneric θ)
    {Ω : Set (Matrix T dIn ℝ)} (hΩ : IsOpen Ω) (h0 : (0 : Matrix T dIn ℝ) ∈ Ω) :
    ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i, X i ∈ Ω) ∧ (∀ i, X i ∈ noKinkAll θ) ∧
      ∀ᶠ τ in 𝓝[≠] (0 : ℝ),
        (∀ (i : Fin n) (ℓ : Fin L) (t : T) (j : hid ℓ),
          (hidden (Arch.mlp σ id hid) 1 (θ.smallWrites τ) (X i) ℓ.castSucc * θ.read ℓ) t j ≠ 0) ∧
        jacobianRank (Arch.mlp σ id hid) 1 X (θ.smallWrites τ)
            + (Fintype.card d ^ 2 + ∑ ℓ, Fintype.card (hid ℓ))
          = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) := by
  sorry

/-- **Lemma A.30, second sentence, with inputs in an open set that contains `0`, near `θ_τ`:**
under the conditions `SmallWritesGeneric`, for an open set `Ω` of inputs with `0 ∈ Ω` there is a
finite batch of inputs of `Ω` such that, for all small `τ ≠ 0` and every parameter `θ'` near
`θ_τ`, no pre-activation on the batch vanishes at `θ'` and the Jacobian of the residual network on
the batch at `θ'` has rank `P − d² − s`. (Near `θ_τ` the rank on every batch is at most this
number: `eventually_eventually_funDim_smallWrites_mlp_rescale`.) -/
theorem exists_eventually_eventually_jacobianRank_smallWrites_mlp_rescale_of_isOpen {k : ℕ}
    (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (hhom : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (hU : UnitsRescale σ σ' k dIn dOut (Σ ℓ, hid ℓ))
    (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) (hθ : SmallWritesGeneric θ)
    {Ω : Set (Matrix T dIn ℝ)} (hΩ : IsOpen Ω) (h0 : (0 : Matrix T dIn ℝ) ∈ Ω) :
    ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i, X i ∈ Ω) ∧
      ∀ᶠ τ in 𝓝[≠] (0 : ℝ), ∀ᶠ θ' in 𝓝 (θ.smallWrites τ),
        (∀ (i : Fin n) (ℓ : Fin L) (t : T) (j : hid ℓ),
          (hidden (Arch.mlp σ id hid) 1 θ' (X i) ℓ.castSucc * θ'.read ℓ) t j ≠ 0) ∧
        jacobianRank (Arch.mlp σ id hid) 1 X θ'
            + (Fintype.card d ^ 2 + ∑ ℓ, Fintype.card (hid ℓ))
          = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) := by
  sorry

/-- **Lemma A.30 for ReLU blocks with inputs in an open set that contains `0`:** with
`d_in, d_out ≥ d ≥ 2` and blocks of any widths, for an open set `Ω` of inputs with `0 ∈ Ω`, there
is an open set `U` of weights such that: at every `θ ∈ U` the residual network has
`fd = P − d² − s`, attained by the rank of the Jacobian on a finite batch of inputs of `Ω` on
which no pre-activation vanishes; `U` contains `θ_τ` for generic `θ` and all small `τ ≠ 0`; and at
almost every point of `U` the skips add at least `L d²` when every block has at least `d` hidden
units. -/
theorem exists_isOpen_jacobianRank_smallWrites_relu_of_isOpen
    (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    {Ω : Set (Matrix T dIn ℝ)} (hΩ : IsOpen Ω) (h0 : (0 : Matrix T dIn ℝ) ∈ Ω) :
    ∃ U : Set (Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut), IsOpen U ∧
      (∀ θ ∈ U, funDim (Arch.mlp relu id hid) 1 θ
            + (Fintype.card d ^ 2 + ∑ ℓ, Fintype.card (hid ℓ))
          = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut) ∧
        ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i, X i ∈ Ω) ∧
          (∀ (i : Fin n) (ℓ : Fin L) (t : T) (j : hid ℓ),
            (hidden (Arch.mlp relu id hid) 1 θ (X i) ℓ.castSucc * θ.read ℓ) t j ≠ 0) ∧
          jacobianRank (Arch.mlp relu id hid) 1 X θ
              + (Fintype.card d ^ 2 + ∑ ℓ, Fintype.card (hid ℓ))
            = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut)) ∧
      (∀ (μ : Measure (Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut))
        [μ.IsAddHaarMeasure], ∀ᵐ θ ∂μ, ∀ᶠ τ in 𝓝[≠] (0 : ℝ), θ.smallWrites τ ∈ U) ∧
      (∀ (μ : Measure (Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut))
        [μ.IsAddHaarMeasure], (∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) →
        ∀ᵐ θ ∂μ, θ ∈ U → funDim (Arch.mlp relu id hid) 0 θ + L * Fintype.card d ^ 2
          ≤ funDim (Arch.mlp relu id hid) 1 θ) := by
  sorry

/-- **Lemma A.30 for ReLU² blocks with inputs in an open set that contains `0`:** as
`exists_isOpen_jacobianRank_smallWrites_relu_of_isOpen`. -/
theorem exists_isOpen_jacobianRank_smallWrites_reluSq_of_isOpen
    (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    {Ω : Set (Matrix T dIn ℝ)} (hΩ : IsOpen Ω) (h0 : (0 : Matrix T dIn ℝ) ∈ Ω) :
    ∃ U : Set (Params (Arch.mlp (T := T) (d := d) reluSq id hid) dIn dOut), IsOpen U ∧
      (∀ θ ∈ U, funDim (Arch.mlp reluSq id hid) 1 θ
            + (Fintype.card d ^ 2 + ∑ ℓ, Fintype.card (hid ℓ))
          = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) reluSq id hid) dIn dOut) ∧
        ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i, X i ∈ Ω) ∧
          (∀ (i : Fin n) (ℓ : Fin L) (t : T) (j : hid ℓ),
            (hidden (Arch.mlp reluSq id hid) 1 θ (X i) ℓ.castSucc * θ.read ℓ) t j ≠ 0) ∧
          jacobianRank (Arch.mlp reluSq id hid) 1 X θ
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
