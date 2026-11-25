import SkipsLean.Residual.DepthReGLU

/-!
# Lemma A.30 for ReGLU blocks with inputs in an open set that contains `0`

Paper (skips paper), Lemma A.30: "Let the blocks be ReLU, ReLU² or ReGLU blocks, without
normalization or biases, let `E` and `D` have rank `d_model`, and let inputs range over all of
`ℝ^{1×d_in}`, or over an open set that contains `0`." Its proof: "On each region of inputs on which
these pre-activations keep their signs, `J_0 η` is a polynomial in `x`, and the regions are cones
with apex `0`. So a direction that is flat on a neighborhood of `0` is flat at every input at
which no pre-activation vanishes".

`Residual/DepthReGLU.lean` has the lemma for inputs in all of `ℝ^{T×d_in}`. Here the second case,
for an open set `Ω` of inputs with `0 ∈ Ω`, as in `Residual/DepthRescaleOpen.lean` for ReLU and
ReLU² blocks. A ReGLU unit `relu(g) v` is positively homogeneous of degree `2` in its gate and
value together, so for `c > 0`, `(J_0 η)(c x) = c · x (η_E D + E η_D) + c² · (the terms of the
units)`. The inputs are those at which no gate pre-activation vanishes (`noKinkGateAll`); `s` is
twice the number of hidden units (the rescalings of the values and of the gates).
-/

namespace Skips

open Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d]
  [Fintype dIn] [Fintype dOut]
variable {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]

/-- **Proof of Lemma A.30, "a direction that is flat on a neighborhood of `0` is flat at every
input at which no pre-activation vanishes", for ReGLU blocks:** let `Ω` be an open set of inputs
that contains `0`. If `(J_0 η)(x) = 0` at every input of `Ω` at which no limit pre-activation of
a gate vanishes, then `(J_0 η)(x) = 0` at every input at which no limit pre-activation of a gate
vanishes. -/
theorem smallWritesLimit_eq_zero_of_forall_mem_isOpen_reglu
    (θ η : Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut)
    {Ω : Set (Matrix T dIn ℝ)} (hΩ : IsOpen Ω) (h0 : (0 : Matrix T dIn ℝ) ∈ Ω)
    (hη : ∀ x ∈ Ω, x ∈ noKinkGateAll θ →
      smallWritesLimit (Arch.gated relu id hid) θ η x = 0) :
    ∀ x ∈ noKinkGateAll θ, smallWritesLimit (Arch.gated relu id hid) θ η x = 0 := by
  sorry

/-- **Lemma A.30 for ReGLU blocks, first sentence, with inputs in an open set that contains `0`,
at one parameter:** under the conditions `SmallWritesGenericReGLU`, for an open set `Ω` of inputs
with `0 ∈ Ω` there is a finite batch of inputs of `Ω` at which no limit pre-activation of a gate
vanishes such that, for all small `τ ≠ 0`, no pre-activation of a gate on the batch vanishes at
`θ_τ` and the Jacobian of the residual network on the batch at `θ_τ` has rank `P − d² − s`. -/
theorem exists_eventually_jacobianRank_smallWrites_reglu_of_isOpen
    (θ : Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut)
    (hθ : SmallWritesGenericReGLU θ)
    {Ω : Set (Matrix T dIn ℝ)} (hΩ : IsOpen Ω) (h0 : (0 : Matrix T dIn ℝ) ∈ Ω) :
    ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i, X i ∈ Ω) ∧ (∀ i, X i ∈ noKinkGateAll θ) ∧
      ∀ᶠ τ in 𝓝[≠] (0 : ℝ),
        (∀ (i : Fin n) (ℓ : Fin L) (t : T) (j : hid ℓ),
          (hidden (Arch.gated relu id hid) 1 (θ.smallWrites τ) (X i) ℓ.castSucc * θ.read ℓ) t
            (Sum.inl j) ≠ 0) ∧
        jacobianRank (Arch.gated relu id hid) 1 X (θ.smallWrites τ)
            + (Fintype.card d ^ 2 + 2 * ∑ ℓ, Fintype.card (hid ℓ))
          = Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut) := by
  sorry

/-- **Lemma A.30 for ReGLU blocks, second sentence, with inputs in an open set that contains `0`,
near `θ_τ`:** under the conditions `SmallWritesGenericReGLU`, for an open set `Ω` of inputs with
`0 ∈ Ω` there is a finite batch of inputs of `Ω` such that, for all small `τ ≠ 0` and every
parameter `θ'` near `θ_τ`, no pre-activation of a gate on the batch vanishes at `θ'` and the
Jacobian of the residual network on the batch at `θ'` has rank `P − d² − s`. (Near `θ_τ` the rank
on every batch is at most this number: `eventually_eventually_funDim_smallWrites_reglu`.) -/
theorem exists_eventually_eventually_jacobianRank_smallWrites_reglu_of_isOpen
    (θ : Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut)
    (hθ : SmallWritesGenericReGLU θ)
    {Ω : Set (Matrix T dIn ℝ)} (hΩ : IsOpen Ω) (h0 : (0 : Matrix T dIn ℝ) ∈ Ω) :
    ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i, X i ∈ Ω) ∧
      ∀ᶠ τ in 𝓝[≠] (0 : ℝ), ∀ᶠ θ' in 𝓝 (θ.smallWrites τ),
        (∀ (i : Fin n) (ℓ : Fin L) (t : T) (j : hid ℓ),
          (hidden (Arch.gated relu id hid) 1 θ' (X i) ℓ.castSucc * θ'.read ℓ) t (Sum.inl j)
            ≠ 0) ∧
        jacobianRank (Arch.gated relu id hid) 1 X θ'
            + (Fintype.card d ^ 2 + 2 * ∑ ℓ, Fintype.card (hid ℓ))
          = Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut) := by
  sorry

/-- **Lemma A.30 for ReGLU blocks with inputs in an open set that contains `0`:** with
`d_in, d_out ≥ d ≥ 2` and blocks of any widths, for an open set `Ω` of inputs with `0 ∈ Ω`, there
is an open set `U` of weights such that: at every `θ ∈ U` the residual network has
`fd = P − d² − s`, attained by the rank of the Jacobian on a finite batch of inputs of `Ω` on
which no pre-activation of a gate vanishes; `U` contains `θ_τ` for generic `θ` and all small
`τ ≠ 0`; and at almost every point of `U` the skips add at least `L d²` when every block has at
least `d` hidden units. -/
theorem exists_isOpen_jacobianRank_smallWrites_reglu_of_isOpen
    (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    {Ω : Set (Matrix T dIn ℝ)} (hΩ : IsOpen Ω) (h0 : (0 : Matrix T dIn ℝ) ∈ Ω) :
    ∃ U : Set (Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut), IsOpen U ∧
      (∀ θ ∈ U, funDim (Arch.gated relu id hid) 1 θ
            + (Fintype.card d ^ 2 + 2 * ∑ ℓ, Fintype.card (hid ℓ))
          = Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut) ∧
        ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i, X i ∈ Ω) ∧
          (∀ (i : Fin n) (ℓ : Fin L) (t : T) (j : hid ℓ),
            (hidden (Arch.gated relu id hid) 1 θ (X i) ℓ.castSucc * θ.read ℓ) t (Sum.inl j)
              ≠ 0) ∧
          jacobianRank (Arch.gated relu id hid) 1 X θ
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
