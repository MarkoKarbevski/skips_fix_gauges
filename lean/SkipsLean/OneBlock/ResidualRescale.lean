import SkipsLean.OneBlock.Rescale
import SkipsLean.OneBlock.Residual
import SkipsLean.Residual.UpperBoundSymmetries

/-!
# The one-block theorem with a skip, for ReLU and ReLU² blocks

Paper (skips): Theorem 4.6 (i) (Theorem B.1 (i) in the appendix) for a ReLU and for a ReLU² block.
"Let `L = 1` … Without normalization, the residual network satisfies the equality condition. So
does the skipless network, and the skip raises the functional dimension by exactly `d²`."
For these blocks the equality condition with a skip is `fd = P - d² - d_hidden` at generic
parameters, and without a skip `fd = P - 2 d² - d_hidden` (`OneBlock/Rescale.lean`).

As in `OneBlock/Rescale.lean`, two statements are made for each kind of block: the value of
`funDim`, and a batch of inputs with no hidden unit at its kink on which the Jacobian has that
rank. The skip does not change the arguments of the hidden units of the one block, so the inputs
with no hidden unit at its kink are the same set `noKink θ`.

The proof is stated once, for every activation that is positively homogeneous of degree `k`,
differentiable away from `0`, and satisfies Lemma C.3 with the rescalings (`UnitsRescale`), whose
statement includes the linear term `x M` of the skip (`M = E D`).
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {hid : Fin 1 → Type} [∀ ℓ, Fintype (hid ℓ)]
variable {σ σ' : ℝ → ℝ}

/-- At an input with no hidden unit at its kink, the output of a residual network of one block is
differentiable in the parameters, when `σ` is differentiable away from `0`. -/
theorem differentiableAt_eval_residual_of_mem_noKink (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) (x : Matrix T dIn ℝ)
    (hx : x ∈ noKink θ) :
    DifferentiableAt ℝ
      (fun θ' : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut =>
        eval (Arch.mlp σ id hid) 1 θ' x) θ := by
  sorry

/-- **Steps 1 to 3 of the proof of Theorem B.1 (i) for an activation with the rescalings.** Under
the conditions `OneBlockGeneric`, a direction that is flat for the residual network at every
input with no hidden unit at its kink is the sum of the direction of one change of basis, the
same at both hidden states, and a direction of the rescalings of the hidden units. -/
theorem flatOn_noKink_le_mlp_rescale_residual {k : ℕ}
    (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (hU : UnitsRescale σ σ' k dIn dOut (hid 0))
    (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) (hθ : OneBlockGeneric θ)
    (η : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)
    (hη : η ∈ flatOn (Arch.mlp σ id hid) 1 θ (noKink θ)) :
    ∃ (X : Matrix d d ℝ) (α : ∀ ℓ, hid ℓ → ℝ),
      η = cobDir θ (fun _ => X) + rescaleDirMlp k θ α := by
  sorry

/-- **Theorem 4.6 (i) / B.1 (i) for an activation with the rescalings, under the conditions of
the proof:** with a skip, `fd = P - d² - d_hidden`. -/
theorem funDim_mlp_oneBlock_rescale_residual {k : ℕ}
    (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (hhom : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (hU : UnitsRescale σ σ' k dIn dOut (hid 0))
    (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) (hθ : OneBlockGeneric θ) :
    funDim (Arch.mlp σ id hid) 1 θ + (Fintype.card d ^ 2 + Fintype.card (hid 0))
      = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) := by
  sorry

/-- The same rank on a batch of inputs with no hidden unit at its kink. -/
theorem exists_jacobianRank_mlp_oneBlock_rescale_residual {k : ℕ}
    (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (hhom : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (hU : UnitsRescale σ σ' k dIn dOut (hid 0))
    (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) (hθ : OneBlockGeneric θ) :
    ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i, X i ∈ noKink θ) ∧
      jacobianRank (Arch.mlp σ id hid) 1 X θ + (Fintype.card d ^ 2 + Fintype.card (hid 0))
        = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) := by
  sorry

/-- **Theorem 4.6 (i) for a ReLU block, with a skip:** for `d_in, d_out, d_hidden ≥ d ≥ 2`, at
generic parameters, `fd = P - d² - d_hidden`. -/
theorem ae_funDim_relu_oneBlock_residual
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ θ ∂μ, funDim (Arch.mlp relu id hid) 1 θ
        + (Fintype.card d ^ 2 + Fintype.card (hid 0))
      = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut) := by
  sorry

/-- Theorem 4.6 (i) for a ReLU block with a skip, on the paper's inputs: at generic parameters the
Jacobian has the rank `P - d² - d_hidden` on a batch of inputs with no hidden unit at its kink. -/
theorem ae_exists_jacobianRank_relu_oneBlock_residual
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ θ ∂μ, ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i, X i ∈ noKink θ) ∧
      jacobianRank (Arch.mlp relu id hid) 1 X θ
          + (Fintype.card d ^ 2 + Fintype.card (hid 0))
        = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut) := by
  sorry

/-- **Theorem 4.6 (i) for a ReLU block:** at generic parameters the skip raises the functional
dimension by exactly `d²`. -/
theorem ae_funDim_relu_oneBlock_residual_eq_add
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ θ ∂μ, funDim (Arch.mlp relu id hid) 1 θ
      = funDim (Arch.mlp relu id hid) 0 θ + Fintype.card d ^ 2 := by
  sorry

/-- **Theorem 4.6 (i) for a ReLU² block, with a skip:** for `d_in, d_out, d_hidden ≥ d ≥ 2`, at
generic parameters, `fd = P - d² - d_hidden`. -/
theorem ae_funDim_reluSq_oneBlock_residual
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) reluSq id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ θ ∂μ, funDim (Arch.mlp reluSq id hid) 1 θ
        + (Fintype.card d ^ 2 + Fintype.card (hid 0))
      = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) reluSq id hid) dIn dOut) := by
  sorry

/-- Theorem 4.6 (i) for a ReLU² block with a skip, on the paper's inputs. -/
theorem ae_exists_jacobianRank_reluSq_oneBlock_residual
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) reluSq id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ θ ∂μ, ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i, X i ∈ noKink θ) ∧
      jacobianRank (Arch.mlp reluSq id hid) 1 X θ
          + (Fintype.card d ^ 2 + Fintype.card (hid 0))
        = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) reluSq id hid) dIn dOut) := by
  sorry

/-- **Theorem 4.6 (i) for a ReLU² block:** at generic parameters the skip raises the functional
dimension by exactly `d²`. -/
theorem ae_funDim_reluSq_oneBlock_residual_eq_add
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) reluSq id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ θ ∂μ, funDim (Arch.mlp reluSq id hid) 1 θ
      = funDim (Arch.mlp reluSq id hid) 0 θ + Fintype.card d ^ 2 := by
  sorry

end Skips
