import SkipsLean.Dimension.Space

/-!
# Functional dimension

Paper (dimension paper): Definition 4.1, and Appendix C, "Notation and flat directions".

For a finite batch `X = (x_1, …, x_n)` of inputs, `evalBatch A S X θ` holds the outputs
`F_θ(x_1), …, F_θ(x_n)`. Its derivative in `θ` is the Jacobian of the paper. The functional
dimension at `θ` is the largest rank of this Jacobian over all finite batches, and the redundancy
is `P` minus it. A direction `η` is flat at `θ` if the derivative of `θ ↦ F_θ(x)` along `η`
vanishes for every input `x`; the flat directions form the subspace `K(θ)`, and the functional
dimension is `P - dim K(θ)`.

The derivative of a map that is not differentiable is `0` in Mathlib, so the statements below
assume that `θ ↦ F_θ(x)` is differentiable at `θ` for every `x`. `differentiable_eval` gives this
when the maps `f_ℓ` and `χ` are differentiable.
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise Topology

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [Fintype dIn] [Fintype dOut]
variable (A : Arch T d L) (S : Fin L → Matrix d d ℝ)

/-- The outputs on a batch `X = (x_1, …, x_n)` of inputs. -/
def evalBatch {n : ℕ} (X : Fin n → Matrix T dIn ℝ) (θ : Params A dIn dOut) :
    Fin n → Matrix T dOut ℝ :=
  fun i => eval A S θ (X i)

/-- The rank of the Jacobian of `θ ↦ (F_θ(x_1), …, F_θ(x_n))` at `θ`. -/
noncomputable def jacobianRank {n : ℕ} (X : Fin n → Matrix T dIn ℝ) (θ : Params A dIn dOut) : ℕ :=
  Module.finrank ℝ (LinearMap.range (fderiv ℝ (evalBatch A S X) θ).toLinearMap)

/-- **Definition 4.1.** The functional dimension at `θ`: the largest rank of the Jacobian of the
outputs on a finite batch of inputs. -/
noncomputable def funDim (θ : Params A dIn dOut) : ℕ :=
  sSup {r : ℕ | ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), r = jacobianRank A S X θ}

/-- **Definition 4.1.** The redundancy at `θ`: `P` minus the functional dimension. -/
noncomputable def redundancy (θ : Params A dIn dOut) : ℕ :=
  Module.finrank ℝ (Params A dIn dOut) - funDim A S θ

/-- The flat directions `K(θ)`: the directions `η` along which the derivative of `θ ↦ F_θ(x)`
vanishes for every input `x`. -/
noncomputable def flat (θ : Params A dIn dOut) : Submodule ℝ (Params A dIn dOut) :=
  ⨅ x : Matrix T dIn ℝ, LinearMap.ker (fderiv ℝ (fun θ' => eval A S θ' x) θ).toLinearMap

variable {A S}

/-- If the maps `f_ℓ` of the blocks and the map `χ` are differentiable, the output at an input
`x` is a differentiable function of the parameters. -/
theorem differentiable_eval (hf : ∀ ℓ, Differentiable ℝ (A.f ℓ)) (hχ : Differentiable ℝ A.χ)
    (x : Matrix T dIn ℝ) :
    Differentiable ℝ (fun θ : Params A dIn dOut => eval A S θ x) := by
  sorry

variable (θ : Params A dIn dOut)

/-- The rank of the Jacobian on any batch is at most the number `P` of parameters. -/
theorem jacobianRank_le_finrank {n : ℕ} (X : Fin n → Matrix T dIn ℝ) :
    jacobianRank A S X θ ≤ Module.finrank ℝ (Params A dIn dOut) := by
  sorry

/-- The functional dimension is attained on some finite batch. -/
theorem exists_jacobianRank_eq_funDim :
    ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), jacobianRank A S X θ = funDim A S θ := by
  sorry

/-- The rank of the Jacobian on any batch is at most the functional dimension. -/
theorem jacobianRank_le_funDim {n : ℕ} (X : Fin n → Matrix T dIn ℝ) :
    jacobianRank A S X θ ≤ funDim A S θ := by
  sorry

/-- **Appendix C, "Notation and flat directions":** the functional dimension is `P - dim K(θ)`. -/
theorem funDim_add_finrank_flat
    (hdiff : ∀ x : Matrix T dIn ℝ, DifferentiableAt ℝ (fun θ' : Params A dIn dOut => eval A S θ' x) θ) :
    funDim A S θ + Module.finrank ℝ (flat A S θ) = Module.finrank ℝ (Params A dIn dOut) := by
  sorry

/-- A subspace of flat directions bounds the functional dimension from above: this is how a
count of symmetries gives an upper bound (the first step of the proof of Theorem 4.3). -/
theorem funDim_add_finrank_le_of_le_flat
    (hdiff : ∀ x : Matrix T dIn ℝ, DifferentiableAt ℝ (fun θ' : Params A dIn dOut => eval A S θ' x) θ)
    (V : Submodule ℝ (Params A dIn dOut)) (hV : V ≤ flat A S θ) :
    funDim A S θ + Module.finrank ℝ V ≤ Module.finrank ℝ (Params A dIn dOut) := by
  sorry

/-- **A direction of a symmetry is flat** (Section 4, the paragraph after Definition 4.1). If a
curve `γ` of parameters passes through `θ` with velocity `η` and the function of the network is
the same along it, then `η` is flat at `θ`. -/
theorem mem_flat_of_hasDerivAt
    (hdiff : ∀ x : Matrix T dIn ℝ, DifferentiableAt ℝ (fun θ' : Params A dIn dOut => eval A S θ' x) θ)
    (γ : ℝ → Params A dIn dOut) (η : Params A dIn dOut) (hγ : HasDerivAt γ η 0) (hγ0 : γ 0 = θ)
    (hconst : ∀ᶠ τ in 𝓝 (0 : ℝ), ∀ x : Matrix T dIn ℝ, eval A S (γ τ) x = eval A S θ x) :
    η ∈ flat A S θ := by
  sorry

end Skips
