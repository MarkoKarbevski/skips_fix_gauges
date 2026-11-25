import SkipsLean.Dimension.FunctionalBiasesKinks

/-!
# Directions with biases that are flat on a set of inputs

Paper (skips paper), Appendix B, "Notation and flat directions": "For the ReLU-type activations,
`F(θ, x)` is differentiable in `θ` at the inputs `x` at which no hidden unit sits at its kink,
which form an open set of full measure, and "every input" means every such input."

For networks with biases (`Network/Biases.lean`), the twins of `flatOn`, `flat_le_flatOn` and
`exists_jacobianRank_add_finrank_flatOn` of `Dimension/Functional.lean`:

* `flatOnB A S p U`: the directions of weights and biases that are flat at every input of `U`;
* `flatB_le_flatOnB`: a flat direction is flat at every input of `U`;
* `exists_jacobianRankB_add_finrank_flatOnB`: if the output at every input of `U` is
  differentiable in `(θ, b)` at `p`, some finite batch of inputs of `U` has a Jacobian of rank
  `P − dim K_U(θ, b)`. With `U` the inputs at which no hidden unit sits at its kink, this is the
  rank on the paper's inputs.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise Topology

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [Fintype dIn] [Fintype dOut]

/-- The directions of weights and biases that are flat at every input of a set `U`. -/
noncomputable def flatOnB (A : Arch T d L) (S : Fin L → Matrix d d ℝ) (p : ParamsB A dIn dOut)
    (U : Set (Matrix T dIn ℝ)) : Submodule ℝ (ParamsB A dIn dOut) :=
  ⨅ x ∈ U,
    LinearMap.ker (fderiv ℝ (fun q : ParamsB A dIn dOut => evalB A S q.1 q.2 x) p).toLinearMap

variable {A : Arch T d L} {S : Fin L → Matrix d d ℝ} (p : ParamsB A dIn dOut)

omit [Fintype T] in
/-- A flat direction is flat at every input of `U`. -/
theorem flatB_le_flatOnB (U : Set (Matrix T dIn ℝ)) : flatB A S p ≤ flatOnB A S p U := by
  -- an infimum over every input lies below the infimum over the inputs of `U`
  intro η hη
  rw [flatB, Submodule.mem_iInf] at hη
  rw [flatOnB, Submodule.mem_iInf]
  intro x
  rw [Submodule.mem_iInf]
  intro _
  exact hη x

/-- Helper: a direction is in the kernel of the Jacobian on a batch of inputs at which the output
is differentiable if and only if the derivative of the output at every input of the batch
vanishes along it. -/
private theorem mem_ker_fderiv_evalBatchB_iff_fbo {n : ℕ} (X : Fin n → Matrix T dIn ℝ)
    (hX : ∀ i, DifferentiableAt ℝ (fun q : ParamsB A dIn dOut => evalB A S q.1 q.2 (X i)) p)
    (η : ParamsB A dIn dOut) :
    η ∈ LinearMap.ker (fderiv ℝ (evalBatchB A S X) p).toLinearMap ↔
      ∀ i, fderiv ℝ (fun q : ParamsB A dIn dOut => evalB A S q.1 q.2 (X i)) p η = 0 := by
  -- the derivative of the outputs on the batch is the tuple of the derivatives of the outputs
  have h : fderiv ℝ (evalBatchB A S X) p =
      ContinuousLinearMap.pi fun i =>
        fderiv ℝ (fun q : ParamsB A dIn dOut => evalB A S q.1 q.2 (X i)) p :=
    fderiv_pi hX
  rw [LinearMap.mem_ker]
  show fderiv ℝ (evalBatchB A S X) p η = 0 ↔ _
  rw [h]
  constructor
  · intro h0 i
    exact congr_fun h0 i
  · intro h0
    funext i
    exact h0 i

/-- On a set `U` of inputs at which `(θ, b) ↦ F_{θ,b}(x)` is differentiable at `p`, some finite
batch of inputs of `U` has a Jacobian of rank `P − dim K_U(θ, b)`, where `K_U(θ, b)` are the
directions that are flat at every input of `U`. -/
theorem exists_jacobianRankB_add_finrank_flatOnB (U : Set (Matrix T dIn ℝ))
    (hU : ∀ x ∈ U,
      DifferentiableAt ℝ (fun q : ParamsB A dIn dOut => evalB A S q.1 q.2 x) p) :
    ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i, X i ∈ U) ∧
      jacobianRankB A S X p + Module.finrank ℝ (flatOnB A S p U)
        = Module.finrank ℝ (ParamsB A dIn dOut) := by
  -- among the kernels on finite batches of inputs of `U`, take one of least dimension
  obtain ⟨n, X, hXU, hX⟩ := Nat.sInf_mem (s := {k : ℕ | ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ),
      (∀ i, X i ∈ U) ∧
        k = Module.finrank ℝ (LinearMap.ker (fderiv ℝ (evalBatchB A S X) p).toLinearMap)})
    ⟨_, 0, fun i => i.elim0, fun i => i.elim0, rfl⟩
  refine ⟨n, X, hXU, ?_⟩
  -- the directions flat on `U` are in the kernel on `X`, since the inputs of `X` are in `U`
  have hge : flatOnB A S p U ≤ LinearMap.ker (fderiv ℝ (evalBatchB A S X) p).toLinearMap := by
    intro η hη
    rw [flatOnB, Submodule.mem_iInf] at hη
    rw [mem_ker_fderiv_evalBatchB_iff_fbo p X (fun i => hU _ (hXU i))]
    intro i
    have hi := (Submodule.mem_iInf _).1 (hη (X i)) (hXU i)
    rw [LinearMap.mem_ker] at hi
    exact hi
  -- the kernel on `X` is flat at every input `x` of `U`
  have hle : LinearMap.ker (fderiv ℝ (evalBatchB A S X) p).toLinearMap ≤ flatOnB A S p U := by
    intro η hη
    rw [flatOnB, Submodule.mem_iInf]
    intro x
    rw [Submodule.mem_iInf]
    intro hx
    -- the batch with `x` added has its inputs in `U`
    have hXU' : ∀ i, (Fin.cons x X : Fin (n + 1) → Matrix T dIn ℝ) i ∈ U := by
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa only [Fin.cons_zero] using hx
      · simpa only [Fin.cons_succ] using hXU j
    -- adding the input `x` to the batch can only shrink the kernel ...
    have hle' : LinearMap.ker (fderiv ℝ (evalBatchB A S
          (Fin.cons x X : Fin (n + 1) → Matrix T dIn ℝ)) p).toLinearMap ≤
        LinearMap.ker (fderiv ℝ (evalBatchB A S X) p).toLinearMap := by
      intro ξ hξ
      rw [mem_ker_fderiv_evalBatchB_iff_fbo p _ (fun i => hU _ (hXU' i))] at hξ
      rw [mem_ker_fderiv_evalBatchB_iff_fbo p X (fun i => hU _ (hXU i))]
      intro i
      simpa only [Fin.cons_succ] using hξ i.succ
    -- ... and its dimension is not smaller, so the kernel stays the same
    have heq := Submodule.eq_of_le_of_finrank_le hle' (by
      rw [← hX]
      exact Nat.sInf_le ⟨n + 1, Fin.cons x X, hXU', rfl⟩)
    -- hence the derivative at `x`, the input added, vanishes along `η`
    rw [← heq, mem_ker_fderiv_evalBatchB_iff_fbo p _ (fun i => hU _ (hXU' i))] at hη
    have h0 := hη 0
    simp only [Fin.cons_zero] at h0
    rw [LinearMap.mem_ker]
    exact h0
  -- the kernel on `X` is `K_U(θ, b)`; rank–nullity on `X`
  rw [← le_antisymm hle hge]
  exact LinearMap.finrank_range_add_finrank_ker _

end Skips
