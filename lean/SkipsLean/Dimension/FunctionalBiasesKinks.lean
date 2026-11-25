import SkipsLean.Dimension.FunctionalBiases

/-!
# The functional dimension with biases, without a hypothesis of differentiability

Paper (skips paper), Appendix B, "Notation and flat directions": "For the ReLU-type activations,
`F(θ, x)` is differentiable in `θ` at the inputs `x` at which no hidden unit sits at its kink,
which form an open set of full measure, and "every input" means every such input." With biases
the kinks lie on hyperplanes that need not pass through the origin; at an input on one of them
the output need not be differentiable in the parameters.

`Dimension/FunctionalBiases.lean` has the general statements for networks with biases under the
hypothesis that the output at every input is differentiable in `(θ, b)` at the point. Here are
the forms without that hypothesis, the twins of `mem_flat_of_hasDerivAt'`,
`funDim_add_finrank_flat'` and `funDim_add_finrank_le_of_le_flat'` of `Dimension/Functional.lean`.
In Lean the derivative of a map at a point where it is not differentiable is `0`; so an input at
which the output is not differentiable in `(θ, b)` puts no condition on a flat direction, and a
batch that contains such an input has a Jacobian of rank `0`. With this convention:

* `mem_flatB_of_hasDerivAt'`: the velocity of a curve of parameters along which the function does
  not change is flat;
* `funDimB_add_finrank_flatB'`: `fd = P − dim K(θ, b)`;
* `funDimB_add_finrank_le_of_le_flatB'`: a space of flat directions bounds the functional
  dimension.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise Topology

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [Fintype dIn] [Fintype dOut]
variable {A : Arch T d L} {S : Fin L → Matrix d d ℝ} (p : ParamsB A dIn dOut)

/-- Helper: a direction is in the kernel of the Jacobian on a batch of inputs at which the output
is differentiable if and only if the derivative of the output at every input of the batch
vanishes along it. -/
private theorem mem_ker_fderiv_evalBatchB_iff_fbk {n : ℕ} (X : Fin n → Matrix T dIn ℝ)
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

/-- Helper: every flat direction is in the kernel of the Jacobian on every batch: on a batch with
an input at which the output is not differentiable, the Jacobian is `0`. -/
private theorem flatB_le_ker_fbk {n : ℕ} (X : Fin n → Matrix T dIn ℝ) :
    flatB A S p ≤ LinearMap.ker (fderiv ℝ (evalBatchB A S X) p).toLinearMap := by
  by_cases hX : ∀ i,
      DifferentiableAt ℝ (fun q : ParamsB A dIn dOut => evalB A S q.1 q.2 (X i)) p
  · -- every input of the batch is differentiable: the kernel is that at each input
    intro η hη
    rw [flatB, Submodule.mem_iInf] at hη
    rw [mem_ker_fderiv_evalBatchB_iff_fbk p X hX]
    intro i
    have hi := hη (X i)
    rw [LinearMap.mem_ker] at hi
    exact hi
  · -- some output is not differentiable, so neither is the tuple, and its derivative is `0`
    have hnd : ¬DifferentiableAt ℝ (evalBatchB A S X) p := fun h =>
      hX (differentiableAt_pi.1 h)
    rw [fderiv_zero_of_not_differentiableAt hnd]
    intro η _
    exact LinearMap.mem_ker.2 rfl

/-- Helper: some finite batch of inputs at which the output is differentiable has the kernel
`K(θ, b)`: among such batches take one whose kernel has least dimension; adding an input at
which the output is differentiable cannot shrink it, and an input at which it is not puts no
condition. -/
private theorem exists_ker_le_flatB_fbk :
    ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ),
      LinearMap.ker (fderiv ℝ (evalBatchB A S X) p).toLinearMap ≤ flatB A S p := by
  -- `U`: the inputs at which the output is differentiable in `(θ, b)` at `p`
  set U : Set (Matrix T dIn ℝ) :=
    {x | DifferentiableAt ℝ (fun q : ParamsB A dIn dOut => evalB A S q.1 q.2 x) p} with hU
  -- among the kernels on finite batches of inputs of `U`, take one of least dimension
  obtain ⟨n, X, hXU, hX⟩ := Nat.sInf_mem (s := {k : ℕ | ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ),
      (∀ i, X i ∈ U) ∧
        k = Module.finrank ℝ (LinearMap.ker (fderiv ℝ (evalBatchB A S X) p).toLinearMap)})
    ⟨_, 0, fun i => i.elim0, fun i => i.elim0, rfl⟩
  refine ⟨n, X, fun η hη => ?_⟩
  rw [flatB, Submodule.mem_iInf]
  intro x
  by_cases hx : x ∈ U
  · -- the batch with `x` added has its inputs in `U`
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
      rw [mem_ker_fderiv_evalBatchB_iff_fbk p _ hXU'] at hξ
      rw [mem_ker_fderiv_evalBatchB_iff_fbk p X hXU]
      intro i
      simpa only [Fin.cons_succ] using hξ i.succ
    -- ... and its dimension is not smaller, so the kernel stays the same
    have heq := Submodule.eq_of_le_of_finrank_le hle' (by
      rw [← hX]
      exact Nat.sInf_le ⟨n + 1, Fin.cons x X, hXU', rfl⟩)
    -- hence the derivative at `x`, the input added, vanishes along `η`
    rw [← heq, mem_ker_fderiv_evalBatchB_iff_fbk p _ hXU'] at hη
    have h0 := hη 0
    simp only [Fin.cons_zero] at h0
    rw [LinearMap.mem_ker]
    exact h0
  · -- not differentiable at `p`: the derivative is `0`
    rw [fderiv_zero_of_not_differentiableAt hx]
    exact LinearMap.mem_ker.2 rfl

/-- **A direction of a symmetry is flat, with biases, without a hypothesis of
differentiability.** If a curve `γ` of parameters passes through `(θ, b)` with velocity `η` and
the function of the network is the same along it, then `η` is flat at `(θ, b)`. -/
theorem mem_flatB_of_hasDerivAt'
    (γ : ℝ → ParamsB A dIn dOut) (η : ParamsB A dIn dOut) (hγ : HasDerivAt γ η 0)
    (hγ0 : γ 0 = p)
    (hconst : ∀ᶠ τ in 𝓝 (0 : ℝ), ∀ x : Matrix T dIn ℝ,
      evalB A S (γ τ).1 (γ τ).2 x = evalB A S p.1 p.2 x) :
    η ∈ flatB A S p := by
  rw [flatB, Submodule.mem_iInf]
  intro x
  rw [LinearMap.mem_ker]
  show fderiv ℝ (fun q : ParamsB A dIn dOut => evalB A S q.1 q.2 x) p η = 0
  by_cases hx : DifferentiableAt ℝ (fun q : ParamsB A dIn dOut => evalB A S q.1 q.2 x) p
  · -- the chain rule: `τ ↦ F_{γ(τ)}(x)` has derivative `D F(x) η` at `0`
    have hl : HasFDerivAt (fun q : ParamsB A dIn dOut => evalB A S q.1 q.2 x)
        (fderiv ℝ (fun q : ParamsB A dIn dOut => evalB A S q.1 q.2 x) p) (γ 0) := by
      rw [hγ0]
      exact hx.hasFDerivAt
    have h1 := hl.comp_hasDerivAt (0 : ℝ) hγ
    -- the same map is constant near `0`, so its derivative there is `0`
    have h2 : HasDerivAt ((fun q : ParamsB A dIn dOut => evalB A S q.1 q.2 x) ∘ γ) 0 0 :=
      (hasDerivAt_const (0 : ℝ) (evalB A S p.1 p.2 x)).congr_of_eventuallyEq
        (hconst.mono fun τ hτ => hτ x)
    exact h1.unique h2
  · -- not differentiable at `p`: the derivative is `0`
    rw [fderiv_zero_of_not_differentiableAt hx, _root_.zero_apply]

/-- **The functional dimension with biases is `P − dim K(θ, b)`, without a hypothesis of
differentiability** (with Lean's convention that the derivative is `0` where it does not
exist). -/
theorem funDimB_add_finrank_flatB' :
    funDimB A S p + Module.finrank ℝ (flatB A S p) = Module.finrank ℝ (ParamsB A dIn dOut) := by
  -- a finite batch `X₀` whose kernel is `K(θ, b)`
  obtain ⟨n₀, X₀, hX₀⟩ := exists_ker_le_flatB_fbk (S := S) p
  have h₀ : Module.finrank ℝ (LinearMap.ker (fderiv ℝ (evalBatchB A S X₀) p).toLinearMap) =
      Module.finrank ℝ (flatB A S p) := by
    rw [le_antisymm hX₀ (flatB_le_ker_fbk (S := S) p X₀)]
  -- rank–nullity on `X₀`: its rank is `P - dim K(θ, b)`
  have hrn₀ := LinearMap.finrank_range_add_finrank_ker (fderiv ℝ (evalBatchB A S X₀) p).toLinearMap
  -- on every batch the kernel contains `K(θ, b)`, so the rank is at most that on `X₀`
  have hle : funDimB A S p ≤ jacobianRankB A S X₀ p := by
    obtain ⟨n, X, hX⟩ := exists_jacobianRankB_eq_funDimB (S := S) p
    have hrn := LinearMap.finrank_range_add_finrank_ker (fderiv ℝ (evalBatchB A S X) p).toLinearMap
    have hmono := Submodule.finrank_mono (flatB_le_ker_fbk (S := S) p X)
    rw [jacobianRankB] at hX ⊢
    omega
  have hge := jacobianRankB_le_funDimB (S := S) p X₀
  rw [jacobianRankB] at hle hge
  omega

/-- **A space of flat directions bounds the functional dimension with biases,** without a
hypothesis of differentiability: `fd + dim V ≤ P`. -/
theorem funDimB_add_finrank_le_of_le_flatB' (V : Submodule ℝ (ParamsB A dIn dOut))
    (hV : V ≤ flatB A S p) :
    funDimB A S p + Module.finrank ℝ V ≤ Module.finrank ℝ (ParamsB A dIn dOut) := by
  -- `fd + dim K = P` and `dim V ≤ dim K`
  have h := funDimB_add_finrank_flatB' (S := S) p
  have hV' := Submodule.finrank_mono hV
  omega

end Skips
