import SkipsLean.OneBlock.LearnedSkipBound

/-!
# The network whose skips are parameters, without a hypothesis of differentiability

Paper (skips paper): Appendix B, "Notation and flat directions": "For the ReLU-type activations,
`F(θ, x)` is differentiable in `θ` at the inputs `x` at which no hidden unit sits at its kink, which
form an open set of full measure, and 'every input' means every such input." Theorem B.1 (iii) is
stated for ReLU, ReLU² and ReGLU blocks as well: "Let the network be pre-RMSNorm without biases,
with a learned skip `A`, full or upper triangular. For generic parameters and `ε > 0`, its
functional dimension exceeds that of the residual network of part (ii) by exactly
`d_model (d_model + 1)/2`".

`OneBlock/LearnedSkip.lean` and `OneBlock/LearnedSkipBound.lean` state the rank–nullity identity and
the upper bound for differentiable blocks. Here they are stated with no hypothesis on the blocks,
as `Dimension/Functional.lean` does for the networks with fixed skips (`flatOn`, `flat_le_flatOn`,
`funDim_add_finrank_flat'`, `exists_jacobianRank_add_finrank_flatOn`): Mathlib's derivative of a map
at a point where it is not differentiable is `0`, so an input at which `(θ, v) ↦ F_{θ,v}(x)` is not
differentiable puts no condition on the flat directions, and a batch that contains such an input
has a Jacobian of rank `0`.

* `flatSkipsOn A ι p U`: the directions `(η, a)` that are flat at every input of a set `U`.
* `funDimSkips_add_finrank_flatSkips'`: `fd + dim (flat directions) = number of parameters`.
* `exists_jacobianRankSkips_add_finrank_flatSkipsOn`: on a set `U` of inputs at which the output
  is differentiable in `(θ, v)`, a finite batch of inputs of `U` has the rank
  `(number of parameters) − dim (directions flat on U)`.
* `funDimLearned_add_le_rmsNorm'`: the upper bound of `OneBlock/LearnedSkipBound.lean` for one
  block with a full learned skip, for any block.
-/

namespace Skips

open Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The directions `(η, a)` of the weights and the skips that are flat at every input of a set
`U`: the derivative of `(θ, v) ↦ F_{θ,v}(x)` at `p` vanishes along them for every `x ∈ U`. -/
noncomputable def flatSkipsOn (A : Arch T d L) (ι : V →L[ℝ] (Fin L → Matrix d d ℝ))
    (p : Params A dIn dOut × V) (U : Set (Matrix T dIn ℝ)) :
    Submodule ℝ (Params A dIn dOut × V) :=
  ⨅ x ∈ U,
    LinearMap.ker (fderiv ℝ (fun p' : Params A dIn dOut × V => evalSkips A ι p' x) p).toLinearMap

/-- A flat direction is flat at every input of `U`. -/
theorem flatSkips_le_flatSkipsOn (A : Arch T d L) (ι : V →L[ℝ] (Fin L → Matrix d d ℝ))
    (p : Params A dIn dOut × V) (U : Set (Matrix T dIn ℝ)) :
    flatSkips A ι p ≤ flatSkipsOn A ι p U := by
  -- an infimum over every input lies below the infimum over the inputs of `U`
  intro η hη
  rw [flatSkips, Submodule.mem_iInf] at hη
  rw [flatSkipsOn, Submodule.mem_iInf]
  intro x
  rw [Submodule.mem_iInf]
  intro _
  exact hη x

/-! ### Helpers for the rank–nullity identity -/

omit [Fintype T] [DecidableEq d] in
/-- Helper (the private `exists_jacobianRankSkips_eq_lsg` of `OneBlock/LearnedSkip.lean`): under a
bound on the ranks, the functional dimension is attained on a batch. -/
private theorem exists_jacobianRankSkips_eq_lso (A : Arch T d L)
    (ι : V →L[ℝ] (Fin L → Matrix d d ℝ)) (p : Params A dIn dOut × V) (N : ℕ)
    (hN : ∀ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), jacobianRankSkips A ι X p ≤ N) :
    ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), jacobianRankSkips A ι X p = funDimSkips A ι p := by
  -- a nonempty set of naturals bounded above contains its supremum
  obtain ⟨n, X, h⟩ := Nat.sSup_mem (s := {r : ℕ | ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ),
      r = jacobianRankSkips A ι X p}) ⟨_, 0, fun i => i.elim0, rfl⟩
    ⟨N, by rintro _ ⟨n, X, rfl⟩; exact hN n X⟩
  exact ⟨n, X, h.symm⟩

omit [Fintype T] [DecidableEq d] in
/-- Helper (the private `jacobianRankSkips_le_funDimSkips_lsg`): under a bound on the ranks, every
rank is at most the functional dimension. -/
private theorem jacobianRankSkips_le_funDimSkips_lso (A : Arch T d L)
    (ι : V →L[ℝ] (Fin L → Matrix d d ℝ)) (p : Params A dIn dOut × V) (N : ℕ)
    (hN : ∀ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), jacobianRankSkips A ι X p ≤ N)
    {n : ℕ} (X : Fin n → Matrix T dIn ℝ) :
    jacobianRankSkips A ι X p ≤ funDimSkips A ι p :=
  le_csSup ⟨N, by rintro _ ⟨n, X, rfl⟩; exact hN n X⟩ ⟨n, X, rfl⟩

omit [DecidableEq d] in
/-- Helper (the twin of `mem_ker_fderiv_evalBatch_iff'`): on a batch of inputs at which the output
is differentiable, a direction is in the kernel of the Jacobian if and only if the derivative of
the output at every input of the batch vanishes along it. -/
private theorem mem_ker_lso (A : Arch T d L) (ι : V →L[ℝ] (Fin L → Matrix d d ℝ))
    (p : Params A dIn dOut × V) {n : ℕ} (X : Fin n → Matrix T dIn ℝ)
    (hX : ∀ i,
      DifferentiableAt ℝ (fun p' : Params A dIn dOut × V => evalSkips A ι p' (X i)) p)
    (η : Params A dIn dOut × V) :
    η ∈ LinearMap.ker (fderiv ℝ (fun p' : Params A dIn dOut × V => fun i : Fin n =>
        evalSkips A ι p' (X i)) p).toLinearMap ↔
      ∀ i, fderiv ℝ (fun p' => evalSkips A ι p' (X i)) p η = 0 := by
  -- the derivative of the outputs on the batch is the tuple of the derivatives of the outputs
  have h : fderiv ℝ (fun p' : Params A dIn dOut × V => fun i : Fin n =>
        evalSkips A ι p' (X i)) p =
      ContinuousLinearMap.pi fun i => fderiv ℝ (fun p' => evalSkips A ι p' (X i)) p :=
    fderiv_pi hX
  rw [LinearMap.mem_ker]
  show fderiv ℝ (fun p' : Params A dIn dOut × V => fun i : Fin n =>
    evalSkips A ι p' (X i)) p η = 0 ↔ _
  rw [h]
  constructor
  · intro h0 i
    exact congr_fun h0 i
  · intro h0
    funext i
    exact h0 i

omit [DecidableEq d] in
/-- Helper (the twin of `flat_le_ker'`): every flat direction is in the kernel of the Jacobian on
every batch; on a batch with an input at which the output is not differentiable, the Jacobian is
`0`. -/
private theorem flatSkips_le_ker_lso (A : Arch T d L) (ι : V →L[ℝ] (Fin L → Matrix d d ℝ))
    (p : Params A dIn dOut × V) {n : ℕ} (X : Fin n → Matrix T dIn ℝ) :
    flatSkips A ι p ≤ LinearMap.ker (fderiv ℝ (fun p' : Params A dIn dOut × V =>
      fun i : Fin n => evalSkips A ι p' (X i)) p).toLinearMap := by
  by_cases hX : ∀ i,
      DifferentiableAt ℝ (fun p' : Params A dIn dOut × V => evalSkips A ι p' (X i)) p
  · -- every input of the batch is differentiable: the kernel is that at each input
    intro η hη
    rw [flatSkips, Submodule.mem_iInf] at hη
    rw [mem_ker_lso A ι p X hX]
    intro i
    have hi := hη (X i)
    rw [LinearMap.mem_ker] at hi
    exact hi
  · -- some output is not differentiable, so neither is the tuple, and its derivative is `0`
    have hnd : ¬DifferentiableAt ℝ (fun p' : Params A dIn dOut × V =>
        fun i : Fin n => evalSkips A ι p' (X i)) p := fun h => hX (differentiableAt_pi.1 h)
    rw [fderiv_zero_of_not_differentiableAt hnd]
    intro η _
    exact LinearMap.mem_ker.2 rfl

omit [DecidableEq d] in
/-- Helper (the twin of `exists_jacobianRank_add_finrank_flatOn_aux`): among the batches of inputs
of `U`, one whose kernel has least dimension has the kernel `flatSkipsOn A ι p U`; then
rank–nullity. -/
private theorem exists_rank_add_finrank_flatSkipsOn_lso [FiniteDimensional ℝ V] (A : Arch T d L)
    (ι : V →L[ℝ] (Fin L → Matrix d d ℝ)) (p : Params A dIn dOut × V) (U : Set (Matrix T dIn ℝ))
    (hU : ∀ x ∈ U,
      DifferentiableAt ℝ (fun p' : Params A dIn dOut × V => evalSkips A ι p' x) p) :
    ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i, X i ∈ U) ∧
      jacobianRankSkips A ι X p + Module.finrank ℝ (flatSkipsOn A ι p U)
        = Module.finrank ℝ (Params A dIn dOut × V) := by
  -- among the kernels on finite batches of inputs of `U`, take one of least dimension
  obtain ⟨n, X, hXU, hX⟩ := Nat.sInf_mem (s := {k : ℕ | ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ),
      (∀ i, X i ∈ U) ∧ k = Module.finrank ℝ (LinearMap.ker (fderiv ℝ
        (fun p' : Params A dIn dOut × V => fun i : Fin n => evalSkips A ι p' (X i))
          p).toLinearMap)})
    ⟨_, 0, fun i => i.elim0, fun i => i.elim0, rfl⟩
  refine ⟨n, X, hXU, ?_⟩
  -- the directions flat on `U` are in the kernel on `X`, since the inputs of `X` are in `U`
  have hge : flatSkipsOn A ι p U ≤ LinearMap.ker (fderiv ℝ (fun p' : Params A dIn dOut × V =>
      fun i : Fin n => evalSkips A ι p' (X i)) p).toLinearMap := by
    intro η hη
    rw [flatSkipsOn, Submodule.mem_iInf] at hη
    rw [mem_ker_lso A ι p X (fun i => hU _ (hXU i))]
    intro i
    have hi := (Submodule.mem_iInf _).1 (hη (X i)) (hXU i)
    rw [LinearMap.mem_ker] at hi
    exact hi
  -- the kernel on `X` is flat at every input `x` of `U`
  have hle : LinearMap.ker (fderiv ℝ (fun p' : Params A dIn dOut × V =>
      fun i : Fin n => evalSkips A ι p' (X i)) p).toLinearMap ≤ flatSkipsOn A ι p U := by
    intro η hη
    rw [flatSkipsOn, Submodule.mem_iInf]
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
    have hle' : LinearMap.ker (fderiv ℝ (fun p' : Params A dIn dOut × V =>
          fun i : Fin (n + 1) => evalSkips A ι p' ((Fin.cons x X : Fin (n + 1) → _) i))
            p).toLinearMap ≤
        LinearMap.ker (fderiv ℝ (fun p' : Params A dIn dOut × V =>
          fun i : Fin n => evalSkips A ι p' (X i)) p).toLinearMap := by
      intro ξ hξ
      rw [mem_ker_lso A ι p _ (fun i => hU _ (hXU' i))] at hξ
      rw [mem_ker_lso A ι p X (fun i => hU _ (hXU i))]
      intro i
      simpa only [Fin.cons_succ] using hξ i.succ
    -- ... and its dimension is not smaller, so the kernel stays the same
    have heq := Submodule.eq_of_le_of_finrank_le hle' (by
      rw [← hX]
      exact Nat.sInf_le ⟨n + 1, Fin.cons x X, hXU', rfl⟩)
    -- hence the derivative at `x`, the input added, vanishes along `η`
    rw [← heq, mem_ker_lso A ι p _ (fun i => hU _ (hXU' i))] at hη
    have h0 := hη 0
    simp only [Fin.cons_zero] at h0
    rw [LinearMap.mem_ker]
    exact h0
  -- the kernel on `X` is `flatSkipsOn A ι p U`; rank–nullity on `X`
  rw [← le_antisymm hle hge]
  exact LinearMap.finrank_range_add_finrank_ker _

/-- `fd = (number of parameters) − dim K`, for the network whose skips are parameters, with no
hypothesis of differentiability. -/
theorem funDimSkips_add_finrank_flatSkips' [FiniteDimensional ℝ V] (A : Arch T d L)
    (ι : V →L[ℝ] (Fin L → Matrix d d ℝ)) (p : Params A dIn dOut × V) :
    funDimSkips A ι p + Module.finrank ℝ (flatSkips A ι p)
      = Module.finrank ℝ (Params A dIn dOut × V) := by
  -- the inputs outside `U`, where the output is not differentiable at `p`, put no condition on
  -- flat directions: `flatSkipsOn A ι p U = flatSkips A ι p`
  have hflat : flatSkipsOn A ι p
      {x | DifferentiableAt ℝ (fun p' : Params A dIn dOut × V => evalSkips A ι p' x) p}
        = flatSkips A ι p := by
    refine le_antisymm (fun η hη => ?_) (flatSkips_le_flatSkipsOn A ι p _)
    rw [flatSkipsOn, Submodule.mem_iInf] at hη
    rw [flatSkips, Submodule.mem_iInf]
    intro x
    by_cases hx : DifferentiableAt ℝ (fun p' : Params A dIn dOut × V => evalSkips A ι p' x) p
    · exact (Submodule.mem_iInf _).1 (hη x) hx
    · rw [fderiv_zero_of_not_differentiableAt hx]
      exact LinearMap.mem_ker.2 rfl
  -- a batch `X₀` of inputs of `U` has rank `(number of parameters) − dim K(p)`
  obtain ⟨n₀, X₀, -, h₀⟩ := exists_rank_add_finrank_flatSkipsOn_lso A ι p
    {x | DifferentiableAt ℝ (fun p' : Params A dIn dOut × V => evalSkips A ι p' x) p}
    (fun _ hx => hx)
  rw [hflat] at h₀
  -- the ranks are at most the number of parameters, so the functional dimension is attained
  have hN : ∀ (n : ℕ) (X : Fin n → Matrix T dIn ℝ),
      jacobianRankSkips A ι X p ≤ Module.finrank ℝ (Params A dIn dOut × V) :=
    fun _ _ => LinearMap.finrank_range_le _
  obtain ⟨n, X, hX⟩ := exists_jacobianRankSkips_eq_lso A ι p _ hN
  -- on every batch the kernel contains `K(p)`, so the rank is at most that on `X₀`
  have hrn := LinearMap.finrank_range_add_finrank_ker (fderiv ℝ (fun p' : Params A dIn dOut × V =>
    fun i : Fin n => evalSkips A ι p' (X i)) p).toLinearMap
  have hmono := Submodule.finrank_mono (flatSkips_le_ker_lso A ι p X)
  have hge := jacobianRankSkips_le_funDimSkips_lso A ι p _ hN X₀
  unfold jacobianRankSkips at hX hge h₀
  omega

/-- On a set `U` of inputs at which `(θ, v) ↦ F_{θ,v}(x)` is differentiable at `p`, some finite
batch of inputs of `U` has a Jacobian of rank `(number of parameters) − dim K_U(p)`, where `K_U(p)`
are the directions that are flat at every input of `U`. -/
theorem exists_jacobianRankSkips_add_finrank_flatSkipsOn [FiniteDimensional ℝ V] (A : Arch T d L)
    (ι : V →L[ℝ] (Fin L → Matrix d d ℝ)) (p : Params A dIn dOut × V) (U : Set (Matrix T dIn ℝ))
    (hU : ∀ x ∈ U,
      DifferentiableAt ℝ (fun p' : Params A dIn dOut × V => evalSkips A ι p' x) p) :
    ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i, X i ∈ U) ∧
      jacobianRankSkips A ι X p + Module.finrank ℝ (flatSkipsOn A ι p U)
        = Module.finrank ℝ (Params A dIn dOut × V) := by
  -- the argument is in `exists_rank_add_finrank_flatSkipsOn_lso`, above its first use
  exact exists_rank_add_finrank_flatSkipsOn_lso A ι p U hU

/-! ### Flat directions of the family whose skips are parameters -/

omit [DecidableEq d] in
/-- Helper (the twin of `mem_flat_of_hasDerivAt'`): if a curve `γ` through `p` with velocity `v`
keeps the function near `τ = 0`, then `v` is flat. -/
private theorem mem_flatSkips_of_hasDerivAt_lso {A : Arch T d L}
    (ι : V →L[ℝ] (Fin L → Matrix d d ℝ)) (p : Params A dIn dOut × V)
    (γ : ℝ → Params A dIn dOut × V) (v : Params A dIn dOut × V) (hγ : HasDerivAt γ v 0)
    (hγ0 : γ 0 = p)
    (hconst : ∀ᶠ τ in 𝓝 (0 : ℝ), ∀ x : Matrix T dIn ℝ,
      evalSkips A ι (γ τ) x = evalSkips A ι p x) :
    v ∈ flatSkips A ι p := by
  rw [flatSkips, Submodule.mem_iInf]
  intro x
  rw [LinearMap.mem_ker]
  show fderiv ℝ (fun p' => evalSkips A ι p' x) p v = 0
  by_cases hx : DifferentiableAt ℝ (fun p' : Params A dIn dOut × V => evalSkips A ι p' x) p
  · -- the chain rule: `τ ↦ F_{γ(τ)}(x)` has derivative `D_p F(x) v` at `0`
    have hl : HasFDerivAt (fun p' => evalSkips A ι p' x)
        (fderiv ℝ (fun p' => evalSkips A ι p' x) p) (γ 0) := by
      rw [hγ0]
      exact hx.hasFDerivAt
    have h1 := hl.comp_hasDerivAt (0 : ℝ) hγ
    -- the same map is constant near `0`, so its derivative there is `0`
    have h2 : HasDerivAt ((fun p' => evalSkips A ι p' x) ∘ γ) 0 0 :=
      (hasDerivAt_const (0 : ℝ) (evalSkips A ι p x)).congr_of_eventuallyEq
        (hconst.mono fun τ hτ => hτ x)
    exact h1.unique h2
  · -- not differentiable at `p`: Mathlib's derivative is `0`
    rw [fderiv_zero_of_not_differentiableAt hx, _root_.zero_apply]

/-! ### The rotations `exp (τ X_ℓ)` (copies of the private helpers of
`Dimension/UpperBoundRMSNorm.lean`) -/

-- As in Mathlib's `MatrixExponential.lean`: without this option the instances of the operator
-- norm (e.g. `CompleteSpace`) are not found.
set_option backward.isDefEq.respectTransparency false in
/-- The derivative at `τ = 0` of an entry of `exp (τ Y)` is the entry of `Y` (computed with the
operator norm, under which matrices form a normed ring). -/
private theorem hasDerivAt_exp_smul_apply_lso (Y : Matrix d d ℝ) (i j : d) :
    HasDerivAt (fun τ : ℝ => NormedSpace.exp (τ • Y) i j) (Y i j) 0 := by
  let _ : NormedRing (Matrix d d ℝ) := Matrix.linftyOpNormedRing
  let _ : NormedAlgebra ℝ (Matrix d d ℝ) := Matrix.linftyOpNormedAlgebra
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) Y (0 : ℝ)
  rw [zero_smul, NormedSpace.exp_zero, one_mul] at h
  exact (LinearMap.toContinuousLinearMap
    (Matrix.entryLinearMap ℝ ℝ i j)).hasFDerivAt.comp_hasDerivAt 0 h

/-- With the elementwise norm, the derivative of a matrix-valued function is taken entry by
entry. -/
private theorem hasDerivAt_matrix_lso {m n : Type*} [Fintype m] [Fintype n] {f : ℝ → Matrix m n ℝ}
    {f' : Matrix m n ℝ} {x : ℝ} (h : ∀ i j, HasDerivAt (fun τ => f τ i j) (f' i j) x) :
    HasDerivAt f f' x :=
  hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 (h i)

/-- The derivative of `τ ↦ M exp (τ Y)` at `0` is `M Y`. -/
private theorem hasDerivAt_mul_exp_lso {m : Type*} [Fintype m] (M : Matrix m d ℝ)
    (Y : Matrix d d ℝ) :
    HasDerivAt (fun τ : ℝ => M * NormedSpace.exp (τ • Y)) (M * Y) 0 :=
  hasDerivAt_matrix_lso fun i j => by
    simp only [Matrix.mul_apply]
    exact HasDerivAt.fun_sum fun k _ => (hasDerivAt_exp_smul_apply_lso Y k j).const_mul (M i k)

/-- The derivative of `τ ↦ exp (τ Y) M` at `0` is `Y M`. -/
private theorem hasDerivAt_exp_mul_lso {n : Type*} [Fintype n] (Y : Matrix d d ℝ)
    (M : Matrix d n ℝ) :
    HasDerivAt (fun τ : ℝ => NormedSpace.exp (τ • Y) * M) (Y * M) 0 :=
  hasDerivAt_matrix_lso fun i j => by
    simp only [Matrix.mul_apply]
    exact HasDerivAt.fun_sum fun k _ => (hasDerivAt_exp_smul_apply_lso Y i k).mul_const (M k j)

-- See `hasDerivAt_exp_smul_apply_lso` for this option.
set_option backward.isDefEq.respectTransparency false in
/-- The derivative of `τ ↦ exp (-τ Y) S exp (τ Z)` at `0` is `−Y S + S Z` (the product rule,
with the operator norm). -/
private theorem hasDerivAt_exp_mul_exp_lso (Y Z S : Matrix d d ℝ) :
    HasDerivAt (fun τ : ℝ => NormedSpace.exp (τ • -Y) * S * NormedSpace.exp (τ • Z))
      (-(Y * S) + S * Z) 0 := by
  let _ : NormedRing (Matrix d d ℝ) := Matrix.linftyOpNormedRing
  let _ : NormedAlgebra ℝ (Matrix d d ℝ) := Matrix.linftyOpNormedAlgebra
  have h1 := hasDerivAt_exp_smul_const (𝕂 := ℝ) (-Y) (0 : ℝ)
  have h2 := hasDerivAt_exp_smul_const (𝕂 := ℝ) Z (0 : ℝ)
  have h := (h1.mul_const S).fun_mul h2
  simp only [zero_smul, NormedSpace.exp_zero, one_mul, mul_one] at h
  rw [neg_mul] at h
  exact h

/-- `exp (τ Y) exp (-τ Y) = 1`. -/
private theorem exp_smul_mul_exp_smul_neg_lso (Y : Matrix d d ℝ) (τ : ℝ) :
    NormedSpace.exp (τ • Y) * NormedSpace.exp (τ • -Y) = 1 := by
  rw [← Matrix.exp_add_of_commute _ _ (((Commute.refl Y).neg_right.smul_left τ).smul_right τ),
    smul_neg, add_neg_cancel, NormedSpace.exp_zero]

/-- The invertible matrix `exp (τ Y)`, with inverse `exp (-τ Y)`. -/
private noncomputable def expGL_lso (Y : Matrix d d ℝ) (τ : ℝ) : GL d ℝ :=
  ⟨NormedSpace.exp (τ • Y), NormedSpace.exp (τ • -Y), exp_smul_mul_exp_smul_neg_lso Y τ,
    by simpa only [neg_neg] using exp_smul_mul_exp_smul_neg_lso (-Y) τ⟩

/-- `exp (0 Y) = 1`. -/
private theorem expGL_zero_lso (Y : Matrix d d ℝ) : expGL_lso Y 0 = 1 := by
  apply Units.ext
  change NormedSpace.exp ((0 : ℝ) • Y) = 1
  rw [zero_smul, NormedSpace.exp_zero]

/-- For antisymmetric `Y`, `exp (τ Y)` is orthogonal: `exp (τ Y)ᵀ = exp (τ Yᵀ) = exp (-τ Y)`. -/
private theorem expGL_mem_orthogonalGroup_lso {Y : Matrix d d ℝ} (hY : Yᵀ = -Y) (τ : ℝ) :
    (expGL_lso Y τ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ := by
  rw [Matrix.mem_orthogonalGroup_iff']
  change (NormedSpace.exp (τ • Y))ᵀ * NormedSpace.exp (τ • Y) = 1
  rw [← Matrix.exp_transpose, Matrix.transpose_smul, hY]
  simpa only [neg_neg] using exp_smul_mul_exp_smul_neg_lso (-Y) τ

omit [Fintype T] [Fintype dIn] [Fintype dOut] in
/-- The curve `τ ↦ θ.cob (exp (τ X_ℓ)) (exp (τ X_ℓ))` passes through `θ` at `τ = 0`. -/
private theorem cob_expGL_zero_lso {A : Arch T d L} (θ : Params A dIn dOut)
    (X : Fin (L + 1) → Matrix d d ℝ) :
    θ.cob (fun ℓ => expGL_lso (X ℓ) 0) (fun ℓ => expGL_lso (X ℓ) 0) = θ := by
  simp only [expGL_zero_lso]
  refine Params.ext' ?_ (fun ℓ => ?_) (fun ℓ => ?_) ?_ <;>
    simp only [Params.cob, inv_one, Units.val_one, Matrix.mul_one, Matrix.one_mul]

omit [Fintype T] in
/-- The curve `τ ↦ θ.cob (exp (τ X_ℓ)) (exp (τ X_ℓ))` has velocity `cobDir θ X` at `τ = 0`. -/
private theorem hasDerivAt_cob_expGL_lso {A : Arch T d L} (θ : Params A dIn dOut)
    (X : Fin (L + 1) → Matrix d d ℝ) :
    HasDerivAt (fun τ : ℝ => θ.cob (fun ℓ => expGL_lso (X ℓ) τ) (fun ℓ => expGL_lso (X ℓ) τ))
      (cobDir θ X) 0 := by
  -- The norm of the parameters is that of the tuple of their components.
  let e : Params A dIn dOut ≃L[ℝ] Params.Prod A dIn dOut :=
    Params.linearEquivProd.toContinuousLinearEquiv
  -- Componentwise: `E exp (τ X_0)`, `exp (-τ X_{ℓ-1}) W_read^ℓ`, `W_write^ℓ exp (τ X_ℓ)`,
  -- `exp (-τ X_L) D`.
  have key : HasDerivAt
      (fun τ : ℝ => e (θ.cob (fun ℓ => expGL_lso (X ℓ) τ) (fun ℓ => expGL_lso (X ℓ) τ)))
      (e (cobDir θ X)) 0 := by
    refine HasDerivAt.prodMk ?_ (HasDerivAt.prodMk ?_ (HasDerivAt.prodMk ?_ ?_))
    · exact hasDerivAt_mul_exp_lso θ.E (X 0)
    · exact hasDerivAt_pi.2 fun ℓ =>
        (hasDerivAt_exp_mul_lso (-X ℓ.castSucc) (θ.read ℓ)).congr_deriv (Matrix.neg_mul _ _)
    · exact hasDerivAt_pi.2 fun ℓ => hasDerivAt_mul_exp_lso (θ.write ℓ) (X ℓ.succ)
    · exact (hasDerivAt_exp_mul_lso (-X (Fin.last L)) θ.D).congr_deriv (Matrix.neg_mul _ _)
  -- Back to the parameters through `e⁻¹`.
  exact e.symm.hasFDerivAt.comp_hasDerivAt (0 : ℝ) key

/-- **The rotations are flat** (Proposition 3.2 under pre-RMSNorm with the skips as parameters):
for antisymmetric `X_ℓ`, the orthogonal changes of basis `G_ℓ = exp (τ X_ℓ)` together with
`S_ℓ ↦ G_{ℓ-1}⁻¹ S_ℓ G_ℓ` keep the function, so their direction
`(cobDir θ X, −X_{ℓ-1} S_ℓ + S_ℓ X_ℓ)` is flat. -/
private theorem rot_mem_flatSkips_lso {A : Arch T d L} {ε : ℝ} (hA : A.χ = rmsNorm ε)
    (θ : Params A dIn dOut) (S : Fin L → Matrix d d ℝ) (X : Fin (L + 1) → Matrix d d ℝ)
    (hX : ∀ ℓ, (X ℓ)ᵀ = -X ℓ) :
    (cobDir θ X, fun ℓ => -(X ℓ.castSucc * S ℓ) + S ℓ * X ℓ.succ)
      ∈ flatSkips A (ContinuousLinearMap.id ℝ (Fin L → Matrix d d ℝ)) (θ, S) := by
  -- the curve `τ ↦ (θ.cob G_τ G_τ, cobSkip S G_τ)` with `G_τ ℓ = exp (τ X_ℓ)` and its velocity
  have hγ : HasDerivAt (fun τ : ℝ => (θ.cob (fun ℓ => expGL_lso (X ℓ) τ)
      (fun ℓ => expGL_lso (X ℓ) τ), cobSkip S (fun ℓ => expGL_lso (X ℓ) τ)))
      (cobDir θ X, fun ℓ => -(X ℓ.castSucc * S ℓ) + S ℓ * X ℓ.succ) 0 :=
    (hasDerivAt_cob_expGL_lso θ X).prodMk
      (hasDerivAt_pi.2 fun ℓ => hasDerivAt_exp_mul_exp_lso (X ℓ.castSucc) (X ℓ.succ) (S ℓ))
  refine mem_flatSkips_of_hasDerivAt_lso _ _ _ _ hγ ?_ ?_
  · -- at `τ = 0` the curve is at `(θ, S)`
    refine Prod.ext (cob_expGL_zero_lso θ X) ?_
    show cobSkip S (fun ℓ => expGL_lso (X ℓ) 0) = S
    funext ℓ
    simp only [cobSkip, expGL_zero_lso, inv_one, Units.val_one, Matrix.one_mul, Matrix.mul_one]
  · -- along the curve the function is kept: pre-RMSNorm commutes with the orthogonal `G_τ ℓ`
    refine Filter.Eventually.of_forall fun τ x => ?_
    have hχ : ∀ ℓ (h : Matrix T d ℝ), A.χ (h * (expGL_lso (X ℓ) τ : Matrix d d ℝ))
        = A.χ h * (expGL_lso (X ℓ) τ : Matrix d d ℝ) := by
      intro ℓ h
      rw [hA]
      exact rmsNorm_mul_orthogonal ε (expGL_mem_orthogonalGroup_lso (hX ℓ) τ) h
    exact eval_cob (M := S) (θ := θ) (G := fun ℓ => expGL_lso (X ℓ) τ)
      (K := fun ℓ => expGL_lso (X ℓ) τ) (x := x) hχ

/-! ### The symmetries inside the block -/

omit [Fintype T] [DecidableEq d] [Fintype dOut] in
/-- Helper (the private `eval_eq_of_blocks_ibl` of `Symmetry/InsideBlocks.lean`): two parameters
with the same `E`, the same `D` and the same output of every block on every hidden state compute
the same function, for any stream matrices. -/
private theorem eval_eq_of_blocks_lso {A : Arch T d L} (θ₁ θ₂ : Params A dIn dOut)
    (hE : θ₂.E = θ₁.E) (hD : θ₂.D = θ₁.D)
    (hb : ∀ ℓ (h : Matrix T d ℝ),
      A.f ℓ (h * θ₂.read ℓ) * θ₂.write ℓ = A.f ℓ (h * θ₁.read ℓ) * θ₁.write ℓ)
    (S : Fin L → Matrix d d ℝ) (x : Matrix T dIn ℝ) :
    eval A S θ₂ x = eval A S θ₁ x := by
  -- the hidden states agree, by induction along the network
  have hh : ∀ ℓ : Fin (L + 1), hidden A S θ₂ x ℓ = hidden A S θ₁ x ℓ := by
    intro ℓ
    induction ℓ using Fin.induction with
    | zero => rw [hidden_zero, hidden_zero, hE]
    | succ ℓ ih => rw [hidden_succ, hidden_succ, ih, hb]
  -- hence the outputs agree
  rw [eval, eval, hh, hD]

omit [DecidableEq d] in
/-- A direction `η` of a symmetry inside the blocks, with the skips not moving, is flat: the
curve `τ ↦ (γ τ, S)` keeps `E`, `D` and the map of every block. -/
private theorem insideBlocks_mem_flatSkips_lso {A : Arch T d L} {θ η : Params A dIn dOut}
    (h : InsideBlocks A θ η) (S : Fin L → Matrix d d ℝ) :
    (η, 0) ∈ flatSkips A (ContinuousLinearMap.id ℝ (Fin L → Matrix d d ℝ)) (θ, S) := by
  obtain ⟨γ, h0, hd, hev⟩ := h
  refine mem_flatSkips_of_hasDerivAt_lso _ _ (fun τ => (γ τ, S)) _
    (hd.prodMk (hasDerivAt_const (0 : ℝ) S)) (by simp only [h0]) ?_
  filter_upwards [hev] with τ hτ x
  exact eval_eq_of_blocks_lso θ (γ τ) hτ.1 hτ.2.1 hτ.2.2 S x

omit [DecidableEq d] in
/-- The directions `(u, 0)`, `u` in the span of the directions of symmetries inside the blocks,
are flat (the flat directions form a subspace). -/
private theorem span_mem_flatSkips_lso {A : Arch T d L} {θ u : Params A dIn dOut}
    (hu : u ∈ Submodule.span ℝ {η | InsideBlocks A θ η}) (S : Fin L → Matrix d d ℝ) :
    (u, 0) ∈ flatSkips A (ContinuousLinearMap.id ℝ (Fin L → Matrix d d ℝ)) (θ, S) := by
  have hle : Submodule.span ℝ {η | InsideBlocks A θ η}
      ≤ (flatSkips A (ContinuousLinearMap.id ℝ (Fin L → Matrix d d ℝ)) (θ, S)).comap
        (LinearMap.inl ℝ (Params A dIn dOut) (Fin L → Matrix d d ℝ)) :=
    Submodule.span_le.2 fun η hη => insideBlocks_mem_flatSkips_lso hη S
  exact hle hu

omit [Fintype T] [DecidableEq d] in
/-- The directions spanned by directions of symmetries inside the blocks have `E` component `0`
(the copy of the private `E_eq_zero_of_mem_span_ibl`). -/
private theorem E_eq_zero_of_mem_span_lso {A : Arch T d L} {θ v : Params A dIn dOut}
    (hv : v ∈ Submodule.span ℝ {η | InsideBlocks A θ η}) : v.E = 0 := by
  induction hv using Submodule.span_induction with
  | mem x hx => exact InsideBlocks.E_eq_zero hx
  | zero => rfl
  | add x y _ _ hx hy => rw [Params.add_E, hx, hy, add_zero]
  | smul a x _ hx => rw [Params.smul_E, hx, smul_zero]

omit [Fintype T] [DecidableEq d] in
/-- The directions spanned by directions of symmetries inside the blocks have `D` component
`0`. -/
private theorem D_eq_zero_of_mem_span_lso {A : Arch T d L} {θ v : Params A dIn dOut}
    (hv : v ∈ Submodule.span ℝ {η | InsideBlocks A θ η}) : v.D = 0 := by
  induction hv using Submodule.span_induction with
  | mem x hx => exact InsideBlocks.D_eq_zero hx
  | zero => rfl
  | add x y _ _ hx hy => rw [Params.add_D, hx, hy, add_zero]
  | smul a x _ hx => rw [Params.smul_D, hx, smul_zero]

/-! ### Independence -/

/-- Helper (the private `cancel_left_of_rank_ibl`): a matrix `M` of rank equal to its number of
columns cancels on the left, `M X = M Y → X = Y` (its kernel is `0` by rank–nullity). -/
private theorem cancel_left_of_rank_lso {m n k : Type*} [Fintype n] (M : Matrix m n ℝ)
    (hM : M.rank = Fintype.card n) {X Y : Matrix n k ℝ} (h : M * X = M * Y) : X = Y := by
  -- `v ↦ M v` is injective: `rank M + dim ker M = card n`
  have hinj : Function.Injective M.mulVecLin := by
    rw [← LinearMap.ker_eq_bot, ← Submodule.finrank_eq_zero]
    have := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
    rw [Module.finrank_fintype_fun_eq_card] at this
    rw [Matrix.rank] at hM
    omega
  -- compare `X` and `Y` column by column
  ext i j
  have hcol : M.mulVecLin (fun l => X l j) = M.mulVecLin (fun l => Y l j) := by
    funext p
    have := congrFun (congrFun h p) j
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
  exact congrFun (hinj hcol) i

/-- A matrix `M` of rank equal to its number of rows cancels on the right, `X M = Y M → X = Y`
(transpose, and cancel `Mᵀ` on the left). -/
private theorem cancel_right_of_rank_lso {m n k : Type*} [Fintype m] [Fintype n]
    (M : Matrix n m ℝ) (hM : M.rank = Fintype.card n) {X Y : Matrix k n ℝ}
    (h : X * M = Y * M) : X = Y := by
  have h' := congrArg Matrix.transpose h
  rw [Matrix.transpose_mul, Matrix.transpose_mul] at h'
  have hMt : Mᵀ.rank = Fintype.card n := by rw [Matrix.rank_transpose, hM]
  exact Matrix.transpose_injective (cancel_left_of_rank_lso Mᵀ hMt h')

/-- The direction of the skips under the changes of basis `X`: `S_ℓ ↦ −X_{ℓ-1} S_ℓ + S_ℓ X_ℓ`,
linear in `X`. -/
private noncomputable def skipDirLin_lso (S : Fin L → Matrix d d ℝ) :
    (Fin (L + 1) → Matrix d d ℝ) →ₗ[ℝ] (Fin L → Matrix d d ℝ) where
  toFun X ℓ := -(X ℓ.castSucc * S ℓ) + S ℓ * X ℓ.succ
  map_add' X Y := by
    funext ℓ
    simp only [Pi.add_apply, Matrix.add_mul, Matrix.mul_add, neg_add]
    abel
  map_smul' c X := by
    funext ℓ
    simp only [Pi.smul_apply, Matrix.smul_mul, Matrix.mul_smul, smul_neg, smul_add,
      RingHom.id_apply]


/-- **The upper bound for one block with a full learned skip under pre-RMSNorm, for any block:**
if `E` and `D` have rank `d` and `U` is a space spanned by directions of symmetries inside the
block, then `fd + d (d − 1) + dim U ≤ P + d²`, where `P` counts the weights without the skip. This
is `funDimLearned_add_le_rmsNorm` without the hypothesis that the block is differentiable. It is
stated for every real `ε`; for `ε = 0` the map `rmsNorm 0` is Lean's total function, the changes of
basis used are the orthogonal ones, and the paper's bound for `ε = 0` (with the scalings) is not
stated here. -/
theorem funDimLearned_add_le_rmsNorm' {A : Arch T d 1} (ε : ℝ) (hA : A.χ = rmsNorm ε)
    (p : Params A dIn dOut × (Fin 1 → Matrix d d ℝ))
    (hE : p.1.E.rank = Fintype.card d) (hD : p.1.D.rank = Fintype.card d)
    (U : Submodule ℝ (Params A dIn dOut))
    (hU : U ≤ Submodule.span ℝ {η | InsideBlocks A p.1 η}) :
    funDimLearned A p + (Fintype.card d * (Fintype.card d - 1) + Module.finrank ℝ U)
      ≤ Module.finrank ℝ (Params A dIn dOut) + Fintype.card d ^ 2 := by
  -- The families `X = (X_0, X_1)` of antisymmetric matrices, as matrices.
  let Ψ : (Fin (1 + 1) → antisymmetric d) →ₗ[ℝ] (Fin (1 + 1) → Matrix d d ℝ) :=
    LinearMap.compLeft (antisymmetric d).subtype (Fin (1 + 1))
  -- The linear map `(X, u) ↦ (cobDir θ X, −X_0 S + S X_1) + (u, 0)`.
  let Φ : (Fin (1 + 1) → antisymmetric d) × U →ₗ[ℝ]
      Params A dIn dOut × (Fin 1 → Matrix d d ℝ) :=
    (((cobDirLin p.1).comp Ψ).prod ((skipDirLin_lso p.2).comp Ψ)).coprod
      ((LinearMap.inl ℝ (Params A dIn dOut) (Fin 1 → Matrix d d ℝ)).comp U.subtype)
  -- Its directions are flat: the rotations are (Step 1), and so are the symmetries inside the
  -- block (Step 2).
  have hflat : LinearMap.range Φ
      ≤ flatSkips A (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) p := by
    rintro _ ⟨⟨X, u⟩, rfl⟩
    rw [LinearMap.coprod_apply]
    exact Submodule.add_mem _
      (rot_mem_flatSkips_lso hA p.1 p.2 (fun ℓ => (X ℓ : Matrix d d ℝ)) fun ℓ => (X ℓ).2)
      (span_mem_flatSkips_lso (hU u.2) p.2)
  -- It is injective (Step 3): `u` has `E` and `D` components `0`, so the `E` component `E X_0`
  -- gives `X_0`, the `D` component `−X_1 D` gives `X_1`, and then the rest gives `u`.
  have hinj : Function.Injective Φ := by
    rintro ⟨X, u⟩ ⟨Y, u'⟩ h
    have h1 : cobDir p.1 (fun ℓ => (X ℓ : Matrix d d ℝ)) + (u : Params A dIn dOut)
        = cobDir p.1 (fun ℓ => (Y ℓ : Matrix d d ℝ)) + (u' : Params A dIn dOut) :=
      congrArg Prod.fst h
    have hu0 := E_eq_zero_of_mem_span_lso (hU u.2)
    have hu0' := E_eq_zero_of_mem_span_lso (hU u'.2)
    have hv0 := D_eq_zero_of_mem_span_lso (hU u.2)
    have hv0' := D_eq_zero_of_mem_span_lso (hU u'.2)
    -- the embedding: `E X_0 = E Y_0`
    have hX0 : (X 0 : Matrix d d ℝ) = Y 0 := by
      have h2 := congrArg Params.E h1
      rw [Params.add_E, Params.add_E, hu0, hu0', add_zero, add_zero] at h2
      exact cancel_left_of_rank_lso p.1.E hE h2
    -- the readout: `−X_1 D = −Y_1 D`
    have hX1 : (X (Fin.last 1) : Matrix d d ℝ) = Y (Fin.last 1) := by
      have h2 := congrArg Params.D h1
      rw [Params.add_D, Params.add_D, hv0, hv0', add_zero, add_zero] at h2
      have h3 : -((X (Fin.last 1) : Matrix d d ℝ) * p.1.D)
          = -((Y (Fin.last 1) : Matrix d d ℝ) * p.1.D) := h2
      exact cancel_right_of_rank_lso p.1.D hD (neg_inj.1 h3)
    have hXY : X = Y := by
      refine funext fun ℓ => Subtype.ext ?_
      fin_cases ℓ
      exacts [hX0, hX1]
    subst hXY
    exact Prod.ext rfl (Subtype.ext (add_left_cancel h1))
  -- The source has dimension `2 · d (d − 1) / 2 + dim U = d (d − 1) + dim U`.
  have hdim : Module.finrank ℝ ((Fin (1 + 1) → antisymmetric d) × U)
      = Fintype.card d * (Fintype.card d - 1) + Module.finrank ℝ U := by
    rw [Module.finrank_prod,
      Module.finrank_pi_fintype (R := ℝ) (ι := Fin (1 + 1)) (M := fun _ => antisymmetric d),
      finrank_antisymmetric, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    have h2 := Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self (Fintype.card d))
    generalize Fintype.card d * (Fintype.card d - 1) = n at h2 ⊢
    omega
  -- So the flat directions have dimension at least `d (d − 1) + dim U`.
  have hmono : Fintype.card d * (Fintype.card d - 1) + Module.finrank ℝ U
      ≤ Module.finrank ℝ (flatSkips A (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) p) :=
    calc Fintype.card d * (Fintype.card d - 1) + Module.finrank ℝ U
        = Module.finrank ℝ ((Fin (1 + 1) → antisymmetric d) × U) := hdim.symm
      _ = Module.finrank ℝ (LinearMap.range Φ) := (LinearMap.finrank_range_of_inj hinj).symm
      _ ≤ _ := Submodule.finrank_mono hflat
  -- Step 4: `fd + dim(flat) = P + d²`, with no hypothesis of differentiability.
  have hsum : funDimLearned A p
      + Module.finrank ℝ (flatSkips A (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) p)
      = Module.finrank ℝ (Params A dIn dOut × (Fin 1 → Matrix d d ℝ)) :=
    funDimSkips_add_finrank_flatSkips' A _ p
  have hP : Module.finrank ℝ (Params A dIn dOut × (Fin 1 → Matrix d d ℝ))
      = Module.finrank ℝ (Params A dIn dOut) + Fintype.card d ^ 2 := by
    rw [Module.finrank_prod, Module.finrank_pi_fintype, Module.finrank_matrix]
    simp [sq]
  calc funDimLearned A p + (Fintype.card d * (Fintype.card d - 1) + Module.finrank ℝ U)
      ≤ funDimLearned A p
        + Module.finrank ℝ (flatSkips A (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) p) :=
        Nat.add_le_add_left hmono _
    _ = Module.finrank ℝ (Params A dIn dOut × (Fin 1 → Matrix d d ℝ)) := hsum
    _ = _ := hP

end Skips
