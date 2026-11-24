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

omit [Fintype T] in
/-- A linear map on the parameters is differentiable: the space of parameters is
finite-dimensional, so the map is continuous. -/
private theorem differentiable_linear {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (l : Params A dIn dOut →ₗ[ℝ] F) : Differentiable ℝ l := by
  rw [← LinearMap.coe_toContinuousLinearMap' l]
  exact (LinearMap.toContinuousLinearMap l).differentiable

omit [Fintype T] in
/-- The embedding `E` is a differentiable (linear) function of the parameters. -/
private theorem differentiable_E : Differentiable ℝ (fun θ : Params A dIn dOut => θ.E) := by
  let l : Params A dIn dOut →ₗ[ℝ] Matrix dIn d ℝ :=
    { toFun := fun θ => θ.E, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  exact differentiable_linear l

omit [Fintype T] in
/-- The read of block `ℓ` is a differentiable (linear) function of the parameters. -/
private theorem differentiable_read (ℓ : Fin L) :
    Differentiable ℝ (fun θ : Params A dIn dOut => θ.read ℓ) := by
  let l : Params A dIn dOut →ₗ[ℝ] Matrix d (A.r ℓ) ℝ :=
    { toFun := fun θ => θ.read ℓ, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  exact differentiable_linear l

omit [Fintype T] in
/-- The write of block `ℓ` is a differentiable (linear) function of the parameters. -/
private theorem differentiable_write (ℓ : Fin L) :
    Differentiable ℝ (fun θ : Params A dIn dOut => θ.write ℓ) := by
  let l : Params A dIn dOut →ₗ[ℝ] Matrix (A.w ℓ) d ℝ :=
    { toFun := fun θ => θ.write ℓ, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  exact differentiable_linear l

omit [Fintype T] in
/-- The readout `D` is a differentiable (linear) function of the parameters. -/
private theorem differentiable_D : Differentiable ℝ (fun θ : Params A dIn dOut => θ.D) := by
  let l : Params A dIn dOut →ₗ[ℝ] Matrix d dOut ℝ :=
    { toFun := fun θ => θ.D, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  exact differentiable_linear l

/-- The product of two differentiable matrix-valued maps is differentiable: matrix
multiplication is bilinear, hence continuous on finite-dimensional spaces. -/
private theorem differentiable_matMul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
    {f : E → Matrix m n ℝ} {g : E → Matrix n p ℝ}
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) :
    Differentiable ℝ (fun y => f y * g y) := by
  -- matrix multiplication as a bilinear map
  let B : Matrix m n ℝ →ₗ[ℝ] Matrix n p ℝ →ₗ[ℝ] Matrix m p ℝ :=
    LinearMap.mk₂ ℝ (fun a b => a * b) Matrix.add_mul (fun c a b => Matrix.smul_mul c a b)
      Matrix.mul_add (fun c a b => Matrix.mul_smul a c b)
  -- the same map with continuous linear maps (all spaces are finite-dimensional)
  let B' : Matrix m n ℝ →L[ℝ] Matrix n p ℝ →L[ℝ] Matrix m p ℝ :=
    LinearMap.toContinuousLinearMap
      ((LinearMap.toContinuousLinearMap :
        (Matrix n p ℝ →ₗ[ℝ] Matrix m p ℝ) ≃ₗ[ℝ] (Matrix n p ℝ →L[ℝ] Matrix m p ℝ)).toLinearMap ∘ₗ B)
  have hB : (fun y => f y * g y) = fun y => B' (f y) (g y) := rfl
  rw [hB]
  exact (B'.differentiable.comp hf).clm_apply hg

/-- If the maps `f_ℓ` of the blocks and the map `χ` are differentiable, the output at an input
`x` is a differentiable function of the parameters. -/
theorem differentiable_eval (hf : ∀ ℓ, Differentiable ℝ (A.f ℓ)) (hχ : Differentiable ℝ A.χ)
    (x : Matrix T dIn ℝ) :
    Differentiable ℝ (fun θ : Params A dIn dOut => eval A S θ x) := by
  -- every hidden state is a differentiable function of the parameters, by induction on `ℓ`
  have hh : ∀ ℓ : Fin (L + 1),
      Differentiable ℝ (fun θ : Params A dIn dOut => hidden A S θ x ℓ) := by
    intro ℓ
    induction ℓ using Fin.induction with
    | zero =>
      -- `h_0 = x E`
      simp only [hidden_zero]
      exact differentiable_matMul (differentiable_const x) differentiable_E
    | succ ℓ ih =>
      -- `h_{ℓ+1} = h_ℓ S_ℓ + f_ℓ (χ(h_ℓ) W_read) W_write`: products, compositions and a sum
      simp only [hidden_succ]
      exact (differentiable_matMul ih (differentiable_const (S ℓ))).add
        (differentiable_matMul ((hf ℓ).comp (differentiable_matMul (hχ.comp ih)
          (differentiable_read ℓ))) (differentiable_write ℓ))
  -- the output `χ(h_L) D`
  simp only [eval]
  exact differentiable_matMul (hχ.comp (hh (Fin.last L))) differentiable_D

variable (θ : Params A dIn dOut)

/-- The rank of the Jacobian on any batch is at most the number `P` of parameters. -/
theorem jacobianRank_le_finrank {n : ℕ} (X : Fin n → Matrix T dIn ℝ) :
    jacobianRank A S X θ ≤ Module.finrank ℝ (Params A dIn dOut) := by
  -- the range of a linear map has at most the dimension of its domain
  exact LinearMap.finrank_range_le _

omit [Fintype T] in
/-- The ranks in the definition of `funDim` form a nonempty set: the empty batch has one. -/
private theorem funDim_set_nonempty :
    {r : ℕ | ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), r = jacobianRank A S X θ}.Nonempty :=
  ⟨_, 0, fun i => i.elim0, rfl⟩

/-- The ranks in the definition of `funDim` are at most `P`. -/
private theorem funDim_set_bddAbove :
    BddAbove {r : ℕ | ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), r = jacobianRank A S X θ} := by
  refine ⟨Module.finrank ℝ (Params A dIn dOut), ?_⟩
  rintro _ ⟨n, X, rfl⟩
  exact jacobianRank_le_finrank θ X

/-- The functional dimension is attained on some finite batch. -/
theorem exists_jacobianRank_eq_funDim :
    ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), jacobianRank A S X θ = funDim A S θ := by
  -- a nonempty set of naturals that is bounded above contains its supremum
  obtain ⟨n, X, h⟩ :=
    Nat.sSup_mem (funDim_set_nonempty (S := S) θ) (funDim_set_bddAbove (S := S) θ)
  exact ⟨n, X, h.symm⟩

/-- The rank of the Jacobian on any batch is at most the functional dimension. -/
theorem jacobianRank_le_funDim {n : ℕ} (X : Fin n → Matrix T dIn ℝ) :
    jacobianRank A S X θ ≤ funDim A S θ := by
  -- a member of a set of naturals bounded above is at most its supremum
  exact le_csSup (funDim_set_bddAbove (S := S) θ) ⟨n, X, rfl⟩

omit [Fintype T] in
/-- Rank–nullity for the Jacobian on a batch: its rank and the dimension of its kernel add up
to `P`. -/
private theorem jacobianRank_add_finrank_ker {n : ℕ} (X : Fin n → Matrix T dIn ℝ) :
    jacobianRank A S X θ +
        Module.finrank ℝ (LinearMap.ker (fderiv ℝ (evalBatch A S X) θ).toLinearMap) =
      Module.finrank ℝ (Params A dIn dOut) :=
  LinearMap.finrank_range_add_finrank_ker _

/-- A direction is in the kernel of the Jacobian on a batch if and only if the derivative of the
output at every input of the batch vanishes along it. -/
private theorem mem_ker_fderiv_evalBatch_iff
    (hdiff : ∀ x : Matrix T dIn ℝ, DifferentiableAt ℝ (fun θ' : Params A dIn dOut => eval A S θ' x) θ)
    {n : ℕ} (X : Fin n → Matrix T dIn ℝ) (η : Params A dIn dOut) :
    η ∈ LinearMap.ker (fderiv ℝ (evalBatch A S X) θ).toLinearMap ↔
      ∀ i, fderiv ℝ (fun θ' => eval A S θ' (X i)) θ η = 0 := by
  -- the derivative of the outputs on the batch is the tuple of the derivatives of the outputs
  have h : fderiv ℝ (evalBatch A S X) θ =
      ContinuousLinearMap.pi fun i => fderiv ℝ (fun θ' => eval A S θ' (X i)) θ :=
    fderiv_pi fun i => hdiff (X i)
  rw [LinearMap.mem_ker]
  show fderiv ℝ (evalBatch A S X) θ η = 0 ↔ _
  rw [h]
  constructor
  · intro h0 i
    exact congr_fun h0 i
  · intro h0
    funext i
    exact h0 i

/-- Every flat direction is in the kernel of the Jacobian on every batch. -/
private theorem flat_le_ker
    (hdiff : ∀ x : Matrix T dIn ℝ, DifferentiableAt ℝ (fun θ' : Params A dIn dOut => eval A S θ' x) θ)
    {n : ℕ} (X : Fin n → Matrix T dIn ℝ) :
    flat A S θ ≤ LinearMap.ker (fderiv ℝ (evalBatch A S X) θ).toLinearMap := by
  intro η hη
  rw [flat, Submodule.mem_iInf] at hη
  rw [mem_ker_fderiv_evalBatch_iff θ hdiff]
  intro i
  have hi := hη (X i)
  rw [LinearMap.mem_ker] at hi
  exact hi

/-- Some finite batch has the kernel `K(θ)`: adding inputs can only shrink the kernel, so a
kernel of least dimension cannot shrink further and lies in the kernel at every input. -/
private theorem exists_ker_le_flat
    (hdiff : ∀ x : Matrix T dIn ℝ, DifferentiableAt ℝ (fun θ' : Params A dIn dOut => eval A S θ' x) θ) :
    ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ),
      LinearMap.ker (fderiv ℝ (evalBatch A S X) θ).toLinearMap ≤ flat A S θ := by
  -- among the kernels on finite batches, take one of least dimension
  obtain ⟨n, X, hX⟩ := Nat.sInf_mem (s := {k : ℕ | ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ),
      k = Module.finrank ℝ (LinearMap.ker (fderiv ℝ (evalBatch A S X) θ).toLinearMap)})
    ⟨_, 0, fun i => i.elim0, rfl⟩
  refine ⟨n, X, fun η hη => ?_⟩
  rw [flat, Submodule.mem_iInf]
  intro x
  -- adding the input `x` to the batch can only shrink the kernel ...
  have hle : LinearMap.ker (fderiv ℝ (evalBatch A S
        (Fin.cons x X : Fin (n + 1) → Matrix T dIn ℝ)) θ).toLinearMap ≤
      LinearMap.ker (fderiv ℝ (evalBatch A S X) θ).toLinearMap := by
    intro ξ hξ
    rw [mem_ker_fderiv_evalBatch_iff θ hdiff] at hξ ⊢
    intro i
    simpa only [Fin.cons_succ] using hξ i.succ
  -- ... and its dimension is not smaller, so the kernel stays the same
  have heq := Submodule.eq_of_le_of_finrank_le hle (by
    rw [← hX]
    exact Nat.sInf_le ⟨n + 1, Fin.cons x X, rfl⟩)
  -- hence the derivative at `x`, the input added, vanishes along `η`
  rw [← heq, mem_ker_fderiv_evalBatch_iff θ hdiff] at hη
  have h0 := hη 0
  simp only [Fin.cons_zero] at h0
  rw [LinearMap.mem_ker]
  exact h0

/-- **Appendix C, "Notation and flat directions":** the functional dimension is `P - dim K(θ)`. -/
theorem funDim_add_finrank_flat
    (hdiff : ∀ x : Matrix T dIn ℝ, DifferentiableAt ℝ (fun θ' : Params A dIn dOut => eval A S θ' x) θ) :
    funDim A S θ + Module.finrank ℝ (flat A S θ) = Module.finrank ℝ (Params A dIn dOut) := by
  -- a finite batch `X₀` whose kernel is `K(θ)`
  obtain ⟨n₀, X₀, hX₀⟩ := exists_ker_le_flat θ hdiff
  have h₀ : Module.finrank ℝ (LinearMap.ker (fderiv ℝ (evalBatch A S X₀) θ).toLinearMap) =
      Module.finrank ℝ (flat A S θ) := by
    rw [le_antisymm hX₀ (flat_le_ker θ hdiff X₀)]
  -- rank–nullity on `X₀`: its rank is `P - dim K(θ)`
  have hrn₀ := jacobianRank_add_finrank_ker (S := S) θ X₀
  -- on every batch the kernel contains `K(θ)`, so the rank is at most that on `X₀`
  have hle : funDim A S θ ≤ jacobianRank A S X₀ θ := by
    obtain ⟨n, X, hX⟩ := exists_jacobianRank_eq_funDim (S := S) θ
    have hrn := jacobianRank_add_finrank_ker (S := S) θ X
    have hmono := Submodule.finrank_mono (flat_le_ker θ hdiff X)
    omega
  have hge := jacobianRank_le_funDim (S := S) θ X₀
  omega

/-- A subspace of flat directions bounds the functional dimension from above: this is how a
count of symmetries gives an upper bound (the first step of the proof of Theorem 4.3). -/
theorem funDim_add_finrank_le_of_le_flat
    (hdiff : ∀ x : Matrix T dIn ℝ, DifferentiableAt ℝ (fun θ' : Params A dIn dOut => eval A S θ' x) θ)
    (V : Submodule ℝ (Params A dIn dOut)) (hV : V ≤ flat A S θ) :
    funDim A S θ + Module.finrank ℝ V ≤ Module.finrank ℝ (Params A dIn dOut) := by
  -- `fd(θ) + dim K(θ) = P` and `dim V ≤ dim K(θ)`
  have h := funDim_add_finrank_flat θ hdiff
  have hV' := Submodule.finrank_mono hV
  omega

/-- **A direction of a symmetry is flat** (Section 4, the paragraph after Definition 4.1). If a
curve `γ` of parameters passes through `θ` with velocity `η` and the function of the network is
the same along it, then `η` is flat at `θ`. -/
theorem mem_flat_of_hasDerivAt
    (hdiff : ∀ x : Matrix T dIn ℝ, DifferentiableAt ℝ (fun θ' : Params A dIn dOut => eval A S θ' x) θ)
    (γ : ℝ → Params A dIn dOut) (η : Params A dIn dOut) (hγ : HasDerivAt γ η 0) (hγ0 : γ 0 = θ)
    (hconst : ∀ᶠ τ in 𝓝 (0 : ℝ), ∀ x : Matrix T dIn ℝ, eval A S (γ τ) x = eval A S θ x) :
    η ∈ flat A S θ := by
  rw [flat, Submodule.mem_iInf]
  intro x
  rw [LinearMap.mem_ker]
  show fderiv ℝ (fun θ' => eval A S θ' x) θ η = 0
  -- the chain rule: `τ ↦ F_{γ(τ)}(x)` has derivative `D_θ F(x) η` at `0`
  have hl : HasFDerivAt (fun θ' => eval A S θ' x) (fderiv ℝ (fun θ' => eval A S θ' x) θ)
      (γ 0) := by
    rw [hγ0]
    exact (hdiff x).hasFDerivAt
  have h1 := hl.comp_hasDerivAt (0 : ℝ) hγ
  -- the same map is constant near `0`, so its derivative there is `0`
  have h2 : HasDerivAt ((fun θ' => eval A S θ' x) ∘ γ) 0 0 :=
    (hasDerivAt_const (0 : ℝ) (eval A S θ x)).congr_of_eventuallyEq
      (hconst.mono fun τ hτ => hτ x)
  exact h1.unique h2

/-! ### Without a hypothesis of differentiability

Mathlib's derivative of a map at a point where it is not differentiable is `0`. So an input `x` at
which `θ ↦ F_θ(x)` is not differentiable at `θ` puts no condition on `flat A S θ`, and a batch that
contains such an input has a Jacobian of rank `0`. The flat directions `K(θ)` are therefore the
directions that are flat "at every input at which the network is differentiable in `θ`", and the
functional dimension is the largest rank over the batches of such inputs. This is the convention
of the paper for ReLU, ReLU² and ReGLU blocks (Appendix C, "Notation and flat directions": "every
input" means every input at which no hidden unit sits at its kink), with a set of inputs that may
be larger. The statements of this section hold for every network, with no hypothesis. -/

/-- The directions that are flat at every input of a set `U`. -/
noncomputable def flatOn (A : Arch T d L) (S : Fin L → Matrix d d ℝ) (θ : Params A dIn dOut)
    (U : Set (Matrix T dIn ℝ)) : Submodule ℝ (Params A dIn dOut) :=
  ⨅ x ∈ U, LinearMap.ker (fderiv ℝ (fun θ' => eval A S θ' x) θ).toLinearMap

/-- A flat direction is flat at every input of `U`. -/
theorem flat_le_flatOn (U : Set (Matrix T dIn ℝ)) : flat A S θ ≤ flatOn A S θ U := by
  -- an infimum over every input lies below the infimum over the inputs of `U`
  intro η hη
  rw [flat, Submodule.mem_iInf] at hη
  rw [flatOn, Submodule.mem_iInf]
  intro x
  rw [Submodule.mem_iInf]
  intro _
  exact hη x

/-- A direction of a symmetry is flat, with no hypothesis of differentiability: if a curve of
parameters through `θ` with velocity `η` keeps the function near `τ = 0`, then `η` is flat. -/
theorem mem_flat_of_hasDerivAt'
    (γ : ℝ → Params A dIn dOut) (η : Params A dIn dOut) (hγ : HasDerivAt γ η 0) (hγ0 : γ 0 = θ)
    (hconst : ∀ᶠ τ in 𝓝 (0 : ℝ), ∀ x : Matrix T dIn ℝ, eval A S (γ τ) x = eval A S θ x) :
    η ∈ flat A S θ := by
  sorry

/-- `fd(θ) = P - dim K(θ)`, with no hypothesis of differentiability. -/
theorem funDim_add_finrank_flat' :
    funDim A S θ + Module.finrank ℝ (flat A S θ) = Module.finrank ℝ (Params A dIn dOut) := by
  sorry

/-- A subspace of flat directions bounds the functional dimension, with no hypothesis of
differentiability. -/
theorem funDim_add_finrank_le_of_le_flat' (V : Submodule ℝ (Params A dIn dOut))
    (hV : V ≤ flat A S θ) :
    funDim A S θ + Module.finrank ℝ V ≤ Module.finrank ℝ (Params A dIn dOut) := by
  sorry

/-- On a set `U` of inputs at which `θ ↦ F_θ(x)` is differentiable at `θ`, some finite batch of
inputs of `U` has a Jacobian of rank `P - dim K_U(θ)`, where `K_U(θ)` are the directions that are
flat at every input of `U`. -/
theorem exists_jacobianRank_add_finrank_flatOn (U : Set (Matrix T dIn ℝ))
    (hU : ∀ x ∈ U, DifferentiableAt ℝ (fun θ' : Params A dIn dOut => eval A S θ' x) θ) :
    ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i, X i ∈ U) ∧
      jacobianRank A S X θ + Module.finrank ℝ (flatOn A S θ U)
        = Module.finrank ℝ (Params A dIn dOut) := by
  sorry

end Skips
