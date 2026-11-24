import SkipsLean.Dimension.GenericRank
import SkipsLean.Symmetry.InsideBlocks
import SkipsLean.Symmetry.Normalized

/-!
# The functional dimension of a network with learned skips

Paper (skips paper): Theorem 4.6 (ii): "Under RMSNorm, the residual network satisfies the equality
condition, and the skip raises the functional dimension by at least `d_model (d_model − 1)/2`. A
learned skip raises it by exactly `d_model (d_model + 1)/2` more than an identity skip." Appendix B:
with one block the network under pre-RMSNorm is
`x ↦ N_ε(x E A + f(N_ε(x E) W_read) W_write) D`, "with the identity skip `A = I`. A learned skip
`A ∈ ℝ^{d_model × d_model}` is full or upper triangular." Theorem B.1 (iii): "Let the network be
pre-RMSNorm without biases, with a learned skip `A`, full or upper triangular. For generic
parameters and `ε > 0`, its functional dimension exceeds that of the residual network of part (ii)
by exactly `d_model (d_model + 1)/2`, and it satisfies the equality condition."

In `eval A S θ x` the stream matrices `S` are the skips (`Residual/LearnedSkips.lean`). Here they
become parameters: the skips are `ι v` for a continuous linear map `ι` from a space `V` (all
matrices: `ι` the identity, `funDimLearned`; another choice of `V` gives a restricted family, as
the upper triangular skips), the parameters are the pairs `(θ, v)`, and `funDimSkips` is the
functional dimension of this family (Definition 4.1 for it).

The statements of this file and of `OneBlock/LearnedSkipZero.lean`, `OneBlock/LearnedSkipBound.lean`
are the general steps; the values for the kinds of block are in `OneBlock/LearnedSkipKinds.lean`.
The route differs from Part (iii) of the paper's proof of Theorem B.1 (which runs Steps 1 to 5 of
its part (ii) again): for one block,
- the orthogonal changes of basis at `h_0` and at `h_1`, with `A ↦ G_0⁻¹ A G_1`, and the symmetries
  inside the block bound the functional dimension by `P + d² − d (d − 1) − s`
  (`funDimLearned_add_le_rmsNorm`, `OneBlock/LearnedSkipBound.lean`; the paper: "The directions
  `η^rot` […] For a full `A` they have dimension `d_model (d_model − 1)`");
- at the skip `A = 0` the family has the functional dimension of the skipless network plus the
  dimension of `V` (`funDim_add_finrank_le_funDimSkips_zero`, `OneBlock/LearnedSkipZero.lean`): a
  flat direction `(η, a)` there has `a = 0`, because along the inputs `t x`, `t → ∞`, the input of
  the block stays bounded while the skip term grows like `t`, the derivative of `N_ε` is injective
  for `ε > 0`, and `E`, `D` have rank `d`;
- at generic parameters the functional dimension is the largest (`ae_funDimSkips_ge`).
So where the skipless network attains `P − d (d − 1) − s` (tanh, GELU, SwiGLU, GeGLU blocks of width
at least `d`), the network with a full learned skip has `P + d² − d (d − 1) − s`.
-/

namespace Skips

open Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- **The function of the network whose skips are parameters:** the parameters are `(θ, v)`, the
skips are `ι v`, and the function is that of the weights `θ` with the stream matrices `ι v`. -/
def evalSkips (A : Arch T d L) (ι : V →L[ℝ] (Fin L → Matrix d d ℝ))
    (p : Params A dIn dOut × V) (x : Matrix T dIn ℝ) : Matrix T dOut ℝ :=
  eval A (ι p.2) p.1 x

/-- The rank of the Jacobian of `(θ, v) ↦ (F_{θ,v}(x_1), …, F_{θ,v}(x_n))` at `p`. -/
noncomputable def jacobianRankSkips (A : Arch T d L) (ι : V →L[ℝ] (Fin L → Matrix d d ℝ))
    {n : ℕ} (X : Fin n → Matrix T dIn ℝ) (p : Params A dIn dOut × V) : ℕ :=
  Module.finrank ℝ (LinearMap.range (fderiv ℝ
    (fun p' : Params A dIn dOut × V => fun i : Fin n => evalSkips A ι p' (X i)) p).toLinearMap)

/-- **Definition 4.1 for the network whose skips are parameters:** the largest rank of the
Jacobian of the outputs on a finite batch of inputs, in the weights and the skips. -/
noncomputable def funDimSkips (A : Arch T d L) (ι : V →L[ℝ] (Fin L → Matrix d d ℝ))
    (p : Params A dIn dOut × V) : ℕ :=
  sSup {r : ℕ | ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), r = jacobianRankSkips A ι X p}

/-- The flat directions of the network whose skips are parameters: the directions `(η, a)` along
which the derivative of `(θ, v) ↦ F_{θ,v}(x)` vanishes for every input `x`. -/
noncomputable def flatSkips (A : Arch T d L) (ι : V →L[ℝ] (Fin L → Matrix d d ℝ))
    (p : Params A dIn dOut × V) : Submodule ℝ (Params A dIn dOut × V) :=
  ⨅ x : Matrix T dIn ℝ,
    LinearMap.ker (fderiv ℝ (fun p' : Params A dIn dOut × V => evalSkips A ι p' x) p).toLinearMap

/-- **The functional dimension of the network with full learned skips** `A_1, …, A_L` (all
`d × d` matrices), at the weights and skips `p = (θ, (A_ℓ))`. -/
noncomputable abbrev funDimLearned (A : Arch T d L)
    (p : Params A dIn dOut × (Fin L → Matrix d d ℝ)) : ℕ :=
  funDimSkips A (ContinuousLinearMap.id ℝ (Fin L → Matrix d d ℝ)) p

/-! ### The outputs as functions of the weights and the skips -/

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the product of two differentiable matrix-valued maps is differentiable (a copy of the
private `differentiable_matMul` of `Dimension/Functional.lean`). -/
private theorem differentiable_matMul_lsg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
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

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the product of two analytic matrix-valued maps is analytic (a copy of the private
`analyticOnNhd_matMul` of `Dimension/GenericRank.lean`). -/
private theorem analyticOnNhd_matMul_lsg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
    {f : E → Matrix m n ℝ} {g : E → Matrix n p ℝ} {s : Set E}
    (hf : AnalyticOnNhd ℝ f s) (hg : AnalyticOnNhd ℝ g s) :
    AnalyticOnNhd ℝ (fun y => f y * g y) s := by
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
  exact fun y hy => (B'.analyticAt_bilinear (f y, g y)).comp₂ (hf y hy) (hg y hy)

omit [Fintype T] [DecidableEq d] in
/-- Helper: a linear function of the weights `θ`, as a continuous linear map of `(θ, v)` (the
space of weights is finite-dimensional). -/
private noncomputable def fstLin_lsg {A : Arch T d L} {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (l : Params A dIn dOut →ₗ[ℝ] F) : Params A dIn dOut × V →L[ℝ] F :=
  (LinearMap.toContinuousLinearMap l).comp (ContinuousLinearMap.fst ℝ (Params A dIn dOut) V)

/-- Helper: the skip of block `ℓ`, `(θ, v) ↦ (ι v)_ℓ`, as a continuous linear map. -/
private noncomputable def skipLin_lsg (A : Arch T d L) (ι : V →L[ℝ] (Fin L → Matrix d d ℝ))
    (ℓ : Fin L) : Params A dIn dOut × V →L[ℝ] Matrix d d ℝ :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin L => Matrix d d ℝ) ℓ).comp
    (ι.comp (ContinuousLinearMap.snd ℝ (Params A dIn dOut) V))

omit [DecidableEq d] in
/-- **The output is differentiable in the weights and the skips jointly:** for differentiable
maps `f_ℓ` and `χ`, the map `(θ, v) ↦ F_{θ, ι v}(x)` is differentiable. -/
private theorem differentiable_evalSkips_lsg (A : Arch T d L)
    (ι : V →L[ℝ] (Fin L → Matrix d d ℝ)) (hf : ∀ ℓ, Differentiable ℝ (A.f ℓ))
    (hχ : Differentiable ℝ A.χ) (x : Matrix T dIn ℝ) :
    Differentiable ℝ (fun p : Params A dIn dOut × V => evalSkips A ι p x) := by
  -- the weights and the skips are continuous linear functions of `(θ, v)`
  have hE : Differentiable ℝ (fun p : Params A dIn dOut × V => p.1.E) :=
    (fstLin_lsg (V := V) (F := Matrix dIn d ℝ)
      { toFun := fun θ : Params A dIn dOut => θ.E, map_add' := fun _ _ => rfl,
        map_smul' := fun _ _ => rfl }).differentiable
  have hr : ∀ ℓ, Differentiable ℝ (fun p : Params A dIn dOut × V => p.1.read ℓ) := fun ℓ =>
    (fstLin_lsg (V := V) (F := Matrix d (A.r ℓ) ℝ)
      { toFun := fun θ : Params A dIn dOut => θ.read ℓ, map_add' := fun _ _ => rfl,
        map_smul' := fun _ _ => rfl }).differentiable
  have hw : ∀ ℓ, Differentiable ℝ (fun p : Params A dIn dOut × V => p.1.write ℓ) := fun ℓ =>
    (fstLin_lsg (V := V) (F := Matrix (A.w ℓ) d ℝ)
      { toFun := fun θ : Params A dIn dOut => θ.write ℓ, map_add' := fun _ _ => rfl,
        map_smul' := fun _ _ => rfl }).differentiable
  have hD : Differentiable ℝ (fun p : Params A dIn dOut × V => p.1.D) :=
    (fstLin_lsg (V := V) (F := Matrix d dOut ℝ)
      { toFun := fun θ : Params A dIn dOut => θ.D, map_add' := fun _ _ => rfl,
        map_smul' := fun _ _ => rfl }).differentiable
  have hS : ∀ ℓ, Differentiable ℝ (fun p : Params A dIn dOut × V => ι p.2 ℓ) := fun ℓ =>
    (skipLin_lsg (dIn := dIn) (dOut := dOut) A ι ℓ).differentiable
  -- every hidden state is differentiable in `(θ, v)`, by induction on `ℓ`
  have hh : ∀ ℓ : Fin (L + 1), Differentiable ℝ
      (fun p : Params A dIn dOut × V => hidden A (ι p.2) p.1 x ℓ) := by
    intro ℓ
    induction ℓ using Fin.induction with
    | zero =>
      -- `h_0 = x E`
      simp only [hidden_zero]
      exact differentiable_matMul_lsg (differentiable_const x) hE
    | succ ℓ ih =>
      -- `h_{ℓ+1} = h_ℓ (ι v)_ℓ + f_ℓ (χ(h_ℓ) W_read) W_write`
      simp only [hidden_succ]
      exact (differentiable_matMul_lsg ih (hS ℓ)).add
        (differentiable_matMul_lsg ((hf ℓ).comp (differentiable_matMul_lsg (hχ.comp ih)
          (hr ℓ))) (hw ℓ))
  -- the output `χ(h_L) D`
  simp only [evalSkips, eval]
  exact differentiable_matMul_lsg (hχ.comp (hh (Fin.last L))) hD

omit [DecidableEq d] in
/-- **The output is analytic in the weights and the skips jointly:** for real-analytic maps `f_ℓ`
and `χ`, the map `(θ, v) ↦ F_{θ, ι v}(x)` is real-analytic. -/
private theorem analyticOnNhd_evalSkips_lsg (A : Arch T d L)
    (ι : V →L[ℝ] (Fin L → Matrix d d ℝ)) (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ)
    (hχ : AnalyticOnNhd ℝ A.χ Set.univ) (x : Matrix T dIn ℝ) :
    AnalyticOnNhd ℝ (fun p : Params A dIn dOut × V => evalSkips A ι p x) Set.univ := by
  -- the weights and the skips are continuous linear functions of `(θ, v)`
  have hE : AnalyticOnNhd ℝ (fun p : Params A dIn dOut × V => p.1.E) Set.univ :=
    (fstLin_lsg (V := V) (F := Matrix dIn d ℝ)
      { toFun := fun θ : Params A dIn dOut => θ.E, map_add' := fun _ _ => rfl,
        map_smul' := fun _ _ => rfl }).analyticOnNhd _
  have hr : ∀ ℓ, AnalyticOnNhd ℝ (fun p : Params A dIn dOut × V => p.1.read ℓ) Set.univ :=
    fun ℓ => (fstLin_lsg (V := V) (F := Matrix d (A.r ℓ) ℝ)
      { toFun := fun θ : Params A dIn dOut => θ.read ℓ, map_add' := fun _ _ => rfl,
        map_smul' := fun _ _ => rfl }).analyticOnNhd _
  have hw : ∀ ℓ, AnalyticOnNhd ℝ (fun p : Params A dIn dOut × V => p.1.write ℓ) Set.univ :=
    fun ℓ => (fstLin_lsg (V := V) (F := Matrix (A.w ℓ) d ℝ)
      { toFun := fun θ : Params A dIn dOut => θ.write ℓ, map_add' := fun _ _ => rfl,
        map_smul' := fun _ _ => rfl }).analyticOnNhd _
  have hD : AnalyticOnNhd ℝ (fun p : Params A dIn dOut × V => p.1.D) Set.univ :=
    (fstLin_lsg (V := V) (F := Matrix d dOut ℝ)
      { toFun := fun θ : Params A dIn dOut => θ.D, map_add' := fun _ _ => rfl,
        map_smul' := fun _ _ => rfl }).analyticOnNhd _
  have hS : ∀ ℓ, AnalyticOnNhd ℝ (fun p : Params A dIn dOut × V => ι p.2 ℓ) Set.univ :=
    fun ℓ => (skipLin_lsg (dIn := dIn) (dOut := dOut) A ι ℓ).analyticOnNhd _
  -- every hidden state is analytic in `(θ, v)`, by induction on `ℓ`
  have hh : ∀ ℓ : Fin (L + 1), AnalyticOnNhd ℝ
      (fun p : Params A dIn dOut × V => hidden A (ι p.2) p.1 x ℓ) Set.univ := by
    intro ℓ
    induction ℓ using Fin.induction with
    | zero =>
      -- `h_0 = x E`
      simp only [hidden_zero]
      exact analyticOnNhd_matMul_lsg analyticOnNhd_const hE
    | succ ℓ ih =>
      -- `h_{ℓ+1} = h_ℓ (ι v)_ℓ + f_ℓ (χ(h_ℓ) W_read) W_write`
      simp only [hidden_succ]
      exact (analyticOnNhd_matMul_lsg ih (hS ℓ)).add
        (analyticOnNhd_matMul_lsg ((hf ℓ).comp (analyticOnNhd_matMul_lsg
          (hχ.comp ih (Set.mapsTo_univ _ _)) (hr ℓ)) (Set.mapsTo_univ _ _)) (hw ℓ))
  -- the output `χ(h_L) D`
  simp only [evalSkips, eval]
  exact analyticOnNhd_matMul_lsg (hχ.comp (hh (Fin.last L)) (Set.mapsTo_univ _ _)) hD

/-! ### The supremum in `funDimSkips` -/

omit [Fintype T] [DecidableEq d] in
/-- Helper: under a bound on the ranks, the functional dimension is attained on a batch. -/
private theorem exists_jacobianRankSkips_eq_lsg (A : Arch T d L)
    (ι : V →L[ℝ] (Fin L → Matrix d d ℝ)) (p : Params A dIn dOut × V) (N : ℕ)
    (hN : ∀ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), jacobianRankSkips A ι X p ≤ N) :
    ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), jacobianRankSkips A ι X p = funDimSkips A ι p := by
  -- a nonempty set of naturals bounded above contains its supremum
  obtain ⟨n, X, h⟩ := Nat.sSup_mem (s := {r : ℕ | ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ),
      r = jacobianRankSkips A ι X p}) ⟨_, 0, fun i => i.elim0, rfl⟩
    ⟨N, by rintro _ ⟨n, X, rfl⟩; exact hN n X⟩
  exact ⟨n, X, h.symm⟩

omit [Fintype T] [DecidableEq d] in
/-- Helper: under a bound on the ranks, every rank is at most the functional dimension. -/
private theorem jacobianRankSkips_le_funDimSkips_lsg (A : Arch T d L)
    (ι : V →L[ℝ] (Fin L → Matrix d d ℝ)) (p : Params A dIn dOut × V) (N : ℕ)
    (hN : ∀ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), jacobianRankSkips A ι X p ≤ N)
    {n : ℕ} (X : Fin n → Matrix T dIn ℝ) :
    jacobianRankSkips A ι X p ≤ funDimSkips A ι p :=
  le_csSup ⟨N, by rintro _ ⟨n, X, rfl⟩; exact hN n X⟩ ⟨n, X, rfl⟩

omit [Fintype T] [DecidableEq d] in
/-- Helper: for a finite-dimensional `V` the ranks are at most the number of parameters. -/
private theorem jacobianRankSkips_le_finrank_lsg [FiniteDimensional ℝ V] (A : Arch T d L)
    (ι : V →L[ℝ] (Fin L → Matrix d d ℝ)) (p : Params A dIn dOut × V)
    (n : ℕ) (X : Fin n → Matrix T dIn ℝ) :
    jacobianRankSkips A ι X p ≤ Module.finrank ℝ (Params A dIn dOut × V) :=
  -- the range of a linear map has at most the dimension of its domain
  LinearMap.finrank_range_le _

/-! ### The flat directions -/

omit [DecidableEq d] in
/-- Helper: a direction is in the kernel of the Jacobian on a batch if and only if the derivative
of the output at every input of the batch vanishes along it. -/
private theorem mem_ker_lsg (A : Arch T d L) (ι : V →L[ℝ] (Fin L → Matrix d d ℝ))
    (p : Params A dIn dOut × V)
    (hdiff : ∀ x : Matrix T dIn ℝ,
      DifferentiableAt ℝ (fun p' : Params A dIn dOut × V => evalSkips A ι p' x) p)
    {n : ℕ} (X : Fin n → Matrix T dIn ℝ) (η : Params A dIn dOut × V) :
    η ∈ LinearMap.ker (fderiv ℝ (fun p' : Params A dIn dOut × V => fun i : Fin n =>
        evalSkips A ι p' (X i)) p).toLinearMap ↔
      ∀ i, fderiv ℝ (fun p' => evalSkips A ι p' (X i)) p η = 0 := by
  -- the derivative of the outputs on the batch is the tuple of the derivatives of the outputs
  have h : fderiv ℝ (fun p' : Params A dIn dOut × V => fun i : Fin n =>
        evalSkips A ι p' (X i)) p =
      ContinuousLinearMap.pi fun i => fderiv ℝ (fun p' => evalSkips A ι p' (X i)) p :=
    fderiv_pi fun i => hdiff (X i)
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
/-- Helper: every flat direction is in the kernel of the Jacobian on every batch. -/
private theorem flatSkips_le_ker_lsg (A : Arch T d L) (ι : V →L[ℝ] (Fin L → Matrix d d ℝ))
    (p : Params A dIn dOut × V)
    (hdiff : ∀ x : Matrix T dIn ℝ,
      DifferentiableAt ℝ (fun p' : Params A dIn dOut × V => evalSkips A ι p' x) p)
    {n : ℕ} (X : Fin n → Matrix T dIn ℝ) :
    flatSkips A ι p ≤ LinearMap.ker (fderiv ℝ (fun p' : Params A dIn dOut × V =>
      fun i : Fin n => evalSkips A ι p' (X i)) p).toLinearMap := by
  intro η hη
  rw [flatSkips, Submodule.mem_iInf] at hη
  rw [mem_ker_lsg A ι p hdiff]
  intro i
  have hi := hη (X i)
  rw [LinearMap.mem_ker] at hi
  exact hi

omit [DecidableEq d] in
/-- Helper: some finite batch has the kernel `flatSkips`: adding inputs can only shrink the
kernel, so a kernel of least dimension lies in the kernel at every input. -/
private theorem exists_ker_le_flatSkips_lsg [FiniteDimensional ℝ V] (A : Arch T d L)
    (ι : V →L[ℝ] (Fin L → Matrix d d ℝ)) (p : Params A dIn dOut × V)
    (hdiff : ∀ x : Matrix T dIn ℝ,
      DifferentiableAt ℝ (fun p' : Params A dIn dOut × V => evalSkips A ι p' x) p) :
    ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ),
      LinearMap.ker (fderiv ℝ (fun p' : Params A dIn dOut × V =>
        fun i : Fin n => evalSkips A ι p' (X i)) p).toLinearMap ≤ flatSkips A ι p := by
  -- among the kernels on finite batches, take one of least dimension
  obtain ⟨n, X, hX⟩ := Nat.sInf_mem (s := {k : ℕ | ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ),
      k = Module.finrank ℝ (LinearMap.ker (fderiv ℝ (fun p' : Params A dIn dOut × V =>
        fun i : Fin n => evalSkips A ι p' (X i)) p).toLinearMap)})
    ⟨_, 0, fun i => i.elim0, rfl⟩
  refine ⟨n, X, fun η hη => ?_⟩
  rw [flatSkips, Submodule.mem_iInf]
  intro x
  -- adding the input `x` to the batch can only shrink the kernel ...
  have hle : LinearMap.ker (fderiv ℝ (fun p' : Params A dIn dOut × V =>
        fun i : Fin (n + 1) => evalSkips A ι p' ((Fin.cons x X : Fin (n + 1) → _) i))
          p).toLinearMap ≤
      LinearMap.ker (fderiv ℝ (fun p' : Params A dIn dOut × V =>
        fun i : Fin n => evalSkips A ι p' (X i)) p).toLinearMap := by
    intro ξ hξ
    rw [mem_ker_lsg A ι p hdiff] at hξ ⊢
    intro i
    simpa only [Fin.cons_succ] using hξ i.succ
  -- ... and its dimension is not smaller, so the kernel stays the same
  have heq := Submodule.eq_of_le_of_finrank_le hle (by
    rw [← hX]
    exact Nat.sInf_le ⟨n + 1, Fin.cons x X, rfl⟩)
  -- hence the derivative at `x`, the input added, vanishes along `η`
  rw [← heq, mem_ker_lsg A ι p hdiff] at hη
  have h0 := hη 0
  simp only [Fin.cons_zero] at h0
  rw [LinearMap.mem_ker]
  exact h0

/-- For differentiable blocks, the functional dimension and the dimension of the flat directions
add up to the number of parameters (weights and skips). -/
theorem funDimSkips_add_finrank_flatSkips [FiniteDimensional ℝ V] (A : Arch T d L)
    (ι : V →L[ℝ] (Fin L → Matrix d d ℝ)) (hf : ∀ ℓ, Differentiable ℝ (A.f ℓ))
    (hχ : Differentiable ℝ A.χ) (p : Params A dIn dOut × V) :
    funDimSkips A ι p + Module.finrank ℝ (flatSkips A ι p)
      = Module.finrank ℝ (Params A dIn dOut × V) := by
  -- the output at every input is differentiable at `p`
  have hdiff : ∀ x : Matrix T dIn ℝ,
      DifferentiableAt ℝ (fun p' : Params A dIn dOut × V => evalSkips A ι p' x) p :=
    fun x => differentiable_evalSkips_lsg A ι hf hχ x p
  have hN := jacobianRankSkips_le_finrank_lsg A ι p
  -- a finite batch `X₀` whose kernel is the space of flat directions
  obtain ⟨n₀, X₀, hX₀⟩ := exists_ker_le_flatSkips_lsg A ι p hdiff
  have h₀ := le_antisymm hX₀ (flatSkips_le_ker_lsg A ι p hdiff X₀)
  -- rank–nullity on `X₀`: its rank is `P - dim K(p)`
  have hrn₀ := LinearMap.finrank_range_add_finrank_ker (fderiv ℝ (fun p' : Params A dIn dOut × V =>
    fun i : Fin n₀ => evalSkips A ι p' (X₀ i)) p).toLinearMap
  rw [h₀] at hrn₀
  -- on every batch the kernel contains `K(p)`, so the rank is at most that on `X₀`
  obtain ⟨n, X, hX⟩ := exists_jacobianRankSkips_eq_lsg A ι p _ hN
  have hrn := LinearMap.finrank_range_add_finrank_ker (fderiv ℝ (fun p' : Params A dIn dOut × V =>
    fun i : Fin n => evalSkips A ι p' (X i)) p).toLinearMap
  have hmono := Submodule.finrank_mono (flatSkips_le_ker_lsg A ι p hdiff X)
  have hge := jacobianRankSkips_le_funDimSkips_lsg A ι p _ hN X₀
  unfold jacobianRankSkips at hX hge
  omega

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (copied from `Dimension/GenericRank.lean`, where it is private): let `x ↦ J x`
be an analytic family of linear maps between finite-dimensional spaces,
and `N` a fixed linear map. If `J x₀ ∘ N` is injective, then `J x ∘ N` is injective at almost every
`x`. With a left inverse `K` of `J x₀ ∘ N`, the determinant of `K ∘ J x ∘ N` is analytic in `x`
and equal to `1` at `x₀`, so it vanishes only on a null set. -/
private theorem ae_injective_comp_of_analytic_lsg
    {X E E' F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [μ.IsAddHaarMeasure]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [AddCommGroup E']
    [Module ℝ E'] [FiniteDimensional ℝ E'] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F]
    {J : X → E →L[ℝ] F} (hJ : AnalyticOnNhd ℝ J Set.univ) (N : E' →ₗ[ℝ] E) {x₀ : X}
    (h₀ : Function.Injective ((J x₀ : E →ₗ[ℝ] F) ∘ₗ N)) :
    ∀ᵐ x ∂μ, Function.Injective ((J x : E →ₗ[ℝ] F) ∘ₗ N) := by
  -- a left inverse `K` of `J x₀ ∘ N`
  obtain ⟨K, hK⟩ :=
    ((J x₀ : E →ₗ[ℝ] F) ∘ₗ N).exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 h₀)
  -- the matrix of `K ∘ J x ∘ N` in a basis `b` of `E'`, a linear function of `J x`
  let b := Module.finBasis ℝ E'
  let Ψ : (E →L[ℝ] F) →ₗ[ℝ]
      Matrix (Fin (Module.finrank ℝ E')) (Fin (Module.finrank ℝ E')) ℝ :=
    (LinearMap.toMatrix b b).toLinearMap ∘ₗ (LinearMap.llcomp ℝ E' F E' K) ∘ₗ
      (LinearMap.lcomp ℝ F N) ∘ₗ (ContinuousLinearMap.coeLM ℝ)
  have hΨ : ∀ x, Ψ (J x) = LinearMap.toMatrix b b (K ∘ₗ ((J x : E →ₗ[ℝ] F) ∘ₗ N)) :=
    fun x => rfl
  -- its determinant `φ x` is an analytic function of `x`: a polynomial in the entries
  let φ : X → ℝ := fun x => (Ψ (J x)).det
  have hentry : ∀ i j, AnalyticOnNhd ℝ (fun x => Ψ (J x) i j) Set.univ := fun i j =>
    ((LinearMap.toContinuousLinearMap ((Matrix.entryLinearMap ℝ ℝ i j) ∘ₗ Ψ)).analyticOnNhd
      _).comp hJ (Set.mapsTo_univ _ _)
  have hφ : AnalyticOnNhd ℝ φ Set.univ := by
    show AnalyticOnNhd ℝ (fun x => (Ψ (J x)).det) Set.univ
    simp only [Matrix.det_apply']
    exact Finset.analyticOnNhd_fun_sum _ fun σ _ => analyticOnNhd_const.mul
      (Finset.analyticOnNhd_fun_prod _ fun i _ => hentry (σ i) i)
  -- `φ x₀ = det 1 = 1`
  have hφ₀ : φ x₀ = 1 := by
    show (Ψ (J x₀)).det = 1
    rw [hΨ, hK, LinearMap.toMatrix_id, Matrix.det_one]
  -- so `φ x ≠ 0` for almost every `x`
  have hnull := measure_zeroSet_of_analytic μ hφ ⟨x₀, by rw [hφ₀]; exact one_ne_zero⟩
  have hae : ∀ᵐ x ∂μ, φ x ≠ 0 := by
    rw [ae_iff]
    simpa only [ne_eq, not_not] using hnull
  -- where `φ x ≠ 0`, `K ∘ J x ∘ N` is invertible, so `J x ∘ N` is injective
  refine hae.mono fun x hx => ?_
  have hdet : LinearMap.det (K ∘ₗ ((J x : E →ₗ[ℝ] F) ∘ₗ N)) ≠ 0 := by
    rw [← LinearMap.det_toMatrix b]
    exact hx
  have hbij := (Module.End.isUnit_iff _).1
    ((LinearMap.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hdet))
  have hinj := hbij.1
  rw [LinearMap.coe_comp] at hinj
  exact hinj.of_comp

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (copied from `Dimension/GenericRank.lean`, where it is private): for an analytic family
`x ↦ J x` of linear maps between finite-dimensional spaces, the
rank of `J x` is at least the rank of `J x₀` for almost every `x`. On a complement `C` of the
kernel of `J x₀`, the map `J x₀` is injective and `C` has the dimension of its range; the
restrictions of `J x` to `C` form an analytic family, injective at almost every `x`. -/
private theorem ae_finrank_range_ge_lsg
    {X F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [μ.IsAddHaarMeasure]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {J : X → X →L[ℝ] F} (hJ : AnalyticOnNhd ℝ J Set.univ) (x₀ : X) :
    ∀ᵐ x ∂μ, Module.finrank ℝ (LinearMap.range (J x₀).toLinearMap) ≤
      Module.finrank ℝ (LinearMap.range (J x).toLinearMap) := by
  -- a complement `C` of the kernel of `J x₀`: its dimension is the rank of `J x₀`
  obtain ⟨C, hC⟩ := (LinearMap.ker (J x₀).toLinearMap).exists_isCompl
  have hdimC : Module.finrank ℝ C = Module.finrank ℝ (LinearMap.range (J x₀).toLinearMap) := by
    have h1 := Submodule.finrank_add_eq_of_isCompl hC
    have h2 := LinearMap.finrank_range_add_finrank_ker (J x₀).toLinearMap
    omega
  -- the restriction `J x₀ ∘ ι_C` is injective
  have hinj₀ : Function.Injective ((J x₀ : X →ₗ[ℝ] F) ∘ₗ C.subtype) := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro v hv
    have hv' : (v : X) ∈ LinearMap.ker (J x₀).toLinearMap := hv
    exact Subtype.ext (Submodule.disjoint_def.1 hC.disjoint _ hv' v.2)
  -- where `J x ∘ ι_C` is injective, the range of `J x` contains a copy of `C`
  refine (ae_injective_comp_of_analytic_lsg μ hJ C.subtype hinj₀).mono fun x hx => ?_
  rw [← hdimC, ← LinearMap.finrank_range_of_inj hx]
  exact Submodule.finrank_mono (LinearMap.range_comp_le_range _ _)

/-- **The generic functional dimension is the largest,** for real-analytic blocks: at almost
every `(θ, v)` the functional dimension is at least that at any one `p₀`. -/
theorem ae_funDimSkips_ge [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (A : Arch T d L) (ι : V →L[ℝ] (Fin L → Matrix d d ℝ))
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (hχ : AnalyticOnNhd ℝ A.χ Set.univ)
    (μ : Measure (Params A dIn dOut × V)) [μ.IsAddHaarMeasure] (p₀ : Params A dIn dOut × V) :
    ∀ᵐ p ∂μ, funDimSkips A ι p₀ ≤ funDimSkips A ι p := by
  -- a batch `X` on which the rank at `p₀` is the functional dimension at `p₀`
  obtain ⟨n, X, hX⟩ :=
    exists_jacobianRankSkips_eq_lsg A ι p₀ _ (jacobianRankSkips_le_finrank_lsg A ι p₀)
  rw [← hX]
  -- the outputs on the batch, and hence their derivative, are analytic in `(θ, v)`
  have hB : AnalyticOnNhd ℝ (fun p : Params A dIn dOut × V => fun i : Fin n =>
      evalSkips A ι p (X i)) Set.univ :=
    AnalyticOnNhd.pi fun i => analyticOnNhd_evalSkips_lsg A ι hf hχ (X i)
  -- at generic `p` the rank on `X` is at least that at `p₀`, and at most the functional dimension
  have hBorel : BorelSpace (Params A dIn dOut × V) := Prod.borelSpace
  filter_upwards [ae_finrank_range_ge_lsg μ hB.fderiv p₀] with p hp
  exact hp.trans (jacobianRankSkips_le_funDimSkips_lsg A ι p _
    (jacobianRankSkips_le_finrank_lsg A ι p) X)

omit [DecidableEq d] in
/-- Helper: the Jacobian of the restricted family on a batch is that of the larger family
composed with `(θ, v') ↦ (θ, j v')`, so its rank is not larger (the chain rule). -/
private theorem jacobianRankSkips_comp_le_lsg {V' : Type*} [NormedAddCommGroup V']
    [NormedSpace ℝ V'] (A : Arch T d L) (ι : V →L[ℝ] (Fin L → Matrix d d ℝ)) (j : V' →L[ℝ] V)
    (hf : ∀ ℓ, Differentiable ℝ (A.f ℓ)) (hχ : Differentiable ℝ A.χ)
    {n : ℕ} (X : Fin n → Matrix T dIn ℝ) (θ : Params A dIn dOut) (v' : V') :
    jacobianRankSkips A (ι.comp j) X (θ, v') ≤ jacobianRankSkips A ι X (θ, j v') := by
  -- the map `(θ, v') ↦ (θ, j v')`
  let m : Params A dIn dOut × V' →L[ℝ] Params A dIn dOut × V :=
    (ContinuousLinearMap.id ℝ (Params A dIn dOut)).prodMap j
  -- the outputs of the larger family on the batch: differentiable
  let G : Params A dIn dOut × V → Fin n → Matrix T dOut ℝ :=
    fun p => fun i => evalSkips A ι p (X i)
  have hG : Differentiable ℝ G :=
    differentiable_pi.2 fun i => differentiable_evalSkips_lsg A ι hf hχ (X i)
  -- the restricted family is the larger one composed with `m`
  have hcomp : (fun p' : Params A dIn dOut × V' => fun i : Fin n =>
      evalSkips A (ι.comp j) p' (X i)) = G ∘ m := rfl
  have hd : fderiv ℝ (G ∘ m) (θ, v') = (fderiv ℝ G (θ, j v')).comp m := by
    rw [fderiv_comp _ (hG _) m.differentiableAt, m.fderiv]
    rfl
  -- the range of a composition lies in the range of the outer map
  unfold jacobianRankSkips
  rw [hcomp, hd]
  exact Submodule.finrank_mono (LinearMap.range_comp_le_range _ _)

omit [DecidableEq d] in
/-- Helper: the ranks are bounded, also for an infinite-dimensional `V`: through the chain rule,
by the number of weights and of entries of the skips. -/
private theorem jacobianRankSkips_le_lsg (A : Arch T d L) (ι : V →L[ℝ] (Fin L → Matrix d d ℝ))
    (hf : ∀ ℓ, Differentiable ℝ (A.f ℓ)) (hχ : Differentiable ℝ A.χ)
    (p : Params A dIn dOut × V) (n : ℕ) (X : Fin n → Matrix T dIn ℝ) :
    jacobianRankSkips A ι X p ≤
      Module.finrank ℝ (Params A dIn dOut × (Fin L → Matrix d d ℝ)) := by
  -- the family is that of all skips composed with `ι`
  have h := jacobianRankSkips_comp_le_lsg A (ContinuousLinearMap.id ℝ _) ι hf hχ X p.1 p.2
  -- `id ∘ ι` and `ι` give the same outputs, so the same Jacobian (by definition)
  have h' : jacobianRankSkips A ι X p ≤
      jacobianRankSkips A (ContinuousLinearMap.id ℝ _) X (p.1, ι p.2) := h
  exact h'.trans (LinearMap.finrank_range_le _)

/-- A restricted family of skips has at most the functional dimension of the family it is
restricted from: for `j : V' → V` linear, the family with the skips `ι (j v')` has at `(θ, v')` at
most the functional dimension of the family with the skips `ι v` at `(θ, j v')`. -/
theorem funDimSkips_comp_le {V' : Type*} [NormedAddCommGroup V'] [NormedSpace ℝ V']
    (A : Arch T d L) (ι : V →L[ℝ] (Fin L → Matrix d d ℝ)) (j : V' →L[ℝ] V)
    (hf : ∀ ℓ, Differentiable ℝ (A.f ℓ)) (hχ : Differentiable ℝ A.χ)
    (θ : Params A dIn dOut) (v' : V') :
    funDimSkips A (ι.comp j) (θ, v') ≤ funDimSkips A ι (θ, j v') := by
  -- a batch on which the restricted family attains its functional dimension
  obtain ⟨n, X, hX⟩ := exists_jacobianRankSkips_eq_lsg A (ι.comp j) (θ, v') _
    (jacobianRankSkips_le_lsg A (ι.comp j) hf hχ (θ, v'))
  rw [← hX]
  -- its rank there is at most the rank of the larger family, at most its functional dimension
  exact (jacobianRankSkips_comp_le_lsg A ι j hf hχ X θ v').trans
    (jacobianRankSkips_le_funDimSkips_lsg A ι (θ, j v') _
      (jacobianRankSkips_le_lsg A ι hf hχ (θ, j v')) X)

end Skips
