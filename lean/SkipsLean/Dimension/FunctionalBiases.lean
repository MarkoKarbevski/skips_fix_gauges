import SkipsLean.Network.Biases
import SkipsLean.Dimension.GenericRank
import SkipsLean.Generic.Params
import SkipsLean.Dimension.GenericRankOn

/-!
# The functional dimension of a network with biases

Paper (skips paper), Definition 4.1 and Appendix B, "Notation and flat directions", for the
networks with biases of `Network/Biases.lean`: "With biases, `θ` also holds `b_E`, `b_read^ℓ`,
`b_write^ℓ` and `b_D`" (Lemma A.27), and `P` counts them (Theorem B.1 (i): "with biases on the
embedding, the block and the readout, counted in `P`").

Here the parameters of a network with biases are the pairs `(θ, b)` (`ParamsB A dIn dOut`), a
real normed vector space of finite dimension with its Borel σ-algebra, and the definitions and
general statements of `Dimension/Functional.lean` and `Dimension/GenericRank.lean` are repeated
for them:

* `evalBatchB`, `jacobianRankB`, `funDimB`, `flatB`: the outputs on a batch, the rank of the
  Jacobian in `(θ, b)`, Definition 4.1, and the flat directions;
* `differentiable_evalB`, `analyticOnNhd_evalB_params`: the output at an input is differentiable,
  respectively real-analytic, in `(θ, b)` when the maps of the blocks and `χ` are;
* `jacobianRankB_le_finrank`, `jacobianRankB_le_funDimB`, `exists_jacobianRankB_eq_funDimB`;
* `funDimB_add_finrank_flatB`: the functional dimension is `P` minus the dimension of the space
  of flat directions; `funDimB_add_finrank_le_of_le_flatB`: a space of flat directions bounds it;
* `mem_flatB_of_hasDerivAt`: the velocity of a curve of parameters along which the function does
  not change is flat;
* `ae_funDimB_ge`: for real-analytic blocks the functional dimension at almost every `(θ, b)` is
  at least its value at any one point.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise Topology

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [Fintype dIn] [Fintype dOut]

/-- **The parameters of a network with biases:** the pairs `(θ, b)` of the weights and the
biases. -/
abbrev ParamsB (A : Arch T d L) (dIn dOut : Type*) : Type _ :=
  Params A dIn dOut × Biases A dOut

/-- The biases carry their Borel σ-algebra. -/
noncomputable instance {A : Arch T d L} : MeasurableSpace (Biases A dOut) := borel _

instance {A : Arch T d L} : BorelSpace (Biases A dOut) := ⟨rfl⟩

variable (A : Arch T d L) (S : Fin L → Matrix d d ℝ)

/-- The outputs of the network with biases on a batch `X = (x_1, …, x_n)` of inputs. -/
def evalBatchB {n : ℕ} (X : Fin n → Matrix T dIn ℝ) (p : ParamsB A dIn dOut) :
    Fin n → Matrix T dOut ℝ :=
  fun i => evalB A S p.1 p.2 (X i)

/-- The rank of the Jacobian of `(θ, b) ↦ (F_{θ,b}(x_1), …, F_{θ,b}(x_n))` at `p = (θ, b)`. -/
noncomputable def jacobianRankB {n : ℕ} (X : Fin n → Matrix T dIn ℝ) (p : ParamsB A dIn dOut) :
    ℕ :=
  Module.finrank ℝ (LinearMap.range (fderiv ℝ (evalBatchB A S X) p).toLinearMap)

/-- **Definition 4.1 for a network with biases.** The functional dimension at `(θ, b)`: the
largest rank of the Jacobian of the outputs on a finite batch of inputs. -/
noncomputable def funDimB (p : ParamsB A dIn dOut) : ℕ :=
  sSup {r : ℕ | ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), r = jacobianRankB A S X p}

/-- The flat directions at `(θ, b)`: the directions along which the derivative of
`(θ, b) ↦ F_{θ,b}(x)` vanishes for every input `x`. -/
noncomputable def flatB (p : ParamsB A dIn dOut) : Submodule ℝ (ParamsB A dIn dOut) :=
  ⨅ x : Matrix T dIn ℝ,
    LinearMap.ker (fderiv ℝ (fun q : ParamsB A dIn dOut => evalB A S q.1 q.2 x) p).toLinearMap

variable {A S}

omit [Fintype T] in
/-- Helper: a linear map on the parameters with biases is differentiable: the space is
finite-dimensional, so the map is continuous. -/
private theorem differentiable_linear_fnb {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (l : ParamsB A dIn dOut →ₗ[ℝ] F) : Differentiable ℝ l := by
  rw [← LinearMap.coe_toContinuousLinearMap' l]
  exact (LinearMap.toContinuousLinearMap l).differentiable

omit [Fintype T] in
/-- Helper: a linear map on the parameters with biases is analytic. -/
private theorem analyticOnNhd_linear_fnb {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (l : ParamsB A dIn dOut →ₗ[ℝ] F) : AnalyticOnNhd ℝ l Set.univ := by
  rw [← LinearMap.coe_toContinuousLinearMap' l]
  exact (LinearMap.toContinuousLinearMap l).analyticOnNhd _

omit [Fintype T] [Fintype d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the product of two differentiable matrix-valued maps is differentiable: matrix
multiplication is bilinear, hence continuous on finite-dimensional spaces. -/
private theorem differentiable_matMul_fnb {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m n q : Type*} [Fintype m] [Fintype n] [Fintype q]
    {f : E → Matrix m n ℝ} {g : E → Matrix n q ℝ}
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) :
    Differentiable ℝ (fun y => f y * g y) := by
  -- matrix multiplication as a bilinear map
  let B : Matrix m n ℝ →ₗ[ℝ] Matrix n q ℝ →ₗ[ℝ] Matrix m q ℝ :=
    LinearMap.mk₂ ℝ (fun a b => a * b) Matrix.add_mul (fun c a b => Matrix.smul_mul c a b)
      Matrix.mul_add (fun c a b => Matrix.mul_smul a c b)
  -- the same map with continuous linear maps (all spaces are finite-dimensional)
  let B' : Matrix m n ℝ →L[ℝ] Matrix n q ℝ →L[ℝ] Matrix m q ℝ :=
    LinearMap.toContinuousLinearMap
      ((LinearMap.toContinuousLinearMap :
        (Matrix n q ℝ →ₗ[ℝ] Matrix m q ℝ) ≃ₗ[ℝ] (Matrix n q ℝ →L[ℝ] Matrix m q ℝ)).toLinearMap ∘ₗ B)
  have hB : (fun y => f y * g y) = fun y => B' (f y) (g y) := rfl
  rw [hB]
  exact (B'.differentiable.comp hf).clm_apply hg

omit [Fintype T] [Fintype d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the product of two analytic matrix-valued maps is analytic (matrix multiplication is a
continuous bilinear map). -/
private theorem analyticOnNhd_matMul_fnb {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m n q : Type*} [Fintype m] [Fintype n] [Fintype q]
    {f : E → Matrix m n ℝ} {g : E → Matrix n q ℝ} {s : Set E}
    (hf : AnalyticOnNhd ℝ f s) (hg : AnalyticOnNhd ℝ g s) :
    AnalyticOnNhd ℝ (fun y => f y * g y) s := by
  -- matrix multiplication as a bilinear map
  let B : Matrix m n ℝ →ₗ[ℝ] Matrix n q ℝ →ₗ[ℝ] Matrix m q ℝ :=
    LinearMap.mk₂ ℝ (fun a b => a * b) Matrix.add_mul (fun c a b => Matrix.smul_mul c a b)
      Matrix.mul_add (fun c a b => Matrix.mul_smul a c b)
  -- the same map with continuous linear maps (all spaces are finite-dimensional)
  let B' : Matrix m n ℝ →L[ℝ] Matrix n q ℝ →L[ℝ] Matrix m q ℝ :=
    LinearMap.toContinuousLinearMap
      ((LinearMap.toContinuousLinearMap :
        (Matrix n q ℝ →ₗ[ℝ] Matrix m q ℝ) ≃ₗ[ℝ] (Matrix n q ℝ →L[ℝ] Matrix m q ℝ)).toLinearMap ∘ₗ B)
  have hB : (fun y => f y * g y) = fun y => B' (f y) (g y) := rfl
  rw [hB]
  exact fun y hy => (B'.analyticAt_bilinear (f y, g y)).comp₂ (hf y hy) (hg y hy)

/-- If the maps `f_ℓ` of the blocks and the map `χ` are differentiable, the output of the network
with biases at an input `x` is a differentiable function of `(θ, b)`. -/
theorem differentiable_evalB (hf : ∀ ℓ, Differentiable ℝ (A.f ℓ)) (hχ : Differentiable ℝ A.χ)
    (x : Matrix T dIn ℝ) :
    Differentiable ℝ (fun p : ParamsB A dIn dOut => evalB A S p.1 p.2 x) := by
  -- the weights, and the matrices whose rows are the biases, are linear in `(θ, b)`
  have hE : Differentiable ℝ (fun p : ParamsB A dIn dOut => p.1.E) :=
    differentiable_linear_fnb (F := Matrix dIn d ℝ)
      { toFun := fun p => p.1.E, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hr : ∀ ℓ, Differentiable ℝ (fun p : ParamsB A dIn dOut => p.1.read ℓ) := fun ℓ =>
    differentiable_linear_fnb (F := Matrix d (A.r ℓ) ℝ)
      { toFun := fun p => p.1.read ℓ, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hw : ∀ ℓ, Differentiable ℝ (fun p : ParamsB A dIn dOut => p.1.write ℓ) := fun ℓ =>
    differentiable_linear_fnb (F := Matrix (A.w ℓ) d ℝ)
      { toFun := fun p => p.1.write ℓ, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hD : Differentiable ℝ (fun p : ParamsB A dIn dOut => p.1.D) :=
    differentiable_linear_fnb (F := Matrix d dOut ℝ)
      { toFun := fun p => p.1.D, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hbE : Differentiable ℝ (fun p : ParamsB A dIn dOut => Matrix.of fun _ : T => p.2.E) :=
    differentiable_linear_fnb (F := Matrix T d ℝ)
      { toFun := fun p => Matrix.of fun _ : T => p.2.E, map_add' := fun _ _ => rfl,
        map_smul' := fun _ _ => rfl }
  have hbr : ∀ ℓ, Differentiable ℝ
      (fun p : ParamsB A dIn dOut => Matrix.of fun _ : T => p.2.read ℓ) := fun ℓ =>
    differentiable_linear_fnb (F := Matrix T (A.r ℓ) ℝ)
      { toFun := fun p => Matrix.of fun _ : T => p.2.read ℓ, map_add' := fun _ _ => rfl,
        map_smul' := fun _ _ => rfl }
  have hbw : ∀ ℓ, Differentiable ℝ
      (fun p : ParamsB A dIn dOut => Matrix.of fun _ : T => p.2.write ℓ) := fun ℓ =>
    differentiable_linear_fnb (F := Matrix T d ℝ)
      { toFun := fun p => Matrix.of fun _ : T => p.2.write ℓ, map_add' := fun _ _ => rfl,
        map_smul' := fun _ _ => rfl }
  have hbD : Differentiable ℝ (fun p : ParamsB A dIn dOut => Matrix.of fun _ : T => p.2.D) :=
    differentiable_linear_fnb (F := Matrix T dOut ℝ)
      { toFun := fun p => Matrix.of fun _ : T => p.2.D, map_add' := fun _ _ => rfl,
        map_smul' := fun _ _ => rfl }
  -- every hidden state is a differentiable function of `(θ, b)`, by induction on `ℓ`
  have hh : ∀ ℓ : Fin (L + 1),
      Differentiable ℝ (fun p : ParamsB A dIn dOut => hiddenB A S p.1 p.2 x ℓ) := by
    intro ℓ
    induction ℓ using Fin.induction with
    | zero =>
      -- `h_0 = x E + b_E`
      simp only [hiddenB_zero]
      exact (differentiable_matMul_fnb (differentiable_const x) hE).add hbE
    | succ ℓ ih =>
      -- `h_{ℓ+1} = h_ℓ S_ℓ + f_ℓ (χ(h_ℓ) W_read + b_read) W_write + b_write`
      simp only [hiddenB_succ]
      exact (differentiable_matMul_fnb ih (differentiable_const (S ℓ))).add
        ((differentiable_matMul_fnb ((hf ℓ).comp ((differentiable_matMul_fnb (hχ.comp ih)
          (hr ℓ)).add (hbr ℓ))) (hw ℓ)).add (hbw ℓ))
  -- the output `χ(h_L) D + b_D`
  simp only [evalB]
  exact (differentiable_matMul_fnb (hχ.comp (hh (Fin.last L))) hD).add hbD

/-- The output of a network with biases with real-analytic maps `f_ℓ` and `χ` at a fixed input
is a real-analytic function of `(θ, b)`, for all stream matrices. -/
theorem analyticOnNhd_evalB_params (A : Arch T d L) (S : Fin L → Matrix d d ℝ)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (hχ : AnalyticOnNhd ℝ A.χ Set.univ)
    (x : Matrix T dIn ℝ) :
    AnalyticOnNhd ℝ (fun p : ParamsB A dIn dOut => evalB A S p.1 p.2 x) Set.univ := by
  -- the weights, and the matrices whose rows are the biases, are linear in `(θ, b)`
  have hE : AnalyticOnNhd ℝ (fun p : ParamsB A dIn dOut => p.1.E) Set.univ :=
    analyticOnNhd_linear_fnb (F := Matrix dIn d ℝ)
      { toFun := fun p => p.1.E, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hr : ∀ ℓ, AnalyticOnNhd ℝ (fun p : ParamsB A dIn dOut => p.1.read ℓ) Set.univ := fun ℓ =>
    analyticOnNhd_linear_fnb (F := Matrix d (A.r ℓ) ℝ)
      { toFun := fun p => p.1.read ℓ, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hw : ∀ ℓ, AnalyticOnNhd ℝ (fun p : ParamsB A dIn dOut => p.1.write ℓ) Set.univ :=
    fun ℓ => analyticOnNhd_linear_fnb (F := Matrix (A.w ℓ) d ℝ)
      { toFun := fun p => p.1.write ℓ, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hD : AnalyticOnNhd ℝ (fun p : ParamsB A dIn dOut => p.1.D) Set.univ :=
    analyticOnNhd_linear_fnb (F := Matrix d dOut ℝ)
      { toFun := fun p => p.1.D, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hbE : AnalyticOnNhd ℝ
      (fun p : ParamsB A dIn dOut => Matrix.of fun _ : T => p.2.E) Set.univ :=
    analyticOnNhd_linear_fnb (F := Matrix T d ℝ)
      { toFun := fun p => Matrix.of fun _ : T => p.2.E, map_add' := fun _ _ => rfl,
        map_smul' := fun _ _ => rfl }
  have hbr : ∀ ℓ, AnalyticOnNhd ℝ
      (fun p : ParamsB A dIn dOut => Matrix.of fun _ : T => p.2.read ℓ) Set.univ := fun ℓ =>
    analyticOnNhd_linear_fnb (F := Matrix T (A.r ℓ) ℝ)
      { toFun := fun p => Matrix.of fun _ : T => p.2.read ℓ, map_add' := fun _ _ => rfl,
        map_smul' := fun _ _ => rfl }
  have hbw : ∀ ℓ, AnalyticOnNhd ℝ
      (fun p : ParamsB A dIn dOut => Matrix.of fun _ : T => p.2.write ℓ) Set.univ := fun ℓ =>
    analyticOnNhd_linear_fnb (F := Matrix T d ℝ)
      { toFun := fun p => Matrix.of fun _ : T => p.2.write ℓ, map_add' := fun _ _ => rfl,
        map_smul' := fun _ _ => rfl }
  have hbD : AnalyticOnNhd ℝ
      (fun p : ParamsB A dIn dOut => Matrix.of fun _ : T => p.2.D) Set.univ :=
    analyticOnNhd_linear_fnb (F := Matrix T dOut ℝ)
      { toFun := fun p => Matrix.of fun _ : T => p.2.D, map_add' := fun _ _ => rfl,
        map_smul' := fun _ _ => rfl }
  -- every hidden state is an analytic function of `(θ, b)`, by induction on `ℓ`
  have hh : ∀ ℓ : Fin (L + 1),
      AnalyticOnNhd ℝ (fun p : ParamsB A dIn dOut => hiddenB A S p.1 p.2 x ℓ) Set.univ := by
    intro ℓ
    induction ℓ using Fin.induction with
    | zero =>
      -- `h_0 = x E + b_E`
      simp only [hiddenB_zero]
      exact (analyticOnNhd_matMul_fnb analyticOnNhd_const hE).add hbE
    | succ ℓ ih =>
      -- `h_{ℓ+1} = h_ℓ S_ℓ + f_ℓ (χ(h_ℓ) W_read + b_read) W_write + b_write`
      simp only [hiddenB_succ]
      exact (analyticOnNhd_matMul_fnb ih analyticOnNhd_const).add
        ((analyticOnNhd_matMul_fnb ((hf ℓ).comp ((analyticOnNhd_matMul_fnb
          (hχ.comp ih (Set.mapsTo_univ _ _)) (hr ℓ)).add (hbr ℓ)) (Set.mapsTo_univ _ _))
          (hw ℓ)).add (hbw ℓ))
  -- the output `χ(h_L) D + b_D`
  simp only [evalB]
  exact (analyticOnNhd_matMul_fnb (hχ.comp (hh (Fin.last L)) (Set.mapsTo_univ _ _)) hD).add hbD

variable (p : ParamsB A dIn dOut)

/-- The rank of the Jacobian on any batch is at most the number `P` of parameters, biases
included. -/
theorem jacobianRankB_le_finrank {n : ℕ} (X : Fin n → Matrix T dIn ℝ) :
    jacobianRankB A S X p ≤ Module.finrank ℝ (ParamsB A dIn dOut) := by
  -- the range of a linear map has at most the dimension of its domain
  exact LinearMap.finrank_range_le _

omit [Fintype T] in
/-- Helper: the ranks in the definition of `funDimB` form a nonempty set: the empty batch has
one. -/
private theorem funDimB_set_nonempty_fnb :
    {r : ℕ | ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), r = jacobianRankB A S X p}.Nonempty :=
  ⟨_, 0, fun i => i.elim0, rfl⟩

/-- Helper: the ranks in the definition of `funDimB` are at most `P`. -/
private theorem funDimB_set_bddAbove_fnb :
    BddAbove {r : ℕ | ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), r = jacobianRankB A S X p} := by
  refine ⟨Module.finrank ℝ (ParamsB A dIn dOut), ?_⟩
  rintro _ ⟨n, X, rfl⟩
  exact jacobianRankB_le_finrank p X

/-- The functional dimension of a network with biases is attained on some finite batch. -/
theorem exists_jacobianRankB_eq_funDimB :
    ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), jacobianRankB A S X p = funDimB A S p := by
  -- a nonempty set of naturals that is bounded above contains its supremum
  obtain ⟨n, X, h⟩ :=
    Nat.sSup_mem (funDimB_set_nonempty_fnb (S := S) p) (funDimB_set_bddAbove_fnb (S := S) p)
  exact ⟨n, X, h.symm⟩

/-- The rank of the Jacobian on any batch is at most the functional dimension. -/
theorem jacobianRankB_le_funDimB {n : ℕ} (X : Fin n → Matrix T dIn ℝ) :
    jacobianRankB A S X p ≤ funDimB A S p := by
  -- a member of a set of naturals bounded above is at most its supremum
  exact le_csSup (funDimB_set_bddAbove_fnb (S := S) p) ⟨n, X, rfl⟩

omit [Fintype T] in
/-- Helper: rank–nullity for the Jacobian on a batch: its rank and the dimension of its kernel
add up to `P`. -/
private theorem jacobianRankB_add_finrank_ker_fnb {n : ℕ} (X : Fin n → Matrix T dIn ℝ) :
    jacobianRankB A S X p +
        Module.finrank ℝ (LinearMap.ker (fderiv ℝ (evalBatchB A S X) p).toLinearMap) =
      Module.finrank ℝ (ParamsB A dIn dOut) :=
  LinearMap.finrank_range_add_finrank_ker _

/-- Helper: a direction is in the kernel of the Jacobian on a batch if and only if the derivative
of the output at every input of the batch vanishes along it. -/
private theorem mem_ker_fderiv_evalBatchB_iff_fnb
    (hdiff : ∀ x : Matrix T dIn ℝ,
      DifferentiableAt ℝ (fun q : ParamsB A dIn dOut => evalB A S q.1 q.2 x) p)
    {n : ℕ} (X : Fin n → Matrix T dIn ℝ) (η : ParamsB A dIn dOut) :
    η ∈ LinearMap.ker (fderiv ℝ (evalBatchB A S X) p).toLinearMap ↔
      ∀ i, fderiv ℝ (fun q : ParamsB A dIn dOut => evalB A S q.1 q.2 (X i)) p η = 0 := by
  -- the derivative of the outputs on the batch is the tuple of the derivatives of the outputs
  have h : fderiv ℝ (evalBatchB A S X) p =
      ContinuousLinearMap.pi fun i =>
        fderiv ℝ (fun q : ParamsB A dIn dOut => evalB A S q.1 q.2 (X i)) p :=
    fderiv_pi fun i => hdiff (X i)
  rw [LinearMap.mem_ker]
  show fderiv ℝ (evalBatchB A S X) p η = 0 ↔ _
  rw [h]
  constructor
  · intro h0 i
    exact congr_fun h0 i
  · intro h0
    funext i
    exact h0 i

/-- Helper: every flat direction is in the kernel of the Jacobian on every batch. -/
private theorem flatB_le_ker_fnb
    (hdiff : ∀ x : Matrix T dIn ℝ,
      DifferentiableAt ℝ (fun q : ParamsB A dIn dOut => evalB A S q.1 q.2 x) p)
    {n : ℕ} (X : Fin n → Matrix T dIn ℝ) :
    flatB A S p ≤ LinearMap.ker (fderiv ℝ (evalBatchB A S X) p).toLinearMap := by
  intro η hη
  rw [flatB, Submodule.mem_iInf] at hη
  rw [mem_ker_fderiv_evalBatchB_iff_fnb p hdiff]
  intro i
  have hi := hη (X i)
  rw [LinearMap.mem_ker] at hi
  exact hi

/-- Helper: some finite batch has the kernel `K(θ, b)`: adding inputs can only shrink the
kernel, so a kernel of least dimension cannot shrink further and lies in the kernel at every
input. -/
private theorem exists_ker_le_flatB_fnb
    (hdiff : ∀ x : Matrix T dIn ℝ,
      DifferentiableAt ℝ (fun q : ParamsB A dIn dOut => evalB A S q.1 q.2 x) p) :
    ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ),
      LinearMap.ker (fderiv ℝ (evalBatchB A S X) p).toLinearMap ≤ flatB A S p := by
  -- among the kernels on finite batches, take one of least dimension
  obtain ⟨n, X, hX⟩ := Nat.sInf_mem (s := {k : ℕ | ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ),
      k = Module.finrank ℝ (LinearMap.ker (fderiv ℝ (evalBatchB A S X) p).toLinearMap)})
    ⟨_, 0, fun i => i.elim0, rfl⟩
  refine ⟨n, X, fun η hη => ?_⟩
  rw [flatB, Submodule.mem_iInf]
  intro x
  -- adding the input `x` to the batch can only shrink the kernel ...
  have hle : LinearMap.ker (fderiv ℝ (evalBatchB A S
        (Fin.cons x X : Fin (n + 1) → Matrix T dIn ℝ)) p).toLinearMap ≤
      LinearMap.ker (fderiv ℝ (evalBatchB A S X) p).toLinearMap := by
    intro ξ hξ
    rw [mem_ker_fderiv_evalBatchB_iff_fnb p hdiff] at hξ ⊢
    intro i
    simpa only [Fin.cons_succ] using hξ i.succ
  -- ... and its dimension is not smaller, so the kernel stays the same
  have heq := Submodule.eq_of_le_of_finrank_le hle (by
    rw [← hX]
    exact Nat.sInf_le ⟨n + 1, Fin.cons x X, rfl⟩)
  -- hence the derivative at `x`, the input added, vanishes along `η`
  rw [← heq, mem_ker_fderiv_evalBatchB_iff_fnb p hdiff] at hη
  have h0 := hη 0
  simp only [Fin.cons_zero] at h0
  rw [LinearMap.mem_ker]
  exact h0

/-- **Appendix B, "Notation and flat directions", with biases:** the functional dimension is
`P − dim K(θ, b)`. -/
theorem funDimB_add_finrank_flatB
    (hdiff : ∀ x : Matrix T dIn ℝ,
      DifferentiableAt ℝ (fun q : ParamsB A dIn dOut => evalB A S q.1 q.2 x) p) :
    funDimB A S p + Module.finrank ℝ (flatB A S p) = Module.finrank ℝ (ParamsB A dIn dOut) := by
  -- a finite batch `X₀` whose kernel is `K(θ, b)`
  obtain ⟨n₀, X₀, hX₀⟩ := exists_ker_le_flatB_fnb p hdiff
  have h₀ : Module.finrank ℝ (LinearMap.ker (fderiv ℝ (evalBatchB A S X₀) p).toLinearMap) =
      Module.finrank ℝ (flatB A S p) := by
    rw [le_antisymm hX₀ (flatB_le_ker_fnb p hdiff X₀)]
  -- rank–nullity on `X₀`: its rank is `P - dim K(θ, b)`
  have hrn₀ := jacobianRankB_add_finrank_ker_fnb (S := S) p X₀
  -- on every batch the kernel contains `K(θ, b)`, so the rank is at most that on `X₀`
  have hle : funDimB A S p ≤ jacobianRankB A S X₀ p := by
    obtain ⟨n, X, hX⟩ := exists_jacobianRankB_eq_funDimB (S := S) p
    have hrn := jacobianRankB_add_finrank_ker_fnb (S := S) p X
    have hmono := Submodule.finrank_mono (flatB_le_ker_fnb p hdiff X)
    omega
  have hge := jacobianRankB_le_funDimB (S := S) p X₀
  omega

/-- A subspace of flat directions bounds the functional dimension of a network with biases from
above. -/
theorem funDimB_add_finrank_le_of_le_flatB
    (hdiff : ∀ x : Matrix T dIn ℝ,
      DifferentiableAt ℝ (fun q : ParamsB A dIn dOut => evalB A S q.1 q.2 x) p)
    (V : Submodule ℝ (ParamsB A dIn dOut)) (hV : V ≤ flatB A S p) :
    funDimB A S p + Module.finrank ℝ V ≤ Module.finrank ℝ (ParamsB A dIn dOut) := by
  -- `fd(θ, b) + dim K(θ, b) = P` and `dim V ≤ dim K(θ, b)`
  have h := funDimB_add_finrank_flatB p hdiff
  have hV' := Submodule.finrank_mono hV
  omega

/-- **A direction of a symmetry is flat, with biases.** If a curve `γ` of parameters passes
through `(θ, b)` with velocity `η` and the function of the network is the same along it, then `η`
is flat at `(θ, b)`. -/
theorem mem_flatB_of_hasDerivAt
    (hdiff : ∀ x : Matrix T dIn ℝ,
      DifferentiableAt ℝ (fun q : ParamsB A dIn dOut => evalB A S q.1 q.2 x) p)
    (γ : ℝ → ParamsB A dIn dOut) (η : ParamsB A dIn dOut) (hγ : HasDerivAt γ η 0)
    (hγ0 : γ 0 = p)
    (hconst : ∀ᶠ τ in 𝓝 (0 : ℝ), ∀ x : Matrix T dIn ℝ,
      evalB A S (γ τ).1 (γ τ).2 x = evalB A S p.1 p.2 x) :
    η ∈ flatB A S p := by
  rw [flatB, Submodule.mem_iInf]
  intro x
  rw [LinearMap.mem_ker]
  show fderiv ℝ (fun q : ParamsB A dIn dOut => evalB A S q.1 q.2 x) p η = 0
  -- the chain rule: `τ ↦ F_{γ(τ)}(x)` has derivative `D F(x) η` at `0`
  have hl : HasFDerivAt (fun q : ParamsB A dIn dOut => evalB A S q.1 q.2 x)
      (fderiv ℝ (fun q : ParamsB A dIn dOut => evalB A S q.1 q.2 x) p) (γ 0) := by
    rw [hγ0]
    exact (hdiff x).hasFDerivAt
  have h1 := hl.comp_hasDerivAt (0 : ℝ) hγ
  -- the same map is constant near `0`, so its derivative there is `0`
  have h2 : HasDerivAt ((fun q : ParamsB A dIn dOut => evalB A S q.1 q.2 x) ∘ γ) 0 0 :=
    (hasDerivAt_const (0 : ℝ) (evalB A S p.1 p.2 x)).congr_of_eventuallyEq
      (hconst.mono fun τ hτ => hτ x)
  exact h1.unique h2

/-- **The functional dimension of a network with biases is, at almost every `(θ, b)`, at least
its value at any one point,** for real-analytic maps `f_ℓ` and `χ` and any stream matrices. -/
theorem ae_funDimB_ge (A : Arch T d L) (S : Fin L → Matrix d d ℝ)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (hχ : AnalyticOnNhd ℝ A.χ Set.univ)
    (μ : Measure (ParamsB A dIn dOut)) [μ.IsAddHaarMeasure] (p₀ : ParamsB A dIn dOut) :
    ∀ᵐ p ∂μ, funDimB A S p₀ ≤ funDimB A S p := by
  -- a batch `X` on which the rank at `p₀` is `fd(p₀)`
  obtain ⟨n, X, hX⟩ := exists_jacobianRankB_eq_funDimB (S := S) p₀
  rw [← hX]
  -- the outputs on the batch are analytic in `(θ, b)`
  have hB : AnalyticOnNhd ℝ
      (evalBatchB A S X : ParamsB A dIn dOut → Fin n → Matrix T dOut ℝ) Set.univ :=
    AnalyticOnNhd.pi fun i => analyticOnNhd_evalB_params A S hf hχ (X i)
  -- so the rank on `X` at almost every `p` is at least that at `p₀`, and at most `fd(p)`
  have h := ae_finrank_range_fderiv_ge_of_isPreconnected μ isOpen_univ isPreconnected_univ
    (by rw [Set.compl_univ]; exact measure_empty) hB (Set.mem_univ p₀)
  filter_upwards [h] with p hp
  exact hp.trans (jacobianRankB_le_funDimB (S := S) p X)

end Skips
