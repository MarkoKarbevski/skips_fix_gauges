import SkipsLean.Residual.SmallParameter
import SkipsLean.Dimension.GenericRank

/-!
# Residual networks with small writes

Paper (skips paper): Lemma A.27 (Small writes) and its proof, for blocks without normalization
and without biases. For parameters `θ` and a number `τ`, the parameters `θ_τ` hold `τ W_write^ℓ` in
place of every write. At `θ_τ` every hidden state is `x E + O(τ)`, and the output is

  `y = x E D + τ ∑_ℓ f_ℓ(x E W_read^ℓ) W_write^ℓ D + O(τ²)`.

With `J_τ` the Jacobian of the outputs at `θ_τ` and `S_τ` the map that divides the coordinates of
the reads by `τ`, the limit `J_0 = lim_{τ → 0} J_τ S_τ` is, at one input `x`,

  `(J_0 η)(x) = x (η_E D + E η_D)
      + ∑_ℓ (D f_ℓ(x E W_read^ℓ)(x E η_read^ℓ) W_write^ℓ + f_ℓ(x E W_read^ℓ) η_write^ℓ) D`,

the formula of the paper with `ψ_M = η_E D + E η_D`, `ψ_C = E η_read` and `ψ_A = η_write D`,
written for arbitrary differentiable maps `f_ℓ`. A direction `η` is flat for `J_0` if
`(J_0 η)(x) = 0` for every input `x`. The last paragraph of the proof ("The rank") gives: if the
flat directions of `J_0` form a space of dimension `m`, then `fd(θ_τ) ≥ P - m` for all small
`τ ≠ 0`.

Here the limit is taken as in `Residual/SmallParameter.lean`: with `G τ θ` the outputs at `θ_τ` on
a batch, `G 0 θ = (x E D)_x` does not depend on the reads and the writes, and `∂_τ G(0, θ)` is the
sum over the blocks above. That the same `τ` multiplies the directions of the writes as well does
not change the rank for `τ ≠ 0`.
-/

namespace Skips

open Matrix Filter Topology
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]

/-- **The parameters `θ_τ` of Lemma A.27:** the embedding, the reads and the readout of `θ`, and
the writes `τ W_write^ℓ`. -/
def Params.smallWrites {A : Arch T d L} (θ : Params A dIn dOut) (τ : ℝ) : Params A dIn dOut where
  E := θ.E
  read := θ.read
  write ℓ := τ • θ.write ℓ
  D := θ.D

/-- **The limit `J_0` of the proof of Lemma A.27, at one input `x`,** without normalization and
without biases: `(J_0 η)(x) = x (η_E D + E η_D) + ∑_ℓ (D f_ℓ(x E W_read^ℓ)(x E η_read^ℓ) W_write^ℓ
+ f_ℓ(x E W_read^ℓ) η_write^ℓ) D`. -/
noncomputable def smallWritesLimit (A : Arch T d L) (θ η : Params A dIn dOut)
    (x : Matrix T dIn ℝ) : Matrix T dOut ℝ :=
  x * (η.E * θ.D + θ.E * η.D)
    + ∑ ℓ, (fderiv ℝ (A.f ℓ) (x * θ.E * θ.read ℓ) (x * θ.E * η.read ℓ) * θ.write ℓ
        + A.f ℓ (x * θ.E * θ.read ℓ) * η.write ℓ) * θ.D

variable (A : Arch T d L) (θ : Params A dIn dOut)

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the embedding of `θ_τ` is that of `θ`. -/
@[simp] private theorem smallWrites_E (τ : ℝ) : (θ.smallWrites τ).E = θ.E := rfl

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the reads of `θ_τ` are those of `θ`. -/
@[simp] private theorem smallWrites_read (τ : ℝ) (ℓ : Fin L) :
    (θ.smallWrites τ).read ℓ = θ.read ℓ := rfl

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the writes of `θ_τ` are `τ W_write^ℓ`. -/
@[simp] private theorem smallWrites_write (τ : ℝ) (ℓ : Fin L) :
    (θ.smallWrites τ).write ℓ = τ • θ.write ℓ := rfl

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the readout of `θ_τ` is that of `θ`. -/
@[simp] private theorem smallWrites_D (τ : ℝ) : (θ.smallWrites τ).D = θ.D := rfl

omit [Fintype T] [Fintype dOut] in
/-- Helper: the residual step at `θ_τ` without normalization,
`h_{k+1} = h_k + τ (f_k(h_k W_read^k) W_write^k)`. -/
private theorem hidden_smallWrites_succ (hA : A.χ = id) (x : Matrix T dIn ℝ) (τ : ℝ) (k : Fin L) :
    hidden A 1 (θ.smallWrites τ) x k.succ = hidden A 1 (θ.smallWrites τ) x k.castSucc
      + τ • (A.f k (hidden A 1 (θ.smallWrites τ) x k.castSucc * θ.read k) * θ.write k) := by
  rw [hidden_succ, hA, Pi.one_apply, Matrix.mul_one, id_eq, smallWrites_read, smallWrites_write,
    Matrix.mul_smul]

omit [Fintype T] [Fintype dOut] in
/-- Helper: at `τ = 0` every hidden state is `x E`. -/
private theorem hidden_smallWrites_zero (hA : A.χ = id) (x : Matrix T dIn ℝ) (k : Fin (L + 1)) :
    hidden A 1 (θ.smallWrites 0) x k = x * θ.E := by
  induction k using Fin.induction with
  | zero => rw [hidden_zero, smallWrites_E]
  | succ k ih => rw [hidden_smallWrites_succ A θ hA, ih, zero_smul, add_zero]

/-- At `τ = 0` the residual network without normalization computes `x ↦ x E D`
(proof of Lemma A.27: "`y = x E D + τ (…) + O(τ²)`"). -/
theorem eval_smallWrites_zero (hA : A.χ = id) (x : Matrix T dIn ℝ) :
    eval A 1 (θ.smallWrites 0) x = x * θ.E * θ.D := by
  rw [eval, hidden_smallWrites_zero A θ hA, hA, id_eq, smallWrites_D]

/-- Helper: the derivative at `0` of `τ ↦ τ g(τ)`, for `g` continuous at `0`, is `g(0)`. -/
private theorem hasDerivAt_smul_self_SW {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g : ℝ → F} (hg : ContinuousAt g 0) : HasDerivAt (fun τ : ℝ => τ • g τ) (g 0) 0 := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  refine Tendsto.congr' ?_ (hg.tendsto.mono_left nhdsWithin_le_nhds)
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [zero_add, zero_smul, sub_zero, smul_smul, inv_mul_cancel₀ ht, one_smul]

/-- Helper: a sum over the blocks before `k + 1` is the sum over the blocks before `k` plus the
term of block `k`. -/
private theorem sum_ite_lt_succ_SW {M : Type*} [AddCommMonoid M] {m : ℕ} (a : Fin m → M)
    (k : Fin m) :
    (∑ ℓ : Fin m, if (ℓ : ℕ) < (k : ℕ) + 1 then a ℓ else 0)
      = (∑ ℓ : Fin m, if (ℓ : ℕ) < (k : ℕ) then a ℓ else 0) + a k := by
  have h : ∀ ℓ : Fin m, (if (ℓ : ℕ) < (k : ℕ) + 1 then a ℓ else 0)
      = (if (ℓ : ℕ) < (k : ℕ) then a ℓ else 0) + (if ℓ = k then a ℓ else 0) := by
    intro ℓ
    by_cases h1 : (ℓ : ℕ) < k
    · have h2 : ℓ ≠ k := fun h => by rw [h] at h1; exact lt_irrefl _ h1
      have h3 : (ℓ : ℕ) < k + 1 := by omega
      simp only [h1, h2, h3, ite_true, ite_false, add_zero]
    · by_cases h2 : ℓ = k
      · subst h2
        simp
      · have h3 : ¬ (ℓ : ℕ) < k + 1 := fun h => h2 (Fin.ext (by omega))
        simp only [h1, h2, h3, ite_false, add_zero]
  rw [Finset.sum_congr rfl fun ℓ _ => h ℓ, Finset.sum_add_distrib]
  simp

omit [Fintype T] [Fintype dOut] in
/-- Helper: every hidden state at `θ_τ` is continuous in `τ`. -/
private theorem continuous_hidden_smallWrites (hA : A.χ = id) (hf : ∀ ℓ, Continuous (A.f ℓ))
    (x : Matrix T dIn ℝ) (k : Fin (L + 1)) :
    Continuous (fun τ : ℝ => hidden A 1 (θ.smallWrites τ) x k) := by
  induction k using Fin.induction with
  | zero =>
    simp only [hidden_zero, smallWrites_E]
    exact continuous_const
  | succ k ih =>
    simp only [hidden_smallWrites_succ A θ hA]
    exact ih.add (continuous_id.smul
      (((hf k).comp (ih.matrix_mul continuous_const)).matrix_mul continuous_const))

omit [Fintype dOut] in
/-- Helper: the derivative at `τ = 0` of the hidden state `h_k` at `θ_τ` is the sum over the
blocks `ℓ < k` of `f_ℓ(x E W_read^ℓ) W_write^ℓ`. -/
private theorem hasDerivAt_hidden_smallWrites (hA : A.χ = id) (hf : ∀ ℓ, Continuous (A.f ℓ))
    (x : Matrix T dIn ℝ) (k : Fin (L + 1)) :
    HasDerivAt (fun τ : ℝ => hidden A 1 (θ.smallWrites τ) x k)
      (∑ ℓ : Fin L, if (ℓ : ℕ) < (k : ℕ) then A.f ℓ (x * θ.E * θ.read ℓ) * θ.write ℓ else 0)
      0 := by
  induction k using Fin.induction with
  | zero =>
    -- `h_0 = x E` does not depend on `τ`
    simp only [hidden_zero, smallWrites_E, Fin.val_zero, Nat.not_lt_zero, ite_false,
      Finset.sum_const_zero]
    exact hasDerivAt_const _ _
  | succ k ih =>
    -- `h_{k+1}(τ) = h_k(τ) + τ g(τ)`, and the derivative of `τ g(τ)` at `0` is `g(0)`
    simp only [hidden_smallWrites_succ A θ hA]
    have hg : ContinuousAt (fun τ : ℝ =>
        A.f k (hidden A 1 (θ.smallWrites τ) x k.castSucc * θ.read k) * θ.write k) 0 :=
      (((hf k).comp ((continuous_hidden_smallWrites A θ hA hf x k.castSucc).matrix_mul
        continuous_const)).matrix_mul continuous_const).continuousAt
    have h2 := ih.add (hasDerivAt_smul_self_SW hg)
    -- `g(0)` is the term of block `k` at `h_k(0) = x E`
    have hv : (∑ ℓ : Fin L, if (ℓ : ℕ) < (k.castSucc : ℕ)
          then A.f ℓ (x * θ.E * θ.read ℓ) * θ.write ℓ else 0)
        + A.f k (hidden A 1 (θ.smallWrites 0) x k.castSucc * θ.read k) * θ.write k
        = ∑ ℓ : Fin L, if (ℓ : ℕ) < (k.succ : ℕ)
          then A.f ℓ (x * θ.E * θ.read ℓ) * θ.write ℓ else 0 := by
      rw [hidden_smallWrites_zero A θ hA, Fin.val_succ, Fin.val_castSucc]
      exact (sum_ite_lt_succ_SW (fun ℓ => A.f ℓ (x * θ.E * θ.read ℓ) * θ.write ℓ) k).symm
    rw [hv] at h2
    exact h2

/-- Helper: `y ↦ y M`, as a linear map. -/
private def mulRightLinSW {m n p : Type*} [Fintype n] (M : Matrix n p ℝ) :
    Matrix m n ℝ →ₗ[ℝ] Matrix m p ℝ where
  toFun X := X * M
  map_add' X Y := Matrix.add_mul X Y M
  map_smul' c X := Matrix.smul_mul c X M

/-- Helper: `y ↦ y M`, as a continuous linear map. -/
private noncomputable def mulRightCLMSW {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
    (M : Matrix n p ℝ) : Matrix m n ℝ →L[ℝ] Matrix m p ℝ :=
  LinearMap.toContinuousLinearMap (mulRightLinSW M)

/-- **The term of order `τ` of the output at `θ_τ`** (proof of Lemma A.27, the expansion of `y`):
the derivative of `τ ↦ F_{θ_τ}(x)` at `τ = 0` is `∑_ℓ f_ℓ(x E W_read^ℓ) W_write^ℓ D`. -/
theorem hasDerivAt_eval_smallWrites (hA : A.χ = id) (hf : ∀ ℓ, Differentiable ℝ (A.f ℓ))
    (x : Matrix T dIn ℝ) :
    HasDerivAt (fun τ : ℝ => eval A 1 (θ.smallWrites τ) x)
      ((∑ ℓ, A.f ℓ (x * θ.E * θ.read ℓ) * θ.write ℓ) * θ.D) 0 := by
  -- the derivative of the last hidden state: every block is before `L`
  have hL := hasDerivAt_hidden_smallWrites A θ hA (fun ℓ => (hf ℓ).continuous) x (Fin.last L)
  have hsum : (∑ ℓ : Fin L, if (ℓ : ℕ) < ((Fin.last L : Fin (L + 1)) : ℕ)
      then A.f ℓ (x * θ.E * θ.read ℓ) * θ.write ℓ else 0)
        = ∑ ℓ, A.f ℓ (x * θ.E * θ.read ℓ) * θ.write ℓ :=
    Finset.sum_congr rfl fun ℓ _ => by simp [ℓ.isLt]
  rw [hsum] at hL
  -- the output is `h_L D`, and `y ↦ y D` is linear
  have hc := (mulRightCLMSW (m := T) θ.D).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hL
  simp only [eval, hA, id_eq, smallWrites_D]
  exact hc

/-! ### Helpers for the rank: derivatives in the parameters -/

/-- Helper: matrix multiplication as a continuous bilinear map. -/
private noncomputable def mulBSW (m n p : Type*) [Fintype m] [Fintype n] [Fintype p] :
    Matrix m n ℝ →L[ℝ] Matrix n p ℝ →L[ℝ] Matrix m p ℝ :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap :
      (Matrix n p ℝ →ₗ[ℝ] Matrix m p ℝ) ≃ₗ[ℝ] (Matrix n p ℝ →L[ℝ] Matrix m p ℝ)).toLinearMap ∘ₗ
      LinearMap.mk₂ ℝ (fun a b => a * b) Matrix.add_mul (fun c a b => Matrix.smul_mul c a b)
        Matrix.mul_add (fun c a b => Matrix.mul_smul a c b))

/-- Helper: the product rule for matrix-valued maps, with the value of the derivative,
`(f g)' v = f' v g + f g' v`. -/
private theorem hasFDerivAt_mul_SW {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m n p : Type*} [Fintype m] [Fintype n] [Fintype p] {f : E → Matrix m n ℝ}
    {g : E → Matrix n p ℝ} {f' : E →L[ℝ] Matrix m n ℝ} {g' : E →L[ℝ] Matrix n p ℝ} {y : E}
    (hf : HasFDerivAt f f' y) (hg : HasFDerivAt g g' y) :
    ∃ h' : E →L[ℝ] Matrix m p ℝ, HasFDerivAt (fun z => f z * g z) h' y ∧
      ∀ v, h' v = f' v * g y + f y * g' v := by
  -- the derivative of the bilinear map `(a, b) ↦ a b` along `(f, g)`
  have h := (mulBSW m n p).hasFDerivAt_of_bilinear hf hg
  refine ⟨_, h, fun v => ?_⟩
  show f y * g' v + f' v * g y = _
  exact add_comm _ _

/-- Helper: the embedding, as a continuous linear map of the parameters. -/
private noncomputable def clmE_SW : Params A dIn dOut →L[ℝ] Matrix dIn d ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun θ' => θ'.E, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }

/-- Helper: the read of block `ℓ`, as a continuous linear map of the parameters. -/
private noncomputable def clmRead_SW (ℓ : Fin L) : Params A dIn dOut →L[ℝ] Matrix d (A.r ℓ) ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun θ' => θ'.read ℓ, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }

/-- Helper: the write of block `ℓ`, as a continuous linear map of the parameters. -/
private noncomputable def clmWrite_SW (ℓ : Fin L) :
    Params A dIn dOut →L[ℝ] Matrix (A.w ℓ) d ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun θ' => θ'.write ℓ, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }

/-- Helper: the readout, as a continuous linear map of the parameters. -/
private noncomputable def clmD_SW : Params A dIn dOut →L[ℝ] Matrix d dOut ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun θ' => θ'.D, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }

omit [Fintype T] [DecidableEq d] in
@[simp] private theorem clmE_SW_apply (v : Params A dIn dOut) : clmE_SW A v = v.E := rfl

omit [Fintype T] [DecidableEq d] in
@[simp] private theorem clmRead_SW_apply (ℓ : Fin L) (v : Params A dIn dOut) :
    clmRead_SW A ℓ v = v.read ℓ := rfl

omit [Fintype T] [DecidableEq d] in
@[simp] private theorem clmWrite_SW_apply (ℓ : Fin L) (v : Params A dIn dOut) :
    clmWrite_SW A ℓ v = v.write ℓ := rfl

omit [Fintype T] [DecidableEq d] in
@[simp] private theorem clmD_SW_apply (v : Params A dIn dOut) : clmD_SW A v = v.D := rfl

omit [DecidableEq d] in
/-- Helper: the derivative of `θ' ↦ x E' D'` at `θ` along `v` is `x v_E D + x E v_D`. -/
private theorem hasFDerivAt_xED_SW (x : Matrix T dIn ℝ) :
    ∃ g' : Params A dIn dOut →L[ℝ] Matrix T dOut ℝ,
      HasFDerivAt (fun θ' : Params A dIn dOut => x * θ'.E * θ'.D) g' θ ∧
        ∀ v, g' v = x * v.E * θ.D + x * θ.E * v.D := by
  obtain ⟨a', ha, hav⟩ := hasFDerivAt_mul_SW (hasFDerivAt_const x θ) (clmE_SW A).hasFDerivAt
  have hxE : HasFDerivAt (fun θ' : Params A dIn dOut => x * θ'.E) a' θ := ha
  obtain ⟨b', hb, hbv⟩ := hasFDerivAt_mul_SW hxE (clmD_SW A).hasFDerivAt
  refine ⟨b', hb, fun v => ?_⟩
  rw [hbv, hav]
  simp only [clmE_SW_apply, clmD_SW_apply, _root_.zero_apply, Matrix.zero_mul, zero_add]

omit [DecidableEq d] in
/-- Helper: the derivative of the term `θ' ↦ f_ℓ(x E' W'_read) W'_write` of block `ℓ` at `θ`
along `v` (chain rule and product rule). -/
private theorem hasFDerivAt_block_SW (hf : ∀ ℓ, Differentiable ℝ (A.f ℓ)) (x : Matrix T dIn ℝ)
    (ℓ : Fin L) :
    ∃ g' : Params A dIn dOut →L[ℝ] Matrix T d ℝ,
      HasFDerivAt (fun θ' : Params A dIn dOut => A.f ℓ (x * θ'.E * θ'.read ℓ) * θ'.write ℓ) g' θ ∧
        ∀ v, g' v = fderiv ℝ (A.f ℓ) (x * θ.E * θ.read ℓ)
            (x * v.E * θ.read ℓ + x * θ.E * v.read ℓ) * θ.write ℓ
          + A.f ℓ (x * θ.E * θ.read ℓ) * v.write ℓ := by
  -- `θ' ↦ x E'` and `θ' ↦ x E' W'_read`
  obtain ⟨a', ha, hav⟩ := hasFDerivAt_mul_SW (hasFDerivAt_const x θ) (clmE_SW A).hasFDerivAt
  have hxE : HasFDerivAt (fun θ' : Params A dIn dOut => x * θ'.E) a' θ := ha
  obtain ⟨b', hb, hbv⟩ := hasFDerivAt_mul_SW hxE (clmRead_SW A ℓ).hasFDerivAt
  have hxER : HasFDerivAt (fun θ' : Params A dIn dOut => x * θ'.E * θ'.read ℓ) b' θ := hb
  -- the chain rule through `f_ℓ`
  have hfl : HasFDerivAt (A.f ℓ) (fderiv ℝ (A.f ℓ) (x * θ.E * θ.read ℓ))
      (x * θ.E * θ.read ℓ) := (hf ℓ _).hasFDerivAt
  have hc := hfl.comp θ hxER
  have hc' : HasFDerivAt (fun θ' : Params A dIn dOut => A.f ℓ (x * θ'.E * θ'.read ℓ))
      ((fderiv ℝ (A.f ℓ) (x * θ.E * θ.read ℓ)).comp b') θ := hc
  -- the product with `W'_write`
  obtain ⟨c', hcw, hcv⟩ := hasFDerivAt_mul_SW hc' (clmWrite_SW A ℓ).hasFDerivAt
  refine ⟨c', hcw, fun v => ?_⟩
  rw [hcv, ContinuousLinearMap.comp_apply, hbv, hav]
  simp only [clmE_SW_apply, clmRead_SW_apply, clmWrite_SW_apply, _root_.zero_apply,
    Matrix.zero_mul, zero_add]

omit [DecidableEq d] in
/-- Helper: the derivative of `θ' ↦ (∑_ℓ f_ℓ(x E' W'_read) W'_write) D'` at `θ` along `v`. -/
private theorem hasFDerivAt_sumD_SW (hf : ∀ ℓ, Differentiable ℝ (A.f ℓ)) (x : Matrix T dIn ℝ) :
    ∃ g' : Params A dIn dOut →L[ℝ] Matrix T dOut ℝ,
      HasFDerivAt (fun θ' : Params A dIn dOut =>
          (∑ ℓ, A.f ℓ (x * θ'.E * θ'.read ℓ) * θ'.write ℓ) * θ'.D) g' θ ∧
        ∀ v, g' v = (∑ ℓ, (fderiv ℝ (A.f ℓ) (x * θ.E * θ.read ℓ)
            (x * v.E * θ.read ℓ + x * θ.E * v.read ℓ) * θ.write ℓ
          + A.f ℓ (x * θ.E * θ.read ℓ) * v.write ℓ)) * θ.D
          + (∑ ℓ, A.f ℓ (x * θ.E * θ.read ℓ) * θ.write ℓ) * v.D := by
  choose B hB hBv using hasFDerivAt_block_SW A θ hf x
  have hs : HasFDerivAt (fun θ' : Params A dIn dOut =>
      ∑ ℓ, A.f ℓ (x * θ'.E * θ'.read ℓ) * θ'.write ℓ) (∑ ℓ, B ℓ) θ :=
    HasFDerivAt.fun_sum fun ℓ _ => hB ℓ
  obtain ⟨g', hg, hgv⟩ := hasFDerivAt_mul_SW hs (clmD_SW A).hasFDerivAt
  refine ⟨g', hg, fun v => ?_⟩
  rw [hgv, _root_.sum_apply]
  simp only [hBv, clmD_SW_apply]

/-! ### Helpers for the rank: the maps of the small-parameter lemma -/

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the components of a difference of parameters. -/
@[simp] private theorem sub_E_SW (v w : Params A dIn dOut) : (v - w).E = v.E - w.E := rfl

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
@[simp] private theorem sub_read_SW (v w : Params A dIn dOut) (ℓ : Fin L) :
    (v - w).read ℓ = v.read ℓ - w.read ℓ := rfl

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
@[simp] private theorem sub_write_SW (v w : Params A dIn dOut) (ℓ : Fin L) :
    (v - w).write ℓ = v.write ℓ - w.write ℓ := rfl

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
@[simp] private theorem sub_D_SW (v w : Params A dIn dOut) : (v - w).D = v.D - w.D := rfl

/-- Helper: the part `π η = (0, η_read, η_write, 0)` of a direction that the small-parameter lemma
divides by `τ`, as a linear map. -/
private def linPi_SW : Params A dIn dOut →ₗ[ℝ] Params A dIn dOut where
  toFun η := ⟨0, η.read, η.write, 0⟩
  map_add' _ _ := Params.ext' (add_zero 0).symm (fun _ => rfl) (fun _ => rfl) (add_zero 0).symm
  map_smul' c _ := Params.ext' (smul_zero c).symm (fun _ => rfl) (fun _ => rfl) (smul_zero c).symm

/-- Helper: `π` as a continuous linear map. -/
private noncomputable def clmPi_SW : Params A dIn dOut →L[ℝ] Params A dIn dOut :=
  LinearMap.toContinuousLinearMap (linPi_SW A)

omit [Fintype T] [DecidableEq d] in
@[simp] private theorem clmPi_SW_E (η : Params A dIn dOut) : (clmPi_SW A η).E = 0 := rfl

omit [Fintype T] [DecidableEq d] in
@[simp] private theorem clmPi_SW_read (η : Params A dIn dOut) (ℓ : Fin L) :
    (clmPi_SW A η).read ℓ = η.read ℓ := rfl

omit [Fintype T] [DecidableEq d] in
@[simp] private theorem clmPi_SW_write (η : Params A dIn dOut) (ℓ : Fin L) :
    (clmPi_SW A η).write ℓ = η.write ℓ := rfl

omit [Fintype T] [DecidableEq d] in
@[simp] private theorem clmPi_SW_D (η : Params A dIn dOut) : (clmPi_SW A η).D = 0 := rfl

/-- Helper: the writes `η ↦ (0, 0, η_write, 0)`, as a linear map. -/
private def linW_SW : Params A dIn dOut →ₗ[ℝ] Params A dIn dOut where
  toFun η := ⟨0, fun _ => 0, η.write, 0⟩
  map_add' _ _ := Params.ext' (add_zero 0).symm (fun _ => (add_zero 0).symm) (fun _ => rfl)
    (add_zero 0).symm
  map_smul' c _ := Params.ext' (smul_zero c).symm (fun _ => (smul_zero c).symm) (fun _ => rfl)
    (smul_zero c).symm

/-- Helper: `θ' ↦ θ'_τ` as a linear map, for a fixed `τ`. -/
private def linSmall_SW (τ : ℝ) : Params A dIn dOut →ₗ[ℝ] Params A dIn dOut where
  toFun θ' := θ'.smallWrites τ
  map_add' _ _ := Params.ext' rfl (fun _ => rfl) (fun _ => smul_add τ _ _) rfl
  map_smul' c _ := Params.ext' rfl (fun _ => rfl) (fun _ => smul_comm τ c _) rfl

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: `θ'_τ = (θ' - W θ') + τ W θ'`, with `W θ' = (0, 0, θ'_write, 0)`. -/
private theorem smallWrites_eq_SW (τ : ℝ) (θ' : Params A dIn dOut) :
    θ'.smallWrites τ = (θ' - linW_SW A θ') + τ • linW_SW A θ' := by
  refine Params.ext' ?_ (fun ℓ => ?_) (fun ℓ => ?_) ?_
  · show θ'.E = θ'.E - 0 + τ • 0
    rw [sub_zero, smul_zero, add_zero]
  · show θ'.read ℓ = θ'.read ℓ - 0 + τ • 0
    rw [sub_zero, smul_zero, add_zero]
  · show τ • θ'.write ℓ = θ'.write ℓ - θ'.write ℓ + τ • θ'.write ℓ
    rw [sub_self, zero_add]
  · show θ'.D = θ'.D - 0 + τ • 0
    rw [sub_zero, smul_zero, add_zero]

/-- Helper: `η ↦ J_0 η` at one input `x` is linear in `η`. -/
private noncomputable def limitLin_SW (x : Matrix T dIn ℝ) :
    Params A dIn dOut →ₗ[ℝ] Matrix T dOut ℝ where
  toFun η := smallWritesLimit A θ η x
  map_add' η η' := by
    simp only [smallWritesLimit, Params.add_E, Params.add_D, Params.add_read, Params.add_write,
      Matrix.add_mul, Matrix.mul_add, map_add, Finset.sum_add_distrib]
    abel
  map_smul' c η := by
    simp only [smallWritesLimit, Params.smul_E, Params.smul_D, Params.smul_read,
      Params.smul_write, Matrix.smul_mul, Matrix.mul_smul, map_smul, ← Finset.smul_sum,
      ← smul_add, RingHom.id_apply]

/-- Helper (kernel stabilisation): for a family of linear maps on a finite-dimensional space,
finitely many of them have the common kernel of all of them. -/
private theorem exists_batch_ker_SW {ι P F : Type*} [AddCommGroup P] [Module ℝ P]
    [FiniteDimensional ℝ P] [AddCommGroup F] [Module ℝ F] (Λ : ι → P →ₗ[ℝ] F) :
    ∃ (n : ℕ) (X : Fin n → ι), ∀ η, (∀ i, Λ (X i) η = 0) → ∀ x, Λ x η = 0 := by
  -- the common kernel of a batch
  let K : ∀ n : ℕ, (Fin n → ι) → Submodule ℝ P := fun n X => ⨅ i, LinearMap.ker (Λ (X i))
  have hmem : ∀ n (X : Fin n → ι) η, η ∈ K n X ↔ ∀ i, Λ (X i) η = 0 := by
    intro n X η
    simp only [K, Submodule.mem_iInf, LinearMap.mem_ker]
  -- a batch whose common kernel has least dimension
  obtain ⟨n, X, hX⟩ := Nat.sInf_mem (s := {k : ℕ | ∃ (n : ℕ) (X : Fin n → ι),
      k = Module.finrank ℝ (K n X)}) ⟨_, 0, Fin.elim0, rfl⟩
  refine ⟨n, X, fun η hη x => ?_⟩
  -- adding the input `x` can only shrink the kernel, and not its dimension: it stays the same
  have hle : K (n + 1) (Fin.cons x X) ≤ K n X := by
    intro ξ hξ
    rw [hmem] at hξ ⊢
    intro i
    simpa only [Fin.cons_succ] using hξ i.succ
  have heq := Submodule.eq_of_le_of_finrank_le hle (by
    rw [← hX]
    exact Nat.sInf_le ⟨n + 1, Fin.cons x X, rfl⟩)
  have hηK : η ∈ K (n + 1) (Fin.cons x X) := by
    rw [heq, hmem]
    exact hη
  rw [hmem] at hηK
  simpa only [Fin.cons_zero] using hηK 0

/-- **Proof of Lemma A.27, "The rank", for real-analytic blocks without normalization:** if every
direction that is flat for `J_0` lies in a subspace `V` of the parameters, then for all small
`τ ≠ 0` the residual network has `fd(θ_τ) ≥ P - dim V`. -/
theorem eventually_funDim_smallWrites_ge (hA : A.χ = id)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (V : Submodule ℝ (Params A dIn dOut))
    (hV : ∀ η : Params A dIn dOut, (∀ x, smallWritesLimit A θ η x = 0) → η ∈ V) :
    ∀ᶠ τ in 𝓝[≠] (0 : ℝ),
      Module.finrank ℝ (Params A dIn dOut)
        ≤ funDim A 1 (θ.smallWrites τ) + Module.finrank ℝ V := by
  -- the maps `f_ℓ` are differentiable, and `χ = id` is analytic
  have hfd : ∀ ℓ, Differentiable ℝ (A.f ℓ) := fun ℓ z =>
    ((hf ℓ) z (Set.mem_univ z)).differentiableAt
  have hχ : AnalyticOnNhd ℝ A.χ Set.univ := by
    rw [hA]
    exact analyticOnNhd_id
  -- (b) a finite batch `X` on which the flat directions of `J_0` are decided
  obtain ⟨n, X, hX⟩ := exists_batch_ker_SW (limitLin_SW A θ (dOut := dOut))
  -- the outputs on the batch are analytic, hence `C²`, in the parameters
  have hev : ∀ i, AnalyticOnNhd ℝ (fun θ' : Params A dIn dOut => eval A 1 θ' (X i)) Set.univ :=
    fun i => analyticOnNhd_eval_params A 1 hf hχ (X i)
  have hEvC : ContDiff ℝ 2 (evalBatch A 1 X : Params A dIn dOut → Fin n → Matrix T dOut ℝ) :=
    contDiff_pi.2 fun i => (hev i).contDiff
  -- `G τ θ'` is the batch of outputs at `θ'_τ`
  set G : ℝ → Params A dIn dOut → (Fin n → Matrix T dOut ℝ) :=
    fun τ θ' => evalBatch A 1 X (θ'.smallWrites τ) with hGdef
  -- (d) `(τ, θ') ↦ G τ θ'` is `C²`: `θ'_τ = (θ' - W θ') + τ W θ'` is smooth in `(τ, θ')`
  have hG : ContDiff ℝ 2 (fun p : ℝ × Params A dIn dOut => G p.1 p.2) := by
    let W := LinearMap.toContinuousLinearMap (linW_SW A (dIn := dIn) (dOut := dOut))
    have hS : ContDiff ℝ 2 (fun p : ℝ × Params A dIn dOut => (p.2 - W p.2) + p.1 • W p.2) :=
      (contDiff_snd.sub (W.contDiff.comp contDiff_snd)).add
        (contDiff_fst.smul (W.contDiff.comp contDiff_snd))
    have hc := hEvC.comp hS
    have hfun : (fun p : ℝ × Params A dIn dOut => G p.1 p.2)
        = evalBatch A 1 X ∘ (fun p : ℝ × Params A dIn dOut => (p.2 - W p.2) + p.1 • W p.2) := by
      funext p
      show evalBatch A 1 X (p.2.smallWrites p.1) = evalBatch A 1 X ((p.2 - W p.2) + p.1 • W p.2)
      rw [smallWrites_eq_SW A p.1 p.2]
      rfl
    rw [hfun]
    exact hc
  -- step 1: `G 0 θ' = (X_i E' D')_i`; step 2: `∂_τ G(0, θ') = ((∑_ℓ f_ℓ(X_i E' W'_read) W'_write) D')_i`
  have hG0 : G 0 = fun θ' i => X i * θ'.E * θ'.D := by
    funext θ' i
    exact eval_smallWrites_zero A θ' hA (X i)
  have hG1 : (fun θ' => deriv (fun τ => G τ θ') 0)
      = fun θ' i => (∑ ℓ, A.f ℓ (X i * θ'.E * θ'.read ℓ) * θ'.write ℓ) * θ'.D := by
    funext θ'
    have hd : HasDerivAt (fun τ => G τ θ')
        (fun i => (∑ ℓ, A.f ℓ (X i * θ'.E * θ'.read ℓ) * θ'.write ℓ) * θ'.D) 0 :=
      hasDerivAt_pi.2 fun i => hasDerivAt_eval_smallWrites A θ' hA hfd (X i)
    exact hd.deriv
  -- their derivatives in the parameters at `θ`
  choose a' ha ha' using fun i => hasFDerivAt_xED_SW A θ (dOut := dOut) (X i)
  choose b' hb hb' using fun i => hasFDerivAt_sumD_SW A θ (dOut := dOut) hfd (X i)
  have hD0 : ∀ v, fderiv ℝ (G 0) θ v = fun i => X i * v.E * θ.D + X i * θ.E * v.D := by
    intro v
    have hd : HasFDerivAt (G 0) (ContinuousLinearMap.pi a') θ := by
      rw [hG0]
      exact hasFDerivAt_pi.2 ha
    rw [hd.fderiv]
    funext i
    exact ha' i v
  have hD1 : ∀ v, fderiv ℝ (fun θ' => deriv (fun τ => G τ θ') 0) θ v
      = fun i => (∑ ℓ, (fderiv ℝ (A.f ℓ) (X i * θ.E * θ.read ℓ)
            (X i * v.E * θ.read ℓ + X i * θ.E * v.read ℓ) * θ.write ℓ
          + A.f ℓ (X i * θ.E * θ.read ℓ) * v.write ℓ)) * θ.D
          + (∑ ℓ, A.f ℓ (X i * θ.E * θ.read ℓ) * θ.write ℓ) * v.D := by
    intro v
    have hd : HasFDerivAt (fun θ' => deriv (fun τ => G τ θ') 0) (ContinuousLinearMap.pi b') θ := by
      rw [hG1]
      exact hasFDerivAt_pi.2 hb
    rw [hd.fderiv]
    funext i
    exact hb' i v
  -- (e) `G 0` does not move along `π η = (0, η_read, η_write, 0)`
  have h0 : ∀ η, fderiv ℝ (G 0) θ (clmPi_SW A η) = 0 := by
    intro η
    rw [hD0]
    funext i
    simp only [clmPi_SW_E, clmPi_SW_D, Matrix.mul_zero, Matrix.zero_mul, add_zero, Pi.zero_apply]
  -- (f) the limit `D_θ G(0, θ)(η - π η) + D_θ(∂_τ G(0, ·))(θ)(π η)` is `(J_0 η)(X_i)`, so its
  -- kernel is flat for `J_0` on the batch, hence at every input, hence in `V`
  have hV' : ∀ η, fderiv ℝ (G 0) θ (η - clmPi_SW A η)
      + fderiv ℝ (fun θ' => deriv (fun τ => G τ θ') 0) θ (clmPi_SW A η) = 0 → η ∈ V := by
    intro η hη
    rw [hD0, hD1] at hη
    apply hV
    refine hX η (fun i => ?_)
    have hi := congrFun hη i
    simp only [Pi.add_apply, Pi.zero_apply] at hi
    show smallWritesLimit A θ η (X i) = 0
    refine Eq.trans ?_ hi
    simp only [smallWritesLimit, sub_E_SW, sub_D_SW, clmPi_SW_E, clmPi_SW_D, clmPi_SW_read,
      clmPi_SW_write, sub_zero, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
      Matrix.mul_add, Matrix.sum_mul, Matrix.mul_assoc]
  -- (c) the small-parameter lemma
  have key := eventually_finrank_le_of_small_parameter G hG (clmPi_SW A) θ h0 V hV'
  -- (g) `D_θ G(τ, θ) = J(θ_τ) ∘ S_τ`, so its rank is at most `jacobianRank` at `θ_τ`, at most `fd(θ_τ)`
  have hrank : ∀ τ, Module.finrank ℝ (LinearMap.range (fderiv ℝ (G τ) θ).toLinearMap)
      ≤ funDim A 1 (θ.smallWrites τ) := by
    intro τ
    let S := LinearMap.toContinuousLinearMap (linSmall_SW A (dIn := dIn) (dOut := dOut) τ)
    have hEv : DifferentiableAt ℝ (evalBatch A 1 X) (S θ) :=
      differentiableAt_pi.2 fun i => (hev i _ (Set.mem_univ _)).differentiableAt
    have hcomp : HasFDerivAt (G τ) ((fderiv ℝ (evalBatch A 1 X) (S θ)).comp S) θ := by
      have hc := hEv.hasFDerivAt.comp θ S.hasFDerivAt
      exact hc
    rw [hcomp.fderiv]
    calc Module.finrank ℝ
          (LinearMap.range ((fderiv ℝ (evalBatch A 1 X) (S θ)).comp S).toLinearMap)
        ≤ Module.finrank ℝ (LinearMap.range (fderiv ℝ (evalBatch A 1 X) (S θ)).toLinearMap) :=
          Submodule.finrank_mono (LinearMap.range_comp_le_range _ _)
      _ = jacobianRank A 1 X (θ.smallWrites τ) := rfl
      _ ≤ funDim A 1 (θ.smallWrites τ) := jacobianRank_le_funDim _ X
  filter_upwards [key] with τ hτ
  exact hτ.trans (Nat.add_le_add_right (hrank τ) _)

end Skips
