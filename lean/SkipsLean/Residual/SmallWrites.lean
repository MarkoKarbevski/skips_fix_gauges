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

/-- **Proof of Lemma A.27, "The rank", for real-analytic blocks without normalization:** if every
direction that is flat for `J_0` lies in a subspace `V` of the parameters, then for all small
`τ ≠ 0` the residual network has `fd(θ_τ) ≥ P - dim V`. -/
theorem eventually_funDim_smallWrites_ge (hA : A.χ = id)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (V : Submodule ℝ (Params A dIn dOut))
    (hV : ∀ η : Params A dIn dOut, (∀ x, smallWritesLimit A θ η x = 0) → η ∈ V) :
    ∀ᶠ τ in 𝓝[≠] (0 : ℝ),
      Module.finrank ℝ (Params A dIn dOut)
        ≤ funDim A 1 (θ.smallWrites τ) + Module.finrank ℝ V := by
  sorry

end Skips
