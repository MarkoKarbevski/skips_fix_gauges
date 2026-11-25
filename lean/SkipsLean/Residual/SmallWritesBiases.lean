import SkipsLean.Residual.SmallWrites
import SkipsLean.Dimension.FunctionalBiases

/-!
# Residual networks with biases and small writes

Paper (skips paper), Lemma A.27 (Small writes): "With biases, `θ` also holds `b_E`, `b_read^ℓ`,
`b_write^ℓ` and `b_D`, and `θ_τ` holds `τ b_write^ℓ` in place of `b_write^ℓ`." Its proof, "MLP
blocks without normalization": "At `θ_τ` every hidden state is `h_ℓ = xE + b_E + O(τ)`, so the
output is

`y = xED + b_E D + b_D
  + τ ∑_ℓ (f((xE + b_E) W_read^ℓ + b_read^ℓ) W_write^ℓ + b_write^ℓ) D + O(τ²)`."

"Differentiating along `η` and letting `τ → 0`,
`(J_0 η)(x) = x ψ_M + ψ_γ + ∑_i (σ(z_i) ψ_{a_i} + σ'(z_i) (x ψ_{c_i} + ψ_{β_i}) a_i)`, where […]
`ψ_M = η_E D + E η_D`, `ψ_γ = η_{b_E} D + b_E η_D + η_{b_D} + ∑_ℓ η_{b_write^ℓ} D`,
`ψ_C = E η_read`, `ψ_β = b_E η_read + η_{b_read}`, `ψ_A = η_write D`."

Here, for the networks with biases of `Network/Biases.lean`, the twins of the definitions and
statements of `Residual/SmallWrites.lean`:

* `smallWritesB p τ`: the weights and biases `θ_τ`: the writes `τ W_write^ℓ` and the write biases
  `τ b_write^ℓ`, everything else as in `p = (θ, b)`.
* `smallWritesLimitB A p η x`: the limit `(J_0 η)(x)`, written for arbitrary differentiable maps
  `f_ℓ`: with `h = xE + b_E`,
  `x ψ_M + ψ_γ + ∑_ℓ (D f_ℓ(h W_read^ℓ + b_read^ℓ)(h η_read^ℓ + η_{b_read^ℓ}) W_write^ℓ
  + f_ℓ(h W_read^ℓ + b_read^ℓ) η_write^ℓ) D` (here `x ψ_C + ψ_β = h η_read + η_{b_read}`).
* `evalB_smallWritesB_zero`, `hasDerivAt_evalB_smallWritesB`: the two terms of the expansion of
  `y`.
* `eventually_funDimB_smallWritesB_ge`: the last paragraph of the proof ("The rank"): if the flat
  directions of `J_0` lie in a space `V`, then `fd(θ_τ) ≥ P − dim V` for all small `τ ≠ 0`, `P`
  counting the biases.

Numeric check: `ai_notes/small_writes_biases_check_2026-11-25.py`.
-/

namespace Skips

open Matrix Filter Topology
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]

/-- **The weights and biases `θ_τ` of Lemma A.27 with biases:** the embedding, the reads, the
readout, the embedding bias, the read biases and the readout bias of `p = (θ, b)`, the writes
`τ W_write^ℓ` and the write biases `τ b_write^ℓ`. -/
def smallWritesB {A : Arch T d L} (p : ParamsB A dIn dOut) (τ : ℝ) : ParamsB A dIn dOut :=
  (p.1.smallWrites τ,
    { E := p.2.E
      read := p.2.read
      write := fun ℓ => τ • p.2.write ℓ
      D := p.2.D })

/-- **The limit `J_0` of the proof of Lemma A.27 with biases, at one input `x`,** without
normalization: with `h = xE + b_E`,
`(J_0 η)(x) = x (η_E D + E η_D) + (η_{b_E} D + b_E η_D + η_{b_D} + ∑_ℓ η_{b_write^ℓ} D)
+ ∑_ℓ (D f_ℓ(h W_read^ℓ + b_read^ℓ)(h η_read^ℓ + η_{b_read^ℓ}) W_write^ℓ
+ f_ℓ(h W_read^ℓ + b_read^ℓ) η_write^ℓ) D`, the row `ψ_γ` added to every token. -/
noncomputable def smallWritesLimitB (A : Arch T d L) (p η : ParamsB A dIn dOut)
    (x : Matrix T dIn ℝ) : Matrix T dOut ℝ :=
  x * (η.1.E * p.1.D + p.1.E * η.1.D)
    + Matrix.of (fun _ => η.2.E ᵥ* p.1.D + p.2.E ᵥ* η.1.D + η.2.D + ∑ ℓ, η.2.write ℓ ᵥ* p.1.D)
    + ∑ ℓ, (fderiv ℝ (A.f ℓ)
          ((x * p.1.E + Matrix.of fun _ => p.2.E) * p.1.read ℓ + Matrix.of fun _ => p.2.read ℓ)
          ((x * p.1.E + Matrix.of fun _ => p.2.E) * η.1.read ℓ + Matrix.of fun _ => η.2.read ℓ)
          * p.1.write ℓ
        + A.f ℓ
          ((x * p.1.E + Matrix.of fun _ => p.2.E) * p.1.read ℓ + Matrix.of fun _ => p.2.read ℓ)
          * η.1.write ℓ) * p.1.D

variable (A : Arch T d L) (p : ParamsB A dIn dOut)

/-! ### Helpers: the components of `θ_τ`, and rows added to every token -/

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the embedding of `θ_τ` is that of `p`. -/
@[simp] private theorem smallWritesB_E_swb (τ : ℝ) : (smallWritesB p τ).1.E = p.1.E := rfl

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the reads of `θ_τ` are those of `p`. -/
@[simp] private theorem smallWritesB_read_swb (τ : ℝ) (ℓ : Fin L) :
    (smallWritesB p τ).1.read ℓ = p.1.read ℓ := rfl

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the writes of `θ_τ` are `τ W_write^ℓ`. -/
@[simp] private theorem smallWritesB_write_swb (τ : ℝ) (ℓ : Fin L) :
    (smallWritesB p τ).1.write ℓ = τ • p.1.write ℓ := rfl

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the readout of `θ_τ` is that of `p`. -/
@[simp] private theorem smallWritesB_D_swb (τ : ℝ) : (smallWritesB p τ).1.D = p.1.D := rfl

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the embedding bias of `θ_τ` is that of `p`. -/
@[simp] private theorem smallWritesB_bE_swb (τ : ℝ) : (smallWritesB p τ).2.E = p.2.E := rfl

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the read biases of `θ_τ` are those of `p`. -/
@[simp] private theorem smallWritesB_bread_swb (τ : ℝ) (ℓ : Fin L) :
    (smallWritesB p τ).2.read ℓ = p.2.read ℓ := rfl

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the write biases of `θ_τ` are `τ b_write^ℓ`. -/
@[simp] private theorem smallWritesB_bwrite_swb (τ : ℝ) (ℓ : Fin L) :
    (smallWritesB p τ).2.write ℓ = τ • p.2.write ℓ := rfl

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the readout bias of `θ_τ` is that of `p`. -/
@[simp] private theorem smallWritesB_bD_swb (τ : ℝ) : (smallWritesB p τ).2.D = p.2.D := rfl

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the row `v + w` added to every token is the row `v` added plus the row `w` added. -/
private theorem of_row_add_swb {n : Type*} (v w : n → ℝ) :
    (Matrix.of fun _ : T => v + w) = (Matrix.of fun _ : T => v) + Matrix.of fun _ : T => w :=
  rfl

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the same for `c v`. -/
private theorem of_row_smul_swb {n : Type*} (c : ℝ) (v : n → ℝ) :
    (Matrix.of fun _ : T => c • v) = c • Matrix.of fun _ : T => v := rfl

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the same for the row `0`. -/
private theorem of_row_zero_swb {n : Type*} : (Matrix.of fun _ : T => (0 : n → ℝ)) = 0 := rfl

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the same for a sum of rows. -/
private theorem of_row_sum_swb {n ι : Type*} (s : Finset ι) (w : ι → n → ℝ) :
    (Matrix.of fun _ : T => ∑ i ∈ s, w i) = ∑ i ∈ s, Matrix.of fun _ : T => w i := by
  ext t j
  simp only [Matrix.of_apply, Finset.sum_apply, Matrix.sum_apply]

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the row `v` added to every token, times `M`, is the row `v M` added to every
token. -/
private theorem of_row_mul_swb {n k : Type*} [Fintype n] (v : n → ℝ) (M : Matrix n k ℝ) :
    (Matrix.of fun _ : T => v) * M = Matrix.of fun _ : T => v ᵥ* M := rfl

/-! ### The expansion of the output at `θ_τ` -/

omit [Fintype T] [Fintype dOut] in
/-- Helper: the residual step at `θ_τ`,
`h_{k+1} = h_k + τ (f_k(h_k W_read^k + b_read^k) W_write^k + b_write^k)`. -/
private theorem hiddenB_smallWritesB_succ_swb (hA : A.χ = id) (x : Matrix T dIn ℝ) (τ : ℝ)
    (k : Fin L) :
    hiddenB A 1 (smallWritesB p τ).1 (smallWritesB p τ).2 x k.succ
      = hiddenB A 1 (smallWritesB p τ).1 (smallWritesB p τ).2 x k.castSucc
        + τ • (A.f k (hiddenB A 1 (smallWritesB p τ).1 (smallWritesB p τ).2 x k.castSucc
            * p.1.read k + Matrix.of fun _ => p.2.read k) * p.1.write k
          + Matrix.of fun _ => p.2.write k) := by
  rw [hiddenB_succ, hA, Pi.one_apply, Matrix.mul_one, id_eq, smallWritesB_read_swb,
    smallWritesB_bread_swb, smallWritesB_write_swb, smallWritesB_bwrite_swb, Matrix.mul_smul,
    of_row_smul_swb, smul_add]

omit [Fintype T] [Fintype dOut] in
/-- Helper: at `τ = 0` every hidden state is `x E + b_E`. -/
private theorem hiddenB_smallWritesB_zero_swb (hA : A.χ = id) (x : Matrix T dIn ℝ)
    (k : Fin (L + 1)) :
    hiddenB A 1 (smallWritesB p 0).1 (smallWritesB p 0).2 x k
      = x * p.1.E + Matrix.of fun _ => p.2.E := by
  induction k using Fin.induction with
  | zero => exact hiddenB_zero A 1 _ _ x
  | succ k ih => rw [hiddenB_smallWritesB_succ_swb A p hA, ih, zero_smul, add_zero]

omit [Fintype T] [Fintype dOut] in
/-- At `τ = 0` the residual network with biases, without normalization, computes
`x ↦ (xE + b_E) D + b_D` (proof of Lemma A.27: "`y = xED + b_E D + b_D + τ (…) + O(τ²)`"). -/
theorem evalB_smallWritesB_zero (hA : A.χ = id) (x : Matrix T dIn ℝ) :
    evalB A 1 (smallWritesB p 0).1 (smallWritesB p 0).2 x
      = (x * p.1.E + Matrix.of fun _ => p.2.E) * p.1.D + Matrix.of fun _ => p.2.D := by
  rw [evalB, hiddenB_smallWritesB_zero_swb A p hA, hA, id_eq, smallWritesB_D_swb,
    smallWritesB_bD_swb]

/-- Helper: the derivative at `0` of `τ ↦ τ g(τ)`, for `g` continuous at `0`, is `g(0)`. -/
private theorem hasDerivAt_smul_self_swb {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g : ℝ → F} (hg : ContinuousAt g 0) : HasDerivAt (fun τ : ℝ => τ • g τ) (g 0) 0 := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  refine Tendsto.congr' ?_ (hg.tendsto.mono_left nhdsWithin_le_nhds)
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [zero_add, zero_smul, sub_zero, smul_smul, inv_mul_cancel₀ ht, one_smul]

/-- Helper: a sum over the blocks before `k + 1` is the sum over the blocks before `k` plus the
term of block `k`. -/
private theorem sum_ite_lt_succ_swb {M : Type*} [AddCommMonoid M] {m : ℕ} (a : Fin m → M)
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
        simp only [lt_add_iff_pos_right, Order.lt_one_iff, ↓reduceIte, lt_self_iff_false, zero_add]
      · have h3 : ¬ (ℓ : ℕ) < k + 1 := fun h => h2 (Fin.ext (by omega))
        simp only [h1, h2, h3, ite_false, add_zero]
  rw [Finset.sum_congr rfl fun ℓ _ => h ℓ, Finset.sum_add_distrib]
  simp only [Fin.val_fin_lt, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

omit [Fintype T] [Fintype dOut] in
/-- Helper: every hidden state at `θ_τ` is continuous in `τ`. -/
private theorem continuous_hiddenB_smallWritesB_swb (hA : A.χ = id)
    (hf : ∀ ℓ, Continuous (A.f ℓ)) (x : Matrix T dIn ℝ) (k : Fin (L + 1)) :
    Continuous (fun τ : ℝ => hiddenB A 1 (smallWritesB p τ).1 (smallWritesB p τ).2 x k) := by
  induction k using Fin.induction with
  | zero =>
    simp only [hiddenB_zero, smallWritesB_E_swb, smallWritesB_bE_swb]
    exact continuous_const
  | succ k ih =>
    simp only [hiddenB_smallWritesB_succ_swb A p hA]
    exact ih.add (continuous_id.smul ((((hf k).comp ((ih.matrix_mul continuous_const).add
      continuous_const)).matrix_mul continuous_const).add continuous_const))

omit [Fintype dOut] in
/-- Helper: the derivative at `τ = 0` of the hidden state `h_k` at `θ_τ` is the sum over the
blocks `ℓ < k` of `f_ℓ((x E + b_E) W_read^ℓ + b_read^ℓ) W_write^ℓ + b_write^ℓ`. -/
private theorem hasDerivAt_hiddenB_smallWritesB_swb (hA : A.χ = id)
    (hf : ∀ ℓ, Continuous (A.f ℓ)) (x : Matrix T dIn ℝ) (k : Fin (L + 1)) :
    HasDerivAt (fun τ : ℝ => hiddenB A 1 (smallWritesB p τ).1 (smallWritesB p τ).2 x k)
      (∑ ℓ : Fin L, if (ℓ : ℕ) < (k : ℕ) then
        (A.f ℓ ((x * p.1.E + Matrix.of fun _ => p.2.E) * p.1.read ℓ
          + Matrix.of fun _ => p.2.read ℓ) * p.1.write ℓ + (Matrix.of fun _ => p.2.write ℓ))
        else 0) 0 := by
  induction k using Fin.induction with
  | zero =>
    -- `h_0 = x E + b_E` does not depend on `τ`
    simp only [hiddenB_zero, smallWritesB_E_swb, smallWritesB_bE_swb, Fin.val_zero,
      Nat.not_lt_zero, ite_false, Finset.sum_const_zero]
    exact hasDerivAt_const _ _
  | succ k ih =>
    -- `h_{k+1}(τ) = h_k(τ) + τ g(τ)`, and the derivative of `τ g(τ)` at `0` is `g(0)`
    simp only [hiddenB_smallWritesB_succ_swb A p hA]
    have hg : ContinuousAt (fun τ : ℝ =>
        A.f k (hiddenB A 1 (smallWritesB p τ).1 (smallWritesB p τ).2 x k.castSucc * p.1.read k
          + Matrix.of fun _ => p.2.read k) * p.1.write k + Matrix.of fun _ => p.2.write k) 0 :=
      ((((hf k).comp (((continuous_hiddenB_smallWritesB_swb A p hA hf x k.castSucc).matrix_mul
        continuous_const).add continuous_const)).matrix_mul continuous_const).add
        continuous_const).continuousAt
    have h2 := ih.add (hasDerivAt_smul_self_swb hg)
    -- `g(0)` is the term of block `k` at `h_k(0) = x E + b_E`
    have hv : (∑ ℓ : Fin L, if (ℓ : ℕ) < (k.castSucc : ℕ) then
          (A.f ℓ ((x * p.1.E + Matrix.of fun _ => p.2.E) * p.1.read ℓ
            + Matrix.of fun _ => p.2.read ℓ) * p.1.write ℓ + (Matrix.of fun _ => p.2.write ℓ))
          else 0)
        + (A.f k (hiddenB A 1 (smallWritesB p 0).1 (smallWritesB p 0).2 x k.castSucc
            * p.1.read k + Matrix.of fun _ => p.2.read k) * p.1.write k
          + Matrix.of fun _ => p.2.write k)
        = ∑ ℓ : Fin L, if (ℓ : ℕ) < (k.succ : ℕ) then
          (A.f ℓ ((x * p.1.E + Matrix.of fun _ => p.2.E) * p.1.read ℓ
            + Matrix.of fun _ => p.2.read ℓ) * p.1.write ℓ + (Matrix.of fun _ => p.2.write ℓ))
          else 0 := by
      rw [hiddenB_smallWritesB_zero_swb A p hA, Fin.val_succ, Fin.val_castSucc]
      exact (sum_ite_lt_succ_swb (fun ℓ => A.f ℓ ((x * p.1.E + Matrix.of fun _ => p.2.E)
        * p.1.read ℓ + Matrix.of fun _ => p.2.read ℓ) * p.1.write ℓ
        + Matrix.of fun _ => p.2.write ℓ) k).symm
    rw [hv] at h2
    exact h2

/-- Helper: `y ↦ y M`, as a linear map. -/
private def mulRightLin_swb {m n q : Type*} [Fintype n] (M : Matrix n q ℝ) :
    Matrix m n ℝ →ₗ[ℝ] Matrix m q ℝ where
  toFun X := X * M
  map_add' X Y := Matrix.add_mul X Y M
  map_smul' c X := Matrix.smul_mul c X M

/-- Helper: `y ↦ y M`, as a continuous linear map. -/
private noncomputable def mulRightCLM_swb {m n q : Type*} [Fintype m] [Fintype n] [Fintype q]
    (M : Matrix n q ℝ) : Matrix m n ℝ →L[ℝ] Matrix m q ℝ :=
  LinearMap.toContinuousLinearMap (mulRightLin_swb M)

/-- **The term of order `τ` of the output at `θ_τ`, with biases** (proof of Lemma A.27, the
expansion of `y`): the derivative of `τ ↦ F_{θ_τ}(x)` at `τ = 0` is
`∑_ℓ (f_ℓ((xE + b_E) W_read^ℓ + b_read^ℓ) W_write^ℓ + b_write^ℓ) D`. -/
theorem hasDerivAt_evalB_smallWritesB (hA : A.χ = id) (hf : ∀ ℓ, Differentiable ℝ (A.f ℓ))
    (x : Matrix T dIn ℝ) :
    HasDerivAt (fun τ : ℝ => evalB A 1 (smallWritesB p τ).1 (smallWritesB p τ).2 x)
      ((∑ ℓ, (A.f ℓ ((x * p.1.E + Matrix.of fun _ => p.2.E) * p.1.read ℓ
            + Matrix.of fun _ => p.2.read ℓ) * p.1.write ℓ
          + Matrix.of fun _ => p.2.write ℓ)) * p.1.D) 0 := by
  -- the derivative of the last hidden state: every block is before `L`
  have hL := hasDerivAt_hiddenB_smallWritesB_swb A p hA (fun ℓ => (hf ℓ).continuous) x
    (Fin.last L)
  have hsum : (∑ ℓ : Fin L, if (ℓ : ℕ) < ((Fin.last L : Fin (L + 1)) : ℕ) then
        (A.f ℓ ((x * p.1.E + Matrix.of fun _ => p.2.E) * p.1.read ℓ
          + Matrix.of fun _ => p.2.read ℓ) * p.1.write ℓ + (Matrix.of fun _ => p.2.write ℓ))
        else 0)
      = ∑ ℓ, (A.f ℓ ((x * p.1.E + Matrix.of fun _ => p.2.E) * p.1.read ℓ
          + Matrix.of fun _ => p.2.read ℓ) * p.1.write ℓ + Matrix.of fun _ => p.2.write ℓ) :=
    Finset.sum_congr rfl fun ℓ _ => by simp only [Fin.val_last, ℓ.isLt, ↓reduceIte]
  rw [hsum] at hL
  -- the output is `h_L D + b_D`, and `y ↦ y D` is linear
  have hc := ((mulRightCLM_swb (m := T) p.1.D).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hL).add_const
    (Matrix.of fun _ : T => p.2.D)
  simp only [evalB, hA, id_eq, smallWritesB_D_swb, smallWritesB_bD_swb]
  exact hc

/-! ### Helpers for the rank: derivatives in the weights and biases -/

/-- Helper: matrix multiplication as a continuous bilinear map. -/
private noncomputable def mulB_swb (m n q : Type*) [Fintype m] [Fintype n] [Fintype q] :
    Matrix m n ℝ →L[ℝ] Matrix n q ℝ →L[ℝ] Matrix m q ℝ :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap :
      (Matrix n q ℝ →ₗ[ℝ] Matrix m q ℝ) ≃ₗ[ℝ] (Matrix n q ℝ →L[ℝ] Matrix m q ℝ)).toLinearMap ∘ₗ
      LinearMap.mk₂ ℝ (fun a b => a * b) Matrix.add_mul (fun c a b => Matrix.smul_mul c a b)
        Matrix.mul_add (fun c a b => Matrix.mul_smul a c b))

/-- Helper: the product rule for matrix-valued maps, with the value of the derivative,
`(f g)' v = f' v g + f g' v`. -/
private theorem hasFDerivAt_mul_swb {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m n q : Type*} [Fintype m] [Fintype n] [Fintype q] {f : E → Matrix m n ℝ}
    {g : E → Matrix n q ℝ} {f' : E →L[ℝ] Matrix m n ℝ} {g' : E →L[ℝ] Matrix n q ℝ} {y : E}
    (hf : HasFDerivAt f f' y) (hg : HasFDerivAt g g' y) :
    ∃ h' : E →L[ℝ] Matrix m q ℝ, HasFDerivAt (fun z => f z * g z) h' y ∧
      ∀ v, h' v = f' v * g y + f y * g' v := by
  -- the derivative of the bilinear map `(a, b) ↦ a b` along `(f, g)`
  have h := (mulB_swb m n q).hasFDerivAt_of_bilinear hf hg
  refine ⟨_, h, fun v => ?_⟩
  show f y * g' v + f' v * g y = _
  exact add_comm _ _

/-- Helper: the product rule followed by a sum, `(f g + c)' v = f' v g + f g' v + c' v`. -/
private theorem hasFDerivAt_mul_add_swb {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m n q : Type*} [Fintype m] [Fintype n] [Fintype q] {f : E → Matrix m n ℝ}
    {g : E → Matrix n q ℝ} {c : E → Matrix m q ℝ} {f' : E →L[ℝ] Matrix m n ℝ}
    {g' : E →L[ℝ] Matrix n q ℝ} {c' : E →L[ℝ] Matrix m q ℝ} {y : E}
    (hf : HasFDerivAt f f' y) (hg : HasFDerivAt g g' y) (hc : HasFDerivAt c c' y) :
    ∃ h' : E →L[ℝ] Matrix m q ℝ, HasFDerivAt (fun z => f z * g z + c z) h' y ∧
      ∀ v, h' v = f' v * g y + f y * g' v + c' v := by
  obtain ⟨h', hh, hhv⟩ := hasFDerivAt_mul_swb hf hg
  refine ⟨h' + c', hh.add hc, fun v => ?_⟩
  show h' v + c' v = _
  rw [hhv]

/-- Helper: a linear map from a finite-dimensional space to matrices is its own derivative. -/
private theorem hasFDerivAt_lin_swb {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {m n : Type*} [Fintype m] [Fintype n] (f : E → Matrix m n ℝ)
    (hadd : ∀ u v, f (u + v) = f u + f v) (hsmul : ∀ (c : ℝ) u, f (c • u) = c • f u) (y : E) :
    ∃ f' : E →L[ℝ] Matrix m n ℝ, HasFDerivAt f f' y ∧ ∀ v, f' v = f v :=
  ⟨LinearMap.toContinuousLinearMap ⟨⟨f, hadd⟩, hsmul⟩,
    (LinearMap.toContinuousLinearMap ⟨⟨f, hadd⟩, hsmul⟩).hasFDerivAt, fun _ => rfl⟩

/-- Helper: the derivative of the term `z ↦ f(h(z) R(z) + b(z)) W(z) + c(z)` of a block (the
chain rule through `f` and two product rules). -/
private theorem hasFDerivAt_block_swb {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m n r w : Type*} [Fintype m] [Fintype n] [Fintype r] [Fintype w]
    (f : Matrix m r ℝ → Matrix m w ℝ) {h : E → Matrix m n ℝ} {R : E → Matrix n r ℝ}
    {b : E → Matrix m r ℝ} {W : E → Matrix w n ℝ} {c : E → Matrix m n ℝ}
    {h' : E →L[ℝ] Matrix m n ℝ} {R' : E →L[ℝ] Matrix n r ℝ} {b' : E →L[ℝ] Matrix m r ℝ}
    {W' : E →L[ℝ] Matrix w n ℝ} {c' : E →L[ℝ] Matrix m n ℝ} {y : E}
    (hf : DifferentiableAt ℝ f (h y * R y + b y)) (hh : HasFDerivAt h h' y)
    (hR : HasFDerivAt R R' y) (hb : HasFDerivAt b b' y) (hW : HasFDerivAt W W' y)
    (hc : HasFDerivAt c c' y) :
    ∃ g' : E →L[ℝ] Matrix m n ℝ, HasFDerivAt (fun z => f (h z * R z + b z) * W z + c z) g' y ∧
      ∀ v, g' v = fderiv ℝ f (h y * R y + b y) (h' v * R y + h y * R' v + b' v) * W y
        + f (h y * R y + b y) * W' v + c' v := by
  -- the argument `h R + b` of `f`, then the chain rule through `f`
  obtain ⟨z', hz, hzv⟩ := hasFDerivAt_mul_add_swb hh hR hb
  have hfz : HasFDerivAt (fun z => f (h z * R z + b z)) ((fderiv ℝ f (h y * R y + b y)).comp z')
      y := hf.hasFDerivAt.comp y hz
  -- the product with `W` and the sum with `c`
  obtain ⟨g', hg, hgv⟩ := hasFDerivAt_mul_add_swb hfz hW hc
  refine ⟨g', hg, fun v => ?_⟩
  rw [hgv, ContinuousLinearMap.comp_apply, hzv]

/-- Helper: the derivative of `z ↦ (∑_ℓ F_ℓ(z)) M(z)`. -/
private theorem hasFDerivAt_sum_mul_swb {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι m n q : Type*} [Fintype ι] [Fintype m] [Fintype n] [Fintype q]
    {F : ι → E → Matrix m n ℝ} {F' : ι → E →L[ℝ] Matrix m n ℝ} {M : E → Matrix n q ℝ}
    {M' : E →L[ℝ] Matrix n q ℝ} {y : E} (hF : ∀ i, HasFDerivAt (F i) (F' i) y)
    (hM : HasFDerivAt M M' y) :
    ∃ g' : E →L[ℝ] Matrix m q ℝ, HasFDerivAt (fun z => (∑ i, F i z) * M z) g' y ∧
      ∀ v, g' v = (∑ i, F' i v) * M y + (∑ i, F i y) * M' v := by
  have hs : HasFDerivAt (fun z => ∑ i, F i z) (∑ i, F' i) y :=
    HasFDerivAt.fun_sum fun i _ => hF i
  obtain ⟨g', hg, hgv⟩ := hasFDerivAt_mul_swb hs hM
  refine ⟨g', hg, fun v => ?_⟩
  rw [hgv, _root_.sum_apply]

/-! ### Helpers for the rank: the maps of the small-parameter lemma -/

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the embedding of a difference of weights. -/
@[simp] private theorem params_sub_E_swb (u w : Params A dIn dOut) : (u - w).E = u.E - w.E :=
  rfl

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
@[simp] private theorem params_sub_read_swb (u w : Params A dIn dOut) (ℓ : Fin L) :
    (u - w).read ℓ = u.read ℓ - w.read ℓ := rfl

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
@[simp] private theorem params_sub_write_swb (u w : Params A dIn dOut) (ℓ : Fin L) :
    (u - w).write ℓ = u.write ℓ - w.write ℓ := rfl

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
@[simp] private theorem params_sub_D_swb (u w : Params A dIn dOut) : (u - w).D = u.D - w.D :=
  rfl

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the embedding bias of a difference of biases. -/
@[simp] private theorem biases_sub_E_swb (u w : Biases A dOut) : (u - w).E = u.E - w.E := rfl

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
@[simp] private theorem biases_sub_read_swb (u w : Biases A dOut) (ℓ : Fin L) :
    (u - w).read ℓ = u.read ℓ - w.read ℓ := rfl

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
@[simp] private theorem biases_sub_write_swb (u w : Biases A dOut) (ℓ : Fin L) :
    (u - w).write ℓ = u.write ℓ - w.write ℓ := rfl

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
@[simp] private theorem biases_sub_D_swb (u w : Biases A dOut) : (u - w).D = u.D - w.D := rfl

/-- Helper: the part `π η` of a direction that the small-parameter lemma divides by `τ`: the
reads, the writes, the read biases and the write biases, as a linear map. -/
private def linPi_swb : ParamsB A dIn dOut →ₗ[ℝ] ParamsB A dIn dOut where
  toFun η := (⟨0, η.1.read, η.1.write, 0⟩, ⟨0, η.2.read, η.2.write, 0⟩)
  map_add' _ _ := Prod.ext
    (Params.ext' (add_zero 0).symm (fun _ => rfl) (fun _ => rfl) (add_zero 0).symm)
    (Biases.ext' (add_zero 0).symm (fun _ => rfl) (fun _ => rfl) (add_zero 0).symm)
  map_smul' c _ := Prod.ext
    (Params.ext' (smul_zero c).symm (fun _ => rfl) (fun _ => rfl) (smul_zero c).symm)
    (Biases.ext' (smul_zero c).symm (fun _ => rfl) (fun _ => rfl) (smul_zero c).symm)

/-- Helper: `π` as a continuous linear map. -/
private noncomputable def clmPi_swb : ParamsB A dIn dOut →L[ℝ] ParamsB A dIn dOut :=
  LinearMap.toContinuousLinearMap (linPi_swb A)

omit [Fintype T] [DecidableEq d] in
@[simp] private theorem clmPi_swb_apply (η : ParamsB A dIn dOut) :
    clmPi_swb A η = (⟨0, η.1.read, η.1.write, 0⟩, ⟨0, η.2.read, η.2.write, 0⟩) := rfl

/-- Helper: the writes and the write biases `q ↦ ((0, 0, W_write, 0), (0, 0, b_write, 0))`, as a
linear map. -/
private def linW_swb : ParamsB A dIn dOut →ₗ[ℝ] ParamsB A dIn dOut where
  toFun q := (⟨0, fun _ => 0, q.1.write, 0⟩, ⟨0, fun _ => 0, q.2.write, 0⟩)
  map_add' _ _ := Prod.ext
    (Params.ext' (add_zero 0).symm (fun _ => (add_zero 0).symm) (fun _ => rfl) (add_zero 0).symm)
    (Biases.ext' (add_zero 0).symm (fun _ => (add_zero 0).symm) (fun _ => rfl) (add_zero 0).symm)
  map_smul' c _ := Prod.ext
    (Params.ext' (smul_zero c).symm (fun _ => (smul_zero c).symm) (fun _ => rfl)
      (smul_zero c).symm)
    (Biases.ext' (smul_zero c).symm (fun _ => (smul_zero c).symm) (fun _ => rfl)
      (smul_zero c).symm)

/-- Helper: `q ↦ q_τ` as a linear map, for a fixed `τ`. -/
private def linSmall_swb (τ : ℝ) : ParamsB A dIn dOut →ₗ[ℝ] ParamsB A dIn dOut where
  toFun q := smallWritesB q τ
  map_add' _ _ := Prod.ext (Params.ext' rfl (fun _ => rfl) (fun _ => smul_add τ _ _) rfl)
    (Biases.ext' rfl (fun _ => rfl) (fun _ => smul_add τ _ _) rfl)
  map_smul' c _ := Prod.ext (Params.ext' rfl (fun _ => rfl) (fun _ => smul_comm τ c _) rfl)
    (Biases.ext' rfl (fun _ => rfl) (fun _ => smul_comm τ c _) rfl)

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: `q_τ = (q - W q) + τ W q`, with `W q` the writes and the write biases of `q`. -/
private theorem smallWritesB_eq_swb (τ : ℝ) (q : ParamsB A dIn dOut) :
    smallWritesB q τ = (q - linW_swb A q) + τ • linW_swb A q := by
  refine Prod.ext (Params.ext' ?_ (fun ℓ => ?_) (fun ℓ => ?_) ?_)
    (Biases.ext' ?_ (fun ℓ => ?_) (fun ℓ => ?_) ?_) <;>
  simp only [smallWritesB_E_swb, smallWritesB_read_swb, smallWritesB_write_swb,
    smallWritesB_D_swb, smallWritesB_bE_swb, smallWritesB_bread_swb, smallWritesB_bwrite_swb,
    smallWritesB_bD_swb, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst,
    Prod.smul_snd, Params.add_E, Params.add_read, Params.add_write, Params.add_D, Params.smul_E,
    Params.smul_read, Params.smul_write, Params.smul_D, Biases.add_E, Biases.add_read,
    Biases.add_write, Biases.add_D, Biases.smul_E, Biases.smul_read, Biases.smul_write,
    Biases.smul_D, params_sub_E_swb, params_sub_read_swb, params_sub_write_swb, params_sub_D_swb,
    biases_sub_E_swb, biases_sub_read_swb, biases_sub_write_swb, biases_sub_D_swb, linW_swb,
    LinearMap.coe_mk, AddHom.coe_mk, sub_zero, smul_zero, add_zero, sub_self, zero_add]

/-- Helper: `η ↦ J_0 η` at one input `x` is linear in `η`. -/
private noncomputable def limitLin_swb (x : Matrix T dIn ℝ) :
    ParamsB A dIn dOut →ₗ[ℝ] Matrix T dOut ℝ where
  toFun η := smallWritesLimitB A p η x
  map_add' η η' := by
    simp only [smallWritesLimitB, Prod.fst_add, Prod.snd_add, Params.add_E, Params.add_D,
      Params.add_read, Params.add_write, Biases.add_E, Biases.add_D, Biases.add_read,
      Biases.add_write, Matrix.add_mul, Matrix.mul_add, Matrix.add_vecMul, Matrix.vecMul_add,
      of_row_add_swb, map_add, Finset.sum_add_distrib]
    abel
  map_smul' c η := by
    simp only [smallWritesLimitB, Prod.smul_fst, Prod.smul_snd, Params.smul_E, Params.smul_D,
      Params.smul_read, Params.smul_write, Biases.smul_E, Biases.smul_D, Biases.smul_read,
      Biases.smul_write, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_vecMul,
      Matrix.vecMul_smul, Matrix.add_mul, Matrix.mul_add, of_row_add_swb, of_row_smul_swb,
      of_row_sum_swb, map_add, map_smul, Finset.smul_sum, smul_add, Finset.sum_add_distrib,
      RingHom.id_apply]

/-- Helper (kernel stabilisation): for a family of linear maps on a finite-dimensional space,
finitely many of them have the common kernel of all of them. -/
private theorem exists_batch_ker_swb {ι P F : Type*} [AddCommGroup P] [Module ℝ P]
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

/-- **Proof of Lemma A.27, "The rank", with biases, for real-analytic blocks without
normalization:** if every direction of weights and biases that is flat for `J_0` lies in a
subspace `V`, then for all small `τ ≠ 0` the residual network has `fd(θ_τ) ≥ P − dim V`, with `P`
counting the biases. -/
theorem eventually_funDimB_smallWritesB_ge (hA : A.χ = id)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ)
    (V : Submodule ℝ (ParamsB A dIn dOut))
    (hV : ∀ η : ParamsB A dIn dOut, (∀ x, smallWritesLimitB A p η x = 0) → η ∈ V) :
    ∀ᶠ τ in 𝓝[≠] (0 : ℝ),
      Module.finrank ℝ (ParamsB A dIn dOut)
        ≤ funDimB A 1 (smallWritesB p τ) + Module.finrank ℝ V := by
  -- the maps `f_ℓ` are differentiable, and `χ = id` is analytic
  have hfd : ∀ ℓ, Differentiable ℝ (A.f ℓ) := fun ℓ z =>
    ((hf ℓ) z (Set.mem_univ z)).differentiableAt
  have hχ : AnalyticOnNhd ℝ A.χ Set.univ := by
    rw [hA]
    exact analyticOnNhd_id
  -- (b) a finite batch `X` on which the flat directions of `J_0` are decided
  obtain ⟨n, X, hX⟩ := exists_batch_ker_swb (limitLin_swb A p)
  -- the outputs on the batch are analytic, hence `C²`, in the weights and biases
  have hev : ∀ i, AnalyticOnNhd ℝ
      (fun q : ParamsB A dIn dOut => evalB A 1 q.1 q.2 (X i)) Set.univ :=
    fun i => analyticOnNhd_evalB_params A 1 hf hχ (X i)
  have hEvC : ContDiff ℝ 2
      (evalBatchB A 1 X : ParamsB A dIn dOut → Fin n → Matrix T dOut ℝ) :=
    contDiff_pi.2 fun i => (hev i).contDiff
  -- `G τ q` is the batch of outputs at `q_τ`
  set G : ℝ → ParamsB A dIn dOut → (Fin n → Matrix T dOut ℝ) :=
    fun τ q => evalBatchB A 1 X (smallWritesB q τ) with hGdef
  -- (d) `(τ, q) ↦ G τ q` is `C²`: `q_τ = (q - W q) + τ W q` is smooth in `(τ, q)`
  have hG : ContDiff ℝ 2 (fun r : ℝ × ParamsB A dIn dOut => G r.1 r.2) := by
    let W := LinearMap.toContinuousLinearMap (linW_swb A (dIn := dIn) (dOut := dOut))
    have hS : ContDiff ℝ 2 (fun r : ℝ × ParamsB A dIn dOut => (r.2 - W r.2) + r.1 • W r.2) :=
      (contDiff_snd.sub (W.contDiff.comp contDiff_snd)).add
        (contDiff_fst.smul (W.contDiff.comp contDiff_snd))
    have hc := hEvC.comp hS
    have hfun : (fun r : ℝ × ParamsB A dIn dOut => G r.1 r.2)
        = evalBatchB A 1 X ∘ (fun r : ℝ × ParamsB A dIn dOut => (r.2 - W r.2) + r.1 • W r.2) := by
      funext r
      show evalBatchB A 1 X (smallWritesB r.2 r.1)
        = evalBatchB A 1 X ((r.2 - W r.2) + r.1 • W r.2)
      rw [smallWritesB_eq_swb A r.1 r.2]
      rfl
    rw [hfun]
    exact hc
  -- step 1: `G 0 q = ((X_i E' + b'_E) D' + b'_D)_i`;
  -- step 2: `∂_τ G(0, q) = ((∑_ℓ f_ℓ((X_i E' + b'_E) W'_read + b'_read) W'_write + b'_write) D')_i`
  have hG0 : G 0 = fun q i =>
      (X i * q.1.E + Matrix.of fun _ => q.2.E) * q.1.D + Matrix.of fun _ => q.2.D := by
    funext q i
    exact evalB_smallWritesB_zero A q hA (X i)
  have hG1 : (fun q => deriv (fun τ => G τ q) 0)
      = fun q i => (∑ ℓ, (A.f ℓ ((X i * q.1.E + Matrix.of fun _ => q.2.E) * q.1.read ℓ
            + Matrix.of fun _ => q.2.read ℓ) * q.1.write ℓ
          + Matrix.of fun _ => q.2.write ℓ)) * q.1.D := by
    funext q
    have hd : HasDerivAt (fun τ => G τ q)
        (fun i => (∑ ℓ, (A.f ℓ ((X i * q.1.E + Matrix.of fun _ => q.2.E) * q.1.read ℓ
            + Matrix.of fun _ => q.2.read ℓ) * q.1.write ℓ
          + Matrix.of fun _ => q.2.write ℓ)) * q.1.D) 0 :=
      hasDerivAt_pi.2 fun i => hasDerivAt_evalB_smallWritesB A q hA hfd (X i)
    exact hd.deriv
  -- the components of the weights and biases are linear in `q`, and so is `q ↦ x E' + b'_E`
  choose h' hh hh' using fun x : Matrix T dIn ℝ =>
    hasFDerivAt_lin_swb (fun q : ParamsB A dIn dOut => x * q.1.E + Matrix.of fun _ => q.2.E)
      (fun u v => by
        show x * (u.1.E + v.1.E) + (Matrix.of fun _ : T => u.2.E + v.2.E)
          = (x * u.1.E + Matrix.of fun _ : T => u.2.E) + (x * v.1.E + Matrix.of fun _ => v.2.E)
        rw [Matrix.mul_add, of_row_add_swb]
        abel)
      (fun c u => by
        show x * (c • u.1.E) + (Matrix.of fun _ : T => c • u.2.E)
          = c • (x * u.1.E + Matrix.of fun _ : T => u.2.E)
        rw [Matrix.mul_smul, of_row_smul_swb, smul_add]) p
  choose R' hR hR' using fun ℓ => hasFDerivAt_lin_swb
    (fun q : ParamsB A dIn dOut => q.1.read ℓ) (fun _ _ => rfl) (fun _ _ => rfl) p
  choose bR' hbR hbR' using fun ℓ => hasFDerivAt_lin_swb
    (fun q : ParamsB A dIn dOut => Matrix.of fun _ : T => q.2.read ℓ) (fun _ _ => rfl)
    (fun _ _ => rfl) p
  choose W' hW hW' using fun ℓ => hasFDerivAt_lin_swb
    (fun q : ParamsB A dIn dOut => q.1.write ℓ) (fun _ _ => rfl) (fun _ _ => rfl) p
  choose bW' hbW hbW' using fun ℓ => hasFDerivAt_lin_swb
    (fun q : ParamsB A dIn dOut => Matrix.of fun _ : T => q.2.write ℓ) (fun _ _ => rfl)
    (fun _ _ => rfl) p
  obtain ⟨D', hD, hD'⟩ := hasFDerivAt_lin_swb
    (fun q : ParamsB A dIn dOut => q.1.D) (fun _ _ => rfl) (fun _ _ => rfl) p
  obtain ⟨bD', hbD, hbD'⟩ := hasFDerivAt_lin_swb
    (fun q : ParamsB A dIn dOut => Matrix.of fun _ : T => q.2.D) (fun _ _ => rfl)
    (fun _ _ => rfl) p
  -- the derivatives of `G 0` and of `∂_τ G(0, ·)` at `p`, input by input
  choose a' ha ha' using fun i => hasFDerivAt_mul_add_swb (hh (X i)) hD hbD
  choose B hB hBv using fun i ℓ => hasFDerivAt_block_swb (A.f ℓ) ((hfd ℓ) _) (hh (X i)) (hR ℓ)
    (hbR ℓ) (hW ℓ) (hbW ℓ)
  choose b' hb hb' using fun i => hasFDerivAt_sum_mul_swb (hB i) hD
  have hD0 : ∀ v, fderiv ℝ (G 0) p v = fun i => a' i v := by
    intro v
    have hd : HasFDerivAt (G 0) (ContinuousLinearMap.pi a') p := by
      rw [hG0]
      exact hasFDerivAt_pi.2 ha
    rw [hd.fderiv]
    rfl
  have hD1 : ∀ v, fderiv ℝ (fun q => deriv (fun τ => G τ q) 0) p v = fun i => b' i v := by
    intro v
    have hd : HasFDerivAt (fun q => deriv (fun τ => G τ q) 0) (ContinuousLinearMap.pi b') p := by
      rw [hG1]
      exact hasFDerivAt_pi.2 hb
    rw [hd.fderiv]
    rfl
  -- (e) `G 0` does not move along `π η`: it does not depend on the reads, the writes and their
  -- biases
  have h0 : ∀ η, fderiv ℝ (G 0) p (clmPi_swb A η) = 0 := by
    intro η
    rw [hD0]
    funext i
    simp only [ha', hh', hD', hbD', clmPi_swb_apply, Matrix.mul_zero, Matrix.zero_mul,
      of_row_zero_swb, add_zero, Pi.zero_apply]
  -- (f) the limit `D_q G(0, p)(η - π η) + D_q(∂_τ G(0, ·))(p)(π η)` is `(J_0 η)(X_i)`, so its
  -- kernel is flat for `J_0` on the batch, hence at every input, hence in `V`
  have hV' : ∀ η, fderiv ℝ (G 0) p (η - clmPi_swb A η)
      + fderiv ℝ (fun q => deriv (fun τ => G τ q) 0) p (clmPi_swb A η) = 0 → η ∈ V := by
    intro η hη
    rw [hD0, hD1] at hη
    apply hV
    refine hX η (fun i => ?_)
    have hi := congrFun hη i
    simp only [Pi.add_apply, Pi.zero_apply, ha', hb', hBv, hh', hR', hbR', hW', hbW', hD',
      hbD'] at hi
    show smallWritesLimitB A p η (X i) = 0
    refine Eq.trans ?_ hi
    simp only [smallWritesLimitB, Prod.fst_sub, Prod.snd_sub, params_sub_E_swb,
      params_sub_D_swb, biases_sub_E_swb, biases_sub_D_swb, clmPi_swb_apply, sub_zero,
      Matrix.mul_zero, Matrix.zero_mul, of_row_zero_swb, add_zero, zero_add, Matrix.mul_add,
      Matrix.add_mul, Matrix.sum_mul, Matrix.mul_assoc, of_row_mul_swb, of_row_add_swb,
      of_row_sum_swb, Finset.sum_add_distrib]
    abel
  -- (c) the small-parameter lemma
  have key := eventually_finrank_le_of_small_parameter G hG (clmPi_swb A) p h0 V hV'
  -- (g) `D_q G(τ, p) = J(p_τ) ∘ S_τ`, so its rank is at most `jacobianRankB` at `p_τ`, at most
  -- `fd(p_τ)`
  have hrank : ∀ τ, Module.finrank ℝ (LinearMap.range (fderiv ℝ (G τ) p).toLinearMap)
      ≤ funDimB A 1 (smallWritesB p τ) := by
    intro τ
    let S := LinearMap.toContinuousLinearMap (linSmall_swb A (dIn := dIn) (dOut := dOut) τ)
    have hEv : DifferentiableAt ℝ (evalBatchB A 1 X) (S p) :=
      differentiableAt_pi.2 fun i => (hev i _ (Set.mem_univ _)).differentiableAt
    have hcomp : HasFDerivAt (G τ) ((fderiv ℝ (evalBatchB A 1 X) (S p)).comp S) p := by
      have hc := hEv.hasFDerivAt.comp p S.hasFDerivAt
      exact hc
    rw [hcomp.fderiv]
    calc Module.finrank ℝ
          (LinearMap.range ((fderiv ℝ (evalBatchB A 1 X) (S p)).comp S).toLinearMap)
        ≤ Module.finrank ℝ (LinearMap.range (fderiv ℝ (evalBatchB A 1 X) (S p)).toLinearMap) :=
          Submodule.finrank_mono (LinearMap.range_comp_le_range _ _)
      _ = jacobianRankB A 1 X (smallWritesB p τ) := rfl
      _ ≤ funDimB A 1 (smallWritesB p τ) := jacobianRankB_le_funDimB _ X
  filter_upwards [key] with τ hτ
  exact hτ.trans (Nat.add_le_add_right (hrank τ) _)

end Skips
