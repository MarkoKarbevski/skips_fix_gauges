import SkipsLean.Residual.SmallWrites

/-!
# Residual networks with small writes, with a normalization

Paper (skips paper): proof of Lemma A.27, paragraph "Under pre-RMSNorm". At `θ_τ` every hidden
state is `x E + O(τ)` and every block reads `N_ε(x E) + O(τ)`, so the output is

  `y = N_ε(x E) D + τ 𝐃N_ε(x E) (g(N_ε(x E))) D + O(τ²)`,  `g(n) = ∑_ℓ f_ℓ(n W_read^ℓ) W_write^ℓ`,

and, with `h = x E` and `n = N_ε(h)`,

  `(J_0 η)(x) = 𝐃N_ε(h) (x η_E + D_θ g(n) η) D + N_ε(h) η_D`,

"where `D_θ g(n) η` is the derivative of the wide block at the input `n` along the entries of `η`
at its reads and writes".

This file states the expansion, the limit `J_0` and the paragraph "The rank" as
`Residual/SmallWrites.lean` does without normalization, for an arbitrary map `χ` in the place of
`N_ε` (differentiable, resp. real-analytic). For `χ = id` the limit below is `smallWritesLimit`.
-/

namespace Skips

open Matrix Filter Topology
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]

/-- **The limit `J_0` of the proof of Lemma A.27 under pre-RMSNorm, at one input `x`,** for a
map `χ` in the place of `N_ε`: `(J_0 η)(x) = 𝐃χ(h) (x η_E + D_θ g(n) η) D + χ(h) η_D` with
`h = x E`, `n = χ(h)` and
`D_θ g(n) η = ∑_ℓ (D f_ℓ(n W_read^ℓ)(n η_read^ℓ) W_write^ℓ + f_ℓ(n W_read^ℓ) η_write^ℓ)`. -/
noncomputable def smallWritesLimitNorm (A : Arch T d L) (θ η : Params A dIn dOut)
    (x : Matrix T dIn ℝ) : Matrix T dOut ℝ :=
  fderiv ℝ A.χ (x * θ.E)
      (x * η.E + ∑ ℓ, (fderiv ℝ (A.f ℓ) (A.χ (x * θ.E) * θ.read ℓ) (A.χ (x * θ.E) * η.read ℓ)
            * θ.write ℓ
          + A.f ℓ (A.χ (x * θ.E) * θ.read ℓ) * η.write ℓ)) * θ.D
    + A.χ (x * θ.E) * η.D

variable (A : Arch T d L) (θ : Params A dIn dOut)

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the embedding of `θ_τ` is that of `θ`. -/
@[simp] private theorem smallWrites_E_SN (τ : ℝ) : (θ.smallWrites τ).E = θ.E := rfl

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the reads of `θ_τ` are those of `θ`. -/
@[simp] private theorem smallWrites_read_SN (τ : ℝ) (ℓ : Fin L) :
    (θ.smallWrites τ).read ℓ = θ.read ℓ := rfl

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the writes of `θ_τ` are `τ W_write^ℓ`. -/
@[simp] private theorem smallWrites_write_SN (τ : ℝ) (ℓ : Fin L) :
    (θ.smallWrites τ).write ℓ = τ • θ.write ℓ := rfl

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the readout of `θ_τ` is that of `θ`. -/
@[simp] private theorem smallWrites_D_SN (τ : ℝ) : (θ.smallWrites τ).D = θ.D := rfl

omit [Fintype T] [Fintype dOut] in
/-- Helper: the residual step at `θ_τ`, `h_{k+1} = h_k + τ (f_k(χ(h_k) W_read^k) W_write^k)`. -/
private theorem hidden_smallWrites_succ_SN (x : Matrix T dIn ℝ) (τ : ℝ) (k : Fin L) :
    hidden A 1 (θ.smallWrites τ) x k.succ = hidden A 1 (θ.smallWrites τ) x k.castSucc
      + τ • (A.f k (A.χ (hidden A 1 (θ.smallWrites τ) x k.castSucc) * θ.read k) * θ.write k) := by
  rw [hidden_succ, Pi.one_apply, Matrix.mul_one, smallWrites_read_SN, smallWrites_write_SN,
    Matrix.mul_smul]

omit [Fintype T] [Fintype dOut] in
/-- Helper: at `τ = 0` every hidden state is `x E`. -/
private theorem hidden_smallWrites_zero_SN (x : Matrix T dIn ℝ) (k : Fin (L + 1)) :
    hidden A 1 (θ.smallWrites 0) x k = x * θ.E := by
  induction k using Fin.induction with
  | zero => rw [hidden_zero, smallWrites_E_SN]
  | succ k ih => rw [hidden_smallWrites_succ_SN A θ, ih, zero_smul, add_zero]

/-- At `τ = 0` the residual network computes `x ↦ χ(x E) D`
(proof of Lemma A.27 under pre-RMSNorm: "`y = N_ε(x E) D + τ (…) + O(τ²)`"). -/
theorem eval_smallWrites_zero_norm (x : Matrix T dIn ℝ) :
    eval A 1 (θ.smallWrites 0) x = A.χ (x * θ.E) * θ.D := by
  rw [eval, hidden_smallWrites_zero_SN A θ x, smallWrites_D_SN]

/-- Helper: the derivative at `0` of `τ ↦ τ g(τ)`, for `g` continuous at `0`, is `g(0)`. -/
private theorem hasDerivAt_smul_self_SN {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g : ℝ → F} (hg : ContinuousAt g 0) : HasDerivAt (fun τ : ℝ => τ • g τ) (g 0) 0 := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  refine Tendsto.congr' ?_ (hg.tendsto.mono_left nhdsWithin_le_nhds)
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [zero_add, zero_smul, sub_zero, smul_smul, inv_mul_cancel₀ ht, one_smul]

/-- Helper: a sum over the blocks before `k + 1` is the sum over the blocks before `k` plus the
term of block `k`. -/
private theorem sum_ite_lt_succ_SN {M : Type*} [AddCommMonoid M] {m : ℕ} (a : Fin m → M)
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
private theorem continuous_hidden_smallWrites_SN (hχ : Continuous A.χ)
    (hf : ∀ ℓ, Continuous (A.f ℓ)) (x : Matrix T dIn ℝ) (k : Fin (L + 1)) :
    Continuous (fun τ : ℝ => hidden A 1 (θ.smallWrites τ) x k) := by
  induction k using Fin.induction with
  | zero =>
    simp only [hidden_zero, smallWrites_E_SN]
    exact continuous_const
  | succ k ih =>
    simp only [hidden_smallWrites_succ_SN A θ]
    exact ih.add (continuous_id.smul
      (((hf k).comp ((hχ.comp ih).matrix_mul continuous_const)).matrix_mul continuous_const))

omit [Fintype dOut] in
/-- Helper: the derivative at `τ = 0` of the hidden state `h_k` at `θ_τ` is the sum over the
blocks `ℓ < k` of `f_ℓ(χ(x E) W_read^ℓ) W_write^ℓ`. -/
private theorem hasDerivAt_hidden_smallWrites_SN (hχ : Continuous A.χ)
    (hf : ∀ ℓ, Continuous (A.f ℓ)) (x : Matrix T dIn ℝ) (k : Fin (L + 1)) :
    HasDerivAt (fun τ : ℝ => hidden A 1 (θ.smallWrites τ) x k)
      (∑ ℓ : Fin L, if (ℓ : ℕ) < (k : ℕ)
        then A.f ℓ (A.χ (x * θ.E) * θ.read ℓ) * θ.write ℓ else 0) 0 := by
  induction k using Fin.induction with
  | zero =>
    -- `h_0 = x E` does not depend on `τ`
    simp only [hidden_zero, smallWrites_E_SN, Fin.val_zero, Nat.not_lt_zero, ite_false,
      Finset.sum_const_zero]
    exact hasDerivAt_const _ _
  | succ k ih =>
    -- `h_{k+1}(τ) = h_k(τ) + τ g(τ)`, and the derivative of `τ g(τ)` at `0` is `g(0)`
    simp only [hidden_smallWrites_succ_SN A θ]
    have hg : ContinuousAt (fun τ : ℝ =>
        A.f k (A.χ (hidden A 1 (θ.smallWrites τ) x k.castSucc) * θ.read k) * θ.write k) 0 :=
      (((hf k).comp ((hχ.comp (continuous_hidden_smallWrites_SN A θ hχ hf x k.castSucc)).matrix_mul
        continuous_const)).matrix_mul continuous_const).continuousAt
    have h2 := ih.add (hasDerivAt_smul_self_SN hg)
    -- `g(0)` is the term of block `k` at `h_k(0) = x E`
    have hv : (∑ ℓ : Fin L, if (ℓ : ℕ) < (k.castSucc : ℕ)
          then A.f ℓ (A.χ (x * θ.E) * θ.read ℓ) * θ.write ℓ else 0)
        + A.f k (A.χ (hidden A 1 (θ.smallWrites 0) x k.castSucc) * θ.read k) * θ.write k
        = ∑ ℓ : Fin L, if (ℓ : ℕ) < (k.succ : ℕ)
          then A.f ℓ (A.χ (x * θ.E) * θ.read ℓ) * θ.write ℓ else 0 := by
      rw [hidden_smallWrites_zero_SN A θ, Fin.val_succ, Fin.val_castSucc]
      exact (sum_ite_lt_succ_SN (fun ℓ => A.f ℓ (A.χ (x * θ.E) * θ.read ℓ) * θ.write ℓ) k).symm
    rw [hv] at h2
    exact h2

/-- Helper: `y ↦ y M`, as a linear map. -/
private def mulRightLin_SN {m n p : Type*} [Fintype n] (M : Matrix n p ℝ) :
    Matrix m n ℝ →ₗ[ℝ] Matrix m p ℝ where
  toFun X := X * M
  map_add' X Y := Matrix.add_mul X Y M
  map_smul' c X := Matrix.smul_mul c X M

/-- Helper: `y ↦ y M`, as a continuous linear map. -/
private noncomputable def mulRightCLM_SN {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
    (M : Matrix n p ℝ) : Matrix m n ℝ →L[ℝ] Matrix m p ℝ :=
  LinearMap.toContinuousLinearMap (mulRightLin_SN M)

/-- **The term of order `τ` of the output at `θ_τ`, with a normalization** (proof of Lemma A.27
under pre-RMSNorm, the expansion of `y`): the derivative of `τ ↦ F_{θ_τ}(x)` at `τ = 0` is
`𝐃χ(x E) (∑_ℓ f_ℓ(χ(x E) W_read^ℓ) W_write^ℓ) D`. -/
theorem hasDerivAt_eval_smallWrites_norm (hχ : Differentiable ℝ A.χ)
    (hf : ∀ ℓ, Differentiable ℝ (A.f ℓ)) (x : Matrix T dIn ℝ) :
    HasDerivAt (fun τ : ℝ => eval A 1 (θ.smallWrites τ) x)
      (fderiv ℝ A.χ (x * θ.E) (∑ ℓ, A.f ℓ (A.χ (x * θ.E) * θ.read ℓ) * θ.write ℓ) * θ.D) 0 := by
  -- the derivative of the last hidden state: every block is before `L`
  have hL := hasDerivAt_hidden_smallWrites_SN A θ hχ.continuous (fun ℓ => (hf ℓ).continuous) x
    (Fin.last L)
  have hsum : (∑ ℓ : Fin L, if (ℓ : ℕ) < ((Fin.last L : Fin (L + 1)) : ℕ)
      then A.f ℓ (A.χ (x * θ.E) * θ.read ℓ) * θ.write ℓ else 0)
        = ∑ ℓ, A.f ℓ (A.χ (x * θ.E) * θ.read ℓ) * θ.write ℓ :=
    Finset.sum_congr rfl fun ℓ _ => by simp only [Fin.val_last, ℓ.isLt, ↓reduceIte]
  rw [hsum] at hL
  -- the chain rule through `χ` at `h_L(0) = x E`
  have hχx : HasFDerivAt A.χ (fderiv ℝ A.χ (x * θ.E)) (x * θ.E) := (hχ _).hasFDerivAt
  have h1 := hχx.comp_hasDerivAt_of_eq (0 : ℝ) hL
    (hidden_smallWrites_zero_SN A θ x (Fin.last L)).symm
  -- the output is `χ(h_L) D`, and `y ↦ y D` is linear
  have hc := (mulRightCLM_SN (m := T) θ.D).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
  simp only [eval, smallWrites_D_SN]
  exact hc

/-! ### Helpers for the rank: derivatives in the parameters -/

/-- Helper: matrix multiplication as a continuous bilinear map. -/
private noncomputable def mulB_SN (m n p : Type*) [Fintype m] [Fintype n] [Fintype p] :
    Matrix m n ℝ →L[ℝ] Matrix n p ℝ →L[ℝ] Matrix m p ℝ :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap :
      (Matrix n p ℝ →ₗ[ℝ] Matrix m p ℝ) ≃ₗ[ℝ] (Matrix n p ℝ →L[ℝ] Matrix m p ℝ)).toLinearMap ∘ₗ
      LinearMap.mk₂ ℝ (fun a b => a * b) Matrix.add_mul (fun c a b => Matrix.smul_mul c a b)
        Matrix.mul_add (fun c a b => Matrix.mul_smul a c b))

/-- Helper: the product rule for matrix-valued maps, with the value of the derivative,
`(f g)' v = f' v g + f g' v`. -/
private theorem hasFDerivAt_mul_SN {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m n p : Type*} [Fintype m] [Fintype n] [Fintype p] {f : E → Matrix m n ℝ}
    {g : E → Matrix n p ℝ} {f' : E →L[ℝ] Matrix m n ℝ} {g' : E →L[ℝ] Matrix n p ℝ} {y : E}
    (hf : HasFDerivAt f f' y) (hg : HasFDerivAt g g' y) :
    ∃ h' : E →L[ℝ] Matrix m p ℝ, HasFDerivAt (fun z => f z * g z) h' y ∧
      ∀ v, h' v = f' v * g y + f y * g' v := by
  -- the derivative of the bilinear map `(a, b) ↦ a b` along `(f, g)`
  have h := (mulB_SN m n p).hasFDerivAt_of_bilinear hf hg
  refine ⟨_, h, fun v => ?_⟩
  show f y * g' v + f' v * g y = _
  exact add_comm _ _

/-- Helper: the product rule for matrix-valued maps of a real number,
`(f g)' = f' g + f g'`. -/
private theorem hasDerivAt_mul_SN {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
    {f : ℝ → Matrix m n ℝ} {g : ℝ → Matrix n p ℝ} {f' : Matrix m n ℝ} {g' : Matrix n p ℝ}
    {s : ℝ} (hf : HasDerivAt f f' s) (hg : HasDerivAt g g' s) :
    HasDerivAt (fun z => f z * g z) (f' * g s + f s * g') s := by
  obtain ⟨h', hh, hv⟩ := hasFDerivAt_mul_SN hf.hasFDerivAt hg.hasFDerivAt
  refine hh.hasDerivAt.congr_deriv ?_
  rw [hv, ContinuousLinearMap.toSpanSingleton_apply_one,
    ContinuousLinearMap.toSpanSingleton_apply_one]

/-- Helper: the embedding, as a continuous linear map of the parameters. -/
private noncomputable def clmE_SN : Params A dIn dOut →L[ℝ] Matrix dIn d ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun θ' => θ'.E, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }

/-- Helper: the readout, as a continuous linear map of the parameters. -/
private noncomputable def clmD_SN : Params A dIn dOut →L[ℝ] Matrix d dOut ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun θ' => θ'.D, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }

omit [Fintype T] [DecidableEq d] in
@[simp] private theorem clmE_SN_apply (v : Params A dIn dOut) : clmE_SN A v = v.E := rfl

omit [Fintype T] [DecidableEq d] in
@[simp] private theorem clmD_SN_apply (v : Params A dIn dOut) : clmD_SN A v = v.D := rfl

omit [DecidableEq d] in
/-- Helper: the derivative of `θ' ↦ χ(x E') D'` at `θ` along `v` is
`𝐃χ(x E)(x v_E) D + χ(x E) v_D` (chain rule and product rule). -/
private theorem hasFDerivAt_chiED_SN (hχ : Differentiable ℝ A.χ) (x : Matrix T dIn ℝ) :
    ∃ g' : Params A dIn dOut →L[ℝ] Matrix T dOut ℝ,
      HasFDerivAt (fun θ' : Params A dIn dOut => A.χ (x * θ'.E) * θ'.D) g' θ ∧
        ∀ v, g' v = fderiv ℝ A.χ (x * θ.E) (x * v.E) * θ.D + A.χ (x * θ.E) * v.D := by
  -- `θ' ↦ x E'`
  obtain ⟨a', ha, hav⟩ := hasFDerivAt_mul_SN (hasFDerivAt_const x θ) (clmE_SN A).hasFDerivAt
  have hxE : HasFDerivAt (fun θ' : Params A dIn dOut => x * θ'.E) a' θ := ha
  -- the chain rule through `χ`
  have hχx : HasFDerivAt A.χ (fderiv ℝ A.χ (x * θ.E)) (x * θ.E) := (hχ _).hasFDerivAt
  have hc := hχx.comp θ hxE
  have hc' : HasFDerivAt (fun θ' : Params A dIn dOut => A.χ (x * θ'.E))
      ((fderiv ℝ A.χ (x * θ.E)).comp a') θ := hc
  -- the product with `D'`
  obtain ⟨b', hb, hbv⟩ := hasFDerivAt_mul_SN hc' (clmD_SN A).hasFDerivAt
  refine ⟨b', hb, fun v => ?_⟩
  rw [hbv, ContinuousLinearMap.comp_apply, hav]
  simp only [clmE_SN_apply, clmD_SN_apply, _root_.zero_apply, Matrix.zero_mul, zero_add]

omit [DecidableEq d] in
/-- Helper: along a line in the read and the write of block `ℓ`, at a fixed input `n`, the
derivative at `0` of `s ↦ f_ℓ(n (R + s R')) (W + s W')` is `𝐃f_ℓ(n R)(n R') W + f_ℓ(n R) W'`. -/
private theorem hasDerivAt_block_line_SN (hf : ∀ ℓ, Differentiable ℝ (A.f ℓ))
    (n : Matrix T d ℝ) (ℓ : Fin L) (R R' : Matrix d (A.r ℓ) ℝ) (W W' : Matrix (A.w ℓ) d ℝ) :
    HasDerivAt (fun s : ℝ => A.f ℓ (n * (R + s • R')) * (W + s • W'))
      (fderiv ℝ (A.f ℓ) (n * R) (n * R') * W + A.f ℓ (n * R) * W') 0 := by
  -- the lines `s ↦ R + s R'` and `s ↦ W + s W'`
  have hR : HasDerivAt (fun s : ℝ => R + s • R') ((1 : ℝ) • R') 0 :=
    ((hasDerivAt_id' (0 : ℝ)).smul_const R').const_add R
  have hW : HasDerivAt (fun s : ℝ => W + s • W') ((1 : ℝ) • W') 0 :=
    ((hasDerivAt_id' (0 : ℝ)).smul_const W').const_add W
  -- `s ↦ n (R + s R')`
  have hnR : HasDerivAt (fun s : ℝ => n * (R + s • R')) (n * R') 0 := by
    refine (hasDerivAt_mul_SN (hasDerivAt_const (0 : ℝ) n) hR).congr_deriv ?_
    rw [Matrix.zero_mul, zero_add, one_smul]
  -- the chain rule through `f_ℓ`
  have hfl : HasFDerivAt (A.f ℓ) (fderiv ℝ (A.f ℓ) (n * R)) (n * R) := (hf ℓ _).hasFDerivAt
  have hc := hfl.comp_hasDerivAt_of_eq (0 : ℝ) hnR (by rw [zero_smul, add_zero])
  -- the product with the write
  have hp := hasDerivAt_mul_SN hc hW
  refine hp.congr_deriv ?_
  simp only [Function.comp_apply, zero_smul, add_zero, one_smul]
  rfl

/-! ### Helpers for the rank: the maps of the small-parameter lemma -/

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the components of a difference of parameters. -/
@[simp] private theorem sub_E_SN (v w : Params A dIn dOut) : (v - w).E = v.E - w.E := rfl

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
@[simp] private theorem sub_D_SN (v w : Params A dIn dOut) : (v - w).D = v.D - w.D := rfl

/-- Helper: the part `π η = (0, η_read, η_write, 0)` of a direction that the small-parameter lemma
divides by `τ`, as a linear map. -/
private def linPi_SN : Params A dIn dOut →ₗ[ℝ] Params A dIn dOut where
  toFun η := ⟨0, η.read, η.write, 0⟩
  map_add' _ _ := Params.ext' (add_zero 0).symm (fun _ => rfl) (fun _ => rfl) (add_zero 0).symm
  map_smul' c _ := Params.ext' (smul_zero c).symm (fun _ => rfl) (fun _ => rfl) (smul_zero c).symm

/-- Helper: `π` as a continuous linear map. -/
private noncomputable def clmPi_SN : Params A dIn dOut →L[ℝ] Params A dIn dOut :=
  LinearMap.toContinuousLinearMap (linPi_SN A)

omit [Fintype T] [DecidableEq d] in
@[simp] private theorem clmPi_SN_E (η : Params A dIn dOut) : (clmPi_SN A η).E = 0 := rfl

omit [Fintype T] [DecidableEq d] in
@[simp] private theorem clmPi_SN_read (η : Params A dIn dOut) (ℓ : Fin L) :
    (clmPi_SN A η).read ℓ = η.read ℓ := rfl

omit [Fintype T] [DecidableEq d] in
@[simp] private theorem clmPi_SN_write (η : Params A dIn dOut) (ℓ : Fin L) :
    (clmPi_SN A η).write ℓ = η.write ℓ := rfl

omit [Fintype T] [DecidableEq d] in
@[simp] private theorem clmPi_SN_D (η : Params A dIn dOut) : (clmPi_SN A η).D = 0 := rfl

/-- Helper: the writes `η ↦ (0, 0, η_write, 0)`, as a linear map. -/
private def linW_SN : Params A dIn dOut →ₗ[ℝ] Params A dIn dOut where
  toFun η := ⟨0, fun _ => 0, η.write, 0⟩
  map_add' _ _ := Params.ext' (add_zero 0).symm (fun _ => (add_zero 0).symm) (fun _ => rfl)
    (add_zero 0).symm
  map_smul' c _ := Params.ext' (smul_zero c).symm (fun _ => (smul_zero c).symm) (fun _ => rfl)
    (smul_zero c).symm

/-- Helper: `θ' ↦ θ'_τ` as a linear map, for a fixed `τ`. -/
private def linSmall_SN (τ : ℝ) : Params A dIn dOut →ₗ[ℝ] Params A dIn dOut where
  toFun θ' := θ'.smallWrites τ
  map_add' _ _ := Params.ext' rfl (fun _ => rfl) (fun _ => smul_add τ _ _) rfl
  map_smul' c _ := Params.ext' rfl (fun _ => rfl) (fun _ => smul_comm τ c _) rfl

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: `θ'_τ = (θ' - W θ') + τ W θ'`, with `W θ' = (0, 0, θ'_write, 0)`. -/
private theorem smallWrites_eq_SN (τ : ℝ) (θ' : Params A dIn dOut) :
    θ'.smallWrites τ = (θ' - linW_SN A θ') + τ • linW_SN A θ' := by
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
private noncomputable def limitLin_SN (x : Matrix T dIn ℝ) :
    Params A dIn dOut →ₗ[ℝ] Matrix T dOut ℝ where
  toFun η := smallWritesLimitNorm A θ η x
  map_add' η η' := by
    simp only [smallWritesLimitNorm, Params.add_E, Params.add_D, Params.add_read,
      Params.add_write, Matrix.add_mul, Matrix.mul_add, map_add, Finset.sum_add_distrib]
    abel
  map_smul' c η := by
    simp only [smallWritesLimitNorm, Params.smul_E, Params.smul_D, Params.smul_read,
      Params.smul_write, Matrix.smul_mul, Matrix.mul_smul, map_smul, ← Finset.smul_sum,
      ← smul_add, RingHom.id_apply]

/-- Helper (kernel stabilisation): for a family of linear maps on a finite-dimensional space,
finitely many of them have the common kernel of all of them. -/
private theorem exists_batch_ker_SN {ι P F : Type*} [AddCommGroup P] [Module ℝ P]
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

/-- Helper: if `(τ, θ') ↦ G τ θ'` is `C²`, then `θ' ↦ ∂_τ G(0, θ')` is differentiable. -/
private theorem differentiableAt_deriv_SN {P Y : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (G : ℝ → P → Y)
    (hG : ContDiff ℝ 2 (fun p : ℝ × P => G p.1 p.2)) (θ : P) :
    DifferentiableAt ℝ (fun θ' => deriv (fun τ => G τ θ') 0) θ := by
  set F : ℝ × P → Y := fun p => G p.1 p.2 with hF
  have hFd : ∀ p, HasFDerivAt F (fderiv ℝ F p) p := fun p =>
    ((hG.differentiable (by norm_num)) p).hasFDerivAt
  have hA1 : ContDiff ℝ 1 (fderiv ℝ F) := hG.fderiv_right (by norm_num)
  -- `∂_τ G(0, θ') = D F(0, θ') (1, 0)`
  have h2 : (fun θ' => deriv (fun τ => G τ θ') 0) = fun θ' => fderiv ℝ F (0, θ') (1, 0) := by
    funext θ'
    have hin : HasDerivAt (fun τ : ℝ => (τ, θ')) ((1 : ℝ), (0 : P)) 0 :=
      (hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_const (0 : ℝ) θ')
    have hc := (hFd (0, θ')).comp_hasDerivAt (0 : ℝ) hin
    exact hc.deriv
  rw [h2]
  -- `θ' ↦ D F(0, θ')` is differentiable, since `F` is `C²`
  have hin : DifferentiableAt ℝ (fun θ' : P => ((0 : ℝ), θ')) θ :=
    (differentiableAt_const _).prodMk differentiableAt_fun_id
  have hd := ((hA1.differentiable (by norm_num)) ((0 : ℝ), θ)).comp θ hin
  exact hd.clm_apply (differentiableAt_const _)

/-- Helper: the derivative of a differentiable map along `v` is the derivative at `0` of the map
on the line `s ↦ θ + s v`. -/
private theorem fderiv_apply_eq_of_line_SN {P Y : Type*} [NormedAddCommGroup P]
    [NormedSpace ℝ P] [NormedAddCommGroup Y] [NormedSpace ℝ Y] {Φ : P → Y} {θ v : P} {y : Y}
    (hΦ : DifferentiableAt ℝ Φ θ) (hl : HasDerivAt (fun s : ℝ => Φ (θ + s • v)) y 0) :
    fderiv ℝ Φ θ v = y := by
  have hline : HasDerivAt (fun s : ℝ => θ + s • v) ((1 : ℝ) • v) 0 :=
    ((hasDerivAt_id' (0 : ℝ)).smul_const v).const_add θ
  have hc := hΦ.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hline (by rw [zero_smul, add_zero])
  rw [one_smul] at hc
  exact hc.unique hl

/-- **Proof of Lemma A.27, "The rank", for real-analytic blocks and a real-analytic `χ`:** if
every direction that is flat for `J_0` lies in a subspace `V` of the parameters, then for all
small `τ ≠ 0` the residual network has `fd(θ_τ) ≥ P - dim V`. -/
theorem eventually_funDim_smallWrites_ge_norm (hχ : AnalyticOnNhd ℝ A.χ Set.univ)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (V : Submodule ℝ (Params A dIn dOut))
    (hV : ∀ η : Params A dIn dOut, (∀ x, smallWritesLimitNorm A θ η x = 0) → η ∈ V) :
    ∀ᶠ τ in 𝓝[≠] (0 : ℝ),
      Module.finrank ℝ (Params A dIn dOut)
        ≤ funDim A 1 (θ.smallWrites τ) + Module.finrank ℝ V := by
  -- the maps `f_ℓ` and `χ` are differentiable
  have hfd : ∀ ℓ, Differentiable ℝ (A.f ℓ) := fun ℓ z =>
    ((hf ℓ) z (Set.mem_univ z)).differentiableAt
  have hχd : Differentiable ℝ A.χ := fun z => (hχ z (Set.mem_univ z)).differentiableAt
  -- (b) a finite batch `X` on which the flat directions of `J_0` are decided
  obtain ⟨n, X, hX⟩ := exists_batch_ker_SN (limitLin_SN A θ (dOut := dOut))
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
    let W := LinearMap.toContinuousLinearMap (linW_SN A (dIn := dIn) (dOut := dOut))
    have hS : ContDiff ℝ 2 (fun p : ℝ × Params A dIn dOut => (p.2 - W p.2) + p.1 • W p.2) :=
      (contDiff_snd.sub (W.contDiff.comp contDiff_snd)).add
        (contDiff_fst.smul (W.contDiff.comp contDiff_snd))
    have hc := hEvC.comp hS
    have hfun : (fun p : ℝ × Params A dIn dOut => G p.1 p.2)
        = evalBatch A 1 X ∘ (fun p : ℝ × Params A dIn dOut => (p.2 - W p.2) + p.1 • W p.2) := by
      funext p
      show evalBatch A 1 X (p.2.smallWrites p.1) = evalBatch A 1 X ((p.2 - W p.2) + p.1 • W p.2)
      rw [smallWrites_eq_SN A p.1 p.2]
      rfl
    rw [hfun]
    exact hc
  -- step 1: `G 0 θ' = (χ(X_i E') D')_i`;
  -- step 2: `∂_τ G(0, θ') = (𝐃χ(X_i E')(∑_ℓ f_ℓ(χ(X_i E') W'_read) W'_write) D')_i`
  have hG0 : G 0 = fun θ' i => A.χ (X i * θ'.E) * θ'.D := by
    funext θ' i
    exact eval_smallWrites_zero_norm A θ' (X i)
  have hG1 : ∀ θ', deriv (fun τ => G τ θ') 0
      = fun i => fderiv ℝ A.χ (X i * θ'.E)
          (∑ ℓ, A.f ℓ (A.χ (X i * θ'.E) * θ'.read ℓ) * θ'.write ℓ) * θ'.D := by
    intro θ'
    have hd : HasDerivAt (fun τ => G τ θ') (fun i => fderiv ℝ A.χ (X i * θ'.E)
        (∑ ℓ, A.f ℓ (A.χ (X i * θ'.E) * θ'.read ℓ) * θ'.write ℓ) * θ'.D) 0 :=
      hasDerivAt_pi.2 fun i => hasDerivAt_eval_smallWrites_norm A θ' hχd hfd (X i)
    exact hd.deriv
  -- the derivative of `G 0` in the parameters at `θ`
  choose a' ha ha' using fun i => hasFDerivAt_chiED_SN A θ (dOut := dOut) hχd (X i)
  have hD0 : ∀ v, fderiv ℝ (G 0) θ v
      = fun i => fderiv ℝ A.χ (X i * θ.E) (X i * v.E) * θ.D + A.χ (X i * θ.E) * v.D := by
    intro v
    have hd : HasFDerivAt (G 0) (ContinuousLinearMap.pi a') θ := by
      rw [hG0]
      exact hasFDerivAt_pi.2 ha
    rw [hd.fderiv]
    funext i
    exact ha' i v
  -- the derivative of `∂_τ G(0, ·)` at `θ` along `π η`: on the line `θ + s π η` the embedding
  -- and the readout stay those of `θ`, so only the reads and the writes move
  have hD1 : ∀ η, fderiv ℝ (fun θ' => deriv (fun τ => G τ θ') 0) θ (clmPi_SN A η)
      = fun i => fderiv ℝ A.χ (X i * θ.E)
          (∑ ℓ, (fderiv ℝ (A.f ℓ) (A.χ (X i * θ.E) * θ.read ℓ) (A.χ (X i * θ.E) * η.read ℓ)
              * θ.write ℓ
            + A.f ℓ (A.χ (X i * θ.E) * θ.read ℓ) * η.write ℓ)) * θ.D := by
    intro η
    refine fderiv_apply_eq_of_line_SN (differentiableAt_deriv_SN G hG θ) ?_
    have he : ∀ s : ℝ, deriv (fun τ => G τ (θ + s • clmPi_SN A η)) 0
        = fun i => fderiv ℝ A.χ (X i * θ.E)
          (∑ ℓ, A.f ℓ (A.χ (X i * θ.E) * (θ.read ℓ + s • η.read ℓ))
            * (θ.write ℓ + s • η.write ℓ)) * θ.D := by
      intro s
      rw [hG1]
      simp only [Params.add_E, Params.smul_E, clmPi_SN_E, smul_zero, add_zero, Params.add_D,
        Params.smul_D, clmPi_SN_D, Params.add_read, Params.smul_read, clmPi_SN_read,
        Params.add_write, Params.smul_write, clmPi_SN_write]
    simp only [he]
    refine hasDerivAt_pi.2 fun i => ?_
    -- the sum over the blocks, then the linear maps `𝐃χ(X_i E)` and `y ↦ y D`
    have hs := HasDerivAt.fun_sum (u := Finset.univ) fun ℓ _ =>
      hasDerivAt_block_line_SN A hfd (A.χ (X i * θ.E)) ℓ (θ.read ℓ) (η.read ℓ) (θ.write ℓ)
        (η.write ℓ)
    have hc := (fderiv ℝ A.χ (X i * θ.E)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hs
    have hc2 := (mulRightCLM_SN (m := T) θ.D).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hc
    exact hc2
  -- (e) `G 0` does not move along `π η = (0, η_read, η_write, 0)`
  have h0 : ∀ η, fderiv ℝ (G 0) θ (clmPi_SN A η) = 0 := by
    intro η
    rw [hD0]
    funext i
    simp only [clmPi_SN_E, clmPi_SN_D, Matrix.mul_zero, map_zero, Matrix.zero_mul, add_zero,
      Pi.zero_apply]
  -- (f) the limit `D_θ G(0, θ)(η - π η) + D_θ(∂_τ G(0, ·))(θ)(π η)` is `(J_0 η)(X_i)`, so its
  -- kernel is flat for `J_0` on the batch, hence at every input, hence in `V`
  have hV' : ∀ η, fderiv ℝ (G 0) θ (η - clmPi_SN A η)
      + fderiv ℝ (fun θ' => deriv (fun τ => G τ θ') 0) θ (clmPi_SN A η) = 0 → η ∈ V := by
    intro η hη
    rw [hD0, hD1] at hη
    apply hV
    refine hX η (fun i => ?_)
    have hi := congrFun hη i
    simp only [Pi.add_apply, Pi.zero_apply] at hi
    show smallWritesLimitNorm A θ η (X i) = 0
    refine Eq.trans ?_ hi
    simp only [smallWritesLimitNorm, sub_E_SN, sub_D_SN, clmPi_SN_E, clmPi_SN_D, sub_zero,
      map_add, Matrix.add_mul]
    exact add_right_comm _ _ _
  -- (c) the small-parameter lemma
  have key := eventually_finrank_le_of_small_parameter G hG (clmPi_SN A) θ h0 V hV'
  -- (g) `D_θ G(τ, θ) = J(θ_τ) ∘ S_τ`, so its rank is at most `jacobianRank` at `θ_τ`, at most `fd(θ_τ)`
  have hrank : ∀ τ, Module.finrank ℝ (LinearMap.range (fderiv ℝ (G τ) θ).toLinearMap)
      ≤ funDim A 1 (θ.smallWrites τ) := by
    intro τ
    let S := LinearMap.toContinuousLinearMap (linSmall_SN A (dIn := dIn) (dOut := dOut) τ)
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
