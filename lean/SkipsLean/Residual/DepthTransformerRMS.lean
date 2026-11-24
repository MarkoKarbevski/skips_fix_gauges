import SkipsLean.Residual.DepthAttentionRMSDim
import SkipsLean.Residual.DepthMlpRMS
import SkipsLean.Dimension.UpperBoundTransformer
import SkipsLean.Generic.Sum

/-!
# Residual networks of attention blocks and MLP blocks at any depth, under pre-RMSNorm

Paper (skips paper): Lemma A.27 (Small writes), second value: "let each block, in any order and
of any width, be an attention block […] or an MLP block, with all MLP blocks tanh, all GELU, all
SwiGLU or all GeGLU blocks. […] For all small `τ ≠ 0`, the residual network has
`fd(θ_τ) = P − d_model (d_model − 1)/2 − s` (pre-RMSNorm with `ε > 0`, no biases)". Theorem 4.7:
"Let the blocks be analytic, with or without pre-RMSNorm. The residual network satisfies the
equality condition: at generic parameters its functional dimension is `P − dim G − s`. So the
skips raise the functional dimension by at least `L dim G`".

The proof of Lemma A.27 under pre-RMSNorm: "This is the equation of the proof of Theorem B.1(ii)
with `h_1 = xE` and `D_θ h_1 η = x η_E + D_θ g(n) η`, and its Steps 1 to 5 go through with three
changes. […] In Step 4, the hidden units are handled first, on inputs with equal tokens, as
above. So the flat directions are the `η^Y`, the rescalings of the units and the changes of basis
inside the heads, a space of dimension `d_model (d_model − 1)/2 + s`."

Here for `Arch.attentionMlp sees σ (rmsNorm ε) H dh hid` (`Network/Transformer.lean`): `L` blocks,
block `ℓ` with the heads `H ℓ` of width `dh ℓ` and the hidden units `hid ℓ` (an attention block if
`hid ℓ` is empty, an MLP block if `H ℓ` is empty), under pre-RMSNorm with `ε > 0`, with a token
`t₂` that sees itself and another token `t₁`; stated for every activation that satisfies the
conclusion of Lemma B.3 with `s = 0` (`UnitsRigid`) for the hidden units of all blocks together.
The conditions on `θ` are those of the two kinds of block, on the two parts of the parameters:
`SmallWritesGenericAttentionRMS θ.sumFst` (`Residual/DepthAttentionRMS.lean`) and
`SmallWritesGenericRMS θ.sumSnd` (`Residual/DepthMlpRMS.lean`). For a block without heads `dh ℓ`
is any nonempty type. The twin without normalization: `Residual/DepthTransformer.lean`.

* `smallWritesLimitNorm_eq_zero_attentionMlp_rmsNorm`: the flat directions of `J_0`;
* `eventually_funDim_smallWrites_attentionMlp_rmsNorm`: `fd(θ_τ) = P − d(d−1)/2 − s` for all small
  `τ ≠ 0`, `s = 2 ∑_ℓ H_ℓ d_{h,ℓ}²`;
* `ae_smallWritesGeneric_attentionMlp_rmsNorm`: the conditions at generic parameters;
* `ae_funDim_attentionMlp_residual_rmsNorm`: Theorem 4.7, and `…_ge_add`: the gain of at least
  `L d(d−1)/2` for blocks of total width `H d_h + d_hidden ≥ d`;
* the named kinds: attention with tanh blocks, attention with GELU blocks.
-/

namespace Skips

open Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {sees : T → T → Prop} [DecidableRel sees]
variable {H dh hid : Fin L → Type} [∀ ℓ, Fintype (H ℓ)] [∀ ℓ, Fintype (dh ℓ)]
  [∀ ℓ, Fintype (hid ℓ)] {σ σ' : ℝ → ℝ} {ε : ℝ}

/-! ### Helpers: derivatives of matrix curves at `0` -/

/-- Helper (as `hasDerivAt_line_rma` of `Residual/DepthAttentionRMS.lean`): a line `τ ↦ M + τ N`
of matrices has the derivative `N`. -/
private theorem hasDerivAt_line_dtr {m n : Type*} [Fintype m] [Fintype n] (M N : Matrix m n ℝ) :
    HasDerivAt (fun τ : ℝ => M + τ • N) N 0 := by
  have h := ((hasDerivAt_id (0 : ℝ)).smul_const N).const_add M
  rw [one_smul] at h
  exact h

/-- Helper (as `hasDerivAt_mul_rma`): the product rule for two matrix curves, entry by entry. -/
private theorem hasDerivAt_mul_dtr {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
    {A : ℝ → Matrix m n ℝ} {B : ℝ → Matrix n p ℝ} {A' : Matrix m n ℝ} {B' : Matrix n p ℝ}
    (hA : HasDerivAt A A' 0) (hB : HasDerivAt B B' 0) :
    HasDerivAt (fun τ => A τ * B τ) (A' * B 0 + A 0 * B') 0 := by
  refine hasDerivAt_pi.2 fun a => hasDerivAt_pi.2 fun c => ?_
  have h := HasDerivAt.fun_sum (u := Finset.univ) fun b _ =>
    (hasDerivAt_pi.1 (hasDerivAt_pi.1 hA a) b).fun_mul (hasDerivAt_pi.1 (hasDerivAt_pi.1 hB b) c)
  simp only [Matrix.add_apply, Matrix.mul_apply, ← Finset.sum_add_distrib]
  exact h

/-- Helper: a row vector times a matrix curve, `τ ↦ u M(τ)`, has the derivative `u M'`. -/
private theorem hasDerivAt_vecMul_dtr {m n : Type*} [Fintype m] [Fintype n] (u : m → ℝ)
    {M : ℝ → Matrix m n ℝ} {M' : Matrix m n ℝ} (hM : HasDerivAt M M' 0) :
    HasDerivAt (fun τ => u ᵥ* M τ) (u ᵥ* M') 0 := by
  refine hasDerivAt_pi.2 fun j => ?_
  have h := HasDerivAt.fun_sum (u := Finset.univ) fun k _ =>
    (hasDerivAt_pi.1 (hasDerivAt_pi.1 hM k) j).const_mul (u k)
  exact h

omit [DecidableEq d] in
/-- Helper (as `hasDerivAt_block_rma`): for a map `f` differentiable at `n R`, the curve
`τ ↦ f(n (R + τ R')) (W + τ W')` has at `τ = 0` the derivative `D f(n R)(n R') W + f(n R) W'`
(chain rule and product rule). -/
private theorem hasDerivAt_blockCurve_dtr {r w : Type*} [Fintype r] [Fintype w]
    (f : Matrix T r ℝ → Matrix T w ℝ) (n : Matrix T d ℝ) (R R' : Matrix d r ℝ)
    (W W' : Matrix w d ℝ) (hf : DifferentiableAt ℝ f (n * R)) :
    HasDerivAt (fun τ : ℝ => f (n * (R + τ • R')) * (W + τ • W'))
      (fderiv ℝ f (n * R) (n * R') * W + f (n * R) * W') 0 := by
  -- the line `τ ↦ n (R + τ R')` has the derivative `n R'`
  have hl : HasDerivAt (fun τ : ℝ => n * (R + τ • R')) (n * R') 0 :=
    (hasDerivAt_mul_dtr (hasDerivAt_const (0 : ℝ) n) (hasDerivAt_line_dtr R R')).congr_deriv
      (by simp only [Matrix.zero_mul, zero_add])
  -- the chain rule through `f`
  have hc := hf.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hl (by rw [zero_smul, add_zero])
  have hc' : HasDerivAt (fun τ : ℝ => f (n * (R + τ • R'))) (fderiv ℝ f (n * R) (n * R')) 0 :=
    hc
  -- the product rule with the write
  have h := hasDerivAt_mul_dtr hc' (hasDerivAt_line_dtr W W')
  exact h.congr_deriv (by simp only [zero_smul, add_zero])

omit [DecidableEq d] in
/-- Helper (`f_sum_mul`, differentiated along the reads and the writes): in a network of
`A.sum B`, the derivative of block `ℓ` along `(R', W')` is the derivative of block `ℓ` of `A`
along the columns and rows of `A`, plus that of block `ℓ` of `B` along those of `B`. -/
private theorem blockTerm_sum_dtr (A B : Arch T d L) (ℓ : Fin L) (hA : Differentiable ℝ (A.f ℓ))
    (hB : Differentiable ℝ (B.f ℓ)) (n : Matrix T d ℝ) (R R' : Matrix d (A.r ℓ ⊕ B.r ℓ) ℝ)
    (W W' : Matrix (A.w ℓ ⊕ B.w ℓ) d ℝ) :
    fderiv ℝ ((A.sum B).f ℓ) (n * R) (n * R') * W + (A.sum B).f ℓ (n * R) * W'
      = (fderiv ℝ (A.f ℓ) (n * R.submatrix id Sum.inl) (n * R'.submatrix id Sum.inl)
            * W.submatrix Sum.inl id
          + A.f ℓ (n * R.submatrix id Sum.inl) * W'.submatrix Sum.inl id)
        + (fderiv ℝ (B.f ℓ) (n * R.submatrix id Sum.inr) (n * R'.submatrix id Sum.inr)
            * W.submatrix Sum.inr id
          + B.f ℓ (n * R.submatrix id Sum.inr) * W'.submatrix Sum.inr id) := by
  -- the three curves `τ ↦ f(n (R + τ R')) (W + τ W')` and their derivatives at `0`
  have hS := hasDerivAt_blockCurve_dtr ((A.sum B).f ℓ) n R R' W W'
    (differentiable_f_sum hA hB _)
  have hA' := hasDerivAt_blockCurve_dtr (A.f ℓ) n (R.submatrix id Sum.inl)
    (R'.submatrix id Sum.inl) (W.submatrix Sum.inl id) (W'.submatrix Sum.inl id) (hA _)
  have hB' := hasDerivAt_blockCurve_dtr (B.f ℓ) n (R.submatrix id Sum.inr)
    (R'.submatrix id Sum.inr) (W.submatrix Sum.inr id) (W'.submatrix Sum.inr id) (hB _)
  -- along the curve, the block of the sum is the sum of the two blocks (`f_sum_mul`)
  have e : (fun τ : ℝ => (A.sum B).f ℓ (n * (R + τ • R')) * (W + τ • W'))
      = fun τ => A.f ℓ (n * (R.submatrix id Sum.inl + τ • R'.submatrix id Sum.inl))
            * (W.submatrix Sum.inl id + τ • W'.submatrix Sum.inl id)
          + B.f ℓ (n * (R.submatrix id Sum.inr + τ • R'.submatrix id Sum.inr))
            * (W.submatrix Sum.inr id + τ • W'.submatrix Sum.inr id) := by
    funext τ
    rw [f_sum_mul]
    rfl
  rw [e] at hS
  exact hS.unique (hA'.add hB')

/-! ### Helpers: the blocks on a state whose rows are all equal -/

/-- Helper (as `attnWeights_sum_rat` of `Absorb/RMSNormAttention.lean`): row `t` of the weights
sums to `1` when token `t` sees some token (the denominator is positive). -/
private theorem attnWeights_sum_dtr (Z : Matrix T T ℝ) (t : T) (ht : ∃ s, sees t s) :
    ∑ s, attnWeights sees Z t s = 1 := by
  obtain ⟨s, hs⟩ := ht
  have hS : 0 < ∑ s', if sees t s' then Real.exp (Z t s') else 0 := by
    refine Finset.sum_pos' (fun s' _ => ?_) ⟨s, Finset.mem_univ _, ?_⟩
    · split_ifs
      · exact (Real.exp_pos _).le
      · exact le_rfl
    · simp only [hs, ite_true]
      exact Real.exp_pos _
  have h1 : ∀ s, attnWeights sees Z t s = (if sees t s then Real.exp (Z t s) else 0)
      / ∑ s', if sees t s' then Real.exp (Z t s') else 0 := by
    intro s
    simp only [attnWeights, Matrix.of_apply]
    split_ifs
    · rfl
    · rw [zero_div]
  simp only [h1, ← Finset.sum_div]
  exact div_self hS.ne'

omit [DecidableEq d] in
/-- Helper: if row `t` of `P` sums to `1`, row `t` of `P n C`, for the state `n` whose rows all
equal `u`, is `u C`. -/
private theorem row_const_dtr {m : Type*} [Fintype m] (P : Matrix T T ℝ) (u : d → ℝ) (t : T)
    (hP : ∑ s, P t s = 1) (C : Matrix d m ℝ) :
    (P * Matrix.of (fun _ : T => u) * C) t = u ᵥ* C := by
  have h : (P * Matrix.of (fun _ : T => u)) t = u := by
    funext k
    simp only [Matrix.mul_apply, Matrix.of_apply, ← Finset.sum_mul, hP, one_mul]
  rw [Matrix.mul_apply_eq_vecMul, h]

omit [DecidableEq d] in
/-- Helper ("every head gives it the value of the common row"): on the state `n` whose rows all
equal `u`, row `t` of the output of attention block `ℓ` is `u ∑_i W_{V,i} W_{O,i}`, whatever the
scores, when token `t` sees some token. -/
private theorem attn_row_const_dtr (χ : Matrix T d ℝ → Matrix T d ℝ) (u : d → ℝ) (t : T)
    (ht : ∃ s, sees t s) (ℓ : Fin L) (R : Matrix d (H ℓ × (dh ℓ ⊕ (dh ℓ ⊕ dh ℓ))) ℝ)
    (W : Matrix (H ℓ × dh ℓ) d ℝ) :
    ((Arch.attention (T := T) (d := d) sees χ H dh).f ℓ (Matrix.of (fun _ : T => u) * R) * W) t
      = u ᵥ* ∑ i, (R.submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k)))
          * W.submatrix (fun k : dh ℓ => (i, k)) id := by
  -- equation (4): the sum over the heads of `P_i n W_{V,i} W_{O,i}`
  rw [f_attention_mul, vecMul_sum]
  funext j
  simp only [attentionBlock, attnHeads, Matrix.sum_apply, Finset.sum_apply]
  exact Finset.sum_congr rfl fun i _ =>
    congrFun (row_const_dtr _ u t (attnWeights_sum_dtr _ t ht) _) j

omit [DecidableEq d] in
/-- Helper: on the state `n` whose rows all equal `u`, row `t` of the derivative of attention
block `ℓ` along the reads and the writes is `u ∑_i (η_{V,i} W_{O,i} + W_{V,i} η_{O,i})`, linear
in `u`, when token `t` sees some token. -/
private theorem attn_dir_row_const_dtr (χ : Matrix T d ℝ → Matrix T d ℝ) (u : d → ℝ) (t : T)
    (ht : ∃ s, sees t s) (ℓ : Fin L) (R R' : Matrix d (H ℓ × (dh ℓ ⊕ (dh ℓ ⊕ dh ℓ))) ℝ)
    (W W' : Matrix (H ℓ × dh ℓ) d ℝ) :
    (fderiv ℝ ((Arch.attention (T := T) (d := d) sees χ H dh).f ℓ)
          (Matrix.of (fun _ : T => u) * R) (Matrix.of (fun _ : T => u) * R') * W
        + (Arch.attention (T := T) (d := d) sees χ H dh).f ℓ (Matrix.of (fun _ : T => u) * R)
          * W') t
      = u ᵥ* ∑ i, ((R'.submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k)))
            * W.submatrix (fun k : dh ℓ => (i, k)) id
          + (R.submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k)))
            * W'.submatrix (fun k : dh ℓ => (i, k)) id) := by
  -- the curve `τ ↦ f_ℓ(n (R + τ R')) (W + τ W')` at `τ = 0`, row `t`
  have h1 := hasDerivAt_pi.1 (hasDerivAt_blockCurve_dtr
    ((Arch.attention (T := T) (d := d) sees χ H dh).f ℓ) (Matrix.of (fun _ : T => u)) R R' W W'
    (differentiable_f_attention sees χ H dh ℓ _)) t
  -- the same row is `u ∑_i (W_{V,i} + τ η_{V,i}) (W_{O,i} + τ η_{O,i})`
  have e : (fun τ : ℝ => ((Arch.attention (T := T) (d := d) sees χ H dh).f ℓ
        (Matrix.of (fun _ : T => u) * (R + τ • R')) * (W + τ • W')) t)
      = fun τ => u ᵥ* ∑ i, ((R.submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k)))
            + τ • (R'.submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))))
          * (W.submatrix (fun k : dh ℓ => (i, k)) id
            + τ • W'.submatrix (fun k : dh ℓ => (i, k)) id) := by
    funext τ
    exact attn_row_const_dtr χ u t ht ℓ (R + τ • R') (W + τ • W')
  have h2 := hasDerivAt_vecMul_dtr u (HasDerivAt.fun_sum (u := Finset.univ) fun i _ =>
    hasDerivAt_mul_dtr
      (hasDerivAt_line_dtr (R.submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k)))
        (R'.submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))))
      (hasDerivAt_line_dtr (W.submatrix (fun k : dh ℓ => (i, k)) id)
        (W'.submatrix (fun k : dh ℓ => (i, k)) id)))
  rw [e] at h1
  refine h1.unique (h2.congr_deriv ?_)
  simp only [zero_smul, add_zero]

/-- Helper (as `fderiv_map_apply_dmr` of `Residual/DepthMlpRMS.lean`): the derivative of
`M ↦ σ(M)` (entrywise) at `P` along `Q` has the entries `σ'(P_{t i}) Q_{t i}`. -/
private theorem fderiv_map_apply_dtr (hσ : ∀ z, HasDerivAt σ (σ' z) z) {m n : Type*} [Fintype m]
    [Fintype n] (P Q : Matrix m n ℝ) (t : m) (i : n) :
    fderiv ℝ (fun M : Matrix m n ℝ => M.map σ) P Q t i = σ' (P t i) * Q t i := by
  have hσd : Differentiable ℝ σ := fun z => (hσ z).differentiableAt
  have hd : Differentiable ℝ (fun M : Matrix m n ℝ => M.map σ) :=
    differentiable_pi.2 fun t => differentiable_pi.2 fun i =>
      hσd.comp (differentiable_pi.1 (differentiable_pi.1 differentiable_id t) i)
  -- the chain rule along the line `τ ↦ P + τ Q`
  have hline : HasDerivAt (fun τ : ℝ => P + τ • Q) Q 0 := hasDerivAt_line_dtr P Q
  have h0 : P = P + (0 : ℝ) • Q := by rw [zero_smul, add_zero]
  have h1 := (hd P).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hline h0
  have h2 := hasDerivAt_pi.1 (hasDerivAt_pi.1 h1 t) i
  -- the same derivative, entrywise: `τ ↦ σ(P_{t i} + τ Q_{t i})`
  have h3 : HasDerivAt (fun τ : ℝ => σ (P t i + τ * Q t i)) (σ' (P t i) * Q t i) 0 := by
    have hu : HasDerivAt (fun τ : ℝ => P t i + τ * Q t i) (Q t i) 0 := by
      have h := ((hasDerivAt_id (0 : ℝ)).mul_const (Q t i)).const_add (P t i)
      rw [one_mul] at h
      exact h
    exact (hσ (P t i)).comp_of_eq (0 : ℝ) hu (by rw [zero_mul, add_zero])
  exact h2.unique h3

omit [Fintype d] [DecidableEq d] in
/-- Helper: the same for the map of block `ℓ` of an MLP network. -/
private theorem fderiv_f_mlp_apply_dtr (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    {χ : Matrix T d ℝ → Matrix T d ℝ} (ℓ : Fin L) (P Q : Matrix T (hid ℓ) ℝ) (t : T)
    (i : hid ℓ) :
    fderiv ℝ ((Arch.mlp (T := T) (d := d) σ χ hid).f ℓ) P Q t i = σ' (P t i) * Q t i :=
  fderiv_map_apply_dtr hσ P Q t i

omit [DecidableEq d] in
/-- Helper: on the state `n` whose rows all equal `u`, entry `(t, j)` of the derivative of MLP
block `ℓ` along the reads and the writes is
`∑_i (σ(u c_i) ψ_{a_i, j} + σ'(u c_i) (u ψ_{c_i}) a_{i, j})`. -/
private theorem mlp_dir_row_const_dtr (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (χ : Matrix T d ℝ → Matrix T d ℝ) (u : d → ℝ) (t : T) (ℓ : Fin L)
    (R R' : Matrix d (hid ℓ) ℝ) (W W' : Matrix (hid ℓ) d ℝ) (j : d) :
    (fderiv ℝ ((Arch.mlp (T := T) (d := d) σ χ hid).f ℓ) (Matrix.of (fun _ : T => u) * R)
          (Matrix.of (fun _ : T => u) * R') * W
        + (Arch.mlp (T := T) (d := d) σ χ hid).f ℓ (Matrix.of (fun _ : T => u) * R) * W') t j
      = ∑ i, (σ (u ⬝ᵥ Rᵀ i) * W' i j + σ' (u ⬝ᵥ Rᵀ i) * (u ⬝ᵥ R'ᵀ i) * W i j) := by
  rw [Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [fderiv_f_mlp_apply_dtr hσ]
  show σ' (u ⬝ᵥ Rᵀ i) * (u ⬝ᵥ R'ᵀ i) * W i j + σ (u ⬝ᵥ Rᵀ i) * W' i j = _
  ring

/-- Helper: `v ↦ v ⬝ w` is analytic (a linear form). -/
private theorem analyticOnNhd_dotProduct_dtr {n : Type*} [Fintype n] (w : n → ℝ) :
    AnalyticOnNhd ℝ (fun v : n → ℝ => v ⬝ᵥ w) Set.univ := by
  simp only [dotProduct]
  exact Finset.analyticOnNhd_fun_sum _ fun k _ =>
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : n => ℝ) k).analyticOnNhd _).mul
      analyticOnNhd_const

omit [Fintype T] [DecidableEq d] in
/-- Helper: `N_ε(0) = 0`. -/
private theorem rmsNorm_zero_dtr : rmsNorm ε (0 : Matrix T d ℝ) = 0 := by
  ext t k
  simp [rmsNorm, rmsRow]

/-- **Proof of Lemma A.27, attention blocks and MLP blocks under pre-RMSNorm, the flat
directions of `J_0`:** let `ε > 0` and let token `t₂` see itself and another token `t₁`. Under
the conditions of the lemma, a direction `η` with `(J_0 η)(x) = 0` at every input `x` has
`η_E = E Y` and `η_D = −Y D` for one antisymmetric matrix `Y`; in every block the reads and the
writes of its heads are those of the directions of the changes of basis inside the heads, and
the reads and the writes of its hidden units vanish. -/
theorem smallWritesLimitNorm_eq_zero_attentionMlp_rmsNorm (hε : 0 < ε)
    (hσ : ∀ z, HasDerivAt σ (σ' z) z) (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (hU : UnitsRigid σ σ' d d (Σ ℓ, hid ℓ))
    (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁)
    (θ : Params (Arch.attentionMlp (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut)
    (hθa : SmallWritesGenericAttentionRMS θ.sumFst) (hθm : SmallWritesGenericRMS θ.sumSnd)
    (η : Params (Arch.attentionMlp (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut)
    (hη : ∀ x, smallWritesLimitNorm (Arch.attentionMlp sees σ (rmsNorm ε) H dh hid) θ η x = 0) :
    ∃ (Y : Matrix d d ℝ) (Γ Γ' : ∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ),
      Yᵀ = -Y ∧ η.E = θ.E * Y ∧ η.D = -(Y * θ.D)
        ∧ (∀ ℓ, η.sumFst.read ℓ = (headDirQK θ.sumFst Γ + headDirVO θ.sumFst Γ').read ℓ)
        ∧ (∀ ℓ, η.sumFst.write ℓ = (headDirQK θ.sumFst Γ + headDirVO θ.sumFst Γ').write ℓ)
        ∧ (∀ ℓ, η.sumSnd.read ℓ = 0) ∧ (∀ ℓ, η.sumSnd.write ℓ = 0) := by
  have : Nonempty T := ⟨t₁⟩
  have hσd : Differentiable ℝ σ := fun z => (hσ z).differentiableAt
  -- the blocks are analytic, hence `C¹`
  have hf : ∀ ℓ, ContDiff ℝ 1
      ((Arch.attentionMlp (T := T) (d := d) sees σ (rmsNorm ε) H dh hid).f ℓ) := fun ℓ =>
    (analyticOnNhd_f_sum (analyticOnNhd_f_attention (d := d) sees (rmsNorm ε) H dh ℓ)
      (analyticOnNhd_f_mlp hσa ℓ)).contDiff
  -- Steps 1 to 3: the equation of the wide block at every `n = N_ε(x E)`
  obtain ⟨-, -, -, -, hF⟩ :=
    exists_antisymm_of_smallWritesLimitNorm_rmsNorm hε rfl hf θ hθa.rank_E hθa.rank_D η hη
  -- the wide block of the heads and the wide block of the hidden units, along `η`
  obtain ⟨GA, hGA⟩ : ∃ GA : Matrix T d ℝ → Matrix T d ℝ, GA = fun n =>
      ∑ ℓ, (fderiv ℝ ((Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh).f ℓ)
          (n * θ.sumFst.read ℓ) (n * η.sumFst.read ℓ) * θ.sumFst.write ℓ
        + (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh).f ℓ (n * θ.sumFst.read ℓ)
          * η.sumFst.write ℓ) := ⟨_, rfl⟩
  obtain ⟨GM, hGM⟩ : ∃ GM : Matrix T d ℝ → Matrix T d ℝ, GM = fun n =>
      ∑ ℓ, (fderiv ℝ ((Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid).f ℓ)
          (n * θ.sumSnd.read ℓ) (n * η.sumSnd.read ℓ) * θ.sumSnd.write ℓ
        + (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid).f ℓ (n * θ.sumSnd.read ℓ)
          * η.sumSnd.write ℓ) := ⟨_, rfl⟩
  -- `f_sum_mul` and its derivative: the wide block of the sum is the sum of the two
  have hsplit : ∀ n : Matrix T d ℝ,
      ∑ ℓ, (fderiv ℝ ((Arch.attentionMlp (T := T) (d := d) sees σ (rmsNorm ε) H dh hid).f ℓ)
          (n * θ.read ℓ) (n * η.read ℓ) * θ.write ℓ
        + (Arch.attentionMlp (T := T) (d := d) sees σ (rmsNorm ε) H dh hid).f ℓ (n * θ.read ℓ)
          * η.write ℓ) = GA n + GM n := by
    intro n
    simp only [hGA, hGM]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun ℓ _ => blockTerm_sum_dtr
      (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh)
      (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) ℓ
      (differentiable_f_attention (d := d) sees (rmsNorm ε) H dh ℓ) (differentiable_f_mlp hσd ℓ)
      n (θ.read ℓ) (η.read ℓ) (θ.write ℓ) (η.write ℓ)
  -- Step 4 (a), the heads: on a state whose rows all equal `v`, row `t₂` of the wide block of
  -- the heads is `v Ψ`, `Ψ = ∑_{ℓ,i} (η_V W_O + W_V η_O)`, linear in `v`
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : Matrix d d ℝ, Ψ = ∑ ℓ, ∑ i : H ℓ,
      (((η.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k)))
          * (θ.sumFst.write ℓ).submatrix (fun k : dh ℓ => (i, k)) id
        + ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k)))
          * (η.sumFst.write ℓ).submatrix (fun k : dh ℓ => (i, k)) id) := ⟨_, rfl⟩
  have hGA_row : ∀ (v : d → ℝ) (j : d), GA (Matrix.of fun _ => v) t₂ j = (v ᵥ* Ψ) j := by
    intro v j
    simp only [hGA]
    rw [Matrix.sum_apply, hΨ, vecMul_sum, Finset.sum_apply]
    exact Finset.sum_congr rfl fun ℓ _ => congrFun (attn_dir_row_const_dtr (rmsNorm ε) v t₂
      ⟨t₂, hs2⟩ ℓ (θ.sumFst.read ℓ) (η.sumFst.read ℓ) (θ.sumFst.write ℓ) (η.sumFst.write ℓ)) j
  -- the hidden units: entry `(t₂, j)` is the sum over the units `(ℓ, i)` of all blocks
  have hGM_row : ∀ (v : d → ℝ) (j : d), GM (Matrix.of fun _ => v) t₂ j
      = ∑ p : (Σ ℓ, hid ℓ), (σ (v ⬝ᵥ (θ.sumSnd.read p.1)ᵀ p.2) * η.sumSnd.write p.1 p.2 j
        + σ' (v ⬝ᵥ (θ.sumSnd.read p.1)ᵀ p.2) * (v ⬝ᵥ (η.sumSnd.read p.1)ᵀ p.2)
          * θ.sumSnd.write p.1 p.2 j) := by
    intro v j
    simp only [hGM]
    rw [Matrix.sum_apply, Fintype.sum_sigma]
    exact Finset.sum_congr rfl fun ℓ _ => mlp_dir_row_const_dtr hσ (rmsNorm ε) v t₂ ℓ
      (θ.sumSnd.read ℓ) (η.sumSnd.read ℓ) (θ.sumSnd.write ℓ) (η.sumSnd.write ℓ) j
  -- the equation at every normalized state `n = N_ε(h)` whose rows all equal `v` (`x = h E⁺`)
  obtain ⟨B, hB⟩ : ∃ B : Matrix d dIn ℝ, B * θ.E = 1 :=
    Matrix.vecMul_surjective_iff_exists_left_inverse.mp
      (Matrix.vecMul_surjective_iff_rank_eq_card.mpr hθa.rank_E)
  have hrow : ∀ (h : Matrix T d ℝ) (v : d → ℝ), rmsNorm ε h = Matrix.of (fun _ => v) →
      ∀ j : d, (v ᵥ* Ψ) j + ∑ p : (Σ ℓ, hid ℓ), (σ (v ⬝ᵥ (θ.sumSnd.read p.1)ᵀ p.2)
          * η.sumSnd.write p.1 p.2 j
        + σ' (v ⬝ᵥ (θ.sumSnd.read p.1)ᵀ p.2) * (v ⬝ᵥ (η.sumSnd.read p.1)ᵀ p.2)
          * θ.sumSnd.write p.1 p.2 j) = 0 := by
    intro h v hv j
    have e := hF (h * B)
    rw [Matrix.mul_assoc h B θ.E, hB, Matrix.mul_one, hv, hsplit] at e
    have e2 := congrFun (congrFun e t₂) j
    rw [Matrix.add_apply, hGA_row, hGM_row, Matrix.zero_apply] at e2
    exact e2
  -- Step 4 (b): `σ'` is analytic, and the equation holds near `v = 0` (the range of `N_ε` is
  -- open and contains `0`), hence for all `v`
  have hσ'a : AnalyticOnNhd ℝ σ' Set.univ := by
    have e : σ' = deriv σ := funext fun z => (hσ z).deriv.symm
    rw [e]
    exact hσa.deriv
  have hopen : IsOpen {v : d → ℝ |
      (Matrix.of fun _ : T => v) ∈ Set.range (rmsNorm ε : Matrix T d ℝ → Matrix T d ℝ)} :=
    (isOpenMap_rmsNorm hε).isOpen_range.preimage (continuous_pi fun _ => continuous_id)
  have h0 : (0 : d → ℝ) ∈ {v : d → ℝ |
      (Matrix.of fun _ : T => v) ∈ Set.range (rmsNorm ε : Matrix T d ℝ → Matrix T d ℝ)} :=
    ⟨0, by rw [rmsNorm_zero_dtr]; rfl⟩
  have hall : ∀ (v : d → ℝ) (j : d), (v ᵥ* Ψ) j + ∑ p : (Σ ℓ, hid ℓ),
      (σ (v ⬝ᵥ (θ.sumSnd.read p.1)ᵀ p.2) * η.sumSnd.write p.1 p.2 j
        + σ' (v ⬝ᵥ (θ.sumSnd.read p.1)ᵀ p.2) * (v ⬝ᵥ (η.sumSnd.read p.1)ᵀ p.2)
          * θ.sumSnd.write p.1 p.2 j) = 0 := by
    intro v j
    have hg : AnalyticOnNhd ℝ (fun v : d → ℝ => (v ᵥ* Ψ) j + ∑ p : (Σ ℓ, hid ℓ),
        (σ (v ⬝ᵥ (θ.sumSnd.read p.1)ᵀ p.2) * η.sumSnd.write p.1 p.2 j
          + σ' (v ⬝ᵥ (θ.sumSnd.read p.1)ᵀ p.2) * (v ⬝ᵥ (η.sumSnd.read p.1)ᵀ p.2)
            * θ.sumSnd.write p.1 p.2 j)) Set.univ :=
      (analyticOnNhd_dotProduct_dtr (fun k => Ψ k j)).add
        (Finset.analyticOnNhd_fun_sum _ fun p _ =>
          ((hσa.comp (analyticOnNhd_dotProduct_dtr _) (Set.mapsTo_univ _ _)).mul
            analyticOnNhd_const).add
          (((hσ'a.comp (analyticOnNhd_dotProduct_dtr _) (Set.mapsTo_univ _ _)).mul
            (analyticOnNhd_dotProduct_dtr _)).mul analyticOnNhd_const))
    have hev : (fun v : d → ℝ => (v ᵥ* Ψ) j + ∑ p : (Σ ℓ, hid ℓ),
        (σ (v ⬝ᵥ (θ.sumSnd.read p.1)ᵀ p.2) * η.sumSnd.write p.1 p.2 j
          + σ' (v ⬝ᵥ (θ.sumSnd.read p.1)ᵀ p.2) * (v ⬝ᵥ (η.sumSnd.read p.1)ᵀ p.2)
            * θ.sumSnd.write p.1 p.2 j)) =ᶠ[nhds 0] 0 :=
      Filter.eventually_of_mem (hopen.mem_nhds h0) fun w hw => by
        obtain ⟨h, hh⟩ := hw
        exact hrow h w hh j
    exact hg.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
      (Set.mem_univ 0) hev (Set.mem_univ v)
  -- Step 4 (c): Lemma B.3 for the units of all blocks together, with `E`, `D` the identity and
  -- the linear term `x Ψ`: the reads and the writes of the hidden units vanish
  obtain ⟨-, -, hc, -, ha⟩ := hU (fun p => (θ.sumSnd.read p.1)ᵀ p.2) 0
    (fun p => θ.sumSnd.write p.1 p.2) Ψ 0 (fun p => (η.sumSnd.read p.1)ᵀ p.2) 0
    (fun p => η.sumSnd.write p.1 p.2)
    (fun p => hθm.row_ne_zero p.1 p.2) (fun p => hθm.col_ne_zero p.1 p.2) hθm.col_not_collinear
    (by
      intro v
      funext j
      have h := hall v j
      simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
        add_zero]
      exact h)
  have hmr : ∀ ℓ, η.sumSnd.read ℓ = 0 := fun ℓ => by
    ext k i
    exact congrFun (congrFun hc ⟨ℓ, i⟩) k
  have hmw : ∀ ℓ, η.sumSnd.write ℓ = 0 := fun ℓ => by
    ext i k
    exact congrFun (congrFun ha ⟨ℓ, i⟩) k
  -- so the wide block of the hidden units vanishes along `η`, and `η.sumFst` is flat for `J_0`
  -- of the network of the heads alone
  have hGM0 : ∀ n, GM n = 0 := by
    intro n
    simp only [hGM, hmr, hmw, Matrix.mul_zero, map_zero, Matrix.zero_mul, add_zero,
      Finset.sum_const_zero]
  have hηA : ∀ x, smallWritesLimitNorm (Arch.attention sees (rmsNorm ε) H dh) θ.sumFst
      η.sumFst x = 0 := by
    intro x
    have e := hη x
    rw [smallWritesLimitNorm, hsplit, hGM0, add_zero] at e
    rw [smallWritesLimitNorm]
    simp only [hGA] at e
    exact e
  -- Step 4 for the heads (`Residual/DepthAttentionRMS.lean`)
  obtain ⟨Y, Γ, Γ', hYa, hE, hD, hr, hw⟩ :=
    smallWritesLimitNorm_eq_zero_attention_rmsNorm hε t₁ t₂ h12 hs2 hs1 θ.sumFst hθa η.sumFst hηA
  exact ⟨Y, Γ, Γ', hYa, hE, hD, hr, hw, hmr, hmw⟩

/-! ### Helpers: the space of the flat directions of `J_0` -/

omit [Fintype T] [DecidableEq d] [Fintype dIn] in
/-- Helper (as `flatEDLin_rma` of `Residual/DepthAttentionRMS.lean`): the directions
`Y ↦ (E Y, 0, 0, −Y D)` of one change of basis at all hidden states, as a linear map. -/
private def flatEDLin_dtr {A : Arch T d L} (θ : Params A dIn dOut) :
    Matrix d d ℝ →ₗ[ℝ] Params A dIn dOut where
  toFun X := ⟨θ.E * X, 0, 0, -(X * θ.D)⟩
  map_add' X Y := by
    apply Params.ext'
    · exact Matrix.mul_add _ _ _
    · intro ℓ
      exact (add_zero 0).symm
    · intro ℓ
      exact (add_zero 0).symm
    · show -((X + Y) * θ.D) = -(X * θ.D) + -(Y * θ.D)
      rw [Matrix.add_mul, neg_add]
  map_smul' c X := by
    apply Params.ext'
    · exact Matrix.mul_smul _ _ _
    · intro ℓ
      exact (smul_zero c).symm
    · intro ℓ
      exact (smul_zero c).symm
    · show -((c • X) * θ.D) = c • -(X * θ.D)
      rw [Matrix.smul_mul, smul_neg]

/-- Helper (as `headDirQKLin_rma`): `Γ ↦ headDirQK θ Γ` is linear. -/
private noncomputable def headDirQKLin_dtr {χ : Matrix T d ℝ → Matrix T d ℝ}
    (θ : Params (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut) :
    (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) →ₗ[ℝ]
      Params (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut where
  toFun := headDirQK θ
  map_add' Γ Δ := by
    apply Params.ext'
    · simp [headDirQK]
    · intro ℓ
      ext a ⟨i, k | k | k⟩
      · simp only [headDirQK, Params.add_read, Matrix.add_apply, Matrix.of_apply, Pi.add_apply,
          mul_add, Finset.sum_add_distrib]
      · simp only [headDirQK, Params.add_read, Matrix.add_apply, Matrix.of_apply, Pi.add_apply,
          mul_add, Finset.sum_add_distrib, neg_add]
      · simp [headDirQK]
    · intro ℓ
      simp [headDirQK]
    · simp [headDirQK]
  map_smul' c Γ := by
    apply Params.ext'
    · simp [headDirQK]
    · intro ℓ
      ext a ⟨i, k | k | k⟩
      · simp only [headDirQK, Params.smul_read, Matrix.smul_apply, Matrix.of_apply, Pi.smul_apply,
          smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => by ring
      · simp only [headDirQK, Params.smul_read, Matrix.smul_apply, Matrix.of_apply, Pi.smul_apply,
          smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_neg]
        exact congrArg Neg.neg (Finset.sum_congr rfl fun _ _ => by ring)
      · simp [headDirQK]
    · intro ℓ
      simp [headDirQK]
    · simp [headDirQK]

/-- Helper (as `headDirVOLin_rma`): `Γ' ↦ headDirVO θ Γ'` is linear. -/
private noncomputable def headDirVOLin_dtr {χ : Matrix T d ℝ → Matrix T d ℝ}
    (θ : Params (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut) :
    (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) →ₗ[ℝ]
      Params (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut where
  toFun := headDirVO θ
  map_add' Γ Δ := by
    apply Params.ext'
    · simp [headDirVO]
    · intro ℓ
      ext a ⟨i, k | k | k⟩
      · simp [headDirVO]
      · simp [headDirVO]
      · simp only [headDirVO, Params.add_read, Matrix.add_apply, Matrix.of_apply, Pi.add_apply,
          mul_add, Finset.sum_add_distrib]
    · intro ℓ
      ext p b
      simp only [headDirVO, Params.add_write, Matrix.add_apply, Matrix.of_apply, Pi.add_apply,
        add_mul, Finset.sum_add_distrib, neg_add]
    · simp [headDirVO]
  map_smul' c Γ := by
    apply Params.ext'
    · simp [headDirVO]
    · intro ℓ
      ext a ⟨i, k | k | k⟩
      · simp [headDirVO]
      · simp [headDirVO]
      · simp only [headDirVO, Params.smul_read, Matrix.smul_apply, Matrix.of_apply, Pi.smul_apply,
          smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => by ring
    · intro ℓ
      ext p b
      simp only [headDirVO, Params.smul_write, Matrix.smul_apply, Matrix.of_apply, Pi.smul_apply,
        smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_neg]
      exact congrArg Neg.neg (Finset.sum_congr rfl fun _ _ => by ring)
    · simp [headDirVO]

/-- Helper (as `finrank_headFun_rma`): the families `Γ` of `d_h × d_h` matrices, one for each
head of each block, form a space of dimension `∑_ℓ H_ℓ d_{h,ℓ}²`. -/
private theorem finrank_headFun_dtr :
    Module.finrank ℝ (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)
      = ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2 := by
  rw [Module.finrank_pi_fintype]
  simp only [Module.finrank_pi_fintype, Module.finrank_matrix, Module.finrank_self, mul_one,
    Finset.sum_const, Finset.card_univ, smul_eq_mul, sq]

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: `η ↦ Params.sumInl η` (a direction of `A` as a direction of the sum, `0` on the part
of `B`) is linear. -/
private def sumInlLin_dtr (A B : Arch T d L) :
    Params A dIn dOut →ₗ[ℝ] Params (A.sum B) dIn dOut where
  toFun η := Params.sumInl η
  map_add' η ζ := by
    refine Params.ext' rfl (fun ℓ => ?_) (fun ℓ => ?_) rfl
    · ext a (j | j)
      · rfl
      · exact (add_zero 0).symm
    · ext (i | i) a
      · rfl
      · exact (add_zero 0).symm
  map_smul' c η := by
    refine Params.ext' rfl (fun ℓ => ?_) (fun ℓ => ?_) rfl
    · ext a (j | j)
      · rfl
      · exact (smul_zero c).symm
    · ext (i | i) a
      · rfl
      · exact (smul_zero c).symm

/-- **Lemma A.27 (Small writes), second value, for attention blocks and MLP blocks, under the
conditions of its proof:** with `ε > 0` and a token that sees itself and another token, for all
small `τ ≠ 0` the residual network has `fd(θ_τ) = P − d(d−1)/2 − 2 ∑_ℓ H_ℓ d_{h,ℓ}²`. -/
theorem eventually_funDim_smallWrites_attentionMlp_rmsNorm (hε : 0 < ε)
    (hσ : ∀ z, HasDerivAt σ (σ' z) z) (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (hU : UnitsRigid σ σ' d d (Σ ℓ, hid ℓ))
    (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁)
    (θ : Params (Arch.attentionMlp (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut)
    (hθa : SmallWritesGenericAttentionRMS θ.sumFst) (hθm : SmallWritesGenericRMS θ.sumSnd) :
    ∀ᶠ τ in 𝓝[≠] (0 : ℝ),
      funDim (Arch.attentionMlp sees σ (rmsNorm ε) H dh hid) 1 (θ.smallWrites τ)
          + (Fintype.card d * (Fintype.card d - 1) / 2
            + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
        = Module.finrank ℝ
            (Params
              (Arch.attentionMlp (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut) := by
  -- the flat directions of `J_0` lie in the range `V` of the linear map
  -- `(Y, Γ, Γ') ↦ (E Y, 0, 0, −Y D) + (headDirQK θ_A Γ + headDirVO θ_A Γ', 0)` on antisymmetric
  -- `Y`, with `0` at the hidden units (the first theorem)
  let Φ := ((flatEDLin_dtr θ).comp (antisymmetric d).subtype).coprod
    ((sumInlLin_dtr (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh)
      (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid)).comp
        ((headDirQKLin_dtr θ.sumFst).coprod (headDirVOLin_dtr θ.sumFst)))
  have hV : ∀ η, (∀ x, smallWritesLimitNorm (Arch.attentionMlp sees σ (rmsNorm ε) H dh hid) θ
      η x = 0) → η ∈ LinearMap.range Φ := by
    intro η hη
    obtain ⟨Y, Γ, Γ', hYa, hE, hD, hr, hw, hmr, hmw⟩ :=
      smallWritesLimitNorm_eq_zero_attentionMlp_rmsNorm hε hσ hσa hU t₁ t₂ h12 hs2 hs1 θ hθa
        hθm η hη
    refine ⟨(⟨Y, hYa⟩, Γ, Γ'), ?_⟩
    apply Params.ext'
    · show θ.E * Y + ((0 : Matrix dIn d ℝ) + 0) = η.E
      rw [add_zero, add_zero, hE]
    · intro ℓ
      ext a (j | j)
      · show (0 : ℝ) + (headDirQK θ.sumFst Γ + headDirVO θ.sumFst Γ').read ℓ a j
          = η.read ℓ a (Sum.inl j)
        rw [zero_add]
        exact (congrFun (congrFun (hr ℓ) a) j).symm
      · show (0 : ℝ) + 0 = η.read ℓ a (Sum.inr j)
        rw [zero_add]
        exact (congrFun (congrFun (hmr ℓ) a) j).symm
    · intro ℓ
      ext (i | i) b
      · show (0 : ℝ) + (headDirQK θ.sumFst Γ + headDirVO θ.sumFst Γ').write ℓ i b
          = η.write ℓ (Sum.inl i) b
        rw [zero_add]
        exact (congrFun (congrFun (hw ℓ) i) b).symm
      · show (0 : ℝ) + 0 = η.write ℓ (Sum.inr i) b
        rw [zero_add]
        exact (congrFun (congrFun (hmw ℓ) i) b).symm
    · show -(Y * θ.D) + ((0 : Matrix d dOut ℝ) + 0) = η.D
      rw [add_zero, add_zero, hD]
  -- `dim V ≤ d(d−1)/2 + 2 ∑_ℓ H_ℓ d_{h,ℓ}²`, the dimension of the domain of the map
  have hdim : Module.finrank ℝ (LinearMap.range Φ)
      ≤ Fintype.card d * (Fintype.card d - 1) / 2
        + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2 := by
    have h := LinearMap.finrank_range_le Φ
    rwa [Module.finrank_prod, Module.finrank_prod, finrank_antisymmetric, finrank_headFun_dtr,
      ← two_mul] at h
  -- `≥`: "The rank" of the proof of Lemma A.27 (`N_ε` and the blocks are analytic); `≤`: the
  -- upper bound for residual networks of attention blocks and MLP blocks under pre-RMSNorm, as
  -- `θ ↦ θ_τ` changes neither `E` nor the reads
  filter_upwards [eventually_funDim_smallWrites_ge_norm
    (Arch.attentionMlp (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) θ
    (analyticOnNhd_rmsNorm hε)
    (fun ℓ => analyticOnNhd_f_sum (analyticOnNhd_f_attention (d := d) sees (rmsNorm ε) H dh ℓ)
      (analyticOnNhd_f_mlp hσa ℓ)) _ hV] with τ hτ
  have hle := funDim_add_le_residual_attentionMlp_rmsNorm ε (θ.smallWrites τ) hθa.rank_E
    hθa.rank_Q hθa.rank_V
  generalize Fintype.card d * (Fintype.card d - 1) / 2 = N at hle hdim ⊢
  omega

/-! ### Helpers: generic parameters of the MLP part -/

/-- Helper (as `rank_eq_of_isUnit_det_rows_dmr` of `Residual/DepthMlpRMS.lean`): a matrix with
`d` columns has rank `d` if some `d` of its rows form an invertible matrix. -/
private theorem rank_eq_of_isUnit_det_rows_dtr {m : Type*} (M : Matrix m d ℝ) (ρ : d ↪ m)
    (h : IsUnit (M.submatrix ρ id).det) : M.rank = Fintype.card d :=
  le_antisymm (Matrix.rank_le_card_width M)
    ((Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).2 h)).symm.le.trans
      (Matrix.rank_submatrix_le M ρ id))

/-- Helper (a copy of `ae_smallWritesGenericRMS` of `Residual/DepthMlpRMS.lean`, whose proof
does not use a token; that theorem carries `[Nonempty T]` from its section): the conditions of
Lemma A.27 under pre-RMSNorm, for MLP blocks, hold at generic parameters. -/
private theorem ae_smallWritesGenericRMS_dtr
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, SmallWritesGenericRMS θ := by
  classical
  -- two distinct coordinates of `h`, `d` rows of `E`, `d` columns of `D`
  obtain ⟨k₁, k₂, hk⟩ := Fintype.exists_pair_of_one_lt_card (show 1 < Fintype.card d by omega)
  obtain ⟨ρ⟩ := Function.Embedding.nonempty_of_card_le hdIn
  obtain ⟨cD⟩ := Function.Embedding.nonempty_of_card_le hdOut
  -- the parameters with all entries `1`
  let θ₁ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut :=
    ⟨Matrix.of fun _ _ => 1, fun _ => Matrix.of fun _ _ => 1, fun _ => Matrix.of fun _ _ => 1,
      Matrix.of fun _ _ => 1⟩
  -- the entries of the reads and of the writes are linear, hence analytic, in the parameters
  have hR : ∀ (ℓ : Fin L) (k : d) (i : hid ℓ), AnalyticOnNhd ℝ
      (fun θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut => θ.read ℓ k i)
      Set.univ := fun ℓ k i =>
    analyticOnNhd_linear ((Matrix.entryLinearMap ℝ ℝ k i).comp
      (Params.linRead (A := Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) (dIn := dIn)
        (dOut := dOut) ℓ))
  have hW : ∀ (ℓ : Fin L) (i : hid ℓ) (k : d), AnalyticOnNhd ℝ
      (fun θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut => θ.write ℓ i k)
      Set.univ := fun ℓ i k =>
    analyticOnNhd_linear ((Matrix.entryLinearMap ℝ ℝ i k).comp
      (Params.linWrite (A := Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) (dIn := dIn)
        (dOut := dOut) ℓ))
  -- the ranks of `E` and `D`: invertible minors
  have h1 := ae_isUnit_det_submatrix μ
  -- the rows of the writes are nonzero: their entries at `k₁` are
  have h2 : ∀ᵐ θ ∂μ, ∀ ℓ (i : hid ℓ), θ.write ℓ i k₁ ≠ 0 :=
    ae_all_iff.2 fun ℓ => ae_all_iff.2 fun i =>
      ae_ne_zero_of_analytic μ (hW ℓ i k₁) ⟨θ₁, show (1 : ℝ) ≠ 0 from one_ne_zero⟩
  -- the columns of the reads are nonzero: their entries at `k₁` are
  have h3 : ∀ᵐ θ ∂μ, ∀ ℓ (i : hid ℓ), θ.read ℓ k₁ i ≠ 0 :=
    ae_all_iff.2 fun ℓ => ae_all_iff.2 fun i =>
      ae_ne_zero_of_analytic μ (hR ℓ k₁ i) ⟨θ₁, show (1 : ℝ) ≠ 0 from one_ne_zero⟩
  -- two columns of distinct units, of one block or of two blocks, are not collinear: a `2 × 2`
  -- minor does not vanish
  have h4 : ∀ᵐ θ ∂μ, ∀ p q : (Σ ℓ, hid ℓ), p ≠ q →
      θ.read p.1 k₁ p.2 * θ.read q.1 k₂ q.2 - θ.read q.1 k₁ q.2 * θ.read p.1 k₂ p.2 ≠ 0 := by
    refine ae_all_iff.2 fun p => ae_all_iff.2 fun q => ?_
    by_cases hpq : p = q
    · exact Filter.Eventually.of_forall fun _ h => absurd hpq h
    · -- witness: the reads of all blocks side by side are `E₀ W₀`, with a nonzero minor
      obtain ⟨E₀, W₀, hEW⟩ := exists_minor_ne_zero hk hk hpq
      let θ₀ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut :=
        ⟨0, fun ℓ => Matrix.of fun k i => (E₀ * W₀) k ⟨ℓ, i⟩, 0, 0⟩
      have hg : AnalyticOnNhd ℝ
          (fun θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut =>
            θ.read p.1 k₁ p.2 * θ.read q.1 k₂ q.2 - θ.read q.1 k₁ q.2 * θ.read p.1 k₂ p.2)
          Set.univ :=
        ((hR p.1 k₁ p.2).mul (hR q.1 k₂ q.2)).sub ((hR q.1 k₁ q.2).mul (hR p.1 k₂ p.2))
      exact (ae_ne_zero_of_analytic μ hg ⟨θ₀, hEW⟩).mono fun _ h _ => h
  filter_upwards [h1, h2, h3, h4] with θ h1 h2 h3 h4
  refine ⟨rank_eq_of_isUnit_det_rows_dtr θ.E ρ (h1.2.2.1 ρ),
    rank_eq_card_of_isUnit_det θ.D cD (h1.2.1 cD), fun ℓ i hi => h2 ℓ i (congrFun hi k₁),
    fun ℓ i hi => h3 ℓ i (congrFun hi k₁), ?_⟩
  -- if `c_p = r c_q`, the minor of the columns `p`, `q` vanishes
  intro p q hpq r hr
  have e1 : θ.read p.1 k₁ p.2 = r * θ.read q.1 k₁ q.2 := congrFun hr k₁
  have e2 : θ.read p.1 k₂ p.2 = r * θ.read q.1 k₂ q.2 := congrFun hr k₂
  apply h4 p q hpq
  rw [e1, e2]
  ring

/-- **The conditions of Lemma A.27 under pre-RMSNorm hold at generic parameters,** for
`d_in, d_out ≥ d ≥ 2`, heads of width `1 ≤ d_h ≤ d` and blocks of any widths. -/
theorem ae_smallWritesGeneric_attentionMlp_rmsNorm
    (μ : Measure (Params
      (Arch.attentionMlp (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ)) :
    ∀ᵐ θ ∂μ, SmallWritesGenericAttentionRMS θ.sumFst ∧ SmallWritesGenericRMS θ.sumSnd := by
  -- the conditions on the heads hold for the first part, those on the hidden units for the
  -- second part, of generic parameters of the sum (`Generic/Sum.lean`)
  filter_upwards [ae_sumFst μ
      (ae_smallWritesGenericAttentionRMS Measure.addHaar hd hdIn hdOut hdh hdh0),
    ae_sumSnd μ (ae_smallWritesGenericRMS_dtr Measure.addHaar hd hdIn hdOut)] with θ h1 h2
  exact ⟨h1, h2⟩

/-- **Theorem 4.7 of the skips paper for attention blocks and MLP blocks under pre-RMSNorm
(`ε > 0`):** with `d_in, d_out ≥ d ≥ 2`, heads of width `1 ≤ d_h ≤ d`, blocks of any widths and a
token that sees itself and another token, at almost every parameter the residual network has the
functional dimension `P − d(d−1)/2 − 2 ∑_ℓ H_ℓ d_{h,ℓ}²`. -/
theorem ae_funDim_attentionMlp_residual_rmsNorm (hε : 0 < ε)
    (hσ : ∀ z, HasDerivAt σ (σ' z) z) (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (hU : UnitsRigid σ σ' d d (Σ ℓ, hid ℓ))
    (μ : Measure (Params
      (Arch.attentionMlp (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ θ ∂μ, funDim (Arch.attentionMlp sees σ (rmsNorm ε) H dh hid) 1 θ
        + (Fintype.card d * (Fintype.card d - 1) / 2
          + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
      = Module.finrank ℝ
          (Params (Arch.attentionMlp (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut) := by
  have : Nonempty T := ⟨t₁⟩
  -- one parameter `θ₀` with the conditions of Lemma A.27, and one small `τ ≠ 0`:
  -- `fd(θ₀_τ) = P − d(d−1)/2 − s`
  obtain ⟨θ₀, hθa, hθm⟩ :=
    (ae_smallWritesGeneric_attentionMlp_rmsNorm μ hd hdIn hdOut hdh hdh0).exists
  obtain ⟨τ, hτ⟩ := (eventually_funDim_smallWrites_attentionMlp_rmsNorm hε hσ hσa hU t₁ t₂ h12
    hs2 hs1 θ₀ hθa hθm).exists
  -- at almost every `θ`, `fd(θ) ≥ fd(θ₀_τ)` (analytic outputs) and `fd(θ) ≤ P − d(d−1)/2 − s`
  filter_upwards [ae_funDim_ge (Arch.attentionMlp sees σ (rmsNorm ε) H dh hid) 1
      (fun ℓ => analyticOnNhd_f_sum (analyticOnNhd_f_attention (d := d) sees (rmsNorm ε) H dh ℓ)
        (analyticOnNhd_f_mlp hσa ℓ)) (analyticOnNhd_rmsNorm hε) μ (θ₀.smallWrites τ),
    ae_funDim_add_le_residual_attentionMlp_rmsNorm ε μ hdIn hdh] with θ h1 h2
  generalize Fintype.card d * (Fintype.card d - 1) / 2 = N at hτ h2 ⊢
  omega

/-- **Theorem 4.7, the gain, for attention blocks and MLP blocks under pre-RMSNorm
(`ε > 0`):** if moreover every block has total width `H d_h + d_hidden ≥ d`, at almost every
parameter the skips raise the functional dimension by at least `L d(d−1)/2`. -/
theorem ae_funDim_attentionMlp_residual_rmsNorm_ge_add (hε : 0 < ε)
    (hσ : ∀ z, HasDerivAt σ (σ' z) z) (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (hU : UnitsRigid σ σ' d d (Σ ℓ, hid ℓ))
    (μ : Measure (Params
      (Arch.attentionMlp (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (hW : ∀ ℓ,
      Fintype.card d ≤ Fintype.card (H ℓ) * Fintype.card (dh ℓ) + Fintype.card (hid ℓ))
    (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ θ ∂μ, funDim (Arch.attentionMlp sees σ (rmsNorm ε) H dh hid) 0 θ
        + L * (Fintype.card d * (Fintype.card d - 1) / 2)
      ≤ funDim (Arch.attentionMlp sees σ (rmsNorm ε) H dh hid) 1 θ := by
  -- `fd₁ = P − d(d−1)/2 − s` and `fd₀ ≤ P − (L + 1) d(d−1)/2 − s`
  filter_upwards [ae_funDim_attentionMlp_residual_rmsNorm hε hσ hσa hU μ hd hdIn hdOut hdh hdh0
      t₁ t₂ h12 hs2 hs1, ae_funDim_add_le_skipless_attentionMlp_rmsNorm ε μ hdIn hdh hW]
    with θ h1 h2
  rw [add_one_mul] at h2
  generalize Fintype.card d * (Fintype.card d - 1) / 2 = N at h1 h2 ⊢
  omega

/-- **Theorem 4.7 of the skips paper for attention blocks and tanh blocks under pre-RMSNorm
(`ε > 0`):** at almost every parameter the residual network has the functional dimension
`P − d(d−1)/2 − 2 ∑_ℓ H_ℓ d_{h,ℓ}²`. -/
theorem ae_funDim_attention_tanh_residual_rmsNorm (hε : 0 < ε)
    (μ : Measure (Params
      (Arch.attentionMlp (T := T) (d := d) sees Real.tanh (rmsNorm ε) H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ θ ∂μ, funDim (Arch.attentionMlp sees Real.tanh (rmsNorm ε) H dh hid) 1 θ
        + (Fintype.card d * (Fintype.card d - 1) / 2
          + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
      = Module.finrank ℝ
          (Params
          (Arch.attentionMlp (T := T) (d := d) sees Real.tanh (rmsNorm ε) H dh hid) dIn dOut) := by
  exact ae_funDim_attentionMlp_residual_rmsNorm hε hasDerivAt_tanh analyticOnNhd_tanh
    (tanh_unitsRigid _ _ _) μ hd hdIn hdOut hdh hdh0 t₁ t₂ h12 hs2 hs1

/-- **Theorem 4.7 of the skips paper for attention blocks and GELU blocks under pre-RMSNorm
(`ε > 0`):** at almost every parameter the residual network has the functional dimension
`P − d(d−1)/2 − 2 ∑_ℓ H_ℓ d_{h,ℓ}²`. -/
theorem ae_funDim_attention_gelu_residual_rmsNorm (hε : 0 < ε)
    (μ : Measure (Params
      (Arch.attentionMlp (T := T) (d := d) sees gelu (rmsNorm ε) H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ θ ∂μ, funDim (Arch.attentionMlp sees gelu (rmsNorm ε) H dh hid) 1 θ
        + (Fintype.card d * (Fintype.card d - 1) / 2
          + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
      = Module.finrank ℝ
          (Params
            (Arch.attentionMlp (T := T) (d := d) sees gelu (rmsNorm ε) H dh hid) dIn dOut) := by
  exact ae_funDim_attentionMlp_residual_rmsNorm hε hasDerivAt_gelu analyticOnNhd_gelu
    (gelu_unitsRigid _ _ _) μ hd hdIn hdOut hdh hdh0 t₁ t₂ h12 hs2 hs1

end Skips
