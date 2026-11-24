import SkipsLean.Residual.DepthAttentionDim
import SkipsLean.Residual.DepthGated
import SkipsLean.Dimension.UpperBoundTransformer
import SkipsLean.Generic.Sum

/-!
# Residual networks of attention blocks and gated blocks at any depth, without normalization

Paper (skips paper): Lemma A.27 (Small writes): "Let `d_model ≥ 2`, let `E` and `D` have rank
`d_model`, and let each block, in any order and of any width, be an attention block with heads of
width at most `d_model`, causal or not, on sequences of at least two tokens, or an MLP block, with
all MLP blocks tanh, all GELU, all SwiGLU or all GeGLU blocks. […] For all small `τ ≠ 0`, the
residual network has `fd(θ_τ) = P − d_model² − s` (no normalization, no biases)". Theorem 4.7
(Equality for residual networks at any depth): "Let the blocks be analytic, with or without
pre-RMSNorm. The residual network satisfies the equality condition: at generic parameters its
functional dimension is `P − dim G − s`. So the skips raise the functional dimension by at least
`L dim G`".

The proof of Lemma A.27 for attention blocks: "First take an input whose tokens all equal `x`.
Head `i` then gives every token the output `x C_i`, whatever its scores are, so `ψ_{B_i}` does not
enter […]. This is `D_φ G(φ, x) ψ` with `M + ∑_i C_i` in place of `M`, so for a flat `η`
Lemma B.3 gives a rescaling at every unit. The terms of the units then vanish at every input:
they act on each token separately, and they are the derivative along a rescaling, which does not
change the function. Next take an input whose tokens other than the second all equal the first.
[…] So Step 2 for attention blocks in Appendix B gives `ψ_M = 0`, `ψ_{B_i} = 0` and
`ψ_{C_i} = 0` for every head."

Here for `Arch.attentionGated sees σ id H dh hid` (`Network/Transformer.lean`): `L` blocks, block
`ℓ` with the heads `H ℓ` of width `dh ℓ` and the hidden units `hid ℓ` (an attention block if `hid
ℓ` is empty, a gated block if `H ℓ` is empty), without normalization, with a token `t₂` that sees
itself and another token `t₁`; stated for every gate that satisfies the conclusion of Lemma B.3
(`GatedUnitsRescale`) for the hidden units of all blocks together. The conditions on `θ` are those
of the two kinds of block, on the two parts of the parameters: `SmallWritesGenericAttention
θ.sumFst` (`Residual/DepthAttention.lean`) and `SmallWritesGenericGated θ.sumSnd`
(`Residual/DepthGated.lean`). For a block without heads `dh ℓ` is any nonempty type.

* `smallWritesLimit_eq_zero_attentionGated`: the flat directions of `J_0`;
* `eventually_funDim_smallWrites_attentionGated`: `fd(θ_τ) = P − d² − s` for all small `τ ≠ 0`,
  `s = 2 ∑_ℓ H_ℓ d_{h,ℓ}² + ∑_ℓ d_hidden,ℓ`;
* `ae_smallWritesGeneric_attentionGated`: the conditions at generic parameters;
* `ae_funDim_attentionGated_residual`: Theorem 4.7, and `…_ge_add`: the gain of at least `L d²` for
  blocks of total width `H d_h + d_hidden ≥ d`;
* the named kinds: attention with SwiGLU blocks, attention with GeGLU blocks.
-/

namespace Skips

open Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {sees : T → T → Prop} [DecidableRel sees]
variable {H dh hid : Fin L → Type} [∀ ℓ, Fintype (H ℓ)] [∀ ℓ, Fintype (dh ℓ)]
  [∀ ℓ, Fintype (hid ℓ)] {σ σ' : ℝ → ℝ}

/-! ### Helpers: lines and linear algebra -/

/-- Helper (as `hasDerivAt_lineDG` of `Residual/DepthGated.lean`): the line `τ ↦ a + τ b` has
the velocity `b`. -/
private theorem hasDerivAt_line_dtg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a b : E) : HasDerivAt (fun τ : ℝ => a + τ • b) b 0 := by
  have h := ((hasDerivAt_id (0 : ℝ)).smul_const b).const_add a
  rw [one_smul] at h
  exact h

/-- Helper (as `hasDerivAt_affineDG` of `Residual/DepthGated.lean`): `τ ↦ a + τ b` has the
derivative `b` at `0`, in `ℝ`. -/
private theorem hasDerivAt_affine_dtg (a b : ℝ) : HasDerivAt (fun τ : ℝ => a + τ * b) b 0 := by
  have h := ((hasDerivAt_id' (x := (0 : ℝ))).mul_const b).const_add a
  rw [one_mul] at h
  exact h

/-- Helper (the private `cancel_left_of_rank_dg` of `Residual/DepthGated.lean`): a matrix whose
rank is its number of columns cancels on the left, via a left inverse. -/
private theorem cancel_left_of_rank_dtg {m n k : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (M : Matrix m n ℝ) (hM : M.rank = Fintype.card n) {X Y : Matrix n k ℝ}
    (h : M * X = M * Y) : X = Y := by
  obtain ⟨B, hB⟩ := Matrix.vecMul_surjective_iff_exists_left_inverse.mp
    (Matrix.vecMul_surjective_iff_rank_eq_card.mpr hM)
  have := congrArg (B * ·) h
  simpa only [← Matrix.mul_assoc, hB, Matrix.one_mul] using this

/-- Helper (the private `cancel_right_of_rank_dg` of `Residual/DepthGated.lean`): a matrix whose
rank is its number of rows cancels on the right, via a right inverse. -/
private theorem cancel_right_of_rank_dtg {m n k : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] (M : Matrix m n ℝ) (hM : M.rank = Fintype.card m) {X Y : Matrix k m ℝ}
    (h : X * M = Y * M) : X = Y := by
  obtain ⟨R, hR⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.mp
    (Matrix.mulVec_surjective_iff_rank_eq_card.mpr hM)
  have := congrArg (· * R) h
  simpa only [Matrix.mul_assoc, hR, Matrix.mul_one] using this

omit [Fintype T] in
/-- Helper: if the rows of `x` are all equal, so are the rows of `x Q`. -/
private theorem mul_row_eq_dtg {m n : Type*} [Fintype m] {x : Matrix T m ℝ} {t : T}
    (hx : ∀ s, x s = x t) (Q : Matrix m n ℝ) (s : T) : (x * Q) s = (x * Q) t := by
  funext c
  rw [Matrix.mul_apply, Matrix.mul_apply, hx s]

/-! ### Helpers: the gated blocks (copies of private helpers of `Residual/DepthGated.lean`) -/

omit [Fintype d] [DecidableEq d] in
/-- Helper (the private `fderiv_f_gated_apply` of `Residual/DepthGated.lean`): the derivative of
the map of a gated block at `M` along `N`: entry `(t, i)` is
`σ'(M_{t, g i}) N_{t, g i} M_{t, v i} + σ(M_{t, g i}) N_{t, v i}`. -/
private theorem fderiv_f_gated_apply_dtg (hσ : ∀ z, HasDerivAt σ (σ' z) z) (ℓ : Fin L)
    (M N : Matrix T (hid ℓ ⊕ hid ℓ) ℝ) (t : T) (i : hid ℓ) :
    fderiv ℝ ((Arch.gated (T := T) (d := d) σ id hid).f ℓ) M N t i
      = σ' (M t (Sum.inl i)) * N t (Sum.inl i) * M t (Sum.inr i)
        + σ (M t (Sum.inl i)) * N t (Sum.inr i) := by
  have hd := differentiable_f_gated (T := T) (d := d) (χ := id) (hid := hid)
    (fun z => (hσ z).differentiableAt) ℓ
  -- the chain rule along the line `τ ↦ M + τ N`
  have h1 := (hd M).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) (hasDerivAt_line_dtg M N)
    (by rw [zero_smul, add_zero])
  have h2 := hasDerivAt_pi.1 (hasDerivAt_pi.1 h1 t) i
  -- the same derivative computed on the entry `(t, i)`
  have h3 : HasDerivAt (fun τ : ℝ => σ (M t (Sum.inl i) + τ * N t (Sum.inl i))
      * (M t (Sum.inr i) + τ * N t (Sum.inr i)))
      (σ' (M t (Sum.inl i)) * N t (Sum.inl i) * M t (Sum.inr i)
        + σ (M t (Sum.inl i)) * N t (Sum.inr i)) 0 := by
    have hu := hasDerivAt_affine_dtg (M t (Sum.inl i)) (N t (Sum.inl i))
    have hw := hasDerivAt_affine_dtg (M t (Sum.inr i)) (N t (Sum.inr i))
    have h := ((hσ _).comp (0 : ℝ) hu).mul hw
    convert h using 1
    · rfl
    · simp only [Function.comp_apply, zero_mul, add_zero]
  exact h2.unique h3

omit [DecidableEq d] [Fintype dOut] in
/-- Helper (the private `smallWritesLimit_gated_apply` of `Residual/DepthGated.lean`): the entries
of `(J_0 η)(x)` for gated blocks:
`(x ψ_M)_{t o} + ∑_ℓ ∑_i [σ(z) w (ψ_A)_{i o} + σ'(z) (x ψ_C)_{t, g i} w A_{i o}
+ σ(z) (x ψ_C)_{t, v i} A_{i o}]`, with `z = (x C)_{t, g i}`, `w = (x C)_{t, v i}`. -/
private theorem smallWritesLimit_gated_apply_dtg (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (θ η : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) (x : Matrix T dIn ℝ)
    (t : T) (o : dOut) :
    smallWritesLimit (Arch.gated σ id hid) θ η x t o
      = (x * (η.E * θ.D + θ.E * η.D)) t o + ∑ ℓ, ∑ i : hid ℓ,
        (σ ((x * (θ.E * θ.read ℓ)) t (Sum.inl i)) * (x * (θ.E * θ.read ℓ)) t (Sum.inr i)
            * (η.write ℓ * θ.D) i o
          + σ' ((x * (θ.E * θ.read ℓ)) t (Sum.inl i)) * (x * (θ.E * η.read ℓ)) t (Sum.inl i)
            * (x * (θ.E * θ.read ℓ)) t (Sum.inr i) * (θ.write ℓ * θ.D) i o
          + σ ((x * (θ.E * θ.read ℓ)) t (Sum.inl i)) * (x * (θ.E * η.read ℓ)) t (Sum.inr i)
            * (θ.write ℓ * θ.D) i o) := by
  unfold smallWritesLimit
  rw [Matrix.add_apply, Matrix.sum_apply]
  congr 1
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc _ (η.write ℓ), Matrix.add_apply,
    Matrix.mul_apply, Matrix.mul_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [fderiv_f_gated_apply_dtg hσ, Matrix.mul_assoc x θ.E (θ.read ℓ),
    Matrix.mul_assoc x θ.E (η.read ℓ)]
  have hf : (Arch.gated (T := T) (d := d) σ id hid).f ℓ (x * (θ.E * θ.read ℓ)) t i
      = σ ((x * (θ.E * θ.read ℓ)) t (Sum.inl i)) * (x * (θ.E * θ.read ℓ)) t (Sum.inr i) := rfl
  rw [hf]
  ring

/-! ### Helpers: the attention blocks at an input whose tokens are all equal -/

/-- Helper (as `attnWeights_sum_rat` of `Absorb/RMSNormAttention.lean`): row `t` of the weights
sums to `1` when token `t` sees some token (the denominator is positive). -/
private theorem attnWeights_sum_dtg (Z : Matrix T T ℝ) (t : T) (ht : ∃ s, sees t s) :
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

omit [Fintype d] [DecidableEq d] in
/-- Helper (as `f_attention_entry_const_rat` of `Absorb/RMSNormAttention.lean`): if the value
coordinate `k` of head `i` is the same number `v` at every token, entry `(t, (i, k))` of the
output of the block is `v` when token `t` sees some token. -/
private theorem f_attention_entry_const_dtg (ℓ : Fin L)
    (M : Matrix T (H ℓ × (dh ℓ ⊕ (dh ℓ ⊕ dh ℓ))) ℝ) (i : H ℓ) (k : dh ℓ) (v : ℝ)
    (hv : ∀ s, M s (i, Sum.inr (Sum.inr k)) = v) (t s : T) (hts : sees t s) :
    (Arch.attention (T := T) (d := d) sees id H dh).f ℓ M t (i, k) = v := by
  show ∑ s', attnWeights sees _ t s' * M s' (i, Sum.inr (Sum.inr k)) = v
  simp only [hv, ← Finset.sum_mul, attnWeights_sum_dtg _ t ⟨s, hts⟩, one_mul]

omit [Fintype d] [DecidableEq d] in
/-- Helper: at a hidden state whose rows are all equal, along a direction whose rows are all
equal, the derivative of an attention block gives a token that sees itself the value part of the
direction (along the line the rows stay equal, so every head returns their common value). -/
private theorem fderiv_f_attention_const_dtg (ℓ : Fin L)
    (M N : Matrix T (H ℓ × (dh ℓ ⊕ (dh ℓ ⊕ dh ℓ))) ℝ) (t : T) (ht : sees t t)
    (hM : ∀ s, M s = M t) (hN : ∀ s, N s = N t) (i : H ℓ) (k : dh ℓ) :
    fderiv ℝ ((Arch.attention (T := T) (d := d) sees id H dh).f ℓ) M N t (i, k)
      = N t (i, Sum.inr (Sum.inr k)) := by
  -- the chain rule along the line `τ ↦ M + τ N`
  have h1 := ((differentiable_f_attention (d := d) sees id H dh ℓ) M).hasFDerivAt
    |>.comp_hasDerivAt_of_eq (0 : ℝ) (hasDerivAt_line_dtg M N) (by rw [zero_smul, add_zero])
  have h2 := hasDerivAt_pi.1 (hasDerivAt_pi.1 h1 t) (i, k)
  -- on the line, entry `(t, (i, k))` is `M_{t, v} + τ N_{t, v}`
  have h3 : HasDerivAt (fun τ : ℝ =>
      (Arch.attention (T := T) (d := d) sees id H dh).f ℓ (M + τ • N) t (i, k))
      (N t (i, Sum.inr (Sum.inr k))) 0 := by
    have he : (fun τ : ℝ =>
        (Arch.attention (T := T) (d := d) sees id H dh).f ℓ (M + τ • N) t (i, k))
        = fun τ => M t (i, Sum.inr (Sum.inr k)) + τ * N t (i, Sum.inr (Sum.inr k)) := by
      funext τ
      refine f_attention_entry_const_dtg ℓ _ i k _ (fun s => ?_) t t ht
      show M s (i, Sum.inr (Sum.inr k)) + τ * N s (i, Sum.inr (Sum.inr k)) = _
      rw [hM s, hN s]
    rw [he]
    exact hasDerivAt_affine_dtg _ _
  exact h2.unique h3

/-- Helper: the value columns `W_V` of the read of block `ℓ` of an attention network, one column
for each head and each coordinate of its value. -/
private def valueRead_dtg
    (θ : Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut) (ℓ : Fin L) :
    Matrix d (H ℓ × dh ℓ) ℝ :=
  Matrix.of fun k p => θ.read ℓ k (p.1, Sum.inr (Sum.inr p.2))

omit [DecidableEq d] [Fintype dOut] in
/-- Helper ("head `i` then gives every token the output `x C_i`, whatever its scores are"): at an
input whose rows are all equal, row `t` of `(J_0 η)(x)`, for a token `t` that sees itself, is
row `t` of `x (ψ_M + ∑_ℓ (E η_V W_O + E W_V η_O) D)`. -/
private theorem smallWritesLimit_attention_const_dtg (t : T) (ht : sees t t)
    (θ η : Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut)
    (x : Matrix T dIn ℝ) (hx : ∀ s, x s = x t) :
    smallWritesLimit (Arch.attention sees id H dh) θ η x t
      = (x * (η.E * θ.D + θ.E * η.D + ∑ ℓ, (θ.E * valueRead_dtg η ℓ * θ.write ℓ
          + θ.E * valueRead_dtg θ ℓ * η.write ℓ) * θ.D)) t := by
  funext o
  unfold smallWritesLimit
  rw [Matrix.add_apply, Matrix.sum_apply, Matrix.mul_add x (η.E * θ.D + θ.E * η.D),
    Matrix.add_apply, Matrix.mul_sum, Matrix.sum_apply]
  congr 1
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  -- the rows of `x E W_read` and of `x E η_read` are all equal
  have hM := mul_row_eq_dtg (mul_row_eq_dtg hx θ.E) (θ.read ℓ)
  have hN := mul_row_eq_dtg (mul_row_eq_dtg hx θ.E) (η.read ℓ)
  -- row `t` of block `ℓ` before `D`: every head gives token `t` its value
  have hF : (fderiv ℝ ((Arch.attention (T := T) (d := d) sees id H dh).f ℓ)
        (x * θ.E * θ.read ℓ) (x * θ.E * η.read ℓ) * θ.write ℓ
      + (Arch.attention (T := T) (d := d) sees id H dh).f ℓ (x * θ.E * θ.read ℓ)
        * η.write ℓ) t
      = (x * θ.E * valueRead_dtg η ℓ * θ.write ℓ
        + x * θ.E * valueRead_dtg θ ℓ * η.write ℓ) t := by
    funext j
    rw [Matrix.add_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply,
      Matrix.mul_apply, Matrix.mul_apply]
    congr 1
    · refine Finset.sum_congr rfl fun p _ => ?_
      obtain ⟨i, k⟩ := p
      rw [fderiv_f_attention_const_dtg ℓ _ _ t ht hM hN i k]
      rfl
    · refine Finset.sum_congr rfl fun p _ => ?_
      obtain ⟨i, k⟩ := p
      rw [f_attention_entry_const_dtg ℓ _ i k _ (fun s => congrFun (hM s) _) t t ht]
      rfl
  have hA : x * ((θ.E * valueRead_dtg η ℓ * θ.write ℓ + θ.E * valueRead_dtg θ ℓ * η.write ℓ)
      * θ.D) = (x * θ.E * valueRead_dtg η ℓ * θ.write ℓ
        + x * θ.E * valueRead_dtg θ ℓ * η.write ℓ) * θ.D := by
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
  rw [hA, Matrix.mul_apply, Matrix.mul_apply, hF]

/-! ### Helpers: `J_0` of a network with two kinds of block -/

omit [Fintype d] [DecidableEq d] in
/-- Helper: the derivative of the map of a block of `A.sum B`, at the entries of the first part:
the derivative of the map of block `ℓ` of `A` on the first part. -/
private theorem fderiv_f_sum_inl_dtg {A B : Arch T d L} (hA : ∀ ℓ, Differentiable ℝ (A.f ℓ))
    (hB : ∀ ℓ, Differentiable ℝ (B.f ℓ)) (ℓ : Fin L) (M N : Matrix T (A.r ℓ ⊕ B.r ℓ) ℝ)
    (t : T) (a : A.w ℓ) :
    fderiv ℝ ((A.sum B).f ℓ) M N t (Sum.inl a)
      = fderiv ℝ (A.f ℓ) (M.submatrix id Sum.inl) (N.submatrix id Sum.inl) t a := by
  -- the chain rule along the line `τ ↦ M + τ N`, and along its first part
  have h1 := ((differentiable_f_sum (hA ℓ) (hB ℓ)) M).hasFDerivAt.comp_hasDerivAt_of_eq
    (0 : ℝ) (hasDerivAt_line_dtg M N) (by rw [zero_smul, add_zero])
  have h2 := hasDerivAt_pi.1 (hasDerivAt_pi.1 h1 t) (Sum.inl a)
  have h3 := ((hA ℓ) (M.submatrix id Sum.inl)).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ)
    (hasDerivAt_line_dtg (M.submatrix id Sum.inl) (N.submatrix id Sum.inl))
    (by rw [zero_smul, add_zero])
  have h4 := hasDerivAt_pi.1 (hasDerivAt_pi.1 h3 t) a
  exact h2.unique h4

omit [Fintype d] [DecidableEq d] in
/-- Helper: the derivative of the map of a block of `A.sum B`, at the entries of the second
part: the derivative of the map of block `ℓ` of `B` on the second part. -/
private theorem fderiv_f_sum_inr_dtg {A B : Arch T d L} (hA : ∀ ℓ, Differentiable ℝ (A.f ℓ))
    (hB : ∀ ℓ, Differentiable ℝ (B.f ℓ)) (ℓ : Fin L) (M N : Matrix T (A.r ℓ ⊕ B.r ℓ) ℝ)
    (t : T) (b : B.w ℓ) :
    fderiv ℝ ((A.sum B).f ℓ) M N t (Sum.inr b)
      = fderiv ℝ (B.f ℓ) (M.submatrix id Sum.inr) (N.submatrix id Sum.inr) t b := by
  have h1 := ((differentiable_f_sum (hA ℓ) (hB ℓ)) M).hasFDerivAt.comp_hasDerivAt_of_eq
    (0 : ℝ) (hasDerivAt_line_dtg M N) (by rw [zero_smul, add_zero])
  have h2 := hasDerivAt_pi.1 (hasDerivAt_pi.1 h1 t) (Sum.inr b)
  have h3 := ((hB ℓ) (M.submatrix id Sum.inr)).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ)
    (hasDerivAt_line_dtg (M.submatrix id Sum.inr) (N.submatrix id Sum.inr))
    (by rw [zero_smul, add_zero])
  have h4 := hasDerivAt_pi.1 (hasDerivAt_pi.1 h3 t) b
  exact h2.unique h4

omit [DecidableEq d] in
/-- Helper (as `f_sum_mul` for the derivative): the derivative of block `ℓ` of `A.sum B` at
`h R` along `h N`, followed by the write `W`, is the sum of those of the two parts. -/
private theorem fderiv_sum_mul_dtg {A B : Arch T d L} (hA : ∀ ℓ, Differentiable ℝ (A.f ℓ))
    (hB : ∀ ℓ, Differentiable ℝ (B.f ℓ)) (ℓ : Fin L) (h : Matrix T d ℝ)
    (R N : Matrix d (A.r ℓ ⊕ B.r ℓ) ℝ) (W : Matrix (A.w ℓ ⊕ B.w ℓ) d ℝ) :
    fderiv ℝ ((A.sum B).f ℓ) (h * R) (h * N) * W
      = fderiv ℝ (A.f ℓ) (h * R.submatrix id Sum.inl) (h * N.submatrix id Sum.inl)
          * W.submatrix Sum.inl id
        + fderiv ℝ (B.f ℓ) (h * R.submatrix id Sum.inr) (h * N.submatrix id Sum.inr)
          * W.submatrix Sum.inr id := by
  -- entry `(t, a)`: the sum over the rows of `W` splits into the rows of `W_A` and of `W_B`
  ext t a
  simp only [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.add_apply, Matrix.submatrix_apply,
    id, fderiv_f_sum_inl_dtg hA hB, fderiv_f_sum_inr_dtg hA hB]
  rfl

omit [DecidableEq d] [Fintype dOut] in
/-- Helper: for a network of `A.sum B`, `J_0` is the sum of the `J_0` of its two parts, less one
copy of the term `x (η_E D + E η_D)` that both contain. -/
private theorem smallWritesLimit_sum_dtg {A B : Arch T d L}
    (hA : ∀ ℓ, Differentiable ℝ (A.f ℓ)) (hB : ∀ ℓ, Differentiable ℝ (B.f ℓ))
    (θ η : Params (A.sum B) dIn dOut) (x : Matrix T dIn ℝ) :
    smallWritesLimit (A.sum B) θ η x + x * (η.E * θ.D + θ.E * η.D)
      = smallWritesLimit A θ.sumFst η.sumFst x + smallWritesLimit B θ.sumSnd η.sumSnd x := by
  -- block `ℓ`: its derivative and its output split into those of the two parts
  have hblock : ∀ ℓ, (fderiv ℝ ((A.sum B).f ℓ) (x * θ.E * θ.read ℓ) (x * θ.E * η.read ℓ)
        * θ.write ℓ + (A.sum B).f ℓ (x * θ.E * θ.read ℓ) * η.write ℓ) * θ.D
      = (fderiv ℝ (A.f ℓ) (x * θ.E * (θ.read ℓ).submatrix id Sum.inl)
            (x * θ.E * (η.read ℓ).submatrix id Sum.inl) * (θ.write ℓ).submatrix Sum.inl id
          + A.f ℓ (x * θ.E * (θ.read ℓ).submatrix id Sum.inl)
            * (η.write ℓ).submatrix Sum.inl id) * θ.D
        + (fderiv ℝ (B.f ℓ) (x * θ.E * (θ.read ℓ).submatrix id Sum.inr)
            (x * θ.E * (η.read ℓ).submatrix id Sum.inr) * (θ.write ℓ).submatrix Sum.inr id
          + B.f ℓ (x * θ.E * (θ.read ℓ).submatrix id Sum.inr)
            * (η.write ℓ).submatrix Sum.inr id) * θ.D := by
    intro ℓ
    rw [fderiv_sum_mul_dtg hA hB, f_sum_mul, ← Matrix.add_mul]
    congr 1
    abel
  unfold smallWritesLimit
  rw [Finset.sum_congr rfl fun ℓ _ => hblock ℓ, Finset.sum_add_distrib]
  simp only [Params.sumFst, Params.sumSnd]
  abel

/-- **Proof of Lemma A.27, attention blocks and gated blocks without normalization, the flat
directions of `J_0`:** let token `t₂` see itself and another token `t₁`. Under the conditions of
the lemma, a direction `η` with `(J_0 η)(x) = 0` at every input `x` has `η_E = E X` and
`η_D = −X D` for one matrix `X`; in every block the reads and the writes of its heads are those
of the directions of the changes of basis inside the heads, and
it vanishes at the gate columns of the hidden units and rescales every hidden unit (the value
column of unit `i` of block `ℓ` by `−α_{ℓ,i}`, its write row by `α_{ℓ,i}`). -/
theorem smallWritesLimit_eq_zero_attentionGated (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hU : GatedUnitsRescale σ σ' dIn dOut (Σ ℓ, hid ℓ))
    (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁)
    (θ : Params (Arch.attentionGated (T := T) (d := d) sees σ id H dh hid) dIn dOut)
    (hθa : SmallWritesGenericAttention θ.sumFst) (hθm : SmallWritesGenericGated θ.sumSnd)
    (η : Params (Arch.attentionGated (T := T) (d := d) sees σ id H dh hid) dIn dOut)
    (hη : ∀ x, smallWritesLimit (Arch.attentionGated sees σ id H dh hid) θ η x = 0) :
    ∃ (X : Matrix d d ℝ) (Γ Γ' : ∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) (α : ∀ ℓ, hid ℓ → ℝ),
      η.E = θ.E * X ∧ η.D = -(X * θ.D)
        ∧ (∀ ℓ, η.sumFst.read ℓ = (headDirQK θ.sumFst Γ + headDirVO θ.sumFst Γ').read ℓ)
        ∧ (∀ ℓ, η.sumFst.write ℓ = (headDirQK θ.sumFst Γ + headDirVO θ.sumFst Γ').write ℓ)
        ∧ (∀ ℓ (i : hid ℓ) a, η.sumSnd.read ℓ a (Sum.inl i) = 0)
        ∧ (∀ ℓ (i : hid ℓ) a,
          η.sumSnd.read ℓ a (Sum.inr i) = -(α ℓ i) * θ.sumSnd.read ℓ a (Sum.inr i))
        ∧ (∀ ℓ (i : hid ℓ) a, η.sumSnd.write ℓ i a = α ℓ i * θ.sumSnd.write ℓ i a) := by
  classical
  have hdA : ∀ ℓ, Differentiable ℝ ((Arch.attention (T := T) (d := d) sees id H dh).f ℓ) :=
    fun ℓ => differentiable_f_attention (d := d) sees id H dh ℓ
  have hdB : ∀ ℓ, Differentiable ℝ ((Arch.gated (T := T) (d := d) σ id hid).f ℓ) :=
    fun ℓ => differentiable_f_gated (fun z => (hσ z).differentiableAt) ℓ
  -- `J_0` of the network is that of its heads plus that of its hidden units, less `x ψ_M`
  have hsplit : ∀ x, smallWritesLimit (Arch.attention sees id H dh) θ.sumFst η.sumFst x
      + smallWritesLimit (Arch.gated σ id hid) θ.sumSnd η.sumSnd x
      = x * (η.E * θ.D + θ.E * η.D) := by
    intro x
    have h := smallWritesLimit_sum_dtg hdA hdB θ η x
    rw [hη x, zero_add] at h
    exact h.symm
  -- Step 1 (equal tokens): at the input whose rows all equal `v`, row `t₂` is
  -- `v (ψ_M + ∑_p ψ_{C_p})` plus the terms of the hidden units, so Lemma B.3 for the hidden units
  -- of all blocks together, with `M + ∑ C` in the place of `M`: the gate columns of `E η_read`
  -- vanish and every unit only rescales its value
  obtain ⟨-, -, hc, -, α, hα⟩ := hU
    (fun p => (θ.sumSnd.E * θ.sumSnd.read p.1)ᵀ (Sum.inl p.2)) 0
    (fun p => (θ.sumSnd.E * θ.sumSnd.read p.1)ᵀ (Sum.inr p.2)) 0
    (fun p => (θ.sumSnd.write p.1 * θ.sumSnd.D) p.2)
    (η.E * θ.D + θ.E * η.D + ∑ ℓ, (θ.E * valueRead_dtg η.sumFst ℓ * θ.sumFst.write ℓ
      + θ.E * valueRead_dtg θ.sumFst ℓ * η.sumFst.write ℓ) * θ.D) 0
    (fun p => (θ.sumSnd.E * η.sumSnd.read p.1)ᵀ (Sum.inl p.2)) 0
    (fun p => (θ.sumSnd.E * η.sumSnd.read p.1)ᵀ (Sum.inr p.2)) 0
    (fun p => (η.sumSnd.write p.1 * θ.sumSnd.D) p.2)
    (fun p => hθm.row_ne_zero p.1 p.2) (fun p => hθm.gate_ne_zero p.1 p.2)
    (fun p q hpq => hθm.gate_not_collinear p q hpq) (fun p => hθm.value_ne_zero p.1 p.2) (by
      intro v
      funext o
      have h := congrFun (congrFun (hsplit (Matrix.of fun _ => v)) t₂) o
      rw [Matrix.add_apply, smallWritesLimit_attention_const_dtg t₂ hs2 _ _ _ (fun _ => rfl),
        smallWritesLimit_gated_apply_dtg hσ] at h
      have key : ∀ a b c : ℝ, a + (b + c) = b → a + c = 0 := fun a b c h => by linarith
      have h' := key _ _ _ h
      simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
        add_zero]
      rw [Fintype.sum_sigma]
      exact h')
  -- Step 2: the terms of the hidden units vanish at every input (gate direction `0`, value
  -- direction `−α` times the value, write direction `α` times the write)
  have hgat : ∀ x : Matrix T dIn ℝ, smallWritesLimit (Arch.gated σ id hid) θ.sumSnd η.sumSnd x
      = x * (η.E * θ.D + θ.E * η.D) := by
    intro x
    ext t o
    rw [smallWritesLimit_gated_apply_dtg hσ]
    refine add_eq_left.2 (Finset.sum_eq_zero fun ℓ _ => Finset.sum_eq_zero fun i _ => ?_)
    have g0 : (x * (θ.sumSnd.E * η.sumSnd.read ℓ)) t (Sum.inl i) = 0 := by
      rw [Matrix.mul_apply]
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [show (θ.sumSnd.E * η.sumSnd.read ℓ) k (Sum.inl i) = 0 from
        congrFun (congrFun hc ⟨ℓ, i⟩) k, mul_zero]
    have v0 : (x * (θ.sumSnd.E * η.sumSnd.read ℓ)) t (Sum.inr i)
        = -(α ⟨ℓ, i⟩) * (x * (θ.sumSnd.E * θ.sumSnd.read ℓ)) t (Sum.inr i) := by
      rw [Matrix.mul_apply, Matrix.mul_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [show (θ.sumSnd.E * η.sumSnd.read ℓ) k (Sum.inr i)
        = -(α ⟨ℓ, i⟩) * (θ.sumSnd.E * θ.sumSnd.read ℓ) k (Sum.inr i) from
        congrFun (hα ⟨ℓ, i⟩).1 k]
      ring
    have w0 : (η.sumSnd.write ℓ * θ.sumSnd.D) i o
        = α ⟨ℓ, i⟩ * (θ.sumSnd.write ℓ * θ.sumSnd.D) i o := congrFun (hα ⟨ℓ, i⟩).2.2 o
    rw [g0, v0, w0]
    ring
  -- so the heads alone have `J_0 η = 0` at every input, and Step 2 for attention blocks applies
  have hattn : ∀ x, smallWritesLimit (Arch.attention sees id H dh) θ.sumFst η.sumFst x = 0 := by
    intro x
    have h := hsplit x
    rw [hgat x] at h
    exact add_eq_right.1 h
  obtain ⟨X, Γ, Γ', hE, hD, hr, hw⟩ :=
    smallWritesLimit_eq_zero_attention t₁ t₂ h12 hs2 hs1 θ.sumFst hθa η.sumFst hattn
  -- the reads of the hidden units: `E η_read = E R'` with `R'` the rescaled value columns, and `E`
  -- cancels
  have hread : ∀ ℓ, η.sumSnd.read ℓ = Matrix.of fun k j =>
      Sum.elim (fun _ => 0) (fun i => -(α ⟨ℓ, i⟩) * θ.sumSnd.read ℓ k (Sum.inr i)) j := by
    intro ℓ
    apply cancel_left_of_rank_dtg θ.sumSnd.E hθm.rank_E
    ext a j
    rcases j with i | i
    · have h1 : (θ.sumSnd.E * η.sumSnd.read ℓ) a (Sum.inl i) = 0 :=
        congrFun (congrFun hc ⟨ℓ, i⟩) a
      rw [h1, Matrix.mul_apply]
      exact (Finset.sum_eq_zero fun k _ => mul_zero (θ.sumSnd.E a k)).symm
    · have h1 : (θ.sumSnd.E * η.sumSnd.read ℓ) a (Sum.inr i)
          = -(α ⟨ℓ, i⟩) * (θ.sumSnd.E * θ.sumSnd.read ℓ) a (Sum.inr i) :=
        congrFun (hα ⟨ℓ, i⟩).1 a
      rw [h1, Matrix.mul_apply, Matrix.mul_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      show _ = θ.sumSnd.E a k * (-(α ⟨ℓ, i⟩) * θ.sumSnd.read ℓ k (Sum.inr i))
      ring
  -- the writes of the hidden units: `η_write D = W' D` with `W'` the rescaled rows, and `D`
  -- cancels
  have hwrite : ∀ ℓ, η.sumSnd.write ℓ = Matrix.of fun i k => α ⟨ℓ, i⟩ * θ.sumSnd.write ℓ i k := by
    intro ℓ
    apply cancel_right_of_rank_dtg θ.sumSnd.D hθm.rank_D
    ext i o
    have h1 : (η.sumSnd.write ℓ * θ.sumSnd.D) i o
        = α ⟨ℓ, i⟩ * (θ.sumSnd.write ℓ * θ.sumSnd.D) i o :=
      congrFun (hα ⟨ℓ, i⟩).2.2 o
    rw [h1, Matrix.mul_apply, Matrix.mul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    show _ = α ⟨ℓ, i⟩ * θ.sumSnd.write ℓ i k * θ.sumSnd.D k o
    ring
  refine ⟨X, Γ, Γ', fun ℓ i => α ⟨ℓ, i⟩, hE, hD, hr, hw, fun ℓ i a => ?_, fun ℓ i a => ?_,
    fun ℓ i a => ?_⟩
  · rw [hread ℓ]
    rfl
  · rw [hread ℓ]
    rfl
  · rw [hwrite ℓ]
    rfl

/-! ### Helpers: the space of the flat directions of `J_0` -/

omit [Fintype T] [DecidableEq d] [Fintype dIn] in
/-- Helper (as `flatEDLin_dpa` of `Residual/DepthAttention.lean`): the directions
`X ↦ (E X, 0, 0, −X D)` of one change of basis at all hidden states, as a linear map. -/
private def flatEDLin_dtg {A : Arch T d L} (θ : Params A dIn dOut) :
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

/-- Helper (as `headDirQKLin_dpa` of `Residual/DepthAttention.lean`): `Γ ↦ headDirQK θ Γ` is
linear. -/
private noncomputable def headDirQKLin_dtg
    (θ : Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut) :
    (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) →ₗ[ℝ]
      Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut where
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

/-- Helper (as `headDirVOLin_dpa` of `Residual/DepthAttention.lean`): `Γ' ↦ headDirVO θ Γ'` is
linear. -/
private noncomputable def headDirVOLin_dtg
    (θ : Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut) :
    (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) →ₗ[ℝ]
      Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut where
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

/-- Helper (as `rescaleDirLin_ubt` of `Dimension/UpperBoundTransformer.lean`):
`α ↦ rescaleDir θ α` is linear. -/
private noncomputable def rescaleDirLin_dtg
    (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) :
    (∀ ℓ, hid ℓ → ℝ) →ₗ[ℝ] Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut where
  toFun := rescaleDir θ
  map_add' α β := by
    apply Params.ext'
    · simp [rescaleDir]
    · intro ℓ
      ext k j
      cases j with
      | inl i => simp [rescaleDir]
      | inr i =>
        simp only [rescaleDir, Pi.add_apply, Params.add_read, Matrix.add_apply, Matrix.of_apply,
          Sum.elim_inr]
        ring
    · intro ℓ
      ext i k
      simp [rescaleDir, add_mul]
    · simp [rescaleDir]
  map_smul' c α := by
    apply Params.ext'
    · simp [rescaleDir]
    · intro ℓ
      ext k j
      cases j <;> simp [rescaleDir, mul_assoc]
    · intro ℓ
      ext i k
      simp [rescaleDir, mul_assoc]
    · simp [rescaleDir]

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: `η ↦ sumInl η`, a direction of `A` as a direction of `A.sum B`, is linear. -/
private def sumInlLin_dtg {A B : Arch T d L} :
    Params A dIn dOut →ₗ[ℝ] Params (A.sum B) dIn dOut where
  toFun := Params.sumInl
  map_add' η ζ := by
    refine Params.ext' rfl (fun ℓ => Matrix.ext fun a p => ?_)
      (fun ℓ => Matrix.ext fun p a => ?_) rfl
    · rcases p with j | j
      · rfl
      · exact (add_zero (0 : ℝ)).symm
    · rcases p with i | i
      · rfl
      · exact (add_zero (0 : ℝ)).symm
  map_smul' c η := by
    refine Params.ext' rfl (fun ℓ => Matrix.ext fun a p => ?_)
      (fun ℓ => Matrix.ext fun p a => ?_) rfl
    · rcases p with j | j
      · rfl
      · exact (smul_zero c).symm
    · rcases p with i | i
      · rfl
      · exact (smul_zero c).symm

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: `η ↦ sumInr η`, a direction of `B` as a direction of `A.sum B`, is linear. -/
private def sumInrLin_dtg {A B : Arch T d L} :
    Params B dIn dOut →ₗ[ℝ] Params (A.sum B) dIn dOut where
  toFun := Params.sumInr
  map_add' η ζ := by
    refine Params.ext' rfl (fun ℓ => Matrix.ext fun a p => ?_)
      (fun ℓ => Matrix.ext fun p a => ?_) rfl
    · rcases p with j | j
      · exact (add_zero (0 : ℝ)).symm
      · rfl
    · rcases p with i | i
      · exact (add_zero (0 : ℝ)).symm
      · rfl
  map_smul' c η := by
    refine Params.ext' rfl (fun ℓ => Matrix.ext fun a p => ?_)
      (fun ℓ => Matrix.ext fun p a => ?_) rfl
    · rcases p with j | j
      · exact (smul_zero c).symm
      · rfl
    · rcases p with i | i
      · exact (smul_zero c).symm
      · rfl

/-- Helper (as `finrank_headFun_dpa` of `Residual/DepthAttention.lean`): the families `Γ` of
`d_h × d_h` matrices, one for each head of each block, form a space of dimension
`∑_ℓ H_ℓ d_{h,ℓ}²`. -/
private theorem finrank_headFun_dtg :
    Module.finrank ℝ (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)
      = ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2 := by
  rw [Module.finrank_pi_fintype]
  simp only [Module.finrank_pi_fintype, Module.finrank_matrix, Module.finrank_self, mul_one,
    Finset.sum_const, Finset.card_univ, smul_eq_mul, sq]

/-- Helper: the families `α` of numbers, one for each hidden unit of each block, form a space of
dimension `∑_ℓ d_hidden,ℓ`. -/
private theorem finrank_hidFun_dtg :
    Module.finrank ℝ (∀ ℓ, hid ℓ → ℝ) = ∑ ℓ, Fintype.card (hid ℓ) := by
  rw [Module.finrank_pi_fintype]
  simp only [Module.finrank_fintype_fun_eq_card]

/-- **Lemma A.27 (Small writes), first value, for attention blocks and gated blocks, under the
conditions of its proof:** with a token that sees itself and another token, for all small `τ ≠ 0`
the residual network has `fd(θ_τ) = P − d² − 2 ∑_ℓ H_ℓ d_{h,ℓ}² − ∑_ℓ d_hidden,ℓ`. -/
theorem eventually_funDim_smallWrites_attentionGated (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hσa : AnalyticOnNhd ℝ σ Set.univ) (hU : GatedUnitsRescale σ σ' dIn dOut (Σ ℓ, hid ℓ))
    (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁)
    (θ : Params (Arch.attentionGated (T := T) (d := d) sees σ id H dh hid) dIn dOut)
    (hθa : SmallWritesGenericAttention θ.sumFst) (hθm : SmallWritesGenericGated θ.sumSnd) :
    ∀ᶠ τ in 𝓝[≠] (0 : ℝ),
      funDim (Arch.attentionGated sees σ id H dh hid) 1 (θ.smallWrites τ)
          + (Fintype.card d ^ 2
            + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
              + ∑ ℓ, Fintype.card (hid ℓ)))
        = Module.finrank ℝ
            (Params (Arch.attentionGated (T := T) (d := d) sees σ id H dh hid) dIn dOut) := by
  classical
  -- the flat directions of `J_0` lie in the range `V` of the linear map
  -- `(X, (Γ, Γ'), α) ↦ (E X, 0, 0, −X D) + sumInl (headDirQK θ_A Γ + headDirVO θ_A Γ')
  -- + sumInr (rescaleDir θ_B α)` (the first theorem)
  let Φ := (flatEDLin_dtg θ).coprod
    ((sumInlLin_dtg.comp ((headDirQKLin_dtg θ.sumFst).coprod (headDirVOLin_dtg θ.sumFst))).coprod
      (sumInrLin_dtg.comp (rescaleDirLin_dtg θ.sumSnd)))
  have hV : ∀ η, (∀ x, smallWritesLimit (Arch.attentionGated sees σ id H dh hid) θ η x = 0) →
      η ∈ LinearMap.range Φ := by
    intro η hη
    obtain ⟨X, Γ, Γ', α, hE, hD, hr, hw, hg, hv, hwr⟩ :=
      smallWritesLimit_eq_zero_attentionGated hσ hU t₁ t₂ h12 hs2 hs1 θ hθa hθm η hη
    refine ⟨(X, (Γ, Γ'), α), ?_⟩
    apply Params.ext'
    · show θ.E * X + ((0 + 0 : Matrix dIn d ℝ) + 0) = η.E
      rw [add_zero, add_zero, add_zero, hE]
    · intro ℓ
      ext a p
      rcases p with j | i | i
      · -- a column of a head
        show (0 : ℝ) + ((headDirQK θ.sumFst Γ + headDirVO θ.sumFst Γ').read ℓ a j + 0)
          = η.read ℓ a (Sum.inl j)
        rw [zero_add, add_zero]
        exact (congrFun (congrFun (hr ℓ) a) j).symm
      · -- the gate column of a hidden unit
        show (0 : ℝ) + (0 + 0) = η.read ℓ a (Sum.inr (Sum.inl i))
        rw [add_zero, add_zero]
        exact (hg ℓ i a).symm
      · -- the value column of a hidden unit
        show (0 : ℝ) + (0 + -(α ℓ i) * θ.sumSnd.read ℓ a (Sum.inr i))
          = η.read ℓ a (Sum.inr (Sum.inr i))
        rw [zero_add, zero_add]
        exact (hv ℓ i a).symm
    · intro ℓ
      ext p b
      rcases p with j | i
      · show (0 : ℝ) + ((headDirQK θ.sumFst Γ + headDirVO θ.sumFst Γ').write ℓ j b + 0)
          = η.write ℓ (Sum.inl j) b
        rw [zero_add, add_zero]
        exact (congrFun (congrFun (hw ℓ) j) b).symm
      · show (0 : ℝ) + (0 + α ℓ i * θ.sumSnd.write ℓ i b) = η.write ℓ (Sum.inr i) b
        rw [zero_add, zero_add]
        exact (hwr ℓ i b).symm
    · show -(X * θ.D) + ((0 + 0 : Matrix d dOut ℝ) + 0) = η.D
      rw [add_zero, add_zero, add_zero, hD]
  -- `dim V ≤ d² + 2 ∑_ℓ H_ℓ d_{h,ℓ}² + ∑_ℓ d_hidden,ℓ`, the dimension of the domain of the map
  have hdim : Module.finrank ℝ (LinearMap.range Φ)
      ≤ Fintype.card d ^ 2 + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
        + ∑ ℓ, Fintype.card (hid ℓ)) := by
    have h := LinearMap.finrank_range_le Φ
    rwa [Module.finrank_prod, Module.finrank_prod, Module.finrank_prod, Module.finrank_matrix,
      Module.finrank_self, mul_one, ← sq, finrank_headFun_dtg, ← two_mul,
      finrank_hidFun_dtg] at h
  -- `≥`: "The rank" of the proof of Lemma A.27, with analytic blocks
  have hf : ∀ ℓ, AnalyticOnNhd ℝ
      ((Arch.attentionGated (T := T) (d := d) sees σ id H dh hid).f ℓ) Set.univ := fun ℓ =>
    analyticOnNhd_f_sum (analyticOnNhd_f_attention (d := d) sees id H dh ℓ)
      (analyticOnNhd_f_gated hσa ℓ)
  -- `≤`: the upper bound for residual networks, as `θ ↦ θ_τ` changes neither `E` nor the reads;
  -- no value column of a read vanishes since no value column of `E W_read^ℓ` does
  have hval : ∀ ℓ i, (fun k => θ.sumSnd.read ℓ k (Sum.inr i)) ≠ 0 := by
    intro ℓ i h0
    apply hθm.value_ne_zero ℓ i
    funext a
    show ∑ k, θ.sumSnd.E a k * θ.sumSnd.read ℓ k (Sum.inr i) = 0
    exact Finset.sum_eq_zero fun k _ => by
      rw [show θ.sumSnd.read ℓ k (Sum.inr i) = 0 from congrFun h0 k, mul_zero]
  filter_upwards [eventually_funDim_smallWrites_ge
    (Arch.attentionGated (T := T) (d := d) sees σ id H dh hid) θ rfl hf _ hV] with τ hτ
  have hle := funDim_add_le_residual_attentionGated (θ.smallWrites τ) hθa.rank_E hθa.rank_Q
    hθa.rank_V hval
  omega

/-- **The conditions of Lemma A.27 hold at generic parameters,** for `d_in, d_out ≥ d ≥ 2`,
heads of width `1 ≤ d_h ≤ d` and blocks of any widths. -/
theorem ae_smallWritesGeneric_attentionGated
    (μ : Measure (Params (Arch.attentionGated (T := T) (d := d) sees σ id H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ)) :
    ∀ᵐ θ ∂μ, SmallWritesGenericAttention θ.sumFst ∧ SmallWritesGenericGated θ.sumSnd := by
  sorry

/-- **Theorem 4.7 of the skips paper for attention blocks and gated blocks, without
normalization:** with `d_in, d_out ≥ d ≥ 2`, heads of width `1 ≤ d_h ≤ d`, blocks of any widths
and a token that sees itself and another token, at almost every parameter the residual network
has the functional dimension `P − d² − 2 ∑_ℓ H_ℓ d_{h,ℓ}² − ∑_ℓ d_hidden,ℓ`. -/
theorem ae_funDim_attentionGated_residual (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hσa : AnalyticOnNhd ℝ σ Set.univ) (hU : GatedUnitsRescale σ σ' dIn dOut (Σ ℓ, hid ℓ))
    (μ : Measure (Params (Arch.attentionGated (T := T) (d := d) sees σ id H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ θ ∂μ, funDim (Arch.attentionGated sees σ id H dh hid) 1 θ
        + (Fintype.card d ^ 2
          + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
              + ∑ ℓ, Fintype.card (hid ℓ)))
      = Module.finrank ℝ
          (Params (Arch.attentionGated (T := T) (d := d) sees σ id H dh hid) dIn dOut) := by
  sorry

/-- **Theorem 4.7, the gain, for attention blocks and gated blocks, without normalization:** if
moreover every block has total width `H d_h + d_hidden ≥ d`, at almost every parameter the skips
raise the functional dimension by at least `L d²`. -/
theorem ae_funDim_attentionGated_residual_ge_add (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hσa : AnalyticOnNhd ℝ σ Set.univ) (hU : GatedUnitsRescale σ σ' dIn dOut (Σ ℓ, hid ℓ))
    (μ : Measure (Params (Arch.attentionGated (T := T) (d := d) sees σ id H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (hW : ∀ ℓ,
      Fintype.card d ≤ Fintype.card (H ℓ) * Fintype.card (dh ℓ) + Fintype.card (hid ℓ))
    (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ θ ∂μ, funDim (Arch.attentionGated sees σ id H dh hid) 0 θ + L * Fintype.card d ^ 2
      ≤ funDim (Arch.attentionGated sees σ id H dh hid) 1 θ := by
  sorry

/-- **Theorem 4.7 of the skips paper for attention blocks and SwiGLU blocks, without
normalization:** at almost every parameter the residual network has the functional dimension
`P − d² − 2 ∑_ℓ H_ℓ d_{h,ℓ}² − ∑_ℓ d_hidden,ℓ`. -/
theorem ae_funDim_attention_swiglu_residual
    (μ : Measure (Params (Arch.attentionGated (T := T) (d := d) sees silu id H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ θ ∂μ, funDim (Arch.attentionGated sees silu id H dh hid) 1 θ
        + (Fintype.card d ^ 2
          + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
              + ∑ ℓ, Fintype.card (hid ℓ)))
      = Module.finrank ℝ
          (Params (Arch.attentionGated (T := T) (d := d) sees silu id H dh hid) dIn dOut) := by
  sorry

/-- **Theorem 4.7 of the skips paper for attention blocks and GeGLU blocks, without
normalization:** at almost every parameter the residual network has the functional dimension
`P − d² − 2 ∑_ℓ H_ℓ d_{h,ℓ}² − ∑_ℓ d_hidden,ℓ`. -/
theorem ae_funDim_attention_geglu_residual
    (μ : Measure (Params (Arch.attentionGated (T := T) (d := d) sees gelu id H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ θ ∂μ, funDim (Arch.attentionGated sees gelu id H dh hid) 1 θ
        + (Fintype.card d ^ 2
          + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
              + ∑ ℓ, Fintype.card (hid ℓ)))
      = Module.finrank ℝ
          (Params (Arch.attentionGated (T := T) (d := d) sees gelu id H dh hid) dIn dOut) := by
  sorry

end Skips
