import SkipsLean.Residual.DepthAttentionDim
import SkipsLean.Residual.DepthMlp
import SkipsLean.Dimension.UpperBoundTransformer
import SkipsLean.Generic.Sum

/-!
# Residual networks of attention blocks and MLP blocks at any depth, without normalization

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

Here for `Arch.attentionMlp sees σ id H dh hid` (`Network/Transformer.lean`): `L` blocks, block
`ℓ` with the heads `H ℓ` of width `dh ℓ` and the hidden units `hid ℓ` (an attention block if `hid
ℓ` is empty, an MLP block if `H ℓ` is empty), without normalization, with a token `t₂` that sees
itself and another token `t₁`; stated for every activation that satisfies the conclusion of Lemma
B.3 with `s = 0` (`UnitsRigid`) for the hidden units of all blocks together. The conditions on `θ`
are those of the two kinds of block, on the two parts of the parameters:
`SmallWritesGenericAttention θ.sumFst` (`Residual/DepthAttention.lean`) and `SmallWritesGeneric
θ.sumSnd` (`Residual/DepthMlp.lean`). For a block without heads `dh ℓ` is any nonempty type.

* `smallWritesLimit_eq_zero_attentionMlp`: the flat directions of `J_0`;
* `eventually_funDim_smallWrites_attentionMlp`: `fd(θ_τ) = P − d² − s` for all small `τ ≠ 0`,
  `s = 2 ∑_ℓ H_ℓ d_{h,ℓ}²`;
* `ae_smallWritesGeneric_attentionMlp`: the conditions at generic parameters;
* `ae_funDim_attentionMlp_residual`: Theorem 4.7, and `…_ge_add`: the gain of at least `L d²` for
  blocks of total width `H d_h + d_hidden ≥ d`;
* the named kinds: attention with tanh blocks, attention with GELU blocks.
-/

namespace Skips

open Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {sees : T → T → Prop} [DecidableRel sees]
variable {H dh hid : Fin L → Type} [∀ ℓ, Fintype (H ℓ)] [∀ ℓ, Fintype (dh ℓ)]
  [∀ ℓ, Fintype (hid ℓ)] {σ σ' : ℝ → ℝ}

/-! ### Helpers: derivatives of matrix curves at `0` -/

/-- Helper (as `hasDerivAt_line_dpa` of `Residual/DepthAttention.lean`): a line `τ ↦ M + τ N` of
matrices has the derivative `N`. -/
private theorem hasDerivAt_line_dtm {m n : Type*} [Fintype m] [Fintype n] (M N : Matrix m n ℝ) :
    HasDerivAt (fun τ : ℝ => M + τ • N) N 0 := by
  have h := ((hasDerivAt_id (0 : ℝ)).smul_const N).const_add M
  rw [one_smul] at h
  exact h

/-- Helper (as `hasDerivAt_mul_dpa`): the product rule for two matrix curves, entry by entry. -/
private theorem hasDerivAt_mul_dtm {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
    {A : ℝ → Matrix m n ℝ} {B : ℝ → Matrix n p ℝ} {A' : Matrix m n ℝ} {B' : Matrix n p ℝ}
    (hA : HasDerivAt A A' 0) (hB : HasDerivAt B B' 0) :
    HasDerivAt (fun τ => A τ * B τ) (A' * B 0 + A 0 * B') 0 := by
  refine hasDerivAt_pi.2 fun a => hasDerivAt_pi.2 fun c => ?_
  have h := HasDerivAt.fun_sum (u := Finset.univ) fun b _ =>
    (hasDerivAt_pi.1 (hasDerivAt_pi.1 hA a) b).fun_mul (hasDerivAt_pi.1 (hasDerivAt_pi.1 hB b) c)
  simp only [Matrix.add_apply, Matrix.mul_apply, ← Finset.sum_add_distrib]
  exact h

/-! ### Helpers: `J_0` as the derivative of a curve, for any blocks -/

omit [DecidableEq d] in
/-- Helper (as `hasDerivAt_block_dpa`, for any differentiable block): the term of block `ℓ`
along the moved reads and writes, `τ ↦ f_ℓ(x E (W_read + τ η_read)) (W_write + τ η_write) D`, has
at `τ = 0` the derivative `(D f_ℓ(x E W_read)(x E η_read) W_write + f_ℓ(x E W_read) η_write) D`
(chain rule). -/
private theorem hasDerivAt_block_dtm {A : Arch T d L} {ℓ : Fin L}
    (hf : Differentiable ℝ (A.f ℓ)) (θ η : Params A dIn dOut) (x : Matrix T dIn ℝ) :
    HasDerivAt (fun τ : ℝ => A.f ℓ (x * θ.E * (θ.read ℓ + τ • η.read ℓ))
        * (θ.write ℓ + τ • η.write ℓ) * θ.D)
      ((fderiv ℝ (A.f ℓ) (x * θ.E * θ.read ℓ) (x * θ.E * η.read ℓ) * θ.write ℓ
        + A.f ℓ (x * θ.E * θ.read ℓ) * η.write ℓ) * θ.D) 0 := by
  -- the line `τ ↦ x E (W_read + τ η_read)` has the derivative `x E η_read`
  have hl : HasDerivAt (fun τ : ℝ => x * θ.E * (θ.read ℓ + τ • η.read ℓ))
      (x * θ.E * η.read ℓ) 0 :=
    (hasDerivAt_mul_dtm (hasDerivAt_const (0 : ℝ) (x * θ.E))
      (hasDerivAt_line_dtm (θ.read ℓ) (η.read ℓ))).congr_deriv
      (by simp only [Matrix.zero_mul, zero_add])
  -- the chain rule through `f_ℓ`
  have hc := (hf (x * θ.E * θ.read ℓ)).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hl
    (by rw [zero_smul, add_zero])
  have hc' : HasDerivAt (fun τ : ℝ => A.f ℓ (x * θ.E * (θ.read ℓ + τ • η.read ℓ)))
      (fderiv ℝ (A.f ℓ) (x * θ.E * θ.read ℓ) (x * θ.E * η.read ℓ)) 0 := hc
  -- the product rule with the write and with `D`
  have h := hasDerivAt_mul_dtm (hasDerivAt_mul_dtm hc'
    (hasDerivAt_line_dtm (θ.write ℓ) (η.write ℓ))) (hasDerivAt_const (0 : ℝ) θ.D)
  exact h.congr_deriv (by simp only [zero_smul, add_zero, Matrix.mul_zero])

omit [Fintype T] [DecidableEq d] [Fintype dOut] in
/-- Helper: the curve whose derivative at `τ = 0` is `(J_0 η)(x)`: `x (E D + τ ψ_M)` with
`ψ_M = η_E D + E η_D`, plus the blocks with the reads and the writes moved by `τ η` (`E` and `D`
do not move inside the blocks). -/
private noncomputable def curve_dtm (A : Arch T d L) (θ η : Params A dIn dOut)
    (x : Matrix T dIn ℝ) (τ : ℝ) : Matrix T dOut ℝ :=
  x * (θ.E * θ.D + τ • (η.E * θ.D + θ.E * η.D))
    + ∑ ℓ, A.f ℓ (x * θ.E * (θ.read ℓ + τ • η.read ℓ)) * (θ.write ℓ + τ • η.write ℓ) * θ.D

omit [DecidableEq d] in
/-- Helper: `(J_0 η)(x)` is the derivative of `curve_dtm` at `τ = 0`, for differentiable
blocks. -/
private theorem hasDerivAt_curve_dtm {A : Arch T d L} (hf : ∀ ℓ, Differentiable ℝ (A.f ℓ))
    (θ η : Params A dIn dOut) (x : Matrix T dIn ℝ) :
    HasDerivAt (curve_dtm A θ η x) (smallWritesLimit A θ η x) 0 := by
  have hd := (hasDerivAt_mul_dtm (hasDerivAt_const (0 : ℝ) x)
    (hasDerivAt_line_dtm (θ.E * θ.D) (η.E * θ.D + θ.E * η.D))).add
    (HasDerivAt.fun_sum (u := Finset.univ) fun ℓ _ => hasDerivAt_block_dtm (hf ℓ) θ η x)
  refine hd.congr_deriv ?_
  rw [Matrix.zero_mul, zero_add]
  rfl

omit [Fintype T] [DecidableEq d] [Fintype dOut] in
/-- Helper ("the output of a block of the sum is the output of the attention block plus the
output of the MLP block", `f_sum_mul`): the curve of a network of `A.sum B`, plus
`x (E D + τ ψ_M)`, is the sum of the curves of its two parts. -/
private theorem curve_sum_dtm {A B : Arch T d L} (θ η : Params (A.sum B) dIn dOut)
    (x : Matrix T dIn ℝ) (τ : ℝ) :
    curve_dtm (A.sum B) θ η x τ + x * (θ.E * θ.D + τ • (η.E * θ.D + θ.E * η.D))
      = curve_dtm A θ.sumFst η.sumFst x τ + curve_dtm B θ.sumSnd η.sumSnd x τ := by
  -- block `ℓ`: `f_ℓ(x E R) W D = f_ℓ^A(x E R_A) W_A D + f_ℓ^B(x E R_B) W_B D`
  have hl : ∀ ℓ, (A.sum B).f ℓ (x * θ.E * (θ.read ℓ + τ • η.read ℓ))
        * (θ.write ℓ + τ • η.write ℓ) * θ.D
      = A.f ℓ (x * θ.sumFst.E * (θ.sumFst.read ℓ + τ • η.sumFst.read ℓ))
          * (θ.sumFst.write ℓ + τ • η.sumFst.write ℓ) * θ.sumFst.D
        + B.f ℓ (x * θ.sumSnd.E * (θ.sumSnd.read ℓ + τ • η.sumSnd.read ℓ))
          * (θ.sumSnd.write ℓ + τ • η.sumSnd.write ℓ) * θ.sumSnd.D := by
    intro ℓ
    rw [f_sum_mul, Matrix.add_mul]
    rfl
  -- the linear terms: the two parts have the `E` and the `D` of `θ`
  have eA : x * (θ.sumFst.E * θ.sumFst.D
      + τ • (η.sumFst.E * θ.sumFst.D + θ.sumFst.E * η.sumFst.D))
      = x * (θ.E * θ.D + τ • (η.E * θ.D + θ.E * η.D)) := rfl
  have eB : x * (θ.sumSnd.E * θ.sumSnd.D
      + τ • (η.sumSnd.E * θ.sumSnd.D + θ.sumSnd.E * η.sumSnd.D))
      = x * (θ.E * θ.D + τ • (η.E * θ.D + θ.E * η.D)) := rfl
  rw [curve_dtm, curve_dtm, curve_dtm, eA, eB]
  simp only [hl, Finset.sum_add_distrib]
  abel

omit [DecidableEq d] in
/-- Helper: `(J_0 η)(x)` of a network of `A.sum B`, plus `x ψ_M`, is the sum of the
`(J_0 η)(x)` of its two parts, at `θ.sumFst`, `η.sumFst` and at `θ.sumSnd`, `η.sumSnd`. -/
private theorem smallWritesLimit_sum_dtm {A B : Arch T d L}
    (hA : ∀ ℓ, Differentiable ℝ (A.f ℓ)) (hB : ∀ ℓ, Differentiable ℝ (B.f ℓ))
    (θ η : Params (A.sum B) dIn dOut) (x : Matrix T dIn ℝ) :
    smallWritesLimit (A.sum B) θ η x + x * (η.E * θ.D + θ.E * η.D)
      = smallWritesLimit A θ.sumFst η.sumFst x + smallWritesLimit B θ.sumSnd η.sumSnd x := by
  -- the derivatives at `τ = 0` of the two sides of `curve_sum_dtm`
  have h1 := (hasDerivAt_curve_dtm (fun ℓ => differentiable_f_sum (hA ℓ) (hB ℓ)) θ η x).add
    (hasDerivAt_mul_dtm (hasDerivAt_const (0 : ℝ) x)
      (hasDerivAt_line_dtm (θ.E * θ.D) (η.E * θ.D + θ.E * η.D)))
  have h2 := ((hasDerivAt_curve_dtm hA θ.sumFst η.sumFst x).add
    (hasDerivAt_curve_dtm hB θ.sumSnd η.sumSnd x)).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun τ => curve_sum_dtm θ η x τ)
  have h := h1.unique h2
  rw [Matrix.zero_mul, zero_add] at h
  exact h

omit [Fintype T] [DecidableEq d] [Fintype dOut] in
/-- Helper: if the reads and the writes of `η` vanish, `(J_0 η)(x) = x ψ_M`. -/
private theorem smallWritesLimit_of_zero_dtm {A : Arch T d L} (θ η : Params A dIn dOut)
    (hr : ∀ ℓ, η.read ℓ = 0) (hw : ∀ ℓ, η.write ℓ = 0) (x : Matrix T dIn ℝ) :
    smallWritesLimit A θ η x = x * (η.E * θ.D + θ.E * η.D) := by
  simp only [smallWritesLimit, hr, hw, Matrix.mul_zero, map_zero, Matrix.zero_mul, add_zero,
    Finset.sum_const_zero]

/-! ### Helpers: the heads at an input whose tokens are all equal -/

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (as `moveRW_dpa`): the parameters `θ` with the reads and the writes moved by `τ η`;
`E` and `D` stay. -/
private def moveRW_dtm {A : Arch T d L} (θ η : Params A dIn dOut) (τ : ℝ) :
    Params A dIn dOut where
  E := θ.E
  read ℓ := θ.read ℓ + τ • η.read ℓ
  write ℓ := θ.write ℓ + τ • η.write ℓ
  D := θ.D

/-- Helper: the value matrix `W_{V,i}` of head `i` of block `ℓ`. -/
private abbrev wV_dtm (θ : Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut)
    (ℓ : Fin L) (i : H ℓ) : Matrix d (dh ℓ) ℝ :=
  (θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))

/-- Helper: the output matrix `W_{O,i}` of head `i` of block `ℓ`. -/
private abbrev wO_dtm (θ : Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut)
    (ℓ : Fin L) (i : H ℓ) : Matrix (dh ℓ) d ℝ :=
  (θ.write ℓ).submatrix (fun k : dh ℓ => (i, k)) id

omit [DecidableEq d] in
/-- Helper (as `hasDerivAt_headValue_dpa`): along the moved reads and writes, the matrix `C` of
head `i` of block `ℓ` has at `τ = 0` the derivative `E η_V W_O D + E W_V η_O D`. -/
private theorem hasDerivAt_headValue_dtm
    (θ η : Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut) (ℓ : Fin L)
    (i : H ℓ) :
    HasDerivAt (fun τ => headValue (moveRW_dtm θ η τ) ℓ i)
      (θ.E * wV_dtm η ℓ i * wO_dtm θ ℓ i * θ.D + θ.E * wV_dtm θ ℓ i * wO_dtm η ℓ i * θ.D) 0 := by
  -- `C(τ) = E (W_V + τ η_V) (W_O + τ η_O) D`
  have h := hasDerivAt_mul_dtm (hasDerivAt_mul_dtm (hasDerivAt_mul_dtm
    (hasDerivAt_const (0 : ℝ) θ.E) (hasDerivAt_line_dtm (wV_dtm θ ℓ i) (wV_dtm η ℓ i)))
    (hasDerivAt_line_dtm (wO_dtm θ ℓ i) (wO_dtm η ℓ i))) (hasDerivAt_const (0 : ℝ) θ.D)
  exact h.congr_deriv (by simp only [zero_smul, add_zero, Matrix.zero_mul, zero_add,
    Matrix.mul_zero, Matrix.add_mul])

omit [DecidableEq d] [Fintype dOut] in
/-- Helper (as `sum_heads_eq_dpa`, "let the heads of all attention blocks form one attention
block"): `∑_{(ℓ,i)} P(x B_{ℓ,i} x^⊤) x C_{ℓ,i} = ∑_ℓ f_ℓ(x E W_read^ℓ) W_write^ℓ D`. -/
private theorem sum_heads_eq_dtm
    (θ : Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut) (x : Matrix T dIn ℝ) :
    ∑ p : (Σ ℓ, H ℓ), attnWeights sees (x * headScore θ p.1 p.2 * xᵀ) * x * headValue θ p.1 p.2
      = ∑ ℓ, (Arch.attention (T := T) (d := d) sees id H dh).f ℓ (x * θ.E * θ.read ℓ)
          * θ.write ℓ * θ.D := by
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  -- block `ℓ` is equation (4) on the hidden state `x E`
  rw [f_attention_mul]
  simp only [attentionBlock, attnHeads, headScore, headValue, Matrix.sum_mul,
    Matrix.transpose_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]

/-- Helper (as the private `attnWeights_sum_rat` of `Absorb/RMSNormAttention.lean`): row `t` of
the weights sums to `1` when token `t` sees some token (the denominator is positive). -/
private theorem attnWeights_sum_dtm (Z : Matrix T T ℝ) (t : T) (ht : ∃ s, sees t s) :
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

omit [Fintype dOut] in
/-- Helper ("head `i` then gives every token the output `x C_i`, whatever its scores are"): if the
rows of `x` all equal `v` and token `t` sees itself, row `t` of `P x C` is row `t` of `x C`. -/
private theorem row_attn_const_dtm (t : T) (ht : sees t t) (Z : Matrix T T ℝ) (v : dIn → ℝ)
    (C : Matrix dIn dOut ℝ) :
    (attnWeights sees Z * Matrix.of (fun _ : T => v) * C) t
      = (Matrix.of (fun _ : T => v) * C) t := by
  funext o
  rw [Matrix.mul_assoc, Matrix.mul_apply]
  -- every row of `x C` is `v C`, and the weights of row `t` sum to `1`
  calc ∑ s, attnWeights sees Z t s * (Matrix.of (fun _ : T => v) * C) s o
      = ∑ s, attnWeights sees Z t s * (Matrix.of (fun _ : T => v) * C) t o := rfl
    _ = (∑ s, attnWeights sees Z t s) * (Matrix.of (fun _ : T => v) * C) t o :=
        (Finset.sum_mul _ _ _).symm
    _ = (Matrix.of (fun _ : T => v) * C) t o := by
        rw [attnWeights_sum_dtm Z t ⟨t, ht⟩, one_mul]

omit [DecidableEq d] in
/-- Helper ("First take an input whose tokens all equal `x`. Head `i` then gives every token the
output `x C_i`, whatever its scores are"): at an input whose rows all equal `v`, row `t` of
`(J_0 η)(x)` of the attention network is `v K` for one matrix `K` (`K = ψ_M + ∑_p ψ_{C_p}`), when
token `t` sees itself. -/
private theorem smallWritesLimit_attention_const_dtm (t : T) (ht : sees t t)
    (θ η : Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut) :
    ∃ K : Matrix dIn dOut ℝ, ∀ v : dIn → ℝ,
      smallWritesLimit (Arch.attention sees id H dh) θ η (Matrix.of fun _ : T => v) t
        = v ᵥ* K := by
  refine ⟨η.E * θ.D + θ.E * η.D + ∑ p : (Σ ℓ, H ℓ), (θ.E * wV_dtm η p.1 p.2 * wO_dtm θ p.1 p.2
    * θ.D + θ.E * wV_dtm θ p.1 p.2 * wO_dtm η p.1 p.2 * θ.D), fun v => ?_⟩
  obtain ⟨x, hx⟩ : ∃ x : Matrix T dIn ℝ, x = Matrix.of fun _ : T => v := ⟨_, rfl⟩
  rw [← hx]
  -- along the curve, head `p` gives row `t` the value `v C_p(τ)`
  have heq : ∀ τ, curve_dtm (Arch.attention sees id H dh) θ η x τ t
      = (x * (θ.E * θ.D + τ • (η.E * θ.D + θ.E * η.D))
        + ∑ p : (Σ ℓ, H ℓ), x * headValue (moveRW_dtm θ η τ) p.1 p.2) t := by
    intro τ
    have hs : ∑ ℓ, (Arch.attention (T := T) (d := d) sees id H dh).f ℓ
          (x * θ.E * (θ.read ℓ + τ • η.read ℓ)) * (θ.write ℓ + τ • η.write ℓ) * θ.D
        = ∑ p : (Σ ℓ, H ℓ), attnWeights sees (x * headScore (moveRW_dtm θ η τ) p.1 p.2 * xᵀ)
          * x * headValue (moveRW_dtm θ η τ) p.1 p.2 :=
      (sum_heads_eq_dtm (moveRW_dtm θ η τ) x).symm
    rw [curve_dtm, hs]
    funext o
    simp only [Matrix.add_apply, Matrix.sum_apply]
    congr 1
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [hx]
    exact congrFun (row_attn_const_dtm t ht _ v _) o
  -- the derivative of `x M(τ) + ∑_p x C_p(τ)` at `τ = 0` is `x (ψ_M + ∑_p ψ_{C_p})`
  have h2 : HasDerivAt (fun τ : ℝ => x * (θ.E * θ.D + τ • (η.E * θ.D + θ.E * η.D))
      + ∑ p : (Σ ℓ, H ℓ), x * headValue (moveRW_dtm θ η τ) p.1 p.2)
      (x * (η.E * θ.D + θ.E * η.D + ∑ p : (Σ ℓ, H ℓ), (θ.E * wV_dtm η p.1 p.2
        * wO_dtm θ p.1 p.2 * θ.D + θ.E * wV_dtm θ p.1 p.2 * wO_dtm η p.1 p.2 * θ.D))) 0 := by
    have h := (hasDerivAt_mul_dtm (hasDerivAt_const (0 : ℝ) x)
      (hasDerivAt_line_dtm (θ.E * θ.D) (η.E * θ.D + θ.E * η.D))).add
      (HasDerivAt.fun_sum (u := Finset.univ) fun (p : Σ ℓ, H ℓ) _ =>
        hasDerivAt_mul_dtm (hasDerivAt_const (0 : ℝ) x) (hasDerivAt_headValue_dtm θ η p.1 p.2))
    refine h.congr_deriv ?_
    simp only [Matrix.zero_mul, zero_add, Matrix.mul_add, Matrix.mul_sum]
  -- row `t`: `(J_0 η)(x)` is the derivative of the curve, which is `x K` there
  have h1 := hasDerivAt_pi.1 (hasDerivAt_curve_dtm
    (fun ℓ => differentiable_f_attention (T := T) (d := d) sees id H dh ℓ) θ η x) t
  have h3 := (hasDerivAt_pi.1 h2 t).congr_of_eventuallyEq (Filter.Eventually.of_forall heq)
  rw [h1.unique h3, Matrix.mul_apply_eq_vecMul, hx]
  rfl

/-! ### Helpers: the terms of the hidden units (as in `Residual/DepthMlp.lean`) -/

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (as `fderiv_map_apply_dm`): the derivative of `M ↦ σ(M)` (entrywise) at `P` along `Q`
has the entries `σ'(P_{t i}) Q_{t i}`. -/
private theorem fderiv_map_apply_dtm (hσ : ∀ z, HasDerivAt σ (σ' z) z) {m n : Type*}
    [Fintype m] [Fintype n] (P Q : Matrix m n ℝ) (t : m) (i : n) :
    fderiv ℝ (fun M : Matrix m n ℝ => M.map σ) P Q t i = σ' (P t i) * Q t i := by
  have hσd : Differentiable ℝ σ := fun z => (hσ z).differentiableAt
  have hd : Differentiable ℝ (fun M : Matrix m n ℝ => M.map σ) :=
    differentiable_pi.2 fun t => differentiable_pi.2 fun i =>
      hσd.comp (differentiable_pi.1 (differentiable_pi.1 differentiable_id t) i)
  -- the chain rule along the line `τ ↦ P + τ Q`
  have hline : HasDerivAt (fun τ : ℝ => P + τ • Q) Q 0 := hasDerivAt_line_dtm P Q
  have h0 : P = P + (0 : ℝ) • Q := by rw [zero_smul, add_zero]
  have h1 := (hd P).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hline h0
  have h2 := hasDerivAt_pi.1 (hasDerivAt_pi.1 h1 t) i
  -- the same derivative, entrywise: `τ ↦ σ(P_{t i} + τ Q_{t i})`
  have h3 : HasDerivAt (fun τ : ℝ => σ (P t i + τ * Q t i)) (σ' (P t i) * Q t i) 0 := by
    have hu : HasDerivAt (fun τ : ℝ => P t i + τ * Q t i) (Q t i) 0 := by
      have h := ((hasDerivAt_id (0 : ℝ)).mul_const (Q t i)).const_add (P t i)
      rw [one_mul] at h
      exact h
    have h := (hσ (P t i)).comp_of_eq (0 : ℝ) hu (by rw [zero_mul, add_zero])
    exact h
  exact h2.unique h3

omit [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the same for the map of block `ℓ` of an MLP network. -/
private theorem fderiv_f_mlp_apply_dtm (hσ : ∀ z, HasDerivAt σ (σ' z) z) (ℓ : Fin L)
    (P Q : Matrix T (hid ℓ) ℝ) (t : T) (i : hid ℓ) :
    fderiv ℝ ((Arch.mlp (T := T) (d := d) σ id hid).f ℓ) P Q t i = σ' (P t i) * Q t i :=
  fderiv_map_apply_dtm hσ P Q t i

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: an entry of `M N + M' N'`. -/
private theorem mul_add_mul_apply_dtm {m n k : Type*} [Fintype n] (M M' : Matrix m n ℝ)
    (N N' : Matrix n k ℝ) (t : m) (o : k) :
    (M * N + M' * N') t o = ∑ i, (M t i * N i o + M' t i * N' i o) := by
  simp only [Matrix.add_apply, Matrix.mul_apply, Finset.sum_add_distrib]

omit [DecidableEq d] [Fintype dOut] in
/-- Helper (as `smallWritesLimit_mlp_apply` of `Residual/DepthMlp.lean`): the entries of
`(J_0 η)(x)` for MLP blocks, `(x ψ_M)_{t o} + ∑_ℓ ∑_i [σ(z_{ℓ i}) (ψ_A^ℓ)_{i o}
+ σ'(z_{ℓ i}) (x ψ_C^ℓ)_{t i} (A^ℓ)_{i o}]` with `z_{ℓ i} = (x C^ℓ)_{t i}`. -/
private theorem smallWritesLimit_mlp_apply_dtm (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (θ η : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) (x : Matrix T dIn ℝ) (t : T)
    (o : dOut) :
    smallWritesLimit (Arch.mlp σ id hid) θ η x t o
      = (x * (η.E * θ.D + θ.E * η.D)) t o + ∑ ℓ, ∑ i : hid ℓ,
        (σ ((x * (θ.E * θ.read ℓ)) t i) * (η.write ℓ * θ.D) i o
          + σ' ((x * (θ.E * θ.read ℓ)) t i) * (x * (θ.E * η.read ℓ)) t i
            * (θ.write ℓ * θ.D) i o) := by
  rw [smallWritesLimit, Matrix.add_apply, Matrix.sum_apply]
  congr 1
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  have e : ∀ F' F : Matrix T (hid ℓ) ℝ, ((F' * θ.write ℓ + F * η.write ℓ) * θ.D) t o
      = ∑ i, (F' t i * (θ.write ℓ * θ.D) i o + F t i * (η.write ℓ * θ.D) i o) := by
    intro F' F
    rw [Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc]
    exact mul_add_mul_apply_dtm _ _ _ _ t o
  rw [e]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [fderiv_f_mlp_apply_dtm hσ, Matrix.mul_assoc x θ.E (θ.read ℓ),
    Matrix.mul_assoc x θ.E (η.read ℓ)]
  show σ' _ * _ * _ + σ _ * _ = _
  ring

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (as `cancel_left_of_rank_dm`): a matrix whose rank is its number of columns cancels
on the left, via a left inverse. -/
private theorem cancel_left_of_rank_dtm {m n k : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (M : Matrix m n ℝ) (hM : M.rank = Fintype.card n) {X Y : Matrix n k ℝ}
    (h : M * X = M * Y) : X = Y := by
  obtain ⟨B, hB⟩ := Matrix.vecMul_surjective_iff_exists_left_inverse.mp
    (Matrix.vecMul_surjective_iff_rank_eq_card.mpr hM)
  have := congrArg (B * ·) h
  simpa only [← Matrix.mul_assoc, hB, Matrix.one_mul] using this

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (as `cancel_right_of_rank_dm`): a matrix whose rank is its number of rows cancels on
the right, via a right inverse. -/
private theorem cancel_right_of_rank_dtm {m n k : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    (M : Matrix m n ℝ) (hM : M.rank = Fintype.card m) {X Y : Matrix k m ℝ}
    (h : X * M = Y * M) : X = Y := by
  obtain ⟨R, hR⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.mp
    (Matrix.mulVec_surjective_iff_rank_eq_card.mpr hM)
  have := congrArg (· * R) h
  simpa only [Matrix.mul_assoc, hR, Matrix.mul_one] using this

/-- **Proof of Lemma A.27, attention blocks and MLP blocks without normalization, the flat
directions of `J_0`:** let token `t₂` see itself and another token `t₁`. Under the conditions of
the lemma, a direction `η` with `(J_0 η)(x) = 0` at every input `x` has `η_E = E X` and
`η_D = −X D` for one matrix `X`; in every block the reads and the writes of its heads are those
of the directions of the changes of basis inside the heads, and
the reads and the writes of its hidden units vanish. -/
theorem smallWritesLimit_eq_zero_attentionMlp (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hU : UnitsRigid σ σ' dIn dOut (Σ ℓ, hid ℓ))
    (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁)
    (θ : Params (Arch.attentionMlp (T := T) (d := d) sees σ id H dh hid) dIn dOut)
    (hθa : SmallWritesGenericAttention θ.sumFst) (hθm : SmallWritesGeneric θ.sumSnd)
    (η : Params (Arch.attentionMlp (T := T) (d := d) sees σ id H dh hid) dIn dOut)
    (hη : ∀ x, smallWritesLimit (Arch.attentionMlp sees σ id H dh hid) θ η x = 0) :
    ∃ (X : Matrix d d ℝ) (Γ Γ' : ∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ),
      η.E = θ.E * X ∧ η.D = -(X * θ.D)
        ∧ (∀ ℓ, η.sumFst.read ℓ = (headDirQK θ.sumFst Γ + headDirVO θ.sumFst Γ').read ℓ)
        ∧ (∀ ℓ, η.sumFst.write ℓ = (headDirQK θ.sumFst Γ + headDirVO θ.sumFst Γ').write ℓ)
        ∧ (∀ ℓ, η.sumSnd.read ℓ = 0) ∧ (∀ ℓ, η.sumSnd.write ℓ = 0) := by
  have hσd : Differentiable ℝ σ := fun z => (hσ z).differentiableAt
  -- `(J_0 η)(x) = x ψ_M + [the terms of the heads] + [the terms of the hidden units]`
  -- (`f_sum_mul`), the heads at `θ.sumFst`, `η.sumFst`, the hidden units at `θ.sumSnd`, `η.sumSnd`
  have hsum : ∀ x, smallWritesLimit (Arch.attentionMlp sees σ id H dh hid) θ η x
      + x * (η.E * θ.D + θ.E * η.D)
      = smallWritesLimit (Arch.attention sees id H dh) θ.sumFst η.sumFst x
        + smallWritesLimit (Arch.mlp σ id hid) θ.sumSnd η.sumSnd x := fun x =>
    smallWritesLimit_sum_dtm (fun ℓ => differentiable_f_attention (T := T) (d := d) sees id H dh ℓ)
      (fun ℓ => differentiable_f_mlp (T := T) (d := d) (χ := id) hσd ℓ) θ η x
  -- Step 1 (equal tokens): at an input whose rows all equal `v`, row `t₂` of the terms of the
  -- heads is `v K` with `K = ψ_M + ∑_p ψ_{C_p}`, whatever the scores are
  obtain ⟨K, hK⟩ := smallWritesLimit_attention_const_dtm t₂ hs2 θ.sumFst η.sumFst
  have key : ∀ (v : dIn → ℝ) (o : dOut), (v ᵥ* K) o + ∑ ℓ, ∑ i : hid ℓ,
      (σ ((Matrix.of (fun _ : T => v) * (θ.sumSnd.E * θ.sumSnd.read ℓ)) t₂ i)
          * (η.sumSnd.write ℓ * θ.sumSnd.D) i o
        + σ' ((Matrix.of (fun _ : T => v) * (θ.sumSnd.E * θ.sumSnd.read ℓ)) t₂ i)
          * (Matrix.of (fun _ : T => v) * (θ.sumSnd.E * η.sumSnd.read ℓ)) t₂ i
            * (θ.sumSnd.write ℓ * θ.sumSnd.D) i o) = 0 := by
    intro v o
    have h := congrFun (congrFun (hsum (Matrix.of fun _ : T => v)) t₂) o
    rw [Matrix.add_apply, Matrix.add_apply, hη, Matrix.zero_apply, zero_add, hK v,
      smallWritesLimit_mlp_apply_dtm hσ] at h
    have e : (Matrix.of (fun _ : T => v)
        * (η.sumSnd.E * θ.sumSnd.D + θ.sumSnd.E * η.sumSnd.D)) t₂ o
        = (Matrix.of (fun _ : T => v) * (η.E * θ.D + θ.E * η.D)) t₂ o := rfl
    rw [e] at h
    linarith
  -- Lemma B.3 for the units of all blocks together, with `M + ∑ C` in the place of `M`:
  -- `E η_read = 0` and `η_write D = 0` at every hidden unit
  obtain ⟨-, -, hc, -, ha⟩ := hU (fun p => (θ.sumSnd.E * θ.sumSnd.read p.1)ᵀ p.2) 0
    (fun p => (θ.sumSnd.write p.1 * θ.sumSnd.D) p.2) K 0
    (fun p => (θ.sumSnd.E * η.sumSnd.read p.1)ᵀ p.2) 0
    (fun p => (η.sumSnd.write p.1 * θ.sumSnd.D) p.2)
    (fun p => hθm.row_ne_zero p.1 p.2) (fun p => hθm.col_ne_zero p.1 p.2)
    (fun p q hpq => hθm.col_not_collinear p q hpq) (by
      intro v
      funext o
      simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
        add_zero]
      rw [Fintype.sum_sigma]
      exact key v o)
  -- `E` cancels on the left and `D` on the right: the reads and writes of the units vanish
  have hr2 : ∀ ℓ, η.sumSnd.read ℓ = 0 := fun ℓ => by
    refine cancel_left_of_rank_dtm θ.sumSnd.E hθm.rank_E ?_
    rw [Matrix.mul_zero]
    ext a i
    exact congrFun (congrFun hc ⟨ℓ, i⟩) a
  have hw2 : ∀ ℓ, η.sumSnd.write ℓ = 0 := fun ℓ => by
    refine cancel_right_of_rank_dtm θ.sumSnd.D hθm.rank_D ?_
    rw [Matrix.zero_mul]
    ext i o
    exact congrFun (congrFun ha ⟨ℓ, i⟩) o
  -- Step 2: "The terms of the units then vanish at every input", so `(J_0 η)(x) = 0` is the
  -- condition of the attention network at `θ.sumFst` and the direction `η.sumFst`
  have hA0 : ∀ x, smallWritesLimit (Arch.attention sees id H dh) θ.sumFst η.sumFst x = 0 := by
    intro x
    have h := hsum x
    rw [hη, zero_add, smallWritesLimit_of_zero_dtm θ.sumSnd η.sumSnd hr2 hw2] at h
    have e : x * (η.sumSnd.E * θ.sumSnd.D + θ.sumSnd.E * η.sumSnd.D)
        = x * (η.E * θ.D + θ.E * η.D) := rfl
    rw [e] at h
    exact right_eq_add.mp h
  -- the attention case (`Residual/DepthAttention.lean`): `X`, `Γ`, `Γ'`
  obtain ⟨X, Γ, Γ', hE, hD, hr, hw⟩ :=
    smallWritesLimit_eq_zero_attention t₁ t₂ h12 hs2 hs1 θ.sumFst hθa η.sumFst hA0
  exact ⟨X, Γ, Γ', hE, hD, hr, hw, hr2, hw2⟩

/-! ### Helpers: the space of the flat directions of `J_0` -/

omit [Fintype T] [DecidableEq d] [Fintype dIn] in
/-- Helper (as `flatEDLin_dpa` of `Residual/DepthAttention.lean`): the directions
`X ↦ (E X, 0, 0, −X D)` of one change of basis at all hidden states, as a linear map. -/
private def flatEDLin_dtm {A : Arch T d L} (θ : Params A dIn dOut) :
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

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: a direction of `A` as a direction of `A.sum B` (`Params.sumInl`, `0` at the reads and
the writes of `B`) depends linearly on it. -/
private def sumInlLin_dtm {A B : Arch T d L} :
    Params A dIn dOut →ₗ[ℝ] Params (A.sum B) dIn dOut where
  toFun := Params.sumInl
  map_add' η ζ := by
    apply Params.ext'
    · rfl
    · intro ℓ
      ext a p
      cases p <;> simp [Params.sumInl]
    · intro ℓ
      ext p a
      cases p <;> simp [Params.sumInl]
    · rfl
  map_smul' c η := by
    apply Params.ext'
    · simp [Params.sumInl]
    · intro ℓ
      ext a p
      cases p <;> simp [Params.sumInl]
    · intro ℓ
      ext p a
      cases p <;> simp [Params.sumInl]
    · simp [Params.sumInl]

/-- Helper (as `headDirQKLin_dpa`): `Γ ↦ headDirQK θ Γ` is linear. -/
private noncomputable def headDirQKLin_dtm
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

/-- Helper (as `headDirVOLin_dpa`): `Γ' ↦ headDirVO θ Γ'` is linear. -/
private noncomputable def headDirVOLin_dtm
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

/-- Helper (as `finrank_headFun_dpa`): the families `Γ` of `d_h × d_h` matrices, one for each
head of each block, form a space of dimension `∑_ℓ H_ℓ d_{h,ℓ}²`. -/
private theorem finrank_headFun_dtm :
    Module.finrank ℝ (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)
      = ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2 := by
  rw [Module.finrank_pi_fintype]
  simp only [Module.finrank_pi_fintype, Module.finrank_matrix, Module.finrank_self, mul_one,
    Finset.sum_const, Finset.card_univ, smul_eq_mul, sq]

/-- **Lemma A.27 (Small writes), first value, for attention blocks and MLP blocks, under the
conditions of its proof:** with a token that sees itself and another token, for all small `τ ≠ 0`
the residual network has `fd(θ_τ) = P − d² − 2 ∑_ℓ H_ℓ d_{h,ℓ}²`. -/
theorem eventually_funDim_smallWrites_attentionMlp (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hσa : AnalyticOnNhd ℝ σ Set.univ) (hU : UnitsRigid σ σ' dIn dOut (Σ ℓ, hid ℓ))
    (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁)
    (θ : Params (Arch.attentionMlp (T := T) (d := d) sees σ id H dh hid) dIn dOut)
    (hθa : SmallWritesGenericAttention θ.sumFst) (hθm : SmallWritesGeneric θ.sumSnd) :
    ∀ᶠ τ in 𝓝[≠] (0 : ℝ),
      funDim (Arch.attentionMlp sees σ id H dh hid) 1 (θ.smallWrites τ)
          + (Fintype.card d ^ 2
            + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
        = Module.finrank ℝ
            (Params (Arch.attentionMlp (T := T) (d := d) sees σ id H dh hid) dIn dOut) := by
  classical
  -- the flat directions of `J_0` lie in the range `V` of the linear map
  -- `(X, Γ, Γ') ↦ (E X, 0, 0, −X D) + [headDirQK θ_A Γ + headDirVO θ_A Γ' on the heads, 0 on the
  -- hidden units]` (the first theorem)
  let Φ := (flatEDLin_dtm θ).coprod
    ((sumInlLin_dtm (B := Arch.mlp (T := T) (d := d) σ id hid)).comp
      ((headDirQKLin_dtm θ.sumFst).coprod (headDirVOLin_dtm θ.sumFst)))
  have hV : ∀ η, (∀ x, smallWritesLimit (Arch.attentionMlp sees σ id H dh hid) θ η x = 0) →
      η ∈ LinearMap.range Φ := by
    intro η hη
    obtain ⟨X, Γ, Γ', hE, hD, hr, hw, hr2, hw2⟩ :=
      smallWritesLimit_eq_zero_attentionMlp hσ hU t₁ t₂ h12 hs2 hs1 θ hθa hθm η hη
    refine ⟨(X, Γ, Γ'), ?_⟩
    rw [LinearMap.coprod_apply, LinearMap.comp_apply, LinearMap.coprod_apply]
    apply Params.ext'
    · show θ.E * X + ((0 : Matrix dIn d ℝ) + 0) = η.E
      rw [add_zero, add_zero, hE]
    · -- the heads: those of `headDirQK θ_A Γ + headDirVO θ_A Γ'`; the hidden units: `0`
      intro ℓ
      ext a p
      cases p with
      | inl j => exact (zero_add _).trans (congrFun (congrFun (hr ℓ) a) j).symm
      | inr j => exact (zero_add _).trans (congrFun (congrFun (hr2 ℓ) a) j).symm
    · intro ℓ
      ext p b
      cases p with
      | inl j => exact (zero_add _).trans (congrFun (congrFun (hw ℓ) j) b).symm
      | inr j => exact (zero_add _).trans (congrFun (congrFun (hw2 ℓ) j) b).symm
    · show -(X * θ.D) + ((0 : Matrix d dOut ℝ) + 0) = η.D
      rw [add_zero, add_zero, hD]
  -- `dim V ≤ d² + 2 ∑_ℓ H_ℓ d_{h,ℓ}²`, the dimension of the domain of the map
  have hdim : Module.finrank ℝ (LinearMap.range Φ)
      ≤ Fintype.card d ^ 2 + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2 := by
    have h := LinearMap.finrank_range_le Φ
    rwa [Module.finrank_prod, Module.finrank_prod, Module.finrank_matrix, Module.finrank_self,
      mul_one, ← sq, finrank_headFun_dtm, ← two_mul] at h
  -- the blocks of the sum are analytic
  have hf : ∀ ℓ, AnalyticOnNhd ℝ ((Arch.attentionMlp (T := T) (d := d) sees σ id H dh hid).f ℓ)
      Set.univ := fun ℓ =>
    analyticOnNhd_f_sum (analyticOnNhd_f_attention sees id H dh ℓ) (analyticOnNhd_f_mlp hσa ℓ)
  -- `≥`: "The rank" of the proof of Lemma A.27; `≤`: the upper bound for residual networks, as
  -- `θ ↦ θ_τ` changes neither `E` nor the reads
  filter_upwards [eventually_funDim_smallWrites_ge
    (Arch.attentionMlp (T := T) (d := d) sees σ id H dh hid) θ rfl hf _ hV] with τ hτ
  have hle := funDim_add_le_residual_attentionMlp (θ.smallWrites τ) hθa.rank_E hθa.rank_Q
    hθa.rank_V
  omega

/-! ### Helpers: the conditions on the MLP part at generic parameters, for any tokens -/

omit [Fintype T] in
/-- Helper (as `rank_eq_of_isUnit_det_rows_dm` of `Residual/DepthMlp.lean`): a matrix with `d`
columns has rank `d` if some `d` of its rows form an invertible matrix. -/
private theorem rank_eq_of_isUnit_det_rows_dtm {m : Type*} [Fintype m] (M : Matrix m d ℝ)
    (ρ : d ↪ m) (h : IsUnit (M.submatrix ρ id).det) : M.rank = Fintype.card d :=
  le_antisymm (Matrix.rank_le_card_width M)
    ((Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).2 h)).symm.le.trans
      (Matrix.rank_submatrix_le M ρ id))

omit [Fintype T] [Fintype dIn] [Fintype dOut] in
/-- Helper (as `exists_minor_ne_zero_dm`): for two distinct hidden units `p ≠ q`, some
parameters have a nonzero minor of the columns `c_p`, `c_q` of `E W_read` at the input
coordinates `a₁`, `a₂`. -/
private theorem exists_minor_ne_zero_dtm {a₁ a₂ : dIn} {k₁ k₂ : d} (ha : a₁ ≠ a₂)
    (hk : k₁ ≠ k₂) {p q : Σ ℓ, hid ℓ} (hpq : p ≠ q) :
    ∃ θ₀ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut,
      (θ₀.E * θ₀.read p.1) a₁ p.2 * (θ₀.E * θ₀.read q.1) a₂ q.2
        - (θ₀.E * θ₀.read q.1) a₁ q.2 * (θ₀.E * θ₀.read p.1) a₂ p.2 ≠ 0 := by
  classical
  let E₀ : Matrix dIn d ℝ :=
    Matrix.of fun a k => if k = (if a = a₁ then k₁ else k₂) then 1 else 0
  let R₀ : ∀ ℓ, Matrix d (hid ℓ) ℝ := fun ℓ =>
    Matrix.of fun k j => if k = (if (⟨ℓ, j⟩ : Σ ℓ, hid ℓ) = p then k₁ else k₂) then 1 else 0
  -- the column of the unit `s` of `E₀ W₀` is the column `k₁` (for `s = p`) or `k₂` of `E₀`
  have hcol : ∀ (s : Σ ℓ, hid ℓ) (a : dIn),
      (E₀ * R₀ s.1) a s.2 = E₀ a (if s = p then k₁ else k₂) := by
    intro s a
    simp only [R₀, Matrix.mul_apply, Matrix.of_apply, Sigma.eta, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  refine ⟨⟨E₀, R₀, 0, 0⟩, ?_⟩
  show (E₀ * R₀ p.1) a₁ p.2 * (E₀ * R₀ q.1) a₂ q.2
    - (E₀ * R₀ q.1) a₁ q.2 * (E₀ * R₀ p.1) a₂ p.2 ≠ 0
  simp only [hcol]
  simp [E₀, Ne.symm hpq, Ne.symm ha, hk, Ne.symm hk]

/-- Helper (`ae_smallWritesGeneric` of `Residual/DepthMlp.lean`, whose statement asks for a
token, `[Nonempty T]`; its proof does not use one): the conditions of Lemma A.27 for MLP blocks
hold at generic parameters, for `d_in, d_out ≥ d ≥ 2` and blocks of any widths. -/
private theorem ae_smallWritesGeneric_dtm
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)) [μ.IsAddHaarMeasure]
    (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, SmallWritesGeneric θ := by
  classical
  -- two distinct coordinates of `h`, two distinct input coordinates, one output coordinate
  obtain ⟨k₁, k₂, hk⟩ := Fintype.exists_pair_of_one_lt_card (show 1 < Fintype.card d by omega)
  obtain ⟨a₁, a₂, ha⟩ := Fintype.exists_pair_of_one_lt_card (show 1 < Fintype.card dIn by omega)
  obtain ⟨o₀⟩ : Nonempty dOut := Fintype.card_pos_iff.1 (by omega)
  obtain ⟨cD⟩ := Function.Embedding.nonempty_of_card_le hdOut
  obtain ⟨ρE⟩ := Function.Embedding.nonempty_of_card_le hdIn
  -- the parameters with all entries `1`
  let θ₁ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut :=
    ⟨Matrix.of fun _ _ => 1, fun _ => Matrix.of fun _ _ => 1, fun _ => Matrix.of fun _ _ => 1,
      Matrix.of fun _ _ => 1⟩
  -- the ranks of `E` and `D`: invertible minors (`Generic/Params.lean`)
  have h2 := ae_isUnit_det_submatrix μ
  -- the rows of `W_write^ℓ D` are nonzero: their entries at `o₀` are
  have h3 : ∀ᵐ θ ∂μ, ∀ ℓ (i : hid ℓ), (θ.write ℓ * θ.D) i o₀ ≠ 0 := by
    refine ae_all_iff.2 fun ℓ => ae_all_iff.2 fun i => ?_
    exact ae_ne_zero_of_analytic μ (analyticOnNhd_write_mul_D (A := Arch.mlp σ id hid)
      (dIn := dIn) ℓ i o₀) ⟨θ₁, sum_one_mul_one_ne_zero hd⟩
  -- the columns of `E W_read^ℓ` are nonzero: their entries at `a₁` are
  have h4 : ∀ᵐ θ ∂μ, ∀ ℓ (i : hid ℓ), (θ.E * θ.read ℓ) a₁ i ≠ 0 := by
    refine ae_all_iff.2 fun ℓ => ae_all_iff.2 fun i => ?_
    exact ae_ne_zero_of_analytic μ (analyticOnNhd_E_mul_read (A := Arch.mlp σ id hid)
      (dOut := dOut) ℓ a₁ i) ⟨θ₁, sum_one_mul_one_ne_zero hd⟩
  -- two columns of distinct units, of one block or of two blocks, are not collinear: a `2 × 2`
  -- minor does not vanish
  have h5 : ∀ᵐ θ ∂μ, ∀ p q : (Σ ℓ, hid ℓ), p ≠ q →
      (θ.E * θ.read p.1) a₁ p.2 * (θ.E * θ.read q.1) a₂ q.2
        - (θ.E * θ.read q.1) a₁ q.2 * (θ.E * θ.read p.1) a₂ p.2 ≠ 0 := by
    refine ae_all_iff.2 fun p => ae_all_iff.2 fun q => ?_
    by_cases hpq : p = q
    · exact Filter.Eventually.of_forall fun _ h => absurd hpq h
    · obtain ⟨θ₀, h₀⟩ := exists_minor_ne_zero_dtm (T := T) (σ := σ) (dOut := dOut) ha hk hpq
      have hC : ∀ (s : Σ ℓ, hid ℓ) (a : dIn), AnalyticOnNhd ℝ
          (fun θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut =>
            (θ.E * θ.read s.1) a s.2) Set.univ :=
        fun s a => analyticOnNhd_E_mul_read (A := Arch.mlp σ id hid) (dOut := dOut) s.1 a s.2
      have hg : AnalyticOnNhd ℝ
          (fun θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut =>
            (θ.E * θ.read p.1) a₁ p.2 * (θ.E * θ.read q.1) a₂ q.2
              - (θ.E * θ.read q.1) a₁ q.2 * (θ.E * θ.read p.1) a₂ p.2) Set.univ :=
        ((hC p a₁).mul (hC q a₂)).sub ((hC q a₁).mul (hC p a₂))
      exact (ae_ne_zero_of_analytic μ hg ⟨θ₀, h₀⟩).mono fun _ h _ => h
  filter_upwards [h2, h3, h4, h5] with θ h2 h3 h4 h5
  refine ⟨rank_eq_of_isUnit_det_rows_dtm θ.E ρE (h2.2.2.1 ρE),
    rank_eq_card_of_isUnit_det θ.D cD (h2.2.1 cD),
    fun ℓ i hi => h3 ℓ i (congrFun hi o₀), fun ℓ i hi => h4 ℓ i (congrFun hi a₁), ?_⟩
  -- if `c_p = r c_q`, the minor of the columns `p`, `q` vanishes
  intro p q hpq r hr
  have e1 : (θ.E * θ.read p.1) a₁ p.2 = r * (θ.E * θ.read q.1) a₁ q.2 := congrFun hr a₁
  have e2 : (θ.E * θ.read p.1) a₂ p.2 = r * (θ.E * θ.read q.1) a₂ q.2 := congrFun hr a₂
  apply h5 p q hpq
  rw [e1, e2]
  ring

/-- **The conditions of Lemma A.27 hold at generic parameters,** for `d_in, d_out ≥ d ≥ 2`,
heads of width `1 ≤ d_h ≤ d` and blocks of any widths. -/
theorem ae_smallWritesGeneric_attentionMlp
    (μ : Measure (Params (Arch.attentionMlp (T := T) (d := d) sees σ id H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ)) :
    ∀ᵐ θ ∂μ, SmallWritesGenericAttention θ.sumFst ∧ SmallWritesGeneric θ.sumSnd := by
  -- the conditions of the two kinds of block, on the two parts of the parameters
  filter_upwards [ae_sumFst μ (ae_smallWritesGenericAttention Measure.addHaar hd hdIn hdOut hdh
      hdh0), ae_sumSnd μ (ae_smallWritesGeneric_dtm Measure.addHaar hd hdIn hdOut)] with θ h1 h2
  exact ⟨h1, h2⟩

/-- **Theorem 4.7 of the skips paper for attention blocks and MLP blocks, without
normalization:** with `d_in, d_out ≥ d ≥ 2`, heads of width `1 ≤ d_h ≤ d`, blocks of any widths
and a token that sees itself and another token, at almost every parameter the residual network
has the functional dimension `P − d² − 2 ∑_ℓ H_ℓ d_{h,ℓ}²`. -/
theorem ae_funDim_attentionMlp_residual (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hσa : AnalyticOnNhd ℝ σ Set.univ) (hU : UnitsRigid σ σ' dIn dOut (Σ ℓ, hid ℓ))
    (μ : Measure (Params (Arch.attentionMlp (T := T) (d := d) sees σ id H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ θ ∂μ, funDim (Arch.attentionMlp sees σ id H dh hid) 1 θ
        + (Fintype.card d ^ 2
          + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
      = Module.finrank ℝ
          (Params (Arch.attentionMlp (T := T) (d := d) sees σ id H dh hid) dIn dOut) := by
  classical
  have hf : ∀ ℓ, AnalyticOnNhd ℝ ((Arch.attentionMlp (T := T) (d := d) sees σ id H dh hid).f ℓ)
      Set.univ := fun ℓ =>
    analyticOnNhd_f_sum (analyticOnNhd_f_attention sees id H dh ℓ) (analyticOnNhd_f_mlp hσa ℓ)
  -- one parameter `θ₀` with the conditions of Lemma A.27, and one small `τ ≠ 0`:
  -- `fd(θ₀_τ) = P - d² - s`
  obtain ⟨θ₀, hθa, hθm⟩ := (ae_smallWritesGeneric_attentionMlp μ hd hdIn hdOut hdh hdh0).exists
  obtain ⟨τ, hτ⟩ := (eventually_funDim_smallWrites_attentionMlp hσ hσa hU t₁ t₂ h12 hs2 hs1 θ₀
    hθa hθm).exists
  -- at almost every `θ`, `fd(θ) ≥ fd(θ₀_τ)` (analytic outputs) and `fd(θ) ≤ P - d² - s`
  filter_upwards [ae_funDim_ge (Arch.attentionMlp sees σ id H dh hid) 1 hf analyticOnNhd_id μ
      (θ₀.smallWrites τ),
    ae_funDim_add_le_residual_attentionMlp μ hdIn hdh] with θ h1 h2
  omega

/-- **Theorem 4.7, the gain, for attention blocks and MLP blocks, without normalization:** if
moreover every block has total width `H d_h + d_hidden ≥ d`, at almost every parameter the skips
raise the functional dimension by at least `L d²`. -/
theorem ae_funDim_attentionMlp_residual_ge_add (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hσa : AnalyticOnNhd ℝ σ Set.univ) (hU : UnitsRigid σ σ' dIn dOut (Σ ℓ, hid ℓ))
    (μ : Measure (Params (Arch.attentionMlp (T := T) (d := d) sees σ id H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (hW : ∀ ℓ,
      Fintype.card d ≤ Fintype.card (H ℓ) * Fintype.card (dh ℓ) + Fintype.card (hid ℓ))
    (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ θ ∂μ, funDim (Arch.attentionMlp sees σ id H dh hid) 0 θ + L * Fintype.card d ^ 2
      ≤ funDim (Arch.attentionMlp sees σ id H dh hid) 1 θ := by
  -- `fd₁ = P - d² - s` and `fd₀ ≤ P - (L + 1) d² - s`
  filter_upwards [ae_funDim_attentionMlp_residual hσ hσa hU μ hd hdIn hdOut hdh hdh0 t₁ t₂ h12
      hs2 hs1, ae_funDim_add_le_skipless_attentionMlp μ hdIn hdh hW] with θ h1 h2
  rw [add_one_mul] at h2
  omega

/-- **Theorem 4.7 of the skips paper for attention blocks and tanh blocks, without
normalization:** at almost every parameter the residual network has the functional dimension
`P − d² − 2 ∑_ℓ H_ℓ d_{h,ℓ}²`. -/
theorem ae_funDim_attention_tanh_residual
    (μ : Measure (Params (Arch.attentionMlp (T := T) (d := d) sees Real.tanh id H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ θ ∂μ, funDim (Arch.attentionMlp sees Real.tanh id H dh hid) 1 θ
        + (Fintype.card d ^ 2
          + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
      = Module.finrank ℝ
          (Params (Arch.attentionMlp (T := T) (d := d) sees Real.tanh id H dh hid) dIn dOut) := by
  exact ae_funDim_attentionMlp_residual hasDerivAt_tanh analyticOnNhd_tanh
    (tanh_unitsRigid _ _ _) μ hd hdIn hdOut hdh hdh0 t₁ t₂ h12 hs2 hs1

/-- **Theorem 4.7 of the skips paper for attention blocks and GELU blocks, without
normalization:** at almost every parameter the residual network has the functional dimension
`P − d² − 2 ∑_ℓ H_ℓ d_{h,ℓ}²`. -/
theorem ae_funDim_attention_gelu_residual
    (μ : Measure (Params (Arch.attentionMlp (T := T) (d := d) sees gelu id H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ θ ∂μ, funDim (Arch.attentionMlp sees gelu id H dh hid) 1 θ
        + (Fintype.card d ^ 2
          + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
      = Module.finrank ℝ
          (Params (Arch.attentionMlp (T := T) (d := d) sees gelu id H dh hid) dIn dOut) := by
  exact ae_funDim_attentionMlp_residual hasDerivAt_gelu analyticOnNhd_gelu
    (gelu_unitsRigid _ _ _) μ hd hdIn hdOut hdh hdh0 t₁ t₂ h12 hs2 hs1

end Skips
