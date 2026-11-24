import SkipsLean.OneBlock.LearnedSkipGain
import SkipsLean.Residual.DepthAttentionRMSDim
import SkipsLean.Network.AttentionAnalytic
import Mathlib.MeasureTheory.Measure.Haar.Disintegration

/-!
# One attention block with a full learned skip under pre-RMSNorm

Paper (skips paper): Theorem 4.6 (ii): "A learned skip raises it by exactly
`d_model (d_model + 1)/2` more than an identity skip." Theorem B.1 (iii): "Let the network be
pre-RMSNorm without biases, with a learned skip `A`, full or upper triangular. For generic
parameters and `ε > 0`, its functional dimension exceeds that of the residual network of part (ii)
by exactly `d_model (d_model + 1)/2`, and it satisfies the equality condition." Its proof, Step 4,
after equation (17), `∂_ψ B(n) = q(n) 𝐃B(n) n`: "For attention, `q(n) n` stands for the matrix with
the rows `q(n_t) n_t`, one per token. We show that `q = 0`, hence `X_s = 0`. […] For attention, on
the two-token inputs of Step 2 for attention blocks with `u = t n̂` and `v` fixed, the right side is
`t³ q(n̂) n̂ S + O(t²)` and the left side is `O(t)`." Here `S = ∑_i W_{V,i} W_{O,i}`.

The Lean statement of Step 4 is the paper's (`NoSymmetricPart` at all inputs, for a block with
`S ≠ 0` in which some token sees a token). A shorter proof than the paper's is available: on inputs
whose tokens are all equal to a row `v`, a token that sees some token has the output `v S`, for
all weights, so equation (17) reads `v (X S + ∂_ψ S) = q(v) v S` on the ball, a linear map equal to
a cubic one, and `q(v) v S = 0`. The statement does not ask for two tokens.

Stated here:

* Step 4: `NoSymmetricPart` for an attention block, where `E` has rank `d`, some token sees a
  token and `S ≠ 0`.
* At one parameter, with `E`, `D` of rank `d` and an invertible skip: the functional dimension is
  that of the residual network at the same weights plus `d (d + 1)/2`
  (`funDimLearned_eq_funDim_residual_add_of_noSymmetricPart`).
* For `d_in, d_out ≥ d ≥ 2`, at least one head, heads of width `1 ≤ d_h ≤ d` and a token that sees
  itself and another token (the hypotheses of `ae_funDim_attention_residual_rmsNorm`, the residual
  value): at almost every `(θ, A)` the functional dimension is `P + d² − d (d − 1) − 2 H d_h²`,
  which is `d (d + 1)/2` more than the residual network at almost every `θ'`.

Numeric check: `learned_skip_relu_attention_check_2026-11-24.py`. Not stated here: the upper
triangular skip; `ε = 0`.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {sees : T → T → Prop} [DecidableRel sees]
variable {H dh : Fin 1 → Type} [∀ ℓ, Fintype (H ℓ)] [∀ ℓ, Fintype (dh ℓ)] {ε : ℝ}

omit [Nonempty T] [Fintype d] [DecidableEq d] in
/-- Helper (copy of the private `attnWeights_sum_oor` of `Symmetry/OnlyOrthogonalRows.lean`): row
`t` of the weights sums to `1` when token `t` sees some token (the denominator is positive). -/
private theorem attnWeights_sum_lsa (Z : Matrix T T ℝ) (t : T) (ht : ∃ s, sees t s) :
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

omit [Nonempty T] [DecidableEq d] in
/-- Helper (step (a), equal tokens): on a pre-activation whose rows all equal `m`, row `t₀` of
the attention block, for a token `t₀` that sees some token, is the value part
`(m_{(i, V k)})_{(i, k)}` of `m`: its weights sum to `1` and all values are equal. -/
private theorem f_row_const_lsa (m : H 0 × (dh 0 ⊕ (dh 0 ⊕ dh 0)) → ℝ) (t₀ s₀ : T)
    (hs : sees t₀ s₀) :
    (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh).f 0 (Matrix.of fun _ => m) t₀
      = fun p => m (p.1, Sum.inr (Sum.inr p.2)) := by
  funext p
  show ∑ s', attnWeights sees _ t₀ s' * m (p.1, Sum.inr (Sum.inr p.2))
    = m (p.1, Sum.inr (Sum.inr p.2))
  rw [← Finset.sum_mul, attnWeights_sum_lsa _ t₀ ⟨s₀, hs⟩, one_mul]

omit [Nonempty T] [DecidableEq d] in
/-- Helper (step (a), the derivative): at a pre-activation with equal rows `m`, in a direction
with equal rows `k`, row `t₀` of the derivative of the block is the value part of `k`: along the
line `M + τ N` the rows stay equal, so row `t₀` is affine in `τ`. -/
private theorem fderiv_f_row_const_lsa (m k : H 0 × (dh 0 ⊕ (dh 0 ⊕ dh 0)) → ℝ) (t₀ s₀ : T)
    (hs : sees t₀ s₀) :
    fderiv ℝ ((Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh).f 0)
        (Matrix.of fun _ => m) (Matrix.of fun _ => k) t₀
      = fun p => k (p.1, Sum.inr (Sum.inr p.2)) := by
  funext p
  -- the line `τ ↦ M + τ N` and the chain rule through the block
  have hl : HasDerivAt (fun τ : ℝ => (Matrix.of fun _ : T => m) + τ • Matrix.of fun _ : T => k)
      (Matrix.of fun _ : T => k) 0 := by
    have h := ((hasDerivAt_id (0 : ℝ)).smul_const (Matrix.of fun _ : T => k)).const_add
      (Matrix.of fun _ : T => m)
    rw [one_smul] at h
    exact h
  have hf := (differentiable_f_attention (d := d) sees (rmsNorm ε) H dh 0
    (Matrix.of fun _ : T => m)).hasFDerivAt
  have hc := hf.comp_hasDerivAt_of_eq (0 : ℝ) hl (by rw [zero_smul, add_zero])
  have he := hasDerivAt_pi.1 (hasDerivAt_pi.1 hc t₀) p
  -- entry `(t₀, p)` along the line is `m_{g p} + τ k_{g p}`
  have hfun : ∀ τ : ℝ, (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh).f 0
      ((Matrix.of fun _ : T => m) + τ • Matrix.of fun _ : T => k) t₀ p
        = m (p.1, Sum.inr (Sum.inr p.2)) + τ * k (p.1, Sum.inr (Sum.inr p.2)) := by
    intro τ
    have e : (Matrix.of fun _ : T => m) + τ • (Matrix.of fun _ : T => k)
        = Matrix.of fun _ : T => m + τ • k := rfl
    rw [e, f_row_const_lsa _ t₀ s₀ hs]
    rfl
  have h2 : HasDerivAt (fun τ : ℝ => m (p.1, Sum.inr (Sum.inr p.2))
      + τ * k (p.1, Sum.inr (Sum.inr p.2))) (k (p.1, Sum.inr (Sum.inr p.2))) 0 := by
    have h := ((hasDerivAt_id (0 : ℝ)).mul_const (k (p.1, Sum.inr (Sum.inr p.2)))).const_add
      (m (p.1, Sum.inr (Sum.inr p.2)))
    rw [one_mul] at h
    exact h
  exact he.unique (h2.congr_of_eventuallyEq (Filter.Eventually.of_forall hfun))

omit [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: row `t` of a sum of matrices is the sum of the rows. -/
private theorem row_add_lsa {m n : Type*} (A B : Matrix m n ℝ) (t : m) :
    (A + B) t = A t + B t := rfl

omit [DecidableEq d] in
/-- Helper (as the private `exists_rmsNorm_eq` of `Depth/StepTanhRMS.lean`, on one row): the
values of `N_ε` on a row (`ε > 0`) include every `v` with `‖v‖² / d < 1`. -/
private theorem exists_rmsRow_eq_lsa (hε : 0 < ε) (v : d → ℝ)
    (hv : v ⬝ᵥ v / (Fintype.card d : ℝ) < 1) : ∃ h, rmsRow ε h = v := by
  -- with `a = ‖v‖² / d < 1` and `c = √ε / √(1 - a)`: `‖c v‖² / d + ε = c²`
  obtain ⟨a, ha⟩ : ∃ a, a = v ⬝ᵥ v / (Fintype.card d : ℝ) := ⟨_, rfl⟩
  have h1a : 0 < 1 - a := by rw [ha]; linarith
  obtain ⟨c, hc⟩ : ∃ c, c = Real.sqrt ε / Real.sqrt (1 - a) := ⟨_, rfl⟩
  have hc0 : 0 < c := by rw [hc]; exact div_pos (Real.sqrt_pos.2 hε) (Real.sqrt_pos.2 h1a)
  have hc2 : c ^ 2 = ε / (1 - a) := by
    rw [hc, div_pow, Real.sq_sqrt hε.le, Real.sq_sqrt h1a.le]
  have hε' : ε = c ^ 2 * (1 - a) := by rw [hc2]; field_simp
  have hrad : (c • v) ⬝ᵥ (c • v) / (Fintype.card d : ℝ) + ε = c ^ 2 := by
    rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    have : c * (c * (v ⬝ᵥ v)) / (Fintype.card d : ℝ) = c ^ 2 * a := by rw [ha]; ring
    rw [this, hε']
    ring
  -- so `N_ε(c v) = c⁻¹ c v = v`
  refine ⟨c • v, ?_⟩
  unfold rmsRow
  rw [hrad, Real.sqrt_sq hc0.le, smul_smul, inv_mul_cancel₀ hc0.ne', one_smul]

omit [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (copy of the private `dense_setOf_ne_zero_of_linear'` of `Depth/StepTanhRMS.lean`): the
set where a nonzero additive and homogeneous function `f` does not vanish is dense. -/
private theorem dense_setOf_ne_zero_of_linear_lsa {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : E → ℝ) (hadd : ∀ x y, f (x + y) = f x + f y)
    (hsmul : ∀ (c : ℝ) x, f (c • x) = c * f x) {x₀ : E} (hx₀ : f x₀ ≠ 0) :
    Dense {x | f x ≠ 0} := by
  intro x
  by_cases hx : f x ≠ 0
  · exact subset_closure hx
  rw [not_not] at hx
  -- from a zero `x` of `f`, the points `x + s x₀` with `s ≠ 0` tend to `x`
  have ht : Filter.Tendsto (fun s : ℝ => x + s • x₀) (nhdsWithin 0 {0}ᶜ) (nhds x) := by
    have hc : Continuous (fun s : ℝ => x + s • x₀) :=
      continuous_const.add (continuous_id.smul continuous_const)
    have h0 := hc.tendsto 0
    rw [zero_smul, add_zero] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  refine mem_closure_of_tendsto ht (eventually_nhdsWithin_of_forall fun s hs => ?_)
  show f (x + s • x₀) ≠ 0
  rw [hadd, hsmul, hx, zero_add]
  exact mul_ne_zero hs hx₀

omit [Fintype T] [Nonempty T] [Fintype dIn] [Fintype dOut] in
/-- Helper (step (c), the end): a symmetric matrix `X` with `⟨ξ X, ξ⟩ = 0` for every row `ξ` is
`0` (polarization: `⟨(e_j + e_i) X, e_j + e_i⟩ = X_{jj} + X_{ji} + X_{ij} + X_{ii}`). -/
private theorem eq_zero_of_symm_of_dotProduct_lsa {X : Matrix d d ℝ} (hX : Xᵀ = X)
    (hq : ∀ ξ : d → ℝ, (ξ ᵥ* X) ⬝ᵥ ξ = 0) : X = 0 := by
  have hd : ∀ i, X i i = 0 := fun i => by
    simpa only [single_one_vecMul, dotProduct_single, Matrix.row_apply, mul_one] using
      hq (Pi.single i 1)
  ext i j
  have e := hq (Pi.single j 1 + Pi.single i 1)
  simp only [add_vecMul, dotProduct_add, single_one_vecMul, dotProduct_single, mul_one,
    Pi.add_apply, Matrix.row_apply, hd, zero_add, add_zero] at e
  have hs : X j i = X i j := by
    have := congrFun (congrFun hX i) j
    rw [Matrix.transpose_apply] at this
    exact this
  rw [Matrix.zero_apply]
  linarith

/-- **Proof of Theorem B.1 (iii), Step 4, for an attention block:** for `ε > 0`, if `E` has rank
`d`, some token sees a token and `S = ∑_i W_{V,i} W_{O,i}` is not `0`, equation (17) at all inputs
forces `X_s = 0`. -/
theorem noSymmetricPart_attention_rmsNorm (hε : 0 < ε)
    (θ : Params (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut)
    (hE : θ.E.rank = Fintype.card d) (hsees : ∃ t s, sees t s)
    (hS : ∑ i, headValueModel θ 0 i ≠ 0) :
    NoSymmetricPart (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) ε θ Set.univ := by
  classical
  intro X ψr ψw hX hyp
  obtain ⟨t₀, s₀, hs⟩ := hsees
  -- the value columns `W_V` of the read and `ψ_V` of `ψ_read`, and `S = W_V W_O = ∑_i C_i`,
  -- `S' = ψ_V W_O + W_V ψ_O`
  obtain ⟨Wv, hWv⟩ : ∃ Wv : Matrix d (H 0 × dh 0) ℝ,
      Wv = (θ.read 0).submatrix id fun p => (p.1, Sum.inr (Sum.inr p.2)) := ⟨_, rfl⟩
  obtain ⟨ψv, hψv⟩ : ∃ ψv : Matrix d (H 0 × dh 0) ℝ,
      ψv = ψr.submatrix id fun p => (p.1, Sum.inr (Sum.inr p.2)) := ⟨_, rfl⟩
  have hSv : Wv * θ.write 0 = ∑ i, headValueModel θ 0 i := by
    ext a b
    rw [hWv, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.sum_apply]
    rfl
  obtain ⟨S, hSdef⟩ : ∃ S : Matrix d d ℝ, S = Wv * θ.write 0 := ⟨_, rfl⟩
  have hS0 : S ≠ 0 := by rw [hSdef, hSv]; exact hS
  obtain ⟨S', hS'⟩ : ∃ S' : Matrix d d ℝ, S' = ψv * θ.write 0 + Wv * ψw := ⟨_, rfl⟩
  -- (b) at the input with equal rows `w`, `n = N_ε(x E)` has equal rows `v`, and row `t₀` of
  -- equation (17) reads `v (X S + S') = q(v) v S`, for every `v` with `‖v‖² / d < 1`
  have hball : ∀ v : d → ℝ, v ⬝ᵥ v / (Fintype.card d : ℝ) < 1 →
      v ᵥ* (X * S + S') = ((v ᵥ* X) ⬝ᵥ v / (Fintype.card d : ℝ)) • (v ᵥ* S) := by
    intro v hv
    -- an input `x` with equal rows `w` and `N_ε(w E) = v` (`E` has rank `d`)
    obtain ⟨h₀, hh₀⟩ := exists_rmsRow_eq_lsa hε v hv
    obtain ⟨w, hw⟩ := (Matrix.vecMul_surjective_iff_rank_eq_card.mpr hE) h₀
    have hn : rmsNorm ε ((Matrix.of fun _ : T => w) * θ.E) = Matrix.of fun _ : T => v := by
      show (Matrix.of fun _ : T => rmsRow ε (w ᵥ* θ.E)) = _
      rw [show w ᵥ* θ.E = h₀ from hw, hh₀]
    have e := hyp (Matrix.of fun _ : T => w) (Set.mem_univ _)
    rw [hn] at e
    -- the pre-activation `n W_read` and the direction `tangentRMS X n W_read + n ψ_read` have
    -- equal rows
    obtain ⟨u, hu⟩ : ∃ u : d → ℝ,
        u = v ᵥ* X - ((v ᵥ* X) ⬝ᵥ v / (Fintype.card d : ℝ)) • v := ⟨_, rfl⟩
    have h1 : (Matrix.of fun _ : T => v) * θ.read 0 = Matrix.of fun _ : T => v ᵥ* θ.read 0 :=
      rfl
    have h2 : tangentRMS X (Matrix.of fun _ : T => v) * θ.read 0
        + (Matrix.of fun _ : T => v) * ψr = Matrix.of fun _ : T => u ᵥ* θ.read 0 + v ᵥ* ψr := by
      rw [hu]
      rfl
    rw [h1, h2] at e
    -- row `t₀`, by step (a)
    have e1 := congrFun e t₀
    rw [row_add_lsa, Matrix.mul_apply_eq_vecMul, Matrix.mul_apply_eq_vecMul,
      fderiv_f_row_const_lsa _ _ t₀ s₀ hs, f_row_const_lsa _ t₀ s₀ hs] at e1
    have e2 : (u ᵥ* Wv + v ᵥ* ψv) ᵥ* θ.write 0 + (v ᵥ* Wv) ᵥ* ψw = 0 := by
      rw [hWv, hψv]
      exact e1
    rw [add_vecMul, vecMul_vecMul, vecMul_vecMul, vecMul_vecMul, hu, sub_vecMul, smul_vecMul,
      vecMul_vecMul] at e2
    rw [hSdef, hS', vecMul_add, vecMul_add]
    linear_combination e2
  -- `d` is not empty (else `X = 0`), so `d ≥ 1`
  rcases isEmpty_or_nonempty d with hd | hd
  · ext i
    exact isEmptyElim i
  have hcard : (1 : ℝ) ≤ Fintype.card d := by exact_mod_cast Fintype.card_pos
  -- (c) `v ↦ v (X S + S')` is linear and `v ↦ q(v) v S` cubic: on `c v` and `(c/2) v` in the
  -- ball, `q(v) v S = 0`, for every `v`
  have hQ : ∀ v : d → ℝ, ((v ᵥ* X) ⬝ᵥ v / (Fintype.card d : ℝ)) • (v ᵥ* S) = 0 := by
    intro v
    have hr : 0 ≤ v ⬝ᵥ v := Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)
    obtain ⟨c, hc⟩ : ∃ c : ℝ, c = (1 + v ⬝ᵥ v)⁻¹ := ⟨_, rfl⟩
    have hc0 : 0 < c := by rw [hc]; positivity
    have hc1 : c * (1 + v ⬝ᵥ v) = 1 := by rw [hc]; field_simp
    -- the scalings `c' v`, `0 < c' ≤ c`, lie in the ball
    have hin : ∀ c' : ℝ, 0 < c' → c' ≤ c →
        (c' • v) ⬝ᵥ (c' • v) / (Fintype.card d : ℝ) < 1 := by
      intro c' h0 hle
      rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
      have h4 : c' * (1 + v ⬝ᵥ v) ≤ 1 :=
        (mul_le_mul_of_nonneg_right hle (by linarith)).trans_eq hc1
      have h5 : c' * (v ⬝ᵥ v) ≤ 1 - c' := by linarith
      have h6 : c' * (c' * (v ⬝ᵥ v)) ≤ c' * (v ⬝ᵥ v) :=
        mul_le_of_le_one_left (mul_nonneg h0.le hr) (by nlinarith)
      have h3 : c' * (c' * (v ⬝ᵥ v)) < 1 := by linarith
      calc c' * (c' * (v ⬝ᵥ v)) / (Fintype.card d : ℝ) ≤ c' * (c' * (v ⬝ᵥ v)) :=
            div_le_self (by positivity) hcard
        _ < 1 := h3
    have e1 := hball (c • v) (hin c hc0 le_rfl)
    have e2 := hball ((c / 2) • v) (hin (c / 2) (by positivity) (by linarith))
    simp only [smul_vecMul, smul_dotProduct, dotProduct_smul, smul_eq_mul] at e1 e2
    funext j
    have f1 := congrFun e1 j
    have f2 := congrFun e2 j
    simp only [Pi.smul_apply, smul_eq_mul] at f1 f2 ⊢
    have h3 : c ^ 3 * ((v ᵥ* X) ⬝ᵥ v / (Fintype.card d : ℝ) * (v ᵥ* S) j) = 0 := by
      linear_combination (8 / 3 : ℝ) * f2 - (4 / 3 : ℝ) * f1
    rw [Pi.zero_apply]
    exact (mul_eq_zero.1 h3).resolve_left (pow_ne_zero 3 hc0.ne')
  -- `S ≠ 0`: some entry `S_{ab} ≠ 0`, so `v S ≠ 0` on a dense set, there `q(v) = 0`, and `q = 0`
  -- everywhere by continuity
  obtain ⟨a, b, hab⟩ : ∃ a b, S a b ≠ 0 := by
    by_contra hne
    exact hS0 (Matrix.ext fun a b => by
      by_contra h
      exact hne ⟨a, b, h⟩)
  have hdense : Dense {v : d → ℝ | (v ᵥ* S) b ≠ 0} :=
    dense_setOf_ne_zero_of_linear_lsa (fun v => (v ᵥ* S) b)
      (fun x y => by rw [add_vecMul]; rfl) (fun c x => by rw [smul_vecMul]; rfl)
      (x₀ := Pi.single a 1) (by rw [single_one_vecMul]; exact hab)
  have hcont : Continuous fun v : d → ℝ => (v ᵥ* X) ⬝ᵥ v / (Fintype.card d : ℝ) :=
    ((continuous_id.matrix_vecMul continuous_const).dotProduct continuous_id).div_const _
  have hq0 := Continuous.ext_on hdense hcont continuous_const fun v hv => by
    have e := congrFun (hQ v) b
    rw [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at e
    exact (mul_eq_zero.1 e).resolve_right hv
  -- a symmetric `X` with `q = 0` is `0`
  refine eq_zero_of_symm_of_dotProduct_lsa hX fun ξ => ?_
  have e : (ξ ᵥ* X) ⬝ᵥ ξ / (Fintype.card d : ℝ) = 0 := congrFun hq0 ξ
  exact (div_eq_zero_iff.1 e).resolve_right (lt_of_lt_of_le one_pos hcard).ne'

/-- **Theorem 4.6 (ii), "A learned skip raises it by exactly `d (d + 1)/2` more than an identity
skip", for an attention block, at one parameter:** for `ε > 0`, if `E` and `D` have rank `d`, some
token sees a token, `S = ∑_i W_{V,i} W_{O,i}` is not `0` and the skip `A = R 0` is invertible, the
network with the full learned skip has at `(θ, A)` the functional dimension of the residual network
at `θ` plus `d (d + 1)/2`. -/
theorem funDimLearned_attention_rmsNorm_eq_residual_add (hε : 0 < ε)
    (θ : Params (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut)
    (hE : θ.E.rank = Fintype.card d) (hD : θ.D.rank = Fintype.card d)
    (hsees : ∃ t s, sees t s) (hS : ∑ i, headValueModel θ 0 i ≠ 0)
    (R : Fin 1 → Matrix d d ℝ) (hR : IsUnit (R 0).det) :
    funDimLearned (Arch.attention sees (rmsNorm ε) H dh) (θ, R)
      = funDim (Arch.attention sees (rmsNorm ε) H dh) 1 θ
        + Fintype.card d * (Fintype.card d + 1) / 2 := by
  sorry

/-- **Theorem B.1 (iii) of the skips paper for one attention block with a full learned skip,
`ε > 0`:** for `d_in, d_out ≥ d ≥ 2`, at least one head, heads of width `1 ≤ d_h ≤ d` and a token
that sees itself and another token, at almost every `(θ, A)` the functional dimension is
`P + d² − d (d − 1) − 2 H d_h²`, with `P` the number of weights without the skip. -/
theorem ae_funDimLearned_attention_rmsNorm (hε : 0 < ε) [Nonempty (H 0)]
    (μ : Measure (Params (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut
      × (Fin 1 → Matrix d d ℝ)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ p ∂μ, funDimLearned (Arch.attention sees (rmsNorm ε) H dh) p
        + (Fintype.card d * (Fintype.card d - 1)
          + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
      = Module.finrank ℝ
          (Params (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut)
        + Fintype.card d ^ 2 := by
  sorry

/-- **Theorem 4.6 (ii) of the skips paper, "A learned skip raises it by exactly `d (d + 1)/2` more
than an identity skip", for one attention block, `ε > 0`:** at almost every `(θ, A)` and almost
every `θ'`, the network with the full learned skip `A` has `d (d + 1)/2` more functional dimension
than the residual network at `θ'`. -/
theorem ae_funDimLearned_attention_rmsNorm_eq_residual_add (hε : 0 < ε) [Nonempty (H 0)]
    (μ : Measure (Params (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut
      × (Fin 1 → Matrix d d ℝ)))
    [μ.IsAddHaarMeasure]
    (ν : Measure (Params (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut))
    [ν.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ p ∂μ, ∀ᵐ θ' ∂ν, funDimLearned (Arch.attention sees (rmsNorm ε) H dh) p
      = funDim (Arch.attention sees (rmsNorm ε) H dh) 1 θ'
        + Fintype.card d * (Fintype.card d + 1) / 2 := by
  sorry

end Skips
