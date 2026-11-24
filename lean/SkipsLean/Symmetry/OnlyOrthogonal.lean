import SkipsLean.Symmetry.Normalized
import SkipsLean.Basic.RMSNormConverse
import SkipsLean.Network.Blocks
import SkipsLean.Activations.Gaussian
import SkipsLean.Activations.ReLU
import SkipsLean.OneBlock.UnitsSwiGLU

/-!
# Under pre-RMSNorm only orthogonal changes of basis pass (skipless networks)

Paper: "Skip Connections Unlock at Least d_model² Parameters per Layer", Lemma A.4 (Only orthogonal
changes of basis pass), and with it the skipless half of Theorem 3.3 (ii) = Theorem A.17 (i) under
pre-RMSNorm.

Lemma A.4: "Consider a skipless pre-RMSNorm network with `ε > 0` whose blocks are those of
Section 2, and let `G_0, …, G_L` be invertible. Multiply the writes into every hidden state `h_ℓ`
by `G_ℓ` on the right and its reads by `G_ℓ⁻¹` on the left. If this preserves the function at all
parameters, every `G_ℓ` is orthogonal." Its proof uses three facts: "(a) Scaling. If
`N_ε^G(c ũ) = N_ε(c u)` for all `c > 0`, then `ũ = u` and `‖u G‖ = ‖u‖`"; "(b) Blocks separate
their inputs. If rows `a` and `a'` satisfy `B(a) = B(a')` for all parameters of a block `B`, then
`a = a'`. […] For a vanilla block, `σ(a w) = σ(a' w)` for every column `w`. If `a ≠ a'`, choose `w`
with `α = a w ≠ a' w = β`, and replace `w` by `t w`: `σ(t α) = σ(t β)` for all `t`. If `β = −α`,
`σ` is even. Otherwise `σ(z) = σ(q z)` for all `z` with some `|q| < 1`, so
`σ(z) = σ(q^k z) → σ(0)`, and `σ` is constant. None of tanh, GELU, ReLU and ReLU² is even or
constant. For a gated block, `σ(a g)(a v) = σ(a' g)(a' v)` for all columns `g` and `v`, so
`σ(a g) a = σ(a' g) a'` for all `g`. If `a = 0` then `a' = 0`. Otherwise `a' = κ a` for a number
`κ ≠ 0`, and `σ(z) = κ σ(κ z)` for all `z`. For the ReLU gate this gives `κ = 1`. The SiLU and GELU
gates have `σ'(0) = 1/2`, so `κ² = 1`, and they are not odd, so `κ = 1`"; "(c) Hidden states reach
every row"; then an induction from the last hidden state.

Theorem 3.3 (ii): "The changes of basis that preserve the function at all parameters form a group
of dimension `(L + 1) dim 𝒢` in a skipless network and `dim 𝒢` in a residual one". Under
pre-RMSNorm, for a skipless network, this is: the families `G_0, …, G_L` that preserve the function
at all parameters are exactly those with every `G_ℓ` orthogonal (`eval_cob_rmsNorm` gives "if",
Lemma A.4 "only if"). The count `(L + 1) d (d − 1)/2` is the dimension of this group; it is not a
Lean statement here. (For residual networks the two characterizations are in
`Residual/OneChangeOfBasis.lean`; without normalization every family passes in a skipless network,
`eval_cob_skipless`.)

Stated here for MLP blocks and for gated blocks, with what the proof uses of the activation or
gate as hypotheses, and then for the seven kinds of block. Every block has at least one hidden
unit (a block without hidden units writes `0`, and the hidden state after it carries no
condition). Attention blocks are not defined in this library, so the lemma is not stated for
them. A change of basis is `Params.cob θ G G`.
-/

namespace Skips

open Matrix

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]
variable {σ : ℝ → ℝ} {ε : ℝ}

/-! ### Fact (b): blocks separate their inputs -/

open Filter Topology in
/-- Helper for fact (b), vanilla: if `σ(t α) = σ(t β)` for all `t` and `|β| < |α|`, then `σ` is
constant: `σ(z) = σ(q z)` with `q = β/α`, so `σ(z) = σ(q^k z) → σ(0)`. -/
private theorem const_of_scale_eq (hσc : Continuous σ) {α β : ℝ} (hlt : |β| < |α|)
    (hab : ∀ t, σ (t * α) = σ (t * β)) : ∀ z, σ z = σ 0 := by
  have hα : α ≠ 0 := fun h0 => by rw [h0, abs_zero] at hlt; exact (abs_nonneg β).not_gt hlt
  set q := β / α with hq_def
  have hq : |q| < 1 := by
    rw [hq_def, abs_div, div_lt_one (abs_pos.mpr hα)]
    exact hlt
  -- `σ(z) = σ(q z)` (take `t = z/α`)
  have h1 : ∀ z, σ z = σ (q * z) := by
    intro z
    have := hab (z / α)
    rwa [div_mul_cancel₀ z hα, show z / α * β = q * z by rw [hq_def]; field_simp] at this
  -- `σ(z) = σ(q^k z)` for all `k`
  have hk : ∀ (k : ℕ) z, σ z = σ (q ^ k * z) := by
    intro k
    induction k with
    | zero => intro z; rw [pow_zero, one_mul]
    | succ k ih => intro z; rw [ih z, h1 (q ^ k * z), pow_succ, mul_comm (q ^ k) q, mul_assoc]
  -- `q^k z → 0`, and `σ` is continuous
  intro z
  have hlim : Tendsto (fun k : ℕ => σ (q ^ k * z)) atTop (𝓝 (σ (0 * z))) :=
    (hσc.tendsto _).comp ((tendsto_pow_atTop_nhds_zero_of_abs_lt_one hq).mul_const z)
  rw [zero_mul] at hlim
  have hconst : (fun k : ℕ => σ (q ^ k * z)) = fun _ => σ z := funext fun k => (hk k z).symm
  rw [hconst] at hlim
  exact tendsto_nhds_unique tendsto_const_nhds hlim

/-- **Fact (b) for a vanilla block:** if `σ` is continuous, not even and not constant, and
`σ(a w) = σ(a' w)` for every column `w`, then `a = a'`. -/
theorem eq_of_forall_map_dotProduct_eq (hσc : Continuous σ) (hne : ¬ ∀ z, σ (-z) = σ z)
    (hnc : ¬ ∀ z, σ z = σ 0) {a a' : d → ℝ}
    (h : ∀ w : d → ℝ, σ (a ⬝ᵥ w) = σ (a' ⬝ᵥ w)) : a = a' := by
  by_contra hne'
  -- a coordinate `i` where they differ: `α = a i ≠ a' i = β`
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hne'
  -- the column `t e_i`: `σ(t α) = σ(t β)` for all `t`
  have hab : ∀ t, σ (t * a i) = σ (t * a' i) := by
    intro t
    have := h (t • Pi.single i 1)
    simpa only [dotProduct_smul, dotProduct_single, mul_one, smul_eq_mul, mul_comm t] using this
  rcases lt_trichotomy |a i| |a' i| with hlt | heq | hlt
  · exact hnc (const_of_scale_eq hσc hlt fun t => (hab t).symm)
  · -- `|α| = |β|` and `α ≠ β`: `β = -α`, and `σ` is even
    rcases abs_eq_abs.mp heq with h1 | h1
    · exact hi h1
    · have hα : a' i ≠ 0 := fun h0 => hi (by rw [h1, h0, neg_zero])
      apply hne
      intro z
      have := hab (-z / a' i)
      rw [h1, div_mul_cancel₀ _ hα, show -z / a' i * -a' i = z by field_simp] at this
      exact this.symm
  · exact hnc (const_of_scale_eq hσc hlt hab)

omit [DecidableEq d] in
/-- Helper: a nonzero row `b` takes every value `z` as a dot product: `b ⬝ ((z/‖b‖²) b) = z`. -/
private theorem dotProduct_smul_self_div {b : d → ℝ} (hb : b ≠ 0) (z : ℝ) :
    b ⬝ᵥ ((z / (b ⬝ᵥ b)) • b) = z := by
  have hbb : b ⬝ᵥ b ≠ 0 := fun h0 => hb (dotProduct_self_eq_zero.mp h0)
  rw [dotProduct_smul, smul_eq_mul, div_mul_cancel₀ z hbb]

/-- **Fact (b) for a gated block:** if the gate `σ` is not identically zero, `σ(z) = κ σ(κ z)` for
all `z` only for `κ = 1`, and `σ(a g)(a v) = σ(a' g)(a' v)` for all columns `g` and `v`, then
`a = a'`. -/
theorem eq_of_forall_gate_mul_eq (hσ0 : ∃ z, σ z ≠ 0)
    (hκ : ∀ κ : ℝ, (∀ z, σ z = κ * σ (κ * z)) → κ = 1) {a a' : d → ℝ}
    (h : ∀ g v : d → ℝ, σ (a ⬝ᵥ g) * (a ⬝ᵥ v) = σ (a' ⬝ᵥ g) * (a' ⬝ᵥ v)) : a = a' := by
  obtain ⟨z₀, hz₀⟩ := hσ0
  -- the dot products with every `v` agree, so `σ(a g) a = σ(a' g) a'` for every `g`
  have hvec : ∀ g, σ (a ⬝ᵥ g) • a = σ (a' ⬝ᵥ g) • a' := by
    intro g
    funext i
    have := h g (Pi.single i 1)
    simpa only [dotProduct_single, mul_one, Pi.smul_apply, smul_eq_mul] using this
  -- if one of them is `0`, so is the other
  have hzero : ∀ b b' : d → ℝ, (∀ g, σ (b ⬝ᵥ g) • b = σ (b' ⬝ᵥ g) • b') → b = 0 → b' = 0 := by
    intro b b' hbb hb
    by_contra hb'
    have := hbb ((z₀ / (b' ⬝ᵥ b')) • b')
    rw [hb, smul_zero, dotProduct_smul_self_div hb'] at this
    exact hb' ((smul_eq_zero.mp this.symm).resolve_left hz₀)
  by_cases ha : a = 0
  · rw [ha, hzero a a' hvec ha]
  by_cases ha' : a' = 0
  · rw [ha', hzero a' a (fun g => (hvec g).symm) ha']
  -- both nonzero: `a' = κ a` with `κ ≠ 0`
  have e0 := hvec ((z₀ / (a ⬝ᵥ a)) • a)
  rw [dotProduct_smul_self_div ha] at e0
  set s := σ (a' ⬝ᵥ ((z₀ / (a ⬝ᵥ a)) • a))
  have hs : s ≠ 0 := by
    intro hs0
    rw [hs0, zero_smul] at e0
    exact ha ((smul_eq_zero.mp e0).resolve_left hz₀)
  set κ := s⁻¹ * σ z₀ with hκ_def
  have ha'κ : a' = κ • a := by
    rw [hκ_def, mul_smul, e0, smul_smul, inv_mul_cancel₀ hs, one_smul]
  -- `σ(z) = κ σ(κ z)` for all `z`
  have hscale : ∀ z, σ z = κ * σ (κ * z) := by
    intro z
    have e := hvec ((z / (a ⬝ᵥ a)) • a)
    rw [dotProduct_smul_self_div ha, ha'κ, smul_dotProduct, dotProduct_smul_self_div ha,
      smul_smul, smul_eq_mul] at e
    have : σ z = σ (κ * z) * κ := smul_left_injective ℝ ha e
    rw [this, mul_comm]
  rw [ha'κ, hκ κ hscale, one_smul]

/-! ### Lemma A.4 -/

/-! #### Hidden states -/

omit [Fintype T] [DecidableEq d] [Fintype dOut] in
/-- Helper: a hidden state depends only on the embedding and on the blocks before it. -/
private theorem hidden_congr {A : Arch T d L} {M : Fin L → Matrix d d ℝ}
    (θ θ' : Params A dIn dOut) (x : Matrix T dIn ℝ) (hE : θ.E = θ'.E) (ℓ : Fin (L + 1))
    (hr : ∀ j : Fin L, (j : ℕ) < ℓ → θ.read j = θ'.read j)
    (hw : ∀ j : Fin L, (j : ℕ) < ℓ → θ.write j = θ'.write j) :
    hidden A M θ x ℓ = hidden A M θ' x ℓ := by
  induction ℓ using Fin.induction with
  | zero => rw [hidden_zero, hidden_zero, hE]
  | succ i ih =>
    have hi : (i : ℕ) < (i.succ : ℕ) := by rw [Fin.val_succ]; omega
    have hlt : ∀ j : Fin L, (j : ℕ) < (i.castSucc : ℕ) → (j : ℕ) < (i.succ : ℕ) := by
      intro j hj
      rw [Fin.val_castSucc] at hj
      rw [Fin.val_succ]
      omega
    rw [hidden_succ, hidden_succ, ih (fun j hj => hr j (hlt j hj)) (fun j hj => hw j (hlt j hj)),
      hr i hi, hw i hi]

omit [Fintype T] [DecidableEq d] [Fintype dOut] in
/-- Helper: without skips, `h_{k+1} = f_k(χ(h_k) W_read^k) W_write^k`. -/
private theorem hidden_succ_skipless {A : Arch T d L} (θ : Params A dIn dOut)
    (x : Matrix T dIn ℝ) (k : Fin L) :
    hidden A 0 θ x k.succ = A.f k (A.χ (hidden A 0 θ x k.castSucc) * θ.read k) * θ.write k := by
  rw [hidden_succ, Pi.zero_apply, Matrix.mul_zero, zero_add]

omit [Fintype T] [DecidableEq d] [Fintype dOut] in
/-- Helper: a block `j < k` is not the block `k`. -/
private theorem ne_of_lt_castSucc {j k : Fin L} (hj : (j : ℕ) < (k.castSucc : ℕ)) : j ≠ k :=
  fun e => by rw [e, Fin.val_castSucc] at hj; exact lt_irrefl _ hj

omit [Fintype T] [Fintype dOut] in
/-- Helper for fact (a): multiplying the embedding (`ℓ = 0`) or the write into `h_ℓ` by `c`
multiplies `h_ℓ` by `c`, in the network and in the changed one (the parameters before do not
change). -/
private theorem exists_params_smul_hidden {A : Arch T d L} (θ : Params A dIn dOut)
    (x : Matrix T dIn ℝ) (G : Fin (L + 1) → GL d ℝ) (c : ℝ) (ℓ : Fin (L + 1)) :
    ∃ θ' : Params A dIn dOut, hidden A 0 θ' x ℓ = c • hidden A 0 θ x ℓ ∧
      hidden A 0 (θ'.cob G G) x ℓ = c • hidden A 0 (θ.cob G G) x ℓ := by
  cases ℓ using Fin.cases with
  | zero =>
    -- the embedding `c E`
    refine ⟨⟨c • θ.E, θ.read, θ.write, θ.D⟩, ?_, ?_⟩
    · rw [hidden_zero, hidden_zero]
      exact Matrix.mul_smul _ _ _
    · rw [hidden_zero, hidden_zero]
      show x * ((c • θ.E) * _) = c • (x * (θ.E * _))
      rw [Matrix.smul_mul, Matrix.mul_smul]
  | succ k =>
    classical
    -- the write `c W_write^k`
    let θ' : Params A dIn dOut := ⟨θ.E, θ.read, Function.update θ.write k (c • θ.write k), θ.D⟩
    have hw : ∀ j : Fin L, (j : ℕ) < (k.castSucc : ℕ) → θ'.write j = θ.write j :=
      fun j hj => Function.update_of_ne (ne_of_lt_castSucc hj) _ _
    have e1 : hidden A 0 θ' x k.castSucc = hidden A 0 θ x k.castSucc :=
      hidden_congr θ' θ x rfl k.castSucc (fun _ _ => rfl) hw
    have e2 : hidden A 0 (θ'.cob G G) x k.castSucc = hidden A 0 (θ.cob G G) x k.castSucc :=
      hidden_congr (θ'.cob G G) (θ.cob G G) x rfl k.castSucc (fun _ _ => rfl) fun j hj => by
        show θ'.write j * _ = θ.write j * _
        rw [hw j hj]
    have hwk : θ'.write k = c • θ.write k := Function.update_self _ _ _
    have hwk' : (θ'.cob G G).write k = c • (θ.cob G G).write k := by
      show θ'.write k * (G k.succ : Matrix d d ℝ) = c • (θ.write k * (G k.succ : Matrix d d ℝ))
      rw [hwk, Matrix.smul_mul]
    refine ⟨θ', ?_, ?_⟩
    · rw [hidden_succ_skipless, hidden_succ_skipless, e1, hwk, Matrix.mul_smul]
    · rw [hidden_succ_skipless, hidden_succ_skipless, e2, hwk', Matrix.mul_smul]
      rfl

/-! #### Facts on rows and matrices -/

omit [Fintype T] [DecidableEq d] [Fintype dOut] in
/-- Helper: two matrices with the same products with every matrix on the right are equal. -/
private theorem eq_of_forall_mul_right' {m n : Type*} [Fintype m] [Nonempty n]
    {X Y : Matrix T m ℝ} (h : ∀ D : Matrix m n ℝ, X * D = Y * D) : X = Y := by
  classical
  obtain ⟨o⟩ := ‹Nonempty n›
  ext t k
  -- the matrix `e_k e_oᵀ` reads off the column `k`
  have := congrFun (congrFun (h (Matrix.single k o 1)) t) o
  simpa only [mul_single_apply_same, mul_one] using this

omit [DecidableEq d] in
/-- Helper: the argument `‖v‖² / d_model + ε` of the square root in RMSNorm is positive. -/
private theorem rms_arg_pos (hε : 0 < ε) (v : d → ℝ) :
    0 < v ⬝ᵥ v / (Fintype.card d : ℝ) + ε := by
  have : 0 ≤ v ⬝ᵥ v / (Fintype.card d : ℝ) :=
    div_nonneg (Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)) (Nat.cast_nonneg _)
  linarith

/-- Helper: `p⁻¹ u = q⁻¹ w` with `p, q ≠ 0` gives `q u = p w`. -/
private theorem mul_eq_mul_of_inv_mul_eq {p q u w : ℝ} (hp : p ≠ 0) (hq : q ≠ 0)
    (h : p⁻¹ * u = q⁻¹ * w) : q * u = p * w :=
  calc q * u = q * (p * (p⁻¹ * u)) := by rw [mul_inv_cancel_left₀ hp]
    _ = q * (p * (q⁻¹ * w)) := by rw [h]
    _ = p * w := by rw [mul_left_comm p, mul_inv_cancel_left₀ hq]

omit [DecidableEq d] in
/-- Helper, fact (a) on rows: if `N_ε(a) M = N_ε(b)` and `N_ε(2a) M = N_ε(2b)` with `ε > 0`, then
`a M = b`. Write `y = a M`: `y = λ b` with `λ = s(a)/s(b) = s(2a)/s(2b)`, where `s(v)² = ‖v‖²/d + ε`;
if `b ≠ 0` the two factors agree, which forces `‖a‖ = ‖b‖` and `λ = 1`. -/
private theorem vecMul_eq_of_rmsRow_two (hε : 0 < ε) (M : Matrix d d ℝ) {a b : d → ℝ}
    (h1 : rmsRow ε a ᵥ* M = rmsRow ε b)
    (h2 : rmsRow ε ((2 : ℝ) • a) ᵥ* M = rmsRow ε ((2 : ℝ) • b)) : a ᵥ* M = b := by
  -- `‖2v‖² / d = 4 (‖v‖² / d)`
  have h4 : ∀ v : d → ℝ, ((2 : ℝ) • v) ⬝ᵥ ((2 : ℝ) • v) / (Fintype.card d : ℝ)
      = 4 * (v ⬝ᵥ v / (Fintype.card d : ℝ)) := by
    intro v
    rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    ring
  have hp0 : ∀ v : d → ℝ, 0 ≤ v ⬝ᵥ v / (Fintype.card d : ℝ) := fun v =>
    div_nonneg (Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)) (Nat.cast_nonneg _)
  have hA0 := hp0 a
  have hB0 := hp0 b
  unfold rmsRow at h1 h2
  rw [h4, h4, Matrix.smul_vecMul, Matrix.smul_vecMul] at h2
  rw [Matrix.smul_vecMul] at h1
  generalize a ⬝ᵥ a / (Fintype.card d : ℝ) = A at h1 h2 hA0
  generalize b ⬝ᵥ b / (Fintype.card d : ℝ) = B at h1 h2 hB0
  generalize a ᵥ* M = y at h1 h2 ⊢
  -- the four square roots are positive
  have hS : ∀ t : ℝ, 0 ≤ t → 0 < Real.sqrt (t + ε) := fun t ht => Real.sqrt_pos.mpr (by linarith)
  have hsa := hS A hA0
  have hsb := hS B hB0
  have hsa2 := hS (4 * A) (by linarith)
  have hsb2 := hS (4 * B) (by linarith)
  -- `s(b) y = s(a) b` and `s(2b) y = s(2a) b`, entry by entry
  have e1 : ∀ i, Real.sqrt (B + ε) * y i = Real.sqrt (A + ε) * b i := by
    intro i
    have := congrFun h1 i
    simp only [Pi.smul_apply, smul_eq_mul] at this
    exact mul_eq_mul_of_inv_mul_eq hsa.ne' hsb.ne' this
  have e2 : ∀ i, Real.sqrt (4 * B + ε) * y i = Real.sqrt (4 * A + ε) * b i := by
    intro i
    have := congrFun h2 i
    simp only [Pi.smul_apply, smul_eq_mul] at this
    have := mul_eq_mul_of_inv_mul_eq hsa2.ne' hsb2.ne' this
    linear_combination this / 2
  by_cases hb : b = 0
  · -- `b = 0`: then `y = 0`
    funext i
    have := e1 i
    rw [hb, Pi.zero_apply, mul_zero] at this
    rw [hb, Pi.zero_apply]
    exact (mul_eq_zero.mp this).resolve_left hsb.ne'
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hb
  -- the two factors agree: `s(a) s(2b) = s(2a) s(b)`
  have hk : Real.sqrt (A + ε) * Real.sqrt (4 * B + ε) = Real.sqrt (4 * A + ε) * Real.sqrt (B + ε) := by
    apply mul_right_cancel₀ hi₀
    linear_combination (-Real.sqrt (4 * B + ε)) * e1 i₀ + Real.sqrt (B + ε) * e2 i₀
  -- squaring: `(A + ε)(4B + ε) = (4A + ε)(B + ε)`, so `3 ε (A - B) = 0`
  have hsq := congrArg (· ^ 2) hk
  simp only [mul_pow, Real.sq_sqrt (show (0 : ℝ) ≤ A + ε by linarith),
    Real.sq_sqrt (show (0 : ℝ) ≤ B + ε by linarith),
    Real.sq_sqrt (show (0 : ℝ) ≤ 4 * A + ε by linarith),
    Real.sq_sqrt (show (0 : ℝ) ≤ 4 * B + ε by linarith)] at hsq
  have hAB : A = B := by
    have h3 : (A - B) * (3 * ε) = 0 := by linear_combination -hsq
    have := (mul_eq_zero.mp h3).resolve_right (by positivity)
    linarith
  -- so `s(a) = s(b)` and `y = b`
  subst hAB
  funext i
  exact mul_left_cancel₀ hsb.ne' (e1 i)


/-! #### Lemma A.4 for a general block -/

omit [Fintype T] [Fintype dOut] in
/-- Helper, fact (c): every row is a row of the hidden state `h_ℓ` for some parameters and input,
if every block can make a nonzero hidden unit from every nonzero row. -/
private theorem exists_hidden_row {A : Arch T d L} [Nonempty T] [Nonempty dIn] [Nonempty d]
    (hε : 0 < ε) (hA : A.χ = rmsNorm ε)
    (hnz : ∀ k (N : Matrix T d ℝ) (t : T), N t ≠ 0 →
      ∃ (W : Matrix d (A.r k) ℝ) (j : A.w k), A.f k (N * W) t j ≠ 0)
    (ℓ : Fin (L + 1)) (v : d → ℝ) :
    ∃ (θ : Params A dIn dOut) (x : Matrix T dIn ℝ) (t : T), hidden A 0 θ x ℓ t = v := by
  classical
  induction ℓ using Fin.induction generalizing v with
  | zero =>
    obtain ⟨t⟩ := ‹Nonempty T›
    obtain ⟨i⟩ := ‹Nonempty dIn›
    -- a one-hot input and an embedding with the row `v`
    refine ⟨⟨Matrix.of fun _ => v, 0, 0, 0⟩, Matrix.of fun _ => Pi.single i 1, t, ?_⟩
    rw [hidden_zero]
    funext k
    simp only [Matrix.mul_apply, Matrix.of_apply, Pi.single_apply, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  | succ k ih =>
    obtain ⟨i₀⟩ := ‹Nonempty d›
    -- parameters with a nonzero row `t` of `h_k`, so `N_ε(h_k)` has a nonzero row `t`
    obtain ⟨θ, x, t, ht⟩ := ih (Pi.single i₀ 1)
    have hN : rmsNorm ε (hidden A 0 θ x k.castSucc) t ≠ 0 := by
      show rmsRow ε (hidden A 0 θ x k.castSucc t) ≠ 0
      rw [ht]
      refine smul_ne_zero (inv_ne_zero (Real.sqrt_pos.mpr (rms_arg_pos hε _)).ne') fun h0 => ?_
      have := congrFun h0 i₀
      rw [Pi.single_eq_same, Pi.zero_apply] at this
      exact one_ne_zero this
    -- a read with a nonzero unit `j`, of value `c`; the write with the row `c⁻¹ v` at `j`
    obtain ⟨W, j, hc⟩ := hnz k _ t hN
    generalize hc_def : A.f k (rmsNorm ε (hidden A 0 θ x k.castSucc) * W) t j = c at hc
    let θ' : Params A dIn dOut := ⟨θ.E, Function.update θ.read k W,
      Function.update θ.write k (Matrix.of fun j' i => if j' = j then c⁻¹ * v i else 0), θ.D⟩
    have e1 : hidden A 0 θ' x k.castSucc = hidden A 0 θ x k.castSucc :=
      hidden_congr θ' θ x rfl k.castSucc
        (fun i hi => Function.update_of_ne (ne_of_lt_castSucc hi) _ _)
        (fun i hi => Function.update_of_ne (ne_of_lt_castSucc hi) _ _)
    have hrk : θ'.read k = W := Function.update_self _ _ _
    have hwk : θ'.write k = Matrix.of fun j' i => if j' = j then c⁻¹ * v i else 0 :=
      Function.update_self _ _ _
    refine ⟨θ', x, t, ?_⟩
    rw [hidden_succ_skipless, e1, hrk, hwk, hA]
    funext i
    simp only [Matrix.mul_apply, Matrix.of_apply, mul_ite, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ↓reduceIte, hc_def]
    exact mul_inv_cancel_left₀ hc (v i)

omit [Fintype T] [Fintype dOut] in
/-- Lemma A.4 for a skipless pre-RMSNorm network (`ε > 0`) whose blocks separate their inputs
(fact (b), `hsep`) and make a nonzero hidden unit from every nonzero row (`hnz`, for fact (c)).
Downward induction on `ℓ` for `S(ℓ)`: `N_ε(h̃_ℓ) G_ℓ⁻¹ = N_ε(h_ℓ)` for all parameters and inputs,
where `h̃_ℓ = ũ_ℓ G_ℓ` is the hidden state of the changed network. -/
private theorem orthogonal_of_eval_cob_skipless_rmsNorm_gen {A : Arch T d L} [Nonempty T]
    [Nonempty dIn] [Nonempty dOut] (hε : 0 < ε) (hA : A.χ = rmsNorm ε)
    (hsep : ∀ k (n n' : Matrix T d ℝ),
      (∀ W : Matrix d (A.r k) ℝ, A.f k (n' * W) = A.f k (n * W)) → n' = n)
    (hnz : ∀ k (N : Matrix T d ℝ) (t : T), N t ≠ 0 →
      ∃ (W : Matrix d (A.r k) ℝ) (j : A.w k), A.f k (N * W) t j ≠ 0)
    (G : Fin (L + 1) → GL d ℝ)
    (h : ∀ (θ : Params A dIn dOut) (x : Matrix T dIn ℝ),
      eval A 0 (θ.cob G G) x = eval A 0 θ x) :
    ∀ ℓ, (G ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ := by
  classical
  rcases isEmpty_or_nonempty d with hd | hd
  · -- no coordinates: every `0 × 0` matrix is orthogonal
    intro ℓ
    rw [mem_orthogonalGroup_iff]
    exact Matrix.ext fun i => isEmptyElim i
  -- `S ℓ`
  let S : Fin (L + 1) → Prop := fun ℓ => ∀ (θ : Params A dIn dOut) (x : Matrix T dIn ℝ),
    rmsNorm ε (hidden A 0 (θ.cob G G) x ℓ) * (↑(G ℓ)⁻¹ : Matrix d d ℝ)
      = rmsNorm ε (hidden A 0 θ x ℓ)
  -- fact (a): from `S ℓ`, `ũ_ℓ = h̃_ℓ G_ℓ⁻¹ = h_ℓ` (scale the write into `h_ℓ` by `2`)
  have hU : ∀ ℓ, S ℓ → ∀ (θ : Params A dIn dOut) (x : Matrix T dIn ℝ),
      hidden A 0 (θ.cob G G) x ℓ * (↑(G ℓ)⁻¹ : Matrix d d ℝ) = hidden A 0 θ x ℓ := by
    intro ℓ hS θ x
    obtain ⟨θ₂, e2, e2'⟩ := exists_params_smul_hidden θ x G 2 ℓ
    have h1 := hS θ x
    have h2 := hS θ₂ x
    rw [e2, e2'] at h2
    funext t
    exact vecMul_eq_of_rmsRow_two hε _ (congrFun h1 t) (congrFun h2 t)
  -- `S L`: the outputs agree for every readout `D`
  have hlast : S (Fin.last L) := by
    intro θ x
    refine eq_of_forall_mul_right' (n := dOut) fun D => ?_
    have he := h ⟨θ.E, θ.read, θ.write, D⟩ x
    unfold eval at he
    change A.χ (hidden A 0 (θ.cob G G) x (Fin.last L))
        * ((↑(G (Fin.last L))⁻¹ : Matrix d d ℝ) * D)
      = A.χ (hidden A 0 θ x (Fin.last L)) * D at he
    rw [hA, ← Matrix.mul_assoc] at he
    exact he
  -- fact (b): from `ũ_{k+1} = h_{k+1}` for all reads and writes of block `k` to `S k`
  have hstep : ∀ k : Fin L, S k.succ → S k.castSucc := by
    intro k hS θ x
    apply hsep k
    intro W
    refine eq_of_forall_mul_right' (n := d) fun V => ?_
    let θ' : Params A dIn dOut :=
      ⟨θ.E, Function.update θ.read k W, Function.update θ.write k V, θ.D⟩
    have hr : ∀ j : Fin L, (j : ℕ) < (k.castSucc : ℕ) → θ'.read j = θ.read j :=
      fun j hj => Function.update_of_ne (ne_of_lt_castSucc hj) _ _
    have hw : ∀ j : Fin L, (j : ℕ) < (k.castSucc : ℕ) → θ'.write j = θ.write j :=
      fun j hj => Function.update_of_ne (ne_of_lt_castSucc hj) _ _
    have e1 : hidden A 0 θ' x k.castSucc = hidden A 0 θ x k.castSucc :=
      hidden_congr θ' θ x rfl k.castSucc hr hw
    have e2 : hidden A 0 (θ'.cob G G) x k.castSucc = hidden A 0 (θ.cob G G) x k.castSucc :=
      hidden_congr (θ'.cob G G) (θ.cob G G) x rfl k.castSucc
        (fun j hj => by
          show (↑(G j.castSucc)⁻¹ : Matrix d d ℝ) * θ'.read j
            = (↑(G j.castSucc)⁻¹ : Matrix d d ℝ) * θ.read j
          rw [hr j hj])
        (fun j hj => by
          show θ'.write j * (G j.succ : Matrix d d ℝ) = θ.write j * (G j.succ : Matrix d d ℝ)
          rw [hw j hj])
    have hrk : θ'.read k = W := Function.update_self _ _ _
    have hwk : θ'.write k = V := Function.update_self _ _ _
    have hrk' : (θ'.cob G G).read k = (↑(G k.castSucc)⁻¹ : Matrix d d ℝ) * W := by
      show (↑(G k.castSucc)⁻¹ : Matrix d d ℝ) * θ'.read k = _
      rw [hrk]
    have hwk' : (θ'.cob G G).write k = V * (G k.succ : Matrix d d ℝ) := by
      show θ'.write k * (G k.succ : Matrix d d ℝ) = _
      rw [hwk]
    have hU' := hU k.succ hS θ' x
    rw [hidden_succ_skipless, hidden_succ_skipless, e1, e2, hrk, hwk, hrk', hwk', hA,
      Matrix.mul_assoc _ (V * _), Matrix.mul_assoc V, Units.mul_inv, Matrix.mul_one,
      ← Matrix.mul_assoc (rmsNorm ε _)] at hU'
    exact hU'
  have hS : ∀ ℓ, S ℓ := fun ℓ => Fin.reverseInduction hlast hstep ℓ
  -- fact (c): every row `v` is a row of some `h_ℓ`, and `N_ε(h_ℓ G_ℓ) = N_ε(h_ℓ) G_ℓ`
  intro ℓ
  refine (orthogonal_of_rmsRow_vecMul hε (G ℓ) (G ℓ) fun v _ => ?_).1
  obtain ⟨θ, x, t, hv⟩ := exists_hidden_row (dIn := dIn) (dOut := dOut) hε hA hnz ℓ v
  have h1 := hS ℓ θ x
  have h2 := hU ℓ (hS ℓ) θ x
  -- `h̃_ℓ = h_ℓ G_ℓ`
  have h3 : hidden A 0 (θ.cob G G) x ℓ = hidden A 0 θ x ℓ * (G ℓ : Matrix d d ℝ) := by
    rw [← h2, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
  rw [h3] at h1
  have h4 : rmsNorm ε (hidden A 0 θ x ℓ * (G ℓ : Matrix d d ℝ))
      = rmsNorm ε (hidden A 0 θ x ℓ) * (G ℓ : Matrix d d ℝ) := by
    rw [← h1, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
  have h5 := congrFun h4 t
  change rmsRow ε (hidden A 0 θ x ℓ t ᵥ* (G ℓ : Matrix d d ℝ))
    = rmsRow ε (hidden A 0 θ x ℓ t) ᵥ* (G ℓ : Matrix d d ℝ) at h5
  rwa [hv] at h5

/-- **Lemma A.4 for vanilla blocks** whose activation is continuous, not even and not constant:
if the changes of basis `G_0, …, G_L` preserve the function of the skipless pre-RMSNorm network
(`ε > 0`) for all values of the parameters, every `G_ℓ` is orthogonal. -/
theorem orthogonal_of_eval_cob_skipless_rmsNorm_mlp [Nonempty T] [Nonempty dIn] [Nonempty dOut]
    (hε : 0 < ε) (hσc : Continuous σ) (hne : ¬ ∀ z, σ (-z) = σ z) (hnc : ¬ ∀ z, σ z = σ 0)
    (hhid : ∀ ℓ, Nonempty (hid ℓ)) (G : Fin (L + 1) → GL d ℝ)
    (h : ∀ (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)
      (x : Matrix T dIn ℝ),
      eval (Arch.mlp σ (rmsNorm ε) hid) 0 (θ.cob G G) x
        = eval (Arch.mlp σ (rmsNorm ε) hid) 0 θ x) :
    ∀ ℓ, (G ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ := by
  classical
  refine orthogonal_of_eval_cob_skipless_rmsNorm_gen (A := Arch.mlp σ (rmsNorm ε) hid) hε rfl
    ?_ ?_ G h
  · -- fact (b), row by row: a read whose columns all equal `w` gives `σ(n' w) = σ(n w)`
    intro k n n' hW
    obtain ⟨j₀⟩ := hhid k
    funext t
    refine eq_of_forall_map_dotProduct_eq hσc hne hnc fun w => ?_
    exact congrFun (congrFun (hW (Matrix.of fun i _ => w i)) t) j₀
  · -- `σ(z) ≠ 0` for some `z`, and the read column `(z/‖n‖²) n` gives the unit the value `σ(z)`
    intro k N t hN
    obtain ⟨j₀⟩ := hhid k
    obtain ⟨z, hz⟩ : ∃ z, σ z ≠ 0 := by
      by_contra hcon
      simp only [not_exists, not_not] at hcon
      exact hnc fun z => by rw [hcon z, hcon 0]
    refine ⟨Matrix.of fun i _ => ((z / (N t ⬝ᵥ N t)) • N t) i, j₀, ?_⟩
    show σ (N t ⬝ᵥ ((z / (N t ⬝ᵥ N t)) • N t)) ≠ 0
    rwa [dotProduct_smul_self_div hN]

/-- **Lemma A.4 for gated blocks** whose gate is not identically zero and satisfies
`σ(z) = κ σ(κ z)` for all `z` only for `κ = 1`. -/
theorem orthogonal_of_eval_cob_skipless_rmsNorm_gated [Nonempty T] [Nonempty dIn]
    [Nonempty dOut] (hε : 0 < ε) (hσ0 : ∃ z, σ z ≠ 0)
    (hκ : ∀ κ : ℝ, (∀ z, σ z = κ * σ (κ * z)) → κ = 1)
    (hhid : ∀ ℓ, Nonempty (hid ℓ)) (G : Fin (L + 1) → GL d ℝ)
    (h : ∀ (θ : Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)
      (x : Matrix T dIn ℝ),
      eval (Arch.gated σ (rmsNorm ε) hid) 0 (θ.cob G G) x
        = eval (Arch.gated σ (rmsNorm ε) hid) 0 θ x) :
    ∀ ℓ, (G ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ := by
  classical
  refine orthogonal_of_eval_cob_skipless_rmsNorm_gen (A := Arch.gated σ (rmsNorm ε) hid) hε rfl
    ?_ ?_ G h
  · -- fact (b), row by row: gate columns `g` and value columns `v` give
    -- `σ(n' g)(n' v) = σ(n g)(n v)`
    intro k n n' hW
    obtain ⟨j₀⟩ := hhid k
    funext t
    refine eq_of_forall_gate_mul_eq hσ0 hκ fun g v => ?_
    exact congrFun (congrFun
      (hW (Matrix.of fun i c => Sum.elim (fun _ => g i) (fun _ => v i) c)) t) j₀
  · -- the gate column `(z/‖n‖²) n` with `σ(z) ≠ 0` and the value column `n/‖n‖²`
    intro k N t hN
    obtain ⟨j₀⟩ := hhid k
    obtain ⟨z, hz⟩ := hσ0
    refine ⟨Matrix.of fun i c => Sum.elim (fun _ => ((z / (N t ⬝ᵥ N t)) • N t) i)
      (fun _ => ((1 / (N t ⬝ᵥ N t)) • N t) i) c, j₀, ?_⟩
    show σ (N t ⬝ᵥ ((z / (N t ⬝ᵥ N t)) • N t)) * (N t ⬝ᵥ ((1 / (N t ⬝ᵥ N t)) • N t)) ≠ 0
    rw [dotProduct_smul_self_div hN, dotProduct_smul_self_div hN, mul_one]
    exact hz

/-! ### Theorem 3.3 (ii), skipless networks under pre-RMSNorm -/

/-- **Theorem 3.3 (ii), skipless, pre-RMSNorm (`ε > 0`), vanilla blocks:** the changes of basis
`G_0, …, G_L` preserve the function for all values of the parameters if and only if every `G_ℓ` is
orthogonal. -/
theorem eval_cob_skipless_rmsNorm_iff_mlp [Nonempty T] [Nonempty dIn] [Nonempty dOut]
    (hε : 0 < ε) (hσc : Continuous σ) (hne : ¬ ∀ z, σ (-z) = σ z) (hnc : ¬ ∀ z, σ z = σ 0)
    (hhid : ∀ ℓ, Nonempty (hid ℓ)) (G : Fin (L + 1) → GL d ℝ) :
    (∀ (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)
        (x : Matrix T dIn ℝ),
        eval (Arch.mlp σ (rmsNorm ε) hid) 0 (θ.cob G G) x
          = eval (Arch.mlp σ (rmsNorm ε) hid) 0 θ x)
      ↔ ∀ ℓ, (G ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ := by
  -- "only if" is Lemma A.4; "if" is Proposition 3.2 under pre-RMSNorm
  exact ⟨orthogonal_of_eval_cob_skipless_rmsNorm_mlp hε hσc hne hnc hhid G,
    fun hG θ x => eval_cob_rmsNorm θ x ε rfl G hG⟩

/-- **Theorem 3.3 (ii), skipless, pre-RMSNorm (`ε > 0`), gated blocks.** -/
theorem eval_cob_skipless_rmsNorm_iff_gated [Nonempty T] [Nonempty dIn] [Nonempty dOut]
    (hε : 0 < ε) (hσ0 : ∃ z, σ z ≠ 0) (hκ : ∀ κ : ℝ, (∀ z, σ z = κ * σ (κ * z)) → κ = 1)
    (hhid : ∀ ℓ, Nonempty (hid ℓ)) (G : Fin (L + 1) → GL d ℝ) :
    (∀ (θ : Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)
        (x : Matrix T dIn ℝ),
        eval (Arch.gated σ (rmsNorm ε) hid) 0 (θ.cob G G) x
          = eval (Arch.gated σ (rmsNorm ε) hid) 0 θ x)
      ↔ ∀ ℓ, (G ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ := by
  -- "only if" is Lemma A.4; "if" is Proposition 3.2 under pre-RMSNorm
  exact ⟨orthogonal_of_eval_cob_skipless_rmsNorm_gated hε hσ0 hκ hhid G,
    fun hG θ x => eval_cob_rmsNorm θ x ε rfl G hG⟩

/-! ### The activations and gates of the paper -/

/-- "None of tanh, GELU, ReLU and ReLU² is even or constant", and all four are continuous. -/
theorem tanh_not_even_not_const :
    Continuous Real.tanh ∧ (¬ ∀ z, Real.tanh (-z) = Real.tanh z) ∧
      ¬ ∀ z, Real.tanh z = Real.tanh 0 := by
  -- `tanh = sinh / cosh` with `cosh > 0`; `tanh 1 > 0 = tanh 0`, `tanh (-1) = -tanh 1`
  have htanh : Real.tanh = fun z => Real.sinh z / Real.cosh z :=
    funext fun z => Real.tanh_eq_sinh_div_cosh z
  have h1 : 0 < Real.tanh 1 := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr one_pos) (Real.cosh_pos 1)
  refine ⟨?_, fun h => ?_, fun h => ?_⟩
  · rw [htanh]
    exact Real.continuous_sinh.div Real.continuous_cosh fun z => (Real.cosh_pos z).ne'
  · have := h 1
    rw [Real.tanh_neg] at this
    linarith
  · have := h 1
    rw [Real.tanh_zero] at this
    linarith

theorem gelu_not_even_not_const :
    Continuous gelu ∧ (¬ ∀ z, gelu (-z) = gelu z) ∧ ¬ ∀ z, gelu z = gelu 0 := by
  -- `gelu 1 - gelu (-1) = 1`, `gelu 0 = 0 < Φ(1) = gelu 1`
  refine ⟨continuous_iff_continuousAt.mpr fun z => (hasDerivAt_gelu z).continuousAt,
    fun h => ?_, fun h => ?_⟩
  · have e := gelu_sub_gelu_neg 1
    rw [h 1, sub_self] at e
    exact zero_ne_one e
  · have := h 1
    rw [gelu, gelu, zero_mul, one_mul] at this
    exact (gaussCdf_pos 1).ne' this

theorem relu_not_even_not_const :
    Continuous relu ∧ (¬ ∀ z, relu (-z) = relu z) ∧ ¬ ∀ z, relu z = relu 0 := by
  -- `relu 1 = 1`, `relu (-1) = relu 0 = 0`
  refine ⟨continuous_id.max continuous_const, fun h => ?_, fun h => ?_⟩
  · have := h 1
    simp only [relu] at this
    norm_num at this
  · have := h 1
    simp only [relu] at this
    norm_num at this

theorem reluSq_not_even_not_const :
    Continuous reluSq ∧ (¬ ∀ z, reluSq (-z) = reluSq z) ∧ ¬ ∀ z, reluSq z = reluSq 0 := by
  refine ⟨(continuous_id.max continuous_const).pow 2, fun h => ?_, fun h => ?_⟩
  · have := h 1
    simp only [reluSq] at this
    norm_num at this
  · have := h 1
    simp only [reluSq] at this
    norm_num at this

/-- The ReLU gate: `σ(z) = κ σ(κ z)` for all `z` only for `κ = 1`. -/
theorem relu_gate_scale : (∃ z, relu z ≠ 0) ∧ ∀ κ : ℝ, (∀ z, relu z = κ * relu (κ * z)) → κ = 1 := by
  refine ⟨⟨1, by simp only [relu]; norm_num⟩, fun κ h => ?_⟩
  -- at `z = 1`: `1 = κ max(κ, 0)`
  have h1 := h 1
  simp only [relu, mul_one] at h1
  rcases le_or_gt κ 0 with hk | hk
  · rw [max_eq_right hk] at h1
    norm_num at h1
  · rw [max_eq_left hk.le, max_eq_left zero_le_one] at h1
    nlinarith

/-- The SiLU gate: `σ'(0) = 1/2` and SiLU is not odd, so `σ(z) = κ σ(κ z)` only for `κ = 1`. -/
theorem silu_gate_scale : (∃ z, silu z ≠ 0) ∧ ∀ κ : ℝ, (∀ z, silu z = κ * silu (κ * z)) → κ = 1 := by
  have hs1 : silu 1 = 1 / (1 + Real.exp (-1)) := rfl
  refine ⟨⟨1, by rw [hs1]; positivity⟩, fun κ h => ?_⟩
  -- differentiate at `0`: `σ'(0) = κ² σ'(0)` with `σ'(0) = 1/2`
  have hfun : silu = fun z => κ * silu (κ * z) := funext h
  have h2 : HasDerivAt silu (κ * (siluDeriv (κ * 0) * (κ * 1))) 0 := by
    have := ((hasDerivAt_silu (κ * 0)).comp (0 : ℝ) ((hasDerivAt_id (0 : ℝ)).const_mul κ)).const_mul κ
    rw [hfun]
    exact this
  have e := (hasDerivAt_silu 0).unique h2
  have hd0 : siluDeriv 0 = 1 / 2 := by
    simp only [siluDeriv, neg_zero, Real.exp_zero, zero_mul]
    norm_num
  rw [mul_zero, hd0] at e
  have hκ2 : κ = 1 ∨ κ = -1 := by
    have : (κ - 1) * (κ + 1) = 0 := by linear_combination -2 * e
    rcases mul_eq_zero.mp this with h | h
    · left; linarith
    · right; linarith
  rcases hκ2 with hκ | hκ
  · exact hκ
  -- `κ = -1` would make SiLU odd: `σ(1) = -σ(-1)`, i.e. `e^{-1} = e`
  exfalso
  have e1 := h 1
  rw [hκ] at e1
  simp only [silu, mul_one, neg_neg] at e1
  have hp1 : 0 < 1 + Real.exp (-1) := by positivity
  have hp2 : 0 < 1 + Real.exp 1 := by positivity
  field_simp at e1
  have : Real.exp (-1) = Real.exp 1 := by linarith
  have := Real.exp_injective this
  norm_num at this

/-- The GELU gate: `σ'(0) = 1/2` and GELU is not odd, so `σ(z) = κ σ(κ z)` only for `κ = 1`. -/
theorem gelu_gate_scale : (∃ z, gelu z ≠ 0) ∧ ∀ κ : ℝ, (∀ z, gelu z = κ * gelu (κ * z)) → κ = 1 := by
  have hg1 : gelu 1 = gaussCdf 1 := one_mul _
  refine ⟨⟨1, by rw [hg1]; exact (gaussCdf_pos 1).ne'⟩, fun κ h => ?_⟩
  -- differentiate at `0`: `σ'(0) = κ² σ'(0)` with `σ'(0) = Φ(0) > 0`
  have hfun : gelu = fun z => κ * gelu (κ * z) := funext h
  have h2 : HasDerivAt gelu
      (κ * ((gaussCdf (κ * 0) + κ * 0 * gaussPdf (κ * 0)) * (κ * 1))) 0 := by
    have := ((hasDerivAt_gelu (κ * 0)).comp (0 : ℝ) ((hasDerivAt_id (0 : ℝ)).const_mul κ)).const_mul κ
    rw [hfun]
    exact this
  have e := (hasDerivAt_gelu 0).unique h2
  simp only [mul_zero, zero_mul, add_zero, mul_one] at e
  have hΦ := gaussCdf_pos 0
  have hκ2 : κ = 1 ∨ κ = -1 := by
    have : gaussCdf 0 * ((κ - 1) * (κ + 1)) = 0 := by linear_combination -e
    rcases mul_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hΦ.ne') with h | h
    · left; linarith
    · right; linarith
  rcases hκ2 with hκ | hκ
  · exact hκ
  -- `κ = -1` would make GELU odd: `Φ(1) = 1/2 = Φ(-1)`, against `Φ` strictly increasing
  exfalso
  have e1 := h 1
  rw [hκ] at e1
  have e2 := gelu_sub_gelu_neg 1
  rw [show (-1 : ℝ) * 1 = -1 by norm_num] at e1
  have hΦ1 : gaussCdf 1 = 1 / 2 := by rw [← hg1]; linarith
  have hΦm1 : gaussCdf (-1) = 1 / 2 := by rw [gaussCdf_neg, hΦ1]; norm_num
  have := strictMono_gaussCdf (show (-1 : ℝ) < 1 by norm_num)
  rw [hΦ1, hΦm1] at this
  exact lt_irrefl _ this

end Skips
