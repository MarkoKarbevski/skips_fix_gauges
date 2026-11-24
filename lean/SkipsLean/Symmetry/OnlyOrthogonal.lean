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
  sorry

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
  sorry

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
  sorry

/-- **Theorem 3.3 (ii), skipless, pre-RMSNorm (`ε > 0`), gated blocks.** -/
theorem eval_cob_skipless_rmsNorm_iff_gated [Nonempty T] [Nonempty dIn] [Nonempty dOut]
    (hε : 0 < ε) (hσ0 : ∃ z, σ z ≠ 0) (hκ : ∀ κ : ℝ, (∀ z, σ z = κ * σ (κ * z)) → κ = 1)
    (hhid : ∀ ℓ, Nonempty (hid ℓ)) (G : Fin (L + 1) → GL d ℝ) :
    (∀ (θ : Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)
        (x : Matrix T dIn ℝ),
        eval (Arch.gated σ (rmsNorm ε) hid) 0 (θ.cob G G) x
          = eval (Arch.gated σ (rmsNorm ε) hid) 0 θ x)
      ↔ ∀ ℓ, (G ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ := by
  sorry

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
