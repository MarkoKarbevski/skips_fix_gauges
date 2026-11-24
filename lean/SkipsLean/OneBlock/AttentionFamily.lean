import SkipsLean.Network.Attention
import SkipsLean.OneBlock.Tanh

/-!
# A sum of attention heads is determined to first order by its matrices

Paper (dimension paper, proof of Theorem C.1, "Attention blocks"; skips paper, "Part (i) for
attention blocks" and the proof of Lemma A.27, "let the heads of all attention blocks form one
attention block"): a family of heads with the matrices `B_j` (scores `x_t B_j x_s^⊤`) and `C_j`
gives the output `∑_j P_j(x) x C_j`. "With `u = x_2` and `v = x_2 − x_1`, head `i` puts the weight
`1/(1 + k e^{−u B_i v^⊤})` on the second token and the rest on the copies of the first, and
`1/(1 + e^{−z}) = ½ + ½ tanh(z/2)` gives the output at the second token
`y_2 = u S − ½ v S + ½ ∑_i tanh(½ (u B_i v^⊤ − log k)) v C_i`  (8)." And Step 2: "For such a `v`,
(8) is, as a function of `u`, the function `G` of Lemma C.3 with one tanh hidden unit per head
[…] and Lemma C.3 for tanh shows that all of these vanish. This holds for all `v` in an open set,
so `D_θ B_i η = 0` and `D_θ C_i η = 0` for every head."

Here these two steps for any finite family `J` of heads given by matrices, with no network: the
heads may be those of one block (`OneBlock/Attention.lean` proves this case for the parameters
of one block) or of all blocks of a network (Lemma A.27 of the skips paper). The mask enters
through a token `t₂` that sees itself and another token `t₁`.

* `twoTokenInput t₂ u v`: the input with the row `u` at `t₂` and the row `u − v` elsewhere.
* `attnFamily_two_tokens`: equation (8) for a family of heads.
* `attnFamily_rigid`: if, along curves `M(τ)`, `B_j(τ)`, `C_j(τ)` of matrices, the output
  `x M(τ) + ∑_j P_{B_j(τ)}(x) x C_j(τ)` has derivative `0` at `τ = 0` at every input `x`, and some
  `v` has the `B_j(0) v^⊤` nonzero and pairwise non-collinear and every `v C_j(0)` nonzero, then
  the derivatives of `M`, of every `B_j` and of every `C_j` at `0` vanish.
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise

variable {T dIn dOut J : Type*} [Fintype T] [Fintype dIn] [Fintype dOut] [Fintype J]
variable {sees : T → T → Prop} [DecidableRel sees]

/-- **The inputs of the proof:** the row `u` at the token `t₂` and the row `u − v` at every other
token. -/
def twoTokenInput [DecidableEq T] (t₂ : T) (u v : dIn → ℝ) : Matrix T dIn ℝ :=
  Matrix.of fun t => if t = t₂ then u else u - v

/-! ### Helpers: the row of the token `t₂` (copied from `OneBlock/Attention.lean`) -/

/-- Helper: `1 - e^z / (e^z + k e^{z - w}) = ½ - ½ tanh(½ (w - log k))` for `k > 0`. -/
private theorem one_sub_weight_fam (z w k : ℝ) (hk : 0 < k) :
    1 - Real.exp z / (Real.exp z + k * Real.exp (z - w))
      = 1 / 2 - 1 / 2 * Real.tanh (1 / 2 * (w - Real.log k)) := by
  obtain ⟨y, hy⟩ : ∃ y, y = 1 / 2 * (w - Real.log k) := ⟨_, rfl⟩
  rw [← hy]
  have hw : w = y + y + Real.log k := by rw [hy]; ring
  have he : Real.exp w = Real.exp y * Real.exp y * k := by
    rw [hw, Real.exp_add, Real.exp_add, Real.exp_log hk]
  rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq, Real.exp_sub, he, Real.exp_neg]
  have h1 := Real.exp_pos z
  have h2 := Real.exp_pos y
  field_simp
  ring

/-- Helper: a probability vector `p` against the rows `u` at `t₂` and `u - v` elsewhere gives
`u - (1 - p_{t₂}) v`. -/
private theorem vecMul_rows_fam {m n : Type*} [Fintype m] [DecidableEq m] (t₂ : m)
    (p : m → ℝ) (hp : ∑ s, p s = 1) (X : Matrix m n ℝ) (u v : n → ℝ) (hX2 : X t₂ = u)
    (hXs : ∀ s, s ≠ t₂ → X s = u - v) :
    p ᵥ* X = u - (1 - p t₂) • v := by
  have h1 : ∑ s ∈ Finset.univ.erase t₂, p s = 1 - p t₂ := by
    rw [← hp, ← Finset.add_sum_erase _ _ (Finset.mem_univ t₂)]
    ring
  have h2 : ∑ s ∈ Finset.univ.erase t₂, p s • X s = ∑ s ∈ Finset.univ.erase t₂, p s • (u - v) :=
    Finset.sum_congr rfl fun s hs => by rw [hXs s (Finset.ne_of_mem_erase hs)]
  rw [Matrix.vecMul_eq_sum, ← Finset.add_sum_erase _ _ (Finset.mem_univ t₂), hX2, h2,
    ← Finset.sum_smul, h1]
  module

/-- Helper: the weights of row `t₂` when `t₂` sees itself with the score `z` and every other
token with the score `z - w`: they sum to `1`, and the weight at `t₂` is `e^z / (e^z + k e^{z-w})`,
`k` the number of tokens other than `t₂` that `t₂` sees. -/
private theorem attnWeights_row_fam [DecidableEq T] (t₂ : T) (hs2 : sees t₂ t₂)
    (Z : Matrix T T ℝ) (z w : ℝ) (hz : Z t₂ t₂ = z) (hzw : ∀ s, s ≠ t₂ → Z t₂ s = z - w) :
    (∑ s, attnWeights sees Z t₂ s = 1) ∧ attnWeights sees Z t₂ t₂
      = Real.exp z / (Real.exp z
        + ((Finset.univ.filter fun s => sees t₂ s ∧ s ≠ t₂).card : ℝ) * Real.exp (z - w)) := by
  obtain ⟨den, hden⟩ : ∃ den, den = ∑ s', if sees t₂ s' then Real.exp (Z t₂ s') else 0 :=
    ⟨_, rfl⟩
  have hpos : 0 < den := by
    rw [hden]
    refine Finset.sum_pos' (fun s _ => ?_) ⟨t₂, Finset.mem_univ _, ?_⟩
    · split_ifs <;> positivity
    · rw [ite_eq_left hs2]
      exact Real.exp_pos _
  -- the denominator is `e^z + k e^{z - w}`
  have hden' : den = Real.exp z
      + ((Finset.univ.filter fun s => sees t₂ s ∧ s ≠ t₂).card : ℝ) * Real.exp (z - w) := by
    have hs : ∀ s, (if sees t₂ s then Real.exp (Z t₂ s) else 0)
        = (if s = t₂ then Real.exp z else 0)
          + (if sees t₂ s ∧ s ≠ t₂ then Real.exp (z - w) else 0) := by
      intro s
      by_cases h : s = t₂
      · subst h
        simp [hs2, hz]
      · by_cases hst : sees t₂ s <;> simp [h, hst, hzw s h]
    rw [hden, Finset.sum_congr rfl fun s _ => hs s, Finset.sum_add_distrib, Finset.sum_ite_eq',
      ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, ite_eq_left (Finset.mem_univ t₂)]
  have hP : ∀ s, attnWeights sees Z t₂ s
      = (if sees t₂ s then Real.exp (Z t₂ s) else 0) / den := by
    intro s
    simp only [attnWeights, Matrix.of_apply, ← hden]
    split_ifs <;> simp
  refine ⟨?_, ?_⟩
  · rw [Finset.sum_congr rfl fun s _ => hP s, ← Finset.sum_div, ← hden, div_self hpos.ne']
  · rw [hP, ite_eq_left hs2, hz, hden']

/-- Helper: row `t₂` of `P_B(x) x` at `x = twoTokenInput t₂ u v` is
`u - (½ - ½ tanh(½ (u B v^⊤ - log k))) v`. -/
private theorem row_two_tokens_fam [DecidableEq T] (t₁ t₂ : T) (h12 : t₁ ≠ t₂)
    (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) (B : Matrix dIn dIn ℝ) (u v : dIn → ℝ) :
    (attnWeights sees (twoTokenInput t₂ u v * B * (twoTokenInput t₂ u v)ᵀ)
      * twoTokenInput t₂ u v) t₂
      = u - ((1 / 2 : ℝ) - (1 / 2 : ℝ) * Real.tanh ((1 / 2) * (u ⬝ᵥ (B *ᵥ v)
          - Real.log ((Finset.univ.filter fun s => sees t₂ s ∧ s ≠ t₂).card : ℝ)))) • v := by
  obtain ⟨X, hX⟩ : ∃ X : Matrix T dIn ℝ, X = twoTokenInput t₂ u v := ⟨_, rfl⟩
  rw [← hX]
  have hX2 : X t₂ = u := by
    rw [hX]
    exact ite_eq_left rfl
  have hXs : ∀ s, s ≠ t₂ → X s = u - v := fun s hs => by
    rw [hX]
    exact ite_eq_right hs
  -- the scores of row `t₂`: `u B uᵀ` at `t₂`, `u B (u - v)ᵀ` elsewhere
  have hZ : ∀ s, (X * B * Xᵀ) t₂ s = u ⬝ᵥ (B *ᵥ X s) := by
    intro s
    rw [Matrix.mul_mul_apply, Matrix.transpose_transpose, hX2]
  have hk : 0 < ((Finset.univ.filter fun s => sees t₂ s ∧ s ≠ t₂).card : ℝ) :=
    Nat.cast_pos.2 (Finset.card_pos.2 ⟨t₁, Finset.mem_filter.2 ⟨Finset.mem_univ _, hs1, h12⟩⟩)
  obtain ⟨h1, h2⟩ := attnWeights_row_fam t₂ hs2 (X * B * Xᵀ) (u ⬝ᵥ (B *ᵥ u)) (u ⬝ᵥ (B *ᵥ v))
    (by rw [hZ, hX2])
    (fun s hs => by rw [hZ, hXs s hs, Matrix.mulVec_sub, dotProduct_sub])
  rw [Matrix.mul_apply_eq_vecMul, vecMul_rows_fam t₂ _ h1 X u v hX2 hXs, h2,
    one_sub_weight_fam _ _ _ hk]

/-- Helper: row `t` of a sum of matrices. -/
private theorem row_sum_fam {ι m n : Type*} [Fintype ι] (F : ι → Matrix m n ℝ) (t : m) :
    (∑ i, F i) t = ∑ i, F i t := by
  ext o
  rw [Matrix.sum_apply, Finset.sum_apply]

omit [Fintype dOut] in
/-- **Equation (8) for a family of heads:** let token `t₂` see itself and another token `t₁`, and
let `k` be the number of tokens other than `t₂` that `t₂` sees. At the input `twoTokenInput t₂ u v`
the sum of the heads has at `t₂` the row
`u ∑_j C_j − ½ v ∑_j C_j + ½ ∑_j tanh(½ (u B_j v^⊤ − log k)) v C_j`. -/
theorem attnFamily_two_tokens [DecidableEq T] (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂)
    (hs1 : sees t₂ t₁) (B : J → Matrix dIn dIn ℝ) (C : J → Matrix dIn dOut ℝ)
    (u v : dIn → ℝ) :
    (∑ j, attnWeights sees (twoTokenInput t₂ u v * B j * (twoTokenInput t₂ u v)ᵀ)
        * twoTokenInput t₂ u v * C j) t₂
      = u ᵥ* (∑ j, C j) - (1 / 2 : ℝ) • (v ᵥ* ∑ j, C j)
        + ∑ j, ((1 / 2 : ℝ) * Real.tanh ((1 / 2) * (u ⬝ᵥ (B j *ᵥ v)
            - Real.log ((Finset.univ.filter fun s => sees t₂ s ∧ s ≠ t₂).card : ℝ))))
          • (v ᵥ* C j) := by
  -- head `j` gives at `t₂` the row `(u - (½ - ½ tanh(…)) v) C_j`
  have hi : ∀ j, (attnWeights sees (twoTokenInput t₂ u v * B j * (twoTokenInput t₂ u v)ᵀ)
        * twoTokenInput t₂ u v * C j) t₂
      = (u - ((1 / 2 : ℝ) - (1 / 2 : ℝ) * Real.tanh ((1 / 2) * (u ⬝ᵥ (B j *ᵥ v)
          - Real.log ((Finset.univ.filter fun s => sees t₂ s ∧ s ≠ t₂).card : ℝ)))) • v)
        ᵥ* C j := fun j => by
    rw [Matrix.mul_apply_eq_vecMul, row_two_tokens_fam t₁ t₂ h12 hs2 hs1 (B j) u v]
  rw [row_sum_fam, Finset.sum_congr rfl fun j _ => hi j]
  -- collect the terms
  simp only [Matrix.vecMul_sum, Matrix.sub_vecMul, Matrix.smul_vecMul, sub_smul,
    Finset.sum_sub_distrib, Finset.smul_sum]
  abel

/-! ### Helpers: Step 2 (copied from `OneBlock/Attention.lean`) -/

/-- Helper: `τ ↦ x N(τ)` has the derivative `x N'`. -/
private theorem hasDerivAt_vecMul_fam {m n : Type*} [Fintype m] [Fintype n] (x : m → ℝ)
    {N : ℝ → Matrix m n ℝ} {N' : Matrix m n ℝ} (hN : HasDerivAt N N' 0) :
    HasDerivAt (fun τ => x ᵥ* N τ) (x ᵥ* N') 0 :=
  hasDerivAt_pi.2 fun b => HasDerivAt.fun_sum (u := Finset.univ) fun a _ =>
    (hasDerivAt_pi.1 (hasDerivAt_pi.1 hN a) b).const_mul (x a)

/-- Helper: `τ ↦ N(τ) y` has the derivative `N' y`. -/
private theorem hasDerivAt_mulVec_fam {m n : Type*} [Fintype m] [Fintype n] (y : n → ℝ)
    {N : ℝ → Matrix m n ℝ} {N' : Matrix m n ℝ} (hN : HasDerivAt N N' 0) :
    HasDerivAt (fun τ => N τ *ᵥ y) (N' *ᵥ y) 0 :=
  hasDerivAt_pi.2 fun a => HasDerivAt.fun_sum (u := Finset.univ) fun b _ =>
    (hasDerivAt_pi.1 (hasDerivAt_pi.1 hN a) b).mul_const (y b)

/-- Helper: the derivative at `0` of `τ ↦ x M(τ) + γ(τ) + ∑_i tanh(x c_i(τ) + β_i) a_i(τ)`, in the
form of `UnitsRigid`. -/
private theorem hasDerivAt_units_fam {n k q : Type*} [Fintype n] [Fintype k] [Fintype q]
    (x : n → ℝ) {Mf : ℝ → Matrix n k ℝ} {γf : ℝ → k → ℝ} {cf : q → ℝ → n → ℝ} (β : q → ℝ)
    {af : q → ℝ → k → ℝ} {M' : Matrix n k ℝ} {γ' : k → ℝ} {c' c0 : q → n → ℝ}
    {a' a0 : q → k → ℝ} (hM : HasDerivAt Mf M' 0) (hγ : HasDerivAt γf γ' 0)
    (hc : ∀ i, HasDerivAt (cf i) (c' i) 0) (ha : ∀ i, HasDerivAt (af i) (a' i) 0)
    (hc0 : ∀ i, cf i 0 = c0 i) (ha0 : ∀ i, af i 0 = a0 i) :
    HasDerivAt (fun τ => x ᵥ* Mf τ + γf τ + ∑ i, Real.tanh (x ⬝ᵥ cf i τ + β i) • af i τ)
      (x ᵥ* M' + γ' + ∑ i, (Real.tanh (x ⬝ᵥ c0 i + β i) • a' i
        + ((1 - Real.tanh (x ⬝ᵥ c0 i + β i) ^ 2) * (x ⬝ᵥ c' i + 0)) • a0 i)) 0 := by
  -- the chain rule through `tanh` for every unit
  have hth : ∀ i, HasDerivAt (fun τ => Real.tanh (x ⬝ᵥ cf i τ + β i))
      ((1 - Real.tanh (x ⬝ᵥ c0 i + β i) ^ 2) * (x ⬝ᵥ c' i + 0)) 0 := by
    intro i
    have hdot : HasDerivAt (fun τ => x ⬝ᵥ cf i τ + β i) (x ⬝ᵥ c' i + 0) 0 :=
      (HasDerivAt.fun_sum (u := Finset.univ) fun j _ =>
        (hasDerivAt_pi.1 (hc i) j).const_mul (x j)).add (hasDerivAt_const (0 : ℝ) (β i))
    exact (hasDerivAt_tanh _).comp_of_eq (0 : ℝ) hdot (by simp only [hc0])
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) fun i _ => (hth i).smul (ha i)
  exact (((hasDerivAt_vecMul_fam x hM).add hγ).add hsum).congr_deriv (by simp only [hc0, ha0])

/-- Helper: a matrix `N` with `N v = 0` for all `v` near `v₀` is `0`. -/
private theorem eq_zero_of_mulVec_fam {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    {P : (n → ℝ) → Prop} {v₀ : n → ℝ} (hP : ∀ᶠ v in nhds v₀, P v) (N : Matrix m n ℝ)
    (h : ∀ v, P v → N *ᵥ v = 0) : N = 0 := by
  -- the kernel of `v ↦ N v` has nonempty interior, so it is everything
  have hK : LinearMap.ker (Matrix.mulVecLin N) = ⊤ := by
    refine Submodule.eq_top_of_nonempty_interior' _ ⟨v₀, ?_⟩
    exact interior_mono (fun v hv => LinearMap.mem_ker.2 (h v hv))
      (mem_interior_iff_mem_nhds.2 hP)
  ext a b
  have h1 : Pi.single b 1 ∈ LinearMap.ker (Matrix.mulVecLin N) := hK ▸ Submodule.mem_top
  have h2 := congrFun (LinearMap.mem_ker.1 h1) a
  rw [Matrix.mulVecLin_apply, Matrix.mulVec_single_one] at h2
  exact h2

/-- Helper: a matrix `N` with `v N = 0` for all `v` near `v₀` is `0`. -/
private theorem eq_zero_of_vecMul_fam {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    {P : (m → ℝ) → Prop} {v₀ : m → ℝ} (hP : ∀ᶠ v in nhds v₀, P v) (N : Matrix m n ℝ)
    (h : ∀ v, P v → v ᵥ* N = 0) : N = 0 :=
  Matrix.transpose_eq_zero.1 (eq_zero_of_mulVec_fam hP Nᵀ fun v hv => by
    rw [Matrix.mulVec_transpose]
    exact h v hv)

/-- Helper: row `t` of a sum of two matrices. -/
private theorem row_add_fam {m n : Type*} (A B : Matrix m n ℝ) (t : m) :
    (A + B) t = A t + B t :=
  rfl

/-- **Step 2 for a family of heads:** let token `t₂` see itself and another token `t₁`. Let
`M(τ)`, `B_j(τ)`, `C_j(τ)` be curves of matrices with the derivatives `dM`, `dB_j`, `dC_j` at
`τ = 0`, and let some `v` have the columns `B_j(0) v^⊤` nonzero and pairwise non-collinear and
every row `v C_j(0)` nonzero. If at every input `x` the output
`x M(τ) + ∑_j P_{B_j(τ)}(x) x C_j(τ)` has derivative `0` at `τ = 0`, then `dM = 0` and
`dB_j = 0`, `dC_j = 0` for every head. -/
theorem attnFamily_rigid (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁)
    (Mc : ℝ → Matrix dIn dOut ℝ) (Bc : J → ℝ → Matrix dIn dIn ℝ)
    (Cc : J → ℝ → Matrix dIn dOut ℝ) (dM : Matrix dIn dOut ℝ) (dB : J → Matrix dIn dIn ℝ)
    (dC : J → Matrix dIn dOut ℝ) (hM : HasDerivAt Mc dM 0)
    (hB : ∀ j, HasDerivAt (Bc j) (dB j) 0) (hC : ∀ j, HasDerivAt (Cc j) (dC j) 0)
    (hv : ∃ v : dIn → ℝ, (∀ j, Bc j 0 *ᵥ v ≠ 0)
      ∧ (∀ i j, i ≠ j → ∀ r : ℝ, Bc i 0 *ᵥ v ≠ r • (Bc j 0 *ᵥ v))
      ∧ (∀ j, v ᵥ* Cc j 0 ≠ 0))
    (hflat : ∀ x : Matrix T dIn ℝ, HasDerivAt
      (fun τ : ℝ => x * Mc τ + ∑ j, attnWeights sees (x * Bc j τ * xᵀ) * x * Cc j τ) 0 0) :
    dM = 0 ∧ ∀ j, dB j = 0 ∧ dC j = 0 := by
  classical
  -- `lk = log k`, `k` the number of tokens other than `t₂` that `t₂` sees
  obtain ⟨lk, hlk⟩ : ∃ lk : ℝ,
      lk = Real.log ((Finset.univ.filter fun s => sees t₂ s ∧ s ≠ t₂).card : ℝ) := ⟨_, rfl⟩
  -- equation (8) along the curves, differentiated at `τ = 0`, for all `u` and `v`
  have hzero : ∀ u v : dIn → ℝ,
      u ᵥ* (dM + ∑ j, dC j) + -(1 / 2 : ℝ) • (v ᵥ* ∑ j, dC j)
        + ∑ j, (Real.tanh (u ⬝ᵥ ((1 / 2 : ℝ) • (Bc j 0 *ᵥ v)) + -(1 / 2) * lk)
            • ((1 / 2 : ℝ) • (v ᵥ* dC j))
          + ((1 - Real.tanh (u ⬝ᵥ ((1 / 2 : ℝ) • (Bc j 0 *ᵥ v)) + -(1 / 2) * lk) ^ 2)
              * (u ⬝ᵥ ((1 / 2 : ℝ) • (dB j *ᵥ v)) + 0))
            • ((1 / 2 : ℝ) • (v ᵥ* Cc j 0))) = 0 := by
    intro u v
    have hG := hasDerivAt_units_fam u
      (Mf := fun τ => Mc τ + ∑ j, Cc j τ)
      (γf := fun τ => -(1 / 2 : ℝ) • (v ᵥ* ∑ j, Cc j τ))
      (cf := fun j τ => (1 / 2 : ℝ) • (Bc j τ *ᵥ v)) (fun _ => -(1 / 2) * lk)
      (af := fun j τ => (1 / 2 : ℝ) • (v ᵥ* Cc j τ))
      (c0 := fun j => (1 / 2 : ℝ) • (Bc j 0 *ᵥ v))
      (a0 := fun j => (1 / 2 : ℝ) • (v ᵥ* Cc j 0))
      (hM.add (HasDerivAt.fun_sum (u := Finset.univ) fun j _ => hC j))
      ((hasDerivAt_vecMul_fam v (HasDerivAt.fun_sum (u := Finset.univ) fun j _ =>
        hC j)).const_smul (-(1 / 2 : ℝ)))
      (fun j => (hasDerivAt_mulVec_fam v (hB j)).const_smul (1 / 2 : ℝ))
      (fun j => (hasDerivAt_vecMul_fam v (hC j)).const_smul (1 / 2 : ℝ))
      (fun j => rfl) (fun j => rfl)
    have hF := hasDerivAt_pi.1 (hflat (twoTokenInput t₂ u v)) t₂
    refine hG.unique (hF.congr_of_eventuallyEq (Filter.Eventually.of_forall fun τ => ?_))
    dsimp only
    -- equation (8) at `τ`
    have h8 := attnFamily_two_tokens t₁ t₂ h12 hs2 hs1 (fun j => Bc j τ) (fun j => Cc j τ) u v
    rw [← hlk] at h8
    have hu : twoTokenInput t₂ u v t₂ = u := ite_eq_left rfl
    have hS : ∑ j, Real.tanh (u ⬝ᵥ ((1 / 2 : ℝ) • (Bc j τ *ᵥ v)) + -(1 / 2) * lk)
          • ((1 / 2 : ℝ) • (v ᵥ* Cc j τ))
        = ∑ j, ((1 / 2 : ℝ) * Real.tanh ((1 / 2) * (u ⬝ᵥ (Bc j τ *ᵥ v) - lk)))
          • (v ᵥ* Cc j τ) := Finset.sum_congr rfl fun j _ => by
      have harg : u ⬝ᵥ ((1 / 2 : ℝ) • (Bc j τ *ᵥ v)) + -(1 / 2) * lk
          = (1 / 2) * (u ⬝ᵥ (Bc j τ *ᵥ v) - lk) := by
        rw [dotProduct_smul, smul_eq_mul]
        ring
      rw [harg, smul_smul, mul_comm]
    rw [row_add_fam, Matrix.mul_apply_eq_vecMul, hu, h8, hS, Matrix.vecMul_add, neg_smul]
    abel
  -- Step 2, Lemma C.3 for tanh, at every `v` with the three properties
  have hstep : ∀ v : dIn → ℝ, (∀ j, Bc j 0 *ᵥ v ≠ 0)
      → (∀ i j, i ≠ j → ∀ r : ℝ, Bc i 0 *ᵥ v ≠ r • (Bc j 0 *ᵥ v))
      → (∀ j, v ᵥ* Cc j 0 ≠ 0)
      → dM + ∑ j, dC j = 0 ∧ (∀ j, dB j *ᵥ v = 0) ∧ (∀ j, v ᵥ* dC j = 0) := by
    intro v h1 h2 h3
    have hhalf : (1 / 2 : ℝ) ≠ 0 := by norm_num
    obtain ⟨hψM, -, hψc, -, hψa⟩ := tanh_unitsRigid dIn dOut J
      (fun j => (1 / 2 : ℝ) • (Bc j 0 *ᵥ v)) (fun _ => -(1 / 2) * lk)
      (fun j => (1 / 2 : ℝ) • (v ᵥ* Cc j 0)) (dM + ∑ j, dC j)
      (-(1 / 2 : ℝ) • (v ᵥ* ∑ j, dC j)) (fun j => (1 / 2 : ℝ) • (dB j *ᵥ v)) 0
      (fun j => (1 / 2 : ℝ) • (v ᵥ* dC j))
      (fun j => smul_ne_zero hhalf (h3 j)) (fun j => smul_ne_zero hhalf (h1 j))
      (fun i j hij r hr => h2 i j hij r (by
        rw [smul_comm r] at hr
        exact smul_right_injective _ hhalf hr))
      (fun x => hzero x v)
    refine ⟨hψM, fun j => ?_, fun j => ?_⟩
    · have h := congrFun hψc j
      simpa [hhalf] using h
    · have h := congrFun hψa j
      simpa [hhalf] using h
  -- the `v` with the three properties form a neighbourhood of the given one
  obtain ⟨v₀, hv1, hv2, hv3⟩ := hv
  have hBc : ∀ j, Continuous fun v : dIn → ℝ => Bc j 0 *ᵥ v :=
    fun j => continuous_const.matrix_mulVec continuous_id
  have hCc : ∀ j, Continuous fun v : dIn → ℝ => v ᵥ* Cc j 0 :=
    fun j => continuous_id.matrix_vecMul continuous_const
  have hnhds : ∀ᶠ v in nhds v₀, (∀ j, Bc j 0 *ᵥ v ≠ 0)
      ∧ (∀ i j, i ≠ j → ∀ r : ℝ, Bc i 0 *ᵥ v ≠ r • (Bc j 0 *ᵥ v))
      ∧ (∀ j, v ᵥ* Cc j 0 ≠ 0) := by
    refine (Filter.eventually_all.2 fun j => (hBc j).continuousAt.eventually_ne (hv1 j)).and
      ((Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => ?_).and
        (Filter.eventually_all.2 fun j => (hCc j).continuousAt.eventually_ne (hv3 j)))
    by_cases hij : i = j
    · exact Filter.Eventually.of_forall fun _ h => absurd hij h
    · -- non-collinearity of a pair is linear independence, an open condition
      have hli : LinearIndependent ℝ ![Bc i 0 *ᵥ v₀, Bc j 0 *ᵥ v₀] := by
        rw [linearIndependent_fin2]
        exact ⟨hv1 j, fun r h => hv2 i j hij r h.symm⟩
      have hcont : Continuous fun v : dIn → ℝ => ![Bc i 0 *ᵥ v, Bc j 0 *ᵥ v] :=
        continuous_pi (Fin.forall_fin_two.2 ⟨hBc i, hBc j⟩)
      refine ((hcont.tendsto v₀).eventually hli.eventually).mono fun v hv _ r h => ?_
      rw [linearIndependent_fin2] at hv
      exact hv.2 r h.symm
  -- a matrix that kills every `v` of a neighbourhood is `0`
  have hdB : ∀ j, dB j = 0 := fun j =>
    eq_zero_of_mulVec_fam hnhds _ fun v hv => (hstep v hv.1 hv.2.1 hv.2.2).2.1 j
  have hdC : ∀ j, dC j = 0 := fun j =>
    eq_zero_of_vecMul_fam hnhds _ fun v hv => (hstep v hv.1 hv.2.1 hv.2.2).2.2 j
  have hM0 := (hstep v₀ hv1 hv2 hv3).1
  simp only [hdC, Finset.sum_const_zero, add_zero] at hM0
  exact ⟨hM0, fun j => ⟨hdB j, hdC j⟩⟩

end Skips
