import SkipsLean.Depth.StepTanh

/-!
# Generic rays: the exponents of the gates are independent over `ℚ`

Paper (dimension): Appendix D.5, proof of Lemma D.12, "A generic ray", condition (i): "the numbers
`r_1, …, r_q` are linearly independent over `ℚ`", where `r_j = |ξ c_j|^p`. "These `ξ` are dense in
`C_k`. For (i): if integers `κ_1, …, κ_q` are not all zero, `∑_j κ_j r_j` is
`ξ (∑_j κ_j c_j c_j^⊤) ξ^⊤` for GELU and GeGLU blocks and `ξ ∑_j κ_j s_j c_j` for SwiGLU blocks,
and by (K3) it vanishes only for `ξ` on a quadric, or in a hyperplane."

Stated here for the hidden units of several tokens: `Ξ` has one row `ξ_t` per token, and the
numbers `|ξ_t c_j|` (`p = 1`), or `(ξ_t c_j)²` (`p = 2`), over all tokens `t` and all hidden units
`j`, are linearly independent over `ℚ` for a dense set of `Ξ`. (For `p = 1` the sign of `ξ_t c_j`
does not matter for the independence.) The same statement for the numbers `ξ_t c_j` themselves is
`dense_setOf_linearIndependent_mul` in `Depth/StepTanh.lean`.
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise Topology

variable {T d : Type*} [Fintype T] [Fintype d] [DecidableEq d]

/-- Helper: real numbers `x_i` that are linearly independent over `ℚ` stay independent after taking
absolute values, since `|x_i| = ε_i x_i` with signs `ε_i = ±1`, units of `ℚ`. -/
private theorem linearIndependent_abs_of_linearIndependent {ι : Type*} {x : ι → ℝ}
    (hx : LinearIndependent ℚ x) : LinearIndependent ℚ (fun i => |x i|) := by
  classical
  let w : ι → ℚˣ := fun i => if 0 ≤ x i then 1 else -1
  convert hx.units_smul w using 1
  funext i
  simp only [Pi.smul_apply', w, Units.smul_def]
  split_ifs with hi
  · rw [abs_of_nonneg hi, Units.val_one, one_smul]
  · rw [abs_of_neg (not_le.1 hi), Units.val_neg, Units.val_one, neg_smul, one_smul]

omit [Fintype T] [Fintype d] [DecidableEq d] in
/-- Helper: the set where `f` does not vanish is dense if `f` is quadratic along lines,
`f (x + τ y) = f x + τ g(x, y) + τ² f y`, and `f x₀ ≠ 0` for some `x₀`. From a zero `x` of `f`,
`f (x + ε x₀) = ε (g(x, x₀) + ε f x₀)` is not zero for small `ε ≠ 0`. -/
private theorem dense_setOf_ne_zero_of_quadratic (f : Matrix T d ℝ → ℝ)
    (g : Matrix T d ℝ → Matrix T d ℝ → ℝ)
    (hq : ∀ x y (τ : ℝ), f (x + τ • y) = f x + τ * g x y + τ ^ 2 * f y)
    {x₀ : Matrix T d ℝ} (hx₀ : f x₀ ≠ 0) : Dense {x | f x ≠ 0} := by
  intro x
  by_cases hx : f x ≠ 0
  · exact subset_closure hx
  rw [not_not] at hx
  -- the points `x + ε x₀` tend to `x` as `ε → 0`
  have ht : Filter.Tendsto (fun ε : ℝ => x + ε • x₀) (𝓝[≠] 0) (𝓝 x) := by
    have hc : Continuous (fun ε : ℝ => x + ε • x₀) :=
      continuous_const.add (continuous_id.smul continuous_const)
    have h0 := hc.tendsto 0
    rw [zero_smul, add_zero] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  -- for small `ε ≠ 0`, `g(x, x₀) + ε f x₀ ≠ 0` (if `g(x, x₀) = 0`, because `f x₀ ≠ 0`)
  have hev : ∀ᶠ ε in 𝓝[≠] (0 : ℝ), ε ≠ 0 ∧ g x x₀ + ε * f x₀ ≠ 0 := by
    by_cases hb : g x x₀ = 0
    · refine eventually_nhdsWithin_of_forall fun ε hε => ⟨hε, ?_⟩
      rw [hb, zero_add]
      exact mul_ne_zero hε hx₀
    · have hc : Continuous fun ε : ℝ => g x x₀ + ε * f x₀ := by fun_prop
      have h0 : ∀ᶠ ε in 𝓝 (0 : ℝ), g x x₀ + ε * f x₀ ≠ 0 :=
        (hc.continuousAt (x := 0)).eventually_ne (by simpa using hb)
      filter_upwards [self_mem_nhdsWithin, h0.filter_mono nhdsWithin_le_nhds] with ε hε h1
      exact ⟨hε, h1⟩
  refine mem_closure_of_tendsto ht (hev.mono fun ε hε => ?_)
  show f (x + ε • x₀) ≠ 0
  rw [hq, hx, zero_add, show ε * g x x₀ + ε ^ 2 * f x₀ = ε * (g x x₀ + ε * f x₀) by ring]
  exact mul_ne_zero hε.1 hε.2

/-- **(i) on a generic ray, `p = 1`:** if the columns `c_j` are linearly independent over `ℚ`, then
for a dense set of matrices `Ξ` the numbers `|ξ_t c_j|`, over all tokens and all hidden units, are
linearly independent over `ℚ`. -/
theorem dense_setOf_linearIndependent_abs_dotProduct {q : Type*} [Fintype q] (c : q → d → ℝ)
    (hc : LinearIndependent ℚ c) :
    Dense {Ξ : Matrix T d ℝ | LinearIndependent ℚ (fun i : T × q => |Ξ i.1 ⬝ᵥ c i.2|)} := by
  -- the numbers `ξ_t c_j` are independent over `ℚ` for a dense set of `Ξ`
  -- (`dense_setOf_linearIndependent_mul` with `W_{i j} = c_j i`, so that `(Ξ W)_{t j} = ξ_t c_j`),
  -- and then so are their absolute values
  have h := dense_setOf_linearIndependent_mul (T := T) (Matrix.of fun i j => c j i) hc
  exact h.mono fun Ξ hΞ => linearIndependent_abs_of_linearIndependent hΞ

/-- **(i) on a generic ray, `p = 2`:** if the matrices `c_j c_j^⊤` are linearly independent over
`ℚ`, then for a dense set of matrices `Ξ` the numbers `(ξ_t c_j)²`, over all tokens and all hidden
units, are linearly independent over `ℚ`. -/
theorem dense_setOf_linearIndependent_sq_dotProduct {q : Type*} [Fintype q] (c : q → d → ℝ)
    (hc : LinearIndependent ℚ (fun j : q => Matrix.vecMulVec (c j) (c j))) :
    Dense {Ξ : Matrix T d ℝ | LinearIndependent ℚ (fun i : T × q => (Ξ i.1 ⬝ᵥ c i.2) ^ 2)} := by
  classical
  -- for `κ : T × q → ℚ`, the quadratic function `Ξ ↦ ∑ κ_{t j} (ξ_t c_j)²`
  let Q : (T × q → ℚ) → Matrix T d ℝ → ℝ := fun κ Ξ =>
    ∑ p : T × q, (κ p : ℝ) * (Ξ p.1 ⬝ᵥ c p.2) ^ 2
  -- the set is the intersection, over `κ ≠ 0`, of the sets where `Q κ` does not vanish
  have hset : {Ξ : Matrix T d ℝ | LinearIndependent ℚ (fun i : T × q => (Ξ i.1 ⬝ᵥ c i.2) ^ 2)}
      = ⋂ κ : {κ : T × q → ℚ // κ ≠ 0}, {Ξ | Q κ.1 Ξ ≠ 0} := by
    ext Ξ
    simp only [Set.mem_iInter]
    show LinearIndependent ℚ _ ↔ ∀ κ : {κ : T × q → ℚ // κ ≠ 0}, Q κ.1 Ξ ≠ 0
    rw [Fintype.linearIndependent_iff]
    simp only [Rat.smul_def]
    constructor
    · rintro hli ⟨κ, hκ⟩ h0
      exact hκ (funext (hli κ h0))
    · intro h κ h0
      by_contra hne
      exact h ⟨κ, fun hκ => hne fun i => by rw [hκ]; rfl⟩ h0
  rw [hset]
  -- Baire: a countable intersection of open dense sets is dense
  have : BaireSpace (Matrix T d ℝ) := inferInstanceAs (BaireSpace (T → d → ℝ))
  refine dense_iInter_of_isOpen (fun κ => isOpen_ne_fun ?_ continuous_const) (fun κ => ?_)
  · -- `Q κ` is continuous
    show Continuous fun Ξ : Matrix T d ℝ => ∑ p : T × q, (κ.1 p : ℝ) * (Ξ p.1 ⬝ᵥ c p.2) ^ 2
    fun_prop
  obtain ⟨κ, hκ⟩ := κ
  -- a token `t₀` and a hidden unit `j₀` with `κ_{t₀ j₀} ≠ 0`
  obtain ⟨⟨t₀, j₀⟩, hj₀⟩ : ∃ p, κ p ≠ 0 := by
    by_contra hne
    push Not at hne
    exact hκ (funext hne)
  -- the quadratic form `ξ ↦ ξ S ξ^⊤ = ∑_j κ_{t₀ j} (ξ c_j)²` of `S = ∑_j κ_{t₀ j} c_j c_j^⊤` is not
  -- identically zero: otherwise polarization gives `S = 0`, against `hc`
  obtain ⟨ξ₀, hξ₀⟩ : ∃ ξ₀ : d → ℝ, ∑ j, (κ (t₀, j) : ℝ) * (ξ₀ ⬝ᵥ c j) ^ 2 ≠ 0 := by
    by_contra hne
    push Not at hne
    -- `S_{a b} = 0`: evaluate the form at `e_a`, `e_b` and `e_a + e_b`
    have hS : ∀ a b, ∑ j, (κ (t₀, j) : ℝ) * (c j a * c j b) = 0 := by
      intro a b
      have ha := hne (Pi.single a 1)
      have hb := hne (Pi.single b 1)
      have hab := hne (Pi.single a 1 + Pi.single b 1)
      simp only [add_dotProduct, single_dotProduct, one_mul] at ha hb hab
      have e : ∑ j, (κ (t₀, j) : ℝ) * (c j a + c j b) ^ 2 = ∑ j, (κ (t₀, j) : ℝ) * c j a ^ 2
          + ∑ j, (κ (t₀, j) : ℝ) * c j b ^ 2 + 2 * ∑ j, (κ (t₀, j) : ℝ) * (c j a * c j b) := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun j _ => by ring
      linarith
    refine hj₀ (Fintype.linearIndependent_iff.1 hc (fun j => κ (t₀, j)) ?_ j₀)
    ext a b
    simp only [Matrix.sum_apply, Matrix.smul_apply, Rat.smul_def, vecMulVec_apply,
      Matrix.zero_apply]
    exact hS a b
  -- `Ξ₀` with the row `ξ₀` at `t₀` and zero rows elsewhere has `Q κ Ξ₀ ≠ 0`
  obtain ⟨Ξ₀, h0, hne0⟩ : ∃ Ξ₀ : Matrix T d ℝ, Ξ₀ t₀ = ξ₀ ∧ ∀ t, t ≠ t₀ → Ξ₀ t = 0 :=
    ⟨Pi.single (M := fun _ : T => d → ℝ) t₀ ξ₀, Pi.single_eq_same (M := fun _ : T => d → ℝ) t₀ ξ₀,
      fun t ht => Pi.single_eq_of_ne (M := fun _ : T => d → ℝ) ht ξ₀⟩
  have hQ0 : Q κ Ξ₀ ≠ 0 := by
    show ∑ p : T × q, (κ p : ℝ) * (Ξ₀ p.1 ⬝ᵥ c p.2) ^ 2 ≠ 0
    rw [Fintype.sum_prod_type, Finset.sum_eq_single t₀]
    · simpa only [h0] using hξ₀
    · intro t _ ht
      exact Finset.sum_eq_zero fun j _ => by simp [hne0 t ht]
    · intro h; exact absurd (Finset.mem_univ t₀) h
  -- `Q κ (x + τ y) = Q κ x + τ B(x, y) + τ² Q κ y`: a nonzero quadratic polynomial in `τ`
  refine dense_setOf_ne_zero_of_quadratic (Q κ)
    (fun x y => ∑ p : T × q, (κ p : ℝ) * (2 * (x p.1 ⬝ᵥ c p.2) * (y p.1 ⬝ᵥ c p.2)))
    (fun x y τ => ?_) hQ0
  have hrow : ∀ t, (x + τ • y) t = x t + τ • y t := fun t => rfl
  simp only [Q, hrow, add_dotProduct, smul_dotProduct, smul_eq_mul, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun p _ => by ring

end Skips
