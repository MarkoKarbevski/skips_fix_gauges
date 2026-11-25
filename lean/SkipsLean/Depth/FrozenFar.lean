import SkipsLean.Depth.Frozen
import SkipsLean.Activations.GateFar

/-!
# The network after `h_k` far out in its cone

Paper (dimension): Lemma D.11 (The network after `h_k` far out in its cone). "In the case (n), for
gated blocks, let `θ` be good, `k ≤ L`, `h° ∈ C_k`, and let `η` be a direction of the weights of
the blocks `k+1, …, L` and of `D`. There are numbers `ϱ, κ, t₀ > 0` such that, for `t ≥ t₀`, the
maps `u ↦ 𝓑_{>k}(t (h° + u))` and `u ↦ 𝐃_θ 𝓑_{>k}(t (h° + u)) η` extend to holomorphic maps on the
rows `u ∈ ℂ^{1×d_model}` with `|u_j| ≤ ϱ` for all `j`, and for these `u`, at `h = t (h° + u)`,

  `‖𝓑_{>k}(h) − 𝓑°_{>k}(h)‖ ≤ e^{−κ t^p}`,   `‖𝐃_θ 𝓑_{>k}(h) η − 𝐃_θ 𝓑°_{>k}(h) η‖ ≤ e^{−κ t^p}`."

The paper uses the complex rows `u` in one place: in the proof of Lemma D.12, fact (b), Cauchy's
estimate turns the first bound into the same bound for the derivative `𝐃𝓑_{>k} − 𝐃𝓑°_{>k}` in the
hidden state. The statement here is for real `u` and has this bound for the derivative as a third
clause in its place; the holomorphic extension with the two bounds on the complex polydisc:
`Depth/FrozenFarHolomorphic.lean`. A hidden state has the rows `T`, and
`h°` is a matrix `H` all of whose rows lie in `C_k`. The gate is any `σ` with `GateFar σ σ' p`
(SiLU with `p = 1`, GELU with `p = 2`).
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise Topology

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]
variable {σ σ' : ℝ → ℝ} {p : ℕ}

open Filter

/-! ### Families that are exponentially small, or polynomially bounded, in `t` -/

/-- Eventually in `t`, uniformly in `i ∈ S`: `f t i ≤ c t^N e^{-a t^p}` for some `a > 0`. -/
private def ExpSmall (p : ℕ) {ι : Type*} (S : Set ι) (f : ℝ → ι → ℝ) : Prop :=
  ∃ a : ℝ, 0 < a ∧ ∃ c : ℝ, ∃ N : ℕ,
    ∀ᶠ t in atTop, ∀ i ∈ S, f t i ≤ c * t ^ N * Real.exp (-(a * t ^ p))

/-- Eventually in `t`, uniformly in `i ∈ S`: `f t i ≤ c t^N`. -/
private def PolyB {ι : Type*} (S : Set ι) (f : ℝ → ι → ℝ) : Prop :=
  ∃ c : ℝ, ∃ N : ℕ, ∀ᶠ t in atTop, ∀ i ∈ S, f t i ≤ c * t ^ N

section Asymptotics

variable {ι : Type*} {S : Set ι}

private theorem ExpSmall.mono {f g : ℝ → ι → ℝ} (hg : ExpSmall p S g)
    (h : ∀ᶠ t in atTop, ∀ i ∈ S, f t i ≤ g t i) : ExpSmall p S f := by
  obtain ⟨a, ha, c, N, hb⟩ := hg
  exact ⟨a, ha, c, N, by filter_upwards [hb, h] with t h1 h2 i hi using (h2 i hi).trans (h1 i hi)⟩

private theorem PolyB.mono {f g : ℝ → ι → ℝ} (hg : PolyB S g)
    (h : ∀ᶠ t in atTop, ∀ i ∈ S, f t i ≤ g t i) : PolyB S f := by
  obtain ⟨c, N, hb⟩ := hg
  exact ⟨c, N, by filter_upwards [hb, h] with t h1 h2 i hi using (h2 i hi).trans (h1 i hi)⟩

/-- `c t^N e^{-a t^p}` itself. -/
private theorem expSmall_monomial {a : ℝ} (ha : 0 < a) (c : ℝ) (N : ℕ) :
    ExpSmall p S (fun t _ => c * t ^ N * Real.exp (-(a * t ^ p))) :=
  ⟨a, ha, c, N, Eventually.of_forall fun _ _ _ => le_rfl⟩

/-- `c t^N` itself. -/
private theorem polyB_monomial (c : ℝ) (N : ℕ) : PolyB S (fun t _ => c * t ^ N) :=
  ⟨c, N, Eventually.of_forall fun _ _ _ => le_rfl⟩

/-- Helper: for `t ≥ 1`, `c t^N ≤ |c| t^M` when `N ≤ M`. -/
private theorem mul_pow_le_abs_mul_pow {t : ℝ} (ht : 1 ≤ t) (c : ℝ) {N M : ℕ} (hNM : N ≤ M) :
    c * t ^ N ≤ |c| * t ^ M :=
  mul_le_mul (le_abs_self c) (pow_le_pow_right₀ ht hNM) (pow_nonneg (zero_le_one.trans ht) _)
    (abs_nonneg c)

/-- The sum of two exponentially small families is exponentially small. -/
private theorem ExpSmall.add {f g : ℝ → ι → ℝ} (hf : ExpSmall p S f) (hg : ExpSmall p S g) :
    ExpSmall p S (fun t i => f t i + g t i) := by
  obtain ⟨a₁, ha₁, c₁, N₁, h₁⟩ := hf
  obtain ⟨a₂, ha₂, c₂, N₂, h₂⟩ := hg
  refine ⟨min a₁ a₂, lt_min ha₁ ha₂, |c₁| + |c₂|, N₁ + N₂, ?_⟩
  filter_upwards [h₁, h₂, eventually_ge_atTop 1] with t ht₁ ht₂ ht i hi
  -- each term is at most `|c| t^{N₁+N₂} e^{-min(a₁,a₂) t^p}`
  have key : ∀ (a c : ℝ) (N : ℕ), min a₁ a₂ ≤ a → N ≤ N₁ + N₂ →
      c * t ^ N * Real.exp (-(a * t ^ p))
        ≤ |c| * t ^ (N₁ + N₂) * Real.exp (-(min a₁ a₂ * t ^ p)) := by
    intro a c N ha hN
    have htp : 0 ≤ t ^ p := pow_nonneg (zero_le_one.trans ht) p
    have h2 : Real.exp (-(a * t ^ p)) ≤ Real.exp (-(min a₁ a₂ * t ^ p)) :=
      Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_right ha htp))
    calc c * t ^ N * Real.exp (-(a * t ^ p))
        ≤ |c| * t ^ (N₁ + N₂) * Real.exp (-(a * t ^ p)) :=
          mul_le_mul_of_nonneg_right (mul_pow_le_abs_mul_pow ht c hN) (Real.exp_pos _).le
      _ ≤ _ := mul_le_mul_of_nonneg_left h2
          (mul_nonneg (abs_nonneg c) (pow_nonneg (zero_le_one.trans ht) _))
  calc f t i + g t i
      ≤ c₁ * t ^ N₁ * Real.exp (-(a₁ * t ^ p)) + c₂ * t ^ N₂ * Real.exp (-(a₂ * t ^ p)) :=
        add_le_add (ht₁ i hi) (ht₂ i hi)
    _ ≤ |c₁| * t ^ (N₁ + N₂) * Real.exp (-(min a₁ a₂ * t ^ p))
          + |c₂| * t ^ (N₁ + N₂) * Real.exp (-(min a₁ a₂ * t ^ p)) :=
        add_le_add (key a₁ c₁ N₁ (min_le_left _ _) (Nat.le_add_right _ _))
          (key a₂ c₂ N₂ (min_le_right _ _) (Nat.le_add_left _ _))
    _ = (|c₁| + |c₂|) * t ^ (N₁ + N₂) * Real.exp (-(min a₁ a₂ * t ^ p)) := by ring

/-- The sum of two polynomially bounded families is polynomially bounded. -/
private theorem PolyB.add {f g : ℝ → ι → ℝ} (hf : PolyB S f) (hg : PolyB S g) :
    PolyB S (fun t i => f t i + g t i) := by
  obtain ⟨c₁, N₁, h₁⟩ := hf
  obtain ⟨c₂, N₂, h₂⟩ := hg
  refine ⟨|c₁| + |c₂|, N₁ + N₂, ?_⟩
  filter_upwards [h₁, h₂, eventually_ge_atTop 1] with t ht₁ ht₂ ht i hi
  calc f t i + g t i ≤ c₁ * t ^ N₁ + c₂ * t ^ N₂ := add_le_add (ht₁ i hi) (ht₂ i hi)
    _ ≤ |c₁| * t ^ (N₁ + N₂) + |c₂| * t ^ (N₁ + N₂) :=
        add_le_add (mul_pow_le_abs_mul_pow ht c₁ (Nat.le_add_right _ _))
          (mul_pow_le_abs_mul_pow ht c₂ (Nat.le_add_left _ _))
    _ = (|c₁| + |c₂|) * t ^ (N₁ + N₂) := by ring

/-- An exponentially small family times a polynomially bounded one (both nonnegative) is
exponentially small. -/
private theorem ExpSmall.mul {f g : ℝ → ι → ℝ} (hf : ExpSmall p S f) (hg : PolyB S g)
    (hf0 : ∀ᶠ t in atTop, ∀ i ∈ S, 0 ≤ f t i) (hg0 : ∀ᶠ t in atTop, ∀ i ∈ S, 0 ≤ g t i) :
    ExpSmall p S (fun t i => f t i * g t i) := by
  obtain ⟨a, ha, c₁, N₁, h₁⟩ := hf
  obtain ⟨c₂, N₂, h₂⟩ := hg
  refine ⟨a, ha, c₁ * c₂, N₁ + N₂, ?_⟩
  filter_upwards [h₁, h₂, hf0, hg0] with t ht₁ ht₂ hf0 hg0 i hi
  calc f t i * g t i ≤ (c₁ * t ^ N₁ * Real.exp (-(a * t ^ p))) * (c₂ * t ^ N₂) :=
        mul_le_mul (ht₁ i hi) (ht₂ i hi) (hg0 i hi) ((hf0 i hi).trans (ht₁ i hi))
    _ = c₁ * c₂ * t ^ (N₁ + N₂) * Real.exp (-(a * t ^ p)) := by ring

/-- An exponentially small family is polynomially bounded. -/
private theorem ExpSmall.polyB {f : ℝ → ι → ℝ} (hf : ExpSmall p S f) : PolyB S f := by
  obtain ⟨a, ha, c, N, h⟩ := hf
  refine ⟨|c|, N, ?_⟩
  filter_upwards [h, eventually_ge_atTop 0] with t ht ht0 i hi
  have he : Real.exp (-(a * t ^ p)) ≤ 1 :=
    Real.exp_le_one_iff.2 (neg_nonpos.2 (mul_nonneg ha.le (pow_nonneg ht0 p)))
  calc f t i ≤ c * t ^ N * Real.exp (-(a * t ^ p)) := ht i hi
    _ ≤ |c| * t ^ N * Real.exp (-(a * t ^ p)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self c) (pow_nonneg ht0 N))
          (Real.exp_pos _).le
    _ ≤ |c| * t ^ N * 1 :=
        mul_le_mul_of_nonneg_left he (mul_nonneg (abs_nonneg c) (pow_nonneg ht0 N))
    _ = |c| * t ^ N := mul_one _

/-- **Absorbing the powers of `t`:** an exponentially small family is eventually at most
`e^{-κ t^p}` for some `κ > 0` (here `p ≥ 1`). -/
private theorem ExpSmall.exists_bound (hp : 1 ≤ p) {f : ℝ → ι → ℝ} (hf : ExpSmall p S f) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ᶠ t in atTop, ∀ i ∈ S, f t i ≤ Real.exp (-(κ * t ^ p)) := by
  obtain ⟨a, ha, c, N, h⟩ := hf
  refine ⟨a / 2, half_pos ha, ?_⟩
  -- `|c| t^N e^{-a t / 2} → 0`
  have hlim := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (N : ℝ) (a / 2)
    (half_pos ha)).const_mul |c|
  rw [mul_zero] at hlim
  filter_upwards [h, hlim.eventually (Iic_mem_nhds one_pos), eventually_ge_atTop 1]
    with t ht hl ht1 i hi
  have ht0 : 0 ≤ t := zero_le_one.trans ht1
  rw [Real.rpow_natCast] at hl
  -- `t ≤ t^p`, so `e^{-a t^p / 2} ≤ e^{-a t / 2}`
  have htp : t ≤ t ^ p := le_self_pow₀ ht1 (by omega)
  have h1 : Real.exp (-(a / 2 * t ^ p)) ≤ Real.exp (-(a / 2) * t) := by
    apply Real.exp_le_exp.2
    have := mul_le_mul_of_nonneg_left htp (half_pos ha).le
    linarith
  have hsplit : Real.exp (-(a * t ^ p))
      = Real.exp (-(a / 2 * t ^ p)) * Real.exp (-(a / 2 * t ^ p)) := by
    rw [← Real.exp_add]; ring_nf
  calc f t i ≤ c * t ^ N * Real.exp (-(a * t ^ p)) := ht i hi
    _ ≤ |c| * t ^ N * Real.exp (-(a * t ^ p)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self c) (pow_nonneg ht0 N))
          (Real.exp_pos _).le
    _ = (|c| * (t ^ N * Real.exp (-(a / 2 * t ^ p)))) * Real.exp (-(a / 2 * t ^ p)) := by
        rw [hsplit]; ring
    _ ≤ (|c| * (t ^ N * Real.exp (-(a / 2) * t))) * Real.exp (-(a / 2 * t ^ p)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left h1 (pow_nonneg ht0 N)) (abs_nonneg c)) (Real.exp_pos _).le
    _ ≤ 1 * Real.exp (-(a / 2 * t ^ p)) := mul_le_mul_of_nonneg_right hl (Real.exp_pos _).le
    _ = Real.exp (-(a / 2 * t ^ p)) := one_mul _

/-- An exponentially small family is eventually at most any `ε > 0`. -/
private theorem ExpSmall.eventually_le (hp : 1 ≤ p) {f : ℝ → ι → ℝ} (hf : ExpSmall p S f)
    {ε : ℝ} (hε : 0 < ε) : ∀ᶠ t in atTop, ∀ i ∈ S, f t i ≤ ε := by
  obtain ⟨κ, hκ, h⟩ := hf.exists_bound hp
  have hlim : Tendsto (fun t : ℝ => Real.exp (-(κ * t ^ p))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp
      ((tendsto_pow_atTop (by omega)).const_mul_atTop hκ)
  filter_upwards [h, hlim.eventually (Iic_mem_nhds hε)] with t ht hl i hi
  exact (ht i hi).trans hl

end Asymptotics
/-! ### Matrices: entries and the elementwise norm -/

/-- An entry of a product: `|(M N)_{ik}| ≤ n ‖M‖ ‖N‖`. -/
private theorem abs_mul_apply_le {m n o : Type*} [Fintype m] [Fintype n] [Fintype o]
    (M : Matrix m n ℝ) (N : Matrix n o ℝ) (i : m) (k : o) :
    |(M * N) i k| ≤ Fintype.card n * ‖M‖ * ‖N‖ := by
  rw [Matrix.mul_apply]
  calc |∑ j, M i j * N j k| ≤ ∑ j, |M i j * N j k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : n, ‖M‖ * ‖N‖ := Finset.sum_le_sum fun j _ => by
        rw [abs_mul]
        have h1 : |M i j| ≤ ‖M‖ := by
          rw [← Real.norm_eq_abs]; exact Matrix.norm_apply_le_norm M
        have h2 : |N j k| ≤ ‖N‖ := by
          rw [← Real.norm_eq_abs]; exact Matrix.norm_apply_le_norm N
        exact mul_le_mul h1 h2 (abs_nonneg _) (norm_nonneg _)
    _ = Fintype.card n * ‖M‖ * ‖N‖ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc]

/-- A matrix whose entries are at most `r` has the norm at most `r`. -/
private theorem norm_le_of_abs_le {m n : Type*} [Fintype m] [Fintype n] {M : Matrix m n ℝ}
    {r : ℝ} (hr : 0 ≤ r) (h : ∀ i j, |M i j| ≤ r) : ‖M‖ ≤ r :=
  (Matrix.norm_le_iff hr).2 fun i j => by rw [Real.norm_eq_abs]; exact h i j

/-- `‖M N‖ ≤ n ‖M‖ ‖N‖` for the elementwise norm. -/
private theorem norm_mul_le' {m n o : Type*} [Fintype m] [Fintype n] [Fintype o]
    (M : Matrix m n ℝ) (N : Matrix n o ℝ) : ‖M * N‖ ≤ Fintype.card n * ‖M‖ * ‖N‖ :=
  norm_le_of_abs_le (by positivity) fun i k => abs_mul_apply_le M N i k

/-! ### The hidden units of a gated block, with any gate values -/

/-- The outputs of the hidden units of a gated block whose unit `j` has the gate value `a j`:
entry `(τ, j)` is `a_j(P_{τ, inl j}) P_{τ, inr j}` for the pre-activations `P`. -/
private def qa {m ι : Type*} (a : ι → ℝ → ℝ) (P : Matrix m (ι ⊕ ι) ℝ) : Matrix m ι ℝ :=
  Matrix.of fun τ j => a j (P τ (Sum.inl j)) * P τ (Sum.inr j)

/-- The derivative of `qa a` at `P` along `Pd`, for gate values with the derivatives `a' j`. -/
private def dqa {m ι : Type*} (a a' : ι → ℝ → ℝ) (P Pd : Matrix m (ι ⊕ ι) ℝ) : Matrix m ι ℝ :=
  Matrix.of fun τ j => a' j (P τ (Sum.inl j)) * Pd τ (Sum.inl j) * P τ (Sum.inr j)
    + a j (P τ (Sum.inl j)) * Pd τ (Sum.inr j)

private theorem qa_sub {m ι : Type*} (a b : ι → ℝ → ℝ) (P : Matrix m (ι ⊕ ι) ℝ) :
    qa a P - qa b P = qa (fun j z => a j z - b j z) P := by
  ext τ j; simp only [qa, Matrix.sub_apply, Matrix.of_apply]; ring

private theorem dqa_sub {m ι : Type*} (a a' b b' : ι → ℝ → ℝ) (P Pd : Matrix m (ι ⊕ ι) ℝ) :
    dqa a a' P Pd - dqa b b' P Pd
      = dqa (fun j z => a j z - b j z) (fun j z => a' j z - b' j z) P Pd := by
  ext τ j; simp only [dqa, Matrix.sub_apply, Matrix.of_apply]; ring

private theorem norm_qa_le {m ι : Type*} [Fintype m] [Fintype ι] {a : ι → ℝ → ℝ}
    {P : Matrix m (ι ⊕ ι) ℝ} {α Z : ℝ} (hα : 0 ≤ α) (hZ : 0 ≤ Z)
    (ha : ∀ τ j, |a j (P τ (Sum.inl j))| ≤ α) (hP : ∀ τ j, |P τ (Sum.inr j)| ≤ Z) :
    ‖qa a P‖ ≤ α * Z :=
  norm_le_of_abs_le (mul_nonneg hα hZ) fun τ j => by
    simp only [qa, Matrix.of_apply, abs_mul]
    exact mul_le_mul (ha τ j) (hP τ j) (abs_nonneg _) hα

private theorem norm_dqa_le {m ι : Type*} [Fintype m] [Fintype ι] {a a' : ι → ℝ → ℝ}
    {P Pd : Matrix m (ι ⊕ ι) ℝ} {α α' D D' Z : ℝ} (hα : 0 ≤ α) (hα' : 0 ≤ α') (hD : 0 ≤ D)
    (hD' : 0 ≤ D') (hZ : 0 ≤ Z)
    (ha : ∀ τ j, |a j (P τ (Sum.inl j))| ≤ α) (ha' : ∀ τ j, |a' j (P τ (Sum.inl j))| ≤ α')
    (hPg : ∀ τ j, |Pd τ (Sum.inl j)| ≤ D) (hPv : ∀ τ j, |Pd τ (Sum.inr j)| ≤ D')
    (hP : ∀ τ j, |P τ (Sum.inr j)| ≤ Z) :
    ‖dqa a a' P Pd‖ ≤ α' * D * Z + α * D' :=
  norm_le_of_abs_le (by positivity) fun τ j => by
    simp only [dqa, Matrix.of_apply]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul, abs_mul]
      exact mul_le_mul (mul_le_mul (ha' τ j) (hPg τ j) (abs_nonneg _) hα') (hP τ j)
        (abs_nonneg _) (mul_nonneg hα' hD)
    · rw [abs_mul]
      exact mul_le_mul (ha τ j) (hPv τ j) (abs_nonneg _) hα

/-- `qa a (c P) = c² qa a P` for gate values homogeneous of degree one. -/
private theorem qa_smul {m ι : Type*} {a : ι → ℝ → ℝ} (ha : ∀ j c z, a j (c * z) = c * a j z)
    (c : ℝ) (P : Matrix m (ι ⊕ ι) ℝ) : qa a (c • P) = c ^ 2 • qa a P := by
  ext τ j
  simp only [qa, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, ha]
  ring

/-- Helper: the product rule for matrix-valued functions of one real variable (as in
`Depth/StepTanh.lean`). -/
private theorem hasDerivAt_matMulF {m n o : Type*} [Fintype m] [Fintype n] [Fintype o]
    {A : ℝ → Matrix m n ℝ} {B : ℝ → Matrix n o ℝ} {A' : Matrix m n ℝ} {B' : Matrix n o ℝ}
    {τ : ℝ} (hA : HasDerivAt A A' τ) (hB : HasDerivAt B B' τ) :
    HasDerivAt (fun s => A s * B s) (A' * B τ + A τ * B') τ := by
  refine hasDerivAt_pi.2 fun t => hasDerivAt_pi.2 fun i => ?_
  have h := HasDerivAt.fun_sum (u := Finset.univ) fun j _ =>
    (hasDerivAt_pi.1 (hasDerivAt_pi.1 hA t) j).mul (hasDerivAt_pi.1 (hasDerivAt_pi.1 hB j) i)
  simp only [Matrix.mul_apply, Matrix.add_apply, ← Finset.sum_add_distrib]
  exact h

/-- Helper: the line `s ↦ a + s b` has the velocity `b`. -/
private theorem hasDerivAt_lineF {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (a b : E) :
    HasDerivAt (fun s : ℝ => a + s • b) b 0 := by
  have h := ((hasDerivAt_id (0 : ℝ)).smul_const b).const_add a
  rw [one_smul] at h
  exact h

/-- The derivative of `s ↦ qa a (P s)`. -/
private theorem hasDerivAt_qa {m ι : Type*} [Fintype m] [Fintype ι] {a a' : ι → ℝ → ℝ}
    (ha : ∀ j z, HasDerivAt (a j) (a' j z) z) {P : ℝ → Matrix m (ι ⊕ ι) ℝ}
    {Pd : Matrix m (ι ⊕ ι) ℝ} {τ : ℝ} (hP : HasDerivAt P Pd τ) :
    HasDerivAt (fun s => qa a (P s)) (dqa a a' (P τ) Pd) τ :=
  hasDerivAt_pi.2 fun t => hasDerivAt_pi.2 fun j =>
    ((ha j (P τ t (Sum.inl j))).comp τ (hasDerivAt_pi.1 (hasDerivAt_pi.1 hP t) (Sum.inl j))).mul
      (hasDerivAt_pi.1 (hasDerivAt_pi.1 hP t) (Sum.inr j))

/-- The block along a line of hidden states: `s ↦ qa a ((h + s v) W) V` has the derivative
`dqa a a' (h W) (v W) V` at `0`. -/
private theorem hasDerivAt_block_line {m ι n : Type*} [Fintype m] [Fintype ι] [Fintype n]
    {a a' : ι → ℝ → ℝ} (ha : ∀ j z, HasDerivAt (a j) (a' j z) z) (W : Matrix n (ι ⊕ ι) ℝ)
    (V : Matrix ι n ℝ) (h v : Matrix m n ℝ) :
    HasDerivAt (fun s : ℝ => qa a ((h + s • v) * W) * V) (dqa a a' (h * W) (v * W) * V) 0 := by
  have hP := hasDerivAt_matMulF (hasDerivAt_lineF h v) (hasDerivAt_const (0 : ℝ) W)
  have hQ := hasDerivAt_matMulF (hasDerivAt_qa ha hP) (hasDerivAt_const (0 : ℝ) V)
  simp only [zero_smul, add_zero, Matrix.mul_zero] at hQ
  exact hQ

/-- The block along a line of weights: `s ↦ qa a (h (W + s ηW)) (V + s ηV)` has the derivative
`dqa a a' (h W) (h ηW) V + qa a (h W) ηV` at `0`. -/
private theorem hasDerivAt_block_params {m ι n : Type*} [Fintype m] [Fintype ι] [Fintype n]
    {a a' : ι → ℝ → ℝ} (ha : ∀ j z, HasDerivAt (a j) (a' j z) z) (W ηW : Matrix n (ι ⊕ ι) ℝ)
    (V ηV : Matrix ι n ℝ) (h : Matrix m n ℝ) :
    HasDerivAt (fun s : ℝ => qa a (h * (W + s • ηW)) * (V + s • ηV))
      (dqa a a' (h * W) (h * ηW) * V + qa a (h * W) * ηV) 0 := by
  have hP := hasDerivAt_matMulF (hasDerivAt_const (0 : ℝ) h) (hasDerivAt_lineF W ηW)
  have hQ := hasDerivAt_matMulF (hasDerivAt_qa ha hP) (hasDerivAt_lineF V ηV)
  simp only [zero_smul, add_zero, Matrix.zero_mul, zero_add] at hQ
  exact hQ

/-! ### Frozen gate values -/

open Classical in
/-- The gate value of a frozen unit: `z` if the unit is active, `0` otherwise. -/
private noncomputable def aF {ι : Type*} (s : Finset ι) (j : ι) (z : ℝ) : ℝ :=
  if j ∈ s then z else 0

open Classical in
/-- Its derivative: `1` if the unit is active, `0` otherwise. -/
private noncomputable def aF' {ι : Type*} (s : Finset ι) (j : ι) (_z : ℝ) : ℝ :=
  if j ∈ s then 1 else 0

private theorem aF_of_mem {ι : Type*} {s : Finset ι} {j : ι} (h : j ∈ s) (z : ℝ) :
    aF s j z = z := by
  unfold aF; simp [h]

private theorem aF_of_notMem {ι : Type*} {s : Finset ι} {j : ι} (h : j ∉ s) (z : ℝ) :
    aF s j z = 0 := by
  unfold aF; simp [h]

private theorem aF'_of_mem {ι : Type*} {s : Finset ι} {j : ι} (h : j ∈ s) (z : ℝ) :
    aF' s j z = 1 := by
  unfold aF'; simp [h]

private theorem aF'_of_notMem {ι : Type*} {s : Finset ι} {j : ι} (h : j ∉ s) (z : ℝ) :
    aF' s j z = 0 := by
  unfold aF'; simp [h]

private theorem hasDerivAt_aF {ι : Type*} (s : Finset ι) (j : ι) (z : ℝ) :
    HasDerivAt (aF s j) (aF' s j z) z := by
  by_cases h : j ∈ s
  · have e : aF s j = id := funext fun y => aF_of_mem h y
    rw [e, aF'_of_mem h]
    exact hasDerivAt_id z
  · have e : aF s j = fun _ => 0 := funext fun y => aF_of_notMem h y
    rw [e, aF'_of_notMem h]
    exact hasDerivAt_const z 0

private theorem aF_mul {ι : Type*} (s : Finset ι) (j : ι) (c z : ℝ) :
    aF s j (c * z) = c * aF s j z := by
  by_cases h : j ∈ s
  · rw [aF_of_mem h, aF_of_mem h]
  · rw [aF_of_notMem h, aF_of_notMem h, mul_zero]

private theorem abs_aF_le {ι : Type*} (s : Finset ι) (j : ι) (z : ℝ) : |aF s j z| ≤ |z| := by
  by_cases h : j ∈ s
  · rw [aF_of_mem h]
  · rw [aF_of_notMem h, abs_zero]; exact abs_nonneg z

private theorem abs_aF'_le {ι : Type*} (s : Finset ι) (j : ι) (z : ℝ) : |aF' s j z| ≤ 1 := by
  by_cases h : j ∈ s
  · rw [aF'_of_mem h, abs_one]
  · rw [aF'_of_notMem h, abs_zero]; exact zero_le_one

/-- The fixed map of a frozen block is `qa` with the frozen gate values. -/
private theorem frozen_f_eq {T d : Type*} {L : ℕ} {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]
    (A : ∀ ℓ, Finset (hid ℓ)) (ℓ : Fin L) (P : Matrix T (hid ℓ ⊕ hid ℓ) ℝ) :
    (Arch.frozen (T := T) (d := d) A).f ℓ P = qa (aF (A ℓ)) P := by
  ext τ j
  simp only [qa, Matrix.of_apply]
  by_cases h : j ∈ A ℓ
  · rw [aF_of_mem h]
    exact Set.indicator_of_mem (Finset.mem_coe.2 h) _
  · rw [aF_of_notMem h, zero_mul]
    exact Set.indicator_of_notMem (fun h' => h (Finset.mem_coe.1 h')) _

/-! ### The gate far from zero -/

section Gate

/-- For `2 ≤ y ≤ z`: `|σ(z) − z| ≤ z e^{−y^p/p}` and `|σ'(z) − 1| ≤ 4 z² e^{−y^p/p}`. -/
private theorem gate_pos_bound (hg : GateFar σ σ' p) {y z : ℝ} (hy : 2 ≤ y) (hyz : y ≤ z) :
    |σ z - z| ≤ z * Real.exp (-(y ^ p / p)) ∧
      |σ' z - 1| ≤ 4 * z ^ 2 * Real.exp (-(y ^ p / p)) := by
  obtain ⟨h1, h2, h3⟩ := hg.gap z (hy.trans hyz)
  have hp : (0 : ℝ) < p := by exact_mod_cast hg.one_le
  have hz0 : 0 ≤ z := by linarith
  -- `y ↦ e^{−y^p/p}` is decreasing
  have he : Real.exp (-(z ^ p / p)) ≤ Real.exp (-(y ^ p / p)) :=
    Real.exp_le_exp.2 (neg_le_neg (div_le_div_of_nonneg_right
      (pow_le_pow_left₀ (by linarith) hyz p) hp.le))
  have hδ : 0 ≤ z - σ z := le_trans (by positivity) h1
  constructor
  · rw [abs_sub_comm, abs_of_nonneg hδ]
    exact h2.trans (mul_le_mul_of_nonneg_left he hz0)
  · rw [abs_sub_comm]
    calc |1 - σ' z| ≤ 4 * z * (z - σ z) := h3
      _ ≤ 4 * z * (z * Real.exp (-(y ^ p / p))) :=
          mul_le_mul_of_nonneg_left (h2.trans (mul_le_mul_of_nonneg_left he hz0)) (by positivity)
      _ = 4 * z ^ 2 * Real.exp (-(y ^ p / p)) := by ring

/-- For `2 ≤ y ≤ −z`: `|σ(z)| ≤ −z e^{−y^p/p}` and `|σ'(z)| ≤ 4 z² e^{−y^p/p}`, by (24). -/
private theorem gate_neg_bound (hg : GateFar σ σ' p) {y z : ℝ} (hy : 2 ≤ y) (hyz : y ≤ -z) :
    |σ z| ≤ -z * Real.exp (-(y ^ p / p)) ∧ |σ' z| ≤ 4 * z ^ 2 * Real.exp (-(y ^ p / p)) := by
  obtain ⟨h1, h2⟩ := gate_pos_bound hg hy hyz
  obtain ⟨n1, n2⟩ := hg.neg (-z)
  rw [neg_neg] at n1 n2
  rw [n1, n2, abs_neg, abs_sub_comm, abs_sub_comm 1, ← neg_sq z]
  exact ⟨h1, h2⟩

/-- The gate against the frozen gate, for a unit whose pre-activation has the sign of the unit
(`z ≥ y` if it is active, `z ≤ −y` otherwise), `y ≥ 2`. -/
private theorem gate_aF_bound {ι : Type*} (hg : GateFar σ σ' p) (s : Finset ι) (j : ι)
    {y z : ℝ} (hy : 2 ≤ y) (hpos : j ∈ s → y ≤ z) (hneg : j ∉ s → y ≤ -z) :
    |σ z - aF s j z| ≤ |z| * Real.exp (-(y ^ p / p)) ∧
      |σ' z - aF' s j z| ≤ 4 * |z| ^ 2 * Real.exp (-(y ^ p / p)) := by
  rw [sq_abs]
  by_cases hj : j ∈ s
  · rw [aF_of_mem hj, aF'_of_mem hj]
    have hz := hpos hj
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ z)]
    exact gate_pos_bound hg hy hz
  · rw [aF_of_notMem hj, aF'_of_notMem hj, sub_zero, sub_zero]
    have hz := hneg hj
    rw [abs_of_nonpos (by linarith : z ≤ 0)]
    exact gate_neg_bound hg hy hz

end Gate
/-! ### One block far out in its cone -/

section Block

/-- The hidden units of a gated block against those of the frozen block, from bounds on the
entries: the pre-activations `P` (at most `Z`), the direction `Pd` (at most `D`) and the gates
(`εσ`, `εσ'`). -/
private theorem block_pointwise {m ι : Type*} [Fintype m] [Fintype ι] (s : Finset ι)
    (P Pd : Matrix m (ι ⊕ ι) ℝ) {Z D εσ εσ' : ℝ} (hZ : 0 ≤ Z) (hD : 0 ≤ D) (hε : 0 ≤ εσ)
    (hε' : 0 ≤ εσ') (hP : ∀ τ r, |P τ r| ≤ Z) (hPd : ∀ τ r, |Pd τ r| ≤ D)
    (hσ : ∀ τ j, |σ (P τ (Sum.inl j)) - aF s j (P τ (Sum.inl j))| ≤ εσ)
    (hσ' : ∀ τ j, |σ' (P τ (Sum.inl j)) - aF' s j (P τ (Sum.inl j))| ≤ εσ') :
    ‖qa (fun _ => σ) P - qa (aF s) P‖ ≤ εσ * Z ∧ ‖qa (aF s) P‖ ≤ Z * Z ∧
      ‖dqa (fun _ => σ) (fun _ => σ') P Pd - dqa (aF s) (aF' s) P Pd‖ ≤ εσ' * D * Z + εσ * D ∧
      ‖dqa (aF s) (aF' s) P Pd‖ ≤ 1 * D * Z + Z * D := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [qa_sub]
    exact norm_qa_le hε hZ hσ fun τ j => hP τ _
  · exact norm_qa_le hZ hZ (fun τ j => (abs_aF_le s j _).trans (hP τ _)) fun τ j => hP τ _
  · rw [dqa_sub]
    exact norm_dqa_le hε hε' hD hD hZ hσ hσ' (fun τ j => hPd τ _) (fun τ j => hPd τ _)
      fun τ j => hP τ _
  · exact norm_dqa_le hZ zero_le_one hD hD hZ (fun τ j => (abs_aF_le s j _).trans (hP τ _))
      (fun τ j => abs_aF'_le s j _) (fun τ j => hPd τ _) (fun τ j => hPd τ _) fun τ j => hP τ _

/-- **The block far out in its cone** (step 2 of the proof). At `h = t (H + U)`, with the gates
of `H` of the signs of the active set `s` and at least `2μ` away from zero, and `‖U‖ ≤ ϱ` small:
the gated block minus the frozen block, and the same for their derivatives along `v` (`‖v‖ ≤ 1`)
and along the direction `(ηW, ηV)` of the weights, are exponentially small in `t`, and the
derivatives of the gated block are polynomially bounded. -/
private theorem block_bounds {m ι n : Type*} [Fintype m] [Fintype ι] [Fintype n]
    (hg : GateFar σ σ' p) (s : Finset ι) (W ηW : Matrix n (ι ⊕ ι) ℝ) (V ηV : Matrix ι n ℝ)
    (H : Matrix m n ℝ) {μ : ℝ} (hμ : 0 < μ)
    (hpos : ∀ τ, ∀ j ∈ s, 2 * μ ≤ (H * W) τ (Sum.inl j))
    (hneg : ∀ τ, ∀ j ∉ s, (H * W) τ (Sum.inl j) ≤ -(2 * μ))
    {ϱ : ℝ} (hϱ0 : 0 ≤ ϱ) (hϱ : Fintype.card n * ϱ * ‖W‖ ≤ μ)
    (S : Set (Matrix m n ℝ × Matrix m n ℝ)) (hS : ∀ i ∈ S, ‖i.1‖ ≤ ϱ ∧ ‖i.2‖ ≤ 1) :
    ExpSmall p S (fun t i => ‖qa (fun _ => σ) ((t • (H + i.1)) * W) * V
        - qa (aF s) ((t • (H + i.1)) * W) * V‖) ∧
    PolyB S (fun t i => ‖dqa (fun _ => σ) (fun _ => σ') ((t • (H + i.1)) * W) (i.2 * W) * V‖) ∧
    ExpSmall p S (fun t i => ‖dqa (fun _ => σ) (fun _ => σ') ((t • (H + i.1)) * W) (i.2 * W) * V
        - dqa (aF s) (aF' s) ((t • (H + i.1)) * W) (i.2 * W) * V‖) ∧
    PolyB S (fun t i => ‖dqa (fun _ => σ) (fun _ => σ') ((t • (H + i.1)) * W)
        ((t • (H + i.1)) * ηW) * V + qa (fun _ => σ) ((t • (H + i.1)) * W) * ηV‖) ∧
    ExpSmall p S (fun t i => ‖(dqa (fun _ => σ) (fun _ => σ') ((t • (H + i.1)) * W)
        ((t • (H + i.1)) * ηW) * V + qa (fun _ => σ) ((t • (H + i.1)) * W) * ηV)
        - (dqa (aF s) (aF' s) ((t • (H + i.1)) * W) ((t • (H + i.1)) * ηW) * V
          + qa (aF s) ((t • (H + i.1)) * W) * ηV)‖) := by
  have hp : (0 : ℝ) < p := by exact_mod_cast hg.one_le
  -- the rate `a = μ^p / p`, and the bounds `R₀, R₁, R₂` of the entries
  obtain ⟨a, ha_def⟩ : ∃ a : ℝ, a = μ ^ p / p := ⟨_, rfl⟩
  have ha : 0 < a := by rw [ha_def]; positivity
  obtain ⟨R₀, hR₀⟩ : ∃ R₀ : ℝ, R₀ = Fintype.card n * (‖H‖ + ϱ) * ‖W‖ := ⟨_, rfl⟩
  obtain ⟨R₁, hR₁⟩ : ∃ R₁ : ℝ, R₁ = Fintype.card n * ‖W‖ := ⟨_, rfl⟩
  obtain ⟨R₂, hR₂⟩ : ∃ R₂ : ℝ, R₂ = Fintype.card n * (‖H‖ + ϱ) * ‖ηW‖ := ⟨_, rfl⟩
  have hR₀0 : 0 ≤ R₀ := by rw [hR₀]; positivity
  have hR₁0 : 0 ≤ R₁ := by rw [hR₁]; positivity
  have hR₂0 : 0 ≤ R₂ := by rw [hR₂]; positivity
  -- the entries, for `t ≥ max 1 (2/μ)` and `i ∈ S`; step 1 (the gates)
  have key : ∀ t : ℝ, max 1 (2 / μ) ≤ t → ∀ i ∈ S,
      (∀ τ r, |((t • (H + i.1)) * W) τ r| ≤ t * R₀) ∧ (∀ τ r, |(i.2 * W) τ r| ≤ R₁) ∧
      (∀ τ r, |((t • (H + i.1)) * ηW) τ r| ≤ t * R₂) ∧
      (∀ τ j, |σ (((t • (H + i.1)) * W) τ (Sum.inl j))
          - aF s j (((t • (H + i.1)) * W) τ (Sum.inl j))| ≤ t * R₀ * Real.exp (-(a * t ^ p))) ∧
      (∀ τ j, |σ' (((t • (H + i.1)) * W) τ (Sum.inl j))
          - aF' s j (((t • (H + i.1)) * W) τ (Sum.inl j))|
        ≤ 4 * (t * R₀) ^ 2 * Real.exp (-(a * t ^ p))) := by
    intro t ht i hi
    have ht1 : 1 ≤ t := (le_max_left _ _).trans ht
    have ht0 : 0 ≤ t := zero_le_one.trans ht1
    have htμ : 2 ≤ t * μ := (div_le_iff₀ hμ).1 ((le_max_right _ _).trans ht)
    obtain ⟨hU, hv⟩ := hS i hi
    -- entries of `t (H + U) M`
    have hent : ∀ (M : Matrix n (ι ⊕ ι) ℝ) τ r,
        |((t • (H + i.1)) * M) τ r| ≤ t * (Fintype.card n * (‖H‖ + ϱ) * ‖M‖) := by
      intro M τ r
      rw [Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg ht0]
      refine mul_le_mul_of_nonneg_left ((abs_mul_apply_le _ _ _ _).trans ?_) ht0
      have : ‖H + i.1‖ ≤ ‖H‖ + ϱ := (norm_add_le _ _).trans (by linarith)
      gcongr
    have hP : ∀ τ r, |((t • (H + i.1)) * W) τ r| ≤ t * R₀ := by rw [hR₀]; exact hent W
    -- the rate: `e^{−(tμ)^p/p} = e^{−a t^p}`
    have hrate : Real.exp (-((t * μ) ^ p / p)) = Real.exp (-(a * t ^ p)) := by
      rw [ha_def, mul_pow]; ring_nf
    refine ⟨hP, fun τ r => ?_, by rw [hR₂]; exact hent ηW, fun τ j => ?_, fun τ j => ?_⟩
    · calc |(i.2 * W) τ r| ≤ Fintype.card n * ‖i.2‖ * ‖W‖ := abs_mul_apply_le _ _ _ _
        _ ≤ Fintype.card n * 1 * ‖W‖ := by gcongr
        _ = R₁ := by rw [hR₁, mul_one]
    all_goals
      -- the pre-activation `z` of the gate has the sign of the unit, `|z| ≥ t μ`
      have hz : ((t • (H + i.1)) * W) τ (Sum.inl j)
          = t * ((H * W) τ (Sum.inl j) + (i.1 * W) τ (Sum.inl j)) := by
        rw [Matrix.smul_mul, Matrix.add_mul, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
      have hUW : |(i.1 * W) τ (Sum.inl j)| ≤ μ := by
        refine (abs_mul_apply_le _ _ _ _).trans (le_trans ?_ hϱ)
        gcongr
      have hUW' := abs_le.1 hUW
      have hpos' : j ∈ s → t * μ ≤ ((t • (H + i.1)) * W) τ (Sum.inl j) := fun hj => by
        rw [hz]
        have := hpos τ j hj
        exact mul_le_mul_of_nonneg_left (by linarith) ht0
      have hneg' : j ∉ s → t * μ ≤ -((t • (H + i.1)) * W) τ (Sum.inl j) := fun hj => by
        rw [hz, ← mul_neg]
        have := hneg τ j hj
        exact mul_le_mul_of_nonneg_left (by linarith) ht0
      obtain ⟨g1, g2⟩ := gate_aF_bound hg s j htμ hpos' hneg'
      rw [hrate] at g1 g2
    · exact g1.trans (mul_le_mul_of_nonneg_right (hP τ _) (Real.exp_pos _).le)
    · refine g2.trans (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)
      gcongr
      exact hP τ _
  -- step 2: the five bounds
  have hx : ExpSmall p S (fun t i => ‖qa (fun _ => σ) ((t • (H + i.1)) * W) * V
      - qa (aF s) ((t • (H + i.1)) * W) * V‖) := by
    refine (expSmall_monomial (S := S) ha (Fintype.card ι * R₀ ^ 2 * ‖V‖) 2).mono ?_
    filter_upwards [eventually_ge_atTop (max 1 (2 / μ))] with t ht i hi
    have ht0 : 0 ≤ t := zero_le_one.trans ((le_max_left _ _).trans ht)
    obtain ⟨hP, hv, -, g1, g2⟩ := key t ht i hi
    obtain ⟨b1, -, -, -⟩ := block_pointwise s _ (i.2 * W) (by positivity) hR₁0 (by positivity)
      (by positivity) hP hv g1 g2
    rw [← Matrix.sub_mul]
    exact (norm_mul_le' _ _).trans (le_trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left b1 (Nat.cast_nonneg _)) (norm_nonneg _)) (le_of_eq (by ring)))
  have hww : ExpSmall p S (fun t i =>
      ‖dqa (fun _ => σ) (fun _ => σ') ((t • (H + i.1)) * W) (i.2 * W) * V
        - dqa (aF s) (aF' s) ((t • (H + i.1)) * W) (i.2 * W) * V‖) := by
    refine ((expSmall_monomial (S := S) ha (Fintype.card ι * (4 * R₀ ^ 3 * R₁) * ‖V‖) 3).add
      (expSmall_monomial (S := S) ha (Fintype.card ι * (R₀ * R₁) * ‖V‖) 1)).mono ?_
    filter_upwards [eventually_ge_atTop (max 1 (2 / μ))] with t ht i hi
    have ht0 : 0 ≤ t := zero_le_one.trans ((le_max_left _ _).trans ht)
    obtain ⟨hP, hv, -, g1, g2⟩ := key t ht i hi
    obtain ⟨-, -, b3, -⟩ := block_pointwise s _ (i.2 * W) (by positivity) hR₁0 (by positivity)
      (by positivity) hP hv g1 g2
    rw [← Matrix.sub_mul]
    exact (norm_mul_le' _ _).trans (le_trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left b3 (Nat.cast_nonneg _)) (norm_nonneg _)) (le_of_eq (by ring)))
  have hw0 : PolyB S (fun t i =>
      ‖dqa (aF s) (aF' s) ((t • (H + i.1)) * W) (i.2 * W) * V‖) := by
    refine (polyB_monomial (S := S) (Fintype.card ι * (2 * R₀ * R₁) * ‖V‖) 1).mono ?_
    filter_upwards [eventually_ge_atTop (max 1 (2 / μ))] with t ht i hi
    have ht0 : 0 ≤ t := zero_le_one.trans ((le_max_left _ _).trans ht)
    obtain ⟨hP, hv, -, g1, g2⟩ := key t ht i hi
    obtain ⟨-, -, -, b4⟩ := block_pointwise s _ (i.2 * W) (by positivity) hR₁0 (by positivity)
      (by positivity) hP hv g1 g2
    exact (norm_mul_le' _ _).trans (le_trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left b4 (Nat.cast_nonneg _)) (norm_nonneg _)) (le_of_eq (by ring)))
  -- the direction of the weights: `q − q° = (dqa − dqa°) V + (qa − qa°) ηV`
  have hsplit : ∀ A₁ A₂ B₁ B₂ : Matrix m ι ℝ,
      (A₁ * V + B₁ * ηV) - (A₂ * V + B₂ * ηV) = (A₁ - A₂) * V + (B₁ - B₂) * ηV := by
    intro A₁ A₂ B₁ B₂
    rw [Matrix.sub_mul, Matrix.sub_mul]
    abel
  have hqq : ExpSmall p S (fun t i => ‖(dqa (fun _ => σ) (fun _ => σ') ((t • (H + i.1)) * W)
        ((t • (H + i.1)) * ηW) * V + qa (fun _ => σ) ((t • (H + i.1)) * W) * ηV)
        - (dqa (aF s) (aF' s) ((t • (H + i.1)) * W) ((t • (H + i.1)) * ηW) * V
          + qa (aF s) ((t • (H + i.1)) * W) * ηV)‖) := by
    refine ((expSmall_monomial (S := S) ha (Fintype.card ι * (4 * R₀ ^ 3 * R₂) * ‖V‖) 4).add
      (expSmall_monomial (S := S) ha
        (Fintype.card ι * (R₀ * R₂) * ‖V‖ + Fintype.card ι * R₀ ^ 2 * ‖ηV‖) 2)).mono ?_
    filter_upwards [eventually_ge_atTop (max 1 (2 / μ))] with t ht i hi
    have ht0 : 0 ≤ t := zero_le_one.trans ((le_max_left _ _).trans ht)
    obtain ⟨hP, -, hθ, g1, g2⟩ := key t ht i hi
    obtain ⟨b1, -, b3, -⟩ := block_pointwise s _ _ (by positivity) (by positivity)
      (by positivity) (by positivity) hP hθ g1 g2
    rw [hsplit]
    refine (norm_add_le _ _).trans (le_trans (add_le_add
      ((norm_mul_le' _ _).trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left b3 (Nat.cast_nonneg _)) (norm_nonneg _)))
      ((norm_mul_le' _ _).trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left b1 (Nat.cast_nonneg _)) (norm_nonneg _)))) (le_of_eq ?_))
    ring
  have hq0 : PolyB S (fun t i => ‖dqa (aF s) (aF' s) ((t • (H + i.1)) * W)
        ((t • (H + i.1)) * ηW) * V + qa (aF s) ((t • (H + i.1)) * W) * ηV‖) := by
    refine (polyB_monomial (S := S)
      (Fintype.card ι * (2 * R₀ * R₂) * ‖V‖ + Fintype.card ι * R₀ ^ 2 * ‖ηV‖) 2).mono ?_
    filter_upwards [eventually_ge_atTop (max 1 (2 / μ))] with t ht i hi
    have ht0 : 0 ≤ t := zero_le_one.trans ((le_max_left _ _).trans ht)
    obtain ⟨hP, -, hθ, g1, g2⟩ := key t ht i hi
    obtain ⟨-, b2, -, b4⟩ := block_pointwise s _ _ (by positivity) (by positivity)
      (by positivity) (by positivity) hP hθ g1 g2
    refine (norm_add_le _ _).trans (le_trans (add_le_add
      ((norm_mul_le' _ _).trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left b4 (Nat.cast_nonneg _)) (norm_nonneg _)))
      ((norm_mul_le' _ _).trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left b2 (Nat.cast_nonneg _)) (norm_nonneg _)))) (le_of_eq ?_))
    ring
  exact ⟨hx, (hw0.add hww.polyB).mono (Eventually.of_forall fun t i _ => norm_le_insert' _ _),
    hww, (hq0.add hqq.polyB).mono (Eventually.of_forall fun t i _ => norm_le_insert' _ _), hqq⟩

end Block


/-! ### A `C¹` map is Lipschitz on a closed ball -/

/-- A `C¹` map on a finite-dimensional space is Lipschitz on every closed ball (its derivative is
bounded there, and the ball is convex). -/
private theorem exists_lipschitz_closedBall {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} (hf : ContDiff ℝ 1 f) (x₀ : E) (r : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Metric.closedBall x₀ r, ∀ y ∈ Metric.closedBall x₀ r,
      ‖f x - f y‖ ≤ C * ‖x - y‖ := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall x₀ r).exists_bound_of_continuousOn
    (hf.continuous_fderiv one_ne_zero).continuousOn
  refine ⟨max C 0, le_max_right _ _, fun x hx y hy => ?_⟩
  exact (convex_closedBall x₀ r).norm_image_sub_le_of_norm_fderiv_le
    (fun z _ => (hf.differentiable one_ne_zero) z) (fun z hz => (hC z hz).trans (le_max_left _ _))
    hy hx

/-- The derivative of a `C²` map is bounded and Lipschitz on every closed ball, applied to `v`. -/
private theorem exists_fderiv_lipschitz_closedBall {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} (hf : ContDiff ℝ 2 f) (x₀ : E) (r : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ (∀ x ∈ Metric.closedBall x₀ r, ∀ v, ‖fderiv ℝ f x v‖ ≤ C * ‖v‖) ∧
      ∀ x ∈ Metric.closedBall x₀ r, ∀ y ∈ Metric.closedBall x₀ r, ∀ v,
        ‖fderiv ℝ f x v - fderiv ℝ f y v‖ ≤ C * ‖x - y‖ * ‖v‖ := by
  have hf1 : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  obtain ⟨C₁, hC₁0, hC₁⟩ := exists_lipschitz_closedBall hf1 x₀ r
  obtain ⟨C₂, hC₂⟩ := (isCompact_closedBall x₀ r).exists_bound_of_continuousOn
    (hf.continuous_fderiv (by norm_num)).continuousOn
  refine ⟨max C₁ C₂, le_max_of_le_left hC₁0, fun x hx v => ?_, fun x hx y hy v => ?_⟩
  · exact ((fderiv ℝ f x).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right ((hC₂ x hx).trans (le_max_right _ _)) (norm_nonneg v))
  · rw [← _root_.sub_apply]
    exact ((fderiv ℝ f x - fderiv ℝ f y).le_opNorm v).trans (mul_le_mul_of_nonneg_right
      ((hC₁ x hx y hy).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)))
      (norm_nonneg v))

/-! ### The chain rule through one block, for any architecture without normalization -/

/-- Helper: for `Φ` differentiable at `(x, y)`, the derivatives of its two partial maps, along `b`
and `a`, add up to its derivative along `(a, b)` (as in `Depth/StepTanh.lean`). -/
private theorem fderiv_partial_addF {E₁ E₂ F : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {Φ : E₁ → E₂ → F} {x : E₁} {y : E₂}
    (hΦ : DifferentiableAt ℝ (fun p : E₁ × E₂ => Φ p.1 p.2) (x, y)) (a : E₁) (b : E₂) :
    fderiv ℝ (fun y' => Φ x y') y b + fderiv ℝ (fun x' => Φ x' y) x a
      = fderiv ℝ (fun p : E₁ × E₂ => Φ p.1 p.2) (x, y) (a, b) := by
  have h1 : HasFDerivAt (fun x' => Φ x' y)
      ((fderiv ℝ (fun p : E₁ × E₂ => Φ p.1 p.2) (x, y)).comp
        (ContinuousLinearMap.inl ℝ E₁ E₂)) x := by
    have hc := hΦ.hasFDerivAt.comp x (hasFDerivAt_prodMk_left (𝕜 := ℝ) x y)
    exact hc
  have h2 : HasFDerivAt (fun y' => Φ x y')
      ((fderiv ℝ (fun p : E₁ × E₂ => Φ p.1 p.2) (x, y)).comp
        (ContinuousLinearMap.inr ℝ E₁ E₂)) y := by
    have hc := hΦ.hasFDerivAt.comp y (hasFDerivAt_prodMk_right (𝕜 := ℝ) x y)
    exact hc
  rw [h1.fderiv, h2.fderiv, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.inl_apply, ContinuousLinearMap.inr_apply, ← map_add, Prod.mk_add_mk,
    zero_add, add_zero]

/-- The chain rule for `𝓑_{>ℓ-1} = 𝓑_{>ℓ} ∘ g_ℓ` along `v`, with the derivative `w` of the block
along the line `h + s v`. -/
private theorem fderiv_suffix_castSucc_line (A : Arch T d L) (hχ : A.χ = id)
    (hf : ∀ ℓ, Differentiable ℝ (A.f ℓ)) (θ : Params A dIn dOut) (ℓ : Fin L)
    (h v w : Matrix T d ℝ)
    (hw : HasDerivAt (fun s : ℝ => A.f ℓ ((h + s • v) * θ.read ℓ) * θ.write ℓ) w 0) :
    fderiv ℝ (fun h' : Matrix T d ℝ => suffix A 0 θ ℓ.castSucc h') h v
      = fderiv ℝ (fun h' : Matrix T d ℝ => suffix A 0 θ ℓ.succ h')
          (A.f ℓ (h * θ.read ℓ) * θ.write ℓ) w := by
  have hB := differentiable_suffix A θ hχ hf ℓ.succ
  have hB' := differentiable_suffix A θ hχ hf ℓ.castSucc
  have e1 : HasDerivAt (fun s : ℝ => suffix A 0 θ ℓ.castSucc (h + s • v))
      (fderiv ℝ (fun h' : Matrix T d ℝ => suffix A 0 θ ℓ.castSucc h') h v) 0 := by
    have hc := (hB' h).hasFDerivAt.comp_hasDerivAt_of_eq 0 (hasDerivAt_lineF h v) (by simp)
    exact hc
  have e2 : HasDerivAt (fun s : ℝ => suffix A 0 θ ℓ.castSucc (h + s • v))
      (fderiv ℝ (fun h' : Matrix T d ℝ => suffix A 0 θ ℓ.succ h')
        (A.f ℓ (h * θ.read ℓ) * θ.write ℓ) w) 0 := by
    have hc := (hB (A.f ℓ (h * θ.read ℓ) * θ.write ℓ)).hasFDerivAt.comp_hasDerivAt_of_eq 0 hw
      (by simp)
    have hfun : (fun s : ℝ => suffix A 0 θ ℓ.castSucc (h + s • v))
        = (fun h' : Matrix T d ℝ => suffix A 0 θ ℓ.succ h') ∘
          fun s : ℝ => A.f ℓ ((h + s • v) * θ.read ℓ) * θ.write ℓ := by
      funext s
      rw [suffix_castSucc_eq_comp A θ hχ ℓ]
      rfl
    rw [hfun]
    exact hc
  exact e1.unique e2

/-- The chain rule for `θ ↦ 𝓑_{>ℓ-1}(h) = 𝓑_{>ℓ}(g_ℓ(h))` along `η`, with the derivative `w` of
the block along the line of weights `θ + s η`. -/
private theorem fderiv_params_suffix_castSucc_line (A : Arch T d L) (hχ : A.χ = id)
    (hf : ∀ ℓ, Differentiable ℝ (A.f ℓ)) (θ η : Params A dIn dOut) (ℓ : Fin L)
    (h w : Matrix T d ℝ)
    (hw : HasDerivAt (fun s : ℝ =>
      A.f ℓ (h * (θ.read ℓ + s • η.read ℓ)) * (θ.write ℓ + s • η.write ℓ)) w 0) :
    fderiv ℝ (fun θ' : Params A dIn dOut => suffix A 0 θ' ℓ.castSucc h) θ η
      = fderiv ℝ (fun θ' : Params A dIn dOut =>
          suffix A 0 θ' ℓ.succ (A.f ℓ (h * θ.read ℓ) * θ.write ℓ)) θ η
        + fderiv ℝ (fun h' : Matrix T d ℝ => suffix A 0 θ ℓ.succ h')
          (A.f ℓ (h * θ.read ℓ) * θ.write ℓ) w := by
  have hΦ := differentiable_suffix_prod A (dIn := dIn) (dOut := dOut) hχ hf ℓ.succ
  have hP := differentiable_params_suffix A (dIn := dIn) (dOut := dOut) hχ hf ℓ.castSucc h
  have e1 : HasDerivAt (fun s : ℝ => suffix A 0 (θ + s • η) ℓ.castSucc h)
      (fderiv ℝ (fun θ' : Params A dIn dOut => suffix A 0 θ' ℓ.castSucc h) θ η) 0 := by
    have hc := (hP θ).hasFDerivAt.comp_hasDerivAt_of_eq 0 (hasDerivAt_lineF θ η) (by simp)
    exact hc
  have e2 : HasDerivAt (fun s : ℝ => suffix A 0 (θ + s • η) ℓ.castSucc h)
      (fderiv ℝ (fun p : Params A dIn dOut × Matrix T d ℝ => suffix A 0 p.1 ℓ.succ p.2)
        (θ, A.f ℓ (h * θ.read ℓ) * θ.write ℓ) (η, w)) 0 := by
    have hc := (hΦ (θ, A.f ℓ (h * θ.read ℓ) * θ.write ℓ)).hasFDerivAt.comp_hasDerivAt_of_eq 0
      ((hasDerivAt_lineF θ η).prodMk hw) (by simp)
    have hfun : (fun s : ℝ => suffix A 0 (θ + s • η) ℓ.castSucc h)
        = (fun p : Params A dIn dOut × Matrix T d ℝ => suffix A 0 p.1 ℓ.succ p.2) ∘
          fun s : ℝ => (θ + s • η,
            A.f ℓ (h * (θ.read ℓ + s • η.read ℓ)) * (θ.write ℓ + s • η.write ℓ)) := by
      funext s
      simp only [Function.comp_apply, suffix_castSucc, hχ, id, Pi.zero_apply, Matrix.mul_zero,
        zero_add, Params.add_read, Params.smul_read, Params.add_write, Params.smul_write]
    rw [hfun]
    exact hc
  calc _ = fderiv ℝ (fun p : Params A dIn dOut × Matrix T d ℝ => suffix A 0 p.1 ℓ.succ p.2)
        (θ, A.f ℓ (h * θ.read ℓ) * θ.write ℓ) (η, w) := e1.unique e2
    _ = fderiv ℝ (fun h' : Matrix T d ℝ => suffix A 0 θ ℓ.succ h')
          (A.f ℓ (h * θ.read ℓ) * θ.write ℓ) w
        + fderiv ℝ (fun θ' : Params A dIn dOut =>
          suffix A 0 θ' ℓ.succ (A.f ℓ (h * θ.read ℓ) * θ.write ℓ)) θ η :=
      (fderiv_partial_addF (Φ := fun θ' h' => suffix A 0 θ' ℓ.succ h') (hΦ _) η w).symm
    _ = _ := add_comm _ _

/-! ### The two networks through block `ℓ` -/

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
private theorem toFrozen_read (A : ∀ ℓ, Finset (hid ℓ))
    (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) (ℓ : Fin L) :
    (θ.toFrozen A).read ℓ = θ.read ℓ := rfl

/-- The gated network through block `ℓ`: `𝓑_{>ℓ-1}(h) = 𝓑_{>ℓ}(qa σ (h W) V)`. -/
private theorem suffix_gated_castSucc (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (ℓ : Fin L) (h : Matrix T d ℝ) :
    suffix (Arch.gated σ id hid) 0 θ ℓ.castSucc h
      = suffix (Arch.gated σ id hid) 0 θ ℓ.succ (qa (fun _ => σ) (h * θ.read ℓ) * θ.write ℓ) := by
  rw [suffix_castSucc_eq_comp _ θ rfl ℓ]
  rfl

/-- The frozen network through block `ℓ`: `𝓑°_{>ℓ-1}(h) = 𝓑°_{>ℓ}(qa aF (h W) V)`. -/
private theorem suffix_frozen_castSucc (A : ∀ ℓ, Finset (hid ℓ))
    (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) (ℓ : Fin L) (h : Matrix T d ℝ) :
    suffix (Arch.frozen A) 0 (θ.toFrozen A) ℓ.castSucc h
      = suffix (Arch.frozen A) 0 (θ.toFrozen A) ℓ.succ
          (qa (aF (A ℓ)) (h * θ.read ℓ) * θ.write ℓ) := by
  rw [suffix_castSucc_eq_comp _ _ rfl ℓ, Function.comp_apply, frozen_f_eq]
  rfl

/-- The derivative of the gated network through block `ℓ`, along `v`. -/
private theorem fderiv_gated_castSucc (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) (ℓ : Fin L)
    (h v : Matrix T d ℝ) :
    fderiv ℝ (fun h' : Matrix T d ℝ => suffix (Arch.gated σ id hid) 0 θ ℓ.castSucc h') h v
      = fderiv ℝ (fun h' : Matrix T d ℝ => suffix (Arch.gated σ id hid) 0 θ ℓ.succ h')
          (qa (fun _ => σ) (h * θ.read ℓ) * θ.write ℓ)
          (dqa (fun _ => σ) (fun _ => σ') (h * θ.read ℓ) (v * θ.read ℓ) * θ.write ℓ) :=
  fderiv_suffix_castSucc_line _ rfl (differentiable_f_gated fun z => (hσ z).differentiableAt)
    θ ℓ h v _ (hasDerivAt_block_line (a := fun _ => σ) (fun _ z => hσ z) _ _ h v)

/-- The derivative of the frozen network through block `ℓ`, along `v`. -/
private theorem fderiv_frozen_castSucc (A : ∀ ℓ, Finset (hid ℓ))
    (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) (ℓ : Fin L)
    (h v : Matrix T d ℝ) :
    fderiv ℝ (fun h' : Matrix T d ℝ => suffix (Arch.frozen A) 0 (θ.toFrozen A) ℓ.castSucc h') h v
      = fderiv ℝ (fun h' : Matrix T d ℝ => suffix (Arch.frozen A) 0 (θ.toFrozen A) ℓ.succ h')
          (qa (aF (A ℓ)) (h * θ.read ℓ) * θ.write ℓ)
          (dqa (aF (A ℓ)) (aF' (A ℓ)) (h * θ.read ℓ) (v * θ.read ℓ) * θ.write ℓ) := by
  have hfF : ∀ ℓ, Differentiable ℝ ((Arch.frozen (T := T) (d := d) A).f ℓ) := fun ℓ =>
    differentiableOn_univ.1 (analyticOnNhd_f_frozen A ℓ).differentiableOn
  have hfe : (Arch.frozen (T := T) (d := d) A).f ℓ = qa (aF (A ℓ)) := funext (frozen_f_eq A ℓ)
  have c := fderiv_suffix_castSucc_line (Arch.frozen A) rfl hfF (θ.toFrozen A) ℓ h v
    (dqa (aF (A ℓ)) (aF' (A ℓ)) (h * θ.read ℓ) (v * θ.read ℓ) * θ.write ℓ) (by
      rw [hfe]
      exact hasDerivAt_block_line (hasDerivAt_aF (A ℓ)) (θ.read ℓ) (θ.write ℓ) h v)
  rw [hfe] at c
  exact c

/-- The derivative of the gated network through block `ℓ` in the weights, along `η`. -/
private theorem fderiv_params_gated_castSucc (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (θ η : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) (ℓ : Fin L)
    (h : Matrix T d ℝ) :
    fderiv ℝ (fun θ' : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut =>
        suffix (Arch.gated σ id hid) 0 θ' ℓ.castSucc h) θ η
      = fderiv ℝ (fun θ' : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut =>
          suffix (Arch.gated σ id hid) 0 θ' ℓ.succ (qa (fun _ => σ) (h * θ.read ℓ) * θ.write ℓ))
          θ η
        + fderiv ℝ (fun h' : Matrix T d ℝ => suffix (Arch.gated σ id hid) 0 θ ℓ.succ h')
          (qa (fun _ => σ) (h * θ.read ℓ) * θ.write ℓ)
          (dqa (fun _ => σ) (fun _ => σ') (h * θ.read ℓ) (h * η.read ℓ) * θ.write ℓ
            + qa (fun _ => σ) (h * θ.read ℓ) * η.write ℓ) :=
  fderiv_params_suffix_castSucc_line _ rfl
    (differentiable_f_gated fun z => (hσ z).differentiableAt) θ η ℓ h _
    (hasDerivAt_block_params (a := fun _ => σ) (fun _ z => hσ z) _ _ _ _ h)

/-- The derivative of the frozen network through block `ℓ` in the weights, along `η`. -/
private theorem fderiv_params_frozen_castSucc (A : ∀ ℓ, Finset (hid ℓ))
    (θ η : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) (ℓ : Fin L)
    (h : Matrix T d ℝ) :
    fderiv ℝ (fun θ' : Params (Arch.frozen (T := T) (d := d) A) dIn dOut =>
        suffix (Arch.frozen A) 0 θ' ℓ.castSucc h) (θ.toFrozen A) (η.toFrozen A)
      = fderiv ℝ (fun θ' : Params (Arch.frozen (T := T) (d := d) A) dIn dOut =>
          suffix (Arch.frozen A) 0 θ' ℓ.succ (qa (aF (A ℓ)) (h * θ.read ℓ) * θ.write ℓ))
          (θ.toFrozen A) (η.toFrozen A)
        + fderiv ℝ (fun h' : Matrix T d ℝ => suffix (Arch.frozen A) 0 (θ.toFrozen A) ℓ.succ h')
          (qa (aF (A ℓ)) (h * θ.read ℓ) * θ.write ℓ)
          (dqa (aF (A ℓ)) (aF' (A ℓ)) (h * θ.read ℓ) (h * η.read ℓ) * θ.write ℓ
            + qa (aF (A ℓ)) (h * θ.read ℓ) * η.write ℓ) := by
  have hfF : ∀ ℓ, Differentiable ℝ ((Arch.frozen (T := T) (d := d) A).f ℓ) := fun ℓ =>
    differentiableOn_univ.1 (analyticOnNhd_f_frozen A ℓ).differentiableOn
  have hfe : (Arch.frozen (T := T) (d := d) A).f ℓ = qa (aF (A ℓ)) := funext (frozen_f_eq A ℓ)
  have c := fderiv_params_suffix_castSucc_line (Arch.frozen A) rfl hfF (θ.toFrozen A)
    (η.toFrozen A) ℓ h (dqa (aF (A ℓ)) (aF' (A ℓ)) (h * θ.read ℓ) (h * η.read ℓ) * θ.write ℓ
      + qa (aF (A ℓ)) (h * θ.read ℓ) * η.write ℓ) (by
      rw [hfe]
      exact hasDerivAt_block_params (hasDerivAt_aF (A ℓ)) (θ.read ℓ) (η.read ℓ) (θ.write ℓ)
        (η.write ℓ) h)
  rw [hfe] at c
  exact c

/-! ### Step 4: the frozen network on the dilations of a ball -/

/-- **The frozen network is Lipschitz with polynomial growth** on the dilations `t² z` of a closed
ball (`t ≥ 1`), by its homogeneity of the degree `M = 2^{L−k}` and since it is real-analytic: its
value, its derivative in the hidden state, and its derivative in the weights along `η₀`. -/
private theorem frozen_lip (A : ∀ ℓ, Finset (hid ℓ))
    (θ₀ η₀ : Params (Arch.frozen (T := T) (d := d) A) dIn dOut) (k : Fin (L + 1))
    (H' : Matrix T d ℝ) (r : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 1 ≤ t →
      ∀ z₁ ∈ Metric.closedBall H' r, ∀ z₂ ∈ Metric.closedBall H' r,
      ‖suffix (Arch.frozen A) 0 θ₀ k (t ^ 2 • z₁) - suffix (Arch.frozen A) 0 θ₀ k (t ^ 2 • z₂)‖
          ≤ C * t ^ (2 * 2 ^ (L - (k : ℕ))) * ‖t ^ 2 • z₁ - t ^ 2 • z₂‖ ∧
      (∀ v, ‖fderiv ℝ (fun h' : Matrix T d ℝ => suffix (Arch.frozen A) 0 θ₀ k h') (t ^ 2 • z₁) v
          - fderiv ℝ (fun h' : Matrix T d ℝ => suffix (Arch.frozen A) 0 θ₀ k h') (t ^ 2 • z₂) v‖
          ≤ C * t ^ (2 * 2 ^ (L - (k : ℕ))) * ‖t ^ 2 • z₁ - t ^ 2 • z₂‖ * ‖v‖) ∧
      (∀ v, ‖fderiv ℝ (fun h' : Matrix T d ℝ => suffix (Arch.frozen A) 0 θ₀ k h')
          (t ^ 2 • z₂) v‖ ≤ C * t ^ (2 * 2 ^ (L - (k : ℕ))) * ‖v‖) ∧
      ‖fderiv ℝ (fun θ' : Params (Arch.frozen (T := T) (d := d) A) dIn dOut =>
            suffix (Arch.frozen A) 0 θ' k (t ^ 2 • z₁)) θ₀ η₀
          - fderiv ℝ (fun θ' : Params (Arch.frozen (T := T) (d := d) A) dIn dOut =>
            suffix (Arch.frozen A) 0 θ' k (t ^ 2 • z₂)) θ₀ η₀‖
          ≤ C * t ^ (2 * 2 ^ (L - (k : ℕ))) * ‖t ^ 2 • z₁ - t ^ 2 • z₂‖ := by
  have hfa : ∀ ℓ, AnalyticOnNhd ℝ ((Arch.frozen (T := T) (d := d) A).f ℓ) Set.univ :=
    analyticOnNhd_f_frozen A
  -- the value and the derivative in the hidden state, on the ball
  have hB : ContDiff ℝ 2 (fun h' : Matrix T d ℝ => suffix (Arch.frozen A) 0 θ₀ k h') :=
    (analyticOnNhd_suffix (Arch.frozen A) θ₀ rfl hfa k).contDiff
  obtain ⟨C₁, hC₁0, hC₁⟩ := exists_lipschitz_closedBall (hB.of_le (by norm_num)) H' r
  obtain ⟨C₂, hC₂0, hC₂b, hC₂⟩ := exists_fderiv_lipschitz_closedBall hB H' r
  -- the derivative in the weights along `η₀`, a `C¹` function of the hidden state
  have hP : ContDiff ℝ 1 (fun z : Matrix T d ℝ =>
      fderiv ℝ (fun θ' : Params (Arch.frozen (T := T) (d := d) A) dIn dOut =>
        suffix (Arch.frozen A) 0 θ' k z) θ₀ η₀) := by
    have hj : ContDiff ℝ 2 (fun p : Params (Arch.frozen (T := T) (d := d) A) dIn dOut ×
        Matrix T d ℝ => suffix (Arch.frozen A) 0 p.1 k p.2) :=
      (analyticOnNhd_suffix_prod (Arch.frozen A) rfl hfa k).contDiff
    have hsw : ContDiff ℝ 2 (fun q : Matrix T d ℝ ×
        Params (Arch.frozen (T := T) (d := d) A) dIn dOut => (q.2, q.1)) :=
      contDiff_snd.prodMk contDiff_fst
    have hc := hj.comp hsw
    have hj' : ContDiff ℝ 2 (Function.uncurry fun (z : Matrix T d ℝ)
        (θ' : Params (Arch.frozen (T := T) (d := d) A) dIn dOut) =>
          suffix (Arch.frozen A) 0 θ' k z) := hc
    exact (hj'.fderiv contDiff_const (by norm_num)).clm_apply contDiff_const
  obtain ⟨C₃, hC₃0, hC₃⟩ := exists_lipschitz_closedBall hP H' r
  refine ⟨C₁ + C₂ + C₃, by positivity, fun t ht z₁ hz₁ z₂ hz₂ => ?_⟩
  -- homogeneity: `t^2` to the powers `M` and `M - 1`, `M = 2^{L-k}`
  have hc0 : 0 ≤ t ^ 2 := by positivity
  have hc : t ^ 2 ≠ 0 := by positivity
  have hnum : ∀ j : ℕ, j ≤ 2 ^ (L - (k : ℕ)) → ∀ C' Y Y' : ℝ, 0 ≤ C' → C' ≤ C₁ + C₂ + C₃ →
      0 ≤ Y → Y ≤ Y' →
        (t ^ 2) ^ j * (C' * Y) ≤ (C₁ + C₂ + C₃) * t ^ (2 * 2 ^ (L - (k : ℕ))) * Y' := by
    intro j hj C' Y Y' hC' hC'C hY hYY'
    have h1 : (t ^ 2) ^ j ≤ t ^ (2 * 2 ^ (L - (k : ℕ))) := by
      rw [pow_mul]
      exact pow_le_pow_right₀ (by nlinarith) hj
    calc (t ^ 2) ^ j * (C' * Y) ≤ t ^ (2 * 2 ^ (L - (k : ℕ))) * ((C₁ + C₂ + C₃) * Y') :=
          mul_le_mul h1 (mul_le_mul hC'C hYY' hY (by positivity)) (by positivity) (by positivity)
      _ = _ := by ring
  have hsub : ‖t ^ 2 • z₁ - t ^ 2 • z₂‖ = t ^ 2 * ‖z₁ - z₂‖ := by
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc0]
  have hle : ‖z₁ - z₂‖ ≤ ‖t ^ 2 • z₁ - t ^ 2 • z₂‖ := by
    rw [hsub]
    exact le_mul_of_one_le_left (norm_nonneg _) (by nlinarith)
  refine ⟨?_, fun v => ?_, fun v => ?_, ?_⟩
  · rw [suffix_frozen_smul, suffix_frozen_smul, ← smul_sub, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg hc0 _)]
    exact hnum _ le_rfl C₁ _ _ hC₁0 (by linarith) (norm_nonneg _) hle |>.trans' (by
      gcongr; exact hC₁ z₁ hz₁ z₂ hz₂)
  · rw [fderiv_suffix_frozen_smul A θ₀ k hc, fderiv_suffix_frozen_smul A θ₀ k hc, ← smul_sub,
      norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hc0 _)]
    refine (mul_le_mul_of_nonneg_left (hC₂ z₁ hz₁ z₂ hz₂ v) (pow_nonneg hc0 _)).trans ?_
    rw [mul_assoc C₂, mul_assoc _ _ ‖v‖]
    exact hnum _ (Nat.sub_le _ _) C₂ _ _ hC₂0 (by linarith) (by positivity)
      (mul_le_mul_of_nonneg_right hle (norm_nonneg v))
  · rw [fderiv_suffix_frozen_smul A θ₀ k hc, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg hc0 _)]
    exact (mul_le_mul_of_nonneg_left (hC₂b z₂ hz₂ v) (pow_nonneg hc0 _)).trans
      (hnum _ (Nat.sub_le _ _) C₂ _ _ hC₂0 (by linarith) (norm_nonneg v) le_rfl)
  · rw [fderiv_params_suffix_frozen_smul, fderiv_params_suffix_frozen_smul, ← smul_sub,
      norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hc0 _)]
    exact (mul_le_mul_of_nonneg_left (hC₃ z₁ hz₁ z₂ hz₂) (pow_nonneg hc0 _)).trans
      (hnum _ le_rfl C₃ _ _ hC₃0 (by linarith) (norm_nonneg _) hle)

/-! ### Step 5: putting the bounds together -/

/-- **Step 5, abstractly.** The network after the block (`G`, its derivative `DG` in the hidden
state, its derivative `P` in the weights) and the frozen one (`G₀`, `DG₀`, `P₀`), at the outputs
`x` and `x₀` of the gated and the frozen block, with the directions `w`, `w₀` (in the hidden
state) and `q`, `q₀` (in the weights) through the block: if the networks after the block are
exponentially close at `x` (the induction hypothesis), the frozen one is Lipschitz with polynomial
growth between `x₀` and `x`, and the block bounds hold, then the three differences before the block
are exponentially small. -/
private theorem combine_bounds {ι X Y : Type*} [SeminormedAddCommGroup X]
    [SeminormedAddCommGroup Y] {S : Set ι} (G G₀ P P₀ : X → Y) (DG DG₀ : X → X → Y)
    (hlin : ∀ x a b, DG₀ x a - DG₀ x b = DG₀ x (a - b))
    (x x₀ w w₀ q q₀ : ℝ → ι → X) {κ C : ℝ} (hκ : 0 < κ) (hC : 0 ≤ C) (N : ℕ)
    (hx : ExpSmall p S fun t i => ‖x t i - x₀ t i‖)
    (hw : PolyB S fun t i => ‖w t i‖) (hww : ExpSmall p S fun t i => ‖w t i - w₀ t i‖)
    (hq : PolyB S fun t i => ‖q t i‖) (hqq : ExpSmall p S fun t i => ‖q t i - q₀ t i‖)
    (hnet : ∀ᶠ t in atTop, ∀ i ∈ S,
      (‖G (x t i) - G₀ (x t i)‖ ≤ Real.exp (-(κ * t ^ p)) ∧
        (∀ v, ‖DG (x t i) v - DG₀ (x t i) v‖ ≤ Real.exp (-(κ * t ^ p)) * ‖v‖) ∧
        ‖P (x t i) - P₀ (x t i)‖ ≤ Real.exp (-(κ * t ^ p))) ∧
      (‖G₀ (x t i) - G₀ (x₀ t i)‖ ≤ C * t ^ N * ‖x t i - x₀ t i‖ ∧
        (∀ v, ‖DG₀ (x t i) v - DG₀ (x₀ t i) v‖ ≤ C * t ^ N * ‖x t i - x₀ t i‖ * ‖v‖) ∧
        (∀ v, ‖DG₀ (x₀ t i) v‖ ≤ C * t ^ N * ‖v‖) ∧
        ‖P₀ (x t i) - P₀ (x₀ t i)‖ ≤ C * t ^ N * ‖x t i - x₀ t i‖)) :
    ExpSmall p S (fun t i => ‖G (x t i) - G₀ (x₀ t i)‖) ∧
    ExpSmall p S (fun t i => ‖DG (x t i) (w t i) - DG₀ (x₀ t i) (w₀ t i)‖) ∧
    ExpSmall p S (fun t i =>
      ‖(P (x t i) + DG (x t i) (q t i)) - (P₀ (x₀ t i) + DG₀ (x₀ t i) (q₀ t i))‖) := by
  have he : ExpSmall p S (fun t (_ : ι) => Real.exp (-(κ * t ^ p))) :=
    (expSmall_monomial hκ 1 0).mono (Eventually.of_forall fun t i _ => by simp)
  have hCt : PolyB S (fun t (_ : ι) => C * t ^ N) := polyB_monomial C N
  have hCt0 : ∀ᶠ t in atTop, ∀ i ∈ S, 0 ≤ C * t ^ N := by
    filter_upwards [eventually_ge_atTop 0] with t ht i _ using mul_nonneg hC (pow_nonneg ht N)
  have hn : ∀ f : ℝ → ι → X, ∀ᶠ t in atTop, ∀ i ∈ S, 0 ≤ ‖f t i‖ := fun f =>
    Eventually.of_forall fun _ _ _ => norm_nonneg _
  have he0 : ∀ᶠ t in atTop, ∀ i ∈ S, 0 ≤ Real.exp (-(κ * t ^ p)) :=
    Eventually.of_forall fun _ _ _ => (Real.exp_pos _).le
  -- `‖x − x₀‖ C t^N` is exponentially small
  have hxC := hx.mul hCt (hn _) hCt0
  have hxC0 : ∀ᶠ t in atTop, ∀ i ∈ S, 0 ≤ ‖x t i - x₀ t i‖ * (C * t ^ N) := by
    filter_upwards [hCt0] with t h i hi using mul_nonneg (norm_nonneg _) (h i hi)
  -- the derivative of the networks after the block, along `u` and `u₀`
  have hD : ∀ u u₀ : ℝ → ι → X, (PolyB S fun t i => ‖u t i‖) →
      (ExpSmall p S fun t i => ‖u t i - u₀ t i‖) →
      ExpSmall p S (fun t i => ‖DG (x t i) (u t i) - DG₀ (x₀ t i) (u₀ t i)‖) := by
    intro u u₀ hu huu
    refine (((he.mul hu he0 (hn _)).add (hxC.mul hu hxC0 (hn _))).add
      (huu.mul hCt (hn _) hCt0)).mono ?_
    filter_upwards [hnet] with t hb i hi
    obtain ⟨⟨-, h2, -⟩, -, h5, h6, -⟩ := hb i hi
    have t1 := norm_sub_le_norm_sub_add_norm_sub (DG (x t i) (u t i)) (DG₀ (x t i) (u t i))
      (DG₀ (x₀ t i) (u₀ t i))
    have t2 := norm_sub_le_norm_sub_add_norm_sub (DG₀ (x t i) (u t i)) (DG₀ (x₀ t i) (u t i))
      (DG₀ (x₀ t i) (u₀ t i))
    rw [hlin] at t2
    have b2 := h2 (u t i)
    have b5 := h5 (u t i)
    have b6 := h6 (u t i - u₀ t i)
    nlinarith
  refine ⟨?_, hD w w₀ hw hww, ?_⟩
  · refine (he.add hxC).mono ?_
    filter_upwards [hnet] with t hb i hi
    obtain ⟨⟨h1, -, -⟩, h4, -, -, -⟩ := hb i hi
    have t1 := norm_sub_le_norm_sub_add_norm_sub (G (x t i)) (G₀ (x t i)) (G₀ (x₀ t i))
    nlinarith
  · refine ((he.add hxC).add (hD q q₀ hq hqq)).mono ?_
    filter_upwards [hnet] with t hb i hi
    obtain ⟨⟨-, -, h3⟩, -, -, -, h7⟩ := hb i hi
    have e : (P (x t i) + DG (x t i) (q t i)) - (P₀ (x₀ t i) + DG₀ (x₀ t i) (q₀ t i))
        = (P (x t i) - P₀ (x₀ t i)) + (DG (x t i) (q t i) - DG₀ (x₀ t i) (q₀ t i)) := by abel
    rw [e]
    have t1 := norm_add_le (P (x t i) - P₀ (x₀ t i))
      (DG (x t i) (q t i) - DG₀ (x₀ t i) (q₀ t i))
    have t2 := norm_sub_le_norm_sub_add_norm_sub (P (x t i)) (P₀ (x t i)) (P₀ (x₀ t i))
    nlinarith

/-! ### The induction -/

/-- A positive function on a finite type has a positive lower bound `2μ`. -/
private theorem exists_pos_two_mul_le {α : Type*} [Finite α] (f : α → ℝ) (hf : ∀ a, 0 < f a) :
    ∃ μ : ℝ, 0 < μ ∧ ∀ a, 2 * μ ≤ f a := by
  cases isEmpty_or_nonempty α with
  | inl h => exact ⟨1, one_pos, fun a => (IsEmpty.false a).elim⟩
  | inr h =>
    obtain ⟨a₀, ha₀⟩ := Finite.exists_min f
    exact ⟨f a₀ / 2, half_pos (hf a₀), fun a => by linarith [ha₀ a]⟩

/-- The claim of Lemma D.11 at `k`, for all `H` with rows in `C k` at once. -/
private def FarBound (p : ℕ) (C : Fin (L + 1) → Set (d → ℝ)) (A : ∀ ℓ, Finset (hid ℓ))
    (θ η : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) (k : Fin (L + 1)) : Prop :=
  ∀ H : Matrix T d ℝ, (∀ t, H t ∈ C k) →
    ∃ ϱ : ℝ, 0 < ϱ ∧ ∃ κ : ℝ, 0 < κ ∧ ∃ t₀ : ℝ, ∀ t : ℝ, t₀ ≤ t → ∀ U : Matrix T d ℝ, ‖U‖ ≤ ϱ →
      ‖suffix (Arch.gated σ id hid) 0 θ k (t • (H + U))
          - suffix (Arch.frozen A) 0 (θ.toFrozen A) k (t • (H + U))‖ ≤ Real.exp (-(κ * t ^ p)) ∧
      (∀ v : Matrix T d ℝ,
        ‖fderiv ℝ (fun h' : Matrix T d ℝ => suffix (Arch.gated σ id hid) 0 θ k h') (t • (H + U)) v
            - fderiv ℝ (fun h' : Matrix T d ℝ => suffix (Arch.frozen A) 0 (θ.toFrozen A) k h')
                (t • (H + U)) v‖ ≤ Real.exp (-(κ * t ^ p)) * ‖v‖) ∧
      ‖fderiv ℝ (fun θ' : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut =>
              suffix (Arch.gated σ id hid) 0 θ' k (t • (H + U))) θ η
          - fderiv ℝ (fun θ' : Params (Arch.frozen (T := T) (d := d) A) dIn dOut =>
              suffix (Arch.frozen A) 0 θ' k (t • (H + U))) (θ.toFrozen A) (η.toFrozen A)‖
        ≤ Real.exp (-(κ * t ^ p))

/-- `k = L`: both networks are `h ↦ h D`, and all three differences vanish. -/
private theorem farBound_last {C : Fin (L + 1) → Set (d → ℝ)} {A : ∀ ℓ, Finset (hid ℓ)}
    (θ η : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) :
    FarBound p C A θ η (Fin.last L) := by
  intro H _
  refine ⟨1, one_pos, 1, one_pos, 0, fun t _ U _ => ⟨?_, fun v => ?_, ?_⟩⟩
  · rw [suffix_last_eq_mul _ θ rfl, suffix_last_eq_mul _ (θ.toFrozen A) rfl,
      show (θ.toFrozen A).D = θ.D from rfl, sub_self, norm_zero]
    exact (Real.exp_pos _).le
  · rw [fderiv_suffix_last _ θ rfl, fderiv_suffix_last _ (θ.toFrozen A) rfl,
      show (θ.toFrozen A).D = θ.D from rfl, sub_self, norm_zero]
    exact mul_nonneg (Real.exp_pos _).le (norm_nonneg v)
  · rw [fderiv_params_suffix_last _ θ rfl, fderiv_params_suffix_last _ (θ.toFrozen A) rfl,
      show (η.toFrozen A).D = η.D from rfl, sub_self, norm_zero]
    exact (Real.exp_pos _).le

/-- **The step from `ℓ + 1` to `ℓ`** (steps 1 to 5 of the proof): the bounds after block `ℓ`, at
every `H'` with rows in `C_{ℓ+1}`, give them before the block, at every `H` with rows in `C_ℓ`. -/
private theorem farBound_castSucc (hg : GateFar σ σ' p) {C : Fin (L + 1) → Set (d → ℝ)}
    {A : ∀ ℓ, Finset (hid ℓ)} {θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut}
    (hθ : GoodForConesGated C A θ) (η : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (ℓ : Fin L) (ih : FarBound p C A θ η ℓ.succ) : FarBound p C A θ η ℓ.castSucc := by
  intro H hH
  have hp1 := hg.one_le
  -- step 1: the gates of `H` have the signs of the active set, and are `2μ` away from zero
  have hgp : ∀ τ, ∀ j ∈ A ℓ, 0 < (H * θ.read ℓ) τ (Sum.inl j) := fun τ j hj =>
    hθ.gate_pos ℓ (H τ) (hH τ) j hj
  have hgn : ∀ τ, ∀ j ∉ A ℓ, (H * θ.read ℓ) τ (Sum.inl j) < 0 := fun τ j hj =>
    hθ.gate_neg ℓ (H τ) (hH τ) j hj
  have hsign : ∀ τ j, 0 < |(H * θ.read ℓ) τ (Sum.inl j)| := by
    intro τ j
    by_cases hj : j ∈ A ℓ
    · exact abs_pos.2 (hgp τ j hj).ne'
    · exact abs_pos.2 (hgn τ j hj).ne
  obtain ⟨μ, hμ, hμle⟩ := exists_pos_two_mul_le
    (fun a : T × hid ℓ => |(H * θ.read ℓ) a.1 (Sum.inl a.2)|) fun a => hsign a.1 a.2
  have hpos : ∀ τ, ∀ j ∈ A ℓ, 2 * μ ≤ (H * θ.read ℓ) τ (Sum.inl j) := fun τ j hj => by
    have h1 := hμle (τ, j)
    rwa [abs_of_pos (hgp τ j hj)] at h1
  have hneg : ∀ τ, ∀ j ∉ A ℓ, (H * θ.read ℓ) τ (Sum.inl j) ≤ -(2 * μ) := fun τ j hj => by
    have h1 := hμle (τ, j)
    rw [abs_of_neg (hgn τ j hj)] at h1
    linarith
  -- step 3: the frozen block sends `H` to `H'`, with rows in `C_{ℓ+1}`
  obtain ⟨H', hH'⟩ : ∃ H', H' = qa (aF (A ℓ)) (H * θ.read ℓ) * θ.write ℓ := ⟨_, rfl⟩
  have hH'C : ∀ τ, H' τ ∈ C ℓ.succ := fun τ => by
    rw [hH', ← frozen_f_eq (d := d) A ℓ, frozen_block_apply A θ ℓ H τ]
    exact hθ.frozen_mem ℓ (H τ) (hH τ)
  -- the induction hypothesis at `H'`
  obtain ⟨ϱ', hϱ', κ', hκ', t₀', hIH⟩ := ih H' hH'C
  -- step 4: the frozen network after the block, on the dilations of the ball around `H'`
  obtain ⟨Cf, hCf0, hCf⟩ := frozen_lip A (θ.toFrozen A) (η.toFrozen A) ℓ.succ H' ϱ'
  -- the frozen block is continuous: `‖g°(H + U) − H'‖ ≤ ϱ'/2` for small `U`
  have hcont : Continuous (fun n : Matrix T d ℝ => qa (aF (A ℓ)) (n * θ.read ℓ) * θ.write ℓ) := by
    have h := analyticOnNhd_block (Arch.frozen (T := T) (d := d) A) (θ.toFrozen A)
      (analyticOnNhd_f_frozen A) ℓ
    have h2 := continuousOn_univ.mp h.continuousOn
    have e : (fun n : Matrix T d ℝ => (Arch.frozen (T := T) (d := d) A).f ℓ
        (n * (θ.toFrozen A).read ℓ) * (θ.toFrozen A).write ℓ)
        = fun n => qa (aF (A ℓ)) (n * θ.read ℓ) * θ.write ℓ :=
      funext fun n => by rw [frozen_f_eq]; rfl
    rw [e] at h2
    exact h2
  obtain ⟨δ, hδ, hδc⟩ := Metric.continuousAt_iff.1 hcont.continuousAt (ϱ' / 2) (half_pos hϱ')
  -- the radius `ϱ`
  have hD0 : 0 < (Fintype.card d : ℝ) * ‖θ.read ℓ‖ + 1 := by positivity
  obtain ⟨ϱ, hϱdef⟩ : ∃ ϱ : ℝ, ϱ = min (δ / 2) (μ / (Fintype.card d * ‖θ.read ℓ‖ + 1)) :=
    ⟨_, rfl⟩
  have hϱ : 0 < ϱ := by rw [hϱdef]; exact lt_min (half_pos hδ) (div_pos hμ hD0)
  have hϱW : Fintype.card d * ϱ * ‖θ.read ℓ‖ ≤ μ := by
    have h1 : ϱ ≤ μ / (Fintype.card d * ‖θ.read ℓ‖ + 1) := hϱdef ▸ min_le_right _ _
    rw [le_div_iff₀ hD0] at h1
    nlinarith [norm_nonneg (θ.read ℓ)]
  have hϱδ : ∀ U : Matrix T d ℝ, ‖U‖ ≤ ϱ →
      ‖qa (aF (A ℓ)) ((H + U) * θ.read ℓ) * θ.write ℓ - H'‖ ≤ ϱ' / 2 := by
    intro U hU
    have h1 : dist (H + U) H < δ := by
      rw [dist_eq_norm, add_sub_cancel_left]
      have : ϱ ≤ δ / 2 := hϱdef ▸ min_le_left _ _
      linarith
    have h2 : dist (qa (aF (A ℓ)) ((H + U) * θ.read ℓ) * θ.write ℓ)
        (qa (aF (A ℓ)) (H * θ.read ℓ) * θ.write ℓ) < ϱ' / 2 := hδc h1
    rw [dist_eq_norm, ← hH'] at h2
    exact h2.le
  -- step 2: the block bounds on `S = {(U, v) : ‖U‖ ≤ ϱ, ‖v‖ ≤ 1}`
  obtain ⟨S, hS⟩ : ∃ S : Set (Matrix T d ℝ × Matrix T d ℝ), S = {i | ‖i.1‖ ≤ ϱ ∧ ‖i.2‖ ≤ 1} :=
    ⟨_, rfl⟩
  have hSm : ∀ i ∈ S, ‖i.1‖ ≤ ϱ ∧ ‖i.2‖ ≤ 1 := fun i hi => by rw [hS] at hi; exact hi
  obtain ⟨hx, hw, hww, hq, hqq⟩ := block_bounds hg (A ℓ) (θ.read ℓ) (η.read ℓ) (θ.write ℓ)
    (η.write ℓ) H hμ hpos hneg hϱ.le hϱW S hSm
  -- step 5: the induction hypothesis and the frozen network at the outputs of the two blocks
  obtain ⟨hv1, hv2, hv3⟩ := combine_bounds (S := S) (p := p)
    (fun z => suffix (Arch.gated σ id hid) 0 θ ℓ.succ z)
    (fun z => suffix (Arch.frozen A) 0 (θ.toFrozen A) ℓ.succ z)
    (fun z => fderiv ℝ (fun θ' : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut =>
      suffix (Arch.gated σ id hid) 0 θ' ℓ.succ z) θ η)
    (fun z => fderiv ℝ (fun θ' : Params (Arch.frozen (T := T) (d := d) A) dIn dOut =>
      suffix (Arch.frozen A) 0 θ' ℓ.succ z) (θ.toFrozen A) (η.toFrozen A))
    (fun z v => fderiv ℝ (fun h' : Matrix T d ℝ => suffix (Arch.gated σ id hid) 0 θ ℓ.succ h') z v)
    (fun z v => fderiv ℝ (fun h' : Matrix T d ℝ =>
      suffix (Arch.frozen A) 0 (θ.toFrozen A) ℓ.succ h') z v)
    (fun z a b => (map_sub _ a b).symm)
    (fun t i => qa (fun _ => σ) ((t • (H + i.1)) * θ.read ℓ) * θ.write ℓ)
    (fun t i => qa (aF (A ℓ)) ((t • (H + i.1)) * θ.read ℓ) * θ.write ℓ)
    (fun t i => dqa (fun _ => σ) (fun _ => σ') ((t • (H + i.1)) * θ.read ℓ)
      (i.2 * θ.read ℓ) * θ.write ℓ)
    (fun t i => dqa (aF (A ℓ)) (aF' (A ℓ)) ((t • (H + i.1)) * θ.read ℓ)
      (i.2 * θ.read ℓ) * θ.write ℓ)
    (fun t i => dqa (fun _ => σ) (fun _ => σ') ((t • (H + i.1)) * θ.read ℓ)
      ((t • (H + i.1)) * η.read ℓ) * θ.write ℓ
        + qa (fun _ => σ) ((t • (H + i.1)) * θ.read ℓ) * η.write ℓ)
    (fun t i => dqa (aF (A ℓ)) (aF' (A ℓ)) ((t • (H + i.1)) * θ.read ℓ)
      ((t • (H + i.1)) * η.read ℓ) * θ.write ℓ
        + qa (aF (A ℓ)) ((t • (H + i.1)) * θ.read ℓ) * η.write ℓ)
    hκ' hCf0 (2 * 2 ^ (L - ((ℓ.succ : Fin (L + 1)) : ℕ))) hx hw hww hq hqq (by
      filter_upwards [hx.eventually_le hp1 (half_pos hϱ'), eventually_ge_atTop (max 1 t₀')]
        with t hxt ht i hi
      have ht1 : 1 ≤ t := (le_max_left _ _).trans ht
      have ht0 : 0 < t := zero_lt_one.trans_le ht1
      have hc : t ^ 2 ≠ 0 := by positivity
      have hxi := hxt i hi
      have hUi : ‖i.1‖ ≤ ϱ := (hSm i hi).1
      -- the outputs of the two blocks: `x = t² z₁` and `x₀ = t² z₂`
      obtain ⟨X, hX⟩ : ∃ X, X = qa (fun _ => σ) ((t • (H + i.1)) * θ.read ℓ) * θ.write ℓ :=
        ⟨_, rfl⟩
      obtain ⟨X₀, hX₀⟩ : ∃ X₀, X₀ = qa (aF (A ℓ)) ((t • (H + i.1)) * θ.read ℓ) * θ.write ℓ :=
        ⟨_, rfl⟩
      rw [← hX, ← hX₀] at hxi ⊢
      obtain ⟨z₂, hz₂⟩ : ∃ z₂, z₂ = qa (aF (A ℓ)) ((H + i.1) * θ.read ℓ) * θ.write ℓ := ⟨_, rfl⟩
      have hX₀z : X₀ = t ^ 2 • z₂ := by
        rw [hX₀, hz₂, Matrix.smul_mul, qa_smul (aF_mul (A ℓ)), Matrix.smul_mul]
      have hz₂' : ‖z₂ - H'‖ ≤ ϱ' / 2 := by rw [hz₂]; exact hϱδ i.1 hUi
      have hz₂b : z₂ ∈ Metric.closedBall H' ϱ' := by
        rw [Metric.mem_closedBall, dist_eq_norm]; linarith
      obtain ⟨z₁, hz₁⟩ : ∃ z₁, z₁ = (t ^ 2)⁻¹ • X := ⟨_, rfl⟩
      have hXz : X = t ^ 2 • z₁ := by rw [hz₁, smul_smul, mul_inv_cancel₀ hc, one_smul]
      have hz₁₂ : ‖z₁ - z₂‖ ≤ ‖X - X₀‖ := by
        have e : z₁ - z₂ = (t ^ 2)⁻¹ • (X - X₀) := by
          rw [hz₁, hX₀z, smul_sub, smul_smul, inv_mul_cancel₀ hc, one_smul]
        rw [e, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact mul_le_of_le_one_left (norm_nonneg _) (inv_le_one_of_one_le₀ (by nlinarith))
      have hz₁b : z₁ ∈ Metric.closedBall H' ϱ' := by
        rw [Metric.mem_closedBall, dist_eq_norm]
        have := norm_sub_le_norm_sub_add_norm_sub z₁ z₂ H'
        linarith
      -- the induction hypothesis at `t²` and `U'' = z₁ − H'`
      have ht₀' : t₀' ≤ t ^ 2 := by nlinarith [le_max_right 1 t₀']
      obtain ⟨i1, i2, i3⟩ := hIH (t ^ 2) ht₀' (z₁ - H') (by rw [← dist_eq_norm]; exact hz₁b)
      rw [add_sub_cancel, ← hXz] at i1 i2 i3
      have hexp : Real.exp (-(κ' * (t ^ 2) ^ p)) ≤ Real.exp (-(κ' * t ^ p)) :=
        Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ ht0.le (by nlinarith) p) hκ'.le))
      -- the frozen network between `x₀` and `x`
      obtain ⟨f1, f2, f3, f4⟩ := hCf t ht1 z₁ hz₁b z₂ hz₂b
      rw [← hXz, ← hX₀z] at f1 f2 f4
      rw [← hX₀z] at f3
      exact ⟨⟨i1.trans hexp, fun v => (i2 v).trans
        (mul_le_mul_of_nonneg_right hexp (norm_nonneg v)), i3.trans hexp⟩, f1, f2, f3, f4⟩)
  -- absorbing the powers of `t`
  obtain ⟨κ₁, hκ₁, e1⟩ := hv1.exists_bound hp1
  obtain ⟨κ₂, hκ₂, e2⟩ := hv2.exists_bound hp1
  obtain ⟨κ₃, hκ₃, e3⟩ := hv3.exists_bound hp1
  obtain ⟨t₀, ht₀⟩ := eventually_atTop.1 (e1.and (e2.and (e3.and (eventually_ge_atTop 0))))
  refine ⟨ϱ, hϱ, min κ₁ (min κ₂ κ₃), lt_min hκ₁ (lt_min hκ₂ hκ₃), t₀, fun t ht U hU => ?_⟩
  obtain ⟨f1, f2, f3, ht0⟩ := ht₀ t ht
  have hmono : ∀ κ'', min κ₁ (min κ₂ κ₃) ≤ κ'' →
      Real.exp (-(κ'' * t ^ p)) ≤ Real.exp (-(min κ₁ (min κ₂ κ₃) * t ^ p)) := fun κ'' h =>
    Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_right h (pow_nonneg ht0 p)))
  have hS0 : (U, (0 : Matrix T d ℝ)) ∈ S := by rw [hS]; exact ⟨hU, by simp⟩
  refine ⟨?_, fun v => ?_, ?_⟩
  · -- the value
    rw [suffix_gated_castSucc, suffix_frozen_castSucc]
    exact (f1 _ hS0).trans (hmono _ (min_le_left _ _))
  · -- the derivative in the hidden state, along `v = ‖v‖ u` with `‖u‖ ≤ 1`
    rcases eq_or_ne v 0 with rfl | hv
    · simp
    have hnv : 0 < ‖v‖ := norm_pos_iff.2 hv
    obtain ⟨u, hu⟩ : ∃ u, u = ‖v‖⁻¹ • v := ⟨_, rfl⟩
    have hvu : v = ‖v‖ • u := by rw [hu, smul_smul, mul_inv_cancel₀ hnv.ne', one_smul]
    have hu1 : ‖u‖ ≤ 1 := by
      rw [hu, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hnv.ne']
    have hSu : (U, u) ∈ S := by rw [hS]; exact ⟨hU, hu1⟩
    conv_lhs => rw [hvu, map_smul, map_smul, ← smul_sub, norm_smul, norm_norm]
    rw [fderiv_gated_castSucc hg.hasDerivAt, fderiv_frozen_castSucc, mul_comm ‖v‖]
    exact mul_le_mul_of_nonneg_right
      ((f2 _ hSu).trans (hmono _ ((min_le_right _ _).trans (min_le_left _ _)))) hnv.le
  · -- the derivative in the weights
    rw [fderiv_params_gated_castSucc hg.hasDerivAt, fderiv_params_frozen_castSucc]
    exact (f3 _ hS0).trans (hmono _ ((min_le_right _ _).trans (min_le_right _ _)))

/-- The claim for every `k`, by reverse induction. -/
private theorem farBound_all (hg : GateFar σ σ' p) {C : Fin (L + 1) → Set (d → ℝ)}
    {A : ∀ ℓ, Finset (hid ℓ)} {θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut}
    (hθ : GoodForConesGated C A θ) (η : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (k : Fin (L + 1)) : FarBound p C A θ η k := by
  induction k using Fin.reverseInduction with
  | last => exact farBound_last θ η
  | cast ℓ ih => exact farBound_castSucc hg hθ η ℓ ih

/-- **Lemma D.11, for real hidden states, with the derivative in the hidden state.** Let `θ` be
good for the cones, and let all rows of `H` lie in `C_k`. There are `ϱ, κ > 0` and `t₀` such that
for `t ≥ t₀` and `‖U‖ ≤ ϱ`, at `h = t (H + U)`, the network after `h_k` and the frozen network
after `h_k`, their derivatives in the hidden state (along `v`, up to the factor `‖v‖`), and their
derivatives in the weights along `η` differ by at most `e^{−κ t^p}`. -/
theorem exists_far_frozen_bounds (hg : GateFar σ σ' p) {C : Fin (L + 1) → Set (d → ℝ)}
    {A : ∀ ℓ, Finset (hid ℓ)} {θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut}
    (hθ : GoodForConesGated C A θ) (k : Fin (L + 1)) (H : Matrix T d ℝ) (hH : ∀ t, H t ∈ C k)
    (η : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) :
    ∃ ϱ : ℝ, 0 < ϱ ∧ ∃ κ : ℝ, 0 < κ ∧ ∃ t₀ : ℝ, ∀ t : ℝ, t₀ ≤ t → ∀ U : Matrix T d ℝ, ‖U‖ ≤ ϱ →
      ‖suffix (Arch.gated σ id hid) 0 θ k (t • (H + U))
          - suffix (Arch.frozen A) 0 (θ.toFrozen A) k (t • (H + U))‖ ≤ Real.exp (-(κ * t ^ p)) ∧
      (∀ v : Matrix T d ℝ,
        ‖fderiv ℝ (fun h' : Matrix T d ℝ => suffix (Arch.gated σ id hid) 0 θ k h') (t • (H + U)) v
            - fderiv ℝ (fun h' : Matrix T d ℝ => suffix (Arch.frozen A) 0 (θ.toFrozen A) k h')
                (t • (H + U)) v‖ ≤ Real.exp (-(κ * t ^ p)) * ‖v‖) ∧
      ‖fderiv ℝ (fun θ' : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut =>
              suffix (Arch.gated σ id hid) 0 θ' k (t • (H + U))) θ η
          - fderiv ℝ (fun θ' : Params (Arch.frozen (T := T) (d := d) A) dIn dOut =>
              suffix (Arch.frozen A) 0 θ' k (t • (H + U))) (θ.toFrozen A) (η.toFrozen A)‖
        ≤ Real.exp (-(κ * t ^ p)) :=
  farBound_all hg hθ η k H hH

end Skips
