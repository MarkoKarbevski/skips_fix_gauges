import SkipsLean.Residual.SmallWritesNorm
import SkipsLean.Depth.SuffixRMS

/-!
# Small writes under pre-RMSNorm: the final normalization, large inputs, the skip

Paper (skips paper): proof of Lemma A.27, paragraph "Under pre-RMSNorm", for `ε > 0`. With
`h = x E`, `n = N_ε(h)` and the limit

  `(J_0 η)(x) = 𝐃N_ε(h) (x η_E + D_θ g(n) η) D + N_ε(h) η_D`

(`smallWritesLimitNorm`, `Residual/SmallWritesNorm.lean`), "this is the equation of the proof of
Theorem B.1 (ii) with `h_1 = x E` and `D_θ h_1 η = x η_E + D_θ g(n) η`, and its Steps 1 to 5 go
through with three changes. In Step 2, `D_θ g(n) η` is bounded, since `‖n_t‖ < √d` for every
token `t`. In Step 3, the direction `η^Y` has the entries `E Y` at `E` and `-Y D` at `D` and no
others, since `𝐃N_ε(h)(h Y) = N_ε(h) Y` for antisymmetric `Y`."

This file states Steps 1 to 3 for a direction `η` that is flat for `J_0`: there is an
antisymmetric `Y` with `η_E = E Y` and `η_D = -Y D`, and `D_θ g(n) η = 0` at every
`n = N_ε(x E)`. Step 4 starts there (`Residual/DepthMlpRMS.lean`, `Residual/DepthGatedRMS.lean`).
The steps do not depend on the kind of block: the maps `f_ℓ` are arbitrary continuously
differentiable maps.
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d]
  [Fintype dIn] [Fintype dOut]

/-- The derivative of the wide block along the reads and writes of `η`, at the input `n`. -/
private noncomputable def blockDirSS (A : Arch T d L) (θ η : Params A dIn dOut)
    (n : Matrix T d ℝ) : Matrix T d ℝ :=
  ∑ ℓ, (fderiv ℝ (A.f ℓ) (n * θ.read ℓ) (n * η.read ℓ) * θ.write ℓ
    + A.f ℓ (n * θ.read ℓ) * η.write ℓ)

omit [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: one term of `blockDirSS` is continuous in `n` (`f_ℓ` is `C¹`). -/
private theorem continuous_blockDirSS_term (A : Arch T d L) (θ η : Params A dIn dOut)
    (hf : ∀ ℓ, ContDiff ℝ 1 (A.f ℓ)) (ℓ : Fin L) :
    Continuous fun n : Matrix T d ℝ => fderiv ℝ (A.f ℓ) (n * θ.read ℓ) (n * η.read ℓ) * θ.write ℓ
      + A.f ℓ (n * θ.read ℓ) * η.write ℓ := by
  have hr : Continuous fun n : Matrix T d ℝ => n * θ.read ℓ :=
    continuous_id.matrix_mul continuous_const
  have he : Continuous fun n : Matrix T d ℝ => n * η.read ℓ :=
    continuous_id.matrix_mul continuous_const
  have h1 : Continuous fun n : Matrix T d ℝ =>
      fderiv ℝ (A.f ℓ) (n * θ.read ℓ) (n * η.read ℓ) := by
    have h0 := (hf ℓ).continuous_fderiv_apply one_ne_zero
    have h1 : Continuous fun n : Matrix T d ℝ => (n * θ.read ℓ, n * η.read ℓ) := hr.prodMk he
    have h2 := h0.comp h1
    exact h2
  have h3 : Continuous fun n : Matrix T d ℝ =>
      fderiv ℝ (A.f ℓ) (n * θ.read ℓ) (n * η.read ℓ) * θ.write ℓ :=
    h1.matrix_mul continuous_const
  have h4 : Continuous fun n : Matrix T d ℝ => A.f ℓ (n * θ.read ℓ) :=
    (hf ℓ).continuous.comp hr
  have h5 : Continuous fun n : Matrix T d ℝ => A.f ℓ (n * θ.read ℓ) * η.write ℓ :=
    h4.matrix_mul continuous_const
  exact h3.add h5

omit [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: `blockDirSS` is continuous in `n`. -/
private theorem continuous_blockDirSS (A : Arch T d L) (θ η : Params A dIn dOut)
    (hf : ∀ ℓ, ContDiff ℝ 1 (A.f ℓ)) : Continuous (blockDirSS A θ η) := by
  have h : Continuous fun n : Matrix T d ℝ => ∑ ℓ, (fderiv ℝ (A.f ℓ) (n * θ.read ℓ)
      (n * η.read ℓ) * θ.write ℓ + A.f ℓ (n * θ.read ℓ) * η.write ℓ) :=
    continuous_finsetSum _ fun ℓ _ => continuous_blockDirSS_term A θ η hf ℓ
  exact h

omit [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
private theorem norm_rmsNorm_le_ss {ε : ℝ} (hε : 0 < ε) (h : Matrix T d ℝ) :
    ‖rmsNorm ε h‖ ≤ Real.sqrt (Fintype.card d) := by
  refine (Matrix.norm_le_iff (Real.sqrt_nonneg _)).2 fun t i => ?_
  rw [Real.norm_eq_abs]
  apply Real.abs_le_sqrt
  show ((Real.sqrt ((h t ⬝ᵥ h t) / (Fintype.card d : ℝ) + ε))⁻¹ * h t i) ^ 2 ≤ _
  have hD : (0 : ℝ) < Fintype.card d := Nat.cast_pos.2 (Fintype.card_pos_iff.2 ⟨i⟩)
  have hsum : h t i ^ 2 ≤ h t ⬝ᵥ h t := by
    have := Finset.single_le_sum (f := fun j => h t j * h t j)
      (fun j _ => mul_self_nonneg (h t j)) (Finset.mem_univ i)
    simpa [dotProduct, sq] using this
  have hpos : 0 < (h t ⬝ᵥ h t) / (Fintype.card d : ℝ) + ε := by
    have := div_nonneg (le_trans (sq_nonneg _) hsum) hD.le
    linarith
  rw [mul_pow, inv_pow, Real.sq_sqrt hpos.le, inv_mul_le_iff₀ hpos, add_mul,
    div_mul_cancel₀ _ hD.ne']
  nlinarith

omit [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
private theorem exists_bound_blockDirSS (A : Arch T d L) (θ η : Params A dIn dOut)
    (hf : ∀ ℓ, ContDiff ℝ 1 (A.f ℓ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ B, ∀ h : Matrix T d ℝ, ‖blockDirSS A θ η (rmsNorm ε h)‖ ≤ B := by
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : Matrix T d ℝ)
    (Real.sqrt (Fintype.card d))).exists_bound_of_continuousOn
    (continuous_blockDirSS A θ η hf).continuousOn
  exact ⟨B, fun h => hB _ (mem_closedBall_zero_iff.2 (norm_rmsNorm_le_ss hε h))⟩

private theorem eq_zero_of_norm_smul_le_ss {M : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M]
    {b : M} {B : ℝ} (h : ∀ s : ℝ, 1 ≤ s → ‖s • b‖ ≤ B) : b = 0 := by
  by_contra hb
  have hb' : 0 < ‖b‖ := norm_pos_iff.2 hb
  have hs1 : (1 : ℝ) ≤ max 1 ((|B| + 1) / ‖b‖) := le_max_left _ _
  have hs2 : (|B| + 1) / ‖b‖ ≤ max 1 ((|B| + 1) / ‖b‖) := le_max_right _ _
  have h1 := h _ hs1
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith)] at h1
  rw [div_le_iff₀ hb'] at hs2
  linarith [le_abs_self B]

private theorem eq_zero_of_norm_cube_smul_add_le_ss {M : Type*} [NormedAddCommGroup M]
    [NormedSpace ℝ M] {a b : M} {B : ℝ} (h : ∀ s : ℝ, 1 ≤ s → ‖s ^ 3 • a + s • b‖ ≤ B) :
    a = 0 := by
  refine eq_zero_of_norm_smul_le_ss (B := |B| + ‖b‖) fun s hs => ?_
  have h1 := h s hs
  have hs0 : 0 < s := by linarith
  have h2 : ‖s ^ 3 • a‖ ≤ ‖s ^ 3 • a + s • b‖ + ‖s • b‖ := by
    have := norm_sub_le (s ^ 3 • a + s • b) (s • b)
    simpa using this
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (pow_pos hs0 3),
    abs_of_pos hs0] at h2
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs0]
  have ha := norm_nonneg a
  have hb := norm_nonneg b
  have hB := le_abs_self B
  have hB0 := abs_nonneg B
  have e1 : s * (s ^ 2 * ‖a‖) ≤ s * (|B| + ‖b‖) := by nlinarith
  have e2 : s ^ 2 * ‖a‖ ≤ |B| + ‖b‖ := le_of_mul_le_mul_left e1 hs0
  have e3 : s * ‖a‖ ≤ s ^ 2 * ‖a‖ :=
    mul_le_mul_of_nonneg_right (by nlinarith) ha
  linarith

omit [DecidableEq d] in
private theorem row_eq_of_fderiv_ss {ε : ℝ} (hε : 0 < ε) (v k w : d → ℝ)
    (e : (Real.sqrt ((v ⬝ᵥ v) / (Fintype.card d : ℝ) + ε))⁻¹ • k
      - ((v ⬝ᵥ k) / (Fintype.card d : ℝ)
          * (Real.sqrt ((v ⬝ᵥ v) / (Fintype.card d : ℝ) + ε))⁻¹ ^ 3) • v
      = (Real.sqrt ((v ⬝ᵥ v) / (Fintype.card d : ℝ) + ε))⁻¹ • w) :
    k = w + ((w ⬝ᵥ v) / ((Fintype.card d : ℝ) * ε)) • v := by
  rcases (Nat.cast_nonneg (Fintype.card d) : (0 : ℝ) ≤ Fintype.card d).eq_or_lt with hD | hD
  · have : IsEmpty d := Fintype.card_eq_zero_iff.1 (by exact_mod_cast hD.symm)
    funext i
    exact isEmptyElim i
  have hvv : 0 ≤ v ⬝ᵥ v := Finset.sum_nonneg fun j _ => mul_self_nonneg (v j)
  have hpos : 0 < (v ⬝ᵥ v) / (Fintype.card d : ℝ) + ε := by
    have := div_nonneg hvv hD.le
    linarith
  have hρpos : 0 < Real.sqrt ((v ⬝ᵥ v) / (Fintype.card d : ℝ) + ε) := Real.sqrt_pos.2 hpos
  have hρ2 : Real.sqrt ((v ⬝ᵥ v) / (Fintype.card d : ℝ) + ε) ^ 2
      = (v ⬝ᵥ v) / (Fintype.card d : ℝ) + ε := Real.sq_sqrt hpos.le
  generalize Real.sqrt ((v ⬝ᵥ v) / (Fintype.card d : ℝ) + ε) = ρ at e hρpos hρ2
  generalize (Fintype.card d : ℝ) = D at e hρ2 hD ⊢
  have hρ0 : ρ ≠ 0 := hρpos.ne'
  have hD0 : D ≠ 0 := hD.ne'
  obtain ⟨c, hc⟩ : ∃ c, c = (v ⬝ᵥ k) / D * ρ⁻¹ ^ 2 := ⟨_, rfl⟩
  -- multiplying row `t` by `ρ`: `k = w + c v`
  have hk : k = w + c • v := by
    funext i
    have ei := congrFun e i
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at ei
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have hinv : ρ * ρ⁻¹ = 1 := mul_inv_cancel₀ hρ0
    rw [hc]
    linear_combination ρ * ei - (k i - w i - (v ⬝ᵥ k) / D * ρ⁻¹ ^ 2 * v i) * hinv
  -- the product with `v`: `c d ε = ⟨w, v⟩`
  have hdot : v ⬝ᵥ k = v ⬝ᵥ w + c * (v ⬝ᵥ v) := by
    rw [hk, dotProduct_add, dotProduct_smul, smul_eq_mul]
  have h1 : c * (D * ρ ^ 2) = v ⬝ᵥ k := by
    rw [hc]
    field_simp
  have hcD : c * (D * ε) = w ⬝ᵥ v := by
    rw [hρ2] at h1
    rw [dotProduct_comm]
    have h2 : c * (D * ((v ⬝ᵥ v) / D + ε)) = c * (v ⬝ᵥ v) + c * (D * ε) := by
      field_simp
    linarith
  rw [hk]
  congr 2
  rw [eq_div_iff (mul_ne_zero hD0 hε.ne')]
  exact hcD

omit [Nonempty T] in
private theorem rows_of_fderiv_rmsNorm_ss {ε : ℝ} (hε : 0 < ε) (h k : Matrix T d ℝ)
    (Y : Matrix d d ℝ)
    (hk : fderiv ℝ (rmsNorm ε : Matrix T d ℝ → Matrix T d ℝ) h k = rmsNorm ε h * Y) (t : T) :
    k t = h t ᵥ* Y + (((h t ᵥ* Y) ⬝ᵥ h t) / ((Fintype.card d : ℝ) * ε)) • h t := by
  refine row_eq_of_fderiv_ss hε (h t) (k t) (h t ᵥ* Y) ?_
  have e := congrFun hk t
  rw [fderiv_rmsNorm_apply hε] at e
  refine e.trans ?_
  show rmsRow ε (h t) ᵥ* Y = _
  rw [rmsRow, smul_vecMul]

omit [Fintype T] [Nonempty T] [Fintype dOut] in
private theorem exists_input_ss {E : Matrix dIn d ℝ} {Ep : Matrix d dIn ℝ} (hEp : Ep * E = 1)
    (v : d → ℝ) : ∃ x : Matrix T dIn ℝ, ∀ t, (x * E) t = v :=
  ⟨Matrix.of fun _ => v ᵥ* Ep, fun t => by
    show (v ᵥ* Ep) ᵥ* E = v
    rw [vecMul_vecMul, hEp, vecMul_one]⟩

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
private theorem eq_zero_of_forall_mul_eq_zero_ss {m n : Type*} [Fintype m]
    {M : Matrix m n ℝ} (h : ∀ w : Matrix T m ℝ, w * M = 0) : M = 0 := by
  classical
  obtain ⟨t₀⟩ := ‹Nonempty T›
  refine Matrix.ext_of_single_vecMul fun i => ?_
  rw [Matrix.vecMul_zero]
  exact congrFun (h (Matrix.of fun _ => Pi.single i 1)) t₀

omit [Fintype T] [Fintype dOut] in
private theorem eq_zero_of_rmsNorm_mul_eq_zero_ss {m : Type*} {ε : ℝ} (hε : 0 < ε)
    {E : Matrix dIn d ℝ} {Ep : Matrix d dIn ℝ} (hEp : Ep * E = 1) {M : Matrix d m ℝ}
    (h : ∀ x : Matrix T dIn ℝ, rmsNorm ε (x * E) * M = 0) : M = 0 := by
  obtain ⟨t₀⟩ := ‹Nonempty T›
  refine Matrix.ext_of_single_vecMul fun i => ?_
  rw [Matrix.vecMul_zero]
  obtain ⟨x, hx⟩ := exists_input_ss (T := T) hEp (Pi.single i 1)
  have e : rmsRow ε ((x * E) t₀) ᵥ* M = 0 := congrFun (h x) t₀
  rw [hx t₀, rmsRow, smul_vecMul] at e
  refine (smul_eq_zero.1 e).resolve_left (inv_ne_zero (Real.sqrt_pos.2 ?_).ne')
  have : 0 ≤ (Pi.single i (1 : ℝ) ⬝ᵥ Pi.single i 1) / (Fintype.card d : ℝ) :=
    div_nonneg (Finset.sum_nonneg fun j _ => mul_self_nonneg _) (Nat.cast_nonneg _)
  linarith

/-- **Proof of Lemma A.27 under pre-RMSNorm (`ε > 0`), Steps 1 to 3:** let `E` and `D` have rank
`d`, and let `η` be flat for the limit `J_0`. Then there is an antisymmetric `Y` with
`η_E = E Y` and `η_D = -Y D`, and the derivative of the wide block
`n ↦ ∑_ℓ f_ℓ(n W_read^ℓ) W_write^ℓ` along the entries of `η` at the reads and the writes
vanishes at every `n = N_ε(x E)`. -/
theorem exists_antisymm_of_smallWritesLimitNorm_rmsNorm {A : Arch T d L} {ε : ℝ} (hε : 0 < ε)
    (hA : A.χ = rmsNorm ε) (hf : ∀ ℓ, ContDiff ℝ 1 (A.f ℓ)) (θ : Params A dIn dOut)
    (hE : θ.E.rank = Fintype.card d) (hD : θ.D.rank = Fintype.card d)
    (η : Params A dIn dOut) (hη : ∀ x, smallWritesLimitNorm A θ η x = 0) :
    ∃ Y : Matrix d d ℝ, Yᵀ = -Y ∧ η.E = θ.E * Y ∧ η.D = -(Y * θ.D) ∧
      ∀ x : Matrix T dIn ℝ,
        ∑ ℓ, (fderiv ℝ (A.f ℓ) (rmsNorm ε (x * θ.E) * θ.read ℓ)
                (rmsNorm ε (x * θ.E) * η.read ℓ) * θ.write ℓ
              + A.f ℓ (rmsNorm ε (x * θ.E) * θ.read ℓ) * η.write ℓ) = 0 := by
  -- the hypothesis with `N = N_ε` and the block term `S(x) = blockDirSS A θ η (N (x E))`
  have hη' : ∀ x : Matrix T dIn ℝ,
      fderiv ℝ (rmsNorm ε : Matrix T d ℝ → Matrix T d ℝ) (x * θ.E)
          (x * η.E + blockDirSS A θ η (rmsNorm ε (x * θ.E))) * θ.D
        + rmsNorm ε (x * θ.E) * η.D = 0 := by
    intro x
    have e := hη x
    rw [smallWritesLimitNorm, hA] at e
    exact e
  -- Step 1: a right inverse `D⁺` of `D` and a left inverse `E⁺` of `E`
  obtain ⟨Dp, hDp⟩ : ∃ B : Matrix dOut d ℝ, θ.D * B = 1 :=
    Matrix.mulVec_surjective_iff_exists_right_inverse.1
      (Matrix.mulVec_surjective_iff_rank_eq_card.2 hD)
  obtain ⟨Ep, hEp⟩ : ∃ B : Matrix d dIn ℝ, B * θ.E = 1 :=
    Matrix.vecMul_surjective_iff_exists_left_inverse.1
      (Matrix.vecMul_surjective_iff_rank_eq_card.2 hE)
  obtain ⟨Y, hY⟩ : ∃ Y : Matrix d d ℝ, Y = -(η.D * Dp) := ⟨_, rfl⟩
  -- multiplying by `D⁺`: `𝐃N(h) k(x) = N(h) Y`
  have h1 : ∀ x : Matrix T dIn ℝ,
      fderiv ℝ (rmsNorm ε : Matrix T d ℝ → Matrix T d ℝ) (x * θ.E)
          (x * η.E + blockDirSS A θ η (rmsNorm ε (x * θ.E)))
        = rmsNorm ε (x * θ.E) * Y := by
    intro x
    have e := congrArg (· * Dp) (hη' x)
    simp only [Matrix.add_mul, Matrix.mul_assoc, hDp, Matrix.mul_one, Matrix.zero_mul] at e
    rw [hY, Matrix.mul_neg]
    exact eq_neg_of_add_eq_zero_left e
  -- substituting back: `N(h) (Y D + η_D) = 0` for every `x`, so `η_D = -Y D`
  have hDeq : η.D = -(Y * θ.D) := by
    have e : ∀ x : Matrix T dIn ℝ, rmsNorm ε (x * θ.E) * (Y * θ.D + η.D) = 0 := by
      intro x
      have e := hη' x
      rw [h1 x] at e
      rw [Matrix.mul_add, ← Matrix.mul_assoc]
      exact e
    exact eq_neg_of_add_eq_zero_right (eq_zero_of_rmsNorm_mul_eq_zero_ss hε hEp e)
  -- row `t` of `k(x)`: `k(x)_t = h_t Y + μ_t h_t`, `μ_t = ⟨h_t Y, h_t⟩ / (d ε)`
  have hrow : ∀ (x : Matrix T dIn ℝ) (t : T),
      (x * η.E + blockDirSS A θ η (rmsNorm ε (x * θ.E))) t
        = (x * θ.E) t ᵥ* Y
          + ((((x * θ.E) t ᵥ* Y) ⬝ᵥ (x * θ.E) t) / ((Fintype.card d : ℝ) * ε)) • (x * θ.E) t :=
    fun x t => rows_of_fderiv_rmsNorm_ss hε _ _ Y (h1 x) t
  -- the block term is bounded, since `‖N_ε(h)‖ ≤ √d`
  obtain ⟨B, hB⟩ := exists_bound_blockDirSS A θ η hf hε
  obtain ⟨t₀⟩ := ‹Nonempty T›
  -- Step 2: along a ray `x = s w`, the cubic term must vanish, so `⟨u Y, u⟩ = 0` for every row `u`
  have hq : ∀ u : d → ℝ, (u ᵥ* Y) ⬝ᵥ u = 0 := by
    intro u
    obtain ⟨w, hw⟩ := exists_input_ss (T := T) hEp u
    have key : ∀ s : ℝ, 1 ≤ s →
        ‖s ^ 3 • ((((u ᵥ* Y) ⬝ᵥ u) / ((Fintype.card d : ℝ) * ε)) • u)
          + s • (u ᵥ* Y - (w * η.E) t₀)‖ ≤ B := by
      intro s _
      have e := hrow (s • w) t₀
      have e1 : (s • w * η.E + blockDirSS A θ η (rmsNorm ε (s • w * θ.E))) t₀
          = s • (w * η.E) t₀ + blockDirSS A θ η (rmsNorm ε (s • w * θ.E)) t₀ := by
        rw [Matrix.smul_mul]
        rfl
      have e2 : (s • w * θ.E) t₀ = s • u := by
        rw [Matrix.smul_mul, ← hw t₀]
        rfl
      rw [e1, e2, smul_vecMul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul] at e
      have e3 : blockDirSS A θ η (rmsNorm ε (s • w * θ.E)) t₀
          = s ^ 3 • ((((u ᵥ* Y) ⬝ᵥ u) / ((Fintype.card d : ℝ) * ε)) • u)
            + s • (u ᵥ* Y - (w * η.E) t₀) := by
        funext i
        have ei := congrFun e i
        simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at ei ⊢
        linear_combination ei
      rw [← e3]
      exact (norm_le_pi_norm _ t₀).trans (hB _)
    have ha := eq_zero_of_norm_cube_smul_add_le_ss key
    rcases smul_eq_zero.1 ha with h0 | h0
    · rcases div_eq_zero_iff.1 h0 with h0 | h0
      · exact h0
      · have hD0 : (Fintype.card d : ℝ) = 0 := (mul_eq_zero.1 h0).resolve_right hε.ne'
        have : IsEmpty d := Fintype.card_eq_zero_iff.1 (by exact_mod_cast hD0)
        rw [dotProduct, Finset.univ_eq_empty, Finset.sum_empty]
    · rw [h0, dotProduct_zero]
  -- polarisation: `Y` is antisymmetric
  have hYt : Yᵀ = -Y := by
    ext i j
    rw [Matrix.transpose_apply, Matrix.neg_apply]
    have hi := hq (Pi.single i 1)
    have hj := hq (Pi.single j 1)
    have hij := hq (Pi.single i 1 + Pi.single j 1)
    simp only [add_vecMul, dotProduct_add, single_one_vecMul, dotProduct_single, Pi.add_apply,
      Matrix.row_apply, mul_one] at hi hj hij
    linarith
  -- with `μ = 0`, Step 1 reads `k(x) = x E Y`
  have hk : ∀ x : Matrix T dIn ℝ,
      x * η.E + blockDirSS A θ η (rmsNorm ε (x * θ.E)) = x * θ.E * Y := by
    intro x
    funext t
    rw [hrow x t, hq, zero_div, zero_smul, add_zero]
    rfl
  -- Step 3: along a ray, `s w (E Y - η_E) = S(s w)` is bounded, so `η_E = E Y`
  have hEeq : η.E = θ.E * Y := by
    have hM : ∀ w : Matrix T dIn ℝ, w * (θ.E * Y - η.E) = 0 := by
      intro w
      refine eq_zero_of_norm_smul_le_ss (B := B) fun s _ => ?_
      have e := hk (s • w)
      have e' : s • (w * (θ.E * Y - η.E)) = blockDirSS A θ η (rmsNorm ε (s • w * θ.E)) := by
        rw [eq_sub_of_add_eq' e, Matrix.mul_sub, smul_sub, Matrix.smul_mul, Matrix.smul_mul,
          Matrix.smul_mul, Matrix.mul_assoc]
      rw [e']
      exact hB _
    exact (sub_eq_zero.1 (eq_zero_of_forall_mul_eq_zero_ss hM)).symm
  refine ⟨Y, hYt, hEeq, hDeq, fun x => ?_⟩
  -- so `S(x) = 0` for every `x`
  have e := hk x
  rw [hEeq, ← Matrix.mul_assoc] at e
  exact add_eq_left.1 e

end Skips
