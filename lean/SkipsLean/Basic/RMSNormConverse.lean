import SkipsLean.Basic.RMSNorm

/-!
# Which changes of basis RMSNorm lets through

Paper (dimension paper): Lemma A.1, the direction "only if". If a read can undo the change of
basis `G` behind RMSNorm, that is, if `N_ε(vG) = N_ε(v) M` for one matrix `M` and all nonzero rows
`v`, then `G` is orthogonal for `ε > 0`, and a positive multiple of an orthogonal matrix for
`ε = 0`; in both cases `M` is the orthogonal factor.
-/

namespace Skips

open Matrix

variable {d : Type*} [Fintype d] [DecidableEq d]

/-! ### Helpers on rows -/

omit [DecidableEq d] in
/-- Helper: a squared norm `‖v‖² = v ⬝ᵥ v` is nonnegative. -/
private theorem dotProduct_self_nonneg' (v : d → ℝ) : 0 ≤ v ⬝ᵥ v :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)

omit [DecidableEq d] in
/-- Helper: the squared norm of a nonzero row is positive. -/
private theorem dotProduct_self_pos' {v : d → ℝ} (hv : v ≠ 0) : 0 < v ⬝ᵥ v :=
  lt_of_le_of_ne (dotProduct_self_nonneg' v) (Ne.symm (dotProduct_self_eq_zero.not.mpr hv))

omit [DecidableEq d] in
/-- Helper: a nonzero row has a coordinate, so `d_model > 0`. -/
private theorem card_pos_of_ne_zero {v : d → ℝ} (hv : v ≠ 0) : (0 : ℝ) < Fintype.card d := by
  obtain ⟨i, -⟩ := Function.ne_iff.mp hv
  exact_mod_cast Fintype.card_pos_iff.mpr ⟨i⟩

omit [DecidableEq d] in
/-- Helper: the RMS denominator `sqrt (‖v‖² / d_model + ε)` of a nonzero row is positive for
`ε ≥ 0`. -/
private theorem rms_sqrt_pos {ε : ℝ} (hε : 0 ≤ ε) {v : d → ℝ} (hv : v ≠ 0) :
    0 < Real.sqrt ((v ⬝ᵥ v) / (Fintype.card d : ℝ) + ε) := by
  have h1 := dotProduct_self_pos' hv
  have h2 := card_pos_of_ne_zero hv
  exact Real.sqrt_pos.mpr (by positivity)

omit [Fintype d] in
/-- Helper: the basis row `e_i` is nonzero. -/
private theorem single_one_ne_zero (i : d) : (Pi.single i (1 : ℝ) : d → ℝ) ≠ 0 := by
  intro h0
  have h1 := congrFun h0 i
  rw [Pi.single_eq_same, Pi.zero_apply] at h1
  exact one_ne_zero h1

/-- Helper: an invertible matrix sends nonzero rows to nonzero rows. -/
private theorem vecMul_GL_ne_zero (G : GL d ℝ) {v : d → ℝ} (hv : v ≠ 0) :
    v ᵥ* (G : Matrix d d ℝ) ≠ 0 := by
  intro h0
  apply hv
  -- `v = (vG) G⁻¹ = 0`
  have hvG : v ᵥ* (G : Matrix d d ℝ) ᵥ* (↑G⁻¹ : Matrix d d ℝ) = v := by
    rw [Matrix.vecMul_vecMul, Units.mul_inv, Matrix.vecMul_one]
  rw [← hvG, h0, Matrix.zero_vecMul]

omit [Fintype d] [DecidableEq d] in
/-- Helper: from `α • x = β • y` with `β ≠ 0`, the row `y` is the multiple `(β⁻¹ α) • x`. -/
private theorem eq_smul_of_smul_eq_smul {α β : ℝ} (hβ : β ≠ 0) {x y : d → ℝ}
    (hxy : α • x = β • y) : y = (β⁻¹ * α) • x := by
  rw [mul_smul, hxy, smul_smul, inv_mul_cancel₀ hβ, one_smul]

/-! ### Norm-preserving matrices and matrices with all rows as eigenvectors -/

/-- Helper: a matrix that preserves the squared norm of every row is orthogonal. -/
private theorem orthogonal_of_dotProduct_vecMul_self {M : Matrix d d ℝ}
    (h : ∀ v : d → ℝ, (v ᵥ* M) ⬝ᵥ (v ᵥ* M) = v ⬝ᵥ v) : M ∈ Matrix.orthogonalGroup d ℝ := by
  -- polarization: `M` preserves all dot products
  have hpol : ∀ v w : d → ℝ, (v ᵥ* M) ⬝ᵥ (w ᵥ* M) = v ⬝ᵥ w := by
    intro v w
    have hvw := h (v + w)
    simp only [Matrix.add_vecMul, add_dotProduct, dotProduct_add, h v, h w] at hvw
    linarith [dotProduct_comm (w ᵥ* M) (v ᵥ* M), dotProduct_comm w v]
  -- entry `(i, j)` of `M Mᵀ` is the dot product of the rows `e_i M` and `e_j M`
  rw [mem_orthogonalGroup_iff d ℝ]
  ext i j
  have hij := hpol (Pi.single i 1) (Pi.single j 1)
  rw [single_one_vecMul, single_one_vecMul, single_dotProduct, one_mul, Pi.single_apply] at hij
  rw [Matrix.one_apply, ← hij]
  rfl

/-- Helper: if every row is a left eigenvector of `N`, then `N` is a multiple of `1`. -/
private theorem eq_smul_one_of_vecMul_eq_smul {N : Matrix d d ℝ}
    (h : ∀ v : d → ℝ, ∃ r : ℝ, v ᵥ* N = r • v) (i₀ : d) :
    N = N i₀ i₀ • (1 : Matrix d d ℝ) := by
  -- `e_i N = r e_i`: the row `i` of `N` vanishes off the diagonal
  have hoff : ∀ i j, i ≠ j → N i j = 0 := by
    intro i j hij
    obtain ⟨r, hr⟩ := h (Pi.single i 1)
    have hj := congrFun hr j
    rw [single_one_vecMul, Matrix.row_apply, Pi.smul_apply, Pi.single_eq_of_ne hij.symm,
      smul_zero] at hj
    exact hj
  -- `(e_i + e_j) N = μ (e_i + e_j)`: the diagonal entries at `i` and `j` both equal `μ`
  have hdiag : ∀ i j, N i i = N j j := by
    intro i j
    by_cases hij : i = j
    · rw [hij]
    obtain ⟨μ, hμ⟩ := h (Pi.single i 1 + Pi.single j 1)
    rw [Matrix.add_vecMul, single_one_vecMul, single_one_vecMul] at hμ
    have hi := congrFun hμ i
    have hj := congrFun hμ j
    simp only [Pi.add_apply, Pi.smul_apply, Matrix.row_apply, Pi.single_eq_same,
      Pi.single_eq_of_ne hij, Pi.single_eq_of_ne (Ne.symm hij), smul_eq_mul, add_zero, zero_add,
      mul_one] at hi hj
    linarith [hoff i j hij, hoff j i (Ne.symm hij)]
  ext i j
  rw [Matrix.smul_apply, smul_eq_mul]
  by_cases hij : i = j
  · subst hij
    rw [Matrix.one_apply_eq, mul_one, hdiag i i₀]
  · rw [Matrix.one_apply_ne hij, mul_zero, hoff i j hij]

/-! ### Facts about `rmsRow` -/

omit [DecidableEq d] in
/-- Helper: for `ε = 0` every nonzero row is normalized to squared norm `d_model`. -/
private theorem rmsRow_zero_dotProduct_self {w : d → ℝ} (hw : w ≠ 0) :
    rmsRow 0 w ⬝ᵥ rmsRow 0 w = Fintype.card d := by
  have hw2 := dotProduct_self_pos' hw
  have hn := card_pos_of_ne_zero hw
  unfold rmsRow
  rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc, ← mul_inv,
    Real.mul_self_sqrt (by positivity), add_zero, inv_div, div_mul_cancel₀ _ hw2.ne']

omit [DecidableEq d] in
/-- Helper: RMSNorm of the doubled row `2w`, with `‖2w‖² / d_model = 4 (‖w‖² / d_model)`. -/
private theorem rmsRow_two_smul (ε : ℝ) (w : d → ℝ) :
    rmsRow ε ((2 : ℝ) • w)
      = (2 : ℝ) • ((Real.sqrt (4 * ((w ⬝ᵥ w) / (Fintype.card d : ℝ)) + ε))⁻¹ • w) := by
  unfold rmsRow
  rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, smul_comm,
    show (2 : ℝ) * (2 * (w ⬝ᵥ w)) / (Fintype.card d : ℝ)
      = 4 * ((w ⬝ᵥ w) / (Fintype.card d : ℝ)) by ring]

omit [Fintype d] [DecidableEq d] in
/-- Helper (`ε > 0`): the relations of RMSNorm at a row and at its double force `a = b`, where
`a`, `b` are the scaled squared norms `‖vG‖² / d_model` and `‖v‖² / d_model`. -/
private theorem eq_of_rms_relations {ε a b : ℝ} (hε : 0 < ε) (ha : 0 ≤ a) (hb : 0 ≤ b)
    {x y : d → ℝ} (hx : x ≠ 0)
    (h1 : (Real.sqrt (a + ε))⁻¹ • x = (Real.sqrt (b + ε))⁻¹ • y)
    (h2 : (Real.sqrt (4 * a + ε))⁻¹ • x = (Real.sqrt (4 * b + ε))⁻¹ • y) : a = b := by
  have hS : ∀ t : ℝ, 0 ≤ t → 0 < Real.sqrt (t + ε) := fun t ht => Real.sqrt_pos.mpr (by linarith)
  have ha4 : 0 ≤ 4 * a := by linarith
  have hb4 : 0 ≤ 4 * b := by linarith
  -- both relations write `y` as a multiple of `x ≠ 0`, so the two factors agree
  have e1 := eq_smul_of_smul_eq_smul (inv_pos.mpr (hS b hb)).ne' h1
  have e2 := eq_smul_of_smul_eq_smul (inv_pos.mpr (hS (4 * b) hb4)).ne' h2
  have e := (smul_left_inj hx).mp (e1.symm.trans e2)
  -- `sqrt (b + ε) * sqrt (4a + ε) = sqrt (4b + ε) * sqrt (a + ε)`
  rw [inv_inv, inv_inv, ← div_eq_mul_inv, ← div_eq_mul_inv,
    div_eq_div_iff (hS a ha).ne' (hS (4 * a) ha4).ne',
    ← Real.sqrt_mul (show (0 : ℝ) ≤ b + ε by linarith) (4 * a + ε),
    ← Real.sqrt_mul (show (0 : ℝ) ≤ 4 * b + ε by linarith) (a + ε)] at e
  have e' := (Real.sqrt_inj (mul_nonneg (by linarith) (by linarith))
    (mul_nonneg (by linarith) (by linarith))).mp e
  -- `(b + ε)(4a + ε) = (4b + ε)(a + ε)` means `3ε (a - b) = 0`
  have h3 : (3 * ε) * (a - b) = 0 := by linear_combination e'
  have h4 := (mul_eq_zero.mp h3).resolve_left (by positivity)
  linarith

/-- **Lemma A.1, "only if", for `ε > 0`.** -/
theorem orthogonal_of_rmsRow_vecMul {ε : ℝ} (hε : 0 < ε) (G : GL d ℝ) (M : Matrix d d ℝ)
    (h : ∀ v : d → ℝ, v ≠ 0 → rmsRow ε (v ᵥ* (G : Matrix d d ℝ)) = rmsRow ε v ᵥ* M) :
    (G : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ ∧ M = (G : Matrix d d ℝ) := by
  -- for a nonzero row `v`: `vM = vG` and `‖vG‖² = ‖v‖²`
  have key : ∀ v : d → ℝ, v ≠ 0 → v ᵥ* M = v ᵥ* (G : Matrix d d ℝ) ∧
      (v ᵥ* (G : Matrix d d ℝ)) ⬝ᵥ (v ᵥ* (G : Matrix d d ℝ)) = v ⬝ᵥ v := by
    intro v hv
    have hn := card_pos_of_ne_zero hv
    -- the relation at `v`
    have h1 := h v hv
    unfold rmsRow at h1
    rw [Matrix.smul_vecMul] at h1
    -- the relation at `2v`, divided by `2`
    have h2 := h ((2 : ℝ) • v) (smul_ne_zero two_ne_zero hv)
    simp only [Matrix.smul_vecMul, rmsRow_two_smul] at h2
    rw [smul_right_inj two_ne_zero] at h2
    -- together they give `‖vG‖² / d_model = ‖v‖² / d_model`
    have hab := eq_of_rms_relations hε (div_nonneg (dotProduct_self_nonneg' _) hn.le)
      (div_nonneg (dotProduct_self_nonneg' _) hn.le) (vecMul_GL_ne_zero G hv) h1 h2
    refine ⟨?_, (div_left_inj₀ hn.ne').mp hab⟩
    -- with equal norms the relation at `v` reads `c • vG = c • vM`
    rw [hab] at h1
    exact ((smul_right_inj (inv_pos.mpr (rms_sqrt_pos hε.le hv)).ne').mp h1).symm
  refine ⟨orthogonal_of_dotProduct_vecMul_self fun v => ?_,
    Matrix.ext_of_single_vecMul fun i => (key _ (single_one_ne_zero i)).1⟩
  by_cases hv : v = 0
  · rw [hv, Matrix.zero_vecMul]
  · exact (key v hv).2

/-- **Lemma A.1, "only if", for `ε = 0`.** -/
theorem conformal_of_rmsRow_zero_vecMul (G : GL d ℝ) (M : Matrix d d ℝ)
    (h : ∀ v : d → ℝ, v ≠ 0 → rmsRow 0 (v ᵥ* (G : Matrix d d ℝ)) = rmsRow 0 v ᵥ* M) :
    M ∈ Matrix.orthogonalGroup d ℝ ∧ ∃ c : ℝ, 0 < c ∧ (G : Matrix d d ℝ) = c • M := by
  -- Step 1: `M` preserves squared norms, since both sides have squared norm `d_model`
  have hnorm : ∀ v : d → ℝ, (v ᵥ* M) ⬝ᵥ (v ᵥ* M) = v ⬝ᵥ v := by
    intro v
    by_cases hv : v = 0
    · rw [hv, Matrix.zero_vecMul]
    have e1 := rmsRow_zero_dotProduct_self (vecMul_GL_ne_zero G hv)
    have e2 := rmsRow_zero_dotProduct_self hv
    rw [h v hv] at e1
    unfold rmsRow at e1 e2
    rw [Matrix.smul_vecMul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul] at e1
    rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul] at e2
    have hk := (inv_pos.mpr (rms_sqrt_pos le_rfl hv)).ne'
    exact mul_left_cancel₀ hk (mul_left_cancel₀ hk (e1.trans e2.symm))
  have hM : M ∈ Matrix.orthogonalGroup d ℝ := orthogonal_of_dotProduct_vecMul_self hnorm
  refine ⟨hM, ?_⟩
  -- Step 2: every nonzero row is a left eigenvector of `N = G Mᵀ`, with a positive eigenvalue
  have hMMt : M * Mᵀ = 1 := (mem_orthogonalGroup_iff d ℝ).mp hM
  have heig : ∀ v : d → ℝ, v ≠ 0 →
      ∃ r : ℝ, 0 < r ∧ v ᵥ* ((G : Matrix d d ℝ) * Mᵀ) = r • v := by
    intro v hv
    have hsx := rms_sqrt_pos le_rfl (vecMul_GL_ne_zero G hv)
    have hsv := rms_sqrt_pos le_rfl hv
    have hA := h v hv
    unfold rmsRow at hA
    rw [Matrix.smul_vecMul] at hA
    -- `vG = r • vM` with `r = sqrt (‖vG‖² / d) / sqrt (‖v‖² / d) > 0`
    obtain ⟨r, hr, hxr⟩ : ∃ r : ℝ, 0 < r ∧ v ᵥ* (G : Matrix d d ℝ) = r • (v ᵥ* M) :=
      ⟨_, mul_pos (inv_pos.mpr (inv_pos.mpr hsx)) (inv_pos.mpr hsv),
        eq_smul_of_smul_eq_smul (inv_pos.mpr hsx).ne' hA.symm⟩
    refine ⟨r, hr, ?_⟩
    rw [← Matrix.vecMul_vecMul, hxr, Matrix.smul_vecMul, Matrix.vecMul_vecMul, hMMt,
      Matrix.vecMul_one]
  -- Step 3: so `G Mᵀ = c • 1` with `c > 0`, and `G = G Mᵀ M = c • M`
  rcases isEmpty_or_nonempty d with hd | ⟨⟨i₀⟩⟩
  · -- no coordinates: every matrix equals `1 • M`
    exact ⟨1, one_pos, Matrix.ext fun i j => isEmptyElim i⟩
  have hall : ∀ v : d → ℝ, ∃ r : ℝ, v ᵥ* ((G : Matrix d d ℝ) * Mᵀ) = r • v := by
    intro v
    by_cases hv : v = 0
    · exact ⟨0, by rw [hv, Matrix.zero_vecMul, smul_zero]⟩
    · obtain ⟨r, -, hr⟩ := heig v hv
      exact ⟨r, hr⟩
  have hN := eq_smul_one_of_vecMul_eq_smul hall i₀
  -- the scalar is the eigenvalue of `e_{i₀}`, hence positive
  have hpos : 0 < ((G : Matrix d d ℝ) * Mᵀ) i₀ i₀ := by
    obtain ⟨r, hr, hre⟩ := heig (Pi.single i₀ 1) (single_one_ne_zero i₀)
    have hi := congrFun hre i₀
    rw [single_one_vecMul, Matrix.row_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul,
      mul_one] at hi
    rw [hi]
    exact hr
  generalize ((G : Matrix d d ℝ) * Mᵀ) i₀ i₀ = c at hN hpos
  refine ⟨c, hpos, ?_⟩
  have hMtM : Mᵀ * M = 1 := (mem_orthogonalGroup_iff' d ℝ).mp hM
  calc (G : Matrix d d ℝ) = (G : Matrix d d ℝ) * Mᵀ * M := by
        rw [Matrix.mul_assoc, hMtM, Matrix.mul_one]
    _ = c • M := by rw [hN, Matrix.smul_mul, Matrix.one_mul]

end Skips
