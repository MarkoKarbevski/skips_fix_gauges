import SkipsLean.OneBlock.LearnedSkip

/-!
# One block with learned skips under pre-RMSNorm, at the skip `0`

Paper (skips paper): Theorem 4.6 (ii) and Theorem B.1 (iii) (the learned skip); the definitions and
the route are in `OneBlock/LearnedSkip.lean`. This file has the step at the skip `A = 0`, which is
not in the paper: there the network is the skipless network `x ↦ N_ε(f(N_ε(x E) W_read) W_write) D`,
and a flat direction `(η, a)` of the family with the skips `ι v` has `a = 0`. (For the inputs `t x`
with all rows of `x E` nonzero, as `t → ∞`: the input `N_ε(t x E)` of the block converges, so the
hidden state `g(t x)` and its derivative along `η` stay bounded, while the derivative along `a` is
`t · DN_ε(g(t x)) (x E (ι a)) D`; so `DN_ε(g_∞) (x E (ι a)) D = 0`; `D` has rank `d`, the derivative
of `N_ε` is injective for `ε > 0`, `E` has rank `d` and `ι` is injective.) So the flat directions
are those of the skipless network, and the functional dimension is that of the skipless network
plus `dim V` (`funDimSkips_add_finrank_flatSkips`, `funDim_add_finrank_flat'`).
-/

namespace Skips

open Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-! ### RMSNorm with `ε > 0` (copies of the lemmas of `Depth/SuffixRMS.lean`, not imported here) -/

omit [DecidableEq d] in
/-- Helper: `‖v‖² / d + ε > 0` for `ε > 0`. -/
private theorem dotProduct_self_div_add_pos_lsz {ε : ℝ} (hε : 0 < ε) (v : d → ℝ) :
    0 < (v ⬝ᵥ v) / (Fintype.card d : ℝ) + ε := by
  have : 0 ≤ (v ⬝ᵥ v) / (Fintype.card d : ℝ) :=
    div_nonneg (Finset.sum_nonneg fun j _ => mul_self_nonneg (v j)) (Nat.cast_nonneg _)
  linarith

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: with the elementwise norm, the derivative of a matrix-valued function of one real
variable is taken entry by entry. -/
private theorem hasDerivAt_matrix_lsz {m n : Type*} [Fintype m] [Fintype n]
    {f : ℝ → Matrix m n ℝ} {f' : Matrix m n ℝ} {x : ℝ}
    (h : ∀ i j, HasDerivAt (fun τ => f τ i j) (f' i j) x) : HasDerivAt f f' x :=
  hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 (h i)

/-- Helper: the derivative of RMSNorm with `ε > 0`, row by row: with `s_t = √(‖h_t‖²/d + ε)`,
`(𝐃N_ε(h) U)_t = U_t / s_t - (⟨h_t, U_t⟩/d) h_t / s_t³` (`fderiv_rmsNorm_apply`). -/
private theorem fderiv_rmsNorm_apply_lsz {ε : ℝ} (hε : 0 < ε) (h U : Matrix T d ℝ) :
    fderiv ℝ (rmsNorm ε : Matrix T d ℝ → Matrix T d ℝ) h U
      = Matrix.of fun t =>
          (Real.sqrt ((h t ⬝ᵥ h t) / (Fintype.card d : ℝ) + ε))⁻¹ • U t
            - ((h t ⬝ᵥ U t) / (Fintype.card d : ℝ)
                * (Real.sqrt ((h t ⬝ᵥ h t) / (Fintype.card d : ℝ) + ε))⁻¹ ^ 3) • h t := by
  -- the line `τ ↦ h + τ U` passes through `h` with velocity `U`
  have hline : HasDerivAt (fun τ : ℝ => h + τ • U) U 0 := by
    have h1 := ((hasDerivAt_id (0 : ℝ)).smul_const U).const_add h
    rw [one_smul] at h1
    exact h1
  have h0 : h = h + (0 : ℝ) • U := by rw [zero_smul, add_zero]
  -- the chain rule: `τ ↦ N_ε(h + τ U)` has the derivative `𝐃N_ε(h) U` at `0`
  have hF := ((differentiable_rmsNorm (T := T) (d := d) hε) h).hasFDerivAt.comp_hasDerivAt_of_eq
    (0 : ℝ) hline h0
  -- the same derivative, entry by entry: entry `(t, i)` is `q(τ)^{-1/2} (h_{ti} + τ U_{ti})`
  refine hF.unique (hasDerivAt_matrix_lsz fun t i => ?_)
  have hpos := dotProduct_self_div_add_pos_lsz hε (h t)
  have hdot : HasDerivAt (fun τ : ℝ => (h t + τ • U t) ⬝ᵥ (h t + τ • U t))
      (2 * (h t ⬝ᵥ U t)) 0 := by
    have e : (fun τ : ℝ => (h t + τ • U t) ⬝ᵥ (h t + τ • U t))
        = fun τ => h t ⬝ᵥ h t + τ * (2 * (h t ⬝ᵥ U t)) + τ * τ * (U t ⬝ᵥ U t) := by
      funext τ
      simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul,
        dotProduct_comm (U t) (h t)]
      ring
    rw [e]
    exact hasDerivAt_quad _ _ _
  have hq := (hdot.div_const (Fintype.card d : ℝ)).add_const ε
  have hs : 0 < Real.sqrt ((h t ⬝ᵥ h t) / (Fintype.card d : ℝ) + ε) := Real.sqrt_pos.2 hpos
  have hsq := hq.sqrt (by simp only [zero_smul, add_zero]; exact hpos.ne')
  have hinv := hsq.inv (by simp only [zero_smul, add_zero]; exact hs.ne')
  have hent : HasDerivAt (fun τ : ℝ => h t i + τ * U t i) (U t i) 0 := by
    have h1 := ((hasDerivAt_id (0 : ℝ)).mul_const (U t i)).const_add (h t i)
    rw [one_mul] at h1
    exact h1
  show HasDerivAt (fun τ : ℝ => (Real.sqrt ((h t + τ • U t) ⬝ᵥ (h t + τ • U t)
      / (Fintype.card d : ℝ) + ε))⁻¹ * (h t i + τ * U t i))
    ((Real.sqrt ((h t ⬝ᵥ h t) / (Fintype.card d : ℝ) + ε))⁻¹ * U t i
      - ((h t ⬝ᵥ U t) / (Fintype.card d : ℝ)
        * (Real.sqrt ((h t ⬝ᵥ h t) / (Fintype.card d : ℝ) + ε))⁻¹ ^ 3) * h t i) 0
  refine (hinv.mul hent).congr_deriv ?_
  simp only [Pi.inv_apply, zero_smul, add_zero, zero_mul]
  ring

/-- Helper: for `ε > 0` the derivative of RMSNorm is injective at every `h`
(`injective_fderiv_rmsNorm`; row by row, `𝐃N_ε(h) U = 0` says `U_t = c h_t`, and the product with
`h_t` then gives `ε ⟨h_t, U_t⟩ = 0`). -/
private theorem injective_fderiv_rmsNorm_lsz {ε : ℝ} (hε : 0 < ε) (h : Matrix T d ℝ) :
    Function.Injective (fderiv ℝ (rmsNorm ε : Matrix T d ℝ → Matrix T d ℝ) h) := by
  refine (injective_iff_map_eq_zero _).2 fun U hU => ?_
  rw [fderiv_rmsNorm_apply_lsz hε] at hU
  -- every row `U_t` vanishes
  have hUt : ∀ t, U t = 0 := by
    intro t
    have hpos := dotProduct_self_div_add_pos_lsz hε (h t)
    have hs : 0 < Real.sqrt ((h t ⬝ᵥ h t) / (Fintype.card d : ℝ) + ε) := Real.sqrt_pos.2 hpos
    have hs2 : Real.sqrt ((h t ⬝ᵥ h t) / (Fintype.card d : ℝ) + ε) ^ 2
        = (h t ⬝ᵥ h t) / (Fintype.card d : ℝ) + ε := Real.sq_sqrt hpos.le
    have hrow : (Real.sqrt ((h t ⬝ᵥ h t) / (Fintype.card d : ℝ) + ε))⁻¹ • U t
        - ((h t ⬝ᵥ U t) / (Fintype.card d : ℝ)
          * (Real.sqrt ((h t ⬝ᵥ h t) / (Fintype.card d : ℝ) + ε))⁻¹ ^ 3) • h t = 0 :=
      congrFun hU t
    generalize Real.sqrt ((h t ⬝ᵥ h t) / (Fintype.card d : ℝ) + ε) = s at hs hs2 hrow
    -- its product with `h_t`: `r / s - (r/d) ‖h_t‖² / s³ = ε r / s³` with `r = ⟨h_t, U_t⟩`
    have hdot := congrArg (fun w => h t ⬝ᵥ w) hrow
    simp only [dotProduct_sub, dotProduct_smul, smul_eq_mul, dotProduct_zero] at hdot
    have hu : s⁻¹ ^ 2 * ((h t ⬝ᵥ h t) / (Fintype.card d : ℝ) + ε) = 1 := by
      rw [← hs2, inv_pow, inv_mul_cancel₀ (pow_ne_zero 2 hs.ne')]
    have hr : h t ⬝ᵥ U t = 0 := by
      have e : s⁻¹ ^ 3 * (ε * (h t ⬝ᵥ U t)) = 0 := by
        linear_combination hdot + (s⁻¹ * (h t ⬝ᵥ U t)) * hu
      have e' := (mul_eq_zero.1 e).resolve_left (pow_ne_zero 3 (inv_ne_zero hs.ne'))
      exact (mul_eq_zero.1 e').resolve_left hε.ne'
    rw [hr, zero_div, zero_mul, zero_smul, sub_zero] at hrow
    exact (smul_eq_zero.1 hrow).resolve_left (inv_ne_zero hs.ne')
  ext t i
  rw [hUt t]
  rfl

omit [DecidableEq d] in
/-- Helper: RMSNorm with `ε > 0` is continuously differentiable (each entry is
`(√(‖h_t‖²/d + ε))⁻¹ h_{ti}`, and the root is taken at a positive number). -/
private theorem contDiff_rmsNorm_lsz {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ 1 (rmsNorm ε : Matrix T d ℝ → Matrix T d ℝ) := by
  refine contDiff_pi.2 fun t => contDiff_pi.2 fun i => ?_
  have hrow : ContDiff ℝ 1 fun h : Matrix T d ℝ => h t := contDiff_pi.1 contDiff_id t
  have hent : ContDiff ℝ 1 fun h : Matrix T d ℝ => h t i := contDiff_pi.1 hrow i
  have hq : ContDiff ℝ 1 fun h : Matrix T d ℝ => (h t ⬝ᵥ h t) / (Fintype.card d : ℝ) + ε := by
    simp only [dotProduct]
    exact ((ContDiff.sum fun j _ => (contDiff_pi.1 hrow j).mul (contDiff_pi.1 hrow j)).div_const
      _).add contDiff_const
  refine contDiff_iff_contDiffAt.2 fun h => ?_
  have hpos := dotProduct_self_div_add_pos_lsz hε (h t)
  show ContDiffAt ℝ 1 (fun h : Matrix T d ℝ =>
    (Real.sqrt ((h t ⬝ᵥ h t) / (Fintype.card d : ℝ) + ε))⁻¹ * h t i) h
  exact ((hq.contDiffAt.sqrt hpos.ne').inv (Real.sqrt_pos.2 hpos).ne').mul hent.contDiffAt

/-! ### Rays `x = s w`, `s → ∞` (copies of helpers of `OneBlock/ResidualRMSSteps.lean`) -/

omit [DecidableEq d] in
/-- Helper: `0 ≤ ⟨v, v⟩`. -/
private theorem dot_self_nonneg_lsz (v : d → ℝ) : 0 ≤ v ⬝ᵥ v :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)

/-- Helper: `c(v, y) = (‖v‖²/d + ε y²)^{-1/2}`; along the ray `s v`, `N_ε(s v) = c(v, 1/s) v`. -/
private noncomputable def cLsz (ε : ℝ) (v : d → ℝ) (y : ℝ) : ℝ :=
  (Real.sqrt ((v ⬝ᵥ v) / (Fintype.card d : ℝ) + ε * y ^ 2))⁻¹

/-- Helper: the matrix with rows `c(a_t, y) a_t`, which is `N_ε(s a)` at `y = 1/s`. -/
private noncomputable def nLsz (ε : ℝ) (a : Matrix T d ℝ) (y : ℝ) : Matrix T d ℝ :=
  Matrix.of fun t => cLsz ε (a t) y • a t

/-- Helper: the matrix that is `𝐃N_ε(s a)(s b)` at `y = 1/s`. -/
private noncomputable def dnLsz (ε : ℝ) (a b : Matrix T d ℝ) (y : ℝ) : Matrix T d ℝ :=
  Matrix.of fun t => cLsz ε (a t) y • b t
    - ((a t ⬝ᵥ b t) / (Fintype.card d : ℝ) * cLsz ε (a t) y ^ 3) • a t

omit [DecidableEq d] in
/-- Helper: `(‖s v‖²/d + ε)^{-1/2} = c(v, 1/s) / s` for `s > 0`. -/
private theorem inv_sqrt_smul_lsz {ε s : ℝ} (hs : 0 < s) (v : d → ℝ) :
    (Real.sqrt ((s • v) ⬝ᵥ (s • v) / (Fintype.card d : ℝ) + ε))⁻¹ = cLsz ε v s⁻¹ * s⁻¹ := by
  unfold cLsz
  have e : (s • v) ⬝ᵥ (s • v) / (Fintype.card d : ℝ) + ε
      = s ^ 2 * ((v ⬝ᵥ v) / (Fintype.card d : ℝ) + ε * s⁻¹ ^ 2) := by
    rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    field_simp
  rw [e, Real.sqrt_mul (sq_nonneg s), Real.sqrt_sq hs.le, mul_inv, mul_comm]

omit [Fintype T] [DecidableEq d] in
/-- Helper: `N_ε(s a) = n(1/s)` for `s > 0`. -/
private theorem rmsNorm_smul_lsz {ε s : ℝ} (hs : 0 < s) (a : Matrix T d ℝ) :
    rmsNorm ε (s • a) = nLsz ε a s⁻¹ := by
  funext t i
  show (Real.sqrt ((s • a t) ⬝ᵥ (s • a t) / (Fintype.card d : ℝ) + ε))⁻¹ * (s * a t i)
    = cLsz ε (a t) s⁻¹ * a t i
  rw [inv_sqrt_smul_lsz hs, mul_assoc, inv_mul_cancel_left₀ hs.ne']

/-- Helper: `𝐃N_ε(s a)(s b) = dn(1/s)` for `s > 0`. -/
private theorem fderiv_rmsNorm_smul_lsz {ε s : ℝ} (hε : 0 < ε) (hs : 0 < s)
    (a b : Matrix T d ℝ) :
    fderiv ℝ (rmsNorm ε : Matrix T d ℝ → Matrix T d ℝ) (s • a) (s • b) = dnLsz ε a b s⁻¹ := by
  rw [fderiv_rmsNorm_apply_lsz hε]
  funext t i
  show (Real.sqrt ((s • a t) ⬝ᵥ (s • a t) / (Fintype.card d : ℝ) + ε))⁻¹ * (s * b t i)
      - ((s • a t) ⬝ᵥ (s • b t) / (Fintype.card d : ℝ)
        * (Real.sqrt ((s • a t) ⬝ᵥ (s • a t) / (Fintype.card d : ℝ) + ε))⁻¹ ^ 3) * (s * a t i)
    = cLsz ε (a t) s⁻¹ * b t i
      - ((a t ⬝ᵥ b t) / (Fintype.card d : ℝ) * cLsz ε (a t) s⁻¹ ^ 3) * a t i
  rw [inv_sqrt_smul_lsz hs, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  field_simp

omit [DecidableEq d] in
/-- Helper: `y ↦ c(v, y)` is continuous at `0` if `v ≠ 0`. -/
private theorem continuousAt_cLsz {ε : ℝ} {v : d → ℝ} (hv : v ≠ 0) :
    ContinuousAt (cLsz ε v) 0 := by
  have hpos : 0 < (v ⬝ᵥ v) / (Fintype.card d : ℝ) := by
    have h1 : 0 < v ⬝ᵥ v :=
      lt_of_le_of_ne (dot_self_nonneg_lsz v) (Ne.symm (mt dotProduct_self_eq_zero.1 hv))
    have h2 : (0 : ℝ) < Fintype.card d := by
      obtain ⟨i, -⟩ := Function.ne_iff.1 hv
      exact_mod_cast Fintype.card_pos_iff.2 ⟨i⟩
    positivity
  have hc : Continuous fun y : ℝ => Real.sqrt ((v ⬝ᵥ v) / (Fintype.card d : ℝ) + ε * y ^ 2) := by
    fun_prop
  refine hc.continuousAt.inv₀ ?_
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, add_zero]
  exact (Real.sqrt_pos.2 hpos).ne'

omit [Fintype T] [DecidableEq d] in
/-- Helper: `n` and `dn` are continuous at `0` if every row of `a` is nonzero. -/
private theorem continuousAt_nLsz_dnLsz {ε : ℝ} {a : Matrix T d ℝ} (ha : ∀ t, a t ≠ 0)
    (b : Matrix T d ℝ) : ContinuousAt (nLsz ε a) 0 ∧ ContinuousAt (dnLsz ε a b) 0 := by
  constructor
  · refine continuousAt_pi.2 fun t => continuousAt_pi.2 fun i => ?_
    show ContinuousAt (fun y => cLsz ε (a t) y * a t i) 0
    exact (continuousAt_cLsz (ha t)).mul continuousAt_const
  · refine continuousAt_pi.2 fun t => continuousAt_pi.2 fun i => ?_
    show ContinuousAt (fun y => cLsz ε (a t) y * b t i
      - ((a t ⬝ᵥ b t) / (Fintype.card d : ℝ) * cLsz ε (a t) y ^ 3) * a t i) 0
    exact ((continuousAt_cLsz (ha t)).mul continuousAt_const).sub
      ((continuousAt_const.mul ((continuousAt_cLsz (ha t)).pow 3)).mul continuousAt_const)

/-! ### Linear algebra (copies of helpers of `OneBlock/ResidualRMSSteps.lean`) -/

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: a matrix `Z` with `u Z = 0` for every row vector `u` is `0`. -/
private theorem eq_zero_of_vecMul_lsz {m n : Type*} [Fintype m] [DecidableEq m]
    {Z : Matrix m n ℝ} (h : ∀ u : m → ℝ, u ᵥ* Z = 0) : Z = 0 := by
  ext i j
  have := congrFun (h (Pi.single i 1)) j
  rwa [Matrix.single_one_vecMul, Matrix.row_apply] at this

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dOut] in
/-- Helper: row `t` of `w M`, for the input `w` whose rows all equal `w₀`, is `w₀ M`. -/
private theorem constRows_mul_lsz (w₀ : dIn → ℝ) (M : Matrix dIn d ℝ) (t : T) :
    ((Matrix.of fun _ : T => w₀) * M) t = w₀ ᵥ* M := by
  rw [Matrix.mul_apply_eq_vecMul]
  rfl

omit [Fintype T] [DecidableEq d] [Fintype dOut] in
/-- Helper: if `E` has rank `d`, a property of row vectors that holds at `0` and at the rows of
`w E` whenever all of them are nonzero holds for every row vector (every `u` is `w₀ E`). -/
private theorem forall_of_rows_lsz [Nonempty T] {E : Matrix dIn d ℝ}
    (hE : E.rank = Fintype.card d) {P : (d → ℝ) → Prop} (h0 : P 0)
    (h : ∀ w : Matrix T dIn ℝ, (∀ t, (w * E) t ≠ 0) → ∀ t, P ((w * E) t)) (u : d → ℝ) : P u := by
  by_cases hu : u = 0
  · rw [hu]
    exact h0
  obtain ⟨w₀, hw₀⟩ := Matrix.vecMul_surjective_iff_rank_eq_card.2 hE u
  have hrow : ∀ t : T, ((Matrix.of fun _ : T => w₀) * E) t = u := fun t =>
    (constRows_mul_lsz w₀ E t).trans hw₀
  have := h _ (fun t => by rw [hrow]; exact hu) (Classical.arbitrary T)
  rwa [hrow] at this

/-! ### Derivatives along lines -/

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the product rule for matrices depending on one real variable. -/
private theorem hasDerivAt_mul_lsz {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
    {P : ℝ → Matrix m n ℝ} {Q : ℝ → Matrix n p ℝ} {P' P0 : Matrix m n ℝ} {Q' Q0 : Matrix n p ℝ}
    {τ : ℝ} (hP : HasDerivAt P P' τ) (hQ : HasDerivAt Q Q' τ) (hP0 : P τ = P0) (hQ0 : Q τ = Q0) :
    HasDerivAt (fun s => P s * Q s) (P' * Q0 + P0 * Q') τ := by
  subst hP0 hQ0
  refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => ?_
  have hPe : ∀ k, HasDerivAt (fun s => P s i k) (P' i k) τ := fun k =>
    hasDerivAt_pi.1 (hasDerivAt_pi.1 hP i) k
  have hQe : ∀ k, HasDerivAt (fun s => Q s k j) (Q' k j) τ := fun k =>
    hasDerivAt_pi.1 (hasDerivAt_pi.1 hQ k) j
  have h : HasDerivAt (fun s => ∑ k, P s i k * Q s k j)
      (∑ k, (P' i k * Q τ k j + P τ i k * Q' k j)) τ :=
    HasDerivAt.fun_sum (u := Finset.univ) (A := fun k s => P s i k * Q s k j)
      fun k _ => (hPe k).mul (hQe k)
  refine h.congr_deriv ?_
  simp only [Matrix.add_apply, Matrix.mul_apply, Finset.sum_add_distrib]

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: `τ ↦ M + τ N` has the derivative `N` at `0`. -/
private theorem hasDerivAt_affine_lsz {m n : Type*} [Fintype m] [Fintype n] (M N : Matrix m n ℝ) :
    HasDerivAt (fun τ : ℝ => M + τ • N) N 0 := by
  have h := ((hasDerivAt_id (0 : ℝ)).smul_const N).const_add M
  rw [one_smul] at h
  exact h

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the product of two differentiable matrix-valued maps is differentiable
(`differentiable_matMul` of `Dimension/Functional.lean`, private there). -/
private theorem differentiable_matMul_lsz {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
    {f : E → Matrix m n ℝ} {g : E → Matrix n p ℝ}
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) :
    Differentiable ℝ (fun y => f y * g y) := by
  let B : Matrix m n ℝ →ₗ[ℝ] Matrix n p ℝ →ₗ[ℝ] Matrix m p ℝ :=
    LinearMap.mk₂ ℝ (fun a b => a * b) Matrix.add_mul (fun c a b => Matrix.smul_mul c a b)
      Matrix.mul_add (fun c a b => Matrix.mul_smul a c b)
  let B' : Matrix m n ℝ →L[ℝ] Matrix n p ℝ →L[ℝ] Matrix m p ℝ :=
    LinearMap.toContinuousLinearMap
      ((LinearMap.toContinuousLinearMap :
        (Matrix n p ℝ →ₗ[ℝ] Matrix m p ℝ) ≃ₗ[ℝ] (Matrix n p ℝ →L[ℝ] Matrix m p ℝ)).toLinearMap ∘ₗ B)
  have hB : (fun y => f y * g y) = fun y => B' (f y) (g y) := rfl
  rw [hB]
  exact (B'.differentiable.comp hf).clm_apply hg

/-! ### One block with the skip `M` under pre-RMSNorm -/

/-- Helper: the write `g(x) = f(N_ε(x E) W_read) W_write` of the block. -/
private noncomputable def gLsz (A : Arch T d 1) (ε : ℝ) (θ : Params A dIn dOut)
    (x : Matrix T dIn ℝ) : Matrix T d ℝ :=
  A.f 0 (rmsNorm ε (x * θ.E) * θ.read 0) * θ.write 0

/-- Helper: the derivative `k(x)` of `g(x)` along `η`. -/
private noncomputable def kLsz (A : Arch T d 1) (ε : ℝ) (θ η : Params A dIn dOut)
    (x : Matrix T dIn ℝ) : Matrix T d ℝ :=
  fderiv ℝ (A.f 0) (rmsNorm ε (x * θ.E) * θ.read 0)
      (fderiv ℝ (rmsNorm ε : Matrix T d ℝ → Matrix T d ℝ) (x * θ.E) (x * η.E) * θ.read 0
        + rmsNorm ε (x * θ.E) * η.read 0) * θ.write 0
    + A.f 0 (rmsNorm ε (x * θ.E) * θ.read 0) * η.write 0

omit [Fintype T] [DecidableEq d] [Fintype dOut] in
/-- Helper: the function of one block with the skip `S 0` under pre-RMSNorm,
`F(x) = N_ε(x E S_0 + g(x)) D`. -/
private theorem eval_eq_lsz {A : Arch T d 1} {ε : ℝ} (hA : A.χ = rmsNorm ε)
    (S : Fin 1 → Matrix d d ℝ) (θ : Params A dIn dOut) (x : Matrix T dIn ℝ) :
    eval A S θ x = rmsNorm ε (x * θ.E * S 0 + gLsz A ε θ x) * θ.D := by
  have h1 : (Fin.last 1 : Fin 2) = (0 : Fin 1).succ := rfl
  rw [eval, h1, hidden_succ, Fin.castSucc_zero, hidden_zero, hA]
  rfl

omit [DecidableEq d] [Fintype dOut] in
/-- Helper: `τ ↦ x (E + τ η_E)` has the derivative `x η_E` at `0`. -/
private theorem hasDerivAt_xE_lsz {A : Arch T d 1} (θ η : Params A dIn dOut)
    (x : Matrix T dIn ℝ) : HasDerivAt (fun τ : ℝ => x * (θ + τ • η).E) (x * η.E) 0 := by
  have h := hasDerivAt_mul_lsz (hasDerivAt_const (0 : ℝ) x) (hasDerivAt_affine_lsz θ.E η.E)
    (P0 := x) (Q0 := θ.E) rfl (by simp)
  rw [Matrix.zero_mul, zero_add] at h
  exact h

omit [Fintype dOut] in
/-- Helper: along the line `θ + τ η`, the write `g(x)` has the derivative `k(x)` at `τ = 0`. -/
private theorem hasDerivAt_gLsz_line {A : Arch T d 1} {ε : ℝ} (hε : 0 < ε)
    (hf : Differentiable ℝ (A.f 0)) (θ η : Params A dIn dOut) (x : Matrix T dIn ℝ) :
    HasDerivAt (fun τ : ℝ => gLsz A ε (θ + τ • η) x) (kLsz A ε θ η x) 0 := by
  -- `N_ε(x E(τ))`
  have hN : HasDerivAt (fun τ : ℝ => rmsNorm ε (x * (θ + τ • η).E))
      (fderiv ℝ (rmsNorm ε : Matrix T d ℝ → Matrix T d ℝ) (x * θ.E) (x * η.E)) 0 :=
    ((differentiable_rmsNorm hε) (x * θ.E)).hasFDerivAt.comp_hasDerivAt_of_eq 0
      (hasDerivAt_xE_lsz θ η x) (by simp)
  -- `N_ε(x E(τ)) W_read(τ)`
  have hNR := hasDerivAt_mul_lsz hN (hasDerivAt_affine_lsz (θ.read 0) (η.read 0))
    (P0 := rmsNorm ε (x * θ.E)) (Q0 := θ.read 0) (by simp) (by simp)
  -- `f(N_ε(x E(τ)) W_read(τ))`
  have hF := ((hf (rmsNorm ε (x * θ.E) * θ.read 0))).hasFDerivAt.comp_hasDerivAt_of_eq 0 hNR
    (by simp)
  -- `f(…) W_write(τ)`
  have hFW := hasDerivAt_mul_lsz hF (hasDerivAt_affine_lsz (θ.write 0) (η.write 0))
    (P0 := A.f 0 (rmsNorm ε (x * θ.E) * θ.read 0)) (Q0 := θ.write 0) (by simp) (by simp)
  exact hFW

/-- Helper (step 2): along the line `(θ + τ η, τ M)`, the function `N_ε(x E S + g(x)) D` has the
derivative `𝐃N_ε(g(x)) (x E M + k(x)) D + N_ε(g(x)) η_D` at `τ = 0`. -/
private theorem hasDerivAt_skip_line_lsz {A : Arch T d 1} {ε : ℝ} (hε : 0 < ε)
    (hf : Differentiable ℝ (A.f 0)) (θ η : Params A dIn dOut) (M : Matrix d d ℝ)
    (x : Matrix T dIn ℝ) :
    HasDerivAt (fun τ : ℝ => rmsNorm ε (x * (θ + τ • η).E * (τ • M) + gLsz A ε (θ + τ • η) x)
        * (θ + τ • η).D)
      (fderiv ℝ (rmsNorm ε : Matrix T d ℝ → Matrix T d ℝ) (gLsz A ε θ x)
          (x * θ.E * M + kLsz A ε θ η x) * θ.D + rmsNorm ε (gLsz A ε θ x) * η.D) 0 := by
  -- `τ ↦ τ M`
  have hM : HasDerivAt (fun τ : ℝ => τ • M) M 0 := by
    have h := (hasDerivAt_id (0 : ℝ)).smul_const M
    rw [one_smul] at h
    exact h
  -- `x E(τ) (τ M)` has the derivative `x E M`
  have hS := hasDerivAt_mul_lsz (hasDerivAt_xE_lsz θ η x) hM (P0 := x * θ.E) (Q0 := 0)
    (by simp) (by simp)
  rw [Matrix.mul_zero, zero_add] at hS
  have hh := hS.add (hasDerivAt_gLsz_line hε hf θ η x)
  -- `N_ε(…)`, then the product with `D(τ)`
  have hN := ((differentiable_rmsNorm (T := T) (d := d) hε) (gLsz A ε θ x)).hasFDerivAt
    |>.comp_hasDerivAt_of_eq 0 hh (by simp)
  exact hasDerivAt_mul_lsz hN (hasDerivAt_affine_lsz θ.D η.D)
    (P0 := rmsNorm ε (gLsz A ε θ x)) (Q0 := θ.D) (by simp) (by simp)

/-- Helper: for differentiable blocks, `(θ, v) ↦ F_{θ, v}(x)` is differentiable (one block under
pre-RMSNorm with `ε > 0`). -/
private theorem differentiable_evalSkips_lsz {A : Arch T d 1} {ε : ℝ} (hε : 0 < ε)
    (hA : A.χ = rmsNorm ε) (hf : Differentiable ℝ (A.f 0))
    (ι : V →L[ℝ] (Fin 1 → Matrix d d ℝ)) (x : Matrix T dIn ℝ) :
    Differentiable ℝ (fun p : Params A dIn dOut × V => evalSkips A ι p x) := by
  -- the weights and the skip are linear, hence differentiable, functions of `(θ, v)`
  have hE : Differentiable ℝ (fun p : Params A dIn dOut × V => p.1.E) :=
    (LinearMap.toContinuousLinearMap
      (Params.linE (A := A) (dIn := dIn) (dOut := dOut))).differentiable.comp differentiable_fst
  have hR : Differentiable ℝ (fun p : Params A dIn dOut × V => p.1.read 0) :=
    (LinearMap.toContinuousLinearMap
      (Params.linRead (A := A) (dIn := dIn) (dOut := dOut) 0)).differentiable.comp
      differentiable_fst
  have hW : Differentiable ℝ (fun p : Params A dIn dOut × V => p.1.write 0) :=
    (LinearMap.toContinuousLinearMap
      (Params.linWrite (A := A) (dIn := dIn) (dOut := dOut) 0)).differentiable.comp
      differentiable_fst
  have hD : Differentiable ℝ (fun p : Params A dIn dOut × V => p.1.D) :=
    (LinearMap.toContinuousLinearMap
      (Params.linD (A := A) (dIn := dIn) (dOut := dOut))).differentiable.comp differentiable_fst
  have hS : Differentiable ℝ (fun p : Params A dIn dOut × V => ι p.2 0) :=
    differentiable_pi.1 (ι.differentiable.comp differentiable_snd) 0
  have hN := differentiable_rmsNorm (T := T) (d := d) hε
  -- `x E`, `g(x)`, `x E (ι v)_0 + g(x)` and `N_ε(…) D`
  have hxE : Differentiable ℝ (fun p : Params A dIn dOut × V => x * p.1.E) :=
    differentiable_matMul_lsz (differentiable_const x) hE
  have hg : Differentiable ℝ (fun p : Params A dIn dOut × V => gLsz A ε p.1 x) :=
    differentiable_matMul_lsz (hf.comp (differentiable_matMul_lsz (hN.comp hxE) hR)) hW
  have h1 : Differentiable ℝ
      (fun p : Params A dIn dOut × V => x * p.1.E * ι p.2 0 + gLsz A ε p.1 x) :=
    (differentiable_matMul_lsz hxE hS).add hg
  have h2 := differentiable_matMul_lsz (hN.comp h1) hD
  have e : (fun p : Params A dIn dOut × V => evalSkips A ι p x)
      = fun p => rmsNorm ε (x * p.1.E * ι p.2 0 + gLsz A ε p.1 x) * p.1.D := by
    funext p
    exact eval_eq_lsz hA _ _ _
  rw [e]
  exact h2

omit [DecidableEq d] in
/-- Helper: the chain rule along the line `τ ↦ p + τ q` of weights and skips. -/
private theorem hasDerivAt_evalSkips_line_lsz (A : Arch T d L)
    (ι : V →L[ℝ] (Fin L → Matrix d d ℝ)) (p q : Params A dIn dOut × V) (x : Matrix T dIn ℝ)
    (hdiff : DifferentiableAt ℝ (fun p' : Params A dIn dOut × V => evalSkips A ι p' x) p) :
    HasDerivAt (fun τ : ℝ => evalSkips A ι (p + τ • q) x)
      (fderiv ℝ (fun p' : Params A dIn dOut × V => evalSkips A ι p' x) p q) 0 := by
  have hline : HasDerivAt (fun τ : ℝ => p + τ • q) q 0 := by
    have h := ((hasDerivAt_id (0 : ℝ)).smul_const q).const_add p
    rw [one_smul] at h
    exact h
  have h0 : p = p + (0 : ℝ) • q := by rw [zero_smul, add_zero]
  exact hdiff.hasFDerivAt.comp_hasDerivAt_of_eq 0 hline h0

/-- Helper (step 2): a flat direction `(η, a)` at `(θ, 0)` satisfies
`𝐃N_ε(g(x)) (x E (ι a)_0 + k(x)) D + N_ε(g(x)) η_D = 0` at every input `x`. -/
private theorem flatSkips_eq_lsz {A : Arch T d 1} {ε : ℝ} (hε : 0 < ε) (hA : A.χ = rmsNorm ε)
    (hf : Differentiable ℝ (A.f 0)) (ι : V →L[ℝ] (Fin 1 → Matrix d d ℝ))
    (θ η : Params A dIn dOut) (a : V) (hη : (η, a) ∈ flatSkips A ι (θ, 0))
    (x : Matrix T dIn ℝ) :
    fderiv ℝ (rmsNorm ε : Matrix T d ℝ → Matrix T d ℝ) (gLsz A ε θ x)
        (x * θ.E * ι a 0 + kLsz A ε θ η x) * θ.D + rmsNorm ε (gLsz A ε θ x) * η.D = 0 := by
  have h0 : fderiv ℝ (fun p' : Params A dIn dOut × V => evalSkips A ι p' x) (θ, 0) (η, a) = 0 :=
    LinearMap.mem_ker.1 ((Submodule.mem_iInf _).1 hη x)
  have h1 := hasDerivAt_evalSkips_line_lsz A ι (θ, 0) (η, a) x
    (differentiable_evalSkips_lsz hε hA hf ι x (θ, 0))
  rw [h0] at h1
  have e : (fun τ : ℝ => evalSkips A ι ((θ, 0) + τ • (η, a)) x) = fun τ =>
      rmsNorm ε (x * (θ + τ • η).E * (τ • ι a 0) + gLsz A ε (θ + τ • η) x) * (θ + τ • η).D := by
    funext τ
    show eval A (ι (0 + τ • a)) (θ + τ • η) x = _
    rw [zero_add, map_smul, eval_eq_lsz hA]
    rfl
  rw [e] at h1
  exact (hasDerivAt_skip_line_lsz hε hf θ η (ι a 0) x).unique h1

/-- Helper (step 4): a flat direction `(η, 0)` at `(θ, 0)` has `η` flat for the skipless
network. -/
private theorem mem_flat_of_flatSkips_lsz {A : Arch T d 1} {ε : ℝ} (hε : 0 < ε)
    (hA : A.χ = rmsNorm ε) (hf : Differentiable ℝ (A.f 0))
    (ι : V →L[ℝ] (Fin 1 → Matrix d d ℝ)) (θ η : Params A dIn dOut)
    (hη : (η, (0 : V)) ∈ flatSkips A ι (θ, 0)) : η ∈ flat A 0 θ := by
  rw [flat, Submodule.mem_iInf]
  intro x
  rw [LinearMap.mem_ker]
  show fderiv ℝ (fun θ' => eval A 0 θ' x) θ η = 0
  have h0 : fderiv ℝ (fun p' : Params A dIn dOut × V => evalSkips A ι p' x) (θ, 0) (η, 0) = 0 :=
    LinearMap.mem_ker.1 ((Submodule.mem_iInf _).1 hη x)
  have h1 := hasDerivAt_evalSkips_line_lsz A ι (θ, 0) (η, 0) x
    (differentiable_evalSkips_lsz hε hA hf ι x (θ, 0))
  rw [h0] at h1
  have hd : DifferentiableAt ℝ (fun θ' : Params A dIn dOut => eval A 0 θ' x) θ :=
    differentiable_eval (fun ℓ => by rw [Subsingleton.elim ℓ 0]; exact hf)
      (by rw [hA]; exact differentiable_rmsNorm hε) x θ
  have h2 := hasDerivAt_eval_line (A := A) 0 θ η x hd
  have e : (fun τ : ℝ => evalSkips A ι ((θ, 0) + τ • (η, 0)) x)
      = fun τ => eval A 0 (θ + τ • η) x := by
    funext τ
    show eval A (ι (0 + τ • 0)) (θ + τ • η) x = _
    rw [smul_zero, zero_add, map_zero]
  rw [e] at h1
  exact h2.unique h1

/-! ### Step 3: large inputs -/

/-- Helper: `g(s w)` at `y = 1/s`, with `a = w E`. -/
private noncomputable def gRayLsz (A : Arch T d 1) (ε : ℝ) (θ : Params A dIn dOut)
    (a : Matrix T d ℝ) (y : ℝ) : Matrix T d ℝ :=
  A.f 0 (nLsz ε a y * θ.read 0) * θ.write 0

/-- Helper: `k(s w)` at `y = 1/s`, with `a = w E` and `b = w η_E`. -/
private noncomputable def kRayLsz (A : Arch T d 1) (ε : ℝ) (θ η : Params A dIn dOut)
    (a b : Matrix T d ℝ) (y : ℝ) : Matrix T d ℝ :=
  fderiv ℝ (A.f 0) (nLsz ε a y * θ.read 0) (dnLsz ε a b y * θ.read 0 + nLsz ε a y * η.read 0)
      * θ.write 0
    + A.f 0 (nLsz ε a y * θ.read 0) * η.write 0

omit [Fintype T] [DecidableEq d] [Fintype dOut] in
/-- Helper: `g(s w) = G(1/s)` for `s > 0`. -/
private theorem gLsz_smul_lsz {A : Arch T d 1} {ε s : ℝ} (hs : 0 < s) (θ : Params A dIn dOut)
    (w : Matrix T dIn ℝ) : gLsz A ε θ (s • w) = gRayLsz A ε θ (w * θ.E) s⁻¹ := by
  rw [gLsz, Matrix.smul_mul, rmsNorm_smul_lsz hs]
  rfl

omit [Fintype dOut] in
/-- Helper: `k(s w) = K(1/s)` for `s > 0`. -/
private theorem kLsz_smul_lsz {A : Arch T d 1} {ε s : ℝ} (hε : 0 < ε) (hs : 0 < s)
    (θ η : Params A dIn dOut) (w : Matrix T dIn ℝ) :
    kLsz A ε θ η (s • w) = kRayLsz A ε θ η (w * θ.E) (w * η.E) s⁻¹ := by
  rw [kLsz, Matrix.smul_mul, Matrix.smul_mul, rmsNorm_smul_lsz hs, fderiv_rmsNorm_smul_lsz hε hs]
  rfl

omit [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: `G` and `K` are continuous at `0` if every row of `a` is nonzero (the input
`N_ε(s w E)` of the block converges as `s → ∞`). -/
private theorem continuousAt_ray_lsz {A : Arch T d 1} {ε : ℝ} (hf : ContDiff ℝ 1 (A.f 0))
    (θ η : Params A dIn dOut) {a : Matrix T d ℝ} (ha : ∀ t, a t ≠ 0) (b : Matrix T d ℝ) :
    ContinuousAt (gRayLsz A ε θ a) 0 ∧ ContinuousAt (kRayLsz A ε θ η a b) 0 := by
  obtain ⟨hn, hdn⟩ := continuousAt_nLsz_dnLsz (ε := ε) ha b
  have hfd := hf.continuous_fderiv_apply one_ne_zero
  have hR : ∀ M : Matrix d (A.r 0) ℝ, Continuous fun N : Matrix T d ℝ => N * M := fun M =>
    continuous_id.matrix_mul continuous_const
  have hW : ∀ M : Matrix (A.w 0) d ℝ, Continuous fun N : Matrix T (A.w 0) ℝ => N * M := fun M =>
    continuous_id.matrix_mul continuous_const
  have h1 : ContinuousAt (fun y => nLsz ε a y * θ.read 0) 0 :=
    ContinuousAt.comp (f := nLsz ε a) (x := 0) (hR _).continuousAt hn
  have h4 := ContinuousAt.comp (x := (0 : ℝ)) (hf.continuous.comp (hR (θ.read 0))).continuousAt hn
  refine ⟨ContinuousAt.comp (x := (0 : ℝ)) (hW (θ.write 0)).continuousAt h4, ?_⟩
  have h2 : ContinuousAt (fun y => dnLsz ε a b y * θ.read 0 + nLsz ε a y * η.read 0) 0 :=
    (ContinuousAt.comp (f := dnLsz ε a b) (x := 0) (hR _).continuousAt hdn).add
      (ContinuousAt.comp (f := nLsz ε a) (x := 0) (hR _).continuousAt hn)
  have h3 := ContinuousAt.comp (x := (0 : ℝ)) hfd.continuousAt (h1.prodMk h2)
  exact (ContinuousAt.comp (x := (0 : ℝ)) (hW (θ.write 0)).continuousAt h3).add
    (ContinuousAt.comp (x := (0 : ℝ)) (hW (η.write 0)).continuousAt h4)

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: a map continuous at `0` that vanishes at every `1/s`, `s > 0`, vanishes at `0`. -/
private theorem eq_zero_of_inv_lsz {X : Type*} [TopologicalSpace X] [T2Space X] [Zero X]
    {Φ : ℝ → X} (hΦ : ContinuousAt Φ 0) (h : ∀ s : ℝ, 0 < s → Φ s⁻¹ = 0) : Φ 0 = 0 :=
  tendsto_nhds_unique (hΦ.tendsto.comp tendsto_inv_atTop_zero)
    (tendsto_const_nhds.congr' ((eventually_gt_atTop 0).mono fun s hs => (h s hs).symm))

/-- Helper (step 3): if `𝐃N_ε(g(x)) (x E M + k(x)) D + N_ε(g(x)) η_D = 0` at every input, `D` has
rank `d` and every row of `w E` is nonzero, then `w E M = 0`. (At `x = s w`, divided by `s`:
`𝐃N_ε(G(y)) (w E M) D + y (𝐃N_ε(G(y)) K(y) D + N_ε(G(y)) η_D) = 0` with `y = 1/s`; at `y = 0`,
`𝐃N_ε(G(0)) (w E M) D = 0`; then `D` has a right inverse and `𝐃N_ε(G(0))` is injective.) -/
private theorem mul_eq_zero_of_ray_lsz {A : Arch T d 1} {ε : ℝ} (hε : 0 < ε)
    (hf : ContDiff ℝ 1 (A.f 0)) (θ η : Params A dIn dOut) (M : Matrix d d ℝ)
    (hD : θ.D.rank = Fintype.card d)
    (hid : ∀ x : Matrix T dIn ℝ, fderiv ℝ (rmsNorm ε : Matrix T d ℝ → Matrix T d ℝ)
        (gLsz A ε θ x) (x * θ.E * M + kLsz A ε θ η x) * θ.D
          + rmsNorm ε (gLsz A ε θ x) * η.D = 0)
    (w : Matrix T dIn ℝ) (hw : ∀ t, (w * θ.E) t ≠ 0) : w * θ.E * M = 0 := by
  -- a right inverse `D⁺` of `D`
  obtain ⟨Dp, hDp⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.1
    (Matrix.mulVec_surjective_iff_rank_eq_card.2 hD)
  obtain ⟨hG, hK⟩ := continuousAt_ray_lsz (ε := ε) hf θ η hw (w * η.E)
  have hDN := (contDiff_rmsNorm_lsz (T := T) (d := d) hε).continuous_fderiv_apply one_ne_zero
  have hmD : Continuous fun N : Matrix T d ℝ => N * θ.D :=
    continuous_id.matrix_mul continuous_const
  have hmη : Continuous fun N : Matrix T d ℝ => N * η.D :=
    continuous_id.matrix_mul continuous_const
  -- `Φ(y) = 𝐃N_ε(G(y)) (w E M) D + y (𝐃N_ε(G(y)) K(y) D + N_ε(G(y)) η_D)` vanishes at `0`
  have hΦ0 := eq_zero_of_inv_lsz (Φ := fun y : ℝ =>
      fderiv ℝ (rmsNorm ε : Matrix T d ℝ → Matrix T d ℝ) (gRayLsz A ε θ (w * θ.E) y)
          (w * θ.E * M) * θ.D
        + y • (fderiv ℝ (rmsNorm ε : Matrix T d ℝ → Matrix T d ℝ) (gRayLsz A ε θ (w * θ.E) y)
            (kRayLsz A ε θ η (w * θ.E) (w * η.E) y) * θ.D
          + rmsNorm ε (gRayLsz A ε θ (w * θ.E) y) * η.D)) ?_ ?_
  · -- at `y = 0`: `𝐃N_ε(G(0)) (w E M) D = 0`, so `𝐃N_ε(G(0)) (w E M) = 0` and `w E M = 0`
    simp only [zero_smul, add_zero] at hΦ0
    have e2 := congrArg (· * Dp) hΦ0
    rw [Matrix.mul_assoc _ θ.D Dp, hDp, Matrix.mul_one, Matrix.zero_mul] at e2
    exact injective_fderiv_rmsNorm_lsz hε _ (by rw [e2, map_zero])
  · -- `Φ` is continuous at `0`
    have c1 : ContinuousAt (fun y => fderiv ℝ (rmsNorm ε : Matrix T d ℝ → Matrix T d ℝ)
        (gRayLsz A ε θ (w * θ.E) y) (w * θ.E * M)) 0 :=
      ContinuousAt.comp (f := fun y => (gRayLsz A ε θ (w * θ.E) y, w * θ.E * M)) (x := (0 : ℝ))
        hDN.continuousAt (hG.prodMk continuousAt_const)
    have c2 : ContinuousAt (fun y => fderiv ℝ (rmsNorm ε : Matrix T d ℝ → Matrix T d ℝ)
        (gRayLsz A ε θ (w * θ.E) y) (kRayLsz A ε θ η (w * θ.E) (w * η.E) y)) 0 :=
      ContinuousAt.comp (f := fun y => (gRayLsz A ε θ (w * θ.E) y,
          kRayLsz A ε θ η (w * θ.E) (w * η.E) y)) (x := (0 : ℝ))
        hDN.continuousAt (hG.prodMk hK)
    have c3 : ContinuousAt (fun y => rmsNorm ε (gRayLsz A ε θ (w * θ.E) y)) 0 :=
      ContinuousAt.comp (f := gRayLsz A ε θ (w * θ.E)) (x := (0 : ℝ))
        (differentiable_rmsNorm hε).continuous.continuousAt hG
    exact (hmD.continuousAt.comp c1).add (continuousAt_id.smul
      ((hmD.continuousAt.comp c2).add (hmη.continuousAt.comp c3)))
  · -- `Φ(1/s)` is `1/s` times the identity at `x = s w`
    intro s hs
    have e := hid (s • w)
    rw [gLsz_smul_lsz hs, kLsz_smul_lsz hε hs, Matrix.smul_mul, Matrix.smul_mul, map_add,
      map_smul, Matrix.add_mul, Matrix.smul_mul] at e
    calc _ = s⁻¹ • (s • (fderiv ℝ (rmsNorm ε : Matrix T d ℝ → Matrix T d ℝ)
            (gRayLsz A ε θ (w * θ.E) s⁻¹) (w * θ.E * M) * θ.D)
          + fderiv ℝ (rmsNorm ε : Matrix T d ℝ → Matrix T d ℝ) (gRayLsz A ε θ (w * θ.E) s⁻¹)
            (kRayLsz A ε θ η (w * θ.E) (w * η.E) s⁻¹) * θ.D
          + rmsNorm ε (gRayLsz A ε θ (w * θ.E) s⁻¹) * η.D) := by
          simp only [smul_add, smul_smul, inv_mul_cancel₀ hs.ne', one_smul, add_assoc]
      _ = 0 := by rw [e, smul_zero]

/-- Helper (step 3): a flat direction `(η, a)` at `(θ, 0)` has `a = 0`. -/
private theorem skip_eq_zero_lsz [Nonempty T] {A : Arch T d 1} {ε : ℝ} (hε : 0 < ε)
    (hA : A.χ = rmsNorm ε) (hf : ContDiff ℝ 1 (A.f 0)) (ι : V →L[ℝ] (Fin 1 → Matrix d d ℝ))
    (hι : Function.Injective ι) (θ : Params A dIn dOut) (hE : θ.E.rank = Fintype.card d)
    (hD : θ.D.rank = Fintype.card d) (η : Params A dIn dOut) (a : V)
    (hp : (η, a) ∈ flatSkips A ι (θ, 0)) : a = 0 := by
  have hid := flatSkips_eq_lsz hε hA (hf.differentiable one_ne_zero) ι θ η a hp
  -- `u (ι a)_0 = 0` for every row vector `u`: the rows of `w E` (all nonzero) give every `u ≠ 0`
  have hM : ι a 0 = 0 := by
    refine eq_zero_of_vecMul_lsz (forall_of_rows_lsz (T := T) hE
      (P := fun u => u ᵥ* ι a 0 = 0) (Matrix.zero_vecMul _) ?_)
    intro w hw t
    show (w * θ.E) t ᵥ* ι a 0 = 0
    rw [← Matrix.mul_apply_eq_vecMul, mul_eq_zero_of_ray_lsz hε hf θ η (ι a 0) hD hid w hw]
    rfl
  -- `Fin 1` has one element, and `ι` is injective
  have h1 : ι a = ι 0 := by
    rw [map_zero]
    funext i
    rw [Subsingleton.elim i 0, hM]
    rfl
  exact hι h1

/-- **One block under pre-RMSNorm (`ε > 0`), at the skip `0`:** for a real-analytic block, `E` and
`D` of rank `d` and an injective `ι`, the family with the skips `ι v` has at `(θ, 0)` at least the
functional dimension of the skipless network at `θ` plus the dimension of `V`. -/
theorem funDim_add_finrank_le_funDimSkips_zero [Nonempty T] [FiniteDimensional ℝ V]
    {A : Arch T d 1} {ε : ℝ} (hε : 0 < ε) (hA : A.χ = rmsNorm ε)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ)
    (ι : V →L[ℝ] (Fin 1 → Matrix d d ℝ)) (hι : Function.Injective ι)
    (θ : Params A dIn dOut) (hE : θ.E.rank = Fintype.card d) (hD : θ.D.rank = Fintype.card d) :
    funDim A 0 θ + Module.finrank ℝ V ≤ funDimSkips A ι (θ, 0) := by
  have hf1 : ContDiff ℝ 1 (A.f 0) := (hf 0).contDiff
  have hfd : Differentiable ℝ (A.f 0) := hf1.differentiable one_ne_zero
  -- a flat direction `(η, a)` has `a = 0`, and `η` is flat for the skipless network
  have key : ∀ p ∈ flatSkips A ι (θ, 0), p.2 = 0 ∧ p.1 ∈ flat A 0 θ := by
    rintro ⟨η, a⟩ hp
    have ha : a = 0 := skip_eq_zero_lsz hε hA hf1 ι hι θ hE hD η a hp
    subst ha
    exact ⟨rfl, mem_flat_of_flatSkips_lsz hε hA hfd ι θ η hp⟩
  -- so `(η, a) ↦ η` maps the flat directions with skips injectively into those without
  let φ : flatSkips A ι (θ, 0) →ₗ[ℝ] flat A 0 θ :=
    LinearMap.codRestrict (flat A 0 θ)
      ((LinearMap.fst ℝ (Params A dIn dOut) V).domRestrict (flatSkips A ι (θ, 0)))
      (fun p => (key p.1 p.2).2)
  have hφ : Function.Injective φ := by
    intro p q hpq
    have h1 : p.1.1 = q.1.1 := congrArg Subtype.val hpq
    exact Subtype.ext (Prod.ext h1 ((key p.1 p.2).1.trans (key q.1 q.2).1.symm))
  have hle := LinearMap.finrank_le_finrank_of_injective hφ
  -- the dimension counts `fd + dim K = P` with and without the skips
  have h1 := funDimSkips_add_finrank_flatSkips A ι
    (fun ℓ => by rw [Subsingleton.elim ℓ 0]; exact hfd)
    (by rw [hA]; exact differentiable_rmsNorm hε) (θ, 0)
  have h2 := funDim_add_finrank_flat' (S := 0) θ
  rw [Module.finrank_prod] at h1
  omega

end Skips
