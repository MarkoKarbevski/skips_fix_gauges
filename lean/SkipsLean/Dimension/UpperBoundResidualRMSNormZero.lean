import SkipsLean.Dimension.UpperBoundRMSNormZero
import SkipsLean.Residual.UpperBoundSymmetries

/-!
# The upper bound for residual networks under pre-RMSNorm with `ε = 0`: one copy of `CO(d)`

Paper (skips paper): Theorem A.17 (Symmetry counts and upper bounds) and Theorem 4.2: "at generic
parameters, the functional dimension is at most `P − (L + 1) dim 𝒢 − s` without skips and at most
`P − dim 𝒢 − s` with identity skips", where under pre-RMSNorm `𝒢` is "`CO(d_model)` when `ε = 0`
and `O(d_model)` when `ε > 0`" (Lemma A.2), and `dim CO(d) = d(d−1)/2 + 1`. Theorem B.1 (iv) uses
the bound `P − d(d−1)/2 − 1 − s` for the residual network with `ε = 0`.

The bound without skips for `ε = 0` is `Dimension/UpperBoundRMSNormZero.lean` (Theorem 4.3 of the
dimension paper), with one copy of `CO(d)` at each hidden state: the directions `cobDir θ Y`
(antisymmetric `Y_ℓ`) and `scaleDir θ β`. With identity skips the change of basis `G = cQ` is the
same at all hidden states (Theorem 3.3): `E ↦ E G`, `W_read^ℓ ↦ Q⁻¹ W_read^ℓ`,
`W_write^ℓ ↦ W_write^ℓ G`, `D ↦ Q⁻¹ D`. Its directions at `θ` are `cobDir θ (fun _ => Y)` with one
antisymmetric `Y`, and `scaleDir θ (fun _ => β)` with one number `β`. Stated here for arbitrary
maps `f_ℓ`, as the statements of `Dimension/UpperBoundRMSNormZero.lean`: they hold at every
parameter, for Lean's total function (`rmsRow 0 0 = 0`). The symmetries inside the blocks are not
counted (no term `s`): for tanh and GELU blocks this is the bound of Theorem A.17 (ii), for blocks
with symmetries inside it is weaker by `s`.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {A : Arch T d L} (θ : Params A dIn dOut)

omit [Fintype T] [Fintype dOut] in
/-- Helper (Theorem 3.3 (i) for `ε = 0`): with identity skips, the same `G = c Q` (`c > 0`, `Q`
orthogonal) at all hidden states, `G` at the writes and `Q⁻¹` at the reads, keeps the function:
the special case of `eval_cob` with `rmsNorm 0 (h G) = rmsNorm 0 h Q`. -/
private theorem eval_cob_residual_rmsNorm_zero_rb0 (x : Matrix T dIn ℝ) (hA : A.χ = rmsNorm 0)
    (G Q : GL d ℝ) {c : ℝ} (hc : 0 < c) (hQ : (Q : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ)
    (hG : (G : Matrix d d ℝ) = c • (Q : Matrix d d ℝ)) :
    eval A 1 (θ.cob (fun _ => G) (fun _ => Q)) x = eval A 1 θ x := by
  -- RMSNorm with `ε = 0` loses the scale `c` (Lemma A.1): `χ (h G) = χ (h) Q`.
  have hχ : ∀ (_ : Fin (L + 1)) (h : Matrix T d ℝ),
      A.χ (h * (G : Matrix d d ℝ)) = A.χ h * (Q : Matrix d d ℝ) := by
    intro _ h
    rw [hA, hG]
    exact rmsNorm_zero_mul_smul_orthogonal hc hQ h
  -- the identity skips stay `G⁻¹ I G = I`
  have hskip : cobSkip (1 : Fin L → Matrix d d ℝ) (fun _ => G) = 1 := by
    funext ℓ
    simp only [cobSkip, Pi.one_apply, Matrix.mul_one, Units.inv_mul]
  have h := eval_cob (M := 1) (θ := θ) (G := fun _ => G) (K := fun _ => Q) (x := x) hχ
  rwa [hskip] at h

/-- Helper (the private `scalarGL_rz` of `UpperBoundRMSNormZero.lean`): the invertible scalar
matrix `c • 1`, for `c ≠ 0`. -/
private noncomputable def scalarGL_rb0 (c : ℝ) (hc : c ≠ 0) : GL d ℝ :=
  ⟨c • 1, c⁻¹ • 1, by simp [smul_smul, hc], by simp [smul_smul, hc]⟩

/-- Helper (the private `scaleCurve_rz`): the curve of the scales, `E ↦ e^{τ β_0} E`,
`W_write^ℓ ↦ e^{τ β_ℓ} W_write^ℓ`, the reads and `D` unchanged. -/
private noncomputable def scaleCurve_rb0 (β : Fin (L + 1) → ℝ) (τ : ℝ) :
    Params A dIn dOut where
  E := Real.exp (τ * β 0) • θ.E
  read := θ.read
  write ℓ := Real.exp (τ * β ℓ.succ) • θ.write ℓ
  D := θ.D

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the curve passes through `θ` at `τ = 0`. -/
private theorem scaleCurve_zero_rb0 (β : Fin (L + 1) → ℝ) : scaleCurve_rb0 θ β 0 = θ := by
  refine Params.ext' ?_ (fun ℓ => ?_) (fun ℓ => ?_) ?_ <;>
    simp only [scaleCurve_rb0, zero_mul, Real.exp_zero, one_smul]

omit [Fintype T] [Fintype dIn] [Fintype dOut] in
/-- Helper: the curve is the change of basis `G_ℓ = e^{τ β_ℓ} 1` at the writes and `K_ℓ = 1` at
the reads. -/
private theorem scaleCurve_eq_cob_rb0 (β : Fin (L + 1) → ℝ) (τ : ℝ) :
    scaleCurve_rb0 θ β τ
      = θ.cob (fun ℓ => scalarGL_rb0 (Real.exp (τ * β ℓ)) (Real.exp_ne_zero _)) (fun _ => 1) := by
  refine Params.ext' ?_ (fun ℓ => ?_) (fun ℓ => ?_) ?_
  · show Real.exp (τ * β 0) • θ.E = θ.E * (Real.exp (τ * β 0) • (1 : Matrix d d ℝ))
    rw [Matrix.mul_smul, Matrix.mul_one]
  · show θ.read ℓ = (↑(1 : GL d ℝ)⁻¹ : Matrix d d ℝ) * θ.read ℓ
    rw [inv_one, Units.val_one, Matrix.one_mul]
  · show Real.exp (τ * β ℓ.succ) • θ.write ℓ
      = θ.write ℓ * (Real.exp (τ * β ℓ.succ) • (1 : Matrix d d ℝ))
    rw [Matrix.mul_smul, Matrix.mul_one]
  · show θ.D = (↑(1 : GL d ℝ)⁻¹ : Matrix d d ℝ) * θ.D
    rw [inv_one, Units.val_one, Matrix.one_mul]

/-- Helper: `τ ↦ e^{τ a} b` has derivative `a b` at `τ = 0`. -/
private theorem hasDerivAt_exp_mul_const_rb0 (a b : ℝ) :
    HasDerivAt (fun τ : ℝ => Real.exp (τ * a) * b) (a * b) 0 := by
  have h := ((hasDerivAt_id (0 : ℝ)).mul_const a).exp.mul_const b
  simpa using h

omit [Fintype T] [DecidableEq d] in
/-- Helper: the curve has velocity `scaleDir θ β` at `τ = 0`, entry by entry, through the linear
equivalence of the parameters with the tuples of their components. -/
private theorem hasDerivAt_scaleCurve_rb0 (β : Fin (L + 1) → ℝ) :
    HasDerivAt (scaleCurve_rb0 θ β) (scaleDir θ β) 0 := by
  have hprod : HasDerivAt (fun τ : ℝ => Params.linearEquivProd (scaleCurve_rb0 θ β τ))
      (Params.linearEquivProd (scaleDir θ β)) 0 := by
    refine HasDerivAt.prodMk ?_ (HasDerivAt.prodMk ?_ (HasDerivAt.prodMk ?_ ?_))
    · -- the entries of the embedding are `e^{τ β_0} E_ik`
      exact hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun k =>
        hasDerivAt_exp_mul_const_rb0 (β 0) (θ.E i k)
    · -- the reads do not move
      exact hasDerivAt_const (0 : ℝ) θ.read
    · -- the entries of the writes are `e^{τ β_ℓ} W_ik`
      exact hasDerivAt_pi.2 fun ℓ => hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun k =>
        hasDerivAt_exp_mul_const_rb0 (β ℓ.succ) (θ.write ℓ i k)
    · -- the readout does not move
      exact hasDerivAt_const (0 : ℝ) θ.D
  -- back from the tuples of components to the parameters
  exact (LinearMap.toContinuousLinearMap
    (Params.linearEquivProd (A := A) (dIn := dIn)
      (dOut := dOut)).symm.toLinearMap).hasFDerivAt.comp_hasDerivAt 0 hprod

/-- The direction of one orthogonal change of basis at all hidden states is flat for a residual
network under pre-RMSNorm with `ε = 0`. -/
theorem cobDir_const_mem_flat_residual_rmsNorm_zero (hA : A.χ = rmsNorm 0) (Y : Matrix d d ℝ)
    (hY : Yᵀ = -Y) : cobDir θ (fun _ => Y) ∈ flat A 1 θ := by
  -- the orthogonal part `c = 1`, `G = Q = exp (τ Y)` at all hidden states: the statement of
  -- `Residual/UpperBoundSymmetries.lean` for every real `ε`, here `ε = 0`
  exact cobDir_const_mem_flat_residual_rmsNorm' θ 0 hA Y hY

/-- The direction of one scale at all hidden states (`E ↦ β E`, `W_write^ℓ ↦ β W_write^ℓ`) is flat
for a residual network under pre-RMSNorm with `ε = 0`. -/
theorem scaleDir_const_mem_flat_residual_rmsNorm_zero (hA : A.χ = rmsNorm 0) (β : ℝ) :
    scaleDir θ (fun _ => β) ∈ flat A 1 θ := by
  -- The scalings `e^{τ β}` at all hidden states move `θ` with velocity `scaleDir θ (fun _ => β)`,
  -- and keep the function (Theorem 3.3 (i) for `ε = 0`, with `c = e^{τ β}` and `Q = 1`).
  refine mem_flat_of_hasDerivAt' θ (scaleCurve_rb0 θ fun _ => β) (scaleDir θ fun _ => β)
    (hasDerivAt_scaleCurve_rb0 θ _) (scaleCurve_zero_rb0 θ _)
    (Filter.Eventually.of_forall fun τ x => ?_)
  rw [scaleCurve_eq_cob_rb0 θ _ τ]
  refine eval_cob_residual_rmsNorm_zero_rb0 θ x hA
    (scalarGL_rb0 (Real.exp (τ * β)) (Real.exp_ne_zero _)) 1 (Real.exp_pos (τ * β))
    (one_mem _) ?_
  show Real.exp (τ * β) • (1 : Matrix d d ℝ) = Real.exp (τ * β) • ((1 : GL d ℝ) : Matrix d d ℝ)
  rw [Units.val_one]

omit [Fintype T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (the private `cancel_left_of_rank_rz`): a matrix `M` of rank equal to its number of
columns cancels on the left, `M X = M Y → X = Y` (its kernel is `0` by rank–nullity). -/
private theorem cancel_left_of_rank_rb0 {m n k : Type*} [Fintype n] (M : Matrix m n ℝ)
    (hM : M.rank = Fintype.card n) {X Y : Matrix n k ℝ} (h : M * X = M * Y) : X = Y := by
  -- `v ↦ M v` is injective: `rank M + dim ker M = card n`
  have hinj : Function.Injective M.mulVecLin := by
    rw [← LinearMap.ker_eq_bot, ← Submodule.finrank_eq_zero]
    have := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
    rw [Module.finrank_fintype_fun_eq_card] at this
    rw [Matrix.rank] at hM
    omega
  -- compare `X` and `Y` column by column
  ext i j
  have hcol : M.mulVecLin (fun l => X l j) = M.mulVecLin (fun l => Y l j) := by
    funext p
    have := congrFun (congrFun h p) j
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
  exact congrFun (hinj hcol) i

omit [Fintype T] [Fintype d] [Fintype dIn] [Fintype dOut] in
/-- Helper (the private `antisymm_add_smul_one_inj_rz`): an antisymmetric matrix plus a scalar
matrix determines both: the diagonal of an antisymmetric matrix vanishes. -/
private theorem antisymm_add_smul_one_inj_rb0 [Nonempty d] {X X' : Matrix d d ℝ}
    (hX : Xᵀ = -X) (hX' : X'ᵀ = -X') {b b' : ℝ}
    (h : X + b • (1 : Matrix d d ℝ) = X' + b' • 1) : X = X' ∧ b = b' := by
  obtain ⟨k⟩ := ‹Nonempty d›
  -- the diagonal entries of an antisymmetric matrix vanish
  have hd : ∀ {Z : Matrix d d ℝ}, Zᵀ = -Z → Z k k = 0 := fun {Z} hZ => by
    have := congrFun (congrFun hZ k) k
    rw [transpose_apply, Matrix.neg_apply] at this
    linarith
  -- the entry `(k, k)` gives `b = b'`, and then `X = X'`
  have hk := congrFun (congrFun h k) k
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one,
    hd hX, hd hX', zero_add] at hk
  subst hk
  exact ⟨add_right_cancel h, rfl⟩

omit [Fintype T] [Fintype dIn] [Fintype dOut] in
/-- Helper (the private `mul_add_smul_inj_rz`): if `M` has rank `d`, then `M X + b M` with
antisymmetric `X` determines `X` and `b`: it is `M (X + b 1)`. -/
private theorem mul_add_smul_inj_rb0 [Nonempty d] {m : Type*} (M : Matrix m d ℝ)
    (hM : M.rank = Fintype.card d) {X X' : Matrix d d ℝ} (hX : Xᵀ = -X) (hX' : X'ᵀ = -X')
    {b b' : ℝ} (h : M * X + b • M = M * X' + b' • M) : X = X' ∧ b = b' := by
  have h' : M * (X + b • (1 : Matrix d d ℝ)) = M * (X' + b' • 1) := by
    rw [Matrix.mul_add, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_one]
    exact h
  exact antisymm_add_smul_one_inj_rb0 hX hX' (cancel_left_of_rank_rb0 M hM h')

/-- Helper (the private `scaleDirLin_rz`): `β ↦ scaleDir θ β` is linear. -/
private noncomputable def scaleDirLin_rb0 : (Fin (L + 1) → ℝ) →ₗ[ℝ] Params A dIn dOut where
  toFun := scaleDir θ
  map_add' β β' := by
    refine Params.ext' ?_ (fun ℓ => ?_) (fun ℓ => ?_) ?_ <;>
      simp only [scaleDir, Params.add_E, Params.add_read, Params.add_write, Params.add_D,
        Pi.add_apply, add_smul, add_zero]
  map_smul' c β := by
    refine Params.ext' ?_ (fun ℓ => ?_) (fun ℓ => ?_) ?_ <;>
      simp only [scaleDir, Params.smul_E, Params.smul_read, Params.smul_write, Params.smul_D,
        Pi.smul_apply, smul_eq_mul, mul_smul, smul_zero, RingHom.id_apply]

/-- **The upper bound for residual networks under pre-RMSNorm with `ε = 0`:** if `E` has rank
`d ≥ 1`, the functional dimension of a residual network is at most `P − (d(d−1)/2 + 1)`. -/
theorem funDim_add_le_residual_rmsNorm_zero [Nonempty d] (hA : A.χ = rmsNorm 0)
    (hE : θ.E.rank = Fintype.card d) :
    funDim A 1 θ + (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
      ≤ Module.finrank ℝ (Params A dIn dOut) := by
  -- the linear map `(Y, β) ↦ cobDir θ (fun _ => Y) + scaleDir θ (fun _ => β)`, `Y` antisymmetric
  let Φ : antisymmetric d × ℝ →ₗ[ℝ] Params A dIn dOut :=
    ((cobDirLin θ).comp (LinearMap.pi fun _ => (antisymmetric d).subtype)).coprod
      ((scaleDirLin_rb0 θ).comp (LinearMap.pi fun _ => LinearMap.id))
  -- its directions are flat, since both summands are
  have hV : LinearMap.range Φ ≤ flat A 1 θ := by
    rintro _ ⟨p, rfl⟩
    rw [LinearMap.coprod_apply]
    exact Submodule.add_mem _
      (cobDir_const_mem_flat_residual_rmsNorm_zero θ hA (p.1 : Matrix d d ℝ) p.1.2)
      (scaleDir_const_mem_flat_residual_rmsNorm_zero θ hA p.2)
  -- it is injective: its `E` component is `E Y + β E = E (Y + β 1)`, and `E` has rank `d`
  have hinj : Function.Injective Φ := by
    intro p q hpq
    rw [LinearMap.coprod_apply, LinearMap.coprod_apply] at hpq
    have h' : cobDir θ (fun _ => (p.1 : Matrix d d ℝ)) + scaleDir θ (fun _ => p.2)
        = cobDir θ (fun _ => (q.1 : Matrix d d ℝ)) + scaleDir θ (fun _ => q.2) := hpq
    have h0 : θ.E * (p.1 : Matrix d d ℝ) + p.2 • θ.E = θ.E * (q.1 : Matrix d d ℝ) + q.2 • θ.E :=
      congrArg Params.E h'
    obtain ⟨h1, h2⟩ := mul_add_smul_inj_rb0 θ.E hE p.1.2 q.1.2 h0
    exact Prod.ext (Subtype.ext h1) h2
  -- the domain has dimension `d (d - 1) / 2 + 1`
  have hdim : Module.finrank ℝ (antisymmetric d × ℝ)
      = Fintype.card d * (Fintype.card d - 1) / 2 + 1 := by
    rw [Module.finrank_prod, finrank_antisymmetric, Module.finrank_self]
  have h := funDim_add_finrank_le_of_le_flat' θ _ hV
  rwa [LinearMap.finrank_range_of_inj hinj, hdim] at h

omit [Fintype T] in
/-- Helper (the private `rank_eq_of_isUnit_det_submatrix` of `Generic/Params.lean`): a matrix
with `d` columns has rank `d` if some `d` of its rows form an invertible matrix. -/
private theorem rank_eq_of_isUnit_det_submatrix_rb0 {m : Type*} (M : Matrix m d ℝ) (ρ : d ↪ m)
    (h : IsUnit (M.submatrix ρ id).det) : M.rank = Fintype.card d :=
  le_antisymm (Matrix.rank_le_card_width M)
    ((Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).2 h)).symm.le.trans
      (Matrix.rank_submatrix_le M ρ id))

/-- Helper (the private `ae_rank_E` of `Generic/Params.lean`): at generic parameters `E` has rank
`d`, when `d_in ≥ d`. -/
private theorem ae_rank_E_rb0 (μ : Measure (Params A dIn dOut)) [μ.IsAddHaarMeasure]
    (hdIn : Fintype.card d ≤ Fintype.card dIn) :
    ∀ᵐ η ∂μ, η.E.rank = Fintype.card d := by
  -- `d` rows of `E`, invertible at generic parameters
  obtain ⟨ρ⟩ := Function.Embedding.nonempty_of_card_le hdIn
  filter_upwards [ae_isUnit_det_submatrix μ] with η hη
  exact rank_eq_of_isUnit_det_submatrix_rb0 η.E ρ (hη.2.2.1 ρ)

/-- **Skips paper, Theorem A.17 (ii), residual networks under pre-RMSNorm with `ε = 0`, at generic
parameters:** for `d_in ≥ d ≥ 1`, the functional dimension of a residual network is at most
`P − (d(d−1)/2 + 1)`, with `d(d−1)/2 + 1` the dimension of `CO(d)`. -/
theorem ae_funDim_add_le_residual_rmsNorm_zero [Nonempty d]
    (μ : Measure (Params A dIn dOut)) [μ.IsAddHaarMeasure] (hA : A.χ = rmsNorm 0)
    (hdIn : Fintype.card d ≤ Fintype.card dIn) :
    ∀ᵐ θ ∂μ, funDim A 1 θ + (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
      ≤ Module.finrank ℝ (Params A dIn dOut) := by
  -- the pointwise bound holds wherever `E` has rank `d`
  filter_upwards [ae_rank_E_rb0 μ hdIn] with θ hE
  exact funDim_add_le_residual_rmsNorm_zero θ hA hE

end Skips
