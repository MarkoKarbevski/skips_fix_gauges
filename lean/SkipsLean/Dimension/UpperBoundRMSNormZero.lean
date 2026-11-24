import SkipsLean.Dimension.UpperBoundRMSNorm
import SkipsLean.Dimension.Rescaling
import SkipsLean.Symmetry.Normalized
import SkipsLean.Generic.Params
import SkipsLean.Generic.Gated

/-!
# The upper bound under pre-RMSNorm with `ε = 0`: the group `CO(d)`

Paper (dimension paper): Theorem 4.3 and the sentence after it, "For `ε = 0` the same bound holds,
with `𝒢 = CO(d_model)`, for the four kinds of block of the main result (Appendix D.2)"; `CO(d)` is
"the group of the matrices `cQ`, of dimension `d(d−1)/2 + 1`" (`c > 0`, `Q` orthogonal). The bound
is `fd ≤ P − (L + 1) (d(d−1)/2 + 1) − s`.

By Proposition 3.2 for `ε = 0` (`eval_cob_rmsNorm_zero`), with `G_ℓ = c_ℓ Q_ℓ` the writes (and `E`)
are multiplied by `G_ℓ` and the reads (and `D`) by `Q_ℓ⁻¹`: RMSNorm with `ε = 0` loses the scale.
So the directions of the symmetries at `θ` are `cobDir θ Y` with antisymmetric `Y_0, …, Y_L` (the
orthogonal part) and `scaleDir θ β` (the scales: `E ↦ β_0 E`, `W_write^ℓ ↦ β_ℓ W_write^ℓ`, the
reads and `D` unchanged), and for gated blocks the rescalings `rescaleDir θ α` of the hidden units.

RMSNorm with `ε = 0` is not differentiable at `0`, and the Lean `rmsNorm 0` maps a zero row to `0`.
The statements below hold at every parameter and for arbitrary maps `f_ℓ`: `flat` and `funDim` are
defined through the Fréchet derivative in the parameters, which Lean takes to be `0` where the
output is not differentiable (as in the statements with a prime of
`Dimension/UpperBoundRMSNorm.lean`).
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]

section General

variable {A : Arch T d L}

/-- The direction in which the scales `c_0, …, c_L > 0` of the hidden states move the parameters
under pre-RMSNorm with `ε = 0`: `E ↦ β_0 E` and `W_write^ℓ ↦ β_ℓ W_write^ℓ`; the reads and `D`
do not move. It is the derivative at `τ = 0` of `θ.cob (fun ℓ => exp (τ β_ℓ) • 1) (fun _ => 1)`. -/
def scaleDir (θ : Params A dIn dOut) (β : Fin (L + 1) → ℝ) : Params A dIn dOut where
  E := β 0 • θ.E
  read _ := 0
  write ℓ := β ℓ.succ • θ.write ℓ
  D := 0

variable (θ : Params A dIn dOut)

/-- Helper: the invertible scalar matrix `c • 1`, for `c ≠ 0`. -/
private noncomputable def scalarGL_rz (c : ℝ) (hc : c ≠ 0) : GL d ℝ :=
  ⟨c • 1, c⁻¹ • 1, by simp [smul_smul, hc], by simp [smul_smul, hc]⟩

/-- Helper: the curve of the scales, written out: `E ↦ e^{τ β_0} E`,
`W_write^ℓ ↦ e^{τ β_ℓ} W_write^ℓ`, the reads and `D` unchanged. -/
private noncomputable def scaleCurve_rz (β : Fin (L + 1) → ℝ) (τ : ℝ) : Params A dIn dOut where
  E := Real.exp (τ * β 0) • θ.E
  read := θ.read
  write ℓ := Real.exp (τ * β ℓ.succ) • θ.write ℓ
  D := θ.D

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the curve passes through `θ` at `τ = 0`. -/
private theorem scaleCurve_zero_rz (β : Fin (L + 1) → ℝ) : scaleCurve_rz θ β 0 = θ := by
  refine Params.ext' ?_ (fun ℓ => ?_) (fun ℓ => ?_) ?_ <;>
    simp only [scaleCurve_rz, zero_mul, Real.exp_zero, one_smul]

omit [Fintype T] [Fintype dIn] [Fintype dOut] in
/-- Helper: the curve is the change of basis `G_ℓ = e^{τ β_ℓ} 1` at the writes and `K_ℓ = 1` at
the reads. -/
private theorem scaleCurve_eq_cob_rz (β : Fin (L + 1) → ℝ) (τ : ℝ) :
    scaleCurve_rz θ β τ = θ.cob (fun ℓ => scalarGL_rz (Real.exp (τ * β ℓ)) (Real.exp_ne_zero _))
      (fun _ => 1) := by
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
private theorem hasDerivAt_exp_mul_const_rz (a b : ℝ) :
    HasDerivAt (fun τ : ℝ => Real.exp (τ * a) * b) (a * b) 0 := by
  have h := ((hasDerivAt_id (0 : ℝ)).mul_const a).exp.mul_const b
  simpa using h

omit [Fintype T] [DecidableEq d] in
/-- Helper: the curve has velocity `scaleDir θ β` at `τ = 0`, entry by entry, through the linear
equivalence of the parameters with the tuples of their components. -/
private theorem hasDerivAt_scaleCurve_rz (β : Fin (L + 1) → ℝ) :
    HasDerivAt (scaleCurve_rz θ β) (scaleDir θ β) 0 := by
  have hprod : HasDerivAt (fun τ : ℝ => Params.linearEquivProd (scaleCurve_rz θ β τ))
      (Params.linearEquivProd (scaleDir θ β)) 0 := by
    refine HasDerivAt.prodMk ?_ (HasDerivAt.prodMk ?_ (HasDerivAt.prodMk ?_ ?_))
    · -- the entries of the embedding are `e^{τ β_0} E_ik`
      exact hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun k =>
        hasDerivAt_exp_mul_const_rz (β 0) (θ.E i k)
    · -- the reads do not move
      exact hasDerivAt_const (0 : ℝ) θ.read
    · -- the entries of the writes are `e^{τ β_ℓ} W_ik`
      exact hasDerivAt_pi.2 fun ℓ => hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun k =>
        hasDerivAt_exp_mul_const_rz (β ℓ.succ) (θ.write ℓ i k)
    · -- the readout does not move
      exact hasDerivAt_const (0 : ℝ) θ.D
  -- back from the tuples of components to the parameters
  exact (LinearMap.toContinuousLinearMap
    (Params.linearEquivProd (A := A) (dIn := dIn)
      (dOut := dOut)).symm.toLinearMap).hasFDerivAt.comp_hasDerivAt 0 hprod

/-- **Proposition 3.2 for `ε = 0`, infinitesimal form, the scales:** without skip connections and
under pre-RMSNorm with `ε = 0`, every direction `scaleDir θ β` is flat, for arbitrary maps
`f_ℓ`. -/
theorem scaleDir_mem_flat_skipless_rmsNorm_zero (hA : A.χ = rmsNorm 0) (β : Fin (L + 1) → ℝ) :
    scaleDir θ β ∈ flat A 0 θ := by
  -- The scalings `e^{τ β_ℓ}` move `θ` with velocity `scaleDir θ β`, and keep the function
  -- (Proposition 3.2 for `ε = 0`, with `c_ℓ = e^{τ β_ℓ}` and `Q_ℓ = 1`).
  refine mem_flat_of_hasDerivAt' θ (scaleCurve_rz θ β) (scaleDir θ β)
    (hasDerivAt_scaleCurve_rz θ β) (scaleCurve_zero_rz θ β)
    (Filter.Eventually.of_forall fun τ x => ?_)
  rw [scaleCurve_eq_cob_rz θ β τ]
  exact eval_cob_rmsNorm_zero θ x hA _ (fun _ => 1) (fun ℓ => Real.exp (τ * β ℓ))
    (fun _ => Real.exp_pos _) (fun _ => one_mem _) (fun _ => rfl)

omit [Fintype T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: a matrix `M` of rank equal to its number of columns cancels on the left,
`M X = M Y → X = Y` (its kernel is `0` by rank–nullity). -/
private theorem cancel_left_of_rank_rz {m n k : Type*} [Fintype n] (M : Matrix m n ℝ)
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
/-- Helper: an antisymmetric matrix plus a scalar matrix determines both: the diagonal of an
antisymmetric matrix vanishes, so a diagonal entry gives the scalar. -/
private theorem antisymm_add_smul_one_inj_rz [Nonempty d] {X X' : Matrix d d ℝ} (hX : Xᵀ = -X)
    (hX' : X'ᵀ = -X') {b b' : ℝ} (h : X + b • (1 : Matrix d d ℝ) = X' + b' • 1) :
    X = X' ∧ b = b' := by
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
/-- Helper: if `M` has rank `d`, then `M X + b M` with antisymmetric `X` determines `X` and `b`:
it is `M (X + b 1)`. -/
private theorem mul_add_smul_inj_rz [Nonempty d] {m : Type*} (M : Matrix m d ℝ)
    (hM : M.rank = Fintype.card d) {X X' : Matrix d d ℝ} (hX : Xᵀ = -X) (hX' : X'ᵀ = -X')
    {b b' : ℝ} (h : M * X + b • M = M * X' + b' • M) : X = X' ∧ b = b' := by
  have h' : M * (X + b • (1 : Matrix d d ℝ)) = M * (X' + b' • 1) := by
    rw [Matrix.mul_add, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_one]
    exact h
  exact antisymm_add_smul_one_inj_rz hX hX' (cancel_left_of_rank_rz M hM h')

/-- **Lemma B.1 for `ε = 0`, infinitesimal form:** if `E` and every write have rank `d ≥ 1`, the
antisymmetric matrices `Y_0, …, Y_L` and the numbers `β_0, …, β_L` are determined by the direction
`cobDir θ Y + scaleDir θ β`. -/
theorem cobDir_add_scaleDir_injective [Nonempty d] (hE : θ.E.rank = Fintype.card d)
    (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d)
    {Y Y' : Fin (L + 1) → Matrix d d ℝ} (hY : ∀ ℓ, (Y ℓ)ᵀ = -Y ℓ) (hY' : ∀ ℓ, (Y' ℓ)ᵀ = -Y' ℓ)
    {β β' : Fin (L + 1) → ℝ}
    (h : cobDir θ Y + scaleDir θ β = cobDir θ Y' + scaleDir θ β') :
    Y = Y' ∧ β = β' := by
  -- the embedding moves by `E Y_0 + β_0 E`, the write of block `ℓ` by `W Y_{ℓ+1} + β_{ℓ+1} W`
  have h0 : θ.E * Y 0 + β 0 • θ.E = θ.E * Y' 0 + β' 0 • θ.E := congrArg Params.E h
  have hwr : ∀ ℓ : Fin L, θ.write ℓ * Y ℓ.succ + β ℓ.succ • θ.write ℓ
      = θ.write ℓ * Y' ℓ.succ + β' ℓ.succ • θ.write ℓ := fun ℓ =>
    congrArg (fun η => η.write ℓ) h
  -- every hidden state is `0` or a successor; `E` and the writes have rank `d`
  have key : ∀ ℓ, Y ℓ = Y' ℓ ∧ β ℓ = β' ℓ := by
    intro ℓ
    cases ℓ using Fin.cases with
    | zero => exact mul_add_smul_inj_rz θ.E hE (hY 0) (hY' 0) h0
    | succ ℓ => exact mul_add_smul_inj_rz (θ.write ℓ) (hw ℓ) (hY _) (hY' _) (hwr ℓ)
  exact ⟨funext fun ℓ => (key ℓ).1, funext fun ℓ => (key ℓ).2⟩

/-- Helper: `β ↦ scaleDir θ β` is linear. -/
private noncomputable def scaleDirLin_rz : (Fin (L + 1) → ℝ) →ₗ[ℝ] Params A dIn dOut where
  toFun := scaleDir θ
  map_add' β β' := by
    refine Params.ext' ?_ (fun ℓ => ?_) (fun ℓ => ?_) ?_ <;>
      simp only [scaleDir, Params.add_E, Params.add_read, Params.add_write, Params.add_D,
        Pi.add_apply, add_smul, add_zero]
  map_smul' c β := by
    refine Params.ext' ?_ (fun ℓ => ?_) (fun ℓ => ?_) ?_ <;>
      simp only [scaleDir, Params.smul_E, Params.smul_read, Params.smul_write, Params.smul_D,
        Pi.smul_apply, smul_eq_mul, mul_smul, smul_zero, RingHom.id_apply]

/-- **Theorem 4.3 of the dimension paper for `ε = 0`, for the group `CO(d)`, for arbitrary maps
`f_ℓ`:** if `E` and every write have rank `d ≥ 1`, the functional dimension of a network without
skip connections under pre-RMSNorm with `ε = 0` is at most `P − (L + 1) (d(d−1)/2 + 1)`. -/
theorem funDim_add_le_skipless_rmsNorm_zero [Nonempty d] (hA : A.χ = rmsNorm 0)
    (hE : θ.E.rank = Fintype.card d) (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d) :
    funDim A 0 θ + (L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
      ≤ Module.finrank ℝ (Params A dIn dOut) := by
  -- the linear map `(Y, β) ↦ cobDir θ Y + scaleDir θ β`, with antisymmetric `Y_ℓ`
  let Φ : (Fin (L + 1) → antisymmetric d) × (Fin (L + 1) → ℝ) →ₗ[ℝ] Params A dIn dOut :=
    ((cobDirLin θ).comp (LinearMap.compLeft (antisymmetric d).subtype (Fin (L + 1)))).coprod
      (scaleDirLin_rz θ)
  -- its directions are flat, since both summands are
  have hV : LinearMap.range Φ ≤ flat A 0 θ := by
    rintro _ ⟨p, rfl⟩
    rw [LinearMap.coprod_apply]
    exact Submodule.add_mem _
      (cobDir_mem_flat_skipless_rmsNorm' θ 0 hA (fun ℓ => (p.1 ℓ : Matrix d d ℝ))
        fun ℓ => (p.1 ℓ).2)
      (scaleDir_mem_flat_skipless_rmsNorm_zero θ hA p.2)
  -- it is injective (Lemma B.1 for `ε = 0`)
  have hinj : Function.Injective Φ := by
    intro p q hpq
    rw [LinearMap.coprod_apply, LinearMap.coprod_apply] at hpq
    have h' : cobDir θ (fun ℓ => (p.1 ℓ : Matrix d d ℝ)) + scaleDir θ p.2
        = cobDir θ (fun ℓ => (q.1 ℓ : Matrix d d ℝ)) + scaleDir θ q.2 := hpq
    obtain ⟨h1, h2⟩ := cobDir_add_scaleDir_injective θ hE hw (fun ℓ => (p.1 ℓ).2)
      (fun ℓ => (q.1 ℓ).2) h'
    exact Prod.ext (funext fun ℓ => Subtype.ext (congrFun h1 ℓ)) h2
  -- the domain has dimension `(L + 1) (d (d - 1) / 2 + 1)`
  have hdim : Module.finrank ℝ ((Fin (L + 1) → antisymmetric d) × (Fin (L + 1) → ℝ)) =
      (L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2 + 1) := by
    rw [Module.finrank_prod, Module.finrank_pi_fintype, finrank_antisymmetric, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul, Module.finrank_fin_fun]
    ring
  have h := funDim_add_finrank_le_of_le_flat' θ _ hV
  rwa [LinearMap.finrank_range_of_inj hinj, hdim] at h

/-- **Theorem 4.3 of the dimension paper for `ε = 0` at generic parameters:** for `d_in ≥ d ≥ 1`
and writes of at least `d` rows (MLP blocks of at least `d` hidden units), the functional
dimension of a network without skip connections under pre-RMSNorm with `ε = 0` is at most
`P − (L + 1) (d(d−1)/2 + 1)`. -/
theorem ae_funDim_add_le_skipless_rmsNorm_zero [Nonempty d]
    (μ : Measure (Params A dIn dOut)) [μ.IsAddHaarMeasure] (hA : A.χ = rmsNorm 0)
    (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hw : ∀ ℓ, Fintype.card d ≤ Fintype.card (A.w ℓ)) :
    ∀ᵐ θ ∂μ, funDim A 0 θ + (L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
      ≤ Module.finrank ℝ (Params A dIn dOut) := by
  -- the pointwise bound holds wherever `E` and the writes have rank `d`
  filter_upwards [ae_rank_E_write μ hdIn hw] with θ hθ
  exact funDim_add_le_skipless_rmsNorm_zero θ hA hθ.1 hθ.2

end General

section Gated

variable {σ : ℝ → ℝ} {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]

/-- Helper: `α ↦ rescaleDir θ α` is linear. -/
private noncomputable def rescaleDirLin_rz {χ : Matrix T d ℝ → Matrix T d ℝ}
    (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut) :
    (∀ ℓ, hid ℓ → ℝ) →ₗ[ℝ] Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut where
  toFun := rescaleDir θ
  map_add' α β := by
    apply Params.ext'
    · simp [rescaleDir]
    · intro ℓ
      ext k j
      cases j with
      | inl i => simp [rescaleDir]
      | inr i =>
        simp only [rescaleDir, Pi.add_apply, Params.add_read, Matrix.add_apply, Matrix.of_apply,
          Sum.elim_inr]
        ring
    · intro ℓ
      ext i k
      simp [rescaleDir, add_mul]
    · simp [rescaleDir]
  map_smul' c α := by
    apply Params.ext'
    · simp [rescaleDir]
    · intro ℓ
      ext k j
      cases j <;> simp [rescaleDir, mul_assoc]
    · intro ℓ
      ext i k
      simp [rescaleDir, mul_assoc]
    · simp [rescaleDir]

omit [Fintype T] [Fintype dIn] [Fintype dOut] in
/-- Helper (Lemma B.1 for `ε = 0`, gated blocks): if `E` and every write have rank `d` and no
value column of a read vanishes, `cobDir θ Y + scaleDir θ β + rescaleDir θ α` with antisymmetric
`Y_ℓ` determines `Y`, `β` and `α`. Block by block: `E` gives `Y_0, β_0`; the value columns of the
read of block `ℓ` give `α_ℓ`; its write gives `Y_{ℓ+1}, β_{ℓ+1}`. -/
private theorem cobDir_add_scaleDir_add_rescaleDir_injective_rz [Nonempty d]
    {χ : Matrix T d ℝ → Matrix T d ℝ}
    (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d) (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d)
    (hv : ∀ ℓ i, (fun k => θ.read ℓ k (Sum.inr i)) ≠ 0)
    {Y Y' : Fin (L + 1) → Matrix d d ℝ} (hY : ∀ ℓ, (Y ℓ)ᵀ = -Y ℓ) (hY' : ∀ ℓ, (Y' ℓ)ᵀ = -Y' ℓ)
    {β β' : Fin (L + 1) → ℝ} {α α' : ∀ ℓ, hid ℓ → ℝ}
    (h : cobDir θ Y + scaleDir θ β + rescaleDir θ α
      = cobDir θ Y' + scaleDir θ β' + rescaleDir θ α') :
    Y = Y' ∧ β = β' ∧ α = α' := by
  -- the embedding moves by `E Y_0 + β_0 E` (the rescalings leave `E` alone)
  have h0 : θ.E * Y 0 + β 0 • θ.E = θ.E * Y' 0 + β' 0 • θ.E := by
    have hE0 := congrArg Params.E h
    change θ.E * Y 0 + β 0 • θ.E + 0 = θ.E * Y' 0 + β' 0 • θ.E + 0 at hE0
    rwa [add_zero, add_zero] at hE0
  -- block `ℓ`: if `Y_ℓ = Y'_ℓ`, then `α_ℓ = α'_ℓ`, `Y_{ℓ+1} = Y'_{ℓ+1}`, `β_{ℓ+1} = β'_{ℓ+1}`
  have key : ∀ ℓ : Fin L, Y ℓ.castSucc = Y' ℓ.castSucc →
      α ℓ = α' ℓ ∧ Y ℓ.succ = Y' ℓ.succ ∧ β ℓ.succ = β' ℓ.succ := by
    intro ℓ hℓ
    -- the value column `e_i` moves by `-Y_ℓ e_i - α_i e_i` (the scales leave the reads alone);
    -- an entry `k` with `e_i k ≠ 0` gives `α_i = α'_i`
    have hα : α ℓ = α' ℓ := by
      funext i
      obtain ⟨k, hk⟩ := Function.ne_iff.mp (hv ℓ i)
      have hr := congrFun (congrFun (congrArg (fun η => η.read ℓ) h) k) (Sum.inr i)
      change -(Y ℓ.castSucc * θ.read ℓ) k (Sum.inr i) + 0 + -(α ℓ i) * θ.read ℓ k (Sum.inr i) =
        -(Y' ℓ.castSucc * θ.read ℓ) k (Sum.inr i) + 0 + -(α' ℓ i) * θ.read ℓ k (Sum.inr i) at hr
      rw [hℓ, add_right_inj] at hr
      exact neg_inj.mp (mul_right_cancel₀ hk hr)
    -- the write moves by `W Y_{ℓ+1} + β_{ℓ+1} W + diag(α_ℓ) W`, the last terms agree
    have hw' := congrArg (fun η => η.write ℓ) h
    change θ.write ℓ * Y ℓ.succ + β ℓ.succ • θ.write ℓ
        + Matrix.of (fun i k => α ℓ i * θ.write ℓ i k) =
      θ.write ℓ * Y' ℓ.succ + β' ℓ.succ • θ.write ℓ
        + Matrix.of (fun i k => α' ℓ i * θ.write ℓ i k) at hw'
    rw [hα, add_left_inj] at hw'
    exact ⟨hα, mul_add_smul_inj_rz (θ.write ℓ) (hw ℓ) (hY _) (hY' _) hw'⟩
  -- by induction along the network, `Y = Y'` and `β = β'`; then `α = α'`
  have hYβ : ∀ ℓ : Fin (L + 1), Y ℓ = Y' ℓ ∧ β ℓ = β' ℓ := by
    intro ℓ
    induction ℓ using Fin.induction with
    | zero => exact mul_add_smul_inj_rz θ.E hE (hY 0) (hY' 0) h0
    | succ ℓ ih => exact (key ℓ ih.1).2
  exact ⟨funext fun ℓ => (hYβ ℓ).1, funext fun ℓ => (hYβ ℓ).2,
    funext fun ℓ => (key ℓ (hYβ ℓ.castSucc).1).1⟩

/-- **Theorem 4.3 of the dimension paper for `ε = 0`, for gated blocks:** if `E` and every write
have rank `d ≥ 1` and no value column of a read vanishes, the functional dimension of a network of
gated blocks without skip connections under pre-RMSNorm with `ε = 0` is at most
`P − (L + 1) (d(d−1)/2 + 1) − s`, with `s` the number of hidden units. -/
theorem funDim_add_le_skipless_gated_rmsNorm_zero [Nonempty d]
    (θ : Params (Arch.gated (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d) (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d)
    (hv : ∀ ℓ i, (fun k => θ.read ℓ k (Sum.inr i)) ≠ 0) :
    funDim (Arch.gated σ (rmsNorm 0) hid) 0 θ
        + ((L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
          + ∑ ℓ, Fintype.card (hid ℓ))
      ≤ Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) := by
  -- the linear map `((Y, β), α) ↦ cobDir θ Y + scaleDir θ β + rescaleDir θ α`, with
  -- antisymmetric `Y_ℓ`
  let Φ : ((Fin (L + 1) → antisymmetric d) × (Fin (L + 1) → ℝ)) × (∀ ℓ, hid ℓ → ℝ) →ₗ[ℝ]
      Params (Arch.gated (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut :=
    (((cobDirLin θ).comp (LinearMap.compLeft (antisymmetric d).subtype (Fin (L + 1)))).coprod
      (scaleDirLin_rz θ)).coprod (rescaleDirLin_rz θ)
  -- its directions are flat, since the three summands are
  have hV : LinearMap.range Φ ≤ flat (Arch.gated σ (rmsNorm 0) hid) 0 θ := by
    rintro _ ⟨p, rfl⟩
    rw [LinearMap.coprod_apply, LinearMap.coprod_apply]
    exact Submodule.add_mem _ (Submodule.add_mem _
      (cobDir_mem_flat_skipless_rmsNorm' θ 0 rfl (fun ℓ => (p.1.1 ℓ : Matrix d d ℝ))
        fun ℓ => (p.1.1 ℓ).2)
      (scaleDir_mem_flat_skipless_rmsNorm_zero θ rfl p.1.2))
      (rescaleDir_mem_flat' θ 0 p.2)
  -- it is injective (Lemma B.1 for `ε = 0`)
  have hinj : Function.Injective Φ := by
    intro p q hpq
    rw [LinearMap.coprod_apply, LinearMap.coprod_apply, LinearMap.coprod_apply,
      LinearMap.coprod_apply] at hpq
    have h' : cobDir θ (fun ℓ => (p.1.1 ℓ : Matrix d d ℝ)) + scaleDir θ p.1.2 + rescaleDir θ p.2
        = cobDir θ (fun ℓ => (q.1.1 ℓ : Matrix d d ℝ)) + scaleDir θ q.1.2
          + rescaleDir θ q.2 := hpq
    obtain ⟨h1, h2, h3⟩ := cobDir_add_scaleDir_add_rescaleDir_injective_rz θ hE hw hv
      (fun ℓ => (p.1.1 ℓ).2) (fun ℓ => (q.1.1 ℓ).2) h'
    exact Prod.ext (Prod.ext (funext fun ℓ => Subtype.ext (congrFun h1 ℓ)) h2) h3
  -- the domain has dimension `(L + 1) (d (d - 1) / 2 + 1) + s`
  have hdim : Module.finrank ℝ
      (((Fin (L + 1) → antisymmetric d) × (Fin (L + 1) → ℝ)) × (∀ ℓ, hid ℓ → ℝ)) =
      (L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2 + 1) + ∑ ℓ, Fintype.card (hid ℓ) := by
    rw [Module.finrank_prod, Module.finrank_prod, Module.finrank_pi_fintype,
      finrank_antisymmetric, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
      Module.finrank_fin_fun, Module.finrank_pi_fintype]
    simp only [Module.finrank_fintype_fun_eq_card]
    ring
  have h := funDim_add_finrank_le_of_le_flat' θ _ hV
  rwa [LinearMap.finrank_range_of_inj hinj, hdim] at h

/-- **Theorem 4.3 of the dimension paper for `ε = 0`, for gated blocks, at generic parameters:**
for `d_in ≥ d ≥ 1` and at least `d` hidden units in every block, the functional dimension is at
most `P − (L + 1) (d(d−1)/2 + 1) − s`. -/
theorem ae_funDim_add_le_skipless_gated_rmsNorm_zero [Nonempty d]
    (μ : Measure (Params (Arch.gated (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, funDim (Arch.gated σ (rmsNorm 0) hid) 0 θ
        + ((L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
          + ∑ ℓ, Fintype.card (hid ℓ))
      ≤ Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) := by
  -- the pointwise bound holds wherever `E` and the writes have rank `d` and no value column of a
  -- read vanishes
  filter_upwards [ae_rank_E_write μ hdIn hhid, ae_value_ne_zero μ] with θ h1 h2
  exact funDim_add_le_skipless_gated_rmsNorm_zero θ h1.1 h1.2 h2

end Gated

end Skips
