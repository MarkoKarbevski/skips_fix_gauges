import SkipsLean.Dimension.UpperBoundResidualRMSNormZero

/-!
# Residual networks under pre-RMSNorm with `ε = 0`, ReLU, ReLU² and ReGLU blocks: the upper bound

Paper (skips paper), Theorem B.1 (iv): "Let the network be pre-RMSNorm with `ε = 0`, without
biases, with a ReLU, ReLU² or ReGLU block of width at least `d_model`. For generic parameters the
residual network has functional dimension `P − d_model (d_model − 1)/2 − 1 − s`".

Its proof, "The residual network": "a flat direction is the sum of a direction of the rotation
and scaling of all hidden states and a direction `ψ` of the weights of the block along which `B`
has derivative zero on the sphere of radius `√d_model`. […] makes `ψ` a rescaling of the units.
So `dim K(θ) = d_model (d_model − 1)/2 + 1 + s`."

Here: the half "at most" of this value, at any depth. For a residual network of MLP blocks with a
positively homogeneous activation (ReLU, ReLU²: `s` is the number of hidden units) or of gated
blocks with a positively homogeneous gate (ReGLU: `s` is twice the number of hidden units) under
pre-RMSNorm with `ε = 0`, the directions of the rotation of all hidden states, of their scaling,
and of the rescalings of the hidden units are flat and independent, so the functional dimension is
at most `P − (d(d−1)/2 + 1) − s`: at one parameter under the conditions of the proof (`E` of rank
`d ≥ 1`, no column of a read zero), and at almost every parameter for `d_in ≥ d`. No width of the
blocks is asked. The twin for `ε > 0` is `Residual/UpperBoundSymmetries.lean`; without the
rescalings, `Dimension/UpperBoundResidualRMSNormZero.lean`.

The functional dimension is Lean's `funDim`, over all inputs, with the derivative in the weights
taken to be `0` where the output is not differentiable, and with Lean's `rmsNorm 0`, which maps a
zero row to `0`. It is at least the paper's, which uses fewer inputs, so the bound holds for the
paper's. Not stated here: the half "at least".
-/

namespace Skips

open Matrix MeasureTheory

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {σ : ℝ → ℝ} {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]

/-! ### Helpers: the rotation and scaling of all hidden states, and the rescalings -/

omit [Fintype T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (the private `cancel_left_of_rank_rb0`): a matrix `M` of rank equal to its number of
columns cancels on the left, `M X = M Y → X = Y` (its kernel is `0` by rank–nullity). -/
private theorem cancel_left_of_rank_urz {m n k : Type*} [Fintype n] (M : Matrix m n ℝ)
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
/-- Helper (the private `antisymm_add_smul_one_inj_rb0`): an antisymmetric matrix plus a scalar
matrix determines both: the diagonal of an antisymmetric matrix vanishes. -/
private theorem antisymm_add_smul_one_inj_urz [Nonempty d] {X X' : Matrix d d ℝ}
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
/-- Helper (the private `mul_add_smul_inj_rb0`): if `M` has rank `d`, then `M X + b M` with
antisymmetric `X` determines `X` and `b`: it is `M (X + b 1)`. -/
private theorem mul_add_smul_inj_urz [Nonempty d] {m : Type*} (M : Matrix m d ℝ)
    (hM : M.rank = Fintype.card d) {X X' : Matrix d d ℝ} (hX : Xᵀ = -X) (hX' : X'ᵀ = -X')
    {b b' : ℝ} (h : M * X + b • M = M * X' + b' • M) : X = X' ∧ b = b' := by
  have h' : M * (X + b • (1 : Matrix d d ℝ)) = M * (X' + b' • 1) := by
    rw [Matrix.mul_add, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_one]
    exact h
  exact antisymm_add_smul_one_inj_urz hX hX' (cancel_left_of_rank_urz M hM h')

/-- Helper (the private `scaleDirLin_rb0`): `β ↦ scaleDir θ β` is linear. -/
private noncomputable def scaleDirLin_urz {A : Arch T d L} (θ : Params A dIn dOut) :
    (Fin (L + 1) → ℝ) →ₗ[ℝ] Params A dIn dOut where
  toFun := scaleDir θ
  map_add' β β' := by
    refine Params.ext' ?_ (fun ℓ => ?_) (fun ℓ => ?_) ?_ <;>
      simp only [scaleDir, Params.add_E, Params.add_read, Params.add_write, Params.add_D,
        Pi.add_apply, add_smul, add_zero]
  map_smul' c β := by
    refine Params.ext' ?_ (fun ℓ => ?_) (fun ℓ => ?_) ?_ <;>
      simp only [scaleDir, Params.smul_E, Params.smul_read, Params.smul_write, Params.smul_D,
        Pi.smul_apply, smul_eq_mul, mul_smul, smul_zero, RingHom.id_apply]

/-- Helper: the bound from the rotation and scaling of all hidden states and the symmetries
inside the blocks, under pre-RMSNorm with `ε = 0`. Let `ρ : V → Params` be linear and injective
with `E` component `0` (the directions of the rescalings). If the directions `ρ v` are flat and
`E` has rank `d ≥ 1`, then `fd ≤ P - (d(d-1)/2 + 1) - dim V`. -/
private theorem funDim_add_le_of_coScale_add_urz [Nonempty d] {A : Arch T d L}
    (θ : Params A dIn dOut) (hA : A.χ = rmsNorm 0) (hE : θ.E.rank = Fintype.card d)
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (ρ : V →ₗ[ℝ] Params A dIn dOut) (hρ : Function.Injective ρ) (hρE : ∀ v, (ρ v).E = 0)
    (hflat : ∀ v, ρ v ∈ flat A 1 θ) :
    funDim A 1 θ + ((Fintype.card d * (Fintype.card d - 1) / 2 + 1) + Module.finrank ℝ V)
      ≤ Module.finrank ℝ (Params A dIn dOut) := by
  -- the linear map `(Y, c) ↦ cobDir θ (fun _ => Y) + scaleDir θ (fun _ => c)`, `Y` antisymmetric
  let Ψ : antisymmetric d × ℝ →ₗ[ℝ] Params A dIn dOut :=
    ((cobDirLin θ).comp (LinearMap.pi fun _ => (antisymmetric d).subtype)).coprod
      ((scaleDirLin_urz θ).comp (LinearMap.pi fun _ => LinearMap.id))
  have hΨ : ∀ p : antisymmetric d × ℝ,
      Ψ p = cobDir θ (fun _ => (p.1 : Matrix d d ℝ)) + scaleDir θ (fun _ => p.2) := fun _ => rfl
  -- and with it the rescalings: `((Y, c), v) ↦ Ψ (Y, c) + ρ v`
  let Φ : (antisymmetric d × ℝ) × V →ₗ[ℝ] Params A dIn dOut := Ψ.coprod ρ
  have hΦ : ∀ p v, Φ (p, v) = Ψ p + ρ v := fun _ _ => rfl
  -- its directions are flat, since all summands are
  have hV : LinearMap.range Φ ≤ flat A 1 θ := by
    rintro _ ⟨⟨p, v⟩, rfl⟩
    rw [hΦ, hΨ]
    exact Submodule.add_mem _ (Submodule.add_mem _
      (cobDir_const_mem_flat_residual_rmsNorm_zero θ hA (p.1 : Matrix d d ℝ) p.1.2)
      (scaleDir_const_mem_flat_residual_rmsNorm_zero θ hA p.2)) (hflat v)
  -- it is injective: its `E` component is `E Y + c E = E (Y + c 1)` (the rescalings leave `E`
  -- alone), which gives `Y` and `c` since `E` has rank `d`; then `ρ v` gives `v`
  have hinj : Function.Injective Φ := by
    rintro ⟨p, v⟩ ⟨q, v'⟩ h
    rw [hΦ, hΦ] at h
    have h0 : θ.E * (p.1 : Matrix d d ℝ) + p.2 • θ.E = θ.E * (q.1 : Matrix d d ℝ) + q.2 • θ.E := by
      have hE0 := congrArg Params.E h
      rw [Params.add_E, Params.add_E, hρE, hρE, add_zero, add_zero] at hE0
      exact hE0
    obtain ⟨h1, h2⟩ := mul_add_smul_inj_urz θ.E hE p.1.2 q.1.2 h0
    obtain rfl : p = q := Prod.ext (Subtype.ext h1) h2
    exact Prod.ext rfl (hρ (add_left_cancel h))
  -- the domain has dimension `d (d - 1) / 2 + 1 + dim V`
  have hdim : Module.finrank ℝ ((antisymmetric d × ℝ) × V)
      = (Fintype.card d * (Fintype.card d - 1) / 2 + 1) + Module.finrank ℝ V := by
    rw [Module.finrank_prod, Module.finrank_prod, finrank_antisymmetric, Module.finrank_self]
  have h := funDim_add_finrank_le_of_le_flat' θ _ hV
  rwa [LinearMap.finrank_range_of_inj hinj, hdim] at h

omit [Fintype T] in
/-- Helper (the private `rank_eq_of_isUnit_det_submatrix_rb0`): a matrix with `d` columns has
rank `d` if some `d` of its rows form an invertible matrix. -/
private theorem rank_eq_of_isUnit_det_submatrix_urz {m : Type*} (M : Matrix m d ℝ) (ρ : d ↪ m)
    (h : IsUnit (M.submatrix ρ id).det) : M.rank = Fintype.card d :=
  le_antisymm (Matrix.rank_le_card_width M)
    ((Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).2 h)).symm.le.trans
      (Matrix.rank_submatrix_le M ρ id))

/-- Helper (the private `ae_rank_E_rb0`): at generic parameters `E` has rank `d`, when
`d_in ≥ d`. -/
private theorem ae_rank_E_urz {A : Arch T d L} (μ : Measure (Params A dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn) :
    ∀ᵐ η ∂μ, η.E.rank = Fintype.card d := by
  -- `d` rows of `E`, invertible at generic parameters
  obtain ⟨ρ⟩ := Function.Embedding.nonempty_of_card_le hdIn
  filter_upwards [ae_isUnit_det_submatrix μ] with η hη
  exact rank_eq_of_isUnit_det_submatrix_urz η.E ρ (hη.2.2.1 ρ)

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (the private `finrank_hidFun`): the numbers of the rescalings of the hidden units form
a space of dimension `s`, the number of hidden units. -/
private theorem finrank_hidFun_urz :
    Module.finrank ℝ (∀ ℓ, hid ℓ → ℝ) = ∑ ℓ, Fintype.card (hid ℓ) := by
  rw [Module.finrank_pi_fintype]
  simp only [Module.finrank_fintype_fun_eq_card]

/-- Helper (the private `mlpRescaleLin`): `α ↦ rescaleDirMlp k θ α` is linear. -/
private noncomputable def mlpRescaleLin_urz {χ : Matrix T d ℝ → Matrix T d ℝ} (k : ℕ)
    (θ : Params (Arch.mlp (T := T) (d := d) σ χ hid) dIn dOut) :
    (∀ ℓ, hid ℓ → ℝ) →ₗ[ℝ] Params (Arch.mlp (T := T) (d := d) σ χ hid) dIn dOut where
  toFun := rescaleDirMlp k θ
  map_add' α β := by
    apply Params.ext'
    · simp [rescaleDirMlp]
    · intro ℓ
      ext a i
      simp only [rescaleDirMlp, Pi.add_apply, Params.add_read, Matrix.add_apply, Matrix.of_apply]
      ring
    · intro ℓ
      ext i a
      simp only [rescaleDirMlp, Pi.add_apply, Params.add_write, Matrix.add_apply, Matrix.of_apply]
      ring
    · simp [rescaleDirMlp]
  map_smul' c α := by
    apply Params.ext'
    · simp [rescaleDirMlp]
    · intro ℓ
      ext a i
      simp only [rescaleDirMlp, Pi.smul_apply, Params.smul_read, Matrix.smul_apply,
        Matrix.of_apply, smul_eq_mul, RingHom.id_apply]
      ring
    · intro ℓ
      ext i a
      simp only [rescaleDirMlp, Pi.smul_apply, Params.smul_write, Matrix.smul_apply,
        Matrix.of_apply, smul_eq_mul, RingHom.id_apply]
      ring
    · simp [rescaleDirMlp]

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (the private `mlpRescaleLin_injective`): if no column of a read vanishes,
`α ↦ rescaleDirMlp k θ α` is injective: the read column `c_i` moves by `α_i c_i`. -/
private theorem mlpRescaleLin_injective_urz {χ : Matrix T d ℝ → Matrix T d ℝ} (k : ℕ)
    (θ : Params (Arch.mlp (T := T) (d := d) σ χ hid) dIn dOut)
    (hc : ∀ ℓ i, (fun a => θ.read ℓ a i) ≠ 0) :
    Function.Injective (mlpRescaleLin_urz k θ) := by
  intro α α' h
  have h' : rescaleDirMlp k θ α = rescaleDirMlp k θ α' := h
  funext ℓ i
  -- an entry `a` with `c_i a ≠ 0`
  obtain ⟨a, ha⟩ := Function.ne_iff.mp (hc ℓ i)
  have hr := congrFun (congrFun (congrArg (fun η => η.read ℓ) h') a) i
  change α ℓ i * θ.read ℓ a i = α' ℓ i * θ.read ℓ a i at hr
  exact mul_right_cancel₀ ha hr

/-- Helper (the private `valueRescaleLin`): `α ↦ rescaleDir θ α` is linear. -/
private noncomputable def valueRescaleLin_urz {χ : Matrix T d ℝ → Matrix T d ℝ}
    (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut) :
    (∀ ℓ, hid ℓ → ℝ) →ₗ[ℝ] Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut where
  toFun := rescaleDir θ
  map_add' α β := by
    apply Params.ext'
    · simp [rescaleDir]
    · intro ℓ
      ext a j
      cases j with
      | inl i => simp [rescaleDir]
      | inr i =>
        simp only [rescaleDir, Pi.add_apply, Params.add_read, Matrix.add_apply, Matrix.of_apply,
          Sum.elim_inr]
        ring
    · intro ℓ
      ext i a
      simp [rescaleDir, add_mul]
    · simp [rescaleDir]
  map_smul' c α := by
    apply Params.ext'
    · simp [rescaleDir]
    · intro ℓ
      ext a j
      cases j <;> simp [rescaleDir, mul_assoc]
    · intro ℓ
      ext i a
      simp [rescaleDir, mul_assoc]
    · simp [rescaleDir]

/-- Helper (the private `gateRescaleLin`): `β ↦ rescaleDirGate k θ β` is linear. -/
private noncomputable def gateRescaleLin_urz {χ : Matrix T d ℝ → Matrix T d ℝ} (k : ℕ)
    (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut) :
    (∀ ℓ, hid ℓ → ℝ) →ₗ[ℝ] Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut where
  toFun := rescaleDirGate k θ
  map_add' α β := by
    apply Params.ext'
    · simp [rescaleDirGate]
    · intro ℓ
      ext a j
      cases j with
      | inl i =>
        simp only [rescaleDirGate, Pi.add_apply, Params.add_read, Matrix.add_apply,
          Matrix.of_apply, Sum.elim_inl]
        ring
      | inr i => simp [rescaleDirGate]
    · intro ℓ
      ext i a
      simp only [rescaleDirGate, Pi.add_apply, Params.add_write, Matrix.add_apply,
        Matrix.of_apply]
      ring
    · simp [rescaleDirGate]
  map_smul' c α := by
    apply Params.ext'
    · simp [rescaleDirGate]
    · intro ℓ
      ext a j
      cases j with
      | inl i =>
        simp only [rescaleDirGate, Pi.smul_apply, Params.smul_read, Matrix.smul_apply,
          Matrix.of_apply, Sum.elim_inl, smul_eq_mul, RingHom.id_apply]
        ring
      | inr i => simp [rescaleDirGate]
    · intro ℓ
      ext i a
      simp only [rescaleDirGate, Pi.smul_apply, Params.smul_write, Matrix.smul_apply,
        Matrix.of_apply, smul_eq_mul, RingHom.id_apply]
      ring
    · simp [rescaleDirGate]

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (the private `valueGateRescaleLin_injective`): if no value column and no gate column of
a read vanishes, `(α, β) ↦ rescaleDir θ α + rescaleDirGate k θ β` is injective: the gate column
`g_i` moves by `β_i g_i` and the value column `e_i` by `-α_i e_i`. -/
private theorem valueGateRescaleLin_injective_urz {χ : Matrix T d ℝ → Matrix T d ℝ} (k : ℕ)
    (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut)
    (hv : ∀ ℓ i, (fun a => θ.read ℓ a (Sum.inr i)) ≠ 0)
    (hg : ∀ ℓ i, (fun a => θ.read ℓ a (Sum.inl i)) ≠ 0) :
    Function.Injective ((valueRescaleLin_urz θ).coprod (gateRescaleLin_urz k θ)) := by
  rintro ⟨α, β⟩ ⟨α', β'⟩ h
  have h' : rescaleDir θ α + rescaleDirGate k θ β = rescaleDir θ α' + rescaleDirGate k θ β' := h
  -- the gate columns: an entry `a` with `g_i a ≠ 0` gives `β_i = β'_i`
  have hβ : β = β' := by
    funext ℓ i
    obtain ⟨a, ha⟩ := Function.ne_iff.mp (hg ℓ i)
    have hr := congrFun (congrFun (congrArg (fun η => η.read ℓ) h') a) (Sum.inl i)
    change 0 + β ℓ i * θ.read ℓ a (Sum.inl i) = 0 + β' ℓ i * θ.read ℓ a (Sum.inl i) at hr
    rw [zero_add, zero_add] at hr
    exact mul_right_cancel₀ ha hr
  -- the value columns: an entry `a` with `e_i a ≠ 0` gives `α_i = α'_i`
  have hα : α = α' := by
    funext ℓ i
    obtain ⟨a, ha⟩ := Function.ne_iff.mp (hv ℓ i)
    have hr := congrFun (congrFun (congrArg (fun η => η.read ℓ) h') a) (Sum.inr i)
    change -(α ℓ i) * θ.read ℓ a (Sum.inr i) + 0 = -(α' ℓ i) * θ.read ℓ a (Sum.inr i) + 0 at hr
    rw [add_zero, add_zero] at hr
    exact neg_inj.mp (mul_right_cancel₀ ha hr)
  exact Prod.ext hα hβ

/-- **Theorem B.1 (iv) of the skips paper, the residual network, the half "at most", under the
conditions of the proof:** for a residual network of MLP blocks with `σ(λ z) = λ^k σ(z)` for
`λ > 0` under pre-RMSNorm with `ε = 0`, if `E` has rank `d ≥ 1` and no column of a read is zero,
the functional dimension is at most `P − (d(d−1)/2 + 1) − s`, `s` the number of hidden units. -/
theorem funDim_add_le_residual_mlp_rescale_rmsNorm_zero [Nonempty d] {k : ℕ}
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d)
    (hc : ∀ ℓ i, (fun a => θ.read ℓ a i) ≠ 0) :
    funDim (Arch.mlp σ (rmsNorm 0) hid) 1 θ
        + ((Fintype.card d * (Fintype.card d - 1) / 2 + 1) + ∑ ℓ, Fintype.card (hid ℓ))
      ≤ Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) := by
  -- the flat directions `cobDir θ (fun _ => Y) + scaleDir θ (fun _ => c) + rescaleDirMlp k θ α`,
  -- of dimension `d (d - 1) / 2 + 1 + s`
  have h := funDim_add_le_of_coScale_add_urz θ rfl hE (mlpRescaleLin_urz k θ)
    (mlpRescaleLin_injective_urz k θ hc) (fun _ => rfl) (fun α => rescaleDirMlp_mem_flat hσ θ 1 α)
  rwa [finrank_hidFun_urz] at h

/-- The bound of `funDim_add_le_residual_mlp_rescale_rmsNorm_zero` at almost every parameter, for
`d_in ≥ d ≥ 1`. -/
theorem ae_funDim_add_le_residual_mlp_rescale_rmsNorm_zero [Nonempty d] {k : ℕ}
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn) :
    ∀ᵐ θ ∂μ, funDim (Arch.mlp σ (rmsNorm 0) hid) 1 θ
        + ((Fintype.card d * (Fintype.card d - 1) / 2 + 1) + ∑ ℓ, Fintype.card (hid ℓ))
      ≤ Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) := by
  -- the pointwise bound holds wherever `E` has rank `d` and no column of a read vanishes
  filter_upwards [ae_rank_E_urz μ hdIn, ae_read_col_ne_zero μ] with θ h1 h2
  exact funDim_add_le_residual_mlp_rescale_rmsNorm_zero hσ θ h1 h2

/-- **Theorem B.1 (iv) of the skips paper, the residual network, the half "at most", for ReLU
blocks at generic parameters:** under pre-RMSNorm with `ε = 0`, with `d_in ≥ d ≥ 1`, the
functional dimension is at most `P − d(d−1)/2 − 1 − s`. -/
theorem ae_funDim_add_le_residual_relu_rmsNorm_zero [Nonempty d]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn) :
    ∀ᵐ θ ∂μ, funDim (Arch.mlp relu (rmsNorm 0) hid) 1 θ
        + ((Fintype.card d * (Fintype.card d - 1) / 2 + 1) + ∑ ℓ, Fintype.card (hid ℓ))
      ≤ Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut) := by
  -- ReLU is positively homogeneous of degree `1`
  exact ae_funDim_add_le_residual_mlp_rescale_rmsNorm_zero relu_homogeneous μ hdIn

/-- **Theorem B.1 (iv) of the skips paper, the residual network, the half "at most", for ReLU²
blocks at generic parameters.** -/
theorem ae_funDim_add_le_residual_reluSq_rmsNorm_zero [Nonempty d]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) reluSq (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn) :
    ∀ᵐ θ ∂μ, funDim (Arch.mlp reluSq (rmsNorm 0) hid) 1 θ
        + ((Fintype.card d * (Fintype.card d - 1) / 2 + 1) + ∑ ℓ, Fintype.card (hid ℓ))
      ≤ Module.finrank ℝ
          (Params (Arch.mlp (T := T) (d := d) reluSq (rmsNorm 0) hid) dIn dOut) := by
  -- ReLU² is positively homogeneous of degree `2`
  exact ae_funDim_add_le_residual_mlp_rescale_rmsNorm_zero reluSq_homogeneous μ hdIn

/-- **Theorem B.1 (iv) of the skips paper, the residual network, the half "at most", for gated
blocks under the conditions of the proof:** for a residual network of gated blocks whose gate has
`σ(λ z) = λ^k σ(z)` for `λ > 0`, under pre-RMSNorm with `ε = 0`, if `E` has rank `d ≥ 1` and no
value column and no gate column of a read is zero, the functional dimension is at most
`P − (d(d−1)/2 + 1) − s`, `s` twice the number of hidden units. -/
theorem funDim_add_le_residual_gated_gate_rmsNorm_zero [Nonempty d] {k : ℕ}
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (θ : Params (Arch.gated (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d)
    (hv : ∀ ℓ i, (fun a => θ.read ℓ a (Sum.inr i)) ≠ 0)
    (hg : ∀ ℓ i, (fun a => θ.read ℓ a (Sum.inl i)) ≠ 0) :
    funDim (Arch.gated σ (rmsNorm 0) hid) 1 θ
        + ((Fintype.card d * (Fintype.card d - 1) / 2 + 1) + 2 * ∑ ℓ, Fintype.card (hid ℓ))
      ≤ Module.finrank ℝ
          (Params (Arch.gated (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) := by
  -- the flat directions `cobDir θ (fun _ => Y) + scaleDir θ (fun _ => c) + rescaleDir θ α
  -- + rescaleDirGate k θ β`, of dimension `d (d - 1) / 2 + 1 + 2 s`
  have h := funDim_add_le_of_coScale_add_urz θ rfl hE
    ((valueRescaleLin_urz θ).coprod (gateRescaleLin_urz k θ))
    (valueGateRescaleLin_injective_urz k θ hv hg)
    (fun _ => show (0 : Matrix dIn d ℝ) + 0 = 0 from add_zero 0)
    (fun p => Submodule.add_mem _ (rescaleDir_mem_flat' θ 1 p.1)
      (rescaleDirGate_mem_flat hσ θ 1 p.2))
  rwa [Module.finrank_prod, finrank_hidFun_urz, ← two_mul] at h

/-- The bound of `funDim_add_le_residual_gated_gate_rmsNorm_zero` at almost every parameter, for
`d_in ≥ d ≥ 1`. -/
theorem ae_funDim_add_le_residual_gated_gate_rmsNorm_zero [Nonempty d] {k : ℕ}
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (μ : Measure (Params (Arch.gated (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn) :
    ∀ᵐ θ ∂μ, funDim (Arch.gated σ (rmsNorm 0) hid) 1 θ
        + ((Fintype.card d * (Fintype.card d - 1) / 2 + 1) + 2 * ∑ ℓ, Fintype.card (hid ℓ))
      ≤ Module.finrank ℝ
          (Params (Arch.gated (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) := by
  -- the pointwise bound holds wherever `E` has rank `d` and no value column and no gate column
  -- of a read vanishes
  filter_upwards [ae_rank_E_urz μ hdIn, ae_value_ne_zero μ, ae_gate_ne_zero μ] with θ h1 h2 h3
  exact funDim_add_le_residual_gated_gate_rmsNorm_zero hσ θ h1 h2 h3

/-- **Theorem B.1 (iv) of the skips paper, the residual network, the half "at most", for ReGLU
blocks at generic parameters:** under pre-RMSNorm with `ε = 0`, with `d_in ≥ d ≥ 1`, the
functional dimension is at most `P − d(d−1)/2 − 1 − s`, `s = 2 d_hidden`. -/
theorem ae_funDim_add_le_residual_reglu_rmsNorm_zero [Nonempty d]
    (μ : Measure (Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn) :
    ∀ᵐ θ ∂μ, funDim (Arch.gated relu (rmsNorm 0) hid) 1 θ
        + ((Fintype.card d * (Fintype.card d - 1) / 2 + 1) + 2 * ∑ ℓ, Fintype.card (hid ℓ))
      ≤ Module.finrank ℝ
          (Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut) := by
  -- ReLU is positively homogeneous of degree `1`
  exact ae_funDim_add_le_residual_gated_gate_rmsNorm_zero relu_homogeneous μ hdIn

end Skips
