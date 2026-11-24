import SkipsLean.Dimension.UpperBoundRMSNormZero
import SkipsLean.Dimension.RescalingGate
import SkipsLean.OneBlock.Common
import SkipsLean.OneBlock.SkiplessHomogeneousRMSZero

/-!
# One skipless block under pre-RMSNorm with `ε = 0`, ReGLU: the bound

Paper (skips paper), Theorem B.1 (iv): "Let the network be pre-RMSNorm with `ε = 0`, without
biases, with a ReLU, ReLU² or ReGLU block of width at least `d_model`. For generic parameters the
residual network has functional dimension `P − d_model (d_model − 1)/2 − 1 − s`, and the skipless
network at most `P − d_model² − d_model (d_model − 1)/2 − 1 − s`, with equality for ReLU and ReLU²
blocks."

Its proof, "Part (iv)": "With `ε = 0`, `N_ε(h) = √d_model h/‖h‖` depends only on the direction of
`h`, and `B(λ n) = λ^k B(n)` for `λ > 0`, so `N_ε(B(N_ε(h))) = N_ε(B(h))`: the skipless network
computes `x ↦ N_ε(B(x E)) D`. Its normalization before the block drops out, which leaves the
changes of basis `GL(d_model)` at `h_0` and `CO(d_model)` at `h_1`", and "The skipless network:
the bound. The changes of basis in `GL(d_model)` at `h_0` and in `CO(d_model)` at `h_1` and the
symmetries inside the block preserve the function. […] For generic parameters these directions
are independent, as in Step 3 of part (i). So
`dim K(θ) ≥ d_model² + d_model (d_model − 1)/2 + 1 + s`, which is the bound."

Here, for one gated block whose gate is positively homogeneous of degree `k` (ReGLU: `k = 1`), so
that the block is positively homogeneous of degree `k + 1` in its input; `s` is twice the number
of hidden units (the rescaling of the value and the rescaling of the gate of every hidden unit,
`Dimension/Rescaling.lean` and `Dimension/RescalingGate.lean`): the direction of a change of basis
`I + τ X` at `h_0`, for every matrix `X`, is flat under pre-RMSNorm with `ε = 0`; the bound at one
parameter under the conditions of the proof (`E` and the write of rank `d`, no gate column and no
value column of the read zero); the bound at almost every parameter for a ReGLU block of width at
least `d`. The twin for ReLU and ReLU² blocks is `OneBlock/SkiplessHomogeneousRMSZero.lean`.

The functional dimension is Lean's `funDim`, over all inputs, with the derivative in the weights
taken to be `0` where the output is not differentiable, and with Lean's `rmsNorm 0`, which maps a
zero row to `0`. It is at least the paper's, which uses fewer inputs, so the bound holds for the
paper's. Not stated here: the value for the residual network.
-/

namespace Skips

open Matrix MeasureTheory

variable {T d dIn dOut : Type*} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {σ : ℝ → ℝ} {hid : Fin 1 → Type} [∀ ℓ, Fintype (hid ℓ)]

/-- **Proof of Theorem B.1 (iv) of the skips paper, "Its normalization before the block drops
out", for a gated block:** for one skipless gated block whose gate has `σ(λ z) = λ^k σ(z)` for
`λ > 0`, under pre-RMSNorm with `ε = 0`, the direction of the change of basis `I + τ X` at `h_0`
(`E X` at `E`, `−X W_read` at `W_read`) is flat, for every matrix `X`. -/
theorem cobDir_zero_mem_flat_skipless_gated_homogeneous_rmsNorm_zero {k : ℕ}
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (θ : Params (Arch.gated (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) (X : Matrix d d ℝ) :
    cobDir θ ![X, 0] ∈ flat (Arch.gated σ (rmsNorm 0) hid) 0 θ := by
  -- the gated block is positively homogeneous of degree `k + 1` row by row
  exact cobDir_zero_mem_flat_skipless_rmsNorm_zero_of_rowHomogeneous rfl
    (rowHomogeneous_gated hσ (rmsNorm 0) hid) θ X

omit [Fintype T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (the private `cancel_left_of_rank_shz` of `OneBlock/SkiplessHomogeneousRMSZero.lean`):
a matrix `M` of rank equal to its number of columns cancels on the left, `M X = M Y → X = Y` (its
kernel is `0` by rank–nullity). -/
private theorem cancel_left_of_rank_shg {m n k : Type*} [Fintype n] (M : Matrix m n ℝ)
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
/-- Helper: if `Y + b I = 0` with `Y` antisymmetric, then `Y = 0` and `b = 0`: the diagonal of an
antisymmetric matrix vanishes, so a diagonal entry gives `b = 0`. -/
private theorem antisymm_add_smul_one_eq_zero_shg [Nonempty d] {Y : Matrix d d ℝ}
    (hY : Yᵀ = -Y) {b : ℝ} (h : Y + b • (1 : Matrix d d ℝ) = 0) : Y = 0 ∧ b = 0 := by
  obtain ⟨k⟩ := ‹Nonempty d›
  -- the diagonal entry `(k, k)` of `Y` vanishes
  have hd : Y k k = 0 := by
    have := congrFun (congrFun hY k) k
    rw [transpose_apply, Matrix.neg_apply] at this
    linarith
  -- so the entry `(k, k)` of `Y + b I` is `b`
  have hk := congrFun (congrFun h k) k
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one, hd,
    zero_add, Matrix.zero_apply] at hk
  subst hk
  simpa using h

omit [Fintype T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: a matrix and an antisymmetric matrix `(X, Y)`, as the family `![X, Y]` of matrices on
the two hidden states, linearly. -/
private noncomputable def pairLin_shg :
    (Matrix d d ℝ × antisymmetric d) →ₗ[ℝ] (Fin (1 + 1) → Matrix d d ℝ) where
  toFun p := ![p.1, (p.2 : Matrix d d ℝ)]
  map_add' p q := by
    funext i
    fin_cases i <;> rfl
  map_smul' c p := by
    funext i
    fin_cases i <;> rfl

/-- Helper: `α ↦ rescaleDir θ α` is linear (a copy of the private `rescaleDirLinValue` of
`Dimension/RescalingGate.lean`). -/
private noncomputable def rescaleDirLin_shg
    (θ : Params (Arch.gated (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) :
    (∀ ℓ, hid ℓ → ℝ) →ₗ[ℝ] Params (Arch.gated (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut where
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

/-- Helper: `β ↦ rescaleDirGate k θ β` is linear (a copy of the private `rescaleDirGateLin` of
`Dimension/RescalingGate.lean`). -/
private noncomputable def rescaleDirGateLin_shg (k : ℕ)
    (θ : Params (Arch.gated (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) :
    (∀ ℓ, hid ℓ → ℝ) →ₗ[ℝ] Params (Arch.gated (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut where
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

/-- **Theorem B.1 (iv) of the skips paper, the skipless network, the bound, for a gated block
under the conditions of the proof:** for one skipless gated block with a positively homogeneous
gate under pre-RMSNorm with `ε = 0`, if `E` and the write have rank `d ≥ 1` and no value column
and no gate column of the read is zero, the functional dimension is at most
`P − d² − (d(d−1)/2 + 1) − s`, where `s` is twice the number of hidden units. -/
theorem funDim_add_le_skipless_gated_homogeneous_rmsNorm_zero [Nonempty d] {k : ℕ}
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (θ : Params (Arch.gated (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d) (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d)
    (hv : ∀ ℓ i, (fun a => θ.read ℓ a (Sum.inr i)) ≠ 0)
    (hg : ∀ ℓ i, (fun a => θ.read ℓ a (Sum.inl i)) ≠ 0) :
    funDim (Arch.gated σ (rmsNorm 0) hid) 0 θ
        + (Fintype.card d ^ 2 + (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
          + 2 * Fintype.card (hid 0))
      ≤ Module.finrank ℝ
          (Params (Arch.gated (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) := by
  -- the linear map `(((X, Y), c), (α, β)) ↦ cobDir θ ![X, Y] + c scaleDir θ ![0, 1]
  -- + rescaleDir θ α + rescaleDirGate k θ β` with antisymmetric `Y`: the changes of basis `GL(d)`
  -- at `h_0` and `CO(d)` at `h_1`, the rescalings of the values and of the gates
  let Φ : ((Matrix d d ℝ × antisymmetric d) × ℝ) × ((∀ ℓ, hid ℓ → ℝ) × (∀ ℓ, hid ℓ → ℝ)) →ₗ[ℝ]
      Params (Arch.gated (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut :=
    (((cobDirLin θ).comp pairLin_shg).coprod
      (LinearMap.toSpanSingleton ℝ _ (scaleDir θ ![0, 1]))).coprod
      ((rescaleDirLin_shg θ).coprod (rescaleDirGateLin_shg k θ))
  -- its directions are flat, since the summands are
  have hV : LinearMap.range Φ ≤ flat (Arch.gated σ (rmsNorm 0) hid) 0 θ := by
    rintro _ ⟨p, rfl⟩
    rw [LinearMap.coprod_apply, LinearMap.coprod_apply, LinearMap.coprod_apply]
    refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_)
      (Submodule.add_mem _ (rescaleDir_mem_flat' θ 0 p.2.1)
        (rescaleDirGate_mem_flat hσ θ 0 p.2.2))
    · -- `cobDir θ ![X, Y] = cobDir θ ![X, 0] + cobDir θ ![0, Y]`: the change of basis `I + τ X`
      -- at `h_0` (Theorem 1) and the orthogonal one `exp (τ Y)` at `h_1`
      have hsplit : pairLin_shg p.1.1 = ![p.1.1.1, 0] + ![0, (p.1.1.2 : Matrix d d ℝ)] := by
        funext i
        fin_cases i <;> simp [pairLin_shg]
      rw [LinearMap.comp_apply, hsplit, map_add, cobDirLin_apply, cobDirLin_apply]
      refine Submodule.add_mem _
        (cobDir_zero_mem_flat_skipless_gated_homogeneous_rmsNorm_zero hσ θ p.1.1.1) ?_
      refine cobDir_mem_flat_skipless_rmsNorm' θ 0 rfl _ fun ℓ => ?_
      fin_cases ℓ
      · simp
      · exact p.1.1.2.2
    · -- the scale `c` at `h_1`
      rw [LinearMap.toSpanSingleton_apply]
      exact Submodule.smul_mem _ _ (scaleDir_mem_flat_skipless_rmsNorm_zero θ rfl _)
  -- it is injective (Lemma B.1)
  have hinj : Function.Injective Φ := by
    refine (injective_iff_map_eq_zero Φ).2 fun p hp => ?_
    obtain ⟨⟨⟨X, Y⟩, c⟩, α, β⟩ := p
    rw [LinearMap.coprod_apply, LinearMap.coprod_apply, LinearMap.coprod_apply] at hp
    -- the embedding moves by `E X` (no scale at `h_0`, the rescalings leave `E` alone): `X = 0`
    have hX : X = 0 := by
      have h := congrArg Params.E hp
      change θ.E * X + c • ((0 : ℝ) • θ.E) + (0 + 0) = 0 at h
      rw [zero_smul, smul_zero, add_zero, add_zero, add_zero] at h
      exact cancel_left_of_rank_shg θ.E hE (h.trans (Matrix.mul_zero _).symm)
    subst hX
    -- the gate column `i` of the read moves by `β_i` times itself (the rescaling of the values
    -- leaves it alone); an entry `a` with `W_read a (inl i) ≠ 0` gives `β_i = 0`
    have hβ : β = 0 := by
      funext ℓ
      obtain rfl : ℓ = 0 := Subsingleton.elim ℓ 0
      funext i
      obtain ⟨a, ha⟩ := Function.ne_iff.mp (hg 0 i)
      have h := congrArg (fun η => η.read 0 a (Sum.inl i)) hp
      change -((0 : Matrix d d ℝ) * θ.read 0) a (Sum.inl i)
        + c • (0 : Matrix d (hid 0 ⊕ hid 0) ℝ) a (Sum.inl i)
        + (0 + β 0 i * θ.read 0 a (Sum.inl i)) = 0 at h
      simp only [Matrix.zero_mul, neg_zero, Matrix.zero_apply, smul_zero, zero_add] at h
      exact (mul_eq_zero.mp h).resolve_right ha
    subst hβ
    -- the value column `i` of the read moves by `-α_i` times itself (the rescaling of the gates
    -- leaves it alone); an entry `a` with `W_read a (inr i) ≠ 0` gives `α_i = 0`
    have hα : α = 0 := by
      funext ℓ
      obtain rfl : ℓ = 0 := Subsingleton.elim ℓ 0
      funext i
      obtain ⟨a, ha⟩ := Function.ne_iff.mp (hv 0 i)
      have h := congrArg (fun η => η.read 0 a (Sum.inr i)) hp
      change -((0 : Matrix d d ℝ) * θ.read 0) a (Sum.inr i)
        + c • (0 : Matrix d (hid 0 ⊕ hid 0) ℝ) a (Sum.inr i)
        + (-(α 0 i) * θ.read 0 a (Sum.inr i) + 0) = 0 at h
      simp only [Matrix.zero_mul, neg_zero, Matrix.zero_apply, smul_zero, zero_add,
        add_zero] at h
      exact neg_eq_zero.mp ((mul_eq_zero.mp h).resolve_right ha)
    subst hα
    -- the write moves by `W_write (Y + c I)`, and `W_write` has rank `d`
    have hYc : (Y : Matrix d d ℝ) + c • (1 : Matrix d d ℝ) = 0 := by
      have h := congrArg (fun η => η.write 0) hp
      change θ.write 0 * (Y : Matrix d d ℝ) + c • ((1 : ℝ) • θ.write 0)
        + (Matrix.of (fun i a => (0 : ∀ ℓ, hid ℓ → ℝ) 0 i * θ.write 0 i a)
          + Matrix.of (fun i a => -((k : ℝ) * (0 : ∀ ℓ, hid ℓ → ℝ) 0 i) * θ.write 0 i a))
        = 0 at h
      have h0 : Matrix.of (fun i a => (0 : ∀ ℓ, hid ℓ → ℝ) 0 i * θ.write 0 i a)
          + Matrix.of (fun i a => -((k : ℝ) * (0 : ∀ ℓ, hid ℓ → ℝ) 0 i) * θ.write 0 i a)
          = 0 := by
        ext i a
        simp
      rw [h0, add_zero, one_smul] at h
      apply cancel_left_of_rank_shg (θ.write 0) (hw 0)
      rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one, Matrix.mul_zero]
      exact h
    obtain ⟨hY, hc0⟩ := antisymm_add_smul_one_eq_zero_shg Y.2 hYc
    obtain rfl : Y = 0 := Subtype.ext hY
    subst hc0
    rfl
  -- the domain has dimension `d² + (d (d - 1) / 2 + 1) + 2 s`
  have hdim : Module.finrank ℝ
      (((Matrix d d ℝ × antisymmetric d) × ℝ) × ((∀ ℓ, hid ℓ → ℝ) × (∀ ℓ, hid ℓ → ℝ))) =
      Fintype.card d ^ 2 + (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
        + 2 * Fintype.card (hid 0) := by
    rw [Module.finrank_prod, Module.finrank_prod, Module.finrank_prod, Module.finrank_prod,
      Module.finrank_matrix, finrank_antisymmetric, Module.finrank_self,
      Module.finrank_pi_fintype, Fin.sum_univ_one]
    simp only [Module.finrank_fintype_fun_eq_card]
    ring
  have h := funDim_add_finrank_le_of_le_flat' θ _ hV
  rwa [LinearMap.finrank_range_of_inj hinj, hdim] at h

/-- **Theorem B.1 (iv) of the skips paper, the skipless network, for a ReGLU block of width at
least `d` at generic parameters:** under pre-RMSNorm with `ε = 0`, with `d_in ≥ d ≥ 1`, the
functional dimension is at most `P − d² − d(d−1)/2 − 1 − s`, `s = 2 d_hidden`. -/
theorem ae_funDim_add_le_skipless_reglu_oneBlock_rmsNorm_zero [Nonempty d]
    (μ : Measure (Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, funDim (Arch.gated relu (rmsNorm 0) hid) 0 θ
        + (Fintype.card d ^ 2 + (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
          + 2 * Fintype.card (hid 0))
      ≤ Module.finrank ℝ
          (Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut) := by
  -- the pointwise bound holds wherever `E` and the write have rank `d` and no value column and
  -- no gate column of the read vanishes
  filter_upwards [ae_rank_E_write μ hdIn hhid, ae_value_ne_zero μ, ae_gate_ne_zero μ]
    with θ h1 h2 h3
  exact funDim_add_le_skipless_gated_homogeneous_rmsNorm_zero relu_homogeneous θ h1.1 h1.2 h2 h3

end Skips
