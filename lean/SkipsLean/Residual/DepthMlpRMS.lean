import SkipsLean.Residual.SmallWritesRMSSteps
import SkipsLean.OneBlock.Tanh
import SkipsLean.OneBlock.GELU
import SkipsLean.Activations.Analytic

/-!
# Residual networks of `tanh` and GELU blocks at any depth, under pre-RMSNorm

Paper (skips paper): Lemma A.27 (Small writes), its second value `fd(θ_τ) = P - d(d-1)/2 - s`
(pre-RMSNorm with `ε > 0`, no biases), and Theorem 4.7 (Equality for residual networks at any
depth) under pre-RMSNorm, for MLP blocks whose hidden units have no symmetry of their own
(`s = 0`): `tanh` blocks and GELU blocks. The blocks may have any widths.

Steps 1 to 3 of the paragraph "Under pre-RMSNorm" of the proof of Lemma A.27 are in
`Residual/SmallWritesRMSSteps.lean`. Here, as in Steps 4 and 5 of the proof of Theorem B.1 (ii):
the derivative of the wide block `n ↦ ∑_ℓ f_ℓ(n W_read^ℓ) W_write^ℓ` along the entries of `η`
vanishes for `n` in the image of `x ↦ N_ε(x E)`, an open set, hence for all `n` (the activation is
real-analytic); Lemma B.3 "with `E` and `D` replaced by the identity and `M = 0`", for the units of
all blocks together, gives `η_read^ℓ = 0` and `η_write^ℓ = 0`. So the flat directions of `J_0` are
`η_E = E Y`, `η_D = -Y D` with `Y` antisymmetric, a space of dimension `d(d-1)/2`.

Theorem 4.7 follows as without normalization (`Residual/DepthMlp.lean`).
-/

namespace Skips

open Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d]
  [Fintype dIn] [Fintype dOut]
variable {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]
variable {σ σ' : ℝ → ℝ} {ε : ℝ}

/-- **The conditions on `θ` in Lemma A.27 under pre-RMSNorm, for MLP blocks:** `E` and `D` have
rank `d`, and the hypotheses of Lemma B.3 hold for the units of all blocks together, "with `E` and
`D` replaced by the identity": every row of every `W_write^ℓ` is nonzero, and the columns of the
`W_read^ℓ`, over all blocks `ℓ` and hidden units `i`, are nonzero and pairwise non-collinear. -/
structure SmallWritesGenericRMS
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut) : Prop where
  rank_E : θ.E.rank = Fintype.card d
  rank_D : θ.D.rank = Fintype.card d
  /-- every row of `W_write^ℓ` is nonzero -/
  row_ne_zero : ∀ ℓ i, θ.write ℓ i ≠ 0
  /-- every column of `W_read^ℓ` is nonzero -/
  col_ne_zero : ∀ ℓ i, (θ.read ℓ)ᵀ i ≠ 0
  /-- the columns of the reads of all blocks together are pairwise non-collinear -/
  col_not_collinear : ∀ p q : (Σ ℓ, hid ℓ), p ≠ q → ∀ r : ℝ,
    (θ.read p.1)ᵀ p.2 ≠ r • (θ.read q.1)ᵀ q.2

/-! ### Helpers: the derivative of a block, analyticity, `N_ε(0) = 0` -/

/-- Helper (as `fderiv_map_apply_rm` of `OneBlock/ResidualRMSMlp.lean`): the derivative of
`M ↦ σ(M)` (entrywise) at `P` along `Q` has the entries `σ'(P_{t i}) Q_{t i}`. -/
private theorem fderiv_map_apply_dmr (hσ : ∀ z, HasDerivAt σ (σ' z) z) {m n : Type*} [Fintype m]
    [Fintype n] (P Q : Matrix m n ℝ) (t : m) (i : n) :
    fderiv ℝ (fun M : Matrix m n ℝ => M.map σ) P Q t i = σ' (P t i) * Q t i := by
  have hσd : Differentiable ℝ σ := fun z => (hσ z).differentiableAt
  have hd : Differentiable ℝ (fun M : Matrix m n ℝ => M.map σ) :=
    differentiable_pi.2 fun t => differentiable_pi.2 fun i =>
      hσd.comp (differentiable_pi.1 (differentiable_pi.1 differentiable_id t) i)
  -- the chain rule along the line `τ ↦ P + τ Q`
  have hline : HasDerivAt (fun τ : ℝ => P + τ • Q) Q 0 := by
    have h := ((hasDerivAt_id (0 : ℝ)).smul_const Q).const_add P
    rw [one_smul] at h
    exact h
  have h0 : P = P + (0 : ℝ) • Q := by rw [zero_smul, add_zero]
  have h1 := (hd P).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hline h0
  have h2 := hasDerivAt_pi.1 (hasDerivAt_pi.1 h1 t) i
  -- the same derivative, entrywise: `τ ↦ σ(P_{t i} + τ Q_{t i})`
  have h3 : HasDerivAt (fun τ : ℝ => σ (P t i + τ * Q t i)) (σ' (P t i) * Q t i) 0 := by
    have hu : HasDerivAt (fun τ : ℝ => P t i + τ * Q t i) (Q t i) 0 := by
      have h := ((hasDerivAt_id (0 : ℝ)).mul_const (Q t i)).const_add (P t i)
      rw [one_mul] at h
      exact h
    exact (hσ (P t i)).comp_of_eq (0 : ℝ) hu (by rw [zero_mul, add_zero])
  exact h2.unique h3

omit [Nonempty T] [Fintype d] [DecidableEq d] in
/-- Helper: the same for the map of block `ℓ` of an MLP network. -/
private theorem fderiv_f_mlp_apply_dmr (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    {χ : Matrix T d ℝ → Matrix T d ℝ} (ℓ : Fin L) (P Q : Matrix T (hid ℓ) ℝ) (t : T)
    (i : hid ℓ) :
    fderiv ℝ ((Arch.mlp (T := T) (d := d) σ χ hid).f ℓ) P Q t i = σ' (P t i) * Q t i :=
  fderiv_map_apply_dmr hσ P Q t i

/-- Helper: `v ↦ v ⬝ w` is analytic (a linear form). -/
private theorem analyticOnNhd_dotProduct_dmr {n : Type*} [Fintype n] (w : n → ℝ) :
    AnalyticOnNhd ℝ (fun v : n → ℝ => v ⬝ᵥ w) Set.univ := by
  simp only [dotProduct]
  exact Finset.analyticOnNhd_fun_sum _ fun k _ =>
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : n => ℝ) k).analyticOnNhd _).mul
      analyticOnNhd_const

omit [Fintype T] [Nonempty T] [DecidableEq d] in
/-- Helper: `N_ε(0) = 0`. -/
private theorem rmsNorm_zero_dmr : rmsNorm ε (0 : Matrix T d ℝ) = 0 := by
  ext t k
  simp [rmsNorm, rmsRow]

/-- **Proof of Lemma A.27 under pre-RMSNorm, MLP blocks, the flat directions of `J_0`:** under
the conditions of the lemma, a direction `η` with `(J_0 η)(x) = 0` at every input `x` has
`η_E = E Y` and `η_D = -Y D` for one antisymmetric matrix `Y`, and `η_read^ℓ = 0`,
`η_write^ℓ = 0` for every block. -/
theorem smallWritesLimitNorm_eq_zero_mlp_rmsNorm (hε : 0 < ε)
    (hσ : ∀ z, HasDerivAt σ (σ' z) z) (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (hU : UnitsRigid σ σ' d d (Σ ℓ, hid ℓ))
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)
    (hθ : SmallWritesGenericRMS θ)
    (η : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)
    (hη : ∀ x, smallWritesLimitNorm (Arch.mlp σ (rmsNorm ε) hid) θ η x = 0) :
    ∃ Y : Matrix d d ℝ, Yᵀ = -Y ∧ η.E = θ.E * Y ∧ η.D = -(Y * θ.D)
      ∧ (∀ ℓ, η.read ℓ = 0) ∧ (∀ ℓ, η.write ℓ = 0) := by
  -- the block maps `M ↦ σ(M)` are analytic, hence `C¹`
  have hf : ∀ ℓ, ContDiff ℝ 1 ((Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid).f ℓ) :=
    fun ℓ => (analyticOnNhd_f_mlp hσa ℓ).contDiff
  -- Steps 1 to 3: `Y` antisymmetric, `η_E = E Y`, `η_D = -Y D`, and the equation of the wide
  -- block at every `n = N_ε(x E)`
  obtain ⟨Y, hYa, hEY, hDY, hF⟩ :=
    exists_antisymm_of_smallWritesLimitNorm_rmsNorm hε rfl hf θ hθ.rank_E hθ.rank_D η hη
  -- Step 4 (a): `x ↦ x E` is onto, through a left inverse `B` of `E`
  obtain ⟨B, hB⟩ := Matrix.vecMul_surjective_iff_exists_left_inverse.mp
    (Matrix.vecMul_surjective_iff_rank_eq_card.mpr hθ.rank_E)
  -- row `t₀` of the equation of the wide block at a normalized state `n` whose rows all equal
  -- `v`, as a sum over the hidden units `(ℓ, i)` of all blocks
  have hrow : ∀ (h : Matrix T d ℝ) (v : d → ℝ), rmsNorm ε h = Matrix.of (fun _ => v) →
      ∀ j : d, ∑ p : (Σ ℓ, hid ℓ), (σ (v ⬝ᵥ (θ.read p.1)ᵀ p.2) * η.write p.1 p.2 j
        + σ' (v ⬝ᵥ (θ.read p.1)ᵀ p.2) * (v ⬝ᵥ (η.read p.1)ᵀ p.2) * θ.write p.1 p.2 j) = 0 := by
    intro h v hv j
    have e := hF (h * B)
    rw [Matrix.mul_assoc h B θ.E, hB, Matrix.mul_one, hv] at e
    have e2 := congrFun (congrFun e (Classical.arbitrary T)) j
    rw [Matrix.sum_apply, Matrix.zero_apply] at e2
    rw [Fintype.sum_sigma]
    refine Eq.trans ?_ e2
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    rw [Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [fderiv_f_mlp_apply_dmr hσ]
    show σ (v ⬝ᵥ (θ.read ℓ)ᵀ i) * η.write ℓ i j
        + σ' (v ⬝ᵥ (θ.read ℓ)ᵀ i) * (v ⬝ᵥ (η.read ℓ)ᵀ i) * θ.write ℓ i j
      = σ' (v ⬝ᵥ (θ.read ℓ)ᵀ i) * (v ⬝ᵥ (η.read ℓ)ᵀ i) * θ.write ℓ i j
        + σ (v ⬝ᵥ (θ.read ℓ)ᵀ i) * η.write ℓ i j
    ring
  -- Step 4 (b): `σ'` is analytic, and the row equation holds near `v = 0` (the range of `N_ε` is
  -- open and contains `0`), hence for all `v`
  have hσ'a : AnalyticOnNhd ℝ σ' Set.univ := by
    have e : σ' = deriv σ := funext fun z => (hσ z).deriv.symm
    rw [e]
    exact hσa.deriv
  have hopen : IsOpen {v : d → ℝ |
      (Matrix.of fun _ : T => v) ∈ Set.range (rmsNorm ε : Matrix T d ℝ → Matrix T d ℝ)} :=
    (isOpenMap_rmsNorm hε).isOpen_range.preimage (continuous_pi fun _ => continuous_id)
  have h0 : (0 : d → ℝ) ∈ {v : d → ℝ |
      (Matrix.of fun _ : T => v) ∈ Set.range (rmsNorm ε : Matrix T d ℝ → Matrix T d ℝ)} :=
    ⟨0, by rw [rmsNorm_zero_dmr]; rfl⟩
  have hall : ∀ (v : d → ℝ) (j : d), ∑ p : (Σ ℓ, hid ℓ), (σ (v ⬝ᵥ (θ.read p.1)ᵀ p.2)
      * η.write p.1 p.2 j
        + σ' (v ⬝ᵥ (θ.read p.1)ᵀ p.2) * (v ⬝ᵥ (η.read p.1)ᵀ p.2) * θ.write p.1 p.2 j) = 0 := by
    intro v j
    have hg : AnalyticOnNhd ℝ (fun v : d → ℝ => ∑ p : (Σ ℓ, hid ℓ),
        (σ (v ⬝ᵥ (θ.read p.1)ᵀ p.2) * η.write p.1 p.2 j
          + σ' (v ⬝ᵥ (θ.read p.1)ᵀ p.2) * (v ⬝ᵥ (η.read p.1)ᵀ p.2) * θ.write p.1 p.2 j))
        Set.univ :=
      Finset.analyticOnNhd_fun_sum _ fun p _ =>
        ((hσa.comp (analyticOnNhd_dotProduct_dmr _) (Set.mapsTo_univ _ _)).mul
          analyticOnNhd_const).add
        (((hσ'a.comp (analyticOnNhd_dotProduct_dmr _) (Set.mapsTo_univ _ _)).mul
          (analyticOnNhd_dotProduct_dmr _)).mul analyticOnNhd_const)
    have hev : (fun v : d → ℝ => ∑ p : (Σ ℓ, hid ℓ),
        (σ (v ⬝ᵥ (θ.read p.1)ᵀ p.2) * η.write p.1 p.2 j
          + σ' (v ⬝ᵥ (θ.read p.1)ᵀ p.2) * (v ⬝ᵥ (η.read p.1)ᵀ p.2) * θ.write p.1 p.2 j))
        =ᶠ[nhds 0] 0 :=
      Filter.eventually_of_mem (hopen.mem_nhds h0) fun w hw => by
        obtain ⟨h, hh⟩ := hw
        exact hrow h w hh j
    exact hg.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
      (Set.mem_univ 0) hev (Set.mem_univ v)
  -- Step 4 (c): Lemma B.3 for the units of all blocks together, with `E`, `D` the identity and
  -- `M = 0`: `η_read^ℓ = 0` and `η_write^ℓ = 0`
  obtain ⟨-, -, hc, -, ha⟩ := hU (fun p => (θ.read p.1)ᵀ p.2) 0 (fun p => θ.write p.1 p.2) 0 0
    (fun p => (η.read p.1)ᵀ p.2) 0 (fun p => η.write p.1 p.2)
    (fun p => hθ.row_ne_zero p.1 p.2) (fun p => hθ.col_ne_zero p.1 p.2) hθ.col_not_collinear (by
      intro v
      funext j
      have h := hall v j
      simp only [Matrix.vecMul_zero, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        Pi.zero_apply, add_zero, zero_add]
      exact h)
  refine ⟨Y, hYa, hEY, hDY, fun ℓ => ?_, fun ℓ => ?_⟩
  · ext k i
    exact congrFun (congrFun hc ⟨ℓ, i⟩) k
  · ext i k
    exact congrFun (congrFun ha ⟨ℓ, i⟩) k

/-- Helper (as `smallWritesFlatLin` of `Residual/DepthMlp.lean`): the directions
`Y ↦ (E Y, 0, 0, -Y D)` of one change of basis at all hidden states (reads and writes fixed), as a
linear map from `Matrix d d ℝ`. -/
private def smallWritesFlatLinRMS
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut) :
    Matrix d d ℝ →ₗ[ℝ] Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut where
  toFun X := ⟨θ.E * X, 0, 0, -(X * θ.D)⟩
  map_add' X Y := by
    apply Params.ext'
    · exact Matrix.mul_add _ _ _
    · intro ℓ
      exact (add_zero 0).symm
    · intro ℓ
      exact (add_zero 0).symm
    · show -((X + Y) * θ.D) = -(X * θ.D) + -(Y * θ.D)
      rw [Matrix.add_mul, neg_add]
  map_smul' c X := by
    apply Params.ext'
    · exact Matrix.mul_smul _ _ _
    · intro ℓ
      exact (smul_zero c).symm
    · intro ℓ
      exact (smul_zero c).symm
    · show -((c • X) * θ.D) = c • -(X * θ.D)
      rw [Matrix.smul_mul, smul_neg]

/-- **Lemma A.27 (Small writes), second value, for MLP blocks with `s = 0`, under the conditions
of its proof:** under pre-RMSNorm with `ε > 0`, for all small `τ ≠ 0` the residual network has
`fd(θ_τ) = P - d(d-1)/2`. -/
theorem eventually_funDim_smallWrites_mlp_rmsNorm (hε : 0 < ε)
    (hσ : ∀ z, HasDerivAt σ (σ' z) z) (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (hU : UnitsRigid σ σ' d d (Σ ℓ, hid ℓ))
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)
    (hθ : SmallWritesGenericRMS θ) :
    ∀ᶠ τ in 𝓝[≠] (0 : ℝ),
      funDim (Arch.mlp σ (rmsNorm ε) hid) 1 (θ.smallWrites τ)
          + Fintype.card d * (Fintype.card d - 1) / 2
        = Module.finrank ℝ
            (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut) := by
  have hσd : Differentiable ℝ σ := fun z => (hσ z).differentiableAt
  -- the flat directions of `J_0` lie in the range `V` of `Y ↦ (E Y, 0, 0, -Y D)` on
  -- antisymmetric `Y` (step 1)
  let Φ : antisymmetric d →ₗ[ℝ]
      Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut :=
    (smallWritesFlatLinRMS θ).comp (antisymmetric d).subtype
  have hV : ∀ η, (∀ x, smallWritesLimitNorm (Arch.mlp σ (rmsNorm ε) hid) θ η x = 0) →
      η ∈ LinearMap.range Φ := by
    intro η hη
    obtain ⟨Y, hYa, hE, hD, hr, hw⟩ :=
      smallWritesLimitNorm_eq_zero_mlp_rmsNorm hε hσ hσa hU θ hθ η hη
    refine ⟨⟨Y, hYa⟩, ?_⟩
    apply Params.ext'
    · exact hE.symm
    · intro ℓ
      exact (hr ℓ).symm
    · intro ℓ
      exact (hw ℓ).symm
    · exact hD.symm
  -- `dim V ≤ d (d - 1) / 2`
  have hdim : Module.finrank ℝ (LinearMap.range Φ)
      ≤ Fintype.card d * (Fintype.card d - 1) / 2 := by
    calc Module.finrank ℝ (LinearMap.range Φ)
        ≤ Module.finrank ℝ (antisymmetric d) := LinearMap.finrank_range_le Φ
      _ = Fintype.card d * (Fintype.card d - 1) / 2 := finrank_antisymmetric
  -- `≥`: "The rank" of the proof of Lemma A.27 (`N_ε` is analytic); `≤`: the upper bound for
  -- residual networks under pre-RMSNorm, as `E` is not changed by `θ ↦ θ_τ`
  filter_upwards [eventually_funDim_smallWrites_ge_norm (Arch.mlp σ (rmsNorm ε) hid) θ
    (analyticOnNhd_rmsNorm hε) (fun ℓ => analyticOnNhd_f_mlp hσa ℓ) _ hV] with τ hτ
  have hle := funDim_add_le_residual_rmsNorm (θ.smallWrites τ) hε rfl
    (fun ℓ => differentiable_f_mlp hσd ℓ) hθ.rank_E
  generalize Fintype.card d * (Fintype.card d - 1) / 2 = N at hle hdim ⊢
  omega

omit [Fintype T] [Nonempty T] in
/-- Helper (as `rank_eq_of_isUnit_det_rows_rm` of `OneBlock/ResidualRMSMlp.lean`): a matrix with
`d` columns has rank `d` if some `d` of its rows form an invertible matrix. -/
private theorem rank_eq_of_isUnit_det_rows_dmr {m : Type*} (M : Matrix m d ℝ) (ρ : d ↪ m)
    (h : IsUnit (M.submatrix ρ id).det) : M.rank = Fintype.card d :=
  le_antisymm (Matrix.rank_le_card_width M)
    ((Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).2 h)).symm.le.trans
      (Matrix.rank_submatrix_le M ρ id))

/-- The conditions of Lemma A.27 under pre-RMSNorm hold at generic parameters, for
`d_in, d_out ≥ d ≥ 2` and blocks of any widths. -/
theorem ae_smallWritesGenericRMS
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, SmallWritesGenericRMS θ := by
  classical
  -- two distinct coordinates of `h`, `d` rows of `E`, `d` columns of `D`
  obtain ⟨k₁, k₂, hk⟩ := Fintype.exists_pair_of_one_lt_card (show 1 < Fintype.card d by omega)
  obtain ⟨ρ⟩ := Function.Embedding.nonempty_of_card_le hdIn
  obtain ⟨cD⟩ := Function.Embedding.nonempty_of_card_le hdOut
  -- the parameters with all entries `1`
  let θ₁ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut :=
    ⟨Matrix.of fun _ _ => 1, fun _ => Matrix.of fun _ _ => 1, fun _ => Matrix.of fun _ _ => 1,
      Matrix.of fun _ _ => 1⟩
  -- the entries of the reads and of the writes are linear, hence analytic, in the parameters
  have hR : ∀ (ℓ : Fin L) (k : d) (i : hid ℓ), AnalyticOnNhd ℝ
      (fun θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut => θ.read ℓ k i)
      Set.univ := fun ℓ k i =>
    analyticOnNhd_linear ((Matrix.entryLinearMap ℝ ℝ k i).comp
      (Params.linRead (A := Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) (dIn := dIn)
        (dOut := dOut) ℓ))
  have hW : ∀ (ℓ : Fin L) (i : hid ℓ) (k : d), AnalyticOnNhd ℝ
      (fun θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut => θ.write ℓ i k)
      Set.univ := fun ℓ i k =>
    analyticOnNhd_linear ((Matrix.entryLinearMap ℝ ℝ i k).comp
      (Params.linWrite (A := Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) (dIn := dIn)
        (dOut := dOut) ℓ))
  -- the ranks of `E` and `D`: invertible minors
  have h1 := ae_isUnit_det_submatrix μ
  -- the rows of the writes are nonzero: their entries at `k₁` are
  have h2 : ∀ᵐ θ ∂μ, ∀ ℓ (i : hid ℓ), θ.write ℓ i k₁ ≠ 0 :=
    ae_all_iff.2 fun ℓ => ae_all_iff.2 fun i =>
      ae_ne_zero_of_analytic μ (hW ℓ i k₁) ⟨θ₁, show (1 : ℝ) ≠ 0 from one_ne_zero⟩
  -- the columns of the reads are nonzero: their entries at `k₁` are
  have h3 : ∀ᵐ θ ∂μ, ∀ ℓ (i : hid ℓ), θ.read ℓ k₁ i ≠ 0 :=
    ae_all_iff.2 fun ℓ => ae_all_iff.2 fun i =>
      ae_ne_zero_of_analytic μ (hR ℓ k₁ i) ⟨θ₁, show (1 : ℝ) ≠ 0 from one_ne_zero⟩
  -- two columns of distinct units, of one block or of two blocks, are not collinear: a `2 × 2`
  -- minor does not vanish
  have h4 : ∀ᵐ θ ∂μ, ∀ p q : (Σ ℓ, hid ℓ), p ≠ q →
      θ.read p.1 k₁ p.2 * θ.read q.1 k₂ q.2 - θ.read q.1 k₁ q.2 * θ.read p.1 k₂ p.2 ≠ 0 := by
    refine ae_all_iff.2 fun p => ae_all_iff.2 fun q => ?_
    by_cases hpq : p = q
    · exact Filter.Eventually.of_forall fun _ h => absurd hpq h
    · -- witness: the reads of all blocks side by side are `E₀ W₀`, with a nonzero minor
      obtain ⟨E₀, W₀, hEW⟩ := exists_minor_ne_zero hk hk hpq
      let θ₀ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut :=
        ⟨0, fun ℓ => Matrix.of fun k i => (E₀ * W₀) k ⟨ℓ, i⟩, 0, 0⟩
      have hg : AnalyticOnNhd ℝ
          (fun θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut =>
            θ.read p.1 k₁ p.2 * θ.read q.1 k₂ q.2 - θ.read q.1 k₁ q.2 * θ.read p.1 k₂ p.2)
          Set.univ :=
        ((hR p.1 k₁ p.2).mul (hR q.1 k₂ q.2)).sub ((hR q.1 k₁ q.2).mul (hR p.1 k₂ p.2))
      exact (ae_ne_zero_of_analytic μ hg ⟨θ₀, hEW⟩).mono fun _ h _ => h
  filter_upwards [h1, h2, h3, h4] with θ h1 h2 h3 h4
  refine ⟨rank_eq_of_isUnit_det_rows_dmr θ.E ρ (h1.2.2.1 ρ),
    rank_eq_card_of_isUnit_det θ.D cD (h1.2.1 cD), fun ℓ i hi => h2 ℓ i (congrFun hi k₁),
    fun ℓ i hi => h3 ℓ i (congrFun hi k₁), ?_⟩
  -- if `c_p = r c_q`, the minor of the columns `p`, `q` vanishes
  intro p q hpq r hr
  have e1 : θ.read p.1 k₁ p.2 = r * θ.read q.1 k₁ q.2 := congrFun hr k₁
  have e2 : θ.read p.1 k₂ p.2 = r * θ.read q.1 k₂ q.2 := congrFun hr k₂
  apply h4 p q hpq
  rw [e1, e2]
  ring

/-- **Lemma A.27 (Small writes), second value, for MLP blocks with `s = 0`:** with
`d_in, d_out ≥ d ≥ 2` and blocks of any widths, under pre-RMSNorm with `ε > 0`, for generic
parameters `θ` and all small `τ ≠ 0`, the residual network has `fd(θ_τ) = P - d(d-1)/2`. -/
theorem ae_eventually_funDim_smallWrites_mlp_rmsNorm (hε : 0 < ε)
    (hσ : ∀ z, HasDerivAt σ (σ' z) z) (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (hU : UnitsRigid σ σ' d d (Σ ℓ, hid ℓ))
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, ∀ᶠ τ in 𝓝[≠] (0 : ℝ),
      funDim (Arch.mlp σ (rmsNorm ε) hid) 1 (θ.smallWrites τ)
          + Fintype.card d * (Fintype.card d - 1) / 2
        = Module.finrank ℝ
            (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut) := by
  filter_upwards [ae_smallWritesGenericRMS μ hd hdIn hdOut] with θ hθ
  exact eventually_funDim_smallWrites_mlp_rmsNorm hε hσ hσa hU θ hθ

/-- **Theorem 4.7 of the skips paper for MLP blocks with `s = 0`, under pre-RMSNorm:** with
`d_in, d_out ≥ d ≥ 2`, `L` blocks of any widths and `ε > 0`, at generic parameters the residual
network has the functional dimension `P - d(d-1)/2`. -/
theorem ae_funDim_mlp_residual_rmsNorm (hε : 0 < ε)
    (hσ : ∀ z, HasDerivAt σ (σ' z) z) (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (hU : UnitsRigid σ σ' d d (Σ ℓ, hid ℓ))
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, funDim (Arch.mlp σ (rmsNorm ε) hid) 1 θ
        + Fintype.card d * (Fintype.card d - 1) / 2
      = Module.finrank ℝ
          (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut) := by
  have hσd : Differentiable ℝ σ := fun z => (hσ z).differentiableAt
  have hf : ∀ ℓ, AnalyticOnNhd ℝ ((Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid).f ℓ) Set.univ :=
    fun ℓ => analyticOnNhd_f_mlp hσa ℓ
  -- one parameter `θ₀` with the conditions of Lemma A.27, and one small `τ ≠ 0`:
  -- `fd(θ₀_τ) = P - d(d-1)/2`
  obtain ⟨θ₀, hθ₀⟩ := (ae_smallWritesGenericRMS μ hd hdIn hdOut).exists
  obtain ⟨τ, hτ⟩ := (eventually_funDim_smallWrites_mlp_rmsNorm hε hσ hσa hU θ₀ hθ₀).exists
  -- at almost every `θ`, `fd(θ) ≥ fd(θ₀_τ)` (analytic outputs) and `fd(θ) ≤ P - d(d-1)/2`
  filter_upwards [ae_funDim_ge (Arch.mlp σ (rmsNorm ε) hid) 1 hf (analyticOnNhd_rmsNorm hε) μ
      (θ₀.smallWrites τ),
    ae_funDim_add_le_residual_rmsNorm μ hε rfl (fun ℓ => differentiable_f_mlp hσd ℓ) hdIn]
    with θ h1 h2
  generalize Fintype.card d * (Fintype.card d - 1) / 2 = N at hτ h2 ⊢
  omega

/-! ### The two kinds of block -/

/-- **Lemma A.27 (Small writes), second value, for `tanh` blocks under pre-RMSNorm.** -/
theorem ae_eventually_funDim_smallWrites_tanh_rmsNorm (hε : 0 < ε)
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) Real.tanh (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, ∀ᶠ τ in 𝓝[≠] (0 : ℝ),
      funDim (Arch.mlp Real.tanh (rmsNorm ε) hid) 1 (θ.smallWrites τ)
          + Fintype.card d * (Fintype.card d - 1) / 2
        = Module.finrank ℝ
            (Params (Arch.mlp (T := T) (d := d) Real.tanh (rmsNorm ε) hid) dIn dOut) := by
  exact ae_eventually_funDim_smallWrites_mlp_rmsNorm hε hasDerivAt_tanh analyticOnNhd_tanh
    (tanh_unitsRigid _ _ _) μ hd hdIn hdOut

/-- **Lemma A.27 (Small writes), second value, for GELU blocks under pre-RMSNorm.** -/
theorem ae_eventually_funDim_smallWrites_gelu_rmsNorm (hε : 0 < ε)
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, ∀ᶠ τ in 𝓝[≠] (0 : ℝ),
      funDim (Arch.mlp gelu (rmsNorm ε) hid) 1 (θ.smallWrites τ)
          + Fintype.card d * (Fintype.card d - 1) / 2
        = Module.finrank ℝ
            (Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm ε) hid) dIn dOut) := by
  exact ae_eventually_funDim_smallWrites_mlp_rmsNorm hε hasDerivAt_gelu analyticOnNhd_gelu
    (gelu_unitsRigid _ _ _) μ hd hdIn hdOut

/-- **Theorem 4.7 of the skips paper for `tanh` blocks under pre-RMSNorm:** with `ε > 0`, at
generic parameters the residual network of `L` blocks has the functional dimension
`P - d(d-1)/2`. -/
theorem ae_funDim_tanh_residual_rmsNorm (hε : 0 < ε)
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) Real.tanh (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, funDim (Arch.mlp Real.tanh (rmsNorm ε) hid) 1 θ
        + Fintype.card d * (Fintype.card d - 1) / 2
      = Module.finrank ℝ
          (Params (Arch.mlp (T := T) (d := d) Real.tanh (rmsNorm ε) hid) dIn dOut) := by
  exact ae_funDim_mlp_residual_rmsNorm hε hasDerivAt_tanh analyticOnNhd_tanh
    (tanh_unitsRigid _ _ _) μ hd hdIn hdOut

/-- **Theorem 4.7 of the skips paper for GELU blocks under pre-RMSNorm.** -/
theorem ae_funDim_gelu_residual_rmsNorm (hε : 0 < ε)
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, funDim (Arch.mlp gelu (rmsNorm ε) hid) 1 θ
        + Fintype.card d * (Fintype.card d - 1) / 2
      = Module.finrank ℝ
          (Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm ε) hid) dIn dOut) := by
  exact ae_funDim_mlp_residual_rmsNorm hε hasDerivAt_gelu analyticOnNhd_gelu
    (gelu_unitsRigid _ _ _) μ hd hdIn hdOut

end Skips
