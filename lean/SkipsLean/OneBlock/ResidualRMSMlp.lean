import SkipsLean.OneBlock.ResidualRMSSteps
import SkipsLean.OneBlock.Tanh
import SkipsLean.OneBlock.GELU
import SkipsLean.Activations.Analytic

/-!
# One residual `tanh` or GELU block under pre-RMSNorm

Paper (skips paper): Theorem 4.6 (ii), first sentence (Theorem B.1 (ii) in the appendix), for
`ε > 0` and no biases, for MLP blocks whose hidden units have no symmetry of their own (`s = 0`):
`tanh` blocks and GELU blocks. At generic parameters the residual network of one block has the
functional dimension `P - d(d-1)/2`. The block may have any width.

Steps 1 to 3 of the proof are in `OneBlock/ResidualRMSSteps.lean`. Here:

* Step 4 (the block): the derivative of `n ↦ f(n W_read) W_write` along the entries of `η'`
  vanishes for every `n` in the image of `x ↦ N_ε(x E)`, an open set of hidden states (the open
  ball of radius `√d` in the paper), since `E` has rank `d`. For a real-analytic activation it then
  vanishes for all `n`. "So Lemma B.3, with `E` and `D` replaced by the identity and `M = 0`",
  gives `η'_read = 0` and `η'_write = 0` (`UnitsRigid` with the columns of `W_read` and the rows of
  `W_write`).
* Step 5 (counting): the flat directions are those of the orthogonal change of basis,
  `cobDir θ (fun _ => Y)` with `Y` antisymmetric; "an antisymmetric `Y` with `E Y = 0` vanishes",
  so `dim K(θ) = d(d-1)/2`.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {hid : Fin 1 → Type} [∀ ℓ, Fintype (hid ℓ)]
variable {σ σ' : ℝ → ℝ} {ε : ℝ}

/-- **The conditions on `θ` in the proof of Theorem B.1 (ii), for one MLP block:** `E` and `D`
have rank `d`, and the hypotheses of Lemma B.3 hold "with `E` and `D` replaced by the identity":
every row of `W_write` is nonzero, and the columns of `W_read` are nonzero and pairwise
non-collinear. -/
structure OneBlockGenericRMS
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut) : Prop where
  rank_E : θ.E.rank = Fintype.card d
  rank_D : θ.D.rank = Fintype.card d
  /-- every row of `W_write` is nonzero -/
  row_ne_zero : ∀ i, θ.write 0 i ≠ 0
  /-- every column of `W_read` is nonzero -/
  col_ne_zero : ∀ i, (θ.read 0)ᵀ i ≠ 0
  /-- the columns of `W_read` are pairwise non-collinear -/
  col_not_collinear : ∀ i j, i ≠ j → ∀ r : ℝ, (θ.read 0)ᵀ i ≠ r • (θ.read 0)ᵀ j

/-! ### Helpers -/

/-- Helper: the derivative of `M ↦ σ(M)` (entrywise) at `P` along `Q` has the entries
`σ'(P_{t i}) Q_{t i}`. -/
private theorem fderiv_map_apply_rm (hσ : ∀ z, HasDerivAt σ (σ' z) z) {m n : Type*} [Fintype m]
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
/-- Helper: the same for the map of the block of an MLP network. -/
private theorem fderiv_f_mlp_apply_rm (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    {χ : Matrix T d ℝ → Matrix T d ℝ} (P Q : Matrix T (hid 0) ℝ) (t : T) (i : hid 0) :
    fderiv ℝ ((Arch.mlp (T := T) (d := d) σ χ hid).f 0) P Q t i = σ' (P t i) * Q t i :=
  fderiv_map_apply_rm hσ P Q t i

/-- Helper: `v ↦ v ⬝ w` is analytic (a linear form). -/
private theorem analyticOnNhd_dotProduct_rm {n : Type*} [Fintype n] (w : n → ℝ) :
    AnalyticOnNhd ℝ (fun v : n → ℝ => v ⬝ᵥ w) Set.univ := by
  simp only [dotProduct]
  exact Finset.analyticOnNhd_fun_sum _ fun k _ =>
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : n => ℝ) k).analyticOnNhd _).mul
      analyticOnNhd_const

omit [Fintype T] [Nonempty T] [DecidableEq d] in
/-- Helper: `N_ε(0) = 0`. -/
private theorem rmsNorm_zero_rm : rmsNorm ε (0 : Matrix T d ℝ) = 0 := by
  ext t k
  simp [rmsNorm, rmsRow]

/-- **Proof of Theorem B.1 (ii), Steps 1 to 4, for one MLP block with `s = 0`:** under the
conditions of the proof, every flat direction of the residual network under pre-RMSNorm
(`ε > 0`) is the direction of one antisymmetric `Y` at both hidden states. -/
theorem flat_le_cobDir_const_mlp_residual_rmsNorm (hε : 0 < ε)
    (hσ : ∀ z, HasDerivAt σ (σ' z) z) (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (hU : UnitsRigid σ σ' d d (hid 0))
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)
    (hθ : OneBlockGenericRMS θ)
    (η : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)
    (hη : η ∈ flat (Arch.mlp σ (rmsNorm ε) hid) 1 θ) :
    ∃ Y : Matrix d d ℝ, Yᵀ = -Y ∧ η = cobDir θ (fun _ => Y) := by
  -- the block map `M ↦ σ(M)` is analytic, hence `C¹`
  have hf : ContDiff ℝ 1 ((Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid).f 0) :=
    (analyticOnNhd_f_mlp hσa 0).contDiff
  -- Steps 1 to 3: `Y` antisymmetric, `η_E = E Y`, `η_D = -Y D`, and the block equation
  obtain ⟨Y, hYa, hEY, hDY, hF⟩ :=
    exists_antisymm_of_flat_residual_rmsNorm hε rfl hf θ hθ.rank_E hθ.rank_D η hη
  generalize hR' : η.read 0 + Y * θ.read 0 = R' at hF
  generalize hW' : η.write 0 - θ.write 0 * Y = W' at hF
  -- Step 4 (a): `x ↦ x E` is onto, through a left inverse `B` of `E`
  obtain ⟨B, hB⟩ := Matrix.vecMul_surjective_iff_exists_left_inverse.mp
    (Matrix.vecMul_surjective_iff_rank_eq_card.mpr hθ.rank_E)
  -- row `t₀` of the block equation at a normalized state `n` whose rows all equal `v`
  have hrow : ∀ (h : Matrix T d ℝ) (v : d → ℝ), rmsNorm ε h = Matrix.of (fun _ => v) →
      ∀ j : d, ∑ i : hid 0, (σ (v ⬝ᵥ (θ.read 0)ᵀ i) * W' i j
        + σ' (v ⬝ᵥ (θ.read 0)ᵀ i) * (v ⬝ᵥ R'ᵀ i) * θ.write 0 i j) = 0 := by
    intro h v hv j
    have e := hF (h * B)
    rw [Matrix.mul_assoc, hB, Matrix.mul_one, hv] at e
    have e2 := congrFun (congrFun e (Classical.arbitrary T)) j
    rw [Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply, ← Finset.sum_add_distrib,
      Matrix.zero_apply] at e2
    refine Eq.trans ?_ e2
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [fderiv_f_mlp_apply_rm hσ]
    show _ = σ' (v ⬝ᵥ (θ.read 0)ᵀ i) * (v ⬝ᵥ R'ᵀ i) * θ.write 0 i j
      + σ (v ⬝ᵥ (θ.read 0)ᵀ i) * W' i j
    ring
  -- Step 4 (b): `σ'` is analytic, and the row equation holds near `v = 0`, hence for all `v`
  have hσ'a : AnalyticOnNhd ℝ σ' Set.univ := by
    have e : σ' = deriv σ := funext fun z => (hσ z).deriv.symm
    rw [e]
    exact hσa.deriv
  have hopen : IsOpen {v : d → ℝ |
      (Matrix.of fun _ : T => v) ∈ Set.range (rmsNorm ε : Matrix T d ℝ → Matrix T d ℝ)} :=
    (isOpenMap_rmsNorm hε).isOpen_range.preimage (continuous_pi fun _ => continuous_id)
  have h0 : (0 : d → ℝ) ∈ {v : d → ℝ |
      (Matrix.of fun _ : T => v) ∈ Set.range (rmsNorm ε : Matrix T d ℝ → Matrix T d ℝ)} :=
    ⟨0, by rw [rmsNorm_zero_rm]; rfl⟩
  have hall : ∀ (v : d → ℝ) (j : d), ∑ i : hid 0, (σ (v ⬝ᵥ (θ.read 0)ᵀ i) * W' i j
      + σ' (v ⬝ᵥ (θ.read 0)ᵀ i) * (v ⬝ᵥ R'ᵀ i) * θ.write 0 i j) = 0 := by
    intro v j
    have hg : AnalyticOnNhd ℝ (fun v : d → ℝ => ∑ i : hid 0, (σ (v ⬝ᵥ (θ.read 0)ᵀ i) * W' i j
        + σ' (v ⬝ᵥ (θ.read 0)ᵀ i) * (v ⬝ᵥ R'ᵀ i) * θ.write 0 i j)) Set.univ :=
      Finset.analyticOnNhd_fun_sum _ fun i _ =>
        ((hσa.comp (analyticOnNhd_dotProduct_rm _) (Set.mapsTo_univ _ _)).mul
          analyticOnNhd_const).add
        (((hσ'a.comp (analyticOnNhd_dotProduct_rm _) (Set.mapsTo_univ _ _)).mul
          (analyticOnNhd_dotProduct_rm _)).mul analyticOnNhd_const)
    have hev : (fun v : d → ℝ => ∑ i : hid 0, (σ (v ⬝ᵥ (θ.read 0)ᵀ i) * W' i j
        + σ' (v ⬝ᵥ (θ.read 0)ᵀ i) * (v ⬝ᵥ R'ᵀ i) * θ.write 0 i j)) =ᶠ[nhds 0] 0 :=
      Filter.eventually_of_mem (hopen.mem_nhds h0) fun w hw => by
        obtain ⟨h, hh⟩ := hw
        exact hrow h w hh j
    exact hg.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
      (Set.mem_univ 0) hev (Set.mem_univ v)
  -- Step 4 (c): Lemma B.3 with `E`, `D` the identity and `M = 0`: `η'_read = 0`, `η'_write = 0`
  obtain ⟨-, -, hc, -, ha⟩ := hU (fun i => (θ.read 0)ᵀ i) 0 (fun i => θ.write 0 i) 0 0
    (fun i => R'ᵀ i) 0 (fun i => W' i) hθ.row_ne_zero hθ.col_ne_zero hθ.col_not_collinear (by
      intro v
      funext j
      have h := hall v j
      simp only [Matrix.vecMul_zero, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        Pi.zero_apply, add_zero, zero_add]
      exact h)
  have hR0 : R' = 0 := by
    ext k i
    exact congrFun (congrFun hc i) k
  have hW0 : W' = 0 := by
    ext i k
    exact congrFun (congrFun ha i) k
  rw [hR0] at hR'
  rw [hW0] at hW'
  -- Step 4 (d): `η = cobDir θ (Y, Y)`, component by component
  refine ⟨Y, hYa, Params.ext' hEY (fun ℓ => ?_) (fun ℓ => ?_) hDY⟩
  · obtain rfl := Subsingleton.elim ℓ 0
    exact eq_neg_of_add_eq_zero_left hR'
  · obtain rfl := Subsingleton.elim ℓ 0
    exact sub_eq_zero.mp hW'

/-- **Theorem 4.6 (ii) of the skips paper, first sentence, for one MLP block with `s = 0`, under
the conditions of its proof:** under pre-RMSNorm with `ε > 0` the residual network has the
functional dimension `P - d(d-1)/2`. -/
theorem funDim_mlp_oneBlock_residual_rmsNorm (hε : 0 < ε)
    (hσ : ∀ z, HasDerivAt σ (σ' z) z) (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (hU : UnitsRigid σ σ' d d (hid 0))
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)
    (hθ : OneBlockGenericRMS θ) :
    funDim (Arch.mlp σ (rmsNorm ε) hid) 1 θ + Fintype.card d * (Fintype.card d - 1) / 2
      = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut) := by
  have hσd : Differentiable ℝ σ := fun z => (hσ z).differentiableAt
  have hf' : ∀ ℓ, Differentiable ℝ ((Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid).f ℓ) :=
    fun ℓ => differentiable_f_mlp hσd ℓ
  have hdiff : ∀ x : Matrix T dIn ℝ, DifferentiableAt ℝ
      (fun θ' : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut =>
        eval (Arch.mlp σ (rmsNorm ε) hid) 1 θ' x) θ := fun x =>
    (differentiable_eval hf' (differentiable_rmsNorm hε) x).differentiableAt
  -- `≤`: the antisymmetric changes of basis, the same at both hidden states, are flat
  have hle := funDim_add_le_residual_rmsNorm θ hε rfl hf' hθ.rank_E
  -- `≥`: `K(θ)` lies in the range of `Y ↦ cobDir θ (Y, Y)` on antisymmetric `Y`
  let Φ : antisymmetric d →ₗ[ℝ]
      Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut :=
    (cobDirLin θ).comp (LinearMap.pi fun _ => (antisymmetric d).subtype)
  have hflat : flat (Arch.mlp σ (rmsNorm ε) hid) 1 θ ≤ LinearMap.range Φ := by
    intro η hη
    obtain ⟨Y, hY, rfl⟩ := flat_le_cobDir_const_mlp_residual_rmsNorm hε hσ hσa hU θ hθ η hη
    exact ⟨⟨Y, hY⟩, rfl⟩
  -- a space of dimension at most `d (d - 1) / 2`
  have hdim : Module.finrank ℝ (LinearMap.range Φ)
      ≤ Fintype.card d * (Fintype.card d - 1) / 2 := by
    calc Module.finrank ℝ (LinearMap.range Φ)
        ≤ Module.finrank ℝ (antisymmetric d) := LinearMap.finrank_range_le Φ
      _ = Fintype.card d * (Fintype.card d - 1) / 2 := finrank_antisymmetric
  -- `fd(θ) + dim K(θ) = P`
  have h := funDim_add_finrank_flat θ hdiff
  have hmono := Submodule.finrank_mono hflat
  generalize Fintype.card d * (Fintype.card d - 1) / 2 = N at hle hdim ⊢
  omega

omit [Fintype T] [Nonempty T] in
/-- Helper: a matrix with `d` columns has rank `d` if some `d` of its rows form an invertible
matrix. -/
private theorem rank_eq_of_isUnit_det_rows_rm {m : Type*} (M : Matrix m d ℝ) (ρ : d ↪ m)
    (h : IsUnit (M.submatrix ρ id).det) : M.rank = Fintype.card d :=
  le_antisymm (Matrix.rank_le_card_width M)
    ((Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).2 h)).symm.le.trans
      (Matrix.rank_submatrix_le M ρ id))

/-- The conditions of the proof hold at generic parameters, for `d_in, d_out ≥ d ≥ 2` and a block
of any width. -/
theorem ae_oneBlockGenericRMS
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, OneBlockGenericRMS θ := by
  classical
  -- two distinct coordinates of `h`, `d` rows of `E`, `d` columns of `D`
  obtain ⟨k₁, k₂, hk⟩ := Fintype.exists_pair_of_one_lt_card (show 1 < Fintype.card d by omega)
  obtain ⟨ρ⟩ := Function.Embedding.nonempty_of_card_le hdIn
  obtain ⟨cD⟩ := Function.Embedding.nonempty_of_card_le hdOut
  -- the parameters with all entries `1`
  let θ₁ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut :=
    ⟨Matrix.of fun _ _ => 1, fun _ => Matrix.of fun _ _ => 1, fun _ => Matrix.of fun _ _ => 1,
      Matrix.of fun _ _ => 1⟩
  -- the entries of the read and of the write are linear, hence analytic, in the parameters
  have hR : ∀ (k : d) (i : hid 0), AnalyticOnNhd ℝ
      (fun θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut => θ.read 0 k i)
      Set.univ := fun k i =>
    analyticOnNhd_linear ((Matrix.entryLinearMap ℝ ℝ k i).comp
      (Params.linRead (A := Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) (dIn := dIn)
        (dOut := dOut) 0))
  have hW : ∀ (i : hid 0) (k : d), AnalyticOnNhd ℝ
      (fun θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut => θ.write 0 i k)
      Set.univ := fun i k =>
    analyticOnNhd_linear ((Matrix.entryLinearMap ℝ ℝ i k).comp
      (Params.linWrite (A := Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) (dIn := dIn)
        (dOut := dOut) 0))
  -- the ranks of `E` and `D`: invertible minors
  have h1 := ae_isUnit_det_submatrix μ
  -- the rows of the write are nonzero: their entries at `k₁` are
  have h2 : ∀ᵐ θ ∂μ, ∀ i : hid 0, θ.write 0 i k₁ ≠ 0 :=
    ae_all_iff.2 fun i =>
      ae_ne_zero_of_analytic μ (hW i k₁) ⟨θ₁, show (1 : ℝ) ≠ 0 from one_ne_zero⟩
  -- the columns of the read are nonzero: their entries at `k₁` are
  have h3 : ∀ᵐ θ ∂μ, ∀ i : hid 0, θ.read 0 k₁ i ≠ 0 :=
    ae_all_iff.2 fun i =>
      ae_ne_zero_of_analytic μ (hR k₁ i) ⟨θ₁, show (1 : ℝ) ≠ 0 from one_ne_zero⟩
  -- two columns of the read are not collinear: a `2 × 2` minor does not vanish
  have h4 : ∀ᵐ θ ∂μ, ∀ i j : hid 0, i ≠ j →
      θ.read 0 k₁ i * θ.read 0 k₂ j - θ.read 0 k₁ j * θ.read 0 k₂ i ≠ 0 := by
    refine ae_all_iff.2 fun i => ae_all_iff.2 fun j => ?_
    by_cases hij : i = j
    · exact Filter.Eventually.of_forall fun _ h => absurd hij h
    · obtain ⟨E₀, W₀, hEW⟩ := exists_minor_ne_zero hk hk hij
      let θ₀ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut :=
        ⟨0, fun ℓ => Fin.cases (E₀ * W₀) (fun l => l.elim0) ℓ, 0, 0⟩
      have hg : AnalyticOnNhd ℝ
          (fun θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut =>
            θ.read 0 k₁ i * θ.read 0 k₂ j - θ.read 0 k₁ j * θ.read 0 k₂ i) Set.univ :=
        ((hR k₁ i).mul (hR k₂ j)).sub ((hR k₁ j).mul (hR k₂ i))
      exact (ae_ne_zero_of_analytic μ hg ⟨θ₀, hEW⟩).mono fun _ h _ => h
  filter_upwards [h1, h2, h3, h4] with θ h1 h2 h3 h4
  refine ⟨rank_eq_of_isUnit_det_rows_rm θ.E ρ (h1.2.2.1 ρ),
    rank_eq_card_of_isUnit_det θ.D cD (h1.2.1 cD), fun i hi => h2 i (congrFun hi k₁),
    fun i hi => h3 i (congrFun hi k₁), ?_⟩
  -- if `c_i = r c_j`, the minor of the columns `i`, `j` vanishes
  intro i j hij r hr
  have e1 : θ.read 0 k₁ i = r * θ.read 0 k₁ j := congrFun hr k₁
  have e2 : θ.read 0 k₂ i = r * θ.read 0 k₂ j := congrFun hr k₂
  apply h4 i j hij
  rw [e1, e2]
  ring

/-- **Theorem 4.6 (ii) of the skips paper, first sentence, for one MLP block with `s = 0`:** with
`d_in, d_out ≥ d ≥ 2` and a block of any width, under pre-RMSNorm with `ε > 0`, at generic
parameters the residual network has the functional dimension `P - d(d-1)/2`. -/
theorem ae_funDim_mlp_oneBlock_residual_rmsNorm (hε : 0 < ε)
    (hσ : ∀ z, HasDerivAt σ (σ' z) z) (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (hU : UnitsRigid σ σ' d d (hid 0))
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, funDim (Arch.mlp σ (rmsNorm ε) hid) 1 θ
        + Fintype.card d * (Fintype.card d - 1) / 2
      = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut) := by
  filter_upwards [ae_oneBlockGenericRMS μ hd hdIn hdOut] with θ hθ
  exact funDim_mlp_oneBlock_residual_rmsNorm hε hσ hσa hU θ hθ

/-! ### The two kinds of block -/

/-- **Theorem 4.6 (ii) of the skips paper, first sentence, for a `tanh` block:** under pre-RMSNorm
with `ε > 0`, at generic parameters the residual network of one block has the functional
dimension `P - d(d-1)/2`. -/
theorem ae_funDim_tanh_oneBlock_residual_rmsNorm (hε : 0 < ε)
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) Real.tanh (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, funDim (Arch.mlp Real.tanh (rmsNorm ε) hid) 1 θ
        + Fintype.card d * (Fintype.card d - 1) / 2
      = Module.finrank ℝ
          (Params (Arch.mlp (T := T) (d := d) Real.tanh (rmsNorm ε) hid) dIn dOut) := by
  exact ae_funDim_mlp_oneBlock_residual_rmsNorm hε hasDerivAt_tanh analyticOnNhd_tanh
      (tanh_unitsRigid _ _ _) μ hd hdIn hdOut

/-- **Theorem 4.6 (ii) of the skips paper, first sentence, for a GELU block.** -/
theorem ae_funDim_gelu_oneBlock_residual_rmsNorm (hε : 0 < ε)
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, funDim (Arch.mlp gelu (rmsNorm ε) hid) 1 θ
        + Fintype.card d * (Fintype.card d - 1) / 2
      = Module.finrank ℝ
          (Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm ε) hid) dIn dOut) := by
  exact ae_funDim_mlp_oneBlock_residual_rmsNorm hε hasDerivAt_gelu analyticOnNhd_gelu
      (gelu_unitsRigid _ _ _) μ hd hdIn hdOut

end Skips
