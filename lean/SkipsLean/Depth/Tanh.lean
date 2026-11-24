import SkipsLean.Depth.StepTanh
import SkipsLean.Generic.Params

/-!
# Theorem 5.2 (i) without normalization: `tanh` blocks at any depth

Paper (dimension paper): Theorem 5.2 (i), the case without normalization, and its proof in
Appendix D.7 ("The parts together", first paragraph).

A network of `L` `tanh` blocks without skip connections, without normalization and without biases,
with `d_in, d_out ≥ d` and at least `d` hidden units in every block, has the functional dimension
`P - (L + 1) d²` at generic parameters.

The proof of the paper takes `θ` with: (R1) `E`, `D` and every write of rank `d`; for every block
(T1) no row of the write vanishes and (T2) the columns of the read are linearly independent over
`ℚ`; and every `W_read W_write` invertible. Such `θ` are regular (the derivative of a block at `0`
is `v ↦ v W_read W_write`). Claim `(D_L)` holds (Lemma D.5), the step of Lemma D.7 gives `(D_k)`
for `k = L - 1, …, 0`, and Proposition D.4 gives the functional dimension. The conditions fail only
on a set of measure zero; (T2) fails on countably many proper linear subspaces.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]

/-- The conditions on the parameters of a network of `tanh` blocks that the proof of
Theorem 5.2 (i) uses in the case without normalization. -/
structure TanhDepthGeneric (θ : Params (Arch.mlp (T := T) (d := d) Real.tanh id hid) dIn dOut) :
    Prop where
  /-- (R1) -/
  rank_E : θ.E.rank = Fintype.card d
  /-- (R1) -/
  rank_D : θ.D.rank = Fintype.card d
  /-- (R1) -/
  rank_write : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d
  /-- (T1): no row of a write vanishes -/
  write_row_ne_zero : ∀ ℓ (i : hid ℓ), θ.write ℓ i ≠ 0
  /-- (T2): the columns of every read are linearly independent over `ℚ` -/
  read_cols_indep : ∀ ℓ, LinearIndependent ℚ (fun j : hid ℓ => fun i : d => θ.read ℓ i j)
  /-- every `W_read W_write` is invertible -/
  read_mul_write : ∀ ℓ, IsUnit (θ.read ℓ * θ.write ℓ).det

/-- Helper: `M ↦ M.map tanh` has the identity as its derivative at `0`, since `tanh' 0 = 1`. -/
private theorem hasFDerivAt_map_tanh_zero {m n : Type*} [Fintype m] [Fintype n] :
    HasFDerivAt (fun M : Matrix m n ℝ => M.map Real.tanh)
      (ContinuousLinearMap.id ℝ (Matrix m n ℝ)) 0 := by
  refine hasFDerivAt_pi'' fun t => hasFDerivAt_pi'' fun i => ?_
  -- the entry `(t, i)` is `tanh` of the entry `(t, i)` of `M`, and `tanh' 0 = 1 - tanh 0 ^ 2 = 1`
  have h := (hasDerivAt_tanh ((0 : Matrix m n ℝ) t i)).comp_hasFDerivAt (0 : Matrix m n ℝ)
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : n => ℝ) i).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : m => n → ℝ) t)).hasFDerivAt
  refine h.congr_fderiv (ContinuousLinearMap.ext fun M => ?_)
  show (1 - Real.tanh ((0 : Matrix m n ℝ) t i) ^ 2) * M t i = M t i
  rw [Matrix.zero_apply, Real.tanh_zero]
  ring

variable (θ : Params (Arch.mlp (T := T) (d := d) Real.tanh id hid) dIn dOut)

/-- Under the conditions `θ` is regular: the derivative of block `ℓ` at `0` is
`v ↦ v W_read W_write`, which is injective. -/
theorem regular_of_tanhDepthGeneric (hθ : TanhDepthGeneric θ) :
    Regular (Arch.mlp Real.tanh id hid) θ := by
  refine ⟨hθ.rank_E, hθ.rank_D, hθ.rank_write, fun ℓ => ⟨0, ?_⟩⟩
  -- the right multiplications by the read and by the write, as continuous linear maps
  let mR : Matrix T d ℝ →L[ℝ] Matrix T (hid ℓ) ℝ := LinearMap.toContinuousLinearMap
    { toFun := fun n' => n' * θ.read ℓ
      map_add' := fun a b => Matrix.add_mul a b _
      map_smul' := fun c a => Matrix.smul_mul c a _ }
  let mW : Matrix T (hid ℓ) ℝ →L[ℝ] Matrix T d ℝ := LinearMap.toContinuousLinearMap
    { toFun := fun M => M * θ.write ℓ
      map_add' := fun a b => Matrix.add_mul a b _
      map_smul' := fun c a => Matrix.smul_mul c a _ }
  -- the block is `n' ↦ mW ((mR n').map tanh)`; its derivative at `0` is `v ↦ v W_read W_write`
  have h1 : HasFDerivAt (fun M : Matrix T (hid ℓ) ℝ => M.map Real.tanh)
      (ContinuousLinearMap.id ℝ _) (mR 0) := by
    rw [map_zero]
    exact hasFDerivAt_map_tanh_zero
  have hf : HasFDerivAt
      (fun n' : Matrix T d ℝ => (Arch.mlp Real.tanh id hid).f ℓ (n' * θ.read ℓ) * θ.write ℓ)
      (mW.comp ((ContinuousLinearMap.id ℝ _).comp mR)) 0 :=
    mW.hasFDerivAt.comp (0 : Matrix T d ℝ) (h1.comp (0 : Matrix T d ℝ) mR.hasFDerivAt)
  rw [hf.fderiv]
  -- `v ↦ v W_read W_write` is injective: multiply on the right by `(W_read W_write)⁻¹`
  have key : ∀ v : Matrix T d ℝ, v * θ.read ℓ * θ.write ℓ * (θ.read ℓ * θ.write ℓ)⁻¹ = v := by
    intro v
    rw [Matrix.mul_assoc v, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (hθ.read_mul_write ℓ),
      Matrix.mul_one]
  intro v w hvw
  have hvw' : v * θ.read ℓ * θ.write ℓ = w * θ.read ℓ * θ.write ℓ := hvw
  rw [← key v, ← key w, hvw']

/-- Under the conditions Claim `(D_k)` holds at every hidden state: `(D_L)` by Lemma D.5, and then
`(D_k)` for `k = L - 1, …, 0` by Lemma D.7. -/
theorem claim_of_tanhDepthGeneric [Nonempty T] (hθ : TanhDepthGeneric θ) (k : Fin (L + 1)) :
    Claim (Arch.mlp Real.tanh id hid) θ k := by
  -- `(D_L)` by Lemma D.5, then `(D_{k+1}) ⇒ (D_k)` by Lemma D.7
  induction k using Fin.reverseInduction with
  | last => exact claim_last _ θ rfl
  | cast k ih =>
    exact claim_castSucc_tanh θ (regular_of_tanhDepthGeneric θ hθ) k (hθ.write_row_ne_zero k)
      (hθ.read_cols_indep k) ih

/-- **Theorem 5.2 (i) without normalization, under the conditions of its proof:** the functional
dimension of a network of `L` `tanh` blocks is `P - (L + 1) d²`. -/
theorem funDim_tanh_skipless [Nonempty T] (hθ : TanhDepthGeneric θ) :
    funDim (Arch.mlp Real.tanh id hid) 0 θ + (L + 1) * Fintype.card d ^ 2
      = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) Real.tanh id hid) dIn dOut) :=
  -- Proposition D.4, with the blocks analytic, `θ` regular and `(D_0)`
  funDim_of_claim _ θ rfl (fun ℓ => analyticOnNhd_f_mlp analyticOnNhd_tanh ℓ)
    (regular_of_tanhDepthGeneric θ hθ) (claim_of_tanhDepthGeneric θ hθ 0)

/-- Helper: the determinant of a product of two matrices that depend linearly on a point of a
finite-dimensional space is analytic: a finite sum of signed finite products of entries, and each
entry is a polynomial of degree two. -/
private theorem analyticOnNhd_det_mul {P m : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [FiniteDimensional ℝ P] [Fintype m] (F : P →ₗ[ℝ] Matrix d m ℝ)
    (G : P →ₗ[ℝ] Matrix m d ℝ) : AnalyticOnNhd ℝ (fun y => (F y * G y).det) Set.univ := by
  simp only [Matrix.det_apply']
  exact Finset.analyticOnNhd_fun_sum _ fun σ _ => analyticOnNhd_const.mul
    (Finset.analyticOnNhd_fun_prod _ fun i _ => analyticOnNhd_mul_apply F G (σ i) i)

omit [Fintype d] in
/-- Helper: the `d × m` matrix whose row `i` is the unit vector at `c i`, times its transpose, is
the identity. -/
private theorem indicator_mul_transpose {m : Type*} [Fintype m] [DecidableEq m] (c : d ↪ m) :
    (Matrix.of fun i j => if c i = j then (1 : ℝ) else 0) *
      (Matrix.of fun i j => if c i = j then (1 : ℝ) else 0)ᵀ = 1 := by
  ext i i'
  simp [Matrix.mul_apply, Matrix.one_apply, c.injective.eq_iff]

/-- The conditions hold at generic parameters, when `d_in, d_out ≥ d ≥ 1` and every block has at
least `d` hidden units. -/
theorem ae_tanhDepthGeneric [Nonempty d]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) Real.tanh id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, TanhDepthGeneric θ := by
  classical
  obtain k₀ : d := Classical.arbitrary d
  obtain ⟨cD⟩ := Function.Embedding.nonempty_of_card_le hdOut
  -- (R1): `E` and the writes (`Generic/Params.lean`); `D`, by an invertible `d × d` minor
  have h1 := ae_rank_E_write μ hdIn hhid
  have h2 := ae_isUnit_det_submatrix μ
  -- (T1): the entry `k₀` of every row of every write is a nonzero linear functional, so it is
  -- nonzero at generic parameters
  have h3 : ∀ᵐ θ ∂μ, ∀ ℓ (i : hid ℓ), θ.write ℓ i k₀ ≠ 0 := by
    refine ae_all_iff.2 fun ℓ => ae_all_iff.2 fun i => ?_
    let l : Params (Arch.mlp (T := T) (d := d) Real.tanh id hid) dIn dOut →ₗ[ℝ] ℝ :=
      (Matrix.entryLinearMap ℝ ℝ i k₀).comp (Params.linWrite
        (A := Arch.mlp (T := T) (d := d) Real.tanh id hid) (dIn := dIn) (dOut := dOut) ℓ)
    have hl : ∀ θ, l θ = θ.write ℓ i k₀ := fun θ => rfl
    -- it is `1` at the parameters whose writes have all entries `1`
    have h₁ : l ⟨0, 0, fun _ => Matrix.of fun _ _ => 1, 0⟩ ≠ 0 := by
      rw [hl]
      exact one_ne_zero
    filter_upwards [ae_ne_zero_of_analytic μ (analyticOnNhd_linear l) ⟨_, h₁⟩] with θ h
    rwa [hl] at h
  -- (T2): for rationals `κ ≠ 0`, the entry `k₀` of `∑ κ_j c_j` is a nonzero
  -- linear functional, so it is nonzero at generic parameters; there are countably many `κ`
  have h4 : ∀ᵐ θ ∂μ, ∀ ℓ (κ : hid ℓ → ℚ),
      ∑ j, κ j • (fun i : d => θ.read ℓ i j) = 0 → ∀ j, κ j = 0 := by
    refine ae_all_iff.2 fun ℓ => ae_all_iff.2 fun κ => ?_
    by_cases hκ : ∀ j, κ j = 0
    · exact Filter.Eventually.of_forall fun _ _ => hκ
    obtain ⟨j₀, hj₀⟩ := not_forall.1 hκ
    have hg : AnalyticOnNhd ℝ
        (fun θ : Params (Arch.mlp (T := T) (d := d) Real.tanh id hid) dIn dOut =>
          ∑ j, (κ j : ℝ) * θ.read ℓ k₀ j) Set.univ :=
      Finset.analyticOnNhd_fun_sum _ fun j _ => analyticOnNhd_const.mul
        (analyticOnNhd_linear ((Matrix.entryLinearMap ℝ ℝ k₀ j).comp (Params.linRead
          (A := Arch.mlp (T := T) (d := d) Real.tanh id hid) (dIn := dIn) (dOut := dOut) ℓ)))
    -- it is `κ_{j₀}` at the parameters whose read `ℓ` has the column `j₀` of ones, zeros elsewhere
    let θ₀ : Params (Arch.mlp (T := T) (d := d) Real.tanh id hid) dIn dOut :=
      ⟨0, Pi.single (M := fun ℓ => Matrix d (hid ℓ) ℝ) ℓ
        (Matrix.of fun _ j => if j = j₀ then 1 else 0), 0, 0⟩
    have hθ₀ : ∑ j, (κ j : ℝ) * θ₀.read ℓ k₀ j ≠ 0 := by
      show ∑ j, (κ j : ℝ) * Pi.single (M := fun ℓ => Matrix d (hid ℓ) ℝ) ℓ
        (Matrix.of fun _ j => if j = j₀ then (1 : ℝ) else 0) ℓ k₀ j ≠ 0
      rw [Pi.single_eq_same]
      simp only [Matrix.of_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, ite_true]
      exact Rat.cast_ne_zero.2 hj₀
    filter_upwards [ae_ne_zero_of_analytic μ hg ⟨θ₀, hθ₀⟩] with θ hθ hsum
    -- the entry `k₀` of `∑ κ_j c_j = 0`
    have hk₀ := congrFun hsum k₀
    simp only [Finset.sum_apply, Pi.smul_apply, Rat.smul_def, Pi.zero_apply] at hk₀
    exact absurd hk₀ hθ
  -- every `W_read W_write` is invertible: its determinant is analytic, and it is `1` at the
  -- parameters whose read `ℓ` is `1` on `d` of its columns and `0` elsewhere, and whose write is
  -- the transpose of the read
  have h5 : ∀ᵐ θ ∂μ, ∀ ℓ, (θ.read ℓ * θ.write ℓ).det ≠ 0 := by
    have cR : ∀ ℓ, d ↪ hid ℓ := fun ℓ =>
      (Function.Embedding.nonempty_of_card_le (hhid ℓ)).some
    let R : ∀ ℓ, Matrix d (hid ℓ) ℝ := fun ℓ =>
      Matrix.of fun i j => if cR ℓ i = j then 1 else 0
    let θ₀ : Params (Arch.mlp (T := T) (d := d) Real.tanh id hid) dIn dOut :=
      ⟨0, R, fun ℓ => (R ℓ)ᵀ, 0⟩
    refine ae_all_iff.2 fun ℓ => ae_ne_zero_of_analytic μ (analyticOnNhd_det_mul
      (Params.linRead (A := Arch.mlp (T := T) (d := d) Real.tanh id hid) (dIn := dIn)
        (dOut := dOut) ℓ)
      (Params.linWrite (A := Arch.mlp (T := T) (d := d) Real.tanh id hid) (dIn := dIn)
        (dOut := dOut) ℓ)) ⟨θ₀, ?_⟩
    show (R ℓ * (R ℓ)ᵀ).det ≠ 0
    rw [indicator_mul_transpose, Matrix.det_one]
    exact one_ne_zero
  filter_upwards [h1, h2, h3, h4, h5] with θ h1 h2 h3 h4 h5
  exact ⟨h1.1, rank_eq_card_of_isUnit_det θ.D cD (h2.2.1 cD), h1.2,
    fun ℓ i hi => h3 ℓ i (congrFun hi k₀), fun ℓ => Fintype.linearIndependent_iff.2 (h4 ℓ),
    fun ℓ => isUnit_iff_ne_zero.2 (h5 ℓ)⟩

/-- **Theorem 5.2 (i), the case without normalization:** a network of `L` `tanh` blocks without
skip connections, without normalization and without biases, with `d_in, d_out ≥ d ≥ 2` and at
least `d` hidden units in every block, has the functional dimension `P - (L + 1) d²` at generic
parameters. (The proof uses `d ≥ 1` only.) -/
theorem ae_funDim_tanh_skipless [Nonempty T]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) Real.tanh id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, funDim (Arch.mlp Real.tanh id hid) 0 θ + (L + 1) * Fintype.card d ^ 2
      = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) Real.tanh id hid) dIn dOut) := by
  have : Nonempty d := Fintype.card_pos_iff.1 (by omega)
  -- the conclusion holds wherever the conditions of the proof hold
  filter_upwards [ae_tanhDepthGeneric μ hdIn hdOut hhid] with θ hθ
  exact funDim_tanh_skipless θ hθ

end Skips
