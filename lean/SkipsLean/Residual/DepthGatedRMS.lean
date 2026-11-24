import SkipsLean.Residual.SmallWritesRMSSteps
import SkipsLean.Residual.UpperBoundSymmetries
import SkipsLean.OneBlock.SwiGLU
import SkipsLean.OneBlock.GeGLU
import SkipsLean.Activations.Analytic

/-!
# Residual networks of SwiGLU and GeGLU blocks at any depth, under pre-RMSNorm

Paper (skips paper): Lemma A.27 (Small writes), its second value `fd(θ_τ) = P - d(d-1)/2 - s`
(pre-RMSNorm with `ε > 0`, no biases), and Theorem 4.7 under pre-RMSNorm, for gated blocks:
SwiGLU and GeGLU. Here `s` is the number of hidden units of all blocks. The blocks may have any
widths.

As in `Residual/DepthMlpRMS.lean`, with Lemma B.3 for gated units (`GatedUnitsRescale`, "with `E`
and `D` replaced by the identity and `M = 0`") applied to the hidden units of all blocks together:
a direction `η` that is flat for the limit `J_0` has `η_E = E Y`, `η_D = -Y D` with `Y`
antisymmetric, no component at the gates, and rescales every hidden unit. These directions form a
space of dimension `d(d-1)/2 + s`.
-/

namespace Skips

open Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d]
  [Fintype dIn] [Fintype dOut]
variable {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]
variable {σ σ' : ℝ → ℝ} {ε : ℝ}

/-- **The conditions on `θ` in Lemma A.27 under pre-RMSNorm, for gated blocks:** `E` and `D` have
rank `d`, and the hypotheses of Lemma B.3 hold for the units of all blocks together, "with `E` and
`D` replaced by the identity": every row of every `W_write^ℓ` and every value column of every
`W_read^ℓ` is nonzero, and the gate columns of the `W_read^ℓ`, over all blocks `ℓ` and hidden
units `i`, are nonzero and pairwise non-collinear. -/
structure SmallWritesGenericGatedRMS
    (θ : Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut) : Prop where
  rank_E : θ.E.rank = Fintype.card d
  rank_D : θ.D.rank = Fintype.card d
  /-- every row of `W_write^ℓ` is nonzero -/
  row_ne_zero : ∀ ℓ i, θ.write ℓ i ≠ 0
  /-- every gate column of `W_read^ℓ` is nonzero -/
  gate_ne_zero : ∀ ℓ (i : hid ℓ), (θ.read ℓ)ᵀ (Sum.inl i) ≠ 0
  /-- the gate columns of the reads of all blocks together are pairwise non-collinear -/
  gate_not_collinear : ∀ p q : (Σ ℓ, hid ℓ), p ≠ q → ∀ r : ℝ,
    (θ.read p.1)ᵀ (Sum.inl p.2) ≠ r • (θ.read q.1)ᵀ (Sum.inl q.2)
  /-- every value column of `W_read^ℓ` is nonzero -/
  value_ne_zero : ∀ ℓ (i : hid ℓ), (θ.read ℓ)ᵀ (Sum.inr i) ≠ 0

/-! ### Helpers: the derivative of a block, and its analyticity in the hidden state -/

omit [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (the private `hasDerivAt_affineDG` of `Residual/DepthGated.lean`): `τ ↦ a + τ b` has
the derivative `b` at `0`. -/
private theorem hasDerivAt_affine_dgr (a b : ℝ) : HasDerivAt (fun τ : ℝ => a + τ * b) b 0 := by
  have h := ((hasDerivAt_id' (x := (0 : ℝ))).mul_const b).const_add a
  rw [one_mul] at h
  exact h

omit [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (the private `fderiv_f_gated_apply_rg` of `OneBlock/ResidualRMSGated.lean`, for any
block `ℓ`): the derivative of the map of a gated block at `M` along `N`: entry `(t, i)` is
`σ'(M_{t, g i}) N_{t, g i} M_{t, v i} + σ(M_{t, g i}) N_{t, v i}`. -/
private theorem fderiv_f_gated_apply_dgr (hσ : ∀ z, HasDerivAt σ (σ' z) z) (ℓ : Fin L)
    (M N : Matrix T (hid ℓ ⊕ hid ℓ) ℝ) (t : T) (i : hid ℓ) :
    fderiv ℝ ((Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid).f ℓ) M N t i
      = σ' (M t (Sum.inl i)) * N t (Sum.inl i) * M t (Sum.inr i)
        + σ (M t (Sum.inl i)) * N t (Sum.inr i) := by
  have hd := differentiable_f_gated (T := T) (d := d) (χ := rmsNorm ε) (hid := hid)
    (fun z => (hσ z).differentiableAt) ℓ
  -- the chain rule along the line `τ ↦ M + τ N`
  have hline : HasDerivAt (fun τ : ℝ => M + τ • N) N 0 := by
    have h := ((hasDerivAt_id (0 : ℝ)).smul_const N).const_add M
    rw [one_smul] at h
    exact h
  have h1 := (hd M).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hline (by rw [zero_smul, add_zero])
  have h2 := hasDerivAt_pi.1 (hasDerivAt_pi.1 h1 t) i
  -- the same derivative computed on the entry `(t, i)`
  have h3 : HasDerivAt (fun τ : ℝ => σ (M t (Sum.inl i) + τ * N t (Sum.inl i))
      * (M t (Sum.inr i) + τ * N t (Sum.inr i)))
      (σ' (M t (Sum.inl i)) * N t (Sum.inl i) * M t (Sum.inr i)
        + σ (M t (Sum.inl i)) * N t (Sum.inr i)) 0 := by
    have hu := hasDerivAt_affine_dgr (M t (Sum.inl i)) (N t (Sum.inl i))
    have hw := hasDerivAt_affine_dgr (M t (Sum.inr i)) (N t (Sum.inr i))
    have h := ((hσ _).comp (0 : ℝ) hu).mul hw
    convert h using 1
    · rfl
    · simp only [Function.comp_apply, zero_mul, add_zero]
  exact h2.unique h3

/-- Helper (the private `gatedDir` of `OneBlock/ResidualRMSGated.lean`): the derivative of
`n ↦ f(n W_read) W_write` along the entries `R'` (of the read) and `W'` (of the write), entry by
entry, at the read `R` and the write `W`:
`∑_i [σ(z_i) w_i W'_{i k} + σ'(z_i) (n R')_{t, g i} w_i W_{i k} + σ(z_i) (n R')_{t, v i} W_{i k}]`
with `z_i = (n R)_{t, g i}` and `w_i = (n R)_{t, v i}` (the order of the terms of Lemma B.3). -/
private noncomputable def gatedDirDGR (σ σ' : ℝ → ℝ) {q : Type*} [Fintype q]
    (R R' : Matrix d (q ⊕ q) ℝ) (W W' : Matrix q d ℝ) (n : Matrix T d ℝ) : Matrix T d ℝ :=
  Matrix.of fun t k => ∑ i : q,
    (σ ((n * R) t (Sum.inl i)) * (n * R) t (Sum.inr i) * W' i k
      + σ' ((n * R) t (Sum.inl i)) * (n * R') t (Sum.inl i) * (n * R) t (Sum.inr i) * W i k
      + σ ((n * R) t (Sum.inl i)) * (n * R') t (Sum.inr i) * W i k)

omit [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the derivative of block `ℓ` along the entries of a direction at its read and its write
is `gatedDirDGR`. -/
private theorem fderiv_add_eq_gatedDirDGR (hσ : ∀ z, HasDerivAt σ (σ' z) z) (ℓ : Fin L)
    (n : Matrix T d ℝ) (R R' : Matrix d (hid ℓ ⊕ hid ℓ) ℝ) (W W' : Matrix (hid ℓ) d ℝ) :
    fderiv ℝ ((Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid).f ℓ) (n * R) (n * R') * W
        + (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid).f ℓ (n * R) * W'
      = gatedDirDGR σ σ' R R' W W' n := by
  ext t k
  rw [gatedDirDGR, Matrix.of_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [fderiv_f_gated_apply_dgr hσ]
  have hf : (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid).f ℓ (n * R) t i
      = σ ((n * R) t (Sum.inl i)) * (n * R) t (Sum.inr i) := rfl
  rw [hf]
  ring

omit [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: an entry of `n R` is a real-analytic (linear) function of `n`. -/
private theorem analyticOnNhd_mul_entry_dgr {m : Type*} (R : Matrix d m ℝ) (t : T) (j : m) :
    AnalyticOnNhd ℝ (fun n : Matrix T d ℝ => (n * R) t j) Set.univ := by
  have h : (fun n : Matrix T d ℝ => (n * R) t j) = fun n => ∑ k, n t k * R k j := rfl
  rw [h]
  exact Finset.analyticOnNhd_fun_sum _ fun k _ =>
    (analyticOnNhd_matrix_entry t k).mul analyticOnNhd_const

omit [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (Step 4 (b)): for analytic `σ` and `σ'`, every entry of `gatedDirDGR` is a
real-analytic function of the hidden state `n`. -/
private theorem analyticOnNhd_gatedDirDGR_apply (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (hσ'a : AnalyticOnNhd ℝ σ' Set.univ) {q : Type*} [Fintype q]
    (R R' : Matrix d (q ⊕ q) ℝ) (W W' : Matrix q d ℝ) (t : T) (k : d) :
    AnalyticOnNhd ℝ (fun n : Matrix T d ℝ => gatedDirDGR σ σ' R R' W W' n t k) Set.univ := by
  have hz := fun j => analyticOnNhd_mul_entry_dgr (T := T) R t j
  have hz' := fun j => analyticOnNhd_mul_entry_dgr (T := T) R' t j
  have hs := fun j => hσa.comp (hz j) (Set.mapsTo_univ _ _)
  have hs' := fun j => hσ'a.comp (hz j) (Set.mapsTo_univ _ _)
  exact Finset.analyticOnNhd_fun_sum _ fun i _ =>
    ((((hs (Sum.inl i)).mul (hz (Sum.inr i))).mul analyticOnNhd_const).add
      ((((hs' (Sum.inl i)).mul (hz' (Sum.inl i))).mul (hz (Sum.inr i))).mul
        analyticOnNhd_const)).add
      (((hs (Sum.inl i)).mul (hz' (Sum.inr i))).mul analyticOnNhd_const)

/-- **Proof of Lemma A.27 under pre-RMSNorm, gated blocks, the flat directions of `J_0`:** under
the conditions of the lemma, a direction `η` with `(J_0 η)(x) = 0` at every input `x` has
`η_E = E Y` and `η_D = -Y D` for one antisymmetric matrix `Y`, vanishes at every gate column of a
read, and rescales every hidden unit: for numbers `α_{ℓ,i}`, the value column of unit `i` of block
`ℓ` in `η_read^ℓ` is `-α_{ℓ,i}` times that of `W_read^ℓ`, and its row in `η_write^ℓ` is `α_{ℓ,i}`
times that of `W_write^ℓ`. -/
theorem smallWritesLimitNorm_eq_zero_gated_rmsNorm (hε : 0 < ε)
    (hσ : ∀ z, HasDerivAt σ (σ' z) z) (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (hU : GatedUnitsRescale σ σ' d d (Σ ℓ, hid ℓ))
    (θ : Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)
    (hθ : SmallWritesGenericGatedRMS θ)
    (η : Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)
    (hη : ∀ x, smallWritesLimitNorm (Arch.gated σ (rmsNorm ε) hid) θ η x = 0) :
    ∃ (Y : Matrix d d ℝ) (α : ∀ ℓ, hid ℓ → ℝ), Yᵀ = -Y ∧ η.E = θ.E * Y ∧ η.D = -(Y * θ.D)
      ∧ (∀ ℓ (i : hid ℓ) a, η.read ℓ a (Sum.inl i) = 0)
      ∧ (∀ ℓ (i : hid ℓ) a, η.read ℓ a (Sum.inr i) = -(α ℓ i) * θ.read ℓ a (Sum.inr i))
      ∧ (∀ ℓ (i : hid ℓ) a, η.write ℓ i a = α ℓ i * θ.write ℓ i a) := by
  -- Steps 1 to 3 (`Residual/SmallWritesRMSSteps.lean`): `Y` antisymmetric, `η_E = E Y`,
  -- `η_D = -Y D`, and the derivative of the wide block along `η` vanishes at every `n = N_ε(x E)`
  have hf : ∀ ℓ, ContDiff ℝ 1 ((Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid).f ℓ) :=
    fun ℓ => (analyticOnNhd_f_gated hσa ℓ).contDiff
  obtain ⟨Y, hY, hYE, hYD, hF⟩ := exists_antisymm_of_smallWritesLimitNorm_rmsNorm
    (A := Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) hε rfl hf θ hθ.rank_E hθ.rank_D η hη
  -- Step 4 (a): `x ↦ x E` is onto (`E` has a left inverse `B`), so this derivative vanishes on
  -- the range of `N_ε`
  obtain ⟨B, hB⟩ := Matrix.vecMul_surjective_iff_exists_left_inverse.mp
    (Matrix.vecMul_surjective_iff_rank_eq_card.mpr hθ.rank_E)
  have hrange : ∀ h : Matrix T d ℝ, ∑ ℓ, gatedDirDGR σ σ' (θ.read ℓ) (η.read ℓ) (θ.write ℓ)
      (η.write ℓ) (rmsNorm ε h) = 0 := by
    intro h
    have hx := hF (h * B)
    have hhB : h * B * θ.E = h := by rw [Matrix.mul_assoc, hB, Matrix.mul_one]
    rw [hhB] at hx
    refine Eq.trans ?_ hx
    exact Finset.sum_congr rfl fun ℓ _ => (fderiv_add_eq_gatedDirDGR hσ ℓ (rmsNorm ε h)
      (θ.read ℓ) (η.read ℓ) (θ.write ℓ) (η.write ℓ)).symm
  -- Step 4 (b): its entries are real-analytic in `n` (`σ' = deriv σ` is analytic) and vanish on
  -- the open range of `N_ε`, which contains `N_ε(0)`, so they vanish everywhere
  have hσ'a : AnalyticOnNhd ℝ σ' Set.univ := by
    have h : σ' = deriv σ := funext fun z => (hσ z).deriv.symm
    rw [h]
    exact hσa.deriv
  have hzero : ∀ n : Matrix T d ℝ, ∑ ℓ, gatedDirDGR σ σ' (θ.read ℓ) (η.read ℓ) (θ.write ℓ)
      (η.write ℓ) n = 0 := by
    intro n
    ext t k
    have hA : AnalyticOnNhd ℝ (fun n : Matrix T d ℝ => (∑ ℓ, gatedDirDGR σ σ' (θ.read ℓ)
        (η.read ℓ) (θ.write ℓ) (η.write ℓ) n) t k) Set.univ := by
      have h : (fun n : Matrix T d ℝ => (∑ ℓ, gatedDirDGR σ σ' (θ.read ℓ) (η.read ℓ)
          (θ.write ℓ) (η.write ℓ) n) t k) = fun n => ∑ ℓ, gatedDirDGR σ σ' (θ.read ℓ)
          (η.read ℓ) (θ.write ℓ) (η.write ℓ) n t k := by
        funext n
        rw [Matrix.sum_apply]
      rw [h]
      exact Finset.analyticOnNhd_fun_sum _ fun ℓ _ =>
        analyticOnNhd_gatedDirDGR_apply hσa hσ'a _ _ _ _ t k
    have hopen : IsOpen (Set.range (rmsNorm ε : Matrix T d ℝ → Matrix T d ℝ)) :=
      (isOpenMap_rmsNorm hε).isOpen_range
    have hev : (fun n : Matrix T d ℝ => (∑ ℓ, gatedDirDGR σ σ' (θ.read ℓ) (η.read ℓ)
        (θ.write ℓ) (η.write ℓ) n) t k) =ᶠ[nhds (rmsNorm ε 0)] 0 :=
      Filter.eventually_of_mem (hopen.mem_nhds (Set.mem_range_self 0)) fun n hn => by
        obtain ⟨h, rfl⟩ := hn
        simp only [hrange h, Matrix.zero_apply, Pi.zero_apply]
    exact hA.eqOn_zero_of_preconnected_of_eventuallyEq_zero convex_univ.isPreconnected
      (Set.mem_univ _) hev (Set.mem_univ n)
  -- Step 4 (c): Lemma B.3 for the hidden units of all blocks together, with `E` and `D` replaced
  -- by the identity and `M = 0` (inputs `n` with all rows equal to `v`): the gate columns of
  -- `η_read^ℓ` vanish, and every unit only rescales its value
  obtain ⟨-, -, hc, -, α, hα⟩ := hU
    (fun p => (θ.read p.1)ᵀ (Sum.inl p.2)) 0 (fun p => (θ.read p.1)ᵀ (Sum.inr p.2)) 0
    (fun p => θ.write p.1 p.2) 0 0 (fun p => (η.read p.1)ᵀ (Sum.inl p.2)) 0
    (fun p => (η.read p.1)ᵀ (Sum.inr p.2)) 0 (fun p => η.write p.1 p.2)
    (fun p => hθ.row_ne_zero p.1 p.2) (fun p => hθ.gate_ne_zero p.1 p.2)
    (fun p q hpq => hθ.gate_not_collinear p q hpq) (fun p => hθ.value_ne_zero p.1 p.2) (by
      intro v
      funext k
      have h := congrFun (congrFun (hzero (Matrix.of fun _ => v)) (Classical.arbitrary T)) k
      rw [Matrix.sum_apply] at h
      simp only [Matrix.vecMul_zero, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        Pi.zero_apply, add_zero, zero_add]
      rw [Fintype.sum_sigma]
      exact h)
  -- Step 4 (d): the clauses, entry by entry
  refine ⟨Y, fun ℓ i => α ⟨ℓ, i⟩, hY, hYE, hYD, fun ℓ i a => ?_, fun ℓ i a => ?_,
    fun ℓ i a => ?_⟩
  · exact congrFun (congrFun hc ⟨ℓ, i⟩) a
  · exact congrFun (hα ⟨ℓ, i⟩).1 a
  · exact congrFun (hα ⟨ℓ, i⟩).2.2 a

/-- Helper (the private `limitFlatLin` of `Residual/DepthGated.lean`, under pre-RMSNorm): the
flat directions of `J_0` found in `smallWritesLimitNorm_eq_zero_gated_rmsNorm`,
`(Y, α) ↦ (E Y, the reads with gate columns `0` and value columns `-α_{ℓ,i}` times those of
`W_read^ℓ`, the writes with rows `α_{ℓ,i}` times those of `W_write^ℓ`, -Y D)`, as a linear map. -/
private noncomputable def limitFlatLinRMS
    (θ : Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut) :
    (Matrix d d ℝ × (∀ ℓ, hid ℓ → ℝ)) →ₗ[ℝ]
      Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut where
  toFun p := ⟨θ.E * p.1,
    fun ℓ => Matrix.of fun k j =>
      Sum.elim (fun _ => 0) (fun i => -(p.2 ℓ i) * θ.read ℓ k (Sum.inr i)) j,
    fun ℓ => Matrix.of fun i k => p.2 ℓ i * θ.write ℓ i k, -(p.1 * θ.D)⟩
  map_add' p q := by
    apply Params.ext'
    · exact Matrix.mul_add _ _ _
    · intro ℓ
      ext k j
      rcases j with i | i
      · exact (add_zero 0).symm
      · show -((p.2 + q.2) ℓ i) * θ.read ℓ k (Sum.inr i)
          = -(p.2 ℓ i) * θ.read ℓ k (Sum.inr i) + -(q.2 ℓ i) * θ.read ℓ k (Sum.inr i)
        rw [Pi.add_apply, Pi.add_apply]
        ring
    · intro ℓ
      ext i k
      show (p.2 + q.2) ℓ i * θ.write ℓ i k = p.2 ℓ i * θ.write ℓ i k + q.2 ℓ i * θ.write ℓ i k
      rw [Pi.add_apply, Pi.add_apply]
      ring
    · show -((p.1 + q.1) * θ.D) = -(p.1 * θ.D) + -(q.1 * θ.D)
      rw [Matrix.add_mul, neg_add]
  map_smul' c p := by
    apply Params.ext'
    · exact Matrix.mul_smul _ _ _
    · intro ℓ
      ext k j
      rcases j with i | i
      · exact (smul_zero c).symm
      · show -((c • p.2) ℓ i) * θ.read ℓ k (Sum.inr i) = c * (-(p.2 ℓ i) * θ.read ℓ k (Sum.inr i))
        rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul]
        ring
    · intro ℓ
      ext i k
      show (c • p.2) ℓ i * θ.write ℓ i k = c * (p.2 ℓ i * θ.write ℓ i k)
      rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul]
      ring
    · show -((c • p.1) * θ.D) = c • -(p.1 * θ.D)
      rw [Matrix.smul_mul, smul_neg]

omit [Fintype T] [Nonempty T] [Fintype dIn] [Fintype dOut] in
/-- Helper: the pairs `(Y, α)` of an antisymmetric `d × d` matrix and one number per hidden unit
form a space of dimension `d(d-1)/2 + s`. -/
private theorem finrank_limitFlatDomainRMS :
    Module.finrank ℝ (antisymmetric d × (∀ ℓ, hid ℓ → ℝ))
      = Fintype.card d * (Fintype.card d - 1) / 2 + ∑ ℓ, Fintype.card (hid ℓ) := by
  rw [Module.finrank_prod, finrank_antisymmetric, Module.finrank_pi_fintype]
  simp only [Module.finrank_fintype_fun_eq_card]

/-- **Lemma A.27 (Small writes), second value, for gated blocks, under the conditions of its
proof:** under pre-RMSNorm with `ε > 0`, for all small `τ ≠ 0` the residual network has
`fd(θ_τ) = P - d(d-1)/2 - s`, with `s` the number of hidden units. -/
theorem eventually_funDim_smallWrites_gated_rmsNorm (hε : 0 < ε)
    (hσ : ∀ z, HasDerivAt σ (σ' z) z) (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (hU : GatedUnitsRescale σ σ' d d (Σ ℓ, hid ℓ))
    (θ : Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)
    (hθ : SmallWritesGenericGatedRMS θ) :
    ∀ᶠ τ in 𝓝[≠] (0 : ℝ),
      funDim (Arch.gated σ (rmsNorm ε) hid) 1 (θ.smallWrites τ)
          + (Fintype.card d * (Fintype.card d - 1) / 2 + ∑ ℓ, Fintype.card (hid ℓ))
        = Module.finrank ℝ
            (Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut) := by
  -- `≥`: every flat direction of `J_0` lies in the range of `(Y, α) ↦ limitFlatLinRMS θ (Y, α)`
  -- with `Y` antisymmetric (step 1), of dimension at most `d(d-1)/2 + s`
  let Φ : (antisymmetric d × (∀ ℓ, hid ℓ → ℝ)) →ₗ[ℝ]
      Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut :=
    (limitFlatLinRMS θ).comp ((antisymmetric d).subtype.prodMap LinearMap.id)
  have hV : ∀ η, (∀ x, smallWritesLimitNorm (Arch.gated σ (rmsNorm ε) hid) θ η x = 0) →
      η ∈ LinearMap.range Φ := by
    intro η hη
    obtain ⟨Y, α, hY, hE, hD, hg, hv, hw⟩ :=
      smallWritesLimitNorm_eq_zero_gated_rmsNorm hε hσ hσa hU θ hθ η hη
    refine LinearMap.mem_range.2 ⟨(⟨Y, hY⟩, α), ?_⟩
    apply Params.ext'
    · exact hE.symm
    · intro ℓ
      ext k j
      rcases j with i | i
      · exact (hg ℓ i k).symm
      · exact (hv ℓ i k).symm
    · intro ℓ
      ext i k
      exact (hw ℓ i k).symm
    · exact hD.symm
  have hdim : Module.finrank ℝ (LinearMap.range Φ)
      ≤ Fintype.card d * (Fintype.card d - 1) / 2 + ∑ ℓ, Fintype.card (hid ℓ) :=
    (LinearMap.finrank_range_le _).trans finrank_limitFlatDomainRMS.le
  have hge := eventually_funDim_smallWrites_ge_norm (Arch.gated σ (rmsNorm ε) hid) θ
    (analyticOnNhd_rmsNorm hε) (fun ℓ => analyticOnNhd_f_gated hσa ℓ) _ hV
  -- `≤`: at every `τ` the network has the symmetries of one orthogonal change of basis and of the
  -- rescalings; `E` and the reads of `θ_τ` are those of `θ`
  filter_upwards [hge] with τ hτ
  have hle := funDim_add_le_residual_gated_rmsNorm ε (θ.smallWrites τ) hθ.rank_E
    (fun ℓ i => hθ.value_ne_zero ℓ i)
  omega

omit [Fintype T] [Nonempty T] [Fintype dIn] [Fintype dOut] in
/-- Helper (the private `rank_eq_of_isUnit_det_submatrix` of `Generic/Params.lean`): a matrix
with `d` columns has rank `d` if some `d` of its rows form an invertible matrix. -/
private theorem rank_eq_of_isUnit_det_rows_dgr {m : Type*} (M : Matrix m d ℝ) (ρ : d ↪ m)
    (h : IsUnit (M.submatrix ρ id).det) : M.rank = Fintype.card d :=
  le_antisymm (Matrix.rank_le_card_width M)
    ((Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).2 h)).symm.le.trans
      (Matrix.rank_submatrix_le M ρ id))

/-- The conditions of Lemma A.27 under pre-RMSNorm for gated blocks hold at generic parameters,
for `d_in, d_out ≥ d ≥ 2` and blocks of any widths. -/
theorem ae_smallWritesGenericGatedRMS
    (μ : Measure (Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, SmallWritesGenericGatedRMS θ := by
  classical
  -- two distinct coordinates `k₁ ≠ k₂` of the hidden states, `d` rows of `E`, `d` columns of `D`
  obtain ⟨k₁, k₂, hk⟩ := Fintype.exists_pair_of_one_lt_card (show 1 < Fintype.card d by omega)
  obtain ⟨ρE⟩ := Function.Embedding.nonempty_of_card_le hdIn
  obtain ⟨cD⟩ := Function.Embedding.nonempty_of_card_le hdOut
  -- the ranks of `E` and `D`: invertible `d × d` minors (`Generic/Params.lean`)
  have h1 := ae_isUnit_det_submatrix μ
  -- an entry of a write or of a read is a linear functional of the parameters, not zero at the
  -- parameters with all entries `1`
  let θ₁ : Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut :=
    ⟨Matrix.of fun _ _ => 1, fun _ => Matrix.of fun _ _ => 1, fun _ => Matrix.of fun _ _ => 1,
      Matrix.of fun _ _ => 1⟩
  have hr : ∀ ℓ (k : d) (j : hid ℓ ⊕ hid ℓ), AnalyticOnNhd ℝ
      (fun θ : Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut =>
        θ.read ℓ k j) Set.univ := fun ℓ k j =>
    analyticOnNhd_linear ((Matrix.entryLinearMap ℝ ℝ k j).comp
      (Params.linRead (A := Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) (dIn := dIn)
        (dOut := dOut) ℓ))
  have hw : ∀ ℓ (i : hid ℓ) (k : d), AnalyticOnNhd ℝ
      (fun θ : Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut =>
        θ.write ℓ i k) Set.univ := fun ℓ i k =>
    analyticOnNhd_linear ((Matrix.entryLinearMap ℝ ℝ i k).comp
      (Params.linWrite (A := Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) (dIn := dIn)
        (dOut := dOut) ℓ))
  have h2 : ∀ᵐ θ ∂μ, ∀ ℓ (i : hid ℓ), θ.write ℓ i k₁ ≠ 0 :=
    ae_all_iff.2 fun ℓ => ae_all_iff.2 fun i =>
      ae_ne_zero_of_analytic μ (hw ℓ i k₁) ⟨θ₁, one_ne_zero⟩
  have h3 : ∀ᵐ θ ∂μ, ∀ ℓ (j : hid ℓ ⊕ hid ℓ), θ.read ℓ k₁ j ≠ 0 :=
    ae_all_iff.2 fun ℓ => ae_all_iff.2 fun j =>
      ae_ne_zero_of_analytic μ (hr ℓ k₁ j) ⟨θ₁, one_ne_zero⟩
  -- two gate columns, of the same block or of two blocks, are not collinear: a `2 × 2` minor does
  -- not vanish (it is not `0` for the reads cut out of a matrix `E₀ W₀` of `exists_minor_ne_zero`)
  have h4 : ∀ᵐ θ ∂μ, ∀ p q : (Σ ℓ, hid ℓ), p ≠ q →
      θ.read p.1 k₁ (Sum.inl p.2) * θ.read q.1 k₂ (Sum.inl q.2)
        - θ.read q.1 k₁ (Sum.inl q.2) * θ.read p.1 k₂ (Sum.inl p.2) ≠ 0 := by
    refine ae_all_iff.2 fun p => ae_all_iff.2 fun q => ?_
    by_cases hpq : p = q
    · exact Filter.Eventually.of_forall fun _ h _ => absurd hpq h
    · obtain ⟨E₀, W₀, hEW⟩ := exists_minor_ne_zero (q := Σ ℓ, hid ℓ) hk hk hpq
      -- the gate column of unit `p` of the read is column `p` of `E₀ W₀`, the values `0`
      let θ₀ : Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut :=
        ⟨0, fun ℓ => Matrix.of fun k j => Sum.elim (fun i => (E₀ * W₀) k ⟨ℓ, i⟩) (fun _ => 0) j,
          0, 0⟩
      have hg := ((hr p.1 k₁ (Sum.inl p.2)).mul (hr q.1 k₂ (Sum.inl q.2))).sub
        ((hr q.1 k₁ (Sum.inl q.2)).mul (hr p.1 k₂ (Sum.inl p.2)))
      exact (ae_ne_zero_of_analytic μ hg ⟨θ₀, hEW⟩).mono fun _ h _ => h
  filter_upwards [h1, h2, h3, h4] with θ h1 h2 h3 h4
  refine ⟨rank_eq_of_isUnit_det_rows_dgr θ.E ρE (h1.2.2.1 ρE),
    rank_eq_card_of_isUnit_det θ.D cD (h1.2.1 cD), fun ℓ i hi => h2 ℓ i (congrFun hi k₁),
    fun ℓ i hi => h3 ℓ (Sum.inl i) (congrFun hi k₁), ?_,
    fun ℓ i hi => h3 ℓ (Sum.inr i) (congrFun hi k₁)⟩
  -- if `c_p = r c_q`, the minor of the gate columns `p`, `q` vanishes
  intro p q hpq r hr
  have e1 : θ.read p.1 k₁ (Sum.inl p.2) = r * θ.read q.1 k₁ (Sum.inl q.2) := congrFun hr k₁
  have e2 : θ.read p.1 k₂ (Sum.inl p.2) = r * θ.read q.1 k₂ (Sum.inl q.2) := congrFun hr k₂
  apply h4 p q hpq
  rw [e1, e2]
  ring

/-- **Lemma A.27 (Small writes), second value, for gated blocks:** with `d_in, d_out ≥ d ≥ 2` and
blocks of any widths, under pre-RMSNorm with `ε > 0`, for generic parameters `θ` and all small
`τ ≠ 0`, the residual network has `fd(θ_τ) = P - d(d-1)/2 - s`. -/
theorem ae_eventually_funDim_smallWrites_gated_rmsNorm (hε : 0 < ε)
    (hσ : ∀ z, HasDerivAt σ (σ' z) z) (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (hU : GatedUnitsRescale σ σ' d d (Σ ℓ, hid ℓ))
    (μ : Measure (Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, ∀ᶠ τ in 𝓝[≠] (0 : ℝ),
      funDim (Arch.gated σ (rmsNorm ε) hid) 1 (θ.smallWrites τ)
          + (Fintype.card d * (Fintype.card d - 1) / 2 + ∑ ℓ, Fintype.card (hid ℓ))
        = Module.finrank ℝ
            (Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut) := by
  filter_upwards [ae_smallWritesGenericGatedRMS μ hd hdIn hdOut] with θ hθ
  exact eventually_funDim_smallWrites_gated_rmsNorm hε hσ hσa hU θ hθ

/-- **Theorem 4.7 of the skips paper for gated blocks under pre-RMSNorm:** with
`d_in, d_out ≥ d ≥ 2`, `L` blocks of any widths and `ε > 0`, at generic parameters the residual
network has the functional dimension `P - d(d-1)/2 - s`, with `s` the number of hidden units. -/
theorem ae_funDim_gated_residual_rmsNorm (hε : 0 < ε)
    (hσ : ∀ z, HasDerivAt σ (σ' z) z) (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (hU : GatedUnitsRescale σ σ' d d (Σ ℓ, hid ℓ))
    (μ : Measure (Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, funDim (Arch.gated σ (rmsNorm ε) hid) 1 θ
        + (Fintype.card d * (Fintype.card d - 1) / 2 + ∑ ℓ, Fintype.card (hid ℓ))
      = Module.finrank ℝ
          (Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut) := by
  have : Nonempty d := Fintype.card_pos_iff.1 (by omega)
  -- one parameter `θ₀` with the conditions, and one small `τ ≠ 0`: `fd(θ₀_τ) = P - d(d-1)/2 - s`
  obtain ⟨θ₀, hθ₀⟩ := (ae_smallWritesGenericGatedRMS μ hd hdIn hdOut).exists
  obtain ⟨τ, hτ⟩ := (eventually_funDim_smallWrites_gated_rmsNorm hε hσ hσa hU θ₀ hθ₀).exists
  -- at generic `θ`, `fd(θ) ≥ fd(θ₀_τ)` (analytic blocks and `N_ε`), and `fd(θ) ≤ P - d(d-1)/2 - s`
  filter_upwards [ae_funDim_ge (Arch.gated σ (rmsNorm ε) hid) 1
    (fun ℓ => analyticOnNhd_f_gated hσa ℓ) (analyticOnNhd_rmsNorm hε) μ (θ₀.smallWrites τ),
    ae_funDim_add_le_residual_gated_rmsNorm ε μ hdIn] with θ h1 h2
  omega

/-! ### The two kinds of block -/

/-- **Lemma A.27 (Small writes), second value, for SwiGLU blocks under pre-RMSNorm.** -/
theorem ae_eventually_funDim_smallWrites_swiglu_rmsNorm (hε : 0 < ε)
    (μ : Measure (Params (Arch.gated (T := T) (d := d) silu (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, ∀ᶠ τ in 𝓝[≠] (0 : ℝ),
      funDim (Arch.gated silu (rmsNorm ε) hid) 1 (θ.smallWrites τ)
          + (Fintype.card d * (Fintype.card d - 1) / 2 + ∑ ℓ, Fintype.card (hid ℓ))
        = Module.finrank ℝ
            (Params (Arch.gated (T := T) (d := d) silu (rmsNorm ε) hid) dIn dOut) := by
  exact ae_eventually_funDim_smallWrites_gated_rmsNorm hε hasDerivAt_silu analyticOnNhd_silu
    (silu_gatedUnitsRescale _ _ _) μ hd hdIn hdOut

/-- **Lemma A.27 (Small writes), second value, for GeGLU blocks under pre-RMSNorm.** -/
theorem ae_eventually_funDim_smallWrites_geglu_rmsNorm (hε : 0 < ε)
    (μ : Measure (Params (Arch.gated (T := T) (d := d) gelu (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, ∀ᶠ τ in 𝓝[≠] (0 : ℝ),
      funDim (Arch.gated gelu (rmsNorm ε) hid) 1 (θ.smallWrites τ)
          + (Fintype.card d * (Fintype.card d - 1) / 2 + ∑ ℓ, Fintype.card (hid ℓ))
        = Module.finrank ℝ
            (Params (Arch.gated (T := T) (d := d) gelu (rmsNorm ε) hid) dIn dOut) := by
  exact ae_eventually_funDim_smallWrites_gated_rmsNorm hε hasDerivAt_gelu analyticOnNhd_gelu
    (gelu_gatedUnitsRescale _ _ _) μ hd hdIn hdOut

/-- **Theorem 4.7 of the skips paper for SwiGLU blocks under pre-RMSNorm:** with `ε > 0`, at
generic parameters the residual network of `L` blocks has the functional dimension
`P - d(d-1)/2 - s`. -/
theorem ae_funDim_swiglu_residual_rmsNorm (hε : 0 < ε)
    (μ : Measure (Params (Arch.gated (T := T) (d := d) silu (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, funDim (Arch.gated silu (rmsNorm ε) hid) 1 θ
        + (Fintype.card d * (Fintype.card d - 1) / 2 + ∑ ℓ, Fintype.card (hid ℓ))
      = Module.finrank ℝ
          (Params (Arch.gated (T := T) (d := d) silu (rmsNorm ε) hid) dIn dOut) := by
  exact ae_funDim_gated_residual_rmsNorm hε hasDerivAt_silu analyticOnNhd_silu
    (silu_gatedUnitsRescale _ _ _) μ hd hdIn hdOut

/-- **Theorem 4.7 of the skips paper for GeGLU blocks under pre-RMSNorm.** -/
theorem ae_funDim_geglu_residual_rmsNorm (hε : 0 < ε)
    (μ : Measure (Params (Arch.gated (T := T) (d := d) gelu (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, funDim (Arch.gated gelu (rmsNorm ε) hid) 1 θ
        + (Fintype.card d * (Fintype.card d - 1) / 2 + ∑ ℓ, Fintype.card (hid ℓ))
      = Module.finrank ℝ
          (Params (Arch.gated (T := T) (d := d) gelu (rmsNorm ε) hid) dIn dOut) := by
  exact ae_funDim_gated_residual_rmsNorm hε hasDerivAt_gelu analyticOnNhd_gelu
    (gelu_gatedUnitsRescale _ _ _) μ hd hdIn hdOut

end Skips
