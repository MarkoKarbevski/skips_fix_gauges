import SkipsLean.OneBlock.ResidualRMSSteps
import SkipsLean.OneBlock.SwiGLU
import SkipsLean.OneBlock.GeGLU
import SkipsLean.Activations.Analytic

/-!
# One residual SwiGLU or GeGLU block under pre-RMSNorm

Paper (skips paper): Theorem 4.6 (ii), first sentence (Theorem B.1 (ii) in the appendix), for
`ε > 0` and no biases, for gated blocks: SwiGLU and GeGLU. At generic parameters the residual
network of one block has the functional dimension `P - d(d-1)/2 - s`, with `s` the number of
hidden units (one rescaling per hidden unit). The block may have any width.

Steps 1 to 3 of the proof are in `OneBlock/ResidualRMSSteps.lean`. Steps 4 and 5 are as in
`OneBlock/ResidualRMSMlp.lean`, with Lemma B.3 for gated units (`GatedUnitsRescale`, "with `E` and
`D` replaced by the identity and `M = 0`"): it "makes the entries of `η'` at each hidden unit a
rescaling". So the flat directions are those of the orthogonal change of basis and of the
rescalings of the hidden units, a space of dimension `d(d-1)/2 + s`.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {hid : Fin 1 → Type} [∀ ℓ, Fintype (hid ℓ)]
variable {σ σ' : ℝ → ℝ} {ε : ℝ}

/-- **The conditions on `θ` in the proof of Theorem B.1 (ii), for one gated block:** `E` and `D`
have rank `d`, and the hypotheses of Lemma B.3 hold "with `E` and `D` replaced by the identity":
every row of `W_write` and every value column of `W_read` is nonzero, and the gate columns of
`W_read` are nonzero and pairwise non-collinear. -/
structure OneBlockGenericGatedRMS
    (θ : Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut) : Prop where
  rank_E : θ.E.rank = Fintype.card d
  rank_D : θ.D.rank = Fintype.card d
  /-- every row of `W_write` is nonzero -/
  row_ne_zero : ∀ i, θ.write 0 i ≠ 0
  /-- every gate column of `W_read` is nonzero -/
  gate_ne_zero : ∀ i : hid 0, (θ.read 0)ᵀ (Sum.inl i) ≠ 0
  /-- the gate columns of `W_read` are pairwise non-collinear -/
  gate_not_collinear : ∀ i j : hid 0, i ≠ j → ∀ r : ℝ,
    (θ.read 0)ᵀ (Sum.inl i) ≠ r • (θ.read 0)ᵀ (Sum.inl j)
  /-- every value column of `W_read` is nonzero -/
  value_ne_zero : ∀ i : hid 0, (θ.read 0)ᵀ (Sum.inr i) ≠ 0

/-! ### Helpers: the derivative of the block, and its analyticity in the hidden state -/

omit [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (the private `hasDerivAt_affineDG` of `Residual/DepthGated.lean`): `τ ↦ a + τ b` has
the derivative `b` at `0`. -/
private theorem hasDerivAt_affine_rg (a b : ℝ) : HasDerivAt (fun τ : ℝ => a + τ * b) b 0 := by
  have h := ((hasDerivAt_id' (x := (0 : ℝ))).mul_const b).const_add a
  rw [one_mul] at h
  exact h

omit [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (the private `fderiv_f_gated_apply` of `Residual/DepthGated.lean`): the derivative of
the map of the gated block at `M` along `N`: entry `(t, i)` is
`σ'(M_{t, g i}) N_{t, g i} M_{t, v i} + σ(M_{t, g i}) N_{t, v i}`. -/
private theorem fderiv_f_gated_apply_rg (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (M N : Matrix T (hid 0 ⊕ hid 0) ℝ) (t : T) (i : hid 0) :
    fderiv ℝ ((Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid).f 0) M N t i
      = σ' (M t (Sum.inl i)) * N t (Sum.inl i) * M t (Sum.inr i)
        + σ (M t (Sum.inl i)) * N t (Sum.inr i) := by
  have hd := differentiable_f_gated (T := T) (d := d) (χ := rmsNorm ε) (hid := hid)
    (fun z => (hσ z).differentiableAt) 0
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
    have hu := hasDerivAt_affine_rg (M t (Sum.inl i)) (N t (Sum.inl i))
    have hw := hasDerivAt_affine_rg (M t (Sum.inr i)) (N t (Sum.inr i))
    have h := ((hσ _).comp (0 : ℝ) hu).mul hw
    convert h using 1
    · rfl
    · simp only [Function.comp_apply, zero_mul, add_zero]
  exact h2.unique h3

/-- Helper: the derivative of `n ↦ f(n W_read) W_write` along the entries `R'` (of the read) and
`W'` (of the write), entry by entry, at the read `R` and the write `W`:
`∑_i [σ(z_i) w_i W'_{i k} + σ'(z_i) (n R')_{t, g i} w_i W_{i k} + σ(z_i) (n R')_{t, v i} W_{i k}]`
with `z_i = (n R)_{t, g i}` and `w_i = (n R)_{t, v i}` (the order of the terms of Lemma B.3). -/
private noncomputable def gatedDir (σ σ' : ℝ → ℝ) {q : Type*} [Fintype q]
    (R R' : Matrix d (q ⊕ q) ℝ) (W W' : Matrix q d ℝ) (n : Matrix T d ℝ) : Matrix T d ℝ :=
  Matrix.of fun t k => ∑ i : q,
    (σ ((n * R) t (Sum.inl i)) * (n * R) t (Sum.inr i) * W' i k
      + σ' ((n * R) t (Sum.inl i)) * (n * R') t (Sum.inl i) * (n * R) t (Sum.inr i) * W i k
      + σ ((n * R) t (Sum.inl i)) * (n * R') t (Sum.inr i) * W i k)

omit [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the derivative of the block of Steps 1 to 3 is `gatedDir`. -/
private theorem fderiv_add_eq_gatedDir (hσ : ∀ z, HasDerivAt σ (σ' z) z) (n : Matrix T d ℝ)
    (R R' : Matrix d (hid 0 ⊕ hid 0) ℝ) (W W' : Matrix (hid 0) d ℝ) :
    fderiv ℝ ((Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid).f 0) (n * R) (n * R') * W
        + (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid).f 0 (n * R) * W'
      = gatedDir σ σ' R R' W W' n := by
  ext t k
  rw [gatedDir, Matrix.of_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [fderiv_f_gated_apply_rg hσ]
  have hf : (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid).f 0 (n * R) t i
      = σ ((n * R) t (Sum.inl i)) * (n * R) t (Sum.inr i) := rfl
  rw [hf]
  ring

omit [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: an entry of `n R` is a real-analytic (linear) function of `n`. -/
private theorem analyticOnNhd_mul_entry_rg {m : Type*} (R : Matrix d m ℝ) (t : T) (j : m) :
    AnalyticOnNhd ℝ (fun n : Matrix T d ℝ => (n * R) t j) Set.univ := by
  have h : (fun n : Matrix T d ℝ => (n * R) t j) = fun n => ∑ k, n t k * R k j := rfl
  rw [h]
  exact Finset.analyticOnNhd_fun_sum _ fun k _ =>
    (analyticOnNhd_matrix_entry t k).mul analyticOnNhd_const

omit [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (Step 4 (b)): for analytic `σ` and `σ'`, every entry of `gatedDir` is a real-analytic
function of the hidden state `n`. -/
private theorem analyticOnNhd_gatedDir_apply (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (hσ'a : AnalyticOnNhd ℝ σ' Set.univ) {q : Type*} [Fintype q]
    (R R' : Matrix d (q ⊕ q) ℝ) (W W' : Matrix q d ℝ) (t : T) (k : d) :
    AnalyticOnNhd ℝ (fun n : Matrix T d ℝ => gatedDir σ σ' R R' W W' n t k) Set.univ := by
  have hz := fun j => analyticOnNhd_mul_entry_rg (T := T) R t j
  have hz' := fun j => analyticOnNhd_mul_entry_rg (T := T) R' t j
  have hs := fun j => hσa.comp (hz j) (Set.mapsTo_univ _ _)
  have hs' := fun j => hσ'a.comp (hz j) (Set.mapsTo_univ _ _)
  exact Finset.analyticOnNhd_fun_sum _ fun i _ =>
    ((((hs (Sum.inl i)).mul (hz (Sum.inr i))).mul analyticOnNhd_const).add
      ((((hs' (Sum.inl i)).mul (hz' (Sum.inl i))).mul (hz (Sum.inr i))).mul
        analyticOnNhd_const)).add
      (((hs (Sum.inl i)).mul (hz' (Sum.inr i))).mul analyticOnNhd_const)

/-- **Proof of Theorem B.1 (ii), Steps 1 to 4, for one gated block:** under the conditions of the
proof, every flat direction of the residual network under pre-RMSNorm (`ε > 0`) is the sum of
the direction of one antisymmetric `Y` at both hidden states and of the direction of a rescaling
of the values of the hidden units. -/
theorem flat_le_cobDir_const_add_rescaleDir_gated_residual_rmsNorm (hε : 0 < ε)
    (hσ : ∀ z, HasDerivAt σ (σ' z) z) (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (hU : GatedUnitsRescale σ σ' d d (hid 0))
    (θ : Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)
    (hθ : OneBlockGenericGatedRMS θ)
    (η : Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)
    (hη : η ∈ flat (Arch.gated σ (rmsNorm ε) hid) 1 θ) :
    ∃ (Y : Matrix d d ℝ) (α : ∀ ℓ, hid ℓ → ℝ), Yᵀ = -Y ∧
      η = cobDir θ (fun _ => Y) + rescaleDir θ α := by
  -- Steps 1 to 3 (`OneBlock/ResidualRMSSteps.lean`): `Y` antisymmetric, `η_E = E Y`,
  -- `η_D = -Y D`, and the derivative of the block along `η'` vanishes at every `n = N_ε(x E)`
  have hf : ContDiff ℝ 1 ((Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid).f 0) :=
    (analyticOnNhd_f_gated hσa 0).contDiff
  obtain ⟨Y, hY, hYE, hYD, hF⟩ := exists_antisymm_of_flat_residual_rmsNorm
    (A := Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) hε rfl hf θ hθ.rank_E hθ.rank_D η hη
  -- Step 4 (a): `x ↦ x E` is onto (`E` has a left inverse `B`), so this derivative vanishes on
  -- the range of `N_ε`
  obtain ⟨B, hB⟩ := Matrix.vecMul_surjective_iff_exists_left_inverse.mp
    (Matrix.vecMul_surjective_iff_rank_eq_card.mpr hθ.rank_E)
  have hrange : ∀ h : Matrix T d ℝ, gatedDir σ σ' (θ.read 0) (η.read 0 + Y * θ.read 0)
      (θ.write 0) (η.write 0 - θ.write 0 * Y) (rmsNorm ε h) = 0 := by
    intro h
    have hx := hF (h * B)
    have hhB : h * B * θ.E = h := by rw [Matrix.mul_assoc, hB, Matrix.mul_one]
    rw [hhB] at hx
    rw [← fderiv_add_eq_gatedDir hσ]
    exact hx
  -- Step 4 (b): its entries are real-analytic in `n` (`σ' = deriv σ` is analytic) and vanish on
  -- the open nonempty range of `N_ε`, so they vanish everywhere
  have hσ'a : AnalyticOnNhd ℝ σ' Set.univ := by
    have h : σ' = deriv σ := funext fun z => (hσ z).deriv.symm
    rw [h]
    exact hσa.deriv
  have hzero : ∀ n : Matrix T d ℝ, gatedDir σ σ' (θ.read 0) (η.read 0 + Y * θ.read 0)
      (θ.write 0) (η.write 0 - θ.write 0 * Y) n = 0 := by
    intro n
    ext t k
    have hA := analyticOnNhd_gatedDir_apply hσa hσ'a (θ.read 0) (η.read 0 + Y * θ.read 0)
      (θ.write 0) (η.write 0 - θ.write 0 * Y) t k
    have hopen : IsOpen (Set.range (rmsNorm ε : Matrix T d ℝ → Matrix T d ℝ)) :=
      (isOpenMap_rmsNorm hε).isOpen_range
    have hev : (fun n => gatedDir σ σ' (θ.read 0) (η.read 0 + Y * θ.read 0)
        (θ.write 0) (η.write 0 - θ.write 0 * Y) n t k) =ᶠ[nhds (rmsNorm ε 0)] 0 :=
      Filter.eventually_of_mem (hopen.mem_nhds (Set.mem_range_self 0)) fun n hn => by
        obtain ⟨h, rfl⟩ := hn
        simp only [hrange h, Matrix.zero_apply, Pi.zero_apply]
    exact hA.eqOn_zero_of_preconnected_of_eventuallyEq_zero convex_univ.isPreconnected
      (Set.mem_univ _) hev (Set.mem_univ n)
  -- Step 4 (c): Lemma B.3 with `E` and `D` replaced by the identity and `M = 0` (inputs `n` with
  -- all rows equal to `v`): the gate columns of `R'` vanish, and every unit only rescales its
  -- value, `R'_{v i} = -α_i W_{read, v i}`, `W'_i = α_i W_{write, i}`
  obtain ⟨-, -, hc, -, α, hα⟩ := hU
    (fun i => (θ.read 0)ᵀ (Sum.inl i)) 0 (fun i => (θ.read 0)ᵀ (Sum.inr i)) 0
    (fun i => θ.write 0 i) 0 0 (fun i => (η.read 0 + Y * θ.read 0)ᵀ (Sum.inl i)) 0
    (fun i => (η.read 0 + Y * θ.read 0)ᵀ (Sum.inr i)) 0 (fun i => (η.write 0 - θ.write 0 * Y) i)
    (fun i => hθ.row_ne_zero i) (fun i => hθ.gate_ne_zero i)
    (fun i j hij => hθ.gate_not_collinear i j hij) (fun i => hθ.value_ne_zero i) (by
      intro v
      funext k
      have h := congrFun (congrFun (hzero (Matrix.of fun _ => v)) (Classical.arbitrary T)) k
      simp only [Matrix.vecMul_zero, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        Pi.zero_apply, add_zero, zero_add]
      exact h)
  -- Step 4 (d): `η = cobDir θ (Y, Y) + rescaleDir θ α`, component by component (one block)
  let α' : ∀ ℓ : Fin 1, hid ℓ → ℝ := fun ℓ => Fin.cases α (fun l => l.elim0) ℓ
  refine ⟨Y, α', hY, Params.ext' ?_ (fun ℓ => ?_) (fun ℓ => ?_) ?_⟩
  · show η.E = θ.E * Y + 0
    rw [add_zero]
    exact hYE
  · obtain rfl := Subsingleton.elim ℓ 0
    ext k j
    rcases j with i | i
    · have h1 : η.read 0 k (Sum.inl i) + (Y * θ.read 0) k (Sum.inl i) = 0 :=
        congrFun (congrFun hc i) k
      show η.read 0 k (Sum.inl i) = -((Y * θ.read 0) k (Sum.inl i)) + 0
      linarith
    · have h1 : η.read 0 k (Sum.inr i) + (Y * θ.read 0) k (Sum.inr i)
          = -(α i) * θ.read 0 k (Sum.inr i) := congrFun (hα i).1 k
      show η.read 0 k (Sum.inr i)
        = -((Y * θ.read 0) k (Sum.inr i)) + -(α i) * θ.read 0 k (Sum.inr i)
      linarith
  · obtain rfl := Subsingleton.elim ℓ 0
    ext i k
    have h1 : η.write 0 i k - (θ.write 0 * Y) i k = α i * θ.write 0 i k :=
      congrFun (hα i).2.2 k
    show η.write 0 i k = (θ.write 0 * Y) i k + α i * θ.write 0 i k
    linarith
  · show η.D = -(Y * θ.D) + 0
    rw [add_zero]
    exact hYD

/-- Helper (the private `rescaleDirLinG` of `OneBlock/Residual.lean`): `α ↦ rescaleDir θ α` is
linear. -/
private noncomputable def rescaleDirLinRG
    (θ : Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut) :
    (∀ ℓ : Fin 1, hid ℓ → ℝ) →ₗ[ℝ]
      Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut where
  toFun := rescaleDir θ
  map_add' α β := by
    apply Params.ext'
    · exact (add_zero 0).symm
    · intro ℓ
      ext k j
      rcases j with i | i
      · exact (add_zero 0).symm
      · show -((α + β) ℓ i) * θ.read ℓ k (Sum.inr i)
          = -(α ℓ i) * θ.read ℓ k (Sum.inr i) + -(β ℓ i) * θ.read ℓ k (Sum.inr i)
        rw [Pi.add_apply, Pi.add_apply]
        ring
    · intro ℓ
      ext i k
      show (α + β) ℓ i * θ.write ℓ i k = α ℓ i * θ.write ℓ i k + β ℓ i * θ.write ℓ i k
      rw [Pi.add_apply, Pi.add_apply]
      ring
    · exact (add_zero 0).symm
  map_smul' c α := by
    apply Params.ext'
    · exact (smul_zero c).symm
    · intro ℓ
      ext k j
      rcases j with i | i
      · exact (smul_zero c).symm
      · show -((c • α) ℓ i) * θ.read ℓ k (Sum.inr i) = c * (-(α ℓ i) * θ.read ℓ k (Sum.inr i))
        rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul]
        ring
    · intro ℓ
      ext i k
      show (c • α) ℓ i * θ.write ℓ i k = c * (α ℓ i * θ.write ℓ i k)
      rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul]
      ring
    · exact (smul_zero c).symm

/-- **Theorem 4.6 (ii) of the skips paper, first sentence, for one gated block, under the
conditions of its proof:** under pre-RMSNorm with `ε > 0` the residual network has the functional
dimension `P - d(d-1)/2 - d_hidden`. -/
theorem funDim_gated_oneBlock_residual_rmsNorm (hε : 0 < ε)
    (hσ : ∀ z, HasDerivAt σ (σ' z) z) (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (hU : GatedUnitsRescale σ σ' d d (hid 0))
    (θ : Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)
    (hθ : OneBlockGenericGatedRMS θ) :
    funDim (Arch.gated σ (rmsNorm ε) hid) 1 θ
        + (Fintype.card d * (Fintype.card d - 1) / 2 + Fintype.card (hid 0))
      = Module.finrank ℝ
          (Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut) := by
  have hσd : Differentiable ℝ σ := fun z => (hσ z).differentiableAt
  have hdiff : ∀ x : Matrix T dIn ℝ, DifferentiableAt ℝ
      (fun θ' : Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut =>
        eval (Arch.gated σ (rmsNorm ε) hid) 1 θ' x) θ := fun x =>
    (differentiable_eval (A := Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) (S := 1)
      (differentiable_f_gated hσd) (differentiable_rmsNorm hε) x).differentiableAt
  -- Step 5: the directions of one orthogonal change of basis and of the rescalings,
  -- `(Y, α) ↦ cobDir θ (Y, Y) + rescaleDir θ α` with `Y` antisymmetric
  let Φ : (antisymmetric d × (∀ ℓ : Fin 1, hid ℓ → ℝ)) →ₗ[ℝ]
      Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut :=
    ((cobDirLin θ).comp (LinearMap.pi fun _ => (antisymmetric d).subtype)).coprod
      (rescaleDirLinRG θ)
  -- every flat direction is one of them (Steps 1 to 4)
  have hle : flat (Arch.gated σ (rmsNorm ε) hid) 1 θ ≤ LinearMap.range Φ := by
    intro η hη
    obtain ⟨Y, α, hY, rfl⟩ :=
      flat_le_cobDir_const_add_rescaleDir_gated_residual_rmsNorm hε hσ hσa hU θ hθ η hη
    exact LinearMap.mem_range.2 ⟨(⟨Y, hY⟩, α), rfl⟩
  -- the domain has dimension `d(d-1)/2 + d_hidden`
  have hdim : Module.finrank ℝ (antisymmetric d × (∀ ℓ : Fin 1, hid ℓ → ℝ))
      = Fintype.card d * (Fintype.card d - 1) / 2 + Fintype.card (hid 0) := by
    rw [Module.finrank_prod, finrank_antisymmetric, Module.finrank_pi_fintype]
    simp only [Module.finrank_fintype_fun_eq_card, Finset.univ_unique, Fin.default_eq_zero,
      Finset.sum_singleton]
  -- `≥`: `fd(θ) = P - dim K(θ)` (Appendix C) and `dim K(θ) ≤ d(d-1)/2 + d_hidden`
  have h1 := funDim_add_finrank_flat θ hdiff
  have h2 := (Submodule.finrank_mono hle).trans (LinearMap.finrank_range_le Φ)
  rw [hdim] at h2
  -- `≤`: these directions are flat and independent (Theorem 4.2 with identity skips)
  have hv : ∀ ℓ i, (fun a => θ.read ℓ a (Sum.inr i)) ≠ 0 := by
    intro ℓ i
    obtain rfl := Subsingleton.elim ℓ 0
    exact hθ.value_ne_zero i
  have h3 := funDim_add_le_residual_gated_rmsNorm ε θ hθ.rank_E hv
  rw [Fin.sum_univ_one] at h3
  omega

omit [Fintype T] [Nonempty T] [Fintype dIn] [Fintype dOut] in
/-- Helper (the private `rank_eq_of_isUnit_det_submatrix` of `Generic/Params.lean`): a matrix
with `d` columns has rank `d` if some `d` of its rows form an invertible matrix. -/
private theorem rank_eq_of_isUnit_det_rows_rg {m : Type*} (M : Matrix m d ℝ) (ρ : d ↪ m)
    (h : IsUnit (M.submatrix ρ id).det) : M.rank = Fintype.card d :=
  le_antisymm (Matrix.rank_le_card_width M)
    ((Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).2 h)).symm.le.trans
      (Matrix.rank_submatrix_le M ρ id))

/-- The conditions of the proof hold at generic parameters, for `d_in, d_out ≥ d ≥ 2` and a block
of any width. -/
theorem ae_oneBlockGenericGatedRMS
    (μ : Measure (Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, OneBlockGenericGatedRMS θ := by
  classical
  -- two distinct coordinates `k₁ ≠ k₂` of the hidden states, `d` rows of `E`, `d` columns of `D`
  obtain ⟨k₁, k₂, hk⟩ := Fintype.exists_pair_of_one_lt_card (show 1 < Fintype.card d by omega)
  obtain ⟨ρE⟩ := Function.Embedding.nonempty_of_card_le hdIn
  obtain ⟨cD⟩ := Function.Embedding.nonempty_of_card_le hdOut
  -- the ranks of `E` and `D`: invertible `d × d` minors (`Generic/Params.lean`)
  have h1 := ae_isUnit_det_submatrix μ
  -- an entry of the write or of the read is a linear functional of the parameters, not zero at
  -- the parameters with all entries `1`
  let θ₁ : Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut :=
    ⟨Matrix.of fun _ _ => 1, fun _ => Matrix.of fun _ _ => 1, fun _ => Matrix.of fun _ _ => 1,
      Matrix.of fun _ _ => 1⟩
  have hr : ∀ (k : d) (j : hid 0 ⊕ hid 0), AnalyticOnNhd ℝ
      (fun θ : Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut =>
        θ.read 0 k j) Set.univ := fun k j =>
    analyticOnNhd_linear ((Matrix.entryLinearMap ℝ ℝ k j).comp
      (Params.linRead (A := Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) (dIn := dIn)
        (dOut := dOut) 0))
  have hw : ∀ (i : hid 0) (k : d), AnalyticOnNhd ℝ
      (fun θ : Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut =>
        θ.write 0 i k) Set.univ := fun i k =>
    analyticOnNhd_linear ((Matrix.entryLinearMap ℝ ℝ i k).comp
      (Params.linWrite (A := Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) (dIn := dIn)
        (dOut := dOut) 0))
  have h2 : ∀ᵐ θ ∂μ, ∀ i : hid 0, θ.write 0 i k₁ ≠ 0 :=
    ae_all_iff.2 fun i => ae_ne_zero_of_analytic μ (hw i k₁) ⟨θ₁, one_ne_zero⟩
  have h3 : ∀ᵐ θ ∂μ, ∀ j : hid 0 ⊕ hid 0, θ.read 0 k₁ j ≠ 0 :=
    ae_all_iff.2 fun j => ae_ne_zero_of_analytic μ (hr k₁ j) ⟨θ₁, one_ne_zero⟩
  -- two gate columns of the read are not collinear: a `2 × 2` minor does not vanish (it is `1`
  -- for a read `E₀ W₀` of `exists_minor_ne_zero`)
  have h4 : ∀ᵐ θ ∂μ, ∀ i j : hid 0, i ≠ j →
      θ.read 0 k₁ (Sum.inl i) * θ.read 0 k₂ (Sum.inl j)
        - θ.read 0 k₁ (Sum.inl j) * θ.read 0 k₂ (Sum.inl i) ≠ 0 := by
    refine ae_all_iff.2 fun i => ae_all_iff.2 fun j => ?_
    by_cases hij : i = j
    · exact Filter.Eventually.of_forall fun _ h _ => absurd hij h
    · obtain ⟨E₀, W₀, hEW⟩ := exists_minor_ne_zero (q := hid 0 ⊕ hid 0) hk hk
        (Sum.inl_injective.ne hij)
      let θ₀ : Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut :=
        ⟨0, fun ℓ => Fin.cases (E₀ * W₀) (fun l => l.elim0) ℓ, 0, 0⟩
      have hg := ((hr k₁ (Sum.inl i)).mul (hr k₂ (Sum.inl j))).sub
        ((hr k₁ (Sum.inl j)).mul (hr k₂ (Sum.inl i)))
      exact (ae_ne_zero_of_analytic μ hg ⟨θ₀, hEW⟩).mono fun _ h _ => h
  filter_upwards [h1, h2, h3, h4] with θ h1 h2 h3 h4
  refine ⟨rank_eq_of_isUnit_det_rows_rg θ.E ρE (h1.2.2.1 ρE),
    rank_eq_card_of_isUnit_det θ.D cD (h1.2.1 cD), fun i hi => h2 i (congrFun hi k₁),
    fun i hi => h3 (Sum.inl i) (congrFun hi k₁), ?_, fun i hi => h3 (Sum.inr i) (congrFun hi k₁)⟩
  -- if `c_i = r c_j`, the minor of the gate columns `i`, `j` vanishes
  intro i j hij r hr
  have e1 : θ.read 0 k₁ (Sum.inl i) = r * θ.read 0 k₁ (Sum.inl j) := congrFun hr k₁
  have e2 : θ.read 0 k₂ (Sum.inl i) = r * θ.read 0 k₂ (Sum.inl j) := congrFun hr k₂
  apply h4 i j hij
  rw [e1, e2]
  ring

/-- **Theorem 4.6 (ii) of the skips paper, first sentence, for one gated block:** with
`d_in, d_out ≥ d ≥ 2` and a block of any width, under pre-RMSNorm with `ε > 0`, at generic
parameters the residual network has the functional dimension `P - d(d-1)/2 - d_hidden`. -/
theorem ae_funDim_gated_oneBlock_residual_rmsNorm (hε : 0 < ε)
    (hσ : ∀ z, HasDerivAt σ (σ' z) z) (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (hU : GatedUnitsRescale σ σ' d d (hid 0))
    (μ : Measure (Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, funDim (Arch.gated σ (rmsNorm ε) hid) 1 θ
        + (Fintype.card d * (Fintype.card d - 1) / 2 + Fintype.card (hid 0))
      = Module.finrank ℝ
          (Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut) := by
  filter_upwards [ae_oneBlockGenericGatedRMS μ hd hdIn hdOut] with θ hθ
  exact funDim_gated_oneBlock_residual_rmsNorm hε hσ hσa hU θ hθ

/-! ### The two kinds of block -/

/-- **Theorem 4.6 (ii) of the skips paper, first sentence, for a SwiGLU block:** under pre-RMSNorm
with `ε > 0`, at generic parameters the residual network of one block has the functional
dimension `P - d(d-1)/2 - d_hidden`. -/
theorem ae_funDim_swiglu_oneBlock_residual_rmsNorm (hε : 0 < ε)
    (μ : Measure (Params (Arch.gated (T := T) (d := d) silu (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, funDim (Arch.gated silu (rmsNorm ε) hid) 1 θ
        + (Fintype.card d * (Fintype.card d - 1) / 2 + Fintype.card (hid 0))
      = Module.finrank ℝ
          (Params (Arch.gated (T := T) (d := d) silu (rmsNorm ε) hid) dIn dOut) := by
  exact ae_funDim_gated_oneBlock_residual_rmsNorm hε hasDerivAt_silu analyticOnNhd_silu
      (silu_gatedUnitsRescale _ _ _) μ hd hdIn hdOut

/-- **Theorem 4.6 (ii) of the skips paper, first sentence, for a GeGLU block.** -/
theorem ae_funDim_geglu_oneBlock_residual_rmsNorm (hε : 0 < ε)
    (μ : Measure (Params (Arch.gated (T := T) (d := d) gelu (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, funDim (Arch.gated gelu (rmsNorm ε) hid) 1 θ
        + (Fintype.card d * (Fintype.card d - 1) / 2 + Fintype.card (hid 0))
      = Module.finrank ℝ
          (Params (Arch.gated (T := T) (d := d) gelu (rmsNorm ε) hid) dIn dOut) := by
  exact ae_funDim_gated_oneBlock_residual_rmsNorm hε hasDerivAt_gelu analyticOnNhd_gelu
      (gelu_gatedUnitsRescale _ _ _) μ hd hdIn hdOut

end Skips
