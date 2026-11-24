import SkipsLean.Residual.SmallWrites
import SkipsLean.Residual.UpperBoundSymmetries
import SkipsLean.OneBlock.SwiGLU
import SkipsLean.OneBlock.GeGLU
import SkipsLean.Activations.Analytic

/-!
# Residual networks of SwiGLU and GeGLU blocks at any depth

Paper (skips paper): Lemma A.27 (Small writes), its first value `fd(θ_τ) = P - d² - s`, and
Theorem 4.7 (Equality for residual networks at any depth), both without normalization and without
biases, for gated blocks: SwiGLU and GeGLU. Here `s` is the number of hidden units of all blocks
(one rescaling per hidden unit). The blocks may have any widths.

As in `Residual/DepthMlp.lean`, with Lemma B.3 for gated units (`GatedUnitsRescale`) applied to the
hidden units of all blocks together: "the read of a unit has a gate and a value", and a direction
`η` that is flat for the limit `J_0` has `η_E = E X`, `η_D = -X D`, no component at the gates, and
rescales every hidden unit: its value column is multiplied by `-α_{ℓ,i}` and its row of the write
by `α_{ℓ,i}`. These directions form a space of dimension `d² + s`.
-/

namespace Skips

open Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d]
  [Fintype dIn] [Fintype dOut]
variable {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]
variable {σ σ' : ℝ → ℝ}

/-- **The conditions on `θ` in Lemma A.27, for gated blocks without normalization:** `E` and `D`
have rank `d`, and the hypotheses of Lemma B.3 hold for the units of all blocks together: with
`c_{ℓ,i}` the gate columns and `e_{ℓ,i}` the value columns of `E W_read^ℓ`, and `a_{ℓ,i}` the rows
of `W_write^ℓ D`, every `a_{ℓ,i}` and every `e_{ℓ,i}` is nonzero, and the `c_{ℓ,i}`, over all blocks
`ℓ` and hidden units `i`, are nonzero and pairwise non-collinear. -/
structure SmallWritesGenericGated
    (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) : Prop where
  rank_E : θ.E.rank = Fintype.card d
  rank_D : θ.D.rank = Fintype.card d
  /-- every row `a_{ℓ,i}` of `W_write^ℓ D` is nonzero -/
  row_ne_zero : ∀ ℓ i, (θ.write ℓ * θ.D) i ≠ 0
  /-- every gate column `c_{ℓ,i}` of `E W_read^ℓ` is nonzero -/
  gate_ne_zero : ∀ ℓ (i : hid ℓ), (θ.E * θ.read ℓ)ᵀ (Sum.inl i) ≠ 0
  /-- the gate columns of all blocks together are pairwise non-collinear -/
  gate_not_collinear : ∀ p q : (Σ ℓ, hid ℓ), p ≠ q → ∀ r : ℝ,
    (θ.E * θ.read p.1)ᵀ (Sum.inl p.2) ≠ r • (θ.E * θ.read q.1)ᵀ (Sum.inl q.2)
  /-- every value column `e_{ℓ,i}` of `E W_read^ℓ` is nonzero -/
  value_ne_zero : ∀ ℓ (i : hid ℓ), (θ.E * θ.read ℓ)ᵀ (Sum.inr i) ≠ 0

/-! ### Helpers: linear algebra -/

/-- Helper (the private `cancel_left_of_rank_res` of `OneBlock/Residual.lean`): a matrix whose rank
is its number of columns cancels on the left, via a left inverse. -/
private theorem cancel_left_of_rank_dg {m n k : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (M : Matrix m n ℝ) (hM : M.rank = Fintype.card n) {X Y : Matrix n k ℝ}
    (h : M * X = M * Y) : X = Y := by
  obtain ⟨B, hB⟩ := Matrix.vecMul_surjective_iff_exists_left_inverse.mp
    (Matrix.vecMul_surjective_iff_rank_eq_card.mpr hM)
  have := congrArg (B * ·) h
  simpa only [← Matrix.mul_assoc, hB, Matrix.one_mul] using this

/-- Helper (the private `cancel_right_of_rank_res` of `OneBlock/Residual.lean`): a matrix whose
rank is its number of rows cancels on the right, via a right inverse. -/
private theorem cancel_right_of_rank_dg {m n k : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    (M : Matrix m n ℝ) (hM : M.rank = Fintype.card m) {X Y : Matrix k m ℝ}
    (h : X * M = Y * M) : X = Y := by
  obtain ⟨R, hR⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.mp
    (Matrix.mulVec_surjective_iff_rank_eq_card.mpr hM)
  have := congrArg (· * R) h
  simpa only [Matrix.mul_assoc, hR, Matrix.mul_one] using this

omit [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (the private `hasDerivAt_lineG` of `Depth/BlockIdentityGated.lean`): the line
`τ ↦ a + τ b` has the velocity `b`. -/
private theorem hasDerivAt_lineDG {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (a b : E) :
    HasDerivAt (fun τ : ℝ => a + τ • b) b 0 := by
  have h := ((hasDerivAt_id (0 : ℝ)).smul_const b).const_add a
  rw [one_smul] at h
  exact h

omit [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: `τ ↦ a + τ b` has the derivative `b` at `0`, in `ℝ`. -/
private theorem hasDerivAt_affineDG (a b : ℝ) : HasDerivAt (fun τ : ℝ => a + τ * b) b 0 := by
  have h := ((hasDerivAt_id' (x := (0 : ℝ))).mul_const b).const_add a
  rw [one_mul] at h
  exact h

omit [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the derivative of the map of a gated block at `M` along `N`: entry `(t, i)` is
`σ'(M_{t, g i}) N_{t, g i} M_{t, v i} + σ(M_{t, g i}) N_{t, v i}`. -/
private theorem fderiv_f_gated_apply (hσ : ∀ z, HasDerivAt σ (σ' z) z) (ℓ : Fin L)
    (M N : Matrix T (hid ℓ ⊕ hid ℓ) ℝ) (t : T) (i : hid ℓ) :
    fderiv ℝ ((Arch.gated (T := T) (d := d) σ id hid).f ℓ) M N t i
      = σ' (M t (Sum.inl i)) * N t (Sum.inl i) * M t (Sum.inr i)
        + σ (M t (Sum.inl i)) * N t (Sum.inr i) := by
  have hd := differentiable_f_gated (T := T) (d := d) (χ := id) (hid := hid)
    (fun z => (hσ z).differentiableAt) ℓ
  -- the chain rule along the line `τ ↦ M + τ N`
  have h1 := (hd M).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) (hasDerivAt_lineDG M N)
    (by rw [zero_smul, add_zero])
  have h2 := hasDerivAt_pi.1 (hasDerivAt_pi.1 h1 t) i
  -- the same derivative computed on the entry `(t, i)`
  have h3 : HasDerivAt (fun τ : ℝ => σ (M t (Sum.inl i) + τ * N t (Sum.inl i))
      * (M t (Sum.inr i) + τ * N t (Sum.inr i)))
      (σ' (M t (Sum.inl i)) * N t (Sum.inl i) * M t (Sum.inr i)
        + σ (M t (Sum.inl i)) * N t (Sum.inr i)) 0 := by
    have hu := hasDerivAt_affineDG (M t (Sum.inl i)) (N t (Sum.inl i))
    have hw := hasDerivAt_affineDG (M t (Sum.inr i)) (N t (Sum.inr i))
    have h := ((hσ _).comp (0 : ℝ) hu).mul hw
    convert h using 1
    · rfl
    · simp only [Function.comp_apply, zero_mul, add_zero]
  exact h2.unique h3

omit [Nonempty T] [DecidableEq d] [Fintype dOut] in
/-- Helper: the entries of `(J_0 η)(x)` for gated blocks:
`(x ψ_M)_{t o} + ∑_ℓ ∑_i [σ(z) w (ψ_A)_{i o} + σ'(z) (x ψ_C)_{t, g i} w A_{i o}
+ σ(z) (x ψ_C)_{t, v i} A_{i o}]`, with `z = (x C)_{t, g i}`, `w = (x C)_{t, v i}`. -/
private theorem smallWritesLimit_gated_apply (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (θ η : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) (x : Matrix T dIn ℝ)
    (t : T) (o : dOut) :
    smallWritesLimit (Arch.gated σ id hid) θ η x t o
      = (x * (η.E * θ.D + θ.E * η.D)) t o + ∑ ℓ, ∑ i : hid ℓ,
        (σ ((x * (θ.E * θ.read ℓ)) t (Sum.inl i)) * (x * (θ.E * θ.read ℓ)) t (Sum.inr i)
            * (η.write ℓ * θ.D) i o
          + σ' ((x * (θ.E * θ.read ℓ)) t (Sum.inl i)) * (x * (θ.E * η.read ℓ)) t (Sum.inl i)
            * (x * (θ.E * θ.read ℓ)) t (Sum.inr i) * (θ.write ℓ * θ.D) i o
          + σ ((x * (θ.E * θ.read ℓ)) t (Sum.inl i)) * (x * (θ.E * η.read ℓ)) t (Sum.inr i)
            * (θ.write ℓ * θ.D) i o) := by
  unfold smallWritesLimit
  rw [Matrix.add_apply, Matrix.sum_apply]
  congr 1
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc _ (η.write ℓ), Matrix.add_apply,
    Matrix.mul_apply, Matrix.mul_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [fderiv_f_gated_apply hσ, Matrix.mul_assoc x θ.E (θ.read ℓ),
    Matrix.mul_assoc x θ.E (η.read ℓ)]
  have hf : (Arch.gated (T := T) (d := d) σ id hid).f ℓ (x * (θ.E * θ.read ℓ)) t i
      = σ ((x * (θ.E * θ.read ℓ)) t (Sum.inl i)) * (x * (θ.E * θ.read ℓ)) t (Sum.inr i) := rfl
  rw [hf]
  ring

/-- **Proof of Lemma A.27, gated blocks without normalization, the flat directions of `J_0`:**
under the conditions of the lemma, a direction `η` with `(J_0 η)(x) = 0` at every input `x` has
`η_E = E X` and `η_D = -X D` for one matrix `X`, vanishes at every gate column of a read, and
rescales every hidden unit: for numbers `α_{ℓ,i}`, the value column of unit `i` of block `ℓ` in
`η_read^ℓ` is `-α_{ℓ,i}` times that of `W_read^ℓ`, and its row in `η_write^ℓ` is `α_{ℓ,i}` times that
of `W_write^ℓ`. Stated for every gate that satisfies the conclusion of Lemma B.3
(`GatedUnitsRescale`) for the hidden units of all blocks together. -/
theorem smallWritesLimit_eq_zero_gated (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hU : GatedUnitsRescale σ σ' dIn dOut (Σ ℓ, hid ℓ))
    (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (hθ : SmallWritesGenericGated θ)
    (η : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (hη : ∀ x, smallWritesLimit (Arch.gated σ id hid) θ η x = 0) :
    ∃ (X : Matrix d d ℝ) (α : ∀ ℓ, hid ℓ → ℝ), η.E = θ.E * X ∧ η.D = -(X * θ.D)
      ∧ (∀ ℓ (i : hid ℓ) a, η.read ℓ a (Sum.inl i) = 0)
      ∧ (∀ ℓ (i : hid ℓ) a, η.read ℓ a (Sum.inr i) = -(α ℓ i) * θ.read ℓ a (Sum.inr i))
      ∧ (∀ ℓ (i : hid ℓ) a, η.write ℓ i a = α ℓ i * θ.write ℓ i a) := by
  -- Lemma B.3 for the hidden units of all blocks together, on the inputs `x` whose rows all equal
  -- `v`: `ψ_M = 0`, the gate columns of `ψ_C` vanish, and every unit only rescales its value
  obtain ⟨hm, -, hc, -, α, hα⟩ := hU
    (fun p => (θ.E * θ.read p.1)ᵀ (Sum.inl p.2)) 0 (fun p => (θ.E * θ.read p.1)ᵀ (Sum.inr p.2)) 0
    (fun p => (θ.write p.1 * θ.D) p.2)
    (η.E * θ.D + θ.E * η.D) 0 (fun p => (θ.E * η.read p.1)ᵀ (Sum.inl p.2)) 0
    (fun p => (θ.E * η.read p.1)ᵀ (Sum.inr p.2)) 0 (fun p => (η.write p.1 * θ.D) p.2)
    (fun p => hθ.row_ne_zero p.1 p.2) (fun p => hθ.gate_ne_zero p.1 p.2)
    (fun p q hpq => hθ.gate_not_collinear p q hpq) (fun p => hθ.value_ne_zero p.1 p.2) (by
      intro v
      funext o
      have h := hη (Matrix.of fun _ => v)
      have h' := congrFun (congrFun h (Classical.arbitrary T)) o
      rw [smallWritesLimit_gated_apply hσ] at h'
      simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
        add_zero]
      rw [Fintype.sum_sigma]
      exact h')
  -- the reads: `E η_read^ℓ = E R'_ℓ` with `R'_ℓ` the rescaled value columns, and `E` cancels
  have hread : ∀ ℓ, η.read ℓ = Matrix.of fun k j =>
      Sum.elim (fun _ => 0) (fun i => -(α ⟨ℓ, i⟩) * θ.read ℓ k (Sum.inr i)) j := by
    intro ℓ
    apply cancel_left_of_rank_dg θ.E hθ.rank_E
    ext a j
    rcases j with i | i
    · have h1 : (θ.E * η.read ℓ) a (Sum.inl i) = 0 := congrFun (congrFun hc ⟨ℓ, i⟩) a
      rw [h1, Matrix.mul_apply]
      exact (Finset.sum_eq_zero fun k _ => mul_zero (θ.E a k)).symm
    · have h1 : (θ.E * η.read ℓ) a (Sum.inr i)
          = -(α ⟨ℓ, i⟩) * (θ.E * θ.read ℓ) a (Sum.inr i) := congrFun (hα ⟨ℓ, i⟩).1 a
      rw [h1, Matrix.mul_apply, Matrix.mul_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      show _ = θ.E a k * (-(α ⟨ℓ, i⟩) * θ.read ℓ k (Sum.inr i))
      ring
  -- the writes: `η_write^ℓ D = W'_ℓ D` with `W'_ℓ` the rescaled rows, and `D` cancels
  have hwrite : ∀ ℓ, η.write ℓ = Matrix.of fun i k => α ⟨ℓ, i⟩ * θ.write ℓ i k := by
    intro ℓ
    apply cancel_right_of_rank_dg θ.D hθ.rank_D
    ext i o
    have h1 : (η.write ℓ * θ.D) i o = α ⟨ℓ, i⟩ * (θ.write ℓ * θ.D) i o :=
      congrFun (hα ⟨ℓ, i⟩).2.2 o
    rw [h1, Matrix.mul_apply, Matrix.mul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    show _ = α ⟨ℓ, i⟩ * θ.write ℓ i k * θ.D k o
    ring
  -- `η_E D + E η_D = 0`: with a right inverse `R` of `D` and `X = -η_D R`, `η_E = E X`, and then
  -- `E η_D = -E X D`, so `η_D = -X D`
  obtain ⟨R, hR⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.mp
    (Matrix.mulVec_surjective_iff_rank_eq_card.mpr hθ.rank_D)
  have hE : η.E = θ.E * -(η.D * R) := by
    have h := congrArg (· * R) hm
    simp only [Matrix.add_mul, Matrix.mul_assoc, hR, Matrix.mul_one, Matrix.zero_mul] at h
    rw [Matrix.mul_neg]
    exact eq_neg_of_add_eq_zero_left h
  have hD : η.D = -(-(η.D * R) * θ.D) := by
    apply cancel_left_of_rank_dg θ.E hθ.rank_E
    rw [Matrix.mul_neg, ← Matrix.mul_assoc, ← hE]
    exact eq_neg_of_add_eq_zero_right hm
  refine ⟨-(η.D * R), fun ℓ i => α ⟨ℓ, i⟩, hE, hD, fun ℓ i a => ?_, fun ℓ i a => ?_,
    fun ℓ i a => ?_⟩
  · rw [hread ℓ]
    rfl
  · rw [hread ℓ]
    rfl
  · rw [hwrite ℓ]
    rfl

/-- Helper: the flat directions of `J_0` found in `smallWritesLimit_eq_zero_gated`,
`(X, α) ↦ (E X, the reads with gate columns `0` and value columns `-α_{ℓ,i}` times those of
`W_read^ℓ`, the writes with rows `α_{ℓ,i}` times those of `W_write^ℓ`, -X D)`, as a linear map. -/
private noncomputable def limitFlatLin
    (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) :
    (Matrix d d ℝ × (∀ ℓ, hid ℓ → ℝ)) →ₗ[ℝ]
      Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut where
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

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the pairs `(X, α)` of a `d × d` matrix and one number per hidden unit form a space of
dimension `d² + s`. -/
private theorem finrank_limitFlatDomain :
    Module.finrank ℝ (Matrix d d ℝ × (∀ ℓ, hid ℓ → ℝ))
      = Fintype.card d ^ 2 + ∑ ℓ, Fintype.card (hid ℓ) := by
  rw [Module.finrank_prod, Module.finrank_matrix, Module.finrank_self, mul_one, ← sq,
    Module.finrank_pi_fintype]
  simp only [Module.finrank_fintype_fun_eq_card]

/-- **Lemma A.27 (Small writes), first value, for gated blocks, under the conditions of its
proof:** for all small `τ ≠ 0` the residual network has `fd(θ_τ) = P - d² - s`, with `s` the number
of hidden units. -/
theorem eventually_funDim_smallWrites_gated (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hσa : AnalyticOnNhd ℝ σ Set.univ) (hU : GatedUnitsRescale σ σ' dIn dOut (Σ ℓ, hid ℓ))
    (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (hθ : SmallWritesGenericGated θ) :
    ∀ᶠ τ in 𝓝[≠] (0 : ℝ),
      funDim (Arch.gated σ id hid) 1 (θ.smallWrites τ)
          + (Fintype.card d ^ 2 + ∑ ℓ, Fintype.card (hid ℓ))
        = Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) := by
  -- `≥`: every flat direction of `J_0` lies in the range `V` of `limitFlatLin θ` (step 1), of
  -- dimension at most `d² + s`
  have hV : ∀ η, (∀ x, smallWritesLimit (Arch.gated σ id hid) θ η x = 0) →
      η ∈ LinearMap.range (limitFlatLin θ) := by
    intro η hη
    obtain ⟨X, α, hE, hD, hg, hv, hw⟩ := smallWritesLimit_eq_zero_gated hσ hU θ hθ η hη
    refine LinearMap.mem_range.2 ⟨(X, α), ?_⟩
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
  have hdim : Module.finrank ℝ (LinearMap.range (limitFlatLin θ))
      ≤ Fintype.card d ^ 2 + ∑ ℓ, Fintype.card (hid ℓ) :=
    (LinearMap.finrank_range_le _).trans finrank_limitFlatDomain.le
  have hge := eventually_funDim_smallWrites_ge (Arch.gated σ id hid) θ rfl
    (fun ℓ => analyticOnNhd_f_gated hσa ℓ) _ hV
  -- `≤`: at every `τ` the network has the symmetries of the one change of basis and of the
  -- rescalings; `E` and the reads of `θ_τ` are those of `θ`, and no value column of a read
  -- vanishes since no value column of `E W_read^ℓ` does
  have hv : ∀ ℓ i, (fun a => θ.read ℓ a (Sum.inr i)) ≠ 0 := by
    intro ℓ i h0
    apply hθ.value_ne_zero ℓ i
    funext a
    show ∑ k, θ.E a k * θ.read ℓ k (Sum.inr i) = 0
    exact Finset.sum_eq_zero fun k _ => by
      rw [show θ.read ℓ k (Sum.inr i) = 0 from congrFun h0 k, mul_zero]
  filter_upwards [hge] with τ hτ
  have hle := funDim_add_le_residual_gated (θ.smallWrites τ) hθ.rank_E hv
  omega

omit [Fintype T] [Nonempty T] in
/-- Helper (the private `rank_eq_of_isUnit_det_submatrix` of `Generic/Params.lean`): a matrix
with `d` columns has rank `d` if some `d` of its rows form an invertible matrix. -/
private theorem rank_eq_of_isUnit_det_submatrix_dg {m : Type*} (M : Matrix m d ℝ) (ρ : d ↪ m)
    (h : IsUnit (M.submatrix ρ id).det) : M.rank = Fintype.card d :=
  le_antisymm (Matrix.rank_le_card_width M)
    ((Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).2 h)).symm.le.trans
      (Matrix.rank_submatrix_le M ρ id))

/-- The conditions of Lemma A.27 for gated blocks hold at generic parameters, for
`d_in, d_out ≥ d ≥ 2` and blocks of any widths. -/
theorem ae_smallWritesGenericGated
    (μ : Measure (Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)) [μ.IsAddHaarMeasure]
    (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, SmallWritesGenericGated θ := by
  classical
  -- two distinct coordinates of `h`, two distinct input coordinates, one output coordinate
  obtain ⟨k₁, k₂, hk⟩ := Fintype.exists_pair_of_one_lt_card (show 1 < Fintype.card d by omega)
  obtain ⟨a₁, a₂, ha⟩ := Fintype.exists_pair_of_one_lt_card (show 1 < Fintype.card dIn by omega)
  obtain ⟨o₀⟩ : Nonempty dOut := Fintype.card_pos_iff.1 (by omega)
  obtain ⟨ρE⟩ := Function.Embedding.nonempty_of_card_le hdIn
  obtain ⟨cD⟩ := Function.Embedding.nonempty_of_card_le hdOut
  -- the parameters with all entries `1`
  let θ₁ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut :=
    ⟨Matrix.of fun _ _ => 1, fun _ => Matrix.of fun _ _ => 1, fun _ => Matrix.of fun _ _ => 1,
      Matrix.of fun _ _ => 1⟩
  -- the ranks of `E` and `D`: invertible `d × d` minors
  have h2 := ae_isUnit_det_submatrix μ
  -- the rows of `W_write^ℓ D` are nonzero: their entries at `o₀` are
  have h3 : ∀ᵐ θ ∂μ, ∀ ℓ (i : hid ℓ), (θ.write ℓ * θ.D) i o₀ ≠ 0 := by
    refine ae_all_iff.2 fun ℓ => ae_all_iff.2 fun i => ?_
    exact ae_ne_zero_of_analytic μ
      (analyticOnNhd_write_mul_D (A := Arch.gated (T := T) (d := d) σ id hid) (dIn := dIn) ℓ i o₀)
      ⟨θ₁, sum_one_mul_one_ne_zero hd⟩
  -- the gate and value columns of `E W_read^ℓ` are nonzero: their entries at `a₁` are
  have h4 : ∀ᵐ θ ∂μ, ∀ ℓ (j : hid ℓ ⊕ hid ℓ), (θ.E * θ.read ℓ) a₁ j ≠ 0 := by
    refine ae_all_iff.2 fun ℓ => ae_all_iff.2 fun j => ?_
    exact ae_ne_zero_of_analytic μ
      (analyticOnNhd_E_mul_read (A := Arch.gated (T := T) (d := d) σ id hid) (dOut := dOut) ℓ a₁ j)
      ⟨θ₁, sum_one_mul_one_ne_zero hd⟩
  -- two gate columns, of the same block or of two blocks, are not collinear: a `2 × 2` minor does
  -- not vanish
  have hC : ∀ ℓ (a : dIn) (j : hid ℓ ⊕ hid ℓ), AnalyticOnNhd ℝ
      (fun θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut =>
        (θ.E * θ.read ℓ) a j) Set.univ := fun ℓ a j =>
    analyticOnNhd_E_mul_read (A := Arch.gated (T := T) (d := d) σ id hid) (dOut := dOut) ℓ a j
  have h5 : ∀ᵐ θ ∂μ, ∀ p q : (Σ ℓ, hid ℓ), p ≠ q →
      (θ.E * θ.read p.1) a₁ (Sum.inl p.2) * (θ.E * θ.read q.1) a₂ (Sum.inl q.2)
        - (θ.E * θ.read q.1) a₁ (Sum.inl q.2) * (θ.E * θ.read p.1) a₂ (Sum.inl p.2) ≠ 0 := by
    refine ae_all_iff.2 fun p => ae_all_iff.2 fun q => ?_
    by_cases hpq : p = q
    · exact Filter.Eventually.of_forall fun _ h _ => absurd hpq h
    · -- the gate column of unit `p` of the read is column `p` of `W₀`, all other columns `0`
      obtain ⟨E₀, W₀, hEW⟩ := exists_minor_ne_zero (q := Σ ℓ, hid ℓ) ha hk hpq
      let θ₀ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut :=
        ⟨E₀, fun ℓ => Matrix.of fun k j => Sum.elim (fun i => W₀ k ⟨ℓ, i⟩) (fun _ => 0) j, 0, 0⟩
      have hg := ((hC p.1 a₁ (Sum.inl p.2)).mul (hC q.1 a₂ (Sum.inl q.2))).sub
        ((hC q.1 a₁ (Sum.inl q.2)).mul (hC p.1 a₂ (Sum.inl p.2)))
      exact (ae_ne_zero_of_analytic μ hg ⟨θ₀, hEW⟩).mono fun _ h _ => h
  filter_upwards [h2, h3, h4, h5] with θ h2 h3 h4 h5
  refine ⟨rank_eq_of_isUnit_det_submatrix_dg θ.E ρE (h2.2.2.1 ρE),
    rank_eq_card_of_isUnit_det θ.D cD (h2.2.1 cD), fun ℓ i hi => h3 ℓ i (congrFun hi o₀),
    fun ℓ i hi => h4 ℓ (Sum.inl i) (congrFun hi a₁), ?_,
    fun ℓ i hi => h4 ℓ (Sum.inr i) (congrFun hi a₁)⟩
  -- if `c_p = r c_q`, the minor of the gate columns `p`, `q` vanishes
  intro p q hpq r hr
  have e1 : (θ.E * θ.read p.1) a₁ (Sum.inl p.2) = r * (θ.E * θ.read q.1) a₁ (Sum.inl q.2) :=
    congrFun hr a₁
  have e2 : (θ.E * θ.read p.1) a₂ (Sum.inl p.2) = r * (θ.E * θ.read q.1) a₂ (Sum.inl q.2) :=
    congrFun hr a₂
  apply h5 p q hpq
  rw [e1, e2]
  ring

/-- **Lemma A.27 (Small writes), first value, for gated blocks:** with `d_in, d_out ≥ d ≥ 2` and
blocks of any widths, for generic parameters `θ` and all small `τ ≠ 0`, the residual network has
`fd(θ_τ) = P - d² - s`. -/
theorem ae_eventually_funDim_smallWrites_gated (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hσa : AnalyticOnNhd ℝ σ Set.univ) (hU : GatedUnitsRescale σ σ' dIn dOut (Σ ℓ, hid ℓ))
    (μ : Measure (Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)) [μ.IsAddHaarMeasure]
    (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, ∀ᶠ τ in 𝓝[≠] (0 : ℝ),
      funDim (Arch.gated σ id hid) 1 (θ.smallWrites τ)
          + (Fintype.card d ^ 2 + ∑ ℓ, Fintype.card (hid ℓ))
        = Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) := by
  filter_upwards [ae_smallWritesGenericGated μ hd hdIn hdOut] with θ hθ
  exact eventually_funDim_smallWrites_gated hσ hσa hU θ hθ

/-- **Theorem 4.7 of the skips paper for gated blocks, without normalization:** with
`d_in, d_out ≥ d ≥ 2` and `L` blocks of any widths, at generic parameters the residual network has
the functional dimension `P - d² - s`, with `s` the number of hidden units. -/
theorem ae_funDim_gated_residual (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hσa : AnalyticOnNhd ℝ σ Set.univ) (hU : GatedUnitsRescale σ σ' dIn dOut (Σ ℓ, hid ℓ))
    (μ : Measure (Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)) [μ.IsAddHaarMeasure]
    (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, funDim (Arch.gated σ id hid) 1 θ
        + (Fintype.card d ^ 2 + ∑ ℓ, Fintype.card (hid ℓ))
      = Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) := by
  have : Nonempty d := Fintype.card_pos_iff.1 (by omega)
  -- one parameter `θ₀` with the conditions, and one small `τ ≠ 0`: `fd(θ₀_τ) = P - d² - s`
  obtain ⟨θ₀, hθ₀⟩ := (ae_smallWritesGenericGated μ hd hdIn hdOut).exists
  obtain ⟨τ, hτ⟩ := (eventually_funDim_smallWrites_gated hσ hσa hU θ₀ hθ₀).exists
  -- at generic `θ`, `fd(θ) ≥ fd(θ₀_τ)` (analytic blocks), and `fd(θ) ≤ P - d² - s`
  filter_upwards [ae_funDim_ge (Arch.gated σ id hid) 1 (fun ℓ => analyticOnNhd_f_gated hσa ℓ)
    analyticOnNhd_id μ (θ₀.smallWrites τ), ae_funDim_add_le_residual_gated μ hdIn] with θ h1 h2
  omega

/-! ### The two kinds of block -/

/-- **Lemma A.27 (Small writes) for SwiGLU blocks, without normalization and without biases.** -/
theorem ae_eventually_funDim_smallWrites_swiglu
    (μ : Measure (Params (Arch.gated (T := T) (d := d) silu id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, ∀ᶠ τ in 𝓝[≠] (0 : ℝ),
      funDim (Arch.gated silu id hid) 1 (θ.smallWrites τ)
          + (Fintype.card d ^ 2 + ∑ ℓ, Fintype.card (hid ℓ))
        = Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) silu id hid) dIn dOut) := by
  exact ae_eventually_funDim_smallWrites_gated hasDerivAt_silu analyticOnNhd_silu
    (silu_gatedUnitsRescale _ _ _) μ hd hdIn hdOut

/-- **Lemma A.27 (Small writes) for GeGLU blocks, without normalization and without biases.** -/
theorem ae_eventually_funDim_smallWrites_geglu
    (μ : Measure (Params (Arch.gated (T := T) (d := d) gelu id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, ∀ᶠ τ in 𝓝[≠] (0 : ℝ),
      funDim (Arch.gated gelu id hid) 1 (θ.smallWrites τ)
          + (Fintype.card d ^ 2 + ∑ ℓ, Fintype.card (hid ℓ))
        = Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) gelu id hid) dIn dOut) := by
  exact ae_eventually_funDim_smallWrites_gated hasDerivAt_gelu analyticOnNhd_gelu
    (gelu_gatedUnitsRescale _ _ _) μ hd hdIn hdOut

/-- **Theorem 4.7 of the skips paper for SwiGLU blocks, without normalization:** at generic
parameters the residual network of `L` blocks has the functional dimension `P - d² - s`. -/
theorem ae_funDim_swiglu_residual
    (μ : Measure (Params (Arch.gated (T := T) (d := d) silu id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, funDim (Arch.gated silu id hid) 1 θ
        + (Fintype.card d ^ 2 + ∑ ℓ, Fintype.card (hid ℓ))
      = Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) silu id hid) dIn dOut) := by
  exact ae_funDim_gated_residual hasDerivAt_silu analyticOnNhd_silu (silu_gatedUnitsRescale _ _ _)
    μ hd hdIn hdOut

/-- **Theorem 4.7 of the skips paper for GeGLU blocks, without normalization:** at generic
parameters the residual network of `L` blocks has the functional dimension `P - d² - s`. -/
theorem ae_funDim_geglu_residual
    (μ : Measure (Params (Arch.gated (T := T) (d := d) gelu id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, funDim (Arch.gated gelu id hid) 1 θ
        + (Fintype.card d ^ 2 + ∑ ℓ, Fintype.card (hid ℓ))
      = Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) gelu id hid) dIn dOut) := by
  exact ae_funDim_gated_residual hasDerivAt_gelu analyticOnNhd_gelu (gelu_gatedUnitsRescale _ _ _)
    μ hd hdIn hdOut

end Skips
