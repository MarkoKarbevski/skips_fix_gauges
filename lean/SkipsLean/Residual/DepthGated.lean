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
  sorry

/-- The conditions of Lemma A.27 for gated blocks hold at generic parameters, for
`d_in, d_out ≥ d ≥ 2` and blocks of any widths. -/
theorem ae_smallWritesGenericGated
    (μ : Measure (Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)) [μ.IsAddHaarMeasure]
    (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, SmallWritesGenericGated θ := by
  sorry

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
  sorry

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
  sorry

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
  sorry

/-- **Lemma A.27 (Small writes) for GeGLU blocks, without normalization and without biases.** -/
theorem ae_eventually_funDim_smallWrites_geglu
    (μ : Measure (Params (Arch.gated (T := T) (d := d) gelu id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, ∀ᶠ τ in 𝓝[≠] (0 : ℝ),
      funDim (Arch.gated gelu id hid) 1 (θ.smallWrites τ)
          + (Fintype.card d ^ 2 + ∑ ℓ, Fintype.card (hid ℓ))
        = Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) gelu id hid) dIn dOut) := by
  sorry

/-- **Theorem 4.7 of the skips paper for SwiGLU blocks, without normalization:** at generic
parameters the residual network of `L` blocks has the functional dimension `P - d² - s`. -/
theorem ae_funDim_swiglu_residual
    (μ : Measure (Params (Arch.gated (T := T) (d := d) silu id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, funDim (Arch.gated silu id hid) 1 θ
        + (Fintype.card d ^ 2 + ∑ ℓ, Fintype.card (hid ℓ))
      = Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) silu id hid) dIn dOut) := by
  sorry

/-- **Theorem 4.7 of the skips paper for GeGLU blocks, without normalization:** at generic
parameters the residual network of `L` blocks has the functional dimension `P - d² - s`. -/
theorem ae_funDim_geglu_residual
    (μ : Measure (Params (Arch.gated (T := T) (d := d) gelu id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, funDim (Arch.gated gelu id hid) 1 θ
        + (Fintype.card d ^ 2 + ∑ ℓ, Fintype.card (hid ℓ))
      = Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) gelu id hid) dIn dOut) := by
  sorry

end Skips
