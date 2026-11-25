import SkipsLean.Residual.SmallWritesBiases
import SkipsLean.Residual.DepthGated
import SkipsLean.Symmetry.BiasesRescaleCount
import SkipsLean.OneBlock.MlpBiases

/-!
# Residual networks of SwiGLU and GeGLU blocks with biases at any depth

Paper (skips paper), Lemma A.27 (Small writes), its third value: "For all small `τ ≠ 0`, the
residual network has" the functional dimension "`fd(θ_τ) = P − d_model² − (L + 1) d_model − s`"
for "MLP blocks with biases, no normalization", where the MLP blocks may be "all SwiGLU or all
GeGLU blocks". Its proof: "For the gated blocks, the read of a unit has a gate and a value: `c_i`
and `β_i` belong to the gate, and `e_i`, `β_i′`, `ψ_{e_i}` and `ψ_{β_i′}` are the same
quantities for the value. […] So the flat directions form a space of dimension `d_model² + s`
without biases, and `d_model² + (L + 1) d_model + s` with biases."

Here for gated blocks with biases (`Network/Biases.lean`) of any widths and a gate activation
with the conclusion of Lemma B.3 for SwiGLU and GeGLU (`GatedUnitsRescale`) for the units of all
blocks together, under the conditions `SmallWritesGenericGated` of `Residual/DepthGated.lean` on
the weights; `s` is the number of hidden units of all blocks. The twins: `Residual/DepthGated.lean`
without biases, `Residual/DepthMlpBiases.lean` for `s = 0`; the frame is
`Residual/SmallWritesBiases.lean`.

* `smallWritesLimitB_eq_zero_gated`: a direction that is flat for `J_0` has `η_E = EX`,
  `η_D = −XD`, no component at the gate columns and gate biases, rescales the value of every
  hidden unit (value column and value bias times `−α`, write row times `α`), and has
  `η_{b_D} = −(η_{b_E} − b_E X + ∑_ℓ η_{b_write^ℓ}) D`: a space of dimension
  `d² + (L + 1) d + s`.
* `eventually_funDimB_smallWritesB_gated`: `fd(θ_τ) = P − d² − (L + 1) d − s` for all small
  `τ ≠ 0`, `P` counting the biases; the upper bound is `funDimB_add_le_residual_gated`
  (`Symmetry/BiasesRescaleCount.lean`).
* The same for generic weights and biases (`d_in, d_out ≥ d ≥ 2`), and at generic weights and
  biases the residual network with biases has `fd = P − d² − (L + 1) d − s` at any depth (the
  count of Lemma A.8, attained; not a numbered statement of the paper). Named for SwiGLU and
  GeGLU.
-/

namespace Skips

open Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d]
  [Fintype dIn] [Fintype dOut]
variable {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]
variable {σ σ' : ℝ → ℝ}

/-! ### Helpers: linear algebra -/

/-- Helper (the private `cancel_left_of_rank_dg` of `Residual/DepthGated.lean`): a matrix whose
rank is its number of columns cancels on the left, via a left inverse. -/
private theorem cancel_left_of_rank_dgb {m n k : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (M : Matrix m n ℝ) (hM : M.rank = Fintype.card n) {X Y : Matrix n k ℝ}
    (h : M * X = M * Y) : X = Y := by
  obtain ⟨B, hB⟩ := Matrix.vecMul_surjective_iff_exists_left_inverse.mp
    (Matrix.vecMul_surjective_iff_rank_eq_card.mpr hM)
  have := congrArg (B * ·) h
  simpa only [← Matrix.mul_assoc, hB, Matrix.one_mul] using this

/-- Helper (the private `cancel_right_of_rank_dg` of `Residual/DepthGated.lean`): a matrix whose
rank is its number of rows cancels on the right, via a right inverse. -/
private theorem cancel_right_of_rank_dgb {m n k : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    (M : Matrix m n ℝ) (hM : M.rank = Fintype.card m) {X Y : Matrix k m ℝ}
    (h : X * M = Y * M) : X = Y := by
  obtain ⟨R, hR⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.mp
    (Matrix.mulVec_surjective_iff_rank_eq_card.mpr hM)
  have := congrArg (· * R) h
  simpa only [Matrix.mul_assoc, hR, Matrix.mul_one] using this

/-! ### Helpers: the entries of `J_0` for gated blocks with biases -/

omit [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (the private `hasDerivAt_lineDG` of `Residual/DepthGated.lean`): the line
`τ ↦ a + τ b` has the velocity `b`. -/
private theorem hasDerivAt_line_dgb {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a b : E) : HasDerivAt (fun τ : ℝ => a + τ • b) b 0 := by
  have h := ((hasDerivAt_id (0 : ℝ)).smul_const b).const_add a
  rw [one_smul] at h
  exact h

omit [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: `τ ↦ a + τ b` has the derivative `b` at `0`, in `ℝ`. -/
private theorem hasDerivAt_affine_dgb (a b : ℝ) :
    HasDerivAt (fun τ : ℝ => a + τ * b) b 0 := by
  have h := ((hasDerivAt_id' (x := (0 : ℝ))).mul_const b).const_add a
  rw [one_mul] at h
  exact h

omit [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (the private `fderiv_f_gated_apply` of `Residual/DepthGated.lean`): the derivative of
the map of a gated block at `M` along `N`: entry `(t, i)` is
`σ'(M_{t, g i}) N_{t, g i} M_{t, v i} + σ(M_{t, g i}) N_{t, v i}`. -/
private theorem fderiv_f_gated_apply_dgb (hσ : ∀ z, HasDerivAt σ (σ' z) z) (ℓ : Fin L)
    (M N : Matrix T (hid ℓ ⊕ hid ℓ) ℝ) (t : T) (i : hid ℓ) :
    fderiv ℝ ((Arch.gated (T := T) (d := d) σ id hid).f ℓ) M N t i
      = σ' (M t (Sum.inl i)) * N t (Sum.inl i) * M t (Sum.inr i)
        + σ (M t (Sum.inl i)) * N t (Sum.inr i) := by
  have hd := differentiable_f_gated (T := T) (d := d) (χ := id) (hid := hid)
    (fun z => (hσ z).differentiableAt) ℓ
  -- the chain rule along the line `τ ↦ M + τ N`
  have h1 := (hd M).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) (hasDerivAt_line_dgb M N)
    (by rw [zero_smul, add_zero])
  have h2 := hasDerivAt_pi.1 (hasDerivAt_pi.1 h1 t) i
  -- the same derivative computed on the entry `(t, i)`
  have h3 : HasDerivAt (fun τ : ℝ => σ (M t (Sum.inl i) + τ * N t (Sum.inl i))
      * (M t (Sum.inr i) + τ * N t (Sum.inr i)))
      (σ' (M t (Sum.inl i)) * N t (Sum.inl i) * M t (Sum.inr i)
        + σ (M t (Sum.inl i)) * N t (Sum.inr i)) 0 := by
    have hu := hasDerivAt_affine_dgb (M t (Sum.inl i)) (N t (Sum.inl i))
    have hw := hasDerivAt_affine_dgb (M t (Sum.inr i)) (N t (Sum.inr i))
    have h := ((hσ _).comp (0 : ℝ) hu).mul hw
    convert h using 1
    · rfl
    · simp only [Function.comp_apply, zero_mul, add_zero]
  exact h2.unique h3

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dOut] in
/-- Helper: the pre-activations `(x E + b_E) R + b` of a read `R` with the read bias `b`. -/
private noncomputable def preB_dgb {r : Type*} (E : Matrix dIn d ℝ) (bE : d → ℝ)
    (R : Matrix d r ℝ) (b : r → ℝ) (x : Matrix T dIn ℝ) : Matrix T r ℝ :=
  (x * E + Matrix.of fun _ => bE) * R + Matrix.of fun _ => b

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dOut] in
/-- Helper: at the input whose rows all equal `v`, the entry `(t, j)` of `(x E + b_E) R + b` is
`v · (E R)_{:, j} + (b_E R + b)_j`. -/
private theorem preB_of_dgb {r : Type*} (E : Matrix dIn d ℝ) (bE : d → ℝ) (R : Matrix d r ℝ)
    (b : r → ℝ) (v : dIn → ℝ) (t : T) (j : r) :
    preB_dgb E bE R b (Matrix.of fun _ : T => v) t j = v ⬝ᵥ (E * R)ᵀ j + (bE ᵥ* R + b) j := by
  unfold preB_dgb
  rw [Matrix.add_apply, Matrix.add_mul, Matrix.add_apply, Matrix.mul_assoc, Matrix.of_apply,
    Pi.add_apply, add_assoc]
  rfl

omit [Nonempty T] [DecidableEq d] [Fintype dOut] in
/-- Helper: the entries of `(J_0 η)(x)` for gated blocks with biases: with `z`, `w` the gate and
the value of unit `i` of block `ℓ` (entries of `(x E + b_E) W_read^ℓ + b_read^ℓ`) and `ż`, `ẇ`
those of `(x E + b_E) η_read^ℓ + η_{b_read^ℓ}`, it is `(x ψ_M)_{t o} + (ψ_γ)_o
+ ∑_ℓ ∑_i [σ(z) w (ψ_A)_{i o} + σ'(z) ż w A_{i o} + σ(z) ẇ A_{i o}]`. -/
private theorem smallWritesLimitB_gated_apply_dgb (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (p η : ParamsB (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) (x : Matrix T dIn ℝ)
    (t : T) (o : dOut) :
    smallWritesLimitB (Arch.gated σ id hid) p η x t o
      = (x * (η.1.E * p.1.D + p.1.E * η.1.D)) t o
        + (η.2.E ᵥ* p.1.D + p.2.E ᵥ* η.1.D + η.2.D + ∑ ℓ, η.2.write ℓ ᵥ* p.1.D) o
        + ∑ ℓ, ∑ i : hid ℓ,
          (σ (preB_dgb p.1.E p.2.E (p.1.read ℓ) (p.2.read ℓ) x t (Sum.inl i))
              * preB_dgb p.1.E p.2.E (p.1.read ℓ) (p.2.read ℓ) x t (Sum.inr i)
              * (η.1.write ℓ * p.1.D) i o
            + σ' (preB_dgb p.1.E p.2.E (p.1.read ℓ) (p.2.read ℓ) x t (Sum.inl i))
              * preB_dgb p.1.E p.2.E (η.1.read ℓ) (η.2.read ℓ) x t (Sum.inl i)
              * preB_dgb p.1.E p.2.E (p.1.read ℓ) (p.2.read ℓ) x t (Sum.inr i)
              * (p.1.write ℓ * p.1.D) i o
            + σ (preB_dgb p.1.E p.2.E (p.1.read ℓ) (p.2.read ℓ) x t (Sum.inl i))
              * preB_dgb p.1.E p.2.E (η.1.read ℓ) (η.2.read ℓ) x t (Sum.inr i)
              * (p.1.write ℓ * p.1.D) i o) := by
  unfold smallWritesLimitB preB_dgb
  rw [Matrix.add_apply, Matrix.add_apply, Matrix.sum_apply]
  -- the bias row `ψ_γ` is added to every token
  refine congrArg₂ (· + ·) ?_ (Finset.sum_congr rfl fun ℓ _ => ?_)
  · rfl
  rw [Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc _ (η.1.write ℓ), Matrix.add_apply,
    Matrix.mul_apply, Matrix.mul_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [fderiv_f_gated_apply_dgb hσ]
  have hf : (Arch.gated (T := T) (d := d) σ id hid).f ℓ
      ((x * p.1.E + Matrix.of fun _ => p.2.E) * p.1.read ℓ + Matrix.of fun _ => p.2.read ℓ) t i
      = σ (((x * p.1.E + Matrix.of fun _ : T => p.2.E) * p.1.read ℓ
          + Matrix.of fun _ : T => p.2.read ℓ) t (Sum.inl i))
        * ((x * p.1.E + Matrix.of fun _ : T => p.2.E) * p.1.read ℓ
          + Matrix.of fun _ : T => p.2.read ℓ) t (Sum.inr i) := rfl
  rw [hf]
  ring
/-- **Proof of Lemma A.27, gated blocks with biases without normalization, the flat directions of
`J_0`:** under the conditions of the lemma on the weights, a direction `η` of weights and biases
with `(J_0 η)(x) = 0` at every input `x` has `η_E = E X` and `η_D = −X D` for one matrix `X`,
vanishes at every gate column of a read and at every gate bias, and rescales the value of every
hidden unit: for numbers `α_{ℓ,i}`, the value column and the value bias of unit `i` of block `ℓ`
move by `−α_{ℓ,i}` times themselves and its write row by `α_{ℓ,i}` times itself; and
`η_{b_D} = −(η_{b_E} − b_E X + ∑_ℓ η_{b_write^ℓ}) D`. -/
theorem smallWritesLimitB_eq_zero_gated (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hU : GatedUnitsRescale σ σ' dIn dOut (Σ ℓ, hid ℓ))
    (p : ParamsB (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (hp : SmallWritesGenericGated p.1)
    (η : ParamsB (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (hη : ∀ x, smallWritesLimitB (Arch.gated σ id hid) p η x = 0) :
    ∃ (X : Matrix d d ℝ) (α : ∀ ℓ, hid ℓ → ℝ),
      η.1.E = p.1.E * X ∧ η.1.D = -(X * p.1.D) ∧
      (∀ ℓ (i : hid ℓ) a, η.1.read ℓ a (Sum.inl i) = 0) ∧
      (∀ ℓ (i : hid ℓ) a, η.1.read ℓ a (Sum.inr i) = -(α ℓ i) * p.1.read ℓ a (Sum.inr i)) ∧
      (∀ ℓ (i : hid ℓ) a, η.1.write ℓ i a = α ℓ i * p.1.write ℓ i a) ∧
      (∀ ℓ (i : hid ℓ), η.2.read ℓ (Sum.inl i) = 0) ∧
      (∀ ℓ (i : hid ℓ), η.2.read ℓ (Sum.inr i) = -(α ℓ i) * p.2.read ℓ (Sum.inr i)) ∧
      η.2.D = -((η.2.E - p.2.E ᵥ* X + ∑ ℓ, η.2.write ℓ) ᵥ* p.1.D) := by
  -- Lemma B.3 for the hidden units of all blocks together, on the inputs `x` whose rows all equal
  -- `v` (then `h₀` has all rows `v E + b_E`): `ψ_M = 0`, `ψ_γ = 0`, the gate parts of `ψ_C` and
  -- `ψ_β` vanish, and every unit only rescales its value
  obtain ⟨hm, hγ, hc, hβ, α, hα⟩ := hU
    (fun q => (p.1.E * p.1.read q.1)ᵀ (Sum.inl q.2))
    (fun q => (p.2.E ᵥ* p.1.read q.1 + p.2.read q.1) (Sum.inl q.2))
    (fun q => (p.1.E * p.1.read q.1)ᵀ (Sum.inr q.2))
    (fun q => (p.2.E ᵥ* p.1.read q.1 + p.2.read q.1) (Sum.inr q.2))
    (fun q => (p.1.write q.1 * p.1.D) q.2)
    (η.1.E * p.1.D + p.1.E * η.1.D)
    (η.2.E ᵥ* p.1.D + p.2.E ᵥ* η.1.D + η.2.D + ∑ ℓ, η.2.write ℓ ᵥ* p.1.D)
    (fun q => (p.1.E * η.1.read q.1)ᵀ (Sum.inl q.2))
    (fun q => (p.2.E ᵥ* η.1.read q.1 + η.2.read q.1) (Sum.inl q.2))
    (fun q => (p.1.E * η.1.read q.1)ᵀ (Sum.inr q.2))
    (fun q => (p.2.E ᵥ* η.1.read q.1 + η.2.read q.1) (Sum.inr q.2))
    (fun q => (η.1.write q.1 * p.1.D) q.2)
    (fun q => hp.row_ne_zero q.1 q.2) (fun q => hp.gate_ne_zero q.1 q.2)
    (fun q r hqr => hp.gate_not_collinear q r hqr) (fun q => hp.value_ne_zero q.1 q.2) (by
      intro v
      funext o
      have h := congrFun (congrFun (hη (Matrix.of fun _ => v)) (Classical.arbitrary T)) o
      rw [smallWritesLimitB_gated_apply_dgb hσ] at h
      simp only [preB_of_dgb] at h
      simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
        at h ⊢
      rw [Fintype.sum_sigma]
      exact h)
  -- the reads: `E η_read^ℓ = E R'_ℓ` with `R'_ℓ` the rescaled value columns, and `E` cancels
  have hread : ∀ ℓ, η.1.read ℓ = Matrix.of fun k j =>
      Sum.elim (fun _ => 0) (fun i => -(α ⟨ℓ, i⟩) * p.1.read ℓ k (Sum.inr i)) j := by
    intro ℓ
    apply cancel_left_of_rank_dgb p.1.E hp.rank_E
    ext a j
    rcases j with i | i
    · have h1 : (p.1.E * η.1.read ℓ) a (Sum.inl i) = 0 := congrFun (congrFun hc ⟨ℓ, i⟩) a
      rw [h1, Matrix.mul_apply]
      exact (Finset.sum_eq_zero fun k _ => mul_zero (p.1.E a k)).symm
    · have h1 : (p.1.E * η.1.read ℓ) a (Sum.inr i)
          = -(α ⟨ℓ, i⟩) * (p.1.E * p.1.read ℓ) a (Sum.inr i) := congrFun (hα ⟨ℓ, i⟩).1 a
      rw [h1, Matrix.mul_apply, Matrix.mul_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      show _ = p.1.E a k * (-(α ⟨ℓ, i⟩) * p.1.read ℓ k (Sum.inr i))
      ring
  -- the writes: `η_write^ℓ D = W'_ℓ D` with `W'_ℓ` the rescaled rows, and `D` cancels
  have hwrite : ∀ ℓ, η.1.write ℓ = Matrix.of fun i k => α ⟨ℓ, i⟩ * p.1.write ℓ i k := by
    intro ℓ
    apply cancel_right_of_rank_dgb p.1.D hp.rank_D
    ext i o
    have h1 : (η.1.write ℓ * p.1.D) i o = α ⟨ℓ, i⟩ * (p.1.write ℓ * p.1.D) i o :=
      congrFun (hα ⟨ℓ, i⟩).2.2 o
    rw [h1, Matrix.mul_apply, Matrix.mul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    show _ = α ⟨ℓ, i⟩ * p.1.write ℓ i k * p.1.D k o
    ring
  -- the gate biases: `b_E η_read + η_{b_read}` vanishes at the gates, and so does `η_read`
  have hbg : ∀ ℓ (i : hid ℓ), η.2.read ℓ (Sum.inl i) = 0 := by
    intro ℓ i
    have h1 : (p.2.E ᵥ* η.1.read ℓ + η.2.read ℓ) (Sum.inl i) = 0 := congrFun hβ ⟨ℓ, i⟩
    have h2 : (p.2.E ᵥ* η.1.read ℓ) (Sum.inl i) = 0 := by
      rw [hread ℓ]
      simp only [Matrix.vecMul, dotProduct, Matrix.of_apply, Sum.elim_inl, mul_zero,
        Finset.sum_const_zero]
    rw [Pi.add_apply, h2, zero_add] at h1
    exact h1
  -- the value biases: `b_E η_read + η_{b_read} = −α (b_E W_read + b_read)` at the values, and
  -- `η_read = −α W_read` there
  have hbv : ∀ ℓ (i : hid ℓ), η.2.read ℓ (Sum.inr i) = -(α ⟨ℓ, i⟩) * p.2.read ℓ (Sum.inr i) := by
    intro ℓ i
    have h1 : (p.2.E ᵥ* η.1.read ℓ + η.2.read ℓ) (Sum.inr i)
        = -(α ⟨ℓ, i⟩) * (p.2.E ᵥ* p.1.read ℓ + p.2.read ℓ) (Sum.inr i) := (hα ⟨ℓ, i⟩).2.1
    have h2 : (p.2.E ᵥ* η.1.read ℓ) (Sum.inr i)
        = -(α ⟨ℓ, i⟩) * (p.2.E ᵥ* p.1.read ℓ) (Sum.inr i) := by
      rw [hread ℓ]
      simp only [Matrix.vecMul, dotProduct, Matrix.of_apply, Sum.elim_inr, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    rw [Pi.add_apply, Pi.add_apply, h2] at h1
    linear_combination h1
  -- `η_E D + E η_D = 0`: with a right inverse `R` of `D` and `X = -η_D R`, `η_E = E X`, and then
  -- `E η_D = -E X D`, so `η_D = -X D`
  obtain ⟨R, hR⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.mp
    (Matrix.mulVec_surjective_iff_rank_eq_card.mpr hp.rank_D)
  have hE : η.1.E = p.1.E * -(η.1.D * R) := by
    have h := congrArg (· * R) hm
    simp only [Matrix.add_mul, Matrix.mul_assoc, hR, Matrix.mul_one, Matrix.zero_mul] at h
    rw [Matrix.mul_neg]
    exact eq_neg_of_add_eq_zero_left h
  have hD : η.1.D = -(-(η.1.D * R) * p.1.D) := by
    apply cancel_left_of_rank_dgb p.1.E hp.rank_E
    rw [Matrix.mul_neg, ← Matrix.mul_assoc, ← hE]
    exact eq_neg_of_add_eq_zero_right hm
  obtain ⟨X, hEX, hDX⟩ : ∃ X : Matrix d d ℝ, η.1.E = p.1.E * X ∧ η.1.D = -(X * p.1.D) :=
    ⟨_, hE, hD⟩
  -- the readout bias: `ψ_γ = 0` with `η_D = −X D`
  have hbD : η.2.D = -((η.2.E - p.2.E ᵥ* X + ∑ ℓ, η.2.write ℓ) ᵥ* p.1.D) := by
    rw [hDX, Matrix.vecMul_neg, ← Matrix.vecMul_vecMul] at hγ
    rw [Matrix.add_vecMul, Matrix.sub_vecMul, Matrix.sum_vecMul]
    calc η.2.D = (η.2.E ᵥ* p.1.D + -(p.2.E ᵥ* X ᵥ* p.1.D) + η.2.D
            + ∑ ℓ, η.2.write ℓ ᵥ* p.1.D)
          - (η.2.E ᵥ* p.1.D - p.2.E ᵥ* X ᵥ* p.1.D + ∑ ℓ, η.2.write ℓ ᵥ* p.1.D) := by abel
      _ = _ := by rw [hγ, zero_sub]
  refine ⟨X, fun ℓ i => α ⟨ℓ, i⟩, hEX, hDX, fun ℓ i a => ?_, fun ℓ i a => ?_,
    fun ℓ i a => ?_, hbg, hbv, hbD⟩
  · rw [hread ℓ]
    rfl
  · rw [hread ℓ]
    rfl
  · rw [hwrite ℓ]
    rfl

/-- **Lemma A.27 (Small writes), third value, for gated blocks, under the conditions of its
proof:** for all small `τ ≠ 0` the residual network with biases has
`fd(θ_τ) = P − d² − (L + 1) d − s`, with `s` the number of hidden units and `P` counting the
biases. -/
theorem eventually_funDimB_smallWritesB_gated (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hσa : AnalyticOnNhd ℝ σ Set.univ) (hU : GatedUnitsRescale σ σ' dIn dOut (Σ ℓ, hid ℓ))
    (p : ParamsB (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (hp : SmallWritesGenericGated p.1) :
    ∀ᶠ τ in 𝓝[≠] (0 : ℝ),
      funDimB (Arch.gated σ id hid) 1 (smallWritesB p τ)
          + (Fintype.card d ^ 2 + (L + 1) * Fintype.card d + ∑ ℓ, Fintype.card (hid ℓ))
        = Module.finrank ℝ (ParamsB (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) := by
  sorry

/-- **Lemma A.27 (Small writes), third value, for gated blocks:** with `d_in, d_out ≥ d ≥ 2` and
blocks of any widths, for generic weights and biases and all small `τ ≠ 0`, the residual network
with biases has `fd(θ_τ) = P − d² − (L + 1) d − s`. -/
theorem ae_eventually_funDimB_smallWritesB_gated (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hσa : AnalyticOnNhd ℝ σ Set.univ) (hU : GatedUnitsRescale σ σ' dIn dOut (Σ ℓ, hid ℓ))
    (μ : Measure (ParamsB (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)) [μ.IsAddHaarMeasure]
    (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, ∀ᶠ τ in 𝓝[≠] (0 : ℝ),
      funDimB (Arch.gated σ id hid) 1 (smallWritesB p τ)
          + (Fintype.card d ^ 2 + (L + 1) * Fintype.card d + ∑ ℓ, Fintype.card (hid ℓ))
        = Module.finrank ℝ (ParamsB (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) :=
  (ae_paramsB_of_forall_ae (fun ν _ => ae_smallWritesGenericGated ν hd hdIn hdOut) μ).mono
    fun p hp => eventually_funDimB_smallWritesB_gated hσ hσa hU p hp

/-- **Residual networks of gated blocks with biases, at any depth, at generic weights and
biases** (as Theorem 4.7 follows from the first value of Lemma A.27; the count of Lemma A.8,
attained): with `d_in, d_out ≥ d ≥ 2` and `L` blocks of any widths, the residual network with
biases has the functional dimension `P − d² − (L + 1) d − s`. -/
theorem ae_funDimB_gated_residual (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hσa : AnalyticOnNhd ℝ σ Set.univ) (hU : GatedUnitsRescale σ σ' dIn dOut (Σ ℓ, hid ℓ))
    (μ : Measure (ParamsB (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)) [μ.IsAddHaarMeasure]
    (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, funDimB (Arch.gated σ id hid) 1 p
        + (Fintype.card d ^ 2 + (L + 1) * Fintype.card d + ∑ ℓ, Fintype.card (hid ℓ))
      = Module.finrank ℝ (ParamsB (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) := by
  sorry

/-! ### The two kinds of block -/

/-- **Lemma A.27 (Small writes), third value, for SwiGLU blocks with biases, without
normalization.** -/
theorem ae_eventually_funDimB_smallWritesB_swiglu
    (μ : Measure (ParamsB (Arch.gated (T := T) (d := d) silu id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, ∀ᶠ τ in 𝓝[≠] (0 : ℝ),
      funDimB (Arch.gated silu id hid) 1 (smallWritesB p τ)
          + (Fintype.card d ^ 2 + (L + 1) * Fintype.card d + ∑ ℓ, Fintype.card (hid ℓ))
        = Module.finrank ℝ (ParamsB (Arch.gated (T := T) (d := d) silu id hid) dIn dOut) :=
  ae_eventually_funDimB_smallWritesB_gated hasDerivAt_silu analyticOnNhd_silu
    (silu_gatedUnitsRescale _ _ _) μ hd hdIn hdOut

/-- **Residual networks of SwiGLU blocks with biases at any depth:** at generic weights and
biases the functional dimension is `P − d² − (L + 1) d − s`. -/
theorem ae_funDimB_swiglu_residual
    (μ : Measure (ParamsB (Arch.gated (T := T) (d := d) silu id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, funDimB (Arch.gated silu id hid) 1 p
        + (Fintype.card d ^ 2 + (L + 1) * Fintype.card d + ∑ ℓ, Fintype.card (hid ℓ))
      = Module.finrank ℝ (ParamsB (Arch.gated (T := T) (d := d) silu id hid) dIn dOut) :=
  ae_funDimB_gated_residual hasDerivAt_silu analyticOnNhd_silu
    (silu_gatedUnitsRescale _ _ _) μ hd hdIn hdOut

/-- **Lemma A.27 (Small writes), third value, for GeGLU blocks with biases, without
normalization.** -/
theorem ae_eventually_funDimB_smallWritesB_geglu
    (μ : Measure (ParamsB (Arch.gated (T := T) (d := d) gelu id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, ∀ᶠ τ in 𝓝[≠] (0 : ℝ),
      funDimB (Arch.gated gelu id hid) 1 (smallWritesB p τ)
          + (Fintype.card d ^ 2 + (L + 1) * Fintype.card d + ∑ ℓ, Fintype.card (hid ℓ))
        = Module.finrank ℝ (ParamsB (Arch.gated (T := T) (d := d) gelu id hid) dIn dOut) :=
  ae_eventually_funDimB_smallWritesB_gated hasDerivAt_gelu analyticOnNhd_gelu
    (gelu_gatedUnitsRescale _ _ _) μ hd hdIn hdOut

/-- **Residual networks of GeGLU blocks with biases at any depth:** at generic weights and
biases the functional dimension is `P − d² − (L + 1) d − s`. -/
theorem ae_funDimB_geglu_residual
    (μ : Measure (ParamsB (Arch.gated (T := T) (d := d) gelu id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, funDimB (Arch.gated gelu id hid) 1 p
        + (Fintype.card d ^ 2 + (L + 1) * Fintype.card d + ∑ ℓ, Fintype.card (hid ℓ))
      = Module.finrank ℝ (ParamsB (Arch.gated (T := T) (d := d) gelu id hid) dIn dOut) :=
  ae_funDimB_gated_residual hasDerivAt_gelu analyticOnNhd_gelu
    (gelu_gatedUnitsRescale _ _ _) μ hd hdIn hdOut

end Skips
