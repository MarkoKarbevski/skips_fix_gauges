import SkipsLean.Residual.SmallWrites
import SkipsLean.OneBlock.Tanh
import SkipsLean.OneBlock.GELU
import SkipsLean.Activations.Analytic

/-!
# Residual networks of `tanh` and GELU blocks at any depth

Paper (skips paper): Lemma A.27 (Small writes), its first value `fd(θ_τ) = P - d² - s`, and
Theorem 4.7 (Equality for residual networks at any depth), both without normalization and without
biases, for MLP blocks whose hidden units have no symmetry of their own (`s = 0`): `tanh` blocks
and GELU blocks. The blocks may have any widths.

The proof of Lemma A.27 places the reads of all blocks side by side and stacks their writes, "so
that `n ↦ f(n W_read) W_write` is one wide block that holds all hidden units of the network". For a
direction `η` that is flat for the limit `J_0` (`Residual/SmallWrites.lean`), Lemma B.3 for the
units of all blocks together (`UnitsRigid` on the hidden units `Σ ℓ, hid ℓ`) gives
`η_E D + E η_D = 0`, `E η_read^ℓ = 0` and `η_write^ℓ D = 0`; as `E` and `D` have rank `d`, this is
`η_E = E X`, `η_D = -X D`, `η_read^ℓ = 0`, `η_write^ℓ = 0`: a space of dimension `d²`.

Theorem 4.7 follows as in the paper: the rank of the Jacobian on a batch is at least its value at
one parameter outside a set of measure zero (the outputs are real-analytic in the parameters), and
at most `P - d²` wherever `E` has rank `d`.
-/

namespace Skips

open Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d]
  [Fintype dIn] [Fintype dOut]
variable {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]
variable {σ σ' : ℝ → ℝ}

/-- **The conditions on `θ` in Lemma A.27, for MLP blocks without normalization:** `E` and `D`
have rank `d`, and "the hypotheses of Lemma B.3 hold for the units of all blocks together": with
`c_{ℓ,i}` the columns of `E W_read^ℓ` and `a_{ℓ,i}` the rows of `W_write^ℓ D`, every `a_{ℓ,i}` is
nonzero and the `c_{ℓ,i}`, over all blocks `ℓ` and hidden units `i`, are nonzero and pairwise
non-collinear. -/
structure SmallWritesGeneric (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) :
    Prop where
  rank_E : θ.E.rank = Fintype.card d
  rank_D : θ.D.rank = Fintype.card d
  /-- every row `a_{ℓ,i}` of `W_write^ℓ D` is nonzero -/
  row_ne_zero : ∀ ℓ i, (θ.write ℓ * θ.D) i ≠ 0
  /-- every column `c_{ℓ,i}` of `E W_read^ℓ` is nonzero -/
  col_ne_zero : ∀ ℓ i, (θ.E * θ.read ℓ)ᵀ i ≠ 0
  /-- the columns `c_{ℓ,i}` of all blocks together are pairwise non-collinear -/
  col_not_collinear : ∀ p q : (Σ ℓ, hid ℓ), p ≠ q → ∀ r : ℝ,
    (θ.E * θ.read p.1)ᵀ p.2 ≠ r • (θ.E * θ.read q.1)ᵀ q.2

/-! ### Helpers: linear algebra -/

omit [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (as `cancel_left_of_rank_res` of `OneBlock/Residual.lean`): a matrix whose rank is its
number of columns cancels on the left, via a left inverse. -/
private theorem cancel_left_of_rank_dm {m n k : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (M : Matrix m n ℝ) (hM : M.rank = Fintype.card n) {X Y : Matrix n k ℝ}
    (h : M * X = M * Y) : X = Y := by
  obtain ⟨B, hB⟩ := Matrix.vecMul_surjective_iff_exists_left_inverse.mp
    (Matrix.vecMul_surjective_iff_rank_eq_card.mpr hM)
  have := congrArg (B * ·) h
  simpa only [← Matrix.mul_assoc, hB, Matrix.one_mul] using this

omit [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: a matrix whose rank is its number of rows cancels on the right, via a right
inverse. -/
private theorem cancel_right_of_rank_dm {m n k : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    (M : Matrix m n ℝ) (hM : M.rank = Fintype.card m) {X Y : Matrix k m ℝ}
    (h : X * M = Y * M) : X = Y := by
  obtain ⟨R, hR⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.mp
    (Matrix.mulVec_surjective_iff_rank_eq_card.mpr hM)
  have := congrArg (· * R) h
  simpa only [Matrix.mul_assoc, hR, Matrix.mul_one] using this

/-! ### Helpers: the limit `J_0` for MLP blocks -/

omit [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the derivative of `M ↦ σ(M)` (entrywise) at `P` along `Q` has the entries
`σ'(P_{t i}) Q_{t i}`. -/
private theorem fderiv_map_apply_dm (hσ : ∀ z, HasDerivAt σ (σ' z) z) {m n : Type*} [Fintype m]
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
    have h := (hσ (P t i)).comp_of_eq (0 : ℝ) hu (by rw [zero_mul, add_zero])
    exact h
  exact h2.unique h3

omit [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the same for the map of block `ℓ` of an MLP network. -/
private theorem fderiv_f_mlp_apply_dm (hσ : ∀ z, HasDerivAt σ (σ' z) z) (ℓ : Fin L)
    (P Q : Matrix T (hid ℓ) ℝ) (t : T) (i : hid ℓ) :
    fderiv ℝ ((Arch.mlp (T := T) (d := d) σ id hid).f ℓ) P Q t i = σ' (P t i) * Q t i :=
  fderiv_map_apply_dm hσ P Q t i

omit [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: an entry of `M N + M' N'`. -/
private theorem mul_add_mul_apply_dm {m n k : Type*} [Fintype n] (M M' : Matrix m n ℝ)
    (N N' : Matrix n k ℝ) (t : m) (o : k) :
    (M * N + M' * N') t o = ∑ i, (M t i * N i o + M' t i * N' i o) := by
  simp only [Matrix.add_apply, Matrix.mul_apply, Finset.sum_add_distrib]

omit [Nonempty T] [DecidableEq d] [Fintype dOut] in
/-- Helper: the entries of `(J_0 η)(x)` for MLP blocks,
`(x ψ_M)_{t o} + ∑_ℓ ∑_i [σ(z_{ℓ i}) (ψ_A^ℓ)_{i o} + σ'(z_{ℓ i}) (x ψ_C^ℓ)_{t i} (A^ℓ)_{i o}]` with
`z_{ℓ i} = (x C^ℓ)_{t i}`, `C^ℓ = E W_read^ℓ`, `A^ℓ = W_write^ℓ D`, `ψ_C^ℓ = E η_read^ℓ`,
`ψ_A^ℓ = η_write^ℓ D`. -/
private theorem smallWritesLimit_mlp_apply (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (θ η : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) (x : Matrix T dIn ℝ) (t : T)
    (o : dOut) :
    smallWritesLimit (Arch.mlp σ id hid) θ η x t o
      = (x * (η.E * θ.D + θ.E * η.D)) t o + ∑ ℓ, ∑ i : hid ℓ,
        (σ ((x * (θ.E * θ.read ℓ)) t i) * (η.write ℓ * θ.D) i o
          + σ' ((x * (θ.E * θ.read ℓ)) t i) * (x * (θ.E * η.read ℓ)) t i
            * (θ.write ℓ * θ.D) i o) := by
  rw [smallWritesLimit, Matrix.add_apply, Matrix.sum_apply]
  congr 1
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  have e : ∀ F' F : Matrix T (hid ℓ) ℝ, ((F' * θ.write ℓ + F * η.write ℓ) * θ.D) t o
      = ∑ i, (F' t i * (θ.write ℓ * θ.D) i o + F t i * (η.write ℓ * θ.D) i o) := by
    intro F' F
    rw [Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc]
    exact mul_add_mul_apply_dm _ _ _ _ t o
  rw [e]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [fderiv_f_mlp_apply_dm hσ, Matrix.mul_assoc x θ.E (θ.read ℓ),
    Matrix.mul_assoc x θ.E (η.read ℓ)]
  show σ' _ * _ * _ + σ _ * _ = _
  ring

/-- **Proof of Lemma A.27, MLP blocks without normalization, the flat directions of `J_0`:** under
the conditions of the lemma, a direction `η` with `(J_0 η)(x) = 0` at every input `x` has
`η_E = E X` and `η_D = -X D` for one matrix `X`, and `η_read^ℓ = 0`, `η_write^ℓ = 0` for every
block. Stated for every activation that satisfies the conclusion of Lemma B.3 with `s = 0`
(`UnitsRigid`) for the hidden units of all blocks together. -/
theorem smallWritesLimit_eq_zero_mlp (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hU : UnitsRigid σ σ' dIn dOut (Σ ℓ, hid ℓ))
    (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) (hθ : SmallWritesGeneric θ)
    (η : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)
    (hη : ∀ x, smallWritesLimit (Arch.mlp σ id hid) θ η x = 0) :
    ∃ X : Matrix d d ℝ, η.E = θ.E * X ∧ η.D = -(X * θ.D)
      ∧ (∀ ℓ, η.read ℓ = 0) ∧ (∀ ℓ, η.write ℓ = 0) := by
  -- row `t₀` of `(J_0 η)(x) = 0` at the inputs `x` whose rows all equal `v`, as a sum over the
  -- hidden units `(ℓ, i)` of all blocks
  have key : ∀ (v : dIn → ℝ) (o : dOut),
      (v ᵥ* (η.E * θ.D + θ.E * η.D)) o + ∑ p : (Σ ℓ, hid ℓ),
        (σ (v ⬝ᵥ (θ.E * θ.read p.1)ᵀ p.2) * (η.write p.1 * θ.D) p.2 o
          + σ' (v ⬝ᵥ (θ.E * θ.read p.1)ᵀ p.2) * (v ⬝ᵥ (θ.E * η.read p.1)ᵀ p.2)
            * (θ.write p.1 * θ.D) p.2 o) = 0 := by
    intro v o
    have h := congrFun (congrFun (hη (Matrix.of fun _ => v)) (Classical.arbitrary T)) o
    rw [smallWritesLimit_mlp_apply hσ, Matrix.zero_apply] at h
    rw [Fintype.sum_sigma]
    exact h
  -- Lemma B.3 for the units of all blocks together, with the linear term `x ψ_M`:
  -- `ψ_M = 0`, `ψ_C = 0` and `ψ_A = 0`
  obtain ⟨hM, -, hc, -, ha⟩ := hU (fun p => (θ.E * θ.read p.1)ᵀ p.2) 0
    (fun p => (θ.write p.1 * θ.D) p.2) (η.E * θ.D + θ.E * η.D) 0
    (fun p => (θ.E * η.read p.1)ᵀ p.2) 0 (fun p => (η.write p.1 * θ.D) p.2)
    (fun p => hθ.row_ne_zero p.1 p.2) (fun p => hθ.col_ne_zero p.1 p.2)
    (fun p q hpq => hθ.col_not_collinear p q hpq) (by
      intro v
      funext o
      simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
        add_zero]
      exact key v o)
  -- `E η_read^ℓ = 0` and `η_write^ℓ D = 0`; `E` cancels on the left and `D` on the right
  have hr : ∀ ℓ, η.read ℓ = 0 := fun ℓ => by
    refine cancel_left_of_rank_dm θ.E hθ.rank_E ?_
    rw [Matrix.mul_zero]
    ext a i
    exact congrFun (congrFun hc ⟨ℓ, i⟩) a
  have hw : ∀ ℓ, η.write ℓ = 0 := fun ℓ => by
    refine cancel_right_of_rank_dm θ.D hθ.rank_D ?_
    rw [Matrix.zero_mul]
    ext i o
    exact congrFun (congrFun ha ⟨ℓ, i⟩) o
  -- `η_E D + E η_D = 0`: with a right inverse `R` of `D`, `X = -(η_D R)`
  obtain ⟨R, hR⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.mp
    (Matrix.mulVec_surjective_iff_rank_eq_card.mpr hθ.rank_D)
  have h1 : η.E + θ.E * (η.D * R) = 0 := by
    have h := congrArg (· * R) hM
    simpa only [Matrix.add_mul, Matrix.mul_assoc, hR, Matrix.mul_one, Matrix.zero_mul] using h
  have hE : η.E = θ.E * -(η.D * R) := by
    rw [Matrix.mul_neg]
    exact eq_neg_of_add_eq_zero_left h1
  -- then `E η_D = -η_E D = E (-(X D))`
  have hD : θ.E * η.D = θ.E * -(-(η.D * R) * θ.D) := by
    rw [Matrix.mul_neg, ← Matrix.mul_assoc, ← hE]
    exact eq_neg_of_add_eq_zero_right hM
  exact ⟨-(η.D * R), hE, cancel_left_of_rank_dm θ.E hθ.rank_E hD, hr, hw⟩

/-- **Lemma A.27 (Small writes), first value, for MLP blocks with `s = 0`, under the conditions of
its proof:** for all small `τ ≠ 0` the residual network has `fd(θ_τ) = P - d²`. -/
theorem eventually_funDim_smallWrites_mlp (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hσa : AnalyticOnNhd ℝ σ Set.univ) (hU : UnitsRigid σ σ' dIn dOut (Σ ℓ, hid ℓ))
    (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) (hθ : SmallWritesGeneric θ) :
    ∀ᶠ τ in 𝓝[≠] (0 : ℝ),
      funDim (Arch.mlp σ id hid) 1 (θ.smallWrites τ) + Fintype.card d ^ 2
        = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) := by
  sorry

/-- The conditions of Lemma A.27 hold at generic parameters, for `d_in, d_out ≥ d ≥ 2` and blocks
of any widths. -/
theorem ae_smallWritesGeneric
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)) [μ.IsAddHaarMeasure]
    (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, SmallWritesGeneric θ := by
  sorry

/-- **Lemma A.27 (Small writes), first value, for MLP blocks with `s = 0`:** with
`d_in, d_out ≥ d ≥ 2` and blocks of any widths, for generic parameters `θ` and all small `τ ≠ 0`,
the residual network has `fd(θ_τ) = P - d²`. -/
theorem ae_eventually_funDim_smallWrites_mlp (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hσa : AnalyticOnNhd ℝ σ Set.univ) (hU : UnitsRigid σ σ' dIn dOut (Σ ℓ, hid ℓ))
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)) [μ.IsAddHaarMeasure]
    (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, ∀ᶠ τ in 𝓝[≠] (0 : ℝ),
      funDim (Arch.mlp σ id hid) 1 (θ.smallWrites τ) + Fintype.card d ^ 2
        = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) := by
  sorry

/-- **Theorem 4.7 of the skips paper for MLP blocks with `s = 0`, without normalization:** with
`d_in, d_out ≥ d ≥ 2` and `L` blocks of any widths, at generic parameters the residual network has
the functional dimension `P - d²`. -/
theorem ae_funDim_mlp_residual (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hσa : AnalyticOnNhd ℝ σ Set.univ) (hU : UnitsRigid σ σ' dIn dOut (Σ ℓ, hid ℓ))
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)) [μ.IsAddHaarMeasure]
    (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, funDim (Arch.mlp σ id hid) 1 θ + Fintype.card d ^ 2
      = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) := by
  sorry

/-! ### The two kinds of block -/

/-- **Lemma A.27 (Small writes) for `tanh` blocks, without normalization and without biases.** -/
theorem ae_eventually_funDim_smallWrites_tanh
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) Real.tanh id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, ∀ᶠ τ in 𝓝[≠] (0 : ℝ),
      funDim (Arch.mlp Real.tanh id hid) 1 (θ.smallWrites τ) + Fintype.card d ^ 2
        = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) Real.tanh id hid) dIn dOut) := by
  sorry

/-- **Lemma A.27 (Small writes) for GELU blocks, without normalization and without biases.** -/
theorem ae_eventually_funDim_smallWrites_gelu
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) gelu id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, ∀ᶠ τ in 𝓝[≠] (0 : ℝ),
      funDim (Arch.mlp gelu id hid) 1 (θ.smallWrites τ) + Fintype.card d ^ 2
        = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) gelu id hid) dIn dOut) := by
  sorry

/-- **Theorem 4.7 of the skips paper for `tanh` blocks, without normalization:** at generic
parameters the residual network of `L` blocks has the functional dimension `P - d²`. -/
theorem ae_funDim_tanh_residual
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) Real.tanh id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, funDim (Arch.mlp Real.tanh id hid) 1 θ + Fintype.card d ^ 2
      = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) Real.tanh id hid) dIn dOut) := by
  sorry

/-- **Theorem 4.7 of the skips paper for GELU blocks, without normalization:** at generic
parameters the residual network of `L` blocks has the functional dimension `P - d²`. -/
theorem ae_funDim_gelu_residual
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) gelu id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, funDim (Arch.mlp gelu id hid) 1 θ + Fintype.card d ^ 2
      = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) gelu id hid) dIn dOut) := by
  sorry

end Skips
