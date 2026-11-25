import SkipsLean.Residual.SmallWritesBiases
import SkipsLean.Residual.DepthMlp
import SkipsLean.Symmetry.BiasesFlat
import SkipsLean.OneBlock.MlpBiases

/-!
# Residual networks of `tanh` and GELU blocks with biases at any depth

Paper (skips paper), Lemma A.27 (Small writes), its third value: "For all small `τ ≠ 0`, the
residual network has" the functional dimension "`fd(θ_τ) = P − d_model² − (L + 1) d_model − s`"
for "MLP blocks with biases, no normalization". Its proof: "At generic parameters the hypotheses
of Lemma B.3 hold for the units of all blocks together, as for one block (Appendix B). So for a
flat `η` the lemma gives
`ψ_M = 0`, `ψ_γ = 0` and a rescaling at every unit. As `E` and `D` have rank `d_model`,
`ψ_M = 0` gives `η_E = EX` and `η_D = −XD` for some `X ∈ ℝ^{d_model × d_model}`. The rescalings
determine `η_read` and `η_write` through `ψ_C` and `ψ_A`, and then `η_{b_read}` through `ψ_β`.
Finally `ψ_γ = 0` determines `η_{b_D}` once `η_{b_E}` and the `η_{b_write^ℓ}` are chosen. So
the flat directions form a space of dimension `d_model² + s` without biases, and
`d_model² + (L + 1) d_model + s` with biases."

Here for MLP blocks whose hidden units have no symmetry of their own (`s = 0`: `tanh` and GELU),
with biases (`Network/Biases.lean`), of any widths, under the conditions `SmallWritesGeneric` of
`Residual/DepthMlp.lean` on the weights (they do not involve the biases). The twin without biases
is `Residual/DepthMlp.lean`; the frame is `Residual/SmallWritesBiases.lean`.

* `smallWritesLimitB_eq_zero_mlp`: a direction that is flat for `J_0` has `η_E = EX`,
  `η_D = −XD`, `η_read^ℓ = 0`, `η_write^ℓ = 0`, `η_{b_read^ℓ} = 0` and
  `η_{b_D} = −(η_{b_E} − b_E X + ∑_ℓ η_{b_write^ℓ}) D`: a space of dimension `d² + (L + 1) d`
  (`X`, `η_{b_E}` and the `η_{b_write^ℓ}` are free).
* `eventually_funDimB_smallWritesB_mlp`: `fd(θ_τ) = P − d² − (L + 1) d` for all small `τ ≠ 0`,
  `P` counting the biases; the upper bound is `funDimB_add_le_residual`
  (`Symmetry/BiasesFlat.lean`).
* The same for generic weights and biases (`d_in, d_out ≥ d ≥ 2`), and, as Theorem 4.7 follows
  from the first value: at generic weights and biases the residual network with biases has
  `fd = P − d² − (L + 1) d` (the paper states this count in Lemma A.8 and checks it in Table 6
  for `tanh` networks with biases; it is not a numbered statement of its own). Named for `tanh`
  and GELU.

Numeric check: `ai_notes/small_writes_biases_check_2026-11-25.py`.
-/

namespace Skips

open Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d]
  [Fintype dIn] [Fintype dOut]
variable {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]
variable {σ σ' : ℝ → ℝ}

/-! ### Helpers: linear algebra -/

omit [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (as `cancel_left_of_rank_dm` of `Residual/DepthMlp.lean`): a matrix whose rank is its
number of columns cancels on the left, via a left inverse. -/
private theorem cancel_left_of_rank_dmb {m n k : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (M : Matrix m n ℝ) (hM : M.rank = Fintype.card n) {X Y : Matrix n k ℝ}
    (h : M * X = M * Y) : X = Y := by
  obtain ⟨B, hB⟩ := Matrix.vecMul_surjective_iff_exists_left_inverse.mp
    (Matrix.vecMul_surjective_iff_rank_eq_card.mpr hM)
  have := congrArg (B * ·) h
  simpa only [← Matrix.mul_assoc, hB, Matrix.one_mul] using this

omit [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: a matrix whose rank is its number of rows cancels on the right, via a right
inverse. -/
private theorem cancel_right_of_rank_dmb {m n k : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    (M : Matrix m n ℝ) (hM : M.rank = Fintype.card m) {X Y : Matrix k m ℝ}
    (h : X * M = Y * M) : X = Y := by
  obtain ⟨R, hR⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.mp
    (Matrix.mulVec_surjective_iff_rank_eq_card.mpr hM)
  have := congrArg (· * R) h
  simpa only [Matrix.mul_assoc, hR, Matrix.mul_one] using this

/-! ### Helpers: the limit `J_0` for MLP blocks with biases -/

omit [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the derivative of `M ↦ σ(M)` (entrywise) at `P` along `Q` has the entries
`σ'(P_{t i}) Q_{t i}`. -/
private theorem fderiv_map_apply_dmb (hσ : ∀ z, HasDerivAt σ (σ' z) z) {m n : Type*}
    [Fintype m] [Fintype n] (P Q : Matrix m n ℝ) (t : m) (i : n) :
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
private theorem fderiv_f_mlp_apply_dmb (hσ : ∀ z, HasDerivAt σ (σ' z) z) (ℓ : Fin L)
    (P Q : Matrix T (hid ℓ) ℝ) (t : T) (i : hid ℓ) :
    fderiv ℝ ((Arch.mlp (T := T) (d := d) σ id hid).f ℓ) P Q t i = σ' (P t i) * Q t i :=
  fderiv_map_apply_dmb hσ P Q t i

omit [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: an entry of `M N + M' N'`. -/
private theorem mul_add_mul_apply_dmb {m n k : Type*} [Fintype n] (M M' : Matrix m n ℝ)
    (N N' : Matrix n k ℝ) (t : m) (o : k) :
    (M * N + M' * N') t o = ∑ i, (M t i * N i o + M' t i * N' i o) := by
  simp only [Matrix.add_apply, Matrix.mul_apply, Finset.sum_add_distrib]

omit [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the entries of the pre-activations `z = (x E + b_E) R + b`, with the rows `b_E` and
`b` added to every token: `z_{t i} = (x (E R))_{t i} + (b_E R + b)_i`. -/
private theorem zrow_dmb {m n k r : Type*} [Fintype n] [Fintype k] (x : Matrix m n ℝ)
    (E : Matrix n k ℝ) (bE : k → ℝ) (R : Matrix k r ℝ) (b : r → ℝ) (t : m) (i : r) :
    ((x * E + Matrix.of fun _ => bE) * R + Matrix.of fun _ => b : Matrix m r ℝ) t i
      = (x * (E * R)) t i + (bE ᵥ* R + b) i := by
  rw [Matrix.add_mul, Matrix.mul_assoc, Matrix.add_apply, Matrix.add_apply, add_assoc]
  rfl

omit [Nonempty T] [DecidableEq d] [Fintype dOut] in
/-- Helper: the entries of `(J_0 η)(x)` for MLP blocks with biases,
`(x ψ_M)_{t o} + (ψ_γ)_o + ∑_ℓ ∑_i [σ(z_{ℓ i}) (ψ_A^ℓ)_{i o}
+ σ'(z_{ℓ i}) ((x ψ_C^ℓ)_{t i} + (ψ_β^ℓ)_i) (A^ℓ)_{i o}]` with
`z_{ℓ i} = (x C^ℓ)_{t i} + β^ℓ_i`, `C^ℓ = E W_read^ℓ`, `β^ℓ = b_E W_read^ℓ + b_read^ℓ`,
`A^ℓ = W_write^ℓ D`. -/
private theorem smallWritesLimitB_mlp_apply_dmb (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (p η : ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) (x : Matrix T dIn ℝ)
    (t : T) (o : dOut) :
    smallWritesLimitB (Arch.mlp σ id hid) p η x t o
      = (x * (η.1.E * p.1.D + p.1.E * η.1.D)) t o
        + (η.2.E ᵥ* p.1.D + p.2.E ᵥ* η.1.D + η.2.D + ∑ ℓ, η.2.write ℓ ᵥ* p.1.D) o
        + ∑ ℓ, ∑ i : hid ℓ,
          (σ ((x * (p.1.E * p.1.read ℓ)) t i + (p.2.E ᵥ* p.1.read ℓ + p.2.read ℓ) i)
              * (η.1.write ℓ * p.1.D) i o
            + σ' ((x * (p.1.E * p.1.read ℓ)) t i + (p.2.E ᵥ* p.1.read ℓ + p.2.read ℓ) i)
              * ((x * (p.1.E * η.1.read ℓ)) t i + (p.2.E ᵥ* η.1.read ℓ + η.2.read ℓ) i)
              * (p.1.write ℓ * p.1.D) i o) := by
  rw [smallWritesLimitB, Matrix.add_apply, Matrix.add_apply, Matrix.of_apply, Matrix.sum_apply]
  congr 1
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  have e : ∀ F' F : Matrix T (hid ℓ) ℝ, ((F' * p.1.write ℓ + F * η.1.write ℓ) * p.1.D) t o
      = ∑ i, (F' t i * (p.1.write ℓ * p.1.D) i o + F t i * (η.1.write ℓ * p.1.D) i o) := by
    intro F' F
    rw [Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc]
    exact mul_add_mul_apply_dmb _ _ _ _ t o
  rw [e]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [fderiv_f_mlp_apply_dmb hσ]
  show σ' _ * _ * _ + σ _ * _ = _
  rw [zrow_dmb, zrow_dmb]
  ring

/-- **Proof of Lemma A.27, MLP blocks with biases without normalization, the flat directions of
`J_0`:** under the conditions of the lemma on the weights, a direction `η` of weights and biases
with `(J_0 η)(x) = 0` at every input `x` has `η_E = E X` and `η_D = −X D` for one matrix `X`,
`η_read^ℓ = 0`, `η_write^ℓ = 0` and `η_{b_read^ℓ} = 0` for every block, and
`η_{b_D} = −(η_{b_E} − b_E X + ∑_ℓ η_{b_write^ℓ}) D`. Stated for every activation that
satisfies the conclusion of Lemma B.3 with `s = 0` (`UnitsRigid`) for the hidden units of all
blocks together. -/
theorem smallWritesLimitB_eq_zero_mlp (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hU : UnitsRigid σ σ' dIn dOut (Σ ℓ, hid ℓ))
    (p : ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) (hp : SmallWritesGeneric p.1)
    (η : ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)
    (hη : ∀ x, smallWritesLimitB (Arch.mlp σ id hid) p η x = 0) :
    ∃ X : Matrix d d ℝ, η.1.E = p.1.E * X ∧ η.1.D = -(X * p.1.D) ∧
      (∀ ℓ, η.1.read ℓ = 0) ∧ (∀ ℓ, η.1.write ℓ = 0) ∧ (∀ ℓ, η.2.read ℓ = 0) ∧
      η.2.D = -((η.2.E - p.2.E ᵥ* X + ∑ ℓ, η.2.write ℓ) ᵥ* p.1.D) := by
  -- row `t₀` of `(J_0 η)(x) = 0` at the inputs `x` whose rows all equal `v`, as a sum over the
  -- hidden units `(ℓ, i)` of all blocks
  have key : ∀ (v : dIn → ℝ) (o : dOut),
      (v ᵥ* (η.1.E * p.1.D + p.1.E * η.1.D)) o
        + (η.2.E ᵥ* p.1.D + p.2.E ᵥ* η.1.D + η.2.D + ∑ ℓ, η.2.write ℓ ᵥ* p.1.D) o
        + ∑ u : (Σ ℓ, hid ℓ),
          (σ (v ⬝ᵥ (p.1.E * p.1.read u.1)ᵀ u.2 + (p.2.E ᵥ* p.1.read u.1 + p.2.read u.1) u.2)
              * (η.1.write u.1 * p.1.D) u.2 o
            + σ' (v ⬝ᵥ (p.1.E * p.1.read u.1)ᵀ u.2 + (p.2.E ᵥ* p.1.read u.1 + p.2.read u.1) u.2)
              * (v ⬝ᵥ (p.1.E * η.1.read u.1)ᵀ u.2
                + (p.2.E ᵥ* η.1.read u.1 + η.2.read u.1) u.2)
              * (p.1.write u.1 * p.1.D) u.2 o) = 0 := by
    intro v o
    have h := congrFun (congrFun (hη (Matrix.of fun _ => v)) (Classical.arbitrary T)) o
    rw [smallWritesLimitB_mlp_apply_dmb hσ, Matrix.zero_apply] at h
    rw [Fintype.sum_sigma]
    exact h
  -- Lemma B.3 for the units of all blocks together, with the linear term `x ψ_M` and the
  -- constant `ψ_γ`: `ψ_M = 0`, `ψ_γ = 0`, `ψ_C = 0`, `ψ_β = 0` and `ψ_A = 0`
  obtain ⟨hM, hγ, hc, hβ, ha⟩ := hU (fun u => (p.1.E * p.1.read u.1)ᵀ u.2)
    (fun u => (p.2.E ᵥ* p.1.read u.1 + p.2.read u.1) u.2) (fun u => (p.1.write u.1 * p.1.D) u.2)
    (η.1.E * p.1.D + p.1.E * η.1.D)
    (η.2.E ᵥ* p.1.D + p.2.E ᵥ* η.1.D + η.2.D + ∑ ℓ, η.2.write ℓ ᵥ* p.1.D)
    (fun u => (p.1.E * η.1.read u.1)ᵀ u.2) (fun u => (p.2.E ᵥ* η.1.read u.1 + η.2.read u.1) u.2)
    (fun u => (η.1.write u.1 * p.1.D) u.2)
    (fun u => hp.row_ne_zero u.1 u.2) (fun u => hp.col_ne_zero u.1 u.2)
    (fun u w huw => hp.col_not_collinear u w huw) (by
      intro v
      funext o
      simpa only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
        using key v o)
  -- `E η_read^ℓ = 0` and `η_write^ℓ D = 0`; `E` cancels on the left and `D` on the right
  have hr : ∀ ℓ, η.1.read ℓ = 0 := fun ℓ => by
    refine cancel_left_of_rank_dmb p.1.E hp.rank_E ?_
    rw [Matrix.mul_zero]
    ext a i
    exact congrFun (congrFun hc ⟨ℓ, i⟩) a
  have hw : ∀ ℓ, η.1.write ℓ = 0 := fun ℓ => by
    refine cancel_right_of_rank_dmb p.1.D hp.rank_D ?_
    rw [Matrix.zero_mul]
    ext i o
    exact congrFun (congrFun ha ⟨ℓ, i⟩) o
  -- then `ψ_β = b_E η_read + η_{b_read} = 0` gives `η_{b_read}^ℓ = 0`
  have hbr : ∀ ℓ, η.2.read ℓ = 0 := fun ℓ => by
    funext i
    have h := congrFun hβ ⟨ℓ, i⟩
    simp only [hr ℓ, Matrix.vecMul_zero, zero_add, Pi.zero_apply] at h
    exact h
  -- `η_E D + E η_D = 0`: with a right inverse `R` of `D`, `X = -(η_D R)`
  obtain ⟨R, hR⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.mp
    (Matrix.mulVec_surjective_iff_rank_eq_card.mpr hp.rank_D)
  have h1 : η.1.E + p.1.E * (η.1.D * R) = 0 := by
    have h := congrArg (· * R) hM
    simpa only [Matrix.add_mul, Matrix.mul_assoc, hR, Matrix.mul_one, Matrix.zero_mul] using h
  have hE : η.1.E = p.1.E * -(η.1.D * R) := by
    rw [Matrix.mul_neg]
    exact eq_neg_of_add_eq_zero_left h1
  -- then `E η_D = -η_E D = E (-(X D))`
  have hD : η.1.D = -(-(η.1.D * R) * p.1.D) := by
    refine cancel_left_of_rank_dmb p.1.E hp.rank_E ?_
    rw [Matrix.mul_neg, ← Matrix.mul_assoc, ← hE]
    exact eq_neg_of_add_eq_zero_right hM
  -- `ψ_γ = 0` with `η_D = -X D`: `η_{b_D} = -(η_{b_E} - b_E X + ∑_ℓ η_{b_write^ℓ}) D`
  have hbD : η.2.D = -((η.2.E - p.2.E ᵥ* -(η.1.D * R) + ∑ ℓ, η.2.write ℓ) ᵥ* p.1.D) := by
    rw [hD, Matrix.vecMul_neg] at hγ
    rw [Matrix.add_vecMul, Matrix.sub_vecMul, Matrix.vecMul_vecMul, Matrix.sum_vecMul,
      eq_neg_iff_add_eq_zero, ← hγ]
    abel
  exact ⟨-(η.1.D * R), hE, hD, hr, hw, hbr, hbD⟩

/-- Helper: the directions `(X, e, w) ↦ ((E X, 0, 0, −X D), (e, 0, w, −(e − b_E X + ∑_ℓ w_ℓ) D))`
of one change of basis at all hidden states and of the translations (reads, writes and read
biases fixed), as a linear map from `Matrix d d ℝ × (d → ℝ) × (Fin L → d → ℝ)`. -/
private def smallWritesFlatLinB_dmb
    (p : ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) :
    Matrix d d ℝ × (d → ℝ) × (Fin L → d → ℝ) →ₗ[ℝ]
      ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut where
  toFun Xew := (⟨p.1.E * Xew.1, 0, 0, -(Xew.1 * p.1.D)⟩,
    ⟨Xew.2.1, 0, Xew.2.2, -((Xew.2.1 - p.2.E ᵥ* Xew.1 + ∑ ℓ, Xew.2.2 ℓ) ᵥ* p.1.D)⟩)
  map_add' u w := by
    refine Prod.ext (Params.ext' ?_ (fun ℓ => ?_) (fun ℓ => ?_) ?_)
      (Biases.ext' ?_ (fun ℓ => ?_) (fun ℓ => ?_) ?_) <;>
    simp only [Prod.fst_add, Prod.snd_add, Params.add_E, Params.add_read, Params.add_write,
      Params.add_D, Biases.add_E, Biases.add_read, Biases.add_write, Biases.add_D, Pi.add_apply,
      Pi.zero_apply, Matrix.mul_add, Matrix.add_mul, Matrix.vecMul_add, Matrix.add_vecMul,
      Matrix.sub_vecMul, Matrix.sum_vecMul, Finset.sum_add_distrib, neg_add, add_zero]
    abel
  map_smul' c u := by
    refine Prod.ext (Params.ext' ?_ (fun ℓ => ?_) (fun ℓ => ?_) ?_)
      (Biases.ext' ?_ (fun ℓ => ?_) (fun ℓ => ?_) ?_) <;>
    simp only [Prod.smul_fst, Prod.smul_snd, Params.smul_E, Params.smul_read, Params.smul_write,
      Params.smul_D, Biases.smul_E, Biases.smul_read, Biases.smul_write, Biases.smul_D,
      Pi.smul_apply, Pi.zero_apply, Matrix.mul_smul, Matrix.smul_mul, Matrix.vecMul_smul,
      Matrix.smul_vecMul, Matrix.add_vecMul, Matrix.sub_vecMul, Matrix.sum_vecMul,
      Finset.smul_sum, smul_add, smul_sub, smul_neg, smul_zero, RingHom.id_apply]

/-- **Lemma A.27 (Small writes), third value, for MLP blocks with `s = 0`, under the conditions of
its proof:** for all small `τ ≠ 0` the residual network with biases has
`fd(θ_τ) = P − d² − (L + 1) d`, with `P` counting the biases. -/
theorem eventually_funDimB_smallWritesB_mlp (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hσa : AnalyticOnNhd ℝ σ Set.univ) (hU : UnitsRigid σ σ' dIn dOut (Σ ℓ, hid ℓ))
    (p : ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) (hp : SmallWritesGeneric p.1) :
    ∀ᶠ τ in 𝓝[≠] (0 : ℝ),
      funDimB (Arch.mlp σ id hid) 1 (smallWritesB p τ)
          + (Fintype.card d ^ 2 + (L + 1) * Fintype.card d)
        = Module.finrank ℝ (ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) := by
  have hσd : Differentiable ℝ σ := fun z => (hσ z).differentiableAt
  -- the flat directions of `J_0` lie in the range `V` of `(X, e, w) ↦ …` (the previous theorem)
  have hV : ∀ η, (∀ x, smallWritesLimitB (Arch.mlp σ id hid) p η x = 0) →
      η ∈ LinearMap.range (smallWritesFlatLinB_dmb p) := by
    intro η hη
    obtain ⟨X, hE, hD, hr, hw, hbr, hbD⟩ := smallWritesLimitB_eq_zero_mlp hσ hU p hp η hη
    exact ⟨(X, η.2.E, η.2.write), Prod.ext
      (Params.ext' hE.symm (fun ℓ => (hr ℓ).symm) (fun ℓ => (hw ℓ).symm) hD.symm)
      (Biases.ext' rfl (fun ℓ => (hbr ℓ).symm) (fun _ => rfl) hbD.symm)⟩
  -- `dim V ≤ d² + d + L d = d² + (L + 1) d`
  have hdim : Module.finrank ℝ (LinearMap.range (smallWritesFlatLinB_dmb p))
      ≤ Fintype.card d ^ 2 + (L + 1) * Fintype.card d := by
    have h := LinearMap.finrank_range_le (smallWritesFlatLinB_dmb p)
    have h2 : Module.finrank ℝ (Matrix d d ℝ × (d → ℝ) × (Fin L → d → ℝ))
        = Fintype.card d ^ 2 + (L + 1) * Fintype.card d := by
      simp only [Module.finrank_prod, Module.finrank_matrix, Module.finrank_self,
        Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        smul_eq_mul, mul_one]
      ring
    omega
  -- `≥`: "The rank" of the proof of Lemma A.27 (`Residual/SmallWritesBiases.lean`); `≤`: the
  -- upper bound for residual networks with biases, as `E` is not changed by `p ↦ p_τ`
  filter_upwards [eventually_funDimB_smallWritesB_ge (Arch.mlp σ id hid) p rfl
    (fun ℓ => analyticOnNhd_f_mlp hσa ℓ) _ hV] with τ hτ
  have hle := funDimB_add_le_residual (smallWritesB p τ) rfl
    (fun ℓ => differentiable_f_mlp hσd ℓ) hp.rank_E
  omega

/-- **Lemma A.27 (Small writes), third value, for MLP blocks with `s = 0`:** with
`d_in, d_out ≥ d ≥ 2` and blocks of any widths, for generic weights and biases and all small
`τ ≠ 0`, the residual network with biases has `fd(θ_τ) = P − d² − (L + 1) d`. -/
theorem ae_eventually_funDimB_smallWritesB_mlp (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hσa : AnalyticOnNhd ℝ σ Set.univ) (hU : UnitsRigid σ σ' dIn dOut (Σ ℓ, hid ℓ))
    (μ : Measure (ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)) [μ.IsAddHaarMeasure]
    (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, ∀ᶠ τ in 𝓝[≠] (0 : ℝ),
      funDimB (Arch.mlp σ id hid) 1 (smallWritesB p τ)
          + (Fintype.card d ^ 2 + (L + 1) * Fintype.card d)
        = Module.finrank ℝ (ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) :=
  (ae_paramsB_of_forall_ae (fun ν _ => ae_smallWritesGeneric ν hd hdIn hdOut) μ).mono
    fun p hp => eventually_funDimB_smallWritesB_mlp hσ hσa hU p hp

/-- **Residual networks of MLP blocks with `s = 0` with biases, at any depth, at generic weights
and biases** (as Theorem 4.7 follows from the first value of Lemma A.27; the count of Lemma A.8,
attained): with `d_in, d_out ≥ d ≥ 2` and `L` blocks of any widths, the residual network with
biases has the functional dimension `P − d² − (L + 1) d`. -/
theorem ae_funDimB_mlp_residual (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hσa : AnalyticOnNhd ℝ σ Set.univ) (hU : UnitsRigid σ σ' dIn dOut (Σ ℓ, hid ℓ))
    (μ : Measure (ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)) [μ.IsAddHaarMeasure]
    (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, funDimB (Arch.mlp σ id hid) 1 p
        + (Fintype.card d ^ 2 + (L + 1) * Fintype.card d)
      = Module.finrank ℝ (ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) := by
  have hσd : Differentiable ℝ σ := fun z => (hσ z).differentiableAt
  have hf : ∀ ℓ, AnalyticOnNhd ℝ ((Arch.mlp (T := T) (d := d) σ id hid).f ℓ) Set.univ :=
    fun ℓ => analyticOnNhd_f_mlp hσa ℓ
  -- the conditions of Lemma A.27 on the weights hold at almost every `(θ, b)`
  have hgen : ∀ᵐ p ∂μ, SmallWritesGeneric p.1 :=
    ae_paramsB_of_forall_ae (fun ν _ => ae_smallWritesGeneric ν hd hdIn hdOut) μ
  -- one `p₀` with these conditions, and one small `τ ≠ 0`: `fd(p₀_τ) = P - d² - (L + 1) d`
  obtain ⟨p₀, hp₀⟩ := hgen.exists
  obtain ⟨τ, hτ⟩ := (eventually_funDimB_smallWritesB_mlp hσ hσa hU p₀ hp₀).exists
  -- at almost every `p`, `fd(p) ≥ fd(p₀_τ)` (analytic outputs) and, as `E` has rank `d`,
  -- `fd(p) ≤ P - d² - (L + 1) d`
  filter_upwards [ae_funDimB_ge (Arch.mlp σ id hid) 1 hf analyticOnNhd_id μ (smallWritesB p₀ τ),
    hgen] with p h1 h2
  have h3 := funDimB_add_le_residual p rfl (fun ℓ => differentiable_f_mlp hσd ℓ) h2.rank_E
  omega

/-! ### The two kinds of block -/

/-- **Lemma A.27 (Small writes), third value, for `tanh` blocks with biases, without
normalization.** -/
theorem ae_eventually_funDimB_smallWritesB_tanh
    (μ : Measure (ParamsB (Arch.mlp (T := T) (d := d) Real.tanh id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, ∀ᶠ τ in 𝓝[≠] (0 : ℝ),
      funDimB (Arch.mlp Real.tanh id hid) 1 (smallWritesB p τ)
          + (Fintype.card d ^ 2 + (L + 1) * Fintype.card d)
        = Module.finrank ℝ (ParamsB (Arch.mlp (T := T) (d := d) Real.tanh id hid) dIn dOut) :=
  ae_eventually_funDimB_smallWritesB_mlp hasDerivAt_tanh analyticOnNhd_tanh
    (tanh_unitsRigid _ _ _) μ hd hdIn hdOut

/-- **Residual networks of `tanh` blocks with biases at any depth:** at generic weights and
biases the functional dimension is `P − d² − (L + 1) d`. -/
theorem ae_funDimB_tanh_residual
    (μ : Measure (ParamsB (Arch.mlp (T := T) (d := d) Real.tanh id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, funDimB (Arch.mlp Real.tanh id hid) 1 p
        + (Fintype.card d ^ 2 + (L + 1) * Fintype.card d)
      = Module.finrank ℝ (ParamsB (Arch.mlp (T := T) (d := d) Real.tanh id hid) dIn dOut) :=
  ae_funDimB_mlp_residual hasDerivAt_tanh analyticOnNhd_tanh
    (tanh_unitsRigid _ _ _) μ hd hdIn hdOut

/-- **Lemma A.27 (Small writes), third value, for GELU blocks with biases, without
normalization.** -/
theorem ae_eventually_funDimB_smallWritesB_gelu
    (μ : Measure (ParamsB (Arch.mlp (T := T) (d := d) gelu id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, ∀ᶠ τ in 𝓝[≠] (0 : ℝ),
      funDimB (Arch.mlp gelu id hid) 1 (smallWritesB p τ)
          + (Fintype.card d ^ 2 + (L + 1) * Fintype.card d)
        = Module.finrank ℝ (ParamsB (Arch.mlp (T := T) (d := d) gelu id hid) dIn dOut) :=
  ae_eventually_funDimB_smallWritesB_mlp hasDerivAt_gelu analyticOnNhd_gelu
    (gelu_unitsRigid _ _ _) μ hd hdIn hdOut

/-- **Residual networks of GELU blocks with biases at any depth:** at generic weights and
biases the functional dimension is `P − d² − (L + 1) d`. -/
theorem ae_funDimB_gelu_residual
    (μ : Measure (ParamsB (Arch.mlp (T := T) (d := d) gelu id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, funDimB (Arch.mlp gelu id hid) 1 p
        + (Fintype.card d ^ 2 + (L + 1) * Fintype.card d)
      = Module.finrank ℝ (ParamsB (Arch.mlp (T := T) (d := d) gelu id hid) dIn dOut) :=
  ae_funDimB_mlp_residual hasDerivAt_gelu analyticOnNhd_gelu
    (gelu_unitsRigid _ _ _) μ hd hdIn hdOut

end Skips
