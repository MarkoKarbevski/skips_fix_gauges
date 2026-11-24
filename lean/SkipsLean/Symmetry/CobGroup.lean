import SkipsLean.Generic.GroupDimension
import SkipsLean.Symmetry.OnlyOrthogonalRows
import SkipsLean.Residual.OneChangeOfBasis

/-!
# The group of the changes of basis that preserve the function, and its dimension

Paper (skips paper): Theorem 3.3 (One change of basis for the whole network), part (ii): "The
changes of basis that preserve the function at all parameters form a group of dimension
`(L + 1) dim 𝒢` in a skipless network and `dim 𝒢` in a residual one: `(L + 1) d_model²` and
`d_model²` without normalization, and `(L + 1) d_model (d_model − 1)/2` and
`d_model (d_model − 1)/2` under pre-RMSNorm." Theorem A.17 (i) is the same sentence for
"Without normalization or with pre-RMSNorm and `ε > 0`".

Here: `cobPreserving A S dIn dOut` is the set of the families `G_0, …, G_L` of invertible matrices
such that `θ.cob G G` computes the same function as `θ` for all values of the parameters `θ`
(skipless: `S = 0`; residual: `S = 1`). It is a subgroup of the families of invertible matrices,
for any network. Its dimension is stated for the set of matrices `cobPreservingMat`, as the
Hausdorff dimension (`Generic/GroupDimension.lean` says why this notion):
- skipless, no normalization: every family passes, dimension `(L + 1) d²` (any blocks);
- skipless, pre-RMSNorm (`ε > 0`): exactly the families of orthogonal matrices pass, dimension
  `(L + 1) d (d − 1)/2`: for any network for which only orthogonal changes of basis pass
  (Lemma A.4), and by name for MLP blocks, gated blocks, attention blocks and the networks of
  attention blocks and MLP or gated blocks, under the hypotheses of Lemma A.4 for them
  (`Symmetry/OnlyOrthogonal.lean`, `Symmetry/OnlyOrthogonalRows.lean`);
- residual, no normalization: exactly the families with all `G_ℓ` equal pass, dimension `d²`;
  residual, pre-RMSNorm: all equal and orthogonal, dimension `d (d − 1)/2`; both under the
  hypothesis of Theorem A.5 (iii) that every block is nonzero for some value of its parameters
  (`Residual/OneChangeOfBasis.lean`).
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise ENNReal

variable {T d : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d]

/-- **The changes of basis that preserve the function at all parameters** (Theorem 3.3 (ii)): the
families `G_0, …, G_L` of invertible matrices such that `θ.cob G G` and `θ` compute the same
function, for all parameters `θ` with inputs in `ℝ^{T × d_in}` and outputs in `ℝ^{T × d_out}`. -/
def cobPreserving (A : Arch T d L) (S : Fin L → Matrix d d ℝ) (dIn dOut : Type*) [Fintype dIn]
    [Fintype dOut] : Set (Fin (L + 1) → GL d ℝ) :=
  {G | ∀ (θ : Params A dIn dOut) (x : Matrix T dIn ℝ), eval A S (θ.cob G G) x = eval A S θ x}

/-- The set `cobPreserving`, as a set of families of `d × d` matrices. -/
def cobPreservingMat (A : Arch T d L) (S : Fin L → Matrix d d ℝ) (dIn dOut : Type*)
    [Fintype dIn] [Fintype dOut] : Set (Fin (L + 1) → Matrix d d ℝ) :=
  (fun (G : Fin (L + 1) → GL d ℝ) ℓ => (G ℓ : Matrix d d ℝ)) '' cobPreserving A S dIn dOut

variable {dIn dOut : Type*} [Fintype dIn] [Fintype dOut]
variable {sees : T → T → Prop} [DecidableRel sees]
variable {H dh hid : Fin L → Type} [∀ ℓ, Fintype (H ℓ)] [∀ ℓ, Fintype (dh ℓ)]
  [∀ ℓ, Fintype (hid ℓ)] {σ : ℝ → ℝ} {ε : ℝ}

omit [Fintype T] [Fintype dIn] [Fintype dOut] in
/-- Helper: two changes of basis in a row are the change of basis by the product. -/
private theorem cob_cob_cgrp (A : Arch T d L) (θ : Params A dIn dOut)
    (G G' : Fin (L + 1) → GL d ℝ) : (θ.cob G G).cob G' G' = θ.cob (G * G') (G * G') := by
  refine Params.ext' ?_ (fun ℓ => ?_) (fun ℓ => ?_) ?_ <;>
    simp only [Params.cob, Pi.mul_apply, _root_.mul_inv_rev, Units.val_mul, Matrix.mul_assoc]

omit [Fintype T] [Fintype dIn] [Fintype dOut] in
/-- Helper: the change of basis `1` does not move the parameters. -/
private theorem cob_one_cgrp (A : Arch T d L) (θ : Params A dIn dOut) :
    θ.cob (1 : Fin (L + 1) → GL d ℝ) 1 = θ := by
  refine Params.ext' ?_ (fun ℓ => ?_) (fun ℓ => ?_) ?_ <;>
    simp only [Params.cob, Pi.one_apply, inv_one, Units.val_one, Matrix.mul_one, Matrix.one_mul]

/-- **Theorem 3.3 (ii), "form a group":** for any network, the changes of basis that preserve the
function at all parameters are a subgroup of the families of invertible matrices. -/
theorem exists_subgroup_eq_cobPreserving (A : Arch T d L) (S : Fin L → Matrix d d ℝ) :
    ∃ K : Subgroup (Fin (L + 1) → GL d ℝ),
      (K : Set (Fin (L + 1) → GL d ℝ)) = cobPreserving A S dIn dOut := by
  refine ⟨⟨⟨⟨cobPreserving A S dIn dOut, ?_⟩, ?_⟩, ?_⟩, rfl⟩
  · -- `G G'` at `θ` is `G'` at `θ.cob G G`, then `G` at `θ`
    intro G G' hG hG' θ x
    rw [← cob_cob_cgrp, hG' (θ.cob G G) x, hG θ x]
  · intro θ x
    rw [cob_one_cgrp]
  · -- `θ = (θ.cob G⁻¹ G⁻¹).cob G G`, and `G` preserves the function at `θ.cob G⁻¹ G⁻¹`
    intro G hG θ x
    have h1 : (θ.cob G⁻¹ G⁻¹).cob G G = θ := by
      rw [cob_cob_cgrp, inv_mul_cancel, cob_one_cgrp]
    conv_rhs => rw [← h1]
    exact (hG _ x).symm

/-! ### Skipless networks -/

/-- Without normalization every family of changes of basis preserves the function of a skipless
network (Proposition 3.2). -/
theorem cobPreserving_skipless (A : Arch T d L) (hA : A.χ = id) :
    cobPreserving A 0 dIn dOut = Set.univ :=
  Set.eq_univ_of_forall fun G θ x => eval_cob_skipless (θ := θ) (G := G) (x := x) hA

omit [Fintype T] in
/-- Helper: a matrix with invertible determinant is the value of an element of `GL d ℝ`. -/
private theorem exists_gl_of_isUnit_det_cgrp {g : Matrix d d ℝ} (hg : IsUnit g.det) :
    ∃ G : GL d ℝ, (G : Matrix d d ℝ) = g :=
  ⟨((Matrix.isUnit_iff_isUnit_det _).mpr hg).unit, IsUnit.unit_spec _⟩

omit [Fintype T] in
/-- Helper: an element of `GL d ℝ` has an invertible determinant. -/
private theorem isUnit_det_gl_cgrp (G : GL d ℝ) : IsUnit (G : Matrix d d ℝ).det :=
  (Matrix.isUnit_iff_isUnit_det _).mp G.isUnit

omit [Fintype T] in
/-- Helper: an orthogonal matrix has an invertible determinant. -/
private theorem isUnit_det_of_mem_orthogonalGroup_cgrp {Q : Matrix d d ℝ}
    (hQ : Q ∈ Matrix.orthogonalGroup d ℝ) : IsUnit Q.det :=
  Matrix.isUnit_det_of_right_inverse ((Matrix.mem_orthogonalGroup_iff d ℝ).mp hQ)

/-- **Theorem 3.3 (ii), skipless, no normalization:** the group has dimension `(L + 1) d²`. -/
theorem dimH_cobPreservingMat_skipless (A : Arch T d L) (hA : A.χ = id) :
    dimH (cobPreservingMat A 0 dIn dOut) = (((L + 1) * Fintype.card d ^ 2 : ℕ) : ℝ≥0∞) := by
  -- every family passes, and the families of invertible matrices are the image of `GL`
  have himg : cobPreservingMat A 0 dIn dOut
      = {m : Fin (L + 1) → Matrix d d ℝ | ∀ ℓ, IsUnit (m ℓ).det} := by
    rw [cobPreservingMat, cobPreserving_skipless A hA]
    ext m
    constructor
    · rintro ⟨G, -, rfl⟩ ℓ
      exact isUnit_det_gl_cgrp (G ℓ)
    · intro hm
      choose G hG using fun ℓ => exists_gl_of_isUnit_det_cgrp (hm ℓ)
      exact ⟨G, Set.mem_univ _, funext hG⟩
  rw [himg]
  exact dimH_setOf_forall_isUnit_det (L + 1)

/-- **Theorem 3.3 (ii), skipless, pre-RMSNorm, for any network for which only orthogonal changes
of basis pass** (the conclusion of Lemma A.4, as the hypothesis `hOnly`): the group has dimension
`(L + 1) d (d − 1)/2`. -/
theorem dimH_cobPreservingMat_skipless_rmsNorm (A : Arch T d L) (hA : A.χ = rmsNorm ε)
    (hOnly : ∀ G ∈ cobPreserving A 0 dIn dOut,
      ∀ ℓ, (G ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ) :
    dimH (cobPreservingMat A 0 dIn dOut)
      = (((L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2) : ℕ) : ℝ≥0∞) := by
  -- exactly the families of orthogonal matrices pass: `hOnly`, and pre-RMSNorm commutes with
  -- orthogonal matrices (`eval_cob_rmsNorm`)
  have himg : cobPreservingMat A 0 dIn dOut
      = {m : Fin (L + 1) → Matrix d d ℝ | ∀ ℓ, m ℓ ∈ Matrix.orthogonalGroup d ℝ} := by
    ext m
    constructor
    · rintro ⟨G, hG, rfl⟩ ℓ
      exact hOnly G hG ℓ
    · intro hm
      choose G hG using fun ℓ =>
        exists_gl_of_isUnit_det_cgrp (isUnit_det_of_mem_orthogonalGroup_cgrp (hm ℓ))
      refine ⟨G, fun θ x => ?_, funext hG⟩
      exact eval_cob_rmsNorm (θ := θ) (x := x) ε hA G fun ℓ => (hG ℓ).symm ▸ hm ℓ
  rw [himg]
  exact dimH_setOf_forall_mem_orthogonalGroup (L + 1)

/-- **Theorem 3.3 (ii), skipless, pre-RMSNorm (`ε > 0`), MLP blocks** with an activation that is
continuous, not even and not constant (tanh, GELU, ReLU, ReLU²) and at least one hidden unit per
block: the group has dimension `(L + 1) d (d − 1)/2`. -/
theorem dimH_cobPreservingMat_skipless_rmsNorm_mlp [Nonempty T] [Nonempty dIn] [Nonempty dOut]
    (hε : 0 < ε) (hσc : Continuous σ) (hne : ¬ ∀ z, σ (-z) = σ z) (hnc : ¬ ∀ z, σ z = σ 0)
    (hhid : ∀ ℓ, Nonempty (hid ℓ)) :
    dimH (cobPreservingMat (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) 0 dIn dOut)
      = (((L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2) : ℕ) : ℝ≥0∞) :=
  dimH_cobPreservingMat_skipless_rmsNorm _ rfl fun G hG =>
    orthogonal_of_eval_cob_skipless_rmsNorm_mlp hε hσc hne hnc hhid G hG

/-- **Theorem 3.3 (ii), skipless, pre-RMSNorm (`ε > 0`), gated blocks** whose gate is not
identically zero and satisfies `σ(z) = κ σ(κ z)` for all `z` only for `κ = 1` (the ReLU, SiLU and
GELU gates), with at least one hidden unit per block. -/
theorem dimH_cobPreservingMat_skipless_rmsNorm_gated [Nonempty T] [Nonempty dIn]
    [Nonempty dOut] (hε : 0 < ε) (hσ0 : ∃ z, σ z ≠ 0)
    (hκ : ∀ κ : ℝ, (∀ z, σ z = κ * σ (κ * z)) → κ = 1) (hhid : ∀ ℓ, Nonempty (hid ℓ)) :
    dimH (cobPreservingMat (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) 0 dIn dOut)
      = (((L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2) : ℕ) : ℝ≥0∞) :=
  dimH_cobPreservingMat_skipless_rmsNorm _ rfl fun G hG =>
    orthogonal_of_eval_cob_skipless_rmsNorm_gated hε hσ0 hκ hhid G hG

/-- **Theorem 3.3 (ii), skipless, pre-RMSNorm (`ε > 0`), attention blocks:** every token sees
some token and every block has a head of width at least `1`. -/
theorem dimH_cobPreservingMat_skipless_rmsNorm_attention [Nonempty T] [Nonempty dIn]
    [Nonempty dOut] (hε : 0 < ε) (hsees : ∀ t, ∃ s, sees t s)
    (hH : ∀ ℓ, Nonempty (H ℓ)) (hdh : ∀ ℓ, Nonempty (dh ℓ)) :
    dimH (cobPreservingMat (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) 0 dIn dOut)
      = (((L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2) : ℕ) : ℝ≥0∞) :=
  dimH_cobPreservingMat_skipless_rmsNorm _ rfl fun G hG =>
    orthogonal_of_eval_cob_skipless_rmsNorm_attention hε hsees hH hdh G hG

/-- **Theorem 3.3 (ii), skipless, pre-RMSNorm (`ε > 0`), attention blocks and MLP blocks in any
order** (the hypotheses of Lemma A.4 for them). -/
theorem dimH_cobPreservingMat_skipless_rmsNorm_attentionMlp [Nonempty T] [Nonempty dIn]
    [Nonempty dOut] (hε : 0 < ε) (hσc : Continuous σ) (hne : ¬ ∀ z, σ (-z) = σ z)
    (hnc : ¬ ∀ z, σ z = σ 0) (hsees : ∀ t, ∃ s, sees t s)
    (hblk : ∀ ℓ, (Nonempty (H ℓ) ∧ Nonempty (dh ℓ)) ∨ Nonempty (hid ℓ)) :
    dimH (cobPreservingMat
        (Arch.attentionMlp (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) 0 dIn dOut)
      = (((L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2) : ℕ) : ℝ≥0∞) :=
  dimH_cobPreservingMat_skipless_rmsNorm _ rfl fun G hG =>
    orthogonal_of_eval_cob_skipless_rmsNorm_attentionMlp hε hσc hne hnc hsees hblk G hG

/-- **Theorem 3.3 (ii), skipless, pre-RMSNorm (`ε > 0`), attention blocks and gated blocks in
any order** (the hypotheses of Lemma A.4 for them). -/
theorem dimH_cobPreservingMat_skipless_rmsNorm_attentionGated [Nonempty T] [Nonempty dIn]
    [Nonempty dOut] (hε : 0 < ε) (hσ0 : ∃ z, σ z ≠ 0)
    (hκ : ∀ κ : ℝ, (∀ z, σ z = κ * σ (κ * z)) → κ = 1) (hsees : ∀ t, ∃ s, sees t s)
    (hblk : ∀ ℓ, (Nonempty (H ℓ) ∧ Nonempty (dh ℓ)) ∨ Nonempty (hid ℓ)) :
    dimH (cobPreservingMat
        (Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) 0 dIn dOut)
      = (((L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2) : ℕ) : ℝ≥0∞) :=
  dimH_cobPreservingMat_skipless_rmsNorm _ rfl fun G hG =>
    orthogonal_of_eval_cob_skipless_rmsNorm_attentionGated hε hσ0 hκ hsees hblk G hG

/-! ### Residual networks -/

/-- **Theorem 3.3 (ii), residual, no normalization:** if every block is nonzero for some value of
its parameters, the changes of basis that preserve the function at all parameters are the
families with all `G_ℓ` equal, a group of dimension `d²`. -/
theorem dimH_cobPreservingMat_residual [Nonempty T] [Nonempty dIn] [Nonempty dOut]
    (A : Arch T d L) (hA : A.χ = id)
    (hne : ∀ ℓ, ∃ (x : Matrix T dIn ℝ) (E : Matrix dIn d ℝ) (W : Matrix d (A.r ℓ) ℝ),
      A.f ℓ (x * E * W) ≠ 0) :
    dimH (cobPreservingMat A 1 dIn dOut) = ((Fintype.card d ^ 2 : ℕ) : ℝ≥0∞) := by
  -- exactly the families with all `G_ℓ` equal pass (`eval_cob_residual_iff`)
  have himg : cobPreservingMat A 1 dIn dOut = {m : Fin (L + 1) → Matrix d d ℝ |
      ∃ g : Matrix d d ℝ, IsUnit g.det ∧ ∀ ℓ, m ℓ = g} := by
    ext m
    constructor
    · rintro ⟨G, hG, rfl⟩
      have hc := (eval_cob_residual_iff hA hne G).mp hG
      exact ⟨G 0, isUnit_det_gl_cgrp (G 0), fun ℓ => by
        show (G ℓ : Matrix d d ℝ) = G 0
        rw [hc ℓ]⟩
    · rintro ⟨g, hg, hm⟩
      obtain ⟨G₀, hG₀⟩ := exists_gl_of_isUnit_det_cgrp hg
      refine ⟨fun _ : Fin (L + 1) => G₀, (eval_cob_residual_iff hA hne _).mpr fun ℓ => rfl, ?_⟩
      funext ℓ
      rw [hm ℓ, ← hG₀]
  rw [himg]
  exact dimH_setOf_const_isUnit_det (Nat.succ_pos L)

/-- **Theorem 3.3 (ii), residual, pre-RMSNorm (`ε > 0`):** if every block is nonzero for some
value of its parameters, the changes of basis that preserve the function at all parameters are
the families with all `G_ℓ` equal to one orthogonal matrix, a group of dimension
`d (d − 1)/2`. -/
theorem dimH_cobPreservingMat_residual_rmsNorm [Nonempty T] [Nonempty dIn] [Nonempty dOut]
    (A : Arch T d L) (hε : 0 < ε) (hA : A.χ = rmsNorm ε)
    (hne : ∀ ℓ, ∃ (x : Matrix T dIn ℝ) (E : Matrix dIn d ℝ) (W : Matrix d (A.r ℓ) ℝ),
      A.f ℓ (rmsNorm ε (x * E) * W) ≠ 0) :
    dimH (cobPreservingMat A 1 dIn dOut)
      = ((Fintype.card d * (Fintype.card d - 1) / 2 : ℕ) : ℝ≥0∞) := by
  -- exactly the families with all `G_ℓ` equal to one orthogonal matrix pass
  -- (`eval_cob_residual_rmsNorm_iff`)
  have himg : cobPreservingMat A 1 dIn dOut = {m : Fin (L + 1) → Matrix d d ℝ |
      ∃ Q : Matrix d d ℝ, Q ∈ Matrix.orthogonalGroup d ℝ ∧ ∀ ℓ, m ℓ = Q} := by
    ext m
    constructor
    · rintro ⟨G, hG, rfl⟩
      obtain ⟨hc, hQ⟩ := (eval_cob_residual_rmsNorm_iff hε hA hne G).mp hG
      exact ⟨G 0, hQ, fun ℓ => by
        show (G ℓ : Matrix d d ℝ) = G 0
        rw [hc ℓ]⟩
    · rintro ⟨Q, hQ, hm⟩
      obtain ⟨G₀, hG₀⟩ :=
        exists_gl_of_isUnit_det_cgrp (isUnit_det_of_mem_orthogonalGroup_cgrp hQ)
      refine ⟨fun _ : Fin (L + 1) => G₀,
        (eval_cob_residual_rmsNorm_iff hε hA hne _).mpr ⟨fun ℓ => rfl, hG₀ ▸ hQ⟩, ?_⟩
      funext ℓ
      rw [hm ℓ, ← hG₀]
  rw [himg]
  exact dimH_setOf_const_mem_orthogonalGroup (Nat.succ_pos L)

end Skips
