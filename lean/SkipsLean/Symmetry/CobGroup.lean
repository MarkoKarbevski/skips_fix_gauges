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

/-- **Theorem 3.3 (ii), "form a group":** for any network, the changes of basis that preserve the
function at all parameters are a subgroup of the families of invertible matrices. -/
theorem exists_subgroup_eq_cobPreserving (A : Arch T d L) (S : Fin L → Matrix d d ℝ) :
    ∃ K : Subgroup (Fin (L + 1) → GL d ℝ),
      (K : Set (Fin (L + 1) → GL d ℝ)) = cobPreserving A S dIn dOut := by
  sorry

/-! ### Skipless networks -/

/-- Without normalization every family of changes of basis preserves the function of a skipless
network (Proposition 3.2). -/
theorem cobPreserving_skipless (A : Arch T d L) (hA : A.χ = id) :
    cobPreserving A 0 dIn dOut = Set.univ := by
  sorry

/-- **Theorem 3.3 (ii), skipless, no normalization:** the group has dimension `(L + 1) d²`. -/
theorem dimH_cobPreservingMat_skipless (A : Arch T d L) (hA : A.χ = id) :
    dimH (cobPreservingMat A 0 dIn dOut) = (((L + 1) * Fintype.card d ^ 2 : ℕ) : ℝ≥0∞) := by
  sorry

/-- **Theorem 3.3 (ii), skipless, pre-RMSNorm, for any network for which only orthogonal changes
of basis pass** (the conclusion of Lemma A.4, as the hypothesis `hOnly`): the group has dimension
`(L + 1) d (d − 1)/2`. -/
theorem dimH_cobPreservingMat_skipless_rmsNorm (A : Arch T d L) (hA : A.χ = rmsNorm ε)
    (hOnly : ∀ G ∈ cobPreserving A 0 dIn dOut,
      ∀ ℓ, (G ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ) :
    dimH (cobPreservingMat A 0 dIn dOut)
      = (((L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2) : ℕ) : ℝ≥0∞) := by
  sorry

/-- **Theorem 3.3 (ii), skipless, pre-RMSNorm (`ε > 0`), MLP blocks** with an activation that is
continuous, not even and not constant (tanh, GELU, ReLU, ReLU²) and at least one hidden unit per
block: the group has dimension `(L + 1) d (d − 1)/2`. -/
theorem dimH_cobPreservingMat_skipless_rmsNorm_mlp [Nonempty T] [Nonempty dIn] [Nonempty dOut]
    (hε : 0 < ε) (hσc : Continuous σ) (hne : ¬ ∀ z, σ (-z) = σ z) (hnc : ¬ ∀ z, σ z = σ 0)
    (hhid : ∀ ℓ, Nonempty (hid ℓ)) :
    dimH (cobPreservingMat (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) 0 dIn dOut)
      = (((L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2) : ℕ) : ℝ≥0∞) := by
  sorry

/-- **Theorem 3.3 (ii), skipless, pre-RMSNorm (`ε > 0`), gated blocks** whose gate is not
identically zero and satisfies `σ(z) = κ σ(κ z)` for all `z` only for `κ = 1` (the ReLU, SiLU and
GELU gates), with at least one hidden unit per block. -/
theorem dimH_cobPreservingMat_skipless_rmsNorm_gated [Nonempty T] [Nonempty dIn]
    [Nonempty dOut] (hε : 0 < ε) (hσ0 : ∃ z, σ z ≠ 0)
    (hκ : ∀ κ : ℝ, (∀ z, σ z = κ * σ (κ * z)) → κ = 1) (hhid : ∀ ℓ, Nonempty (hid ℓ)) :
    dimH (cobPreservingMat (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) 0 dIn dOut)
      = (((L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2) : ℕ) : ℝ≥0∞) := by
  sorry

/-- **Theorem 3.3 (ii), skipless, pre-RMSNorm (`ε > 0`), attention blocks:** every token sees
some token and every block has a head of width at least `1`. -/
theorem dimH_cobPreservingMat_skipless_rmsNorm_attention [Nonempty T] [Nonempty dIn]
    [Nonempty dOut] (hε : 0 < ε) (hsees : ∀ t, ∃ s, sees t s)
    (hH : ∀ ℓ, Nonempty (H ℓ)) (hdh : ∀ ℓ, Nonempty (dh ℓ)) :
    dimH (cobPreservingMat (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) 0 dIn dOut)
      = (((L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2) : ℕ) : ℝ≥0∞) := by
  sorry

/-- **Theorem 3.3 (ii), skipless, pre-RMSNorm (`ε > 0`), attention blocks and MLP blocks in any
order** (the hypotheses of Lemma A.4 for them). -/
theorem dimH_cobPreservingMat_skipless_rmsNorm_attentionMlp [Nonempty T] [Nonempty dIn]
    [Nonempty dOut] (hε : 0 < ε) (hσc : Continuous σ) (hne : ¬ ∀ z, σ (-z) = σ z)
    (hnc : ¬ ∀ z, σ z = σ 0) (hsees : ∀ t, ∃ s, sees t s)
    (hblk : ∀ ℓ, (Nonempty (H ℓ) ∧ Nonempty (dh ℓ)) ∨ Nonempty (hid ℓ)) :
    dimH (cobPreservingMat
        (Arch.attentionMlp (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) 0 dIn dOut)
      = (((L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2) : ℕ) : ℝ≥0∞) := by
  sorry

/-- **Theorem 3.3 (ii), skipless, pre-RMSNorm (`ε > 0`), attention blocks and gated blocks in
any order** (the hypotheses of Lemma A.4 for them). -/
theorem dimH_cobPreservingMat_skipless_rmsNorm_attentionGated [Nonempty T] [Nonempty dIn]
    [Nonempty dOut] (hε : 0 < ε) (hσ0 : ∃ z, σ z ≠ 0)
    (hκ : ∀ κ : ℝ, (∀ z, σ z = κ * σ (κ * z)) → κ = 1) (hsees : ∀ t, ∃ s, sees t s)
    (hblk : ∀ ℓ, (Nonempty (H ℓ) ∧ Nonempty (dh ℓ)) ∨ Nonempty (hid ℓ)) :
    dimH (cobPreservingMat
        (Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) 0 dIn dOut)
      = (((L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2) : ℕ) : ℝ≥0∞) := by
  sorry

/-! ### Residual networks -/

/-- **Theorem 3.3 (ii), residual, no normalization:** if every block is nonzero for some value of
its parameters, the changes of basis that preserve the function at all parameters are the
families with all `G_ℓ` equal, a group of dimension `d²`. -/
theorem dimH_cobPreservingMat_residual [Nonempty T] [Nonempty dIn] [Nonempty dOut]
    (A : Arch T d L) (hA : A.χ = id)
    (hne : ∀ ℓ, ∃ (x : Matrix T dIn ℝ) (E : Matrix dIn d ℝ) (W : Matrix d (A.r ℓ) ℝ),
      A.f ℓ (x * E * W) ≠ 0) :
    dimH (cobPreservingMat A 1 dIn dOut) = ((Fintype.card d ^ 2 : ℕ) : ℝ≥0∞) := by
  sorry

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
  sorry

end Skips
