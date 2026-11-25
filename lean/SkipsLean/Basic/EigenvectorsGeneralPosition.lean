import SkipsLean.Imports

/-!
# A matrix with more than `d` eigenvectors in general position is a multiple of the identity

A fact of linear algebra, stated once for the two forms of Lemma A.18 of the skips paper for
ReGLU blocks with the readout (`Dimension/UpperBoundReadoutInside.lean`,
`Symmetry/LocallyFreeReadout.lean`). The proof of the lemma says: "each read, of rank `d_model`
and with generic columns, then forces `G_{ℓ−1} = I` and the remaining scales to be 1". For a
ReGLU block the change of basis `G_{ℓ−1}` multiplies every gate column and every value column of
the read by a number of its own, so every column is an eigenvector of `G_{ℓ−1}`; "generic
columns" is used in this form: more than `d` vectors, any `d` of them linearly independent.

Proof: `d` of the vectors form a basis, and one more vector has all its coordinates in this basis
nonzero (else it and `d − 1` vectors of the basis would be dependent); comparing `M v` in the
basis, all eigenvalues are equal.
-/

namespace Skips

open Matrix

/-- If more than `d` vectors of `ℝ^d`, any `d` of which are linearly independent, are all
eigenvectors of a matrix `M`, then `M` is a multiple of the identity. -/
theorem eq_smul_one_of_eigenvectors_generalPosition {d q : Type*} [Fintype d] [DecidableEq d]
    [Fintype q] (v : q → d → ℝ)
    (hgp : ∀ S : Finset q, S.card ≤ Fintype.card d → LinearIndependent ℝ fun j : S => v j)
    (hq : Fintype.card d < Fintype.card q) (M : Matrix d d ℝ)
    (hM : ∀ j, ∃ μ : ℝ, M *ᵥ v j = μ • v j) :
    ∃ μ : ℝ, M = μ • (1 : Matrix d d ℝ) := by
  classical
  choose μ hμ using hM
  -- a vector `v j₀`, and `d` other vectors `v j`, `j ∈ S₀`
  obtain ⟨j₀⟩ : Nonempty q := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨S₀, hS₀, hcard⟩ : ∃ S₀ ⊆ Finset.univ.erase j₀, S₀.card = Fintype.card d := by
    refine Finset.exists_subset_card_eq ?_
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
    omega
  have hj₀ : j₀ ∉ S₀ := fun h => by simpa using hS₀ h
  -- the `d` vectors `v j`, `j ∈ S₀`, are independent, so they form a basis `b` of `ℝ^d`
  have hli : LinearIndependent ℝ fun j : S₀ => v j := hgp S₀ hcard.le
  let b := basisOfLinearIndependentOfCardEqFinrank' (K := ℝ) (fun j : S₀ => v j) hli
    (by rw [Fintype.card_coe, hcard, Module.finrank_fintype_fun_eq_card])
  have hb : ∀ j, b j = v j := fun j => by simp [b]
  -- the coordinates of `v j₀` in this basis: `v j₀ = ∑ c_j v_j`
  obtain ⟨c, hc⟩ : ∃ c : S₀ → ℝ, ∑ j, c j • v j = v j₀ :=
    ⟨b.repr (v j₀), by simpa only [hb] using b.sum_repr (v j₀)⟩
  -- no coordinate `c_{j₁}` is zero: else `v j₀` and the `v j`, `j ∈ S₀ \ {j₁}`, are `d`
  -- dependent vectors
  have hc0 : ∀ j₁, c j₁ ≠ 0 := by
    intro j₁ h1
    have hS : (insert j₀ (S₀.erase j₁)).card ≤ Fintype.card d := by
      have h2 := Finset.card_insert_le j₀ (S₀.erase j₁)
      have h3 := Finset.card_erase_of_mem j₁.2
      have h4 : 0 < S₀.card := Finset.card_pos.2 ⟨_, j₁.2⟩
      omega
    have hli' : LinearIndepOn ℝ v (↑(insert j₀ (S₀.erase j₁)) : Set q) := hgp _ hS
    rw [Finset.coe_insert] at hli'
    refine ((linearIndepOn_insert (by simp [hj₀])).1 hli').2 ?_
    rw [← hc]
    refine sum_mem fun j _ => ?_
    by_cases hj : j = j₁
    · rw [hj, h1, zero_smul]
      exact zero_mem _
    · have hmem : (j : q) ∈ (↑(S₀.erase j₁) : Set q) :=
        Finset.mem_coe.2 (Finset.mem_erase.2 ⟨fun h => hj (Subtype.ext h), j.2⟩)
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_image_of_mem v hmem))
  -- `M v j₀ = μ_{j₀} v j₀` in the basis: `c_j μ_j = c_j μ_{j₀}`, so `μ_j = μ_{j₀}`
  have hμeq : ∀ j : S₀, μ j = μ j₀ := by
    have e1 : M *ᵥ v j₀ = ∑ j : S₀, (c j * μ j) • v j := by
      rw [← hc, Matrix.mulVec_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Matrix.mulVec_smul, hμ, smul_smul]
    have e2 : μ j₀ • v j₀ = ∑ j : S₀, (c j * μ j₀) • v j := by
      rw [← hc, Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_smul, mul_comm]
    have h0 : ∑ j : S₀, (c j * (μ j - μ j₀)) • v j = 0 := by
      simp only [mul_sub, sub_smul, Finset.sum_sub_distrib]
      rw [← e1, ← e2, hμ, sub_self]
    intro j
    have h5 := Fintype.linearIndependent_iff.1 hli _ h0 j
    exact sub_eq_zero.1 ((mul_eq_zero.1 h5).resolve_left (hc0 j))
  -- so `M` and `μ_{j₀} 1` agree on the basis
  refine ⟨μ j₀, Matrix.toLin'.injective (b.ext fun j => ?_)⟩
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, hb, hμ, hμeq, Matrix.smul_mulVec,
    Matrix.one_mulVec]

end Skips
