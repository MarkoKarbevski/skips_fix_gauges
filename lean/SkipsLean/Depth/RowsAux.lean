import SkipsLean.Depth.StepTanh

/-!
# Three facts about rows, for the step on the path

Paper (dimension paper): Appendix D.6, proof of Lemma D.18 (the step for `tanh` on the path).

* "By (S2), for integers `κ_j` that are not all zero, `∑_j κ_j ξ c_j = ξ ∑_j κ_j c_j` vanishes only
  for `ξ` in a hyperplane. Let `P' ⊂ P` be the dense set of the `ξ` for which `ξ c_1, …, ξ c_q` are
  linearly independent over `ℚ`."
* "A matrix for which every row of an open set is an eigenvector is a multiple of the identity."
* A matrix `M` with `ξ M = 0` for every row `ξ` of a nonempty open set is `0` (used for
  `ξ (Y_k W + η_W) = 0`).

Rows are functions `d → ℝ`, and `ξ M` is `ξ ᵥ* M`.
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise

variable {d : Type*} [Fintype d] [DecidableEq d]

omit [DecidableEq d] in
/-- **The set `P'` is dense:** if the columns `c_j` of `W` are linearly independent over `ℚ`, then
for a dense set of rows `ξ` the numbers `ξ c_1, …, ξ c_q` are linearly independent over `ℚ`. -/
theorem dense_setOf_linearIndependent_vecMul {q : Type*} [Fintype q] (W : Matrix d q ℝ)
    (hW : LinearIndependent ℚ (fun j : q => fun i : d => W i j)) :
    Dense {ξ : d → ℝ | LinearIndependent ℚ (fun j : q => (ξ ᵥ* W) j)} := by
  classical
  -- the dense set of one-row matrices `Ξ`, and its image under `Ξ ↦ Ξ ()` (the row)
  have hD := dense_setOf_linearIndependent_mul (T := Unit) W hW
  have hr : Continuous fun Ξ : Matrix Unit d ℝ => Ξ () := continuous_apply ()
  have hs : Function.Surjective fun Ξ : Matrix Unit d ℝ => Ξ () :=
    fun ξ => ⟨Matrix.of fun _ => ξ, rfl⟩
  have hsurj : DenseRange fun Ξ : Matrix Unit d ℝ => Ξ () := hs.denseRange
  refine (hsurj.dense_image hr hD).mono ?_
  rintro _ ⟨Ξ, hΞ, rfl⟩
  -- the row `ξ W` is the family `(Ξ W)_{() j}`, reindexed along `j ↦ ((), j)`
  have hc := hΞ.comp (fun j : q => ((), j)) (fun a b h => (Prod.mk.inj h).2)
  exact hc

omit [Fintype d] [DecidableEq d] in
/-- Helper: a point `ξ₀` of an open set `U` and a direction `y` give a `δ ≠ 0` with
`ξ₀ ± δ y ∈ U`. -/
private theorem exists_line_mem_aux (U : Set (d → ℝ)) (hU : IsOpen U) {ξ₀ : d → ℝ}
    (h0 : ξ₀ ∈ U) (y : d → ℝ) : ∃ δ : ℝ, δ ≠ 0 ∧ ξ₀ + δ • y ∈ U ∧ ξ₀ - δ • y ∈ U := by
  have hc : Continuous fun s : ℝ => ξ₀ + s • y := by fun_prop
  have hn : (fun s : ℝ => ξ₀ + s • y) ⁻¹' U ∈ nhds (0 : ℝ) :=
    hc.continuousAt.preimage_mem_nhds (by simpa using hU.mem_nhds h0)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hn
  have h1 : ε / 2 ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (by positivity)]
    linarith
  have h2 : -(ε / 2) ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_neg, abs_of_pos (by positivity)]
    linarith
  refine ⟨ε / 2, by positivity, hball h1, ?_⟩
  have e := hball h2
  simpa only [Set.mem_preimage, neg_smul, ← sub_eq_add_neg] using e

/-- **"A matrix for which every row of an open set is an eigenvector is a multiple of the
identity":** if `ξ S` is parallel to `ξ` (all `2 × 2` minors of the two rows vanish) for every `ξ`
in a nonempty open set, then `S = c I`. -/
theorem exists_eq_smul_one_of_vecMul_parallel (S : Matrix d d ℝ) (U : Set (d → ℝ))
    (hU : IsOpen U) (hne : U.Nonempty)
    (h : ∀ ξ ∈ U, ∀ i j, (ξ ᵥ* S) i * ξ j = (ξ ᵥ* S) j * ξ i) :
    ∃ c : ℝ, S = c • (1 : Matrix d d ℝ) := by
  obtain ⟨ξ₀, h0⟩ := hne
  -- the quadratic `P(y) = (yS)_i y_j - (yS)_j y_i` vanishes everywhere:
  -- `P(ξ₀ + δy) + P(ξ₀ - δy) - 2 P(ξ₀) = 2 δ² P(y)`
  have hP : ∀ y : d → ℝ, ∀ i j, (y ᵥ* S) i * y j = (y ᵥ* S) j * y i := by
    intro y i j
    obtain ⟨δ, hδ, h1, h2⟩ := exists_line_mem_aux U hU h0 y
    have e1 := h _ h1 i j
    have e2 := h _ h2 i j
    have e0 := h _ h0 i j
    simp only [Matrix.add_vecMul, Matrix.sub_vecMul, Matrix.smul_vecMul, Pi.add_apply,
      Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e1 e2
    have key : δ ^ 2 * ((y ᵥ* S) i * y j - (y ᵥ* S) j * y i) = 0 := by
      linear_combination (e1 + e2 - 2 * e0) / 2
    have := (mul_eq_zero.1 key).resolve_left (pow_ne_zero 2 hδ)
    linarith
  -- at `y = e_a`: `S` is diagonal
  have hdiag : ∀ a i, i ≠ a → S a i = 0 := by
    intro a i hi
    have e := hP (Pi.single a 1) i a
    simpa [Matrix.single_one_vecMul, Pi.single_eq_of_ne hi] using e
  -- at `y = e_a + e_b`: the diagonal entries are equal
  have heq : ∀ a b, S a a = S b b := by
    intro a b
    rcases eq_or_ne a b with rfl | hab
    · rfl
    have e := hP (Pi.single a 1 + Pi.single b 1) a b
    simp [Matrix.add_vecMul, Pi.single_eq_of_ne hab,
      Pi.single_eq_of_ne hab.symm] at e
    rw [hdiag b a hab, hdiag a b hab.symm] at e
    linarith
  rcases isEmpty_or_nonempty d with hd | ⟨⟨a₀⟩⟩
  · exact ⟨0, Subsingleton.elim _ _⟩
  refine ⟨S a₀ a₀, ?_⟩
  ext a b
  rcases eq_or_ne a b with rfl | hab
  · simp [heq a a₀]
  · simp [Matrix.one_apply_ne hab, hdiag a b hab.symm]

omit [DecidableEq d] in
/-- A matrix `M` with `ξ M = 0` for every row `ξ` of a nonempty open set is `0`. -/
theorem eq_zero_of_vecMul_eq_zero_of_isOpen {q : Type*} [Fintype q] (M : Matrix d q ℝ)
    (U : Set (d → ℝ)) (hU : IsOpen U) (hne : U.Nonempty) (h : ∀ ξ ∈ U, ξ ᵥ* M = 0) : M = 0 := by
  classical
  obtain ⟨ξ₀, h0⟩ := hne
  -- `(ξ₀ + δ y) M = 0` and `ξ₀ M = 0` give `y M = 0` for every `y`
  have hy : ∀ y : d → ℝ, y ᵥ* M = 0 := by
    intro y
    obtain ⟨δ, hδ, h1, -⟩ := exists_line_mem_aux U hU h0 y
    have e := h _ h1
    rw [Matrix.add_vecMul, Matrix.smul_vecMul, h ξ₀ h0, zero_add] at e
    exact (smul_eq_zero.1 e).resolve_left hδ
  -- at `y = e_a`: row `a` of `M` is `0`
  ext a j
  have e := congrFun (hy (Pi.single a 1)) j
  simpa [Matrix.single_one_vecMul] using e

end Skips
