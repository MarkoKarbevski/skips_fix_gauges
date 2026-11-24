import SkipsLean.Absorb.GatedBiasesCells

/-!
# Gated blocks with biases: one hyperplane at a time, and the count of Lemma C.8

Paper (absorb paper), Appendix C.2, proof of Lemma C.8 (Gated blocks with biases), after the
expansion along rays: "One hyperplane at a time. Near a point of `H` that lies on no other
hyperplane, the terms of the other hyperplanes are smooth. […] The terms of `H` are then `x Δ_H`,
with `Δ_H = G_− − ν a_− = G_+ + ν a_+`, and the second identity becomes `M = ∑_H Δ_H + Z`. As
`g = ±η ν` on side `±`, `G_± ± ν a_±` is the sum of the matrices `Δ_j` over the units of `B_{θ′}`
on side `±`, minus the same sum over the units of `B_θ`. […] So `A_+ + A_− = 0`.
Counting. Orient the hyperplane `H_i` of unit `i` of `B_θ` so that unit `i` lies on side `+`; no
other unit of `B_θ` lies on `H_i`. Let `J^±` be the sets of units of `B_{θ′}` on side `±` of `H_i`.
If both were empty, `A_+ + A_−` would be `−η_i v_i ŵ_i`, where `g_i = η_i ν`, which does not
vanish; so `H_i` carries `|J^+| + |J^−| − 1 ≥ 0` extra units. If `J^+` is empty, `Δ_{H_i} = −Δ_i`.
Otherwise `Δ_{H_i}` is the sum of the `Δ_j` over `J^−`, at most `|J^−| ≤ |J^+| + |J^−| − 1`
matrices of rank one. A hyperplane of no unit of `B_θ` carries `|J^+| + |J^−|` units of `B_{θ′}`,
with `J^±` defined in the same way, and `Δ_H` is a sum of at most that many matrices of rank one.
Each unit of `B_{θ′}` with gate read `0` adds one matrix of rank one to `Z`, and `B_θ` has no such
unit. With `S` the units `i` for which `J^+` is empty, `M + ∑_{i∈S} Δ_i` is therefore a sum of at
most `n` matrices of rank one."

Here this part of the proof is stated from the two identities of `Absorb/GatedBiasesCells.lean`
(`M + Λ_θ(x) = Λ_{θ′}(x)` and `Q_θ(x, ·) = Q_{θ′}(x, ·)` at every `x` off the hyperplanes). Two
inputs on the two sides of the hyperplane of a unit `i`, close to a point of it that lies on no
other hyperplane, give the two facts of "One hyperplane at a time": the sums of the `Δ` over the
units on the two sides agree, and the units of `B_{θ′}` on the hyperplane carry `v_i ŵ_i ≠ 0`.

"`M + ∑_{i∈S} Δ_i` is a sum of at most `n` matrices of rank one", with `n` the number of units
that `B_{θ′}` has more than `B_θ`, is stated as: its rank plus the number of units of `B_θ` is at
most the number of units of `B_{θ′}` (so `B_{θ′}` has at least as many units as `B_θ`).
-/

namespace Skips

open Matrix

variable {p q m m' : Type*} [Fintype p] [Fintype q] [Fintype m] [Fintype m']

/-- **Proof of Lemma C.8 of the absorb paper, "One hyperplane at a time" and "Counting":** let the
gate reads of `B_θ` be nonzero and pairwise non-collinear, and its value reads and writes nonzero.
If the two identities of the expansion along rays hold at every `x` off the hyperplanes of both
blocks, then for some set `S` of units of `B_θ` the rank of `M + ∑_{i∈S} Δ_i` is at most the number
of units that `B_{θ′}` has more than `B_θ`. -/
theorem exists_rank_add_card_le_of_gateLinear_gateQuadratic (σ : ℝ → ℝ)
    (Wg : Matrix p m ℝ) (bg : m → ℝ) (Wv : Matrix p m ℝ) (bv : m → ℝ) (Ww : Matrix m q ℝ)
    (Wg' : Matrix p m' ℝ) (bg' : m' → ℝ) (Wv' : Matrix p m' ℝ) (bv' : m' → ℝ)
    (Ww' : Matrix m' q ℝ) (M : Matrix p q ℝ)
    (hg : ∀ j, Wgᵀ j ≠ 0) (hcol : ∀ i j, i ≠ j → ∀ r : ℝ, Wgᵀ i ≠ r • Wgᵀ j)
    (hv : ∀ j, Wvᵀ j ≠ 0) (hw : ∀ j, Ww j ≠ 0)
    (hcell : ∀ x : p → ℝ, (∀ j, (x ᵥ* Wg) j ≠ 0) → (∀ j, (x ᵥ* Wg') j = 0 → Wg'ᵀ j = 0) →
      M + gateLinear σ Wg bg Wv bv Ww x = gateLinear σ Wg' bg' Wv' bv' Ww' x ∧
        ∀ y : p → ℝ, gateQuadratic Wg Wv Ww x y = gateQuadratic Wg' Wv' Ww' x y) :
    ∃ S : Finset m, (M + ∑ i ∈ S, gateDelta Wg bg Wv bv Ww i).rank + Fintype.card m
      ≤ Fintype.card m' := by
  sorry

end Skips
