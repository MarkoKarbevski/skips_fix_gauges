import SkipsLean.OneBlock.UnitsParallelAt

/-!
# Hidden units in general position, and what follows for a ReLU block of width at least `d`

Paper (skips paper), proof of Theorem B.1 (iv), "The skipless network: equality": "The network is
defined on the set `Ω` of inputs at which some unit is active: for generic parameters `h_1 ≠ 0`
there, and `h_1 = 0` elsewhere. Indeed, let `S` be the set of units active at `x`, and let `w_i`
be the columns of `W_read`. If `|S| < d_model`, the rows `a_i`, `i ∈ S`, are linearly independent.
If `|S| ≥ d_model` and `k = 1`, `h_1 = x E ∑_{i∈S} w_i a_i`, and this `d_model × d_model` matrix
is invertible." Then "For generic parameters and `x_0` in an open dense set of such points,
`h_1(x_0)` is not parallel to `a_i`", "for generic parameters two entries `h_a` and `h_b` of `h_1`
have no common factor", and "the `c_i` are pairwise non-collinear".

Here the conditions on `W_read` (columns `w_i`) and `W_write` (rows `a_i`) under which these hold
for a ReLU block (`k = 1`), as one definition, `UnitsGeneralPosition W_read W_write`:

1. the columns `w_i` are pairwise non-collinear (also not opposite);
2. any at most `d` of the rows `a_i` are linearly independent;
3. for every set `S` of at least `d` units the `d × d` matrix `M_S = ∑_{i∈S} w_i a_i` is
   invertible;
4. for every such `S` and every unit `i` outside it, `(a_i M_S⁻¹) · w_i ≠ 0` (then no nonzero
   point `u` of the hyperplane `u · w_i = 0` has `u M_S` parallel to `a_i`; the paper's "`x_0` in
   an open dense set", which for `d_model = 2` is a condition on the parameters).

All four hold at almost every parameter of a block of width at least `d ≥ 2`
(`OneBlock/UnitsGeneralPositionGeneric.lean`). From them, for `E` of rank `d`, `d ≥ 2` and at
least `d` units: the hypotheses of `relu_unitsParallelAt_of_generic` at the columns of
`E W_read` and the rows of `W_write`, hence `UnitsParallelAt`; a nonempty open set of outputs of
the block at rows off the kinks; and the ranks of `W_read` and `W_write`.
-/

namespace Skips

open Matrix

/-- **Hidden units in general position** (the conditions "for generic parameters" of the proof
of Theorem B.1 (iv) of the skips paper, "The skipless network: equality", for `k = 1`): the
columns `w_i` of `W_read` are pairwise non-collinear; any at most `d` rows `a_i` of `W_write` are
linearly independent; for every set `S` of at least `d` units, `M_S = ∑_{i∈S} w_i a_i` is
invertible, and `(a_i M_S⁻¹) · w_i ≠ 0` for every unit `i` outside `S`. -/
def UnitsGeneralPosition {d q : Type*} [Fintype d] [DecidableEq d] (Wr : Matrix d q ℝ)
    (Ww : Matrix q d ℝ) : Prop :=
  (∀ i j, i ≠ j → ∀ r : ℝ, Wrᵀ i ≠ r • Wrᵀ j) ∧
  (∀ S : Finset q, S.card ≤ Fintype.card d → LinearIndependent ℝ fun i : S => Ww i) ∧
  (∀ S : Finset q, Fintype.card d ≤ S.card →
    IsUnit (∑ i ∈ S, Matrix.vecMulVec (Wrᵀ i) (Ww i)).det) ∧
  ∀ (i : q) (S : Finset q), i ∉ S → Fintype.card d ≤ S.card →
    (Ww i ᵥ* (∑ j ∈ S, Matrix.vecMulVec (Wrᵀ j) (Ww j))⁻¹) ⬝ᵥ Wrᵀ i ≠ 0

variable {dIn d q : Type*} [Fintype dIn] [Fintype d] [DecidableEq d] [Fintype q]

/-- **In general position, `W_read` and `W_write` have rank `d` and no column of `W_read` is
zero** (at least `d ≥ 2` units): `W_read W_write = M_S` for `S` the set of all units. -/
theorem rank_of_unitsGeneralPosition {Wr : Matrix d q ℝ} {Ww : Matrix q d ℝ}
    (hd : 2 ≤ Fintype.card d) (hq : Fintype.card d ≤ Fintype.card q)
    (hG : UnitsGeneralPosition Wr Ww) :
    Wr.rank = Fintype.card d ∧ Ww.rank = Fintype.card d ∧ ∀ i, (fun a => Wr a i) ≠ 0 := by
  sorry

/-- **"The kinks stay" and "One scale" for a ReLU block of width at least `d` in general
position:** for `E` of rank `d ≥ 2` and at least `d` units in general position, `UnitsParallelAt`
holds at the columns `c_i` of `E W_read` and the rows `a_i` of `W_write`. -/
theorem relu_unitsParallelAt_of_unitsGeneralPosition (E : Matrix dIn d ℝ) {Wr : Matrix d q ℝ}
    {Ww : Matrix q d ℝ} (hd : 2 ≤ Fintype.card d) (hq : Fintype.card d ≤ Fintype.card q)
    (hE : E.rank = Fintype.card d) (hG : UnitsGeneralPosition Wr Ww) :
    UnitsParallelAt relu reluDeriv 1 (fun i => (E * Wr)ᵀ i) (fun i => Ww i) := by
  sorry

/-- **"`h_1` takes all values in an open set" for a ReLU block of width at least `d` in general
position:** for `E` of rank `d ≥ 2` and at least `d` units in general position, the outputs
`∑_i max(x c_i, 0) a_i` at rows `x` off the kinks fill a nonempty open set (on a region with at
least `d` active units the output is `x E M_S` with `M_S` invertible). -/
theorem exists_open_relu_of_unitsGeneralPosition (E : Matrix dIn d ℝ) {Wr : Matrix d q ℝ}
    {Ww : Matrix q d ℝ} (hd : 2 ≤ Fintype.card d) (hq : Fintype.card d ≤ Fintype.card q)
    (hE : E.rank = Fintype.card d) (hG : UnitsGeneralPosition Wr Ww) :
    ∃ O : Set (d → ℝ), IsOpen O ∧ O.Nonempty ∧ ∀ v ∈ O, ∃ x : dIn → ℝ,
      (∀ i, x ⬝ᵥ (E * Wr)ᵀ i ≠ 0) ∧ ∑ i, relu (x ⬝ᵥ (E * Wr)ᵀ i) • Ww i = v := by
  sorry

end Skips
