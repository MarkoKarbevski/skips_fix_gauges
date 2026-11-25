import SkipsLean.OneBlock.UnitsParallelAtSq
import SkipsLean.OneBlock.UnitsGeneralPosition

/-!
# ReLU² units in general position: the conditions on the weights

Paper (skips paper), proof of Theorem B.1 (iv), "The skipless network: equality. Let
`σ(z) = max(z, 0)^k` with `k = 1` or `2`, and write `h_1 = B(xE) = ∑_i σ(x c_i) a_i`, with `c_i`
the columns of `C = E W_read` and `a_i` the rows of `W_write`. The network is defined on the set
`Ω` of inputs at which some unit is active: for generic parameters `h_1 ≠ 0` there, and `h_1 = 0`
elsewhere. […] If `|S| ≥ d_model` and `k = 2`, the entries of `h_1` are `d_model` quadratic forms
in `xE`. A common zero other than `0`, real or complex, makes their resultant vanish." Then
"For generic parameters and `x_0` in an open dense set of such points, `h_1(x_0)` is not parallel
to `a_i`", "for generic parameters two entries `h_a` and `h_b` of `h_1` have no common factor",
and, in the case `ε = 0` of part (iii), "since `h_1` takes all values in an open set".

Here the conditions on `W_read` (columns `w_i`) and `W_write` (rows `a_i`) under which these hold
for a ReLU² block (`k = 2`), as one definition, `UnitsGeneralPositionSq W_read W_write`:

1. the columns `w_i` are pairwise non-collinear (also not opposite);
2. no row `a_i` is zero;
3. `∑_i max(u w_i, 0)² a_i ≠ 0` at every `u` at which a unit is active (for real `u`; the
   paper's resultant also excludes complex zeros, which the proof does not need);
4. for every unit `i` a point `u_0` of its hyperplane, on no other hyperplane, at which
   `∑_j max(u_0 w_j, 0)² a_j` is not a multiple of `a_i`;
5. for every set `S` of at least two units a line `t ↦ u + t v` and two entries `e`, `f` for
   which the polynomials `t ↦ ∑_{i∈S} ((u + t v) w_i)² a_{i e}` and the same with `f` have a
   resultant that is not zero (`quadRes`);
6. a point `u` on no hyperplane at which the derivative `v ↦ ∑_i 2 max(u w_i, 0) (v w_i) a_i` of
   the map of the block is invertible ("`h_1` takes all values in an open set").

All six hold at almost every parameter of a block of width at least `d ≥ 2`
(`OneBlock/SkiplessReluSqWideRMSZero.lean`). From them, for `E` of rank `d`, `d ≥ 2` and at
least `d` units: the hypotheses of `reluSq_unitsParallelAt_of_generic` at the columns of
`E W_read` and the rows of `W_write`, hence `UnitsParallelAt`; a nonempty open set of outputs of
the block at rows off the kinks; and the ranks of `W_read` and `W_write`.
-/

namespace Skips

open Matrix

/-- **ReLU² hidden units in general position** (the conditions "for generic parameters" of the
proof of Theorem B.1 (iv) of the skips paper, "The skipless network: equality", for `k = 2`). -/
def UnitsGeneralPositionSq {d q : Type*} [Fintype d] [DecidableEq d] [Fintype q]
    (Wr : Matrix d q ℝ) (Ww : Matrix q d ℝ) : Prop :=
  (∀ i j, i ≠ j → ∀ r : ℝ, Wrᵀ i ≠ r • Wrᵀ j) ∧
  (∀ i, Ww i ≠ 0) ∧
  (∀ u : d → ℝ, (∃ i, 0 < u ⬝ᵥ Wrᵀ i) → ∑ i, reluSq (u ⬝ᵥ Wrᵀ i) • Ww i ≠ 0) ∧
  (∀ i, ∃ u₀ : d → ℝ, u₀ ⬝ᵥ Wrᵀ i = 0 ∧ (∀ j, j ≠ i → u₀ ⬝ᵥ Wrᵀ j ≠ 0) ∧
    ∀ r : ℝ, ∑ j, reluSq (u₀ ⬝ᵥ Wrᵀ j) • Ww j ≠ r • Ww i) ∧
  (∀ S : Finset q, 2 ≤ S.card → ∃ (u v : d → ℝ) (e f : d),
    quadRes (∑ i ∈ S, (u ⬝ᵥ Wrᵀ i) ^ 2 * Ww i e)
      (2 * ∑ i ∈ S, (u ⬝ᵥ Wrᵀ i) * (v ⬝ᵥ Wrᵀ i) * Ww i e) (∑ i ∈ S, (v ⬝ᵥ Wrᵀ i) ^ 2 * Ww i e)
      (∑ i ∈ S, (u ⬝ᵥ Wrᵀ i) ^ 2 * Ww i f)
      (2 * ∑ i ∈ S, (u ⬝ᵥ Wrᵀ i) * (v ⬝ᵥ Wrᵀ i) * Ww i f)
      (∑ i ∈ S, (v ⬝ᵥ Wrᵀ i) ^ 2 * Ww i f) ≠ 0) ∧
  ∃ u : d → ℝ, (∀ i, u ⬝ᵥ Wrᵀ i ≠ 0) ∧
    IsUnit (∑ i, reluSqDeriv (u ⬝ᵥ Wrᵀ i) • Matrix.vecMulVec (Wrᵀ i) (Ww i)).det

variable {dIn d q : Type*} [Fintype dIn] [Fintype d] [DecidableEq d] [Fintype q]

/-- ReLU² units in general position, `d ≥ 2`: `W_read` and `W_write` have rank `d`, and no column
of `W_read` is zero. -/
theorem rank_of_unitsGeneralPositionSq {Wr : Matrix d q ℝ} {Ww : Matrix q d ℝ}
    (hd : 2 ≤ Fintype.card d) (hG : UnitsGeneralPositionSq Wr Ww) :
    Wr.rank = Fintype.card d ∧ Ww.rank = Fintype.card d ∧ ∀ i, (fun a => Wr a i) ≠ 0 := by
  sorry

/-- **"The kinks stay" and "One scale" for a ReLU² block whose units are in general position:**
for `E` of rank `d ≥ 2`, `UnitsParallelAt` holds at the columns `c_i` of `E W_read` and the rows
`a_i` of `W_write`. -/
theorem reluSq_unitsParallelAt_of_unitsGeneralPositionSq (E : Matrix dIn d ℝ)
    {Wr : Matrix d q ℝ} {Ww : Matrix q d ℝ} (hd : 2 ≤ Fintype.card d)
    (hE : E.rank = Fintype.card d) (hG : UnitsGeneralPositionSq Wr Ww) :
    UnitsParallelAt reluSq reluSqDeriv 2 (fun i => (E * Wr)ᵀ i) (fun i => Ww i) := by
  sorry

/-- **"`h_1` takes all values in an open set", for a ReLU² block whose units are in general
position:** for `E` of rank `d`, the outputs `∑_i max(x c_i, 0)² a_i` of the block at the rows `x`
on no hyperplane `x c_i = 0` contain a nonempty open set. -/
theorem exists_open_reluSq_of_unitsGeneralPositionSq (E : Matrix dIn d ℝ) {Wr : Matrix d q ℝ}
    {Ww : Matrix q d ℝ} (hE : E.rank = Fintype.card d) (hG : UnitsGeneralPositionSq Wr Ww) :
    ∃ O : Set (d → ℝ), IsOpen O ∧ O.Nonempty ∧ ∀ v ∈ O, ∃ x : dIn → ℝ,
      (∀ i, x ⬝ᵥ (E * Wr)ᵀ i ≠ 0) ∧ ∑ i, reluSq (x ⬝ᵥ (E * Wr)ᵀ i) • Ww i = v := by
  sorry

end Skips
