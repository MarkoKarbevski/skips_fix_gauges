import SkipsLean.OneBlock.SkiplessHomogeneousRMSZeroEq
import SkipsLean.OneBlock.SkiplessReluWideRMSZero
import SkipsLean.OneBlock.UnitsGeneralPositionSq

/-!
# One skipless ReLU² block of width at least `d` under pre-RMSNorm with `ε = 0`: the equality

Paper (skips paper), Theorem B.1 (iv): "Let the network be pre-RMSNorm with `ε = 0`, without
biases, with a ReLU, ReLU² or ReGLU block of width at least `d_model`. For generic parameters the
residual network has functional dimension `P − d_model (d_model − 1)/2 − 1 − s`, and the skipless
network at most `P − d_model² − d_model (d_model − 1)/2 − 1 − s`, with equality for ReLU and ReLU²
blocks. So the skip raises the functional dimension by at least `d_model²`, and by exactly
`d_model²` for ReLU and ReLU² blocks."

Here "with equality" and "by exactly `d_model²`" **for a ReLU² block of width at least
`d_model`** (`OneBlock/SkiplessHomogeneousRMSZeroEq.lean` has width exactly `d_model`;
`OneBlock/SkiplessReluWideRMSZero.lean` the ReLU block of width at least `d_model`):

* at almost every parameter of a block of width at least `d ≥ 2` the hidden units are in general
  position in the sense for ReLU² (`UnitsGeneralPositionSq`,
  `OneBlock/UnitsGeneralPositionSq.lean`), one statement for each of its conditions;
* then the statements at one parameter (`OneBlock/SkiplessHomogeneousRMSZeroEqAt.lean`) apply.

The paper's proof of "for generic parameters `h_1 ≠ 0` there" uses the resultant of `d_model`
quadratic forms, and it does not show that "two entries `h_a` and `h_b` of `h_1` have no common
factor" holds for generic parameters. The Lean route: the parameters at which the output of the
block vanishes at a row with an active unit lie in the image of a map of the parameter space
into itself whose derivative is nowhere invertible (one row `a_i` is solved for, and the map is
homogeneous of degree `0` in the row that takes its place), a set of measure zero; and the
condition on two entries is a resultant of two polynomials in one variable, on one line, which
is not zero for almost every parameter.

The functional dimension: the value of Lean's `funDim`, and a finite batch of the paper's inputs
(no normalized row vanishes, no hidden unit at its kink) with this rank; the two together are the
paper's statement.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {hid : Fin 1 → Type} [∀ ℓ, Fintype (hid ℓ)]

/-- **"For generic parameters `h_1 ≠ 0` there", for ReLU² units:** at almost every parameter of
one MLP block, `∑_i max(u w_i, 0)² a_i ≠ 0` at every `u` at which a unit is active. -/
theorem ae_forall_sum_reluSq_ne_zero {σ : ℝ → ℝ}
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] :
    ∀ᵐ θ ∂μ, ∀ u : d → ℝ, (∃ i, 0 < u ⬝ᵥ (θ.read 0)ᵀ i) →
      ∑ i, reluSq (u ⬝ᵥ (θ.read 0)ᵀ i) • θ.write 0 i ≠ 0 := by
  sorry

/-- **"`h_1(x_0)` is not parallel to `a_i`", for ReLU² units:** at almost every parameter of one
MLP block with at least two hidden units and `d ≥ 2`, every unit `i` has a point `u_0` of its
hyperplane, on no other hyperplane, at which `∑_j max(u_0 w_j, 0)² a_j` is not a multiple of
`a_i`. -/
theorem ae_exists_kink_point_reluSq {σ : ℝ → ℝ}
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hq : 2 ≤ Fintype.card (hid 0)) :
    ∀ᵐ θ ∂μ, ∀ i, ∃ u₀ : d → ℝ, u₀ ⬝ᵥ (θ.read 0)ᵀ i = 0 ∧
      (∀ j, j ≠ i → u₀ ⬝ᵥ (θ.read 0)ᵀ j ≠ 0) ∧
      ∀ r : ℝ, ∑ j, reluSq (u₀ ⬝ᵥ (θ.read 0)ᵀ j) • θ.write 0 j ≠ r • θ.write 0 i := by
  sorry

/-- **"Two entries `h_a` and `h_b` of `h_1` have no common factor", for ReLU² units, on a line:**
at almost every parameter of one MLP block with `d ≥ 2`, for every set `S` of at least two units
there are a line `t ↦ u + t v` and two entries `e`, `f` for which the resultant of the
polynomials `t ↦ ∑_{i∈S} ((u + t v) w_i)² a_{i e}` and `t ↦ ∑_{i∈S} ((u + t v) w_i)² a_{i f}` is
not zero. -/
theorem ae_exists_quadRes_ne_zero {σ : ℝ → ℝ}
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) :
    ∀ᵐ θ ∂μ, ∀ S : Finset (hid 0), 2 ≤ S.card → ∃ (u v : d → ℝ) (e f : d),
      quadRes (∑ i ∈ S, (u ⬝ᵥ (θ.read 0)ᵀ i) ^ 2 * θ.write 0 i e)
        (2 * ∑ i ∈ S, (u ⬝ᵥ (θ.read 0)ᵀ i) * (v ⬝ᵥ (θ.read 0)ᵀ i) * θ.write 0 i e)
        (∑ i ∈ S, (v ⬝ᵥ (θ.read 0)ᵀ i) ^ 2 * θ.write 0 i e)
        (∑ i ∈ S, (u ⬝ᵥ (θ.read 0)ᵀ i) ^ 2 * θ.write 0 i f)
        (2 * ∑ i ∈ S, (u ⬝ᵥ (θ.read 0)ᵀ i) * (v ⬝ᵥ (θ.read 0)ᵀ i) * θ.write 0 i f)
        (∑ i ∈ S, (v ⬝ᵥ (θ.read 0)ᵀ i) ^ 2 * θ.write 0 i f) ≠ 0 := by
  sorry

/-- **"`h_1` takes all values in an open set", for ReLU² units, the derivative:** at almost every
parameter of one MLP block of width at least `d`, there is a point `u` on no hyperplane at which
the derivative `v ↦ ∑_i 2 max(u w_i, 0) (v w_i) a_i` of the map of the block is invertible. -/
theorem ae_exists_isUnit_det_reluSqDeriv {σ : ℝ → ℝ}
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hcard : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ θ ∂μ, ∃ u : d → ℝ, (∀ i, u ⬝ᵥ (θ.read 0)ᵀ i ≠ 0) ∧
      IsUnit (∑ i, reluSqDeriv (u ⬝ᵥ (θ.read 0)ᵀ i)
        • Matrix.vecMulVec ((θ.read 0)ᵀ i) (θ.write 0 i)).det := by
  sorry

/-- **The conditions "for generic parameters" of the proof of Theorem B.1 (iv), "The skipless
network: equality", for ReLU²:** for one MLP block with at least `d ≥ 2` hidden units, at almost
every parameter the hidden units are in general position in the sense for ReLU². -/
theorem ae_unitsGeneralPositionSq {σ : ℝ → ℝ}
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d)
    (hcard : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ θ ∂μ, UnitsGeneralPositionSq (θ.read 0) (θ.write 0) := by
  -- the first two conditions are among those for ReLU; the other four are the statements above
  filter_upwards [ae_unitsGeneralPosition μ hd hcard, ae_forall_sum_reluSq_ne_zero μ,
    ae_exists_kink_point_reluSq μ hd (hd.trans hcard), ae_exists_quadRes_ne_zero μ hd,
    ae_exists_isUnit_det_reluSqDeriv μ hcard] with θ hG h3 h4 h5 h6
  refine ⟨hG.1, fun i h0 => ?_, h3, h4, h5, h6⟩
  -- one row of `W_write` is a linearly independent family, so it is not zero
  have hli := hG.2.1 {i} (by rw [Finset.card_singleton]; omega)
  exact hli.ne_zero ⟨i, Finset.mem_singleton_self i⟩ h0

omit [Nonempty T] in
/-- Helper: at almost every parameter `E` and `D` have rank `d` (`d_in, d_out ≥ d`, width at
least `d`); a copy of `ae_rank_E_D_srw`. -/
private theorem ae_rank_E_D_ssq {σ : ℝ → ℝ}
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hcard : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ θ ∂μ, θ.E.rank = Fintype.card d ∧ θ.D.rank = Fintype.card d := by
  obtain ⟨ρD⟩ := Function.Embedding.nonempty_of_card_le hdOut
  filter_upwards [ae_rank_E_write μ hdIn
      (fun ℓ => by obtain rfl := Subsingleton.elim ℓ 0; exact hcard),
    ae_isUnit_det_submatrix μ] with θ h1 h2
  exact ⟨h1.1, rank_eq_card_of_isUnit_det θ.D ρD (h2.2.1 ρD)⟩

/-- **Theorem B.1 (iv) of the skips paper, the skipless network, "with equality", for one ReLU²
block of width at least `d`:** for `d_in, d_out ≥ d ≥ 2` and at least `d` hidden units, at almost
every parameter `funDim = P − d² − (d(d−1)/2 + 1) − s`. -/
theorem ae_funDim_reluSq_oneBlock_skipless_rmsNorm_zero_of_le
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) reluSq (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hcard : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ θ ∂μ, funDim (Arch.mlp reluSq (rmsNorm 0) hid) 0 θ
        + (Fintype.card d ^ 2 + (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
          + Fintype.card (hid 0))
      = Module.finrank ℝ
          (Params (Arch.mlp (T := T) (d := d) reluSq (rmsNorm 0) hid) dIn dOut) := by
  filter_upwards [ae_rank_E_D_ssq μ hdIn hdOut hcard,
    ae_unitsGeneralPositionSq μ hd hcard] with θ hθ hG
  obtain ⟨hR, hW, hc⟩ := rank_of_unitsGeneralPositionSq hd hG
  exact funDim_mlp_oneBlock_rescale_skipless_rmsNorm_zero_of_unitsParallelAt
    (fun z _ => hasDerivAt_reluSq z) reluSq_homogeneous θ hd hθ.1 hθ.2 hR hW hc
    (reluSq_unitsParallelAt_of_unitsGeneralPositionSq θ.E hd hθ.1 hG)
    (exists_open_reluSq_of_unitsGeneralPositionSq θ.E hθ.1 hG)

/-- **The same in the paper's own sense:** at almost every parameter a finite batch of inputs at
which no normalized row vanishes and no hidden unit sits at its kink, on which the Jacobian has
the rank `P − d² − d(d−1)/2 − 1 − s`. -/
theorem ae_exists_jacobianRank_reluSq_oneBlock_skipless_rmsNorm_zero_of_le
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) reluSq (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hcard : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ θ ∂μ, ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ),
      (∀ i, X i ∈ skiplessZeroDomain (Arch.mlp reluSq (rmsNorm 0) hid) θ ∩ noKinkRMS θ) ∧
      jacobianRank (Arch.mlp reluSq (rmsNorm 0) hid) 0 X θ
          + (Fintype.card d ^ 2 + (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
            + Fintype.card (hid 0))
        = Module.finrank ℝ
            (Params (Arch.mlp (T := T) (d := d) reluSq (rmsNorm 0) hid) dIn dOut) := by
  filter_upwards [ae_rank_E_D_ssq μ hdIn hdOut hcard,
    ae_unitsGeneralPositionSq μ hd hcard] with θ hθ hG
  obtain ⟨hR, hW, hc⟩ := rank_of_unitsGeneralPositionSq hd hG
  exact exists_jacobianRank_mlp_oneBlock_rescale_skipless_rmsNorm_zero_of_unitsParallelAt
    (fun z _ => hasDerivAt_reluSq z) reluSq_homogeneous θ hd hθ.1 hθ.2 hR hW hc
    (reluSq_unitsParallelAt_of_unitsGeneralPositionSq θ.E hd hθ.1 hG)
    (exists_open_reluSq_of_unitsGeneralPositionSq θ.E hθ.1 hG)

/-- **Theorem B.1 (iv) of the skips paper, "by exactly `d_model²` for ReLU and ReLU² blocks", for
one ReLU² block of width at least `d`:** at almost every parameter `funDim` of the residual
network is `funDim` of the skipless network plus `d²`. -/
theorem ae_funDim_reluSq_oneBlock_residual_rmsNorm_zero_eq_add_of_le
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) reluSq (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hcard : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ θ ∂μ, funDim (Arch.mlp reluSq (rmsNorm 0) hid) 1 θ
      = funDim (Arch.mlp reluSq (rmsNorm 0) hid) 0 θ + Fintype.card d ^ 2 := by
  have : Nonempty (hid 0) := Fintype.card_pos_iff.1 (by omega)
  filter_upwards [ae_funDim_reluSq_oneBlock_residual_rmsNorm_zero μ hd hdIn hdOut,
    ae_funDim_reluSq_oneBlock_skipless_rmsNorm_zero_of_le μ hd hdIn hdOut hcard] with θ h1 h0
  omega

end Skips
