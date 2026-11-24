import SkipsLean.OneBlock.SkiplessHomogeneousRMSZeroEq
import SkipsLean.OneBlock.UnitsParallelAt

/-!
# One skipless block of any width with a homogeneous activation, `ε = 0`: the equality

Paper (skips paper), Theorem B.1 (iv): "Let the network be pre-RMSNorm with `ε = 0`, without
biases, with a ReLU, ReLU² or ReGLU block of width at least `d_model`. For generic parameters the
residual network has functional dimension `P − d_model (d_model − 1)/2 − 1 − s`, and the skipless
network at most `P − d_model² − d_model (d_model − 1)/2 − 1 − s`, with equality for ReLU and ReLU²
blocks."

`OneBlock/SkiplessHomogeneousRMSZeroEq.lean` has "with equality" for a block of width exactly
`d_model`, where the columns `c_i` of `E W_read` and the rows `a_i` of `W_write` are linearly
independent. Here the same three statements at one parameter **with no condition on the width**:
the two places where the width was used are hypotheses on the parameter,

* "The kinks stay" and "One scale" at the units of this parameter: `UnitsParallelAt σ σ' k c a`
  (`OneBlock/UnitsParallelAt.lean`) for the columns `c_i` of `E W_read` and the rows `a_i` of
  `W_write`;
* "since `h_1` takes all values in an open set": a nonempty open set of vectors `v`, each the
  output `∑_i σ(x c_i) a_i` of the block at a row `x` at which no hidden unit sits at its kink;

and the columns of `W_read` are nonzero (the bound `OneBlock/SkiplessHomogeneousRMSZero.lean`
asks it). The steps of the proof are those of the file for width `d_model`: the final
normalization (equation (18), `OneBlock/SkiplessRMSZeroReadout.lean`), the units, and "Counting"
with Lemma B.2 (`keeps_products_iff_mem_range_cobDir`).

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
variable {σ σ' : ℝ → ℝ}

/-- **Proof of Theorem B.1 (iv) of the skips paper, "The skipless network: equality", for an MLP
block of any width with a positively homogeneous activation, at one parameter:** let `ε = 0`,
`d ≥ 2`, let `σ` be differentiable off `0` and positively homogeneous of degree `k`; let `E`, `D`,
`W_read`, `W_write` have rank `d`; let the steps "The kinks stay" and "One scale" hold at the
columns `c_i` of `E W_read` and the rows `a_i` of `W_write` (`UnitsParallelAt`), and let the
outputs `∑_i σ(x c_i) a_i` of the block at rows `x` off the kinks fill a nonempty open set. Then a
direction that is flat at every input at which no normalized row vanishes and no hidden unit sits
at its kink is the direction of a change of basis `I + τ X` at `h_0`, of a rotation and a scaling
at `h_1`, plus a rescaling of the hidden units. -/
theorem flatOn_le_mlp_rescale_skipless_rmsNorm_zero_of_unitsParallelAt {k : ℕ}
    (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (hhom : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
    (hd : 2 ≤ Fintype.card d)
    (hE : θ.E.rank = Fintype.card d) (hD : θ.D.rank = Fintype.card d)
    (hR : (θ.read 0).rank = Fintype.card d) (hW : (θ.write 0).rank = Fintype.card d)
    (hP : UnitsParallelAt σ σ' k (fun i => (θ.E * θ.read 0)ᵀ i) (fun i => θ.write 0 i))
    (hO : ∃ O : Set (d → ℝ), IsOpen O ∧ O.Nonempty ∧ ∀ v ∈ O, ∃ x : dIn → ℝ,
      (∀ i, x ⬝ᵥ (θ.E * θ.read 0)ᵀ i ≠ 0) ∧
        ∑ i, σ (x ⬝ᵥ (θ.E * θ.read 0)ᵀ i) • θ.write 0 i = v)
    (η : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
    (hη : η ∈ flatOn (Arch.mlp σ (rmsNorm 0) hid) 0 θ
      (skiplessZeroDomain (Arch.mlp σ (rmsNorm 0) hid) θ ∩ noKinkRMS θ)) :
    ∃ (X Y : Matrix d d ℝ) (c : ℝ) (α : ∀ ℓ, hid ℓ → ℝ), Yᵀ = -Y ∧
      η = cobDir θ ![X, Y] + c • scaleDir θ ![0, 1] + rescaleDirMlp k θ α := by
  sorry

/-- **Theorem B.1 (iv) of the skips paper, the skipless network, "with equality", for an MLP
block of any width with a positively homogeneous activation, at one parameter:** under the
conditions of `flatOn_le_mlp_rescale_skipless_rmsNorm_zero_of_unitsParallelAt` and for nonzero
columns of `W_read`, `funDim = P − d² − (d(d−1)/2 + 1) − s`, with `s` the number of hidden
units. -/
theorem funDim_mlp_oneBlock_rescale_skipless_rmsNorm_zero_of_unitsParallelAt {k : ℕ}
    (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (hhom : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
    (hd : 2 ≤ Fintype.card d)
    (hE : θ.E.rank = Fintype.card d) (hD : θ.D.rank = Fintype.card d)
    (hR : (θ.read 0).rank = Fintype.card d) (hW : (θ.write 0).rank = Fintype.card d)
    (hc : ∀ i, (fun a => θ.read 0 a i) ≠ 0)
    (hP : UnitsParallelAt σ σ' k (fun i => (θ.E * θ.read 0)ᵀ i) (fun i => θ.write 0 i))
    (hO : ∃ O : Set (d → ℝ), IsOpen O ∧ O.Nonempty ∧ ∀ v ∈ O, ∃ x : dIn → ℝ,
      (∀ i, x ⬝ᵥ (θ.E * θ.read 0)ᵀ i ≠ 0) ∧
        ∑ i, σ (x ⬝ᵥ (θ.E * θ.read 0)ᵀ i) • θ.write 0 i = v) :
    funDim (Arch.mlp σ (rmsNorm 0) hid) 0 θ
        + (Fintype.card d ^ 2 + (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
          + Fintype.card (hid 0))
      = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) := by
  sorry

/-- **Theorem B.1 (iv) of the skips paper, the skipless network, "with equality", in the paper's
own sense, at one parameter:** under the same conditions, a finite batch of inputs at which no
normalized row vanishes and no hidden unit sits at its kink, on which the Jacobian has the rank
`P − d² − (d(d−1)/2 + 1) − s`. -/
theorem exists_jacobianRank_mlp_oneBlock_rescale_skipless_rmsNorm_zero_of_unitsParallelAt {k : ℕ}
    (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (hhom : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
    (hd : 2 ≤ Fintype.card d)
    (hE : θ.E.rank = Fintype.card d) (hD : θ.D.rank = Fintype.card d)
    (hR : (θ.read 0).rank = Fintype.card d) (hW : (θ.write 0).rank = Fintype.card d)
    (hc : ∀ i, (fun a => θ.read 0 a i) ≠ 0)
    (hP : UnitsParallelAt σ σ' k (fun i => (θ.E * θ.read 0)ᵀ i) (fun i => θ.write 0 i))
    (hO : ∃ O : Set (d → ℝ), IsOpen O ∧ O.Nonempty ∧ ∀ v ∈ O, ∃ x : dIn → ℝ,
      (∀ i, x ⬝ᵥ (θ.E * θ.read 0)ᵀ i ≠ 0) ∧
        ∑ i, σ (x ⬝ᵥ (θ.E * θ.read 0)ᵀ i) • θ.write 0 i = v) :
    ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ),
      (∀ i, X i ∈ skiplessZeroDomain (Arch.mlp σ (rmsNorm 0) hid) θ ∩ noKinkRMS θ) ∧
      jacobianRank (Arch.mlp σ (rmsNorm 0) hid) 0 X θ
          + (Fintype.card d ^ 2 + (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
            + Fintype.card (hid 0))
        = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) := by
  sorry

end Skips
