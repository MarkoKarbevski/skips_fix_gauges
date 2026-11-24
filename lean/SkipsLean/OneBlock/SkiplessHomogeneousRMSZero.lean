import SkipsLean.Dimension.UpperBoundRMSNormZero
import SkipsLean.Dimension.RescalingMlp
import SkipsLean.OneBlock.Common

/-!
# One skipless block under pre-RMSNorm with `ε = 0`, ReLU and ReLU²: the bound

Paper (skips paper), Theorem B.1 (iv): "Let the network be pre-RMSNorm with `ε = 0`, without
biases, with a ReLU, ReLU² or ReGLU block of width at least `d_model`. For generic parameters the
residual network has functional dimension `P − d_model (d_model − 1)/2 − 1 − s`, and the skipless
network at most `P − d_model² − d_model (d_model − 1)/2 − 1 − s`, with equality for ReLU and ReLU²
blocks."

Its proof, "Part (iv)": "With `ε = 0`, `N_ε(h) = √d_model h/‖h‖` depends only on the direction of
`h`, and `B(λ n) = λ^k B(n)` for `λ > 0`, so `N_ε(B(N_ε(h))) = N_ε(B(h))`: the skipless network
computes `x ↦ N_ε(B(x E)) D`. Its normalization before the block drops out, which leaves the
changes of basis `GL(d_model)` at `h_0` and `CO(d_model)` at `h_1`, of dimension
`d_model² + d_model (d_model − 1)/2 + 1`". And "The skipless network: the bound. The changes of
basis in `GL(d_model)` at `h_0` and in `CO(d_model)` at `h_1` and the symmetries inside the block
preserve the function. They move the parameters along the directions with the entries `E X` at
`E` and `−X W_read` at `W_read`, with the entries `W_write (Y + c I)` at `W_write` and `−Y D` at
`D` for an antisymmetric `Y` and a number `c`, and along the rescalings of the units. For generic
parameters these directions are independent, as in Step 3 of part (i). So
`dim K(θ) ≥ d_model² + d_model (d_model − 1)/2 + 1 + s`, which is the bound."

Here, for one MLP block whose activation is positively homogeneous of degree `k` (ReLU: `k = 1`;
ReLU²: `k = 2`), `s` is the number of hidden units: the direction of a change of basis `I + τ X`
at `h_0`, for every matrix `X`, is flat under pre-RMSNorm with `ε = 0`; the bound at one parameter
under the conditions of the proof (`E` and the write of rank `d`, no read column zero); the bound
at almost every parameter for ReLU and ReLU² blocks of width at least `d`.

The functional dimension is Lean's `funDim`, over all inputs, with the derivative in the weights
taken to be `0` where the output is not differentiable, and with Lean's `rmsNorm 0`, which maps a
zero row to `0`. It is at least the paper's, which uses fewer inputs, so the bound holds for the
paper's. Not stated here: the bound for ReGLU blocks; the value for the residual network; the
equality for ReLU and ReLU² blocks.
-/

namespace Skips

open Matrix MeasureTheory

variable {T d dIn dOut : Type*} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {σ : ℝ → ℝ} {hid : Fin 1 → Type} [∀ ℓ, Fintype (hid ℓ)]

/-- **Proof of Theorem B.1 (iv) of the skips paper, "Its normalization before the block drops
out":** for one skipless MLP block with `σ(λ z) = λ^k σ(z)` for `λ > 0`, under pre-RMSNorm with
`ε = 0`, the direction of the change of basis `I + τ X` at `h_0` (`E X` at `E`, `−X W_read` at
`W_read`) is flat, for every matrix `X`. -/
theorem cobDir_zero_mem_flat_skipless_mlp_homogeneous_rmsNorm_zero {k : ℕ}
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) (X : Matrix d d ℝ) :
    cobDir θ ![X, 0] ∈ flat (Arch.mlp σ (rmsNorm 0) hid) 0 θ := by
  sorry

/-- **Theorem B.1 (iv) of the skips paper, the skipless network, the bound, under the conditions
of the proof:** for one skipless MLP block with a positively homogeneous activation under
pre-RMSNorm with `ε = 0`, if `E` and the write have rank `d ≥ 1` and no read column is zero, the
functional dimension is at most `P − d² − (d(d−1)/2 + 1) − s`, where `s` is the number of hidden
units. -/
theorem funDim_add_le_skipless_mlp_homogeneous_rmsNorm_zero [Nonempty d] {k : ℕ}
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d) (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d)
    (hc : ∀ ℓ i, (fun a => θ.read ℓ a i) ≠ 0) :
    funDim (Arch.mlp σ (rmsNorm 0) hid) 0 θ
        + (Fintype.card d ^ 2 + (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
          + Fintype.card (hid 0))
      ≤ Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) := by
  sorry

/-- **Theorem B.1 (iv) of the skips paper, the skipless network, for a ReLU block of width at
least `d` at generic parameters:** under pre-RMSNorm with `ε = 0`, with `d_in ≥ d ≥ 1`, the
functional dimension is at most `P − d² − d(d−1)/2 − 1 − s`. -/
theorem ae_funDim_add_le_skipless_relu_oneBlock_rmsNorm_zero [Nonempty d]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, funDim (Arch.mlp relu (rmsNorm 0) hid) 0 θ
        + (Fintype.card d ^ 2 + (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
          + Fintype.card (hid 0))
      ≤ Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut) := by
  sorry

/-- **Theorem B.1 (iv) of the skips paper, the skipless network, for a ReLU² block of width at
least `d` at generic parameters:** under pre-RMSNorm with `ε = 0`, with `d_in ≥ d ≥ 1`, the
functional dimension is at most `P − d² − d(d−1)/2 − 1 − s`. -/
theorem ae_funDim_add_le_skipless_reluSq_oneBlock_rmsNorm_zero [Nonempty d]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) reluSq (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, funDim (Arch.mlp reluSq (rmsNorm 0) hid) 0 θ
        + (Fintype.card d ^ 2 + (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
          + Fintype.card (hid 0))
      ≤ Module.finrank ℝ
          (Params (Arch.mlp (T := T) (d := d) reluSq (rmsNorm 0) hid) dIn dOut) := by
  sorry

end Skips
