import SkipsLean.Dimension.UpperBoundRMSNormZero

/-!
# The upper bound for residual networks under pre-RMSNorm with `ε = 0`: one copy of `CO(d)`

Paper (skips paper): Theorem A.17 (Symmetry counts and upper bounds) and Theorem 4.2: "at generic
parameters, the functional dimension is at most `P − (L + 1) dim 𝒢 − s` without skips and at most
`P − dim 𝒢 − s` with identity skips", where under pre-RMSNorm `𝒢` is "`CO(d_model)` when `ε = 0`
and `O(d_model)` when `ε > 0`" (Lemma A.2), and `dim CO(d) = d(d−1)/2 + 1`. Theorem B.1 (iv) uses
the bound `P − d(d−1)/2 − 1 − s` for the residual network with `ε = 0`.

The bound without skips for `ε = 0` is `Dimension/UpperBoundRMSNormZero.lean` (Theorem 4.3 of the
dimension paper), with one copy of `CO(d)` at each hidden state: the directions `cobDir θ Y`
(antisymmetric `Y_ℓ`) and `scaleDir θ β`. With identity skips the change of basis `G = cQ` is the
same at all hidden states (Theorem 3.3): `E ↦ E G`, `W_read^ℓ ↦ Q⁻¹ W_read^ℓ`,
`W_write^ℓ ↦ W_write^ℓ G`, `D ↦ Q⁻¹ D`. Its directions at `θ` are `cobDir θ (fun _ => Y)` with one
antisymmetric `Y`, and `scaleDir θ (fun _ => β)` with one number `β`. Stated here for blocks of any
kind (`s = 0`), as the statements of `Dimension/UpperBoundRMSNormZero.lean`: they hold at every
parameter and for arbitrary maps `f_ℓ`, for Lean's total function (`rmsRow 0 0 = 0`).
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {A : Arch T d L} (θ : Params A dIn dOut)

/-- The direction of one orthogonal change of basis at all hidden states is flat for a residual
network under pre-RMSNorm with `ε = 0`. -/
theorem cobDir_const_mem_flat_residual_rmsNorm_zero (hA : A.χ = rmsNorm 0) (Y : Matrix d d ℝ)
    (hY : Yᵀ = -Y) : cobDir θ (fun _ => Y) ∈ flat A 1 θ := by
  sorry

/-- The direction of one scale at all hidden states (`E ↦ β E`, `W_write^ℓ ↦ β W_write^ℓ`) is flat
for a residual network under pre-RMSNorm with `ε = 0`. -/
theorem scaleDir_const_mem_flat_residual_rmsNorm_zero (hA : A.χ = rmsNorm 0) (β : ℝ) :
    scaleDir θ (fun _ => β) ∈ flat A 1 θ := by
  sorry

/-- **The upper bound for residual networks under pre-RMSNorm with `ε = 0`:** if `E` has rank
`d ≥ 1`, the functional dimension of a residual network is at most `P − (d(d−1)/2 + 1)`. -/
theorem funDim_add_le_residual_rmsNorm_zero [Nonempty d] (hA : A.χ = rmsNorm 0)
    (hE : θ.E.rank = Fintype.card d) :
    funDim A 1 θ + (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
      ≤ Module.finrank ℝ (Params A dIn dOut) := by
  sorry

/-- **Skips paper, Theorem A.17 (ii), residual networks under pre-RMSNorm with `ε = 0`, at generic
parameters:** for `d_in ≥ d ≥ 1`, the functional dimension of a residual network is at most
`P − (d(d−1)/2 + 1)`, with `d(d−1)/2 + 1` the dimension of `CO(d)`. -/
theorem ae_funDim_add_le_residual_rmsNorm_zero [Nonempty d]
    (μ : Measure (Params A dIn dOut)) [μ.IsAddHaarMeasure] (hA : A.χ = rmsNorm 0)
    (hdIn : Fintype.card d ≤ Fintype.card dIn) :
    ∀ᵐ θ ∂μ, funDim A 1 θ + (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
      ≤ Module.finrank ℝ (Params A dIn dOut) := by
  sorry

end Skips
