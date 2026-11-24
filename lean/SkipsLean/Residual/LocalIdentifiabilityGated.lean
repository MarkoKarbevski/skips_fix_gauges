import SkipsLean.Dimension.OrbitNetwork
import SkipsLean.Dimension.ExpOrbitGated
import SkipsLean.Generic.Gated
import SkipsLean.Residual.UpperBoundSymmetries
import SkipsLean.Residual.DepthGated
import SkipsLean.Residual.DepthGatedRMS

/-!
# Residual networks of gated blocks are locally identifiable

Paper (skips paper): Definition 4.4, Proposition 4.5 and Corollary 4.9.

"Corollary 4.9 (Residual networks are locally identifiable). Let the blocks be analytic, with or
without pre-RMSNorm, and let `θ` be generic parameters of the residual network. Every `θ'` near
`θ` with the same function is obtained from `θ` by symmetries inside the blocks and by one matrix
`G ∈ 𝒢`, all close to the identity. The matrix `G` is the same at all hidden states: for every
block `ℓ`, `E ↦ E G`, `W_read^ℓ ↦ G⁻¹ W_read^ℓ`, `W_write^ℓ ↦ W_write^ℓ G`, `D ↦ G⁻¹ D`."

Stated here, for residual networks of gated blocks (`s` is the number of hidden units of the
network; the symmetries inside the blocks are the rescalings of the values of the hidden units):

* The direction of Proposition 4.5 from the equality condition to local identifiability, at one
  parameter, for a real-analytic gate: if `E` has rank `d`, no value column of a read vanishes and
  the functional dimension at `θ` is `P − d² − s`, resp. `P − d(d−1)/2 − s` under pre-RMSNorm with
  `ε > 0`, then every `θ'` near `θ` with the same function is
  `(θ.rescale c).cob (fun _ => G) (fun _ => G)` with factors `c > 0` near `1` and one invertible
  (resp. orthogonal) `G` near the identity.
* Corollary 4.9 for SwiGLU and GeGLU blocks, without normalization and under pre-RMSNorm with
  `ε > 0`: this holds at almost every parameter (Theorem 4.7 gives the functional dimension).

The twin for networks without skip connections is `Dimension/LocalIdentifiabilityGated.lean`; the
blocks without symmetries inside are in `Residual/LocalIdentifiability.lean`. All use
`exists_mem_orbit_of_eval_eq` (`Dimension/OrbitNetwork.lean`) and `θ.rescale c`
(`Dimension/RescaleAction.lean`). Not stated here: the converse direction of Proposition 4.5,
attention blocks, and the case `ε = 0`.
-/

namespace Skips

open Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {σ : ℝ → ℝ} {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]

/-- **Proposition 4.5 for residual networks of gated blocks, from the equality condition to
local identifiability, without normalization:** for a real-analytic gate `σ`, if `E` has rank `d`,
no value column of a read vanishes and `fd(θ) = P − d² − s`, then every `θ'` near `θ` with the
same function is `θ` after a rescaling of the values of the hidden units by factors `c` near `1`
and the change of basis by one invertible `G` near the identity at all hidden states. -/
theorem exists_cob_rescale_of_eval_eq_residual_gated (hσ : AnalyticOnNhd ℝ σ Set.univ)
    (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d)
    (hv : ∀ ℓ i, (fun k => θ.read ℓ k (Sum.inr i)) ≠ 0)
    (hfd : funDim (Arch.gated σ id hid) 1 θ
        + (Fintype.card d ^ 2 + ∑ ℓ, Fintype.card (hid ℓ))
      = Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)) :
    ∀ V ∈ 𝓝 (1 : Matrix d d ℝ), ∀ W ∈ 𝓝 (1 : ∀ ℓ, hid ℓ → ℝ), ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.gated σ id hid) 1 θ' x
        = eval (Arch.gated σ id hid) 1 θ x) →
        ∃ (G : GL d ℝ) (c : ∀ ℓ, hid ℓ → ℝ), (G : Matrix d d ℝ) ∈ V ∧ c ∈ W ∧
          (∀ ℓ i, 0 < c ℓ i) ∧ θ' = (θ.rescale c).cob (fun _ => G) (fun _ => G) := by
  sorry

/-- **Proposition 4.5 for residual networks of gated blocks, from the equality condition to
local identifiability, under pre-RMSNorm with `ε > 0`:** for a real-analytic gate `σ`, if `E` has
rank `d`, no value column of a read vanishes and `fd(θ) = P − d(d−1)/2 − s`, then every `θ'` near
`θ` with the same function is `θ` after a rescaling of the values of the hidden units by factors
`c` near `1` and the change of basis by one orthogonal `Q` near the identity at all hidden
states. -/
theorem exists_cob_rescale_of_eval_eq_residual_gated_rmsNorm {ε : ℝ} (hε : 0 < ε)
    (hσ : AnalyticOnNhd ℝ σ Set.univ)
    (θ : Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d)
    (hv : ∀ ℓ i, (fun k => θ.read ℓ k (Sum.inr i)) ≠ 0)
    (hfd : funDim (Arch.gated σ (rmsNorm ε) hid) 1 θ
        + (Fintype.card d * (Fintype.card d - 1) / 2 + ∑ ℓ, Fintype.card (hid ℓ))
      = Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)) :
    ∀ V ∈ 𝓝 (1 : Matrix d d ℝ), ∀ W ∈ 𝓝 (1 : ∀ ℓ, hid ℓ → ℝ), ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.gated σ (rmsNorm ε) hid) 1 θ' x
        = eval (Arch.gated σ (rmsNorm ε) hid) 1 θ x) →
        ∃ (Q : GL d ℝ) (c : ∀ ℓ, hid ℓ → ℝ),
          (Q : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ ∧ (Q : Matrix d d ℝ) ∈ V ∧ c ∈ W ∧
          (∀ ℓ i, 0 < c ℓ i) ∧ θ' = (θ.rescale c).cob (fun _ => Q) (fun _ => Q) := by
  sorry

/-- **Corollary 4.9 for SwiGLU blocks without normalization:** for `d_in, d_out ≥ d ≥ 2`, at almost
every parameter `θ` of the residual network, every `θ'` near `θ` with the same function is `θ` after
a rescaling of the value of each hidden unit, close to `1`, and the change of basis by one
invertible `G` near the identity at all hidden states. -/
theorem ae_exists_cob_rescale_of_eval_eq_swiglu_residual [Nonempty T]
    (μ : Measure (Params (Arch.gated (T := T) (d := d) silu id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, ∀ V ∈ 𝓝 (1 : Matrix d d ℝ), ∀ W ∈ 𝓝 (1 : ∀ ℓ, hid ℓ → ℝ), ∃ U ∈ 𝓝 θ,
      ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.gated silu id hid) 1 θ' x
        = eval (Arch.gated silu id hid) 1 θ x) →
        ∃ (G : GL d ℝ) (c : ∀ ℓ, hid ℓ → ℝ), (G : Matrix d d ℝ) ∈ V ∧ c ∈ W ∧
          (∀ ℓ i, 0 < c ℓ i) ∧ θ' = (θ.rescale c).cob (fun _ => G) (fun _ => G) := by
  sorry

/-- **Corollary 4.9 for SwiGLU blocks under pre-RMSNorm with `ε > 0`:** for `d_in, d_out ≥ d ≥ 2`,
at almost every parameter `θ` of the residual network, every `θ'` near `θ` with the same function is
`θ` after a rescaling of the value of each hidden unit, close to `1`, and the change of basis by one
orthogonal `Q` near the identity at all hidden states. -/
theorem ae_exists_cob_rescale_of_eval_eq_swiglu_residual_rmsNorm [Nonempty T] {ε : ℝ} (hε : 0 < ε)
    (μ : Measure (Params (Arch.gated (T := T) (d := d) silu (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, ∀ V ∈ 𝓝 (1 : Matrix d d ℝ), ∀ W ∈ 𝓝 (1 : ∀ ℓ, hid ℓ → ℝ), ∃ U ∈ 𝓝 θ,
      ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.gated silu (rmsNorm ε) hid) 1 θ' x
        = eval (Arch.gated silu (rmsNorm ε) hid) 1 θ x) →
        ∃ (Q : GL d ℝ) (c : ∀ ℓ, hid ℓ → ℝ),
          (Q : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ ∧ (Q : Matrix d d ℝ) ∈ V ∧ c ∈ W ∧
          (∀ ℓ i, 0 < c ℓ i) ∧ θ' = (θ.rescale c).cob (fun _ => Q) (fun _ => Q) := by
  sorry

/-- **Corollary 4.9 for GeGLU blocks without normalization:** for `d_in, d_out ≥ d ≥ 2`, at almost
every parameter `θ` of the residual network, every `θ'` near `θ` with the same function is `θ` after
a rescaling of the value of each hidden unit, close to `1`, and the change of basis by one
invertible `G` near the identity at all hidden states. -/
theorem ae_exists_cob_rescale_of_eval_eq_geglu_residual [Nonempty T]
    (μ : Measure (Params (Arch.gated (T := T) (d := d) gelu id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, ∀ V ∈ 𝓝 (1 : Matrix d d ℝ), ∀ W ∈ 𝓝 (1 : ∀ ℓ, hid ℓ → ℝ), ∃ U ∈ 𝓝 θ,
      ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.gated gelu id hid) 1 θ' x
        = eval (Arch.gated gelu id hid) 1 θ x) →
        ∃ (G : GL d ℝ) (c : ∀ ℓ, hid ℓ → ℝ), (G : Matrix d d ℝ) ∈ V ∧ c ∈ W ∧
          (∀ ℓ i, 0 < c ℓ i) ∧ θ' = (θ.rescale c).cob (fun _ => G) (fun _ => G) := by
  sorry

/-- **Corollary 4.9 for GeGLU blocks under pre-RMSNorm with `ε > 0`:** for `d_in, d_out ≥ d ≥ 2`, at
almost every parameter `θ` of the residual network, every `θ'` near `θ` with the same function is
`θ` after a rescaling of the value of each hidden unit, close to `1`, and the change of basis by one
orthogonal `Q` near the identity at all hidden states. -/
theorem ae_exists_cob_rescale_of_eval_eq_geglu_residual_rmsNorm [Nonempty T] {ε : ℝ} (hε : 0 < ε)
    (μ : Measure (Params (Arch.gated (T := T) (d := d) gelu (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, ∀ V ∈ 𝓝 (1 : Matrix d d ℝ), ∀ W ∈ 𝓝 (1 : ∀ ℓ, hid ℓ → ℝ), ∃ U ∈ 𝓝 θ,
      ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.gated gelu (rmsNorm ε) hid) 1 θ' x
        = eval (Arch.gated gelu (rmsNorm ε) hid) 1 θ x) →
        ∃ (Q : GL d ℝ) (c : ∀ ℓ, hid ℓ → ℝ),
          (Q : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ ∧ (Q : Matrix d d ℝ) ∈ V ∧ c ∈ W ∧
          (∀ ℓ i, 0 < c ℓ i) ∧ θ' = (θ.rescale c).cob (fun _ => Q) (fun _ => Q) := by
  sorry

end Skips
