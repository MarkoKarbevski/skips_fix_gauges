import SkipsLean.Dimension.OrbitNetwork
import SkipsLean.Dimension.ExpOrbit
import SkipsLean.Generic.Params
import SkipsLean.Residual.UpperBoundSymmetries
import SkipsLean.Residual.DepthMlp
import SkipsLean.Residual.DepthMlpRMS

/-!
# Residual networks are locally identifiable up to one change of basis

Paper (skips paper): Definition 4.4, Proposition 4.5 and Corollary 4.9.

"Proposition 4.5 (The equality condition and local identifiability). Let the blocks be analytic,
with or without pre-RMSNorm, within the scope of Section 2. A skipless or a residual network
satisfies the equality condition if and only if, at generic parameters, it is locally identifiable
up to its symmetries. Every symmetry that is needed is then close to the identity."

"Corollary 4.9 (Residual networks are locally identifiable). Let the blocks be analytic, with or
without pre-RMSNorm, and let `θ` be generic parameters of the residual network. Every `θ'` near
`θ` with the same function is obtained from `θ` by symmetries inside the blocks and by one matrix
`G ∈ 𝒢`, all close to the identity. The matrix `G` is the same at all hidden states: for every
block `ℓ`, `E ↦ E G`, `W_read^ℓ ↦ G⁻¹ W_read^ℓ`, `W_write^ℓ ↦ W_write^ℓ G`, `D ↦ G⁻¹ D`."

Stated here, for residual networks whose blocks have no symmetries inside (`s = 0`: tanh and GELU
blocks):

* The direction of Proposition 4.5 from the equality condition to local identifiability, at one
  parameter: for real-analytic blocks, if `E` has rank `d` and the functional dimension at `θ` is
  `P − d²` (without normalization), resp. `P − d(d−1)/2` (under pre-RMSNorm with `ε > 0`), then
  every `θ'` near `θ` with the same function is `θ.cob (fun _ => G) (fun _ => G)` with one
  invertible (resp. orthogonal) `G` near the identity.
* Corollary 4.9 for tanh and GELU blocks, without normalization and under pre-RMSNorm with
  `ε > 0`: this holds at almost every parameter (Theorem 4.7 gives the functional dimension).

The twin for networks without skip connections is `Dimension/LocalIdentifiability.lean`; both use
`exists_mem_orbit_of_eval_eq` (`Dimension/OrbitNetwork.lean`). Not stated here: the converse
direction of Proposition 4.5, the blocks with symmetries inside (SwiGLU and GeGLU:
`Residual/LocalIdentifiabilityGated.lean`; attention), and the case `ε = 0`.
`θ.cob (fun _ => G) (fun _ => G)` is the change of basis with the same `G` at all hidden states
(`Symmetry/ChangeOfBasis.lean`).
-/

namespace Skips

open Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]

/-- **Proposition 4.5 for residual networks, from the equality condition to local
identifiability, without normalization:** for real-analytic blocks, if `E` has rank `d` and
`fd(θ) = P − d²`, then for every neighborhood `V` of the identity there is a neighborhood `U` of
`θ` such that every `θ' ∈ U` with the same function is `θ` after the change of basis by one
`G ∈ V` at all hidden states. -/
theorem exists_cob_of_eval_eq_residual (A : Arch T d L) (hA : A.χ = id)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (θ : Params A dIn dOut)
    (hE : θ.E.rank = Fintype.card d)
    (hfd : funDim A 1 θ + Fintype.card d ^ 2 = Module.finrank ℝ (Params A dIn dOut)) :
    ∀ V ∈ 𝓝 (1 : Matrix d d ℝ), ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval A 1 θ' x = eval A 1 θ x) →
        ∃ G : GL d ℝ, (G : Matrix d d ℝ) ∈ V ∧ θ' = θ.cob (fun _ => G) (fun _ => G) := by
  sorry

/-- **Proposition 4.5 for residual networks, from the equality condition to local
identifiability, under pre-RMSNorm with `ε > 0`:** for real-analytic blocks, if `E` has rank `d`
and `fd(θ) = P − d(d−1)/2`, then for every neighborhood `V` of the identity there is a
neighborhood `U` of `θ` such that every `θ' ∈ U` with the same function is `θ` after the change of
basis by one orthogonal `Q ∈ V` at all hidden states. -/
theorem exists_cob_of_eval_eq_residual_rmsNorm (A : Arch T d L) {ε : ℝ} (hε : 0 < ε)
    (hA : A.χ = rmsNorm ε) (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ)
    (θ : Params A dIn dOut) (hE : θ.E.rank = Fintype.card d)
    (hfd : funDim A 1 θ + Fintype.card d * (Fintype.card d - 1) / 2
      = Module.finrank ℝ (Params A dIn dOut)) :
    ∀ V ∈ 𝓝 (1 : Matrix d d ℝ), ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval A 1 θ' x = eval A 1 θ x) →
        ∃ Q : GL d ℝ, (Q : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ ∧
          (Q : Matrix d d ℝ) ∈ V ∧ θ' = θ.cob (fun _ => Q) (fun _ => Q) := by
  sorry

variable {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]

/-- **Corollary 4.9 for tanh blocks without normalization:** for `d_in, d_out ≥ d ≥ 2`, at
almost every parameter `θ` of the residual network, every `θ'` near `θ` with the same function is
`θ` after the change of basis by one invertible `G` near the identity at all hidden states. -/
theorem ae_exists_cob_of_eval_eq_tanh_residual [Nonempty T]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) Real.tanh id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, ∀ V ∈ 𝓝 (1 : Matrix d d ℝ), ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.mlp Real.tanh id hid) 1 θ' x
        = eval (Arch.mlp Real.tanh id hid) 1 θ x) →
        ∃ G : GL d ℝ, (G : Matrix d d ℝ) ∈ V ∧ θ' = θ.cob (fun _ => G) (fun _ => G) := by
  sorry

/-- **Corollary 4.9 for GELU blocks without normalization:** for `d_in, d_out ≥ d ≥ 2`, at
almost every parameter `θ` of the residual network, every `θ'` near `θ` with the same function is
`θ` after the change of basis by one invertible `G` near the identity at all hidden states. -/
theorem ae_exists_cob_of_eval_eq_gelu_residual [Nonempty T]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) gelu id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, ∀ V ∈ 𝓝 (1 : Matrix d d ℝ), ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.mlp gelu id hid) 1 θ' x
        = eval (Arch.mlp gelu id hid) 1 θ x) →
        ∃ G : GL d ℝ, (G : Matrix d d ℝ) ∈ V ∧ θ' = θ.cob (fun _ => G) (fun _ => G) := by
  sorry

/-- **Corollary 4.9 for tanh blocks under pre-RMSNorm with `ε > 0`:** for
`d_in, d_out ≥ d ≥ 2`, at almost every parameter `θ` of the residual network, every `θ'` near `θ`
with the same function is `θ` after the change of basis by one orthogonal `Q` near the identity at
all hidden states. -/
theorem ae_exists_cob_of_eval_eq_tanh_residual_rmsNorm [Nonempty T] {ε : ℝ} (hε : 0 < ε)
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) Real.tanh (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, ∀ V ∈ 𝓝 (1 : Matrix d d ℝ), ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.mlp Real.tanh (rmsNorm ε) hid) 1 θ' x
        = eval (Arch.mlp Real.tanh (rmsNorm ε) hid) 1 θ x) →
        ∃ Q : GL d ℝ, (Q : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ ∧
          (Q : Matrix d d ℝ) ∈ V ∧ θ' = θ.cob (fun _ => Q) (fun _ => Q) := by
  sorry

/-- **Corollary 4.9 for GELU blocks under pre-RMSNorm with `ε > 0`:** for
`d_in, d_out ≥ d ≥ 2`, at almost every parameter `θ` of the residual network, every `θ'` near `θ`
with the same function is `θ` after the change of basis by one orthogonal `Q` near the identity at
all hidden states. -/
theorem ae_exists_cob_of_eval_eq_gelu_residual_rmsNorm [Nonempty T] {ε : ℝ} (hε : 0 < ε)
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, ∀ V ∈ 𝓝 (1 : Matrix d d ℝ), ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.mlp gelu (rmsNorm ε) hid) 1 θ' x
        = eval (Arch.mlp gelu (rmsNorm ε) hid) 1 θ x) →
        ∃ Q : GL d ℝ, (Q : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ ∧
          (Q : Matrix d d ℝ) ∈ V ∧ θ' = θ.cob (fun _ => Q) (fun _ => Q) := by
  sorry

end Skips
