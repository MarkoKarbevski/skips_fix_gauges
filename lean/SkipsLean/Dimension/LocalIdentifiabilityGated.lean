import SkipsLean.Dimension.OrbitNetwork
import SkipsLean.Dimension.ExpOrbitGated
import SkipsLean.Generic.Gated
import SkipsLean.Depth.GeluGatedTheorem

/-!
# Local identifiability up to the changes of basis and the rescalings: gated blocks

Paper (dimension paper): Definition 4.5, Proposition 4.6 and Corollary 5.3.

"Proposition 4.6 (The equality condition and local identifiability). Let the blocks be tanh, GELU,
SwiGLU, GeGLU or attention blocks, without normalization or under pre-RMSNorm. A network satisfies
the equality condition if and only if, at generic parameters, it is locally identifiable up to its
symmetries. Every symmetry that is needed is then close to the identity."

"Corollary 5.3 (Local identifiability). Without normalization or under pre-RMSNorm with `ε > 0`, in
the cases of Theorem 5.2, let `θ` be generic parameters. Every `θ'` near `θ` with the same function
is obtained from `θ` by matrices `G_0, …, G_L ∈ 𝒢` close to the identity, one per hidden state, as
in Proposition 3.2, and for SwiGLU and GeGLU blocks by a rescaling of the value of each hidden
unit, close to 1."

Stated here, for networks of gated blocks without skip connections (`s` is the number of hidden
units of the network):

* The direction of Proposition 4.6 from the equality condition to local identifiability, at one
  parameter, for a real-analytic gate: if `E` and the writes have rank `d`, no value column of a
  read vanishes (the conditions of Lemma B.1) and the functional dimension at `θ` is
  `P − (L+1) d² − s`, resp. `P − (L+1) d(d−1)/2 − s` under pre-RMSNorm with `ε > 0`, then every
  `θ'` near `θ` with the same function is `(θ.rescale c).cob G G` with factors `c > 0` near `1` and
  invertible (resp. orthogonal) `G_0, …, G_L` near the identity.
* Corollary 5.3 for SwiGLU and GeGLU blocks, without normalization and under pre-RMSNorm with
  `ε > 0`: this holds at almost every parameter.

The blocks without symmetries inside are in `Dimension/LocalIdentifiability.lean`; residual
networks in `Residual/LocalIdentifiability.lean` and `Residual/LocalIdentifiabilityGated.lean`.
All use `exists_mem_orbit_of_eval_eq` (`Dimension/OrbitNetwork.lean`). `θ.rescale c` divides the
value column of hidden unit `i` of block `ℓ` by `c ℓ i` and multiplies its write row by `c ℓ i`
(`Dimension/RescaleAction.lean`). Not stated here: the converse direction of Proposition 4.6 and
attention blocks.
-/

namespace Skips

open Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {σ : ℝ → ℝ} {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]

/-- **Proposition 4.6 for gated blocks, from the equality condition to local identifiability,
without normalization:** for a real-analytic gate `σ`, if `E` and the writes have rank `d`, no
value column of a read vanishes and `fd(θ) = P − (L+1) d² − s`, then every `θ'` near `θ` with the
same function is `θ` after a rescaling of the values of the hidden units by factors `c` near `1`
and a change of basis by invertible `G_0, …, G_L` near the identity. -/
theorem exists_cob_rescale_of_eval_eq_skipless_gated (hσ : AnalyticOnNhd ℝ σ Set.univ)
    (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d) (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d)
    (hv : ∀ ℓ i, (fun k => θ.read ℓ k (Sum.inr i)) ≠ 0)
    (hfd : funDim (Arch.gated σ id hid) 0 θ
        + ((L + 1) * Fintype.card d ^ 2 + ∑ ℓ, Fintype.card (hid ℓ))
      = Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)) :
    ∀ V ∈ 𝓝 (1 : Fin (L + 1) → Matrix d d ℝ), ∀ W ∈ 𝓝 (1 : ∀ ℓ, hid ℓ → ℝ), ∃ U ∈ 𝓝 θ,
      ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.gated σ id hid) 0 θ' x
        = eval (Arch.gated σ id hid) 0 θ x) →
        ∃ (G : Fin (L + 1) → GL d ℝ) (c : ∀ ℓ, hid ℓ → ℝ),
          (fun ℓ => (G ℓ : Matrix d d ℝ)) ∈ V ∧ c ∈ W ∧ (∀ ℓ i, 0 < c ℓ i) ∧
          θ' = (θ.rescale c).cob G G := by
  sorry

/-- **Proposition 4.6 for gated blocks, from the equality condition to local identifiability,
under pre-RMSNorm with `ε > 0`:** for a real-analytic gate `σ`, if `E` and the writes have rank
`d`, no value column of a read vanishes and `fd(θ) = P − (L+1) d(d−1)/2 − s`, then every `θ'` near
`θ` with the same function is `θ` after a rescaling of the values of the hidden units by factors
`c` near `1` and a change of basis by orthogonal `Q_0, …, Q_L` near the identity. -/
theorem exists_cob_rescale_of_eval_eq_skipless_gated_rmsNorm {ε : ℝ} (hε : 0 < ε)
    (hσ : AnalyticOnNhd ℝ σ Set.univ)
    (θ : Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d) (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d)
    (hv : ∀ ℓ i, (fun k => θ.read ℓ k (Sum.inr i)) ≠ 0)
    (hfd : funDim (Arch.gated σ (rmsNorm ε) hid) 0 θ
        + ((L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2) + ∑ ℓ, Fintype.card (hid ℓ))
      = Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)) :
    ∀ V ∈ 𝓝 (1 : Fin (L + 1) → Matrix d d ℝ), ∀ W ∈ 𝓝 (1 : ∀ ℓ, hid ℓ → ℝ), ∃ U ∈ 𝓝 θ,
      ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.gated σ (rmsNorm ε) hid) 0 θ' x
        = eval (Arch.gated σ (rmsNorm ε) hid) 0 θ x) →
        ∃ (Q : Fin (L + 1) → GL d ℝ) (c : ∀ ℓ, hid ℓ → ℝ),
          (∀ ℓ, (Q ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ) ∧
          (fun ℓ => (Q ℓ : Matrix d d ℝ)) ∈ V ∧ c ∈ W ∧ (∀ ℓ i, 0 < c ℓ i) ∧
          θ' = (θ.rescale c).cob Q Q := by
  sorry

/-- **Corollary 5.3 for SwiGLU blocks without normalization:** for `d_in, d_out ≥ d ≥ 2` and at
least `d` hidden units per block, at almost every parameter `θ`, every `θ'` near `θ` with the same
function is `θ` after a rescaling of the value of each hidden unit, close to `1`, and a change of
basis by invertible `G_0, …, G_L` near the identity. -/
theorem ae_exists_cob_rescale_of_eval_eq_swiglu_skipless [Nonempty T]
    (μ : Measure (Params (Arch.gated (T := T) (d := d) silu id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, ∀ V ∈ 𝓝 (1 : Fin (L + 1) → Matrix d d ℝ), ∀ W ∈ 𝓝 (1 : ∀ ℓ, hid ℓ → ℝ),
      ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.gated silu id hid) 0 θ' x
        = eval (Arch.gated silu id hid) 0 θ x) →
        ∃ (G : Fin (L + 1) → GL d ℝ) (c : ∀ ℓ, hid ℓ → ℝ),
          (fun ℓ => (G ℓ : Matrix d d ℝ)) ∈ V ∧ c ∈ W ∧ (∀ ℓ i, 0 < c ℓ i) ∧
          θ' = (θ.rescale c).cob G G := by
  sorry

/-- **Corollary 5.3 for SwiGLU blocks under pre-RMSNorm with `ε > 0`:** for `d_in, d_out ≥ d ≥ 2`
and at least `d` hidden units per block, at almost every parameter `θ`, every `θ'` near `θ` with the
same function is `θ` after a rescaling of the value of each hidden unit, close to `1`, and a change
of basis by orthogonal `Q_0, …, Q_L` near the identity. -/
theorem ae_exists_cob_rescale_of_eval_eq_swiglu_skipless_rmsNorm [Nonempty T] {ε : ℝ} (hε : 0 < ε)
    (μ : Measure (Params (Arch.gated (T := T) (d := d) silu (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, ∀ V ∈ 𝓝 (1 : Fin (L + 1) → Matrix d d ℝ), ∀ W ∈ 𝓝 (1 : ∀ ℓ, hid ℓ → ℝ),
      ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.gated silu (rmsNorm ε) hid) 0 θ' x
        = eval (Arch.gated silu (rmsNorm ε) hid) 0 θ x) →
        ∃ (Q : Fin (L + 1) → GL d ℝ) (c : ∀ ℓ, hid ℓ → ℝ),
          (∀ ℓ, (Q ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ) ∧
          (fun ℓ => (Q ℓ : Matrix d d ℝ)) ∈ V ∧ c ∈ W ∧ (∀ ℓ i, 0 < c ℓ i) ∧
          θ' = (θ.rescale c).cob Q Q := by
  sorry

/-- **Corollary 5.3 for GeGLU blocks without normalization:** for `d_in, d_out ≥ d ≥ 2` and at
least `d` hidden units per block, at almost every parameter `θ`, every `θ'` near `θ` with the same
function is `θ` after a rescaling of the value of each hidden unit, close to `1`, and a change of
basis by invertible `G_0, …, G_L` near the identity. -/
theorem ae_exists_cob_rescale_of_eval_eq_geglu_skipless [Nonempty T]
    (μ : Measure (Params (Arch.gated (T := T) (d := d) gelu id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, ∀ V ∈ 𝓝 (1 : Fin (L + 1) → Matrix d d ℝ), ∀ W ∈ 𝓝 (1 : ∀ ℓ, hid ℓ → ℝ),
      ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.gated gelu id hid) 0 θ' x
        = eval (Arch.gated gelu id hid) 0 θ x) →
        ∃ (G : Fin (L + 1) → GL d ℝ) (c : ∀ ℓ, hid ℓ → ℝ),
          (fun ℓ => (G ℓ : Matrix d d ℝ)) ∈ V ∧ c ∈ W ∧ (∀ ℓ i, 0 < c ℓ i) ∧
          θ' = (θ.rescale c).cob G G := by
  sorry

/-- **Corollary 5.3 for GeGLU blocks under pre-RMSNorm with `ε > 0`:** for `d_in, d_out ≥ d ≥ 2` and
at least `d` hidden units per block, at almost every parameter `θ`, every `θ'` near `θ` with the
same function is `θ` after a rescaling of the value of each hidden unit, close to `1`, and a change
of basis by orthogonal `Q_0, …, Q_L` near the identity. -/
theorem ae_exists_cob_rescale_of_eval_eq_geglu_skipless_rmsNorm [Nonempty T] {ε : ℝ} (hε : 0 < ε)
    (μ : Measure (Params (Arch.gated (T := T) (d := d) gelu (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, ∀ V ∈ 𝓝 (1 : Fin (L + 1) → Matrix d d ℝ), ∀ W ∈ 𝓝 (1 : ∀ ℓ, hid ℓ → ℝ),
      ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.gated gelu (rmsNorm ε) hid) 0 θ' x
        = eval (Arch.gated gelu (rmsNorm ε) hid) 0 θ x) →
        ∃ (Q : Fin (L + 1) → GL d ℝ) (c : ∀ ℓ, hid ℓ → ℝ),
          (∀ ℓ, (Q ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ) ∧
          (fun ℓ => (Q ℓ : Matrix d d ℝ)) ∈ V ∧ c ∈ W ∧ (∀ ℓ i, 0 < c ℓ i) ∧
          θ' = (θ.rescale c).cob Q Q := by
  sorry

end Skips
