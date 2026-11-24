import SkipsLean.Generic.LevelSetOrbit
import SkipsLean.Generic.Params
import SkipsLean.Dimension.GenericRank
import SkipsLean.Depth.Tanh
import SkipsLean.Depth.TanhRMS
import SkipsLean.Depth.GeluGatedTheorem

/-!
# Local identifiability up to the changes of basis

Paper (dimension paper): Definition 4.5, Proposition 4.6 and Corollary 5.3.

"Definition 4.5 (Identifiability up to symmetries). A network is identifiable up to its symmetries
at `θ` if every `θ'` with `F_{θ'} = F_θ` is the image of `θ` under a symmetry: a change of basis of
Proposition 3.2, a symmetry inside a block, or a composition of these. It is locally identifiable at
`θ` if this holds for every `θ'` in some neighborhood of `θ`."

"Proposition 4.6 (The equality condition and local identifiability). Let the blocks be tanh, GELU,
SwiGLU, GeGLU or attention blocks, without normalization or under pre-RMSNorm. A network satisfies
the equality condition if and only if, at generic parameters, it is locally identifiable up to its
symmetries. Every symmetry that is needed is then close to the identity."

"Corollary 5.3 (Local identifiability). Without normalization or under pre-RMSNorm with `ε > 0`, in
the cases of Theorem 5.2, let `θ` be generic parameters. Every `θ'` near `θ` with the same function
is obtained from `θ` by matrices `G_0, …, G_L ∈ 𝒢` close to the identity, one per hidden state, as
in Proposition 3.2, and for SwiGLU and GeGLU blocks by a rescaling of the value of each hidden
unit, close to 1."

Stated here, for networks without skip connections whose blocks have no symmetries inside
(`s = 0`: tanh and GELU blocks):

* The direction of Proposition 4.6 from the equality condition to local identifiability, at one
  parameter: for real-analytic blocks, if `E` and the writes have rank `d` and the functional
  dimension at `θ` is `P − (L+1) d²` (without normalization), resp. `P − (L+1) d(d−1)/2` (under
  pre-RMSNorm with `ε > 0`), then every `θ'` near `θ` with the same function is `θ.cob G G` with
  invertible (resp. orthogonal) `G_0, …, G_L` near the identity: for every neighborhood `V` of the
  identity there is a neighborhood `U` of `θ`.
* Corollary 5.3 for tanh blocks without normalization and for tanh and GELU blocks under
  pre-RMSNorm with `ε > 0`: this holds at almost every parameter.

Not stated here: the converse direction of Proposition 4.6 (it uses Sard's theorem), the blocks
with symmetries inside (SwiGLU, GeGLU, attention), and networks with skip connections.
`θ.cob G G` is the change of basis of Proposition 3.2 (`Symmetry/ChangeOfBasis.lean`): `E G_0`,
`G_{ℓ−1}⁻¹ W_read^ℓ`, `W_write^ℓ G_ℓ`, `G_L⁻¹ D`.
-/

namespace Skips

open Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]

/-- **Proposition 4.6, from the equality condition to local identifiability, without
normalization:** for real-analytic blocks, if `E` and the writes have rank `d` and
`fd(θ) = P − (L+1) d²`, then for every neighborhood `V` of the identity there is a neighborhood `U`
of `θ` such that every `θ' ∈ U` with the same function is `θ.cob G G` with `G ∈ V`. -/
theorem exists_cob_of_eval_eq_skipless (A : Arch T d L) (hA : A.χ = id)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (θ : Params A dIn dOut)
    (hE : θ.E.rank = Fintype.card d) (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d)
    (hfd : funDim A 0 θ + (L + 1) * Fintype.card d ^ 2 = Module.finrank ℝ (Params A dIn dOut)) :
    ∀ V ∈ 𝓝 (1 : Fin (L + 1) → Matrix d d ℝ), ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval A 0 θ' x = eval A 0 θ x) →
        ∃ G : Fin (L + 1) → GL d ℝ, (fun ℓ => (G ℓ : Matrix d d ℝ)) ∈ V ∧ θ' = θ.cob G G := by
  sorry

/-- **Proposition 4.6, from the equality condition to local identifiability, under pre-RMSNorm
with `ε > 0`:** for real-analytic blocks, if `E` and the writes have rank `d` and
`fd(θ) = P − (L+1) d(d−1)/2`, then for every neighborhood `V` of the identity there is a
neighborhood `U` of `θ` such that every `θ' ∈ U` with the same function is `θ.cob Q Q` with
orthogonal `Q_ℓ`, `Q ∈ V`. -/
theorem exists_cob_of_eval_eq_skipless_rmsNorm (A : Arch T d L) {ε : ℝ} (hε : 0 < ε)
    (hA : A.χ = rmsNorm ε) (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ)
    (θ : Params A dIn dOut) (hE : θ.E.rank = Fintype.card d)
    (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d)
    (hfd : funDim A 0 θ + (L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2)
      = Module.finrank ℝ (Params A dIn dOut)) :
    ∀ V ∈ 𝓝 (1 : Fin (L + 1) → Matrix d d ℝ), ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval A 0 θ' x = eval A 0 θ x) →
        ∃ Q : Fin (L + 1) → GL d ℝ,
          (∀ ℓ, (Q ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ) ∧
          (fun ℓ => (Q ℓ : Matrix d d ℝ)) ∈ V ∧ θ' = θ.cob Q Q := by
  sorry

variable {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]

/-- **Corollary 5.3 for tanh blocks without normalization:** for `d_in, d_out ≥ d ≥ 2` and at least
`d` hidden units per block, at almost every parameter `θ`: every `θ'` near `θ` with the same
function is `θ.cob G G` with invertible `G_0, …, G_L` near the identity. -/
theorem ae_exists_cob_of_eval_eq_tanh_skipless [Nonempty T]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) Real.tanh id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, ∀ V ∈ 𝓝 (1 : Fin (L + 1) → Matrix d d ℝ), ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.mlp Real.tanh id hid) 0 θ' x
        = eval (Arch.mlp Real.tanh id hid) 0 θ x) →
        ∃ G : Fin (L + 1) → GL d ℝ, (fun ℓ => (G ℓ : Matrix d d ℝ)) ∈ V ∧ θ' = θ.cob G G := by
  sorry

/-- **Corollary 5.3 for tanh blocks under pre-RMSNorm with `ε > 0`:** at almost every parameter
`θ`, every `θ'` near `θ` with the same function is `θ.cob Q Q` with orthogonal `Q_0, …, Q_L` near
the identity. -/
theorem ae_exists_cob_of_eval_eq_tanh_skipless_rmsNorm [Nonempty T] {ε : ℝ} (hε : 0 < ε)
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) Real.tanh (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, ∀ V ∈ 𝓝 (1 : Fin (L + 1) → Matrix d d ℝ), ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.mlp Real.tanh (rmsNorm ε) hid) 0 θ' x
        = eval (Arch.mlp Real.tanh (rmsNorm ε) hid) 0 θ x) →
        ∃ Q : Fin (L + 1) → GL d ℝ,
          (∀ ℓ, (Q ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ) ∧
          (fun ℓ => (Q ℓ : Matrix d d ℝ)) ∈ V ∧ θ' = θ.cob Q Q := by
  sorry

/-- **Corollary 5.3 for GELU blocks under pre-RMSNorm with `ε > 0`:** at almost every parameter
`θ`, every `θ'` near `θ` with the same function is `θ.cob Q Q` with orthogonal `Q_0, …, Q_L` near
the identity. -/
theorem ae_exists_cob_of_eval_eq_gelu_skipless_rmsNorm [Nonempty T] {ε : ℝ} (hε : 0 < ε)
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, ∀ V ∈ 𝓝 (1 : Fin (L + 1) → Matrix d d ℝ), ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.mlp gelu (rmsNorm ε) hid) 0 θ' x
        = eval (Arch.mlp gelu (rmsNorm ε) hid) 0 θ x) →
        ∃ Q : Fin (L + 1) → GL d ℝ,
          (∀ ℓ, (Q ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ) ∧
          (fun ℓ => (Q ℓ : Matrix d d ℝ)) ∈ V ∧ θ' = θ.cob Q Q := by
  sorry

end Skips
