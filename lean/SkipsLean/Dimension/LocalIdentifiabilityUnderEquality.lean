import SkipsLean.Dimension.LocalIdentifiability

/-!
# The equality condition and local identifiability: the symmetries are close to the identity

Paper (dimension paper), Proposition 4.6: "Let the blocks be tanh, GELU, SwiGLU, GeGLU or
attention blocks, without normalization or under pre-RMSNorm. A network satisfies the equality
condition if and only if, at generic parameters, it is locally identifiable up to its symmetries.
Every symmetry that is needed is then close to the identity." (Skips paper, Proposition 4.5, has
the same last sentence.)

`Dimension/LocalIdentifiability.lean` has the last sentence at one parameter, under the rank
conditions of the proof (`exists_cob_of_eval_eq_skipless` and its twin with `_rmsNorm`).
Here it is one statement under the equality condition: if the bound is attained at almost every
parameter, then at almost every parameter `θ`, for every neighborhood `V` of the identity, every
`θ'` close enough to `θ` with the same function is the image of `θ` under changes of basis in `V`.
Stated for skipless networks of real-analytic blocks with no symmetry inside the blocks (tanh and
GELU blocks are of this kind), for `d_in ≥ d` and writes of at least `d` rows. The same for blocks
with symmetries inside (SwiGLU, GeGLU, attention), for residual networks and for networks with two
kinds of block: `Dimension/IdentifiableUnderEquality.lean`,
`Residual/IdentifiableUnderEquality.lean`, `Dimension/IdentifiableUnderEqualityTransformer.lean`.
-/

namespace Skips

open Matrix MeasureTheory Topology
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]

/-- **Proposition 4.6 of the dimension paper, last sentence, without normalization:** for a
skipless network of real-analytic blocks with `d_in ≥ d` and writes of at least `d` rows, if the
equality condition holds (`fd(θ) = P − (L+1) d²` at almost every `θ`), then at almost every `θ`,
for every neighborhood `V` of the identity there is a neighborhood `U` of `θ` such that every
`θ' ∈ U` with the same function is `θ.cob G G` with `G ∈ V`. -/
theorem ae_exists_cob_of_eval_eq_skipless_of_ae_funDim (A : Arch T d L) (hA : A.χ = id)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ)
    (μ : Measure (Params A dIn dOut)) [μ.IsAddHaarMeasure]
    (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hw : ∀ ℓ, Fintype.card d ≤ Fintype.card (A.w ℓ))
    (hfd : ∀ᵐ θ ∂μ, funDim A 0 θ + (L + 1) * Fintype.card d ^ 2
      = Module.finrank ℝ (Params A dIn dOut)) :
    ∀ᵐ θ ∂μ, ∀ V ∈ 𝓝 (1 : Fin (L + 1) → Matrix d d ℝ), ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval A 0 θ' x = eval A 0 θ x) →
        ∃ G : Fin (L + 1) → GL d ℝ, (fun ℓ => (G ℓ : Matrix d d ℝ)) ∈ V ∧ θ' = θ.cob G G := by
  -- at almost every `θ`, `E` and the writes have rank `d` and the bound is attained
  filter_upwards [ae_rank_E_write μ hdIn hw, hfd] with θ hθ hθfd
  exact exists_cob_of_eval_eq_skipless A hA hf θ hθ.1 hθ.2 hθfd

/-- **Proposition 4.6 of the dimension paper, last sentence, under pre-RMSNorm with `ε > 0`:** for
a skipless network of real-analytic blocks with `d_in ≥ d` and writes of at least `d` rows, if the
equality condition holds (`fd(θ) = P − (L+1) d(d−1)/2` at almost every `θ`), then at almost every
`θ`, for every neighborhood `V` of the identity there is a neighborhood `U` of `θ` such that every
`θ' ∈ U` with the same function is `θ.cob Q Q` with orthogonal `Q_ℓ`, `Q ∈ V`. -/
theorem ae_exists_cob_of_eval_eq_skipless_rmsNorm_of_ae_funDim (A : Arch T d L) {ε : ℝ}
    (hε : 0 < ε) (hA : A.χ = rmsNorm ε) (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ)
    (μ : Measure (Params A dIn dOut)) [μ.IsAddHaarMeasure]
    (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hw : ∀ ℓ, Fintype.card d ≤ Fintype.card (A.w ℓ))
    (hfd : ∀ᵐ θ ∂μ, funDim A 0 θ + (L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2)
      = Module.finrank ℝ (Params A dIn dOut)) :
    ∀ᵐ θ ∂μ, ∀ V ∈ 𝓝 (1 : Fin (L + 1) → Matrix d d ℝ), ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval A 0 θ' x = eval A 0 θ x) →
        ∃ Q : Fin (L + 1) → GL d ℝ,
          (∀ ℓ, (Q ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ) ∧
          (fun ℓ => (Q ℓ : Matrix d d ℝ)) ∈ V ∧ θ' = θ.cob Q Q := by
  -- at almost every `θ`, `E` and the writes have rank `d` and the bound is attained
  filter_upwards [ae_rank_E_write μ hdIn hw, hfd] with θ hθ hθfd
  exact exists_cob_of_eval_eq_skipless_rmsNorm A hε hA hf θ hθ.1 hθ.2 hθfd

end Skips
