import SkipsLean.Generic.LevelSetOrbit
import SkipsLean.Dimension.GenericRank

/-!
# A family of symmetries of the dimension of the redundancy reaches every nearby parameter

Paper (dimension paper): Appendix B, proof of Proposition 4.6; (skips paper): Proposition 4.5,
which is the same statement for networks with skip connections.

"Take `θ` at which the rank on `X` is `r` and the symmetries act locally freely […]. The changes of
basis of Proposition 3.2, the rescalings and the changes of basis inside the heads form a Lie group
of dimension `k`, which acts smoothly. It acts locally freely at `θ`, so the map that sends an
element of the group to the image of `θ` under it is an immersion near the identity, and it maps a
neighborhood of the identity onto a manifold `O ⊂ Z` of dimension `k`. If `r = P − k`, then `O` is
open in `Z`, since the two have the same dimension. So every `θ'` close to `θ` with
`F_{θ'} = F_θ` is the image of `θ` under a symmetry close to the identity."

Stated here, once for all kinds of network (any stream matrices `S`, any real-analytic maps
`f_ℓ` and `χ`): let `Φ : M → Params` be a family of parameters through `θ = Φ(0)`, strictly
differentiable at `0` with an injective derivative, with `F_{Φ(m)} = F_θ` for `m` near `0`, and let
`fd(θ) + dim M = P`. Then for every neighborhood `V` of `0` there is a neighborhood `U` of `θ` such
that every `θ' ∈ U` with the same function is `Φ(m)` with `m ∈ V`.

It follows from `exists_mem_orbit_of_level_set` (`Generic/LevelSetOrbit.lean`) on a batch `X` on
which the rank of the Jacobian at `θ` is the functional dimension. The statements on local
identifiability (`Dimension/LocalIdentifiability.lean`, `Residual/LocalIdentifiability.lean`, and
the two files for gated blocks) apply it to the changes of basis and the rescalings.
-/

namespace Skips

open Matrix Filter Topology
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]

/-- **Proof of Proposition 4.6 (dimension paper) and of Proposition 4.5 (skips paper), from the
equality condition to local identifiability, for any family of symmetries:** if the family
`Φ : M → Params` passes through `θ = Φ 0`, is strictly differentiable at `0` with an injective
derivative, preserves the function near `0`, and `fd(θ) + dim M = P`, then every `θ'` near `θ`
with the same function is `Φ m` with `m` near `0`. -/
theorem exists_mem_orbit_of_eval_eq (A : Arch T d L) (S : Fin L → Matrix d d ℝ)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (hχ : AnalyticOnNhd ℝ A.χ Set.univ)
    (θ : Params A dIn dOut)
    {M : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M] [FiniteDimensional ℝ M]
    {Φ : M → Params A dIn dOut} {Φ' : M →L[ℝ] Params A dIn dOut}
    (hΦ : HasStrictFDerivAt Φ Φ' 0) (hΦ0 : Φ 0 = θ) (hinj : Function.Injective Φ')
    (hconst : ∀ᶠ m in 𝓝 (0 : M), ∀ x : Matrix T dIn ℝ, eval A S (Φ m) x = eval A S θ x)
    (hfd : funDim A S θ + Module.finrank ℝ M = Module.finrank ℝ (Params A dIn dOut)) :
    ∀ V ∈ 𝓝 (0 : M), ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval A S θ' x = eval A S θ x) → ∃ m ∈ V, Φ m = θ' := by
  sorry

end Skips
