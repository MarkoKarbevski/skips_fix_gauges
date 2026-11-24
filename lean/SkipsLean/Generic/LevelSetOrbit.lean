import SkipsLean.Imports

/-!
# An orbit of the dimension of the kernel fills the level set near a point

Paper (dimension paper): Appendix B, proof of Proposition 4.6 (the equality condition and local
identifiability), the direction from the equality condition to local identifiability:

"Take `θ` at which the rank on `X` is `r` and the symmetries act locally freely […]. By the
constant rank theorem, after shrinking `U`, the set `Z = {θ' ∈ U : F_X(θ') = F_X(θ)}` is a
connected manifold of dimension `P − r`, whose tangent space at each point is the kernel of the
Jacobian. […] The changes of basis of Proposition 3.2, the rescalings and the changes of basis
inside the heads form a Lie group of dimension `k`, which acts smoothly. It acts locally freely at
`θ`, so the map that sends an element of the group to the image of `θ` under it is an immersion
near the identity, and it maps a neighborhood of the identity onto a manifold `O ⊂ Z` of dimension
`k`. If `r = P − k`, then `O` is open in `Z`, since the two have the same dimension. So every `θ'`
close to `θ` with `F_{θ'} = F_θ` is the image of `θ` under a symmetry close to the identity."

Stated here without manifolds and without the constant rank theorem, for maps between
finite-dimensional real spaces. `F` is the map whose level set is considered (the outputs on a
batch), strictly differentiable at `θ₀` with derivative `F'`; `Φ` parametrizes the orbit near
`θ₀ = Φ 0` (the image of `θ₀` under the symmetries near the identity, in coordinates `m ∈ M`),
strictly differentiable at `0` with an injective derivative ("acts locally freely"), and `F ∘ Φ` is
constant near `0` (the symmetries preserve the function). If the kernel of `F'` has the dimension
of `M` (`r = P − k`), then every `θ'` near `θ₀` with `F θ' = F θ₀` is `Φ m` for an `m` near `0`.
(With the projection `ρ` onto the range of `F'` and a projection `L` onto its kernel `K`, the map
`θ ↦ (ρ (F θ), L (θ − θ₀))` is a local homeomorphism at `θ₀`, and `m ↦ L (Φ m − θ₀)` is one at `0`
onto a neighborhood of `0` in `K`; the level set of `ρ ∘ F` is a graph over `K`, and the orbit
covers it.)
-/

namespace Skips

open Filter Topology

/-- **"`O` is open in `Z`, since the two have the same dimension":** let `F` be strictly
differentiable at `θ₀` with derivative `F'`, let `Φ` be strictly differentiable at `0` with an
injective derivative `Φ'`, `Φ 0 = θ₀`, and `F (Φ m) = F θ₀` for `m` near `0`. If the kernel of `F'`
has the dimension of the space `M` of the `m`, then for every neighborhood `V` of `0` in `M` there
is a neighborhood `U` of `θ₀` such that every `θ' ∈ U` with `F θ' = F θ₀` is `Φ m` for some
`m ∈ V`. -/
theorem exists_mem_orbit_of_level_set
    {P M Y : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    [NormedAddCommGroup M] [NormedSpace ℝ M] [FiniteDimensional ℝ M]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    {F : P → Y} {F' : P →L[ℝ] Y} {Φ : M → P} {Φ' : M →L[ℝ] P} {θ₀ : P}
    (hF : HasStrictFDerivAt F F' θ₀) (hΦ : HasStrictFDerivAt Φ Φ' 0) (hΦ0 : Φ 0 = θ₀)
    (hinj : Function.Injective Φ') (hconst : ∀ᶠ m in 𝓝 (0 : M), F (Φ m) = F θ₀)
    (hdim : Module.finrank ℝ (LinearMap.ker F'.toLinearMap) = Module.finrank ℝ M) :
    ∀ V ∈ 𝓝 (0 : M), ∃ U ∈ 𝓝 θ₀, ∀ θ' ∈ U, F θ' = F θ₀ → ∃ m ∈ V, Φ m = θ' := by
  sorry

end Skips
