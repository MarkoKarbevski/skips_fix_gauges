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

/-- A continuous left inverse of an injective continuous linear map into a finite-dimensional
space. -/
private lemma exists_leftInverse_lso {E Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
    {f' : E →L[ℝ] Z} (hinj : Function.Injective f') : ∃ L : Z →L[ℝ] E, ∀ x, L (f' x) = x := by
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective f'.toLinearMap
    (LinearMap.ker_eq_bot.2 hinj)
  exact ⟨LinearMap.toContinuousLinearMap g, fun x => LinearMap.congr_fun hg x⟩

/-- A map with an injective strict derivative between finite-dimensional spaces is injective
near the point (inverse function theorem for `L ∘ f`, `L` a left inverse of the derivative). -/
private lemma exists_injOn_lso {E Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
    {f : E → Z} {f' : E →L[ℝ] Z} {a : E} (hf : HasStrictFDerivAt f f' a)
    (hinj : Function.Injective f') : ∃ N ∈ 𝓝 a, Set.InjOn f N := by
  obtain ⟨L, hL⟩ := exists_leftInverse_lso hinj
  have hLf : HasStrictFDerivAt (L ∘ f) ((ContinuousLinearEquiv.refl ℝ E : E →L[ℝ] E)) a := by
    have h := L.hasStrictFDerivAt.comp a hf
    exact h.congr_fderiv (ContinuousLinearMap.ext fun x => by simp [hL])
  refine ⟨(hLf.toOpenPartialHomeomorph (L ∘ f)).source,
    (hLf.toOpenPartialHomeomorph (L ∘ f)).open_source.mem_nhds
      hLf.mem_toOpenPartialHomeomorph_source, ?_⟩
  intro x hx y hy hxy
  apply (hLf.toOpenPartialHomeomorph (L ∘ f)).injOn hx hy
  simp only [HasStrictFDerivAt.toOpenPartialHomeomorph_coe, Function.comp_apply, hxy]

/-- Step 1: `F' ∘ Φ' = 0`, since `F ∘ Φ` is constant near `0`. -/
private lemma comp_eq_zero_lso {P M Y : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup M] [NormedSpace ℝ M] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {F : P → Y} {F' : P →L[ℝ] Y} {Φ : M → P} {Φ' : M →L[ℝ] P} {θ₀ : P}
    (hF : HasStrictFDerivAt F F' θ₀) (hΦ : HasStrictFDerivAt Φ Φ' 0) (hΦ0 : Φ 0 = θ₀)
    (hconst : ∀ᶠ m in 𝓝 (0 : M), F (Φ m) = F θ₀) (m : M) : F' (Φ' m) = 0 := by
  have h1 : HasFDerivAt (F ∘ Φ) (F'.comp Φ') 0 := by
    rw [← hΦ0] at hF
    exact (hF.comp 0 hΦ).hasFDerivAt
  have h2 : HasFDerivAt (F ∘ Φ) (0 : M →L[ℝ] Y) 0 :=
    (hasFDerivAt_const (F θ₀) (0 : M)).congr_of_eventuallyEq hconst
  exact DFunLike.congr_fun (h1.unique h2) m

/-- Step 2: the kernel of `F'` is the range of `Φ'` (same dimension). -/
private lemma mem_range_lso {P M Y : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [FiniteDimensional ℝ P] [NormedAddCommGroup M] [NormedSpace ℝ M] [FiniteDimensional ℝ M]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {F' : P →L[ℝ] Y} {Φ' : M →L[ℝ] P} (h0 : ∀ m, F' (Φ' m) = 0)
    (hinj : Function.Injective Φ')
    (hdim : Module.finrank ℝ (LinearMap.ker F'.toLinearMap) = Module.finrank ℝ M)
    (v : P) (hv : F' v = 0) : ∃ m, Φ' m = v := by
  have hle : LinearMap.range Φ'.toLinearMap ≤ LinearMap.ker F'.toLinearMap := by
    rintro _ ⟨m, rfl⟩
    exact h0 m
  have heq := Submodule.eq_of_le_of_finrank_eq hle
    (by rw [LinearMap.finrank_range_of_inj (f := Φ'.toLinearMap) hinj, hdim])
  have hv' : v ∈ LinearMap.range Φ'.toLinearMap := heq ▸ hv
  exact hv'

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
  intro V hV
  -- Steps 1 and 2: the kernel of `F'` is the range of `Φ'`.
  have hrange := mem_range_lso (comp_eq_zero_lso hF hΦ hΦ0 hconst) hinj hdim
  -- A left inverse `Λ : P → M` of `Φ'` (in place of a projection onto the kernel).
  obtain ⟨Λ, hΛ⟩ := exists_leftInverse_lso hinj
  have hΛθ : HasStrictFDerivAt (fun θ => Λ (θ - θ₀)) Λ θ₀ := by
    have h := Λ.hasStrictFDerivAt.comp θ₀ ((hasStrictFDerivAt_id θ₀).sub_const θ₀)
    simpa using h
  -- Step 4: `Ψ θ = (F θ, Λ (θ - θ₀))` has an injective strict derivative, so it is injective
  -- on a neighborhood `N` of `θ₀`.
  have hΨ : HasStrictFDerivAt (fun θ => (F θ, Λ (θ - θ₀))) (F'.prod Λ) θ₀ := hF.prodMk hΛθ
  have hΨinj : Function.Injective (F'.prod Λ) := by
    refine (injective_iff_map_eq_zero (F'.prod Λ)).2 fun v hv => ?_
    obtain ⟨m, rfl⟩ := hrange v (congrArg Prod.fst hv)
    have hm : m = 0 := (hΛ m).symm.trans (congrArg Prod.snd hv)
    rw [hm, map_zero]
  obtain ⟨N, hN, hNinj⟩ := exists_injOn_lso hΨ hΨinj
  -- Step 5: `g m = Λ (Φ m - θ₀)` has the strict derivative `id` at `0`: it maps neighborhoods
  -- of `0` onto neighborhoods of `0`.
  have hg : HasStrictFDerivAt (fun m => Λ (Φ m - θ₀))
      ((ContinuousLinearEquiv.refl ℝ M : M →L[ℝ] M)) 0 := by
    have hΛθ' : HasStrictFDerivAt (fun θ => Λ (θ - θ₀)) Λ (Φ 0) := hΦ0 ▸ hΛθ
    have h := hΛθ'.comp 0 hΦ
    exact h.congr_fderiv (ContinuousLinearMap.ext fun m => by simp [hΛ])
  have hgmap := hg.map_nhds_eq_of_equiv
  -- Step 6.
  have hV' : V ∩ {m | F (Φ m) = F θ₀} ∩ Φ ⁻¹' N ∈ 𝓝 (0 : M) :=
    inter_mem (inter_mem hV hconst) (hΦ.continuousAt.preimage_mem_nhds (hΦ0 ▸ hN))
  have himg : (fun m => Λ (Φ m - θ₀)) '' (V ∩ {m | F (Φ m) = F θ₀} ∩ Φ ⁻¹' N) ∈
      𝓝 (Λ (θ₀ - θ₀)) := by
    have h := image_mem_map (m := fun m => Λ (Φ m - θ₀)) hV'
    rw [hgmap, hΦ0] at h
    exact h
  refine ⟨N ∩ (fun θ => Λ (θ - θ₀)) ⁻¹'
      ((fun m => Λ (Φ m - θ₀)) '' (V ∩ {m | F (Φ m) = F θ₀} ∩ Φ ⁻¹' N)),
    inter_mem hN (hΛθ.continuousAt.preimage_mem_nhds himg), fun θ' hθ' hFθ' => ?_⟩
  obtain ⟨m, ⟨⟨hmV, hmF⟩, hmN⟩, hgm⟩ := hθ'.2
  refine ⟨m, hmV, hNinj hmN hθ'.1 ?_⟩
  exact Prod.ext (hmF.trans hFθ'.symm) hgm

end Skips
