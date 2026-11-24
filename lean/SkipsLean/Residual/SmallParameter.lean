import SkipsLean.Imports
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# The rank of a Jacobian along a small parameter

Paper (skips paper): proof of Lemma A.27, its first paragraph and its last paragraph ("The
rank"). There `J_τ` is the Jacobian of the outputs at the parameters `θ_τ`, `S_τ` divides some
coordinates of a direction by `τ`, `rank J_τ = rank (J_τ S_τ)` for `τ ≠ 0`, the limit
`J_0 = lim_{τ → 0} J_τ S_τ` exists, and, the rank being lower semicontinuous,
`rank J_τ ≥ rank J_0` for all small `τ ≠ 0`.

This file states that step without networks, for a map `G τ θ` of a real number `τ` and of
parameters `θ` that is twice continuously differentiable in `(τ, θ)`. The coordinates that `S_τ`
divides by `τ` are given by a continuous linear map `π` on the parameters (`π η` is the part of the
direction `η` that is divided), and the hypothesis is that `G 0` does not move along them at `θ`.
Then, as `τ → 0`,

  `D_θ G(τ, θ) ((η - π η) + τ⁻¹ π η) → D_θ G(0, θ) (η - π η) + D_θ (∂_τ G(0, ·))(θ) (π η)`,

since the second derivative of `G` is symmetric. The right-hand side is `J_0 η`.

In the paper `G τ θ` is the batch of outputs at `θ_τ`; the derivative of `θ ↦ θ_τ` is invertible for
`τ ≠ 0`, so the rank of `D_θ G(τ, θ)` is the rank of `J_τ`. Here only "the rank of a composition is
at most the rank of the outer map" is used, which needs no inverse.
-/

namespace Skips

open Filter Topology

variable {P Y : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]

omit [FiniteDimensional ℝ P] [FiniteDimensional ℝ Y] in
/-- Steps 1 to 3: for a fixed direction `w`, the map `τ ↦ D_θ G(τ, θ) w` has derivative
`D_θ (∂_τ G(0, ·))(θ) w` at `τ = 0`, by the symmetry of the second derivative of
`F (τ, θ') = G τ θ'`. -/
private theorem hasDerivAt_fderiv_small_parameter (G : ℝ → P → Y)
    (hG : ContDiff ℝ 2 (fun p : ℝ × P => G p.1 p.2)) (θ w : P) :
    HasDerivAt (fun τ => fderiv ℝ (G τ) θ w)
      (fderiv ℝ (fun θ' => deriv (fun τ => G τ θ') 0) θ w) 0 := by
  set F : ℝ × P → Y := fun p => G p.1 p.2 with hF
  set A : ℝ × P → (ℝ × P →L[ℝ] Y) := fderiv ℝ F with hA
  have hFd : ∀ p, HasFDerivAt F (A p) p := fun p =>
    ((hG.differentiable (by norm_num)) p).hasFDerivAt
  have hA1 : ContDiff ℝ 1 A := hG.fderiv_right (by norm_num)
  have hAd : ∀ p, HasFDerivAt A (fderiv ℝ A p) p := fun p =>
    ((hA1.differentiable (by norm_num)) p).hasFDerivAt
  -- step 1: `D_θ G(τ, θ') = D F(τ, θ') ∘ inr`
  have h1 : ∀ τ θ', fderiv ℝ (G τ) θ' = (A (τ, θ')).comp (ContinuousLinearMap.inr ℝ ℝ P) := by
    intro τ θ'
    have hc := (hFd (τ, θ')).comp θ' (hasFDerivAt_prodMk_right (𝕜 := ℝ) τ θ')
    exact hc.fderiv
  -- `∂_τ G(0, θ') = D F(0, θ') (1, 0)`
  have h2 : ∀ θ', deriv (fun τ => G τ θ') 0 = A (0, θ') (1, 0) := by
    intro θ'
    have hin : HasDerivAt (fun τ : ℝ => (τ, θ')) ((1 : ℝ), (0 : P)) 0 :=
      (hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_const (0 : ℝ) θ')
    have hc := (hFd (0, θ')).comp_hasDerivAt (0 : ℝ) hin
    exact hc.deriv
  -- the derivative in `τ` of `D F(τ, θ) (0, w)`
  have h3 : HasDerivAt (fun τ => A (τ, θ) (0, w)) (fderiv ℝ A (0, θ) (1, 0) (0, w)) 0 := by
    have hin : HasDerivAt (fun τ : ℝ => (τ, θ)) ((1 : ℝ), (0 : P)) 0 :=
      (hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_const (0 : ℝ) θ)
    have hc := (hAd (0, θ)).comp_hasDerivAt (0 : ℝ) hin
    have hc2 := (ContinuousLinearMap.apply ℝ Y ((0 : ℝ), w)).hasFDerivAt.comp_hasDerivAt
      (0 : ℝ) hc
    exact hc2
  -- step 3: symmetry of the second derivative
  have hsymm : fderiv ℝ A (0, θ) (1, 0) (0, w) = fderiv ℝ A (0, θ) (0, w) (1, 0) :=
    (hG.contDiffAt.isSymmSndFDerivAt (by simp)) (1, 0) (0, w)
  -- the derivative in `θ'` of `∂_τ G(0, θ')`
  have h4 : fderiv ℝ (fun θ' => deriv (fun τ => G τ θ') 0) θ w
      = fderiv ℝ A (0, θ) (0, w) (1, 0) := by
    have he : (fun θ' => deriv (fun τ => G τ θ') 0) = fun θ' => A (0, θ') (1, 0) :=
      funext h2
    have hc := (hAd (0, θ)).comp θ (hasFDerivAt_prodMk_right (𝕜 := ℝ) (0 : ℝ) θ)
    have hc2 := (ContinuousLinearMap.apply ℝ Y ((1 : ℝ), (0 : P))).hasFDerivAt.comp θ hc
    have hc3 : HasFDerivAt (fun θ' => A (0, θ') (1, 0))
        ((ContinuousLinearMap.apply ℝ Y ((1 : ℝ), (0 : P))).comp
          ((fderiv ℝ A (0, θ)).comp (ContinuousLinearMap.inr ℝ ℝ P))) θ := hc2
    rw [he, hc3.fderiv]
    rfl
  have he : (fun τ => fderiv ℝ (G τ) θ w) = fun τ => A (τ, θ) (0, w) := by
    funext τ
    rw [h1]
    rfl
  rw [he, h4, ← hsymm]
  exact h3

/-- **Proof of Lemma A.27 of the skips paper, "`J_τ S_τ → J_0`" and "the rank is lower
semicontinuous", without networks.** Let `G τ θ` be twice continuously differentiable in `(τ, θ)`,
and let `G 0` have derivative zero at `θ` along every direction `π η`. Then for all small `τ ≠ 0`
the rank of `D_θ G(τ, θ)` is at least the rank of the limit
`J_0 η = D_θ G(0, θ) (η - π η) + D_θ (∂_τ G(0, ·))(θ) (π η)`. -/
theorem eventually_finrank_range_le_of_small_parameter (G : ℝ → P → Y)
    (hG : ContDiff ℝ 2 (fun p : ℝ × P => G p.1 p.2)) (π : P →L[ℝ] P) (θ : P)
    (h0 : ∀ η, fderiv ℝ (G 0) θ (π η) = 0) :
    ∀ᶠ τ in 𝓝[≠] (0 : ℝ),
      Module.finrank ℝ (LinearMap.range
          ((fderiv ℝ (G 0) θ).comp (ContinuousLinearMap.id ℝ P - π)
            + (fderiv ℝ (fun θ' => deriv (fun τ => G τ θ') 0) θ).comp π).toLinearMap)
        ≤ Module.finrank ℝ (LinearMap.range (fderiv ℝ (G τ) θ).toLinearMap) := by
  -- the limit `J_0`
  set K0 : P →L[ℝ] Y := (fderiv ℝ (G 0) θ).comp (ContinuousLinearMap.id ℝ P - π)
      + (fderiv ℝ (fun θ' => deriv (fun τ => G τ θ') 0) θ).comp π with hK0
  set r := Module.finrank ℝ (LinearMap.range K0.toLinearMap) with hr
  -- step 5: `r` directions `v i` whose images `J_0 v i` are linearly independent
  let b := Module.finBasis ℝ (LinearMap.range K0.toLinearMap)
  have hb : ∀ i, ∃ v, K0 v = (b i : Y) := fun i => LinearMap.mem_range.1 (b i).2
  choose v hv using hb
  have hli0 : LinearIndependent ℝ (fun i => K0 (v i)) := by
    have hl := b.linearIndependent.map' (LinearMap.range K0.toLinearMap).subtype
      (Submodule.ker_subtype _)
    convert hl using 1
    funext i
    exact hv i
  -- step 4: `J_τ S_τ v i → J_0 v i` as `τ → 0`, `τ ≠ 0`
  set f : ℝ → Fin r → Y := fun τ i => fderiv ℝ (G τ) θ ((v i - π (v i)) + τ⁻¹ • π (v i))
    with hf
  have htend : Tendsto f (𝓝[≠] 0) (𝓝 (fun i => K0 (v i))) := by
    refine tendsto_pi_nhds.2 fun i => ?_
    -- the part `η - π η`: continuity at `0`
    have ha := ((hasDerivAt_fderiv_small_parameter G hG θ (v i - π (v i))).continuousAt.tendsto
      ).mono_left (nhdsWithin_le_nhds (s := {(0 : ℝ)}ᶜ))
    -- the part `τ⁻¹ π η`: a slope, since `D_θ G(0, θ) (π η) = 0`
    have hs := (hasDerivAt_fderiv_small_parameter G hG θ (π (v i))).tendsto_slope_zero
    simp only [zero_add, h0, sub_zero] at hs
    have hsum := ha.add hs
    convert hsum using 1
    · funext τ
      simp only [hf, map_add, map_smul]
    · simp only [hK0, _root_.add_apply, ContinuousLinearMap.comp_apply,
        _root_.sub_apply, ContinuousLinearMap.id_apply]
  -- linear independence is an open condition
  have hev : ∀ᶠ τ in 𝓝[≠] (0 : ℝ), LinearIndependent ℝ (f τ) :=
    htend.eventually (isOpen_setOfPred_linearIndependent.mem_nhds hli0)
  filter_upwards [hev] with τ hτ
  -- the `f τ i` lie in the range of `D_θ G(τ, θ)`
  calc r = Fintype.card (Fin r) := (Fintype.card_fin r).symm
    _ = Module.finrank ℝ (Submodule.span ℝ (Set.range (f τ))) := (finrank_span_eq_card hτ).symm
    _ ≤ Module.finrank ℝ (LinearMap.range (fderiv ℝ (G τ) θ).toLinearMap) :=
      Submodule.finrank_mono (Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact ⟨_, rfl⟩))

/-- **The same step in the form used for Lemma A.27,** by the kernel of the limit: if every
direction `η` with `J_0 η = 0` lies in a subspace `V`, then for all small `τ ≠ 0` the rank of
`D_θ G(τ, θ)` is at least `dim P - dim V`. -/
theorem eventually_finrank_le_of_small_parameter (G : ℝ → P → Y)
    (hG : ContDiff ℝ 2 (fun p : ℝ × P => G p.1 p.2)) (π : P →L[ℝ] P) (θ : P)
    (h0 : ∀ η, fderiv ℝ (G 0) θ (π η) = 0) (V : Submodule ℝ P)
    (hV : ∀ η, fderiv ℝ (G 0) θ (η - π η)
        + fderiv ℝ (fun θ' => deriv (fun τ => G τ θ') 0) θ (π η) = 0 → η ∈ V) :
    ∀ᶠ τ in 𝓝[≠] (0 : ℝ),
      Module.finrank ℝ P
        ≤ Module.finrank ℝ (LinearMap.range (fderiv ℝ (G τ) θ).toLinearMap)
          + Module.finrank ℝ V := by
  filter_upwards [eventually_finrank_range_le_of_small_parameter G hG π θ h0] with τ hτ
  set K0 : P →L[ℝ] Y := (fderiv ℝ (G 0) θ).comp (ContinuousLinearMap.id ℝ P - π)
      + (fderiv ℝ (fun θ' => deriv (fun τ => G τ θ') 0) θ).comp π with hK0
  -- the kernel of `J_0` lies in `V`
  have hker : LinearMap.ker K0.toLinearMap ≤ V := fun η hη => hV η hη
  -- rank–nullity for `J_0`
  have h1 := LinearMap.finrank_range_add_finrank_ker K0.toLinearMap
  have h2 := Submodule.finrank_mono hker
  omega

end Skips
