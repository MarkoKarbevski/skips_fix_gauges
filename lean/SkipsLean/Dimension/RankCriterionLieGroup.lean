import SkipsLean.Dimension.RankCriterion
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# The rank criterion, with the Lie group

Paper (skips paper), Lemma A.26 (A rank criterion): "Let `{F_θ}_{θ ∈ ℝ^P}` and
`{G_η}_{η ∈ ℝ^{P'}}` be two parametrized families of maps `ℝ^{T × d_in} → ℝ^{T × d_out}` such
that, for every input `x`, `F_θ(x)` is real-analytic in `θ` and `G_η(x)` is real-analytic in `η`.
Let a Lie group `H` act smoothly on `ℝ^{P'}`, written `η ↦ a · η` for `a ∈ H`, such that
`G_{a·η} = G_η` for all `a ∈ H` and all `η ∈ ℝ^{P'}`, and such that the orbit
`H · η = {a · η : a ∈ H}` has dimension at least `k` at generic `η`. Suppose that at some `θ_0`
the Jacobian of `θ ↦ (F_θ(x))_{x ∈ X}` has rank greater than `P' − k` on some finite batch `X`.
(i) For almost every `θ`, no `η` satisfies `F_θ = G_η`. (ii) If the outputs `G_η(x)`, `x ∈ X`,
are definable functions of `η`, then for almost every `θ` there is a `δ > 0` such that every `η`
has `‖F_θ(x) − G_η(x)‖ ≥ δ` at some `x ∈ X`." Its proof begins: "At generic `η` the map `G_X` is
constant along the orbit `H · η`, since `G_{a·η} = G_η`, and this orbit has dimension at least
`k`. So the Jacobian of `G_X` has rank at most `r_0 = P' − k`; the rank is lower semicontinuous,
so the bound holds at every `η`."

`Dimension/RankCriterion.lean` has the lemma from the bound `rank DG ≤ r_0` at every parameter.
Here the two sentences that give this bound, and the lemma in the paper's form:

* `H` is a Lie group in the sense of Mathlib (`LieGroup I ∞ H`, on any model), acting on the
  parameters `P'` of the second family (`MulAction H P'`), and "acts smoothly" is the smoothness of
  `(a, η) ↦ a · η`.
* `orbitDim I η`: the dimension of the orbit `H · η`, as the rank of the derivative of
  `a ↦ a · η` at the identity. (For a smooth action of a Lie group the orbit is an immersed
  submanifold, the image of `H / H_η` under an injective immersion, and its dimension is this
  rank; the orbit is not built as a manifold here.)
* `finrank_range_fderiv_add_orbitDim_le`: "the map `G_X` is constant along the orbit […] So the
  Jacobian of `G_X` has rank at most `P' − k`", at one `η`, written with a sum.
* `finrank_range_fderiv_le_of_ae`: "the rank is lower semicontinuous, so the bound holds at every
  `η`", for any continuously differentiable map and any Haar measure.
* `finrank_range_fderiv_add_le_of_ae_orbitDim`: the two together.
* `ae_forall_ne_of_lieGroup_action`, `ae_exists_pos_le_norm_sub_of_lieGroup_action`: parts (i)
  and (ii) for two families of maps on any set of inputs with values in a finite-dimensional
  space. "Generic" is "for almost every `η`", for a Haar measure of `P'`; "rank greater than
  `P' − k`" is written `P' < rank + k`. Sard's theorem and, in (ii), the property of definable
  sets are the hypotheses from the literature of `Dimension/RankCriterion.lean`.
-/

namespace Skips

open MeasureTheory
open scoped Manifold ContDiff

variable {P P' Y : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [MeasurableSpace P] [BorelSpace P] [NormedAddCommGroup P'] [NormedSpace ℝ P']
  [FiniteDimensional ℝ P'] [MeasurableSpace P'] [BorelSpace P'] [NormedAddCommGroup Y]
  [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]

variable {EH : Type*} [NormedAddCommGroup EH] [NormedSpace ℝ EH] {MH : Type*}
  [TopologicalSpace MH] (I : ModelWithCorners ℝ EH MH) {H : Type*} [Group H]
  [TopologicalSpace H] [ChartedSpace MH H] [LieGroup I ∞ H] [MulAction H P']

/-- **The dimension of the orbit `H · η`:** the rank of the derivative of `a ↦ a · η` at the
identity of `H`. -/
noncomputable def orbitDim (η : P') : ℕ :=
  Module.finrank ℝ (LinearMap.range (mfderiv I 𝓘(ℝ, P') (fun a : H => a • η) 1).toLinearMap)

/-- **Proof of Lemma A.26, "the map `G_X` is constant along the orbit `H · η` […] So the Jacobian
of `G_X` has rank at most `P' − k`":** if `G` is invariant under a smooth action of a Lie group
and differentiable at `η`, the rank of its derivative at `η` plus the dimension of the orbit of
`η` is at most the dimension of the parameter space. -/
theorem finrank_range_fderiv_add_orbitDim_le (G : P' → Y)
    (hact : ContMDiff (I.prod 𝓘(ℝ, P')) 𝓘(ℝ, P') ∞ fun p : H × P' => p.1 • p.2)
    (hinv : ∀ (a : H) (η : P'), G (a • η) = G η) (η : P') (hG : DifferentiableAt ℝ G η) :
    Module.finrank ℝ (LinearMap.range (fderiv ℝ G η).toLinearMap) + orbitDim I (H := H) η
      ≤ Module.finrank ℝ P' := by
  -- the orbit map `o a = a • η` is smooth, so differentiable at `1`, and `o 1 = η`
  have hp : ContMDiff I (I.prod 𝓘(ℝ, P')) ∞ fun a : H => (a, η) :=
    contMDiff_id.prodMk contMDiff_const
  have hosm : ContMDiff I 𝓘(ℝ, P') ∞ fun a : H => a • η := by
    have hc := hact.comp hp
    exact hc
  have hoD : MDifferentiableAt I 𝓘(ℝ, P') (fun a : H => a • η) 1 :=
    hosm.mdifferentiableAt (by simp)
  have ho1 : (fun a : H => a • η) 1 = η := one_smul H η
  have hGD : MDifferentiableAt 𝓘(ℝ, P') 𝓘(ℝ, Y) G ((fun a : H => a • η) 1) := by
    rw [ho1]
    exact hG.mdifferentiableAt
  -- `G ∘ o` is constant, so its derivative vanishes: by the chain rule, `DG(η) ∘ Do(1) = 0`
  have hconst : G ∘ (fun a : H => a • η) = fun _ => G η := funext fun a => hinv a η
  have hchain := mfderiv_comp (1 : H) hGD hoD
  rw [hconst, mfderiv_const] at hchain
  have hker : ∀ w, fderiv ℝ G ((fun a : H => a • η) 1)
      (mfderiv I 𝓘(ℝ, P') (fun a : H => a • η) 1 w) = 0 := fun w => by
    have h1 := DFunLike.congr_fun hchain w
    rw [mfderiv_eq_fderiv] at h1
    exact h1.symm
  -- so the range of `Do(1)`, read in `P'`, lies in the kernel of `DG(η)`
  set Do := mfderiv I 𝓘(ℝ, P') (fun a : H => a • η) 1 with hDo
  set e := NormedSpace.fromTangentSpace (𝕜 := ℝ) ((fun a : H => a • η) 1) with he
  have hDG : fderiv ℝ G ((fun a : H => a • η) 1) = fderiv ℝ G η := congrArg (fderiv ℝ G) ho1
  have hle : LinearMap.range (e.toLinearEquiv.toLinearMap ∘ₗ Do.toLinearMap)
      ≤ LinearMap.ker (fderiv ℝ G η).toLinearMap := by
    rintro _ ⟨w, rfl⟩
    rw [LinearMap.mem_ker, ← hDG]
    exact hker w
  have hrange : Module.finrank ℝ (LinearMap.range Do.toLinearMap)
      = Module.finrank ℝ (LinearMap.range (e.toLinearEquiv.toLinearMap ∘ₗ Do.toLinearMap)) := by
    rw [LinearMap.range_comp, LinearEquiv.finrank_map_eq]
  -- rank-nullity for `DG(η)`
  have hrn := LinearMap.finrank_range_add_finrank_ker (fderiv ℝ G η).toLinearMap
  have hmono := Submodule.finrank_mono hle
  show Module.finrank ℝ (LinearMap.range (fderiv ℝ G η).toLinearMap)
      + Module.finrank ℝ (LinearMap.range Do.toLinearMap) ≤ Module.finrank ℝ P'
  omega

/-- **Proof of Lemma A.26, "the rank is lower semicontinuous, so the bound holds at every
`η`":** a bound on the rank of the derivative of a continuously differentiable map that holds at
almost every point, for a Haar measure, holds at every point. -/
theorem finrank_range_fderiv_le_of_ae (G : P' → Y) (hG : ContDiff ℝ 1 G) (r₀ : ℕ)
    (ν : Measure P') [ν.IsAddHaarMeasure]
    (h : ∀ᵐ η ∂ν, Module.finrank ℝ (LinearMap.range (fderiv ℝ G η).toLinearMap) ≤ r₀) (η : P') :
    Module.finrank ℝ (LinearMap.range (fderiv ℝ G η).toLinearMap) ≤ r₀ := by
  -- the set where the rank exceeds `r₀` is open: the rank of a continuous linear map is lower
  -- semicontinuous, and `DG` is continuous
  set U : Set P' := {η' | r₀ < Module.finrank ℝ (LinearMap.range (fderiv ℝ G η').toLinearMap)}
    with hU
  have hUeq : U = fderiv ℝ G ⁻¹' {f : P' →L[ℝ] Y | ↑(r₀ + 1) ≤ (f : P' →ₗ[ℝ] Y).rank} := by
    ext η'
    simp only [hU, Set.mem_ofPred_eq, Set.mem_preimage, LinearMap.rank,
      ← Module.finrank_eq_rank, Nat.cast_le]
    omega
  have hUo : IsOpen U := by
    rw [hUeq]
    exact (isOpen_setOfPred_nat_le_rank (r₀ + 1)).preimage (hG.continuous_fderiv one_ne_zero)
  -- it is null, by the hypothesis
  have hnull : ν U = 0 := by
    rw [ae_iff] at h
    refine measure_mono_null (fun η' hη' => ?_) h
    simp only [Set.mem_ofPred_eq, not_le]
    exact hη'
  -- a nonempty open set has positive Haar measure, so `U` is empty
  by_contra hcon
  have hpos := hUo.measure_pos ν ⟨η, lt_of_not_ge hcon⟩
  exact absurd hnull hpos.ne'

/-- **Proof of Lemma A.26, the bound on the rank of the Jacobian of `G_X`:** if a Lie group acts
smoothly on the parameters, `G` is invariant, and the orbits have dimension at least `k` at
almost every parameter, then the rank of the derivative of `G` is at most `P' − k` at every
parameter. -/
theorem finrank_range_fderiv_add_le_of_ae_orbitDim (G : P' → Y) (hG : ContDiff ℝ 1 G)
    (hact : ContMDiff (I.prod 𝓘(ℝ, P')) 𝓘(ℝ, P') ∞ fun p : H × P' => p.1 • p.2)
    (hinv : ∀ (a : H) (η : P'), G (a • η) = G η) (k : ℕ)
    (ν : Measure P') [ν.IsAddHaarMeasure] (horbit : ∀ᵐ η ∂ν, k ≤ orbitDim I (H := H) η)
    (η : P') :
    Module.finrank ℝ (LinearMap.range (fderiv ℝ G η).toLinearMap) + k
      ≤ Module.finrank ℝ P' := by
  have hd : ∀ η', DifferentiableAt ℝ G η' := fun η' => (hG.differentiable one_ne_zero) η'
  -- at almost every `η'`: `rank DG(η') ≤ P' − k`, and `k ≤ P'`
  have h1 : ∀ᵐ η' ∂ν, Module.finrank ℝ (LinearMap.range (fderiv ℝ G η').toLinearMap)
      ≤ Module.finrank ℝ P' - k ∧ k ≤ Module.finrank ℝ P' := by
    filter_upwards [horbit] with η' hη'
    have h := finrank_range_fderiv_add_orbitDim_le I G hact hinv η' (hd η')
    omega
  obtain ⟨η', -, hk⟩ := h1.exists
  -- so at every `η`
  have h2 := finrank_range_fderiv_le_of_ae G hG (Module.finrank ℝ P' - k) ν
    (h1.mono fun _ h => h.1) η
  omega

section Families

variable {In Out : Type*} [NormedAddCommGroup Out] [NormedSpace ℝ Out] [FiniteDimensional ℝ Out]

/-- **Lemma A.26 (i):** let `F_θ(x)` and `G_η(x)` be real-analytic in the parameters for every
input `x`, let a Lie group act smoothly on the parameters `η` with `G_{a·η} = G_η`, and let the
orbits have dimension at least `k` at almost every `η`. If at some `θ_0` the Jacobian of
`θ ↦ (F_θ(x))_{x ∈ X}` has rank greater than `P' − k` on a finite batch `X`, then for almost
every `θ` no `η` satisfies `F_θ = G_η`. Sard's theorem is a hypothesis from the literature. -/
theorem ae_forall_ne_of_lieGroup_action (hSard : ∀ r : ℕ, SardCriticalValues P' (Fin r → ℝ))
    (F : P → In → Out) (G : P' → In → Out)
    (hF : ∀ x, AnalyticOnNhd ℝ (fun θ => F θ x) Set.univ)
    (hG : ∀ x, AnalyticOnNhd ℝ (fun η => G η x) Set.univ)
    (hact : ContMDiff (I.prod 𝓘(ℝ, P')) 𝓘(ℝ, P') ∞ fun p : H × P' => p.1 • p.2)
    (hinv : ∀ (a : H) (η : P'), G (a • η) = G η) (k : ℕ)
    (ν : Measure P') [ν.IsAddHaarMeasure] (horbit : ∀ᵐ η ∂ν, k ≤ orbitDim I (H := H) η)
    {n : ℕ} (X : Fin n → In) (θ₀ : P)
    (hθ₀ : Module.finrank ℝ P' < Module.finrank ℝ (LinearMap.range
      (fderiv ℝ (fun θ => fun i => F θ (X i)) θ₀).toLinearMap) + k)
    (μ : Measure P) [μ.IsAddHaarMeasure] :
    ∀ᵐ θ ∂μ, ∀ η : P', F θ ≠ G η := by
  -- the outputs on the batch
  have hFX : AnalyticOnNhd ℝ (fun θ => fun i => F θ (X i)) Set.univ :=
    AnalyticOnNhd.pi fun i => hF (X i)
  have hGX : AnalyticOnNhd ℝ (fun η => fun i => G η (X i)) Set.univ :=
    AnalyticOnNhd.pi fun i => hG (X i)
  -- the rank of the Jacobian of `G_X` is at most `P' − k` at every `η`
  have hr := finrank_range_fderiv_add_le_of_ae_orbitDim I (fun η => fun i => G η (X i))
    hGX.contDiff hact (fun a η => by simp only [hinv a η]) k ν horbit
  have h := ae_notMem_range_of_rank_lt hSard (fun θ => fun i => F θ (X i))
    (fun η => fun i => G η (X i)) hFX hGX (Module.finrank ℝ P' - k)
    (fun η => by have := hr η; omega) θ₀ (by have := hr 0; omega) μ
  filter_upwards [h] with θ hθ η heq
  exact hθ ⟨η, funext fun i => by rw [heq]⟩

/-- **Lemma A.26 (ii):** under the hypotheses of (i), if the set of the outputs of the family
`G` on the batch `X` has the property of definable sets that the paper uses
(`ClosureNullOfNull`), then for almost every `θ` there is a `δ > 0` such that every `η` has
`‖F_θ(x) − G_η(x)‖ ≥ δ` at some `x ∈ X`. -/
theorem ae_exists_pos_le_norm_sub_of_lieGroup_action
    (hSard : ∀ r : ℕ, SardCriticalValues P' (Fin r → ℝ))
    (F : P → In → Out) (G : P' → In → Out)
    (hF : ∀ x, AnalyticOnNhd ℝ (fun θ => F θ x) Set.univ)
    (hG : ∀ x, AnalyticOnNhd ℝ (fun η => G η x) Set.univ)
    (hact : ContMDiff (I.prod 𝓘(ℝ, P')) 𝓘(ℝ, P') ∞ fun p : H × P' => p.1 • p.2)
    (hinv : ∀ (a : H) (η : P'), G (a • η) = G η) (k : ℕ)
    (ν : Measure P') [ν.IsAddHaarMeasure] (horbit : ∀ᵐ η ∂ν, k ≤ orbitDim I (H := H) η)
    {n : ℕ} (X : Fin n → In)
    (hcl : ClosureNullOfNull (Set.range fun η : P' => fun i => G η (X i))) (θ₀ : P)
    (hθ₀ : Module.finrank ℝ P' < Module.finrank ℝ (LinearMap.range
      (fderiv ℝ (fun θ => fun i => F θ (X i)) θ₀).toLinearMap) + k)
    (μ : Measure P) [μ.IsAddHaarMeasure] :
    ∀ᵐ θ ∂μ, ∃ δ : ℝ, 0 < δ ∧ ∀ η : P', ∃ i, δ ≤ ‖F θ (X i) - G η (X i)‖ := by
  have hFX : AnalyticOnNhd ℝ (fun θ => fun i => F θ (X i)) Set.univ :=
    AnalyticOnNhd.pi fun i => hF (X i)
  have hGX : AnalyticOnNhd ℝ (fun η => fun i => G η (X i)) Set.univ :=
    AnalyticOnNhd.pi fun i => hG (X i)
  have hr := finrank_range_fderiv_add_le_of_ae_orbitDim I (fun η => fun i => G η (X i))
    hGX.contDiff hact (fun a η => by simp only [hinv a η]) k ν horbit
  have h := ae_notMem_closure_range_of_rank_lt hSard (fun θ => fun i => F θ (X i))
    (fun η => fun i => G η (X i)) hFX hGX hcl (Module.finrank ℝ P' - k)
    (fun η => by have := hr η; omega) θ₀ (by have := hr 0; omega) μ
  filter_upwards [h] with θ hθ
  -- a positive distance `δ` to every output of `G` on `X`
  obtain ⟨δ, hδ, hS⟩ := exists_pos_le_norm_sub_of_notMem_closure hθ
  refine ⟨δ, hδ, fun η => ?_⟩
  -- the norm on the batch is the largest norm of an output: some input `X i` attains `δ`
  by_contra hcon
  push Not at hcon
  have hlt : ‖(fun i => F θ (X i)) - fun i => G η (X i)‖ < δ :=
    (pi_norm_lt_iff hδ).2 fun i => hcon i
  exact absurd (hS _ ⟨η, rfl⟩) (not_le.2 hlt)

end Families

end Skips
