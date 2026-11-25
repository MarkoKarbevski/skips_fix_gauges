import SkipsLean.Depth.ScaledSuffixOrders
import SkipsLean.Generic.HolomorphicExtension

/-!
# The rest of the network on a ray: the holomorphic extension, bounded uniformly in `t`

Paper (dimension), Lemma D.10 (The rest of the network on a ray), second sentence: "Moreover,
there are numbers `ϱ, t₀ > 0` such that the maps `u ↦ 𝓑_{>k}(t (h° + u))` and
`u ↦ 𝐃_θ 𝓑_{>k}(t (h° + u)) η` extend to holomorphic maps on the rows `u ∈ ℂ^{1×d_model}` with
`|u_j| ≤ ϱ` for all `j`, which are bounded uniformly in `t ≥ t₀`." Its proof: "So
`𝓑_{>k}(t (h° + u))` is a real-analytic function of `(1/t, u)` near `(0, 0)`. It extends to a
holomorphic and bounded function on a complex neighborhood of `(0, 0)`, which gives `ϱ` and `t_0`.
[…] The weights enter analytically as well, which gives the same for `𝐃_θ 𝓑_{>k}(·) η`."

Here, for hidden states `H` of all tokens without zero rows (the paper's `h°` is one row), with
`t^m` in the place of `t` as in `Depth/ScaledSuffix.lean`, and for every direction `η` of the
weights: numbers `ϱ, t₀ > 0` and a bound `C` such that, for every `t ≥ t₀`, each of the two maps
agrees at the real `u` with `|u_{τ j}| ≤ ϱ` with a map that is holomorphic on the complex `u` with
`|u_{τ j}| ≤ ϱ` and bounded by `C` there (`exists_holomorphic_suffix_pow_bounded`; in the paper's
form, `m = 1`: `exists_holomorphic_suffix_bounded`). The extension is the one of
`Generic/HolomorphicExtension.lean`, of the map `(s, h) ↦ 𝓑^♯(N_{ε s^{2m}}(h))` at `(0, H)`.
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise Topology

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable (A : Arch T d L) {ε : ℝ}

/-- **Lemma D.10, second sentence, with `t^m` in the place of `t`:** under pre-RMSNorm with
`ε > 0` and for real-analytic blocks, at a hidden state `H` without zero rows there are numbers
`ϱ, t₀ > 0` and `C` such that, for `t ≥ t₀`, the maps `u ↦ 𝓑_{>k}(t^m (H + u))` and
`u ↦ 𝐃_θ 𝓑_{>k}(t^m (H + u)) η` extend to holomorphic maps on the complex `u` with
`|u_{τ j}| ≤ ϱ` for all entries, bounded by `C`. -/
theorem exists_holomorphic_suffix_pow_bounded (hε : 0 < ε) (hχ : A.χ = rmsNorm ε)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (m : ℕ) (θ η : Params A dIn dOut)
    (k : Fin (L + 1)) (H : Matrix T d ℝ) (hH : ∀ τ, H τ ≠ 0) :
    ∃ ϱ : ℝ, 0 < ϱ ∧ ∃ t₀ : ℝ, 0 < t₀ ∧ ∃ C : ℝ, ∀ t : ℝ, t₀ ≤ t →
      (∃ G : Matrix T d ℂ → Matrix T dOut ℂ,
        AnalyticOnNhd ℂ G {u | ∀ τ j, ‖u τ j‖ ≤ ϱ}
        ∧ (∀ u : Matrix T d ℝ, (∀ τ j, |u τ j| ≤ ϱ) →
            G (u.map fun a : ℝ => (a : ℂ))
              = (suffix A 0 θ k (t ^ m • (H + u))).map fun a : ℝ => (a : ℂ))
        ∧ ∀ u : Matrix T d ℂ, (∀ τ j, ‖u τ j‖ ≤ ϱ) → ‖G u‖ ≤ C)
      ∧ ∃ G' : Matrix T d ℂ → Matrix T dOut ℂ,
        AnalyticOnNhd ℂ G' {u | ∀ τ j, ‖u τ j‖ ≤ ϱ}
        ∧ (∀ u : Matrix T d ℝ, (∀ τ j, |u τ j| ≤ ϱ) →
            G' (u.map fun a : ℝ => (a : ℂ))
              = (fderiv ℝ (fun θ' : Params A dIn dOut => suffix A 0 θ' k (t ^ m • (H + u)))
                  θ η).map fun a : ℝ => (a : ℂ))
        ∧ ∀ u : Matrix T d ℂ, (∀ τ j, ‖u τ j‖ ≤ ϱ) → ‖G' u‖ ≤ C := by
  -- the two maps of `(s, h)`, real-analytic at `(0, H)`
  have h1 : AnalyticAt ℝ (fun z : ℝ × Matrix T d ℝ => scaledSuffix A ε m θ k z) (0, H) := by
    have ha := analyticAt_scaledSuffix A hε hχ hf m θ k 0 H hH
    have hi : AnalyticAt ℝ (fun z : ℝ × Matrix T d ℝ =>
        ((θ, z) : Params A dIn dOut × ℝ × Matrix T d ℝ)) (0, H) :=
      analyticAt_const.prod analyticAt_id
    have hc := ha.comp_of_eq hi rfl
    exact hc
  have h2 := analyticAt_fderiv_params_scaledSuffix A hε hχ hf m θ η k 0 H hH
  -- their holomorphic extensions, for `|s| ≤ s₁` and `|s| ≤ s₂`
  obtain ⟨ϱ₁, hϱ₁, s₁, hs₁, C₁, hG₁⟩ := exists_holomorphic_extension_real_param h1
  obtain ⟨ϱ₂, hϱ₂, s₂, hs₂, C₂, hG₂⟩ := exists_holomorphic_extension_real_param h2
  have ht₀ : 0 < max (1 / s₁) (1 / s₂) := lt_max_of_lt_left (by positivity)
  refine ⟨min ϱ₁ ϱ₂, lt_min hϱ₁ hϱ₂, max (1 / s₁) (1 / s₂), ht₀, max C₁ C₂, fun t ht => ?_⟩
  have ht0 : 0 < t := ht₀.trans_le ht
  -- `s = 1/t` has `|s| ≤ s₁` and `|s| ≤ s₂`
  have hs : ∀ s₀ : ℝ, 0 < s₀ → 1 / s₀ ≤ t → |1 / t| ≤ s₀ := fun s₀ hs₀ h => by
    rw [abs_of_pos (by positivity)]
    exact (one_div_le hs₀ ht0).1 h
  obtain ⟨G, hGa, hGr, hGb⟩ := hG₁ (1 / t) (hs s₁ hs₁ (le_of_max_le_left ht))
  obtain ⟨G', hGa', hGr', hGb'⟩ := hG₂ (1 / t) (hs s₂ hs₂ (le_of_max_le_right ht))
  have hu₁ : ∀ u : Matrix T d ℂ, (∀ τ j, ‖u τ j‖ ≤ min ϱ₁ ϱ₂) → ∀ τ j, ‖u τ j‖ ≤ ϱ₁ :=
    fun u hu τ j => (hu τ j).trans (min_le_left _ _)
  have hu₂ : ∀ u : Matrix T d ℂ, (∀ τ j, ‖u τ j‖ ≤ min ϱ₁ ϱ₂) → ∀ τ j, ‖u τ j‖ ≤ ϱ₂ :=
    fun u hu τ j => (hu τ j).trans (min_le_right _ _)
  refine ⟨⟨G, hGa.mono fun u hu => hu₁ u hu, fun u hu => ?_,
    fun u hu => (hGb u (hu₁ u hu)).trans (le_max_left _ _)⟩,
    G', hGa'.mono fun u hu => hu₂ u hu, fun u hu => ?_,
    fun u hu => (hGb' u (hu₂ u hu)).trans (le_max_right _ _)⟩
  · -- at real `u`: `𝓑_{>k}(t^m (H + u)) = 𝓑^♯(N_{ε t^{-2m}}(H + u))`
    rw [hGr u fun τ j => (hu τ j).trans (min_le_left _ _),
      suffix_pow_smul_eq_scaledSuffix A hχ θ k ht0 m]
  · -- the same for the derivative in the weights
    rw [hGr' u fun τ j => (hu τ j).trans (min_le_right _ _),
      fderiv_params_suffix_pow_smul A hχ θ η k ht0 m]

/-- **Lemma D.10, second sentence:** the maps `u ↦ 𝓑_{>k}(t (H + u))` and
`u ↦ 𝐃_θ 𝓑_{>k}(t (H + u)) η` extend to holomorphic maps on the complex `u` with
`|u_{τ j}| ≤ ϱ` for all entries, which are bounded uniformly in `t ≥ t₀`. -/
theorem exists_holomorphic_suffix_bounded (hε : 0 < ε) (hχ : A.χ = rmsNorm ε)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (θ η : Params A dIn dOut)
    (k : Fin (L + 1)) (H : Matrix T d ℝ) (hH : ∀ τ, H τ ≠ 0) :
    ∃ ϱ : ℝ, 0 < ϱ ∧ ∃ t₀ : ℝ, 0 < t₀ ∧ ∃ C : ℝ, ∀ t : ℝ, t₀ ≤ t →
      (∃ G : Matrix T d ℂ → Matrix T dOut ℂ,
        AnalyticOnNhd ℂ G {u | ∀ τ j, ‖u τ j‖ ≤ ϱ}
        ∧ (∀ u : Matrix T d ℝ, (∀ τ j, |u τ j| ≤ ϱ) →
            G (u.map fun a : ℝ => (a : ℂ))
              = (suffix A 0 θ k (t • (H + u))).map fun a : ℝ => (a : ℂ))
        ∧ ∀ u : Matrix T d ℂ, (∀ τ j, ‖u τ j‖ ≤ ϱ) → ‖G u‖ ≤ C)
      ∧ ∃ G' : Matrix T d ℂ → Matrix T dOut ℂ,
        AnalyticOnNhd ℂ G' {u | ∀ τ j, ‖u τ j‖ ≤ ϱ}
        ∧ (∀ u : Matrix T d ℝ, (∀ τ j, |u τ j| ≤ ϱ) →
            G' (u.map fun a : ℝ => (a : ℂ))
              = (fderiv ℝ (fun θ' : Params A dIn dOut => suffix A 0 θ' k (t • (H + u)))
                  θ η).map fun a : ℝ => (a : ℂ))
        ∧ ∀ u : Matrix T d ℂ, (∀ τ j, ‖u τ j‖ ≤ ϱ) → ‖G' u‖ ≤ C := by
  simpa only [pow_one] using exists_holomorphic_suffix_pow_bounded A hε hχ hf 1 θ η k H hH

end Skips
