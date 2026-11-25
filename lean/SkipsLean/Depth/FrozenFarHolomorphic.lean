import SkipsLean.Depth.FrozenFar
import SkipsLean.Activations.GateFarC

/-!
# The network after `h_k` far out in its cone: the holomorphic extension

Paper (dimension): Lemma D.11 (The network after `h_k` far out in its cone). "In the case (n), for
gated blocks, let `θ` be good, `k ≤ L`, `h° ∈ C_k`, and let `η` be a direction of the weights of
the blocks `k+1, …, L` and of `D`. There are numbers `ϱ, κ, t₀ > 0` such that, for `t ≥ t₀`, the
maps `u ↦ 𝓑_{>k}(t (h° + u))` and `u ↦ 𝐃_θ 𝓑_{>k}(t (h° + u)) η` extend to holomorphic maps on the
rows `u ∈ ℂ^{1×d_model}` with `|u_j| ≤ ϱ` for all `j`, and for these `u`, at `h = t (h° + u)`,

  `‖𝓑_{>k}(h) − 𝓑°_{>k}(h)‖ ≤ e^{−κ t^p}`,   `‖𝐃_θ 𝓑_{>k}(h) η − 𝐃_θ 𝓑°_{>k}(h) η‖ ≤ e^{−κ t^p}`."

`Depth/FrozenFar.lean` has the bounds for real `u` (with the bound for the derivative in the
hidden state, which the paper gets from the complex `u` by Cauchy's estimate). Here the lemma as
the paper states it, for complex `u`: for `t ≥ t₀` there are maps `G`, `G°`, `G'`, `G°'` that are
holomorphic on the complex `u` with `|u_{τ j}| ≤ ϱ` for all entries (holomorphic near each point
of this closed polydisc), that agree at the real `u` of the polydisc with `u ↦ 𝓑_{>k}(t (H + u))`,
with the same map of the frozen network, and with the derivatives of the two in the weights along
`η`, and that satisfy the two bounds on the whole polydisc. A holomorphic map on the polydisc is
determined by its values at the real points, so these are the extensions of the paper. A hidden
state has the rows `T`, and `h°` is a matrix `H` all of whose rows lie in `C_k`. The gate is any
`σ` with `GateFar σ σ' p` and `GateFarC σ p` (SiLU with `p = 1`, GELU with `p = 2`).
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise Topology

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]
variable {σ σ' : ℝ → ℝ} {p : ℕ}

/-- **Lemma D.11, with the holomorphic extension.** Let `θ` be good for the cones, and let all
rows of `H` lie in `C_k`. There are `ϱ, κ > 0` and `t₀` such that for `t ≥ t₀` the maps
`u ↦ 𝓑_{>k}(t (H + u))` and `u ↦ 𝐃_θ 𝓑_{>k}(t (H + u)) η`, and the same maps of the frozen network,
extend to holomorphic maps on the complex `u` with `|u_{τ j}| ≤ ϱ`, and on this polydisc the
network and the frozen network, and their derivatives in the weights along `η`, differ by at most
`e^{−κ t^p}`. -/
theorem exists_far_frozen_holomorphic (hg : GateFar σ σ' p) (hgC : GateFarC σ p)
    {C : Fin (L + 1) → Set (d → ℝ)} {A : ∀ ℓ, Finset (hid ℓ)}
    {θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut}
    (hθ : GoodForConesGated C A θ) (k : Fin (L + 1)) (H : Matrix T d ℝ) (hH : ∀ t, H t ∈ C k)
    (η : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) :
    ∃ ϱ : ℝ, 0 < ϱ ∧ ∃ κ : ℝ, 0 < κ ∧ ∃ t₀ : ℝ, ∀ t : ℝ, t₀ ≤ t →
      ∃ G G₀ G' G₀' : Matrix T d ℂ → Matrix T dOut ℂ,
        AnalyticOnNhd ℂ G {u | ∀ τ j, ‖u τ j‖ ≤ ϱ} ∧
        AnalyticOnNhd ℂ G₀ {u | ∀ τ j, ‖u τ j‖ ≤ ϱ} ∧
        AnalyticOnNhd ℂ G' {u | ∀ τ j, ‖u τ j‖ ≤ ϱ} ∧
        AnalyticOnNhd ℂ G₀' {u | ∀ τ j, ‖u τ j‖ ≤ ϱ} ∧
        (∀ U : Matrix T d ℝ, (∀ τ j, |U τ j| ≤ ϱ) →
          G (U.map fun a : ℝ => (a : ℂ))
              = (suffix (Arch.gated σ id hid) 0 θ k (t • (H + U))).map (fun a : ℝ => (a : ℂ)) ∧
          G₀ (U.map fun a : ℝ => (a : ℂ))
              = (suffix (Arch.frozen A) 0 (θ.toFrozen A) k (t • (H + U))).map
                  (fun a : ℝ => (a : ℂ)) ∧
          G' (U.map fun a : ℝ => (a : ℂ))
              = (fderiv ℝ (fun θ' : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut =>
                  suffix (Arch.gated σ id hid) 0 θ' k (t • (H + U))) θ η).map
                  (fun a : ℝ => (a : ℂ)) ∧
          G₀' (U.map fun a : ℝ => (a : ℂ))
              = (fderiv ℝ (fun θ' : Params (Arch.frozen (T := T) (d := d) A) dIn dOut =>
                  suffix (Arch.frozen A) 0 θ' k (t • (H + U))) (θ.toFrozen A)
                  (η.toFrozen A)).map (fun a : ℝ => (a : ℂ))) ∧
        ∀ u : Matrix T d ℂ, (∀ τ j, ‖u τ j‖ ≤ ϱ) →
          ‖G u - G₀ u‖ ≤ Real.exp (-(κ * t ^ p)) ∧ ‖G' u - G₀' u‖ ≤ Real.exp (-(κ * t ^ p)) := by
  sorry

end Skips
