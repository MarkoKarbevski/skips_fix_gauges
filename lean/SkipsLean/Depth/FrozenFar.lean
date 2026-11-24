import SkipsLean.Depth.Frozen
import SkipsLean.Activations.GateFar

/-!
# The network after `h_k` far out in its cone

Paper (dimension): Lemma D.11 (The network after `h_k` far out in its cone). "In the case (n), for
gated blocks, let `θ` be good, `k ≤ L`, `h° ∈ C_k`, and let `η` be a direction of the weights of
the blocks `k+1, …, L` and of `D`. There are numbers `ϱ, κ, t₀ > 0` such that, for `t ≥ t₀`, the
maps `u ↦ 𝓑_{>k}(t (h° + u))` and `u ↦ 𝐃_θ 𝓑_{>k}(t (h° + u)) η` extend to holomorphic maps on the
rows `u ∈ ℂ^{1×d_model}` with `|u_j| ≤ ϱ` for all `j`, and for these `u`, at `h = t (h° + u)`,

  `‖𝓑_{>k}(h) − 𝓑°_{>k}(h)‖ ≤ e^{−κ t^p}`,   `‖𝐃_θ 𝓑_{>k}(h) η − 𝐃_θ 𝓑°_{>k}(h) η‖ ≤ e^{−κ t^p}`."

The paper uses the complex rows `u` in one place: in the proof of Lemma D.12, fact (b), Cauchy's
estimate turns the first bound into the same bound for the derivative `𝐃𝓑_{>k} − 𝐃𝓑°_{>k}` in the
hidden state. The statement here is for real `u` and has this bound for the derivative as a third
clause in its place; the holomorphic extension is not stated. A hidden state has the rows `T`, and
`h°` is a matrix `H` all of whose rows lie in `C_k`. The gate is any `σ` with `GateFar σ σ' p`
(SiLU with `p = 1`, GELU with `p = 2`).
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise Topology

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]
variable {σ σ' : ℝ → ℝ} {p : ℕ}

/-- **Lemma D.11, for real hidden states, with the derivative in the hidden state.** Let `θ` be
good for the cones, and let all rows of `H` lie in `C_k`. There are `ϱ, κ > 0` and `t₀` such that
for `t ≥ t₀` and `‖U‖ ≤ ϱ`, at `h = t (H + U)`, the network after `h_k` and the frozen network
after `h_k`, their derivatives in the hidden state (along `v`, up to the factor `‖v‖`), and their
derivatives in the weights along `η` differ by at most `e^{−κ t^p}`. -/
theorem exists_far_frozen_bounds (hg : GateFar σ σ' p) {C : Fin (L + 1) → Set (d → ℝ)}
    {A : ∀ ℓ, Finset (hid ℓ)} {θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut}
    (hθ : GoodForConesGated C A θ) (k : Fin (L + 1)) (H : Matrix T d ℝ) (hH : ∀ t, H t ∈ C k)
    (η : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) :
    ∃ ϱ : ℝ, 0 < ϱ ∧ ∃ κ : ℝ, 0 < κ ∧ ∃ t₀ : ℝ, ∀ t : ℝ, t₀ ≤ t → ∀ U : Matrix T d ℝ, ‖U‖ ≤ ϱ →
      ‖suffix (Arch.gated σ id hid) 0 θ k (t • (H + U))
          - suffix (Arch.frozen A) 0 (θ.toFrozen A) k (t • (H + U))‖ ≤ Real.exp (-(κ * t ^ p)) ∧
      (∀ v : Matrix T d ℝ,
        ‖fderiv ℝ (fun h' : Matrix T d ℝ => suffix (Arch.gated σ id hid) 0 θ k h') (t • (H + U)) v
            - fderiv ℝ (fun h' : Matrix T d ℝ => suffix (Arch.frozen A) 0 (θ.toFrozen A) k h')
                (t • (H + U)) v‖ ≤ Real.exp (-(κ * t ^ p)) * ‖v‖) ∧
      ‖fderiv ℝ (fun θ' : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut =>
              suffix (Arch.gated σ id hid) 0 θ' k (t • (H + U))) θ η
          - fderiv ℝ (fun θ' : Params (Arch.frozen (T := T) (d := d) A) dIn dOut =>
              suffix (Arch.frozen A) 0 θ' k (t • (H + U))) (θ.toFrozen A) (η.toFrozen A)‖
        ≤ Real.exp (-(κ * t ^ p)) := by
  sorry

end Skips
