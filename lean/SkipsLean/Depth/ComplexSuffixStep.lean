import SkipsLean.Depth.ComplexSuffix

/-!
# Lemma D.14, step by step: the cone depends only on the later blocks

Paper (dimension paper): Appendix D.6 (the case `ε = 0`), Lemma D.14 (`𝓑_{>k}` on a complex cone):
"Let `θ` satisfy (R1) and (R2). For every `k` there is a `κ_k ∈ (0, 1]` such that `𝓑_{>k}`, with
its derivatives `𝐃𝓑_{>k}` and `𝐃_θ𝓑_{>k}`, extends to a holomorphic map on `C_{κ_k}` […]. The
number `κ_k` depends only on the weights of the blocks `k + 1, …, L` and on `D`."

Its proof: "`𝓑_{>L}(h) = N(h) D` is holomorphic on `C_1`: `κ_L = 1`. Let `k < L`. The map `g_{k+1}`
is holomorphic near `S` and maps the compact set `S` into the real rows `h ≠ 0`, by (R2), hence
into the open set `C_{κ_{k+1}}`. […] So there is a `κ_k` such that `N` maps `C_{κ_k}` into the
points at distance less than `ρ` from `S`, and `𝓑_{>k} = 𝓑_{>k+1} ∘ g_{k+1} ∘ N` is holomorphic on
`C_{κ_k}`."

`Depth/ComplexSuffix.lean` has the lemma for a regular `θ`. Here are its two steps, with (R2) for
one block only, and the last sentence: `HolomorphicOnCone σC θ k κ` depends only on the weights of
the blocks after the hidden state `k` and on `D`. They are used to choose the blocks of the
parameter `θ*` from the last to the first ("Parameters that satisfy all conditions, in the case
(0)": "Let `D` and the blocks `ℓ + 1, …, L` be chosen […]. This fixes `κ_ℓ` (Lemma D.14).").

Numbering: the block `ℓ : Fin L` is the paper's block `ℓ + 1`, between the hidden states
`ℓ.castSucc` and `ℓ.succ`. (R2) for it is written for one row: `σ(n W) V ≠ 0` for every row `n` on
the sphere `‖n‖² = d`.
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut] {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)] {σ : ℝ → ℝ} {σC : ℂ → ℂ}

/-- **Lemma D.14, "`𝓑_{>L}(h) = N(h) D` is holomorphic on `C_1`: `κ_L = 1`",** at every `θ`. -/
theorem holomorphicOnCone_last (σC : ℂ → ℂ)
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) :
    HolomorphicOnCone σC θ (Fin.last L) 1 := by
  sorry

/-- **Lemma D.14, the step from `k + 1` to `k`:** let `σC` extend `σ` and be holomorphic at every
real point. If `𝓑_{>ℓ+1}` is holomorphic on a cone `C_{κ'}`, `κ' > 0`, and block `ℓ` satisfies (R2)
(`σ(n W) V ≠ 0` for every row `n` on the sphere `‖n‖² = d`), then there is a `κ ∈ (0, 1]` such that
`𝓑_{>ℓ}` is holomorphic on `C_κ`. -/
theorem exists_holomorphicOnCone_castSucc (hσ : ∀ x : ℝ, σC (x : ℂ) = ((σ x : ℝ) : ℂ))
    (hσC : ∀ x : ℝ, AnalyticAt ℂ σC (x : ℂ))
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) (ℓ : Fin L)
    {κ' : ℝ} (hκ' : 0 < κ') (h : HolomorphicOnCone σC θ ℓ.succ κ')
    (hR2 : ∀ n : d → ℝ, n ⬝ᵥ n = (Fintype.card d : ℝ) →
      (fun j : hid ℓ => σ ((n ᵥ* θ.read ℓ) j)) ᵥ* θ.write ℓ ≠ 0) :
    ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1 ∧ HolomorphicOnCone σC θ ℓ.castSucc κ := by
  sorry

/-- **Lemma D.14, "The number `κ_k` depends only on the weights of the blocks `k + 1, …, L` and on
`D`":** if `θ'` has the same reads and writes as `θ` in the blocks after the hidden state `k`, and
the same `D`, then `𝓑_{>k}` is holomorphic on the same cones at `θ'` as at `θ`. -/
theorem HolomorphicOnCone.congr
    {θ θ' : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut} {k : Fin (L + 1)}
    {κ : ℝ} (h : HolomorphicOnCone σC θ k κ)
    (hread : ∀ ℓ : Fin L, k ≤ ℓ.castSucc → θ'.read ℓ = θ.read ℓ)
    (hwrite : ∀ ℓ : Fin L, k ≤ ℓ.castSucc → θ'.write ℓ = θ.write ℓ) (hD : θ'.D = θ.D) :
    HolomorphicOnCone σC θ' k κ := by
  sorry

end Skips
