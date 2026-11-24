import SkipsLean.Depth.SuffixRMS
import SkipsLean.Depth.StepTanhRMS

/-!
# The rest of the network on a ray, under pre-RMSNorm

Paper (dimension): Lemma D.10 (The rest of the network on a ray). "In the case (+), let `k ≤ L`,
let `h° ≠ 0` be a row, let `v_1, …, v_i` be rows, and let `η` be a direction of the weights of the
blocks `k+1, …, L` and of `D`. With `𝐃^i` the derivative of order `i` in `h`, the maps
`t ↦ t^i 𝐃^i 𝓑_{>k}(t h°)(v_1, …, v_i)` and `t ↦ t^i 𝐃^i (𝐃_θ 𝓑_{>k}(·) η)(t h°)(v_1, …, v_i)` are
real-analytic functions of `1/t` near `1/t = 0`, so they are meromorphic at infinity. Moreover,
there are numbers `ϱ, t₀ > 0` such that the maps `u ↦ 𝓑_{>k}(t (h° + u))` and
`u ↦ 𝐃_θ 𝓑_{>k}(t (h° + u)) η` extend to holomorphic maps on the rows `u ∈ ℂ^{1×d_model}` with
`|u_j| ≤ ϱ` for all `j`, which are bounded uniformly in `t ≥ t₀`." Its proof: "`𝓑_{>k} = 𝓑^♯ ∘ N_ε`
[…] For `t > 0` and a row `u`, `N_ε(t (h° + u)) = (h° + u) / √(‖h° + u‖²/d_model + ε t^{−2})`, and
the right side is a real-analytic function of `(1/t, u)` near `(0, 0)`, also at `1/t = 0`, because
`h° ≠ 0`. So `𝓑_{>k}(t (h° + u))` is a real-analytic function of `(1/t, u)` near `(0, 0)`."

Stated here, for a real variable: the network after the normalization of `h_k` (`suffixPost`, the
paper's `𝓑^♯`), and the map `(s, h) ↦ 𝓑^♯(N_{ε s^{2m}}(h))` (`scaledSuffix`), which is
`𝓑_{>k}(t^m h)` at `s = 1/t` for every `t > 0` (the proof of Lemma D.12 uses the lemma "with `t^m` in
the place of `t`", `m = 2` for gated blocks and `m = 1` for GELU blocks). This map is real-analytic
in `(θ, s, h)` at every `s`, also at `s = 0`, at hidden states `h` without zero rows; it is even in
`s`; and the derivatives of `𝓑_{>k}` in the hidden state and in the weights at `t^m h` are those of
the map at `(1/t, h)`, the first with the factor `t^{−m}`. The derivatives of all orders of the
paper, their being meromorphic at infinity, and the bounds uniform in `t` (which the paper gets from
a holomorphic extension) follow from this real-analyticity near `s = 0`; they are not stated here.
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise Topology

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable (A : Arch T d L) {ε : ℝ}

/-- **The network after the normalization of the hidden state `h_k`** (the paper's `𝓑^♯`):
`𝓑_{>k}(h) = 𝓑^♯(χ(h))`. -/
def suffixPost (θ : Params A dIn dOut) (k : Fin (L + 1)) (n : Matrix T d ℝ) : Matrix T dOut ℝ :=
  Fin.lastCases (motive := fun _ => Matrix T dOut ℝ) (n * θ.D)
    (fun ℓ => suffix A 0 θ ℓ.succ (A.f ℓ (n * θ.read ℓ) * θ.write ℓ)) k

/-- `𝓑_{>k}(h) = 𝓑^♯(χ(h))`, in a network without skips. -/
theorem suffix_eq_suffixPost (θ : Params A dIn dOut) (k : Fin (L + 1)) (h : Matrix T d ℝ) :
    suffix A 0 θ k h = suffixPost A θ k (A.χ h) := by
  sorry

/-- **The rest of the network on a ray, in the variables `s = 1/t` and `h`:**
`(s, h) ↦ 𝓑^♯(N_{ε s^{2m}}(h))`. For `t > 0` it is `𝓑_{>k}(t^m h)` at `s = 1/t`. -/
noncomputable def scaledSuffix (ε : ℝ) (m : ℕ) (θ : Params A dIn dOut) (k : Fin (L + 1))
    (z : ℝ × Matrix T d ℝ) : Matrix T dOut ℝ :=
  suffixPost A θ k (rmsNorm (ε * z.1 ^ (2 * m)) z.2)

/-- `𝓑_{>k}(t^m h) = 𝓑^♯(N_{ε t^{−2m}}(h))` for `t > 0`, under pre-RMSNorm. -/
theorem suffix_pow_smul_eq_scaledSuffix (hχ : A.χ = rmsNorm ε) (θ : Params A dIn dOut)
    (k : Fin (L + 1)) {t : ℝ} (ht : 0 < t) (m : ℕ) (h : Matrix T d ℝ) :
    suffix A 0 θ k (t ^ m • h) = scaledSuffix A ε m θ k (1 / t, h) := by
  sorry

/-- The map is even in `s`. -/
theorem scaledSuffix_neg (m : ℕ) (θ : Params A dIn dOut) (k : Fin (L + 1)) (s : ℝ)
    (h : Matrix T d ℝ) :
    scaledSuffix A ε m θ k (-s, h) = scaledSuffix A ε m θ k (s, h) := by
  sorry

/-- **Lemma D.10, for a real variable:** under pre-RMSNorm with `ε > 0` and for real-analytic
blocks, `(θ, s, h) ↦ 𝓑^♯(N_{ε s^{2m}}(h))` is real-analytic at every `(θ, s, H)` such that no row
of `H` vanishes; in particular at `s = 0`, which is `t = ∞`. -/
theorem analyticAt_scaledSuffix (hε : 0 < ε) (hχ : A.χ = rmsNorm ε)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (m : ℕ) (θ : Params A dIn dOut)
    (k : Fin (L + 1)) (s : ℝ) (H : Matrix T d ℝ) (hH : ∀ t, H t ≠ 0) :
    AnalyticAt ℝ (fun x : Params A dIn dOut × ℝ × Matrix T d ℝ => scaledSuffix A ε m x.1 k x.2)
      (θ, s, H) := by
  sorry

/-- The derivative of `𝓑_{>k}` in the hidden state at `t^m h`, from the map at `(1/t, h)`. -/
theorem fderiv_suffix_pow_smul (hε : 0 < ε) (hχ : A.χ = rmsNorm ε)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (θ : Params A dIn dOut) (k : Fin (L + 1))
    {t : ℝ} (ht : 0 < t) (m : ℕ) (h u : Matrix T d ℝ) :
    fderiv ℝ (fun h' : Matrix T d ℝ => suffix A 0 θ k h') (t ^ m • h) u
      = (1 / t) ^ m
        • fderiv ℝ (fun h' : Matrix T d ℝ => scaledSuffix A ε m θ k (1 / t, h')) h u := by
  sorry

/-- The derivative of `𝓑_{>k}` in the weights at `t^m h`, from the map at `(1/t, h)`. -/
theorem fderiv_params_suffix_pow_smul (hχ : A.χ = rmsNorm ε) (θ η : Params A dIn dOut)
    (k : Fin (L + 1)) {t : ℝ} (ht : 0 < t) (m : ℕ) (h : Matrix T d ℝ) :
    fderiv ℝ (fun θ' : Params A dIn dOut => suffix A 0 θ' k (t ^ m • h)) θ η
      = fderiv ℝ (fun θ' : Params A dIn dOut => scaledSuffix A ε m θ' k (1 / t, h)) θ η := by
  sorry

end Skips
