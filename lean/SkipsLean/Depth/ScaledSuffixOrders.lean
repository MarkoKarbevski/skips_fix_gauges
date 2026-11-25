import SkipsLean.Depth.ScaledSuffix
import SkipsLean.Activations.MillsAtInfinity

/-!
# The rest of the network on a ray: derivatives of all orders, meromorphic at infinity

Paper (dimension), Lemma D.10 (The rest of the network on a ray): "In the case (+), let `k ≤ L`,
let `h° ≠ 0` be a row, let `v_1, …, v_i` be rows, and let `η` be a direction of the weights of the
blocks `k+1, …, L` and of `D`. With `𝐃^i` the derivative of order `i` in `h`, the maps
`t ↦ t^i 𝐃^i 𝓑_{>k}(t h°)(v_1, …, v_i)` and `t ↦ t^i 𝐃^i (𝐃_θ 𝓑_{>k}(·) η)(t h°)(v_1, …, v_i)` are
real-analytic functions of `1/t` near `1/t = 0`, so they are meromorphic at infinity." Its proof:
"So `𝓑_{>k}(t (h° + u))` is a real-analytic function of `(1/t, u)` near `(0, 0)`. […] A derivative
of order `i` in `v = t u` at `v = 0` is `t^{−i}` times the derivative of order `i` in `u` at
`u = 0`. The weights enter analytically as well, which gives the same for `𝐃_θ 𝓑_{>k}(·) η`."

`Depth/ScaledSuffix.lean` has the map `(s, h) ↦ 𝓑^♯(N_{ε s^{2m}}(h))` (`scaledSuffix`), which is
`𝓑_{>k}(t^m h)` at `s = 1/t`, its real-analyticity in `(θ, s, h)` also at `s = 0`, and the first
derivatives. Here, for every order `i`, with `t^m` in the place of `t` as there (the proof of
Lemma D.12 uses the lemma "with `t^m` in the place of `t`"), for hidden states `H` of all tokens
without zero rows, and for every direction `η` of the weights:

* `iteratedFDeriv_suffix_pow_smul`: `t^{m i} 𝐃^i 𝓑_{>k}(t^m H)(v)` is the derivative of order `i`
  in `h` of the map at `(1/t, H)`; `analyticAt_iteratedFDeriv_scaledSuffix`: that derivative is a
  real-analytic function of `s`, also at `s = 0`;
* `meromorphicAtInfinity_iteratedFDeriv_suffix_pow`, and in the paper's form (`m = 1`)
  `meromorphicAtInfinity_iteratedFDeriv_suffix`: the first map of the lemma is meromorphic at
  infinity (`MeromorphicAtInfinity`, `Activations/MillsAtInfinity.lean`), with the exponent
  `l = 0`: it is a real-analytic function of `1/t` near `1/t = 0`;
* the same four statements for `𝐃_θ 𝓑_{>k}(·) η`, and `analyticAt_fderiv_params_scaledSuffix`:
  "The weights enter analytically as well", the derivative in the weights is real-analytic in
  `(s, h)`.

The holomorphic extension in `u` with bounds uniform in `t` (the second sentence of the lemma):
`Depth/ScaledSuffixHolomorphic.lean`.
-/

namespace Skips

open Matrix Filter
open scoped Matrix.Norms.Elementwise Topology

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable (A : Arch T d L) {ε : ℝ}

/-- **Lemma D.10, "A derivative of order `i` in `v = t u` at `v = 0` is `t^{−i}` times the
derivative of order `i` in `u` at `u = 0`":** under pre-RMSNorm, for `t > 0`,
`t^{m i} 𝐃^i 𝓑_{>k}(t^m H)(v_1, …, v_i)` is the derivative of order `i` in the hidden state of
`h ↦ 𝓑^♯(N_{ε t^{−2m}}(h))` at `H`. -/
theorem iteratedFDeriv_suffix_pow_smul (hχ : A.χ = rmsNorm ε) (θ : Params A dIn dOut)
    (k : Fin (L + 1)) {t : ℝ} (ht : 0 < t) (m i : ℕ) (H : Matrix T d ℝ)
    (v : Fin i → Matrix T d ℝ) :
    (t ^ m) ^ i • iteratedFDeriv ℝ i (fun h' : Matrix T d ℝ => suffix A 0 θ k h') (t ^ m • H) v
      = iteratedFDeriv ℝ i
          (fun h' : Matrix T d ℝ => scaledSuffix A ε m θ k (1 / t, h')) H v := by
  sorry

/-- **Lemma D.10, the derivatives of all orders as functions of `s = 1/t`:** under pre-RMSNorm
with `ε > 0` and for real-analytic blocks, the derivative of order `i` in the hidden state of
`h ↦ 𝓑^♯(N_{ε s^{2m}}(h))` at a hidden state `H` without zero rows, applied to `v_1, …, v_i`, is
a real-analytic function of `s` at every `s`, also at `s = 0`. -/
theorem analyticAt_iteratedFDeriv_scaledSuffix (hε : 0 < ε) (hχ : A.χ = rmsNorm ε)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (m i : ℕ) (θ : Params A dIn dOut)
    (k : Fin (L + 1)) (s : ℝ) (H : Matrix T d ℝ) (hH : ∀ τ, H τ ≠ 0)
    (v : Fin i → Matrix T d ℝ) :
    AnalyticAt ℝ (fun s' : ℝ => iteratedFDeriv ℝ i
      (fun h' : Matrix T d ℝ => scaledSuffix A ε m θ k (s', h')) H v) s := by
  sorry

/-- **Lemma D.10, first map, with `t^m` in the place of `t`:**
`t ↦ t^{m i} 𝐃^i 𝓑_{>k}(t^m H)(v_1, …, v_i)` is a real-analytic function of `1/t` near
`1/t = 0`, so it is meromorphic at infinity. -/
theorem meromorphicAtInfinity_iteratedFDeriv_suffix_pow (hε : 0 < ε) (hχ : A.χ = rmsNorm ε)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (m i : ℕ) (θ : Params A dIn dOut)
    (k : Fin (L + 1)) (H : Matrix T d ℝ) (hH : ∀ τ, H τ ≠ 0) (v : Fin i → Matrix T d ℝ) :
    MeromorphicAtInfinity (fun t : ℝ => (t ^ m) ^ i
      • iteratedFDeriv ℝ i (fun h' : Matrix T d ℝ => suffix A 0 θ k h') (t ^ m • H) v) := by
  refine ⟨0, fun s => iteratedFDeriv ℝ i
    (fun h' : Matrix T d ℝ => scaledSuffix A ε m θ k (s, h')) H v,
    analyticAt_iteratedFDeriv_scaledSuffix A hε hχ hf m i θ k 0 H hH v, ?_⟩
  filter_upwards [eventually_gt_atTop 0] with t ht
  rw [pow_zero, one_smul]
  exact iteratedFDeriv_suffix_pow_smul A hχ θ k ht m i H v

/-- **Lemma D.10, first map:** `t ↦ t^i 𝐃^i 𝓑_{>k}(t H)(v_1, …, v_i)` is a real-analytic
function of `1/t` near `1/t = 0`, so it is meromorphic at infinity. -/
theorem meromorphicAtInfinity_iteratedFDeriv_suffix (hε : 0 < ε) (hχ : A.χ = rmsNorm ε)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (i : ℕ) (θ : Params A dIn dOut)
    (k : Fin (L + 1)) (H : Matrix T d ℝ) (hH : ∀ τ, H τ ≠ 0) (v : Fin i → Matrix T d ℝ) :
    MeromorphicAtInfinity (fun t : ℝ => t ^ i
      • iteratedFDeriv ℝ i (fun h' : Matrix T d ℝ => suffix A 0 θ k h') (t • H) v) := by
  simpa only [pow_one] using
    meromorphicAtInfinity_iteratedFDeriv_suffix_pow A hε hχ hf 1 i θ k H hH v

/-- **Lemma D.10, the derivative in the weights, "The weights enter analytically as well, which
gives the same for `𝐃_θ 𝓑_{>k}(·) η`":** under pre-RMSNorm, for `t > 0`,
`t^{m i} 𝐃^i (𝐃_θ 𝓑_{>k}(·) η)(t^m H)(v_1, …, v_i)` is the derivative of order `i` in the hidden
state of `h ↦ 𝐃_θ 𝓑^♯(N_{ε t^{−2m}}(h)) η` at `H`. -/
theorem iteratedFDeriv_fderiv_params_suffix_pow_smul (hχ : A.χ = rmsNorm ε)
    (θ η : Params A dIn dOut) (k : Fin (L + 1)) {t : ℝ} (ht : 0 < t) (m i : ℕ)
    (H : Matrix T d ℝ) (v : Fin i → Matrix T d ℝ) :
    (t ^ m) ^ i • iteratedFDeriv ℝ i (fun h' : Matrix T d ℝ =>
        fderiv ℝ (fun θ' : Params A dIn dOut => suffix A 0 θ' k h') θ η) (t ^ m • H) v
      = iteratedFDeriv ℝ i (fun h' : Matrix T d ℝ =>
        fderiv ℝ (fun θ' : Params A dIn dOut => scaledSuffix A ε m θ' k (1 / t, h')) θ η) H v := by
  sorry

/-- **Lemma D.10, "The weights enter analytically as well":** under pre-RMSNorm with `ε > 0`
and for real-analytic blocks, `(s, h) ↦ 𝐃_θ 𝓑^♯(N_{ε s^{2m}}(h)) η` is real-analytic at every
`(s, H)` such that no row of `H` vanishes, also at `s = 0`. -/
theorem analyticAt_fderiv_params_scaledSuffix (hε : 0 < ε) (hχ : A.χ = rmsNorm ε)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (m : ℕ) (θ η : Params A dIn dOut)
    (k : Fin (L + 1)) (s : ℝ) (H : Matrix T d ℝ) (hH : ∀ τ, H τ ≠ 0) :
    AnalyticAt ℝ (fun z : ℝ × Matrix T d ℝ =>
      fderiv ℝ (fun θ' : Params A dIn dOut => scaledSuffix A ε m θ' k z) θ η) (s, H) := by
  sorry

/-- **Lemma D.10, the derivative in the weights, as a function of `s = 1/t`:** under
pre-RMSNorm with `ε > 0` and for real-analytic blocks, the derivative of order `i` in the hidden
state of `h ↦ 𝐃_θ 𝓑^♯(N_{ε s^{2m}}(h)) η` at a hidden state `H` without zero rows is a
real-analytic function of `s` at every `s`, also at `s = 0`. -/
theorem analyticAt_iteratedFDeriv_fderiv_params_scaledSuffix (hε : 0 < ε)
    (hχ : A.χ = rmsNorm ε) (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (m i : ℕ)
    (θ η : Params A dIn dOut) (k : Fin (L + 1)) (s : ℝ) (H : Matrix T d ℝ)
    (hH : ∀ τ, H τ ≠ 0) (v : Fin i → Matrix T d ℝ) :
    AnalyticAt ℝ (fun s' : ℝ => iteratedFDeriv ℝ i (fun h' : Matrix T d ℝ =>
      fderiv ℝ (fun θ' : Params A dIn dOut => scaledSuffix A ε m θ' k (s', h')) θ η) H v) s := by
  sorry

/-- **Lemma D.10, second map, with `t^m` in the place of `t`:**
`t ↦ t^{m i} 𝐃^i (𝐃_θ 𝓑_{>k}(·) η)(t^m H)(v_1, …, v_i)` is a real-analytic function of `1/t`
near `1/t = 0`, so it is meromorphic at infinity. -/
theorem meromorphicAtInfinity_iteratedFDeriv_fderiv_params_suffix_pow (hε : 0 < ε)
    (hχ : A.χ = rmsNorm ε) (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (m i : ℕ)
    (θ η : Params A dIn dOut) (k : Fin (L + 1)) (H : Matrix T d ℝ) (hH : ∀ τ, H τ ≠ 0)
    (v : Fin i → Matrix T d ℝ) :
    MeromorphicAtInfinity (fun t : ℝ => (t ^ m) ^ i • iteratedFDeriv ℝ i
      (fun h' : Matrix T d ℝ => fderiv ℝ (fun θ' : Params A dIn dOut => suffix A 0 θ' k h') θ η)
      (t ^ m • H) v) := by
  refine ⟨0, fun s => iteratedFDeriv ℝ i (fun h' : Matrix T d ℝ =>
    fderiv ℝ (fun θ' : Params A dIn dOut => scaledSuffix A ε m θ' k (s, h')) θ η) H v,
    analyticAt_iteratedFDeriv_fderiv_params_scaledSuffix A hε hχ hf m i θ η k 0 H hH v, ?_⟩
  filter_upwards [eventually_gt_atTop 0] with t ht
  rw [pow_zero, one_smul]
  exact iteratedFDeriv_fderiv_params_suffix_pow_smul A hχ θ η k ht m i H v

/-- **Lemma D.10, second map:** `t ↦ t^i 𝐃^i (𝐃_θ 𝓑_{>k}(·) η)(t H)(v_1, …, v_i)` is a
real-analytic function of `1/t` near `1/t = 0`, so it is meromorphic at infinity. -/
theorem meromorphicAtInfinity_iteratedFDeriv_fderiv_params_suffix (hε : 0 < ε)
    (hχ : A.χ = rmsNorm ε) (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (i : ℕ)
    (θ η : Params A dIn dOut) (k : Fin (L + 1)) (H : Matrix T d ℝ) (hH : ∀ τ, H τ ≠ 0)
    (v : Fin i → Matrix T d ℝ) :
    MeromorphicAtInfinity (fun t : ℝ => t ^ i • iteratedFDeriv ℝ i
      (fun h' : Matrix T d ℝ => fderiv ℝ (fun θ' : Params A dIn dOut => suffix A 0 θ' k h') θ η)
      (t • H) v) := by
  simpa only [pow_one] using
    meromorphicAtInfinity_iteratedFDeriv_fderiv_params_suffix_pow A hε hχ hf 1 i θ η k H hH v

end Skips
