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
  infinity (`MeromorphicAtInfinity`, `Activations/MillsAtInfinity.lean`; the proof takes the
  exponent `l = 0`): it is a real-analytic function of `1/t` near `1/t = 0`;
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

/-- Helper: the iterated derivative of `y ↦ g (c y)` for a scalar `c ≠ 0`: `c^i` times the
iterated derivative of `g` at `c x` (a composition with a continuous linear equivalence, no
smoothness needed). -/
private theorem iteratedFDeriv_comp_smul_ord {F G : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G] (g : F → G) {c : ℝ} (hc : c ≠ 0)
    (i : ℕ) (x : F) (v : Fin i → F) :
    iteratedFDeriv ℝ i (fun y => g (c • y)) x v = c ^ i • iteratedFDeriv ℝ i g (c • x) v := by
  -- `y ↦ c y` as a continuous linear equivalence
  let e : F ≃L[ℝ] F := ContinuousLinearEquiv.smulLeft (Units.mk0 c hc)
  have he : ∀ y, e y = c • y := fun y => rfl
  have h1 : (fun y => g (c • y)) = g ∘ e := funext fun y => by rw [Function.comp_apply, he]
  have h2 := e.iteratedFDerivWithin_comp_right g uniqueDiffOn_univ (Set.mem_univ (e x)) i
  rw [Set.preimage_univ, iteratedFDerivWithin_univ, iteratedFDerivWithin_univ] at h2
  rw [h1, h2, ContinuousMultilinearMap.compContinuousLinearMap_apply]
  -- pull the `i` factors `c` out
  have h3 : (fun j => (e : F →L[ℝ] F) (v j)) = fun j => (fun _ => c) j • v j := rfl
  rw [h3, ContinuousMultilinearMap.map_smul_univ, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, he]

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
  -- by the scaling identity, `h' ↦ 𝓑^♯(N_{ε t^{-2m}}(h'))` is `h' ↦ 𝓑_{>k}(t^m h')`
  have hfun : (fun h' : Matrix T d ℝ => scaledSuffix A ε m θ k (1 / t, h'))
      = fun h' => suffix A 0 θ k (t ^ m • h') :=
    funext fun h' => (suffix_pow_smul_eq_scaledSuffix A hχ θ k ht m h').symm
  rw [hfun]
  -- a derivative of order `i` of `h' ↦ g (t^m h')` is `t^{m i}` times that of `g` at `t^m H`
  have hc := iteratedFDeriv_comp_smul_ord (fun h' : Matrix T d ℝ => suffix A 0 θ k h')
    (pow_ne_zero m ht.ne') i H v
  exact hc.symm

/-- Helper: where `Ψ` is analytic on an open set containing `(a, b)`, the iterated derivative of
`y ↦ Ψ (a, y)` at `b` is that of `Ψ` at `(a, b)` on vectors `(0, v_j)`. -/
private theorem iteratedFDeriv_slice_ord {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {Ψ : E × F → G} {U : Set (E × F)} (hU : IsOpen U) (hΨ : AnalyticOnNhd ℝ Ψ U) {a : E} {b : F}
    (hab : (a, b) ∈ U) (i : ℕ) :
    iteratedFDeriv ℝ i (fun y => Ψ (a, y)) b
      = (iteratedFDeriv ℝ i Ψ (a, b)).compContinuousLinearMap
          fun _ => ContinuousLinearMap.inr ℝ E F := by
  -- `y ↦ Ψ (a, y)` is `Ψ' ∘ inr` with the translate `Ψ' z = Ψ ((a, 0) + z)`
  set Ψ' : E × F → G := fun z => Ψ ((a, 0) + z) with hΨ'
  have h1 : (fun y => Ψ (a, y)) = Ψ' ∘ ContinuousLinearMap.inr ℝ E F := funext fun y => by
    simp only [hΨ', Function.comp_apply, ContinuousLinearMap.inr_apply, Prod.mk_add_mk, add_zero,
      zero_add]
  -- `Ψ'` is analytic on the open set `W`, which contains `(0, b)`
  set W : Set (E × F) := (fun z => (a, 0) + z) ⁻¹' U with hW
  have hWo : IsOpen W := hU.preimage (continuous_const.add continuous_id)
  have hbW : ContinuousLinearMap.inr ℝ E F b ∈ W := by
    simp only [hW, Set.mem_preimage, ContinuousLinearMap.inr_apply, Prod.mk_add_mk, add_zero,
      zero_add]
    exact hab
  have hΨ'a : AnalyticOnNhd ℝ Ψ' W := fun z hz =>
    (hΨ _ hz).comp (analyticAt_const.add analyticAt_id)
  have hΨ'c : ContDiffOn ℝ i Ψ' W := hΨ'a.contDiffOn hWo.uniqueDiffOn
  have hpre : IsOpen ((ContinuousLinearMap.inr ℝ E F) ⁻¹' W) :=
    hWo.preimage (ContinuousLinearMap.inr ℝ E F).continuous
  have h2 := (ContinuousLinearMap.inr ℝ E F).iteratedFDerivWithin_comp_right hΨ'c
    hWo.uniqueDiffOn hpre.uniqueDiffOn hbW (le_refl (i : WithTop ℕ∞))
  rw [iteratedFDerivWithin_of_isOpen i hpre hbW, iteratedFDerivWithin_of_isOpen i hWo hbW] at h2
  rw [h1, h2, hΨ', iteratedFDeriv_comp_add_left]
  simp only [ContinuousLinearMap.inr_apply, Prod.mk_add_mk, add_zero, zero_add]

/-- Helper: if `Ψ` is analytic at `(a, b)`, then `a' ↦ 𝐃^i_y Ψ(a', y)|_{y = b} (v)` is analytic at
`a`. -/
private theorem analyticAt_iteratedFDeriv_slice_ord {E F G : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [CompleteSpace G] {Ψ : E × F → G} {a : E} {b : F}
    (hΨ : AnalyticAt ℝ Ψ (a, b)) (i : ℕ) (v : Fin i → F) :
    AnalyticAt ℝ (fun a' => iteratedFDeriv ℝ i (fun y => Ψ (a', y)) b v) a := by
  -- `Ψ` is analytic on the open set `U` of the points where it is analytic
  set U : Set (E × F) := {z | AnalyticAt ℝ Ψ z} with hUdef
  have hUo : IsOpen U := isOpen_analyticAt ℝ Ψ
  have hΨU : AnalyticOnNhd ℝ Ψ U := fun z hz => hz
  -- the iterated derivative of `Ψ` is analytic at `(a, b)`, and so is its value on `(0, v_j)`
  have hD := hΨU.iteratedFDeriv i (a, b) hΨ
  have hpath : AnalyticAt ℝ (fun a' : E => (a', b)) a := analyticAt_id.prod analyticAt_const
  have hc : AnalyticAt ℝ (fun a' => iteratedFDeriv ℝ i Ψ (a', b)
      (fun j => ContinuousLinearMap.inr ℝ E F (v j))) a :=
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin i => E × F) G
      (fun j => ContinuousLinearMap.inr ℝ E F (v j))).analyticAt _ |>.comp
      (hD.comp_of_eq hpath rfl)
  refine hc.congr ?_
  -- near `a`, `(a', b) ∈ U`, and there the two agree
  have hev : ∀ᶠ a' in 𝓝 a, (a', b) ∈ U :=
    (continuous_id.prodMk continuous_const).continuousAt.preimage_mem_nhds (hUo.mem_nhds hΨ)
  filter_upwards [hev] with a' ha'
  rw [iteratedFDeriv_slice_ord hUo hΨU ha' i,
    ContinuousMultilinearMap.compContinuousLinearMap_apply]

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
  -- `(s', h') ↦ 𝓑^♯(N_{ε s'^{2m}}(h'))` with the weights `θ` is analytic at `(s, H)`
  have h1 := analyticAt_scaledSuffix A hε hχ hf m θ k s H hH
  have hp : AnalyticAt ℝ (fun z : ℝ × Matrix T d ℝ =>
      ((θ, z) : Params A dIn dOut × ℝ × Matrix T d ℝ)) (s, H) :=
    analyticAt_const.prod analyticAt_id
  have h2 : AnalyticAt ℝ (fun z : ℝ × Matrix T d ℝ => scaledSuffix A ε m θ k z) (s, H) := by
    have hc := h1.comp_of_eq hp rfl
    exact hc
  -- so its derivative of order `i` in `h'` alone, applied to `v`, is analytic in `s'`
  have h3 := analyticAt_iteratedFDeriv_slice_ord h2 i v
  exact h3

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
  -- by the scaling identity for every `θ'`, the map of `h'` is `h' ↦ g (t^m h')` with
  -- `g h = 𝐃_θ 𝓑_{>k}(h) η`
  have hfun : (fun h' : Matrix T d ℝ =>
        fderiv ℝ (fun θ' : Params A dIn dOut => scaledSuffix A ε m θ' k (1 / t, h')) θ η)
      = fun h' => fderiv ℝ (fun θ' : Params A dIn dOut => suffix A 0 θ' k (t ^ m • h')) θ η :=
    funext fun h' => (fderiv_params_suffix_pow_smul A hχ θ η k ht m h').symm
  rw [hfun]
  have hc := iteratedFDeriv_comp_smul_ord (fun h' : Matrix T d ℝ =>
    fderiv ℝ (fun θ' : Params A dIn dOut => suffix A 0 θ' k h') θ η) (pow_ne_zero m ht.ne') i H v
  exact hc.symm

/-- Helper: if `Φ` is analytic at `(a, b)`, then `z ↦ 𝐃_x Φ(x, z)|_{x = a} η` is analytic at
`b`. -/
private theorem analyticAt_fderiv_fst_ord {E F G : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [CompleteSpace G] {Φ : E × F → G} {a : E} {b : F}
    (hΦ : AnalyticAt ℝ Φ (a, b)) (η : E) :
    AnalyticAt ℝ (fun z => fderiv ℝ (fun x => Φ (x, z)) a η) b := by
  set U : Set (E × F) := {p | AnalyticAt ℝ Φ p} with hUdef
  have hUo : IsOpen U := isOpen_analyticAt ℝ Φ
  -- `z ↦ 𝐃Φ(a, z)(η, 0)` is analytic at `b`
  have hpath : AnalyticAt ℝ (fun z : F => (a, z)) b := analyticAt_const.prod analyticAt_id
  have hc : AnalyticAt ℝ (fun z => fderiv ℝ Φ (a, z) (η, 0)) b :=
    (ContinuousLinearMap.apply ℝ G ((η, 0) : E × F)).analyticAt _ |>.comp
      (hΦ.fderiv.comp_of_eq hpath rfl)
  refine hc.congr ?_
  -- near `b`, `Φ` is differentiable at `(a, z)`, and the chain rule with `x ↦ (x, z)`
  have hev : ∀ᶠ z in 𝓝 b, (a, z) ∈ U :=
    (continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds (hUo.mem_nhds hΦ)
  filter_upwards [hev] with z hz
  have hd : HasFDerivAt Φ (fderiv ℝ Φ (a, z)) (a, z) :=
    (AnalyticAt.differentiableAt hz).hasFDerivAt
  have h2 := (hd.comp a (hasFDerivAt_prodMk_left (𝕜 := ℝ) a z)).fderiv
  have h3 : fderiv ℝ (fun x => Φ (x, z)) a η = fderiv ℝ Φ (a, z) (η, 0) := by
    have h4 := DFunLike.congr_fun h2 η
    exact h4
  exact h3.symm

/-- **Lemma D.10, "The weights enter analytically as well":** under pre-RMSNorm with `ε > 0`
and for real-analytic blocks, `(s, h) ↦ 𝐃_θ 𝓑^♯(N_{ε s^{2m}}(h)) η` is real-analytic at every
`(s, H)` such that no row of `H` vanishes, also at `s = 0`. -/
theorem analyticAt_fderiv_params_scaledSuffix (hε : 0 < ε) (hχ : A.χ = rmsNorm ε)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (m : ℕ) (θ η : Params A dIn dOut)
    (k : Fin (L + 1)) (s : ℝ) (H : Matrix T d ℝ) (hH : ∀ τ, H τ ≠ 0) :
    AnalyticAt ℝ (fun z : ℝ × Matrix T d ℝ =>
      fderiv ℝ (fun θ' : Params A dIn dOut => scaledSuffix A ε m θ' k z) θ η) (s, H) := by
  -- `(θ', z) ↦ 𝓑^♯(N_{ε s^{2m}}(h))` is analytic at `(θ, s, H)`, and so is its derivative in
  -- `θ'` alone applied to `η`, as a function of `z`
  have h1 := analyticAt_scaledSuffix A hε hχ hf m θ k s H hH
  have h2 := analyticAt_fderiv_fst_ord h1 η
  exact h2

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
  -- `(s', h') ↦ 𝐃_θ 𝓑^♯(N_{ε s'^{2m}}(h')) η` is analytic at `(s, H)`
  have h1 := analyticAt_fderiv_params_scaledSuffix A hε hχ hf m θ η k s H hH
  -- so its derivative of order `i` in `h'` alone, applied to `v`, is analytic in `s'`
  have h2 := analyticAt_iteratedFDeriv_slice_ord h1 i v
  exact h2

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
