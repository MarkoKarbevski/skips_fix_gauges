import SkipsLean.Depth.FrozenFar
import SkipsLean.Depth.RayInduction
import SkipsLean.Depth.RayDense

/-!
# Lemma D.12 on a ray, for gated blocks without normalization: from (28) to (38)

Paper (dimension): Appendix D.5, proof of Lemma D.12, from its beginning to equation (38), in the
case (n). "Let `Z` and `η` satisfy (16) for `k`, so that (28) holds […]. Let `𝓑^∞ = 𝓑°_{>k+1}` in
the case (n), and let `𝓛^∞` be (27) with `𝓑^∞` in the place of `𝓑`." On a ray `n = t ξ` with
`ξ ∈ C_k`, (24) turns (28) into (33), the expansion (34) in the small terms `δ_j(t)` of the gates
has the three properties (a), (b), (c), and for a generic ray, that is, for `ξ ∈ C_k` such that

  (i) the numbers `r_1, …, r_q` are linearly independent over `ℚ` (`r_j = |ξ c_j|^p`);
  (ii) `ι_j(ξ) ≠ 0` for every `j`;
  (iii) `g°(ξ) ∈ U^∞`,

the induction on the exponents shows that all coefficients vanish. "What the induction gives. For
this `ξ` and every `t > 0`, all coefficients of the expansion of `(w̃, w̃') ↦ 𝓛^∞(w̃, w̃'; t ξ)` at
`(t ξ W_g I_A, 1_A)` vanish, so this real-analytic map vanishes. The rows `t ξ` of this kind are
dense in `C_k`. So, with (37), for all `n ∈ C_k` and all rows `w̃ ∈ ℝ^{1×q}`, with `ŵ = w̃ ⊙ ι(n)`,

  `ż^g(n) = 0`,   `𝐃𝓑^∞(ŵ V) ((w̃ ⊙ ż^v(n)) V + ŵ η_V) + 𝐃_θ 𝓑^∞(ŵ V) η' = 0`.   (38)"

Stated here, for a gate `σ` with `GateFar σ σ' p` and hidden states with the rows `T`: (38) at one
generic `Ξ` (one row `ξ_t` per token; (i) is asked of the numbers `|ξ_t c_j|^p` over all tokens and
hidden units, and (iii) says that the derivative of the frozen network after the block is injective
at `g°(Ξ)`, which is what the proof uses of `U^∞`); then (38) for all `n` with rows in `C_k`, given
that the `Ξ` with (i) are dense; then the same for SwiGLU and GeGLU blocks from the independence
over `ℚ` of (K3) for block `k`. The first part of (38), `ż^g(n) = 0` on an open set of `n`, is
stated as `Z W_g + η_g = 0`. The second part is written with `writeLHS` for the frozen network at
`v = w̃ ⊙ ι(n)`, `vdot = w̃ ⊙ ż^v(n)`.

In the case (n) the frozen network is homogeneous (`suffix_frozen_smul`), so that
`𝓛^∞(t (W° + y), w̃'; t ξ) = t^{2 · 2^{L−k−1}} 𝓛^∞(W° + y, w̃'; ξ)`: the coefficients of (34) are
constants times powers of `t`, which is fact (a) in this case. Fact (b) is Lemma D.11
(`exists_far_frozen_bounds`), and the induction is `ray_induction_matrix`.
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise Topology

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]
variable {σ σ' : ℝ → ℝ} {p : ℕ}

section Helpers

open Filter

/-- Helper: for `Φ` differentiable at `(x, y)`, the derivatives of its two partial maps, along `b`
and `a`, add up to its derivative along `(a, b)` (as in `Depth/StepTanh.lean`). -/
private theorem fderiv_partial_addR {E₁ E₂ F : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {Φ : E₁ → E₂ → F} {x : E₁} {y : E₂}
    (hΦ : DifferentiableAt ℝ (fun p : E₁ × E₂ => Φ p.1 p.2) (x, y)) (a : E₁) (b : E₂) :
    fderiv ℝ (fun y' => Φ x y') y b + fderiv ℝ (fun x' => Φ x' y) x a
      = fderiv ℝ (fun p : E₁ × E₂ => Φ p.1 p.2) (x, y) (a, b) := by
  have h1 : HasFDerivAt (fun x' => Φ x' y)
      ((fderiv ℝ (fun p : E₁ × E₂ => Φ p.1 p.2) (x, y)).comp
        (ContinuousLinearMap.inl ℝ E₁ E₂)) x := by
    have hc := hΦ.hasFDerivAt.comp x (hasFDerivAt_prodMk_left (𝕜 := ℝ) x y)
    exact hc
  have h2 : HasFDerivAt (fun y' => Φ x y')
      ((fderiv ℝ (fun p : E₁ × E₂ => Φ p.1 p.2) (x, y)).comp
        (ContinuousLinearMap.inr ℝ E₁ E₂)) y := by
    have hc := hΦ.hasFDerivAt.comp y (hasFDerivAt_prodMk_right (𝕜 := ℝ) x y)
    exact hc
  rw [h1.fderiv, h2.fderiv, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.inl_apply, ContinuousLinearMap.inr_apply, ← map_add, Prod.mk_add_mk,
    zero_add, add_zero]

/-- Helper: an analytic family of continuous linear maps, applied to an analytic family of vectors,
is analytic (as in `Depth/StepTanh.lean`). -/
private theorem analyticOnNhd_clm_applyR {X E F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {J : X → E →L[ℝ] F} {v : X → E} {s : Set X} (hJ : AnalyticOnNhd ℝ J s)
    (hv : AnalyticOnNhd ℝ v s) : AnalyticOnNhd ℝ (fun x => J x (v x)) s :=
  fun x hx => ((ContinuousLinearMap.id ℝ (E →L[ℝ] F)).analyticAt_bilinear (J x, v x)).comp₂
    (hJ x hx) (hv x hx)

omit [Fintype T] [DecidableEq d] in
/-- Helper: the left side of the identity for one block is affine in `vdot`: a change `D` of
`vdot` changes it by `𝐃𝓑(v V)(D V)`. -/
private theorem writeLHS_add_vdot (Ar : Arch T d L) (θ η : Params Ar dIn dOut) (k : Fin L)
    (v vdot D : Matrix T (Ar.w k) ℝ) :
    writeLHS Ar θ k η v (vdot + D)
      = writeLHS Ar θ k η v vdot
        + fderiv ℝ (fun h' : Matrix T d ℝ => suffix Ar 0 θ k.succ h') (v * θ.write k)
            (D * θ.write k) := by
  unfold writeLHS
  rw [Matrix.add_mul, add_right_comm _ (D * θ.write k), map_add]
  abel

/-- Helper: the left side of the identity for one block of the frozen network is real-analytic in
`v` and `vdot`: it is the derivative of `(θ', h) ↦ 𝓑°(h)` at `(θ, v V)` along
`(η, vdot V + v η_V)`. -/
private theorem analyticOnNhd_writeLHS_frozen {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] (A : ∀ ℓ, Finset (hid ℓ))
    (θ η : Params (Arch.frozen (T := T) (d := d) A) dIn dOut) (k : Fin L)
    {v vdot : X → Matrix T (hid k) ℝ} (hv : AnalyticOnNhd ℝ v Set.univ)
    (hvd : AnalyticOnNhd ℝ vdot Set.univ) :
    AnalyticOnNhd ℝ (fun x => writeLHS (Arch.frozen A) θ k η (v x) (vdot x)) Set.univ := by
  have hΦ := analyticOnNhd_suffix_prod (Arch.frozen (T := T) (d := d) A) (dIn := dIn)
    (dOut := dOut) rfl (analyticOnNhd_f_frozen A) k.succ
  have heq : (fun x => writeLHS (Arch.frozen A) θ k η (v x) (vdot x)) = fun x => fderiv ℝ
      (fun p : Params (Arch.frozen (T := T) (d := d) A) dIn dOut × Matrix T d ℝ =>
        suffix (Arch.frozen A) 0 p.1 k.succ p.2)
      (θ, v x * θ.write k) (η, vdot x * θ.write k + v x * η.write k) := by
    funext x
    exact fderiv_partial_addR
      (Φ := fun θ' h' => suffix (Arch.frozen (T := T) (d := d) A) 0 θ' k.succ h')
      (hΦ _ (Set.mem_univ _)).differentiableAt η _
  rw [heq]
  exact analyticOnNhd_clm_applyR (hΦ.fderiv.comp (analyticOnNhd_const.prod
      (analyticOnNhd_matrix_mul hv analyticOnNhd_const)) (Set.mapsTo_univ _ _))
    (analyticOnNhd_const.prod ((analyticOnNhd_matrix_mul hvd analyticOnNhd_const).add
      (analyticOnNhd_matrix_mul hv analyticOnNhd_const)))

/-- Helper: a real function that is at most a power of `t` times `e^{-κ t^p}` tends to `0`. -/
private theorem tendsto_zero_of_abs_le_pow_mul_exp {f : ℝ → ℝ} {B κ : ℝ} {N q : ℕ}
    (hκ : 0 < κ) (hq : 1 ≤ q)
    (hf : ∀ᶠ t in atTop, |f t| ≤ B * t ^ N * Real.exp (-(κ * t ^ q))) :
    Tendsto f atTop (𝓝 0) := by
  have h := (fasterThanPowers_iff f).1 (fasterThanPowers_of_le_pow_mul_exp hκ hq
    (by simpa only [Real.norm_eq_abs] using hf)) 0
  simp only [pow_zero, one_mul] at h
  exact tendsto_zero_iff_norm_tendsto_zero.2 h

/-- Helper: `e^{-κ t^{2p}} (t² C + 1) ≤ e^{-R t^p}` for all large `t`, for `κ > 0`. -/
private theorem eventually_exp_mul_le {κ : ℝ} (hκ : 0 < κ) (hp : 1 ≤ p) (C R : ℝ) :
    ∀ᶠ t : ℝ in atTop,
      Real.exp (-(κ * (t ^ 2) ^ p)) * (t ^ 2 * C + 1) ≤ Real.exp (-(R * t ^ p)) := by
  -- `f(t) = (t² C + 1) e^{-(κ/2) t^{2p}} → 0`
  have hf : Tendsto (fun t : ℝ => (t ^ 2 * C + 1) * Real.exp (-(κ / 2 * t ^ (2 * p))))
      atTop (𝓝 0) := by
    refine tendsto_zero_of_abs_le_pow_mul_exp (B := |C| + 1) (N := 2) (q := 2 * p) (half_pos hκ)
      (by omega) ?_
    filter_upwards [eventually_ge_atTop 1] with t ht
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
    have h1 : 1 ≤ t ^ 2 := one_le_pow₀ ht
    calc |t ^ 2 * C + 1| ≤ |t ^ 2 * C| + |1| := abs_add_le _ _
      _ = t ^ 2 * |C| + 1 := by
        rw [abs_mul, abs_of_nonneg (by positivity), abs_one]
      _ ≤ (|C| + 1) * t ^ 2 := by nlinarith [abs_nonneg C]
  have h1 := hf.eventually_lt_const one_pos
  -- `R t^p ≤ (κ/2) t^{2p}` for large `t`
  have h2 : ∀ᶠ t : ℝ in atTop, 2 * |R| / κ ≤ t ^ p :=
    (tendsto_pow_atTop (by omega : p ≠ 0)).eventually_ge_atTop _
  filter_upwards [h1, h2, eventually_ge_atTop 0] with t ht1 ht2 ht0
  have hpow : (t ^ 2) ^ p = t ^ p * t ^ p := by rw [← pow_mul, ← pow_add]; ring_nf
  have hpow' : t ^ (2 * p) = t ^ p * t ^ p := by rw [← pow_add]; ring_nf
  have htp : 0 ≤ t ^ p := pow_nonneg ht0 p
  have hR : R * t ^ p ≤ κ / 2 * (t ^ p * t ^ p) := by
    have h3 : 2 * |R| ≤ κ * t ^ p := by
      rw [div_le_iff₀ hκ] at ht2
      linarith
    nlinarith [le_abs_self R, abs_nonneg R]
  rw [hpow' ] at ht1
  calc Real.exp (-(κ * (t ^ 2) ^ p)) * (t ^ 2 * C + 1)
      = ((t ^ 2 * C + 1) * Real.exp (-(κ / 2 * (t ^ p * t ^ p))))
          * Real.exp (-(κ / 2 * (t ^ p * t ^ p))) := by
        rw [mul_assoc, ← Real.exp_add, hpow]
        ring_nf
    _ ≤ 1 * Real.exp (-(κ / 2 * (t ^ p * t ^ p))) :=
        mul_le_mul_of_nonneg_right ht1.le (Real.exp_pos _).le
    _ ≤ Real.exp (-(R * t ^ p)) := by
        rw [one_mul, Real.exp_le_exp]
        linarith

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: equation (25) on the ray, for one gate with `|ξ c_j| = u`: for `t u ≥ 2`, with
`δ = t u − σ(t u)` and `e = e^{-(u^p/p) t^p}`: `δ > 0`, `e ≤ 6 δ`, `δ ≤ t u e` and
`|δ'(t u)| ≤ 4 t u δ`. -/
private theorem gate_ray_bounds (hg : GateFar σ σ' p) {u t : ℝ} (h2 : 2 ≤ t * u) :
    0 < t * u - σ (t * u) ∧
      Real.exp (-(u ^ p / p * t ^ p)) ≤ 6 * (t * u - σ (t * u)) ∧
      t * u - σ (t * u) ≤ t * u * Real.exp (-(u ^ p / p * t ^ p)) ∧
      |1 - σ' (t * u)| ≤ 4 * (t * u) * (t * u - σ (t * u)) := by
  obtain ⟨h1, h2', h3⟩ := hg.gap (t * u) h2
  have he : (t * u) ^ p / (p : ℝ) = u ^ p / p * t ^ p := by rw [mul_pow]; ring
  rw [he] at h1 h2'
  exact ⟨lt_of_lt_of_le (by positivity) h1, by linarith, h2', h3⟩

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the bounds on the small terms `ζ = δ/t` and `ν = t δ'/δ` of one gate on the ray that
the induction on the exponents asks for, and `ν ζ = δ'`. -/
private theorem ray_small_bounds (hg : GateFar σ σ' p) {u t B : ℝ} (hu : 0 < u) (ht : 1 ≤ t)
    (h2 : 2 ≤ t * u) (hB6 : 6 ≤ B) (hBu : 4 * u ≤ B) :
    Real.exp (-(u ^ p / p * t ^ p)) ≤ B * t ^ 2 * ((t * u - σ (t * u)) / t) ∧
      |(t * u - σ (t * u)) / t| ≤ B * t ^ 2 * Real.exp (-(u ^ p / p * t ^ p)) ∧
      |t * (1 - σ' (t * u)) / (t * u - σ (t * u))| ≤ B * t ^ 2 ∧
      |(t * u - σ (t * u)) / t| ≤ u * t ^ 0 * Real.exp (-(u ^ p / p * t ^ p)) ∧
      |t * (1 - σ' (t * u)) / (t * u - σ (t * u)) * ((t * u - σ (t * u)) / t)|
        ≤ 4 * u ^ 2 * t ^ 2 * Real.exp (-(u ^ p / p * t ^ p)) ∧
      t * (1 - σ' (t * u)) / (t * u - σ (t * u)) * ((t * u - σ (t * u)) / t)
        = 1 - σ' (t * u) := by
  obtain ⟨hδ, h1, h2', h3⟩ := gate_ray_bounds hg h2
  have ht0 : 0 < t := by linarith
  have he := (Real.exp_pos (-(u ^ p / p * t ^ p))).le
  generalize t * u - σ (t * u) = δ at *
  generalize 1 - σ' (t * u) = δ' at *
  generalize Real.exp (-(u ^ p / p * t ^ p)) = e at *
  have hνζ : t * δ' / δ * (δ / t) = δ' := by field_simp
  refine ⟨?_, ?_, ?_, ?_, ?_, hνζ⟩
  · -- `e ≤ 6 δ ≤ B t δ = B t² (δ/t)`
    rw [show B * t ^ 2 * (δ / t) = B * t * δ by field_simp]
    have h6 : 6 ≤ B * t := by nlinarith
    have h7 : 6 * δ ≤ B * t * δ := mul_le_mul_of_nonneg_right h6 hδ.le
    linarith
  · -- `δ/t ≤ u e ≤ B t² e`
    rw [abs_of_pos (div_pos hδ ht0), div_le_iff₀ ht0]
    have h4 : t * u * e ≤ t * B * e := by gcongr; linarith
    have h5 : t * B * e ≤ B * t ^ 2 * e * t := by
      have : t ≤ t ^ 2 * t := by nlinarith
      nlinarith
    linarith
  · -- `t |δ'| / δ ≤ 4 u t² ≤ B t²`
    rw [abs_div, abs_mul, abs_of_pos ht0, abs_of_pos hδ, div_le_iff₀ hδ]
    have h4 : t * |δ'| ≤ t * (4 * (t * u) * δ) := by gcongr
    have h5 : 4 * u * (t ^ 2 * δ) ≤ B * (t ^ 2 * δ) :=
      mul_le_mul_of_nonneg_right hBu (by positivity)
    calc t * |δ'| ≤ t * (4 * (t * u) * δ) := h4
      _ = 4 * u * (t ^ 2 * δ) := by ring
      _ ≤ B * (t ^ 2 * δ) := h5
      _ = B * t ^ 2 * δ := by ring
  · rw [abs_of_pos (div_pos hδ ht0), div_le_iff₀ ht0, pow_zero, mul_one]
    linarith
  · rw [hνζ]
    calc |δ'| ≤ 4 * (t * u) * δ := h3
      _ ≤ 4 * (t * u) * (t * u * e) := by gcongr
      _ = 4 * u ^ 2 * t ^ 2 * e := by ring

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: `|ν(t)| = t |δ'(t u)| / δ(t u) → ∞` (the last property of `GateFar`, at `y = t u`). -/
private theorem tendsto_abs_nu (hg : GateFar σ σ' p) {u : ℝ} (hu : 0 < u) :
    Tendsto (fun t : ℝ => |t * (1 - σ' (t * u)) / (t * u - σ (t * u))|) atTop atTop := by
  have h := (hg.ratio.comp (tendsto_id.atTop_mul_const hu)).atTop_div_const hu
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop (2 / u), eventually_gt_atTop 0] with t ht ht0
  have h2 : 2 ≤ t * u := by rwa [div_le_iff₀ hu] at ht
  have hδ := (gate_ray_bounds hg h2).1
  simp only [Function.comp_apply, id]
  rw [abs_div, abs_mul, abs_of_pos ht0, abs_of_pos hδ]
  have := hu.ne'
  have := hδ.ne'
  field_simp

omit [DecidableEq d] in
/-- Helper: `‖b + d‖ ≤ ‖a − b‖ + ‖c − d‖` when `a + c = 0`. -/
private theorem norm_add_le_of_add_eq_zero {F : Type*} [NormedAddCommGroup F] {a b c e : F}
    (h : a + c = 0) : ‖b + e‖ ≤ ‖a - b‖ + ‖c - e‖ := by
  have : b + e = (a + c) - ((a - b) + (c - e)) := by abel
  rw [this, h, zero_sub, norm_neg]
  exact norm_add_le _ _

/-- Helper: **fact (b)**, case (n). Let `w(t) → w₀` and `ẇ(t) → ẇ₀`, let the rows of `w₀ V` lie
in `C_{k+1}`, and let the left side `𝓛` of the identity for block `k` vanish at
`(t² w(t), t² ẇ(t))` for large `t`. Then the left side `𝓛°` for the frozen network there is, for
every `R`, at most `e^{-R t^p}` for large `t`: Lemma D.11 with `t²` in the place of `t`. -/
private theorem eventually_norm_writeLHS_frozen_le (hg : GateFar σ σ' p)
    {C : Fin (L + 1) → Set (d → ℝ)} {A : ∀ ℓ, Finset (hid ℓ)}
    {θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut}
    (hθ : GoodForConesGated C A θ) (k : Fin L)
    (η : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    {w wd : ℝ → Matrix T (hid k) ℝ} {w₀ wd₀ : Matrix T (hid k) ℝ}
    (hw : Tendsto w atTop (𝓝 w₀)) (hwd : Tendsto wd atTop (𝓝 wd₀))
    (hH : ∀ τ, (w₀ * θ.write k) τ ∈ C k.succ)
    (hzero : ∀ᶠ t in atTop,
      writeLHS (Arch.gated σ id hid) θ k η (t ^ 2 • w t) (t ^ 2 • wd t) = 0) (R : ℝ) :
    ∀ᶠ t in atTop, ‖writeLHS (Arch.frozen A) (θ.toFrozen A) k (η.toFrozen A)
      (t ^ 2 • w t) (t ^ 2 • wd t)‖ ≤ Real.exp (-(R * t ^ p)) := by
  obtain ⟨ϱ, hϱ, κ, hκ, t₀, hb⟩ :=
    exists_far_frozen_bounds hg hθ k.succ (w₀ * θ.write k) hH η
  -- `U(t) = w(t) V − w₀ V → 0`, and the direction `ẇ(t) V + w(t) η_V` converges
  have hU : Tendsto (fun t => w t * θ.write k - w₀ * θ.write k) atTop (𝓝 0) := by
    have hc : Continuous fun M : Matrix T (hid k) ℝ => M * θ.write k - w₀ * θ.write k :=
      (continuous_id.matrix_mul continuous_const).sub continuous_const
    have h := (hc.tendsto w₀).comp hw
    rwa [sub_self] at h
  have hdir : Tendsto (fun t => wd t * θ.write k + w t * η.write k) atTop
      (𝓝 (wd₀ * θ.write k + w₀ * η.write k)) :=
    (((continuous_id.matrix_mul continuous_const).tendsto wd₀).comp hwd).add
      (((continuous_id.matrix_mul continuous_const).tendsto w₀).comp hw)
  have e1 := hU.norm.eventually_lt_const (show ‖(0 : Matrix T d ℝ)‖ < ϱ by rwa [norm_zero])
  have e2 := hdir.norm.eventually_lt_const (lt_add_one ‖wd₀ * θ.write k + w₀ * η.write k‖)
  have e3 := (tendsto_pow_atTop (two_ne_zero : (2 : ℕ) ≠ 0)).eventually_ge_atTop t₀
  filter_upwards [e1, e2, e3, hzero, eventually_exp_mul_le hκ hg.one_le
    (‖wd₀ * θ.write k + w₀ * η.write k‖ + 1) R] with t hUt hdt ht0 hz hF
  obtain ⟨-, h2, h3⟩ := hb (t ^ 2) ht0 _ hUt.le
  -- the point is `t² w V = t² (w₀ V + U)`, the direction `t² (ẇ V + w η_V)`
  have hpt : (t ^ 2 • w t) * θ.write k
      = t ^ 2 • (w₀ * θ.write k + (w t * θ.write k - w₀ * θ.write k)) := by
    rw [add_sub_cancel, Matrix.smul_mul]
  have hdt : (t ^ 2 • wd t) * θ.write k + (t ^ 2 • w t) * η.write k
      = t ^ 2 • (wd t * θ.write k + w t * η.write k) := by
    rw [Matrix.smul_mul, Matrix.smul_mul, smul_add]
  have hfro : writeLHS (Arch.frozen A) (θ.toFrozen A) k (η.toFrozen A) (t ^ 2 • w t)
      (t ^ 2 • wd t)
      = fderiv ℝ (fun h' : Matrix T d ℝ => suffix (Arch.frozen A) 0 (θ.toFrozen A) k.succ h')
          ((t ^ 2 • w t) * θ.write k)
          ((t ^ 2 • wd t) * θ.write k + (t ^ 2 • w t) * η.write k)
        + fderiv ℝ (fun θ' : Params (Arch.frozen (T := T) (d := d) A) dIn dOut =>
            suffix (Arch.frozen A) 0 θ' k.succ ((t ^ 2 • w t) * θ.write k))
          (θ.toFrozen A) (η.toFrozen A) := rfl
  have hgat : writeLHS (Arch.gated σ id hid) θ k η (t ^ 2 • w t) (t ^ 2 • wd t)
      = fderiv ℝ (fun h' : Matrix T d ℝ => suffix (Arch.gated σ id hid) 0 θ k.succ h')
          ((t ^ 2 • w t) * θ.write k)
          ((t ^ 2 • wd t) * θ.write k + (t ^ 2 • w t) * η.write k)
        + fderiv ℝ (fun θ' : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut =>
            suffix (Arch.gated σ id hid) 0 θ' k.succ ((t ^ 2 • w t) * θ.write k)) θ η := rfl
  rw [hgat, hpt, hdt] at hz
  rw [hfro, hpt, hdt]
  -- `𝓛° = 𝓛° − 𝓛`, and Lemma D.11
  refine (norm_add_le_of_add_eq_zero hz).trans ?_
  have hdn : ‖t ^ 2 • (wd t * θ.write k + w t * η.write k)‖
      ≤ t ^ 2 * (‖wd₀ * θ.write k + w₀ * η.write k‖ + 1) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    gcongr
  calc _ ≤ Real.exp (-(κ * (t ^ 2) ^ p)) * ‖t ^ 2 • (wd t * θ.write k + w t * η.write k)‖
        + Real.exp (-(κ * (t ^ 2) ^ p)) := add_le_add (h2 _) h3
    _ ≤ Real.exp (-(κ * (t ^ 2) ^ p)) * (t ^ 2 * (‖wd₀ * θ.write k + w₀ * η.write k‖ + 1))
        + Real.exp (-(κ * (t ^ 2) ^ p)) := by gcongr
    _ = Real.exp (-(κ * (t ^ 2) ^ p))
        * (t ^ 2 * (‖wd₀ * θ.write k + w₀ * η.write k‖ + 1) + 1) := by ring
    _ ≤ _ := hF

/-- Helper: **Lemma D.12 up to (38) on one generic ray, with the reads written out.** Here
`M = Ξ W_read` holds the gates `g = Ξ W_g` and the values `ι = Ξ W_v`, and `Q = Ξ (Z W_read + η_read)`
holds `ż^g` and `ż^v`; `hray` is (28) on the ray `n = t Ξ`. -/
private theorem frozen_flat_core (hg : GateFar σ σ' p) {C : Fin (L + 1) → Set (d → ℝ)}
    {A : ∀ ℓ, Finset (hid ℓ)} {θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut}
    (hθ : GoodForConesGated C A θ) (k : Fin L)
    (η : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (M Q : Matrix T (hid k ⊕ hid k) ℝ)
    (hray : ∀ t : ℝ, writeLHS (Arch.gated σ id hid) θ k η
      (Matrix.of fun a j => σ (t * M a (Sum.inl j)) * (t * M a (Sum.inr j)))
      (Matrix.of fun a j => σ' (t * M a (Sum.inl j)) * (t * Q a (Sum.inl j))
          * (t * M a (Sum.inr j)) + σ (t * M a (Sum.inl j)) * (t * Q a (Sum.inr j))) = 0)
    (hpos : ∀ a, ∀ j ∈ A k, 0 < M a (Sum.inl j))
    (hneg : ∀ a, ∀ j ∉ A k, M a (Sum.inl j) < 0)
    (hi : LinearIndependent ℚ (fun i : T × hid k => |M i.1 (Sum.inl i.2)| ^ p))
    (hii : ∀ a j, M a (Sum.inr j) ≠ 0)
    (hH : ∀ τ, ((Arch.frozen (T := T) (d := d) A).f k M * θ.write k) τ ∈ C k.succ)
    (hiii : Function.Injective
      (fderiv ℝ (fun h' : Matrix T d ℝ => suffix (Arch.frozen A) 0 (θ.toFrozen A) k.succ h')
        ((Arch.frozen (T := T) (d := d) A).f k M * θ.write k))) :
    (∀ a j, Q a (Sum.inl j) = 0) ∧
      ∀ w : Matrix T (hid k) ℝ,
        writeLHS (Arch.frozen A) (θ.toFrozen A) k (η.toFrozen A)
          (Matrix.of fun a j => w a j * M a (Sum.inr j))
          (Matrix.of fun a j => w a j * Q a (Sum.inr j)) = 0 := by
  classical
  -- the sizes `u = |g|` of the gates, the frozen gates `W°`, the indicator `1_A` of the active
  -- units and the signs `s`
  obtain ⟨u, hu⟩ : ∃ u : Matrix T (hid k) ℝ, ∀ a j, u a j = |M a (Sum.inl j)| :=
    ⟨Matrix.of fun a j => |M a (Sum.inl j)|, fun _ _ => rfl⟩
  have hupos : ∀ a j, 0 < u a j := by
    intro a j
    rw [hu]
    by_cases hj : j ∈ A k
    · exact abs_pos.2 (hpos a j hj).ne'
    · exact abs_pos.2 (hneg a j hj).ne
  obtain ⟨Wo, hWo⟩ : ∃ Wo : Matrix T (hid k) ℝ,
      ∀ a j, Wo a j = if j ∈ A k then M a (Sum.inl j) else 0 :=
    ⟨Matrix.of fun a j => if j ∈ A k then M a (Sum.inl j) else 0, fun _ _ => rfl⟩
  obtain ⟨IA, hIA⟩ : ∃ IA : Matrix T (hid k) ℝ, ∀ a j, IA a j = if j ∈ A k then 1 else 0 :=
    ⟨Matrix.of fun a j => if j ∈ A k then 1 else 0, fun _ _ => rfl⟩
  obtain ⟨sg, hsg⟩ : ∃ sg : hid k → ℝ, ∀ j, sg j = if j ∈ A k then 1 else -1 :=
    ⟨fun j => if j ∈ A k then 1 else -1, fun _ => rfl⟩
  have hsg0 : ∀ j, sg j ≠ 0 := by
    intro j
    rw [hsg]
    split_ifs <;> norm_num
  -- (24) on the ray: `σ(t g) = t W° − δ(t u)` and `σ'(t g) = 1_A − s δ'(t u)`
  have hσt : ∀ (t : ℝ) a j,
      σ (t * M a (Sum.inl j)) = t * Wo a j - (t * u a j - σ (t * u a j)) := by
    intro t a j
    rw [hWo, hu]
    by_cases hj : j ∈ A k
    · rw [abs_of_pos (hpos a j hj)]
      simp only [hj, ↓reduceIte]
      ring
    · rw [abs_of_neg (hneg a j hj)]
      simp only [hj, ↓reduceIte]
      have h := (hg.neg (t * -M a (Sum.inl j))).1
      rw [show -(t * -M a (Sum.inl j)) = t * M a (Sum.inl j) by ring] at h
      rw [h]
      ring
  have hσ't : ∀ (t : ℝ) a j,
      σ' (t * M a (Sum.inl j)) = IA a j - sg j * (1 - σ' (t * u a j)) := by
    intro t a j
    rw [hIA, hsg, hu]
    by_cases hj : j ∈ A k
    · rw [abs_of_pos (hpos a j hj)]
      simp only [hj, ↓reduceIte]
      ring
    · rw [abs_of_neg (hneg a j hj)]
      simp only [hj, ↓reduceIte]
      have h := (hg.neg (t * -M a (Sum.inl j))).2
      rw [show -(t * -M a (Sum.inl j)) = t * M a (Sum.inl j) by ring] at h
      rw [h]
      ring
  -- the small terms `ζ = δ(t u)/t` and `ν = t δ'(t u)/δ(t u)`, the rates `r = u^p/p`,
  -- and `x' = −s ⊙ ν ⊙ ζ`
  obtain ⟨ζ, hζ⟩ : ∃ ζ : ℝ → Matrix T (hid k) ℝ,
      ∀ t a j, ζ t a j = (t * u a j - σ (t * u a j)) / t :=
    ⟨fun t => Matrix.of fun a j => (t * u a j - σ (t * u a j)) / t, fun _ _ _ => rfl⟩
  obtain ⟨ν, hν⟩ : ∃ ν : ℝ → Matrix T (hid k) ℝ,
      ∀ t a j, ν t a j = t * (1 - σ' (t * u a j)) / (t * u a j - σ (t * u a j)) :=
    ⟨fun t => Matrix.of fun a j => t * (1 - σ' (t * u a j)) / (t * u a j - σ (t * u a j)),
      fun _ _ _ => rfl⟩
  obtain ⟨r, hr⟩ : ∃ r : Matrix T (hid k) ℝ, ∀ a j, r a j = u a j ^ p / p :=
    ⟨Matrix.of fun a j => u a j ^ p / p, fun _ _ => rfl⟩
  obtain ⟨x', hx'⟩ : ∃ x' : ℝ → Matrix T (hid k) ℝ,
      ∀ t a j, x' t a j = -sg j * (ν t a j * ζ t a j) :=
    ⟨fun t => Matrix.of fun a j => -sg j * (ν t a j * ζ t a j), fun _ _ _ => rfl⟩
  -- the outputs `v₁(y) = (W° + y) ⊙ ι` and their derivative
  -- `v̇₁(y, x) = (1_A + x) ⊙ ż^g ⊙ ι + (W° + y) ⊙ ż^v`, scaled by `t⁻²`
  obtain ⟨v₁, hv₁⟩ : ∃ f : Matrix T (hid k) ℝ → Matrix T (hid k) ℝ,
      ∀ y, f y = Matrix.of fun a j => (Wo a j + y a j) * M a (Sum.inr j) :=
    ⟨fun y => Matrix.of fun a j => (Wo a j + y a j) * M a (Sum.inr j), fun _ => rfl⟩
  obtain ⟨vd₁, hvd₁⟩ : ∃ f : Matrix T (hid k) ℝ → Matrix T (hid k) ℝ → Matrix T (hid k) ℝ,
      ∀ y x, f y x = Matrix.of fun a j => (IA a j + x a j) * Q a (Sum.inl j) * M a (Sum.inr j)
        + (Wo a j + y a j) * Q a (Sum.inr j) :=
    ⟨fun y x => Matrix.of fun a j => (IA a j + x a j) * Q a (Sum.inl j) * M a (Sum.inr j)
        + (Wo a j + y a j) * Q a (Sum.inr j), fun _ _ => rfl⟩
  -- one constant `B` for the bounds
  obtain ⟨B, hB6, hBu⟩ : ∃ B : ℝ, 6 ≤ B ∧ ∀ a j, 4 * u a j ≤ B := by
    have hs : ∀ a j, u a j ≤ ∑ a, ∑ j, u a j := fun a j =>
      (Finset.single_le_sum (fun j _ => (hupos a j).le) (Finset.mem_univ j)).trans
        (Finset.single_le_sum (f := fun a => ∑ j, u a j)
          (fun a _ => Finset.sum_nonneg fun j _ => (hupos a j).le) (Finset.mem_univ a))
    have h0 : 0 ≤ ∑ a, ∑ j, u a j :=
      Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun j _ => (hupos a j).le
    exact ⟨6 + 4 * ∑ a, ∑ j, u a j, by linarith, fun a j => by linarith [hs a j]⟩
  -- the ray is far out: `t ≥ 1` and `t u ≥ 2` for all large `t`
  have hgood : ∀ᶠ t : ℝ in atTop, 1 ≤ t ∧ ∀ a j, 2 ≤ t * u a j := by
    refine (eventually_ge_atTop 1).and (eventually_all.2 fun a => eventually_all.2 fun j => ?_)
    filter_upwards [eventually_ge_atTop (2 / u a j)] with t ht
    rwa [div_le_iff₀ (hupos a j)] at ht
  have hrpos : ∀ a j, 0 < r a j := by
    intro a j
    rw [hr]
    have : (0 : ℝ) < p := Nat.cast_pos.2 (by have := hg.one_le; omega)
    exact div_pos (pow_pos (hupos a j) p) this
  -- (i): the rates are independent over `ℚ`
  have hrQ : LinearIndependent ℚ (fun i : T × hid k => r i.1 i.2) := by
    rw [Fintype.linearIndependent_iff] at hi ⊢
    intro c hc i
    refine hi c ?_ i
    have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by have := hg.one_le; omega)
    have : ∑ i, c i • r i.1 i.2 = (p : ℝ)⁻¹ * ∑ i, c i • |M i.1 (Sum.inl i.2)| ^ p := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hr, hu, Rat.smul_def, Rat.smul_def]
      ring
    rw [this] at hc
    exact (mul_eq_zero.1 hc).resolve_left (inv_ne_zero hp0)
  -- the three bounds of the induction (from (25)), with `N = 2`
  have hζl : ∀ᶠ t : ℝ in atTop, ∀ a j, Real.exp (-(r a j * t ^ p)) ≤ B * t ^ 2 * ζ t a j := by
    filter_upwards [hgood] with t ht a j
    rw [hr, hζ]
    exact (ray_small_bounds hg (hupos a j) ht.1 (ht.2 a j) hB6 (hBu a j)).1
  have hζu : ∀ᶠ t : ℝ in atTop, ∀ a j,
      |ζ t a j| ≤ B * t ^ 2 * Real.exp (-(r a j * t ^ p)) := by
    filter_upwards [hgood] with t ht a j
    rw [hr, hζ]
    exact (ray_small_bounds hg (hupos a j) ht.1 (ht.2 a j) hB6 (hBu a j)).2.1
  have hνb : ∀ᶠ t : ℝ in atTop, ∀ a j, |ν t a j| ≤ B * t ^ 2 := by
    filter_upwards [hgood] with t ht a j
    rw [hν]
    exact (ray_small_bounds hg (hupos a j) ht.1 (ht.2 a j) hB6 (hBu a j)).2.2.1
  -- `ζ → 0` and `x' → 0`
  have hζ0 : Tendsto ζ atTop (𝓝 0) := by
    refine tendsto_pi_nhds.2 fun a => tendsto_pi_nhds.2 fun j => ?_
    refine tendsto_zero_of_abs_le_pow_mul_exp (B := u a j) (N := 0) (q := p) (hrpos a j)
      hg.one_le ?_
    filter_upwards [hgood] with t ht
    rw [hr, hζ]
    exact (ray_small_bounds hg (hupos a j) ht.1 (ht.2 a j) hB6 (hBu a j)).2.2.2.1
  have hx'0 : Tendsto x' atTop (𝓝 0) := by
    refine tendsto_pi_nhds.2 fun a => tendsto_pi_nhds.2 fun j => ?_
    have h : Tendsto (fun t => ν t a j * ζ t a j) atTop (𝓝 0) := by
      refine tendsto_zero_of_abs_le_pow_mul_exp (B := 4 * u a j ^ 2) (N := 2) (q := p)
        (hrpos a j) hg.one_le ?_
      filter_upwards [hgood] with t ht
      rw [hr, hν, hζ]
      exact (ray_small_bounds hg (hupos a j) ht.1 (ht.2 a j) hB6 (hBu a j)).2.2.2.2.1
    have h2 := h.const_mul (-sg j)
    rw [mul_zero] at h2
    exact h2.congr fun t => (hx' t a j).symm
  -- steps 1 and 3: on the ray, the outputs are `t² v₁(−ζ)` and their derivative `t² v̇₁(−ζ, x')`
  have hscale : ∀ᶠ t : ℝ in atTop,
      (Matrix.of fun a j => σ (t * M a (Sum.inl j)) * (t * M a (Sum.inr j))) = t ^ 2 • v₁ (-ζ t) ∧
      (Matrix.of fun a j => σ' (t * M a (Sum.inl j)) * (t * Q a (Sum.inl j))
          * (t * M a (Sum.inr j)) + σ (t * M a (Sum.inl j)) * (t * Q a (Sum.inr j)))
        = t ^ 2 • vd₁ (-ζ t) (x' t) := by
    filter_upwards [hgood] with t ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hδ : ∀ a j, t * u a j - σ (t * u a j) = t * ζ t a j := fun a j => by
      rw [hζ]
      field_simp
    have hδ' : ∀ a j, 1 - σ' (t * u a j) = ν t a j * ζ t a j := fun a j => by
      rw [hν, hζ]
      exact (ray_small_bounds hg (hupos a j) ht.1 (ht.2 a j) hB6 (hBu a j)).2.2.2.2.2.symm
    refine ⟨?_, ?_⟩
    · ext a j
      rw [hv₁]
      simp only [Matrix.smul_apply, Matrix.of_apply, Matrix.neg_apply, smul_eq_mul]
      rw [hσt, hδ]
      ring
    · ext a j
      rw [hvd₁]
      simp only [Matrix.smul_apply, Matrix.of_apply, Matrix.neg_apply, smul_eq_mul]
      rw [hσt, hσ't, hδ, hδ', hx']
      ring
  -- the point after the block: `v₁(0) V = g°(Ξ)`
  have hv₁0 : v₁ 0 = (Arch.frozen (T := T) (d := d) A).f k M := by
    rw [hv₁]
    ext a j
    show (Wo a j + 0) * M a (Sum.inr j)
      = Set.indicator (↑(A k) : Set (hid k)) (fun i => M a (Sum.inl i) * M a (Sum.inr i)) j
    rw [hWo, add_zero]
    by_cases hj : j ∈ A k
    · rw [Set.indicator_of_mem (Finset.mem_coe.2 hj)]
      simp only [hj, ↓reduceIte]
    · rw [Set.indicator_of_notMem (by simpa using hj)]
      simp only [hj, ↓reduceIte, zero_mul]
  -- step 3: `𝓛°(v₁(y), v̇₁(y, x)) = Ψ₀(y) + ∑ x_{aj} ż^g_{aj} ι_{aj} 𝐃𝓑°(v₁(y) V)(E_{aj} V)`
  obtain ⟨Ψ₀, hΨ₀⟩ : ∃ Ψ : Matrix T (hid k) ℝ → Matrix T dOut ℝ, ∀ y,
      Ψ y = writeLHS (Arch.frozen A) (θ.toFrozen A) k (η.toFrozen A) (v₁ y) (vd₁ y 0) :=
    ⟨fun y => writeLHS (Arch.frozen A) (θ.toFrozen A) k (η.toFrozen A) (v₁ y) (vd₁ y 0),
      fun _ => rfl⟩
  obtain ⟨Jm, hJm⟩ : ∃ J : Matrix T (hid k) ℝ → T → hid k → Matrix T dOut ℝ, ∀ y a j,
      J y a j = fderiv ℝ
        (fun h' : Matrix T d ℝ => suffix (Arch.frozen A) 0 (θ.toFrozen A) k.succ h')
        (v₁ y * θ.write k) (Matrix.single a j (1 : ℝ) * θ.write k) :=
    ⟨fun y a j => fderiv ℝ
        (fun h' : Matrix T d ℝ => suffix (Arch.frozen A) 0 (θ.toFrozen A) k.succ h')
        (v₁ y * θ.write k) (Matrix.single a j (1 : ℝ) * θ.write k), fun _ _ _ => rfl⟩
  have hdecomp : ∀ y x : Matrix T (hid k) ℝ,
      writeLHS (Arch.frozen A) (θ.toFrozen A) k (η.toFrozen A) (v₁ y) (vd₁ y x)
        = Ψ₀ y + ∑ a, ∑ j, (x a j * Q a (Sum.inl j) * M a (Sum.inr j)) • Jm y a j := by
    intro y x
    have hsplit : vd₁ y x = vd₁ y 0
        + Matrix.of fun a j => x a j * Q a (Sum.inl j) * M a (Sum.inr j) := by
      rw [hvd₁, hvd₁]
      ext a j
      simp only [Matrix.of_apply, Matrix.add_apply, Matrix.zero_apply]
      ring
    rw [hsplit, writeLHS_add_vdot, ← hΨ₀]
    congr 1
    rw [Matrix.matrix_eq_sum_single
      (Matrix.of fun a j => x a j * Q a (Sum.inl j) * M a (Sum.inr j))]
    simp only [Matrix.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hJm, ← map_smul, ← Matrix.smul_mul, Matrix.smul_single, smul_eq_mul, mul_one,
      Matrix.of_apply]
    rfl
  -- `G₀(1/t, ζ) + ∑ ν ζ G(1/t, ζ) = 𝓛°(v₁(−ζ), v̇₁(−ζ, x'))`, with
  -- `G₀(s, y) = Ψ₀(−y)` and `G_{aj}(s, y) = −s_j ż^g_{aj} ι_{aj} 𝐃𝓑°(v₁(−y) V)(E_{aj} V)`
  have hsum : ∀ t, Ψ₀ (-ζ t) + ∑ a, ∑ j, (ν t a j * ζ t a j)
      • ((-sg j * Q a (Sum.inl j) * M a (Sum.inr j)) • Jm (-ζ t) a j)
      = writeLHS (Arch.frozen A) (θ.toFrozen A) k (η.toFrozen A) (v₁ (-ζ t))
          (vd₁ (-ζ t) (x' t)) := by
    intro t
    rw [hdecomp]
    congr 1
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => ?_
    rw [smul_smul, hx']
    congr 1
    ring
  -- step 4, fact (b): the left side is smaller than `e^{−R t^p}` for every `R`
  have hv₁c : Continuous v₁ := by
    rw [show v₁ = fun y => Matrix.of fun a j => (Wo a j + y a j) * M a (Sum.inr j) from funext hv₁]
    exact continuous_matrix fun a j => by
      simp only [Matrix.of_apply]
      exact (continuous_const.add (continuous_id.matrix_elem a j)).mul continuous_const
  have hvd₁c : Continuous fun z : Matrix T (hid k) ℝ × Matrix T (hid k) ℝ => vd₁ z.1 z.2 := by
    rw [show (fun z : Matrix T (hid k) ℝ × Matrix T (hid k) ℝ => vd₁ z.1 z.2) = fun z =>
      Matrix.of fun a j => (IA a j + z.2 a j) * Q a (Sum.inl j) * M a (Sum.inr j)
        + (Wo a j + z.1 a j) * Q a (Sum.inr j) from funext fun z => hvd₁ z.1 z.2]
    exact continuous_matrix fun a j => by
      simp only [Matrix.of_apply]
      exact (((continuous_const.add (continuous_snd.matrix_elem a j)).mul
        continuous_const).mul continuous_const).add
        ((continuous_const.add (continuous_fst.matrix_elem a j)).mul continuous_const)
  have hnζ : Tendsto (fun t => -ζ t) atTop (𝓝 0) := by
    have h := hζ0.neg
    rwa [neg_zero] at h
  have hfb : ∀ R : ℝ, ∀ᶠ t : ℝ in atTop,
      ‖Ψ₀ (-ζ t) + ∑ a, ∑ j, (ν t a j * ζ t a j)
        • ((-sg j * Q a (Sum.inl j) * M a (Sum.inr j)) • Jm (-ζ t) a j)‖
        ≤ Real.exp (-(R * t ^ p)) := by
    intro R
    have hw : Tendsto (fun t => v₁ (-ζ t)) atTop (𝓝 (v₁ 0)) := (hv₁c.tendsto 0).comp hnζ
    have hwd : Tendsto (fun t => vd₁ (-ζ t) (x' t)) atTop (𝓝 (vd₁ 0 0)) :=
      (hvd₁c.tendsto (0, 0)).comp (hnζ.prodMk_nhds hx'0)
    have hH' : ∀ τ, (v₁ 0 * θ.write k) τ ∈ C k.succ := by
      rw [hv₁0]
      exact hH
    have hzero : ∀ᶠ t : ℝ in atTop, writeLHS (Arch.gated σ id hid) θ k η
        (t ^ 2 • v₁ (-ζ t)) (t ^ 2 • vd₁ (-ζ t) (x' t)) = 0 := by
      filter_upwards [hscale] with t ht
      rw [← ht.1, ← ht.2]
      exact hray t
    filter_upwards [eventually_norm_writeLHS_frozen_le hg hθ k η hw hwd hH' hzero R,
      eventually_ge_atTop 1] with t hb ht
    rw [writeLHS_frozen_smul A (θ.toFrozen A) (η.toFrozen A) k (by positivity)] at hb
    rw [hsum]
    refine le_trans ?_ hb
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact le_mul_of_one_le_left (norm_nonneg _) (one_le_pow₀ (one_le_pow₀ ht))
  -- fact (a): `G₀` and the `G_{aj}` are real-analytic
  have hv₁an : AnalyticOnNhd ℝ v₁ Set.univ := by
    rw [show v₁ = fun y => Matrix.of fun a j => (Wo a j + y a j) * M a (Sum.inr j) from funext hv₁]
    show AnalyticOnNhd ℝ (fun y : Matrix T (hid k) ℝ => fun a j => (Wo a j + y a j) * M a (Sum.inr j))
      Set.univ
    exact AnalyticOnNhd.pi fun a => AnalyticOnNhd.pi fun j =>
      (analyticOnNhd_const.add (analyticOnNhd_matrix_entry a j)).mul analyticOnNhd_const
  have hvd₁an : AnalyticOnNhd ℝ (fun y => vd₁ y 0) Set.univ := by
    rw [show (fun y => vd₁ y 0) = fun y => Matrix.of fun a j => (IA a j + (0 : Matrix T (hid k) ℝ) a j)
      * Q a (Sum.inl j) * M a (Sum.inr j) + (Wo a j + y a j) * Q a (Sum.inr j)
      from funext fun y => hvd₁ y 0]
    show AnalyticOnNhd ℝ (fun y : Matrix T (hid k) ℝ => fun a j => (IA a j + (0 : Matrix T (hid k) ℝ) a j)
      * Q a (Sum.inl j) * M a (Sum.inr j) + (Wo a j + y a j) * Q a (Sum.inr j)) Set.univ
    exact AnalyticOnNhd.pi fun a => AnalyticOnNhd.pi fun j => analyticOnNhd_const.add
      ((analyticOnNhd_const.add (analyticOnNhd_matrix_entry a j)).mul analyticOnNhd_const)
  have hneg2 : AnalyticOnNhd ℝ (fun z : ℝ × Matrix T (hid k) ℝ => -z.2) Set.univ :=
    analyticOnNhd_snd.neg
  have hG₀an : AnalyticAt ℝ (fun z : ℝ × Matrix T (hid k) ℝ => Ψ₀ (-z.2)) 0 := by
    have h := analyticOnNhd_writeLHS_frozen A (θ.toFrozen A) (η.toFrozen A) k
      (hv₁an.comp hneg2 (Set.mapsTo_univ _ _)) (hvd₁an.comp hneg2 (Set.mapsTo_univ _ _))
    rw [show (fun z : ℝ × Matrix T (hid k) ℝ => Ψ₀ (-z.2)) = fun z =>
      writeLHS (Arch.frozen A) (θ.toFrozen A) k (η.toFrozen A) (v₁ (-z.2)) (vd₁ (-z.2) 0)
      from funext fun z => hΨ₀ _]
    exact h 0 (Set.mem_univ _)
  have hB := analyticOnNhd_suffix (Arch.frozen (T := T) (d := d) A) (dIn := dIn) (dOut := dOut)
    (θ.toFrozen A) rfl (analyticOnNhd_f_frozen A) k.succ
  have hGan : ∀ a j, AnalyticAt ℝ (fun z : ℝ × Matrix T (hid k) ℝ =>
      (-sg j * Q a (Sum.inl j) * M a (Sum.inr j)) • Jm (-z.2) a j) 0 := by
    intro a j
    have hJ := hB.fderiv.comp (analyticOnNhd_matrix_mul (hv₁an.comp hneg2 (Set.mapsTo_univ _ _))
      (analyticOnNhd_const (v := θ.write k))) (Set.mapsTo_univ _ _)
    have h := ((analyticOnNhd_const (v := -sg j * Q a (Sum.inl j) * M a (Sum.inr j))).smul
      (analyticOnNhd_clm_applyR hJ
      (analyticOnNhd_const (v := Matrix.single a j (1 : ℝ) * θ.write k)))) 0 (Set.mem_univ _)
    rw [show (fun z : ℝ × Matrix T (hid k) ℝ =>
        (-sg j * Q a (Sum.inl j) * M a (Sum.inr j)) • Jm (-z.2) a j) = fun z =>
        (-sg j * Q a (Sum.inl j) * M a (Sum.inr j)) • fderiv ℝ
          (suffix (Arch.frozen A) 0 (θ.toFrozen A) k.succ) (v₁ (-z.2) * θ.write k)
          (Matrix.single a j (1 : ℝ) * θ.write k) from funext fun z => by rw [hJm]]
    exact h
  -- step 5: `G_{aj}(·, 0) = 0` forces `ż^g_{aj} = 0` (`𝐃𝓑°` is injective at `g°(Ξ)`)
  have hzg : ∀ a j, (-sg j * Q a (Sum.inl j) * M a (Sum.inr j)) • Jm 0 a j = 0 →
      Q a (Sum.inl j) = 0 := by
    intro a j h
    rw [hJm, hv₁0, ← map_smul] at h
    have h1 := hiii (h.trans (map_zero _).symm)
    obtain ⟨i, hi⟩ : ∃ i, θ.write k j i ≠ 0 := by
      by_contra hne
      push Not at hne
      exact hθ.write_ne_zero k j (funext hne)
    have h2 := congrFun (congrFun h1 a) i
    simp only [Matrix.smul_apply, Matrix.single_mul_apply_same, one_mul, smul_eq_mul,
      Matrix.zero_apply] at h2
    rcases mul_eq_zero.1 ((mul_eq_zero.1 h2).resolve_right hi) with h4 | h4
    · rcases mul_eq_zero.1 h4 with h5 | h5
      · exact absurd (neg_eq_zero.1 h5) (hsg0 j)
      · exact h5
    · exact absurd h4 (hii a j)
  -- the step "one small factor": `|ν| → ∞`, so the coefficient of `ν` must vanish
  have hstep : ∀ a j, FasterThanPowers (fun t : ℝ =>
      fderiv ℝ (fun y : Matrix T (hid k) ℝ => Ψ₀ (-y)) 0 (Matrix.single a j 1)
        + ν t a j • ((-sg j * Q a (Sum.inl j) * M a (Sum.inr j)) • Jm (-0) a j)) →
      ∀ᶠ z in 𝓝 (0 : ℝ × Matrix T (hid k) ℝ),
        (-sg j * Q a (Sum.inl j) * M a (Sum.inr j)) • Jm (-z.2) a j = 0 := by
    intro a j hft
    have hb0 : (-sg j * Q a (Sum.inl j) * M a (Sum.inr j)) • Jm (-0) a j = 0 := by
      by_contra hb
      set c := fderiv ℝ (fun y : Matrix T (hid k) ℝ => Ψ₀ (-y)) 0 (Matrix.single a j 1)
      set b := (-sg j * Q a (Sum.inl j) * M a (Sum.inr j)) • Jm (-0) a j
      have hbpos : 0 < ‖b‖ := norm_pos_iff.2 hb
      have h1 := ((fasterThanPowers_iff _).1 hft 0).eventually_lt_const one_pos
      have hνinf : Tendsto (fun t => |ν t a j|) atTop atTop :=
        (tendsto_abs_nu hg (hupos a j)).congr fun t => by rw [hν]
      have h2 := hνinf.eventually_ge_atTop ((‖c‖ + 1) / ‖b‖)
      obtain ⟨t, ht1, ht2⟩ := (h1.and h2).exists
      simp only [pow_zero, one_mul] at ht1
      have h3 : ‖c‖ + 1 ≤ ‖ν t a j • b‖ := by
        rw [norm_smul, Real.norm_eq_abs, ← div_le_iff₀ hbpos]
        exact ht2
      have h4 : ‖ν t a j • b‖ ≤ ‖c + ν t a j • b‖ + ‖c‖ := by
        calc ‖ν t a j • b‖ = ‖(c + ν t a j • b) - c‖ := by rw [add_sub_cancel_left]
          _ ≤ _ := norm_sub_le _ _
      linarith
    have hQ0 := hzg a j (by rwa [neg_zero] at hb0)
    exact Eventually.of_forall fun z => by rw [hQ0, mul_zero, zero_mul, zero_smul]
  -- step 6: the induction on the exponents
  obtain ⟨hG₀0, hG0⟩ := ray_induction_matrix p hg.one_le r hrpos hrQ ζ ν B 2 hζl hζu hνb
    (fun z : ℝ × Matrix T (hid k) ℝ => Ψ₀ (-z.2))
    (fun a j z => (-sg j * Q a (Sum.inl j) * M a (Sum.inr j)) • Jm (-z.2) a j)
    hG₀an hGan hfb hstep
  -- `ż^g = 0`
  have hQ0 : ∀ a j, Q a (Sum.inl j) = 0 := fun a j => hzg a j (by
    have h := (hG0 a j).self_of_nhds
    simpa only [Prod.snd_zero, neg_zero] using h)
  refine ⟨hQ0, fun w => ?_⟩
  -- `Φ(w) = 𝓛°(w ⊙ ι, w ⊙ ż^v)` is real-analytic and vanishes near `W°`
  have hΦan : AnalyticOnNhd ℝ (fun w : Matrix T (hid k) ℝ =>
      writeLHS (Arch.frozen A) (θ.toFrozen A) k (η.toFrozen A)
        (Matrix.of fun a j => w a j * M a (Sum.inr j))
        (Matrix.of fun a j => w a j * Q a (Sum.inr j))) Set.univ := by
    refine analyticOnNhd_writeLHS_frozen A _ _ k ?_ ?_
    · show AnalyticOnNhd ℝ (fun w : Matrix T (hid k) ℝ => fun a j => w a j * M a (Sum.inr j))
        Set.univ
      exact AnalyticOnNhd.pi fun a => AnalyticOnNhd.pi fun j =>
        (analyticOnNhd_matrix_entry a j).mul analyticOnNhd_const
    · show AnalyticOnNhd ℝ (fun w : Matrix T (hid k) ℝ => fun a j => w a j * Q a (Sum.inr j))
        Set.univ
      exact AnalyticOnNhd.pi fun a => AnalyticOnNhd.pi fun j =>
        (analyticOnNhd_matrix_entry a j).mul analyticOnNhd_const
  have hΦeq : ∀ w : Matrix T (hid k) ℝ,
      writeLHS (Arch.frozen A) (θ.toFrozen A) k (η.toFrozen A)
        (Matrix.of fun a j => w a j * M a (Sum.inr j))
        (Matrix.of fun a j => w a j * Q a (Sum.inr j)) = Ψ₀ (-(Wo - w)) := by
    intro w
    rw [hΨ₀, hv₁, hvd₁]
    congr 1
    · ext a j
      simp only [Matrix.of_apply, Matrix.neg_apply, Matrix.sub_apply]
      ring
    · ext a j
      simp only [Matrix.of_apply, Matrix.neg_apply, Matrix.sub_apply, Matrix.zero_apply, hQ0]
      ring
  have hc : Tendsto (fun w : Matrix T (hid k) ℝ => ((0 : ℝ), Wo - w)) (𝓝 Wo)
      (𝓝 (0 : ℝ × Matrix T (hid k) ℝ)) := by
    have h := (tendsto_const_nhds (x := (0 : ℝ)) (f := 𝓝 Wo)).prodMk_nhds
      ((tendsto_const_nhds (x := Wo)).sub tendsto_id)
    rw [sub_self] at h
    exact h
  have hzero : (fun w : Matrix T (hid k) ℝ =>
      writeLHS (Arch.frozen A) (θ.toFrozen A) k (η.toFrozen A)
        (Matrix.of fun a j => w a j * M a (Sum.inr j))
        (Matrix.of fun a j => w a j * Q a (Sum.inr j))) =ᶠ[𝓝 Wo] 0 := by
    filter_upwards [hc.eventually hG₀0] with w hw
    rw [hΦeq]
    exact hw
  exact hΦan.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
    (Set.mem_univ Wo) hzero (Set.mem_univ w)

omit [Fintype T] [Fintype d] [DecidableEq d] in
/-- Helper: the set where a nonzero additive and homogeneous function does not vanish is dense
(as in `Depth/StepTanh.lean`). -/
private theorem dense_setOf_ne_zero_of_linearR (f : Matrix T d ℝ → ℝ)
    (hadd : ∀ x y, f (x + y) = f x + f y) (hsmul : ∀ (c : ℝ) x, f (c • x) = c * f x)
    {x₀ : Matrix T d ℝ} (hx₀ : f x₀ ≠ 0) : Dense {x | f x ≠ 0} := by
  intro x
  by_cases hx : f x ≠ 0
  · exact subset_closure hx
  rw [not_not] at hx
  have ht : Tendsto (fun ε : ℝ => x + ε • x₀) (𝓝[≠] 0) (𝓝 x) := by
    have hc : Continuous (fun ε : ℝ => x + ε • x₀) :=
      continuous_const.add (continuous_id.smul continuous_const)
    have h0 := hc.tendsto 0
    rw [zero_smul, add_zero] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  refine mem_closure_of_tendsto ht (eventually_nhdsWithin_of_forall fun ε hε => ?_)
  show f (x + ε • x₀) ≠ 0
  rw [hadd, hsmul, hx, zero_add]
  exact mul_ne_zero hε hx₀

end Helpers

/-- **Lemma D.12 up to (38), on one generic ray, case (n).** Let `θ` be good for the cones, let `Z`
and `η` satisfy (16) for `k`, and let `Ξ` have its rows in `C_k` and satisfy (i), (ii), (iii).
Then `ż^g(Ξ) = 0`, and the second part of (38) holds at `n = Ξ` for every `w̃`. -/
theorem frozen_flat_at_generic_ray (hg : GateFar σ σ' p) {C : Fin (L + 1) → Set (d → ℝ)}
    {A : ∀ ℓ, Finset (hid ℓ)} {θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut}
    (hθ : GoodForConesGated C A θ) (k : Fin L) (Z : Matrix d d ℝ)
    (η : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (hflat : SuffixFlat (Arch.gated σ id hid) θ k.castSucc Z η)
    (Ξ : Matrix T d ℝ) (hΞ : ∀ t, Ξ t ∈ C k.castSucc)
    (hi : LinearIndependent ℚ (fun i : T × hid k => |(Ξ * θ.read k) i.1 (Sum.inl i.2)| ^ p))
    (hii : ∀ t j, (Ξ * θ.read k) t (Sum.inr j) ≠ 0)
    (hiii : Function.Injective
      (fderiv ℝ (fun h' : Matrix T d ℝ => suffix (Arch.frozen A) 0 (θ.toFrozen A) k.succ h')
        ((Arch.frozen (T := T) (d := d) A).f k (Ξ * θ.read k) * θ.write k))) :
    (∀ t j, (Ξ * (Z * θ.read k + η.read k)) t (Sum.inl j) = 0) ∧
      ∀ w : Matrix T (hid k) ℝ,
        writeLHS (Arch.frozen A) (θ.toFrozen A) k (η.toFrozen A)
          (Matrix.of fun t j => w t j * (Ξ * θ.read k) t (Sum.inr j))
          (Matrix.of fun t j => w t j * (Ξ * (Z * θ.read k + η.read k)) t (Sum.inr j)) = 0 := by
  -- (28) on the ray `n = t Ξ`: everything is linear in `n`
  have hray : ∀ t : ℝ, writeLHS (Arch.gated σ id hid) θ k η
      (Matrix.of fun a j => σ (t * (Ξ * θ.read k) a (Sum.inl j))
        * (t * (Ξ * θ.read k) a (Sum.inr j)))
      (Matrix.of fun a j => σ' (t * (Ξ * θ.read k) a (Sum.inl j))
          * (t * (Ξ * (Z * θ.read k + η.read k)) a (Sum.inl j))
          * (t * (Ξ * θ.read k) a (Sum.inr j))
        + σ (t * (Ξ * θ.read k) a (Sum.inl j))
          * (t * (Ξ * (Z * θ.read k + η.read k)) a (Sum.inr j))) = 0 := by
    intro t
    have e := (suffixFlat_castSucc_iff_gated hg.hasDerivAt θ k Z η).1 hflat (t • Ξ)
    rw [blockLHSGated_eq_writeLHS] at e
    simp only [Matrix.of_apply, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul] at e
    exact e
  -- the gates have one sign on `C_k` (K1), and `g°(Ξ)` has its rows in `C_{k+1}` (K2)
  exact frozen_flat_core hg hθ k η (Ξ * θ.read k) (Ξ * (Z * θ.read k + η.read k)) hray
    (fun a j hj => hθ.gate_pos k (Ξ a) (hΞ a) j hj)
    (fun a j hj => hθ.gate_neg k (Ξ a) (hΞ a) j hj) hi hii
    (fun τ => by
      rw [frozen_block_apply A θ k Ξ τ]
      exact hθ.frozen_mem k (Ξ τ) (hΞ τ)) hiii

/-- **Lemma D.12 up to (38), case (n).** Let `θ` be good for the cones, and let the `Ξ` with (i)
be dense. If `Z` and `η` satisfy (16) for `k`, then `Z W_g + η_g = 0`, and the second part of (38)
holds for every `n` with its rows in `C_k` and every `w̃`. -/
theorem frozen_flat_of_suffixFlat [Nonempty T] (hg : GateFar σ σ' p)
    {C : Fin (L + 1) → Set (d → ℝ)} {A : ∀ ℓ, Finset (hid ℓ)}
    {θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut}
    (hθ : GoodForConesGated C A θ) (k : Fin L)
    (hdense : Dense {Ξ : Matrix T d ℝ |
      LinearIndependent ℚ (fun i : T × hid k => |(Ξ * θ.read k) i.1 (Sum.inl i.2)| ^ p)})
    (Z : Matrix d d ℝ) (η : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (hflat : SuffixFlat (Arch.gated σ id hid) θ k.castSucc Z η) :
    (∀ i j, (Z * θ.read k + η.read k) i (Sum.inl j) = 0) ∧
      ∀ n : Matrix T d ℝ, (∀ t, n t ∈ C k.castSucc) → ∀ w : Matrix T (hid k) ℝ,
        writeLHS (Arch.frozen A) (θ.toFrozen A) k (η.toFrozen A)
          (Matrix.of fun t j => w t j * (n * θ.read k) t (Sum.inr j))
          (Matrix.of fun t j => w t j * (n * (Z * θ.read k + η.read k)) t (Sum.inr j)) = 0 := by
  classical
  -- the open set `O` of the `n` with all rows in `C_k`; it is not empty
  obtain ⟨O, hO⟩ : ∃ O : Set (Matrix T d ℝ), O = {n | ∀ t, n t ∈ C k.castSucc} := ⟨_, rfl⟩
  have hOo : IsOpen O := by
    rw [hO, show {n : Matrix T d ℝ | ∀ t, n t ∈ C k.castSucc}
      = ⋂ t, (fun n : Matrix T d ℝ => n t) ⁻¹' C k.castSucc by ext n; simp]
    exact isOpen_iInter_of_finite fun t => (hθ.cone _).isOpen.preimage (continuous_apply t)
  obtain ⟨n₀, hn₀⟩ : O.Nonempty := by
    obtain ⟨c, hc⟩ := (hθ.cone k.castSucc).nonempty
    exact ⟨Matrix.of fun _ => c, by rw [hO]; exact fun _ => hc⟩
  -- the entries of `Ξ N` are linear, hence analytic and continuous, in `Ξ`
  have hent : ∀ (N : Matrix d (hid k ⊕ hid k) ℝ) t c,
      AnalyticOnNhd ℝ (fun Ξ : Matrix T d ℝ => (Ξ * N) t c) Set.univ := fun N t c =>
    (analyticOnNhd_matrix_entry t c).comp (analyticOnNhd_matrix_mul analyticOnNhd_id
      analyticOnNhd_const) (Set.mapsTo_univ _ _)
  have hentc : ∀ (N : Matrix d (hid k ⊕ hid k) ℝ) t c,
      Continuous fun Ξ : Matrix T d ℝ => (Ξ * N) t c := fun N t c =>
    continuousOn_univ.mp (hent N t c).continuousOn
  -- (ii): the `Ξ` with no vanishing value `ι_{tj}(Ξ)` form an open dense set `S₂` (K3)
  obtain ⟨S₂, hS₂⟩ : ∃ S₂ : Set (Matrix T d ℝ),
      S₂ = ⋂ i : T × hid k, {Ξ | (Ξ * θ.read k) i.1 (Sum.inr i.2) ≠ 0} := ⟨_, rfl⟩
  have hS₂o : IsOpen S₂ := by
    rw [hS₂]
    exact isOpen_iInter_of_finite fun i => isOpen_ne_fun (hentc _ _ _) continuous_const
  have hS₂d : Dense S₂ := by
    rw [hS₂]
    have : BaireSpace (Matrix T d ℝ) := inferInstanceAs (BaireSpace (T → d → ℝ))
    refine dense_iInter_of_isOpen (fun i => isOpen_ne_fun (hentc _ _ _) continuous_const)
      fun i => ?_
    obtain ⟨l, hl⟩ : ∃ l, θ.read k l (Sum.inr i.2) ≠ 0 := by
      by_contra hne
      push Not at hne
      exact hθ.value_ne_zero k i.2 (funext hne)
    refine dense_setOf_ne_zero_of_linearR (fun Ξ => (Ξ * θ.read k) i.1 (Sum.inr i.2))
      (fun x y => by rw [Matrix.add_mul, Matrix.add_apply])
      (fun c x => by rw [Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul])
      (x₀ := Matrix.single i.1 l (1 : ℝ)) ?_
    show (Matrix.single i.1 l (1 : ℝ) * θ.read k) i.1 (Sum.inr i.2) ≠ 0
    rw [Matrix.single_mul_apply_same, one_mul]
    exact hl
  -- (iii): Lemma D.2 for the frozen network before block `k`
  obtain ⟨U, hUo, hUd, hU⟩ := exists_open_dense_injective_fderiv_suffix
    (Arch.frozen (T := T) (d := d) A) (dIn := dIn) (dOut := dOut) (θ.toFrozen A) rfl
    (analyticOnNhd_f_frozen A) (regular_frozen_of_goodForConesGated hθ) k.castSucc
  -- the generic `Ξ`: (i), (ii) and `Ξ ∈ U`; they are dense, so `O` lies in the closure of the
  -- generic `Ξ ∈ O`
  obtain ⟨D, hD⟩ : ∃ D : Set (Matrix T d ℝ), D = {Ξ : Matrix T d ℝ |
      LinearIndependent ℚ (fun i : T × hid k => |(Ξ * θ.read k) i.1 (Sum.inl i.2)| ^ p)}
      ∩ (S₂ ∩ U) := ⟨_, rfl⟩
  have hDd : Dense D := by
    rw [hD]
    exact hdense.inter_of_isOpen_right (hS₂d.inter_of_isOpen_left hUd hS₂o) (hS₂o.inter hUo)
  have hsub : O ⊆ closure (O ∩ D) := hDd.open_subset_closure_inter hOo
  have hgen : ∀ Ξ ∈ O ∩ D, (∀ t j, (Ξ * (Z * θ.read k + η.read k)) t (Sum.inl j) = 0) ∧
      ∀ w : Matrix T (hid k) ℝ,
        writeLHS (Arch.frozen A) (θ.toFrozen A) k (η.toFrozen A)
          (Matrix.of fun t j => w t j * (Ξ * θ.read k) t (Sum.inr j))
          (Matrix.of fun t j => w t j * (Ξ * (Z * θ.read k + η.read k)) t (Sum.inr j)) = 0 := by
    rintro Ξ ⟨hΞO, hΞD⟩
    rw [hO] at hΞO
    rw [hD] at hΞD
    obtain ⟨hΞi, hΞ₂, hΞU⟩ := hΞD
    rw [hS₂, Set.mem_iInter] at hΞ₂
    refine frozen_flat_at_generic_ray hg hθ k Z η hflat Ξ hΞO hΞi (fun t j => hΞ₂ (t, j)) ?_
    -- `𝐃𝓑°_{>k}(Ξ) = 𝐃𝓑°_{>k+1}(g°(Ξ)) ∘ 𝐃g°(Ξ)` is injective; so `𝐃g°(Ξ)` is injective, hence
    -- onto, and `𝐃𝓑°_{>k+1}(g°(Ξ))` is injective
    have hinj : Function.Injective (fderiv ℝ
        (suffix (Arch.frozen (T := T) (d := d) A) 0 (θ.toFrozen A) k.castSucc) Ξ) := hU Ξ hΞU
    rw [fderiv_suffix_castSucc (Arch.frozen (T := T) (d := d) A) (θ.toFrozen A) rfl
      (analyticOnNhd_f_frozen A) k Ξ, ContinuousLinearMap.coe_comp] at hinj
    have hsurj := LinearMap.injective_iff_surjective.1 hinj.of_comp
    exact hinj.of_comp_right hsurj
  obtain ⟨t₀⟩ := ‹Nonempty T›
  refine ⟨fun i j => ?_, fun n hn w => ?_⟩
  · -- `Ξ ↦ ż^g_{t₀ j}(Ξ)` vanishes at the generic `Ξ ∈ O`, hence on `O`, hence everywhere
    have hO0 : Set.EqOn (fun Ξ : Matrix T d ℝ => (Ξ * (Z * θ.read k + η.read k)) t₀ (Sum.inl j))
        0 O :=
      Set.EqOn.of_subset_closure (fun Ξ hΞ => (hgen Ξ hΞ).1 t₀ j)
        ((hent _ t₀ (Sum.inl j)).continuousOn.mono (Set.subset_univ O)) continuousOn_const
        Set.inter_subset_left hsub
    have hall := (hent _ t₀ (Sum.inl j)).eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (Set.mem_univ n₀) (Filter.eventually_of_mem (hOo.mem_nhds hn₀) hO0)
      (Set.mem_univ (Matrix.single t₀ i (1 : ℝ)))
    simpa only [Matrix.single_mul_apply_same, one_mul, Pi.zero_apply] using hall
  · -- the second part of (38) holds at the generic `Ξ ∈ O`, and is continuous in `n`
    have hΦ : AnalyticOnNhd ℝ (fun n : Matrix T d ℝ =>
        writeLHS (Arch.frozen A) (θ.toFrozen A) k (η.toFrozen A)
          (Matrix.of fun t j => w t j * (n * θ.read k) t (Sum.inr j))
          (Matrix.of fun t j => w t j * (n * (Z * θ.read k + η.read k)) t (Sum.inr j)))
        Set.univ := by
      refine analyticOnNhd_writeLHS_frozen A _ _ k ?_ ?_
      · show AnalyticOnNhd ℝ (fun n : Matrix T d ℝ => fun t j =>
          w t j * (n * θ.read k) t (Sum.inr j)) Set.univ
        exact AnalyticOnNhd.pi fun t => AnalyticOnNhd.pi fun j =>
          analyticOnNhd_const.mul (hent _ t _)
      · show AnalyticOnNhd ℝ (fun n : Matrix T d ℝ => fun t j =>
          w t j * (n * (Z * θ.read k + η.read k)) t (Sum.inr j)) Set.univ
        exact AnalyticOnNhd.pi fun t => AnalyticOnNhd.pi fun j =>
          analyticOnNhd_const.mul (hent _ t _)
    have hnO : n ∈ O := by rw [hO]; exact hn
    exact Set.EqOn.of_subset_closure (fun Ξ hΞ => (hgen Ξ hΞ).2 w)
      (hΦ.continuousOn.mono (Set.subset_univ O)) continuousOn_const Set.inter_subset_left hsub hnO

/-- **Lemma D.12 up to (38), SwiGLU blocks, case (n):** with the gate columns of block `k`
linearly independent over `ℚ`. -/
theorem frozen_flat_of_suffixFlat_swiglu [Nonempty T] {C : Fin (L + 1) → Set (d → ℝ)}
    {A : ∀ ℓ, Finset (hid ℓ)} {θ : Params (Arch.gated (T := T) (d := d) silu id hid) dIn dOut}
    (hθ : GoodForConesGated C A θ) (k : Fin L)
    (hQ : LinearIndependent ℚ (fun j : hid k => (θ.read k)ᵀ (Sum.inl j)))
    (Z : Matrix d d ℝ) (η : Params (Arch.gated (T := T) (d := d) silu id hid) dIn dOut)
    (hflat : SuffixFlat (Arch.gated silu id hid) θ k.castSucc Z η) :
    (∀ i j, (Z * θ.read k + η.read k) i (Sum.inl j) = 0) ∧
      ∀ n : Matrix T d ℝ, (∀ t, n t ∈ C k.castSucc) → ∀ w : Matrix T (hid k) ℝ,
        writeLHS (Arch.frozen A) (θ.toFrozen A) k (η.toFrozen A)
          (Matrix.of fun t j => w t j * (n * θ.read k) t (Sum.inr j))
          (Matrix.of fun t j => w t j * (n * (Z * θ.read k + η.read k)) t (Sum.inr j)) = 0 := by
  -- SiLU with `p = 1`, and (i) is dense by the independence of the gate columns
  refine frozen_flat_of_suffixFlat gateFar_silu hθ k ?_ Z η hflat
  have h := dense_setOf_linearIndependent_abs_dotProduct (T := T)
    (fun j : hid k => (θ.read k)ᵀ (Sum.inl j)) hQ
  have e : ∀ (Ξ : Matrix T d ℝ) (i : T × hid k),
      (Ξ * θ.read k) i.1 (Sum.inl i.2) = Ξ i.1 ⬝ᵥ (θ.read k)ᵀ (Sum.inl i.2) := fun _ _ => rfl
  simp only [pow_one, e]
  exact h

/-- **Lemma D.12 up to (38), GeGLU blocks, case (n):** with the matrices `c_j c_j^⊤` of the gate
columns of block `k` linearly independent over `ℚ`. -/
theorem frozen_flat_of_suffixFlat_geglu [Nonempty T] {C : Fin (L + 1) → Set (d → ℝ)}
    {A : ∀ ℓ, Finset (hid ℓ)} {θ : Params (Arch.gated (T := T) (d := d) gelu id hid) dIn dOut}
    (hθ : GoodForConesGated C A θ) (k : Fin L)
    (hQ : LinearIndependent ℚ (fun j : hid k =>
      Matrix.vecMulVec ((θ.read k)ᵀ (Sum.inl j)) ((θ.read k)ᵀ (Sum.inl j))))
    (Z : Matrix d d ℝ) (η : Params (Arch.gated (T := T) (d := d) gelu id hid) dIn dOut)
    (hflat : SuffixFlat (Arch.gated gelu id hid) θ k.castSucc Z η) :
    (∀ i j, (Z * θ.read k + η.read k) i (Sum.inl j) = 0) ∧
      ∀ n : Matrix T d ℝ, (∀ t, n t ∈ C k.castSucc) → ∀ w : Matrix T (hid k) ℝ,
        writeLHS (Arch.frozen A) (θ.toFrozen A) k (η.toFrozen A)
          (Matrix.of fun t j => w t j * (n * θ.read k) t (Sum.inr j))
          (Matrix.of fun t j => w t j * (n * (Z * θ.read k + η.read k)) t (Sum.inr j)) = 0 := by
  -- GELU with `p = 2`, and (i) is dense by the independence of the matrices `c_j c_j^⊤`
  refine frozen_flat_of_suffixFlat gateFar_gelu hθ k ?_ Z η hflat
  have h := dense_setOf_linearIndependent_sq_dotProduct (T := T)
    (fun j : hid k => (θ.read k)ᵀ (Sum.inl j)) hQ
  have e : ∀ (Ξ : Matrix T d ℝ) (i : T × hid k),
      (Ξ * θ.read k) i.1 (Sum.inl i.2) = Ξ i.1 ⬝ᵥ (θ.read k)ᵀ (Sum.inl i.2) := fun _ _ => rfl
  simp only [sq_abs, e]
  exact h

end Skips
