import SkipsLean.Depth.ScaledSuffix
import SkipsLean.Depth.RayInduction
import SkipsLean.Depth.RayDense
import SkipsLean.Depth.Frozen
import SkipsLean.Activations.OneSmallFactor

/-!
# Lemma D.12 on a ray, for GELU blocks under pre-RMSNorm: from (28) to (38)

Paper (dimension): Appendix D.5, proof of Lemma D.12, from its beginning to equation (38), for GELU
blocks in the case (+). "A GELU block has the form of a GeGLU block in which the value `n e_j` of
every hidden unit is replaced by the number `1`": `ι(n) = (1, …, 1)`, `m = 1`, there is no `ż^v`,
`ŵ = w̃`, and `𝓛` is the map (21) of the block identity for MLP blocks (`blockLHS` in
`Depth/StepTanh.lean`, which is `writeLHS` at `v = w̃`, `vdot = w̃' ⊙ ż`). The proof is the one
for gated blocks (see `Depth/RayGatedPlus.lean` and `Depth/RayGatedN.lean` for the quotations), with
Lemma D.9 in the step "one small factor". Equation (38) reads: for all `n ∈ C_k` and all rows `w̃`,
`ż(n) = 0` and `𝐃𝓑(w̃ V)(w̃ η_V) + 𝐃_θ 𝓑(w̃ V) η' = 0`.

Stated here, for an MLP block whose activation `σ` has `GateFar σ σ' p`, with the step "one small
factor" as the hypothesis `hone`, and for hidden states with the rows `T`: (38) at one generic `Ξ`
((i) the numbers `|ξ_t c_j|^p` are independent over `ℚ`; (iii) the derivative of the network after
the block is injective at `g°(Ξ)`; there is no (ii)); then (38) for all `n` with rows in `C_k`,
given that the `Ξ` with (i) are dense; then for GELU blocks from the independence over `ℚ` of the
matrices `c_j c_j^⊤` of block `k`.
-/

namespace Skips

open Matrix Filter
open scoped Matrix.Norms.Elementwise Topology

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]
variable {σ σ' : ℝ → ℝ} {p : ℕ} {ε : ℝ}

/-- Helper: the derivative of `z ↦ G (x, y, z)` is that of `G` along `(0, 0, w)`. -/
private theorem fderiv_partial_thd {X Y Z F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {G : X × Y × Z → F} {x : X} {y : Y} {z : Z}
    (hG : DifferentiableAt ℝ G (x, y, z)) (w : Z) :
    fderiv ℝ (fun z' => G (x, y, z')) z w = fderiv ℝ G (x, y, z) (0, 0, w) := by
  have h : HasFDerivAt (fun z' : Z => ((x, y, z') : X × Y × Z))
      ((0 : Z →L[ℝ] X).prod ((0 : Z →L[ℝ] Y).prod (ContinuousLinearMap.id ℝ Z))) z :=
    (hasFDerivAt_const x z).prodMk ((hasFDerivAt_const y z).prodMk (hasFDerivAt_id z))
  have hc := hG.hasFDerivAt.comp z h
  exact DFunLike.congr_fun hc.fderiv w

/-- Helper: the derivative of `x ↦ G (x, y, z)` is that of `G` along `(v, 0, 0)`. -/
private theorem fderiv_partial_fst3 {X Y Z F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {G : X × Y × Z → F} {x : X} {y : Y} {z : Z}
    (hG : DifferentiableAt ℝ G (x, y, z)) (v : X) :
    fderiv ℝ (fun x' => G (x', y, z)) x v = fderiv ℝ G (x, y, z) (v, 0, 0) := by
  have h : HasFDerivAt (fun x' : X => ((x', y, z) : X × Y × Z))
      ((ContinuousLinearMap.id ℝ X).prod ((0 : X →L[ℝ] Y).prod (0 : X →L[ℝ] Z))) x :=
    (hasFDerivAt_id x).prodMk ((hasFDerivAt_const y x).prodMk (hasFDerivAt_const z x))
  have hc := hG.hasFDerivAt.comp x h
  exact DFunLike.congr_fun hc.fderiv v

/-- Helper: the derivative of `y ↦ G (x, y)` is that of `G` along `(0, w)`. -/
private theorem fderiv_partial_snd2 {X Y F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {G : X × Y → F} {x : X} {y : Y} (hG : DifferentiableAt ℝ G (x, y)) (w : Y) :
    fderiv ℝ (fun y' => G (x, y')) y w = fderiv ℝ G (x, y) (0, w) := by
  have hc := hG.hasFDerivAt.comp y (hasFDerivAt_prodMk_right (𝕜 := ℝ) x y)
  exact DFunLike.congr_fun hc.fderiv w

/-- Helper: an analytic family of continuous linear maps, applied to an analytic family of vectors,
is analytic. -/
private theorem analyticAt_clm_apply' {X E F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {J : X → E →L[ℝ] F} {v : X → E} {x : X} (hJ : AnalyticAt ℝ J x) (hv : AnalyticAt ℝ v x) :
    AnalyticAt ℝ (fun x => J x (v x)) x :=
  ((ContinuousLinearMap.id ℝ (E →L[ℝ] F)).analyticAt_bilinear (J x, v x)).comp₂ hJ hv

/-- Helper: for `G` analytic at `(x₀, y₀)`, the partial derivative `x ↦ ∂_y G(x, y₀) v` is
analytic at `x₀`. -/
private theorem analyticAt_fderiv_partial_snd {X Y F : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] {G : X × Y → F} {x₀ : X} {y₀ : Y}
    (hG : AnalyticAt ℝ G (x₀, y₀)) (v : Y) :
    AnalyticAt ℝ (fun x => fderiv ℝ (fun y => G (x, y)) y₀ v) x₀ := by
  have hp : AnalyticAt ℝ (fun x : X => ((x, y₀) : X × Y)) x₀ := analyticAt_id.prod analyticAt_const
  have hJ := hG.fderiv.comp_of_eq hp rfl
  have h3 := analyticAt_clm_apply' hJ (analyticAt_const (v := ((0 : X), v)))
  refine h3.congr ?_
  filter_upwards [hp.continuousAt.eventually hG.eventually_analyticAt] with x hx
  exact (fderiv_partial_snd2 hx.differentiableAt v).symm

/-- Helper: `x ↦ 𝐃_h Φ(s(x), g(x)) (w(x))`, with `Φ(s, h)` the network after a hidden state on a
ray (`scaledSuffix`, `m = 1`), is real-analytic at `x₀` if `s`, `g`, `w` are and no row of `g(x₀)`
vanishes. -/
private theorem analyticAt_fderiv_scaledSuffix (Ar : Arch T d L) (hε : 0 < ε)
    (hχ : Ar.χ = rmsNorm ε) (hf : ∀ ℓ, AnalyticOnNhd ℝ (Ar.f ℓ) Set.univ)
    (θ : Params Ar dIn dOut) (k' : Fin (L + 1)) {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] {s : X → ℝ} {g w : X → Matrix T d ℝ} {x₀ : X} (hs : AnalyticAt ℝ s x₀)
    (hg : AnalyticAt ℝ g x₀) (hw : AnalyticAt ℝ w x₀) (hH : ∀ t, g x₀ t ≠ 0) :
    AnalyticAt ℝ (fun x => fderiv ℝ (fun h' : Matrix T d ℝ => scaledSuffix Ar ε 1 θ k' (s x, h'))
      (g x) (w x)) x₀ := by
  have hF := analyticAt_scaledSuffix Ar hε hχ hf 1 θ k' (s x₀) (g x₀) hH
  have hp : AnalyticAt ℝ (fun x => ((θ, s x, g x) : Params Ar dIn dOut × ℝ × Matrix T d ℝ)) x₀ :=
    analyticAt_const.prod (hs.prod hg)
  have hJ := hF.fderiv.comp_of_eq hp rfl
  have hv : AnalyticAt ℝ (fun x => ((0, 0, w x) : Params Ar dIn dOut × ℝ × Matrix T d ℝ)) x₀ :=
    analyticAt_const.prod (analyticAt_const.prod hw)
  have h3 := analyticAt_clm_apply' hJ hv
  refine h3.congr ?_
  filter_upwards [hp.continuousAt.eventually hF.eventually_analyticAt] with x hx
  exact (fderiv_partial_thd hx.differentiableAt (w x)).symm

/-- Helper: `x ↦ 𝐃_θ Φ(s(x), g(x)) η` is real-analytic at `x₀` if `s`, `g` are and no row of
`g(x₀)` vanishes. -/
private theorem analyticAt_fderiv_params_scaledSuffix (Ar : Arch T d L) (hε : 0 < ε)
    (hχ : Ar.χ = rmsNorm ε) (hf : ∀ ℓ, AnalyticOnNhd ℝ (Ar.f ℓ) Set.univ)
    (θ η : Params Ar dIn dOut) (k' : Fin (L + 1)) {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] {s : X → ℝ} {g : X → Matrix T d ℝ} {x₀ : X} (hs : AnalyticAt ℝ s x₀)
    (hg : AnalyticAt ℝ g x₀) (hH : ∀ t, g x₀ t ≠ 0) :
    AnalyticAt ℝ (fun x => fderiv ℝ (fun θ' : Params Ar dIn dOut =>
      scaledSuffix Ar ε 1 θ' k' (s x, g x)) θ η) x₀ := by
  have hF := analyticAt_scaledSuffix Ar hε hχ hf 1 θ k' (s x₀) (g x₀) hH
  have hp : AnalyticAt ℝ (fun x => ((θ, s x, g x) : Params Ar dIn dOut × ℝ × Matrix T d ℝ)) x₀ :=
    analyticAt_const.prod (hs.prod hg)
  have hJ := hF.fderiv.comp_of_eq hp rfl
  have h3 := analyticAt_clm_apply' hJ
    (analyticAt_const (v := ((η, 0, 0) : Params Ar dIn dOut × ℝ × Matrix T d ℝ)))
  refine h3.congr ?_
  filter_upwards [hp.continuousAt.eventually hF.eventually_analyticAt] with x hx
  exact (fderiv_partial_fst3 hx.differentiableAt η).symm

/-- Helper (step 3, the scaling): for `t > 0`,
`𝓛(t X, t³ M) = t² (𝐃_hΦ(1/t, X V)(M V + t^{-2} X η_V) + t^{-2} 𝐃_θΦ(1/t, X V) η)`, with
`Φ(s, h) = scaledSuffix` (`m = 1`) after block `k`. -/
private theorem writeLHS_smul_eq (Ar : Arch T d L) (hε : 0 < ε) (hχ : Ar.χ = rmsNorm ε)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (Ar.f ℓ) Set.univ) (θ η : Params Ar dIn dOut) (k : Fin L)
    {t : ℝ} (ht : 0 < t) (X M : Matrix T (Ar.w k) ℝ) :
    writeLHS Ar θ k η (t • X) (t ^ 3 • M) = t ^ 2 • (
      fderiv ℝ (fun h' : Matrix T d ℝ => scaledSuffix Ar ε 1 θ k.succ (1 / t, h')) (X * θ.write k)
        (M * θ.write k + (1 / t) ^ 2 • (X * η.write k))
      + (1 / t) ^ 2 • fderiv ℝ (fun θ' : Params Ar dIn dOut =>
          scaledSuffix Ar ε 1 θ' k.succ (1 / t, X * θ.write k)) θ η) := by
  have e1 : (t • X) * θ.write k = t ^ 1 • (X * θ.write k) := by rw [pow_one, Matrix.smul_mul]
  have e2 : (t ^ 3 • M) * θ.write k + (t • X) * η.write k
      = t ^ 3 • (M * θ.write k + (1 / t) ^ 2 • (X * η.write k)) := by
    rw [Matrix.smul_mul, Matrix.smul_mul, smul_add, smul_smul]
    congr 2
    field_simp
  unfold writeLHS
  rw [e1, e2, fderiv_suffix_pow_smul Ar hε hχ hf θ k.succ ht 1,
    fderiv_params_suffix_pow_smul Ar hχ θ η k.succ ht 1, map_smul]
  have h1 : (1 / t) ^ 1 * t ^ 3 = t ^ 2 := by field_simp
  have h2 : t ^ 2 * (1 / t) ^ 2 = 1 := by field_simp
  simp only [smul_add, smul_smul]
  rw [h1, h2, one_smul]

/-- `G₀(s, y)` of step 3 (with `y ↦ −y`): the scaled left side at `x' = 0`,
`𝐃_hΦ(s, ĥ)((M₀ + s² M₂) V + s² (W° − y) η_V) + s² 𝐃_θΦ(s, ĥ) η` with `ĥ = (W° − y) V`. -/
private noncomputable def rayG0 (Ar : Arch T d L) (ε : ℝ) (θ η : Params Ar dIn dOut) (k : Fin L)
    (Wo M₀ M₂ : Matrix T (Ar.w k) ℝ) (z : ℝ × Matrix T (Ar.w k) ℝ) : Matrix T dOut ℝ :=
  fderiv ℝ (fun h' : Matrix T d ℝ => scaledSuffix Ar ε 1 θ k.succ (z.1, h'))
      ((Wo - z.2) * θ.write k)
      ((M₀ + z.1 ^ 2 • M₂) * θ.write k + z.1 ^ 2 • ((Wo - z.2) * η.write k))
    + z.1 ^ 2 • fderiv ℝ (fun θ' : Params Ar dIn dOut =>
        scaledSuffix Ar ε 1 θ' k.succ (z.1, (Wo - z.2) * θ.write k)) θ η

/-- `G_{τj}(s, y)` of step 3: `(c₀ + s² c₂)_{τj} 𝐃_hΦ(s, (W° − y) V)(E_{τj} V)`. -/
private noncomputable def rayG (Ar : Arch T d L) (ε : ℝ) (θ : Params Ar dIn dOut) (k : Fin L)
    [DecidableEq T] [DecidableEq (Ar.w k)] (Wo c₀ c₂ : Matrix T (Ar.w k) ℝ) (τ : T) (j : Ar.w k)
    (z : ℝ × Matrix T (Ar.w k) ℝ) : Matrix T dOut ℝ :=
  (c₀ τ j + z.1 ^ 2 * c₂ τ j) • fderiv ℝ (fun h' : Matrix T d ℝ =>
    scaledSuffix Ar ε 1 θ k.succ (z.1, h')) ((Wo - z.2) * θ.write k) (Matrix.single τ j (1 : ℝ) * θ.write k)

/-- `G₀` is even in `s`. -/
private theorem rayG0_neg (Ar : Arch T d L) (θ η : Params Ar dIn dOut) (k : Fin L)
    (Wo M₀ M₂ : Matrix T (Ar.w k) ℝ) (s : ℝ) (y : Matrix T (Ar.w k) ℝ) :
    rayG0 Ar ε θ η k Wo M₀ M₂ (-s, y) = rayG0 Ar ε θ η k Wo M₀ M₂ (s, y) := by
  have h1 : (fun h' : Matrix T d ℝ => scaledSuffix Ar ε 1 θ k.succ (-s, h'))
      = fun h' => scaledSuffix Ar ε 1 θ k.succ (s, h') :=
    funext fun h' => scaledSuffix_neg Ar 1 θ k.succ s h'
  have h2 : (fun θ' : Params Ar dIn dOut => scaledSuffix Ar ε 1 θ' k.succ (-s, (Wo - y) * θ.write k))
      = fun θ' => scaledSuffix Ar ε 1 θ' k.succ (s, (Wo - y) * θ.write k) :=
    funext fun θ' => scaledSuffix_neg Ar 1 θ' k.succ s _
  simp only [rayG0, neg_sq, h1, h2]

/-- `G_{τj}` is even in `s`. -/
private theorem rayG_neg (Ar : Arch T d L) (θ : Params Ar dIn dOut) (k : Fin L)
    [DecidableEq T] [DecidableEq (Ar.w k)] (Wo c₀ c₂ : Matrix T (Ar.w k) ℝ) (τ : T) (j : Ar.w k)
    (s : ℝ) (y : Matrix T (Ar.w k) ℝ) :
    rayG Ar ε θ k Wo c₀ c₂ τ j (-s, y) = rayG Ar ε θ k Wo c₀ c₂ τ j (s, y) := by
  have h1 : (fun h' : Matrix T d ℝ => scaledSuffix Ar ε 1 θ k.succ (-s, h'))
      = fun h' => scaledSuffix Ar ε 1 θ k.succ (s, h') :=
    funext fun h' => scaledSuffix_neg Ar 1 θ k.succ s h'
  simp only [rayG, neg_sq, h1]

/-- `G₀` is real-analytic at `(0, 0)` if no row of `W° V` vanishes. -/
private theorem analyticAt_rayG0 (Ar : Arch T d L) (hε : 0 < ε) (hχ : Ar.χ = rmsNorm ε)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (Ar.f ℓ) Set.univ) (θ η : Params Ar dIn dOut) (k : Fin L)
    (Wo M₀ M₂ : Matrix T (Ar.w k) ℝ) (hH : ∀ t, (Wo * θ.write k) t ≠ 0) :
    AnalyticAt ℝ (rayG0 Ar ε θ η k Wo M₀ M₂) 0 := by
  have hg : AnalyticOnNhd ℝ (fun z : ℝ × Matrix T (Ar.w k) ℝ => (Wo - z.2) * θ.write k)
      Set.univ :=
    analyticOnNhd_matrix_mul (analyticOnNhd_const.sub analyticOnNhd_snd) analyticOnNhd_const
  have hw : AnalyticOnNhd ℝ (fun z : ℝ × Matrix T (Ar.w k) ℝ =>
      (M₀ + z.1 ^ 2 • M₂) * θ.write k + z.1 ^ 2 • ((Wo - z.2) * η.write k)) Set.univ :=
    (analyticOnNhd_matrix_mul (analyticOnNhd_const.add
      ((analyticOnNhd_fst.pow 2).smul analyticOnNhd_const)) analyticOnNhd_const).add
      ((analyticOnNhd_fst.pow 2).smul
        (analyticOnNhd_matrix_mul (analyticOnNhd_const.sub analyticOnNhd_snd) analyticOnNhd_const))
  have hH' : ∀ t, ((Wo - (0 : ℝ × Matrix T (Ar.w k) ℝ).2) * θ.write k) t ≠ 0 := by
    simpa only [Prod.snd_zero, sub_zero] using hH
  have h1 := analyticAt_fderiv_scaledSuffix Ar hε hχ hf θ k.succ (x₀ := 0) analyticAt_fst
    (hg 0 (Set.mem_univ _)) (hw 0 (Set.mem_univ _)) hH'
  have h2 := analyticAt_fderiv_params_scaledSuffix Ar hε hχ hf θ η k.succ (x₀ := 0) analyticAt_fst
    (hg 0 (Set.mem_univ _)) hH'
  exact h1.add ((analyticAt_fst.pow 2).fun_smul h2)

/-- `G_{τj}` is real-analytic at `(0, 0)` if no row of `W° V` vanishes. -/
private theorem analyticAt_rayG (Ar : Arch T d L) (hε : 0 < ε) (hχ : Ar.χ = rmsNorm ε)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (Ar.f ℓ) Set.univ) (θ : Params Ar dIn dOut) (k : Fin L)
    [DecidableEq T] [DecidableEq (Ar.w k)] (Wo c₀ c₂ : Matrix T (Ar.w k) ℝ) (τ : T) (j : Ar.w k)
    (hH : ∀ t, (Wo * θ.write k) t ≠ 0) :
    AnalyticAt ℝ (rayG Ar ε θ k Wo c₀ c₂ τ j) 0 := by
  have hg : AnalyticOnNhd ℝ (fun z : ℝ × Matrix T (Ar.w k) ℝ => (Wo - z.2) * θ.write k)
      Set.univ :=
    analyticOnNhd_matrix_mul (analyticOnNhd_const.sub analyticOnNhd_snd) analyticOnNhd_const
  have hH' : ∀ t, ((Wo - (0 : ℝ × Matrix T (Ar.w k) ℝ).2) * θ.write k) t ≠ 0 := by
    simpa only [Prod.snd_zero, sub_zero] using hH
  have h1 := analyticAt_fderiv_scaledSuffix Ar hε hχ hf θ k.succ (x₀ := 0) analyticAt_fst
    (hg 0 (Set.mem_univ _)) (analyticAt_const (v := Matrix.single τ j (1 : ℝ) * θ.write k)) hH'
  exact (analyticAt_const.add ((analyticAt_fst.pow 2).mul analyticAt_const)).fun_smul h1

/-- Helper (the identity theorem on `ℝ`): if `(a + s² b) β(s) = 0` near `0` and `β` is analytic on
`ℝ` with `β(1) ≠ 0`, then `a = 0` and `b = 0`. -/
private theorem eq_zero_of_eventually_smul_eq_zero {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {β : ℝ → F} (hβ : AnalyticOnNhd ℝ β Set.univ) (h1 : β 1 ≠ 0) {a b : ℝ}
    (h : ∀ᶠ s in 𝓝 (0 : ℝ), (a + s ^ 2 * b) • β s = 0) : a = 0 ∧ b = 0 := by
  -- `β` does not vanish near `0`, except possibly at `0`
  have hne : ∀ᶠ s in 𝓝[≠] (0 : ℝ), β s ≠ 0 :=
    (hβ 0 (Set.mem_univ _)).eventually_eq_zero_or_eventually_ne_zero.resolve_left fun h0 =>
      h1 (hβ.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (Set.mem_univ 0)
        h0 (Set.mem_univ 1))
  -- so `a + s² b = 0` there
  have hq : ∀ᶠ s in 𝓝[≠] (0 : ℝ), a + s ^ 2 * b = 0 := by
    filter_upwards [hne, nhdsWithin_le_nhds h] with s hs1 hs2
    exact (smul_eq_zero.1 hs2).resolve_right hs1
  -- at the limit `s → 0`: `a = 0`
  have hlim : Tendsto (fun s : ℝ => a + s ^ 2 * b) (𝓝[≠] (0 : ℝ)) (𝓝 a) := by
    have hc : Continuous fun s : ℝ => a + s ^ 2 * b := by fun_prop
    have h0 := hc.tendsto 0
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul, add_zero] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  have ha : a = 0 := tendsto_nhds_unique hlim (tendsto_const_nhds.congr' (hq.mono fun s hs => hs.symm))
  -- and at some `s ≠ 0`: `s² b = 0`
  obtain ⟨s, hs, hs0⟩ := (hq.and eventually_mem_nhdsWithin).exists
  rw [ha, zero_add] at hs
  exact ⟨ha, (mul_eq_zero.1 hs).resolve_left (pow_ne_zero 2 hs0)⟩

omit [Fintype d] [DecidableEq d] [Fintype dOut] in
/-- Helper: a continuous linear map at `M V` is the sum of its values at the rows `E_{τj} V`,
with the weights `M_{τj}`. -/
private theorem clm_mul_eq_sum {q : Type*} [Fintype q] [DecidableEq q] [DecidableEq T]
    (Λ : Matrix T d ℝ →L[ℝ] Matrix T dOut ℝ) (M : Matrix T q ℝ) (V : Matrix q d ℝ) :
    Λ (M * V) = ∑ τ, ∑ j, M τ j • Λ (Matrix.single τ j (1 : ℝ) * V) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single M]
  rw [Matrix.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Matrix.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← map_smul, ← Matrix.smul_mul, Matrix.smul_single, smul_eq_mul, mul_one]

omit [Fintype d] [DecidableEq d] [Fintype dOut] in
/-- Helper: the derivative of a map of hidden states at `h`, along `M V`, is the sum of its values
along the rows `E_{τj} V`, with the weights `M_{τj}`. -/
private theorem fderiv_mul_eq_sum {q : Type*} [Fintype q] [DecidableEq q] [DecidableEq T]
    (Fn : Matrix T d ℝ → Matrix T dOut ℝ) (h : Matrix T d ℝ) (M : Matrix T q ℝ)
    (V : Matrix q d ℝ) :
    fderiv ℝ Fn h (M * V) = ∑ τ, ∑ j, M τ j • fderiv ℝ Fn h (Matrix.single τ j (1 : ℝ) * V) :=
  clm_mul_eq_sum (fderiv ℝ Fn h) M V

/-- Step 3 on the ray, with `G₀`:
`𝓛(t (W° − y), t³ ((M₀ + t^{-2} M₂) + X')) = t² (G₀(1/t, y) + 𝐃_hΦ(1/t, (W° − y) V)(X' V))`. -/
private theorem writeLHS_ray_eq (Ar : Arch T d L) (hε : 0 < ε) (hχ : Ar.χ = rmsNorm ε)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (Ar.f ℓ) Set.univ) (θ η : Params Ar dIn dOut) (k : Fin L)
    {t : ℝ} (ht : 0 < t) (Wo M₀ M₂ Y X' : Matrix T (Ar.w k) ℝ) :
    writeLHS Ar θ k η (t • (Wo - Y)) (t ^ 3 • ((M₀ + (1 / t) ^ 2 • M₂) + X'))
      = t ^ 2 • (rayG0 Ar ε θ η k Wo M₀ M₂ (1 / t, Y)
        + fderiv ℝ (fun h' : Matrix T d ℝ => scaledSuffix Ar ε 1 θ k.succ (1 / t, h'))
          ((Wo - Y) * θ.write k) (X' * θ.write k)) := by
  rw [writeLHS_smul_eq Ar hε hχ hf θ η k ht]
  congr 1
  simp only [rayG0]
  rw [Matrix.add_mul (M₀ + _) X', add_right_comm _ (X' * θ.write k), map_add]
  abel

/-- Helper (step 2, the small terms): for `t ≥ 1`, `t u ≥ 2` and a constant `A₀ ≥ 6, 4u`, with
`δ(y) = y − σ(y)` and `r = u^p/p`: `e^{−r t^p} ≤ A₀ t² ζ`, `|ζ| ≤ A₀ t² e^{−r t^p}` and
`|ν| ≤ A₀ t²`, for `ζ = δ(t u)/t` and `ν = t δ'(t u)/δ(t u)`; and `δ(t u) > 0`. -/
private theorem gap_bounds (hg : GateFar σ σ' p) {u t A₀ : ℝ} (hu : 0 < u) (ht1 : 1 ≤ t)
    (ht2 : 2 ≤ t * u) (hA6 : 6 ≤ A₀) (hAu : 4 * u ≤ A₀) :
    Real.exp (-(u ^ p / p * t ^ p)) ≤ A₀ * t ^ 2 * ((t * u - σ (t * u)) / t) ∧
      |(t * u - σ (t * u)) / t| ≤ A₀ * t ^ 2 * Real.exp (-(u ^ p / p * t ^ p)) ∧
      |t * (1 - σ' (t * u)) / (t * u - σ (t * u))| ≤ A₀ * t ^ 2 ∧
      0 < t * u - σ (t * u) := by
  obtain ⟨hlo, hup, hd'⟩ := hg.gap (t * u) ht2
  have he : (t * u) ^ p / (p : ℝ) = u ^ p / p * t ^ p := by rw [mul_pow]; ring
  rw [he] at hlo hup
  obtain ⟨E, hE⟩ : ∃ E, E = Real.exp (-(u ^ p / p * t ^ p)) := ⟨_, rfl⟩
  rw [← hE] at hlo hup ⊢
  have hE0 : 0 < E := by rw [hE]; exact Real.exp_pos _
  have ht0 : 0 < t := by linarith
  obtain ⟨δ, hδ⟩ : ∃ δ, δ = t * u - σ (t * u) := ⟨_, rfl⟩
  rw [← hδ] at hlo hup hd' ⊢
  have hδ0 : 0 < δ := by linarith
  have hAt : 6 ≤ A₀ * t := by nlinarith
  have hu' : u ≤ A₀ := by linarith
  refine ⟨?_, ?_, ?_, hδ0⟩
  · -- `e^{−r t^p} ≤ 6 δ ≤ A₀ t δ = A₀ t² (δ/t)`
    have e : A₀ * t ^ 2 * (δ / t) = A₀ * t * δ := by field_simp
    rw [e]
    calc E ≤ 6 * δ := by linarith
      _ ≤ A₀ * t * δ := mul_le_mul_of_nonneg_right hAt hδ0.le
  · -- `δ/t ≤ u e^{−r t^p} ≤ A₀ t² e^{−r t^p}`
    rw [abs_of_pos (div_pos hδ0 ht0), div_le_iff₀ ht0]
    have ht3 : t ≤ t ^ 3 := by
      have h2 : 1 ≤ t ^ 2 := one_le_pow₀ ht1
      nlinarith
    have h1 : t * u ≤ t ^ 3 * A₀ := mul_le_mul ht3 hu' hu.le (by positivity)
    calc δ ≤ t * u * E := hup
      _ ≤ t ^ 3 * A₀ * E := mul_le_mul_of_nonneg_right h1 hE0.le
      _ = A₀ * t ^ 2 * E * t := by ring
  · -- `t |δ'|/δ ≤ 4 t² u ≤ A₀ t²`
    rw [abs_div, abs_mul, abs_of_pos ht0, abs_of_pos hδ0, div_le_iff₀ hδ0]
    calc t * |1 - σ' (t * u)| ≤ t * (4 * (t * u) * δ) := mul_le_mul_of_nonneg_left hd' ht0.le
      _ = (4 * u) * (t ^ 2 * δ) := by ring
      _ ≤ A₀ * (t ^ 2 * δ) := mul_le_mul_of_nonneg_right hAu (by positivity)
      _ = A₀ * t ^ 2 * δ := by ring

omit [Fintype T] [DecidableEq d] in
/-- Helper: equation (20) on the ray `n = t Ξ`: `ż(t Ξ) = t P₁ + t³ P₃` with `P₁ = Ξ (Z W + η_W)`
and `P₃ = −(⟨Ξ Z, Ξ⟩/d) ⊙ Ξ W`, row by row (as in `claimRMS_castSucc_tanh`). -/
private theorem tangentRMS_smul_mul {q : Type*} [Fintype q] (Z : Matrix d d ℝ) (Ξ : Matrix T d ℝ)
    (W ηW : Matrix d q ℝ) (t : ℝ) :
    tangentRMS Z (t • Ξ) * W + (t • Ξ) * ηW = t • (Ξ * (Z * W + ηW))
      + t ^ 3 • -(Matrix.of fun τ j => ((Ξ * Z) τ ⬝ᵥ Ξ τ / (Fintype.card d : ℝ)) * (Ξ * W) τ j) := by
  have hrow : ∀ (c : ℝ) (M : Matrix T d ℝ) (τ : T), (c • M) τ = c • M τ := fun _ _ _ => rfl
  have hT : tangentRMS Z (t • Ξ) = t • (Ξ * Z) - t ^ 3 • Matrix.of fun τ =>
      ((Ξ * Z) τ ⬝ᵥ Ξ τ / (Fintype.card d : ℝ)) • Ξ τ := by
    ext τ i
    simp only [tangentRMS, Matrix.smul_mul, hrow, smul_dotProduct, dotProduct_smul,
      Matrix.of_apply, Matrix.sub_apply, Matrix.smul_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul]
    ring
  have hPW : (Matrix.of fun τ => ((Ξ * Z) τ ⬝ᵥ Ξ τ / (Fintype.card d : ℝ)) • Ξ τ) * W
      = Matrix.of fun τ j => ((Ξ * Z) τ ⬝ᵥ Ξ τ / (Fintype.card d : ℝ)) * (Ξ * W) τ j := by
    ext τ j
    simp only [Matrix.mul_apply, Matrix.of_apply, Pi.smul_apply, smul_eq_mul,
      Finset.mul_sum, mul_assoc]
  rw [hT, Matrix.sub_mul, Matrix.smul_mul, Matrix.smul_mul, hPW, Matrix.smul_mul,
    Matrix.mul_add, Matrix.mul_assoc, smul_add, smul_neg]
  abel

/-- Helper: for `Φ` differentiable at `(x, y)`, the derivatives of its two partial maps add up to
its derivative along `(a, b)` (as in `Depth/StepTanh.lean`). -/
private theorem fderiv_partial_add'' {E₁ E₂ F : Type*} [NormedAddCommGroup E₁]
    [NormedSpace ℝ E₁] [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {Φ : E₁ → E₂ → F} {x : E₁} {y : E₂}
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
private theorem analyticOnNhd_clm_apply'' {X E F : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {J : X → E →L[ℝ] F} {v : X → E} {s : Set X} (hJ : AnalyticOnNhd ℝ J s)
    (hv : AnalyticOnNhd ℝ v s) : AnalyticOnNhd ℝ (fun x => J x (v x)) s :=
  fun x hx => ((ContinuousLinearMap.id ℝ (E →L[ℝ] F)).analyticAt_bilinear (J x, v x)).comp₂
    (hJ x hx) (hv x hx)

/-- Helper (step 6): for a real-analytic `χ` and real-analytic blocks, `w ↦ 𝓛(w, 0)` is
real-analytic on the whole space. -/
private theorem analyticOnNhd_writeLHS_zero (Ar : Arch T d L)
    (hχ : AnalyticOnNhd ℝ Ar.χ Set.univ) (hf : ∀ ℓ, AnalyticOnNhd ℝ (Ar.f ℓ) Set.univ)
    (θ η : Params Ar dIn dOut) (k : Fin L) :
    AnalyticOnNhd ℝ (fun w : Matrix T (Ar.w k) ℝ => writeLHS Ar θ k η w 0) Set.univ := by
  have hΦ := analyticOnNhd_suffix_prod_of_analytic Ar (dIn := dIn) (dOut := dOut) hχ hf k.succ
  -- `𝓛(w, 0)` is the derivative of `(θ', h') ↦ 𝓑(h')` at `(θ, w V)` along `(η, 0 V + w η_V)`
  have heq : (fun w : Matrix T (Ar.w k) ℝ => writeLHS Ar θ k η w 0) = fun w => fderiv ℝ
      (fun p : Params Ar dIn dOut × Matrix T d ℝ => suffix Ar 0 p.1 k.succ p.2)
      (θ, w * θ.write k) (η, (0 : Matrix T (Ar.w k) ℝ) * θ.write k + w * η.write k) := by
    funext w
    exact fderiv_partial_add'' (Φ := fun θ' h' => suffix Ar 0 θ' k.succ h')
      (hΦ _ (Set.mem_univ _)).differentiableAt η _
  rw [heq]
  exact analyticOnNhd_clm_apply'' (hΦ.fderiv.comp (analyticOnNhd_const.prod
      (analyticOnNhd_matrix_mul analyticOnNhd_id analyticOnNhd_const)) (Set.mapsTo_univ _ _))
    (analyticOnNhd_const.prod (analyticOnNhd_const.add
      (analyticOnNhd_matrix_mul analyticOnNhd_id analyticOnNhd_const)))

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: `w ↦ W − w/t` tends to `0` at `t W`. -/
private theorem tendsto_sub_inv_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (W : E)
    {t : ℝ} (ht : t ≠ 0) : Tendsto (fun w : E => W - t⁻¹ • w) (𝓝 (t • W)) (𝓝 0) := by
  have hc : Continuous fun w : E => W - t⁻¹ • w := by fun_prop
  have h := hc.tendsto (t • W)
  simp only [inv_smul_smul₀ ht, sub_self] at h
  exact h

/-- **Lemma D.12 up to (38), on one generic ray, MLP blocks, case (+).** Let `θ` be good for the
cones, let `Z` and `η` satisfy (16) for `k`, and let `Ξ` have its rows in `C_k` and satisfy (i) and
(iii). Then `ż(Ξ) = 0`, and `𝐃𝓑(w̃ V)(w̃ η_V) + 𝐃_θ 𝓑(w̃ V) η = 0` for every `w̃`. -/
theorem flat_at_generic_ray_mlp_rmsNorm (hε : 0 < ε) (hg : GateFar σ σ' p)
    (hone : ∀ u : ℝ, 0 < u → ∀ a b : ℝ → Matrix T dOut ℝ, AnalyticAt ℝ a 0 → AnalyticAt ℝ b 0 →
      (∀ᶠ s in 𝓝 (0 : ℝ), a (-s) = a s ∧ b (-s) = b s) →
      FasterThanPowers (fun t : ℝ =>
        a (1 / t) + (t * (1 - σ' (t * u)) / (t * u - σ (t * u))) • b (1 / t)) →
      ∀ᶠ s in 𝓝 (0 : ℝ), b s = 0)
    {C : Fin (L + 1) → Set (d → ℝ)} {A : ∀ ℓ, Finset (hid ℓ)}
    {θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut}
    (hθ : GoodForConesMlp C A θ) (k : Fin L) (Z : Matrix d d ℝ)
    (η : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)
    (hflat : SuffixFlat (Arch.mlp σ (rmsNorm ε) hid) θ k.castSucc Z η)
    (Ξ : Matrix T d ℝ) (hΞ : ∀ t, Ξ t ∈ C k.castSucc)
    (hi : LinearIndependent ℚ (fun i : T × hid k => |(Ξ * θ.read k) i.1 i.2| ^ p))
    (hiii : Function.Injective
      (fderiv ℝ (fun h' : Matrix T d ℝ => suffix (Arch.mlp σ (rmsNorm ε) hid) 0 θ k.succ h')
        (Matrix.of fun t => frozenMlp θ k (A k) (Ξ t)))) :
    tangentRMS Z Ξ * θ.read k + Ξ * η.read k = 0 ∧
      ∀ w : Matrix T (hid k) ℝ, writeLHS (Arch.mlp σ (rmsNorm ε) hid) θ k η w 0 = 0 := by
  classical
  -- the blocks are real-analytic
  have hf : ∀ ℓ, AnalyticOnNhd ℝ ((Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid).f ℓ) Set.univ :=
    fun ℓ => analyticOnNhd_f_mlp hg.analytic ℓ
  -- (K1) on the rows of `Ξ`: the gates `g = Ξ W` are positive on `A k` and negative off it
  have hgate : ∀ τ j, (j ∈ A k → 0 < (Ξ * θ.read k) τ j) ∧
      (j ∉ A k → (Ξ * θ.read k) τ j < 0) := fun τ j =>
    ⟨fun hj => hθ.gate_pos k (Ξ τ) (hΞ τ) j hj, fun hj => hθ.gate_neg k (Ξ τ) (hΞ τ) j hj⟩
  -- `u = |g| > 0`
  obtain ⟨u, hu_def⟩ : ∃ u : Matrix T (hid k) ℝ, ∀ τ j, u τ j = |(Ξ * θ.read k) τ j| :=
    ⟨fun τ j => |(Ξ * θ.read k) τ j|, fun _ _ => rfl⟩
  have hu : ∀ τ j, 0 < u τ j := fun τ j => by
    rw [hu_def]
    refine abs_pos.2 ?_
    by_cases hj : j ∈ A k
    · exact ((hgate τ j).1 hj).ne'
    · exact ((hgate τ j).2 hj).ne
  -- `W°` (the gates on `A k`), the signs `s_j`, and `ż(t Ξ) = t P₁ + t³ P₃`
  obtain ⟨Wo, hWo⟩ : ∃ Wo : Matrix T (hid k) ℝ, ∀ τ j,
      Wo τ j = if j ∈ A k then (Ξ * θ.read k) τ j else 0 :=
    ⟨fun τ j => if j ∈ A k then (Ξ * θ.read k) τ j else 0, fun _ _ => rfl⟩
  obtain ⟨sg, hsg⟩ : ∃ sg : hid k → ℝ, ∀ j, sg j = if j ∈ A k then 1 else -1 :=
    ⟨fun j => if j ∈ A k then 1 else -1, fun _ => rfl⟩
  have hsg0 : ∀ j, sg j ≠ 0 := fun j => by
    rw [hsg]
    split_ifs <;> norm_num
  obtain ⟨P₁, hP₁⟩ : ∃ P₁ : Matrix T (hid k) ℝ, P₁ = Ξ * (Z * θ.read k + η.read k) := ⟨_, rfl⟩
  obtain ⟨P₃, hP₃⟩ : ∃ P₃ : Matrix T (hid k) ℝ, P₃ = -(Matrix.of fun τ j =>
      ((Ξ * Z) τ ⬝ᵥ Ξ τ / (Fintype.card d : ℝ)) * (Ξ * θ.read k) τ j) := ⟨_, rfl⟩
  have hzd : ∀ t : ℝ,
      tangentRMS Z (t • Ξ) * θ.read k + (t • Ξ) * η.read k = t • P₁ + t ^ 3 • P₃ := fun t => by
    rw [hP₁, hP₃]
    exact tangentRMS_smul_mul Z Ξ _ _ t
  -- the matrices `M₀ = 1_A ⊙ P₃`, `M₂ = 1_A ⊙ P₁` and the coefficients `c = −s ⊙ P`
  obtain ⟨M₀, hM₀⟩ : ∃ M₀ : Matrix T (hid k) ℝ, ∀ τ j, M₀ τ j = if j ∈ A k then P₃ τ j else 0 :=
    ⟨fun τ j => if j ∈ A k then P₃ τ j else 0, fun _ _ => rfl⟩
  obtain ⟨M₂, hM₂⟩ : ∃ M₂ : Matrix T (hid k) ℝ, ∀ τ j, M₂ τ j = if j ∈ A k then P₁ τ j else 0 :=
    ⟨fun τ j => if j ∈ A k then P₁ τ j else 0, fun _ _ => rfl⟩
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : Matrix T (hid k) ℝ, ∀ τ j, c₀ τ j = -(sg j) * P₃ τ j :=
    ⟨fun τ j => -(sg j) * P₃ τ j, fun _ _ => rfl⟩
  obtain ⟨c₂, hc₂⟩ : ∃ c₂ : Matrix T (hid k) ℝ, ∀ τ j, c₂ τ j = -(sg j) * P₁ τ j :=
    ⟨fun τ j => -(sg j) * P₁ τ j, fun _ _ => rfl⟩
  -- the maps `G₀` and `G_{τj}` of step 3
  set G₀ := rayG0 (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) ε θ η k Wo M₀ M₂ with hG₀
  set G := rayG (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) ε θ k Wo c₀ c₂ with hG
  -- `W° V = g°(Ξ)`, whose rows lie in `C_{k+1}`, so none vanishes
  have hWoV : Wo * θ.write k = Matrix.of fun τ => frozenMlp θ k (A k) (Ξ τ) := by
    ext τ i
    simp only [Matrix.mul_apply, hWo, Matrix.of_apply, frozenMlp, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, ite_mul, zero_mul]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
    rfl
  have hH : ∀ τ, (Wo * θ.write k) τ ≠ 0 := fun τ h0 => by
    have hm := hθ.frozen_mem k (Ξ τ) (hΞ τ)
    rw [hWoV] at h0
    rw [show frozenMlp θ k (A k) (Ξ τ) = 0 from h0] at hm
    exact (hθ.cone k.succ).zero_notMem hm
  have hG₀an : AnalyticAt ℝ G₀ 0 := analyticAt_rayG0 _ hε rfl hf θ η k Wo M₀ M₂ hH
  have hGan : ∀ τ j, AnalyticAt ℝ (G τ j) 0 := fun τ j =>
    analyticAt_rayG _ hε rfl hf θ k Wo c₀ c₂ τ j hH
  -- step 5: if `G_{τj}(s, 0) = 0` near `0`, then both coefficients vanish
  have hcoef : ∀ τ j, (∀ᶠ s in 𝓝 (0 : ℝ), G τ j (s, 0) = 0) → c₀ τ j = 0 ∧ c₂ τ j = 0 := by
    intro τ j h
    refine eq_zero_of_eventually_smul_eq_zero (β := fun s => fderiv ℝ (fun h' : Matrix T d ℝ =>
        scaledSuffix (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) ε 1 θ k.succ (s, h'))
        ((Wo - 0) * θ.write k) (Matrix.single τ j (1 : ℝ) * θ.write k)) ?_ ?_ h
    · -- `β` is analytic on `ℝ`
      intro S₀ _
      exact analyticAt_fderiv_scaledSuffix _ hε rfl hf θ k.succ analyticAt_id analyticAt_const
        analyticAt_const (by simpa only [sub_zero] using hH)
    · -- `β(1) = 𝐃𝓑(g°(Ξ))(E_{τj} V) ≠ 0`, by (iii) and `a_j ≠ 0`
      have hfun : (fun h' : Matrix T d ℝ =>
          scaledSuffix (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) ε 1 θ k.succ (1, h'))
          = fun h' => suffix (Arch.mlp σ (rmsNorm ε) hid) 0 θ k.succ h' := by
        funext h'
        have e := suffix_pow_smul_eq_scaledSuffix (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid)
          (dIn := dIn) (dOut := dOut) rfl θ k.succ one_pos 1 h'
        rw [one_pow, one_smul, div_one] at e
        exact e.symm
      show fderiv ℝ (fun h' : Matrix T d ℝ =>
          scaledSuffix (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) ε 1 θ k.succ (1, h'))
          ((Wo - 0) * θ.write k) (Matrix.single τ j (1 : ℝ) * θ.write k) ≠ 0
      rw [hfun, sub_zero, hWoV]
      intro h0
      have h1 := hiii (h0.trans (map_zero _).symm)
      apply hθ.write_ne_zero k j
      funext i
      have e := congrFun (congrFun h1 τ) i
      rw [Matrix.single_mul_apply_same, one_mul] at e
      exact e
  -- the small terms `ζ`, `ν` of step 2 and the rates `r = u^p/p`
  obtain ⟨ζ, hζ⟩ : ∃ ζ : ℝ → Matrix T (hid k) ℝ, ∀ t τ j,
      ζ t τ j = (t * u τ j - σ (t * u τ j)) / t :=
    ⟨fun t τ j => (t * u τ j - σ (t * u τ j)) / t, fun _ _ _ => rfl⟩
  obtain ⟨ν, hν⟩ : ∃ ν : ℝ → Matrix T (hid k) ℝ, ∀ t τ j,
      ν t τ j = t * (1 - σ' (t * u τ j)) / (t * u τ j - σ (t * u τ j)) :=
    ⟨fun t τ j => t * (1 - σ' (t * u τ j)) / (t * u τ j - σ (t * u τ j)), fun _ _ _ => rfl⟩
  obtain ⟨r, hr⟩ : ∃ r : Matrix T (hid k) ℝ, ∀ τ j, r τ j = u τ j ^ p / p :=
    ⟨fun τ j => u τ j ^ p / p, fun _ _ => rfl⟩
  -- step 1 on the ray, entry by entry: `σ(t g) = t W° − δ(t u)` and
  -- `σ'(t g) = 1_A − s δ'(t u)`, by (24)
  have hent : ∀ t : ℝ, t ≠ 0 → ∀ τ j,
      σ (((t • Ξ) * θ.read k) τ j) = t * (Wo τ j - ζ t τ j) ∧
      σ' (((t • Ξ) * θ.read k) τ j) * (t * P₁ τ j + t ^ 3 * P₃ τ j)
        = t ^ 3 * ((M₀ τ j + (1 / t) ^ 2 * M₂ τ j)
          + (-(sg j) * (1 - σ' (t * u τ j))) * (P₃ τ j + (1 / t) ^ 2 * P₁ τ j)) := by
    intro t ht τ j
    have e : ((t • Ξ) * θ.read k) τ j = t * (Ξ * θ.read k) τ j := by
      rw [Matrix.smul_mul]
      rfl
    rw [e, hζ, hWo, hsg, hM₀, hM₂]
    by_cases hj : j ∈ A k
    · have hu' : u τ j = (Ξ * θ.read k) τ j := by rw [hu_def, abs_of_pos ((hgate τ j).1 hj)]
      simp only [hj, ite_true, hu']
      constructor
      · field_simp
        ring
      · field_simp
        ring
    · have hu' : (Ξ * θ.read k) τ j = -u τ j := by
        rw [hu_def, abs_of_neg ((hgate τ j).2 hj), neg_neg]
      obtain ⟨hn1, hn2⟩ := hg.neg (t * u τ j)
      have e2 : t * (Ξ * θ.read k) τ j = -(t * u τ j) := by rw [hu']; ring
      simp only [hj, ite_false]
      rw [e2, hn1, hn2]
      constructor
      · field_simp
        ring
      · field_simp
        ring
  have hR1 : ∀ t : ℝ, t ≠ 0 → ((t • Ξ) * θ.read k).map σ = t • (Wo - ζ t) := fun t ht => by
    ext τ j
    rw [Matrix.map_apply, (hent t ht τ j).1]
    rfl
  have hR2 : ∀ t : ℝ, t ≠ 0 → (Matrix.of fun τ j => ((t • Ξ) * θ.read k).map σ' τ j
        * (tangentRMS Z (t • Ξ) * θ.read k + (t • Ξ) * η.read k) τ j)
      = t ^ 3 • ((M₀ + (1 / t) ^ 2 • M₂) + Matrix.of fun τ j =>
          (-(sg j) * (1 - σ' (t * u τ j))) * (P₃ τ j + (1 / t) ^ 2 * P₁ τ j)) := fun t ht => by
    ext τ j
    rw [hzd t]
    simp only [Matrix.of_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    exact (hent t ht τ j).2
  -- step 3: `G₀(1/t, ζ) + ∑ (ν ζ) G_{τj}(1/t, ζ) = t^{-2} 𝓛(v(t), v̇(t)) = 0`
  have hzero : ∀ t : ℝ, 0 < t → (∀ τ j, t * u τ j - σ (t * u τ j) ≠ 0) →
      G₀ (1 / t, ζ t) + ∑ a, ∑ j, (ν t a j * ζ t a j) • G a j (1 / t, ζ t) = 0 := by
    intro t ht hδ
    -- (16) at `n = t Ξ`, by Lemma D.6
    have e := (suffixFlat_castSucc_iff_mlp_rmsNorm hε hg.hasDerivAt hg.analytic θ k Z η).1
      hflat (t • Ξ)
    have e2 : writeLHS (Arch.mlp σ (rmsNorm ε) hid) θ k η (t • (Wo - ζ t))
        (t ^ 3 • ((M₀ + (1 / t) ^ 2 • M₂) + Matrix.of fun τ j =>
          (-(sg j) * (1 - σ' (t * u τ j))) * (P₃ τ j + (1 / t) ^ 2 * P₁ τ j))) = 0 := by
      rw [← hR1 t ht.ne', ← hR2 t ht.ne']
      exact e
    rw [writeLHS_ray_eq _ hε rfl hf θ η k ht, fderiv_mul_eq_sum] at e2
    have e3 := (smul_eq_zero.1 e2).resolve_left (pow_ne_zero 2 ht.ne')
    refine Eq.trans ?_ e3
    congr 1
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [hG, rayG, smul_smul, Matrix.of_apply]
    congr 1
    rw [hν, hζ, hc₀, hc₂]
    have ht' := ht.ne'
    have hδ' := hδ a j
    field_simp
    ring
  -- step 2: the bounds on the small terms, with one constant `A₀` and `N = 2`
  obtain ⟨A₀, hA₀⟩ : ∃ A₀ : ℝ, A₀ = 6 + 4 * ∑ a, ∑ j, u a j := ⟨_, rfl⟩
  have hsum0 : 0 ≤ ∑ a, ∑ j, u a j :=
    Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun j _ => (hu a j).le
  have hsum : ∀ a j, u a j ≤ ∑ a, ∑ j, u a j := fun a j =>
    (Finset.single_le_sum (fun j _ => (hu a j).le) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun a => ∑ j, u a j)
        (fun a _ => Finset.sum_nonneg fun j _ => (hu a j).le) (Finset.mem_univ a))
  have hA6 : 6 ≤ A₀ := by rw [hA₀]; linarith
  have hAu : ∀ a j, 4 * u a j ≤ A₀ := fun a j => by rw [hA₀]; linarith [hsum a j]
  have hbnd : ∀ᶠ t in atTop, ∀ a j,
      Real.exp (-(u a j ^ p / p * t ^ p)) ≤ A₀ * t ^ 2 * ((t * u a j - σ (t * u a j)) / t) ∧
      |(t * u a j - σ (t * u a j)) / t| ≤ A₀ * t ^ 2 * Real.exp (-(u a j ^ p / p * t ^ p)) ∧
      |t * (1 - σ' (t * u a j)) / (t * u a j - σ (t * u a j))| ≤ A₀ * t ^ 2 ∧
      0 < t * u a j - σ (t * u a j) :=
    Filter.eventually_all.2 fun a => Filter.eventually_all.2 fun j => by
      filter_upwards [eventually_ge_atTop 1, eventually_ge_atTop (2 / u a j)] with t ht1 ht2
      exact gap_bounds hg (hu a j) ht1 ((div_le_iff₀ (hu a j)).1 ht2) hA6 (hAu a j)
  have hζl : ∀ᶠ t : ℝ in atTop, ∀ a j, Real.exp (-(r a j * t ^ p)) ≤ A₀ * t ^ 2 * ζ t a j :=
    hbnd.mono fun t h a j => by rw [hr, hζ]; exact (h a j).1
  have hζu : ∀ᶠ t : ℝ in atTop, ∀ a j, |ζ t a j| ≤ A₀ * t ^ 2 * Real.exp (-(r a j * t ^ p)) :=
    hbnd.mono fun t h a j => by rw [hr, hζ]; exact (h a j).2.1
  have hνb : ∀ᶠ t : ℝ in atTop, ∀ a j, |ν t a j| ≤ A₀ * t ^ 2 :=
    hbnd.mono fun t h a j => by rw [hν]; exact (h a j).2.2.1
  -- fact (b): the left side vanishes for all large `t`
  have hidt : ∀ R : ℝ, ∀ᶠ t : ℝ in atTop,
      ‖G₀ (1 / t, ζ t) + ∑ a, ∑ j, (ν t a j * ζ t a j) • G a j (1 / t, ζ t)‖
        ≤ Real.exp (-(R * t ^ p)) := by
    intro R
    filter_upwards [hbnd, eventually_gt_atTop 0] with t h ht
    rw [hzero t ht fun a j => (h a j).2.2.2.ne', norm_zero]
    exact (Real.exp_pos _).le
  -- the rates are positive and independent over `ℚ` (by (i), up to the factor `1/p`)
  have hp0 : p ≠ 0 := by have := hg.one_le; omega
  have hrpos : ∀ a j, 0 < r a j := fun a j => by
    rw [hr]
    exact div_pos (pow_pos (hu a j) p) (Nat.cast_pos.2 (Nat.pos_of_ne_zero hp0))
  have hrQ : LinearIndependent ℚ (fun i : T × hid k => r i.1 i.2) := by
    have hpQ : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hp0
    have h := hi.units_smul (fun _ => Units.mk0 ((p : ℚ)⁻¹) (inv_ne_zero hpQ))
    convert h using 1
    funext i
    rw [hr, hu_def, Pi.smul_apply', Units.smul_def, Units.val_mk0, Rat.smul_def, Rat.cast_inv,
      Rat.cast_natCast]
    ring
  -- step 4: `G₀` and `G_{τj}` are even in `s`
  have hG₀even : ∀ s y, G₀ (-s, y) = G₀ (s, y) := fun s y => rayG0_neg _ θ η k Wo M₀ M₂ s y
  have hGeven : ∀ τ j s y, G τ j (-s, y) = G τ j (s, y) := fun τ j s y =>
    rayG_neg _ θ k Wo c₀ c₂ τ j s y
  -- step 5: the step "one small factor"
  have hstep : ∀ a j,
      FasterThanPowers (fun t : ℝ =>
        fderiv ℝ (fun y : Matrix T (hid k) ℝ => G₀ (1 / t, y)) 0 (Matrix.single a j 1)
          + ν t a j • G a j (1 / t, 0)) →
      ∀ᶠ z in 𝓝 (0 : ℝ × Matrix T (hid k) ℝ), G a j z = 0 := by
    intro a j hfast
    have hfast' : FasterThanPowers (fun t : ℝ =>
        (fun s => fderiv ℝ (fun y : Matrix T (hid k) ℝ => G₀ (s, y)) 0 (Matrix.single a j 1))
          (1 / t)
        + (t * (1 - σ' (t * u a j)) / (t * u a j - σ (t * u a j)))
          • (fun s => G a j (s, 0)) (1 / t)) :=
      hfast.congr (Eventually.of_forall fun t => by rw [hν])
    have hb0 := hone (u a j) (hu a j)
      (fun s => fderiv ℝ (fun y : Matrix T (hid k) ℝ => G₀ (s, y)) 0 (Matrix.single a j 1))
      (fun s => G a j (s, 0))
      (analyticAt_fderiv_partial_snd (x₀ := (0 : ℝ)) (y₀ := (0 : Matrix T (hid k) ℝ)) hG₀an _)
      ((hGan a j).comp_of_eq (analyticAt_id.prod analyticAt_const) rfl)
      (Eventually.of_forall fun s => ⟨by simp only [hG₀even], hGeven a j s 0⟩) hfast'
    obtain ⟨h0, h2⟩ := hcoef a j hb0
    exact Eventually.of_forall fun z => by
      simp only [hG, rayG, h0, h2, mul_zero, zero_add, zero_smul]
  -- the induction on the exponents
  have hRI := ray_induction_matrix (T := T) (q := hid k) (F := Matrix T dOut ℝ) p hg.one_le r
    hrpos hrQ ζ ν A₀ 2 hζl hζu hνb G₀ G hG₀an hGan
  obtain ⟨hG₀0, hG0⟩ := hRI hidt hstep
  -- step 6: `P₁ = 0` and `P₃ = 0`
  have hP0 : ∀ a j, P₃ a j = 0 ∧ P₁ a j = 0 := fun a j => by
    have h := ((continuous_id.prodMk continuous_const).tendsto' (0 : ℝ)
      ((0 : ℝ), (0 : Matrix T (hid k) ℝ)) rfl).eventually (hG0 a j)
    obtain ⟨h0, h2⟩ := hcoef a j h
    rw [hc₀] at h0
    rw [hc₂] at h2
    exact ⟨(mul_eq_zero.1 h0).resolve_left (neg_ne_zero.2 (hsg0 j)),
      (mul_eq_zero.1 h2).resolve_left (neg_ne_zero.2 (hsg0 j))⟩
  have hP₁0 : P₁ = 0 := by ext a j; exact (hP0 a j).2
  have hP₃0 : P₃ = 0 := by ext a j; exact (hP0 a j).1
  refine ⟨?_, ?_⟩
  · -- `ż(Ξ) = P₁ + P₃ = 0`
    have e := hzd 1
    simp only [one_smul, one_pow, hP₁0, hP₃0, add_zero] at e
    exact e
  · -- `M₀ = 0`, `M₂ = 0`, and `G₀(s₀, y) = 0` for some `s₀ > 0` and all `y` near `0`
    have hM₀0 : M₀ = 0 := by
      ext a j
      rw [hM₀, hP₃0]
      split_ifs <;> rfl
    have hM₂0 : M₂ = 0 := by
      ext a j
      rw [hM₂, hP₁0]
      split_ifs <;> rfl
    have hcur : ∀ᶠ S in 𝓝 (0 : ℝ), ∀ᶠ Y in 𝓝 (0 : Matrix T (hid k) ℝ), G₀ (S, Y) = 0 := by
      have h := hG₀0
      rw [← Prod.mk_zero_zero, nhds_prod_eq] at h
      exact h.curry
    have h1 : ∀ᶠ S in 𝓝[>] (0 : ℝ), ∀ᶠ Y in 𝓝 (0 : Matrix T (hid k) ℝ), G₀ (S, Y) = 0 :=
      nhdsWithin_le_nhds hcur
    obtain ⟨S₀, hS₀, hS₀pos⟩ := (h1.and eventually_mem_nhdsWithin).exists
    have hS₀' : (0 : ℝ) < S₀ := hS₀pos
    obtain ⟨t₀, ht₀⟩ : ∃ t₀ : ℝ, t₀ = S₀⁻¹ := ⟨_, rfl⟩
    have ht₀pos : 0 < t₀ := by rw [ht₀]; exact inv_pos.2 hS₀'
    have hts : 1 / t₀ = S₀ := by rw [ht₀, one_div, inv_inv]
    -- so `𝓛(w, 0) = t₀² G₀(s₀, W° − w/t₀) = 0` for `w` near `t₀ W°`
    have hloc : (fun w : Matrix T (hid k) ℝ =>
        writeLHS (Arch.mlp σ (rmsNorm ε) hid) θ k η w 0) =ᶠ[𝓝 (t₀ • Wo)] 0 := by
      filter_upwards [(tendsto_sub_inv_smul Wo ht₀pos.ne').eventually hS₀] with w hw
      have hw' : w = t₀ • (Wo - (Wo - t₀⁻¹ • w)) := by
        rw [sub_sub_cancel, smul_inv_smul₀ ht₀pos.ne']
      have h0 : (0 : Matrix T (hid k) ℝ) = t₀ ^ 3 • ((M₀ + (1 / t₀) ^ 2 • M₂) + 0) := by
        rw [hM₀0, hM₂0, smul_zero, add_zero, add_zero, smul_zero]
      show writeLHS _ θ k η w 0 = 0
      rw [h0, hw', writeLHS_ray_eq _ hε rfl hf θ η k ht₀pos, ← hG₀, hts, hw, Matrix.zero_mul,
        map_zero, add_zero, smul_zero]
    -- the identity theorem on the whole space
    intro w
    exact (analyticOnNhd_writeLHS_zero _ (analyticOnNhd_rmsNorm hε) hf θ η k
      ).eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
      (Set.mem_univ (t₀ • Wo)) hloc (Set.mem_univ w)

/-- **Lemma D.12 up to (38), MLP blocks, case (+).** Let `θ` be good for the cones and regular, and
let the `Ξ` with (i) be dense. If `Z` and `η` satisfy (16) for `k`, then `ż(n) = 0` for every `n`
with its rows in `C_k`, and `𝐃𝓑(w̃ V)(w̃ η_V) + 𝐃_θ 𝓑(w̃ V) η = 0` for every `w̃`. -/
theorem flat_of_suffixFlat_mlp_rmsNorm (hε : 0 < ε) (hg : GateFar σ σ' p)
    (hone : ∀ u : ℝ, 0 < u → ∀ a b : ℝ → Matrix T dOut ℝ, AnalyticAt ℝ a 0 → AnalyticAt ℝ b 0 →
      (∀ᶠ s in 𝓝 (0 : ℝ), a (-s) = a s ∧ b (-s) = b s) →
      FasterThanPowers (fun t : ℝ =>
        a (1 / t) + (t * (1 - σ' (t * u)) / (t * u - σ (t * u))) • b (1 / t)) →
      ∀ᶠ s in 𝓝 (0 : ℝ), b s = 0)
    {C : Fin (L + 1) → Set (d → ℝ)} {A : ∀ ℓ, Finset (hid ℓ)}
    {θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut}
    (hθ : GoodForConesMlp C A θ) (hreg : Regular (Arch.mlp σ (rmsNorm ε) hid) θ) (k : Fin L)
    (hdense : Dense {Ξ : Matrix T d ℝ |
      LinearIndependent ℚ (fun i : T × hid k => |(Ξ * θ.read k) i.1 i.2| ^ p)})
    (Z : Matrix d d ℝ) (η : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)
    (hflat : SuffixFlat (Arch.mlp σ (rmsNorm ε) hid) θ k.castSucc Z η) :
    (∀ n : Matrix T d ℝ, (∀ t, n t ∈ C k.castSucc) →
        tangentRMS Z n * θ.read k + n * η.read k = 0) ∧
      ∀ w : Matrix T (hid k) ℝ, writeLHS (Arch.mlp σ (rmsNorm ε) hid) θ k η w 0 = 0 := by
  sorry

/-- **Lemma D.12 up to (38), GELU blocks, case (+):** with the matrices `c_j c_j^⊤` of the read
columns of block `k` linearly independent over `ℚ`. -/
theorem flat_of_suffixFlat_gelu_rmsNorm (hε : 0 < ε) {C : Fin (L + 1) → Set (d → ℝ)}
    {A : ∀ ℓ, Finset (hid ℓ)}
    {θ : Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm ε) hid) dIn dOut}
    (hθ : GoodForConesMlp C A θ) (k : Fin L)
    (hQ : LinearIndependent ℚ (fun j : hid k =>
      Matrix.vecMulVec ((θ.read k)ᵀ j) ((θ.read k)ᵀ j)))
    (Z : Matrix d d ℝ) (η : Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm ε) hid) dIn dOut)
    (hflat : SuffixFlat (Arch.mlp gelu (rmsNorm ε) hid) θ k.castSucc Z η) :
    (∀ n : Matrix T d ℝ, (∀ t, n t ∈ C k.castSucc) →
        tangentRMS Z n * θ.read k + n * η.read k = 0) ∧
      ∀ w : Matrix T (hid k) ℝ, writeLHS (Arch.mlp gelu (rmsNorm ε) hid) θ k η w 0 = 0 := by
  sorry

end Skips
