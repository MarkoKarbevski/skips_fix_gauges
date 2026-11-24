import SkipsLean.Depth.ScaledSuffix
import SkipsLean.Depth.RayInduction
import SkipsLean.Depth.RayDense
import SkipsLean.Depth.Frozen
import SkipsLean.Activations.OneSmallFactor

/-!
# Lemma D.12 on a ray, for gated blocks under pre-RMSNorm: from (28) to (38)

Paper (dimension): Appendix D.5, proof of Lemma D.12, from its beginning to equation (38), in the
case (+), for gated blocks. Here `𝓑^∞ = 𝓑_{>k+1}`, the network itself, and `𝓛^∞ = 𝓛`. On a ray
`n = t ξ` with `ξ ∈ C_k`, (24) turns (28) into (33); the left side is expanded in the small terms
of the gates, (34), with coefficients that are meromorphic at infinity, fact (a), "built from
derivatives of `𝓑` and of `𝐃_θ 𝓑(·) η'` at `t^m h°` and from polynomials in `t`, so this is
Lemma D.10 with `t^m` in the place of `t`"; the left side vanishes, fact (b). For a generic ray
((i), (ii), (iii): see `Depth/RayGatedN.lean`) the induction on the exponents shows that all
coefficients vanish, where the step "one small factor" is Lemma D.9 for GeGLU blocks and the parity
(30) for SwiGLU blocks, and where, by (29), `L'_j(t) = ż^g_j(t ξ) ι_j(t ξ) 𝐃𝓑^∞(t^m h°) a_j`: "By
(iii), (K3) and Lemma D.2, `𝐃𝓑^∞(h°) a_j ≠ 0`, so the last factor, which is real-analytic in `t`,
vanishes only at isolated `t`." The result is (38): "for all `n ∈ C_k` and all rows
`w̃ ∈ ℝ^{1×q}`, with `ŵ = w̃ ⊙ ι(n)`, `ż^g(n) = 0` and
`𝐃𝓑^∞(ŵ V) ((w̃ ⊙ ż^v(n)) V + ŵ η_V) + 𝐃_θ 𝓑^∞(ŵ V) η' = 0`."

Stated here, for a gate `σ` with `GateFar σ σ' p` and with the step "one small factor" as the
hypothesis `hone` (it is `one_small_factor_gelu` for GELU and `one_small_factor_silu` for SiLU;
the evenness in `hone` is the parity (30) in the variable `s = 1/t`), and for hidden states with
the rows `T`: (38) at one generic `Ξ`; then (38) for all `n` with rows in `C_k`, given that the `Ξ`
with (i) are dense; then the same for SwiGLU and GeGLU blocks from the independence over `ℚ` of
(K3) for block `k`. In the case (+), `ż(n) = (n Z − ⟨n Z, n⟩ n / d) W_read + n η_read`
(`tangentRMS`). The second part of (38) is written with `writeLHS` at `v = w̃ ⊙ ι(n)`,
`vdot = w̃ ⊙ ż^v(n)`. Condition (iii) says that the derivative of the network after the block is
injective at `g°(Ξ)`.
-/

namespace Skips

open Matrix Filter
open scoped Matrix.Norms.Elementwise Topology

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]
variable {σ σ' : ℝ → ℝ} {p : ℕ} {ε : ℝ}

/-! ### Generic helpers: partial derivatives of analytic maps -/

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the derivative of a partial map in the second variable is the derivative of the joint
map along `(0, v)`. -/
private theorem fderiv_partial_sndRGP {E₁ E₂ G : Type*} [NormedAddCommGroup E₁]
    [NormedSpace ℝ E₁] [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [NormedAddCommGroup G]
    [NormedSpace ℝ G] {f : E₁ × E₂ → G} {x : E₁} {y : E₂} (hf : DifferentiableAt ℝ f (x, y))
    (v : E₂) : fderiv ℝ (fun y' => f (x, y')) y v = fderiv ℝ f (x, y) (0, v) := by
  have h : HasFDerivAt (fun y' => f (x, y'))
      ((fderiv ℝ f (x, y)).comp (ContinuousLinearMap.inr ℝ E₁ E₂)) y :=
    hf.hasFDerivAt.comp y (hasFDerivAt_prodMk_right x y)
  rw [h.fderiv]
  rfl

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: a partial derivative of a map that is analytic at a point, taken at analytic points
along analytic directions, is analytic. -/
private theorem analyticAt_fderiv_partialRGP {X E₁ E₂ G : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [NormedAddCommGroup E₂]
    [NormedSpace ℝ E₂] [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    {f : E₁ × E₂ → G} {a : X → E₁} {b c : X → E₂} {x₀ : X}
    (hf : AnalyticAt ℝ f (a x₀, b x₀)) (ha : AnalyticAt ℝ a x₀) (hb : AnalyticAt ℝ b x₀)
    (hc : AnalyticAt ℝ c x₀) :
    AnalyticAt ℝ (fun x => fderiv ℝ (fun y => f (a x, y)) (b x) (c x)) x₀ := by
  have hab : AnalyticAt ℝ (fun x => (a x, b x)) x₀ := ha.prod hb
  -- the derivative of the joint map, at `(a x, b x)` and along `(0, c x)`
  have hJ : AnalyticAt ℝ (fun x => fderiv ℝ f (a x, b x)) x₀ := hf.fderiv.comp_of_eq hab rfl
  have hv : AnalyticAt ℝ (fun x => ((0 : E₁), c x)) x₀ := analyticAt_const.prod hc
  have happ : AnalyticAt ℝ (fun x => fderiv ℝ f (a x, b x) (0, c x)) x₀ :=
    ((ContinuousLinearMap.id ℝ (E₁ × E₂ →L[ℝ] G)).analyticAt_bilinear _).comp₂ hJ hv
  -- near `x₀`, `f` is differentiable at `(a x, b x)`, where the two derivatives agree
  refine happ.congr ?_
  have hev : ∀ᶠ x in 𝓝 x₀, AnalyticAt ℝ f (a x, b x) :=
    hab.continuousAt.tendsto.eventually hf.eventually_analyticAt
  filter_upwards [hev] with x hx
  exact (fderiv_partial_sndRGP hx.differentiableAt (c x)).symm

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the product of two matrix-valued maps that are analytic at a point is analytic there. -/
private theorem analyticAt_matMulRGP {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {m n q : Type*} [Fintype m] [Fintype n] [Fintype q]
    {f : X → Matrix m n ℝ} {g : X → Matrix n q ℝ} {x : X}
    (hf : AnalyticAt ℝ f x) (hg : AnalyticAt ℝ g x) :
    AnalyticAt ℝ (fun y => f y * g y) x := by
  let B : Matrix m n ℝ →ₗ[ℝ] Matrix n q ℝ →ₗ[ℝ] Matrix m q ℝ :=
    LinearMap.mk₂ ℝ (fun a b => a * b) Matrix.add_mul (fun c a b => Matrix.smul_mul c a b)
      Matrix.mul_add (fun c a b => Matrix.mul_smul a c b)
  let B' : Matrix m n ℝ →L[ℝ] Matrix n q ℝ →L[ℝ] Matrix m q ℝ :=
    LinearMap.toContinuousLinearMap
      ((LinearMap.toContinuousLinearMap :
        (Matrix n q ℝ →ₗ[ℝ] Matrix m q ℝ) ≃ₗ[ℝ] (Matrix n q ℝ →L[ℝ] Matrix m q ℝ)).toLinearMap ∘ₗ B)
  have hB : (fun y => f y * g y) = fun y => B' (f y) (g y) := rfl
  rw [hB]
  exact (B'.analyticAt_bilinear (f x, g x)).comp₂ hf hg

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: an entry of an analytic matrix-valued map is analytic. -/
private theorem analyticAt_entryRGP {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {m n : Type*} [Fintype m] [Fintype n] {f : X → Matrix m n ℝ} {x : X}
    (hf : AnalyticAt ℝ f x) (i : m) (j : n) : AnalyticAt ℝ (fun y => f y i j) x :=
  (analyticOnNhd_matrix_entry i j (f x) (Set.mem_univ _)).comp_of_eq hf rfl

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: a matrix whose entries are analytic is analytic. -/
private theorem analyticAt_matrixOfRGP {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {m n : Type*} [Fintype m] [Fintype n] {f : X → m → n → ℝ} {x : X}
    (hf : ∀ i j, AnalyticAt ℝ (fun y => f y i j) x) :
    AnalyticAt ℝ (fun y => (Matrix.of (f y) : Matrix m n ℝ)) x :=
  AnalyticAt.pi fun i => AnalyticAt.pi fun j => hf i j

/-! ### The rest of the network on a ray: analyticity of its derivatives -/

/-- Helper: `x ↦ 𝐃_h Φ(a x, b x)(c x)`, the derivative of `h ↦ 𝓑^♯(N_{ε s^{2m}}(h))` at `s = a x`,
is analytic at `x₀` if `a`, `b`, `c` are and no row of `b x₀` vanishes (Lemma D.10). -/
private theorem analyticAt_fderiv_scaledSuffixRGP (A : Arch T d L) (hε : 0 < ε)
    (hχ : A.χ = rmsNorm ε) (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (m : ℕ)
    (θ : Params A dIn dOut) (k : Fin (L + 1)) {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] {a : X → ℝ} {b c : X → Matrix T d ℝ} {x₀ : X} (ha : AnalyticAt ℝ a x₀)
    (hb : AnalyticAt ℝ b x₀) (hc : AnalyticAt ℝ c x₀) (hb₀ : ∀ τ, b x₀ τ ≠ 0) :
    AnalyticAt ℝ (fun x => fderiv ℝ (fun h' : Matrix T d ℝ => scaledSuffix A ε m θ k (a x, h'))
      (b x) (c x)) x₀ := by
  have hF : AnalyticAt ℝ (fun z : ℝ × Matrix T d ℝ => scaledSuffix A ε m θ k z) (a x₀, b x₀) := by
    have h1 := analyticAt_scaledSuffix A hε hχ hf m θ k (a x₀) (b x₀) hb₀
    have h2 : AnalyticAt ℝ (fun z : ℝ × Matrix T d ℝ => ((θ, z) : Params A dIn dOut × ℝ × Matrix T d ℝ))
        (a x₀, b x₀) := analyticAt_const.prod analyticAt_id
    have hc := h1.comp h2
    exact hc
  exact analyticAt_fderiv_partialRGP (f := fun z : ℝ × Matrix T d ℝ => scaledSuffix A ε m θ k z)
    hF ha hb hc

/-- Helper: `x ↦ 𝐃_θ Φ(a x, b x) η`, the derivative in the weights, is analytic at `x₀` if `a`, `b`
are and no row of `b x₀` vanishes (Lemma D.10). -/
private theorem analyticAt_fderiv_params_scaledSuffixRGP (A : Arch T d L) (hε : 0 < ε)
    (hχ : A.χ = rmsNorm ε) (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (m : ℕ)
    (θ η : Params A dIn dOut) (k : Fin (L + 1)) {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] {a : X → ℝ} {b : X → Matrix T d ℝ} {x₀ : X} (ha : AnalyticAt ℝ a x₀)
    (hb : AnalyticAt ℝ b x₀) (hb₀ : ∀ τ, b x₀ τ ≠ 0) :
    AnalyticAt ℝ (fun x => fderiv ℝ (fun θ' : Params A dIn dOut => scaledSuffix A ε m θ' k
      (a x, b x)) θ η) x₀ := by
  have hF : AnalyticAt ℝ (fun z : (ℝ × Matrix T d ℝ) × Params A dIn dOut =>
      scaledSuffix A ε m z.2 k z.1) ((a x₀, b x₀), θ) := by
    have h1 := analyticAt_scaledSuffix A hε hχ hf m θ k (a x₀) (b x₀) hb₀
    have h2 : AnalyticAt ℝ (fun z : (ℝ × Matrix T d ℝ) × Params A dIn dOut =>
        ((z.2, z.1) : Params A dIn dOut × ℝ × Matrix T d ℝ)) ((a x₀, b x₀), θ) :=
      analyticAt_snd.prod analyticAt_fst
    have hc := h1.comp_of_eq h2 rfl
    exact hc
  exact analyticAt_fderiv_partialRGP
    (f := fun z : (ℝ × Matrix T d ℝ) × Params A dIn dOut => scaledSuffix A ε m z.2 k z.1)
    (a := fun x => (a x, b x)) (b := fun _ => θ) (c := fun _ => η) hF (ha.prod hb)
    analyticAt_const analyticAt_const

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: an analytic family of continuous linear maps, applied to an analytic family of vectors,
is analytic (as in `Depth/StepTanhRMS.lean`, at one point). -/
private theorem analyticAt_clm_applyRGP {X E F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {J : X → E →L[ℝ] F} {v : X → E} {x : X} (hJ : AnalyticAt ℝ J x) (hv : AnalyticAt ℝ v x) :
    AnalyticAt ℝ (fun x => J x (v x)) x :=
  ((ContinuousLinearMap.id ℝ (E →L[ℝ] F)).analyticAt_bilinear (J x, v x)).comp₂ hJ hv

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: for `Φ` differentiable at `(x, y)`, the derivatives of its two partial maps, along `b`
and `a`, add up to its derivative along `(a, b)` (as in `Depth/BlockIdentityGated.lean`). -/
private theorem fderiv_partial_addRGP {E₁ E₂ F : Type*} [NormedAddCommGroup E₁]
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

/-- Helper: for an analytic normalization and analytic blocks, the left side `writeLHS` of the
identity for one block is analytic in the outputs `v` of the hidden units and their derivative
`vdot`. -/
private theorem analyticAt_writeLHSRGP (A : Arch T d L) (hχ : AnalyticOnNhd ℝ A.χ Set.univ)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (θ η : Params A dIn dOut) (k : Fin L)
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {v vdot : X → Matrix T (A.w k) ℝ}
    {x₀ : X} (hv : AnalyticAt ℝ v x₀) (hvd : AnalyticAt ℝ vdot x₀) :
    AnalyticAt ℝ (fun x => writeLHS A θ k η (v x) (vdot x)) x₀ := by
  have hΦ := analyticOnNhd_suffix_prod_of_analytic A (dIn := dIn) (dOut := dOut) hχ hf k.succ
  -- `writeLHS` is the derivative of `(θ', h') ↦ 𝓑(h')` at `(θ, v V)` along `(η, vdot V + v η_V)`
  have heq : (fun x => writeLHS A θ k η (v x) (vdot x)) = fun x => fderiv ℝ
      (fun p : Params A dIn dOut × Matrix T d ℝ => suffix A 0 p.1 k.succ p.2) (θ, v x * θ.write k)
      (η, vdot x * θ.write k + v x * η.write k) := by
    funext x
    exact fderiv_partial_addRGP (Φ := fun θ' h' => suffix A 0 θ' k.succ h')
      (hΦ _ (Set.mem_univ _)).differentiableAt η _
  rw [heq]
  have hp : AnalyticAt ℝ (fun x => ((θ, v x * θ.write k) : Params A dIn dOut × Matrix T d ℝ)) x₀ :=
    analyticAt_const.prod (analyticAt_matMulRGP hv analyticAt_const)
  have hJ := (hΦ.fderiv _ (Set.mem_univ _)).comp_of_eq hp rfl
  have hd : AnalyticAt ℝ (fun x => ((η, vdot x * θ.write k + v x * η.write k) :
      Params A dIn dOut × Matrix T d ℝ)) x₀ :=
    analyticAt_const.prod ((analyticAt_matMulRGP hvd analyticAt_const).fun_add
      (analyticAt_matMulRGP hv analyticAt_const))
  have hc := analyticAt_clm_applyRGP hJ hd
  exact hc

/-! ### The left side of the identity on a ray, in the variable `s = 1/t` -/

/-- **The scaled left side** `Ψ(s, v, R) = 𝐃_hΦ(s, v V)(R V + s² v η_V) + s² 𝐃_θΦ(s, v V) η` with
`Φ(s, h) = 𝓑^♯(N_{ε s⁴}(h))`: for `t > 0`, `𝓛(t² v, t⁴ R) = t² Ψ(1/t, v, R)`. -/
private noncomputable def scaledLHS (A : Arch T d L) (ε : ℝ) (θ η : Params A dIn dOut) (k : Fin L)
    (S : ℝ) (v R : Matrix T (A.w k) ℝ) : Matrix T dOut ℝ :=
  fderiv ℝ (fun h' : Matrix T d ℝ => scaledSuffix A ε 2 θ k.succ (S, h')) (v * θ.write k)
      (R * θ.write k + S ^ 2 • (v * η.write k))
    + S ^ 2 • fderiv ℝ (fun θ' : Params A dIn dOut => scaledSuffix A ε 2 θ' k.succ
        (S, v * θ.write k)) θ η

/-- Helper: **the scaling of the left side on a ray** (Lemma D.10 with `t²` in the place of `t`):
`𝓛(t² v, t⁴ R) = t² Ψ(1/t, v, R)` for `t > 0`. -/
private theorem writeLHS_pow_smulRGP (A : Arch T d L) (hε : 0 < ε) (hχ : A.χ = rmsNorm ε)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (θ η : Params A dIn dOut) (k : Fin L) {t : ℝ}
    (ht : 0 < t) (v R : Matrix T (A.w k) ℝ) :
    writeLHS A θ k η (t ^ 2 • v) (t ^ 4 • R) = t ^ 2 • scaledLHS A ε θ η k (1 / t) v R := by
  unfold writeLHS scaledLHS
  rw [Matrix.smul_mul, Matrix.smul_mul, Matrix.smul_mul,
    fderiv_suffix_pow_smul A hε hχ hf θ k.succ ht 2, fderiv_params_suffix_pow_smul A hχ θ η k.succ ht 2]
  have ht' := ht.ne'
  have h1 : (1 / t) ^ 2 * t ^ 4 = t ^ 2 := by field_simp
  have h2 : (1 / t) ^ 2 * t ^ 2 = 1 := by field_simp
  have h3 : t ^ 2 * (1 / t) ^ 2 = 1 := by field_simp
  rw [map_add, map_smul, map_smul, map_add, map_smul, smul_add, smul_add, smul_add, smul_smul,
    smul_smul, smul_smul, smul_smul, h1, h2, h3, one_smul, one_smul]

omit [Fintype T] [DecidableEq d] in
/-- Helper: `Ψ` is affine in `R`. -/
private theorem scaledLHS_addRGP (A : Arch T d L) (θ η : Params A dIn dOut) (k : Fin L) (S : ℝ)
    (v R R' : Matrix T (A.w k) ℝ) :
    scaledLHS A ε θ η k S v (R + R') = scaledLHS A ε θ η k S v R
      + fderiv ℝ (fun h' : Matrix T d ℝ => scaledSuffix A ε 2 θ k.succ (S, h')) (v * θ.write k)
          (R' * θ.write k) := by
  unfold scaledLHS
  rw [Matrix.add_mul, add_right_comm, map_add]
  abel

/-- Helper: `Ψ` is even in `s`. -/
private theorem scaledLHS_negRGP (A : Arch T d L) (θ η : Params A dIn dOut) (k : Fin L) (S : ℝ)
    (v R : Matrix T (A.w k) ℝ) :
    scaledLHS A ε θ η k (-S) v R = scaledLHS A ε θ η k S v R := by
  unfold scaledLHS
  have h1 : (fun h' : Matrix T d ℝ => scaledSuffix A ε 2 θ k.succ (-S, h'))
      = fun h' => scaledSuffix A ε 2 θ k.succ (S, h') :=
    funext fun h' => scaledSuffix_neg A 2 θ k.succ S h'
  have h2 : (fun θ' : Params A dIn dOut => scaledSuffix A ε 2 θ' k.succ (-S, v * θ.write k))
      = fun θ' => scaledSuffix A ε 2 θ' k.succ (S, v * θ.write k) :=
    funext fun θ' => scaledSuffix_neg A 2 θ' k.succ S _
  rw [h1, h2, neg_sq]

/-- Helper: `Ψ` at analytic arguments is analytic, where no row of `v V` vanishes (Lemma D.10). -/
private theorem analyticAt_scaledLHSRGP (A : Arch T d L) (hε : 0 < ε) (hχ : A.χ = rmsNorm ε)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (θ η : Params A dIn dOut) (k : Fin L)
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {a : X → ℝ}
    {b c : X → Matrix T (A.w k) ℝ} {x₀ : X} (ha : AnalyticAt ℝ a x₀) (hb : AnalyticAt ℝ b x₀)
    (hc : AnalyticAt ℝ c x₀) (hb₀ : ∀ τ, (b x₀ * θ.write k) τ ≠ 0) :
    AnalyticAt ℝ (fun x => scaledLHS A ε θ η k (a x) (b x) (c x)) x₀ := by
  have hbV : AnalyticAt ℝ (fun x => b x * θ.write k) x₀ := analyticAt_matMulRGP hb analyticAt_const
  have hdir : AnalyticAt ℝ (fun x => c x * θ.write k + a x ^ 2 • (b x * η.write k)) x₀ :=
    (analyticAt_matMulRGP hc analyticAt_const).fun_add
      ((ha.fun_pow 2).fun_smul (analyticAt_matMulRGP hb analyticAt_const))
  have h1 := analyticAt_fderiv_scaledSuffixRGP A hε hχ hf 2 θ k.succ ha hbV hdir hb₀
  have h2 := analyticAt_fderiv_params_scaledSuffixRGP A hε hχ hf 2 θ η k.succ ha hbV hb₀
  have h3 := h1.fun_add ((ha.fun_pow 2).fun_smul h2)
  exact h3

/-! ### Gated blocks on a ray -/

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper, equation (24) on a ray: with `u = |g| > 0`, `σ(t g) = t W° − δ(t u)` and
`σ'(t g) = 1_A − s δ'(t u)`, where `W° = g`, `1_A = 1`, `s = 1` if `g > 0` and `W° = 0`, `1_A = 0`,
`s = −1` if `g < 0`. -/
private theorem gate_on_rayRGP (hg : GateFar σ σ' p) {g : ℝ} (hg0 : g ≠ 0) (t : ℝ) :
    σ (t * g) = t * (if 0 < g then g else 0) - (t * |g| - σ (t * |g|)) ∧
      σ' (t * g) = (if 0 < g then 1 else 0) - (if 0 < g then 1 else -1) * (1 - σ' (t * |g|)) := by
  by_cases hpos : 0 < g
  · rw [abs_of_pos hpos]
    simp only [hpos, ↓reduceIte]
    constructor <;> ring
  · have hneg : g < 0 := lt_of_le_of_ne (not_lt.1 hpos) hg0
    rw [abs_of_neg hneg]
    simp only [hpos, ↓reduceIte]
    have e : t * g = -(t * -g) := by ring
    obtain ⟨h1, h2⟩ := hg.neg (t * -g)
    rw [e, h1, h2]
    constructor <;> ring

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper, equation (25) on a ray: for `t ≥ 1` and `t u ≥ 2`, the small term `ζ = δ(t u)/t` lies
between `e^{−r t^p}` divided and multiplied by `A t²`, and `|ν| = |t δ'(t u)/δ(t u)| ≤ A t²`, with
`r = u^p/p` and `A = 6 + 4 U` for any `U ≥ u`. -/
private theorem ray_boundsRGP (hg : GateFar σ σ' p) {u U t : ℝ} (hu : 0 < u) (huU : u ≤ U)
    (ht1 : 1 ≤ t) (ht : 2 / u ≤ t) :
    Real.exp (-(u ^ p / p * t ^ p)) ≤ (6 + 4 * U) * t ^ 2 * ((t * u - σ (t * u)) / t) ∧
      |(t * u - σ (t * u)) / t| ≤ (6 + 4 * U) * t ^ 2 * Real.exp (-(u ^ p / p * t ^ p)) ∧
      |t * (1 - σ' (t * u)) / (t * u - σ (t * u))| ≤ (6 + 4 * U) * t ^ 2 ∧
      0 < t * u - σ (t * u) := by
  have ht0 : 0 < t := by linarith
  have hy : 2 ≤ t * u := by rwa [div_le_iff₀ hu] at ht
  obtain ⟨hlo, hup, hd'⟩ := hg.gap (t * u) hy
  have hE : (t * u) ^ p / (p : ℝ) = u ^ p / p * t ^ p := by rw [mul_pow]; ring
  rw [hE] at hlo hup
  obtain ⟨E, hEdef⟩ : ∃ E, E = Real.exp (-(u ^ p / p * t ^ p)) := ⟨_, rfl⟩
  rw [← hEdef] at hlo hup ⊢
  have hEpos : 0 < E := by rw [hEdef]; exact Real.exp_pos _
  obtain ⟨δ, hδdef⟩ : ∃ δ, δ = t * u - σ (t * u) := ⟨_, rfl⟩
  rw [← hδdef] at hlo hup hd' ⊢
  have hδ : 0 < δ := lt_of_lt_of_le (by positivity) hlo
  have hU : 0 ≤ U := le_trans hu.le huU
  have ht2 : t ≤ t ^ 2 := by nlinarith
  have ht21 : 1 ≤ t ^ 2 := by nlinarith
  have hζ0 : 0 ≤ δ / t := div_nonneg hδ.le ht0.le
  refine ⟨?_, ?_, ?_, hδ⟩
  · -- `E ≤ 6 δ = 6 t (δ/t) ≤ (6 + 4U) t² (δ/t)`
    have e2 : 6 * δ = 6 * t * (δ / t) := by field_simp
    have e3 : 6 * t ≤ (6 + 4 * U) * t ^ 2 := by nlinarith
    calc E ≤ 6 * t * (δ / t) := by linarith
      _ ≤ (6 + 4 * U) * t ^ 2 * (δ / t) := mul_le_mul_of_nonneg_right e3 hζ0
  · -- `δ/t ≤ u E ≤ (6 + 4U) t² E`
    rw [abs_of_nonneg hζ0, div_le_iff₀ ht0]
    have e3 : u * t ≤ (6 + 4 * U) * t ^ 2 * t := by
      have h1 : u ≤ 6 + 4 * U := by linarith
      have h2 : t ≤ t ^ 2 * t := by nlinarith
      calc u * t ≤ (6 + 4 * U) * t := mul_le_mul_of_nonneg_right h1 ht0.le
        _ ≤ (6 + 4 * U) * (t ^ 2 * t) := mul_le_mul_of_nonneg_left h2 (by linarith)
        _ = (6 + 4 * U) * t ^ 2 * t := by ring
    calc δ ≤ t * u * E := hup
      _ = u * t * E := by ring
      _ ≤ (6 + 4 * U) * t ^ 2 * t * E := mul_le_mul_of_nonneg_right e3 hEpos.le
      _ = (6 + 4 * U) * t ^ 2 * E * t := by ring
  · -- `t |δ'|/δ ≤ 4 u t² ≤ (6 + 4U) t²`
    rw [abs_div, abs_mul, abs_of_pos ht0, abs_of_pos hδ, div_le_iff₀ hδ]
    have e3 : t * (4 * (t * u) * δ) ≤ (6 + 4 * U) * t ^ 2 * δ := by
      have : 4 * u ≤ 6 + 4 * U := by linarith
      have h' : t * (4 * (t * u) * δ) = (4 * u) * t ^ 2 * δ := by ring
      rw [h']
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right this (by positivity)) hδ.le
    calc t * |1 - σ' (t * u)| ≤ t * (4 * (t * u) * δ) := mul_le_mul_of_nonneg_left hd' ht0.le
      _ ≤ (6 + 4 * U) * t ^ 2 * δ := e3

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: `M V = ∑_{i j} M_{i j} (E_{i j} V)`, with the matrix units `E_{i j}`. -/
private theorem mul_eq_sum_singleRGP {m n q : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] (M : Matrix m n ℝ) (V : Matrix n q ℝ) :
    M * V = ∑ i, ∑ j, M i j • (Matrix.single i j (1 : ℝ) * V) := by
  have h : M * V = (∑ i, ∑ j, Matrix.single i j (M i j)) * V := by
    rw [← Matrix.matrix_eq_sum_single M]
  rw [h, Matrix.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Matrix.smul_mul, Matrix.smul_single, smul_eq_mul, mul_one]

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: if `a + s² b = 0` for all `s ≠ 0` near `0`, then `a = 0` and `b = 0`. -/
private theorem eq_zero_of_eventually_add_sq_mulRGP {a b : ℝ}
    (h : ∀ᶠ s in 𝓝[≠] (0 : ℝ), a + s ^ 2 * b = 0) : a = 0 ∧ b = 0 := by
  have hc : Continuous fun s : ℝ => a + s ^ 2 * b := by fun_prop
  have h1 : Tendsto (fun s : ℝ => a + s ^ 2 * b) (𝓝[≠] 0) (𝓝 (a + 0 ^ 2 * b)) :=
    (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have h2 : Tendsto (fun s : ℝ => a + s ^ 2 * b) (𝓝[≠] 0) (𝓝 0) :=
    tendsto_const_nhds.congr' (h.mono fun s hs => hs.symm)
  have ha : a = 0 := by
    have := tendsto_nhds_unique h1 h2
    simpa using this
  obtain ⟨s, hs, hs0⟩ := (h.and self_mem_nhdsWithin).exists
  refine ⟨ha, ?_⟩
  rw [ha, zero_add] at hs
  exact (mul_eq_zero.1 hs).resolve_left (pow_ne_zero 2 (Set.mem_compl_singleton_iff.1 hs0))

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (the end of the step "one small factor"): if `β` is analytic on `ℝ` with `β(1) ≠ 0`, and
`c (a + s² b) β(s) = 0` for all `s` near `0`, with `c ≠ 0`, then `a = 0` and `b = 0`: `β` vanishes
only at isolated points. -/
private theorem coeff_eq_zero_of_smulRGP {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {β : ℝ → E} (hβ : AnalyticOnNhd ℝ β Set.univ) (hβ1 : β 1 ≠ 0) {c a b : ℝ} (hc : c ≠ 0)
    (h : ∀ᶠ s in 𝓝 (0 : ℝ), (c * (a + s ^ 2 * b)) • β s = 0) : a = 0 ∧ b = 0 := by
  refine eq_zero_of_eventually_add_sq_mulRGP ?_
  -- `β` does not vanish near `0`, except perhaps at `0` (identity theorem on `ℝ`)
  have hne : ∀ᶠ s in 𝓝[≠] (0 : ℝ), β s ≠ 0 := by
    rcases (hβ 0 (Set.mem_univ _)).eventually_eq_zero_or_eventually_ne_zero with h0 | h0
    · exfalso
      exact hβ1 (hβ.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
        (Set.mem_univ 0) h0 (Set.mem_univ 1))
    · exact h0
  filter_upwards [hne, nhdsWithin_le_nhds h] with s hs1 hs2
  rcases smul_eq_zero.1 hs2 with h3 | h3
  · exact (mul_eq_zero.1 h3).resolve_left hc
  · exact absurd h3 hs1

omit [Fintype T] [DecidableEq d] in
/-- Helper, equation (26) in the case (+) on a ray: what the hidden units read changes along the
ray `n = t Ξ` as `ż(t Ξ) = t P₁ + t³ P₃`, with `P₁ = Ξ Z W + Ξ η_W` and `P₃` with the rows
`−(⟨(Ξ Z)_τ, Ξ_τ⟩ / d) (Ξ W)_τ`. -/
private theorem ray_formulaRGP (Z : Matrix d d ℝ) (Ξ : Matrix T d ℝ) {r : Type*} [Fintype r]
    (W Wη : Matrix d r ℝ) (t : ℝ) :
    tangentRMS Z (t • Ξ) * W + (t • Ξ) * Wη = t • (Ξ * Z * W + Ξ * Wη)
      + t ^ 3 • (Matrix.of fun τ c => -((Ξ * Z) τ ⬝ᵥ Ξ τ / (Fintype.card d : ℝ)) * (Ξ * W) τ c) := by
  have hrow : ∀ (c : ℝ) (N : Matrix T d ℝ) (τ : T), (c • N) τ = c • N τ := fun _ _ _ => rfl
  have hT : tangentRMS Z (t • Ξ) = t • (Ξ * Z) - t ^ 3 • Matrix.of fun τ =>
      ((Ξ * Z) τ ⬝ᵥ Ξ τ / (Fintype.card d : ℝ)) • Ξ τ := by
    ext τ i
    simp only [tangentRMS, Matrix.smul_mul, hrow, smul_dotProduct, dotProduct_smul,
      Matrix.of_apply, Matrix.sub_apply, Matrix.smul_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul]
    ring
  have hNW : (Matrix.of fun τ => ((Ξ * Z) τ ⬝ᵥ Ξ τ / (Fintype.card d : ℝ)) • Ξ τ) * W
      = Matrix.of fun τ c => ((Ξ * Z) τ ⬝ᵥ Ξ τ / (Fintype.card d : ℝ)) * (Ξ * W) τ c := by
    ext τ c
    simp only [Matrix.mul_apply, Matrix.of_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
      mul_assoc]
  rw [hT, Matrix.sub_mul, Matrix.smul_mul, Matrix.smul_mul, hNW, Matrix.smul_mul]
  ext τ c
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul,
    Matrix.mul_assoc]
  ring

/-- The outputs of the hidden units on a ray, divided by `t²`: `v₁(y) = (W° − y) ⊙ ι`, where `M`
holds the gates (`Sum.inl`) and the values `ι` (`Sum.inr`) of `Ξ W`, and `W°` is the gate where it is
positive and `0` otherwise. -/
private noncomputable def rayV {q : Type*} (M : Matrix T (q ⊕ q) ℝ) (y : Matrix T q ℝ) :
    Matrix T q ℝ :=
  Matrix.of fun τ j =>
    ((if 0 < M τ (Sum.inl j) then M τ (Sum.inl j) else 0) - y τ j) * M τ (Sum.inr j)

/-- Their derivative divided by `t⁴`, without the small terms of the gate derivatives:
`R(s, y) = 1_A ⊙ (P₃^g + s² P₁^g) ⊙ ι + (W° − y) ⊙ (P₃^v + s² P₁^v)`. -/
private noncomputable def rayR {q : Type*} (M P₁ P₃ : Matrix T (q ⊕ q) ℝ) (S : ℝ)
    (y : Matrix T q ℝ) : Matrix T q ℝ :=
  Matrix.of fun τ j =>
    (if 0 < M τ (Sum.inl j) then 1 else 0) * (P₃ τ (Sum.inl j) + S ^ 2 * P₁ τ (Sum.inl j))
        * M τ (Sum.inr j)
      + ((if 0 < M τ (Sum.inl j) then M τ (Sum.inl j) else 0) - y τ j)
        * (P₃ τ (Sum.inr j) + S ^ 2 * P₁ τ (Sum.inr j))

/-- The coefficient of the small term `δ'_{τ j}` of a gate derivative:
`−s_j ι_{τ j} (P₃^g + s² P₁^g)_{τ j}`. -/
private noncomputable def rayCoef {q : Type*} (M P₁ P₃ : Matrix T (q ⊕ q) ℝ) (τ : T) (j : q)
    (S : ℝ) : ℝ :=
  (-(if 0 < M τ (Sum.inl j) then 1 else -1) * M τ (Sum.inr j))
    * (P₃ τ (Sum.inl j) + S ^ 2 * P₁ τ (Sum.inl j))

/-- The small terms `ζ_{τ j}(t) = δ(t u_{τ j})/t`, `u_{τ j} = |g_{τ j}|`. -/
private noncomputable def rayζ (σ : ℝ → ℝ) {q : Type*} (M : Matrix T (q ⊕ q) ℝ) (t : ℝ) :
    Matrix T q ℝ :=
  Matrix.of fun τ j => (t * |M τ (Sum.inl j)| - σ (t * |M τ (Sum.inl j)|)) / t

/-- The factors `ν_{τ j}(t) = t δ'(t u_{τ j})/δ(t u_{τ j})`. -/
private noncomputable def rayν (σ σ' : ℝ → ℝ) {q : Type*} (M : Matrix T (q ⊕ q) ℝ) (t : ℝ) :
    Matrix T q ℝ :=
  Matrix.of fun τ j =>
    t * (1 - σ' (t * |M τ (Sum.inl j)|)) / (t * |M τ (Sum.inl j)| - σ (t * |M τ (Sum.inl j)|))

/-- The map `G₀(s, y) = Ψ(s, v₁(y), R(s, y))` of the induction (the coefficient-free part). -/
private noncomputable def rayG₀ (θ η : Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)
    (k : Fin L) (M P₁ P₃ : Matrix T (hid k ⊕ hid k) ℝ) (z : ℝ × Matrix T (hid k) ℝ) :
    Matrix T dOut ℝ :=
  scaledLHS (Arch.gated σ (rmsNorm ε) hid) ε θ η k z.1 (rayV M z.2) (rayR M P₁ P₃ z.1 z.2)

/-- The maps `G_{τ j}(s, y) = c_{τ j}(s) 𝐃_hΦ(s, v₁(y) V)(E_{τ j} V)` of the induction. -/
private noncomputable def rayG (θ : Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)
    (k : Fin L) [DecidableEq T] [DecidableEq (hid k)] (M P₁ P₃ : Matrix T (hid k ⊕ hid k) ℝ)
    (τ : T) (j : hid k) (z : ℝ × Matrix T (hid k) ℝ) : Matrix T dOut ℝ :=
  rayCoef M P₁ P₃ τ j z.1 • fderiv ℝ (fun h' : Matrix T d ℝ =>
      scaledSuffix (Arch.gated σ (rmsNorm ε) hid) ε 2 θ k.succ (z.1, h'))
    (rayV M z.2 * θ.write k) (Matrix.single τ j (1 : ℝ) * θ.write k)

/-- Helper: **the expansion on a ray** (equations (33), (34)): for `t > 0` where no `δ(t u)`
vanishes, the left side of (28) at `n = t Ξ` is
`t² (G₀(1/t, ζ(t)) + ∑_{τ j} ν_{τ j}(t) ζ_{τ j}(t) G_{τ j}(1/t, ζ(t)))`. -/
private theorem blockLHS_ray_expansionRGP (hε : 0 < ε) (hg : GateFar σ σ' p)
    (θ η : Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut) (k : Fin L)
    [DecidableEq T] [DecidableEq (hid k)] (M P₁ P₃ : Matrix T (hid k ⊕ hid k) ℝ)
    (hM : ∀ τ j, M τ (Sum.inl j) ≠ 0) {t : ℝ} (ht : 0 < t)
    (hδ : ∀ τ j, t * |M τ (Sum.inl j)| - σ (t * |M τ (Sum.inl j)|) ≠ 0) :
    blockLHSGated θ k η (Matrix.of fun τ j => σ ((t • M) τ (Sum.inl j)))
        (Matrix.of fun τ j => σ' ((t • M) τ (Sum.inl j))) (t • M) (t • P₁ + t ^ 3 • P₃)
      = t ^ 2 • (rayG₀ θ η k M P₁ P₃ (1 / t, rayζ σ M t)
          + ∑ τ, ∑ j, (rayν σ σ' M t τ j * rayζ σ M t τ j)
            • rayG θ k M P₁ P₃ τ j (1 / t, rayζ σ M t)) := by
  have hf : ∀ ℓ, AnalyticOnNhd ℝ ((Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid).f ℓ) Set.univ :=
    fun ℓ => analyticOnNhd_f_gated hg.analytic ℓ
  have ht' := ht.ne'
  rw [blockLHSGated_eq_writeLHS]
  -- the outputs of the hidden units are `t² v₁(ζ)`
  have hv : (Matrix.of fun τ j => (Matrix.of fun τ j => σ ((t • M) τ (Sum.inl j))) τ j
      * (t • M) τ (Sum.inr j)) = t ^ 2 • rayV M (rayζ σ M t) := by
    ext τ j
    obtain ⟨h1, -⟩ := gate_on_rayRGP hg (hM τ j) t
    simp only [Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, rayV, rayζ]
    rw [h1]
    field_simp
  -- their derivative is `t⁴ (R(1/t, ζ) + X)`, with `X_{τ j} = ν ζ c_{τ j}(1/t)`
  have hvd : (Matrix.of fun τ j => (Matrix.of fun τ j => σ' ((t • M) τ (Sum.inl j))) τ j
        * (t • P₁ + t ^ 3 • P₃) τ (Sum.inl j) * (t • M) τ (Sum.inr j)
        + (Matrix.of fun τ j => σ ((t • M) τ (Sum.inl j))) τ j * (t • P₁ + t ^ 3 • P₃) τ (Sum.inr j))
      = t ^ 4 • (rayR M P₁ P₃ (1 / t) (rayζ σ M t) + Matrix.of fun τ j =>
          (rayν σ σ' M t τ j * rayζ σ M t τ j) * rayCoef M P₁ P₃ τ j (1 / t)) := by
    ext τ j
    obtain ⟨h1, h2⟩ := gate_on_rayRGP hg (hM τ j) t
    have hνζ : rayν σ σ' M t τ j * rayζ σ M t τ j = 1 - σ' (t * |M τ (Sum.inl j)|) := by
      simp only [rayν, rayζ, Matrix.of_apply]
      field_simp [hδ τ j]
    simp only [Matrix.of_apply, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
    rw [hνζ]
    simp only [rayR, rayCoef, rayζ, Matrix.of_apply]
    rw [h1, h2]
    field_simp
    ring
  rw [hv, hvd, writeLHS_pow_smulRGP _ hε rfl hf θ η k ht, scaledLHS_addRGP,
    mul_eq_sum_singleRGP (Matrix.of fun τ j => rayν σ σ' M t τ j * rayζ σ M t τ j
      * rayCoef M P₁ P₃ τ j (1 / t)) (θ.write k), map_sum]
  congr 2
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, Matrix.of_apply, rayG, smul_smul]

omit [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: `(s, y) ↦ v₁(y)` is analytic (affine). -/
private theorem analyticAt_rayVRGP {q : Type*} [Fintype q] (M : Matrix T (q ⊕ q) ℝ)
    (z₀ : ℝ × Matrix T q ℝ) : AnalyticAt ℝ (fun z : ℝ × Matrix T q ℝ => rayV M z.2) z₀ := by
  unfold rayV
  refine analyticAt_matrixOfRGP fun τ j => ?_
  exact (analyticAt_const.fun_sub (analyticAt_entryRGP analyticAt_snd τ j)).fun_mul analyticAt_const

omit [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: `(s, y) ↦ R(s, y)` is analytic (polynomial). -/
private theorem analyticAt_rayRRGP {q : Type*} [Fintype q] (M P₁ P₃ : Matrix T (q ⊕ q) ℝ)
    (z₀ : ℝ × Matrix T q ℝ) :
    AnalyticAt ℝ (fun z : ℝ × Matrix T q ℝ => rayR M P₁ P₃ z.1 z.2) z₀ := by
  unfold rayR
  refine analyticAt_matrixOfRGP fun τ j => ?_
  exact ((analyticAt_const.fun_mul (analyticAt_const.fun_add
    ((analyticAt_fst.fun_pow 2).fun_mul analyticAt_const))).fun_mul analyticAt_const).fun_add
    ((analyticAt_const.fun_sub (analyticAt_entryRGP analyticAt_snd τ j)).fun_mul
      (analyticAt_const.fun_add ((analyticAt_fst.fun_pow 2).fun_mul analyticAt_const)))

/-- Helper: `G₀` is analytic at `(0, 0)` when no row of `v₁(0) V` vanishes (fact (a)). -/
private theorem analyticAt_rayG₀RGP (hε : 0 < ε) (hg : GateFar σ σ' p)
    (θ η : Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut) (k : Fin L)
    (M P₁ P₃ : Matrix T (hid k ⊕ hid k) ℝ) (h0 : ∀ τ, (rayV M 0 * θ.write k) τ ≠ 0) :
    AnalyticAt ℝ (rayG₀ θ η k M P₁ P₃) 0 := by
  have hf : ∀ ℓ, AnalyticOnNhd ℝ ((Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid).f ℓ) Set.univ :=
    fun ℓ => analyticOnNhd_f_gated hg.analytic ℓ
  have h := analyticAt_scaledLHSRGP (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) hε rfl hf θ η k
    (a := fun z : ℝ × Matrix T (hid k) ℝ => z.1) (b := fun z => rayV M z.2)
    (c := fun z => rayR M P₁ P₃ z.1 z.2) (x₀ := 0) analyticAt_fst (analyticAt_rayVRGP M 0)
    (analyticAt_rayRRGP M P₁ P₃ 0) h0
  exact h

/-- Helper: every `G_{τ j}` is analytic at `(0, 0)` when no row of `v₁(0) V` vanishes. -/
private theorem analyticAt_rayGRGP (hε : 0 < ε) (hg : GateFar σ σ' p)
    (θ : Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut) (k : Fin L)
    [DecidableEq T] [DecidableEq (hid k)] (M P₁ P₃ : Matrix T (hid k ⊕ hid k) ℝ) (τ : T)
    (j : hid k) (h0 : ∀ τ, (rayV M 0 * θ.write k) τ ≠ 0) :
    AnalyticAt ℝ (rayG θ k M P₁ P₃ τ j) 0 := by
  have hf : ∀ ℓ, AnalyticOnNhd ℝ ((Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid).f ℓ) Set.univ :=
    fun ℓ => analyticOnNhd_f_gated hg.analytic ℓ
  have h1 : AnalyticAt ℝ (fun z : ℝ × Matrix T (hid k) ℝ => rayCoef M P₁ P₃ τ j z.1) 0 := by
    unfold rayCoef
    exact analyticAt_const.fun_mul (analyticAt_const.fun_add
      ((analyticAt_fst.fun_pow 2).fun_mul analyticAt_const))
  have h2 := analyticAt_fderiv_scaledSuffixRGP (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) hε
    rfl hf 2 θ k.succ (a := fun z : ℝ × Matrix T (hid k) ℝ => z.1)
    (b := fun z => rayV M z.2 * θ.write k) (c := fun _ => Matrix.single τ j (1 : ℝ) * θ.write k)
    (x₀ := 0) analyticAt_fst (analyticAt_matMulRGP (analyticAt_rayVRGP M 0) analyticAt_const)
    analyticAt_const h0
  have h3 := h1.fun_smul h2
  exact h3

/-- Helper: `G₀` is even in `s` (equation (30) in the variable `s = 1/t`). -/
private theorem rayG₀_negRGP
    (θ η : Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut) (k : Fin L)
    (M P₁ P₃ : Matrix T (hid k ⊕ hid k) ℝ) (S : ℝ) (y : Matrix T (hid k) ℝ) :
    rayG₀ θ η k M P₁ P₃ (-S, y) = rayG₀ θ η k M P₁ P₃ (S, y) := by
  show scaledLHS _ ε θ η k (-S) (rayV M y) (rayR M P₁ P₃ (-S) y)
    = scaledLHS _ ε θ η k S (rayV M y) (rayR M P₁ P₃ S y)
  rw [scaledLHS_negRGP]
  unfold rayR
  simp only [neg_sq]

/-- Helper: every `G_{τ j}` is even in `s`. -/
private theorem rayG_negRGP
    (θ : Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut) (k : Fin L)
    [DecidableEq T] [DecidableEq (hid k)] (M P₁ P₃ : Matrix T (hid k ⊕ hid k) ℝ) (τ : T)
    (j : hid k) (S : ℝ) (y : Matrix T (hid k) ℝ) :
    rayG θ k M P₁ P₃ τ j (-S, y) = rayG θ k M P₁ P₃ τ j (S, y) := by
  have h : (fun h' : Matrix T d ℝ =>
      scaledSuffix (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) ε 2 θ k.succ (-S, h'))
      = fun h' => scaledSuffix (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) ε 2 θ k.succ (S, h') :=
    funext fun h' => scaledSuffix_neg _ 2 θ k.succ S h'
  show rayCoef M P₁ P₃ τ j (-S) • fderiv ℝ (fun h' : Matrix T d ℝ =>
      scaledSuffix (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) ε 2 θ k.succ (-S, h'))
      (rayV M y * θ.write k) (Matrix.single τ j (1 : ℝ) * θ.write k)
    = rayCoef M P₁ P₃ τ j S • fderiv ℝ (fun h' : Matrix T d ℝ =>
      scaledSuffix (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) ε 2 θ k.succ (S, h'))
      (rayV M y * θ.write k) (Matrix.single τ j (1 : ℝ) * θ.write k)
  rw [h]
  unfold rayCoef
  rw [neg_sq]

/-- **Lemma D.12 up to (38), on one generic ray, gated blocks, case (+).** Let `θ` be good for the
cones, let `Z` and `η` satisfy (16) for `k`, and let `Ξ` have its rows in `C_k` and satisfy (i),
(ii), (iii). Then `ż^g(Ξ) = 0`, and the second part of (38) holds at `n = Ξ` for every `w̃`. -/
theorem flat_at_generic_ray_gated_rmsNorm (hε : 0 < ε) (hg : GateFar σ σ' p)
    (hone : ∀ u : ℝ, 0 < u → ∀ a b : ℝ → Matrix T dOut ℝ, AnalyticAt ℝ a 0 → AnalyticAt ℝ b 0 →
      (∀ᶠ s in 𝓝 (0 : ℝ), a (-s) = a s ∧ b (-s) = b s) →
      FasterThanPowers (fun t : ℝ =>
        a (1 / t) + (t * (1 - σ' (t * u)) / (t * u - σ (t * u))) • b (1 / t)) →
      ∀ᶠ s in 𝓝 (0 : ℝ), b s = 0)
    {C : Fin (L + 1) → Set (d → ℝ)} {A : ∀ ℓ, Finset (hid ℓ)}
    {θ : Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut}
    (hθ : GoodForConesGated C A θ) (k : Fin L) (Z : Matrix d d ℝ)
    (η : Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)
    (hflat : SuffixFlat (Arch.gated σ (rmsNorm ε) hid) θ k.castSucc Z η)
    (Ξ : Matrix T d ℝ) (hΞ : ∀ t, Ξ t ∈ C k.castSucc)
    (hi : LinearIndependent ℚ (fun i : T × hid k => |(Ξ * θ.read k) i.1 (Sum.inl i.2)| ^ p))
    (hii : ∀ t j, (Ξ * θ.read k) t (Sum.inr j) ≠ 0)
    (hiii : Function.Injective
      (fderiv ℝ (fun h' : Matrix T d ℝ => suffix (Arch.gated σ (rmsNorm ε) hid) 0 θ k.succ h')
        (Matrix.of fun t => frozenGated θ k (A k) (Ξ t)))) :
    (∀ t j, (tangentRMS Z Ξ * θ.read k + Ξ * η.read k) t (Sum.inl j) = 0) ∧
      ∀ w : Matrix T (hid k) ℝ,
        writeLHS (Arch.gated σ (rmsNorm ε) hid) θ k η
          (Matrix.of fun t j => w t j * (Ξ * θ.read k) t (Sum.inr j))
          (Matrix.of fun t j =>
            w t j * (tangentRMS Z Ξ * θ.read k + Ξ * η.read k) t (Sum.inr j)) = 0 := by
  sorry

/-- **Lemma D.12 up to (38), gated blocks, case (+).** Let `θ` be good for the cones and regular,
and let the `Ξ` with (i) be dense. If `Z` and `η` satisfy (16) for `k`, then (38) holds for every
`n` with its rows in `C_k` and every `w̃`. -/
theorem flat_of_suffixFlat_gated_rmsNorm (hε : 0 < ε) (hg : GateFar σ σ' p)
    (hone : ∀ u : ℝ, 0 < u → ∀ a b : ℝ → Matrix T dOut ℝ, AnalyticAt ℝ a 0 → AnalyticAt ℝ b 0 →
      (∀ᶠ s in 𝓝 (0 : ℝ), a (-s) = a s ∧ b (-s) = b s) →
      FasterThanPowers (fun t : ℝ =>
        a (1 / t) + (t * (1 - σ' (t * u)) / (t * u - σ (t * u))) • b (1 / t)) →
      ∀ᶠ s in 𝓝 (0 : ℝ), b s = 0)
    {C : Fin (L + 1) → Set (d → ℝ)} {A : ∀ ℓ, Finset (hid ℓ)}
    {θ : Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut}
    (hθ : GoodForConesGated C A θ) (hreg : Regular (Arch.gated σ (rmsNorm ε) hid) θ) (k : Fin L)
    (hdense : Dense {Ξ : Matrix T d ℝ |
      LinearIndependent ℚ (fun i : T × hid k => |(Ξ * θ.read k) i.1 (Sum.inl i.2)| ^ p)})
    (Z : Matrix d d ℝ) (η : Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)
    (hflat : SuffixFlat (Arch.gated σ (rmsNorm ε) hid) θ k.castSucc Z η) :
    ∀ n : Matrix T d ℝ, (∀ t, n t ∈ C k.castSucc) →
      (∀ t j, (tangentRMS Z n * θ.read k + n * η.read k) t (Sum.inl j) = 0) ∧
      ∀ w : Matrix T (hid k) ℝ,
        writeLHS (Arch.gated σ (rmsNorm ε) hid) θ k η
          (Matrix.of fun t j => w t j * (n * θ.read k) t (Sum.inr j))
          (Matrix.of fun t j =>
            w t j * (tangentRMS Z n * θ.read k + n * η.read k) t (Sum.inr j)) = 0 := by
  sorry

/-- **Lemma D.12 up to (38), SwiGLU blocks, case (+):** with the gate columns of block `k`
linearly independent over `ℚ`. -/
theorem flat_of_suffixFlat_swiglu_rmsNorm (hε : 0 < ε) {C : Fin (L + 1) → Set (d → ℝ)}
    {A : ∀ ℓ, Finset (hid ℓ)}
    {θ : Params (Arch.gated (T := T) (d := d) silu (rmsNorm ε) hid) dIn dOut}
    (hθ : GoodForConesGated C A θ) (k : Fin L)
    (hQ : LinearIndependent ℚ (fun j : hid k => (θ.read k)ᵀ (Sum.inl j)))
    (Z : Matrix d d ℝ) (η : Params (Arch.gated (T := T) (d := d) silu (rmsNorm ε) hid) dIn dOut)
    (hflat : SuffixFlat (Arch.gated silu (rmsNorm ε) hid) θ k.castSucc Z η) :
    ∀ n : Matrix T d ℝ, (∀ t, n t ∈ C k.castSucc) →
      (∀ t j, (tangentRMS Z n * θ.read k + n * η.read k) t (Sum.inl j) = 0) ∧
      ∀ w : Matrix T (hid k) ℝ,
        writeLHS (Arch.gated silu (rmsNorm ε) hid) θ k η
          (Matrix.of fun t j => w t j * (n * θ.read k) t (Sum.inr j))
          (Matrix.of fun t j =>
            w t j * (tangentRMS Z n * θ.read k + n * η.read k) t (Sum.inr j)) = 0 := by
  sorry

/-- **Lemma D.12 up to (38), GeGLU blocks, case (+):** with the matrices `c_j c_j^⊤` of the gate
columns of block `k` linearly independent over `ℚ`. -/
theorem flat_of_suffixFlat_geglu_rmsNorm (hε : 0 < ε) {C : Fin (L + 1) → Set (d → ℝ)}
    {A : ∀ ℓ, Finset (hid ℓ)}
    {θ : Params (Arch.gated (T := T) (d := d) gelu (rmsNorm ε) hid) dIn dOut}
    (hθ : GoodForConesGated C A θ) (k : Fin L)
    (hQ : LinearIndependent ℚ (fun j : hid k =>
      Matrix.vecMulVec ((θ.read k)ᵀ (Sum.inl j)) ((θ.read k)ᵀ (Sum.inl j))))
    (Z : Matrix d d ℝ) (η : Params (Arch.gated (T := T) (d := d) gelu (rmsNorm ε) hid) dIn dOut)
    (hflat : SuffixFlat (Arch.gated gelu (rmsNorm ε) hid) θ k.castSucc Z η) :
    ∀ n : Matrix T d ℝ, (∀ t, n t ∈ C k.castSucc) →
      (∀ t j, (tangentRMS Z n * θ.read k + n * η.read k) t (Sum.inl j) = 0) ∧
      ∀ w : Matrix T (hid k) ℝ,
        writeLHS (Arch.gated gelu (rmsNorm ε) hid) θ k η
          (Matrix.of fun t j => w t j * (n * θ.read k) t (Sum.inr j))
          (Matrix.of fun t j =>
            w t j * (tangentRMS Z n * θ.read k + n * η.read k) t (Sum.inr j)) = 0 := by
  sorry

end Skips
