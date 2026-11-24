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

/-! ### Generic rays are dense -/

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (a copy of the private lemma of `Depth/Suffix.lean`): an analytic family `J` of linear
maps that is injective at one point `x₀` is injective on an open dense set that contains `x₀`. -/
private theorem exists_open_dense_injective_of_analyticRGP
    {X E F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {J : X → E →L[ℝ] F} (hJ : AnalyticOnNhd ℝ J Set.univ) {x₀ : X}
    (h₀ : Function.Injective (J x₀)) :
    ∃ U : Set X, IsOpen U ∧ Dense U ∧ x₀ ∈ U ∧ ∀ x ∈ U, Function.Injective (J x) := by
  obtain ⟨K, hK⟩ :=
    (J x₀ : E →ₗ[ℝ] F).exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 h₀)
  let b := Module.finBasis ℝ E
  let Ψ : (E →L[ℝ] F) →ₗ[ℝ]
      Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
    (LinearMap.toMatrix b b).toLinearMap ∘ₗ (LinearMap.llcomp ℝ E F E K) ∘ₗ
      (ContinuousLinearMap.coeLM ℝ)
  have hΨ : ∀ x, Ψ (J x) = LinearMap.toMatrix b b (K ∘ₗ (J x : E →ₗ[ℝ] F)) := fun x => rfl
  let φ : X → ℝ := fun x => (Ψ (J x)).det
  have hentry : ∀ i j, AnalyticOnNhd ℝ (fun x => Ψ (J x) i j) Set.univ := fun i j =>
    ((LinearMap.toContinuousLinearMap ((Matrix.entryLinearMap ℝ ℝ i j) ∘ₗ Ψ)).analyticOnNhd
      _).comp hJ (Set.mapsTo_univ _ _)
  have hφ : AnalyticOnNhd ℝ φ Set.univ := by
    show AnalyticOnNhd ℝ (fun x => (Ψ (J x)).det) Set.univ
    simp only [Matrix.det_apply']
    exact Finset.analyticOnNhd_fun_sum _ fun σ _ => analyticOnNhd_const.mul
      (Finset.analyticOnNhd_fun_prod _ fun i _ => hentry (σ i) i)
  have hφcont : Continuous φ := continuousOn_univ.mp hφ.continuousOn
  have hφ₀ : φ x₀ = 1 := by
    show (Ψ (J x₀)).det = 1
    rw [hΨ, hK, LinearMap.toMatrix_id, Matrix.det_one]
  have hφinj : ∀ x, φ x ≠ 0 → Function.Injective (J x) := by
    intro x hx
    have hdet : LinearMap.det (K ∘ₗ (J x : E →ₗ[ℝ] F)) ≠ 0 := by
      rw [← LinearMap.det_toMatrix b]
      exact hx
    have hbij := (Module.End.isUnit_iff _).1
      ((LinearMap.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hdet))
    have hinj := hbij.1
    rw [LinearMap.coe_comp] at hinj
    exact hinj.of_comp
  refine ⟨{x | φ x ≠ 0}, isOpen_ne_fun hφcont continuous_const, ?_, ?_, hφinj⟩
  · rw [dense_iff_inter_open]
    rintro W hW ⟨z, hz⟩
    by_contra hne
    have hzero : φ =ᶠ[𝓝 z] 0 := Filter.eventually_of_mem (hW.mem_nhds hz) fun y hy => by
      by_contra hy'
      exact hne ⟨y, hy, hy'⟩
    have h1 := hφ.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
      (Set.mem_univ z) hzero (Set.mem_univ x₀)
    rw [hφ₀] at h1
    exact one_ne_zero h1
  · show φ x₀ ≠ 0
    rw [hφ₀]
    exact one_ne_zero

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper, condition (iii): let `G` be an analytic map of a finite-dimensional space to itself with
an injective derivative at some point, and let `B` be analytic with an injective derivative on an
open dense set. Then `𝐃B(G x)` is injective for all `x` in an open dense set. (By the inverse
function theorem the image of `G` meets the open dense set, so `𝐃(B ∘ G)` is injective somewhere,
hence on an open dense set; there `𝐃G(x)` is injective, hence onto, so `𝐃B(G x)` is injective.) -/
private theorem exists_open_dense_injective_fderiv_compRGP {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] {G : E → E} {B : E → F} (hG : AnalyticOnNhd ℝ G Set.univ)
    (hB : AnalyticOnNhd ℝ B Set.univ) {x₁ : E} (hx₁ : Function.Injective (fderiv ℝ G x₁))
    {U : Set E} (hUd : Dense U) (hU : ∀ h ∈ U, Function.Injective (fderiv ℝ B h)) :
    ∃ U₃ : Set E, IsOpen U₃ ∧ Dense U₃ ∧ ∀ x ∈ U₃, Function.Injective (fderiv ℝ B (G x)) := by
  -- an open set `V ∋ x₁` on which `𝐃G` is injective
  obtain ⟨V, hVo, -, hx₁V, hV⟩ := exists_open_dense_injective_of_analyticRGP hG.fderiv hx₁
  -- inverse function theorem: `G(V)` is a neighbourhood of `G x₁`
  let e := (LinearEquiv.ofInjectiveEndo (fderiv ℝ G x₁ : E →ₗ[ℝ] E) hx₁).toContinuousLinearEquiv
  have hs : HasStrictFDerivAt G (e : E →L[ℝ] E) x₁ := by
    have he : (e : E →L[ℝ] E) = fderiv ℝ G x₁ := ContinuousLinearMap.ext fun v => rfl
    rw [he]
    exact (hG x₁ (Set.mem_univ _)).hasStrictFDerivAt
  have hnhds : G '' V ∈ 𝓝 (G x₁) := by
    have hm := Filter.image_mem_map (m := G) (hVo.mem_nhds hx₁V)
    rw [hs.map_nhds_eq_of_equiv] at hm
    exact hm
  -- it meets `U`: some `x₂ ∈ V` has `G x₂ ∈ U`, and there `𝐃(B ∘ G)` is injective
  obtain ⟨_, hyU, x₂, hx₂V, rfl⟩ := hUd.inter_nhds_nonempty hnhds
  have hcomp : ∀ x, fderiv ℝ (B ∘ G) x = (fderiv ℝ B (G x)).comp (fderiv ℝ G x) := fun x =>
    fderiv_comp x (hB _ (Set.mem_univ _)).differentiableAt (hG x (Set.mem_univ _)).differentiableAt
  have hinj₂ : Function.Injective (fderiv ℝ (B ∘ G) x₂) := by
    rw [hcomp, ContinuousLinearMap.coe_comp]
    exact (hU _ hyU).comp (hV x₂ hx₂V)
  -- so `𝐃(B ∘ G)` is injective on an open dense set `U₃`
  obtain ⟨U₃, hU₃o, hU₃d, -, hU₃⟩ := exists_open_dense_injective_of_analyticRGP
    (hB.comp hG (Set.mapsTo_univ _ _)).fderiv hinj₂
  refine ⟨U₃, hU₃o, hU₃d, fun x hx => ?_⟩
  have h := hU₃ x hx
  rw [hcomp, ContinuousLinearMap.coe_comp] at h
  -- `𝐃G(x)` is injective, hence onto (an endomorphism of a finite-dimensional space)
  have hGsurj : Function.Surjective (fderiv ℝ G x) :=
    (LinearMap.injective_iff_surjective (f := (fderiv ℝ G x : E →ₗ[ℝ] E))).1 h.of_comp
  intro a b hab
  obtain ⟨a', rfl⟩ := hGsurj a
  obtain ⟨b', rfl⟩ := hGsurj b
  exact congrArg _ (h hab)

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (as in `Depth/StepTanhRMS.lean`): the set where a nonzero additive and homogeneous
function `f` does not vanish is dense. -/
private theorem dense_setOf_ne_zero_of_linearRGP {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : E → ℝ) (hadd : ∀ x y, f (x + y) = f x + f y)
    (hsmul : ∀ (c : ℝ) x, f (c • x) = c * f x) {x₀ : E} (hx₀ : f x₀ ≠ 0) :
    Dense {x | f x ≠ 0} := by
  intro x
  by_cases hx : f x ≠ 0
  · exact subset_closure hx
  rw [not_not] at hx
  have ht : Filter.Tendsto (fun s : ℝ => x + s • x₀) (𝓝[≠] 0) (𝓝 x) := by
    have hc : Continuous (fun s : ℝ => x + s • x₀) :=
      continuous_const.add (continuous_id.smul continuous_const)
    have h0 := hc.tendsto 0
    rw [zero_smul, add_zero] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  refine mem_closure_of_tendsto ht (eventually_nhdsWithin_of_forall fun s hs => ?_)
  show f (x + s • x₀) ≠ 0
  rw [hadd, hsmul, hx, zero_add]
  exact mul_ne_zero hs hx₀

omit [Fintype T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (a copy of the private `analyticOnNhd_frozenGated` of `Depth/Cones.lean`): the frozen
gated block is a polynomial, hence analytic. -/
private theorem analyticOnNhd_frozenGatedRGP
    (θ : Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut) (ℓ : Fin L)
    (B : Finset (hid ℓ)) : AnalyticOnNhd ℝ (frozenGated θ ℓ B) Set.univ := by
  have hdot : ∀ c : d → ℝ, AnalyticOnNhd ℝ (fun v : d → ℝ => v ⬝ᵥ c) Set.univ := fun c =>
    (LinearMap.toContinuousLinearMap
      ({ toFun := fun v => v ⬝ᵥ c
         map_add' := fun v w => add_dotProduct v w c
         map_smul' := fun r v => smul_dotProduct r v c } : (d → ℝ) →ₗ[ℝ] ℝ)).analyticOnNhd _
  show AnalyticOnNhd ℝ (fun n => ∑ j ∈ B, ((n ⬝ᵥ (θ.read ℓ)ᵀ (Sum.inl j)) *
    (n ⬝ᵥ (θ.read ℓ)ᵀ (Sum.inr j))) • θ.write ℓ j) Set.univ
  refine Finset.analyticOnNhd_fun_sum _ fun j _ => ?_
  have h := ((hdot ((θ.read ℓ)ᵀ (Sum.inl j))).mul (hdot ((θ.read ℓ)ᵀ (Sum.inr j)))).smul
    (analyticOnNhd_const (v := θ.write ℓ j))
  exact h

omit [Fintype T] [DecidableEq d] in
/-- Helper (a copy of the private `injective_fderiv_rowwise` of `Depth/Cones.lean`): a map acting
row by row has, at the matrix all of whose rows are `x`, an injective derivative if the map of one
row has. -/
private theorem injective_fderiv_rowwiseRGP [Finite T] {g : (d → ℝ) → (d → ℝ)}
    {G : (d → ℝ) →L[ℝ] (d → ℝ)} {x : d → ℝ} (hg : HasFDerivAt g G x)
    (hG : Function.Injective G) :
    Function.Injective (fderiv ℝ (fun n : T → d → ℝ => fun t => g (n t)) (fun _ => x)) := by
  have : Fintype T := Fintype.ofFinite T
  have h : HasFDerivAt (fun n : T → d → ℝ => fun t => g (n t))
      (ContinuousLinearMap.pi fun t => G.comp (ContinuousLinearMap.proj t)) (fun _ => x) :=
    hasFDerivAt_pi.2 fun t =>
      hg.comp (fun _ : T => x) (hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : T => d → ℝ) t _)
  rw [h.fderiv]
  intro V W hVW
  funext t
  exact hG (congrFun hVW t)

omit [DecidableEq d] in
/-- Helper: `n ↦ n Z − ⟨n Z, n⟩ n / d` (equation (14)) is analytic (a polynomial). -/
private theorem analyticAt_tangentRMSRGP (Z : Matrix d d ℝ) (n₀ : Matrix T d ℝ) :
    AnalyticAt ℝ (tangentRMS (T := T) Z) n₀ := by
  have hZ : AnalyticAt ℝ (fun n : Matrix T d ℝ => n * Z) n₀ :=
    analyticAt_matMulRGP analyticAt_id analyticAt_const
  have hid' : AnalyticAt ℝ (fun n : Matrix T d ℝ => n) n₀ := analyticAt_id
  show AnalyticAt ℝ (fun n : Matrix T d ℝ => (Matrix.of fun t i =>
    (n * Z) t i - ((∑ l, (n * Z) t l * n t l) / (Fintype.card d : ℝ)) * n t i : Matrix T d ℝ)) n₀
  refine analyticAt_matrixOfRGP fun t i => ?_
  exact (analyticAt_entryRGP hZ t i).fun_sub (((Finset.analyticAt_fun_sum _ fun l _ =>
    (analyticAt_entryRGP hZ t l).fun_mul (analyticAt_entryRGP hid' t l)).div_const).fun_mul
      (analyticAt_entryRGP hid' t i))


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
  classical
  have hf : ∀ ℓ, AnalyticOnNhd ℝ ((Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid).f ℓ) Set.univ :=
    fun ℓ => analyticOnNhd_f_gated hg.analytic ℓ
  -- the gates (`Sum.inl`) and the values `ι` (`Sum.inr`) on the ray: `M = Ξ W`
  obtain ⟨M, hMdef⟩ : ∃ M, M = Ξ * θ.read k := ⟨_, rfl⟩
  have hMe : ∀ τ c, M τ c = Ξ τ ⬝ᵥ (θ.read k)ᵀ c := fun τ c => by rw [hMdef]; rfl
  -- (K1): the gate `g_{τ j}` is positive exactly for the active units, and never zero
  have hMA : ∀ τ j, (j ∈ A k ↔ 0 < M τ (Sum.inl j)) := by
    intro τ j
    rw [hMe]
    by_cases hj : j ∈ A k
    · exact ⟨fun _ => hθ.gate_pos k (Ξ τ) (hΞ τ) j hj, fun _ => hj⟩
    · exact ⟨fun h => absurd h hj,
        fun h => absurd h (not_lt.2 (hθ.gate_neg k (Ξ τ) (hΞ τ) j hj).le)⟩
  have hM0 : ∀ τ j, M τ (Sum.inl j) ≠ 0 := by
    intro τ j
    rw [hMe]
    by_cases hj : j ∈ A k
    · exact (hθ.gate_pos k (Ξ τ) (hΞ τ) j hj).ne'
    · exact (hθ.gate_neg k (Ξ τ) (hΞ τ) j hj).ne
  -- (ii)
  have hι : ∀ τ j, M τ (Sum.inr j) ≠ 0 := by rw [hMdef]; exact hii
  rw [← hMdef] at hi
  -- the frozen hidden state `v₁(0) V`, with the rows `g°(ξ_τ)` in `C_{k+1}`
  have hH : rayV M 0 * θ.write k = Matrix.of fun τ => frozenGated θ k (A k) (Ξ τ) := by
    ext τ i
    simp only [rayV, Matrix.mul_apply, Matrix.of_apply, Matrix.zero_apply, sub_zero, frozenGated,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ← hMe]
    rw [← Finset.univ_inter (A k), ← Finset.sum_ite_mem]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : j ∈ A k
    · simp only [hj, (hMA τ j).1 hj, ↓reduceIte]
    · have hn : ¬ 0 < M τ (Sum.inl j) := fun h => hj ((hMA τ j).2 h)
      simp only [hj, hn, ↓reduceIte, zero_mul]
  have hH0 : ∀ τ, (rayV M 0 * θ.write k) τ ≠ 0 := by
    intro τ h
    have hmem := hθ.frozen_mem k (Ξ τ) (hΞ τ)
    rw [hH] at h
    have h' : frozenGated θ k (A k) (Ξ τ) = 0 := h
    exact (hθ.cone k.succ).zero_notMem (h' ▸ hmem)
  -- what the hidden units read changes along the ray as `t P₁ + t³ P₃` (case (+))
  obtain ⟨P₁, P₃, hP⟩ : ∃ P₁ P₃ : Matrix T (hid k ⊕ hid k) ℝ, ∀ t : ℝ,
      tangentRMS Z (t • Ξ) * θ.read k + (t • Ξ) * η.read k = t • P₁ + t ^ 3 • P₃ :=
    ⟨_, _, ray_formulaRGP Z Ξ (θ.read k) (η.read k)⟩
  -- (28) on the ray, expanded: fact (b), the left side vanishes
  have h28 := (suffixFlat_castSucc_iff_gated_rmsNorm hε hg.hasDerivAt hg.analytic θ k Z η).1 hflat
  have hray : ∀ t : ℝ, 0 < t →
      (∀ τ j, t * |M τ (Sum.inl j)| - σ (t * |M τ (Sum.inl j)|) ≠ 0) →
      rayG₀ θ η k M P₁ P₃ (1 / t, rayζ σ M t) + ∑ τ, ∑ j, (rayν σ σ' M t τ j * rayζ σ M t τ j)
        • rayG θ k M P₁ P₃ τ j (1 / t, rayζ σ M t) = 0 := by
    intro t ht hδ
    have e := h28 (t • Ξ)
    rw [hP t, Matrix.smul_mul, ← hMdef, blockLHS_ray_expansionRGP hε hg θ η k M P₁ P₃ hM0 ht hδ] at e
    exact (smul_eq_zero.1 e).resolve_left (pow_ne_zero 2 ht.ne')
  -- `β(s) = 𝐃_hΦ(s, v₁(0) V)(E_{τ j} V)` is analytic on `ℝ`, and `β(1) = 𝐃𝓑(g°(Ξ))(E_{τ j} V) ≠ 0`
  have hβ : ∀ τ j, AnalyticOnNhd ℝ (fun S => fderiv ℝ (fun h' : Matrix T d ℝ =>
      scaledSuffix (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) ε 2 θ k.succ (S, h'))
      (rayV M 0 * θ.write k) (Matrix.single τ j (1 : ℝ) * θ.write k)) Set.univ :=
    fun τ j S _ => analyticAt_fderiv_scaledSuffixRGP _ hε rfl hf 2 θ k.succ (a := fun S => S)
      (b := fun _ => rayV M 0 * θ.write k) (c := fun _ => Matrix.single τ j (1 : ℝ) * θ.write k)
      analyticAt_id analyticAt_const analyticAt_const hH0
  have hβ1 : ∀ τ j, fderiv ℝ (fun h' : Matrix T d ℝ =>
      scaledSuffix (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) ε 2 θ k.succ (1, h'))
      (rayV M 0 * θ.write k) (Matrix.single τ j (1 : ℝ) * θ.write k) ≠ 0 := by
    intro τ j h
    have e := fderiv_suffix_pow_smul (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) hε rfl hf θ
      k.succ one_pos 2 (rayV M 0 * θ.write k) (Matrix.single τ j (1 : ℝ) * θ.write k)
    rw [one_pow, one_smul, div_one, one_pow, one_smul, h, hH] at e
    -- by (iii), `E_{τ j} V = 0`, but its row `τ` is `a_j ≠ 0`
    have hinj := hiii (e.trans (map_zero _).symm)
    refine hθ.write_ne_zero k j (funext fun i => ?_)
    have := congrFun (congrFun hinj τ) i
    simpa [Matrix.single_mul_apply_same] using this
  -- if `G_{τ j}(s, 0) = 0` near `0`, the gate coefficients `P₃^g`, `P₁^g` vanish at `(τ, j)`
  have hcoef : ∀ τ j, (∀ᶠ s in 𝓝 (0 : ℝ), rayG θ k M P₁ P₃ τ j (s, 0) = 0) →
      P₃ τ (Sum.inl j) = 0 ∧ P₁ τ (Sum.inl j) = 0 := by
    intro τ j h
    refine coeff_eq_zero_of_smulRGP (hβ τ j) (hβ1 τ j)
      (c := -(if 0 < M τ (Sum.inl j) then 1 else -1) * M τ (Sum.inr j)) ?_ h
    refine mul_ne_zero (neg_ne_zero.2 ?_) (hι τ j)
    split_ifs <;> norm_num
  have hGzero : ∀ τ j, P₃ τ (Sum.inl j) = 0 → P₁ τ (Sum.inl j) = 0 →
      ∀ z, rayG θ k M P₁ P₃ τ j z = 0 := by
    intro τ j h3 h1 z
    simp only [rayG, rayCoef, h3, h1, mul_zero, add_zero, zero_smul]
  -- the rates `r_{τ j} = u_{τ j}^p / p`, independent over `ℚ` by (i)
  have hp1 := hg.one_le
  have hrQ : LinearIndependent ℚ (fun i : T × hid k =>
      (Matrix.of fun τ j => |M τ (Sum.inl j)| ^ p / (p : ℝ) : Matrix T (hid k) ℝ) i.1 i.2) := by
    have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    have h := hi.units_smul (fun _ => Units.mk0 ((p : ℚ)⁻¹) (inv_ne_zero hp0))
    convert h using 1
    funext i
    simp only [Matrix.of_apply, Pi.smul_apply', Units.smul_def, Units.val_mk0, Rat.smul_def,
      Rat.cast_inv, Rat.cast_natCast]
    ring
  have hr : ∀ τ j, 0 < (Matrix.of fun τ j => |M τ (Sum.inl j)| ^ p / (p : ℝ) :
      Matrix T (hid k) ℝ) τ j := fun τ j =>
    div_pos (pow_pos (abs_pos.2 (hM0 τ j)) p) (Nat.cast_pos.2 (by omega))
  -- the bounds of the small terms (25), with `A = 6 + 4 U`
  obtain ⟨U, hU⟩ : ∃ U, U = ∑ τ, ∑ j, |M τ (Sum.inl j)| := ⟨_, rfl⟩
  have huU : ∀ τ j, |M τ (Sum.inl j)| ≤ U := fun τ j => by
    rw [hU]
    exact le_trans (Finset.single_le_sum (f := fun j => |M τ (Sum.inl j)|)
        (fun j _ => abs_nonneg _) (Finset.mem_univ j))
      (Finset.single_le_sum (f := fun τ => ∑ j, |M τ (Sum.inl j)|)
        (fun τ _ => Finset.sum_nonneg fun j _ => abs_nonneg _) (Finset.mem_univ τ))
  have hev : ∀ᶠ t in atTop, 1 ≤ t ∧ ∀ τ j, 2 / |M τ (Sum.inl j)| ≤ t :=
    (eventually_ge_atTop 1).and
      (eventually_all.2 fun τ => eventually_all.2 fun j => eventually_ge_atTop _)
  have hb : ∀ t, (1 ≤ t ∧ ∀ τ j, 2 / |M τ (Sum.inl j)| ≤ t) → ∀ τ j, _ := fun t ht τ j =>
    ray_boundsRGP hg (abs_pos.2 (hM0 τ j)) (huU τ j) ht.1 (ht.2 τ j)
  -- evenness and analyticity of `G₀` and `G_{τ j}`
  have hG₀an := analyticAt_rayG₀RGP hε hg θ η k M P₁ P₃ hH0
  have hGan := fun τ j => analyticAt_rayGRGP hε hg θ k M P₁ P₃ τ j hH0
  -- **the induction on the exponents**
  obtain ⟨hG₀0, hG0⟩ := ray_induction_matrix p hp1
    (Matrix.of fun τ j => |M τ (Sum.inl j)| ^ p / (p : ℝ)) hr hrQ (rayζ σ M) (rayν σ σ' M)
    (6 + 4 * U) 2 (hev.mono fun t ht τ j => (hb t ht τ j).1)
    (hev.mono fun t ht τ j => (hb t ht τ j).2.1) (hev.mono fun t ht τ j => (hb t ht τ j).2.2.1)
    (rayG₀ θ η k M P₁ P₃) (rayG θ k M P₁ P₃) hG₀an hGan
    (fun R => hev.mono fun t ht => by
      have ht0 : 0 < t := by linarith [ht.1]
      rw [hray t ht0 fun τ j => (hb t ht τ j).2.2.2.ne', norm_zero]
      exact (Real.exp_pos _).le)
    (fun τ j hF => by
      -- the step "one small factor": `hone` with `a(s) = ∂G₀/∂y_{τ j}(s, 0)`, `b(s) = G_{τ j}(s, 0)`
      have ha : AnalyticAt ℝ (fun S => fderiv ℝ (fun y => rayG₀ θ η k M P₁ P₃ (S, y)) 0
          (Matrix.single τ j (1 : ℝ))) 0 := by
        have h := analyticAt_fderiv_partialRGP (f := rayG₀ θ η k M P₁ P₃) (a := fun S : ℝ => S)
          (b := fun _ => (0 : Matrix T (hid k) ℝ)) (c := fun _ => Matrix.single τ j (1 : ℝ))
          hG₀an analyticAt_id analyticAt_const analyticAt_const
        exact h
      have hbA : AnalyticAt ℝ (fun S => rayG θ k M P₁ P₃ τ j (S, 0)) 0 := by
        have h := (hGan τ j).comp_of_eq
          (analyticAt_id.prod analyticAt_const :
            AnalyticAt ℝ (fun S : ℝ => ((S, (0 : Matrix T (hid k) ℝ)) : ℝ × Matrix T (hid k) ℝ)) 0)
          rfl
        exact h
      have heven : ∀ᶠ s in 𝓝 (0 : ℝ),
          fderiv ℝ (fun y => rayG₀ θ η k M P₁ P₃ (-s, y)) 0 (Matrix.single τ j (1 : ℝ))
            = fderiv ℝ (fun y => rayG₀ θ η k M P₁ P₃ (s, y)) 0 (Matrix.single τ j (1 : ℝ))
          ∧ rayG θ k M P₁ P₃ τ j (-s, 0) = rayG θ k M P₁ P₃ τ j (s, 0) :=
        Eventually.of_forall fun s =>
          ⟨by simp only [rayG₀_negRGP], rayG_negRGP θ k M P₁ P₃ τ j s 0⟩
      have h0 := hone |M τ (Sum.inl j)| (abs_pos.2 (hM0 τ j)) _ _ ha hbA heven hF
      obtain ⟨h3, h1⟩ := hcoef τ j h0
      exact Eventually.of_forall (hGzero τ j h3 h1))
  -- every gate coefficient vanishes, so `ż^g(Ξ) = (P₁ + P₃)^g = 0`
  have hgate : ∀ τ j, P₃ τ (Sum.inl j) = 0 ∧ P₁ τ (Sum.inl j) = 0 := by
    intro τ j
    refine hcoef τ j ?_
    have hc : Tendsto (fun s : ℝ => ((s, 0) : ℝ × Matrix T (hid k) ℝ)) (𝓝 0) (𝓝 0) := by
      have := ((continuous_id.prodMk continuous_const : Continuous fun s : ℝ =>
        ((s, (0 : Matrix T (hid k) ℝ)) : ℝ × Matrix T (hid k) ℝ))).tendsto 0
      exact this
    exact hc.eventually (hG0 τ j)
  have h1 := hP 1
  simp only [one_smul, one_pow] at h1
  refine ⟨fun τ j => ?_, fun w => ?_⟩
  · rw [h1, Matrix.add_apply, (hgate τ j).1, (hgate τ j).2, add_zero]
  -- the continuation: `F(t, w) = 𝓛(w ⊙ (t ι), w ⊙ (t P₁^v + t³ P₃^v))` is analytic in `(t, w)`
  let Wo : Matrix T (hid k) ℝ :=
    Matrix.of fun τ j => if 0 < M τ (Sum.inl j) then M τ (Sum.inl j) else 0
  let F : ℝ × Matrix T (hid k) ℝ → Matrix T dOut ℝ := fun x =>
    writeLHS (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) θ k η
      (Matrix.of fun τ j => x.2 τ j * (x.1 * M τ (Sum.inr j)))
      (Matrix.of fun τ j => x.2 τ j * (x.1 * P₁ τ (Sum.inr j) + x.1 ^ 3 * P₃ τ (Sum.inr j)))
  have hFan : AnalyticOnNhd ℝ F Set.univ := fun x _ => by
    have hv : AnalyticAt ℝ (fun x : ℝ × Matrix T (hid k) ℝ =>
        (Matrix.of fun τ j => x.2 τ j * (x.1 * M τ (Sum.inr j)) : Matrix T (hid k) ℝ)) x :=
      analyticAt_matrixOfRGP fun τ j =>
        (analyticAt_entryRGP analyticAt_snd τ j).fun_mul (analyticAt_fst.fun_mul analyticAt_const)
    have hvd : AnalyticAt ℝ (fun x : ℝ × Matrix T (hid k) ℝ =>
        (Matrix.of fun τ j => x.2 τ j * (x.1 * P₁ τ (Sum.inr j) + x.1 ^ 3 * P₃ τ (Sum.inr j)) :
          Matrix T (hid k) ℝ)) x :=
      analyticAt_matrixOfRGP fun τ j =>
        (analyticAt_entryRGP analyticAt_snd τ j).fun_mul ((analyticAt_fst.fun_mul
          analyticAt_const).fun_add ((analyticAt_fst.fun_pow 3).fun_mul analyticAt_const))
    have h := analyticAt_writeLHSRGP (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid)
      (analyticOnNhd_rmsNorm hε) hf θ η k hv hvd
    exact h
  -- for `t > 0`, `F(t, w) = t² G₀(1/t, W° − w/t)` (by the scaling, as the gate coefficients vanish)
  have hFG : ∀ x : ℝ × Matrix T (hid k) ℝ, 0 < x.1 →
      F x = x.1 ^ 2 • rayG₀ θ η k M P₁ P₃ (1 / x.1, Wo - (1 / x.1) • x.2) := by
    rintro ⟨t, w'⟩ ht
    simp only at ht ⊢
    have ht' := ht.ne'
    have hv : (Matrix.of fun τ j => w' τ j * (t * M τ (Sum.inr j)))
        = t ^ 2 • rayV M (Wo - (1 / t) • w') := by
      ext τ j
      simp only [rayV, Wo, Matrix.of_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
      field_simp
      ring
    have hvd : (Matrix.of fun τ j => w' τ j * (t * P₁ τ (Sum.inr j) + t ^ 3 * P₃ τ (Sum.inr j)))
        = t ^ 4 • rayR M P₁ P₃ (1 / t) (Wo - (1 / t) • w') := by
      ext τ j
      simp only [rayR, Wo, Matrix.of_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul,
        (hgate τ j).1, (hgate τ j).2]
      field_simp
      ring
    show writeLHS _ θ k η _ _ = _
    rw [hv, hvd, writeLHS_pow_smulRGP _ hε rfl hf θ η k ht]
    rfl
  -- `G₀` vanishes on an open set `O ∋ 0`, which contains `(1/t₀, 0)` for some `t₀ > 0`
  obtain ⟨O, hOsub, hOo, hO0⟩ := eventually_nhds_iff.1 hG₀0
  have hlim : Tendsto (fun t : ℝ => ((1 / t, 0) : ℝ × Matrix T (hid k) ℝ)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun t : ℝ => 1 / t) atTop (𝓝 0) := by
      simpa only [one_div] using tendsto_inv_atTop_zero
    exact h1.prodMk_nhds tendsto_const_nhds
  obtain ⟨t₀, ht₀O, ht₀⟩ := ((hlim.eventually_mem (hOo.mem_nhds hO0)).and
    (eventually_gt_atTop 0)).exists
  -- so `F` vanishes near `(t₀, t₀ W°)`
  have hzero : F =ᶠ[𝓝 ((t₀, t₀ • Wo) : ℝ × Matrix T (hid k) ℝ)] 0 := by
    have hφ : ContinuousAt (fun x : ℝ × Matrix T (hid k) ℝ =>
        ((1 / x.1, Wo - (1 / x.1) • x.2) : ℝ × Matrix T (hid k) ℝ)) (t₀, t₀ • Wo) :=
      (continuousAt_const.div continuousAt_fst ht₀.ne').prodMk
        (continuousAt_const.sub ((continuousAt_const.div continuousAt_fst ht₀.ne').smul
          continuousAt_snd))
    have hval : ((1 / (t₀, t₀ • Wo).1, Wo - (1 / (t₀, t₀ • Wo).1) • (t₀, t₀ • Wo).2) :
        ℝ × Matrix T (hid k) ℝ) = (1 / t₀, 0) := by
      simp only [smul_smul, one_div, inv_mul_cancel₀ ht₀.ne', one_smul, sub_self]
    have h1 : ∀ᶠ x in 𝓝 ((t₀, t₀ • Wo) : ℝ × Matrix T (hid k) ℝ),
        ((1 / x.1, Wo - (1 / x.1) • x.2) : ℝ × Matrix T (hid k) ℝ) ∈ O :=
      hφ.eventually_mem (by rw [hval]; exact hOo.mem_nhds ht₀O)
    have h2 : ∀ᶠ x in 𝓝 ((t₀, t₀ • Wo) : ℝ × Matrix T (hid k) ℝ), 0 < x.1 :=
      (continuous_fst.tendsto _).eventually (eventually_gt_nhds ht₀)
    filter_upwards [h1, h2] with x hx1 hx2
    show F x = 0
    rw [hFG x hx2, hOsub _ hx1, smul_zero]
  -- the identity theorem: `F = 0` everywhere, in particular at `t = 1`, which is (38)
  have hall := hFan.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
    (Set.mem_univ _) hzero (Set.mem_univ ((1 : ℝ), w))
  have e : F (1, w) = 0 := hall
  simp only [F, one_mul, one_pow] at e
  rw [← hMdef, h1]
  simp only [Matrix.add_apply]
  exact e

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
  classical
  have hf : ∀ ℓ, AnalyticOnNhd ℝ ((Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid).f ℓ) Set.univ :=
    fun ℓ => analyticOnNhd_f_gated hg.analytic ℓ
  have hBaire : BaireSpace (Matrix T d ℝ) := inferInstanceAs (BaireSpace (T → d → ℝ))
  have hrow : ∀ (Ξ : Matrix T d ℝ) τ c, (Ξ * θ.read k) τ c = Ξ τ ⬝ᵥ (θ.read k)ᵀ c :=
    fun _ _ _ => rfl
  -- the matrices with their rows in `C_k` form an open set
  have hOo : IsOpen {n : Matrix T d ℝ | ∀ t, n t ∈ C k.castSucc} := by
    rw [Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun t =>
      (hθ.cone k.castSucc).isOpen.preimage (continuous_apply t)
  -- (ii): no value `ι_{τ j}` vanishes, on an open dense set (no value column `e_j` vanishes)
  have hD2 : ∀ i : T × hid k, IsOpen {Ξ : Matrix T d ℝ | (Ξ * θ.read k) i.1 (Sum.inr i.2) ≠ 0}
      ∧ Dense {Ξ : Matrix T d ℝ | (Ξ * θ.read k) i.1 (Sum.inr i.2) ≠ 0} := by
    rintro ⟨τ, j⟩
    have hc : Continuous fun Ξ : Matrix T d ℝ => (Ξ * θ.read k) τ (Sum.inr j) :=
      (continuous_apply_apply τ (Sum.inr j)).comp (continuous_id.matrix_mul continuous_const)
    refine ⟨isOpen_ne_fun hc continuous_const, ?_⟩
    refine dense_setOf_ne_zero_of_linearRGP (fun Ξ : Matrix T d ℝ => (Ξ * θ.read k) τ (Sum.inr j))
      (fun x y => by simp only [Matrix.add_mul, Matrix.add_apply])
      (fun c x => by simp only [Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul])
      (x₀ := Pi.single (M := fun _ : T => d → ℝ) τ ((θ.read k)ᵀ (Sum.inr j))) ?_
    show (Pi.single (M := fun _ : T => d → ℝ) τ ((θ.read k)ᵀ (Sum.inr j))) τ ⬝ᵥ
      (θ.read k)ᵀ (Sum.inr j) ≠ 0
    rw [Pi.single_eq_same]
    exact fun h => hθ.value_ne_zero k j (dotProduct_self_eq_zero.1 h)
  have hD2o : IsOpen (⋂ i : T × hid k, {Ξ : Matrix T d ℝ | (Ξ * θ.read k) i.1 (Sum.inr i.2) ≠ 0}) :=
    isOpen_iInter_of_finite fun i => (hD2 i).1
  have hD2d : Dense (⋂ i : T × hid k, {Ξ : Matrix T d ℝ | (Ξ * θ.read k) i.1 (Sum.inr i.2) ≠ 0}) :=
    dense_iInter_of_isOpen (fun i => (hD2 i).1) (fun i => (hD2 i).2)
  -- (iii): `𝐃𝓑(g°(Ξ))` is injective on an open dense set (Lemma D.2 and (K2))
  obtain ⟨U, -, hUd, hU⟩ := exists_open_dense_injective_fderiv_suffix_rmsNorm
    (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) θ hε rfl hf hreg k.succ
  have hgo : AnalyticOnNhd ℝ (fun Ξ : Matrix T d ℝ =>
      (Matrix.of fun t => frozenGated θ k (A k) (Ξ t) : Matrix T d ℝ)) Set.univ := by
    show AnalyticOnNhd ℝ (fun Ξ : Matrix T d ℝ => fun t => frozenGated θ k (A k) (Ξ t)) Set.univ
    exact AnalyticOnNhd.pi fun t => (analyticOnNhd_frozenGatedRGP θ k (A k)).comp
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : T => d → ℝ) t).analyticOnNhd _)
      (Set.mapsTo_univ _ _)
  obtain ⟨ν, hν⟩ := hθ.frozen_deriv k
  have hgν : HasFDerivAt (frozenGated θ k (A k)) (fderiv ℝ (frozenGated θ k (A k)) ν) ν :=
    (analyticOnNhd_frozenGatedRGP θ k (A k) ν (Set.mem_univ _)).differentiableAt.hasFDerivAt
  have hinjν : Function.Injective (fderiv ℝ (fun Ξ : Matrix T d ℝ =>
      (Matrix.of fun t => frozenGated θ k (A k) (Ξ t) : Matrix T d ℝ)) (fun _ => ν)) := by
    have h := injective_fderiv_rowwiseRGP (T := T) hgν hν
    exact h
  obtain ⟨U₃, hU₃o, hU₃d, hU₃⟩ := exists_open_dense_injective_fderiv_compRGP hgo
    (analyticOnNhd_suffix_of_analytic (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) θ
      (analyticOnNhd_rmsNorm hε) hf k.succ) hinjν hUd hU
  -- the generic `Ξ`, with (i), (ii), (iii), are dense
  have hD : Dense ({Ξ : Matrix T d ℝ |
      LinearIndependent ℚ (fun i : T × hid k => |(Ξ * θ.read k) i.1 (Sum.inl i.2)| ^ p)} ∩
      ((⋂ i : T × hid k, {Ξ : Matrix T d ℝ | (Ξ * θ.read k) i.1 (Sum.inr i.2) ≠ 0}) ∩ U₃)) :=
    hdense.inter_of_isOpen_right (hD2d.inter_of_isOpen_left hU₃d hD2o) (hD2o.inter hU₃o)
  -- at a generic `Ξ` with its rows in `C_k`, (38) holds
  have hgood : ∀ Ξ ∈ {n : Matrix T d ℝ | ∀ t, n t ∈ C k.castSucc} ∩ ({Ξ : Matrix T d ℝ |
      LinearIndependent ℚ (fun i : T × hid k => |(Ξ * θ.read k) i.1 (Sum.inl i.2)| ^ p)} ∩
      ((⋂ i : T × hid k, {Ξ : Matrix T d ℝ | (Ξ * θ.read k) i.1 (Sum.inr i.2) ≠ 0}) ∩ U₃)),
      (∀ t j, (tangentRMS Z Ξ * θ.read k + Ξ * η.read k) t (Sum.inl j) = 0) ∧
      ∀ w : Matrix T (hid k) ℝ,
        writeLHS (Arch.gated σ (rmsNorm ε) hid) θ k η
          (Matrix.of fun t j => w t j * (Ξ * θ.read k) t (Sum.inr j))
          (Matrix.of fun t j =>
            w t j * (tangentRMS Z Ξ * θ.read k + Ξ * η.read k) t (Sum.inr j)) = 0 := by
    rintro Ξ ⟨hO, h1, h2, h3⟩
    exact flat_at_generic_ray_gated_rmsNorm hε hg hone hθ k Z η hflat Ξ hO h1
      (fun t j => Set.mem_iInter.1 h2 (t, j)) (hU₃ Ξ h3)
  -- both parts of (38) are closed conditions in `n`
  intro n hn
  have hcl := hD.open_subset_closure_inter hOo hn
  have hzan : ∀ n₀ : Matrix T d ℝ, AnalyticAt ℝ
      (fun n : Matrix T d ℝ => tangentRMS Z n * θ.read k + n * η.read k) n₀ := fun n₀ =>
    (analyticAt_matMulRGP (analyticAt_tangentRMSRGP Z n₀) analyticAt_const).fun_add
      (analyticAt_matMulRGP analyticAt_id analyticAt_const)
  refine ⟨fun t j => ?_, fun w => ?_⟩
  · have hc : Continuous fun n : Matrix T d ℝ =>
        (tangentRMS Z n * θ.read k + n * η.read k) t (Sum.inl j) :=
      continuous_iff_continuousAt.2 fun n₀ => (analyticAt_entryRGP (hzan n₀) t (Sum.inl j)).continuousAt
    exact (closure_minimal (fun Ξ hΞ => (hgood Ξ hΞ).1 t j) (isClosed_eq hc continuous_const)) hcl
  · have hc : Continuous fun n : Matrix T d ℝ =>
        writeLHS (Arch.gated σ (rmsNorm ε) hid) θ k η
          (Matrix.of fun t j => w t j * (n * θ.read k) t (Sum.inr j))
          (Matrix.of fun t j =>
            w t j * (tangentRMS Z n * θ.read k + n * η.read k) t (Sum.inr j)) := by
      refine continuous_iff_continuousAt.2 fun n₀ => ?_
      have hv : AnalyticAt ℝ (fun n : Matrix T d ℝ =>
          (Matrix.of fun t j => w t j * (n * θ.read k) t (Sum.inr j) : Matrix T (hid k) ℝ)) n₀ :=
        analyticAt_matrixOfRGP fun t j => analyticAt_const.fun_mul (analyticAt_entryRGP
          (analyticAt_matMulRGP analyticAt_id analyticAt_const) t (Sum.inr j))
      have hvd : AnalyticAt ℝ (fun n : Matrix T d ℝ => (Matrix.of fun t j =>
          w t j * (tangentRMS Z n * θ.read k + n * η.read k) t (Sum.inr j) :
            Matrix T (hid k) ℝ)) n₀ :=
        analyticAt_matrixOfRGP fun t j =>
          analyticAt_const.fun_mul (analyticAt_entryRGP (hzan n₀) t (Sum.inr j))
      have h := analyticAt_writeLHSRGP (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid)
        (analyticOnNhd_rmsNorm hε) hf θ η k hv hvd
      exact h.continuousAt
    exact (closure_minimal (fun Ξ hΞ => (hgood Ξ hΞ).2 w) (isClosed_eq hc continuous_const)) hcl

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
  rcases isEmpty_or_nonempty T with hT | hT
  · -- no token: both parts of (38) hold trivially
    intro n _
    refine ⟨fun t => isEmptyElim t, fun w => ?_⟩
    ext t
    exact isEmptyElim t
  · -- (i) is dense: the numbers `|ξ_t c_j|` are independent over `ℚ` for a dense set of `Ξ`
    have hdense : Dense {Ξ : Matrix T d ℝ |
        LinearIndependent ℚ (fun i : T × hid k => |(Ξ * θ.read k) i.1 (Sum.inl i.2)| ^ 1)} := by
      have hset : {Ξ : Matrix T d ℝ |
          LinearIndependent ℚ (fun i : T × hid k => |(Ξ * θ.read k) i.1 (Sum.inl i.2)| ^ 1)}
          = {Ξ : Matrix T d ℝ | LinearIndependent ℚ
              (fun i : T × hid k => |Ξ i.1 ⬝ᵥ (θ.read k)ᵀ (Sum.inl i.2)|)} := by
        ext Ξ
        simp only [pow_one]
        rfl
      rw [hset]
      exact dense_setOf_linearIndependent_abs_dotProduct (T := T)
        (fun j : hid k => (θ.read k)ᵀ (Sum.inl j)) hQ
    -- "one small factor" for SiLU is the parity (30)
    exact flat_of_suffixFlat_gated_rmsNorm hε gateFar_silu
      (fun u hu a b ha hb heven h => one_small_factor_silu hu ha hb heven h) hθ
      (regular_of_goodForConesGated_swiglu hθ) k hdense Z η hflat

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
  rcases isEmpty_or_nonempty T with hT | hT
  · -- no token: both parts of (38) hold trivially
    intro n _
    refine ⟨fun t => isEmptyElim t, fun w => ?_⟩
    ext t
    exact isEmptyElim t
  · -- (i) is dense: the numbers `(ξ_t c_j)²` are independent over `ℚ` for a dense set of `Ξ`
    have hdense : Dense {Ξ : Matrix T d ℝ |
        LinearIndependent ℚ (fun i : T × hid k => |(Ξ * θ.read k) i.1 (Sum.inl i.2)| ^ 2)} := by
      have hset : {Ξ : Matrix T d ℝ |
          LinearIndependent ℚ (fun i : T × hid k => |(Ξ * θ.read k) i.1 (Sum.inl i.2)| ^ 2)}
          = {Ξ : Matrix T d ℝ | LinearIndependent ℚ
              (fun i : T × hid k => (Ξ i.1 ⬝ᵥ (θ.read k)ᵀ (Sum.inl i.2)) ^ 2)} := by
        ext Ξ
        simp only [sq_abs]
        rfl
      rw [hset]
      exact dense_setOf_linearIndependent_sq_dotProduct (T := T)
        (fun j : hid k => (θ.read k)ᵀ (Sum.inl j)) hQ
    -- "one small factor" for GELU is Lemma D.9
    exact flat_of_suffixFlat_gated_rmsNorm hε gateFar_gelu
      (fun u hu a b ha hb _ h => one_small_factor_gelu hu ha hb h) hθ
      (regular_of_goodForConesGated_geglu hθ) k hdense Z η hflat

end Skips
