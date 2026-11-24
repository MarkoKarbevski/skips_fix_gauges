import SkipsLean.OneBlock.LearnedSkipRMSZeroBoundKinds

/-!
# One block with an upper triangular learned skip under pre-RMSNorm with `ε = 0`: "at most"

Paper (skips paper), Theorem B.1 (iii): "Let the network be pre-RMSNorm without biases, with a
learned skip `A`, full or upper triangular. […] For `ε = 0` it exceeds that of the residual
network with `ε = 0` by at most `d_model (d_model + 1)/2 − 1`, with equality for ReLU, ReLU² and
ReGLU blocks."

Its proof: "For an upper triangular `A`, view the network as the network with a full `A`
restricted to triangular skips: its flat directions are those of the full network whose entry
`η_A` is upper triangular." And, in "The case `ε = 0`": "For the learned skip, `η^rot` and `K_B`
are flat, which gives at least `d_model (d_model − 1) + 2`, respectively
`d_model (d_model − 1)/2 + 2`, dimensions besides `K_B`, against `d_model (d_model − 1)/2 + 1`
for the residual network. So the difference is at most `d_model (d_model + 1)/2 − 1`."

Here, for an upper triangular learned skip and a block whose fixed map is analytic (tanh, GELU,
SwiGLU, GeGLU, attention):

* At an input at which no normalized row vanishes, the output is a differentiable function of the
  weights and the skip. So the Jacobian of the family of triangular skips on a batch of such
  inputs is that of the family of all skips composed with the inclusion (the chain rule), and the
  triangular family has at most the functional dimension of the full one at the same weights and
  skip (`funDimSkipsOn_tri_le_learned_rmsNorm_zero`).
* With the bound for the full skip (`funDimSkipsOn_add_le_learned_rmsNorm_zero`,
  `OneBlock/LearnedSkipRMSZeroBound.lean`): the functional dimension is at most
  `P + d(d+1)/2 − (d(d−1)/2 + 2) − dim V_θ`, where `P + d(d+1)/2` counts the weights and the
  entries of the triangular skip.
* The difference to the residual network with the same weights is at most `d(d+1)/2 − 1`: at one
  parameter, at almost every `(θ, A)` with `A` upper triangular, and for the kinds of block by
  name.

The route differs from the paper's: the paper counts the flat directions of the triangular
family, `d(d−1)/2 + 2` besides `K_B`; here the bound is carried from the family of all skips. The
two give the same number, `P + d² − (d(d−1) + 2) = P + d(d+1)/2 − (d(d−1)/2 + 2)`.

The functional dimensions are those on the inputs at which no normalized row vanishes
(`funDimSkipsOn` on `learnedZeroDomain`, `funDimOn` on `residualZeroDomain`), and the two networks
have the same weights `θ`. As in `OneBlock/LearnedSkipRMSZeroBoundKinds.lean`, the blocks may have
any width with at least one hidden unit (one head of positive width), and `d_in, d_out ≥ d ≥ 2`.
Not stated: ReLU, ReLU², ReGLU blocks and the equality for them.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d]
  [LinearOrder d] [Fintype dIn] [Fintype dOut]

/-- Helper (a copy of the private `differentiableAt_matMul_rzo`): the product of two matrix-valued
maps that are differentiable at a point is differentiable there. -/
private theorem differentiableAt_matMul_lzt {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
    {f : P → Matrix m n ℝ} {g : P → Matrix n p ℝ} {y : P}
    (hf : DifferentiableAt ℝ f y) (hg : DifferentiableAt ℝ g y) :
    DifferentiableAt ℝ (fun y => f y * g y) y := by
  let B : Matrix m n ℝ →ₗ[ℝ] Matrix n p ℝ →ₗ[ℝ] Matrix m p ℝ :=
    LinearMap.mk₂ ℝ (fun a b => a * b) Matrix.add_mul (fun c a b => Matrix.smul_mul c a b)
      Matrix.mul_add (fun c a b => Matrix.mul_smul a c b)
  let B' : Matrix m n ℝ →L[ℝ] Matrix n p ℝ →L[ℝ] Matrix m p ℝ :=
    LinearMap.toContinuousLinearMap
      ((LinearMap.toContinuousLinearMap :
        (Matrix n p ℝ →ₗ[ℝ] Matrix m p ℝ) ≃ₗ[ℝ] (Matrix n p ℝ →L[ℝ] Matrix m p ℝ)).toLinearMap ∘ₗ B)
  have hB : (fun y => f y * g y) = fun y => B' (f y) (g y) := rfl
  rw [hB]
  exact (B'.differentiableAt.comp y hf).clm_apply hg

omit [Fintype T] [Nonempty T] [DecidableEq d] [LinearOrder d] [Fintype dOut] in
/-- Helper (a copy of the private `eval_eq_ltr`, for `ε = 0`): the function of one block under
pre-RMSNorm with the skip `S 0`, `F(x) = N_0(x E S + f(N_0(x E) W_read) W_write) D`. -/
private theorem eval_eq_lzt {A : Arch T d 1} (hA : A.χ = rmsNorm 0)
    (S : Fin 1 → Matrix d d ℝ) (θ : Params A dIn dOut) (x : Matrix T dIn ℝ) :
    eval A S θ x = rmsNorm 0 (x * θ.E * S 0
      + A.f 0 (rmsNorm 0 (x * θ.E) * θ.read 0) * θ.write 0) * θ.D := by
  have h1 : (Fin.last 1 : Fin 2) = (0 : Fin 1).succ := rfl
  rw [eval, h1, hidden_succ, Fin.castSucc_zero, hidden_zero, hA]

omit [Nonempty T] [DecidableEq d] [LinearOrder d] in
/-- Helper (the twin of the private `differentiableAt_evalSkips_ltr` for `ε = 0`): at an input `x`
at which no normalized row vanishes and `f` is differentiable at `N_0(x E) W_read`, the output with
the full learned skip is a differentiable function of `(θ, R)`. -/
private theorem differentiableAt_evalSkips_lzt {A : Arch T d 1}
    (hA : A.χ = rmsNorm 0) (θ : Params A dIn dOut) (R : Fin 1 → Matrix d d ℝ)
    (x : Matrix T dIn ℝ) (hx : x ∈ learnedZeroDomain A θ R)
    (hfx : DifferentiableAt ℝ (A.f 0) (rmsNorm 0 (x * θ.E) * θ.read 0)) :
    DifferentiableAt ℝ (fun p : Params A dIn dOut × (Fin 1 → Matrix d d ℝ) =>
      evalSkips A (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) p x) (θ, R) := by
  have e : (fun p : Params A dIn dOut × (Fin 1 → Matrix d d ℝ) =>
      evalSkips A (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) p x)
      = fun p => rmsNorm 0 (x * p.1.E * p.2 0
          + A.f 0 (rmsNorm 0 (x * p.1.E) * p.1.read 0) * p.1.write 0) * p.1.D :=
    funext fun p => eval_eq_lzt hA p.2 p.1 x
  rw [e]
  -- the weights and the skip are linear, hence differentiable, functions of `(θ, R)`
  have hE : DifferentiableAt ℝ
      (fun p : Params A dIn dOut × (Fin 1 → Matrix d d ℝ) => p.1.E) (θ, R) :=
    ((LinearMap.toContinuousLinearMap (Params.linE (A := A) (dIn := dIn) (dOut := dOut))).comp
      (ContinuousLinearMap.fst ℝ _ (Fin 1 → Matrix d d ℝ))).differentiableAt
  have hR : DifferentiableAt ℝ
      (fun p : Params A dIn dOut × (Fin 1 → Matrix d d ℝ) => p.1.read 0) (θ, R) :=
    ((LinearMap.toContinuousLinearMap
      (Params.linRead (A := A) (dIn := dIn) (dOut := dOut) 0)).comp
      (ContinuousLinearMap.fst ℝ _ (Fin 1 → Matrix d d ℝ))).differentiableAt
  have hW : DifferentiableAt ℝ
      (fun p : Params A dIn dOut × (Fin 1 → Matrix d d ℝ) => p.1.write 0) (θ, R) :=
    ((LinearMap.toContinuousLinearMap
      (Params.linWrite (A := A) (dIn := dIn) (dOut := dOut) 0)).comp
      (ContinuousLinearMap.fst ℝ _ (Fin 1 → Matrix d d ℝ))).differentiableAt
  have hD : DifferentiableAt ℝ
      (fun p : Params A dIn dOut × (Fin 1 → Matrix d d ℝ) => p.1.D) (θ, R) :=
    ((LinearMap.toContinuousLinearMap (Params.linD (A := A) (dIn := dIn) (dOut := dOut))).comp
      (ContinuousLinearMap.fst ℝ _ (Fin 1 → Matrix d d ℝ))).differentiableAt
  have hS : DifferentiableAt ℝ
      (fun p : Params A dIn dOut × (Fin 1 → Matrix d d ℝ) => p.2 0) (θ, R) :=
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => Matrix d d ℝ) 0).comp
      (ContinuousLinearMap.snd ℝ (Params A dIn dOut) _)).differentiableAt
  -- `x E`, `N_0(x E)` (no row of `x E` is zero), `N_0(x E) W_read`, `f(…)`
  have h1 : DifferentiableAt ℝ
      (fun p : Params A dIn dOut × (Fin 1 → Matrix d d ℝ) => x * p.1.E) (θ, R) :=
    differentiableAt_matMul_lzt (differentiableAt_const x) hE
  have h2 : DifferentiableAt ℝ
      (fun p : Params A dIn dOut × (Fin 1 → Matrix d d ℝ) => rmsNorm 0 (x * p.1.E)) (θ, R) :=
    DifferentiableAt.comp (f := fun p : Params A dIn dOut × (Fin 1 → Matrix d d ℝ) =>
      x * p.1.E) (θ, R) (analyticAt_rmsNorm_zero (x * θ.E) hx.1).differentiableAt h1
  have h3 : DifferentiableAt ℝ (fun p : Params A dIn dOut × (Fin 1 → Matrix d d ℝ) =>
      rmsNorm 0 (x * p.1.E) * p.1.read 0) (θ, R) :=
    differentiableAt_matMul_lzt h2 hR
  have h4 : DifferentiableAt ℝ (fun p : Params A dIn dOut × (Fin 1 → Matrix d d ℝ) =>
      A.f 0 (rmsNorm 0 (x * p.1.E) * p.1.read 0)) (θ, R) :=
    DifferentiableAt.comp (f := fun p : Params A dIn dOut × (Fin 1 → Matrix d d ℝ) =>
      rmsNorm 0 (x * p.1.E) * p.1.read 0) (θ, R) hfx h3
  -- `h_1 = x E S + f(…) W_write`, `N_0(h_1)` (no row of `h_1` is zero) and `N_0(h_1) D`
  have h5 : DifferentiableAt ℝ (fun p : Params A dIn dOut × (Fin 1 → Matrix d d ℝ) =>
      x * p.1.E * p.2 0 + A.f 0 (rmsNorm 0 (x * p.1.E) * p.1.read 0) * p.1.write 0) (θ, R) :=
    (differentiableAt_matMul_lzt h1 hS).add (differentiableAt_matMul_lzt h4 hW)
  have h6 : DifferentiableAt ℝ (fun p : Params A dIn dOut × (Fin 1 → Matrix d d ℝ) =>
      rmsNorm 0 (x * p.1.E * p.2 0
        + A.f 0 (rmsNorm 0 (x * p.1.E) * p.1.read 0) * p.1.write 0)) (θ, R) :=
    DifferentiableAt.comp (f := fun p : Params A dIn dOut × (Fin 1 → Matrix d d ℝ) =>
      x * p.1.E * p.2 0 + A.f 0 (rmsNorm 0 (x * p.1.E) * p.1.read 0) * p.1.write 0) (θ, R)
      (analyticAt_rmsNorm_zero _ hx.2).differentiableAt h5
  exact differentiableAt_matMul_lzt h6 hD

omit [Nonempty T] [DecidableEq d] [LinearOrder d] in
/-- Helper (the twin of the private `jacobianRankSkips_comp_le_lsg` of `OneBlock/LearnedSkip.lean`
with differentiability at the inputs of the batch only): the Jacobian of the restricted family on
a batch is that of the larger family composed with `(θ, v') ↦ (θ, j v')`, so its rank is not
larger (the chain rule). -/
private theorem jacobianRankSkips_comp_le_lzt {L : ℕ} {V V' : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [NormedAddCommGroup V'] [NormedSpace ℝ V'] (A : Arch T d L)
    (ι : V →L[ℝ] (Fin L → Matrix d d ℝ)) (j : V' →L[ℝ] V) {n : ℕ}
    (X : Fin n → Matrix T dIn ℝ) (θ : Params A dIn dOut) (v' : V')
    (hdiff : ∀ i, DifferentiableAt ℝ
      (fun p : Params A dIn dOut × V => evalSkips A ι p (X i)) (θ, j v')) :
    jacobianRankSkips A (ι.comp j) X (θ, v') ≤ jacobianRankSkips A ι X (θ, j v') := by
  -- the map `(θ, v') ↦ (θ, j v')`
  let m : Params A dIn dOut × V' →L[ℝ] Params A dIn dOut × V :=
    (ContinuousLinearMap.id ℝ (Params A dIn dOut)).prodMap j
  -- the outputs of the larger family on the batch: differentiable at `(θ, j v')`
  let G : Params A dIn dOut × V → Fin n → Matrix T dOut ℝ :=
    fun p => fun i => evalSkips A ι p (X i)
  have hG : DifferentiableAt ℝ G (m (θ, v')) := differentiableAt_pi.2 hdiff
  -- the restricted family is the larger one composed with `m`
  have hcomp : (fun p' : Params A dIn dOut × V' => fun i : Fin n =>
      evalSkips A (ι.comp j) p' (X i)) = G ∘ m := rfl
  have hd : fderiv ℝ (G ∘ m) (θ, v') = (fderiv ℝ G (θ, j v')).comp m := by
    rw [fderiv_comp (θ, v') hG m.differentiableAt, m.fderiv]
    rfl
  -- the range of a composition lies in the range of the outer map
  unfold jacobianRankSkips
  rw [hcomp, hd]
  exact Submodule.finrank_mono (LinearMap.range_comp_le_range _ _)

omit [Nonempty T] [DecidableEq d] in
/-- **One block under pre-RMSNorm with `ε = 0`, on the inputs at which no normalized row
vanishes:** the family of upper triangular skips has at `(θ, R)` at most the functional dimension
of the family of all skips ("view the network as the network with a full `A` restricted to
triangular skips"). -/
theorem funDimSkipsOn_tri_le_learned_rmsNorm_zero {A : Arch T d 1} (hA : A.χ = rmsNorm 0)
    (hf : Differentiable ℝ (A.f 0)) (θ : Params A dIn dOut) (R : Fin 1 → upperTriangular d) :
    funDimSkipsOn A (triSkips d 1) (θ, R)
        (learnedZeroDomain A θ fun ℓ => (R ℓ : Matrix d d ℝ))
      ≤ funDimSkipsOn A (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ))
          (θ, fun ℓ => (R ℓ : Matrix d d ℝ))
          (learnedZeroDomain A θ fun ℓ => (R ℓ : Matrix d d ℝ)) := by
  -- the ranks of the full family are at most the number of weights and entries of the skip
  have hbdd : BddAbove {r : ℕ | ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ),
      (∀ i, X i ∈ learnedZeroDomain A θ fun ℓ => (R ℓ : Matrix d d ℝ)) ∧
      r = jacobianRankSkips A (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) X
        (θ, fun ℓ => (R ℓ : Matrix d d ℝ))} := by
    refine ⟨Module.finrank ℝ (Params A dIn dOut × (Fin 1 → Matrix d d ℝ)), ?_⟩
    rintro r ⟨n, X, -, rfl⟩
    exact LinearMap.finrank_range_le _
  unfold funDimSkipsOn
  refine csSup_le' ?_
  rintro r ⟨n, X, hX, rfl⟩
  refine le_trans ?_ (le_csSup hbdd ⟨n, X, hX, rfl⟩)
  -- on the batch the outputs of the full family are differentiable at `(θ, R)`: the chain rule
  exact jacobianRankSkips_comp_le_lzt A (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ))
    (triSkips d 1) X θ R fun i => differentiableAt_evalSkips_lzt hA θ _ (X i) (hX i) (hf _)

omit [Nonempty T] in
/-- **Proof of Theorem B.1 (iii) of the skips paper, "The case `ε = 0`", the bound for the upper
triangular learned skip:** for one block with an analytic fixed map and an invertible upper
triangular learned skip `A`, under pre-RMSNorm with `ε = 0`, if `E` has rank `d ≥ 1`, the
functional dimension on the inputs at which no normalized row vanishes is at most
`P + d(d+1)/2 − (d(d−1)/2 + 2) − dim V_θ`. -/
theorem funDimSkipsOn_tri_add_le_learned_rmsNorm_zero {A : Arch T d 1} [Nonempty d]
    (hA : A.χ = rmsNorm 0) (hf : AnalyticOnNhd ℝ (A.f 0) Set.univ) (θ : Params A dIn dOut)
    (R : Fin 1 → upperTriangular d) (hE : θ.E.rank = Fintype.card d)
    (hR : IsUnit (R 0 : Matrix d d ℝ).det) :
    funDimSkipsOn A (triSkips d 1) (θ, R)
        (learnedZeroDomain A θ fun ℓ => (R ℓ : Matrix d d ℝ))
        + ((Fintype.card d * (Fintype.card d - 1) / 2 + 2)
          + Module.finrank ℝ (blockFlatSphere A θ))
      ≤ Module.finrank ℝ (Params A dIn dOut)
        + Fintype.card d * (Fintype.card d + 1) / 2 := by
  have h1 := funDimSkipsOn_tri_le_learned_rmsNorm_zero hA
    (differentiableOn_univ.1 hf.differentiableOn) θ R
  have h2 := funDimSkipsOn_add_le_learned_rmsNorm_zero hA hf θ
    (fun ℓ => (R ℓ : Matrix d d ℝ)) hE hR
  -- `d(d−1)` and `d(d+1)` are even, and `d(d+1)/2 + d(d−1)/2 = d²`
  have e1 := Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self (Fintype.card d))
  have e2 := Nat.two_mul_div_two_of_even (Nat.even_mul_succ_self (Fintype.card d))
  have e3 : Fintype.card d * (Fintype.card d + 1) + Fintype.card d * (Fintype.card d - 1)
      = 2 * Fintype.card d ^ 2 := by
    obtain ⟨k, hk⟩ : ∃ k, Fintype.card d = k + 1 :=
      ⟨Fintype.card d - 1, (Nat.sub_add_cancel Fintype.card_pos).symm⟩
    rw [hk, Nat.add_sub_cancel]
    ring
  generalize Fintype.card d * (Fintype.card d + 1) = y at e2 e3 ⊢
  generalize Fintype.card d * (Fintype.card d - 1) = x at h2 e1 e3 ⊢
  generalize Fintype.card d ^ 2 = q at h2 e3
  omega

/-- **Theorem B.1 (iii) of the skips paper for `ε = 0`, "at most", for an upper triangular learned
skip, at one parameter:** under the conditions of the value for the residual network (`d ≥ 2`,
`E`, `D` of rank `d`, one input `w` with the rows of `w E` and `g(w)` independent for every token)
and for an invertible upper triangular learned skip, the functional dimension of the network with
the learned skip exceeds that of the residual network with the same weights by at most
`d(d+1)/2 − 1`; both on the inputs at which no normalized row vanishes. -/
theorem funDimSkipsOn_tri_le_funDimOn_residual_add_rmsNorm_zero {A : Arch T d 1}
    (hA : A.χ = rmsNorm 0) (hd : 2 ≤ Fintype.card d)
    (hf : AnalyticOnNhd ℝ (A.f 0) Set.univ) (θ : Params A dIn dOut)
    (R : Fin 1 → upperTriangular d) (hE : θ.E.rank = Fintype.card d)
    (hD : θ.D.rank = Fintype.card d) (hR : IsUnit (R 0 : Matrix d d ℝ).det)
    (hw : ∃ w : Matrix T dIn ℝ, ∀ t, LinearIndependent ℝ
      ![(w * θ.E) t, (A.f 0 (rmsNorm 0 (w * θ.E) * θ.read 0) * θ.write 0) t]) :
    funDimSkipsOn A (triSkips d 1) (θ, R)
        (learnedZeroDomain A θ fun ℓ => (R ℓ : Matrix d d ℝ))
      ≤ funDimOn A 1 θ (residualZeroDomain A θ)
        + (Fintype.card d * (Fintype.card d + 1) / 2 - 1) :=
  (funDimSkipsOn_tri_le_learned_rmsNorm_zero hA
    (differentiableOn_univ.1 hf.differentiableOn) θ R).trans
    (funDimSkipsOn_learned_le_funDimOn_residual_add_rmsNorm_zero hA hd hf θ
      (fun ℓ => (R ℓ : Matrix d d ℝ)) hE hD hR hw)

omit [Fintype T] [Nonempty T] [DecidableEq d] [LinearOrder d] in
/-- Helper (copy of the private `ae_fst_lzk` of `OneBlock/LearnedSkipRMSZeroBoundKinds.lean`): a
condition on the weights that holds at almost every `θ` holds at almost every `(θ, v)`. -/
private theorem ae_fst_lzt {A : Arch T d 1} {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] (hB : BorelSpace V)
    (μ : Measure (Params A dIn dOut × V)) (hμ : μ.IsAddHaarMeasure) {Q : Params A dIn dOut → Prop}
    (h : ∀ᵐ θ ∂(Measure.addHaar : Measure (Params A dIn dOut)), Q θ) :
    ∀ᵐ p ∂μ, Q p.1 := by
  -- a measurable null set `N` outside which `Q` holds
  rw [ae_iff] at h
  obtain ⟨N, hsub, hN, hN0⟩ := exists_measurable_superset_of_null h
  have hc : ∀ᵐ θ ∂(Measure.addHaar : Measure (Params A dIn dOut)), θ ∈ Nᶜ :=
    measure_eq_zero_iff_ae_notMem.1 hN0
  have h1 := (ae_comp_linearMap_mem_iff (LinearMap.fst ℝ (Params A dIn dOut) V) μ
    Measure.addHaar (LinearMap.fst_surjective) hN.compl).2 hc
  refine h1.mono fun p hp => ?_
  by_contra hq
  exact hp (hsub hq)

omit [LinearOrder d] in
/-- Helper (copy of the private `ae_isUnit_det_lzk` of
`OneBlock/LearnedSkipRMSZeroBoundKinds.lean`): if a square matrix that depends linearly on a point
of `E` is the identity at one point, it is invertible at almost every point. -/
private theorem ae_isUnit_det_lzt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] (hB : BorelSpace E) (μ : Measure E)
    (hμ : μ.IsAddHaarMeasure) (Φ : E →ₗ[ℝ] Matrix d d ℝ) (x₀ : E) (h₀ : Φ x₀ = 1) :
    ∀ᵐ x ∂μ, IsUnit (Φ x).det := by
  -- the entries are linear, so the determinant is analytic
  have hentry : ∀ i j, AnalyticOnNhd ℝ (fun x => Φ x i j) Set.univ := fun i j =>
    (LinearMap.toContinuousLinearMap ((Matrix.entryLinearMap ℝ ℝ i j) ∘ₗ Φ)).analyticOnNhd _
  have hφ : AnalyticOnNhd ℝ (fun x => (Φ x).det) Set.univ := by
    simp only [Matrix.det_apply']
    exact Finset.analyticOnNhd_fun_sum _ fun σ _ => analyticOnNhd_const.mul
      (Finset.analyticOnNhd_fun_prod _ fun i _ => hentry (σ i) i)
  -- it is `1` at `x₀`, so its zero set is null
  have hnull := measure_zeroSet_of_analytic μ hφ ⟨x₀, by rw [h₀, Matrix.det_one]; exact one_ne_zero⟩
  rw [ae_iff]
  simpa only [isUnit_iff_ne_zero, not_not] using hnull

/-- **Theorem B.1 (iii) of the skips paper for `ε = 0`, "at most", for an upper triangular learned
skip, at generic weights and skip, for a block with an analytic fixed map:** if at almost every
`θ` the embedding and the readout have rank `d` and some input `w` has the rows of `w E` and
`g(w)` independent for every token, then at almost every `(θ, A)`, `A` upper triangular, the
functional dimension of the network with the learned skip `A` exceeds that of the residual
network with the weights `θ` by at most `d(d+1)/2 − 1`. -/
theorem ae_funDimSkipsOn_tri_le_funDimOn_residual_add_rmsNorm_zero {A : Arch T d 1}
    (hA : A.χ = rmsNorm 0) (hd : 2 ≤ Fintype.card d) (hf : AnalyticOnNhd ℝ (A.f 0) Set.univ)
    (μ : Measure (Params A dIn dOut × (Fin 1 → upperTriangular d))) [μ.IsAddHaarMeasure]
    (hgen : ∀ᵐ θ ∂(Measure.addHaar : Measure (Params A dIn dOut)),
      θ.E.rank = Fintype.card d ∧ θ.D.rank = Fintype.card d ∧
      ∃ w : Matrix T dIn ℝ, ∀ t, LinearIndependent ℝ
        ![(w * θ.E) t, (A.f 0 (rmsNorm 0 (w * θ.E) * θ.read 0) * θ.write 0) t]) :
    ∀ᵐ p ∂μ, funDimSkipsOn A (triSkips d 1) p
        (learnedZeroDomain A p.1 fun ℓ => (p.2 ℓ : Matrix d d ℝ))
      ≤ funDimOn A 1 p.1 (residualZeroDomain A p.1)
        + (Fintype.card d * (Fintype.card d + 1) / 2 - 1) := by
  -- at almost every `(θ, A)`: `E`, `D` of rank `d` and the input `w` (from `θ`), and the
  -- triangular skip `A_0` invertible (its determinant is a polynomial, `1` at `A_0 = 1`)
  have hBt : BorelSpace (Fin 1 → upperTriangular d) := inferInstance
  have hBp : BorelSpace (Params A dIn dOut × (Fin 1 → upperTriangular d)) := Prod.borelSpace
  have hdet : ∀ᵐ p ∂μ, IsUnit (p.2 0 : Matrix d d ℝ).det :=
    ae_isUnit_det_lzt hBp μ (by assumption)
      ((upperTriangular d).subtype
        ∘ₗ (LinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => upperTriangular d) 0)
        ∘ₗ (LinearMap.snd ℝ _ (Fin 1 → upperTriangular d)))
      (0, fun _ => ⟨1, Matrix.blockTriangular_one⟩) rfl
  filter_upwards [ae_fst_lzt hBt μ (by assumption) hgen, hdet] with p hp hdp
  obtain ⟨hE, hD, hw⟩ := hp
  -- the bound at one parameter
  exact funDimSkipsOn_tri_le_funDimOn_residual_add_rmsNorm_zero hA hd hf p.1 p.2 hE hD hdp hw

variable {hid H dh : Fin 1 → Type} [∀ ℓ, Fintype (hid ℓ)] [∀ ℓ, Fintype (H ℓ)]
  [∀ ℓ, Fintype (dh ℓ)]
variable {σ : ℝ → ℝ}

/-- **Theorem B.1 (iii) of the skips paper for `ε = 0`, "at most", for one MLP block with an
analytic activation that is nonzero on the positive reals:** for `d_in, d_out ≥ d ≥ 2`, at almost
every weights and triangular skip `(θ, A)` the functional dimension exceeds that of the residual
network with the weights `θ` by at most `d(d+1)/2 − 1`. -/
theorem ae_funDimSkipsOn_tri_le_residual_add_mlp_oneBlock_rmsNorm_zero
    (hσa : AnalyticOnNhd ℝ σ Set.univ) (hσp : ∀ z, 0 < z → σ z ≠ 0)
    [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut
      × (Fin 1 → upperTriangular d)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, funDimSkipsOn (Arch.mlp σ (rmsNorm 0) hid)
        (triSkips d 1) p
        (learnedZeroDomain (Arch.mlp σ (rmsNorm 0) hid) p.1
          fun ℓ => (p.2 ℓ : Matrix d d ℝ))
      ≤ funDimOn (Arch.mlp σ (rmsNorm 0) hid) 1 p.1
          (residualZeroDomain (Arch.mlp σ (rmsNorm 0) hid) p.1)
        + (Fintype.card d * (Fintype.card d + 1) / 2 - 1) := by
  have : Nonempty d := Fintype.card_pos_iff.1 (by omega)
  have hf : ∀ ℓ, AnalyticOnNhd ℝ ((Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid).f ℓ) Set.univ :=
    fun ℓ => analyticOnNhd_f_mlp hσa ℓ
  refine ae_funDimSkipsOn_tri_le_funDimOn_residual_add_rmsNorm_zero rfl hd (hf 0) μ ?_
  -- at almost every `θ`: `E` and `D` have rank `d`, and the input `w` of the proof exists
  filter_upwards [ae_turnGeneric _ (fun ℓ => continuousOn_univ.mp (hf ℓ).continuousOn)
    Measure.addHaar hd hdIn hdOut (ae_someBlockNonzero_mlp hσp ⟨0, inferInstance⟩ Measure.addHaar),
    ae_exists_linearIndependent_rows_mlp (continuousOn_univ.mp hσa.continuousOn) hσp Measure.addHaar
      hd hdIn hdOut] with θ hθ hw
  exact ⟨hθ.rank_E, hθ.rank_D, hw⟩

/-- **Theorem B.1 (iii) of the skips paper for `ε = 0`, "at most", for one tanh block:** for `d_in,
d_out ≥ d ≥ 2`, at almost every weights and triangular skip `(θ, A)` the functional dimension
exceeds that of the residual network with the weights `θ` by at most `d(d+1)/2 − 1`. -/
theorem ae_funDimSkipsOn_tri_le_residual_add_tanh_oneBlock_rmsNorm_zero
    [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) Real.tanh (rmsNorm 0) hid) dIn dOut
      × (Fin 1 → upperTriangular d)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, funDimSkipsOn (Arch.mlp Real.tanh (rmsNorm 0) hid)
        (triSkips d 1) p
        (learnedZeroDomain (Arch.mlp Real.tanh (rmsNorm 0) hid) p.1
          fun ℓ => (p.2 ℓ : Matrix d d ℝ))
      ≤ funDimOn (Arch.mlp Real.tanh (rmsNorm 0) hid) 1 p.1
          (residualZeroDomain (Arch.mlp Real.tanh (rmsNorm 0) hid) p.1)
        + (Fintype.card d * (Fintype.card d + 1) / 2 - 1) := by
  exact ae_funDimSkipsOn_tri_le_residual_add_mlp_oneBlock_rmsNorm_zero analyticOnNhd_tanh
    (fun _ hz => tanh_ne_zero_of_pos hz) μ hd hdIn hdOut

/-- **Theorem B.1 (iii) of the skips paper for `ε = 0`, "at most", for one GELU block:** for `d_in,
d_out ≥ d ≥ 2`, at almost every weights and triangular skip `(θ, A)` the functional dimension
exceeds that of the residual network with the weights `θ` by at most `d(d+1)/2 − 1`. -/
theorem ae_funDimSkipsOn_tri_le_residual_add_gelu_oneBlock_rmsNorm_zero
    [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm 0) hid) dIn dOut
      × (Fin 1 → upperTriangular d)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, funDimSkipsOn (Arch.mlp gelu (rmsNorm 0) hid)
        (triSkips d 1) p
        (learnedZeroDomain (Arch.mlp gelu (rmsNorm 0) hid) p.1
          fun ℓ => (p.2 ℓ : Matrix d d ℝ))
      ≤ funDimOn (Arch.mlp gelu (rmsNorm 0) hid) 1 p.1
          (residualZeroDomain (Arch.mlp gelu (rmsNorm 0) hid) p.1)
        + (Fintype.card d * (Fintype.card d + 1) / 2 - 1) := by
  exact ae_funDimSkipsOn_tri_le_residual_add_mlp_oneBlock_rmsNorm_zero analyticOnNhd_gelu
    (fun _ hz => gelu_ne_zero_of_pos hz) μ hd hdIn hdOut

/-- **Theorem B.1 (iii) of the skips paper for `ε = 0`, "at most", for one gated block with an
analytic gate that is nonzero on the positive reals:** for `d_in, d_out ≥ d ≥ 2`, at almost every
weights and triangular skip `(θ, A)` the functional dimension exceeds that of the residual
network with the weights `θ` by at most `d(d+1)/2 − 1`. -/
theorem ae_funDimSkipsOn_tri_le_residual_add_gated_oneBlock_rmsNorm_zero
    (hσa : AnalyticOnNhd ℝ σ Set.univ) (hσp : ∀ z, 0 < z → σ z ≠ 0)
    [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.gated (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut
      × (Fin 1 → upperTriangular d)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, funDimSkipsOn (Arch.gated σ (rmsNorm 0) hid)
        (triSkips d 1) p
        (learnedZeroDomain (Arch.gated σ (rmsNorm 0) hid) p.1
          fun ℓ => (p.2 ℓ : Matrix d d ℝ))
      ≤ funDimOn (Arch.gated σ (rmsNorm 0) hid) 1 p.1
          (residualZeroDomain (Arch.gated σ (rmsNorm 0) hid) p.1)
        + (Fintype.card d * (Fintype.card d + 1) / 2 - 1) := by
  have : Nonempty d := Fintype.card_pos_iff.1 (by omega)
  have hf : ∀ ℓ, AnalyticOnNhd ℝ ((Arch.gated (T := T) (d := d) σ (rmsNorm 0) hid).f ℓ)
      Set.univ :=
    fun ℓ => analyticOnNhd_f_gated hσa ℓ
  refine ae_funDimSkipsOn_tri_le_funDimOn_residual_add_rmsNorm_zero rfl hd (hf 0) μ ?_
  -- at almost every `θ`: `E` and `D` have rank `d`, and the input `w` of the proof exists
  filter_upwards [ae_turnGeneric _ (fun ℓ => continuousOn_univ.mp (hf ℓ).continuousOn)
    Measure.addHaar hd hdIn hdOut
      (ae_someBlockNonzero_gated hσp ⟨0, inferInstance⟩ Measure.addHaar),
    ae_exists_linearIndependent_rows_gated (continuousOn_univ.mp hσa.continuousOn) hσp
      Measure.addHaar hd hdIn hdOut] with θ hθ hw
  exact ⟨hθ.rank_E, hθ.rank_D, hw⟩

/-- **Theorem B.1 (iii) of the skips paper for `ε = 0`, "at most", for one SwiGLU block:** for
`d_in, d_out ≥ d ≥ 2`, at almost every weights and triangular skip `(θ, A)` the functional
dimension exceeds that of the residual network with the weights `θ` by at most `d(d+1)/2 − 1`. -/
theorem ae_funDimSkipsOn_tri_le_residual_add_swiglu_oneBlock_rmsNorm_zero
    [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.gated (T := T) (d := d) silu (rmsNorm 0) hid) dIn dOut
      × (Fin 1 → upperTriangular d)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, funDimSkipsOn (Arch.gated silu (rmsNorm 0) hid)
        (triSkips d 1) p
        (learnedZeroDomain (Arch.gated silu (rmsNorm 0) hid) p.1
          fun ℓ => (p.2 ℓ : Matrix d d ℝ))
      ≤ funDimOn (Arch.gated silu (rmsNorm 0) hid) 1 p.1
          (residualZeroDomain (Arch.gated silu (rmsNorm 0) hid) p.1)
        + (Fintype.card d * (Fintype.card d + 1) / 2 - 1) := by
  exact ae_funDimSkipsOn_tri_le_residual_add_gated_oneBlock_rmsNorm_zero analyticOnNhd_silu
    (fun _ hz => silu_ne_zero_of_pos hz) μ hd hdIn hdOut

/-- **Theorem B.1 (iii) of the skips paper for `ε = 0`, "at most", for one GeGLU block:** for
`d_in, d_out ≥ d ≥ 2`, at almost every weights and triangular skip `(θ, A)` the functional
dimension exceeds that of the residual network with the weights `θ` by at most `d(d+1)/2 − 1`. -/
theorem ae_funDimSkipsOn_tri_le_residual_add_geglu_oneBlock_rmsNorm_zero
    [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.gated (T := T) (d := d) gelu (rmsNorm 0) hid) dIn dOut
      × (Fin 1 → upperTriangular d)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, funDimSkipsOn (Arch.gated gelu (rmsNorm 0) hid)
        (triSkips d 1) p
        (learnedZeroDomain (Arch.gated gelu (rmsNorm 0) hid) p.1
          fun ℓ => (p.2 ℓ : Matrix d d ℝ))
      ≤ funDimOn (Arch.gated gelu (rmsNorm 0) hid) 1 p.1
          (residualZeroDomain (Arch.gated gelu (rmsNorm 0) hid) p.1)
        + (Fintype.card d * (Fintype.card d + 1) / 2 - 1) := by
  exact ae_funDimSkipsOn_tri_le_residual_add_gated_oneBlock_rmsNorm_zero analyticOnNhd_gelu
    (fun _ hz => gelu_ne_zero_of_pos hz) μ hd hdIn hdOut

/-- **Theorem B.1 (iii) of the skips paper for `ε = 0`, "at most", for one attention block with a
head of positive width and a mask in which every token sees some token:** for `d_in, d_out ≥ d ≥
2`, at almost every weights and triangular skip `(θ, A)` the functional dimension exceeds that of
the residual network with the weights `θ` by at most `d(d+1)/2 − 1`. -/
theorem ae_funDimSkipsOn_tri_le_residual_add_attention_oneBlock_rmsNorm_zero
    (sees : T → T → Prop) [DecidableRel sees] (hsees : ∀ t, ∃ s, sees t s)
    [Nonempty (H 0)] [Nonempty (dh 0)]
    (μ : Measure (Params (Arch.attention (T := T) (d := d) sees (rmsNorm 0) H dh) dIn dOut
      × (Fin 1 → upperTriangular d)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, funDimSkipsOn (Arch.attention sees (rmsNorm 0) H dh)
        (triSkips d 1) p
        (learnedZeroDomain (Arch.attention sees (rmsNorm 0) H dh) p.1
          fun ℓ => (p.2 ℓ : Matrix d d ℝ))
      ≤ funDimOn (Arch.attention sees (rmsNorm 0) H dh) 1 p.1
          (residualZeroDomain (Arch.attention sees (rmsNorm 0) H dh) p.1)
        + (Fintype.card d * (Fintype.card d + 1) / 2 - 1) := by
  have : Nonempty d := Fintype.card_pos_iff.1 (by omega)
  obtain ⟨t₁⟩ := (inferInstance : Nonempty T)
  obtain ⟨s₁, hs₁⟩ := hsees t₁
  have hf : ∀ ℓ, AnalyticOnNhd ℝ ((Arch.attention (T := T) (d := d) sees (rmsNorm 0) H dh).f ℓ)
      Set.univ :=
    fun ℓ => analyticOnNhd_f_attention sees _ H dh ℓ
  refine ae_funDimSkipsOn_tri_le_funDimOn_residual_add_rmsNorm_zero rfl hd (hf 0) μ ?_
  -- at almost every `θ`: `E` and `D` have rank `d`, and the input `w` of the proof exists
  filter_upwards [ae_turnGeneric _ (fun ℓ => continuousOn_univ.mp (hf ℓ).continuousOn)
    Measure.addHaar hd hdIn hdOut
      (ae_someBlockNonzero_attention ⟨0, inferInstance, inferInstance⟩ t₁ s₁ hs₁ Measure.addHaar),
    ae_exists_linearIndependent_rows_attention sees hsees Measure.addHaar hd hdIn hdOut]
    with θ hθ hw
  exact ⟨hθ.rank_E, hθ.rank_D, hw⟩

end Skips
