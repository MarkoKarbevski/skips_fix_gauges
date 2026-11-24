import SkipsLean.Depth.ComplexSuffix
import SkipsLean.Depth.StepZeroValues

/-!
# The identity for one block at complex rows, and its continuation along the path

Paper (dimension paper): Appendix D.6 (the case `ε = 0`), "The identity on the path" and
Lemma D.15 (Continuation).

"With the notation of (20) and (21), let `κ = κ_{k+1}`. The same formulas define `ż(n) ∈ ℂ^{1×q}`
for `n ∈ ℂ^{1×d}`, and `𝓛(w̃, w̃'; n)` for rows `w̃, w̃' ∈ ℂ^{1×q}` with `w̃V ∈ C_κ`. `𝓛` is
holomorphic in `w̃`, affine in `w̃'` and polynomial in `n`."

"Lemma D.15 (Continuation). In the case (0), let (22) hold, and let `ξ, ξ'` be orthonormal. Suppose
that for every real `t ≥ 1` the function `σ` is holomorphic at every `n(t) c_j` and
`σ(n(t)W) V ∈ C_κ`. Then `𝓛(σ(n(t)W), σ'(n(t)W); n(t)) = 0` for all real `t ≥ 1`."

Its proof: "The left side is a holomorphic function of `t` on an open set that contains `[1, ∞)`,
hence on a connected open neighborhood of `[1, ∞)`. This neighborhood contains an arc of the unit
circle around `t = 1`, on which `n(t) ∈ S` and the function vanishes by (22). So it vanishes on
the whole neighborhood."

Here: the formulas (20) and (21) at complex arguments are `zdotC` and `blockLHSC`, with the complex
derivatives of `suffixC` (`Depth/ComplexSuffix.lean`) in the place of the real derivatives of
`𝓑`; at real arguments they are the real `ż` and `𝓛` (`blockLHS`, `Depth/StepTanh.lean`). The
activation `σ` is extended by a map `σC : ℂ → ℂ`, and `σ'` on the path is the complex derivative
`deriv σC`. A hidden state has the rows `T`; the path is taken at every token, with a pair
`ξ, ξ'` per token (`pathMatrix`). Numbering as in `Depth/StepTanh.lean`: the block is `k : Fin L`,
the hidden state before it `k.castSucc` and after it `k.succ`.
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut] {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)] {σ σ' : ℝ → ℝ} {σC : ℂ → ℂ}

/-- The right side of equation (14) at a complex `n`, row by row: `n Z − (⟨n Z, n⟩/d) n`, with
`⟨u, v⟩ = u vᵀ` (no complex conjugation). -/
noncomputable def tangentRMSC (Z : Matrix d d ℝ) (n : Matrix T d ℂ) : Matrix T d ℂ :=
  Matrix.of fun t => (n * Z.map (fun x : ℝ => (x : ℂ))) t
    - (((n * Z.map (fun x : ℝ => (x : ℂ))) t ⬝ᵥ n t) / (Fintype.card d : ℂ)) • n t

/-- **Equation (20) at a complex `n`:** `ż(n) = (n Z − (⟨n Z, n⟩/d) n) W + n η_W`, for block `k`
with the read `W`. -/
noncomputable def zdotC (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
    (k : Fin L) (Z : Matrix d d ℝ)
    (η : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) (n : Matrix T d ℂ) :
    Matrix T (hid k) ℂ :=
  tangentRMSC Z n * θ.toC.1 k + n * η.toC.1 k

/-- **Equation (21) at complex arguments:**
`𝓛 = 𝐃𝓑(w̃ V) ((w̃' ⊙ ż) V + w̃ η_V) + 𝐃_θ 𝓑(w̃ V) η`, for block `k` with the write `V` and the
network `𝓑 = 𝓑_{>k+1}` after it, at complex `w̃`, `w̃'` and `ż`. The derivatives are the complex
derivatives of `suffixC σC`, in the hidden state and in the weights. -/
noncomputable def blockLHSC (σC : ℂ → ℂ)
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) (k : Fin L)
    (η : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
    (w w' zdot : Matrix T (hid k) ℂ) : Matrix T dOut ℂ :=
  fderiv ℂ (fun h' : Matrix T d ℂ => suffixC σC θ.toC k.succ h') (w * θ.toC.2.1 k)
      ((Matrix.of fun t j => w' t j * zdot t j) * θ.toC.2.1 k + w * η.toC.2.1 k)
    + fderiv ℂ (fun ω : CWeights d dOut hid => suffixC σC ω k.succ (w * θ.toC.2.1 k))
        θ.toC η.toC

/-- **The path at every token:** row `τ` is `n(t) = (√d/2)(t ν + ν̄/t)` for the pair `ξ = Ξ τ`,
`ξ' = Ξ' τ`. -/
noncomputable def pathMatrix (Ξ Ξ' : Matrix T d ℝ) (t : ℂ) : Matrix T d ℂ :=
  Matrix.of fun τ => pathRow (Ξ τ) (Ξ' τ) t

omit [Fintype T] [DecidableEq d] in
/-- At a real `n`, the complex `n Z − (⟨n Z, n⟩/d) n` is the real one. -/
theorem tangentRMSC_ofReal (Z : Matrix d d ℝ) (n : Matrix T d ℝ) :
    tangentRMSC Z (n.map (fun x : ℝ => (x : ℂ)))
      = (tangentRMS Z n).map (fun x : ℝ => (x : ℂ)) := by
  -- entry by entry: the cast of sums and products of reals
  ext t i
  simp only [tangentRMSC, tangentRMS, Matrix.of_apply, Matrix.map_apply, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul, Matrix.mul_apply, dotProduct]
  push_cast
  rfl

omit [Fintype T] in
/-- Helper: the cast of a product of real matrices is the product of the casts. -/
private theorem map_mul_ofReal_cbi {m n p : Type*} [Fintype n] (A : Matrix m n ℝ)
    (B : Matrix n p ℝ) :
    (A * B).map (fun x : ℝ => (x : ℂ))
      = A.map (fun x : ℝ => (x : ℂ)) * B.map (fun x : ℝ => (x : ℂ)) :=
  Matrix.map_mul (f := Complex.ofRealHom)

omit [Fintype T] in
/-- Helper: the cast of a sum of real matrices is the sum of the casts. -/
private theorem map_add_ofReal_cbi {m n : Type*} (A B : Matrix m n ℝ) :
    (A + B).map (fun x : ℝ => (x : ℂ))
      = A.map (fun x : ℝ => (x : ℂ)) + B.map (fun x : ℝ => (x : ℂ)) :=
  Matrix.map_add _ (fun a b => Complex.ofReal_add a b) A B

omit [Fintype dIn] [Fintype dOut] in
/-- At a real `n`, the complex `ż(n)` is the real `ż(n)` of equation (20). -/
theorem zdotC_ofReal (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
    (k : Fin L) (Z : Matrix d d ℝ)
    (η : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) (n : Matrix T d ℝ) :
    zdotC θ k Z η (n.map (fun x : ℝ => (x : ℂ)))
      = (tangentRMS Z n * θ.read k + n * η.read k).map (fun x : ℝ => (x : ℂ)) := by
  -- the cast of `A W + n η_W` is `A.map ↑ * W.map ↑ + n.map ↑ * η_W.map ↑`
  rw [map_add_ofReal_cbi, map_mul_ofReal_cbi, map_mul_ofReal_cbi, ← tangentRMSC_ofReal]
  rfl

/-- Helper: a real map `f` whose cast `c' ∘ f` is `G ∘ c` for a map `G` that is complex
differentiable at `y = c x`: the complex derivative of `G` along `u = c v` is the cast of the real
derivative of `f` along `v`. (`r` is a left inverse of `c'`, so that `f = r ∘ G ∘ c` is
differentiable.) -/
private theorem fderiv_ofReal_aux_cbi {E F E' F' : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup E']
    [NormedSpace ℂ E'] [NormedSpace ℝ E'] [IsScalarTower ℝ ℂ E'] [NormedAddCommGroup F']
    [NormedSpace ℂ F'] [NormedSpace ℝ F'] [IsScalarTower ℝ ℂ F']
    (f : E → F) (G : E' → F') (c : E →L[ℝ] E') (c' : F →L[ℝ] F') (r : F' →L[ℝ] F)
    (hr : ∀ y, r (c' y) = y) (hfG : ∀ x, c' (f x) = G (c x)) (x : E) (y : E') (hy : c x = y)
    (hG : DifferentiableAt ℂ G y) (v : E) (u : E') (hu : c v = u) :
    fderiv ℂ G y u = c' (fderiv ℝ f x v) := by
  subst hy hu
  -- the real derivative of `G ∘ c`
  have h1 : HasFDerivAt (fun y => G (c y))
      (((fderiv ℂ G (c x)).restrictScalars ℝ).comp c) x :=
    (hG.hasFDerivAt.restrictScalars ℝ).comp x c.hasFDerivAt
  -- `f = r ∘ G ∘ c` is differentiable
  have hf : f = fun y => r (G (c y)) := funext fun y => by rw [← hfG, hr]
  have hfd : DifferentiableAt ℝ f x := by
    rw [hf]
    exact (r.hasFDerivAt.comp x h1).differentiableAt
  -- so `c' ∘ f = G ∘ c` also has the derivative `c' ∘ 𝐃f(x)`; uniqueness
  have h2 : HasFDerivAt (fun y => G (c y)) (c'.comp (fderiv ℝ f x)) x := by
    have h3 := c'.hasFDerivAt.comp x hfd.hasFDerivAt
    have e : (fun y => G (c y)) = c' ∘ f := funext fun y => (hfG y).symm
    rw [e]
    exact h3
  exact congrArg (fun L : E →L[ℝ] F' => L v) (h1.unique h2)

omit [Fintype T] in
/-- Helper: the cast of `c • A` for a real `c`. -/
private theorem map_smul_ofReal_cbi {m n : Type*} (c : ℝ) (A : Matrix m n ℝ) :
    (c • A).map (fun x : ℝ => (x : ℂ)) = c • A.map (fun x : ℝ => (x : ℂ)) := by
  ext i j
  simp [Complex.real_smul]

omit [Fintype T] in
/-- Helper: the cast of real matrices to complex matrices, as a real continuous linear map. -/
private noncomputable def castCLM_cbi (m n : Type*) [Fintype m] [Fintype n] :
    Matrix m n ℝ →L[ℝ] Matrix m n ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => M.map (fun x : ℝ => (x : ℂ))
      map_add' := map_add_ofReal_cbi
      map_smul' := map_smul_ofReal_cbi }

omit [Fintype T] in
/-- Helper: the real part of complex matrices, as a real continuous linear map. -/
private noncomputable def reCLM_cbi (m n : Type*) [Fintype m] [Fintype n] :
    Matrix m n ℂ →L[ℝ] Matrix m n ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => M.map Complex.re
      map_add' := fun A B => by ext i j; simp
      map_smul' := fun c A => by ext i j; simp [Complex.real_smul] }

omit [Fintype T] in
/-- Helper: the real part of the cast is the matrix. -/
private theorem reCLM_castCLM_cbi {m n : Type*} [Fintype m] [Fintype n] (M : Matrix m n ℝ) :
    reCLM_cbi m n (castCLM_cbi m n M) = M := by
  ext i j
  simp [reCLM_cbi, castCLM_cbi]

/-- **`𝐃𝓑_{>k}` extends:** if `𝓑_{>k}` is holomorphic on a cone `C_κ`, `κ > 0`, then at a real
hidden state `h` without a zero row the complex derivative of `suffixC` in the hidden state, along
a real direction `v`, is the real derivative `𝐃𝓑_{>k}(h) v`. -/
theorem fderiv_suffixC_ofReal (hσ : ∀ x : ℝ, σC (x : ℂ) = ((σ x : ℝ) : ℂ))
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) (k : Fin (L + 1))
    {κ : ℝ} (hκ : 0 < κ) (hhol : HolomorphicOnCone σC θ k κ)
    (h v : Matrix T d ℝ) (hh : ∀ t, h t ≠ 0) :
    fderiv ℂ (fun h' : Matrix T d ℂ => suffixC σC θ.toC k h')
        (h.map (fun x : ℝ => (x : ℂ))) (v.map (fun x : ℝ => (x : ℂ)))
      = (fderiv ℝ (fun h' : Matrix T d ℝ => suffix (Arch.mlp σ (rmsNorm 0) hid) 0 θ k h')
          h v).map (fun x : ℝ => (x : ℂ)) := by
  -- `suffixC` is holomorphic at the real `h`, whose rows are in the cone
  have ha := hhol (h.map (fun x : ℝ => (x : ℂ))) fun t => ofReal_mem_complexCone hκ (h t) (hh t)
  have hi : AnalyticAt ℂ (fun h' : Matrix T d ℂ => ((θ.toC, h') : CWeights d dOut hid × _))
      (h.map (fun x : ℝ => (x : ℂ))) := analyticAt_const.prod analyticAt_id
  have hG : DifferentiableAt ℂ (fun h' : Matrix T d ℂ => suffixC σC θ.toC k h')
      (h.map (fun x : ℝ => (x : ℂ))) := (ha.comp hi).differentiableAt
  -- `suffixC` extends `suffix` (`suffixC_ofReal`)
  exact fderiv_ofReal_aux_cbi (fun h' => suffix (Arch.mlp σ (rmsNorm 0) hid) 0 θ k h')
    (fun h' => suffixC σC θ.toC k h') (castCLM_cbi T d) (castCLM_cbi T dOut) (reCLM_cbi T dOut)
    reCLM_castCLM_cbi (fun x => (suffixC_ofReal hσ θ k x).symm) h _ rfl hG v _ rfl

/-- Helper: `θ ↦ θ.toC` as a real continuous linear map. -/
private noncomputable def toCCLM_cbi :
    Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut →L[ℝ] CWeights d dOut hid :=
  LinearMap.toContinuousLinearMap
    { toFun := fun θ' => θ'.toC
      map_add' := fun _ _ => Prod.ext (funext fun _ => map_add_ofReal_cbi _ _)
        (Prod.ext (funext fun _ => map_add_ofReal_cbi _ _) (map_add_ofReal_cbi _ _))
      map_smul' := fun _ _ => Prod.ext (funext fun _ => map_smul_ofReal_cbi _ _)
        (Prod.ext (funext fun _ => map_smul_ofReal_cbi _ _) (map_smul_ofReal_cbi _ _)) }

omit [Fintype T] [DecidableEq d] in
/-- Helper: the value of `toCCLM_cbi`. -/
private theorem toCCLM_cbi_apply
    (θ' : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) :
    toCCLM_cbi θ' = θ'.toC := rfl

/-- **`𝐃_θ𝓑_{>k}` extends:** under the same hypotheses, the complex derivative of `suffixC` in the
weights, at the real weights `θ` and along a real direction `η`, is the real derivative
`𝐃_θ𝓑_{>k}(h) η`. -/
theorem fderiv_weights_suffixC_ofReal (hσ : ∀ x : ℝ, σC (x : ℂ) = ((σ x : ℝ) : ℂ))
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) (k : Fin (L + 1))
    {κ : ℝ} (hκ : 0 < κ) (hhol : HolomorphicOnCone σC θ k κ)
    (h : Matrix T d ℝ) (hh : ∀ t, h t ≠ 0)
    (η : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) :
    fderiv ℂ (fun ω : CWeights d dOut hid => suffixC σC ω k (h.map (fun x : ℝ => (x : ℂ))))
        θ.toC η.toC
      = (fderiv ℝ (fun θ' : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut =>
          suffix (Arch.mlp σ (rmsNorm 0) hid) 0 θ' k h) θ η).map (fun x : ℝ => (x : ℂ)) := by
  -- `suffixC` is holomorphic at the real weights, at the real `h`
  have ha := hhol (h.map (fun x : ℝ => (x : ℂ))) fun t => ofReal_mem_complexCone hκ (h t) (hh t)
  have hi : AnalyticAt ℂ (fun ω : CWeights d dOut hid =>
      ((ω, h.map (fun x : ℝ => (x : ℂ))) : CWeights d dOut hid × Matrix T d ℂ)) θ.toC :=
    analyticAt_id.prod analyticAt_const
  have hG : DifferentiableAt ℂ (fun ω : CWeights d dOut hid =>
      suffixC σC ω k (h.map (fun x : ℝ => (x : ℂ)))) θ.toC :=
    (ha.comp_of_eq hi rfl).differentiableAt
  -- `suffixC` extends `suffix`, at all real weights (`suffixC_ofReal`)
  have hfG : ∀ θ' : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut,
      castCLM_cbi T dOut (suffix (Arch.mlp σ (rmsNorm 0) hid) 0 θ' k h)
        = suffixC σC (toCCLM_cbi θ') k (h.map (fun x : ℝ => (x : ℂ))) := by
    intro θ'
    rw [toCCLM_cbi_apply]
    exact (suffixC_ofReal hσ θ' k h).symm
  -- (the hypotheses as later goals: elaborated as arguments they time out)
  have key := fderiv_ofReal_aux_cbi (fun θ' => suffix (Arch.mlp σ (rmsNorm 0) hid) 0 θ' k h)
    (fun ω => suffixC σC ω k (h.map (fun x : ℝ => (x : ℂ)))) toCCLM_cbi (castCLM_cbi T dOut)
    (reCLM_cbi T dOut) reCLM_castCLM_cbi ?_ θ θ.toC ?_ hG η η.toC ?_
  · exact key
  · exact hfG
  · exact toCCLM_cbi_apply θ
  · exact toCCLM_cbi_apply η

/-- **"The same formulas define `𝓛`":** at real `w̃`, `w̃'` and `ż`, with `w̃ V` without a zero
row, the complex `𝓛` is the real `𝓛` of equation (21). -/
theorem blockLHSC_ofReal (hσ : ∀ x : ℝ, σC (x : ℂ) = ((σ x : ℝ) : ℂ))
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) (k : Fin L)
    {κ : ℝ} (hκ : 0 < κ) (hhol : HolomorphicOnCone σC θ k.succ κ)
    (η : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
    (w w' zdot : Matrix T (hid k) ℝ) (hw : ∀ t, (w * θ.write k) t ≠ 0) :
    blockLHSC σC θ k η (w.map (fun x : ℝ => (x : ℂ))) (w'.map (fun x : ℝ => (x : ℂ)))
        (zdot.map (fun x : ℝ => (x : ℂ)))
      = (blockLHS θ k η w w' zdot).map (fun x : ℝ => (x : ℂ)) := by
  -- the point `w̃ V` and the direction `(w̃' ⊙ ż) V + w̃ η_V` are the casts of the real ones
  have e1 : w.map (fun x : ℝ => (x : ℂ)) * θ.toC.2.1 k
      = (w * θ.write k).map (fun x : ℝ => (x : ℂ)) := (map_mul_ofReal_cbi _ _).symm
  have e2 : (Matrix.of fun t j => w'.map (fun x : ℝ => (x : ℂ)) t j
        * zdot.map (fun x : ℝ => (x : ℂ)) t j) * θ.toC.2.1 k
        + w.map (fun x : ℝ => (x : ℂ)) * η.toC.2.1 k
      = ((Matrix.of fun t j => w' t j * zdot t j) * θ.write k
        + w * η.write k).map (fun x : ℝ => (x : ℂ)) := by
    rw [map_add_ofReal_cbi, map_mul_ofReal_cbi, map_mul_ofReal_cbi]
    congr 2
    ext t j
    simp
  -- both derivatives extend (`fderiv_suffixC_ofReal`, `fderiv_weights_suffixC_ofReal`)
  unfold blockLHSC blockLHS
  rw [e1, e2, fderiv_suffixC_ofReal hσ θ k.succ hκ hhol _ _ hw,
    fderiv_weights_suffixC_ofReal hσ θ k.succ hκ hhol _ hw η, map_add_ofReal_cbi]

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (as `analyticAt_matrix_mul_cs` of `Depth/ComplexSuffix.lean`): the matrix product of
two analytic matrix-valued maps is analytic. -/
private theorem analyticAt_matrix_mul_cbi {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
    {f : E → Matrix m n ℂ} {g : E → Matrix n p ℂ} {x : E}
    (hf : AnalyticAt ℂ f x) (hg : AnalyticAt ℂ g x) :
    AnalyticAt ℂ (fun y => f y * g y) x := by
  -- matrix multiplication as a bilinear map
  let B : Matrix m n ℂ →ₗ[ℂ] Matrix n p ℂ →ₗ[ℂ] Matrix m p ℂ :=
    LinearMap.mk₂ ℂ (fun a b => a * b) Matrix.add_mul (fun c a b => Matrix.smul_mul c a b)
      Matrix.mul_add (fun c a b => Matrix.mul_smul a c b)
  -- the same map with continuous linear maps (all spaces are finite-dimensional)
  let B' : Matrix m n ℂ →L[ℂ] Matrix n p ℂ →L[ℂ] Matrix m p ℂ :=
    LinearMap.toContinuousLinearMap
      ((LinearMap.toContinuousLinearMap :
        (Matrix n p ℂ →ₗ[ℂ] Matrix m p ℂ) ≃ₗ[ℂ] (Matrix n p ℂ →L[ℂ] Matrix m p ℂ)).toLinearMap ∘ₗ B)
  have hB : (fun y => f y * g y) = fun y => B' (f y) (g y) := rfl
  rw [hB]
  exact (B'.analyticAt_bilinear (f x, g x)).comp₂ hf hg

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: an entry of an analytic matrix-valued map is analytic. -/
private theorem analyticAt_entry_cbi {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {m n : Type*} [Fintype m] [Fintype n] {F : E → Matrix m n ℂ} {x : E}
    (hF : AnalyticAt ℂ F x) (i : m) (j : n) : AnalyticAt ℂ (fun y => F y i j) x := by
  have he : AnalyticAt ℂ (fun M : Matrix m n ℂ => M i j) (F x) :=
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : n => ℂ) j).comp
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : m => n → ℂ) i)).analyticAt _
  exact AnalyticAt.comp (f := F) he hF

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: if `F` is analytic at `x` and `s` is analytic at every entry of `F x`, then
`y ↦ s(F y)` (entrywise) is analytic at `x`. -/
private theorem analyticAt_map_cbi {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {m n : Type*} [Fintype m] [Fintype n] {s : ℂ → ℂ} {F : E → Matrix m n ℂ} {x : E}
    (hF : AnalyticAt ℂ F x) (hs : ∀ i j, AnalyticAt ℂ s (F x i j)) :
    AnalyticAt ℂ (fun y => (F y).map s) x := by
  show AnalyticAt ℂ (fun y => fun i => fun j => s (F y i j)) x
  exact AnalyticAt.pi fun i => AnalyticAt.pi fun j =>
    AnalyticAt.comp (f := fun y => F y i j) (hs i j) (analyticAt_entry_cbi hF i j)

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the entrywise product of two analytic matrix-valued maps is analytic. -/
private theorem analyticAt_hadamard_cbi {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {m n : Type*} [Fintype m] [Fintype n] {A B : E → Matrix m n ℂ} {x : E}
    (hA : AnalyticAt ℂ A x) (hB : AnalyticAt ℂ B x) :
    AnalyticAt ℂ (fun y => Matrix.of fun i j => A y i j * B y i j) x := by
  show AnalyticAt ℂ (fun y => fun i => fun j => A y i j * B y i j) x
  exact AnalyticAt.pi fun i => AnalyticAt.pi fun j =>
    (analyticAt_entry_cbi hA i j).mul (analyticAt_entry_cbi hB i j)

omit [DecidableEq d] in
/-- Helper: the path `t ↦ n(t)` is analytic at every `t₀ ≠ 0` (its entries are polynomials in `t`
and `t⁻¹`). -/
private theorem analyticAt_pathMatrix_cbi (Ξ Ξ' : Matrix T d ℝ) {t₀ : ℂ} (ht₀ : t₀ ≠ 0) :
    AnalyticAt ℂ (pathMatrix Ξ Ξ') t₀ := by
  show AnalyticAt ℂ (fun t => fun τ => fun i => pathRow (Ξ τ) (Ξ' τ) t i) t₀
  refine AnalyticAt.pi fun τ => AnalyticAt.pi fun i => ?_
  exact analyticAt_const.mul ((analyticAt_id.mul analyticAt_const).add
    ((analyticAt_id.inv ht₀).mul analyticAt_const))

omit [DecidableEq d] in
/-- Helper: `n ↦ n Z − (⟨n Z, n⟩/d) n` after an analytic map is analytic (a polynomial). -/
private theorem analyticAt_tangentRMSC_cbi {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (Z : Matrix d d ℝ) {N : E → Matrix T d ℂ} {x : E} (hN : AnalyticAt ℂ N x) :
    AnalyticAt ℂ (fun y => tangentRMSC Z (N y)) x := by
  have hNZ : AnalyticAt ℂ (fun y => N y * Z.map (fun x : ℝ => (x : ℂ))) x :=
    analyticAt_matrix_mul_cbi hN analyticAt_const
  show AnalyticAt ℂ (fun y => fun τ => fun i => (N y * Z.map (fun x : ℝ => (x : ℂ))) τ i
    - ((N y * Z.map (fun x : ℝ => (x : ℂ))) τ ⬝ᵥ N y τ) / (Fintype.card d : ℂ) * N y τ i) x
  refine AnalyticAt.pi fun τ => AnalyticAt.pi fun i => ?_
  have hdot : AnalyticAt ℂ (fun y => (N y * Z.map (fun x : ℝ => (x : ℂ))) τ ⬝ᵥ N y τ) x :=
    Finset.analyticAt_fun_sum _ fun j _ =>
      (analyticAt_entry_cbi hNZ τ j).mul (analyticAt_entry_cbi hN τ j)
  exact (analyticAt_entry_cbi hNZ τ i).sub (hdot.div_const.mul (analyticAt_entry_cbi hN τ i))

/-- Helper (the complex copy of `fderiv_partial_add_szv` of `Depth/StepZeroValues.lean`): the two
partial derivatives of a map of `(x, y)` that is differentiable at `(x, y)` add up to its
derivative. -/
private theorem fderiv_partial_add_cbi {E₁ E₂ F : Type*} [NormedAddCommGroup E₁]
    [NormedSpace ℂ E₁] [NormedAddCommGroup E₂] [NormedSpace ℂ E₂] [NormedAddCommGroup F]
    [NormedSpace ℂ F] {Φ : E₁ → E₂ → F} {x : E₁} {y : E₂}
    (hΦ : DifferentiableAt ℂ (fun p : E₁ × E₂ => Φ p.1 p.2) (x, y)) (a : E₁) (b : E₂) :
    fderiv ℂ (fun y' => Φ x y') y b + fderiv ℂ (fun x' => Φ x' y) x a
      = fderiv ℂ (fun p : E₁ × E₂ => Φ p.1 p.2) (x, y) (a, b) := by
  have h1 : HasFDerivAt (fun x' => Φ x' y)
      ((fderiv ℂ (fun p : E₁ × E₂ => Φ p.1 p.2) (x, y)).comp
        (ContinuousLinearMap.inl ℂ E₁ E₂)) x := by
    have hc := hΦ.hasFDerivAt.comp x (hasFDerivAt_prodMk_left (𝕜 := ℂ) x y)
    exact hc
  have h2 : HasFDerivAt (fun y' => Φ x y')
      ((fderiv ℂ (fun p : E₁ × E₂ => Φ p.1 p.2) (x, y)).comp
        (ContinuousLinearMap.inr ℂ E₁ E₂)) y := by
    have hc := hΦ.hasFDerivAt.comp y (hasFDerivAt_prodMk_right (𝕜 := ℂ) x y)
    exact hc
  rw [h1.fderiv, h2.fderiv, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.inl_apply, ContinuousLinearMap.inr_apply, ← map_add, Prod.mk_add_mk,
    zero_add, add_zero]

omit [DecidableEq d] [Fintype dIn] in
/-- Helper, step (a) of the proof of Lemma D.15: at a real `t₀ ≥ 1` where `σC` is holomorphic at
the entries of `n(t₀) W` and the rows of `σC(n(t₀) W) V` are in the cone, `t ↦ 𝓛(t)` is analytic.
Near `t₀`, `𝓑_{>k+1}` is holomorphic at `(θ, σC(n(t) W) V)`, so `𝓛(t)` is its joint derivative
applied to `(η, (w̃' ⊙ ż) V + w̃ η_V)`, which is analytic in `t`. -/
private theorem analyticAt_blockLHSC_path_cbi
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) (k : Fin L)
    {κ : ℝ} (hhol : HolomorphicOnCone σC θ k.succ κ)
    (Z : Matrix d d ℝ) (η : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
    (Ξ Ξ' : Matrix T d ℝ) (t₀ : ℝ) (ht₀ : 1 ≤ t₀)
    (hσan : ∀ τ j, AnalyticAt ℂ σC ((pathMatrix Ξ Ξ' (t₀ : ℂ) * θ.toC.1 k) τ j))
    (hcone : ∀ τ, ((pathMatrix Ξ Ξ' (t₀ : ℂ) * θ.toC.1 k).map σC * θ.toC.2.1 k) τ
      ∈ complexCone κ) :
    AnalyticAt ℂ (fun t : ℂ => blockLHSC σC θ k η ((pathMatrix Ξ Ξ' t * θ.toC.1 k).map σC)
        ((pathMatrix Ξ Ξ' t * θ.toC.1 k).map (deriv σC))
        (zdotC θ k Z η (pathMatrix Ξ Ξ' t))) (t₀ : ℂ) := by
  have ht0 : (t₀ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (by linarith)
  -- the path, the inputs of the hidden units and their outputs are analytic at `t₀`
  have hN := analyticAt_pathMatrix_cbi Ξ Ξ' ht0
  have hM : AnalyticAt ℂ (fun t => pathMatrix Ξ Ξ' t * θ.toC.1 k) (t₀ : ℂ) :=
    analyticAt_matrix_mul_cbi hN analyticAt_const
  have hw : AnalyticAt ℂ (fun t => (pathMatrix Ξ Ξ' t * θ.toC.1 k).map σC) (t₀ : ℂ) :=
    analyticAt_map_cbi hM hσan
  have hw' : AnalyticAt ℂ (fun t => (pathMatrix Ξ Ξ' t * θ.toC.1 k).map (deriv σC)) (t₀ : ℂ) :=
    analyticAt_map_cbi hM fun τ j => (hσan τ j).deriv
  have hz : AnalyticAt ℂ (fun t => zdotC θ k Z η (pathMatrix Ξ Ξ' t)) (t₀ : ℂ) :=
    (analyticAt_matrix_mul_cbi (analyticAt_tangentRMSC_cbi Z hN) analyticAt_const).add
      (analyticAt_matrix_mul_cbi hN analyticAt_const)
  have hwV : AnalyticAt ℂ (fun t => (pathMatrix Ξ Ξ' t * θ.toC.1 k).map σC * θ.toC.2.1 k)
      (t₀ : ℂ) := analyticAt_matrix_mul_cbi hw analyticAt_const
  have hdir : AnalyticAt ℂ (fun t =>
      (Matrix.of fun τ j => (pathMatrix Ξ Ξ' t * θ.toC.1 k).map (deriv σC) τ j
        * zdotC θ k Z η (pathMatrix Ξ Ξ' t) τ j) * θ.toC.2.1 k
      + (pathMatrix Ξ Ξ' t * θ.toC.1 k).map σC * η.toC.2.1 k) (t₀ : ℂ) :=
    (analyticAt_matrix_mul_cbi (analyticAt_hadamard_cbi hw' hz) analyticAt_const).add
      (analyticAt_matrix_mul_cbi hw analyticAt_const)
  -- `𝓑_{>k+1}` is holomorphic at `(θ, σ(n(t₀) W) V)`
  have hΦ0 : AnalyticAt ℂ (fun p : CWeights d dOut hid × Matrix T d ℂ => suffixC σC p.1 k.succ p.2)
      (θ.toC, (pathMatrix Ξ Ξ' (t₀ : ℂ) * θ.toC.1 k).map σC * θ.toC.2.1 k) := hhol _ hcone
  have hp : AnalyticAt ℂ (fun t : ℂ => ((θ.toC, (pathMatrix Ξ Ξ' t * θ.toC.1 k).map σC
      * θ.toC.2.1 k) : CWeights d dOut hid × Matrix T d ℂ)) (t₀ : ℂ) := analyticAt_const.prod hwV
  -- the right side `𝐃Φ(θ, w̃V)(η, (w̃' ⊙ ż) V + w̃ η_V)` is analytic at `t₀`
  have hDp := hΦ0.fderiv.comp_of_eq hp rfl
  have hq : AnalyticAt ℂ (fun t : ℂ => ((η.toC,
      (Matrix.of fun τ j => (pathMatrix Ξ Ξ' t * θ.toC.1 k).map (deriv σC) τ j
        * zdotC θ k Z η (pathMatrix Ξ Ξ' t) τ j) * θ.toC.2.1 k
      + (pathMatrix Ξ Ξ' t * θ.toC.1 k).map σC * η.toC.2.1 k) : CWeights d dOut hid × Matrix T d ℂ))
      (t₀ : ℂ) := analyticAt_const.prod hdir
  have hR := ((ContinuousLinearMap.id ℂ _).analyticAt_bilinear _).comp₂ hDp hq
  -- near `t₀`, `𝓑_{>k+1}` is holomorphic at `(θ, w̃V)`, and the two partial derivatives of `𝓛`
  -- add up to this derivative
  have hev := hp.continuousAt.eventually hΦ0.eventually_analyticAt
  refine hR.congr (hev.mono fun t ht => ?_)
  exact (fderiv_partial_add_cbi (Φ := fun ω h' => suffixC σC ω k.succ h') ht.differentiableAt
    _ _).symm


omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: at a real point the complex derivative of `σC` is `σ'` (the restriction of `σC` to
the reals is `σ`; uniqueness of the derivative). -/
private theorem deriv_ofReal_cbi (hσd : ∀ z, HasDerivAt σ (σ' z) z)
    (hσ : ∀ x : ℝ, σC (x : ℂ) = ((σ x : ℝ) : ℂ)) (hσC : ∀ x : ℝ, AnalyticAt ℂ σC (x : ℂ))
    (x : ℝ) : deriv σC (x : ℂ) = ((σ' x : ℝ) : ℂ) := by
  have h1 : HasDerivAt (fun y : ℝ => σC (y : ℂ)) (deriv σC (x : ℂ)) x :=
    (hσC x).differentiableAt.hasDerivAt.comp_ofReal
  have h2 : HasDerivAt (fun y : ℝ => ((σ y : ℝ) : ℂ)) ((σ' x : ℝ) : ℂ) x := (hσd x).ofReal_comp
  have e : (fun y : ℝ => σC (y : ℂ)) = fun y => ((σ y : ℝ) : ℂ) := funext hσ
  rw [e] at h1
  exact h1.unique h2

omit [Fintype T] [DecidableEq d] in
/-- Helper: on the unit circle the path is real: `n(e^{iφ})` has the rows
`√d (cos φ ξ − sin φ ξ')`. -/
private theorem pathMatrix_exp_mul_I_cbi (Ξ Ξ' : Matrix T d ℝ) (φ : ℝ) :
    pathMatrix Ξ Ξ' (Complex.exp (φ * Complex.I))
      = (Matrix.of fun τ i => Real.sqrt (Fintype.card d)
          * (Real.cos φ * Ξ τ i - Real.sin φ * Ξ' τ i)).map (fun x : ℝ => (x : ℂ)) := by
  ext τ i
  exact pathRow_exp_mul_I (Ξ τ) (Ξ' τ) φ i

omit [Fintype T] [DecidableEq d] in
/-- Helper: for orthonormal `ξ, ξ'` the row `√d (cos φ ξ − sin φ ξ')` is on the sphere
`‖n‖² = d`. -/
private theorem circle_dotProduct_self_cbi (ξ ξ' : d → ℝ) (hξ : ξ ⬝ᵥ ξ = 1)
    (hξ' : ξ' ⬝ᵥ ξ' = 1) (hξξ' : ξ ⬝ᵥ ξ' = 0) (φ : ℝ) :
    (fun i => Real.sqrt (Fintype.card d) * (Real.cos φ * ξ i - Real.sin φ * ξ' i))
      ⬝ᵥ (fun i => Real.sqrt (Fintype.card d) * (Real.cos φ * ξ i - Real.sin φ * ξ' i))
      = (Fintype.card d : ℝ) := by
  -- expand the square: `d (cos² ⟨ξ, ξ⟩ − 2 cos sin ⟨ξ, ξ'⟩ + sin² ⟨ξ', ξ'⟩)`
  have key : (fun i => Real.sqrt (Fintype.card d) * (Real.cos φ * ξ i - Real.sin φ * ξ' i))
      ⬝ᵥ (fun i => Real.sqrt (Fintype.card d) * (Real.cos φ * ξ i - Real.sin φ * ξ' i))
      = Real.sqrt (Fintype.card d) ^ 2 * (Real.cos φ ^ 2 * (ξ ⬝ᵥ ξ)
        - 2 * Real.cos φ * Real.sin φ * (ξ ⬝ᵥ ξ') + Real.sin φ ^ 2 * (ξ' ⬝ᵥ ξ')) := by
    simp only [dotProduct, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [key, hξ, hξ', hξξ', Real.sq_sqrt (Nat.cast_nonneg _)]
  linear_combination (Fintype.card d : ℝ) * Real.cos_sq_add_sin_sq φ

/-- Helper, step (c) of the proof of Lemma D.15: the points `e^{i/(m+1)}` of the unit circle tend
to `1` and differ from `1` (their imaginary part `sin (1/(m+1))` is positive). -/
private theorem tendsto_exp_mul_I_cbi :
    Filter.Tendsto (fun m : ℕ => Complex.exp ((((1 : ℝ) / ((m : ℝ) + 1) : ℝ) : ℂ) * Complex.I))
      Filter.atTop (nhdsWithin (1 : ℂ) {1}ᶜ) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, Filter.Eventually.of_forall fun m => ?_⟩
  · -- `1/(m+1) → 0` and `φ ↦ e^{iφ}` is continuous, with `e^0 = 1`
    have h0 : Filter.Tendsto (fun m : ℕ => (1 : ℝ) / ((m : ℝ) + 1)) Filter.atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hc : Continuous fun φ : ℝ => Complex.exp ((φ : ℂ) * Complex.I) := by fun_prop
    have h1 := (hc.tendsto 0).comp h0
    have e : Complex.exp (((0 : ℝ) : ℂ) * Complex.I) = 1 := by simp
    rw [e] at h1
    exact h1
  · -- `0 < 1/(m+1) ≤ 1 < π`, so `Im e^{i/(m+1)} = sin (1/(m+1)) > 0`
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro h
    have him := congrArg Complex.im h
    rw [Complex.exp_ofReal_mul_I_im, Complex.one_im] at him
    have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    have hle : (1 : ℝ) / ((m : ℝ) + 1) ≤ 1 := by
      rw [div_le_one hm]
      linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
    have hpos : 0 < Real.sin ((1 : ℝ) / ((m : ℝ) + 1)) :=
      Real.sin_pos_of_pos_of_lt_pi (by positivity)
        (lt_of_le_of_lt hle (by linarith [Real.pi_gt_three]))
    linarith

/-- **Lemma D.15 of the dimension paper (Continuation).** In the case (0), for an MLP block with a
real-analytic activation `σ` (derivative `σ'`) that extends to a map `σC` holomorphic at every real
point, let `θ` be regular, let `𝓑_{>k+1}` be holomorphic on the cone `C_κ`, and let the identity
(16) hold before block `k` for `Z` and `η` (equivalently (22), by
`suffixFlatZero_castSucc_iff_mlp_sphere`). Let `ξ, ξ'` be orthonormal at every token. Suppose that
for every real `t ≥ 1` the map `σC` is holomorphic at every `n(t) c_j` and every row of
`σC(n(t) W) V` is in `C_κ`. Then `𝓛(σC(n(t)W), σC'(n(t)W); n(t)) = 0` for all real `t ≥ 1`. -/
theorem blockLHSC_pathMatrix_eq_zero [Nonempty d] (hσd : ∀ z, HasDerivAt σ (σ' z) z)
    (hσa : AnalyticOnNhd ℝ σ Set.univ) (hσ : ∀ x : ℝ, σC (x : ℂ) = ((σ x : ℝ) : ℂ))
    (hσC : ∀ x : ℝ, AnalyticAt ℂ σC (x : ℂ))
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
    (hθ : RegularZero (Arch.mlp σ (rmsNorm 0) hid) θ) (k : Fin L)
    {κ : ℝ} (hκ : 0 < κ) (hhol : HolomorphicOnCone σC θ k.succ κ)
    (Z : Matrix d d ℝ) (η : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
    (h16 : SuffixFlatZero (Arch.mlp σ (rmsNorm 0) hid) θ k.castSucc Z η)
    (Ξ Ξ' : Matrix T d ℝ) (hΞ : ∀ τ, Ξ τ ⬝ᵥ Ξ τ = 1) (hΞ' : ∀ τ, Ξ' τ ⬝ᵥ Ξ' τ = 1)
    (hΞΞ' : ∀ τ, Ξ τ ⬝ᵥ Ξ' τ = 0)
    (hpath : ∀ t : ℝ, 1 ≤ t →
      (∀ τ j, AnalyticAt ℂ σC ((pathMatrix Ξ Ξ' (t : ℂ) * θ.toC.1 k) τ j)) ∧
      ∀ τ, ((pathMatrix Ξ Ξ' (t : ℂ) * θ.toC.1 k).map σC * θ.toC.2.1 k) τ ∈ complexCone κ) :
    ∀ t : ℝ, 1 ≤ t →
      blockLHSC σC θ k η ((pathMatrix Ξ Ξ' (t : ℂ) * θ.toC.1 k).map σC)
        ((pathMatrix Ξ Ξ' (t : ℂ) * θ.toC.1 k).map (deriv σC))
        (zdotC θ k Z η (pathMatrix Ξ Ξ' (t : ℂ))) = 0 := by
  -- `𝓛` along the path, as a function of the complex variable `t`
  obtain ⟨G, hG⟩ : ∃ G : ℂ → Matrix T dOut ℂ, G = fun t =>
      blockLHSC σC θ k η ((pathMatrix Ξ Ξ' t * θ.toC.1 k).map σC)
        ((pathMatrix Ξ Ξ' t * θ.toC.1 k).map (deriv σC)) (zdotC θ k Z η (pathMatrix Ξ Ξ' t)) :=
    ⟨_, rfl⟩
  -- (a) `G` is analytic at every real `t₀ ≥ 1`
  have hGan : AnalyticOnNhd ℂ G ((fun t : ℝ => (t : ℂ)) '' Set.Ici 1) := by
    rintro _ ⟨t₀, ht₀, rfl⟩
    rw [hG]
    exact analyticAt_blockLHSC_path_cbi θ k hhol Z η Ξ Ξ' t₀ ht₀ (hpath t₀ ht₀).1
      (hpath t₀ ht₀).2
  -- (b) `G` vanishes on the unit circle, where the path is real and on the sphere: (22)
  have hb : ∀ φ : ℝ, G (Complex.exp (φ * Complex.I)) = 0 := by
    intro φ
    obtain ⟨n, hn_def⟩ : ∃ n : Matrix T d ℝ, n = Matrix.of fun τ i =>
        Real.sqrt (Fintype.card d) * (Real.cos φ * Ξ τ i - Real.sin φ * Ξ' τ i) := ⟨_, rfl⟩
    have hN : pathMatrix Ξ Ξ' (Complex.exp (φ * Complex.I)) = n.map (fun x : ℝ => (x : ℂ)) := by
      rw [hn_def]
      exact pathMatrix_exp_mul_I_cbi Ξ Ξ' φ
    have hn : ∀ τ, n τ ⬝ᵥ n τ = (Fintype.card d : ℝ) := fun τ => by
      rw [hn_def]
      exact circle_dotProduct_self_cbi (Ξ τ) (Ξ' τ) (hΞ τ) (hΞ' τ) (hΞΞ' τ) φ
    have hNW : pathMatrix Ξ Ξ' (Complex.exp (φ * Complex.I)) * θ.toC.1 k
        = (n * θ.read k).map (fun x : ℝ => (x : ℂ)) := by
      rw [hN, map_mul_ofReal_cbi]
      rfl
    have h1 : (pathMatrix Ξ Ξ' (Complex.exp (φ * Complex.I)) * θ.toC.1 k).map σC
        = ((n * θ.read k).map σ).map (fun x : ℝ => (x : ℂ)) := by
      rw [hNW]
      ext τ j
      simp only [Matrix.map_apply, hσ]
    have h2 : (pathMatrix Ξ Ξ' (Complex.exp (φ * Complex.I)) * θ.toC.1 k).map (deriv σC)
        = ((n * θ.read k).map σ').map (fun x : ℝ => (x : ℂ)) := by
      rw [hNW]
      ext τ j
      simp only [Matrix.map_apply, deriv_ofReal_cbi hσd hσ hσC]
    have h3 : zdotC θ k Z η (pathMatrix Ξ Ξ' (Complex.exp (φ * Complex.I)))
        = (tangentRMS Z n * θ.read k + n * η.read k).map (fun x : ℝ => (x : ℂ)) := by
      rw [hN]
      exact zdotC_ofReal θ k Z η n
    rw [hG]
    dsimp only
    rw [h1, h2, h3, blockLHSC_ofReal hσ θ k hκ hhol η ((n * θ.read k).map σ)
      ((n * θ.read k).map σ') (tangentRMS Z n * θ.read k + n * η.read k)
      (hθ.block_ne_zero k n hn),
      (suffixFlatZero_castSucc_iff_mlp_sphere hσd hσa θ hθ k Z η).1 h16 n hn]
    ext τ j
    simp
  -- (c) identity theorem on the connected set `[1, ∞) ⊂ ℂ`, from the zeros `e^{i/(m+1)} → 1`
  have hS : IsPreconnected ((fun t : ℝ => (t : ℂ)) '' Set.Ici 1) :=
    isPreconnected_Ici.image _ Complex.continuous_ofReal.continuousOn
  have h1S : (1 : ℂ) ∈ (fun t : ℝ => (t : ℂ)) '' Set.Ici 1 :=
    ⟨1, Set.self_mem_Ici, Complex.ofReal_one⟩
  have hfreq : ∃ᶠ z in nhdsWithin (1 : ℂ) {1}ᶜ, G z = 0 :=
    tendsto_exp_mul_I_cbi.frequently (Filter.Frequently.of_forall fun m => hb _)
  have hzero := hGan.eqOn_zero_of_preconnected_of_frequently_eq_zero hS h1S hfreq
  intro t ht
  have e := hzero ⟨t, ht, rfl⟩
  rw [hG] at e
  exact e


end Skips
