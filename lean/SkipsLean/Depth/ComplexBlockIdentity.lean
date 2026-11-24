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
  sorry

end Skips
