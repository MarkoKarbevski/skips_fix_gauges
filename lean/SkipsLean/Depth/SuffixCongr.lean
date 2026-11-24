import SkipsLean.Depth.ComplexBlockIdentity

/-!
# The network after a hidden state depends only on the later blocks; `𝓛` at complex arguments

Paper (dimension paper): Appendix D.3, "The network after the block does not depend on the
weights of the block" (the derivative `𝐃_θ𝓑_{>k}(h) η` is the paper's `𝐃_θ𝓑_{>k}(h) η'`, with `η'`
the components of `η` at the blocks after `h_k` and at `D`), and Appendix D.6 (the case `ε = 0`),
"The identity on the path": "`𝓛` is holomorphic in `w̃`, affine in `w̃'` and polynomial in `n`",
together with "`𝓑_{>k}(λh) = 𝓑_{>k}(h)` for `λ > 0`" (Lemma D.14), which the proof of Lemma D.19
uses as "a derivative of order `i` of `𝓑` is homogeneous of degree `−i`".

Stated here, for networks with any stream matrices `S` and any blocks (first two statements), and
for MLP blocks with an activation extended by `σC : ℂ → ℂ` under pre-RMSNorm with `ε = 0` (the
others):

* `𝓑_{>j}` and its complex version do not change when the weights of the blocks before `h_j` and
  `E` change; so the derivative in the weights vanishes along a direction that is zero at the
  blocks after `h_j` and at `D`.
* `𝓛(w̃, w̃'; ż)` (`blockLHSC`) is holomorphic in `(w̃, w̃', ż)` where the rows of `w̃V` lie in a
  cone on which `𝓑_{>k+1}` is holomorphic.
* `𝓛(c w̃, w̃'; c ż) = 𝓛(w̃, w̃'; ż)` for `c > 0`, on such a cone `C_κ` with `κ ≤ 1`.

Numbering: block `ℓ : Fin L` lies after the hidden state `j : Fin (L + 1)` when `j ≤ ℓ.castSucc`.
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]

/-- **`𝓑_{>j}` depends only on the blocks after `h_j` and on `D`** (any blocks, any stream
matrices). -/
theorem suffix_congr (A : Arch T d L) (S : Fin L → Matrix d d ℝ) (θ θ' : Params A dIn dOut)
    (j : Fin (L + 1)) (h : Matrix T d ℝ)
    (hr : ∀ ℓ : Fin L, j ≤ ℓ.castSucc → θ'.read ℓ = θ.read ℓ)
    (hw : ∀ ℓ : Fin L, j ≤ ℓ.castSucc → θ'.write ℓ = θ.write ℓ) (hD : θ'.D = θ.D) :
    suffix A S θ' j h = suffix A S θ j h := by
  induction j using Fin.reverseInduction generalizing h with
  | last =>
    -- `𝓑_{>L}(h) = χ(h) D`, and the two `D` agree
    rw [suffix_last, suffix_last, hD]
  | cast ℓ ih =>
    -- block `ℓ` is after `h_ℓ`: its read and write agree; then the induction hypothesis
    rw [suffix_castSucc, suffix_castSucc, hr ℓ le_rfl, hw ℓ le_rfl]
    exact ih _ (fun ℓ' hℓ' => hr ℓ' ((Fin.castSucc_le_succ ℓ).trans hℓ'))
      (fun ℓ' hℓ' => hw ℓ' ((Fin.castSucc_le_succ ℓ).trans hℓ'))

/-- **The derivative of `𝓑_{>j}` in the weights vanishes along a direction that is zero at the
blocks after `h_j` and at `D`** (any blocks, any stream matrices; no differentiability is asked:
where `𝓑_{>j}` is not differentiable in the weights, Lean's derivative is `0`). -/
theorem fderiv_param_suffix_eq_zero (A : Arch T d L) (S : Fin L → Matrix d d ℝ)
    (θ η : Params A dIn dOut) (j : Fin (L + 1)) (h : Matrix T d ℝ)
    (hr : ∀ ℓ : Fin L, j ≤ ℓ.castSucc → η.read ℓ = 0)
    (hw : ∀ ℓ : Fin L, j ≤ ℓ.castSucc → η.write ℓ = 0) (hD : η.D = 0) :
    fderiv ℝ (fun θ' : Params A dIn dOut => suffix A S θ' j h) θ η = 0 := by
  by_cases hf : DifferentiableAt ℝ (fun θ' : Params A dIn dOut => suffix A S θ' j h) θ
  · -- the derivative along `η` is the derivative of `τ ↦ 𝓑_{>j}(h)` at `θ + τ η`, a constant
    have hγ : HasDerivAt (fun τ : ℝ => θ + τ • η) η 0 :=
      (((hasDerivAt_id' (0 : ℝ)).smul_const η).const_add θ).congr_deriv (one_smul ℝ η)
    have h1 := hf.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hγ (by rw [zero_smul, add_zero])
    have hc : (fun τ : ℝ => suffix A S (θ + τ • η) j h) = fun _ => suffix A S θ j h := by
      funext τ
      refine suffix_congr A S θ (θ + τ • η) j h (fun ℓ hℓ => ?_) (fun ℓ hℓ => ?_) ?_
      · rw [Params.add_read, Params.smul_read, hr ℓ hℓ, smul_zero, add_zero]
      · rw [Params.add_write, Params.smul_write, hw ℓ hℓ, smul_zero, add_zero]
      · rw [Params.add_D, Params.smul_D, hD, smul_zero, add_zero]
    have h2 : HasDerivAt (fun τ : ℝ => suffix A S (θ + τ • η) j h) 0 0 := by
      rw [hc]
      exact hasDerivAt_const _ _
    exact h1.unique h2
  · -- not differentiable: Lean's derivative is `0`
    rw [fderiv_zero_of_not_differentiableAt hf]
    rfl

variable {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)] {σ : ℝ → ℝ} {σC : ℂ → ℂ}

/-- **`𝓑_{>j}` at complex weights depends only on the blocks after `h_j` and on `D`.** -/
theorem suffixC_congr (σC : ℂ → ℂ) (ω ω' : CWeights d dOut hid) (j : Fin (L + 1))
    (h : Matrix T d ℂ)
    (hr : ∀ ℓ : Fin L, j ≤ ℓ.castSucc → ω'.1 ℓ = ω.1 ℓ)
    (hw : ∀ ℓ : Fin L, j ≤ ℓ.castSucc → ω'.2.1 ℓ = ω.2.1 ℓ) (hD : ω'.2.2 = ω.2.2) :
    suffixC σC ω' j h = suffixC σC ω j h := by
  induction j using Fin.reverseInduction generalizing h with
  | last =>
    -- `𝓑_{>L}(h) = N(h) D`, and the two `D` agree
    simp only [suffixC, Fin.reverseInduction_last]
    rw [hD]
  | cast ℓ ih =>
    -- block `ℓ` is after `h_ℓ`: its read and write agree; then the induction hypothesis
    simp only [suffixC, Fin.reverseInduction_castSucc]
    rw [hr ℓ le_rfl, hw ℓ le_rfl]
    exact ih _ (fun ℓ' hℓ' => hr ℓ' ((Fin.castSucc_le_succ ℓ).trans hℓ'))
      (fun ℓ' hℓ' => hw ℓ' ((Fin.castSucc_le_succ ℓ).trans hℓ'))

/-- **The complex derivative of `𝓑_{>j}` in the weights vanishes along a direction that is zero at
the blocks after `h_j` and at `D`.** -/
theorem fderiv_weights_suffixC_eq_zero (σC : ℂ → ℂ) (ω ζ : CWeights d dOut hid)
    (j : Fin (L + 1)) (h : Matrix T d ℂ)
    (hr : ∀ ℓ : Fin L, j ≤ ℓ.castSucc → ζ.1 ℓ = 0)
    (hw : ∀ ℓ : Fin L, j ≤ ℓ.castSucc → ζ.2.1 ℓ = 0) (hD : ζ.2.2 = 0) :
    fderiv ℂ (fun ω' : CWeights d dOut hid => suffixC σC ω' j h) ω ζ = 0 := by
  by_cases hf : DifferentiableAt ℂ (fun ω' : CWeights d dOut hid => suffixC σC ω' j h) ω
  · -- the derivative along `ζ` is the derivative of `τ ↦ 𝓑_{>j}(h)` at `ω + τ ζ`, a constant
    have hγ : HasDerivAt (fun τ : ℂ => ω + τ • ζ) ζ 0 :=
      (((hasDerivAt_id' (0 : ℂ)).smul_const ζ).const_add ω).congr_deriv (one_smul ℂ ζ)
    have h1 := hf.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℂ) hγ (by rw [zero_smul, add_zero])
    have hc : (fun τ : ℂ => suffixC σC (ω + τ • ζ) j h) = fun _ => suffixC σC ω j h := by
      funext τ
      refine suffixC_congr σC ω (ω + τ • ζ) j h (fun ℓ hℓ => ?_) (fun ℓ hℓ => ?_) ?_
      · show ω.1 ℓ + τ • ζ.1 ℓ = ω.1 ℓ
        rw [hr ℓ hℓ, smul_zero, add_zero]
      · show ω.2.1 ℓ + τ • ζ.2.1 ℓ = ω.2.1 ℓ
        rw [hw ℓ hℓ, smul_zero, add_zero]
      · show ω.2.2 + τ • ζ.2.2 = ω.2.2
        rw [hD, smul_zero, add_zero]
    have h2 : HasDerivAt (fun τ : ℂ => suffixC σC (ω + τ • ζ) j h) 0 0 := by
      rw [hc]
      exact hasDerivAt_const _ _
    exact h1.unique h2
  · -- not differentiable: Lean's derivative is `0`
    rw [fderiv_zero_of_not_differentiableAt hf]
    rfl

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (as `analyticAt_matrix_mul_cbi` of `Depth/ComplexBlockIdentity.lean`, where it is
private): the matrix product of two analytic matrix-valued maps is analytic. -/
private theorem analyticAt_matrix_mul_sc {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
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
/-- Helper (as `analyticAt_entry_cbi`): an entry of an analytic matrix-valued map is analytic. -/
private theorem analyticAt_entry_sc {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {m n : Type*} [Fintype m] [Fintype n] {F : E → Matrix m n ℂ} {x : E}
    (hF : AnalyticAt ℂ F x) (i : m) (j : n) : AnalyticAt ℂ (fun y => F y i j) x := by
  have he : AnalyticAt ℂ (fun M : Matrix m n ℂ => M i j) (F x) :=
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : n => ℂ) j).comp
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : m => n → ℂ) i)).analyticAt _
  exact AnalyticAt.comp (f := F) he hF

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (as `analyticAt_hadamard_cbi`): the entrywise product of two analytic matrix-valued
maps is analytic. -/
private theorem analyticAt_hadamard_sc {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {m n : Type*} [Fintype m] [Fintype n] {A B : E → Matrix m n ℂ} {x : E}
    (hA : AnalyticAt ℂ A x) (hB : AnalyticAt ℂ B x) :
    AnalyticAt ℂ (fun y => Matrix.of fun i j => A y i j * B y i j) x := by
  show AnalyticAt ℂ (fun y => fun i => fun j => A y i j * B y i j) x
  exact AnalyticAt.pi fun i => AnalyticAt.pi fun j =>
    (analyticAt_entry_sc hA i j).mul (analyticAt_entry_sc hB i j)

/-- Helper (as `fderiv_partial_add_cbi`): the two partial derivatives of a map of `(x, y)` that is
differentiable at `(x, y)` add up to its derivative. -/
private theorem fderiv_partial_add_sc {E₁ E₂ F : Type*} [NormedAddCommGroup E₁]
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

/-- **"`𝓛` is holomorphic in `w̃`, affine in `w̃'`"** (and in `ż`): if `𝓑_{>k+1}` is holomorphic on
the cone `C_κ` and the rows of `w̃₀V` lie in `C_κ`, then `(w̃, w̃', ż) ↦ 𝓛(w̃, w̃'; ż)` is
holomorphic at `(w̃₀, w̃'₀, ż₀)`. -/
theorem analyticAt_blockLHSC
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) (k : Fin L) {κ : ℝ}
    (hhol : HolomorphicOnCone σC θ k.succ κ)
    (η : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
    (w₀ w₀' zd₀ : Matrix T (hid k) ℂ) (hw₀ : ∀ t, (w₀ * θ.toC.2.1 k) t ∈ complexCone κ) :
    AnalyticAt ℂ
      (fun p : Matrix T (hid k) ℂ × Matrix T (hid k) ℂ × Matrix T (hid k) ℂ =>
        blockLHSC σC θ k η p.1 p.2.1 p.2.2) (w₀, w₀', zd₀) := by
  -- the point `w̃ V` and the direction `(w̃' ⊙ ż) V + w̃ η_V` are polynomials in `(w̃, w̃', ż)`
  have hfst : AnalyticAt ℂ
      (fun p : Matrix T (hid k) ℂ × Matrix T (hid k) ℂ × Matrix T (hid k) ℂ => p.1)
      (w₀, w₀', zd₀) := analyticAt_fst
  have hsnd1 : AnalyticAt ℂ
      (fun p : Matrix T (hid k) ℂ × Matrix T (hid k) ℂ × Matrix T (hid k) ℂ => p.2.1)
      (w₀, w₀', zd₀) :=
    AnalyticAt.comp (f := fun p : Matrix T (hid k) ℂ × Matrix T (hid k) ℂ × Matrix T (hid k) ℂ =>
      p.2) analyticAt_fst analyticAt_snd
  have hsnd2 : AnalyticAt ℂ
      (fun p : Matrix T (hid k) ℂ × Matrix T (hid k) ℂ × Matrix T (hid k) ℂ => p.2.2)
      (w₀, w₀', zd₀) :=
    AnalyticAt.comp (f := fun p : Matrix T (hid k) ℂ × Matrix T (hid k) ℂ × Matrix T (hid k) ℂ =>
      p.2) analyticAt_snd analyticAt_snd
  have hwV : AnalyticAt ℂ
      (fun p : Matrix T (hid k) ℂ × Matrix T (hid k) ℂ × Matrix T (hid k) ℂ => p.1 * θ.toC.2.1 k)
      (w₀, w₀', zd₀) := analyticAt_matrix_mul_sc hfst analyticAt_const
  have hdir : AnalyticAt ℂ
      (fun p : Matrix T (hid k) ℂ × Matrix T (hid k) ℂ × Matrix T (hid k) ℂ =>
        (Matrix.of fun t j => p.2.1 t j * p.2.2 t j) * θ.toC.2.1 k + p.1 * η.toC.2.1 k)
      (w₀, w₀', zd₀) :=
    (analyticAt_matrix_mul_sc (analyticAt_hadamard_sc hsnd1 hsnd2) analyticAt_const).add
      (analyticAt_matrix_mul_sc hfst analyticAt_const)
  -- `𝓑_{>k+1}` is holomorphic at `(θ, w̃₀ V)`, whose rows are in `C_κ`
  have hΦ0 : AnalyticAt ℂ (fun q : CWeights d dOut hid × Matrix T d ℂ => suffixC σC q.1 k.succ q.2)
      (θ.toC, w₀ * θ.toC.2.1 k) := hhol _ hw₀
  have hp : AnalyticAt ℂ
      (fun p : Matrix T (hid k) ℂ × Matrix T (hid k) ℂ × Matrix T (hid k) ℂ =>
        ((θ.toC, p.1 * θ.toC.2.1 k) : CWeights d dOut hid × Matrix T d ℂ)) (w₀, w₀', zd₀) :=
    analyticAt_const.prod hwV
  -- the right side `𝐃Φ(θ, w̃V)(η, (w̃' ⊙ ż) V + w̃ η_V)` is analytic at `(w̃₀, w̃₀', ż₀)`
  have hDp := hΦ0.fderiv.comp_of_eq hp rfl
  have hq : AnalyticAt ℂ
      (fun p : Matrix T (hid k) ℂ × Matrix T (hid k) ℂ × Matrix T (hid k) ℂ =>
        ((η.toC, (Matrix.of fun t j => p.2.1 t j * p.2.2 t j) * θ.toC.2.1 k
          + p.1 * η.toC.2.1 k) : CWeights d dOut hid × Matrix T d ℂ)) (w₀, w₀', zd₀) :=
    analyticAt_const.prod hdir
  have hR := ((ContinuousLinearMap.id ℂ _).analyticAt_bilinear _).comp₂ hDp hq
  -- near `(w̃₀, w̃₀', ż₀)`, `𝓑_{>k+1}` is holomorphic at `(θ, w̃V)`, and the two partial
  -- derivatives in `𝓛` add up to this derivative
  have hev := hp.continuousAt.eventually hΦ0.eventually_analyticAt
  refine hR.congr (hev.mono fun p hp' => ?_)
  exact (fderiv_partial_add_sc (Φ := fun ω h' => suffixC σC ω k.succ h') hp'.differentiableAt
    _ _).symm

/-- **`𝓛(c w̃, w̃'; c ż) = 𝓛(w̃, w̃'; ż)` for `c > 0`:** if `𝓑_{>k+1}` is holomorphic on the cone
`C_κ`, `0 < κ ≤ 1`, and the rows of `w̃V` lie in `C_κ`. (`𝐃𝓑(ch)(cv) = 𝐃𝓑(h)v` and
`𝐃_θ𝓑(ch) = 𝐃_θ𝓑(h)`, the derivatives of `𝓑(ch) = 𝓑(h)`.) -/
theorem blockLHSC_smul
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) (k : Fin L) {κ : ℝ}
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hhol : HolomorphicOnCone σC θ k.succ κ)
    (η : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
    (w w' zd : Matrix T (hid k) ℂ) (hw : ∀ t, (w * θ.toC.2.1 k) t ∈ complexCone κ) {c : ℝ}
    (hc : 0 < c) :
    blockLHSC σC θ k η ((c : ℂ) • w) w' ((c : ℂ) • zd) = blockLHSC σC θ k η w w' zd := by
  -- the point `h = w̃ V`, with rows in `C_κ`
  obtain ⟨h, hh⟩ : ∃ h : Matrix T d ℂ, h = w * θ.toC.2.1 k := ⟨_, rfl⟩
  have hcone : ∀ t, h t ∈ complexCone κ := by
    rw [hh]
    exact hw
  -- (1) `𝓑_{>k+1}(c h') = 𝓑_{>k+1}(h')` at every `ω`, for every `h'` with rows in `C_κ`
  have h1 : ∀ (ω : CWeights d dOut hid) (h' : Matrix T d ℂ), (∀ t, h' t ∈ complexCone κ) →
      suffixC σC ω k.succ ((c : ℂ) • h') = suffixC σC ω k.succ h' := by
    intro ω h' hh'
    have hpos : ∀ t, 0 < (h' t ⬝ᵥ h' t).re := fun t =>
      re_dotProduct_self_pos_of_mem_complexCone hκ.le hκ1 (hh' t)
    exact suffixC_smul_rows σC ω k.succ h' hpos (fun _ => c) (fun _ => hc)
  -- (2) so the maps `ω ↦ 𝓑_{>k+1}(c h)` and `ω ↦ 𝓑_{>k+1}(h)` are equal
  have h2 : (fun ω : CWeights d dOut hid => suffixC σC ω k.succ ((c : ℂ) • h))
      = fun ω => suffixC σC ω k.succ h := funext fun ω => h1 ω h hcone
  -- (3) `h' ↦ 𝓑(c h')` and `𝓑` agree near `h`, so `𝐃𝓑(c h)(c v) = 𝐃𝓑(h) v`
  have hBd : DifferentiableAt ℂ (fun h' : Matrix T d ℂ => suffixC σC θ.toC k.succ h')
      ((c : ℂ) • h) := by
    have ha := hhol ((c : ℂ) • h) fun t => smul_mem_complexCone (hcone t) c hc
    have hi : AnalyticAt ℂ (fun h' : Matrix T d ℂ => ((θ.toC, h') : CWeights d dOut hid × _))
        ((c : ℂ) • h) := analyticAt_const.prod analyticAt_id
    exact (ha.comp hi).differentiableAt
  have hnhds : ∀ᶠ h' in nhds h, ∀ t, h' t ∈ complexCone κ :=
    Filter.eventually_all.2 fun t =>
      (continuous_apply t).continuousAt.eventually_mem ((isOpen_complexCone κ).mem_nhds (hcone t))
  have hev : (fun h' : Matrix T d ℂ => suffixC σC θ.toC k.succ h')
      =ᶠ[nhds h] fun h' => suffixC σC θ.toC k.succ ((c : ℂ) • h') :=
    hnhds.mono fun h' hh' => (h1 θ.toC h' hh').symm
  let S : Matrix T d ℂ →L[ℂ] Matrix T d ℂ := (c : ℂ) • ContinuousLinearMap.id ℂ _
  have hS : HasFDerivAt (fun h' : Matrix T d ℂ => suffixC σC θ.toC k.succ ((c : ℂ) • h'))
      ((fderiv ℂ (fun h' : Matrix T d ℂ => suffixC σC θ.toC k.succ h') ((c : ℂ) • h)).comp S)
      h := by
    have hc := hBd.hasFDerivAt.comp h S.hasFDerivAt
    exact hc
  have h3 : ∀ v : Matrix T d ℂ,
      fderiv ℂ (fun h' : Matrix T d ℂ => suffixC σC θ.toC k.succ h') ((c : ℂ) • h) ((c : ℂ) • v)
        = fderiv ℂ (fun h' : Matrix T d ℂ => suffixC σC θ.toC k.succ h') h v := by
    intro v
    have h4 := (hS.congr_of_eventuallyEq hev).fderiv
    exact (DFunLike.congr_fun h4 v).symm
  -- the point `(c w̃) V = c h` and the direction `(w̃' ⊙ c ż) V + (c w̃) η_V = c v`
  have e1 : ((c : ℂ) • w) * θ.toC.2.1 k = (c : ℂ) • h := by
    rw [hh, Matrix.smul_mul]
  have e2 : (Matrix.of fun t j => w' t j * ((c : ℂ) • zd) t j) * θ.toC.2.1 k
        + ((c : ℂ) • w) * η.toC.2.1 k
      = (c : ℂ) • ((Matrix.of fun t j => w' t j * zd t j) * θ.toC.2.1 k + w * η.toC.2.1 k) := by
    have e3 : (Matrix.of fun t j => w' t j * ((c : ℂ) • zd) t j)
        = (c : ℂ) • Matrix.of fun t j => w' t j * zd t j := by
      ext t j
      simp only [Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
      ring
    rw [e3, Matrix.smul_mul, Matrix.smul_mul, smul_add]
  unfold blockLHSC
  rw [e1, e2, ← hh, h2, h3]

end Skips
