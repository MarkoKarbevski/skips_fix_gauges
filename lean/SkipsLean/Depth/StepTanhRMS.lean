import SkipsLean.Depth.SuffixRMS
import SkipsLean.Depth.StepTanh

/-!
# The step from `(D_{k+1})` to `(D_k)` for a `tanh` block under pre-RMSNorm with `ε > 0`

Paper (dimension paper): Appendix D.3, equations (14) and (20) to (23) with Lemma D.6 ("The
identity at every real row"), and Appendix D.4, Lemma D.7 ("The step for tanh on rays"), in the
case (+).

Under pre-RMSNorm a block reads `n = N_ε(h)`. For a matrix `Z`, equation (14) is
`𝐃N_ε(h)(h Z) = n Z - ⟨n Z, n⟩ n / d`, row by row, so in the identity for one block

  `ż(n) = (n Z - ⟨n Z, n⟩ n / d) W + n η_W`   (equation (20)).

The identity (16) before the block is `𝓛(σ(n W), σ'(n W); n) = 0` for the values `n` of `N_ε`, the
rows of the ball `‖n‖² < d` (equation (22)); its left side is real-analytic in `n`, so it holds at
every row `n` (Lemma D.6). On a ray `n = t ξ` this reads `t³ 𝒯_3 + t 𝒯_1 + 𝒯_0 = 0`, and `𝒯_3 = 0`
says that `Z` is antisymmetric.

Numbering and tokens are as in `Depth/StepTanh.lean`: the block is `k : Fin L`, the hidden state
before it `k.castSucc` and after it `k.succ`, and a hidden state has the rows `T`.
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise Topology

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]
variable {σ σ' : ℝ → ℝ} {ε : ℝ}

/-- The right side of equation (14), row by row: `n Z - ⟨n Z, n⟩ n / d`. -/
noncomputable def tangentRMS (Z : Matrix d d ℝ) (n : Matrix T d ℝ) : Matrix T d ℝ :=
  Matrix.of fun t => (n * Z) t - (((n * Z) t ⬝ᵥ n t) / (Fintype.card d : ℝ)) • n t

omit [Fintype T] [DecidableEq d] in
/-- Helper: a row of `rmsNorm ε h * Z` is `s⁻¹ • (h * Z) t`. -/
private theorem rmsNorm_mul_row (Z : Matrix d d ℝ) (h : Matrix T d ℝ) (t : T) :
    (rmsNorm ε h * Z) t
      = (Real.sqrt ((h t ⬝ᵥ h t) / (Fintype.card d : ℝ) + ε))⁻¹ • (h * Z) t := by
  rw [Matrix.mul_apply_eq_vecMul, Matrix.mul_apply_eq_vecMul]
  exact Matrix.smul_vecMul (R := ℝ) _ (h t) Z

omit [DecidableEq d] in
/-- **Equation (14):** for `ε > 0`, `𝐃N_ε(h)(h Z) = n Z - ⟨n Z, n⟩ n / d` at `n = N_ε(h)`. -/
theorem fderiv_rmsNorm_mul (hε : 0 < ε) (Z : Matrix d d ℝ) (h : Matrix T d ℝ) :
    fderiv ℝ (rmsNorm ε : Matrix T d ℝ → Matrix T d ℝ) h (h * Z)
      = tangentRMS Z (rmsNorm ε h) := by
  classical
  obtain ⟨v, hv⟩ : ∃ v, v = h * Z := ⟨_, rfl⟩
  rw [← hv]
  -- the derivative of `τ ↦ N_ε(h + τ v)` at `0` is `𝐃N_ε(h) v` ...
  have hl : HasDerivAt (fun τ : ℝ => h + τ • v) v 0 := by
    have h1 := ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add h
    rw [one_smul] at h1
    exact h1
  have hline : HasDerivAt (fun τ : ℝ => rmsNorm ε (h + τ • v))
      (fderiv ℝ (rmsNorm ε : Matrix T d ℝ → Matrix T d ℝ) h v) 0 := by
    have hc := (differentiable_rmsNorm (T := T) (d := d) hε h).hasFDerivAt.comp_hasDerivAt_of_eq
      (0 : ℝ) hl (by rw [zero_smul, add_zero])
    exact hc
  -- ... and, entry by entry, `n Z - ⟨n Z, n⟩ n / d`
  refine hline.unique (hasDerivAt_pi.2 fun t => hasDerivAt_pi.2 fun j => ?_)
  -- the radicand `q(τ) = ‖h_t + τ v_t‖² / d + ε` along the line
  have hx : ∀ i, HasDerivAt (fun τ : ℝ => h t i + τ * v t i) (v t i) 0 := fun i => by
    have h1 := ((hasDerivAt_id (0 : ℝ)).mul_const (v t i)).const_add (h t i)
    rw [one_mul] at h1
    exact h1
  have hq := ((HasDerivAt.fun_sum (u := Finset.univ) fun i _ => (hx i).mul (hx i)).div_const
    (Fintype.card d : ℝ)).add_const ε
  have hsum : (∑ i, (h t i + 0 * v t i) * (h t i + 0 * v t i)) = h t ⬝ᵥ h t := by
    simp only [zero_mul, add_zero, dotProduct]
  have hq0 : 0 < (∑ i, (h t i + 0 * v t i) * (h t i + 0 * v t i)) / (Fintype.card d : ℝ) + ε := by
    rw [hsum]
    have : 0 ≤ (h t ⬝ᵥ h t) / (Fintype.card d : ℝ) :=
      div_nonneg (Finset.sum_nonneg fun i _ => mul_self_nonneg _) (Nat.cast_nonneg _)
    linarith
  have hm := ((hq.sqrt hq0.ne').inv (Real.sqrt_pos.2 hq0).ne').mul (hx j)
  have hm' : HasDerivAt (fun τ : ℝ => (Real.sqrt ((∑ i, (h t i + τ * v t i) * (h t i + τ * v t i))
          / (Fintype.card d : ℝ) + ε))⁻¹ * (h t j + τ * v t j)) _ 0 := hm
  refine hm'.congr_deriv ?_
  -- the algebra of equation (14), with `s = √(‖h_t‖² / d + ε)`
  obtain ⟨s, hs⟩ : ∃ s, s = Real.sqrt ((h t ⬝ᵥ h t) / (Fintype.card d : ℝ) + ε) := ⟨_, rfl⟩
  have hs0 : 0 < s := by
    rw [hs]
    exact Real.sqrt_pos.2 (by rw [hsum] at hq0; exact hq0)
  have hrow : (rmsNorm ε h * Z) t = s⁻¹ • v t := by rw [hs, hv]; exact rmsNorm_mul_row Z h t
  have hnt : rmsNorm ε h t = s⁻¹ • h t := by rw [hs]; rfl
  have hsum' : ∑ i, (v t i * (h t i + 0 * v t i) + (h t i + 0 * v t i) * v t i)
      = 2 * (v t ⬝ᵥ h t) := by
    simp only [zero_mul, add_zero, dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp only [Pi.mul_apply, Pi.inv_apply]
  rw [hsum, hsum', ← hs, zero_mul, add_zero]
  show _ = (rmsNorm ε h * Z) t j - ((rmsNorm ε h * Z) t ⬝ᵥ rmsNorm ε h t) / (Fintype.card d : ℝ)
      * rmsNorm ε h t j
  rw [hrow, hnt, smul_dotProduct, dotProduct_smul, Pi.smul_apply, Pi.smul_apply, smul_eq_mul,
    smul_eq_mul, smul_eq_mul, smul_eq_mul]
  field_simp
  ring

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the line `τ ↦ a + τ b` has the velocity `b` (as in `Depth/StepTanh.lean`). -/
private theorem hasDerivAt_line' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (a b : E) :
    HasDerivAt (fun τ : ℝ => a + τ • b) b 0 := by
  have h := ((hasDerivAt_id (0 : ℝ)).smul_const b).const_add a
  rw [one_smul] at h
  exact h

omit [DecidableEq d] in
/-- Helper: equation (14) along the line `τ ↦ h + τ h Z`. -/
private theorem hasDerivAt_rmsNorm_line (hε : 0 < ε) (Z : Matrix d d ℝ) (h : Matrix T d ℝ) :
    HasDerivAt (fun τ : ℝ => rmsNorm ε (h + τ • (h * Z))) (tangentRMS Z (rmsNorm ε h)) 0 := by
  classical
  rw [← fderiv_rmsNorm_mul hε Z h]
  have hc := (differentiable_rmsNorm (T := T) (d := d) hε h).hasFDerivAt.comp_hasDerivAt_of_eq
    (0 : ℝ) (hasDerivAt_line' h (h * Z)) (by rw [zero_smul, add_zero])
  exact hc

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the product rule for matrix-valued functions of one real variable (as in
`Depth/StepTanh.lean`). -/
private theorem hasDerivAt_matMul' {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
    {A : ℝ → Matrix m n ℝ} {B : ℝ → Matrix n p ℝ} {A' : Matrix m n ℝ} {B' : Matrix n p ℝ}
    {τ : ℝ} (hA : HasDerivAt A A' τ) (hB : HasDerivAt B B' τ) :
    HasDerivAt (fun s => A s * B s) (A' * B τ + A τ * B') τ := by
  refine hasDerivAt_pi.2 fun t => hasDerivAt_pi.2 fun i => ?_
  have h := HasDerivAt.fun_sum (u := Finset.univ) fun j _ =>
    (hasDerivAt_pi.1 (hasDerivAt_pi.1 hA t) j).mul (hasDerivAt_pi.1 (hasDerivAt_pi.1 hB j) i)
  simp only [Matrix.mul_apply, Matrix.add_apply, ← Finset.sum_add_distrib]
  exact h

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the derivative of `s ↦ σ(P(s))`, entry by entry (as in `Depth/StepTanh.lean`). -/
private theorem hasDerivAt_map' {m n : Type*} [Fintype m] [Fintype n]
    (hσ : ∀ z, HasDerivAt σ (σ' z) z) {P : ℝ → Matrix m n ℝ} {P' : Matrix m n ℝ} {τ : ℝ}
    (hP : HasDerivAt P P' τ) :
    HasDerivAt (fun s => (P s).map σ) (Matrix.of fun t j => σ' (P τ t j) * P' t j) τ :=
  hasDerivAt_pi.2 fun t => hasDerivAt_pi.2 fun j =>
    (hσ (P τ t j)).comp τ (hasDerivAt_pi.1 (hasDerivAt_pi.1 hP t) j)

/-- Helper: for `Φ` differentiable at `(x, y)`, the derivatives of its two partial maps add up to
its derivative along `(a, b)` (as in `Depth/StepTanh.lean`). -/
private theorem fderiv_partial_add' {E₁ E₂ F : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
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

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the product of two differentiable matrix-valued maps is differentiable (as in
`Depth/Suffix.lean`). -/
private theorem differentiable_matMul'' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
    {f : E → Matrix m n ℝ} {g : E → Matrix n p ℝ}
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) :
    Differentiable ℝ (fun y => f y * g y) := by
  let B : Matrix m n ℝ →ₗ[ℝ] Matrix n p ℝ →ₗ[ℝ] Matrix m p ℝ :=
    LinearMap.mk₂ ℝ (fun a b => a * b) Matrix.add_mul (fun c a b => Matrix.smul_mul c a b)
      Matrix.mul_add (fun c a b => Matrix.mul_smul a c b)
  let B' : Matrix m n ℝ →L[ℝ] Matrix n p ℝ →L[ℝ] Matrix m p ℝ :=
    LinearMap.toContinuousLinearMap
      ((LinearMap.toContinuousLinearMap :
        (Matrix n p ℝ →ₗ[ℝ] Matrix m p ℝ) ≃ₗ[ℝ] (Matrix n p ℝ →L[ℝ] Matrix m p ℝ)).toLinearMap ∘ₗ B)
  have hB : (fun y => f y * g y) = fun y => B' (f y) (g y) := rfl
  rw [hB]
  exact (B'.differentiable.comp hf).clm_apply hg

/-- For a differentiable `χ` and differentiable blocks, `(θ, h) ↦ 𝓑_{>k}(h)` (with the weights
`θ`) is jointly differentiable. (The reverse induction of `differentiable_suffix_prod`, with `χ`
before every read and before the readout.) -/
theorem differentiable_suffix_prod_of_differentiable (A : Arch T d L)
    (hχ : Differentiable ℝ A.χ) (hf : ∀ ℓ, Differentiable ℝ (A.f ℓ)) (k : Fin (L + 1)) :
    Differentiable ℝ (fun p : Params A dIn dOut × Matrix T d ℝ => suffix A 0 p.1 k p.2) := by
  -- the weights are linear, hence differentiable, functions of the parameters
  have hD : Differentiable ℝ (fun θ' : Params A dIn dOut => θ'.D) :=
    (LinearMap.toContinuousLinearMap (Params.linD (A := A) (dIn := dIn) (dOut := dOut))).differentiable
  have hr : ∀ ℓ, Differentiable ℝ (fun θ' : Params A dIn dOut => θ'.read ℓ) := fun ℓ =>
    (LinearMap.toContinuousLinearMap
      (Params.linRead (A := A) (dIn := dIn) (dOut := dOut) ℓ)).differentiable
  have hw : ∀ ℓ, Differentiable ℝ (fun θ' : Params A dIn dOut => θ'.write ℓ) := fun ℓ =>
    (LinearMap.toContinuousLinearMap
      (Params.linWrite (A := A) (dIn := dIn) (dOut := dOut) ℓ)).differentiable
  induction k using Fin.reverseInduction with
  | last =>
    -- `(θ, h) ↦ χ(h) D`
    simp only [suffix_last]
    exact differentiable_matMul'' (hχ.comp differentiable_snd) (hD.comp differentiable_fst)
  | cast ℓ ih =>
    -- `(θ, h) ↦ 𝓑_{>ℓ}(f_ℓ(χ(h) W_read) W_write)`, with the weights `θ`
    simp only [suffix_castSucc, Pi.zero_apply, Matrix.mul_zero, zero_add]
    exact ih.comp (differentiable_fst.prodMk (differentiable_matMul''
      ((hf ℓ).comp (differentiable_matMul'' (hχ.comp differentiable_snd)
        ((hr ℓ).comp differentiable_fst)))
      ((hw ℓ).comp differentiable_fst)))

/-- **The identity for one block, case (+)** (equation (22), by the chain rule and (14)): for an
MLP block whose activation `σ` has the derivative `σ'`, the identity (16) for the hidden state
before block `k` holds for `Z` and `η` if and only if `𝓛(σ(n W), σ'(n W); n) = 0` at every value
`n = N_ε(h)`, with `ż(n) = (n Z - ⟨n Z, n⟩ n / d) W + n η_W`. -/
theorem suffixFlat_castSucc_iff_mlp_rmsNorm_values (hε : 0 < ε)
    (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut) (k : Fin L)
    (Z : Matrix d d ℝ) (η : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut) :
    SuffixFlat (Arch.mlp σ (rmsNorm ε) hid) θ k.castSucc Z η ↔
      ∀ h : Matrix T d ℝ,
        blockLHS θ k η ((rmsNorm ε h * θ.read k).map σ) ((rmsNorm ε h * θ.read k).map σ')
          (tangentRMS Z (rmsNorm ε h) * θ.read k + rmsNorm ε h * η.read k) = 0 := by
  -- `N_ε` and the blocks are differentiable, hence so are `(θ', h') ↦ 𝓑_{>k+1}(h')` and
  -- `𝓑_{>k}(h')`
  have hfd : ∀ ℓ, Differentiable ℝ ((Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid).f ℓ) :=
    differentiable_f_mlp fun z => (hσ z).differentiableAt
  have hχd : Differentiable ℝ (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid).χ :=
    differentiable_rmsNorm hε
  have hΦ := differentiable_suffix_prod_of_differentiable
    (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) (dIn := dIn) (dOut := dOut) hχd hfd k.succ
  have hΨ := differentiable_suffix_prod_of_differentiable
    (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) (dIn := dIn) (dOut := dOut) hχd hfd k.castSucc
  -- it suffices that the two left sides agree at every `h`
  suffices key : ∀ h : Matrix T d ℝ,
      fderiv ℝ (fun h' : Matrix T d ℝ => suffix (Arch.mlp σ (rmsNorm ε) hid) 0 θ k.castSucc h') h
          (h * Z)
        + fderiv ℝ (fun θ' : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut =>
            suffix (Arch.mlp σ (rmsNorm ε) hid) 0 θ' k.castSucc h) θ η
      = blockLHS θ k η ((rmsNorm ε h * θ.read k).map σ) ((rmsNorm ε h * θ.read k).map σ')
          (tangentRMS Z (rmsNorm ε h) * θ.read k + rmsNorm ε h * η.read k) by
    exact forall_congr' fun h => by rw [key h]
  intro h
  -- the block along the line `τ ↦ (θ + τ η, h + τ h Z)`, entrywise, with (14): equation (22)
  have hg := hasDerivAt_matMul' (hasDerivAt_map' hσ (hasDerivAt_matMul'
    (hasDerivAt_rmsNorm_line hε Z h) (hasDerivAt_line' (θ.read k) (η.read k))))
    (hasDerivAt_line' (θ.write k) (η.write k))
  simp only [zero_smul, add_zero] at hg
  -- the derivative of `τ ↦ 𝓑_{>k}(h + τ h Z)` (with the weights `θ + τ η`) at `0`, directly ...
  have e1 : HasDerivAt
      (fun τ : ℝ => suffix (Arch.mlp σ (rmsNorm ε) hid) 0 (θ + τ • η) k.castSucc (h + τ • (h * Z)))
      (fderiv ℝ (fun p : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut
          × Matrix T d ℝ => suffix (Arch.mlp σ (rmsNorm ε) hid) 0 p.1 k.castSucc p.2) (θ, h)
        (η, h * Z)) 0 := by
    have hc := (hΨ (θ, h)).hasFDerivAt.comp_hasDerivAt_of_eq 0
      ((hasDerivAt_line' θ η).prodMk (hasDerivAt_line' h (h * Z))) (by simp)
    exact hc
  -- ... and through the block: `𝓑_{>k}(h') = 𝓑_{>k+1}(σ(N_ε(h') W) V)`
  have e2 : HasDerivAt
      (fun τ : ℝ => suffix (Arch.mlp σ (rmsNorm ε) hid) 0 (θ + τ • η) k.castSucc (h + τ • (h * Z)))
      (fderiv ℝ (fun p : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut
          × Matrix T d ℝ => suffix (Arch.mlp σ (rmsNorm ε) hid) 0 p.1 k.succ p.2)
        (θ, (rmsNorm ε h * θ.read k).map σ * θ.write k)
        (η, (Matrix.of fun t j => σ' ((rmsNorm ε h * θ.read k) t j)
            * (tangentRMS Z (rmsNorm ε h) * θ.read k + rmsNorm ε h * η.read k) t j) * θ.write k
          + (rmsNorm ε h * θ.read k).map σ * η.write k)) 0 := by
    have hc := (hΦ (θ, (rmsNorm ε h * θ.read k).map σ * θ.write k)).hasFDerivAt.comp_hasDerivAt_of_eq
      0 ((hasDerivAt_line' θ η).prodMk hg) (by simp)
    have hfun : (fun τ : ℝ =>
        suffix (Arch.mlp σ (rmsNorm ε) hid) 0 (θ + τ • η) k.castSucc (h + τ • (h * Z)))
        = (fun p : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut × Matrix T d ℝ =>
            suffix (Arch.mlp σ (rmsNorm ε) hid) 0 p.1 k.succ p.2) ∘ fun τ : ℝ =>
          (θ + τ • η, (rmsNorm ε (h + τ • (h * Z)) * (θ.read k + τ • η.read k)).map σ
            * (θ.write k + τ • η.write k)) := by
      funext τ
      simp only [Function.comp_apply, suffix_castSucc, Pi.zero_apply, Matrix.mul_zero, zero_add]
      rfl
    rw [hfun]
    exact hc
  -- both sides are derivatives of the joint maps `(θ', h') ↦ 𝓑(h')` along `(η, ·)`
  unfold blockLHS
  calc _ = _ := fderiv_partial_add'
        (Φ := fun θ' h' => suffix (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) 0 θ' k.castSucc h')
        (hΨ (θ, h)) η (h * Z)
    _ = _ := e1.unique e2
    _ = _ := (fderiv_partial_add'
        (Φ := fun θ' h' => suffix (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) 0 θ' k.succ h')
        (hΦ _) η _).symm


omit [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: `y ↦ y M`, as a continuous linear map (as in `Depth/StepTanh.lean`). -/
private noncomputable def mulRightCLM' {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
    (M : Matrix n p ℝ) : Matrix m n ℝ →L[ℝ] Matrix m p ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun y => y * M
      map_add' := fun a b => Matrix.add_mul a b M
      map_smul' := fun c a => Matrix.smul_mul c a M }

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the product of two analytic matrix-valued maps is analytic (as in
`Depth/StepTanh.lean`). -/
private theorem analyticOnNhd_matMul' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
    {f : E → Matrix m n ℝ} {g : E → Matrix n p ℝ} {s : Set E}
    (hf : AnalyticOnNhd ℝ f s) (hg : AnalyticOnNhd ℝ g s) :
    AnalyticOnNhd ℝ (fun y => f y * g y) s := by
  let B : Matrix m n ℝ →ₗ[ℝ] Matrix n p ℝ →ₗ[ℝ] Matrix m p ℝ :=
    LinearMap.mk₂ ℝ (fun a b => a * b) Matrix.add_mul (fun c a b => Matrix.smul_mul c a b)
      Matrix.mul_add (fun c a b => Matrix.mul_smul a c b)
  let B' : Matrix m n ℝ →L[ℝ] Matrix n p ℝ →L[ℝ] Matrix m p ℝ :=
    LinearMap.toContinuousLinearMap
      ((LinearMap.toContinuousLinearMap :
        (Matrix n p ℝ →ₗ[ℝ] Matrix m p ℝ) ≃ₗ[ℝ] (Matrix n p ℝ →L[ℝ] Matrix m p ℝ)).toLinearMap ∘ₗ B)
  have hB : (fun y => f y * g y) = fun y => B' (f y) (g y) := rfl
  rw [hB]
  exact fun y hy => (B'.analyticAt_bilinear (f y, g y)).comp₂ (hf y hy) (hg y hy)

/-- Helper: an analytic family of continuous linear maps, applied to an analytic family of vectors,
is analytic (as in `Depth/StepTanh.lean`). -/
private theorem analyticOnNhd_clm_apply' {X E F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {J : X → E →L[ℝ] F} {v : X → E} {s : Set X} (hJ : AnalyticOnNhd ℝ J s)
    (hv : AnalyticOnNhd ℝ v s) : AnalyticOnNhd ℝ (fun x => J x (v x)) s :=
  fun x hx => ((ContinuousLinearMap.id ℝ (E →L[ℝ] F)).analyticAt_bilinear (J x, v x)).comp₂
    (hJ x hx) (hv x hx)

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: `M ↦ σ(M)`, entry by entry, is analytic if `σ` is (as `analyticOnNhd_f_mlp`). -/
private theorem analyticOnNhd_map' {m n : Type*} [Fintype m] [Fintype n]
    (hσ : AnalyticOnNhd ℝ σ Set.univ) :
    AnalyticOnNhd ℝ (fun M : Matrix m n ℝ => M.map σ) Set.univ := by
  show AnalyticOnNhd ℝ (fun M : Matrix m n ℝ => fun t => fun i => σ (M t i)) Set.univ
  exact AnalyticOnNhd.pi fun t => AnalyticOnNhd.pi fun i =>
    hσ.comp (analyticOnNhd_matrix_entry t i) (Set.mapsTo_univ _ _)

omit [DecidableEq d] in
/-- Helper: `n ↦ n Z - ⟨n Z, n⟩ n / d` (equation (14)) is a polynomial in the entries of `n`, hence
analytic. -/
private theorem analyticOnNhd_tangentRMS (Z : Matrix d d ℝ) :
    AnalyticOnNhd ℝ (tangentRMS (T := T) Z) Set.univ := by
  have hZ : ∀ t i, AnalyticOnNhd ℝ (fun n : Matrix T d ℝ => (n * Z) t i) Set.univ := fun t i =>
    (analyticOnNhd_matrix_entry t i).comp ((mulRightCLM' (m := T) Z).analyticOnNhd Set.univ)
      (Set.mapsTo_univ _ _)
  show AnalyticOnNhd ℝ (fun n : Matrix T d ℝ => fun t i =>
    (n * Z) t i - ((n * Z) t ⬝ᵥ n t / (Fintype.card d : ℝ)) * n t i) Set.univ
  refine AnalyticOnNhd.pi fun t => AnalyticOnNhd.pi fun i =>
    (hZ t i).sub (AnalyticOnNhd.mul ?_ (analyticOnNhd_matrix_entry t i))
  show AnalyticOnNhd ℝ
    (fun n : Matrix T d ℝ => (∑ l, (n * Z) t l * n t l) / (Fintype.card d : ℝ)) Set.univ
  exact (Finset.analyticOnNhd_fun_sum _ fun l _ =>
    (hZ t l).mul (analyticOnNhd_matrix_entry t l)).div_const

omit [Fintype T] [DecidableEq d] in
/-- Helper: the values of `N_ε` (`ε > 0`) include every `n` whose rows have `‖n_t‖² / d < 1`: the
paper's inverse `h_t = √ε (1 - ‖n_t‖² / d)^{-1/2} n_t`. -/
private theorem exists_rmsNorm_eq (hε : 0 < ε) (n : Matrix T d ℝ)
    (hn : ∀ t, n t ⬝ᵥ n t / (Fintype.card d : ℝ) < 1) : ∃ h, rmsNorm ε h = n := by
  refine ⟨Matrix.of fun t =>
    (Real.sqrt ε / Real.sqrt (1 - n t ⬝ᵥ n t / (Fintype.card d : ℝ))) • n t, ?_⟩
  ext t j
  -- with `a = ‖n_t‖² / d < 1` and `c = √ε / √(1 - a)`: `‖c n_t‖² / d + ε = c²`
  obtain ⟨a, ha⟩ : ∃ a, a = n t ⬝ᵥ n t / (Fintype.card d : ℝ) := ⟨_, rfl⟩
  have h1a : 0 < 1 - a := by have := hn t; rw [← ha] at this; linarith
  obtain ⟨c, hc⟩ : ∃ c, c = Real.sqrt ε / Real.sqrt (1 - a) := ⟨_, rfl⟩
  have hc0 : 0 < c := by rw [hc]; exact div_pos (Real.sqrt_pos.2 hε) (Real.sqrt_pos.2 h1a)
  have hc2 : c ^ 2 = ε / (1 - a) := by
    rw [hc, div_pow, Real.sq_sqrt hε.le, Real.sq_sqrt h1a.le]
  have hε' : ε = c ^ 2 * (1 - a) := by rw [hc2]; field_simp
  have hrad : (c • n t) ⬝ᵥ (c • n t) / (Fintype.card d : ℝ) + ε = c ^ 2 := by
    rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    have : c * (c * (n t ⬝ᵥ n t)) / (Fintype.card d : ℝ) = c ^ 2 * a := by rw [ha]; ring
    rw [this, hε']
    ring
  -- so `N_ε(c n_t) = c⁻¹ c n_t = n_t`
  show rmsRow ε ((Real.sqrt ε / Real.sqrt (1 - n t ⬝ᵥ n t / (Fintype.card d : ℝ))) • n t) j
    = n t j
  rw [← ha, ← hc]
  unfold rmsRow
  rw [hrad, Real.sqrt_sq hc0.le, smul_smul, inv_mul_cancel₀ hc0.ne', one_smul]

/-- **Lemma D.6 (the identity at every real row), case (+):** for a real-analytic activation, the
identity (16) before block `k` holds if and only if `𝓛(σ(n W), σ'(n W); n) = 0` for every
`n` (equation (23)): the left side is real-analytic in `n`, and the values of `N_ε` form an open
set. -/
theorem suffixFlat_castSucc_iff_mlp_rmsNorm (hε : 0 < ε) (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut) (k : Fin L)
    (Z : Matrix d d ℝ) (η : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut) :
    SuffixFlat (Arch.mlp σ (rmsNorm ε) hid) θ k.castSucc Z η ↔
      ∀ n : Matrix T d ℝ,
        blockLHS θ k η ((n * θ.read k).map σ) ((n * θ.read k).map σ')
          (tangentRMS Z n * θ.read k + n * η.read k) = 0 := by
  rw [suffixFlat_castSucc_iff_mlp_rmsNorm_values hε hσ θ k Z η]
  refine ⟨fun hval => ?_, fun hG h => hG (rmsNorm ε h)⟩
  -- the left side `G(n)` of (23), as a function of the row `n`
  let G : Matrix T d ℝ → Matrix T dOut ℝ := fun n =>
    blockLHS θ k η ((n * θ.read k).map σ) ((n * θ.read k).map σ')
      (tangentRMS Z n * θ.read k + n * η.read k)
  -- `σ' = deriv σ` is analytic, `N_ε` and the blocks are analytic, hence so is
  -- `(θ', h') ↦ 𝓑_{>k+1}(h')`
  have hσ'a : AnalyticOnNhd ℝ σ' Set.univ := by
    rw [show σ' = deriv σ from funext fun z => (hσ z).deriv.symm]
    exact hσa.deriv
  have hf : ∀ ℓ, AnalyticOnNhd ℝ ((Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid).f ℓ) Set.univ :=
    fun ℓ => analyticOnNhd_f_mlp hσa ℓ
  have hΦ := analyticOnNhd_suffix_prod_of_analytic (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid)
    (dIn := dIn) (dOut := dOut) (analyticOnNhd_rmsNorm hε) hf k.succ
  -- the outputs `σ(n W)` of the hidden units, and the direction `(σ'(n W) ⊙ ż(n)) V + σ(n W) η_V`
  have hnW := (mulRightCLM' (m := T) (θ.read k)).analyticOnNhd Set.univ
  have hw : AnalyticOnNhd ℝ (fun n : Matrix T d ℝ => (n * θ.read k).map σ) Set.univ :=
    (analyticOnNhd_map' hσa).comp hnW (Set.mapsTo_univ _ _)
  have hzdot : AnalyticOnNhd ℝ
      (fun n : Matrix T d ℝ => tangentRMS Z n * θ.read k + n * η.read k) Set.univ :=
    (analyticOnNhd_matMul' (analyticOnNhd_tangentRMS Z) analyticOnNhd_const).add
      ((mulRightCLM' (m := T) (η.read k)).analyticOnNhd Set.univ)
  have hdir : AnalyticOnNhd ℝ (fun n : Matrix T d ℝ =>
      (Matrix.of fun t j => ((n * θ.read k).map σ') t j
          * (tangentRMS Z n * θ.read k + n * η.read k) t j) * θ.write k
        + (n * θ.read k).map σ * η.write k) Set.univ := by
    refine (analyticOnNhd_matMul' ?_ analyticOnNhd_const).add
      (analyticOnNhd_matMul' hw analyticOnNhd_const)
    show AnalyticOnNhd ℝ (fun n : Matrix T d ℝ => fun t j => ((n * θ.read k).map σ') t j
      * (tangentRMS Z n * θ.read k + n * η.read k) t j) Set.univ
    exact AnalyticOnNhd.pi fun t => AnalyticOnNhd.pi fun j =>
      ((analyticOnNhd_matrix_entry t j).comp ((analyticOnNhd_map' hσ'a).comp hnW
        (Set.mapsTo_univ _ _)) (Set.mapsTo_univ _ _)).mul
      ((analyticOnNhd_matrix_entry t j).comp hzdot (Set.mapsTo_univ _ _))
  -- `G(n)` is the derivative of `(θ', h') ↦ 𝓑_{>k+1}(h')` at `(θ, σ(n W) V)` along `(η, ·)`
  have hGeq : G = fun n => fderiv ℝ
      (fun p : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut × Matrix T d ℝ =>
        suffix (Arch.mlp σ (rmsNorm ε) hid) 0 p.1 k.succ p.2)
      (θ, (n * θ.read k).map σ * θ.write k)
      (η, (Matrix.of fun t j => ((n * θ.read k).map σ') t j
          * (tangentRMS Z n * θ.read k + n * η.read k) t j) * θ.write k
        + (n * θ.read k).map σ * η.write k) := by
    funext n
    exact fderiv_partial_add'
      (Φ := fun θ' h' => suffix (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) 0 θ' k.succ h')
      (hΦ _ (Set.mem_univ _)).differentiableAt η _
  -- so `G` is analytic on the whole space
  have hG : AnalyticOnNhd ℝ G Set.univ := by
    rw [hGeq]
    exact analyticOnNhd_clm_apply' (hΦ.fderiv.comp (analyticOnNhd_const.prod
        (analyticOnNhd_matMul' hw analyticOnNhd_const)) (Set.mapsTo_univ _ _))
      (analyticOnNhd_const.prod hdir)
  -- `G` vanishes on the open set of the `n` with `‖n_t‖² / d < 1`, values of `N_ε`, around `0`
  have hUo : IsOpen {n : Matrix T d ℝ | ∀ t, n t ⬝ᵥ n t / (Fintype.card d : ℝ) < 1} := by
    rw [Set.ofPred_forall]
    refine isOpen_iInter_of_finite fun t => isOpen_lt ?_ continuous_const
    show Continuous fun n : Matrix T d ℝ => (∑ i, n t i * n t i) / (Fintype.card d : ℝ)
    fun_prop
  have h0 : (0 : Matrix T d ℝ) ∈ {n : Matrix T d ℝ | ∀ t, n t ⬝ᵥ n t / (Fintype.card d : ℝ) < 1} :=
    fun t => by
      rw [show (0 : Matrix T d ℝ) t = 0 from rfl, zero_dotProduct, zero_div]
      exact zero_lt_one
  have hzero : G =ᶠ[𝓝 0] 0 := Filter.eventually_of_mem (hUo.mem_nhds h0) fun n hn => by
    obtain ⟨h, rfl⟩ := exists_rmsNorm_eq hε n hn
    exact hval h
  -- the identity principle on the (connected) whole space
  intro n
  exact hG.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (Set.mem_univ 0)
    hzero (Set.mem_univ n)

variable (θ : Params (Arch.mlp (T := T) (d := d) Real.tanh (rmsNorm ε) hid) dIn dOut)

/-- **The fact in the proof of Lemma D.7, case (+).** Let `θ` be regular and let no row of the
write `V` of block `k` vanish (T1). If `𝐃𝓑(w̃ V) (((1 - w̃²) ⊙ b) V) = 0` for all `w̃`, then
`b = 0`. -/
theorem eq_zero_of_fderiv_suffix_one_sub_sq_rmsNorm (hε : 0 < ε)
    (hθ : Regular (Arch.mlp Real.tanh (rmsNorm ε) hid) θ) (k : Fin L)
    (hT1 : ∀ i : hid k, θ.write k i ≠ 0) (b : Matrix T (hid k) ℝ)
    (h : ∀ w : Matrix T (hid k) ℝ,
      fderiv ℝ
        (fun h' : Matrix T d ℝ => suffix (Arch.mlp Real.tanh (rmsNorm ε) hid) 0 θ k.succ h')
        (w * θ.write k) ((Matrix.of fun t j => (1 - w t j ^ 2) * b t j) * θ.write k) = 0) :
    b = 0 := by
  classical
  -- Lemma D.2, case (+), after the block: `𝐃𝓑` is injective on an open dense set `U`
  obtain ⟨U, -, hUd, hU⟩ := exists_open_dense_injective_fderiv_suffix_rmsNorm
    (Arch.mlp Real.tanh (rmsNorm ε) hid) θ hε rfl
    (fun ℓ => analyticOnNhd_f_mlp analyticOnNhd_tanh ℓ) hθ k.succ
  -- `V` has rank `d`, so `V⁺ V = 1` for some `V⁺`, and `w ↦ w V` is onto, hence open
  obtain ⟨Vp, hVp⟩ : ∃ Vp : Matrix d (hid k) ℝ, Vp * θ.write k = 1 :=
    Matrix.vecMul_surjective_iff_exists_left_inverse.1
      (Matrix.vecMul_surjective_iff_rank_eq_card.2 (hθ.rank_write k))
  have hopen : IsOpenMap (mulRightCLM' (m := T) (θ.write k)) :=
    (mulRightCLM' (m := T) (θ.write k)).isOpenMap fun y =>
      ⟨y * Vp, by show y * Vp * θ.write k = y; rw [Matrix.mul_assoc, hVp, Matrix.mul_one]⟩
  -- so the `w` with `w V ∈ U` are dense, and there `((1 - w²) ⊙ b) V = 0`
  have hdense : Dense {w : Matrix T (hid k) ℝ | w * θ.write k ∈ U} := hUd.preimage hopen
  let F : Matrix T (hid k) ℝ → Matrix T d ℝ :=
    fun w => (Matrix.of fun t j => (1 - w t j ^ 2) * b t j) * θ.write k
  have hF : ∀ w ∈ {w : Matrix T (hid k) ℝ | w * θ.write k ∈ U}, F w = 0 :=
    fun w hw => hU _ hw (by rw [h w, map_zero])
  -- `F` is continuous (a polynomial in `w`), so it vanishes everywhere
  have hFc : Continuous F := by fun_prop
  have hF0 : F = fun _ => 0 := Continuous.ext_on hdense hFc continuous_const hF
  -- at `w = 0` and at `w = single t j 1`, row `t` of the difference is `b_{t j} a_j`
  ext t j
  obtain ⟨i, hi⟩ : ∃ i, θ.write k j i ≠ 0 := by
    by_contra hne
    push Not at hne
    exact hT1 j (funext hne)
  have e0 := congrFun (congrFun (congrFun hF0 0) t) i
  have e1 := congrFun (congrFun (congrFun hF0 (Matrix.single t j (1 : ℝ))) t) i
  simp only [F, Matrix.mul_apply, Matrix.of_apply, Matrix.zero_apply] at e0 e1
  have hdiff : ∑ j', (1 - (0 : ℝ) ^ 2) * b t j' * θ.write k j' i
      - ∑ j', (1 - Matrix.single t j (1 : ℝ) t j' ^ 2) * b t j' * θ.write k j' i
      = b t j * θ.write k j i := by
    rw [← Finset.sum_sub_distrib, Finset.sum_eq_single j]
    · rw [Matrix.single_apply_same]
      ring
    · intro j' _ hj'
      rw [Matrix.single_apply_of_ne _ _ _ _ _ (fun h => hj' h.2.symm)]
      ring
    · intro hj; exact absurd (Finset.mem_univ j) hj
  rw [e0, e1, sub_zero] at hdiff
  exact (mul_eq_zero.1 hdiff.symm).resolve_right hi

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the set where a nonzero additive and homogeneous function `f` does not vanish is dense
(as in `Depth/StepTanh.lean`, on any normed space). -/
private theorem dense_setOf_ne_zero_of_linear' {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : E → ℝ) (hadd : ∀ x y, f (x + y) = f x + f y)
    (hsmul : ∀ (c : ℝ) x, f (c • x) = c * f x) {x₀ : E} (hx₀ : f x₀ ≠ 0) :
    Dense {x | f x ≠ 0} := by
  intro x
  by_cases hx : f x ≠ 0
  · exact subset_closure hx
  rw [not_not] at hx
  -- from a zero `x` of `f`, the points `x + s x₀` with `s ≠ 0` tend to `x`
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

/-- Helper: a matrix `Z` with `⟨ξ Z, ξ⟩ = 0` for every row `ξ` is antisymmetric (polarization:
`⟨(e_j + e_i) Z, e_j + e_i⟩ = Z_{jj} + Z_{ji} + Z_{ij} + Z_{ii}`). -/
private theorem mem_antisymmetric_of_vecMul_dotProduct_self {Z : Matrix d d ℝ}
    (hq : ∀ ξ : d → ℝ, (ξ ᵥ* Z) ⬝ᵥ ξ = 0) : Z ∈ antisymmetric d := by
  have hd : ∀ i, Z i i = 0 := fun i => by
    simpa only [single_one_vecMul, dotProduct_single, Matrix.row_apply, mul_one] using
      hq (Pi.single i 1)
  show Zᵀ = -Z
  ext i j
  have e := hq (Pi.single j 1 + Pi.single i 1)
  simp only [add_vecMul, dotProduct_add, single_one_vecMul, dotProduct_single, mul_one,
    Pi.add_apply, Matrix.row_apply, hd, zero_add, add_zero] at e
  rw [Matrix.transpose_apply, Matrix.neg_apply]
  linarith

/-- **Lemma D.7 (the step for `tanh` on rays), case (+).** Let `ε > 0`, let `θ` be regular, and let
block `k` satisfy (T1), no row of its write vanishes, and (T2), the columns of its read are linearly
independent over `ℚ`. Then `(D_{k+1})` implies `(D_k)`. -/
theorem claimRMS_castSucc_tanh [Nonempty T] (hε : 0 < ε)
    (hθ : Regular (Arch.mlp Real.tanh (rmsNorm ε) hid) θ) (k : Fin L)
    (hT1 : ∀ i : hid k, θ.write k i ≠ 0)
    (hT2 : LinearIndependent ℚ (fun j : hid k => fun i : d => θ.read k i j))
    (hk : ClaimRMS (Arch.mlp Real.tanh (rmsNorm ε) hid) θ k.succ) :
    ClaimRMS (Arch.mlp Real.tanh (rmsNorm ε) hid) θ k.castSucc := by
  classical
  intro Z η hZη
  have hf : ∀ ℓ, AnalyticOnNhd ℝ ((Arch.mlp (T := T) (d := d) Real.tanh (rmsNorm ε) hid).f ℓ)
      Set.univ := fun ℓ => analyticOnNhd_f_mlp analyticOnNhd_tanh ℓ
  -- Lemma D.6 with `σ = tanh`: the identity (23) at every row `n`
  have h23 :=
    (suffixFlat_castSucc_iff_mlp_rmsNorm hε hasDerivAt_tanh analyticOnNhd_tanh θ k Z η).1 hZη
  obtain ⟨C, hC⟩ : ∃ C : Matrix d (hid k) ℝ, C = Z * θ.read k + η.read k := ⟨_, rfl⟩
  -- the part of degree `3` of `ż` on a ray: `B Ξ = (⟨Ξ Z, Ξ⟩ / d) ⊙ Ξ W`, row by row
  let B : Matrix T d ℝ → Matrix T (hid k) ℝ := fun Ξ => Matrix.of fun τ j =>
    ((Ξ * Z) τ ⬝ᵥ Ξ τ / (Fintype.card d : ℝ)) * (Ξ * θ.read k) τ j
  -- equation (20) on the ray `n = t Ξ`: `ż(t Ξ) = t Ξ C - t³ B Ξ`
  have hzdot : ∀ (Ξ : Matrix T d ℝ) (t : ℝ),
      tangentRMS Z (t • Ξ) * θ.read k + (t • Ξ) * η.read k = t • (Ξ * C) - t ^ 3 • B Ξ := by
    intro Ξ t
    have hrow : ∀ (c : ℝ) (M : Matrix T d ℝ) (τ : T), (c • M) τ = c • M τ := fun _ _ _ => rfl
    have hT : tangentRMS Z (t • Ξ) = t • (Ξ * Z) - t ^ 3 • Matrix.of fun τ =>
        ((Ξ * Z) τ ⬝ᵥ Ξ τ / (Fintype.card d : ℝ)) • Ξ τ := by
      ext τ i
      simp only [tangentRMS, Matrix.smul_mul, hrow, smul_dotProduct, dotProduct_smul,
        Matrix.of_apply, Matrix.sub_apply, Matrix.smul_apply, Pi.sub_apply, Pi.smul_apply,
        smul_eq_mul]
      ring
    have hPW : (Matrix.of fun τ => ((Ξ * Z) τ ⬝ᵥ Ξ τ / (Fintype.card d : ℝ)) • Ξ τ) * θ.read k
        = B Ξ := by
      ext τ j
      simp only [B, Matrix.mul_apply, Matrix.of_apply, Pi.smul_apply, smul_eq_mul,
        Finset.mul_sum, mul_assoc]
    rw [hT, Matrix.sub_mul, Matrix.smul_mul, Matrix.smul_mul, hPW, Matrix.smul_mul, hC,
      Matrix.mul_add, Matrix.mul_assoc, smul_add]
    abel
  -- the maps `𝒯_3 Ξ`, `𝒯_1 Ξ` and `𝒯_0` of the outputs `w` of the hidden units
  let T3 : Matrix T d ℝ → Matrix T (hid k) ℝ → Matrix T dOut ℝ := fun Ξ w =>
    -fderiv ℝ (fun h' : Matrix T d ℝ => suffix (Arch.mlp Real.tanh (rmsNorm ε) hid) 0 θ k.succ h')
      (w * θ.write k) ((Matrix.of fun t j => (1 - w t j ^ 2) * B Ξ t j) * θ.write k)
  let T1 : Matrix T d ℝ → Matrix T (hid k) ℝ → Matrix T dOut ℝ := fun Ξ w =>
    fderiv ℝ (fun h' : Matrix T d ℝ => suffix (Arch.mlp Real.tanh (rmsNorm ε) hid) 0 θ k.succ h')
      (w * θ.write k) ((Matrix.of fun t j => (1 - w t j ^ 2) * (Ξ * C) t j) * θ.write k)
  let T0 : Matrix T (hid k) ℝ → Matrix T dOut ℝ := fun w =>
    fderiv ℝ (fun h' : Matrix T d ℝ => suffix (Arch.mlp Real.tanh (rmsNorm ε) hid) 0 θ k.succ h')
        (w * θ.write k) (w * η.write k)
      + fderiv ℝ (fun θ' : Params (Arch.mlp (T := T) (d := d) Real.tanh (rmsNorm ε) hid) dIn dOut =>
          suffix (Arch.mlp Real.tanh (rmsNorm ε) hid) 0 θ' k.succ (w * θ.write k)) θ η
  -- all are analytic: `𝓑` and `(θ', h') ↦ 𝓑(h')` are, hence so are their derivatives
  have hB := analyticOnNhd_suffix_of_analytic
    (Arch.mlp (T := T) (d := d) Real.tanh (rmsNorm ε) hid) θ (analyticOnNhd_rmsNorm hε) hf k.succ
  have hΦ := analyticOnNhd_suffix_prod_of_analytic
    (Arch.mlp (T := T) (d := d) Real.tanh (rmsNorm ε) hid) (dIn := dIn) (dOut := dOut)
    (analyticOnNhd_rmsNorm hε) hf k.succ
  have hJ := hB.fderiv.comp ((mulRightCLM' (m := T) (θ.write k)).analyticOnNhd Set.univ)
    (Set.mapsTo_univ _ _)
  have hdirAn : ∀ b : Matrix T (hid k) ℝ, AnalyticOnNhd ℝ (fun w : Matrix T (hid k) ℝ =>
      (Matrix.of fun t j => (1 - w t j ^ 2) * b t j) * θ.write k) Set.univ := by
    intro b
    refine analyticOnNhd_matMul' ?_ analyticOnNhd_const
    show AnalyticOnNhd ℝ (fun w : Matrix T (hid k) ℝ => fun t j => (1 - w t j ^ 2) * b t j)
      Set.univ
    exact AnalyticOnNhd.pi fun t => AnalyticOnNhd.pi fun j =>
      (analyticOnNhd_const.sub ((analyticOnNhd_matrix_entry t j).pow 2)).mul analyticOnNhd_const
  have hT1an : ∀ Ξ, AnalyticOnNhd ℝ (T1 Ξ) Set.univ := fun Ξ =>
    analyticOnNhd_clm_apply' hJ (hdirAn (Ξ * C))
  have hT3an : ∀ Ξ, AnalyticOnNhd ℝ (T3 Ξ) Set.univ := fun Ξ =>
    (analyticOnNhd_clm_apply' hJ (hdirAn (B Ξ))).neg
  have hT0eq : T0 = fun w => fderiv ℝ
      (fun p : Params (Arch.mlp (T := T) (d := d) Real.tanh (rmsNorm ε) hid) dIn dOut
          × Matrix T d ℝ => suffix (Arch.mlp Real.tanh (rmsNorm ε) hid) 0 p.1 k.succ p.2)
      (θ, w * θ.write k) (η, w * η.write k) := by
    funext w
    exact fderiv_partial_add' (Φ := fun θ' h' =>
        suffix (Arch.mlp (T := T) (d := d) Real.tanh (rmsNorm ε) hid) 0 θ' k.succ h')
      (hΦ _ (Set.mem_univ _)).differentiableAt η (w * η.write k)
  have hT0an : AnalyticOnNhd ℝ T0 Set.univ := by
    rw [hT0eq]
    exact analyticOnNhd_clm_apply' (hΦ.fderiv.comp (analyticOnNhd_const.prod
        ((mulRightCLM' (m := T) (θ.write k)).analyticOnNhd Set.univ)) (Set.mapsTo_univ _ _))
      (analyticOnNhd_const.prod ((mulRightCLM' (m := T) (η.write k)).analyticOnNhd Set.univ))
  -- on the ray `n = t Ξ`, (23) reads `𝒯_0(w) + t 𝒯_1(w) + t³ 𝒯_3(w) = 0` at `w = tanh(t Ξ W)`
  have hray : ∀ (Ξ : Matrix T d ℝ) (t : ℝ),
      T0 ((t • (Ξ * θ.read k)).map Real.tanh) + t • T1 Ξ ((t • (Ξ * θ.read k)).map Real.tanh)
        + t ^ 3 • T3 Ξ ((t • (Ξ * θ.read k)).map Real.tanh) = 0 := by
    intro Ξ t
    have e := h23 (t • Ξ)
    rw [hzdot Ξ t] at e
    unfold blockLHS at e
    simp only [Matrix.smul_mul] at e
    -- the direction splits into its parts of degree `1` and `3` in `t`
    have hdir : (Matrix.of fun a j =>
        ((t • (Ξ * θ.read k)).map fun z => 1 - Real.tanh z ^ 2) a j
          * (t • (Ξ * C) - t ^ 3 • B Ξ) a j)
        = t • (Matrix.of fun a j =>
            (1 - ((t • (Ξ * θ.read k)).map Real.tanh) a j ^ 2) * (Ξ * C) a j)
          - t ^ 3 • (Matrix.of fun a j =>
            (1 - ((t • (Ξ * θ.read k)).map Real.tanh) a j ^ 2) * B Ξ a j) := by
      ext a j
      simp only [Matrix.of_apply, Matrix.map_apply, Matrix.smul_apply, Matrix.sub_apply,
        smul_eq_mul]
      ring
    rw [hdir, Matrix.sub_mul, Matrix.smul_mul, Matrix.smul_mul, map_add, map_sub, map_smul,
      map_smul] at e
    show (_ + _) + t • _ + t ^ 3 • -_ = 0
    rw [smul_neg, ← sub_eq_add_neg, add_sub_assoc, add_comm, ← add_assoc]
    exact e
  -- for `Ξ` in the dense set of (T2) on a ray, Lemma D.1 makes `𝒯_0`, `𝒯_1 Ξ`, `𝒯_3 Ξ` vanish
  have hsep : ∀ Ξ ∈ {Ξ : Matrix T d ℝ |
      LinearIndependent ℚ (fun p : T × hid k => (Ξ * θ.read k) p.1 p.2)},
      (∀ w, T0 w = 0) ∧ (∀ w, T1 Ξ w = 0) ∧ ∀ w, T3 Ξ w = 0 := by
    intro Ξ hΞ
    have hs := tanh_ray_separation_matrix (Ξ * θ.read k) hΞ 3 ![T0, T1 Ξ, 0, T3 Ξ]
      (fun i => by fin_cases i; exacts [hT0an, hT1an Ξ, analyticOnNhd_const, hT3an Ξ])
      (fun t _ => by simpa [Fin.sum_univ_four] using hray Ξ t)
    exact ⟨hs 0, hs 1, hs 3⟩
  have hD := dense_setOf_linearIndependent_mul (T := T) (θ.read k) hT2
  obtain ⟨t₀⟩ := ‹Nonempty T›
  -- (b): `Ξ C = 0` on the dense set (by the fact), so for every `Ξ`, so `C = 0`
  have hΞC : ∀ Ξ ∈ {Ξ : Matrix T d ℝ |
      LinearIndependent ℚ (fun p : T × hid k => (Ξ * θ.read k) p.1 p.2)}, Ξ * C = 0 :=
    fun Ξ hΞ => eq_zero_of_fderiv_suffix_one_sub_sq_rmsNorm θ hε hθ k hT1 (Ξ * C) (hsep Ξ hΞ).2.1
  have hall : (fun Ξ : Matrix T d ℝ => Ξ * C) = fun _ => 0 :=
    Continuous.ext_on hD (continuous_id.matrix_mul continuous_const) continuous_const hΞC
  have hC0 : C = 0 := by
    ext i j
    have e := congrFun (congrFun (congrFun hall (Matrix.single t₀ i (1 : ℝ))) t₀) j
    simpa only [Matrix.single_mul_apply_same, one_mul, Matrix.zero_apply] using e
  have hread : η.read k = -(Z * θ.read k) := by
    rw [hC] at hC0
    rw [eq_neg_iff_add_eq_zero, add_comm]
    exact hC0
  -- (a): `B Ξ = 0` on the dense set (by the fact), so for every `Ξ` ...
  have hBΞ : ∀ Ξ ∈ {Ξ : Matrix T d ℝ |
      LinearIndependent ℚ (fun p : T × hid k => (Ξ * θ.read k) p.1 p.2)}, B Ξ = 0 :=
    fun Ξ hΞ => eq_zero_of_fderiv_suffix_one_sub_sq_rmsNorm θ hε hθ k hT1 (B Ξ)
      fun w => neg_eq_zero.1 ((hsep Ξ hΞ).2.2 w)
  have hBc : Continuous B := by
    show Continuous fun Ξ : Matrix T d ℝ => Matrix.of fun τ j =>
      ((Ξ * Z) τ ⬝ᵥ Ξ τ / (Fintype.card d : ℝ)) * (Ξ * θ.read k) τ j
    simp only [dotProduct]
    fun_prop
  have hBall : B = fun _ => 0 := Continuous.ext_on hD hBc continuous_const hBΞ
  -- ... so `⟨ξ Z, ξ⟩ = 0` for every row `ξ`, and `Z` is antisymmetric
  have hanti : Z ∈ antisymmetric d := by
    rcases isEmpty_or_nonempty (hid k) with hh | ⟨⟨j₀⟩⟩
    · -- no hidden unit: the write has no rows and rank `d`, so `d` is empty
      have h1 : Fintype.card d ≤ Fintype.card (hid k) := by
        have h := Matrix.rank_le_card_height (θ.write k)
        rw [hθ.rank_write k] at h
        exact h
      have h2 : Fintype.card (hid k) = 0 := Fintype.card_eq_zero_iff.2 hh
      have : IsEmpty d := Fintype.card_eq_zero_iff.1 (by omega)
      show Zᵀ = -Z
      ext i
      exact isEmptyElim i
    · -- a hidden unit `j₀`: its read column `c` is not zero (T2)
      let c : d → ℝ := fun i => θ.read k i j₀
      have hc : c ≠ 0 := hT2.ne_zero j₀
      -- with all rows of `Ξ` equal to `ξ`: `(⟨ξ Z, ξ⟩ / d) (ξ ⬝ c) = 0`
      have hpoly : ∀ ξ : d → ℝ, ((ξ ᵥ* Z) ⬝ᵥ ξ / (Fintype.card d : ℝ)) * (ξ ⬝ᵥ c) = 0 :=
        fun ξ => congrFun (congrFun (congrFun hBall (Matrix.of fun _ : T => ξ)) t₀) j₀
      -- the `ξ` with `ξ ⬝ c ≠ 0` are dense, so `⟨ξ Z, ξ⟩ / d = 0` for every `ξ`
      have hdense : Dense {ξ : d → ℝ | ξ ⬝ᵥ c ≠ 0} :=
        dense_setOf_ne_zero_of_linear' (fun ξ : d → ℝ => ξ ⬝ᵥ c)
          (fun x y => add_dotProduct x y c) (fun a x => by rw [smul_dotProduct, smul_eq_mul])
          (x₀ := c) (fun h => hc (dotProduct_self_eq_zero.1 h))
      have hq' : (fun ξ : d → ℝ => (ξ ᵥ* Z) ⬝ᵥ ξ / (Fintype.card d : ℝ)) = fun _ => 0 :=
        Continuous.ext_on hdense (by simp only [dotProduct, vecMul]; fun_prop) continuous_const
          fun ξ hξ => (mul_eq_zero.1 (hpoly ξ)).resolve_right hξ
      -- `d` is not empty, so `d ≠ 0`
      have hd : (Fintype.card d : ℝ) ≠ 0 := by
        obtain ⟨i, -⟩ := Function.ne_iff.1 hc
        have : Nonempty d := ⟨i⟩
        exact Nat.cast_ne_zero.2 Fintype.card_ne_zero
      refine mem_antisymmetric_of_vecMul_dotProduct_self fun ξ => ?_
      have e := congrFun hq' ξ
      rwa [div_eq_zero_iff, or_iff_left hd] at e
  -- (c): `𝒯_0 = 0` is the hypothesis of Lemma D.3 at the write `V` (rank `d`)
  obtain ⟨Ξ₀, hΞ₀⟩ := hD.nonempty
  obtain ⟨Z', hZ', hflat'⟩ := suffixFlat_of_flat_at_write_rmsNorm
    (Arch.mlp (T := T) (d := d) Real.tanh (rmsNorm ε) hid) θ hε rfl hf hθ k.succ (θ.write k)
    (hθ.rank_write k) (η.write k) η (hsep Ξ₀ hΞ₀).1
  -- `(D_{k+1})` gives the antisymmetric changes of basis after the block
  obtain ⟨X, hXk, hXa, hX, hXD⟩ := hk Z' η hflat'
  -- put `Z` at the hidden state before the block
  refine ⟨Function.update X k.castSucc Z, Function.update_self _ _ _, fun ℓ hℓ => ?_,
    fun ℓ hℓ => ?_, ?_⟩
  · -- antisymmetric: `Z` by (a), the later ones by `(D_{k+1})`
    rcases eq_or_ne ℓ k.castSucc with rfl | hne
    · rw [Function.update_self]
      exact hanti
    · rw [Function.update_of_ne hne]
      refine hXa ℓ ?_
      have hlt : k.castSucc < ℓ := lt_of_le_of_ne hℓ (Ne.symm hne)
      rw [Fin.lt_def, Fin.val_castSucc] at hlt
      rw [Fin.le_def, Fin.val_succ]
      omega
  · rcases eq_or_ne ℓ k with rfl | hne
    · -- the block itself: (b) and (c)
      rw [Function.update_self, Function.update_of_ne (Fin.castSucc_lt_succ).ne', hXk]
      exact ⟨hread, hZ'⟩
    · -- a later block: `(D_{k+1})`
      have hlt : k < ℓ := lt_of_le_of_ne (Fin.castSucc_le_castSucc_iff.1 hℓ) (Ne.symm hne)
      have hle : k.succ ≤ ℓ.castSucc := by
        rw [Fin.le_def, Fin.val_succ, Fin.val_castSucc]
        exact hlt
      have h1 : ℓ.castSucc ≠ k.castSucc := fun h => hne (Fin.castSucc_injective _ h)
      have h2 : ℓ.succ ≠ k.castSucc := by
        intro h
        have := congrArg Fin.val h
        rw [Fin.val_succ, Fin.val_castSucc] at this
        have := Fin.lt_def.1 hlt
        omega
      rw [Function.update_of_ne h1, Function.update_of_ne h2]
      exact hX ℓ hle
  · -- the readout
    rw [Function.update_of_ne (Fin.castSucc_lt_last k).ne']
    exact hXD

end Skips
