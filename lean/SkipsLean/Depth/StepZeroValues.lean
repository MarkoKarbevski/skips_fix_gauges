import SkipsLean.Depth.StepTanhRMS
import SkipsLean.Depth.SuffixZeroClaim

/-!
# The identity for one block in the case (0), and Lemma D.17

Paper (dimension paper): Appendix D.3, equations (14) and (20) to (22), in the case (0)
(pre-RMSNorm with `ε = 0`), and Appendix D.6, Lemma D.17.

Equation (14): "In the cases (+) and (0), for a `d × d` matrix `Z` and `n = χ(h)`,
`𝐃χ(h)(hZ) = nZ − (⟨nZ, n⟩/d) n`." The identity for one block: with
`ż(n) = (nZ − (⟨nZ, n⟩/d) n) W + n η_W` (20) and
`𝓛(w̃, w̃'; n) = 𝐃𝓑(w̃V)((w̃' ⊙ ż(n)) V + w̃ η_V) + 𝐃_θ𝓑(w̃V) η'` (21), "(16) for `k` is
equivalent to `𝓛(σ(nW), σ'(nW); n) = 0` for all values `n` of `χ`, (22), that is, […] for `n ∈ S`
in the case (0)."

Lemma D.17 (A change of the reads moves the output): "In the case (0), let `θ` be regular with (S1)
for block `k + 1`, let `V = W_write^{k+1}` have the rows `a_1, …, a_q`, and let `b ∈ ℂ^{1 × q}`. If
`𝐃𝓑_{>k+1}(w̃V)(((1 − w̃²) ⊙ b) V) = 0` for all `w̃` in a nonempty open subset of `ℝ^{1 × q}`, […]
then `b = 0`." (S1): "any two rows of `V` are linearly independent". Here it is stated for a real
`b`, the case to which the paper's proof reduces ("At real `w̃` the derivative is a real linear
map, so the real and the imaginary part of `b` satisfy the hypothesis: let `b` be real").

Numbering and tokens are as in `Depth/StepTanh.lean`: the block is `k : Fin L`, the hidden state
before it `k.castSucc` and after it `k.succ`, a hidden state has the rows `T`, and `S` is "every
row on the sphere `‖n‖² = d`". `blockLHS` (`Depth/StepTanh.lean`) is `𝓛`, and `tangentRMS Z n`
(`Depth/StepTanhRMS.lean`) is `nZ − (⟨nZ, n⟩/d) n`.
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut] {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)] {σ σ' : ℝ → ℝ}

omit [Fintype T] [DecidableEq d] in
/-- Helper: a row of `N(h)`, `N` RMSNorm with `ε = 0`, is `ρ⁻¹ h_t` with `ρ = √(‖h_t‖² / d)`. -/
private theorem rmsNorm_zero_row_szv (h : Matrix T d ℝ) (t : T) :
    rmsNorm 0 h t = (Real.sqrt ((h t ⬝ᵥ h t) / (Fintype.card d : ℝ)))⁻¹ • h t := by
  show rmsRow 0 (h t) = _
  unfold rmsRow
  rw [add_zero]

omit [Fintype T] [DecidableEq d] in
/-- Helper: a row of `N(h) Z` is `ρ⁻¹ (h Z)_t`. -/
private theorem rmsNorm_zero_mul_row_szv (Z : Matrix d d ℝ) (h : Matrix T d ℝ) (t : T) :
    (rmsNorm 0 h * Z) t = (Real.sqrt ((h t ⬝ᵥ h t) / (Fintype.card d : ℝ)))⁻¹ • (h * Z) t := by
  rw [Matrix.mul_apply_eq_vecMul, Matrix.mul_apply_eq_vecMul, rmsNorm_zero_row_szv]
  exact Matrix.smul_vecMul (R := ℝ) _ (h t) Z

omit [DecidableEq d] in
/-- **Equation (14) in the case (0):** `𝐃N(h)(hZ) = nZ − (⟨nZ, n⟩/d) n` at `n = N(h)`, for `N`
RMSNorm with `ε = 0` and `h` without a zero row. -/
theorem fderiv_rmsNorm_zero_mul (Z : Matrix d d ℝ) (h : Matrix T d ℝ) (hh : ∀ t, h t ≠ 0) :
    fderiv ℝ (rmsNorm 0 : Matrix T d ℝ → Matrix T d ℝ) h (h * Z)
      = tangentRMS Z (rmsNorm 0 h) := by
  rw [fderiv_rmsNorm_zero_apply h (h * Z) hh]
  ext t i
  -- with `ρ = √(‖h_t‖² / d)`: `n_t = ρ⁻¹ h_t` and `(n Z)_t = ρ⁻¹ (h Z)_t`
  show (Real.sqrt ((h t ⬝ᵥ h t) / (Fintype.card d : ℝ)))⁻¹ * (h * Z) t i
      - ((h t ⬝ᵥ (h * Z) t) / (Fintype.card d : ℝ)
        * (Real.sqrt ((h t ⬝ᵥ h t) / (Fintype.card d : ℝ)))⁻¹ ^ 3) * h t i
    = (rmsNorm 0 h * Z) t i
      - ((rmsNorm 0 h * Z) t ⬝ᵥ rmsNorm 0 h t) / (Fintype.card d : ℝ) * rmsNorm 0 h t i
  rw [rmsNorm_zero_mul_row_szv, rmsNorm_zero_row_szv, smul_dotProduct, dotProduct_smul,
    Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul,
    dotProduct_comm ((h * Z) t) (h t)]
  ring

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the line `τ ↦ a + τ b` has the velocity `b` (as in `Depth/StepTanhRMS.lean`). -/
private theorem hasDerivAt_line_szv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a b : E) : HasDerivAt (fun τ : ℝ => a + τ • b) b 0 := by
  have h := ((hasDerivAt_id (0 : ℝ)).smul_const b).const_add a
  rw [one_smul] at h
  exact h

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the product rule for matrix-valued functions of one real variable (as in
`Depth/StepTanhRMS.lean`). -/
private theorem hasDerivAt_matMul_szv {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
    {A : ℝ → Matrix m n ℝ} {B : ℝ → Matrix n p ℝ} {A' : Matrix m n ℝ} {B' : Matrix n p ℝ}
    {τ : ℝ} (hA : HasDerivAt A A' τ) (hB : HasDerivAt B B' τ) :
    HasDerivAt (fun s => A s * B s) (A' * B τ + A τ * B') τ := by
  refine hasDerivAt_pi.2 fun t => hasDerivAt_pi.2 fun i => ?_
  have h := HasDerivAt.fun_sum (u := Finset.univ) fun j _ =>
    (hasDerivAt_pi.1 (hasDerivAt_pi.1 hA t) j).mul (hasDerivAt_pi.1 (hasDerivAt_pi.1 hB j) i)
  simp only [Matrix.mul_apply, Matrix.add_apply, ← Finset.sum_add_distrib]
  exact h

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the derivative of `s ↦ σ(P(s))`, entry by entry (as in `Depth/StepTanhRMS.lean`). -/
private theorem hasDerivAt_map_szv {m n : Type*} [Fintype m] [Fintype n]
    (hσ : ∀ z, HasDerivAt σ (σ' z) z) {P : ℝ → Matrix m n ℝ} {P' : Matrix m n ℝ} {τ : ℝ}
    (hP : HasDerivAt P P' τ) :
    HasDerivAt (fun s => (P s).map σ) (Matrix.of fun t j => σ' (P τ t j) * P' t j) τ :=
  hasDerivAt_pi.2 fun t => hasDerivAt_pi.2 fun j =>
    (hσ (P τ t j)).comp τ (hasDerivAt_pi.1 (hasDerivAt_pi.1 hP t) j)

/-- Helper: for `Φ` differentiable at `(x, y)`, the derivatives of its two partial maps add up to
its derivative along `(a, b)` (as in `Depth/StepTanhRMS.lean`). -/
private theorem fderiv_partial_add_szv {E₁ E₂ F : Type*} [NormedAddCommGroup E₁]
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

omit [DecidableEq d] in
/-- Helper: equation (14) along the line `τ ↦ h + τ h Z`, at `h` without a zero row. -/
private theorem hasDerivAt_rmsNorm_zero_line_szv (Z : Matrix d d ℝ) (h : Matrix T d ℝ)
    (hh : ∀ t, h t ≠ 0) :
    HasDerivAt (fun τ : ℝ => rmsNorm 0 (h + τ • (h * Z))) (tangentRMS Z (rmsNorm 0 h)) 0 := by
  rw [← fderiv_rmsNorm_zero_mul Z h hh]
  have hc := (analyticAt_rmsNorm_zero h hh).differentiableAt.hasFDerivAt.comp_hasDerivAt_of_eq
    (0 : ℝ) (hasDerivAt_line_szv h (h * Z)) (by rw [zero_smul, add_zero])
  exact hc

/-- **The identity for one block, case (0)** (equation (22), by the chain rule and (14)): for an
MLP block with a real-analytic activation `σ` with derivative `σ'`, and regular `θ`, the identity
(16) for the hidden state before block `k` holds for `Z` and `η` if and only if
`𝓛(σ(n W), σ'(n W); n) = 0` at every value `n = N(h)`, `h` without a zero row, with
`ż(n) = (n Z − (⟨n Z, n⟩/d) n) W + n η_W`. -/
theorem suffixFlatZero_castSucc_iff_mlp_values (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
    (hθ : RegularZero (Arch.mlp σ (rmsNorm 0) hid) θ) (k : Fin L)
    (Z : Matrix d d ℝ) (η : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) :
    SuffixFlatZero (Arch.mlp σ (rmsNorm 0) hid) θ k.castSucc Z η ↔
      ∀ h : Matrix T d ℝ, (∀ t, h t ≠ 0) →
        blockLHS θ k η ((rmsNorm 0 h * θ.read k).map σ) ((rmsNorm 0 h * θ.read k).map σ')
          (tangentRMS Z (rmsNorm 0 h) * θ.read k + rmsNorm 0 h * η.read k) = 0 := by
  have hf : ∀ ℓ, AnalyticOnNhd ℝ ((Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid).f ℓ) Set.univ :=
    fun ℓ => analyticOnNhd_f_mlp hσa ℓ
  -- it suffices that the two left sides agree at every `h` without a zero row
  suffices key : ∀ h : Matrix T d ℝ, (∀ t, h t ≠ 0) →
      fderiv ℝ (fun h' : Matrix T d ℝ => suffix (Arch.mlp σ (rmsNorm 0) hid) 0 θ k.castSucc h') h
          (h * Z)
        + fderiv ℝ (fun θ' : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut =>
            suffix (Arch.mlp σ (rmsNorm 0) hid) 0 θ' k.castSucc h) θ η
      = blockLHS θ k η ((rmsNorm 0 h * θ.read k).map σ) ((rmsNorm 0 h * θ.read k).map σ')
          (tangentRMS Z (rmsNorm 0 h) * θ.read k + rmsNorm 0 h * η.read k) by
    exact forall_congr' fun h => forall_congr' fun hh => by rw [key h hh]
  intro h hh
  -- the rows of `n = N(h)` are on the sphere, so by (R2) `g = σ(n W) V` has no zero row
  have hg0 : ∀ t, ((rmsNorm 0 h * θ.read k).map σ * θ.write k) t ≠ 0 :=
    hθ.block_ne_zero k (rmsNorm 0 h) fun t => rmsNorm_zero_dotProduct_self h t (hh t)
  -- so `(θ', h') ↦ 𝓑_{>k}(h')` is differentiable at `(θ, h)`, and `(θ', h') ↦ 𝓑_{>k+1}(h')` at
  -- `(θ, g)`
  have hΨ := (analyticAt_suffix_prod_zero (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) θ rfl hf
    hθ k.castSucc h hh).differentiableAt
  have hΦ := (analyticAt_suffix_prod_zero (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) θ rfl hf
    hθ k.succ _ hg0).differentiableAt
  -- the block along the line `τ ↦ (θ + τ η, h + τ h Z)`, entrywise, with (14): equation (22)
  have hg := hasDerivAt_matMul_szv (hasDerivAt_map_szv hσ (hasDerivAt_matMul_szv
    (hasDerivAt_rmsNorm_zero_line_szv Z h hh) (hasDerivAt_line_szv (θ.read k) (η.read k))))
    (hasDerivAt_line_szv (θ.write k) (η.write k))
  simp only [zero_smul, add_zero] at hg
  -- the derivative of `τ ↦ 𝓑_{>k}(h + τ h Z)` (with the weights `θ + τ η`) at `0`, directly ...
  have e1 : HasDerivAt
      (fun τ : ℝ => suffix (Arch.mlp σ (rmsNorm 0) hid) 0 (θ + τ • η) k.castSucc (h + τ • (h * Z)))
      (fderiv ℝ (fun p : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut
          × Matrix T d ℝ => suffix (Arch.mlp σ (rmsNorm 0) hid) 0 p.1 k.castSucc p.2) (θ, h)
        (η, h * Z)) 0 := by
    have hc := hΨ.hasFDerivAt.comp_hasDerivAt_of_eq 0
      ((hasDerivAt_line_szv θ η).prodMk (hasDerivAt_line_szv h (h * Z))) (by simp)
    exact hc
  -- ... and through the block: `𝓑_{>k}(h') = 𝓑_{>k+1}(σ(N(h') W) V)`
  have e2 : HasDerivAt
      (fun τ : ℝ => suffix (Arch.mlp σ (rmsNorm 0) hid) 0 (θ + τ • η) k.castSucc (h + τ • (h * Z)))
      (fderiv ℝ (fun p : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut
          × Matrix T d ℝ => suffix (Arch.mlp σ (rmsNorm 0) hid) 0 p.1 k.succ p.2)
        (θ, (rmsNorm 0 h * θ.read k).map σ * θ.write k)
        (η, (Matrix.of fun t j => σ' ((rmsNorm 0 h * θ.read k) t j)
            * (tangentRMS Z (rmsNorm 0 h) * θ.read k + rmsNorm 0 h * η.read k) t j) * θ.write k
          + (rmsNorm 0 h * θ.read k).map σ * η.write k)) 0 := by
    have hc := hΦ.hasFDerivAt.comp_hasDerivAt_of_eq 0 ((hasDerivAt_line_szv θ η).prodMk hg)
      (by simp)
    have hfun : (fun τ : ℝ =>
        suffix (Arch.mlp σ (rmsNorm 0) hid) 0 (θ + τ • η) k.castSucc (h + τ • (h * Z)))
        = (fun p : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut × Matrix T d ℝ =>
            suffix (Arch.mlp σ (rmsNorm 0) hid) 0 p.1 k.succ p.2) ∘ fun τ : ℝ =>
          (θ + τ • η, (rmsNorm 0 (h + τ • (h * Z)) * (θ.read k + τ • η.read k)).map σ
            * (θ.write k + τ • η.write k)) := by
      funext τ
      simp only [Function.comp_apply, suffix_castSucc, Pi.zero_apply, Matrix.mul_zero, zero_add]
      rfl
    rw [hfun]
    exact hc
  -- both sides are derivatives of the joint maps `(θ', h') ↦ 𝓑(h')` along `(η, ·)`
  unfold blockLHS
  calc _ = _ := fderiv_partial_add_szv
        (Φ := fun θ' h' => suffix (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) 0 θ' k.castSucc h')
        hΨ η (h * Z)
    _ = _ := e1.unique e2
    _ = _ := (fderiv_partial_add_szv
        (Φ := fun θ' h' => suffix (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) 0 θ' k.succ h')
        hΦ η _).symm

omit [Fintype T] [DecidableEq d] in
/-- Helper: RMSNorm with `ε = 0` fixes a matrix whose rows are on the sphere `‖n‖² = d`. -/
private theorem rmsNorm_zero_eq_self_szv [Nonempty d] (n : Matrix T d ℝ)
    (hn : ∀ t, n t ⬝ᵥ n t = (Fintype.card d : ℝ)) : rmsNorm 0 n = n := by
  have hd : (Fintype.card d : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  ext t i
  show rmsRow 0 (n t) i = n t i
  unfold rmsRow
  rw [hn t, div_self hd, add_zero, Real.sqrt_one, inv_one, one_smul]

/-- **Equation (22) in the case (0), on the sphere:** under the same hypotheses and `d ≥ 1`, the
identity (16) before block `k` holds if and only if `𝓛(σ(n W), σ'(n W); n) = 0` for every `n` with
all rows on the sphere `‖n‖² = d`. -/
theorem suffixFlatZero_castSucc_iff_mlp_sphere [Nonempty d] (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
    (hθ : RegularZero (Arch.mlp σ (rmsNorm 0) hid) θ) (k : Fin L)
    (Z : Matrix d d ℝ) (η : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) :
    SuffixFlatZero (Arch.mlp σ (rmsNorm 0) hid) θ k.castSucc Z η ↔
      ∀ n : Matrix T d ℝ, (∀ t, n t ⬝ᵥ n t = (Fintype.card d : ℝ)) →
        blockLHS θ k η ((n * θ.read k).map σ) ((n * θ.read k).map σ')
          (tangentRMS Z n * θ.read k + n * η.read k) = 0 := by
  refine (suffixFlatZero_castSucc_iff_mlp_values hσ hσa θ hθ k Z η).trans
    ⟨fun hval n hn => ?_, fun hS h hh => hS _ fun t => rmsNorm_zero_dotProduct_self h t (hh t)⟩
  -- a matrix `n` with its rows on the sphere has no zero row (`d ≥ 1`), and `N(n) = n`
  have hn0 : ∀ t, n t ≠ 0 := fun t ht => by
    have e := hn t
    rw [ht, zero_dotProduct] at e
    exact Nat.cast_ne_zero.2 Fintype.card_ne_zero e.symm
  have e := hval n hn0
  rwa [rmsNorm_zero_eq_self_szv n hn] at e

/-- **Lemma D.17 of the dimension paper (a change of the reads moves the output), for a real `b`.**
In the case (0), let the blocks be real-analytic MLP blocks, `d ≥ 2`, `θ` regular, and let any two
rows of the write `V` of block `k` be linearly independent (S1). If
`𝐃𝓑(w̃ V)(((1 − w̃²) ⊙ b) V) = 0` for all `w̃` in a nonempty open set, then `b = 0`. -/
theorem eq_zero_of_fderiv_suffix_one_sub_sq_zero (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
    (hθ : RegularZero (Arch.mlp σ (rmsNorm 0) hid) θ) (hd : 2 ≤ Fintype.card d) (k : Fin L)
    (hS1 : ∀ i j : hid k, i ≠ j → ∀ a c : ℝ, a • θ.write k i + c • θ.write k j = 0 →
      a = 0 ∧ c = 0)
    (b : Matrix T (hid k) ℝ) (O : Set (Matrix T (hid k) ℝ)) (hO : IsOpen O) (hne : O.Nonempty)
    (h : ∀ w ∈ O,
      fderiv ℝ
        (fun h' : Matrix T d ℝ => suffix (Arch.mlp σ (rmsNorm 0) hid) 0 θ k.succ h')
        (w * θ.write k) ((Matrix.of fun t j => (1 - w t j ^ 2) * b t j) * θ.write k) = 0) :
    b = 0 := by
  sorry

end Skips
