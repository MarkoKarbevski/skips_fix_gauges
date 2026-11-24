import SkipsLean.Depth.SuffixZero

/-!
# The case (0): regular parameters and the derivative of `𝓑_{>k}`

Paper (dimension paper): Appendix D.3 in the case (0), pre-RMSNorm with `ε = 0`. "We call `θ`
regular if (R1) `E`, `D` and every `W_write^ℓ` have rank `d`; (R2) in the case (0), for every `ℓ`
and every `n ∈ S`: `g_ℓ(n) ≠ 0`; (R3) for every `ℓ`: […] in the case (0), there is an `n ∈ S` such
that no row `v ≠ 0` with `⟨v, n⟩ = 0` has `𝐃g_ℓ(n) v ∈ ℝ g_ℓ(n)`. […] In the case (0), by (R2),
[`𝓑_{>k}`] is defined and real-analytic on all rows `h ≠ 0`."

Lemma D.2 (The derivative of `𝓑_{>k}`), the case (0): "Let `θ` be regular. For every `k` there is
an open dense set `U_k` of rows such that, for `h ∈ U_k`, `𝐃𝓑_{>k}(h) v = 0` only if […]
`v ∈ ℝ h`, in the case (0). In the case (0), `U_k` consists of rows `h ≠ 0` and is closed under
multiplication by positive numbers."

Here `S` is the sphere `‖n‖² = d`, `g_ℓ(n) = f_ℓ(n W_read^ℓ) W_write^ℓ` is block `ℓ`, and a hidden
state has the rows `T` (tokens): "`h ≠ 0`" is "no row of `h` vanishes", "`n ∈ S`" is "every row of
`n` is on `S`", "`v ∈ ℝ h`" is "every row of `v` is a multiple of the same row of `h`", and the
positive numbers multiply the rows one by one. For blocks that act on every token alone (MLP
blocks) these are the paper's statements for one token, at every token.
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable (A : Arch T d L) (θ : Params A dIn dOut)

/-- "`θ` is regular", in the case (0): (R1) `E`, `D` and every write have rank `d`; (R2) no row of
`g_ℓ(n)` vanishes when every row of `n` is on the sphere `‖n‖² = d`; (R3) for every block there is
such an `n` at which a `v` whose rows are orthogonal to the rows of `n`, and for which every row of
`𝐃g_ℓ(n) v` is a multiple of the same row of `g_ℓ(n)`, is `0`. -/
structure RegularZero : Prop where
  rank_E : θ.E.rank = Fintype.card d
  rank_D : θ.D.rank = Fintype.card d
  rank_write : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d
  block_ne_zero : ∀ (ℓ : Fin L) (n : Matrix T d ℝ),
    (∀ t, n t ⬝ᵥ n t = (Fintype.card d : ℝ)) →
      ∀ t, (A.f ℓ (n * θ.read ℓ) * θ.write ℓ) t ≠ 0
  deriv_block : ∀ ℓ : Fin L, ∃ n : Matrix T d ℝ, (∀ t, n t ⬝ᵥ n t = (Fintype.card d : ℝ)) ∧
    ∀ v : Matrix T d ℝ, (∀ t, v t ⬝ᵥ n t = 0) →
      (∀ t, ∃ a : ℝ,
        fderiv ℝ (fun n' : Matrix T d ℝ => A.f ℓ (n' * θ.read ℓ) * θ.write ℓ) n v t
          = a • (A.f ℓ (n * θ.read ℓ) * θ.write ℓ) t) →
      v = 0

omit [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- RMSNorm with `ε = 0` maps a nonzero row to the sphere `‖n‖² = d`. -/
theorem rmsNorm_zero_dotProduct_self (h : Matrix T d ℝ) (t : T) (ht : h t ≠ 0) :
    (rmsNorm 0 h) t ⬝ᵥ (rmsNorm 0 h) t = (Fintype.card d : ℝ) := by
  -- `N(h)_t = ρ⁻¹ h_t` with `ρ² = ‖h_t‖²/d > 0`
  have h1 : 0 < h t ⬝ᵥ h t :=
    lt_of_le_of_ne (Finset.sum_nonneg fun j _ => mul_self_nonneg (h t j))
      (fun h0 => ht (dotProduct_self_eq_zero.1 h0.symm))
  obtain ⟨j, -⟩ := Function.ne_iff.1 ht
  have h2 : (0 : ℝ) < Fintype.card d := Nat.cast_pos.2 (Fintype.card_pos_iff.2 ⟨j⟩)
  have hq : 0 < (h t ⬝ᵥ h t) / (Fintype.card d : ℝ) + 0 := by
    rw [add_zero]; exact div_pos h1 h2
  show rmsRow 0 (h t) ⬝ᵥ rmsRow 0 (h t) = _
  unfold rmsRow
  rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc, ← mul_inv,
    Real.mul_self_sqrt hq.le, add_zero]
  field_simp

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (the `AnalyticAt` form of `analyticOnNhd_matrix_mul`): the matrix product of two
maps analytic at a point is analytic there. -/
private theorem analyticAt_matrix_mul_zd {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
    {f : E → Matrix m n ℝ} {g : E → Matrix n p ℝ} {x : E}
    (hf : AnalyticAt ℝ f x) (hg : AnalyticAt ℝ g x) :
    AnalyticAt ℝ (fun y => f y * g y) x := by
  let B : Matrix m n ℝ →ₗ[ℝ] Matrix n p ℝ →ₗ[ℝ] Matrix m p ℝ :=
    LinearMap.mk₂ ℝ (fun a b => a * b) Matrix.add_mul (fun c a b => Matrix.smul_mul c a b)
      Matrix.mul_add (fun c a b => Matrix.mul_smul a c b)
  let B' : Matrix m n ℝ →L[ℝ] Matrix n p ℝ →L[ℝ] Matrix m p ℝ :=
    LinearMap.toContinuousLinearMap
      ((LinearMap.toContinuousLinearMap :
        (Matrix n p ℝ →ₗ[ℝ] Matrix m p ℝ) ≃ₗ[ℝ] (Matrix n p ℝ →L[ℝ] Matrix m p ℝ)).toLinearMap ∘ₗ B)
  have hB : (fun y => f y * g y) = fun y => B' (f y) (g y) := rfl
  rw [hB]
  exact (B'.analyticAt_bilinear (f x, g x)).comp₂ hf hg

/-- **Appendix D.3, the case (0): "by (R2), it is defined and real-analytic on all rows `h ≠ 0`".**
For real-analytic blocks under pre-RMSNorm with `ε = 0`, at parameters with (R2), the map
`(θ', h') ↦ 𝓑_{>k}(h')` at the weights `θ'` is real-analytic at `(θ, h)` for every `h` without a
zero row. -/
theorem analyticAt_suffix_prod_zero (hχ : A.χ = rmsNorm 0)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (hθ : RegularZero A θ) (k : Fin (L + 1))
    (h : Matrix T d ℝ) (hh : ∀ t, h t ≠ 0) :
    AnalyticAt ℝ
      (fun p : Params A dIn dOut × Matrix T d ℝ => suffix A 0 p.1 k p.2) (θ, h) := by
  -- the weights are linear, hence analytic, functions of the parameters
  have hD : AnalyticOnNhd ℝ (fun p : Params A dIn dOut × Matrix T d ℝ => p.1.D) Set.univ :=
    ((LinearMap.toContinuousLinearMap
      (Params.linD (A := A) (dIn := dIn) (dOut := dOut))).analyticOnNhd _).comp
      analyticOnNhd_fst (Set.mapsTo_univ _ _)
  have hr : ∀ ℓ, AnalyticOnNhd ℝ
      (fun p : Params A dIn dOut × Matrix T d ℝ => p.1.read ℓ) Set.univ := fun ℓ =>
    ((LinearMap.toContinuousLinearMap
      (Params.linRead (A := A) (dIn := dIn) (dOut := dOut) ℓ)).analyticOnNhd _).comp
      analyticOnNhd_fst (Set.mapsTo_univ _ _)
  have hw : ∀ ℓ, AnalyticOnNhd ℝ
      (fun p : Params A dIn dOut × Matrix T d ℝ => p.1.write ℓ) Set.univ := fun ℓ =>
    ((LinearMap.toContinuousLinearMap
      (Params.linWrite (A := A) (dIn := dIn) (dOut := dOut) ℓ)).analyticOnNhd _).comp
      analyticOnNhd_fst (Set.mapsTo_univ _ _)
  induction k using Fin.reverseInduction generalizing h with
  | last =>
    -- `(θ', h') ↦ N(h') D'`
    simp only [suffix_last, hχ]
    have hN : AnalyticAt ℝ (fun p : Params A dIn dOut × Matrix T d ℝ => rmsNorm 0 p.2) (θ, h) := by
      have hc := (analyticAt_rmsNorm_zero h hh).comp (analyticAt_snd (𝕜 := ℝ) (p := (θ, h)))
      exact hc
    exact analyticAt_matrix_mul_zd hN (hD _ (Set.mem_univ _))
  | cast ℓ ih =>
    -- `(θ', h') ↦ 𝓑_{>ℓ}(f_ℓ(N(h') W'_read) W'_write)`, with the weights `θ'`
    simp only [suffix_castSucc, Pi.zero_apply, Matrix.mul_zero, zero_add, hχ]
    have hN : AnalyticAt ℝ (fun p : Params A dIn dOut × Matrix T d ℝ => rmsNorm 0 p.2) (θ, h) := by
      have hc := (analyticAt_rmsNorm_zero h hh).comp (analyticAt_snd (𝕜 := ℝ) (p := (θ, h)))
      exact hc
    have hg : AnalyticAt ℝ (fun p : Params A dIn dOut × Matrix T d ℝ =>
        (p.1, A.f ℓ (rmsNorm 0 p.2 * p.1.read ℓ) * p.1.write ℓ)) (θ, h) :=
      analyticAt_fst.prod (analyticAt_matrix_mul_zd
        ((hf ℓ _ (Set.mem_univ _)).comp (analyticAt_matrix_mul_zd hN (hr ℓ _ (Set.mem_univ _))))
        (hw ℓ _ (Set.mem_univ _)))
    -- the block's value at `(θ, h)` has no zero row, by (R2): the rows of `N(h)` are on the sphere
    have hne : ∀ t, (A.f ℓ (rmsNorm 0 h * θ.read ℓ) * θ.write ℓ) t ≠ 0 :=
      hθ.block_ne_zero ℓ _ fun t => rmsNorm_zero_dotProduct_self h t (hh t)
    have hc := (ih _ hne).comp_of_eq hg rfl
    exact hc

omit [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (as `rmsRow_zero_smul` in `Basic/RMSNorm.lean`, private there): `N_0(c w) = N_0(w)`
for `c > 0`, also for `w = 0`. -/
private theorem rmsRow_zero_smul_zd {c : ℝ} (hc : 0 < c) (w : d → ℝ) :
    rmsRow 0 (c • w) = rmsRow 0 w := by
  unfold rmsRow
  have hs : Real.sqrt ((c • w ⬝ᵥ c • w) / (Fintype.card d : ℝ) + 0)
      = c * Real.sqrt ((w ⬝ᵥ w) / (Fintype.card d : ℝ) + 0) := by
    have : (c • w ⬝ᵥ c • w) / (Fintype.card d : ℝ) + 0
        = c ^ 2 * ((w ⬝ᵥ w) / (Fintype.card d : ℝ) + 0) := by
      rw [smul_dotProduct, dotProduct_smul]
      simp only [smul_eq_mul, add_zero]
      ring
    rw [this, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc.le]
  rw [hs, mul_inv, smul_smul]
  congr 1
  rw [mul_comm c⁻¹, mul_assoc, inv_mul_cancel₀ hc.ne', mul_one]

omit [Fintype T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: `N_0` forgets positive scales of the rows. -/
private theorem rmsNorm_zero_smul_rows_zd (h : Matrix T d ℝ) (c : T → ℝ) (hc : ∀ t, 0 < c t) :
    rmsNorm 0 (Matrix.of fun t => c t • h t) = rmsNorm 0 h := by
  ext t i
  show rmsRow 0 (c t • h t) i = rmsRow 0 (h t) i
  rw [rmsRow_zero_smul_zd (hc t)]

/-- **Appendix D.3, the case (0), "`𝓑_{>k}(λh) = 𝓑_{>k}(h)` for `λ > 0`":** under pre-RMSNorm with
`ε = 0`, multiplying the rows of `h` by positive numbers does not change `𝓑_{>k}(h)`. -/
theorem suffix_zero_smul_rows (hχ : A.χ = rmsNorm 0) (k : Fin (L + 1)) (h : Matrix T d ℝ)
    (c : T → ℝ) (hc : ∀ t, 0 < c t) :
    suffix A 0 θ k (Matrix.of fun t => c t • h t) = suffix A 0 θ k h := by
  -- `𝓑_{>k}(h)` depends on `h` only through `N(h)`
  induction k using Fin.reverseInduction with
  | last => rw [suffix_last, suffix_last, hχ, rmsNorm_zero_smul_rows_zd h c hc]
  | cast ℓ _ =>
    simp only [suffix_castSucc, Pi.zero_apply, Matrix.mul_zero, zero_add, hχ,
      rmsNorm_zero_smul_rows_zd h c hc]

/-- **Lemma D.2 of the dimension paper (the derivative of `𝓑_{>k}`), the case (0):** let the
blocks be real-analytic, `d ≥ 2`, and `θ` regular. For every `k` there is an open dense set `U_k`
of matrices without a zero row, closed under multiplication of the rows by positive numbers, such
that for `h ∈ U_k`, `𝐃𝓑_{>k}(h) v = 0` only if every row of `v` is a multiple of the same row of
`h`. -/
theorem exists_open_dense_fderiv_suffix_zero (hχ : A.χ = rmsNorm 0)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (hθ : RegularZero A θ)
    (hd : 2 ≤ Fintype.card d) (k : Fin (L + 1)) :
    ∃ U : Set (Matrix T d ℝ), IsOpen U ∧ Dense U ∧ (∀ h ∈ U, ∀ t, h t ≠ 0) ∧
      (∀ h ∈ U, ∀ c : T → ℝ, (∀ t, 0 < c t) → (Matrix.of fun t => c t • h t) ∈ U) ∧
      ∀ h ∈ U, ∀ v : Matrix T d ℝ,
        fderiv ℝ (fun h' : Matrix T d ℝ => suffix A 0 θ k h') h v = 0 →
          ∀ t, ∃ a : ℝ, v t = a • h t := by
  sorry

end Skips
