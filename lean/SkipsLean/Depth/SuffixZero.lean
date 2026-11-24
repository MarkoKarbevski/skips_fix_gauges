import SkipsLean.Depth.SuffixRMS

/-!
# The claim `(D_k)` in the case (0): pre-RMSNorm with `ε = 0`

Paper (dimension paper): Appendix D.3 in the case (0). "For `k = 0, …, L` and a row `h`, with
`h ≠ 0` in the case (0), let `𝓑_{>k}(h)` be the output of the network when its hidden state `h_k`
is set to `h`." The identity (16) is asked "for all rows `h`, with `h ≠ 0` in the case (0)", and
Claim `(D_k)` reads, in the case (0) (equation (18)): "with `Z_ℓ = Y_ℓ + β_ℓ I` for antisymmetric
matrices `Y_k, …, Y_L` and numbers `β_k, …, β_L`,

`Z = Y_k + β_k I`, `η = ((−Y_{ℓ−1} W_read^ℓ, W_write^ℓ (Y_ℓ + β_ℓ I))_{ℓ=k+1}^L, −Y_L D)`."

Lemma D.5 (The readout), the case (0): "Here (16) is `𝐃N(h)(hZ) D + N(h) η_D = 0`. Multiplying by
`‖h‖³/√d` gives `‖h‖² h (ZD + η_D) = ⟨hZ, h⟩ hD` for all rows `h`. […] `Z = Y_L + βI` with `Y_L`
antisymmetric, and `η_D = −Y_L D`."

In Lean a hidden state has the rows `T` (tokens), and "`h ≠ 0`" is "no row of `h` vanishes". The
Lean `rmsNorm 0` maps a zero row to `0`; where a row vanishes it is not differentiable, and nothing
is claimed there.
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]

/-! ### RMSNorm with `ε = 0` away from the zero rows -/

/-- Helper: `√` is analytic at a positive number, where it agrees with `x ↦ exp (log x / 2)`. -/
private theorem analyticAt_sqrt_of_pos_sz {x : ℝ} (hx : 0 < x) : AnalyticAt ℝ Real.sqrt x := by
  have h : AnalyticAt ℝ (Real.exp ∘ fun y => Real.log y * (1 / 2)) x :=
    ((analyticAt_log hx).mul analyticAt_const).rexp
  refine h.congr ?_
  filter_upwards [lt_mem_nhds hx] with y hy
  show Real.exp (Real.log y * (1 / 2)) = Real.sqrt y
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hy]

omit [DecidableEq d] in
/-- Helper: `‖v‖² / d > 0` for a row `v ≠ 0` (then `d` is not empty). -/
private theorem dotProduct_self_div_pos_sz {v : d → ℝ} (hv : v ≠ 0) :
    0 < (v ⬝ᵥ v) / (Fintype.card d : ℝ) := by
  have h1 : 0 < v ⬝ᵥ v :=
    lt_of_le_of_ne (Finset.sum_nonneg fun j _ => mul_self_nonneg (v j))
      (fun h => hv (dotProduct_self_eq_zero.1 h.symm))
  obtain ⟨j, -⟩ := Function.ne_iff.1 hv
  have h2 : (0 : ℝ) < Fintype.card d := Nat.cast_pos.2 (Fintype.card_pos_iff.2 ⟨j⟩)
  exact div_pos h1 h2

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (as in `Depth/SuffixRMS.lean`): an entry of a matrix is a real-analytic (linear)
function of the matrix. -/
private theorem analyticAt_entry_sz {m n : Type*} [Fintype m] [Fintype n] (t : m) (i : n)
    (M₀ : Matrix m n ℝ) : AnalyticAt ℝ (fun M : Matrix m n ℝ => M t i) M₀ :=
  ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : n => ℝ) i).comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : m => n → ℝ) t)).analyticAt _

omit [DecidableEq d] in
/-- RMSNorm with `ε = 0` is real-analytic at every matrix without a zero row. -/
theorem analyticAt_rmsNorm_zero (h : Matrix T d ℝ) (hh : ∀ t, h t ≠ 0) :
    AnalyticAt ℝ (rmsNorm 0 : Matrix T d ℝ → Matrix T d ℝ) h := by
  -- entry `(t, i)` is `(√(‖h_t‖²/d + 0))⁻¹ h_{ti}`
  show AnalyticAt ℝ (fun h : Matrix T d ℝ => fun t => fun i =>
    (Real.sqrt ((h t ⬝ᵥ h t) / (Fintype.card d : ℝ) + 0))⁻¹ * h t i) h
  refine AnalyticAt.pi fun t => AnalyticAt.pi fun i => ?_
  -- the quantity under the root is a polynomial in the entries, positive at `h` (`h_t ≠ 0`)
  have hq : AnalyticAt ℝ (fun h : Matrix T d ℝ => (h t ⬝ᵥ h t) / (Fintype.card d : ℝ) + 0) h :=
    ((Finset.analyticAt_fun_sum _ fun j _ =>
      (analyticAt_entry_sz t j h).mul (analyticAt_entry_sz t j h)).div_const).add
        analyticAt_const
  have hpos : 0 < (h t ⬝ᵥ h t) / (Fintype.card d : ℝ) + 0 := by
    rw [add_zero]; exact dotProduct_self_div_pos_sz (hh t)
  -- `√` is analytic at a positive number, and the inverse where it is not zero
  exact (((analyticAt_sqrt_of_pos_sz hpos).comp
    (f := fun h : Matrix T d ℝ => (h t ⬝ᵥ h t) / (Fintype.card d : ℝ) + 0) hq).inv
      (Real.sqrt_pos.2 hpos).ne').mul (analyticAt_entry_sz t i h)

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: with the elementwise norm, the derivative of a matrix-valued function of one real
variable is taken entry by entry. -/
private theorem hasDerivAt_matrix_sz {m n : Type*} [Fintype m] [Fintype n]
    {f : ℝ → Matrix m n ℝ} {f' : Matrix m n ℝ} {x : ℝ}
    (h : ∀ i j, HasDerivAt (fun τ => f τ i j) (f' i j) x) : HasDerivAt f f' x :=
  hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 (h i)

omit [DecidableEq d] in
/-- **The derivative of RMSNorm with `ε = 0`** at a matrix `h` without a zero row: on every row,
`𝐃N(h) u = u/ρ − ⟨h, u⟩ h/(d ρ³)` with `ρ = ‖h‖/√d` (the formula of the case `ε > 0` with
`ε = 0`). -/
theorem fderiv_rmsNorm_zero_apply (h U : Matrix T d ℝ) (hh : ∀ t, h t ≠ 0) :
    fderiv ℝ (rmsNorm 0 : Matrix T d ℝ → Matrix T d ℝ) h U
      = Matrix.of fun t =>
          (Real.sqrt ((h t ⬝ᵥ h t) / (Fintype.card d : ℝ)))⁻¹ • U t
            - ((h t ⬝ᵥ U t) / (Fintype.card d : ℝ)
                * (Real.sqrt ((h t ⬝ᵥ h t) / (Fintype.card d : ℝ)))⁻¹ ^ 3) • h t := by
  -- the line `τ ↦ h + τ U` passes through `h` with velocity `U`
  have hline : HasDerivAt (fun τ : ℝ => h + τ • U) U 0 := by
    have h1 := ((hasDerivAt_id (0 : ℝ)).smul_const U).const_add h
    rw [one_smul] at h1
    exact h1
  have h0 : h = h + (0 : ℝ) • U := by rw [zero_smul, add_zero]
  -- the chain rule: `τ ↦ N(h + τ U)` has the derivative `𝐃N(h) U` at `0`
  have hF := (analyticAt_rmsNorm_zero h hh).differentiableAt.hasFDerivAt.comp_hasDerivAt_of_eq
    (0 : ℝ) hline h0
  -- the same derivative, entry by entry: entry `(t, i)` is `q(τ)^{-1/2} (h_{ti} + τ U_{ti})`
  refine hF.unique (hasDerivAt_matrix_sz fun t i => ?_)
  have hpos := dotProduct_self_div_pos_sz (hh t)
  -- `‖h_t + τ U_t‖² = ‖h_t‖² + 2 τ ⟨h_t, U_t⟩ + τ² ‖U_t‖²` has the derivative `2 ⟨h_t, U_t⟩` at `0`
  have hdot : HasDerivAt (fun τ : ℝ => (h t + τ • U t) ⬝ᵥ (h t + τ • U t))
      (2 * (h t ⬝ᵥ U t)) 0 := by
    have e : (fun τ : ℝ => (h t + τ • U t) ⬝ᵥ (h t + τ • U t))
        = fun τ => h t ⬝ᵥ h t + τ * (2 * (h t ⬝ᵥ U t)) + τ * τ * (U t ⬝ᵥ U t) := by
      funext τ
      simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul,
        dotProduct_comm (U t) (h t)]
      ring
    rw [e]
    exact hasDerivAt_quad _ _ _
  -- `q(τ) = ‖h_t + τ U_t‖²/d`, then `q^{-1/2}`, then the product with `h_{ti} + τ U_{ti}`
  have hq := hdot.div_const (Fintype.card d : ℝ)
  have hs : 0 < Real.sqrt ((h t ⬝ᵥ h t) / (Fintype.card d : ℝ)) := Real.sqrt_pos.2 hpos
  have hsq := hq.sqrt (by simp only [zero_smul, add_zero]; exact hpos.ne')
  have hinv := hsq.inv (by simp only [zero_smul, add_zero]; exact hs.ne')
  have hent : HasDerivAt (fun τ : ℝ => h t i + τ * U t i) (U t i) 0 := by
    have h1 := ((hasDerivAt_id (0 : ℝ)).mul_const (U t i)).const_add (h t i)
    rw [one_mul] at h1
    exact h1
  show HasDerivAt (fun τ : ℝ => (Real.sqrt ((h t + τ • U t) ⬝ᵥ (h t + τ • U t)
      / (Fintype.card d : ℝ) + 0))⁻¹ * (h t i + τ * U t i))
    ((Real.sqrt ((h t ⬝ᵥ h t) / (Fintype.card d : ℝ)))⁻¹ * U t i
      - ((h t ⬝ᵥ U t) / (Fintype.card d : ℝ)
        * (Real.sqrt ((h t ⬝ᵥ h t) / (Fintype.card d : ℝ)))⁻¹ ^ 3) * h t i) 0
  simp only [add_zero]
  refine (hinv.mul hent).congr_deriv ?_
  simp only [Pi.inv_apply, zero_smul, add_zero, zero_mul]
  ring

omit [DecidableEq d] in
/-- **Equation (15) of the dimension paper for the normalization:** RMSNorm with `ε = 0` does not
change along `h`: `𝐃N(h) h = 0` at every matrix `h` without a zero row. -/
theorem fderiv_rmsNorm_zero_self (h : Matrix T d ℝ) (hh : ∀ t, h t ≠ 0) :
    fderiv ℝ (rmsNorm 0 : Matrix T d ℝ → Matrix T d ℝ) h h = 0 := by
  rw [fderiv_rmsNorm_zero_apply h h hh]
  ext t i
  -- with `ρ = √q`, `q = ‖h_t‖²/d`: `ρ⁻¹ - q ρ⁻³ = 0` because `q = ρ²`
  have hpos := dotProduct_self_div_pos_sz (hh t)
  have hs : 0 < Real.sqrt ((h t ⬝ᵥ h t) / (Fintype.card d : ℝ)) := Real.sqrt_pos.2 hpos
  have hs2 : Real.sqrt ((h t ⬝ᵥ h t) / (Fintype.card d : ℝ)) ^ 2
      = (h t ⬝ᵥ h t) / (Fintype.card d : ℝ) := Real.sq_sqrt hpos.le
  show (Real.sqrt ((h t ⬝ᵥ h t) / (Fintype.card d : ℝ)))⁻¹ * h t i
      - ((h t ⬝ᵥ h t) / (Fintype.card d : ℝ)
        * (Real.sqrt ((h t ⬝ᵥ h t) / (Fintype.card d : ℝ)))⁻¹ ^ 3) * h t i = 0
  generalize Real.sqrt ((h t ⬝ᵥ h t) / (Fintype.card d : ℝ)) = ρ at hs hs2 ⊢
  rw [← hs2]
  have hne := hs.ne'
  field_simp
  ring

variable (A : Arch T d L) (θ : Params A dIn dOut)

/-! ### The identity (16) and the claim in the case (0) -/

/-- The identity (16) of the paper for `k`, `Z` and `η` in the case (0):
`𝐃𝓑_{>k}(h) (h Z) + 𝐃_θ 𝓑_{>k}(h) η = 0` for all `h` without a zero row. -/
def SuffixFlatZero (k : Fin (L + 1)) (Z : Matrix d d ℝ) (η : Params A dIn dOut) : Prop :=
  ∀ h : Matrix T d ℝ, (∀ t, h t ≠ 0) →
    fderiv ℝ (fun h' : Matrix T d ℝ => suffix A 0 θ k h') h (h * Z)
      + fderiv ℝ (fun θ' : Params A dIn dOut => suffix A 0 θ' k h) θ η = 0

/-- **Claim `(D_k)` in the case (0)** (equation (18)), for blocks without symmetries inside: every
`Z` and `η` that satisfy the identity (16) for `k` come from the symmetries at the hidden states
`h_k, …, h_L`: `Z = Y_k + β_k I` with antisymmetric `Y_k, …, Y_L` and numbers `β_k, …, β_L`, the
reads move by `−Y_{ℓ−1} W_read^ℓ`, the writes by `W_write^ℓ (Y_ℓ + β_ℓ I)` and `D` by `−Y_L D`. -/
def ClaimZero (k : Fin (L + 1)) : Prop :=
  ∀ (Z : Matrix d d ℝ) (η : Params A dIn dOut), SuffixFlatZero A θ k Z η →
    ∃ (Y : Fin (L + 1) → Matrix d d ℝ) (β : Fin (L + 1) → ℝ),
      (∀ ℓ, k ≤ ℓ → Y ℓ ∈ antisymmetric d) ∧ Z = Y k + β k • (1 : Matrix d d ℝ) ∧
      (∀ ℓ : Fin L, k ≤ ℓ.castSucc →
        η.read ℓ = -(Y ℓ.castSucc * θ.read ℓ) ∧
        η.write ℓ = θ.write ℓ * (Y ℓ.succ + β ℓ.succ • (1 : Matrix d d ℝ))) ∧
      η.D = -(Y (Fin.last L) * θ.D)

/-- Helper: `y ↦ y M`, as a continuous linear map. -/
private noncomputable def mulRightCLM_sz {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
    (M : Matrix n p ℝ) : Matrix m n ℝ →L[ℝ] Matrix m p ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun y => y * M
      map_add' := fun a b => Matrix.add_mul a b M
      map_smul' := fun c a => Matrix.smul_mul c a M }

/-- Helper: for `χ = N` (RMSNorm with `ε = 0`), the derivative of `h ↦ 𝓑_{>L}(h) = N(h) D` at a
matrix `h` without a zero row, along `v`, is `(𝐃N(h) v) D`. -/
private theorem fderiv_suffix_last_zero_sz (hχ : A.χ = rmsNorm 0) (h v : Matrix T d ℝ)
    (hh : ∀ t, h t ≠ 0) :
    fderiv ℝ (fun h' : Matrix T d ℝ => suffix A 0 θ (Fin.last L) h') h v
      = fderiv ℝ (rmsNorm 0 : Matrix T d ℝ → Matrix T d ℝ) h v * θ.D := by
  simp only [suffix_last, hχ]
  -- `h ↦ N(h) D` is `y ↦ y D` after `N`, which is differentiable at `h`
  have hc := (mulRightCLM_sz (m := T) θ.D).hasFDerivAt.comp h
    (analyticAt_rmsNorm_zero h hh).differentiableAt.hasFDerivAt
  exact DFunLike.congr_fun hc.fderiv v

/-- **Lemma D.5 of the dimension paper (the readout), the case (0):** if `D` has rank `d ≥ 2`,
then `(D_L)` holds under pre-RMSNorm with `ε = 0`. -/
theorem claimZero_last [Nonempty T] (hχ : A.χ = rmsNorm 0) (hD : θ.D.rank = Fintype.card d)
    (hd : 2 ≤ Fintype.card d) : ClaimZero A θ (Fin.last L) := by
  intro Z η hZ
  obtain ⟨t₀⟩ := ‹Nonempty T›
  obtain ⟨i₀⟩ : Nonempty d := Fintype.card_pos_iff.1 (by omega)
  -- `D R = 1` (`D` has rank `d`)
  obtain ⟨R, hR⟩ : ∃ R : Matrix dOut d ℝ, θ.D * R = 1 :=
    Matrix.mulVec_surjective_iff_exists_right_inverse.1
      (Matrix.mulVec_surjective_iff_rank_eq_card.2 hD)
  -- (16) at the hidden state all of whose rows are `u ≠ 0`, on row `t₀`, multiplied by
  -- `d ρ³` (`ρ = ‖u‖/√d`): `‖u‖² (u Z D + u η_D) = ⟨u, u Z⟩ u D`, also for `u = 0`
  have hrow : ∀ u : d → ℝ, (u ⬝ᵥ u) • ((u ᵥ* Z) ᵥ* θ.D + u ᵥ* η.D)
      = (u ⬝ᵥ (u ᵥ* Z)) • (u ᵥ* θ.D) := by
    intro u
    by_cases hu : u = 0
    · subst hu
      simp only [zero_dotProduct, zero_smul]
    have hrows : ∀ t, (Matrix.of fun _ : T => u) t ≠ 0 := fun _ => hu
    have e := hZ (Matrix.of fun _ : T => u) hrows
    rw [fderiv_suffix_last_zero_sz A θ hχ _ _ hrows, fderiv_params_suffix_last_eq_mul A θ, hχ,
      fderiv_rmsNorm_zero_apply _ _ hrows] at e
    -- row `t₀` of `(𝐃N(h)(h Z)) D + N(h) η_D = 0`
    have e' : ((Real.sqrt ((u ⬝ᵥ u) / (Fintype.card d : ℝ)))⁻¹ • (u ᵥ* Z)
        - ((u ⬝ᵥ (u ᵥ* Z)) / (Fintype.card d : ℝ)
            * (Real.sqrt ((u ⬝ᵥ u) / (Fintype.card d : ℝ)))⁻¹ ^ 3) • u) ᵥ* θ.D
        + ((Real.sqrt ((u ⬝ᵥ u) / (Fintype.card d : ℝ) + 0))⁻¹ • u) ᵥ* η.D = 0 :=
      congrFun e t₀
    rw [add_zero] at e'
    simp only [Matrix.sub_vecMul, Matrix.smul_vecMul] at e'
    -- `ρ > 0` and `‖u‖² = d ρ²`
    have hpos := dotProduct_self_div_pos_sz hu
    have hc : (Fintype.card d : ℝ) ≠ 0 := fun h0 => by
      rw [h0, div_zero] at hpos
      exact lt_irrefl _ hpos
    have hs := Real.sqrt_pos.2 hpos
    have hs2 : Real.sqrt ((u ⬝ᵥ u) / (Fintype.card d : ℝ)) ^ 2
        = (u ⬝ᵥ u) / (Fintype.card d : ℝ) := Real.sq_sqrt hpos.le
    have hN : u ⬝ᵥ u
        = (Fintype.card d : ℝ) * Real.sqrt ((u ⬝ᵥ u) / (Fintype.card d : ℝ)) ^ 2 := by
      rw [hs2]
      field_simp
    generalize Real.sqrt ((u ⬝ᵥ u) / (Fintype.card d : ℝ)) = ρ at hs hN e'
    have hρ := hs.ne'
    rw [hN]
    -- multiply the row by `d ρ³`
    have e2 := congrArg (fun w => ((Fintype.card d : ℝ) * ρ ^ 3) • w) e'
    simp only [smul_add, smul_sub, smul_smul, smul_zero] at e2
    have k1 : (Fintype.card d : ℝ) * ρ ^ 3 * ρ⁻¹ = (Fintype.card d : ℝ) * ρ ^ 2 := by
      field_simp
    have k2 : (Fintype.card d : ℝ) * ρ ^ 3
        * ((u ⬝ᵥ (u ᵥ* Z)) / (Fintype.card d : ℝ) * ρ⁻¹ ^ 3) = u ⬝ᵥ (u ᵥ* Z) := by
      field_simp
    rw [k1, k2] at e2
    linear_combination (norm := module) e2
  -- the same identity for the rows of `M = Z D + η_D`
  have hrowM : ∀ u : d → ℝ, (u ⬝ᵥ u) • (u ᵥ* (Z * θ.D + η.D))
      = (u ⬝ᵥ (u ᵥ* Z)) • (u ᵥ* θ.D) := by
    intro u
    rw [Matrix.vecMul_add, ← Matrix.vecMul_vecMul]
    exact hrow u
  -- two different rows of `D` are linearly independent (`D R = 1`)
  have hind : ∀ i j : d, i ≠ j → ∀ a b : ℝ, a • θ.D i + b • θ.D j = 0 → a = 0 ∧ b = 0 := by
    intro i j hij a b hab
    have hw : (a • Pi.single i 1 + b • Pi.single j 1 : d → ℝ) ᵥ* θ.D = 0 := by
      rw [Matrix.add_vecMul, Matrix.smul_vecMul, Matrix.smul_vecMul, Matrix.single_one_vecMul,
        Matrix.single_one_vecMul]
      exact hab
    have hw' := congrArg (· ᵥ* R) hw
    simp only [Matrix.vecMul_vecMul, hR, Matrix.vecMul_one, Matrix.zero_vecMul] at hw'
    have ha := congrFun hw' i
    have hb := congrFun hw' j
    simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, Pi.single_eq_of_ne hij,
      Pi.single_eq_of_ne (Ne.symm hij), smul_eq_mul, mul_one, mul_zero, add_zero, zero_add,
      Pi.zero_apply] at ha hb
    exact ⟨ha, hb⟩
  -- the identity at `e_i`: row `i` of `M` is `Z_ii D_i`
  have hdiagM : ∀ i, (Z * θ.D + η.D) i = Z i i • θ.D i := by
    intro i
    have e := hrowM (Pi.single i 1)
    rw [single_one_dotProduct, single_one_dotProduct, Matrix.single_one_vecMul,
      Matrix.single_one_vecMul, Matrix.single_one_vecMul, Pi.single_eq_same, one_smul] at e
    exact e
  -- the identity at `e_i + e_j`, `i ≠ j`: `Z_ii = Z_jj` and `Z_ij + Z_ji = 0`
  have hpair : ∀ i j : d, i ≠ j → Z i i = Z j j ∧ Z i j + Z j i = 0 := by
    intro i j hij
    have e := hrowM (Pi.single i 1 + Pi.single j 1)
    simp only [add_dotProduct, dotProduct_add, Matrix.add_vecMul, single_one_dotProduct,
      Matrix.single_one_vecMul, Matrix.row, Pi.single_eq_same,
      Pi.single_eq_of_ne hij, Pi.single_eq_of_ne (Ne.symm hij), add_zero, zero_add,
      hdiagM i, hdiagM j] at e
    have e3 : (2 * Z i i - (Z i i + Z i j + (Z j i + Z j j))) • θ.D i
        + (2 * Z j j - (Z i i + Z i j + (Z j i + Z j j))) • θ.D j = 0 := by
      linear_combination (norm := module) e
    obtain ⟨h1, h2⟩ := hind i j hij _ _ e3
    constructor <;> linarith
  -- so the diagonal of `Z` is constant, `β`, and `M = β D`
  set β := Z i₀ i₀
  have hdiag : ∀ i, Z i i = β := by
    intro i
    by_cases hi : i = i₀
    · rw [hi]
    · exact (hpair i i₀ hi).1
  have hM : Z * θ.D + η.D = β • θ.D := by
    ext i o
    have e := congrFun (hdiagM i) o
    rw [hdiag i] at e
    exact e
  -- `Y = Z - β I` is antisymmetric
  have hY : (Z - β • (1 : Matrix d d ℝ))ᵀ = -(Z - β • (1 : Matrix d d ℝ)) := by
    ext i j
    simp only [Matrix.transpose_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.neg_apply,
      smul_eq_mul]
    by_cases hij : i = j
    · subst hij
      rw [hdiag i, Matrix.one_apply_eq, mul_one, sub_self, neg_zero]
    · rw [Matrix.one_apply_ne hij, Matrix.one_apply_ne (Ne.symm hij), mul_zero, sub_zero,
        sub_zero]
      linarith [(hpair i j hij).2]
  -- `Z = Y + β I`; no block comes after `L`; `η_D = β D - Z D = -Y D`
  refine ⟨fun _ => Z - β • (1 : Matrix d d ℝ), fun _ => β, fun _ _ => hY,
    (sub_add_cancel Z _).symm, fun ℓ hℓ => absurd hℓ (not_le.2 (Fin.castSucc_lt_last ℓ)), ?_⟩
  show η.D = -((Z - β • (1 : Matrix d d ℝ)) * θ.D)
  rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, neg_sub, ← hM]
  abel

end Skips
