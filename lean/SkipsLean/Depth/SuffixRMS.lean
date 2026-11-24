import SkipsLean.Depth.Suffix
import SkipsLean.Dimension.UpperBoundRMSNorm

/-!
# The claim `(D_k)` under pre-RMSNorm with `ε > 0`

Paper (dimension paper): Appendix D.3 ("The claim, and the reduction to one step"), in the case (+):
`χ = N_ε` with `ε > 0`, the group of the changes of basis is `O(d)`, and its Lie algebra `𝔤` is the
set of the antisymmetric matrices.

The identity (16) is the one of the case (n) (`SuffixFlat`, which is stated for any `χ`). Claim
`(D_k)` now says: if `Z` and `η` satisfy (16) for `k`, then `Z` is antisymmetric, and there are
antisymmetric `Z_k = Z, Z_{k+1}, …, Z_L` with

  `η_read^ℓ = - Z_{ℓ-1} W_read^ℓ`,  `η_write^ℓ = W_write^ℓ Z_ℓ`  (`ℓ = k+1, …, L`),  `η_D = - Z_L D`.

"Regular" is as in the case (n) (`Regular`: (R1), and (R3) for the blocks as maps of their inputs).
Stated here: Lemma D.2, Lemma D.3, Proposition D.4 and Lemma D.5 in the case (+), and that the
network after a hidden state is real-analytic for a real-analytic `χ`.
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise Topology

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable (A : Arch T d L) (θ : Params A dIn dOut) {ε : ℝ}

/-- Helper: `√` is analytic at a positive number, where it agrees with `x ↦ exp (log x / 2)`. -/
private theorem analyticAt_sqrt_of_pos {x : ℝ} (hx : 0 < x) : AnalyticAt ℝ Real.sqrt x := by
  have h : AnalyticAt ℝ (Real.exp ∘ fun y => Real.log y * (1 / 2)) x :=
    ((analyticAt_log hx).mul analyticAt_const).rexp
  refine h.congr ?_
  filter_upwards [lt_mem_nhds hx] with y hy
  show Real.exp (Real.log y * (1 / 2)) = Real.sqrt y
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hy]

omit [DecidableEq d] in
/-- Helper: `‖v‖² / d + ε > 0` for `ε > 0`. -/
private theorem dotProduct_self_div_add_pos (hε : 0 < ε) (v : d → ℝ) :
    0 < (v ⬝ᵥ v) / (Fintype.card d : ℝ) + ε := by
  have : 0 ≤ (v ⬝ᵥ v) / (Fintype.card d : ℝ) :=
    div_nonneg (Finset.sum_nonneg fun j _ => mul_self_nonneg (v j)) (Nat.cast_nonneg _)
  linarith

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (as `analyticOnNhd_matrix_entry` in `Network/Analytic.lean`, not imported here): an
entry of a matrix is a real-analytic (linear) function of the matrix. -/
private theorem analyticOnNhd_entry {m n : Type*} [Fintype m] [Fintype n] (t : m) (i : n) :
    AnalyticOnNhd ℝ (fun M : Matrix m n ℝ => M t i) Set.univ :=
  ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : n => ℝ) i).comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : m => n → ℝ) t)).analyticOnNhd _

omit [DecidableEq d] in
/-- RMSNorm with `ε > 0` is real-analytic. -/
theorem analyticOnNhd_rmsNorm (hε : 0 < ε) :
    AnalyticOnNhd ℝ (rmsNorm ε : Matrix T d ℝ → Matrix T d ℝ) Set.univ := by
  -- entry `(t, i)` is `(√(‖h_t‖²/d + ε))⁻¹ h_{ti}`
  show AnalyticOnNhd ℝ (fun h : Matrix T d ℝ => fun t => fun i =>
    (Real.sqrt ((h t ⬝ᵥ h t) / (Fintype.card d : ℝ) + ε))⁻¹ * h t i) Set.univ
  refine AnalyticOnNhd.pi fun t => AnalyticOnNhd.pi fun i => fun h _ => ?_
  -- the quantity under the root is a polynomial in the entries, and it is at least `ε > 0`
  have hq : AnalyticAt ℝ (fun h : Matrix T d ℝ => (h t ⬝ᵥ h t) / (Fintype.card d : ℝ) + ε) h :=
    (((Finset.analyticOnNhd_fun_sum _ fun j _ =>
      (analyticOnNhd_entry t j).mul (analyticOnNhd_entry t j)) h
        (Set.mem_univ _)).div_const).add analyticAt_const
  have hpos := dotProduct_self_div_add_pos hε (h t)
  -- `√` is analytic at a positive number, and the inverse where it is not zero
  exact (((analyticAt_sqrt_of_pos hpos).comp
    (f := fun h : Matrix T d ℝ => (h t ⬝ᵥ h t) / (Fintype.card d : ℝ) + ε) hq).inv
      (Real.sqrt_pos.2 hpos).ne').mul (analyticOnNhd_entry t i h (Set.mem_univ _))

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- The matrix product of two analytic matrix-valued maps is analytic (matrix multiplication is a
continuous bilinear map). -/
theorem analyticOnNhd_matrix_mul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
    {f : E → Matrix m n ℝ} {g : E → Matrix n p ℝ} {s : Set E}
    (hf : AnalyticOnNhd ℝ f s) (hg : AnalyticOnNhd ℝ g s) :
    AnalyticOnNhd ℝ (fun y => f y * g y) s := by
  -- matrix multiplication as a bilinear map
  let B : Matrix m n ℝ →ₗ[ℝ] Matrix n p ℝ →ₗ[ℝ] Matrix m p ℝ :=
    LinearMap.mk₂ ℝ (fun a b => a * b) Matrix.add_mul (fun c a b => Matrix.smul_mul c a b)
      Matrix.mul_add (fun c a b => Matrix.mul_smul a c b)
  -- the same map with continuous linear maps (all spaces are finite-dimensional)
  let B' : Matrix m n ℝ →L[ℝ] Matrix n p ℝ →L[ℝ] Matrix m p ℝ :=
    LinearMap.toContinuousLinearMap
      ((LinearMap.toContinuousLinearMap :
        (Matrix n p ℝ →ₗ[ℝ] Matrix m p ℝ) ≃ₗ[ℝ] (Matrix n p ℝ →L[ℝ] Matrix m p ℝ)).toLinearMap ∘ₗ B)
  have hB : (fun y => f y * g y) = fun y => B' (f y) (g y) := rfl
  rw [hB]
  exact fun y hy => (B'.analyticAt_bilinear (f y, g y)).comp₂ (hf y hy) (hg y hy)

/-- For a real-analytic `χ` and real-analytic blocks, the network after a hidden state is
real-analytic in the weights and the hidden state together. -/
theorem analyticOnNhd_suffix_prod_of_analytic (hχ : AnalyticOnNhd ℝ A.χ Set.univ)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (k : Fin (L + 1)) :
    AnalyticOnNhd ℝ
      (fun p : Params A dIn dOut × Matrix T d ℝ => suffix A 0 p.1 k p.2) Set.univ := by
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
  -- `(θ, h) ↦ χ(h)` is analytic
  have hχ' : AnalyticOnNhd ℝ (fun p : Params A dIn dOut × Matrix T d ℝ => A.χ p.2) Set.univ :=
    hχ.comp analyticOnNhd_snd (Set.mapsTo_univ _ _)
  induction k using Fin.reverseInduction with
  | last =>
    -- `(θ, h) ↦ χ(h) D`
    simp only [suffix_last]
    exact analyticOnNhd_matrix_mul hχ' hD
  | cast ℓ ih =>
    -- `(θ, h) ↦ 𝓑_{>ℓ}(f_ℓ(χ(h) W_read) W_write)`, with the weights `θ`
    simp only [suffix_castSucc, Pi.zero_apply, Matrix.mul_zero, zero_add]
    have hg : AnalyticOnNhd ℝ (fun p : Params A dIn dOut × Matrix T d ℝ =>
        (p.1, A.f ℓ (A.χ p.2 * p.1.read ℓ) * p.1.write ℓ)) Set.univ :=
      analyticOnNhd_fst.prod (analyticOnNhd_matrix_mul
        ((hf ℓ).comp (analyticOnNhd_matrix_mul hχ' (hr ℓ)) (Set.mapsTo_univ _ _)) (hw ℓ))
    have hc := ih.comp hg (Set.mapsTo_univ _ _)
    exact hc

/-- For a real-analytic `χ` and real-analytic blocks, `𝓑_{>k}` is real-analytic in the hidden
state. -/
theorem analyticOnNhd_suffix_of_analytic (hχ : AnalyticOnNhd ℝ A.χ Set.univ)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (k : Fin (L + 1)) :
    AnalyticOnNhd ℝ (fun h : Matrix T d ℝ => suffix A 0 θ k h) Set.univ := by
  -- compose with `h ↦ (θ, h)`
  have h1 : AnalyticOnNhd ℝ (fun h : Matrix T d ℝ => (θ, h)) Set.univ :=
    analyticOnNhd_const.prod analyticOnNhd_id
  have hc := (analyticOnNhd_suffix_prod_of_analytic A hχ hf k).comp h1 (Set.mapsTo_univ _ _)
  exact hc

/-- **Claim `(D_k)` in the case (+),** for blocks without symmetries inside: every `Z` and `η` that
satisfy the identity (16) for `k` come from changes of basis `Z_k = Z, Z_{k+1}, …, Z_L` at the
hidden states `h_k, …, h_L`, all antisymmetric. -/
def ClaimRMS (k : Fin (L + 1)) : Prop :=
  ∀ (Z : Matrix d d ℝ) (η : Params A dIn dOut), SuffixFlat A θ k Z η →
    ∃ X : Fin (L + 1) → Matrix d d ℝ, X k = Z ∧ (∀ ℓ, k ≤ ℓ → X ℓ ∈ antisymmetric d) ∧
      (∀ ℓ : Fin L, k ≤ ℓ.castSucc →
        η.read ℓ = -(X ℓ.castSucc * θ.read ℓ) ∧ η.write ℓ = θ.write ℓ * X ℓ.succ) ∧
      η.D = -(X (Fin.last L) * θ.D)

/-! ### The derivative of RMSNorm -/

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: with the elementwise norm, the derivative of a matrix-valued function of one real
variable is taken entry by entry. -/
private theorem hasDerivAt_matrix {m n : Type*} [Fintype m] [Fintype n] {f : ℝ → Matrix m n ℝ}
    {f' : Matrix m n ℝ} {x : ℝ} (h : ∀ i j, HasDerivAt (fun τ => f τ i j) (f' i j) x) :
    HasDerivAt f f' x :=
  hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 (h i)

/-- **The derivative of RMSNorm** with `ε > 0`, row by row: with `s_t = √(‖h_t‖²/d + ε)`,
`(𝐃N_ε(h) U)_t = U_t / s_t - (⟨h_t, U_t⟩/d) h_t / s_t³`. -/
theorem fderiv_rmsNorm_apply (hε : 0 < ε) (h U : Matrix T d ℝ) :
    fderiv ℝ (rmsNorm ε : Matrix T d ℝ → Matrix T d ℝ) h U
      = Matrix.of fun t =>
          (Real.sqrt ((h t ⬝ᵥ h t) / (Fintype.card d : ℝ) + ε))⁻¹ • U t
            - ((h t ⬝ᵥ U t) / (Fintype.card d : ℝ)
                * (Real.sqrt ((h t ⬝ᵥ h t) / (Fintype.card d : ℝ) + ε))⁻¹ ^ 3) • h t := by
  -- the line `τ ↦ h + τ U` passes through `h` with velocity `U`
  have hline : HasDerivAt (fun τ : ℝ => h + τ • U) U 0 := by
    have h1 := ((hasDerivAt_id (0 : ℝ)).smul_const U).const_add h
    rw [one_smul] at h1
    exact h1
  have h0 : h = h + (0 : ℝ) • U := by rw [zero_smul, add_zero]
  -- the chain rule: `τ ↦ N_ε(h + τ U)` has the derivative `𝐃N_ε(h) U` at `0`
  have hF := ((differentiable_rmsNorm (T := T) (d := d) hε) h).hasFDerivAt.comp_hasDerivAt_of_eq
    (0 : ℝ) hline h0
  -- the same derivative, entry by entry: entry `(t, i)` is `q(τ)^{-1/2} (h_{ti} + τ U_{ti})`
  refine hF.unique (hasDerivAt_matrix fun t i => ?_)
  have hpos := dotProduct_self_div_add_pos hε (h t)
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
  -- `q(τ) = ‖h_t + τ U_t‖²/d + ε`, then `q^{-1/2}`, then the product with `h_{ti} + τ U_{ti}`
  have hq := (hdot.div_const (Fintype.card d : ℝ)).add_const ε
  have hs : 0 < Real.sqrt ((h t ⬝ᵥ h t) / (Fintype.card d : ℝ) + ε) := Real.sqrt_pos.2 hpos
  have hsq := hq.sqrt (by simp only [zero_smul, add_zero]; exact hpos.ne')
  have hinv := hsq.inv (by simp only [zero_smul, add_zero]; exact hs.ne')
  have hent : HasDerivAt (fun τ : ℝ => h t i + τ * U t i) (U t i) 0 := by
    have h1 := ((hasDerivAt_id (0 : ℝ)).mul_const (U t i)).const_add (h t i)
    rw [one_mul] at h1
    exact h1
  show HasDerivAt (fun τ : ℝ => (Real.sqrt ((h t + τ • U t) ⬝ᵥ (h t + τ • U t)
      / (Fintype.card d : ℝ) + ε))⁻¹ * (h t i + τ * U t i))
    ((Real.sqrt ((h t ⬝ᵥ h t) / (Fintype.card d : ℝ) + ε))⁻¹ * U t i
      - ((h t ⬝ᵥ U t) / (Fintype.card d : ℝ)
        * (Real.sqrt ((h t ⬝ᵥ h t) / (Fintype.card d : ℝ) + ε))⁻¹ ^ 3) * h t i) 0
  refine (hinv.mul hent).congr_deriv ?_
  simp only [Pi.inv_apply, zero_smul, add_zero, zero_mul]
  ring

/-! ### Derivatives of the network after a hidden state, for any `χ` -/

/-- Helper: `y ↦ y M`, as a linear map. -/
private def mulRightLin {m n p : Type*} [Fintype n] (M : Matrix n p ℝ) :
    Matrix m n ℝ →ₗ[ℝ] Matrix m p ℝ where
  toFun y := y * M
  map_add' a b := Matrix.add_mul a b M
  map_smul' c a := Matrix.smul_mul c a M

/-- Helper: `y ↦ M y`, as a linear map. -/
private def mulLeftLin {m n p : Type*} [Fintype n] (M : Matrix m n ℝ) :
    Matrix n p ℝ →ₗ[ℝ] Matrix m p ℝ where
  toFun y := M * y
  map_add' a b := Matrix.mul_add M a b
  map_smul' c a := Matrix.mul_smul M c a

/-- Helper: the derivative of a linear map on a finite-dimensional space is the map itself. -/
private theorem fderiv_linMap {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (l : E →ₗ[ℝ] F)
    (x v : E) : fderiv ℝ (fun y => l y) x v = l v := by
  have h := (LinearMap.toContinuousLinearMap l).fderiv (x := x)
  rw [LinearMap.coe_toContinuousLinearMap'] at h
  change fderiv ℝ (⇑l) x v = l v
  rw [h]
  rfl

/-- Helper: `y ↦ y M`, as a continuous linear map. -/
private noncomputable def mulRightCLM {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
    (M : Matrix n p ℝ) : Matrix m n ℝ →L[ℝ] Matrix m p ℝ :=
  LinearMap.toContinuousLinearMap (mulRightLin M)

/-- For a differentiable `χ`, the derivative of `h ↦ 𝓑_{>L}(h) = χ(h) D` along `v` is
`(𝐃χ(h) v) D`. -/
theorem fderiv_suffix_last_of_differentiable (hχ : Differentiable ℝ A.χ) (h v : Matrix T d ℝ) :
    fderiv ℝ (fun h' : Matrix T d ℝ => suffix A 0 θ (Fin.last L) h') h v
      = fderiv ℝ A.χ h v * θ.D := by
  simp only [suffix_last]
  -- `h ↦ χ(h) D` is `y ↦ y D` after `χ`
  have hc := (mulRightCLM (m := T) θ.D).hasFDerivAt.comp h (hχ h).hasFDerivAt
  exact DFunLike.congr_fun hc.fderiv v

/-- For any `χ`, the derivative of `θ ↦ 𝓑_{>L}(h) = χ(h) D` along `η` is `χ(h) η_D`. -/
theorem fderiv_params_suffix_last_eq_mul (h : Matrix T d ℝ) (η : Params A dIn dOut) :
    fderiv ℝ (fun θ' : Params A dIn dOut => suffix A 0 θ' (Fin.last L) h) θ η = A.χ h * η.D := by
  simp only [suffix_last]
  exact fderiv_linMap
    ((mulLeftLin (A.χ h)).comp (Params.linD (A := A) (dIn := dIn) (dOut := dOut))) θ η

/-! ### Lemma D.2 -/

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: a matrix of rank its number of rows has a right inverse. -/
private theorem exists_right_inverse_of_rank {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] (M : Matrix m n ℝ) (hM : M.rank = Fintype.card m) :
    ∃ B : Matrix n m ℝ, M * B = 1 :=
  Matrix.mulVec_surjective_iff_exists_right_inverse.1
    (Matrix.mulVec_surjective_iff_rank_eq_card.2 hM)

/-- **Lemma D.2, case (+):** for a regular `θ` and analytic blocks there is, for every `k`, an open
dense set of hidden states `h` at which the derivative of `𝓑_{>k}` is injective. (`N_ε` is a
diffeomorphism of the rows onto the ball `‖n‖² < d`.) -/
theorem exists_open_dense_injective_fderiv_suffix_rmsNorm (hε : 0 < ε) (hχ : A.χ = rmsNorm ε)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (hθ : Regular A θ) (k : Fin (L + 1)) :
    ∃ U : Set (Matrix T d ℝ), IsOpen U ∧ Dense U ∧
      ∀ h ∈ U, Function.Injective (fderiv ℝ (fun h' : Matrix T d ℝ => suffix A 0 θ k h') h) := by
  sorry

/-- **Lemma D.3, case (+) (a direction at a write).** Let `θ` be regular, and let `M` be a matrix
with `d` columns and rank `d`. If `𝐃𝓑_{>k}(w M) (w η_M) + 𝐃_θ 𝓑_{>k}(w M) η = 0` for all `w`, then
`η_M = M Z` for a `d × d` matrix `Z`, and the identity (16) holds for `k`, `Z` and `η`. -/
theorem suffixFlat_of_flat_at_write_rmsNorm [Nonempty T] (hε : 0 < ε) (hχ : A.χ = rmsNorm ε)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (hθ : Regular A θ) (k : Fin (L + 1))
    {m : Type*} [Fintype m] (M : Matrix m d ℝ) (hM : M.rank = Fintype.card d)
    (ηM : Matrix m d ℝ) (η : Params A dIn dOut)
    (h : ∀ w : Matrix T m ℝ,
      fderiv ℝ (fun h' : Matrix T d ℝ => suffix A 0 θ k h') (w * M) (w * ηM)
        + fderiv ℝ (fun θ' : Params A dIn dOut => suffix A 0 θ' k (w * M)) θ η = 0) :
    ∃ Z : Matrix d d ℝ, ηM = M * Z ∧ SuffixFlat A θ k Z η := by
  sorry

/-- **Lemma D.5, case (+):** if `D` has rank `d`, then `(D_L)` holds. (The identity (16) for `L` is
`(n Z - ⟨n Z, n⟩ n / d) D + n η_D = 0` for the rows `n` of the ball; its part of degree `1` gives
`η_D = - Z D`, and its part of degree `3` gives that `Z` is antisymmetric.) -/
theorem claimRMS_last [Nonempty T] (hε : 0 < ε) (hχ : A.χ = rmsNorm ε)
    (hD : θ.D.rank = Fintype.card d) : ClaimRMS A θ (Fin.last L) := by
  intro Z η hZ
  have hχd : Differentiable ℝ A.χ := by rw [hχ]; exact differentiable_rmsNorm hε
  obtain ⟨t₀⟩ := ‹Nonempty T›
  -- `D R = 1` (`D` has rank `d`)
  obtain ⟨R, hR⟩ := exists_right_inverse_of_rank θ.D hD
  -- (16) at the hidden state whose rows are all `a v`, on row `t₀`: with
  -- `c = a / √(a² ‖v‖²/d + ε)` (so that `N_ε(a v) = c v`), `c (v Z D + v η_D) - c³ (⟨v, v Z⟩/d) v D = 0`
  have hrow : ∀ (a : ℝ) (v : d → ℝ),
      (a * (Real.sqrt (a * a * (v ⬝ᵥ v) / (Fintype.card d : ℝ) + ε))⁻¹) •
          ((v ᵥ* Z) ᵥ* θ.D + v ᵥ* η.D)
        - ((a * (Real.sqrt (a * a * (v ⬝ᵥ v) / (Fintype.card d : ℝ) + ε))⁻¹) ^ 3
            * ((v ⬝ᵥ (v ᵥ* Z)) / (Fintype.card d : ℝ))) • (v ᵥ* θ.D) = 0 := by
    intro a v
    have e := hZ (Matrix.of fun _ => a • v)
    rw [fderiv_suffix_last_of_differentiable A θ hχd, fderiv_params_suffix_last_eq_mul A θ, hχ,
      fderiv_rmsNorm_apply hε] at e
    -- row `t₀` of `(𝐃N_ε(h)(h Z)) D + N_ε(h) η_D = 0`
    have e' : ((Real.sqrt (((a • v) ⬝ᵥ (a • v)) / (Fintype.card d : ℝ) + ε))⁻¹
          • ((a • v) ᵥ* Z)
        - (((a • v) ⬝ᵥ ((a • v) ᵥ* Z)) / (Fintype.card d : ℝ)
            * (Real.sqrt (((a • v) ⬝ᵥ (a • v)) / (Fintype.card d : ℝ) + ε))⁻¹ ^ 3) • (a • v))
          ᵥ* θ.D
        + ((Real.sqrt (((a • v) ⬝ᵥ (a • v)) / (Fintype.card d : ℝ) + ε))⁻¹ • (a • v)) ᵥ* η.D
        = 0 := congrFun e t₀
    have hvv : (a • v) ⬝ᵥ (a • v) = a * a * (v ⬝ᵥ v) := by
      simp only [smul_dotProduct, dotProduct_smul, smul_eq_mul]
      ring
    have hvZ : (a • v) ⬝ᵥ ((a • v) ᵥ* Z) = a * a * (v ⬝ᵥ (v ᵥ* Z)) := by
      simp only [Matrix.smul_vecMul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
      ring
    rw [hvv, hvZ] at e'
    generalize (Real.sqrt (a * a * (v ⬝ᵥ v) / (Fintype.card d : ℝ) + ε))⁻¹ = u at e' ⊢
    simp only [Matrix.sub_vecMul, Matrix.smul_vecMul] at e'
    linear_combination (norm := module) e'
  -- two values of `c²` differ (`1 / (y + ε) ≠ 4 / (4 y + ε)` as `ε ≠ 0`), so both parts vanish:
  -- `v (Z D + η_D) = 0` and `(⟨v, v Z⟩/d) v D = 0`
  have hsplit : ∀ v : d → ℝ, (v ᵥ* Z) ᵥ* θ.D + v ᵥ* η.D = 0 ∧
      ((v ⬝ᵥ (v ᵥ* Z)) / (Fintype.card d : ℝ)) • (v ᵥ* θ.D) = 0 := by
    intro v
    have hp : 0 ≤ v ⬝ᵥ v := Finset.sum_nonneg fun j _ => mul_self_nonneg (v j)
    -- for `a ≠ 0`, `c ≠ 0`, so `v Z D + v η_D = c² (⟨v, v Z⟩/d) v D`
    have key : ∀ a : ℝ, a ≠ 0 →
        (v ᵥ* Z) ᵥ* θ.D + v ᵥ* η.D
          = ((a * (Real.sqrt (a * a * (v ⬝ᵥ v) / (Fintype.card d : ℝ) + ε))⁻¹) ^ 2) •
              (((v ⬝ᵥ (v ᵥ* Z)) / (Fintype.card d : ℝ)) • (v ᵥ* θ.D)) := by
      intro a ha
      have hq : 0 ≤ a * a * (v ⬝ᵥ v) / (Fintype.card d : ℝ) :=
        div_nonneg (mul_nonneg (mul_self_nonneg a) hp) (Nat.cast_nonneg _)
      have hs : 0 < Real.sqrt (a * a * (v ⬝ᵥ v) / (Fintype.card d : ℝ) + ε) :=
        Real.sqrt_pos.2 (by linarith)
      have hc : a * (Real.sqrt (a * a * (v ⬝ᵥ v) / (Fintype.card d : ℝ) + ε))⁻¹ ≠ 0 :=
        mul_ne_zero ha (inv_ne_zero hs.ne')
      have e := hrow a v
      generalize a * (Real.sqrt (a * a * (v ⬝ᵥ v) / (Fintype.card d : ℝ) + ε))⁻¹ = c at hc e ⊢
      have e2 : c • ((v ᵥ* Z) ᵥ* θ.D + v ᵥ* η.D
          - c ^ 2 • (((v ⬝ᵥ (v ᵥ* Z)) / (Fintype.card d : ℝ)) • (v ᵥ* θ.D))) = 0 := by
        linear_combination (norm := module) e
      exact sub_eq_zero.1 ((smul_eq_zero.1 e2).resolve_left hc)
    -- `c² = 1 / (y + ε)` for `a = 1` and `c² = 4 / (4 y + ε)` for `a = 2`, with `y = ‖v‖²/d`
    have hy : 0 ≤ v ⬝ᵥ v / (Fintype.card d : ℝ) := div_nonneg hp (Nat.cast_nonneg _)
    have k1 := key 1 one_ne_zero
    have k2 := key 2 two_ne_zero
    rw [show (1 : ℝ) * 1 * (v ⬝ᵥ v) / (Fintype.card d : ℝ) + ε
      = v ⬝ᵥ v / (Fintype.card d : ℝ) + ε by ring] at k1
    rw [show (2 : ℝ) * 2 * (v ⬝ᵥ v) / (Fintype.card d : ℝ) + ε
      = 4 * (v ⬝ᵥ v / (Fintype.card d : ℝ)) + ε by ring] at k2
    have hne : ∀ y : ℝ, 0 ≤ y →
        (1 * (Real.sqrt (y + ε))⁻¹) ^ 2 - (2 * (Real.sqrt (4 * y + ε))⁻¹) ^ 2 ≠ 0 := by
      intro y hy
      have h1 : 0 < y + ε := by linarith
      have h2 : 0 < 4 * y + ε := by linarith
      have h1' := h1.ne'
      have h2' := h2.ne'
      rw [mul_pow, mul_pow, inv_pow, inv_pow, Real.sq_sqrt h1.le, Real.sq_sqrt h2.le]
      have e : (1 : ℝ) ^ 2 * (y + ε)⁻¹ - 2 ^ 2 * (4 * y + ε)⁻¹
          = -(3 * ε) / ((y + ε) * (4 * y + ε)) := by
        field_simp
        ring
      rw [e]
      exact div_ne_zero (by linarith) (mul_pos h1 h2).ne'
    have hQ : ((v ⬝ᵥ (v ᵥ* Z)) / (Fintype.card d : ℝ)) • (v ᵥ* θ.D) = 0 := by
      have e3 : ((1 * (Real.sqrt (v ⬝ᵥ v / (Fintype.card d : ℝ) + ε))⁻¹) ^ 2
          - (2 * (Real.sqrt (4 * (v ⬝ᵥ v / (Fintype.card d : ℝ)) + ε))⁻¹) ^ 2)
          • (((v ⬝ᵥ (v ᵥ* Z)) / (Fintype.card d : ℝ)) • (v ᵥ* θ.D)) = 0 := by
        rw [sub_smul, ← k1, ← k2, sub_self]
      exact (smul_eq_zero.1 e3).resolve_left (hne _ hy)
    exact ⟨by rw [k1, hQ, smul_zero], hQ⟩
  -- the part of degree `1`: `v (Z D + η_D) = 0` for every row `v`, so `η_D = -Z D`
  have hDZ : Z * θ.D + η.D = 0 := by
    ext i o
    have e := (hsplit (Pi.single i 1)).1
    rw [Matrix.vecMul_vecMul, ← Matrix.vecMul_add, Matrix.single_one_vecMul,
      Matrix.row_apply'] at e
    exact congrFun e o
  -- the part of degree `3`: `⟨v, v Z⟩ = 0` for every row `v` (`v D ≠ 0` for `v ≠ 0`)
  have hquad : ∀ v : d → ℝ, v ⬝ᵥ (v ᵥ* Z) = 0 := by
    intro v
    rcases smul_eq_zero.1 (hsplit v).2 with h1 | h1
    · rcases div_eq_zero_iff.1 h1 with h2 | h2
      · exact h2
      · -- `d` is empty
        have : IsEmpty d := Fintype.card_eq_zero_iff.1 (by exact_mod_cast h2)
        rw [dotProduct, Finset.univ_eq_empty, Finset.sum_empty]
    · -- `v D = 0` gives `v = v D R = 0`
      have hv : v = 0 := by
        have h2 := congrArg (· ᵥ* R) h1
        simp only [Matrix.vecMul_vecMul, hR, Matrix.vecMul_one, Matrix.zero_vecMul] at h2
        exact h2
      rw [hv, zero_dotProduct]
  -- so `Z` is antisymmetric (polarization: `v = e_i + e_j`)
  have hZa : Zᵀ = -Z := by
    ext i j
    have e := hquad (Pi.single i 1 + Pi.single j 1)
    rw [Matrix.add_vecMul, dotProduct_add, add_dotProduct, add_dotProduct, hquad, hquad, zero_add,
      add_zero, Matrix.single_one_vecMul, Matrix.single_one_vecMul, single_one_dotProduct,
      single_one_dotProduct, Matrix.row_apply, Matrix.row_apply] at e
    rw [Matrix.transpose_apply, Matrix.neg_apply]
    linarith
  -- `X_L = Z`; no block comes after `L`
  refine ⟨fun _ => Z, rfl, fun _ _ => hZa,
    fun ℓ hℓ => absurd hℓ (not_le.2 (Fin.castSucc_lt_last ℓ)), ?_⟩
  show η.D = -(Z * θ.D)
  rw [eq_neg_iff_add_eq_zero, add_comm]
  exact hDZ

/-- **Proposition D.4, case (+), first part:** if `θ` is regular and `(D_0)` holds at `θ`, every
flat direction is the direction of antisymmetric changes of basis at the hidden states. -/
theorem flat_le_range_cobDir_of_claimRMS [Nonempty T] (hε : 0 < ε) (hχ : A.χ = rmsNorm ε)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (hθ : Regular A θ) (h0 : ClaimRMS A θ 0)
    (η : Params A dIn dOut) (hη : η ∈ flat A 0 θ) :
    ∃ X : Fin (L + 1) → Matrix d d ℝ, (∀ ℓ, X ℓ ∈ antisymmetric d) ∧ η = cobDir θ X := by
  sorry

/-- **Proposition D.4, case (+):** if `θ` is regular and `(D_0)` holds at `θ`, the functional
dimension at `θ` is `P - (L + 1) d (d - 1) / 2`. -/
theorem funDim_of_claimRMS [Nonempty T] (hε : 0 < ε) (hχ : A.χ = rmsNorm ε)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (hθ : Regular A θ) (h0 : ClaimRMS A θ 0) :
    funDim A 0 θ + (L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2)
      = Module.finrank ℝ (Params A dIn dOut) := by
  sorry

end Skips
