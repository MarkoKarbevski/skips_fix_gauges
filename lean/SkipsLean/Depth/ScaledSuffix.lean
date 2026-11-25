import SkipsLean.Depth.SuffixRMS
import SkipsLean.Depth.StepTanhRMS

/-!
# The rest of the network on a ray, under pre-RMSNorm

Paper (dimension): Lemma D.10 (The rest of the network on a ray). "In the case (+), let `k ≤ L`,
let `h° ≠ 0` be a row, let `v_1, …, v_i` be rows, and let `η` be a direction of the weights of the
blocks `k+1, …, L` and of `D`. With `𝐃^i` the derivative of order `i` in `h`, the maps
`t ↦ t^i 𝐃^i 𝓑_{>k}(t h°)(v_1, …, v_i)` and `t ↦ t^i 𝐃^i (𝐃_θ 𝓑_{>k}(·) η)(t h°)(v_1, …, v_i)` are
real-analytic functions of `1/t` near `1/t = 0`, so they are meromorphic at infinity. Moreover,
there are numbers `ϱ, t₀ > 0` such that the maps `u ↦ 𝓑_{>k}(t (h° + u))` and
`u ↦ 𝐃_θ 𝓑_{>k}(t (h° + u)) η` extend to holomorphic maps on the rows `u ∈ ℂ^{1×d_model}` with
`|u_j| ≤ ϱ` for all `j`, which are bounded uniformly in `t ≥ t₀`." Its proof: "`𝓑_{>k} = 𝓑^♯ ∘ N_ε`
[…] For `t > 0` and a row `u`, `N_ε(t (h° + u)) = (h° + u) / √(‖h° + u‖²/d_model + ε t^{−2})`, and
the right side is a real-analytic function of `(1/t, u)` near `(0, 0)`, also at `1/t = 0`, because
`h° ≠ 0`. So `𝓑_{>k}(t (h° + u))` is a real-analytic function of `(1/t, u)` near `(0, 0)`."

Stated here, for a real variable: the network after the normalization of `h_k` (`suffixPost`, the
paper's `𝓑^♯`), and the map `(s, h) ↦ 𝓑^♯(N_{ε s^{2m}}(h))` (`scaledSuffix`), which is
`𝓑_{>k}(t^m h)` at `s = 1/t` for every `t > 0` (the proof of Lemma D.12 uses the lemma "with `t^m`
in the place of `t`", `m = 2` for gated blocks and `m = 1` for GELU blocks). This map is
real-analytic in `(θ, s, h)` at every `s`, also at `s = 0`, at hidden states `h` without zero
rows; it is even in `s`; and the derivatives of `𝓑_{>k}` in the hidden state and in the weights at
`t^m h` are those of the map at `(1/t, h)`, the first with the factor `t^{−m}`. The derivatives of
all orders of the paper and their being meromorphic at infinity: `Depth/ScaledSuffixOrders.lean`;
the holomorphic extension with bounds uniform in `t`: `Depth/ScaledSuffixHolomorphic.lean`.
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise Topology

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable (A : Arch T d L) {ε : ℝ}

/-- **The network after the normalization of the hidden state `h_k`** (the paper's `𝓑^♯`):
`𝓑_{>k}(h) = 𝓑^♯(χ(h))`. -/
def suffixPost (θ : Params A dIn dOut) (k : Fin (L + 1)) (n : Matrix T d ℝ) : Matrix T dOut ℝ :=
  Fin.lastCases (motive := fun _ => Matrix T dOut ℝ) (n * θ.D)
    (fun ℓ => suffix A 0 θ ℓ.succ (A.f ℓ (n * θ.read ℓ) * θ.write ℓ)) k

/-- `𝓑_{>k}(h) = 𝓑^♯(χ(h))`, in a network without skips. -/
theorem suffix_eq_suffixPost (θ : Params A dIn dOut) (k : Fin (L + 1)) (h : Matrix T d ℝ) :
    suffix A 0 θ k h = suffixPost A θ k (A.χ h) := by
  cases k using Fin.lastCases with
  | last =>
    -- `𝓑_{>L}(h) = χ(h) D`
    rw [suffix_last]
    simp only [suffixPost, Fin.lastCases_last]
  | cast ℓ =>
    -- `𝓑_{>ℓ-1}(h) = 𝓑_{>ℓ}(f_ℓ(χ(h) W_read) W_write)`: the stream term `h 0` vanishes
    rw [suffix_castSucc]
    simp only [suffixPost, Fin.lastCases_castSucc, Pi.zero_apply, Matrix.mul_zero, zero_add]

omit [Fintype T] [DecidableEq d] in
/-- Helper: a positive factor of the hidden state moves into the constant of RMSNorm,
`N_ε(c h) = N_{ε c^{-2}}(h)` for `c > 0`. -/
private theorem rmsNorm_smul_of_pos {c : ℝ} (hc : 0 < c) (ε : ℝ) (h : Matrix T d ℝ) :
    rmsNorm ε (c • h) = rmsNorm (ε * c⁻¹ ^ 2) h := by
  ext τ i
  -- row by row
  have hrow : rmsRow ε (c • h τ) = rmsRow (ε * c⁻¹ ^ 2) (h τ) := by
    unfold rmsRow
    -- `‖c v‖²/d + ε = c² (‖v‖²/d + ε c^{-2})`
    have hc2 : c ^ 2 * c⁻¹ ^ 2 = 1 := by rw [← mul_pow, mul_inv_cancel₀ hc.ne', one_pow]
    have hq : (c • h τ ⬝ᵥ c • h τ) / (Fintype.card d : ℝ) + ε
        = c ^ 2 * ((h τ ⬝ᵥ h τ) / (Fintype.card d : ℝ) + ε * c⁻¹ ^ 2) := by
      rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
      linear_combination (-ε) * hc2
    -- `√(c² x) = c √x` (for every real `x`), and the factor `c` cancels
    rw [hq, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc.le, mul_inv, smul_smul]
    congr 1
    rw [mul_comm c⁻¹, mul_assoc, inv_mul_cancel₀ hc.ne', mul_one]
  exact congrFun hrow i

/-- **The rest of the network on a ray, in the variables `s = 1/t` and `h`:**
`(s, h) ↦ 𝓑^♯(N_{ε s^{2m}}(h))`. For `t > 0` it is `𝓑_{>k}(t^m h)` at `s = 1/t`. -/
noncomputable def scaledSuffix (ε : ℝ) (m : ℕ) (θ : Params A dIn dOut) (k : Fin (L + 1))
    (z : ℝ × Matrix T d ℝ) : Matrix T dOut ℝ :=
  suffixPost A θ k (rmsNorm (ε * z.1 ^ (2 * m)) z.2)

/-- `𝓑_{>k}(t^m h) = 𝓑^♯(N_{ε t^{−2m}}(h))` for `t > 0`, under pre-RMSNorm. -/
theorem suffix_pow_smul_eq_scaledSuffix (hχ : A.χ = rmsNorm ε) (θ : Params A dIn dOut)
    (k : Fin (L + 1)) {t : ℝ} (ht : 0 < t) (m : ℕ) (h : Matrix T d ℝ) :
    suffix A 0 θ k (t ^ m • h) = scaledSuffix A ε m θ k (1 / t, h) := by
  -- `𝓑_{>k}(t^m h) = 𝓑^♯(N_ε(t^m h))` and `N_ε(t^m h) = N_{ε t^{-2m}}(h)`
  rw [suffix_eq_suffixPost, hχ, rmsNorm_smul_of_pos (pow_pos ht m)]
  have he : (t ^ m)⁻¹ ^ 2 = (1 / t) ^ (2 * m) := by
    rw [one_div, ← inv_pow, ← pow_mul, mul_comm]
  rw [he]
  rfl

/-- The map is even in `s`. -/
theorem scaledSuffix_neg (m : ℕ) (θ : Params A dIn dOut) (k : Fin (L + 1)) (s : ℝ)
    (h : Matrix T d ℝ) :
    scaledSuffix A ε m θ k (-s, h) = scaledSuffix A ε m θ k (s, h) := by
  -- `(-s)^{2m} = s^{2m}`
  show suffixPost A θ k (rmsNorm (ε * (-s) ^ (2 * m)) h)
    = suffixPost A θ k (rmsNorm (ε * s ^ (2 * m)) h)
  rw [Even.neg_pow (even_two_mul m)]

/-- Helper (copy of a private lemma of `Depth/SuffixRMS.lean`): `√` is analytic at a positive
number, where it agrees with `x ↦ exp (log x / 2)`. -/
private theorem analyticAt_sqrt_of_pos'' {x : ℝ} (hx : 0 < x) : AnalyticAt ℝ Real.sqrt x := by
  have h : AnalyticAt ℝ (Real.exp ∘ fun y => Real.log y * (1 / 2)) x :=
    ((analyticAt_log hx).mul analyticAt_const).rexp
  refine h.congr ?_
  filter_upwards [lt_mem_nhds hx] with y hy
  show Real.exp (Real.log y * (1 / 2)) = Real.sqrt y
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hy]

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (copy of a private lemma of `Depth/SuffixRMS.lean`): an entry of a matrix is an
analytic (linear) function of the matrix. -/
private theorem analyticOnNhd_entry'' {m n : Type*} [Fintype m] [Fintype n] (t : m) (i : n) :
    AnalyticOnNhd ℝ (fun M : Matrix m n ℝ => M t i) Set.univ :=
  ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : n => ℝ) i).comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : m => n → ℝ) t)).analyticOnNhd _

omit [DecidableEq d] in
/-- Helper: for `ε ≥ 0`, `(s, h) ↦ N_{ε s^{2m}}(h)` is real-analytic at `(s, H)` if no row of `H`
vanishes, also at `s = 0`: there the quantity under the root is `‖H_τ‖²/d + ε s^{2m} > 0`. -/
private theorem analyticAt_rmsNorm_scaled (hε : 0 ≤ ε) (m : ℕ) (s : ℝ) (H : Matrix T d ℝ)
    (hH : ∀ t, H t ≠ 0) :
    AnalyticAt ℝ (fun z : ℝ × Matrix T d ℝ => rmsNorm (ε * z.1 ^ (2 * m)) z.2) (s, H) := by
  -- entry `(τ, i)` is `(√(‖h_τ‖²/d + ε s^{2m}))⁻¹ h_{τi}`
  show AnalyticAt ℝ (fun z : ℝ × Matrix T d ℝ => fun τ => fun i =>
    (Real.sqrt ((z.2 τ ⬝ᵥ z.2 τ) / (Fintype.card d : ℝ) + ε * z.1 ^ (2 * m)))⁻¹ * z.2 τ i) (s, H)
  refine AnalyticAt.pi fun τ => AnalyticAt.pi fun i => ?_
  -- the entries of `h` are analytic functions of `(s, h)`
  have hent : ∀ j, AnalyticAt ℝ (fun z : ℝ × Matrix T d ℝ => z.2 τ j) (s, H) := fun j => by
    have hc := (analyticOnNhd_entry'' τ j H (Set.mem_univ _)).comp_of_eq
      (analyticAt_snd (𝕜 := ℝ) (p := (s, H))) rfl
    exact hc
  -- the quantity under the root is a polynomial in `s` and the entries of `h`
  have hq : AnalyticAt ℝ (fun z : ℝ × Matrix T d ℝ =>
      (z.2 τ ⬝ᵥ z.2 τ) / (Fintype.card d : ℝ) + ε * z.1 ^ (2 * m)) (s, H) :=
    ((Finset.analyticAt_fun_sum _ fun j _ => (hent j).mul (hent j)).div_const).add
      (analyticAt_const.mul (analyticAt_fst.pow _))
  -- it is positive at `(s, H)`: `‖H_τ‖² > 0` as `H_τ ≠ 0`, and `ε s^{2m} ≥ 0`
  have hpos : 0 < (H τ ⬝ᵥ H τ) / (Fintype.card d : ℝ) + ε * s ^ (2 * m) := by
    obtain ⟨j, -⟩ := Function.ne_iff.1 (hH τ)
    have hd : (0 : ℝ) < Fintype.card d := Nat.cast_pos.2 (Fintype.card_pos_iff.2 ⟨j⟩)
    have h1 : 0 < H τ ⬝ᵥ H τ :=
      lt_of_le_of_ne (Finset.sum_nonneg fun j _ => mul_self_nonneg (H τ j))
        (Ne.symm (mt dotProduct_self_eq_zero.1 (hH τ)))
    have h2 : 0 ≤ ε * s ^ (2 * m) := mul_nonneg hε (Even.pow_nonneg (even_two_mul m) s)
    have h3 := div_pos h1 hd
    linarith
  -- `√` is analytic at a positive number, and the inverse where it is not zero
  exact (((analyticAt_sqrt_of_pos'' hpos).comp
    (f := fun z : ℝ × Matrix T d ℝ =>
      (z.2 τ ⬝ᵥ z.2 τ) / (Fintype.card d : ℝ) + ε * z.1 ^ (2 * m)) hq).inv
      (Real.sqrt_pos.2 hpos).ne').mul (hent i)

/-- Helper: for an analytic `χ` and analytic blocks, `(θ', n) ↦ 𝓑^♯(n)` (with the weights `θ'`)
is real-analytic. -/
private theorem analyticOnNhd_suffixPost (hχ : AnalyticOnNhd ℝ A.χ Set.univ)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (k : Fin (L + 1)) :
    AnalyticOnNhd ℝ
      (fun p : Params A dIn dOut × Matrix T d ℝ => suffixPost A p.1 k p.2) Set.univ := by
  cases k using Fin.lastCases with
  | last =>
    -- `(θ', n) ↦ n D'`
    have hD : AnalyticOnNhd ℝ (fun p : Params A dIn dOut × Matrix T d ℝ => p.1.D) Set.univ :=
      ((LinearMap.toContinuousLinearMap
        (Params.linD (A := A) (dIn := dIn) (dOut := dOut))).analyticOnNhd _).comp
        analyticOnNhd_fst (Set.mapsTo_univ _ _)
    simp only [suffixPost, Fin.lastCases_last]
    exact analyticOnNhd_matrix_mul analyticOnNhd_snd hD
  | cast ℓ =>
    -- `(θ', n) ↦ 𝓑_{>ℓ+1}(f_ℓ(n W'_read) W'_write)` with the weights `θ'`
    have hr : AnalyticOnNhd ℝ
        (fun p : Params A dIn dOut × Matrix T d ℝ => p.1.read ℓ) Set.univ :=
      ((LinearMap.toContinuousLinearMap
        (Params.linRead (A := A) (dIn := dIn) (dOut := dOut) ℓ)).analyticOnNhd _).comp
        analyticOnNhd_fst (Set.mapsTo_univ _ _)
    have hw : AnalyticOnNhd ℝ
        (fun p : Params A dIn dOut × Matrix T d ℝ => p.1.write ℓ) Set.univ :=
      ((LinearMap.toContinuousLinearMap
        (Params.linWrite (A := A) (dIn := dIn) (dOut := dOut) ℓ)).analyticOnNhd _).comp
        analyticOnNhd_fst (Set.mapsTo_univ _ _)
    simp only [suffixPost, Fin.lastCases_castSucc]
    have hg : AnalyticOnNhd ℝ (fun p : Params A dIn dOut × Matrix T d ℝ =>
        (p.1, A.f ℓ (p.2 * p.1.read ℓ) * p.1.write ℓ)) Set.univ :=
      analyticOnNhd_fst.prod (analyticOnNhd_matrix_mul
        ((hf ℓ).comp (analyticOnNhd_matrix_mul analyticOnNhd_snd hr) (Set.mapsTo_univ _ _)) hw)
    have hc := (analyticOnNhd_suffix_prod_of_analytic (dIn := dIn) (dOut := dOut) A hχ hf
      ℓ.succ).comp hg (Set.mapsTo_univ _ _)
    exact hc

/-- **Lemma D.10, for a real variable:** under pre-RMSNorm with `ε > 0` and for real-analytic
blocks, `(θ, s, h) ↦ 𝓑^♯(N_{ε s^{2m}}(h))` is real-analytic at every `(θ, s, H)` such that no row
of `H` vanishes; in particular at `s = 0`, which is `t = ∞`. -/
theorem analyticAt_scaledSuffix (hε : 0 < ε) (hχ : A.χ = rmsNorm ε)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (m : ℕ) (θ : Params A dIn dOut)
    (k : Fin (L + 1)) (s : ℝ) (H : Matrix T d ℝ) (hH : ∀ t, H t ≠ 0) :
    AnalyticAt ℝ (fun x : Params A dIn dOut × ℝ × Matrix T d ℝ => scaledSuffix A ε m x.1 k x.2)
      (θ, s, H) := by
  have hχa : AnalyticOnNhd ℝ A.χ Set.univ := by rw [hχ]; exact analyticOnNhd_rmsNorm hε
  -- `(θ', s, h) ↦ (θ', N_{ε s^{2m}}(h))` is analytic at `(θ, s, H)`, as no row of `H` vanishes
  have hN := analyticAt_rmsNorm_scaled hε.le m s H hH
  have h1 : AnalyticAt ℝ (fun x : Params A dIn dOut × ℝ × Matrix T d ℝ =>
      (x.1, rmsNorm (ε * x.2.1 ^ (2 * m)) x.2.2)) (θ, s, H) := by
    have hc := hN.comp_of_eq
      (analyticAt_snd (𝕜 := ℝ) (p := ((θ, s, H) : Params A dIn dOut × ℝ × Matrix T d ℝ))) rfl
    exact analyticAt_fst.prod hc
  -- `(θ', n) ↦ 𝓑^♯(n)` with the weights `θ'` is analytic everywhere
  have h2 := analyticOnNhd_suffixPost (dIn := dIn) (dOut := dOut) A hχa hf k
    (θ, rmsNorm (ε * s ^ (2 * m)) H) (Set.mem_univ _)
  have hc := h2.comp_of_eq h1 rfl
  exact hc

/-- The derivative of `𝓑_{>k}` in the hidden state at `t^m h`, from the map at `(1/t, h)`. -/
theorem fderiv_suffix_pow_smul (hε : 0 < ε) (hχ : A.χ = rmsNorm ε)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (θ : Params A dIn dOut) (k : Fin (L + 1))
    {t : ℝ} (ht : 0 < t) (m : ℕ) (h u : Matrix T d ℝ) :
    fderiv ℝ (fun h' : Matrix T d ℝ => suffix A 0 θ k h') (t ^ m • h) u
      = (1 / t) ^ m
        • fderiv ℝ (fun h' : Matrix T d ℝ => scaledSuffix A ε m θ k (1 / t, h')) h u := by
  have hχa : AnalyticOnNhd ℝ A.χ Set.univ := by rw [hχ]; exact analyticOnNhd_rmsNorm hε
  -- by the scaling identity, `h' ↦ 𝓑^♯(N_{ε t^{-2m}}(h'))` is `h' ↦ 𝓑_{>k}(t^m h')`
  have hfun : (fun h' : Matrix T d ℝ => scaledSuffix A ε m θ k (1 / t, h'))
      = fun h' => suffix A 0 θ k (t ^ m • h') :=
    funext fun h' => (suffix_pow_smul_eq_scaledSuffix A hχ θ k ht m h').symm
  rw [hfun]
  -- the chain rule with the linear map `h' ↦ t^m h'`:
  -- `𝐃(𝓑_{>k}(t^m ·))(h) u = t^m 𝐃𝓑_{>k}(t^m h) u`
  have hF := (analyticOnNhd_suffix_of_analytic A θ hχa hf k (t ^ m • h)
    (Set.mem_univ _)).differentiableAt.hasFDerivAt
  have hl : HasFDerivAt (fun h' : Matrix T d ℝ => t ^ m • h')
      (t ^ m • ContinuousLinearMap.id ℝ (Matrix T d ℝ)) h :=
    (hasFDerivAt_id h).const_smul (t ^ m)
  have hc := hF.comp h hl
  have e : fderiv ℝ (fun h' : Matrix T d ℝ => suffix A 0 θ k (t ^ m • h')) h u
      = t ^ m • fderiv ℝ (fun h' : Matrix T d ℝ => suffix A 0 θ k h') (t ^ m • h) u := by
    have e := DFunLike.congr_fun hc.fderiv u
    -- the right side of `e` is `𝐃𝓑_{>k}(t^m h) (t^m u)`, by definition
    have e2 : fderiv ℝ (fun h' : Matrix T d ℝ => suffix A 0 θ k h') (t ^ m • h) (t ^ m • u)
        = t ^ m • fderiv ℝ (fun h' : Matrix T d ℝ => suffix A 0 θ k h') (t ^ m • h) u :=
      map_smul _ _ _
    exact e.trans e2
  -- `(1/t)^m t^m = 1`
  rw [e, smul_smul, ← mul_pow, one_div, inv_mul_cancel₀ ht.ne', one_pow, one_smul]

/-- The derivative of `𝓑_{>k}` in the weights at `t^m h`, from the map at `(1/t, h)`. -/
theorem fderiv_params_suffix_pow_smul (hχ : A.χ = rmsNorm ε) (θ η : Params A dIn dOut)
    (k : Fin (L + 1)) {t : ℝ} (ht : 0 < t) (m : ℕ) (h : Matrix T d ℝ) :
    fderiv ℝ (fun θ' : Params A dIn dOut => suffix A 0 θ' k (t ^ m • h)) θ η
      = fderiv ℝ (fun θ' : Params A dIn dOut => scaledSuffix A ε m θ' k (1 / t, h)) θ η := by
  -- the two functions of the weights are equal (the scaling identity holds for every `θ'`)
  have hfun : (fun θ' : Params A dIn dOut => suffix A 0 θ' k (t ^ m • h))
      = fun θ' => scaledSuffix A ε m θ' k (1 / t, h) :=
    funext fun θ' => suffix_pow_smul_eq_scaledSuffix A hχ θ' k ht m h
  rw [hfun]

end Skips
