import SkipsLean.Depth.SuffixZero
import Mathlib.Analysis.Normed.Module.Connected

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

/-! ### Lemma D.2 in the case (0): helpers -/

omit [DecidableEq d] in
/-- Helper: `‖v‖² > 0` for a row `v ≠ 0`. -/
private theorem dotProduct_self_pos_zd {v : d → ℝ} (hv : v ≠ 0) : 0 < v ⬝ᵥ v :=
  lt_of_le_of_ne (Finset.sum_nonneg fun j _ => mul_self_nonneg (v j))
    (fun h0 => hv (dotProduct_self_eq_zero.1 h0.symm))

omit [DecidableEq d] in
/-- Helper: `‖v‖² / d > 0` for a row `v ≠ 0` (then `d` is not empty). -/
private theorem dotProduct_self_div_pos_zd {v : d → ℝ} (hv : v ≠ 0) :
    0 < (v ⬝ᵥ v) / (Fintype.card d : ℝ) := by
  obtain ⟨j, -⟩ := Function.ne_iff.1 hv
  exact div_pos (dotProduct_self_pos_zd hv) (Nat.cast_pos.2 (Fintype.card_pos_iff.2 ⟨j⟩))

/-- The matrices without a zero row (the paper's "rows `h ≠ 0`"). -/
private def nzRows_zd (T d : Type*) : Set (Matrix T d ℝ) := {h | ∀ t, h t ≠ 0}

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the matrices without a zero row are the product of the sets `{v ≠ 0}`. -/
private theorem nzRows_eq_pi_zd :
    nzRows_zd T d = Set.pi Set.univ fun _ : T => ({0}ᶜ : Set (d → ℝ)) := by
  exact Set.ext fun h => ⟨fun hh t _ => hh t, fun hh t => hh t (Set.mem_univ t)⟩

omit [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the matrices without a zero row form an open set. -/
private theorem isOpen_nzRows_zd : IsOpen (nzRows_zd T d) := by
  rw [nzRows_eq_pi_zd]
  exact isOpen_set_pi Set.finite_univ fun _ _ => isOpen_compl_singleton

omit [Fintype T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: for `d ≥ 2` the matrices without a zero row form a connected set. -/
private theorem isPreconnected_nzRows_zd (hd : 2 ≤ Fintype.card d) :
    IsPreconnected (nzRows_zd T d) := by
  rw [nzRows_eq_pi_zd]
  refine isPreconnected_univ_pi fun _ =>
    (isConnected_compl_singleton_of_one_lt_rank ?_ 0).isPreconnected
  rw [rank_fun']
  exact_mod_cast hd

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: for `d ≥ 1` the matrices without a zero row form a dense set. -/
private theorem dense_nzRows_zd [Nonempty d] : Dense (nzRows_zd T d) := by
  rw [nzRows_eq_pi_zd]
  exact dense_pi _ fun _ _ => dense_compl_singleton 0

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: an analytic family `x ↦ J x` of linear maps between finite-dimensional spaces (each
`x ↦ J x w` analytic on a connected open set `D`) that is injective at one point `x₀ ∈ D` is
injective on an open set `V ⊆ D` that contains `x₀` and meets every open set that meets `D`.
With a left inverse `K` of `J x₀`, the determinant `φ x` of `K ∘ J x` is analytic on `D` with
`φ x₀ = 1`; `V = {x ∈ D | φ x ≠ 0}`, and by the identity theorem `φ` vanishes on no nonempty open
subset of `D`. -/
private theorem exists_open_injective_of_analytic_zd
    {X E F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {D : Set X} (hDo : IsOpen D) (hDc : IsPreconnected D) {J : X → E →ₗ[ℝ] F}
    (hJ : ∀ w, AnalyticOnNhd ℝ (fun x => J x w) D) {x₀ : X} (hx₀ : x₀ ∈ D)
    (h₀ : Function.Injective (J x₀)) :
    ∃ V : Set X, IsOpen V ∧ x₀ ∈ V ∧ V ⊆ D ∧ (∀ x ∈ V, Function.Injective (J x)) ∧
      ∀ O : Set X, IsOpen O → (O ∩ D).Nonempty → (O ∩ V).Nonempty := by
  -- a left inverse `K` of `J x₀`
  obtain ⟨K, hK⟩ := (J x₀).exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 h₀)
  -- the matrix of `K ∘ J x` in a basis `b` of `E`; its entries are analytic on `D`
  let b := Module.finBasis ℝ E
  have hentry : ∀ i j, AnalyticOnNhd ℝ (fun x => LinearMap.toMatrix b b (K ∘ₗ J x) i j) D := by
    intro i j
    have e : (fun x => LinearMap.toMatrix b b (K ∘ₗ J x) i j)
        = fun x => LinearMap.toContinuousLinearMap (b.coord i ∘ₗ K) (J x (b j)) := by
      funext x
      rw [LinearMap.toMatrix_apply]
      rfl
    rw [e]
    intro x hx
    have hc := ((LinearMap.toContinuousLinearMap (b.coord i ∘ₗ K)).analyticAt _).comp
      (hJ (b j) x hx)
    exact hc
  -- its determinant `φ x` is analytic on `D` (a polynomial in the entries), and `φ x₀ = 1`
  let φ : X → ℝ := fun x => (LinearMap.toMatrix b b (K ∘ₗ J x)).det
  have hφ : AnalyticOnNhd ℝ φ D := by
    show AnalyticOnNhd ℝ (fun x => (LinearMap.toMatrix b b (K ∘ₗ J x)).det) D
    simp only [Matrix.det_apply']
    exact Finset.analyticOnNhd_fun_sum _ fun σ _ => analyticOnNhd_const.mul
      (Finset.analyticOnNhd_fun_prod _ fun i _ => hentry (σ i) i)
  have hφ₀ : φ x₀ = 1 := by
    show (LinearMap.toMatrix b b (K ∘ₗ J x₀)).det = 1
    rw [hK, LinearMap.toMatrix_id, Matrix.det_one]
  -- where `φ x ≠ 0`, `K ∘ J x` is invertible, so `J x` is injective
  have hφinj : ∀ x, φ x ≠ 0 → Function.Injective (J x) := by
    intro x hx
    have hdet : LinearMap.det (K ∘ₗ J x) ≠ 0 := by
      rw [← LinearMap.det_toMatrix b]
      exact hx
    have hbij := (Module.End.isUnit_iff _).1
      ((LinearMap.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hdet))
    have hinj := hbij.1
    rw [LinearMap.coe_comp] at hinj
    exact hinj.of_comp
  refine ⟨D ∩ φ ⁻¹' {0}ᶜ, hφ.continuousOn.isOpen_inter_preimage hDo isOpen_compl_singleton,
    ⟨hx₀, by rw [Set.mem_preimage, hφ₀]; exact one_ne_zero⟩, Set.inter_subset_left,
    fun x hx => hφinj x hx.2, ?_⟩
  -- if `φ` vanished on a nonempty open subset of `D`, it would vanish on `D`
  rintro O hO ⟨z, hzO, hzD⟩
  by_contra hne
  have hzero : φ =ᶠ[nhds z] 0 :=
    Filter.eventually_of_mem ((hO.inter hDo).mem_nhds ⟨hzO, hzD⟩) fun y hy => by
      by_contra hy'
      exact hne ⟨y, hy.1, hy.2, hy'⟩
  have h1 := hφ.eqOn_zero_of_preconnected_of_eventuallyEq_zero hDc hzD hzero hx₀
  rw [hφ₀] at h1
  exact one_ne_zero h1

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: `x ↦ 𝐃f(x) w` is analytic where `f` is. -/
private theorem analyticOnNhd_fderiv_apply_zd {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {f : E → F}
    {s : Set E} (hf : AnalyticOnNhd ℝ f s) (w : E) :
    AnalyticOnNhd ℝ (fun x => fderiv ℝ f x w) s := fun x hx => by
  have hc := ((ContinuousLinearMap.apply ℝ F w).analyticAt _).comp (hf.fderiv x hx)
  exact hc

omit [Fintype T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: `N_0(h)` is `h` with its rows multiplied by positive numbers. -/
private theorem rmsNorm_zero_eq_smul_rows_zd (h : Matrix T d ℝ) :
    ∃ c : T → ℝ, (∀ t, 0 < c t) ∧ rmsNorm 0 h = Matrix.of fun t => c t • h t := by
  classical
  refine ⟨fun t => if h t = 0 then 1
    else (Real.sqrt ((h t ⬝ᵥ h t) / (Fintype.card d : ℝ) + 0))⁻¹, fun t => ?_, ?_⟩
  · by_cases ht : h t = 0
    · simp only [ht, ite_true]
      exact one_pos
    · simp only [ht, ite_false]
      exact inv_pos.2 (Real.sqrt_pos.2 (by rw [add_zero]; exact dotProduct_self_div_pos_zd ht))
  · ext t i
    show rmsRow 0 (h t) i = _
    by_cases ht : h t = 0
    · simp [rmsRow, ht]
    · simp [rmsRow, ht]

omit [Fintype T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: `N_0 ∘ N_0 = N_0`. -/
private theorem rmsNorm_zero_idem_zd (h : Matrix T d ℝ) :
    rmsNorm 0 (rmsNorm 0 h) = rmsNorm 0 h := by
  obtain ⟨c, hc, e⟩ := rmsNorm_zero_eq_smul_rows_zd h
  conv_lhs => rw [e, rmsNorm_zero_smul_rows_zd h c hc]

/-- Helper: `𝓑_{>k}(N_0(h)) = 𝓑_{>k}(h)`. -/
private theorem suffix_rmsNorm_zero_zd (hχ : A.χ = rmsNorm 0) (k : Fin (L + 1))
    (h : Matrix T d ℝ) : suffix A 0 θ k (rmsNorm 0 h) = suffix A 0 θ k h := by
  obtain ⟨c, hc, e⟩ := rmsNorm_zero_eq_smul_rows_zd h
  rw [e]
  exact suffix_zero_smul_rows A θ hχ k h c hc

omit [DecidableEq d] in
/-- Helper: `𝐃N_0(h)` vanishes on the matrices whose rows are multiples of the rows of `h`. -/
private theorem fderiv_rmsNorm_zero_radial_zd (h : Matrix T d ℝ) (hh : ∀ t, h t ≠ 0)
    (a : T → ℝ) :
    fderiv ℝ (rmsNorm 0 : Matrix T d ℝ → Matrix T d ℝ) h (Matrix.of fun t => a t • h t) = 0 := by
  rw [fderiv_rmsNorm_zero_apply _ _ hh]
  ext t i
  have e := congrFun (congrFun (fderiv_rmsNorm_zero_self h hh) t) i
  rw [fderiv_rmsNorm_zero_apply _ _ hh] at e
  have hrow : (Matrix.of fun t => a t • h t) t = a t • h t := rfl
  simp only [Matrix.of_apply, hrow, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, dotProduct_smul,
    Matrix.zero_apply] at e ⊢
  linear_combination (a t) * e

omit [DecidableEq d] in
/-- Helper: a map `F` with `F ∘ N_0 = F` has `𝐃F(h) v = 0` when every row of `v` is a multiple
of the same row of `h` (no zero row in `h`). -/
private theorem fderiv_radial_zd {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Matrix T d ℝ → E} (hF : ∀ h, F (rmsNorm 0 h) = F h) {h : Matrix T d ℝ}
    (hh : ∀ t, h t ≠ 0) (hd : DifferentiableAt ℝ F (rmsNorm 0 h)) (a : T → ℝ) :
    fderiv ℝ F h (Matrix.of fun t => a t • h t) = 0 := by
  have e : F = F ∘ rmsNorm 0 := funext fun h => (hF h).symm
  have hc := fderiv_comp (g := F) (f := rmsNorm 0) h hd
    (analyticAt_rmsNorm_zero h hh).differentiableAt
  -- the chain rule, stated here so that the instances are the ones of the goal
  have h1 : fderiv ℝ (F ∘ rmsNorm 0) h (Matrix.of fun t => a t • h t)
      = fderiv ℝ F (rmsNorm 0 h)
          (fderiv ℝ (rmsNorm 0 : Matrix T d ℝ → Matrix T d ℝ) h (Matrix.of fun t => a t • h t)) :=
    DFunLike.congr_fun hc _
  rw [← e, fderiv_rmsNorm_zero_radial_zd h hh a, map_zero] at h1
  exact h1

omit [DecidableEq d] in
/-- Helper: a map `F` that does not change when the rows are multiplied by `c t` has
`𝐃F(h) v = 𝐃F(c·h)(c·v)`. -/
private theorem fderiv_smul_rows_zd {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Matrix T d ℝ → E} (c : T → ℝ) (hF : ∀ h, F (Matrix.of fun t => c t • h t) = F h)
    {h : Matrix T d ℝ} (hd : DifferentiableAt ℝ F (Matrix.of fun t => c t • h t))
    (v : Matrix T d ℝ) :
    fderiv ℝ F h v
      = fderiv ℝ F (Matrix.of fun t => c t • h t) (Matrix.of fun t => c t • v t) := by
  -- the row scaling `S`, a linear map
  let S : Matrix T d ℝ →ₗ[ℝ] Matrix T d ℝ :=
    { toFun := fun v => Matrix.of fun t => c t • v t
      map_add' := fun v w => by
        ext t i
        simp only [Matrix.of_apply, Matrix.add_apply, Pi.smul_apply, smul_eq_mul, mul_add]
      map_smul' := fun r v => by
        ext t i
        simp only [Matrix.of_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul,
          RingHom.id_apply]
        ring }
  let S' := LinearMap.toContinuousLinearMap S
  have e : F = F ∘ S' := funext fun h => (hF h).symm
  have hc := fderiv_comp (g := F) (f := ⇑S') h hd S'.differentiableAt
  -- the chain rule, stated here so that the instances are the ones of the goal
  have h1 : fderiv ℝ (F ∘ S') h v = fderiv ℝ F (S' h) (fderiv ℝ (⇑S') h v) :=
    DFunLike.congr_fun hc v
  have h2 : fderiv ℝ (⇑S') h v = S' v := DFunLike.congr_fun S'.fderiv v
  rw [h2, ← e] at h1
  exact h1

/-- Helper: the map `v ↦ (⟨v_t, h_t⟩)_t`. -/
private def radialLin_zd (h : Matrix T d ℝ) : Matrix T d ℝ →ₗ[ℝ] (T → ℝ) where
  toFun v := fun t => v t ⬝ᵥ h t
  map_add' v w := funext fun t => add_dotProduct (v t) (w t) (h t)
  map_smul' r v := funext fun t => smul_dotProduct r (v t) (h t)

omit [DecidableEq d] in
/-- Helper: for a map `F` with `F ∘ N_0 = F`, at `h` without a zero row: `𝐃F(h) v = 0` only for
`v` with rows multiples of those of `h`, if and only if `v ↦ (𝐃F(h) v, (⟨v_t, h_t⟩)_t)` is
injective. -/
private theorem kerProp_iff_injective_zd {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Matrix T d ℝ → E} (hF : ∀ h, F (rmsNorm 0 h) = F h) {h : Matrix T d ℝ}
    (hh : ∀ t, h t ≠ 0) (hd : DifferentiableAt ℝ F (rmsNorm 0 h)) :
    (∀ v : Matrix T d ℝ, fderiv ℝ F h v = 0 → ∀ t, ∃ a : ℝ, v t = a • h t) ↔
      Function.Injective ((fderiv ℝ F h : Matrix T d ℝ →ₗ[ℝ] E).prod (radialLin_zd h)) := by
  constructor
  · -- `v` in the kernel: its rows are `a_t h_t` with `a_t ‖h_t‖² = 0`
    intro hk
    refine (injective_iff_map_eq_zero _).2 fun v hv => ?_
    have h1 : fderiv ℝ F h v = 0 := congrArg Prod.fst hv
    have h2 : ∀ t, v t ⬝ᵥ h t = 0 := fun t => congrFun (congrArg Prod.snd hv) t
    ext t i
    obtain ⟨a, ha⟩ := hk v h1 t
    have h2t := h2 t
    rw [ha, smul_dotProduct, smul_eq_mul] at h2t
    have ha0 : a = 0 := (mul_eq_zero.1 h2t).resolve_right (dotProduct_self_pos_zd (hh t)).ne'
    have hvt : v t = 0 := by rw [ha, ha0, zero_smul]
    exact congrFun hvt i
  · -- remove from `v` its part along the rows of `h`: what is left is in the kernel
    intro hinj v hv t
    let a : T → ℝ := fun t => (v t ⬝ᵥ h t) / (h t ⬝ᵥ h t)
    have hw : ((fderiv ℝ F h : Matrix T d ℝ →ₗ[ℝ] E).prod (radialLin_zd h))
        (v - Matrix.of fun t => a t • h t) = 0 := by
      rw [map_sub]
      refine Prod.ext ?_ ?_
      · show fderiv ℝ F h v - fderiv ℝ F h (Matrix.of fun t => a t • h t) = 0
        rw [hv, fderiv_radial_zd hF hh hd a, sub_zero]
      · funext s
        show v s ⬝ᵥ h s - (a s • h s) ⬝ᵥ h s = 0
        have hs := (dotProduct_self_pos_zd (hh s)).ne'
        rw [smul_dotProduct, smul_eq_mul]
        show v s ⬝ᵥ h s - (v s ⬝ᵥ h s) / (h s ⬝ᵥ h s) * (h s ⬝ᵥ h s) = 0
        rw [div_mul_cancel₀ _ hs, sub_self]
    have h0 := hinj (hw.trans (map_zero _).symm)
    refine ⟨a t, ?_⟩
    have h0t : v t - a t • h t = 0 := congrFun h0 t
    exact sub_eq_zero.1 h0t

omit [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: `N_0(h)` has no zero row when `h` has none (its rows are on the sphere). -/
private theorem rmsNorm_zero_ne_zero_zd (h : Matrix T d ℝ) (hh : ∀ t, h t ≠ 0) :
    ∀ t, rmsNorm 0 h t ≠ 0 := by
  intro t h0
  have e := rmsNorm_zero_dotProduct_self h t (hh t)
  rw [h0, zero_dotProduct] at e
  obtain ⟨j, -⟩ := Function.ne_iff.1 (hh t)
  have hc : (0 : ℝ) < Fintype.card d := Nat.cast_pos.2 (Fintype.card_pos_iff.2 ⟨j⟩)
  linarith

/-- Helper: `h ↦ 𝓑_{>k}(h)` (weights `θ`) is analytic at every `h` without a zero row. -/
private theorem analyticAt_suffix_zd (hχ : A.χ = rmsNorm 0)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (hθ : RegularZero A θ) (k : Fin (L + 1))
    {h : Matrix T d ℝ} (hh : ∀ t, h t ≠ 0) :
    AnalyticAt ℝ (fun h' : Matrix T d ℝ => suffix A 0 θ k h') h := by
  have h1 : AnalyticAt ℝ (fun h' : Matrix T d ℝ => (θ, h')) h :=
    analyticAt_const.prod analyticAt_id
  have hc := (analyticAt_suffix_prod_zero A θ hχ hf hθ k h hh).comp_of_eq h1 rfl
  exact hc

/-- Helper (Lemma D.2 from one good point): if at one `h₀` without a zero row `𝐃𝓑_{>k}(h₀) v = 0`
only for `v` with rows multiples of those of `h₀`, then the set of all such `h` has the five
properties of Lemma D.2. It is the set where the analytic family
`v ↦ (𝐃𝓑_{>k}(h) v, (⟨v_t, h_t⟩)_t)` is injective, on the connected open set of the matrices
without a zero row. -/
private theorem kerSet_zd (hχ : A.χ = rmsNorm 0)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (hθ : RegularZero A θ)
    (hd : 2 ≤ Fintype.card d) (k : Fin (L + 1)) {h₀ : Matrix T d ℝ} (hh₀ : ∀ t, h₀ t ≠ 0)
    (hk₀ : ∀ v : Matrix T d ℝ,
      fderiv ℝ (fun h' : Matrix T d ℝ => suffix A 0 θ k h') h₀ v = 0 →
        ∀ t, ∃ a : ℝ, v t = a • h₀ t) :
    ∃ U : Set (Matrix T d ℝ), IsOpen U ∧ Dense U ∧ (∀ h ∈ U, ∀ t, h t ≠ 0) ∧
      (∀ h ∈ U, ∀ c : T → ℝ, (∀ t, 0 < c t) → (Matrix.of fun t => c t • h t) ∈ U) ∧
      ∀ h ∈ U, ∀ v : Matrix T d ℝ,
        fderiv ℝ (fun h' : Matrix T d ℝ => suffix A 0 θ k h') h v = 0 →
          ∀ t, ∃ a : ℝ, v t = a • h t := by
  have : Nonempty d := Fintype.card_pos_iff.1 (by omega)
  -- `S = 𝓑_{>k}` is analytic on the matrices without a zero row, and `S ∘ N_0 = S`
  have hSa : AnalyticOnNhd ℝ (fun h' : Matrix T d ℝ => suffix A 0 θ k h') (nzRows_zd T d) :=
    fun h hh => analyticAt_suffix_zd A θ hχ hf hθ k hh
  have hSN : ∀ h : Matrix T d ℝ, (fun h' : Matrix T d ℝ => suffix A 0 θ k h') (rmsNorm 0 h)
      = (fun h' : Matrix T d ℝ => suffix A 0 θ k h') h :=
    fun h => suffix_rmsNorm_zero_zd A θ hχ k h
  -- the family `J h = (𝐃S(h), (⟨·_t, h_t⟩)_t)`, analytic in `h`
  let J : Matrix T d ℝ → Matrix T d ℝ →ₗ[ℝ] Matrix T dOut ℝ × (T → ℝ) := fun h =>
    (fderiv ℝ (fun h' : Matrix T d ℝ => suffix A 0 θ k h') h :
      Matrix T d ℝ →ₗ[ℝ] Matrix T dOut ℝ).prod (radialLin_zd h)
  have hJ : ∀ w, AnalyticOnNhd ℝ (fun h => J h w) (nzRows_zd T d) := by
    intro w
    have h1 := analyticOnNhd_fderiv_apply_zd hSa w
    have h2 : AnalyticOnNhd ℝ (fun h : Matrix T d ℝ => radialLin_zd w h) (nzRows_zd T d) :=
      fun h _ => (LinearMap.toContinuousLinearMap (radialLin_zd w)).analyticAt h
    have e : (fun h => J h w) = fun h =>
        (fderiv ℝ (fun h' : Matrix T d ℝ => suffix A 0 θ k h') h w, radialLin_zd w h) := by
      funext h
      exact Prod.ext rfl (funext fun t => dotProduct_comm _ _)
    rw [e]
    exact h1.prod h2
  -- on the matrices without a zero row, the kernel property is the injectivity of `J h`
  have hkey : ∀ h : Matrix T d ℝ, (∀ t, h t ≠ 0) →
      ((∀ v : Matrix T d ℝ, fderiv ℝ (fun h' : Matrix T d ℝ => suffix A 0 θ k h') h v = 0 →
        ∀ t, ∃ a : ℝ, v t = a • h t) ↔ Function.Injective (J h)) := fun h hh =>
    kerProp_iff_injective_zd hSN hh (hSa _ (rmsNorm_zero_ne_zero_zd h hh)).differentiableAt
  refine ⟨{h | (∀ t, h t ≠ 0) ∧ ∀ v : Matrix T d ℝ,
    fderiv ℝ (fun h' : Matrix T d ℝ => suffix A 0 θ k h') h v = 0 →
      ∀ t, ∃ a : ℝ, v t = a • h t}, ?_, ?_, fun h hh => hh.1, ?_, fun h hh => hh.2⟩
  · -- open: around each of its points, `J` is injective on an open set
    rw [isOpen_iff_forall_mem_open]
    intro h hh
    obtain ⟨V, hVo, hhV, hVD, hVinj, -⟩ := exists_open_injective_of_analytic_zd
      isOpen_nzRows_zd (isPreconnected_nzRows_zd hd) hJ hh.1 ((hkey h hh.1).1 hh.2)
    exact ⟨V, fun x hx => ⟨hVD hx, (hkey x (hVD hx)).2 (hVinj x hx)⟩, hVo, hhV⟩
  · -- dense: the open set of injectivity around `h₀` meets every open set that meets the dense
    -- set of the matrices without a zero row
    obtain ⟨V, -, -, hVD, hVinj, hVmeet⟩ := exists_open_injective_of_analytic_zd
      isOpen_nzRows_zd (isPreconnected_nzRows_zd hd) hJ hh₀ ((hkey h₀ hh₀).1 hk₀)
    rw [dense_iff_inter_open]
    intro O hO hOne
    obtain ⟨x, hxO, hxV⟩ := hVmeet O hO (dense_nzRows_zd.inter_open_nonempty O hO hOne)
    exact ⟨x, hxO, hVD hxV, (hkey x (hVD hxV)).2 (hVinj x hxV)⟩
  · -- closed under positive row scalings: `𝐃S(h) v = 𝐃S(c·h)(c·v)`
    rintro h ⟨hh, hk⟩ c hc
    have hch : ∀ t, (Matrix.of fun t => c t • h t) t ≠ 0 :=
      fun t => smul_ne_zero (hc t).ne' (hh t)
    refine ⟨hch, fun w hw t => ?_⟩
    have e := fderiv_smul_rows_zd (F := fun h' : Matrix T d ℝ => suffix A 0 θ k h') c
      (fun h' => suffix_zero_smul_rows A θ hχ k h' c hc) (hSa _ hch).differentiableAt
      (Matrix.of fun t => (c t)⁻¹ • w t)
    have hcw : (Matrix.of fun t => c t • (Matrix.of fun t => (c t)⁻¹ • w t) t) = w := by
      ext s i
      show c s * ((c s)⁻¹ * w s i) = w s i
      rw [← mul_assoc, mul_inv_cancel₀ (hc s).ne', one_mul]
    rw [hcw] at e
    obtain ⟨a, ha⟩ := hk _ (e.trans hw) t
    have ha' : (c t)⁻¹ • w t = a • h t := ha
    refine ⟨a, ?_⟩
    show w t = a • (c t • h t)
    rw [smul_comm, ← ha', smul_smul, mul_inv_cancel₀ (hc t).ne', one_smul]

/-- Helper: `y ↦ y M`, as a continuous linear map. -/
private noncomputable def mulRightCLM_zd {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
    (M : Matrix n p ℝ) : Matrix m n ℝ →L[ℝ] Matrix m p ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun y => y * M
      map_add' := fun a b => Matrix.add_mul a b M
      map_smul' := fun c a => Matrix.smul_mul c a M }

/-- Helper (Lemma D.2 for `k = L`): `𝐃𝓑_{>L}(h) v = (𝐃N_0(h) v) D` vanishes only for `v` with
rows multiples of those of `h`, at every `h` without a zero row (`D` has rank `d`). -/
private theorem kerProp_last_zd (hχ : A.χ = rmsNorm 0) (hθ : RegularZero A θ)
    {h : Matrix T d ℝ} (hh : ∀ t, h t ≠ 0) :
    ∀ v : Matrix T d ℝ,
      fderiv ℝ (fun h' : Matrix T d ℝ => suffix A 0 θ (Fin.last L) h') h v = 0 →
        ∀ t, ∃ a : ℝ, v t = a • h t := by
  intro v hv t
  -- `𝐃𝓑_{>L}(h) v = (𝐃N_0(h) v) D`
  have hc := (mulRightCLM_zd (m := T) θ.D).hasFDerivAt.comp h
    (analyticAt_rmsNorm_zero h hh).differentiableAt.hasFDerivAt
  have e : fderiv ℝ (fun h' : Matrix T d ℝ => suffix A 0 θ (Fin.last L) h') h v
      = fderiv ℝ (rmsNorm 0 : Matrix T d ℝ → Matrix T d ℝ) h v * θ.D := by
    simp only [suffix_last, hχ]
    exact DFunLike.congr_fun hc.fderiv v
  rw [e] at hv
  -- `D R = 1`, so `𝐃N_0(h) v = 0`
  obtain ⟨R, hR⟩ : ∃ R : Matrix dOut d ℝ, θ.D * R = 1 :=
    Matrix.mulVec_surjective_iff_exists_right_inverse.1
      (Matrix.mulVec_surjective_iff_rank_eq_card.2 hθ.rank_D)
  have h0 : fderiv ℝ (rmsNorm 0 : Matrix T d ℝ → Matrix T d ℝ) h v = 0 := by
    have h1 := congrArg (· * R) hv
    simp only [Matrix.mul_assoc, hR, Matrix.mul_one, Matrix.zero_mul] at h1
    exact h1
  rw [fderiv_rmsNorm_zero_apply _ _ hh] at h0
  -- row `t`: `ρ⁻¹ v_t = (⟨h_t, v_t⟩/(d ρ³)) h_t`
  have h0t : (Real.sqrt ((h t ⬝ᵥ h t) / (Fintype.card d : ℝ)))⁻¹ • v t
      - ((h t ⬝ᵥ v t) / (Fintype.card d : ℝ)
        * (Real.sqrt ((h t ⬝ᵥ h t) / (Fintype.card d : ℝ)))⁻¹ ^ 3) • h t = 0 :=
    congrFun h0 t
  have hρ := (Real.sqrt_pos.2 (dotProduct_self_div_pos_zd (hh t))).ne'
  generalize Real.sqrt ((h t ⬝ᵥ h t) / (Fintype.card d : ℝ)) = ρ at h0t hρ
  refine ⟨ρ * ((h t ⬝ᵥ v t) / (Fintype.card d : ℝ) * ρ⁻¹ ^ 3), ?_⟩
  rw [sub_eq_zero] at h0t
  rw [← smul_smul, ← h0t, smul_smul, mul_inv_cancel₀ hρ, one_smul]

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (as in `Depth/SuffixRMS.lean`): an entry of a matrix is an analytic (linear) function
of the matrix. -/
private theorem analyticAt_entry_zd {m n : Type*} [Fintype m] [Fintype n] (t : m) (i : n)
    (M₀ : Matrix m n ℝ) : AnalyticAt ℝ (fun M : Matrix m n ℝ => M t i) M₀ :=
  ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : n => ℝ) i).comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : m => n → ℝ) t)).analyticAt _

/-- `Ψ(h) = (‖h_t‖² G(h)_t)_t`: `G(h)` with its rows multiplied by the squared norms of the rows
of `h`. -/
private def rowScale_zd (G : Matrix T d ℝ → Matrix T d ℝ) (h : Matrix T d ℝ) : Matrix T d ℝ :=
  Matrix.of fun t => (h t ⬝ᵥ h t) • G h t

omit [DecidableEq d] in
/-- Helper: `Ψ` is analytic where `G` is. -/
private theorem analyticAt_rowScale_zd {G : Matrix T d ℝ → Matrix T d ℝ} {h : Matrix T d ℝ}
    (hG : AnalyticAt ℝ G h) : AnalyticAt ℝ (rowScale_zd G) h := by
  show AnalyticAt ℝ (fun h' : Matrix T d ℝ => fun t => fun i => (h' t ⬝ᵥ h' t) * G h' t i) h
  refine AnalyticAt.pi fun t => AnalyticAt.pi fun i => ?_
  have hq : AnalyticAt ℝ (fun h' : Matrix T d ℝ => h' t ⬝ᵥ h' t) h :=
    Finset.analyticAt_fun_sum _ fun j _ =>
      (analyticAt_entry_zd t j h).mul (analyticAt_entry_zd t j h)
  have hGe : AnalyticAt ℝ (fun h' => G h' t i) h := by
    have hc := (analyticAt_entry_zd t i (G h)).comp hG
    exact hc
  exact hq.mul hGe

omit [DecidableEq d] in
/-- Helper: the derivative of `Ψ`, row by row:
`𝐃Ψ(h) v = (2 ⟨h_t, v_t⟩ G(h)_t + ‖h_t‖² (𝐃G(h) v)_t)_t`. -/
private theorem fderiv_rowScale_zd {G : Matrix T d ℝ → Matrix T d ℝ} {h : Matrix T d ℝ}
    (hG : DifferentiableAt ℝ G h) (hΨ : DifferentiableAt ℝ (rowScale_zd G) h)
    (v : Matrix T d ℝ) :
    fderiv ℝ (rowScale_zd G) h v
      = Matrix.of fun t => (2 * (h t ⬝ᵥ v t)) • G h t + (h t ⬝ᵥ h t) • fderiv ℝ G h v t := by
  -- along the line `τ ↦ h + τ v`, entry by entry
  have hline : HasDerivAt (fun τ : ℝ => h + τ • v) v 0 := by
    have h1 := ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add h
    rw [one_smul] at h1
    exact h1
  have h0 : h = h + (0 : ℝ) • v := by rw [zero_smul, add_zero]
  have hF := hΨ.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hline h0
  have hGl := hG.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hline h0
  refine hF.unique (hasDerivAt_pi.2 fun t => hasDerivAt_pi.2 fun i => ?_)
  -- `‖h_t + τ v_t‖²` has the derivative `2 ⟨h_t, v_t⟩` at `0`
  have hdot : HasDerivAt (fun τ : ℝ => (h t + τ • v t) ⬝ᵥ (h t + τ • v t))
      (2 * (h t ⬝ᵥ v t)) 0 := by
    have e : (fun τ : ℝ => (h t + τ • v t) ⬝ᵥ (h t + τ • v t))
        = fun τ => h t ⬝ᵥ h t + τ * (2 * (h t ⬝ᵥ v t)) + τ * τ * (v t ⬝ᵥ v t) := by
      funext τ
      simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul,
        dotProduct_comm (v t) (h t)]
      ring
    rw [e]
    exact hasDerivAt_quad _ _ _
  -- the entry `(t, i)` of `G(h + τ v)`
  have hGe : HasDerivAt (fun τ : ℝ => G (h + τ • v) t i) (fderiv ℝ G h v t i) 0 :=
    hasDerivAt_pi.1 (hasDerivAt_pi.1 hGl t) i
  have hm := hdot.mul hGe
  simp only [zero_smul, add_zero] at hm
  exact hm

omit [DecidableEq d] in
/-- Helper: at `h` without a zero row, for `G` with `G ∘ N_0 = G`: if `𝐃Ψ(h)` is injective, then
`𝐃G(h) v` has rows multiples of those of `G(h)` only for `v` with rows multiples of those of
`h` (remove from `v` the part along the rows of `h` that has the same image under `𝐃Ψ(h)`). -/
private theorem rk_of_injective_rowScale_zd {G : Matrix T d ℝ → Matrix T d ℝ}
    (hGN : ∀ h, G (rmsNorm 0 h) = G h) {h : Matrix T d ℝ} (hh : ∀ t, h t ≠ 0)
    (hGd : DifferentiableAt ℝ G (rmsNorm 0 h)) (hGd' : DifferentiableAt ℝ G h)
    (hΨd : DifferentiableAt ℝ (rowScale_zd G) h)
    (hinj : Function.Injective (fderiv ℝ (rowScale_zd G) h)) :
    ∀ v : Matrix T d ℝ, (∀ t, ∃ b : ℝ, fderiv ℝ G h v t = b • G h t) →
      ∀ t, ∃ a : ℝ, v t = a • h t := by
  intro v hv
  choose b hb using hv
  obtain ⟨a, ha⟩ : ∃ a : T → ℝ, ∀ t,
      a t * (2 * (h t ⬝ᵥ h t)) = 2 * (h t ⬝ᵥ v t) + (h t ⬝ᵥ h t) * b t :=
    ⟨fun t => (2 * (h t ⬝ᵥ v t) + (h t ⬝ᵥ h t) * b t) / (2 * (h t ⬝ᵥ h t)), fun t =>
      div_mul_cancel₀ _ (mul_ne_zero two_ne_zero (dotProduct_self_pos_zd (hh t)).ne')⟩
  -- `𝐃G(h)` vanishes along the rows of `h`
  have hw0 : fderiv ℝ G h (Matrix.of fun t => a t • h t) = 0 := fderiv_radial_zd hGN hh hGd a
  -- `𝐃Ψ(h) v = 𝐃Ψ(h) (a·h)`
  have heq : fderiv ℝ (rowScale_zd G) h v
      = fderiv ℝ (rowScale_zd G) h (Matrix.of fun t => a t • h t) := by
    rw [fderiv_rowScale_zd hGd' hΨd, fderiv_rowScale_zd hGd' hΨd, hw0]
    ext t i
    have hbt := congrFun (hb t) i
    have hrow : (Matrix.of fun t => a t • h t) t = a t • h t := rfl
    simp only [Matrix.of_apply, hrow, Pi.add_apply, Pi.smul_apply, smul_eq_mul, dotProduct_smul,
      Matrix.zero_apply, mul_zero, add_zero] at hbt ⊢
    rw [hbt]
    linear_combination (-(G h t i)) * ha t
  have hva := hinj heq
  intro t
  exact ⟨a t, congrFun hva t⟩

omit [DecidableEq d] in
/-- Helper: the converse: at `h` without a zero row, for `G` with `G ∘ N_0 = G` and no zero row
in `G(h)`, the property of `𝐃G(h)` makes `𝐃Ψ(h)` injective. -/
private theorem injective_rowScale_of_rk_zd {G : Matrix T d ℝ → Matrix T d ℝ}
    (hGN : ∀ h, G (rmsNorm 0 h) = G h) {h : Matrix T d ℝ} (hh : ∀ t, h t ≠ 0)
    (hGd : DifferentiableAt ℝ G (rmsNorm 0 h)) (hGd' : DifferentiableAt ℝ G h)
    (hΨd : DifferentiableAt ℝ (rowScale_zd G) h) (hG0 : ∀ t, G h t ≠ 0)
    (hrk : ∀ v : Matrix T d ℝ, (∀ t, ∃ b : ℝ, fderiv ℝ G h v t = b • G h t) →
      ∀ t, ∃ a : ℝ, v t = a • h t) :
    Function.Injective (fderiv ℝ (rowScale_zd G) h) := by
  refine (injective_iff_map_eq_zero _).2 fun v hv => ?_
  rw [fderiv_rowScale_zd hGd' hΨd] at hv
  have hrow : ∀ t, (2 * (h t ⬝ᵥ v t)) • G h t + (h t ⬝ᵥ h t) • fderiv ℝ G h v t = 0 :=
    fun t => congrFun hv t
  -- every row of `𝐃G(h) v` is a multiple of the same row of `G(h)`
  have hb : ∀ t, ∃ b : ℝ, fderiv ℝ G h v t = b • G h t := by
    intro t
    have hs := (dotProduct_self_pos_zd (hh t)).ne'
    refine ⟨-(2 * (h t ⬝ᵥ v t)) / (h t ⬝ᵥ h t), ?_⟩
    ext i
    have ei := congrFun (hrow t) i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at ei ⊢
    rw [div_mul_eq_mul_div, eq_div_iff hs]
    linear_combination ei
  -- so the rows of `v` are `a_t h_t`, and `𝐃G(h) v = 0`
  choose a ha using hrk v hb
  have hvr : v = Matrix.of fun t => a t • h t := by
    ext t i
    exact congrFun (ha t) i
  have hG0' : fderiv ℝ G h v = 0 := by
    rw [hvr]
    exact fderiv_radial_zd hGN hh hGd a
  -- then `2 ⟨h_t, v_t⟩ G(h)_t = 0` with `G(h)_t ≠ 0`: `a_t ‖h_t‖² = 0`
  ext t i
  have e' : (2 * (h t ⬝ᵥ v t)) • G h t = 0 := by
    have e := hrow t
    rw [hG0'] at e
    rwa [show (0 : Matrix T d ℝ) t = 0 from rfl, smul_zero, add_zero] at e
  have hhv : h t ⬝ᵥ v t = 0 := by
    rcases smul_eq_zero.1 e' with h1 | h1
    · linarith
    · exact absurd h1 (hG0 t)
  rw [ha t, dotProduct_smul, smul_eq_mul] at hhv
  have ha0 : a t = 0 := (mul_eq_zero.1 hhv).resolve_right (dotProduct_self_pos_zd (hh t)).ne'
  show v t i = 0
  rw [ha t, ha0, zero_smul]
  rfl

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
