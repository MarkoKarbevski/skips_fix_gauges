import SkipsLean.Depth.FlatAtWriteRows

/-!
# From an open set of rows to all hidden states, at any matrix of rank `d`

Paper (dimension paper): Appendix D.6 (the case `ε = 0`), proof of Lemma D.19, Step 1: "The right
side is real-analytic and homogeneous of degree `0` in the row `n ≠ 0`, and it vanishes for `ξ` in
the open set `P`, hence for all `n ≠ 0`. With `h = n W V`, which takes every value by (P1), this is
(16) for `k + 1`"; and proof of Lemma D.18, part (c): "The left side is real-analytic on the rows
`w̃ ∈ ℝ^{1×q}` with `w̃V ≠ 0`. These form a connected set, the complement of a subspace of
codimension `d_model ≥ 2`, so the identity holds on all of it."

`Depth/FlatAtWriteRows.lean` has this for the write `V` of a block and `η_V` (part (c) of
Lemma D.18). Here it is stated for any matrix `M` of rank `d` and any `η_M`, and for the network
after any hidden state: Step 1 of Lemma D.19 uses `M = W V` and `η_M = Z W V + η_W V + W η_V`.
The conclusion is the hypothesis of Lemma D.3 (`suffixFlatZero_of_flat_at_write`).
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut] {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)] {σ : ℝ → ℝ}

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: `r ↦ c(r) M`, with `c(r)` the matrix whose rows all equal `r`, as a linear map. -/
private def rowsMulLin_fam {q n : Type*} (p : Type*) [Fintype q] (M : Matrix q n ℝ) :
    (q → ℝ) →ₗ[ℝ] Matrix p n ℝ where
  toFun r := (Matrix.of fun _ : p => r) * M
  map_add' a b := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.of_apply, Pi.add_apply, Matrix.add_apply, add_mul,
      Finset.sum_add_distrib]
  map_smul' c a := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.of_apply, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul,
      RingHom.id_apply, Finset.mul_sum, mul_assoc]

/-- Helper: for `Φ` differentiable at `(x, y)`, the derivatives of its two partial maps add up to
its derivative along `(a, b)` (as in `Depth/StepZeroValues.lean`). -/
private theorem fderiv_partial_add_fam {E₁ E₂ F : Type*} [NormedAddCommGroup E₁]
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

/-- Helper: `y ↦ 𝐃f(g(y)) u(y)` is analytic at `x` if `f` is analytic at `g(x)` and `g`, `u` are
analytic at `x`. -/
private theorem analyticAt_fderiv_apply_fam {E F G : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {f : E → F} {g u : G → E} {x : G}
    (hg : AnalyticAt ℝ g x) (hu : AnalyticAt ℝ u x) (hf : AnalyticAt ℝ f (g x)) :
    AnalyticAt ℝ (fun y => fderiv ℝ f (g y) (u y)) x := by
  have h1 := hf.fderiv.comp hg
  have h2 := ((ContinuousLinearMap.id ℝ (E →L[ℝ] F)).analyticAt_bilinear
    (fderiv ℝ f (g x), u x)).comp₂ h1 hu
  exact h2

/-- **From an open set of rows to all hidden states:** in the case (0), for real-analytic MLP
blocks, `d ≥ 2`, regular `θ` and a matrix `M` of rank `d`: if
`𝐃𝓑_{>j}(rM)(r η_M) + 𝐃_θ𝓑_{>j}(rM) η = 0` for the rows `r` of a nonempty open set (the same row
at every token), then the identity holds at every `w` such that `wM` has no zero row. -/
theorem flat_at_matrix_of_isOpen_rows [Nonempty T] (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
    (hθ : RegularZero (Arch.mlp σ (rmsNorm 0) hid) θ) (hd : 2 ≤ Fintype.card d)
    (j : Fin (L + 1)) {m : Type*} [Fintype m] (M : Matrix m d ℝ)
    (hM : M.rank = Fintype.card d) (ηM : Matrix m d ℝ)
    (η : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
    (O : Set (m → ℝ)) (hO : IsOpen O) (hne : O.Nonempty)
    (h : ∀ r ∈ O,
      fderiv ℝ (fun h' : Matrix T d ℝ => suffix (Arch.mlp σ (rmsNorm 0) hid) 0 θ j h')
          ((Matrix.of fun (_ : T) => r) * M) ((Matrix.of fun (_ : T) => r) * ηM)
        + fderiv ℝ (fun θ' : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut =>
            suffix (Arch.mlp σ (rmsNorm 0) hid) 0 θ' j
              ((Matrix.of fun (_ : T) => r) * M)) θ η = 0) :
    ∀ w : Matrix T m ℝ, (∀ t, (w * M) t ≠ 0) →
      fderiv ℝ (fun h' : Matrix T d ℝ => suffix (Arch.mlp σ (rmsNorm 0) hid) 0 θ j h')
          (w * M) (w * ηM)
        + fderiv ℝ (fun θ' : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut =>
            suffix (Arch.mlp σ (rmsNorm 0) hid) 0 θ' j (w * M)) θ η = 0 := by
  classical
  have hf : ∀ ℓ, AnalyticOnNhd ℝ ((Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid).f ℓ) Set.univ :=
    fun ℓ => analyticOnNhd_f_mlp hσa ℓ
  -- the rows of `c(r) M` (all rows `r`) are `r M`
  have hrow : ∀ (r : m → ℝ) (N : Matrix m d ℝ) (t : T),
      ((Matrix.of fun (_ : T) => r) * N) t = r ᵥ* N := fun r N t => by
    rw [Matrix.mul_apply_eq_vecMul]
    rfl
  -- (2) the domain: the rows `r` with `r V ≠ 0`, the complement of the kernel `K` of `r ↦ r V`,
  -- which is onto `d → ℝ` (`V` has rank `d`)
  have hsurj : Function.Surjective (Matrix.vecMulLinear (M)) :=
    Matrix.vecMul_surjective_iff_rank_eq_card.2 hM
  obtain ⟨K, hK⟩ : ∃ K : Submodule ℝ (m → ℝ), K = LinearMap.ker (M).vecMulLinear :=
    ⟨_, rfl⟩
  have hmemD : ∀ r, r ∈ (K : Set (m → ℝ))ᶜ ↔ r ᵥ* M ≠ 0 := fun r => by
    rw [hK]
    exact Iff.rfl
  -- it is open (`K` is closed) ...
  have hDo : IsOpen (K : Set (m → ℝ))ᶜ := K.isClosed_of_finiteDimensional.isOpen_compl
  -- ... and connected: the quotient by `K` is `d → ℝ`, of dimension `d ≥ 2`
  have hDc : IsConnected (K : Set (m → ℝ))ᶜ := by
    have hfin : Module.finrank ℝ ((m → ℝ) ⧸ K) = Fintype.card d := by
      rw [hK, (LinearMap.quotKerEquivOfSurjective _ hsurj).finrank_eq,
        Module.finrank_fintype_fun_eq_card]
    refine isConnected_compl_of_one_lt_codim ?_
    rw [← Module.finrank_eq_rank, hfin]
    exact_mod_cast hd
  -- (4, first part) `O` meets the complement of `K`, a proper subspace (dense complement)
  obtain ⟨i₀⟩ : Nonempty d := Fintype.card_pos_iff.1 (by omega)
  obtain ⟨y, hy⟩ := hsurj (fun _ => 1)
  have hKtop : K ≠ ⊤ := fun hKt => by
    have hyK : y ∈ K := hKt ▸ Submodule.mem_top
    rw [hK, LinearMap.mem_ker, hy] at hyK
    exact one_ne_zero (congrFun hyK i₀)
  have hint : interior (K : Set (m → ℝ)) = ∅ := by
    by_contra hcon
    exact hKtop (K.eq_top_of_nonempty_interior' (Set.nonempty_iff_ne_empty.2 hcon))
  obtain ⟨r₁, hr₁O, hr₁D⟩ :=
    (interior_eq_empty_iff_dense_compl.1 hint).inter_open_nonempty O hO hne
  -- (3) on the domain the left side is the joint derivative of `(θ', h') ↦ 𝓑(h')` along
  -- `(η, c(r) η_V)`, at `(θ, c(r) V)`
  have hΦ : ∀ r : m → ℝ, r ᵥ* M ≠ 0 → AnalyticAt ℝ
      (fun p : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut × Matrix T d ℝ =>
        suffix (Arch.mlp σ (rmsNorm 0) hid) 0 p.1 j p.2)
      (θ, (Matrix.of fun (_ : T) => r) * M) := fun r hr =>
    analyticAt_suffix_prod_zero (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) θ rfl hf hθ
      j _ fun t => by rw [hrow]; exact hr
  have hjoint : ∀ r : m → ℝ, r ᵥ* M ≠ 0 →
      fderiv ℝ (fun h' : Matrix T d ℝ => suffix (Arch.mlp σ (rmsNorm 0) hid) 0 θ j h')
          ((Matrix.of fun (_ : T) => r) * M) ((Matrix.of fun (_ : T) => r) * ηM)
        + fderiv ℝ (fun θ' : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut =>
            suffix (Arch.mlp σ (rmsNorm 0) hid) 0 θ' j
              ((Matrix.of fun (_ : T) => r) * M)) θ η
      = fderiv ℝ
          (fun p : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut × Matrix T d ℝ =>
            suffix (Arch.mlp σ (rmsNorm 0) hid) 0 p.1 j p.2)
          (θ, (Matrix.of fun (_ : T) => r) * M)
          (η, (Matrix.of fun (_ : T) => r) * ηM) := fun r hr =>
    fderiv_partial_add_fam
      (Φ := fun θ' h' => suffix (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) 0 θ' j h')
      (hΦ r hr).differentiableAt η _
  -- the joint derivative is analytic in `r` on the domain
  have han : AnalyticOnNhd ℝ (fun r : m → ℝ => fderiv ℝ
      (fun p : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut × Matrix T d ℝ =>
        suffix (Arch.mlp σ (rmsNorm 0) hid) 0 p.1 j p.2)
      (θ, (Matrix.of fun (_ : T) => r) * M)
      (η, (Matrix.of fun (_ : T) => r) * ηM)) (K : Set (m → ℝ))ᶜ := fun r hr => by
    have hg := analyticAt_const (v := θ) |>.prod
      ((LinearMap.toContinuousLinearMap (rowsMulLin_fam T (M))).analyticAt r)
    have hu := analyticAt_const (v := η) |>.prod
      ((LinearMap.toContinuousLinearMap (rowsMulLin_fam T (ηM))).analyticAt r)
    have hc := analyticAt_fderiv_apply_fam hg hu (hΦ r ((hmemD r).1 hr))
    exact hc
  -- (4) the identity theorem: it vanishes near `r₁ ∈ O` (by `h`), so on the connected domain
  have hzero := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero hDc.isPreconnected hr₁D
    (Filter.eventually_of_mem ((hO.inter hDo).mem_nhds ⟨hr₁O, hr₁D⟩)
      fun r hr => ((hjoint r ((hmemD r).1 hr.2)).symm.trans (h r hr.1)))
  have hmain : ∀ r : m → ℝ, r ᵥ* M ≠ 0 →
      fderiv ℝ (fun h' : Matrix T d ℝ => suffix (Arch.mlp σ (rmsNorm 0) hid) 0 θ j h')
          ((Matrix.of fun (_ : T) => r) * M) ((Matrix.of fun (_ : T) => r) * ηM)
        + fderiv ℝ (fun θ' : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut =>
            suffix (Arch.mlp σ (rmsNorm 0) hid) 0 θ' j
              ((Matrix.of fun (_ : T) => r) * M)) θ η = 0 := fun r hr =>
    (hjoint r hr).trans (hzero ((hmemD r).2 hr))
  -- (1) from rows to all hidden states: row `t` at `w` is row `t` at `c(w_t)`
  intro w hw
  funext t
  have hc1 : (Matrix.of fun (_ : T) => (w * M) t)
      = (Matrix.of fun (_ : T) => w t) * M := by
    funext t'
    rw [hrow]
    rfl
  have hc2 : (Matrix.of fun (_ : T) => (w * ηM) t)
      = (Matrix.of fun (_ : T) => w t) * ηM := by
    funext t'
    rw [hrow]
    rfl
  have e1 := fderiv_suffix_zero_row hσa θ hθ j (w * M) (w * ηM) hw t
  have e2 := fderiv_param_suffix_zero_row hσa θ hθ j (w * M) hw η t
  rw [hc1, hc2] at e1
  rw [hc1] at e2
  have e3 := congrFun (hmain (w t) (by rw [← Matrix.mul_apply_eq_vecMul]; exact hw t)) t
  refine (Pi.add_apply _ _ t).trans ?_
  rw [e1, e2]
  exact e3


end Skips
