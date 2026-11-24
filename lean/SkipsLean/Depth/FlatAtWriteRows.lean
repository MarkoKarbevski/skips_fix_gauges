import SkipsLean.Depth.SuffixRows
import SkipsLean.Network.Analytic
import Mathlib.Analysis.Normed.Module.Connected

/-!
# From an open set of rows to all hidden states: the last part of the step on the path

Paper (dimension paper): Appendix D.6 (the case `ε = 0`), proof of Lemma D.18, part (c):
"`𝐃𝓑(w̃V)(w̃ η_V) + 𝐃_θ𝓑(w̃V) η' = 0` for real `w̃` near `s̄`. The left side is real-analytic on the
rows `w̃ ∈ ℝ^{1×q}` with `w̃V ≠ 0`. These form a connected set, the complement of a subspace of
codimension `d_model ≥ 2`, so the identity holds on all of it."

Here `V` is the write of block `k : Fin L` (the paper's block `k + 1`), `𝓑 = 𝓑_{>k+1}` is
`suffix … k.succ`, and a hidden state has the rows `T`. The hypothesis is the identity at the
hidden states with the same row `w̃V` at every token, for `w̃` in a nonempty open set of rows; the
conclusion is the identity at every `w` such that `wV` has no zero row, the hypothesis of Lemma D.3
(`suffixFlatZero_of_flat_at_write`, `Depth/SuffixZeroClaim.lean`). The passage from one row to all
tokens is `Depth/SuffixRows.lean`.
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut] {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)] {σ : ℝ → ℝ}

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: `r ↦ c(r) M`, with `c(r)` the matrix whose rows all equal `r`, as a linear map. -/
private def rowsMulLin_faw {q n : Type*} (m : Type*) [Fintype q] (M : Matrix q n ℝ) :
    (q → ℝ) →ₗ[ℝ] Matrix m n ℝ where
  toFun r := (Matrix.of fun _ : m => r) * M
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
private theorem fderiv_partial_add_faw {E₁ E₂ F : Type*} [NormedAddCommGroup E₁]
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
private theorem analyticAt_fderiv_apply_faw {E F G : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {f : E → F} {g u : G → E} {x : G}
    (hg : AnalyticAt ℝ g x) (hu : AnalyticAt ℝ u x) (hf : AnalyticAt ℝ f (g x)) :
    AnalyticAt ℝ (fun y => fderiv ℝ f (g y) (u y)) x := by
  have h1 := hf.fderiv.comp hg
  have h2 := ((ContinuousLinearMap.id ℝ (E →L[ℝ] F)).analyticAt_bilinear
    (fderiv ℝ f (g x), u x)).comp₂ h1 hu
  exact h2

/-- **Proof of Lemma D.18, part (c):** in the case (0), for real-analytic MLP blocks, `d ≥ 2` and
regular `θ`: if `𝐃𝓑(w̃V)(w̃ η_V) + 𝐃_θ𝓑(w̃V) η = 0` for all rows `w̃` in a nonempty open set (the
same row at every token), then `𝐃𝓑(wV)(w η_V) + 𝐃_θ𝓑(wV) η = 0` for every `w` such that `wV` has
no zero row. -/
theorem flat_at_write_of_isOpen_rows [Nonempty T] (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
    (hθ : RegularZero (Arch.mlp σ (rmsNorm 0) hid) θ) (hd : 2 ≤ Fintype.card d) (k : Fin L)
    (η : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
    (O : Set (hid k → ℝ)) (hO : IsOpen O) (hne : O.Nonempty)
    (h : ∀ r ∈ O,
      fderiv ℝ (fun h' : Matrix T d ℝ => suffix (Arch.mlp σ (rmsNorm 0) hid) 0 θ k.succ h')
          ((Matrix.of fun (_ : T) => r) * θ.write k) ((Matrix.of fun (_ : T) => r) * η.write k)
        + fderiv ℝ (fun θ' : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut =>
            suffix (Arch.mlp σ (rmsNorm 0) hid) 0 θ' k.succ
              ((Matrix.of fun (_ : T) => r) * θ.write k)) θ η = 0) :
    ∀ w : Matrix T (hid k) ℝ, (∀ t, (w * θ.write k) t ≠ 0) →
      fderiv ℝ (fun h' : Matrix T d ℝ => suffix (Arch.mlp σ (rmsNorm 0) hid) 0 θ k.succ h')
          (w * θ.write k) (w * η.write k)
        + fderiv ℝ (fun θ' : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut =>
            suffix (Arch.mlp σ (rmsNorm 0) hid) 0 θ' k.succ (w * θ.write k)) θ η = 0 := by
  classical
  have hf : ∀ ℓ, AnalyticOnNhd ℝ ((Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid).f ℓ) Set.univ :=
    fun ℓ => analyticOnNhd_f_mlp hσa ℓ
  -- the rows of `c(r) M` (all rows `r`) are `r M`
  have hrow : ∀ (r : hid k → ℝ) (M : Matrix (hid k) d ℝ) (t : T),
      ((Matrix.of fun (_ : T) => r) * M) t = r ᵥ* M := fun r M t => by
    rw [Matrix.mul_apply_eq_vecMul]
    rfl
  -- (2) the domain: the rows `r` with `r V ≠ 0`, the complement of the kernel `K` of `r ↦ r V`,
  -- which is onto `d → ℝ` (`V` has rank `d`)
  have hsurj : Function.Surjective (Matrix.vecMulLinear (θ.write k)) :=
    Matrix.vecMul_surjective_iff_rank_eq_card.2 (hθ.rank_write k)
  obtain ⟨K, hK⟩ : ∃ K : Submodule ℝ (hid k → ℝ), K = LinearMap.ker (θ.write k).vecMulLinear :=
    ⟨_, rfl⟩
  have hmemD : ∀ r, r ∈ (K : Set (hid k → ℝ))ᶜ ↔ r ᵥ* θ.write k ≠ 0 := fun r => by
    rw [hK]
    exact Iff.rfl
  -- it is open (`K` is closed) ...
  have hDo : IsOpen (K : Set (hid k → ℝ))ᶜ := K.isClosed_of_finiteDimensional.isOpen_compl
  -- ... and connected: the quotient by `K` is `d → ℝ`, of dimension `d ≥ 2`
  have hDc : IsConnected (K : Set (hid k → ℝ))ᶜ := by
    have hfin : Module.finrank ℝ ((hid k → ℝ) ⧸ K) = Fintype.card d := by
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
  have hint : interior (K : Set (hid k → ℝ)) = ∅ := by
    by_contra hcon
    exact hKtop (K.eq_top_of_nonempty_interior' (Set.nonempty_iff_ne_empty.2 hcon))
  obtain ⟨r₁, hr₁O, hr₁D⟩ :=
    (interior_eq_empty_iff_dense_compl.1 hint).inter_open_nonempty O hO hne
  -- (3) on the domain the left side is the joint derivative of `(θ', h') ↦ 𝓑(h')` along
  -- `(η, c(r) η_V)`, at `(θ, c(r) V)`
  have hΦ : ∀ r : hid k → ℝ, r ᵥ* θ.write k ≠ 0 → AnalyticAt ℝ
      (fun p : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut × Matrix T d ℝ =>
        suffix (Arch.mlp σ (rmsNorm 0) hid) 0 p.1 k.succ p.2)
      (θ, (Matrix.of fun (_ : T) => r) * θ.write k) := fun r hr =>
    analyticAt_suffix_prod_zero (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) θ rfl hf hθ
      k.succ _ fun t => by rw [hrow]; exact hr
  have hjoint : ∀ r : hid k → ℝ, r ᵥ* θ.write k ≠ 0 →
      fderiv ℝ (fun h' : Matrix T d ℝ => suffix (Arch.mlp σ (rmsNorm 0) hid) 0 θ k.succ h')
          ((Matrix.of fun (_ : T) => r) * θ.write k) ((Matrix.of fun (_ : T) => r) * η.write k)
        + fderiv ℝ (fun θ' : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut =>
            suffix (Arch.mlp σ (rmsNorm 0) hid) 0 θ' k.succ
              ((Matrix.of fun (_ : T) => r) * θ.write k)) θ η
      = fderiv ℝ
          (fun p : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut × Matrix T d ℝ =>
            suffix (Arch.mlp σ (rmsNorm 0) hid) 0 p.1 k.succ p.2)
          (θ, (Matrix.of fun (_ : T) => r) * θ.write k)
          (η, (Matrix.of fun (_ : T) => r) * η.write k) := fun r hr =>
    fderiv_partial_add_faw
      (Φ := fun θ' h' => suffix (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) 0 θ' k.succ h')
      (hΦ r hr).differentiableAt η _
  -- the joint derivative is analytic in `r` on the domain
  have han : AnalyticOnNhd ℝ (fun r : hid k → ℝ => fderiv ℝ
      (fun p : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut × Matrix T d ℝ =>
        suffix (Arch.mlp σ (rmsNorm 0) hid) 0 p.1 k.succ p.2)
      (θ, (Matrix.of fun (_ : T) => r) * θ.write k)
      (η, (Matrix.of fun (_ : T) => r) * η.write k)) (K : Set (hid k → ℝ))ᶜ := fun r hr => by
    have hg := analyticAt_const (v := θ) |>.prod
      ((LinearMap.toContinuousLinearMap (rowsMulLin_faw T (θ.write k))).analyticAt r)
    have hu := analyticAt_const (v := η) |>.prod
      ((LinearMap.toContinuousLinearMap (rowsMulLin_faw T (η.write k))).analyticAt r)
    have hc := analyticAt_fderiv_apply_faw hg hu (hΦ r ((hmemD r).1 hr))
    exact hc
  -- (4) the identity theorem: it vanishes near `r₁ ∈ O` (by `h`), so on the connected domain
  have hzero := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero hDc.isPreconnected hr₁D
    (Filter.eventually_of_mem ((hO.inter hDo).mem_nhds ⟨hr₁O, hr₁D⟩)
      fun r hr => ((hjoint r ((hmemD r).1 hr.2)).symm.trans (h r hr.1)))
  have hmain : ∀ r : hid k → ℝ, r ᵥ* θ.write k ≠ 0 →
      fderiv ℝ (fun h' : Matrix T d ℝ => suffix (Arch.mlp σ (rmsNorm 0) hid) 0 θ k.succ h')
          ((Matrix.of fun (_ : T) => r) * θ.write k) ((Matrix.of fun (_ : T) => r) * η.write k)
        + fderiv ℝ (fun θ' : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut =>
            suffix (Arch.mlp σ (rmsNorm 0) hid) 0 θ' k.succ
              ((Matrix.of fun (_ : T) => r) * θ.write k)) θ η = 0 := fun r hr =>
    (hjoint r hr).trans (hzero ((hmemD r).2 hr))
  -- (1) from rows to all hidden states: row `t` at `w` is row `t` at `c(w_t)`
  intro w hw
  funext t
  have hc1 : (Matrix.of fun (_ : T) => (w * θ.write k) t)
      = (Matrix.of fun (_ : T) => w t) * θ.write k := by
    funext t'
    rw [hrow]
    rfl
  have hc2 : (Matrix.of fun (_ : T) => (w * η.write k) t)
      = (Matrix.of fun (_ : T) => w t) * η.write k := by
    funext t'
    rw [hrow]
    rfl
  have e1 := fderiv_suffix_zero_row hσa θ hθ k.succ (w * θ.write k) (w * η.write k) hw t
  have e2 := fderiv_param_suffix_zero_row hσa θ hθ k.succ (w * θ.write k) hw η t
  rw [hc1, hc2] at e1
  rw [hc1] at e2
  have e3 := congrFun (hmain (w t) (by rw [← Matrix.mul_apply_eq_vecMul]; exact hw t)) t
  refine (Pi.add_apply _ _ t).trans ?_
  rw [e1, e2]
  exact e3

end Skips
