import SkipsLean.Depth.SuffixRows
import SkipsLean.Depth.SuffixZeroClaim

/-!
# Homogeneity of `𝓑_{>k}` in the case `ε = 0`, and a direction that `𝐃𝓑_{>k}` kills on an open set

Paper (dimension paper): Appendix D.3 in the case (0) and Appendix D.6. Under pre-RMSNorm with
`ε = 0`, `𝓑_{>k}(λh) = 𝓑_{>k}(h)` for `λ > 0`; so `𝐃𝓑_{>k}(h) h = 0` (the source of (15)) and "a
derivative of order `i` of `𝓑` is homogeneous of degree `−i`" (proof of Lemma D.19). The proof of
Lemma D.19 then uses Lemma D.2 in this form (Steps 2 and 4): "By (P1), `a_j ≠ 0`, so by Lemma D.2
`𝐃𝓑(n W V) a_j ≠ 0` on an open dense set of `n`", and "`η°a_j` is a multiple of `n W V` for an open
set of rows `n`, so `η°a_j = 0`".

Stated here, for regular `θ` and hidden states without a zero row: `𝐃𝓑_{>j}(ch)(cv) = 𝐃𝓑_{>j}(h)v`
and `𝐃_θ𝓑_{>j}(ch) = 𝐃_θ𝓑_{>j}(h)` for `c > 0`; `𝐃𝓑_{>j}(h) h = 0`; and, for MLP blocks, `d ≥ 2`
and an invertible matrix `M`: if `𝐃𝓑_{>j}(xM)(a) = 0` for the rows `x` of a nonempty open set (the
same rows `xM` and `a` at every token), then `a = 0`.
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]

section General

variable (A : Arch T d L) (θ : Params A dIn dOut)

/-- Helper: `𝓑_{>j}` has the derivative `fderiv` at every hidden state without a zero row. -/
private theorem hasFDerivAt_suffix_zero_szr (hχ : A.χ = rmsNorm 0)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (hθ : RegularZero A θ) (j : Fin (L + 1))
    (h₀ : Matrix T d ℝ) (hh₀ : ∀ t, h₀ t ≠ 0) :
    HasFDerivAt (fun h' : Matrix T d ℝ => suffix A 0 θ j h')
      (fderiv ℝ (fun h' : Matrix T d ℝ => suffix A 0 θ j h') h₀) h₀ := by
  have hA := (analyticAt_suffix_prod_zero A θ hχ hf hθ j h₀ hh₀).differentiableAt
  have hc := hA.hasFDerivAt.comp h₀ (hasFDerivAt_prodMk_right (𝕜 := ℝ) θ h₀)
  exact hc.differentiableAt.hasFDerivAt

/-- **"A derivative of order `1` of `𝓑` is homogeneous of degree `−1`":**
`𝐃𝓑_{>j}(ch)(cv) = 𝐃𝓑_{>j}(h)v` for `c > 0`, regular `θ` and `h` without a zero row. -/
theorem fderiv_suffix_zero_smul (hχ : A.χ = rmsNorm 0)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (hθ : RegularZero A θ) (j : Fin (L + 1))
    (h v : Matrix T d ℝ) (hh : ∀ t, h t ≠ 0) {c : ℝ} (hc : 0 < c) :
    fderiv ℝ (fun h' : Matrix T d ℝ => suffix A 0 θ j h') (c • h) (c • v)
      = fderiv ℝ (fun h' : Matrix T d ℝ => suffix A 0 θ j h') h v := by
  set B := fun h' : Matrix T d ℝ => suffix A 0 θ j h' with hB
  -- `𝓑_{>j}` is differentiable at every hidden state without a zero row
  have hd : ∀ h₀ : Matrix T d ℝ, (∀ s, h₀ s ≠ 0) → HasFDerivAt B (fderiv ℝ B h₀) h₀ :=
    hasFDerivAt_suffix_zero_szr A θ hχ hf hθ j
  -- the scaling `S = c • id`, and `𝓑_{>j} ∘ S = 𝓑_{>j}`
  let S : Matrix T d ℝ →L[ℝ] Matrix T d ℝ := c • ContinuousLinearMap.id ℝ (Matrix T d ℝ)
  have hfac : B ∘ ⇑S = B := funext fun h' =>
    suffix_zero_smul_rows A θ hχ j h' (fun _ => c) fun _ => hc
  -- the chain rule at `h` through `S`, and uniqueness of the derivative
  have h1 := (hd (S h) fun t => smul_ne_zero hc.ne' (hh t)).comp h S.hasFDerivAt
  rw [hfac] at h1
  have e := DFunLike.congr_fun (h1.unique (hd h hh)) v
  exact e

/-- **`𝐃𝓑_{>j}(h) h = 0`** for regular `θ` and `h` without a zero row (the derivative at `c = 1` of
`𝓑_{>j}(ch) = 𝓑_{>j}(h)`). -/
theorem fderiv_suffix_zero_apply_self (hχ : A.χ = rmsNorm 0)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (hθ : RegularZero A θ) (j : Fin (L + 1))
    (h : Matrix T d ℝ) (hh : ∀ t, h t ≠ 0) :
    fderiv ℝ (fun h' : Matrix T d ℝ => suffix A 0 θ j h') h h = 0 := by
  set B := fun h' : Matrix T d ℝ => suffix A 0 θ j h' with hB
  -- the curve `τ ↦ 𝓑_{>j}((1 + τ) h)` has the derivative `𝐃𝓑_{>j}(h) h` at `0`
  have hγ : HasDerivAt (fun τ : ℝ => (1 + τ) • h) ((1 : ℝ) • h) 0 :=
    ((hasDerivAt_id (0 : ℝ)).const_add 1).smul_const h
  have h1 := (hasFDerivAt_suffix_zero_szr A θ hχ hf hθ j h hh).comp_hasDerivAt_of_eq (0 : ℝ) hγ
    (by rw [add_zero, one_smul])
  -- and it is constant near `0`, since `1 + τ > 0` there
  have hconst : (B ∘ fun τ : ℝ => (1 + τ) • h) =ᶠ[nhds 0] fun _ => B h := by
    filter_upwards [Ioi_mem_nhds (show (-1 : ℝ) < 0 by norm_num)] with τ hτ
    exact suffix_zero_smul_rows A θ hχ j h (fun _ => 1 + τ) fun _ => by
      rw [Set.mem_Ioi] at hτ; linarith
  have h2 := (hasDerivAt_const (0 : ℝ) (B h)).congr_of_eventuallyEq hconst
  have e := h1.unique h2
  rw [one_smul] at e
  exact e

/-- **`𝐃_θ𝓑_{>j}(ch) = 𝐃_θ𝓑_{>j}(h)`** for `c > 0`. -/
theorem fderiv_param_suffix_zero_smul (hχ : A.χ = rmsNorm 0) (j : Fin (L + 1))
    (h : Matrix T d ℝ) (η : Params A dIn dOut) {c : ℝ} (hc : 0 < c) :
    fderiv ℝ (fun θ' : Params A dIn dOut => suffix A 0 θ' j (c • h)) θ η
      = fderiv ℝ (fun θ' : Params A dIn dOut => suffix A 0 θ' j h) θ η := by
  -- the two maps of `θ'` are equal
  have e : (fun θ' : Params A dIn dOut => suffix A 0 θ' j (c • h))
      = fun θ' : Params A dIn dOut => suffix A 0 θ' j h :=
    funext fun θ' => suffix_zero_smul_rows A θ' hχ j h (fun _ => c) fun _ => hc
  rw [e]

end General

variable {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)] {σ : ℝ → ℝ}

omit [DecidableEq d] in
/-- Helper (as `exists_not_smul_zc`, private in `Depth/SuffixZeroClaim.lean`): if `d` has at
least two elements, every row `v` has a row `e` that is not a multiple of `v`. -/
private theorem exists_not_smul_szr (hd : 2 ≤ Fintype.card d) (v : d → ℝ) :
    ∃ e : d → ℝ, ∀ c : ℝ, e ≠ c • v := by
  classical
  obtain ⟨i, j, hij⟩ := Fintype.exists_pair_of_one_lt_card (by omega : 1 < Fintype.card d)
  by_contra hcon
  push Not at hcon
  obtain ⟨a, ha⟩ := hcon (Pi.single i 1)
  obtain ⟨b, hb⟩ := hcon (Pi.single j 1)
  have h1 := congrFun ha i
  have h2 := congrFun ha j
  have h3 := congrFun hb j
  simp only [Pi.single_eq_same, Pi.single_eq_of_ne hij.symm, Pi.smul_apply, smul_eq_mul] at h1 h2 h3
  have ha0 : a = 0 := by linear_combination a * h3 - b * h2
  rw [ha0, zero_mul] at h1
  exact one_ne_zero h1

omit [Fintype d] [DecidableEq d] in
/-- Helper (as `eq_zero_of_smul_of_smul_zc`, private in `Depth/SuffixZeroClaim.lean`): a row `r`
that is a multiple of `v` and of `v + s e` (`s ≠ 0`, `e` not a multiple of `v`) is `0`. -/
private theorem eq_zero_of_smul_of_smul_szr {r v e : d → ℝ} (he : ∀ c : ℝ, e ≠ c • v) {s a b : ℝ}
    (hs : s ≠ 0) (ha : r = a • v) (hb : r = b • (v + s • e)) : r = 0 := by
  by_cases hb0 : b = 0
  · rw [hb, hb0, zero_smul]
  · exfalso
    -- `a v = b v + b s e`, so `e = ((a - b) / (b s)) v`
    have h1 : (b * s) • e = (a - b) • v := by
      rw [sub_smul, ← ha, hb, smul_add, smul_smul]
      abel
    apply he ((a - b) / (b * s))
    rw [div_eq_mul_inv, mul_comm (a - b), mul_smul, ← h1, smul_smul,
      inv_mul_cancel₀ (mul_ne_zero hb0 hs), one_smul]

omit [Fintype T] [Fintype d] [DecidableEq d] in
/-- Helper: a point `g` of an open set `U` of hidden states and a direction `E` give a `δ ≠ 0`
with `g + δ E ∈ U`. -/
private theorem exists_line_mem_szr {U : Set (Matrix T d ℝ)} (hU : IsOpen U) {g : Matrix T d ℝ}
    (hg : g ∈ U) (E : Matrix T d ℝ) : ∃ δ : ℝ, δ ≠ 0 ∧ g + δ • E ∈ U := by
  have hc : Continuous fun s : ℝ => g + s • E := by fun_prop
  have hn : (fun s : ℝ => g + s • E) ⁻¹' U ∈ nhds (0 : ℝ) :=
    hc.continuousAt.preimage_mem_nhds (by simpa using hU.mem_nhds hg)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hn
  refine ⟨ε / 2, by positivity, hball ?_⟩
  rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (by positivity)]
  linarith

/-- **Lemma D.2 on an open set of rows:** for real-analytic MLP blocks in the case (0), `d ≥ 2`,
regular `θ` and an invertible matrix `M`: if `𝐃𝓑_{>j}(xM)(a) = 0` for every row `x` of a nonempty
open set (the row `xM` and the row `a` at every token), then `a = 0`. -/
theorem eq_zero_of_fderiv_suffix_zero_eq_zero_rows [Nonempty T]
    (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
    (hθ : RegularZero (Arch.mlp σ (rmsNorm 0) hid) θ) (hd : 2 ≤ Fintype.card d)
    (j : Fin (L + 1)) (M : Matrix d d ℝ) (hM : IsUnit M.det)
    (N : Set (d → ℝ)) (hN : IsOpen N) (hNne : N.Nonempty) (a : d → ℝ)
    (h : ∀ x ∈ N,
      fderiv ℝ (fun h' : Matrix T d ℝ => suffix (Arch.mlp σ (rmsNorm 0) hid) 0 θ j h')
        ((Matrix.of fun (_ : T) => x) * M) (Matrix.of fun (_ : T) => a) = 0) :
    a = 0 := by
  classical
  obtain ⟨t₀⟩ := ‹Nonempty T›
  have hf : ∀ ℓ, AnalyticOnNhd ℝ ((Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid).f ℓ) Set.univ :=
    fun ℓ => analyticOnNhd_f_mlp hσa ℓ
  -- the open dense set `U` of Lemma D.2
  obtain ⟨U, hUo, hUd, hU0, -, hUk⟩ := exists_open_dense_fderiv_suffix_zero
    (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) θ rfl hf hθ hd j
  -- the open set `R = {xM | x ∈ N}` of rows, the preimage of `N` under `r ↦ r M⁻¹`
  obtain ⟨R, hRdef⟩ : ∃ R : Set (d → ℝ), R = (fun r => r ᵥ* M⁻¹) ⁻¹' N := ⟨_, rfl⟩
  have hRo : IsOpen R := by
    rw [hRdef]
    exact hN.preimage (continuous_id.matrix_vecMul continuous_const)
  have hRM : ∀ r : d → ℝ,
      (Matrix.of fun (_ : T) => r ᵥ* M⁻¹) * M = Matrix.of fun (_ : T) => r := by
    intro r
    refine funext fun t => ?_
    rw [Matrix.mul_apply_eq_vecMul]
    show r ᵥ* M⁻¹ ᵥ* M = r
    rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul M hM, Matrix.vecMul_one]
  -- (iii) for `g ∈ U` with `g t₀ ∈ R`, `a` is a multiple of `g t₀`: with `v` the matrix with the
  -- row `a` at `t₀` and `0` elsewhere, `𝐃𝓑_{>j}(g) v = 0` row by row, then Lemma D.2
  have hmul : ∀ g ∈ U, g t₀ ∈ R → ∃ b : ℝ, a = b • g t₀ := by
    intro g hgU hgR
    rw [hRdef] at hgR
    obtain ⟨v, hv⟩ : ∃ v : Matrix T d ℝ, v = Pi.single (M := fun _ : T => d → ℝ) t₀ a :=
      ⟨_, rfl⟩
    have hzero : fderiv ℝ (fun h' : Matrix T d ℝ =>
        suffix (Arch.mlp σ (rmsNorm 0) hid) 0 θ j h') g v = 0 := by
      refine funext fun t => ?_
      rw [fderiv_suffix_zero_row hσa θ hθ j g v (hU0 g hgU) t]
      by_cases ht : t = t₀
      · rw [ht]
        have e1 : (Matrix.of fun _ : T => v t₀) = Matrix.of fun _ : T => a := by
          rw [hv, Pi.single_eq_same]
        rw [e1, ← hRM (g t₀), h _ hgR]
      · have e1 : (Matrix.of fun _ : T => v t) = 0 := by
          rw [hv, Pi.single_eq_of_ne ht]
          rfl
        rw [e1, map_zero]
    obtain ⟨b, hb⟩ := hUk g hgU v hzero t₀
    refine ⟨b, ?_⟩
    rw [← hb, hv, Pi.single_eq_same]
  -- a point `g₀ ∈ U` with `g₀ t₀ ∈ R` (`U` is dense)
  obtain ⟨x₀, hx₀⟩ := hNne
  have hW : IsOpen {g : Matrix T d ℝ | g t₀ ∈ R} := hRo.preimage (continuous_apply t₀)
  have hWne : {g : Matrix T d ℝ | g t₀ ∈ R}.Nonempty := by
    refine ⟨Matrix.of fun _ => x₀ ᵥ* M, ?_⟩
    show x₀ ᵥ* M ∈ R
    rw [hRdef]
    show x₀ ᵥ* M ᵥ* M⁻¹ ∈ N
    rw [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv M hM, Matrix.vecMul_one]
    exact hx₀
  obtain ⟨g₀, hg₀W, hg₀U⟩ := dense_iff_inter_open.1 hUd _ hW hWne
  -- (iv) a row `e` not a multiple of `g₀ t₀`, and `δ ≠ 0` with `g₀ + δ E ∈ U` and
  -- `(g₀ + δ E) t₀ = g₀ t₀ + δ e ∈ R`; `a` is a multiple of both rows, so `a = 0`
  obtain ⟨e, he⟩ := exists_not_smul_szr hd (g₀ t₀)
  obtain ⟨E, hE⟩ : ∃ E : Matrix T d ℝ, E = Pi.single (M := fun _ : T => d → ℝ) t₀ e :=
    ⟨_, rfl⟩
  obtain ⟨δ, hδ, hδU, hδW⟩ := exists_line_mem_szr (hUo.inter hW) ⟨hg₀U, hg₀W⟩ E
  obtain ⟨b₁, hb₁⟩ := hmul g₀ hg₀U hg₀W
  obtain ⟨b₂, hb₂⟩ := hmul _ hδU hδW
  have hrow : (g₀ + δ • E) t₀ = g₀ t₀ + δ • e := by
    have e1 : (g₀ + δ • E) t₀ = g₀ t₀ + δ • E t₀ := rfl
    rw [e1, hE, Pi.single_eq_same]
  rw [hrow] at hb₂
  exact eq_zero_of_smul_of_smul_szr he hδ hb₁ hb₂

omit [Fintype d] [DecidableEq d] in
/-- Helper: a point `x₀` of an open set `N` of rows and a direction `y` give a `δ ≠ 0` with
`x₀ + k δ y ∈ N` for `k = 1, 2, 3`. -/
private theorem exists_three_mem_szr {N : Set (d → ℝ)} (hN : IsOpen N) {x₀ : d → ℝ}
    (h0 : x₀ ∈ N) (y : d → ℝ) :
    ∃ δ : ℝ, δ ≠ 0 ∧ x₀ + δ • y ∈ N ∧ x₀ + (2 * δ) • y ∈ N ∧ x₀ + (3 * δ) • y ∈ N := by
  have hc : Continuous fun s : ℝ => x₀ + s • y := by fun_prop
  have hn : (fun s : ℝ => x₀ + s • y) ⁻¹' N ∈ nhds (0 : ℝ) :=
    hc.continuousAt.preimage_mem_nhds (by simpa using hN.mem_nhds h0)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hn
  have hmem : ∀ s : ℝ, 0 < s → s < ε → x₀ + s • y ∈ N := fun s hs hsε => hball (by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hs]
    exact hsε)
  exact ⟨ε / 4, by positivity, hmem _ (by positivity) (by linarith),
    hmem _ (by positivity) (by linarith), hmem _ (by positivity) (by linarith)⟩

omit [DecidableEq d] in
/-- Helper: the cubic identity `(x ⬝ x)(x ⬝ u) = (x Z xᵀ)(x ⬝ c)` on a nonempty open set of rows
holds for every row: the third difference of the cubic `s ↦ P(x₀ + s y)` with the step `δ` is
`6 δ³ P(y)`. -/
private theorem cubic_eq_szr (Z : Matrix d d ℝ) (u c : d → ℝ) (N : Set (d → ℝ))
    (hN : IsOpen N) (hNne : N.Nonempty)
    (h : ∀ x ∈ N, (x ⬝ᵥ x) * (x ⬝ᵥ u) = ((x ᵥ* Z) ⬝ᵥ x) * (x ⬝ᵥ c)) (y : d → ℝ) :
    (y ⬝ᵥ y) * (y ⬝ᵥ u) = ((y ᵥ* Z) ⬝ᵥ y) * (y ⬝ᵥ c) := by
  obtain ⟨x₀, h0⟩ := hNne
  obtain ⟨δ, hδ, h1, h2, h3⟩ := exists_three_mem_szr hN h0 y
  have e0 := h _ h0
  have e1 := h _ h1
  have e2 := h _ h2
  have e3 := h _ h3
  simp only [Matrix.add_vecMul, Matrix.smul_vecMul, add_dotProduct, dotProduct_add,
    smul_dotProduct, dotProduct_smul, smul_eq_mul] at e1 e2 e3
  have key : δ ^ 3 * ((y ⬝ᵥ y) * (y ⬝ᵥ u) - ((y ᵥ* Z) ⬝ᵥ y) * (y ⬝ᵥ c)) = 0 := by
    linear_combination (e3 - 3 * e2 + 3 * e1 - e0) / 6
  have := (mul_eq_zero.1 key).resolve_left (pow_ne_zero 3 hδ)
  linarith

/-- **From `ż_j(n) = 0` on an open set to `Z`** (proof of Lemma D.19, Step 2: "that is, by (20),
`‖n‖² n (Z c_j + η_{c_j}) = ⟨nZ, n⟩ n c_j` on an open cone of rows `n`, hence for all `n`. For
`n` orthogonal to `c_j` this gives `n (Z c_j + η_{c_j}) = 0`, so `Z c_j + η_{c_j} = β_k c_j` for a
number `β_k`, and then `⟨nZ, n⟩ = β_k ‖n‖²` for all `n`. So `Z = Y_k + β_k I` with `Y_k`
antisymmetric"): if
`(x ⬝ x)(x ⬝ u) = (x Z xᵀ)(x ⬝ c)` for the rows `x` of a nonempty open set and `c ≠ 0`, then
`u = β c` and `Z − β I` is antisymmetric, for a number `β`. -/
theorem exists_smul_of_quadratic_rows (Z : Matrix d d ℝ) (u c : d → ℝ) (hc : c ≠ 0)
    (N : Set (d → ℝ)) (hN : IsOpen N) (hNne : N.Nonempty)
    (h : ∀ x ∈ N, (x ⬝ᵥ x) * (x ⬝ᵥ u) = ((x ᵥ* Z) ⬝ᵥ x) * (x ⬝ᵥ c)) :
    ∃ β : ℝ, u = β • c ∧ Z - β • (1 : Matrix d d ℝ) ∈ antisymmetric d := by
  -- the identity holds for every row `x`
  have hall := cubic_eq_szr Z u c N hN hNne h
  have hcc : c ⬝ᵥ c ≠ 0 := fun h0 => hc (dotProduct_self_eq_zero.1 h0)
  -- `u = β c` with `β = ⟨u, c⟩ / ⟨c, c⟩`: `w = u − β c` has `⟨w, c⟩ = 0`, so `‖w‖⁴ = 0`
  obtain ⟨β, hβ⟩ : ∃ β : ℝ, β = (u ⬝ᵥ c) / (c ⬝ᵥ c) := ⟨_, rfl⟩
  have hu : u = β • c := by
    obtain ⟨w, hw⟩ : ∃ w : d → ℝ, w = u - β • c := ⟨_, rfl⟩
    have hwc : w ⬝ᵥ c = 0 := by
      rw [hw, sub_dotProduct, smul_dotProduct, smul_eq_mul, hβ, div_mul_cancel₀ _ hcc, sub_self]
    have hwu : w ⬝ᵥ u = w ⬝ᵥ w := by
      have hu' : u = w + β • c := by rw [hw, sub_add_cancel]
      rw [hu', dotProduct_add, dotProduct_smul, smul_eq_mul, hwc, mul_zero, add_zero]
    have e := hall w
    rw [hwc, mul_zero, hwu, mul_self_eq_zero, dotProduct_self_eq_zero] at e
    rw [← sub_eq_zero, ← hw, e]
  -- `⟨xZ, x⟩ = β ‖x‖²` for every row `x`: directly where `⟨x, c⟩ ≠ 0`, and from the quadratic
  -- `s ↦ ⟨yZ, y⟩ − β ‖y‖²` at `y = x + s c`, `s = 1, −1, 2`, where `⟨x, c⟩ = 0`
  have hq0 : ∀ x : d → ℝ, x ⬝ᵥ c ≠ 0 → (x ᵥ* Z) ⬝ᵥ x = β * (x ⬝ᵥ x) := by
    intro x hx
    have e := hall x
    rw [hu, dotProduct_smul, smul_eq_mul] at e
    apply mul_right_cancel₀ hx
    linear_combination -e
  have hq : ∀ x : d → ℝ, (x ᵥ* Z) ⬝ᵥ x = β * (x ⬝ᵥ x) := by
    intro x
    by_cases hx : x ⬝ᵥ c = 0
    · have key : ∀ s : ℝ, s ≠ 0 →
          ((x + s • c) ᵥ* Z) ⬝ᵥ (x + s • c) = β * ((x + s • c) ⬝ᵥ (x + s • c)) := by
        intro s hs
        refine hq0 _ ?_
        rw [add_dotProduct, hx, smul_dotProduct, smul_eq_mul, zero_add]
        exact mul_ne_zero hs hcc
      have k1 := key 1 one_ne_zero
      have k2 := key (-1) (by norm_num)
      have k3 := key 2 two_ne_zero
      simp only [Matrix.add_vecMul, Matrix.smul_vecMul, add_dotProduct, dotProduct_add,
        smul_dotProduct, dotProduct_smul, smul_eq_mul] at k1 k2 k3
      linear_combination k1 + k2 / 3 - k3 / 3
    · exact hq0 x hx
  -- `Q = Z − β I` has `x Q xᵀ = 0` for every `x`; by polarization `Qᵀ = −Q`
  obtain ⟨Q, hQ⟩ : ∃ Q : Matrix d d ℝ, Q = Z - β • (1 : Matrix d d ℝ) := ⟨_, rfl⟩
  have hQ0 : ∀ x : d → ℝ, (x ᵥ* Q) ⬝ᵥ x = 0 := by
    intro x
    rw [hQ, Matrix.vecMul_sub, Matrix.vecMul_smul, Matrix.vecMul_one, sub_dotProduct,
      smul_dotProduct, smul_eq_mul, hq x, sub_self]
  have hpol : ∀ x y : d → ℝ, (x ᵥ* Q) ⬝ᵥ y + (y ᵥ* Q) ⬝ᵥ x = 0 := by
    intro x y
    have e := hQ0 (x + y)
    simp only [Matrix.add_vecMul, add_dotProduct, dotProduct_add] at e
    linear_combination e - hQ0 x - hQ0 y
  refine ⟨β, hu, ?_⟩
  rw [← hQ]
  show Qᵀ = -Q
  ext a b
  have e := hpol (Pi.single b 1) (Pi.single a 1)
  simp only [Matrix.single_one_vecMul, dotProduct_single, mul_one, Matrix.row] at e
  rw [Matrix.transpose_apply, Matrix.neg_apply]
  linear_combination e

end Skips
