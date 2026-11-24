import SkipsLean.Depth.SuffixZeroDeriv
import SkipsLean.Dimension.UpperBoundRMSNormZero

/-!
# The case (0): a direction at a write, and the claim gives the rank

Paper (dimension paper): Appendix D.3 in the case (0), pre-RMSNorm with `ε = 0`.

Lemma D.3 (A direction at a write): "Let `θ` be regular, `0 ≤ k ≤ L`, and let `A` be a matrix with
`d` columns and rank `d`. Let `η_A` be a matrix of the size of `A` and `η` a direction of the
weights of the blocks `k + 1, …, L` and of `D`. If `𝐃𝓑_{>k}(wA)(w η_A) + 𝐃_θ𝓑_{>k}(wA) η = 0` for
all rows `w`, with `wA ≠ 0` in the case (0), then `η_A = AZ` for a `d × d` matrix `Z`, and (16)
holds."

Proposition D.4 (The claim gives the rank): "Let `θ` be regular […] and let `(D_0)` hold at `θ`.
Then the directions `η` with `𝐃_θ F(θ, x) η = 0` for all `x`, with `xE ≠ 0` in the case (0), are
the directions `η^Z` of (11) […], and the Jacobian of the network has the rank (13) on some finite
batch of such inputs." In the case (0) the directions of the symmetries are
`cobDir θ Y + scaleDir θ β` with antisymmetric `Y_0, …, Y_L` and numbers `β_0, …, β_L`
(`Dimension/UpperBoundRMSNormZero.lean`), and the rank is `P − (L + 1)(d(d−1)/2 + 1)`.

A hidden state has the rows `T`; "`≠ 0`" is "no row vanishes". The Lean `flat` and `funDim` use
every input: at an input where the output is not differentiable in the parameters Lean takes the
derivative to be `0`, which asks nothing of a direction.
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable (A : Arch T d L) (θ : Params A dIn dOut)

omit [Fintype T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: if `d` has at least two elements, every row `v` has a row `e` that is not a multiple
of `v` (one of two unit rows `e_i`, `e_j`: if both were multiples of `v`, then `v_j ≠ 0` and
`e_i = a v` with `a v_j = 0`, so `a = 0`, against `a v_i = 1`). -/
private theorem exists_not_smul_zc (hd : 2 ≤ Fintype.card d) (v : d → ℝ) :
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

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: a row `r` that is a multiple of `v` and of `v + s e` (`s ≠ 0`, `e` not a multiple of
`v`) is `0`. -/
private theorem eq_zero_of_smul_of_smul_zc {r v e : d → ℝ} (he : ∀ c : ℝ, e ≠ c • v) {s a b : ℝ}
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

/-- **Lemma D.3 of the dimension paper (a direction at a write), the case (0):** let the blocks be
real-analytic, `d ≥ 2`, `θ` regular, and `M` a matrix with `d` columns and rank `d`. If
`𝐃𝓑_{>k}(wM)(w η_M) + 𝐃_θ𝓑_{>k}(wM) η = 0` for all `w` such that `wM` has no zero row, then
`η_M = M Z` for a matrix `Z`, and the identity (16) holds for `k`, `Z` and `η`. -/
theorem suffixFlatZero_of_flat_at_write [Nonempty T] (hχ : A.χ = rmsNorm 0)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (hθ : RegularZero A θ)
    (hd : 2 ≤ Fintype.card d) (k : Fin (L + 1))
    {m : Type*} [Fintype m] (M : Matrix m d ℝ) (hM : M.rank = Fintype.card d)
    (ηM : Matrix m d ℝ) (η : Params A dIn dOut)
    (h : ∀ w : Matrix T m ℝ, (∀ t, (w * M) t ≠ 0) →
      fderiv ℝ (fun h' : Matrix T d ℝ => suffix A 0 θ k h') (w * M) (w * ηM)
        + fderiv ℝ (fun θ' : Params A dIn dOut => suffix A 0 θ' k (w * M)) θ η = 0) :
    ∃ Z : Matrix d d ℝ, ηM = M * Z ∧ SuffixFlatZero A θ k Z η := by
  classical
  -- a left inverse `M⁺` of `M` (rank `d`)
  obtain ⟨Mp, hMp⟩ : ∃ B : Matrix d m ℝ, B * M = 1 :=
    Matrix.vecMul_surjective_iff_exists_left_inverse.1
      (Matrix.vecMul_surjective_iff_rank_eq_card.2 hM)
  -- the open dense set `U` of Lemma D.2 for `k`
  obtain ⟨U, hUo, hUd, hU0, -, hU⟩ := exists_open_dense_fderiv_suffix_zero A θ hχ hf hθ hd k
  -- (i) if `w₁ M = 0` and `h₀ ∈ U`, every row of `w₁ η_M` is a multiple of the same row of `h₀`:
  -- subtract the hypothesis at `h₀ M⁺` from the one at `h₀ M⁺ + w₁`, two preimages of `h₀`
  have hpar : ∀ w₁ : Matrix T m ℝ, w₁ * M = 0 →
      ∀ h₀ ∈ U, ∀ t, ∃ a : ℝ, (w₁ * ηM) t = a • h₀ t := by
    intro w₁ hw₁ h₀ hh₀
    have hw₀ : h₀ * Mp * M = h₀ := by rw [Matrix.mul_assoc, hMp, Matrix.mul_one]
    have hw₂ : (h₀ * Mp + w₁) * M = h₀ := by rw [Matrix.add_mul, hw₁, add_zero, hw₀]
    have e₀ := h (h₀ * Mp) (by rw [hw₀]; exact hU0 h₀ hh₀)
    have e₁ := h (h₀ * Mp + w₁) (by rw [hw₂]; exact hU0 h₀ hh₀)
    rw [hw₀] at e₀
    rw [hw₂, Matrix.add_mul, map_add, add_right_comm, e₀, zero_add] at e₁
    exact hU h₀ hh₀ _ e₁
  -- (ii) so `w₁ M = 0` implies `w₁ η_M = 0`: row `t` of `w₁ η_M` is a multiple of row `t` of
  -- `h₀ ∈ U` and of `h₀ + s E ∈ U` (small `s ≠ 0`), whose row `t` is `h₀_t + s e` with `e` not a
  -- multiple of `h₀_t` (`d ≥ 2`)
  have hker : ∀ w₁ : Matrix T m ℝ, w₁ * M = 0 → w₁ * ηM = 0 := by
    intro w₁ hw₁
    obtain ⟨h₀, hh₀⟩ := hUd.nonempty
    funext t
    obtain ⟨e, he⟩ := exists_not_smul_zc hd (h₀ t)
    let E : Matrix T d ℝ := Matrix.of fun t' i => if t' = t then e i else 0
    have hrow : ∀ s : ℝ, (h₀ + s • E) t = h₀ t + s • e := by
      intro s
      funext i
      simp only [smul_of, Matrix.add_apply, of_apply, Pi.smul_apply, ↓reduceIte, smul_eq_mul,
        Pi.add_apply, E]
    -- for small `s ≠ 0`, `h₀ + s E ∈ U` (`U` is open)
    have hcont : Continuous fun s : ℝ => h₀ + s • E :=
      continuous_const.add (continuous_id.smul continuous_const)
    have hev : ∀ᶠ s in nhdsWithin (0 : ℝ) {0}ᶜ, h₀ + s • E ∈ U ∧ s ≠ 0 := by
      refine Filter.Eventually.and (nhdsWithin_le_nhds (hcont.continuousAt.preimage_mem_nhds ?_))
        self_mem_nhdsWithin
      show U ∈ nhds (h₀ + (0 : ℝ) • E)
      rw [zero_smul, add_zero]
      exact hUo.mem_nhds hh₀
    obtain ⟨s, hsU, hs0⟩ := hev.exists
    obtain ⟨a, ha⟩ := hpar w₁ hw₁ h₀ hh₀ t
    obtain ⟨b, hb⟩ := hpar w₁ hw₁ _ hsU t
    rw [hrow] at hb
    exact eq_zero_of_smul_of_smul_zc he hs0 ha hb
  -- (iii) every row of `(1 - M M⁺) η_M` vanishes (`1 - M M⁺` kills `M`; take `w` with equal rows)
  obtain ⟨t₀⟩ := ‹Nonempty T›
  have hP : (1 - M * Mp) * M = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hMp, Matrix.mul_one, sub_self]
  have hPη : (1 - M * Mp) * ηM = 0 := by
    ext i c
    have hwM : (Matrix.of fun (_ : T) j => (1 - M * Mp : Matrix m m ℝ) i j) * M = 0 := by
      ext t c'
      simpa only [Matrix.mul_apply, Matrix.of_apply, Matrix.zero_apply] using
        congrFun (congrFun hP i) c'
    simpa only [Matrix.mul_apply, Matrix.of_apply, Matrix.zero_apply] using
      congrFun (congrFun (hker _ hwM) t₀) c
  -- so `η_M = M Z` with `Z = M⁺ η_M`
  have hZ : ηM = M * (Mp * ηM) := by
    rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at hPη
    rw [← Matrix.mul_assoc]
    exact hPη
  refine ⟨Mp * ηM, hZ, ?_⟩
  -- (iv) the identity (16) at `h'`: the hypothesis at `w = h' M⁺`, with `w M = h'`, `w η_M = h' Z`
  intro h' hh'
  have hw : h' * Mp * M = h' := by rw [Matrix.mul_assoc, hMp, Matrix.mul_one]
  have e := h (h' * Mp) (by rw [hw]; exact hh')
  rw [hw, Matrix.mul_assoc] at e
  exact e

/-- Helper: `y ↦ M y`, as a linear map. -/
private def mulLeftLin_zc {m n p : Type*} [Fintype n] (M : Matrix m n ℝ) :
    Matrix n p ℝ →ₗ[ℝ] Matrix m p ℝ where
  toFun y := M * y
  map_add' a b := Matrix.mul_add M a b
  map_smul' c a := Matrix.mul_smul M c a

/-- Helper: the chain rule for `F_θ(x) = 𝓑_{>0}(x E)` at an input `x` such that `x E` has no zero
row (where `(θ', h) ↦ 𝓑_{>0}(h)` is analytic): the derivative of `θ ↦ F_θ(x)` along `η` is
`𝐃𝓑_{>0}(x E)(x η_E) + 𝐃_θ 𝓑_{>0}(x E) η`. -/
private theorem fderiv_eval_eq_fderiv_suffix_zc (hχ : A.χ = rmsNorm 0)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (hθ : RegularZero A θ)
    (x : Matrix T dIn ℝ) (hx : ∀ t, (x * θ.E) t ≠ 0) (η : Params A dIn dOut) :
    fderiv ℝ (fun θ' : Params A dIn dOut => eval A 0 θ' x) θ η
      = fderiv ℝ (fun h' : Matrix T d ℝ => suffix A 0 θ 0 h') (x * θ.E) (x * η.E)
        + fderiv ℝ (fun θ' : Params A dIn dOut => suffix A 0 θ' 0 (x * θ.E)) θ η := by
  -- `Φ(θ', h) = 𝓑_{>0}(h)` with the weights `θ'`, and its derivative `Φ'` at `(θ, x E)`
  let Φ : Params A dIn dOut × Matrix T d ℝ → Matrix T dOut ℝ := fun p => suffix A 0 p.1 0 p.2
  have hΦ : HasFDerivAt Φ (fderiv ℝ Φ (θ, x * θ.E)) (θ, x * θ.E) :=
    (analyticAt_suffix_prod_zero A θ hχ hf hθ 0 (x * θ.E) hx).differentiableAt.hasFDerivAt
  -- `θ' ↦ x θ'_E`, a continuous linear map
  let lE : Params A dIn dOut →L[ℝ] Matrix T d ℝ := LinearMap.toContinuousLinearMap
    ((mulLeftLin_zc x).comp (Params.linE (A := A) (dIn := dIn) (dOut := dOut)))
  -- three chain rules: `F_θ'(x) = Φ(θ', x θ'_E)`, `θ' ↦ Φ(θ', x E)` and `h ↦ Φ(θ, h)`
  have h1 : HasFDerivAt (fun θ' : Params A dIn dOut => eval A 0 θ' x)
      ((fderiv ℝ Φ (θ, x * θ.E)).comp ((ContinuousLinearMap.id ℝ _).prod lE)) θ := by
    have hc := hΦ.comp θ ((hasFDerivAt_id θ).prodMk lE.hasFDerivAt)
    have hfun : (fun θ' : Params A dIn dOut => eval A 0 θ' x) = Φ ∘ fun θ' => (id θ', lE θ') :=
      funext fun θ' => eval_eq_suffix_zero A 0 θ' x
    rw [hfun]
    exact hc
  have h2 : HasFDerivAt (fun θ' : Params A dIn dOut => suffix A 0 θ' 0 (x * θ.E))
      ((fderiv ℝ Φ (θ, x * θ.E)).comp (ContinuousLinearMap.inl ℝ _ _)) θ := by
    have hl : HasFDerivAt (fun θ' : Params A dIn dOut => (θ', x * θ.E))
        (ContinuousLinearMap.inl ℝ (Params A dIn dOut) (Matrix T d ℝ)) θ :=
      hasFDerivAt_prodMk_left θ (x * θ.E)
    have hc := hΦ.comp θ hl
    exact hc
  have h3 : HasFDerivAt (fun h' : Matrix T d ℝ => suffix A 0 θ 0 h')
      ((fderiv ℝ Φ (θ, x * θ.E)).comp (ContinuousLinearMap.inr ℝ _ _)) (x * θ.E) := by
    have hl : HasFDerivAt (fun h' : Matrix T d ℝ => (θ, h'))
        (ContinuousLinearMap.inr ℝ (Params A dIn dOut) (Matrix T d ℝ)) (x * θ.E) :=
      hasFDerivAt_prodMk_right θ (x * θ.E)
    have hc := hΦ.comp (x * θ.E) hl
    exact hc
  rw [h1.fderiv, h2.fderiv, h3.fderiv]
  -- `Φ'(η, x η_E) = Φ'(0, x η_E) + Φ'(η, 0)`
  show fderiv ℝ Φ (θ, x * θ.E) (η, x * η.E)
    = fderiv ℝ Φ (θ, x * θ.E) (0, x * η.E) + fderiv ℝ Φ (θ, x * θ.E) (η, 0)
  rw [← map_add (fderiv ℝ Φ (θ, x * θ.E)), Prod.mk_add_mk, zero_add, add_zero]

/-- **Proposition D.4 of the dimension paper, the case (0), the flat directions:** for
real-analytic blocks under pre-RMSNorm with `ε = 0`, `d ≥ 2`, regular `θ` and `(D_0)`, every flat
direction is a direction of the symmetries: `η = cobDir θ Y + scaleDir θ β` with antisymmetric
`Y_0, …, Y_L` and numbers `β_0, …, β_L`. -/
theorem flat_le_cobDir_add_scaleDir_of_claimZero [Nonempty T] (hχ : A.χ = rmsNorm 0)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (hθ : RegularZero A θ)
    (hd : 2 ≤ Fintype.card d) (h0 : ClaimZero A θ 0)
    (η : Params A dIn dOut) (hη : η ∈ flat A 0 θ) :
    ∃ (Y : Fin (L + 1) → Matrix d d ℝ) (β : Fin (L + 1) → ℝ),
      (∀ ℓ, Y ℓ ∈ antisymmetric d) ∧ η = cobDir θ Y + scaleDir θ β := by
  -- for every input `x` such that `x E` has no zero row:
  -- `0 = 𝐃_θ F(x) η = 𝐃𝓑_{>0}(x E)(x η_E) + 𝐃_θ 𝓑_{>0}(x E) η`
  have hx : ∀ x : Matrix T dIn ℝ, (∀ t, (x * θ.E) t ≠ 0) →
      fderiv ℝ (fun h' : Matrix T d ℝ => suffix A 0 θ 0 h') (x * θ.E) (x * η.E)
        + fderiv ℝ (fun θ' : Params A dIn dOut => suffix A 0 θ' 0 (x * θ.E)) θ η = 0 := by
    intro x hxE
    rw [← fderiv_eval_eq_fderiv_suffix_zc A θ hχ hf hθ x hxE η]
    exact LinearMap.mem_ker.1 ((Submodule.mem_iInf _).1 hη x)
  -- Lemma D.3 at the embedding (rank `d` by (R1)): `η_E = E Z` and the identity (16) for `k = 0`
  obtain ⟨Z, hEZ, hZ⟩ :=
    suffixFlatZero_of_flat_at_write A θ hχ hf hθ hd 0 θ.E hθ.rank_E η.E η hx
  -- the claim `(D_0)` gives `Z = Y_0 + β_0 I` and the moves of the reads, the writes and `D`
  obtain ⟨Y, β, hYa, hZY, hrw, hD⟩ := h0 Z η hZ
  refine ⟨Y, β, fun ℓ => hYa ℓ (Fin.zero_le _),
    Params.ext' ?_ (fun ℓ => ?_) (fun ℓ => ?_) ?_⟩
  · -- `η_E = E (Y_0 + β_0 I) = E Y_0 + β_0 E`
    rw [hEZ, hZY, Params.add_E]
    simp only [cobDir, scaleDir, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one]
  · rw [(hrw ℓ (Fin.zero_le _)).1, Params.add_read]
    simp only [cobDir, scaleDir, add_zero]
  · -- `η_write = W (Y + β I) = W Y + β W`
    rw [(hrw ℓ (Fin.zero_le _)).2, Params.add_write]
    simp only [cobDir, scaleDir, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one]
  · rw [hD, Params.add_D]
    simp only [cobDir, scaleDir, add_zero]

/-- Helper: `β ↦ scaleDir θ β` is linear (as `scaleDirLin_rz` in
`Dimension/UpperBoundRMSNormZero.lean`, which is private). -/
private noncomputable def scaleDirLin_zc : (Fin (L + 1) → ℝ) →ₗ[ℝ] Params A dIn dOut where
  toFun := scaleDir θ
  map_add' β β' := by
    refine Params.ext' ?_ (fun ℓ => ?_) (fun ℓ => ?_) ?_ <;>
      simp only [scaleDir, Params.add_E, Params.add_read, Params.add_write, Params.add_D,
        Pi.add_apply, add_smul, add_zero]
  map_smul' c β := by
    refine Params.ext' ?_ (fun ℓ => ?_) (fun ℓ => ?_) ?_ <;>
      simp only [scaleDir, Params.smul_E, Params.smul_read, Params.smul_write, Params.smul_D,
        Pi.smul_apply, smul_eq_mul, mul_smul, smul_zero, RingHom.id_apply]

/-- **Proposition D.4 of the dimension paper, the case (0), the rank:** for real-analytic blocks
under pre-RMSNorm with `ε = 0`, `d ≥ 2`, regular `θ` and `(D_0)`, the functional dimension is
`P − (L + 1)(d(d−1)/2 + 1)`. -/
theorem funDim_of_claimZero [Nonempty T] (hχ : A.χ = rmsNorm 0)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (hθ : RegularZero A θ)
    (hd : 2 ≤ Fintype.card d) (h0 : ClaimZero A θ 0) :
    funDim A 0 θ + (L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
      = Module.finrank ℝ (Params A dIn dOut) := by
  have : Nonempty d := Fintype.card_pos_iff.1 (by omega)
  -- `≤`: the directions of the symmetries are flat (Theorem 4.3 for `ε = 0`)
  have hle := funDim_add_le_skipless_rmsNorm_zero θ hχ hθ.rank_E hθ.rank_write
  -- `≥`: `K(θ)` lies in the range of `(Y, β) ↦ cobDir θ Y + scaleDir θ β` (antisymmetric `Y_ℓ`)
  let Φ : (Fin (L + 1) → antisymmetric d) × (Fin (L + 1) → ℝ) →ₗ[ℝ] Params A dIn dOut :=
    ((cobDirLin θ).comp (LinearMap.compLeft (antisymmetric d).subtype (Fin (L + 1)))).coprod
      (scaleDirLin_zc A θ)
  have hflat : flat A 0 θ ≤ LinearMap.range Φ := by
    intro η hη
    obtain ⟨Y, β, hY, rfl⟩ := flat_le_cobDir_add_scaleDir_of_claimZero A θ hχ hf hθ hd h0 η hη
    exact ⟨(fun ℓ => ⟨Y ℓ, hY ℓ⟩, β), rfl⟩
  -- a space of dimension at most `(L + 1) (d (d - 1) / 2 + 1)`
  have hdim : Module.finrank ℝ (LinearMap.range Φ)
      ≤ (L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2 + 1) := by
    calc Module.finrank ℝ (LinearMap.range Φ)
        ≤ Module.finrank ℝ ((Fin (L + 1) → antisymmetric d) × (Fin (L + 1) → ℝ)) :=
          LinearMap.finrank_range_le Φ
      _ = (L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2 + 1) := by
        rw [Module.finrank_prod, Module.finrank_pi_fintype, finrank_antisymmetric,
          Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
          Module.finrank_fin_fun]
        ring
  -- `fd(θ) + dim K(θ) = P`
  have h := funDim_add_finrank_flat' (S := 0) θ
  have hmono := Submodule.finrank_mono hflat
  generalize (L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2 + 1) = N at hle hdim ⊢
  omega

end Skips
