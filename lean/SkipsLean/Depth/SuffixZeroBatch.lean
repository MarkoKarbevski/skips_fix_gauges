import SkipsLean.Depth.SuffixZeroClaim

/-!
# The case (0): the rank on a finite batch of inputs with nonzero hidden states

Paper (dimension paper): Proposition D.4 (The claim gives the rank), its last clause in the case
(0): "… and the Jacobian of the network has the rank (13) on some finite batch of such inputs",
the inputs `x` with `xE ≠ 0`. Appendix D.7 uses it: "By Proposition D.4 there is a finite batch
`X*`, with `xE ≠ 0` for all its inputs, on which the Jacobian at `θ*` has the rank (13)."

`funDim_of_claimZero` (`Depth/SuffixZeroClaim.lean`) gives the functional dimension, the largest
rank over all finite batches. Here the batch is named, with its inputs: no row of `xE` vanishes
(a hidden state has the rows `T`). In the case (0) the rank (13) is
`P − (L + 1)(d(d−1)/2 + 1)`.
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable (A : Arch T d L) (θ : Params A dIn dOut)

/-- Helper: `y ↦ M y`, as a linear map (as `mulLeftLin_zc` in `Depth/SuffixZeroClaim.lean`, which
is private). -/
private def mulLeftLin_bat {m n p : Type*} [Fintype n] (M : Matrix m n ℝ) :
    Matrix n p ℝ →ₗ[ℝ] Matrix m p ℝ where
  toFun y := M * y
  map_add' a b := Matrix.mul_add M a b
  map_smul' c a := Matrix.mul_smul M c a

/-- Helper: the chain rule for `F_θ(x) = 𝓑_{>0}(x E)` at an input `x` such that `x E` has no zero
row (where `(θ', h) ↦ 𝓑_{>0}(h)` is analytic): `θ ↦ F_θ(x)` is differentiable at `θ`, and its
derivative along `η` is `𝐃𝓑_{>0}(x E)(x η_E) + 𝐃_θ 𝓑_{>0}(x E) η` (as
`fderiv_eval_eq_fderiv_suffix_zc` in `Depth/SuffixZeroClaim.lean`, which is private). -/
private theorem fderiv_eval_eq_fderiv_suffix_bat (hχ : A.χ = rmsNorm 0)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (hθ : RegularZero A θ)
    (x : Matrix T dIn ℝ) (hx : ∀ t, (x * θ.E) t ≠ 0) :
    DifferentiableAt ℝ (fun θ' : Params A dIn dOut => eval A 0 θ' x) θ ∧
    ∀ η : Params A dIn dOut,
    fderiv ℝ (fun θ' : Params A dIn dOut => eval A 0 θ' x) θ η
      = fderiv ℝ (fun h' : Matrix T d ℝ => suffix A 0 θ 0 h') (x * θ.E) (x * η.E)
        + fderiv ℝ (fun θ' : Params A dIn dOut => suffix A 0 θ' 0 (x * θ.E)) θ η := by
  -- `Φ(θ', h) = 𝓑_{>0}(h)` with the weights `θ'`, and its derivative `Φ'` at `(θ, x E)`
  let Φ : Params A dIn dOut × Matrix T d ℝ → Matrix T dOut ℝ := fun p => suffix A 0 p.1 0 p.2
  have hΦ : HasFDerivAt Φ (fderiv ℝ Φ (θ, x * θ.E)) (θ, x * θ.E) :=
    (analyticAt_suffix_prod_zero A θ hχ hf hθ 0 (x * θ.E) hx).differentiableAt.hasFDerivAt
  -- `θ' ↦ x θ'_E`, a continuous linear map
  let lE : Params A dIn dOut →L[ℝ] Matrix T d ℝ := LinearMap.toContinuousLinearMap
    ((mulLeftLin_bat x).comp (Params.linE (A := A) (dIn := dIn) (dOut := dOut)))
  -- three chain rules: `F_θ'(x) = Φ(θ', x θ'_E)`, `θ' ↦ Φ(θ', x E)` and `h ↦ Φ(θ, h)`
  have h1 : HasFDerivAt (fun θ' : Params A dIn dOut => eval A 0 θ' x)
      ((fderiv ℝ Φ (θ, x * θ.E)).comp ((ContinuousLinearMap.id ℝ _).prod lE)) θ := by
    have hc := hΦ.comp θ ((hasFDerivAt_id θ).prodMk lE.hasFDerivAt)
    have hfun : (fun θ' : Params A dIn dOut => eval A 0 θ' x) = Φ ∘ fun θ' => (id θ', lE θ') :=
      funext fun θ' => eval_eq_suffix_zero A 0 θ' x
    rw [hfun]
    exact hc
  refine ⟨h1.differentiableAt, fun η => ?_⟩
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

/-- Helper: `β ↦ scaleDir θ β` is linear (as `scaleDirLin_zc` in `Depth/SuffixZeroClaim.lean`,
which is private). -/
private noncomputable def scaleDirLin_bat : (Fin (L + 1) → ℝ) →ₗ[ℝ] Params A dIn dOut where
  toFun := scaleDir θ
  map_add' β β' := by
    refine Params.ext' ?_ (fun ℓ => ?_) (fun ℓ => ?_) ?_ <;>
      simp only [scaleDir, Params.add_E, Params.add_read, Params.add_write, Params.add_D,
        Pi.add_apply, add_smul, add_zero]
  map_smul' c β := by
    refine Params.ext' ?_ (fun ℓ => ?_) (fun ℓ => ?_) ?_ <;>
      simp only [scaleDir, Params.smul_E, Params.smul_read, Params.smul_write, Params.smul_D,
        Pi.smul_apply, smul_eq_mul, mul_smul, smul_zero, RingHom.id_apply]

/-- Helper: a direction that is flat at every input `x` such that `x E` has no zero row is a
direction of the symmetries, `η = cobDir θ Y + scaleDir θ β` with antisymmetric `Y_0, …, Y_L`
(the proof of `flat_le_cobDir_add_scaleDir_of_claimZero`, which uses only these inputs). -/
private theorem flatOn_le_cobDir_add_scaleDir_bat [Nonempty T] (hχ : A.χ = rmsNorm 0)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (hθ : RegularZero A θ)
    (hd : 2 ≤ Fintype.card d) (h0 : ClaimZero A θ 0) (η : Params A dIn dOut)
    (hη : η ∈ flatOn A 0 θ {x : Matrix T dIn ℝ | ∀ t, (x * θ.E) t ≠ 0}) :
    ∃ (Y : Fin (L + 1) → Matrix d d ℝ) (β : Fin (L + 1) → ℝ),
      (∀ ℓ, Y ℓ ∈ antisymmetric d) ∧ η = cobDir θ Y + scaleDir θ β := by
  -- for every input `x` such that `x E` has no zero row:
  -- `0 = 𝐃_θ F(x) η = 𝐃𝓑_{>0}(x E)(x η_E) + 𝐃_θ 𝓑_{>0}(x E) η`
  have hx : ∀ x : Matrix T dIn ℝ, (∀ t, (x * θ.E) t ≠ 0) →
      fderiv ℝ (fun h' : Matrix T d ℝ => suffix A 0 θ 0 h') (x * θ.E) (x * η.E)
        + fderiv ℝ (fun θ' : Params A dIn dOut => suffix A 0 θ' 0 (x * θ.E)) θ η = 0 := by
    intro x hxE
    rw [← (fderiv_eval_eq_fderiv_suffix_bat A θ hχ hf hθ x hxE).2 η]
    exact LinearMap.mem_ker.1 ((Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hη x) hxE)
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

/-- **Proposition D.4 of the dimension paper, the case (0), the batch:** for real-analytic blocks
under pre-RMSNorm with `ε = 0`, `d ≥ 2`, regular `θ` and `(D_0)`, there is a finite batch of inputs
`x` such that `xE` has no zero row on which the Jacobian has the rank
`P − (L + 1)(d(d−1)/2 + 1)`. -/
theorem exists_batch_jacobianRank_of_claimZero [Nonempty T] (hχ : A.χ = rmsNorm 0)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (hθ : RegularZero A θ)
    (hd : 2 ≤ Fintype.card d) (h0 : ClaimZero A θ 0) :
    ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i t, (X i * θ.E) t ≠ 0) ∧
      jacobianRank A 0 X θ + (L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
        = Module.finrank ℝ (Params A dIn dOut) := by
  have : Nonempty d := Fintype.card_pos_iff.1 (by omega)
  -- the inputs `x` such that `x E` has no zero row, where the output is differentiable in `θ`
  set U : Set (Matrix T dIn ℝ) := {x | ∀ t, (x * θ.E) t ≠ 0} with hUdef
  have hU : ∀ x ∈ U, DifferentiableAt ℝ (fun θ' : Params A dIn dOut => eval A 0 θ' x) θ :=
    fun x hx => (fderiv_eval_eq_fderiv_suffix_bat A θ hχ hf hθ x hx).1
  -- a batch of inputs of `U` with rank `P - dim K_U(θ)`
  obtain ⟨n, X, hXU, hX⟩ := exists_jacobianRank_add_finrank_flatOn (S := 0) θ U hU
  refine ⟨n, X, fun i => hXU i, ?_⟩
  -- `dim K(θ) = (L + 1)(d(d-1)/2 + 1)` and `K(θ) ≤ K_U(θ)`
  have hfd := funDim_of_claimZero A θ hχ hf hθ hd h0
  have hfl := funDim_add_finrank_flat' (S := 0) θ
  have hge := Submodule.finrank_mono (flat_le_flatOn (S := 0) θ U)
  -- `K_U(θ)` lies in the range of `(Y, β) ↦ cobDir θ Y + scaleDir θ β` (antisymmetric `Y_ℓ`)
  let Φ : (Fin (L + 1) → antisymmetric d) × (Fin (L + 1) → ℝ) →ₗ[ℝ] Params A dIn dOut :=
    ((cobDirLin θ).comp (LinearMap.compLeft (antisymmetric d).subtype (Fin (L + 1)))).coprod
      (scaleDirLin_bat A θ)
  have hflat : flatOn A 0 θ U ≤ LinearMap.range Φ := by
    intro η hη
    obtain ⟨Y, β, hY, rfl⟩ := flatOn_le_cobDir_add_scaleDir_bat A θ hχ hf hθ hd h0 η hη
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
  have hle := Submodule.finrank_mono hflat
  generalize (L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2 + 1) = N at hfd hdim ⊢
  omega

end Skips
