import SkipsLean.Depth.SuffixRMS
import SkipsLean.Dimension.Rescaling
import SkipsLean.Activations.Analytic

/-!
# Claim `(D_k)` for gated blocks, and what it gives

Paper (dimension): Appendix D.3. "Claim `(D_k)`, for `k = 0, …, L`. Let `Z` be a `d × d` matrix
and `η` a direction of the weights of the blocks `k+1, …, L` and of `D`. If (16) holds, then
`Z ∈ 𝔤`, and with `Z_k = Z` there are `Z_{k+1}, …, Z_L ∈ 𝔤` such that … For gated blocks there
are, in addition, diagonal matrices `Δ_{k+1}, …, Δ_L`, with `Δ_ℓ` of size `q_ℓ`, such that

  `η = ({-Z_{ℓ-1} W_g^ℓ, -Z_{ℓ-1} W_v^ℓ - W_v^ℓ Δ_ℓ, Δ_ℓ W_write^ℓ + W_write^ℓ Z_ℓ}_{ℓ=k+1}^L, -Z_L D)`  (19)."

Here `𝔤` is the space of all matrices in the case (n) (no normalization) and the space of
antisymmetric matrices in the case (+) (pre-RMSNorm with `ε > 0`); gated blocks are not treated in
the case (0). The diagonal matrix `Δ_ℓ` is the function `α ℓ : hid ℓ → ℝ` of its diagonal entries,
and the three terms with `Δ_ℓ` in (19) are the entries of `rescaleDir θ α`
(`Dimension/Rescaling.lean`): `0` at the gate columns, `-α_i` times the value column of unit `i`,
`α_i` times its write row.

Stated here, for the cases (n) and (+): the claim (`ClaimGated`); Lemma D.5 for gated blocks
(`(D_L)` holds); Proposition D.4 for gated blocks ("Let `θ` be regular, with no vanishing value
column if the blocks are gated, and let `(D_0)` hold at `θ`. Then the directions `η` with
`D_θ F(θ, x) η = 0` for all `x` … are the directions … `η^{Z,Δ}` of (12) for gated blocks, and the
Jacobian of the network has the rank (13) on some finite batch"), where the rank (13) is
`P - (L + 1) dim G - s` with `s = ∑_ℓ q_ℓ`.

For GELU blocks in the case (+) the claim has the form (17) of tanh blocks, and `ClaimRMS`,
`claimRMS_last`, `funDim_of_claimRMS` of `Depth/SuffixRMS.lean` apply as they are.
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise Topology

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {σ : ℝ → ℝ} {χ : Matrix T d ℝ → Matrix T d ℝ} {hid : Fin L → Type}
  [∀ ℓ, Fintype (hid ℓ)]

/-- **Claim `(D_k)` for gated blocks,** with the changes of basis in the subspace `g` of matrices
(all matrices in the case (n), the antisymmetric ones in the case (+)): every `Z` and `η` that
satisfy the identity (16) for `k` come from changes of basis `Z_k = Z, Z_{k+1}, …, Z_L ∈ g` at the
hidden states `h_k, …, h_L` and from rescalings of the values of the hidden units of the blocks
after `h_k`, as in (19). -/
def ClaimGated (g : Submodule ℝ (Matrix d d ℝ))
    (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut) (k : Fin (L + 1)) : Prop :=
  ∀ (Z : Matrix d d ℝ) (η : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut),
    SuffixFlat (Arch.gated σ χ hid) θ k Z η →
    ∃ (X : Fin (L + 1) → Matrix d d ℝ) (α : ∀ ℓ, hid ℓ → ℝ),
      X k = Z ∧ (∀ ℓ, k ≤ ℓ → X ℓ ∈ g) ∧
      (∀ ℓ : Fin L, k ≤ ℓ.castSucc →
        η.read ℓ = -(X ℓ.castSucc * θ.read ℓ) + (rescaleDir θ α).read ℓ ∧
        η.write ℓ = θ.write ℓ * X ℓ.succ + (rescaleDir θ α).write ℓ) ∧
      η.D = -(X (Fin.last L) * θ.D)

/-! ### Lemma D.5 for gated blocks: `(D_L)` -/

/-- **Lemma D.5, gated blocks, case (n):** `(D_L)` holds. -/
theorem claimGated_last [Nonempty T]
    (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) :
    ClaimGated ⊤ θ (Fin.last L) := by
  intro Z η hZ
  -- Lemma D.5 for the same architecture: `X_L = Z` and `η_D = -Z D`
  obtain ⟨X, hXL, -, hXD⟩ := claim_last (Arch.gated σ id hid) θ rfl Z η hZ
  -- no block comes after `L`, so no rescaling is needed (`α = 0`)
  exact ⟨X, 0, hXL, fun _ _ => Submodule.mem_top,
    fun ℓ hℓ => absurd hℓ (not_le.2 (Fin.castSucc_lt_last ℓ)), hXD⟩

/-- **Lemma D.5, gated blocks, case (+):** if `D` has rank `d`, then `(D_L)` holds. -/
theorem claimGated_last_rmsNorm [Nonempty T] {ε : ℝ} (hε : 0 < ε)
    (θ : Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)
    (hD : θ.D.rank = Fintype.card d) :
    ClaimGated (antisymmetric d) θ (Fin.last L) := by
  intro Z η hZ
  -- Lemma D.5 for the same architecture: `X_L = Z` is antisymmetric and `η_D = -Z D`
  obtain ⟨X, hXL, hXa, -, hXD⟩ :=
    claimRMS_last (Arch.gated σ (rmsNorm ε) hid) θ hε rfl hD Z η hZ
  -- no block comes after `L`, so no rescaling is needed (`α = 0`)
  exact ⟨X, 0, hXL, hXa, fun ℓ hℓ => absurd hℓ (not_le.2 (Fin.castSucc_lt_last ℓ)), hXD⟩

/-! ### Proposition D.4 for gated blocks -/

/-- Helper (a copy of the private `rescaleDirLin` of `Dimension/Rescaling.lean`):
`α ↦ rescaleDir θ α` is linear. -/
private noncomputable def rescaleDirLinG
    (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut) :
    (∀ ℓ, hid ℓ → ℝ) →ₗ[ℝ] Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut where
  toFun := rescaleDir θ
  map_add' α β := by
    apply Params.ext'
    · simp [rescaleDir]
    · intro ℓ
      ext k j
      cases j with
      | inl i => simp [rescaleDir]
      | inr i =>
        simp only [rescaleDir, Pi.add_apply, Params.add_read, Matrix.add_apply, Matrix.of_apply,
          Sum.elim_inr]
        ring
    · intro ℓ
      ext i k
      simp [rescaleDir, add_mul]
    · simp [rescaleDir]
  map_smul' c α := by
    apply Params.ext'
    · simp [rescaleDir]
    · intro ℓ
      ext k j
      cases j <;> simp [rescaleDir, mul_assoc]
    · intro ℓ
      ext i k
      simp [rescaleDir, mul_assoc]
    · simp [rescaleDir]

omit [Fintype T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (a copy of the private `finrank_dirDomain` of `Dimension/Rescaling.lean`): the pairs
`(X, α)` form a space of dimension `(L + 1) d² + s`. -/
private theorem finrank_dirDomainG :
    Module.finrank ℝ ((Fin (L + 1) → Matrix d d ℝ) × (∀ ℓ, hid ℓ → ℝ)) =
      (L + 1) * Fintype.card d ^ 2 + ∑ ℓ, Fintype.card (hid ℓ) := by
  rw [Module.finrank_prod, Module.finrank_pi_fintype, Module.finrank_matrix,
    Module.finrank_pi_fintype]
  simp [sq, Module.finrank_fintype_fun_eq_card]

/-- **Proposition D.4, gated blocks, case (n), first part:** if `θ` is regular and `(D_0)` holds
at `θ`, every flat direction is the sum of the direction of changes of basis at the hidden states
and of the direction of rescalings of the values (`η^{Z,Δ}` of the paper). -/
theorem flat_le_cobDir_add_rescaleDir_of_claimGated [Nonempty T]
    (hσ : AnalyticOnNhd ℝ σ Set.univ)
    (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (hθ : Regular (Arch.gated σ id hid) θ) (h0 : ClaimGated ⊤ θ 0)
    (η : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (hη : η ∈ flat (Arch.gated σ id hid) 0 θ) :
    ∃ (X : Fin (L + 1) → Matrix d d ℝ) (α : ∀ ℓ, hid ℓ → ℝ),
      η = cobDir θ X + rescaleDir θ α := by
  -- the gated blocks are real-analytic
  have hf : ∀ ℓ, AnalyticOnNhd ℝ ((Arch.gated (T := T) (d := d) σ id hid).f ℓ) Set.univ :=
    analyticOnNhd_f_gated hσ
  have hfd : ∀ ℓ, Differentiable ℝ ((Arch.gated (T := T) (d := d) σ id hid).f ℓ) := fun ℓ =>
    differentiableOn_univ.1 (hf ℓ).differentiableOn
  -- for every input `x`: `0 = 𝐃_θ F(x) η = 𝐃𝓑_{>0}(x E)(x η_E) + 𝐃_θ 𝓑_{>0}(x E) η`
  have hx : ∀ x : Matrix T dIn ℝ,
      fderiv ℝ (fun h' : Matrix T d ℝ => suffix (Arch.gated σ id hid) 0 θ 0 h') (x * θ.E)
          (x * η.E)
        + fderiv ℝ (fun θ' : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut =>
            suffix (Arch.gated σ id hid) 0 θ' 0 (x * θ.E)) θ η = 0 := by
    intro x
    rw [← fderiv_eval_eq_fderiv_suffix (Arch.gated σ id hid) θ rfl hfd x η]
    exact LinearMap.mem_ker.1 ((Submodule.mem_iInf _).1 hη x)
  -- Lemma D.3 at the embedding (rank `d` by (R1)): `η_E = E Z` and the identity (16) for `k = 0`
  obtain ⟨Z, hEZ, hZ⟩ :=
    suffixFlat_of_flat_at_write (Arch.gated σ id hid) θ rfl hf hθ 0 θ.E hθ.rank_E η.E η hx
  -- the claim `(D_0)` gives the changes of basis `X` with `X_0 = Z` and the rescalings `α`
  obtain ⟨X, α, hX0, -, hX, hXD⟩ := h0 Z η hZ
  -- the entries of `η`: at `E` (where `rescaleDir` is `0`), at every block, and at `D`
  refine ⟨X, α, Params.ext' ?_ (fun ℓ => (hX ℓ (Fin.zero_le _)).1)
    (fun ℓ => (hX ℓ (Fin.zero_le _)).2) ?_⟩
  · show η.E = θ.E * X 0 + 0
    rw [add_zero, hX0, hEZ]
  · show η.D = -(X (Fin.last L) * θ.D) + 0
    rw [add_zero, hXD]

/-- **Proposition D.4, gated blocks, case (n):** if `θ` is regular, no value column of a read
vanishes and `(D_0)` holds at `θ`, the functional dimension at `θ` is
`P - (L + 1) d² - ∑ d_hidden`. -/
theorem funDim_of_claimGated [Nonempty T] (hσ : AnalyticOnNhd ℝ σ Set.univ)
    (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (hθ : Regular (Arch.gated σ id hid) θ)
    (hv : ∀ ℓ i, (fun k => θ.read ℓ k (Sum.inr i)) ≠ 0) (h0 : ClaimGated ⊤ θ 0) :
    funDim (Arch.gated σ id hid) 0 θ
        + ((L + 1) * Fintype.card d ^ 2 + ∑ ℓ, Fintype.card (hid ℓ))
      = Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) := by
  have hσd : Differentiable ℝ σ := differentiableOn_univ.1 hσ.differentiableOn
  -- `≤`: the changes of basis and the rescalings are flat, and they span a space of dimension
  -- `(L + 1) d² + s` (Lemma B.1 for gated blocks)
  have hle := funDim_add_le_skipless_gated θ hσd hθ.rank_E hθ.rank_write hv
  -- `≥`: `K(θ)` lies in the range of `(X, α) ↦ cobDir θ X + rescaleDir θ α`
  let Φ := (cobDirLin θ).coprod (rescaleDirLinG θ)
  have hflat : flat (Arch.gated σ id hid) 0 θ ≤ LinearMap.range Φ := by
    intro η hη
    obtain ⟨X, α, rfl⟩ := flat_le_cobDir_add_rescaleDir_of_claimGated hσ θ hθ h0 η hη
    exact ⟨(X, α), rfl⟩
  -- a space of dimension at most `(L + 1) d² + s`
  have hdim : Module.finrank ℝ (LinearMap.range Φ)
      ≤ (L + 1) * Fintype.card d ^ 2 + ∑ ℓ, Fintype.card (hid ℓ) := by
    calc Module.finrank ℝ (LinearMap.range Φ)
        ≤ Module.finrank ℝ ((Fin (L + 1) → Matrix d d ℝ) × (∀ ℓ, hid ℓ → ℝ)) :=
          LinearMap.finrank_range_le Φ
      _ = (L + 1) * Fintype.card d ^ 2 + ∑ ℓ, Fintype.card (hid ℓ) := finrank_dirDomainG
  -- `fd(θ) + dim K(θ) = P`
  have h := funDim_add_finrank_flat' (S := 0) θ
  have hmono := Submodule.finrank_mono hflat
  generalize (L + 1) * Fintype.card d ^ 2 + ∑ ℓ, Fintype.card (hid ℓ) = N at hle hdim ⊢
  omega

/-- **Proposition D.4, gated blocks, case (+), first part:** if `θ` is regular and `(D_0)` holds
at `θ`, every flat direction is the sum of the direction of antisymmetric changes of basis at the
hidden states and of the direction of rescalings of the values. -/
theorem flat_le_cobDir_add_rescaleDir_of_claimGated_rmsNorm [Nonempty T] {ε : ℝ} (hε : 0 < ε)
    (hσ : AnalyticOnNhd ℝ σ Set.univ)
    (θ : Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)
    (hθ : Regular (Arch.gated σ (rmsNorm ε) hid) θ) (h0 : ClaimGated (antisymmetric d) θ 0)
    (η : Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)
    (hη : η ∈ flat (Arch.gated σ (rmsNorm ε) hid) 0 θ) :
    ∃ (X : Fin (L + 1) → Matrix d d ℝ) (α : ∀ ℓ, hid ℓ → ℝ),
      (∀ ℓ, X ℓ ∈ antisymmetric d) ∧ η = cobDir θ X + rescaleDir θ α := by
  -- the gated blocks are real-analytic
  have hf : ∀ ℓ,
      AnalyticOnNhd ℝ ((Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid).f ℓ) Set.univ :=
    analyticOnNhd_f_gated hσ
  -- for every input `x`: `0 = 𝐃_θ F(x) η = 𝐃𝓑_{>0}(x E)(x η_E) + 𝐃_θ 𝓑_{>0}(x E) η`
  have hx : ∀ x : Matrix T dIn ℝ,
      fderiv ℝ (fun h' : Matrix T d ℝ => suffix (Arch.gated σ (rmsNorm ε) hid) 0 θ 0 h')
          (x * θ.E) (x * η.E)
        + fderiv ℝ (fun θ' : Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut =>
            suffix (Arch.gated σ (rmsNorm ε) hid) 0 θ' 0 (x * θ.E)) θ η = 0 := by
    intro x
    rw [← fderiv_eval_eq_fderiv_suffix_rmsNorm (Arch.gated σ (rmsNorm ε) hid) θ hε rfl hf x η]
    exact LinearMap.mem_ker.1 ((Submodule.mem_iInf _).1 hη x)
  -- Lemma D.3 at the embedding (rank `d` by (R1)): `η_E = E Z` and the identity (16) for `k = 0`
  obtain ⟨Z, hEZ, hZ⟩ := suffixFlat_of_flat_at_write_rmsNorm (Arch.gated σ (rmsNorm ε) hid) θ
    hε rfl hf hθ 0 θ.E hθ.rank_E η.E η hx
  -- the claim `(D_0)` gives the antisymmetric changes of basis `X` with `X_0 = Z` and the
  -- rescalings `α`
  obtain ⟨X, α, hX0, hXa, hX, hXD⟩ := h0 Z η hZ
  -- the entries of `η`: at `E` (where `rescaleDir` is `0`), at every block, and at `D`
  refine ⟨X, α, fun ℓ => hXa ℓ (Fin.zero_le _), Params.ext' ?_
    (fun ℓ => (hX ℓ (Fin.zero_le _)).1) (fun ℓ => (hX ℓ (Fin.zero_le _)).2) ?_⟩
  · show η.E = θ.E * X 0 + 0
    rw [add_zero, hX0, hEZ]
  · show η.D = -(X (Fin.last L) * θ.D) + 0
    rw [add_zero, hXD]

/-- **Proposition D.4, gated blocks, case (+):** if `θ` is regular, no value column of a read
vanishes and `(D_0)` holds at `θ`, the functional dimension at `θ` is
`P - (L + 1) d (d - 1) / 2 - ∑ d_hidden`. -/
theorem funDim_of_claimGated_rmsNorm [Nonempty T] {ε : ℝ} (hε : 0 < ε)
    (hσ : AnalyticOnNhd ℝ σ Set.univ)
    (θ : Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)
    (hθ : Regular (Arch.gated σ (rmsNorm ε) hid) θ)
    (hv : ∀ ℓ i, (fun k => θ.read ℓ k (Sum.inr i)) ≠ 0)
    (h0 : ClaimGated (antisymmetric d) θ 0) :
    funDim (Arch.gated σ (rmsNorm ε) hid) 0 θ
        + ((L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2)
          + ∑ ℓ, Fintype.card (hid ℓ))
      = Module.finrank ℝ
          (Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut) := by
  have hσd : Differentiable ℝ σ := differentiableOn_univ.1 hσ.differentiableOn
  -- `≤`: the antisymmetric changes of basis and the rescalings are flat, and they span a space
  -- of dimension `(L + 1) d (d - 1) / 2 + s` (Lemma B.1 for gated blocks)
  have hle := funDim_add_le_skipless_gated_rmsNorm hε θ hσd hθ.rank_E hθ.rank_write hv
  -- `≥`: `K(θ)` lies in the range of `(X, α) ↦ cobDir θ X + rescaleDir θ α` on antisymmetric
  -- families `X`
  let Φ : ((Fin (L + 1) → antisymmetric d) × (∀ ℓ, hid ℓ → ℝ)) →ₗ[ℝ]
      Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut :=
    ((cobDirLin θ).comp (LinearMap.compLeft (antisymmetric d).subtype (Fin (L + 1)))).coprod
      (rescaleDirLinG θ)
  have hflat : flat (Arch.gated σ (rmsNorm ε) hid) 0 θ ≤ LinearMap.range Φ := by
    intro η hη
    obtain ⟨X, α, hX, rfl⟩ :=
      flat_le_cobDir_add_rescaleDir_of_claimGated_rmsNorm hε hσ θ hθ h0 η hη
    exact ⟨(fun ℓ => ⟨X ℓ, hX ℓ⟩, α), rfl⟩
  -- a space of dimension at most `(L + 1) d (d - 1) / 2 + s`
  have hdim : Module.finrank ℝ (LinearMap.range Φ)
      ≤ (L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2) + ∑ ℓ, Fintype.card (hid ℓ) := by
    calc Module.finrank ℝ (LinearMap.range Φ)
        ≤ Module.finrank ℝ ((Fin (L + 1) → antisymmetric d) × (∀ ℓ, hid ℓ → ℝ)) :=
          LinearMap.finrank_range_le Φ
      _ = (L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2)
          + ∑ ℓ, Fintype.card (hid ℓ) := by
        rw [Module.finrank_prod, Module.finrank_pi_fintype, finrank_antisymmetric,
          Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
          Module.finrank_pi_fintype]
        simp only [Module.finrank_fintype_fun_eq_card]
  -- `fd(θ) + dim K(θ) = P`
  have h := funDim_add_finrank_flat' (S := 0) θ
  have hmono := Submodule.finrank_mono hflat
  generalize (L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2)
    + ∑ ℓ, Fintype.card (hid ℓ) = N at hle hdim ⊢
  omega

end Skips
