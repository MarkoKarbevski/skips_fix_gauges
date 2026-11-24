import SkipsLean.Dimension.OrbitNetwork
import SkipsLean.Dimension.ExpOrbit
import SkipsLean.Generic.Params
import SkipsLean.Residual.UpperBoundSymmetries
import SkipsLean.Residual.DepthMlp
import SkipsLean.Residual.DepthMlpRMS

/-!
# Residual networks are locally identifiable up to one change of basis

Paper (skips paper): Definition 4.4, Proposition 4.5 and Corollary 4.9.

"Proposition 4.5 (The equality condition and local identifiability). Let the blocks be analytic,
with or without pre-RMSNorm, within the scope of Section 2. A skipless or a residual network
satisfies the equality condition if and only if, at generic parameters, it is locally identifiable
up to its symmetries. Every symmetry that is needed is then close to the identity."

"Corollary 4.9 (Residual networks are locally identifiable). Let the blocks be analytic, with or
without pre-RMSNorm, and let `θ` be generic parameters of the residual network. Every `θ'` near
`θ` with the same function is obtained from `θ` by symmetries inside the blocks and by one matrix
`G ∈ 𝒢`, all close to the identity. The matrix `G` is the same at all hidden states: for every
block `ℓ`, `E ↦ E G`, `W_read^ℓ ↦ G⁻¹ W_read^ℓ`, `W_write^ℓ ↦ W_write^ℓ G`, `D ↦ G⁻¹ D`."

Stated here, for residual networks whose blocks have no symmetries inside (`s = 0`: tanh and GELU
blocks):

* The direction of Proposition 4.5 from the equality condition to local identifiability, at one
  parameter: for real-analytic blocks, if `E` has rank `d` and the functional dimension at `θ` is
  `P − d²` (without normalization), resp. `P − d(d−1)/2` (under pre-RMSNorm with `ε > 0`), then
  every `θ'` near `θ` with the same function is `θ.cob (fun _ => G) (fun _ => G)` with one
  invertible (resp. orthogonal) `G` near the identity.
* Corollary 4.9 for tanh and GELU blocks, without normalization and under pre-RMSNorm with
  `ε > 0`: this holds at almost every parameter (Theorem 4.7 gives the functional dimension).

The twin for networks without skip connections is `Dimension/LocalIdentifiability.lean`; both use
`exists_mem_orbit_of_eval_eq` (`Dimension/OrbitNetwork.lean`). Not stated here: the converse
direction of Proposition 4.5, the blocks with symmetries inside (SwiGLU and GeGLU:
`Residual/LocalIdentifiabilityGated.lean`; attention), and the case `ε = 0`.
`θ.cob (fun _ => G) (fun _ => G)` is the change of basis with the same `G` at all hidden states
(`Symmetry/ChangeOfBasis.lean`).
-/

namespace Skips

open Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]

omit [Fintype T] [Fintype dOut] in
/-- Helper: a matrix `M` with `d` columns and of rank `d` cancels on the left: `M X = M Y` gives
`X = Y` (some `B` has `B M = 1`). -/
private theorem mul_left_cancel_of_rank_rli {m : Type*} [Fintype m] {M : Matrix m d ℝ}
    (hM : M.rank = Fintype.card d) {X Y : Matrix d d ℝ} (h : M * X = M * Y) : X = Y := by
  -- `v ↦ v M` is onto, so some `B` has `B M = 1`
  obtain ⟨B, hB⟩ : ∃ B : Matrix d m ℝ, B * M = 1 := by
    have hs := (Matrix.vecMul_surjective_iff_rank_eq_card (M := M)).2 hM
    choose v hv using fun i : d => hs (Pi.single i 1)
    have hv' : ∀ i, v i ᵥ* M = Pi.single i 1 := hv
    refine ⟨Matrix.of v, ?_⟩
    ext i j
    rw [Matrix.mul_apply_eq_vecMul, show (Matrix.of v) i = v i from rfl, hv',
      Matrix.one_eq_pi_single]
  calc X = B * M * X := by rw [hB, Matrix.one_mul]
    _ = B * M * Y := by rw [Matrix.mul_assoc, h, ← Matrix.mul_assoc]
    _ = Y := by rw [hB, Matrix.one_mul]

/-- **The argument common to the two statements of Proposition 4.5 for residual networks.** Let
the maps `f_ℓ` and `χ` be real-analytic, `E` of rank `d`, and `ι : M → Matrix d d ℝ` an injective
linear map such that the change of basis `exp (ι m)` at all hidden states preserves the function.
If `fd(θ) + dim M = P`, then for every neighborhood `V` of the identity, every `θ'` near `θ` with
the same function is `θ.cob (exp ι m) (exp ι m)` with `exp (ι m) ∈ V`. The orbit
`m ↦ θ.cob (exp ι m)` has the derivative `m ↦ cobDir θ (fun _ => ι m)`, injective since its `E`
component is `E ι m`; `exists_mem_orbit_of_eval_eq`. -/
private theorem exists_cobExp_of_eval_eq_rli (A : Arch T d L)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (hχ : AnalyticOnNhd ℝ A.χ Set.univ)
    (θ : Params A dIn dOut) (hE : θ.E.rank = Fintype.card d)
    {M : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M] [FiniteDimensional ℝ M]
    (ι : M →L[ℝ] Matrix d d ℝ) (hι : Function.Injective ι)
    (hfd : funDim A 1 θ + Module.finrank ℝ M = Module.finrank ℝ (Params A dIn dOut))
    (hpres : ∀ (m : M) (x : Matrix T dIn ℝ),
      eval A 1 (θ.cob (fun _ => expGL (ι m)) (fun _ => expGL (ι m))) x = eval A 1 θ x) :
    ∀ V ∈ 𝓝 (1 : Matrix d d ℝ), ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval A 1 θ' x = eval A 1 θ x) →
        ∃ m : M, NormedSpace.exp (ι m) ∈ V ∧
          θ' = θ.cob (fun _ => expGL (ι m)) (fun _ => expGL (ι m)) := by
  intro V hV
  -- the constant family `m ↦ (ι m, …, ι m)` of matrices, one per hidden state
  let κ : M →L[ℝ] (Fin (L + 1) → Matrix d d ℝ) := ContinuousLinearMap.pi fun _ => ι
  -- the orbit map `m ↦ θ.cob (exp ι m) (exp ι m)`, strictly differentiable at `0`
  obtain ⟨Φ', hΦ', hΦ'v⟩ := hasStrictFDerivAt_cobExp θ
  have hΦ'0 : HasStrictFDerivAt (cobExp θ) Φ' (κ 0) := by
    rw [map_zero]
    exact hΦ'
  have hΦ := hΦ'0.comp (0 : M) κ.hasStrictFDerivAt
  -- its derivative `m ↦ cobDir θ (fun _ => ι m)` is injective: the `E` component is `E ι m`
  have hinj : Function.Injective (Φ'.comp κ) := by
    intro m₁ m₂ h
    have h' : cobDir θ (κ m₁) = cobDir θ (κ m₂) := by
      rw [← hΦ'v, ← hΦ'v]
      exact h
    exact hι (mul_left_cancel_of_rank_rli hE (congrArg Params.E h'))
  -- it passes through `θ` and keeps the function
  have hΦ0 : (cobExp θ ∘ κ) 0 = θ := by
    show cobExp θ (κ 0) = θ
    rw [map_zero]
    exact cobExp_zero θ
  have hconst : ∀ᶠ m in 𝓝 (0 : M), ∀ x : Matrix T dIn ℝ,
      eval A 1 ((cobExp θ ∘ κ) m) x = eval A 1 θ x :=
    Eventually.of_forall fun m x => hpres m x
  -- the `m` with `exp (ι m) ∈ V` form a neighborhood of `0`
  have hcont : ContinuousAt (fun m : M => NormedSpace.exp (ι m)) 0 :=
    ContinuousAt.comp_of_eq (f := fun m : M => ι m)
      hasStrictFDerivAt_matrix_exp_zero.continuousAt ι.continuous.continuousAt (map_zero ι)
  have hV' : (fun m : M => NormedSpace.exp (ι m)) ⁻¹' V ∈ 𝓝 (0 : M) := by
    refine hcont.preimage_mem_nhds ?_
    rw [map_zero, NormedSpace.exp_zero]
    exact hV
  -- the orbit fills the level set near `θ`
  obtain ⟨U, hU, hUV⟩ := exists_mem_orbit_of_eval_eq A 1 hf hχ θ hΦ hΦ0 hinj hconst hfd _ hV'
  refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
  obtain ⟨m, hm, hmθ⟩ := hUV θ' hθ' heq
  exact ⟨m, hm, hmθ.symm⟩

/-- **Proposition 4.5 for residual networks, from the equality condition to local
identifiability, without normalization:** for real-analytic blocks, if `E` has rank `d` and
`fd(θ) = P − d²`, then for every neighborhood `V` of the identity there is a neighborhood `U` of
`θ` such that every `θ' ∈ U` with the same function is `θ` after the change of basis by one
`G ∈ V` at all hidden states. -/
theorem exists_cob_of_eval_eq_residual (A : Arch T d L) (hA : A.χ = id)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (θ : Params A dIn dOut)
    (hE : θ.E.rank = Fintype.card d)
    (hfd : funDim A 1 θ + Fintype.card d ^ 2 = Module.finrank ℝ (Params A dIn dOut)) :
    ∀ V ∈ 𝓝 (1 : Matrix d d ℝ), ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval A 1 θ' x = eval A 1 θ x) →
        ∃ G : GL d ℝ, (G : Matrix d d ℝ) ∈ V ∧ θ' = θ.cob (fun _ => G) (fun _ => G) := by
  intro V hV
  -- `χ = id` is analytic
  have hχ : AnalyticOnNhd ℝ A.χ Set.univ := by
    rw [hA]
    exact analyticOnNhd_id
  -- the `d × d` matrices form a space of dimension `d²`
  have hdimM : Module.finrank ℝ (Matrix d d ℝ) = Fintype.card d ^ 2 := by
    rw [Module.finrank_matrix]
    simp [sq]
  -- the orbit `m ↦ θ.cob (exp m) (exp m)` fills the level set near `θ` (one change of basis at all
  -- hidden states keeps the function of a residual network)
  obtain ⟨U, hU, hUV⟩ := exists_cobExp_of_eval_eq_rli A hf hχ θ hE
    (ContinuousLinearMap.id ℝ (Matrix d d ℝ)) (fun _ _ h => h) (by rw [hdimM]; exact hfd)
    (fun m x => eval_cob_residual θ x hA _) V hV
  refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
  -- `G = exp m`
  obtain ⟨m, hm, hmθ⟩ := hUV θ' hθ' heq
  exact ⟨expGL m, hm, hmθ⟩


/-- **Proposition 4.5 for residual networks, from the equality condition to local
identifiability, under pre-RMSNorm with `ε > 0`:** for real-analytic blocks, if `E` has rank `d`
and `fd(θ) = P − d(d−1)/2`, then for every neighborhood `V` of the identity there is a
neighborhood `U` of `θ` such that every `θ' ∈ U` with the same function is `θ` after the change of
basis by one orthogonal `Q ∈ V` at all hidden states. -/
theorem exists_cob_of_eval_eq_residual_rmsNorm (A : Arch T d L) {ε : ℝ} (hε : 0 < ε)
    (hA : A.χ = rmsNorm ε) (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ)
    (θ : Params A dIn dOut) (hE : θ.E.rank = Fintype.card d)
    (hfd : funDim A 1 θ + Fintype.card d * (Fintype.card d - 1) / 2
      = Module.finrank ℝ (Params A dIn dOut)) :
    ∀ V ∈ 𝓝 (1 : Matrix d d ℝ), ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval A 1 θ' x = eval A 1 θ x) →
        ∃ Q : GL d ℝ, (Q : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ ∧
          (Q : Matrix d d ℝ) ∈ V ∧ θ' = θ.cob (fun _ => Q) (fun _ => Q) := by
  intro V hV
  -- RMSNorm with `ε > 0` is analytic
  have hχ : AnalyticOnNhd ℝ A.χ Set.univ := by
    rw [hA]
    exact analyticOnNhd_rmsNorm hε
  -- the antisymmetric matrices, inside all the matrices
  let ι : antisymmetric d →L[ℝ] Matrix d d ℝ := (antisymmetric d).subtypeL
  have hι : Function.Injective ι := Subtype.val_injective
  -- the changes of basis `exp m`, `m` antisymmetric, are orthogonal
  have horth : ∀ m : antisymmetric d,
      ((expGL (ι m) : GL d ℝ) : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ :=
    fun m => exp_mem_orthogonalGroup_of_transpose_eq_neg m.2
  -- the orbit `m ↦ θ.cob (exp m) (exp m)` fills the level set near `θ` (one orthogonal change of
  -- basis at all hidden states keeps the function of a residual network under pre-RMSNorm)
  obtain ⟨U, hU, hUV⟩ := exists_cobExp_of_eval_eq_rli A hf hχ θ hE ι hι
    (by rw [finrank_antisymmetric]; exact hfd)
    (fun m x => eval_cob_residual_rmsNorm θ x ε hA _ (horth m)) V hV
  refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
  -- `Q = exp m`
  obtain ⟨m, hm, hmθ⟩ := hUV θ' hθ' heq
  exact ⟨expGL (ι m), horth m, hm, hmθ⟩

omit [Fintype T] in
/-- Helper (the private `rank_eq_of_isUnit_det_submatrix` of `Generic/Params.lean`): a matrix
with `d` columns has rank `d` if some `d` of its rows form an invertible matrix. -/
private theorem rank_eq_of_isUnit_det_submatrix_rli {m : Type*} (M : Matrix m d ℝ) (ρ : d ↪ m)
    (h : IsUnit (M.submatrix ρ id).det) : M.rank = Fintype.card d :=
  le_antisymm (Matrix.rank_le_card_width M)
    ((Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).2 h)).symm.le.trans
      (Matrix.rank_submatrix_le M ρ id))

/-- Helper (the private `ae_rank_E` of `Generic/Params.lean`): at generic parameters `E` has rank
`d`, when `d_in ≥ d`. -/
private theorem ae_rank_E_rli {A : Arch T d L} (μ : Measure (Params A dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn) :
    ∀ᵐ θ ∂μ, θ.E.rank = Fintype.card d := by
  -- `d` rows of `E`, invertible at generic parameters
  obtain ⟨ρ⟩ := Function.Embedding.nonempty_of_card_le hdIn
  filter_upwards [ae_isUnit_det_submatrix μ] with θ hθ
  exact rank_eq_of_isUnit_det_submatrix_rli θ.E ρ (hθ.2.2.1 ρ)


variable {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]

/-- **Corollary 4.9 for tanh blocks without normalization:** for `d_in, d_out ≥ d ≥ 2`, at
almost every parameter `θ` of the residual network, every `θ'` near `θ` with the same function is
`θ` after the change of basis by one invertible `G` near the identity at all hidden states. -/
theorem ae_exists_cob_of_eval_eq_tanh_residual [Nonempty T]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) Real.tanh id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, ∀ V ∈ 𝓝 (1 : Matrix d d ℝ), ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.mlp Real.tanh id hid) 1 θ' x
        = eval (Arch.mlp Real.tanh id hid) 1 θ x) →
        ∃ G : GL d ℝ, (G : Matrix d d ℝ) ∈ V ∧ θ' = θ.cob (fun _ => G) (fun _ => G) := by
  -- at generic parameters `E` has rank `d`, and `fd(θ) = P - d²` (Theorem 4.7)
  filter_upwards [ae_rank_E_rli μ hdIn, ae_funDim_tanh_residual μ hd hdIn hdOut] with θ hE hfd
  -- Proposition 4.5 at `θ`, with the analytic blocks of tanh
  exact exists_cob_of_eval_eq_residual _ rfl (fun ℓ => analyticOnNhd_f_mlp analyticOnNhd_tanh ℓ)
    θ hE hfd

/-- **Corollary 4.9 for GELU blocks without normalization:** for `d_in, d_out ≥ d ≥ 2`, at
almost every parameter `θ` of the residual network, every `θ'` near `θ` with the same function is
`θ` after the change of basis by one invertible `G` near the identity at all hidden states. -/
theorem ae_exists_cob_of_eval_eq_gelu_residual [Nonempty T]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) gelu id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, ∀ V ∈ 𝓝 (1 : Matrix d d ℝ), ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.mlp gelu id hid) 1 θ' x
        = eval (Arch.mlp gelu id hid) 1 θ x) →
        ∃ G : GL d ℝ, (G : Matrix d d ℝ) ∈ V ∧ θ' = θ.cob (fun _ => G) (fun _ => G) := by
  -- at generic parameters `E` has rank `d`, and `fd(θ) = P - d²` (Theorem 4.7)
  filter_upwards [ae_rank_E_rli μ hdIn, ae_funDim_gelu_residual μ hd hdIn hdOut] with θ hE hfd
  -- Proposition 4.5 at `θ`, with the analytic blocks of GELU
  exact exists_cob_of_eval_eq_residual _ rfl (fun ℓ => analyticOnNhd_f_mlp analyticOnNhd_gelu ℓ)
    θ hE hfd

/-- **Corollary 4.9 for tanh blocks under pre-RMSNorm with `ε > 0`:** for
`d_in, d_out ≥ d ≥ 2`, at almost every parameter `θ` of the residual network, every `θ'` near `θ`
with the same function is `θ` after the change of basis by one orthogonal `Q` near the identity at
all hidden states. -/
theorem ae_exists_cob_of_eval_eq_tanh_residual_rmsNorm [Nonempty T] {ε : ℝ} (hε : 0 < ε)
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) Real.tanh (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, ∀ V ∈ 𝓝 (1 : Matrix d d ℝ), ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.mlp Real.tanh (rmsNorm ε) hid) 1 θ' x
        = eval (Arch.mlp Real.tanh (rmsNorm ε) hid) 1 θ x) →
        ∃ Q : GL d ℝ, (Q : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ ∧
          (Q : Matrix d d ℝ) ∈ V ∧ θ' = θ.cob (fun _ => Q) (fun _ => Q) := by
  -- at generic parameters `E` has rank `d`, and `fd(θ) = P - d(d-1)/2` (Theorem 4.7)
  filter_upwards [ae_rank_E_rli μ hdIn, ae_funDim_tanh_residual_rmsNorm hε μ hd hdIn hdOut]
    with θ hE hfd
  -- Proposition 4.5 under pre-RMSNorm at `θ`, with the analytic blocks of tanh
  exact exists_cob_of_eval_eq_residual_rmsNorm _ hε rfl
    (fun ℓ => analyticOnNhd_f_mlp analyticOnNhd_tanh ℓ) θ hE hfd

/-- **Corollary 4.9 for GELU blocks under pre-RMSNorm with `ε > 0`:** for
`d_in, d_out ≥ d ≥ 2`, at almost every parameter `θ` of the residual network, every `θ'` near `θ`
with the same function is `θ` after the change of basis by one orthogonal `Q` near the identity at
all hidden states. -/
theorem ae_exists_cob_of_eval_eq_gelu_residual_rmsNorm [Nonempty T] {ε : ℝ} (hε : 0 < ε)
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, ∀ V ∈ 𝓝 (1 : Matrix d d ℝ), ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.mlp gelu (rmsNorm ε) hid) 1 θ' x
        = eval (Arch.mlp gelu (rmsNorm ε) hid) 1 θ x) →
        ∃ Q : GL d ℝ, (Q : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ ∧
          (Q : Matrix d d ℝ) ∈ V ∧ θ' = θ.cob (fun _ => Q) (fun _ => Q) := by
  -- at generic parameters `E` has rank `d`, and `fd(θ) = P - d(d-1)/2` (Theorem 4.7)
  filter_upwards [ae_rank_E_rli μ hdIn, ae_funDim_gelu_residual_rmsNorm hε μ hd hdIn hdOut]
    with θ hE hfd
  -- Proposition 4.5 under pre-RMSNorm at `θ`, with the analytic blocks of GELU
  exact exists_cob_of_eval_eq_residual_rmsNorm _ hε rfl
    (fun ℓ => analyticOnNhd_f_mlp analyticOnNhd_gelu ℓ) θ hE hfd

end Skips
