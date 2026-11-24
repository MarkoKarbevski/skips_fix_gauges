import SkipsLean.Dimension.OrbitNetwork
import SkipsLean.Dimension.ExpOrbitGated
import SkipsLean.Generic.Gated
import SkipsLean.Residual.UpperBoundSymmetries
import SkipsLean.Residual.DepthGated
import SkipsLean.Residual.DepthGatedRMS

/-!
# Residual networks of gated blocks are locally identifiable

Paper (skips paper): Definition 4.4, Proposition 4.5 and Corollary 4.9.

"Corollary 4.9 (Residual networks are locally identifiable). Let the blocks be analytic, with or
without pre-RMSNorm, and let `θ` be generic parameters of the residual network. Every `θ'` near
`θ` with the same function is obtained from `θ` by symmetries inside the blocks and by one matrix
`G ∈ 𝒢`, all close to the identity. The matrix `G` is the same at all hidden states: for every
block `ℓ`, `E ↦ E G`, `W_read^ℓ ↦ G⁻¹ W_read^ℓ`, `W_write^ℓ ↦ W_write^ℓ G`, `D ↦ G⁻¹ D`."

Stated here, for residual networks of gated blocks (`s` is the number of hidden units of the
network; the symmetries inside the blocks are the rescalings of the values of the hidden units):

* The direction of Proposition 4.5 from the equality condition to local identifiability, at one
  parameter, for a real-analytic gate: if `E` has rank `d`, no value column of a read vanishes and
  the functional dimension at `θ` is `P − d² − s`, resp. `P − d(d−1)/2 − s` under pre-RMSNorm with
  `ε > 0`, then every `θ'` near `θ` with the same function is
  `(θ.rescale c).cob (fun _ => G) (fun _ => G)` with factors `c > 0` near `1` and one invertible
  (resp. orthogonal) `G` near the identity.
* Corollary 4.9 for SwiGLU and GeGLU blocks, without normalization and under pre-RMSNorm with
  `ε > 0`: this holds at almost every parameter (Theorem 4.7 gives the functional dimension).

The twin for networks without skip connections is `Dimension/LocalIdentifiabilityGated.lean`; the
blocks without symmetries inside are in `Residual/LocalIdentifiability.lean`. All use
`exists_mem_orbit_of_eval_eq` (`Dimension/OrbitNetwork.lean`) and `θ.rescale c`
(`Dimension/RescaleAction.lean`). Not stated here: the converse direction of Proposition 4.5,
attention blocks, and the case `ε = 0`.
-/

namespace Skips

open Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {σ : ℝ → ℝ} {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]

/-- Helper (the private `cancel_left_of_rank` of `Dimension/Rescaling.lean`): a matrix `M` of rank
equal to its number of columns cancels on the left, `M X = M Y → X = Y` (its kernel is `0` by
rank–nullity). -/
private theorem cancel_left_of_rank_rlig {m n k : Type*} [Fintype n] (M : Matrix m n ℝ)
    (hM : M.rank = Fintype.card n) {X Y : Matrix n k ℝ} (h : M * X = M * Y) : X = Y := by
  -- `v ↦ M v` is injective: `rank M + dim ker M = card n`
  have hinj : Function.Injective M.mulVecLin := by
    rw [← LinearMap.ker_eq_bot, ← Submodule.finrank_eq_zero]
    have := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
    rw [Module.finrank_fintype_fun_eq_card] at this
    rw [Matrix.rank] at hM
    omega
  -- compare `X` and `Y` column by column
  ext i j
  have hcol : M.mulVecLin (fun l => X l j) = M.mulVecLin (fun l => Y l j) := by
    funext p
    have := congrFun (congrFun h p) j
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
  exact congrFun (hinj hcol) i

/-- **The argument common to the two statements of Proposition 4.5 for gated blocks.** Let `σ` and
`χ` be real-analytic, `E` of rank `d`, no value column of a read zero, and `ι₀ : N → Matrix d d ℝ`
an injective linear map (all matrices, or the antisymmetric ones) such that the change of basis
`exp (ι₀ n)` at all hidden states preserves the function of every residual network of these
blocks. If `fd(θ) + dim N + s = P`, then every `θ'` near `θ` with the same function is
`(θ.rescale c).cob (exp ι₀ n) (exp ι₀ n)` with `exp (ι₀ n) ∈ V`, `c ∈ W`, `c > 0`. The proof:
`exists_mem_orbit_of_eval_eq` for the map `(n, α) ↦ cobExpRescale θ (fun _ => ι₀ n, α)`, whose
derivative `(n, α) ↦ cobDir θ (fun _ => ι₀ n) + rescaleDir θ α` is injective. -/
private theorem exists_cobExpRescale_of_eval_eq_rlig {χ : Matrix T d ℝ → Matrix T d ℝ}
    (hσ : AnalyticOnNhd ℝ σ Set.univ) (hχ : AnalyticOnNhd ℝ χ Set.univ)
    (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d)
    (hv : ∀ ℓ i, (fun k => θ.read ℓ k (Sum.inr i)) ≠ 0)
    {N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N] [FiniteDimensional ℝ N]
    (ι₀ : N →L[ℝ] Matrix d d ℝ) (hι₀ : Function.Injective ι₀)
    (hfd : funDim (Arch.gated σ χ hid) 1 θ + (Module.finrank ℝ N + ∑ ℓ, Fintype.card (hid ℓ))
      = Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut))
    (hpres : ∀ (n : N) (η : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut)
      (x : Matrix T dIn ℝ), eval (Arch.gated σ χ hid) 1
        (η.cob (fun _ => expGL (ι₀ n)) (fun _ => expGL (ι₀ n))) x
        = eval (Arch.gated σ χ hid) 1 η x) :
    ∀ V ∈ 𝓝 (1 : Matrix d d ℝ), ∀ W ∈ 𝓝 (1 : ∀ ℓ, hid ℓ → ℝ), ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.gated σ χ hid) 1 θ' x
        = eval (Arch.gated σ χ hid) 1 θ x) →
        ∃ (n : N) (c : ∀ ℓ, hid ℓ → ℝ), NormedSpace.exp (ι₀ n) ∈ V ∧ c ∈ W ∧
          (∀ ℓ i, 0 < c ℓ i) ∧
          θ' = (θ.rescale c).cob (fun _ => expGL (ι₀ n)) (fun _ => expGL (ι₀ n)) := by
  intro V hV W hW
  -- the embedding `(n, α) ↦ (fun _ => ι₀ n, α)`: the same matrix at every hidden state
  let ι : (N × (∀ ℓ, hid ℓ → ℝ)) →L[ℝ] (Fin (L + 1) → Matrix d d ℝ) × (∀ ℓ, hid ℓ → ℝ) :=
    (ContinuousLinearMap.pi fun _ : Fin (L + 1) =>
      ι₀.comp (ContinuousLinearMap.fst ℝ N (∀ ℓ, hid ℓ → ℝ))).prod
      (ContinuousLinearMap.snd ℝ N (∀ ℓ, hid ℓ → ℝ))
  -- the map `(n, α) ↦ (θ.rescale (e^α)).cob (exp ι₀ n) (exp ι₀ n)`, strictly differentiable at `0`
  obtain ⟨Φ', hΦ', hΦ'v⟩ := hasStrictFDerivAt_cobExpRescale θ
  have hΦ'0 : HasStrictFDerivAt (cobExpRescale θ) Φ' (ι 0) := by
    rw [map_zero]
    exact hΦ'
  have hΦ := hΦ'0.comp (0 : N × (∀ ℓ, hid ℓ → ℝ)) ι.hasStrictFDerivAt
  have hΦ0 : cobExpRescale θ (ι 0) = θ := by
    rw [map_zero]
    exact cobExpRescale_zero θ
  -- its derivative `(n, α) ↦ cobDir θ (fun _ => ι₀ n) + rescaleDir θ α` is injective
  have hinj : Function.Injective (Φ'.comp ι) := by
    rintro ⟨n, α⟩ ⟨n', α'⟩ h
    have h' : cobDir θ (fun _ => ι₀ n) + rescaleDir θ α
        = cobDir θ (fun _ => ι₀ n') + rescaleDir θ α' :=
      (hΦ'v (ι (n, α))).symm.trans (h.trans (hΦ'v (ι (n', α'))))
    -- the `E` component: `E ι₀ n = E ι₀ n'` (the rescalings leave `E` alone), and `E` has rank `d`
    have h0 : θ.E * ι₀ n = θ.E * ι₀ n' := by
      have hE0 := congrArg Params.E h'
      change θ.E * ι₀ n + 0 = θ.E * ι₀ n' + 0 at hE0
      rwa [add_zero, add_zero] at hE0
    have hn : ι₀ n = ι₀ n' := cancel_left_of_rank_rlig θ.E hE h0
    -- the value column `e_i` of block `ℓ` moves by `-ι₀ n e_i - α_i e_i`; the first terms agree,
    -- and an entry `k` with `e_i k ≠ 0` gives `α_i = α'_i`
    have hα : α = α' := by
      funext ℓ i
      obtain ⟨k, hk⟩ := Function.ne_iff.mp (hv ℓ i)
      have hr := congrFun (congrFun (congrArg (fun η => η.read ℓ) h') k) (Sum.inr i)
      change -(ι₀ n * θ.read ℓ) k (Sum.inr i) + -(α ℓ i) * θ.read ℓ k (Sum.inr i) =
        -(ι₀ n' * θ.read ℓ) k (Sum.inr i) + -(α' ℓ i) * θ.read ℓ k (Sum.inr i) at hr
      rw [hn, add_right_inj] at hr
      exact neg_inj.mp (mul_right_cancel₀ hk hr)
    rw [hι₀ hn, hα]
  -- it keeps the function: a rescaling of the values, then one change of basis
  have hconst : ∀ᶠ p in 𝓝 (0 : N × (∀ ℓ, hid ℓ → ℝ)), ∀ x : Matrix T dIn ℝ,
      eval (Arch.gated σ χ hid) 1 ((cobExpRescale θ ∘ ι) p) x
        = eval (Arch.gated σ χ hid) 1 θ x := by
    refine Eventually.of_forall fun p x => ?_
    have h1 : (cobExpRescale θ ∘ ι) p = (θ.rescale fun ℓ i => Real.exp (p.2 ℓ i)).cob
        (fun _ => expGL (ι₀ p.1)) (fun _ => expGL (ι₀ p.1)) := rfl
    rw [h1, hpres]
    exact eval_rescale_params θ _ (fun ℓ i => (Real.exp_pos _).ne') 1 x
  -- the dimension of `N × (∀ ℓ, hid ℓ → ℝ)`
  have hdim : Module.finrank ℝ (N × (∀ ℓ, hid ℓ → ℝ))
      = Module.finrank ℝ N + ∑ ℓ, Fintype.card (hid ℓ) := by
    rw [Module.finrank_prod, Module.finrank_pi_fintype]
    simp only [Module.finrank_fintype_fun_eq_card]
  -- the `(n, α)` with `exp (ι₀ n) ∈ V` and `e^α ∈ W` form a neighborhood of `0`
  have hexp : ContinuousAt (fun Y : Matrix d d ℝ => NormedSpace.exp Y) 0 :=
    hasStrictFDerivAt_matrix_exp_zero.continuousAt
  have hV' : (fun p : N × (∀ ℓ, hid ℓ → ℝ) => NormedSpace.exp (ι₀ p.1)) ⁻¹' V
      ∈ 𝓝 (0 : N × (∀ ℓ, hid ℓ → ℝ)) := by
    have hc : ContinuousAt (fun p : N × (∀ ℓ, hid ℓ → ℝ) => NormedSpace.exp (ι₀ p.1)) 0 :=
      ContinuousAt.comp_of_eq (f := fun p : N × (∀ ℓ, hid ℓ → ℝ) => ι₀ p.1) hexp
        (ι₀.continuous.comp continuous_fst).continuousAt (by simp only [Prod.fst_zero, map_zero])
    refine hc.preimage_mem_nhds ?_
    have h1 : NormedSpace.exp (ι₀ (0 : N × (∀ ℓ, hid ℓ → ℝ)).1) = (1 : Matrix d d ℝ) := by
      rw [Prod.fst_zero, map_zero, NormedSpace.exp_zero]
    rw [h1]
    exact hV
  have hW' : (fun p : N × (∀ ℓ, hid ℓ → ℝ) => fun ℓ i => Real.exp (p.2 ℓ i)) ⁻¹' W
      ∈ 𝓝 (0 : N × (∀ ℓ, hid ℓ → ℝ)) := by
    have hc : Continuous
        (fun p : N × (∀ ℓ, hid ℓ → ℝ) => fun ℓ (i : hid ℓ) => Real.exp (p.2 ℓ i)) :=
      continuous_pi fun ℓ => continuous_pi fun i => Real.continuous_exp.comp
        ((continuous_apply i).comp ((continuous_apply ℓ).comp continuous_snd))
    refine hc.continuousAt.preimage_mem_nhds ?_
    have h1 : (fun ℓ (i : hid ℓ) => Real.exp ((0 : N × (∀ ℓ, hid ℓ → ℝ)).2 ℓ i))
        = (1 : ∀ ℓ, hid ℓ → ℝ) := by
      funext ℓ i
      simp only [Prod.snd_zero, Pi.zero_apply, Real.exp_zero, Pi.one_apply]
    rw [h1]
    exact hW
  -- the orbit fills the level set near `θ`
  obtain ⟨U, hU, hUV⟩ := exists_mem_orbit_of_eval_eq (Arch.gated σ χ hid) 1
    (fun ℓ => analyticOnNhd_f_gated hσ ℓ) hχ θ hΦ hΦ0 hinj hconst (by rw [hdim]; exact hfd) _
    (Filter.inter_mem hV' hW')
  refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
  obtain ⟨p, hp, hpθ⟩ := hUV θ' hθ' heq
  exact ⟨p.1, fun ℓ i => Real.exp (p.2 ℓ i), hp.1, hp.2, fun ℓ i => Real.exp_pos _, hpθ.symm⟩

/-- **Proposition 4.5 for residual networks of gated blocks, from the equality condition to
local identifiability, without normalization:** for a real-analytic gate `σ`, if `E` has rank `d`,
no value column of a read vanishes and `fd(θ) = P − d² − s`, then every `θ'` near `θ` with the
same function is `θ` after a rescaling of the values of the hidden units by factors `c` near `1`
and the change of basis by one invertible `G` near the identity at all hidden states. -/
theorem exists_cob_rescale_of_eval_eq_residual_gated (hσ : AnalyticOnNhd ℝ σ Set.univ)
    (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d)
    (hv : ∀ ℓ i, (fun k => θ.read ℓ k (Sum.inr i)) ≠ 0)
    (hfd : funDim (Arch.gated σ id hid) 1 θ
        + (Fintype.card d ^ 2 + ∑ ℓ, Fintype.card (hid ℓ))
      = Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)) :
    ∀ V ∈ 𝓝 (1 : Matrix d d ℝ), ∀ W ∈ 𝓝 (1 : ∀ ℓ, hid ℓ → ℝ), ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.gated σ id hid) 1 θ' x
        = eval (Arch.gated σ id hid) 1 θ x) →
        ∃ (G : GL d ℝ) (c : ∀ ℓ, hid ℓ → ℝ), (G : Matrix d d ℝ) ∈ V ∧ c ∈ W ∧
          (∀ ℓ i, 0 < c ℓ i) ∧ θ' = (θ.rescale c).cob (fun _ => G) (fun _ => G) := by
  intro V hV W hW
  -- the `d × d` matrices form a space of dimension `d²`
  have hdimM : Module.finrank ℝ (Matrix d d ℝ) = Fintype.card d ^ 2 := by
    rw [Module.finrank_matrix, Module.finrank_self, mul_one, sq]
  -- the orbit of the rescalings and of one change of basis `exp m` fills the level set near `θ`
  -- (Proposition 3.2 with identity skips for the invariance)
  obtain ⟨U, hU, hUV⟩ := exists_cobExpRescale_of_eval_eq_rlig hσ analyticOnNhd_id θ hE hv
    (ContinuousLinearMap.id ℝ (Matrix d d ℝ)) (fun _ _ h => h) (by rw [hdimM]; exact hfd)
    (fun m η x => eval_cob_residual η x rfl _) V hV W hW
  refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
  -- `G = exp m`, `c = e^α`
  obtain ⟨m, c, hm, hc, hc0, hθ'⟩ := hUV θ' hθ' heq
  exact ⟨expGL m, c, hm, hc, hc0, hθ'⟩

/-- **Proposition 4.5 for residual networks of gated blocks, from the equality condition to
local identifiability, under pre-RMSNorm with `ε > 0`:** for a real-analytic gate `σ`, if `E` has
rank `d`, no value column of a read vanishes and `fd(θ) = P − d(d−1)/2 − s`, then every `θ'` near
`θ` with the same function is `θ` after a rescaling of the values of the hidden units by factors
`c` near `1` and the change of basis by one orthogonal `Q` near the identity at all hidden
states. -/
theorem exists_cob_rescale_of_eval_eq_residual_gated_rmsNorm {ε : ℝ} (hε : 0 < ε)
    (hσ : AnalyticOnNhd ℝ σ Set.univ)
    (θ : Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d)
    (hv : ∀ ℓ i, (fun k => θ.read ℓ k (Sum.inr i)) ≠ 0)
    (hfd : funDim (Arch.gated σ (rmsNorm ε) hid) 1 θ
        + (Fintype.card d * (Fintype.card d - 1) / 2 + ∑ ℓ, Fintype.card (hid ℓ))
      = Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)) :
    ∀ V ∈ 𝓝 (1 : Matrix d d ℝ), ∀ W ∈ 𝓝 (1 : ∀ ℓ, hid ℓ → ℝ), ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.gated σ (rmsNorm ε) hid) 1 θ' x
        = eval (Arch.gated σ (rmsNorm ε) hid) 1 θ x) →
        ∃ (Q : GL d ℝ) (c : ∀ ℓ, hid ℓ → ℝ),
          (Q : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ ∧ (Q : Matrix d d ℝ) ∈ V ∧ c ∈ W ∧
          (∀ ℓ i, 0 < c ℓ i) ∧ θ' = (θ.rescale c).cob (fun _ => Q) (fun _ => Q) := by
  intro V hV W hW
  -- the antisymmetric matrices, inside all the matrices
  let ι₀ : antisymmetric d →L[ℝ] Matrix d d ℝ := (antisymmetric d).subtypeL
  have hι₀ : Function.Injective ι₀ := Subtype.val_injective
  -- the changes of basis `exp m`, `m` antisymmetric, are orthogonal
  have horth : ∀ m : antisymmetric d,
      ((expGL (ι₀ m) : GL d ℝ) : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ :=
    fun m => exp_mem_orthogonalGroup_of_transpose_eq_neg m.2
  -- the orbit of the rescalings and of one orthogonal change of basis `exp m` fills the level
  -- set near `θ` (Proposition 3.2 under pre-RMSNorm with identity skips for the invariance)
  obtain ⟨U, hU, hUV⟩ := exists_cobExpRescale_of_eval_eq_rlig hσ (analyticOnNhd_rmsNorm hε) θ
    hE hv ι₀ hι₀ (by rw [finrank_antisymmetric]; exact hfd)
    (fun m η x => eval_cob_residual_rmsNorm η x ε rfl _ (horth m)) V hV W hW
  refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
  -- `Q = exp m`, `c = e^α`
  obtain ⟨m, c, hm, hc, hc0, hθ'⟩ := hUV θ' hθ' heq
  exact ⟨expGL (ι₀ m), c, horth m, hm, hc, hc0, hθ'⟩

/-- Helper (the private `rank_eq_of_isUnit_det_submatrix` of `Generic/Params.lean`): a matrix
with `d` columns has rank `d` if some `d` of its rows form an invertible matrix. -/
private theorem rank_eq_of_isUnit_det_submatrix_rlig {m : Type*} (M : Matrix m d ℝ) (ρ : d ↪ m)
    (h : IsUnit (M.submatrix ρ id).det) : M.rank = Fintype.card d :=
  le_antisymm (Matrix.rank_le_card_width M)
    ((Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).2 h)).symm.le.trans
      (Matrix.rank_submatrix_le M ρ id))

/-- Helper (the private `ae_rank_E` of `Generic/Params.lean`): at generic parameters `E` has rank
`d`, when `d_in ≥ d`. -/
private theorem ae_rank_E_rlig {A : Arch T d L} (μ : Measure (Params A dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn) :
    ∀ᵐ θ ∂μ, θ.E.rank = Fintype.card d := by
  -- `d` rows of `E`, invertible at generic parameters
  obtain ⟨ρ⟩ := Function.Embedding.nonempty_of_card_le hdIn
  filter_upwards [ae_isUnit_det_submatrix μ] with θ hθ
  exact rank_eq_of_isUnit_det_submatrix_rlig θ.E ρ (hθ.2.2.1 ρ)

/-- **Corollary 4.9 for SwiGLU blocks without normalization:** for `d_in, d_out ≥ d ≥ 2`, at almost
every parameter `θ` of the residual network, every `θ'` near `θ` with the same function is `θ` after
a rescaling of the value of each hidden unit, close to `1`, and the change of basis by one
invertible `G` near the identity at all hidden states. -/
theorem ae_exists_cob_rescale_of_eval_eq_swiglu_residual [Nonempty T]
    (μ : Measure (Params (Arch.gated (T := T) (d := d) silu id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, ∀ V ∈ 𝓝 (1 : Matrix d d ℝ), ∀ W ∈ 𝓝 (1 : ∀ ℓ, hid ℓ → ℝ), ∃ U ∈ 𝓝 θ,
      ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.gated silu id hid) 1 θ' x
        = eval (Arch.gated silu id hid) 1 θ x) →
        ∃ (G : GL d ℝ) (c : ∀ ℓ, hid ℓ → ℝ), (G : Matrix d d ℝ) ∈ V ∧ c ∈ W ∧
          (∀ ℓ i, 0 < c ℓ i) ∧ θ' = (θ.rescale c).cob (fun _ => G) (fun _ => G) := by
  -- `d ≥ 2`, so `d` is not empty
  have : Nonempty d := Fintype.card_pos_iff.mp (by omega)
  -- at generic parameters `E` has rank `d`, no value column of a read vanishes, and
  -- `fd(θ) = P - d² - s` (Theorem 4.7)
  filter_upwards [ae_rank_E_rlig μ hdIn, ae_value_ne_zero μ,
    ae_funDim_swiglu_residual μ hd hdIn hdOut] with θ hE hv hfd
  -- Proposition 4.5 at `θ`, with the analytic gate SiLU
  exact exists_cob_rescale_of_eval_eq_residual_gated analyticOnNhd_silu θ hE hv hfd

/-- **Corollary 4.9 for SwiGLU blocks under pre-RMSNorm with `ε > 0`:** for `d_in, d_out ≥ d ≥ 2`,
at almost every parameter `θ` of the residual network, every `θ'` near `θ` with the same function is
`θ` after a rescaling of the value of each hidden unit, close to `1`, and the change of basis by one
orthogonal `Q` near the identity at all hidden states. -/
theorem ae_exists_cob_rescale_of_eval_eq_swiglu_residual_rmsNorm [Nonempty T] {ε : ℝ} (hε : 0 < ε)
    (μ : Measure (Params (Arch.gated (T := T) (d := d) silu (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, ∀ V ∈ 𝓝 (1 : Matrix d d ℝ), ∀ W ∈ 𝓝 (1 : ∀ ℓ, hid ℓ → ℝ), ∃ U ∈ 𝓝 θ,
      ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.gated silu (rmsNorm ε) hid) 1 θ' x
        = eval (Arch.gated silu (rmsNorm ε) hid) 1 θ x) →
        ∃ (Q : GL d ℝ) (c : ∀ ℓ, hid ℓ → ℝ),
          (Q : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ ∧ (Q : Matrix d d ℝ) ∈ V ∧ c ∈ W ∧
          (∀ ℓ i, 0 < c ℓ i) ∧ θ' = (θ.rescale c).cob (fun _ => Q) (fun _ => Q) := by
  -- `d ≥ 2`, so `d` is not empty
  have : Nonempty d := Fintype.card_pos_iff.mp (by omega)
  -- at generic parameters `E` has rank `d`, no value column of a read vanishes, and
  -- `fd(θ) = P - d(d-1)/2 - s` (Theorem 4.7 under pre-RMSNorm)
  filter_upwards [ae_rank_E_rlig μ hdIn, ae_value_ne_zero μ,
    ae_funDim_swiglu_residual_rmsNorm hε μ hd hdIn hdOut] with θ hE hv hfd
  -- Proposition 4.5 under pre-RMSNorm at `θ`, with the analytic gate SiLU
  exact exists_cob_rescale_of_eval_eq_residual_gated_rmsNorm hε analyticOnNhd_silu θ hE hv hfd

/-- **Corollary 4.9 for GeGLU blocks without normalization:** for `d_in, d_out ≥ d ≥ 2`, at almost
every parameter `θ` of the residual network, every `θ'` near `θ` with the same function is `θ` after
a rescaling of the value of each hidden unit, close to `1`, and the change of basis by one
invertible `G` near the identity at all hidden states. -/
theorem ae_exists_cob_rescale_of_eval_eq_geglu_residual [Nonempty T]
    (μ : Measure (Params (Arch.gated (T := T) (d := d) gelu id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, ∀ V ∈ 𝓝 (1 : Matrix d d ℝ), ∀ W ∈ 𝓝 (1 : ∀ ℓ, hid ℓ → ℝ), ∃ U ∈ 𝓝 θ,
      ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.gated gelu id hid) 1 θ' x
        = eval (Arch.gated gelu id hid) 1 θ x) →
        ∃ (G : GL d ℝ) (c : ∀ ℓ, hid ℓ → ℝ), (G : Matrix d d ℝ) ∈ V ∧ c ∈ W ∧
          (∀ ℓ i, 0 < c ℓ i) ∧ θ' = (θ.rescale c).cob (fun _ => G) (fun _ => G) := by
  -- `d ≥ 2`, so `d` is not empty
  have : Nonempty d := Fintype.card_pos_iff.mp (by omega)
  -- at generic parameters `E` has rank `d`, no value column of a read vanishes, and
  -- `fd(θ) = P - d² - s` (Theorem 4.7)
  filter_upwards [ae_rank_E_rlig μ hdIn, ae_value_ne_zero μ,
    ae_funDim_geglu_residual μ hd hdIn hdOut] with θ hE hv hfd
  -- Proposition 4.5 at `θ`, with the analytic gate GELU
  exact exists_cob_rescale_of_eval_eq_residual_gated analyticOnNhd_gelu θ hE hv hfd

/-- **Corollary 4.9 for GeGLU blocks under pre-RMSNorm with `ε > 0`:** for `d_in, d_out ≥ d ≥ 2`, at
almost every parameter `θ` of the residual network, every `θ'` near `θ` with the same function is
`θ` after a rescaling of the value of each hidden unit, close to `1`, and the change of basis by one
orthogonal `Q` near the identity at all hidden states. -/
theorem ae_exists_cob_rescale_of_eval_eq_geglu_residual_rmsNorm [Nonempty T] {ε : ℝ} (hε : 0 < ε)
    (μ : Measure (Params (Arch.gated (T := T) (d := d) gelu (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, ∀ V ∈ 𝓝 (1 : Matrix d d ℝ), ∀ W ∈ 𝓝 (1 : ∀ ℓ, hid ℓ → ℝ), ∃ U ∈ 𝓝 θ,
      ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.gated gelu (rmsNorm ε) hid) 1 θ' x
        = eval (Arch.gated gelu (rmsNorm ε) hid) 1 θ x) →
        ∃ (Q : GL d ℝ) (c : ∀ ℓ, hid ℓ → ℝ),
          (Q : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ ∧ (Q : Matrix d d ℝ) ∈ V ∧ c ∈ W ∧
          (∀ ℓ i, 0 < c ℓ i) ∧ θ' = (θ.rescale c).cob (fun _ => Q) (fun _ => Q) := by
  -- `d ≥ 2`, so `d` is not empty
  have : Nonempty d := Fintype.card_pos_iff.mp (by omega)
  -- at generic parameters `E` has rank `d`, no value column of a read vanishes, and
  -- `fd(θ) = P - d(d-1)/2 - s` (Theorem 4.7 under pre-RMSNorm)
  filter_upwards [ae_rank_E_rlig μ hdIn, ae_value_ne_zero μ,
    ae_funDim_geglu_residual_rmsNorm hε μ hd hdIn hdOut] with θ hE hv hfd
  -- Proposition 4.5 under pre-RMSNorm at `θ`, with the analytic gate GELU
  exact exists_cob_rescale_of_eval_eq_residual_gated_rmsNorm hε analyticOnNhd_gelu θ hE hv hfd

end Skips
