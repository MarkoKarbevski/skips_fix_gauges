import SkipsLean.Dimension.OrbitNetwork
import SkipsLean.Dimension.ExpOrbitGated
import SkipsLean.Generic.Gated
import SkipsLean.Depth.GeluGatedTheorem

/-!
# Local identifiability up to the changes of basis and the rescalings: gated blocks

Paper (dimension paper): Definition 4.5, Proposition 4.6 and Corollary 5.3.

"Proposition 4.6 (The equality condition and local identifiability). Let the blocks be tanh, GELU,
SwiGLU, GeGLU or attention blocks, without normalization or under pre-RMSNorm. A network satisfies
the equality condition if and only if, at generic parameters, it is locally identifiable up to its
symmetries. Every symmetry that is needed is then close to the identity."

"Corollary 5.3 (Local identifiability). Without normalization or under pre-RMSNorm with `ε > 0`, in
the cases of Theorem 5.2, let `θ` be generic parameters. Every `θ'` near `θ` with the same function
is obtained from `θ` by matrices `G_0, …, G_L ∈ 𝒢` close to the identity, one per hidden state, as
in Proposition 3.2, and for SwiGLU and GeGLU blocks by a rescaling of the value of each hidden
unit, close to 1."

Stated here, for networks of gated blocks without skip connections (`s` is the number of hidden
units of the network):

* The direction of Proposition 4.6 from the equality condition to local identifiability, at one
  parameter, for a real-analytic gate: if `E` and the writes have rank `d`, no value column of a
  read vanishes (the conditions of Lemma B.1) and the functional dimension at `θ` is
  `P − (L+1) d² − s`, resp. `P − (L+1) d(d−1)/2 − s` under pre-RMSNorm with `ε > 0`, then every
  `θ'` near `θ` with the same function is `(θ.rescale c).cob G G` with factors `c > 0` near `1` and
  invertible (resp. orthogonal) `G_0, …, G_L` near the identity.
* Corollary 5.3 for SwiGLU and GeGLU blocks, without normalization and under pre-RMSNorm with
  `ε > 0`: this holds at almost every parameter.

The blocks without symmetries inside are in `Dimension/LocalIdentifiability.lean`; residual
networks in `Residual/LocalIdentifiability.lean` and `Residual/LocalIdentifiabilityGated.lean`.
All use `exists_mem_orbit_of_eval_eq` (`Dimension/OrbitNetwork.lean`). `θ.rescale c` divides the
value column of hidden unit `i` of block `ℓ` by `c ℓ i` and multiplies its write row by `c ℓ i`
(`Dimension/RescaleAction.lean`). Not stated here: the converse direction of Proposition 4.6 and
attention blocks.
-/

namespace Skips

open Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {σ : ℝ → ℝ} {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]

/-- **The argument common to the two statements of Proposition 4.6 for gated blocks.** Let the
gate `σ` and the map `χ` be real-analytic, `E` and the writes of rank `d`, no value column of a read
zero, and `ι : M → (Fin (L+1) → Matrix d d ℝ) × (∀ ℓ, hid ℓ → ℝ)` an injective linear map such that
the rescalings `e^{(ι m).2}` followed by the changes of basis `exp (ι m).1` preserve the function.
If `fd(θ) + dim M = P`, then every `θ'` near `θ` with the same function is
`cobExpRescale θ (ι m)` with `exp (ι m).1 ∈ V` and `e^{(ι m).2} ∈ W`. The proof: the derivative of
`m ↦ cobExpRescale θ (ι m)` at `0` is `m ↦ cobDir θ (ι m).1 + rescaleDir θ (ι m).2`, injective
(Lemma B.1), and `exists_mem_orbit_of_eval_eq`. -/
private theorem exists_cobExpRescale_of_eval_eq_lig {χ : Matrix T d ℝ → Matrix T d ℝ}
    (hσ : AnalyticOnNhd ℝ σ Set.univ) (hχ : AnalyticOnNhd ℝ χ Set.univ)
    (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d) (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d)
    (hv : ∀ ℓ i, (fun k => θ.read ℓ k (Sum.inr i)) ≠ 0)
    {M : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M] [FiniteDimensional ℝ M]
    (ι : M →L[ℝ] (Fin (L + 1) → Matrix d d ℝ) × (∀ ℓ, hid ℓ → ℝ)) (hι : Function.Injective ι)
    (hfd : funDim (Arch.gated σ χ hid) 0 θ + Module.finrank ℝ M
      = Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut))
    (hpres : ∀ (m : M) (x : Matrix T dIn ℝ),
      eval (Arch.gated σ χ hid) 0 (cobExpRescale θ (ι m)) x = eval (Arch.gated σ χ hid) 0 θ x) :
    ∀ V ∈ 𝓝 (1 : Fin (L + 1) → Matrix d d ℝ), ∀ W ∈ 𝓝 (1 : ∀ ℓ, hid ℓ → ℝ), ∃ U ∈ 𝓝 θ,
      ∀ θ' ∈ U, (∀ x : Matrix T dIn ℝ, eval (Arch.gated σ χ hid) 0 θ' x
        = eval (Arch.gated σ χ hid) 0 θ x) →
        ∃ m : M, (fun ℓ => NormedSpace.exp ((ι m).1 ℓ)) ∈ V ∧
          (fun ℓ i => Real.exp ((ι m).2 ℓ i)) ∈ W ∧ θ' = cobExpRescale θ (ι m) := by
  intro V hV W hW
  -- the orbit map `(m, α) ↦ (θ.rescale (e^α)).cob (exp m) (exp m)`, strictly differentiable at `0`
  obtain ⟨Φ', hΦ', hΦ'v⟩ := hasStrictFDerivAt_cobExpRescale θ
  have hΦ'0 : HasStrictFDerivAt (cobExpRescale θ) Φ' (ι 0) := by
    rw [map_zero]
    exact hΦ'
  have hΦ := hΦ'0.comp (0 : M) ι.hasStrictFDerivAt
  -- its derivative `m ↦ cobDir θ (ι m).1 + rescaleDir θ (ι m).2` is injective (Lemma B.1)
  have hinj : Function.Injective (Φ'.comp ι) := by
    intro m₁ m₂ h
    have h' : cobDir θ (ι m₁).1 + rescaleDir θ (ι m₁).2
        = cobDir θ (ι m₂).1 + rescaleDir θ (ι m₂).2 := by
      rw [← hΦ'v, ← hΦ'v]
      exact h
    exact hι (cobDir_add_rescaleDir_injective θ hE hw hv h')
  -- it passes through `θ` and keeps the function
  have hΦ0 : (cobExpRescale θ ∘ ι) 0 = θ := by
    rw [Function.comp_apply, map_zero]
    exact cobExpRescale_zero θ
  have hconst : ∀ᶠ m in 𝓝 (0 : M), ∀ x : Matrix T dIn ℝ,
      eval (Arch.gated σ χ hid) 0 ((cobExpRescale θ ∘ ι) m) x
        = eval (Arch.gated σ χ hid) 0 θ x :=
    Eventually.of_forall fun m x => hpres m x
  -- the `m` with `exp (ι m).1 ∈ V` and `e^{(ι m).2} ∈ W` form a neighborhood of `0`
  have hexp : ContinuousAt (fun Y : Matrix d d ℝ => NormedSpace.exp Y) 0 :=
    hasStrictFDerivAt_matrix_exp_zero.continuousAt
  have hcV : ContinuousAt (fun m : M => fun ℓ => NormedSpace.exp ((ι m).1 ℓ)) 0 :=
    continuousAt_pi.2 fun ℓ => ContinuousAt.comp_of_eq (f := fun m : M => (ι m).1 ℓ) hexp
      ((continuous_apply ℓ).comp (continuous_fst.comp ι.continuous)).continuousAt
      (by simp only [map_zero, Prod.fst_zero, Pi.zero_apply])
  have hcW : Continuous (fun m : M => fun ℓ i => Real.exp ((ι m).2 ℓ i)) :=
    continuous_pi fun ℓ => continuous_pi fun i => Real.continuous_exp.comp
      ((continuous_apply i).comp ((continuous_apply ℓ).comp (continuous_snd.comp ι.continuous)))
  have hV' : (fun m : M => fun ℓ => NormedSpace.exp ((ι m).1 ℓ)) ⁻¹' V ∈ 𝓝 (0 : M) := by
    refine hcV.preimage_mem_nhds ?_
    have h1 : (fun ℓ => NormedSpace.exp ((ι (0 : M)).1 ℓ)) = (1 : Fin (L + 1) → Matrix d d ℝ) := by
      funext ℓ
      simp only [map_zero, Prod.fst_zero, Pi.zero_apply, NormedSpace.exp_zero, Pi.one_apply]
    rw [h1]
    exact hV
  have hW' : (fun m : M => fun ℓ i => Real.exp ((ι m).2 ℓ i)) ⁻¹' W ∈ 𝓝 (0 : M) := by
    refine hcW.continuousAt.preimage_mem_nhds ?_
    have h1 : (fun ℓ i => Real.exp ((ι (0 : M)).2 ℓ i)) = (1 : ∀ ℓ, hid ℓ → ℝ) := by
      funext ℓ i
      simp only [map_zero, Prod.snd_zero, Pi.zero_apply, Real.exp_zero, Pi.one_apply]
    rw [h1]
    exact hW
  -- the orbit fills the level set near `θ`
  obtain ⟨U, hU, hUV⟩ := exists_mem_orbit_of_eval_eq (Arch.gated σ χ hid) 0
    (fun ℓ => analyticOnNhd_f_gated hσ ℓ) hχ θ hΦ hΦ0 hinj hconst hfd _ (inter_mem hV' hW')
  refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
  obtain ⟨m, ⟨hmV, hmW⟩, hmθ⟩ := hUV θ' hθ' heq
  exact ⟨m, hmV, hmW, hmθ.symm⟩

/-- **Proposition 4.6 for gated blocks, from the equality condition to local identifiability,
without normalization:** for a real-analytic gate `σ`, if `E` and the writes have rank `d`, no
value column of a read vanishes and `fd(θ) = P − (L+1) d² − s`, then every `θ'` near `θ` with the
same function is `θ` after a rescaling of the values of the hidden units by factors `c` near `1`
and a change of basis by invertible `G_0, …, G_L` near the identity. -/
theorem exists_cob_rescale_of_eval_eq_skipless_gated (hσ : AnalyticOnNhd ℝ σ Set.univ)
    (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d) (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d)
    (hv : ∀ ℓ i, (fun k => θ.read ℓ k (Sum.inr i)) ≠ 0)
    (hfd : funDim (Arch.gated σ id hid) 0 θ
        + ((L + 1) * Fintype.card d ^ 2 + ∑ ℓ, Fintype.card (hid ℓ))
      = Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)) :
    ∀ V ∈ 𝓝 (1 : Fin (L + 1) → Matrix d d ℝ), ∀ W ∈ 𝓝 (1 : ∀ ℓ, hid ℓ → ℝ), ∃ U ∈ 𝓝 θ,
      ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.gated σ id hid) 0 θ' x
        = eval (Arch.gated σ id hid) 0 θ x) →
        ∃ (G : Fin (L + 1) → GL d ℝ) (c : ∀ ℓ, hid ℓ → ℝ),
          (fun ℓ => (G ℓ : Matrix d d ℝ)) ∈ V ∧ c ∈ W ∧ (∀ ℓ i, 0 < c ℓ i) ∧
          θ' = (θ.rescale c).cob G G := by
  intro V hV W hW
  -- the pairs `(m, α)` form a space of dimension `(L + 1) d² + s`
  have hdimM : Module.finrank ℝ ((Fin (L + 1) → Matrix d d ℝ) × (∀ ℓ, hid ℓ → ℝ))
      = (L + 1) * Fintype.card d ^ 2 + ∑ ℓ, Fintype.card (hid ℓ) := by
    rw [Module.finrank_prod, Module.finrank_pi_fintype, Module.finrank_matrix,
      Module.finrank_pi_fintype]
    simp [sq, Module.finrank_fintype_fun_eq_card]
  -- the rescalings and then the changes of basis preserve the function (Proposition 3.2)
  have hpres : ∀ (p : (Fin (L + 1) → Matrix d d ℝ) × (∀ ℓ, hid ℓ → ℝ)) (x : Matrix T dIn ℝ),
      eval (Arch.gated σ id hid) 0
          (cobExpRescale θ (ContinuousLinearMap.id ℝ _ p)) x
        = eval (Arch.gated σ id hid) 0 θ x := by
    intro p x
    have h1 := eval_cob_skipless (A := Arch.gated σ id hid)
      (θ.rescale fun ℓ i => Real.exp (p.2 ℓ i)) (fun ℓ => expGL (p.1 ℓ)) x rfl
    exact h1.trans (eval_rescale_params θ _ (fun _ _ => Real.exp_ne_zero _) 0 x)
  -- the orbit `(m, α) ↦ (θ.rescale (e^α)).cob (exp m) (exp m)` fills the level set near `θ`
  obtain ⟨U, hU, hUV⟩ := exists_cobExpRescale_of_eval_eq_lig hσ analyticOnNhd_id θ hE hw hv
    (ContinuousLinearMap.id ℝ _) (fun _ _ h => h) (by rw [hdimM]; exact hfd) hpres V hV W hW
  refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
  -- `G_ℓ = exp m_ℓ` and `c ℓ i = e^{α ℓ i}`
  obtain ⟨p, hpV, hpW, rfl⟩ := hUV θ' hθ' heq
  exact ⟨fun ℓ => expGL (p.1 ℓ), fun ℓ i => Real.exp (p.2 ℓ i), hpV, hpW,
    fun _ _ => Real.exp_pos _, rfl⟩

/-- **Proposition 4.6 for gated blocks, from the equality condition to local identifiability,
under pre-RMSNorm with `ε > 0`:** for a real-analytic gate `σ`, if `E` and the writes have rank
`d`, no value column of a read vanishes and `fd(θ) = P − (L+1) d(d−1)/2 − s`, then every `θ'` near
`θ` with the same function is `θ` after a rescaling of the values of the hidden units by factors
`c` near `1` and a change of basis by orthogonal `Q_0, …, Q_L` near the identity. -/
theorem exists_cob_rescale_of_eval_eq_skipless_gated_rmsNorm {ε : ℝ} (hε : 0 < ε)
    (hσ : AnalyticOnNhd ℝ σ Set.univ)
    (θ : Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d) (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d)
    (hv : ∀ ℓ i, (fun k => θ.read ℓ k (Sum.inr i)) ≠ 0)
    (hfd : funDim (Arch.gated σ (rmsNorm ε) hid) 0 θ
        + ((L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2) + ∑ ℓ, Fintype.card (hid ℓ))
      = Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)) :
    ∀ V ∈ 𝓝 (1 : Fin (L + 1) → Matrix d d ℝ), ∀ W ∈ 𝓝 (1 : ∀ ℓ, hid ℓ → ℝ), ∃ U ∈ 𝓝 θ,
      ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.gated σ (rmsNorm ε) hid) 0 θ' x
        = eval (Arch.gated σ (rmsNorm ε) hid) 0 θ x) →
        ∃ (Q : Fin (L + 1) → GL d ℝ) (c : ∀ ℓ, hid ℓ → ℝ),
          (∀ ℓ, (Q ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ) ∧
          (fun ℓ => (Q ℓ : Matrix d d ℝ)) ∈ V ∧ c ∈ W ∧ (∀ ℓ i, 0 < c ℓ i) ∧
          θ' = (θ.rescale c).cob Q Q := by
  intro V hV W hW
  -- the families of antisymmetric matrices, with the rescalings, inside all the pairs `(m, α)`
  let ι : ((Fin (L + 1) → antisymmetric d) × (∀ ℓ, hid ℓ → ℝ)) →L[ℝ]
      (Fin (L + 1) → Matrix d d ℝ) × (∀ ℓ, hid ℓ → ℝ) :=
    (ContinuousLinearMap.pi fun ℓ =>
      (antisymmetric d).subtypeL.comp (ContinuousLinearMap.proj ℓ)).prodMap
      (ContinuousLinearMap.id ℝ _)
  have hι : Function.Injective ι := by
    intro p q h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    exact Prod.ext (funext fun ℓ => Subtype.ext (congrFun h1 ℓ)) h2
  -- they form a space of dimension `(L + 1) d (d - 1) / 2 + s`
  have hdimM : Module.finrank ℝ ((Fin (L + 1) → antisymmetric d) × (∀ ℓ, hid ℓ → ℝ))
      = (L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2) + ∑ ℓ, Fintype.card (hid ℓ) := by
    rw [Module.finrank_prod, Module.finrank_pi_fintype, finrank_antisymmetric, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul, Module.finrank_pi_fintype]
    simp only [Module.finrank_fintype_fun_eq_card]
  -- the changes of basis `exp m_ℓ`, `m_ℓ` antisymmetric, are orthogonal
  have horth : ∀ (p : (Fin (L + 1) → antisymmetric d) × (∀ ℓ, hid ℓ → ℝ)) ℓ,
      ((expGL ((ι p).1 ℓ) : GL d ℝ) : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ :=
    fun p ℓ => exp_mem_orthogonalGroup_of_transpose_eq_neg (p.1 ℓ).2
  -- the rescalings and then the changes of basis preserve the function (Proposition 3.2 under
  -- pre-RMSNorm)
  have hpres : ∀ (p : (Fin (L + 1) → antisymmetric d) × (∀ ℓ, hid ℓ → ℝ))
      (x : Matrix T dIn ℝ), eval (Arch.gated σ (rmsNorm ε) hid) 0 (cobExpRescale θ (ι p)) x
        = eval (Arch.gated σ (rmsNorm ε) hid) 0 θ x := by
    intro p x
    have h1 := eval_cob_rmsNorm (A := Arch.gated σ (rmsNorm ε) hid)
      (θ.rescale fun ℓ i => Real.exp ((ι p).2 ℓ i)) x ε rfl (fun ℓ => expGL ((ι p).1 ℓ))
      (horth p)
    exact h1.trans (eval_rescale_params θ _ (fun _ _ => Real.exp_ne_zero _) 0 x)
  -- the orbit fills the level set near `θ`
  obtain ⟨U, hU, hUV⟩ := exists_cobExpRescale_of_eval_eq_lig hσ (analyticOnNhd_rmsNorm hε) θ
    hE hw hv ι hι (by rw [hdimM]; exact hfd) hpres V hV W hW
  refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
  -- `Q_ℓ = exp m_ℓ` and `c ℓ i = e^{α ℓ i}`
  obtain ⟨p, hpV, hpW, rfl⟩ := hUV θ' hθ' heq
  exact ⟨fun ℓ => expGL ((ι p).1 ℓ), fun ℓ i => Real.exp ((ι p).2 ℓ i), horth p, hpV, hpW,
    fun _ _ => Real.exp_pos _, rfl⟩

/-- **Corollary 5.3 for SwiGLU blocks without normalization:** for `d_in, d_out ≥ d ≥ 2` and at
least `d` hidden units per block, at almost every parameter `θ`, every `θ'` near `θ` with the same
function is `θ` after a rescaling of the value of each hidden unit, close to `1`, and a change of
basis by invertible `G_0, …, G_L` near the identity. -/
theorem ae_exists_cob_rescale_of_eval_eq_swiglu_skipless [Nonempty T]
    (μ : Measure (Params (Arch.gated (T := T) (d := d) silu id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, ∀ V ∈ 𝓝 (1 : Fin (L + 1) → Matrix d d ℝ), ∀ W ∈ 𝓝 (1 : ∀ ℓ, hid ℓ → ℝ),
      ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.gated silu id hid) 0 θ' x
        = eval (Arch.gated silu id hid) 0 θ x) →
        ∃ (G : Fin (L + 1) → GL d ℝ) (c : ∀ ℓ, hid ℓ → ℝ),
          (fun ℓ => (G ℓ : Matrix d d ℝ)) ∈ V ∧ c ∈ W ∧ (∀ ℓ i, 0 < c ℓ i) ∧
          θ' = (θ.rescale c).cob G G := by
  have : Nonempty d := Fintype.card_pos_iff.1 (by omega)
  -- at generic parameters `E` and the writes have rank `d`, no value column vanishes, and the
  -- functional dimension is the bound of Theorem 4.3
  filter_upwards [ae_rank_E_write μ hdIn hhid, ae_value_ne_zero μ,
    ae_funDim_swiglu_skipless μ hd hdIn hdOut hhid] with θ hθ hv hfd
  -- Proposition 4.6 at `θ`, with the analytic gate of SwiGLU
  exact exists_cob_rescale_of_eval_eq_skipless_gated analyticOnNhd_silu θ hθ.1 hθ.2 hv hfd

/-- **Corollary 5.3 for SwiGLU blocks under pre-RMSNorm with `ε > 0`:** for `d_in, d_out ≥ d ≥ 2`
and at least `d` hidden units per block, at almost every parameter `θ`, every `θ'` near `θ` with the
same function is `θ` after a rescaling of the value of each hidden unit, close to `1`, and a change
of basis by orthogonal `Q_0, …, Q_L` near the identity. -/
theorem ae_exists_cob_rescale_of_eval_eq_swiglu_skipless_rmsNorm [Nonempty T] {ε : ℝ} (hε : 0 < ε)
    (μ : Measure (Params (Arch.gated (T := T) (d := d) silu (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, ∀ V ∈ 𝓝 (1 : Fin (L + 1) → Matrix d d ℝ), ∀ W ∈ 𝓝 (1 : ∀ ℓ, hid ℓ → ℝ),
      ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.gated silu (rmsNorm ε) hid) 0 θ' x
        = eval (Arch.gated silu (rmsNorm ε) hid) 0 θ x) →
        ∃ (Q : Fin (L + 1) → GL d ℝ) (c : ∀ ℓ, hid ℓ → ℝ),
          (∀ ℓ, (Q ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ) ∧
          (fun ℓ => (Q ℓ : Matrix d d ℝ)) ∈ V ∧ c ∈ W ∧ (∀ ℓ i, 0 < c ℓ i) ∧
          θ' = (θ.rescale c).cob Q Q := by
  have : Nonempty d := Fintype.card_pos_iff.1 (by omega)
  -- at generic parameters `E` and the writes have rank `d`, no value column vanishes, and the
  -- functional dimension is the bound of Theorem 4.3
  filter_upwards [ae_rank_E_write μ hdIn hhid, ae_value_ne_zero μ,
    ae_funDim_swiglu_skipless_rmsNorm hε μ hd hdIn hdOut hhid] with θ hθ hv hfd
  -- Proposition 4.6 at `θ`, with the analytic gate of SwiGLU
  exact exists_cob_rescale_of_eval_eq_skipless_gated_rmsNorm hε analyticOnNhd_silu θ hθ.1 hθ.2
    hv hfd

/-- **Corollary 5.3 for GeGLU blocks without normalization:** for `d_in, d_out ≥ d ≥ 2` and at
least `d` hidden units per block, at almost every parameter `θ`, every `θ'` near `θ` with the same
function is `θ` after a rescaling of the value of each hidden unit, close to `1`, and a change of
basis by invertible `G_0, …, G_L` near the identity. -/
theorem ae_exists_cob_rescale_of_eval_eq_geglu_skipless [Nonempty T]
    (μ : Measure (Params (Arch.gated (T := T) (d := d) gelu id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, ∀ V ∈ 𝓝 (1 : Fin (L + 1) → Matrix d d ℝ), ∀ W ∈ 𝓝 (1 : ∀ ℓ, hid ℓ → ℝ),
      ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.gated gelu id hid) 0 θ' x
        = eval (Arch.gated gelu id hid) 0 θ x) →
        ∃ (G : Fin (L + 1) → GL d ℝ) (c : ∀ ℓ, hid ℓ → ℝ),
          (fun ℓ => (G ℓ : Matrix d d ℝ)) ∈ V ∧ c ∈ W ∧ (∀ ℓ i, 0 < c ℓ i) ∧
          θ' = (θ.rescale c).cob G G := by
  have : Nonempty d := Fintype.card_pos_iff.1 (by omega)
  -- at generic parameters `E` and the writes have rank `d`, no value column vanishes, and the
  -- functional dimension is the bound of Theorem 4.3
  filter_upwards [ae_rank_E_write μ hdIn hhid, ae_value_ne_zero μ,
    ae_funDim_geglu_skipless μ hd hdIn hdOut hhid] with θ hθ hv hfd
  -- Proposition 4.6 at `θ`, with the analytic gate of GeGLU
  exact exists_cob_rescale_of_eval_eq_skipless_gated analyticOnNhd_gelu θ hθ.1 hθ.2 hv hfd

/-- **Corollary 5.3 for GeGLU blocks under pre-RMSNorm with `ε > 0`:** for `d_in, d_out ≥ d ≥ 2` and
at least `d` hidden units per block, at almost every parameter `θ`, every `θ'` near `θ` with the
same function is `θ` after a rescaling of the value of each hidden unit, close to `1`, and a change
of basis by orthogonal `Q_0, …, Q_L` near the identity. -/
theorem ae_exists_cob_rescale_of_eval_eq_geglu_skipless_rmsNorm [Nonempty T] {ε : ℝ} (hε : 0 < ε)
    (μ : Measure (Params (Arch.gated (T := T) (d := d) gelu (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, ∀ V ∈ 𝓝 (1 : Fin (L + 1) → Matrix d d ℝ), ∀ W ∈ 𝓝 (1 : ∀ ℓ, hid ℓ → ℝ),
      ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.gated gelu (rmsNorm ε) hid) 0 θ' x
        = eval (Arch.gated gelu (rmsNorm ε) hid) 0 θ x) →
        ∃ (Q : Fin (L + 1) → GL d ℝ) (c : ∀ ℓ, hid ℓ → ℝ),
          (∀ ℓ, (Q ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ) ∧
          (fun ℓ => (Q ℓ : Matrix d d ℝ)) ∈ V ∧ c ∈ W ∧ (∀ ℓ i, 0 < c ℓ i) ∧
          θ' = (θ.rescale c).cob Q Q := by
  have : Nonempty d := Fintype.card_pos_iff.1 (by omega)
  -- at generic parameters `E` and the writes have rank `d`, no value column vanishes, and the
  -- functional dimension is the bound of Theorem 4.3
  filter_upwards [ae_rank_E_write μ hdIn hhid, ae_value_ne_zero μ,
    ae_funDim_geglu_skipless_rmsNorm hε μ hd hdIn hdOut hhid] with θ hθ hv hfd
  -- Proposition 4.6 at `θ`, with the analytic gate of GeGLU
  exact exists_cob_rescale_of_eval_eq_skipless_gated_rmsNorm hε analyticOnNhd_gelu θ hθ.1 hθ.2
    hv hfd

end Skips
