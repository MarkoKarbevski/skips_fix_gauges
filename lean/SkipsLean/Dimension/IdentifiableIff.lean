import SkipsLean.Dimension.IdentifiableConverseCob
import SkipsLean.Dimension.LocalIdentifiability
import SkipsLean.Dimension.LocalIdentifiabilityGated
import SkipsLean.Dimension.LocalIdentifiabilityAttention
import SkipsLean.Residual.LocalIdentifiabilityAttentionRMS
import SkipsLean.Dimension.UpperBoundAttention

/-!
# The equality condition is local identifiability: networks without skip connections

Paper (dimension paper): Proposition 4.6 (The equality condition and local identifiability): "Let
the blocks be tanh, GELU, SwiGLU, GeGLU or attention blocks, without normalization or under
pre-RMSNorm. A network satisfies the equality condition if and only if, at generic parameters, it
is locally identifiable up to its symmetries. Every symmetry that is needed is then close to the
identity." Definition 4.4: "A network satisfies the equality condition if the bound of Theorem 4.3
is attained at generic parameters". Definition 4.5: "A network is identifiable up to its symmetries
at `θ` if every `θ′` with `F_{θ′} = F_θ` is the image of `θ` under a symmetry: a change of basis of
Proposition 3.2, a symmetry inside a block, or a composition of these. It is locally identifiable
at `θ` if this holds for every `θ′` in some neighborhood of `θ`." The skips paper, Proposition 4.5,
states the same for skipless networks.

Here the equivalence, for skipless networks (stream matrices `0`) with `d_in ≥ d` and blocks of
width at least `d` (the Scope of the papers; for attention the width is `H d_h`, and `d_h ≤ d`):
"the functional dimension is `P − (L + 1) dim 𝒢 − s` at almost every parameter" if and only if "at
almost every parameter `θ`, every `θ'` near `θ` with the same function is the image of `θ` under a
symmetry". The symmetries are those of the papers: the changes of basis `G_0, …, G_L` (orthogonal
under pre-RMSNorm), for gated blocks the rescalings of the values of the hidden units by nonzero
factors, for attention blocks the changes of basis inside the heads. The first statements are for
any real-analytic blocks, with the changes of basis alone (`s = 0`): they contain tanh and GELU
blocks, and are also stated for MLP blocks by name.

The direction from the equality condition to local identifiability, with the symmetries close to
the identity ("Every symmetry that is needed is then close to the identity"), is in
`Dimension/LocalIdentifiability.lean`, `Dimension/LocalIdentifiabilityGated.lean`,
`Dimension/LocalIdentifiabilityAttention.lean` and `Residual/LocalIdentifiabilityAttentionRMS.lean`;
the other direction is `Dimension/IdentifiableConverseCob.lean` with the upper bounds of
Theorem 4.3. Residual networks: `Residual/IdentifiableIff.lean`.
-/

namespace Skips

open Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {sees : T → T → Prop} [DecidableRel sees]
variable {H dh hid : Fin L → Type} [∀ ℓ, Fintype (H ℓ)] [∀ ℓ, Fintype (dh ℓ)]
  [∀ ℓ, DecidableEq (dh ℓ)] [∀ ℓ, Fintype (hid ℓ)] {σ : ℝ → ℝ} {ε : ℝ}

/-- **Proposition 4.6 of the dimension paper and Proposition 4.5 of the skips paper, for skipless
networks of any real-analytic blocks, without normalization:** `fd = P − (L + 1) d²` at almost every
parameter if and only if at almost every parameter `θ` every `θ'` near `θ` with the same function is
`θ` after a change of basis by invertible `G_0, …, G_L`. -/
theorem ae_funDim_skipless_iff_ae_locally_cob
    (A : Arch T d L) (hA : A.χ = id)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ)
    (μ : Measure (Params
      A dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hw : ∀ ℓ, Fintype.card d ≤ Fintype.card (A.w ℓ)) :
    (∀ᵐ θ ∂μ, funDim A 0 θ
        + (L + 1) * Fintype.card d ^ 2
      = Module.finrank ℝ (Params
          A dIn dOut)) ↔
    (∀ᵐ θ ∂μ, ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval A 0 θ' x
        = eval A 0 θ x) →
        ∃ G : Fin (L + 1) → GL d ℝ,
            θ' = θ.cob G G) := by
  -- `χ = id` is analytic
  have hχ : AnalyticOnNhd ℝ A.χ Set.univ := by
    rw [hA]
    exact analyticOnNhd_id
  constructor
  · -- the equality condition gives local identifiability at the parameters where `E` and the
    -- writes have rank `d` (Proposition 4.6 at one parameter, with any neighborhood of `1`)
    intro h
    filter_upwards [h, ae_rank_E_write μ hdIn hw] with θ hfd hθ
    obtain ⟨U, hU, hUV⟩ := exists_cob_of_eval_eq_skipless A hA hf θ hθ.1 hθ.2 hfd Set.univ
      Filter.univ_mem
    refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
    obtain ⟨G, -, hG⟩ := hUV θ' hθ' heq
    exact ⟨G, hG⟩
  · -- local identifiability gives the lower bound `P ≤ fd + (L + 1) d²`, with no symmetry inside
    -- the blocks (`N` of dimension `0`, `Ψ θ n = θ`)
    intro h
    have hlow := ae_finrank_le_funDim_add_of_ae_locally_cob A 0 hf hχ μ (N := Fin 0 → ℝ)
      (fun θ _ => θ) Set.univ (fun _ => contDiffOn_const) (by
        filter_upwards [h] with θ ⟨U, hU, hUV⟩
        exact ⟨U, hU, fun θ' hθ' heq => ⟨0, Set.mem_univ _, hUV θ' hθ' heq⟩⟩)
    -- and the upper bound of Theorem 4.3
    have hup := ae_funDim_add_le_skipless μ hA
      (fun ℓ => differentiableOn_univ.1 (hf ℓ).differentiableOn) hdIn hw
    filter_upwards [hlow, hup] with θ h1 h2
    rw [Module.finrank_fin_fun] at h1
    omega

/-- **Proposition 4.6 of the dimension paper and Proposition 4.5 of the skips paper, for skipless
networks of any real-analytic blocks, under pre-RMSNorm with `ε > 0`:** `fd = P − (L + 1) d(d−1)/2`
at almost every parameter if and only if at almost every parameter `θ` every `θ'` near `θ` with the
same function is `θ` after a change of basis by orthogonal `Q_0, …, Q_L`. -/
theorem ae_funDim_skipless_iff_ae_locally_cob_rmsNorm
    (A : Arch T d L) (hε : 0 < ε) (hA : A.χ = rmsNorm ε)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ)
    (μ : Measure (Params
      A dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hw : ∀ ℓ, Fintype.card d ≤ Fintype.card (A.w ℓ)) :
    (∀ᵐ θ ∂μ, funDim A 0 θ
        + (L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2)
      = Module.finrank ℝ (Params
          A dIn dOut)) ↔
    (∀ᵐ θ ∂μ, ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval A 0 θ' x
        = eval A 0 θ x) →
        ∃ Q : Fin (L + 1) → GL d ℝ,
            (∀ ℓ, (Q ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ) ∧
            θ' = θ.cob Q Q) := by
  -- RMSNorm with `ε > 0` is analytic
  have hχ : AnalyticOnNhd ℝ A.χ Set.univ := by
    rw [hA]
    exact analyticOnNhd_rmsNorm hε
  constructor
  · -- the equality condition gives local identifiability at the parameters where `E` and the
    -- writes have rank `d` (Proposition 4.6 at one parameter, with any neighborhood of `1`)
    intro h
    filter_upwards [h, ae_rank_E_write μ hdIn hw] with θ hfd hθ
    obtain ⟨U, hU, hUV⟩ := exists_cob_of_eval_eq_skipless_rmsNorm A hε hA hf θ hθ.1 hθ.2 hfd
      Set.univ Filter.univ_mem
    refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
    obtain ⟨Q, hQ, -, hQθ⟩ := hUV θ' hθ' heq
    exact ⟨Q, hQ, hQθ⟩
  · -- local identifiability gives the lower bound `P ≤ fd + (L + 1) d(d−1)/2`, with no symmetry
    -- inside the blocks (`N` of dimension `0`, `Ψ θ n = θ`)
    intro h
    have hlow := ae_finrank_le_funDim_add_of_ae_locally_cob_orthogonal A 0 hf hχ μ
      (N := Fin 0 → ℝ) (fun θ _ => θ) Set.univ (fun _ => contDiffOn_const) (by
        filter_upwards [h] with θ ⟨U, hU, hUV⟩
        exact ⟨U, hU, fun θ' hθ' heq => ⟨0, Set.mem_univ _, hUV θ' hθ' heq⟩⟩)
    -- and the upper bound of Theorem 4.3 under pre-RMSNorm
    have hup := ae_funDim_add_le_skipless_rmsNorm μ hε hA
      (fun ℓ => differentiableOn_univ.1 (hf ℓ).differentiableOn) hdIn hw
    filter_upwards [hlow, hup] with θ h1 h2
    rw [Module.finrank_fin_fun] at h1
    omega

/-- **Proposition 4.6 of the dimension paper and Proposition 4.5 of the skips paper, for skipless
networks of MLP blocks with a real-analytic activation (tanh, GELU), without normalization:** `fd =
P − (L + 1) d²` at almost every parameter if and only if at almost every parameter `θ` every `θ'`
near `θ` with the same function is `θ` after a change of basis by invertible `G_0, …, G_L`. -/
theorem ae_funDim_mlp_skipless_iff_ae_locally_cob
    (hσ : AnalyticOnNhd ℝ σ Set.univ)
    (μ : Measure (Params
      (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    (∀ᵐ θ ∂μ, funDim (Arch.mlp σ id hid) 0 θ
        + (L + 1) * Fintype.card d ^ 2
      = Module.finrank ℝ (Params
          (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)) ↔
    (∀ᵐ θ ∂μ, ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.mlp σ id hid) 0 θ' x
        = eval (Arch.mlp σ id hid) 0 θ x) →
        ∃ G : Fin (L + 1) → GL d ℝ,
            θ' = θ.cob G G) :=
  -- the case of any real-analytic blocks, with the analytic blocks `σ` entrywise
  ae_funDim_skipless_iff_ae_locally_cob _ rfl (fun ℓ => analyticOnNhd_f_mlp hσ ℓ) μ hdIn hhid

/-- **Proposition 4.6 of the dimension paper and Proposition 4.5 of the skips paper, for skipless
networks of MLP blocks with a real-analytic activation (tanh, GELU), under pre-RMSNorm with `ε >
0`:** `fd = P − (L + 1) d(d−1)/2` at almost every parameter if and only if at almost every parameter
`θ` every `θ'` near `θ` with the same function is `θ` after a change of basis by orthogonal `Q_0, …,
Q_L`. -/
theorem ae_funDim_mlp_skipless_iff_ae_locally_cob_rmsNorm
    (hε : 0 < ε) (hσ : AnalyticOnNhd ℝ σ Set.univ)
    (μ : Measure (Params
      (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    (∀ᵐ θ ∂μ, funDim (Arch.mlp σ (rmsNorm ε) hid) 0 θ
        + (L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2)
      = Module.finrank ℝ (Params
          (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)) ↔
    (∀ᵐ θ ∂μ, ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.mlp σ (rmsNorm ε) hid) 0 θ' x
        = eval (Arch.mlp σ (rmsNorm ε) hid) 0 θ x) →
        ∃ Q : Fin (L + 1) → GL d ℝ,
            (∀ ℓ, (Q ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ) ∧
            θ' = θ.cob Q Q) :=
  -- the case of any real-analytic blocks, with the analytic blocks `σ` entrywise
  ae_funDim_skipless_iff_ae_locally_cob_rmsNorm _ hε rfl (fun ℓ => analyticOnNhd_f_mlp hσ ℓ) μ
    hdIn hhid

omit [Fintype T] [DecidableEq d] in
/-- Helper: a map into the parameters is `C¹` on a set if its four components are. -/
private theorem contDiffOn_params_iffs {A : Arch T d L} {N : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] {Φ : N → Params A dIn dOut} {s : Set N}
    (hE : ContDiffOn ℝ 1 (fun n => (Φ n).E) s) (hr : ContDiffOn ℝ 1 (fun n => (Φ n).read) s)
    (hw : ContDiffOn ℝ 1 (fun n => (Φ n).write) s) (hD : ContDiffOn ℝ 1 (fun n => (Φ n).D) s) :
    ContDiffOn ℝ 1 Φ s := by
  -- the parameters are the tuples of their components, by a continuous linear equivalence
  let e := (Params.linearEquivProd (A := A) (dIn := dIn) (dOut := dOut)).toContinuousLinearEquiv
  have h : ContDiffOn ℝ 1 (e ∘ Φ) s := hE.prodMk (hr.prodMk (hw.prodMk hD))
  exact e.comp_contDiffOn_iff.1 h

omit [DecidableEq d] in
/-- Helper: the rescaling `c ↦ θ.rescale c` is `C¹` where no factor `c ℓ i` vanishes (the value
columns are divided by `c ℓ i`, the rows of the writes multiplied by `c ℓ i`). -/
private theorem contDiffOn_rescale_iffs {χ : Matrix T d ℝ → Matrix T d ℝ}
    (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut) :
    ContDiffOn ℝ 1 (fun c : ∀ ℓ, hid ℓ → ℝ => θ.rescale c) {c | ∀ ℓ i, c ℓ i ≠ 0} := by
  -- the coordinate `c ↦ c ℓ i` is linear
  have hc : ∀ ℓ i, ContDiffOn ℝ 1 (fun c : ∀ ℓ, hid ℓ → ℝ => c ℓ i) {c | ∀ ℓ i, c ℓ i ≠ 0} :=
    fun ℓ i => (contDiff_pi.1 (contDiff_apply ℝ (fun ℓ => hid ℓ → ℝ) ℓ) i).contDiffOn
  refine contDiffOn_params_iffs ?_ ?_ ?_ ?_
  · show ContDiffOn ℝ 1 (fun _ => θ.E) _
    exact contDiffOn_const
  · -- the reads: the value column of unit `i` is divided by `c ℓ i`
    refine contDiffOn_pi.2 fun ℓ => contDiffOn_pi.2 fun k => contDiffOn_pi.2 fun j => ?_
    rcases j with i | i
    · show ContDiffOn ℝ 1 (fun _ => θ.read ℓ k (Sum.inl i)) _
      exact contDiffOn_const
    · show ContDiffOn ℝ 1 (fun c : ∀ ℓ, hid ℓ → ℝ => (c ℓ i)⁻¹ * θ.read ℓ k (Sum.inr i)) _
      exact ((hc ℓ i).inv fun c h => h ℓ i).mul contDiffOn_const
  · -- the writes: the row of unit `i` is multiplied by `c ℓ i`
    refine contDiffOn_pi.2 fun ℓ => contDiffOn_pi.2 fun i => contDiffOn_pi.2 fun k => ?_
    show ContDiffOn ℝ 1 (fun c : ∀ ℓ, hid ℓ → ℝ => c ℓ i * θ.write ℓ i k) _
    exact (hc ℓ i).mul contDiffOn_const
  · show ContDiffOn ℝ 1 (fun _ => θ.D) _
    exact contDiffOn_const

/-- **Proposition 4.6 of the dimension paper and Proposition 4.5 of the skips paper, for skipless
networks of gated blocks with a real-analytic gate (SwiGLU, GeGLU), without normalization:** `fd = P
− (L + 1) d² − s` at almost every parameter (`s = ∑ d_hidden`) if and only if at almost every
parameter `θ` every `θ'` near `θ` with the same function is `θ` after a rescaling of the values of
the hidden units by nonzero factors `c` and a change of basis by invertible `G_0, …, G_L`. -/
theorem ae_funDim_gated_skipless_iff_ae_locally_cob_rescale
    [Nonempty d] (hσ : AnalyticOnNhd ℝ σ Set.univ)
    (μ : Measure (Params
      (Arch.gated (T := T) (d := d) σ id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    (∀ᵐ θ ∂μ, funDim (Arch.gated σ id hid) 0 θ
        + ((L + 1) * Fintype.card d ^ 2
          + ∑ ℓ, Fintype.card (hid ℓ))
      = Module.finrank ℝ (Params
          (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)) ↔
    (∀ᵐ θ ∂μ, ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.gated σ id hid) 0 θ' x
        = eval (Arch.gated σ id hid) 0 θ x) →
        ∃ c : ∀ ℓ, hid ℓ → ℝ, (∀ ℓ i, c ℓ i ≠ 0) ∧
          ∃ G : Fin (L + 1) → GL d ℝ,
            θ' = (θ.rescale c).cob G G) := by
  constructor
  · -- the equality condition gives local identifiability at the parameters where `E` and the
    -- writes have rank `d` and no value column of a read vanishes (Proposition 4.6 at one
    -- parameter, with any neighborhoods of `1`)
    intro h
    filter_upwards [h, ae_rank_E_write μ hdIn hhid, ae_value_ne_zero μ] with θ hfd hθ hv
    obtain ⟨U, hU, hUV⟩ := exists_cob_rescale_of_eval_eq_skipless_gated hσ θ hθ.1 hθ.2 hv hfd
      Set.univ Filter.univ_mem Set.univ Filter.univ_mem
    refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
    obtain ⟨G, c, -, -, hc, hG⟩ := hUV θ' hθ' heq
    exact ⟨c, fun ℓ i => (hc ℓ i).ne', G, hG⟩
  · -- local identifiability gives the lower bound `P ≤ fd + (L + 1) d² + s`, with the
    -- rescalings `Ψ θ c = θ.rescale c` on the factors `c` with no zero (`N` of dimension `s`)
    intro h
    have hlow := ae_finrank_le_funDim_add_of_ae_locally_cob (Arch.gated σ id hid) 0
      (fun ℓ => analyticOnNhd_f_gated hσ ℓ) analyticOnNhd_id μ (N := ∀ ℓ, hid ℓ → ℝ)
      (fun θ c => θ.rescale c) {c | ∀ ℓ i, c ℓ i ≠ 0} contDiffOn_rescale_iffs (by
        filter_upwards [h] with θ ⟨U, hU, hUV⟩
        refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
        obtain ⟨c, hc, G, hG⟩ := hUV θ' hθ' heq
        exact ⟨c, hc, G, hG⟩)
    -- and the upper bound of Theorem 4.3 for gated blocks
    have hup := ae_funDim_add_le_skipless_gated (differentiableOn_univ.1 hσ.differentiableOn) μ
      hdIn hhid
    have hdim : Module.finrank ℝ (∀ ℓ, hid ℓ → ℝ) = ∑ ℓ, Fintype.card (hid ℓ) := by
      rw [Module.finrank_pi_fintype]
      simp only [Module.finrank_fintype_fun_eq_card]
    filter_upwards [hlow, hup] with θ h1 h2
    rw [hdim] at h1
    generalize ∑ ℓ, Fintype.card (hid ℓ) = s at h1 h2
    omega

/-- **Proposition 4.6 of the dimension paper and Proposition 4.5 of the skips paper, for skipless
networks of gated blocks with a real-analytic gate (SwiGLU, GeGLU), under pre-RMSNorm with `ε >
0`:** `fd = P − (L + 1) d(d−1)/2 − s` at almost every parameter (`s = ∑ d_hidden`) if and only if at
almost every parameter `θ` every `θ'` near `θ` with the same function is `θ` after a rescaling of
the values of the hidden units by nonzero factors `c` and a change of basis by orthogonal `Q_0, …,
Q_L`. -/
theorem ae_funDim_gated_skipless_iff_ae_locally_cob_rescale_rmsNorm
    (hε : 0 < ε) [Nonempty d] (hσ : AnalyticOnNhd ℝ σ Set.univ)
    (μ : Measure (Params
      (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    (∀ᵐ θ ∂μ, funDim (Arch.gated σ (rmsNorm ε) hid) 0 θ
        + ((L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2)
          + ∑ ℓ, Fintype.card (hid ℓ))
      = Module.finrank ℝ (Params
          (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)) ↔
    (∀ᵐ θ ∂μ, ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.gated σ (rmsNorm ε) hid) 0 θ' x
        = eval (Arch.gated σ (rmsNorm ε) hid) 0 θ x) →
        ∃ c : ∀ ℓ, hid ℓ → ℝ, (∀ ℓ i, c ℓ i ≠ 0) ∧
          ∃ Q : Fin (L + 1) → GL d ℝ,
            (∀ ℓ, (Q ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ) ∧
            θ' = (θ.rescale c).cob Q Q) := by
  constructor
  · -- the equality condition gives local identifiability at the parameters where `E` and the
    -- writes have rank `d` and no value column of a read vanishes (Proposition 4.6 under
    -- pre-RMSNorm at one parameter, with any neighborhoods of `1`)
    intro h
    filter_upwards [h, ae_rank_E_write μ hdIn hhid, ae_value_ne_zero μ] with θ hfd hθ hv
    obtain ⟨U, hU, hUV⟩ := exists_cob_rescale_of_eval_eq_skipless_gated_rmsNorm hε hσ θ hθ.1 hθ.2
      hv hfd Set.univ Filter.univ_mem Set.univ Filter.univ_mem
    refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
    obtain ⟨Q, c, hQ, -, -, hc, hQθ⟩ := hUV θ' hθ' heq
    exact ⟨c, fun ℓ i => (hc ℓ i).ne', Q, hQ, hQθ⟩
  · -- local identifiability gives the lower bound `P ≤ fd + (L + 1) d(d−1)/2 + s`, with the
    -- rescalings `Ψ θ c = θ.rescale c` on the factors `c` with no zero (`N` of dimension `s`)
    intro h
    have hlow := ae_finrank_le_funDim_add_of_ae_locally_cob_orthogonal
      (Arch.gated σ (rmsNorm ε) hid) 0 (fun ℓ => analyticOnNhd_f_gated hσ ℓ)
      (analyticOnNhd_rmsNorm hε) μ (N := ∀ ℓ, hid ℓ → ℝ)
      (fun θ c => θ.rescale c) {c | ∀ ℓ i, c ℓ i ≠ 0} contDiffOn_rescale_iffs (by
        filter_upwards [h] with θ ⟨U, hU, hUV⟩
        refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
        obtain ⟨c, hc, Q, hQ, hQθ⟩ := hUV θ' hθ' heq
        exact ⟨c, hc, Q, hQ, hQθ⟩)
    -- and the upper bound of Theorem 4.3 for gated blocks under pre-RMSNorm
    have hup := ae_funDim_add_le_skipless_gated_rmsNorm hε
      (differentiableOn_univ.1 hσ.differentiableOn) μ hdIn hhid
    have hdim : Module.finrank ℝ (∀ ℓ, hid ℓ → ℝ) = ∑ ℓ, Fintype.card (hid ℓ) := by
      rw [Module.finrank_pi_fintype]
      simp only [Module.finrank_fintype_fun_eq_card]
    filter_upwards [hlow, hup] with θ h1 h2
    rw [hdim] at h1
    generalize ∑ ℓ, Fintype.card (hid ℓ) = s at h1 h2
    generalize Fintype.card d * (Fintype.card d - 1) / 2 = q at h1 h2
    omega

/-- **Proposition 4.6 of the dimension paper and Proposition 4.5 of the skips paper, for skipless
networks of attention blocks, without normalization:** `fd = P − (L + 1) d² − s` at almost every
parameter (`s = 2 ∑ H d_h²`) if and only if at almost every parameter `θ` every `θ'` near `θ` with
the same function is `θ` after changes of basis inside the heads and a change of basis by invertible
`G_0, …, G_L`. -/
theorem ae_funDim_attention_skipless_iff_ae_locally_cob_heads
    (μ : Measure (Params
      (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d)
    (hH : ∀ ℓ, Fintype.card d ≤ Fintype.card (H ℓ) * Fintype.card (dh ℓ)) :
    (∀ᵐ θ ∂μ, funDim (Arch.attention sees id H dh) 0 θ
        + ((L + 1) * Fintype.card d ^ 2
          + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
      = Module.finrank ℝ (Params
          (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut)) ↔
    (∀ᵐ θ ∂μ, ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.attention sees id H dh) 0 θ' x
        = eval (Arch.attention sees id H dh) 0 θ x) →
        ∃ K K' : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ,
          ∃ G : Fin (L + 1) → GL d ℝ,
            θ' = ((θ.headsQK K).headsVO K').cob G G) := by
  sorry

/-- **Proposition 4.6 of the dimension paper and Proposition 4.5 of the skips paper, for skipless
networks of attention blocks, under pre-RMSNorm with `ε > 0`:** `fd = P − (L + 1) d(d−1)/2 − s` at
almost every parameter (`s = 2 ∑ H d_h²`) if and only if at almost every parameter `θ` every `θ'`
near `θ` with the same function is `θ` after changes of basis inside the heads and a change of basis
by orthogonal `Q_0, …, Q_L`. -/
theorem ae_funDim_attention_skipless_iff_ae_locally_cob_heads_rmsNorm
    (hε : 0 < ε)
    (μ : Measure (Params
      (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d)
    (hH : ∀ ℓ, Fintype.card d ≤ Fintype.card (H ℓ) * Fintype.card (dh ℓ)) :
    (∀ᵐ θ ∂μ, funDim (Arch.attention sees (rmsNorm ε) H dh) 0 θ
        + ((L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2)
          + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
      = Module.finrank ℝ (Params
          (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut)) ↔
    (∀ᵐ θ ∂μ, ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.attention sees (rmsNorm ε) H dh) 0 θ' x
        = eval (Arch.attention sees (rmsNorm ε) H dh) 0 θ x) →
        ∃ K K' : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ,
          ∃ Q : Fin (L + 1) → GL d ℝ,
            (∀ ℓ, (Q ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ) ∧
            θ' = ((θ.headsQK K).headsVO K').cob Q Q) := by
  sorry

end Skips
