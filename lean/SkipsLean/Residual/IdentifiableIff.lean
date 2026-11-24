import SkipsLean.Dimension.IdentifiableConverseCob
import SkipsLean.Residual.LocalIdentifiability
import SkipsLean.Residual.LocalIdentifiabilityGated
import SkipsLean.Residual.LocalIdentifiabilityTransformer
import SkipsLean.Residual.UpperBoundSymmetries
import SkipsLean.Dimension.UpperBoundTransformer

/-!
# The equality condition is local identifiability: residual networks

Paper (skips paper): Proposition 4.5 (The equality condition and local identifiability): "Let the
blocks be analytic, with or without pre-RMSNorm, within the scope of Section 2. A skipless or a
residual network satisfies the equality condition if and only if, at generic parameters, it is
locally identifiable up to its symmetries. Every symmetry that is needed is then close to the
identity." Definition 4.3: "A network satisfies the equality condition if its bound in Theorem 4.2
is attained at generic parameters". Definition 4.4: "A network is identifiable up to its symmetries
at `θ` if every `θ′` with `F_{θ′} = F_θ` is the image of `θ` under a symmetry: a change of basis
that preserves the function, a symmetry inside a block, or a composition of these. It is locally
identifiable at `θ` if this holds for every `θ′` in some neighborhood of `θ`."

Here the equivalence for residual networks (stream matrices `1`) with `d_in ≥ d` and blocks of any
widths (heads of width `d_h ≤ d`): "the functional dimension is `P − dim 𝒢 − s` at almost every
parameter" if and only if "at almost every parameter `θ`, every `θ'` near `θ` with the same
function is the image of `θ` under a symmetry". The symmetries are those of the paper: one change
of basis at all hidden states (orthogonal under pre-RMSNorm), for gated blocks the rescalings of
the values of the hidden units by nonzero factors, for attention blocks the changes of basis
inside the heads. The first statements are for any real-analytic blocks, with the change of basis
alone (`s = 0`): they contain tanh and GELU blocks, and are also stated for MLP blocks by name.
For tanh, GELU, SwiGLU, GeGLU and attention blocks both sides hold (Theorem 4.7, Corollary 4.9).

The direction from the equality condition to local identifiability, with the symmetries close to
the identity, is in `Residual/LocalIdentifiability.lean`, `Residual/LocalIdentifiabilityGated.lean`,
`Dimension/LocalIdentifiabilityAttention.lean`, `Residual/LocalIdentifiabilityAttentionRMS.lean`
and `Residual/LocalIdentifiabilityTransformer.lean`; the other direction is
`Dimension/IdentifiableConverseCob.lean` with the upper bounds of Theorem 4.2. Skipless networks:
`Dimension/IdentifiableIff.lean`.
-/

namespace Skips

open Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {sees : T → T → Prop} [DecidableRel sees]
variable {H dh hid : Fin L → Type} [∀ ℓ, Fintype (H ℓ)] [∀ ℓ, Fintype (dh ℓ)]
  [∀ ℓ, DecidableEq (dh ℓ)] [∀ ℓ, Fintype (hid ℓ)] {σ : ℝ → ℝ} {ε : ℝ}

/-! ### Helpers: generic parameters -/

/-- Helper (the private `ae_rank_E_lia` of `Dimension/LocalIdentifiabilityAttention.lean`): at
generic parameters `E` has rank `d`, when `d_in ≥ d`. -/
private theorem ae_rank_E_iffr {A : Arch T d L} (μ : Measure (Params A dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn) :
    ∀ᵐ θ ∂μ, θ.E.rank = Fintype.card d := by
  -- `d` rows `ρ` of `E`, invertible at generic parameters
  obtain ⟨ρ⟩ := Function.Embedding.nonempty_of_card_le hdIn
  filter_upwards [ae_isUnit_det_submatrix μ] with θ hθ
  have h1 : (θ.E.submatrix ρ id).rank = Fintype.card d :=
    Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).2 (hθ.2.2.1 ρ))
  have h2 := Matrix.rank_submatrix_le θ.E ρ id
  have h3 := Matrix.rank_le_card_width θ.E
  omega

/-- Helper: the space `Fin 0 → ℝ` of the families of a network without symmetries inside the
blocks has dimension `0`. -/
private theorem finrank_fin_zero_iffr : Module.finrank ℝ (Fin 0 → ℝ) = 0 :=
  Module.finrank_fin_fun ℝ

/-! ### Helpers: families of parameters of class `C¹` -/

omit [Fintype T] [DecidableEq d] in
/-- Helper: a family of parameters is of class `C¹` on a set if every entry of its four components
is (the parameters are the tuples of their components, by a continuous linear equivalence). -/
private theorem contDiffOn_params_iffr {A : Arch T d L} {N : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] {f : N → Params A dIn dOut} {Ω : Set N}
    (hE : ∀ i j, ContDiffOn ℝ 1 (fun n => (f n).E i j) Ω)
    (hr : ∀ ℓ k j, ContDiffOn ℝ 1 (fun n => (f n).read ℓ k j) Ω)
    (hw : ∀ ℓ j k, ContDiffOn ℝ 1 (fun n => (f n).write ℓ j k) Ω)
    (hD : ∀ k j, ContDiffOn ℝ 1 (fun n => (f n).D k j) Ω) :
    ContDiffOn ℝ 1 f Ω := by
  let e := (Params.linearEquivProd (A := A) (dIn := dIn) (dOut := dOut)).toContinuousLinearEquiv
  rw [← e.comp_contDiffOn_iff]
  -- the four components, entry by entry
  have h : ContDiffOn ℝ 1 (fun n => ((f n).E, (f n).read, (f n).write, (f n).D)) Ω :=
    (contDiffOn_pi' fun i => contDiffOn_pi' fun j => hE i j).prodMk
      ((contDiffOn_pi' fun ℓ => contDiffOn_pi' fun k => contDiffOn_pi' fun j => hr ℓ k j).prodMk
        ((contDiffOn_pi' fun ℓ => contDiffOn_pi' fun j => contDiffOn_pi' fun k =>
          hw ℓ j k).prodMk (contDiffOn_pi' fun k => contDiffOn_pi' fun j => hD k j)))
  exact h

/-! ### Blocks without symmetries inside -/

/-- **Proposition 4.5 of the skips paper, for residual networks of any real-analytic blocks, without
normalization:** `fd = P − d²` at almost every parameter if and only if at almost every parameter
`θ` every `θ'` near `θ` with the same function is `θ` after a change of basis by one invertible `G`
at all hidden states. -/
theorem ae_funDim_residual_iff_ae_locally_cob
    (A : Arch T d L) (hA : A.χ = id)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ)
    (μ : Measure (Params
      A dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn) :
    (∀ᵐ θ ∂μ, funDim A 1 θ
        + Fintype.card d ^ 2
      = Module.finrank ℝ (Params
          A dIn dOut)) ↔
    (∀ᵐ θ ∂μ, ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval A 1 θ' x
        = eval A 1 θ x) →
        ∃ G : GL d ℝ,
            θ' = θ.cob
              (fun _ => G) (fun _ => G)) := by
  constructor
  · -- from the equality condition: Proposition 4.5 at every `θ` where `E` has rank `d`, with no
    -- condition on `G` (the neighbourhood `Set.univ` of the identity)
    intro h
    filter_upwards [h, ae_rank_E_iffr μ hdIn] with θ hfd hE
    obtain ⟨U, hU, hUV⟩ :=
      exists_cob_of_eval_eq_residual A hA hf θ hE hfd Set.univ Filter.univ_mem
    refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
    obtain ⟨G, -, hG⟩ := hUV θ' hθ' heq
    exact ⟨G, hG⟩
  · -- to the equality condition: the lower bound `P ≤ fd + d²` from local identifiability, with
    -- the constant family `Ψ θ n = θ` on the zero space, and the upper bound of Theorem 4.2
    intro h
    have hχ : AnalyticOnNhd ℝ A.χ Set.univ := by
      rw [hA]
      exact analyticOnNhd_id
    have hlow := ae_finrank_le_funDim_add_of_ae_locally_cob_const A 1 hf hχ μ
      (N := Fin 0 → ℝ) (fun θ _ => θ) Set.univ (fun _ => contDiffOn_const) (by
        filter_upwards [h] with θ ⟨U, hU, hUV⟩
        refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
        obtain ⟨G, hG⟩ := hUV θ' hθ' heq
        exact ⟨0, Set.mem_univ _, G, hG⟩)
    have hup := ae_funDim_add_le_residual μ hA
      (fun ℓ => differentiableOn_univ.1 (hf ℓ).differentiableOn) hdIn
    filter_upwards [hlow, hup] with θ h1 h2
    rw [finrank_fin_zero_iffr] at h1
    omega

/-- **Proposition 4.5 of the skips paper, for residual networks of any real-analytic blocks, under
pre-RMSNorm with `ε > 0`:** `fd = P − d(d−1)/2` at almost every parameter if and only if at almost
every parameter `θ` every `θ'` near `θ` with the same function is `θ` after a change of basis by one
orthogonal `Q` at all hidden states. -/
theorem ae_funDim_residual_iff_ae_locally_cob_rmsNorm
    (A : Arch T d L) (hε : 0 < ε) (hA : A.χ = rmsNorm ε)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ)
    (μ : Measure (Params
      A dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn) :
    (∀ᵐ θ ∂μ, funDim A 1 θ
        + Fintype.card d * (Fintype.card d - 1) / 2
      = Module.finrank ℝ (Params
          A dIn dOut)) ↔
    (∀ᵐ θ ∂μ, ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval A 1 θ' x
        = eval A 1 θ x) →
        ∃ Q : GL d ℝ, (Q : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ ∧
            θ' = θ.cob
              (fun _ => Q) (fun _ => Q)) := by
  constructor
  · -- from the equality condition: Proposition 4.5 at every `θ` where `E` has rank `d`, with no
    -- condition on `Q` (the neighbourhood `Set.univ` of the identity)
    intro h
    filter_upwards [h, ae_rank_E_iffr μ hdIn] with θ hfd hE
    obtain ⟨U, hU, hUV⟩ :=
      exists_cob_of_eval_eq_residual_rmsNorm A hε hA hf θ hE hfd Set.univ Filter.univ_mem
    refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
    obtain ⟨Q, hQ, -, hQθ⟩ := hUV θ' hθ' heq
    exact ⟨Q, hQ, hQθ⟩
  · -- to the equality condition: the lower bound `P ≤ fd + d(d-1)/2` from local
    -- identifiability, with the constant family `Ψ θ n = θ` on the zero space, and the upper
    -- bound of Theorem 4.2
    intro h
    have hχ : AnalyticOnNhd ℝ A.χ Set.univ := by
      rw [hA]
      exact analyticOnNhd_rmsNorm hε
    have hlow := ae_finrank_le_funDim_add_of_ae_locally_cob_const_orthogonal A 1 hf hχ μ
      (N := Fin 0 → ℝ) (fun θ _ => θ) Set.univ (fun _ => contDiffOn_const) (by
        filter_upwards [h] with θ ⟨U, hU, hUV⟩
        refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
        obtain ⟨Q, hQ, hQθ⟩ := hUV θ' hθ' heq
        exact ⟨0, Set.mem_univ _, Q, hQ, hQθ⟩)
    have hup := ae_funDim_add_le_residual_rmsNorm μ hε hA
      (fun ℓ => differentiableOn_univ.1 (hf ℓ).differentiableOn) hdIn
    filter_upwards [hlow, hup] with θ h1 h2
    rw [finrank_fin_zero_iffr] at h1
    generalize Fintype.card d * (Fintype.card d - 1) / 2 = a at h1 h2 ⊢
    omega

/-- **Proposition 4.5 of the skips paper, for residual networks of MLP blocks with a real-analytic
activation (tanh, GELU), without normalization:** `fd = P − d²` at almost every parameter if and
only if at almost every parameter `θ` every `θ'` near `θ` with the same function is `θ` after a
change of basis by one invertible `G` at all hidden states. -/
theorem ae_funDim_mlp_residual_iff_ae_locally_cob
    (hσ : AnalyticOnNhd ℝ σ Set.univ)
    (μ : Measure (Params
      (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn) :
    (∀ᵐ θ ∂μ, funDim (Arch.mlp σ id hid) 1 θ
        + Fintype.card d ^ 2
      = Module.finrank ℝ (Params
          (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)) ↔
    (∀ᵐ θ ∂μ, ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.mlp σ id hid) 1 θ' x
        = eval (Arch.mlp σ id hid) 1 θ x) →
        ∃ G : GL d ℝ,
            θ' = θ.cob
              (fun _ => G) (fun _ => G)) := by
  -- the MLP blocks are real-analytic
  exact ae_funDim_residual_iff_ae_locally_cob _ rfl (fun ℓ => analyticOnNhd_f_mlp hσ ℓ) μ hdIn

/-- **Proposition 4.5 of the skips paper, for residual networks of MLP blocks with a real-analytic
activation (tanh, GELU), under pre-RMSNorm with `ε > 0`:** `fd = P − d(d−1)/2` at almost every
parameter if and only if at almost every parameter `θ` every `θ'` near `θ` with the same function is
`θ` after a change of basis by one orthogonal `Q` at all hidden states. -/
theorem ae_funDim_mlp_residual_iff_ae_locally_cob_rmsNorm
    (hε : 0 < ε) (hσ : AnalyticOnNhd ℝ σ Set.univ)
    (μ : Measure (Params
      (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn) :
    (∀ᵐ θ ∂μ, funDim (Arch.mlp σ (rmsNorm ε) hid) 1 θ
        + Fintype.card d * (Fintype.card d - 1) / 2
      = Module.finrank ℝ (Params
          (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)) ↔
    (∀ᵐ θ ∂μ, ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.mlp σ (rmsNorm ε) hid) 1 θ' x
        = eval (Arch.mlp σ (rmsNorm ε) hid) 1 θ x) →
        ∃ Q : GL d ℝ, (Q : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ ∧
            θ' = θ.cob
              (fun _ => Q) (fun _ => Q)) := by
  -- the MLP blocks are real-analytic
  exact ae_funDim_residual_iff_ae_locally_cob_rmsNorm _ hε rfl
    (fun ℓ => analyticOnNhd_f_mlp hσ ℓ) μ hdIn

/-! ### Gated blocks -/

/-- Helper: the space of the factors of the rescalings has dimension `s = ∑ d_hidden`. -/
private theorem finrank_hidFun_iffr :
    Module.finrank ℝ (∀ ℓ, hid ℓ → ℝ) = ∑ ℓ, Fintype.card (hid ℓ) := by
  rw [Module.finrank_pi_fintype]
  simp only [Module.finrank_fintype_fun_eq_card]

omit [Fintype T] [DecidableEq d] in
/-- Helper: the rescalings `c ↦ θ.rescale c` are of class `C¹` where no factor vanishes (the
values are divided by the factors, the outputs multiplied by them). -/
private theorem contDiffOn_rescale_iffr {χ : Matrix T d ℝ → Matrix T d ℝ}
    (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut) :
    ContDiffOn ℝ 1 (fun c => θ.rescale c) {c : ∀ ℓ, hid ℓ → ℝ | ∀ ℓ i, c ℓ i ≠ 0} := by
  refine contDiffOn_params_iffr (fun i j => contDiffOn_const (c := θ.E i j)) (fun ℓ k j => ?_)
    (fun ℓ i k => ?_) (fun k j => contDiffOn_const (c := θ.D k j))
  · rcases j with i | i
    · -- the gate columns do not change
      exact contDiffOn_const (c := θ.read ℓ k (Sum.inl i))
    · -- the value columns are divided by `c_{ℓ i}`, which does not vanish on the set
      have hc : ContDiff ℝ 1 fun c : (∀ ℓ, hid ℓ → ℝ) => c ℓ i := by fun_prop
      exact (hc.contDiffOn.inv fun c (hc0 : ∀ ℓ i, c ℓ i ≠ 0) => hc0 ℓ i).mul contDiffOn_const
  · -- the output rows are multiplied by `c_{ℓ i}`
    have hc : ContDiff ℝ 1 fun c : (∀ ℓ, hid ℓ → ℝ) => c ℓ i := by fun_prop
    exact (hc.mul contDiff_const).contDiffOn

/-- **Proposition 4.5 of the skips paper, for residual networks of gated blocks with a real-analytic
gate (SwiGLU, GeGLU), without normalization:** `fd = P − d² − s` at almost every parameter (`s = ∑
d_hidden`) if and only if at almost every parameter `θ` every `θ'` near `θ` with the same function
is `θ` after a rescaling of the values of the hidden units by nonzero factors `c` and a change of
basis by one invertible `G` at all hidden states. -/
theorem ae_funDim_gated_residual_iff_ae_locally_cob_rescale
    [Nonempty d] (hσ : AnalyticOnNhd ℝ σ Set.univ)
    (μ : Measure (Params
      (Arch.gated (T := T) (d := d) σ id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn) :
    (∀ᵐ θ ∂μ, funDim (Arch.gated σ id hid) 1 θ
        + (Fintype.card d ^ 2
          + ∑ ℓ, Fintype.card (hid ℓ))
      = Module.finrank ℝ (Params
          (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)) ↔
    (∀ᵐ θ ∂μ, ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.gated σ id hid) 1 θ' x
        = eval (Arch.gated σ id hid) 1 θ x) →
        ∃ c : ∀ ℓ, hid ℓ → ℝ, (∀ ℓ i, c ℓ i ≠ 0) ∧
          ∃ G : GL d ℝ,
            θ' = (θ.rescale c).cob
              (fun _ => G) (fun _ => G)) := by
  constructor
  · -- from the equality condition: Proposition 4.5 at every `θ` where `E` has rank `d` and no
    -- value column vanishes, with no condition on `G` and `c` (the neighbourhoods `Set.univ`)
    intro h
    filter_upwards [h, ae_rank_E_iffr μ hdIn, ae_value_ne_zero μ] with θ hfd hE hv
    obtain ⟨U, hU, hUV⟩ := exists_cob_rescale_of_eval_eq_residual_gated hσ θ hE hv hfd
      Set.univ Filter.univ_mem Set.univ Filter.univ_mem
    refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
    obtain ⟨G, c, -, -, hc0, hθ'⟩ := hUV θ' hθ' heq
    exact ⟨c, fun ℓ i => (hc0 ℓ i).ne', G, hθ'⟩
  · -- to the equality condition: the lower bound `P ≤ fd + d² + s` from local identifiability,
    -- with the rescalings `Ψ θ c = θ.rescale c` on the factors without zero, and the upper bound
    -- of Theorem 4.2
    intro h
    have hlow := ae_finrank_le_funDim_add_of_ae_locally_cob_const
      (Arch.gated (T := T) (d := d) σ id hid) 1 (fun ℓ => analyticOnNhd_f_gated hσ ℓ)
      analyticOnNhd_id μ (fun θ c => θ.rescale c) {c | ∀ ℓ i, c ℓ i ≠ 0}
      (fun θ => contDiffOn_rescale_iffr θ) (by
        filter_upwards [h] with θ ⟨U, hU, hUV⟩
        refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
        obtain ⟨c, hc, G, hG⟩ := hUV θ' hθ' heq
        exact ⟨c, hc, G, hG⟩)
    have hup := ae_funDim_add_le_residual_gated μ hdIn
    filter_upwards [hlow, hup] with θ h1 h2
    rw [finrank_hidFun_iffr] at h1
    generalize ∑ ℓ, Fintype.card (hid ℓ) = s at h1 h2 ⊢
    omega

/-- **Proposition 4.5 of the skips paper, for residual networks of gated blocks with a real-analytic
gate (SwiGLU, GeGLU), under pre-RMSNorm with `ε > 0`:** `fd = P − d(d−1)/2 − s` at almost every
parameter (`s = ∑ d_hidden`) if and only if at almost every parameter `θ` every `θ'` near `θ` with
the same function is `θ` after a rescaling of the values of the hidden units by nonzero factors `c`
and a change of basis by one orthogonal `Q` at all hidden states. -/
theorem ae_funDim_gated_residual_iff_ae_locally_cob_rescale_rmsNorm
    (hε : 0 < ε) [Nonempty d] (hσ : AnalyticOnNhd ℝ σ Set.univ)
    (μ : Measure (Params
      (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn) :
    (∀ᵐ θ ∂μ, funDim (Arch.gated σ (rmsNorm ε) hid) 1 θ
        + (Fintype.card d * (Fintype.card d - 1) / 2
          + ∑ ℓ, Fintype.card (hid ℓ))
      = Module.finrank ℝ (Params
          (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)) ↔
    (∀ᵐ θ ∂μ, ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.gated σ (rmsNorm ε) hid) 1 θ' x
        = eval (Arch.gated σ (rmsNorm ε) hid) 1 θ x) →
        ∃ c : ∀ ℓ, hid ℓ → ℝ, (∀ ℓ i, c ℓ i ≠ 0) ∧
          ∃ Q : GL d ℝ, (Q : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ ∧
            θ' = (θ.rescale c).cob
              (fun _ => Q) (fun _ => Q)) := by
  constructor
  · -- from the equality condition: Proposition 4.5 at every `θ` where `E` has rank `d` and no
    -- value column vanishes, with no condition on `Q` and `c` (the neighbourhoods `Set.univ`)
    intro h
    filter_upwards [h, ae_rank_E_iffr μ hdIn, ae_value_ne_zero μ] with θ hfd hE hv
    obtain ⟨U, hU, hUV⟩ := exists_cob_rescale_of_eval_eq_residual_gated_rmsNorm hε hσ θ hE hv hfd
      Set.univ Filter.univ_mem Set.univ Filter.univ_mem
    refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
    obtain ⟨Q, c, hQ, -, -, hc0, hθ'⟩ := hUV θ' hθ' heq
    exact ⟨c, fun ℓ i => (hc0 ℓ i).ne', Q, hQ, hθ'⟩
  · -- to the equality condition: the lower bound `P ≤ fd + d(d-1)/2 + s` from local
    -- identifiability, with the rescalings `Ψ θ c = θ.rescale c` on the factors without zero, and
    -- the upper bound of Theorem 4.2
    intro h
    have hlow := ae_finrank_le_funDim_add_of_ae_locally_cob_const_orthogonal
      (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) 1 (fun ℓ => analyticOnNhd_f_gated hσ ℓ)
      (analyticOnNhd_rmsNorm hε) μ (fun θ c => θ.rescale c) {c | ∀ ℓ i, c ℓ i ≠ 0}
      (fun θ => contDiffOn_rescale_iffr θ) (by
        filter_upwards [h] with θ ⟨U, hU, hUV⟩
        refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
        obtain ⟨c, hc, Q, hQ, hQθ⟩ := hUV θ' hθ' heq
        exact ⟨c, hc, Q, hQ, hQθ⟩)
    have hup := ae_funDim_add_le_residual_gated_rmsNorm ε μ hdIn
    filter_upwards [hlow, hup] with θ h1 h2
    rw [finrank_hidFun_iffr] at h1
    generalize ∑ ℓ, Fintype.card (hid ℓ) = s at h1 h2 ⊢
    generalize Fintype.card d * (Fintype.card d - 1) / 2 = a at h1 h2 ⊢
    omega

/-- **Proposition 4.5 of the skips paper, for residual networks of attention blocks, without
normalization:** `fd = P − d² − s` at almost every parameter (`s = 2 ∑ H d_h²`) if and only if at
almost every parameter `θ` every `θ'` near `θ` with the same function is `θ` after changes of basis
inside the heads and a change of basis by one invertible `G` at all hidden states. -/
theorem ae_funDim_attention_residual_iff_ae_locally_cob_heads
    (μ : Measure (Params
      (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) :
    (∀ᵐ θ ∂μ, funDim (Arch.attention sees id H dh) 1 θ
        + (Fintype.card d ^ 2
          + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
      = Module.finrank ℝ (Params
          (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut)) ↔
    (∀ᵐ θ ∂μ, ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.attention sees id H dh) 1 θ' x
        = eval (Arch.attention sees id H dh) 1 θ x) →
        ∃ K K' : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ,
          ∃ G : GL d ℝ,
            θ' = ((θ.headsQK K).headsVO K').cob
              (fun _ => G) (fun _ => G)) := by
  sorry

/-- **Proposition 4.5 of the skips paper, for residual networks of attention blocks, under
pre-RMSNorm with `ε > 0`:** `fd = P − d(d−1)/2 − s` at almost every parameter (`s = 2 ∑ H d_h²`) if
and only if at almost every parameter `θ` every `θ'` near `θ` with the same function is `θ` after
changes of basis inside the heads and a change of basis by one orthogonal `Q` at all hidden states.
-/
theorem ae_funDim_attention_residual_iff_ae_locally_cob_heads_rmsNorm
    (hε : 0 < ε)
    (μ : Measure (Params
      (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) :
    (∀ᵐ θ ∂μ, funDim (Arch.attention sees (rmsNorm ε) H dh) 1 θ
        + (Fintype.card d * (Fintype.card d - 1) / 2
          + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
      = Module.finrank ℝ (Params
          (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut)) ↔
    (∀ᵐ θ ∂μ, ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.attention sees (rmsNorm ε) H dh) 1 θ' x
        = eval (Arch.attention sees (rmsNorm ε) H dh) 1 θ x) →
        ∃ K K' : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ,
          ∃ Q : GL d ℝ, (Q : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ ∧
            θ' = ((θ.headsQK K).headsVO K').cob
              (fun _ => Q) (fun _ => Q)) := by
  sorry

/-- **Proposition 4.5 of the skips paper, for residual networks of attention blocks and MLP blocks
with a real-analytic activation, in any order, without normalization:** `fd = P − d² − s` at almost
every parameter (`s = 2 ∑ H d_h²`) if and only if at almost every parameter `θ` every `θ'` near `θ`
with the same function is `θ` after changes of basis inside the heads and a change of basis by one
invertible `G` at all hidden states. -/
theorem ae_funDim_attentionMlp_residual_iff_ae_locally_cob_heads
    (hσ : AnalyticOnNhd ℝ σ Set.univ)
    (μ : Measure (Params
      (Arch.attentionMlp (T := T) (d := d) sees σ id H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) :
    (∀ᵐ θ ∂μ, funDim (Arch.attentionMlp sees σ id H dh hid) 1 θ
        + (Fintype.card d ^ 2
          + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
      = Module.finrank ℝ (Params
          (Arch.attentionMlp (T := T) (d := d) sees σ id H dh hid) dIn dOut)) ↔
    (∀ᵐ θ ∂μ, ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.attentionMlp sees σ id H dh hid) 1 θ' x
        = eval (Arch.attentionMlp sees σ id H dh hid) 1 θ x) →
        ∃ K K' : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ,
          ∃ G : GL d ℝ,
            θ' = (Params.sumOf ((θ.sumFst.headsQK K).headsVO K') θ.sumSnd).cob
              (fun _ => G) (fun _ => G)) := by
  sorry

/-- **Proposition 4.5 of the skips paper, for residual networks of attention blocks and MLP blocks
with a real-analytic activation, in any order, under pre-RMSNorm with `ε > 0`:** `fd = P − d(d−1)/2
− s` at almost every parameter (`s = 2 ∑ H d_h²`) if and only if at almost every parameter `θ` every
`θ'` near `θ` with the same function is `θ` after changes of basis inside the heads and a change of
basis by one orthogonal `Q` at all hidden states. -/
theorem ae_funDim_attentionMlp_residual_iff_ae_locally_cob_heads_rmsNorm
    (hε : 0 < ε) (hσ : AnalyticOnNhd ℝ σ Set.univ)
    (μ : Measure (Params
      (Arch.attentionMlp (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) :
    (∀ᵐ θ ∂μ, funDim (Arch.attentionMlp sees σ (rmsNorm ε) H dh hid) 1 θ
        + (Fintype.card d * (Fintype.card d - 1) / 2
          + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
      = Module.finrank ℝ (Params
          (Arch.attentionMlp (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut)) ↔
    (∀ᵐ θ ∂μ, ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.attentionMlp sees σ (rmsNorm ε) H dh hid) 1 θ' x
        = eval (Arch.attentionMlp sees σ (rmsNorm ε) H dh hid) 1 θ x) →
        ∃ K K' : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ,
          ∃ Q : GL d ℝ, (Q : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ ∧
            θ' = (Params.sumOf ((θ.sumFst.headsQK K).headsVO K') θ.sumSnd).cob
              (fun _ => Q) (fun _ => Q)) := by
  sorry

/-- **Proposition 4.5 of the skips paper, for residual networks of attention blocks and gated blocks
with a real-analytic gate, in any order, without normalization:** `fd = P − d² − s` at almost every
parameter (`s = 2 ∑ H d_h² + ∑ d_hidden`) if and only if at almost every parameter `θ` every `θ'`
near `θ` with the same function is `θ` after changes of basis inside the heads, a rescaling of the
values of the hidden units by nonzero factors `c` and a change of basis by one invertible `G` at all
hidden states. -/
theorem ae_funDim_attentionGated_residual_iff_ae_locally_cob_heads_rescale
    [Nonempty d] (hσ : AnalyticOnNhd ℝ σ Set.univ)
    (μ : Measure (Params
      (Arch.attentionGated (T := T) (d := d) sees σ id H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) :
    (∀ᵐ θ ∂μ, funDim (Arch.attentionGated sees σ id H dh hid) 1 θ
        + (Fintype.card d ^ 2
          + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
            + ∑ ℓ, Fintype.card (hid ℓ)))
      = Module.finrank ℝ (Params
          (Arch.attentionGated (T := T) (d := d) sees σ id H dh hid) dIn dOut)) ↔
    (∀ᵐ θ ∂μ, ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.attentionGated sees σ id H dh hid) 1 θ' x
        = eval (Arch.attentionGated sees σ id H dh hid) 1 θ x) →
        ∃ (K K' : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ) (c : ∀ ℓ, hid ℓ → ℝ), (∀ ℓ i, c ℓ i ≠ 0) ∧
          ∃ G : GL d ℝ,
            θ' = (Params.sumOf ((θ.sumFst.headsQK K).headsVO K') (θ.sumSnd.rescale c)).cob
              (fun _ => G) (fun _ => G)) := by
  sorry

/-- **Proposition 4.5 of the skips paper, for residual networks of attention blocks and gated blocks
with a real-analytic gate, in any order, under pre-RMSNorm with `ε > 0`:** `fd = P − d(d−1)/2 − s`
at almost every parameter (`s = 2 ∑ H d_h² + ∑ d_hidden`) if and only if at almost every parameter
`θ` every `θ'` near `θ` with the same function is `θ` after changes of basis inside the heads, a
rescaling of the values of the hidden units by nonzero factors `c` and a change of basis by one
orthogonal `Q` at all hidden states. -/
theorem ae_funDim_attentionGated_residual_iff_ae_locally_cob_heads_rescale_rmsNorm
    (hε : 0 < ε) [Nonempty d] (hσ : AnalyticOnNhd ℝ σ Set.univ)
    (μ : Measure (Params
      (Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) :
    (∀ᵐ θ ∂μ, funDim (Arch.attentionGated sees σ (rmsNorm ε) H dh hid) 1 θ
        + (Fintype.card d * (Fintype.card d - 1) / 2
          + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
            + ∑ ℓ, Fintype.card (hid ℓ)))
      = Module.finrank ℝ (Params
          (Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut)) ↔
    (∀ᵐ θ ∂μ, ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.attentionGated sees σ (rmsNorm ε) H dh hid) 1 θ' x
        = eval (Arch.attentionGated sees σ (rmsNorm ε) H dh hid) 1 θ x) →
        ∃ (K K' : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ) (c : ∀ ℓ, hid ℓ → ℝ), (∀ ℓ i, c ℓ i ≠ 0) ∧
          ∃ Q : GL d ℝ, (Q : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ ∧
            θ' = (Params.sumOf ((θ.sumFst.headsQK K).headsVO K') (θ.sumSnd.rescale c)).cob
              (fun _ => Q) (fun _ => Q)) := by
  sorry

end Skips
