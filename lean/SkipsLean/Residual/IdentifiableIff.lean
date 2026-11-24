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
function is the image of `θ` under a symmetry". The symmetries are the continuous symmetries of
the paper: one change of basis at all hidden states (orthogonal under pre-RMSNorm), for gated
blocks the rescalings of the values of the hidden units by nonzero factors, for attention blocks
the changes of basis inside the heads. The permutations of hidden units or heads and the sign
flips of tanh units, which the paper lists among the symmetries inside the blocks and counts in
the proof of the converse, are not in the family: the direction from local identifiability to the
equality condition is proved here for this smaller family. The first statements are for any real-analytic blocks, with the change of basis
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

/-! ### Attention blocks -/

/-- Helper: the determinant of a matrix whose entries are `C¹` is `C¹` (a polynomial in the
entries). -/
private theorem contDiff_det_iffr {m X : Type*} [Fintype m] [DecidableEq m] [NormedAddCommGroup X]
    [NormedSpace ℝ X] {g : X → Matrix m m ℝ} (hg : ∀ a b, ContDiff ℝ 1 fun x => g x a b) :
    ContDiff ℝ 1 fun x => (g x).det := by
  simp only [Matrix.det_apply']
  exact ContDiff.sum fun τ _ => contDiff_const.mul (contDiff_prod fun i _ => hg (τ i) i)

/-- Helper: the entries of the inverse of a matrix whose entries are `C¹` are `C¹` where the
matrix is invertible: `A⁻¹ = det(A)⁻¹ adj(A)`, and the entries of the adjugate are
determinants. -/
private theorem contDiffOn_inv_entry_iffr {m X : Type*} [Fintype m] [DecidableEq m]
    [NormedAddCommGroup X] [NormedSpace ℝ X] {g : X → Matrix m m ℝ}
    (hg : ∀ a b, ContDiff ℝ 1 fun x => g x a b) {s : Set X} (hs : ∀ x ∈ s, IsUnit (g x))
    (a b : m) : ContDiffOn ℝ 1 (fun x => (g x)⁻¹ a b) s := by
  have h1 : (fun x => (g x)⁻¹ a b)
      = fun x => ((g x).det)⁻¹ * ((g x).updateRow b (Pi.single a 1)).det := by
    funext x
    rw [Matrix.inv_def, Matrix.smul_apply, Matrix.adjugate_apply, Ring.inverse_eq_inv, smul_eq_mul]
  rw [h1]
  have hdet : ContDiff ℝ 1 fun x => (g x).det := contDiff_det_iffr hg
  -- the matrix of the adjugate entry: row `b` replaced by the unit row `a`
  have hadj : ContDiff ℝ 1 fun x => ((g x).updateRow b (Pi.single a 1)).det := by
    refine contDiff_det_iffr fun i j => ?_
    rcases eq_or_ne i b with rfl | h
    · simp only [Matrix.updateRow_self]
      exact contDiff_const
    · simp only [Matrix.updateRow_ne h]
      exact hg i j
  exact (hdet.contDiffOn.inv fun x hx =>
    ((Matrix.isUnit_iff_isUnit_det _).1 (hs x hx)).ne_zero).mul hadj.contDiffOn

omit [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] [∀ ℓ, DecidableEq (dh ℓ)] in
/-- Helper: the parameters `(θ.headsQK K).headsVO K'` written with the matrices `K`, `K'` and,
as separate arguments, their inverses `Ki`, `K'i`: the query columns `W_Q K`, the key columns
`W_K Kiᵀ`, the value columns `W_V K'`, the output rows `K'i W_O`. -/
private noncomputable def headsMat_iffr {χ : Matrix T d ℝ → Matrix T d ℝ}
    (θ : Params (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut)
    (K Ki K' K'i : ∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) :
    Params (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut where
  E := θ.E
  read ℓ := Matrix.of fun a p =>
    match p.2 with
    | Sum.inl k => ∑ k', θ.read ℓ a (p.1, Sum.inl k') * K ℓ p.1 k' k
    | Sum.inr (Sum.inl k) => ∑ k', θ.read ℓ a (p.1, Sum.inr (Sum.inl k')) * Ki ℓ p.1 k k'
    | Sum.inr (Sum.inr k) => ∑ k', θ.read ℓ a (p.1, Sum.inr (Sum.inr k')) * K' ℓ p.1 k' k
  write ℓ := Matrix.of fun (p : H ℓ × dh ℓ) b => ∑ k', K'i ℓ p.1 p.2 k' * θ.write ℓ (p.1, k') b
  D := θ.D

omit [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] [∀ ℓ, DecidableEq (dh ℓ)] in
/-- Helper: the family of the changes of basis inside the heads, at the pairs `n = (k, k')` of
families of matrices, with the matrix inverses of `k`, `k'`. -/
private noncomputable def headsFam_iffr {χ : Matrix T d ℝ → Matrix T d ℝ}
    (θ : Params (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut)
    (n : (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)) :
    Params (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut :=
  headsMat_iffr θ n.1 (fun ℓ i => (n.1 ℓ i)⁻¹) n.2 (fun ℓ i => (n.2 ℓ i)⁻¹)

omit [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: at the invertible matrices of `K`, `K'`, the family is `(θ.headsQK K).headsVO K'`. -/
private theorem headsFam_coe_iffr {χ : Matrix T d ℝ → Matrix T d ℝ}
    (θ : Params (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut)
    (K K' : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ) :
    headsFam_iffr θ (fun ℓ i => (K ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ),
      fun ℓ i => (K' ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)) = (θ.headsQK K).headsVO K' := by
  -- the matrix inverse of `K` is the matrix of `K⁻¹`
  simp only [headsFam_iffr, ← Matrix.coe_units_inv]
  refine Params.ext' rfl (fun ℓ => ?_) (fun ℓ => rfl) rfl
  ext a p
  rcases p with ⟨i, k | k | k⟩ <;> rfl

omit [DecidableEq d] in
/-- Helper: the family of the changes of basis inside the heads is `C¹` where the matrices are
invertible. -/
private theorem contDiffOn_headsFam_iffr {χ : Matrix T d ℝ → Matrix T d ℝ}
    (θ : Params (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut) :
    ContDiffOn ℝ 1 (headsFam_iffr θ)
      {n | ∀ ℓ i, IsUnit (n.1 ℓ i) ∧ IsUnit (n.2 ℓ i)} := by
  refine contDiffOn_params_iffr (fun i j => contDiffOn_const (c := θ.E i j)) (fun ℓ a p => ?_)
    (fun ℓ p b => ?_) (fun k j => contDiffOn_const (c := θ.D k j))
  · rcases p with ⟨i, k | k | k⟩
    · -- the query columns `W_Q k`
      have hk : ∀ k', ContDiff ℝ 1 fun n : (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)
          × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) => n.1 ℓ i k' k := fun k' => by fun_prop
      exact (ContDiff.sum fun k' _ => contDiff_const.mul (hk k')).contDiffOn
    · -- the key columns `W_K (k⁻¹)ᵀ`
      exact ContDiffOn.sum fun k' _ => contDiffOn_const.mul
        (contDiffOn_inv_entry_iffr (g := fun n : (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)
          × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) => n.1 ℓ i) (fun _ _ => by fun_prop)
          (fun n (hn : ∀ ℓ i, IsUnit (n.1 ℓ i) ∧ IsUnit (n.2 ℓ i)) => (hn ℓ i).1) k k')
    · -- the value columns `W_V k'`
      have hk : ∀ k', ContDiff ℝ 1 fun n : (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)
          × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) => n.2 ℓ i k' k := fun k' => by fun_prop
      exact (ContDiff.sum fun k' _ => contDiff_const.mul (hk k')).contDiffOn
  · -- the output rows `k'⁻¹ W_O`
    rcases p with ⟨i, k⟩
    exact ContDiffOn.sum fun k' _ => ContDiffOn.mul
      (contDiffOn_inv_entry_iffr (g := fun n : (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)
        × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) => n.2 ℓ i) (fun _ _ => by fun_prop)
        (fun n (hn : ∀ ℓ i, IsUnit (n.1 ℓ i) ∧ IsUnit (n.2 ℓ i)) => (hn ℓ i).2) k k')
      contDiffOn_const

omit [∀ ℓ, DecidableEq (dh ℓ)] in
/-- Helper (the private `finrank_headFun_lia`): the families of matrices of the heads form a
space of dimension `∑_ℓ H_ℓ d_{h,ℓ}²`. -/
private theorem finrank_headFun_iffr :
    Module.finrank ℝ (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)
      = ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2 := by
  rw [Module.finrank_pi_fintype]
  simp only [Module.finrank_pi_fintype, Module.finrank_matrix, Module.finrank_self, mul_one,
    Finset.sum_const, Finset.card_univ, smul_eq_mul, sq]

omit [Fintype T] [DecidableEq d] in
/-- Helper (the private `analyticOnNhd_det_lia`): the determinant of a square matrix that depends
linearly on the parameters is an analytic function of the parameters. -/
private theorem analyticOnNhd_det_iffr {A : Arch T d L} {n : Type*} [Fintype n] [DecidableEq n]
    (Φ : Params A dIn dOut →ₗ[ℝ] Matrix n n ℝ) :
    AnalyticOnNhd ℝ (fun θ => (Φ θ).det) Set.univ := by
  simp only [Matrix.det_apply']
  exact Finset.analyticOnNhd_fun_sum _ fun σ _ => analyticOnNhd_const.mul
    (Finset.analyticOnNhd_fun_prod _ fun i _ =>
      analyticOnNhd_linear ((Matrix.entryLinearMap ℝ ℝ (σ i) i).comp Φ))

/-- Helper (the private `exists_submatrix_eq_one_lia`): a matrix whose submatrix on the rows `r`
and the columns `c` (both injective) is the identity. -/
private theorem exists_submatrix_eq_one_iffr {m p n : Type*} [DecidableEq n] {r : n → m}
    (hr : Function.Injective r) {c : n → p} (hc : Function.Injective c) :
    ∃ M : Matrix m p ℝ, M.submatrix r c = 1 := by
  classical
  refine ⟨Matrix.of fun a b => if ∃ x, r x = a ∧ c x = b then 1 else 0, ?_⟩
  ext x y
  simp [Matrix.one_apply, hr.eq_iff, hc.eq_iff]

omit [Fintype T] [DecidableEq d] in
/-- Helper (the private `ae_rank_read_cols_lia`): at generic parameters, `n ≤ d` distinct
columns `c` of the read of block `ℓ` form a matrix of rank `n`. -/
private theorem ae_rank_read_cols_iffr {A : Arch T d L} (μ : Measure (Params A dIn dOut))
    [μ.IsAddHaarMeasure] (ℓ : Fin L) {n : Type*} [Fintype n] [DecidableEq n] {c : n → A.r ℓ}
    (hc : Function.Injective c) (hn : Fintype.card n ≤ Fintype.card d) :
    ∀ᵐ θ ∂μ, ((θ.read ℓ).submatrix id c).rank = Fintype.card n := by
  -- `n` rows `ρ`, and the square submatrix of the read on the rows `ρ` and the columns `c`
  obtain ⟨ρ⟩ := Function.Embedding.nonempty_of_card_le hn
  obtain ⟨M, hM⟩ := exists_submatrix_eq_one_iffr ρ.injective hc
  let Φ : Params A dIn dOut →ₗ[ℝ] Matrix n n ℝ :=
    { toFun := fun θ => ((θ.read ℓ).submatrix id c).submatrix ρ id
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  -- it is the identity at the parameter whose read `ℓ` is `M`, so its determinant is not
  -- identically zero, and it is nonzero almost everywhere
  have hne : ∃ θ, (Φ θ).det ≠ 0 := by
    refine ⟨⟨0, Pi.single ℓ M, 0, 0⟩, ?_⟩
    show ((Pi.single (M := fun ℓ => Matrix d (A.r ℓ) ℝ) ℓ M ℓ).submatrix ρ c).det ≠ 0
    rw [Pi.single_eq_same, hM, Matrix.det_one]
    exact one_ne_zero
  filter_upwards [ae_ne_zero_of_analytic μ (analyticOnNhd_det_iffr Φ) hne] with θ hθ
  -- an invertible `n × n` submatrix gives rank `≥ n`, and the rank is at most the width `n`
  have h1 : (((θ.read ℓ).submatrix id c).submatrix ρ id).rank = Fintype.card n :=
    Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hθ))
  have h2 : (((θ.read ℓ).submatrix id c).submatrix ρ id).rank
      ≤ ((θ.read ℓ).submatrix id c).rank :=
    Matrix.rank_submatrix_le _ ρ id
  have h3 := Matrix.rank_le_card_width ((θ.read ℓ).submatrix id c)
  omega

omit [DecidableEq d] in
/-- Helper (the private `ae_rank_QV_lia`): at generic parameters the query matrix and the value
matrix of every head have rank `d_h`, when `d_h ≤ d`. -/
private theorem ae_rank_QV_iffr {χ : Matrix T d ℝ → Matrix T d ℝ}
    (μ : Measure (Params (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut))
    [μ.IsAddHaarMeasure] (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) :
    ∀ᵐ θ ∂μ, (∀ ℓ (i : H ℓ), ((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k)).rank
        = Fintype.card (dh ℓ)) ∧
      ∀ ℓ (i : H ℓ), ((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))).rank
        = Fintype.card (dh ℓ) := by
  -- finitely many conditions, two for each head of each block
  refine (ae_all_iff.2 fun ℓ => ae_all_iff.2 fun i => ?_).and
    (ae_all_iff.2 fun ℓ => ae_all_iff.2 fun i => ?_)
  · exact ae_rank_read_cols_iffr μ ℓ (c := fun k : dh ℓ => (i, Sum.inl k))
      (fun _ _ h => Sum.inl_injective (Prod.mk.inj h).2) (hdh ℓ)
  · exact ae_rank_read_cols_iffr μ ℓ (c := fun k : dh ℓ => (i, Sum.inr (Sum.inr k)))
      (fun _ _ h => Sum.inr_injective (Sum.inr_injective (Prod.mk.inj h).2)) (hdh ℓ)

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
  constructor
  · -- from the equality condition: Proposition 4.5 at every `θ` where `E` has rank `d` and the
    -- query and value matrices of every head have rank `d_h`, with no condition on `G`, `K`, `K'`
    intro h
    filter_upwards [h, ae_rank_E_iffr μ hdIn, ae_rank_QV_iffr μ hdh] with θ hfd hE hQV
    obtain ⟨U, hU, hUV⟩ := exists_cob_heads_of_eval_eq_residual_attention θ hE hQV.1 hQV.2 hfd
      Set.univ Filter.univ_mem Set.univ Filter.univ_mem
    refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
    obtain ⟨G, K, K', -, -, -, hθ'⟩ := hUV θ' hθ' heq
    exact ⟨K, K', G, hθ'⟩
  · -- to the equality condition: the lower bound `P ≤ fd + d² + 2 ∑ H d_h²` from local
    -- identifiability, with the changes of basis inside the heads at pairs of families of
    -- invertible matrices, and the upper bound of Theorem 4.2
    intro h
    have hlow := ae_finrank_le_funDim_add_of_ae_locally_cob_const
      (Arch.attention (T := T) (d := d) sees id H dh) 1
      (fun ℓ => analyticOnNhd_f_attention sees id H dh ℓ) analyticOnNhd_id μ headsFam_iffr
      {n | ∀ ℓ i, IsUnit (n.1 ℓ i) ∧ IsUnit (n.2 ℓ i)} (fun θ => contDiffOn_headsFam_iffr θ) (by
        filter_upwards [h] with θ ⟨U, hU, hUV⟩
        refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
        obtain ⟨K, K', G, hG⟩ := hUV θ' hθ' heq
        refine ⟨(fun ℓ i => (K ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ),
          fun ℓ i => (K' ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)),
          fun ℓ i => ⟨(K ℓ i).isUnit, (K' ℓ i).isUnit⟩, G, ?_⟩
        rw [headsFam_coe_iffr]
        exact hG)
    have hup := ae_funDim_add_le_residual_attention μ hdIn hdh
    filter_upwards [hlow, hup] with θ h1 h2
    rw [Module.finrank_prod, finrank_headFun_iffr] at h1
    generalize ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2 = s at h1 h2 ⊢
    omega

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
  constructor
  · -- from the equality condition: Proposition 4.5 at every `θ` where `E` has rank `d` and the
    -- query and value matrices of every head have rank `d_h`, with no condition on `Q`, `K`, `K'`
    intro h
    filter_upwards [h, ae_rank_E_iffr μ hdIn, ae_rank_QV_iffr μ hdh] with θ hfd hE hQV
    obtain ⟨U, hU, hUV⟩ := exists_cob_heads_of_eval_eq_residual_attention_rmsNorm hε θ hE hQV.1
      hQV.2 hfd Set.univ Filter.univ_mem Set.univ Filter.univ_mem
    refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
    obtain ⟨Q, K, K', hQ, -, -, -, hθ'⟩ := hUV θ' hθ' heq
    exact ⟨K, K', Q, hQ, hθ'⟩
  · -- to the equality condition: the lower bound `P ≤ fd + d(d-1)/2 + 2 ∑ H d_h²` from local
    -- identifiability, with the changes of basis inside the heads at pairs of families of
    -- invertible matrices, and the upper bound of Theorem 4.2
    intro h
    have hlow := ae_finrank_le_funDim_add_of_ae_locally_cob_const_orthogonal
      (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) 1
      (fun ℓ => analyticOnNhd_f_attention sees (rmsNorm ε) H dh ℓ) (analyticOnNhd_rmsNorm hε) μ
      headsFam_iffr {n | ∀ ℓ i, IsUnit (n.1 ℓ i) ∧ IsUnit (n.2 ℓ i)}
      (fun θ => contDiffOn_headsFam_iffr θ) (by
        filter_upwards [h] with θ ⟨U, hU, hUV⟩
        refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
        obtain ⟨K, K', Q, hQ, hQθ⟩ := hUV θ' hθ' heq
        refine ⟨(fun ℓ i => (K ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ),
          fun ℓ i => (K' ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)),
          fun ℓ i => ⟨(K ℓ i).isUnit, (K' ℓ i).isUnit⟩, Q, hQ, ?_⟩
        rw [headsFam_coe_iffr]
        exact hQθ)
    have hup := ae_funDim_add_le_residual_attention_rmsNorm ε μ hdIn hdh
    filter_upwards [hlow, hup] with θ h1 h2
    rw [Module.finrank_prod, finrank_headFun_iffr] at h1
    generalize ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2 = s at h1 h2 ⊢
    generalize Fintype.card d * (Fintype.card d - 1) / 2 = a at h1 h2 ⊢
    omega

/-! ### Attention blocks and MLP or gated blocks -/

omit [Fintype T] [DecidableEq d] [Fintype d] [Fintype dIn] [Fintype dOut] in
/-- Helper (the private `sumOfLin_lit` of `Residual/LocalIdentifiabilityTransformer.lean`):
`(a, b) ↦ Params.sumOf a b` is linear. -/
private noncomputable def sumOfLin_iffr {A B : Arch T d L} :
    (Params A dIn dOut × Params B dIn dOut) →ₗ[ℝ] Params (A.sum B) dIn dOut where
  toFun p := Params.sumOf p.1 p.2
  map_add' p q := by
    refine Params.ext' rfl (fun ℓ => ?_) (fun ℓ => ?_) rfl
    · ext k j
      rcases j with j | j <;> rfl
    · ext j k
      rcases j with j | j <;> rfl
  map_smul' c p := by
    refine Params.ext' rfl (fun ℓ => ?_) (fun ℓ => ?_) rfl
    · ext k j
      rcases j with j | j <;> rfl
    · ext j k
      rcases j with j | j <;> rfl

omit [Fintype T] [DecidableEq d] in
/-- Helper: the parameters of the sum, made of two families of class `C¹`, are of class `C¹`
(`Params.sumOf` is linear). -/
private theorem contDiffOn_sumOf_iffr {A B : Arch T d L} {N : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] {fa : N → Params A dIn dOut} {fb : N → Params B dIn dOut} {Ω : Set N}
    (ha : ContDiffOn ℝ 1 fa Ω) (hb : ContDiffOn ℝ 1 fb Ω) :
    ContDiffOn ℝ 1 (fun n => Params.sumOf (fa n) (fb n)) Ω := by
  have h := (LinearMap.toContinuousLinearMap
    (sumOfLin_iffr (A := A) (B := B) (dIn := dIn) (dOut := dOut))).contDiff.comp_contDiffOn
      (ha.prodMk hb)
  exact h

omit [DecidableEq d] in
/-- Helper (the private `ae_rank_QV_lit`, for the first part of a sum): at generic parameters
the query matrix and the value matrix of every head have rank `d_h`, when `d_h ≤ d`. -/
private theorem ae_rank_QV_sum_iffr {B : Arch T d L} {χ : Matrix T d ℝ → Matrix T d ℝ}
    (μ : Measure (Params ((Arch.attention (T := T) (d := d) sees χ H dh).sum B) dIn dOut))
    [μ.IsAddHaarMeasure] (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) :
    ∀ᵐ θ ∂μ, (∀ ℓ (i : H ℓ),
        ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k)).rank
          = Fintype.card (dh ℓ)) ∧
      ∀ ℓ (i : H ℓ),
        ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))).rank
          = Fintype.card (dh ℓ) := by
  classical
  -- finitely many conditions, two for each head of each block; the read of the first part is
  -- made of columns of the read of the sum
  refine (ae_all_iff.2 fun ℓ => ae_all_iff.2 fun i => ?_).and
    (ae_all_iff.2 fun ℓ => ae_all_iff.2 fun i => ?_)
  · exact ae_rank_read_cols_iffr μ ℓ (c := fun k : dh ℓ => Sum.inl (i, Sum.inl k))
      (fun _ _ h => Sum.inl_injective (Prod.mk.inj (Sum.inl_injective h)).2) (hdh ℓ)
  · exact ae_rank_read_cols_iffr μ ℓ (c := fun k : dh ℓ => Sum.inl (i, Sum.inr (Sum.inr k)))
      (fun _ _ h => Sum.inr_injective (Sum.inr_injective (Prod.mk.inj (Sum.inl_injective h)).2))
      (hdh ℓ)

omit [Fintype T] [DecidableEq d] in
/-- Helper (the private `ae_value_ne_zero_lit`, for the second part of a sum): at generic
parameters no value column of the gated part of a read vanishes. -/
private theorem ae_value_ne_zero_sum_iffr [Nonempty d] {A : Arch T d L}
    {χ : Matrix T d ℝ → Matrix T d ℝ}
    (μ : Measure (Params (A.sum (Arch.gated (T := T) (d := d) σ χ hid)) dIn dOut))
    [μ.IsAddHaarMeasure] :
    ∀ᵐ θ ∂μ, ∀ ℓ i, (fun k => θ.sumSnd.read ℓ k (Sum.inr i)) ≠ 0 := by
  -- finitely many conditions, one for each hidden unit `i` of each block `ℓ`
  refine ae_all_iff.2 fun ℓ => ae_all_iff.2 fun i => ?_
  -- an entry `k₀` of the value column
  obtain k₀ : d := Classical.arbitrary d
  -- the entry `θ ↦ θ.read ℓ k₀ (inr (inr i))` is a linear functional of the parameters
  let l : Params (A.sum (Arch.gated (T := T) (d := d) σ χ hid)) dIn dOut →ₗ[ℝ] ℝ :=
    (Matrix.entryLinearMap ℝ ℝ k₀ (Sum.inr (Sum.inr i))).comp
      (Params.linRead (A := A.sum (Arch.gated (T := T) (d := d) σ χ hid)) (dIn := dIn)
        (dOut := dOut) ℓ)
  have hl : ∀ θ, l θ = θ.read ℓ k₀ (Sum.inr (Sum.inr i)) := fun θ => rfl
  -- it is not zero at the parameters whose reads have all entries `1`
  have h₁ : l ⟨0, fun _ => Matrix.of fun _ _ => 1, 0, 0⟩ ≠ 0 := by
    rw [hl]
    exact one_ne_zero
  -- an analytic function that is not identically zero is nonzero almost everywhere
  have hne : ∀ᵐ θ ∂μ, l θ ≠ 0 :=
    ae_ne_zero_of_analytic μ (analyticOnNhd_linear l) ⟨_, h₁⟩
  -- and a function with a nonzero entry is not zero
  filter_upwards [hne] with θ h hz
  exact h (by rw [hl]; exact congrFun hz k₀)

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
  constructor
  · -- from the equality condition: Proposition 4.5 at every `θ` where `E` has rank `d` and the
    -- query and value matrices of every head have rank `d_h`, with no condition on `G`, `K`, `K'`
    intro h
    filter_upwards [h, ae_rank_E_iffr μ hdIn, ae_rank_QV_sum_iffr μ hdh] with θ hfd hE hQV
    obtain ⟨U, hU, hUV⟩ := exists_cob_heads_of_eval_eq_residual_attentionMlp hσ θ hE hQV.1
      hQV.2 hfd Set.univ Filter.univ_mem Set.univ Filter.univ_mem
    refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
    obtain ⟨G, K, K', -, -, -, hθ'⟩ := hUV θ' hθ' heq
    exact ⟨K, K', G, hθ'⟩
  · -- to the equality condition: the lower bound `P ≤ fd + d² + 2 ∑ H d_h²` from local
    -- identifiability, with the changes of basis inside the heads of the attention part at pairs
    -- of families of invertible matrices, and the upper bound of Theorem 4.2
    intro h
    have hlow := ae_finrank_le_funDim_add_of_ae_locally_cob_const
      (Arch.attentionMlp (T := T) (d := d) sees σ id H dh hid) 1
      (fun ℓ => analyticOnNhd_f_sum (analyticOnNhd_f_attention sees id H dh ℓ)
        (analyticOnNhd_f_mlp hσ ℓ)) analyticOnNhd_id μ
      (fun θ n => Params.sumOf (headsFam_iffr θ.sumFst n) θ.sumSnd)
      {n | ∀ ℓ i, IsUnit (n.1 ℓ i) ∧ IsUnit (n.2 ℓ i)}
      (fun θ => contDiffOn_sumOf_iffr (contDiffOn_headsFam_iffr θ.sumFst) contDiffOn_const) (by
        filter_upwards [h] with θ ⟨U, hU, hUV⟩
        refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
        obtain ⟨K, K', G, hG⟩ := hUV θ' hθ' heq
        refine ⟨(fun ℓ i => (K ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ),
          fun ℓ i => (K' ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)),
          fun ℓ i => ⟨(K ℓ i).isUnit, (K' ℓ i).isUnit⟩, G, ?_⟩
        rw [headsFam_coe_iffr]
        exact hG)
    have hup := ae_funDim_add_le_residual_attentionMlp μ hdIn hdh
    filter_upwards [hlow, hup] with θ h1 h2
    rw [Module.finrank_prod, finrank_headFun_iffr] at h1
    generalize ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2 = s at h1 h2 ⊢
    omega

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
  constructor
  · -- from the equality condition: Proposition 4.5 at every `θ` where `E` has rank `d` and the
    -- query and value matrices of every head have rank `d_h`, with no condition on `Q`, `K`, `K'`
    intro h
    filter_upwards [h, ae_rank_E_iffr μ hdIn, ae_rank_QV_sum_iffr μ hdh] with θ hfd hE hQV
    obtain ⟨U, hU, hUV⟩ := exists_cob_heads_of_eval_eq_residual_attentionMlp_rmsNorm hε hσ θ hE
      hQV.1 hQV.2 hfd Set.univ Filter.univ_mem Set.univ Filter.univ_mem
    refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
    obtain ⟨Q, K, K', hQ, -, -, -, hθ'⟩ := hUV θ' hθ' heq
    exact ⟨K, K', Q, hQ, hθ'⟩
  · -- to the equality condition: the lower bound `P ≤ fd + d(d-1)/2 + 2 ∑ H d_h²` from local
    -- identifiability, with the changes of basis inside the heads of the attention part at pairs
    -- of families of invertible matrices, and the upper bound of Theorem 4.2
    intro h
    have hlow := ae_finrank_le_funDim_add_of_ae_locally_cob_const_orthogonal
      (Arch.attentionMlp (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) 1
      (fun ℓ => analyticOnNhd_f_sum (analyticOnNhd_f_attention sees (rmsNorm ε) H dh ℓ)
        (analyticOnNhd_f_mlp hσ ℓ)) (analyticOnNhd_rmsNorm hε) μ
      (fun θ n => Params.sumOf (headsFam_iffr θ.sumFst n) θ.sumSnd)
      {n | ∀ ℓ i, IsUnit (n.1 ℓ i) ∧ IsUnit (n.2 ℓ i)}
      (fun θ => contDiffOn_sumOf_iffr (contDiffOn_headsFam_iffr θ.sumFst) contDiffOn_const) (by
        filter_upwards [h] with θ ⟨U, hU, hUV⟩
        refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
        obtain ⟨K, K', Q, hQ, hQθ⟩ := hUV θ' hθ' heq
        refine ⟨(fun ℓ i => (K ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ),
          fun ℓ i => (K' ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)),
          fun ℓ i => ⟨(K ℓ i).isUnit, (K' ℓ i).isUnit⟩, Q, hQ, ?_⟩
        rw [headsFam_coe_iffr]
        exact hQθ)
    have hup := ae_funDim_add_le_residual_attentionMlp_rmsNorm ε μ hdIn hdh
    filter_upwards [hlow, hup] with θ h1 h2
    rw [Module.finrank_prod, finrank_headFun_iffr] at h1
    generalize ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2 = s at h1 h2 ⊢
    generalize Fintype.card d * (Fintype.card d - 1) / 2 = a at h1 h2 ⊢
    omega

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
  constructor
  · -- from the equality condition: Proposition 4.5 at every `θ` where `E` has rank `d`, the
    -- query and value matrices of every head have rank `d_h` and no value column of a gated unit
    -- vanishes, with no condition on `G`, `K`, `K'`, `c` (the neighbourhoods `Set.univ`)
    intro h
    filter_upwards [h, ae_rank_E_iffr μ hdIn, ae_rank_QV_sum_iffr μ hdh,
      ae_value_ne_zero_sum_iffr μ] with θ hfd hE hQV hv
    obtain ⟨U, hU, hUV⟩ := exists_cob_heads_of_eval_eq_residual_attentionGated hσ θ hE hQV.1
      hQV.2 hv hfd Set.univ Filter.univ_mem Set.univ Filter.univ_mem Set.univ Filter.univ_mem
    refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
    obtain ⟨G, K, K', c, -, -, -, -, hc0, hθ'⟩ := hUV θ' hθ' heq
    exact ⟨K, K', c, fun ℓ i => (hc0 ℓ i).ne', G, hθ'⟩
  · -- to the equality condition: the lower bound `P ≤ fd + d² + 2 ∑ H d_h² + s` from local
    -- identifiability, with the changes of basis inside the heads at pairs of families of
    -- invertible matrices and the rescalings by factors without zero, and the upper bound of
    -- Theorem 4.2
    intro h
    have hlow := ae_finrank_le_funDim_add_of_ae_locally_cob_const
      (Arch.attentionGated (T := T) (d := d) sees σ id H dh hid) 1
      (fun ℓ => analyticOnNhd_f_sum (analyticOnNhd_f_attention sees id H dh ℓ)
        (analyticOnNhd_f_gated hσ ℓ)) analyticOnNhd_id μ
      (N := ((∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ))
        × (∀ ℓ, hid ℓ → ℝ))
      (fun θ n => Params.sumOf (headsFam_iffr θ.sumFst n.1) (θ.sumSnd.rescale n.2))
      {n | (∀ ℓ i, IsUnit (n.1.1 ℓ i) ∧ IsUnit (n.1.2 ℓ i)) ∧ ∀ ℓ i, n.2 ℓ i ≠ 0}
      (fun θ => contDiffOn_sumOf_iffr
        ((contDiffOn_headsFam_iffr θ.sumFst).comp contDiffOn_fst fun _ hn => hn.1)
        ((contDiffOn_rescale_iffr θ.sumSnd).comp contDiffOn_snd fun _ hn => hn.2)) (by
        filter_upwards [h] with θ ⟨U, hU, hUV⟩
        refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
        obtain ⟨K, K', c, hc, G, hG⟩ := hUV θ' hθ' heq
        refine ⟨((fun ℓ i => (K ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ),
          fun ℓ i => (K' ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)), c),
          ⟨fun ℓ i => ⟨(K ℓ i).isUnit, (K' ℓ i).isUnit⟩, hc⟩, G, ?_⟩
        rw [headsFam_coe_iffr]
        exact hG)
    have hup := ae_funDim_add_le_residual_attentionGated μ hdIn hdh
    filter_upwards [hlow, hup] with θ h1 h2
    rw [Module.finrank_prod, Module.finrank_prod, finrank_headFun_iffr, finrank_hidFun_iffr] at h1
    generalize ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2 = s at h1 h2 ⊢
    generalize ∑ ℓ, Fintype.card (hid ℓ) = t at h1 h2 ⊢
    omega

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
  constructor
  · -- from the equality condition: Proposition 4.5 at every `θ` where `E` has rank `d`, the
    -- query and value matrices of every head have rank `d_h` and no value column of a gated unit
    -- vanishes, with no condition on `Q`, `K`, `K'`, `c` (the neighbourhoods `Set.univ`)
    intro h
    filter_upwards [h, ae_rank_E_iffr μ hdIn, ae_rank_QV_sum_iffr μ hdh,
      ae_value_ne_zero_sum_iffr μ] with θ hfd hE hQV hv
    obtain ⟨U, hU, hUV⟩ := exists_cob_heads_of_eval_eq_residual_attentionGated_rmsNorm hε hσ θ
      hE hQV.1 hQV.2 hv hfd Set.univ Filter.univ_mem Set.univ Filter.univ_mem Set.univ
      Filter.univ_mem
    refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
    obtain ⟨Q, K, K', c, hQ, -, -, -, -, hc0, hθ'⟩ := hUV θ' hθ' heq
    exact ⟨K, K', c, fun ℓ i => (hc0 ℓ i).ne', Q, hQ, hθ'⟩
  · -- to the equality condition: the lower bound `P ≤ fd + d(d-1)/2 + 2 ∑ H d_h² + s` from local
    -- identifiability, with the changes of basis inside the heads at pairs of families of
    -- invertible matrices and the rescalings by factors without zero, and the upper bound of
    -- Theorem 4.2
    intro h
    have hlow := ae_finrank_le_funDim_add_of_ae_locally_cob_const_orthogonal
      (Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) 1
      (fun ℓ => analyticOnNhd_f_sum (analyticOnNhd_f_attention sees (rmsNorm ε) H dh ℓ)
        (analyticOnNhd_f_gated hσ ℓ)) (analyticOnNhd_rmsNorm hε) μ
      (N := ((∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ))
        × (∀ ℓ, hid ℓ → ℝ))
      (fun θ n => Params.sumOf (headsFam_iffr θ.sumFst n.1) (θ.sumSnd.rescale n.2))
      {n | (∀ ℓ i, IsUnit (n.1.1 ℓ i) ∧ IsUnit (n.1.2 ℓ i)) ∧ ∀ ℓ i, n.2 ℓ i ≠ 0}
      (fun θ => contDiffOn_sumOf_iffr
        ((contDiffOn_headsFam_iffr θ.sumFst).comp contDiffOn_fst fun _ hn => hn.1)
        ((contDiffOn_rescale_iffr θ.sumSnd).comp contDiffOn_snd fun _ hn => hn.2)) (by
        filter_upwards [h] with θ ⟨U, hU, hUV⟩
        refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
        obtain ⟨K, K', c, hc, Q, hQ, hQθ⟩ := hUV θ' hθ' heq
        refine ⟨((fun ℓ i => (K ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ),
          fun ℓ i => (K' ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)), c),
          ⟨fun ℓ i => ⟨(K ℓ i).isUnit, (K' ℓ i).isUnit⟩, hc⟩, Q, hQ, ?_⟩
        rw [headsFam_coe_iffr]
        exact hQθ)
    have hup := ae_funDim_add_le_residual_attentionGated_rmsNorm ε μ hdIn hdh
    filter_upwards [hlow, hup] with θ h1 h2
    rw [Module.finrank_prod, Module.finrank_prod, finrank_headFun_iffr, finrank_hidFun_iffr] at h1
    generalize ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2 = s at h1 h2 ⊢
    generalize ∑ ℓ, Fintype.card (hid ℓ) = t at h1 h2 ⊢
    generalize Fintype.card d * (Fintype.card d - 1) / 2 = a at h1 h2 ⊢
    omega

end Skips
