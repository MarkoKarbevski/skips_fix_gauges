import SkipsLean.Residual.IdentifiableIff
import SkipsLean.Dimension.IdentifiableConverseFamily

/-!
# The equality condition is local identifiability, with permutations and sign flips: residual
    networks

Paper (skips paper, Proposition 4.5): "A skipless or a residual network satisfies the equality
condition if and only if, at generic parameters, it is locally identifiable up to its symmetries."
(The dimension paper, Proposition 4.6, has skipless networks only.) Definition 4.4 of the skips
paper (4.5 of the dimension paper): "A network is
identifiable up to its symmetries at `θ` if every `θ′` with `F_{θ′} = F_θ` is the image of `θ`
under a symmetry: a change of basis […], a symmetry inside a block, or a composition of these."
The symmetries inside the blocks (dimension paper, Appendix B): "Permutations of hidden units or
heads and sign flips of tanh hidden units are finite and remove no parameters", beside the
continuous ones (rescalings, changes of basis inside the heads). The proof of the converse counts
them: "With the permutations and the sign flips, the symmetries form a Lie group of dimension `k`
with finitely many components".

`Residual/IdentifiableIff.lean` states the equivalence with the continuous symmetries only. Here
the same statements with countably many further images `img j θ` of `θ`, one of which is `θ`
itself: every `θ'` near `θ` with the same function is, for some `j`, the image of `img j θ` under
the continuous symmetries. With `img j` running over the compositions of the permutations of
hidden units or heads and the sign flips of tanh units (finitely many linear maps of the
parameters, which normalize the continuous symmetries inside the blocks and commute with the
changes of basis) the right side is local identifiability up to all the symmetries of the papers.
The statements hold for any countably many maps `img j` of the parameters: they need not be
symmetries, linear or continuous.

The direction from the equality condition to local identifiability is the earlier statement (the
identity is among the `img j`); the other direction is
`Dimension/IdentifiableConverseFamily.lean` with the upper bounds of Theorem 4.3 (dimension
paper) and Theorem 4.2 (skips paper).
-/

namespace Skips

open Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {sees : T → T → Prop} [DecidableRel sees]
variable {H dh hid : Fin L → Type} [∀ ℓ, Fintype (H ℓ)] [∀ ℓ, Fintype (dh ℓ)]
  [∀ ℓ, DecidableEq (dh ℓ)] [∀ ℓ, Fintype (hid ℓ)] {σ : ℝ → ℝ} {ε : ℝ}

/-! ### Helpers copied from `Residual/IdentifiableIff.lean` -/

/-- Helper: the space `Fin 0 → ℝ` of the families of a network without symmetries inside the
blocks has dimension `0`. -/
private theorem finrank_fin_zero_iff2 : Module.finrank ℝ (Fin 0 → ℝ) = 0 :=
  Module.finrank_fin_fun ℝ

/-! ### Helpers: families of parameters of class `C¹` -/

omit [Fintype T] [DecidableEq d] in
/-- Helper: a family of parameters is of class `C¹` on a set if every entry of its four components
is (the parameters are the tuples of their components, by a continuous linear equivalence). -/
private theorem contDiffOn_params_iff2 {A : Arch T d L} {N : Type*} [NormedAddCommGroup N]
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

/-- **Proposition 4.5 of the skips paper, for residual networks of any real-analytic blocks, without
normalization, with countably many further images of `θ`:** `fd = P − d²` at almost every parameter
if and only if at almost every parameter `θ` every `θ'` near `θ` with the same function is, for some
`j`, the image `img j θ` of `θ` after a change of basis by one invertible `G` at all hidden states.
The maps `img j` are any countably many maps of the parameters, one of them the identity; the
permutations of hidden units or heads and the sign flips of tanh units, composed, are finitely many
such maps. -/
theorem ae_funDim_residual_iff_ae_locally_cob_family
    (A : Arch T d L) (hA : A.χ = id)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ)
    (μ : Measure (Params
      A dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    {ι : Type*} [Countable ι]
    (img : ι → Params A dIn dOut →
      Params A dIn dOut)
    (j₀ : ι) (himg : ∀ θ, img j₀ θ = θ) :
    (∀ᵐ θ ∂μ, funDim A 1 θ
        + Fintype.card d ^ 2
      = Module.finrank ℝ (Params
          A dIn dOut)) ↔
    (∀ᵐ θ ∂μ, ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval A 1 θ' x
        = eval A 1 θ x) →
        ∃ j : ι, ∃ G : GL d ℝ,
            θ' = (img j θ).cob
              (fun _ => G) (fun _ => G)) := by
  constructor
  · -- from the equality condition: the statement without further images, with `j = j₀`
    intro h
    have h0 := (ae_funDim_residual_iff_ae_locally_cob
      A hA hf μ hdIn).1 h
    filter_upwards [h0] with θ ⟨U, hU, hUV⟩
    refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
    obtain ⟨G, hθ'⟩ := hUV θ' hθ' heq
    refine ⟨j₀, G, ?_⟩
    rw [himg θ]
    exact hθ'
  · -- to the equality condition: the lower bound from local identifiability, with the constant
    -- families `Ψ θ j n = img j θ` on the zero space, and the upper bound of Theorem 4.2
    intro h
    have hχ : AnalyticOnNhd ℝ A.χ Set.univ := by
      rw [hA]
      exact analyticOnNhd_id
    have hlow := ae_finrank_le_funDim_add_of_ae_locally_cob_const_family A 1 hf hχ μ
      (N := Fin 0 → ℝ) (fun θ j _ => img j θ) (fun _ => Set.univ)
      (fun _ _ => contDiffOn_const) (by
        filter_upwards [h] with θ ⟨U, hU, hUV⟩
        refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
        obtain ⟨j, G, hG⟩ := hUV θ' hθ' heq
        exact ⟨j, 0, Set.mem_univ _, G, hG⟩)
    have hup := ae_funDim_add_le_residual μ hA
      (fun ℓ => differentiableOn_univ.1 (hf ℓ).differentiableOn) hdIn
    filter_upwards [hlow, hup] with θ h1 h2
    rw [finrank_fin_zero_iff2] at h1
    omega

/-- **Proposition 4.5 of the skips paper, for residual networks of any real-analytic blocks, under
pre-RMSNorm with `ε > 0`, with countably many further images of `θ`:** `fd = P − d(d−1)/2` at almost
every parameter if and only if at almost every parameter `θ` every `θ'` near `θ` with the same
function is, for some `j`, the image `img j θ` of `θ` after a change of basis by one orthogonal `Q`
at all hidden states. The maps `img j` are any countably many maps of the parameters, one of them
the identity; the permutations of hidden units or heads and the sign flips of tanh units, composed,
are finitely many such maps. -/
theorem ae_funDim_residual_iff_ae_locally_cob_rmsNorm_family
    (A : Arch T d L) (hε : 0 < ε) (hA : A.χ = rmsNorm ε)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ)
    (μ : Measure (Params
      A dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    {ι : Type*} [Countable ι]
    (img : ι → Params A dIn dOut →
      Params A dIn dOut)
    (j₀ : ι) (himg : ∀ θ, img j₀ θ = θ) :
    (∀ᵐ θ ∂μ, funDim A 1 θ
        + Fintype.card d * (Fintype.card d - 1) / 2
      = Module.finrank ℝ (Params
          A dIn dOut)) ↔
    (∀ᵐ θ ∂μ, ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval A 1 θ' x
        = eval A 1 θ x) →
        ∃ j : ι, ∃ Q : GL d ℝ, (Q : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ ∧
            θ' = (img j θ).cob
              (fun _ => Q) (fun _ => Q)) := by
  constructor
  · -- from the equality condition: the statement without further images, with `j = j₀`
    intro h
    have h0 := (ae_funDim_residual_iff_ae_locally_cob_rmsNorm
      A hε hA hf μ hdIn).1 h
    filter_upwards [h0] with θ ⟨U, hU, hUV⟩
    refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
    obtain ⟨Q, hQ, hθ'⟩ := hUV θ' hθ' heq
    refine ⟨j₀, Q, hQ, ?_⟩
    rw [himg θ]
    exact hθ'
  · -- to the equality condition: the lower bound from local identifiability, with the constant
    -- families `Ψ θ j n = img j θ` on the zero space, and the upper bound of Theorem 4.2
    intro h
    have hχ : AnalyticOnNhd ℝ A.χ Set.univ := by
      rw [hA]
      exact analyticOnNhd_rmsNorm hε
    have hlow := ae_finrank_le_funDim_add_of_ae_locally_cob_const_orthogonal_family A 1 hf hχ μ
      (N := Fin 0 → ℝ) (fun θ j _ => img j θ) (fun _ => Set.univ)
      (fun _ _ => contDiffOn_const) (by
        filter_upwards [h] with θ ⟨U, hU, hUV⟩
        refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
        obtain ⟨j, Q, hQ, hQθ⟩ := hUV θ' hθ' heq
        exact ⟨j, 0, Set.mem_univ _, Q, hQ, hQθ⟩)
    have hup := ae_funDim_add_le_residual_rmsNorm μ hε hA
      (fun ℓ => differentiableOn_univ.1 (hf ℓ).differentiableOn) hdIn
    filter_upwards [hlow, hup] with θ h1 h2
    rw [finrank_fin_zero_iff2] at h1
    generalize Fintype.card d * (Fintype.card d - 1) / 2 = a at h1 h2 ⊢
    omega

/-- **Proposition 4.5 of the skips paper, for residual networks of MLP blocks with a real-analytic
activation (tanh, GELU), without normalization, with countably many further images of `θ`:** `fd = P
− d²` at almost every parameter if and only if at almost every parameter `θ` every `θ'` near `θ`
with the same function is, for some `j`, the image `img j θ` of `θ` after a change of basis by one
invertible `G` at all hidden states. The maps `img j` are any countably many maps of the parameters,
one of them the identity; the permutations of hidden units or heads and the sign flips of tanh
units, composed, are finitely many such maps. -/
theorem ae_funDim_mlp_residual_iff_ae_locally_cob_family
    (hσ : AnalyticOnNhd ℝ σ Set.univ)
    (μ : Measure (Params
      (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    {ι : Type*} [Countable ι]
    (img : ι → Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut →
      Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)
    (j₀ : ι) (himg : ∀ θ, img j₀ θ = θ) :
    (∀ᵐ θ ∂μ, funDim (Arch.mlp σ id hid) 1 θ
        + Fintype.card d ^ 2
      = Module.finrank ℝ (Params
          (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)) ↔
    (∀ᵐ θ ∂μ, ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.mlp σ id hid) 1 θ' x
        = eval (Arch.mlp σ id hid) 1 θ x) →
        ∃ j : ι, ∃ G : GL d ℝ,
            θ' = (img j θ).cob
              (fun _ => G) (fun _ => G)) := by
  -- the MLP blocks are real-analytic
  exact ae_funDim_residual_iff_ae_locally_cob_family _ rfl (fun ℓ => analyticOnNhd_f_mlp hσ ℓ) μ
    hdIn img j₀ himg

/-- **Proposition 4.5 of the skips paper, for residual networks of MLP blocks with a real-analytic
activation (tanh, GELU), under pre-RMSNorm with `ε > 0`, with countably many further images of
`θ`:** `fd = P − d(d−1)/2` at almost every parameter if and only if at almost every parameter `θ`
every `θ'` near `θ` with the same function is, for some `j`, the image `img j θ` of `θ` after a
change of basis by one orthogonal `Q` at all hidden states. The maps `img j` are any countably many
maps of the parameters, one of them the identity; the permutations of hidden units or heads and the
sign flips of tanh units, composed, are finitely many such maps. -/
theorem ae_funDim_mlp_residual_iff_ae_locally_cob_rmsNorm_family
    (hε : 0 < ε) (hσ : AnalyticOnNhd ℝ σ Set.univ)
    (μ : Measure (Params
      (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    {ι : Type*} [Countable ι]
    (img : ι → Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut →
      Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)
    (j₀ : ι) (himg : ∀ θ, img j₀ θ = θ) :
    (∀ᵐ θ ∂μ, funDim (Arch.mlp σ (rmsNorm ε) hid) 1 θ
        + Fintype.card d * (Fintype.card d - 1) / 2
      = Module.finrank ℝ (Params
          (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)) ↔
    (∀ᵐ θ ∂μ, ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.mlp σ (rmsNorm ε) hid) 1 θ' x
        = eval (Arch.mlp σ (rmsNorm ε) hid) 1 θ x) →
        ∃ j : ι, ∃ Q : GL d ℝ, (Q : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ ∧
            θ' = (img j θ).cob
              (fun _ => Q) (fun _ => Q)) := by
  -- the MLP blocks are real-analytic
  exact ae_funDim_residual_iff_ae_locally_cob_rmsNorm_family _ hε rfl
    (fun ℓ => analyticOnNhd_f_mlp hσ ℓ) μ hdIn img j₀ himg

/-- Helper: the space of the factors of the rescalings has dimension `s = ∑ d_hidden`. -/
private theorem finrank_hidFun_iff2 :
    Module.finrank ℝ (∀ ℓ, hid ℓ → ℝ) = ∑ ℓ, Fintype.card (hid ℓ) := by
  rw [Module.finrank_pi_fintype]
  simp only [Module.finrank_fintype_fun_eq_card]

omit [Fintype T] [DecidableEq d] in
/-- Helper: the rescalings `c ↦ θ.rescale c` are of class `C¹` where no factor vanishes (the
values are divided by the factors, the outputs multiplied by them). -/
private theorem contDiffOn_rescale_iff2 {χ : Matrix T d ℝ → Matrix T d ℝ}
    (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut) :
    ContDiffOn ℝ 1 (fun c => θ.rescale c) {c : ∀ ℓ, hid ℓ → ℝ | ∀ ℓ i, c ℓ i ≠ 0} := by
  refine contDiffOn_params_iff2 (fun i j => contDiffOn_const (c := θ.E i j)) (fun ℓ k j => ?_)
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
gate (SwiGLU, GeGLU), without normalization, with countably many further images of `θ`:** `fd = P −
d² − s` at almost every parameter (`s = ∑ d_hidden`) if and only if at almost every parameter `θ`
every `θ'` near `θ` with the same function is, for some `j`, the image `img j θ` of `θ` after a
rescaling of the values of the hidden units by nonzero factors `c` and a change of basis by one
invertible `G` at all hidden states. The maps `img j` are any countably many maps of the parameters,
one of them the identity; the permutations of hidden units or heads and the sign flips of tanh
units, composed, are finitely many such maps. -/
theorem ae_funDim_gated_residual_iff_ae_locally_cob_rescale_family
    [Nonempty d] (hσ : AnalyticOnNhd ℝ σ Set.univ)
    (μ : Measure (Params
      (Arch.gated (T := T) (d := d) σ id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    {ι : Type*} [Countable ι]
    (img : ι → Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut →
      Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (j₀ : ι) (himg : ∀ θ, img j₀ θ = θ) :
    (∀ᵐ θ ∂μ, funDim (Arch.gated σ id hid) 1 θ
        + (Fintype.card d ^ 2
          + ∑ ℓ, Fintype.card (hid ℓ))
      = Module.finrank ℝ (Params
          (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)) ↔
    (∀ᵐ θ ∂μ, ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.gated σ id hid) 1 θ' x
        = eval (Arch.gated σ id hid) 1 θ x) →
        ∃ j : ι, ∃ c : ∀ ℓ, hid ℓ → ℝ, (∀ ℓ i, c ℓ i ≠ 0) ∧
          ∃ G : GL d ℝ,
            θ' = ((img j θ).rescale c).cob
              (fun _ => G) (fun _ => G)) := by
  constructor
  · -- from the equality condition: the statement without further images, with `j = j₀`
    intro h
    have h0 := (ae_funDim_gated_residual_iff_ae_locally_cob_rescale
      hσ μ hdIn).1 h
    filter_upwards [h0] with θ ⟨U, hU, hUV⟩
    refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
    obtain ⟨c, hc, G, hθ'⟩ := hUV θ' hθ' heq
    refine ⟨j₀, c, hc, G, ?_⟩
    rw [himg θ]
    exact hθ'
  · -- to the equality condition: the lower bound from local identifiability, with the family
    -- of the rescalings `Ψ θ j c = (img j θ).rescale c`, on the factors without zero,
    -- at each image `img j θ`,
    -- and the upper bound of Theorem 4.2
    intro h
    have hlow := ae_finrank_le_funDim_add_of_ae_locally_cob_const_family
      (Arch.gated (T := T) (d := d) σ id hid) 1
      (fun ℓ => analyticOnNhd_f_gated hσ ℓ) analyticOnNhd_id μ
      (fun θ j c => (img j θ).rescale c)
      (fun _ => {c | ∀ ℓ i, c ℓ i ≠ 0})
      (fun θ j => contDiffOn_rescale_iff2 (img j θ)) (by
        filter_upwards [h] with θ ⟨U, hU, hUV⟩
        refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
        obtain ⟨j, c, hc, G, hθ'⟩ := hUV θ' hθ' heq
        refine ⟨j, c, hc, G, ?_⟩
        exact hθ')
    have hup := ae_funDim_add_le_residual_gated μ hdIn
    filter_upwards [hlow, hup] with θ h1 h2
    rw [finrank_hidFun_iff2] at h1
    generalize ∑ ℓ, Fintype.card (hid ℓ) = t at h1 h2 ⊢
    omega

/-- **Proposition 4.5 of the skips paper, for residual networks of gated blocks with a real-analytic
gate (SwiGLU, GeGLU), under pre-RMSNorm with `ε > 0`, with countably many further images of `θ`:**
`fd = P − d(d−1)/2 − s` at almost every parameter (`s = ∑ d_hidden`) if and only if at almost every
parameter `θ` every `θ'` near `θ` with the same function is, for some `j`, the image `img j θ` of
`θ` after a rescaling of the values of the hidden units by nonzero factors `c` and a change of basis
by one orthogonal `Q` at all hidden states. The maps `img j` are any countably many maps of the
parameters, one of them the identity; the permutations of hidden units or heads and the sign flips
of tanh units, composed, are finitely many such maps. -/
theorem ae_funDim_gated_residual_iff_ae_locally_cob_rescale_rmsNorm_family
    (hε : 0 < ε) [Nonempty d] (hσ : AnalyticOnNhd ℝ σ Set.univ)
    (μ : Measure (Params
      (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    {ι : Type*} [Countable ι]
    (img : ι → Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut →
      Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)
    (j₀ : ι) (himg : ∀ θ, img j₀ θ = θ) :
    (∀ᵐ θ ∂μ, funDim (Arch.gated σ (rmsNorm ε) hid) 1 θ
        + (Fintype.card d * (Fintype.card d - 1) / 2
          + ∑ ℓ, Fintype.card (hid ℓ))
      = Module.finrank ℝ (Params
          (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)) ↔
    (∀ᵐ θ ∂μ, ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.gated σ (rmsNorm ε) hid) 1 θ' x
        = eval (Arch.gated σ (rmsNorm ε) hid) 1 θ x) →
        ∃ j : ι, ∃ c : ∀ ℓ, hid ℓ → ℝ, (∀ ℓ i, c ℓ i ≠ 0) ∧
          ∃ Q : GL d ℝ, (Q : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ ∧
            θ' = ((img j θ).rescale c).cob
              (fun _ => Q) (fun _ => Q)) := by
  constructor
  · -- from the equality condition: the statement without further images, with `j = j₀`
    intro h
    have h0 := (ae_funDim_gated_residual_iff_ae_locally_cob_rescale_rmsNorm
      hε hσ μ hdIn).1 h
    filter_upwards [h0] with θ ⟨U, hU, hUV⟩
    refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
    obtain ⟨c, hc, Q, hQ, hθ'⟩ := hUV θ' hθ' heq
    refine ⟨j₀, c, hc, Q, hQ, ?_⟩
    rw [himg θ]
    exact hθ'
  · -- to the equality condition: the lower bound from local identifiability, with the family
    -- of the rescalings `Ψ θ j c = (img j θ).rescale c`, on the factors without zero,
    -- at each image `img j θ`,
    -- and the upper bound of Theorem 4.2
    intro h
    have hlow := ae_finrank_le_funDim_add_of_ae_locally_cob_const_orthogonal_family
      (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) 1
      (fun ℓ => analyticOnNhd_f_gated hσ ℓ) (analyticOnNhd_rmsNorm hε) μ
      (fun θ j c => (img j θ).rescale c)
      (fun _ => {c | ∀ ℓ i, c ℓ i ≠ 0})
      (fun θ j => contDiffOn_rescale_iff2 (img j θ)) (by
        filter_upwards [h] with θ ⟨U, hU, hUV⟩
        refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
        obtain ⟨j, c, hc, Q, hQ, hθ'⟩ := hUV θ' hθ' heq
        refine ⟨j, c, hc, Q, hQ, ?_⟩
        exact hθ')
    have hup := ae_funDim_add_le_residual_gated_rmsNorm ε μ hdIn
    filter_upwards [hlow, hup] with θ h1 h2
    rw [finrank_hidFun_iff2] at h1
    generalize ∑ ℓ, Fintype.card (hid ℓ) = t at h1 h2 ⊢
    generalize Fintype.card d * (Fintype.card d - 1) / 2 = a at h1 h2 ⊢
    omega

/-- Helper: the determinant of a matrix whose entries are `C¹` is `C¹` (a polynomial in the
entries). -/
private theorem contDiff_det_iff2 {m X : Type*} [Fintype m] [DecidableEq m] [NormedAddCommGroup X]
    [NormedSpace ℝ X] {g : X → Matrix m m ℝ} (hg : ∀ a b, ContDiff ℝ 1 fun x => g x a b) :
    ContDiff ℝ 1 fun x => (g x).det := by
  simp only [Matrix.det_apply']
  exact ContDiff.sum fun τ _ => contDiff_const.mul (contDiff_prod fun i _ => hg (τ i) i)

/-- Helper: the entries of the inverse of a matrix whose entries are `C¹` are `C¹` where the
matrix is invertible: `A⁻¹ = det(A)⁻¹ adj(A)`, and the entries of the adjugate are
determinants. -/
private theorem contDiffOn_inv_entry_iff2 {m X : Type*} [Fintype m] [DecidableEq m]
    [NormedAddCommGroup X] [NormedSpace ℝ X] {g : X → Matrix m m ℝ}
    (hg : ∀ a b, ContDiff ℝ 1 fun x => g x a b) {s : Set X} (hs : ∀ x ∈ s, IsUnit (g x))
    (a b : m) : ContDiffOn ℝ 1 (fun x => (g x)⁻¹ a b) s := by
  have h1 : (fun x => (g x)⁻¹ a b)
      = fun x => ((g x).det)⁻¹ * ((g x).updateRow b (Pi.single a 1)).det := by
    funext x
    rw [Matrix.inv_def, Matrix.smul_apply, Matrix.adjugate_apply, Ring.inverse_eq_inv, smul_eq_mul]
  rw [h1]
  have hdet : ContDiff ℝ 1 fun x => (g x).det := contDiff_det_iff2 hg
  -- the matrix of the adjugate entry: row `b` replaced by the unit row `a`
  have hadj : ContDiff ℝ 1 fun x => ((g x).updateRow b (Pi.single a 1)).det := by
    refine contDiff_det_iff2 fun i j => ?_
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
private noncomputable def headsMat_iff2 {χ : Matrix T d ℝ → Matrix T d ℝ}
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
private noncomputable def headsFam_iff2 {χ : Matrix T d ℝ → Matrix T d ℝ}
    (θ : Params (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut)
    (n : (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)) :
    Params (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut :=
  headsMat_iff2 θ n.1 (fun ℓ i => (n.1 ℓ i)⁻¹) n.2 (fun ℓ i => (n.2 ℓ i)⁻¹)

omit [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: at the invertible matrices of `K`, `K'`, the family is `(θ.headsQK K).headsVO K'`. -/
private theorem headsFam_coe_iff2 {χ : Matrix T d ℝ → Matrix T d ℝ}
    (θ : Params (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut)
    (K K' : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ) :
    headsFam_iff2 θ (fun ℓ i => (K ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ),
      fun ℓ i => (K' ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)) = (θ.headsQK K).headsVO K' := by
  -- the matrix inverse of `K` is the matrix of `K⁻¹`
  simp only [headsFam_iff2, ← Matrix.coe_units_inv]
  refine Params.ext' rfl (fun ℓ => ?_) (fun ℓ => rfl) rfl
  ext a p
  rcases p with ⟨i, k | k | k⟩ <;> rfl

omit [DecidableEq d] in
/-- Helper: the family of the changes of basis inside the heads is `C¹` where the matrices are
invertible. -/
private theorem contDiffOn_headsFam_iff2 {χ : Matrix T d ℝ → Matrix T d ℝ}
    (θ : Params (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut) :
    ContDiffOn ℝ 1 (headsFam_iff2 θ)
      {n | ∀ ℓ i, IsUnit (n.1 ℓ i) ∧ IsUnit (n.2 ℓ i)} := by
  refine contDiffOn_params_iff2 (fun i j => contDiffOn_const (c := θ.E i j)) (fun ℓ a p => ?_)
    (fun ℓ p b => ?_) (fun k j => contDiffOn_const (c := θ.D k j))
  · rcases p with ⟨i, k | k | k⟩
    · -- the query columns `W_Q k`
      have hk : ∀ k', ContDiff ℝ 1 fun n : (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)
          × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) => n.1 ℓ i k' k := fun k' => by fun_prop
      exact (ContDiff.sum fun k' _ => contDiff_const.mul (hk k')).contDiffOn
    · -- the key columns `W_K (k⁻¹)ᵀ`
      exact ContDiffOn.sum fun k' _ => contDiffOn_const.mul
        (contDiffOn_inv_entry_iff2 (g := fun n : (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)
          × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) => n.1 ℓ i) (fun _ _ => by fun_prop)
          (fun n (hn : ∀ ℓ i, IsUnit (n.1 ℓ i) ∧ IsUnit (n.2 ℓ i)) => (hn ℓ i).1) k k')
    · -- the value columns `W_V k'`
      have hk : ∀ k', ContDiff ℝ 1 fun n : (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)
          × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) => n.2 ℓ i k' k := fun k' => by fun_prop
      exact (ContDiff.sum fun k' _ => contDiff_const.mul (hk k')).contDiffOn
  · -- the output rows `k'⁻¹ W_O`
    rcases p with ⟨i, k⟩
    exact ContDiffOn.sum fun k' _ => ContDiffOn.mul
      (contDiffOn_inv_entry_iff2 (g := fun n : (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)
        × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) => n.2 ℓ i) (fun _ _ => by fun_prop)
        (fun n (hn : ∀ ℓ i, IsUnit (n.1 ℓ i) ∧ IsUnit (n.2 ℓ i)) => (hn ℓ i).2) k k')
      contDiffOn_const

omit [∀ ℓ, DecidableEq (dh ℓ)] in
/-- Helper (the private `finrank_headFun_lia`): the families of matrices of the heads form a
space of dimension `∑_ℓ H_ℓ d_{h,ℓ}²`. -/
private theorem finrank_headFun_iff2 :
    Module.finrank ℝ (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)
      = ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2 := by
  rw [Module.finrank_pi_fintype]
  simp only [Module.finrank_pi_fintype, Module.finrank_matrix, Module.finrank_self, mul_one,
    Finset.sum_const, Finset.card_univ, smul_eq_mul, sq]

/-- **Proposition 4.5 of the skips paper, for residual networks of attention blocks, without
normalization, with countably many further images of `θ`:** `fd = P − d² − s` at almost every
parameter (`s = 2 ∑ H d_h²`) if and only if at almost every parameter `θ` every `θ'` near `θ` with
the same function is, for some `j`, the image `img j θ` of `θ` after changes of basis inside the
heads and a change of basis by one invertible `G` at all hidden states. The maps `img j` are any
countably many maps of the parameters, one of them the identity; the permutations of hidden units or
heads and the sign flips of tanh units, composed, are finitely many such maps. -/
theorem ae_funDim_attention_residual_iff_ae_locally_cob_heads_family
    (μ : Measure (Params
      (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d)
    {ι : Type*} [Countable ι]
    (img : ι → Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut →
      Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut)
    (j₀ : ι) (himg : ∀ θ, img j₀ θ = θ) :
    (∀ᵐ θ ∂μ, funDim (Arch.attention sees id H dh) 1 θ
        + (Fintype.card d ^ 2
          + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
      = Module.finrank ℝ (Params
          (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut)) ↔
    (∀ᵐ θ ∂μ, ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.attention sees id H dh) 1 θ' x
        = eval (Arch.attention sees id H dh) 1 θ x) →
        ∃ j : ι, ∃ K K' : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ,
          ∃ G : GL d ℝ,
            θ' = (((img j θ).headsQK K).headsVO K').cob
              (fun _ => G) (fun _ => G)) := by
  constructor
  · -- from the equality condition: the statement without further images, with `j = j₀`
    intro h
    have h0 := (ae_funDim_attention_residual_iff_ae_locally_cob_heads
      μ hdIn hdh).1 h
    filter_upwards [h0] with θ ⟨U, hU, hUV⟩
    refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
    obtain ⟨K, K', G, hθ'⟩ := hUV θ' hθ' heq
    refine ⟨j₀, K, K', G, ?_⟩
    rw [himg θ]
    exact hθ'
  · -- to the equality condition: the lower bound from local identifiability, with the family
    -- of the changes of basis inside the heads at each image `img j θ`,
    -- and the upper bound of Theorem 4.2
    intro h
    have hlow := ae_finrank_le_funDim_add_of_ae_locally_cob_const_family
      (Arch.attention (T := T) (d := d) sees id H dh) 1
      (fun ℓ => analyticOnNhd_f_attention sees id H dh ℓ) analyticOnNhd_id μ
      (fun θ j n => headsFam_iff2 (img j θ) n)
      (fun _ => {n | ∀ ℓ i, IsUnit (n.1 ℓ i) ∧ IsUnit (n.2 ℓ i)})
      (fun θ j => contDiffOn_headsFam_iff2 (img j θ)) (by
        filter_upwards [h] with θ ⟨U, hU, hUV⟩
        refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
        obtain ⟨j, K, K', G, hθ'⟩ := hUV θ' hθ' heq
        refine ⟨j, (fun ℓ i => (K ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ),
          fun ℓ i => (K' ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)),
          fun ℓ i => ⟨(K ℓ i).isUnit, (K' ℓ i).isUnit⟩, G, ?_⟩
        rw [headsFam_coe_iff2]
        exact hθ')
    have hup := ae_funDim_add_le_residual_attention μ hdIn hdh
    filter_upwards [hlow, hup] with θ h1 h2
    rw [Module.finrank_prod, finrank_headFun_iff2] at h1
    generalize ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2 = s at h1 h2 ⊢
    omega

/-- **Proposition 4.5 of the skips paper, for residual networks of attention blocks, under
pre-RMSNorm with `ε > 0`, with countably many further images of `θ`:** `fd = P − d(d−1)/2 − s` at
almost every parameter (`s = 2 ∑ H d_h²`) if and only if at almost every parameter `θ` every `θ'`
near `θ` with the same function is, for some `j`, the image `img j θ` of `θ` after changes of basis
inside the heads and a change of basis by one orthogonal `Q` at all hidden states. The maps `img j`
are any countably many maps of the parameters, one of them the identity; the permutations of hidden
units or heads and the sign flips of tanh units, composed, are finitely many such maps. -/
theorem ae_funDim_attention_residual_iff_ae_locally_cob_heads_rmsNorm_family
    (hε : 0 < ε)
    (μ : Measure (Params
      (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d)
    {ι : Type*} [Countable ι]
    (img : ι → Params (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut →
      Params (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut)
    (j₀ : ι) (himg : ∀ θ, img j₀ θ = θ) :
    (∀ᵐ θ ∂μ, funDim (Arch.attention sees (rmsNorm ε) H dh) 1 θ
        + (Fintype.card d * (Fintype.card d - 1) / 2
          + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
      = Module.finrank ℝ (Params
          (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut)) ↔
    (∀ᵐ θ ∂μ, ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.attention sees (rmsNorm ε) H dh) 1 θ' x
        = eval (Arch.attention sees (rmsNorm ε) H dh) 1 θ x) →
        ∃ j : ι, ∃ K K' : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ,
          ∃ Q : GL d ℝ, (Q : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ ∧
            θ' = (((img j θ).headsQK K).headsVO K').cob
              (fun _ => Q) (fun _ => Q)) := by
  constructor
  · -- from the equality condition: the statement without further images, with `j = j₀`
    intro h
    have h0 := (ae_funDim_attention_residual_iff_ae_locally_cob_heads_rmsNorm
      hε μ hdIn hdh).1 h
    filter_upwards [h0] with θ ⟨U, hU, hUV⟩
    refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
    obtain ⟨K, K', Q, hQ, hθ'⟩ := hUV θ' hθ' heq
    refine ⟨j₀, K, K', Q, hQ, ?_⟩
    rw [himg θ]
    exact hθ'
  · -- to the equality condition: the lower bound from local identifiability, with the family
    -- of the changes of basis inside the heads at each image `img j θ`,
    -- and the upper bound of Theorem 4.2
    intro h
    have hlow := ae_finrank_le_funDim_add_of_ae_locally_cob_const_orthogonal_family
      (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) 1
      (fun ℓ => analyticOnNhd_f_attention sees (rmsNorm ε) H dh ℓ) (analyticOnNhd_rmsNorm hε) μ
      (fun θ j n => headsFam_iff2 (img j θ) n)
      (fun _ => {n | ∀ ℓ i, IsUnit (n.1 ℓ i) ∧ IsUnit (n.2 ℓ i)})
      (fun θ j => contDiffOn_headsFam_iff2 (img j θ)) (by
        filter_upwards [h] with θ ⟨U, hU, hUV⟩
        refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
        obtain ⟨j, K, K', Q, hQ, hθ'⟩ := hUV θ' hθ' heq
        refine ⟨j, (fun ℓ i => (K ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ),
          fun ℓ i => (K' ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)),
          fun ℓ i => ⟨(K ℓ i).isUnit, (K' ℓ i).isUnit⟩, Q, hQ, ?_⟩
        rw [headsFam_coe_iff2]
        exact hθ')
    have hup := ae_funDim_add_le_residual_attention_rmsNorm ε μ hdIn hdh
    filter_upwards [hlow, hup] with θ h1 h2
    rw [Module.finrank_prod, finrank_headFun_iff2] at h1
    generalize ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2 = s at h1 h2 ⊢
    generalize Fintype.card d * (Fintype.card d - 1) / 2 = a at h1 h2 ⊢
    omega

omit [Fintype T] [DecidableEq d] [Fintype d] [Fintype dIn] [Fintype dOut] in
/-- Helper (the private `sumOfLin_lit` of `Residual/LocalIdentifiabilityTransformer.lean`):
`(a, b) ↦ Params.sumOf a b` is linear. -/
private noncomputable def sumOfLin_iff2 {A B : Arch T d L} :
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
private theorem contDiffOn_sumOf_iff2 {A B : Arch T d L} {N : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] {fa : N → Params A dIn dOut} {fb : N → Params B dIn dOut} {Ω : Set N}
    (ha : ContDiffOn ℝ 1 fa Ω) (hb : ContDiffOn ℝ 1 fb Ω) :
    ContDiffOn ℝ 1 (fun n => Params.sumOf (fa n) (fb n)) Ω := by
  have h := (LinearMap.toContinuousLinearMap
    (sumOfLin_iff2 (A := A) (B := B) (dIn := dIn) (dOut := dOut))).contDiff.comp_contDiffOn
      (ha.prodMk hb)
  exact h

/-- **Proposition 4.5 of the skips paper, for residual networks of attention blocks and MLP blocks
with a real-analytic activation, in any order, without normalization, with countably many further
images of `θ`:** `fd = P − d² − s` at almost every parameter (`s = 2 ∑ H d_h²`) if and only if at
almost every parameter `θ` every `θ'` near `θ` with the same function is, for some `j`, the image
`img j θ` of `θ` after changes of basis inside the heads and a change of basis by one invertible `G`
at all hidden states. The maps `img j` are any countably many maps of the parameters, one of them
the identity; the permutations of hidden units or heads and the sign flips of tanh units, composed,
are finitely many such maps. -/
theorem ae_funDim_attentionMlp_residual_iff_ae_locally_cob_heads_family
    (hσ : AnalyticOnNhd ℝ σ Set.univ)
    (μ : Measure (Params
      (Arch.attentionMlp (T := T) (d := d) sees σ id H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d)
    {ι : Type*} [Countable ι]
    (img : ι → Params (Arch.attentionMlp (T := T) (d := d) sees σ id H dh hid) dIn dOut →
      Params (Arch.attentionMlp (T := T) (d := d) sees σ id H dh hid) dIn dOut)
    (j₀ : ι) (himg : ∀ θ, img j₀ θ = θ) :
    (∀ᵐ θ ∂μ, funDim (Arch.attentionMlp sees σ id H dh hid) 1 θ
        + (Fintype.card d ^ 2
          + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
      = Module.finrank ℝ (Params
          (Arch.attentionMlp (T := T) (d := d) sees σ id H dh hid) dIn dOut)) ↔
    (∀ᵐ θ ∂μ, ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.attentionMlp sees σ id H dh hid) 1 θ' x
        = eval (Arch.attentionMlp sees σ id H dh hid) 1 θ x) →
        ∃ j : ι, ∃ K K' : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ,
          ∃ G : GL d ℝ,
            θ' = (Params.sumOf (((img j θ).sumFst.headsQK K).headsVO K') (img j θ).sumSnd).cob
              (fun _ => G) (fun _ => G)) := by
  constructor
  · -- from the equality condition: the statement without further images, with `j = j₀`
    intro h
    have h0 := (ae_funDim_attentionMlp_residual_iff_ae_locally_cob_heads
      hσ μ hdIn hdh).1 h
    filter_upwards [h0] with θ ⟨U, hU, hUV⟩
    refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
    obtain ⟨K, K', G, hθ'⟩ := hUV θ' hθ' heq
    refine ⟨j₀, K, K', G, ?_⟩
    rw [himg θ]
    exact hθ'
  · -- to the equality condition: the lower bound from local identifiability, with the family
    -- of the changes of basis inside the heads of the attention part at each image `img j θ`,
    -- and the upper bound of Theorem 4.2
    intro h
    have hlow := ae_finrank_le_funDim_add_of_ae_locally_cob_const_family
      (Arch.attentionMlp (T := T) (d := d) sees σ id H dh hid) 1
      (fun ℓ => analyticOnNhd_f_sum (analyticOnNhd_f_attention sees id H dh ℓ)
        (analyticOnNhd_f_mlp hσ ℓ)) analyticOnNhd_id μ
      (fun θ j n => Params.sumOf (headsFam_iff2 (img j θ).sumFst n) (img j θ).sumSnd)
      (fun _ => {n | ∀ ℓ i, IsUnit (n.1 ℓ i) ∧ IsUnit (n.2 ℓ i)})
      (fun θ j => contDiffOn_sumOf_iff2 (contDiffOn_headsFam_iff2 (img j θ).sumFst)
        contDiffOn_const) (by
        filter_upwards [h] with θ ⟨U, hU, hUV⟩
        refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
        obtain ⟨j, K, K', G, hθ'⟩ := hUV θ' hθ' heq
        refine ⟨j, (fun ℓ i => (K ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ),
          fun ℓ i => (K' ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)),
          fun ℓ i => ⟨(K ℓ i).isUnit, (K' ℓ i).isUnit⟩, G, ?_⟩
        rw [headsFam_coe_iff2]
        exact hθ')
    have hup := ae_funDim_add_le_residual_attentionMlp μ hdIn hdh
    filter_upwards [hlow, hup] with θ h1 h2
    rw [Module.finrank_prod, finrank_headFun_iff2] at h1
    generalize ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2 = s at h1 h2 ⊢
    omega

/-- **Proposition 4.5 of the skips paper, for residual networks of attention blocks and MLP blocks
with a real-analytic activation, in any order, under pre-RMSNorm with `ε > 0`, with countably many
further images of `θ`:** `fd = P − d(d−1)/2 − s` at almost every parameter (`s = 2 ∑ H d_h²`) if and
only if at almost every parameter `θ` every `θ'` near `θ` with the same function is, for some `j`,
the image `img j θ` of `θ` after changes of basis inside the heads and a change of basis by one
orthogonal `Q` at all hidden states. The maps `img j` are any countably many maps of the parameters,
one of them the identity; the permutations of hidden units or heads and the sign flips of tanh
units, composed, are finitely many such maps. -/
theorem ae_funDim_attentionMlp_residual_iff_ae_locally_cob_heads_rmsNorm_family
    (hε : 0 < ε) (hσ : AnalyticOnNhd ℝ σ Set.univ)
    (μ : Measure (Params
      (Arch.attentionMlp (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d)
    {ι : Type*} [Countable ι]
    (img : ι → Params (Arch.attentionMlp (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut →
      Params (Arch.attentionMlp (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut)
    (j₀ : ι) (himg : ∀ θ, img j₀ θ = θ) :
    (∀ᵐ θ ∂μ, funDim (Arch.attentionMlp sees σ (rmsNorm ε) H dh hid) 1 θ
        + (Fintype.card d * (Fintype.card d - 1) / 2
          + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
      = Module.finrank ℝ (Params
          (Arch.attentionMlp (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut)) ↔
    (∀ᵐ θ ∂μ, ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.attentionMlp sees σ (rmsNorm ε) H dh hid) 1 θ' x
        = eval (Arch.attentionMlp sees σ (rmsNorm ε) H dh hid) 1 θ x) →
        ∃ j : ι, ∃ K K' : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ,
          ∃ Q : GL d ℝ, (Q : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ ∧
            θ' = (Params.sumOf (((img j θ).sumFst.headsQK K).headsVO K') (img j θ).sumSnd).cob
              (fun _ => Q) (fun _ => Q)) := by
  constructor
  · -- from the equality condition: the statement without further images, with `j = j₀`
    intro h
    have h0 := (ae_funDim_attentionMlp_residual_iff_ae_locally_cob_heads_rmsNorm
      hε hσ μ hdIn hdh).1 h
    filter_upwards [h0] with θ ⟨U, hU, hUV⟩
    refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
    obtain ⟨K, K', Q, hQ, hθ'⟩ := hUV θ' hθ' heq
    refine ⟨j₀, K, K', Q, hQ, ?_⟩
    rw [himg θ]
    exact hθ'
  · -- to the equality condition: the lower bound from local identifiability, with the family
    -- of the changes of basis inside the heads of the attention part at each image `img j θ`,
    -- and the upper bound of Theorem 4.2
    intro h
    have hlow := ae_finrank_le_funDim_add_of_ae_locally_cob_const_orthogonal_family
      (Arch.attentionMlp (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) 1
      (fun ℓ => analyticOnNhd_f_sum (analyticOnNhd_f_attention sees (rmsNorm ε) H dh ℓ)
        (analyticOnNhd_f_mlp hσ ℓ)) (analyticOnNhd_rmsNorm hε) μ
      (fun θ j n => Params.sumOf (headsFam_iff2 (img j θ).sumFst n) (img j θ).sumSnd)
      (fun _ => {n | ∀ ℓ i, IsUnit (n.1 ℓ i) ∧ IsUnit (n.2 ℓ i)})
      (fun θ j => contDiffOn_sumOf_iff2 (contDiffOn_headsFam_iff2 (img j θ).sumFst)
        contDiffOn_const) (by
        filter_upwards [h] with θ ⟨U, hU, hUV⟩
        refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
        obtain ⟨j, K, K', Q, hQ, hθ'⟩ := hUV θ' hθ' heq
        refine ⟨j, (fun ℓ i => (K ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ),
          fun ℓ i => (K' ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)),
          fun ℓ i => ⟨(K ℓ i).isUnit, (K' ℓ i).isUnit⟩, Q, hQ, ?_⟩
        rw [headsFam_coe_iff2]
        exact hθ')
    have hup := ae_funDim_add_le_residual_attentionMlp_rmsNorm ε μ hdIn hdh
    filter_upwards [hlow, hup] with θ h1 h2
    rw [Module.finrank_prod, finrank_headFun_iff2] at h1
    generalize ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2 = s at h1 h2 ⊢
    generalize Fintype.card d * (Fintype.card d - 1) / 2 = a at h1 h2 ⊢
    omega

/-- **Proposition 4.5 of the skips paper, for residual networks of attention blocks and gated blocks
with a real-analytic gate, in any order, without normalization, with countably many further images
of `θ`:** `fd = P − d² − s` at almost every parameter (`s = 2 ∑ H d_h² + ∑ d_hidden`) if and only if
at almost every parameter `θ` every `θ'` near `θ` with the same function is, for some `j`, the image
`img j θ` of `θ` after changes of basis inside the heads, a rescaling of the values of the hidden
units by nonzero factors `c` and a change of basis by one invertible `G` at all hidden states. The
maps `img j` are any countably many maps of the parameters, one of them the identity; the
permutations of hidden units or heads and the sign flips of tanh units, composed, are finitely many
such maps. -/
theorem ae_funDim_attentionGated_residual_iff_ae_locally_cob_heads_rescale_family
    [Nonempty d] (hσ : AnalyticOnNhd ℝ σ Set.univ)
    (μ : Measure (Params
      (Arch.attentionGated (T := T) (d := d) sees σ id H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d)
    {ι : Type*} [Countable ι]
    (img : ι → Params (Arch.attentionGated (T := T) (d := d) sees σ id H dh hid) dIn dOut →
      Params (Arch.attentionGated (T := T) (d := d) sees σ id H dh hid) dIn dOut)
    (j₀ : ι) (himg : ∀ θ, img j₀ θ = θ) :
    (∀ᵐ θ ∂μ, funDim (Arch.attentionGated sees σ id H dh hid) 1 θ
        + (Fintype.card d ^ 2
          + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
            + ∑ ℓ, Fintype.card (hid ℓ)))
      = Module.finrank ℝ (Params
          (Arch.attentionGated (T := T) (d := d) sees σ id H dh hid) dIn dOut)) ↔
    (∀ᵐ θ ∂μ, ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.attentionGated sees σ id H dh hid) 1 θ' x
        = eval (Arch.attentionGated sees σ id H dh hid) 1 θ x) →
        ∃ j : ι, ∃ (K K' : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ) (c : ∀ ℓ, hid ℓ → ℝ), (∀ ℓ i, c ℓ i ≠ 0) ∧
          ∃ G : GL d ℝ,
            θ' = (Params.sumOf (((img j θ).sumFst.headsQK K).headsVO K') ((img j θ).sumSnd.rescale
                c)).cob
              (fun _ => G) (fun _ => G)) := by
  constructor
  · -- from the equality condition: the statement without further images, with `j = j₀`
    intro h
    have h0 := (ae_funDim_attentionGated_residual_iff_ae_locally_cob_heads_rescale
      hσ μ hdIn hdh).1 h
    filter_upwards [h0] with θ ⟨U, hU, hUV⟩
    refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
    obtain ⟨K, K', c, hc, G, hθ'⟩ := hUV θ' hθ' heq
    refine ⟨j₀, K, K', c, hc, G, ?_⟩
    rw [himg θ]
    exact hθ'
  · -- to the equality condition: the lower bound from local identifiability, with the family
    -- of the changes of basis inside the heads and the rescalings at each image `img j θ`,
    -- and the upper bound of Theorem 4.2
    intro h
    have hlow := ae_finrank_le_funDim_add_of_ae_locally_cob_const_family
      (Arch.attentionGated (T := T) (d := d) sees σ id H dh hid) 1
      (fun ℓ => analyticOnNhd_f_sum (analyticOnNhd_f_attention sees id H dh ℓ)
        (analyticOnNhd_f_gated hσ ℓ)) analyticOnNhd_id μ
      (N := ((∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ))
        × (∀ ℓ, hid ℓ → ℝ))
      (fun θ j n => Params.sumOf (headsFam_iff2 (img j θ).sumFst n.1)
        ((img j θ).sumSnd.rescale n.2))
      (fun _ => {n | (∀ ℓ i, IsUnit (n.1.1 ℓ i) ∧ IsUnit (n.1.2 ℓ i)) ∧ ∀ ℓ i, n.2 ℓ i ≠ 0})
      (fun θ j => contDiffOn_sumOf_iff2
        ((contDiffOn_headsFam_iff2 (img j θ).sumFst).comp contDiffOn_fst fun _ hn => hn.1)
        ((contDiffOn_rescale_iff2 (img j θ).sumSnd).comp contDiffOn_snd fun _ hn => hn.2)) (by
        filter_upwards [h] with θ ⟨U, hU, hUV⟩
        refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
        obtain ⟨j, K, K', c, hc, G, hθ'⟩ := hUV θ' hθ' heq
        refine ⟨j, ((fun ℓ i => (K ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ),
          fun ℓ i => (K' ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)), c),
          ⟨fun ℓ i => ⟨(K ℓ i).isUnit, (K' ℓ i).isUnit⟩, hc⟩, G, ?_⟩
        rw [headsFam_coe_iff2]
        exact hθ')
    have hup := ae_funDim_add_le_residual_attentionGated μ hdIn hdh
    filter_upwards [hlow, hup] with θ h1 h2
    rw [Module.finrank_prod, Module.finrank_prod, finrank_headFun_iff2, finrank_hidFun_iff2] at h1
    generalize ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2 = s at h1 h2 ⊢
    generalize ∑ ℓ, Fintype.card (hid ℓ) = t at h1 h2 ⊢
    omega

/-- **Proposition 4.5 of the skips paper, for residual networks of attention blocks and gated blocks
with a real-analytic gate, in any order, under pre-RMSNorm with `ε > 0`, with countably many further
images of `θ`:** `fd = P − d(d−1)/2 − s` at almost every parameter (`s = 2 ∑ H d_h² + ∑ d_hidden`)
if and only if at almost every parameter `θ` every `θ'` near `θ` with the same function is, for some
`j`, the image `img j θ` of `θ` after changes of basis inside the heads, a rescaling of the values
of the hidden units by nonzero factors `c` and a change of basis by one orthogonal `Q` at all hidden
states. The maps `img j` are any countably many maps of the parameters, one of them the identity;
the permutations of hidden units or heads and the sign flips of tanh units, composed, are finitely
many such maps. -/
theorem ae_funDim_attentionGated_residual_iff_ae_locally_cob_heads_rescale_rmsNorm_family
    (hε : 0 < ε) [Nonempty d] (hσ : AnalyticOnNhd ℝ σ Set.univ)
    (μ : Measure (Params
      (Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d)
    {ι : Type*} [Countable ι]
    (img : ι → Params (Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut →
      Params (Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut)
    (j₀ : ι) (himg : ∀ θ, img j₀ θ = θ) :
    (∀ᵐ θ ∂μ, funDim (Arch.attentionGated sees σ (rmsNorm ε) H dh hid) 1 θ
        + (Fintype.card d * (Fintype.card d - 1) / 2
          + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
            + ∑ ℓ, Fintype.card (hid ℓ)))
      = Module.finrank ℝ (Params
          (Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut)) ↔
    (∀ᵐ θ ∂μ, ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.attentionGated sees σ (rmsNorm ε) H dh hid) 1 θ' x
        = eval (Arch.attentionGated sees σ (rmsNorm ε) H dh hid) 1 θ x) →
        ∃ j : ι, ∃ (K K' : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ) (c : ∀ ℓ, hid ℓ → ℝ), (∀ ℓ i, c ℓ i ≠ 0) ∧
          ∃ Q : GL d ℝ, (Q : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ ∧
            θ' = (Params.sumOf (((img j θ).sumFst.headsQK K).headsVO K') ((img j θ).sumSnd.rescale
                c)).cob
              (fun _ => Q) (fun _ => Q)) := by
  constructor
  · -- from the equality condition: the statement without further images, with `j = j₀`
    intro h
    have h0 := (ae_funDim_attentionGated_residual_iff_ae_locally_cob_heads_rescale_rmsNorm
      hε hσ μ hdIn hdh).1 h
    filter_upwards [h0] with θ ⟨U, hU, hUV⟩
    refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
    obtain ⟨K, K', c, hc, Q, hQ, hθ'⟩ := hUV θ' hθ' heq
    refine ⟨j₀, K, K', c, hc, Q, hQ, ?_⟩
    rw [himg θ]
    exact hθ'
  · -- to the equality condition: the lower bound from local identifiability, with the family
    -- of the changes of basis inside the heads and the rescalings at each image `img j θ`,
    -- and the upper bound of Theorem 4.2
    intro h
    have hlow := ae_finrank_le_funDim_add_of_ae_locally_cob_const_orthogonal_family
      (Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) 1
      (fun ℓ => analyticOnNhd_f_sum (analyticOnNhd_f_attention sees (rmsNorm ε) H dh ℓ)
        (analyticOnNhd_f_gated hσ ℓ)) (analyticOnNhd_rmsNorm hε) μ
      (N := ((∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ))
        × (∀ ℓ, hid ℓ → ℝ))
      (fun θ j n => Params.sumOf (headsFam_iff2 (img j θ).sumFst n.1)
        ((img j θ).sumSnd.rescale n.2))
      (fun _ => {n | (∀ ℓ i, IsUnit (n.1.1 ℓ i) ∧ IsUnit (n.1.2 ℓ i)) ∧ ∀ ℓ i, n.2 ℓ i ≠ 0})
      (fun θ j => contDiffOn_sumOf_iff2
        ((contDiffOn_headsFam_iff2 (img j θ).sumFst).comp contDiffOn_fst fun _ hn => hn.1)
        ((contDiffOn_rescale_iff2 (img j θ).sumSnd).comp contDiffOn_snd fun _ hn => hn.2)) (by
        filter_upwards [h] with θ ⟨U, hU, hUV⟩
        refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
        obtain ⟨j, K, K', c, hc, Q, hQ, hθ'⟩ := hUV θ' hθ' heq
        refine ⟨j, ((fun ℓ i => (K ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ),
          fun ℓ i => (K' ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)), c),
          ⟨fun ℓ i => ⟨(K ℓ i).isUnit, (K' ℓ i).isUnit⟩, hc⟩, Q, hQ, ?_⟩
        rw [headsFam_coe_iff2]
        exact hθ')
    have hup := ae_funDim_add_le_residual_attentionGated_rmsNorm ε μ hdIn hdh
    filter_upwards [hlow, hup] with θ h1 h2
    rw [Module.finrank_prod, Module.finrank_prod, finrank_headFun_iff2, finrank_hidFun_iff2] at h1
    generalize ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2 = s at h1 h2 ⊢
    generalize ∑ ℓ, Fintype.card (hid ℓ) = t at h1 h2 ⊢
    generalize Fintype.card d * (Fintype.card d - 1) / 2 = a at h1 h2 ⊢
    omega

end Skips
