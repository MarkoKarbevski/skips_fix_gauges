import SkipsLean.Dimension.IdentifiableIff
import SkipsLean.Dimension.IdentifiableConverseFamily

/-!
# The equality condition is local identifiability, with permutations and sign flips: networks
    without skip connections

Paper (dimension paper, Proposition 4.6; skips paper, Proposition 4.5): "A network satisfies the
equality condition if and only if, at generic parameters, it is locally identifiable up to its
symmetries." Definition 4.5 of the dimension paper (4.4 of the skips paper): "A network is
identifiable up to its symmetries at `θ` if every `θ′` with `F_{θ′} = F_θ` is the image of `θ`
under a symmetry: a change of basis […], a symmetry inside a block, or a composition of these."
The symmetries inside the blocks (dimension paper, Appendix B): "Permutations of hidden units or
heads and sign flips of tanh hidden units are finite and remove no parameters", beside the
continuous ones (rescalings, changes of basis inside the heads). The proof of the converse counts
them: "With the permutations and the sign flips, the symmetries form a Lie group of dimension `k`
with finitely many components".

`Dimension/IdentifiableIff.lean` states the equivalence with the continuous symmetries only. Here
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

/-- **Proposition 4.6 of the dimension paper and Proposition 4.5 of the skips paper, for skipless
networks of any real-analytic blocks, without normalization, with countably many further images of
`θ`:** `fd = P − (L + 1) d²` at almost every parameter if and only if at almost every parameter `θ`
every `θ'` near `θ` with the same function is, for some `j`, the image `img j θ` of `θ` after a
change of basis by invertible `G_0, …, G_L`. The maps `img j` are any countably many maps of the
parameters, one of them the identity; the permutations of hidden units or heads and the sign flips
of tanh units, composed, are finitely many such maps. -/
theorem ae_funDim_skipless_iff_ae_locally_cob_family
    (A : Arch T d L) (hA : A.χ = id)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ)
    (μ : Measure (Params
      A dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hw : ∀ ℓ, Fintype.card d ≤ Fintype.card (A.w ℓ))
    {ι : Type*} [Countable ι]
    (img : ι → Params A dIn dOut →
      Params A dIn dOut)
    (j₀ : ι) (himg : ∀ θ, img j₀ θ = θ) :
    (∀ᵐ θ ∂μ, funDim A 0 θ
        + (L + 1) * Fintype.card d ^ 2
      = Module.finrank ℝ (Params
          A dIn dOut)) ↔
    (∀ᵐ θ ∂μ, ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval A 0 θ' x
        = eval A 0 θ x) →
        ∃ j : ι, ∃ G : Fin (L + 1) → GL d ℝ,
            θ' = (img j θ).cob G G) := by
  constructor
  · -- the equality condition gives local identifiability up to the changes of basis
    -- (the statement without further images), and the identity `img j₀` is among the images
    intro h
    filter_upwards [(ae_funDim_skipless_iff_ae_locally_cob A hA hf μ hdIn hw).1 h]
      with θ ⟨U, hU, hUV⟩
    refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
    obtain ⟨G, hG⟩ := hUV θ' hθ' heq
    exact ⟨j₀, G, by rw [himg]; exact hG⟩
  · -- local identifiability gives the lower bound `P ≤ fd + (L + 1) d²`, with no symmetry inside
    -- the blocks (`N` of dimension `0`, `Ψ θ j n = img j θ`)
    intro h
    have hχ : AnalyticOnNhd ℝ A.χ Set.univ := by
      rw [hA]
      exact analyticOnNhd_id
    have hlow := ae_finrank_le_funDim_add_of_ae_locally_cob_family A 0 hf hχ μ
      (N := Fin 0 → ℝ) (fun θ j _ => img j θ) (fun _ => Set.univ)
      (fun _ _ => contDiffOn_const) (by
        filter_upwards [h] with θ ⟨U, hU, hUV⟩
        refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
        obtain ⟨j, G, hG⟩ := hUV θ' hθ' heq
        exact ⟨j, 0, Set.mem_univ _, G, hG⟩)
    -- and the upper bound of Theorem 4.3
    have hup := ae_funDim_add_le_skipless μ hA
      (fun ℓ => differentiableOn_univ.1 (hf ℓ).differentiableOn) hdIn hw
    filter_upwards [hlow, hup] with θ h1 h2
    rw [Module.finrank_fin_fun] at h1
    omega

/-- **Proposition 4.6 of the dimension paper and Proposition 4.5 of the skips paper, for skipless
networks of any real-analytic blocks, under pre-RMSNorm with `ε > 0`, with countably many further
images of `θ`:** `fd = P − (L + 1) d(d−1)/2` at almost every parameter if and only if at almost
every parameter `θ` every `θ'` near `θ` with the same function is, for some `j`, the image `img j θ`
of `θ` after a change of basis by orthogonal `Q_0, …, Q_L`. The maps `img j` are any countably many
maps of the parameters, one of them the identity; the permutations of hidden units or heads and the
sign flips of tanh units, composed, are finitely many such maps. -/
theorem ae_funDim_skipless_iff_ae_locally_cob_rmsNorm_family
    (A : Arch T d L) (hε : 0 < ε) (hA : A.χ = rmsNorm ε)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ)
    (μ : Measure (Params
      A dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hw : ∀ ℓ, Fintype.card d ≤ Fintype.card (A.w ℓ))
    {ι : Type*} [Countable ι]
    (img : ι → Params A dIn dOut →
      Params A dIn dOut)
    (j₀ : ι) (himg : ∀ θ, img j₀ θ = θ) :
    (∀ᵐ θ ∂μ, funDim A 0 θ
        + (L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2)
      = Module.finrank ℝ (Params
          A dIn dOut)) ↔
    (∀ᵐ θ ∂μ, ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval A 0 θ' x
        = eval A 0 θ x) →
        ∃ j : ι, ∃ Q : Fin (L + 1) → GL d ℝ,
            (∀ ℓ, (Q ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ) ∧
            θ' = (img j θ).cob Q Q) := by
  constructor
  · -- the equality condition gives local identifiability up to the orthogonal changes of basis
    -- (the statement without further images), and the identity `img j₀` is among the images
    intro h
    filter_upwards [(ae_funDim_skipless_iff_ae_locally_cob_rmsNorm A hε hA hf μ hdIn hw).1 h]
      with θ ⟨U, hU, hUV⟩
    refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
    obtain ⟨Q, hQ, hQθ⟩ := hUV θ' hθ' heq
    exact ⟨j₀, Q, hQ, by rw [himg]; exact hQθ⟩
  · -- local identifiability gives the lower bound `P ≤ fd + (L + 1) d(d−1)/2`, with no symmetry
    -- inside the blocks (`N` of dimension `0`, `Ψ θ j n = img j θ`)
    intro h
    have hχ : AnalyticOnNhd ℝ A.χ Set.univ := by
      rw [hA]
      exact analyticOnNhd_rmsNorm hε
    have hlow := ae_finrank_le_funDim_add_of_ae_locally_cob_orthogonal_family A 0 hf hχ μ
      (N := Fin 0 → ℝ) (fun θ j _ => img j θ) (fun _ => Set.univ)
      (fun _ _ => contDiffOn_const) (by
        filter_upwards [h] with θ ⟨U, hU, hUV⟩
        refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
        obtain ⟨j, Q, hQ, hQθ⟩ := hUV θ' hθ' heq
        exact ⟨j, 0, Set.mem_univ _, Q, hQ, hQθ⟩)
    -- and the upper bound of Theorem 4.3 under pre-RMSNorm
    have hup := ae_funDim_add_le_skipless_rmsNorm μ hε hA
      (fun ℓ => differentiableOn_univ.1 (hf ℓ).differentiableOn) hdIn hw
    filter_upwards [hlow, hup] with θ h1 h2
    rw [Module.finrank_fin_fun] at h1
    omega

/-- **Proposition 4.6 of the dimension paper and Proposition 4.5 of the skips paper, for skipless
networks of MLP blocks with a real-analytic activation (tanh, GELU), without normalization, with
countably many further images of `θ`:** `fd = P − (L + 1) d²` at almost every parameter if and only
if at almost every parameter `θ` every `θ'` near `θ` with the same function is, for some `j`, the
image `img j θ` of `θ` after a change of basis by invertible `G_0, …, G_L`. The maps `img j` are any
countably many maps of the parameters, one of them the identity; the permutations of hidden units or
heads and the sign flips of tanh units, composed, are finitely many such maps. -/
theorem ae_funDim_mlp_skipless_iff_ae_locally_cob_family
    (hσ : AnalyticOnNhd ℝ σ Set.univ)
    (μ : Measure (Params
      (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ))
    {ι : Type*} [Countable ι]
    (img : ι → Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut →
      Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)
    (j₀ : ι) (himg : ∀ θ, img j₀ θ = θ) :
    (∀ᵐ θ ∂μ, funDim (Arch.mlp σ id hid) 0 θ
        + (L + 1) * Fintype.card d ^ 2
      = Module.finrank ℝ (Params
          (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)) ↔
    (∀ᵐ θ ∂μ, ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.mlp σ id hid) 0 θ' x
        = eval (Arch.mlp σ id hid) 0 θ x) →
        ∃ j : ι, ∃ G : Fin (L + 1) → GL d ℝ,
            θ' = (img j θ).cob G G) :=
  -- the case of any real-analytic blocks, with the analytic blocks `σ` entrywise
  ae_funDim_skipless_iff_ae_locally_cob_family _ rfl (fun ℓ => analyticOnNhd_f_mlp hσ ℓ) μ hdIn
    hhid img j₀ himg

/-- **Proposition 4.6 of the dimension paper and Proposition 4.5 of the skips paper, for skipless
networks of MLP blocks with a real-analytic activation (tanh, GELU), under pre-RMSNorm with `ε > 0`,
with countably many further images of `θ`:** `fd = P − (L + 1) d(d−1)/2` at almost every parameter
if and only if at almost every parameter `θ` every `θ'` near `θ` with the same function is, for some
`j`, the image `img j θ` of `θ` after a change of basis by orthogonal `Q_0, …, Q_L`. The maps `img
j` are any countably many maps of the parameters, one of them the identity; the permutations of
hidden units or heads and the sign flips of tanh units, composed, are finitely many such maps. -/
theorem ae_funDim_mlp_skipless_iff_ae_locally_cob_rmsNorm_family
    (hε : 0 < ε) (hσ : AnalyticOnNhd ℝ σ Set.univ)
    (μ : Measure (Params
      (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ))
    {ι : Type*} [Countable ι]
    (img : ι → Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut →
      Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)
    (j₀ : ι) (himg : ∀ θ, img j₀ θ = θ) :
    (∀ᵐ θ ∂μ, funDim (Arch.mlp σ (rmsNorm ε) hid) 0 θ
        + (L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2)
      = Module.finrank ℝ (Params
          (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)) ↔
    (∀ᵐ θ ∂μ, ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.mlp σ (rmsNorm ε) hid) 0 θ' x
        = eval (Arch.mlp σ (rmsNorm ε) hid) 0 θ x) →
        ∃ j : ι, ∃ Q : Fin (L + 1) → GL d ℝ,
            (∀ ℓ, (Q ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ) ∧
            θ' = (img j θ).cob Q Q) :=
  -- the case of any real-analytic blocks, with the analytic blocks `σ` entrywise
  ae_funDim_skipless_iff_ae_locally_cob_rmsNorm_family _ hε rfl
    (fun ℓ => analyticOnNhd_f_mlp hσ ℓ) μ hdIn hhid img j₀ himg

omit [Fintype T] [DecidableEq d] in
/-- Helper: a map into the parameters is `C¹` on a set if its four components are. -/
private theorem contDiffOn_params_iff1 {A : Arch T d L} {N : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] {Φ : N → Params A dIn dOut} {s : Set N}
    (hE : ContDiffOn ℝ 1 (fun n => (Φ n).E) s) (hr : ContDiffOn ℝ 1 (fun n => (Φ n).read) s)
    (hw : ContDiffOn ℝ 1 (fun n => (Φ n).write) s) (hD : ContDiffOn ℝ 1 (fun n => (Φ n).D) s) :
    ContDiffOn ℝ 1 Φ s := by
  -- the parameters are the tuples of their components, by a continuous linear equivalence
  let e := (Params.linearEquivProd (A := A) (dIn := dIn) (dOut := dOut)).toContinuousLinearEquiv
  have h : ContDiffOn ℝ 1 (e ∘ Φ) s := hE.prodMk (hr.prodMk (hw.prodMk hD))
  exact e.comp_contDiffOn_iff.1 h

omit [Fintype T] [DecidableEq d] in
/-- Helper: the rescaling `c ↦ θ.rescale c` is `C¹` where no factor `c ℓ i` vanishes (the value
columns are divided by `c ℓ i`, the rows of the writes multiplied by `c ℓ i`). -/
private theorem contDiffOn_rescale_iff1 {χ : Matrix T d ℝ → Matrix T d ℝ}
    (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut) :
    ContDiffOn ℝ 1 (fun c : ∀ ℓ, hid ℓ → ℝ => θ.rescale c) {c | ∀ ℓ i, c ℓ i ≠ 0} := by
  -- the coordinate `c ↦ c ℓ i` is linear
  have hc : ∀ ℓ i, ContDiffOn ℝ 1 (fun c : ∀ ℓ, hid ℓ → ℝ => c ℓ i) {c | ∀ ℓ i, c ℓ i ≠ 0} :=
    fun ℓ i => (contDiff_pi.1 (contDiff_apply ℝ (fun ℓ => hid ℓ → ℝ) ℓ) i).contDiffOn
  refine contDiffOn_params_iff1 ?_ ?_ ?_ ?_
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
networks of gated blocks with a real-analytic gate (SwiGLU, GeGLU), without normalization, with
countably many further images of `θ`:** `fd = P − (L + 1) d² − s` at almost every parameter (`s = ∑
d_hidden`) if and only if at almost every parameter `θ` every `θ'` near `θ` with the same function
is, for some `j`, the image `img j θ` of `θ` after a rescaling of the values of the hidden units by
nonzero factors `c` and a change of basis by invertible `G_0, …, G_L`. The maps `img j` are any
countably many maps of the parameters, one of them the identity; the permutations of hidden units or
heads and the sign flips of tanh units, composed, are finitely many such maps. -/
theorem ae_funDim_gated_skipless_iff_ae_locally_cob_rescale_family
    [Nonempty d] (hσ : AnalyticOnNhd ℝ σ Set.univ)
    (μ : Measure (Params
      (Arch.gated (T := T) (d := d) σ id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ))
    {ι : Type*} [Countable ι]
    (img : ι → Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut →
      Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (j₀ : ι) (himg : ∀ θ, img j₀ θ = θ) :
    (∀ᵐ θ ∂μ, funDim (Arch.gated σ id hid) 0 θ
        + ((L + 1) * Fintype.card d ^ 2
          + ∑ ℓ, Fintype.card (hid ℓ))
      = Module.finrank ℝ (Params
          (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)) ↔
    (∀ᵐ θ ∂μ, ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.gated σ id hid) 0 θ' x
        = eval (Arch.gated σ id hid) 0 θ x) →
        ∃ j : ι, ∃ c : ∀ ℓ, hid ℓ → ℝ, (∀ ℓ i, c ℓ i ≠ 0) ∧
          ∃ G : Fin (L + 1) → GL d ℝ,
            θ' = ((img j θ).rescale c).cob G G) := by
  constructor
  · -- the equality condition gives local identifiability up to the rescalings and the changes of
    -- basis (the statement without further images), and the identity `img j₀` is among the images
    intro h
    filter_upwards [(ae_funDim_gated_skipless_iff_ae_locally_cob_rescale hσ μ hdIn hhid).1 h]
      with θ ⟨U, hU, hUV⟩
    refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
    obtain ⟨c, hc, G, hG⟩ := hUV θ' hθ' heq
    exact ⟨j₀, c, hc, G, by rw [himg]; exact hG⟩
  · -- local identifiability gives the lower bound `P ≤ fd + (L + 1) d² + s`, with the
    -- rescalings `Ψ θ j c = (img j θ).rescale c` on the factors `c` with no zero
    intro h
    have hlow := ae_finrank_le_funDim_add_of_ae_locally_cob_family (Arch.gated σ id hid) 0
      (fun ℓ => analyticOnNhd_f_gated hσ ℓ) analyticOnNhd_id μ (N := ∀ ℓ, hid ℓ → ℝ)
      (fun θ j c => (img j θ).rescale c) (fun _ => {c | ∀ ℓ i, c ℓ i ≠ 0})
      (fun θ j => contDiffOn_rescale_iff1 (img j θ)) (by
        filter_upwards [h] with θ ⟨U, hU, hUV⟩
        refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
        obtain ⟨j, c, hc, G, hG⟩ := hUV θ' hθ' heq
        exact ⟨j, c, hc, G, hG⟩)
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
networks of gated blocks with a real-analytic gate (SwiGLU, GeGLU), under pre-RMSNorm with `ε > 0`,
with countably many further images of `θ`:** `fd = P − (L + 1) d(d−1)/2 − s` at almost every
parameter (`s = ∑ d_hidden`) if and only if at almost every parameter `θ` every `θ'` near `θ` with
the same function is, for some `j`, the image `img j θ` of `θ` after a rescaling of the values of
the hidden units by nonzero factors `c` and a change of basis by orthogonal `Q_0, …, Q_L`. The maps
`img j` are any countably many maps of the parameters, one of them the identity; the permutations of
hidden units or heads and the sign flips of tanh units, composed, are finitely many such maps. -/
theorem ae_funDim_gated_skipless_iff_ae_locally_cob_rescale_rmsNorm_family
    (hε : 0 < ε) [Nonempty d] (hσ : AnalyticOnNhd ℝ σ Set.univ)
    (μ : Measure (Params
      (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ))
    {ι : Type*} [Countable ι]
    (img : ι → Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut →
      Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)
    (j₀ : ι) (himg : ∀ θ, img j₀ θ = θ) :
    (∀ᵐ θ ∂μ, funDim (Arch.gated σ (rmsNorm ε) hid) 0 θ
        + ((L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2)
          + ∑ ℓ, Fintype.card (hid ℓ))
      = Module.finrank ℝ (Params
          (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)) ↔
    (∀ᵐ θ ∂μ, ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.gated σ (rmsNorm ε) hid) 0 θ' x
        = eval (Arch.gated σ (rmsNorm ε) hid) 0 θ x) →
        ∃ j : ι, ∃ c : ∀ ℓ, hid ℓ → ℝ, (∀ ℓ i, c ℓ i ≠ 0) ∧
          ∃ Q : Fin (L + 1) → GL d ℝ,
            (∀ ℓ, (Q ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ) ∧
            θ' = ((img j θ).rescale c).cob Q Q) := by
  constructor
  · -- the equality condition gives local identifiability up to the rescalings and the orthogonal
    -- changes of basis (the statement without further images), and the identity `img j₀` is
    -- among the images
    intro h
    filter_upwards
      [(ae_funDim_gated_skipless_iff_ae_locally_cob_rescale_rmsNorm hε hσ μ hdIn hhid).1 h]
      with θ ⟨U, hU, hUV⟩
    refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
    obtain ⟨c, hc, Q, hQ, hQθ⟩ := hUV θ' hθ' heq
    exact ⟨j₀, c, hc, Q, hQ, by rw [himg]; exact hQθ⟩
  · -- local identifiability gives the lower bound `P ≤ fd + (L + 1) d(d−1)/2 + s`, with the
    -- rescalings `Ψ θ j c = (img j θ).rescale c` on the factors `c` with no zero
    intro h
    have hlow := ae_finrank_le_funDim_add_of_ae_locally_cob_orthogonal_family
      (Arch.gated σ (rmsNorm ε) hid) 0 (fun ℓ => analyticOnNhd_f_gated hσ ℓ)
      (analyticOnNhd_rmsNorm hε) μ (N := ∀ ℓ, hid ℓ → ℝ)
      (fun θ j c => (img j θ).rescale c) (fun _ => {c | ∀ ℓ i, c ℓ i ≠ 0})
      (fun θ j => contDiffOn_rescale_iff1 (img j θ)) (by
        filter_upwards [h] with θ ⟨U, hU, hUV⟩
        refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
        obtain ⟨j, c, hc, Q, hQ, hQθ⟩ := hUV θ' hθ' heq
        exact ⟨j, c, hc, Q, hQ, hQθ⟩)
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

/-- Helper: the determinant of a square matrix whose entries are analytic functions is
analytic. -/
private theorem analyticOnNhd_det_iff1 {N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    {n : Type*} [Fintype n] [DecidableEq n] {Φ : N → Matrix n n ℝ}
    (h : ∀ a b, AnalyticOnNhd ℝ (fun p => Φ p a b) Set.univ) :
    AnalyticOnNhd ℝ (fun p => (Φ p).det) Set.univ := by
  simp only [Matrix.det_apply']
  exact Finset.analyticOnNhd_fun_sum _ fun σ _ => analyticOnNhd_const.mul
    (Finset.analyticOnNhd_fun_prod _ fun i _ => h (σ i) i)

/-- Helper: where a square matrix with analytic entries is invertible, the entries of its inverse
are `C¹` (`M⁻¹ = (det M)⁻¹ adj M`, and the entries of the adjugate are determinants). -/
private theorem contDiffOn_inv_entry_iff1 {N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    {n : Type*} [Fintype n] [DecidableEq n] {Φ : N → Matrix n n ℝ}
    (h : ∀ a b, AnalyticOnNhd ℝ (fun p => Φ p a b) Set.univ) {s : Set N}
    (hs : ∀ p ∈ s, (Φ p).det ≠ 0) (a b : n) :
    ContDiffOn ℝ 1 (fun p => (Φ p)⁻¹ a b) s := by
  have he : (fun p => (Φ p)⁻¹ a b)
      = fun p => ((Φ p).det)⁻¹ * ((Φ p).updateRow b (Pi.single a 1)).det := by
    funext p
    rw [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, Matrix.adjugate_apply,
      smul_eq_mul]
  rw [he]
  -- the determinant and the entries of the adjugate are analytic, so `C¹`
  have h1 : ContDiff ℝ 1 (fun p => (Φ p).det) := (analyticOnNhd_det_iff1 h).contDiff
  have h2 : ContDiff ℝ 1 (fun p => ((Φ p).updateRow b (Pi.single a 1)).det) := by
    refine (analyticOnNhd_det_iff1 fun i j => ?_).contDiff
    by_cases hi : i = b
    · subst hi
      simp only [Matrix.updateRow_self]
      exact analyticOnNhd_const
    · simp only [Matrix.updateRow_ne hi]
      exact h i j
  -- and `x ↦ x⁻¹` is smooth away from `0`
  exact (h1.contDiffOn.inv hs).mul h2.contDiffOn

omit [∀ ℓ, DecidableEq (dh ℓ)] in
/-- Helper (the private `finrank_headFun_uba` of `Dimension/UpperBoundAttention.lean`): the
families `Γ` of `d_h × d_h` matrices, one for each head of each block, form a space of dimension
`∑_ℓ H_ℓ d_{h,ℓ}²`. -/
private theorem finrank_headFun_iff1 :
    Module.finrank ℝ (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)
      = ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2 := by
  rw [Module.finrank_pi_fintype]
  simp only [Module.finrank_pi_fintype, Module.finrank_matrix, Module.finrank_self, mul_one,
    Finset.sum_const, Finset.card_univ, smul_eq_mul, sq]

omit [DecidableEq d] [∀ ℓ, DecidableEq (dh ℓ)] in
/-- Helper: the changes of basis inside the heads (`Params.headsQK` and then `Params.headsVO`),
written with matrices `k`, `k'` and separate matrices `ki`, `ki'` in the places of their
inverses: `W_{Q,i} k_i`, `W_{K,i} ki_iᵀ`, `W_{V,i} k'_i`, `ki'_i W_{O,i}`. -/
private noncomputable def headsMat_iff1 {χ : Matrix T d ℝ → Matrix T d ℝ}
    (θ : Params (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut)
    (k ki k' ki' : ∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) :
    Params (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut where
  E := θ.E
  read ℓ := Matrix.of fun a p =>
    match p.2 with
    | Sum.inl j => ∑ j', θ.read ℓ a (p.1, Sum.inl j') * k ℓ p.1 j' j
    | Sum.inr (Sum.inl j) => ∑ j', θ.read ℓ a (p.1, Sum.inr (Sum.inl j')) * ki ℓ p.1 j j'
    | Sum.inr (Sum.inr j) => ∑ j', θ.read ℓ a (p.1, Sum.inr (Sum.inr j')) * k' ℓ p.1 j' j
  write ℓ := Matrix.of fun (p : H ℓ × dh ℓ) b => ∑ j', ki' ℓ p.1 p.2 j' * θ.write ℓ (p.1, j') b
  D := θ.D

omit [DecidableEq d] in
/-- Helper: `headsMat_iff1` with the matrix inverses of `k`, `k'` in the places of the inverses:
the family `Ψ θ` of the changes of basis inside the heads. -/
private noncomputable def headsInv_iff1 {χ : Matrix T d ℝ → Matrix T d ℝ}
    (θ : Params (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut)
    (p : (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)) :
    Params (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut :=
  headsMat_iff1 θ p.1 (fun ℓ i => (p.1 ℓ i)⁻¹) p.2 (fun ℓ i => (p.2 ℓ i)⁻¹)

omit [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: at invertible matrices `K`, `K'`, `headsInv_iff1` is `(θ.headsQK K).headsVO K'`. -/
private theorem headsInv_eq_iff1 {χ : Matrix T d ℝ → Matrix T d ℝ}
    (θ : Params (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut)
    (K K' : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ) :
    headsInv_iff1 θ (fun ℓ i => (K ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ),
        fun ℓ i => (K' ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ))
      = (θ.headsQK K).headsVO K' := by
  -- the matrix inverse of `K ℓ i` is the inverse in `GL`
  show headsMat_iff1 θ (fun ℓ i => (K ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ))
      (fun ℓ i => (K ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)⁻¹) (fun ℓ i => (K' ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ))
      (fun ℓ i => (K' ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)⁻¹) = _
  simp only [← Matrix.coe_units_inv]
  -- then the two agree entry by entry
  refine Params.ext' rfl (fun ℓ => ?_) (fun ℓ => rfl) rfl
  ext a ⟨i, j | j | j⟩ <;> rfl

omit [DecidableEq d] in
/-- Helper: the family `p ↦ headsInv_iff1 θ p` is `C¹` where the matrices are invertible. -/
private theorem contDiffOn_headsInv_iff1 {χ : Matrix T d ℝ → Matrix T d ℝ}
    (θ : Params (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut) :
    ContDiffOn ℝ 1 (headsInv_iff1 θ)
      {p | ∀ ℓ i, (p.1 ℓ i).det ≠ 0 ∧ (p.2 ℓ i).det ≠ 0} := by
  -- the entries of `p.1 ℓ i` and of `p.2 ℓ i` are linear in `p`
  have hc1 : ∀ ℓ i a b, AnalyticOnNhd ℝ (fun p : (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)
      × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) => p.1 ℓ i a b) Set.univ := fun ℓ i a b =>
    analyticOnNhd_linear
      { toFun := fun p : (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)
          × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) => p.1 ℓ i a b
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
  have hc2 : ∀ ℓ i a b, AnalyticOnNhd ℝ (fun p : (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)
      × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) => p.2 ℓ i a b) Set.univ := fun ℓ i a b =>
    analyticOnNhd_linear
      { toFun := fun p : (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)
          × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) => p.2 ℓ i a b
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
  -- the entries of their inverses are `C¹` where they are invertible
  have hi1 := fun ℓ i => contDiffOn_inv_entry_iff1 (hc1 ℓ i)
    (s := {p | ∀ ℓ i, (p.1 ℓ i).det ≠ 0 ∧ (p.2 ℓ i).det ≠ 0}) (fun p hp => (hp ℓ i).1)
  have hi2 := fun ℓ i => contDiffOn_inv_entry_iff1 (hc2 ℓ i)
    (s := {p | ∀ ℓ i, (p.1 ℓ i).det ≠ 0 ∧ (p.2 ℓ i).det ≠ 0}) (fun p hp => (hp ℓ i).2)
  refine contDiffOn_params_iff1 ?_ ?_ ?_ ?_
  · show ContDiffOn ℝ 1 (fun _ => θ.E) _
    exact contDiffOn_const
  · -- the reads: sums of products of an entry of the read and an entry of `k`, `k⁻¹` or `k'`
    refine contDiffOn_pi.2 fun ℓ => contDiffOn_pi.2 fun a => contDiffOn_pi.2 fun q => ?_
    rcases q with ⟨i, j | j | j⟩
    · show ContDiffOn ℝ 1 (fun p : (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)
          × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) =>
        ∑ j', θ.read ℓ a (i, Sum.inl j') * p.1 ℓ i j' j) _
      exact ContDiffOn.sum fun j' _ => contDiffOn_const.mul (hc1 ℓ i j' j).contDiff.contDiffOn
    · show ContDiffOn ℝ 1 (fun p : (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)
          × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) =>
        ∑ j', θ.read ℓ a (i, Sum.inr (Sum.inl j')) * (p.1 ℓ i)⁻¹ j j') _
      exact ContDiffOn.sum fun j' _ => contDiffOn_const.mul (hi1 ℓ i j j')
    · show ContDiffOn ℝ 1 (fun p : (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)
          × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) =>
        ∑ j', θ.read ℓ a (i, Sum.inr (Sum.inr j')) * p.2 ℓ i j' j) _
      exact ContDiffOn.sum fun j' _ => contDiffOn_const.mul (hc2 ℓ i j' j).contDiff.contDiffOn
  · -- the writes: sums of products of an entry of `k'⁻¹` and an entry of the write
    refine contDiffOn_pi.2 fun ℓ => contDiffOn_pi.2 fun q => contDiffOn_pi.2 fun b => ?_
    obtain ⟨i, j⟩ := q
    show ContDiffOn ℝ 1 (fun p : (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)
        × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) =>
      ∑ j', (p.2 ℓ i)⁻¹ j j' * θ.write ℓ (i, j') b) _
    exact ContDiffOn.sum fun j' _ => (hi2 ℓ i j j').mul contDiffOn_const
  · show ContDiffOn ℝ 1 (fun _ => θ.D) _
    exact contDiffOn_const

omit [DecidableEq d] [∀ ℓ, DecidableEq (dh ℓ)] in
/-- Helper: the pairs of families of `d_h × d_h` matrices form a space of dimension
`2 ∑_ℓ H_ℓ d_{h,ℓ}²`. -/
private theorem finrank_headFun_prod_iff1 :
    Module.finrank ℝ ((∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ))
      = 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2 := by
  rw [Module.finrank_prod, finrank_headFun_iff1]
  ring

/-- **Proposition 4.6 of the dimension paper and Proposition 4.5 of the skips paper, for skipless
networks of attention blocks, without normalization, with countably many further images of `θ`:**
`fd = P − (L + 1) d² − s` at almost every parameter (`s = 2 ∑ H d_h²`) if and only if at almost
every parameter `θ` every `θ'` near `θ` with the same function is, for some `j`, the image `img j θ`
of `θ` after changes of basis inside the heads and a change of basis by invertible `G_0, …, G_L`.
The maps `img j` are any countably many maps of the parameters, one of them the identity; the
permutations of hidden units or heads and the sign flips of tanh units, composed, are finitely many
such maps. -/
theorem ae_funDim_attention_skipless_iff_ae_locally_cob_heads_family
    (μ : Measure (Params
      (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d)
    (hH : ∀ ℓ, Fintype.card d ≤ Fintype.card (H ℓ) * Fintype.card (dh ℓ))
    {ι : Type*} [Countable ι]
    (img : ι → Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut →
      Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut)
    (j₀ : ι) (himg : ∀ θ, img j₀ θ = θ) :
    (∀ᵐ θ ∂μ, funDim (Arch.attention sees id H dh) 0 θ
        + ((L + 1) * Fintype.card d ^ 2
          + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
      = Module.finrank ℝ (Params
          (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut)) ↔
    (∀ᵐ θ ∂μ, ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.attention sees id H dh) 0 θ' x
        = eval (Arch.attention sees id H dh) 0 θ x) →
        ∃ j : ι, ∃ K K' : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ,
          ∃ G : Fin (L + 1) → GL d ℝ,
            θ' = (((img j θ).headsQK K).headsVO K').cob G G) := by
  constructor
  · -- the equality condition gives local identifiability up to the changes of basis inside the
    -- heads and of the hidden states (the statement without further images), and the identity
    -- `img j₀` is among the images
    intro h
    filter_upwards
      [(ae_funDim_attention_skipless_iff_ae_locally_cob_heads μ hdIn hdh hH).1 h]
      with θ ⟨U, hU, hUV⟩
    refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
    obtain ⟨K, K', G, hG⟩ := hUV θ' hθ' heq
    exact ⟨j₀, K, K', G, by rw [himg]; exact hG⟩
  · -- local identifiability gives the lower bound `P ≤ fd + (L + 1) d² + s`, with the changes of
    -- basis inside the heads `Ψ θ j (k, k') = headsInv_iff1 (img j θ) (k, k')` on the pairs of
    -- families of invertible matrices
    intro h
    have hlow := ae_finrank_le_funDim_add_of_ae_locally_cob_family
      (Arch.attention sees id H dh) 0
      (fun ℓ => analyticOnNhd_f_attention sees id H dh ℓ) analyticOnNhd_id μ
      (fun θ j p => headsInv_iff1 (img j θ) p)
      (fun _ => {p | ∀ ℓ i, (p.1 ℓ i).det ≠ 0 ∧ (p.2 ℓ i).det ≠ 0})
      (fun θ j => contDiffOn_headsInv_iff1 (img j θ)) (by
        filter_upwards [h] with θ ⟨U, hU, hUV⟩
        refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
        obtain ⟨j, K, K', G, hG⟩ := hUV θ' hθ' heq
        refine ⟨j, (fun ℓ i => (K ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ),
          fun ℓ i => (K' ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)), fun ℓ i => ⟨?_, ?_⟩, G, ?_⟩
        · exact ((Matrix.isUnit_iff_isUnit_det _).1 (K ℓ i).isUnit).ne_zero
        · exact ((Matrix.isUnit_iff_isUnit_det _).1 (K' ℓ i).isUnit).ne_zero
        · show θ' = (headsInv_iff1 (img j θ) _).cob G G
          rw [headsInv_eq_iff1]
          exact hG)
    -- and the upper bound of Theorem 4.3 for attention blocks
    have hup := ae_funDim_add_le_skipless_attention μ hdIn hdh hH
    filter_upwards [hlow, hup] with θ h1 h2
    rw [finrank_headFun_prod_iff1] at h1
    generalize ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2 = s at h1 h2
    omega

/-- **Proposition 4.6 of the dimension paper and Proposition 4.5 of the skips paper, for skipless
networks of attention blocks, under pre-RMSNorm with `ε > 0`, with countably many further images of
`θ`:** `fd = P − (L + 1) d(d−1)/2 − s` at almost every parameter (`s = 2 ∑ H d_h²`) if and only if
at almost every parameter `θ` every `θ'` near `θ` with the same function is, for some `j`, the image
`img j θ` of `θ` after changes of basis inside the heads and a change of basis by orthogonal `Q_0,
…, Q_L`. The maps `img j` are any countably many maps of the parameters, one of them the identity;
the permutations of hidden units or heads and the sign flips of tanh units, composed, are finitely
many such maps. -/
theorem ae_funDim_attention_skipless_iff_ae_locally_cob_heads_rmsNorm_family
    (hε : 0 < ε)
    (μ : Measure (Params
      (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d)
    (hH : ∀ ℓ, Fintype.card d ≤ Fintype.card (H ℓ) * Fintype.card (dh ℓ))
    {ι : Type*} [Countable ι]
    (img : ι → Params (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut →
      Params (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut)
    (j₀ : ι) (himg : ∀ θ, img j₀ θ = θ) :
    (∀ᵐ θ ∂μ, funDim (Arch.attention sees (rmsNorm ε) H dh) 0 θ
        + ((L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2)
          + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
      = Module.finrank ℝ (Params
          (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut)) ↔
    (∀ᵐ θ ∂μ, ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.attention sees (rmsNorm ε) H dh) 0 θ' x
        = eval (Arch.attention sees (rmsNorm ε) H dh) 0 θ x) →
        ∃ j : ι, ∃ K K' : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ,
          ∃ Q : Fin (L + 1) → GL d ℝ,
            (∀ ℓ, (Q ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ) ∧
            θ' = (((img j θ).headsQK K).headsVO K').cob Q Q) := by
  constructor
  · -- the equality condition gives local identifiability up to the changes of basis inside the
    -- heads and the orthogonal changes of basis (the statement without further images), and the
    -- identity `img j₀` is among the images
    intro h
    filter_upwards
      [(ae_funDim_attention_skipless_iff_ae_locally_cob_heads_rmsNorm hε μ hdIn hdh hH).1 h]
      with θ ⟨U, hU, hUV⟩
    refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
    obtain ⟨K, K', Q, hQ, hQθ⟩ := hUV θ' hθ' heq
    exact ⟨j₀, K, K', Q, hQ, by rw [himg]; exact hQθ⟩
  · -- local identifiability gives the lower bound `P ≤ fd + (L + 1) d(d−1)/2 + s`, with the
    -- changes of basis inside the heads `Ψ θ j (k, k') = headsInv_iff1 (img j θ) (k, k')` on the
    -- pairs of families of invertible matrices
    intro h
    have hlow := ae_finrank_le_funDim_add_of_ae_locally_cob_orthogonal_family
      (Arch.attention sees (rmsNorm ε) H dh) 0
      (fun ℓ => analyticOnNhd_f_attention sees (rmsNorm ε) H dh ℓ) (analyticOnNhd_rmsNorm hε) μ
      (fun θ j p => headsInv_iff1 (img j θ) p)
      (fun _ => {p | ∀ ℓ i, (p.1 ℓ i).det ≠ 0 ∧ (p.2 ℓ i).det ≠ 0})
      (fun θ j => contDiffOn_headsInv_iff1 (img j θ)) (by
        filter_upwards [h] with θ ⟨U, hU, hUV⟩
        refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
        obtain ⟨j, K, K', Q, hQ, hQθ⟩ := hUV θ' hθ' heq
        refine ⟨j, (fun ℓ i => (K ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ),
          fun ℓ i => (K' ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)), fun ℓ i => ⟨?_, ?_⟩, Q, hQ, ?_⟩
        · exact ((Matrix.isUnit_iff_isUnit_det _).1 (K ℓ i).isUnit).ne_zero
        · exact ((Matrix.isUnit_iff_isUnit_det _).1 (K' ℓ i).isUnit).ne_zero
        · show θ' = (headsInv_iff1 (img j θ) _).cob Q Q
          rw [headsInv_eq_iff1]
          exact hQθ)
    -- and the upper bound of Theorem 4.3 for attention blocks under pre-RMSNorm
    have hup := ae_funDim_add_le_skipless_attention_rmsNorm ε μ hdIn hdh hH
    filter_upwards [hlow, hup] with θ h1 h2
    rw [finrank_headFun_prod_iff1] at h1
    generalize ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2 = s at h1 h2
    generalize Fintype.card d * (Fintype.card d - 1) / 2 = q at h1 h2
    omega

end Skips
