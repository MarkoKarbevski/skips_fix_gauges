import SkipsLean.Residual.IdentifiableIffFamily
import SkipsLean.Symmetry.FiniteSymmetries

/-!
# The equality condition is local identifiability up to all the symmetries: residual networks

Paper (skips paper, Proposition 4.5): "A skipless or a residual network satisfies the equality
condition if and only if, at generic parameters, it is locally identifiable up to its symmetries."
(The dimension paper, Proposition 4.6, has skipless networks only.) Definition 4.4 of the skips
paper (4.5 of the dimension paper): "A network is
identifiable up to its symmetries at `θ` if every `θ′` with `F_{θ′} = F_θ` is the image of `θ`
under a symmetry: a change of basis […], a symmetry inside a block, or a composition of these. It
is locally identifiable at `θ` if this holds for every `θ′` in some neighborhood of `θ`." The
symmetries inside the blocks (dimension paper, Appendix B): "Permutations of hidden units or heads
and sign flips of tanh hidden units are finite and remove no parameters", and the continuous ones
(the rescalings of the values of gated units, the changes of basis inside the heads).

Here the equivalence in this form, for the kinds of block of the papers: every `θ'` near `θ` with
the same function is `θ` after a finite symmetry (`Symmetry/FiniteSymmetries.lean`: a permutation
of the hidden units, `Params.permUnits`, `Params.permUnitsGated`; sign flips, `Params.flipUnits`;
a permutation of the heads, `Params.permHeads`), a continuous symmetry inside the blocks and a
change of basis. A composition of symmetries in any order has this form: the changes of basis
commute with the symmetries inside the blocks, and the finite symmetries normalize the continuous
ones. The forms with the permutations alone are stated for every real-analytic activation (GELU,
and tanh); the forms with the sign flips are the paper's for an odd activation (tanh), where the
sign flips preserve the function (`eval_flipUnits`). As statements they hold for every
real-analytic activation.

Each statement is the case of the statement with `_family` of the same kind
(`Residual/IdentifiableIffFamily.lean`) in which the maps `img j` are the finite
symmetries; the identity is the trivial permutation with the signs `1`.
-/

namespace Skips

open Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {sees : T → T → Prop} [DecidableRel sees]
variable {H dh hid : Fin L → Type} [∀ ℓ, Fintype (H ℓ)] [∀ ℓ, Fintype (dh ℓ)]
  [∀ ℓ, DecidableEq (dh ℓ)] [∀ ℓ, Fintype (hid ℓ)] {σ : ℝ → ℝ} {ε : ℝ}

/-- **Proposition 4.5 of the skips paper, for residual networks of MLP blocks with a real-analytic
activation (tanh, GELU), without normalization, with the permutations of the hidden units:** `fd = P
− d²` at almost every parameter if and only if at almost every parameter `θ` every `θ'` near `θ`
with the same function is `θ` after a permutation of the hidden units of every block, a change of
basis by one invertible `G` at all hidden states. -/
theorem ae_funDim_mlp_residual_iff_ae_locally_cob_perm
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
        ∃ p : ∀ ℓ, Equiv.Perm (hid ℓ), ∃ G : GL d ℝ,
            θ' = (θ.permUnits p).cob
              (fun _ => G) (fun _ => G)) := by
  have hfam := ae_funDim_mlp_residual_iff_ae_locally_cob_family hσ μ hdIn
    (fun (p : (∀ ℓ, Equiv.Perm (hid ℓ))) θ => θ.permUnits p) (fun _ => 1)
    permUnits_one
  refine hfam.trans ⟨fun h => ?_, fun h => ?_⟩
  · -- a symmetry `j` of the family is a finite symmetry: unpack the index
    filter_upwards [h] with θ ⟨U, hU, hUV⟩
    refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
    obtain ⟨p, G, hθ''⟩ := hUV θ' hθ' heq
    exact ⟨p, G, hθ''⟩
  · -- a finite symmetry is a symmetry `j` of the family: pack the index
    filter_upwards [h] with θ ⟨U, hU, hUV⟩
    refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
    obtain ⟨p, G, hθ''⟩ := hUV θ' hθ' heq
    exact ⟨p, G, hθ''⟩

/-- **Proposition 4.5 of the skips paper, for residual networks of MLP blocks with a real-analytic
activation (tanh, GELU), without normalization, with the permutations and the sign flips of the
hidden units (the finite symmetries for an odd activation: tanh; for an activation that is not odd,
such as GELU, the images under the sign flips are not symmetric, and the paper's form is the one
with the permutations alone):** `fd = P − d²` at almost every parameter if and only if at almost
every parameter `θ` every `θ'` near `θ` with the same function is `θ` after a permutation of the
hidden units of every block, sign flips of hidden units, a change of basis by one invertible `G` at
all hidden states. -/
theorem ae_funDim_mlp_residual_iff_ae_locally_cob_perm_flip
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
        ∃ (p : ∀ ℓ, Equiv.Perm (hid ℓ)) (s : ∀ ℓ, hid ℓ → ℤˣ), ∃ G : GL d ℝ,
            θ' = ((θ.permUnits p).flipUnits s).cob
              (fun _ => G) (fun _ => G)) := by
  have hfam := ae_funDim_mlp_residual_iff_ae_locally_cob_family hσ μ hdIn
    (fun (ps : (∀ ℓ, Equiv.Perm (hid ℓ)) × (∀ ℓ, hid ℓ → ℤˣ)) θ =>
      (θ.permUnits ps.1).flipUnits ps.2) (fun _ => 1, fun _ _ => 1)
    (fun θ => by
      show (θ.permUnits fun _ => 1).flipUnits (fun _ _ => 1) = θ
      rw [permUnits_one, flipUnits_one])
  refine hfam.trans ⟨fun h => ?_, fun h => ?_⟩
  · -- a symmetry `j` of the family is a finite symmetry: unpack the index
    filter_upwards [h] with θ ⟨U, hU, hUV⟩
    refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
    obtain ⟨⟨p, s⟩, G, hθ''⟩ := hUV θ' hθ' heq
    exact ⟨p, s, G, hθ''⟩
  · -- a finite symmetry is a symmetry `j` of the family: pack the index
    filter_upwards [h] with θ ⟨U, hU, hUV⟩
    refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
    obtain ⟨p, s, G, hθ''⟩ := hUV θ' hθ' heq
    exact ⟨(p, s), G, hθ''⟩

/-- **Proposition 4.5 of the skips paper, for residual networks of MLP blocks with a real-analytic
activation (tanh, GELU), under pre-RMSNorm with `ε > 0`, with the permutations of the hidden
units:** `fd = P − d(d−1)/2` at almost every parameter if and only if at almost every parameter `θ`
every `θ'` near `θ` with the same function is `θ` after a permutation of the hidden units of every
block, a change of basis by one orthogonal `Q` at all hidden states. -/
theorem ae_funDim_mlp_residual_iff_ae_locally_cob_rmsNorm_perm
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
        ∃ p : ∀ ℓ, Equiv.Perm (hid ℓ), ∃ Q : GL d ℝ, (Q : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d
            ℝ ∧
            θ' = (θ.permUnits p).cob
              (fun _ => Q) (fun _ => Q)) := by
  have hfam := ae_funDim_mlp_residual_iff_ae_locally_cob_rmsNorm_family hε hσ μ hdIn
    (fun (p : (∀ ℓ, Equiv.Perm (hid ℓ))) θ => θ.permUnits p) (fun _ => 1)
    permUnits_one
  refine hfam.trans ⟨fun h => ?_, fun h => ?_⟩
  · -- a symmetry `j` of the family is a finite symmetry: unpack the index
    filter_upwards [h] with θ ⟨U, hU, hUV⟩
    refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
    obtain ⟨p, Q, hQ, hθ''⟩ := hUV θ' hθ' heq
    exact ⟨p, Q, hQ, hθ''⟩
  · -- a finite symmetry is a symmetry `j` of the family: pack the index
    filter_upwards [h] with θ ⟨U, hU, hUV⟩
    refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
    obtain ⟨p, Q, hQ, hθ''⟩ := hUV θ' hθ' heq
    exact ⟨p, Q, hQ, hθ''⟩

/-- **Proposition 4.5 of the skips paper, for residual networks of MLP blocks with a real-analytic
activation (tanh, GELU), under pre-RMSNorm with `ε > 0`, with the permutations and the sign flips of
the hidden units (the finite symmetries for an odd activation: tanh; for an activation that is not
odd, such as GELU, the images under the sign flips are not symmetric, and the paper's form is the
one with the permutations alone):** `fd = P − d(d−1)/2` at almost every parameter if and only if at
almost every parameter `θ` every `θ'` near `θ` with the same function is `θ` after a permutation of
the hidden units of every block, sign flips of hidden units, a change of basis by one orthogonal `Q`
at all hidden states. -/
theorem ae_funDim_mlp_residual_iff_ae_locally_cob_rmsNorm_perm_flip
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
        ∃ (p : ∀ ℓ, Equiv.Perm (hid ℓ)) (s : ∀ ℓ, hid ℓ → ℤˣ), ∃ Q : GL d ℝ, (Q : Matrix d d ℝ) ∈
            Matrix.orthogonalGroup d ℝ ∧
            θ' = ((θ.permUnits p).flipUnits s).cob
              (fun _ => Q) (fun _ => Q)) := by
  have hfam := ae_funDim_mlp_residual_iff_ae_locally_cob_rmsNorm_family hε hσ μ hdIn
    (fun (ps : (∀ ℓ, Equiv.Perm (hid ℓ)) × (∀ ℓ, hid ℓ → ℤˣ)) θ =>
      (θ.permUnits ps.1).flipUnits ps.2) (fun _ => 1, fun _ _ => 1)
    (fun θ => by
      show (θ.permUnits fun _ => 1).flipUnits (fun _ _ => 1) = θ
      rw [permUnits_one, flipUnits_one])
  refine hfam.trans ⟨fun h => ?_, fun h => ?_⟩
  · -- a symmetry `j` of the family is a finite symmetry: unpack the index
    filter_upwards [h] with θ ⟨U, hU, hUV⟩
    refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
    obtain ⟨⟨p, s⟩, Q, hQ, hθ''⟩ := hUV θ' hθ' heq
    exact ⟨p, s, Q, hQ, hθ''⟩
  · -- a finite symmetry is a symmetry `j` of the family: pack the index
    filter_upwards [h] with θ ⟨U, hU, hUV⟩
    refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
    obtain ⟨p, s, Q, hQ, hθ''⟩ := hUV θ' hθ' heq
    exact ⟨(p, s), Q, hQ, hθ''⟩

/-- **Proposition 4.5 of the skips paper, for residual networks of gated blocks with a real-analytic
gate (SwiGLU, GeGLU), without normalization, with the permutations of the hidden units:** `fd = P −
d² − s` at almost every parameter (`s = ∑ d_hidden`) if and only if at almost every parameter `θ`
every `θ'` near `θ` with the same function is `θ` after a permutation of the hidden units of every
block, a rescaling of the values of the hidden units by nonzero factors `c` and a change of basis by
one invertible `G` at all hidden states. -/
theorem ae_funDim_gated_residual_iff_ae_locally_cob_rescale_perm
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
        ∃ p : ∀ ℓ, Equiv.Perm (hid ℓ), ∃ c : ∀ ℓ, hid ℓ → ℝ, (∀ ℓ i, c ℓ i ≠ 0) ∧
          ∃ G : GL d ℝ,
            θ' = ((θ.permUnitsGated p).rescale c).cob
              (fun _ => G) (fun _ => G)) := by
  have hfam := ae_funDim_gated_residual_iff_ae_locally_cob_rescale_family hσ μ hdIn
    (fun (p : (∀ ℓ, Equiv.Perm (hid ℓ))) θ => θ.permUnitsGated p) (fun _ => 1)
    permUnitsGated_one
  refine hfam.trans ⟨fun h => ?_, fun h => ?_⟩
  · -- a symmetry `j` of the family is a finite symmetry: unpack the index
    filter_upwards [h] with θ ⟨U, hU, hUV⟩
    refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
    obtain ⟨p, c, hc, G, hθ''⟩ := hUV θ' hθ' heq
    exact ⟨p, c, hc, G, hθ''⟩
  · -- a finite symmetry is a symmetry `j` of the family: pack the index
    filter_upwards [h] with θ ⟨U, hU, hUV⟩
    refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
    obtain ⟨p, c, hc, G, hθ''⟩ := hUV θ' hθ' heq
    exact ⟨p, c, hc, G, hθ''⟩

/-- **Proposition 4.5 of the skips paper, for residual networks of gated blocks with a real-analytic
gate (SwiGLU, GeGLU), under pre-RMSNorm with `ε > 0`, with the permutations of the hidden units:**
`fd = P − d(d−1)/2 − s` at almost every parameter (`s = ∑ d_hidden`) if and only if at almost every
parameter `θ` every `θ'` near `θ` with the same function is `θ` after a permutation of the hidden
units of every block, a rescaling of the values of the hidden units by nonzero factors `c` and a
change of basis by one orthogonal `Q` at all hidden states. -/
theorem ae_funDim_gated_residual_iff_ae_locally_cob_rescale_rmsNorm_perm
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
        ∃ p : ∀ ℓ, Equiv.Perm (hid ℓ), ∃ c : ∀ ℓ, hid ℓ → ℝ, (∀ ℓ i, c ℓ i ≠ 0) ∧
          ∃ Q : GL d ℝ, (Q : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ ∧
            θ' = ((θ.permUnitsGated p).rescale c).cob
              (fun _ => Q) (fun _ => Q)) := by
  have hfam := ae_funDim_gated_residual_iff_ae_locally_cob_rescale_rmsNorm_family hε hσ μ hdIn
    (fun (p : (∀ ℓ, Equiv.Perm (hid ℓ))) θ => θ.permUnitsGated p) (fun _ => 1)
    permUnitsGated_one
  refine hfam.trans ⟨fun h => ?_, fun h => ?_⟩
  · -- a symmetry `j` of the family is a finite symmetry: unpack the index
    filter_upwards [h] with θ ⟨U, hU, hUV⟩
    refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
    obtain ⟨p, c, hc, Q, hQ, hθ''⟩ := hUV θ' hθ' heq
    exact ⟨p, c, hc, Q, hQ, hθ''⟩
  · -- a finite symmetry is a symmetry `j` of the family: pack the index
    filter_upwards [h] with θ ⟨U, hU, hUV⟩
    refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
    obtain ⟨p, c, hc, Q, hQ, hθ''⟩ := hUV θ' hθ' heq
    exact ⟨p, c, hc, Q, hQ, hθ''⟩

/-- **Proposition 4.5 of the skips paper, for residual networks of attention blocks, without
normalization, with the permutations of the heads:** `fd = P − d² − s` at almost every parameter (`s
= 2 ∑ H d_h²`) if and only if at almost every parameter `θ` every `θ'` near `θ` with the same
function is `θ` after a permutation of the heads of every block, changes of basis inside the heads
and a change of basis by one invertible `G` at all hidden states. -/
theorem ae_funDim_attention_residual_iff_ae_locally_cob_heads_perm
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
        ∃ q : ∀ ℓ, Equiv.Perm (H ℓ), ∃ K K' : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ,
          ∃ G : GL d ℝ,
            θ' = (((θ.permHeads q).headsQK K).headsVO K').cob
              (fun _ => G) (fun _ => G)) := by
  have hfam := ae_funDim_attention_residual_iff_ae_locally_cob_heads_family μ hdIn hdh
    (fun (q : (∀ ℓ, Equiv.Perm (H ℓ))) θ => θ.permHeads q) (fun _ => 1)
    permHeads_one
  refine hfam.trans ⟨fun h => ?_, fun h => ?_⟩
  · -- a symmetry `j` of the family is a finite symmetry: unpack the index
    filter_upwards [h] with θ ⟨U, hU, hUV⟩
    refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
    obtain ⟨q, K, K', G, hθ''⟩ := hUV θ' hθ' heq
    exact ⟨q, K, K', G, hθ''⟩
  · -- a finite symmetry is a symmetry `j` of the family: pack the index
    filter_upwards [h] with θ ⟨U, hU, hUV⟩
    refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
    obtain ⟨q, K, K', G, hθ''⟩ := hUV θ' hθ' heq
    exact ⟨q, K, K', G, hθ''⟩

/-- **Proposition 4.5 of the skips paper, for residual networks of attention blocks, under
pre-RMSNorm with `ε > 0`, with the permutations of the heads:** `fd = P − d(d−1)/2 − s` at almost
every parameter (`s = 2 ∑ H d_h²`) if and only if at almost every parameter `θ` every `θ'` near `θ`
with the same function is `θ` after a permutation of the heads of every block, changes of basis
inside the heads and a change of basis by one orthogonal `Q` at all hidden states. -/
theorem ae_funDim_attention_residual_iff_ae_locally_cob_heads_rmsNorm_perm
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
        ∃ q : ∀ ℓ, Equiv.Perm (H ℓ), ∃ K K' : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ,
          ∃ Q : GL d ℝ, (Q : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ ∧
            θ' = (((θ.permHeads q).headsQK K).headsVO K').cob
              (fun _ => Q) (fun _ => Q)) := by
  have hfam := ae_funDim_attention_residual_iff_ae_locally_cob_heads_rmsNorm_family hε μ hdIn hdh
    (fun (q : (∀ ℓ, Equiv.Perm (H ℓ))) θ => θ.permHeads q) (fun _ => 1)
    permHeads_one
  refine hfam.trans ⟨fun h => ?_, fun h => ?_⟩
  · -- a symmetry `j` of the family is a finite symmetry: unpack the index
    filter_upwards [h] with θ ⟨U, hU, hUV⟩
    refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
    obtain ⟨q, K, K', Q, hQ, hθ''⟩ := hUV θ' hθ' heq
    exact ⟨q, K, K', Q, hQ, hθ''⟩
  · -- a finite symmetry is a symmetry `j` of the family: pack the index
    filter_upwards [h] with θ ⟨U, hU, hUV⟩
    refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
    obtain ⟨q, K, K', Q, hQ, hθ''⟩ := hUV θ' hθ' heq
    exact ⟨q, K, K', Q, hQ, hθ''⟩

/-- **Proposition 4.5 of the skips paper, for residual networks of attention blocks and MLP blocks
with a real-analytic activation, in any order, without normalization, with the permutations of the
heads and of the hidden units:** `fd = P − d² − s` at almost every parameter (`s = 2 ∑ H d_h²`) if
and only if at almost every parameter `θ` every `θ'` near `θ` with the same function is `θ` after a
permutation of the heads and a permutation of the hidden units of every block, changes of basis
inside the heads and a change of basis by one invertible `G` at all hidden states. -/
theorem ae_funDim_attentionMlp_residual_iff_ae_locally_cob_heads_perm
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
        ∃ (q : ∀ ℓ, Equiv.Perm (H ℓ)) (p : ∀ ℓ, Equiv.Perm (hid ℓ)), ∃ K K' : ∀ ℓ, H ℓ → GL (dh ℓ)
            ℝ,
          ∃ G : GL d ℝ,
            θ' = (Params.sumOf (((θ.sumFst.permHeads q).headsQK K).headsVO K') (θ.sumSnd.permUnits
                p)).cob
              (fun _ => G) (fun _ => G)) := by
  have hfam := ae_funDim_attentionMlp_residual_iff_ae_locally_cob_heads_family hσ μ hdIn hdh
    (fun (qp : (∀ ℓ, Equiv.Perm (H ℓ)) × (∀ ℓ, Equiv.Perm (hid ℓ))) θ =>
      Params.sumOf (θ.sumFst.permHeads qp.1) (θ.sumSnd.permUnits qp.2)) (fun _ => 1, fun _ => 1)
    (fun θ => by
      show Params.sumOf (θ.sumFst.permHeads fun _ => 1) (θ.sumSnd.permUnits fun _ => 1) = θ
      rw [permHeads_one, permUnits_one, Params.sumOf_sumFst_sumSnd])
  refine hfam.trans ⟨fun h => ?_, fun h => ?_⟩
  · -- a symmetry `j` of the family is a finite symmetry: unpack the index
    filter_upwards [h] with θ ⟨U, hU, hUV⟩
    refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
    obtain ⟨⟨q, p⟩, K, K', G, hθ''⟩ := hUV θ' hθ' heq
    exact ⟨q, p, K, K', G, hθ''⟩
  · -- a finite symmetry is a symmetry `j` of the family: pack the index
    filter_upwards [h] with θ ⟨U, hU, hUV⟩
    refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
    obtain ⟨q, p, K, K', G, hθ''⟩ := hUV θ' hθ' heq
    exact ⟨(q, p), K, K', G, hθ''⟩

/-- **Proposition 4.5 of the skips paper, for residual networks of attention blocks and MLP blocks
with a real-analytic activation, in any order, without normalization, with the permutations of the
heads and of the hidden units and the sign flips of the hidden units (the finite symmetries for an
odd activation: tanh; for an activation that is not odd, such as GELU, the images under the sign
flips are not symmetric, and the paper's form is the one with the permutations alone):** `fd = P −
d² − s` at almost every parameter (`s = 2 ∑ H d_h²`) if and only if at almost every parameter `θ`
every `θ'` near `θ` with the same function is `θ` after a permutation of the heads, a permutation of
the hidden units of every block, sign flips of hidden units, changes of basis inside the heads and a
change of basis by one invertible `G` at all hidden states. -/
theorem ae_funDim_attentionMlp_residual_iff_ae_locally_cob_heads_perm_flip
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
        ∃ (q : ∀ ℓ, Equiv.Perm (H ℓ)) (p : ∀ ℓ, Equiv.Perm (hid ℓ)) (s : ∀ ℓ, hid ℓ → ℤˣ), ∃ K K'
            : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ,
          ∃ G : GL d ℝ,
            θ' = (Params.sumOf (((θ.sumFst.permHeads q).headsQK K).headsVO K')
                ((θ.sumSnd.permUnits p).flipUnits s)).cob
              (fun _ => G) (fun _ => G)) := by
  have hfam := ae_funDim_attentionMlp_residual_iff_ae_locally_cob_heads_family hσ μ hdIn hdh
    (fun (qps : (∀ ℓ, Equiv.Perm (H ℓ)) × (∀ ℓ, Equiv.Perm (hid ℓ)) × (∀ ℓ, hid ℓ → ℤˣ)) θ =>
      Params.sumOf (θ.sumFst.permHeads qps.1) ((θ.sumSnd.permUnits qps.2.1).flipUnits qps.2.2))
    (fun _ => 1, fun _ => 1, fun _ _ => 1)
    (fun θ => by
      show Params.sumOf (θ.sumFst.permHeads fun _ => 1)
        ((θ.sumSnd.permUnits fun _ => 1).flipUnits fun _ _ => 1) = θ
      rw [permHeads_one, permUnits_one, flipUnits_one, Params.sumOf_sumFst_sumSnd])
  refine hfam.trans ⟨fun h => ?_, fun h => ?_⟩
  · -- a symmetry `j` of the family is a finite symmetry: unpack the index
    filter_upwards [h] with θ ⟨U, hU, hUV⟩
    refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
    obtain ⟨⟨q, p, s⟩, K, K', G, hθ''⟩ := hUV θ' hθ' heq
    exact ⟨q, p, s, K, K', G, hθ''⟩
  · -- a finite symmetry is a symmetry `j` of the family: pack the index
    filter_upwards [h] with θ ⟨U, hU, hUV⟩
    refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
    obtain ⟨q, p, s, K, K', G, hθ''⟩ := hUV θ' hθ' heq
    exact ⟨(q, p, s), K, K', G, hθ''⟩

/-- **Proposition 4.5 of the skips paper, for residual networks of attention blocks and MLP blocks
with a real-analytic activation, in any order, under pre-RMSNorm with `ε > 0`, with the permutations
of the heads and of the hidden units:** `fd = P − d(d−1)/2 − s` at almost every parameter (`s = 2 ∑
H d_h²`) if and only if at almost every parameter `θ` every `θ'` near `θ` with the same function is
`θ` after a permutation of the heads and a permutation of the hidden units of every block, changes
of basis inside the heads and a change of basis by one orthogonal `Q` at all hidden states. -/
theorem ae_funDim_attentionMlp_residual_iff_ae_locally_cob_heads_rmsNorm_perm
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
        ∃ (q : ∀ ℓ, Equiv.Perm (H ℓ)) (p : ∀ ℓ, Equiv.Perm (hid ℓ)), ∃ K K' : ∀ ℓ, H ℓ → GL (dh ℓ)
            ℝ,
          ∃ Q : GL d ℝ, (Q : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ ∧
            θ' = (Params.sumOf (((θ.sumFst.permHeads q).headsQK K).headsVO K') (θ.sumSnd.permUnits
                p)).cob
              (fun _ => Q) (fun _ => Q)) := by
  have hfam := ae_funDim_attentionMlp_residual_iff_ae_locally_cob_heads_rmsNorm_family hε hσ μ hdIn
    hdh
    (fun (qp : (∀ ℓ, Equiv.Perm (H ℓ)) × (∀ ℓ, Equiv.Perm (hid ℓ))) θ =>
      Params.sumOf (θ.sumFst.permHeads qp.1) (θ.sumSnd.permUnits qp.2)) (fun _ => 1, fun _ => 1)
    (fun θ => by
      show Params.sumOf (θ.sumFst.permHeads fun _ => 1) (θ.sumSnd.permUnits fun _ => 1) = θ
      rw [permHeads_one, permUnits_one, Params.sumOf_sumFst_sumSnd])
  refine hfam.trans ⟨fun h => ?_, fun h => ?_⟩
  · -- a symmetry `j` of the family is a finite symmetry: unpack the index
    filter_upwards [h] with θ ⟨U, hU, hUV⟩
    refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
    obtain ⟨⟨q, p⟩, K, K', Q, hQ, hθ''⟩ := hUV θ' hθ' heq
    exact ⟨q, p, K, K', Q, hQ, hθ''⟩
  · -- a finite symmetry is a symmetry `j` of the family: pack the index
    filter_upwards [h] with θ ⟨U, hU, hUV⟩
    refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
    obtain ⟨q, p, K, K', Q, hQ, hθ''⟩ := hUV θ' hθ' heq
    exact ⟨(q, p), K, K', Q, hQ, hθ''⟩

/-- **Proposition 4.5 of the skips paper, for residual networks of attention blocks and MLP blocks
with a real-analytic activation, in any order, under pre-RMSNorm with `ε > 0`, with the permutations
of the heads and of the hidden units and the sign flips of the hidden units (the finite symmetries
for an odd activation: tanh; for an activation that is not odd, such as GELU, the images under the
sign flips are not symmetric, and the paper's form is the one with the permutations alone):** `fd =
P − d(d−1)/2 − s` at almost every parameter (`s = 2 ∑ H d_h²`) if and only if at almost every
parameter `θ` every `θ'` near `θ` with the same function is `θ` after a permutation of the heads, a
permutation of the hidden units of every block, sign flips of hidden units, changes of basis inside
the heads and a change of basis by one orthogonal `Q` at all hidden states. -/
theorem ae_funDim_attentionMlp_residual_iff_ae_locally_cob_heads_rmsNorm_perm_flip
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
        ∃ (q : ∀ ℓ, Equiv.Perm (H ℓ)) (p : ∀ ℓ, Equiv.Perm (hid ℓ)) (s : ∀ ℓ, hid ℓ → ℤˣ), ∃ K K'
            : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ,
          ∃ Q : GL d ℝ, (Q : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ ∧
            θ' = (Params.sumOf (((θ.sumFst.permHeads q).headsQK K).headsVO K')
                ((θ.sumSnd.permUnits p).flipUnits s)).cob
              (fun _ => Q) (fun _ => Q)) := by
  have hfam := ae_funDim_attentionMlp_residual_iff_ae_locally_cob_heads_rmsNorm_family hε hσ μ hdIn
    hdh
    (fun (qps : (∀ ℓ, Equiv.Perm (H ℓ)) × (∀ ℓ, Equiv.Perm (hid ℓ)) × (∀ ℓ, hid ℓ → ℤˣ)) θ =>
      Params.sumOf (θ.sumFst.permHeads qps.1) ((θ.sumSnd.permUnits qps.2.1).flipUnits qps.2.2))
    (fun _ => 1, fun _ => 1, fun _ _ => 1)
    (fun θ => by
      show Params.sumOf (θ.sumFst.permHeads fun _ => 1)
        ((θ.sumSnd.permUnits fun _ => 1).flipUnits fun _ _ => 1) = θ
      rw [permHeads_one, permUnits_one, flipUnits_one, Params.sumOf_sumFst_sumSnd])
  refine hfam.trans ⟨fun h => ?_, fun h => ?_⟩
  · -- a symmetry `j` of the family is a finite symmetry: unpack the index
    filter_upwards [h] with θ ⟨U, hU, hUV⟩
    refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
    obtain ⟨⟨q, p, s⟩, K, K', Q, hQ, hθ''⟩ := hUV θ' hθ' heq
    exact ⟨q, p, s, K, K', Q, hQ, hθ''⟩
  · -- a finite symmetry is a symmetry `j` of the family: pack the index
    filter_upwards [h] with θ ⟨U, hU, hUV⟩
    refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
    obtain ⟨q, p, s, K, K', Q, hQ, hθ''⟩ := hUV θ' hθ' heq
    exact ⟨(q, p, s), K, K', Q, hQ, hθ''⟩

/-- **Proposition 4.5 of the skips paper, for residual networks of attention blocks and gated blocks
with a real-analytic gate, in any order, without normalization, with the permutations of the heads
and of the hidden units:** `fd = P − d² − s` at almost every parameter (`s = 2 ∑ H d_h² + ∑
d_hidden`) if and only if at almost every parameter `θ` every `θ'` near `θ` with the same function
is `θ` after a permutation of the heads and a permutation of the hidden units of every block,
changes of basis inside the heads, a rescaling of the values of the hidden units by nonzero factors
`c` and a change of basis by one invertible `G` at all hidden states. -/
theorem ae_funDim_attentionGated_residual_iff_ae_locally_cob_heads_rescale_perm
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
        ∃ (q : ∀ ℓ, Equiv.Perm (H ℓ)) (p : ∀ ℓ, Equiv.Perm (hid ℓ)), ∃ (K K' : ∀ ℓ, H ℓ → GL (dh
            ℓ) ℝ) (c : ∀ ℓ, hid ℓ → ℝ), (∀ ℓ i, c ℓ i ≠ 0) ∧
          ∃ G : GL d ℝ,
            θ' = (Params.sumOf (((θ.sumFst.permHeads q).headsQK K).headsVO K')
                ((θ.sumSnd.permUnitsGated p).rescale c)).cob
              (fun _ => G) (fun _ => G)) := by
  have hfam := ae_funDim_attentionGated_residual_iff_ae_locally_cob_heads_rescale_family hσ μ
    hdIn hdh
    (fun (qp : (∀ ℓ, Equiv.Perm (H ℓ)) × (∀ ℓ, Equiv.Perm (hid ℓ))) θ =>
      Params.sumOf (θ.sumFst.permHeads qp.1) (θ.sumSnd.permUnitsGated qp.2))
    (fun _ => 1, fun _ => 1)
    (fun θ => by
      show Params.sumOf (θ.sumFst.permHeads fun _ => 1)
        (θ.sumSnd.permUnitsGated fun _ => 1) = θ
      rw [permHeads_one, permUnitsGated_one, Params.sumOf_sumFst_sumSnd])
  refine hfam.trans ⟨fun h => ?_, fun h => ?_⟩
  · -- a symmetry `j` of the family is a finite symmetry: unpack the index
    filter_upwards [h] with θ ⟨U, hU, hUV⟩
    refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
    obtain ⟨⟨q, p⟩, K, K', c, hc, G, hθ''⟩ := hUV θ' hθ' heq
    exact ⟨q, p, K, K', c, hc, G, hθ''⟩
  · -- a finite symmetry is a symmetry `j` of the family: pack the index
    filter_upwards [h] with θ ⟨U, hU, hUV⟩
    refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
    obtain ⟨q, p, K, K', c, hc, G, hθ''⟩ := hUV θ' hθ' heq
    exact ⟨(q, p), K, K', c, hc, G, hθ''⟩

/-- **Proposition 4.5 of the skips paper, for residual networks of attention blocks and gated blocks
with a real-analytic gate, in any order, under pre-RMSNorm with `ε > 0`, with the permutations of
the heads and of the hidden units:** `fd = P − d(d−1)/2 − s` at almost every parameter (`s = 2 ∑ H
d_h² + ∑ d_hidden`) if and only if at almost every parameter `θ` every `θ'` near `θ` with the same
function is `θ` after a permutation of the heads and a permutation of the hidden units of every
block, changes of basis inside the heads, a rescaling of the values of the hidden units by nonzero
factors `c` and a change of basis by one orthogonal `Q` at all hidden states. -/
theorem ae_funDim_attentionGated_residual_iff_ae_locally_cob_heads_rescale_rmsNorm_perm
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
        ∃ (q : ∀ ℓ, Equiv.Perm (H ℓ)) (p : ∀ ℓ, Equiv.Perm (hid ℓ)), ∃ (K K' : ∀ ℓ, H ℓ → GL (dh
            ℓ) ℝ) (c : ∀ ℓ, hid ℓ → ℝ), (∀ ℓ i, c ℓ i ≠ 0) ∧
          ∃ Q : GL d ℝ, (Q : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ ∧
            θ' = (Params.sumOf (((θ.sumFst.permHeads q).headsQK K).headsVO K')
                ((θ.sumSnd.permUnitsGated p).rescale c)).cob
              (fun _ => Q) (fun _ => Q)) := by
  have hfam := ae_funDim_attentionGated_residual_iff_ae_locally_cob_heads_rescale_rmsNorm_family
    hε hσ μ hdIn hdh
    (fun (qp : (∀ ℓ, Equiv.Perm (H ℓ)) × (∀ ℓ, Equiv.Perm (hid ℓ))) θ =>
      Params.sumOf (θ.sumFst.permHeads qp.1) (θ.sumSnd.permUnitsGated qp.2))
    (fun _ => 1, fun _ => 1)
    (fun θ => by
      show Params.sumOf (θ.sumFst.permHeads fun _ => 1)
        (θ.sumSnd.permUnitsGated fun _ => 1) = θ
      rw [permHeads_one, permUnitsGated_one, Params.sumOf_sumFst_sumSnd])
  refine hfam.trans ⟨fun h => ?_, fun h => ?_⟩
  · -- a symmetry `j` of the family is a finite symmetry: unpack the index
    filter_upwards [h] with θ ⟨U, hU, hUV⟩
    refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
    obtain ⟨⟨q, p⟩, K, K', c, hc, Q, hQ, hθ''⟩ := hUV θ' hθ' heq
    exact ⟨q, p, K, K', c, hc, Q, hQ, hθ''⟩
  · -- a finite symmetry is a symmetry `j` of the family: pack the index
    filter_upwards [h] with θ ⟨U, hU, hUV⟩
    refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
    obtain ⟨q, p, K, K', c, hc, Q, hQ, hθ''⟩ := hUV θ' hθ' heq
    exact ⟨(q, p), K, K', c, hc, Q, hQ, hθ''⟩

end Skips
