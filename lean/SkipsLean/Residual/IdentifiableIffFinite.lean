import SkipsLean.Residual.IdentifiableIffFamily
import SkipsLean.Symmetry.FiniteSymmetries

/-!
# The equality condition is local identifiability up to all the symmetries: residual networks

Paper (dimension paper, Proposition 4.6; skips paper, Proposition 4.5): "A network satisfies the
equality condition if and only if, at generic parameters, it is locally identifiable up to its
symmetries." Definition 4.5 of the dimension paper (4.4 of the skips paper): "A network is
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
  sorry

/-- **Proposition 4.5 of the skips paper, for residual networks of MLP blocks with a real-analytic
activation (tanh, GELU), without normalization, with the permutations and the sign flips of the
hidden units (the finite symmetries for an odd activation: tanh):** `fd = P − d²` at almost every
parameter if and only if at almost every parameter `θ` every `θ'` near `θ` with the same function is
`θ` after a permutation of the hidden units of every block, sign flips of hidden units, a change of
basis by one invertible `G` at all hidden states. -/
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
  sorry

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
  sorry

/-- **Proposition 4.5 of the skips paper, for residual networks of MLP blocks with a real-analytic
activation (tanh, GELU), under pre-RMSNorm with `ε > 0`, with the permutations and the sign flips of
the hidden units (the finite symmetries for an odd activation: tanh):** `fd = P − d(d−1)/2` at
almost every parameter if and only if at almost every parameter `θ` every `θ'` near `θ` with the
same function is `θ` after a permutation of the hidden units of every block, sign flips of hidden
units, a change of basis by one orthogonal `Q` at all hidden states. -/
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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

/-- **Proposition 4.5 of the skips paper, for residual networks of attention blocks and MLP blocks
with a real-analytic activation, in any order, without normalization, with the permutations of the
heads and of the hidden units and the sign flips of the hidden units (the finite symmetries for an
odd activation: tanh):** `fd = P − d² − s` at almost every parameter (`s = 2 ∑ H d_h²`) if and only
if at almost every parameter `θ` every `θ'` near `θ` with the same function is `θ` after a
permutation of the heads, a permutation of the hidden units of every block, sign flips of hidden
units, changes of basis inside the heads and a change of basis by one invertible `G` at all hidden
states. -/
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
  sorry

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
  sorry

/-- **Proposition 4.5 of the skips paper, for residual networks of attention blocks and MLP blocks
with a real-analytic activation, in any order, under pre-RMSNorm with `ε > 0`, with the permutations
of the heads and of the hidden units and the sign flips of the hidden units (the finite symmetries
for an odd activation: tanh):** `fd = P − d(d−1)/2 − s` at almost every parameter (`s = 2 ∑ H d_h²`)
if and only if at almost every parameter `θ` every `θ'` near `θ` with the same function is `θ` after
a permutation of the heads, a permutation of the hidden units of every block, sign flips of hidden
units, changes of basis inside the heads and a change of basis by one orthogonal `Q` at all hidden
states. -/
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
  sorry

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
  sorry

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
  sorry

end Skips
