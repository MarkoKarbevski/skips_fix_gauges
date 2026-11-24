import SkipsLean.Dimension.IdentifiableIffTransformerFamily
import SkipsLean.Symmetry.FiniteSymmetries

/-!
# The equality condition is local identifiability up to all the symmetries: skipless networks of
    attention blocks and MLP or gated blocks

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
(`Dimension/IdentifiableIffTransformerFamily.lean`) in which the maps `img j` are the finite
symmetries; the identity is the trivial permutation with the signs `1`.
-/

namespace Skips

open Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {sees : T → T → Prop} [DecidableRel sees]
variable {H dh hid : Fin L → Type} [∀ ℓ, Fintype (H ℓ)] [∀ ℓ, Fintype (dh ℓ)]
  [∀ ℓ, DecidableEq (dh ℓ)] [∀ ℓ, Fintype (hid ℓ)] {σ σ' : ℝ → ℝ} {ε : ℝ}

/-- **Proposition 4.5 of the skips paper, for skipless networks of attention blocks and MLP blocks
with a real-analytic activation, in any order, without normalization, with the permutations of the
heads and of the hidden units:** `fd = P − (L + 1) d² − s` at almost every parameter (`s = 2 ∑ H
d_h²`) if and only if at almost every parameter `θ` every `θ'` near `θ` with the same function is
`θ` after a permutation of the heads and a permutation of the hidden units of every block, changes
of basis inside the heads and a change of basis by invertible `G_0, …, G_L`. -/
theorem ae_funDim_attentionMlp_skipless_iff_ae_locally_cob_heads_perm
    (hσ : AnalyticOnNhd ℝ σ Set.univ)
    (μ : Measure (Params
      (Arch.attentionMlp (T := T) (d := d) sees σ id H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d)
    (hW : ∀ ℓ,
      Fintype.card d ≤ Fintype.card (H ℓ) * Fintype.card (dh ℓ) + Fintype.card (hid ℓ)) :
    (∀ᵐ θ ∂μ, funDim (Arch.attentionMlp sees σ id H dh hid) 0 θ
        + ((L + 1) * Fintype.card d ^ 2
          + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
      = Module.finrank ℝ (Params
          (Arch.attentionMlp (T := T) (d := d) sees σ id H dh hid) dIn dOut)) ↔
    (∀ᵐ θ ∂μ, ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.attentionMlp sees σ id H dh hid) 0 θ' x
        = eval (Arch.attentionMlp sees σ id H dh hid) 0 θ x) →
        ∃ (q : ∀ ℓ, Equiv.Perm (H ℓ)) (p : ∀ ℓ, Equiv.Perm (hid ℓ)), ∃ K K' : ∀ ℓ, H ℓ → GL (dh ℓ)
            ℝ,
          ∃ G : Fin (L + 1) → GL d ℝ,
            θ' = (Params.sumOf (((θ.sumFst.permHeads q).headsQK K).headsVO K') (θ.sumSnd.permUnits
                p)).cob G G) := by
  -- the case of the statement with countably many images: the permutations of the heads of the
  -- first part and of the hidden units of the second part, the trivial ones as the identity
  rw [ae_funDim_attentionMlp_skipless_iff_ae_locally_cob_heads_family hσ μ hdIn hdh hW
    (fun (j : (∀ ℓ, Equiv.Perm (H ℓ)) × (∀ ℓ, Equiv.Perm (hid ℓ))) θ =>
      Params.sumOf (θ.sumFst.permHeads j.1) (θ.sumSnd.permUnits j.2))
    (fun _ => 1, fun _ => 1)
    (fun θ => by rw [permHeads_one, permUnits_one, Params.sumOf_sumFst_sumSnd])]
  -- the existential over the pairs `(q, p)` is the existential over `q` and `p`
  refine eventually_congr (Eventually.of_forall fun θ => ?_)
  refine exists_congr fun U => and_congr_right fun _ =>
    forall₂_congr fun θ' _ => imp_congr_right fun _ => ?_
  exact ⟨fun ⟨⟨q, p⟩, h⟩ => ⟨q, p, h⟩, fun ⟨q, p, h⟩ => ⟨(q, p), h⟩⟩

/-- **Proposition 4.5 of the skips paper, for skipless networks of attention blocks and MLP blocks
with a real-analytic activation, in any order, without normalization, with the permutations of the
heads and of the hidden units and the sign flips of the hidden units (the finite symmetries for an
odd activation: tanh; for an activation that is not odd, such as GELU, the images under the sign
flips are not symmetric, and the paper's form is the one with the permutations alone):** `fd = P −
(L + 1) d² − s` at almost every parameter (`s = 2 ∑ H d_h²`) if and only if at almost every
parameter `θ` every `θ'` near `θ` with the same function is `θ` after a permutation of the heads, a
permutation of the hidden units of every block, sign flips of hidden units, changes of basis inside
the heads and a change of basis by invertible `G_0, …, G_L`. -/
theorem ae_funDim_attentionMlp_skipless_iff_ae_locally_cob_heads_perm_flip
    (hσ : AnalyticOnNhd ℝ σ Set.univ)
    (μ : Measure (Params
      (Arch.attentionMlp (T := T) (d := d) sees σ id H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d)
    (hW : ∀ ℓ,
      Fintype.card d ≤ Fintype.card (H ℓ) * Fintype.card (dh ℓ) + Fintype.card (hid ℓ)) :
    (∀ᵐ θ ∂μ, funDim (Arch.attentionMlp sees σ id H dh hid) 0 θ
        + ((L + 1) * Fintype.card d ^ 2
          + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
      = Module.finrank ℝ (Params
          (Arch.attentionMlp (T := T) (d := d) sees σ id H dh hid) dIn dOut)) ↔
    (∀ᵐ θ ∂μ, ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.attentionMlp sees σ id H dh hid) 0 θ' x
        = eval (Arch.attentionMlp sees σ id H dh hid) 0 θ x) →
        ∃ (q : ∀ ℓ, Equiv.Perm (H ℓ)) (p : ∀ ℓ, Equiv.Perm (hid ℓ)) (s : ∀ ℓ, hid ℓ → ℤˣ), ∃ K K'
            : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ,
          ∃ G : Fin (L + 1) → GL d ℝ,
            θ' = (Params.sumOf (((θ.sumFst.permHeads q).headsQK K).headsVO K')
                ((θ.sumSnd.permUnits p).flipUnits s)).cob G G) := by
  -- the case of the statement with countably many images: the permutations of the heads of the
  -- first part, the permutations and the sign flips of the hidden units of the second part, the
  -- trivial ones as the identity
  rw [ae_funDim_attentionMlp_skipless_iff_ae_locally_cob_heads_family hσ μ hdIn hdh hW
    (fun (j : (∀ ℓ, Equiv.Perm (H ℓ)) × (∀ ℓ, Equiv.Perm (hid ℓ)) × (∀ ℓ, hid ℓ → ℤˣ)) θ =>
      Params.sumOf (θ.sumFst.permHeads j.1) ((θ.sumSnd.permUnits j.2.1).flipUnits j.2.2))
    (fun _ => 1, fun _ => 1, fun _ _ => 1)
    (fun θ => by rw [permHeads_one, permUnits_one, flipUnits_one, Params.sumOf_sumFst_sumSnd])]
  -- the existential over the triples `(q, p, s)` is the existential over `q`, `p` and `s`
  refine eventually_congr (Eventually.of_forall fun θ => ?_)
  refine exists_congr fun U => and_congr_right fun _ =>
    forall₂_congr fun θ' _ => imp_congr_right fun _ => ?_
  exact ⟨fun ⟨⟨q, p, s⟩, h⟩ => ⟨q, p, s, h⟩, fun ⟨q, p, s, h⟩ => ⟨(q, p, s), h⟩⟩

/-- **Proposition 4.5 of the skips paper, for skipless networks of attention blocks and MLP blocks
with a real-analytic activation, in any order, under pre-RMSNorm with `ε > 0`, with the permutations
of the heads and of the hidden units:** `fd = P − (L + 1) d(d−1)/2 − s` at almost every parameter
(`s = 2 ∑ H d_h²`) if and only if at almost every parameter `θ` every `θ'` near `θ` with the same
function is `θ` after a permutation of the heads and a permutation of the hidden units of every
block, changes of basis inside the heads and a change of basis by orthogonal `Q_0, …, Q_L`. -/
theorem ae_funDim_attentionMlp_skipless_iff_ae_locally_cob_heads_rmsNorm_perm
    (hε : 0 < ε) (hσ : AnalyticOnNhd ℝ σ Set.univ)
    (μ : Measure (Params
      (Arch.attentionMlp (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d)
    (hW : ∀ ℓ,
      Fintype.card d ≤ Fintype.card (H ℓ) * Fintype.card (dh ℓ) + Fintype.card (hid ℓ)) :
    (∀ᵐ θ ∂μ, funDim (Arch.attentionMlp sees σ (rmsNorm ε) H dh hid) 0 θ
        + ((L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2)
          + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
      = Module.finrank ℝ (Params
          (Arch.attentionMlp (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut)) ↔
    (∀ᵐ θ ∂μ, ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.attentionMlp sees σ (rmsNorm ε) H dh hid) 0 θ' x
        = eval (Arch.attentionMlp sees σ (rmsNorm ε) H dh hid) 0 θ x) →
        ∃ (q : ∀ ℓ, Equiv.Perm (H ℓ)) (p : ∀ ℓ, Equiv.Perm (hid ℓ)), ∃ K K' : ∀ ℓ, H ℓ → GL (dh ℓ)
            ℝ,
          ∃ Q : Fin (L + 1) → GL d ℝ,
            (∀ ℓ, (Q ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ) ∧
            θ' = (Params.sumOf (((θ.sumFst.permHeads q).headsQK K).headsVO K') (θ.sumSnd.permUnits
                p)).cob Q Q) := by
  -- the case of the statement with countably many images: the permutations of the heads of the
  -- first part and of the hidden units of the second part, the trivial ones as the identity
  rw [ae_funDim_attentionMlp_skipless_iff_ae_locally_cob_heads_rmsNorm_family hε hσ μ hdIn hdh hW
    (fun (j : (∀ ℓ, Equiv.Perm (H ℓ)) × (∀ ℓ, Equiv.Perm (hid ℓ))) θ =>
      Params.sumOf (θ.sumFst.permHeads j.1) (θ.sumSnd.permUnits j.2))
    (fun _ => 1, fun _ => 1)
    (fun θ => by rw [permHeads_one, permUnits_one, Params.sumOf_sumFst_sumSnd])]
  -- the existential over the pairs `(q, p)` is the existential over `q` and `p`
  refine eventually_congr (Eventually.of_forall fun θ => ?_)
  refine exists_congr fun U => and_congr_right fun _ =>
    forall₂_congr fun θ' _ => imp_congr_right fun _ => ?_
  exact ⟨fun ⟨⟨q, p⟩, h⟩ => ⟨q, p, h⟩, fun ⟨q, p, h⟩ => ⟨(q, p), h⟩⟩

/-- **Proposition 4.5 of the skips paper, for skipless networks of attention blocks and MLP blocks
with a real-analytic activation, in any order, under pre-RMSNorm with `ε > 0`, with the permutations
of the heads and of the hidden units and the sign flips of the hidden units (the finite symmetries
for an odd activation: tanh; for an activation that is not odd, such as GELU, the images under the
sign flips are not symmetric, and the paper's form is the one with the permutations alone):** `fd =
P − (L + 1) d(d−1)/2 − s` at almost every parameter (`s = 2 ∑ H d_h²`) if and only if at almost
every parameter `θ` every `θ'` near `θ` with the same function is `θ` after a permutation of the
heads, a permutation of the hidden units of every block, sign flips of hidden units, changes of
basis inside the heads and a change of basis by orthogonal `Q_0, …, Q_L`. -/
theorem ae_funDim_attentionMlp_skipless_iff_ae_locally_cob_heads_rmsNorm_perm_flip
    (hε : 0 < ε) (hσ : AnalyticOnNhd ℝ σ Set.univ)
    (μ : Measure (Params
      (Arch.attentionMlp (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d)
    (hW : ∀ ℓ,
      Fintype.card d ≤ Fintype.card (H ℓ) * Fintype.card (dh ℓ) + Fintype.card (hid ℓ)) :
    (∀ᵐ θ ∂μ, funDim (Arch.attentionMlp sees σ (rmsNorm ε) H dh hid) 0 θ
        + ((L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2)
          + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
      = Module.finrank ℝ (Params
          (Arch.attentionMlp (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut)) ↔
    (∀ᵐ θ ∂μ, ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.attentionMlp sees σ (rmsNorm ε) H dh hid) 0 θ' x
        = eval (Arch.attentionMlp sees σ (rmsNorm ε) H dh hid) 0 θ x) →
        ∃ (q : ∀ ℓ, Equiv.Perm (H ℓ)) (p : ∀ ℓ, Equiv.Perm (hid ℓ)) (s : ∀ ℓ, hid ℓ → ℤˣ), ∃ K K'
            : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ,
          ∃ Q : Fin (L + 1) → GL d ℝ,
            (∀ ℓ, (Q ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ) ∧
            θ' = (Params.sumOf (((θ.sumFst.permHeads q).headsQK K).headsVO K')
                ((θ.sumSnd.permUnits p).flipUnits s)).cob Q Q) := by
  -- the case of the statement with countably many images: the permutations of the heads of the
  -- first part, the permutations and the sign flips of the hidden units of the second part, the
  -- trivial ones as the identity
  rw [ae_funDim_attentionMlp_skipless_iff_ae_locally_cob_heads_rmsNorm_family hε hσ μ hdIn hdh hW
    (fun (j : (∀ ℓ, Equiv.Perm (H ℓ)) × (∀ ℓ, Equiv.Perm (hid ℓ)) × (∀ ℓ, hid ℓ → ℤˣ)) θ =>
      Params.sumOf (θ.sumFst.permHeads j.1) ((θ.sumSnd.permUnits j.2.1).flipUnits j.2.2))
    (fun _ => 1, fun _ => 1, fun _ _ => 1)
    (fun θ => by rw [permHeads_one, permUnits_one, flipUnits_one, Params.sumOf_sumFst_sumSnd])]
  -- the existential over the triples `(q, p, s)` is the existential over `q`, `p` and `s`
  refine eventually_congr (Eventually.of_forall fun θ => ?_)
  refine exists_congr fun U => and_congr_right fun _ =>
    forall₂_congr fun θ' _ => imp_congr_right fun _ => ?_
  exact ⟨fun ⟨⟨q, p, s⟩, h⟩ => ⟨q, p, s, h⟩, fun ⟨q, p, s, h⟩ => ⟨(q, p, s), h⟩⟩

/-- **Proposition 4.5 of the skips paper, for skipless networks of attention blocks and gated blocks
with a real-analytic gate, in any order, without normalization, with the permutations of the heads
and of the hidden units:** `fd = P − (L + 1) d² − s` at almost every parameter (`s = 2 ∑ H d_h² + ∑
d_hidden`) if and only if at almost every parameter `θ` every `θ'` near `θ` with the same function
is `θ` after a permutation of the heads and a permutation of the hidden units of every block,
changes of basis inside the heads, a rescaling of the values of the hidden units by nonzero factors
`c` and a change of basis by invertible `G_0, …, G_L`. -/
theorem ae_funDim_attentionGated_skipless_iff_ae_locally_cob_heads_rescale_perm
    [Nonempty d] (hσ : AnalyticOnNhd ℝ σ Set.univ)
    (μ : Measure (Params
      (Arch.attentionGated (T := T) (d := d) sees σ id H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d)
    (hW : ∀ ℓ,
      Fintype.card d ≤ Fintype.card (H ℓ) * Fintype.card (dh ℓ) + Fintype.card (hid ℓ)) :
    (∀ᵐ θ ∂μ, funDim (Arch.attentionGated sees σ id H dh hid) 0 θ
        + ((L + 1) * Fintype.card d ^ 2
          + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
            + ∑ ℓ, Fintype.card (hid ℓ)))
      = Module.finrank ℝ (Params
          (Arch.attentionGated (T := T) (d := d) sees σ id H dh hid) dIn dOut)) ↔
    (∀ᵐ θ ∂μ, ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.attentionGated sees σ id H dh hid) 0 θ' x
        = eval (Arch.attentionGated sees σ id H dh hid) 0 θ x) →
        ∃ (q : ∀ ℓ, Equiv.Perm (H ℓ)) (p : ∀ ℓ, Equiv.Perm (hid ℓ)), ∃ (K K' : ∀ ℓ, H ℓ → GL (dh
            ℓ) ℝ) (c : ∀ ℓ, hid ℓ → ℝ), (∀ ℓ i, c ℓ i ≠ 0) ∧
          ∃ G : Fin (L + 1) → GL d ℝ,
            θ' = (Params.sumOf (((θ.sumFst.permHeads q).headsQK K).headsVO K')
                ((θ.sumSnd.permUnitsGated p).rescale c)).cob G G) := by
  -- the case of the statement with countably many images: the permutations of the heads of the
  -- first part and of the hidden units of the second part, the trivial ones as the identity
  rw [ae_funDim_attentionGated_skipless_iff_ae_locally_cob_heads_rescale_family hσ μ hdIn hdh hW
    (fun (j : (∀ ℓ, Equiv.Perm (H ℓ)) × (∀ ℓ, Equiv.Perm (hid ℓ))) θ =>
      Params.sumOf (θ.sumFst.permHeads j.1) (θ.sumSnd.permUnitsGated j.2))
    (fun _ => 1, fun _ => 1)
    (fun θ => by rw [permHeads_one, permUnitsGated_one, Params.sumOf_sumFst_sumSnd])]
  -- the existential over the pairs `(q, p)` is the existential over `q` and `p`
  refine eventually_congr (Eventually.of_forall fun θ => ?_)
  refine exists_congr fun U => and_congr_right fun _ =>
    forall₂_congr fun θ' _ => imp_congr_right fun _ => ?_
  exact ⟨fun ⟨⟨q, p⟩, h⟩ => ⟨q, p, h⟩, fun ⟨q, p, h⟩ => ⟨(q, p), h⟩⟩

/-- **Proposition 4.5 of the skips paper, for skipless networks of attention blocks and gated blocks
with a real-analytic gate, in any order, under pre-RMSNorm with `ε > 0`, with the permutations of
the heads and of the hidden units:** `fd = P − (L + 1) d(d−1)/2 − s` at almost every parameter (`s =
2 ∑ H d_h² + ∑ d_hidden`) if and only if at almost every parameter `θ` every `θ'` near `θ` with the
same function is `θ` after a permutation of the heads and a permutation of the hidden units of every
block, changes of basis inside the heads, a rescaling of the values of the hidden units by nonzero
factors `c` and a change of basis by orthogonal `Q_0, …, Q_L`. -/
theorem ae_funDim_attentionGated_skipless_iff_ae_locally_cob_heads_rescale_rmsNorm_perm
    (hε : 0 < ε) [Nonempty d] (hσ : AnalyticOnNhd ℝ σ Set.univ)
    (μ : Measure (Params
      (Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d)
    (hW : ∀ ℓ,
      Fintype.card d ≤ Fintype.card (H ℓ) * Fintype.card (dh ℓ) + Fintype.card (hid ℓ)) :
    (∀ᵐ θ ∂μ, funDim (Arch.attentionGated sees σ (rmsNorm ε) H dh hid) 0 θ
        + ((L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2)
          + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
            + ∑ ℓ, Fintype.card (hid ℓ)))
      = Module.finrank ℝ (Params
          (Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut)) ↔
    (∀ᵐ θ ∂μ, ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.attentionGated sees σ (rmsNorm ε) H dh hid) 0 θ' x
        = eval (Arch.attentionGated sees σ (rmsNorm ε) H dh hid) 0 θ x) →
        ∃ (q : ∀ ℓ, Equiv.Perm (H ℓ)) (p : ∀ ℓ, Equiv.Perm (hid ℓ)), ∃ (K K' : ∀ ℓ, H ℓ → GL (dh
            ℓ) ℝ) (c : ∀ ℓ, hid ℓ → ℝ), (∀ ℓ i, c ℓ i ≠ 0) ∧
          ∃ Q : Fin (L + 1) → GL d ℝ,
            (∀ ℓ, (Q ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ) ∧
            θ' = (Params.sumOf (((θ.sumFst.permHeads q).headsQK K).headsVO K')
                ((θ.sumSnd.permUnitsGated p).rescale c)).cob Q Q) := by
  -- the case of the statement with countably many images: the permutations of the heads of the
  -- first part and of the hidden units of the second part, the trivial ones as the identity
  rw [ae_funDim_attentionGated_skipless_iff_ae_locally_cob_heads_rescale_rmsNorm_family hε hσ μ hdIn
    hdh hW
    (fun (j : (∀ ℓ, Equiv.Perm (H ℓ)) × (∀ ℓ, Equiv.Perm (hid ℓ))) θ =>
      Params.sumOf (θ.sumFst.permHeads j.1) (θ.sumSnd.permUnitsGated j.2))
    (fun _ => 1, fun _ => 1)
    (fun θ => by rw [permHeads_one, permUnitsGated_one, Params.sumOf_sumFst_sumSnd])]
  -- the existential over the pairs `(q, p)` is the existential over `q` and `p`
  refine eventually_congr (Eventually.of_forall fun θ => ?_)
  refine exists_congr fun U => and_congr_right fun _ =>
    forall₂_congr fun θ' _ => imp_congr_right fun _ => ?_
  exact ⟨fun ⟨⟨q, p⟩, h⟩ => ⟨q, p, h⟩, fun ⟨q, p, h⟩ => ⟨(q, p), h⟩⟩

end Skips
