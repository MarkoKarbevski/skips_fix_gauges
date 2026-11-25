import SkipsLean.Symmetry.LocallyFreeRMSZero
import SkipsLean.Symmetry.InsideBlocksSum
import SkipsLean.Network.Transformer

/-!
# Locally free action: only the identity fixes the parameters (attention with MLP blocks)

Paper (skips paper), Lemma A.18 (Locally free action): "With an embedding of rank `d_model`, it
also holds for networks with attention blocks whose heads have width `d_h ≤ d_model` and total
width `H d_h ≥ d_model`." Its proof goes block by block ("For an attention block, once
`G_{ℓ−1} = I` the changes of basis inside its heads multiply `W_{Q,i}` and `W_{V,i}` on the
right […] The write, which stacks the `W_{O,i}`, then transforms as `W_O ↦ W_O G_ℓ`"), so it
covers networks that have attention blocks and MLP blocks.

`Symmetry/LocallyFreeEmbedding.lean`, `Symmetry/LocallyFreeAttention.lean` and
`Symmetry/LocallyFreeRMSZero.lean` have the statement for the group ("changes of basis and
symmetries inside the blocks that fix `θ` are the identity") for networks of one kind of block.
Here the same for networks of attention blocks and MLP or gated blocks in any order
(`Arch.attentionMlp`, `Arch.attentionGated`: block `ℓ` has an attention part and an MLP part, and
either may be empty). The parameter is fixed when both of its parts are: `θ.sumFst`, the
attention part with `E` and `D`, under the changes of basis `G` and those inside the heads; and
`θ.sumSnd`, the MLP part with `E` and `D`, under `G` and the rescalings. The hypotheses: `E` of
rank `d`; the write of every block (the rows of the attention part above those of the MLP part)
of rank `d`; the query and value matrix of every head of rank `d_h`; no rescaled read column
zero.

* With rescalings of the hidden units (ReLU, ReLU²; with `c = 1` this is tanh and GELU), of the
  values (gated blocks), of values and gates (ReGLU), for the changes of basis `θ.cob G G`
  (no normalization; orthogonal `G` under pre-RMSNorm with `ε > 0`).
* The same for `ε = 0`: `G_ℓ = s_ℓ Q_ℓ`, `s_ℓ > 0`, `Q_ℓ` orthogonal, the writes multiplied by
  `G_ℓ` and the reads by `Q_ℓ⁻¹` (`d ≥ 1`).

Not stated: the form with the readout for these networks (the lemma has it for MLP networks).
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {sees : T → T → Prop} [DecidableRel sees]
variable {H dh hid : Fin L → Type} [∀ ℓ, Fintype (H ℓ)] [∀ ℓ, Fintype (dh ℓ)]
  [∀ ℓ, DecidableEq (dh ℓ)] [∀ ℓ, Fintype (hid ℓ)] {σ : ℝ → ℝ}
  {χ : Matrix T d ℝ → Matrix T d ℝ}

/-- **Lemma A.18, third sentence, for the group: attention blocks with MLP blocks with the
rescalings `c` of the hidden units (ReLU, ReLU²; any degree `k`).** If `E` and the write of every
block have rank `d`, the query and the value matrix of every head have rank `d_h`, no read column
of a hidden unit vanishes, and the changes of basis `G` of the hidden states with the changes of
basis `K`, `K'` inside the heads and these rescalings fix both parts of `θ`, then they are the
identity. -/
theorem cob_heads_rescaleMlp_eq_self_of_rank_E (k : ℕ)
    (θ : Params (Arch.attentionMlp (T := T) (d := d) sees σ χ H dh hid) dIn dOut)
    (G : Fin (L + 1) → GL d ℝ) (K K' : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ) (c : ∀ ℓ, hid ℓ → ℝ)
    (hE : θ.E.rank = Fintype.card d) (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d)
    (hQr : ∀ ℓ (i : H ℓ), ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k)).rank
      = Fintype.card (dh ℓ))
    (hVr : ∀ ℓ (i : H ℓ),
      ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))).rank
        = Fintype.card (dh ℓ))
    (hcol : ∀ ℓ i, (fun a => θ.sumSnd.read ℓ a i) ≠ 0)
    (h1 : ((θ.sumFst.cob G G).headsQK K).headsVO K' = θ.sumFst)
    (h2 : (θ.sumSnd.cob G G).rescaleMlp k c = θ.sumSnd) :
    G = 1 ∧ K = 1 ∧ K' = 1 ∧ ∀ ℓ i, c ℓ i = 1 := by
  sorry

/-- **Lemma A.18, third sentence, for the group: attention blocks with gated blocks with the
rescalings `c` of the values.** If `E` and the write of every block have rank `d`, the query and
the value matrix of every head have rank `d_h`, no value column of a hidden unit vanishes, and the
changes of basis `G` of the hidden states with the changes of basis `K`, `K'` inside the heads and
these rescalings fix both parts of `θ`, then they are the identity. -/
theorem cob_heads_rescale_eq_self_of_rank_E
    (θ : Params (Arch.attentionGated (T := T) (d := d) sees σ χ H dh hid) dIn dOut)
    (G : Fin (L + 1) → GL d ℝ) (K K' : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ) (c : ∀ ℓ, hid ℓ → ℝ)
    (hE : θ.E.rank = Fintype.card d) (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d)
    (hQr : ∀ ℓ (i : H ℓ), ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k)).rank
      = Fintype.card (dh ℓ))
    (hVr : ∀ ℓ (i : H ℓ),
      ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))).rank
        = Fintype.card (dh ℓ))
    (hv : ∀ ℓ i, (fun a => θ.sumSnd.read ℓ a (Sum.inr i)) ≠ 0)
    (h1 : ((θ.sumFst.cob G G).headsQK K).headsVO K' = θ.sumFst)
    (h2 : (θ.sumSnd.cob G G).rescale c = θ.sumSnd) :
    G = 1 ∧ K = 1 ∧ K' = 1 ∧ ∀ ℓ i, c ℓ i = 1 := by
  sorry

/-- **Lemma A.18, third sentence, for the group: attention blocks with ReGLU blocks with the
rescalings `c'` of the values and `c` of the gates.** If `E` and the write of every block have
rank `d`, the query and the value matrix of every head have rank `d_h`, no gate column and no
value column of a hidden unit vanishes, and the changes of basis `G` of the hidden states with the
changes of basis `K`, `K'` inside the heads and these rescalings fix both parts of `θ`, then they
are the identity. -/
theorem cob_heads_rescale_rescaleGate_eq_self_of_rank_E (k : ℕ)
    (θ : Params (Arch.attentionGated (T := T) (d := d) sees σ χ H dh hid) dIn dOut)
    (G : Fin (L + 1) → GL d ℝ) (K K' : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ) (c c' : ∀ ℓ, hid ℓ → ℝ)
    (hE : θ.E.rank = Fintype.card d) (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d)
    (hQr : ∀ ℓ (i : H ℓ), ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k)).rank
      = Fintype.card (dh ℓ))
    (hVr : ∀ ℓ (i : H ℓ),
      ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))).rank
        = Fintype.card (dh ℓ))
    (hv : ∀ ℓ i, (fun a => θ.sumSnd.read ℓ a (Sum.inr i)) ≠ 0)
    (hg : ∀ ℓ i, (fun a => θ.sumSnd.read ℓ a (Sum.inl i)) ≠ 0)
    (h1 : ((θ.sumFst.cob G G).headsQK K).headsVO K' = θ.sumFst)
    (h2 : ((θ.sumSnd.cob G G).rescale c').rescaleGate k c = θ.sumSnd) :
    G = 1 ∧ K = 1 ∧ K' = 1 ∧ (∀ ℓ i, c ℓ i = 1) ∧ ∀ ℓ i, c' ℓ i = 1 := by
  sorry

/-- **The same for `ε = 0`: attention blocks with MLP blocks with the rescalings `c` of the hidden
units (ReLU, ReLU²; any degree `k`).** Let `G_ℓ = s_ℓ Q_ℓ` with `s_ℓ > 0` and `Q_ℓ` orthogonal
(the writes are multiplied by `G_ℓ`, the reads by `Q_ℓ⁻¹`), `d ≥ 1`. Under the same conditions on
`θ`, if these changes of basis with the changes of basis inside the heads and the rescalings fix
both parts of `θ`, then `s = 1`, `Q = 1` and the symmetries inside the blocks are the identity. -/
theorem cob_rmsNorm_zero_heads_rescaleMlp_eq_self_of_rank_E [Nonempty d] (k : ℕ)
    (θ : Params (Arch.attentionMlp (T := T) (d := d) sees σ χ H dh hid) dIn dOut)
    (G Q : Fin (L + 1) → GL d ℝ) (s : Fin (L + 1) → ℝ) (K K' : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ)
    (c : ∀ ℓ, hid ℓ → ℝ) (hs : ∀ ℓ, 0 < s ℓ)
    (hQ : ∀ ℓ, (Q ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ)
    (hG : ∀ ℓ, (G ℓ : Matrix d d ℝ) = s ℓ • (Q ℓ : Matrix d d ℝ))
    (hE : θ.E.rank = Fintype.card d) (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d)
    (hQr : ∀ ℓ (i : H ℓ), ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k)).rank
      = Fintype.card (dh ℓ))
    (hVr : ∀ ℓ (i : H ℓ),
      ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))).rank
        = Fintype.card (dh ℓ))
    (hcol : ∀ ℓ i, (fun a => θ.sumSnd.read ℓ a i) ≠ 0)
    (h1 : ((θ.sumFst.cob G Q).headsQK K).headsVO K' = θ.sumFst)
    (h2 : (θ.sumSnd.cob G Q).rescaleMlp k c = θ.sumSnd) :
    (∀ ℓ, s ℓ = 1) ∧ Q = 1 ∧ K = 1 ∧ K' = 1 ∧ ∀ ℓ i, c ℓ i = 1 := by
  sorry

/-- **The same for `ε = 0`: attention blocks with gated blocks with the rescalings `c` of the
values.** Let `G_ℓ = s_ℓ Q_ℓ` with `s_ℓ > 0` and `Q_ℓ` orthogonal (the writes are multiplied by
`G_ℓ`, the reads by `Q_ℓ⁻¹`), `d ≥ 1`. Under the same conditions on `θ`, if these changes of basis
with the changes of basis inside the heads and the rescalings fix both parts of `θ`, then `s = 1`,
`Q = 1` and the symmetries inside the blocks are the identity. -/
theorem cob_rmsNorm_zero_heads_rescale_eq_self_of_rank_E [Nonempty d]
    (θ : Params (Arch.attentionGated (T := T) (d := d) sees σ χ H dh hid) dIn dOut)
    (G Q : Fin (L + 1) → GL d ℝ) (s : Fin (L + 1) → ℝ) (K K' : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ)
    (c : ∀ ℓ, hid ℓ → ℝ) (hs : ∀ ℓ, 0 < s ℓ)
    (hQ : ∀ ℓ, (Q ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ)
    (hG : ∀ ℓ, (G ℓ : Matrix d d ℝ) = s ℓ • (Q ℓ : Matrix d d ℝ))
    (hE : θ.E.rank = Fintype.card d) (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d)
    (hQr : ∀ ℓ (i : H ℓ), ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k)).rank
      = Fintype.card (dh ℓ))
    (hVr : ∀ ℓ (i : H ℓ),
      ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))).rank
        = Fintype.card (dh ℓ))
    (hv : ∀ ℓ i, (fun a => θ.sumSnd.read ℓ a (Sum.inr i)) ≠ 0)
    (h1 : ((θ.sumFst.cob G Q).headsQK K).headsVO K' = θ.sumFst)
    (h2 : (θ.sumSnd.cob G Q).rescale c = θ.sumSnd) :
    (∀ ℓ, s ℓ = 1) ∧ Q = 1 ∧ K = 1 ∧ K' = 1 ∧ ∀ ℓ i, c ℓ i = 1 := by
  sorry

/-- **The same for `ε = 0`: attention blocks with ReGLU blocks with the rescalings `c'` of the
values and `c` of the gates.** Let `G_ℓ = s_ℓ Q_ℓ` with `s_ℓ > 0` and `Q_ℓ` orthogonal (the writes
are multiplied by `G_ℓ`, the reads by `Q_ℓ⁻¹`), `d ≥ 1`. Under the same conditions on `θ`, if
these changes of basis with the changes of basis inside the heads and the rescalings fix both
parts of `θ`, then `s = 1`, `Q = 1` and the symmetries inside the blocks are the identity. -/
theorem cob_rmsNorm_zero_heads_rescale_rescaleGate_eq_self_of_rank_E [Nonempty d] (k : ℕ)
    (θ : Params (Arch.attentionGated (T := T) (d := d) sees σ χ H dh hid) dIn dOut)
    (G Q : Fin (L + 1) → GL d ℝ) (s : Fin (L + 1) → ℝ) (K K' : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ)
    (c c' : ∀ ℓ, hid ℓ → ℝ) (hs : ∀ ℓ, 0 < s ℓ)
    (hQ : ∀ ℓ, (Q ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ)
    (hG : ∀ ℓ, (G ℓ : Matrix d d ℝ) = s ℓ • (Q ℓ : Matrix d d ℝ))
    (hE : θ.E.rank = Fintype.card d) (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d)
    (hQr : ∀ ℓ (i : H ℓ), ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k)).rank
      = Fintype.card (dh ℓ))
    (hVr : ∀ ℓ (i : H ℓ),
      ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))).rank
        = Fintype.card (dh ℓ))
    (hv : ∀ ℓ i, (fun a => θ.sumSnd.read ℓ a (Sum.inr i)) ≠ 0)
    (hg : ∀ ℓ i, (fun a => θ.sumSnd.read ℓ a (Sum.inl i)) ≠ 0)
    (h1 : ((θ.sumFst.cob G Q).headsQK K).headsVO K' = θ.sumFst)
    (h2 : ((θ.sumSnd.cob G Q).rescale c').rescaleGate k c = θ.sumSnd) :
    (∀ ℓ, s ℓ = 1) ∧ Q = 1 ∧ K = 1 ∧ K' = 1 ∧ (∀ ℓ i, c ℓ i = 1) ∧ ∀ ℓ i, c' ℓ i = 1 := by
  sorry

end Skips
