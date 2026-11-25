import SkipsLean.Symmetry.LocallyFreeReadout
import SkipsLean.Symmetry.LocallyFreeAttention

/-!
# Locally free action under pre-RMSNorm with `ε = 0`, with the symmetries inside blocks

Paper (skips paper), Lemma A.18 (Locally free action): "Consider an MLP network, skipless or
residual, without normalization or with pre-RMSNorm, […] and the symmetries inside blocks of
Section 4.1." Its proof: "With RMSNorm the changes of basis lie in `CO(d_model)` or
`O(d_model)`, and the argument is unchanged." (The dimension paper, Lemma B.1: "Without
normalization or under pre-RMSNorm".)

For `ε > 0` the changes of basis are the orthogonal ones among `θ.cob G G`, and the statements of
`Symmetry/LocallyFreeEmbedding.lean`, `Symmetry/LocallyFreeReadout.lean` and
`Symmetry/LocallyFreeAttention.lean` apply. For `ε = 0` the change of basis `G_ℓ = s_ℓ Q_ℓ`,
`s_ℓ > 0`, `Q_ℓ` orthogonal, multiplies the writes by `G_ℓ` and the reads by `Q_ℓ⁻¹`
(`eval_cob_rmsNorm_zero`): this is `θ.cob G Q`, and those files have it for the changes of basis
alone. Here **`ε = 0` together with the symmetries inside blocks**: if such changes of basis and
symmetries inside the blocks fix `θ`, then `s_ℓ = 1`, `Q_ℓ = 1` and the symmetries inside the
blocks are the identity.

* With the embedding (`E` and the writes of rank `d ≥ 1`): ReLU and ReLU² blocks, gated blocks,
  ReGLU blocks, attention blocks. `E G_0 = E` gives `s_0 Q_0 = 1`, so `s_0 = 1` and `Q_0 = 1`;
  then the read and the write of each block, as without normalization.
* With the readout (`D` and the reads of rank `d ≥ 1`, `E ≠ 0`, no write row zero, the rescaled
  read columns not zero): ReLU and ReLU² blocks, gated blocks, ReGLU blocks. Here a rescaled read
  column is an eigenvector of the orthogonal matrix `Q_{ℓ−1}⁻¹` with a positive eigenvalue, which
  is therefore `1`; so the read columns need not be in general position (for ReGLU blocks without
  normalization they must be: `Symmetry/LocallyFreeReadout.lean`).
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {σ : ℝ → ℝ} {χ : Matrix T d ℝ → Matrix T d ℝ} {hid : Fin L → Type}
  [∀ ℓ, Fintype (hid ℓ)]

/-- **Lemma A.18, first sentence, `ε = 0`, ReLU and ReLU² blocks.** Let `G_ℓ = s_ℓ Q_ℓ` with
`s_ℓ > 0` and `Q_ℓ` orthogonal. If `E` and every write have rank `d ≥ 1`, no column of a read
vanishes, and these changes of basis with the rescalings `c` of the hidden units fix `θ`, then
`s = 1`, `Q = 1` and `c = 1`. -/
theorem cob_rmsNorm_zero_rescaleMlp_eq_self_of_rank_E [Nonempty d] (k : ℕ)
    (θ : Params (Arch.mlp (T := T) (d := d) σ χ hid) dIn dOut) (G Q : Fin (L + 1) → GL d ℝ)
    (s : Fin (L + 1) → ℝ) (c : ∀ ℓ, hid ℓ → ℝ) (hs : ∀ ℓ, 0 < s ℓ)
    (hQ : ∀ ℓ, (Q ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ)
    (hG : ∀ ℓ, (G ℓ : Matrix d d ℝ) = s ℓ • (Q ℓ : Matrix d d ℝ))
    (hE : θ.E.rank = Fintype.card d) (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d)
    (hcol : ∀ ℓ i, (fun a => θ.read ℓ a i) ≠ 0)
    (h : (θ.cob G Q).rescaleMlp k c = θ) :
    (∀ ℓ, s ℓ = 1) ∧ Q = 1 ∧ ∀ ℓ i, c ℓ i = 1 := by
  sorry

/-- **Lemma A.18, first sentence, `ε = 0`, gated blocks with any gate.** Let `G_ℓ = s_ℓ Q_ℓ`
with `s_ℓ > 0` and `Q_ℓ` orthogonal. If `E` and every write have rank `d ≥ 1`, no value column
of a read vanishes, and these changes of basis with the rescalings `c` of the values fix `θ`,
then `s = 1`, `Q = 1` and `c = 1`. -/
theorem cob_rmsNorm_zero_rescale_eq_self_of_rank_E [Nonempty d]
    (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut) (G Q : Fin (L + 1) → GL d ℝ)
    (s : Fin (L + 1) → ℝ) (c : ∀ ℓ, hid ℓ → ℝ) (hs : ∀ ℓ, 0 < s ℓ)
    (hQ : ∀ ℓ, (Q ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ)
    (hG : ∀ ℓ, (G ℓ : Matrix d d ℝ) = s ℓ • (Q ℓ : Matrix d d ℝ))
    (hE : θ.E.rank = Fintype.card d) (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d)
    (hv : ∀ ℓ i, (fun a => θ.read ℓ a (Sum.inr i)) ≠ 0)
    (h : (θ.cob G Q).rescale c = θ) :
    (∀ ℓ, s ℓ = 1) ∧ Q = 1 ∧ ∀ ℓ i, c ℓ i = 1 := by
  sorry

/-- **Lemma A.18, first sentence, `ε = 0`, ReGLU blocks.** Let `G_ℓ = s_ℓ Q_ℓ` with `s_ℓ > 0`
and `Q_ℓ` orthogonal. If `E` and every write have rank `d ≥ 1`, no gate column and no value
column of a read vanishes, and these changes of basis with the rescalings `c'` of the values and
`c` of the gates fix `θ`, then `s = 1`, `Q = 1`, `c = 1` and `c' = 1`. -/
theorem cob_rmsNorm_zero_rescale_rescaleGate_eq_self_of_rank_E [Nonempty d] (k : ℕ)
    (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut) (G Q : Fin (L + 1) → GL d ℝ)
    (s : Fin (L + 1) → ℝ) (c c' : ∀ ℓ, hid ℓ → ℝ) (hs : ∀ ℓ, 0 < s ℓ)
    (hQ : ∀ ℓ, (Q ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ)
    (hG : ∀ ℓ, (G ℓ : Matrix d d ℝ) = s ℓ • (Q ℓ : Matrix d d ℝ))
    (hE : θ.E.rank = Fintype.card d) (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d)
    (hv : ∀ ℓ i, (fun a => θ.read ℓ a (Sum.inr i)) ≠ 0)
    (hg : ∀ ℓ i, (fun a => θ.read ℓ a (Sum.inl i)) ≠ 0)
    (h : ((θ.cob G Q).rescale c').rescaleGate k c = θ) :
    (∀ ℓ, s ℓ = 1) ∧ Q = 1 ∧ (∀ ℓ i, c ℓ i = 1) ∧ ∀ ℓ i, c' ℓ i = 1 := by
  sorry

/-- **Lemma A.18, second sentence, `ε = 0`, ReLU and ReLU² blocks.** Let `G_ℓ = s_ℓ Q_ℓ` with
`s_ℓ > 0` and `Q_ℓ` orthogonal. If `D` and every read have rank `d ≥ 1`, `E ≠ 0`, no column of a
read and no row of a write vanishes, and these changes of basis with positive rescalings `c` of
the hidden units fix `θ`, then `s = 1`, `Q = 1` and `c = 1`. -/
theorem cob_rmsNorm_zero_rescaleMlp_eq_self_of_rank_D [Nonempty d] (k : ℕ)
    (θ : Params (Arch.mlp (T := T) (d := d) σ χ hid) dIn dOut) (G Q : Fin (L + 1) → GL d ℝ)
    (s : Fin (L + 1) → ℝ) (c : ∀ ℓ, hid ℓ → ℝ) (hs : ∀ ℓ, 0 < s ℓ) (hc : ∀ ℓ i, 0 < c ℓ i)
    (hQ : ∀ ℓ, (Q ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ)
    (hG : ∀ ℓ, (G ℓ : Matrix d d ℝ) = s ℓ • (Q ℓ : Matrix d d ℝ))
    (hD : θ.D.rank = Fintype.card d) (hr : ∀ ℓ, (θ.read ℓ).rank = Fintype.card d)
    (hE : θ.E ≠ 0) (hcol : ∀ ℓ i, (fun a => θ.read ℓ a i) ≠ 0)
    (ha : ∀ ℓ i, (fun a => θ.write ℓ i a) ≠ 0)
    (h : (θ.cob G Q).rescaleMlp k c = θ) :
    (∀ ℓ, s ℓ = 1) ∧ Q = 1 ∧ ∀ ℓ i, c ℓ i = 1 := by
  sorry

/-- **Lemma A.18, second sentence, `ε = 0`, gated blocks with any gate.** Let `G_ℓ = s_ℓ Q_ℓ`
with `s_ℓ > 0` and `Q_ℓ` orthogonal. If `D` and every read have rank `d ≥ 1`, `E ≠ 0`, no value
column of a read and no row of a write vanishes, and these changes of basis with the rescalings
`c` of the values fix `θ`, then `s = 1`, `Q = 1` and `c = 1`. -/
theorem cob_rmsNorm_zero_rescale_eq_self_of_rank_D [Nonempty d]
    (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut) (G Q : Fin (L + 1) → GL d ℝ)
    (s : Fin (L + 1) → ℝ) (c : ∀ ℓ, hid ℓ → ℝ) (hs : ∀ ℓ, 0 < s ℓ)
    (hQ : ∀ ℓ, (Q ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ)
    (hG : ∀ ℓ, (G ℓ : Matrix d d ℝ) = s ℓ • (Q ℓ : Matrix d d ℝ))
    (hD : θ.D.rank = Fintype.card d) (hr : ∀ ℓ, (θ.read ℓ).rank = Fintype.card d)
    (hE : θ.E ≠ 0) (hv : ∀ ℓ i, (fun a => θ.read ℓ a (Sum.inr i)) ≠ 0)
    (ha : ∀ ℓ i, (fun a => θ.write ℓ i a) ≠ 0)
    (h : (θ.cob G Q).rescale c = θ) :
    (∀ ℓ, s ℓ = 1) ∧ Q = 1 ∧ ∀ ℓ i, c ℓ i = 1 := by
  sorry

/-- **Lemma A.18, second sentence, `ε = 0`, ReGLU blocks.** Let `G_ℓ = s_ℓ Q_ℓ` with `s_ℓ > 0`
and `Q_ℓ` orthogonal. If `D` and every read have rank `d ≥ 1`, `E ≠ 0`, no gate column and no
value column of a read and no row of a write vanishes, and these changes of basis with the
rescalings `c'` of the values and positive rescalings `c` of the gates fix `θ`, then `s = 1`,
`Q = 1`, `c = 1` and `c' = 1`. -/
theorem cob_rmsNorm_zero_rescale_rescaleGate_eq_self_of_rank_D [Nonempty d] (k : ℕ)
    (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut) (G Q : Fin (L + 1) → GL d ℝ)
    (s : Fin (L + 1) → ℝ) (c c' : ∀ ℓ, hid ℓ → ℝ) (hs : ∀ ℓ, 0 < s ℓ) (hc : ∀ ℓ i, 0 < c ℓ i)
    (hQ : ∀ ℓ, (Q ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ)
    (hG : ∀ ℓ, (G ℓ : Matrix d d ℝ) = s ℓ • (Q ℓ : Matrix d d ℝ))
    (hD : θ.D.rank = Fintype.card d) (hr : ∀ ℓ, (θ.read ℓ).rank = Fintype.card d)
    (hE : θ.E ≠ 0) (hv : ∀ ℓ i, (fun a => θ.read ℓ a (Sum.inr i)) ≠ 0)
    (hg : ∀ ℓ i, (fun a => θ.read ℓ a (Sum.inl i)) ≠ 0)
    (ha : ∀ ℓ i, (fun a => θ.write ℓ i a) ≠ 0)
    (h : ((θ.cob G Q).rescale c').rescaleGate k c = θ) :
    (∀ ℓ, s ℓ = 1) ∧ Q = 1 ∧ (∀ ℓ i, c ℓ i = 1) ∧ ∀ ℓ i, c' ℓ i = 1 := by
  sorry

variable {sees : T → T → Prop} [DecidableRel sees]
variable {H dh : Fin L → Type} [∀ ℓ, Fintype (H ℓ)] [∀ ℓ, Fintype (dh ℓ)]
  [∀ ℓ, DecidableEq (dh ℓ)]

/-- **Lemma A.18, third sentence, `ε = 0`, attention blocks.** Let `G_ℓ = s_ℓ Q_ℓ` with
`s_ℓ > 0` and `Q_ℓ` orthogonal. If `E` and every write have rank `d ≥ 1`, the query matrix and
the value matrix of every head have rank `d_h`, and these changes of basis with the changes of
basis `K`, `K'` inside the heads fix `θ`, then `s = 1`, `Q = 1`, `K = 1` and `K' = 1`. -/
theorem cob_rmsNorm_zero_headsQK_headsVO_eq_self_of_rank_E [Nonempty d]
    (θ : Params (Arch.attention sees χ H dh) dIn dOut) (G Q : Fin (L + 1) → GL d ℝ)
    (s : Fin (L + 1) → ℝ) (K K' : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ) (hs : ∀ ℓ, 0 < s ℓ)
    (hQ : ∀ ℓ, (Q ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ)
    (hG : ∀ ℓ, (G ℓ : Matrix d d ℝ) = s ℓ • (Q ℓ : Matrix d d ℝ))
    (hE : θ.E.rank = Fintype.card d) (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d)
    (hQr : ∀ ℓ (i : H ℓ), ((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k)).rank
      = Fintype.card (dh ℓ))
    (hVr : ∀ ℓ (i : H ℓ),
      ((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))).rank
        = Fintype.card (dh ℓ))
    (h : ((θ.cob G Q).headsQK K).headsVO K' = θ) :
    (∀ ℓ, s ℓ = 1) ∧ Q = 1 ∧ K = 1 ∧ K' = 1 := by
  sorry

end Skips
