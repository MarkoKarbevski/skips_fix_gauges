import SkipsLean.Symmetry.AttentionHeads

/-!
# Locally free action: only the identity fixes the parameters (attention blocks)

Paper (skips paper), Lemma A.18 (Locally free action): "With an embedding of rank `d_model`, it
also holds for networks with attention blocks whose heads have width `d_h ≤ d_model` and total
width `H d_h ≥ d_model`." Its proof: "For an attention block, once `G_{ℓ−1} = I` the changes of
basis inside its heads multiply `W_{Q,i}` and `W_{V,i}` on the right. At generic parameters these
have full column rank, as `d_h ≤ d_model`, so the changes of basis inside the heads are the
identity. The write, which stacks the `W_{O,i}`, then transforms as `W_O ↦ W_O G_ℓ` and has rank
`d_model`, as `H d_h ≥ d_model`, so `G_ℓ = I`."

`Symmetry/AttentionHeads.lean` has this in infinitesimal form
(`cobDir_add_headDirQK_add_headDirVO_injective`). Here the statement for the group, the twin of
`Symmetry/LocallyFreeEmbedding.lean`: if the changes of basis `G` of the hidden states with the
changes of basis `K` (queries and keys) and `K'` (values and outputs) inside the heads fix `θ`,
they are the identity, at every `θ` whose embedding and writes have rank `d` and whose query and
value matrices have rank `d_h`.
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {sees : T → T → Prop} [DecidableRel sees] {χ : Matrix T d ℝ → Matrix T d ℝ}
variable {H dh : Fin L → Type} [∀ ℓ, Fintype (H ℓ)] [∀ ℓ, Fintype (dh ℓ)]
  [∀ ℓ, DecidableEq (dh ℓ)]

/-- **Lemma A.18, third sentence, for the group.** If `E` and every write have rank `d`, the
query matrix and the value matrix of every head have rank `d_h`, and the changes of basis `G` of
the hidden states with the changes of basis `K`, `K'` inside the heads fix `θ`, then `G = 1`,
`K = 1` and `K' = 1`. -/
theorem cob_headsQK_headsVO_eq_self_of_rank_E
    (θ : Params (Arch.attention sees χ H dh) dIn dOut) (G : Fin (L + 1) → GL d ℝ)
    (K K' : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ) (hE : θ.E.rank = Fintype.card d)
    (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d)
    (hQ : ∀ ℓ (i : H ℓ), ((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k)).rank
      = Fintype.card (dh ℓ))
    (hV : ∀ ℓ (i : H ℓ),
      ((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))).rank
        = Fintype.card (dh ℓ))
    (h : ((θ.cob G G).headsQK K).headsVO K' = θ) : G = 1 ∧ K = 1 ∧ K' = 1 := by
  sorry

end Skips
