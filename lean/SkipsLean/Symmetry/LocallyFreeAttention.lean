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

/-- Helper (the private `mul_left_cancel_of_rank` of `Dimension/UpperBound.lean`): a matrix `M`
of rank equal to its number of columns cancels on the left, `M X = M Y → X = Y`. -/
private theorem mul_left_cancel_of_rank_lfa {m n k : Type*} [Fintype n] (M : Matrix m n ℝ)
    (hM : M.rank = Fintype.card n) {X Y : Matrix n k ℝ} (h : M * X = M * Y) : X = Y := by
  -- `v ↦ M v` is injective: `rank M + dim ker M = card n`
  have hinj : Function.Injective M.mulVecLin := by
    rw [← LinearMap.ker_eq_bot, ← Submodule.finrank_eq_zero]
    have := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
    rw [Module.finrank_fintype_fun_eq_card] at this
    rw [Matrix.rank] at hM
    omega
  -- compare `X` and `Y` column by column
  ext i j
  have hcol : M.mulVecLin (fun l => X l j) = M.mulVecLin (fun l => Y l j) := by
    funext p
    have := congrFun (congrFun h p) j
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
  exact congrFun (hinj hcol) i

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
  -- the embedding: `E G_0 = E`, and `E` has rank `d`
  have h0 : G 0 = 1 := by
    have hE0 : θ.E * (G 0 : Matrix d d ℝ) = θ.E * (1 : Matrix d d ℝ) := by
      rw [Matrix.mul_one]
      have h1 := congrArg Params.E h
      exact h1
    exact Units.ext (mul_left_cancel_of_rank_lfa θ.E hE hE0)
  -- block `ℓ`: if `G_{ℓ-1} = 1`, then `K_ℓ = 1`, `K'_ℓ = 1` and `G_ℓ = 1`
  have key : ∀ ℓ : Fin L, G ℓ.castSucc = 1 →
      (∀ i, K ℓ i = 1) ∧ (∀ i, K' ℓ i = 1) ∧ G ℓ.succ = 1 := by
    intro ℓ hℓ
    -- the query matrix of head `i` becomes `W_{Q,i} K_i`, and `W_{Q,i}` has rank `d_h`
    have hK : ∀ i, K ℓ i = 1 := by
      intro i
      apply Units.ext
      refine mul_left_cancel_of_rank_lfa _ (hQ ℓ i) ?_
      rw [Units.val_one, Matrix.mul_one]
      ext a k
      have hr := congrFun (congrFun (congrArg (fun η => η.read ℓ) h) a) (i, Sum.inl k)
      change ∑ k', ((↑(G ℓ.castSucc)⁻¹ : Matrix d d ℝ) * θ.read ℓ) a (i, Sum.inl k')
          * (K ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ) k' k = θ.read ℓ a (i, Sum.inl k) at hr
      rw [hℓ, inv_one, Units.val_one, Matrix.one_mul] at hr
      exact hr
    -- the value matrix of head `i` becomes `W_{V,i} K'_i`, and `W_{V,i}` has rank `d_h`
    have hK' : ∀ i, K' ℓ i = 1 := by
      intro i
      apply Units.ext
      refine mul_left_cancel_of_rank_lfa _ (hV ℓ i) ?_
      rw [Units.val_one, Matrix.mul_one]
      ext a k
      have hr := congrFun (congrFun (congrArg (fun η => η.read ℓ) h) a) (i, Sum.inr (Sum.inr k))
      change ∑ k', ((↑(G ℓ.castSucc)⁻¹ : Matrix d d ℝ) * θ.read ℓ) a (i, Sum.inr (Sum.inr k'))
          * (K' ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ) k' k = θ.read ℓ a (i, Sum.inr (Sum.inr k)) at hr
      rw [hℓ, inv_one, Units.val_one, Matrix.one_mul] at hr
      exact hr
    refine ⟨hK, hK', Units.ext ?_⟩
    -- the write becomes `(K'_i⁻¹ (W G_ℓ)_i)_i = W G_ℓ`, and `W` has rank `d`
    refine mul_left_cancel_of_rank_lfa (θ.write ℓ) (hw ℓ) ?_
    rw [Units.val_one, Matrix.mul_one]
    ext ⟨i, k⟩ b
    have hr := congrFun (congrFun (congrArg (fun η => η.write ℓ) h) (i, k)) b
    change ((↑(K' ℓ i)⁻¹ : Matrix (dh ℓ) (dh ℓ) ℝ)
        * (θ.write ℓ * (G ℓ.succ : Matrix d d ℝ)).submatrix (fun k' : dh ℓ => (i, k')) id) k b
      = θ.write ℓ (i, k) b at hr
    rw [hK' i, inv_one, Units.val_one, Matrix.one_mul] at hr
    exact hr
  -- by induction along the network
  have hG : ∀ ℓ : Fin (L + 1), G ℓ = 1 := by
    intro ℓ
    induction ℓ using Fin.induction with
    | zero => exact h0
    | succ ℓ ih => exact (key ℓ ih).2.2
  exact ⟨funext hG, funext fun ℓ => funext fun i => (key ℓ (hG ℓ.castSucc)).1 i,
    funext fun ℓ => funext fun i => (key ℓ (hG ℓ.castSucc)).2.1 i⟩

end Skips
