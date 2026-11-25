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

/-- Helper (the private `mul_left_cancel_of_rank` of `Dimension/UpperBound.lean`): a matrix `M`
of rank equal to its number of columns cancels on the left, `M X = M Y → X = Y`. -/
private theorem mul_left_cancel_of_rank_lft {m n k : Type*} [Fintype n] (M : Matrix m n ℝ)
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

omit [Fintype T] [Fintype dIn] [Fintype dOut] in
/-- Helper (the induction of the twins): if `E G_0 = E`, and in every block `ℓ` the write
satisfies `W_ℓ G_ℓ = W_ℓ` once `G_{ℓ-1} = 1`, then, with `E` and the writes of rank `d`, every
`G_ℓ` is the identity. -/
private theorem eq_one_of_steps_lft {A : Arch T d L} (θ : Params A dIn dOut)
    (G : Fin (L + 1) → GL d ℝ) (hE : θ.E.rank = Fintype.card d)
    (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d) (h0 : θ.E * (G 0 : Matrix d d ℝ) = θ.E)
    (hstep : ∀ ℓ : Fin L, G ℓ.castSucc = 1 →
      θ.write ℓ * (G ℓ.succ : Matrix d d ℝ) = θ.write ℓ) :
    ∀ ℓ, G ℓ = 1 := by
  intro ℓ
  induction ℓ using Fin.induction with
  | zero =>
    -- the embedding: `E G_0 = E`, and `E` has rank `d`
    apply Units.ext
    refine mul_left_cancel_of_rank_lft θ.E hE ?_
    rw [Units.val_one, Matrix.mul_one]
    exact h0
  | succ ℓ ih =>
    -- block `ℓ`: `W_ℓ G_ℓ = W_ℓ`, and `W_ℓ` has rank `d`
    apply Units.ext
    refine mul_left_cancel_of_rank_lft (θ.write ℓ) (hw ℓ) ?_
    rw [Units.val_one, Matrix.mul_one]
    exact hstep ℓ ih

omit [Fintype T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the write of block `ℓ` of `A.sum B` stacks the write rows of the two parts, so
`W M = W` once `W_A M = W_A` and `W_B M = W_B`. -/
private theorem write_mul_eq_lft {A B : Arch T d L} (θ : Params (A.sum B) dIn dOut) (ℓ : Fin L)
    (M : Matrix d d ℝ) (hA : θ.sumFst.write ℓ * M = θ.sumFst.write ℓ)
    (hB : θ.sumSnd.write ℓ * M = θ.sumSnd.write ℓ) : θ.write ℓ * M = θ.write ℓ := by
  -- row by row: a row of `A` (`Sum.inl`) or of `B` (`Sum.inr`)
  ext p a
  cases p with
  | inl p => exact congrFun (congrFun hA p) a
  | inr p => exact congrFun (congrFun hB p) a

omit [Fintype dIn] [Fintype dOut] in
/-- Helper (block `ℓ` of `cob_headsQK_headsVO_eq_self_of_rank_E`, for any change of basis `R` of
the reads): once `R_{ℓ-1} = 1`, the changes of basis inside the heads of block `ℓ` are the
identity and the write of block `ℓ` satisfies `W G_ℓ = W`. -/
private theorem attention_step_lft (θ : Params (Arch.attention sees χ H dh) dIn dOut)
    (G R : Fin (L + 1) → GL d ℝ) (K K' : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ) (ℓ : Fin L)
    (hR : R ℓ.castSucc = 1)
    (hQr : ∀ i : H ℓ, ((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k)).rank
      = Fintype.card (dh ℓ))
    (hVr : ∀ i : H ℓ,
      ((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))).rank
        = Fintype.card (dh ℓ))
    (h : ((θ.cob G R).headsQK K).headsVO K' = θ) :
    (∀ i, K ℓ i = 1) ∧ (∀ i, K' ℓ i = 1) ∧
      θ.write ℓ * (G ℓ.succ : Matrix d d ℝ) = θ.write ℓ := by
  -- the query matrix of head `i` becomes `W_{Q,i} K_i`, and `W_{Q,i}` has rank `d_h`
  have hK : ∀ i, K ℓ i = 1 := by
    intro i
    apply Units.ext
    refine mul_left_cancel_of_rank_lft _ (hQr i) ?_
    rw [Units.val_one, Matrix.mul_one]
    ext a k
    have hr := congrFun (congrFun (congrArg (fun η => η.read ℓ) h) a) (i, Sum.inl k)
    change ∑ k', ((↑(R ℓ.castSucc)⁻¹ : Matrix d d ℝ) * θ.read ℓ) a (i, Sum.inl k')
        * (K ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ) k' k = θ.read ℓ a (i, Sum.inl k) at hr
    rw [hR, inv_one, Units.val_one, Matrix.one_mul] at hr
    exact hr
  -- the value matrix of head `i` becomes `W_{V,i} K'_i`, and `W_{V,i}` has rank `d_h`
  have hK' : ∀ i, K' ℓ i = 1 := by
    intro i
    apply Units.ext
    refine mul_left_cancel_of_rank_lft _ (hVr i) ?_
    rw [Units.val_one, Matrix.mul_one]
    ext a k
    have hr := congrFun (congrFun (congrArg (fun η => η.read ℓ) h) a) (i, Sum.inr (Sum.inr k))
    change ∑ k', ((↑(R ℓ.castSucc)⁻¹ : Matrix d d ℝ) * θ.read ℓ) a (i, Sum.inr (Sum.inr k'))
        * (K' ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ) k' k = θ.read ℓ a (i, Sum.inr (Sum.inr k)) at hr
    rw [hR, inv_one, Units.val_one, Matrix.one_mul] at hr
    exact hr
  refine ⟨hK, hK', ?_⟩
  -- the write becomes `(K'_i⁻¹ (W G_ℓ)_i)_i = W G_ℓ`
  ext ⟨i, k⟩ b
  have hr := congrFun (congrFun (congrArg (fun η => η.write ℓ) h) (i, k)) b
  change ((↑(K' ℓ i)⁻¹ : Matrix (dh ℓ) (dh ℓ) ℝ)
      * (θ.write ℓ * (G ℓ.succ : Matrix d d ℝ)).submatrix (fun k' : dh ℓ => (i, k')) id) k b
    = θ.write ℓ (i, k) b at hr
  rw [hK' i, inv_one, Units.val_one, Matrix.one_mul] at hr
  exact hr

omit [Fintype T] [Fintype dIn] [Fintype dOut] in
/-- Helper (block `ℓ` of `cob_rescaleMlp_eq_self_of_rank_E`, for any change of basis `R` of the
reads): once `R_{ℓ-1} = 1`, the rescalings of the hidden units of block `ℓ` are `1` and the write
of block `ℓ` satisfies `W G_ℓ = W`. -/
private theorem mlp_step_lft (k : ℕ) (θ : Params (Arch.mlp (T := T) (d := d) σ χ hid) dIn dOut)
    (G R : Fin (L + 1) → GL d ℝ) (c : ∀ ℓ, hid ℓ → ℝ) (ℓ : Fin L) (hR : R ℓ.castSucc = 1)
    (hcol : ∀ i, (fun a => θ.read ℓ a i) ≠ 0) (h : (θ.cob G R).rescaleMlp k c = θ) :
    (∀ i, c ℓ i = 1) ∧ θ.write ℓ * (G ℓ.succ : Matrix d d ℝ) = θ.write ℓ := by
  -- the read column `i` becomes `c_i w_i`, and `w_i ≠ 0`
  have hc : ∀ i, c ℓ i = 1 := by
    intro i
    obtain ⟨a, ha⟩ := Function.ne_iff.mp (hcol i)
    have hr := congrFun (congrFun (congrArg (fun η => η.read ℓ) h) a) i
    change c ℓ i * ((↑(R ℓ.castSucc)⁻¹ : Matrix d d ℝ) * θ.read ℓ) a i = θ.read ℓ a i at hr
    rw [hR, inv_one, Units.val_one, Matrix.one_mul] at hr
    exact mul_right_cancel₀ ha (hr.trans (one_mul _).symm)
  refine ⟨hc, ?_⟩
  -- the write becomes `(1 ^ k)⁻¹ W G_ℓ = W G_ℓ`
  ext i a
  have hr := congrFun (congrFun (congrArg (fun η => η.write ℓ) h) i) a
  change (c ℓ i ^ k)⁻¹ * (θ.write ℓ * (G ℓ.succ : Matrix d d ℝ)) i a = θ.write ℓ i a at hr
  rw [hc i, one_pow, inv_one, one_mul] at hr
  exact hr

omit [Fintype T] [Fintype dIn] [Fintype dOut] in
/-- Helper (block `ℓ` of `cob_rescale_eq_self_of_rank_E`, for any change of basis `R` of the
reads): once `R_{ℓ-1} = 1`, the rescalings of the values of block `ℓ` are `1` and the write of
block `ℓ` satisfies `W G_ℓ = W`. -/
private theorem gated_step_lft (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut)
    (G R : Fin (L + 1) → GL d ℝ) (c : ∀ ℓ, hid ℓ → ℝ) (ℓ : Fin L) (hR : R ℓ.castSucc = 1)
    (hv : ∀ i, (fun a => θ.read ℓ a (Sum.inr i)) ≠ 0) (h : (θ.cob G R).rescale c = θ) :
    (∀ i, c ℓ i = 1) ∧ θ.write ℓ * (G ℓ.succ : Matrix d d ℝ) = θ.write ℓ := by
  -- the value column `i` becomes `c_i⁻¹ e_i`, and `e_i ≠ 0`
  have hc : ∀ i, c ℓ i = 1 := by
    intro i
    obtain ⟨a, ha⟩ := Function.ne_iff.mp (hv i)
    have hr := congrFun (congrFun (congrArg (fun η => η.read ℓ) h) a) (Sum.inr i)
    change (c ℓ i)⁻¹ * ((↑(R ℓ.castSucc)⁻¹ : Matrix d d ℝ) * θ.read ℓ) a (Sum.inr i)
      = θ.read ℓ a (Sum.inr i) at hr
    rw [hR, inv_one, Units.val_one, Matrix.one_mul] at hr
    exact inv_eq_one.mp (mul_right_cancel₀ ha (hr.trans (one_mul _).symm))
  refine ⟨hc, ?_⟩
  -- the write becomes `1 · W G_ℓ = W G_ℓ`
  ext i a
  have hr := congrFun (congrFun (congrArg (fun η => η.write ℓ) h) i) a
  change c ℓ i * (θ.write ℓ * (G ℓ.succ : Matrix d d ℝ)) i a = θ.write ℓ i a at hr
  rw [hc i, one_mul] at hr
  exact hr

omit [Fintype T] [Fintype dIn] [Fintype dOut] in
/-- Helper (block `ℓ` of `cob_rescale_rescaleGate_eq_self_of_rank_E`, for any change of basis `R`
of the reads): once `R_{ℓ-1} = 1`, the rescalings of the gates and of the values of block `ℓ` are
`1` and the write of block `ℓ` satisfies `W G_ℓ = W`. -/
private theorem reglu_step_lft (k : ℕ)
    (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut)
    (G R : Fin (L + 1) → GL d ℝ) (c c' : ∀ ℓ, hid ℓ → ℝ) (ℓ : Fin L) (hR : R ℓ.castSucc = 1)
    (hv : ∀ i, (fun a => θ.read ℓ a (Sum.inr i)) ≠ 0)
    (hg : ∀ i, (fun a => θ.read ℓ a (Sum.inl i)) ≠ 0)
    (h : ((θ.cob G R).rescale c').rescaleGate k c = θ) :
    (∀ i, c ℓ i = 1) ∧ (∀ i, c' ℓ i = 1) ∧
      θ.write ℓ * (G ℓ.succ : Matrix d d ℝ) = θ.write ℓ := by
  -- the gate column `i` becomes `c_i g_i`, and `g_i ≠ 0`
  have hc : ∀ i, c ℓ i = 1 := by
    intro i
    obtain ⟨a, ha⟩ := Function.ne_iff.mp (hg i)
    have hr := congrFun (congrFun (congrArg (fun η => η.read ℓ) h) a) (Sum.inl i)
    change c ℓ i * ((↑(R ℓ.castSucc)⁻¹ : Matrix d d ℝ) * θ.read ℓ) a (Sum.inl i)
      = θ.read ℓ a (Sum.inl i) at hr
    rw [hR, inv_one, Units.val_one, Matrix.one_mul] at hr
    exact mul_right_cancel₀ ha (hr.trans (one_mul _).symm)
  -- the value column `i` becomes `c'_i⁻¹ e_i`, and `e_i ≠ 0`
  have hc' : ∀ i, c' ℓ i = 1 := by
    intro i
    obtain ⟨a, ha⟩ := Function.ne_iff.mp (hv i)
    have hr := congrFun (congrFun (congrArg (fun η => η.read ℓ) h) a) (Sum.inr i)
    change (c' ℓ i)⁻¹ * ((↑(R ℓ.castSucc)⁻¹ : Matrix d d ℝ) * θ.read ℓ) a (Sum.inr i)
      = θ.read ℓ a (Sum.inr i) at hr
    rw [hR, inv_one, Units.val_one, Matrix.one_mul] at hr
    exact inv_eq_one.mp (mul_right_cancel₀ ha (hr.trans (one_mul _).symm))
  refine ⟨hc, hc', ?_⟩
  -- the write becomes `(1 ^ k)⁻¹ (1 · W G_ℓ) = W G_ℓ`
  ext i a
  have hr := congrFun (congrFun (congrArg (fun η => η.write ℓ) h) i) a
  change (c ℓ i ^ k)⁻¹ * (c' ℓ i * (θ.write ℓ * (G ℓ.succ : Matrix d d ℝ)) i a)
    = θ.write ℓ i a at hr
  rw [hc i, hc' i, one_pow, inv_one, one_mul, one_mul] at hr
  exact hr

omit [Fintype dIn] [Fintype dOut] in
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
  -- the embedding: `E G_0 = E` (the attention part has the `E` of `θ`)
  have hE0 : θ.E * (G 0 : Matrix d d ℝ) = θ.E := by
    have hE1 := congrArg Params.E h1
    exact hE1
  -- block `ℓ`, once `G_{ℓ-1} = 1`: the attention part gives `K_ℓ = 1`, `K'_ℓ = 1` and
  -- `W_A G_ℓ = W_A` for its write rows, the MLP part `c_ℓ = 1` and `W_B G_ℓ = W_B`
  have key : ∀ ℓ : Fin L, G ℓ.castSucc = 1 →
      ((∀ i, K ℓ i = 1) ∧ (∀ i, K' ℓ i = 1) ∧
        θ.sumFst.write ℓ * (G ℓ.succ : Matrix d d ℝ) = θ.sumFst.write ℓ) ∧
      ((∀ i, c ℓ i = 1) ∧ θ.sumSnd.write ℓ * (G ℓ.succ : Matrix d d ℝ) = θ.sumSnd.write ℓ) :=
    fun ℓ hℓ => ⟨attention_step_lft θ.sumFst G G K K' ℓ hℓ (hQr ℓ) (hVr ℓ) h1,
      mlp_step_lft k θ.sumSnd G G c ℓ hℓ (hcol ℓ) h2⟩
  -- so the write of block `ℓ` (both parts) satisfies `W G_ℓ = W`; by induction `G = 1`
  have hG : ∀ ℓ, G ℓ = 1 := eq_one_of_steps_lft θ G hE hw hE0 fun ℓ hℓ =>
    write_mul_eq_lft θ ℓ _ (key ℓ hℓ).1.2.2 (key ℓ hℓ).2.2
  exact ⟨funext hG, funext fun ℓ => funext (key ℓ (hG ℓ.castSucc)).1.1,
    funext fun ℓ => funext (key ℓ (hG ℓ.castSucc)).1.2.1, fun ℓ => (key ℓ (hG ℓ.castSucc)).2.1⟩

omit [Fintype dIn] [Fintype dOut] in
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
  -- the embedding: `E G_0 = E` (the attention part has the `E` of `θ`)
  have hE0 : θ.E * (G 0 : Matrix d d ℝ) = θ.E := by
    have hE1 := congrArg Params.E h1
    exact hE1
  -- block `ℓ`, once `G_{ℓ-1} = 1`: the attention part gives `K_ℓ = 1`, `K'_ℓ = 1` and
  -- `W_A G_ℓ = W_A` for its write rows, the gated part `c_ℓ = 1` and `W_B G_ℓ = W_B`
  have key : ∀ ℓ : Fin L, G ℓ.castSucc = 1 →
      ((∀ i, K ℓ i = 1) ∧ (∀ i, K' ℓ i = 1) ∧
        θ.sumFst.write ℓ * (G ℓ.succ : Matrix d d ℝ) = θ.sumFst.write ℓ) ∧
      ((∀ i, c ℓ i = 1) ∧ θ.sumSnd.write ℓ * (G ℓ.succ : Matrix d d ℝ) = θ.sumSnd.write ℓ) :=
    fun ℓ hℓ => ⟨attention_step_lft θ.sumFst G G K K' ℓ hℓ (hQr ℓ) (hVr ℓ) h1,
      gated_step_lft θ.sumSnd G G c ℓ hℓ (hv ℓ) h2⟩
  -- so the write of block `ℓ` (both parts) satisfies `W G_ℓ = W`; by induction `G = 1`
  have hG : ∀ ℓ, G ℓ = 1 := eq_one_of_steps_lft θ G hE hw hE0 fun ℓ hℓ =>
    write_mul_eq_lft θ ℓ _ (key ℓ hℓ).1.2.2 (key ℓ hℓ).2.2
  exact ⟨funext hG, funext fun ℓ => funext (key ℓ (hG ℓ.castSucc)).1.1,
    funext fun ℓ => funext (key ℓ (hG ℓ.castSucc)).1.2.1, fun ℓ => (key ℓ (hG ℓ.castSucc)).2.1⟩

omit [Fintype dIn] [Fintype dOut] in
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
  -- the embedding: `E G_0 = E` (the attention part has the `E` of `θ`)
  have hE0 : θ.E * (G 0 : Matrix d d ℝ) = θ.E := by
    have hE1 := congrArg Params.E h1
    exact hE1
  -- block `ℓ`, once `G_{ℓ-1} = 1`: the attention part gives `K_ℓ = 1`, `K'_ℓ = 1` and
  -- `W_A G_ℓ = W_A` for its write rows, the ReGLU part `c_ℓ = 1`, `c'_ℓ = 1` and `W_B G_ℓ = W_B`
  have key : ∀ ℓ : Fin L, G ℓ.castSucc = 1 →
      ((∀ i, K ℓ i = 1) ∧ (∀ i, K' ℓ i = 1) ∧
        θ.sumFst.write ℓ * (G ℓ.succ : Matrix d d ℝ) = θ.sumFst.write ℓ) ∧
      ((∀ i, c ℓ i = 1) ∧ (∀ i, c' ℓ i = 1) ∧
        θ.sumSnd.write ℓ * (G ℓ.succ : Matrix d d ℝ) = θ.sumSnd.write ℓ) :=
    fun ℓ hℓ => ⟨attention_step_lft θ.sumFst G G K K' ℓ hℓ (hQr ℓ) (hVr ℓ) h1,
      reglu_step_lft k θ.sumSnd G G c c' ℓ hℓ (hv ℓ) (hg ℓ) h2⟩
  -- so the write of block `ℓ` (both parts) satisfies `W G_ℓ = W`; by induction `G = 1`
  have hG : ∀ ℓ, G ℓ = 1 := eq_one_of_steps_lft θ G hE hw hE0 fun ℓ hℓ =>
    write_mul_eq_lft θ ℓ _ (key ℓ hℓ).1.2.2 (key ℓ hℓ).2.2.2
  exact ⟨funext hG, funext fun ℓ => funext (key ℓ (hG ℓ.castSucc)).1.1,
    funext fun ℓ => funext (key ℓ (hG ℓ.castSucc)).1.2.1, fun ℓ => (key ℓ (hG ℓ.castSucc)).2.1,
    fun ℓ => (key ℓ (hG ℓ.castSucc)).2.2.1⟩

/-- Helper (the private `eq_one_of_smul_eq_one_lfz` of `Symmetry/LocallyFreeRMSZero.lean`): if
`s Q = 1` with `Q` orthogonal and `s > 0`, then `s = 1` and `Q = 1`. -/
private theorem eq_one_of_smul_eq_one_lft [Nonempty d] (Q : GL d ℝ)
    (hQ : (Q : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ) {s : ℝ} (hs : 0 < s)
    (h : s • (Q : Matrix d d ℝ) = 1) : s = 1 ∧ Q = 1 := by
  -- `(s Q)(s Q)ᵀ = s² 1`, and `s Q = 1`: `s² = 1`
  have hQQ := (Matrix.mem_orthogonalGroup_iff d ℝ).mp hQ
  have h2 : (s • (Q : Matrix d d ℝ)) * (s • (Q : Matrix d d ℝ))ᵀ
      = (s * s) • (1 : Matrix d d ℝ) := by
    rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hQQ]
  rw [h, Matrix.transpose_one, Matrix.one_mul] at h2
  obtain ⟨x⟩ := (inferInstance : Nonempty d)
  have h3 := congrFun (congrFun h2 x) x
  rw [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h3
  -- so `s = 1`, and then `Q = 1`
  have hs1 : s = 1 := by nlinarith
  refine ⟨hs1, Units.ext ?_⟩
  rw [hs1, one_smul] at h
  exact h

omit [Fintype dIn] [Fintype dOut] in
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
  -- `G_ℓ = 1` gives `s_ℓ = 1` and `Q_ℓ = 1`
  have hGQ : ∀ ℓ, G ℓ = 1 → s ℓ = 1 ∧ Q ℓ = 1 := fun ℓ hℓ =>
    eq_one_of_smul_eq_one_lft (Q ℓ) (hQ ℓ) (hs ℓ) (by rw [← hG ℓ, hℓ, Units.val_one])
  -- the embedding: `E G_0 = E` (the attention part has the `E` of `θ`)
  have hE0 : θ.E * (G 0 : Matrix d d ℝ) = θ.E := by
    have hE1 := congrArg Params.E h1
    exact hE1
  -- block `ℓ`, once `G_{ℓ-1} = 1` (so the reads see `Q_{ℓ-1}⁻¹ = 1`): the attention part gives
  -- `K_ℓ = 1`, `K'_ℓ = 1` and `W_A G_ℓ = W_A`, the MLP part `c_ℓ = 1` and `W_B G_ℓ = W_B`
  have key : ∀ ℓ : Fin L, G ℓ.castSucc = 1 →
      ((∀ i, K ℓ i = 1) ∧ (∀ i, K' ℓ i = 1) ∧
        θ.sumFst.write ℓ * (G ℓ.succ : Matrix d d ℝ) = θ.sumFst.write ℓ) ∧
      ((∀ i, c ℓ i = 1) ∧ θ.sumSnd.write ℓ * (G ℓ.succ : Matrix d d ℝ) = θ.sumSnd.write ℓ) :=
    fun ℓ hℓ => ⟨attention_step_lft θ.sumFst G Q K K' ℓ (hGQ _ hℓ).2 (hQr ℓ) (hVr ℓ) h1,
      mlp_step_lft k θ.sumSnd G Q c ℓ (hGQ _ hℓ).2 (hcol ℓ) h2⟩
  -- so the write of block `ℓ` (both parts) satisfies `W G_ℓ = W`; by induction `G = 1`
  have hG1 : ∀ ℓ, G ℓ = 1 := eq_one_of_steps_lft θ G hE hw hE0 fun ℓ hℓ =>
    write_mul_eq_lft θ ℓ _ (key ℓ hℓ).1.2.2 (key ℓ hℓ).2.2
  exact ⟨fun ℓ => (hGQ ℓ (hG1 ℓ)).1, funext fun ℓ => (hGQ ℓ (hG1 ℓ)).2,
    funext fun ℓ => funext (key ℓ (hG1 ℓ.castSucc)).1.1,
    funext fun ℓ => funext (key ℓ (hG1 ℓ.castSucc)).1.2.1,
    fun ℓ => (key ℓ (hG1 ℓ.castSucc)).2.1⟩

omit [Fintype dIn] [Fintype dOut] in
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
  -- `G_ℓ = 1` gives `s_ℓ = 1` and `Q_ℓ = 1`
  have hGQ : ∀ ℓ, G ℓ = 1 → s ℓ = 1 ∧ Q ℓ = 1 := fun ℓ hℓ =>
    eq_one_of_smul_eq_one_lft (Q ℓ) (hQ ℓ) (hs ℓ) (by rw [← hG ℓ, hℓ, Units.val_one])
  -- the embedding: `E G_0 = E` (the attention part has the `E` of `θ`)
  have hE0 : θ.E * (G 0 : Matrix d d ℝ) = θ.E := by
    have hE1 := congrArg Params.E h1
    exact hE1
  -- block `ℓ`, once `G_{ℓ-1} = 1` (so the reads see `Q_{ℓ-1}⁻¹ = 1`): the attention part gives
  -- `K_ℓ = 1`, `K'_ℓ = 1` and `W_A G_ℓ = W_A`, the gated part `c_ℓ = 1` and `W_B G_ℓ = W_B`
  have key : ∀ ℓ : Fin L, G ℓ.castSucc = 1 →
      ((∀ i, K ℓ i = 1) ∧ (∀ i, K' ℓ i = 1) ∧
        θ.sumFst.write ℓ * (G ℓ.succ : Matrix d d ℝ) = θ.sumFst.write ℓ) ∧
      ((∀ i, c ℓ i = 1) ∧ θ.sumSnd.write ℓ * (G ℓ.succ : Matrix d d ℝ) = θ.sumSnd.write ℓ) :=
    fun ℓ hℓ => ⟨attention_step_lft θ.sumFst G Q K K' ℓ (hGQ _ hℓ).2 (hQr ℓ) (hVr ℓ) h1,
      gated_step_lft θ.sumSnd G Q c ℓ (hGQ _ hℓ).2 (hv ℓ) h2⟩
  -- so the write of block `ℓ` (both parts) satisfies `W G_ℓ = W`; by induction `G = 1`
  have hG1 : ∀ ℓ, G ℓ = 1 := eq_one_of_steps_lft θ G hE hw hE0 fun ℓ hℓ =>
    write_mul_eq_lft θ ℓ _ (key ℓ hℓ).1.2.2 (key ℓ hℓ).2.2
  exact ⟨fun ℓ => (hGQ ℓ (hG1 ℓ)).1, funext fun ℓ => (hGQ ℓ (hG1 ℓ)).2,
    funext fun ℓ => funext (key ℓ (hG1 ℓ.castSucc)).1.1,
    funext fun ℓ => funext (key ℓ (hG1 ℓ.castSucc)).1.2.1,
    fun ℓ => (key ℓ (hG1 ℓ.castSucc)).2.1⟩

omit [Fintype dIn] [Fintype dOut] in
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
  -- `G_ℓ = 1` gives `s_ℓ = 1` and `Q_ℓ = 1`
  have hGQ : ∀ ℓ, G ℓ = 1 → s ℓ = 1 ∧ Q ℓ = 1 := fun ℓ hℓ =>
    eq_one_of_smul_eq_one_lft (Q ℓ) (hQ ℓ) (hs ℓ) (by rw [← hG ℓ, hℓ, Units.val_one])
  -- the embedding: `E G_0 = E` (the attention part has the `E` of `θ`)
  have hE0 : θ.E * (G 0 : Matrix d d ℝ) = θ.E := by
    have hE1 := congrArg Params.E h1
    exact hE1
  -- block `ℓ`, once `G_{ℓ-1} = 1` (so the reads see `Q_{ℓ-1}⁻¹ = 1`): the attention part gives
  -- `K_ℓ = 1`, `K'_ℓ = 1` and `W_A G_ℓ = W_A`, the ReGLU part `c_ℓ = 1`, `c'_ℓ = 1` and
  -- `W_B G_ℓ = W_B`
  have key : ∀ ℓ : Fin L, G ℓ.castSucc = 1 →
      ((∀ i, K ℓ i = 1) ∧ (∀ i, K' ℓ i = 1) ∧
        θ.sumFst.write ℓ * (G ℓ.succ : Matrix d d ℝ) = θ.sumFst.write ℓ) ∧
      ((∀ i, c ℓ i = 1) ∧ (∀ i, c' ℓ i = 1) ∧
        θ.sumSnd.write ℓ * (G ℓ.succ : Matrix d d ℝ) = θ.sumSnd.write ℓ) :=
    fun ℓ hℓ => ⟨attention_step_lft θ.sumFst G Q K K' ℓ (hGQ _ hℓ).2 (hQr ℓ) (hVr ℓ) h1,
      reglu_step_lft k θ.sumSnd G Q c c' ℓ (hGQ _ hℓ).2 (hv ℓ) (hg ℓ) h2⟩
  -- so the write of block `ℓ` (both parts) satisfies `W G_ℓ = W`; by induction `G = 1`
  have hG1 : ∀ ℓ, G ℓ = 1 := eq_one_of_steps_lft θ G hE hw hE0 fun ℓ hℓ =>
    write_mul_eq_lft θ ℓ _ (key ℓ hℓ).1.2.2 (key ℓ hℓ).2.2.2
  exact ⟨fun ℓ => (hGQ ℓ (hG1 ℓ)).1, funext fun ℓ => (hGQ ℓ (hG1 ℓ)).2,
    funext fun ℓ => funext (key ℓ (hG1 ℓ.castSucc)).1.1,
    funext fun ℓ => funext (key ℓ (hG1 ℓ.castSucc)).1.2.1,
    fun ℓ => (key ℓ (hG1 ℓ.castSucc)).2.1, fun ℓ => (key ℓ (hG1 ℓ.castSucc)).2.2.1⟩

end Skips
