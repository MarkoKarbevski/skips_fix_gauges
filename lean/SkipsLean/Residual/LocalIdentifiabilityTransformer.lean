import SkipsLean.Dimension.LocalIdentifiabilityAttention
import SkipsLean.Residual.LocalIdentifiabilityAttentionRMS
import SkipsLean.Residual.LocalIdentifiabilityGated
import SkipsLean.Residual.DepthTransformer
import SkipsLean.Residual.DepthTransformerGated
import SkipsLean.Residual.DepthTransformerRMS
import SkipsLean.Residual.DepthTransformerGatedRMS

/-!
# Residual networks of attention blocks and MLP blocks are locally identifiable

Paper (skips paper): Corollary 4.9 (Residual networks are locally identifiable): "Let the blocks
be analytic, with or without pre-RMSNorm, and let `θ` be generic parameters of the residual
network. Every `θ′` near `θ` with the same function is obtained from `θ` by symmetries inside the
blocks and by one matrix `G ∈ G`, all close to the identity. The matrix `G` is the same at all
hidden states". Proposition 4.5 (The equality condition and local identifiability), the direction
from the equality condition to local identifiability, at one parameter.

Here for the residual networks of `Network/Transformer.lean`, whose blocks are attention blocks
and MLP blocks (`Arch.attentionMlp`), or attention blocks and gated blocks
(`Arch.attentionGated`), in any order; the twins of `Dimension/LocalIdentifiabilityAttention.lean`
(attention blocks) and `Residual/LocalIdentifiability.lean`, `LocalIdentifiabilityGated.lean`
(MLP and gated blocks).

* `Params.sumOf a b`: the parameters of a network of `A.sum B` with the parts `a` and `b` (the
  embedding and the readout of `a`). The symmetries of a transformer `θ` are written with it:
  the changes of basis inside the heads act on the first part `θ.sumFst`
  (`Params.headsQK`, `Params.headsVO`), the rescalings of the values of gated units on the second
  part `θ.sumSnd` (`Params.rescale`), and the change of basis of the hidden states on the whole
  (`Params.cob`).
* At one parameter with the functional dimension of Theorem 4.7 (Proposition 4.5), without
  normalization and under pre-RMSNorm (`ε > 0`; then `G` is orthogonal).
* At almost every parameter (Corollary 4.9), for every activation with the conclusion of
  Lemma B.3, and named for tanh, GELU, SwiGLU and GeGLU blocks.

No permutation of heads or of hidden units is needed: the symmetries of the conclusion are near
the identity.
-/

namespace Skips

open Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ}

/-- **The parameters of a network of `A.sum B` with the two parts `a` and `b`:** the embedding
and the readout of `a`, and in every block the read columns and the write rows of `a` beside
those of `b`. -/
def Params.sumOf {A B : Arch T d L} (a : Params A dIn dOut) (b : Params B dIn dOut) :
    Params (A.sum B) dIn dOut where
  E := a.E
  read ℓ := Matrix.of fun k p => Sum.elim (fun j => a.read ℓ k j) (fun j => b.read ℓ k j) p
  write ℓ := Matrix.of fun p k => Sum.elim (fun i => a.write ℓ i k) (fun i => b.write ℓ i k) p
  D := a.D

/-- A network of `A.sum B` is made of its two parts. -/
theorem Params.sumOf_sumFst_sumSnd {A B : Arch T d L} (θ : Params (A.sum B) dIn dOut) :
    Params.sumOf θ.sumFst θ.sumSnd = θ := by
  refine Params.ext' rfl (fun ℓ => ?_) (fun ℓ => ?_) rfl
  · -- the read columns of the two parts, side by side
    ext k p
    rcases p with j | j <;> rfl
  · -- the write rows of the two parts, one above the other
    ext p k
    rcases p with i | i <;> rfl

variable [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut]
variable {sees : T → T → Prop} [DecidableRel sees]
variable {H dh hid : Fin L → Type} [∀ ℓ, Fintype (H ℓ)] [∀ ℓ, Fintype (dh ℓ)]
  [∀ ℓ, DecidableEq (dh ℓ)] [∀ ℓ, Fintype (hid ℓ)] {σ σ' : ℝ → ℝ} {ε : ℝ}


/-! ### Helpers: the two parts of the parameters of a network of `A.sum B` -/

omit [Fintype T] [Fintype dIn] [Fintype dOut] in
/-- Helper: the change of basis of the hidden states acts part by part: the read columns and the
write rows of the two parts are multiplied by the same matrices, and `E`, `D` are those of the
first part. -/
private theorem sumOf_cob_lit {A B : Arch T d L} (a : Params A dIn dOut) (b : Params B dIn dOut)
    (G K : Fin (L + 1) → GL d ℝ) :
    Params.sumOf (a.cob G K) (b.cob G K) = (Params.sumOf a b).cob G K := by
  refine Params.ext' rfl (fun ℓ => ?_) (fun ℓ => ?_) rfl
  · ext k p
    rcases p with j | j <;> rfl
  · ext p k
    rcases p with i | i <;> rfl

/-- Helper: `(a, b) ↦ Params.sumOf a b` is linear. -/
private noncomputable def sumOfLin_lit {A B : Arch T d L} :
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

omit [Fintype T] [DecidableEq d] [Fintype dOut] in
/-- Helper (the private `eval_eq_of_blocks_ath` of `Symmetry/AttentionHeads.lean`): two parameters
with the same `E`, the same `D` and the same output of every block on every hidden state compute
the same function (induction along the hidden states). -/
private theorem eval_eq_of_blocks_lit {A : Arch T d L} (θ₁ θ₂ : Params A dIn dOut)
    (hE : θ₂.E = θ₁.E) (hD : θ₂.D = θ₁.D)
    (hb : ∀ ℓ (h : Matrix T d ℝ),
      A.f ℓ (h * θ₂.read ℓ) * θ₂.write ℓ = A.f ℓ (h * θ₁.read ℓ) * θ₁.write ℓ)
    (S : Fin L → Matrix d d ℝ) (x : Matrix T dIn ℝ) :
    eval A S θ₂ x = eval A S θ₁ x := by
  -- the hidden states agree, by induction along the network
  have hh : ∀ ℓ : Fin (L + 1), hidden A S θ₂ x ℓ = hidden A S θ₁ x ℓ := by
    intro ℓ
    induction ℓ using Fin.induction with
    | zero => rw [hidden_zero, hidden_zero, hE]
    | succ ℓ ih => rw [hidden_succ, hidden_succ, ih, hb]
  -- hence the outputs agree
  rw [eval, eval, hh, hD]

omit [Fintype T] [DecidableEq d] [Fintype dOut] in
/-- Helper: two networks of `A.sum B` whose first parts have the same `E` and `D`, and whose two
parts have the same output of every block on every hidden state, compute the same function: the
block of the sum is the sum of the blocks (`f_sum_mul`). -/
private theorem eval_sumOf_lit {A B : Arch T d L} (a a' : Params A dIn dOut)
    (b b' : Params B dIn dOut) (hE : a'.E = a.E) (hD : a'.D = a.D)
    (hA : ∀ ℓ (h : Matrix T d ℝ),
      A.f ℓ (h * a'.read ℓ) * a'.write ℓ = A.f ℓ (h * a.read ℓ) * a.write ℓ)
    (hB : ∀ ℓ (h : Matrix T d ℝ),
      B.f ℓ (h * b'.read ℓ) * b'.write ℓ = B.f ℓ (h * b.read ℓ) * b.write ℓ)
    (S : Fin L → Matrix d d ℝ) (x : Matrix T dIn ℝ) :
    eval (A.sum B) S (Params.sumOf a' b') x = eval (A.sum B) S (Params.sumOf a b) x := by
  refine eval_eq_of_blocks_lit (Params.sumOf a b) (Params.sumOf a' b') hE hD (fun ℓ h => ?_) S x
  rw [f_sum_mul, f_sum_mul]
  exact congrArg₂ (· + ·) (hA ℓ h) (hB ℓ h)

/-! ### Helpers: the symmetries inside the blocks keep the map of every block -/

omit [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (the private `headsQK_query_ath` of `Symmetry/AttentionHeads.lean`): the query
matrices of `θ.headsQK K` are `W_{Q,i} K_i`. -/
private theorem headsQK_query_lit {χ : Matrix T d ℝ → Matrix T d ℝ}
    (θ : Params (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut)
    (K : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ) (ℓ : Fin L) (i : H ℓ) :
    ((θ.headsQK K).read ℓ).submatrix id (fun k : dh ℓ => (i, Sum.inl k))
      = (θ.read ℓ).submatrix id (fun k : dh ℓ => (i, Sum.inl k))
        * (K ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ) := by
  ext a k
  rfl

omit [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (the private `headsQK_key_ath`): the key matrices of `θ.headsQK K` are
`W_{K,i} K_i^{-⊤}`. -/
private theorem headsQK_key_lit {χ : Matrix T d ℝ → Matrix T d ℝ}
    (θ : Params (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut)
    (K : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ) (ℓ : Fin L) (i : H ℓ) :
    ((θ.headsQK K).read ℓ).submatrix id (fun k : dh ℓ => (i, Sum.inr (Sum.inl k)))
      = (θ.read ℓ).submatrix id (fun k : dh ℓ => (i, Sum.inr (Sum.inl k)))
        * (((K ℓ i)⁻¹ : GL (dh ℓ) ℝ) : Matrix (dh ℓ) (dh ℓ) ℝ)ᵀ := by
  ext a k
  rfl

omit [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (the private `headsVO_value_ath`): the value matrices of `θ.headsVO K` are
`W_{V,i} K'_i`. -/
private theorem headsVO_value_lit {χ : Matrix T d ℝ → Matrix T d ℝ}
    (θ : Params (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut)
    (K : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ) (ℓ : Fin L) (i : H ℓ) :
    ((θ.headsVO K).read ℓ).submatrix id (fun k : dh ℓ => (i, Sum.inr (Sum.inr k)))
      = (θ.read ℓ).submatrix id (fun k : dh ℓ => (i, Sum.inr (Sum.inr k)))
        * (K ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ) := by
  ext a k
  rfl

omit [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (the private `headsVO_output_ath`): the output matrices of `θ.headsVO K` are
`K'_i^{-1} W_{O,i}`. -/
private theorem headsVO_output_lit {χ : Matrix T d ℝ → Matrix T d ℝ}
    (θ : Params (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut)
    (K : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ) (ℓ : Fin L) (i : H ℓ) :
    ((θ.headsVO K).write ℓ).submatrix (fun k : dh ℓ => (i, k)) id
      = (((K ℓ i)⁻¹ : GL (dh ℓ) ℝ) : Matrix (dh ℓ) (dh ℓ) ℝ)
        * (θ.write ℓ).submatrix (fun k : dh ℓ => (i, k)) id := by
  ext k b
  rfl

omit [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (the private `block_headsQK_ath`): the change of basis between queries and keys
leaves the output of every attention block unchanged:
`W_{Q,i} K (W_{K,i} K^{-⊤})ᵀ = W_{Q,i} W_{K,i}ᵀ`. -/
private theorem block_headsQK_lit {χ : Matrix T d ℝ → Matrix T d ℝ}
    (θ : Params (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut)
    (K : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ) (ℓ : Fin L) (h : Matrix T d ℝ) :
    (Arch.attention sees χ H dh).f ℓ (h * (θ.headsQK K).read ℓ) * (θ.headsQK K).write ℓ
      = (Arch.attention sees χ H dh).f ℓ (h * θ.read ℓ) * θ.write ℓ := by
  rw [f_attention_mul, f_attention_mul]
  unfold attentionBlock
  congr 1
  funext i
  dsimp only
  rw [headsQK_query_lit, headsQK_key_lit, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.mul_assoc, ← Matrix.mul_assoc (K ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ), Units.mul_inv,
    Matrix.one_mul]

omit [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (the private `block_headsVO_ath`): the change of basis between values and outputs
leaves the output of every attention block unchanged: `W_{V,i} K' K'^{-1} W_{O,i} = W_{V,i}
W_{O,i}`. -/
private theorem block_headsVO_lit {χ : Matrix T d ℝ → Matrix T d ℝ}
    (θ : Params (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut)
    (K : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ) (ℓ : Fin L) (h : Matrix T d ℝ) :
    (Arch.attention sees χ H dh).f ℓ (h * (θ.headsVO K).read ℓ) * (θ.headsVO K).write ℓ
      = (Arch.attention sees χ H dh).f ℓ (h * θ.read ℓ) * θ.write ℓ := by
  rw [f_attention_mul, f_attention_mul]
  unfold attentionBlock
  congr 1
  funext i
  dsimp only
  rw [headsVO_value_lit, headsVO_output_lit, Matrix.mul_assoc,
    ← Matrix.mul_assoc (K ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ), Units.mul_inv, Matrix.one_mul]

omit [Fintype T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (the block-wise form of `eval_rescale`, as `block_rescaleCurve_ibk` of
`Symmetry/InsideBlocksKinds.lean`): the rescaling of the values by `c ≠ 0` keeps the map of every
gated block: hidden unit `i` contributes `σ(z_i) (c⁻¹ u_i) (c a_i) = σ(z_i) u_i a_i`. -/
private theorem block_rescale_lit {χ : Matrix T d ℝ → Matrix T d ℝ}
    (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut) (c : ∀ ℓ, hid ℓ → ℝ)
    (hc : ∀ ℓ i, c ℓ i ≠ 0) (ℓ : Fin L) (n : Matrix T d ℝ) :
    (Arch.gated σ χ hid).f ℓ (n * (θ.rescale c).read ℓ) * (θ.rescale c).write ℓ
      = (Arch.gated σ χ hid).f ℓ (n * θ.read ℓ) * θ.write ℓ := by
  -- the gates are the same
  have hz : ∀ t i, (n * (θ.rescale c).read ℓ) t (Sum.inl i) = (n * θ.read ℓ) t (Sum.inl i) :=
    fun _ _ => rfl
  -- the values are divided by `c`
  have hu : ∀ t i, (n * (θ.rescale c).read ℓ) t (Sum.inr i)
      = (c ℓ i)⁻¹ * (n * θ.read ℓ) t (Sum.inr i) := by
    intro t i
    rw [Matrix.mul_apply, Matrix.mul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    show n t j * ((c ℓ i)⁻¹ * θ.read ℓ j (Sum.inr i))
      = (c ℓ i)⁻¹ * (n t j * θ.read ℓ j (Sum.inr i))
    ring
  -- compare term by term
  ext t k
  rw [Matrix.mul_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  show σ ((n * (θ.rescale c).read ℓ) t (Sum.inl i)) * (n * (θ.rescale c).read ℓ) t (Sum.inr i)
      * (c ℓ i * θ.write ℓ i k)
    = σ ((n * θ.read ℓ) t (Sum.inl i)) * (n * θ.read ℓ) t (Sum.inr i) * θ.write ℓ i k
  rw [hz, hu]
  -- `c⁻¹ c = 1`
  calc _ = ((c ℓ i)⁻¹ * c ℓ i)
        * (σ ((n * θ.read ℓ) t (Sum.inl i)) * (n * θ.read ℓ) t (Sum.inr i) * θ.write ℓ i k) := by
        ring
    _ = _ := by rw [inv_mul_cancel₀ (hc ℓ i), one_mul]

/-! ### Helpers: the derivative of the orbit map is injective -/

/-- Helper (the private `cancel_left_of_rank_lia` of
`Dimension/LocalIdentifiabilityAttention.lean`): a matrix `M` of rank equal to its number of
columns cancels on the left, `M X = M Y → X = Y` (its kernel is `0` by rank–nullity). -/
private theorem cancel_left_of_rank_lit {m n k : Type*} [Fintype n] (M : Matrix m n ℝ)
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

omit [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut]
  [∀ ℓ, DecidableEq (dh ℓ)] in
/-- Helper (the private `headDir_injective_lia` of
`Dimension/LocalIdentifiabilityAttention.lean`): if the query and the value matrix of every head
have rank `d_h`, the direction `headDirQK θ Γ + headDirVO θ Γ'` determines `Γ` and `Γ'`: the query
columns of head `i` move by `W_{Q,i} Γ_i`, its value columns by `W_{V,i} Γ'_i`. -/
private theorem headDir_injective_lit {χ : Matrix T d ℝ → Matrix T d ℝ}
    (θ : Params (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut)
    (hQ : ∀ ℓ (i : H ℓ), ((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k)).rank
      = Fintype.card (dh ℓ))
    (hV : ∀ ℓ (i : H ℓ),
      ((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))).rank
        = Fintype.card (dh ℓ))
    {Γ Γ' Δ Δ' : ∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ}
    (h : headDirQK θ Γ + headDirVO θ Γ' = headDirQK θ Δ + headDirVO θ Δ') :
    Γ = Δ ∧ Γ' = Δ' := by
  -- the entry `(a, p)` of the read of block `ℓ`
  have hr : ∀ ℓ a p, (headDirQK θ Γ + headDirVO θ Γ').read ℓ a p
      = (headDirQK θ Δ + headDirVO θ Δ').read ℓ a p := fun ℓ a p => by rw [h]
  refine ⟨?_, ?_⟩ <;> funext ℓ i
  · -- the query columns of head `i`: `W_{Q,i} Γ_i = W_{Q,i} Δ_i`, and `W_{Q,i}` has rank `d_h`
    refine cancel_left_of_rank_lit _ (hQ ℓ i) (Matrix.ext fun a k => ?_)
    have := hr ℓ a (i, Sum.inl k)
    simp only [Params.add_read, Matrix.add_apply, headDirQK, headDirVO, Matrix.of_apply,
      add_zero] at this
    simpa only [Matrix.mul_apply, Matrix.submatrix_apply, id] using this
  · -- the value columns of head `i`: `W_{V,i} Γ'_i = W_{V,i} Δ'_i`
    refine cancel_left_of_rank_lit _ (hV ℓ i) (Matrix.ext fun a k => ?_)
    have := hr ℓ a (i, Sum.inr (Sum.inr k))
    simp only [Params.add_read, Matrix.add_apply, headDirQK, headDirVO, Matrix.of_apply,
      zero_add] at this
    simpa only [Matrix.mul_apply, Matrix.submatrix_apply, id] using this

omit [∀ ℓ, DecidableEq (dh ℓ)] in
/-- Helper (the private `finrank_headFun_lia`): the families `Γ` of `d_h × d_h` matrices, one for
each head of each block, form a space of dimension `∑_ℓ H_ℓ d_{h,ℓ}²`. -/
private theorem finrank_headFun_lit :
    Module.finrank ℝ (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)
      = ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2 := by
  rw [Module.finrank_pi_fintype]
  simp only [Module.finrank_pi_fintype, Module.finrank_matrix, Module.finrank_self, mul_one,
    Finset.sum_const, Finset.card_univ, smul_eq_mul, sq]

/-! ### Helpers: neighborhoods of `0` in the chart of the symmetries -/

/-- Helper: for a continuous linear map `g` into the square matrices, the points `m` with
`exp (g m) ∈ V` form a neighborhood of `0`, when `V` is a neighborhood of `1`. -/
private theorem exp_preimage_mem_nhds_lit {M : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M]
    {n : Type*} [Fintype n] [DecidableEq n] (g : M →L[ℝ] Matrix n n ℝ) {V : Set (Matrix n n ℝ)}
    (hV : V ∈ 𝓝 (1 : Matrix n n ℝ)) :
    (fun m => NormedSpace.exp (g m)) ⁻¹' V ∈ 𝓝 (0 : M) := by
  -- `m ↦ exp (g m)` is continuous at `0`, with value `exp 0 = 1`
  have hc : ContinuousAt (fun m => NormedSpace.exp (g m)) 0 :=
    ContinuousAt.comp_of_eq (f := fun m => g m)
      (hasStrictFDerivAt_matrix_exp_zero (d := n)).continuousAt g.continuous.continuousAt
      (map_zero g)
  refine hc.preimage_mem_nhds ?_
  have h1 : NormedSpace.exp (g 0) = (1 : Matrix n n ℝ) := by
    rw [map_zero, NormedSpace.exp_zero]
  rw [h1]
  exact hV

omit [∀ ℓ, Fintype (H ℓ)] in
/-- Helper: for a continuous linear map `g` into the families of `d_h × d_h` matrices, the points
`m` with `exp (g m) ∈ W` (head by head) form a neighborhood of `0`, when `W` is a neighborhood of
`1`. -/
private theorem exp_heads_preimage_mem_nhds_lit {M : Type*} [NormedAddCommGroup M]
    [NormedSpace ℝ M] (g : M →L[ℝ] ∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)
    {W : Set (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)}
    (hW : W ∈ 𝓝 (1 : ∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)) :
    (fun m => fun ℓ i => NormedSpace.exp (g m ℓ i)) ⁻¹' W ∈ 𝓝 (0 : M) := by
  -- head by head, `m ↦ exp (g m ℓ i)` is continuous at `0`, with value `exp 0 = 1`
  have hc : ContinuousAt (fun m => fun ℓ (i : H ℓ) => NormedSpace.exp (g m ℓ i)) 0 :=
    continuousAt_pi.2 fun ℓ => continuousAt_pi.2 fun i =>
      ContinuousAt.comp_of_eq (f := fun m => g m ℓ i)
        (hasStrictFDerivAt_matrix_exp_zero (d := dh ℓ)).continuousAt
        ((continuous_apply i).comp ((continuous_apply ℓ).comp g.continuous)).continuousAt
        (by simp only [map_zero, Pi.zero_apply])
  refine hc.preimage_mem_nhds ?_
  have h1 : (fun ℓ (i : H ℓ) => NormedSpace.exp (g 0 ℓ i))
      = (1 : ∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) := by
    funext ℓ i
    simp only [map_zero, Pi.zero_apply, NormedSpace.exp_zero, Pi.one_apply]
  rw [h1]
  exact hW

omit [∀ ℓ, Fintype (hid ℓ)] in
/-- Helper: for a continuous linear map `g` into the families of reals, one for each hidden unit,
the points `m` with `e^{g m} ∈ W` form a neighborhood of `0`, when `W` is a neighborhood of `1`. -/
private theorem rexp_preimage_mem_nhds_lit {M : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M]
    (g : M →L[ℝ] ∀ ℓ, hid ℓ → ℝ) {W : Set (∀ ℓ, hid ℓ → ℝ)}
    (hW : W ∈ 𝓝 (1 : ∀ ℓ, hid ℓ → ℝ)) :
    (fun m => fun ℓ i => Real.exp (g m ℓ i)) ⁻¹' W ∈ 𝓝 (0 : M) := by
  have hc : Continuous (fun m => fun ℓ (i : hid ℓ) => Real.exp (g m ℓ i)) :=
    continuous_pi fun ℓ => continuous_pi fun i => Real.continuous_exp.comp
      ((continuous_apply i).comp ((continuous_apply ℓ).comp g.continuous))
  refine hc.continuousAt.preimage_mem_nhds ?_
  have h1 : (fun ℓ (i : hid ℓ) => Real.exp (g 0 ℓ i)) = (1 : ∀ ℓ, hid ℓ → ℝ) := by
    funext ℓ i
    simp only [map_zero, Pi.zero_apply, Real.exp_zero, Pi.one_apply]
  rw [h1]
  exact hW

/-! ### Helpers: generic parameters (copies of the private helpers of
`Dimension/UpperBoundTransformer.lean`) -/


omit [Fintype T] [DecidableEq d] in
/-- Helper (the private `analyticOnNhd_det_uba`): the determinant of a square matrix that depends
linearly on the parameters is an analytic function of the parameters. -/
private theorem analyticOnNhd_det_lit {A : Arch T d L} {n : Type*} [Fintype n] [DecidableEq n]
    (Φ : Params A dIn dOut →ₗ[ℝ] Matrix n n ℝ) :
    AnalyticOnNhd ℝ (fun θ => (Φ θ).det) Set.univ := by
  simp only [Matrix.det_apply']
  exact Finset.analyticOnNhd_fun_sum _ fun σ _ => analyticOnNhd_const.mul
    (Finset.analyticOnNhd_fun_prod _ fun i _ =>
      analyticOnNhd_linear ((Matrix.entryLinearMap ℝ ℝ (σ i) i).comp Φ))

/-- Helper (the private `exists_submatrix_eq_one_uba`): a matrix whose submatrix on the rows `r`
and the columns `c` (both injective) is the identity. -/
private theorem exists_submatrix_eq_one_lit {m p n : Type*} [DecidableEq n] {r : n → m}
    (hr : Function.Injective r) {c : n → p} (hc : Function.Injective c) :
    ∃ M : Matrix m p ℝ, M.submatrix r c = 1 := by
  classical
  refine ⟨Matrix.of fun a b => if ∃ x, r x = a ∧ c x = b then 1 else 0, ?_⟩
  ext x y
  simp [Matrix.one_apply, hr.eq_iff, hc.eq_iff]

omit [Fintype T] [DecidableEq d] in
/-- Helper (the private `ae_rank_read_cols_uba`): at generic parameters, `n ≤ d` distinct columns
`c` of the read of block `ℓ` form a matrix of rank `n`. -/
private theorem ae_rank_read_cols_lit {A : Arch T d L} (μ : Measure (Params A dIn dOut))
    [μ.IsAddHaarMeasure] (ℓ : Fin L) {n : Type*} [Fintype n] [DecidableEq n] {c : n → A.r ℓ}
    (hc : Function.Injective c) (hn : Fintype.card n ≤ Fintype.card d) :
    ∀ᵐ θ ∂μ, ((θ.read ℓ).submatrix id c).rank = Fintype.card n := by
  -- `n` rows `ρ`, and the square submatrix of the read on the rows `ρ` and the columns `c`
  obtain ⟨ρ⟩ := Function.Embedding.nonempty_of_card_le hn
  obtain ⟨M, hM⟩ := exists_submatrix_eq_one_lit ρ.injective hc
  let Φ : Params A dIn dOut →ₗ[ℝ] Matrix n n ℝ :=
    { toFun := fun θ => ((θ.read ℓ).submatrix id c).submatrix ρ id
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  -- it is the identity at the parameter whose read `ℓ` is `M`, so its determinant is not
  -- identically zero, and it is nonzero almost everywhere
  have hne : ∃ θ, (Φ θ).det ≠ 0 := by
    refine ⟨⟨0, Pi.single ℓ M, 0, 0⟩, ?_⟩
    show ((Pi.single (M := fun ℓ => Matrix d (A.r ℓ) ℝ) ℓ M ℓ).submatrix ρ c).det ≠ 0
    rw [Pi.single_eq_same, hM, Matrix.det_one]
    exact one_ne_zero
  filter_upwards [ae_ne_zero_of_analytic μ (analyticOnNhd_det_lit Φ) hne] with θ hθ
  -- an invertible `n × n` submatrix gives rank `≥ n`, and the rank is at most the width `n`
  have h1 : (((θ.read ℓ).submatrix id c).submatrix ρ id).rank = Fintype.card n :=
    Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hθ))
  have h2 : (((θ.read ℓ).submatrix id c).submatrix ρ id).rank
      ≤ ((θ.read ℓ).submatrix id c).rank :=
    Matrix.rank_submatrix_le _ ρ id
  have h3 := Matrix.rank_le_card_width ((θ.read ℓ).submatrix id c)
  omega

omit [DecidableEq d] in
/-- Helper (the private `ae_rank_QV_uba`, for the first part of a sum): at generic parameters the
query matrix and the value matrix of every head have rank `d_h`, when `d_h ≤ d`. The read of the
first part is made of columns of the read of the sum. -/
private theorem ae_rank_QV_lit {B : Arch T d L} {χ : Matrix T d ℝ → Matrix T d ℝ}
    (μ : Measure (Params ((Arch.attention (T := T) (d := d) sees χ H dh).sum B) dIn dOut))
    [μ.IsAddHaarMeasure] (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) :
    ∀ᵐ θ ∂μ, (∀ ℓ (i : H ℓ),
        ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k)).rank
          = Fintype.card (dh ℓ)) ∧
      ∀ ℓ (i : H ℓ),
        ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))).rank
          = Fintype.card (dh ℓ) := by
  classical
  -- finitely many conditions, two for each head of each block
  refine (ae_all_iff.2 fun ℓ => ae_all_iff.2 fun i => ?_).and
    (ae_all_iff.2 fun ℓ => ae_all_iff.2 fun i => ?_)
  · exact ae_rank_read_cols_lit μ ℓ (c := fun k : dh ℓ => Sum.inl (i, Sum.inl k))
      (fun _ _ h => Sum.inl_injective (Prod.mk.inj (Sum.inl_injective h)).2) (hdh ℓ)
  · exact ae_rank_read_cols_lit μ ℓ (c := fun k : dh ℓ => Sum.inl (i, Sum.inr (Sum.inr k)))
      (fun _ _ h => Sum.inr_injective (Sum.inr_injective (Prod.mk.inj (Sum.inl_injective h)).2))
      (hdh ℓ)

/-- Helper (the private `ae_rank_E_uba`): at generic parameters `E` has rank `d`, when
`d_in ≥ d`. -/
private theorem ae_rank_E_lit {A : Arch T d L} (μ : Measure (Params A dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn) :
    ∀ᵐ θ ∂μ, θ.E.rank = Fintype.card d := by
  -- `d` rows `ρ` of `E`, invertible at generic parameters
  obtain ⟨ρ⟩ := Function.Embedding.nonempty_of_card_le hdIn
  filter_upwards [ae_isUnit_det_submatrix μ] with θ hθ
  have h1 : (θ.E.submatrix ρ id).rank = Fintype.card d :=
    Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).2 (hθ.2.2.1 ρ))
  have h2 := Matrix.rank_submatrix_le θ.E ρ id
  have h3 := Matrix.rank_le_card_width θ.E
  omega

omit [Fintype T] [DecidableEq d] in
/-- Helper (`ae_value_ne_zero` of `Generic/Gated.lean`, for the second part of a sum): at generic
parameters no value column of the gated part of a read vanishes. -/
private theorem ae_value_ne_zero_lit [Nonempty d] {A : Arch T d L}
    {χ : Matrix T d ℝ → Matrix T d ℝ}
    (μ : Measure (Params (A.sum (Arch.gated (T := T) (d := d) σ χ hid)) dIn dOut))
    [μ.IsAddHaarMeasure] :
    ∀ᵐ θ ∂μ, ∀ ℓ i, (fun k => θ.sumSnd.read ℓ k (Sum.inr i)) ≠ 0 := by
  -- finitely many conditions, one for each hidden unit `i` of each block `ℓ`
  refine ae_all_iff.2 fun ℓ => ae_all_iff.2 fun i => ?_
  -- an entry `k₀` of the value column
  obtain k₀ : d := Classical.arbitrary d
  -- the entry `θ ↦ θ.read ℓ k₀ (inr (inr i))` is a linear functional of the parameters
  let l : Params (A.sum (Arch.gated (T := T) (d := d) σ χ hid)) dIn dOut →ₗ[ℝ] ℝ :=
    (Matrix.entryLinearMap ℝ ℝ k₀ (Sum.inr (Sum.inr i))).comp
      (Params.linRead (A := A.sum (Arch.gated (T := T) (d := d) σ χ hid)) (dIn := dIn)
        (dOut := dOut) ℓ)
  have hl : ∀ θ, l θ = θ.read ℓ k₀ (Sum.inr (Sum.inr i)) := fun θ => rfl
  -- it is not zero at the parameters whose reads have all entries `1`
  have h₁ : l ⟨0, fun _ => Matrix.of fun _ _ => 1, 0, 0⟩ ≠ 0 := by
    rw [hl]
    exact one_ne_zero
  -- an analytic function that is not identically zero is nonzero almost everywhere
  have hne : ∀ᵐ θ ∂μ, l θ ≠ 0 :=
    ae_ne_zero_of_analytic μ (analyticOnNhd_linear l) ⟨_, h₁⟩
  -- and a function with a nonzero entry is not zero
  filter_upwards [hne] with θ h hz
  exact h (by rw [hl]; exact congrFun hz k₀)

/-- **The argument common to the two statements of Proposition 4.5 for attention blocks and MLP
blocks.** Let `σ` and `χ` be real-analytic, `E` of rank `d`, the query and value matrices of every
head of rank `d_h`, and `ι₀ : N → Matrix d d ℝ` an injective linear map (all matrices, or the
antisymmetric ones) such that the change of basis `exp (ι₀ n)` at all hidden states preserves the
function. If `fd(θ) + dim N + s = P`, then every `θ'` near `θ` with the same function is
`(sumOf ((θ_A.headsQK K).headsVO K') θ_B).cob (exp ι₀ n) (exp ι₀ n)` with `exp (ι₀ n) ∈ V` and
`K, K' ∈ W`. The proof: `exists_mem_orbit_of_eval_eq` for the map
`(n, Γ, Γ') ↦ sumOf (cobExpHeads θ_A (fun _ => ι₀ n, Γ, Γ')) (cobExp θ_B (fun _ => ι₀ n))`, whose
derivative has the first part `cobDir θ_A (fun _ => ι₀ n) + headDirQK θ_A Γ + headDirVO θ_A Γ'`,
which determines `(n, Γ, Γ')`. -/
private theorem exists_orbit_mlp_lit {χ : Matrix T d ℝ → Matrix T d ℝ}
    (hσa : AnalyticOnNhd ℝ σ Set.univ) (hχ : AnalyticOnNhd ℝ χ Set.univ)
    (θ : Params (Arch.attentionMlp (T := T) (d := d) sees σ χ H dh hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d)
    (hQ : ∀ ℓ (i : H ℓ),
      ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k)).rank
        = Fintype.card (dh ℓ))
    (hV : ∀ ℓ (i : H ℓ),
      ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))).rank
        = Fintype.card (dh ℓ))
    {N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N] [FiniteDimensional ℝ N]
    (ι₀ : N →L[ℝ] Matrix d d ℝ) (hι₀ : Function.Injective ι₀)
    (hfd : funDim (Arch.attentionMlp sees σ χ H dh hid) 1 θ
        + (Module.finrank ℝ N + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
      = Module.finrank ℝ (Params
          (Arch.attentionMlp (T := T) (d := d) sees σ χ H dh hid) dIn dOut))
    (hpres : ∀ (n : N)
      (η : Params (Arch.attentionMlp (T := T) (d := d) sees σ χ H dh hid) dIn dOut)
      (x : Matrix T dIn ℝ), eval (Arch.attentionMlp sees σ χ H dh hid) 1
        (η.cob (fun _ => expGL (ι₀ n)) (fun _ => expGL (ι₀ n))) x
        = eval (Arch.attentionMlp sees σ χ H dh hid) 1 η x) :
    ∀ V ∈ 𝓝 (1 : Matrix d d ℝ), ∀ W ∈ 𝓝 (1 : ∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ),
      ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.attentionMlp sees σ χ H dh hid) 1 θ' x
        = eval (Arch.attentionMlp sees σ χ H dh hid) 1 θ x) →
        ∃ (n : N) (K K' : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ),
          NormedSpace.exp (ι₀ n) ∈ V
            ∧ (fun ℓ i => (K ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)) ∈ W
            ∧ (fun ℓ i => (K' ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)) ∈ W
            ∧ θ' = (Params.sumOf ((θ.sumFst.headsQK K).headsVO K') θ.sumSnd).cob
                (fun _ => expGL (ι₀ n)) (fun _ => expGL (ι₀ n)) := by
  intro V hVn W hWn
  -- the coordinates `n`, `Γ`, `Γ'` of `p = (n, Γ, Γ')`
  let πN : (N × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ))
      →L[ℝ] N := ContinuousLinearMap.fst ℝ _ _
  let πQ : (N × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ))
      →L[ℝ] (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) :=
    (ContinuousLinearMap.fst ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _)
  let πV : (N × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ))
      →L[ℝ] (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) :=
    (ContinuousLinearMap.snd ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _)
  -- the embeddings `p ↦ (fun _ => ι₀ n, Γ, Γ')` and `p ↦ fun _ => ι₀ n`: the same matrix at
  -- every hidden state, in both parts
  let ιA : (N × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ))
      →L[ℝ] (Fin (L + 1) → Matrix d d ℝ) × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)
        × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) :=
    (ContinuousLinearMap.pi fun _ : Fin (L + 1) => ι₀.comp πN).prod (πQ.prod πV)
  let ιB : (N × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ))
      →L[ℝ] (Fin (L + 1) → Matrix d d ℝ) :=
    ContinuousLinearMap.pi fun _ : Fin (L + 1) => ι₀.comp πN
  -- the two parts put together, a continuous linear map
  let Sm := LinearMap.toContinuousLinearMap (sumOfLin_lit
    (A := Arch.attention (T := T) (d := d) sees χ H dh) (B := Arch.mlp (T := T) (d := d) σ χ hid)
    (dIn := dIn) (dOut := dOut))
  -- the orbit map: the changes of basis inside the heads of the first part, then the change of
  -- basis `exp (ι₀ n)` of the hidden states in both parts
  let Φ : N × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) →
      Params (Arch.attentionMlp (T := T) (d := d) sees σ χ H dh hid) dIn dOut :=
    fun p => Params.sumOf (cobExpHeads θ.sumFst (ιA p)) (cobExp θ.sumSnd (ιB p))
  -- it is strictly differentiable at `0` (chain rule)
  obtain ⟨ΦA, hΦA, hΦAv⟩ := hasStrictFDerivAt_cobExpHeads θ.sumFst
  obtain ⟨ΦB, hΦB, hΦBv⟩ := hasStrictFDerivAt_cobExp θ.sumSnd
  have hA0 : HasStrictFDerivAt (cobExpHeads θ.sumFst) ΦA (ιA 0) := by
    rw [map_zero]
    exact hΦA
  have hB0 : HasStrictFDerivAt (cobExp θ.sumSnd) ΦB (ιB 0) := by
    rw [map_zero]
    exact hΦB
  have hc := Sm.hasStrictFDerivAt.comp
    (0 : N × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ))
    ((hA0.comp (0 : N × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)
      × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)) ιA.hasStrictFDerivAt).prodMk
      (hB0.comp (0 : N × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)
        × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)) ιB.hasStrictFDerivAt))
  have hΦ : HasStrictFDerivAt Φ (Sm.comp ((ΦA.comp ιA).prod (ΦB.comp ιB))) 0 := hc
  -- it passes through `θ`
  have hΦ0 : Φ 0 = θ := by
    show Params.sumOf (cobExpHeads θ.sumFst (ιA 0)) (cobExp θ.sumSnd (ιB 0)) = θ
    rw [map_zero, map_zero, cobExpHeads_zero, cobExp_zero]
    exact Params.sumOf_sumFst_sumSnd θ
  -- its derivative is injective: the first part of the derivative at `p` is
  -- `cobDir θ_A (fun _ => ι₀ n) + headDirQK θ_A Γ + headDirVO θ_A Γ'`; its `E` component `E ι₀ n`
  -- gives `n`, then the heads give `Γ` and `Γ'` (Lemma B.1)
  have hinj : Function.Injective (Sm.comp ((ΦA.comp ιA).prod (ΦB.comp ιB))) := by
    rintro ⟨n, Γ, Γ'⟩ ⟨n', Δ, Δ'⟩ h
    have h1 := congrArg Params.sumFst h
    have h2 : ΦA (ιA (n, Γ, Γ')) = ΦA (ιA (n', Δ, Δ')) := h1
    rw [hΦAv, hΦAv] at h2
    change cobDir θ.sumFst (fun _ => ι₀ n) + headDirQK θ.sumFst Γ + headDirVO θ.sumFst Γ'
      = cobDir θ.sumFst (fun _ => ι₀ n') + headDirQK θ.sumFst Δ + headDirVO θ.sumFst Δ' at h2
    have h0 : θ.E * ι₀ n = θ.E * ι₀ n' := by
      have hE0 := congrArg Params.E h2
      change θ.E * ι₀ n + 0 + 0 = θ.E * ι₀ n' + 0 + 0 at hE0
      simpa only [add_zero] using hE0
    have hn : ι₀ n = ι₀ n' := cancel_left_of_rank_lit θ.E hE h0
    rw [hn, add_assoc, add_assoc] at h2
    obtain ⟨hΓ, hΓ'⟩ := headDir_injective_lit θ.sumFst hQ hV (add_left_cancel h2)
    rw [hι₀ hn, hΓ, hΓ']
  -- at `p`, it is `θ` after the changes of basis `exp Γ`, `exp Γ'` inside the heads and the change
  -- of basis `exp (ι₀ n)` at all hidden states
  have hform : ∀ p : N × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)
      × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ), Φ p
      = (Params.sumOf ((θ.sumFst.headsQK fun ℓ i => expGL (p.2.1 ℓ i)).headsVO
          fun ℓ i => expGL (p.2.2 ℓ i)) θ.sumSnd).cob
        (fun _ => expGL (ι₀ p.1)) (fun _ => expGL (ι₀ p.1)) := by
    intro p
    rw [← sumOf_cob_lit]
    rfl
  -- so it keeps the function (Appendix B and Proposition 3.2 with identity skips)
  have hconst : ∀ᶠ p in 𝓝 (0 : N × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)
      × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)), ∀ x : Matrix T dIn ℝ,
      eval (Arch.attentionMlp sees σ χ H dh hid) 1 (Φ p) x
        = eval (Arch.attentionMlp sees σ χ H dh hid) 1 θ x := by
    refine Eventually.of_forall fun p x => ?_
    rw [hform p, hpres]
    have h1 := eval_sumOf_lit θ.sumFst
      ((θ.sumFst.headsQK fun ℓ i => expGL (p.2.1 ℓ i)).headsVO fun ℓ i => expGL (p.2.2 ℓ i))
      θ.sumSnd θ.sumSnd rfl rfl
      (fun ℓ h => (block_headsVO_lit (θ.sumFst.headsQK fun ℓ i => expGL (p.2.1 ℓ i))
        (fun ℓ i => expGL (p.2.2 ℓ i)) ℓ h).trans
        (block_headsQK_lit θ.sumFst (fun ℓ i => expGL (p.2.1 ℓ i)) ℓ h))
      (fun _ _ => rfl) 1 x
    rw [Params.sumOf_sumFst_sumSnd] at h1
    exact h1
  -- the triples `(n, Γ, Γ')` form a space of dimension `dim N + 2 ∑_ℓ H_ℓ d_{h,ℓ}²`
  have hdim : Module.finrank ℝ (N × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)
      × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ))
      = Module.finrank ℝ N + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2 := by
    rw [Module.finrank_prod, Module.finrank_prod, finrank_headFun_lit, two_mul]
  -- the `p` with `exp (ι₀ n) ∈ V`, `exp Γ ∈ W`, `exp Γ' ∈ W` form a neighborhood of `0`
  have hV' := exp_preimage_mem_nhds_lit (ι₀.comp πN) hVn
  have hW1 := exp_heads_preimage_mem_nhds_lit πQ hWn
  have hW2 := exp_heads_preimage_mem_nhds_lit πV hWn
  -- the orbit fills the level set near `θ`
  obtain ⟨U, hU, hUV⟩ := exists_mem_orbit_of_eval_eq (Arch.attentionMlp sees σ χ H dh hid) 1
    (fun ℓ => analyticOnNhd_f_sum (analyticOnNhd_f_attention sees χ H dh ℓ)
      (analyticOnNhd_f_mlp hσa ℓ)) hχ θ hΦ hΦ0 hinj hconst (by rw [hdim]; exact hfd) _
    (inter_mem hV' (inter_mem hW1 hW2))
  refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
  -- `K = exp Γ`, `K' = exp Γ'`
  obtain ⟨p, ⟨hpV, hpW1, hpW2⟩, hpθ⟩ := hUV θ' hθ' heq
  exact ⟨p.1, fun ℓ i => expGL (p.2.1 ℓ i), fun ℓ i => expGL (p.2.2 ℓ i), hpV, hpW1, hpW2,
    hpθ.symm.trans (hform p)⟩

/-! ### Attention blocks and MLP blocks -/

/-- **Proposition 4.5 of the skips paper, from the equality condition to local identifiability,
for a residual network of attention blocks and MLP blocks, without normalization:** if `E` has
rank `d`, the query and value matrices of every head have rank `d_h` and `θ` has the functional
dimension of Theorem 4.7, then every `θ'` near `θ` with the same function is `θ` after changes of
basis inside the heads, near the identity, and the change of basis by one invertible `G` near the
identity at all hidden states. -/
theorem exists_cob_heads_of_eval_eq_residual_attentionMlp
    (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (θ : Params
      (Arch.attentionMlp (T := T) (d := d) sees σ id H dh hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d)
    (hQ : ∀ ℓ (i : H ℓ),
      ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k)).rank
        = Fintype.card (dh ℓ))
    (hV : ∀ ℓ (i : H ℓ),
      ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))).rank
        = Fintype.card (dh ℓ))
    (hfd : funDim (Arch.attentionMlp sees σ id H dh hid) 1 θ
        + (Fintype.card d ^ 2
          + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
      = Module.finrank ℝ (Params
          (Arch.attentionMlp (T := T) (d := d) sees σ id H dh hid) dIn dOut)) :
    ∀ V ∈ 𝓝 (1 : Matrix d d ℝ), ∀ W ∈ 𝓝 (1 : ∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ),
      ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.attentionMlp sees σ id H dh hid) 1 θ' x
        = eval (Arch.attentionMlp sees σ id H dh hid) 1 θ x) →
        ∃ (G : GL d ℝ) (K K' : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ),
          (G : Matrix d d ℝ) ∈ V
            ∧ (fun ℓ i => (K ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)) ∈ W
            ∧ (fun ℓ i => (K' ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)) ∈ W
            ∧ θ' = (Params.sumOf ((θ.sumFst.headsQK K).headsVO K') θ.sumSnd).cob
                (fun _ => G) (fun _ => G) := by
  intro V hVn W hWn
  -- the `d × d` matrices form a space of dimension `d²`
  have hdimM : Module.finrank ℝ (Matrix d d ℝ) = Fintype.card d ^ 2 := by
    rw [Module.finrank_matrix, Module.finrank_self, mul_one, sq]
  -- the orbit of the changes of basis inside the heads and of one change of basis `exp m` at all
  -- hidden states fills the level set near `θ` (Proposition 3.2 with identity skips)
  obtain ⟨U, hU, hUV⟩ := exists_orbit_mlp_lit hσa analyticOnNhd_id θ hE hQ hV
    (ContinuousLinearMap.id ℝ (Matrix d d ℝ)) (fun _ _ h => h) (by rw [hdimM]; exact hfd)
    (fun _ η x => eval_cob_residual η x rfl _) V hVn W hWn
  refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
  -- `G = exp m`
  obtain ⟨m, K, K', hm, hK, hK', hθ'⟩ := hUV θ' hθ' heq
  exact ⟨expGL m, K, K', hm, hK, hK', hθ'⟩

/-- **Proposition 4.5 of the skips paper, from the equality condition to local identifiability,
for a residual network of attention blocks and MLP blocks, under pre-RMSNorm (`ε > 0`):** if `E`
has rank `d`, the query and value matrices of every head have rank `d_h` and `θ` has the
functional dimension of Theorem 4.7, then every `θ'` near `θ` with the same function is `θ` after
changes of basis inside the heads, near the identity, and the change of basis by one orthogonal
`Q` near the identity at all hidden states. -/
theorem exists_cob_heads_of_eval_eq_residual_attentionMlp_rmsNorm (hε : 0 < ε)
    (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (θ : Params
      (Arch.attentionMlp (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d)
    (hQ : ∀ ℓ (i : H ℓ),
      ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k)).rank
        = Fintype.card (dh ℓ))
    (hV : ∀ ℓ (i : H ℓ),
      ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))).rank
        = Fintype.card (dh ℓ))
    (hfd : funDim (Arch.attentionMlp sees σ (rmsNorm ε) H dh hid) 1 θ
        + (Fintype.card d * (Fintype.card d - 1) / 2
          + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
      = Module.finrank ℝ (Params
          (Arch.attentionMlp (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut)) :
    ∀ V ∈ 𝓝 (1 : Matrix d d ℝ), ∀ W ∈ 𝓝 (1 : ∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ),
      ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.attentionMlp sees σ (rmsNorm ε) H dh hid) 1 θ' x
        = eval (Arch.attentionMlp sees σ (rmsNorm ε) H dh hid) 1 θ x) →
        ∃ (Q : GL d ℝ) (K K' : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ),
          (Q : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ ∧ (Q : Matrix d d ℝ) ∈ V
            ∧ (fun ℓ i => (K ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)) ∈ W
            ∧ (fun ℓ i => (K' ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)) ∈ W
            ∧ θ' = (Params.sumOf ((θ.sumFst.headsQK K).headsVO K') θ.sumSnd).cob
                (fun _ => Q) (fun _ => Q) := by
  intro V hVn W hWn
  -- the antisymmetric matrices, inside all the matrices
  let ι₀ : antisymmetric d →L[ℝ] Matrix d d ℝ := (antisymmetric d).subtypeL
  -- the changes of basis `exp m`, `m` antisymmetric, are orthogonal
  have horth : ∀ m : antisymmetric d,
      ((expGL (ι₀ m) : GL d ℝ) : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ :=
    fun m => exp_mem_orthogonalGroup_of_transpose_eq_neg m.2
  -- the orbit of the changes of basis inside the heads and of one orthogonal change of basis
  -- `exp m` at all hidden states fills the level set near `θ` (Proposition 3.2 under pre-RMSNorm)
  obtain ⟨U, hU, hUV⟩ := exists_orbit_mlp_lit hσa (analyticOnNhd_rmsNorm hε) θ hE hQ hV ι₀
    Subtype.val_injective (by rw [finrank_antisymmetric]; exact hfd)
    (fun m η x => eval_cob_residual_rmsNorm η x ε rfl _ (horth m)) V hVn W hWn
  refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
  -- `Q = exp m`
  obtain ⟨m, K, K', hm, hK, hK', hθ'⟩ := hUV θ' hθ' heq
  exact ⟨expGL (ι₀ m), K, K', horth m, hm, hK, hK', hθ'⟩

/-- **Corollary 4.9 of the skips paper for attention blocks and MLP blocks, without
normalization:** for `d_in, d_out ≥ d ≥ 2`, heads of width `1 ≤ d_h ≤ d`, blocks of any widths and
a mask with a token that sees itself and another token, at almost every parameter `θ` of the
residual network, every `θ'` near `θ` with the same function is `θ` after changes of basis inside
the heads, near the identity, and the change of basis by one invertible `G` near the identity at
all hidden states. -/
theorem ae_exists_cob_heads_of_eval_eq_attentionMlp_residual
    (hσ : ∀ z, HasDerivAt σ (σ' z) z) (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (hU : UnitsRigid σ σ' dIn dOut (Σ ℓ, hid ℓ))
    (μ : Measure (Params
      (Arch.attentionMlp (T := T) (d := d) sees σ id H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ θ ∂μ, ∀ V ∈ 𝓝 (1 : Matrix d d ℝ), ∀ W ∈ 𝓝 (1 : ∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ),
      ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.attentionMlp sees σ id H dh hid) 1 θ' x
        = eval (Arch.attentionMlp sees σ id H dh hid) 1 θ x) →
        ∃ (G : GL d ℝ) (K K' : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ),
          (G : Matrix d d ℝ) ∈ V
            ∧ (fun ℓ i => (K ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)) ∈ W
            ∧ (fun ℓ i => (K' ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)) ∈ W
            ∧ θ' = (Params.sumOf ((θ.sumFst.headsQK K).headsVO K') θ.sumSnd).cob
                (fun _ => G) (fun _ => G) := by
  -- at generic parameters `E` has rank `d`, the query and value matrices of every head have
  -- rank `d_h`, and `fd(θ) = P - d² - s` (Theorem 4.7)
  filter_upwards [ae_rank_E_lit μ hdIn, ae_rank_QV_lit μ hdh,
    ae_funDim_attentionMlp_residual hσ hσa hU μ hd hdIn hdOut hdh hdh0 t₁ t₂ h12 hs2 hs1]
    with θ hE hQV hfd
  -- Proposition 4.5 at `θ`
  exact exists_cob_heads_of_eval_eq_residual_attentionMlp hσa θ hE hQV.1 hQV.2 hfd

/-- **Corollary 4.9 of the skips paper for attention blocks and MLP blocks, under pre-RMSNorm (`ε
> 0`):** for `d_in, d_out ≥ d ≥ 2`, heads of width `1 ≤ d_h ≤ d`, blocks of any widths and a mask
with a token that sees itself and another token, at almost every parameter `θ` of the residual
network, every `θ'` near `θ` with the same function is `θ` after changes of basis inside the
heads, near the identity, and the change of basis by one orthogonal `Q` near the identity at all
hidden states. -/
theorem ae_exists_cob_heads_of_eval_eq_attentionMlp_residual_rmsNorm (hε : 0 < ε)
    (hσ : ∀ z, HasDerivAt σ (σ' z) z) (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (hU : UnitsRigid σ σ' d d (Σ ℓ, hid ℓ))
    (μ : Measure (Params
      (Arch.attentionMlp (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ θ ∂μ, ∀ V ∈ 𝓝 (1 : Matrix d d ℝ), ∀ W ∈ 𝓝 (1 : ∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ),
      ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.attentionMlp sees σ (rmsNorm ε) H dh hid) 1 θ' x
        = eval (Arch.attentionMlp sees σ (rmsNorm ε) H dh hid) 1 θ x) →
        ∃ (Q : GL d ℝ) (K K' : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ),
          (Q : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ ∧ (Q : Matrix d d ℝ) ∈ V
            ∧ (fun ℓ i => (K ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)) ∈ W
            ∧ (fun ℓ i => (K' ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)) ∈ W
            ∧ θ' = (Params.sumOf ((θ.sumFst.headsQK K).headsVO K') θ.sumSnd).cob
                (fun _ => Q) (fun _ => Q) := by
  -- at generic parameters `E` has rank `d`, the query and value matrices of every head have
  -- rank `d_h`, and `fd(θ) = P - d(d-1)/2 - s` (Theorem 4.7 under pre-RMSNorm)
  filter_upwards [ae_rank_E_lit μ hdIn, ae_rank_QV_lit μ hdh,
    ae_funDim_attentionMlp_residual_rmsNorm hε hσ hσa hU μ hd hdIn hdOut hdh hdh0 t₁ t₂ h12 hs2
      hs1] with θ hE hQV hfd
  -- Proposition 4.5 under pre-RMSNorm at `θ`
  exact exists_cob_heads_of_eval_eq_residual_attentionMlp_rmsNorm hε hσa θ hE hQV.1 hQV.2 hfd

/-- **Corollary 4.9 of the skips paper for attention blocks and tanh blocks, without
normalization:** for `d_in, d_out ≥ d ≥ 2`, heads of width `1 ≤ d_h ≤ d`, blocks of any widths and
a mask with a token that sees itself and another token, at almost every parameter `θ` of the
residual network, every `θ'` near `θ` with the same function is `θ` after changes of basis inside
the heads, near the identity, and the change of basis by one invertible `G` near the identity at
all hidden states. -/
theorem ae_exists_cob_heads_of_eval_eq_attention_tanh_residual
    (μ : Measure (Params
      (Arch.attentionMlp (T := T) (d := d) sees Real.tanh id H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ θ ∂μ, ∀ V ∈ 𝓝 (1 : Matrix d d ℝ), ∀ W ∈ 𝓝 (1 : ∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ),
      ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.attentionMlp sees Real.tanh id H dh hid) 1 θ' x
        = eval (Arch.attentionMlp sees Real.tanh id H dh hid) 1 θ x) →
        ∃ (G : GL d ℝ) (K K' : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ),
          (G : Matrix d d ℝ) ∈ V
            ∧ (fun ℓ i => (K ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)) ∈ W
            ∧ (fun ℓ i => (K' ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)) ∈ W
            ∧ θ' = (Params.sumOf ((θ.sumFst.headsQK K).headsVO K') θ.sumSnd).cob
                (fun _ => G) (fun _ => G) := by
  -- tanh is analytic and its hidden units are rigid (Lemma B.3)
  exact ae_exists_cob_heads_of_eval_eq_attentionMlp_residual hasDerivAt_tanh analyticOnNhd_tanh
    (tanh_unitsRigid _ _ _) μ hd hdIn hdOut hdh hdh0 t₁ t₂ h12 hs2 hs1

/-- **Corollary 4.9 of the skips paper for attention blocks and tanh blocks, under pre-RMSNorm (`ε
> 0`):** for `d_in, d_out ≥ d ≥ 2`, heads of width `1 ≤ d_h ≤ d`, blocks of any widths and a mask
with a token that sees itself and another token, at almost every parameter `θ` of the residual
network, every `θ'` near `θ` with the same function is `θ` after changes of basis inside the
heads, near the identity, and the change of basis by one orthogonal `Q` near the identity at all
hidden states. -/
theorem ae_exists_cob_heads_of_eval_eq_attention_tanh_residual_rmsNorm (hε : 0 < ε)
    (μ : Measure (Params
      (Arch.attentionMlp (T := T) (d := d) sees Real.tanh (rmsNorm ε) H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ θ ∂μ, ∀ V ∈ 𝓝 (1 : Matrix d d ℝ), ∀ W ∈ 𝓝 (1 : ∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ),
      ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.attentionMlp sees Real.tanh (rmsNorm ε) H dh hid) 1 θ' x
        = eval (Arch.attentionMlp sees Real.tanh (rmsNorm ε) H dh hid) 1 θ x) →
        ∃ (Q : GL d ℝ) (K K' : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ),
          (Q : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ ∧ (Q : Matrix d d ℝ) ∈ V
            ∧ (fun ℓ i => (K ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)) ∈ W
            ∧ (fun ℓ i => (K' ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)) ∈ W
            ∧ θ' = (Params.sumOf ((θ.sumFst.headsQK K).headsVO K') θ.sumSnd).cob
                (fun _ => Q) (fun _ => Q) := by
  -- tanh is analytic and its hidden units are rigid (Lemma B.3)
  exact ae_exists_cob_heads_of_eval_eq_attentionMlp_residual_rmsNorm hε hasDerivAt_tanh
    analyticOnNhd_tanh (tanh_unitsRigid _ _ _) μ hd hdIn hdOut hdh hdh0 t₁ t₂ h12 hs2 hs1

/-- **Corollary 4.9 of the skips paper for attention blocks and GELU blocks, without
normalization:** for `d_in, d_out ≥ d ≥ 2`, heads of width `1 ≤ d_h ≤ d`, blocks of any widths and
a mask with a token that sees itself and another token, at almost every parameter `θ` of the
residual network, every `θ'` near `θ` with the same function is `θ` after changes of basis inside
the heads, near the identity, and the change of basis by one invertible `G` near the identity at
all hidden states. -/
theorem ae_exists_cob_heads_of_eval_eq_attention_gelu_residual
    (μ : Measure (Params
      (Arch.attentionMlp (T := T) (d := d) sees gelu id H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ θ ∂μ, ∀ V ∈ 𝓝 (1 : Matrix d d ℝ), ∀ W ∈ 𝓝 (1 : ∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ),
      ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.attentionMlp sees gelu id H dh hid) 1 θ' x
        = eval (Arch.attentionMlp sees gelu id H dh hid) 1 θ x) →
        ∃ (G : GL d ℝ) (K K' : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ),
          (G : Matrix d d ℝ) ∈ V
            ∧ (fun ℓ i => (K ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)) ∈ W
            ∧ (fun ℓ i => (K' ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)) ∈ W
            ∧ θ' = (Params.sumOf ((θ.sumFst.headsQK K).headsVO K') θ.sumSnd).cob
                (fun _ => G) (fun _ => G) := by
  -- GELU is analytic and its hidden units are rigid (Lemma B.3)
  exact ae_exists_cob_heads_of_eval_eq_attentionMlp_residual (σ' := geluDeriv) hasDerivAt_gelu
    analyticOnNhd_gelu (gelu_unitsRigid _ _ _) μ hd hdIn hdOut hdh hdh0 t₁ t₂ h12 hs2 hs1

/-- **Corollary 4.9 of the skips paper for attention blocks and GELU blocks, under pre-RMSNorm (`ε
> 0`):** for `d_in, d_out ≥ d ≥ 2`, heads of width `1 ≤ d_h ≤ d`, blocks of any widths and a mask
with a token that sees itself and another token, at almost every parameter `θ` of the residual
network, every `θ'` near `θ` with the same function is `θ` after changes of basis inside the
heads, near the identity, and the change of basis by one orthogonal `Q` near the identity at all
hidden states. -/
theorem ae_exists_cob_heads_of_eval_eq_attention_gelu_residual_rmsNorm (hε : 0 < ε)
    (μ : Measure (Params
      (Arch.attentionMlp (T := T) (d := d) sees gelu (rmsNorm ε) H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ θ ∂μ, ∀ V ∈ 𝓝 (1 : Matrix d d ℝ), ∀ W ∈ 𝓝 (1 : ∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ),
      ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.attentionMlp sees gelu (rmsNorm ε) H dh hid) 1 θ' x
        = eval (Arch.attentionMlp sees gelu (rmsNorm ε) H dh hid) 1 θ x) →
        ∃ (Q : GL d ℝ) (K K' : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ),
          (Q : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ ∧ (Q : Matrix d d ℝ) ∈ V
            ∧ (fun ℓ i => (K ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)) ∈ W
            ∧ (fun ℓ i => (K' ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)) ∈ W
            ∧ θ' = (Params.sumOf ((θ.sumFst.headsQK K).headsVO K') θ.sumSnd).cob
                (fun _ => Q) (fun _ => Q) := by
  -- GELU is analytic and its hidden units are rigid (Lemma B.3)
  exact ae_exists_cob_heads_of_eval_eq_attentionMlp_residual_rmsNorm (σ' := geluDeriv) hε
    hasDerivAt_gelu analyticOnNhd_gelu (gelu_unitsRigid _ _ _) μ hd hdIn hdOut hdh hdh0 t₁ t₂ h12
    hs2 hs1


/-- **The argument common to the two statements of Proposition 4.5 for attention blocks and gated
blocks.** As `exists_orbit_mlp_lit`, with the rescalings `e^α` of the values of the gated units:
the map `(n, Γ, Γ', α) ↦
sumOf (cobExpHeads θ_A (fun _ => ι₀ n, Γ, Γ')) (cobExpRescale θ_B (fun _ => ι₀ n, α))` has the
derivative with the first part `cobDir θ_A (fun _ => ι₀ n) + headDirQK θ_A Γ + headDirVO θ_A Γ'`
and the second part `cobDir θ_B (fun _ => ι₀ n) + rescaleDir θ_B α`; the first gives
`(n, Γ, Γ')`, then the value columns of the second give `α`. -/
private theorem exists_orbit_gated_lit {χ : Matrix T d ℝ → Matrix T d ℝ}
    (hσa : AnalyticOnNhd ℝ σ Set.univ) (hχ : AnalyticOnNhd ℝ χ Set.univ)
    (θ : Params (Arch.attentionGated (T := T) (d := d) sees σ χ H dh hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d)
    (hQ : ∀ ℓ (i : H ℓ),
      ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k)).rank
        = Fintype.card (dh ℓ))
    (hV : ∀ ℓ (i : H ℓ),
      ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))).rank
        = Fintype.card (dh ℓ))
    (hv : ∀ ℓ i, (fun k => θ.sumSnd.read ℓ k (Sum.inr i)) ≠ 0)
    {N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N] [FiniteDimensional ℝ N]
    (ι₀ : N →L[ℝ] Matrix d d ℝ) (hι₀ : Function.Injective ι₀)
    (hfd : funDim (Arch.attentionGated sees σ χ H dh hid) 1 θ
        + (Module.finrank ℝ N + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
          + ∑ ℓ, Fintype.card (hid ℓ)))
      = Module.finrank ℝ (Params
          (Arch.attentionGated (T := T) (d := d) sees σ χ H dh hid) dIn dOut))
    (hpres : ∀ (n : N)
      (η : Params (Arch.attentionGated (T := T) (d := d) sees σ χ H dh hid) dIn dOut)
      (x : Matrix T dIn ℝ), eval (Arch.attentionGated sees σ χ H dh hid) 1
        (η.cob (fun _ => expGL (ι₀ n)) (fun _ => expGL (ι₀ n))) x
        = eval (Arch.attentionGated sees σ χ H dh hid) 1 η x) :
    ∀ V ∈ 𝓝 (1 : Matrix d d ℝ), ∀ W ∈ 𝓝 (1 : ∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ),
      ∀ Wc ∈ 𝓝 (1 : ∀ ℓ, hid ℓ → ℝ), ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.attentionGated sees σ χ H dh hid) 1 θ' x
        = eval (Arch.attentionGated sees σ χ H dh hid) 1 θ x) →
        ∃ (n : N) (K K' : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ) (c : ∀ ℓ, hid ℓ → ℝ),
          NormedSpace.exp (ι₀ n) ∈ V
            ∧ (fun ℓ i => (K ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)) ∈ W
            ∧ (fun ℓ i => (K' ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)) ∈ W
            ∧ c ∈ Wc ∧ (∀ ℓ i, 0 < c ℓ i)
            ∧ θ' = (Params.sumOf ((θ.sumFst.headsQK K).headsVO K') (θ.sumSnd.rescale c)).cob
                (fun _ => expGL (ι₀ n)) (fun _ => expGL (ι₀ n)) := by
  intro V hVn W hWn Wc hWc
  -- the coordinates `n`, `Γ`, `Γ'`, `α` of `p = (n, Γ, Γ', α)`
  let πN : (N × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)
      × (∀ ℓ, hid ℓ → ℝ)) →L[ℝ] N := ContinuousLinearMap.fst ℝ _ _
  let πQ : (N × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)
      × (∀ ℓ, hid ℓ → ℝ)) →L[ℝ] (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) :=
    (ContinuousLinearMap.fst ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _)
  let πV : (N × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)
      × (∀ ℓ, hid ℓ → ℝ)) →L[ℝ] (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) :=
    (ContinuousLinearMap.fst ℝ _ _).comp
      ((ContinuousLinearMap.snd ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _))
  let πα : (N × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)
      × (∀ ℓ, hid ℓ → ℝ)) →L[ℝ] (∀ ℓ, hid ℓ → ℝ) :=
    (ContinuousLinearMap.snd ℝ _ _).comp
      ((ContinuousLinearMap.snd ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _))
  -- the embeddings `p ↦ (fun _ => ι₀ n, Γ, Γ')` and `p ↦ (fun _ => ι₀ n, α)`
  let ιA : (N × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)
      × (∀ ℓ, hid ℓ → ℝ)) →L[ℝ] (Fin (L + 1) → Matrix d d ℝ)
        × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) :=
    (ContinuousLinearMap.pi fun _ : Fin (L + 1) => ι₀.comp πN).prod (πQ.prod πV)
  let ιB : (N × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)
      × (∀ ℓ, hid ℓ → ℝ)) →L[ℝ] (Fin (L + 1) → Matrix d d ℝ) × (∀ ℓ, hid ℓ → ℝ) :=
    (ContinuousLinearMap.pi fun _ : Fin (L + 1) => ι₀.comp πN).prod πα
  -- the two parts put together, a continuous linear map
  let Sm := LinearMap.toContinuousLinearMap (sumOfLin_lit
    (A := Arch.attention (T := T) (d := d) sees χ H dh)
    (B := Arch.gated (T := T) (d := d) σ χ hid) (dIn := dIn) (dOut := dOut))
  -- the orbit map: the changes of basis inside the heads of the first part, the rescalings of the
  -- values of the second, then the change of basis `exp (ι₀ n)` of the hidden states
  let Φ : N × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)
      × (∀ ℓ, hid ℓ → ℝ) →
      Params (Arch.attentionGated (T := T) (d := d) sees σ χ H dh hid) dIn dOut :=
    fun p => Params.sumOf (cobExpHeads θ.sumFst (ιA p)) (cobExpRescale θ.sumSnd (ιB p))
  -- it is strictly differentiable at `0` (chain rule)
  obtain ⟨ΦA, hΦA, hΦAv⟩ := hasStrictFDerivAt_cobExpHeads θ.sumFst
  obtain ⟨ΦB, hΦB, hΦBv⟩ := hasStrictFDerivAt_cobExpRescale θ.sumSnd
  have hA0 : HasStrictFDerivAt (cobExpHeads θ.sumFst) ΦA (ιA 0) := by
    rw [map_zero]
    exact hΦA
  have hB0 : HasStrictFDerivAt (cobExpRescale θ.sumSnd) ΦB (ιB 0) := by
    rw [map_zero]
    exact hΦB
  have hc := Sm.hasStrictFDerivAt.comp
    (0 : N × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)
      × (∀ ℓ, hid ℓ → ℝ))
    ((hA0.comp (0 : N × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)
      × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) × (∀ ℓ, hid ℓ → ℝ)) ιA.hasStrictFDerivAt).prodMk
      (hB0.comp (0 : N × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)
        × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) × (∀ ℓ, hid ℓ → ℝ)) ιB.hasStrictFDerivAt))
  have hΦ : HasStrictFDerivAt Φ (Sm.comp ((ΦA.comp ιA).prod (ΦB.comp ιB))) 0 := hc
  -- it passes through `θ`
  have hΦ0 : Φ 0 = θ := by
    show Params.sumOf (cobExpHeads θ.sumFst (ιA 0)) (cobExpRescale θ.sumSnd (ιB 0)) = θ
    rw [map_zero, map_zero, cobExpHeads_zero, cobExpRescale_zero]
    exact Params.sumOf_sumFst_sumSnd θ
  -- its derivative is injective: the first part gives `(n, Γ, Γ')` as for attention blocks, then
  -- the value column `e_i` of the second part moves by `-ι₀ n e_i - α_i e_i`, which gives `α`
  have hinj : Function.Injective (Sm.comp ((ΦA.comp ιA).prod (ΦB.comp ιB))) := by
    rintro ⟨n, Γ, Γ', α⟩ ⟨n', Δ, Δ', β⟩ h
    have h1 := congrArg Params.sumFst h
    have h2 : ΦA (ιA (n, Γ, Γ', α)) = ΦA (ιA (n', Δ, Δ', β)) := h1
    rw [hΦAv, hΦAv] at h2
    change cobDir θ.sumFst (fun _ => ι₀ n) + headDirQK θ.sumFst Γ + headDirVO θ.sumFst Γ'
      = cobDir θ.sumFst (fun _ => ι₀ n') + headDirQK θ.sumFst Δ + headDirVO θ.sumFst Δ' at h2
    have h0 : θ.E * ι₀ n = θ.E * ι₀ n' := by
      have hE0 := congrArg Params.E h2
      change θ.E * ι₀ n + 0 + 0 = θ.E * ι₀ n' + 0 + 0 at hE0
      simpa only [add_zero] using hE0
    have hn : ι₀ n = ι₀ n' := cancel_left_of_rank_lit θ.E hE h0
    have hα : α = β := by
      funext ℓ i
      obtain ⟨k, hk⟩ := Function.ne_iff.mp (hv ℓ i)
      have h3 : (ΦB (ιB (n, Γ, Γ', α))).read ℓ k (Sum.inr i)
          = (ΦB (ιB (n', Δ, Δ', β))).read ℓ k (Sum.inr i) :=
        congrFun (congrFun (congrArg (fun η => η.read ℓ) h) k) (Sum.inr (Sum.inr i))
      rw [hΦBv, hΦBv] at h3
      change -(ι₀ n * θ.sumSnd.read ℓ) k (Sum.inr i) + -(α ℓ i) * θ.sumSnd.read ℓ k (Sum.inr i)
        = -(ι₀ n' * θ.sumSnd.read ℓ) k (Sum.inr i)
          + -(β ℓ i) * θ.sumSnd.read ℓ k (Sum.inr i) at h3
      rw [hn, add_right_inj] at h3
      exact neg_inj.mp (mul_right_cancel₀ hk h3)
    rw [hn, add_assoc, add_assoc] at h2
    obtain ⟨hΓ, hΓ'⟩ := headDir_injective_lit θ.sumFst hQ hV (add_left_cancel h2)
    rw [hι₀ hn, hΓ, hΓ', hα]
  -- at `p`, it is `θ` after the changes of basis `exp Γ`, `exp Γ'` inside the heads, the
  -- rescalings `e^α` and the change of basis `exp (ι₀ n)` at all hidden states
  have hform : ∀ p : N × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)
      × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) × (∀ ℓ, hid ℓ → ℝ), Φ p
      = (Params.sumOf ((θ.sumFst.headsQK fun ℓ i => expGL (p.2.1 ℓ i)).headsVO
          fun ℓ i => expGL (p.2.2.1 ℓ i))
          (θ.sumSnd.rescale fun ℓ i => Real.exp (p.2.2.2 ℓ i))).cob
        (fun _ => expGL (ι₀ p.1)) (fun _ => expGL (ι₀ p.1)) := by
    intro p
    rw [← sumOf_cob_lit]
    rfl
  -- so it keeps the function (Appendix B and Proposition 3.2 with identity skips)
  have hconst : ∀ᶠ p in 𝓝 (0 : N × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)
      × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) × (∀ ℓ, hid ℓ → ℝ)), ∀ x : Matrix T dIn ℝ,
      eval (Arch.attentionGated sees σ χ H dh hid) 1 (Φ p) x
        = eval (Arch.attentionGated sees σ χ H dh hid) 1 θ x := by
    refine Eventually.of_forall fun p x => ?_
    rw [hform p, hpres]
    have h1 := eval_sumOf_lit θ.sumFst
      ((θ.sumFst.headsQK fun ℓ i => expGL (p.2.1 ℓ i)).headsVO fun ℓ i => expGL (p.2.2.1 ℓ i))
      θ.sumSnd (θ.sumSnd.rescale fun ℓ i => Real.exp (p.2.2.2 ℓ i)) rfl rfl
      (fun ℓ h => (block_headsVO_lit (θ.sumFst.headsQK fun ℓ i => expGL (p.2.1 ℓ i))
        (fun ℓ i => expGL (p.2.2.1 ℓ i)) ℓ h).trans
        (block_headsQK_lit θ.sumFst (fun ℓ i => expGL (p.2.1 ℓ i)) ℓ h))
      (fun ℓ h => block_rescale_lit θ.sumSnd (fun ℓ i => Real.exp (p.2.2.2 ℓ i))
        (fun ℓ i => (Real.exp_pos _).ne') ℓ h) 1 x
    rw [Params.sumOf_sumFst_sumSnd] at h1
    exact h1
  -- the `p` form a space of dimension `dim N + 2 ∑_ℓ H_ℓ d_{h,ℓ}² + ∑_ℓ d_hidden,ℓ`
  have hdim : Module.finrank ℝ (N × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)
      × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) × (∀ ℓ, hid ℓ → ℝ))
      = Module.finrank ℝ N + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
        + ∑ ℓ, Fintype.card (hid ℓ)) := by
    rw [Module.finrank_prod, Module.finrank_prod, Module.finrank_prod, finrank_headFun_lit,
      Module.finrank_pi_fintype]
    simp only [Module.finrank_fintype_fun_eq_card]
    ring
  -- the `p` with `exp (ι₀ n) ∈ V`, `exp Γ, exp Γ' ∈ W`, `e^α ∈ Wc` form a neighborhood of `0`
  have hV' := exp_preimage_mem_nhds_lit (ι₀.comp πN) hVn
  have hW1 := exp_heads_preimage_mem_nhds_lit πQ hWn
  have hW2 := exp_heads_preimage_mem_nhds_lit πV hWn
  have hW3 := rexp_preimage_mem_nhds_lit πα hWc
  -- the orbit fills the level set near `θ`
  obtain ⟨U, hU, hUV⟩ := exists_mem_orbit_of_eval_eq (Arch.attentionGated sees σ χ H dh hid) 1
    (fun ℓ => analyticOnNhd_f_sum (analyticOnNhd_f_attention sees χ H dh ℓ)
      (analyticOnNhd_f_gated hσa ℓ)) hχ θ hΦ hΦ0 hinj hconst (by rw [hdim]; exact hfd) _
    (inter_mem hV' (inter_mem hW1 (inter_mem hW2 hW3)))
  refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
  -- `K = exp Γ`, `K' = exp Γ'`, `c = e^α`
  obtain ⟨p, ⟨hpV, hpW1, hpW2, hpW3⟩, hpθ⟩ := hUV θ' hθ' heq
  exact ⟨p.1, fun ℓ i => expGL (p.2.1 ℓ i), fun ℓ i => expGL (p.2.2.1 ℓ i),
    fun ℓ i => Real.exp (p.2.2.2 ℓ i), hpV, hpW1, hpW2, hpW3, fun ℓ i => Real.exp_pos _,
    hpθ.symm.trans (hform p)⟩

/-! ### Attention blocks and gated blocks -/

/-- **Proposition 4.5 of the skips paper, from the equality condition to local identifiability,
for a residual network of attention blocks and gated blocks, without normalization:** if `E` has
rank `d`, the query and value matrices of every head have rank `d_h`, no value column of a gated
unit vanishes and `θ` has the functional dimension of Theorem 4.7, then every `θ'` near `θ` with
the same function is `θ` after changes of basis inside the heads and rescalings of the values of
the gated units, near the identity, and the change of basis by one invertible `G` near the
identity at all hidden states. -/
theorem exists_cob_heads_of_eval_eq_residual_attentionGated
    (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (θ : Params
      (Arch.attentionGated (T := T) (d := d) sees σ id H dh hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d)
    (hQ : ∀ ℓ (i : H ℓ),
      ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k)).rank
        = Fintype.card (dh ℓ))
    (hV : ∀ ℓ (i : H ℓ),
      ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))).rank
        = Fintype.card (dh ℓ))
    (hv : ∀ ℓ i, (fun k => θ.sumSnd.read ℓ k (Sum.inr i)) ≠ 0)
    (hfd : funDim (Arch.attentionGated sees σ id H dh hid) 1 θ
        + (Fintype.card d ^ 2
          + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
            + ∑ ℓ, Fintype.card (hid ℓ)))
      = Module.finrank ℝ (Params
          (Arch.attentionGated (T := T) (d := d) sees σ id H dh hid) dIn dOut)) :
    ∀ V ∈ 𝓝 (1 : Matrix d d ℝ), ∀ W ∈ 𝓝 (1 : ∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ),
      ∀ Wc ∈ 𝓝 (1 : ∀ ℓ, hid ℓ → ℝ), ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.attentionGated sees σ id H dh hid) 1 θ' x
        = eval (Arch.attentionGated sees σ id H dh hid) 1 θ x) →
        ∃ (G : GL d ℝ) (K K' : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ) (c : ∀ ℓ, hid ℓ → ℝ),
          (G : Matrix d d ℝ) ∈ V
            ∧ (fun ℓ i => (K ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)) ∈ W
            ∧ (fun ℓ i => (K' ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)) ∈ W
            ∧ c ∈ Wc ∧ (∀ ℓ i, 0 < c ℓ i)
            ∧ θ' = (Params.sumOf ((θ.sumFst.headsQK K).headsVO K') (θ.sumSnd.rescale c)).cob
                (fun _ => G) (fun _ => G) := by
  intro V hVn W hWn Wc hWc
  -- the `d × d` matrices form a space of dimension `d²`
  have hdimM : Module.finrank ℝ (Matrix d d ℝ) = Fintype.card d ^ 2 := by
    rw [Module.finrank_matrix, Module.finrank_self, mul_one, sq]
  -- the orbit of the changes of basis inside the heads, of the rescalings of the values and of
  -- one change of basis `exp m` at all hidden states fills the level set near `θ`
  obtain ⟨U, hU, hUV⟩ := exists_orbit_gated_lit hσa analyticOnNhd_id θ hE hQ hV hv
    (ContinuousLinearMap.id ℝ (Matrix d d ℝ)) (fun _ _ h => h) (by rw [hdimM]; exact hfd)
    (fun _ η x => eval_cob_residual η x rfl _) V hVn W hWn Wc hWc
  refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
  -- `G = exp m`
  obtain ⟨m, K, K', c, hm, hK, hK', hc, hc0, hθ'⟩ := hUV θ' hθ' heq
  exact ⟨expGL m, K, K', c, hm, hK, hK', hc, hc0, hθ'⟩

/-- **Proposition 4.5 of the skips paper, from the equality condition to local identifiability,
for a residual network of attention blocks and gated blocks, under pre-RMSNorm (`ε > 0`):** if `E`
has rank `d`, the query and value matrices of every head have rank `d_h`, no value column of a
gated unit vanishes and `θ` has the functional dimension of Theorem 4.7, then every `θ'` near `θ`
with the same function is `θ` after changes of basis inside the heads and rescalings of the values
of the gated units, near the identity, and the change of basis by one orthogonal `Q` near the
identity at all hidden states. -/
theorem exists_cob_heads_of_eval_eq_residual_attentionGated_rmsNorm (hε : 0 < ε)
    (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (θ : Params
      (Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d)
    (hQ : ∀ ℓ (i : H ℓ),
      ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k)).rank
        = Fintype.card (dh ℓ))
    (hV : ∀ ℓ (i : H ℓ),
      ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))).rank
        = Fintype.card (dh ℓ))
    (hv : ∀ ℓ i, (fun k => θ.sumSnd.read ℓ k (Sum.inr i)) ≠ 0)
    (hfd : funDim (Arch.attentionGated sees σ (rmsNorm ε) H dh hid) 1 θ
        + (Fintype.card d * (Fintype.card d - 1) / 2
          + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
            + ∑ ℓ, Fintype.card (hid ℓ)))
      = Module.finrank ℝ (Params
          (Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut)) :
    ∀ V ∈ 𝓝 (1 : Matrix d d ℝ), ∀ W ∈ 𝓝 (1 : ∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ),
      ∀ Wc ∈ 𝓝 (1 : ∀ ℓ, hid ℓ → ℝ), ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.attentionGated sees σ (rmsNorm ε) H dh hid) 1 θ' x
        = eval (Arch.attentionGated sees σ (rmsNorm ε) H dh hid) 1 θ x) →
        ∃ (Q : GL d ℝ) (K K' : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ) (c : ∀ ℓ, hid ℓ → ℝ),
          (Q : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ ∧ (Q : Matrix d d ℝ) ∈ V
            ∧ (fun ℓ i => (K ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)) ∈ W
            ∧ (fun ℓ i => (K' ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)) ∈ W
            ∧ c ∈ Wc ∧ (∀ ℓ i, 0 < c ℓ i)
            ∧ θ' = (Params.sumOf ((θ.sumFst.headsQK K).headsVO K') (θ.sumSnd.rescale c)).cob
                (fun _ => Q) (fun _ => Q) := by
  intro V hVn W hWn Wc hWc
  -- the antisymmetric matrices, inside all the matrices
  let ι₀ : antisymmetric d →L[ℝ] Matrix d d ℝ := (antisymmetric d).subtypeL
  -- the changes of basis `exp m`, `m` antisymmetric, are orthogonal
  have horth : ∀ m : antisymmetric d,
      ((expGL (ι₀ m) : GL d ℝ) : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ :=
    fun m => exp_mem_orthogonalGroup_of_transpose_eq_neg m.2
  -- the orbit of the changes of basis inside the heads, of the rescalings of the values and of
  -- one orthogonal change of basis `exp m` at all hidden states fills the level set near `θ`
  obtain ⟨U, hU, hUV⟩ := exists_orbit_gated_lit hσa (analyticOnNhd_rmsNorm hε) θ hE hQ hV hv ι₀
    Subtype.val_injective (by rw [finrank_antisymmetric]; exact hfd)
    (fun m η x => eval_cob_residual_rmsNorm η x ε rfl _ (horth m)) V hVn W hWn Wc hWc
  refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
  -- `Q = exp m`
  obtain ⟨m, K, K', c, hm, hK, hK', hc, hc0, hθ'⟩ := hUV θ' hθ' heq
  exact ⟨expGL (ι₀ m), K, K', c, horth m, hm, hK, hK', hc, hc0, hθ'⟩

/-- **Corollary 4.9 of the skips paper for attention blocks and gated blocks, without
normalization:** for `d_in, d_out ≥ d ≥ 2`, heads of width `1 ≤ d_h ≤ d`, blocks of any widths and
a mask with a token that sees itself and another token, at almost every parameter `θ` of the
residual network, every `θ'` near `θ` with the same function is `θ` after changes of basis inside
the heads and rescalings of the values of the gated units, near the identity, and the change of
basis by one invertible `G` near the identity at all hidden states. -/
theorem ae_exists_cob_heads_of_eval_eq_attentionGated_residual
    (hσ : ∀ z, HasDerivAt σ (σ' z) z) (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (hU : GatedUnitsRescale σ σ' dIn dOut (Σ ℓ, hid ℓ))
    (μ : Measure (Params
      (Arch.attentionGated (T := T) (d := d) sees σ id H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ θ ∂μ, ∀ V ∈ 𝓝 (1 : Matrix d d ℝ), ∀ W ∈ 𝓝 (1 : ∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ),
      ∀ Wc ∈ 𝓝 (1 : ∀ ℓ, hid ℓ → ℝ), ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.attentionGated sees σ id H dh hid) 1 θ' x
        = eval (Arch.attentionGated sees σ id H dh hid) 1 θ x) →
        ∃ (G : GL d ℝ) (K K' : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ) (c : ∀ ℓ, hid ℓ → ℝ),
          (G : Matrix d d ℝ) ∈ V
            ∧ (fun ℓ i => (K ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)) ∈ W
            ∧ (fun ℓ i => (K' ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)) ∈ W
            ∧ c ∈ Wc ∧ (∀ ℓ i, 0 < c ℓ i)
            ∧ θ' = (Params.sumOf ((θ.sumFst.headsQK K).headsVO K') (θ.sumSnd.rescale c)).cob
                (fun _ => G) (fun _ => G) := by
  -- `d ≥ 2`, so `d` is not empty
  have : Nonempty d := Fintype.card_pos_iff.mp (by omega)
  -- at generic parameters `E` has rank `d`, the query and value matrices of every head have
  -- rank `d_h`, no value column of a gated unit vanishes, and `fd(θ) = P - d² - s` (Theorem 4.7)
  filter_upwards [ae_rank_E_lit μ hdIn, ae_rank_QV_lit μ hdh, ae_value_ne_zero_lit μ,
    ae_funDim_attentionGated_residual hσ hσa hU μ hd hdIn hdOut hdh hdh0 t₁ t₂ h12 hs2 hs1]
    with θ hE hQV hv hfd
  -- Proposition 4.5 at `θ`
  exact exists_cob_heads_of_eval_eq_residual_attentionGated hσa θ hE hQV.1 hQV.2 hv hfd

/-- **Corollary 4.9 of the skips paper for attention blocks and gated blocks, under pre-RMSNorm
(`ε > 0`):** for `d_in, d_out ≥ d ≥ 2`, heads of width `1 ≤ d_h ≤ d`, blocks of any widths and a
mask with a token that sees itself and another token, at almost every parameter `θ` of the
residual network, every `θ'` near `θ` with the same function is `θ` after changes of basis inside
the heads and rescalings of the values of the gated units, near the identity, and the change of
basis by one orthogonal `Q` near the identity at all hidden states. -/
theorem ae_exists_cob_heads_of_eval_eq_attentionGated_residual_rmsNorm (hε : 0 < ε)
    (hσ : ∀ z, HasDerivAt σ (σ' z) z) (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (hU : GatedUnitsRescale σ σ' d d (Σ ℓ, hid ℓ))
    (μ : Measure (Params
      (Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ θ ∂μ, ∀ V ∈ 𝓝 (1 : Matrix d d ℝ), ∀ W ∈ 𝓝 (1 : ∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ),
      ∀ Wc ∈ 𝓝 (1 : ∀ ℓ, hid ℓ → ℝ), ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.attentionGated sees σ (rmsNorm ε) H dh hid) 1 θ' x
        = eval (Arch.attentionGated sees σ (rmsNorm ε) H dh hid) 1 θ x) →
        ∃ (Q : GL d ℝ) (K K' : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ) (c : ∀ ℓ, hid ℓ → ℝ),
          (Q : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ ∧ (Q : Matrix d d ℝ) ∈ V
            ∧ (fun ℓ i => (K ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)) ∈ W
            ∧ (fun ℓ i => (K' ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)) ∈ W
            ∧ c ∈ Wc ∧ (∀ ℓ i, 0 < c ℓ i)
            ∧ θ' = (Params.sumOf ((θ.sumFst.headsQK K).headsVO K') (θ.sumSnd.rescale c)).cob
                (fun _ => Q) (fun _ => Q) := by
  -- `d ≥ 2`, so `d` is not empty
  have : Nonempty d := Fintype.card_pos_iff.mp (by omega)
  -- at generic parameters `E` has rank `d`, the query and value matrices of every head have
  -- rank `d_h`, no value column of a gated unit vanishes, and `fd(θ) = P - d(d-1)/2 - s`
  -- (Theorem 4.7 under pre-RMSNorm)
  filter_upwards [ae_rank_E_lit μ hdIn, ae_rank_QV_lit μ hdh, ae_value_ne_zero_lit μ,
    ae_funDim_attentionGated_residual_rmsNorm hε hσ hσa hU μ hd hdIn hdOut hdh hdh0 t₁ t₂ h12 hs2
      hs1] with θ hE hQV hv hfd
  -- Proposition 4.5 under pre-RMSNorm at `θ`
  exact exists_cob_heads_of_eval_eq_residual_attentionGated_rmsNorm hε hσa θ hE hQV.1 hQV.2 hv
    hfd

/-- **Corollary 4.9 of the skips paper for attention blocks and SwiGLU blocks, without
normalization:** for `d_in, d_out ≥ d ≥ 2`, heads of width `1 ≤ d_h ≤ d`, blocks of any widths and
a mask with a token that sees itself and another token, at almost every parameter `θ` of the
residual network, every `θ'` near `θ` with the same function is `θ` after changes of basis inside
the heads and rescalings of the values of the gated units, near the identity, and the change of
basis by one invertible `G` near the identity at all hidden states. -/
theorem ae_exists_cob_heads_of_eval_eq_attention_swiglu_residual
    (μ : Measure (Params
      (Arch.attentionGated (T := T) (d := d) sees silu id H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ θ ∂μ, ∀ V ∈ 𝓝 (1 : Matrix d d ℝ), ∀ W ∈ 𝓝 (1 : ∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ),
      ∀ Wc ∈ 𝓝 (1 : ∀ ℓ, hid ℓ → ℝ), ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.attentionGated sees silu id H dh hid) 1 θ' x
        = eval (Arch.attentionGated sees silu id H dh hid) 1 θ x) →
        ∃ (G : GL d ℝ) (K K' : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ) (c : ∀ ℓ, hid ℓ → ℝ),
          (G : Matrix d d ℝ) ∈ V
            ∧ (fun ℓ i => (K ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)) ∈ W
            ∧ (fun ℓ i => (K' ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)) ∈ W
            ∧ c ∈ Wc ∧ (∀ ℓ i, 0 < c ℓ i)
            ∧ θ' = (Params.sumOf ((θ.sumFst.headsQK K).headsVO K') (θ.sumSnd.rescale c)).cob
                (fun _ => G) (fun _ => G) := by
  -- SiLU is analytic and the values of its gated units are determined up to rescaling
  -- (Lemma B.3)
  exact ae_exists_cob_heads_of_eval_eq_attentionGated_residual (σ' := siluDeriv) hasDerivAt_silu
    analyticOnNhd_silu (silu_gatedUnitsRescale _ _ _) μ hd hdIn hdOut hdh hdh0 t₁ t₂ h12 hs2 hs1

/-- **Corollary 4.9 of the skips paper for attention blocks and SwiGLU blocks, under pre-RMSNorm
(`ε > 0`):** for `d_in, d_out ≥ d ≥ 2`, heads of width `1 ≤ d_h ≤ d`, blocks of any widths and a
mask with a token that sees itself and another token, at almost every parameter `θ` of the
residual network, every `θ'` near `θ` with the same function is `θ` after changes of basis inside
the heads and rescalings of the values of the gated units, near the identity, and the change of
basis by one orthogonal `Q` near the identity at all hidden states. -/
theorem ae_exists_cob_heads_of_eval_eq_attention_swiglu_residual_rmsNorm (hε : 0 < ε)
    (μ : Measure (Params
      (Arch.attentionGated (T := T) (d := d) sees silu (rmsNorm ε) H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ θ ∂μ, ∀ V ∈ 𝓝 (1 : Matrix d d ℝ), ∀ W ∈ 𝓝 (1 : ∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ),
      ∀ Wc ∈ 𝓝 (1 : ∀ ℓ, hid ℓ → ℝ), ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.attentionGated sees silu (rmsNorm ε) H dh hid) 1 θ' x
        = eval (Arch.attentionGated sees silu (rmsNorm ε) H dh hid) 1 θ x) →
        ∃ (Q : GL d ℝ) (K K' : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ) (c : ∀ ℓ, hid ℓ → ℝ),
          (Q : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ ∧ (Q : Matrix d d ℝ) ∈ V
            ∧ (fun ℓ i => (K ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)) ∈ W
            ∧ (fun ℓ i => (K' ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)) ∈ W
            ∧ c ∈ Wc ∧ (∀ ℓ i, 0 < c ℓ i)
            ∧ θ' = (Params.sumOf ((θ.sumFst.headsQK K).headsVO K') (θ.sumSnd.rescale c)).cob
                (fun _ => Q) (fun _ => Q) := by
  -- SiLU is analytic and the values of its gated units are determined up to rescaling
  -- (Lemma B.3)
  exact ae_exists_cob_heads_of_eval_eq_attentionGated_residual_rmsNorm (σ' := siluDeriv) hε
    hasDerivAt_silu analyticOnNhd_silu (silu_gatedUnitsRescale _ _ _) μ hd hdIn hdOut hdh hdh0 t₁
    t₂ h12 hs2 hs1

/-- **Corollary 4.9 of the skips paper for attention blocks and GeGLU blocks, without
normalization:** for `d_in, d_out ≥ d ≥ 2`, heads of width `1 ≤ d_h ≤ d`, blocks of any widths and
a mask with a token that sees itself and another token, at almost every parameter `θ` of the
residual network, every `θ'` near `θ` with the same function is `θ` after changes of basis inside
the heads and rescalings of the values of the gated units, near the identity, and the change of
basis by one invertible `G` near the identity at all hidden states. -/
theorem ae_exists_cob_heads_of_eval_eq_attention_geglu_residual
    (μ : Measure (Params
      (Arch.attentionGated (T := T) (d := d) sees gelu id H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ θ ∂μ, ∀ V ∈ 𝓝 (1 : Matrix d d ℝ), ∀ W ∈ 𝓝 (1 : ∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ),
      ∀ Wc ∈ 𝓝 (1 : ∀ ℓ, hid ℓ → ℝ), ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.attentionGated sees gelu id H dh hid) 1 θ' x
        = eval (Arch.attentionGated sees gelu id H dh hid) 1 θ x) →
        ∃ (G : GL d ℝ) (K K' : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ) (c : ∀ ℓ, hid ℓ → ℝ),
          (G : Matrix d d ℝ) ∈ V
            ∧ (fun ℓ i => (K ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)) ∈ W
            ∧ (fun ℓ i => (K' ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)) ∈ W
            ∧ c ∈ Wc ∧ (∀ ℓ i, 0 < c ℓ i)
            ∧ θ' = (Params.sumOf ((θ.sumFst.headsQK K).headsVO K') (θ.sumSnd.rescale c)).cob
                (fun _ => G) (fun _ => G) := by
  -- GELU is analytic and the values of its gated units are determined up to rescaling
  -- (Lemma B.3)
  exact ae_exists_cob_heads_of_eval_eq_attentionGated_residual (σ' := geluDeriv) hasDerivAt_gelu
    analyticOnNhd_gelu (gelu_gatedUnitsRescale _ _ _) μ hd hdIn hdOut hdh hdh0 t₁ t₂ h12 hs2 hs1

/-- **Corollary 4.9 of the skips paper for attention blocks and GeGLU blocks, under pre-RMSNorm
(`ε > 0`):** for `d_in, d_out ≥ d ≥ 2`, heads of width `1 ≤ d_h ≤ d`, blocks of any widths and a
mask with a token that sees itself and another token, at almost every parameter `θ` of the
residual network, every `θ'` near `θ` with the same function is `θ` after changes of basis inside
the heads and rescalings of the values of the gated units, near the identity, and the change of
basis by one orthogonal `Q` near the identity at all hidden states. -/
theorem ae_exists_cob_heads_of_eval_eq_attention_geglu_residual_rmsNorm (hε : 0 < ε)
    (μ : Measure (Params
      (Arch.attentionGated (T := T) (d := d) sees gelu (rmsNorm ε) H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ θ ∂μ, ∀ V ∈ 𝓝 (1 : Matrix d d ℝ), ∀ W ∈ 𝓝 (1 : ∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ),
      ∀ Wc ∈ 𝓝 (1 : ∀ ℓ, hid ℓ → ℝ), ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.attentionGated sees gelu (rmsNorm ε) H dh hid) 1 θ' x
        = eval (Arch.attentionGated sees gelu (rmsNorm ε) H dh hid) 1 θ x) →
        ∃ (Q : GL d ℝ) (K K' : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ) (c : ∀ ℓ, hid ℓ → ℝ),
          (Q : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ ∧ (Q : Matrix d d ℝ) ∈ V
            ∧ (fun ℓ i => (K ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)) ∈ W
            ∧ (fun ℓ i => (K' ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)) ∈ W
            ∧ c ∈ Wc ∧ (∀ ℓ i, 0 < c ℓ i)
            ∧ θ' = (Params.sumOf ((θ.sumFst.headsQK K).headsVO K') (θ.sumSnd.rescale c)).cob
                (fun _ => Q) (fun _ => Q) := by
  -- GELU is analytic and the values of its gated units are determined up to rescaling
  -- (Lemma B.3)
  exact ae_exists_cob_heads_of_eval_eq_attentionGated_residual_rmsNorm (σ' := geluDeriv) hε
    hasDerivAt_gelu analyticOnNhd_gelu (gelu_gatedUnitsRescale _ _ _) μ hd hdIn hdOut hdh hdh0 t₁
    t₂ h12 hs2 hs1

end Skips
