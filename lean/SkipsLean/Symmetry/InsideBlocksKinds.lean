import SkipsLean.Symmetry.InsideBlocks
import SkipsLean.Symmetry.AttentionHeads
import SkipsLean.Dimension.Rescaling

/-!
# The symmetries inside attention blocks and gated blocks are symmetries inside the blocks

Paper (skips paper), Section 4.1: the symmetries inside the blocks are "the rescaling of the value
of a hidden unit of a gated block, and the changes of basis inside an attention head" (and the
rescaling of a hidden unit of a ReLU or ReLU² block, not stated here). Each of them leaves "the
map of that block unchanged".

Here: the directions `headDirQK θ Γ`, `headDirVO θ Γ'` of the changes of basis inside the heads
(`Symmetry/AttentionHeads.lean`) and the directions `rescaleDir θ α` of the rescalings of the
values of gated units (`Dimension/Rescaling.lean`) are directions of symmetries inside the blocks
in the sense of `Symmetry/InsideBlocks.lean`: the curves `θ.headsQK (exp (τ Γ))`,
`θ.headsVO (exp (τ Γ'))` and the rescaling by `exp (τ α)` keep `E`, `D` and the map of every
block. For any `χ`, any mask, and any gate activation `σ`.
-/

namespace Skips

open Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {sees : T → T → Prop} [DecidableRel sees] {χ : Matrix T d ℝ → Matrix T d ℝ}
variable {H dh : Fin L → Type} [∀ ℓ, Fintype (H ℓ)] [∀ ℓ, Fintype (dh ℓ)]
variable {σ : ℝ → ℝ} {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]

section HeadHelpers

variable [∀ ℓ, DecidableEq (dh ℓ)]

omit [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (copy of `headsQK_query_ath`): the query matrices of `θ.headsQK K` are
`W_{Q,i} K_i`. -/
private theorem headsQK_query_ibk (θ : Params (Arch.attention sees χ H dh) dIn dOut)
    (K : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ) (ℓ : Fin L) (i : H ℓ) :
    ((θ.headsQK K).read ℓ).submatrix id (fun k : dh ℓ => (i, Sum.inl k))
      = (θ.read ℓ).submatrix id (fun k : dh ℓ => (i, Sum.inl k))
        * (K ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ) := by
  ext a k
  rfl

omit [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (copy of `headsQK_key_ath`): the key matrices of `θ.headsQK K` are
`W_{K,i} K_i^{-⊤}`. -/
private theorem headsQK_key_ibk (θ : Params (Arch.attention sees χ H dh) dIn dOut)
    (K : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ) (ℓ : Fin L) (i : H ℓ) :
    ((θ.headsQK K).read ℓ).submatrix id (fun k : dh ℓ => (i, Sum.inr (Sum.inl k)))
      = (θ.read ℓ).submatrix id (fun k : dh ℓ => (i, Sum.inr (Sum.inl k)))
        * (((K ℓ i)⁻¹ : GL (dh ℓ) ℝ) : Matrix (dh ℓ) (dh ℓ) ℝ)ᵀ := by
  ext a k
  rfl

omit [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (copy of `headsVO_value_ath`): the value matrices of `θ.headsVO K` are
`W_{V,i} K'_i`. -/
private theorem headsVO_value_ibk (θ : Params (Arch.attention sees χ H dh) dIn dOut)
    (K : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ) (ℓ : Fin L) (i : H ℓ) :
    ((θ.headsVO K).read ℓ).submatrix id (fun k : dh ℓ => (i, Sum.inr (Sum.inr k)))
      = (θ.read ℓ).submatrix id (fun k : dh ℓ => (i, Sum.inr (Sum.inr k)))
        * (K ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ) := by
  ext a k
  rfl

omit [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (copy of `headsVO_output_ath`): the output matrices of `θ.headsVO K` are
`K'_i^{-1} W_{O,i}`. -/
private theorem headsVO_output_ibk (θ : Params (Arch.attention sees χ H dh) dIn dOut)
    (K : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ) (ℓ : Fin L) (i : H ℓ) :
    ((θ.headsVO K).write ℓ).submatrix (fun k : dh ℓ => (i, k)) id
      = (((K ℓ i)⁻¹ : GL (dh ℓ) ℝ) : Matrix (dh ℓ) (dh ℓ) ℝ)
        * (θ.write ℓ).submatrix (fun k : dh ℓ => (i, k)) id := by
  ext k b
  rfl

omit [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (copy of `block_headsQK_ath`): the change of basis between queries and keys leaves the
output of every block unchanged: `W_{Q,i} K (W_{K,i} K^{-⊤})ᵀ = W_{Q,i} W_{K,i}ᵀ`. -/
private theorem block_headsQK_ibk (θ : Params (Arch.attention sees χ H dh) dIn dOut)
    (K : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ) (ℓ : Fin L) (h : Matrix T d ℝ) :
    (Arch.attention sees χ H dh).f ℓ (h * (θ.headsQK K).read ℓ) * (θ.headsQK K).write ℓ
      = (Arch.attention sees χ H dh).f ℓ (h * θ.read ℓ) * θ.write ℓ := by
  rw [f_attention_mul, f_attention_mul]
  unfold attentionBlock
  congr 1
  funext i
  dsimp only
  rw [headsQK_query_ibk, headsQK_key_ibk, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.mul_assoc, ← Matrix.mul_assoc (K ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ), Units.mul_inv,
    Matrix.one_mul]

omit [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (copy of `block_headsVO_ath`): the change of basis between values and outputs leaves
the output of every block unchanged: `W_{V,i} K' K'^{-1} W_{O,i} = W_{V,i} W_{O,i}`. -/
private theorem block_headsVO_ibk (θ : Params (Arch.attention sees χ H dh) dIn dOut)
    (K : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ) (ℓ : Fin L) (h : Matrix T d ℝ) :
    (Arch.attention sees χ H dh).f ℓ (h * (θ.headsVO K).read ℓ) * (θ.headsVO K).write ℓ
      = (Arch.attention sees χ H dh).f ℓ (h * θ.read ℓ) * θ.write ℓ := by
  rw [f_attention_mul, f_attention_mul]
  unfold attentionBlock
  congr 1
  funext i
  dsimp only
  rw [headsVO_value_ibk, headsVO_output_ibk, Matrix.mul_assoc,
    ← Matrix.mul_assoc (K ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ), Units.mul_inv, Matrix.one_mul]

/-- Helper (copy of `expGL_ath`): the change of basis `exp (τ X)`, an element of `GL n ℝ` with
inverse `exp (-τ X)`. -/
private noncomputable def expGL_ibk {n : Type*} [Fintype n] [DecidableEq n] (X : Matrix n n ℝ)
    (τ : ℝ) : GL n ℝ where
  val := NormedSpace.exp (τ • X)
  inv := NormedSpace.exp (τ • (-X))
  val_inv := by
    rw [← Matrix.exp_add_of_commute _ _ (((Commute.refl X).neg_right.smul_left τ).smul_right τ),
      smul_neg, add_neg_cancel, NormedSpace.exp_zero]
  inv_val := by
    rw [← Matrix.exp_add_of_commute _ _ (((Commute.refl X).neg_left.smul_left τ).smul_right τ),
      smul_neg, neg_add_cancel, NormedSpace.exp_zero]

/-- Helper (copy of `expGL_zero_ath`): at `τ = 0` the change of basis `exp (τ X)` is the
identity. -/
private theorem expGL_zero_ibk {n : Type*} [Fintype n] [DecidableEq n] (X : Matrix n n ℝ) :
    expGL_ibk X 0 = 1 :=
  Units.ext (by simp [expGL_ibk])

/-- Helper (copy of `hasDerivAt_exp_entry_ath`): the entry `(a, b)` of `exp (τ X)` has
derivative `X a b` at `τ = 0` (computed with the operator norm, same topology). -/
private theorem hasDerivAt_exp_entry_ibk {n : Type*} [Fintype n] [DecidableEq n]
    (X : Matrix n n ℝ) (a b : n) :
    HasDerivAt (fun τ : ℝ => NormedSpace.exp (τ • X) a b) (X a b) 0 := by
  have h := open scoped Matrix.Norms.Operator in hasDerivAt_exp_smul_const (𝕂 := ℝ) X (0 : ℝ)
  rw [zero_smul, NormedSpace.exp_zero, one_mul] at h
  have h' : HasDerivAt (fun τ : ℝ => NormedSpace.exp (τ • X)) X 0 := h
  -- entry by entry
  exact hasDerivAt_pi.1 (hasDerivAt_pi.1 h' a) b

/-- Helper (copy of `hasDerivAt_sum_mul_expGL_ath`): `τ ↦ ∑_{k'} c_{k'} exp(τ X)_{k' k}` has
derivative `∑_{k'} c_{k'} X_{k' k}` at `0`. -/
private theorem hasDerivAt_sum_mul_expGL_ibk {n : Type*} [Fintype n] [DecidableEq n]
    (X : Matrix n n ℝ) (c : n → ℝ) (k : n) :
    HasDerivAt (fun τ => ∑ k', c k' * (expGL_ibk X τ : Matrix n n ℝ) k' k)
      (∑ k', c k' * X k' k) 0 :=
  HasDerivAt.fun_sum fun k' _ => (hasDerivAt_exp_entry_ibk X k' k).const_mul (c k')

/-- Helper (copy of `hasDerivAt_sum_mul_expGL_inv_ath`): `τ ↦ ∑_{k'} c_{k'} (exp(τ X)⁻¹)_{k k'}`
has derivative `-∑_{k'} c_{k'} X_{k k'}` at `0`, since `exp(τ X)⁻¹ = exp(-τ X)`. -/
private theorem hasDerivAt_sum_mul_expGL_inv_ibk {n : Type*} [Fintype n] [DecidableEq n]
    (X : Matrix n n ℝ) (c : n → ℝ) (k : n) :
    HasDerivAt (fun τ => ∑ k', c k' * (((expGL_ibk X τ)⁻¹ : GL n ℝ) : Matrix n n ℝ) k k')
      (-∑ k', c k' * X k k') 0 := by
  have h := HasDerivAt.fun_sum (u := Finset.univ) fun k' _ =>
    (hasDerivAt_exp_entry_ibk (-X) k k').const_mul (c k')
  refine h.congr_deriv ?_
  simp only [Matrix.neg_apply, mul_neg, Finset.sum_neg_distrib]

/-- Helper (copy of `hasDerivAt_sum_expGL_inv_mul_ath`): `τ ↦ ∑_{k'} (exp(τ X)⁻¹)_{k k'} c_{k'}`
has derivative `-∑_{k'} X_{k k'} c_{k'}` at `0`. -/
private theorem hasDerivAt_sum_expGL_inv_mul_ibk {n : Type*} [Fintype n] [DecidableEq n]
    (X : Matrix n n ℝ) (c : n → ℝ) (k : n) :
    HasDerivAt (fun τ => ∑ k', (((expGL_ibk X τ)⁻¹ : GL n ℝ) : Matrix n n ℝ) k k' * c k')
      (-∑ k', X k k' * c k') 0 := by
  have h := HasDerivAt.fun_sum (u := Finset.univ) fun k' _ =>
    (hasDerivAt_exp_entry_ibk (-X) k k').mul_const (c k')
  refine h.congr_deriv ?_
  simp only [Matrix.neg_apply, neg_mul, Finset.sum_neg_distrib]

omit [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (copy of `headsQK_expGL_zero_ath`): the curve `τ ↦ θ.headsQK (exp (τ Γ))` passes
through `θ` at `τ = 0`. -/
private theorem headsQK_expGL_zero_ibk (θ : Params (Arch.attention sees χ H dh) dIn dOut)
    (Γ : ∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) :
    θ.headsQK (fun ℓ i => expGL_ibk (Γ ℓ i) 0) = θ := by
  simp only [expGL_zero_ibk]
  apply Params.ext'
  · rfl
  · intro ℓ
    ext a ⟨i, k | k | k⟩
    · show ∑ k', θ.read ℓ a (i, Sum.inl k') * ((1 : GL (dh ℓ) ℝ) : Matrix (dh ℓ) (dh ℓ) ℝ) k' k
        = θ.read ℓ a (i, Sum.inl k)
      simp [Matrix.one_apply]
    · show ∑ k', θ.read ℓ a (i, Sum.inr (Sum.inl k'))
          * (((1 : GL (dh ℓ) ℝ)⁻¹ : GL (dh ℓ) ℝ) : Matrix (dh ℓ) (dh ℓ) ℝ) k k'
        = θ.read ℓ a (i, Sum.inr (Sum.inl k))
      simp [Matrix.one_apply]
    · rfl
  · intro ℓ
    rfl
  · rfl

omit [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (copy of `headsVO_expGL_zero_ath`): the curve `τ ↦ θ.headsVO (exp (τ Γ))` passes
through `θ` at `τ = 0`. -/
private theorem headsVO_expGL_zero_ibk (θ : Params (Arch.attention sees χ H dh) dIn dOut)
    (Γ : ∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) :
    θ.headsVO (fun ℓ i => expGL_ibk (Γ ℓ i) 0) = θ := by
  simp only [expGL_zero_ibk]
  apply Params.ext'
  · rfl
  · intro ℓ
    ext a ⟨i, k | k | k⟩
    · rfl
    · rfl
    · show ∑ k', θ.read ℓ a (i, Sum.inr (Sum.inr k'))
          * ((1 : GL (dh ℓ) ℝ) : Matrix (dh ℓ) (dh ℓ) ℝ) k' k
        = θ.read ℓ a (i, Sum.inr (Sum.inr k))
      simp [Matrix.one_apply]
  · intro ℓ
    ext ⟨i, k⟩ b
    show ∑ k', (((1 : GL (dh ℓ) ℝ)⁻¹ : GL (dh ℓ) ℝ) : Matrix (dh ℓ) (dh ℓ) ℝ) k k'
        * θ.write ℓ (i, k') b = θ.write ℓ (i, k) b
    simp [Matrix.one_apply]
  · rfl

omit [DecidableEq d] in
/-- Helper (copy of `hasDerivAt_headsQK_ath`): the curve `τ ↦ θ.headsQK (exp (τ Γ))` has velocity
`headDirQK θ Γ` at `τ = 0` (entry by entry, through `Params.linearEquivProd`). -/
private theorem hasDerivAt_headsQK_ibk (θ : Params (Arch.attention sees χ H dh) dIn dOut)
    (Γ : ∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) :
    HasDerivAt (fun τ : ℝ => θ.headsQK fun ℓ i => expGL_ibk (Γ ℓ i) τ) (headDirQK θ Γ) 0 := by
  have hprod : HasDerivAt
      (fun τ : ℝ => Params.linearEquivProd (θ.headsQK fun ℓ i => expGL_ibk (Γ ℓ i) τ))
      (Params.linearEquivProd (headDirQK θ Γ)) 0 := by
    refine HasDerivAt.prodMk ?_ (HasDerivAt.prodMk ?_ (HasDerivAt.prodMk ?_ ?_))
    · -- the embedding does not move
      exact hasDerivAt_const (0 : ℝ) θ.E
    · -- the queries are `W_Q exp(τ Γ)`, the keys `W_K exp(-τ Γ)ᵀ`, the values do not move
      refine hasDerivAt_pi.2 fun ℓ => hasDerivAt_pi.2 fun a => hasDerivAt_pi.2 fun p => ?_
      obtain ⟨i, k | k | k⟩ := p
      · exact hasDerivAt_sum_mul_expGL_ibk (Γ ℓ i) (fun k' => θ.read ℓ a (i, Sum.inl k')) k
      · exact hasDerivAt_sum_mul_expGL_inv_ibk (Γ ℓ i)
          (fun k' => θ.read ℓ a (i, Sum.inr (Sum.inl k'))) k
      · exact hasDerivAt_const (0 : ℝ) (θ.read ℓ a (i, Sum.inr (Sum.inr k)))
    · -- the writes and the readout do not move
      exact hasDerivAt_const (0 : ℝ) θ.write
    · exact hasDerivAt_const (0 : ℝ) θ.D
  -- back from the tuples of components to the parameters
  exact (LinearMap.toContinuousLinearMap
    (Params.linearEquivProd (A := Arch.attention sees χ H dh) (dIn := dIn)
      (dOut := dOut)).symm.toLinearMap).hasFDerivAt.comp_hasDerivAt 0 hprod

omit [DecidableEq d] in
/-- Helper (copy of `hasDerivAt_headsVO_ath`): the curve `τ ↦ θ.headsVO (exp (τ Γ))` has velocity
`headDirVO θ Γ` at `τ = 0`. -/
private theorem hasDerivAt_headsVO_ibk (θ : Params (Arch.attention sees χ H dh) dIn dOut)
    (Γ : ∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) :
    HasDerivAt (fun τ : ℝ => θ.headsVO fun ℓ i => expGL_ibk (Γ ℓ i) τ) (headDirVO θ Γ) 0 := by
  have hprod : HasDerivAt
      (fun τ : ℝ => Params.linearEquivProd (θ.headsVO fun ℓ i => expGL_ibk (Γ ℓ i) τ))
      (Params.linearEquivProd (headDirVO θ Γ)) 0 := by
    refine HasDerivAt.prodMk ?_ (HasDerivAt.prodMk ?_ (HasDerivAt.prodMk ?_ ?_))
    · -- the embedding does not move
      exact hasDerivAt_const (0 : ℝ) θ.E
    · -- the queries and keys do not move, the values are `W_V exp(τ Γ)`
      refine hasDerivAt_pi.2 fun ℓ => hasDerivAt_pi.2 fun a => hasDerivAt_pi.2 fun p => ?_
      obtain ⟨i, k | k | k⟩ := p
      · exact hasDerivAt_const (0 : ℝ) (θ.read ℓ a (i, Sum.inl k))
      · exact hasDerivAt_const (0 : ℝ) (θ.read ℓ a (i, Sum.inr (Sum.inl k)))
      · exact hasDerivAt_sum_mul_expGL_ibk (Γ ℓ i)
          (fun k' => θ.read ℓ a (i, Sum.inr (Sum.inr k'))) k
    · -- the outputs are `exp(-τ Γ) W_O`
      refine hasDerivAt_pi.2 fun ℓ => hasDerivAt_pi.2 fun p => hasDerivAt_pi.2 fun b => ?_
      obtain ⟨i, k⟩ := p
      exact hasDerivAt_sum_expGL_inv_mul_ibk (Γ ℓ i) (fun k' => θ.write ℓ (i, k') b) k
    · -- the readout does not move
      exact hasDerivAt_const (0 : ℝ) θ.D
  -- back from the tuples of components to the parameters
  exact (LinearMap.toContinuousLinearMap
    (Params.linearEquivProd (A := Arch.attention sees χ H dh) (dIn := dIn)
      (dOut := dOut)).symm.toLinearMap).hasFDerivAt.comp_hasDerivAt 0 hprod

end HeadHelpers

/-- **The changes of basis between the queries and the keys of the heads are symmetries inside
the blocks.** -/
theorem insideBlocks_headDirQK (θ : Params (Arch.attention sees χ H dh) dIn dOut)
    (Γ : ∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) :
    InsideBlocks (Arch.attention sees χ H dh) θ (headDirQK θ Γ) := by
  classical
  -- the curve `τ ↦ θ.headsQK (exp (τ Γ))`: through `θ`, with velocity `headDirQK θ Γ`; it keeps
  -- `E` and `D` by definition and the map of every block at every `τ`
  exact ⟨fun τ => θ.headsQK fun ℓ i => expGL_ibk (Γ ℓ i) τ, headsQK_expGL_zero_ibk θ Γ,
    hasDerivAt_headsQK_ibk θ Γ,
    Filter.Eventually.of_forall fun τ => ⟨rfl, rfl, fun ℓ n => block_headsQK_ibk θ _ ℓ n⟩⟩

/-- **The changes of basis between the values and the outputs of the heads are symmetries inside
the blocks.** -/
theorem insideBlocks_headDirVO (θ : Params (Arch.attention sees χ H dh) dIn dOut)
    (Γ : ∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) :
    InsideBlocks (Arch.attention sees χ H dh) θ (headDirVO θ Γ) := by
  classical
  -- the curve `τ ↦ θ.headsVO (exp (τ Γ))`: through `θ`, with velocity `headDirVO θ Γ`; it keeps
  -- `E` and `D` by definition and the map of every block at every `τ`
  exact ⟨fun τ => θ.headsVO fun ℓ i => expGL_ibk (Γ ℓ i) τ, headsVO_expGL_zero_ibk θ Γ,
    hasDerivAt_headsVO_ibk θ Γ,
    Filter.Eventually.of_forall fun τ => ⟨rfl, rfl, fun ℓ n => block_headsVO_ibk θ _ ℓ n⟩⟩

/-- Helper (copy of the private `hasDerivAt_exp_mul_const` of `Dimension/Rescaling.lean`):
`τ ↦ e^{τ a} b` has derivative `a b` at `τ = 0`. -/
private theorem hasDerivAt_exp_mul_const_ibk (a b : ℝ) :
    HasDerivAt (fun τ : ℝ => Real.exp (τ * a) * b) (a * b) 0 := by
  have h := ((hasDerivAt_id (0 : ℝ)).mul_const a).exp.mul_const b
  simpa using h

/-- Helper (copy of the private `rescaleCurve`): the value column of hidden unit `i` of block `ℓ`
is multiplied by `e^{-τ α ℓ i}`, its write row by `e^{τ α ℓ i}`. -/
private noncomputable def rescaleCurve_ibk
    (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut) (α : ∀ ℓ, hid ℓ → ℝ) (τ : ℝ) :
    Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut where
  E := θ.E
  read ℓ := Matrix.of fun k j => Sum.elim (fun i => θ.read ℓ k (Sum.inl i))
    (fun i => Real.exp (τ * -(α ℓ i)) * θ.read ℓ k (Sum.inr i)) j
  write ℓ := Matrix.of fun i k => Real.exp (τ * α ℓ i) * θ.write ℓ i k
  D := θ.D

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (copy of `rescaleCurve_zero`): the curve passes through `θ` at `τ = 0`. -/
private theorem rescaleCurve_zero_ibk
    (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut) (α : ∀ ℓ, hid ℓ → ℝ) :
    rescaleCurve_ibk θ α 0 = θ := by
  apply Params.ext'
  · rfl
  · intro ℓ
    ext k j
    cases j <;> simp [rescaleCurve_ibk]
  · intro ℓ
    ext i k
    simp [rescaleCurve_ibk]
  · rfl

omit [Fintype T] [DecidableEq d] in
/-- Helper (copy of `hasDerivAt_rescaleCurve`): the curve has velocity `rescaleDir θ α` at
`τ = 0` (entry by entry, through `Params.linearEquivProd`). -/
private theorem hasDerivAt_rescaleCurve_ibk
    (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut) (α : ∀ ℓ, hid ℓ → ℝ) :
    HasDerivAt (rescaleCurve_ibk θ α) (rescaleDir θ α) 0 := by
  have hprod : HasDerivAt (fun τ : ℝ => Params.linearEquivProd (rescaleCurve_ibk θ α τ))
      (Params.linearEquivProd (rescaleDir θ α)) 0 := by
    refine HasDerivAt.prodMk ?_ (HasDerivAt.prodMk ?_ (HasDerivAt.prodMk ?_ ?_))
    · -- the embedding does not move
      exact hasDerivAt_const (0 : ℝ) θ.E
    · -- the gate entries do not move; the value entries are `e^{-τ α} w`
      refine hasDerivAt_pi.2 fun ℓ => hasDerivAt_pi.2 fun k => hasDerivAt_pi.2 fun j => ?_
      cases j with
      | inl i => exact hasDerivAt_const (0 : ℝ) (θ.read ℓ k (Sum.inl i))
      | inr i => exact hasDerivAt_exp_mul_const_ibk (-(α ℓ i)) (θ.read ℓ k (Sum.inr i))
    · -- the write entries are `e^{τ α} a`
      exact hasDerivAt_pi.2 fun ℓ => hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun k =>
        hasDerivAt_exp_mul_const_ibk (α ℓ i) (θ.write ℓ i k)
    · -- the readout does not move
      exact hasDerivAt_const (0 : ℝ) θ.D
  -- back from the tuples of components to the parameters
  exact (LinearMap.toContinuousLinearMap
    (Params.linearEquivProd (A := Arch.gated (T := T) (d := d) σ χ hid) (dIn := dIn)
      (dOut := dOut)).symm.toLinearMap).hasFDerivAt.comp_hasDerivAt 0 hprod

omit [Fintype T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the rescaling keeps the map of every gated block: hidden unit `i` contributes
`σ(z_i) (e^{-τ α} u_i) (e^{τ α} a_i) = σ(z_i) u_i a_i` to every entry. -/
private theorem block_rescaleCurve_ibk
    (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut) (α : ∀ ℓ, hid ℓ → ℝ) (τ : ℝ)
    (ℓ : Fin L) (n : Matrix T d ℝ) :
    (Arch.gated σ χ hid).f ℓ (n * (rescaleCurve_ibk θ α τ).read ℓ)
        * (rescaleCurve_ibk θ α τ).write ℓ
      = (Arch.gated σ χ hid).f ℓ (n * θ.read ℓ) * θ.write ℓ := by
  -- the gates are the same
  have hz : ∀ t i, (n * (rescaleCurve_ibk θ α τ).read ℓ) t (Sum.inl i)
      = (n * θ.read ℓ) t (Sum.inl i) := fun _ _ => rfl
  -- the values are multiplied by `e^{-τ α}`
  have hu : ∀ t i, (n * (rescaleCurve_ibk θ α τ).read ℓ) t (Sum.inr i)
      = Real.exp (τ * -(α ℓ i)) * (n * θ.read ℓ) t (Sum.inr i) := by
    intro t i
    rw [Matrix.mul_apply, Matrix.mul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    show n t j * (Real.exp (τ * -(α ℓ i)) * θ.read ℓ j (Sum.inr i))
      = Real.exp (τ * -(α ℓ i)) * (n t j * θ.read ℓ j (Sum.inr i))
    ring
  -- compare term by term
  ext t k
  rw [Matrix.mul_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  show σ ((n * (rescaleCurve_ibk θ α τ).read ℓ) t (Sum.inl i))
      * (n * (rescaleCurve_ibk θ α τ).read ℓ) t (Sum.inr i)
      * (Real.exp (τ * α ℓ i) * θ.write ℓ i k)
    = σ ((n * θ.read ℓ) t (Sum.inl i)) * (n * θ.read ℓ) t (Sum.inr i) * θ.write ℓ i k
  rw [hz, hu]
  -- `e^{-τ α} e^{τ α} = 1`
  have he : Real.exp (τ * -(α ℓ i)) * Real.exp (τ * α ℓ i) = 1 := by
    rw [← Real.exp_add, mul_neg, neg_add_cancel, Real.exp_zero]
  calc _ = (Real.exp (τ * -(α ℓ i)) * Real.exp (τ * α ℓ i))
        * (σ ((n * θ.read ℓ) t (Sum.inl i)) * (n * θ.read ℓ) t (Sum.inr i) * θ.write ℓ i k) := by
        ring
    _ = _ := by rw [he, one_mul]

/-- **The rescalings of the values of gated units are symmetries inside the blocks.** -/
theorem insideBlocks_rescaleDir (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut)
    (α : ∀ ℓ, hid ℓ → ℝ) :
    InsideBlocks (Arch.gated σ χ hid) θ (rescaleDir θ α) := by
  -- the curve of the rescalings by `e^{τ α}`: through `θ`, with velocity `rescaleDir θ α`; it
  -- keeps `E` and `D` by definition and the map of every block at every `τ`
  exact ⟨rescaleCurve_ibk θ α, rescaleCurve_zero_ibk θ α, hasDerivAt_rescaleCurve_ibk θ α,
    Filter.Eventually.of_forall fun τ => ⟨rfl, rfl, fun ℓ n => block_rescaleCurve_ibk θ α τ ℓ n⟩⟩

end Skips
