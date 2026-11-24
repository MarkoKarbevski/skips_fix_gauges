import SkipsLean.Dimension.IdentifiableConverseCob
import SkipsLean.Residual.LocalIdentifiabilityTransformer
import SkipsLean.Dimension.UpperBoundTransformer

/-!
# The equality condition and local identifiability: skipless transformers

Paper (skips paper): Proposition 4.5 (The equality condition and local identifiability): "Let the
blocks be analytic, with or without pre-RMSNorm, within the scope of Section 2. A skipless or a
residual network satisfies the equality condition if and only if, at generic parameters, it is
locally identifiable up to its symmetries. Every symmetry that is needed is then close to the
identity."

Here for skipless networks (stream matrices `0`) of attention blocks and MLP blocks, and of
attention blocks and gated blocks, in any order (`Network/Transformer.lean`), without
normalization and under pre-RMSNorm with `ε > 0`: first the direction from the equality condition
to local identifiability at one parameter, with the symmetries close to the identity (the twins:
`Residual/LocalIdentifiabilityTransformer.lean` for residual networks,
`Dimension/LocalIdentifiabilityAttention.lean` and `Dimension/LocalIdentifiabilityGated.lean` for
skipless networks of one kind of block); then the equivalence at generic parameters, for
`d_in ≥ d`, heads of width `d_h ≤ d` and blocks of total width `H d_h + d_hidden ≥ d` (the twins:
`Dimension/IdentifiableIff.lean`, `Residual/IdentifiableIff.lean`). The symmetries: the changes of
basis `G_0, …, G_L` (orthogonal under pre-RMSNorm), the changes of basis inside the heads and, for
gated blocks, the rescalings of the values of the hidden units.
-/

namespace Skips

open Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {sees : T → T → Prop} [DecidableRel sees]
variable {H dh hid : Fin L → Type} [∀ ℓ, Fintype (H ℓ)] [∀ ℓ, Fintype (dh ℓ)]
  [∀ ℓ, DecidableEq (dh ℓ)] [∀ ℓ, Fintype (hid ℓ)] {σ σ' : ℝ → ℝ} {ε : ℝ}

/-! ### From the equality condition to local identifiability, at one parameter -/

/-! #### Helpers: the two parts of the parameters of a network of `A.sum B` -/

omit [Fintype T] [Fintype dIn] [Fintype dOut] in
/-- Helper (the private `sumOf_cob_lit` of `Residual/LocalIdentifiabilityTransformer.lean`): the
change of basis of the hidden states acts part by part. -/
private theorem sumOf_cob_ift {A B : Arch T d L} (a : Params A dIn dOut) (b : Params B dIn dOut)
    (G K : Fin (L + 1) → GL d ℝ) :
    Params.sumOf (a.cob G K) (b.cob G K) = (Params.sumOf a b).cob G K := by
  refine Params.ext' rfl (fun ℓ => ?_) (fun ℓ => ?_) rfl
  · ext k p
    rcases p with j | j <;> rfl
  · ext p k
    rcases p with i | i <;> rfl

omit [Fintype T] [DecidableEq d] [Fintype d] [Fintype dIn] [Fintype dOut] in
/-- Helper (the private `sumOfLin_lit` of `Residual/LocalIdentifiabilityTransformer.lean`, as
`sumOfLin_iffr` of `Residual/IdentifiableIff.lean`): `(a, b) ↦ Params.sumOf a b` is linear. -/
private noncomputable def sumOfLin_ift {A B : Arch T d L} :
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
/-- Helper (the private `eval_eq_of_blocks_lit`): two parameters with the same `E`, the same `D`
and the same output of every block on every hidden state compute the same function. -/
private theorem eval_eq_of_blocks_ift {A : Arch T d L} (θ₁ θ₂ : Params A dIn dOut)
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
/-- Helper (the private `eval_sumOf_lit`): two networks of `A.sum B` whose first parts have the
same `E` and `D`, and whose two parts have the same output of every block on every hidden state,
compute the same function. -/
private theorem eval_sumOf_ift {A B : Arch T d L} (a a' : Params A dIn dOut)
    (b b' : Params B dIn dOut) (hE : a'.E = a.E) (hD : a'.D = a.D)
    (hA : ∀ ℓ (h : Matrix T d ℝ),
      A.f ℓ (h * a'.read ℓ) * a'.write ℓ = A.f ℓ (h * a.read ℓ) * a.write ℓ)
    (hB : ∀ ℓ (h : Matrix T d ℝ),
      B.f ℓ (h * b'.read ℓ) * b'.write ℓ = B.f ℓ (h * b.read ℓ) * b.write ℓ)
    (S : Fin L → Matrix d d ℝ) (x : Matrix T dIn ℝ) :
    eval (A.sum B) S (Params.sumOf a' b') x = eval (A.sum B) S (Params.sumOf a b) x := by
  refine eval_eq_of_blocks_ift (Params.sumOf a b) (Params.sumOf a' b') hE hD (fun ℓ h => ?_) S x
  rw [f_sum_mul, f_sum_mul]
  exact congrArg₂ (· + ·) (hA ℓ h) (hB ℓ h)

/-! #### Helpers: the symmetries inside the blocks keep the map of every block -/

omit [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (the private `headsQK_query_lit`): the query matrices of `θ.headsQK K` are
`W_{Q,i} K_i`. -/
private theorem headsQK_query_ift {χ : Matrix T d ℝ → Matrix T d ℝ}
    (θ : Params (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut)
    (K : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ) (ℓ : Fin L) (i : H ℓ) :
    ((θ.headsQK K).read ℓ).submatrix id (fun k : dh ℓ => (i, Sum.inl k))
      = (θ.read ℓ).submatrix id (fun k : dh ℓ => (i, Sum.inl k))
        * (K ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ) := by
  ext a k
  rfl

omit [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (the private `headsQK_key_lit`): the key matrices of `θ.headsQK K` are
`W_{K,i} K_i^{-⊤}`. -/
private theorem headsQK_key_ift {χ : Matrix T d ℝ → Matrix T d ℝ}
    (θ : Params (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut)
    (K : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ) (ℓ : Fin L) (i : H ℓ) :
    ((θ.headsQK K).read ℓ).submatrix id (fun k : dh ℓ => (i, Sum.inr (Sum.inl k)))
      = (θ.read ℓ).submatrix id (fun k : dh ℓ => (i, Sum.inr (Sum.inl k)))
        * (((K ℓ i)⁻¹ : GL (dh ℓ) ℝ) : Matrix (dh ℓ) (dh ℓ) ℝ)ᵀ := by
  ext a k
  rfl

omit [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (the private `headsVO_value_lit`): the value matrices of `θ.headsVO K` are
`W_{V,i} K'_i`. -/
private theorem headsVO_value_ift {χ : Matrix T d ℝ → Matrix T d ℝ}
    (θ : Params (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut)
    (K : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ) (ℓ : Fin L) (i : H ℓ) :
    ((θ.headsVO K).read ℓ).submatrix id (fun k : dh ℓ => (i, Sum.inr (Sum.inr k)))
      = (θ.read ℓ).submatrix id (fun k : dh ℓ => (i, Sum.inr (Sum.inr k)))
        * (K ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ) := by
  ext a k
  rfl

omit [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (the private `headsVO_output_lit`): the output matrices of `θ.headsVO K` are
`K'_i^{-1} W_{O,i}`. -/
private theorem headsVO_output_ift {χ : Matrix T d ℝ → Matrix T d ℝ}
    (θ : Params (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut)
    (K : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ) (ℓ : Fin L) (i : H ℓ) :
    ((θ.headsVO K).write ℓ).submatrix (fun k : dh ℓ => (i, k)) id
      = (((K ℓ i)⁻¹ : GL (dh ℓ) ℝ) : Matrix (dh ℓ) (dh ℓ) ℝ)
        * (θ.write ℓ).submatrix (fun k : dh ℓ => (i, k)) id := by
  ext k b
  rfl

omit [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (the private `block_headsQK_lit`): the change of basis between queries and keys leaves
the output of every attention block unchanged. -/
private theorem block_headsQK_ift {χ : Matrix T d ℝ → Matrix T d ℝ}
    (θ : Params (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut)
    (K : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ) (ℓ : Fin L) (h : Matrix T d ℝ) :
    (Arch.attention sees χ H dh).f ℓ (h * (θ.headsQK K).read ℓ) * (θ.headsQK K).write ℓ
      = (Arch.attention sees χ H dh).f ℓ (h * θ.read ℓ) * θ.write ℓ := by
  rw [f_attention_mul, f_attention_mul]
  unfold attentionBlock
  congr 1
  funext i
  dsimp only
  rw [headsQK_query_ift, headsQK_key_ift, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.mul_assoc, ← Matrix.mul_assoc (K ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ), Units.mul_inv,
    Matrix.one_mul]

omit [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (the private `block_headsVO_lit`): the change of basis between values and outputs
leaves the output of every attention block unchanged. -/
private theorem block_headsVO_ift {χ : Matrix T d ℝ → Matrix T d ℝ}
    (θ : Params (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut)
    (K : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ) (ℓ : Fin L) (h : Matrix T d ℝ) :
    (Arch.attention sees χ H dh).f ℓ (h * (θ.headsVO K).read ℓ) * (θ.headsVO K).write ℓ
      = (Arch.attention sees χ H dh).f ℓ (h * θ.read ℓ) * θ.write ℓ := by
  rw [f_attention_mul, f_attention_mul]
  unfold attentionBlock
  congr 1
  funext i
  dsimp only
  rw [headsVO_value_ift, headsVO_output_ift, Matrix.mul_assoc,
    ← Matrix.mul_assoc (K ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ), Units.mul_inv, Matrix.one_mul]

omit [Fintype T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (the private `block_rescale_lit`): the rescaling of the values by `c ≠ 0` keeps the map
of every gated block: hidden unit `i` contributes `σ(z_i) (c⁻¹ u_i) (c a_i) = σ(z_i) u_i a_i`. -/
private theorem block_rescale_ift {χ : Matrix T d ℝ → Matrix T d ℝ}
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

/-! #### Helpers: the derivative of the orbit map is injective -/

/-- Helper (the private `cancel_left_of_rank_lit`): a matrix `M` of rank equal to its number of
columns cancels on the left, `M X = M Y → X = Y` (its kernel is `0` by rank–nullity). -/
private theorem cancel_left_of_rank_ift {m n k : Type*} [Fintype n] (M : Matrix m n ℝ)
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

omit [DecidableEq d] [Fintype dIn] [Fintype dOut] [∀ ℓ, DecidableEq (dh ℓ)] in
/-- Helper (the step `key` of `cobDir_add_headDirQK_add_headDirVO_injective`,
`Symmetry/AttentionHeads.lean`): if the directions `cobDir θ X + headDirQK θ Γ + headDirVO θ Γ'`
and `cobDir θ Y + headDirQK θ Δ + headDirVO θ Δ'` agree and `X_{ℓ-1} = Y_{ℓ-1}`, then the read of
block `ℓ` gives `Γ_ℓ = Δ_ℓ`, `Γ'_ℓ = Δ'_ℓ`, and its write gives `W_ℓ X_ℓ = W_ℓ Y_ℓ`. -/
private theorem attn_step_ift {χ : Matrix T d ℝ → Matrix T d ℝ}
    (θ : Params (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut)
    (hQ : ∀ ℓ (i : H ℓ), ((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k)).rank
      = Fintype.card (dh ℓ))
    (hV : ∀ ℓ (i : H ℓ),
      ((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))).rank
        = Fintype.card (dh ℓ))
    {X Y : Fin (L + 1) → Matrix d d ℝ} {Γ Γ' Δ Δ' : ∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ}
    (h : cobDir θ X + headDirQK θ Γ + headDirVO θ Γ'
      = cobDir θ Y + headDirQK θ Δ + headDirVO θ Δ')
    (ℓ : Fin L) (hℓ : X ℓ.castSucc = Y ℓ.castSucc) :
    Γ ℓ = Δ ℓ ∧ Γ' ℓ = Δ' ℓ ∧ θ.write ℓ * X ℓ.succ = θ.write ℓ * Y ℓ.succ := by
  have hr := congrArg (fun η => η.read ℓ) h
  -- the query columns of head `i` move by `-X_{ℓ-1} W_{Q,i} + W_{Q,i} Γ_i`, and the first terms
  -- agree; `W_{Q,i}` has rank `d_h`
  have hQK : Γ ℓ = Δ ℓ := by
    funext i
    refine cancel_left_of_rank_ift _ (hQ ℓ i) ?_
    ext a k
    have hk := congrFun (congrFun hr a) (i, Sum.inl k)
    change -(X ℓ.castSucc * θ.read ℓ) a (i, Sum.inl k)
        + (∑ k', θ.read ℓ a (i, Sum.inl k') * Γ ℓ i k' k) + 0
      = -(Y ℓ.castSucc * θ.read ℓ) a (i, Sum.inl k)
        + (∑ k', θ.read ℓ a (i, Sum.inl k') * Δ ℓ i k' k) + 0 at hk
    rw [hℓ] at hk
    simp only [add_zero, add_right_inj] at hk
    exact hk
  -- the value columns of head `i` move by `-X_{ℓ-1} W_{V,i} + W_{V,i} Γ'_i`; `W_{V,i}` has rank
  -- `d_h`
  have hVO : Γ' ℓ = Δ' ℓ := by
    funext i
    refine cancel_left_of_rank_ift _ (hV ℓ i) ?_
    ext a k
    have hk := congrFun (congrFun hr a) (i, Sum.inr (Sum.inr k))
    change -(X ℓ.castSucc * θ.read ℓ) a (i, Sum.inr (Sum.inr k)) + 0
        + (∑ k', θ.read ℓ a (i, Sum.inr (Sum.inr k')) * Γ' ℓ i k' k)
      = -(Y ℓ.castSucc * θ.read ℓ) a (i, Sum.inr (Sum.inr k)) + 0
        + (∑ k', θ.read ℓ a (i, Sum.inr (Sum.inr k')) * Δ' ℓ i k' k) at hk
    rw [hℓ] at hk
    simp only [add_zero, add_right_inj] at hk
    exact hk
  refine ⟨hQK, hVO, ?_⟩
  -- the write moves by `W X_ℓ - (Γ'_i W_{O,i})_i`, and the second terms agree
  have hw' := congrArg (fun η => η.write ℓ) h
  change θ.write ℓ * X ℓ.succ + 0 + (headDirVO θ Γ').write ℓ
    = θ.write ℓ * Y ℓ.succ + 0 + (headDirVO θ Δ').write ℓ at hw'
  have hO : (headDirVO θ Γ').write ℓ = (headDirVO θ Δ').write ℓ := by
    ext ⟨i, k⟩ b
    show -∑ k', Γ' ℓ i k k' * θ.write ℓ (i, k') b = -∑ k', Δ' ℓ i k k' * θ.write ℓ (i, k') b
    rw [hVO]
  rw [hO] at hw'
  simp only [add_zero, add_left_inj] at hw'
  exact hw'

omit [Fintype T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: if the reads and the writes of the directions `cobDir θ X + rescaleDir θ α` and
`cobDir θ Y + rescaleDir θ β` of a gated network agree, no value column vanishes and
`X_{ℓ-1} = Y_{ℓ-1}`, then the value columns of block `ℓ` give `α_ℓ = β_ℓ` (the value column `i`
moves by `-X_{ℓ-1} v_i - α_{ℓ,i} v_i`), and its write gives `W_ℓ X_ℓ = W_ℓ Y_ℓ`. -/
private theorem gated_step_ift {χ : Matrix T d ℝ → Matrix T d ℝ}
    (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut)
    (hv : ∀ ℓ i, (fun k => θ.read ℓ k (Sum.inr i)) ≠ 0)
    {X Y : Fin (L + 1) → Matrix d d ℝ} {α β : ∀ ℓ, hid ℓ → ℝ}
    (hr : ∀ ℓ, (cobDir θ X + rescaleDir θ α).read ℓ = (cobDir θ Y + rescaleDir θ β).read ℓ)
    (hwr : ∀ ℓ, (cobDir θ X + rescaleDir θ α).write ℓ = (cobDir θ Y + rescaleDir θ β).write ℓ)
    (ℓ : Fin L) (hℓ : X ℓ.castSucc = Y ℓ.castSucc) :
    α ℓ = β ℓ ∧ θ.write ℓ * X ℓ.succ = θ.write ℓ * Y ℓ.succ := by
  -- the value column `i`: `-(X_{ℓ-1} R)_{k,i} - α_{ℓ,i} R_{k,i}`, at an entry `k` with
  -- `R_{k,i} ≠ 0`
  have hα : α ℓ = β ℓ := by
    funext i
    obtain ⟨k, hk⟩ := Function.ne_iff.mp (hv ℓ i)
    have h3 : (cobDir θ X + rescaleDir θ α).read ℓ k (Sum.inr i)
        = (cobDir θ Y + rescaleDir θ β).read ℓ k (Sum.inr i) := by rw [hr ℓ]
    change -(X ℓ.castSucc * θ.read ℓ) k (Sum.inr i) + -(α ℓ i) * θ.read ℓ k (Sum.inr i)
      = -(Y ℓ.castSucc * θ.read ℓ) k (Sum.inr i) + -(β ℓ i) * θ.read ℓ k (Sum.inr i) at h3
    rw [hℓ, add_right_inj] at h3
    exact neg_inj.mp (mul_right_cancel₀ hk h3)
  refine ⟨hα, ?_⟩
  -- the write moves by `W X_ℓ + (α_{ℓ,i} w_i)_i`, and the second terms agree
  have hw' := hwr ℓ
  change θ.write ℓ * X ℓ.succ + (rescaleDir θ α).write ℓ
    = θ.write ℓ * Y ℓ.succ + (rescaleDir θ β).write ℓ at hw'
  have hR : (rescaleDir θ α).write ℓ = (rescaleDir θ β).write ℓ := by
    ext i k
    show α ℓ i * θ.write ℓ i k = β ℓ i * θ.write ℓ i k
    rw [hα]
  rw [hR, add_left_inj] at hw'
  exact hw'

omit [Fintype T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (the induction of `cobDir_injective`, `Dimension/UpperBound.lean`, for a sum of
blocks): if `E` and the writes of `θ` have rank `d`, `E X_0 = E Y_0`, and `X_{ℓ-1} = Y_{ℓ-1}`
gives `W_ℓ X_ℓ = W_ℓ Y_ℓ` for the write rows of both parts, then `X = Y`. -/
private theorem fam_eq_ift {A B : Arch T d L} (θ : Params (A.sum B) dIn dOut)
    (hE : θ.E.rank = Fintype.card d) (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d)
    {X Y : Fin (L + 1) → Matrix d d ℝ} (h0 : θ.E * X 0 = θ.E * Y 0)
    (hstep : ∀ ℓ : Fin L, X ℓ.castSucc = Y ℓ.castSucc →
      θ.sumFst.write ℓ * X ℓ.succ = θ.sumFst.write ℓ * Y ℓ.succ ∧
        θ.sumSnd.write ℓ * X ℓ.succ = θ.sumSnd.write ℓ * Y ℓ.succ) :
    X = Y := by
  funext ℓ
  induction ℓ using Fin.induction with
  | zero =>
    -- `E` has rank `d`
    exact cancel_left_of_rank_ift θ.E hE h0
  | succ ℓ ih =>
    -- the write of block `ℓ` is made of the write rows of the two parts, and has rank `d`
    obtain ⟨hA, hB⟩ := hstep ℓ ih
    refine cancel_left_of_rank_ift (θ.write ℓ) (hw ℓ) ?_
    ext p k
    rcases p with p | j
    · exact congrFun (congrFun hA p) k
    · exact congrFun (congrFun hB j) k

omit [∀ ℓ, DecidableEq (dh ℓ)] in
/-- Helper (the private `finrank_headFun_lit`): the families `Γ` of `d_h × d_h` matrices, one for
each head of each block, form a space of dimension `∑_ℓ H_ℓ d_{h,ℓ}²`. -/
private theorem finrank_headFun_ift :
    Module.finrank ℝ (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)
      = ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2 := by
  rw [Module.finrank_pi_fintype]
  simp only [Module.finrank_pi_fintype, Module.finrank_matrix, Module.finrank_self, mul_one,
    Finset.sum_const, Finset.card_univ, smul_eq_mul, sq]

/-! #### Helpers: neighborhoods of `0` in the chart of the symmetries -/

/-- Helper: for a continuous linear map `g` into the families of `L + 1` square matrices, the
points `m` with `exp (g m) ∈ V` (matrix by matrix) form a neighborhood of `0`, when `V` is a
neighborhood of `1`. -/
private theorem exp_fam_preimage_mem_nhds_ift {M : Type*} [NormedAddCommGroup M]
    [NormedSpace ℝ M] (g : M →L[ℝ] (Fin (L + 1) → Matrix d d ℝ))
    {V : Set (Fin (L + 1) → Matrix d d ℝ)} (hV : V ∈ 𝓝 (1 : Fin (L + 1) → Matrix d d ℝ)) :
    (fun m => fun ℓ => NormedSpace.exp (g m ℓ)) ⁻¹' V ∈ 𝓝 (0 : M) := by
  -- matrix by matrix, `m ↦ exp (g m ℓ)` is continuous at `0`, with value `exp 0 = 1`
  have hc : ContinuousAt (fun m => fun ℓ => NormedSpace.exp (g m ℓ)) 0 :=
    continuousAt_pi.2 fun ℓ =>
      ContinuousAt.comp_of_eq (f := fun m => g m ℓ)
        (hasStrictFDerivAt_matrix_exp_zero (d := d)).continuousAt
        ((continuous_apply ℓ).comp g.continuous).continuousAt
        (by simp only [map_zero, Pi.zero_apply])
  refine hc.preimage_mem_nhds ?_
  have h1 : (fun ℓ => NormedSpace.exp (g 0 ℓ)) = (1 : Fin (L + 1) → Matrix d d ℝ) := by
    funext ℓ
    simp only [map_zero, Pi.zero_apply, NormedSpace.exp_zero, Pi.one_apply]
  rw [h1]
  exact hV

omit [∀ ℓ, Fintype (H ℓ)] in
/-- Helper (the private `exp_heads_preimage_mem_nhds_lit`): for a continuous linear map `g` into
the families of `d_h × d_h` matrices, the points `m` with `exp (g m) ∈ W` (head by head) form a
neighborhood of `0`, when `W` is a neighborhood of `1`. -/
private theorem exp_heads_preimage_mem_nhds_ift {M : Type*} [NormedAddCommGroup M]
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
/-- Helper (the private `rexp_preimage_mem_nhds_lit`): for a continuous linear map `g` into the
families of reals, one for each hidden unit, the points `m` with `e^{g m} ∈ W` form a
neighborhood of `0`, when `W` is a neighborhood of `1`. -/
private theorem rexp_preimage_mem_nhds_ift {M : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M]
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

/-! #### The argument common to the plain and the pre-RMSNorm statements -/

/-- **The argument common to the two statements of Proposition 4.5 for skipless networks of
attention blocks and MLP blocks.** Let `σ` and `χ` be real-analytic, `E` and the writes of rank
`d`, the query and value matrices of every head of rank `d_h`, and
`ι₀ : N → (Fin (L + 1) → Matrix d d ℝ)` an injective linear map (all families of matrices, or the
families of antisymmetric ones) such that the changes of basis `exp (ι₀ n)` preserve the function.
If `fd(θ) + dim N + s = P`, then every `θ'` near `θ` with the same function is
`(sumOf ((θ_A.headsQK K).headsVO K') θ_B).cob (exp ι₀ n) (exp ι₀ n)` with `exp (ι₀ n) ∈ V` and
`K, K' ∈ W`. The proof: `exists_mem_orbit_of_eval_eq` for the map
`(n, Γ, Γ') ↦ sumOf (cobExpHeads θ_A (ι₀ n, Γ, Γ')) (cobExp θ_B (ι₀ n))`, whose derivative has the
parts `cobDir θ_A (ι₀ n) + headDirQK θ_A Γ + headDirVO θ_A Γ'` and `cobDir θ_B (ι₀ n)`; by
induction along the network, `E` and the reads and writes of the blocks give `(n, Γ, Γ')`. -/
private theorem exists_orbit_mlp_ift {χ : Matrix T d ℝ → Matrix T d ℝ}
    (hσa : AnalyticOnNhd ℝ σ Set.univ) (hχ : AnalyticOnNhd ℝ χ Set.univ)
    (θ : Params (Arch.attentionMlp (T := T) (d := d) sees σ χ H dh hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d) (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d)
    (hQ : ∀ ℓ (i : H ℓ),
      ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k)).rank
        = Fintype.card (dh ℓ))
    (hV : ∀ ℓ (i : H ℓ),
      ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))).rank
        = Fintype.card (dh ℓ))
    {N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N] [FiniteDimensional ℝ N]
    (ι₀ : N →L[ℝ] (Fin (L + 1) → Matrix d d ℝ)) (hι₀ : Function.Injective ι₀)
    (hfd : funDim (Arch.attentionMlp sees σ χ H dh hid) 0 θ
        + (Module.finrank ℝ N + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
      = Module.finrank ℝ (Params
          (Arch.attentionMlp (T := T) (d := d) sees σ χ H dh hid) dIn dOut))
    (hpres : ∀ (n : N)
      (η : Params (Arch.attentionMlp (T := T) (d := d) sees σ χ H dh hid) dIn dOut)
      (x : Matrix T dIn ℝ), eval (Arch.attentionMlp sees σ χ H dh hid) 0
        (η.cob (fun ℓ => expGL (ι₀ n ℓ)) (fun ℓ => expGL (ι₀ n ℓ))) x
        = eval (Arch.attentionMlp sees σ χ H dh hid) 0 η x) :
    ∀ V ∈ 𝓝 (1 : Fin (L + 1) → Matrix d d ℝ),
      ∀ W ∈ 𝓝 (1 : ∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ), ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.attentionMlp sees σ χ H dh hid) 0 θ' x
        = eval (Arch.attentionMlp sees σ χ H dh hid) 0 θ x) →
        ∃ (n : N) (K K' : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ),
          (fun ℓ => NormedSpace.exp (ι₀ n ℓ)) ∈ V
            ∧ (fun ℓ i => (K ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)) ∈ W
            ∧ (fun ℓ i => (K' ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)) ∈ W
            ∧ θ' = (Params.sumOf ((θ.sumFst.headsQK K).headsVO K') θ.sumSnd).cob
                (fun ℓ => expGL (ι₀ n ℓ)) (fun ℓ => expGL (ι₀ n ℓ)) := by
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
  -- the embeddings `p ↦ (ι₀ n, Γ, Γ')` and `p ↦ ι₀ n`: the same family of matrices in both parts
  let ιA : (N × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ))
      →L[ℝ] (Fin (L + 1) → Matrix d d ℝ) × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)
        × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) :=
    (ι₀.comp πN).prod (πQ.prod πV)
  let ιB : (N × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ))
      →L[ℝ] (Fin (L + 1) → Matrix d d ℝ) := ι₀.comp πN
  -- the two parts put together, a continuous linear map
  let Sm := LinearMap.toContinuousLinearMap (sumOfLin_ift
    (A := Arch.attention (T := T) (d := d) sees χ H dh) (B := Arch.mlp (T := T) (d := d) σ χ hid)
    (dIn := dIn) (dOut := dOut))
  -- the orbit map: the changes of basis inside the heads of the first part, then the changes of
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
  -- its derivative is injective (Lemma B.1): the parts of the derivative at `p` are
  -- `cobDir θ_A (ι₀ n) + headDirQK θ_A Γ + headDirVO θ_A Γ'` and `cobDir θ_B (ι₀ n)`
  have hinj : Function.Injective (Sm.comp ((ΦA.comp ιA).prod (ΦB.comp ιB))) := by
    rintro ⟨n, Γ, Γ'⟩ ⟨n', Δ, Δ'⟩ h
    have h1 := congrArg Params.sumFst h
    have h2 : ΦA (ιA (n, Γ, Γ')) = ΦA (ιA (n', Δ, Δ')) := h1
    rw [hΦAv, hΦAv] at h2
    change cobDir θ.sumFst (ι₀ n) + headDirQK θ.sumFst Γ + headDirVO θ.sumFst Γ'
      = cobDir θ.sumFst (ι₀ n') + headDirQK θ.sumFst Δ + headDirVO θ.sumFst Δ' at h2
    -- the write rows of the second part: `W_B ι₀ n ℓ`
    have h4 : ∀ ℓ, (ΦB (ιB (n, Γ, Γ'))).write ℓ = (ΦB (ιB (n', Δ, Δ'))).write ℓ :=
      fun ℓ => Matrix.ext fun j k =>
        congrFun (congrFun (congrArg (fun η => η.write ℓ) h) (Sum.inr j)) k
    rw [hΦBv, hΦBv] at h4
    change ∀ ℓ : Fin L, θ.sumSnd.write ℓ * ι₀ n ℓ.succ = θ.sumSnd.write ℓ * ι₀ n' ℓ.succ at h4
    -- the `E` component gives `ι₀ n 0`
    have h0 : θ.E * ι₀ n 0 = θ.E * ι₀ n' 0 := by
      have hE0 := congrArg Params.E h2
      change θ.E * ι₀ n 0 + 0 + 0 = θ.E * ι₀ n' 0 + 0 + 0 at hE0
      simpa only [add_zero] using hE0
    -- block by block, the reads give the changes inside the heads and the writes give `ι₀ n ℓ`
    have hX : ι₀ n = ι₀ n' := fam_eq_ift θ hE hw h0 fun ℓ hℓ =>
      ⟨(attn_step_ift θ.sumFst hQ hV h2 ℓ hℓ).2.2, h4 ℓ⟩
    have hΓ : Γ = Δ := funext fun ℓ =>
      (attn_step_ift θ.sumFst hQ hV h2 ℓ (congrFun hX ℓ.castSucc)).1
    have hΓ' : Γ' = Δ' := funext fun ℓ =>
      (attn_step_ift θ.sumFst hQ hV h2 ℓ (congrFun hX ℓ.castSucc)).2.1
    rw [hι₀ hX, hΓ, hΓ']
  -- at `p`, it is `θ` after the changes of basis `exp Γ`, `exp Γ'` inside the heads and the
  -- changes of basis `exp (ι₀ n)` of the hidden states
  have hform : ∀ p : N × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)
      × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ), Φ p
      = (Params.sumOf ((θ.sumFst.headsQK fun ℓ i => expGL (p.2.1 ℓ i)).headsVO
          fun ℓ i => expGL (p.2.2 ℓ i)) θ.sumSnd).cob
        (fun ℓ => expGL (ι₀ p.1 ℓ)) (fun ℓ => expGL (ι₀ p.1 ℓ)) := by
    intro p
    rw [← sumOf_cob_ift]
    rfl
  -- so it keeps the function (Appendix B and Proposition 3.2 without skips)
  have hconst : ∀ᶠ p in 𝓝 (0 : N × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)
      × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)), ∀ x : Matrix T dIn ℝ,
      eval (Arch.attentionMlp sees σ χ H dh hid) 0 (Φ p) x
        = eval (Arch.attentionMlp sees σ χ H dh hid) 0 θ x := by
    refine Eventually.of_forall fun p x => ?_
    rw [hform p, hpres]
    have h1 := eval_sumOf_ift θ.sumFst
      ((θ.sumFst.headsQK fun ℓ i => expGL (p.2.1 ℓ i)).headsVO fun ℓ i => expGL (p.2.2 ℓ i))
      θ.sumSnd θ.sumSnd rfl rfl
      (fun ℓ h => (block_headsVO_ift (θ.sumFst.headsQK fun ℓ i => expGL (p.2.1 ℓ i))
        (fun ℓ i => expGL (p.2.2 ℓ i)) ℓ h).trans
        (block_headsQK_ift θ.sumFst (fun ℓ i => expGL (p.2.1 ℓ i)) ℓ h))
      (fun _ _ => rfl) 0 x
    rw [Params.sumOf_sumFst_sumSnd] at h1
    exact h1
  -- the triples `(n, Γ, Γ')` form a space of dimension `dim N + 2 ∑_ℓ H_ℓ d_{h,ℓ}²`
  have hdim : Module.finrank ℝ (N × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)
      × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ))
      = Module.finrank ℝ N + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2 := by
    rw [Module.finrank_prod, Module.finrank_prod, finrank_headFun_ift, two_mul]
  -- the `p` with `exp (ι₀ n) ∈ V`, `exp Γ ∈ W`, `exp Γ' ∈ W` form a neighborhood of `0`
  have hV' := exp_fam_preimage_mem_nhds_ift (ι₀.comp πN) hVn
  have hW1 := exp_heads_preimage_mem_nhds_ift πQ hWn
  have hW2 := exp_heads_preimage_mem_nhds_ift πV hWn
  -- the orbit fills the level set near `θ`
  obtain ⟨U, hU, hUV⟩ := exists_mem_orbit_of_eval_eq (Arch.attentionMlp sees σ χ H dh hid) 0
    (fun ℓ => analyticOnNhd_f_sum (analyticOnNhd_f_attention sees χ H dh ℓ)
      (analyticOnNhd_f_mlp hσa ℓ)) hχ θ hΦ hΦ0 hinj hconst (by rw [hdim]; exact hfd) _
    (inter_mem hV' (inter_mem hW1 hW2))
  refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
  -- `K = exp Γ`, `K' = exp Γ'`
  obtain ⟨p, ⟨hpV, hpW1, hpW2⟩, hpθ⟩ := hUV θ' hθ' heq
  exact ⟨p.1, fun ℓ i => expGL (p.2.1 ℓ i), fun ℓ i => expGL (p.2.2 ℓ i), hpV, hpW1, hpW2,
    hpθ.symm.trans (hform p)⟩

/-! #### Attention blocks and MLP blocks -/

/-- **Proposition 4.5 of the skips paper, from the equality condition to local identifiability, for
a skipless network of attention blocks and MLP blocks, without normalization:** if `E` and the
writes have rank `d`, the query and value matrices of every head have rank `d_h` and `fd(θ) = P − (L
+ 1) dim 𝒢 − s`, then every `θ'` near `θ` with the same function is `θ` after changes of basis
inside the heads, near the identity, and a change of basis by invertible `G_0, …, G_L` near the
identity. -/
theorem exists_cob_heads_of_eval_eq_skipless_attentionMlp
    (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (θ : Params
      (Arch.attentionMlp (T := T) (d := d) sees σ id H dh hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d) (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d)
    (hQ : ∀ ℓ (i : H ℓ),
      ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k)).rank
        = Fintype.card (dh ℓ))
    (hV : ∀ ℓ (i : H ℓ),
      ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))).rank
        = Fintype.card (dh ℓ))
    (hfd : funDim (Arch.attentionMlp sees σ id H dh hid) 0 θ
        + ((L + 1) * Fintype.card d ^ 2
          + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
      = Module.finrank ℝ (Params
          (Arch.attentionMlp (T := T) (d := d) sees σ id H dh hid) dIn dOut)) :
    ∀ V ∈ 𝓝 (1 : Fin (L + 1) → Matrix d d ℝ), ∀ W ∈ 𝓝 (1 : ∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ),
      ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.attentionMlp sees σ id H dh hid) 0 θ' x
        = eval (Arch.attentionMlp sees σ id H dh hid) 0 θ x) →
        ∃ (G : Fin (L + 1) → GL d ℝ) (K K' : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ),
          (fun ℓ => (G ℓ : Matrix d d ℝ)) ∈ V
            ∧ (fun ℓ i => (K ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)) ∈ W
            ∧ (fun ℓ i => (K' ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)) ∈ W
            ∧ θ' = (Params.sumOf ((θ.sumFst.headsQK K).headsVO K') θ.sumSnd).cob
                G G := by
  intro V hVn W hWn
  -- the families of `L + 1` matrices `d × d` form a space of dimension `(L + 1) d²`
  have hdimN : Module.finrank ℝ (Fin (L + 1) → Matrix d d ℝ) = (L + 1) * Fintype.card d ^ 2 := by
    rw [Module.finrank_pi_fintype]
    simp only [Module.finrank_matrix, Module.finrank_self, mul_one, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul, sq]
  -- the orbit of the changes of basis inside the heads and of the changes of basis `exp m_ℓ` of
  -- the hidden states fills the level set near `θ` (Proposition 3.2 without skips)
  obtain ⟨U, hU, hUV⟩ := exists_orbit_mlp_ift hσa analyticOnNhd_id θ hE hw hQ hV
    (ContinuousLinearMap.id ℝ (Fin (L + 1) → Matrix d d ℝ)) (fun _ _ h => h)
    (by rw [hdimN]; exact hfd)
    (fun _ η x => eval_cob_skipless (A := Arch.attentionMlp sees σ id H dh hid) η _ x rfl)
    V hVn W hWn
  refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
  -- `G_ℓ = exp m_ℓ`
  obtain ⟨m, K, K', hm, hK, hK', hθ'⟩ := hUV θ' hθ' heq
  exact ⟨fun ℓ => expGL (m ℓ), K, K', hm, hK, hK', hθ'⟩

/-- **Proposition 4.5 of the skips paper, from the equality condition to local identifiability, for
a skipless network of attention blocks and MLP blocks, under pre-RMSNorm (`ε > 0`):** if `E` and the
writes have rank `d`, the query and value matrices of every head have rank `d_h` and `fd(θ) = P − (L
+ 1) dim 𝒢 − s`, then every `θ'` near `θ` with the same function is `θ` after changes of basis
inside the heads, near the identity, and a change of basis by orthogonal `Q_0, …, Q_L` near the
identity. -/
theorem exists_cob_heads_of_eval_eq_skipless_attentionMlp_rmsNorm (hε : 0 < ε)
    (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (θ : Params
      (Arch.attentionMlp (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d) (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d)
    (hQ : ∀ ℓ (i : H ℓ),
      ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k)).rank
        = Fintype.card (dh ℓ))
    (hV : ∀ ℓ (i : H ℓ),
      ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))).rank
        = Fintype.card (dh ℓ))
    (hfd : funDim (Arch.attentionMlp sees σ (rmsNorm ε) H dh hid) 0 θ
        + ((L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2)
          + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
      = Module.finrank ℝ (Params
          (Arch.attentionMlp (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut)) :
    ∀ V ∈ 𝓝 (1 : Fin (L + 1) → Matrix d d ℝ), ∀ W ∈ 𝓝 (1 : ∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ),
      ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.attentionMlp sees σ (rmsNorm ε) H dh hid) 0 θ' x
        = eval (Arch.attentionMlp sees σ (rmsNorm ε) H dh hid) 0 θ x) →
        ∃ (Q : Fin (L + 1) → GL d ℝ) (K K' : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ),
          (∀ ℓ, (Q ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ)
            ∧ (fun ℓ => (Q ℓ : Matrix d d ℝ)) ∈ V
            ∧ (fun ℓ i => (K ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)) ∈ W
            ∧ (fun ℓ i => (K' ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)) ∈ W
            ∧ θ' = (Params.sumOf ((θ.sumFst.headsQK K).headsVO K') θ.sumSnd).cob
                Q Q := by
  intro V hVn W hWn
  -- the families of `L + 1` antisymmetric matrices, inside all the families of matrices
  let ι₀ : (Fin (L + 1) → antisymmetric d) →L[ℝ] (Fin (L + 1) → Matrix d d ℝ) :=
    ContinuousLinearMap.pi fun ℓ =>
      (antisymmetric d).subtypeL.comp (ContinuousLinearMap.proj ℓ)
  have hι₀ : Function.Injective ι₀ := fun a b h => funext fun ℓ => Subtype.ext (congrFun h ℓ)
  -- they form a space of dimension `(L + 1) d (d - 1) / 2`
  have hdimN : Module.finrank ℝ (Fin (L + 1) → antisymmetric d)
      = (L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2) := by
    rw [Module.finrank_pi_fintype, finrank_antisymmetric, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul]
  -- the changes of basis `exp a_ℓ`, `a_ℓ` antisymmetric, are orthogonal
  have horth : ∀ (a : Fin (L + 1) → antisymmetric d) ℓ,
      ((expGL (ι₀ a ℓ) : GL d ℝ) : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ :=
    fun a ℓ => exp_mem_orthogonalGroup_of_transpose_eq_neg (a ℓ).2
  -- the orbit of the changes of basis inside the heads and of the orthogonal changes of basis
  -- `exp a_ℓ` of the hidden states fills the level set near `θ` (Proposition 3.2 under
  -- pre-RMSNorm)
  obtain ⟨U, hU, hUV⟩ := exists_orbit_mlp_ift hσa (analyticOnNhd_rmsNorm hε) θ hE hw hQ hV ι₀
    hι₀ (by rw [hdimN]; exact hfd)
    (fun a η x => eval_cob_rmsNorm (A := Arch.attentionMlp sees σ (rmsNorm ε) H dh hid) η x ε
      rfl _ (horth a)) V hVn W hWn
  refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
  -- `Q_ℓ = exp a_ℓ`
  obtain ⟨a, K, K', ha, hK, hK', hθ'⟩ := hUV θ' hθ' heq
  exact ⟨fun ℓ => expGL (ι₀ a ℓ), K, K', horth a, ha, hK, hK', hθ'⟩

/-! #### Attention blocks and gated blocks -/

/-- **The argument common to the two statements of Proposition 4.5 for skipless networks of
attention blocks and gated blocks.** As `exists_orbit_mlp_ift`, with the rescalings `e^α` of the
values of the gated units: the map
`(n, Γ, Γ', α) ↦ sumOf (cobExpHeads θ_A (ι₀ n, Γ, Γ')) (cobExpRescale θ_B (ι₀ n, α))` has the
derivative with the parts `cobDir θ_A (ι₀ n) + headDirQK θ_A Γ + headDirVO θ_A Γ'` and
`cobDir θ_B (ι₀ n) + rescaleDir θ_B α`; by induction along the network, `E` and the reads and
writes of the blocks give `(n, Γ, Γ', α)`. -/
private theorem exists_orbit_gated_ift {χ : Matrix T d ℝ → Matrix T d ℝ}
    (hσa : AnalyticOnNhd ℝ σ Set.univ) (hχ : AnalyticOnNhd ℝ χ Set.univ)
    (θ : Params (Arch.attentionGated (T := T) (d := d) sees σ χ H dh hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d) (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d)
    (hQ : ∀ ℓ (i : H ℓ),
      ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k)).rank
        = Fintype.card (dh ℓ))
    (hV : ∀ ℓ (i : H ℓ),
      ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))).rank
        = Fintype.card (dh ℓ))
    (hv : ∀ ℓ i, (fun k => θ.sumSnd.read ℓ k (Sum.inr i)) ≠ 0)
    {N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N] [FiniteDimensional ℝ N]
    (ι₀ : N →L[ℝ] (Fin (L + 1) → Matrix d d ℝ)) (hι₀ : Function.Injective ι₀)
    (hfd : funDim (Arch.attentionGated sees σ χ H dh hid) 0 θ
        + (Module.finrank ℝ N + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
          + ∑ ℓ, Fintype.card (hid ℓ)))
      = Module.finrank ℝ (Params
          (Arch.attentionGated (T := T) (d := d) sees σ χ H dh hid) dIn dOut))
    (hpres : ∀ (n : N)
      (η : Params (Arch.attentionGated (T := T) (d := d) sees σ χ H dh hid) dIn dOut)
      (x : Matrix T dIn ℝ), eval (Arch.attentionGated sees σ χ H dh hid) 0
        (η.cob (fun ℓ => expGL (ι₀ n ℓ)) (fun ℓ => expGL (ι₀ n ℓ))) x
        = eval (Arch.attentionGated sees σ χ H dh hid) 0 η x) :
    ∀ V ∈ 𝓝 (1 : Fin (L + 1) → Matrix d d ℝ),
      ∀ W ∈ 𝓝 (1 : ∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ),
      ∀ Wc ∈ 𝓝 (1 : ∀ ℓ, hid ℓ → ℝ), ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.attentionGated sees σ χ H dh hid) 0 θ' x
        = eval (Arch.attentionGated sees σ χ H dh hid) 0 θ x) →
        ∃ (n : N) (K K' : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ) (c : ∀ ℓ, hid ℓ → ℝ),
          (fun ℓ => NormedSpace.exp (ι₀ n ℓ)) ∈ V
            ∧ (fun ℓ i => (K ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)) ∈ W
            ∧ (fun ℓ i => (K' ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)) ∈ W
            ∧ c ∈ Wc ∧ (∀ ℓ i, 0 < c ℓ i)
            ∧ θ' = (Params.sumOf ((θ.sumFst.headsQK K).headsVO K') (θ.sumSnd.rescale c)).cob
                (fun ℓ => expGL (ι₀ n ℓ)) (fun ℓ => expGL (ι₀ n ℓ)) := by
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
  -- the embeddings `p ↦ (ι₀ n, Γ, Γ')` and `p ↦ (ι₀ n, α)`
  let ιA : (N × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)
      × (∀ ℓ, hid ℓ → ℝ)) →L[ℝ] (Fin (L + 1) → Matrix d d ℝ)
        × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) :=
    (ι₀.comp πN).prod (πQ.prod πV)
  let ιB : (N × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)
      × (∀ ℓ, hid ℓ → ℝ)) →L[ℝ] (Fin (L + 1) → Matrix d d ℝ) × (∀ ℓ, hid ℓ → ℝ) :=
    (ι₀.comp πN).prod πα
  -- the two parts put together, a continuous linear map
  let Sm := LinearMap.toContinuousLinearMap (sumOfLin_ift
    (A := Arch.attention (T := T) (d := d) sees χ H dh)
    (B := Arch.gated (T := T) (d := d) σ χ hid) (dIn := dIn) (dOut := dOut))
  -- the orbit map: the changes of basis inside the heads of the first part, the rescalings of the
  -- values of the second, then the changes of basis `exp (ι₀ n)` of the hidden states
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
  -- its derivative is injective (Lemma B.1): the parts of the derivative at `p` are
  -- `cobDir θ_A (ι₀ n) + headDirQK θ_A Γ + headDirVO θ_A Γ'` and
  -- `cobDir θ_B (ι₀ n) + rescaleDir θ_B α`
  have hinj : Function.Injective (Sm.comp ((ΦA.comp ιA).prod (ΦB.comp ιB))) := by
    rintro ⟨n, Γ, Γ', α⟩ ⟨n', Δ, Δ', β⟩ h
    have h1 := congrArg Params.sumFst h
    have h2 : ΦA (ιA (n, Γ, Γ', α)) = ΦA (ιA (n', Δ, Δ', β)) := h1
    rw [hΦAv, hΦAv] at h2
    change cobDir θ.sumFst (ι₀ n) + headDirQK θ.sumFst Γ + headDirVO θ.sumFst Γ'
      = cobDir θ.sumFst (ι₀ n') + headDirQK θ.sumFst Δ + headDirVO θ.sumFst Δ' at h2
    -- the read columns and the write rows of the second part
    have h4 : ∀ ℓ, (ΦB (ιB (n, Γ, Γ', α))).read ℓ = (ΦB (ιB (n', Δ, Δ', β))).read ℓ :=
      fun ℓ => Matrix.ext fun k j =>
        congrFun (congrFun (congrArg (fun η => η.read ℓ) h) k) (Sum.inr j)
    have h5 : ∀ ℓ, (ΦB (ιB (n, Γ, Γ', α))).write ℓ = (ΦB (ιB (n', Δ, Δ', β))).write ℓ :=
      fun ℓ => Matrix.ext fun j k =>
        congrFun (congrFun (congrArg (fun η => η.write ℓ) h) (Sum.inr j)) k
    rw [hΦBv, hΦBv] at h4 h5
    change ∀ ℓ, (cobDir θ.sumSnd (ι₀ n) + rescaleDir θ.sumSnd α).read ℓ
      = (cobDir θ.sumSnd (ι₀ n') + rescaleDir θ.sumSnd β).read ℓ at h4
    change ∀ ℓ, (cobDir θ.sumSnd (ι₀ n) + rescaleDir θ.sumSnd α).write ℓ
      = (cobDir θ.sumSnd (ι₀ n') + rescaleDir θ.sumSnd β).write ℓ at h5
    -- the `E` component gives `ι₀ n 0`
    have h0 : θ.E * ι₀ n 0 = θ.E * ι₀ n' 0 := by
      have hE0 := congrArg Params.E h2
      change θ.E * ι₀ n 0 + 0 + 0 = θ.E * ι₀ n' 0 + 0 + 0 at hE0
      simpa only [add_zero] using hE0
    -- block by block, the reads give the changes inside the heads and the rescalings, and the
    -- writes give `ι₀ n ℓ`
    have hX : ι₀ n = ι₀ n' := fam_eq_ift θ hE hw h0 fun ℓ hℓ =>
      ⟨(attn_step_ift θ.sumFst hQ hV h2 ℓ hℓ).2.2, (gated_step_ift θ.sumSnd hv h4 h5 ℓ hℓ).2⟩
    have hΓ : Γ = Δ := funext fun ℓ =>
      (attn_step_ift θ.sumFst hQ hV h2 ℓ (congrFun hX ℓ.castSucc)).1
    have hΓ' : Γ' = Δ' := funext fun ℓ =>
      (attn_step_ift θ.sumFst hQ hV h2 ℓ (congrFun hX ℓ.castSucc)).2.1
    have hα : α = β := funext fun ℓ =>
      (gated_step_ift θ.sumSnd hv h4 h5 ℓ (congrFun hX ℓ.castSucc)).1
    rw [hι₀ hX, hΓ, hΓ', hα]
  -- at `p`, it is `θ` after the changes of basis `exp Γ`, `exp Γ'` inside the heads, the
  -- rescalings `e^α` and the changes of basis `exp (ι₀ n)` of the hidden states
  have hform : ∀ p : N × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)
      × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) × (∀ ℓ, hid ℓ → ℝ), Φ p
      = (Params.sumOf ((θ.sumFst.headsQK fun ℓ i => expGL (p.2.1 ℓ i)).headsVO
          fun ℓ i => expGL (p.2.2.1 ℓ i))
          (θ.sumSnd.rescale fun ℓ i => Real.exp (p.2.2.2 ℓ i))).cob
        (fun ℓ => expGL (ι₀ p.1 ℓ)) (fun ℓ => expGL (ι₀ p.1 ℓ)) := by
    intro p
    rw [← sumOf_cob_ift]
    rfl
  -- so it keeps the function (Appendix B and Proposition 3.2 without skips)
  have hconst : ∀ᶠ p in 𝓝 (0 : N × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)
      × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) × (∀ ℓ, hid ℓ → ℝ)), ∀ x : Matrix T dIn ℝ,
      eval (Arch.attentionGated sees σ χ H dh hid) 0 (Φ p) x
        = eval (Arch.attentionGated sees σ χ H dh hid) 0 θ x := by
    refine Eventually.of_forall fun p x => ?_
    rw [hform p, hpres]
    have h1 := eval_sumOf_ift θ.sumFst
      ((θ.sumFst.headsQK fun ℓ i => expGL (p.2.1 ℓ i)).headsVO fun ℓ i => expGL (p.2.2.1 ℓ i))
      θ.sumSnd (θ.sumSnd.rescale fun ℓ i => Real.exp (p.2.2.2 ℓ i)) rfl rfl
      (fun ℓ h => (block_headsVO_ift (θ.sumFst.headsQK fun ℓ i => expGL (p.2.1 ℓ i))
        (fun ℓ i => expGL (p.2.2.1 ℓ i)) ℓ h).trans
        (block_headsQK_ift θ.sumFst (fun ℓ i => expGL (p.2.1 ℓ i)) ℓ h))
      (fun ℓ h => block_rescale_ift θ.sumSnd (fun ℓ i => Real.exp (p.2.2.2 ℓ i))
        (fun ℓ i => (Real.exp_pos _).ne') ℓ h) 0 x
    rw [Params.sumOf_sumFst_sumSnd] at h1
    exact h1
  -- the `p` form a space of dimension `dim N + 2 ∑_ℓ H_ℓ d_{h,ℓ}² + ∑_ℓ d_hidden,ℓ`
  have hdim : Module.finrank ℝ (N × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)
      × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) × (∀ ℓ, hid ℓ → ℝ))
      = Module.finrank ℝ N + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
        + ∑ ℓ, Fintype.card (hid ℓ)) := by
    rw [Module.finrank_prod, Module.finrank_prod, Module.finrank_prod, finrank_headFun_ift,
      Module.finrank_pi_fintype]
    simp only [Module.finrank_fintype_fun_eq_card]
    ring
  -- the `p` with `exp (ι₀ n) ∈ V`, `exp Γ, exp Γ' ∈ W`, `e^α ∈ Wc` form a neighborhood of `0`
  have hV' := exp_fam_preimage_mem_nhds_ift (ι₀.comp πN) hVn
  have hW1 := exp_heads_preimage_mem_nhds_ift πQ hWn
  have hW2 := exp_heads_preimage_mem_nhds_ift πV hWn
  have hW3 := rexp_preimage_mem_nhds_ift πα hWc
  -- the orbit fills the level set near `θ`
  obtain ⟨U, hU, hUV⟩ := exists_mem_orbit_of_eval_eq (Arch.attentionGated sees σ χ H dh hid) 0
    (fun ℓ => analyticOnNhd_f_sum (analyticOnNhd_f_attention sees χ H dh ℓ)
      (analyticOnNhd_f_gated hσa ℓ)) hχ θ hΦ hΦ0 hinj hconst (by rw [hdim]; exact hfd) _
    (inter_mem hV' (inter_mem hW1 (inter_mem hW2 hW3)))
  refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
  -- `K = exp Γ`, `K' = exp Γ'`, `c = e^α`
  obtain ⟨p, ⟨hpV, hpW1, hpW2, hpW3⟩, hpθ⟩ := hUV θ' hθ' heq
  exact ⟨p.1, fun ℓ i => expGL (p.2.1 ℓ i), fun ℓ i => expGL (p.2.2.1 ℓ i),
    fun ℓ i => Real.exp (p.2.2.2 ℓ i), hpV, hpW1, hpW2, hpW3, fun ℓ i => Real.exp_pos _,
    hpθ.symm.trans (hform p)⟩

/-- **Proposition 4.5 of the skips paper, from the equality condition to local identifiability, for
a skipless network of attention blocks and gated blocks, without normalization:** if `E` and the
writes have rank `d`, the query and value matrices of every head have rank `d_h`, no value column of
a gated unit vanishes and `fd(θ) = P − (L + 1) dim 𝒢 − s`, then every `θ'` near `θ` with the same
function is `θ` after changes of basis inside the heads and rescalings of the values of the gated
units, near the identity, and a change of basis by invertible `G_0, …, G_L` near the identity. -/
theorem exists_cob_heads_of_eval_eq_skipless_attentionGated
    (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (θ : Params
      (Arch.attentionGated (T := T) (d := d) sees σ id H dh hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d) (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d)
    (hQ : ∀ ℓ (i : H ℓ),
      ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k)).rank
        = Fintype.card (dh ℓ))
    (hV : ∀ ℓ (i : H ℓ),
      ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))).rank
        = Fintype.card (dh ℓ))
    (hv : ∀ ℓ i, (fun k => θ.sumSnd.read ℓ k (Sum.inr i)) ≠ 0)
    (hfd : funDim (Arch.attentionGated sees σ id H dh hid) 0 θ
        + ((L + 1) * Fintype.card d ^ 2
          + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
            + ∑ ℓ, Fintype.card (hid ℓ)))
      = Module.finrank ℝ (Params
          (Arch.attentionGated (T := T) (d := d) sees σ id H dh hid) dIn dOut)) :
    ∀ V ∈ 𝓝 (1 : Fin (L + 1) → Matrix d d ℝ), ∀ W ∈ 𝓝 (1 : ∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ),
      ∀ Wc ∈ 𝓝 (1 : ∀ ℓ, hid ℓ → ℝ), ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.attentionGated sees σ id H dh hid) 0 θ' x
        = eval (Arch.attentionGated sees σ id H dh hid) 0 θ x) →
        ∃ (G : Fin (L + 1) → GL d ℝ) (K K' : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ) (c : ∀ ℓ, hid ℓ → ℝ),
          (fun ℓ => (G ℓ : Matrix d d ℝ)) ∈ V
            ∧ (fun ℓ i => (K ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)) ∈ W
            ∧ (fun ℓ i => (K' ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)) ∈ W
            ∧ c ∈ Wc ∧ (∀ ℓ i, 0 < c ℓ i)
            ∧ θ' = (Params.sumOf ((θ.sumFst.headsQK K).headsVO K') (θ.sumSnd.rescale c)).cob
                G G := by
  intro V hVn W hWn Wc hWc
  -- the families of `L + 1` matrices `d × d` form a space of dimension `(L + 1) d²`
  have hdimN : Module.finrank ℝ (Fin (L + 1) → Matrix d d ℝ) = (L + 1) * Fintype.card d ^ 2 := by
    rw [Module.finrank_pi_fintype]
    simp only [Module.finrank_matrix, Module.finrank_self, mul_one, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul, sq]
  -- the orbit of the changes of basis inside the heads, of the rescalings of the values and of the
  -- changes of basis `exp m_ℓ` of the hidden states fills the level set near `θ`
  obtain ⟨U, hU, hUV⟩ := exists_orbit_gated_ift hσa analyticOnNhd_id θ hE hw hQ hV hv
    (ContinuousLinearMap.id ℝ (Fin (L + 1) → Matrix d d ℝ)) (fun _ _ h => h)
    (by rw [hdimN]; exact hfd)
    (fun _ η x => eval_cob_skipless (A := Arch.attentionGated sees σ id H dh hid) η _ x rfl)
    V hVn W hWn Wc hWc
  refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
  -- `G_ℓ = exp m_ℓ`
  obtain ⟨m, K, K', c, hm, hK, hK', hc, hc0, hθ'⟩ := hUV θ' hθ' heq
  exact ⟨fun ℓ => expGL (m ℓ), K, K', c, hm, hK, hK', hc, hc0, hθ'⟩

/-- **Proposition 4.5 of the skips paper, from the equality condition to local identifiability, for
a skipless network of attention blocks and gated blocks, under pre-RMSNorm (`ε > 0`):** if `E` and
the writes have rank `d`, the query and value matrices of every head have rank `d_h`, no value
column of a gated unit vanishes and `fd(θ) = P − (L + 1) dim 𝒢 − s`, then every `θ'` near `θ` with
the same function is `θ` after changes of basis inside the heads and rescalings of the values of the
gated units, near the identity, and a change of basis by orthogonal `Q_0, …, Q_L` near the identity.
-/
theorem exists_cob_heads_of_eval_eq_skipless_attentionGated_rmsNorm (hε : 0 < ε)
    (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (θ : Params
      (Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d) (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d)
    (hQ : ∀ ℓ (i : H ℓ),
      ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k)).rank
        = Fintype.card (dh ℓ))
    (hV : ∀ ℓ (i : H ℓ),
      ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))).rank
        = Fintype.card (dh ℓ))
    (hv : ∀ ℓ i, (fun k => θ.sumSnd.read ℓ k (Sum.inr i)) ≠ 0)
    (hfd : funDim (Arch.attentionGated sees σ (rmsNorm ε) H dh hid) 0 θ
        + ((L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2)
          + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
            + ∑ ℓ, Fintype.card (hid ℓ)))
      = Module.finrank ℝ (Params
          (Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut)) :
    ∀ V ∈ 𝓝 (1 : Fin (L + 1) → Matrix d d ℝ), ∀ W ∈ 𝓝 (1 : ∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ),
      ∀ Wc ∈ 𝓝 (1 : ∀ ℓ, hid ℓ → ℝ), ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.attentionGated sees σ (rmsNorm ε) H dh hid) 0 θ' x
        = eval (Arch.attentionGated sees σ (rmsNorm ε) H dh hid) 0 θ x) →
        ∃ (Q : Fin (L + 1) → GL d ℝ) (K K' : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ) (c : ∀ ℓ, hid ℓ → ℝ),
          (∀ ℓ, (Q ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ)
            ∧ (fun ℓ => (Q ℓ : Matrix d d ℝ)) ∈ V
            ∧ (fun ℓ i => (K ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)) ∈ W
            ∧ (fun ℓ i => (K' ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)) ∈ W
            ∧ c ∈ Wc ∧ (∀ ℓ i, 0 < c ℓ i)
            ∧ θ' = (Params.sumOf ((θ.sumFst.headsQK K).headsVO K') (θ.sumSnd.rescale c)).cob
                Q Q := by
  intro V hVn W hWn Wc hWc
  -- the families of `L + 1` antisymmetric matrices, inside all the families of matrices
  let ι₀ : (Fin (L + 1) → antisymmetric d) →L[ℝ] (Fin (L + 1) → Matrix d d ℝ) :=
    ContinuousLinearMap.pi fun ℓ =>
      (antisymmetric d).subtypeL.comp (ContinuousLinearMap.proj ℓ)
  have hι₀ : Function.Injective ι₀ := fun a b h => funext fun ℓ => Subtype.ext (congrFun h ℓ)
  -- they form a space of dimension `(L + 1) d (d - 1) / 2`
  have hdimN : Module.finrank ℝ (Fin (L + 1) → antisymmetric d)
      = (L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2) := by
    rw [Module.finrank_pi_fintype, finrank_antisymmetric, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul]
  -- the changes of basis `exp a_ℓ`, `a_ℓ` antisymmetric, are orthogonal
  have horth : ∀ (a : Fin (L + 1) → antisymmetric d) ℓ,
      ((expGL (ι₀ a ℓ) : GL d ℝ) : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ :=
    fun a ℓ => exp_mem_orthogonalGroup_of_transpose_eq_neg (a ℓ).2
  -- the orbit of the changes of basis inside the heads, of the rescalings of the values and of the
  -- orthogonal changes of basis `exp a_ℓ` of the hidden states fills the level set near `θ`
  obtain ⟨U, hU, hUV⟩ := exists_orbit_gated_ift hσa (analyticOnNhd_rmsNorm hε) θ hE hw hQ hV hv
    ι₀ hι₀ (by rw [hdimN]; exact hfd)
    (fun a η x => eval_cob_rmsNorm (A := Arch.attentionGated sees σ (rmsNorm ε) H dh hid) η x ε
      rfl _ (horth a)) V hVn W hWn Wc hWc
  refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
  -- `Q_ℓ = exp a_ℓ`
  obtain ⟨a, K, K', c, ha, hK, hK', hc, hc0, hθ'⟩ := hUV θ' hθ' heq
  exact ⟨fun ℓ => expGL (ι₀ a ℓ), K, K', c, horth a, ha, hK, hK', hc, hc0, hθ'⟩

/-! ### The equivalence at generic parameters -/

/-- **Proposition 4.5 of the skips paper, for skipless networks of attention blocks and MLP blocks
with a real-analytic activation, in any order, without normalization:** `fd = P − (L + 1) d² − s` at
almost every parameter (`s = 2 ∑ H d_h²`) if and only if at almost every parameter `θ` every `θ'`
near `θ` with the same function is `θ` after changes of basis inside the heads and a change of basis
by invertible `G_0, …, G_L`. -/
theorem ae_funDim_attentionMlp_skipless_iff_ae_locally_cob_heads
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
        ∃ K K' : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ,
          ∃ G : Fin (L + 1) → GL d ℝ,
            θ' = (Params.sumOf ((θ.sumFst.headsQK K).headsVO K') θ.sumSnd).cob G G) := by
  sorry

/-- **Proposition 4.5 of the skips paper, for skipless networks of attention blocks and MLP blocks
with a real-analytic activation, in any order, under pre-RMSNorm with `ε > 0`:** `fd = P − (L + 1)
d(d−1)/2 − s` at almost every parameter (`s = 2 ∑ H d_h²`) if and only if at almost every parameter
`θ` every `θ'` near `θ` with the same function is `θ` after changes of basis inside the heads and a
change of basis by orthogonal `Q_0, …, Q_L`. -/
theorem ae_funDim_attentionMlp_skipless_iff_ae_locally_cob_heads_rmsNorm
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
        ∃ K K' : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ,
          ∃ Q : Fin (L + 1) → GL d ℝ,
            (∀ ℓ, (Q ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ) ∧
            θ' = (Params.sumOf ((θ.sumFst.headsQK K).headsVO K') θ.sumSnd).cob Q Q) := by
  sorry

/-- **Proposition 4.5 of the skips paper, for skipless networks of attention blocks and gated blocks
with a real-analytic gate, in any order, without normalization:** `fd = P − (L + 1) d² − s` at
almost every parameter (`s = 2 ∑ H d_h² + ∑ d_hidden`) if and only if at almost every parameter `θ`
every `θ'` near `θ` with the same function is `θ` after changes of basis inside the heads, a
rescaling of the values of the hidden units by nonzero factors `c` and a change of basis by
invertible `G_0, …, G_L`. -/
theorem ae_funDim_attentionGated_skipless_iff_ae_locally_cob_heads_rescale
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
        ∃ (K K' : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ) (c : ∀ ℓ, hid ℓ → ℝ), (∀ ℓ i, c ℓ i ≠ 0) ∧
          ∃ G : Fin (L + 1) → GL d ℝ,
            θ' = (Params.sumOf ((θ.sumFst.headsQK K).headsVO K') (θ.sumSnd.rescale c)).cob G G) :=
                by
  sorry

/-- **Proposition 4.5 of the skips paper, for skipless networks of attention blocks and gated blocks
with a real-analytic gate, in any order, under pre-RMSNorm with `ε > 0`:** `fd = P − (L + 1)
d(d−1)/2 − s` at almost every parameter (`s = 2 ∑ H d_h² + ∑ d_hidden`) if and only if at almost
every parameter `θ` every `θ'` near `θ` with the same function is `θ` after changes of basis inside
the heads, a rescaling of the values of the hidden units by nonzero factors `c` and a change of
basis by orthogonal `Q_0, …, Q_L`. -/
theorem ae_funDim_attentionGated_skipless_iff_ae_locally_cob_heads_rescale_rmsNorm
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
        ∃ (K K' : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ) (c : ∀ ℓ, hid ℓ → ℝ), (∀ ℓ i, c ℓ i ≠ 0) ∧
          ∃ Q : Fin (L + 1) → GL d ℝ,
            (∀ ℓ, (Q ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ) ∧
            θ' = (Params.sumOf ((θ.sumFst.headsQK K).headsVO K') (θ.sumSnd.rescale c)).cob Q Q) :=
                by
  sorry

end Skips
