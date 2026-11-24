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
gated blocks, the rescalings of the values of the hidden units. These are the continuous
symmetries; the permutations of hidden units or heads and the sign flips of tanh units are not in
the family, so the direction from local identifiability to the equality condition is proved here
for this smaller family (with all the symmetries:
`Dimension/IdentifiableIffTransformerFamily.lean`,
`Dimension/IdentifiableIffTransformerFinite.lean`).
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

/-! #### Helpers: families of parameters of class `C¹` -/

omit [Fintype T] [DecidableEq d] in
/-- Helper (the private `contDiffOn_params_iffr` of `Residual/IdentifiableIff.lean`): a family of
parameters is of class `C¹` on a set if every entry of its four components is. -/
private theorem contDiffOn_params_ift {A : Arch T d L} {N : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] {f : N → Params A dIn dOut} {Ω : Set N}
    (hE : ∀ i j, ContDiffOn ℝ 1 (fun n => (f n).E i j) Ω)
    (hr : ∀ ℓ k j, ContDiffOn ℝ 1 (fun n => (f n).read ℓ k j) Ω)
    (hw : ∀ ℓ j k, ContDiffOn ℝ 1 (fun n => (f n).write ℓ j k) Ω)
    (hD : ∀ k j, ContDiffOn ℝ 1 (fun n => (f n).D k j) Ω) :
    ContDiffOn ℝ 1 f Ω := by
  let e := (Params.linearEquivProd (A := A) (dIn := dIn) (dOut := dOut)).toContinuousLinearEquiv
  rw [← e.comp_contDiffOn_iff]
  -- the four components, entry by entry
  have h : ContDiffOn ℝ 1 (fun n => ((f n).E, (f n).read, (f n).write, (f n).D)) Ω :=
    (contDiffOn_pi' fun i => contDiffOn_pi' fun j => hE i j).prodMk
      ((contDiffOn_pi' fun ℓ => contDiffOn_pi' fun k => contDiffOn_pi' fun j => hr ℓ k j).prodMk
        ((contDiffOn_pi' fun ℓ => contDiffOn_pi' fun j => contDiffOn_pi' fun k =>
          hw ℓ j k).prodMk (contDiffOn_pi' fun k => contDiffOn_pi' fun j => hD k j)))
  exact h

omit [Fintype T] [DecidableEq d] in
/-- Helper (the private `contDiffOn_sumOf_iffr`): the parameters of the sum, made of two families
of class `C¹`, are of class `C¹` (`Params.sumOf` is linear). -/
private theorem contDiffOn_sumOf_ift {A B : Arch T d L} {N : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] {fa : N → Params A dIn dOut} {fb : N → Params B dIn dOut} {Ω : Set N}
    (ha : ContDiffOn ℝ 1 fa Ω) (hb : ContDiffOn ℝ 1 fb Ω) :
    ContDiffOn ℝ 1 (fun n => Params.sumOf (fa n) (fb n)) Ω := by
  have h := (LinearMap.toContinuousLinearMap
    (sumOfLin_ift (A := A) (B := B) (dIn := dIn) (dOut := dOut))).contDiff.comp_contDiffOn
      (ha.prodMk hb)
  exact h

/-- Helper (the private `finrank_hidFun_iffr`): the space of the factors of the rescalings has
dimension `∑ d_hidden`. -/
private theorem finrank_hidFun_ift :
    Module.finrank ℝ (∀ ℓ, hid ℓ → ℝ) = ∑ ℓ, Fintype.card (hid ℓ) := by
  rw [Module.finrank_pi_fintype]
  simp only [Module.finrank_fintype_fun_eq_card]

omit [Fintype T] [DecidableEq d] in
/-- Helper (the private `contDiffOn_rescale_iffr`): the rescalings `c ↦ θ.rescale c` are of class
`C¹` where no factor vanishes. -/
private theorem contDiffOn_rescale_ift {χ : Matrix T d ℝ → Matrix T d ℝ}
    (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut) :
    ContDiffOn ℝ 1 (fun c => θ.rescale c) {c : ∀ ℓ, hid ℓ → ℝ | ∀ ℓ i, c ℓ i ≠ 0} := by
  refine contDiffOn_params_ift (fun i j => contDiffOn_const (c := θ.E i j)) (fun ℓ k j => ?_)
    (fun ℓ i k => ?_) (fun k j => contDiffOn_const (c := θ.D k j))
  · rcases j with i | i
    · -- the gate columns do not change
      exact contDiffOn_const (c := θ.read ℓ k (Sum.inl i))
    · -- the value columns are divided by `c_{ℓ i}`, which does not vanish on the set
      have hc : ContDiff ℝ 1 fun c : (∀ ℓ, hid ℓ → ℝ) => c ℓ i := by fun_prop
      exact (hc.contDiffOn.inv fun c (hc0 : ∀ ℓ i, c ℓ i ≠ 0) => hc0 ℓ i).mul contDiffOn_const
  · -- the output rows are multiplied by `c_{ℓ i}`
    have hc : ContDiff ℝ 1 fun c : (∀ ℓ, hid ℓ → ℝ) => c ℓ i := by fun_prop
    exact (hc.mul contDiff_const).contDiffOn

/-- Helper (the private `contDiff_det_iffr`): the determinant of a matrix whose entries are `C¹`
is `C¹`. -/
private theorem contDiff_det_ift {m X : Type*} [Fintype m] [DecidableEq m] [NormedAddCommGroup X]
    [NormedSpace ℝ X] {g : X → Matrix m m ℝ} (hg : ∀ a b, ContDiff ℝ 1 fun x => g x a b) :
    ContDiff ℝ 1 fun x => (g x).det := by
  simp only [Matrix.det_apply']
  exact ContDiff.sum fun τ _ => contDiff_const.mul (contDiff_prod fun i _ => hg (τ i) i)

/-- Helper (the private `contDiffOn_inv_entry_iffr`): the entries of the inverse of a matrix whose
entries are `C¹` are `C¹` where the matrix is invertible (`A⁻¹ = det(A)⁻¹ adj(A)`). -/
private theorem contDiffOn_inv_entry_ift {m X : Type*} [Fintype m] [DecidableEq m]
    [NormedAddCommGroup X] [NormedSpace ℝ X] {g : X → Matrix m m ℝ}
    (hg : ∀ a b, ContDiff ℝ 1 fun x => g x a b) {s : Set X} (hs : ∀ x ∈ s, IsUnit (g x))
    (a b : m) : ContDiffOn ℝ 1 (fun x => (g x)⁻¹ a b) s := by
  have h1 : (fun x => (g x)⁻¹ a b)
      = fun x => ((g x).det)⁻¹ * ((g x).updateRow b (Pi.single a 1)).det := by
    funext x
    rw [Matrix.inv_def, Matrix.smul_apply, Matrix.adjugate_apply, Ring.inverse_eq_inv, smul_eq_mul]
  rw [h1]
  have hdet : ContDiff ℝ 1 fun x => (g x).det := contDiff_det_ift hg
  -- the matrix of the adjugate entry: row `b` replaced by the unit row `a`
  have hadj : ContDiff ℝ 1 fun x => ((g x).updateRow b (Pi.single a 1)).det := by
    refine contDiff_det_ift fun i j => ?_
    rcases eq_or_ne i b with rfl | h
    · simp only [Matrix.updateRow_self]
      exact contDiff_const
    · simp only [Matrix.updateRow_ne h]
      exact hg i j
  exact (hdet.contDiffOn.inv fun x hx =>
    ((Matrix.isUnit_iff_isUnit_det _).1 (hs x hx)).ne_zero).mul hadj.contDiffOn

omit [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] [∀ ℓ, DecidableEq (dh ℓ)] in
/-- Helper (the private `headsMat_iffr`): the parameters `(θ.headsQK K).headsVO K'` written with
the matrices `K`, `K'` and, as separate arguments, their inverses `Ki`, `K'i`. -/
private noncomputable def headsMat_ift {χ : Matrix T d ℝ → Matrix T d ℝ}
    (θ : Params (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut)
    (K Ki K' K'i : ∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) :
    Params (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut where
  E := θ.E
  read ℓ := Matrix.of fun a p =>
    match p.2 with
    | Sum.inl k => ∑ k', θ.read ℓ a (p.1, Sum.inl k') * K ℓ p.1 k' k
    | Sum.inr (Sum.inl k) => ∑ k', θ.read ℓ a (p.1, Sum.inr (Sum.inl k')) * Ki ℓ p.1 k k'
    | Sum.inr (Sum.inr k) => ∑ k', θ.read ℓ a (p.1, Sum.inr (Sum.inr k')) * K' ℓ p.1 k' k
  write ℓ := Matrix.of fun (p : H ℓ × dh ℓ) b => ∑ k', K'i ℓ p.1 p.2 k' * θ.write ℓ (p.1, k') b
  D := θ.D

omit [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] [∀ ℓ, DecidableEq (dh ℓ)] in
/-- Helper (the private `headsFam_iffr`): the family of the changes of basis inside the heads, at
the pairs `n = (k, k')` of families of matrices, with the matrix inverses of `k`, `k'`. -/
private noncomputable def headsFam_ift {χ : Matrix T d ℝ → Matrix T d ℝ}
    (θ : Params (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut)
    (n : (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)) :
    Params (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut :=
  headsMat_ift θ n.1 (fun ℓ i => (n.1 ℓ i)⁻¹) n.2 (fun ℓ i => (n.2 ℓ i)⁻¹)

omit [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (the private `headsFam_coe_iffr`): at the invertible matrices of `K`, `K'`, the family
is `(θ.headsQK K).headsVO K'`. -/
private theorem headsFam_coe_ift {χ : Matrix T d ℝ → Matrix T d ℝ}
    (θ : Params (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut)
    (K K' : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ) :
    headsFam_ift θ (fun ℓ i => (K ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ),
      fun ℓ i => (K' ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)) = (θ.headsQK K).headsVO K' := by
  -- the matrix inverse of `K` is the matrix of `K⁻¹`
  simp only [headsFam_ift, ← Matrix.coe_units_inv]
  refine Params.ext' rfl (fun ℓ => ?_) (fun ℓ => rfl) rfl
  ext a p
  rcases p with ⟨i, k | k | k⟩ <;> rfl

omit [DecidableEq d] in
/-- Helper (the private `contDiffOn_headsFam_iffr`): the family of the changes of basis inside the
heads is `C¹` where the matrices are invertible. -/
private theorem contDiffOn_headsFam_ift {χ : Matrix T d ℝ → Matrix T d ℝ}
    (θ : Params (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut) :
    ContDiffOn ℝ 1 (headsFam_ift θ)
      {n | ∀ ℓ i, IsUnit (n.1 ℓ i) ∧ IsUnit (n.2 ℓ i)} := by
  refine contDiffOn_params_ift (fun i j => contDiffOn_const (c := θ.E i j)) (fun ℓ a p => ?_)
    (fun ℓ p b => ?_) (fun k j => contDiffOn_const (c := θ.D k j))
  · rcases p with ⟨i, k | k | k⟩
    · -- the query columns `W_Q k`
      have hk : ∀ k', ContDiff ℝ 1 fun n : (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)
          × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) => n.1 ℓ i k' k := fun k' => by fun_prop
      exact (ContDiff.sum fun k' _ => contDiff_const.mul (hk k')).contDiffOn
    · -- the key columns `W_K (k⁻¹)ᵀ`
      exact ContDiffOn.sum fun k' _ => contDiffOn_const.mul
        (contDiffOn_inv_entry_ift (g := fun n : (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)
          × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) => n.1 ℓ i) (fun _ _ => by fun_prop)
          (fun n (hn : ∀ ℓ i, IsUnit (n.1 ℓ i) ∧ IsUnit (n.2 ℓ i)) => (hn ℓ i).1) k k')
    · -- the value columns `W_V k'`
      have hk : ∀ k', ContDiff ℝ 1 fun n : (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)
          × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) => n.2 ℓ i k' k := fun k' => by fun_prop
      exact (ContDiff.sum fun k' _ => contDiff_const.mul (hk k')).contDiffOn
  · -- the output rows `k'⁻¹ W_O`
    rcases p with ⟨i, k⟩
    exact ContDiffOn.sum fun k' _ => ContDiffOn.mul
      (contDiffOn_inv_entry_ift (g := fun n : (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)
        × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) => n.2 ℓ i) (fun _ _ => by fun_prop)
        (fun n (hn : ∀ ℓ i, IsUnit (n.1 ℓ i) ∧ IsUnit (n.2 ℓ i)) => (hn ℓ i).2) k k')
      contDiffOn_const

/-! #### Helpers: generic parameters -/

omit [Fintype T] [DecidableEq d] in
/-- Helper (the private `analyticOnNhd_det_iffr`): the determinant of a square matrix that depends
linearly on the parameters is an analytic function of the parameters. -/
private theorem analyticOnNhd_det_ift {A : Arch T d L} {n : Type*} [Fintype n] [DecidableEq n]
    (Φ : Params A dIn dOut →ₗ[ℝ] Matrix n n ℝ) :
    AnalyticOnNhd ℝ (fun θ => (Φ θ).det) Set.univ := by
  simp only [Matrix.det_apply']
  exact Finset.analyticOnNhd_fun_sum _ fun σ _ => analyticOnNhd_const.mul
    (Finset.analyticOnNhd_fun_prod _ fun i _ =>
      analyticOnNhd_linear ((Matrix.entryLinearMap ℝ ℝ (σ i) i).comp Φ))

/-- Helper (the private `exists_submatrix_eq_one_iffr`): a matrix whose submatrix on the rows `r`
and the columns `c` (both injective) is the identity. -/
private theorem exists_submatrix_eq_one_ift {m p n : Type*} [DecidableEq n] {r : n → m}
    (hr : Function.Injective r) {c : n → p} (hc : Function.Injective c) :
    ∃ M : Matrix m p ℝ, M.submatrix r c = 1 := by
  classical
  refine ⟨Matrix.of fun a b => if ∃ x, r x = a ∧ c x = b then 1 else 0, ?_⟩
  ext x y
  simp [Matrix.one_apply, hr.eq_iff, hc.eq_iff]

omit [Fintype T] [DecidableEq d] in
/-- Helper (the private `ae_rank_read_cols_iffr`): at generic parameters, `n ≤ d` distinct columns
`c` of the read of block `ℓ` form a matrix of rank `n`. -/
private theorem ae_rank_read_cols_ift {A : Arch T d L} (μ : Measure (Params A dIn dOut))
    [μ.IsAddHaarMeasure] (ℓ : Fin L) {n : Type*} [Fintype n] [DecidableEq n] {c : n → A.r ℓ}
    (hc : Function.Injective c) (hn : Fintype.card n ≤ Fintype.card d) :
    ∀ᵐ θ ∂μ, ((θ.read ℓ).submatrix id c).rank = Fintype.card n := by
  -- `n` rows `ρ`, and the square submatrix of the read on the rows `ρ` and the columns `c`
  obtain ⟨ρ⟩ := Function.Embedding.nonempty_of_card_le hn
  obtain ⟨M, hM⟩ := exists_submatrix_eq_one_ift ρ.injective hc
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
  filter_upwards [ae_ne_zero_of_analytic μ (analyticOnNhd_det_ift Φ) hne] with θ hθ
  -- an invertible `n × n` submatrix gives rank `≥ n`, and the rank is at most the width `n`
  have h1 : (((θ.read ℓ).submatrix id c).submatrix ρ id).rank = Fintype.card n :=
    Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hθ))
  have h2 : (((θ.read ℓ).submatrix id c).submatrix ρ id).rank
      ≤ ((θ.read ℓ).submatrix id c).rank :=
    Matrix.rank_submatrix_le _ ρ id
  have h3 := Matrix.rank_le_card_width ((θ.read ℓ).submatrix id c)
  omega

omit [DecidableEq d] in
/-- Helper (the private `ae_rank_QV_sum_iffr`): at generic parameters the query matrix and the
value matrix of every head of the first part of a sum have rank `d_h`, when `d_h ≤ d`. -/
private theorem ae_rank_QV_sum_ift {B : Arch T d L} {χ : Matrix T d ℝ → Matrix T d ℝ}
    (μ : Measure (Params ((Arch.attention (T := T) (d := d) sees χ H dh).sum B) dIn dOut))
    [μ.IsAddHaarMeasure] (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) :
    ∀ᵐ θ ∂μ, (∀ ℓ (i : H ℓ),
        ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k)).rank
          = Fintype.card (dh ℓ)) ∧
      ∀ ℓ (i : H ℓ),
        ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))).rank
          = Fintype.card (dh ℓ) := by
  classical
  -- finitely many conditions, two for each head of each block; the read of the first part is
  -- made of columns of the read of the sum
  refine (ae_all_iff.2 fun ℓ => ae_all_iff.2 fun i => ?_).and
    (ae_all_iff.2 fun ℓ => ae_all_iff.2 fun i => ?_)
  · exact ae_rank_read_cols_ift μ ℓ (c := fun k : dh ℓ => Sum.inl (i, Sum.inl k))
      (fun _ _ h => Sum.inl_injective (Prod.mk.inj (Sum.inl_injective h)).2) (hdh ℓ)
  · exact ae_rank_read_cols_ift μ ℓ (c := fun k : dh ℓ => Sum.inl (i, Sum.inr (Sum.inr k)))
      (fun _ _ h => Sum.inr_injective (Sum.inr_injective (Prod.mk.inj (Sum.inl_injective h)).2))
      (hdh ℓ)

omit [Fintype T] [DecidableEq d] in
/-- Helper (the private `ae_value_ne_zero_sum_iffr`): at generic parameters no value column of
the gated part of a read vanishes. -/
private theorem ae_value_ne_zero_sum_ift [Nonempty d] {A : Arch T d L}
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

/-! #### The four equivalences -/

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
  -- the write of block `ℓ` has `H_ℓ d_{h,ℓ} + d_hidden,ℓ ≥ d` rows
  have hw : ∀ ℓ, Fintype.card d ≤ Fintype.card
      ((Arch.attentionMlp (T := T) (d := d) sees σ id H dh hid).w ℓ) := fun ℓ => by
    show Fintype.card d ≤ Fintype.card ((H ℓ × dh ℓ) ⊕ hid ℓ)
    rw [Fintype.card_sum, Fintype.card_prod]
    exact hW ℓ
  constructor
  · -- from the equality condition: Proposition 4.5 at every `θ` where `E` and the writes have
    -- rank `d` and the query and value matrices of every head have rank `d_h`, with no condition
    -- on `G`, `K`, `K'` (the neighbourhoods `Set.univ`)
    intro h
    filter_upwards [h, ae_rank_E_write μ hdIn hw, ae_rank_QV_sum_ift μ hdh] with θ hfd hθ hQV
    obtain ⟨U, hU, hUV⟩ := exists_cob_heads_of_eval_eq_skipless_attentionMlp hσ θ hθ.1 hθ.2
      hQV.1 hQV.2 hfd Set.univ Filter.univ_mem Set.univ Filter.univ_mem
    refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
    obtain ⟨G, K, K', -, -, -, hθ'⟩ := hUV θ' hθ' heq
    exact ⟨K, K', G, hθ'⟩
  · -- to the equality condition: the lower bound `P ≤ fd + (L + 1) d² + 2 ∑ H d_h²` from local
    -- identifiability, with the changes of basis inside the heads of the attention part at pairs
    -- of families of invertible matrices, and the upper bound of Theorem 4.2
    intro h
    have hlow := ae_finrank_le_funDim_add_of_ae_locally_cob
      (Arch.attentionMlp (T := T) (d := d) sees σ id H dh hid) 0
      (fun ℓ => analyticOnNhd_f_sum (analyticOnNhd_f_attention sees id H dh ℓ)
        (analyticOnNhd_f_mlp hσ ℓ)) analyticOnNhd_id μ
      (fun θ n => Params.sumOf (headsFam_ift θ.sumFst n) θ.sumSnd)
      {n | ∀ ℓ i, IsUnit (n.1 ℓ i) ∧ IsUnit (n.2 ℓ i)}
      (fun θ => contDiffOn_sumOf_ift (contDiffOn_headsFam_ift θ.sumFst) contDiffOn_const) (by
        filter_upwards [h] with θ ⟨U, hU, hUV⟩
        refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
        obtain ⟨K, K', G, hG⟩ := hUV θ' hθ' heq
        refine ⟨(fun ℓ i => (K ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ),
          fun ℓ i => (K' ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)),
          fun ℓ i => ⟨(K ℓ i).isUnit, (K' ℓ i).isUnit⟩, G, ?_⟩
        rw [headsFam_coe_ift]
        exact hG)
    have hup := ae_funDim_add_le_skipless_attentionMlp μ hdIn hdh hW
    filter_upwards [hlow, hup] with θ h1 h2
    rw [Module.finrank_prod, finrank_headFun_ift] at h1
    generalize ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2 = s at h1 h2 ⊢
    generalize (L + 1) * Fintype.card d ^ 2 = a at h1 h2 ⊢
    omega

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
  -- the write of block `ℓ` has `H_ℓ d_{h,ℓ} + d_hidden,ℓ ≥ d` rows
  have hw : ∀ ℓ, Fintype.card d ≤ Fintype.card
      ((Arch.attentionMlp (T := T) (d := d) sees σ (rmsNorm ε) H dh hid).w ℓ) := fun ℓ => by
    show Fintype.card d ≤ Fintype.card ((H ℓ × dh ℓ) ⊕ hid ℓ)
    rw [Fintype.card_sum, Fintype.card_prod]
    exact hW ℓ
  constructor
  · -- from the equality condition: Proposition 4.5 at every `θ` where `E` and the writes have
    -- rank `d` and the query and value matrices of every head have rank `d_h`, with no condition
    -- on `Q`, `K`, `K'` (the neighbourhoods `Set.univ`)
    intro h
    filter_upwards [h, ae_rank_E_write μ hdIn hw, ae_rank_QV_sum_ift μ hdh] with θ hfd hθ hQV
    obtain ⟨U, hU, hUV⟩ := exists_cob_heads_of_eval_eq_skipless_attentionMlp_rmsNorm hε hσ θ
      hθ.1 hθ.2 hQV.1 hQV.2 hfd Set.univ Filter.univ_mem Set.univ Filter.univ_mem
    refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
    obtain ⟨Q, K, K', hQ, -, -, -, hθ'⟩ := hUV θ' hθ' heq
    exact ⟨K, K', Q, hQ, hθ'⟩
  · -- to the equality condition: the lower bound `P ≤ fd + (L + 1) d(d-1)/2 + 2 ∑ H d_h²` from
    -- local identifiability, with the changes of basis inside the heads of the attention part at
    -- pairs of families of invertible matrices, and the upper bound of Theorem 4.2
    intro h
    have hlow := ae_finrank_le_funDim_add_of_ae_locally_cob_orthogonal
      (Arch.attentionMlp (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) 0
      (fun ℓ => analyticOnNhd_f_sum (analyticOnNhd_f_attention sees (rmsNorm ε) H dh ℓ)
        (analyticOnNhd_f_mlp hσ ℓ)) (analyticOnNhd_rmsNorm hε) μ
      (fun θ n => Params.sumOf (headsFam_ift θ.sumFst n) θ.sumSnd)
      {n | ∀ ℓ i, IsUnit (n.1 ℓ i) ∧ IsUnit (n.2 ℓ i)}
      (fun θ => contDiffOn_sumOf_ift (contDiffOn_headsFam_ift θ.sumFst) contDiffOn_const) (by
        filter_upwards [h] with θ ⟨U, hU, hUV⟩
        refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
        obtain ⟨K, K', Q, hQ, hQθ⟩ := hUV θ' hθ' heq
        refine ⟨(fun ℓ i => (K ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ),
          fun ℓ i => (K' ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)),
          fun ℓ i => ⟨(K ℓ i).isUnit, (K' ℓ i).isUnit⟩, Q, hQ, ?_⟩
        rw [headsFam_coe_ift]
        exact hQθ)
    have hup := ae_funDim_add_le_skipless_attentionMlp_rmsNorm ε μ hdIn hdh hW
    filter_upwards [hlow, hup] with θ h1 h2
    rw [Module.finrank_prod, finrank_headFun_ift] at h1
    generalize ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2 = s at h1 h2 ⊢
    generalize (L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2) = a at h1 h2 ⊢
    omega

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
  -- the write of block `ℓ` has `H_ℓ d_{h,ℓ} + d_hidden,ℓ ≥ d` rows
  have hw : ∀ ℓ, Fintype.card d ≤ Fintype.card
      ((Arch.attentionGated (T := T) (d := d) sees σ id H dh hid).w ℓ) := fun ℓ => by
    show Fintype.card d ≤ Fintype.card ((H ℓ × dh ℓ) ⊕ hid ℓ)
    rw [Fintype.card_sum, Fintype.card_prod]
    exact hW ℓ
  constructor
  · -- from the equality condition: Proposition 4.5 at every `θ` where `E` and the writes have
    -- rank `d`, the query and value matrices of every head have rank `d_h` and no value column of
    -- a gated unit vanishes, with no condition on `G`, `K`, `K'`, `c` (the neighbourhoods
    -- `Set.univ`)
    intro h
    filter_upwards [h, ae_rank_E_write μ hdIn hw, ae_rank_QV_sum_ift μ hdh,
      ae_value_ne_zero_sum_ift μ] with θ hfd hθ hQV hv
    obtain ⟨U, hU, hUV⟩ := exists_cob_heads_of_eval_eq_skipless_attentionGated hσ θ hθ.1 hθ.2
      hQV.1 hQV.2 hv hfd Set.univ Filter.univ_mem Set.univ Filter.univ_mem Set.univ
      Filter.univ_mem
    refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
    obtain ⟨G, K, K', c, -, -, -, -, hc0, hθ'⟩ := hUV θ' hθ' heq
    exact ⟨K, K', c, fun ℓ i => (hc0 ℓ i).ne', G, hθ'⟩
  · -- to the equality condition: the lower bound `P ≤ fd + (L + 1) d² + 2 ∑ H d_h² + s` from
    -- local identifiability, with the changes of basis inside the heads at pairs of families of
    -- invertible matrices and the rescalings by factors without zero, and the upper bound of
    -- Theorem 4.2
    intro h
    have hlow := ae_finrank_le_funDim_add_of_ae_locally_cob
      (Arch.attentionGated (T := T) (d := d) sees σ id H dh hid) 0
      (fun ℓ => analyticOnNhd_f_sum (analyticOnNhd_f_attention sees id H dh ℓ)
        (analyticOnNhd_f_gated hσ ℓ)) analyticOnNhd_id μ
      (N := ((∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ))
        × (∀ ℓ, hid ℓ → ℝ))
      (fun θ n => Params.sumOf (headsFam_ift θ.sumFst n.1) (θ.sumSnd.rescale n.2))
      {n | (∀ ℓ i, IsUnit (n.1.1 ℓ i) ∧ IsUnit (n.1.2 ℓ i)) ∧ ∀ ℓ i, n.2 ℓ i ≠ 0}
      (fun θ => contDiffOn_sumOf_ift
        ((contDiffOn_headsFam_ift θ.sumFst).comp contDiffOn_fst fun _ hn => hn.1)
        ((contDiffOn_rescale_ift θ.sumSnd).comp contDiffOn_snd fun _ hn => hn.2)) (by
        filter_upwards [h] with θ ⟨U, hU, hUV⟩
        refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
        obtain ⟨K, K', c, hc, G, hG⟩ := hUV θ' hθ' heq
        refine ⟨((fun ℓ i => (K ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ),
          fun ℓ i => (K' ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)), c),
          ⟨fun ℓ i => ⟨(K ℓ i).isUnit, (K' ℓ i).isUnit⟩, hc⟩, G, ?_⟩
        rw [headsFam_coe_ift]
        exact hG)
    have hup := ae_funDim_add_le_skipless_attentionGated μ hdIn hdh hW
    filter_upwards [hlow, hup] with θ h1 h2
    rw [Module.finrank_prod, Module.finrank_prod, finrank_headFun_ift, finrank_hidFun_ift] at h1
    generalize ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2 = s at h1 h2 ⊢
    generalize ∑ ℓ, Fintype.card (hid ℓ) = t at h1 h2 ⊢
    generalize (L + 1) * Fintype.card d ^ 2 = a at h1 h2 ⊢
    omega

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
  -- the write of block `ℓ` has `H_ℓ d_{h,ℓ} + d_hidden,ℓ ≥ d` rows
  have hw : ∀ ℓ, Fintype.card d ≤ Fintype.card
      ((Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm ε) H dh hid).w ℓ) := fun ℓ => by
    show Fintype.card d ≤ Fintype.card ((H ℓ × dh ℓ) ⊕ hid ℓ)
    rw [Fintype.card_sum, Fintype.card_prod]
    exact hW ℓ
  constructor
  · -- from the equality condition: Proposition 4.5 at every `θ` where `E` and the writes have
    -- rank `d`, the query and value matrices of every head have rank `d_h` and no value column of
    -- a gated unit vanishes, with no condition on `Q`, `K`, `K'`, `c` (the neighbourhoods
    -- `Set.univ`)
    intro h
    filter_upwards [h, ae_rank_E_write μ hdIn hw, ae_rank_QV_sum_ift μ hdh,
      ae_value_ne_zero_sum_ift μ] with θ hfd hθ hQV hv
    obtain ⟨U, hU, hUV⟩ := exists_cob_heads_of_eval_eq_skipless_attentionGated_rmsNorm hε hσ θ
      hθ.1 hθ.2 hQV.1 hQV.2 hv hfd Set.univ Filter.univ_mem Set.univ Filter.univ_mem Set.univ
      Filter.univ_mem
    refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
    obtain ⟨Q, K, K', c, hQ, -, -, -, -, hc0, hθ'⟩ := hUV θ' hθ' heq
    exact ⟨K, K', c, fun ℓ i => (hc0 ℓ i).ne', Q, hQ, hθ'⟩
  · -- to the equality condition: the lower bound `P ≤ fd + (L + 1) d(d-1)/2 + 2 ∑ H d_h² + s`
    -- from local identifiability, with the changes of basis inside the heads at pairs of families
    -- of invertible matrices and the rescalings by factors without zero, and the upper bound of
    -- Theorem 4.2
    intro h
    have hlow := ae_finrank_le_funDim_add_of_ae_locally_cob_orthogonal
      (Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) 0
      (fun ℓ => analyticOnNhd_f_sum (analyticOnNhd_f_attention sees (rmsNorm ε) H dh ℓ)
        (analyticOnNhd_f_gated hσ ℓ)) (analyticOnNhd_rmsNorm hε) μ
      (N := ((∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ))
        × (∀ ℓ, hid ℓ → ℝ))
      (fun θ n => Params.sumOf (headsFam_ift θ.sumFst n.1) (θ.sumSnd.rescale n.2))
      {n | (∀ ℓ i, IsUnit (n.1.1 ℓ i) ∧ IsUnit (n.1.2 ℓ i)) ∧ ∀ ℓ i, n.2 ℓ i ≠ 0}
      (fun θ => contDiffOn_sumOf_ift
        ((contDiffOn_headsFam_ift θ.sumFst).comp contDiffOn_fst fun _ hn => hn.1)
        ((contDiffOn_rescale_ift θ.sumSnd).comp contDiffOn_snd fun _ hn => hn.2)) (by
        filter_upwards [h] with θ ⟨U, hU, hUV⟩
        refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
        obtain ⟨K, K', c, hc, Q, hQ, hQθ⟩ := hUV θ' hθ' heq
        refine ⟨((fun ℓ i => (K ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ),
          fun ℓ i => (K' ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)), c),
          ⟨fun ℓ i => ⟨(K ℓ i).isUnit, (K' ℓ i).isUnit⟩, hc⟩, Q, hQ, ?_⟩
        rw [headsFam_coe_ift]
        exact hQθ)
    have hup := ae_funDim_add_le_skipless_attentionGated_rmsNorm ε μ hdIn hdh hW
    filter_upwards [hlow, hup] with θ h1 h2
    rw [Module.finrank_prod, Module.finrank_prod, finrank_headFun_ift, finrank_hidFun_ift] at h1
    generalize ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2 = s at h1 h2 ⊢
    generalize ∑ ℓ, Fintype.card (hid ℓ) = t at h1 h2 ⊢
    generalize (L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2) = a at h1 h2 ⊢
    omega

end Skips
