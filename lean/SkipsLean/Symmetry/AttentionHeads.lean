import SkipsLean.Network.Attention
import SkipsLean.Dimension.UpperBound
import SkipsLean.Dimension.Functional

/-!
# The symmetries inside the heads of an attention block

Paper (dimension paper), Appendix B, "The symmetries inside the blocks": "attention, head `i`:
`(W_{Q,i}, W_{K,i}) ↦ (W_{Q,i} K, W_{K,i} K^{-⊤})`, `K ∈ GL(d_h)`;
`(W_{V,i}, W_{O,i}) ↦ (W_{V,i} K', K'^{-1} W_{O,i})`, `K' ∈ GL(d_h)`. […] the changes of basis
inside a head are those of Elhage et al. (2021) and Theus et al. (2025) […] So a block has
[…] `s = 2 H d_h²` for attention". The proof of Lemma B.1 (Locally free action): "In an attention
block, the changes of basis inside the heads map `W_{Q,i} ↦ W_{Q,i} K_i` and
`W_{V,i} ↦ W_{V,i} K'_i`. At generic parameters these matrices have full column rank, as
`d_h ≤ d_model`, so `K_i = K'_i = I`. The write, which stacks the `W_{O,i}`, then becomes
`W_O G_ℓ = W_O` and has rank `d_model`, as `H d_h ≥ d_model`, so `G_ℓ = I`." The proof of
Theorem C.1 for attention blocks, Step 1, has the directions: "`η_{Q,i} = W_{Q,i} Γ_i`,
`η_{K,i} = −W_{K,i} Γ_i^⊤`, `η_{V,i} = W_{V,i} Γ'_i`, `η_{O,i} = −Γ'_i W_{O,i}`" (besides the
changes of basis of the hidden states).

Stated here for networks of attention blocks in the frame of `Arch.attention`
(`Network/Attention.lean`), any depth, any mask, any map `χ`, any stream matrices (with or
without skips):

* `Params.headsQK θ K`, `Params.headsVO θ K'`: the two changes of basis in every head of every
  block, and that they preserve the function.
* `headDirQK θ Γ`, `headDirVO θ Γ'`: their directions at the identity, and that these are flat.
* Lemma B.1 for attention blocks in infinitesimal form: if `E` and the writes have rank `d` and
  the query and value matrices of every head have rank `d_h`, the directions of the changes of
  basis of the hidden states and of the two changes of basis inside the heads are independent.
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {sees : T → T → Prop} [DecidableRel sees] {χ : Matrix T d ℝ → Matrix T d ℝ}
variable {H dh : Fin L → Type} [∀ ℓ, Fintype (H ℓ)] [∀ ℓ, Fintype (dh ℓ)]
  [∀ ℓ, DecidableEq (dh ℓ)]

/-- **The change of basis between the queries and the keys of every head:**
`(W_{Q,i}, W_{K,i}) ↦ (W_{Q,i} K_i, W_{K,i} K_i^{-⊤})` for head `i` of block `ℓ`, with
`K ℓ i ∈ GL(d_h)`. -/
noncomputable def Params.headsQK (θ : Params (Arch.attention sees χ H dh) dIn dOut)
    (K : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ) : Params (Arch.attention sees χ H dh) dIn dOut where
  E := θ.E
  read ℓ := Matrix.of fun a p =>
    match p.2 with
    | Sum.inl k => ∑ k', θ.read ℓ a (p.1, Sum.inl k') * (K ℓ p.1 : Matrix (dh ℓ) (dh ℓ) ℝ) k' k
    | Sum.inr (Sum.inl k) =>
      ∑ k', θ.read ℓ a (p.1, Sum.inr (Sum.inl k'))
        * (((K ℓ p.1)⁻¹ : GL (dh ℓ) ℝ) : Matrix (dh ℓ) (dh ℓ) ℝ) k k'
    | Sum.inr (Sum.inr k) => θ.read ℓ a (p.1, Sum.inr (Sum.inr k))
  write := θ.write
  D := θ.D

/-- **The change of basis between the values and the outputs of every head:**
`(W_{V,i}, W_{O,i}) ↦ (W_{V,i} K'_i, K'_i^{-1} W_{O,i})` for head `i` of block `ℓ`. -/
noncomputable def Params.headsVO (θ : Params (Arch.attention sees χ H dh) dIn dOut)
    (K : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ) : Params (Arch.attention sees χ H dh) dIn dOut where
  E := θ.E
  read ℓ := Matrix.of fun a p =>
    match p.2 with
    | Sum.inl k => θ.read ℓ a (p.1, Sum.inl k)
    | Sum.inr (Sum.inl k) => θ.read ℓ a (p.1, Sum.inr (Sum.inl k))
    | Sum.inr (Sum.inr k) =>
      ∑ k', θ.read ℓ a (p.1, Sum.inr (Sum.inr k')) * (K ℓ p.1 : Matrix (dh ℓ) (dh ℓ) ℝ) k' k
  write ℓ := Matrix.of fun (p : H ℓ × dh ℓ) b =>
    ∑ k', (((K ℓ p.1)⁻¹ : GL (dh ℓ) ℝ) : Matrix (dh ℓ) (dh ℓ) ℝ) p.2 k' * θ.write ℓ (p.1, k') b
  D := θ.D

/-- **The direction of the changes of basis between queries and keys:** `η_{Q,i} = W_{Q,i} Γ_i`,
`η_{K,i} = −W_{K,i} Γ_i^⊤`, and `0` elsewhere. -/
def headDirQK (θ : Params (Arch.attention sees χ H dh) dIn dOut)
    (Γ : ∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) : Params (Arch.attention sees χ H dh) dIn dOut where
  E := 0
  read ℓ := Matrix.of fun a p =>
    match p.2 with
    | Sum.inl k => ∑ k', θ.read ℓ a (p.1, Sum.inl k') * Γ ℓ p.1 k' k
    | Sum.inr (Sum.inl k) => -∑ k', θ.read ℓ a (p.1, Sum.inr (Sum.inl k')) * Γ ℓ p.1 k k'
    | Sum.inr (Sum.inr _) => 0
  write _ := 0
  D := 0

/-- **The direction of the changes of basis between values and outputs:**
`η_{V,i} = W_{V,i} Γ'_i`, `η_{O,i} = −Γ'_i W_{O,i}`, and `0` elsewhere. -/
def headDirVO (θ : Params (Arch.attention sees χ H dh) dIn dOut)
    (Γ : ∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) : Params (Arch.attention sees χ H dh) dIn dOut where
  E := 0
  read ℓ := Matrix.of fun a p =>
    match p.2 with
    | Sum.inl _ => 0
    | Sum.inr (Sum.inl _) => 0
    | Sum.inr (Sum.inr k) => ∑ k', θ.read ℓ a (p.1, Sum.inr (Sum.inr k')) * Γ ℓ p.1 k' k
  write ℓ := Matrix.of fun (p : H ℓ × dh ℓ) b => -∑ k', Γ ℓ p.1 p.2 k' * θ.write ℓ (p.1, k') b
  D := 0

variable (θ : Params (Arch.attention sees χ H dh) dIn dOut)

omit [Fintype T] [DecidableEq d] [Fintype dOut] in
/-- Helper: two parameters with the same `E`, the same `D` and the same output of every block on
every hidden state compute the same function (induction along the hidden states). -/
private theorem eval_eq_of_blocks_ath {A : Arch T d L} (θ₁ θ₂ : Params A dIn dOut)
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

omit [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the query matrices of `θ.headsQK K` are `W_{Q,i} K_i`. -/
private theorem headsQK_query_ath (K : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ) (ℓ : Fin L) (i : H ℓ) :
    ((θ.headsQK K).read ℓ).submatrix id (fun k : dh ℓ => (i, Sum.inl k))
      = (θ.read ℓ).submatrix id (fun k : dh ℓ => (i, Sum.inl k))
        * (K ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ) := by
  ext a k
  rfl

omit [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the key matrices of `θ.headsQK K` are `W_{K,i} K_i^{-⊤}`. -/
private theorem headsQK_key_ath (K : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ) (ℓ : Fin L) (i : H ℓ) :
    ((θ.headsQK K).read ℓ).submatrix id (fun k : dh ℓ => (i, Sum.inr (Sum.inl k)))
      = (θ.read ℓ).submatrix id (fun k : dh ℓ => (i, Sum.inr (Sum.inl k)))
        * (((K ℓ i)⁻¹ : GL (dh ℓ) ℝ) : Matrix (dh ℓ) (dh ℓ) ℝ)ᵀ := by
  ext a k
  rfl

omit [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the value matrices of `θ.headsVO K` are `W_{V,i} K'_i`. -/
private theorem headsVO_value_ath (K : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ) (ℓ : Fin L) (i : H ℓ) :
    ((θ.headsVO K).read ℓ).submatrix id (fun k : dh ℓ => (i, Sum.inr (Sum.inr k)))
      = (θ.read ℓ).submatrix id (fun k : dh ℓ => (i, Sum.inr (Sum.inr k)))
        * (K ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ) := by
  ext a k
  rfl

omit [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the output matrices of `θ.headsVO K` are `K'_i^{-1} W_{O,i}`. -/
private theorem headsVO_output_ath (K : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ) (ℓ : Fin L) (i : H ℓ) :
    ((θ.headsVO K).write ℓ).submatrix (fun k : dh ℓ => (i, k)) id
      = (((K ℓ i)⁻¹ : GL (dh ℓ) ℝ) : Matrix (dh ℓ) (dh ℓ) ℝ)
        * (θ.write ℓ).submatrix (fun k : dh ℓ => (i, k)) id := by
  ext k b
  rfl

omit [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the change of basis between queries and keys leaves the output of every block
unchanged: `W_{Q,i} K (W_{K,i} K^{-⊤})ᵀ = W_{Q,i} K K^{-1} W_{K,i}ᵀ = W_{Q,i} W_{K,i}ᵀ`. -/
private theorem block_headsQK_ath (K : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ) (ℓ : Fin L) (h : Matrix T d ℝ) :
    (Arch.attention sees χ H dh).f ℓ (h * (θ.headsQK K).read ℓ) * (θ.headsQK K).write ℓ
      = (Arch.attention sees χ H dh).f ℓ (h * θ.read ℓ) * θ.write ℓ := by
  rw [f_attention_mul, f_attention_mul]
  unfold attentionBlock
  congr 1
  funext i
  dsimp only
  rw [headsQK_query_ath, headsQK_key_ath, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.mul_assoc, ← Matrix.mul_assoc (K ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ), Units.mul_inv,
    Matrix.one_mul]

omit [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the change of basis between values and outputs leaves the output of every block
unchanged: `W_{V,i} K' K'^{-1} W_{O,i} = W_{V,i} W_{O,i}`. -/
private theorem block_headsVO_ath (K : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ) (ℓ : Fin L) (h : Matrix T d ℝ) :
    (Arch.attention sees χ H dh).f ℓ (h * (θ.headsVO K).read ℓ) * (θ.headsVO K).write ℓ
      = (Arch.attention sees χ H dh).f ℓ (h * θ.read ℓ) * θ.write ℓ := by
  rw [f_attention_mul, f_attention_mul]
  unfold attentionBlock
  congr 1
  funext i
  dsimp only
  rw [headsVO_value_ath, headsVO_output_ath, Matrix.mul_assoc,
    ← Matrix.mul_assoc (K ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ), Units.mul_inv, Matrix.one_mul]

/-- **The changes of basis between queries and keys preserve the function** (Appendix B), for
every mask, every `χ` and all stream matrices. -/
theorem eval_headsQK (K : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ) (S : Fin L → Matrix d d ℝ)
    (x : Matrix T dIn ℝ) :
    eval (Arch.attention sees χ H dh) S (θ.headsQK K) x
      = eval (Arch.attention sees χ H dh) S θ x := by
  -- `E` and `D` do not move, and every block computes the same map
  exact eval_eq_of_blocks_ath θ (θ.headsQK K) rfl rfl (block_headsQK_ath θ K) S x

/-- **The changes of basis between values and outputs preserve the function** (Appendix B). -/
theorem eval_headsVO (K : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ) (S : Fin L → Matrix d d ℝ)
    (x : Matrix T dIn ℝ) :
    eval (Arch.attention sees χ H dh) S (θ.headsVO K) x
      = eval (Arch.attention sees χ H dh) S θ x := by
  -- `E` and `D` do not move, and every block computes the same map
  exact eval_eq_of_blocks_ath θ (θ.headsVO K) rfl rfl (block_headsVO_ath θ K) S x

/-- Helper (the private `expGL` of `Dimension/UpperBound.lean`): the change of basis `exp (τ X)`,
an element of `GL n ℝ` with inverse `exp (-τ X)`. -/
private noncomputable def expGL_ath {n : Type*} [Fintype n] [DecidableEq n] (X : Matrix n n ℝ)
    (τ : ℝ) : GL n ℝ where
  val := NormedSpace.exp (τ • X)
  inv := NormedSpace.exp (τ • (-X))
  val_inv := by
    rw [← Matrix.exp_add_of_commute _ _ (((Commute.refl X).neg_right.smul_left τ).smul_right τ),
      smul_neg, add_neg_cancel, NormedSpace.exp_zero]
  inv_val := by
    rw [← Matrix.exp_add_of_commute _ _ (((Commute.refl X).neg_left.smul_left τ).smul_right τ),
      smul_neg, neg_add_cancel, NormedSpace.exp_zero]

/-- Helper: at `τ = 0` the change of basis `exp (τ X)` is the identity. -/
private theorem expGL_zero_ath {n : Type*} [Fintype n] [DecidableEq n] (X : Matrix n n ℝ) :
    expGL_ath X 0 = 1 :=
  Units.ext (by simp [expGL_ath])

/-- Helper: the entry `(a, b)` of `exp (τ X)` has derivative `X a b` at `τ = 0`. The derivative
only sees the topology, so it may be computed with the operator norm, under which matrices form a
Banach algebra: there the derivative of `exp (τ X)` is `exp (τ X) X`, which is `X` at `τ = 0`. -/
private theorem hasDerivAt_exp_entry_ath {n : Type*} [Fintype n] [DecidableEq n]
    (X : Matrix n n ℝ) (a b : n) :
    HasDerivAt (fun τ : ℝ => NormedSpace.exp (τ • X) a b) (X a b) 0 := by
  have h := open scoped Matrix.Norms.Operator in hasDerivAt_exp_smul_const (𝕂 := ℝ) X (0 : ℝ)
  rw [zero_smul, NormedSpace.exp_zero, one_mul] at h
  have h' : HasDerivAt (fun τ : ℝ => NormedSpace.exp (τ • X)) X 0 := h
  -- entry by entry
  exact hasDerivAt_pi.1 (hasDerivAt_pi.1 h' a) b

/-- Helper: `τ ↦ ∑_{k'} c_{k'} exp(τ X)_{k' k}` has derivative `∑_{k'} c_{k'} X_{k' k}` at `0`. -/
private theorem hasDerivAt_sum_mul_expGL_ath {n : Type*} [Fintype n] [DecidableEq n]
    (X : Matrix n n ℝ) (c : n → ℝ) (k : n) :
    HasDerivAt (fun τ => ∑ k', c k' * (expGL_ath X τ : Matrix n n ℝ) k' k)
      (∑ k', c k' * X k' k) 0 :=
  HasDerivAt.fun_sum fun k' _ => (hasDerivAt_exp_entry_ath X k' k).const_mul (c k')

/-- Helper: `τ ↦ ∑_{k'} c_{k'} (exp(τ X)⁻¹)_{k k'}` has derivative `-∑_{k'} c_{k'} X_{k k'}` at
`0`, since `exp(τ X)⁻¹ = exp(-τ X)`. -/
private theorem hasDerivAt_sum_mul_expGL_inv_ath {n : Type*} [Fintype n] [DecidableEq n]
    (X : Matrix n n ℝ) (c : n → ℝ) (k : n) :
    HasDerivAt (fun τ => ∑ k', c k' * (((expGL_ath X τ)⁻¹ : GL n ℝ) : Matrix n n ℝ) k k')
      (-∑ k', c k' * X k k') 0 := by
  have h := HasDerivAt.fun_sum (u := Finset.univ) fun k' _ =>
    (hasDerivAt_exp_entry_ath (-X) k k').const_mul (c k')
  refine h.congr_deriv ?_
  simp only [Matrix.neg_apply, mul_neg, Finset.sum_neg_distrib]

/-- Helper: `τ ↦ ∑_{k'} (exp(τ X)⁻¹)_{k k'} c_{k'}` has derivative `-∑_{k'} X_{k k'} c_{k'}` at
`0`. -/
private theorem hasDerivAt_sum_expGL_inv_mul_ath {n : Type*} [Fintype n] [DecidableEq n]
    (X : Matrix n n ℝ) (c : n → ℝ) (k : n) :
    HasDerivAt (fun τ => ∑ k', (((expGL_ath X τ)⁻¹ : GL n ℝ) : Matrix n n ℝ) k k' * c k')
      (-∑ k', X k k' * c k') 0 := by
  have h := HasDerivAt.fun_sum (u := Finset.univ) fun k' _ =>
    (hasDerivAt_exp_entry_ath (-X) k k').mul_const (c k')
  refine h.congr_deriv ?_
  simp only [Matrix.neg_apply, neg_mul, Finset.sum_neg_distrib]

omit [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the curve `τ ↦ θ.headsQK (exp (τ Γ))` passes through `θ` at `τ = 0`. -/
private theorem headsQK_expGL_zero_ath (Γ : ∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) :
    θ.headsQK (fun ℓ i => expGL_ath (Γ ℓ i) 0) = θ := by
  simp only [expGL_zero_ath]
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
/-- Helper: the curve `τ ↦ θ.headsVO (exp (τ Γ))` passes through `θ` at `τ = 0`. -/
private theorem headsVO_expGL_zero_ath (Γ : ∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) :
    θ.headsVO (fun ℓ i => expGL_ath (Γ ℓ i) 0) = θ := by
  simp only [expGL_zero_ath]
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
/-- Helper: the curve `τ ↦ θ.headsQK (exp (τ Γ))` has velocity `headDirQK θ Γ` at `τ = 0`. The
derivative is taken entry by entry, through the linear equivalence of the parameters with the
tuples of their components. -/
private theorem hasDerivAt_headsQK_ath (Γ : ∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) :
    HasDerivAt (fun τ : ℝ => θ.headsQK fun ℓ i => expGL_ath (Γ ℓ i) τ) (headDirQK θ Γ) 0 := by
  have hprod : HasDerivAt
      (fun τ : ℝ => Params.linearEquivProd (θ.headsQK fun ℓ i => expGL_ath (Γ ℓ i) τ))
      (Params.linearEquivProd (headDirQK θ Γ)) 0 := by
    refine HasDerivAt.prodMk ?_ (HasDerivAt.prodMk ?_ (HasDerivAt.prodMk ?_ ?_))
    · -- the embedding does not move
      exact hasDerivAt_const (0 : ℝ) θ.E
    · -- the queries are `W_Q exp(τ Γ)`, the keys `W_K exp(-τ Γ)ᵀ`, the values do not move
      refine hasDerivAt_pi.2 fun ℓ => hasDerivAt_pi.2 fun a => hasDerivAt_pi.2 fun p => ?_
      obtain ⟨i, k | k | k⟩ := p
      · exact hasDerivAt_sum_mul_expGL_ath (Γ ℓ i) (fun k' => θ.read ℓ a (i, Sum.inl k')) k
      · exact hasDerivAt_sum_mul_expGL_inv_ath (Γ ℓ i)
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
/-- Helper: the curve `τ ↦ θ.headsVO (exp (τ Γ))` has velocity `headDirVO θ Γ` at `τ = 0`. -/
private theorem hasDerivAt_headsVO_ath (Γ : ∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) :
    HasDerivAt (fun τ : ℝ => θ.headsVO fun ℓ i => expGL_ath (Γ ℓ i) τ) (headDirVO θ Γ) 0 := by
  have hprod : HasDerivAt
      (fun τ : ℝ => Params.linearEquivProd (θ.headsVO fun ℓ i => expGL_ath (Γ ℓ i) τ))
      (Params.linearEquivProd (headDirVO θ Γ)) 0 := by
    refine HasDerivAt.prodMk ?_ (HasDerivAt.prodMk ?_ (HasDerivAt.prodMk ?_ ?_))
    · -- the embedding does not move
      exact hasDerivAt_const (0 : ℝ) θ.E
    · -- the queries and keys do not move, the values are `W_V exp(τ Γ)`
      refine hasDerivAt_pi.2 fun ℓ => hasDerivAt_pi.2 fun a => hasDerivAt_pi.2 fun p => ?_
      obtain ⟨i, k | k | k⟩ := p
      · exact hasDerivAt_const (0 : ℝ) (θ.read ℓ a (i, Sum.inl k))
      · exact hasDerivAt_const (0 : ℝ) (θ.read ℓ a (i, Sum.inr (Sum.inl k)))
      · exact hasDerivAt_sum_mul_expGL_ath (Γ ℓ i)
          (fun k' => θ.read ℓ a (i, Sum.inr (Sum.inr k'))) k
    · -- the outputs are `exp(-τ Γ) W_O`
      refine hasDerivAt_pi.2 fun ℓ => hasDerivAt_pi.2 fun p => hasDerivAt_pi.2 fun b => ?_
      obtain ⟨i, k⟩ := p
      exact hasDerivAt_sum_expGL_inv_mul_ath (Γ ℓ i) (fun k' => θ.write ℓ (i, k') b) k
    · -- the readout does not move
      exact hasDerivAt_const (0 : ℝ) θ.D
  -- back from the tuples of components to the parameters
  exact (LinearMap.toContinuousLinearMap
    (Params.linearEquivProd (A := Arch.attention sees χ H dh) (dIn := dIn)
      (dOut := dOut)).symm.toLinearMap).hasFDerivAt.comp_hasDerivAt 0 hprod

/-- The directions of the changes of basis between queries and keys are flat. -/
theorem headDirQK_mem_flat (S : Fin L → Matrix d d ℝ) (Γ : ∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) :
    headDirQK θ Γ ∈ flat (Arch.attention sees χ H dh) S θ := by
  -- the curve `τ ↦ θ.headsQK (exp (τ Γ))` passes through `θ` with velocity `headDirQK θ Γ`, and
  -- it preserves the function at every `τ`
  exact mem_flat_of_hasDerivAt' θ (fun τ => θ.headsQK fun ℓ i => expGL_ath (Γ ℓ i) τ)
    (headDirQK θ Γ) (hasDerivAt_headsQK_ath θ Γ) (headsQK_expGL_zero_ath θ Γ)
    (Filter.Eventually.of_forall fun τ x => eval_headsQK θ _ S x)

/-- The directions of the changes of basis between values and outputs are flat. -/
theorem headDirVO_mem_flat (S : Fin L → Matrix d d ℝ) (Γ : ∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) :
    headDirVO θ Γ ∈ flat (Arch.attention sees χ H dh) S θ := by
  -- the curve `τ ↦ θ.headsVO (exp (τ Γ))` passes through `θ` with velocity `headDirVO θ Γ`, and
  -- it preserves the function at every `τ`
  exact mem_flat_of_hasDerivAt' θ (fun τ => θ.headsVO fun ℓ i => expGL_ath (Γ ℓ i) τ)
    (headDirVO θ Γ) (hasDerivAt_headsVO_ath θ Γ) (headsVO_expGL_zero_ath θ Γ)
    (Filter.Eventually.of_forall fun τ x => eval_headsVO θ _ S x)

/-- **Lemma B.1 for attention blocks, in infinitesimal form:** if `E` and every write have rank
`d` and the query matrix and the value matrix of every head have rank `d_h`, the changes of basis
`X` of the hidden states and the changes of basis `Γ`, `Γ'` inside the heads are determined by
the direction `cobDir θ X + headDirQK θ Γ + headDirVO θ Γ'`. -/
theorem cobDir_add_headDirQK_add_headDirVO_injective (hE : θ.E.rank = Fintype.card d)
    (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d)
    (hQ : ∀ ℓ (i : H ℓ), ((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k)).rank
      = Fintype.card (dh ℓ))
    (hV : ∀ ℓ (i : H ℓ),
      ((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))).rank
        = Fintype.card (dh ℓ)) :
    Function.Injective
      fun p : (Fin (L + 1) → Matrix d d ℝ) × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)
          × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) =>
        cobDir θ p.1 + headDirQK θ p.2.1 + headDirVO θ p.2.2 := by
  sorry

end Skips
