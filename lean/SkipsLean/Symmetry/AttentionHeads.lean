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

/-- **The changes of basis between queries and keys preserve the function** (Appendix B), for
every mask, every `χ` and all stream matrices. -/
theorem eval_headsQK (K : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ) (S : Fin L → Matrix d d ℝ)
    (x : Matrix T dIn ℝ) :
    eval (Arch.attention sees χ H dh) S (θ.headsQK K) x
      = eval (Arch.attention sees χ H dh) S θ x := by
  sorry

/-- **The changes of basis between values and outputs preserve the function** (Appendix B). -/
theorem eval_headsVO (K : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ) (S : Fin L → Matrix d d ℝ)
    (x : Matrix T dIn ℝ) :
    eval (Arch.attention sees χ H dh) S (θ.headsVO K) x
      = eval (Arch.attention sees χ H dh) S θ x := by
  sorry

/-- The directions of the changes of basis between queries and keys are flat. -/
theorem headDirQK_mem_flat (S : Fin L → Matrix d d ℝ) (Γ : ∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) :
    headDirQK θ Γ ∈ flat (Arch.attention sees χ H dh) S θ := by
  sorry

/-- The directions of the changes of basis between values and outputs are flat. -/
theorem headDirVO_mem_flat (S : Fin L → Matrix d d ℝ) (Γ : ∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) :
    headDirVO θ Γ ∈ flat (Arch.attention sees χ H dh) S θ := by
  sorry

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
