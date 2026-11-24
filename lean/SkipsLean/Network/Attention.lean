import SkipsLean.Network.Blocks

/-!
# Attention blocks

Paper (absorb paper), Section 3.3, equation (4): "An attention block has `H` heads of dimension
`d_h`. Head `i` has the matrices `W_{Q,i}, W_{K,i}, W_{V,i} ∈ ℝ^{d_model × d_h}` and
`W_{O,i} ∈ ℝ^{d_h × d_model}`, and the parameters `θ` of the block are the matrices of all its
heads. The block maps `h ∈ ℝ^{T × d_model}`, whose rows are the `T ≥ 2` tokens, to
`B_θ(h) = ∑_{i=1}^H P_{Γ_i}(h) h W_{V,i} W_{O,i}`, `P_Γ(h) = softmax(h Γ h^⊤)`,
`Γ_i = W_{Q,i} W_{K,i}^⊤ / √d_h`. The entries of the `T × T` matrix `h Γ_i h^⊤` are the scores of
head `i`. The softmax acts on each of its rows, with or without a causal mask, so each row of
`P_Γ(h)` is a probability vector. The read of the block holds the matrices `W_{Q,i}`, `W_{K,i}`
and `W_{V,i}`, and its write the matrices `W_{O,i}`."

The dimension paper (Appendix C, "Attention blocks") and the skips paper (Section 2:
"`W_read = [W_Q | W_K | W_V]`, the query, key and value matrices of all heads, `f` is the
attention map") use the same block: "Head `i` gives token `t` the scores […] and the weights
`a_ts`, their softmax over the tokens `s` that token `t` sees".

Here the mask is a relation `sees t s` ("token `t` sees token `s`"): `fun _ _ => True` without a
mask, `fun t s => s ≤ t` for the causal mask on linearly ordered tokens.

* `attnWeights sees Z`: the weights of a matrix `Z` of scores, row by row.
* `attnHeads sees Γ C h = ∑_i P_{Γ_i}(h) h C_i`: the block as a function of the score matrices
  `Γ_i` and of the value–output products `C_i` of its heads.
* `attentionBlock sees WQ WK WV WO h`: equation (4).
* `Arch.attention`: networks of attention blocks in the frame of `Arch`; block `ℓ` has the heads
  `H ℓ` of dimension `dh ℓ`, the columns of its read are indexed by a head and by a coordinate of
  its query (`Sum.inl k`), of its key (`Sum.inr (Sum.inl k)`) or of its value
  (`Sum.inr (Sum.inr k)`), and the rows of its write by a head and a coordinate.
* `f_attention_mul`: the block of `Arch.attention` on a hidden state is equation (4).
-/

namespace Skips

open Matrix

variable {T d : Type*} {L : ℕ} [Fintype T] [Fintype d]

/-- **The attention weights of a matrix of scores:** row `t` is the softmax of the scores of the
tokens that token `t` sees, and `0` at the tokens it does not see. -/
noncomputable def attnWeights (sees : T → T → Prop) [DecidableRel sees] (Z : Matrix T T ℝ) :
    Matrix T T ℝ :=
  Matrix.of fun t s =>
    if sees t s then Real.exp (Z t s) / ∑ s', if sees t s' then Real.exp (Z t s') else 0 else 0

/-- **An attention block as a function of the score matrices `Γ_i` and of the value–output
products `C_i` of its heads:** `h ↦ ∑_i P_{Γ_i}(h) h C_i`, `P_Γ(h) = softmax(h Γ h^⊤)`. -/
noncomputable def attnHeads (sees : T → T → Prop) [DecidableRel sees] {H : Type*} [Fintype H]
    (Γ C : H → Matrix d d ℝ) (h : Matrix T d ℝ) : Matrix T d ℝ :=
  ∑ i, attnWeights sees (h * Γ i * hᵀ) * h * C i

/-- **An attention block, equation (4) of the absorb paper:** `H` heads of dimension `d_h`, with
`Γ_i = W_{Q,i} W_{K,i}^⊤ / √d_h` and the value–output products `W_{V,i} W_{O,i}`. -/
noncomputable def attentionBlock (sees : T → T → Prop) [DecidableRel sees] {H dh : Type*}
    [Fintype H] [Fintype dh] (WQ WK WV : H → Matrix d dh ℝ) (WO : H → Matrix dh d ℝ)
    (h : Matrix T d ℝ) : Matrix T d ℝ :=
  attnHeads sees (fun i => (Real.sqrt (Fintype.card dh))⁻¹ • (WQ i * (WK i)ᵀ))
    (fun i => WV i * WO i) h

/-- **A network of attention blocks:** block `ℓ` has the heads `H ℓ` of dimension `dh ℓ`. Its
read is `[W_Q | W_K | W_V]` for all heads, its write holds the `W_O`, and its fixed map sends the
queries, keys and values of the tokens to the outputs of the heads: for head `i`, the scores
`⟨q_t, k_s⟩ / √d_h`, their softmax over the tokens `s` that token `t` sees, and the weighted sum
of the values. The map `χ` is the identity or a normalization. -/
noncomputable abbrev Arch.attention (sees : T → T → Prop) [DecidableRel sees]
    (χ : Matrix T d ℝ → Matrix T d ℝ) (H dh : Fin L → Type) [∀ ℓ, Fintype (H ℓ)]
    [∀ ℓ, Fintype (dh ℓ)] : Arch T d L where
  r ℓ := H ℓ × (dh ℓ ⊕ (dh ℓ ⊕ dh ℓ))
  w ℓ := H ℓ × dh ℓ
  f ℓ M := Matrix.of fun t p =>
    ∑ s, attnWeights sees (Matrix.of fun t' s' => (Real.sqrt (Fintype.card (dh ℓ)))⁻¹
        * ∑ k, M t' (p.1, Sum.inl k) * M s' (p.1, Sum.inr (Sum.inl k))) t s
      * M s (p.1, Sum.inr (Sum.inr p.2))
  χ := χ

/-- **The block of `Arch.attention` is equation (4):** on a hidden state `h`, with the read `R`
and the write `W`, the output of block `ℓ` is the attention block whose head `i` has the query,
key and value matrices in the columns `(i, ·)` of `R` and the output matrix in the rows `(i, ·)`
of `W`. -/
theorem f_attention_mul (sees : T → T → Prop) [DecidableRel sees]
    (χ : Matrix T d ℝ → Matrix T d ℝ) (H dh : Fin L → Type) [∀ ℓ, Fintype (H ℓ)]
    [∀ ℓ, Fintype (dh ℓ)] (ℓ : Fin L) (h : Matrix T d ℝ)
    (R : Matrix d (H ℓ × (dh ℓ ⊕ (dh ℓ ⊕ dh ℓ))) ℝ) (W : Matrix (H ℓ × dh ℓ) d ℝ) :
    (Arch.attention sees χ H dh).f ℓ (h * R) * W
      = attentionBlock sees
          (fun i => R.submatrix id fun k => (i, Sum.inl k))
          (fun i => R.submatrix id fun k => (i, Sum.inr (Sum.inl k)))
          (fun i => R.submatrix id fun k => (i, Sum.inr (Sum.inr k)))
          (fun i => W.submatrix (fun k => (i, k)) id) h := by
  sorry

end Skips
