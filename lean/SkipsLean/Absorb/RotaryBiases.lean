import SkipsLean.Absorb.BiasesConstructions

/-!
# Attention blocks with biases and rotary embeddings absorb a linear term

Paper (absorb paper), Appendix C. "Rotary embeddings. With rotary embeddings (Su et al., 2021),
the head dimension `d_h` is even, and the query and the key of the token at position `t` are
multiplied by `R^t`, where the `d_h × d_h` matrix `R` rotates `d_h/2` coordinate planes by fixed
angles. With `h_t` row `t` of `h`, the score of the query at position `t` against the key at
position `s` is then `(h_t W_{Q,i} + b_{Q,i}) R^{t−s} (h_s W_{K,i} + b_{K,i})^⊤ / √d_h`, which
depends on the two positions. Without biases, no such block absorbs a linear term (Theorem 3.4).
With biases, a head whose queries and keys are its biases attends by position alone, and such
heads add up to a skip."

Proposition C.6 (Rotary embeddings with biases): "Let attention blocks have biases and rotary
embeddings, with or without a causal mask, and let one of the rotary angles, `ϑ`, satisfy
`k ϑ ∉ 2πℤ` for `0 < k < T`. Then every attention block absorbs `h M`, for every `M`, with at most
`T² ⌈rank M / d_h⌉` more heads." After it: "The first angle of Su et al. (2021) is `ϑ = 1`, which
satisfies the condition for every `T`."

Here: the tokens are the positions `0, …, n − 1` (`Fin n`; `T = n`), the coordinate planes are an
index type `pl` and the head dimension is `pl × Fin 2`, so `d_h = 2 |pl|`; `R^k` rotates the plane
`c` by `k ϑ_c` (`rotaryPow`); the block is `attentionBlockRotaryB` (for the angles `0` it is the
block with biases of `Absorb/BiasesConstructions.lean`). The proof of the proposition uses the
mask through "Among them, `s = t`": every token sees itself. So the statement is for any such
mask, and the paper's two masks are stated by name. "With at most `k` more heads" is: a block
whose heads are the heads `H` of `B_θ` and a further finite type of at most `k` heads.
-/

namespace Skips

open Matrix

/-- **The power `R^k` of the rotary matrix:** on the head dimension `pl × Fin 2`, the plane `c`
is rotated by the angle `k ϑ_c`. -/
noncomputable def rotaryPow {pl : Type*} [DecidableEq pl] (ϑ : pl → ℝ) (k : ℤ) :
    Matrix (pl × Fin 2) (pl × Fin 2) ℝ :=
  Matrix.of fun x y =>
    if x.1 = y.1 then
      (if x.2 = y.2 then Real.cos (k * ϑ x.1)
        else if x.2 = 0 then -Real.sin (k * ϑ x.1) else Real.sin (k * ϑ x.1))
    else 0

/-- **An attention block with biases and rotary embeddings** on the positions `0, …, n − 1`: as
the block with biases, with the score of the query at position `t` against the key at position
`s` equal to `(h_t W_{Q,i} + b_{Q,i}) R^{t−s} (h_s W_{K,i} + b_{K,i})^⊤ / √d_h`. -/
noncomputable def attentionBlockRotaryB {n : ℕ} {d H pl : Type*} [Fintype d] [Fintype H]
    [Fintype pl] [DecidableEq pl] (sees : Fin n → Fin n → Prop) [DecidableRel sees] (ϑ : pl → ℝ)
    (WQ WK WV : H → Matrix d (pl × Fin 2) ℝ) (bQ bK bV : H → pl × Fin 2 → ℝ)
    (WO : H → Matrix (pl × Fin 2) d ℝ) (bO : d → ℝ) (h : Matrix (Fin n) d ℝ) :
    Matrix (Fin n) d ℝ :=
  (∑ i, attnWeights sees (Matrix.of fun t s =>
        (Real.sqrt (Fintype.card (pl × Fin 2)))⁻¹ *
          (((h t ᵥ* WQ i + bQ i) ᵥ* rotaryPow ϑ ((t : ℤ) - (s : ℤ))) ⬝ᵥ (h s ᵥ* WK i + bK i)))
      * (h * WV i + Matrix.of fun _ => bV i) * WO i)
    + Matrix.of fun _ => bO

/-- **Proposition C.6 of the absorb paper (Rotary embeddings with biases):** let attention blocks
have biases and rotary embeddings, with a mask in which every token sees itself, and let one of
the rotary angles, `ϑ`, satisfy `k ϑ ∉ 2πℤ` for `0 < k < T`. Then every attention block absorbs
`h M`, for every `M`, with at most `T² ⌈rank M / d_h⌉` more heads. -/
theorem exists_attentionBlockRotaryB_add_linear {n : ℕ} {d H pl : Type*} [Fintype d]
    [DecidableEq d] [Fintype H] [Fintype pl] [DecidableEq pl] (sees : Fin n → Fin n → Prop)
    [DecidableRel sees] (hsees : ∀ t, sees t t) (ϑ : pl → ℝ) (c₀ : pl)
    (hϑ : ∀ k : ℕ, 0 < k → k < n → ∀ z : ℤ, (k : ℝ) * ϑ c₀ ≠ 2 * Real.pi * z)
    (WQ WK WV : H → Matrix d (pl × Fin 2) ℝ) (bQ bK bV : H → pl × Fin 2 → ℝ)
    (WO : H → Matrix (pl × Fin 2) d ℝ) (bO : d → ℝ) (M : Matrix d d ℝ) :
    ∃ (K : Type) (_ : Fintype K),
      Fintype.card K ≤ n ^ 2 * ⌈(M.rank : ℚ) / (Fintype.card (pl × Fin 2) : ℚ)⌉₊ ∧
      ∃ (WQ' WK' WV' : H ⊕ K → Matrix d (pl × Fin 2) ℝ) (bQ' bK' bV' : H ⊕ K → pl × Fin 2 → ℝ)
        (WO' : H ⊕ K → Matrix (pl × Fin 2) d ℝ) (bO' : d → ℝ),
        ∀ h : Matrix (Fin n) d ℝ,
          h * M + attentionBlockRotaryB sees ϑ WQ WK WV bQ bK bV WO bO h
            = attentionBlockRotaryB sees ϑ WQ' WK' WV' bQ' bK' bV' WO' bO' h := by
  sorry

/-- **Proposition C.6 without a mask.** -/
theorem exists_attentionBlockRotaryB_add_linear_noMask {n : ℕ} {d H pl : Type*} [Fintype d]
    [DecidableEq d] [Fintype H] [Fintype pl] [DecidableEq pl] (ϑ : pl → ℝ) (c₀ : pl)
    (hϑ : ∀ k : ℕ, 0 < k → k < n → ∀ z : ℤ, (k : ℝ) * ϑ c₀ ≠ 2 * Real.pi * z)
    (WQ WK WV : H → Matrix d (pl × Fin 2) ℝ) (bQ bK bV : H → pl × Fin 2 → ℝ)
    (WO : H → Matrix (pl × Fin 2) d ℝ) (bO : d → ℝ) (M : Matrix d d ℝ) :
    ∃ (K : Type) (_ : Fintype K),
      Fintype.card K ≤ n ^ 2 * ⌈(M.rank : ℚ) / (Fintype.card (pl × Fin 2) : ℚ)⌉₊ ∧
      ∃ (WQ' WK' WV' : H ⊕ K → Matrix d (pl × Fin 2) ℝ) (bQ' bK' bV' : H ⊕ K → pl × Fin 2 → ℝ)
        (WO' : H ⊕ K → Matrix (pl × Fin 2) d ℝ) (bO' : d → ℝ),
        ∀ h : Matrix (Fin n) d ℝ,
          h * M + attentionBlockRotaryB (fun _ _ : Fin n => True) ϑ WQ WK WV bQ bK bV WO bO h
            = attentionBlockRotaryB (fun _ _ : Fin n => True) ϑ WQ' WK' WV' bQ' bK' bV' WO' bO'
              h := by
  sorry

/-- **Proposition C.6 with the causal mask:** token `t` sees the tokens `s ≤ t`. -/
theorem exists_attentionBlockRotaryB_add_linear_causal {n : ℕ} {d H pl : Type*} [Fintype d]
    [DecidableEq d] [Fintype H] [Fintype pl] [DecidableEq pl] (ϑ : pl → ℝ) (c₀ : pl)
    (hϑ : ∀ k : ℕ, 0 < k → k < n → ∀ z : ℤ, (k : ℝ) * ϑ c₀ ≠ 2 * Real.pi * z)
    (WQ WK WV : H → Matrix d (pl × Fin 2) ℝ) (bQ bK bV : H → pl × Fin 2 → ℝ)
    (WO : H → Matrix (pl × Fin 2) d ℝ) (bO : d → ℝ) (M : Matrix d d ℝ) :
    ∃ (K : Type) (_ : Fintype K),
      Fintype.card K ≤ n ^ 2 * ⌈(M.rank : ℚ) / (Fintype.card (pl × Fin 2) : ℚ)⌉₊ ∧
      ∃ (WQ' WK' WV' : H ⊕ K → Matrix d (pl × Fin 2) ℝ) (bQ' bK' bV' : H ⊕ K → pl × Fin 2 → ℝ)
        (WO' : H ⊕ K → Matrix (pl × Fin 2) d ℝ) (bO' : d → ℝ),
        ∀ h : Matrix (Fin n) d ℝ,
          h * M + attentionBlockRotaryB (fun t s : Fin n => s ≤ t) ϑ WQ WK WV bQ bK bV WO bO h
            = attentionBlockRotaryB (fun t s : Fin n => s ≤ t) ϑ WQ' WK' WV' bQ' bK' bV' WO'
              bO' h := by
  sorry

/-- **"The first angle of Su et al. (2021) is `ϑ = 1`, which satisfies the condition for every
`T`":** `k · 1 ∉ 2πℤ` for every `k > 0`. -/
theorem rotary_angle_one (k : ℕ) (hk : 0 < k) (z : ℤ) : (k : ℝ) * 1 ≠ 2 * Real.pi * z := by
  sorry

end Skips
