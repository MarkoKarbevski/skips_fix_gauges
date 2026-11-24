import SkipsLean.Absorb.AttentionBlock

/-!
# Attention heads are identifiable on three or more tokens

Paper (absorb paper), Appendix A.2.

Lemma A.14 (Attention heads are identifiable): "Let `T ≥ 3`. Let
`Γ_1, …, Γ_m ∈ ℝ^{d_model × d_model}` be distinct, let `C_1, …, C_m, M ∈ ℝ^{d_model × d_model}`,
and write `P_Γ(h) = softmax(h Γ h^⊤)`, with the softmax taken row by row, with or without a causal
mask. If `h M + ∑_{k=1}^m P_{Γ_k}(h) h C_k = 0` for all `h` in a nonempty open subset of
`ℝ^{T × d_model}`, then `M = 0` and `C_1 = ⋯ = C_m = 0`."

Proposition A.15 (The softmaxes must match): "Let `T ≥ 3`, let `θ` and `θ′` be parameters of
attention blocks, and suppose that `h M + B_θ(h) = B_{θ′}(h)` for all `h` in a nonempty open set.
Then `M = 0`, and for every matrix `Γ`, the heads with score matrix `Γ` have the same sum of
value–output products in `B_θ` as in `B_{θ′}`."

The proof of the lemma uses the mask through one token only: "look at the last row, which attends
to all `T` tokens with or without a causal mask". So the lemma is stated for any mask `sees` in
which some token sees every token, on at least three tokens; the two masks of the paper (no mask:
`sees = fun _ _ => True`; the causal mask on `Fin n`: `sees t s` is `s ≤ t`) are stated by name.
`P_Γ(h)` is `attnWeights sees (h * Γ * hᵀ)` (`Network/Attention.lean`), and an attention block
with the score matrices `Γ_i` and the value–output products `C_i` is `attnHeads sees Γ C`; the
block `B_θ` of the paper, with the heads `W_{Q,i}, W_{K,i}, W_{V,i}, W_{O,i}` of dimension `d_h`,
is `attentionBlock`, with `Γ_i = W_{Q,i} W_{K,i}^⊤ / √d_h` and `C_i = W_{V,i} W_{O,i}`.

With two tokens the lemma fails (the paper, after Proposition A.15: "With two tokens, heads can
cancel"). The paper's proof moves one token along a complex line and compares the poles of the
heads.
-/

namespace Skips

open Matrix

variable {T d : Type*} [Fintype T] [Fintype d]

/-- **Lemma A.14 of the absorb paper (Attention heads are identifiable):** on at least three
tokens, with a mask in which some token sees every token, let the score matrices `Γ_1, …, Γ_m` be
distinct. If `h M + ∑_k P_{Γ_k}(h) h C_k = 0` for all `h` in a nonempty open set, then `M = 0` and
every `C_k = 0`. -/
theorem attnHeads_identifiable (sees : T → T → Prop) [DecidableRel sees]
    (hT : 3 ≤ Fintype.card T) (hsees : ∃ t₀, ∀ s, sees t₀ s) {m : ℕ}
    (Γ : Fin m → Matrix d d ℝ) (hΓ : Function.Injective Γ) (C : Fin m → Matrix d d ℝ)
    (M : Matrix d d ℝ) (U : Set (Matrix T d ℝ)) (hU : IsOpen U) (hne : U.Nonempty)
    (h0 : ∀ h ∈ U, h * M + ∑ k, attnWeights sees (h * Γ k * hᵀ) * h * C k = 0) :
    M = 0 ∧ ∀ k, C k = 0 := by
  sorry

/-- **Lemma A.14 without a mask:** every token sees every token. -/
theorem attnHeads_identifiable_noMask (hT : 3 ≤ Fintype.card T) {m : ℕ}
    (Γ : Fin m → Matrix d d ℝ) (hΓ : Function.Injective Γ) (C : Fin m → Matrix d d ℝ)
    (M : Matrix d d ℝ) (U : Set (Matrix T d ℝ)) (hU : IsOpen U) (hne : U.Nonempty)
    (h0 : ∀ h ∈ U,
      h * M + ∑ k, attnWeights (fun _ _ : T => True) (h * Γ k * hᵀ) * h * C k = 0) :
    M = 0 ∧ ∀ k, C k = 0 := by
  sorry

/-- **Lemma A.14 with the causal mask:** on the tokens `0, …, n − 1`, `n ≥ 3`, token `t` sees the
tokens `s ≤ t`. -/
theorem attnHeads_identifiable_causal {n : ℕ} (hn : 3 ≤ n) {m : ℕ}
    (Γ : Fin m → Matrix d d ℝ) (hΓ : Function.Injective Γ) (C : Fin m → Matrix d d ℝ)
    (M : Matrix d d ℝ) (U : Set (Matrix (Fin n) d ℝ)) (hU : IsOpen U) (hne : U.Nonempty)
    (h0 : ∀ h ∈ U,
      h * M + ∑ k, attnWeights (fun t s : Fin n => s ≤ t) (h * Γ k * hᵀ) * h * C k = 0) :
    M = 0 ∧ ∀ k, C k = 0 := by
  sorry

open scoped Classical in
/-- **Proposition A.15 of the absorb paper (The softmaxes must match), for attention blocks given
by their score matrices and value–output products:** on at least three tokens, with a mask in
which some token sees every token, if `h M + B(h) = B'(h)` for all `h` in a nonempty open set,
then `M = 0`, and for every matrix `G` the heads with the score matrix `G` have the same sum of
value–output products in `B` as in `B'`. -/
theorem attnHeads_sum_eq_of_mul_add_eq (sees : T → T → Prop) [DecidableRel sees]
    (hT : 3 ≤ Fintype.card T) (hsees : ∃ t₀, ∀ s, sees t₀ s) {H H' : Type*} [Fintype H]
    [Fintype H'] (Γ C : H → Matrix d d ℝ) (Γ' C' : H' → Matrix d d ℝ) (M : Matrix d d ℝ)
    (U : Set (Matrix T d ℝ)) (hU : IsOpen U) (hne : U.Nonempty)
    (h0 : ∀ h ∈ U, h * M + attnHeads sees Γ C h = attnHeads sees Γ' C' h) :
    M = 0 ∧ ∀ G : Matrix d d ℝ,
      (∑ i, if Γ i = G then C i else 0) = ∑ i, if Γ' i = G then C' i else 0 := by
  sorry

open scoped Classical in
/-- **Proposition A.15 of the absorb paper (The softmaxes must match):** for attention blocks
`B_θ`, `B_{θ′}` with any numbers of heads and any head dimensions, on at least three tokens, with
a mask in which some token sees every token: if `h M + B_θ(h) = B_{θ′}(h)` for all `h` in a
nonempty open set, then `M = 0`, and for every matrix `G` the heads with the score matrix
`W_Q W_K^⊤ / √d_h = G` have the same sum of value–output products `W_V W_O` in `B_θ` as in
`B_{θ′}`. -/
theorem attentionBlock_sum_eq_of_mul_add_eq (sees : T → T → Prop) [DecidableRel sees]
    (hT : 3 ≤ Fintype.card T) (hsees : ∃ t₀, ∀ s, sees t₀ s) {H dh H' dh' : Type*} [Fintype H]
    [Fintype dh] [Fintype H'] [Fintype dh'] (WQ WK WV : H → Matrix d dh ℝ)
    (WO : H → Matrix dh d ℝ) (WQ' WK' WV' : H' → Matrix d dh' ℝ) (WO' : H' → Matrix dh' d ℝ)
    (M : Matrix d d ℝ) (U : Set (Matrix T d ℝ)) (hU : IsOpen U) (hne : U.Nonempty)
    (h0 : ∀ h ∈ U, h * M + attentionBlock sees WQ WK WV WO h
      = attentionBlock sees WQ' WK' WV' WO' h) :
    M = 0 ∧ ∀ G : Matrix d d ℝ,
      (∑ i, if (Real.sqrt (Fintype.card dh))⁻¹ • (WQ i * (WK i)ᵀ) = G then WV i * WO i else 0)
        = ∑ i, if (Real.sqrt (Fintype.card dh'))⁻¹ • (WQ' i * (WK' i)ᵀ) = G
            then WV' i * WO' i else 0 := by
  sorry

end Skips
