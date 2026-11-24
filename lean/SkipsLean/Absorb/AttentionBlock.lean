import SkipsLean.Network.Attention
import SkipsLean.Imports

/-!
# No absorption in attention blocks

Paper (absorb paper): Theorem 3.4 (No absorption in attention blocks) and Theorem A.13 (Attention
and linear terms): "Let `θ` and `θ'` be parameters of attention blocks with any numbers of heads
and any head dimensions, and let `M ≠ 0` be a `d_model × d_model` matrix. (i) For almost every
`h ∈ ℝ^{T × d_model}`, `h M + B_θ(h) ≠ B_θ'(h)`. (ii) Some `h` whose rows have norm at most `1`
has a row in which `h M + B_θ(h)` and `B_θ'(h)` differ by at least `‖M‖/3`, where `‖M‖` is the
spectral norm. (iii) With an embedding `E` and a readout `D` with `E D ≠ 0`, the residual network
`X ↦ (X E + B_θ(X E)) D` differs from every skipless network `X ↦ B_θ'(X E') D'`."

Its proof: "Step 1: equal tokens. Let every row of `h` be `x`. Each row of `R_k(h)` sums to `1`,
so every row of `R_k(h) h` is `x`. […] Step 2: one zero token. Let the last row of `h` be `0` and
the other rows `y`. Every score in the last row of `R_k(h)` is a product with the last row of
`h`, which is `0`. So that row of `R_k(h)` is `(1/T, …, 1/T)`, also with a causal mask, since the
last token sees all `T` tokens."

Stated here for blocks given by the score matrices and the value–output products of their heads
(`attnHeads`, `Network/Attention.lean`): any matrices `Γ_i`, `C_i`, so any numbers of heads and
any head dimensions, and the paper's blocks (`attentionBlock`) in the two corollaries for
Theorem 3.4. The mask is any relation `sees` with one token `t₀` that sees all tokens (the last
token under the causal mask, any token without a mask), and there are at least two tokens. Norms
of rows are Euclidean, written `Real.sqrt (v ⬝ᵥ v)`; "at least `‖M‖/3`" is stated for every row
`x` of norm at most `1` as "at least `‖x M‖/3`" (the spectral norm is the largest `‖x M‖`).
-/

namespace Skips

open Matrix MeasureTheory

variable {T d : Type*} [Fintype T] [Fintype d]

/-- **Proof of Theorem A.13, Step 1 (equal tokens):** if every row of `h` is `x`, the row of the
block at a token that sees some token is `x ∑_i C_i`. -/
theorem attnHeads_const_row (sees : T → T → Prop) [DecidableRel sees] {H : Type*} [Fintype H]
    (Γ C : H → Matrix d d ℝ) (x : d → ℝ) (t : T) (ht : ∃ s, sees t s) :
    attnHeads sees Γ C (Matrix.of fun _ => x) t = x ᵥ* ∑ i, C i := by
  sorry

/-- **Proof of Theorem A.13, Step 2 (one zero token):** if row `t₀` of `h` is `0` and token `t₀`
sees all tokens, the row of the block at `t₀` is the mean of the rows of `h` times
`∑_i C_i`. -/
theorem attnHeads_zero_row (sees : T → T → Prop) [DecidableRel sees] {H : Type*} [Fintype H]
    (Γ C : H → Matrix d d ℝ) (h : Matrix T d ℝ) (t₀ : T) (ht₀ : ∀ s, sees t₀ s)
    (h0 : h t₀ = 0) :
    attnHeads sees Γ C h t₀ = ((Fintype.card T : ℝ)⁻¹ • ∑ s, h s) ᵥ* ∑ i, C i := by
  sorry

/-- **Theorem A.13 (ii) / Theorem 3.4 (ii):** with at least two tokens and a token that sees all
tokens, for every row `x` of norm at most `1` some `h` whose rows have norm at most `1` has a row
in which `h M + B_θ(h)` and `B_θ'(h)` differ by at least `‖x M‖/3`. -/
theorem exists_row_attnHeads_sub_ge (sees : T → T → Prop) [DecidableRel sees]
    (hT : 2 ≤ Fintype.card T) (t₀ : T) (ht₀ : ∀ s, sees t₀ s) {H H' : Type*} [Fintype H]
    [Fintype H'] (Γ C : H → Matrix d d ℝ) (Γ' C' : H' → Matrix d d ℝ) (M : Matrix d d ℝ)
    (x : d → ℝ) (hx : x ⬝ᵥ x ≤ 1) :
    ∃ h : Matrix T d ℝ, (∀ t, h t ⬝ᵥ h t ≤ 1) ∧ ∃ t,
      Real.sqrt ((x ᵥ* M) ⬝ᵥ (x ᵥ* M)) / 3
        ≤ Real.sqrt (((h * M + attnHeads sees Γ C h - attnHeads sees Γ' C' h) t)
            ⬝ᵥ ((h * M + attnHeads sees Γ C h - attnHeads sees Γ' C' h) t)) := by
  sorry

/-- **Theorem A.13 (i) / Theorem 3.4 (i):** with at least two tokens and a token that sees all
tokens, for `M ≠ 0` and almost every `h`, `h M + B_θ(h) ≠ B_θ'(h)`. -/
theorem ae_mul_add_attnHeads_ne (sees : T → T → Prop) [DecidableRel sees]
    (hT : 2 ≤ Fintype.card T) (t₀ : T) (ht₀ : ∀ s, sees t₀ s) {H H' : Type*} [Fintype H]
    [Fintype H'] (Γ C : H → Matrix d d ℝ) (Γ' C' : H' → Matrix d d ℝ) (M : Matrix d d ℝ)
    (hM : M ≠ 0) (μ : Measure (T → d → ℝ)) [μ.IsAddHaarMeasure] :
    ∀ᵐ h ∂μ, (Matrix.of h) * M + attnHeads sees Γ C (Matrix.of h)
      ≠ attnHeads sees Γ' C' (Matrix.of h) := by
  sorry

/-- **Theorem A.13 (iii):** with at least two tokens and a token that sees all tokens, an
embedding `E` and a readout `D` with `E D ≠ 0`, the residual network
`X ↦ (X E + B_θ(X E)) D` of one attention block differs from every skipless network
`X ↦ B_θ'(X E') D'` of one attention block, of any model dimension. -/
theorem exists_ne_residual_skipless_attnHeads (sees : T → T → Prop) [DecidableRel sees]
    (hT : 2 ≤ Fintype.card T) (t₀ : T) (ht₀ : ∀ s, sees t₀ s) {dIn dOut d' H H' : Type*}
    [Fintype dIn] [Fintype d'] [Fintype H] [Fintype H'] (Γ C : H → Matrix d d ℝ)
    (Γ' C' : H' → Matrix d' d' ℝ) (E : Matrix dIn d ℝ) (D : Matrix d dOut ℝ)
    (E' : Matrix dIn d' ℝ) (D' : Matrix d' dOut ℝ) (hED : E * D ≠ 0) :
    ∃ X : Matrix T dIn ℝ,
      (X * E + attnHeads sees Γ C (X * E)) * D ≠ attnHeads sees Γ' C' (X * E') * D' := by
  sorry

/-- **Theorem 3.4 (i), for the blocks of equation (4):** attention blocks with any numbers of
heads and any head dimensions, `M ≠ 0`: for almost every `h`, `h M + B_θ(h) ≠ B_θ'(h)`. -/
theorem ae_mul_add_attentionBlock_ne (sees : T → T → Prop) [DecidableRel sees]
    (hT : 2 ≤ Fintype.card T) (t₀ : T) (ht₀ : ∀ s, sees t₀ s) {H H' dh dh' : Type*} [Fintype H]
    [Fintype H'] [Fintype dh] [Fintype dh'] (WQ WK WV : H → Matrix d dh ℝ)
    (WO : H → Matrix dh d ℝ) (WQ' WK' WV' : H' → Matrix d dh' ℝ) (WO' : H' → Matrix dh' d ℝ)
    (M : Matrix d d ℝ) (hM : M ≠ 0) (μ : Measure (T → d → ℝ)) [μ.IsAddHaarMeasure] :
    ∀ᵐ h ∂μ, (Matrix.of h) * M + attentionBlock sees WQ WK WV WO (Matrix.of h)
      ≠ attentionBlock sees WQ' WK' WV' WO' (Matrix.of h) := by
  sorry

/-- **Theorem 3.4 (ii), for the blocks of equation (4).** -/
theorem exists_row_attentionBlock_sub_ge (sees : T → T → Prop) [DecidableRel sees]
    (hT : 2 ≤ Fintype.card T) (t₀ : T) (ht₀ : ∀ s, sees t₀ s) {H H' dh dh' : Type*} [Fintype H]
    [Fintype H'] [Fintype dh] [Fintype dh'] (WQ WK WV : H → Matrix d dh ℝ)
    (WO : H → Matrix dh d ℝ) (WQ' WK' WV' : H' → Matrix d dh' ℝ) (WO' : H' → Matrix dh' d ℝ)
    (M : Matrix d d ℝ) (x : d → ℝ) (hx : x ⬝ᵥ x ≤ 1) :
    ∃ h : Matrix T d ℝ, (∀ t, h t ⬝ᵥ h t ≤ 1) ∧ ∃ t,
      Real.sqrt ((x ᵥ* M) ⬝ᵥ (x ᵥ* M)) / 3
        ≤ Real.sqrt (((h * M + attentionBlock sees WQ WK WV WO h
              - attentionBlock sees WQ' WK' WV' WO' h) t)
            ⬝ᵥ ((h * M + attentionBlock sees WQ WK WV WO h
              - attentionBlock sees WQ' WK' WV' WO' h) t)) := by
  sorry

end Skips
