import SkipsLean.Absorb.BiasesConstructions

/-!
# Attention blocks with biases never absorb a linear term

Paper (absorb paper), Appendix C. Theorem C.1 (Exact absorption with biases): "Let blocks have
biases, and let `M ≠ 0`. […] (ii) No tanh block and no attention block as above absorbs `x M`, at
any width." For attention, "A block absorbs `x M`, for `M ≠ 0`, if a block of the same kind with
biases satisfies […], with the same mask, `h M + B_θ(h) = B_{θ′}(h)` for all
`h ∈ ℝ^{T × d_model}`", and "as above" is: "These scores do not depend on the positions of the
tokens".

Proof of Theorem C.1 (ii), "Attention": "Suppose that `h M + B_θ(h) = B_{θ′}(h)` for all `h`, and
let `C` and `C′` be the sums of the value–output products `W_{V,i} W_{O,i}` of the heads of `θ` and
of `θ′`. If all rows of `h` equal `x`, all keys of a head are equal, so each row of `P_i(h)` is
uniform on the tokens it sees, and all values equal `x W_{V,i} + b_{V,i}`. So every row of `B_θ(h)`
is `x C` plus a constant row, and the equation gives `M = C′ − C`. Now add `ϵδ` to the first row of
this `h`, for a row `δ`, and look at the second row, which sees the first token with or without a
causal mask. […] Hence `δ C = δ C′` for every `δ`, so `C = C′` and `M = 0`, a contradiction."

The proof uses the mask through one pair of tokens only (the second token sees the first). So the
statement is for any mask in which some token sees another token, and the paper's two masks on at
least two tokens are stated by name (no mask: `sees = fun _ _ => True`; the causal mask on `Fin n`:
`sees t s` is `s ≤ t`). The two blocks may have any numbers of heads and any head dimensions. If
every token sees itself only (one token, for the paper's masks), the block is affine in `h` and
absorbs `h M` with more heads; the paper's theorem does not state a number of tokens.

The block with biases is `attentionBlockB` (`Absorb/BiasesConstructions.lean`).
-/

namespace Skips

open Matrix

/-- **Theorem C.1 (ii) of the absorb paper for attention blocks with biases:** with a mask in which
some token sees another token, no attention block with biases, with any number of heads and any
head dimension, absorbs `h M` with `M ≠ 0`. -/
theorem forall_exists_ne_attentionBlockB {T d H dh H' dh' : Type*} [Fintype T] [Fintype d]
    [Fintype H] [Fintype dh] [Fintype H'] [Fintype dh'] (sees : T → T → Prop)
    [DecidableRel sees] (hsees : ∃ t₁ t₂, t₁ ≠ t₂ ∧ sees t₂ t₁)
    (WQ WK WV : H → Matrix d dh ℝ) (bQ bK bV : H → dh → ℝ) (WO : H → Matrix dh d ℝ)
    (bO : d → ℝ) (WQ' WK' WV' : H' → Matrix d dh' ℝ) (bQ' bK' bV' : H' → dh' → ℝ)
    (WO' : H' → Matrix dh' d ℝ) (bO' : d → ℝ) (M : Matrix d d ℝ) (hM : M ≠ 0) :
    ∃ h : Matrix T d ℝ, h * M + attentionBlockB sees WQ WK WV bQ bK bV WO bO h
      ≠ attentionBlockB sees WQ' WK' WV' bQ' bK' bV' WO' bO' h := by
  sorry

/-- **Theorem C.1 (ii) for attention blocks with biases, without a mask:** on at least two tokens,
every token sees every token. -/
theorem forall_exists_ne_attentionBlockB_noMask {T d H dh H' dh' : Type*} [Fintype T] [Fintype d]
    [Fintype H] [Fintype dh] [Fintype H'] [Fintype dh'] (hT : 2 ≤ Fintype.card T)
    (WQ WK WV : H → Matrix d dh ℝ) (bQ bK bV : H → dh → ℝ) (WO : H → Matrix dh d ℝ)
    (bO : d → ℝ) (WQ' WK' WV' : H' → Matrix d dh' ℝ) (bQ' bK' bV' : H' → dh' → ℝ)
    (WO' : H' → Matrix dh' d ℝ) (bO' : d → ℝ) (M : Matrix d d ℝ) (hM : M ≠ 0) :
    ∃ h : Matrix T d ℝ,
      h * M + attentionBlockB (fun _ _ : T => True) WQ WK WV bQ bK bV WO bO h
        ≠ attentionBlockB (fun _ _ : T => True) WQ' WK' WV' bQ' bK' bV' WO' bO' h := by
  sorry

/-- **Theorem C.1 (ii) for attention blocks with biases, with the causal mask:** on the tokens
`0, …, n − 1`, `n ≥ 2`, token `t` sees the tokens `s ≤ t`. -/
theorem forall_exists_ne_attentionBlockB_causal {n : ℕ} (hn : 2 ≤ n) {d H dh H' dh' : Type*}
    [Fintype d] [Fintype H] [Fintype dh] [Fintype H'] [Fintype dh']
    (WQ WK WV : H → Matrix d dh ℝ) (bQ bK bV : H → dh → ℝ) (WO : H → Matrix dh d ℝ)
    (bO : d → ℝ) (WQ' WK' WV' : H' → Matrix d dh' ℝ) (bQ' bK' bV' : H' → dh' → ℝ)
    (WO' : H' → Matrix dh' d ℝ) (bO' : d → ℝ) (M : Matrix d d ℝ) (hM : M ≠ 0) :
    ∃ h : Matrix (Fin n) d ℝ,
      h * M + attentionBlockB (fun t s : Fin n => s ≤ t) WQ WK WV bQ bK bV WO bO h
        ≠ attentionBlockB (fun t s : Fin n => s ≤ t) WQ' WK' WV' bQ' bK' bV' WO' bO' h := by
  sorry

end Skips
