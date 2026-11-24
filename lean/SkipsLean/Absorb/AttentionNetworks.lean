import SkipsLean.Absorb.AttentionZero
import SkipsLean.Basic.RMSNorm
import SkipsLean.Generic.Params
import Mathlib.Algebra.Polynomial.RuleOfSigns

/-!
# Attention networks on long sequences

Paper (absorb paper): Theorem 4.2 (Attention networks on long and short sequences), parts (i)
and (ii): "Without normalization or with pre-RMSNorm and `ε > 0`, let a residual network of `L`
attention blocks have `E D ≠ 0`. Consider skipless networks of `L' ≥ 1` attention blocks, with
any numbers of heads and any head dimensions. (i) If the attention has no mask, no such skipless
network equals the residual one. With a causal mask on `T` tokens, the same holds when
`T ≥ L + 2`, and when `T = L + 1` and `L' ≤ L`. (ii) For almost every choice of weights of the
residual network, no such skipless network equals it, whatever `L'`."

Its proof compares the Jacobians at `X = 0` (`Absorb/AttentionZero.lean`) on the inputs `a b`
with `U a = λ a`. Without a mask, `U a = 0` for a column `a ≠ 0` whose entries add up to `0`.
With a causal mask, `U` is lower triangular with the diagonal entries `1, 1/2, …, 1/T`, and "the
matrix polynomial `p(z) = ∑_{k=0}^L Λ_k z^k − Λ' z^{L'}` vanishes at the `T` points
`z = 1, 1/2, …, 1/T`. If `L' ≤ L`, every entry of `p` is a polynomial of degree at most `L` with
`T ≥ L + 1` roots, so `p = 0`. If `L' > L`, the hypothesis gives `T ≥ L + 2`, and every entry of
`p` has at most `L + 2` nonzero coefficients. By Descartes' rule of signs […] again `p = 0`."
Part (ii): "From `p(1) = 0` and `p(1/2) = 0`, `∑_k (2^{−k} − 2^{−L'}) Λ_k = 0`. The left side
is a polynomial in the weights of the residual network. When all value–output products vanish it
equals `(1 − 2^{−L'}) ξ E D`, so it is not the zero polynomial".

Stated here in the frame of `Arch.attention` (`Network/Attention.lean`): the residual network
has `L` blocks (stream matrices `1`), the skipless network `L' + 1` blocks (stream matrices
`0`), any heads and head dimensions and any model dimension `d'`; without normalization
(`χ = id` in both) and under pre-RMSNorm (`rmsNorm ε`, `rmsNorm ε'`, `ε, ε' > 0`). Without a
mask the tokens are any finite type with at least two elements and `sees = fun _ _ => True`;
with the causal mask the tokens are `Fin n` and `sees t s` is `s ≤ t`. Descartes' rule of signs
is Mathlib's `Polynomial.roots_countP_pos_le_signVariations`. Part (iii) is not stated here.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {H dh : Fin L → Type} [∀ ℓ, Fintype (H ℓ)] [∀ ℓ, Fintype (dh ℓ)]

/-- **Theorem 4.2 (i), no mask, without normalization:** with at least two tokens, a residual
network of `L` attention blocks with `E D ≠ 0` differs from every skipless network of one or more
attention blocks, with any heads, head dimensions and model dimension. -/
theorem exists_ne_residual_skipless_attention_noMask (hT : 2 ≤ Fintype.card T)
    (θ : Params (Arch.attention (T := T) (d := d) (fun _ _ => True) id H dh) dIn dOut)
    (hED : θ.E * θ.D ≠ 0) {L' : ℕ} {d' : Type*} [Fintype d'] [DecidableEq d']
    {H' dh' : Fin (L' + 1) → Type} [∀ ℓ, Fintype (H' ℓ)] [∀ ℓ, Fintype (dh' ℓ)]
    (θ' : Params (Arch.attention (T := T) (d := d') (fun _ _ => True) id H' dh') dIn dOut) :
    ∃ X : Matrix T dIn ℝ,
      eval (Arch.attention (fun _ _ => True) id H dh) 1 θ X
        ≠ eval (Arch.attention (fun _ _ => True) id H' dh') 0 θ' X := by
  sorry

/-- **Theorem 4.2 (i), no mask, under pre-RMSNorm with `ε > 0`.** -/
theorem exists_ne_residual_skipless_attention_noMask_rmsNorm (hT : 2 ≤ Fintype.card T)
    {ε ε' : ℝ} (hε : 0 < ε) (hε' : 0 < ε')
    (θ : Params (Arch.attention (T := T) (d := d) (fun _ _ => True) (rmsNorm ε) H dh) dIn dOut)
    (hED : θ.E * θ.D ≠ 0) {L' : ℕ} {d' : Type*} [Fintype d'] [DecidableEq d']
    {H' dh' : Fin (L' + 1) → Type} [∀ ℓ, Fintype (H' ℓ)] [∀ ℓ, Fintype (dh' ℓ)]
    (θ' : Params (Arch.attention (T := T) (d := d') (fun _ _ => True) (rmsNorm ε') H' dh')
      dIn dOut) :
    ∃ X : Matrix T dIn ℝ,
      eval (Arch.attention (fun _ _ => True) (rmsNorm ε) H dh) 1 θ X
        ≠ eval (Arch.attention (fun _ _ => True) (rmsNorm ε') H' dh') 0 θ' X := by
  sorry

/-- **Theorem 4.2 (i), causal mask, without normalization:** on `n` tokens with the causal mask,
a residual network of `L` attention blocks with `E D ≠ 0` differs from every skipless network of
`L' + 1` attention blocks when `n ≥ L + 2`, and when `n = L + 1` and `L' + 1 ≤ L`. -/
theorem exists_ne_residual_skipless_attention_causal {n : ℕ}
    (θ : Params (Arch.attention (T := Fin n) (d := d) (fun t s => s ≤ t) id H dh) dIn dOut)
    (hED : θ.E * θ.D ≠ 0) {L' : ℕ} {d' : Type*} [Fintype d'] [DecidableEq d']
    {H' dh' : Fin (L' + 1) → Type} [∀ ℓ, Fintype (H' ℓ)] [∀ ℓ, Fintype (dh' ℓ)]
    (θ' : Params (Arch.attention (T := Fin n) (d := d') (fun t s => s ≤ t) id H' dh') dIn dOut)
    (hn : L + 2 ≤ n ∨ (n = L + 1 ∧ L' + 1 ≤ L)) :
    ∃ X : Matrix (Fin n) dIn ℝ,
      eval (Arch.attention (fun t s => s ≤ t) id H dh) 1 θ X
        ≠ eval (Arch.attention (fun t s => s ≤ t) id H' dh') 0 θ' X := by
  sorry

/-- **Theorem 4.2 (i), causal mask, under pre-RMSNorm with `ε > 0`.** -/
theorem exists_ne_residual_skipless_attention_causal_rmsNorm {n : ℕ} {ε ε' : ℝ} (hε : 0 < ε)
    (hε' : 0 < ε')
    (θ : Params (Arch.attention (T := Fin n) (d := d) (fun t s => s ≤ t) (rmsNorm ε) H dh)
      dIn dOut)
    (hED : θ.E * θ.D ≠ 0) {L' : ℕ} {d' : Type*} [Fintype d'] [DecidableEq d']
    {H' dh' : Fin (L' + 1) → Type} [∀ ℓ, Fintype (H' ℓ)] [∀ ℓ, Fintype (dh' ℓ)]
    (θ' : Params (Arch.attention (T := Fin n) (d := d') (fun t s => s ≤ t) (rmsNorm ε') H' dh')
      dIn dOut)
    (hn : L + 2 ≤ n ∨ (n = L + 1 ∧ L' + 1 ≤ L)) :
    ∃ X : Matrix (Fin n) dIn ℝ,
      eval (Arch.attention (fun t s => s ≤ t) (rmsNorm ε) H dh) 1 θ X
        ≠ eval (Arch.attention (fun t s => s ≤ t) (rmsNorm ε') H' dh') 0 θ' X := by
  sorry

/-- **Theorem 4.2 (ii), causal mask, without normalization:** on `n ≥ 2` tokens with the causal
mask, for almost every choice of weights of the residual network of `L` attention blocks, no
skipless network of one or more attention blocks equals it, whatever its depth, heads, head
dimensions and model dimension. -/
theorem ae_forall_ne_residual_skipless_attention_causal [Nonempty d] [Nonempty dIn]
    [Nonempty dOut] {n : ℕ} (hn : 2 ≤ n)
    (μ : Measure (Params (Arch.attention (T := Fin n) (d := d) (fun t s => s ≤ t) id H dh)
      dIn dOut)) [μ.IsAddHaarMeasure] :
    ∀ᵐ θ ∂μ, ∀ (L' : ℕ) (d' : Type) [Fintype d'] [DecidableEq d'] (H' dh' : Fin (L' + 1) → Type)
      [∀ ℓ, Fintype (H' ℓ)] [∀ ℓ, Fintype (dh' ℓ)]
      (θ' : Params (Arch.attention (T := Fin n) (d := d') (fun t s => s ≤ t) id H' dh')
        dIn dOut),
      ∃ X : Matrix (Fin n) dIn ℝ,
        eval (Arch.attention (fun t s => s ≤ t) id H dh) 1 θ X
          ≠ eval (Arch.attention (fun t s => s ≤ t) id H' dh') 0 θ' X := by
  sorry

/-- **Theorem 4.2 (ii), causal mask, under pre-RMSNorm with `ε > 0`.** -/
theorem ae_forall_ne_residual_skipless_attention_causal_rmsNorm [Nonempty d] [Nonempty dIn]
    [Nonempty dOut] {n : ℕ} (hn : 2 ≤ n) {ε : ℝ} (hε : 0 < ε)
    (μ : Measure (Params
      (Arch.attention (T := Fin n) (d := d) (fun t s => s ≤ t) (rmsNorm ε) H dh) dIn dOut))
    [μ.IsAddHaarMeasure] :
    ∀ᵐ θ ∂μ, ∀ (L' : ℕ) (d' : Type) [Fintype d'] [DecidableEq d'] (H' dh' : Fin (L' + 1) → Type)
      [∀ ℓ, Fintype (H' ℓ)] [∀ ℓ, Fintype (dh' ℓ)] (ε' : ℝ), 0 < ε' →
      ∀ θ' : Params (Arch.attention (T := Fin n) (d := d') (fun t s => s ≤ t) (rmsNorm ε') H' dh')
        dIn dOut,
      ∃ X : Matrix (Fin n) dIn ℝ,
        eval (Arch.attention (fun t s => s ≤ t) (rmsNorm ε) H dh) 1 θ X
          ≠ eval (Arch.attention (fun t s => s ≤ t) (rmsNorm ε') H' dh') 0 θ' X := by
  sorry

end Skips
