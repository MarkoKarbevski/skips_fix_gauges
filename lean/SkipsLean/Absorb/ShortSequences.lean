import SkipsLean.Absorb.ShortSequencesPoly
import SkipsLean.Network.Defs

/-!
# Attention networks on short sequences (absorb paper, Theorem 4.2 (iii))

Paper (absorb paper), Theorem 4.2: "Without normalization or with pre-RMSNorm and `ε > 0`, let a
residual network of `L` attention blocks have `E D ≠ 0`. Consider skipless networks of `L' ≥ 1`
attention blocks, with any numbers of heads and any head dimensions. […] (iii) Short sequences.
Without normalization and with a causal mask, in every other case, `T ≤ L` or `T = L + 1 ≤ L'`,
some residual network of `L` blocks with `E D ≠ 0` equals a skipless network of `L'` blocks."
After the theorem: "For `T = 2` and heads whose scores vanish, the residual block
`h ↦ h − 3 U h` equals the composition `h ↦ −2 U² h` of two skipless blocks."

Its proof: equation (10) (`Absorb/ShortSequencesPoly.lean`), then: "Let `Π = diag(1, 1, 0, …, 0)`,
and let the `d_model × d_model` matrix `J` have the entries `J_12 = −1` and `J_21 = 1` and zeros
elsewhere, so that `J² = −Π` and `J Π = Π J = J`. […] Let every score matrix vanish, in both
networks. Then every attention matrix is `U`, block `ℓ` is the linear map `h ↦ h + U h V_ℓ`, and
the residual network is `X ↦ ∑_k U^k X Λ_k`, where `∑_k Λ_k z^k = E ∏_ℓ (I + z V_ℓ) D`. […] the
residual network is `X ↦ Q(U) X E D`. […] The skipless network with the same `E` and `D` whose
blocks have `V'_1 = γ' Π` and `V'_ℓ = Π` for `ℓ ≥ 2` is `X ↦ γ' U^{L'} X E D`, so the two
networks are equal. A block has the sum `V` once its heads have value–output products that add up
to `V`, which two heads of any dimension allow for matrices of rank at most 2."

Here, with the tokens `Fin n`, the causal mask `fun t s => s ≤ t`, the skipless network of
`L' + 1` blocks (the paper's `L'`), every model dimension `m + 2 ≥ 2`, input and output
dimensions `a + 1` and `b + 1`, and two heads of dimension one in every block of both networks:

* `one_sub_three_smul_attnWeights_causal_two`: the identity `I − 3 U = −2 U²` for two tokens;
* `exists_residual_eq_skipless_attention_causal_short`: part (iii), for at least one token, with
  one clause more than the paper: the common function of the two networks is not zero. (For
  `n ≤ L` the statement of the paper is also met by a residual network whose function is zero,
  with `V_ℓ = −ℓ Π` for `ℓ ≤ n`; the construction of the paper gives a nonzero one.)
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise

/-- **After Theorem 4.2:** for two tokens under the causal mask and zero scores, with `U` the
matrix of the attention weights, `I − 3 U = −2 U²`: "the residual block `h ↦ h − 3 U h` equals
the composition `h ↦ −2 U² h` of two skipless blocks". -/
theorem one_sub_three_smul_attnWeights_causal_two :
    (1 : Matrix (Fin 2) (Fin 2) ℝ)
        - (3 : ℝ) • attnWeights (fun t s : Fin 2 => s ≤ t) (0 : Matrix (Fin 2) (Fin 2) ℝ)
      = (-2 : ℝ) • (attnWeights (fun t s : Fin 2 => s ≤ t) (0 : Matrix (Fin 2) (Fin 2) ℝ)
          * attnWeights (fun t s : Fin 2 => s ≤ t) (0 : Matrix (Fin 2) (Fin 2) ℝ)) := by
  sorry

/-- **Theorem 4.2 (iii), short sequences:** without normalization, with the causal mask on
`n ≥ 1` tokens, when `n ≤ L`, or `n = L + 1` and `L ≤ L'`: for every model dimension `m + 2`,
some residual network of `L` attention blocks with `E D ≠ 0` equals a skipless network of
`L' + 1` attention blocks with the same model dimension at every input, and their common
function is not zero. Both networks have two heads of dimension one in every block. -/
theorem exists_residual_eq_skipless_attention_causal_short (n L L' m a b : ℕ) (hn1 : 1 ≤ n)
    (hn : n ≤ L ∨ (n = L + 1 ∧ L ≤ L')) :
    ∃ (θ : Params (Arch.attention (T := Fin n) (d := Fin (m + 2)) (L := L)
          (fun t s => s ≤ t) id (fun _ => Fin 2) (fun _ => Fin 1)) (Fin (a + 1)) (Fin (b + 1)))
      (θ' : Params (Arch.attention (T := Fin n) (d := Fin (m + 2)) (L := L' + 1)
          (fun t s => s ≤ t) id (fun _ => Fin 2) (fun _ => Fin 1)) (Fin (a + 1)) (Fin (b + 1))),
      θ.E * θ.D ≠ 0
        ∧ (∀ X : Matrix (Fin n) (Fin (a + 1)) ℝ,
            eval (Arch.attention (fun t s => s ≤ t) id (fun _ => Fin 2) (fun _ => Fin 1)) 1 θ X
              = eval (Arch.attention (fun t s => s ≤ t) id (fun _ => Fin 2) (fun _ => Fin 1))
                  0 θ' X)
        ∧ ∃ X : Matrix (Fin n) (Fin (a + 1)) ℝ,
            eval (Arch.attention (fun t s => s ≤ t) id (fun _ => Fin 2) (fun _ => Fin 1)) 1 θ X
              ≠ 0 := by
  sorry

end Skips
