import SkipsLean.Absorb.Limits

/-!
# Under RMSNorm a residual network equals no skipless network: the comparison along rays

Paper ("Can an MLP Absorb Its Skip Connection Exactly?"): Theorem 4.3. "Consider pre-RMSNorm
networks, with `ε ≥ 0` and blocks of any kind and width. For almost every choice of weights, a
residual network equals no skipless network, whatever its depth, widths and kinds of blocks."
Proof in Appendix A.3.

This file has the part of the proof that holds at fixed weights ("The skipless network", "The
residual network", "Comparison"); the part "Measure zero" is in `Absorb/RMSNormGeneric.lean`.

The proof compares the two networks along rays `t X`, `t → ∞`. Write `N_0` for RMSNorm with
`ε = 0`, `n̄ = N_0(X E)` and `β(n̄) = ∑_ℓ f_ℓ(n̄ W_read^ℓ) W_write^ℓ`, the sum of the outputs of all
blocks at the normalized state `n̄`. The output of the residual network at `t X` is
`n̄ D + ρ(X) / t + O(1/t²)` with `ρ(X) = DN_0(X E)[β(n̄)] D`, and that of a skipless network is
`G(X) + O(1/t²)`. So equality forces `ρ = 0`, that is, since `D` has rank `d`: for every `n̄` whose
rows have norm `√d`, each row of `β(n̄)` is a multiple of the same row of `n̄`. The condition on the
weights of the residual network under which the two networks differ is the negation
(`TurnGeneric`): `E` and `D` have rank `d`, and at some `n̄` some row of `β(n̄)` is not a multiple of
the same row of `n̄`.

Blocks are of any kind: the fixed maps `f_ℓ` of the residual network are locally Lipschitz, as in
the proof. The skipless network has its own depth `L'`, model dimension `d'`, widths and maps
`f'_ℓ`. For `ε > 0` both networks are defined at every input, and they are equal if they have the
same output at every input; the skipless network may have another constant `ε' > 0`. For `ε = 0`
the paper defines a network at the inputs at which no hidden state has a zero row (`DefinedAt`),
and "two such networks are equal if they agree on a dense set of inputs at which both are
defined" (Section 2, "Normalization"); the statement for `ε = 0` is the negation of this.
-/

namespace Skips

open Matrix Filter
open scoped Matrix.Norms.Elementwise Topology

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]

/-- **The conditions of the proof of Theorem 4.3** on the weights of the residual network: `E` and
`D` have rank `d`, and there is a normalized state `n̄` (every row of norm `√d`) at which some row of
`β(n̄) = ∑_ℓ f_ℓ(n̄ W_read^ℓ) W_write^ℓ` is not a multiple of the same row of `n̄`. -/
structure TurnGeneric (A : Arch T d L) (θ : Params A dIn dOut) : Prop where
  rank_E : θ.E.rank = Fintype.card d
  rank_D : θ.D.rank = Fintype.card d
  /-- at some normalized state, the outputs of the blocks turn some token -/
  turn : ∃ n : Matrix T d ℝ, (∀ t, n t ⬝ᵥ n t = (Fintype.card d : ℝ)) ∧
    ∃ t, ∀ c : ℝ, (∑ ℓ, A.f ℓ (n * θ.read ℓ) * θ.write ℓ) t ≠ c • n t

/-- **Theorem 4.3 for `ε > 0`, under the conditions of the proof.** A pre-RMSNorm residual network
with locally Lipschitz blocks whose weights satisfy `TurnGeneric` equals no pre-RMSNorm skipless
network with locally Lipschitz blocks, whatever its depth, its model dimension, its widths, its
kinds of blocks and its constant `ε' > 0`: the two differ at some input. -/
theorem exists_ne_skipless_rmsNorm_of_turn {ε ε' : ℝ} (hε : 0 < ε) (hε' : 0 < ε')
    (A : Arch T d L) (hχ : A.χ = rmsNorm ε) (hf : ∀ ℓ, LocallyLipschitz (A.f ℓ))
    (θ : Params A dIn dOut) (hθ : TurnGeneric A θ)
    {L' : ℕ} {d' : Type*} [Fintype d'] (A' : Arch T d' L')
    (hχ' : A'.χ = rmsNorm ε') (hf' : ∀ ℓ, LocallyLipschitz (A'.f ℓ))
    (θ' : Params A' dIn dOut) :
    ∃ X : Matrix T dIn ℝ, eval A 1 θ X ≠ eval A' 0 θ' X := by
  sorry

/-- **Theorem 4.3 for `ε = 0`, under the conditions of the proof.** A pre-RMSNorm residual network
with `ε = 0` and locally Lipschitz blocks whose weights satisfy `TurnGeneric` equals no
pre-RMSNorm skipless network with `ε = 0` and continuous blocks, in the paper's sense of equality
for `ε = 0`: there is no dense set of inputs at which both networks are defined and agree. -/
theorem not_dense_eq_skipless_rmsNorm_zero_of_turn
    (A : Arch T d L) (hχ : A.χ = rmsNorm 0) (hf : ∀ ℓ, LocallyLipschitz (A.f ℓ))
    (θ : Params A dIn dOut) (hθ : TurnGeneric A θ)
    {L' : ℕ} {d' : Type*} [Fintype d'] (A' : Arch T d' L')
    (hχ' : A'.χ = rmsNorm 0) (hf' : ∀ ℓ, Continuous (A'.f ℓ))
    (θ' : Params A' dIn dOut) :
    ¬ ∃ S : Set (Matrix T dIn ℝ), Dense S ∧
      ∀ X ∈ S, DefinedAt A 1 θ X ∧ DefinedAt A' 0 θ' X ∧ eval A 1 θ X = eval A' 0 θ' X := by
  sorry

end Skips
