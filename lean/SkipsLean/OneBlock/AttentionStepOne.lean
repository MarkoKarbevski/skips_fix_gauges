import SkipsLean.OneBlock.Attention

/-!
# The one-block theorem for an attention block: Step 1

Paper (dimension paper), proof of Theorem C.1, "Attention blocks", "Step 1: the directions that
keep `B_i` and `C_i`": "For generic parameters `E` and `D` have rank `d_model`; every `W_{Q,i}`,
`W_{K,i}`, `W_{V,i}` and `W_{O,i}^⊤` has rank `d_h`, since `d_h ≤ d_model`; and the queries
`[W_{Q,1}, …, W_{Q,H}] ∈ ℝ^{d_model × H d_h}`, the keys `[W_{K,1}, …, W_{K,H}]` and the output
projection `W_O ∈ ℝ^{H d_h × d_model}` of all heads have rank `d_model`, since
`H d_h ≥ d_model`. Write `η_{Q,i}`, `η_{K,i}`, `η_{V,i}` and `η_{O,i}` for the entries of a
direction `η` at the positions of `W_{Q,i}`, `W_{K,i}`, `W_{V,i}` and `W_{O,i}`, and consider a
direction with `D_θ B_i η = 0` and `D_θ C_i η = 0` for every head. Multiplying `D_θ B_i η = 0`
on the left by the projection `I − E E^+` onto the orthogonal complement of the column space of
`E`, where `E^+` is the pseudo-inverse, leaves `(I − E E^+) η_E W_{Q,i} W_{K,i}^⊤ E^⊤ = 0`. As
`W_{K,i}^⊤ E^⊤` has full row rank, `(I − E E^+) η_E W_{Q,i} = 0` for every head, and as the
queries of all heads have rank `d_model`, `η_E = E X` with `X = E^+ η_E`. In the same way,
multiplying `D_θ C_i η = 0` on the right by the projection `I − D^+ D` gives `η_D = −Y D` with
`Y = −η_D D^+`, because `E W_{V,i}` has full column rank and the output projection has rank
`d_model`. Substituting, and cancelling `E` on the left and `E^⊤` or `D` on the right,
`(η_{Q,i} + X W_{Q,i}) W_{K,i}^⊤ + W_{Q,i} (η_{K,i} + X W_{K,i})^⊤ = 0`,
`(η_{V,i} + X W_{V,i}) W_{O,i} + W_{V,i} (η_{O,i} − W_{O,i} Y) = 0`.
If `P_1` and `P_2` have full column rank and `Z_1 P_2^⊤ + P_1 Z_2^⊤ = 0`, then multiplying on the
right by a right inverse of `P_2^⊤` gives `Z_1 = P_1 Γ` for a square matrix `Γ`, and then
`Z_2 = −P_2 Γ^⊤`. Hence
`η_{Q,i} = −X W_{Q,i} + W_{Q,i} Γ_i`, `η_{K,i} = −X W_{K,i} − W_{K,i} Γ_i^⊤`,
`η_{V,i} = −X W_{V,i} + W_{V,i} Γ'_i`, `η_{O,i} = W_{O,i} Y − Γ'_i W_{O,i}`.
These are the directions of the changes of basis `I + τ X` at `h_0` and `I + τ Y` at `h_1`, and
of `I + τ Γ_i` between the queries and keys and `I + τ Γ'_i` between the values and outputs of
head `i`."

Here: under the conditions `OneBlockGenericAttention θ` (`OneBlock/Attention.lean`; the rank of
the keys of all heads is not among them, the argument does not use it), a direction `η` with
`dAttnScore θ η i = 0` and `dAttnValue θ η i = 0` for every head is
`cobDir θ X + headDirQK θ Γ + headDirVO θ Γ'` (`Dimension/UpperBound.lean`,
`Symmetry/AttentionHeads.lean`). Pure linear algebra; no mask and no input enters.
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {sees : T → T → Prop} [DecidableRel sees]
variable {H dh : Fin 1 → Type} [∀ ℓ, Fintype (H ℓ)] [∀ ℓ, Fintype (dh ℓ)]

/-- **Proof of Theorem C.1 for attention blocks, Step 1:** under the conditions of the proof, a
direction `η` that keeps every `B_i` and every `C_i` to first order is the sum of the direction
of two changes of basis of the hidden states and of the directions of the changes of basis
inside the heads. -/
theorem exists_cobDir_add_headDir_of_keeps
    (θ : Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut)
    (hθ : OneBlockGenericAttention θ)
    (η : Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut)
    (hB : ∀ i, dAttnScore θ η i = 0) (hC : ∀ i, dAttnValue θ η i = 0) :
    ∃ (X : Fin 2 → Matrix d d ℝ) (Γ Γ' : ∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ),
      η = cobDir θ X + headDirQK θ Γ + headDirVO θ Γ' := by
  sorry

end Skips
