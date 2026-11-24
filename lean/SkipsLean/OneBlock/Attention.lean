import SkipsLean.Network.AttentionAnalytic
import SkipsLean.Symmetry.AttentionHeads
import SkipsLean.OneBlock.Tanh
import SkipsLean.Generic.Params

/-!
# The one-block theorem for an attention block: the reduction and Step 2

Paper (dimension paper): Theorem 5.1 (Theorem C.1 in the appendix) for an attention block:
"Let `d_model ≥ 2` and `d_in, d_out ≥ d_model`, let inputs range over all of `ℝ^{T × d_in}`, and
consider networks with one block, without normalization and without biases. The block is […] an
attention block of `H` heads of width `d_h ≤ d_model` with `H d_h ≥ d_model`, causal or not, on
sequences of at least two tokens. At generic parameters the functional dimension is
`P − 2 d_model² − s`", with `s = 2 H d_h²` for an attention block. The skips paper, Theorem B.1
(i), has the same block with a skip ("Part (i) for attention blocks", with `M = E D` "only in the
residual network"); the statements here are for any stream matrix `S 0`, so they serve both.

The proof, "Attention blocks". Reduction: with `B_i = E W_{Q,i} W_{K,i}^⊤ E^⊤ / √d_h`,
`C_i = E W_{V,i} W_{O,i} D`, `S = ∑_i C_i`: "Head `i` gives token `t` the scores `x_t B_i x_s^⊤`
and the weights `a_ts^{(i)}`, their softmax over the tokens `s` that token `t` sees, and the
output at token `t` is `∑_i ∑_s a_ts^{(i)} x_s C_i`. So the parameters enter only through these
matrices. We use inputs of two kinds: with a causal mask, any sequence, whose second token sees
only the first two; without a mask, sequences whose tokens other than the second all equal the
first. Let `k` be the number of tokens other than the second that the second token sees […].
With `u = x_2` and `v = x_2 − x_1`, head `i` puts the weight `1/(1 + k e^{−u B_i v^⊤})` on the
second token and the rest on the copies of the first, and `1/(1 + e^{−z}) = ½ + ½ tanh(z/2)`
gives the output at the second token
`y_2 = u S − ½ v S + ½ ∑_i tanh(½ (u B_i v^⊤ − log k)) v C_i`  (8)."
Step 2: "For generic parameters and generic `v` the columns `B_i v^⊤` are nonzero and pairwise
non-collinear, since `d_model ≥ 2`, and every row `v C_i` is nonzero. For such a `v`, (8) is, as
a function of `u`, the function `G` of Lemma C.3 with one tanh hidden unit per head: unit `i` has
the read column `½ B_i v^⊤`, the bias `−½ log k` and the write row `½ v C_i`, the linear term is
`u S`, and the constant is `−½ v S`. […] Lemma C.3 for tanh shows that all of these vanish. This
holds for all `v` in an open set, so `D_θ B_i η = 0` and `D_θ C_i η = 0` for every head."

Stated here for `Arch.attention sees id H dh` with one block (`Network/Attention.lean`). The
mask enters through one token `t₂` that sees itself and another token `t₁` (the paper's second
and first token: `t₂ = 1`, `t₁ = 0` under the causal mask; any two tokens without a mask). The
inputs of the proof have the row `u` at `t₂` and the row `u − v` at every other token, and the
paper's `k` is the number of tokens other than `t₂` that `t₂` sees.

* `attnQ`, `attnK`, `attnV`, `attnO`: the four matrices of head `i` of the one block.
* `attnScore θ i`, `attnValue θ i`: the matrices `B_i`, `C_i`; `dAttnScore θ η i`,
  `dAttnValue θ η i`: their derivatives along a direction `η` of the parameters.
* `eval_attention_oneBlock`: the reduction, for any stream matrix; `eval_attention_two_tokens`:
  equation (8).
* `OneBlockGenericAttention θ`: the conditions on `θ` that the proof uses.
* `flat_attention_oneBlock_keeps`: Step 2, a flat direction keeps `E S_0 D`, every `B_i` and
  every `C_i` to first order.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {sees : T → T → Prop} [DecidableRel sees] {χ : Matrix T d ℝ → Matrix T d ℝ}
variable {H dh : Fin 1 → Type} [∀ ℓ, Fintype (H ℓ)] [∀ ℓ, Fintype (dh ℓ)]

/-- The query matrix `W_{Q,i}` of head `i` of the one block. -/
abbrev attnQ (θ : Params (Arch.attention sees χ H dh) dIn dOut) (i : H 0) : Matrix d (dh 0) ℝ :=
  (θ.read 0).submatrix id fun k : dh 0 => (i, Sum.inl k)

/-- The key matrix `W_{K,i}` of head `i` of the one block. -/
abbrev attnK (θ : Params (Arch.attention sees χ H dh) dIn dOut) (i : H 0) : Matrix d (dh 0) ℝ :=
  (θ.read 0).submatrix id fun k : dh 0 => (i, Sum.inr (Sum.inl k))

/-- The value matrix `W_{V,i}` of head `i` of the one block. -/
abbrev attnV (θ : Params (Arch.attention sees χ H dh) dIn dOut) (i : H 0) : Matrix d (dh 0) ℝ :=
  (θ.read 0).submatrix id fun k : dh 0 => (i, Sum.inr (Sum.inr k))

/-- The output matrix `W_{O,i}` of head `i` of the one block. -/
abbrev attnO (θ : Params (Arch.attention sees χ H dh) dIn dOut) (i : H 0) : Matrix (dh 0) d ℝ :=
  (θ.write 0).submatrix (fun k : dh 0 => (i, k)) id

/-- **The matrix `B_i = E W_{Q,i} W_{K,i}^⊤ E^⊤ / √d_h`** of head `i` of the one block. -/
noncomputable def attnScore (θ : Params (Arch.attention sees χ H dh) dIn dOut) (i : H 0) :
    Matrix dIn dIn ℝ :=
  (Real.sqrt (Fintype.card (dh 0)))⁻¹ • (θ.E * attnQ θ i * (attnK θ i)ᵀ * θ.Eᵀ)

/-- **The matrix `C_i = E W_{V,i} W_{O,i} D`** of head `i` of the one block. -/
def attnValue (θ : Params (Arch.attention sees χ H dh) dIn dOut) (i : H 0) :
    Matrix dIn dOut ℝ :=
  θ.E * attnV θ i * attnO θ i * θ.D

/-- **`D_θ B_i η`:** the derivative of `B_i` at `θ` along the direction `η`. -/
noncomputable def dAttnScore (θ η : Params (Arch.attention sees χ H dh) dIn dOut) (i : H 0) :
    Matrix dIn dIn ℝ :=
  (Real.sqrt (Fintype.card (dh 0)))⁻¹ •
    (η.E * attnQ θ i * (attnK θ i)ᵀ * θ.Eᵀ + θ.E * attnQ η i * (attnK θ i)ᵀ * θ.Eᵀ
      + θ.E * attnQ θ i * (attnK η i)ᵀ * θ.Eᵀ + θ.E * attnQ θ i * (attnK θ i)ᵀ * η.Eᵀ)

/-- **`D_θ C_i η`:** the derivative of `C_i` at `θ` along the direction `η`. -/
def dAttnValue (θ η : Params (Arch.attention sees χ H dh) dIn dOut) (i : H 0) :
    Matrix dIn dOut ℝ :=
  η.E * attnV θ i * attnO θ i * θ.D + θ.E * attnV η i * attnO θ i * θ.D
    + θ.E * attnV θ i * attnO η i * θ.D + θ.E * attnV θ i * attnO θ i * η.D

/-- `dAttnScore θ η i` is the derivative of `B_i` along the line `θ + τ η`. -/
theorem hasDerivAt_attnScore (θ η : Params (Arch.attention sees χ H dh) dIn dOut) (i : H 0) :
    HasDerivAt (fun τ : ℝ => attnScore (θ + τ • η) i) (dAttnScore θ η i) 0 := by
  sorry

/-- `dAttnValue θ η i` is the derivative of `C_i` along the line `θ + τ η`. -/
theorem hasDerivAt_attnValue (θ η : Params (Arch.attention sees χ H dh) dIn dOut) (i : H 0) :
    HasDerivAt (fun τ : ℝ => attnValue (θ + τ • η) i) (dAttnValue θ η i) 0 := by
  sorry

/-- **Proof of Theorem C.1 for attention blocks, the reduction:** without normalization, the
network of one attention block with the stream matrix `S 0` gives the output
`x E S_0 D + ∑_i P_i(x) x C_i`, where `P_i(x)` holds the weights of the scores `x B_i x^⊤`: "the
parameters enter only through these matrices". -/
theorem eval_attention_oneBlock (S : Fin 1 → Matrix d d ℝ)
    (θ : Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut) (x : Matrix T dIn ℝ) :
    eval (Arch.attention sees id H dh) S θ x
      = x * (θ.E * S 0 * θ.D)
        + ∑ i, attnWeights sees (x * attnScore θ i * xᵀ) * x * attnValue θ i := by
  sorry

/-- **Equation (8):** let token `t₂` see itself and another token `t₁`, and let `k` be the number
of tokens other than `t₂` that `t₂` sees. At the input with the row `u` at `t₂` and the row
`u − v` at every other token, the output at `t₂` is
`u (E S_0 D + ∑_i C_i) − ½ v ∑_i C_i + ½ ∑_i tanh(½ (u B_i v^⊤ − log k)) v C_i`. -/
theorem eval_attention_two_tokens [DecidableEq T] (S : Fin 1 → Matrix d d ℝ) (t₁ t₂ : T)
    (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁)
    (θ : Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut) (u v : dIn → ℝ) :
    eval (Arch.attention sees id H dh) S θ (Matrix.of fun t => if t = t₂ then u else u - v) t₂
      = u ᵥ* (θ.E * S 0 * θ.D + ∑ i, attnValue θ i) - (1 / 2 : ℝ) • (v ᵥ* ∑ i, attnValue θ i)
        + ∑ i, ((1 / 2 : ℝ) * Real.tanh ((1 / 2) * (u ⬝ᵥ (attnScore θ i *ᵥ v)
            - Real.log ((Finset.univ.filter fun s => sees t₂ s ∧ s ≠ t₂).card : ℝ))))
          • (v ᵥ* attnValue θ i) := by
  sorry

/-- **The conditions on `θ` in the proof of Theorem C.1 for an attention block:** `E` and `D`
have rank `d`; the query, key, value and output matrices of every head have rank `d_h`; the
queries of all heads and the write (the output matrices of all heads) have rank `d`; and some `v`
has the columns `B_i v^⊤` nonzero and pairwise non-collinear and every row `v C_i` nonzero. -/
structure OneBlockGenericAttention
    (θ : Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut) : Prop where
  rank_E : θ.E.rank = Fintype.card d
  rank_D : θ.D.rank = Fintype.card d
  rank_Q : ∀ i : H 0, (attnQ θ i).rank = Fintype.card (dh 0)
  rank_K : ∀ i : H 0, (attnK θ i).rank = Fintype.card (dh 0)
  rank_V : ∀ i : H 0, (attnV θ i).rank = Fintype.card (dh 0)
  rank_O : ∀ i : H 0, (attnO θ i).rank = Fintype.card (dh 0)
  /-- the queries of all heads have rank `d` -/
  rank_queries : ((θ.read 0).submatrix id fun p : H 0 × dh 0 => (p.1, Sum.inl p.2)).rank
    = Fintype.card d
  /-- the write, which stacks the output matrices of all heads, has rank `d` -/
  rank_write : (θ.write 0).rank = Fintype.card d
  /-- some `v` has the `B_i v^⊤` nonzero and pairwise non-collinear and every `v C_i` nonzero -/
  exists_v : ∃ v : dIn → ℝ, (∀ i, attnScore θ i *ᵥ v ≠ 0)
    ∧ (∀ i j, i ≠ j → ∀ r : ℝ, attnScore θ i *ᵥ v ≠ r • (attnScore θ j *ᵥ v))
    ∧ (∀ i, v ᵥ* attnValue θ i ≠ 0)

/-- **Proof of Theorem C.1 for attention blocks, Step 2, for any stream matrix:** let token `t₂`
see itself and another token `t₁`, and let some `v` have the columns `B_i v^⊤` nonzero and
pairwise non-collinear and every row `v C_i` nonzero. Then a flat direction `η` of the network
with the stream matrix `S 0` keeps `E S_0 D`, every `B_i` and every `C_i` to first order. -/
theorem flat_attention_oneBlock_keeps (S : Fin 1 → Matrix d d ℝ) (t₁ t₂ : T) (h12 : t₁ ≠ t₂)
    (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁)
    (θ : Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut)
    (hv : ∃ v : dIn → ℝ, (∀ i, attnScore θ i *ᵥ v ≠ 0)
      ∧ (∀ i j, i ≠ j → ∀ r : ℝ, attnScore θ i *ᵥ v ≠ r • (attnScore θ j *ᵥ v))
      ∧ (∀ i, v ᵥ* attnValue θ i ≠ 0))
    (η : Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut)
    (hη : η ∈ flat (Arch.attention sees id H dh) S θ) :
    η.E * S 0 * θ.D + θ.E * S 0 * η.D = 0
      ∧ ∀ i, dAttnScore θ η i = 0 ∧ dAttnValue θ η i = 0 := by
  sorry

end Skips
