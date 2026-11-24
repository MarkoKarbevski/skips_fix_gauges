import SkipsLean.OneBlock.AttentionFamily
import SkipsLean.Residual.SmallWrites
import SkipsLean.Dimension.UpperBoundAttention
import SkipsLean.Network.AttentionAnalytic

/-!
# Residual networks of attention blocks at any depth: small writes

Paper (skips paper): Lemma A.27 (Small writes), its first value, for attention blocks: "Let
`d_model ≥ 2`, let `E` and `D` have rank `d_model`, and let each block, in any order and of any
width, be an attention block with heads of width at most `d_model`, causal or not, on sequences
of at least two tokens […]. For generic parameters `θ` and a number `τ`, let
`θ_τ = (E, (W_read^ℓ, τ W_write^ℓ)_ℓ, D)`. […] For all small `τ ≠ 0`, the residual network has
`fd(θ_τ) = P − d_model² − s` (no normalization, no biases)." Its proof: "let the heads of all
attention blocks form one attention block", and for a direction that is flat for the limit `J_0`
the argument of "Part (i) for attention blocks" of Theorem B.1 gives `D_θ B_j η = 0` and
`D_θ C_j η = 0` for the heads `j` of all blocks, where `E` and `D` do not vary inside the blocks,
and `η_E D + E η_D = 0`.

Here, for `Arch.attention sees id H dh` with `L` blocks (heads `H ℓ` of width `dh ℓ` in block
`ℓ`), without normalization, with a token `t₂` that sees itself and another token `t₁`:

* `headScore θ ℓ i`, `headValue θ ℓ i`: the matrices `B = E W_Q W_K^⊤ E^⊤/√d_h` and
  `C = E W_V W_O D` of head `i` of block `ℓ`.
* `SmallWritesGenericAttention θ`: the conditions on `θ` that the proof uses.
* `smallWritesLimit_eq_zero_attention`: a direction that is flat for `J_0`
  (`smallWritesLimit`, `Residual/SmallWrites.lean`) has `η_E = E X`, `η_D = −X D`, and in every
  block the reads and the writes of the directions of the changes of basis inside the heads.
* `eventually_funDim_smallWrites_attention`: `fd(θ_τ) = P − d² − 2 ∑_ℓ H_ℓ d_{h,ℓ}²` for all
  small `τ ≠ 0`.
-/

namespace Skips

open Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {sees : T → T → Prop} [DecidableRel sees] {χ : Matrix T d ℝ → Matrix T d ℝ}
variable {H dh : Fin L → Type} [∀ ℓ, Fintype (H ℓ)] [∀ ℓ, Fintype (dh ℓ)]

/-- **The matrix `B = E W_Q W_K^⊤ E^⊤ / √d_h`** of head `i` of block `ℓ`. -/
noncomputable def headScore (θ : Params (Arch.attention sees χ H dh) dIn dOut) (ℓ : Fin L)
    (i : H ℓ) : Matrix dIn dIn ℝ :=
  (Real.sqrt (Fintype.card (dh ℓ)))⁻¹ •
    (θ.E * ((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k))
      * ((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inl k)))ᵀ * θ.Eᵀ)

/-- **The matrix `C = E W_V W_O D`** of head `i` of block `ℓ`. -/
def headValue (θ : Params (Arch.attention sees χ H dh) dIn dOut) (ℓ : Fin L) (i : H ℓ) :
    Matrix dIn dOut ℝ :=
  θ.E * ((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k)))
    * ((θ.write ℓ).submatrix (fun k : dh ℓ => (i, k)) id) * θ.D

/-- **The conditions on `θ` in Lemma A.27, for attention blocks without normalization:** `E` and
`D` have rank `d`; the query, key, value and output matrices of every head of every block have
rank `d_h`; and some `v` has the columns `B_j v^⊤` of the heads of all blocks together nonzero
and pairwise non-collinear, and every row `v C_j` nonzero. -/
structure SmallWritesGenericAttention
    (θ : Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut) : Prop where
  rank_E : θ.E.rank = Fintype.card d
  rank_D : θ.D.rank = Fintype.card d
  rank_Q : ∀ ℓ (i : H ℓ), ((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k)).rank
    = Fintype.card (dh ℓ)
  rank_K : ∀ ℓ (i : H ℓ),
    ((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inl k))).rank
      = Fintype.card (dh ℓ)
  rank_V : ∀ ℓ (i : H ℓ),
    ((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))).rank
      = Fintype.card (dh ℓ)
  rank_O : ∀ ℓ (i : H ℓ), ((θ.write ℓ).submatrix (fun k : dh ℓ => (i, k)) id).rank
    = Fintype.card (dh ℓ)
  /-- some `v` has the `B_j v^⊤` of all heads nonzero and pairwise non-collinear and every
  `v C_j` nonzero -/
  exists_v : ∃ v : dIn → ℝ, (∀ p : (Σ ℓ, H ℓ), headScore θ p.1 p.2 *ᵥ v ≠ 0)
    ∧ (∀ p q : (Σ ℓ, H ℓ), p ≠ q → ∀ r : ℝ,
        headScore θ p.1 p.2 *ᵥ v ≠ r • (headScore θ q.1 q.2 *ᵥ v))
    ∧ (∀ p : (Σ ℓ, H ℓ), v ᵥ* headValue θ p.1 p.2 ≠ 0)

/-- **Proof of Lemma A.27, attention blocks without normalization, the flat directions of
`J_0`:** let token `t₂` see itself and another token `t₁`. Under the conditions of the lemma, a
direction `η` with `(J_0 η)(x) = 0` at every input `x` has `η_E = E X` and `η_D = −X D` for one
matrix `X`, and in every block its reads and its writes are those of the directions of the
changes of basis inside the heads. -/
theorem smallWritesLimit_eq_zero_attention (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂)
    (hs1 : sees t₂ t₁) (θ : Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut)
    (hθ : SmallWritesGenericAttention θ)
    (η : Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut)
    (hη : ∀ x, smallWritesLimit (Arch.attention sees id H dh) θ η x = 0) :
    ∃ (X : Matrix d d ℝ) (Γ Γ' : ∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ),
      η.E = θ.E * X ∧ η.D = -(X * θ.D)
        ∧ (∀ ℓ, η.read ℓ = (headDirQK θ Γ + headDirVO θ Γ').read ℓ)
        ∧ (∀ ℓ, η.write ℓ = (headDirQK θ Γ + headDirVO θ Γ').write ℓ) := by
  sorry

/-- **Lemma A.27 (Small writes), first value, for attention blocks, under the conditions of its
proof:** with a token that sees itself and another token, for all small `τ ≠ 0` the residual
network has `fd(θ_τ) = P − d² − 2 ∑_ℓ H_ℓ d_{h,ℓ}²`. -/
theorem eventually_funDim_smallWrites_attention (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂)
    (hs1 : sees t₂ t₁) (θ : Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut)
    (hθ : SmallWritesGenericAttention θ) :
    ∀ᶠ τ in 𝓝[≠] (0 : ℝ),
      funDim (Arch.attention sees id H dh) 1 (θ.smallWrites τ)
          + (Fintype.card d ^ 2 + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
        = Module.finrank ℝ
            (Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut) := by
  sorry

end Skips
