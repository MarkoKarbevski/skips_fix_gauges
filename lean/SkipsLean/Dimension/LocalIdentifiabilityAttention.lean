import SkipsLean.Dimension.OrbitNetwork
import SkipsLean.Dimension.ExpOrbitAttention
import SkipsLean.Dimension.UpperBoundAttention
import SkipsLean.Network.AttentionAnalytic
import SkipsLean.OneBlock.AttentionDim
import SkipsLean.Residual.DepthAttentionDim

/-!
# Attention networks are locally identifiable up to their symmetries

Paper (dimension paper): Proposition 4.6 (The equality condition and local identifiability): "Let
the blocks be tanh, GELU, SwiGLU, GeGLU or attention blocks, without normalization or under
pre-RMSNorm. A network satisfies the equality condition if and only if, at generic parameters, it
is locally identifiable up to its symmetries. Every symmetry that is needed is then close to the
identity." Paper (skips paper):
Proposition 4.5, the same for skipless and residual networks, and Corollary 4.9 (Residual networks
are locally identifiable): "Let the blocks be analytic, with or without pre-RMSNorm, and let `θ`
be generic parameters of the residual network. Every `θ'` near `θ` with the same function is
obtained from `θ` by symmetries inside the blocks and by one matrix `G ∈ 𝒢`, all close to the
identity. The matrix `G` is the same at all hidden states".

Here, for attention blocks without normalization, whose symmetries inside the blocks are the
changes of basis inside the heads (`Params.headsQK`, `Params.headsVO`,
`Symmetry/AttentionHeads.lean`):

* the direction from the equality condition to local identifiability, at one parameter, for
  skipless networks (`fd(θ) = P − (L + 1) d² − s`) and for residual networks
  (`fd(θ) = P − d² − s`), `s = 2 ∑_ℓ H_ℓ d_{h,ℓ}²`;
* at almost every parameter: the skipless network of one attention block (Theorem 5.1 of the
  dimension paper gives its functional dimension) and the residual network of `L` attention
  blocks (Corollary 4.9 of the skips paper; Theorem 4.7 gives its functional dimension).

The twins for MLP blocks are `Dimension/LocalIdentifiability.lean`,
`Dimension/LocalIdentifiabilityGated.lean`, `Residual/LocalIdentifiability.lean` and
`Residual/LocalIdentifiabilityGated.lean`; all use `exists_mem_orbit_of_eval_eq`
(`Dimension/OrbitNetwork.lean`). Not stated here: the converse direction; pre-RMSNorm.
-/

namespace Skips

open Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {sees : T → T → Prop} [DecidableRel sees]

section AnyDepth

variable {L : ℕ} {H dh : Fin L → Type} [∀ ℓ, Fintype (H ℓ)] [∀ ℓ, Fintype (dh ℓ)]
  [∀ ℓ, DecidableEq (dh ℓ)]

/-- **Proposition 4.6 of the dimension paper for attention blocks, from the equality condition to
local identifiability, without normalization:** if `E` and the writes have rank `d`, the query and
value matrices of every head have rank `d_h` and `fd(θ) = P − (L + 1) d² − s`, then every `θ'`
near `θ` with the same function is `θ` after changes of basis inside the heads, near the identity,
and a change of basis by invertible `G_0, …, G_L` near the identity. -/
theorem exists_cob_heads_of_eval_eq_skipless_attention
    (θ : Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut)
    (hE : θ.E.rank = Fintype.card d) (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d)
    (hQ : ∀ ℓ (i : H ℓ), ((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k)).rank
      = Fintype.card (dh ℓ))
    (hV : ∀ ℓ (i : H ℓ),
      ((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))).rank
        = Fintype.card (dh ℓ))
    (hfd : funDim (Arch.attention sees id H dh) 0 θ
        + ((L + 1) * Fintype.card d ^ 2
          + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
      = Module.finrank ℝ (Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut)) :
    ∀ V ∈ 𝓝 (1 : Fin (L + 1) → Matrix d d ℝ),
      ∀ W ∈ 𝓝 (1 : ∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ), ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.attention sees id H dh) 0 θ' x
        = eval (Arch.attention sees id H dh) 0 θ x) →
        ∃ (G : Fin (L + 1) → GL d ℝ) (K K' : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ),
          (fun ℓ => (G ℓ : Matrix d d ℝ)) ∈ V
            ∧ (fun ℓ i => (K ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)) ∈ W
            ∧ (fun ℓ i => (K' ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)) ∈ W
            ∧ θ' = ((θ.headsQK K).headsVO K').cob G G := by
  sorry

/-- **Proposition 4.5 of the skips paper for residual networks of attention blocks, from the
equality condition to local identifiability, without normalization:** if `E` has rank `d`, the
query and value matrices of every head have rank `d_h` and `fd(θ) = P − d² − s`, then every `θ'`
near `θ` with the same function is `θ` after changes of basis inside the heads, near the identity,
and the change of basis by one invertible `G` near the identity at all hidden states. -/
theorem exists_cob_heads_of_eval_eq_residual_attention
    (θ : Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut)
    (hE : θ.E.rank = Fintype.card d)
    (hQ : ∀ ℓ (i : H ℓ), ((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k)).rank
      = Fintype.card (dh ℓ))
    (hV : ∀ ℓ (i : H ℓ),
      ((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))).rank
        = Fintype.card (dh ℓ))
    (hfd : funDim (Arch.attention sees id H dh) 1 θ
        + (Fintype.card d ^ 2 + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
      = Module.finrank ℝ (Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut)) :
    ∀ V ∈ 𝓝 (1 : Matrix d d ℝ), ∀ W ∈ 𝓝 (1 : ∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ),
      ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.attention sees id H dh) 1 θ' x
        = eval (Arch.attention sees id H dh) 1 θ x) →
        ∃ (G : GL d ℝ) (K K' : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ),
          (G : Matrix d d ℝ) ∈ V
            ∧ (fun ℓ i => (K ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)) ∈ W
            ∧ (fun ℓ i => (K' ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)) ∈ W
            ∧ θ' = ((θ.headsQK K).headsVO K').cob (fun _ => G) (fun _ => G) := by
  sorry

/-- **Corollary 4.9 of the skips paper for attention blocks without normalization:** for
`d_in, d_out ≥ d ≥ 2`, heads of width `1 ≤ d_h ≤ d` and a mask with a token that sees itself and
another token, at almost every parameter `θ` of the residual network, every `θ'` near `θ` with
the same function is `θ` after changes of basis inside the heads, near the identity, and the
change of basis by one invertible `G` near the identity at all hidden states. -/
theorem ae_exists_cob_heads_of_eval_eq_attention_residual
    (μ : Measure (Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ θ ∂μ, ∀ V ∈ 𝓝 (1 : Matrix d d ℝ), ∀ W ∈ 𝓝 (1 : ∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ),
      ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.attention sees id H dh) 1 θ' x
        = eval (Arch.attention sees id H dh) 1 θ x) →
        ∃ (G : GL d ℝ) (K K' : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ),
          (G : Matrix d d ℝ) ∈ V
            ∧ (fun ℓ i => (K ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)) ∈ W
            ∧ (fun ℓ i => (K' ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)) ∈ W
            ∧ θ' = ((θ.headsQK K).headsVO K').cob (fun _ => G) (fun _ => G) := by
  sorry

end AnyDepth

section OneBlock

variable {H dh : Fin 1 → Type} [∀ ℓ, Fintype (H ℓ)] [∀ ℓ, Fintype (dh ℓ)]
  [∀ ℓ, DecidableEq (dh ℓ)]

/-- **The skipless network of one attention block is locally identifiable at generic
parameters** (Proposition 4.6 with Theorem 5.1 of the dimension paper): for `d_in, d_out ≥ d ≥ 2`,
`H` heads of width `d_h ≤ d` with `H d_h ≥ d` and a mask with a token that sees itself and another
token, at almost every parameter `θ`, every `θ'` near `θ` with the same function is `θ` after
changes of basis inside the heads, near the identity, and a change of basis by invertible `G_0`,
`G_1` near the identity. -/
theorem ae_exists_cob_heads_of_eval_eq_attention_oneBlock
    (μ : Measure (Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : Fintype.card (dh 0) ≤ Fintype.card d)
    (hH : Fintype.card d ≤ Fintype.card (H 0) * Fintype.card (dh 0))
    (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ θ ∂μ, ∀ V ∈ 𝓝 (1 : Fin 2 → Matrix d d ℝ),
      ∀ W ∈ 𝓝 (1 : ∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ), ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.attention sees id H dh) 0 θ' x
        = eval (Arch.attention sees id H dh) 0 θ x) →
        ∃ (G : Fin 2 → GL d ℝ) (K K' : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ),
          (fun ℓ => (G ℓ : Matrix d d ℝ)) ∈ V
            ∧ (fun ℓ i => (K ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)) ∈ W
            ∧ (fun ℓ i => (K' ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)) ∈ W
            ∧ θ' = ((θ.headsQK K).headsVO K').cob G G := by
  sorry

end OneBlock

end Skips
