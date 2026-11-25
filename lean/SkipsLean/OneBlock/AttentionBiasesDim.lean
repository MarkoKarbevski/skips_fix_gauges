import SkipsLean.OneBlock.AttentionBiasesStepOne
import SkipsLean.OneBlock.AttentionGeneric
import SkipsLean.OneBlock.MlpBiases

/-!
# The one-block theorem for an attention block with biases: the functional dimension

Paper (skips paper), Theorem B.1: "Let `d_model ≥ 2`, let the input and output dimensions be at
least `d_model`, let inputs range over all of `ℝ^{T × d_in}`, and consider networks with one
block: […] an attention block of `H` heads of width `d_h ≤ d_model`, causal or not, on sequences
of at least two tokens. (i) Let the network have no normalization, with or without biases, and
let the block have width at least `d_model`, where the width of an attention block is `H d_h`.
For generic parameters the skipless network has functional dimension `P − 2 d_model² − s` and the
residual network `P − d_model² − s`; with biases on the embedding, the block and the readout,
counted in `P`, both values are `2 d_model` lower, and `2 d_model + 2 H d_h` lower for attention.
Both networks satisfy the equality condition, and the skip raises the functional dimension by
exactly `d_model²`." Its proof for attention blocks, Step 3: "So `dim K(θ)` is
`2 d_model² + 2 H d_h²` without the skip and `d_model² + 2 H d_h²` with it, and
`2 d_model + 2 H d_h` more with biases."

Here, for one attention block with biases (`Network/Biases.lean`: `b_E`, the read bias
`[b_Q | b_K | b_V]`, the write bias `b_O`, and `b_D`), a mask in which every token sees at least
one token, and a token `t₂` that sees itself and another token `t₁`:

* `flatB_le_range_attention_skipless`, `flatB_le_range_attention_residual`: every flat direction
  is a direction of the changes of basis and translations of the hidden states and of the
  symmetries inside the block (Steps 1 and 2 with biases);
* `funDimB_attention_oneBlock`, `funDimB_attention_oneBlock_residual`:
  `fd = P − 2 d² − 2 d − 2 H d_h² − 2 H d_h` without the skip and
  `fd = P − d² − 2 d − 2 H d_h² − 2 H d_h` with it, `P` counting the biases, under the conditions
  `OneBlockGenericAttention` on the weights;
* the same at generic weights and biases for `d_in, d_out ≥ d ≥ 2`, `d_h ≤ d`, `H d_h ≥ d`, and
  "the skip raises the functional dimension by exactly `d_model²`";
* the three statements by name for the two masks of the paper: no mask on any tokens with two
  distinct ones, and the causal mask on the tokens `0, …, n − 1`, `n ≥ 2`.

The hypothesis that every token sees at least one token holds for both masks of the paper (a
token sees itself). It is needed: with a token that sees no token the value biases moved into the
output bias are not a symmetry, and in the example of `attention_biases_check_2026-11-25.py`,
part (d), the rank of the Jacobian is higher by `H d_h = 2` (18 for 16 without the skip, 22 for
20 with it). The values themselves: part (c) of that check, 40 networks of one block.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {sees : T → T → Prop} [DecidableRel sees]
variable {H dh : Fin 1 → Type} [∀ ℓ, Fintype (H ℓ)] [∀ ℓ, Fintype (dh ℓ)]

/-- **Proof of Theorem B.1 (i) for attention blocks with biases, Steps 1 and 2, without the
skip:** under the conditions of the proof on the weights, with a token that sees itself and
another token, every flat direction of the skipless network of one attention block with biases is
the sum of the direction of two changes of basis and two translations of the hidden states and of
a direction of the symmetries inside the block. -/
theorem flatB_le_range_attention_skipless (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂)
    (hs1 : sees t₂ t₁)
    (p : ParamsB (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut)
    (hp : OneBlockGenericAttention p.1)
    (η : ParamsB (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut)
    (hη : η ∈ flatB (Arch.attention sees id H dh) 0 p) :
    ∃ (X : Fin 2 → Matrix d d ℝ) (g : Fin 2 → d → ℝ)
      (Γ Γ' : ∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) (κ ν : ∀ ℓ, H ℓ → dh ℓ → ℝ),
      η = cobDirB p X + (0, translateAtDir p.1 g) + headDirB p (Γ, Γ', κ, ν) := by
  -- Step 2 with the stream matrix `0`: `η` keeps every `B_i`, `C_i`, `β_i` and `γ`
  obtain ⟨⟨-, h⟩, hβ, hγ⟩ :=
    flatB_attention_oneBlock_keeps 0 t₁ t₂ h12 hs2 hs1 p hp.exists_v η hη
  -- Step 1
  exact exists_dirs_of_keeps_attention_biases p hp η (fun i => (h i).1) (fun i => (h i).2) hβ hγ

/-- **Proof of Theorem B.1 (i) for attention blocks with biases, Steps 1 and 2, with the skip:**
under the same conditions, every flat direction of the residual network of one attention block
with biases is the sum of the direction of one change of basis of both hidden states, of the two
translations of Lemma A.8 and of a direction of the symmetries inside the block. -/
theorem flatB_le_range_attention_residual (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂)
    (hs1 : sees t₂ t₁)
    (p : ParamsB (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut)
    (hp : OneBlockGenericAttention p.1)
    (η : ParamsB (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut)
    (hη : η ∈ flatB (Arch.attention sees id H dh) 1 p) :
    ∃ (X : Matrix d d ℝ) (g : Fin 2 → d → ℝ)
      (Γ Γ' : ∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) (κ ν : ∀ ℓ, H ℓ → dh ℓ → ℝ),
      η = cobDirB p (fun _ => X) + (0, translateDir p.1 g) + headDirB p (Γ, Γ', κ, ν) := by
  -- Step 2 with the stream matrix `1`: `η` keeps `M = E D`, every `B_i`, `C_i`, `β_i` and `γ`
  obtain ⟨⟨hM, h⟩, hβ, hγ⟩ :=
    flatB_attention_oneBlock_keeps 1 t₁ t₂ h12 hs2 hs1 p hp.exists_v η hη
  rw [Pi.one_apply, Matrix.mul_one, Matrix.mul_one] at hM
  -- Step 1
  exact exists_dirs_of_keeps_attention_biases_residual p hp η hM (fun i => (h i).1)
    (fun i => (h i).2) hβ hγ

/-- **Theorem B.1 (i) of the skips paper with biases, the skipless network, at one parameter, for
an attention block:** under the conditions `OneBlockGenericAttention` on the weights, for a mask
in which every token sees at least one token and a token that sees itself and another token, the
skipless network with biases has `fd = P − 2 d² − 2 d − 2 H d_h² − 2 H d_h`, with `P` counting
the biases. -/
theorem funDimB_attention_oneBlock (hsee : ∀ t, ∃ s, sees t s) (t₁ t₂ : T) (h12 : t₁ ≠ t₂)
    (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁)
    (p : ParamsB (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut)
    (hp : OneBlockGenericAttention p.1) :
    funDimB (Arch.attention sees id H dh) 0 p
        + (2 * Fintype.card d ^ 2 + 2 * Fintype.card d
          + (2 * (Fintype.card (H 0) * Fintype.card (dh 0) ^ 2)
            + 2 * (Fintype.card (H 0) * Fintype.card (dh 0))))
      = Module.finrank ℝ
          (ParamsB (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut) := by
  sorry

/-- **Theorem B.1 (i) of the skips paper with biases, the residual network, at one parameter,
for an attention block:** under the same conditions, the residual network with biases has
`fd = P − d² − 2 d − 2 H d_h² − 2 H d_h`, with `P` counting the biases. -/
theorem funDimB_attention_oneBlock_residual (hsee : ∀ t, ∃ s, sees t s) (t₁ t₂ : T)
    (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁)
    (p : ParamsB (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut)
    (hp : OneBlockGenericAttention p.1) :
    funDimB (Arch.attention sees id H dh) 1 p
        + (Fintype.card d ^ 2 + 2 * Fintype.card d
          + (2 * (Fintype.card (H 0) * Fintype.card (dh 0) ^ 2)
            + 2 * (Fintype.card (H 0) * Fintype.card (dh 0))))
      = Module.finrank ℝ
          (ParamsB (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut) := by
  sorry

/-- **Theorem B.1 (i) of the skips paper with biases, the skipless network, for an attention
block:** for `d_in, d_out ≥ d ≥ 2`, `H` heads of width `d_h ≤ d` with `H d_h ≥ d`, a mask in
which every token sees at least one token and a token that sees itself and another token, at
generic weights and biases the skipless network has
`fd = P − 2 d² − 2 d − 2 H d_h² − 2 H d_h`. -/
theorem ae_funDimB_attention_oneBlock (hsee : ∀ t, ∃ s, sees t s)
    (μ : Measure (ParamsB (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : Fintype.card (dh 0) ≤ Fintype.card d)
    (hH : Fintype.card d ≤ Fintype.card (H 0) * Fintype.card (dh 0))
    (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ p ∂μ, funDimB (Arch.attention sees id H dh) 0 p
        + (2 * Fintype.card d ^ 2 + 2 * Fintype.card d
          + (2 * (Fintype.card (H 0) * Fintype.card (dh 0) ^ 2)
            + 2 * (Fintype.card (H 0) * Fintype.card (dh 0))))
      = Module.finrank ℝ
          (ParamsB (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut) :=
  -- the conditions on the weights hold at generic weights, hence at generic weights and biases
  (ae_paramsB_of_forall_ae (P := fun θ => OneBlockGenericAttention θ)
    (fun ν _ => ae_oneBlockGenericAttention ν hd hdIn hdOut hdh hH) μ).mono
    fun p hp => funDimB_attention_oneBlock hsee t₁ t₂ h12 hs2 hs1 p hp

/-- **Theorem B.1 (i) of the skips paper with biases, the residual network, for an attention
block:** under the same hypotheses, at generic weights and biases the residual network has
`fd = P − d² − 2 d − 2 H d_h² − 2 H d_h`. -/
theorem ae_funDimB_attention_oneBlock_residual (hsee : ∀ t, ∃ s, sees t s)
    (μ : Measure (ParamsB (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : Fintype.card (dh 0) ≤ Fintype.card d)
    (hH : Fintype.card d ≤ Fintype.card (H 0) * Fintype.card (dh 0))
    (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ p ∂μ, funDimB (Arch.attention sees id H dh) 1 p
        + (Fintype.card d ^ 2 + 2 * Fintype.card d
          + (2 * (Fintype.card (H 0) * Fintype.card (dh 0) ^ 2)
            + 2 * (Fintype.card (H 0) * Fintype.card (dh 0))))
      = Module.finrank ℝ
          (ParamsB (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut) :=
  (ae_paramsB_of_forall_ae (P := fun θ => OneBlockGenericAttention θ)
    (fun ν _ => ae_oneBlockGenericAttention ν hd hdIn hdOut hdh hH) μ).mono
    fun p hp => funDimB_attention_oneBlock_residual hsee t₁ t₂ h12 hs2 hs1 p hp

/-- **Theorem B.1 (i) of the skips paper with biases, "the skip raises the functional dimension
by exactly `d_model²`", for an attention block:** under the same hypotheses, at generic weights
and biases. -/
theorem ae_funDimB_attention_oneBlock_residual_eq_add (hsee : ∀ t, ∃ s, sees t s)
    (μ : Measure (ParamsB (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : Fintype.card (dh 0) ≤ Fintype.card d)
    (hH : Fintype.card d ≤ Fintype.card (H 0) * Fintype.card (dh 0))
    (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ p ∂μ, funDimB (Arch.attention sees id H dh) 1 p
      = funDimB (Arch.attention sees id H dh) 0 p + Fintype.card d ^ 2 := by
  filter_upwards [ae_funDimB_attention_oneBlock hsee μ hd hdIn hdOut hdh hH t₁ t₂ h12 hs2 hs1,
    ae_funDimB_attention_oneBlock_residual hsee μ hd hdIn hdOut hdh hH t₁ t₂ h12 hs2 hs1]
    with p h0 h1
  omega

/-! ### The two masks of the paper: "causal or not, on sequences of at least two tokens" -/

/-- **Theorem B.1 (i) with biases for one attention block without a mask, the skipless
network:** on tokens with two distinct ones, at generic weights and biases
`fd = P − 2 d² − 2 d − 2 H d_h² − 2 H d_h`. -/
theorem ae_funDimB_attention_oneBlock_noMask [Nontrivial T]
    (μ : Measure (ParamsB (Arch.attention (T := T) (d := d) (fun _ _ => True) id H dh) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : Fintype.card (dh 0) ≤ Fintype.card d)
    (hH : Fintype.card d ≤ Fintype.card (H 0) * Fintype.card (dh 0)) :
    ∀ᵐ p ∂μ, funDimB (Arch.attention (fun _ _ => True) id H dh) 0 p
        + (2 * Fintype.card d ^ 2 + 2 * Fintype.card d
          + (2 * (Fintype.card (H 0) * Fintype.card (dh 0) ^ 2)
            + 2 * (Fintype.card (H 0) * Fintype.card (dh 0))))
      = Module.finrank ℝ
          (ParamsB (Arch.attention (T := T) (d := d) (fun _ _ => True) id H dh) dIn dOut) := by
  obtain ⟨t₁, t₂, h12⟩ := exists_pair_ne T
  exact ae_funDimB_attention_oneBlock (fun t => ⟨t, trivial⟩) μ hd hdIn hdOut hdh hH t₁ t₂ h12
    trivial trivial

/-- **Theorem B.1 (i) with biases for one attention block without a mask, the residual
network:** at generic weights and biases `fd = P − d² − 2 d − 2 H d_h² − 2 H d_h`. -/
theorem ae_funDimB_attention_oneBlock_residual_noMask [Nontrivial T]
    (μ : Measure (ParamsB (Arch.attention (T := T) (d := d) (fun _ _ => True) id H dh) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : Fintype.card (dh 0) ≤ Fintype.card d)
    (hH : Fintype.card d ≤ Fintype.card (H 0) * Fintype.card (dh 0)) :
    ∀ᵐ p ∂μ, funDimB (Arch.attention (fun _ _ => True) id H dh) 1 p
        + (Fintype.card d ^ 2 + 2 * Fintype.card d
          + (2 * (Fintype.card (H 0) * Fintype.card (dh 0) ^ 2)
            + 2 * (Fintype.card (H 0) * Fintype.card (dh 0))))
      = Module.finrank ℝ
          (ParamsB (Arch.attention (T := T) (d := d) (fun _ _ => True) id H dh) dIn dOut) := by
  obtain ⟨t₁, t₂, h12⟩ := exists_pair_ne T
  exact ae_funDimB_attention_oneBlock_residual (fun t => ⟨t, trivial⟩) μ hd hdIn hdOut hdh hH
    t₁ t₂ h12 trivial trivial

/-- **Theorem B.1 (i) with biases for one attention block without a mask:** the skip raises the
functional dimension by exactly `d²`, at generic weights and biases. -/
theorem ae_funDimB_attention_oneBlock_residual_eq_add_noMask [Nontrivial T]
    (μ : Measure (ParamsB (Arch.attention (T := T) (d := d) (fun _ _ => True) id H dh) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : Fintype.card (dh 0) ≤ Fintype.card d)
    (hH : Fintype.card d ≤ Fintype.card (H 0) * Fintype.card (dh 0)) :
    ∀ᵐ p ∂μ, funDimB (Arch.attention (fun _ _ => True) id H dh) 1 p
      = funDimB (Arch.attention (fun _ _ => True) id H dh) 0 p + Fintype.card d ^ 2 := by
  obtain ⟨t₁, t₂, h12⟩ := exists_pair_ne T
  exact ae_funDimB_attention_oneBlock_residual_eq_add (fun t => ⟨t, trivial⟩) μ hd hdIn hdOut
    hdh hH t₁ t₂ h12 trivial trivial

/-- **Theorem B.1 (i) with biases for one causal attention block, the skipless network:** on the
tokens `0, …, n − 1`, `n ≥ 2`, where token `t` sees the tokens `s ≤ t`, at generic weights and
biases
`fd = P − 2 d² − 2 d − 2 H d_h² − 2 H d_h`. -/
theorem ae_funDimB_attention_oneBlock_causal {n : ℕ} (hn : 2 ≤ n)
    (μ : Measure (ParamsB (Arch.attention (T := Fin n) (d := d) (fun t s => s ≤ t) id
      H dh) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : Fintype.card (dh 0) ≤ Fintype.card d)
    (hH : Fintype.card d ≤ Fintype.card (H 0) * Fintype.card (dh 0)) :
    ∀ᵐ p ∂μ, funDimB (Arch.attention (T := Fin n) (fun t s => s ≤ t) id H dh) 0 p
        + (2 * Fintype.card d ^ 2 + 2 * Fintype.card d
          + (2 * (Fintype.card (H 0) * Fintype.card (dh 0) ^ 2)
            + 2 * (Fintype.card (H 0) * Fintype.card (dh 0))))
      = Module.finrank ℝ
          (ParamsB (Arch.attention (T := Fin n) (d := d) (fun t s => s ≤ t) id H dh)
            dIn dOut) :=
  -- the second token sees itself and the first
  ae_funDimB_attention_oneBlock (sees := fun t s : Fin n => s ≤ t) (fun t => ⟨t, le_refl t⟩) μ
    hd hdIn hdOut hdh hH ⟨0, by omega⟩ ⟨1, by omega⟩ (Fin.ne_of_val_ne zero_ne_one) (le_refl _)
    (Fin.mk_le_mk.2 zero_le_one)

/-- **Theorem B.1 (i) with biases for one causal attention block, the residual network:** at
generic weights and biases `fd = P − d² − 2 d − 2 H d_h² − 2 H d_h`. -/
theorem ae_funDimB_attention_oneBlock_residual_causal {n : ℕ} (hn : 2 ≤ n)
    (μ : Measure (ParamsB (Arch.attention (T := Fin n) (d := d) (fun t s => s ≤ t) id
      H dh) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : Fintype.card (dh 0) ≤ Fintype.card d)
    (hH : Fintype.card d ≤ Fintype.card (H 0) * Fintype.card (dh 0)) :
    ∀ᵐ p ∂μ, funDimB (Arch.attention (T := Fin n) (fun t s => s ≤ t) id H dh) 1 p
        + (Fintype.card d ^ 2 + 2 * Fintype.card d
          + (2 * (Fintype.card (H 0) * Fintype.card (dh 0) ^ 2)
            + 2 * (Fintype.card (H 0) * Fintype.card (dh 0))))
      = Module.finrank ℝ
          (ParamsB (Arch.attention (T := Fin n) (d := d) (fun t s => s ≤ t) id H dh)
            dIn dOut) :=
  ae_funDimB_attention_oneBlock_residual (sees := fun t s : Fin n => s ≤ t)
    (fun t => ⟨t, le_refl t⟩) μ hd hdIn hdOut hdh hH ⟨0, by omega⟩ ⟨1, by omega⟩
    (Fin.ne_of_val_ne zero_ne_one) (le_refl _) (Fin.mk_le_mk.2 zero_le_one)

/-- **Theorem B.1 (i) with biases for one causal attention block:** the skip raises the
functional dimension by exactly `d²`, at generic weights and biases. -/
theorem ae_funDimB_attention_oneBlock_residual_eq_add_causal {n : ℕ} (hn : 2 ≤ n)
    (μ : Measure (ParamsB (Arch.attention (T := Fin n) (d := d) (fun t s => s ≤ t) id
      H dh) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : Fintype.card (dh 0) ≤ Fintype.card d)
    (hH : Fintype.card d ≤ Fintype.card (H 0) * Fintype.card (dh 0)) :
    ∀ᵐ p ∂μ, funDimB (Arch.attention (T := Fin n) (fun t s => s ≤ t) id H dh) 1 p
      = funDimB (Arch.attention (T := Fin n) (fun t s => s ≤ t) id H dh) 0 p
        + Fintype.card d ^ 2 :=
  ae_funDimB_attention_oneBlock_residual_eq_add (sees := fun t s : Fin n => s ≤ t)
    (fun t => ⟨t, le_refl t⟩) μ hd hdIn hdOut hdh hH ⟨0, by omega⟩ ⟨1, by omega⟩
    (Fin.ne_of_val_ne zero_ne_one) (le_refl _) (Fin.mk_le_mk.2 zero_le_one)

end Skips
