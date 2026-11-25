import SkipsLean.Residual.DepthAttentionGeneric
import SkipsLean.Dimension.GenericRank

/-!
# Residual networks of attention blocks at any depth: the functional dimension

Paper (skips paper): Theorem 4.7 (Equality for residual networks at any depth): "Let the blocks
be analytic, with or without pre-RMSNorm. The residual network satisfies the equality condition:
at generic parameters its functional dimension is `P − dim G − s`. So the skips raise the
functional dimension by at least `L dim G` […]." Corollary 4.10 (Attention-only transformers:
Conjecture 2.4 of Henry, 2026): "Without normalization, consider a residual network of `L`
attention blocks at generic parameters, and let `s = 2 L d_model² / H`. (i) With an embedding and
a readout, its functional dimension is `P − d_model² − s`." Lemma A.27, first value, at generic
parameters.

Here, for attention blocks without normalization, heads of width `1 ≤ d_h ≤ d` (any numbers of
heads; `s = 2 ∑_ℓ H_ℓ d_{h,ℓ}²`), `d_in, d_out ≥ d ≥ 2`, and a mask with a token that sees
itself and another token (two tokens at least; causal or not):

* `ae_eventually_funDim_smallWrites_attention`: Lemma A.27, first value, at almost every `θ`;
* `ae_funDim_attention_residual`: Theorem 4.7 for attention blocks without normalization,
  `fd = P − d² − s` at almost every parameter;
* `ae_funDim_attention_residual_ge_add`: the skips raise the functional dimension by at least
  `L d²`, when every block has total width `H d_h ≥ d`;
* `ae_funDim_attention_residual_of_width`: Corollary 4.10 (i) in the setting of the main text,
  `H` heads of total width `H d_h = d` in every block, with `s = 2 L d² / H`.
Not stated here: Corollary 4.10 (ii) (without an embedding and a readout:
`Residual/BlocksAloneAttention.lean`); pre-RMSNorm (`Residual/DepthAttentionRMSDim.lean`).
-/

namespace Skips

open Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {sees : T → T → Prop} [DecidableRel sees]
variable {H dh : Fin L → Type} [∀ ℓ, Fintype (H ℓ)] [∀ ℓ, Fintype (dh ℓ)]

/-- **Lemma A.27 (Small writes), first value, for attention blocks:** for generic parameters `θ`
and all small `τ ≠ 0`, the residual network has `fd(θ_τ) = P − d² − 2 ∑_ℓ H_ℓ d_{h,ℓ}²`. -/
theorem ae_eventually_funDim_smallWrites_attention
    (μ : Measure (Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ θ ∂μ, ∀ᶠ τ in 𝓝[≠] (0 : ℝ),
      funDim (Arch.attention sees id H dh) 1 (θ.smallWrites τ)
          + (Fintype.card d ^ 2 + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
        = Module.finrank ℝ
            (Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut) := by
  filter_upwards [ae_smallWritesGenericAttention μ hd hdIn hdOut hdh hdh0] with θ hθ
  exact eventually_funDim_smallWrites_attention t₁ t₂ h12 hs2 hs1 θ hθ

/-- **Theorem 4.7 of the skips paper for attention blocks without normalization:** with
`d_in, d_out ≥ d ≥ 2`, `L` attention blocks with heads of width `1 ≤ d_h ≤ d`, and a token that
sees itself and another token, at almost every parameter the residual network has the functional
dimension `P − d² − 2 ∑_ℓ H_ℓ d_{h,ℓ}²`. -/
theorem ae_funDim_attention_residual
    (μ : Measure (Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ θ ∂μ, funDim (Arch.attention sees id H dh) 1 θ
        + (Fintype.card d ^ 2 + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
      = Module.finrank ℝ (Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut) := by
  classical
  -- one parameter `θ₀` with the conditions of Lemma A.27, and one small `τ ≠ 0`:
  -- `fd(θ₀_τ) = P - d² - s`
  obtain ⟨θ₀, hθ₀⟩ := (ae_smallWritesGenericAttention μ hd hdIn hdOut hdh hdh0).exists
  obtain ⟨τ, hτ⟩ := (eventually_funDim_smallWrites_attention t₁ t₂ h12 hs2 hs1 θ₀ hθ₀).exists
  -- at almost every `θ`, `fd(θ) ≥ fd(θ₀_τ)` (analytic outputs) and `fd(θ) ≤ P - d² - s`
  filter_upwards [ae_funDim_ge (Arch.attention sees id H dh) 1
      (fun ℓ => analyticOnNhd_f_attention sees id H dh ℓ) analyticOnNhd_id μ (θ₀.smallWrites τ),
    ae_funDim_add_le_residual_attention μ hdIn hdh] with θ h1 h2
  omega

/-- **Theorem 4.7, the gain, for attention blocks without normalization:** if moreover every
block has total width `H d_h ≥ d`, at almost every parameter the skips raise the functional
dimension by at least `L d²`. -/
theorem ae_funDim_attention_residual_ge_add
    (μ : Measure (Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (hH : ∀ ℓ, Fintype.card d ≤ Fintype.card (H ℓ) * Fintype.card (dh ℓ))
    (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ θ ∂μ, funDim (Arch.attention sees id H dh) 0 θ + L * Fintype.card d ^ 2
      ≤ funDim (Arch.attention sees id H dh) 1 θ := by
  classical
  -- `fd₁ = P - d² - s` and `fd₀ ≤ P - (L + 1) d² - s`
  filter_upwards [ae_funDim_attention_residual μ hd hdIn hdOut hdh hdh0 t₁ t₂ h12 hs2 hs1,
    ae_funDim_add_le_skipless_attention μ hdIn hdh hH] with θ h1 h2
  rw [add_one_mul] at h2
  omega

/-- **Corollary 4.10 (i) of the skips paper (attention-only transformers):** without
normalization, with `d_in, d_out ≥ d ≥ 2` and `L` attention blocks of `Hn` heads each, of total
width `H d_h = d`, on a mask with a token that sees itself and another token: at almost every
parameter the residual network has the functional dimension `P − d² − s`, `s = 2 L d² / H`. -/
theorem ae_funDim_attention_residual_of_width (Hn : ℕ)
    (μ : Measure (Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hHn : ∀ ℓ, Fintype.card (H ℓ) = Hn)
    (hHd : ∀ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) = Fintype.card d)
    (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ θ ∂μ, funDim (Arch.attention sees id H dh) 1 θ
        + (Fintype.card d ^ 2 + 2 * L * Fintype.card d ^ 2 / Hn)
      = Module.finrank ℝ (Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut) := by
  -- every block has heads of width `1 ≤ d_h ≤ d`, since `H d_h = d ≥ 2`
  have hpos : ∀ ℓ, 0 < Fintype.card (H ℓ) ∧ 0 < Fintype.card (dh ℓ) := fun ℓ => by
    have h : 0 < Fintype.card (H ℓ) * Fintype.card (dh ℓ) := by rw [hHd ℓ]; omega
    exact ⟨Nat.pos_of_mul_pos_right h, Nat.pos_of_mul_pos_left h⟩
  have hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d := fun ℓ =>
    hHd ℓ ▸ Nat.le_mul_of_pos_left _ (hpos ℓ).1
  -- `s = 2 ∑_ℓ H d_h² = 2 L d² / H`
  have hs : 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
      = 2 * L * Fintype.card d ^ 2 / Hn := by
    rcases Nat.eq_zero_or_pos L with hL | hL
    · subst hL
      simp
    have hHn0 : 0 < Hn := hHn ⟨0, hL⟩ ▸ (hpos ⟨0, hL⟩).1
    -- each block: `H d_h² = d² / H`, as `d² = (H d_h²) H`
    have hterm : ∀ ℓ, Fintype.card d ^ 2
        = Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2 * Hn := fun ℓ => by
      rw [← hHd ℓ, ← hHn ℓ]
      ring
    have hdvd : Hn ∣ Fintype.card d ^ 2 := Dvd.intro_left _ (hterm ⟨0, hL⟩).symm
    rw [Finset.sum_congr rfl fun ℓ _ => (Nat.div_eq_of_eq_mul_left hHn0 (hterm ℓ)).symm,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
      Nat.mul_div_assoc _ hdvd, mul_assoc]
  rw [← hs]
  exact ae_funDim_attention_residual μ hd hdIn hdOut hdh (fun ℓ => (hpos ℓ).2) t₁ t₂ h12 hs2 hs1

end Skips
