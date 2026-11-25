import SkipsLean.Residual.FewerHiddenUnits

/-!
# Too few extra hidden units: skipless blocks with fewer than `d` hidden units

Paper (skips paper), Theorem A.28 (iii): "Too few extra hidden units. For GELU blocks with an
embedding and a readout, without normalization, and almost every choice of weights, a residual
network of `L` blocks equals no skipless network of `L` blocks with, in total, fewer than
`L d_model / 2` more hidden units."

Its proof begins with the skipless networks that have a block with fewer than `d_model` hidden
units: "If some `d'_hidden,ℓ < d_model`, the hidden state `h_ℓ` of the skipless network lies in a
subspace of dimension `d'_hidden,ℓ`, so the Jacobian of its output with respect to the input has
rank below `d_model` at every input. That of the residual network is `ED + O(τ)` at the parameters
`θ_τ` of Lemma A.27, of rank `d_model` for small `τ`, so by analyticity it has rank `d_model` at
some input for almost every choice of weights, and the two networks differ. So let every
`d'_hidden,ℓ ≥ d_model`."

`Residual/FewerHiddenUnits.lean` has the theorem for skipless blocks of at least `d` hidden units
(the setting of the main text). Here the first case of the proof, and then the theorem for all
widths.

* `inputRank`: the rank of the Jacobian of the output with respect to the input. An input has the
  tokens `T`, and an MLP block acts on every token, so the paper's ranks `d'_hidden,ℓ` and
  `d_model`, which are for one token, are `|T| d'_hidden,ℓ` and `|T| d_model` here.
* `inputRank_skipless_le`: in a network without skips the output is a function of the outputs of
  the hidden units of block `ℓ`, so the rank is at most `|T|` times their number. Stated for every
  kind of block with a differentiable fixed map; the number is that of the rows of the write.
* `le_inputRank_residual_mlp_zero`, `ae_le_inputRank_residual_mlp_zero`: the residual network.
  The paper takes the parameters `θ_τ` and analyticity in the weights. Here the input `0`: when
  `σ(0) = 0` (GELU), every hidden state vanishes there, and the Jacobian at `0` is
  `v ↦ v E ∏_ℓ (I + σ'(0) W_read^ℓ W_write^ℓ) D`, polynomial in the weights. It has rank
  `|T| d` when `E` and `D` have rank `d` and every factor is invertible, which holds at generic
  parameters when `d_in, d_out ≥ d`.
* `ae_forall_eval_residual_ne_skipless_of_card_lt`: so at generic parameters the residual network
  computes the function of no network without skips that has a block with fewer than `d` rows in
  its write, of any depth and with any differentiable blocks.
* `ae_forall_all_widths_eval_residual_ne_skipless_gelu`: Theorem A.28 (iii) as the paper states
  it, for all widths of the skipless network, under Sard's theorem (which the case of widths at
  least `d` uses, `Literature/Sard.lean`).

Theorem A.28 (iv) is stated in the paper only for skipless networks whose blocks all have at least
`d_model` hidden units (`ae_not_isPointwiseLimit_skipless_gelu_widths`).

Numeric check of the Jacobian at `0` and of the rank bound:
`narrow_skipless_input_rank_check_2026-11-25.py`.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [Fintype dIn] [Fintype dOut]

/-- The rank of the Jacobian of the output `x ↦ F_θ(x)` with respect to the input, at the input
`x`. -/
noncomputable def inputRank (A : Arch T d L) (S : Fin L → Matrix d d ℝ) (θ : Params A dIn dOut)
    (x : Matrix T dIn ℝ) : ℕ :=
  Module.finrank ℝ (LinearMap.range (fderiv ℝ (eval A S θ) x).toLinearMap)

/-- **Theorem A.28 (iii) of the skips paper, "the hidden state `h_ℓ` of the skipless network lies
in a subspace of dimension `d'_hidden,ℓ`, so the Jacobian of its output with respect to the input
has rank below `d_model` at every input":** in a network without skips whose blocks and whose map
`χ` are differentiable, the Jacobian of the output with respect to the input has, at every input
and for every block `ℓ`, rank at most `|T|` times the number of rows of the write of block `ℓ`
(for an MLP block, the number of its hidden units). -/
theorem inputRank_skipless_le {A : Arch T d L} (hf : ∀ ℓ, Differentiable ℝ (A.f ℓ))
    (hχ : Differentiable ℝ A.χ) (θ : Params A dIn dOut) (x : Matrix T dIn ℝ) (ℓ : Fin L) :
    inputRank A 0 θ x ≤ Fintype.card T * Fintype.card (A.w ℓ) := by
  sorry

variable [DecidableEq d] {σ : ℝ → ℝ} {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]

/-- **The Jacobian of a residual network of MLP blocks with respect to the input, at the input
`0`, at one parameter:** if `σ(0) = 0` and `σ` is differentiable at `0`, every hidden state
vanishes at the input `0`, and the Jacobian there is
`v ↦ v E ∏_ℓ (I + σ'(0) W_read^ℓ W_write^ℓ) D`. So if `E` and `D` have rank `d` and every
`I + σ'(0) W_read^ℓ W_write^ℓ` is invertible, it has rank at least `|T| d`. -/
theorem le_inputRank_residual_mlp_zero (hσ0 : σ 0 = 0) (hσ : DifferentiableAt ℝ σ 0)
    (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d) (hD : θ.D.rank = Fintype.card d)
    (hu : ∀ ℓ, IsUnit (1 + deriv σ 0 • (θ.read ℓ * θ.write ℓ)).det) :
    Fintype.card T * Fintype.card d ≤ inputRank (Arch.mlp σ id hid) 1 θ 0 := by
  sorry

/-- **Theorem A.28 (iii) of the skips paper, "it has rank `d_model` at some input for almost every
choice of weights", for MLP blocks whose activation has `σ(0) = 0` and is differentiable at `0`:**
with `d_in, d_out ≥ d`, at generic parameters of the residual network the Jacobian of the output
with respect to the input has rank at least `|T| d` at the input `0`. -/
theorem ae_le_inputRank_residual_mlp_zero (hσ0 : σ 0 = 0) (hσ : DifferentiableAt ℝ σ 0)
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, Fintype.card T * Fintype.card d ≤ inputRank (Arch.mlp σ id hid) 1 θ 0 := by
  sorry

/-- **Theorem A.28 (iii) of the skips paper, "If some `d'_hidden,ℓ < d_model` […] the two networks
differ", for MLP blocks whose activation has `σ(0) = 0` and is differentiable at `0`:** with
`d_in, d_out ≥ d` and at least one token, at generic parameters the residual network computes the
function of no network without skips, of any depth `L'` and with any differentiable blocks and
map `χ`, that has a block with fewer than `d` rows in its write (for an MLP block: fewer than `d`
hidden units). -/
theorem ae_forall_eval_residual_ne_skipless_of_card_lt [Nonempty T] (hσ0 : σ 0 = 0)
    (hσ : DifferentiableAt ℝ σ 0)
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, ∀ (L' : ℕ) (A' : Arch T d L'), (∀ ℓ, Differentiable ℝ (A'.f ℓ)) →
      Differentiable ℝ A'.χ → (∃ ℓ, Fintype.card (A'.w ℓ) < Fintype.card d) →
      ∀ η : Params A' dIn dOut, eval (Arch.mlp σ id hid) 1 θ ≠ eval A' 0 η := by
  sorry

/-- **Theorem A.28 (iii) of the skips paper, given Sard's theorem:** for GELU blocks without
normalization and `d_in, d_out ≥ d ≥ 2`, with at least one token, at generic parameters of the
residual network with the hidden units `hid ℓ`, for all widths `m_1, …, m_L` with
`2 ∑_ℓ m_ℓ < 2 ∑_ℓ d_hidden,ℓ + L d` ("in total, fewer than `L d_model / 2` more hidden units"),
no skipless network of GELU blocks of the widths `m` computes the function of the residual
network. (For widths `m_ℓ ≥ d` this is `ae_forall_widths_eval_residual_ne_skipless_gelu`; a
skipless network with some `m_ℓ < d` differs whatever its number of hidden units is.) -/
theorem ae_forall_all_widths_eval_residual_ne_skipless_gelu [Nonempty T]
    (hSard : ∀ (m : Fin L → ℕ) (r : ℕ), SardCriticalValues
      (Params (Arch.mlp (T := T) (d := d) gelu id (fun ℓ => Fin (m ℓ))) dIn dOut) (Fin r → ℝ))
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) gelu id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, ∀ m : Fin L → ℕ,
      2 * ∑ ℓ, m ℓ < 2 * ∑ ℓ, Fintype.card (hid ℓ) + L * Fintype.card d →
      ∀ η : Params (Arch.mlp (T := T) (d := d) gelu id (fun ℓ => Fin (m ℓ))) dIn dOut,
        eval (Arch.mlp gelu id hid) 1 θ ≠ eval (Arch.mlp gelu id (fun ℓ => Fin (m ℓ))) 0 η := by
  -- the two cases of the paper's proof: every width at least `d`, or some width below `d`
  have h1 := ae_forall_widths_eval_residual_ne_skipless_gelu (hid := hid) hSard μ hd hdIn hdOut
  have h2 := ae_forall_eval_residual_ne_skipless_of_card_lt (hid := hid)
    (show gelu 0 = 0 by rw [gelu, zero_mul]) (hasDerivAt_gelu 0).differentiableAt μ hdIn hdOut
  filter_upwards [h1, h2] with θ hθ1 hθ2 m hm η
  by_cases hw : ∀ ℓ, Fintype.card d ≤ m ℓ
  · exact hθ1 m hw hm η
  · obtain ⟨ℓ, hℓ⟩ := not_forall.mp hw
    exact hθ2 L (Arch.mlp gelu id (fun ℓ => Fin (m ℓ)))
      (fun ℓ => differentiableOn_univ.mp
        (analyticOnNhd_f_mlp analyticOnNhd_gelu ℓ).differentiableOn)
      differentiable_id
      ⟨ℓ, by show Fintype.card (Fin (m ℓ)) < Fintype.card d; simpa using hℓ⟩ η

end Skips
