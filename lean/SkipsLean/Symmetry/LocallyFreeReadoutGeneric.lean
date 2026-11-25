import SkipsLean.Symmetry.LocallyFreeReadout
import SkipsLean.Generic.Params
import SkipsLean.Generic.Gated

/-!
# Locally free action at generic parameters (the form with the readout)

Paper (skips paper), Lemma A.18 (Locally free action): "The same holds if the readout has rank
`d_model` and every block has width at least `d_model`", where "the same" is "at generic
parameters the changes of basis and the symmetries inside blocks act locally freely". Its proof:
"rescalings act freely on the rows of a generic write […]; each read, of rank `d_model` and with
generic columns, then forces `G_{ℓ−1} = I` and the remaining scales to be 1."

`Symmetry/LocallyFreeReadout.lean` states, at one parameter with rank conditions, that changes of
basis and rescalings that fix `θ` are the identity. Here the same **at almost every `θ`**, for
`d_out ≥ d ≥ 1` and blocks of width at least `d` (`Symmetry/LocallyFreeGeneric.lean` has the form
with the embedding, for `d_in ≥ d`). The conditions at generic parameters are stated first, the
twins of `ae_rank_E_write`, `ae_read_col_ne_zero`:

* `ae_rank_D_read`: `D` and every read have rank `d` (`d_out ≥ d`, reads with at least `d`
  columns);
* `ae_write_row_ne_zero`: no row of a write is zero (`d ≥ 1`);
* `ae_read_cols_generalPosition`: any `d` columns of a read are linearly independent (reads with
  at least `d` columns), from `ae_isUnit_det_submatrix`.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {σ : ℝ → ℝ} {χ : Matrix T d ℝ → Matrix T d ℝ} {hid : Fin L → Type}
  [∀ ℓ, Fintype (hid ℓ)]

/-- At generic parameters `D` and every read have rank `d`, when `d_out ≥ d` and every read has
at least `d` columns (the twin of `ae_rank_E_write`). -/
theorem ae_rank_D_read {A : Arch T d L} (μ : Measure (Params A dIn dOut)) [μ.IsAddHaarMeasure]
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hr : ∀ ℓ, Fintype.card d ≤ Fintype.card (A.r ℓ)) :
    ∀ᵐ θ ∂μ, θ.D.rank = Fintype.card d ∧ ∀ ℓ, (θ.read ℓ).rank = Fintype.card d := by
  sorry

/-- At generic parameters no row of a write vanishes (`d ≥ 1`; any kind of block). -/
theorem ae_write_row_ne_zero [Nonempty d] {A : Arch T d L} (μ : Measure (Params A dIn dOut))
    [μ.IsAddHaarMeasure] : ∀ᵐ θ ∂μ, ∀ ℓ i, (fun a => θ.write ℓ i a) ≠ 0 := by
  sorry

/-- At generic parameters the columns of every read are in general position: any `d` of them
are linearly independent, when the read has at least `d` columns. -/
theorem ae_read_cols_generalPosition {A : Arch T d L} (μ : Measure (Params A dIn dOut))
    [μ.IsAddHaarMeasure] (hr : ∀ ℓ, Fintype.card d ≤ Fintype.card (A.r ℓ)) :
    ∀ᵐ θ ∂μ, ∀ ℓ (S : Finset (A.r ℓ)), S.card ≤ Fintype.card d →
      LinearIndependent ℝ fun j : S => (θ.read ℓ)ᵀ (j : A.r ℓ) := by
  sorry

/-- **Lemma A.18, second sentence, at generic parameters, the changes of basis** (any kind of
block whose read has at least `d` columns; `d_out ≥ d`): at almost every `θ`, changes of basis
that fix `θ` (`θ.cob G K = θ`) have `K = 1`. -/
theorem ae_cob_eq_self_of_dOut {A : Arch T d L} (μ : Measure (Params A dIn dOut))
    [μ.IsAddHaarMeasure] (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hr : ∀ ℓ, Fintype.card d ≤ Fintype.card (A.r ℓ)) :
    ∀ᵐ θ ∂μ, ∀ G K : Fin (L + 1) → GL d ℝ, θ.cob G K = θ → K = 1 := by
  sorry

/-- **Lemma A.18, second sentence, at generic parameters, ReLU and ReLU² blocks** (any
activation, degree `k ≠ 0`; `d_out ≥ d ≥ 1`, at least `d` hidden units): at almost every `θ`,
changes of basis `G` with positive rescalings `c` of the hidden units that fix `θ` are the
identity. -/
theorem ae_cob_rescaleMlp_eq_self_of_dOut [Nonempty d] (k : ℕ) (hk : k ≠ 0)
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) σ χ hid) dIn dOut)) [μ.IsAddHaarMeasure]
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hw : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, ∀ (G : Fin (L + 1) → GL d ℝ) (c : ∀ ℓ, hid ℓ → ℝ), (∀ ℓ i, 0 < c ℓ i) →
      (θ.cob G G).rescaleMlp k c = θ → G = 1 ∧ ∀ ℓ i, c ℓ i = 1 := by
  sorry

/-- **Lemma A.18, second sentence, at generic parameters, gated blocks with any gate**
(`d_out ≥ d ≥ 1`, at least `d` hidden units): at almost every `θ`, changes of basis `G` with
rescalings `c` of the values that fix `θ` are the identity. -/
theorem ae_cob_rescale_eq_self_of_dOut [Nonempty d]
    (μ : Measure (Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut)) [μ.IsAddHaarMeasure]
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hw : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, ∀ (G : Fin (L + 1) → GL d ℝ) (c : ∀ ℓ, hid ℓ → ℝ),
      (θ.cob G G).rescale c = θ → G = 1 ∧ ∀ ℓ i, c ℓ i = 1 := by
  sorry

/-- **Lemma A.18, second sentence, at generic parameters, ReGLU blocks** (any gate and any degree
`k`; `d_out ≥ d ≥ 1`, at least `d` hidden units): at almost every `θ`, changes of basis `G` with
rescalings `c'` of the values and positive rescalings `c` of the gates that fix `θ` are the
identity. -/
theorem ae_cob_rescale_rescaleGate_eq_self_of_dOut [Nonempty d] (k : ℕ)
    (μ : Measure (Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut)) [μ.IsAddHaarMeasure]
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hw : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, ∀ (G : Fin (L + 1) → GL d ℝ) (c c' : ∀ ℓ, hid ℓ → ℝ), (∀ ℓ i, 0 < c ℓ i) →
      ((θ.cob G G).rescale c').rescaleGate k c = θ →
        G = 1 ∧ (∀ ℓ i, c ℓ i = 1) ∧ ∀ ℓ i, c' ℓ i = 1 := by
  sorry

/-- **Lemma A.18, second sentence, at generic parameters, under pre-RMSNorm with `ε = 0`** (any
kind of block whose read has at least `d` columns and whose write has a row; `d_out ≥ d ≥ 1`,
`d_in ≥ 1`): at almost every `θ`, changes of basis `G_ℓ = c_ℓ Q_ℓ` (the writes multiplied by
`G_ℓ`, the reads by `Q_ℓ⁻¹`) that fix `θ` have `c_ℓ = 1` and `Q_ℓ = 1`. -/
theorem ae_cob_rmsNorm_zero_eq_self_of_dOut [Nonempty d] [Nonempty dIn] {A : Arch T d L}
    (μ : Measure (Params A dIn dOut)) [μ.IsAddHaarMeasure]
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hr : ∀ ℓ, Fintype.card d ≤ Fintype.card (A.r ℓ)) (hw : ∀ ℓ, Nonempty (A.w ℓ)) :
    ∀ᵐ θ ∂μ, ∀ (G Q : Fin (L + 1) → GL d ℝ) (c : Fin (L + 1) → ℝ),
      (∀ ℓ, (G ℓ : Matrix d d ℝ) = c ℓ • (Q ℓ : Matrix d d ℝ)) → θ.cob G Q = θ →
        (∀ ℓ, c ℓ = 1) ∧ Q = 1 := by
  sorry

end Skips
