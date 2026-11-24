import SkipsLean.Dimension.UpperBound
import SkipsLean.Dimension.UpperBoundRMSNorm
import SkipsLean.Dimension.Rescaling
import SkipsLean.Dimension.GenericRank
import SkipsLean.Generic.Params
import SkipsLean.Generic.Gated

/-!
# Skipless networks: the changes of basis at the first and at the last hidden state

Paper (skips paper): proof of Theorem A.28 (i) and (ii). "In a skipless network of the same
widths, with embedding `E'` and readout `D'`, the changes of basis at `h_0` and `h_L`, those inside
the heads and the rescalings have orbits of dimension `2 d² + s` at generic parameters, where `E'`
and `D'` have rank `d` […]. Under pre-RMSNorm with `ε > 0` […] the orthogonal changes of basis at
`h_0` and `h_L`, which commute with the normalization, have orbits of dimension `d (d - 1) + s` in
the skipless network." And the proof of Lemma A.26: "So the Jacobian of `G_X` has rank at most
`r₀ = P' - k`; the rank is lower semicontinuous, so the bound holds at every `η`."

Here: a skipless network of `L ≥ 1` blocks of ANY widths (a block may have fewer than `d` hidden
units, so the changes of basis at the hidden states in between are not used). The directions are
`cobDir θ X` with `X` supported on the first and the last hidden state, and `rescaleDir θ α` for
gated blocks (`s` = the number of gated units; `s = 0` for MLP blocks such as `tanh` and GELU).

* `funDim_add_le_skipless_ends…`: the bound on the functional dimension where `E` and `D` have
  rank `d` (and, for gated blocks, no value column of a read vanishes).
* `jacobianRank_add_le_skipless_ends…`: the same bound for the rank of the Jacobian on every batch
  at EVERY parameter, for real-analytic blocks.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]

section General

variable {A : Arch T d L}

/-- **Proof of Theorem A.28 (ii) of the skips paper, "the changes of basis at `h_0` and `h_L`",
without normalization:** for a skipless network of `L ≥ 1` blocks of any widths whose `E` and `D`
have rank `d`, the functional dimension is at most `P - 2 d²`. -/
theorem funDim_add_le_skipless_ends (hA : A.χ = id) (hf : ∀ ℓ, Differentiable ℝ (A.f ℓ))
    (hL : 0 < L) (θ : Params A dIn dOut) (hE : θ.E.rank = Fintype.card d)
    (hD : θ.D.rank = Fintype.card d) :
    funDim A 0 θ + 2 * Fintype.card d ^ 2 ≤ Module.finrank ℝ (Params A dIn dOut) := by
  sorry

/-- **The same bound at every parameter, on every batch** (proof of Lemma A.26: "the rank is lower
semicontinuous, so the bound holds at every `η`"): for real-analytic blocks, `d_in, d_out ≥ d` and
`L ≥ 1`, the Jacobian of the outputs of a skipless network on a batch has rank at most `P - 2 d²`
at every parameter. -/
theorem jacobianRank_add_le_skipless_ends (hA : A.χ = id)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (hL : 0 < L)
    (hdIn : Fintype.card d ≤ Fintype.card dIn) (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (θ : Params A dIn dOut) {n : ℕ} (X : Fin n → Matrix T dIn ℝ) :
    jacobianRank A 0 X θ + 2 * Fintype.card d ^ 2 ≤ Module.finrank ℝ (Params A dIn dOut) := by
  sorry

/-- **Proof of Theorem A.28 (ii), "the orthogonal changes of basis at `h_0` and `h_L`", under
pre-RMSNorm with `ε > 0`:** for a skipless network of `L ≥ 1` blocks of any widths whose `E` and
`D` have rank `d`, the functional dimension is at most `P - d (d - 1)`. -/
theorem funDim_add_le_skipless_ends_rmsNorm {ε : ℝ} (hε : 0 < ε) (hA : A.χ = rmsNorm ε)
    (hf : ∀ ℓ, Differentiable ℝ (A.f ℓ)) (hL : 0 < L) (θ : Params A dIn dOut)
    (hE : θ.E.rank = Fintype.card d) (hD : θ.D.rank = Fintype.card d) :
    funDim A 0 θ + Fintype.card d * (Fintype.card d - 1)
      ≤ Module.finrank ℝ (Params A dIn dOut) := by
  sorry

/-- **The same bound at every parameter, on every batch, under pre-RMSNorm with `ε > 0`:** for
real-analytic blocks, `d_in, d_out ≥ d` and `L ≥ 1`, the Jacobian of the outputs of a skipless
network on a batch has rank at most `P - d (d - 1)` at every parameter. -/
theorem jacobianRank_add_le_skipless_ends_rmsNorm {ε : ℝ} (hε : 0 < ε) (hA : A.χ = rmsNorm ε)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (hL : 0 < L)
    (hdIn : Fintype.card d ≤ Fintype.card dIn) (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (θ : Params A dIn dOut) {n : ℕ} (X : Fin n → Matrix T dIn ℝ) :
    jacobianRank A 0 X θ + Fintype.card d * (Fintype.card d - 1)
      ≤ Module.finrank ℝ (Params A dIn dOut) := by
  sorry

end General

section Gated

variable {σ : ℝ → ℝ} {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]

/-- **Proof of Theorem A.28 (ii), "the changes of basis at `h_0` and `h_L` […] and the
rescalings", for gated blocks without normalization:** for a skipless network of `L ≥ 1` gated
blocks of any widths whose `E` and `D` have rank `d` and whose reads have no vanishing value
column, the functional dimension is at most `P - 2 d² - s`, with `s` the number of hidden
units. -/
theorem funDim_add_le_skipless_ends_gated
    (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) (hσ : Differentiable ℝ σ)
    (hL : 0 < L) (hE : θ.E.rank = Fintype.card d) (hD : θ.D.rank = Fintype.card d)
    (hv : ∀ ℓ i, (fun k => θ.read ℓ k (Sum.inr i)) ≠ 0) :
    funDim (Arch.gated σ id hid) 0 θ + (2 * Fintype.card d ^ 2 + ∑ ℓ, Fintype.card (hid ℓ))
      ≤ Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) := by
  sorry

/-- **The same bound at every parameter, on every batch, for gated blocks without
normalization:** for a real-analytic gate, `d_in, d_out ≥ d ≥ 1` and `L ≥ 1`, the Jacobian of the
outputs of a skipless network of gated blocks on a batch has rank at most `P - 2 d² - s` at every
parameter. -/
theorem jacobianRank_add_le_skipless_ends_gated [Nonempty d] (hσ : AnalyticOnNhd ℝ σ Set.univ)
    (hL : 0 < L) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) {n : ℕ}
    (X : Fin n → Matrix T dIn ℝ) :
    jacobianRank (Arch.gated σ id hid) 0 X θ
        + (2 * Fintype.card d ^ 2 + ∑ ℓ, Fintype.card (hid ℓ))
      ≤ Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) := by
  sorry

/-- **For gated blocks under pre-RMSNorm with `ε > 0`:** for a skipless network of `L ≥ 1` gated
blocks of any widths whose `E` and `D` have rank `d` and whose reads have no vanishing value
column, the functional dimension is at most `P - d (d - 1) - s`. -/
theorem funDim_add_le_skipless_ends_gated_rmsNorm {ε : ℝ} (hε : 0 < ε)
    (θ : Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)
    (hσ : Differentiable ℝ σ) (hL : 0 < L) (hE : θ.E.rank = Fintype.card d)
    (hD : θ.D.rank = Fintype.card d) (hv : ∀ ℓ i, (fun k => θ.read ℓ k (Sum.inr i)) ≠ 0) :
    funDim (Arch.gated σ (rmsNorm ε) hid) 0 θ
        + (Fintype.card d * (Fintype.card d - 1) + ∑ ℓ, Fintype.card (hid ℓ))
      ≤ Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut) := by
  sorry

/-- **The same bound at every parameter, on every batch, for gated blocks under pre-RMSNorm with
`ε > 0`:** for a real-analytic gate, `d_in, d_out ≥ d ≥ 1` and `L ≥ 1`, the Jacobian of the outputs
of a skipless network of gated blocks on a batch has rank at most `P - d (d - 1) - s` at every
parameter. -/
theorem jacobianRank_add_le_skipless_ends_gated_rmsNorm [Nonempty d] {ε : ℝ} (hε : 0 < ε)
    (hσ : AnalyticOnNhd ℝ σ Set.univ) (hL : 0 < L) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (θ : Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut) {n : ℕ}
    (X : Fin n → Matrix T dIn ℝ) :
    jacobianRank (Arch.gated σ (rmsNorm ε) hid) 0 X θ
        + (Fintype.card d * (Fintype.card d - 1) + ∑ ℓ, Fintype.card (hid ℓ))
      ≤ Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut) := by
  sorry

end Gated

end Skips
