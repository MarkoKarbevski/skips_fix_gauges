import SkipsLean.Depth.GeluZero

/-!
# Theorem 5.2 (ii) for GELU blocks at `ε = 0`, with a batch of inputs in the domain

Paper (dimension paper): Theorem 5.2 (ii), the case `ε = 0`, and Appendix D.7, "The case (0)":
"By Proposition D.4 there is a finite batch `X*`, with `xE ≠ 0` for all its inputs, on which the
Jacobian at `θ*` has the rank (13). By (R2), `θ* ∈ O_{X*}`. […] Hence the rank on `X*` is at least
(13) at almost every parameter."

For `ε = 0` the paper's network is defined at an input when no row of a hidden state vanishes, and
its functional dimension is the largest rank over the finite batches of such inputs. Lean's
`funDim` is that of the total network (`rmsRow 0 0 = 0`) and is at least the paper's value.
`Depth/GeluZero.lean` gives the value of `funDim` at almost every parameter. Stated here: one finite
batch `X` of inputs without a zero row such that, at almost every parameter `θ`, `θ ∈ O_X` (no row
of a hidden state of an input of `X` vanishes) and the rank on `X` is `P − (L+1)(d(d−1)/2 + 1)`.
With the upper bound this is the theorem in the paper's own sense. (The statement was proposed by
the reader of the eighth comparison, who compiled it from the public statements.)
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut] {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]

/-- **Theorem 5.2 (ii) at `ε = 0`, with a batch in the domain:** for `d_in, d_out ≥ d ≥ 2`,
GELU blocks with at least `d` hidden units each and at least one token, there is a finite batch `X`
of inputs without a zero row such that at almost every parameter `θ` no row of a hidden state of an
input of `X` vanishes and the rank of the Jacobian on `X` is `P − (L+1)(d(d−1)/2 + 1)`. -/
theorem exists_batch_ae_jacobianRank_gelu_rmsNorm_zero [Nonempty T]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i t, X i t ≠ 0) ∧
      ∀ᵐ θ ∂μ, θ ∈ hiddenNonzero gelu hid X (Fin.last L) ∧
        jacobianRank (Arch.mlp gelu (rmsNorm 0) hid) 0 X θ
            + (L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
          = Module.finrank ℝ
              (Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm 0) hid) dIn dOut) := by
  have : Nonempty d := Fintype.card_pos_iff.1 (by omega)
  -- the parameter `θ*` and the batch `X*` of Appendix D.7
  obtain ⟨θ₀, n, X, hX, hθ₀, hrank⟩ :=
    exists_jacobianRank_gelu_rmsNorm_zero (T := T) (hid := hid) hd hdIn hdOut hhid
  have hσ0 : ∀ z : ℝ, gelu z = 0 ↔ z = 0 := by
    intro z
    rw [gelu, mul_eq_zero]
    exact ⟨fun h => h.resolve_right (gaussCdf_pos z).ne', fun h => Or.inl h⟩
  have hh2 : ∀ ℓ, 2 ≤ Fintype.card (hid ℓ) := fun ℓ => le_trans hd (hhid ℓ)
  -- Lemma D.20: the complement of `O_X` is null, and `O_X` is open and connected
  have hnull := measure_compl_hiddenNonzero analyticOnNhd_gelu hσ0 hd hh2 X hX μ (Fin.last L)
  -- the rank on `X` is at least the rank at `θ*` at almost every parameter
  have hge := ae_jacobianRank_ge_of_isPreconnected (Arch.mlp gelu (rmsNorm 0) hid) 0 μ X
    (isOpen_hiddenNonzero analyticOnNhd_gelu X (Fin.last L))
    (isPreconnected_hiddenNonzero analyticOnNhd_gelu hσ0 hd hh2 X hX (Fin.last L))
    hnull (analyticOnNhd_evalBatch_hiddenNonzero analyticOnNhd_gelu X) hθ₀
  -- the upper bound with the group `CO(d)`
  have hle := ae_funDim_add_le_skipless_rmsNorm_zero μ
    (A := Arch.mlp (T := T) (d := d) gelu (rmsNorm 0) hid) rfl hdIn hhid
  have hin : ∀ᵐ θ ∂μ, θ ∈ hiddenNonzero gelu hid X (Fin.last L) :=
    compl_mem_ae_iff.2 hnull |> fun h => by simpa using h
  refine ⟨n, X, hX, ?_⟩
  filter_upwards [hge, hle, hin] with θ h1 h2 h3
  have h4 := jacobianRank_le_funDim (S := 0) θ X
  exact ⟨h3, by omega⟩

end Skips
