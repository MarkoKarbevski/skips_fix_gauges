import SkipsLean.OneBlock.LearnedSkipRMSZeroRescaleGeneric
import SkipsLean.OneBlock.LearnedSkipRMSZeroReGLUGeneric

/-!
# The block turns a dense set of the active rows, for a skip that depends linearly on parameters

`OneBlock/LearnedSkipRMSZeroRescale.lean` and `OneBlock/LearnedSkipRMSZeroReGLU.lean` state the
condition that the proof of Theorem B.1 (iii) of the skips paper for `ε = 0` needs and the paper
does not state: the rows `u` at which `u A` and the output of the block are linearly independent
are dense among the rows off the kinks with an active unit (`TurnsActiveRowsSkip`,
`TurnsActiveRowsGatedSkip`). Their files of generic parameters prove it at almost every weights
and full skip `(θ, A)`.

The theorem is for a learned skip that is "full or upper triangular". Here the same statements
once, for a skip `ι v` that depends linearly on a parameter `v` of a finite-dimensional space and
is the identity at one `v₀` (the full skip: `ι` the identity; the upper triangular skip: `ι` the
inclusion of the upper triangular matrices): at almost every `(θ, v)` the block turns a dense set
of the active rows for the skip `ι v`, and turns some row off the kinks. The proofs are those for
the full skip: for every nonempty set `S` of hidden units, a polynomial in `(θ, v)` that is not
zero at one point with the skip `1`.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {hid : Fin 1 → Type} [∀ ℓ, Fintype (hid ℓ)]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- **A ReLU block turns a dense set of the active rows for the skip `ι v`, at almost every
`(θ, v)`,** for `d ≥ 2` and a skip that depends linearly on `v` and is the identity at one
point. -/
theorem ae_turnsActiveRowsSkip_relu_of_linear (ι : V →ₗ[ℝ] Matrix d d ℝ) (v₀ : V)
    (hι : ι v₀ = 1)
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut × V))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) :
    ∀ᵐ p ∂μ, TurnsActiveRowsSkip p.1 (ι p.2) := by
  sorry

/-- **A ReLU² block turns a dense set of the active rows for the skip `ι v`, at almost every
`(θ, v)`,** for `d ≥ 2` and a skip that depends linearly on `v` and is the identity at one
point. -/
theorem ae_turnsActiveRowsSkip_reluSq_of_linear (ι : V →ₗ[ℝ] Matrix d d ℝ) (v₀ : V)
    (hι : ι v₀ = 1)
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) reluSq (rmsNorm 0) hid) dIn dOut × V))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) :
    ∀ᵐ p ∂μ, TurnsActiveRowsSkip p.1 (ι p.2) := by
  sorry

/-- **A ReGLU block turns a dense set of the rows with an active gate for the skip `ι v`, at
almost every `(θ, v)`,** for `d ≥ 2` and a skip that depends linearly on `v` and is the identity
at one point. -/
theorem ae_turnsActiveRowsGatedSkip_reglu_of_linear (ι : V →ₗ[ℝ] Matrix d d ℝ) (v₀ : V)
    (hι : ι v₀ = 1)
    (μ : Measure (Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut × V))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) :
    ∀ᵐ p ∂μ, TurnsActiveRowsGatedSkip p.1 (ι p.2) := by
  sorry

/-- **A ReLU block with a hidden unit turns some row off the kinks, for the skip `ι v`, at almost
every `(θ, v)`,** for `d ≥ 2`. -/
theorem ae_exists_turned_row_skip_relu_of_linear [Nonempty (hid 0)] (ι : V →ₗ[ℝ] Matrix d d ℝ)
    (v₀ : V) (hι : ι v₀ = 1)
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut × V))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) :
    ∀ᵐ p ∂μ, ∃ v : d → ℝ, (∀ i, (v ᵥ* p.1.read 0) i ≠ 0) ∧
      LinearIndependent ℝ ![v ᵥ* ι p.2, vanillaBlock relu (p.1.read 0) (p.1.write 0) v] := by
  sorry

/-- **A ReLU² block with a hidden unit turns some row off the kinks, for the skip `ι v`, at
almost every `(θ, v)`,** for `d ≥ 2`. -/
theorem ae_exists_turned_row_skip_reluSq_of_linear [Nonempty (hid 0)]
    (ι : V →ₗ[ℝ] Matrix d d ℝ) (v₀ : V) (hι : ι v₀ = 1)
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) reluSq (rmsNorm 0) hid) dIn dOut × V))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) :
    ∀ᵐ p ∂μ, ∃ v : d → ℝ, (∀ i, (v ᵥ* p.1.read 0) i ≠ 0) ∧
      LinearIndependent ℝ ![v ᵥ* ι p.2, vanillaBlock reluSq (p.1.read 0) (p.1.write 0) v] := by
  sorry

/-- **A ReGLU block with a hidden unit turns some row off the kinks of the gates, for the skip
`ι v`, at almost every `(θ, v)`,** for `d ≥ 2`. -/
theorem ae_exists_turned_row_skip_reglu_of_linear [Nonempty (hid 0)]
    (ι : V →ₗ[ℝ] Matrix d d ℝ) (v₀ : V) (hι : ι v₀ = 1)
    (μ : Measure (Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut × V))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) :
    ∀ᵐ p ∂μ, ∃ v : d → ℝ, (∀ i, (v ᵥ* p.1.read 0) (Sum.inl i) ≠ 0) ∧
      LinearIndependent ℝ ![v ᵥ* ι p.2, gatedBlock relu ((p.1.read 0).submatrix id Sum.inl)
        ((p.1.read 0).submatrix id Sum.inr) (p.1.write 0) v] := by
  sorry

end Skips
