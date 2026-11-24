import SkipsLean.Absorb.RMSNormRays
import SkipsLean.Generic.Params
import SkipsLean.Generic.Gated
import SkipsLean.Dimension.RescalingMlp

/-!
# Under RMSNorm a residual network equals no skipless network: almost every choice of weights

Paper ("Can an MLP Absorb Its Skip Connection Exactly?"): Theorem 4.3. "Consider pre-RMSNorm
networks, with `ε ≥ 0` and blocks of any kind and width. For almost every choice of weights, a
residual network equals no skipless network, whatever its depth, widths and kinds of blocks."

`Absorb/RMSNormRays.lean` has the comparison along rays, under the conditions `TurnGeneric` on the
weights of the residual network. This file has the last part of the proof (Appendix A.3, "Measure
zero"): the conditions hold for almost every choice of weights. "Fix all weights but the writes.
The condition is linear in the writes, so the writes that satisfy it form a linear subspace. The
subspace is proper if some `a_ℓ(n̄)` has a nonzero entry at some `n̄` … And `a_1` vanishes for all
`n̄` only if the read of block 1 has a zero column, which happens on a set of measure zero. The
weights that satisfy the condition form a closed set … and by Fubini's theorem this set has
measure zero."

For blocks of any kind, what the argument uses of the blocks is that, for almost every choice of
weights, some block has a nonzero output at some normalized state (`SomeBlockNonzero`). The
theorem is stated first with this as a hypothesis, for arbitrary continuous maps `f_ℓ`, and then
for networks of MLP blocks and of gated blocks whose activation (or gate) `σ` is locally Lipschitz
and nonzero on the positive reals, where the hypothesis holds as soon as some block has a hidden
unit. tanh, GELU, ReLU, ReLU² and SiLU are such activations. The scope of the paper is
`d_in, d_out ≥ d ≥ 2`. The skipless network is of any kind: an arbitrary `Arch`.
-/

namespace Skips

open Matrix MeasureTheory Filter
open scoped Matrix.Norms.Elementwise Topology

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]

/-- Some block has a nonzero output at some normalized state: there are a block `ℓ` and a matrix
`n̄` whose rows have norm `√d` with `f_ℓ(n̄ W_read^ℓ) ≠ 0`. -/
def SomeBlockNonzero (A : Arch T d L) (θ : Params A dIn dOut) : Prop :=
  ∃ ℓ, ∃ n : Matrix T d ℝ, (∀ t, n t ⬝ᵥ n t = (Fintype.card d : ℝ)) ∧ A.f ℓ (n * θ.read ℓ) ≠ 0

/-! ### Blocks of any kind -/

/-- **Appendix A.3, "Measure zero".** If the maps `f_ℓ` are continuous and, for almost every choice
of weights, some block has a nonzero output at some normalized state, then the conditions
`TurnGeneric` hold for almost every choice of weights (`d_in, d_out ≥ d ≥ 2`). -/
theorem ae_turnGeneric (A : Arch T d L) (hf : ∀ ℓ, Continuous (A.f ℓ))
    (μ : Measure (Params A dIn dOut)) [μ.IsAddHaarMeasure]
    (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hA : ∀ᵐ θ ∂μ, SomeBlockNonzero A θ) :
    ∀ᵐ θ ∂μ, TurnGeneric A θ := by
  sorry

/-- **Theorem 4.3 for `ε > 0`, blocks of any kind.** For almost every choice of weights, a
pre-RMSNorm residual network with locally Lipschitz blocks equals no pre-RMSNorm skipless network
with locally Lipschitz blocks, whatever its depth, model dimension, widths, kinds of blocks and
constant `ε' > 0`. -/
theorem ae_ne_skipless_rmsNorm {ε : ℝ} (hε : 0 < ε) (A : Arch T d L) (hχ : A.χ = rmsNorm ε)
    (hf : ∀ ℓ, LocallyLipschitz (A.f ℓ))
    (μ : Measure (Params A dIn dOut)) [μ.IsAddHaarMeasure]
    (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hA : ∀ᵐ θ ∂μ, SomeBlockNonzero A θ) :
    ∀ᵐ θ ∂μ, ∀ (L' : ℕ) (d' : Type) [Fintype d'] (A' : Arch T d' L') (ε' : ℝ), 0 < ε' →
      A'.χ = rmsNorm ε' → (∀ ℓ, LocallyLipschitz (A'.f ℓ)) → ∀ θ' : Params A' dIn dOut,
        ∃ X : Matrix T dIn ℝ, eval A 1 θ X ≠ eval A' 0 θ' X := by
  sorry

/-- **Theorem 4.3 for `ε = 0`, blocks of any kind.** For almost every choice of weights, a
pre-RMSNorm residual network with `ε = 0` and locally Lipschitz blocks equals no pre-RMSNorm
skipless network with `ε = 0` and continuous blocks: there is no dense set of inputs at which both
networks are defined and agree. -/
theorem ae_not_dense_eq_skipless_rmsNorm_zero (A : Arch T d L) (hχ : A.χ = rmsNorm 0)
    (hf : ∀ ℓ, LocallyLipschitz (A.f ℓ))
    (μ : Measure (Params A dIn dOut)) [μ.IsAddHaarMeasure]
    (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hA : ∀ᵐ θ ∂μ, SomeBlockNonzero A θ) :
    ∀ᵐ θ ∂μ, ∀ (L' : ℕ) (d' : Type) [Fintype d'] (A' : Arch T d' L'), A'.χ = rmsNorm 0 →
      (∀ ℓ, Continuous (A'.f ℓ)) → ∀ θ' : Params A' dIn dOut,
        ¬ ∃ S : Set (Matrix T dIn ℝ), Dense S ∧
          ∀ X ∈ S, DefinedAt A 1 θ X ∧ DefinedAt A' 0 θ' X ∧ eval A 1 θ X = eval A' 0 θ' X := by
  sorry

/-! ### MLP blocks and gated blocks -/

variable {σ : ℝ → ℝ} {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]

/-- An MLP block with a locally Lipschitz activation is locally Lipschitz. -/
theorem locallyLipschitz_f_mlp {χ : Matrix T d ℝ → Matrix T d ℝ} (hσ : LocallyLipschitz σ)
    (ℓ : Fin L) : LocallyLipschitz ((Arch.mlp (T := T) (d := d) σ χ hid).f ℓ) := by
  sorry

/-- A gated block with a locally Lipschitz gate is locally Lipschitz. -/
theorem locallyLipschitz_f_gated {χ : Matrix T d ℝ → Matrix T d ℝ} (hσ : LocallyLipschitz σ)
    (ℓ : Fin L) : LocallyLipschitz ((Arch.gated (T := T) (d := d) σ χ hid).f ℓ) := by
  sorry

/-- For a network of MLP blocks whose activation is nonzero on the positive reals, in which some
block has a hidden unit: for almost every choice of weights, some block has a nonzero output at
some normalized state (a read column `c ≠ 0` and the state with all rows `√d c / ‖c‖`). -/
theorem ae_someBlockNonzero_mlp [Nonempty T] [Nonempty d] {χ : Matrix T d ℝ → Matrix T d ℝ}
    (hσ : ∀ z, 0 < z → σ z ≠ 0) (hhid : ∃ ℓ, Nonempty (hid ℓ))
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) σ χ hid) dIn dOut)) [μ.IsAddHaarMeasure] :
    ∀ᵐ θ ∂μ, SomeBlockNonzero (Arch.mlp σ χ hid) θ := by
  sorry

/-- The same for a network of gated blocks whose gate is nonzero on the positive reals. -/
theorem ae_someBlockNonzero_gated [Nonempty T] [Nonempty d] {χ : Matrix T d ℝ → Matrix T d ℝ}
    (hσ : ∀ z, 0 < z → σ z ≠ 0) (hhid : ∃ ℓ, Nonempty (hid ℓ))
    (μ : Measure (Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut)) [μ.IsAddHaarMeasure] :
    ∀ᵐ θ ∂μ, SomeBlockNonzero (Arch.gated σ χ hid) θ := by
  sorry

/-- **Theorem 4.3 for `ε > 0`, residual networks of MLP blocks** whose activation is locally
Lipschitz and nonzero on the positive reals: for almost every choice of weights
(`d_in, d_out ≥ d ≥ 2`, some block has a hidden unit), the residual network equals no pre-RMSNorm
skipless network with locally Lipschitz blocks of any kind. -/
theorem ae_ne_skipless_rmsNorm_mlp [Nonempty T] {ε : ℝ} (hε : 0 < ε)
    (hσ : ∀ z, 0 < z → σ z ≠ 0) (hσL : LocallyLipschitz σ) (hhid : ∃ ℓ, Nonempty (hid ℓ))
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure]
    (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, ∀ (L' : ℕ) (d' : Type) [Fintype d'] (A' : Arch T d' L') (ε' : ℝ), 0 < ε' →
      A'.χ = rmsNorm ε' → (∀ ℓ, LocallyLipschitz (A'.f ℓ)) → ∀ θ' : Params A' dIn dOut,
        ∃ X : Matrix T dIn ℝ,
          eval (Arch.mlp σ (rmsNorm ε) hid) 1 θ X ≠ eval A' 0 θ' X := by
  sorry

/-- **Theorem 4.3 for `ε = 0`, residual networks of MLP blocks.** -/
theorem ae_not_dense_eq_skipless_rmsNorm_zero_mlp [Nonempty T]
    (hσ : ∀ z, 0 < z → σ z ≠ 0) (hσL : LocallyLipschitz σ) (hhid : ∃ ℓ, Nonempty (hid ℓ))
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure]
    (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, ∀ (L' : ℕ) (d' : Type) [Fintype d'] (A' : Arch T d' L'), A'.χ = rmsNorm 0 →
      (∀ ℓ, Continuous (A'.f ℓ)) → ∀ θ' : Params A' dIn dOut,
        ¬ ∃ S : Set (Matrix T dIn ℝ), Dense S ∧
          ∀ X ∈ S, DefinedAt (Arch.mlp σ (rmsNorm 0) hid) 1 θ X ∧ DefinedAt A' 0 θ' X ∧
            eval (Arch.mlp σ (rmsNorm 0) hid) 1 θ X = eval A' 0 θ' X := by
  sorry

/-- **Theorem 4.3 for `ε > 0`, residual networks of gated blocks** whose gate is locally Lipschitz
and nonzero on the positive reals. -/
theorem ae_ne_skipless_rmsNorm_gated [Nonempty T] {ε : ℝ} (hε : 0 < ε)
    (hσ : ∀ z, 0 < z → σ z ≠ 0) (hσL : LocallyLipschitz σ) (hhid : ∃ ℓ, Nonempty (hid ℓ))
    (μ : Measure (Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure]
    (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, ∀ (L' : ℕ) (d' : Type) [Fintype d'] (A' : Arch T d' L') (ε' : ℝ), 0 < ε' →
      A'.χ = rmsNorm ε' → (∀ ℓ, LocallyLipschitz (A'.f ℓ)) → ∀ θ' : Params A' dIn dOut,
        ∃ X : Matrix T dIn ℝ,
          eval (Arch.gated σ (rmsNorm ε) hid) 1 θ X ≠ eval A' 0 θ' X := by
  sorry

/-- **Theorem 4.3 for `ε = 0`, residual networks of gated blocks.** -/
theorem ae_not_dense_eq_skipless_rmsNorm_zero_gated [Nonempty T]
    (hσ : ∀ z, 0 < z → σ z ≠ 0) (hσL : LocallyLipschitz σ) (hhid : ∃ ℓ, Nonempty (hid ℓ))
    (μ : Measure (Params (Arch.gated (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure]
    (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, ∀ (L' : ℕ) (d' : Type) [Fintype d'] (A' : Arch T d' L'), A'.χ = rmsNorm 0 →
      (∀ ℓ, Continuous (A'.f ℓ)) → ∀ θ' : Params A' dIn dOut,
        ¬ ∃ S : Set (Matrix T dIn ℝ), Dense S ∧
          ∀ X ∈ S, DefinedAt (Arch.gated σ (rmsNorm 0) hid) 1 θ X ∧ DefinedAt A' 0 θ' X ∧
            eval (Arch.gated σ (rmsNorm 0) hid) 1 θ X = eval A' 0 θ' X := by
  sorry

end Skips
