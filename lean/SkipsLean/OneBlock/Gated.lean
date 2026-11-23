import SkipsLean.Dimension.Rescaling
import SkipsLean.OneBlock.Common
import SkipsLean.OneBlock.Factorization

/-!
# The one-block theorem for a gated block whose only symmetries inside are the rescalings

Paper (dimension paper): Theorem 5.1 (Theorem C.1 in the appendix), for the SwiGLU and the GeGLU
blocks: with one block, without normalization and without biases, at generic parameters the
functional dimension is `P - 2 d² - s`, where `s = d_hidden` counts the rescalings of the values
of the hidden units.

The network is `x ↦ f(x E W_read) W_write D` with `W_read = [W_g | W_v]` and
`f(z, w)_i = σ(z_i) w_i`. With `C = E W_read` and `A = W_write D`, hidden unit `i` has the gate
column `c_i` (column `Sum.inl i` of `C`), the value column `e_i` (column `Sum.inr i` of `C`) and
the write row `a_i` (row `i` of `A`). The conditions that the proof uses are: `E`, `D`, `W_read`
and `W_write` have rank `d`, every `a_i` and every `e_i` is nonzero, and the `c_i` are nonzero and
pairwise non-collinear (`OneBlockGenericGated`). Under them the flat directions are exactly the
sums of a direction of the two changes of basis and a direction of the rescalings.

The proof of the paper has three steps, and only Step 2 (Lemma C.3) depends on the gate
activation. So the theorem is stated here for every gate activation `σ` with derivative `σ'` for
which the conclusion of Lemma C.3 for SwiGLU and GeGLU holds (`GatedUnitsRescale σ σ'`).
`SwiGLU.lean` and `GeGLU.lean` apply it.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

/-- **The conclusion of Lemma C.3 for SwiGLU and GeGLU,** as a property of the gate activation `σ`
and of its derivative `σ'`. Rows are indexed by `n` (the coordinates of an input `x`), hidden units
by `q`, and the coordinates of the output by `k`. The function is
`G(φ, x) = x M + γ + ∑_i σ(x c_i + β_i) (x e_i + β'_i) a_i`; if every `a_i` and every `e_i` is
nonzero and the `c_i` are nonzero and pairwise non-collinear, then a direction `ψ` of the weights
along which the derivative of `G` vanishes at every input `x` only rescales the value of each
hidden unit: `ψ_M = 0`, `ψ_γ = 0`, `ψ_{c_i} = 0`, `ψ_{β_i} = 0`, and
`(ψ_{e_i}, ψ_{β'_i}) = -α_i (e_i, β'_i)`, `ψ_{a_i} = α_i a_i` for some numbers `α_i`. The paper also
assumes that `(e_i, β'_i)` is not proportional to `(c_i, β_i)`; the proofs for SwiGLU and GeGLU do
not use it. -/
def GatedUnitsRescale (σ σ' : ℝ → ℝ) (n k q : Type*) [Fintype n] [Fintype k] [Fintype q] : Prop :=
  ∀ (c : q → n → ℝ) (β : q → ℝ) (e : q → n → ℝ) (β' : q → ℝ) (a : q → k → ℝ)
    (ψM : Matrix n k ℝ) (ψγ : k → ℝ) (ψc : q → n → ℝ) (ψβ : q → ℝ) (ψe : q → n → ℝ)
    (ψβ' : q → ℝ) (ψa : q → k → ℝ),
    (∀ i, a i ≠ 0) → (∀ i, c i ≠ 0) → (∀ i j, i ≠ j → ∀ r : ℝ, c i ≠ r • c j) →
    (∀ i, e i ≠ 0) →
    (∀ x : n → ℝ,
      x ᵥ* ψM + ψγ + ∑ i,
        ((σ (x ⬝ᵥ c i + β i) * (x ⬝ᵥ e i + β' i)) • ψa i
          + (σ' (x ⬝ᵥ c i + β i) * (x ⬝ᵥ ψc i + ψβ i) * (x ⬝ᵥ e i + β' i)) • a i
          + (σ (x ⬝ᵥ c i + β i) * (x ⬝ᵥ ψe i + ψβ' i)) • a i) = 0) →
    ψM = 0 ∧ ψγ = 0 ∧ ψc = 0 ∧ ψβ = 0 ∧
      ∃ α : q → ℝ, ∀ i, ψe i = -(α i) • e i ∧ ψβ' i = -(α i) * β' i ∧ ψa i = α i • a i

variable {T d dIn dOut : Type*} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {hid : Fin 1 → Type} [∀ ℓ, Fintype (hid ℓ)]
variable {σ σ' : ℝ → ℝ}

/-- The conditions on the parameters of one gated block that the proof of the one-block theorem
uses. They do not depend on the gate activation. -/
structure OneBlockGenericGated
    (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) : Prop where
  rank_E : θ.E.rank = Fintype.card d
  rank_D : θ.D.rank = Fintype.card d
  rank_read : (θ.read 0).rank = Fintype.card d
  rank_write : (θ.write 0).rank = Fintype.card d
  /-- every row `a_i` of `A = W_write D` is nonzero -/
  row_ne_zero : ∀ i, (θ.write 0 * θ.D) i ≠ 0
  /-- every gate column `c_i` of `C = E W_read` is nonzero -/
  gate_ne_zero : ∀ i : hid 0, (θ.E * θ.read 0)ᵀ (Sum.inl i) ≠ 0
  /-- the gate columns of `C` are pairwise non-collinear -/
  gate_not_collinear : ∀ i j : hid 0, i ≠ j → ∀ r : ℝ,
    (θ.E * θ.read 0)ᵀ (Sum.inl i) ≠ r • (θ.E * θ.read 0)ᵀ (Sum.inl j)
  /-- every value column `e_i` of `C` is nonzero -/
  value_ne_zero : ∀ i : hid 0, (θ.E * θ.read 0)ᵀ (Sum.inr i) ≠ 0

/-- Under the conditions, every flat direction of one gated block whose gate activation satisfies
Lemma C.3 is the sum of the direction of two changes of basis and of the direction of a rescaling
of the values of the hidden units (Steps 1 to 3 of the proof of Theorem C.1). -/
theorem flat_le_cobDir_add_rescaleDir_gated (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hU : GatedUnitsRescale σ σ' dIn dOut (hid 0))
    (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) (hθ : OneBlockGenericGated θ)
    (η : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (hη : η ∈ flat (Arch.gated σ id hid) 0 θ) :
    ∃ (X : Fin 2 → Matrix d d ℝ) (α : ∀ ℓ, hid ℓ → ℝ), η = cobDir θ X + rescaleDir θ α := by
  sorry

/-- **Theorem 5.1 for a SwiGLU or GeGLU block, under the conditions of its proof:** the
functional dimension is `P - 2 d² - d_hidden`. -/
theorem funDim_gated_oneBlock (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hU : GatedUnitsRescale σ σ' dIn dOut (hid 0))
    (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) (hθ : OneBlockGenericGated θ) :
    funDim (Arch.gated σ id hid) 0 θ + (2 * Fintype.card d ^ 2 + Fintype.card (hid 0))
      = Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) := by
  sorry

/-- The conditions hold at generic parameters, when `d_in, d_out, d_hidden ≥ d ≥ 2`. -/
theorem ae_oneBlockGenericGated
    (μ : Measure (Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ θ ∂μ, OneBlockGenericGated θ := by
  sorry

/-- **Theorem 5.1 for a SwiGLU or GeGLU block:** with one block, without normalization and without
biases, with `d_in, d_out, d_hidden ≥ d ≥ 2`, the functional dimension is `P - 2 d² - d_hidden` at
generic parameters. -/
theorem ae_funDim_gated_oneBlock (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hU : GatedUnitsRescale σ σ' dIn dOut (hid 0))
    (μ : Measure (Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ θ ∂μ, funDim (Arch.gated σ id hid) 0 θ
        + (2 * Fintype.card d ^ 2 + Fintype.card (hid 0))
      = Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) :=
  (ae_oneBlockGenericGated μ hd hdIn hdOut hhid).mono fun θ hθ => funDim_gated_oneBlock hσ hU θ hθ

end Skips
