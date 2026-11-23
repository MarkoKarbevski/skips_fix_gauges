import SkipsLean.OneBlock.Common
import SkipsLean.OneBlock.Factorization

/-!
# The one-block theorem for an MLP block without symmetries inside its hidden units

Paper (dimension paper): Theorem 5.1 (Theorem C.1 in the appendix), for the kinds of MLP block
with `s = 0`, which are the `tanh` and the GELU blocks: with one block, without normalization and
without biases, at generic parameters the functional dimension is `P - 2 d²`.

The network is `x ↦ σ(x E W_read) W_write D`. With `C = E W_read` and `A = W_write D`, let `c_i`
be the columns of `C` and `a_i` the rows of `A`. The conditions that the proof uses are: `E`, `D`,
`W_read` and `W_write` have rank `d`, every `a_i` is nonzero, and the `c_i` are nonzero and pairwise
non-collinear (`OneBlockGeneric`). They hold at generic parameters when
`d_in, d_out, d_hidden ≥ d ≥ 2`.

The proof of the paper has three steps, and only Step 2 (Lemma C.3) depends on the activation. So
the theorem is stated here for every activation `σ` with derivative `σ'` for which the conclusion
of Lemma C.3 holds (`UnitsRigid σ σ'`). `Tanh.lean` and `GELU.lean` apply it.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

/-- **The conclusion of Lemma C.3 for an activation without symmetries inside its hidden units**
(`tanh` and GELU), as a property of the activation `σ` and of its derivative `σ'`. Rows are indexed
by `n` (the coordinates of an input `x`), hidden units by `q`, and the coordinates of the output by
`k`. The function is `G(φ, x) = x M + γ + ∑_i σ(x c_i + β_i) a_i`; if every `a_i` is nonzero and
the `c_i` are nonzero and pairwise non-collinear, then a direction `ψ` of the weights along which
the derivative of `G` vanishes at every input `x` is zero. -/
def UnitsRigid (σ σ' : ℝ → ℝ) (n k q : Type*) [Fintype n] [Fintype k] [Fintype q] : Prop :=
  ∀ (c : q → n → ℝ) (β : q → ℝ) (a : q → k → ℝ)
    (ψM : Matrix n k ℝ) (ψγ : k → ℝ) (ψc : q → n → ℝ) (ψβ : q → ℝ) (ψa : q → k → ℝ),
    (∀ i, a i ≠ 0) → (∀ i, c i ≠ 0) → (∀ i j, i ≠ j → ∀ r : ℝ, c i ≠ r • c j) →
    (∀ x : n → ℝ,
      x ᵥ* ψM + ψγ + ∑ i, (σ (x ⬝ᵥ c i + β i) • ψa i
        + (σ' (x ⬝ᵥ c i + β i) * (x ⬝ᵥ ψc i + ψβ i)) • a i) = 0) →
    ψM = 0 ∧ ψγ = 0 ∧ ψc = 0 ∧ ψβ = 0 ∧ ψa = 0

variable {T d dIn dOut : Type*} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {hid : Fin 1 → Type} [∀ ℓ, Fintype (hid ℓ)]
variable {σ σ' : ℝ → ℝ}

/-- The conditions on the parameters of one MLP block that the proof of the one-block theorem
uses. They do not depend on the activation. -/
structure OneBlockGeneric (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) :
    Prop where
  rank_E : θ.E.rank = Fintype.card d
  rank_D : θ.D.rank = Fintype.card d
  rank_read : (θ.read 0).rank = Fintype.card d
  rank_write : (θ.write 0).rank = Fintype.card d
  /-- every row `a_i` of `A = W_write D` is nonzero -/
  row_ne_zero : ∀ i, (θ.write 0 * θ.D) i ≠ 0
  /-- every column `c_i` of `C = E W_read` is nonzero -/
  col_ne_zero : ∀ i, (θ.E * θ.read 0)ᵀ i ≠ 0
  /-- the columns of `C` are pairwise non-collinear -/
  col_not_collinear : ∀ i j, i ≠ j → ∀ r : ℝ, (θ.E * θ.read 0)ᵀ i ≠ r • (θ.E * θ.read 0)ᵀ j

/-- Under the conditions, every flat direction of one MLP block whose activation satisfies
Lemma C.3 without rescalings is the direction of two changes of basis (Steps 1 to 3 of the proof
of Theorem C.1). -/
theorem flat_le_range_cobDir_mlp (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hU : UnitsRigid σ σ' dIn dOut (hid 0))
    (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) (hθ : OneBlockGeneric θ)
    (η : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)
    (hη : η ∈ flat (Arch.mlp σ id hid) 0 θ) :
    ∃ X : Fin 2 → Matrix d d ℝ, η = cobDir θ X := by
  sorry

/-- **Theorem 5.1 for an MLP block with `s = 0`, under the conditions of its proof:** the
functional dimension is `P - 2 d²`. -/
theorem funDim_mlp_oneBlock (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hU : UnitsRigid σ σ' dIn dOut (hid 0))
    (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) (hθ : OneBlockGeneric θ) :
    funDim (Arch.mlp σ id hid) 0 θ + 2 * Fintype.card d ^ 2
      = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) := by
  sorry

/-- The conditions hold at generic parameters, when `d_in, d_out, d_hidden ≥ d ≥ 2`. -/
theorem ae_oneBlockGeneric
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ θ ∂μ, OneBlockGeneric θ := by
  sorry

/-- **Theorem 5.1 for an MLP block with `s = 0`:** with one block, without normalization and
without biases, with `d_in, d_out, d_hidden ≥ d ≥ 2`, the functional dimension is `P - 2 d²` at
generic parameters. -/
theorem ae_funDim_mlp_oneBlock (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hU : UnitsRigid σ σ' dIn dOut (hid 0))
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ θ ∂μ, funDim (Arch.mlp σ id hid) 0 θ + 2 * Fintype.card d ^ 2
      = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) :=
  (ae_oneBlockGeneric μ hd hdIn hdOut hhid).mono fun θ hθ => funDim_mlp_oneBlock hσ hU θ hθ

end Skips
