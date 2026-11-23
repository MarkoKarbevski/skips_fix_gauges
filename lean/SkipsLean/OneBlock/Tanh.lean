import SkipsLean.OneBlock.Mlp
import SkipsLean.OneBlock.UnitsTanh

/-!
# The one-block theorem for a tanh block

Paper (dimension paper): Theorem 5.1 (Theorem C.1 in the appendix), for a `tanh` block: with one
block, without normalization and without biases, at generic parameters the functional dimension is
`P - 2 d²`.

The network is `x ↦ tanh(x E W_read) W_write D`. The theorem is the general statement of
`Mlp.lean` for the activation `tanh`, whose derivative is `1 - tanh²` and for which Lemma C.3
holds (`UnitsTanh.lean`).
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

/-- `tanh' = 1 - tanh²` (from `tanh = sinh / cosh` and `cosh² - sinh² = 1`). -/
theorem hasDerivAt_tanh (y : ℝ) :
    HasDerivAt Real.tanh (1 - Real.tanh y ^ 2) y := by
  have hfun : Real.tanh = fun z => Real.sinh z / Real.cosh z := by
    funext z; exact Real.tanh_eq_sinh_div_cosh z
  have h := (Real.hasDerivAt_sinh y).div (Real.hasDerivAt_cosh y) (Real.cosh_pos y).ne'
  have hc := (Real.cosh_pos y).ne'
  have heq : 1 - Real.tanh y ^ 2
      = (Real.cosh y * Real.cosh y - Real.sinh y * Real.sinh y) / Real.cosh y ^ 2 := by
    rw [Real.tanh_eq_sinh_div_cosh]
    field_simp
  rw [heq, hfun]
  exact h

/-- Lemma C.3 for `tanh`, in the form that the one-block theorem takes. -/
theorem tanh_unitsRigid (n k q : Type*) [Fintype n] [Fintype k] [Fintype q] :
    UnitsRigid Real.tanh (fun z => 1 - Real.tanh z ^ 2) n k q :=
  fun c β a ψM ψγ ψc ψβ ψa ha hc hcol h =>
    tanh_units_flat_eq_zero c β a ψM ψγ ψc ψβ ψa ha hc hcol h

variable {T d dIn dOut : Type*} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {hid : Fin 1 → Type} [∀ ℓ, Fintype (hid ℓ)]

variable (θ : Params (Arch.mlp (T := T) (d := d) Real.tanh id hid) dIn dOut)

/-- Under the conditions, every flat direction of one `tanh` block is the direction of two changes
of basis (Steps 1 to 3 of the proof of Theorem C.1). -/
theorem flat_le_range_cobDir_tanh (hθ : OneBlockGeneric θ) (η : Params _ dIn dOut)
    (hη : η ∈ flat (Arch.mlp Real.tanh id hid) 0 θ) :
    ∃ X : Fin 2 → Matrix d d ℝ, η = cobDir θ X :=
  flat_le_range_cobDir_mlp hasDerivAt_tanh (tanh_unitsRigid _ _ _) θ hθ η hη

/-- **Theorem 5.1 for a `tanh` block, under the conditions of its proof:** the functional
dimension is `P - 2 d²`. -/
theorem funDim_tanh_oneBlock (hθ : OneBlockGeneric θ) :
    funDim (Arch.mlp Real.tanh id hid) 0 θ + 2 * Fintype.card d ^ 2
      = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) Real.tanh id hid) dIn dOut) :=
  funDim_mlp_oneBlock hasDerivAt_tanh (tanh_unitsRigid _ _ _) θ hθ

/-- **Theorem 5.1 for a `tanh` block:** with one block, without normalization and without biases,
with `d_in, d_out, d_hidden ≥ d ≥ 2`, the functional dimension is `P - 2 d²` at generic
parameters. -/
theorem ae_funDim_tanh_oneBlock
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) Real.tanh id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ θ ∂μ, funDim (Arch.mlp Real.tanh id hid) 0 θ + 2 * Fintype.card d ^ 2
      = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) Real.tanh id hid) dIn dOut) :=
  ae_funDim_mlp_oneBlock hasDerivAt_tanh (tanh_unitsRigid _ _ _) μ hd hdIn hdOut hhid

end Skips
