import SkipsLean.OneBlock.Mlp
import SkipsLean.OneBlock.UnitsGELU

/-!
# The one-block theorem for a GELU block

Paper (dimension paper): Theorem 5.1 (Theorem C.1 in the appendix), for a GELU block: with one
block, without normalization and without biases, at generic parameters the functional dimension is
`P - 2 d²`.

The network is `x ↦ σ(x E W_read) W_write D` with `σ(z) = z Φ(z)`. The theorem is the general
statement of `Mlp.lean` for the activation GELU, whose derivative is `Φ(z) + z φ(z)` and for which
Lemma C.3 holds (`UnitsGELU.lean`).
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

/-- Lemma C.3 for GELU, in the form that the one-block theorem takes. -/
theorem gelu_unitsRigid (n k q : Type*) [Fintype n] [Fintype k] [Fintype q] :
    UnitsRigid gelu geluDeriv n k q :=
  fun c β a ψM ψγ ψc ψβ ψa ha hc hcol h =>
    gelu_units_flat_eq_zero c β a ψM ψγ ψc ψβ ψa ha hc hcol h

variable {T d dIn dOut : Type*} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {hid : Fin 1 → Type} [∀ ℓ, Fintype (hid ℓ)]

variable (θ : Params (Arch.mlp (T := T) (d := d) gelu id hid) dIn dOut)

/-- Under the conditions, every flat direction of one GELU block is the direction of two changes
of basis (Steps 1 to 3 of the proof of Theorem C.1). -/
theorem flat_le_range_cobDir_gelu (hθ : OneBlockGeneric θ) (η : Params _ dIn dOut)
    (hη : η ∈ flat (Arch.mlp gelu id hid) 0 θ) :
    ∃ X : Fin 2 → Matrix d d ℝ, η = cobDir θ X :=
  flat_le_range_cobDir_mlp hasDerivAt_gelu (gelu_unitsRigid _ _ _) θ hθ η hη

/-- **Theorem 5.1 for a GELU block, under the conditions of its proof:** the functional dimension
is `P - 2 d²`. -/
theorem funDim_gelu_oneBlock (hθ : OneBlockGeneric θ) :
    funDim (Arch.mlp gelu id hid) 0 θ + 2 * Fintype.card d ^ 2
      = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) gelu id hid) dIn dOut) :=
  funDim_mlp_oneBlock hasDerivAt_gelu (gelu_unitsRigid _ _ _) θ hθ

/-- **Theorem 5.1 for a GELU block:** with one block, without normalization and without biases,
with `d_in, d_out, d_hidden ≥ d ≥ 2`, the functional dimension is `P - 2 d²` at generic
parameters. -/
theorem ae_funDim_gelu_oneBlock
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) gelu id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ θ ∂μ, funDim (Arch.mlp gelu id hid) 0 θ + 2 * Fintype.card d ^ 2
      = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) gelu id hid) dIn dOut) :=
  ae_funDim_mlp_oneBlock hasDerivAt_gelu (gelu_unitsRigid _ _ _) μ hd hdIn hdOut hhid

end Skips
