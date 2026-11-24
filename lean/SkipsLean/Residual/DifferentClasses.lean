import SkipsLean.Residual.SkiplessEnds
import SkipsLean.Residual.DifferentClassesCriterion
import SkipsLean.Residual.DepthMlp
import SkipsLean.Residual.DepthGated

/-!
# Residual and skipless networks of the same widths: different function classes

Paper (skips paper): Theorem 4.11 (i) and Theorem A.28 (ii), (iv), without normalization, for
`tanh`, GELU, SwiGLU and GeGLU blocks (attention blocks are not defined in this library), `L ≥ 1`
blocks of any widths, `d_in, d_out ≥ d ≥ 2`.

Theorem 4.11 (i): "For analytic blocks, with or without pre-RMSNorm, a residual network at generic
parameters equals no skipless network of the same widths, and is not a pointwise limit of such
networks." Theorem A.28 (iv): "almost every choice of weights of the residual network `F` has a
finite set `X` of inputs and a `δ > 0` such that every such skipless network `G` has
`‖G(x) - F(x)‖ ≥ δ` at some `x ∈ X`."

The proof of Theorem A.28 (ii): the residual network has functional dimension `P - d² - s` at some
parameters (Lemma A.27; here Theorem 4.7, `Residual/DepthMlp.lean` and `Residual/DepthGated.lean`);
in a skipless network of the same widths the changes of basis at `h_0` and `h_L` and the rescalings
give rank at most `P - 2 d² - s` at every parameter (`Residual/SkiplessEnds.lean`); Lemma A.26
(`Residual/DifferentClassesCriterion.lean`). Sard's theorem and the property of definable sets are
hypotheses from the literature (`Literature/Sard.lean`, `Literature/OMinimal.lean`). The skipless
network has the same architecture, hence the same widths; its parameters `η` are any.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d]
  [Fintype dIn] [Fintype dOut] {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)] {σ σ' : ℝ → ℝ}

/-! ### MLP blocks whose hidden units have no symmetry (`s = 0`) -/

/-- **Theorem 4.11 (i) of the skips paper, "equals no skipless network of the same widths", for MLP
blocks whose hidden units have no symmetry (`s = 0`) without normalization, given Sard's theorem**
(Theorem A.28 (ii)): with `d_in, d_out ≥ d ≥ 2` and `L ≥ 1` blocks of any widths, at generic
parameters the residual network computes a function that no skipless network of the same widths
computes. -/
theorem ae_forall_eval_residual_ne_skipless_mlp
    (hSard : ∀ r : ℕ, SardCriticalValues
      (Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) (Fin r → ℝ))
    (hσ : ∀ z, HasDerivAt σ (σ' z) z) (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (hU : UnitsRigid σ σ' dIn dOut (Σ ℓ, hid ℓ))
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hL : 0 < L) :
    ∀ᵐ θ ∂μ, ∀ η : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut,
      eval (Arch.mlp σ id hid) 1 θ ≠ eval (Arch.mlp σ id hid) 0 η := by
  sorry

/-- **Theorem A.28 (iv) of the skips paper for MLP blocks whose hidden units have no symmetry (`s =
0`) without normalization, given Sard's theorem and the property of definable sets:** there is a
finite batch `X` such that for almost every `θ` some `δ > 0` has, for every skipless network `η` of
the same widths, `‖F_θ(x) - G_η(x)‖ ≥ δ` at some `x ∈ X`. -/
theorem exists_batch_ae_exists_pos_le_norm_sub_skipless_mlp
    (hSard : ∀ r : ℕ, SardCriticalValues
      (Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) (Fin r → ℝ))
    (hOmin : ∀ (n : ℕ) (X : Fin n → Matrix T dIn ℝ),
      ClosureNullOfNull
        (Set.range (evalBatch (dOut := dOut) (Arch.mlp (T := T) (d := d) σ id hid) 0 X)))
    (hσ : ∀ z, HasDerivAt σ (σ' z) z) (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (hU : UnitsRigid σ σ' dIn dOut (Σ ℓ, hid ℓ))
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hL : 0 < L) :
    ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), ∀ᵐ θ ∂μ, ∃ δ : ℝ, 0 < δ ∧
      ∀ η : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut,
        ∃ i, δ ≤ ‖eval (Arch.mlp σ id hid) 1 θ (X i) - eval (Arch.mlp σ id hid) 0 η (X i)‖ := by
  sorry

/-- **Theorem 4.11 (i) of the skips paper, "is not a pointwise limit of such networks", for MLP
blocks whose hidden units have no symmetry (`s = 0`) without normalization, given Sard's theorem and
the property of definable sets** (Theorem A.28 (iv), Definition A.29): at generic parameters the
residual network is not a pointwise limit of the skipless networks of the same widths. -/
theorem ae_not_isPointwiseLimit_skipless_mlp
    (hSard : ∀ r : ℕ, SardCriticalValues
      (Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) (Fin r → ℝ))
    (hOmin : ∀ (n : ℕ) (X : Fin n → Matrix T dIn ℝ),
      ClosureNullOfNull
        (Set.range (evalBatch (dOut := dOut) (Arch.mlp (T := T) (d := d) σ id hid) 0 X)))
    (hσ : ∀ z, HasDerivAt σ (σ' z) z) (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (hU : UnitsRigid σ σ' dIn dOut (Σ ℓ, hid ℓ))
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hL : 0 < L) :
    ∀ᵐ θ ∂μ, ¬ IsPointwiseLimit
      (Set.range (eval (Arch.mlp (T := T) (d := d) σ id hid) 0 :
        Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut → Matrix T dIn ℝ → Matrix T dOut ℝ))
      (eval (Arch.mlp σ id hid) 1 θ) := by
  sorry

/-! ### gated blocks whose only symmetries inside the blocks are the rescalings -/

/-- **Theorem 4.11 (i) of the skips paper, "equals no skipless network of the same widths", for
gated blocks whose only symmetries inside the blocks are the rescalings without normalization, given
Sard's theorem** (Theorem A.28 (ii)): with `d_in, d_out ≥ d ≥ 2` and `L ≥ 1` blocks of any widths,
at generic parameters the residual network computes a function that no skipless network of the same
widths computes. -/
theorem ae_forall_eval_residual_ne_skipless_gated
    (hSard : ∀ r : ℕ, SardCriticalValues
      (Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) (Fin r → ℝ))
    (hσ : ∀ z, HasDerivAt σ (σ' z) z) (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (hU : GatedUnitsRescale σ σ' dIn dOut (Σ ℓ, hid ℓ))
    (μ : Measure (Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hL : 0 < L) :
    ∀ᵐ θ ∂μ, ∀ η : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut,
      eval (Arch.gated σ id hid) 1 θ ≠ eval (Arch.gated σ id hid) 0 η := by
  sorry

/-- **Theorem A.28 (iv) of the skips paper for gated blocks whose only symmetries inside the blocks
are the rescalings without normalization, given Sard's theorem and the property of definable sets:**
there is a finite batch `X` such that for almost every `θ` some `δ > 0` has, for every skipless
network `η` of the same widths, `‖F_θ(x) - G_η(x)‖ ≥ δ` at some `x ∈ X`. -/
theorem exists_batch_ae_exists_pos_le_norm_sub_skipless_gated
    (hSard : ∀ r : ℕ, SardCriticalValues
      (Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) (Fin r → ℝ))
    (hOmin : ∀ (n : ℕ) (X : Fin n → Matrix T dIn ℝ),
      ClosureNullOfNull
        (Set.range (evalBatch (dOut := dOut) (Arch.gated (T := T) (d := d) σ id hid) 0 X)))
    (hσ : ∀ z, HasDerivAt σ (σ' z) z) (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (hU : GatedUnitsRescale σ σ' dIn dOut (Σ ℓ, hid ℓ))
    (μ : Measure (Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hL : 0 < L) :
    ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), ∀ᵐ θ ∂μ, ∃ δ : ℝ, 0 < δ ∧
      ∀ η : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut,
        ∃ i, δ ≤ ‖eval (Arch.gated σ id hid) 1 θ (X i) - eval (Arch.gated σ id hid) 0 η (X i)‖ := by
  sorry

/-- **Theorem 4.11 (i) of the skips paper, "is not a pointwise limit of such networks", for gated
blocks whose only symmetries inside the blocks are the rescalings without normalization, given
Sard's theorem and the property of definable sets** (Theorem A.28 (iv), Definition A.29): at generic
parameters the residual network is not a pointwise limit of the skipless networks of the same
widths. -/
theorem ae_not_isPointwiseLimit_skipless_gated
    (hSard : ∀ r : ℕ, SardCriticalValues
      (Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) (Fin r → ℝ))
    (hOmin : ∀ (n : ℕ) (X : Fin n → Matrix T dIn ℝ),
      ClosureNullOfNull
        (Set.range (evalBatch (dOut := dOut) (Arch.gated (T := T) (d := d) σ id hid) 0 X)))
    (hσ : ∀ z, HasDerivAt σ (σ' z) z) (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (hU : GatedUnitsRescale σ σ' dIn dOut (Σ ℓ, hid ℓ))
    (μ : Measure (Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hL : 0 < L) :
    ∀ᵐ θ ∂μ, ¬ IsPointwiseLimit
      (Set.range (eval (Arch.gated (T := T) (d := d) σ id hid) 0 :
        Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut → Matrix T dIn ℝ → Matrix T dOut ℝ))
      (eval (Arch.gated σ id hid) 1 θ) := by
  sorry

/-! ### `tanh` blocks -/

/-- **Theorem 4.11 (i) of the skips paper, "equals no skipless network of the same widths", for
`tanh` blocks without normalization, given Sard's theorem** (Theorem A.28 (ii)): with `d_in, d_out ≥
d ≥ 2` and `L ≥ 1` blocks of any widths, at generic parameters the residual network computes a
function that no skipless network of the same widths computes. -/
theorem ae_forall_eval_residual_ne_skipless_tanh
    (hSard : ∀ r : ℕ, SardCriticalValues
      (Params (Arch.mlp (T := T) (d := d) Real.tanh id hid) dIn dOut) (Fin r → ℝ))
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) Real.tanh id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hL : 0 < L) :
    ∀ᵐ θ ∂μ, ∀ η : Params (Arch.mlp (T := T) (d := d) Real.tanh id hid) dIn dOut,
      eval (Arch.mlp Real.tanh id hid) 1 θ ≠ eval (Arch.mlp Real.tanh id hid) 0 η := by
  sorry

/-- **Theorem 4.11 (i) of the skips paper, "is not a pointwise limit of such networks", for `tanh`
blocks without normalization, given Sard's theorem and the property of definable sets** (Theorem
A.28 (iv), Definition A.29): at generic parameters the residual network is not a pointwise limit of
the skipless networks of the same widths. -/
theorem ae_not_isPointwiseLimit_skipless_tanh
    (hSard : ∀ r : ℕ, SardCriticalValues
      (Params (Arch.mlp (T := T) (d := d) Real.tanh id hid) dIn dOut) (Fin r → ℝ))
    (hOmin : ∀ (n : ℕ) (X : Fin n → Matrix T dIn ℝ),
      ClosureNullOfNull
        (Set.range (evalBatch (dOut := dOut) (Arch.mlp (T := T) (d := d) Real.tanh id hid) 0 X)))
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) Real.tanh id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hL : 0 < L) :
    ∀ᵐ θ ∂μ, ¬ IsPointwiseLimit
      (Set.range (eval (Arch.mlp (T := T) (d := d) Real.tanh id hid) 0 :
        Params (Arch.mlp (T := T) (d := d) Real.tanh id hid) dIn dOut →
          Matrix T dIn ℝ → Matrix T dOut ℝ))
      (eval (Arch.mlp Real.tanh id hid) 1 θ) := by
  sorry

/-! ### GELU blocks -/

/-- **Theorem 4.11 (i) of the skips paper, "equals no skipless network of the same widths", for GELU
blocks without normalization, given Sard's theorem** (Theorem A.28 (ii)): with `d_in, d_out ≥ d ≥ 2`
and `L ≥ 1` blocks of any widths, at generic parameters the residual network computes a function
that no skipless network of the same widths computes. -/
theorem ae_forall_eval_residual_ne_skipless_gelu
    (hSard : ∀ r : ℕ, SardCriticalValues
      (Params (Arch.mlp (T := T) (d := d) gelu id hid) dIn dOut) (Fin r → ℝ))
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) gelu id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hL : 0 < L) :
    ∀ᵐ θ ∂μ, ∀ η : Params (Arch.mlp (T := T) (d := d) gelu id hid) dIn dOut,
      eval (Arch.mlp gelu id hid) 1 θ ≠ eval (Arch.mlp gelu id hid) 0 η := by
  sorry

/-- **Theorem 4.11 (i) of the skips paper, "is not a pointwise limit of such networks", for GELU
blocks without normalization, given Sard's theorem and the property of definable sets** (Theorem
A.28 (iv), Definition A.29): at generic parameters the residual network is not a pointwise limit of
the skipless networks of the same widths. -/
theorem ae_not_isPointwiseLimit_skipless_gelu
    (hSard : ∀ r : ℕ, SardCriticalValues
      (Params (Arch.mlp (T := T) (d := d) gelu id hid) dIn dOut) (Fin r → ℝ))
    (hOmin : ∀ (n : ℕ) (X : Fin n → Matrix T dIn ℝ),
      ClosureNullOfNull
        (Set.range (evalBatch (dOut := dOut) (Arch.mlp (T := T) (d := d) gelu id hid) 0 X)))
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) gelu id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hL : 0 < L) :
    ∀ᵐ θ ∂μ, ¬ IsPointwiseLimit
      (Set.range (eval (Arch.mlp (T := T) (d := d) gelu id hid) 0 :
        Params (Arch.mlp (T := T) (d := d) gelu id hid) dIn dOut →
          Matrix T dIn ℝ → Matrix T dOut ℝ))
      (eval (Arch.mlp gelu id hid) 1 θ) := by
  sorry

/-! ### SwiGLU blocks -/

/-- **Theorem 4.11 (i) of the skips paper, "equals no skipless network of the same widths", for
SwiGLU blocks without normalization, given Sard's theorem** (Theorem A.28 (ii)): with `d_in, d_out ≥
d ≥ 2` and `L ≥ 1` blocks of any widths, at generic parameters the residual network computes a
function that no skipless network of the same widths computes. -/
theorem ae_forall_eval_residual_ne_skipless_swiglu
    (hSard : ∀ r : ℕ, SardCriticalValues
      (Params (Arch.gated (T := T) (d := d) silu id hid) dIn dOut) (Fin r → ℝ))
    (μ : Measure (Params (Arch.gated (T := T) (d := d) silu id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hL : 0 < L) :
    ∀ᵐ θ ∂μ, ∀ η : Params (Arch.gated (T := T) (d := d) silu id hid) dIn dOut,
      eval (Arch.gated silu id hid) 1 θ ≠ eval (Arch.gated silu id hid) 0 η := by
  sorry

/-- **Theorem 4.11 (i) of the skips paper, "is not a pointwise limit of such networks", for SwiGLU
blocks without normalization, given Sard's theorem and the property of definable sets** (Theorem
A.28 (iv), Definition A.29): at generic parameters the residual network is not a pointwise limit of
the skipless networks of the same widths. -/
theorem ae_not_isPointwiseLimit_skipless_swiglu
    (hSard : ∀ r : ℕ, SardCriticalValues
      (Params (Arch.gated (T := T) (d := d) silu id hid) dIn dOut) (Fin r → ℝ))
    (hOmin : ∀ (n : ℕ) (X : Fin n → Matrix T dIn ℝ),
      ClosureNullOfNull
        (Set.range (evalBatch (dOut := dOut) (Arch.gated (T := T) (d := d) silu id hid) 0 X)))
    (μ : Measure (Params (Arch.gated (T := T) (d := d) silu id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hL : 0 < L) :
    ∀ᵐ θ ∂μ, ¬ IsPointwiseLimit
      (Set.range (eval (Arch.gated (T := T) (d := d) silu id hid) 0 :
        Params (Arch.gated (T := T) (d := d) silu id hid) dIn dOut →
          Matrix T dIn ℝ → Matrix T dOut ℝ))
      (eval (Arch.gated silu id hid) 1 θ) := by
  sorry

/-! ### GeGLU blocks -/

/-- **Theorem 4.11 (i) of the skips paper, "equals no skipless network of the same widths", for
GeGLU blocks without normalization, given Sard's theorem** (Theorem A.28 (ii)): with `d_in, d_out ≥
d ≥ 2` and `L ≥ 1` blocks of any widths, at generic parameters the residual network computes a
function that no skipless network of the same widths computes. -/
theorem ae_forall_eval_residual_ne_skipless_geglu
    (hSard : ∀ r : ℕ, SardCriticalValues
      (Params (Arch.gated (T := T) (d := d) gelu id hid) dIn dOut) (Fin r → ℝ))
    (μ : Measure (Params (Arch.gated (T := T) (d := d) gelu id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hL : 0 < L) :
    ∀ᵐ θ ∂μ, ∀ η : Params (Arch.gated (T := T) (d := d) gelu id hid) dIn dOut,
      eval (Arch.gated gelu id hid) 1 θ ≠ eval (Arch.gated gelu id hid) 0 η := by
  sorry

/-- **Theorem 4.11 (i) of the skips paper, "is not a pointwise limit of such networks", for GeGLU
blocks without normalization, given Sard's theorem and the property of definable sets** (Theorem
A.28 (iv), Definition A.29): at generic parameters the residual network is not a pointwise limit of
the skipless networks of the same widths. -/
theorem ae_not_isPointwiseLimit_skipless_geglu
    (hSard : ∀ r : ℕ, SardCriticalValues
      (Params (Arch.gated (T := T) (d := d) gelu id hid) dIn dOut) (Fin r → ℝ))
    (hOmin : ∀ (n : ℕ) (X : Fin n → Matrix T dIn ℝ),
      ClosureNullOfNull
        (Set.range (evalBatch (dOut := dOut) (Arch.gated (T := T) (d := d) gelu id hid) 0 X)))
    (μ : Measure (Params (Arch.gated (T := T) (d := d) gelu id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hL : 0 < L) :
    ∀ᵐ θ ∂μ, ¬ IsPointwiseLimit
      (Set.range (eval (Arch.gated (T := T) (d := d) gelu id hid) 0 :
        Params (Arch.gated (T := T) (d := d) gelu id hid) dIn dOut →
          Matrix T dIn ℝ → Matrix T dOut ℝ))
      (eval (Arch.gated gelu id hid) 1 θ) := by
  sorry

end Skips
