import SkipsLean.Residual.SmallWrites
import SkipsLean.OneBlock.Tanh
import SkipsLean.OneBlock.GELU
import SkipsLean.Activations.Analytic

/-!
# Residual networks of `tanh` and GELU blocks at any depth

Paper (skips paper): Lemma A.27 (Small writes), its first value `fd(θ_τ) = P - d² - s`, and
Theorem 4.7 (Equality for residual networks at any depth), both without normalization and without
biases, for MLP blocks whose hidden units have no symmetry of their own (`s = 0`): `tanh` blocks
and GELU blocks. The blocks may have any widths.

The proof of Lemma A.27 places the reads of all blocks side by side and stacks their writes, "so
that `n ↦ f(n W_read) W_write` is one wide block that holds all hidden units of the network". For a
direction `η` that is flat for the limit `J_0` (`Residual/SmallWrites.lean`), Lemma B.3 for the
units of all blocks together (`UnitsRigid` on the hidden units `Σ ℓ, hid ℓ`) gives
`η_E D + E η_D = 0`, `E η_read^ℓ = 0` and `η_write^ℓ D = 0`; as `E` and `D` have rank `d`, this is
`η_E = E X`, `η_D = -X D`, `η_read^ℓ = 0`, `η_write^ℓ = 0`: a space of dimension `d²`.

Theorem 4.7 follows as in the paper: the rank of the Jacobian on a batch is at least its value at
one parameter outside a set of measure zero (the outputs are real-analytic in the parameters), and
at most `P - d²` wherever `E` has rank `d`.
-/

namespace Skips

open Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d]
  [Fintype dIn] [Fintype dOut]
variable {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]
variable {σ σ' : ℝ → ℝ}

/-- **The conditions on `θ` in Lemma A.27, for MLP blocks without normalization:** `E` and `D`
have rank `d`, and "the hypotheses of Lemma B.3 hold for the units of all blocks together": with
`c_{ℓ,i}` the columns of `E W_read^ℓ` and `a_{ℓ,i}` the rows of `W_write^ℓ D`, every `a_{ℓ,i}` is
nonzero and the `c_{ℓ,i}`, over all blocks `ℓ` and hidden units `i`, are nonzero and pairwise
non-collinear. -/
structure SmallWritesGeneric (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) :
    Prop where
  rank_E : θ.E.rank = Fintype.card d
  rank_D : θ.D.rank = Fintype.card d
  /-- every row `a_{ℓ,i}` of `W_write^ℓ D` is nonzero -/
  row_ne_zero : ∀ ℓ i, (θ.write ℓ * θ.D) i ≠ 0
  /-- every column `c_{ℓ,i}` of `E W_read^ℓ` is nonzero -/
  col_ne_zero : ∀ ℓ i, (θ.E * θ.read ℓ)ᵀ i ≠ 0
  /-- the columns `c_{ℓ,i}` of all blocks together are pairwise non-collinear -/
  col_not_collinear : ∀ p q : (Σ ℓ, hid ℓ), p ≠ q → ∀ r : ℝ,
    (θ.E * θ.read p.1)ᵀ p.2 ≠ r • (θ.E * θ.read q.1)ᵀ q.2

/-- **Proof of Lemma A.27, MLP blocks without normalization, the flat directions of `J_0`:** under
the conditions of the lemma, a direction `η` with `(J_0 η)(x) = 0` at every input `x` has
`η_E = E X` and `η_D = -X D` for one matrix `X`, and `η_read^ℓ = 0`, `η_write^ℓ = 0` for every
block. Stated for every activation that satisfies the conclusion of Lemma B.3 with `s = 0`
(`UnitsRigid`) for the hidden units of all blocks together. -/
theorem smallWritesLimit_eq_zero_mlp (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hU : UnitsRigid σ σ' dIn dOut (Σ ℓ, hid ℓ))
    (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) (hθ : SmallWritesGeneric θ)
    (η : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)
    (hη : ∀ x, smallWritesLimit (Arch.mlp σ id hid) θ η x = 0) :
    ∃ X : Matrix d d ℝ, η.E = θ.E * X ∧ η.D = -(X * θ.D)
      ∧ (∀ ℓ, η.read ℓ = 0) ∧ (∀ ℓ, η.write ℓ = 0) := by
  sorry

/-- **Lemma A.27 (Small writes), first value, for MLP blocks with `s = 0`, under the conditions of
its proof:** for all small `τ ≠ 0` the residual network has `fd(θ_τ) = P - d²`. -/
theorem eventually_funDim_smallWrites_mlp (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hσa : AnalyticOnNhd ℝ σ Set.univ) (hU : UnitsRigid σ σ' dIn dOut (Σ ℓ, hid ℓ))
    (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) (hθ : SmallWritesGeneric θ) :
    ∀ᶠ τ in 𝓝[≠] (0 : ℝ),
      funDim (Arch.mlp σ id hid) 1 (θ.smallWrites τ) + Fintype.card d ^ 2
        = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) := by
  sorry

/-- The conditions of Lemma A.27 hold at generic parameters, for `d_in, d_out ≥ d ≥ 2` and blocks
of any widths. -/
theorem ae_smallWritesGeneric
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)) [μ.IsAddHaarMeasure]
    (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, SmallWritesGeneric θ := by
  sorry

/-- **Lemma A.27 (Small writes), first value, for MLP blocks with `s = 0`:** with
`d_in, d_out ≥ d ≥ 2` and blocks of any widths, for generic parameters `θ` and all small `τ ≠ 0`,
the residual network has `fd(θ_τ) = P - d²`. -/
theorem ae_eventually_funDim_smallWrites_mlp (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hσa : AnalyticOnNhd ℝ σ Set.univ) (hU : UnitsRigid σ σ' dIn dOut (Σ ℓ, hid ℓ))
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)) [μ.IsAddHaarMeasure]
    (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, ∀ᶠ τ in 𝓝[≠] (0 : ℝ),
      funDim (Arch.mlp σ id hid) 1 (θ.smallWrites τ) + Fintype.card d ^ 2
        = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) := by
  sorry

/-- **Theorem 4.7 of the skips paper for MLP blocks with `s = 0`, without normalization:** with
`d_in, d_out ≥ d ≥ 2` and `L` blocks of any widths, at generic parameters the residual network has
the functional dimension `P - d²`. -/
theorem ae_funDim_mlp_residual (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hσa : AnalyticOnNhd ℝ σ Set.univ) (hU : UnitsRigid σ σ' dIn dOut (Σ ℓ, hid ℓ))
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)) [μ.IsAddHaarMeasure]
    (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, funDim (Arch.mlp σ id hid) 1 θ + Fintype.card d ^ 2
      = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) := by
  sorry

/-! ### The two kinds of block -/

/-- **Lemma A.27 (Small writes) for `tanh` blocks, without normalization and without biases.** -/
theorem ae_eventually_funDim_smallWrites_tanh
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) Real.tanh id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, ∀ᶠ τ in 𝓝[≠] (0 : ℝ),
      funDim (Arch.mlp Real.tanh id hid) 1 (θ.smallWrites τ) + Fintype.card d ^ 2
        = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) Real.tanh id hid) dIn dOut) := by
  sorry

/-- **Lemma A.27 (Small writes) for GELU blocks, without normalization and without biases.** -/
theorem ae_eventually_funDim_smallWrites_gelu
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) gelu id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, ∀ᶠ τ in 𝓝[≠] (0 : ℝ),
      funDim (Arch.mlp gelu id hid) 1 (θ.smallWrites τ) + Fintype.card d ^ 2
        = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) gelu id hid) dIn dOut) := by
  sorry

/-- **Theorem 4.7 of the skips paper for `tanh` blocks, without normalization:** at generic
parameters the residual network of `L` blocks has the functional dimension `P - d²`. -/
theorem ae_funDim_tanh_residual
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) Real.tanh id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, funDim (Arch.mlp Real.tanh id hid) 1 θ + Fintype.card d ^ 2
      = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) Real.tanh id hid) dIn dOut) := by
  sorry

/-- **Theorem 4.7 of the skips paper for GELU blocks, without normalization:** at generic
parameters the residual network of `L` blocks has the functional dimension `P - d²`. -/
theorem ae_funDim_gelu_residual
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) gelu id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, funDim (Arch.mlp gelu id hid) 1 θ + Fintype.card d ^ 2
      = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) gelu id hid) dIn dOut) := by
  sorry

end Skips
