import SkipsLean.Dimension.GenericRank
import SkipsLean.Symmetry.InsideBlocks
import SkipsLean.Symmetry.Normalized

/-!
# The functional dimension of a network with learned skips

Paper (skips paper): Theorem 4.6 (ii): "Under RMSNorm, the residual network satisfies the equality
condition, and the skip raises the functional dimension by at least `d_model (d_model − 1)/2`. A
learned skip raises it by exactly `d_model (d_model + 1)/2` more than an identity skip." Appendix B:
with one block the network under pre-RMSNorm is
`x ↦ N_ε(x E A + f(N_ε(x E) W_read) W_write) D`, "with the identity skip `A = I`. A learned skip
`A ∈ ℝ^{d_model × d_model}` is full or upper triangular." Theorem B.1 (iii): "Let the network be
pre-RMSNorm without biases, with a learned skip `A`, full or upper triangular. For generic
parameters and `ε > 0`, its functional dimension exceeds that of the residual network of part (ii)
by exactly `d_model (d_model + 1)/2`, and it satisfies the equality condition."

In `eval A S θ x` the stream matrices `S` are the skips (`Residual/LearnedSkips.lean`). Here they
become parameters: the skips are `ι v` for a continuous linear map `ι` from a space `V` (all
matrices: `ι` the identity, `funDimLearned`; another choice of `V` gives a restricted family, as
the upper triangular skips), the parameters are the pairs `(θ, v)`, and `funDimSkips` is the
functional dimension of this family (Definition 4.1 for it).

The statements of this file and of `OneBlock/LearnedSkipZero.lean`, `OneBlock/LearnedSkipBound.lean`
are the general steps; the values for the kinds of block are in `OneBlock/LearnedSkipKinds.lean`.
The route differs from Part (iii) of the paper's proof of Theorem B.1 (which runs Steps 1 to 5 of
its part (ii) again): for one block,
- the orthogonal changes of basis at `h_0` and at `h_1`, with `A ↦ G_0⁻¹ A G_1`, and the symmetries
  inside the block bound the functional dimension by `P + d² − d (d − 1) − s`
  (`funDimLearned_add_le_rmsNorm`, `OneBlock/LearnedSkipBound.lean`; the paper: "The directions
  `η^rot` […] For a full `A` they have dimension `d_model (d_model − 1)`");
- at the skip `A = 0` the family has the functional dimension of the skipless network plus the
  dimension of `V` (`funDim_add_finrank_le_funDimSkips_zero`, `OneBlock/LearnedSkipZero.lean`): a
  flat direction `(η, a)` there has `a = 0`, because along the inputs `t x`, `t → ∞`, the input of
  the block stays bounded while the skip term grows like `t`, the derivative of `N_ε` is injective
  for `ε > 0`, and `E`, `D` have rank `d`;
- at generic parameters the functional dimension is the largest (`ae_funDimSkips_ge`).
So where the skipless network attains `P − d (d − 1) − s` (tanh, GELU, SwiGLU, GeGLU blocks of width
at least `d`), the network with a full learned skip has `P + d² − d (d − 1) − s`.
-/

namespace Skips

open Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- **The function of the network whose skips are parameters:** the parameters are `(θ, v)`, the
skips are `ι v`, and the function is that of the weights `θ` with the stream matrices `ι v`. -/
def evalSkips (A : Arch T d L) (ι : V →L[ℝ] (Fin L → Matrix d d ℝ))
    (p : Params A dIn dOut × V) (x : Matrix T dIn ℝ) : Matrix T dOut ℝ :=
  eval A (ι p.2) p.1 x

/-- The rank of the Jacobian of `(θ, v) ↦ (F_{θ,v}(x_1), …, F_{θ,v}(x_n))` at `p`. -/
noncomputable def jacobianRankSkips (A : Arch T d L) (ι : V →L[ℝ] (Fin L → Matrix d d ℝ))
    {n : ℕ} (X : Fin n → Matrix T dIn ℝ) (p : Params A dIn dOut × V) : ℕ :=
  Module.finrank ℝ (LinearMap.range (fderiv ℝ
    (fun p' : Params A dIn dOut × V => fun i : Fin n => evalSkips A ι p' (X i)) p).toLinearMap)

/-- **Definition 4.1 for the network whose skips are parameters:** the largest rank of the
Jacobian of the outputs on a finite batch of inputs, in the weights and the skips. -/
noncomputable def funDimSkips (A : Arch T d L) (ι : V →L[ℝ] (Fin L → Matrix d d ℝ))
    (p : Params A dIn dOut × V) : ℕ :=
  sSup {r : ℕ | ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), r = jacobianRankSkips A ι X p}

/-- The flat directions of the network whose skips are parameters: the directions `(η, a)` along
which the derivative of `(θ, v) ↦ F_{θ,v}(x)` vanishes for every input `x`. -/
noncomputable def flatSkips (A : Arch T d L) (ι : V →L[ℝ] (Fin L → Matrix d d ℝ))
    (p : Params A dIn dOut × V) : Submodule ℝ (Params A dIn dOut × V) :=
  ⨅ x : Matrix T dIn ℝ,
    LinearMap.ker (fderiv ℝ (fun p' : Params A dIn dOut × V => evalSkips A ι p' x) p).toLinearMap

/-- **The functional dimension of the network with full learned skips** `A_1, …, A_L` (all
`d × d` matrices), at the weights and skips `p = (θ, (A_ℓ))`. -/
noncomputable abbrev funDimLearned (A : Arch T d L)
    (p : Params A dIn dOut × (Fin L → Matrix d d ℝ)) : ℕ :=
  funDimSkips A (ContinuousLinearMap.id ℝ (Fin L → Matrix d d ℝ)) p

/-- For differentiable blocks, the functional dimension and the dimension of the flat directions
add up to the number of parameters (weights and skips). -/
theorem funDimSkips_add_finrank_flatSkips [FiniteDimensional ℝ V] (A : Arch T d L)
    (ι : V →L[ℝ] (Fin L → Matrix d d ℝ)) (hf : ∀ ℓ, Differentiable ℝ (A.f ℓ))
    (hχ : Differentiable ℝ A.χ) (p : Params A dIn dOut × V) :
    funDimSkips A ι p + Module.finrank ℝ (flatSkips A ι p)
      = Module.finrank ℝ (Params A dIn dOut × V) := by
  sorry

/-- **The generic functional dimension is the largest,** for real-analytic blocks: at almost
every `(θ, v)` the functional dimension is at least that at any one `p₀`. -/
theorem ae_funDimSkips_ge [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (A : Arch T d L) (ι : V →L[ℝ] (Fin L → Matrix d d ℝ))
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (hχ : AnalyticOnNhd ℝ A.χ Set.univ)
    (μ : Measure (Params A dIn dOut × V)) [μ.IsAddHaarMeasure] (p₀ : Params A dIn dOut × V) :
    ∀ᵐ p ∂μ, funDimSkips A ι p₀ ≤ funDimSkips A ι p := by
  sorry

/-- A restricted family of skips has at most the functional dimension of the family it is
restricted from: for `j : V' → V` linear, the family with the skips `ι (j v')` has at `(θ, v')` at
most the functional dimension of the family with the skips `ι v` at `(θ, j v')`. -/
theorem funDimSkips_comp_le {V' : Type*} [NormedAddCommGroup V'] [NormedSpace ℝ V']
    (A : Arch T d L) (ι : V →L[ℝ] (Fin L → Matrix d d ℝ)) (j : V' →L[ℝ] V)
    (hf : ∀ ℓ, Differentiable ℝ (A.f ℓ)) (hχ : Differentiable ℝ A.χ)
    (θ : Params A dIn dOut) (v' : V') :
    funDimSkips A (ι.comp j) (θ, v') ≤ funDimSkips A ι (θ, j v') := by
  sorry

end Skips
