import SkipsLean.Network.Biases
import SkipsLean.Dimension.GenericRank
import SkipsLean.Generic.Params

/-!
# The functional dimension of a network with biases

Paper (skips paper), Definition 4.1 and Appendix B, "Notation and flat directions", for the
networks with biases of `Network/Biases.lean`: "With biases, `θ` also holds `b_E`, `b_read^ℓ`,
`b_write^ℓ` and `b_D`" (Lemma A.27), and `P` counts them (Theorem B.1 (i): "with biases on the
embedding, the block and the readout, counted in `P`").

Here the parameters of a network with biases are the pairs `(θ, b)` (`ParamsB A dIn dOut`), a
real normed vector space of finite dimension with its Borel σ-algebra, and the definitions and
general statements of `Dimension/Functional.lean` and `Dimension/GenericRank.lean` are repeated
for them:

* `evalBatchB`, `jacobianRankB`, `funDimB`, `flatB`: the outputs on a batch, the rank of the
  Jacobian in `(θ, b)`, Definition 4.1, and the flat directions;
* `differentiable_evalB`, `analyticOnNhd_evalB_params`: the output at an input is differentiable,
  respectively real-analytic, in `(θ, b)` when the maps of the blocks and `χ` are;
* `jacobianRankB_le_finrank`, `jacobianRankB_le_funDimB`, `exists_jacobianRankB_eq_funDimB`;
* `funDimB_add_finrank_flatB`: the functional dimension is `P` minus the dimension of the space
  of flat directions; `funDimB_add_finrank_le_of_le_flatB`: a space of flat directions bounds it;
* `mem_flatB_of_hasDerivAt`: the velocity of a curve of parameters along which the function does
  not change is flat;
* `ae_funDimB_ge`: for real-analytic blocks the functional dimension at almost every `(θ, b)` is
  at least its value at any one point.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise Topology

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [Fintype dIn] [Fintype dOut]

/-- **The parameters of a network with biases:** the pairs `(θ, b)` of the weights and the
biases. -/
abbrev ParamsB (A : Arch T d L) (dIn dOut : Type*) : Type _ :=
  Params A dIn dOut × Biases A dOut

/-- The biases carry their Borel σ-algebra. -/
noncomputable instance {A : Arch T d L} : MeasurableSpace (Biases A dOut) := borel _

instance {A : Arch T d L} : BorelSpace (Biases A dOut) := ⟨rfl⟩

variable (A : Arch T d L) (S : Fin L → Matrix d d ℝ)

/-- The outputs of the network with biases on a batch `X = (x_1, …, x_n)` of inputs. -/
def evalBatchB {n : ℕ} (X : Fin n → Matrix T dIn ℝ) (p : ParamsB A dIn dOut) :
    Fin n → Matrix T dOut ℝ :=
  fun i => evalB A S p.1 p.2 (X i)

/-- The rank of the Jacobian of `(θ, b) ↦ (F_{θ,b}(x_1), …, F_{θ,b}(x_n))` at `p = (θ, b)`. -/
noncomputable def jacobianRankB {n : ℕ} (X : Fin n → Matrix T dIn ℝ) (p : ParamsB A dIn dOut) :
    ℕ :=
  Module.finrank ℝ (LinearMap.range (fderiv ℝ (evalBatchB A S X) p).toLinearMap)

/-- **Definition 4.1 for a network with biases.** The functional dimension at `(θ, b)`: the
largest rank of the Jacobian of the outputs on a finite batch of inputs. -/
noncomputable def funDimB (p : ParamsB A dIn dOut) : ℕ :=
  sSup {r : ℕ | ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), r = jacobianRankB A S X p}

/-- The flat directions at `(θ, b)`: the directions along which the derivative of
`(θ, b) ↦ F_{θ,b}(x)` vanishes for every input `x`. -/
noncomputable def flatB (p : ParamsB A dIn dOut) : Submodule ℝ (ParamsB A dIn dOut) :=
  ⨅ x : Matrix T dIn ℝ,
    LinearMap.ker (fderiv ℝ (fun q : ParamsB A dIn dOut => evalB A S q.1 q.2 x) p).toLinearMap

variable {A S}

/-- If the maps `f_ℓ` of the blocks and the map `χ` are differentiable, the output of the network
with biases at an input `x` is a differentiable function of `(θ, b)`. -/
theorem differentiable_evalB (hf : ∀ ℓ, Differentiable ℝ (A.f ℓ)) (hχ : Differentiable ℝ A.χ)
    (x : Matrix T dIn ℝ) :
    Differentiable ℝ (fun p : ParamsB A dIn dOut => evalB A S p.1 p.2 x) := by
  sorry

/-- The output of a network with biases with real-analytic maps `f_ℓ` and `χ` at a fixed input
is a real-analytic function of `(θ, b)`, for all stream matrices. -/
theorem analyticOnNhd_evalB_params (A : Arch T d L) (S : Fin L → Matrix d d ℝ)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (hχ : AnalyticOnNhd ℝ A.χ Set.univ)
    (x : Matrix T dIn ℝ) :
    AnalyticOnNhd ℝ (fun p : ParamsB A dIn dOut => evalB A S p.1 p.2 x) Set.univ := by
  sorry

variable (p : ParamsB A dIn dOut)

/-- The rank of the Jacobian on any batch is at most the number `P` of parameters, biases
included. -/
theorem jacobianRankB_le_finrank {n : ℕ} (X : Fin n → Matrix T dIn ℝ) :
    jacobianRankB A S X p ≤ Module.finrank ℝ (ParamsB A dIn dOut) := by
  sorry

/-- The functional dimension of a network with biases is attained on some finite batch. -/
theorem exists_jacobianRankB_eq_funDimB :
    ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), jacobianRankB A S X p = funDimB A S p := by
  sorry

/-- The rank of the Jacobian on any batch is at most the functional dimension. -/
theorem jacobianRankB_le_funDimB {n : ℕ} (X : Fin n → Matrix T dIn ℝ) :
    jacobianRankB A S X p ≤ funDimB A S p := by
  sorry

/-- **Appendix B, "Notation and flat directions", with biases:** the functional dimension is
`P − dim K(θ, b)`. -/
theorem funDimB_add_finrank_flatB
    (hdiff : ∀ x : Matrix T dIn ℝ,
      DifferentiableAt ℝ (fun q : ParamsB A dIn dOut => evalB A S q.1 q.2 x) p) :
    funDimB A S p + Module.finrank ℝ (flatB A S p) = Module.finrank ℝ (ParamsB A dIn dOut) := by
  sorry

/-- A subspace of flat directions bounds the functional dimension of a network with biases from
above. -/
theorem funDimB_add_finrank_le_of_le_flatB
    (hdiff : ∀ x : Matrix T dIn ℝ,
      DifferentiableAt ℝ (fun q : ParamsB A dIn dOut => evalB A S q.1 q.2 x) p)
    (V : Submodule ℝ (ParamsB A dIn dOut)) (hV : V ≤ flatB A S p) :
    funDimB A S p + Module.finrank ℝ V ≤ Module.finrank ℝ (ParamsB A dIn dOut) := by
  sorry

/-- **A direction of a symmetry is flat, with biases.** If a curve `γ` of parameters passes
through `(θ, b)` with velocity `η` and the function of the network is the same along it, then `η`
is flat at `(θ, b)`. -/
theorem mem_flatB_of_hasDerivAt
    (hdiff : ∀ x : Matrix T dIn ℝ,
      DifferentiableAt ℝ (fun q : ParamsB A dIn dOut => evalB A S q.1 q.2 x) p)
    (γ : ℝ → ParamsB A dIn dOut) (η : ParamsB A dIn dOut) (hγ : HasDerivAt γ η 0)
    (hγ0 : γ 0 = p)
    (hconst : ∀ᶠ τ in 𝓝 (0 : ℝ), ∀ x : Matrix T dIn ℝ,
      evalB A S (γ τ).1 (γ τ).2 x = evalB A S p.1 p.2 x) :
    η ∈ flatB A S p := by
  sorry

/-- **The functional dimension of a network with biases is, at almost every `(θ, b)`, at least
its value at any one point,** for real-analytic maps `f_ℓ` and `χ` and any stream matrices. -/
theorem ae_funDimB_ge (A : Arch T d L) (S : Fin L → Matrix d d ℝ)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (hχ : AnalyticOnNhd ℝ A.χ Set.univ)
    (μ : Measure (ParamsB A dIn dOut)) [μ.IsAddHaarMeasure] (p₀ : ParamsB A dIn dOut) :
    ∀ᵐ p ∂μ, funDimB A S p₀ ≤ funDimB A S p := by
  sorry

end Skips
