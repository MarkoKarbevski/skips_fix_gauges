import SkipsLean.OneBlock.ResidualRMSZeroSteps

/-!
# One block under pre-RMSNorm with `ε = 0`: the gain of the skip is at least `dim CO(d)`

Paper (skips paper), Theorem B.1 (v): "Let the network be pre-RMSNorm with `ε = 0`, without biases,
with a tanh, GELU, SwiGLU, GeGLU or attention block. For generic parameters the skip raises the
functional dimension by at least `d_model (d_model − 1)/2 + 1`, the dimension of `CO(d_model)`."

Its proof: "Let `V_θ` be the space of directions that move only the weights of the block and leave
its output unchanged to first order at every input whose rows lie on this sphere; it contains the
symmetries inside the block. We show that the flat directions of the residual network are those of
`CO(d_model)` and those of `V_θ`, while the skipless network has at least two copies of
`CO(d_model)` and `V_θ`. The bound then holds whatever `V_θ` is. […] So `K(θ)` is the direct sum
of these directions and `V_θ`, and the residual network has functional dimension
`P − dim CO(d_model) − dim V_θ`."

"Notation and flat directions" (Appendix B): with `ε = 0`, "every input" excludes the inputs at
which a row of a hidden state that is normalized vanishes. Lean's `funDim` uses every input, also
an input with a zero row, at which Lean's `rmsNorm 0` is `0`. So the functional dimension of the
theorem is stated here as the largest rank of the Jacobian over the finite batches of inputs of a
set (`funDimOn`): for the residual network the inputs at which no row of `h_0` and of `h_1`
vanishes (`residualZeroDomain`), for the skipless network the inputs at which no row of `h_0` and
of the output `h_1` of the block vanishes (`skiplessZeroDomain`).

Here, at one parameter `θ`, for a fixed map `f` of the block that is analytic, under the
conditions of the proof: `V_θ` (`blockFlatSphere`); the residual network has functional dimension
at least `P − (d(d−1)/2 + 1) − dim V_θ`; the skipless network at most
`P − 2 (d(d−1)/2 + 1) − dim V_θ`; so the skip raises it by at least `d(d−1)/2 + 1`. The
conditions: `d ≥ 2`; `E` and `D` of rank `d`; one input `w` at which for every token the rows of
`w E` and of `g(w)` are linearly independent (residual side); the block is not zero at some point
of the sphere (skipless side: the scale at `h_1` then does not lie in `V_θ`). Not stated here: that
these conditions hold at generic parameters for the five kinds of block.
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]

/-- **The functional dimension on a set of inputs:** the largest rank of the Jacobian in the
weights over the finite batches of inputs of `U`. (For `U` the set of all inputs it is `funDim`.) -/
noncomputable def funDimOn {L : ℕ} (A : Arch T d L) (S : Fin L → Matrix d d ℝ)
    (θ : Params A dIn dOut) (U : Set (Matrix T dIn ℝ)) : ℕ :=
  sSup {r : ℕ | ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i, X i ∈ U) ∧ r = jacobianRank A S X θ}

/-- **The inputs of a skipless network of one block under pre-RMSNorm with `ε = 0` at which no
normalized row vanishes:** no row of `h_0 = x E` and no row of `h_1 = f(N_0(x E) W_read) W_write`
is zero. -/
def skiplessZeroDomain (A : Arch T d 1) (θ : Params A dIn dOut) : Set (Matrix T dIn ℝ) :=
  {x | (∀ t, (x * θ.E) t ≠ 0) ∧
    ∀ t, (A.f 0 (rmsNorm 0 (x * θ.E) * θ.read 0) * θ.write 0) t ≠ 0}

/-- **The space `V_θ` of the proof of Theorem B.1 (v):** the directions that move only the weights
of the block and leave its output unchanged to first order at every input `n` whose rows lie on
the sphere of radius `√d`. (The set of these directions is a subspace; it is written as its
span.) -/
noncomputable def blockFlatSphere (A : Arch T d 1) (θ : Params A dIn dOut) :
    Submodule ℝ (Params A dIn dOut) :=
  Submodule.span ℝ {ψ | ψ.E = 0 ∧ ψ.D = 0 ∧
    ∀ n : Matrix T d ℝ, (∀ t, n t ⬝ᵥ n t = Fintype.card d) →
      fderiv ℝ (A.f 0) (n * θ.read 0) (n * ψ.read 0) * θ.write 0
        + A.f 0 (n * θ.read 0) * ψ.write 0 = 0}

/-- **Theorem B.1 (v) of the skips paper, the residual network:** under the conditions of
`exists_antisymm_scale_of_flatOn_residual_rmsNorm_zero`, the functional dimension of the residual
network with `ε = 0`, on the inputs at which no normalized row vanishes, is at least
`P − (d(d−1)/2 + 1) − dim V_θ`. -/
theorem finrank_le_funDimOn_residual_rmsNorm_zero {A : Arch T d 1}
    (hA : A.χ = rmsNorm 0) (hd : 2 ≤ Fintype.card d)
    (hf : AnalyticOnNhd ℝ (A.f 0) Set.univ) (θ : Params A dIn dOut)
    (hE : θ.E.rank = Fintype.card d) (hD : θ.D.rank = Fintype.card d)
    (hw : ∃ w : Matrix T dIn ℝ, ∀ t, LinearIndependent ℝ
      ![(w * θ.E) t, (A.f 0 (rmsNorm 0 (w * θ.E) * θ.read 0) * θ.write 0) t]) :
    Module.finrank ℝ (Params A dIn dOut)
      ≤ funDimOn A 1 θ (residualZeroDomain A θ)
        + (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
        + Module.finrank ℝ (blockFlatSphere A θ) := by
  sorry

/-- **Theorem B.1 (v) of the skips paper, the skipless network:** if `E` and `D` have rank `d` and
the block is not zero at some `n` with rows on the sphere of radius `√d`, the functional dimension
of the skipless network with `ε = 0`, on the inputs at which no normalized row vanishes, is at
most `P − 2 (d(d−1)/2 + 1) − dim V_θ`: the directions of `CO(d)` at `h_0`, of `CO(d)` at `h_1` and
of `V_θ` are flat and independent. -/
theorem funDimOn_add_le_skipless_rmsNorm_zero {A : Arch T d 1}
    (hA : A.χ = rmsNorm 0) (hf : AnalyticOnNhd ℝ (A.f 0) Set.univ) (θ : Params A dIn dOut)
    (hE : θ.E.rank = Fintype.card d) (hD : θ.D.rank = Fintype.card d)
    (hB : ∃ n : Matrix T d ℝ, (∀ t, n t ⬝ᵥ n t = Fintype.card d) ∧
      A.f 0 (n * θ.read 0) * θ.write 0 ≠ 0) :
    funDimOn A 0 θ (skiplessZeroDomain A θ)
        + 2 * (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
        + Module.finrank ℝ (blockFlatSphere A θ)
      ≤ Module.finrank ℝ (Params A dIn dOut) := by
  sorry

/-- **Theorem B.1 (v) of the skips paper, at one parameter, under the conditions of its proof:**
with `ε = 0`, the skip raises the functional dimension by at least `d(d−1)/2 + 1`, the dimension
of `CO(d)`. -/
theorem funDimOn_skipless_add_le_funDimOn_residual_rmsNorm_zero {A : Arch T d 1}
    (hA : A.χ = rmsNorm 0) (hd : 2 ≤ Fintype.card d)
    (hf : AnalyticOnNhd ℝ (A.f 0) Set.univ) (θ : Params A dIn dOut)
    (hE : θ.E.rank = Fintype.card d) (hD : θ.D.rank = Fintype.card d)
    (hw : ∃ w : Matrix T dIn ℝ, ∀ t, LinearIndependent ℝ
      ![(w * θ.E) t, (A.f 0 (rmsNorm 0 (w * θ.E) * θ.read 0) * θ.write 0) t])
    (hB : ∃ n : Matrix T d ℝ, (∀ t, n t ⬝ᵥ n t = Fintype.card d) ∧
      A.f 0 (n * θ.read 0) * θ.write 0 ≠ 0) :
    funDimOn A 0 θ (skiplessZeroDomain A θ) + (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
      ≤ funDimOn A 1 θ (residualZeroDomain A θ) := by
  sorry

end Skips
