import SkipsLean.Network.Biases
import SkipsLean.Dimension.RescaleAction
import SkipsLean.Dimension.RescaleActionHomogeneous

/-!
# The symmetries inside blocks, in networks with biases

Paper (skips paper), Appendix B, "Reduction": with biases a hidden unit of a vanilla block
computes `σ(x c_i + β_i) a_i`, and "For the gated blocks ReGLU, SwiGLU and GeGLU, in the same way,
the value weights `(e_i, β_i′)` of each unit […] are not proportional to its gate weights
`(c_i, β_i)`". The symmetries inside a block (the `s` of Lemma A.8 and of Theorem B.1 (i)) act on
the weights of a unit together with its read biases:

* a hidden unit with a positively homogeneous activation of degree `k` (ReLU, ReLU²):
  `(c_i, β_i) ↦ λ (c_i, β_i)`, `a_i ↦ λ^{-k} a_i`, for `λ > 0` (`Biases.rescaleMlp`,
  `evalB_rescaleMlp`);
* the value of a gated unit (SwiGLU, GeGLU, ReGLU): `(e_i, β_i′) ↦ λ^{-1} (e_i, β_i′)`,
  `a_i ↦ λ a_i`, for `λ ≠ 0` (`Biases.rescale`, `evalB_rescale`);
* the gate of a gated unit with a positively homogeneous gate of degree `k` (ReGLU):
  `(c_i, β_i) ↦ λ (c_i, β_i)`, `a_i ↦ λ^{-k} a_i`, for `λ > 0` (`Biases.rescaleGate`,
  `evalB_rescaleGate`).

The actions on the weights are `Params.rescaleMlp`, `Params.rescale`, `Params.rescaleGate`
(`Dimension/RescaleAction.lean`, `Dimension/RescaleActionHomogeneous.lean`); the statements hold
for every map `χ` before the reads and all stream matrices, as their twins without biases.
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
variable {σ : ℝ → ℝ} {χ : Matrix T d ℝ → Matrix T d ℝ} {hid : Fin L → Type}
  [∀ ℓ, Fintype (hid ℓ)]

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] in
/-- **The biases after the rescaling of the hidden units of MLP blocks by `c`:** the read bias of
the unit `i` of block `ℓ` is multiplied by `c ℓ i`, as its read column is. -/
def Biases.rescaleMlp (b : Biases (Arch.mlp (T := T) (d := d) σ χ hid) dOut)
    (c : ∀ ℓ, hid ℓ → ℝ) : Biases (Arch.mlp (T := T) (d := d) σ χ hid) dOut where
  E := b.E
  read ℓ := fun i => c ℓ i * b.read ℓ i
  write := b.write
  D := b.D

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] in
/-- **The biases after the rescaling of the values of gated units by `c`:** the value bias of the
unit `i` of block `ℓ` is multiplied by `(c ℓ i)⁻¹`, as its value column is. -/
noncomputable def Biases.rescale (b : Biases (Arch.gated (T := T) (d := d) σ χ hid) dOut)
    (c : ∀ ℓ, hid ℓ → ℝ) : Biases (Arch.gated (T := T) (d := d) σ χ hid) dOut where
  E := b.E
  read ℓ := Sum.elim (fun i => b.read ℓ (Sum.inl i)) (fun i => (c ℓ i)⁻¹ * b.read ℓ (Sum.inr i))
  write := b.write
  D := b.D

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] in
/-- **The biases after the rescaling of the gates of gated units by `c`:** the gate bias of the
unit `i` of block `ℓ` is multiplied by `c ℓ i`, as its gate column is. -/
def Biases.rescaleGate (b : Biases (Arch.gated (T := T) (d := d) σ χ hid) dOut)
    (c : ∀ ℓ, hid ℓ → ℝ) : Biases (Arch.gated (T := T) (d := d) σ χ hid) dOut where
  E := b.E
  read ℓ := Sum.elim (fun i => c ℓ i * b.read ℓ (Sum.inl i)) (fun i => b.read ℓ (Sum.inr i))
  write := b.write
  D := b.D

/-- **The rescalings of the hidden units preserve the function of a network with biases,** for an
activation that is positively homogeneous of degree `k` and positive `c`: the read column and the
read bias of a unit are multiplied by `c`, its write row by `c^{-k}`. -/
theorem evalB_rescaleMlp {k : ℕ}
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (θ : Params (Arch.mlp (T := T) (d := d) σ χ hid) dIn dOut)
    (b : Biases (Arch.mlp (T := T) (d := d) σ χ hid) dOut) (c : ∀ ℓ, hid ℓ → ℝ)
    (hc : ∀ ℓ i, 0 < c ℓ i) (S : Fin L → Matrix d d ℝ) (x : Matrix T dIn ℝ) :
    evalB (Arch.mlp σ χ hid) S (θ.rescaleMlp k c) (b.rescaleMlp c) x
      = evalB (Arch.mlp σ χ hid) S θ b x := by
  sorry

/-- **The rescalings of the values of gated units preserve the function of a network with
biases,** for nonzero `c`: the value column and the value bias of a unit are multiplied by
`c⁻¹`, its write row by `c`. -/
theorem evalB_rescale (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut)
    (b : Biases (Arch.gated (T := T) (d := d) σ χ hid) dOut) (c : ∀ ℓ, hid ℓ → ℝ)
    (hc : ∀ ℓ i, c ℓ i ≠ 0) (S : Fin L → Matrix d d ℝ) (x : Matrix T dIn ℝ) :
    evalB (Arch.gated σ χ hid) S (θ.rescale c) (b.rescale c) x
      = evalB (Arch.gated σ χ hid) S θ b x := by
  sorry

/-- **The rescalings of the gates preserve the function of a network with biases,** for a gate
that is positively homogeneous of degree `k` and positive `c`: the gate column and the gate bias
of a unit are multiplied by `c`, its write row by `c^{-k}`. -/
theorem evalB_rescaleGate {k : ℕ}
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut)
    (b : Biases (Arch.gated (T := T) (d := d) σ χ hid) dOut) (c : ∀ ℓ, hid ℓ → ℝ)
    (hc : ∀ ℓ i, 0 < c ℓ i) (S : Fin L → Matrix d d ℝ) (x : Matrix T dIn ℝ) :
    evalB (Arch.gated σ χ hid) S (θ.rescaleGate k c) (b.rescaleGate c) x
      = evalB (Arch.gated σ χ hid) S θ b x := by
  sorry

end Skips
