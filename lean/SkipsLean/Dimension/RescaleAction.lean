import SkipsLean.Dimension.Rescaling

/-!
# Gated blocks: the rescaling of the values of the hidden units, as a map of the parameters

Paper (dimension paper): Appendix B, "The symmetries inside the blocks"; Corollary 5.3 ("for
SwiGLU and GeGLU blocks by a rescaling of the value of each hidden unit, close to 1").

In a gated block the value column `e_i` of hidden unit `i` and its write row `a_i` can be rescaled,
`(e_i, a_i) ↦ (e_i / c, c a_i)` with `c ≠ 0`, without changing the map of the block.
`θ.rescale c` is the parameter with every value column of the read of block `ℓ` divided by
`c ℓ i` and the write row of the same hidden unit multiplied by `c ℓ i`; `E`, `D` and the gate
columns stay. `Dimension/Rescaling.lean` has the direction `rescaleDir θ α` of these rescalings and
the invariance `eval_rescale` for any parameter of this form.
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {σ : ℝ → ℝ} {χ : Matrix T d ℝ → Matrix T d ℝ} {hid : Fin L → Type}
  [∀ ℓ, Fintype (hid ℓ)]

/-- The rescaling of the values of the hidden units of a gated network: the value column of hidden
unit `i` of block `ℓ` is divided by `c ℓ i`, and its write row is multiplied by `c ℓ i`. -/
noncomputable def Params.rescale (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut)
    (c : ∀ ℓ, hid ℓ → ℝ) : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut where
  E := θ.E
  read ℓ := Matrix.of fun k j =>
    Sum.elim (fun i => θ.read ℓ k (Sum.inl i)) (fun i => (c ℓ i)⁻¹ * θ.read ℓ k (Sum.inr i)) j
  write ℓ := Matrix.of fun i k => c ℓ i * θ.write ℓ i k
  D := θ.D

variable (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut)

/-- The rescalings of the values preserve the function, for all stream matrices. -/
theorem eval_rescale_params (c : ∀ ℓ, hid ℓ → ℝ) (hc : ∀ ℓ i, c ℓ i ≠ 0)
    (S : Fin L → Matrix d d ℝ) (x : Matrix T dIn ℝ) :
    eval (Arch.gated σ χ hid) S (θ.rescale c) x = eval (Arch.gated σ χ hid) S θ x :=
  eval_rescale θ c hc (θ.rescale c) rfl rfl (fun _ _ _ => rfl) (fun _ _ _ => rfl)
    (fun _ _ _ => rfl) S x

end Skips
