import SkipsLean.Dimension.Functional
import SkipsLean.Symmetry.Normalized

/-!
# The upper bound from the changes of basis

Papers: dimension paper, Theorem 4.3 and Lemma B.1, for the changes of basis at the hidden states
(the symmetries inside the blocks, the number `s` of the paper, are not counted here: they depend
on the kind of block); skips paper, the bound for residual networks.

The changes of basis `I + τ X_ℓ` at the hidden states move the parameters, to first order in `τ`,
in the direction `cobDir θ X`:

  `η_E = E X_0`,  `η_read^ℓ = - X_{ℓ-1} W_read^ℓ`,  `η_write^ℓ = W_write^ℓ X_ℓ`,  `η_D = - X_L D`.

These directions are flat. If `E` and every write have rank `d`, different `X` give different
directions (Lemma B.1), so they span a space of dimension `(L + 1) d²`, and the functional
dimension is at most `P - (L + 1) d²`. In a residual network the same `X` acts at every hidden
state, and the bound is `P - d²`. The bounds under pre-RMSNorm are in `UpperBoundRMSNorm.lean`.
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise Topology

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {A : Arch T d L}

/-- The direction in which the changes of basis `I + τ X_ℓ` at the hidden states move `θ`. -/
def cobDir (θ : Params A dIn dOut) (X : Fin (L + 1) → Matrix d d ℝ) : Params A dIn dOut where
  E := θ.E * X 0
  read ℓ := -(X ℓ.castSucc * θ.read ℓ)
  write ℓ := θ.write ℓ * X ℓ.succ
  D := -(X (Fin.last L) * θ.D)

variable (θ : Params A dIn dOut)

/-- **Lemma B.1 (locally free action), for the changes of basis.** If `E` and every write have
rank `d`, the direction `cobDir θ X` determines `X`. -/
theorem cobDir_injective (hE : θ.E.rank = Fintype.card d)
    (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d) :
    Function.Injective (cobDir θ) := by
  sorry

/-- Without normalization and without skip connections, every direction `cobDir θ X` is flat. -/
theorem cobDir_mem_flat_skipless (hA : A.χ = id) (hf : ∀ ℓ, Differentiable ℝ (A.f ℓ))
    (X : Fin (L + 1) → Matrix d d ℝ) :
    cobDir θ X ∈ flat A 0 θ := by
  sorry

/-- **Theorem 4.3, without normalization, for the changes of basis.** If `E` and every write
have rank `d`, the functional dimension of a network without skip connections is at most
`P - (L + 1) d²`. -/
theorem funDim_add_le_skipless (hA : A.χ = id) (hf : ∀ ℓ, Differentiable ℝ (A.f ℓ))
    (hE : θ.E.rank = Fintype.card d) (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d) :
    funDim A 0 θ + (L + 1) * Fintype.card d ^ 2 ≤ Module.finrank ℝ (Params A dIn dOut) := by
  sorry

/-- Without normalization, in a residual network, the direction of one change of basis `X` at
all hidden states is flat. -/
theorem cobDir_const_mem_flat_residual (hA : A.χ = id) (hf : ∀ ℓ, Differentiable ℝ (A.f ℓ))
    (X : Matrix d d ℝ) :
    cobDir θ (fun _ => X) ∈ flat A 1 θ := by
  sorry

/-- **Skips paper, the upper bound for residual networks, without normalization, for the one
change of basis.** If `E` has rank `d`, the functional dimension of a residual network is at
most `P - d²`. -/
theorem funDim_add_le_residual (hA : A.χ = id) (hf : ∀ ℓ, Differentiable ℝ (A.f ℓ))
    (hE : θ.E.rank = Fintype.card d) :
    funDim A 1 θ + Fintype.card d ^ 2 ≤ Module.finrank ℝ (Params A dIn dOut) := by
  sorry

end Skips
