import SkipsLean.Dimension.RescalingGate

/-!
# The rescalings of ReLU, ReLU² and ReGLU blocks, as maps of the parameters

Paper (dimension paper): Appendix B, "The symmetries inside the blocks",

  ReLU:  `(c_i, a_i) ↦ (λ c_i, a_i / λ)`,   ReLU²:  `(c_i, a_i) ↦ (λ c_i, a_i / λ²)`,   `λ > 0`,

and for a ReGLU block the same rescaling of the gate column of each hidden unit.

`Dimension/RescalingMlp.lean` and `Dimension/RescalingGate.lean` state that every parameter of
this form gives the same function (`eval_rescale_mlp`, `eval_rescale_gate`), and have the
directions `rescaleDirMlp`, `rescaleDirGate`. Here the rescalings as maps of the parameters, as
`Params.rescale` (`Dimension/RescaleAction.lean`) for the rescaling of the values of a gated
block: `θ.rescaleMlp k c` and `θ.rescaleGate k c`, for an activation or gate that is positively
homogeneous of degree `k` (`k = 1` for ReLU, `k = 2` for ReLU²). They are used to state that only
the identity fixes a parameter (Lemma A.18 of the skips paper, `Symmetry/LocallyFreeEmbedding.lean`
and `Symmetry/LocallyFreeReadout.lean`).
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {σ : ℝ → ℝ} {χ : Matrix T d ℝ → Matrix T d ℝ} {hid : Fin L → Type}
  [∀ ℓ, Fintype (hid ℓ)]

/-- The rescaling of the hidden units of an MLP network: the read column of hidden unit `i` of
block `ℓ` is multiplied by `c ℓ i`, and its write row is divided by `(c ℓ i)^k`. -/
noncomputable def Params.rescaleMlp (k : ℕ)
    (θ : Params (Arch.mlp (T := T) (d := d) σ χ hid) dIn dOut) (c : ∀ ℓ, hid ℓ → ℝ) :
    Params (Arch.mlp (T := T) (d := d) σ χ hid) dIn dOut where
  E := θ.E
  read ℓ := Matrix.of fun a i => c ℓ i * θ.read ℓ a i
  write ℓ := Matrix.of fun i a => (c ℓ i ^ k)⁻¹ * θ.write ℓ i a
  D := θ.D

/-- The rescaling of the gates of the hidden units of a gated network: the gate column of hidden
unit `i` of block `ℓ` is multiplied by `c ℓ i`, and its write row is divided by `(c ℓ i)^k`; the
value columns stay. -/
noncomputable def Params.rescaleGate (k : ℕ)
    (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut) (c : ∀ ℓ, hid ℓ → ℝ) :
    Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut where
  E := θ.E
  read ℓ := Matrix.of fun a j =>
    Sum.elim (fun i => c ℓ i * θ.read ℓ a (Sum.inl i)) (fun i => θ.read ℓ a (Sum.inr i)) j
  write ℓ := Matrix.of fun i a => (c ℓ i ^ k)⁻¹ * θ.write ℓ i a
  D := θ.D

/-- The rescalings of the hidden units preserve the function, for an activation that is
positively homogeneous of degree `k`, positive `c`, every map `χ` before the reads and all stream
matrices. -/
theorem eval_rescaleMlp_params {k : ℕ}
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (θ : Params (Arch.mlp (T := T) (d := d) σ χ hid) dIn dOut) (c : ∀ ℓ, hid ℓ → ℝ)
    (hc : ∀ ℓ i, 0 < c ℓ i) (S : Fin L → Matrix d d ℝ) (x : Matrix T dIn ℝ) :
    eval (Arch.mlp σ χ hid) S (θ.rescaleMlp k c) x = eval (Arch.mlp σ χ hid) S θ x :=
  eval_rescale_mlp hσ θ (θ.rescaleMlp k c) c hc rfl rfl (fun _ _ _ => rfl) (fun _ _ _ => rfl) S x

/-- The rescalings of the gates preserve the function, for a gate that is positively homogeneous
of degree `k`, positive `c`, every map `χ` before the reads and all stream matrices. -/
theorem eval_rescaleGate_params {k : ℕ}
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut) (c : ∀ ℓ, hid ℓ → ℝ)
    (hc : ∀ ℓ i, 0 < c ℓ i) (S : Fin L → Matrix d d ℝ) (x : Matrix T dIn ℝ) :
    eval (Arch.gated σ χ hid) S (θ.rescaleGate k c) x = eval (Arch.gated σ χ hid) S θ x :=
  eval_rescale_gate hσ θ (θ.rescaleGate k c) c hc rfl rfl (fun _ _ _ => rfl) (fun _ _ _ => rfl)
    (fun _ _ _ => rfl) S x

end Skips
