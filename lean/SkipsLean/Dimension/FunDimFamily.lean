import SkipsLean.Dimension.RankSubmersion
import SkipsLean.Dimension.FunctionalBiases
import SkipsLean.OneBlock.LearnedSkip

/-!
# The functional dimension of a family of functions, and changes of parameters

Paper (skips paper), Definition 4.1 gives the functional dimension of a network at `θ` as the
largest rank of the Jacobian of its outputs on a finite batch of inputs. Theorem A.5 (ii) compares
families with different parameters: "So the networks of mixed blocks with invertible skips and the
residual networks compute the same set of functions, with the same functional dimension at `θ`
and at `Φ(θ)`. The same holds for learned skips, without the `K_ℓ`, and for networks with
biases."

Here, once for all these families:

* `funDimOf F p`: Definition 4.1 for any family `F` of functions `ℝ^{T × d_in} → ℝ^{T × d_out}`
  on a normed space of parameters; the functional dimensions of the library are cases of it
  (`funDim_eq_funDimOf`, `funDimB_eq_funDimOf`, `funDimSkips_eq_funDimOf`).
* `funDimOf_eq_of_comp_of_section`: the last step of the proof of Theorem A.5 (ii) for any two
  families: if `F₁ = F₂ ∘ Φ` near `p` with `Φ` differentiable at `p`, and `F₂ = F₁ ∘ s` near
  `Φ(p)` for a map `s` differentiable at `Φ(p)` with `s(Φ(p)) = p`, then `F₁` at `p` and `F₂`
  at `Φ(p)` have the same functional dimension (`Dimension/RankSubmersion.lean` on every
  batch). No differentiability of the families is asked, and with the section the paper's
  hypothesis that the derivative of `Φ` is onto is not needed.
-/

namespace Skips

open Matrix Filter Topology
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [Fintype dIn] [Fintype dOut]

/-- **Definition 4.1 for any family of functions:** the functional dimension at the parameter
`p` of a family `F` of functions on `ℝ^{T × d_in}`, the largest rank of the Jacobian of
`q ↦ (F_q(x_1), …, F_q(x_n))` at `p` over the finite batches of inputs. -/
noncomputable def funDimOf {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (F : P → Matrix T dIn ℝ → Matrix T dOut ℝ) (p : P) : ℕ :=
  sSup {r : ℕ | ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ),
    r = Module.finrank ℝ (LinearMap.range
      (fderiv ℝ (fun q : P => fun i : Fin n => F q (X i)) p).toLinearMap)}

omit [Fintype T] in
/-- The functional dimension of a network is `funDimOf` of its family of functions. -/
theorem funDim_eq_funDimOf (A : Arch T d L) (S : Fin L → Matrix d d ℝ)
    (θ : Params A dIn dOut) : funDim A S θ = funDimOf (eval A S) θ :=
  rfl

omit [Fintype T] in
/-- The functional dimension of a network with biases is `funDimOf` of its family. -/
theorem funDimB_eq_funDimOf (A : Arch T d L) (S : Fin L → Matrix d d ℝ)
    (p : ParamsB A dIn dOut) :
    funDimB A S p = funDimOf (fun q : ParamsB A dIn dOut => evalB A S q.1 q.2) p :=
  rfl

omit [Fintype T] in
/-- The functional dimension of a network whose skips are parameters is `funDimOf` of its
family. -/
theorem funDimSkips_eq_funDimOf [DecidableEq d] {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (A : Arch T d L) (ι : V →L[ℝ] (Fin L → Matrix d d ℝ))
    (p : Params A dIn dOut × V) : funDimSkips A ι p = funDimOf (evalSkips A ι) p :=
  rfl

omit [Fintype dIn] in
/-- **Proof of Theorem A.5 (ii), "the two networks the same functional dimension", for any two
families:** if `F₁ q = F₂ (Φ q)` for `q` near `p`, `Φ` is differentiable at `p`, and
`F₂ y = F₁ (s y)` for `y` near `Φ p` with `s` differentiable at `Φ p` and `s (Φ p) = p`, then
`F₁` at `p` and `F₂` at `Φ p` have the same functional dimension. -/
theorem funDimOf_eq_of_comp_of_section {P₁ P₂ : Type*} [NormedAddCommGroup P₁]
    [NormedSpace ℝ P₁] [NormedAddCommGroup P₂] [NormedSpace ℝ P₂]
    {F₁ : P₁ → Matrix T dIn ℝ → Matrix T dOut ℝ} {F₂ : P₂ → Matrix T dIn ℝ → Matrix T dOut ℝ}
    {Φ : P₁ → P₂} {s : P₂ → P₁} {p : P₁} (hΦ : DifferentiableAt ℝ Φ p)
    (hs : DifferentiableAt ℝ s (Φ p)) (hsp : s (Φ p) = p)
    (hF₁ : ∀ᶠ q in 𝓝 p, F₁ q = F₂ (Φ q)) (hF₂ : ∀ᶠ y in 𝓝 (Φ p), F₂ y = F₁ (s y)) :
    funDimOf F₁ p = funDimOf F₂ (Φ p) := by
  -- on every batch the two Jacobians have the same range
  have key : ∀ (n : ℕ) (X : Fin n → Matrix T dIn ℝ),
      LinearMap.range (fderiv ℝ (fun q : P₁ => fun i : Fin n => F₁ q (X i)) p).toLinearMap
        = LinearMap.range
          (fderiv ℝ (fun y : P₂ => fun i : Fin n => F₂ y (X i)) (Φ p)).toLinearMap :=
    fun n X => range_fderiv_eq_of_comp_of_section hΦ hs hsp
      (hF₁.mono fun q hq => by simp only [hq]) (hF₂.mono fun y hy => by simp only [hy])
  unfold funDimOf
  congr 1
  ext r
  constructor
  · rintro ⟨n, X, rfl⟩
    exact ⟨n, X, by rw [key n X]⟩
  · rintro ⟨n, X, rfl⟩
    exact ⟨n, X, by rw [key n X]⟩

end Skips
