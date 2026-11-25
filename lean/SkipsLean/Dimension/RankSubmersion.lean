import SkipsLean.Imports

/-!
# The rank of a Jacobian after a change of parameters whose derivative is onto

Paper (skips paper), proof of Theorem A.5 (ii): "For every batch of inputs, the Jacobian of the
mixed network at `θ` is the Jacobian of the residual network at `Φ(θ)` times the derivative of
`Φ`, by the chain rule; a matrix times a matrix that is onto has the rank of the first, so the
two Jacobians have the same rank, and the two networks the same functional dimension."

Here this step once, for any maps (it serves the networks of mixed blocks, the networks with
learned skips, and both with biases): if `f = g ∘ Φ` near `p`, the derivative of `Φ` at `p` is
onto, and `g = f ∘ s` near `Φ(p)` for a map `s` that is differentiable at `Φ(p)` with
`s(Φ(p)) = p`, then the derivatives of `f` at `p` and of `g` at `Φ(p)` have the same range.
The map `s` makes the statement hold with Lean's convention that the derivative is `0` where it
does not exist, with no differentiability asked of `f` or `g`: they are differentiable at `p`
and at `Φ(p)` together. For the gauge fix, `s(θ') = T_{G,K}^{-1}(θ', I, I)`.
-/

namespace Skips

open Filter Topology

/-- **Proof of Theorem A.5 (ii), the chain rule step:** if `f = g ∘ Φ` near `p`, `Φ` has a
derivative at `p` that is onto, and `g = f ∘ s` near `Φ p` for a map `s` differentiable at `Φ p`
with `s (Φ p) = p`, then the derivative of `f` at `p` and the derivative of `g` at `Φ p` have the
same range. -/
theorem range_fderiv_eq_of_comp_of_section {E F G : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G]
    [NormedSpace ℝ G] {f : E → G} {g : F → G} {Φ : E → F} {s : F → E} {p : E} {Φ' : E →L[ℝ] F}
    (hΦ : HasFDerivAt Φ Φ' p) (hsurj : Function.Surjective Φ')
    (hs : DifferentiableAt ℝ s (Φ p)) (hsp : s (Φ p) = p)
    (hf : ∀ᶠ q in 𝓝 p, f q = g (Φ q)) (hg : ∀ᶠ y in 𝓝 (Φ p), g y = f (s y)) :
    LinearMap.range (fderiv ℝ f p).toLinearMap
      = LinearMap.range (fderiv ℝ g (Φ p)).toLinearMap := by
  by_cases hgd : DifferentiableAt ℝ g (Φ p)
  · -- the chain rule: `Df(p) = Dg(Φ p) ∘ Φ'`, and `Φ'` is onto
    have hcomp : HasFDerivAt (fun q => g (Φ q)) ((fderiv ℝ g (Φ p)).comp Φ') p :=
      hgd.hasFDerivAt.comp p hΦ
    have h1 : fderiv ℝ f p = (fderiv ℝ g (Φ p)).comp Φ' :=
      (hcomp.congr_of_eventuallyEq hf).fderiv
    rw [h1]
    ext y
    constructor
    · rintro ⟨η, rfl⟩
      exact ⟨Φ' η, rfl⟩
    · rintro ⟨z, rfl⟩
      obtain ⟨η, rfl⟩ := hsurj z
      exact ⟨η, rfl⟩
  · -- `g = f ∘ s` near `Φ p`: if `f` were differentiable at `p = s (Φ p)`, `g` would be at `Φ p`
    have hfd : ¬ DifferentiableAt ℝ f p := by
      intro hfd
      apply hgd
      have hf' : DifferentiableAt ℝ f (s (Φ p)) := by
        rw [hsp]
        exact hfd
      have hfs : DifferentiableAt ℝ (fun y => f (s y)) (Φ p) := hf'.comp (Φ p) hs
      exact hfs.congr_of_eventuallyEq hg
    -- both derivatives are `0`
    rw [fderiv_zero_of_not_differentiableAt hfd, fderiv_zero_of_not_differentiableAt hgd]
    ext y
    simp

end Skips
