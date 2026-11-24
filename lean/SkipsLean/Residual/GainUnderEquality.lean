import SkipsLean.Generic.Params

/-!
# The gain of the skips under the two equality conditions

Paper (skips paper), Theorem A.17 (iii): "If in addition both networks satisfy the equality
condition, the skips raise the functional dimension by exactly `L dim G`, which is `L d_model²`
without normalization." Part (ii) gives the two bounds `P − (L + 1) dim G − s` without skips and
`P − dim G − s` with them, and a network satisfies the equality condition if its bound is
attained at generic parameters (Definition 4.4 of the dimension paper, Section 4.1 of the skips
paper).

Here part (iii) as it is: for any architecture, any number `g` for `dim G` and any number `s`, if
the two bounds are attained, the functional dimension of the residual network is that of the
skipless network plus `L g`; at one parameter, and at almost every parameter when both equalities
hold at almost every parameter. The equalities themselves are the theorems on the functional
dimension of each kind of network.
-/

namespace Skips

open MeasureTheory

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]

omit [Fintype T] in
/-- **Theorem A.17 (iii) of the skips paper, at one parameter:** if the bound without skips,
`fd = P − (L + 1) g − s`, and the bound with identity skips, `fd = P − g − s`, are both attained
at `θ`, the skips raise the functional dimension by exactly `L g`. -/
theorem funDim_residual_eq_skipless_add_of_equality (A : Arch T d L) (θ : Params A dIn dOut)
    (g s : ℕ)
    (h0 : funDim A 0 θ + ((L + 1) * g + s) = Module.finrank ℝ (Params A dIn dOut))
    (h1 : funDim A 1 θ + (g + s) = Module.finrank ℝ (Params A dIn dOut)) :
    funDim A 1 θ = funDim A 0 θ + L * g := by
  have h : (L + 1) * g = L * g + g := by ring
  omega

omit [Fintype T] in
/-- **Theorem A.17 (iii) of the skips paper:** if both networks satisfy the equality condition
(the two bounds are attained at almost every parameter), then at almost every parameter the
skips raise the functional dimension by exactly `L g`. -/
theorem ae_funDim_residual_eq_skipless_add_of_equality (A : Arch T d L) (g s : ℕ)
    (μ : Measure (Params A dIn dOut))
    (h0 : ∀ᵐ θ ∂μ, funDim A 0 θ + ((L + 1) * g + s) = Module.finrank ℝ (Params A dIn dOut))
    (h1 : ∀ᵐ θ ∂μ, funDim A 1 θ + (g + s) = Module.finrank ℝ (Params A dIn dOut)) :
    ∀ᵐ θ ∂μ, funDim A 1 θ = funDim A 0 θ + L * g := by
  filter_upwards [h0, h1] with θ h0 h1
  exact funDim_residual_eq_skipless_add_of_equality A θ g s h0 h1

end Skips
