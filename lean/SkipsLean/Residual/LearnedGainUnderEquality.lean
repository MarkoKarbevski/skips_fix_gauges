import SkipsLean.OneBlock.LearnedSkip
import SkipsLean.Generic.Params

/-!
# What each learned skip adds, under the equality conditions

Paper (skips paper), Theorem A.12 (iii): "What each skip adds. Under the equality condition for
the networks with learned skips, with identity skips and without skips, the functional dimension
of the network with learned skips exceeds that of the residual network by `L (d_model² − dim G)`,
and that of the residual network exceeds that of the skipless network by `L dim G`. These are
`L d_model (d_model + 1)/2` and `L d_model (d_model − 1)/2` for `ε > 0`, and
`L (d_model (d_model + 1)/2 − 1)` and `L (d_model (d_model − 1)/2 + 1)` for `ε = 0`."

Its proof: "each of the `L + 1` hidden states carries its own copy of `G`. The network with
learned skips has `L d_model²` more parameters than the residual network and `L` more copies of
`G` in its symmetry group. If both satisfy the equality condition, the difference of their
functional dimensions is therefore `L (d_model² − dim G)`".

Here the first difference as it is: for any architecture and numbers `g ≤ d²` (for `dim G`) and
`s`, if the functional dimension with full learned skips is `P + L d² − (L + 1) g − s` at almost
every weights and skips, and the functional dimension with identity skips is `P − g − s` at almost
every weights, then the first exceeds the second by `L (d² − g)`; and the two values of
`d² − g` that the paper names. The second difference is Theorem A.17 (iii),
`Residual/GainUnderEquality.lean`. The equalities themselves are the theorems on the functional
dimension of each kind of network; for one block they are the statements of Theorem B.1 (iii).
-/

namespace Skips

open MeasureTheory

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]

omit [Fintype T] in
/-- **Theorem A.12 (iii) of the skips paper, the first difference:** if both networks satisfy the
equality condition, `fd = P + L d² − (L + 1) g − s` with full learned skips and `fd = P − g − s`
with identity skips, each at almost every parameter, then the functional dimension with learned
skips exceeds that of the residual network by `L (d² − g)`. -/
theorem ae_funDimLearned_eq_residual_add_of_equality (A : Arch T d L) (g s : ℕ)
    (hg : g ≤ Fintype.card d ^ 2)
    (μ : Measure (Params A dIn dOut × (Fin L → Matrix d d ℝ))) (ν : Measure (Params A dIn dOut))
    (hl : ∀ᵐ p ∂μ, funDimLearned A p + ((L + 1) * g + s)
      = Module.finrank ℝ (Params A dIn dOut) + L * Fintype.card d ^ 2)
    (h1 : ∀ᵐ θ ∂ν, funDim A 1 θ + (g + s) = Module.finrank ℝ (Params A dIn dOut)) :
    ∀ᵐ p ∂μ, ∀ᵐ θ ∂ν, funDimLearned A p = funDim A 1 θ + L * (Fintype.card d ^ 2 - g) := by
  have h2 : L * (Fintype.card d ^ 2 - g) + L * g = L * Fintype.card d ^ 2 := by
    rw [← Nat.mul_add, Nat.sub_add_cancel hg]
  have h3 : (L + 1) * g = L * g + g := by ring
  filter_upwards [hl] with p hp
  filter_upwards [h1] with θ hθ
  omega

/-- **`d² − dim O(d) = d (d + 1)/2`:** the first difference of Theorem A.12 (iii) for `ε > 0` is
`L d (d + 1)/2`. -/
theorem sq_sub_half_mul_pred (n : ℕ) : n ^ 2 - n * (n - 1) / 2 = n * (n + 1) / 2 := by
  have h1 := Nat.two_mul_div_two_of_even (Nat.even_mul_succ_self n)
  have h2 := Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self n)
  have h3 : n * (n + 1) + n * (n - 1) = 2 * n ^ 2 := by
    cases n with
    | zero => rfl
    | succ m => rw [Nat.add_sub_cancel]; ring
  generalize n * (n + 1) = y at h1 h3 ⊢
  generalize n * (n - 1) = x at h2 h3 ⊢
  omega

/-- **`d² − dim CO(d) = d (d + 1)/2 − 1`:** the first difference of Theorem A.12 (iii) for
`ε = 0` is `L (d (d + 1)/2 − 1)`. -/
theorem sq_sub_half_mul_pred_add_one (n : ℕ) :
    n ^ 2 - (n * (n - 1) / 2 + 1) = n * (n + 1) / 2 - 1 := by
  have h := sq_sub_half_mul_pred n
  omega

end Skips
