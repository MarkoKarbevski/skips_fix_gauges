import Mathlib.Analysis.Matrix.Normed
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Analysis.Normed.Group.Basic

/-!
# Pointwise limits of a set of networks

Paper (skips paper): Definition A.29 (Pointwise limit), used in Theorem 4.11 and in
Theorem A.28 (iv). "Let `𝒳 = ℝ^{T × d_in}` be the set of inputs, and let `ℱ` be a set of networks
with inputs in `𝒳`. A network `F` is a pointwise limit of `ℱ` if

`∀ n ≥ 1, ∀ (x_1, …, x_n) ∈ 𝒳ⁿ, ∀ δ > 0, ∃ F' ∈ ℱ, ∀ i ∈ {1, …, n} : ‖F'(x_i) - F(x_i)‖ < δ`.

The network `F'` may depend on `n`, on `(x_1, …, x_n)` and on `δ`. If a sequence of networks of
`ℱ` converges to `F` at every input, then `F` is a pointwise limit of `ℱ`."

A network is its function `ℝ^{T × d_in} → ℝ^{T × d_out}`; the norm of a matrix is the largest
absolute value of its entries (the definition does not depend on the norm).
-/

namespace Skips

open Matrix Filter Topology
open scoped Matrix.Norms.Elementwise

variable {T dIn dOut : Type*} [Fintype T] [Fintype dOut]

/-- **Definition A.29 of the skips paper (pointwise limit).** `F` is a pointwise limit of the set
`𝓕` of functions if on every finite batch of inputs and for every `δ > 0`, some function of `𝓕`
is `δ`-close to `F` at every input of the batch. -/
def IsPointwiseLimit (𝓕 : Set (Matrix T dIn ℝ → Matrix T dOut ℝ))
    (F : Matrix T dIn ℝ → Matrix T dOut ℝ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ X : Fin n → Matrix T dIn ℝ, ∀ δ : ℝ, 0 < δ →
    ∃ F' ∈ 𝓕, ∀ i, ‖F' (X i) - F (X i)‖ < δ

/-- **After Definition A.29:** "If a sequence of networks of `ℱ` converges to `F` at every input,
then `F` is a pointwise limit of `ℱ`." -/
theorem isPointwiseLimit_of_tendsto {𝓕 : Set (Matrix T dIn ℝ → Matrix T dOut ℝ)}
    {F : Matrix T dIn ℝ → Matrix T dOut ℝ} (G : ℕ → Matrix T dIn ℝ → Matrix T dOut ℝ)
    (hG : ∀ k, G k ∈ 𝓕) (h : ∀ x, Tendsto (fun k => G k x) atTop (𝓝 (F x))) :
    IsPointwiseLimit 𝓕 F := by
  intro n _ X δ hδ
  -- at each input of the batch the sequence is eventually `δ`-close to `F`; finitely many inputs
  have h1 : ∀ i : Fin n, ∀ᶠ k in atTop, ‖G k (X i) - F (X i)‖ < δ := fun i => by
    have := (Metric.tendsto_nhds.1 (h (X i))) δ hδ
    simpa [dist_eq_norm] using this
  obtain ⟨k, hk⟩ := (eventually_all.2 h1).exists
  exact ⟨G k, hG k, hk⟩

/-- **Theorem A.28 (iv) of the skips paper, "So `F` is not a pointwise limit of these skipless
networks":** if on one finite batch some `δ > 0` has, for every function `F'` of `𝓕`,
`‖F'(x) - F(x)‖ ≥ δ` at some input `x` of the batch, then `F` is not a pointwise limit of `𝓕`. -/
theorem not_isPointwiseLimit_of_exists_pos {𝓕 : Set (Matrix T dIn ℝ → Matrix T dOut ℝ)}
    {F : Matrix T dIn ℝ → Matrix T dOut ℝ} {n : ℕ} (X : Fin n → Matrix T dIn ℝ) {δ : ℝ}
    (hδ : 0 < δ) (h : ∀ F' ∈ 𝓕, ∃ i, δ ≤ ‖F' (X i) - F (X i)‖) :
    ¬ IsPointwiseLimit 𝓕 F := by
  intro hlim
  rcases Nat.eq_zero_or_pos n with hn | hn
  · -- an empty batch: the hypothesis says that `𝓕` is empty, and a limit needs a member of `𝓕`
    subst hn
    obtain ⟨F', hF', -⟩ := hlim 1 le_rfl (fun _ => 0) 1 one_pos
    obtain ⟨i, -⟩ := h F' hF'
    exact i.elim0
  · obtain ⟨F', hF', hclose⟩ := hlim n hn X δ hδ
    obtain ⟨i, hi⟩ := h F' hF'
    exact absurd (hclose i) (not_lt.2 hi)

end Skips
