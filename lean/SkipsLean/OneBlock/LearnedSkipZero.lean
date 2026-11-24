import SkipsLean.OneBlock.LearnedSkip

/-!
# One block with learned skips under pre-RMSNorm, at the skip `0`

Paper (skips paper): Theorem 4.6 (ii) and Theorem B.1 (iii) (the learned skip); the definitions and
the route are in `OneBlock/LearnedSkip.lean`. This file has the step at the skip `A = 0`, which is
not in the paper: there the network is the skipless network `x ↦ N_ε(f(N_ε(x E) W_read) W_write) D`,
and a flat direction `(η, a)` of the family with the skips `ι v` has `a = 0`. (For the inputs `t x`
with all rows of `x E` nonzero, as `t → ∞`: the input `N_ε(t x E)` of the block converges, so the
hidden state `g(t x)` and its derivative along `η` stay bounded, while the derivative along `a` is
`t · DN_ε(g(t x)) (x E (ι a)) D`; so `DN_ε(g_∞) (x E (ι a)) D = 0`; `D` has rank `d`, the derivative
of `N_ε` is injective for `ε > 0`, `E` has rank `d` and `ι` is injective.) So the flat directions
are those of the skipless network, and the functional dimension is that of the skipless network
plus `dim V` (`funDimSkips_add_finrank_flatSkips`, `funDim_add_finrank_flat'`).
-/

namespace Skips

open Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- **One block under pre-RMSNorm (`ε > 0`), at the skip `0`:** for a real-analytic block, `E` and
`D` of rank `d` and an injective `ι`, the family with the skips `ι v` has at `(θ, 0)` at least the
functional dimension of the skipless network at `θ` plus the dimension of `V`. -/
theorem funDim_add_finrank_le_funDimSkips_zero [Nonempty T] [FiniteDimensional ℝ V]
    {A : Arch T d 1} {ε : ℝ} (hε : 0 < ε) (hA : A.χ = rmsNorm ε)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ)
    (ι : V →L[ℝ] (Fin 1 → Matrix d d ℝ)) (hι : Function.Injective ι)
    (θ : Params A dIn dOut) (hE : θ.E.rank = Fintype.card d) (hD : θ.D.rank = Fintype.card d) :
    funDim A 0 θ + Module.finrank ℝ V ≤ funDimSkips A ι (θ, 0) := by
  sorry

end Skips
