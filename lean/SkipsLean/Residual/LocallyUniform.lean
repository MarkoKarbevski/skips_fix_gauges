import SkipsLean.Residual.PointwiseLimit
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

/-!
# Locally uniform approximation and pointwise limits

Paper (skips paper): Theorem 4.11 (i), last sentence: "In particular, it cannot be locally
uniformly approximated by such networks." Section 4.3: "A network `F` is a pointwise limit of a
set of networks if, on every finite set of inputs, networks of the set come arbitrarily close to
`F` (Definition A.29). This is the case when a sequence of them converges to `F` uniformly on
compact sets of inputs."

So "is not a pointwise limit of such networks" contains "cannot be locally uniformly approximated
by such networks": a sequence of networks of the set that converges to `F` locally uniformly, or
uniformly on every compact set of inputs, converges at every input, and then `F` is a pointwise
limit of the set (`isPointwiseLimit_of_tendsto`, `Residual/PointwiseLimit.lean`). Stated here for
any set `𝓕` of functions; with the theorems `ae_not_isPointwiseLimit_skipless_…` it gives the
last sentence of Theorem 4.11 (i) for each kind of block.
-/

namespace Skips

open Matrix Filter Topology
open scoped Matrix.Norms.Elementwise

variable {T dIn dOut : Type*} [Fintype T] [Fintype dOut]

/-- **Section 4.3 of the skips paper:** if a sequence of networks of `𝓕` converges to `F`
uniformly on every compact set of inputs, then `F` is a pointwise limit of `𝓕`. -/
theorem isPointwiseLimit_of_tendstoUniformlyOn_isCompact
    {𝓕 : Set (Matrix T dIn ℝ → Matrix T dOut ℝ)} {F : Matrix T dIn ℝ → Matrix T dOut ℝ}
    (G : ℕ → Matrix T dIn ℝ → Matrix T dOut ℝ) (hG : ∀ k, G k ∈ 𝓕)
    (h : ∀ K : Set (Matrix T dIn ℝ), IsCompact K → TendstoUniformlyOn G F atTop K) :
    IsPointwiseLimit 𝓕 F :=
  -- a point is a compact set
  isPointwiseLimit_of_tendsto G hG fun x =>
    (h {x} isCompact_singleton).tendsto_at (Set.mem_singleton x)

/-- If a sequence of networks of `𝓕` converges to `F` locally uniformly, then `F` is a pointwise
limit of `𝓕`. -/
theorem isPointwiseLimit_of_tendstoLocallyUniformly
    {𝓕 : Set (Matrix T dIn ℝ → Matrix T dOut ℝ)} {F : Matrix T dIn ℝ → Matrix T dOut ℝ}
    (G : ℕ → Matrix T dIn ℝ → Matrix T dOut ℝ) (hG : ∀ k, G k ∈ 𝓕)
    (h : TendstoLocallyUniformly G F atTop) : IsPointwiseLimit 𝓕 F :=
  isPointwiseLimit_of_tendsto G hG fun x =>
    (tendstoLocallyUniformlyOn_univ.2 h).tendsto_at (Set.mem_univ x)

/-- **Theorem 4.11 (i) of the skips paper, last sentence, "In particular, it cannot be locally
uniformly approximated by such networks":** a function that is not a pointwise limit of `𝓕` is
not the locally uniform limit of a sequence of functions of `𝓕`. -/
theorem not_tendstoLocallyUniformly_of_not_isPointwiseLimit
    {𝓕 : Set (Matrix T dIn ℝ → Matrix T dOut ℝ)} {F : Matrix T dIn ℝ → Matrix T dOut ℝ}
    (hF : ¬ IsPointwiseLimit 𝓕 F) (G : ℕ → Matrix T dIn ℝ → Matrix T dOut ℝ)
    (hG : ∀ k, G k ∈ 𝓕) : ¬ TendstoLocallyUniformly G F atTop :=
  fun h => hF (isPointwiseLimit_of_tendstoLocallyUniformly G hG h)

/-- The same for convergence that is uniform on every compact set of inputs. -/
theorem not_tendstoUniformlyOn_isCompact_of_not_isPointwiseLimit
    {𝓕 : Set (Matrix T dIn ℝ → Matrix T dOut ℝ)} {F : Matrix T dIn ℝ → Matrix T dOut ℝ}
    (hF : ¬ IsPointwiseLimit 𝓕 F) (G : ℕ → Matrix T dIn ℝ → Matrix T dOut ℝ)
    (hG : ∀ k, G k ∈ 𝓕) :
    ¬ ∀ K : Set (Matrix T dIn ℝ), IsCompact K → TendstoUniformlyOn G F atTop K :=
  fun h => hF (isPointwiseLimit_of_tendstoUniformlyOn_isCompact G hG h)

end Skips
