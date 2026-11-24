import SkipsLean.Imports

/-!
# Invariance of domain, assumed from the literature

Paper (skips paper): Appendix A.8, proof of Proposition A.32 (i): "By invariance of domain, an
injective continuous map of `ℝ^{d_model}` to itself is open." The paper names the theorem and
gives no reference.

We rely on the result "if `U` is an open subset of `ℝ^n` and `f : U → ℝ^n` is an injective
continuous map, then `f(U)` is open in `ℝ^n` and `f` is a homeomorphism between `U` and `f(U)`"
(invariance of domain), due to L. E. J. Brouwer, *Beweis der Invarianz des n-dimensionalen
Gebiets*, Math. Ann. 71 (1912), 305–315. The statement and the reference are taken from the
article "Invariance of domain" of Wikipedia (read on 24 November 2026); Brouwer's paper itself was
not read. It is formalized as `InvarianceOfDomain` below, in the case `U = ℝ^n` that the paper
uses: an injective continuous map of `ℝ^n` to itself is an open map.

It is not proved here, and it is not an axiom: the theorems that use it take it as a hypothesis.
Mathlib (v4.36.0) does not have it: a search of the pinned sources for "invariance of domain",
"invarianceOfDomain", "Brouwer" and "Borsuk" finds no such statement (24 November 2026).
-/

namespace Skips

/-- **Invariance of domain for maps of `ℝ^n` to itself, as a hypothesis from the literature:** an
injective continuous map `(n → ℝ) → (n → ℝ)` is an open map. -/
def InvarianceOfDomain (n : Type*) [Fintype n] : Prop :=
  ∀ f : (n → ℝ) → (n → ℝ), Continuous f → Function.Injective f → IsOpenMap f

end Skips
