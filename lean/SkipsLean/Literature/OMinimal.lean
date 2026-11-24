import SkipsLean.Imports

/-!
# The o-minimal facts, assumed from the literature

Paper (skips paper): Appendix A.7, Definition A.20, Lemma A.21 (the outputs of the networks are
definable), Definition A.22 and Lemma A.23 (the closure of a definable set), used in the proof of
Lemma A.26 (ii): "The image `π(S)` of `π ∘ G_X` is definable and has measure zero, so its closure
has measure zero (Lemma A.23)."

We rely on the following results, which are not proved and not checked here:

* L. van den Dries, *Tame Topology and O-minimal Structures*, LMS Lecture Note Series 248 (1998):
  the image of a definable set under a definable map is definable (Chapter 1, Lemma (2.3)), cell
  decomposition (Chapter 3, Theorem (2.11)), and `dim (S̄ \ S) < dim S` for a nonempty definable set
  `S` (Chapter 4, Theorem (1.8)); hence the closure of a definable set of measure zero has measure
  zero (Lemma A.23 of the paper);
* P. Speissegger, *The Pfaffian closure of an o-minimal structure* (1997): there is an o-minimal
  structure on the real field in which `exp` and `erf`, and therefore the outputs of the networks
  of the paper as functions of their weights, are definable (Lemma A.21 of the paper).

They are formalized as the one property that the proofs use, `ClosureNullOfNull S`, of a set `S`
(in the paper: the set of outputs of the skipless networks on a finite batch). It is not an axiom:
the theorems that use it take it as a hypothesis. No o-minimal structure is defined in Lean.
-/

namespace Skips

open MeasureTheory

/-- **The property of a definable set that Lemma A.26 (ii) uses, as a hypothesis from the
literature:** for every linear map `π` to some `ℝ^r`, if the image `π(S)` has measure zero, then
its closure has measure zero. (For a definable `S` this is Lemma A.23 of the skips paper applied to
the definable set `π(S)`.) -/
def ClosureNullOfNull {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] (S : Set Y) : Prop :=
  ∀ (r : ℕ) (π : Y →L[ℝ] (Fin r → ℝ)), volume (π '' S) = 0 → volume (closure (π '' S)) = 0

end Skips
