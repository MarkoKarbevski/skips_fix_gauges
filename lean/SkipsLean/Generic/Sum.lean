import SkipsLean.Symmetry.InsideBlocksSum
import SkipsLean.Generic.Params
import Mathlib.MeasureTheory.Measure.Haar.Disintegration

/-!
# Generic parameters of a network with two kinds of block

Papers: "A statement holds at generic parameters if it holds outside a set of Lebesgue measure
zero" (Section 2 of the dimension paper and of the skips paper).

The parameters of a network of `A.sum B` (`Network/Sum.lean`) are, up to a linear change of
coordinates, the parameters of a network of `A` together with the reads and the writes of `B`.
So a condition on the first part `θ.sumFst` that holds at generic parameters of `A` holds at
generic parameters of the sum, and likewise for the second part: the preimage of a null set under
a surjective linear map is a null set (Fubini). This carries the conditions of the proofs for
networks of one kind of block (`ae_smallWritesGenericAttention`, `ae_smallWritesGeneric`, …) to
networks of attention blocks and MLP blocks.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut] {A B : Arch T d L}

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the first part of the parameters of the sum, as a linear map. -/
private def sumFstLin_gsm : Params (A.sum B) dIn dOut →ₗ[ℝ] Params A dIn dOut where
  toFun θ := θ.sumFst
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the second part of the parameters of the sum, as a linear map. -/
private def sumSndLin_gsm : Params (A.sum B) dIn dOut →ₗ[ℝ] Params B dIn dOut where
  toFun θ := θ.sumSnd
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the first part is onto: `sumInl η` has first part `η`. -/
private theorem sumFstLin_surjective_gsm :
    Function.Surjective (sumFstLin_gsm (A := A) (B := B) (dIn := dIn) (dOut := dOut)) :=
  fun η => ⟨Params.sumInl η, Params.ext' rfl (fun _ => Matrix.ext fun _ _ => rfl)
    (fun _ => Matrix.ext fun _ _ => rfl) rfl⟩

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the second part is onto: `sumInr η` has second part `η`. -/
private theorem sumSndLin_surjective_gsm :
    Function.Surjective (sumSndLin_gsm (A := A) (B := B) (dIn := dIn) (dOut := dOut)) :=
  fun η => ⟨Params.sumInr η, Params.ext' rfl (fun _ => Matrix.ext fun _ _ => rfl)
    (fun _ => Matrix.ext fun _ _ => rfl) rfl⟩

omit [Fintype T] [DecidableEq d] in
/-- Helper: the preimage of a null set under an onto linear map between parameter spaces is a
null set. A condition that holds almost everywhere fails on a measurable null set `N`; the
condition holds outside `N`, and the preimage of `Nᶜ` has full measure. -/
private theorem ae_comp_of_surjective_gsm {A' : Arch T d L}
    (μ : Measure (Params (A.sum B) dIn dOut)) [μ.IsAddHaarMeasure]
    (Φ : Params (A.sum B) dIn dOut →ₗ[ℝ] Params A' dIn dOut) (hΦ : Function.Surjective Φ)
    {p : Params A' dIn dOut → Prop}
    (hp : ∀ᵐ θ ∂(Measure.addHaar : Measure (Params A' dIn dOut)), p θ) :
    ∀ᵐ θ ∂μ, p (Φ θ) := by
  rw [ae_iff] at hp
  obtain ⟨N, hsub, hN, hN0⟩ := exists_measurable_superset_of_null hp
  have hc : ∀ᵐ y ∂(Measure.addHaar : Measure (Params A' dIn dOut)), y ∈ Nᶜ :=
    measure_eq_zero_iff_ae_notMem.1 hN0
  have h := (ae_comp_linearMap_mem_iff Φ μ Measure.addHaar hΦ hN.compl).2 hc
  refine h.mono fun θ hθ => ?_
  by_contra hn
  exact hθ (hsub hn)

omit [Fintype T] [DecidableEq d] in
/-- **A condition that holds at generic parameters of `A` holds for the first part of generic
parameters of `A.sum B`.** -/
theorem ae_sumFst (μ : Measure (Params (A.sum B) dIn dOut)) [μ.IsAddHaarMeasure]
    {p : Params A dIn dOut → Prop}
    (hp : ∀ᵐ θ ∂(Measure.addHaar : Measure (Params A dIn dOut)), p θ) :
    ∀ᵐ θ ∂μ, p θ.sumFst :=
  ae_comp_of_surjective_gsm μ sumFstLin_gsm sumFstLin_surjective_gsm hp

omit [Fintype T] [DecidableEq d] in
/-- **A condition that holds at generic parameters of `B` holds for the second part of generic
parameters of `A.sum B`.** -/
theorem ae_sumSnd (μ : Measure (Params (A.sum B) dIn dOut)) [μ.IsAddHaarMeasure]
    {p : Params B dIn dOut → Prop}
    (hp : ∀ᵐ θ ∂(Measure.addHaar : Measure (Params B dIn dOut)), p θ) :
    ∀ᵐ θ ∂μ, p θ.sumSnd :=
  ae_comp_of_surjective_gsm μ sumSndLin_gsm sumSndLin_surjective_gsm hp

end Skips
