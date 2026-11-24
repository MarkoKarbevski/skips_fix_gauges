import SkipsLean.Network.Blocks

/-!
# Real-analytic blocks

Papers: Section 2 ("the maps `f_ℓ` are real-analytic" for the kinds of block of the main results).
Appendix D of the dimension paper uses that the network after a hidden state is real-analytic in
the hidden state. Stated here: `tanh` is real-analytic, and the map of an MLP block is real-analytic
if its activation is.
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise

/-- `tanh` is real-analytic (`tanh = sinh / cosh` and `cosh > 0`). -/
theorem analyticOnNhd_tanh : AnalyticOnNhd ℝ Real.tanh Set.univ := by
  have h : Real.tanh = fun z => Real.sinh z / Real.cosh z := by
    funext z; exact Real.tanh_eq_sinh_div_cosh z
  rw [h]
  exact Real.analyticOnNhd_sinh.div Real.analyticOnNhd_cosh fun z _ => (Real.cosh_pos z).ne'

variable {T d : Type*} {L : ℕ} [Fintype T] {σ : ℝ → ℝ} {χ : Matrix T d ℝ → Matrix T d ℝ}
  {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]

/-- An entry of a matrix is a real-analytic (linear) function of the matrix. -/
theorem analyticOnNhd_matrix_entry {m n : Type*} [Fintype m] [Fintype n] (t : m) (i : n) :
    AnalyticOnNhd ℝ (fun M : Matrix m n ℝ => M t i) Set.univ :=
  ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : n => ℝ) i).comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : m => n → ℝ) t)).analyticOnNhd _

/-- The map of an MLP block is real-analytic if its activation is. -/
theorem analyticOnNhd_f_mlp (hσ : AnalyticOnNhd ℝ σ Set.univ) (ℓ : Fin L) :
    AnalyticOnNhd ℝ ((Arch.mlp (T := T) (d := d) σ χ hid).f ℓ) Set.univ := by
  show AnalyticOnNhd ℝ (fun M : Matrix T (hid ℓ) ℝ => fun t => fun i => σ (M t i)) Set.univ
  exact AnalyticOnNhd.pi fun t => AnalyticOnNhd.pi fun i =>
    hσ.comp (analyticOnNhd_matrix_entry t i) (Set.mapsTo_univ _ _)

end Skips
