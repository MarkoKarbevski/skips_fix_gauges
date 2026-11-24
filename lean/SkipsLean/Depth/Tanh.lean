import SkipsLean.Depth.StepTanh
import SkipsLean.Generic.Params

/-!
# Theorem 5.2 (i) without normalization: `tanh` blocks at any depth

Paper (dimension paper): Theorem 5.2 (i), the case without normalization, and its proof in
Appendix D.7 ("The parts together", first paragraph).

A network of `L` `tanh` blocks without skip connections, without normalization and without biases,
with `d_in, d_out ≥ d` and at least `d` hidden units in every block, has the functional dimension
`P - (L + 1) d²` at generic parameters.

The proof of the paper takes `θ` with: (R1) `E`, `D` and every write of rank `d`; for every block
(T1) no row of the write vanishes and (T2) the columns of the read are linearly independent over
`ℚ`; and every `W_read W_write` invertible. Such `θ` are regular (the derivative of a block at `0`
is `v ↦ v W_read W_write`). Claim `(D_L)` holds (Lemma D.5), the step of Lemma D.7 gives `(D_k)`
for `k = L - 1, …, 0`, and Proposition D.4 gives the functional dimension. The conditions fail only
on a set of measure zero; (T2) fails on countably many proper linear subspaces.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]

/-- The conditions on the parameters of a network of `tanh` blocks that the proof of
Theorem 5.2 (i) uses in the case without normalization. -/
structure TanhDepthGeneric (θ : Params (Arch.mlp (T := T) (d := d) Real.tanh id hid) dIn dOut) :
    Prop where
  /-- (R1) -/
  rank_E : θ.E.rank = Fintype.card d
  /-- (R1) -/
  rank_D : θ.D.rank = Fintype.card d
  /-- (R1) -/
  rank_write : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d
  /-- (T1): no row of a write vanishes -/
  write_row_ne_zero : ∀ ℓ (i : hid ℓ), θ.write ℓ i ≠ 0
  /-- (T2): the columns of every read are linearly independent over `ℚ` -/
  read_cols_indep : ∀ ℓ, LinearIndependent ℚ (fun j : hid ℓ => fun i : d => θ.read ℓ i j)
  /-- every `W_read W_write` is invertible -/
  read_mul_write : ∀ ℓ, IsUnit (θ.read ℓ * θ.write ℓ).det

variable (θ : Params (Arch.mlp (T := T) (d := d) Real.tanh id hid) dIn dOut)

/-- Under the conditions `θ` is regular: the derivative of block `ℓ` at `0` is
`v ↦ v W_read W_write`, which is injective. -/
theorem regular_of_tanhDepthGeneric (hθ : TanhDepthGeneric θ) :
    Regular (Arch.mlp Real.tanh id hid) θ := by
  sorry

/-- Under the conditions Claim `(D_k)` holds at every hidden state: `(D_L)` by Lemma D.5, and then
`(D_k)` for `k = L - 1, …, 0` by Lemma D.7. -/
theorem claim_of_tanhDepthGeneric [Nonempty T] (hθ : TanhDepthGeneric θ) (k : Fin (L + 1)) :
    Claim (Arch.mlp Real.tanh id hid) θ k := by
  sorry

/-- **Theorem 5.2 (i) without normalization, under the conditions of its proof:** the functional
dimension of a network of `L` `tanh` blocks is `P - (L + 1) d²`. -/
theorem funDim_tanh_skipless [Nonempty T] (hθ : TanhDepthGeneric θ) :
    funDim (Arch.mlp Real.tanh id hid) 0 θ + (L + 1) * Fintype.card d ^ 2
      = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) Real.tanh id hid) dIn dOut) := by
  sorry

/-- The conditions hold at generic parameters, when `d_in, d_out ≥ d ≥ 1` and every block has at
least `d` hidden units. -/
theorem ae_tanhDepthGeneric [Nonempty d]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) Real.tanh id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, TanhDepthGeneric θ := by
  sorry

/-- **Theorem 5.2 (i), the case without normalization:** a network of `L` `tanh` blocks without
skip connections, without normalization and without biases, with `d_in, d_out ≥ d ≥ 2` and at
least `d` hidden units in every block, has the functional dimension `P - (L + 1) d²` at generic
parameters. (The proof uses `d ≥ 1` only.) -/
theorem ae_funDim_tanh_skipless [Nonempty T]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) Real.tanh id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, funDim (Arch.mlp Real.tanh id hid) 0 θ + (L + 1) * Fintype.card d ^ 2
      = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) Real.tanh id hid) dIn dOut) := by
  sorry

end Skips
