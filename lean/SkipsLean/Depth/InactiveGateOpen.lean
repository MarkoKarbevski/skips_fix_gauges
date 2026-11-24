import SkipsLean.Depth.InactiveGate
import SkipsLean.Activations.ReLU

/-!
# ReGLU blocks: an open set of weights on which a gate is closed at every input

Paper (dimension paper): Appendix E, proof of Proposition E.1, the part "ReGLU":

"ReGLU. The gate of the hidden unit of block 2 reads `z(u) = ∑_k ReLU(u c_k) (u e_k) a_k r`, and
the sign of a term depends on the value `u e_k`. We choose weights at which every gate of block 1
opens where its value is positive. Let `q` be the number of hidden units of block 1 and
`0 < δ < 1/(q d_model)`. For every `k` choose an index `i(k) ≤ d_model`, with every index chosen by
some `k`. Let `c_k` have the entry `1` at `i(k)` and zeros elsewhere, let `e_k` have the entry `1`
at `i(k)` and `−δ` elsewhere, and let `a_k r = −1` for all `k`. Then
`z(u) = −∑_k ReLU(u_{i(k)}) (u_{i(k)} − δ ∑_{j ≠ i(k)} u_j)
  ≤ −(1 − δ q d_model) ∑_{i : u_i > 0} u_i²`,
so `z(u) < 0` if `u` has a positive entry, and `z(u) = 0` if it has none. Suppose that, at weights
that converge to these, the gate of the hidden unit of block 2 is positive at unit rows `u_n`, and
let `u` be a limit of the `u_n`. Then `z(u) ≥ 0`, so `u` has no positive entry. For large `n`, a
hidden unit `k` with `u_{i(k)} < 0` has a closed gate at `u_n`. A hidden unit `k` with
`u_{i(k)} = 0` has a positive value at `u_n`, since its value at `u` is `−δ ∑_{j ≠ i(k)} u_j > 0`,
so its term is not positive. Hence the gate is not positive at `u_n`, a contradiction. The function
`z` is positively homogeneous in `u`, so at all weights close to the chosen ones the gate is
positive at no input."

Stated here: for a network of ReGLU blocks `Fin (L + 1)`, a block `ℓ.succ` after the first and a
hidden unit `j` of it, if the block before has at least `d` hidden units, there is a nonempty open
set of weights on which the gate of the hidden unit is closed at every input
(`GateInactive`, `Depth/InactiveGate.lean`). The paper's block 1 and block 2 are `ℓ.castSucc` and
`ℓ.succ`.
-/

namespace Skips

open Matrix Filter Topology
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {hid : Fin (L + 1) → Type} [∀ ℓ, Fintype (hid ℓ)] [∀ ℓ, DecidableEq (hid ℓ)]

/-- Helper: the number `u ⬝ᵥ c_k` that the gate of hidden unit `k` of block `m` reads at a row
`u`. -/
private def gate_igo (m : Fin (L + 1)) (k : hid m)
    (θ : Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut) (u : d → ℝ) : ℝ :=
  ∑ b, u b * θ.read m b (Sum.inl k)

/-- Helper: the value `u ⬝ᵥ e_k` of hidden unit `k` of block `m` at a row `u`. -/
private def val_igo (m : Fin (L + 1)) (k : hid m)
    (θ : Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut) (u : d → ℝ) : ℝ :=
  ∑ b, u b * θ.read m b (Sum.inr k)

/-- Helper: the paper's `a_k r`, the write row of hidden unit `k` of block `ℓ.castSucc` times the
gate column of hidden unit `j` of block `ℓ.succ`. -/
private def out_igo (ℓ : Fin L) (j : hid ℓ.succ) (k : hid ℓ.castSucc)
    (θ : Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut) : ℝ :=
  ∑ a, θ.write ℓ.castSucc k a * θ.read ℓ.succ a (Sum.inl j)

/-- Helper: the paper's `z(u) = ∑_k ReLU(u c_k) (u e_k) a_k r`, the number that the gate of hidden
unit `j` of block `ℓ.succ` reads when the row `u` enters block `ℓ.castSucc`. -/
private noncomputable def Z_igo (ℓ : Fin L) (j : hid ℓ.succ)
    (θ : Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut) (u : d → ℝ) : ℝ :=
  ∑ k, relu (gate_igo ℓ.castSucc k θ u) * val_igo ℓ.castSucc k θ u * out_igo ℓ j k θ

omit [Fintype T] [DecidableEq d] [Fintype dOut] [∀ ℓ, DecidableEq (hid ℓ)] in
/-- Helper (step 1): the gate of hidden unit `j` of block `ℓ.succ` reads `z` of the row of the
hidden state before block `ℓ.castSucc`. -/
private theorem gate_eq_igo (ℓ : Fin L) (j : hid ℓ.succ)
    (θ : Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut) (x : Matrix T dIn ℝ)
    (t : T) :
    (hidden (Arch.gated relu id hid) 0 θ x ℓ.succ.castSucc * θ.read ℓ.succ) t (Sum.inl j)
      = Z_igo ℓ j θ (hidden (Arch.gated relu id hid) 0 θ x ℓ.castSucc.castSucc t) := by
  rw [← Fin.succ_castSucc, hidden_succ]
  set H := hidden (Arch.gated relu id hid) 0 θ x ℓ.castSucc.castSucc
  simp only [Pi.zero_apply, Matrix.mul_zero, zero_add]
  calc _ = ∑ a, (∑ k, relu (gate_igo ℓ.castSucc k θ (H t)) * val_igo ℓ.castSucc k θ (H t)
          * θ.write ℓ.castSucc k a) * θ.read ℓ.succ a (Sum.inl j) := rfl
    _ = ∑ k, ∑ a, relu (gate_igo ℓ.castSucc k θ (H t)) * val_igo ℓ.castSucc k θ (H t)
          * θ.write ℓ.castSucc k a * θ.read ℓ.succ a (Sum.inl j) := by
        simp only [Finset.sum_mul]
        exact Finset.sum_comm
    _ = _ := by
        simp only [Z_igo, out_igo, Finset.mul_sum, mul_assoc]

omit [Fintype T] [DecidableEq d] [Fintype dOut] [∀ ℓ, DecidableEq (hid ℓ)] in
/-- Helper (step 1): if `z ≤ 0` at every row, the gate of hidden unit `j` of block `ℓ.succ` is
closed at every input. -/
private theorem gateInactive_of_igo (ℓ : Fin L) (j : hid ℓ.succ)
    (θ : Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut)
    (h : ∀ u, Z_igo ℓ j θ u ≤ 0) : GateInactive θ ℓ.succ j := by
  intro x t
  rw [gate_eq_igo]
  exact h _

/-- **Proof of Proposition E.1, ReGLU:** for `d ≥ 1` and at least `d` hidden units in block
`ℓ.castSucc`, there is a nonempty open set of weights on which the gate of hidden unit `j` of the
next block `ℓ.succ` is closed at every input. -/
theorem exists_isOpen_gateInactive_reglu [Nonempty d] (ℓ : Fin L) (j : hid ℓ.succ)
    (hq : Fintype.card d ≤ Fintype.card (hid ℓ.castSucc)) :
    ∃ U : Set (Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut),
      IsOpen U ∧ U.Nonempty ∧ ∀ θ ∈ U, GateInactive θ ℓ.succ j := by
  sorry

end Skips
