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

omit [Fintype T] [DecidableEq d] [∀ ℓ, DecidableEq (hid ℓ)] in
/-- Helper (step 2): an entry of a read is a continuous function of the parameters (a linear
functional on a finite-dimensional space). -/
private theorem continuous_read_igo (m : Fin (L + 1)) (a : d) (c : hid m ⊕ hid m) :
    Continuous fun θ : Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut =>
      θ.read m a c :=
  ((Matrix.entryLinearMap ℝ ℝ a c).comp
    (Params.linRead (A := Arch.gated (T := T) (d := d) relu id hid) (dIn := dIn) (dOut := dOut)
      m)).continuous_of_finiteDimensional

omit [Fintype T] [DecidableEq d] [∀ ℓ, DecidableEq (hid ℓ)] in
/-- Helper (step 2): an entry of a write is a continuous function of the parameters. -/
private theorem continuous_write_igo (m : Fin (L + 1)) (k : hid m) (a : d) :
    Continuous fun θ : Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut =>
      θ.write m k a :=
  ((Matrix.entryLinearMap ℝ ℝ k a).comp
    (Params.linWrite (A := Arch.gated (T := T) (d := d) relu id hid) (dIn := dIn) (dOut := dOut)
      m)).continuous_of_finiteDimensional

/-- Helper: ReLU is continuous. -/
private theorem continuous_relu_igo : Continuous relu :=
  continuous_id.max continuous_const

omit [Fintype T] [DecidableEq d] [∀ ℓ, DecidableEq (hid ℓ)] in
/-- Helper (step 2): the gate of hidden unit `k` is continuous in the parameters and the row. -/
private theorem continuous_gate_igo (m : Fin (L + 1)) (k : hid m) :
    Continuous fun p : Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut × (d → ℝ) =>
      gate_igo m k p.1 p.2 :=
  continuous_finsetSum _ fun b _ =>
    ((continuous_apply b).comp continuous_snd).mul
      ((continuous_read_igo m b (Sum.inl k)).comp continuous_fst)

omit [Fintype T] [DecidableEq d] [∀ ℓ, DecidableEq (hid ℓ)] in
/-- Helper (step 2): the value of hidden unit `k` is continuous in the parameters and the row. -/
private theorem continuous_val_igo (m : Fin (L + 1)) (k : hid m) :
    Continuous fun p : Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut × (d → ℝ) =>
      val_igo m k p.1 p.2 :=
  continuous_finsetSum _ fun b _ =>
    ((continuous_apply b).comp continuous_snd).mul
      ((continuous_read_igo m b (Sum.inr k)).comp continuous_fst)

omit [Fintype T] [DecidableEq d] [∀ ℓ, DecidableEq (hid ℓ)] in
/-- Helper (step 2): `a_k r` is continuous in the parameters. -/
private theorem continuous_out_igo (ℓ : Fin L) (j : hid ℓ.succ) (k : hid ℓ.castSucc) :
    Continuous fun θ : Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut =>
      out_igo ℓ j k θ :=
  continuous_finsetSum _ fun a _ =>
    (continuous_write_igo ℓ.castSucc k a).mul (continuous_read_igo ℓ.succ a (Sum.inl j))

omit [Fintype T] [DecidableEq d] [∀ ℓ, DecidableEq (hid ℓ)] in
/-- Helper (step 2): `z` is continuous in the parameters and the row. -/
private theorem continuous_Z_igo (ℓ : Fin L) (j : hid ℓ.succ) :
    Continuous fun p : Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut × (d → ℝ) =>
      Z_igo ℓ j p.1 p.2 :=
  continuous_finsetSum _ fun k _ =>
    ((continuous_relu_igo.comp (continuous_gate_igo ℓ.castSucc k)).mul
      (continuous_val_igo ℓ.castSucc k)).mul ((continuous_out_igo ℓ j k).comp continuous_fst)

omit [Fintype T] [DecidableEq d] [Fintype dIn] [Fintype dOut] [∀ ℓ, DecidableEq (hid ℓ)] in
/-- Helper (step 2): `z` is positively homogeneous of degree `2` in the row. -/
private theorem Z_smul_igo (ℓ : Fin L) (j : hid ℓ.succ)
    (θ : Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut) (u : d → ℝ) {c : ℝ}
    (hc : 0 ≤ c) : Z_igo ℓ j θ (c • u) = c ^ 2 * Z_igo ℓ j θ u := by
  -- the gates and the values are linear in the row, and `ReLU (c z) = c ReLU z`
  have hg : ∀ k, gate_igo ℓ.castSucc k θ (c • u) = c * gate_igo ℓ.castSucc k θ u := fun k => by
    simp only [gate_igo, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
  have hv : ∀ k, val_igo ℓ.castSucc k θ (c • u) = c * val_igo ℓ.castSucc k θ u := fun k => by
    simp only [val_igo, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
  have hr : ∀ z, relu (c * z) = c * relu z := fun z => by
    simp only [relu]
    rw [mul_max_of_nonneg _ _ hc, mul_zero]
  simp only [Z_igo, hg, hv, hr, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- Helper (step 3): the weights `θ*`. In the read of block `ℓ.castSucc`, the gate column of
hidden unit `k` has the entry `1` at `i k` and zeros elsewhere, and its value column has the entry
`1` at `i k` and `-δ` elsewhere; every row of the write of block `ℓ.castSucc` has the entry `-1` at
`a₀` and zeros elsewhere; the gate column of hidden unit `j` of block `ℓ.succ` has the entry `1` at
`a₀` and zeros elsewhere; all other weights are `0`. -/
private noncomputable def star_igo (ℓ : Fin L) (j : hid ℓ.succ) (i : hid ℓ.castSucc → d)
    (a₀ : d) (δ : ℝ) : Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut where
  E := 0
  read := Function.update
    (Function.update (fun _ => 0) ℓ.succ
      (Matrix.of fun a c => if c = Sum.inl j ∧ a = a₀ then 1 else 0))
    ℓ.castSucc
    (Matrix.of fun a c => Sum.elim (fun k => if a = i k then 1 else 0)
      (fun k => if a = i k then 1 else -δ) c)
  write := Function.update (fun _ => 0) ℓ.castSucc (Matrix.of fun _ a => if a = a₀ then -1 else 0)
  D := 0

omit [Fintype T] [Fintype dIn] [Fintype dOut] in
/-- Helper (step 3): at `θ*` the gate of hidden unit `k` of block `ℓ.castSucc` reads `u (i k)`. -/
private theorem gate_star_igo (ℓ : Fin L) (j : hid ℓ.succ) (i : hid ℓ.castSucc → d) (a₀ : d)
    (δ : ℝ) (k : hid ℓ.castSucc) (u : d → ℝ) :
    gate_igo ℓ.castSucc k (star_igo (T := T) (dIn := dIn) (dOut := dOut) ℓ j i a₀ δ) u
      = u (i k) := by
  simp [gate_igo, star_igo, Function.update_self]

omit [Fintype T] [Fintype dIn] [Fintype dOut] in
/-- Helper (step 3): at `θ*` the value of hidden unit `k` of block `ℓ.castSucc` is
`(1 + δ) u (i k) - δ ∑_b u b`, that is `u (i k) - δ ∑_{b ≠ i k} u b`. -/
private theorem val_star_igo (ℓ : Fin L) (j : hid ℓ.succ) (i : hid ℓ.castSucc → d) (a₀ : d)
    (δ : ℝ) (k : hid ℓ.castSucc) (u : d → ℝ) :
    val_igo ℓ.castSucc k (star_igo (T := T) (dIn := dIn) (dOut := dOut) ℓ j i a₀ δ) u
      = (1 + δ) * u (i k) - δ * ∑ b, u b := by
  simp only [val_igo, star_igo, Function.update_self, Matrix.of_apply, Sum.elim_inr]
  calc ∑ b, u b * (if b = i k then 1 else -δ)
      = ∑ b, ((if b = i k then (1 + δ) * u b else 0) - δ * u b) :=
        Finset.sum_congr rfl fun b _ => by split_ifs <;> ring
    _ = _ := by
        rw [Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mul_sum]
        simp

omit [Fintype T] [Fintype dIn] [Fintype dOut] in
/-- Helper (step 3): at `θ*`, `a_k r = -1` for every hidden unit `k` of block `ℓ.castSucc`. -/
private theorem out_star_igo (ℓ : Fin L) (j : hid ℓ.succ) (i : hid ℓ.castSucc → d) (a₀ : d)
    (δ : ℝ) (k : hid ℓ.castSucc) :
    out_igo ℓ j k (star_igo (T := T) (dIn := dIn) (dOut := dOut) ℓ j i a₀ δ) = -1 := by
  have hne : ℓ.succ ≠ ℓ.castSucc := Fin.castSucc_lt_succ.ne'
  simp [out_igo, star_igo, Function.update_self, Function.update_of_ne hne]

omit [Fintype T] [Fintype dIn] [Fintype dOut] in
/-- Helper (step 3): `z` at `θ*`. -/
private theorem Z_star_igo (ℓ : Fin L) (j : hid ℓ.succ) (i : hid ℓ.castSucc → d) (a₀ : d)
    (δ : ℝ) (u : d → ℝ) :
    Z_igo ℓ j (star_igo (T := T) (dIn := dIn) (dOut := dOut) ℓ j i a₀ δ) u
      = -∑ k, relu (u (i k)) * ((1 + δ) * u (i k) - δ * ∑ b, u b) := by
  simp only [Z_igo, gate_star_igo, val_star_igo, out_star_igo, mul_neg_one,
    Finset.sum_neg_distrib]

/-- Helper (step 4): if `u` has a positive entry and `i` is onto, the sum
`∑_k ReLU(u (i k)) ((1 + δ) u (i k) - δ ∑_b u b)` is positive, for `0 < δ` and `δ q D < 1`. -/
private theorem sum_pos_igo {ι κ : Type*} [Fintype ι] [Fintype κ] (i : ι → κ)
    (hi : Function.Surjective i) (u : κ → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hδ1 : δ * Fintype.card ι * Fintype.card κ < 1) (hpos : ∃ a, 0 < u a) :
    0 < ∑ k, relu (u (i k)) * ((1 + δ) * u (i k) - δ * ∑ b, u b) := by
  -- the largest entry `M = u a' > 0`, read by the hidden unit `k'`
  obtain ⟨a₁, ha₁⟩ := hpos
  have : Nonempty κ := ⟨a₁⟩
  obtain ⟨a', ha'⟩ := Finite.exists_max u
  obtain ⟨k', hk'⟩ := hi a'
  set M := u a' with hMdef
  have hM : 0 < M := ha₁.trans_le (ha' a₁)
  set D : ℝ := (Fintype.card κ : ℝ) with hDdef
  set S := ∑ b, u b
  -- `∑_b u b ≤ D M`
  have hS : S ≤ D * M := by
    calc S ≤ ∑ _b : κ, M := Finset.sum_le_sum fun b _ => ha' b
      _ = D * M := by simp [D]
  have hD : 0 ≤ D := Nat.cast_nonneg _
  -- every term is at least `-δ D M²`, and the term of `k'` is at least `M² - δ D M²`
  set f : ι → ℝ := fun k => relu (u (i k)) * ((1 + δ) * u (i k) - δ * S) + δ * D * M ^ 2
  have hf : ∀ k, 0 ≤ f k := by
    intro k
    simp only [f, relu]
    rcases le_or_gt (u (i k)) 0 with h | h
    · rw [max_eq_right h, zero_mul, zero_add]
      positivity
    · rw [max_eq_left h.le]
      have h1 : u (i k) * S ≤ u (i k) * (D * M) := mul_le_mul_of_nonneg_left hS h.le
      have h2 : 0 ≤ δ * D * M * (M - u (i k)) :=
        mul_nonneg (by positivity) (by linarith [ha' (i k)])
      nlinarith [mul_pos h h]
  have hfk' : M ^ 2 ≤ f k' := by
    simp only [f, relu, hk', ← hMdef, max_eq_left hM.le]
    have h1 : M * S ≤ M * (D * M) := mul_le_mul_of_nonneg_left hS hM.le
    nlinarith [mul_pos hM hM]
  -- so `M² ≤ ∑_k f k = ∑_k term_k + q δ D M²`, and `q δ D < 1`
  have hsum : M ^ 2 ≤ ∑ k, f k :=
    hfk'.trans (Finset.single_le_sum (fun k _ => hf k) (Finset.mem_univ k'))
  have hsplit : ∑ k, f k = ∑ k, relu (u (i k)) * ((1 + δ) * u (i k) - δ * S)
      + Fintype.card ι * (δ * D * M ^ 2) := by
    simp only [f, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hq : (Fintype.card ι : ℝ) * (δ * D * M ^ 2) < M ^ 2 := by
    have := mul_lt_mul_of_pos_right hδ1 (pow_pos hM 2)
    nlinarith
  linarith

/-- **Proof of Proposition E.1, ReGLU:** for `d ≥ 1` and at least `d` hidden units in block
`ℓ.castSucc`, there is a nonempty open set of weights on which the gate of hidden unit `j` of the
next block `ℓ.succ` is closed at every input. -/
theorem exists_isOpen_gateInactive_reglu [Nonempty d] (ℓ : Fin L) (j : hid ℓ.succ)
    (hq : Fintype.card d ≤ Fintype.card (hid ℓ.castSucc)) :
    ∃ U : Set (Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut),
      IsOpen U ∧ U.Nonempty ∧ ∀ θ ∈ U, GateInactive θ ℓ.succ j := by
  sorry

end Skips
