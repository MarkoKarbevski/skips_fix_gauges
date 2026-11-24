import SkipsLean.Network.Blocks
import SkipsLean.Network.Attention

/-!
# The finite symmetries inside the blocks: permutations and sign flips

Paper (dimension paper, Appendix B, "The symmetries inside the blocks, with their sources";
the skips paper has the same sentence): "Permutations of hidden units or heads and sign flips of
tanh hidden units are finite and remove no parameters (Fefferman, 1994; Hecht-Nielsen, 1989;
Sussmann, 1992)." The proof of Proposition 4.6 counts them among the symmetries: "With the
permutations and the sign flips, the symmetries form a Lie group of dimension `k` with finitely
many components".

Here they are maps of the parameters:

* `Params.permUnits θ p`: the hidden units of every MLP block are permuted (hidden unit `i` of
  block `ℓ` of the new parameter is hidden unit `p ℓ i` of `θ`: its read column and its write row);
* `Params.flipUnits θ s`: the read column and the write row of hidden unit `i` of block `ℓ` are
  multiplied by the sign `s ℓ i ∈ {1, −1}`;
* `Params.permUnitsGated θ p`: the hidden units of every gated block are permuted (gate column,
  value column and write row);
* `Params.permHeads θ q`: the heads of every attention block are permuted (the query, key and
  value columns and the output rows of head `i` of the new parameter are those of head `q ℓ i`).

Each preserves the function, for all stream matrices and every map `χ` before the reads: the
permutations for every activation, the sign flips for an odd activation (tanh). The trivial
permutation and the signs `1` give `θ` back. For a network of attention blocks and MLP or gated
blocks (`Arch.attentionMlp`, `Arch.attentionGated`) the finite symmetries are these maps on the two
parts, `Params.sumOf (θ.sumFst.permHeads q) (θ.sumSnd.permUnits p)`.

The equivalences "equality condition if and only if locally identifiable" with these symmetries:
`Dimension/IdentifiableIffFinite.lean`, `Residual/IdentifiableIffFinite.lean`,
`Dimension/IdentifiableIffTransformerFinite.lean`.
-/

namespace Skips

open Matrix

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {χ : Matrix T d ℝ → Matrix T d ℝ} {σ : ℝ → ℝ}
variable {hid H dh : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)] [∀ ℓ, Fintype (H ℓ)]
  [∀ ℓ, Fintype (dh ℓ)]
variable {sees : T → T → Prop} [DecidableRel sees]

/-- **A permutation of the hidden units of every MLP block:** hidden unit `i` of block `ℓ` of
`θ.permUnits p` is hidden unit `p ℓ i` of `θ`, with its read column and its write row. -/
def Params.permUnits (θ : Params (Arch.mlp (T := T) (d := d) σ χ hid) dIn dOut)
    (p : ∀ ℓ, Equiv.Perm (hid ℓ)) : Params (Arch.mlp (T := T) (d := d) σ χ hid) dIn dOut where
  E := θ.E
  read ℓ := Matrix.of fun a i => θ.read ℓ a (p ℓ i)
  write ℓ := Matrix.of fun i a => θ.write ℓ (p ℓ i) a
  D := θ.D

/-- **Sign flips of the hidden units of MLP blocks:** the read column and the write row of hidden
unit `i` of block `ℓ` are multiplied by the sign `s ℓ i`, which is `1` or `−1`. -/
noncomputable def Params.flipUnits (θ : Params (Arch.mlp (T := T) (d := d) σ χ hid) dIn dOut)
    (s : ∀ ℓ, hid ℓ → ℤˣ) : Params (Arch.mlp (T := T) (d := d) σ χ hid) dIn dOut where
  E := θ.E
  read ℓ := Matrix.of fun a i => (((s ℓ i : ℤˣ) : ℤ) : ℝ) * θ.read ℓ a i
  write ℓ := Matrix.of fun i a => (((s ℓ i : ℤˣ) : ℤ) : ℝ) * θ.write ℓ i a
  D := θ.D

/-- **A permutation of the hidden units of every gated block:** hidden unit `i` of block `ℓ` of
`θ.permUnitsGated p` is hidden unit `p ℓ i` of `θ`, with its gate column, its value column and its
write row. -/
def Params.permUnitsGated (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut)
    (p : ∀ ℓ, Equiv.Perm (hid ℓ)) : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut where
  E := θ.E
  read ℓ := Matrix.of fun a j => θ.read ℓ a (Sum.map (p ℓ) (p ℓ) j)
  write ℓ := Matrix.of fun i a => θ.write ℓ (p ℓ i) a
  D := θ.D

/-- **A permutation of the heads of every attention block:** head `i` of block `ℓ` of
`θ.permHeads q` is head `q ℓ i` of `θ`, with its query, key and value columns and its output
rows. -/
def Params.permHeads (θ : Params (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut)
    (q : ∀ ℓ, Equiv.Perm (H ℓ)) :
    Params (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut where
  E := θ.E
  read ℓ := Matrix.of fun a (c : H ℓ × (dh ℓ ⊕ (dh ℓ ⊕ dh ℓ))) => θ.read ℓ a (q ℓ c.1, c.2)
  write ℓ := Matrix.of fun (c : H ℓ × dh ℓ) a => θ.write ℓ (q ℓ c.1, c.2) a
  D := θ.D

omit [Fintype T] [DecidableEq d] [Fintype dOut] in
/-- Helper (a copy of `eval_eq_of_blocks_ath` of `Symmetry/AttentionHeads.lean`): two parameters
with the same `E`, the same `D` and the same output of every block on every hidden state compute
the same function (induction along the hidden states). -/
private theorem eval_eq_of_blocks_fs {A : Arch T d L} (θ₁ θ₂ : Params A dIn dOut)
    (hE : θ₂.E = θ₁.E) (hD : θ₂.D = θ₁.D)
    (hb : ∀ ℓ (h : Matrix T d ℝ),
      A.f ℓ (h * θ₂.read ℓ) * θ₂.write ℓ = A.f ℓ (h * θ₁.read ℓ) * θ₁.write ℓ)
    (S : Fin L → Matrix d d ℝ) (x : Matrix T dIn ℝ) :
    eval A S θ₂ x = eval A S θ₁ x := by
  -- the hidden states agree, by induction along the network
  have hh : ∀ ℓ : Fin (L + 1), hidden A S θ₂ x ℓ = hidden A S θ₁ x ℓ := by
    intro ℓ
    induction ℓ using Fin.induction with
    | zero => rw [hidden_zero, hidden_zero, hE]
    | succ ℓ ih => rw [hidden_succ, hidden_succ, ih, hb]
  -- hence the outputs agree
  rw [eval, eval, hh, hD]

/-- The permutations of the hidden units of MLP blocks preserve the function, for every
activation, all stream matrices and every map `χ`. -/
theorem eval_permUnits (θ : Params (Arch.mlp (T := T) (d := d) σ χ hid) dIn dOut)
    (p : ∀ ℓ, Equiv.Perm (hid ℓ)) (S : Fin L → Matrix d d ℝ) (x : Matrix T dIn ℝ) :
    eval (Arch.mlp σ χ hid) S (θ.permUnits p) x = eval (Arch.mlp σ χ hid) S θ x := by
  refine eval_eq_of_blocks_fs θ (θ.permUnits p) rfl rfl (fun ℓ n => ?_) S x
  -- entry `(t, a)` is `∑_i σ((n R)_{t, p i}) W_{p i, a}`: reindex the sum by `p ℓ`
  ext t a
  simp only [Matrix.mul_apply, Matrix.map_apply, Params.permUnits, Matrix.of_apply]
  exact Equiv.sum_comp (p ℓ) (fun i => σ (∑ j, n t j * θ.read ℓ j i) * θ.write ℓ i a)

/-- The sign flips of the hidden units of MLP blocks preserve the function when the activation is
odd (tanh), for all stream matrices and every map `χ`. -/
theorem eval_flipUnits (hσ : ∀ z, σ (-z) = -σ z)
    (θ : Params (Arch.mlp (T := T) (d := d) σ χ hid) dIn dOut)
    (s : ∀ ℓ, hid ℓ → ℤˣ) (S : Fin L → Matrix d d ℝ) (x : Matrix T dIn ℝ) :
    eval (Arch.mlp σ χ hid) S (θ.flipUnits s) x = eval (Arch.mlp σ χ hid) S θ x := by
  refine eval_eq_of_blocks_fs θ (θ.flipUnits s) rfl rfl (fun ℓ n => ?_) S x
  ext t a
  simp only [Matrix.mul_apply, Matrix.map_apply, Params.flipUnits, Matrix.of_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  -- `σ(s z) (s w) = σ(z) w` for `s = 1` and for `s = −1` (odd `σ`)
  rcases Int.units_eq_one_or (s ℓ i) with h | h
  · simp [h]
  · simp [h, hσ, Finset.sum_neg_distrib]

/-- The permutations of the hidden units of gated blocks preserve the function, for every gate
activation, all stream matrices and every map `χ`. -/
theorem eval_permUnitsGated (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut)
    (p : ∀ ℓ, Equiv.Perm (hid ℓ)) (S : Fin L → Matrix d d ℝ) (x : Matrix T dIn ℝ) :
    eval (Arch.gated σ χ hid) S (θ.permUnitsGated p) x = eval (Arch.gated σ χ hid) S θ x := by
  refine eval_eq_of_blocks_fs θ (θ.permUnitsGated p) rfl rfl (fun ℓ n => ?_) S x
  -- entry `(t, a)` is `∑_i σ((n R)_{t, inl (p i)}) (n R)_{t, inr (p i)} W_{p i, a}`: reindex
  ext t a
  simp only [Matrix.mul_apply, Params.permUnitsGated, Matrix.of_apply, Sum.map_inl, Sum.map_inr]
  exact Equiv.sum_comp (p ℓ) (fun i => σ (∑ j, n t j * θ.read ℓ j (Sum.inl i))
    * (∑ j, n t j * θ.read ℓ j (Sum.inr i)) * θ.write ℓ i a)

/-- The permutations of the heads of attention blocks preserve the function, for all stream
matrices and every map `χ`. -/
theorem eval_permHeads (θ : Params (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut)
    (q : ∀ ℓ, Equiv.Perm (H ℓ)) (S : Fin L → Matrix d d ℝ) (x : Matrix T dIn ℝ) :
    eval (Arch.attention sees χ H dh) S (θ.permHeads q) x
      = eval (Arch.attention sees χ H dh) S θ x := by
  refine eval_eq_of_blocks_fs θ (θ.permHeads q) rfl rfl (fun ℓ n => ?_) S x
  -- head `i` of `n R'` is head `q ℓ i` of `n R`; reindex the rows `(i, k)` of the write
  ext t a
  rw [Matrix.mul_apply, Matrix.mul_apply]
  exact Equiv.sum_comp (Equiv.prodCongr (q ℓ) (Equiv.refl _))
    (fun c => (Arch.attention sees χ H dh).f ℓ (n * θ.read ℓ) t c * θ.write ℓ c a)

/-- The trivial permutation of the hidden units of MLP blocks gives `θ` back. -/
theorem permUnits_one (θ : Params (Arch.mlp (T := T) (d := d) σ χ hid) dIn dOut) :
    θ.permUnits (fun _ => 1) = θ := by
  rfl

/-- The signs `1` give `θ` back. -/
theorem flipUnits_one (θ : Params (Arch.mlp (T := T) (d := d) σ χ hid) dIn dOut) :
    θ.flipUnits (fun _ _ => 1) = θ := by
  cases θ
  simp only [Params.flipUnits, Units.val_one, Int.cast_one, one_mul]
  rfl

/-- The trivial permutation of the hidden units of gated blocks gives `θ` back. -/
theorem permUnitsGated_one (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut) :
    θ.permUnitsGated (fun _ => 1) = θ := by
  cases θ
  simp only [Params.permUnitsGated, Equiv.Perm.coe_one, Sum.map_id_id, id]
  rfl

/-- The trivial permutation of the heads gives `θ` back. -/
theorem permHeads_one (θ : Params (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut) :
    θ.permHeads (fun _ => 1) = θ := by
  rfl

end Skips
