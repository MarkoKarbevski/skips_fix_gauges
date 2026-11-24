import SkipsLean.Dimension.IdentifiableIffTransformerFinite

/-!
# The finite symmetries compose with the continuous ones

Papers (dimension paper, Definition 4.5; skips paper, Definition 4.4): "A network is identifiable
up to its symmetries at `θ` if every `θ′` with `F_{θ′} = F_θ` is the image of `θ` under a
symmetry: a change of basis […], a symmetry inside a block, or a composition of these."

The equivalences of `Dimension/IdentifiableIffFinite.lean`, `Residual/IdentifiableIffFinite.lean`
and `Dimension/IdentifiableIffTransformerFinite.lean` have on their right sides the symmetries in
one order: a finite symmetry first (permutations of hidden units or heads, sign flips), then the
continuous symmetries inside the blocks (rescalings, changes of basis inside the heads), then a
change of basis. Here are the identities by which a composition of these symmetries in any order
is brought to this form: two symmetries of one kind are one, a finite symmetry moves to the
inside, and a change of basis moves to the outside. That every composition is reduced by them is
an induction that is not a Lean statement.

Also here: for networks of attention blocks and MLP or gated blocks, the finite symmetries (the
maps on the two parts) preserve the function, with the lemma that maps on the two parts which
leave every block unchanged leave the function unchanged.
-/

namespace Skips

open Matrix

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {χ : Matrix T d ℝ → Matrix T d ℝ} {σ : ℝ → ℝ}
variable {hid H dh : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)] [∀ ℓ, Fintype (H ℓ)]
  [∀ ℓ, Fintype (dh ℓ)] [∀ ℓ, DecidableEq (dh ℓ)]
variable {sees : T → T → Prop} [DecidableRel sees]

/-! ### MLP blocks: permutations, sign flips, changes of basis -/

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Two permutations of the hidden units are one permutation. -/
theorem permUnits_permUnits (θ : Params (Arch.mlp (T := T) (d := d) σ χ hid) dIn dOut)
    (p p' : ∀ ℓ, Equiv.Perm (hid ℓ)) :
    (θ.permUnits p).permUnits p' = θ.permUnits (fun ℓ => p ℓ * p' ℓ) := rfl

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Two sign flips are one sign flip. -/
theorem flipUnits_flipUnits (θ : Params (Arch.mlp (T := T) (d := d) σ χ hid) dIn dOut)
    (s s' : ∀ ℓ, hid ℓ → ℤˣ) :
    (θ.flipUnits s).flipUnits s' = θ.flipUnits (fun ℓ i => s ℓ i * s' ℓ i) := by
  refine Params.ext' rfl (fun ℓ => ?_) (fun ℓ => ?_) rfl
  · ext a i; simp [Params.flipUnits]; ring
  · ext i a; simp [Params.flipUnits]; ring

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- A permutation after a sign flip is a sign flip (with the signs permuted) after the
permutation. -/
theorem flipUnits_permUnits (θ : Params (Arch.mlp (T := T) (d := d) σ χ hid) dIn dOut)
    (s : ∀ ℓ, hid ℓ → ℤˣ) (p : ∀ ℓ, Equiv.Perm (hid ℓ)) :
    (θ.flipUnits s).permUnits p = (θ.permUnits p).flipUnits (fun ℓ i => s ℓ (p ℓ i)) := rfl

omit [Fintype T] [Fintype dIn] [Fintype dOut] in
/-- A change of basis commutes with a permutation of the hidden units. -/
theorem cob_permUnits (θ : Params (Arch.mlp (T := T) (d := d) σ χ hid) dIn dOut)
    (G K : Fin (L + 1) → GL d ℝ) (p : ∀ ℓ, Equiv.Perm (hid ℓ)) :
    (θ.cob G K).permUnits p = (θ.permUnits p).cob G K := by
  refine Params.ext' rfl (fun ℓ => ?_) (fun ℓ => ?_) rfl
  · ext a i; simp [Params.permUnits, Params.cob, Matrix.mul_apply]
  · ext i a; simp [Params.permUnits, Params.cob, Matrix.mul_apply]

omit [Fintype T] [Fintype dIn] [Fintype dOut] in
/-- A change of basis commutes with a sign flip. -/
theorem cob_flipUnits (θ : Params (Arch.mlp (T := T) (d := d) σ χ hid) dIn dOut)
    (G K : Fin (L + 1) → GL d ℝ) (s : ∀ ℓ, hid ℓ → ℤˣ) :
    (θ.cob G K).flipUnits s = (θ.flipUnits s).cob G K := by
  refine Params.ext' rfl (fun ℓ => ?_) (fun ℓ => ?_) rfl
  · ext a i; simp [Params.flipUnits, Params.cob, Matrix.mul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_; ring
  · ext i a; simp [Params.flipUnits, Params.cob, Matrix.mul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_; ring

/-! ### Gated blocks: permutations, rescalings, changes of basis -/

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Gated blocks: two permutations of the hidden units are one permutation. -/
theorem permUnitsGated_permUnitsGated
    (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut)
    (p p' : ∀ ℓ, Equiv.Perm (hid ℓ)) :
    (θ.permUnitsGated p).permUnitsGated p' = θ.permUnitsGated (fun ℓ => p ℓ * p' ℓ) := by
  refine Params.ext' rfl (fun ℓ => ?_) (fun ℓ => rfl) rfl
  ext a j; cases j <;> rfl

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Gated blocks: a permutation after a rescaling is a rescaling (with the factors permuted)
after the permutation. -/
theorem rescale_permUnitsGated (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut)
    (c : ∀ ℓ, hid ℓ → ℝ) (p : ∀ ℓ, Equiv.Perm (hid ℓ)) :
    (θ.rescale c).permUnitsGated p = (θ.permUnitsGated p).rescale (fun ℓ i => c ℓ (p ℓ i)) := by
  refine Params.ext' rfl (fun ℓ => ?_) (fun ℓ => rfl) rfl
  ext a j; cases j <;> rfl

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Gated blocks: two rescalings are one rescaling. -/
theorem rescale_rescale (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut)
    (c c' : ∀ ℓ, hid ℓ → ℝ) :
    (θ.rescale c).rescale c' = θ.rescale (fun ℓ i => c ℓ i * c' ℓ i) := by
  refine Params.ext' rfl (fun ℓ => ?_) (fun ℓ => ?_) rfl
  · ext a j; cases j <;> simp [Params.rescale]; ring
  · ext i a; simp [Params.rescale]; ring

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Gated blocks: the sign change of the value of a hidden unit (value column and write row times
`−1`) is the rescaling by the factor `−1`; so the paper's sign flips of gated units are among the
rescalings by nonzero factors. -/
theorem rescale_neg_one (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut) (ℓ : Fin L)
    (a : d) (i : hid ℓ) :
    (θ.rescale (fun _ _ => -1)).read ℓ a (Sum.inr i) = -θ.read ℓ a (Sum.inr i)
    ∧ (θ.rescale (fun _ _ => -1)).read ℓ a (Sum.inl i) = θ.read ℓ a (Sum.inl i)
    ∧ (θ.rescale (fun _ _ => -1)).write ℓ i a = -θ.write ℓ i a := by
  simp [Params.rescale]

omit [Fintype T] [Fintype dIn] [Fintype dOut] in
/-- Gated blocks: a change of basis commutes with a permutation of the hidden units. -/
theorem cob_permUnitsGated (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut)
    (G K : Fin (L + 1) → GL d ℝ) (p : ∀ ℓ, Equiv.Perm (hid ℓ)) :
    (θ.cob G K).permUnitsGated p = (θ.permUnitsGated p).cob G K := by
  refine Params.ext' rfl (fun ℓ => ?_) (fun ℓ => ?_) rfl
  · ext a j; simp [Params.permUnitsGated, Params.cob, Matrix.mul_apply]
  · ext i a; simp [Params.permUnitsGated, Params.cob, Matrix.mul_apply]

omit [Fintype T] [Fintype dIn] [Fintype dOut] in
/-- Gated blocks: a change of basis commutes with a rescaling. -/
theorem cob_rescale (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut)
    (G K : Fin (L + 1) → GL d ℝ) (c : ∀ ℓ, hid ℓ → ℝ) :
    (θ.cob G K).rescale c = (θ.rescale c).cob G K := by
  refine Params.ext' rfl (fun ℓ => ?_) (fun ℓ => ?_) rfl
  · ext a j
    cases j <;> simp [Params.rescale, Params.cob, Matrix.mul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_; ring
  · ext i a; simp [Params.rescale, Params.cob, Matrix.mul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_; ring

/-! ### Attention blocks: permutations of heads, changes of basis inside the heads -/

omit [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] [(ℓ : Fin L) → DecidableEq (dh ℓ)] in
/-- Two permutations of the heads are one permutation. -/
theorem permHeads_permHeads
    (θ : Params (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut)
    (q q' : ∀ ℓ, Equiv.Perm (H ℓ)) :
    (θ.permHeads q).permHeads q' = θ.permHeads (fun ℓ => q ℓ * q' ℓ) := rfl

omit [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- A permutation of the heads after a change of basis between queries and keys is that change
of basis (with the matrices permuted) after the permutation. -/
theorem headsQK_permHeads (θ : Params (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut)
    (K : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ) (q : ∀ ℓ, Equiv.Perm (H ℓ)) :
    (θ.headsQK K).permHeads q = (θ.permHeads q).headsQK (fun ℓ i => K ℓ (q ℓ i)) := by
  refine Params.ext' rfl (fun ℓ => ?_) (fun ℓ => rfl) rfl
  ext a ⟨i, c⟩
  rcases c with k | k | k <;> rfl

omit [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- A permutation of the heads after a change of basis between values and outputs is that change
of basis (with the matrices permuted) after the permutation. -/
theorem headsVO_permHeads (θ : Params (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut)
    (K : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ) (q : ∀ ℓ, Equiv.Perm (H ℓ)) :
    (θ.headsVO K).permHeads q = (θ.permHeads q).headsVO (fun ℓ i => K ℓ (q ℓ i)) := by
  refine Params.ext' rfl (fun ℓ => ?_) (fun ℓ => ?_) rfl
  · ext a ⟨i, c⟩
    rcases c with k | k | k <;> rfl
  · ext ⟨i, k⟩ a; rfl

omit [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- The two changes of basis inside the heads commute. -/
theorem headsVO_headsQK (θ : Params (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut)
    (K K' : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ) :
    (θ.headsVO K').headsQK K = (θ.headsQK K).headsVO K' := by
  refine Params.ext' rfl (fun ℓ => ?_) (fun ℓ => rfl) rfl
  ext a ⟨i, c⟩
  rcases c with k | k | k <;> rfl

/-! ### Changes of basis, and the changes of basis inside the heads -/

omit [Fintype T] [Fintype dIn] [Fintype dOut] in
/-- Two changes of basis are one change of basis (the products, hidden state by hidden state). -/
theorem cob_cob {A : Arch T d L} (θ : Params A dIn dOut) (G K G' K' : Fin (L + 1) → GL d ℝ) :
    (θ.cob G K).cob G' K' = θ.cob (fun ℓ => G ℓ * G' ℓ) (fun ℓ => K ℓ * K' ℓ) := by
  refine Params.ext' ?_ (fun ℓ => ?_) (fun ℓ => ?_) ?_
  · simp [Params.cob, Matrix.mul_assoc]
  · simp [Params.cob, Matrix.mul_assoc, _root_.mul_inv_rev]
  · simp [Params.cob, Matrix.mul_assoc]
  · simp [Params.cob, Matrix.mul_assoc, _root_.mul_inv_rev]

omit [Fintype dIn] [Fintype dOut] [(ℓ : Fin L) → DecidableEq (dh ℓ)] in
/-- A change of basis commutes with a permutation of the heads. -/
theorem cob_permHeads (θ : Params (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut)
    (G K : Fin (L + 1) → GL d ℝ) (q : ∀ ℓ, Equiv.Perm (H ℓ)) :
    (θ.cob G K).permHeads q = (θ.permHeads q).cob G K := by
  refine Params.ext' rfl (fun ℓ => ?_) (fun ℓ => ?_) rfl
  · ext a c; simp [Params.permHeads, Params.cob, Matrix.mul_apply]
  · ext c a; simp [Params.permHeads, Params.cob, Matrix.mul_apply]

omit [Fintype dIn] [Fintype dOut] in
/-- A change of basis commutes with a change of basis between queries and keys. -/
theorem cob_headsQK (θ : Params (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut)
    (G K : Fin (L + 1) → GL d ℝ) (M : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ) :
    (θ.cob G K).headsQK M = (θ.headsQK M).cob G K := by
  refine Params.ext' rfl (fun ℓ => ?_) (fun ℓ => rfl) rfl
  ext a ⟨i, c⟩
  rcases c with k | k | k
  · simp only [Params.headsQK, Params.cob, Matrix.mul_apply, Matrix.of_apply, Finset.sum_mul,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k' _ => ?_
    ring
  · simp only [Params.headsQK, Params.cob, Matrix.mul_apply, Matrix.of_apply, Finset.sum_mul,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k' _ => ?_
    ring
  · rfl

omit [Fintype dIn] [Fintype dOut] in
/-- A change of basis commutes with a change of basis between values and outputs. -/
theorem cob_headsVO (θ : Params (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut)
    (G K : Fin (L + 1) → GL d ℝ) (M : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ) :
    (θ.cob G K).headsVO M = (θ.headsVO M).cob G K := by
  refine Params.ext' rfl (fun ℓ => ?_) (fun ℓ => ?_) rfl
  · ext a ⟨i, c⟩
    rcases c with k | k | k
    · rfl
    · rfl
    · simp only [Params.headsVO, Params.cob, Matrix.mul_apply, Matrix.of_apply, Finset.sum_mul,
        Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k' _ => ?_
      ring
  · ext ⟨i, k⟩ a
    simp only [Params.headsVO, Params.cob, Matrix.mul_apply, Matrix.of_apply, Finset.sum_mul,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k' _ => ?_
    ring

omit [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Two changes of basis between values and outputs are one. -/
theorem headsVO_headsVO (θ : Params (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut)
    (M M' : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ) :
    (θ.headsVO M).headsVO M' = θ.headsVO (fun ℓ i => M ℓ i * M' ℓ i) := by
  refine Params.ext' rfl (fun ℓ => ?_) (fun ℓ => ?_) rfl
  · ext a ⟨i, c⟩
    rcases c with k | k | k
    · rfl
    · rfl
    · simp only [Params.headsVO, Matrix.of_apply, Units.val_mul, Matrix.mul_apply, Finset.sum_mul,
        Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k' _ => ?_
      ring
  · ext ⟨i, k⟩ a
    simp only [Params.headsVO, Matrix.of_apply, _root_.mul_inv_rev, Units.val_mul, Matrix.mul_apply,
      Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k' _ => ?_
    ring

omit [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Two changes of basis between queries and keys are one. -/
theorem headsQK_headsQK (θ : Params (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut)
    (M M' : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ) :
    (θ.headsQK M).headsQK M' = θ.headsQK (fun ℓ i => M ℓ i * M' ℓ i) := by
  refine Params.ext' rfl (fun ℓ => ?_) (fun ℓ => rfl) rfl
  ext a ⟨i, c⟩
  rcases c with k | k | k
  · simp only [Params.headsQK, Matrix.of_apply, Units.val_mul, Matrix.mul_apply, Finset.sum_mul,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k' _ => ?_
    ring
  · simp only [Params.headsQK, Matrix.of_apply, _root_.mul_inv_rev, Units.val_mul, Matrix.mul_apply,
      Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k' _ => ?_
    ring
  · rfl

/-! ### Networks with two kinds of block -/

omit [Fintype T] [DecidableEq d] [Fintype dOut] in
/-- Two parameters with the same embedding and readout whose blocks compute the same maps
compute the same function, for all stream matrices. -/
theorem eval_eq_of_blocks {A : Arch T d L} (θ₁ θ₂ : Params A dIn dOut)
    (hE : θ₂.E = θ₁.E) (hD : θ₂.D = θ₁.D)
    (hb : ∀ ℓ (h : Matrix T d ℝ),
      A.f ℓ (h * θ₂.read ℓ) * θ₂.write ℓ = A.f ℓ (h * θ₁.read ℓ) * θ₁.write ℓ)
    (S : Fin L → Matrix d d ℝ) (x : Matrix T dIn ℝ) :
    eval A S θ₂ x = eval A S θ₁ x := by
  have hh : ∀ ℓ : Fin (L + 1), hidden A S θ₂ x ℓ = hidden A S θ₁ x ℓ := by
    intro ℓ
    induction ℓ using Fin.induction with
    | zero => rw [hidden_zero, hidden_zero, hE]
    | succ ℓ ih => rw [hidden_succ, hidden_succ, ih, hb]
  rw [eval, eval, hh, hD]

omit [Fintype T] [DecidableEq d] [Fintype dOut] in
/-- Maps on the two parts of a network with two kinds of block: if each leaves the output of every
block of its part unchanged, the function is unchanged. -/
theorem eval_sumOf_of_blocks {A B : Arch T d L} (θ : Params (A.sum B) dIn dOut)
    (a : Params A dIn dOut) (b : Params B dIn dOut) (haE : a.E = θ.E) (haD : a.D = θ.D)
    (ha : ∀ ℓ (h : Matrix T d ℝ), A.f ℓ (h * a.read ℓ) * a.write ℓ
      = A.f ℓ (h * θ.sumFst.read ℓ) * θ.sumFst.write ℓ)
    (hb : ∀ ℓ (h : Matrix T d ℝ), B.f ℓ (h * b.read ℓ) * b.write ℓ
      = B.f ℓ (h * θ.sumSnd.read ℓ) * θ.sumSnd.write ℓ)
    (S : Fin L → Matrix d d ℝ) (x : Matrix T dIn ℝ) :
    eval (A.sum B) S (Params.sumOf a b) x = eval (A.sum B) S θ x := by
  refine eval_eq_of_blocks θ (Params.sumOf a b) haE haD (fun ℓ h => ?_) S x
  rw [f_sum_mul, f_sum_mul]
  exact congrArg₂ (· + ·) (ha ℓ h) (hb ℓ h)

omit [Fintype T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- A permutation of the hidden units leaves every MLP block unchanged. -/
theorem block_permUnits (θ : Params (Arch.mlp (T := T) (d := d) σ χ hid) dIn dOut)
    (p : ∀ ℓ, Equiv.Perm (hid ℓ)) (ℓ : Fin L) (n : Matrix T d ℝ) :
    (Arch.mlp (T := T) (d := d) σ χ hid).f ℓ (n * (θ.permUnits p).read ℓ) * (θ.permUnits p).write ℓ
      = (Arch.mlp (T := T) (d := d) σ χ hid).f ℓ (n * θ.read ℓ) * θ.write ℓ := by
  ext t a
  simp only [Matrix.mul_apply, Matrix.map_apply, Params.permUnits, Matrix.of_apply]
  exact Equiv.sum_comp (p ℓ) (fun i => σ (∑ j, n t j * θ.read ℓ j i) * θ.write ℓ i a)

omit [Fintype T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- For an odd activation, a sign flip leaves every MLP block unchanged. -/
theorem block_flipUnits (hσ : ∀ z, σ (-z) = -σ z)
    (θ : Params (Arch.mlp (T := T) (d := d) σ χ hid) dIn dOut)
    (s : ∀ ℓ, hid ℓ → ℤˣ) (ℓ : Fin L) (n : Matrix T d ℝ) :
    (Arch.mlp (T := T) (d := d) σ χ hid).f ℓ (n * (θ.flipUnits s).read ℓ) * (θ.flipUnits s).write ℓ
      = (Arch.mlp (T := T) (d := d) σ χ hid).f ℓ (n * θ.read ℓ) * θ.write ℓ := by
  ext t a
  simp only [Matrix.mul_apply, Matrix.map_apply, Params.flipUnits, Matrix.of_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases Int.units_eq_one_or (s ℓ i) with h | h
  · simp [h]
  · simp [h, hσ, Finset.sum_neg_distrib]

omit [Fintype T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- A permutation of the hidden units leaves every gated block unchanged. -/
theorem block_permUnitsGated (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut)
    (p : ∀ ℓ, Equiv.Perm (hid ℓ)) (ℓ : Fin L) (n : Matrix T d ℝ) :
    (Arch.gated (T := T) (d := d) σ χ hid).f ℓ (n * (θ.permUnitsGated p).read ℓ)
        * (θ.permUnitsGated p).write ℓ
      = (Arch.gated (T := T) (d := d) σ χ hid).f ℓ (n * θ.read ℓ) * θ.write ℓ := by
  ext t a
  simp only [Matrix.mul_apply, Params.permUnitsGated, Matrix.of_apply, Sum.map_inl, Sum.map_inr]
  exact Equiv.sum_comp (p ℓ) (fun i => σ (∑ j, n t j * θ.read ℓ j (Sum.inl i))
    * (∑ j, n t j * θ.read ℓ j (Sum.inr i)) * θ.write ℓ i a)

omit [DecidableEq d] [Fintype dIn] [Fintype dOut] [(ℓ : Fin L) → DecidableEq (dh ℓ)] in
/-- A permutation of the heads leaves every attention block unchanged. -/
theorem block_permHeads (θ : Params (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut)
    (q : ∀ ℓ, Equiv.Perm (H ℓ)) (ℓ : Fin L) (n : Matrix T d ℝ) :
    (Arch.attention (T := T) (d := d) sees χ H dh).f ℓ (n * (θ.permHeads q).read ℓ)
        * (θ.permHeads q).write ℓ
      = (Arch.attention (T := T) (d := d) sees χ H dh).f ℓ (n * θ.read ℓ) * θ.write ℓ := by
  ext t a
  rw [Matrix.mul_apply, Matrix.mul_apply]
  exact Equiv.sum_comp (Equiv.prodCongr (q ℓ) (Equiv.refl _))
    (fun c => (Arch.attention sees χ H dh).f ℓ (n * θ.read ℓ) t c * θ.write ℓ c a)

omit [(ℓ : Fin L) → DecidableEq (dh ℓ)] [DecidableEq d] [Fintype dOut] in
/-- **Networks of attention blocks and MLP blocks:** the permutations of the heads and of the
hidden units preserve the function. -/
theorem eval_attentionMlp_perm
    (θ : Params (Arch.attentionMlp (T := T) (d := d) sees σ χ H dh hid) dIn dOut)
    (q : ∀ ℓ, Equiv.Perm (H ℓ)) (p : ∀ ℓ, Equiv.Perm (hid ℓ))
    (S : Fin L → Matrix d d ℝ) (x : Matrix T dIn ℝ) :
    eval (Arch.attentionMlp sees σ χ H dh hid) S
        (Params.sumOf (θ.sumFst.permHeads q) (θ.sumSnd.permUnits p)) x
      = eval (Arch.attentionMlp sees σ χ H dh hid) S θ x :=
  eval_sumOf_of_blocks θ _ _ rfl rfl (block_permHeads θ.sumFst q) (block_permUnits θ.sumSnd p) S x

omit [(ℓ : Fin L) → DecidableEq (dh ℓ)] [DecidableEq d] [Fintype dOut] in
/-- **Networks of attention blocks and MLP blocks with an odd activation:** the permutations of the
heads and of the hidden units with the sign flips preserve the function. -/
theorem eval_attentionMlp_perm_flip (hσ : ∀ z, σ (-z) = -σ z)
    (θ : Params (Arch.attentionMlp (T := T) (d := d) sees σ χ H dh hid) dIn dOut)
    (q : ∀ ℓ, Equiv.Perm (H ℓ)) (p : ∀ ℓ, Equiv.Perm (hid ℓ)) (s : ∀ ℓ, hid ℓ → ℤˣ)
    (S : Fin L → Matrix d d ℝ) (x : Matrix T dIn ℝ) :
    eval (Arch.attentionMlp sees σ χ H dh hid) S
        (Params.sumOf (θ.sumFst.permHeads q) ((θ.sumSnd.permUnits p).flipUnits s)) x
      = eval (Arch.attentionMlp sees σ χ H dh hid) S θ x :=
  eval_sumOf_of_blocks θ _ _ rfl rfl (block_permHeads θ.sumFst q)
    (fun ℓ h => (block_flipUnits hσ (θ.sumSnd.permUnits p) s ℓ h).trans
      (block_permUnits θ.sumSnd p ℓ h)) S x

omit [(ℓ : Fin L) → DecidableEq (dh ℓ)] [DecidableEq d] [Fintype dOut] in
/-- **Networks of attention blocks and gated blocks:** the permutations of the heads and of the
hidden units preserve the function. -/
theorem eval_attentionGated_perm
    (θ : Params (Arch.attentionGated (T := T) (d := d) sees σ χ H dh hid) dIn dOut)
    (q : ∀ ℓ, Equiv.Perm (H ℓ)) (p : ∀ ℓ, Equiv.Perm (hid ℓ))
    (S : Fin L → Matrix d d ℝ) (x : Matrix T dIn ℝ) :
    eval (Arch.attentionGated sees σ χ H dh hid) S
        (Params.sumOf (θ.sumFst.permHeads q) (θ.sumSnd.permUnitsGated p)) x
      = eval (Arch.attentionGated sees σ χ H dh hid) S θ x :=
  eval_sumOf_of_blocks θ _ _ rfl rfl (block_permHeads θ.sumFst q)
    (block_permUnitsGated θ.sumSnd p) S x

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- The two parts of `sumOf a b` are `a` and `b` (for a common embedding and readout), so maps on
the two parts compose part by part. -/
theorem sumFst_sumOf {A B : Arch T d L} (a : Params A dIn dOut) (b : Params B dIn dOut)
    (hE : b.E = a.E) (hD : b.D = a.D) :
    (Params.sumOf a b).sumFst = a ∧ (Params.sumOf a b).sumSnd = b := by
  constructor
  · rfl
  · exact Params.ext' hE.symm (fun _ => rfl) (fun _ => rfl) hD.symm

omit [Fintype T] [Fintype dIn] [Fintype dOut] in
/-- A change of basis acts on the two parts. -/
theorem sumOf_cob {A B : Arch T d L} (a : Params A dIn dOut) (b : Params B dIn dOut)
    (G K : Fin (L + 1) → GL d ℝ) :
    (Params.sumOf a b).cob G K = Params.sumOf (a.cob G K) (b.cob G K) := by
  refine Params.ext' rfl (fun ℓ => ?_) (fun ℓ => ?_) rfl
  · ext k p; cases p <;> simp [Params.sumOf, Params.cob, Matrix.mul_apply]
  · ext p k; cases p <;> simp [Params.sumOf, Params.cob, Matrix.mul_apply]

end Skips
