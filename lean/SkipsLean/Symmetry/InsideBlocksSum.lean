import SkipsLean.Symmetry.InsideBlocks
import SkipsLean.Network.Sum

/-!
# Symmetries inside the blocks of a network with two kinds of block

Papers. Skips paper, Theorem 4.2 (Upper bounds), with "`s` the dimension of the symmetries inside
the blocks", "summed over the blocks" (Section 4.1), for networks whose blocks are attention
blocks and MLP blocks (Section 2: "A transformer layer has two blocks, its attention and MLP
sub-layers"). In the sum `A.sum B` of two architectures (`Network/Sum.lean`) a symmetry inside
the blocks of `A`, or of `B`, is a symmetry inside the blocks of the sum, and the two families
are independent, so their dimensions add.

* `Params.sumFst θ`, `Params.sumSnd θ`: the parameters of the two parts of a network of `A.sum B`
  (the same `E` and `D`; the read columns and the write rows of the part).
* `Params.sumInl η`, `Params.sumInr η`: a direction of `A`, or of `B`, as a direction of the sum
  (`0` on the other part).
* `InsideBlocks.sumInl`, `InsideBlocks.sumInr`: a direction of a symmetry inside the blocks of a
  part is one of the sum.
* The bounds of `Symmetry/InsideBlocks.lean` for the sum, with `dim V_A + dim V_B`.
-/

namespace Skips

open Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} {A B : Arch T d L}

/-- **The first part of the parameters of a network of `A.sum B`:** `E`, `D`, and in every block
the read columns and the write rows that belong to `A`. -/
def Params.sumFst (θ : Params (A.sum B) dIn dOut) : Params A dIn dOut where
  E := θ.E
  read ℓ := (θ.read ℓ).submatrix id Sum.inl
  write ℓ := (θ.write ℓ).submatrix Sum.inl id
  D := θ.D

/-- **The second part of the parameters of a network of `A.sum B`:** `E`, `D`, and in every block
the read columns and the write rows that belong to `B`. -/
def Params.sumSnd (θ : Params (A.sum B) dIn dOut) : Params B dIn dOut where
  E := θ.E
  read ℓ := (θ.read ℓ).submatrix id Sum.inr
  write ℓ := (θ.write ℓ).submatrix Sum.inr id
  D := θ.D

/-- **A direction of `A` as a direction of the sum:** `0` at the read columns and the write rows
that belong to `B`. -/
def Params.sumInl (η : Params A dIn dOut) : Params (A.sum B) dIn dOut where
  E := η.E
  read ℓ := Matrix.of fun a p => Sum.elim (fun j => η.read ℓ a j) (fun _ => 0) p
  write ℓ := Matrix.of fun p a => Sum.elim (fun i => η.write ℓ i a) (fun _ => 0) p
  D := η.D

/-- **A direction of `B` as a direction of the sum:** `0` at the read columns and the write rows
that belong to `A`. -/
def Params.sumInr (η : Params B dIn dOut) : Params (A.sum B) dIn dOut where
  E := η.E
  read ℓ := Matrix.of fun a p => Sum.elim (fun _ => 0) (fun j => η.read ℓ a j) p
  write ℓ := Matrix.of fun p a => Sum.elim (fun _ => 0) (fun i => η.write ℓ i a) p
  D := η.D

/-- Helper: `Params.sumInl`, the lift of a direction of `A` to the sum, as a linear map. -/
def sumInlLin_ibl : Params A dIn dOut →ₗ[ℝ] Params (A.sum B) dIn dOut where
  toFun := Params.sumInl
  map_add' η ζ := by
    apply Params.ext'
    · rfl
    · intro ℓ
      ext a p
      rcases p with p | p
      · rfl
      · exact (add_zero (0 : ℝ)).symm
    · intro ℓ
      ext p a
      rcases p with p | p
      · rfl
      · exact (add_zero (0 : ℝ)).symm
    · rfl
  map_smul' c η := by
    apply Params.ext'
    · rfl
    · intro ℓ
      ext a p
      rcases p with p | p
      · rfl
      · exact (smul_zero c).symm
    · intro ℓ
      ext p a
      rcases p with p | p
      · rfl
      · exact (smul_zero c).symm
    · rfl

/-- Helper: `Params.sumInr`, the lift of a direction of `B` to the sum, as a linear map. -/
def sumInrLin_ibl : Params B dIn dOut →ₗ[ℝ] Params (A.sum B) dIn dOut where
  toFun := Params.sumInr
  map_add' η ζ := by
    apply Params.ext'
    · rfl
    · intro ℓ
      ext a p
      rcases p with p | p
      · exact (add_zero (0 : ℝ)).symm
      · rfl
    · intro ℓ
      ext p a
      rcases p with p | p
      · exact (add_zero (0 : ℝ)).symm
      · rfl
    · rfl
  map_smul' c η := by
    apply Params.ext'
    · rfl
    · intro ℓ
      ext a p
      rcases p with p | p
      · exact (smul_zero c).symm
      · rfl
    · intro ℓ
      ext p a
      rcases p with p | p
      · exact (smul_zero c).symm
      · rfl
    · rfl

variable [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut]

omit [Fintype T] [DecidableEq d] in
/-- **A symmetry inside the blocks of `A` is a symmetry inside the blocks of the sum.** -/
theorem InsideBlocks.sumInl {θ : Params (A.sum B) dIn dOut} {η : Params A dIn dOut}
    (h : InsideBlocks A θ.sumFst η) : InsideBlocks (A.sum B) θ (Params.sumInl η) := by
  obtain ⟨γ, h0, hd, hev⟩ := h
  -- the curve `τ ↦ θ + (γ(τ) − θ_A)`: the move of `γ`, lifted to the part of `A`
  refine ⟨fun τ => θ + sumInlLin_ibl (B := B) (γ τ - θ.sumFst), ?_, ?_, ?_⟩
  · -- at `τ = 0` it is `θ`
    show θ + sumInlLin_ibl (B := B) (γ 0 - θ.sumFst) = θ
    rw [h0, sub_self, map_zero, add_zero]
  · -- its velocity is the lift of `η`, since the lift is linear (hence continuous)
    have h1 : HasDerivAt (fun τ => sumInlLin_ibl (B := B) (γ τ - θ.sumFst))
        (sumInlLin_ibl (B := B) η) 0 :=
      (LinearMap.toContinuousLinearMap (sumInlLin_ibl (A := A) (B := B) (dIn := dIn)
        (dOut := dOut))).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hd.sub_const θ.sumFst)
    exact h1.const_add θ
  · filter_upwards [hev] with τ hτ
    obtain ⟨hE, hD, hb⟩ := hτ
    refine ⟨?_, ?_, fun ℓ n => ?_⟩
    · -- the embedding and the readout are kept
      show θ.E + ((γ τ).E - θ.sumFst.E) = θ.E
      rw [hE, sub_self, add_zero]
    · show θ.D + ((γ τ).D - θ.sumFst.D) = θ.D
      rw [hD, sub_self, add_zero]
    · -- the block of the sum is the sum of the blocks (`f_sum_mul`): the part of `A` is that of
      -- `γ τ`, which keeps its map, and the part of `B` does not move
      have hrl : ((θ + sumInlLin_ibl (B := B) (γ τ - θ.sumFst)).read ℓ).submatrix id Sum.inl
          = (γ τ).read ℓ := by
        ext a j
        show θ.read ℓ a (Sum.inl j) + ((γ τ).read ℓ a j - θ.read ℓ a (Sum.inl j))
          = (γ τ).read ℓ a j
        ring
      have hrr : ((θ + sumInlLin_ibl (B := B) (γ τ - θ.sumFst)).read ℓ).submatrix id Sum.inr
          = (θ.read ℓ).submatrix id Sum.inr := by
        ext a j
        show θ.read ℓ a (Sum.inr j) + 0 = θ.read ℓ a (Sum.inr j)
        rw [add_zero]
      have hwl : ((θ + sumInlLin_ibl (B := B) (γ τ - θ.sumFst)).write ℓ).submatrix Sum.inl id
          = (γ τ).write ℓ := by
        ext i a
        show θ.write ℓ (Sum.inl i) a + ((γ τ).write ℓ i a - θ.write ℓ (Sum.inl i) a)
          = (γ τ).write ℓ i a
        ring
      have hwr : ((θ + sumInlLin_ibl (B := B) (γ τ - θ.sumFst)).write ℓ).submatrix Sum.inr id
          = (θ.write ℓ).submatrix Sum.inr id := by
        ext i a
        show θ.write ℓ (Sum.inr i) a + 0 = θ.write ℓ (Sum.inr i) a
        rw [add_zero]
      have hb' : A.f ℓ (n * (γ τ).read ℓ) * (γ τ).write ℓ
          = A.f ℓ (n * (θ.read ℓ).submatrix id Sum.inl) * (θ.write ℓ).submatrix Sum.inl id :=
        hb ℓ n
      show (A.sum B).f ℓ (n * (θ + sumInlLin_ibl (B := B) (γ τ - θ.sumFst)).read ℓ)
          * (θ + sumInlLin_ibl (B := B) (γ τ - θ.sumFst)).write ℓ
        = (A.sum B).f ℓ (n * θ.read ℓ) * θ.write ℓ
      rw [f_sum_mul A B ℓ n, f_sum_mul A B ℓ n, hrl, hrr, hwl, hwr, hb']

omit [Fintype T] [DecidableEq d] in
/-- **A symmetry inside the blocks of `B` is a symmetry inside the blocks of the sum.** -/
theorem InsideBlocks.sumInr {θ : Params (A.sum B) dIn dOut} {η : Params B dIn dOut}
    (h : InsideBlocks B θ.sumSnd η) : InsideBlocks (A.sum B) θ (Params.sumInr η) := by
  obtain ⟨γ, h0, hd, hev⟩ := h
  -- the curve `τ ↦ θ + (γ(τ) − θ_B)`: the move of `γ`, lifted to the part of `B`
  refine ⟨fun τ => θ + sumInrLin_ibl (A := A) (γ τ - θ.sumSnd), ?_, ?_, ?_⟩
  · -- at `τ = 0` it is `θ`
    show θ + sumInrLin_ibl (A := A) (γ 0 - θ.sumSnd) = θ
    rw [h0, sub_self, map_zero, add_zero]
  · -- its velocity is the lift of `η`, since the lift is linear (hence continuous)
    have h1 : HasDerivAt (fun τ => sumInrLin_ibl (A := A) (γ τ - θ.sumSnd))
        (sumInrLin_ibl (A := A) η) 0 :=
      (LinearMap.toContinuousLinearMap (sumInrLin_ibl (A := A) (B := B) (dIn := dIn)
        (dOut := dOut))).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hd.sub_const θ.sumSnd)
    exact h1.const_add θ
  · filter_upwards [hev] with τ hτ
    obtain ⟨hE, hD, hb⟩ := hτ
    refine ⟨?_, ?_, fun ℓ n => ?_⟩
    · -- the embedding and the readout are kept
      show θ.E + ((γ τ).E - θ.sumSnd.E) = θ.E
      rw [hE, sub_self, add_zero]
    · show θ.D + ((γ τ).D - θ.sumSnd.D) = θ.D
      rw [hD, sub_self, add_zero]
    · -- the block of the sum is the sum of the blocks (`f_sum_mul`): the part of `B` is that of
      -- `γ τ`, which keeps its map, and the part of `A` does not move
      have hrl : ((θ + sumInrLin_ibl (A := A) (γ τ - θ.sumSnd)).read ℓ).submatrix id Sum.inl
          = (θ.read ℓ).submatrix id Sum.inl := by
        ext a j
        show θ.read ℓ a (Sum.inl j) + 0 = θ.read ℓ a (Sum.inl j)
        rw [add_zero]
      have hrr : ((θ + sumInrLin_ibl (A := A) (γ τ - θ.sumSnd)).read ℓ).submatrix id Sum.inr
          = (γ τ).read ℓ := by
        ext a j
        show θ.read ℓ a (Sum.inr j) + ((γ τ).read ℓ a j - θ.read ℓ a (Sum.inr j))
          = (γ τ).read ℓ a j
        ring
      have hwl : ((θ + sumInrLin_ibl (A := A) (γ τ - θ.sumSnd)).write ℓ).submatrix Sum.inl id
          = (θ.write ℓ).submatrix Sum.inl id := by
        ext i a
        show θ.write ℓ (Sum.inl i) a + 0 = θ.write ℓ (Sum.inl i) a
        rw [add_zero]
      have hwr : ((θ + sumInrLin_ibl (A := A) (γ τ - θ.sumSnd)).write ℓ).submatrix Sum.inr id
          = (γ τ).write ℓ := by
        ext i a
        show θ.write ℓ (Sum.inr i) a + ((γ τ).write ℓ i a - θ.write ℓ (Sum.inr i) a)
          = (γ τ).write ℓ i a
        ring
      have hb' : B.f ℓ (n * (γ τ).read ℓ) * (γ τ).write ℓ
          = B.f ℓ (n * (θ.read ℓ).submatrix id Sum.inr) * (θ.write ℓ).submatrix Sum.inr id :=
        hb ℓ n
      show (A.sum B).f ℓ (n * (θ + sumInrLin_ibl (A := A) (γ τ - θ.sumSnd)).read ℓ)
          * (θ + sumInrLin_ibl (A := A) (γ τ - θ.sumSnd)).write ℓ
        = (A.sum B).f ℓ (n * θ.read ℓ) * θ.write ℓ
      rw [f_sum_mul A B ℓ n, f_sum_mul A B ℓ n, hrl, hrr, hwl, hwr, hb']

variable (θ : Params (A.sum B) dIn dOut)

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the lift of the directions of `A` to the sum is injective. -/
private theorem sumInlLin_injective_ibl :
    Function.Injective (sumInlLin_ibl (A := A) (B := B) (dIn := dIn) (dOut := dOut)) := by
  intro a a' h
  have hE : a.E = a'.E := by have h1 := congrArg Params.E h; exact h1
  have hD : a.D = a'.D := by have h1 := congrArg Params.D h; exact h1
  refine Params.ext' hE (fun ℓ => ?_) (fun ℓ => ?_) hD
  · ext x j
    exact congrFun (congrFun (congrArg (fun p => p.read ℓ) h) x) (Sum.inl j)
  · ext i x
    exact congrFun (congrFun (congrArg (fun p => p.write ℓ) h) (Sum.inl i)) x

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the lift of the directions of `B` to the sum is injective. -/
private theorem sumInrLin_injective_ibl :
    Function.Injective (sumInrLin_ibl (A := A) (B := B) (dIn := dIn) (dOut := dOut)) := by
  intro b b' h
  have hE : b.E = b'.E := by have h1 := congrArg Params.E h; exact h1
  have hD : b.D = b'.D := by have h1 := congrArg Params.D h; exact h1
  refine Params.ext' hE (fun ℓ => ?_) (fun ℓ => ?_) hD
  · ext x j
    exact congrFun (congrFun (congrArg (fun p => p.read ℓ) h) x) (Sum.inr j)
  · ext i x
    exact congrFun (congrFun (congrArg (fun p => p.write ℓ) h) (Sum.inr i)) x

omit [Fintype T] [DecidableEq d] in
/-- Helper: the directions spanned by directions of symmetries inside the blocks have `E` and
`D` components `0` (linear conditions). -/
private theorem ED_eq_zero_of_mem_span_ibl {A' : Arch T d L} {θ' v : Params A' dIn dOut}
    (hv : v ∈ Submodule.span ℝ {η | InsideBlocks A' θ' η}) : v.E = 0 ∧ v.D = 0 := by
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨InsideBlocks.E_eq_zero hx, InsideBlocks.D_eq_zero hx⟩
  | zero => exact ⟨rfl, rfl⟩
  | add x y _ _ hx hy =>
    exact ⟨by rw [Params.add_E, hx.1, hy.1, add_zero], by rw [Params.add_D, hx.2, hy.2, add_zero]⟩
  | smul a x _ hx =>
    exact ⟨by rw [Params.smul_E, hx.1, smul_zero], by rw [Params.smul_D, hx.2, smul_zero]⟩

omit [Fintype T] [DecidableEq d] in
/-- Helper: the lifts of the directions of `V_A` and `V_B` are directions of symmetries inside
the blocks of the sum, and so is everything they span. -/
theorem sup_le_span_ibl (VA : Submodule ℝ (Params A dIn dOut))
    (VB : Submodule ℝ (Params B dIn dOut))
    (hVA : VA ≤ Submodule.span ℝ {η | InsideBlocks A θ.sumFst η})
    (hVB : VB ≤ Submodule.span ℝ {η | InsideBlocks B θ.sumSnd η}) :
    VA.map (sumInlLin_ibl (B := B)) ⊔ VB.map (sumInrLin_ibl (A := A))
      ≤ Submodule.span ℝ {η | InsideBlocks (A.sum B) θ η} := by
  refine sup_le ?_ ?_
  · rw [Submodule.map_le_iff_le_comap]
    refine hVA.trans (Submodule.span_le.2 fun η hη => ?_)
    exact Submodule.subset_span (InsideBlocks.sumInl (θ := θ) hη)
  · rw [Submodule.map_le_iff_le_comap]
    refine hVB.trans (Submodule.span_le.2 fun η hη => ?_)
    exact Submodule.subset_span (InsideBlocks.sumInr (θ := θ) hη)

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: in the lifts of `V_A` and `V_B`, a direction whose read of block `ℓ` is `0` has the
write of block `ℓ` `0`, if this holds in `V_A` and in `V_B`: the read columns and the write rows
of the two parts are disjoint. -/
theorem write_eq_zero_of_read_ibl (VA : Submodule ℝ (Params A dIn dOut))
    (VB : Submodule ℝ (Params B dIn dOut))
    (hrwA : ∀ η ∈ VA, ∀ ℓ, η.read ℓ = 0 → η.write ℓ = 0)
    (hrwB : ∀ η ∈ VB, ∀ ℓ, η.read ℓ = 0 → η.write ℓ = 0) :
    ∀ η ∈ VA.map (sumInlLin_ibl (B := B)) ⊔ VB.map (sumInrLin_ibl (A := A)), ∀ ℓ,
      η.read ℓ = 0 → η.write ℓ = 0 := by
  intro η hη ℓ hr
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hη
  obtain ⟨a, ha, rfl⟩ := Submodule.mem_map.1 hy
  obtain ⟨b, hb, rfl⟩ := Submodule.mem_map.1 hz
  -- the read columns of the part of `A`, and those of the part of `B`, are `0`
  have hra : a.read ℓ = 0 := by
    ext x j
    have h1 : a.read ℓ x j + 0 = 0 := congrFun (congrFun hr x) (Sum.inl j)
    rw [add_zero] at h1
    exact h1
  have hrb : b.read ℓ = 0 := by
    ext x j
    have h1 : 0 + b.read ℓ x j = 0 := congrFun (congrFun hr x) (Sum.inr j)
    rw [zero_add] at h1
    exact h1
  -- hence so are the write rows of the two parts
  have hwa := hrwA a ha ℓ hra
  have hwb := hrwB b hb ℓ hrb
  ext i x
  rcases i with i | i
  · show a.write ℓ i x + 0 = 0
    simp only [hwa, Matrix.zero_apply, add_zero]
  · show 0 + b.write ℓ i x = 0
    simp only [hwb, Matrix.zero_apply, add_zero]

omit [Fintype T] [DecidableEq d] in
/-- Helper: the lifts of `V_A` and `V_B` span a space of dimension `dim V_A + dim V_B`: the lifts
are injective, and they meet only at `0`, since a direction of `V_A` has `E = D = 0` and the two
parts have disjoint read columns and write rows. -/
theorem finrank_sup_ibl (VA : Submodule ℝ (Params A dIn dOut))
    (VB : Submodule ℝ (Params B dIn dOut))
    (hVA : VA ≤ Submodule.span ℝ {η | InsideBlocks A θ.sumFst η}) :
    Module.finrank ℝ ↥(VA.map (sumInlLin_ibl (B := B)) ⊔ VB.map (sumInrLin_ibl (A := A)))
      = Module.finrank ℝ VA + Module.finrank ℝ VB := by
  -- the two lifts meet only at `0`
  have hinf : VA.map (sumInlLin_ibl (B := B)) ⊓ VB.map (sumInrLin_ibl (A := A)) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Submodule.mem_map.1 (Submodule.mem_inf.1 hx).1
    obtain ⟨b, -, hab⟩ := Submodule.mem_map.1 (Submodule.mem_inf.1 hx).2
    obtain ⟨hE, hD⟩ := ED_eq_zero_of_mem_span_ibl (hVA ha)
    have ha0 : a = 0 := by
      refine Params.ext' hE (fun ℓ => ?_) (fun ℓ => ?_) hD
      · ext x j
        exact (congrFun (congrFun (congrArg (fun p => p.read ℓ) hab) x) (Sum.inl j)).symm
      · ext i x
        exact (congrFun (congrFun (congrArg (fun p => p.write ℓ) hab) (Sum.inl i)) x).symm
    rw [ha0, map_zero]
    exact Submodule.zero_mem _
  -- `dim (V_A' ⊔ V_B') + dim (V_A' ⊓ V_B') = dim V_A' + dim V_B'`
  have h := Submodule.finrank_sup_add_finrank_inf_eq (VA.map (sumInlLin_ibl (B := B)))
    (VB.map (sumInrLin_ibl (A := A)))
  rw [hinf, finrank_bot, add_zero,
    ← (Submodule.equivMapOfInjective _ sumInlLin_injective_ibl VA).finrank_eq,
    ← (Submodule.equivMapOfInjective _ sumInrLin_injective_ibl VB).finrank_eq] at h
  exact h

/-- **Theorem 4.3 of the dimension paper for a network with two kinds of block, without
normalization:** let `V_A` and `V_B` be spaces of directions spanned by directions of symmetries
inside the blocks of the two parts, in each of which a direction whose read of block `ℓ` is `0`
has the write of block `ℓ` `0`. If `E` and the writes of the sum have rank `d`,
`fd ≤ P − (L + 1) d² − dim V_A − dim V_B`. -/
theorem funDim_add_le_skipless_sum_of_insideBlocks (hA : A.χ = id)
    (VA : Submodule ℝ (Params A dIn dOut)) (VB : Submodule ℝ (Params B dIn dOut))
    (hVA : VA ≤ Submodule.span ℝ {η | InsideBlocks A θ.sumFst η})
    (hVB : VB ≤ Submodule.span ℝ {η | InsideBlocks B θ.sumSnd η})
    (hrwA : ∀ η ∈ VA, ∀ ℓ, η.read ℓ = 0 → η.write ℓ = 0)
    (hrwB : ∀ η ∈ VB, ∀ ℓ, η.read ℓ = 0 → η.write ℓ = 0)
    (hE : θ.E.rank = Fintype.card d) (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d) :
    funDim (A.sum B) 0 θ
        + ((L + 1) * Fintype.card d ^ 2 + (Module.finrank ℝ VA + Module.finrank ℝ VB))
      ≤ Module.finrank ℝ (Params (A.sum B) dIn dOut) := by
  -- the bound of `Symmetry/InsideBlocks.lean` for the lifts of `V_A` and `V_B` to the sum, of
  -- dimension `dim V_A + dim V_B`
  have h := funDim_add_le_skipless_of_insideBlocks θ hA _ (sup_le_span_ibl θ VA VB hVA hVB)
    (write_eq_zero_of_read_ibl VA VB hrwA hrwB) hE hw
  rwa [finrank_sup_ibl θ VA VB hVA] at h

/-- **The same under pre-RMSNorm** (any `ε`). -/
theorem funDim_add_le_skipless_sum_of_insideBlocks_rmsNorm (ε : ℝ) (hA : A.χ = rmsNorm ε)
    (VA : Submodule ℝ (Params A dIn dOut)) (VB : Submodule ℝ (Params B dIn dOut))
    (hVA : VA ≤ Submodule.span ℝ {η | InsideBlocks A θ.sumFst η})
    (hVB : VB ≤ Submodule.span ℝ {η | InsideBlocks B θ.sumSnd η})
    (hrwA : ∀ η ∈ VA, ∀ ℓ, η.read ℓ = 0 → η.write ℓ = 0)
    (hrwB : ∀ η ∈ VB, ∀ ℓ, η.read ℓ = 0 → η.write ℓ = 0)
    (hE : θ.E.rank = Fintype.card d) (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d) :
    funDim (A.sum B) 0 θ
        + ((L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2)
          + (Module.finrank ℝ VA + Module.finrank ℝ VB))
      ≤ Module.finrank ℝ (Params (A.sum B) dIn dOut) := by
  -- the bound of `Symmetry/InsideBlocks.lean` for the lifts of `V_A` and `V_B` to the sum
  have h := funDim_add_le_skipless_of_insideBlocks_rmsNorm θ ε hA _
    (sup_le_span_ibl θ VA VB hVA hVB) (write_eq_zero_of_read_ibl VA VB hrwA hrwB) hE hw
  rwa [finrank_sup_ibl θ VA VB hVA] at h

/-- **Theorem 4.2 of the skips paper with identity skips, for a network with two kinds of block,
without normalization:** if `E` has rank `d`, `fd ≤ P − d² − dim V_A − dim V_B`. -/
theorem funDim_add_le_residual_sum_of_insideBlocks (hA : A.χ = id)
    (VA : Submodule ℝ (Params A dIn dOut)) (VB : Submodule ℝ (Params B dIn dOut))
    (hVA : VA ≤ Submodule.span ℝ {η | InsideBlocks A θ.sumFst η})
    (hVB : VB ≤ Submodule.span ℝ {η | InsideBlocks B θ.sumSnd η})
    (hE : θ.E.rank = Fintype.card d) :
    funDim (A.sum B) 1 θ
        + (Fintype.card d ^ 2 + (Module.finrank ℝ VA + Module.finrank ℝ VB))
      ≤ Module.finrank ℝ (Params (A.sum B) dIn dOut) := by
  -- the bound of `Symmetry/InsideBlocks.lean` for the lifts of `V_A` and `V_B` to the sum
  have h := funDim_add_le_residual_of_insideBlocks θ hA _ (sup_le_span_ibl θ VA VB hVA hVB) hE
  rwa [finrank_sup_ibl θ VA VB hVA] at h

/-- **The same under pre-RMSNorm** (any `ε`). -/
theorem funDim_add_le_residual_sum_of_insideBlocks_rmsNorm (ε : ℝ) (hA : A.χ = rmsNorm ε)
    (VA : Submodule ℝ (Params A dIn dOut)) (VB : Submodule ℝ (Params B dIn dOut))
    (hVA : VA ≤ Submodule.span ℝ {η | InsideBlocks A θ.sumFst η})
    (hVB : VB ≤ Submodule.span ℝ {η | InsideBlocks B θ.sumSnd η})
    (hE : θ.E.rank = Fintype.card d) :
    funDim (A.sum B) 1 θ
        + (Fintype.card d * (Fintype.card d - 1) / 2
          + (Module.finrank ℝ VA + Module.finrank ℝ VB))
      ≤ Module.finrank ℝ (Params (A.sum B) dIn dOut) := by
  -- the bound of `Symmetry/InsideBlocks.lean` for the lifts of `V_A` and `V_B` to the sum
  have h := funDim_add_le_residual_of_insideBlocks_rmsNorm θ ε hA _
    (sup_le_span_ibl θ VA VB hVA hVB) hE
  rwa [finrank_sup_ibl θ VA VB hVA] at h

end Skips
