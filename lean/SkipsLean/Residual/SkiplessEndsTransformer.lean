import SkipsLean.Residual.SkiplessEndsAttention
import SkipsLean.Dimension.UpperBoundTransformer

/-!
# Skipless transformers: the changes of basis at the two ends and the symmetries inside the blocks

Paper (skips paper): proof of Theorem A.28 (ii). "In a skipless network of the same widths, with
embedding `E′` and readout `D′`, the changes of basis at `h_0` and `h_L`, those inside the heads
and the rescalings have orbits of dimension `2 d_model² + s` at generic parameters, where `E′`
and `D′` have rank `d_model` and the queries and values of every head have full column rank."
Under pre-RMSNorm: "the orthogonal changes of basis at `h_0` and `h_L`, which commute with the
normalization, have orbits of dimension `d_model (d_model − 1) + s` in the skipless network". The
proof of Lemma A.26 uses the bound at every parameter ("the rank is lower semicontinuous, so the
bound holds at every `η`").

Stated once for any architecture and any space `V` of directions spanned by directions of
symmetries inside the blocks (`Symmetry/InsideBlocks.lean`): a skipless network of `L ≥ 1` blocks
whose `E` and `D` have rank `d` has `fd ≤ P − 2 d² − dim V` (no condition on the writes: the
hidden states in between are not used). Then, for the networks of `Network/Transformer.lean`
(attention blocks and MLP blocks, or attention blocks and gated blocks, in any order, of any
widths), the bound on the rank of the Jacobian on every batch at EVERY parameter, with
`s = 2 ∑_ℓ H_ℓ d_{h,ℓ}²` (and `+ ∑_ℓ d_hidden,ℓ` for gated blocks). The twins for networks of one
kind of block: `Residual/SkiplessEnds.lean`, `Residual/SkiplessEndsAttention.lean`.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]

/-! ### Helpers: the changes of basis at `h_0` and `h_L` (copies of the `_se` helpers of
`Residual/SkiplessEnds.lean`) -/

/-- Helper (the private `mul_left_cancel_of_rank_se`): a matrix `M` of rank equal to its number of
columns cancels on the left, `M X = M Y → X = Y`. -/
private theorem mul_left_cancel_of_rank_set {m n k : Type*} [Fintype n] (M : Matrix m n ℝ)
    (hM : M.rank = Fintype.card n) {X Y : Matrix n k ℝ} (h : M * X = M * Y) : X = Y := by
  -- `v ↦ M v` is injective: `rank M + dim ker M = card n`
  have hinj : Function.Injective M.mulVecLin := by
    rw [← LinearMap.ker_eq_bot, ← Submodule.finrank_eq_zero]
    have := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
    rw [Module.finrank_fintype_fun_eq_card] at this
    rw [Matrix.rank] at hM
    omega
  -- compare `X` and `Y` column by column
  ext i j
  have hcol : M.mulVecLin (fun l => X l j) = M.mulVecLin (fun l => Y l j) := by
    funext p
    have := congrFun (congrFun h p) j
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
  exact congrFun (hinj hcol) i

/-- Helper (the private `mul_right_cancel_of_rank_se`): a matrix `M` of rank equal to its number
of rows cancels on the right, `X M = Y M → X = Y`. -/
private theorem mul_right_cancel_of_rank_set {m n k : Type*} [Fintype m] [Fintype n]
    (M : Matrix m n ℝ) (hM : M.rank = Fintype.card m) {X Y : Matrix k m ℝ} (h : X * M = Y * M) :
    X = Y := by
  have hT : Mᵀ * Xᵀ = Mᵀ * Yᵀ := by
    rw [← Matrix.transpose_mul, h, Matrix.transpose_mul]
  exact Matrix.transpose_injective
    (mul_left_cancel_of_rank_set Mᵀ (by rw [Matrix.rank_transpose]; exact hM) hT)

omit [Fintype d] [DecidableEq d] in
/-- Helper: the family `X` with `X_0 = p.1`, `X_L = p.2` and `X_ℓ = 0` at the hidden states in
between, as a linear map of `p = (X_0, X_L)`. -/
private noncomputable def endsLin_set (n : ℕ) :
    (Matrix d d ℝ × Matrix d d ℝ) →ₗ[ℝ] (Fin (n + 1) → Matrix d d ℝ) :=
  (LinearMap.single ℝ (fun _ : Fin (n + 1) => Matrix d d ℝ) 0).coprod
    (LinearMap.single ℝ (fun _ : Fin (n + 1) => Matrix d d ℝ) (Fin.last n))

omit [Fintype d] [DecidableEq d] in
/-- Helper: `0 ≠ L` as hidden states, for `L ≥ 1`. -/
private theorem zero_ne_last_set {n : ℕ} (hn : 0 < n) : (0 : Fin (n + 1)) ≠ Fin.last n := by
  rw [Ne, Fin.ext_iff, Fin.val_zero, Fin.val_last]
  omega

omit [Fintype d] [DecidableEq d] in
/-- Helper: the family `endsLin_set n p` at `h_0` is `p.1`. -/
private theorem endsLin_zero_set {n : ℕ} (hn : 0 < n) (p : Matrix d d ℝ × Matrix d d ℝ) :
    endsLin_set n p 0 = p.1 := by
  simp [endsLin_set, zero_ne_last_set hn]

omit [Fintype d] [DecidableEq d] in
/-- Helper: the family `endsLin_set n p` at `h_L` is `p.2`. -/
private theorem endsLin_last_set {n : ℕ} (hn : 0 < n) (p : Matrix d d ℝ × Matrix d d ℝ) :
    endsLin_set n p (Fin.last n) = p.2 := by
  simp [endsLin_set, (zero_ne_last_set hn).symm]

omit [DecidableEq d] in
/-- Helper: for antisymmetric `X_0`, `X_L`, every matrix of the family `endsLin_set n (X_0, X_L)`
is antisymmetric. -/
private theorem endsLin_mem_antisymmetric_set (n : ℕ) {a b : Matrix d d ℝ}
    (ha : a ∈ antisymmetric d) (hb : b ∈ antisymmetric d) (ℓ : Fin (n + 1)) :
    endsLin_set n (a, b) ℓ ∈ antisymmetric d := by
  simp only [endsLin_set, LinearMap.coprod_apply, LinearMap.coe_single, Pi.add_apply]
  refine Submodule.add_mem _ ?_ ?_
  · rw [Pi.single_apply]
    split_ifs
    · exact ha
    · exact Submodule.zero_mem _
  · rw [Pi.single_apply]
    split_ifs
    · exact hb
    · exact Submodule.zero_mem _

omit [Fintype T] [DecidableEq d] [Fintype dIn] in
/-- Helper: the embedding component `E X_0` determines `X_0` and the readout component `-X_L D`
determines `X_L`, when `E` and `D` have rank `d` (`L ≥ 1`, so `h_0 ≠ h_L`). -/
private theorem ends_eq_set {n : ℕ} (hn : 0 < n) {E : Matrix dIn d ℝ} {D : Matrix d dOut ℝ}
    (hE : E.rank = Fintype.card d) (hD : D.rank = Fintype.card d)
    {p q : Matrix d d ℝ × Matrix d d ℝ}
    (h0 : E * endsLin_set n p 0 = E * endsLin_set n q 0)
    (h1 : -(endsLin_set n p (Fin.last n) * D) = -(endsLin_set n q (Fin.last n) * D)) :
    p = q := by
  rw [endsLin_zero_set hn, endsLin_zero_set hn] at h0
  rw [endsLin_last_set hn, endsLin_last_set hn, neg_inj] at h1
  exact Prod.ext (mul_left_cancel_of_rank_set E hE h0) (mul_right_cancel_of_rank_set D hD h1)

omit [DecidableEq d] in
/-- Helper: the pairs `(X_0, X_L)` form a space of dimension `2 d²`. -/
private theorem finrank_ends_set :
    Module.finrank ℝ (Matrix d d ℝ × Matrix d d ℝ) = 2 * Fintype.card d ^ 2 := by
  rw [Module.finrank_prod, Module.finrank_matrix, Module.finrank_self]
  ring

/-- Helper: the pairs `(X_0, X_L)` of antisymmetric matrices form a space of dimension
`2 · d (d - 1) / 2 = d (d - 1)` (`d (d - 1)` is even). -/
private theorem finrank_ends_antisymmetric_set :
    Module.finrank ℝ (antisymmetric d × antisymmetric d)
      = Fintype.card d * (Fintype.card d - 1) := by
  rw [Module.finrank_prod, finrank_antisymmetric]
  have h := Nat.div_two_mul_two_of_even (Nat.even_mul_pred_self (Fintype.card d))
  generalize Fintype.card d * (Fintype.card d - 1) = k at h ⊢
  omega

/-! ### Helpers: the directions spanned by symmetries inside the blocks (copies of the `_ibl`
helpers of `Symmetry/InsideBlocks.lean` and `Symmetry/InsideBlocksSum.lean`) -/

omit [DecidableEq d] in
/-- Helper (the private `span_le_flat_ibl`): the directions spanned by directions of symmetries
inside the blocks are flat, for every stream. -/
private theorem span_le_flat_set {A : Arch T d L} (θ : Params A dIn dOut)
    (S : Fin L → Matrix d d ℝ) :
    Submodule.span ℝ {η | InsideBlocks A θ η} ≤ flat A S θ :=
  Submodule.span_le.2 fun _ hη => InsideBlocks.mem_flat hη S

omit [Fintype T] [DecidableEq d] in
/-- Helper (the private `ED_eq_zero_of_mem_span_ibl`): the directions spanned by directions of
symmetries inside the blocks have `E` and `D` components `0` (linear conditions). -/
private theorem ED_eq_zero_of_mem_span_set {A' : Arch T d L} {θ' v : Params A' dIn dOut}
    (hv : v ∈ Submodule.span ℝ {η | InsideBlocks A' θ' η}) : v.E = 0 ∧ v.D = 0 := by
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨InsideBlocks.E_eq_zero hx, InsideBlocks.D_eq_zero hx⟩
  | zero => exact ⟨rfl, rfl⟩
  | add x y _ _ hx hy =>
    exact ⟨by rw [Params.add_E, hx.1, hy.1, add_zero], by rw [Params.add_D, hx.2, hy.2, add_zero]⟩
  | smul a x _ hx =>
    exact ⟨by rw [Params.smul_E, hx.1, smul_zero], by rw [Params.smul_D, hx.2, smul_zero]⟩

omit [Fintype T] [DecidableEq d] [Fintype dIn] in
/-- Helper (Lemma B.1 with `X` supported on `h_0` and `h_L`, together with directions `v`, `v'` of
`E` and `D` components `0`): `cobDir θ X + v` determines `(X_0, X_L)` and `v`. The `E` component
`E X_0` gives `X_0`, the `D` component `−X_L D` gives `X_L`, and then `v`. -/
private theorem ends_add_inj_set {A : Arch T d L} (θ : Params A dIn dOut) (hL : 0 < L)
    (hE : θ.E.rank = Fintype.card d) (hD : θ.D.rank = Fintype.card d)
    {p q : Matrix d d ℝ × Matrix d d ℝ} {v v' : Params A dIn dOut}
    (hv : v.E = 0 ∧ v.D = 0) (hv' : v'.E = 0 ∧ v'.D = 0)
    (h : cobDir θ (endsLin_set L p) + v = cobDir θ (endsLin_set L q) + v') :
    p = q ∧ v = v' := by
  have hpq : p = q := by
    refine ends_eq_set hL hE hD ?_ ?_
    · -- the embedding: `E X_0 + v_E = E Y_0 + v'_E`, and `v_E = v'_E = 0`
      have h0 : θ.E * endsLin_set L p 0 + v.E = θ.E * endsLin_set L q 0 + v'.E :=
        congrArg Params.E h
      rwa [hv.1, hv'.1, add_zero, add_zero] at h0
    · -- the readout: `−X_L D + v_D = −Y_L D + v'_D`, and `v_D = v'_D = 0`
      have h1 : -(endsLin_set L p (Fin.last L) * θ.D) + v.D
          = -(endsLin_set L q (Fin.last L) * θ.D) + v'.D := congrArg Params.D h
      rwa [hv.2, hv'.2, add_zero, add_zero] at h1
  subst hpq
  exact ⟨rfl, add_left_cancel h⟩

/-- **Proof of Theorem A.28 (ii) of the skips paper, "the changes of basis at `h_0` and `h_L`"
and the symmetries inside the blocks, without normalization, for any architecture:** for a
skipless network of `L ≥ 1` blocks whose `E` and `D` have rank `d`, and a space `V` of directions
spanned by directions of symmetries inside the blocks, `fd ≤ P − 2 d² − dim V`. -/
theorem funDim_add_le_skipless_ends_of_insideBlocks {A : Arch T d L} (hA : A.χ = id)
    (hL : 0 < L) (θ : Params A dIn dOut) (V : Submodule ℝ (Params A dIn dOut))
    (hV : V ≤ Submodule.span ℝ {η | InsideBlocks A θ η})
    (hE : θ.E.rank = Fintype.card d) (hD : θ.D.rank = Fintype.card d) :
    funDim A 0 θ + (2 * Fintype.card d ^ 2 + Module.finrank ℝ V)
      ≤ Module.finrank ℝ (Params A dIn dOut) := by
  -- the linear map `((X_0, X_L), v) ↦ cobDir θ (ends X_0 X_L) + v`
  let Φ : (Matrix d d ℝ × Matrix d d ℝ) × V →ₗ[ℝ] Params A dIn dOut :=
    ((cobDirLin θ).comp (endsLin_set L)).coprod V.subtype
  -- its directions are flat: the changes of basis are, and so are the directions of `V`
  have hflat : LinearMap.range Φ ≤ flat A 0 θ := by
    rintro _ ⟨p, rfl⟩
    rw [LinearMap.coprod_apply]
    exact Submodule.add_mem _ (cobDir_mem_flat_skipless' θ hA (endsLin_set L p.1))
      (span_le_flat_set θ 0 (hV p.2.2))
  -- it is injective: `E X_0` gives `X_0`, `−X_L D` gives `X_L`, then `v`
  have hinj : Function.Injective Φ := by
    intro a b h
    have h' : cobDir θ (endsLin_set L a.1) + (a.2 : Params A dIn dOut)
        = cobDir θ (endsLin_set L b.1) + b.2 := h
    obtain ⟨h1, h2⟩ := ends_add_inj_set θ hL hE hD (ED_eq_zero_of_mem_span_set (hV a.2.2))
      (ED_eq_zero_of_mem_span_set (hV b.2.2)) h'
    exact Prod.ext h1 (Subtype.ext h2)
  -- the domain has dimension `2 d² + dim V`
  have h := funDim_add_finrank_le_of_le_flat' θ _ hflat
  rwa [LinearMap.finrank_range_of_inj hinj, Module.finrank_prod, finrank_ends_set] at h

/-- **The same under pre-RMSNorm** (any `ε`), with the orthogonal changes of basis at `h_0` and
`h_L`: `fd ≤ P − d (d − 1) − dim V`. -/
theorem funDim_add_le_skipless_ends_of_insideBlocks_rmsNorm {A : Arch T d L} (ε : ℝ)
    (hA : A.χ = rmsNorm ε) (hL : 0 < L) (θ : Params A dIn dOut)
    (V : Submodule ℝ (Params A dIn dOut))
    (hV : V ≤ Submodule.span ℝ {η | InsideBlocks A θ η})
    (hE : θ.E.rank = Fintype.card d) (hD : θ.D.rank = Fintype.card d) :
    funDim A 0 θ + (Fintype.card d * (Fintype.card d - 1) + Module.finrank ℝ V)
      ≤ Module.finrank ℝ (Params A dIn dOut) := by
  -- the same linear map, with `X_0`, `X_L` antisymmetric
  let Φ : (antisymmetric d × antisymmetric d) × V →ₗ[ℝ] Params A dIn dOut :=
    (((cobDirLin θ).comp (endsLin_set L)).comp
        ((antisymmetric d).subtype.prodMap (antisymmetric d).subtype)).coprod V.subtype
  -- its directions are flat: the orthogonal changes of basis are, and so are those of `V`
  have hflat : LinearMap.range Φ ≤ flat A 0 θ := by
    rintro _ ⟨p, rfl⟩
    rw [LinearMap.coprod_apply]
    exact Submodule.add_mem _
      (cobDir_mem_flat_skipless_rmsNorm' θ ε hA
        (endsLin_set L ((p.1.1 : Matrix d d ℝ), (p.1.2 : Matrix d d ℝ)))
        fun ℓ => endsLin_mem_antisymmetric_set L p.1.1.2 p.1.2.2 ℓ)
      (span_le_flat_set θ 0 (hV p.2.2))
  -- it is injective: `E X_0` gives `X_0`, `−X_L D` gives `X_L`, then `v`
  have hinj : Function.Injective Φ := by
    intro a b h
    have h' : cobDir θ (endsLin_set L ((a.1.1 : Matrix d d ℝ), (a.1.2 : Matrix d d ℝ)))
          + (a.2 : Params A dIn dOut)
        = cobDir θ (endsLin_set L ((b.1.1 : Matrix d d ℝ), (b.1.2 : Matrix d d ℝ))) + b.2 := h
    obtain ⟨h1, h2⟩ := ends_add_inj_set θ hL hE hD (ED_eq_zero_of_mem_span_set (hV a.2.2))
      (ED_eq_zero_of_mem_span_set (hV b.2.2)) h'
    exact Prod.ext (Prod.ext (Subtype.ext (congrArg Prod.fst h1))
      (Subtype.ext (congrArg Prod.snd h1))) (Subtype.ext h2)
  -- the domain has dimension `d (d − 1) + dim V`
  have h := funDim_add_finrank_le_of_le_flat' θ _ hflat
  rwa [LinearMap.finrank_range_of_inj hinj, Module.finrank_prod,
    finrank_ends_antisymmetric_set] at h

variable {sees : T → T → Prop} [DecidableRel sees]
variable {H dh hid : Fin L → Type} [∀ ℓ, Fintype (H ℓ)] [∀ ℓ, Fintype (dh ℓ)]
  [∀ ℓ, Fintype (hid ℓ)] {σ σ' : ℝ → ℝ} {ε : ℝ}

/-! ### Helpers: the lifts of the two parts to the sum (copies of the `_ibl` helpers of
`Symmetry/InsideBlocksSum.lean`) -/

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: `Params.sumInl`, the lift of a direction of `A` to the sum, as a linear map. -/
private def sumInlLin_set {A B : Arch T d L} :
    Params A dIn dOut →ₗ[ℝ] Params (A.sum B) dIn dOut where
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

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: `Params.sumInr`, the lift of a direction of `B` to the sum, as a linear map. -/
private def sumInrLin_set {A B : Arch T d L} :
    Params B dIn dOut →ₗ[ℝ] Params (A.sum B) dIn dOut where
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

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the lift of the directions of `A` to the sum is injective. -/
private theorem sumInlLin_injective_set {A B : Arch T d L} :
    Function.Injective (sumInlLin_set (A := A) (B := B) (dIn := dIn) (dOut := dOut)) := by
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
private theorem sumInrLin_injective_set {A B : Arch T d L} :
    Function.Injective (sumInrLin_set (A := A) (B := B) (dIn := dIn) (dOut := dOut)) := by
  intro b b' h
  have hE : b.E = b'.E := by have h1 := congrArg Params.E h; exact h1
  have hD : b.D = b'.D := by have h1 := congrArg Params.D h; exact h1
  refine Params.ext' hE (fun ℓ => ?_) (fun ℓ => ?_) hD
  · ext x j
    exact congrFun (congrFun (congrArg (fun p => p.read ℓ) h) x) (Sum.inr j)
  · ext i x
    exact congrFun (congrFun (congrArg (fun p => p.write ℓ) h) (Sum.inr i)) x

omit [Fintype T] [DecidableEq d] in
/-- Helper (the private `sup_le_span_ibl`): the lifts of the directions of `V_A` and `V_B` are
directions of symmetries inside the blocks of the sum, and so is everything they span. -/
private theorem sup_le_span_set {A B : Arch T d L} (θ : Params (A.sum B) dIn dOut)
    (VA : Submodule ℝ (Params A dIn dOut)) (VB : Submodule ℝ (Params B dIn dOut))
    (hVA : VA ≤ Submodule.span ℝ {η | InsideBlocks A θ.sumFst η})
    (hVB : VB ≤ Submodule.span ℝ {η | InsideBlocks B θ.sumSnd η}) :
    VA.map (sumInlLin_set (B := B)) ⊔ VB.map (sumInrLin_set (A := A))
      ≤ Submodule.span ℝ {η | InsideBlocks (A.sum B) θ η} := by
  refine sup_le ?_ ?_
  · rw [Submodule.map_le_iff_le_comap]
    refine hVA.trans (Submodule.span_le.2 fun η hη => ?_)
    exact Submodule.subset_span (InsideBlocks.sumInl (θ := θ) hη)
  · rw [Submodule.map_le_iff_le_comap]
    refine hVB.trans (Submodule.span_le.2 fun η hη => ?_)
    exact Submodule.subset_span (InsideBlocks.sumInr (θ := θ) hη)

omit [Fintype T] [DecidableEq d] in
/-- Helper (the private `finrank_sup_ibl`): the lifts of `V_A` and `V_B` span a space of dimension
`dim V_A + dim V_B`: the lifts are injective, and they meet only at `0`. -/
private theorem finrank_sup_set {A B : Arch T d L} (θ : Params (A.sum B) dIn dOut)
    (VA : Submodule ℝ (Params A dIn dOut)) (VB : Submodule ℝ (Params B dIn dOut))
    (hVA : VA ≤ Submodule.span ℝ {η | InsideBlocks A θ.sumFst η}) :
    Module.finrank ℝ ↥(VA.map (sumInlLin_set (B := B)) ⊔ VB.map (sumInrLin_set (A := A)))
      = Module.finrank ℝ VA + Module.finrank ℝ VB := by
  -- the two lifts meet only at `0`
  have hinf : VA.map (sumInlLin_set (B := B)) ⊓ VB.map (sumInrLin_set (A := A)) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Submodule.mem_map.1 (Submodule.mem_inf.1 hx).1
    obtain ⟨b, -, hab⟩ := Submodule.mem_map.1 (Submodule.mem_inf.1 hx).2
    obtain ⟨hE, hD⟩ := ED_eq_zero_of_mem_span_set (hVA ha)
    have ha0 : a = 0 := by
      refine Params.ext' hE (fun ℓ => ?_) (fun ℓ => ?_) hD
      · ext x j
        exact (congrFun (congrFun (congrArg (fun p => p.read ℓ) hab) x) (Sum.inl j)).symm
      · ext i x
        exact (congrFun (congrFun (congrArg (fun p => p.write ℓ) hab) (Sum.inl i)) x).symm
    rw [ha0, map_zero]
    exact Submodule.zero_mem _
  -- `dim (V_A' ⊔ V_B') + dim (V_A' ⊓ V_B') = dim V_A' + dim V_B'`
  have h := Submodule.finrank_sup_add_finrank_inf_eq (VA.map (sumInlLin_set (B := B)))
    (VB.map (sumInrLin_set (A := A)))
  rw [hinf, finrank_bot, add_zero,
    ← (Submodule.equivMapOfInjective _ sumInlLin_injective_set VA).finrank_eq,
    ← (Submodule.equivMapOfInjective _ sumInrLin_injective_set VB).finrank_eq] at h
  exact h

/-! ### Helpers: the changes of basis inside the heads and the rescalings of the values (copies of
the `_ubt` helpers of `Dimension/UpperBoundTransformer.lean`) -/

/-- Helper (the private `headDirQKLin_ubt`): `Γ ↦ headDirQK θ Γ` is linear. -/
private noncomputable def headDirQKLin_set {χ : Matrix T d ℝ → Matrix T d ℝ}
    (θ : Params (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut) :
    (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) →ₗ[ℝ]
      Params (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut where
  toFun := headDirQK θ
  map_add' Γ Δ := by
    apply Params.ext'
    · simp [headDirQK]
    · intro ℓ
      ext a ⟨i, k | k | k⟩
      · simp only [headDirQK, Params.add_read, Matrix.add_apply, Matrix.of_apply, Pi.add_apply,
          mul_add, Finset.sum_add_distrib]
      · simp only [headDirQK, Params.add_read, Matrix.add_apply, Matrix.of_apply, Pi.add_apply,
          mul_add, Finset.sum_add_distrib, neg_add]
      · simp [headDirQK]
    · intro ℓ
      simp [headDirQK]
    · simp [headDirQK]
  map_smul' c Γ := by
    apply Params.ext'
    · simp [headDirQK]
    · intro ℓ
      ext a ⟨i, k | k | k⟩
      · simp only [headDirQK, Params.smul_read, Matrix.smul_apply, Matrix.of_apply, Pi.smul_apply,
          smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => by ring
      · simp only [headDirQK, Params.smul_read, Matrix.smul_apply, Matrix.of_apply, Pi.smul_apply,
          smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_neg]
        exact congrArg Neg.neg (Finset.sum_congr rfl fun _ _ => by ring)
      · simp [headDirQK]
    · intro ℓ
      simp [headDirQK]
    · simp [headDirQK]

/-- Helper (the private `headDirVOLin_ubt`): `Γ' ↦ headDirVO θ Γ'` is linear. -/
private noncomputable def headDirVOLin_set {χ : Matrix T d ℝ → Matrix T d ℝ}
    (θ : Params (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut) :
    (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) →ₗ[ℝ]
      Params (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut where
  toFun := headDirVO θ
  map_add' Γ Δ := by
    apply Params.ext'
    · simp [headDirVO]
    · intro ℓ
      ext a ⟨i, k | k | k⟩
      · simp [headDirVO]
      · simp [headDirVO]
      · simp only [headDirVO, Params.add_read, Matrix.add_apply, Matrix.of_apply, Pi.add_apply,
          mul_add, Finset.sum_add_distrib]
    · intro ℓ
      ext p b
      simp only [headDirVO, Params.add_write, Matrix.add_apply, Matrix.of_apply, Pi.add_apply,
        add_mul, Finset.sum_add_distrib, neg_add]
    · simp [headDirVO]
  map_smul' c Γ := by
    apply Params.ext'
    · simp [headDirVO]
    · intro ℓ
      ext a ⟨i, k | k | k⟩
      · simp [headDirVO]
      · simp [headDirVO]
      · simp only [headDirVO, Params.smul_read, Matrix.smul_apply, Matrix.of_apply, Pi.smul_apply,
          smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => by ring
    · intro ℓ
      ext p b
      simp only [headDirVO, Params.smul_write, Matrix.smul_apply, Matrix.of_apply, Pi.smul_apply,
        smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_neg]
      exact congrArg Neg.neg (Finset.sum_congr rfl fun _ _ => by ring)
    · simp [headDirVO]

/-- Helper (the private `finrank_headFun_ubt`): the families `Γ` of `d_h × d_h` matrices, one for
each head of each block, form a space of dimension `∑_ℓ H_ℓ d_{h,ℓ}²`. -/
private theorem finrank_headFun_set :
    Module.finrank ℝ (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)
      = ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2 := by
  rw [Module.finrank_pi_fintype]
  simp only [Module.finrank_pi_fintype, Module.finrank_matrix, Module.finrank_self, mul_one,
    Finset.sum_const, Finset.card_univ, smul_eq_mul, sq]

omit [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (the private `headDirLin_injective_ubt`): if the query and the value matrix of every
head have rank `d_h`, the direction `headDirQK θ Γ + headDirVO θ Γ'` determines `Γ` and `Γ'`. -/
private theorem headDirLin_injective_set {χ : Matrix T d ℝ → Matrix T d ℝ}
    (θ : Params (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut)
    (hQ : ∀ ℓ (i : H ℓ), ((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k)).rank
      = Fintype.card (dh ℓ))
    (hV : ∀ ℓ (i : H ℓ),
      ((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))).rank
        = Fintype.card (dh ℓ)) :
    Function.Injective ((headDirQKLin_set θ).coprod (headDirVOLin_set θ)) := by
  rintro ⟨Γ, Γ'⟩ ⟨Δ, Δ'⟩ h
  have h' : headDirQK θ Γ + headDirVO θ Γ' = headDirQK θ Δ + headDirVO θ Δ' := h
  -- the entry `(a, p)` of the read of block `ℓ`
  have hr : ∀ ℓ a p, (headDirQK θ Γ + headDirVO θ Γ').read ℓ a p
      = (headDirQK θ Δ + headDirVO θ Δ').read ℓ a p := fun ℓ a p => by rw [h']
  refine Prod.ext ?_ ?_ <;> funext ℓ i
  · -- the query columns of head `i`: `W_{Q,i} Γ_i = W_{Q,i} Δ_i`, and `W_{Q,i}` has rank `d_h`
    refine mul_left_cancel_of_rank_set _ (hQ ℓ i) (Matrix.ext fun a k => ?_)
    have := hr ℓ a (i, Sum.inl k)
    simp only [Params.add_read, Matrix.add_apply, headDirQK, headDirVO, Matrix.of_apply,
      add_zero] at this
    simpa only [Matrix.mul_apply, Matrix.submatrix_apply, id] using this
  · -- the value columns of head `i`: `W_{V,i} Γ'_i = W_{V,i} Δ'_i`
    refine mul_left_cancel_of_rank_set _ (hV ℓ i) (Matrix.ext fun a k => ?_)
    have := hr ℓ a (i, Sum.inr (Sum.inr k))
    simp only [Params.add_read, Matrix.add_apply, headDirQK, headDirVO, Matrix.of_apply,
      zero_add] at this
    simpa only [Matrix.mul_apply, Matrix.submatrix_apply, id] using this

omit [DecidableEq d] in
/-- Helper (the private `attn_part_ubt`, without its condition on the writes): the directions of
the changes of basis inside the heads span a space `V_A` of directions of symmetries inside the
blocks, of dimension `2 ∑_ℓ H_ℓ d_{h,ℓ}²`. -/
private theorem attn_part_set {χ : Matrix T d ℝ → Matrix T d ℝ}
    (θ : Params (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut)
    (hQ : ∀ ℓ (i : H ℓ), ((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k)).rank
      = Fintype.card (dh ℓ))
    (hV : ∀ ℓ (i : H ℓ),
      ((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))).rank
        = Fintype.card (dh ℓ)) :
    ∃ V : Submodule ℝ (Params (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut),
      V ≤ Submodule.span ℝ {η | InsideBlocks (Arch.attention sees χ H dh) θ η} ∧
      Module.finrank ℝ V = 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2 := by
  refine ⟨LinearMap.range ((headDirQKLin_set θ).coprod (headDirVOLin_set θ)), ?_, ?_⟩
  · -- each of the two summands is a direction of a symmetry inside the blocks
    rintro _ ⟨p, rfl⟩
    rw [LinearMap.coprod_apply]
    exact Submodule.add_mem _ (Submodule.subset_span (insideBlocks_headDirQK θ p.1))
      (Submodule.subset_span (insideBlocks_headDirVO θ p.2))
  · -- the map `(Γ, Γ') ↦ headDirQK θ Γ + headDirVO θ Γ'` is injective
    rw [LinearMap.finrank_range_of_inj (headDirLin_injective_set θ hQ hV), Module.finrank_prod,
      finrank_headFun_set, two_mul]

omit [Fintype T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (the private `rescaleDirLin_ubt`): `α ↦ rescaleDir θ α` is linear. -/
private noncomputable def rescaleDirLin_set {χ : Matrix T d ℝ → Matrix T d ℝ}
    (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut) :
    (∀ ℓ, hid ℓ → ℝ) →ₗ[ℝ] Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut where
  toFun := rescaleDir θ
  map_add' α β := by
    apply Params.ext'
    · simp [rescaleDir]
    · intro ℓ
      ext k j
      cases j with
      | inl i => simp [rescaleDir]
      | inr i =>
        simp only [rescaleDir, Pi.add_apply, Params.add_read, Matrix.add_apply, Matrix.of_apply,
          Sum.elim_inr]
        ring
    · intro ℓ
      ext i k
      simp [rescaleDir, add_mul]
    · simp [rescaleDir]
  map_smul' c α := by
    apply Params.ext'
    · simp [rescaleDir]
    · intro ℓ
      ext k j
      cases j <;> simp [rescaleDir, mul_assoc]
    · intro ℓ
      ext i k
      simp [rescaleDir, mul_assoc]
    · simp [rescaleDir]

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (the private `rescale_eq_zero_ubt`): if no value column of the read of block `ℓ`
vanishes and the read of block `ℓ` of `rescaleDir θ α` is `0`, then `α_{ℓ,i} = 0` for every
hidden unit `i` of block `ℓ`. -/
private theorem rescale_eq_zero_set {χ : Matrix T d ℝ → Matrix T d ℝ}
    (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut)
    (hv : ∀ ℓ i, (fun k => θ.read ℓ k (Sum.inr i)) ≠ 0) (α : ∀ ℓ, hid ℓ → ℝ) (ℓ : Fin L)
    (h0 : (rescaleDir θ α).read ℓ = 0) (i : hid ℓ) : α ℓ i = 0 := by
  by_contra hα
  refine hv ℓ i (funext fun k => ?_)
  have := congrFun (congrFun h0 k) (Sum.inr i)
  simp only [rescaleDir, Matrix.of_apply, Sum.elim_inr, Matrix.zero_apply] at this
  rcases mul_eq_zero.1 this with h | h
  · exact absurd (neg_eq_zero.1 h) hα
  · exact h

omit [Fintype T] [DecidableEq d] in
/-- Helper (the private `gated_part_ubt`, without its condition on the writes): the directions of
the rescalings of the values of the gated units span a space `V_B` of directions of symmetries
inside the blocks, of dimension `∑_ℓ d_hidden,ℓ`. -/
private theorem gated_part_set {χ : Matrix T d ℝ → Matrix T d ℝ}
    (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut)
    (hv : ∀ ℓ i, (fun k => θ.read ℓ k (Sum.inr i)) ≠ 0) :
    ∃ V : Submodule ℝ (Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut),
      V ≤ Submodule.span ℝ {η | InsideBlocks (Arch.gated σ χ hid) θ η} ∧
      Module.finrank ℝ V = ∑ ℓ, Fintype.card (hid ℓ) := by
  -- `α ↦ rescaleDir θ α` is injective, since its kernel is `0`
  have hinj : Function.Injective (rescaleDirLin_set θ) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro α hα
    have hα' : rescaleDir θ α = 0 := hα
    funext ℓ i
    exact rescale_eq_zero_set θ hv α ℓ (by rw [hα']; rfl) i
  refine ⟨LinearMap.range (rescaleDirLin_set θ), ?_, ?_⟩
  · rintro _ ⟨α, rfl⟩
    exact Submodule.subset_span (insideBlocks_rescaleDir θ α)
  · rw [LinearMap.finrank_range_of_inj hinj, Module.finrank_pi_fintype]
    simp [Module.finrank_fintype_fun_eq_card]

/-! ### Helpers: generic parameters (copies of the `_se` helpers of `Residual/SkiplessEnds.lean`
and of the `_ubt` helpers of `Dimension/UpperBoundTransformer.lean`) -/

omit [Fintype T] in
/-- Helper (the private `rank_eq_of_isUnit_det_rows_se`): a matrix with `d` columns has rank `d`
if some `d` of its rows form an invertible matrix. -/
private theorem rank_eq_of_isUnit_det_rows_set {m : Type*} (M : Matrix m d ℝ) (ρ : d ↪ m)
    (h : IsUnit (M.submatrix ρ id).det) : M.rank = Fintype.card d :=
  le_antisymm (Matrix.rank_le_card_width M)
    ((Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).2 h)).symm.le.trans
      (Matrix.rank_submatrix_le M ρ id))

/-- Helper (the private `ae_rank_E_D_se`): at generic parameters `E` and `D` have rank `d`, when
`d_in ≥ d` and `d_out ≥ d`. -/
private theorem ae_rank_E_D_set {A : Arch T d L} (μ : Measure (Params A dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, θ.E.rank = Fintype.card d ∧ θ.D.rank = Fintype.card d := by
  -- `d` rows of `E` and `d` columns of `D`, invertible at generic parameters
  obtain ⟨ρ⟩ := Function.Embedding.nonempty_of_card_le hdIn
  obtain ⟨c⟩ := Function.Embedding.nonempty_of_card_le hdOut
  filter_upwards [ae_isUnit_det_submatrix μ] with θ hθ
  exact ⟨rank_eq_of_isUnit_det_rows_set θ.E ρ (hθ.2.2.1 ρ),
    rank_eq_card_of_isUnit_det θ.D c (hθ.2.1 c)⟩

omit [Fintype T] [DecidableEq d] in
/-- Helper (the private `analyticOnNhd_det_ubt`): the determinant of a square matrix that depends
linearly on the parameters is an analytic function of the parameters. -/
private theorem analyticOnNhd_det_set {A : Arch T d L} {n : Type*} [Fintype n] [DecidableEq n]
    (Φ : Params A dIn dOut →ₗ[ℝ] Matrix n n ℝ) :
    AnalyticOnNhd ℝ (fun θ => (Φ θ).det) Set.univ := by
  simp only [Matrix.det_apply']
  exact Finset.analyticOnNhd_fun_sum _ fun σ _ => analyticOnNhd_const.mul
    (Finset.analyticOnNhd_fun_prod _ fun i _ =>
      analyticOnNhd_linear ((Matrix.entryLinearMap ℝ ℝ (σ i) i).comp Φ))

/-- Helper (the private `exists_submatrix_eq_one_ubt`): a matrix whose submatrix on the rows `r`
and the columns `c` (both injective) is the identity. -/
private theorem exists_submatrix_eq_one_set {m p n : Type*} [DecidableEq n] {r : n → m}
    (hr : Function.Injective r) {c : n → p} (hc : Function.Injective c) :
    ∃ M : Matrix m p ℝ, M.submatrix r c = 1 := by
  classical
  refine ⟨Matrix.of fun a b => if ∃ x, r x = a ∧ c x = b then 1 else 0, ?_⟩
  ext x y
  simp [Matrix.one_apply, hr.eq_iff, hc.eq_iff]

omit [Fintype T] [DecidableEq d] in
/-- Helper (the private `ae_rank_read_cols_ubt`): at generic parameters, `n ≤ d` distinct columns
`c` of the read of block `ℓ` form a matrix of rank `n`. -/
private theorem ae_rank_read_cols_set {A : Arch T d L} (μ : Measure (Params A dIn dOut))
    [μ.IsAddHaarMeasure] (ℓ : Fin L) {n : Type*} [Fintype n] [DecidableEq n] {c : n → A.r ℓ}
    (hc : Function.Injective c) (hn : Fintype.card n ≤ Fintype.card d) :
    ∀ᵐ θ ∂μ, ((θ.read ℓ).submatrix id c).rank = Fintype.card n := by
  -- `n` rows `ρ`, and the square submatrix of the read on the rows `ρ` and the columns `c`
  obtain ⟨ρ⟩ := Function.Embedding.nonempty_of_card_le hn
  obtain ⟨M, hM⟩ := exists_submatrix_eq_one_set ρ.injective hc
  let Φ : Params A dIn dOut →ₗ[ℝ] Matrix n n ℝ :=
    { toFun := fun θ => ((θ.read ℓ).submatrix id c).submatrix ρ id
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  -- it is the identity at the parameter whose read `ℓ` is `M`, so its determinant is not
  -- identically zero, and it is nonzero almost everywhere
  have hne : ∃ θ, (Φ θ).det ≠ 0 := by
    refine ⟨⟨0, Pi.single ℓ M, 0, 0⟩, ?_⟩
    show ((Pi.single (M := fun ℓ => Matrix d (A.r ℓ) ℝ) ℓ M ℓ).submatrix ρ c).det ≠ 0
    rw [Pi.single_eq_same, hM, Matrix.det_one]
    exact one_ne_zero
  filter_upwards [ae_ne_zero_of_analytic μ (analyticOnNhd_det_set Φ) hne] with θ hθ
  -- an invertible `n × n` submatrix gives rank `≥ n`, and the rank is at most the width `n`
  have h1 : (((θ.read ℓ).submatrix id c).submatrix ρ id).rank = Fintype.card n :=
    Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hθ))
  have h2 : (((θ.read ℓ).submatrix id c).submatrix ρ id).rank
      ≤ ((θ.read ℓ).submatrix id c).rank :=
    Matrix.rank_submatrix_le _ ρ id
  have h3 := Matrix.rank_le_card_width ((θ.read ℓ).submatrix id c)
  omega

omit [DecidableEq d] in
/-- Helper (the private `ae_rank_QV_ubt`): at generic parameters the query matrix and the value
matrix of every head of the first part of a sum have rank `d_h`, when `d_h ≤ d`. -/
private theorem ae_rank_QV_set {B : Arch T d L} {χ : Matrix T d ℝ → Matrix T d ℝ}
    (μ : Measure (Params ((Arch.attention (T := T) (d := d) sees χ H dh).sum B) dIn dOut))
    [μ.IsAddHaarMeasure] (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) :
    ∀ᵐ θ ∂μ, (∀ ℓ (i : H ℓ), ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k)).rank
        = Fintype.card (dh ℓ)) ∧
      ∀ ℓ (i : H ℓ),
        ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))).rank
          = Fintype.card (dh ℓ) := by
  classical
  -- finitely many conditions, two for each head of each block
  refine (ae_all_iff.2 fun ℓ => ae_all_iff.2 fun i => ?_).and
    (ae_all_iff.2 fun ℓ => ae_all_iff.2 fun i => ?_)
  · exact ae_rank_read_cols_set μ ℓ (c := fun k : dh ℓ => Sum.inl (i, Sum.inl k))
      (fun _ _ h => Sum.inl_injective (Prod.mk.inj (Sum.inl_injective h)).2) (hdh ℓ)
  · exact ae_rank_read_cols_set μ ℓ (c := fun k : dh ℓ => Sum.inl (i, Sum.inr (Sum.inr k)))
      (fun _ _ h => Sum.inr_injective (Sum.inr_injective (Prod.mk.inj (Sum.inl_injective h)).2))
      (hdh ℓ)

omit [Fintype T] [DecidableEq d] in
/-- Helper (the private `ae_value_ne_zero_ubt`): at generic parameters no value column of the
gated part of a read vanishes. -/
private theorem ae_value_ne_zero_set [Nonempty d] {A : Arch T d L}
    {χ : Matrix T d ℝ → Matrix T d ℝ}
    (μ : Measure (Params (A.sum (Arch.gated (T := T) (d := d) σ χ hid)) dIn dOut))
    [μ.IsAddHaarMeasure] :
    ∀ᵐ θ ∂μ, ∀ ℓ i, (fun k => θ.sumSnd.read ℓ k (Sum.inr i)) ≠ 0 := by
  -- finitely many conditions, one for each hidden unit `i` of each block `ℓ`
  refine ae_all_iff.2 fun ℓ => ae_all_iff.2 fun i => ?_
  -- an entry `k₀` of the value column
  obtain k₀ : d := Classical.arbitrary d
  -- the entry `θ ↦ θ.read ℓ k₀ (inr (inr i))` is a linear functional of the parameters
  let l : Params (A.sum (Arch.gated (T := T) (d := d) σ χ hid)) dIn dOut →ₗ[ℝ] ℝ :=
    (Matrix.entryLinearMap ℝ ℝ k₀ (Sum.inr (Sum.inr i))).comp
      (Params.linRead (A := A.sum (Arch.gated (T := T) (d := d) σ χ hid)) (dIn := dIn)
        (dOut := dOut) ℓ)
  have hl : ∀ θ, l θ = θ.read ℓ k₀ (Sum.inr (Sum.inr i)) := fun θ => rfl
  -- it is not zero at the parameters whose reads have all entries `1`
  have h₁ : l ⟨0, fun _ => Matrix.of fun _ _ => 1, 0, 0⟩ ≠ 0 := by
    rw [hl]
    exact one_ne_zero
  -- an analytic function that is not identically zero is nonzero almost everywhere
  have hne : ∀ᵐ θ ∂μ, l θ ≠ 0 :=
    ae_ne_zero_of_analytic μ (analyticOnNhd_linear l) ⟨_, h₁⟩
  -- and a function with a nonzero entry is not zero
  filter_upwards [hne] with θ h hz
  exact h (by rw [hl]; exact congrFun hz k₀)

omit [DecidableEq d] in
/-- Helper (the private `jacobianRank_add_le_of_ae_se`; the proof of Lemma A.26: "the rank is
lower semicontinuous, so the bound holds at every `η`"): for real-analytic `f_ℓ` and `χ`, a bound
`fd(θ') + k ≤ P` at almost every `θ'` gives the bound `rank J_X(θ) + k ≤ P` on every batch `X` at
every `θ`. -/
private theorem jacobianRank_add_le_of_ae_set {A : Arch T d L}
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (hχ : AnalyticOnNhd ℝ A.χ Set.univ) {k : ℕ}
    (θ : Params A dIn dOut) {n : ℕ} (X : Fin n → Matrix T dIn ℝ)
    (h : ∀ᵐ θ' ∂(Measure.addHaar : Measure (Params A dIn dOut)),
      funDim A 0 θ' + k ≤ Module.finrank ℝ (Params A dIn dOut)) :
    jacobianRank A 0 X θ + k ≤ Module.finrank ℝ (Params A dIn dOut) := by
  -- a parameter `θ'` with `rank J_X(θ) ≤ fd(θ')` and `fd(θ') + k ≤ P`
  obtain ⟨θ', h1, h2⟩ :=
    ((ae_jacobianRank_le_funDim A 0 hf hχ Measure.addHaar X θ).and h).exists
  omega

/-- **The bound at every parameter, on every batch, for a skipless network of attention blocks and
MLP blocks, without normalization:** for a real-analytic activation, `d_in, d_out ≥ d`, `L ≥ 1`
and heads of width `d_h ≤ d`, the Jacobian of the outputs on a batch has rank at most `P − 2 d² −
2 ∑_ℓ H_ℓ d_{h,ℓ}²` at every parameter. -/
theorem jacobianRank_add_le_skipless_ends_attentionMlp
    (hσa : AnalyticOnNhd ℝ σ Set.univ) (hL : 0 < L)
    (hdIn : Fintype.card d ≤ Fintype.card dIn) (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d)
    (θ : Params
      (Arch.attentionMlp (T := T) (d := d) sees σ id H dh hid) dIn dOut)
    {n : ℕ} (X : Fin n → Matrix T dIn ℝ) :
    jacobianRank (Arch.attentionMlp sees σ id H dh hid) 0 X θ
        + (2 * Fintype.card d ^ 2
          + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
      ≤ Module.finrank ℝ (Params
          (Arch.attentionMlp (T := T) (d := d) sees σ id H dh hid) dIn dOut) := by
  sorry

/-- **The bound at every parameter, on every batch, for a skipless network of attention blocks and
MLP blocks, under pre-RMSNorm with `ε > 0`:** for a real-analytic activation, `d_in, d_out ≥ d`,
`L ≥ 1` and heads of width `d_h ≤ d`, the Jacobian of the outputs on a batch has rank at most `P −
d (d − 1) − 2 ∑_ℓ H_ℓ d_{h,ℓ}²` at every parameter. -/
theorem jacobianRank_add_le_skipless_ends_attentionMlp_rmsNorm (hε : 0 < ε)
    (hσa : AnalyticOnNhd ℝ σ Set.univ) (hL : 0 < L)
    (hdIn : Fintype.card d ≤ Fintype.card dIn) (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d)
    (θ : Params
      (Arch.attentionMlp (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut)
    {n : ℕ} (X : Fin n → Matrix T dIn ℝ) :
    jacobianRank (Arch.attentionMlp sees σ (rmsNorm ε) H dh hid) 0 X θ
        + (Fintype.card d * (Fintype.card d - 1)
          + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
      ≤ Module.finrank ℝ (Params
          (Arch.attentionMlp (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut) := by
  sorry

/-- **The bound at every parameter, on every batch, for a skipless network of attention blocks and
gated blocks, without normalization:** for a real-analytic gate, `d_in, d_out ≥ d` `≥ 1`, `L ≥ 1`
and heads of width `d_h ≤ d`, the Jacobian of the outputs on a batch has rank at most `P − 2 d² −
2 ∑_ℓ H_ℓ d_{h,ℓ}² − ∑_ℓ d_hidden,ℓ` at every parameter. -/
theorem jacobianRank_add_le_skipless_ends_attentionGated [Nonempty d]
    (hσa : AnalyticOnNhd ℝ σ Set.univ) (hL : 0 < L)
    (hdIn : Fintype.card d ≤ Fintype.card dIn) (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d)
    (θ : Params
      (Arch.attentionGated (T := T) (d := d) sees σ id H dh hid) dIn dOut)
    {n : ℕ} (X : Fin n → Matrix T dIn ℝ) :
    jacobianRank (Arch.attentionGated sees σ id H dh hid) 0 X θ
        + (2 * Fintype.card d ^ 2
          + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
            + ∑ ℓ, Fintype.card (hid ℓ)))
      ≤ Module.finrank ℝ (Params
          (Arch.attentionGated (T := T) (d := d) sees σ id H dh hid) dIn dOut) := by
  sorry

/-- **The bound at every parameter, on every batch, for a skipless network of attention blocks and
gated blocks, under pre-RMSNorm with `ε > 0`:** for a real-analytic gate, `d_in, d_out ≥ d` `≥ 1`,
`L ≥ 1` and heads of width `d_h ≤ d`, the Jacobian of the outputs on a batch has rank at most `P −
d (d − 1) − 2 ∑_ℓ H_ℓ d_{h,ℓ}² − ∑_ℓ d_hidden,ℓ` at every parameter. -/
theorem jacobianRank_add_le_skipless_ends_attentionGated_rmsNorm [Nonempty d] (hε : 0 < ε)
    (hσa : AnalyticOnNhd ℝ σ Set.univ) (hL : 0 < L)
    (hdIn : Fintype.card d ≤ Fintype.card dIn) (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d)
    (θ : Params
      (Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut)
    {n : ℕ} (X : Fin n → Matrix T dIn ℝ) :
    jacobianRank (Arch.attentionGated sees σ (rmsNorm ε) H dh hid) 0 X θ
        + (Fintype.card d * (Fintype.card d - 1)
          + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
            + ∑ ℓ, Fintype.card (hid ℓ)))
      ≤ Module.finrank ℝ (Params
          (Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut) := by
  sorry

end Skips
