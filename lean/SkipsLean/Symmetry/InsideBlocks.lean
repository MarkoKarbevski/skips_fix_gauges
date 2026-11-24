import SkipsLean.Dimension.UpperBoundRMSNorm
import SkipsLean.Residual.UpperBoundSymmetries

/-!
# Symmetries inside the blocks, for any kind of block, and the upper bounds they give

Papers. Skips paper, Section 4.1: "the symmetries inside the blocks, which change the read and
the write of one block and leave the map of that block unchanged: the rescaling of a hidden unit
of a ReLU or ReLU² block, the rescaling of the value of a hidden unit of a gated block, and the
changes of basis inside an attention head […]. Let `s` be the total dimension of the symmetries
inside the blocks, summed over the blocks […]. They preserve the function with skips and without
them, so `s` is the same number for both networks." Theorem 4.2 (Upper bounds): "at generic
parameters, the functional dimension is at most `P − (L + 1) dim G − s` without skips and at most
`P − dim G − s` with identity skips." Dimension paper: Theorem 4.3 and Lemma B.1.

The library has these bounds kind by kind (`Dimension/Rescaling.lean`, `RescalingMlp.lean`,
`RescalingGate.lean`, `UpperBoundAttention.lean`, `Residual/UpperBoundSymmetries.lean`). Here they
are stated once, for any architecture, so that they also serve networks with two kinds of block
(`Network/Sum.lean`, `Symmetry/InsideBlocksSum.lean`):

* `InsideBlocks A θ η`: `η` is the velocity at `θ` of a curve of parameters that keeps `E`, `D`
  and the map `n ↦ f_ℓ(n W_read^ℓ) W_write^ℓ` of every block.
* `InsideBlocks.mem_flat`: such a direction is flat, for every stream (with or without skips)
  and every `χ`; its `E` and `D` components are `0`.
* The bounds for a space `V` of directions spanned by such directions: without skips
  `fd ≤ P − (L + 1) dim G − dim V`, if `E` and the writes have rank `d` and a direction of `V`
  whose read of a block is `0` has the write of that block `0` (the directions of Lemma B.1);
  with identity skips `fd ≤ P − dim G − dim V`, if `E` has rank `d`. Without normalization
  `dim G = d²`; under pre-RMSNorm (any `ε`) the changes of basis are the antisymmetric
  directions, `dim G = d(d−1)/2`.
-/

namespace Skips

open Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]

/-- **A direction of a symmetry inside the blocks:** `η` is the velocity at `τ = 0` of a curve
`γ` of parameters through `θ` along which, near `τ = 0`, the embedding and the readout stay those
of `θ` and every block keeps its map `n ↦ f_ℓ(n W_read^ℓ) W_write^ℓ`. -/
def InsideBlocks (A : Arch T d L) (θ η : Params A dIn dOut) : Prop :=
  ∃ γ : ℝ → Params A dIn dOut, γ 0 = θ ∧ HasDerivAt γ η 0 ∧
    ∀ᶠ τ in 𝓝 (0 : ℝ), (γ τ).E = θ.E ∧ (γ τ).D = θ.D ∧
      ∀ ℓ (n : Matrix T d ℝ),
        A.f ℓ (n * (γ τ).read ℓ) * (γ τ).write ℓ = A.f ℓ (n * θ.read ℓ) * θ.write ℓ

variable {A : Arch T d L} {θ η : Params A dIn dOut}

omit [Fintype T] [DecidableEq d] [Fintype dOut] in
/-- Helper (the private `eval_eq_of_blocks_ath` of `Symmetry/AttentionHeads.lean`): two
parameters with the same `E`, the same `D` and the same output of every block on every hidden
state compute the same function (induction along the hidden states). -/
private theorem eval_eq_of_blocks_ibl (θ₁ θ₂ : Params A dIn dOut)
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

omit [DecidableEq d] in
/-- **A symmetry inside the blocks preserves the function with skips and without them:** its
direction is flat for every stream and every `χ`. -/
theorem InsideBlocks.mem_flat (h : InsideBlocks A θ η) (S : Fin L → Matrix d d ℝ) :
    η ∈ flat A S θ := by
  obtain ⟨γ, h0, hd, hev⟩ := h
  -- along the curve the embedding, the readout and every block are kept, hence the function
  refine mem_flat_of_hasDerivAt' θ γ η hd h0 ?_
  filter_upwards [hev] with τ hτ x
  exact eval_eq_of_blocks_ibl θ (γ τ) hτ.1 hτ.2.1 hτ.2.2 S x

omit [Fintype T] [DecidableEq d] in
/-- A direction of a symmetry inside the blocks does not move the embedding. -/
theorem InsideBlocks.E_eq_zero (h : InsideBlocks A θ η) : η.E = 0 := by
  obtain ⟨γ, -, hd, hev⟩ := h
  -- `θ' ↦ θ'.E` is linear, hence continuous: `τ ↦ (γ τ).E` has derivative `η.E` at `0`
  let l : Params A dIn dOut →L[ℝ] Matrix dIn d ℝ := LinearMap.toContinuousLinearMap
    { toFun := fun θ' => θ'.E, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have h1 : HasDerivAt (fun τ => (γ τ).E) η.E 0 := l.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd
  -- it is constant near `0`, so its derivative there is `0`
  have h2 : HasDerivAt (fun τ => (γ τ).E) 0 0 :=
    (hasDerivAt_const (0 : ℝ) θ.E).congr_of_eventuallyEq (hev.mono fun _ hτ => hτ.1)
  exact h1.unique h2

omit [Fintype T] [DecidableEq d] in
/-- A direction of a symmetry inside the blocks does not move the readout. -/
theorem InsideBlocks.D_eq_zero (h : InsideBlocks A θ η) : η.D = 0 := by
  obtain ⟨γ, -, hd, hev⟩ := h
  -- `θ' ↦ θ'.D` is linear, hence continuous: `τ ↦ (γ τ).D` has derivative `η.D` at `0`
  let l : Params A dIn dOut →L[ℝ] Matrix d dOut ℝ := LinearMap.toContinuousLinearMap
    { toFun := fun θ' => θ'.D, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have h1 : HasDerivAt (fun τ => (γ τ).D) η.D 0 := l.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd
  -- it is constant near `0`, so its derivative there is `0`
  have h2 : HasDerivAt (fun τ => (γ τ).D) 0 0 :=
    (hasDerivAt_const (0 : ℝ) θ.D).congr_of_eventuallyEq (hev.mono fun _ hτ => hτ.2.1)
  exact h1.unique h2

variable (θ)

omit [DecidableEq d] in
/-- Helper: the directions spanned by directions of symmetries inside the blocks are flat, for
every stream (the flat directions form a subspace). -/
private theorem span_le_flat_ibl (S : Fin L → Matrix d d ℝ) :
    Submodule.span ℝ {η | InsideBlocks A θ η} ≤ flat A S θ :=
  Submodule.span_le.2 fun _ hη => InsideBlocks.mem_flat hη S

omit [Fintype T] [DecidableEq d] in
/-- Helper: the directions spanned by directions of symmetries inside the blocks have `E`
component `0` (a linear condition). -/
private theorem E_eq_zero_of_mem_span_ibl {v : Params A dIn dOut}
    (hv : v ∈ Submodule.span ℝ {η | InsideBlocks A θ η}) : v.E = 0 := by
  induction hv using Submodule.span_induction with
  | mem x hx => exact InsideBlocks.E_eq_zero hx
  | zero => rfl
  | add x y _ _ hx hy => rw [Params.add_E, hx, hy, add_zero]
  | smul a x _ hx => rw [Params.smul_E, hx, smul_zero]

/-- Helper (the private `cancel_left_of_rank_ubs` of `Residual/UpperBoundSymmetries.lean`): a
matrix `M` of rank equal to its number of columns cancels on the left, `M X = M Y → X = Y` (its
kernel is `0` by rank–nullity). -/
private theorem cancel_left_of_rank_ibl {m n k : Type*} [Fintype n] (M : Matrix m n ℝ)
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

omit [Fintype T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (**Lemma B.1** for the changes of basis together with a space `V` of directions with
`E` component `0`, in which a direction whose read of block `ℓ` is `0` has the write of block `ℓ`
`0`): if `E` and the writes have rank `d`, `cobDir θ X + v` determines `X` and `v ∈ V`. The `E`
component gives `X_0`; if `X_ℓ` is known, the read of block `ℓ` gives the read of `v`, hence that
of `v − v' ∈ V` is `0`, so is its write, and the write of block `ℓ` gives `X_{ℓ+1}`. -/
private theorem cobDir_add_inj_ibl (V : Submodule ℝ (Params A dIn dOut))
    (hVE : ∀ v ∈ V, v.E = 0) (hrw : ∀ η ∈ V, ∀ ℓ, η.read ℓ = 0 → η.write ℓ = 0)
    (hE : θ.E.rank = Fintype.card d) (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d)
    {X Y : Fin (L + 1) → Matrix d d ℝ} {v v' : Params A dIn dOut} (hv : v ∈ V) (hv' : v' ∈ V)
    (h : cobDir θ X + v = cobDir θ Y + v') : X = Y ∧ v = v' := by
  -- the difference `v − v'` lies in `V`
  have hu : v - v' ∈ V := V.sub_mem hv hv'
  have hXY : X = Y := by
    funext k
    induction k using Fin.induction with
    | zero =>
      -- the embedding: `E X_0 = E Y_0`, since `v` and `v'` have `E` component `0`
      have h0 : θ.E * X 0 + v.E = θ.E * Y 0 + v'.E := congrArg Params.E h
      rw [hVE v hv, hVE v' hv', add_zero, add_zero] at h0
      exact cancel_left_of_rank_ibl θ.E hE h0
    | succ ℓ ih =>
      -- the read of block `ℓ`: with `X_ℓ = Y_ℓ`, `v` and `v'` have the same read
      have hr : -(X ℓ.castSucc * θ.read ℓ) + v.read ℓ = -(Y ℓ.castSucc * θ.read ℓ) + v'.read ℓ :=
        congrArg (fun η => η.read ℓ) h
      rw [ih] at hr
      have hr' : (v - v').read ℓ = 0 := by
        show v.read ℓ - v'.read ℓ = 0
        rw [add_left_cancel hr, sub_self]
      -- hence the same write, by the hypothesis on `V`
      have hw' : v.write ℓ = v'.write ℓ := by
        have h1 : v.write ℓ - v'.write ℓ = 0 := hrw _ hu ℓ hr'
        exact sub_eq_zero.1 h1
      -- the write of block `ℓ`: `W_write X_{ℓ+1} = W_write Y_{ℓ+1}`, and `W_write` has rank `d`
      have hwr : θ.write ℓ * X ℓ.succ + v.write ℓ = θ.write ℓ * Y ℓ.succ + v'.write ℓ :=
        congrArg (fun η => η.write ℓ) h
      rw [hw'] at hwr
      exact cancel_left_of_rank_ibl (θ.write ℓ) (hw ℓ) (add_right_cancel hwr)
  subst hXY
  exact ⟨rfl, add_left_cancel h⟩

/-- **Theorem 4.3 of the dimension paper for any symmetries inside the blocks, without
normalization, under the conditions of Lemma B.1:** let `V` be a space of directions spanned by
directions of symmetries inside the blocks, in which a direction whose read of block `ℓ` is `0`
has the write of block `ℓ` `0`. If `E` and the writes have rank `d`,
`fd ≤ P − (L + 1) d² − dim V`. -/
theorem funDim_add_le_skipless_of_insideBlocks (hA : A.χ = id)
    (V : Submodule ℝ (Params A dIn dOut))
    (hV : V ≤ Submodule.span ℝ {η | InsideBlocks A θ η})
    (hrw : ∀ η ∈ V, ∀ ℓ, η.read ℓ = 0 → η.write ℓ = 0)
    (hE : θ.E.rank = Fintype.card d) (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d) :
    funDim A 0 θ + ((L + 1) * Fintype.card d ^ 2 + Module.finrank ℝ V)
      ≤ Module.finrank ℝ (Params A dIn dOut) := by
  -- the linear map `(X, v) ↦ cobDir θ X + v`
  let Φ := (cobDirLin θ).coprod V.subtype
  -- its directions are flat: the changes of basis are, and so are the directions of `V`
  have hflat : LinearMap.range Φ ≤ flat A 0 θ := by
    rintro _ ⟨p, rfl⟩
    rw [LinearMap.coprod_apply]
    exact Submodule.add_mem _ (cobDir_mem_flat_skipless' θ hA p.1)
      (span_le_flat_ibl θ 0 (hV p.2.2))
  -- it is injective (Lemma B.1)
  have hinj : Function.Injective Φ := by
    intro p q hpq
    have h' : cobDir θ p.1 + (p.2 : Params A dIn dOut) = cobDir θ q.1 + q.2 := hpq
    obtain ⟨h1, h2⟩ := cobDir_add_inj_ibl θ V
      (fun v hv => E_eq_zero_of_mem_span_ibl θ (hV hv)) hrw hE hw p.2.2 q.2.2 h'
    exact Prod.ext h1 (Subtype.ext h2)
  -- the domain has dimension `(L + 1) d² + dim V`
  have h := funDim_add_finrank_le_of_le_flat' θ _ hflat
  rwa [LinearMap.finrank_range_of_inj hinj, Module.finrank_prod, finrank_cobDomain] at h

/-- **The same under pre-RMSNorm** (any `ε`):
`fd ≤ P − (L + 1) d(d−1)/2 − dim V`. -/
theorem funDim_add_le_skipless_of_insideBlocks_rmsNorm (ε : ℝ) (hA : A.χ = rmsNorm ε)
    (V : Submodule ℝ (Params A dIn dOut))
    (hV : V ≤ Submodule.span ℝ {η | InsideBlocks A θ η})
    (hrw : ∀ η ∈ V, ∀ ℓ, η.read ℓ = 0 → η.write ℓ = 0)
    (hE : θ.E.rank = Fintype.card d) (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d) :
    funDim A 0 θ
        + ((L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2) + Module.finrank ℝ V)
      ≤ Module.finrank ℝ (Params A dIn dOut) := by
  -- the linear map `(X, v) ↦ cobDir θ X + v`, with antisymmetric `X_ℓ`
  let Φ : (Fin (L + 1) → antisymmetric d) × V →ₗ[ℝ] Params A dIn dOut :=
    ((cobDirLin θ).comp (LinearMap.compLeft (antisymmetric d).subtype (Fin (L + 1)))).coprod
      V.subtype
  -- its directions are flat: the orthogonal changes of basis are, and so are those of `V`
  have hflat : LinearMap.range Φ ≤ flat A 0 θ := by
    rintro _ ⟨p, rfl⟩
    rw [LinearMap.coprod_apply]
    exact Submodule.add_mem _
      (cobDir_mem_flat_skipless_rmsNorm' θ ε hA (fun ℓ => (p.1 ℓ : Matrix d d ℝ))
        fun ℓ => (p.1 ℓ).2)
      (span_le_flat_ibl θ 0 (hV p.2.2))
  -- it is injective (Lemma B.1)
  have hinj : Function.Injective Φ := by
    intro p q hpq
    have h' : cobDir θ (fun ℓ => (p.1 ℓ : Matrix d d ℝ)) + (p.2 : Params A dIn dOut)
        = cobDir θ (fun ℓ => (q.1 ℓ : Matrix d d ℝ)) + q.2 := hpq
    obtain ⟨h1, h2⟩ := cobDir_add_inj_ibl θ V
      (fun v hv => E_eq_zero_of_mem_span_ibl θ (hV hv)) hrw hE hw p.2.2 q.2.2 h'
    exact Prod.ext (funext fun ℓ => Subtype.ext (congrFun h1 ℓ)) (Subtype.ext h2)
  -- the domain has dimension `(L + 1) d(d−1)/2 + dim V`
  have hdim : Module.finrank ℝ ((Fin (L + 1) → antisymmetric d) × V) =
      (L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2) + Module.finrank ℝ V := by
    rw [Module.finrank_prod,
      Module.finrank_pi_fintype (R := ℝ) (ι := Fin (L + 1)) (M := fun _ => antisymmetric d),
      finrank_antisymmetric, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have h := funDim_add_finrank_le_of_le_flat' θ _ hflat
  rwa [LinearMap.finrank_range_of_inj hinj, hdim] at h

/-- Helper (the private `funDim_add_le_of_cobConst_add_uba` of
`Dimension/UpperBoundAttention.lean`): the bound from one change of basis and the symmetries
inside the blocks. Let `ι : W → Matrix d d ℝ` be linear and injective, and `ρ : V → Params` linear
and injective with `E` component `0`. If the directions `cobDir θ (fun _ => ι w)` and `ρ v` are
flat and `E` has rank `d`, then `fd ≤ P - dim W - dim V`. -/
private theorem funDim_add_le_of_cobConst_add_ibl
    {W V : Type*} [AddCommGroup W] [Module ℝ W]
    [FiniteDimensional ℝ W] [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (ι : W →ₗ[ℝ] Matrix d d ℝ) (hι : Function.Injective ι)
    (ρ : V →ₗ[ℝ] Params A dIn dOut) (hρ : Function.Injective ρ) (hρE : ∀ v, (ρ v).E = 0)
    (hE : θ.E.rank = Fintype.card d)
    (hcob : ∀ w, cobDir θ (fun _ => ι w) ∈ flat A 1 θ) (hflat : ∀ v, ρ v ∈ flat A 1 θ) :
    funDim A 1 θ + (Module.finrank ℝ W + Module.finrank ℝ V)
      ≤ Module.finrank ℝ (Params A dIn dOut) := by
  -- the linear map `(w, v) ↦ cobDir θ (fun _ => ι w) + ρ v`
  let Φ : W × V →ₗ[ℝ] Params A dIn dOut :=
    ((cobDirLin θ).comp (LinearMap.pi fun _ : Fin (L + 1) => ι)).coprod ρ
  have hΦ : ∀ w v, Φ (w, v) = cobDir θ (fun _ => ι w) + ρ v := fun _ _ => rfl
  -- its directions are flat, since both summands are
  have hV : LinearMap.range Φ ≤ flat A 1 θ := by
    rintro _ ⟨⟨w, v⟩, rfl⟩
    rw [hΦ]
    exact Submodule.add_mem _ (hcob w) (hflat v)
  -- it is injective: the `E` component `E ι(w)` gives `w`, since `E` has rank `d`; then `ρ v`
  -- gives `v`
  have hinj : Function.Injective Φ := by
    rintro ⟨w, v⟩ ⟨w', v'⟩ h
    rw [hΦ, hΦ] at h
    have h0 : θ.E * ι w = θ.E * ι w' := by
      have hE0 := congrArg Params.E h
      rw [Params.add_E, Params.add_E, hρE, hρE, add_zero, add_zero] at hE0
      exact hE0
    obtain rfl : w = w' := hι (cancel_left_of_rank_ibl θ.E hE h0)
    exact Prod.ext rfl (hρ (add_left_cancel h))
  have h := funDim_add_finrank_le_of_le_flat' θ _ hV
  rwa [LinearMap.finrank_range_of_inj hinj, Module.finrank_prod] at h

/-- **Theorem 4.2 of the skips paper with identity skips, for any symmetries inside the blocks,
without normalization:** if `E` has rank `d`, `fd ≤ P − d² − dim V`. -/
theorem funDim_add_le_residual_of_insideBlocks (hA : A.χ = id)
    (V : Submodule ℝ (Params A dIn dOut))
    (hV : V ≤ Submodule.span ℝ {η | InsideBlocks A θ η})
    (hE : θ.E.rank = Fintype.card d) :
    funDim A 1 θ + (Fintype.card d ^ 2 + Module.finrank ℝ V)
      ≤ Module.finrank ℝ (Params A dIn dOut) := by
  -- the flat directions `cobDir θ (fun _ => X) + v`, of dimension `d² + dim V`
  have h := funDim_add_le_of_cobConst_add_ibl θ LinearMap.id Function.injective_id
    V.subtype V.injective_subtype (fun v => E_eq_zero_of_mem_span_ibl θ (hV v.2)) hE
    (fun X => cobDir_const_mem_flat_residual' θ hA X) (fun v => span_le_flat_ibl θ 1 (hV v.2))
  rwa [Module.finrank_matrix, Module.finrank_self, mul_one, ← sq] at h

/-- **The same under pre-RMSNorm** (any `ε`): `fd ≤ P − d(d−1)/2 − dim V`. -/
theorem funDim_add_le_residual_of_insideBlocks_rmsNorm (ε : ℝ) (hA : A.χ = rmsNorm ε)
    (V : Submodule ℝ (Params A dIn dOut))
    (hV : V ≤ Submodule.span ℝ {η | InsideBlocks A θ η})
    (hE : θ.E.rank = Fintype.card d) :
    funDim A 1 θ + (Fintype.card d * (Fintype.card d - 1) / 2 + Module.finrank ℝ V)
      ≤ Module.finrank ℝ (Params A dIn dOut) := by
  -- the same directions, with `X` antisymmetric
  have h := funDim_add_le_of_cobConst_add_ibl θ (antisymmetric d).subtype
    (antisymmetric d).injective_subtype V.subtype V.injective_subtype
    (fun v => E_eq_zero_of_mem_span_ibl θ (hV v.2)) hE
    (fun X => cobDir_const_mem_flat_residual_rmsNorm' θ ε hA (X : Matrix d d ℝ) X.2)
    (fun v => span_le_flat_ibl θ 1 (hV v.2))
  rwa [finrank_antisymmetric] at h

end Skips
