import SkipsLean.Symmetry.InsideBlocksSum
import SkipsLean.Residual.UpperBoundRescaleRMSNormZero

/-!
# The upper bounds for any symmetries inside the blocks, under pre-RMSNorm with `ε = 0`

Paper (skips paper), Theorem 4.2 (Upper bounds): "Let `G` be the group of changes of basis of one
hidden state, and `s` the dimension of the symmetries inside the blocks, the same with and without
skips. With or without pre-RMSNorm, at generic parameters, the functional dimension is at most
`P − (L + 1) dim G − s` without skips and at most `P − dim G − s` with identity skips." It is a
special case of Theorem A.17 (ii). Appendix A: "`G` is `GL(d_model)` without normalization,
`O(d_model)` under RMSNorm with `ε > 0`, and `CO(d_model)`, the positive multiples of orthogonal
matrices, under RMSNorm with `ε = 0`." So for `ε = 0`, `dim G = d(d−1)/2 + 1`.

`Symmetry/InsideBlocks.lean` and `Symmetry/InsideBlocksSum.lean` have these bounds for any space
`V` of directions of symmetries inside the blocks, without normalization and under pre-RMSNorm for
any `ε` with the orthogonal changes of basis only (`d(d−1)/2` for each). Here their twins for
`ε = 0`, with the scaling of each hidden state as one more flat direction
(`scaleDir`, `Dimension/UpperBoundRMSNormZero.lean`): `(L + 1) (d(d−1)/2 + 1)` without skips and
`d(d−1)/2 + 1` with identity skips, for one architecture and for the sum of two.

The functional dimension is Lean's `funDim` (all inputs; a zero row is normalized to `0`).
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]

section One

variable {A : Arch T d L} (θ : Params A dIn dOut)

omit [DecidableEq d] in
/-- Helper (the private `span_le_flat_ibl` of `Symmetry/InsideBlocks.lean`): the directions
spanned by directions of symmetries inside the blocks are flat, for every stream. -/
private theorem span_le_flat_ibz (S : Fin L → Matrix d d ℝ) :
    Submodule.span ℝ {η | InsideBlocks A θ η} ≤ flat A S θ :=
  Submodule.span_le.2 fun _ hη => InsideBlocks.mem_flat hη S

omit [Fintype T] [DecidableEq d] in
/-- Helper (the private `E_eq_zero_of_mem_span_ibl` of `Symmetry/InsideBlocks.lean`): the
directions spanned by directions of symmetries inside the blocks have `E` component `0`. -/
private theorem E_eq_zero_of_mem_span_ibz {v : Params A dIn dOut}
    (hv : v ∈ Submodule.span ℝ {η | InsideBlocks A θ η}) : v.E = 0 := by
  induction hv using Submodule.span_induction with
  | mem x hx => exact InsideBlocks.E_eq_zero hx
  | zero => rfl
  | add x y _ _ hx hy => rw [Params.add_E, hx, hy, add_zero]
  | smul a x _ hx => rw [Params.smul_E, hx, smul_zero]

omit [Fintype T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (the private `cancel_left_of_rank_rz` of `Dimension/UpperBoundRMSNormZero.lean`): a
matrix `M` of rank equal to its number of columns cancels on the left, `M X = M Y → X = Y` (its
kernel is `0` by rank–nullity). -/
private theorem cancel_left_of_rank_ibz {m n k : Type*} [Fintype n] (M : Matrix m n ℝ)
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

omit [Fintype T] [Fintype d] [Fintype dIn] [Fintype dOut] in
/-- Helper (the private `antisymm_add_smul_one_inj_rz` of `Dimension/UpperBoundRMSNormZero.lean`):
an antisymmetric matrix plus a scalar matrix determines both: the diagonal of an antisymmetric
matrix vanishes, so a diagonal entry gives the scalar. -/
private theorem antisymm_add_smul_one_inj_ibz [Nonempty d] {X X' : Matrix d d ℝ} (hX : Xᵀ = -X)
    (hX' : X'ᵀ = -X') {b b' : ℝ} (h : X + b • (1 : Matrix d d ℝ) = X' + b' • 1) :
    X = X' ∧ b = b' := by
  obtain ⟨k⟩ := ‹Nonempty d›
  -- the diagonal entries of an antisymmetric matrix vanish
  have hd : ∀ {Z : Matrix d d ℝ}, Zᵀ = -Z → Z k k = 0 := fun {Z} hZ => by
    have := congrFun (congrFun hZ k) k
    rw [transpose_apply, Matrix.neg_apply] at this
    linarith
  -- the entry `(k, k)` gives `b = b'`, and then `X = X'`
  have hk := congrFun (congrFun h k) k
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one,
    hd hX, hd hX', zero_add] at hk
  subst hk
  exact ⟨add_right_cancel h, rfl⟩

omit [Fintype T] [Fintype dIn] [Fintype dOut] in
/-- Helper (the private `mul_add_smul_inj_rz` of `Dimension/UpperBoundRMSNormZero.lean`): if `M`
has rank `d`, then `M X + b M` with antisymmetric `X` determines `X` and `b`: it is
`M (X + b 1)`. -/
private theorem mul_add_smul_inj_ibz [Nonempty d] {m : Type*} (M : Matrix m d ℝ)
    (hM : M.rank = Fintype.card d) {X X' : Matrix d d ℝ} (hX : Xᵀ = -X) (hX' : X'ᵀ = -X')
    {b b' : ℝ} (h : M * X + b • M = M * X' + b' • M) : X = X' ∧ b = b' := by
  have h' : M * (X + b • (1 : Matrix d d ℝ)) = M * (X' + b' • 1) := by
    rw [Matrix.mul_add, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_one]
    exact h
  exact antisymm_add_smul_one_inj_ibz hX hX' (cancel_left_of_rank_ibz M hM h')

/-- Helper (the private `scaleDirLin_rz` of `Dimension/UpperBoundRMSNormZero.lean`):
`β ↦ scaleDir θ β` is linear. -/
private noncomputable def scaleDirLin_ibz : (Fin (L + 1) → ℝ) →ₗ[ℝ] Params A dIn dOut where
  toFun := scaleDir θ
  map_add' β β' := by
    refine Params.ext' ?_ (fun ℓ => ?_) (fun ℓ => ?_) ?_ <;>
      simp only [scaleDir, Params.add_E, Params.add_read, Params.add_write, Params.add_D,
        Pi.add_apply, add_smul, add_zero]
  map_smul' c β := by
    refine Params.ext' ?_ (fun ℓ => ?_) (fun ℓ => ?_) ?_ <;>
      simp only [scaleDir, Params.smul_E, Params.smul_read, Params.smul_write, Params.smul_D,
        Pi.smul_apply, smul_eq_mul, mul_smul, smul_zero, RingHom.id_apply]

omit [Fintype T] [Fintype dIn] [Fintype dOut] in
/-- Helper (**Lemma A.18** for `ε = 0`: the changes of basis in `CO(d)` together with a space `V`
of directions with `E` component `0`, in which a direction whose read of block `ℓ` is `0` has the
write of block `ℓ` `0`): if `E` and the writes have rank `d ≥ 1`, `cobDir θ Y + scaleDir θ β + v`
with antisymmetric `Y_ℓ` determines `Y`, `β` and `v ∈ V`. The `E` component gives `Y_0, β_0`; if
`Y_ℓ` is known, the read of block `ℓ` (which the scales leave alone) gives the read of `v`, hence
that of `v − v' ∈ V` is `0`, so is its write, and the write of block `ℓ` gives
`Y_{ℓ+1}, β_{ℓ+1}`. -/
private theorem cobDir_add_scaleDir_add_inj_ibz [Nonempty d]
    (V : Submodule ℝ (Params A dIn dOut))
    (hVE : ∀ v ∈ V, v.E = 0) (hrw : ∀ η ∈ V, ∀ ℓ, η.read ℓ = 0 → η.write ℓ = 0)
    (hE : θ.E.rank = Fintype.card d) (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d)
    {Y Y' : Fin (L + 1) → Matrix d d ℝ} (hY : ∀ ℓ, (Y ℓ)ᵀ = -Y ℓ) (hY' : ∀ ℓ, (Y' ℓ)ᵀ = -Y' ℓ)
    {β β' : Fin (L + 1) → ℝ} {v v' : Params A dIn dOut} (hv : v ∈ V) (hv' : v' ∈ V)
    (h : cobDir θ Y + scaleDir θ β + v = cobDir θ Y' + scaleDir θ β' + v') :
    Y = Y' ∧ β = β' ∧ v = v' := by
  -- the difference `v − v'` lies in `V`
  have hu : v - v' ∈ V := V.sub_mem hv hv'
  have hYβ : ∀ k : Fin (L + 1), Y k = Y' k ∧ β k = β' k := by
    intro k
    induction k using Fin.induction with
    | zero =>
      -- the embedding: `E Y_0 + β_0 E = E Y'_0 + β'_0 E`, since `v`, `v'` have `E` component `0`
      have h0 : θ.E * Y 0 + β 0 • θ.E + v.E = θ.E * Y' 0 + β' 0 • θ.E + v'.E :=
        congrArg Params.E h
      rw [hVE v hv, hVE v' hv', add_zero, add_zero] at h0
      exact mul_add_smul_inj_ibz θ.E hE (hY 0) (hY' 0) h0
    | succ ℓ ih =>
      -- the read of block `ℓ`: with `Y_ℓ = Y'_ℓ`, `v` and `v'` have the same read
      have hr : -(Y ℓ.castSucc * θ.read ℓ) + 0 + v.read ℓ
          = -(Y' ℓ.castSucc * θ.read ℓ) + 0 + v'.read ℓ :=
        congrArg (fun η => η.read ℓ) h
      rw [ih.1, add_right_inj] at hr
      have hr' : (v - v').read ℓ = 0 := by
        show v.read ℓ - v'.read ℓ = 0
        rw [hr, sub_self]
      -- hence the same write, by the hypothesis on `V`
      have hw' : v.write ℓ = v'.write ℓ := by
        have h1 : v.write ℓ - v'.write ℓ = 0 := hrw _ hu ℓ hr'
        exact sub_eq_zero.1 h1
      -- the write of block `ℓ`: `W Y_{ℓ+1} + β_{ℓ+1} W`, and `W` has rank `d`
      have hwr : θ.write ℓ * Y ℓ.succ + β ℓ.succ • θ.write ℓ + v.write ℓ
          = θ.write ℓ * Y' ℓ.succ + β' ℓ.succ • θ.write ℓ + v'.write ℓ :=
        congrArg (fun η => η.write ℓ) h
      rw [hw', add_left_inj] at hwr
      exact mul_add_smul_inj_ibz (θ.write ℓ) (hw ℓ) (hY _) (hY' _) hwr
  -- with `Y = Y'` and `β = β'`, also `v = v'`
  have hY'' : Y = Y' := funext fun k => (hYβ k).1
  have hβ : β = β' := funext fun k => (hYβ k).2
  subst hY'' hβ
  exact ⟨rfl, rfl, add_left_cancel h⟩

/-- **Theorem 4.2 of the skips paper without skips, for any symmetries inside the blocks, under
pre-RMSNorm with `ε = 0`, under the conditions of Lemma A.18:** let `V` be a space of directions
spanned by directions of symmetries inside the blocks, in which a direction whose read of block
`ℓ` is `0` has the write of block `ℓ` `0`. If `E` and the writes have rank `d ≥ 1`,
`fd ≤ P − (L + 1) (d(d−1)/2 + 1) − dim V`. -/
theorem funDim_add_le_skipless_of_insideBlocks_rmsNorm_zero [Nonempty d] (hA : A.χ = rmsNorm 0)
    (V : Submodule ℝ (Params A dIn dOut))
    (hV : V ≤ Submodule.span ℝ {η | InsideBlocks A θ η})
    (hrw : ∀ η ∈ V, ∀ ℓ, η.read ℓ = 0 → η.write ℓ = 0)
    (hE : θ.E.rank = Fintype.card d) (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d) :
    funDim A 0 θ
        + ((L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2 + 1) + Module.finrank ℝ V)
      ≤ Module.finrank ℝ (Params A dIn dOut) := by
  -- the linear map `((Y, β), v) ↦ cobDir θ Y + scaleDir θ β + v`, with antisymmetric `Y_ℓ`
  let Φ : ((Fin (L + 1) → antisymmetric d) × (Fin (L + 1) → ℝ)) × V →ₗ[ℝ]
      Params A dIn dOut :=
    (((cobDirLin θ).comp (LinearMap.compLeft (antisymmetric d).subtype (Fin (L + 1)))).coprod
      (scaleDirLin_ibz θ)).coprod V.subtype
  -- its directions are flat: the changes of basis in `CO(d)` are, and so are those of `V`
  have hflat : LinearMap.range Φ ≤ flat A 0 θ := by
    rintro _ ⟨p, rfl⟩
    rw [LinearMap.coprod_apply, LinearMap.coprod_apply]
    exact Submodule.add_mem _ (Submodule.add_mem _
      (cobDir_mem_flat_skipless_rmsNorm' θ 0 hA (fun ℓ => (p.1.1 ℓ : Matrix d d ℝ))
        fun ℓ => (p.1.1 ℓ).2)
      (scaleDir_mem_flat_skipless_rmsNorm_zero θ hA p.1.2))
      (span_le_flat_ibz θ 0 (hV p.2.2))
  -- it is injective (Lemma A.18 for `ε = 0`)
  have hinj : Function.Injective Φ := by
    intro p q hpq
    rw [LinearMap.coprod_apply, LinearMap.coprod_apply, LinearMap.coprod_apply,
      LinearMap.coprod_apply] at hpq
    have h' : cobDir θ (fun ℓ => (p.1.1 ℓ : Matrix d d ℝ)) + scaleDir θ p.1.2
          + (p.2 : Params A dIn dOut)
        = cobDir θ (fun ℓ => (q.1.1 ℓ : Matrix d d ℝ)) + scaleDir θ q.1.2 + q.2 := hpq
    obtain ⟨h1, h2, h3⟩ := cobDir_add_scaleDir_add_inj_ibz θ V
      (fun v hv => E_eq_zero_of_mem_span_ibz θ (hV hv)) hrw hE hw
      (fun ℓ => (p.1.1 ℓ).2) (fun ℓ => (q.1.1 ℓ).2) p.2.2 q.2.2 h'
    exact Prod.ext (Prod.ext (funext fun ℓ => Subtype.ext (congrFun h1 ℓ)) h2) (Subtype.ext h3)
  -- the domain has dimension `(L + 1) (d(d−1)/2 + 1) + dim V`
  have hdim : Module.finrank ℝ (((Fin (L + 1) → antisymmetric d) × (Fin (L + 1) → ℝ)) × V) =
      (L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2 + 1) + Module.finrank ℝ V := by
    rw [Module.finrank_prod, Module.finrank_prod, Module.finrank_pi_fintype,
      finrank_antisymmetric, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
      Module.finrank_fin_fun]
    ring
  have h := funDim_add_finrank_le_of_le_flat' θ _ hflat
  rwa [LinearMap.finrank_range_of_inj hinj, hdim] at h

/-- **Theorem 4.2 of the skips paper with identity skips, for any symmetries inside the blocks,
under pre-RMSNorm with `ε = 0`:** if `E` has rank `d ≥ 1`, `fd ≤ P − (d(d−1)/2 + 1) − dim V`. -/
theorem funDim_add_le_residual_of_insideBlocks_rmsNorm_zero [Nonempty d] (hA : A.χ = rmsNorm 0)
    (V : Submodule ℝ (Params A dIn dOut))
    (hV : V ≤ Submodule.span ℝ {η | InsideBlocks A θ η})
    (hE : θ.E.rank = Fintype.card d) :
    funDim A 1 θ + ((Fintype.card d * (Fintype.card d - 1) / 2 + 1) + Module.finrank ℝ V)
      ≤ Module.finrank ℝ (Params A dIn dOut) :=
  -- the rotation and the scaling of all hidden states, and the directions of `V`
  funDim_add_le_of_coScale_add_urz θ hA hE V.subtype V.injective_subtype
    (fun v => E_eq_zero_of_mem_span_ibz θ (hV v.2)) (fun v => span_le_flat_ibz θ 1 (hV v.2))

end One

section Sum

variable {A B : Arch T d L} (θ : Params (A.sum B) dIn dOut)

/-- **The bound without skips for a network with two kinds of block, under pre-RMSNorm with
`ε = 0`:** let `V_A` and `V_B` be spaces of directions spanned by directions of symmetries inside
the blocks of the two parts, in each of which a direction whose read of block `ℓ` is `0` has the
write of block `ℓ` `0`. If `E` and the writes of the sum have rank `d ≥ 1`,
`fd ≤ P − (L + 1) (d(d−1)/2 + 1) − dim V_A − dim V_B`. -/
theorem funDim_add_le_skipless_sum_of_insideBlocks_rmsNorm_zero [Nonempty d]
    (hA : A.χ = rmsNorm 0)
    (VA : Submodule ℝ (Params A dIn dOut)) (VB : Submodule ℝ (Params B dIn dOut))
    (hVA : VA ≤ Submodule.span ℝ {η | InsideBlocks A θ.sumFst η})
    (hVB : VB ≤ Submodule.span ℝ {η | InsideBlocks B θ.sumSnd η})
    (hrwA : ∀ η ∈ VA, ∀ ℓ, η.read ℓ = 0 → η.write ℓ = 0)
    (hrwB : ∀ η ∈ VB, ∀ ℓ, η.read ℓ = 0 → η.write ℓ = 0)
    (hE : θ.E.rank = Fintype.card d) (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d) :
    funDim (A.sum B) 0 θ
        + ((L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
          + (Module.finrank ℝ VA + Module.finrank ℝ VB))
      ≤ Module.finrank ℝ (Params (A.sum B) dIn dOut) := by
  -- the bound for one architecture, for the lifts of `V_A` and `V_B` to the sum
  have h := funDim_add_le_skipless_of_insideBlocks_rmsNorm_zero θ hA _
    (sup_le_span_ibl θ VA VB hVA hVB) (write_eq_zero_of_read_ibl VA VB hrwA hrwB) hE hw
  rwa [finrank_sup_ibl θ VA VB hVA] at h

/-- **The bound with identity skips for a network with two kinds of block, under pre-RMSNorm with
`ε = 0`:** if `E` has rank `d ≥ 1`, `fd ≤ P − (d(d−1)/2 + 1) − dim V_A − dim V_B`. -/
theorem funDim_add_le_residual_sum_of_insideBlocks_rmsNorm_zero [Nonempty d]
    (hA : A.χ = rmsNorm 0)
    (VA : Submodule ℝ (Params A dIn dOut)) (VB : Submodule ℝ (Params B dIn dOut))
    (hVA : VA ≤ Submodule.span ℝ {η | InsideBlocks A θ.sumFst η})
    (hVB : VB ≤ Submodule.span ℝ {η | InsideBlocks B θ.sumSnd η})
    (hE : θ.E.rank = Fintype.card d) :
    funDim (A.sum B) 1 θ
        + ((Fintype.card d * (Fintype.card d - 1) / 2 + 1)
          + (Module.finrank ℝ VA + Module.finrank ℝ VB))
      ≤ Module.finrank ℝ (Params (A.sum B) dIn dOut) := by
  -- the bound for one architecture, for the lifts of `V_A` and `V_B` to the sum
  have h := funDim_add_le_residual_of_insideBlocks_rmsNorm_zero θ hA _
    (sup_le_span_ibl θ VA VB hVA hVB) hE
  rwa [finrank_sup_ibl θ VA VB hVA] at h

end Sum

end Skips
