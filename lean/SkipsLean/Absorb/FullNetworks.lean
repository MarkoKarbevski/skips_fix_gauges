import SkipsLean.Absorb.PatternMaps
import SkipsLean.Dimension.RankCriterionOn
import SkipsLean.Residual.DepthRescale
import SkipsLean.Dimension.ParameterCount

/-!
# Full residual ReLU networks and a lower bound from counting dimensions

Paper (absorb paper): Proposition 4.7 (A lower bound from counting dimensions) and the paragraph
before it. "Let the residual network have `P` weights and `s` hidden units. […] So on any finite
set of inputs, the Jacobian of the outputs with respect to the weights has rank at most
`P − d_model² − s` […]. We call a residual ReLU network full if this rank is reached on some
finite set of inputs at which no unit has argument `0`: its only redundancy is then these
symmetries." The proposition: "Consider ReLU networks of `L` blocks without normalization. The
full residual networks form an open set of weights. For almost every full residual network, every
skipless network of `L` blocks with the same `d_model` that equals it has, in total, at least
`L d_model² / (2 d_model − 1)` more hidden units." After it: "Full networks exist: every network
with generic weights is full once all its writes are scaled by a small enough factor."

Stated here for the residual network with the hidden units `hid ℓ` (any widths) and
`d_in ≥ d ≥ 1`:

* `IsFull θ`: a finite batch on which no unit has argument `0` at `θ` and on which the Jacobian
  has rank `P − d² − s`.
* On a batch on which no unit has argument `0` at `θ`, the Jacobian has rank at most
  `P − d² − s`, at every `θ`.
* The full networks form an open set.
* The proposition, in the setting of the main text (every block of the skipless network has at
  least `d` hidden units, Section 2): for almost every `θ`, if `θ` is full then no skipless ReLU
  network of `L` blocks with the widths `m ℓ ≥ d` equals it when
  `(2d − 1) ∑_ℓ m ℓ < (2d − 1) ∑_ℓ d_hidden^ℓ + L d²`, that is, with fewer than
  `L d² / (2d − 1)` more hidden units in total. Sard's theorem is a hypothesis from the
  literature (`Literature/Sard.lean`), as in the proof of the paper.
* Full networks exist (Lemma A.30 of the skips paper, `Residual/DepthRescale.lean`): for generic
  `θ` and all small `τ ≠ 0`, `θ_τ` is full.
-/

namespace Skips

open Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d]
  [Fintype dIn] [Fintype dOut]
variable {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]

/-! ### Helpers: the ReLU block map off its kinks (as in `Residual/DepthRescale.lean`) -/

/-- Helper: the matrices with no zero entry (the pre-activations with no unit at argument `0`). -/
private def noZero_full (m n : Type*) : Set (Matrix m n ℝ) :=
  {M | ∀ t i, M t i ≠ 0}

/-- Helper: the matrices with no zero entry form an open set. -/
private theorem isOpen_noZero_full {m n : Type*} [Fintype m] [Fintype n] :
    IsOpen (noZero_full m n) := by
  refine isOpen_iff_mem_nhds.2 fun M hM => ?_
  exact Filter.eventually_all.2 fun t => Filter.eventually_all.2 fun i =>
    (continuous_id.matrix_elem t i).continuousAt.eventually_ne (hM t i)

/-- Helper: ReLU is `0` or the identity near a point `z ≠ 0`, hence `C¹` there. -/
private theorem contDiffAt_relu_full {z : ℝ} (hz : z ≠ 0) : ContDiffAt ℝ 1 relu z := by
  rcases hz.lt_or_gt with hneg | hpos
  · have h : relu =ᶠ[𝓝 z] fun _ => (0 : ℝ) := by
      filter_upwards [eventually_lt_nhds hneg] with y hy
      exact max_eq_right hy.le
    exact contDiffAt_const.congr_of_eventuallyEq h
  · have h : relu =ᶠ[𝓝 z] fun y => y := by
      filter_upwards [eventually_gt_nhds hpos] with y hy
      exact max_eq_left hy.le
    exact contDiffAt_id.congr_of_eventuallyEq h

/-- Helper: `M ↦ ReLU(M)` (entrywise) is `C¹` on the matrices with no zero entry. -/
private theorem contDiffOn_map_relu_full {m n : Type*} [Fintype m] [Fintype n] :
    ContDiffOn ℝ 1 (fun M : Matrix m n ℝ => M.map relu) (noZero_full m n) := by
  intro M hM
  refine ContDiffAt.contDiffWithinAt (contDiffAt_pi.2 fun t => contDiffAt_pi.2 fun i => ?_)
  have hent : ContDiff ℝ 1 (fun M : Matrix m n ℝ => M t i) :=
    contDiff_pi.1 (contDiff_pi.1 contDiff_id t) i
  have h := (contDiffAt_relu_full (hM t i)).comp M hent.contDiffAt
  exact h

/-! ### Helpers: the outputs on a batch are `C¹` off the kinks (as in
`Residual/SmallWritesOn.lean`) -/

/-- Helper: the product of two matrix-valued maps that are `C^m` at a point is `C^m` there. -/
private theorem contDiffAt_mul_full {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {p q r : Type*} [Fintype p] [Fintype q] [Fintype r] {m : WithTop ℕ∞}
    {f : E → Matrix p q ℝ} {g : E → Matrix q r ℝ} {y : E}
    (hf : ContDiffAt ℝ m f y) (hg : ContDiffAt ℝ m g y) :
    ContDiffAt ℝ m (fun z => f z * g z) y := by
  -- entrywise: `(f g)_{ik} = ∑_j f_{ij} g_{jk}`
  refine contDiffAt_pi.2 fun i => contDiffAt_pi.2 fun k => ?_
  have hfe : ∀ j, ContDiffAt ℝ m (fun z => f z i j) y := fun j =>
    contDiffAt_pi.1 (contDiffAt_pi.1 hf i) j
  have hge : ∀ j, ContDiffAt ℝ m (fun z => g z j k) y := fun j =>
    contDiffAt_pi.1 (contDiffAt_pi.1 hg j) k
  have hs : ContDiffAt ℝ m (fun z => ∑ j, f z i j * g z j k) y :=
    ContDiffAt.sum fun j _ => (hfe j).mul (hge j)
  exact hs

/-- Helper: the embedding, as a continuous linear map of the parameters. -/
private noncomputable def clmE_full (A : Arch T d L) : Params A dIn dOut →L[ℝ] Matrix dIn d ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun θ' => θ'.E, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }

/-- Helper: the read of block `ℓ`, as a continuous linear map of the parameters. -/
private noncomputable def clmRead_full (A : Arch T d L) (ℓ : Fin L) :
    Params A dIn dOut →L[ℝ] Matrix d (A.r ℓ) ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun θ' => θ'.read ℓ, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }

/-- Helper: the write of block `ℓ`, as a continuous linear map of the parameters. -/
private noncomputable def clmWrite_full (A : Arch T d L) (ℓ : Fin L) :
    Params A dIn dOut →L[ℝ] Matrix (A.w ℓ) d ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun θ' => θ'.write ℓ, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }

/-- Helper: the readout, as a continuous linear map of the parameters. -/
private noncomputable def clmD_full (A : Arch T d L) : Params A dIn dOut →L[ℝ] Matrix d dOut ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun θ' => θ'.D, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }

omit [Nonempty T] [DecidableEq d] in
/-- Helper: at parameters `θ₀` whose pre-activations at the input `x` lie in the open sets
`V ℓ`, on which the `f_ℓ` are `C^m`, every hidden state is `C^m` in the parameters at `θ₀`. -/
private theorem contDiffAt_hidden_full (A : Arch T d L) (hA : A.χ = id)
    (S : Fin L → Matrix d d ℝ) (V : ∀ ℓ, Set (Matrix T (A.r ℓ) ℝ)) (hVo : ∀ ℓ, IsOpen (V ℓ))
    {m : WithTop ℕ∞} (hf : ∀ ℓ, ContDiffOn ℝ m (A.f ℓ) (V ℓ)) (θ₀ : Params A dIn dOut)
    (x : Matrix T dIn ℝ) (hx : ∀ ℓ, hidden A S θ₀ x ℓ.castSucc * θ₀.read ℓ ∈ V ℓ)
    (k : Fin (L + 1)) :
    ContDiffAt ℝ m (fun θ' : Params A dIn dOut => hidden A S θ' x k) θ₀ := by
  induction k using Fin.induction with
  | zero =>
    -- `h_0 = x E`
    have hE : ContDiffAt ℝ m (fun θ' : Params A dIn dOut => θ'.E) θ₀ :=
      (clmE_full A (dIn := dIn) (dOut := dOut)).contDiff.contDiffAt
    simp only [hidden_zero]
    exact contDiffAt_mul_full contDiffAt_const hE
  | succ k ih =>
    -- `h_{k+1} = h_k S_k + f_k(h_k W_read^k) W_write^k`, with `h_k W_read^k ∈ V k` at `θ₀`
    have hR : ContDiffAt ℝ m (fun θ' : Params A dIn dOut => θ'.read k) θ₀ :=
      (clmRead_full A (dIn := dIn) (dOut := dOut) k).contDiff.contDiffAt
    have hWr : ContDiffAt ℝ m (fun θ' : Params A dIn dOut => θ'.write k) θ₀ :=
      (clmWrite_full A (dIn := dIn) (dOut := dOut) k).contDiff.contDiffAt
    have hpre : ContDiffAt ℝ m
        (fun θ' : Params A dIn dOut => hidden A S θ' x k.castSucc * θ'.read k) θ₀ :=
      contDiffAt_mul_full ih hR
    have hfk : ContDiffAt ℝ m (A.f k) (hidden A S θ₀ x k.castSucc * θ₀.read k) :=
      (hf k).contDiffAt ((hVo k).mem_nhds (hx k))
    have hc : ContDiffAt ℝ m
        (fun θ' : Params A dIn dOut => A.f k (hidden A S θ' x k.castSucc * θ'.read k)) θ₀ :=
      hfk.comp θ₀ hpre
    have hs := (contDiffAt_mul_full ih (contDiffAt_const (c := S k))).add
      (contDiffAt_mul_full hc hWr)
    simp only [hidden_succ, hA, id_eq]
    exact hs

omit [Nonempty T] [DecidableEq d] in
/-- Helper: at such parameters the outputs on the batch are `C^m` in the parameters. -/
private theorem contDiffAt_evalBatch_full (A : Arch T d L) (hA : A.χ = id)
    (S : Fin L → Matrix d d ℝ) (V : ∀ ℓ, Set (Matrix T (A.r ℓ) ℝ)) (hVo : ∀ ℓ, IsOpen (V ℓ))
    {m : WithTop ℕ∞} (hf : ∀ ℓ, ContDiffOn ℝ m (A.f ℓ) (V ℓ)) (θ₀ : Params A dIn dOut) {n : ℕ}
    (X : Fin n → Matrix T dIn ℝ)
    (hx : ∀ i ℓ, hidden A S θ₀ (X i) ℓ.castSucc * θ₀.read ℓ ∈ V ℓ) :
    ContDiffAt ℝ m (evalBatch A S X) θ₀ := by
  refine contDiffAt_pi.2 fun i => ?_
  have hD : ContDiffAt ℝ m (fun θ' : Params A dIn dOut => θ'.D) θ₀ :=
    (clmD_full A (dIn := dIn) (dOut := dOut)).contDiff.contDiffAt
  have h := contDiffAt_mul_full
    (contDiffAt_hidden_full A hA S V hVo hf θ₀ (X i) (hx i) (Fin.last L)) hD
  simp only [evalBatch, eval, hA, id_eq]
  exact h

/-- **A full residual ReLU network:** the rank `P − d² − s` of the Jacobian is reached on some
finite batch of inputs at which no unit has argument `0`. -/
def IsFull (θ : Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut) : Prop :=
  ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ),
    (∀ (i : Fin n) (ℓ : Fin L) (t : T) (j : hid ℓ),
      (hidden (Arch.mlp relu id hid) 1 θ (X i) ℓ.castSucc * θ.read ℓ) t j ≠ 0) ∧
    jacobianRank (Arch.mlp relu id hid) 1 X θ
        + (Fintype.card d ^ 2 + ∑ ℓ, Fintype.card (hid ℓ))
      = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut)

omit [Nonempty T] in
/-- **"On any finite set of inputs, the Jacobian […] has rank at most `P − d² − s`", at every
parameter:** for `d_in ≥ d ≥ 1`, on a batch on which no unit has argument `0` at `θ`. -/
theorem jacobianRank_add_le_residual_relu_of_ne_zero [Nonempty d]
    (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (θ : Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut) {n : ℕ}
    (X : Fin n → Matrix T dIn ℝ)
    (hX : ∀ (i : Fin n) (ℓ : Fin L) (t : T) (j : hid ℓ),
      (hidden (Arch.mlp relu id hid) 1 θ (X i) ℓ.castSucc * θ.read ℓ) t j ≠ 0) :
    jacobianRank (Arch.mlp relu id hid) 1 X θ
        + (Fintype.card d ^ 2 + ∑ ℓ, Fintype.card (hid ℓ))
      ≤ Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut) := by
  -- near `θ` no unit has argument `0` on `X` and the rank on `X` does not drop
  -- (`Residual/SmallWritesOn.lean`)
  have hev := eventually_jacobianRank_ge_of_contDiffOn (Arch.mlp relu id hid) θ rfl 1
    (fun ℓ => noZero_full T (hid ℓ)) (fun ℓ => isOpen_noZero_full)
    (fun ℓ => contDiffOn_map_relu_full) X (fun i ℓ => hX i ℓ)
  obtain ⟨U, hUsub, hUo, hθU⟩ := mem_nhds_iff.1 hev
  -- a Haar measure: the open set `U ∋ θ` has positive measure, and almost every `θ'` has
  -- `fd(θ') + d² + s ≤ P` (Theorem 4.2 with identity skips, `Residual/UpperBoundSymmetries.lean`)
  let μ : Measure (Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut) := Measure.addHaar
  have hae := ae_funDim_add_le_residual_mlp_rescale relu_homogeneous μ hdIn
  have hpos : μ U ≠ 0 := (hUo.measure_pos μ ⟨θ, hθU⟩).ne'
  obtain ⟨θ', hθ'U, hθ'⟩ : ∃ θ' ∈ U, funDim (Arch.mlp relu id hid) 1 θ'
      + (Fintype.card d ^ 2 + ∑ ℓ, Fintype.card (hid ℓ))
        ≤ Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut) := by
    by_contra hcon
    refine hpos (measure_mono_null (fun x hx => ?_) (ae_iff.1 hae))
    exact fun h => hcon ⟨x, hx, h⟩
  -- the rank at `θ` is at most the rank at `θ'`, which is at most `fd(θ')`
  have h1 := (hUsub hθ'U).2
  have h2 := jacobianRank_le_funDim (A := Arch.mlp relu id hid) (S := 1) θ' X
  omega

omit [Nonempty T] in
/-- **Proposition 4.7, first sentence:** for `d_in ≥ d ≥ 1`, the full residual ReLU networks form
an open set of weights. -/
theorem isOpen_setOf_isFull [Nonempty d] (hdIn : Fintype.card d ≤ Fintype.card dIn) :
    IsOpen {θ : Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut | IsFull θ} := by
  refine isOpen_iff_mem_nhds.2 fun θ₀ hθ₀ => ?_
  obtain ⟨n, X, hX, hr⟩ := hθ₀
  -- near `θ₀` no unit has argument `0` on `X` and the rank on `X` does not drop; it cannot rise
  -- above `P − d² − s` either
  filter_upwards [eventually_jacobianRank_ge_of_contDiffOn (Arch.mlp relu id hid) θ₀ rfl 1
    (fun ℓ => noZero_full T (hid ℓ)) (fun ℓ => isOpen_noZero_full)
    (fun ℓ => contDiffOn_map_relu_full) X (fun i ℓ => hX i ℓ)] with θ' h
  obtain ⟨h1, h2⟩ := h
  have h3 := jacobianRank_add_le_residual_relu_of_ne_zero hdIn θ' X (fun i ℓ => h1 i ℓ)
  exact ⟨n, X, fun i ℓ => h1 i ℓ, by omega⟩

/-! ### Helpers: the competitors and the count -/

/-- Helper: the widths `m` of the skipless networks of the proposition: `m ℓ ≥ d` in every block
and `(2d − 1) ∑_ℓ m ℓ < (2d − 1) ∑_ℓ d_hidden^ℓ + L d²`. -/
private def widths_full (d : Type*) [Fintype d] (hid : Fin L → Type) [∀ ℓ, Fintype (hid ℓ)] :
    Set (Fin L → ℕ) :=
  {m | (∀ ℓ, Fintype.card d ≤ m ℓ) ∧
    (2 * Fintype.card d - 1) * ∑ ℓ, m ℓ
      < (2 * Fintype.card d - 1) * ∑ ℓ, Fintype.card (hid ℓ) + L * Fintype.card d ^ 2}

/-- Helper, the count of the proof of Proposition 4.7: with `P = d_in D + 2 D s + D d_out`
parameters and `s` units for the residual network, `P' = d_in D + 2 D a + D d_out` and `a` units
for the skipless one, a rank `k ≤ P' − (L + 1) D² − a` of the skipless network is below the rank
`r = P − D² − s` of the residual one when `(2D − 1) a < (2D − 1) s + L D²`. -/
private theorem rank_lt_full {D s a L P P' Din Dout k r : ℕ} (hD : 1 ≤ D)
    (hP : P = Din * D + 2 * D * s + D * Dout) (hP' : P' = Din * D + 2 * D * a + D * Dout)
    (hk : k + ((L + 1) * D ^ 2 + a) ≤ P') (hr : r + (D ^ 2 + s) = P)
    (hc : (2 * D - 1) * a < (2 * D - 1) * s + L * D ^ 2) : k < r := by
  -- write `2D = e + 1`, so that `2D a = e a + a` and `2D s = e s + s`
  obtain ⟨e, he⟩ : ∃ e, 2 * D = e + 1 := ⟨2 * D - 1, by omega⟩
  rw [show 2 * D - 1 = e by omega] at hc
  rw [he] at hP hP'
  have h1 : (L + 1) * D ^ 2 = L * D ^ 2 + D ^ 2 := by ring
  have h2 : (e + 1) * a = e * a + a := by ring
  have h3 : (e + 1) * s = e * s + s := by ring
  omega

omit [Nonempty T] in
/-- **Proposition 4.7, second sentence, given Sard's theorem:** for `d_in ≥ d ≥ 1`, for almost
every residual ReLU network `θ` of `L` blocks: if `θ` is full, no skipless ReLU network of `L`
blocks with the same `d` and at least `d` hidden units in every block equals it unless it has, in
total, at least `L d² / (2d − 1)` more hidden units. -/
theorem ae_isFull_imp_eval_ne_skipless_relu [Nonempty d]
    (hSard : ∀ (m : Fin L → ℕ) (r : ℕ), SardCriticalValues
      (Params (Arch.mlp (T := T) (d := d) relu id (fun ℓ => Fin (m ℓ))) dIn dOut) (Fin r → ℝ))
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn) :
    ∀ᵐ θ ∂μ, IsFull θ → ∀ m : Fin L → ℕ, (∀ ℓ, Fintype.card d ≤ m ℓ) →
      (2 * Fintype.card d - 1) * ∑ ℓ, m ℓ
          < (2 * Fintype.card d - 1) * ∑ ℓ, Fintype.card (hid ℓ) + L * Fintype.card d ^ 2 →
      ∀ η : Params (Arch.mlp (T := T) (d := d) relu id (fun ℓ => Fin (m ℓ))) dIn dOut,
        eval (Arch.mlp relu id hid) 1 θ ≠ eval (Arch.mlp relu id (fun ℓ => Fin (m ℓ))) 0 η := by
  -- the bad set: full networks that equal a skipless network with the widths of `widths_full`
  set B : Set (Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut) :=
    {θ | IsFull θ ∧ ∃ m ∈ widths_full d hid,
      ∃ η : Params (Arch.mlp (T := T) (d := d) relu id (fun ℓ => Fin (m ℓ))) dIn dOut,
        eval (Arch.mlp relu id hid) 1 θ = eval (Arch.mlp relu id (fun ℓ => Fin (m ℓ))) 0 η}
    with hB
  have hP := finrank_params_mlp (T := T) (d := d) (dIn := dIn) (dOut := dOut) relu id hid
  have hD : 1 ≤ Fintype.card d := Fintype.card_pos
  -- it is null near each of its points
  have hB0 : μ B = 0 := by
    refine measure_null_of_locally_null B fun θ₀ hθ₀ => ?_
    obtain ⟨⟨n, X, hX, hr⟩, m₀, hm₀, -⟩ := hθ₀
    -- near `θ₀` no unit has argument `0` on `X` and the rank on `X` is at least its value
    -- `r = P − d² − s` at `θ₀`: an open `U ∋ θ₀` where this holds
    have hev := eventually_jacobianRank_ge_of_contDiffOn (Arch.mlp relu id hid) θ₀ rfl 1
      (fun ℓ => noZero_full T (hid ℓ)) (fun ℓ => isOpen_noZero_full)
      (fun ℓ => contDiffOn_map_relu_full) X (fun i ℓ => hX i ℓ)
    obtain ⟨U, hUsub, hUo, hθ₀U⟩ := mem_nhds_iff.1 hev
    refine ⟨B ∩ U, inter_mem_nhdsWithin B (hUo.mem_nhds hθ₀U), ?_⟩
    set r := jacobianRank (Arch.mlp relu id hid) 1 X θ₀ with hr_def
    -- on `U` the outputs on `X` are `C¹`
    have hF : ContDiffOn ℝ 1 (evalBatch (Arch.mlp relu id hid) 1 X) U := fun θ hθ =>
      (contDiffAt_evalBatch_full (Arch.mlp relu id hid) rfl 1 (fun ℓ => noZero_full T (hid ℓ))
        (fun ℓ => isOpen_noZero_full) (fun ℓ => contDiffOn_map_relu_full) θ X
        (hUsub hθ).1).contDiffWithinAt
    -- the count: every pattern map of a competitor has rank below `r`
    have hcount : ∀ m ∈ widths_full d hid, ∀ k, k + ((L + 1) * Fintype.card d ^ 2
        + ∑ ℓ, Fintype.card (Fin (m ℓ)))
          ≤ Module.finrank ℝ
            (Params (Arch.mlp (T := T) (d := d) relu id (fun ℓ => Fin (m ℓ))) dIn dOut) →
        k < r := by
      intro m hm k hk
      have hP' := finrank_params_mlp (T := T) (d := d) (dIn := dIn) (dOut := dOut) relu id
        (fun ℓ => Fin (m ℓ))
      simp only [Fintype.card_fin] at hk hP'
      exact rank_lt_full hD hP hP' hk hr hm.2
    have hhid : ∀ m ∈ widths_full d hid, ∀ ℓ, Fintype.card d ≤ Fintype.card (Fin (m ℓ)) :=
      fun m hm ℓ => (Fintype.card_fin (m ℓ)).symm ▸ hm.1 ℓ
    -- `r ≥ 1`, from the competitor `m₀`
    have hr1 : 1 ≤ r := by
      have h := hcount m₀ hm₀ _ (finrank_range_fderiv_maskedBatch_skipless_add_le hdIn
        (hhid m₀ hm₀) X (fun _ _ _ _ => true) 0)
      omega
    -- the competitors: widths and patterns on `X`, countably many
    let ι := Σ m : widths_full d hid, (Fin n → ∀ ℓ : Fin L, T → Fin (m.1 ℓ) → Bool)
    have hcrit := ae_notMem_iUnion_range_of_rank_lt_on (ι := ι)
      (P' := fun i => Params (Arch.mlp (T := T) (d := d) relu id (fun ℓ => Fin (i.1.1 ℓ)))
        dIn dOut)
      (fun i r => hSard i.1.1 r) (evalBatch (Arch.mlp relu id hid) 1 X) U hUo hF
      (fun i => maskedBatch (d := d) (dOut := dOut) 0 X i.2)
      (fun i => analyticOnNhd_maskedBatch 0 X i.2) (r - 1)
      (fun i η => by
        have h := hcount i.1.1 i.1.2 _ (finrank_range_fderiv_maskedBatch_skipless_add_le hdIn
          (hhid i.1.1 i.1.2) X i.2 η)
        exact Nat.le_sub_one_of_lt h)
      (fun θ hθ => by
        have h : r ≤ jacobianRank (Arch.mlp relu id hid) 1 X θ := (hUsub hθ).2
        exact lt_of_lt_of_le (by omega) h)
      μ
    -- on `B ∩ U` the outputs on `X` are a value of the pattern map of the competitor
    refine measure_mono_null ?_ (ae_iff.1 hcrit)
    rintro θ ⟨⟨-, m, hm, η, heq⟩, hθU⟩ h
    refine h hθU ⟨⟨m, hm⟩, fun i => reluPattern 0 η (X i)⟩ ⟨η, ?_⟩
    rw [← evalBatch_relu_eq_maskedBatch]
    funext i
    exact (congrFun heq (X i)).symm
  -- from the null set to the statement
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hB0] with θ hθ hfull m hm hc η heq
  exact hθ ⟨hfull, m, ⟨hm, hc⟩, η, heq⟩

/-- **"Full networks exist: every network with generic weights is full once all its writes are
scaled by a small enough factor":** with `d_in, d_out ≥ d ≥ 2` and blocks of any widths, for
generic `θ` and all small `τ ≠ 0`, the network `θ_τ` is full. -/
theorem ae_eventually_isFull_smallWrites
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut)) [μ.IsAddHaarMeasure]
    (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, ∀ᶠ τ in 𝓝[≠] (0 : ℝ), IsFull (θ.smallWrites τ) := by
  -- Lemma A.30 for ReLU blocks (`Residual/DepthRescale.lean`); the reads of `θ_τ` are those of `θ`
  filter_upwards [ae_exists_eventually_jacobianRank_smallWrites_relu μ hd hdIn hdOut] with θ h
  obtain ⟨n, X, -, hτ⟩ := h
  filter_upwards [hτ] with τ h
  exact ⟨n, X, h.1, h.2⟩

end Skips
