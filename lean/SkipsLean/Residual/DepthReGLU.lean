import SkipsLean.Residual.DepthGated
import SkipsLean.Residual.SmallWritesOn
import SkipsLean.Residual.UpperBoundSymmetries
import SkipsLean.OneBlock.UnitsReGLU
import SkipsLean.Dimension.RescalingGate

/-!
# Residual networks of ReGLU blocks with small writes

Paper (skips paper): Lemma A.30 (ReLU-type blocks with small writes), for ReGLU blocks: "Let the
blocks be ReLU, ReLU² or ReGLU blocks, without normalization or biases, let `E` and `D` have rank
`d_model`, and let inputs range over all of `ℝ^{1×d_in}`, or over an open set that contains `0`.
For generic parameters `θ`, let `θ_τ` be the parameters `θ` with every `W_write^ℓ` replaced by
`τ W_write^ℓ`, as in Lemma A.27. For all small `τ ≠ 0`, the Jacobian of the residual network at
`θ_τ` has rank `P − d_model² − s` on some finite batch on which no pre-activation vanishes. So
the residual network has functional dimension `P − d_model² − s` on an open set of weights that
contains these, and at almost every point of this set the skips add at least `L d_model²` when
every block has width at least `d_model`." For ReGLU `s = 2 ∑_ℓ d_hidden^ℓ`: one rescaling of the
gate and one of the value for each hidden unit.

Stated here as in `Residual/DepthRescale.lean` (ReLU and ReLU² blocks), with Lemma B.3 for ReGLU
(`relu_gated_units_flat`, `OneBlock/UnitsReGLU.lean`) for the hidden units of all blocks together,
all inputs (`T × d_in` matrices):

* `SmallWritesGenericReGLU θ`: the conditions `SmallWritesGenericGated` of
  `Residual/DepthGated.lean` (those of Lemma A.27 for gated blocks) and the hypothesis of
  Lemma B.3 that only ReGLU uses: no value column of `E W_read^ℓ` is proportional to the gate
  column of the same hidden unit. They hold at generic parameters.
* `noKinkGateAll θ`: the inputs at which no limit pre-activation of a gate, an entry of a gate
  column of `x E W_read^ℓ`, vanishes.
* The kernel of `J_0` at these inputs: `η_E = E X`, `η_D = −X D`, and the reads and the writes
  of `η` are those of a rescaling of the values plus a rescaling of the gates, a space of
  dimension `d² + s`.
* The first sentence: a finite batch in `noKinkGateAll θ` such that for all small `τ ≠ 0` no gate
  pre-activation on the batch vanishes at `θ_τ` and the Jacobian on the batch at `θ_τ` has rank
  `P − d² − s`; hence `funDim (θ_τ) = P − d² − s`.
* The second sentence: `funDim = P − d² − s` at every parameter near `θ_τ`; an open set `U` on
  which `funDim = P − d² − s` and which contains `θ_τ` for generic `θ` and all small `τ ≠ 0`; and
  the gain `≥ L d²` at almost every point of `U` when every block has at least `d` hidden units.
-/

namespace Skips

open Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d]
  [Fintype dIn] [Fintype dOut]
variable {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]
variable {σ : ℝ → ℝ}

/-- **The conditions on `θ` in Lemma A.30, for ReGLU blocks:** those of Lemma A.27 for gated
blocks, and no value column `e_{ℓ,i}` of `E W_read^ℓ` is proportional to the gate column
`c_{ℓ,i}` of the same hidden unit. They do not involve the gate activation. -/
structure SmallWritesGenericReGLU
    (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) : Prop where
  /-- the conditions of Lemma A.27 for gated blocks -/
  gated : SmallWritesGenericGated θ
  /-- no value column of `E W_read^ℓ` is proportional to the gate column of the same unit -/
  value_not_gate : ∀ (ℓ : Fin L) (i : hid ℓ) (r : ℝ),
    (θ.E * θ.read ℓ)ᵀ (Sum.inr i) ≠ r • (θ.E * θ.read ℓ)ᵀ (Sum.inl i)

/-- The inputs at which no limit pre-activation of a gate vanishes: every entry of the gate
columns of `x E W_read^ℓ`, for every block `ℓ`, token and hidden unit, is nonzero. -/
def noKinkGateAll (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) :
    Set (Matrix T dIn ℝ) :=
  {x | ∀ (ℓ : Fin L) (t : T) (i : hid ℓ), (x * θ.E * θ.read ℓ) t (Sum.inl i) ≠ 0}

/-- The conditions of Lemma A.30 for ReGLU blocks hold at generic parameters, for
`d_in, d_out ≥ d ≥ 2` and blocks of any widths. -/
theorem ae_smallWritesGenericReGLU
    (μ : Measure (Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)) [μ.IsAddHaarMeasure]
    (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, SmallWritesGenericReGLU θ := by
  classical
  -- two distinct coordinates of `h` and two distinct input coordinates
  obtain ⟨k₁, k₂, hk⟩ := Fintype.exists_pair_of_one_lt_card (show 1 < Fintype.card d by omega)
  obtain ⟨a₁, a₂, ha⟩ := Fintype.exists_pair_of_one_lt_card (show 1 < Fintype.card dIn by omega)
  have hC : ∀ ℓ (a : dIn) (j : hid ℓ ⊕ hid ℓ), AnalyticOnNhd ℝ
      (fun θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut =>
        (θ.E * θ.read ℓ) a j) Set.univ := fun ℓ a j =>
    analyticOnNhd_E_mul_read (A := Arch.gated (T := T) (d := d) σ id hid) (dOut := dOut) ℓ a j
  -- the value column `e_{ℓ,i}` and the gate column `c_{ℓ,i}` of one unit are not proportional:
  -- a `2 × 2` minor of the two columns does not vanish (as `h6` in `ae_oneBlockGenericReGLU`)
  have h6 : ∀ᵐ θ ∂μ, ∀ ℓ (i : hid ℓ),
      (θ.E * θ.read ℓ) a₁ (Sum.inr i) * (θ.E * θ.read ℓ) a₂ (Sum.inl i)
        - (θ.E * θ.read ℓ) a₁ (Sum.inl i) * (θ.E * θ.read ℓ) a₂ (Sum.inr i) ≠ 0 := by
    refine ae_all_iff.2 fun ℓ => ae_all_iff.2 fun i => ?_
    -- the columns of the reads of all blocks together, indexed by `Σ ℓ, hid ℓ ⊕ hid ℓ`
    obtain ⟨E₀, W₀, hEW⟩ := exists_minor_ne_zero (q := Σ ℓ, hid ℓ ⊕ hid ℓ)
      (i := ⟨ℓ, Sum.inr i⟩) (j := ⟨ℓ, Sum.inl i⟩) ha hk
      (fun h => Sum.inr_ne_inl (eq_of_heq (Sigma.mk.inj_iff.1 h).2))
    let θ₀ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut :=
      ⟨E₀, fun ℓ' => Matrix.of fun k j => W₀ k ⟨ℓ', j⟩, 0, 0⟩
    have hg := ((hC ℓ a₁ (Sum.inr i)).mul (hC ℓ a₂ (Sum.inl i))).sub
      ((hC ℓ a₁ (Sum.inl i)).mul (hC ℓ a₂ (Sum.inr i)))
    exact ae_ne_zero_of_analytic μ hg ⟨θ₀, hEW⟩
  -- the conditions of Lemma A.27 for gated blocks hold at generic parameters (`DepthGated.lean`)
  filter_upwards [ae_smallWritesGenericGated μ hd hdIn hdOut, h6] with θ hg h6
  refine ⟨hg, fun ℓ i r hr => h6 ℓ i ?_⟩
  -- if `e_{ℓ,i} = r c_{ℓ,i}`, the minor vanishes
  have e1 : (θ.E * θ.read ℓ) a₁ (Sum.inr i) = r * (θ.E * θ.read ℓ) a₁ (Sum.inl i) :=
    congrFun hr a₁
  have e2 : (θ.E * θ.read ℓ) a₂ (Sum.inr i) = r * (θ.E * θ.read ℓ) a₂ (Sum.inl i) :=
    congrFun hr a₂
  rw [e1, e2]
  ring

/-! ### Helpers: the block map near pre-activations with no gate at its kink -/

/-- Helper (`contDiffAt_relu_rglu` of `OneBlock/ResidualRMSReGLU.lean`, of order `2`): `relu` is
`C²` away from its kink (it is `0` or the identity near `z ≠ 0`). -/
private theorem contDiffAt_relu_drg {z : ℝ} (hz : z ≠ 0) : ContDiffAt ℝ 2 relu z := by
  rcases hz.lt_or_gt with hneg | hpos
  · refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [eventually_lt_nhds hneg] with y hy
    exact max_eq_right hy.le
  · refine contDiffAt_id.congr_of_eventuallyEq ?_
    filter_upwards [eventually_gt_nhds hpos] with y hy
    exact max_eq_left hy.le

omit [Nonempty T] in
/-- Helper (`isOpen_gateSet_rglu`): the pre-activations of block `ℓ` with no gate at its kink form
an open set (a finite intersection of open sets). -/
private theorem isOpen_gateSet_drg (ℓ : Fin L) :
    IsOpen {M : Matrix T (hid ℓ ⊕ hid ℓ) ℝ | ∀ t i, M t (Sum.inl i) ≠ 0} := by
  have h : {M : Matrix T (hid ℓ ⊕ hid ℓ) ℝ | ∀ t i, M t (Sum.inl i) ≠ 0}
      = ⋂ t, ⋂ i, {M : Matrix T (hid ℓ ⊕ hid ℓ) ℝ | M t (Sum.inl i) ≠ 0} := by
    ext M
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
  rw [h]
  exact isOpen_iInter_of_finite fun t => isOpen_iInter_of_finite fun i =>
    isOpen_ne_fun (continuous_id.matrix_elem t (Sum.inl i)) continuous_const

omit [Nonempty T] [Fintype d] [DecidableEq d] in
/-- Helper (`contDiffAt_f_rglu`, of order `2`): at a pre-activation with no gate at its kink, the
map of a ReGLU block is `C²` (entry by entry, `relu` is `C²` away from `0`). -/
private theorem contDiffAt_f_drg (ℓ : Fin L) (M : Matrix T (hid ℓ ⊕ hid ℓ) ℝ)
    (hM : ∀ t i, M t (Sum.inl i) ≠ 0) :
    ContDiffAt ℝ 2 ((Arch.gated (T := T) (d := d) relu id hid).f ℓ) M := by
  refine contDiffAt_pi.2 fun t => contDiffAt_pi.2 fun i => ?_
  have he : ∀ j, ContDiffAt ℝ 2 (fun N : Matrix T (hid ℓ ⊕ hid ℓ) ℝ => N t j) M := fun j =>
    (contDiff_apply_apply ℝ t j).contDiffAt
  have h := ((contDiffAt_relu_drg (hM t i)).comp M (he (Sum.inl i))).mul (he (Sum.inr i))
  exact h

omit [Nonempty T] [Fintype d] [DecidableEq d] in
/-- Helper (`contDiffOn_f_rglu`, of order `2`): the map of a ReGLU block is `C²` on the
pre-activations with no gate at its kink. -/
private theorem contDiffOn_f_drg (ℓ : Fin L) :
    ContDiffOn ℝ 2 ((Arch.gated (T := T) (d := d) relu id hid).f ℓ)
      {M : Matrix T (hid ℓ ⊕ hid ℓ) ℝ | ∀ t i, M t (Sum.inl i) ≠ 0} := by
  intro M hM
  exact (contDiffAt_f_drg ℓ M hM).contDiffWithinAt

omit [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: `τ ↦ a + τ b` has the derivative `b` at `0`. -/
private theorem hasDerivAt_affine_drg (a b : ℝ) : HasDerivAt (fun τ : ℝ => a + τ * b) b 0 := by
  have h := ((hasDerivAt_id' (x := (0 : ℝ))).mul_const b).const_add a
  rw [one_mul] at h
  exact h

omit [Nonempty T] [Fintype d] [DecidableEq d] in
/-- Helper (`fderiv_f_apply_rglu`): the derivative of the map of a ReGLU block at `M` with no gate
at its kink, along `N`, entry `(t, i)`: `1[M_{t, g i} > 0] N_{t, g i} M_{t, v i}
+ relu(M_{t, g i}) N_{t, v i}`. -/
private theorem fderiv_f_apply_drg (ℓ : Fin L) (M N : Matrix T (hid ℓ ⊕ hid ℓ) ℝ)
    (hM : ∀ t i, M t (Sum.inl i) ≠ 0) (t : T) (i : hid ℓ) :
    fderiv ℝ ((Arch.gated (T := T) (d := d) relu id hid).f ℓ) M N t i
      = reluDeriv (M t (Sum.inl i)) * N t (Sum.inl i) * M t (Sum.inr i)
        + relu (M t (Sum.inl i)) * N t (Sum.inr i) := by
  have hd := (contDiffAt_f_drg (d := d) ℓ M hM).differentiableAt two_ne_zero
  -- the chain rule along the line `τ ↦ M + τ N`
  have hline : HasDerivAt (fun τ : ℝ => M + τ • N) N 0 := by
    have h := ((hasDerivAt_id (0 : ℝ)).smul_const N).const_add M
    rw [one_smul] at h
    exact h
  have h1 := hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hline (by rw [zero_smul, add_zero])
  have h2 := hasDerivAt_pi.1 (hasDerivAt_pi.1 h1 t) i
  -- the same derivative computed on the entry `(t, i)`; `relu` is differentiable at
  -- `M_{t, g i} ≠ 0`
  have h3 : HasDerivAt (fun τ : ℝ => relu (M t (Sum.inl i) + τ * N t (Sum.inl i))
      * (M t (Sum.inr i) + τ * N t (Sum.inr i)))
      (reluDeriv (M t (Sum.inl i)) * N t (Sum.inl i) * M t (Sum.inr i)
        + relu (M t (Sum.inl i)) * N t (Sum.inr i)) 0 := by
    have hu := hasDerivAt_affine_drg (M t (Sum.inl i)) (N t (Sum.inl i))
    have hw := hasDerivAt_affine_drg (M t (Sum.inr i)) (N t (Sum.inr i))
    have h := ((hasDerivAt_relu (hM t i)).comp_of_eq (0 : ℝ) hu
      (by simp only [zero_mul, add_zero])).mul hw
    convert h using 1
    · rfl
    · simp only [Function.comp_apply, zero_mul, add_zero]
  exact h2.unique h3

omit [Nonempty T] [DecidableEq d] [Fintype dOut] in
/-- Helper (`smallWritesLimit_gated_apply` of `DepthGated.lean`, for ReGLU blocks at an input with
no gate at its kink): the entries of `(J_0 η)(x)`:
`(x ψ_M)_{t o} + ∑_ℓ ∑_i [relu(z) w (ψ_A)_{i o} + 1[z > 0] (x ψ_C)_{t, g i} w A_{i o}
+ relu(z) (x ψ_C)_{t, v i} A_{i o}]`, with `z = (x C)_{t, g i}`, `w = (x C)_{t, v i}`. -/
private theorem smallWritesLimit_apply_drg
    (θ η : Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut) (x : Matrix T dIn ℝ)
    (hx : x ∈ noKinkGateAll θ) (t : T) (o : dOut) :
    smallWritesLimit (Arch.gated relu id hid) θ η x t o
      = (x * (η.E * θ.D + θ.E * η.D)) t o + ∑ ℓ, ∑ i : hid ℓ,
        (relu ((x * (θ.E * θ.read ℓ)) t (Sum.inl i)) * (x * (θ.E * θ.read ℓ)) t (Sum.inr i)
            * (η.write ℓ * θ.D) i o
          + reluDeriv ((x * (θ.E * θ.read ℓ)) t (Sum.inl i))
            * (x * (θ.E * η.read ℓ)) t (Sum.inl i)
            * (x * (θ.E * θ.read ℓ)) t (Sum.inr i) * (θ.write ℓ * θ.D) i o
          + relu ((x * (θ.E * θ.read ℓ)) t (Sum.inl i)) * (x * (θ.E * η.read ℓ)) t (Sum.inr i)
            * (θ.write ℓ * θ.D) i o) := by
  unfold smallWritesLimit
  rw [Matrix.add_apply, Matrix.sum_apply]
  congr 1
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc _ (η.write ℓ), Matrix.add_apply,
    Matrix.mul_apply, Matrix.mul_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [fderiv_f_apply_drg ℓ _ _ (hx ℓ), Matrix.mul_assoc x θ.E (θ.read ℓ),
    Matrix.mul_assoc x θ.E (η.read ℓ)]
  have hf : (Arch.gated (T := T) (d := d) relu id hid).f ℓ (x * (θ.E * θ.read ℓ)) t i
      = relu ((x * (θ.E * θ.read ℓ)) t (Sum.inl i)) * (x * (θ.E * θ.read ℓ)) t (Sum.inr i) := rfl
  rw [hf]
  ring

/-- Helper (`cancel_left_of_rank_dg` of `DepthGated.lean`): a matrix whose rank is its number of
columns cancels on the left, via a left inverse. -/
private theorem cancel_left_of_rank_drg {m n k : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (M : Matrix m n ℝ) (hM : M.rank = Fintype.card n) {X Y : Matrix n k ℝ}
    (h : M * X = M * Y) : X = Y := by
  obtain ⟨B, hB⟩ := Matrix.vecMul_surjective_iff_exists_left_inverse.mp
    (Matrix.vecMul_surjective_iff_rank_eq_card.mpr hM)
  have := congrArg (B * ·) h
  simpa only [← Matrix.mul_assoc, hB, Matrix.one_mul] using this

/-- Helper (`cancel_right_of_rank_dg` of `DepthGated.lean`): a matrix whose rank is its number of
rows cancels on the right, via a right inverse. -/
private theorem cancel_right_of_rank_drg {m n k : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    (M : Matrix m n ℝ) (hM : M.rank = Fintype.card m) {X Y : Matrix k m ℝ}
    (h : X * M = Y * M) : X = Y := by
  obtain ⟨R, hR⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.mp
    (Matrix.mulVec_surjective_iff_rank_eq_card.mpr hM)
  have := congrArg (· * R) h
  simpa only [Matrix.mul_assoc, hR, Matrix.mul_one] using this

/-- **Proof of Lemma A.30, the kernel of `J_0`, for ReGLU blocks:** under the conditions
`SmallWritesGenericReGLU`, a direction `η` with `(J_0 η)(x) = 0` at every input at which no limit
pre-activation of a gate vanishes has `η_E = E X` and `η_D = −X D` for one matrix `X`, and its
reads and writes are those of a rescaling of the values plus a rescaling of the gates of the
hidden units (Lemma B.3 for the units of all blocks together). -/
theorem smallWritesLimit_eq_zero_reglu
    (θ : Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut)
    (hθ : SmallWritesGenericReGLU θ)
    (η : Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut)
    (hη : ∀ x ∈ noKinkGateAll θ, smallWritesLimit (Arch.gated relu id hid) θ η x = 0) :
    ∃ (X : Matrix d d ℝ) (α β : ∀ ℓ, hid ℓ → ℝ), η.E = θ.E * X ∧ η.D = -(X * θ.D)
      ∧ (∀ ℓ, η.read ℓ = (rescaleDir θ α + rescaleDirGate 1 θ β).read ℓ)
      ∧ (∀ ℓ, η.write ℓ = (rescaleDir θ α + rescaleDirGate 1 θ β).write ℓ) := by
  -- Lemma B.3 for ReGLU for the hidden units of all blocks together, on the inputs `x` whose rows
  -- all equal `v`, with no gate at its kink: `ψ_M = 0`, and every unit only rescales its gate
  -- (by `λ`) and its value (by `-α`), its write row by `α - λ`
  obtain ⟨hm, -, lam, α, hα⟩ := relu_gated_units_flat (n := dIn) (k := dOut) (q := Σ ℓ, hid ℓ)
    (fun p => (θ.E * θ.read p.1)ᵀ (Sum.inl p.2)) 0 (fun p => (θ.E * θ.read p.1)ᵀ (Sum.inr p.2)) 0
    (fun p => (θ.write p.1 * θ.D) p.2)
    (η.E * θ.D + θ.E * η.D) 0 (fun p => (θ.E * η.read p.1)ᵀ (Sum.inl p.2)) 0
    (fun p => (θ.E * η.read p.1)ᵀ (Sum.inr p.2)) 0 (fun p => (η.write p.1 * θ.D) p.2)
    (fun p => hθ.gated.row_ne_zero p.1 p.2) (fun p => hθ.gated.gate_ne_zero p.1 p.2)
    (fun p q hpq => hθ.gated.gate_not_collinear p q hpq)
    (fun p => hθ.gated.value_ne_zero p.1 p.2)
    (fun p r hr => hθ.value_not_gate p.1 p.2 r (congrArg Prod.fst hr)) (by
      intro v hv
      -- the input with all rows `v` has no gate at its kink
      have hx : (Matrix.of fun _ : T => v) ∈ noKinkGateAll θ := by
        intro ℓ t i
        have h1 := hv ⟨ℓ, i⟩
        rw [Pi.zero_apply, add_zero] at h1
        rw [Matrix.mul_assoc]
        exact h1
      funext o
      have h := hη _ hx
      have h' := congrFun (congrFun h (Classical.arbitrary T)) o
      rw [smallWritesLimit_apply_drg θ η _ hx] at h'
      simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
        add_zero]
      rw [Fintype.sum_sigma]
      exact h')
  -- the reads: `E η_read^ℓ = E R'_ℓ` with `R'_ℓ` the rescaled gate and value columns, and `E`
  -- cancels
  have hread : ∀ ℓ, η.read ℓ = (rescaleDir θ (fun ℓ i => α ⟨ℓ, i⟩)
      + rescaleDirGate 1 θ (fun ℓ i => lam ⟨ℓ, i⟩)).read ℓ := by
    intro ℓ
    apply cancel_left_of_rank_drg θ.E hθ.gated.rank_E
    ext a j
    rcases j with i | i
    · have h1 : (θ.E * η.read ℓ) a (Sum.inl i) = lam ⟨ℓ, i⟩ * (θ.E * θ.read ℓ) a (Sum.inl i) :=
        congrFun (hα ⟨ℓ, i⟩).1 a
      rw [h1, Matrix.mul_apply, Matrix.mul_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      show _ = θ.E a k * (0 + lam ⟨ℓ, i⟩ * θ.read ℓ k (Sum.inl i))
      ring
    · have h1 : (θ.E * η.read ℓ) a (Sum.inr i)
          = -(α ⟨ℓ, i⟩) * (θ.E * θ.read ℓ) a (Sum.inr i) := congrFun (hα ⟨ℓ, i⟩).2.2.1 a
      rw [h1, Matrix.mul_apply, Matrix.mul_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      show _ = θ.E a k * (-(α ⟨ℓ, i⟩) * θ.read ℓ k (Sum.inr i) + 0)
      ring
  -- the writes: `η_write^ℓ D = W'_ℓ D` with `W'_ℓ` the rows rescaled by `α - λ`, and `D` cancels
  have hwrite : ∀ ℓ, η.write ℓ = (rescaleDir θ (fun ℓ i => α ⟨ℓ, i⟩)
      + rescaleDirGate 1 θ (fun ℓ i => lam ⟨ℓ, i⟩)).write ℓ := by
    intro ℓ
    apply cancel_right_of_rank_drg θ.D hθ.gated.rank_D
    ext i o
    have h1 : (η.write ℓ * θ.D) i o = (α ⟨ℓ, i⟩ - lam ⟨ℓ, i⟩) * (θ.write ℓ * θ.D) i o :=
      congrFun (hα ⟨ℓ, i⟩).2.2.2.2 o
    rw [h1, Matrix.mul_apply, Matrix.mul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    show _ = (α ⟨ℓ, i⟩ * θ.write ℓ i k + -(((1 : ℕ) : ℝ) * lam ⟨ℓ, i⟩) * θ.write ℓ i k) * θ.D k o
    rw [Nat.cast_one]
    ring
  -- `η_E D + E η_D = 0`: with a right inverse `R` of `D` and `X = -η_D R`, `η_E = E X`, and then
  -- `E η_D = -E X D`, so `η_D = -X D`
  obtain ⟨R, hR⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.mp
    (Matrix.mulVec_surjective_iff_rank_eq_card.mpr hθ.gated.rank_D)
  have hE : η.E = θ.E * -(η.D * R) := by
    have h := congrArg (· * R) hm
    simp only [Matrix.add_mul, Matrix.mul_assoc, hR, Matrix.mul_one, Matrix.zero_mul] at h
    rw [Matrix.mul_neg]
    exact eq_neg_of_add_eq_zero_left h
  have hD : η.D = -(-(η.D * R) * θ.D) := by
    apply cancel_left_of_rank_drg θ.E hθ.gated.rank_E
    rw [Matrix.mul_neg, ← Matrix.mul_assoc, ← hE]
    exact eq_neg_of_add_eq_zero_right hm
  exact ⟨-(η.D * R), fun ℓ i => α ⟨ℓ, i⟩, fun ℓ i => lam ⟨ℓ, i⟩, hE, hD, hread, hwrite⟩

/-- **Lemma A.30 for ReGLU blocks, first sentence, at one parameter:** under the conditions
`SmallWritesGenericReGLU` there is a finite batch of inputs at which no limit pre-activation of a
gate vanishes such that, for all small `τ ≠ 0`, no gate pre-activation on the batch vanishes at
`θ_τ` and the Jacobian of the residual network on the batch at `θ_τ` has rank
`P − d² − 2 ∑_ℓ d_hidden^ℓ`. -/
theorem exists_eventually_jacobianRank_smallWrites_reglu
    (θ : Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut)
    (hθ : SmallWritesGenericReGLU θ) :
    ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i, X i ∈ noKinkGateAll θ) ∧
      ∀ᶠ τ in 𝓝[≠] (0 : ℝ),
        (∀ (i : Fin n) (ℓ : Fin L) (t : T) (j : hid ℓ),
          (hidden (Arch.gated relu id hid) 1 (θ.smallWrites τ) (X i) ℓ.castSucc * θ.read ℓ) t
            (Sum.inl j) ≠ 0) ∧
        jacobianRank (Arch.gated relu id hid) 1 X (θ.smallWrites τ)
            + (Fintype.card d ^ 2 + 2 * ∑ ℓ, Fintype.card (hid ℓ))
          = Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut) := by
  sorry

/-- **Lemma A.30 for ReGLU blocks, the functional dimension at `θ_τ`:** under the conditions
`SmallWritesGenericReGLU`, for all small `τ ≠ 0` the residual network has
`fd(θ_τ) = P − d² − 2 ∑_ℓ d_hidden^ℓ`. -/
theorem eventually_funDim_smallWrites_reglu
    (θ : Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut)
    (hθ : SmallWritesGenericReGLU θ) :
    ∀ᶠ τ in 𝓝[≠] (0 : ℝ),
      funDim (Arch.gated relu id hid) 1 (θ.smallWrites τ)
          + (Fintype.card d ^ 2 + 2 * ∑ ℓ, Fintype.card (hid ℓ))
        = Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut) := by
  sorry

/-- **Lemma A.30 for ReGLU blocks, second sentence, near `θ_τ`:** under the conditions
`SmallWritesGenericReGLU`, for all small `τ ≠ 0` the residual network has
`fd = P − d² − 2 ∑_ℓ d_hidden^ℓ` at every parameter near `θ_τ`. -/
theorem eventually_eventually_funDim_smallWrites_reglu
    (θ : Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut)
    (hθ : SmallWritesGenericReGLU θ) :
    ∀ᶠ τ in 𝓝[≠] (0 : ℝ), ∀ᶠ θ' in 𝓝 (θ.smallWrites τ),
      funDim (Arch.gated relu id hid) 1 θ'
          + (Fintype.card d ^ 2 + 2 * ∑ ℓ, Fintype.card (hid ℓ))
        = Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut) := by
  sorry

/-- **Lemma A.30 for ReGLU blocks, first sentence:** with `d_in, d_out ≥ d ≥ 2` and blocks of
any widths, for generic parameters `θ` there is a finite batch of inputs at which no limit
pre-activation of a gate vanishes such that, for all small `τ ≠ 0`, no gate pre-activation on
the batch vanishes at `θ_τ` and the Jacobian of the residual network on the batch at `θ_τ` has
rank `P − d² − 2 ∑_ℓ d_hidden^ℓ`. -/
theorem ae_exists_eventually_jacobianRank_smallWrites_reglu
    (μ : Measure (Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut))
    [μ.IsAddHaarMeasure]
    (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i, X i ∈ noKinkGateAll θ) ∧
      ∀ᶠ τ in 𝓝[≠] (0 : ℝ),
        (∀ (i : Fin n) (ℓ : Fin L) (t : T) (j : hid ℓ),
          (hidden (Arch.gated relu id hid) 1 (θ.smallWrites τ) (X i) ℓ.castSucc * θ.read ℓ) t
            (Sum.inl j) ≠ 0) ∧
        jacobianRank (Arch.gated relu id hid) 1 X (θ.smallWrites τ)
            + (Fintype.card d ^ 2 + 2 * ∑ ℓ, Fintype.card (hid ℓ))
          = Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut) := by
  sorry

/-- **Lemma A.30 for ReGLU blocks, second sentence:** with `d_in, d_out ≥ d ≥ 2` and blocks of
any widths, there is an open set `U` of weights on which the residual network has
`fd = P − d² − 2 ∑_ℓ d_hidden^ℓ`, which contains `θ_τ` for generic `θ` and all small `τ ≠ 0`,
and at almost every point of which the skips add at least `L d²` when every block has at least
`d` hidden units. -/
theorem exists_isOpen_funDim_smallWrites_reglu
    (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∃ U : Set (Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut), IsOpen U ∧
      (∀ θ ∈ U, funDim (Arch.gated relu id hid) 1 θ
          + (Fintype.card d ^ 2 + 2 * ∑ ℓ, Fintype.card (hid ℓ))
        = Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut)) ∧
      (∀ (μ : Measure (Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut))
        [μ.IsAddHaarMeasure], ∀ᵐ θ ∂μ, ∀ᶠ τ in 𝓝[≠] (0 : ℝ), θ.smallWrites τ ∈ U) ∧
      (∀ (μ : Measure (Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut))
        [μ.IsAddHaarMeasure], (∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) →
        ∀ᵐ θ ∂μ, θ ∈ U → funDim (Arch.gated relu id hid) 0 θ + L * Fintype.card d ^ 2
          ≤ funDim (Arch.gated relu id hid) 1 θ) := by
  sorry

end Skips
