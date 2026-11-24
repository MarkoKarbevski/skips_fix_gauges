import SkipsLean.Absorb.NoWidth
import SkipsLean.Residual.LearnedSkips
import SkipsLean.Generic.Params
import SkipsLean.Dimension.UpperBoundRMSNorm

/-!
# Residual and skipless networks: when they are equal and when they are not

Paper ("Can an MLP Absorb Its Skip Connection Exactly?"): Proposition 4.4, Theorem 4.1 (with
Corollary A.3) and Proposition 5.4.

Networks are those of the library: `eval A S θ X` with the stream matrices `S = 1` (residual),
`S = 0` (skipless) or learned skips. Two networks are equal if they have the same output at every
input `X`. A skipless network that is compared with a residual one may have another model
dimension `d'`, another depth and other widths; it has the same `d_in`, `d_out` and tokens.

* Proposition 4.4: for `σ(z) - σ(-z) = z` (ReLU, GELU), without normalization, a residual network
  whose reads all have rank `d` equals a skipless network with `d` more hidden units in every block
  and the same embedding and readout.
* Theorem 4.1: a residual network with `E D ≠ 0` equals no skipless network of one or more blocks,
  (i) when every block of both networks vanishes at `0` with derivative `0` there (gated blocks whose
  gate vanishes at `0` and is differentiable there; blocks that are positively homogeneous of degree
  `k > 1`), without normalization or under pre-RMSNorm with `ε > 0`; (ii) for `tanh` blocks without
  normalization.
* Proposition 5.4: for `σ(z) - σ(-z) = c z`, `c ≠ 0`, without normalization, a skipless network of
  vanilla `σ` blocks equals (i) a network with learned skips, invertible at generic weights, and the
  same embedding, readout, `d` and widths, and (ii) at generic weights a residual network with the
  same readout, `d` and widths.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T dIn dOut : Type*} {d : Type} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d]
  [Fintype dIn] [Fintype dOut]
variable {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)] {σ : ℝ → ℝ} {c : ℝ}

/-! ### Proposition 4.4 -/

/-- **Proposition 4.4 (`d` more units per block suffice).** Let `σ(z) - σ(-z) = z`, as for ReLU
and GELU. Without normalization, a residual network whose reads all have rank `d` equals a skipless
network with `d` more hidden units in every block, with the same embedding and readout. -/
theorem exists_skipless_eq_residual_of_rank_read (hσ : ∀ z, σ z - σ (-z) = z)
    (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)
    (hr : ∀ ℓ, (θ.read ℓ).rank = Fintype.card d) :
    ∃ θ' : Params (Arch.mlp (T := T) (d := d) σ id (fun ℓ => hid ℓ ⊕ d)) dIn dOut,
      θ'.E = θ.E ∧ θ'.D = θ.D ∧
      ∀ X : Matrix T dIn ℝ,
        eval (Arch.mlp σ id hid) 1 θ X = eval (Arch.mlp σ id (fun ℓ => hid ℓ ⊕ d)) 0 θ' X := by
  -- Theorem 3.1 (ii) with `M = I`: the residual block `ℓ`, whose read has rank `d`, is a skipless
  -- block with `d` more hidden units
  have hσ1 : ∀ z, σ z - σ (-z) = 1 * z := fun z => by rw [one_mul]; exact hσ z
  have key : ∀ ℓ, ∃ (Wr' : Matrix d (hid ℓ ⊕ d) ℝ) (Ww' : Matrix (hid ℓ ⊕ d) d ℝ),
      ∀ x : d → ℝ, x ᵥ* 1 + vanillaBlock σ (θ.read ℓ) (θ.write ℓ) x = vanillaBlock σ Wr' Ww' x := by
    intro ℓ
    obtain ⟨Wr', Ww', -, h⟩ :=
      exists_vanillaBlock_add_linear hσ1 one_ne_zero (θ.read ℓ) (θ.write ℓ) (hr ℓ) 1
    exact ⟨Wr', Ww', h⟩
  choose Wr' Ww' hW using key
  -- the skipless network: the same embedding and readout, these reads and writes
  let θ' : Params (Arch.mlp (T := T) (d := d) σ id (fun ℓ => hid ℓ ⊕ d)) dIn dOut :=
    ⟨θ.E, Wr', Ww', θ.D⟩
  -- on every hidden state the residual block equals the new skipless block, token by token
  have hblock : ∀ ℓ (h : Matrix T d ℝ),
      h * (1 : Matrix d d ℝ) + (h * θ.read ℓ).map σ * θ.write ℓ
        = h * (0 : Matrix d d ℝ) + (h * Wr' ℓ).map σ * Ww' ℓ := by
    intro ℓ h
    funext t
    rw [Matrix.mul_zero, zero_add, Matrix.mul_one]
    show h t + ((h * θ.read ℓ).map σ * θ.write ℓ) t = ((h * Wr' ℓ).map σ * Ww' ℓ) t
    rw [map_mul_mul_row, map_mul_mul_row, ← hW ℓ (h t), Matrix.vecMul_one]
  -- hence the hidden states of the two networks agree, by induction on the blocks
  have hh : ∀ X k, hidden (Arch.mlp σ id hid) 1 θ X k
      = hidden (Arch.mlp σ id (fun ℓ => hid ℓ ⊕ d)) 0 θ' X k := by
    intro X k
    induction k using Fin.induction with
    | zero => rw [hidden_zero, hidden_zero]
    | succ ℓ ih =>
      rw [hidden_succ, hidden_succ, ← ih]
      exact hblock ℓ _
  -- and so do the outputs
  refine ⟨θ', rfl, rfl, fun X => ?_⟩
  simp only [eval, hh]
  rfl

/-! ### Theorem 4.1 -/

/-- Every block map of the architecture vanishes at `0` and has the derivative `0` there. This is
what the proof of Corollary A.3 uses of the blocks: "each such block maps `0` to `0` and has
Jacobian `0` there". -/
def Arch.FlatAtZero {d : Type*} (A : Arch T d L) : Prop :=
  ∀ ℓ, A.f ℓ 0 = 0 ∧
    HasFDerivAt (A.f ℓ) (0 : Matrix T (A.r ℓ) ℝ →L[ℝ] Matrix T (A.w ℓ) ℝ) 0

/-- Gated blocks whose gate vanishes at `0` and is differentiable there (SwiGLU, GeGLU) vanish at
`0` with derivative `0`: a hidden unit is the product of two terms that vanish at `0`. -/
theorem flatAtZero_gated {d : Type*} {χ : Matrix T d ℝ → Matrix T d ℝ} (h0 : σ 0 = 0)
    (hd : DifferentiableAt ℝ σ 0) : (Arch.gated (T := T) (d := d) σ χ hid).FlatAtZero := by
  intro ℓ
  refine ⟨?_, ?_⟩
  · -- at `M = 0` every hidden unit is `σ(0) · 0 = 0`
    ext t i
    show σ ((0 : Matrix T (hid ℓ ⊕ hid ℓ) ℝ) t (Sum.inl i))
      * (0 : Matrix T (hid ℓ ⊕ hid ℓ) ℝ) t (Sum.inr i) = 0
    simp only [Matrix.zero_apply, mul_zero]
  · show HasFDerivAt (fun M : Matrix T (hid ℓ ⊕ hid ℓ) ℝ =>
      (Matrix.of fun t i => σ (M t (Sum.inl i)) * M t (Sum.inr i) : Matrix T (hid ℓ) ℝ))
      (0 : Matrix T (hid ℓ ⊕ hid ℓ) ℝ →L[ℝ] Matrix T (hid ℓ) ℝ) 0
    refine hasFDerivAt_pi'' fun t => hasFDerivAt_pi'' fun i => ?_
    -- the gate `σ(M_{t, inl i})` and the value `M_{t, inr i}`: entries of `M`
    let pg : Matrix T (hid ℓ ⊕ hid ℓ) ℝ →L[ℝ] ℝ :=
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : hid ℓ ⊕ hid ℓ => ℝ) (Sum.inl i)).comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : T => hid ℓ ⊕ hid ℓ → ℝ) t)
    let pv : Matrix T (hid ℓ ⊕ hid ℓ) ℝ →L[ℝ] ℝ :=
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : hid ℓ ⊕ hid ℓ => ℝ) (Sum.inr i)).comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : T => hid ℓ ⊕ hid ℓ → ℝ) t)
    have hd' : HasDerivAt σ (deriv σ 0) (pg 0) := hd.hasDerivAt
    have h := (hd'.comp_hasFDerivAt (0 : Matrix T (hid ℓ ⊕ hid ℓ) ℝ) pg.hasFDerivAt).mul
      pv.hasFDerivAt
    refine h.congr_fderiv (ContinuousLinearMap.ext fun M => ?_)
    -- the derivative at `0` is `σ(0) · dv + 0 · dg = 0`
    show σ (pg 0) * pv M + pv 0 * (deriv σ 0 * pg M) = 0
    have e1 : pg 0 = 0 := rfl
    have e2 : pv 0 = 0 := rfl
    rw [e1, e2, h0, zero_mul, zero_mul, add_zero]

/-- Helper: a map bounded by `C ‖x‖^k` with `k > 1` has the derivative `0` at `0`. -/
private theorem hasFDerivAt_zero_of_le_rpow {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {k C : ℝ} (hk : 1 < k)
    {f : E → F} (hf : ∀ x, ‖f x‖ ≤ C * ‖x‖ ^ k) : HasFDerivAt f (0 : E →L[ℝ] F) 0 := by
  have hk0 : k ≠ 0 := ne_of_gt (by linarith)
  have hk1 : k - 1 ≠ 0 := ne_of_gt (by linarith)
  -- `f 0 = 0`, from the bound at `0`
  have hf0 : f 0 = 0 := by
    have h := hf 0
    rw [norm_zero, Real.zero_rpow hk0, mul_zero] at h
    exact norm_le_zero_iff.1 h
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  -- `|C| ‖x‖^(k-1) → 0` as `x → 0`
  have ht : Filter.Tendsto (fun x : E => |C| * ‖x‖ ^ (k - 1)) (nhds 0) (nhds 0) := by
    have h2 : ContinuousAt (fun y : ℝ => y ^ (k - 1)) 0 :=
      Real.continuousAt_rpow_const 0 (k - 1) (Or.inr (by linarith))
    have h3 := (h2.tendsto.comp (tendsto_norm_zero (E := E))).const_mul |C|
    rwa [Real.zero_rpow hk1, mul_zero] at h3
  refine Asymptotics.IsLittleO.of_bound fun ε hε => ?_
  filter_upwards [ht.eventually (gt_mem_nhds hε)] with x hx
  rw [zero_add, hf0, sub_zero]
  show ‖f x - 0‖ ≤ ε * ‖x‖
  rw [sub_zero]
  -- `‖f x‖ ≤ C ‖x‖^k ≤ |C| ‖x‖^(k-1) ‖x‖ ≤ ε ‖x‖`
  calc ‖f x‖ ≤ C * ‖x‖ ^ k := hf x
    _ ≤ |C| * ‖x‖ ^ k :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg (norm_nonneg x) k)
    _ = |C| * ‖x‖ ^ (k - 1) * ‖x‖ := by
        rw [mul_assoc, ← Real.rpow_add_one' (y := k - 1) (norm_nonneg x) (by rwa [sub_add_cancel]),
          sub_add_cancel]
    _ ≤ ε * ‖x‖ := mul_le_mul_of_nonneg_right hx.le (norm_nonneg x)

/-- A map that is positively homogeneous of degree `k > 1` and bounded on the unit sphere vanishes
at `0` and has the derivative `0` there. -/
theorem hasFDerivAt_zero_of_homogeneous {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℝ} (hk : 1 < k) (f : E → F)
    (hf : ∀ (lam : ℝ) (x : E), 0 < lam → f (lam • x) = lam ^ k • f x)
    (hb : ∃ C : ℝ, ∀ x : E, ‖x‖ = 1 → ‖f x‖ ≤ C) :
    f 0 = 0 ∧ HasFDerivAt f (0 : E →L[ℝ] F) 0 := by
  obtain ⟨C, hC⟩ := hb
  have hk0 : k ≠ 0 := ne_of_gt (by linarith)
  -- `f 0 = f (2 • 0) = 2^k • f 0`, and `2^k ≠ 1`
  have hf0 : f 0 = 0 := by
    have h := hf 2 0 two_pos
    rw [smul_zero] at h
    have h2 : (1 : ℝ) < 2 ^ k := Real.one_lt_rpow one_lt_two (by linarith)
    have h3 : ((2 : ℝ) ^ k - 1) • f 0 = 0 := by rw [sub_smul, one_smul, ← h, sub_self]
    exact (smul_eq_zero.1 h3).resolve_left (sub_ne_zero.2 h2.ne')
  refine ⟨hf0, hasFDerivAt_zero_of_le_rpow hk (C := C) fun x => ?_⟩
  -- `‖f x‖ = ‖x‖^k ‖f (x / ‖x‖)‖ ≤ C ‖x‖^k`
  rcases eq_or_ne x 0 with rfl | hx
  · rw [hf0, norm_zero, norm_zero, Real.zero_rpow hk0, mul_zero]
  · have hn : 0 < ‖x‖ := norm_pos_iff.2 hx
    have h1 : f x = ‖x‖ ^ k • f (‖x‖⁻¹ • x) := by
      rw [← hf ‖x‖ _ hn, smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
    have h2 : ‖‖x‖⁻¹ • x‖ = 1 := by
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
    have hxk : 0 ≤ ‖x‖ ^ k := Real.rpow_nonneg (norm_nonneg x) k
    rw [h1, norm_smul, Real.norm_eq_abs, abs_of_nonneg hxk]
    exact (mul_le_mul_of_nonneg_left (hC _ h2) hxk).trans_eq (mul_comm _ _)

/-- ReLU² blocks (positively homogeneous of degree `2`) vanish at `0` with derivative `0`. -/
theorem flatAtZero_mlp_reluSq {d : Type*} {χ : Matrix T d ℝ → Matrix T d ℝ} :
    (Arch.mlp (T := T) (d := d) reluSq χ hid).FlatAtZero := by
  intro ℓ
  refine ⟨?_, ?_⟩
  · -- `ReLU²(0) = 0`
    ext t i
    show reluSq ((0 : Matrix T (hid ℓ) ℝ) t i) = 0
    rw [Matrix.zero_apply, reluSq, max_self]
    norm_num
  · show HasFDerivAt (fun M : Matrix T (hid ℓ) ℝ => M.map reluSq)
      (0 : Matrix T (hid ℓ) ℝ →L[ℝ] Matrix T (hid ℓ) ℝ) 0
    refine hasFDerivAt_pi'' fun t => hasFDerivAt_pi'' fun i => ?_
    -- every entry is `ReLU²` of an entry, and `(ReLU²)'(0) = 0`
    have h := (hasDerivAt_reluSq ((0 : Matrix T (hid ℓ) ℝ) t i)).comp_hasFDerivAt
      (0 : Matrix T (hid ℓ) ℝ)
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : hid ℓ => ℝ) i).comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : T => hid ℓ → ℝ) t)).hasFDerivAt
    refine h.congr_fderiv (ContinuousLinearMap.ext fun M => ?_)
    show reluSqDeriv ((0 : Matrix T (hid ℓ) ℝ) t i) * M t i = 0
    rw [Matrix.zero_apply, reluSqDeriv, max_self, mul_zero, zero_mul]

/-- ReGLU blocks (positively homogeneous of degree `2`) vanish at `0` with derivative `0`. -/
theorem flatAtZero_gated_relu {d : Type*} {χ : Matrix T d ℝ → Matrix T d ℝ} :
    (Arch.gated (T := T) (d := d) relu χ hid).FlatAtZero := by
  intro ℓ
  -- every hidden unit `relu(M_{t, inl i}) M_{t, inr i}` is at most `‖M‖²` in absolute value
  have hb : ∀ M : Matrix T (hid ℓ ⊕ hid ℓ) ℝ,
      ‖(Matrix.of fun t i => relu (M t (Sum.inl i)) * M t (Sum.inr i) : Matrix T (hid ℓ) ℝ)‖
        ≤ 1 * ‖M‖ ^ (2 : ℝ) := by
    intro M
    rw [one_mul, Real.rpow_two, sq]
    refine (Matrix.norm_le_iff (mul_nonneg (norm_nonneg M) (norm_nonneg M))).2 fun t i => ?_
    rw [Matrix.of_apply, norm_mul]
    -- `|relu z| ≤ |z|`
    have hr : ‖relu (M t (Sum.inl i))‖ ≤ ‖M t (Sum.inl i)‖ := by
      rw [Real.norm_eq_abs, Real.norm_eq_abs, relu, abs_of_nonneg (le_max_right _ 0)]
      exact max_le (le_abs_self _) (abs_nonneg _)
    exact mul_le_mul (hr.trans (Matrix.norm_apply_le_norm M)) (Matrix.norm_apply_le_norm M)
      (norm_nonneg _) (norm_nonneg M)
  refine ⟨?_, hasFDerivAt_zero_of_le_rpow one_lt_two hb⟩
  -- at `M = 0` every hidden unit is `relu(0) · 0 = 0`
  ext t i
  show relu ((0 : Matrix T (hid ℓ ⊕ hid ℓ) ℝ) t (Sum.inl i))
    * (0 : Matrix T (hid ℓ ⊕ hid ℓ) ℝ) t (Sum.inr i) = 0
  simp only [Matrix.zero_apply, mul_zero]

/-- Helper: the right multiplication by a fixed matrix, as a continuous linear map. -/
private noncomputable def mulRightL {m n : Type*} [Fintype m] [Fintype n] (R : Matrix m n ℝ) :
    Matrix T m ℝ →L[ℝ] Matrix T n ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => M * R
      map_add' := fun a b => Matrix.add_mul a b R
      map_smul' := fun r a => Matrix.smul_mul r a R }

/-- Helper: along the line `τ ↦ τ X`, the embedding `τ X E` has the velocity `X E`. -/
private theorem hasDerivAt_line_mul {m n : Type*} [Fintype m] [Fintype n] (X : Matrix T m ℝ)
    (E : Matrix m n ℝ) : HasDerivAt (fun τ : ℝ => (τ • X) * E) (X * E) 0 := by
  have h := (hasDerivAt_id (0 : ℝ)).smul_const (X * E)
  rw [one_smul] at h
  refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun τ => ?_)
  show (τ • X) * E = τ • (X * E)
  rw [Matrix.smul_mul]

/-- Helper: one block along a curve `γ` through `0`. If `χ` vanishes at `0` and is differentiable
there, and the block map `f` vanishes at `0` with the derivative `0`, then
`γ S + f(χ(γ) R) W` passes through `0` with the velocity `γ'(0) S`: the block term has the
velocity `0`. -/
private theorem hasDerivAt_step {m r w : Type*} [Fintype m] [Fintype r] [Fintype w]
    {χ : Matrix T m ℝ → Matrix T m ℝ} (hχ0 : χ 0 = 0) (hχ : DifferentiableAt ℝ χ 0)
    {f : Matrix T r ℝ → Matrix T w ℝ} (hf0 : f 0 = 0)
    (hf : HasFDerivAt f (0 : Matrix T r ℝ →L[ℝ] Matrix T w ℝ) 0)
    (S : Matrix m m ℝ) (R : Matrix m r ℝ) (W : Matrix w m ℝ) {γ : ℝ → Matrix T m ℝ}
    {v : Matrix T m ℝ} (hγ : HasDerivAt γ v 0) (hγ0 : γ 0 = 0) :
    γ 0 * S + f (χ (γ 0) * R) * W = 0 ∧
      HasDerivAt (fun τ => γ τ * S + f (χ (γ τ) * R) * W) (v * S) 0 := by
  -- at `τ = 0`: `0 S + f(χ(0) R) W = f(0) W = 0`
  refine ⟨by rw [hγ0, Matrix.zero_mul, hχ0, Matrix.zero_mul, hf0, Matrix.zero_mul, add_zero], ?_⟩
  -- the stream term `γ S` has the velocity `v S`
  have h1 := (mulRightL (T := T) S).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hγ
  -- the read `χ(γ) R` passes through `0`
  have h2 := hχ.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hγ hγ0.symm
  have h3 := (mulRightL (T := T) R).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h2
  have h30 : (⇑(mulRightL (T := T) R) ∘ (χ ∘ γ)) 0 = 0 := by
    show χ (γ 0) * R = 0
    rw [hγ0, hχ0, Matrix.zero_mul]
  -- so the block term has the velocity `0`, since `f` has the derivative `0` at `0`
  have h4 := (mulRightL (T := T) W).hasFDerivAt.comp_hasDerivAt (0 : ℝ)
    (hf.comp_hasDerivAt_of_eq (0 : ℝ) h3 h30.symm)
  refine (h1.add h4).congr_deriv ?_
  show v * S + (0 : Matrix T w ℝ) * W = v * S
  rw [Matrix.zero_mul, add_zero]

omit [Fintype dOut] in
/-- Helper: in a network whose blocks are flat at `0` and whose `χ` vanishes at `0` and is
differentiable there, every hidden state along the line `τ ↦ τ X` passes through `0` at `τ = 0`
with some velocity. -/
private theorem hidden_line {m : Type*} [Fintype m] {A : Arch T m L} (hA : A.FlatAtZero)
    (hχ0 : A.χ 0 = 0) (hχ : DifferentiableAt ℝ A.χ 0) (S : Fin L → Matrix m m ℝ)
    (θ : Params A dIn dOut) (X : Matrix T dIn ℝ) (k : Fin (L + 1)) :
    hidden A S θ ((0 : ℝ) • X) k = 0 ∧
      ∃ v, HasDerivAt (fun τ : ℝ => hidden A S θ (τ • X) k) v 0 := by
  induction k using Fin.induction with
  | zero =>
    refine ⟨by rw [hidden_zero, zero_smul, Matrix.zero_mul], X * θ.E, ?_⟩
    simp only [hidden_zero]
    exact hasDerivAt_line_mul X θ.E
  | succ ℓ ih =>
    obtain ⟨h0, v, hd⟩ := ih
    have h := hasDerivAt_step hχ0 hχ (hA ℓ).1 (hA ℓ).2 (S ℓ) (θ.read ℓ) (θ.write ℓ) hd h0
    simp only [hidden_succ]
    exact ⟨h.1, v * S ℓ, h.2⟩

omit [Fintype dOut] in
/-- Helper: in the residual network (`S = 1`) the velocity is `X E` at every hidden state: the
chain rule gives `F'(0) = I` for every block `h ↦ h + f(χ(h) R) W`. -/
private theorem hidden_line_residual {m : Type*} [Fintype m] [DecidableEq m] {A : Arch T m L}
    (hA : A.FlatAtZero) (hχ0 : A.χ 0 = 0) (hχ : DifferentiableAt ℝ A.χ 0)
    (θ : Params A dIn dOut) (X : Matrix T dIn ℝ) (k : Fin (L + 1)) :
    hidden A 1 θ ((0 : ℝ) • X) k = 0 ∧
      HasDerivAt (fun τ : ℝ => hidden A 1 θ (τ • X) k) (X * θ.E) 0 := by
  induction k using Fin.induction with
  | zero =>
    refine ⟨by rw [hidden_zero, zero_smul, Matrix.zero_mul], ?_⟩
    simp only [hidden_zero]
    exact hasDerivAt_line_mul X θ.E
  | succ ℓ ih =>
    obtain ⟨h0, hd⟩ := ih
    have h := hasDerivAt_step hχ0 hχ (hA ℓ).1 (hA ℓ).2 (1 : Matrix m m ℝ) (θ.read ℓ)
      (θ.write ℓ) hd h0
    simp only [hidden_succ]
    exact ⟨h.1, h.2.congr_deriv (Matrix.mul_one _)⟩

omit [Fintype dOut] in
/-- Helper: in the skipless network (`S = 0`) of one or more blocks the last hidden state has the
velocity `0`: it is `f(χ(h) R) W` with `h` through `0`. -/
private theorem hidden_line_skipless_last {m : Type*} [Fintype m] {L' : ℕ}
    {A : Arch T m (L' + 1)} (hA : A.FlatAtZero) (hχ0 : A.χ 0 = 0)
    (hχ : DifferentiableAt ℝ A.χ 0) (θ : Params A dIn dOut) (X : Matrix T dIn ℝ) :
    hidden A 0 θ ((0 : ℝ) • X) (Fin.last (L' + 1)) = 0 ∧
      HasDerivAt (fun τ : ℝ => hidden A 0 θ (τ • X) (Fin.last (L' + 1))) 0 0 := by
  -- the hidden state before the last block passes through `0`
  obtain ⟨h0, v, hd⟩ := hidden_line hA hχ0 hχ 0 θ X (Fin.last L').castSucc
  -- the last block: `h_L = h_{L-1} 0 + f(χ(h_{L-1}) R) W`, with the velocity `v 0 = 0`
  have h := hasDerivAt_step hχ0 hχ (hA (Fin.last L')).1 (hA (Fin.last L')).2 (0 : Matrix m m ℝ)
    (θ.read (Fin.last L')) (θ.write (Fin.last L')) hd h0
  rw [show Fin.last (L' + 1) = (Fin.last L').succ from rfl]
  simp only [hidden_succ]
  exact ⟨h.1, h.2.congr_deriv (Matrix.mul_zero v)⟩

/-- Helper: the readout `χ(γ) D` along a curve `γ` through `0` with the velocity `v`, when `χ` has
the derivative `Lχ` at `0`, has the velocity `Lχ(v) D`. -/
private theorem hasDerivAt_readout {m n : Type*} [Fintype m] [Fintype n]
    {χ : Matrix T m ℝ → Matrix T m ℝ} {Lχ : Matrix T m ℝ →L[ℝ] Matrix T m ℝ}
    (hχ : HasFDerivAt χ Lχ 0) (D : Matrix m n ℝ) {γ : ℝ → Matrix T m ℝ} {v : Matrix T m ℝ}
    (hγ : HasDerivAt γ v 0) (hγ0 : γ 0 = 0) :
    HasDerivAt (fun τ => χ (γ τ) * D) (Lχ v * D) 0 := by
  have h1 := hχ.comp_hasDerivAt_of_eq (0 : ℝ) hγ hγ0.symm
  have h2 := (mulRightL (T := T) D).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
  exact h2

/-- Helper: the proof of Corollary A.3. Let both `χ` vanish at `0`, with the derivatives `Lχ` and
`Lχ'` there, and let all blocks be flat at `0`. Along the line `τ ↦ τ X` the residual network has
the velocity `Lχ(X E) D` at `τ = 0` and the skipless network the velocity `0`; so if
`Lχ(X E) D ≠ 0`, the two networks differ at some input. -/
private theorem exists_ne_of_flat {m m' : Type*} [Fintype m] [DecidableEq m] [Fintype m']
    {L' : ℕ} (A : Arch T m L) (A' : Arch T m' (L' + 1)) {Lχ : Matrix T m ℝ →L[ℝ] Matrix T m ℝ}
    {Lχ' : Matrix T m' ℝ →L[ℝ] Matrix T m' ℝ} (hχ0 : A.χ 0 = 0) (hχ : HasFDerivAt A.χ Lχ 0)
    (hχ0' : A'.χ 0 = 0) (hχ' : HasFDerivAt A'.χ Lχ' 0) (hA : A.FlatAtZero)
    (hA' : A'.FlatAtZero) (θ : Params A dIn dOut) (θ' : Params A' dIn dOut)
    (X : Matrix T dIn ℝ) (hX : Lχ (X * θ.E) * θ.D ≠ 0) :
    ∃ X : Matrix T dIn ℝ, eval A 1 θ X ≠ eval A' 0 θ' X := by
  by_contra hall
  have heq : (fun τ : ℝ => eval A 1 θ (τ • X)) = fun τ => eval A' 0 θ' (τ • X) :=
    funext fun τ => not_not.1 fun h => hall ⟨τ • X, h⟩
  -- the residual network: `F` has the Jacobian `I` at `0`, so the velocity is `Lχ(X E) D`
  obtain ⟨h0, hd⟩ := hidden_line_residual hA hχ0 hχ.differentiableAt θ X (Fin.last L)
  have h1 : HasDerivAt (fun τ : ℝ => eval A 1 θ (τ • X)) (Lχ (X * θ.E) * θ.D) 0 :=
    hasDerivAt_readout hχ θ.D hd h0
  -- the skipless network: `H` has the Jacobian `0` at `0`, so the velocity is `0`
  obtain ⟨h0', hd'⟩ := hidden_line_skipless_last hA' hχ0' hχ'.differentiableAt θ' X
  have h2 : HasDerivAt (fun τ : ℝ => eval A' 0 θ' (τ • X)) (Lχ' 0 * θ'.D) 0 :=
    hasDerivAt_readout hχ' θ'.D hd' h0'
  rw [← heq, map_zero, Matrix.zero_mul] at h2
  exact hX (h1.unique h2)

omit [Fintype T] in
/-- Helper: if `M ≠ 0` and there is a token, some matrix unit `X` has `(X M)_{t o} ≠ 0`. -/
private theorem exists_mul_ne_zero [Nonempty T] {m n : Type*} [Fintype m] {M : Matrix m n ℝ}
    (hM : M ≠ 0) : ∃ (X : Matrix T m ℝ) (t : T) (o : n), (X * M) t o ≠ 0 := by
  classical
  obtain ⟨a, o, h⟩ : ∃ a o, M a o ≠ 0 := by
    by_contra h
    exact hM (Matrix.ext fun a o => not_not.1 fun hao => h ⟨a, o, hao⟩)
  obtain ⟨t⟩ := ‹Nonempty T›
  refine ⟨Matrix.single t a 1, t, o, ?_⟩
  rw [Matrix.single_mul_apply_same, one_mul]
  exact h

/-- **Theorem 4.1 (i) / Corollary A.3, without normalization.** Let every block of a residual
network and of a skipless network of one or more blocks vanish at `0` with derivative `0` there. If
the residual network has `E D ≠ 0`, the two networks differ at some input: at `X = 0` the residual
network has the derivative `X ↦ X E D` and the skipless one the derivative `0`. -/
theorem exists_ne_residual_skipless_of_flatAtZero [Nonempty T] {L' : ℕ} {d' : Type*} [Fintype d']
    (A : Arch T d L) (A' : Arch T d' (L' + 1)) (hχ : A.χ = id) (hχ' : A'.χ = id)
    (hA : A.FlatAtZero) (hA' : A'.FlatAtZero) (θ : Params A dIn dOut) (hED : θ.E * θ.D ≠ 0)
    (θ' : Params A' dIn dOut) :
    ∃ X : Matrix T dIn ℝ, eval A 1 θ X ≠ eval A' 0 θ' X := by
  -- a matrix unit `X` with `X E D ≠ 0`
  obtain ⟨X, t, o, hX⟩ := exists_mul_ne_zero (T := T) hED
  -- without normalization `χ = id` vanishes at `0` and has the derivative `I` there
  refine exists_ne_of_flat A A' (Lχ := ContinuousLinearMap.id ℝ _)
    (Lχ' := ContinuousLinearMap.id ℝ _) (by rw [hχ, id_eq]) (by rw [hχ]; exact hasFDerivAt_id 0)
    (by rw [hχ', id_eq]) (by rw [hχ']; exact hasFDerivAt_id 0) hA hA' θ θ' X fun h => hX ?_
  -- `X E D = 0` would contradict the choice of `X`
  rw [← Matrix.mul_assoc]
  exact congrFun (congrFun h t) o

omit [Fintype T] in
/-- Helper: RMSNorm vanishes at `0`. -/
private theorem rmsNorm_zero_mat {m : Type*} [Fintype m] (ε : ℝ) :
    rmsNorm ε (0 : Matrix T m ℝ) = 0 := by
  ext t i
  simp [rmsNorm, rmsRow]

/-- Helper: RMSNorm with `ε > 0` has the derivative `I / √ε` at `0`: the entry `(t, i)` is
`s(h) h_{t i}` with `s(h) = (‖h_t‖² / d + ε)^{-1/2}` differentiable and `s(0) = 1 / √ε`. -/
private theorem hasFDerivAt_rmsNorm_zero {m : Type*} [Fintype m] {ε : ℝ} (hε : 0 < ε) :
    HasFDerivAt (rmsNorm ε : Matrix T m ℝ → Matrix T m ℝ)
      ((Real.sqrt ε)⁻¹ • ContinuousLinearMap.id ℝ (Matrix T m ℝ)) 0 := by
  refine hasFDerivAt_pi'' fun t => hasFDerivAt_pi'' fun i => ?_
  have hq : Differentiable ℝ fun h : Matrix T m ℝ => (h t ⬝ᵥ h t) / (Fintype.card m : ℝ) + ε := by
    simp only [dotProduct]
    fun_prop
  have h00 : (0 : Matrix T m ℝ) t = 0 := rfl
  have hq0 : ((0 : Matrix T m ℝ) t ⬝ᵥ (0 : Matrix T m ℝ) t) / (Fintype.card m : ℝ) + ε = ε := by
    rw [h00, zero_dotProduct, zero_div, zero_add]
  have hs : DifferentiableAt ℝ
      (fun h : Matrix T m ℝ => (Real.sqrt ((h t ⬝ᵥ h t) / (Fintype.card m : ℝ) + ε))⁻¹) 0 := by
    have hpos : 0 < ((0 : Matrix T m ℝ) t ⬝ᵥ (0 : Matrix T m ℝ) t) / (Fintype.card m : ℝ) + ε := by
      rw [hq0]
      exact hε
    exact ((hq 0).sqrt hpos.ne').inv (Real.sqrt_pos.2 hpos).ne'
  have hp : HasFDerivAt (fun h : Matrix T m ℝ => h t i)
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : m => ℝ) i).comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : T => m → ℝ) t)) 0 :=
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : m => ℝ) i).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : T => m → ℝ) t)).hasFDerivAt
  have h := hs.hasFDerivAt.mul hp
  show HasFDerivAt (fun h : Matrix T m ℝ =>
    (Real.sqrt ((h t ⬝ᵥ h t) / (Fintype.card m : ℝ) + ε))⁻¹ * h t i) _ 0
  refine h.congr_fderiv (ContinuousLinearMap.ext fun M => ?_)
  show (Real.sqrt (((0 : Matrix T m ℝ) t ⬝ᵥ (0 : Matrix T m ℝ) t) / (Fintype.card m : ℝ) + ε))⁻¹
      * M t i + (0 : Matrix T m ℝ) t i * _ = (Real.sqrt ε)⁻¹ * M t i
  rw [hq0, Matrix.zero_apply, zero_mul, add_zero]

/-- **Theorem 4.1 (i) / Corollary A.3, under pre-RMSNorm with `ε > 0`:** the same, since
`N(0) = 0` and `N` has the derivative `I / √ε` at `0`. -/
theorem exists_ne_residual_skipless_of_flatAtZero_rmsNorm [Nonempty T] {L' : ℕ} {d' : Type*}
    [Fintype d'] {ε ε' : ℝ} (hε : 0 < ε) (hε' : 0 < ε')
    (A : Arch T d L) (A' : Arch T d' (L' + 1)) (hχ : A.χ = rmsNorm ε) (hχ' : A'.χ = rmsNorm ε')
    (hA : A.FlatAtZero) (hA' : A'.FlatAtZero) (θ : Params A dIn dOut) (hED : θ.E * θ.D ≠ 0)
    (θ' : Params A' dIn dOut) :
    ∃ X : Matrix T dIn ℝ, eval A 1 θ X ≠ eval A' 0 θ' X := by
  -- a matrix unit `X` with `X E D ≠ 0`
  obtain ⟨X, t, o, hX⟩ := exists_mul_ne_zero (T := T) hED
  -- `N(0) = 0`, and `N` has the derivative `I / √ε` at `0`
  refine exists_ne_of_flat A A' (Lχ := (Real.sqrt ε)⁻¹ • ContinuousLinearMap.id ℝ _)
    (Lχ' := (Real.sqrt ε')⁻¹ • ContinuousLinearMap.id ℝ _) (by rw [hχ]; exact rmsNorm_zero_mat ε)
    (by rw [hχ]; exact hasFDerivAt_rmsNorm_zero hε) (by rw [hχ']; exact rmsNorm_zero_mat ε')
    (by rw [hχ']; exact hasFDerivAt_rmsNorm_zero hε') hA hA' θ θ' X fun h => hX ?_
  -- `(X E / √ε) D = 0` would give `X E D = 0`
  have h1 : ((Real.sqrt ε)⁻¹ • (X * θ.E) * θ.D) t o = 0 := congrFun (congrFun h t) o
  rw [Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul, Matrix.mul_assoc] at h1
  exact (mul_eq_zero.1 h1).resolve_left (inv_ne_zero (Real.sqrt_pos.2 hε).ne')

omit [Fintype T] in
/-- Helper: the entries of `tanh(M) W` are bounded by `∑ i, |W i j|`, whatever `M`. -/
private theorem abs_map_tanh_mul_le {m n : Type*} [Fintype n] (M : Matrix T n ℝ)
    (W : Matrix n m ℝ) (t : T) (j : m) :
    |((M.map Real.tanh) * W) t j| ≤ ∑ i, |W i j| := by
  rw [Matrix.mul_apply]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul, Matrix.map_apply]
  exact mul_le_of_le_one_left (abs_nonneg _) (Real.abs_tanh_lt_one _).le

omit [Fintype T] in
/-- Helper: if the entries of the column `j` of `M` are bounded by `B j`, those of `M D` are
bounded by `∑ j, B j |D j o|`. -/
private theorem abs_mul_apply_le {m n : Type*} [Fintype m] {M : Matrix T m ℝ} {B : m → ℝ}
    (hM : ∀ t j, |M t j| ≤ B j) (D : Matrix m n ℝ) (t : T) (o : n) :
    |(M * D) t o| ≤ ∑ j, B j * |D j o| := by
  rw [Matrix.mul_apply]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_right (hM t j) (abs_nonneg _)

omit [Fintype T] in
/-- Helper: a residual `tanh` block moves a hidden state by at most `∑ i, |W i j|` in the
entry `(t, j)`. -/
private theorem abs_step_tanh_le {m : Type*} [Fintype m] (h Y : Matrix T d ℝ)
    (R : Matrix d m ℝ) (W : Matrix m d ℝ) (t : T) (j : d) :
    |(h * (1 : Matrix d d ℝ) + (h * R).map Real.tanh * W - Y) t j|
      ≤ |(h - Y) t j| + ∑ i, |W i j| := by
  rw [Matrix.mul_one, add_sub_right_comm, Matrix.add_apply]
  exact (abs_add_le _ _).trans (add_le_add le_rfl (abs_map_tanh_mul_le _ _ t j))

omit [Fintype T] [Fintype dOut] in
/-- Helper: in a residual network of `tanh` blocks, `F(X E) - X E` is bounded: at every hidden
state, the entries of `h_k - X E` are bounded independently of `X`. -/
private theorem bounded_hidden_tanh
    (θ : Params (Arch.mlp (T := T) (d := d) Real.tanh id hid) dIn dOut) (k : Fin (L + 1)) :
    ∃ B : d → ℝ, ∀ (X : Matrix T dIn ℝ) (t : T) (j : d),
      |(hidden (Arch.mlp Real.tanh id hid) 1 θ X k - X * θ.E) t j| ≤ B j := by
  induction k using Fin.induction with
  | zero => exact ⟨fun _ => 0, fun X t j => by simp⟩
  | succ ℓ ih =>
    obtain ⟨B, hB⟩ := ih
    refine ⟨fun j => B j + ∑ i, |θ.write ℓ i j|, fun X t j => ?_⟩
    rw [hidden_succ]
    exact (abs_step_tanh_le (hidden (Arch.mlp Real.tanh id hid) 1 θ X ℓ.castSucc) (X * θ.E)
      (θ.read ℓ) (θ.write ℓ) t j).trans (add_le_add (hB X t j) le_rfl)

/-- **Theorem 4.1 (ii):** without normalization, a residual network of `tanh` blocks with
`E D ≠ 0` equals no skipless network of one or more `tanh` blocks, of any depth, widths and model
dimension: the residual network differs from `X E D` by a bounded map, and the skipless one is
bounded. -/
theorem exists_ne_residual_skipless_tanh [Nonempty T] {L' : ℕ} {d' : Type*} [Fintype d']
    {hid' : Fin (L' + 1) → Type} [∀ ℓ, Fintype (hid' ℓ)]
    (θ : Params (Arch.mlp (T := T) (d := d) Real.tanh id hid) dIn dOut) (hED : θ.E * θ.D ≠ 0)
    (θ' : Params (Arch.mlp (T := T) (d := d') Real.tanh id hid') dIn dOut) :
    ∃ X : Matrix T dIn ℝ,
      eval (Arch.mlp Real.tanh id hid) 1 θ X ≠ eval (Arch.mlp Real.tanh id hid') 0 θ' X := by
  -- a matrix unit `X₀` with `(X₀ E D)_{t o} ≠ 0`
  obtain ⟨X₀, t, o, he⟩ := exists_mul_ne_zero (T := T) hED
  -- the residual network is `X E D` plus a map bounded by `C`
  obtain ⟨B, hB⟩ := bounded_hidden_tanh θ (Fin.last L)
  have hres : ∀ X : Matrix T dIn ℝ,
      |eval (Arch.mlp Real.tanh id hid) 1 θ X t o - (X * (θ.E * θ.D)) t o|
        ≤ ∑ j, B j * |θ.D j o| := by
    intro X
    have e1 : eval (Arch.mlp Real.tanh id hid) 1 θ X = X * (θ.E * θ.D)
        + (hidden (Arch.mlp Real.tanh id hid) 1 θ X (Fin.last L) - X * θ.E) * θ.D := by
      show hidden (Arch.mlp Real.tanh id hid) 1 θ X (Fin.last L) * θ.D = _
      rw [Matrix.sub_mul, Matrix.mul_assoc]
      abel
    rw [e1, Matrix.add_apply, add_sub_cancel_left]
    exact abs_mul_apply_le (hB X) θ.D t o
  -- the skipless network is bounded by `C'`: its last hidden state is `tanh(…) W`
  have hskip : ∀ X : Matrix T dIn ℝ,
      |eval (Arch.mlp Real.tanh id hid') 0 θ' X t o|
        ≤ ∑ j, (∑ i, |θ'.write (Fin.last L') i j|) * |θ'.D j o| := by
    intro X
    show |(hidden (Arch.mlp Real.tanh id hid') 0 θ' X (Fin.last L').succ * θ'.D) t o| ≤ _
    rw [hidden_succ, Pi.zero_apply, Matrix.mul_zero, zero_add]
    exact abs_mul_apply_le (fun t j => abs_map_tanh_mul_le _ _ t j) θ'.D t o
  -- along the line `τ X₀` the difference grows like `τ (X₀ E D)_{t o}`: a contradiction
  by_contra hall
  have heq : ∀ X, eval (Arch.mlp Real.tanh id hid) 1 θ X
      = eval (Arch.mlp Real.tanh id hid') 0 θ' X := fun X => not_not.1 fun h => hall ⟨X, h⟩
  set C := ∑ j, B j * |θ.D j o|
  set C' := ∑ j, (∑ i, |θ'.write (Fin.last L') i j|) * |θ'.D j o|
  have hepos : 0 < |(X₀ * (θ.E * θ.D)) t o| := abs_pos.2 he
  set τ := (|C| + |C'| + 1) / |(X₀ * (θ.E * θ.D)) t o| with hτ
  have h1 := hres (τ • X₀)
  have h2 := hskip (τ • X₀)
  rw [← heq] at h2
  rw [Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul] at h1
  have h4 : |τ * (X₀ * (θ.E * θ.D)) t o| ≤ C + C' := by
    rw [abs_le] at h1 h2 ⊢
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  have h5 : |τ * (X₀ * (θ.E * θ.D)) t o| = |C| + |C'| + 1 := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ τ), hτ, div_mul_cancel₀ _ hepos.ne']
  linarith [le_abs_self C, le_abs_self C']

/-! ### Proposition 5.4 -/

variable [∀ ℓ, DecidableEq (hid ℓ)]

/-- The parameters with the reads of the units of `S ℓ` flipped in every block `ℓ` (the blocks
`B'_ℓ` of the proof of Proposition 5.4). -/
def Params.flipReads (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)
    (S : ∀ ℓ, Finset (hid ℓ)) : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut where
  E := θ.E
  read ℓ := flipCols (S ℓ) (θ.read ℓ)
  write := θ.write
  D := θ.D

/-- **Proposition 5.4 (i), the identity of its proof.** Let `σ(z) - σ(-z) = c z`. For any sets
`S_ℓ` of units, the skipless network equals the network with the learned skips
`A_ℓ = c K_ℓ`, `K_ℓ = W_read^ℓ[:,S_ℓ] W_write^ℓ[S_ℓ,:]`, the reads of the units of `S_ℓ` flipped,
and the same embedding, writes and readout. -/
theorem eval_skipless_eq_learned_flipReads (hσ : ∀ z, σ z - σ (-z) = c * z)
    (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) (S : ∀ ℓ, Finset (hid ℓ))
    (X : Matrix T dIn ℝ) :
    eval (Arch.mlp σ id hid) 0 θ X
      = eval (Arch.mlp σ id hid) (fun ℓ => c • subProd (S ℓ) (θ.read ℓ) (θ.write ℓ))
          (θ.flipReads S) X := by
  -- `σ(z) = σ(-z) + c z` gives, token by token, `B_ℓ(h) = h (c K_ℓ) + B'_ℓ(h)`
  have hblock : ∀ ℓ (h : Matrix T d ℝ),
      h * (0 : Matrix d d ℝ) + (h * θ.read ℓ).map σ * θ.write ℓ
        = h * (c • subProd (S ℓ) (θ.read ℓ) (θ.write ℓ))
          + (h * flipCols (S ℓ) (θ.read ℓ)).map σ * θ.write ℓ := by
    intro ℓ h
    funext t
    rw [Matrix.mul_zero, zero_add]
    show ((h * θ.read ℓ).map σ * θ.write ℓ) t
      = (h * (c • subProd (S ℓ) (θ.read ℓ) (θ.write ℓ))) t
        + ((h * flipCols (S ℓ) (θ.read ℓ)).map σ * θ.write ℓ) t
    rw [map_mul_mul_row, map_mul_mul_row, vanillaBlock_flipCols hσ, Matrix.mul_apply_eq_vecMul,
      Matrix.vecMul_smul]
    abel
  -- hence the hidden states `s_ℓ` of the two networks agree, by induction on the blocks
  have hh : ∀ k, hidden (Arch.mlp σ id hid) 0 θ X k
      = hidden (Arch.mlp σ id hid) (fun ℓ => c • subProd (S ℓ) (θ.read ℓ) (θ.write ℓ))
          (θ.flipReads S) X k := by
    intro k
    induction k using Fin.induction with
    | zero => rw [hidden_zero, hidden_zero]; rfl
    | succ ℓ ih =>
      rw [hidden_succ, hidden_succ, ← ih]
      exact hblock ℓ _
  -- and so do the outputs
  simp only [eval, hh]
  rfl

omit [DecidableEq d] in
/-- Helper: for the image `S` of an embedding `e : d ↪ m`, `W_read[:,S] W_write[S,:]` is the
product of the columns `e` of the read and the rows `e` of the write. -/
private theorem subProd_map {m q : Type*} [Fintype m] [DecidableEq m] (e : d ↪ m)
    (Wr : Matrix d m ℝ) (Ww : Matrix m q ℝ) :
    subProd (Finset.univ.map e) Wr Ww = Wr.submatrix id e * Ww.submatrix e id := by
  classical
  ext i j
  rw [subProd, Matrix.mul_apply, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.submatrix_apply, id_eq, mul_ite, mul_one, mul_zero,
    ite_mul, zero_mul]
  rw [Fintype.sum_ite_mem, Finset.sum_map]

/-- **Proposition 5.4 (i):** let `σ(z) - σ(-z) = c z` with `c ≠ 0`, and let every block have at
least `d` hidden units. Without normalization, for almost every choice of weights a skipless
network of vanilla `σ` blocks equals a network with invertible learned skips and the same
embedding, readout, `d` and widths. -/
theorem ae_exists_learned_skips_eq_skipless (hσ : ∀ z, σ z - σ (-z) = c * z) (hc : c ≠ 0)
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)) [μ.IsAddHaarMeasure]
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, ∃ (A : Fin L → Matrix d d ℝ)
      (θ' : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut),
      (∀ ℓ, IsUnit (A ℓ).det) ∧ θ'.E = θ.E ∧ θ'.D = θ.D ∧
      ∀ X : Matrix T dIn ℝ,
        eval (Arch.mlp σ id hid) 0 θ X = eval (Arch.mlp σ id hid) A θ' X := by
  -- `d` units `e ℓ` in every block (`d_hidden ≥ d`); `S_ℓ` is the set of these units
  have e : ∀ ℓ, d ↪ hid ℓ := fun ℓ => (Function.Embedding.nonempty_of_card_le (hhid ℓ)).some
  -- at generic weights `W_read[:,S_ℓ]` and `W_write[S_ℓ,:]` are invertible
  filter_upwards [ae_isUnit_det_submatrix μ] with θ hθ
  refine ⟨fun ℓ => c • subProd (Finset.univ.map (e ℓ)) (θ.read ℓ) (θ.write ℓ),
    θ.flipReads fun ℓ => Finset.univ.map (e ℓ), fun ℓ => ?_, rfl, rfl,
    fun X => eval_skipless_eq_learned_flipReads hσ θ _ X⟩
  -- `det (c K_ℓ) = c^d det W_read[:,S_ℓ] det W_write[S_ℓ,:]`
  dsimp only
  rw [Matrix.det_smul, subProd_map, Matrix.det_mul]
  exact ((isUnit_iff_ne_zero.2 hc).pow _).mul ((hθ.1 ℓ (e ℓ)).mul (hθ.2.2.2 ℓ (e ℓ)))

/-- Helper: the products `A_{k+1} ⋯ A_L` of a family of square matrices, with the empty product
`1` (the recursion of `skipProd`, on matrices). -/
private noncomputable def matProd {m : Type*} [Fintype m] [DecidableEq m]
    (A : Fin L → Matrix m m ℝ) : Fin (L + 1) → Matrix m m ℝ :=
  Fin.reverseInduction (motive := fun _ => Matrix m m ℝ) 1 (fun ℓ P => A ℓ * P)

private theorem matProd_last {m : Type*} [Fintype m] [DecidableEq m] (A : Fin L → Matrix m m ℝ) :
    matProd A (Fin.last L) = 1 := by
  simp [matProd]

private theorem matProd_castSucc {m : Type*} [Fintype m] [DecidableEq m]
    (A : Fin L → Matrix m m ℝ) (ℓ : Fin L) :
    matProd A ℓ.castSucc = A ℓ * matProd A ℓ.succ := by
  simp [matProd]

/-- Helper: `Λ_k = A_{k+1} ⋯ A_L` (equation (7)) as a matrix. -/
private theorem coe_skipProd {m : Type*} [Fintype m] [DecidableEq m] (G : Fin L → GL m ℝ)
    (k : Fin (L + 1)) :
    (skipProd G k : Matrix m m ℝ) = matProd (fun ℓ => (G ℓ : Matrix m m ℝ)) k := by
  induction k using Fin.reverseInduction with
  | last => rw [skipProd_last, Units.val_one, matProd_last]
  | cast ℓ ih => rw [skipProd_castSucc, Units.val_mul, matProd_castSucc, ih]

/-- Helper: `(c I)^L = r I` with `r ≠ 0` when `c ≠ 0`. -/
private theorem matProd_smul_one {m : Type*} [Fintype m] [DecidableEq m] (hc : c ≠ 0)
    (k : Fin (L + 1)) :
    ∃ r : ℝ, r ≠ 0 ∧ matProd (fun _ : Fin L => c • (1 : Matrix m m ℝ)) k = r • 1 := by
  induction k using Fin.reverseInduction with
  | last => exact ⟨1, one_ne_zero, by rw [matProd_last, one_smul]⟩
  | cast ℓ ih =>
    obtain ⟨r, hr, h⟩ := ih
    refine ⟨c * r, mul_ne_zero hc hr, ?_⟩
    rw [matProd_castSucc, h, Matrix.smul_mul, Matrix.one_mul, smul_smul]

/-- Helper: a linear functional on a finite-dimensional space is analytic. -/
private theorem analyticOnNhd_of_linear {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [FiniteDimensional ℝ P] (l : P →ₗ[ℝ] ℝ) : AnalyticOnNhd ℝ l Set.univ := by
  rw [← LinearMap.coe_toContinuousLinearMap' l]
  exact (LinearMap.toContinuousLinearMap l).analyticOnNhd _

/-- Helper: the entries of a product of two matrices with analytic entries are analytic. -/
private theorem analyticOnNhd_mul_entry {P m n p : Type*} [NormedAddCommGroup P]
    [NormedSpace ℝ P] [Fintype n] {M : P → Matrix m n ℝ} {N : P → Matrix n p ℝ}
    (hM : ∀ i j, AnalyticOnNhd ℝ (fun y => M y i j) Set.univ)
    (hN : ∀ i j, AnalyticOnNhd ℝ (fun y => N y i j) Set.univ) (i : m) (j : p) :
    AnalyticOnNhd ℝ (fun y => (M y * N y) i j) Set.univ := by
  simp only [Matrix.mul_apply]
  exact Finset.analyticOnNhd_fun_sum _ fun k _ => (hM i k).mul (hN k j)

/-- Helper: the entries of `A_{k+1} ⋯ A_L` are analytic if those of every `A_ℓ` are. -/
private theorem analyticOnNhd_matProd {P m : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [Fintype m] [DecidableEq m] {A : P → Fin L → Matrix m m ℝ}
    (hA : ∀ ℓ i j, AnalyticOnNhd ℝ (fun y => A y ℓ i j) Set.univ) (k : Fin (L + 1)) :
    ∀ i j, AnalyticOnNhd ℝ (fun y => matProd (A y) k i j) Set.univ := by
  induction k using Fin.reverseInduction with
  | last =>
    intro i j
    simp only [matProd_last]
    exact analyticOnNhd_const
  | cast ℓ ih =>
    intro i j
    simp only [matProd_castSucc]
    exact analyticOnNhd_mul_entry (hA ℓ) ih i j

/-- **Proposition 5.4 (ii):** under the same hypotheses, for almost every choice of weights the
skipless network equals a residual network with the same readout, `d` and widths, whose embedding
`E'` has `E' D ≠ 0` (by Theorem 3.2 (i) of the skips paper, `eval_learned_eq_residual`; the
embedding is `c^L E K_1 ⋯ K_L`). -/
theorem ae_exists_residual_eq_skipless [Nonempty d] [Nonempty dIn] [Nonempty dOut]
    (hσ : ∀ z, σ z - σ (-z) = c * z) (hc : c ≠ 0)
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)) [μ.IsAddHaarMeasure]
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, ∃ θ' : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut,
      θ'.D = θ.D ∧ θ'.E * θ'.D ≠ 0 ∧
      ∀ X : Matrix T dIn ℝ,
        eval (Arch.mlp σ id hid) 0 θ X = eval (Arch.mlp σ id hid) 1 θ' X := by
  -- `d` units `e ℓ` in every block; `S_ℓ` is the set of these units
  have e : ∀ ℓ, d ↪ hid ℓ := fun ℓ => (Function.Embedding.nonempty_of_card_le (hhid ℓ)).some
  -- the learned skips `A_ℓ = c K_ℓ`, `K_ℓ = W_read[:,S_ℓ] W_write[S_ℓ,:]`, as functions of `θ`
  let K : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut → Fin L → Matrix d d ℝ :=
    fun θ ℓ => c • ((θ.read ℓ).submatrix id (e ℓ) * (θ.write ℓ).submatrix (e ℓ) id)
  obtain ⟨a⟩ := ‹Nonempty dIn›
  obtain ⟨o⟩ := ‹Nonempty dOut›
  obtain ⟨k₀⟩ := ‹Nonempty d›
  -- the entry `(a, o)` of `E A_1 ⋯ A_L D` is a polynomial in the weights
  have hK : ∀ ℓ i j, AnalyticOnNhd ℝ
      (fun θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut => K θ ℓ i j) Set.univ := by
    intro ℓ i j
    have hR : ∀ i j, AnalyticOnNhd ℝ
        (fun θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut =>
          (θ.read ℓ).submatrix id (e ℓ) i j) Set.univ := fun i j =>
      analyticOnNhd_of_linear
        { toFun := fun θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut =>
            θ.read ℓ i (e ℓ j)
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
    have hW : ∀ i j, AnalyticOnNhd ℝ
        (fun θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut =>
          (θ.write ℓ).submatrix (e ℓ) id i j) Set.univ := fun i j =>
      analyticOnNhd_of_linear
        { toFun := fun θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut =>
            θ.write ℓ (e ℓ i) j
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
    exact analyticOnNhd_const.mul (analyticOnNhd_mul_entry hR hW i j)
  have hg : AnalyticOnNhd ℝ (fun θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut =>
      (θ.E * matProd (K θ) 0 * θ.D) a o) Set.univ := by
    refine analyticOnNhd_mul_entry (fun i j => analyticOnNhd_mul_entry (fun i j => ?_)
      (analyticOnNhd_matProd hK 0) i j) (fun i j => ?_) a o
    · exact analyticOnNhd_of_linear
        { toFun := fun θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut => θ.E i j
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
    · exact analyticOnNhd_of_linear
        { toFun := fun θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut => θ.D i j
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
  -- it is not identically zero: at the reads `R ℓ` with `R ℓ i j = [e ℓ i = j]`, the writes
  -- `(R ℓ)ᵀ`, and `E`, `D` with the one entry `1` at `(a, k₀)` and `(k₀, o)`, every `K_ℓ = I`
  have hne : ∃ θ₀ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut,
      (θ₀.E * matProd (K θ₀) 0 * θ₀.D) a o ≠ 0 := by
    classical
    let R : ∀ ℓ, Matrix d (hid ℓ) ℝ := fun ℓ => Matrix.of fun i j => if e ℓ i = j then 1 else 0
    have hR : ∀ ℓ, (R ℓ).submatrix id (e ℓ) = 1 := fun ℓ => by
      ext i i'
      simp [R, Matrix.one_apply, (e ℓ).injective.eq_iff]
    let θ₀ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut :=
      ⟨Matrix.single a k₀ 1, R, fun ℓ => (R ℓ)ᵀ, Matrix.single k₀ o 1⟩
    have hK₀ : K θ₀ = fun _ => c • 1 := by
      funext ℓ
      show c • ((R ℓ).submatrix id (e ℓ) * ((R ℓ)ᵀ).submatrix (e ℓ) id) = c • 1
      rw [← Matrix.transpose_submatrix, hR, Matrix.transpose_one, Matrix.one_mul]
    obtain ⟨r, hr, hr'⟩ := matProd_smul_one (m := d) hc (0 : Fin (L + 1))
    refine ⟨θ₀, ?_⟩
    show (Matrix.single a k₀ (1 : ℝ) * matProd (K θ₀) 0 * Matrix.single k₀ o (1 : ℝ)) a o ≠ 0
    rw [hK₀, hr', Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.smul_apply,
      Matrix.single_mul_single_same, Matrix.single_apply_same, smul_eq_mul, mul_one, mul_one]
    exact hr
  -- so it is nonzero at almost every choice of weights
  have hgen : ∀ᵐ θ ∂μ, (θ.E * matProd (K θ) 0 * θ.D) a o ≠ 0 := by
    rw [ae_iff]
    simpa only [ne_eq, not_not] using measure_zeroSet_of_analytic μ hg hne
  filter_upwards [ae_isUnit_det_submatrix μ, hgen] with θ hθ hθ'
  -- the learned skips `A_ℓ = c K_ℓ` are invertible: `det A_ℓ = c^d det W_read[:,S_ℓ] det …`
  have hA : ∀ ℓ, IsUnit (K θ ℓ).det := fun ℓ => by
    show IsUnit (c • ((θ.read ℓ).submatrix id (e ℓ) * (θ.write ℓ).submatrix (e ℓ) id)).det
    rw [Matrix.det_smul, Matrix.det_mul]
    exact ((isUnit_iff_ne_zero.2 hc).pow _).mul ((hθ.1 ℓ (e ℓ)).mul (hθ.2.2.2 ℓ (e ℓ)))
  let G : Fin L → GL d ℝ := fun ℓ => Matrix.GeneralLinearGroup.mk'' (K θ ℓ) (hA ℓ)
  -- Proposition 5.4 (i): the skipless network is the network with the learned skips `A_ℓ`
  have hlearn : ∀ X, eval (Arch.mlp σ id hid) 0 θ X
      = eval (Arch.mlp σ id hid) (fun ℓ => (G ℓ : Matrix d d ℝ))
          (θ.flipReads fun ℓ => Finset.univ.map (e ℓ)) X := by
    intro X
    rw [eval_skipless_eq_learned_flipReads hσ θ (fun ℓ => Finset.univ.map (e ℓ)) X]
    congr 1
    funext ℓ
    show c • subProd (Finset.univ.map (e ℓ)) (θ.read ℓ) (θ.write ℓ) = K θ ℓ
    rw [subProd_map]
  -- Theorem 3.2 (i) of the skips paper: it equals the residual network with the embedding
  -- `E Λ_0 = E A_1 ⋯ A_L` and the readout `D`
  refine ⟨(θ.flipReads fun ℓ => Finset.univ.map (e ℓ)).cob (skipProd G) (skipProd G),
    cob_skipProd_D _ G, ?_, fun X => (hlearn X).trans (eval_learned_eq_residual _ X rfl G)⟩
  rw [cob_skipProd_D]
  show θ.E * (skipProd G 0 : Matrix d d ℝ) * θ.D ≠ 0
  rw [coe_skipProd]
  exact fun h0 => hθ' (congrFun (congrFun h0 a) o)

end Skips
