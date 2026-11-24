import SkipsLean.Absorb.Networks
import SkipsLean.Absorb.SameWidth
import SkipsLean.Dimension.RescalingMlp

/-!
# The first block of a skipless network needs `2 d` hidden units

Paper ("Can an MLP Absorb Its Skip Connection Exactly?"): Theorem 4.5. "Consider networks of ReLU
blocks, or of GELU blocks, without normalization. For almost every choice of weights, a residual
network with model dimension `d` equals no skipless network whose first block has fewer than
`2 d` hidden units, whatever its depth and its other widths."

The proof (Appendix A) has three parts, stated here in this order:

* the conditions on the weights of the residual network that the proof uses (`FirstBlockGeneric`),
  and that they hold for almost every choice of weights;
* the case of ReLU under these conditions: near a generic input the residual network is linear of
  rank `d`, while a skipless network whose first block has fewer than `2 d` hidden units is
  constant, near that input or near its negative, along a subspace of dimension greater than
  `d_in - d`;
* GELU: along rays, `F(t X) / t` of a GELU network tends to the output at `X` of the ReLU network
  with the same weights, with or without skips, so an equality of two GELU networks gives the
  equality of the two ReLU networks.

A skipless network that is compared with the residual one has its own model dimension `d'`, depth
`L' + 1` and widths `hid'`; only its first width `hid' 0` is constrained. Two networks are equal
if they have the same output at every input `X` (a matrix with one row per token).
-/

namespace Skips

open Matrix MeasureTheory Filter
open scoped Matrix.Norms.Elementwise Topology

variable {T dIn dOut : Type*} {d : Type} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d]
  [Fintype dIn] [Fintype dOut]
variable {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)] [∀ ℓ, DecidableEq (hid ℓ)] {σ : ℝ → ℝ}

/-- The same weights, read as the parameters of the network with another activation. -/
def Params.withActivation (σ' : ℝ → ℝ) {χ : Matrix T d ℝ → Matrix T d ℝ}
    (θ : Params (Arch.mlp (T := T) (d := d) σ χ hid) dIn dOut) :
    Params (Arch.mlp (T := T) (d := d) σ' χ hid) dIn dOut where
  E := θ.E
  read := θ.read
  write := θ.write
  D := θ.D

/-- **The conditions of the proof of Theorem 4.5** on the weights of the residual network: `E` and
`D` have rank `d`, no read of a hidden unit vanishes, and `I + W_read[:,S] W_write[S,:]` is
invertible for every block and every set `S` of its hidden units. They do not involve the
activation. -/
structure FirstBlockGeneric (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) :
    Prop where
  rank_E : θ.E.rank = Fintype.card d
  rank_D : θ.D.rank = Fintype.card d
  /-- no read column of a hidden unit vanishes -/
  read_ne_zero : ∀ ℓ (i : hid ℓ), (θ.read ℓ)ᵀ i ≠ 0
  /-- `I + W_read[:,S] W_write[S,:]` is invertible for every block and every set `S` -/
  isUnit_det : ∀ ℓ (S : Finset (hid ℓ)),
    IsUnit ((1 : Matrix d d ℝ) + subProd S (θ.read ℓ) (θ.write ℓ)).det

/-! ### The conditions hold for almost every choice of weights -/

/-- A matrix with `d` columns has rank `d` if some `d` of its rows form an invertible matrix. -/
private theorem rank_eq_of_isUnit_det_rows {m : Type*} [Fintype m] (M : Matrix m d ℝ)
    (ρ : d ↪ m) (h : IsUnit (M.submatrix ρ id).det) : M.rank = Fintype.card d :=
  le_antisymm (Matrix.rank_le_card_width M)
    ((Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).2 h)).symm.le.trans
      (Matrix.rank_submatrix_le M ρ id))

omit [Fintype T] in
/-- At generic weights `I + W_read^ℓ[:,S] W_write^ℓ[S,:]` is invertible for every block and every
set `S` of its units: its determinant is a polynomial in the weights, equal to `1` when the weights
vanish. -/
private theorem ae_isUnit_det_one_add_subProd
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)) [μ.IsAddHaarMeasure] :
    ∀ᵐ θ ∂μ, ∀ ℓ (S : Finset (hid ℓ)),
      IsUnit ((1 : Matrix d d ℝ) + subProd S (θ.read ℓ) (θ.write ℓ)).det := by
  refine ae_all_iff.2 fun ℓ => ae_all_iff.2 fun S => ?_
  -- `θ ↦ W_read^ℓ Π_S` is linear in the parameters
  let F : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut →ₗ[ℝ] Matrix d (hid ℓ) ℝ :=
    { toFun := fun θ => θ.read ℓ * Matrix.diagonal (fun j => if j ∈ S then (1 : ℝ) else 0)
      map_add' := fun _ _ => Matrix.add_mul _ _ _
      map_smul' := fun _ _ => Matrix.smul_mul _ _ _ }
  -- the entries of `I + W_read Π_S W_write` are polynomials in the parameters
  have he : ∀ a b, AnalyticOnNhd ℝ
      (fun θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut =>
        ((1 : Matrix d d ℝ) + subProd S (θ.read ℓ) (θ.write ℓ)) a b) Set.univ := by
    intro a b
    simp only [Matrix.add_apply]
    exact analyticOnNhd_const.add (analyticOnNhd_mul_apply F
      (Params.linWrite (A := Arch.mlp (T := T) (d := d) σ id hid) (dIn := dIn) (dOut := dOut) ℓ)
      a b)
  -- so is the determinant, a signed sum of products of entries
  have hg : AnalyticOnNhd ℝ
      (fun θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut =>
        ((1 : Matrix d d ℝ) + subProd S (θ.read ℓ) (θ.write ℓ)).det) Set.univ := by
    simp only [Matrix.det_apply']
    exact Finset.analyticOnNhd_fun_sum _ fun p _ => analyticOnNhd_const.mul
      (Finset.analyticOnNhd_fun_prod _ fun i _ => he (p i) i)
  -- at the zero parameters it is `det 1 = 1`
  have h0 : ((1 : Matrix d d ℝ) + subProd S
      ((0 : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut).read ℓ)
      ((0 : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut).write ℓ)).det ≠ 0 := by
    simp only [Params.zero_read, Params.zero_write, subProd, Matrix.zero_mul, add_zero,
      Matrix.det_one]
    exact one_ne_zero
  filter_upwards [ae_ne_zero_of_analytic μ hg ⟨0, h0⟩] with θ hθ
  exact isUnit_iff_ne_zero.2 hθ

/-- The conditions of the proof hold for almost every choice of weights (`d_in, d_out ≥ d ≥ 1`):
each is the nonvanishing of polynomials in the weights that do not vanish identically. -/
theorem ae_firstBlockGeneric [Nonempty d]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)) [μ.IsAddHaarMeasure]
    (hdIn : Fintype.card d ≤ Fintype.card dIn) (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, FirstBlockGeneric θ := by
  -- `d` rows of `E` and `d` columns of `D`, invertible at generic weights
  obtain ⟨ρ⟩ := Function.Embedding.nonempty_of_card_le hdIn
  obtain ⟨c⟩ := Function.Embedding.nonempty_of_card_le hdOut
  filter_upwards [ae_isUnit_det_submatrix μ, ae_read_col_ne_zero μ,
    ae_isUnit_det_one_add_subProd μ] with θ h1 h2 h3
  exact ⟨rank_eq_of_isUnit_det_rows θ.E ρ (h1.2.2.1 ρ),
    rank_eq_card_of_isUnit_det θ.D c (h1.2.1 c), fun ℓ i => h2 ℓ i, h3⟩

/-! ### ReLU: the residual network on one row -/

/-- ReLU is continuous. -/
private theorem continuous_relu' : Continuous relu := by
  show Continuous fun z : ℝ => max z 0
  exact continuous_id.max continuous_const

/-- **Fewer conditions than unknowns** (a copy of `exists_ne_zero_forall_dotProduct_eq_zero` of
`Absorb/FewerUnits.lean`, which this file does not import). -/
private theorem exists_ne_zero_forall_dotProduct_eq_zero' {n ι : Type*} [Fintype n] [Fintype ι]
    (u : ι → n → ℝ) (h : Fintype.card ι < Fintype.card n) :
    ∃ x : n → ℝ, x ≠ 0 ∧ ∀ k, x ⬝ᵥ u k = 0 := by
  have hli : ¬ LinearIndependent ℝ (fun a : n => fun k : ι => u k a) := fun hli => by
    have h1 := hli.fintype_card_le_finrank
    rw [Module.finrank_fintype_fun_eq_card] at h1
    omega
  -- a vanishing combination `∑ₐ g_a (u k a)_k = 0` with `g ≠ 0`; take `x = g`
  obtain ⟨g, hg, a, ha⟩ := Fintype.not_linearIndependent_iff.1 hli
  refine ⟨g, fun h0 => ha (congrFun h0 a), fun k => ?_⟩
  have h1 := congrFun hg k
  simpa only [dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using h1

section ReLU

variable (θ : Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut)

/-- The hidden states of the residual ReLU network on one row `x`. -/
private noncomputable def hrow (x : dIn → ℝ) : Fin (L + 1) → d → ℝ :=
  Fin.induction (motive := fun _ => d → ℝ) (x ᵥ* θ.E)
    (fun ℓ h => h + vanillaBlock relu (θ.read ℓ) (θ.write ℓ) h)

omit [Fintype T] [DecidableEq d] [Fintype dOut] [∀ ℓ, DecidableEq (hid ℓ)] in
private theorem hrow_zero (x : dIn → ℝ) : hrow θ x 0 = x ᵥ* θ.E := by
  simp [hrow]

omit [Fintype T] [DecidableEq d] [Fintype dOut] [∀ ℓ, DecidableEq (hid ℓ)] in
private theorem hrow_succ (x : dIn → ℝ) (ℓ : Fin L) :
    hrow θ x ℓ.succ = hrow θ x ℓ.castSucc
      + vanillaBlock relu (θ.read ℓ) (θ.write ℓ) (hrow θ x ℓ.castSucc) := by
  simp [hrow]

omit [Fintype T] [Fintype dOut] [∀ ℓ, DecidableEq (hid ℓ)] in
/-- A row of the hidden states of the residual network is the hidden state of the row. -/
private theorem hidden_row (X : Matrix T dIn ℝ) (t : T) (ℓ : Fin (L + 1)) :
    hidden (Arch.mlp relu id hid) 1 θ X ℓ t = hrow θ (X t) ℓ := by
  induction ℓ using Fin.induction with
  | zero => rw [hidden_zero, hrow_zero, Matrix.mul_apply_eq_vecMul]
  | succ ℓ ih =>
    rw [hidden_succ, hrow_succ, ← ih]
    show (hidden (Arch.mlp relu id hid) 1 θ X ℓ.castSucc * (1 : Matrix d d ℝ)
      + (hidden (Arch.mlp relu id hid) 1 θ X ℓ.castSucc * θ.read ℓ).map relu * θ.write ℓ) t = _
    rw [Matrix.mul_one]
    exact congrArg₂ (· + ·) rfl (map_mul_mul_row relu (θ.read ℓ) (θ.write ℓ) _ t)

omit [Fintype T] [Fintype dOut] [∀ ℓ, DecidableEq (hid ℓ)] in
/-- A row of the output of the residual network. -/
private theorem eval_row (X : Matrix T dIn ℝ) (t : T) :
    eval (Arch.mlp relu id hid) 1 θ X t = hrow θ (X t) (Fin.last L) ᵥ* θ.D := by
  show (hidden (Arch.mlp relu id hid) 1 θ X (Fin.last L) * θ.D) t = _
  rw [Matrix.mul_apply_eq_vecMul, hidden_row]

/-- The active sets: unit `i` of block `ℓ` is active at `x` if its argument is positive. -/
private noncomputable def pat (x : dIn → ℝ) : ∀ ℓ : Fin L, Finset (hid ℓ) :=
  fun ℓ => Finset.univ.filter fun i => 0 < (hrow θ x ℓ.castSucc ᵥ* θ.read ℓ) i

omit [Fintype T] [DecidableEq d] [Fintype dOut] [∀ ℓ, DecidableEq (hid ℓ)] in
private theorem mem_pat (x : dIn → ℝ) (ℓ : Fin L) (i : hid ℓ) :
    i ∈ pat θ x ℓ ↔ 0 < (hrow θ x ℓ.castSucc ᵥ* θ.read ℓ) i := by
  simp [pat]

/-- `Θ_ℓ = ∏_{k < ℓ} (I + W_read^k[:,P_k] W_write^k[P_k,:])` for the active sets `P`. -/
private noncomputable def theta (P : ∀ ℓ : Fin L, Finset (hid ℓ)) : Fin (L + 1) → Matrix d d ℝ :=
  Fin.induction (motive := fun _ => Matrix d d ℝ) 1
    (fun ℓ M => M * (1 + subProd (P ℓ) (θ.read ℓ) (θ.write ℓ)))

omit [Fintype T] [Fintype dIn] [Fintype dOut] in
private theorem theta_zero (P : ∀ ℓ : Fin L, Finset (hid ℓ)) : theta θ P 0 = 1 := by
  simp [theta]

omit [Fintype T] [Fintype dIn] [Fintype dOut] in
private theorem theta_succ (P : ∀ ℓ : Fin L, Finset (hid ℓ)) (ℓ : Fin L) :
    theta θ P ℓ.succ = theta θ P ℓ.castSucc * (1 + subProd (P ℓ) (θ.read ℓ) (θ.write ℓ)) := by
  simp [theta]

omit [Fintype T] [Fintype dIn] in
/-- Under `FirstBlockGeneric`, every `Θ_ℓ` is invertible. -/
private theorem isUnit_det_theta (hθ : FirstBlockGeneric θ) (P : ∀ ℓ : Fin L, Finset (hid ℓ))
    (ℓ : Fin (L + 1)) : IsUnit (theta θ P ℓ).det := by
  induction ℓ using Fin.induction with
  | zero => rw [theta_zero, Matrix.det_one]; exact isUnit_one
  | succ ℓ ih => rw [theta_succ, Matrix.det_mul]; exact ih.mul (hθ.isUnit_det ℓ (P ℓ))

/-- A ReLU block on a row `h` is `h W_read[:,S] W_write[S,:]` for the set `S` of its active
units. -/
private theorem vanillaBlock_relu_eq {p q m : Type*} [Fintype p] [Fintype m] [DecidableEq m]
    (Wr : Matrix p m ℝ) (Ww : Matrix m q ℝ) (h : p → ℝ) (S : Finset m)
    (hS : ∀ i, i ∈ S ↔ 0 < (h ᵥ* Wr) i) :
    vanillaBlock relu Wr Ww h = h ᵥ* subProd S Wr Ww := by
  have hd : (h ᵥ* Wr) ᵥ* Matrix.diagonal (fun j => if j ∈ S then (1 : ℝ) else 0)
      = fun i => relu ((h ᵥ* Wr) i) := by
    funext i
    rw [Matrix.vecMul_diagonal]
    by_cases hi : 0 < (h ᵥ* Wr) i
    · rw [ite_eq_left ((hS i).2 hi), mul_one, relu, max_eq_left hi.le]
    · rw [ite_eq_right (fun h' => hi ((hS i).1 h')), mul_zero, relu,
        max_eq_right (not_lt.1 hi)]
  rw [subProd, ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul, hd]
  rfl

omit [Fintype T] [Fintype dOut] in
/-- **Local linearity.** At every row `x`, the residual network is `x ↦ x E Θ` up to block `ℓ`,
with `Θ` built from the active sets at `x`. -/
private theorem hrow_eq (x : dIn → ℝ) (ℓ : Fin (L + 1)) :
    hrow θ x ℓ = x ᵥ* (θ.E * theta θ (pat θ x) ℓ) := by
  induction ℓ using Fin.induction with
  | zero => rw [hrow_zero, theta_zero, Matrix.mul_one]
  | succ ℓ ih =>
    rw [hrow_succ, vanillaBlock_relu_eq _ _ _ (pat θ x ℓ) (mem_pat θ x ℓ), theta_succ,
      ← Matrix.mul_assoc, ← Matrix.vecMul_vecMul, ← ih, Matrix.vecMul_add, Matrix.vecMul_one]

omit [Fintype T] [DecidableEq d] [Fintype dOut] [∀ ℓ, DecidableEq (hid ℓ)] in
/-- The hidden states depend continuously on the row. -/
private theorem continuous_hrow (ℓ : Fin (L + 1)) : Continuous fun x : dIn → ℝ => hrow θ x ℓ := by
  induction ℓ using Fin.induction with
  | zero =>
    simp only [hrow_zero]
    exact continuous_id.matrix_vecMul continuous_const
  | succ ℓ ih =>
    simp only [hrow_succ]
    refine ih.add ?_
    unfold vanillaBlock
    refine Continuous.matrix_vecMul (continuous_pi fun i => ?_) continuous_const
    exact continuous_relu'.comp
      ((continuous_apply i).comp (ih.matrix_vecMul continuous_const))

omit [Fintype T] [DecidableEq d] [Fintype dOut] [∀ ℓ, DecidableEq (hid ℓ)] in
/-- **The active sets do not change near a row at which no unit switches.** -/
private theorem eventually_pat_eq (x₀ u : dIn → ℝ)
    (hres : ∀ k (i : hid k), (hrow θ x₀ k.castSucc ᵥ* θ.read k) i ≠ 0) :
    ∀ᶠ s in 𝓝 (0 : ℝ), pat θ (x₀ + s • u) = pat θ x₀ := by
  have h : ∀ k (i : hid k), ∀ᶠ s in 𝓝 (0 : ℝ),
      (0 < (hrow θ (x₀ + s • u) k.castSucc ᵥ* θ.read k) i
        ↔ 0 < (hrow θ x₀ k.castSucc ᵥ* θ.read k) i) := by
    intro k i
    -- the argument of the unit is continuous in `s`
    have hc : Continuous fun s : ℝ => (hrow θ (x₀ + s • u) k.castSucc ᵥ* θ.read k) i :=
      (continuous_apply i).comp
        (((continuous_hrow θ k.castSucc).comp (continuous_const.add
          (continuous_id.smul continuous_const))).matrix_vecMul continuous_const)
    have ht : Tendsto (fun s : ℝ => (hrow θ (x₀ + s • u) k.castSucc ᵥ* θ.read k) i) (𝓝 0)
        (𝓝 ((hrow θ x₀ k.castSucc ᵥ* θ.read k) i)) := by
      have := hc.tendsto 0
      simpa only [zero_smul, add_zero] using this
    rcases (hres k i).lt_or_gt with hneg | hpos
    · filter_upwards [ht.eventually (eventually_lt_nhds hneg)] with s hs
      exact ⟨fun h1 => absurd (h1.trans hs) (lt_irrefl _), fun h1 => absurd (h1.trans hneg)
        (lt_irrefl _)⟩
    · filter_upwards [ht.eventually (eventually_gt_nhds hpos)] with s hs
      exact ⟨fun _ => hpos, fun _ => hs⟩
  have hall : ∀ᶠ s in 𝓝 (0 : ℝ), ∀ k (i : hid k),
      (0 < (hrow θ (x₀ + s • u) k.castSucc ᵥ* θ.read k) i
        ↔ 0 < (hrow θ x₀ k.castSucc ᵥ* θ.read k) i) :=
    Filter.eventually_all.2 fun k => Filter.eventually_all.2 fun i => h k i
  filter_upwards [hall] with s hs
  funext k
  ext i
  rw [mem_pat, mem_pat]
  exact hs k i

/-- The vectors of the hyperplanes on which a unit can switch: the argument of unit `i` of block
`k` at `x` is `x ⬝ (E Θ_k w_i)` when the active sets at `x` are `P`. -/
private noncomputable def resVec (P : ∀ ℓ : Fin L, Finset (hid ℓ)) (k : Fin L) (i : hid k) :
    dIn → ℝ :=
  fun a => (θ.E * theta θ P k.castSucc * θ.read k) a i

omit [Fintype T] [Fintype dOut] in
private theorem preact_eq (x : dIn → ℝ) (k : Fin L) (i : hid k) :
    (hrow θ x k.castSucc ᵥ* θ.read k) i = x ⬝ᵥ resVec θ (pat θ x) k i := by
  rw [hrow_eq, Matrix.vecMul_vecMul]
  rfl

/-- The vectors `E Θ_k w_i` are nonzero: `E` has a left inverse, `Θ_k` is invertible and
`w_i ≠ 0`. -/
private theorem resVec_ne_zero (hθ : FirstBlockGeneric θ) {B : Matrix d dIn ℝ}
    (hB : B * θ.E = 1) (P : ∀ ℓ : Fin L, Finset (hid ℓ)) (k : Fin L) (i : hid k) :
    resVec θ P k i ≠ 0 := by
  intro h0
  apply hθ.read_ne_zero k i
  have h1 : resVec θ P k i = θ.E *ᵥ (theta θ P k.castSucc *ᵥ (θ.read k)ᵀ i) := by
    rw [Matrix.mulVec_mulVec]
    rfl
  have hu := isUnit_det_theta θ hθ P k.castSucc
  calc (θ.read k)ᵀ i
      = ((theta θ P k.castSucc)⁻¹ * theta θ P k.castSucc) *ᵥ (θ.read k)ᵀ i := by
        rw [Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]
    _ = (theta θ P k.castSucc)⁻¹ *ᵥ ((B * θ.E) *ᵥ (theta θ P k.castSucc *ᵥ (θ.read k)ᵀ i)) := by
        rw [hB, Matrix.one_mulVec, Matrix.mulVec_mulVec]
    _ = 0 := by
        rw [← Matrix.mulVec_mulVec, ← h1, h0, Matrix.mulVec_zero, Matrix.mulVec_zero]

end ReLU

/-! ### The skipless network depends on the input only through its first block -/

omit [Fintype T] [Fintype dOut] [DecidableEq d] [Fintype d] in
private theorem eval_skipless_congr {σ : ℝ → ℝ} {L' : ℕ} {d' : Type*} [Fintype d']
    {hid' : Fin (L' + 1) → Type} [∀ ℓ, Fintype (hid' ℓ)]
    (θ' : Params (Arch.mlp (T := T) (d := d') σ id hid') dIn dOut) {X₁ X₂ : Matrix T dIn ℝ}
    (h : (X₁ * (θ'.E * θ'.read 0)).map σ = (X₂ * (θ'.E * θ'.read 0)).map σ) :
    eval (Arch.mlp σ id hid') 0 θ' X₁ = eval (Arch.mlp σ id hid') 0 θ' X₂ := by
  have hk : ∀ k : Fin (L' + 1), hidden (Arch.mlp σ id hid') 0 θ' X₁ k.succ
      = hidden (Arch.mlp σ id hid') 0 θ' X₂ k.succ := by
    intro k
    induction k using Fin.induction with
    | zero =>
      rw [hidden_succ, hidden_succ, Fin.castSucc_zero, hidden_zero, hidden_zero]
      show X₁ * θ'.E * (0 : Matrix d' d' ℝ) + (X₁ * θ'.E * θ'.read 0).map σ * θ'.write 0
        = X₂ * θ'.E * (0 : Matrix d' d' ℝ) + (X₂ * θ'.E * θ'.read 0).map σ * θ'.write 0
      rw [Matrix.mul_assoc X₁ θ'.E (θ'.read 0), Matrix.mul_assoc X₂ θ'.E (θ'.read 0), h,
        Matrix.mul_zero, Matrix.mul_zero]
    | succ k ih =>
      rw [hidden_succ, hidden_succ, ← Fin.succ_castSucc, ih]
  unfold eval
  rw [← Fin.succ_last, hk]

/-! ### ReLU: the argument at a generic row -/

/-- **The heart of the proof for ReLU.** Let `x₀` be a row off the hyperplanes of the residual
network and off those of the first block of the skipless one, at which fewer than `d` units of
the first skipless block are active. Then the two networks differ. -/
private theorem false_of_card_active_lt [Nonempty T]
    (θ : Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut) (hθ : FirstBlockGeneric θ)
    {L' : ℕ} {d' : Type*} [Fintype d'] {hid' : Fin (L' + 1) → Type} [∀ ℓ, Fintype (hid' ℓ)]
    (θ' : Params (Arch.mlp (T := T) (d := d') relu id hid') dIn dOut)
    (hall : ∀ X : Matrix T dIn ℝ,
      eval (Arch.mlp relu id hid) 1 θ X = eval (Arch.mlp relu id hid') 0 θ' X)
    (x₀ : dIn → ℝ) (hres : ∀ P k i, x₀ ⬝ᵥ resVec θ P k i ≠ 0)
    (ha : ∀ j : hid' 0, (fun b => (θ'.E * θ'.read 0) b j) ≠ 0 →
      x₀ ⬝ᵥ (fun b => (θ'.E * θ'.read 0) b j) ≠ 0)
    (hcard : (Finset.univ.filter fun j : hid' 0 =>
      0 < x₀ ⬝ᵥ (fun b => (θ'.E * θ'.read 0) b j)).card < Fintype.card d) : False := by
  classical
  obtain ⟨t₀⟩ := ‹Nonempty T›
  -- the reads `a_j = E' w'_j` of the first skipless block, and the units active at `x₀`
  obtain ⟨a, ha_def⟩ : ∃ a : hid' 0 → dIn → ℝ, a = fun j b => (θ'.E * θ'.read 0) b j :=
    ⟨_, rfl⟩
  obtain ⟨Pp, hPp⟩ : ∃ Pp : Finset (hid' 0), Pp = Finset.univ.filter fun j : hid' 0 =>
      0 < x₀ ⬝ᵥ (fun b => (θ'.E * θ'.read 0) b j) := ⟨_, rfl⟩
  rw [← hPp] at hcard
  have ha' : ∀ j, a j ≠ 0 → x₀ ⬝ᵥ a j ≠ 0 := by subst ha_def; exact ha
  have hPp' : ∀ j, j ∈ Pp ↔ 0 < x₀ ⬝ᵥ a j := by
    subst ha_def hPp
    intro j
    rw [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ j, h⟩⟩
  -- a left inverse of `E` and a right inverse of `D`
  obtain ⟨B, hB⟩ : ∃ B : Matrix d dIn ℝ, B * θ.E = 1 :=
    Matrix.vecMul_surjective_iff_exists_left_inverse.1
      (Matrix.vecMul_surjective_iff_rank_eq_card.2 hθ.rank_E)
  obtain ⟨R, hR⟩ : ∃ R : Matrix dOut d ℝ, θ.D * R = 1 :=
    Matrix.mulVec_surjective_iff_exists_right_inverse.1
      (Matrix.mulVec_surjective_iff_rank_eq_card.2 hθ.rank_D)
  -- fewer than `d` conditions: some `y ≠ 0` has `y ⬝ (B a_j) = 0` for the active units `j`
  obtain ⟨y, hy0, hy⟩ := exists_ne_zero_forall_dotProduct_eq_zero'
    (fun j : Pp => B *ᵥ a j) (by rwa [Fintype.card_coe])
  -- the direction `u = y B`: `u a_j = 0` for the active units, and `u E = y`
  obtain ⟨u, hu_def⟩ : ∃ u : dIn → ℝ, u = y ᵥ* B := ⟨_, rfl⟩
  have hu : ∀ j ∈ Pp, u ⬝ᵥ a j = 0 := fun j hj => by
    rw [hu_def, ← Matrix.dotProduct_mulVec]
    exact hy ⟨j, hj⟩
  have huE : u ᵥ* θ.E = y := by rw [hu_def, Matrix.vecMul_vecMul, hB, Matrix.vecMul_one]
  -- the residual network changes along `u`: `u E Θ D ≠ 0`
  set P := pat θ x₀ with hP
  have hΘ := isUnit_det_theta θ hθ P (Fin.last L)
  have huM : u ᵥ* (θ.E * theta θ P (Fin.last L)) ᵥ* θ.D ≠ 0 := by
    intro h0
    apply hy0
    have h1 : y ᵥ* theta θ P (Fin.last L) = 0 := by
      have h2 : u ᵥ* (θ.E * theta θ P (Fin.last L)) ᵥ* θ.D ᵥ* R = 0 := by
        rw [h0, Matrix.zero_vecMul]
      rw [Matrix.vecMul_vecMul _ θ.D R, hR, Matrix.vecMul_one, ← Matrix.vecMul_vecMul, huE] at h2
      exact h2
    calc y = y ᵥ* (theta θ P (Fin.last L) * (theta θ P (Fin.last L))⁻¹) := by
          rw [Matrix.mul_nonsing_inv _ hΘ, Matrix.vecMul_one]
      _ = 0 := by rw [← Matrix.vecMul_vecMul, h1, Matrix.zero_vecMul]
  -- for small `s`, the active sets of the residual network at `x₀ + s u` are those at `x₀`
  have hev1 := eventually_pat_eq θ x₀ u (fun k i => by rw [preact_eq]; exact hres _ k i)
  -- and the first block of the skipless network has the same output at `x₀ + s u` and at `x₀`
  have hev2 : ∀ᶠ s in 𝓝 (0 : ℝ), ∀ j, relu ((x₀ + s • u) ⬝ᵥ a j) = relu (x₀ ⬝ᵥ a j) := by
    refine Filter.eventually_all.2 fun j => ?_
    by_cases huj : u ⬝ᵥ a j = 0
    · exact Filter.Eventually.of_forall fun s => by
        rw [add_dotProduct, smul_dotProduct, huj, smul_zero, add_zero]
    · -- `j` is inactive at `x₀`, with `x₀ a_j < 0`
      have hj : j ∉ Pp := fun hj => huj (hu j hj)
      have haj : a j ≠ 0 := fun h => huj (by rw [h, dotProduct_zero])
      have hneg : x₀ ⬝ᵥ a j < 0 := by
        rw [hPp', not_lt] at hj
        exact lt_of_le_of_ne hj (ha' j haj)
      have ht : Tendsto (fun s : ℝ => (x₀ + s • u) ⬝ᵥ a j) (𝓝 0) (𝓝 (x₀ ⬝ᵥ a j)) := by
        have hc : Continuous fun s : ℝ => (x₀ + s • u) ⬝ᵥ a j := by
          simp only [add_dotProduct, smul_dotProduct, smul_eq_mul]
          exact continuous_const.add (continuous_id.mul continuous_const)
        simpa only [zero_smul, add_zero] using hc.tendsto 0
      filter_upwards [ht.eventually (eventually_lt_nhds hneg)] with s hs
      rw [relu, relu, max_eq_right hs.le, max_eq_right hneg.le]
  -- a small `s ≠ 0` with both properties
  have hev3 : ∀ᶠ s in 𝓝[≠] (0 : ℝ), (pat θ (x₀ + s • u) = P
      ∧ ∀ j, relu ((x₀ + s • u) ⬝ᵥ a j) = relu (x₀ ⬝ᵥ a j)) ∧ s ≠ 0 :=
    ((hev1.and hev2).filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin
  obtain ⟨s, ⟨hs1, hs2⟩, hs0⟩ := hev3.exists
  -- the skipless network has the same output at the two inputs
  have hskip : eval (Arch.mlp relu id hid') 0 θ' (Matrix.of fun _ => x₀ + s • u)
      = eval (Arch.mlp relu id hid') 0 θ' (Matrix.of fun _ => x₀) := by
    refine eval_skipless_congr θ' ?_
    ext t j
    simp only [Matrix.map_apply]
    have h4 := hs2 j
    subst ha_def
    exact h4
  -- the residual network does not
  have e1 : eval (Arch.mlp relu id hid) 1 θ (Matrix.of fun _ => x₀ + s • u) t₀
      = (x₀ + s • u) ᵥ* (θ.E * theta θ P (Fin.last L)) ᵥ* θ.D := by
    rw [eval_row]
    show hrow θ (x₀ + s • u) (Fin.last L) ᵥ* θ.D = _
    rw [hrow_eq, hs1]
  have e0 : eval (Arch.mlp relu id hid) 1 θ (Matrix.of fun _ => x₀) t₀
      = x₀ ᵥ* (θ.E * theta θ P (Fin.last L)) ᵥ* θ.D := by
    rw [eval_row]
    show hrow θ x₀ (Fin.last L) ᵥ* θ.D = _
    rw [hrow_eq]
  have h5 := congrFun ((hall _).trans (hskip.trans (hall _).symm)) t₀
  rw [e1, e0, Matrix.add_vecMul, Matrix.add_vecMul, Matrix.smul_vecMul, Matrix.smul_vecMul] at h5
  have h6 : s • (u ᵥ* (θ.E * theta θ P (Fin.last L)) ᵥ* θ.D) = 0 := by
    have h7 := congrArg (· - x₀ ᵥ* (θ.E * theta θ P (Fin.last L)) ᵥ* θ.D) h5
    simpa only [add_sub_cancel_left, sub_self] using h7
  rcases smul_eq_zero.1 h6 with h7 | h7
  · exact hs0 h7
  · exact huM h7

/-- **Theorem 4.5 for ReLU, under the conditions of the proof.** A residual ReLU network that
satisfies `FirstBlockGeneric` equals no skipless ReLU network whose first block has fewer than
`2 d` hidden units, whatever its model dimension, its depth and its other widths. -/
theorem exists_ne_skipless_of_first_card_lt_relu [Nonempty T]
    (θ : Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut) (hθ : FirstBlockGeneric θ)
    {L' : ℕ} {d' : Type*} [Fintype d'] (hid' : Fin (L' + 1) → Type) [∀ ℓ, Fintype (hid' ℓ)]
    (hcard : Fintype.card (hid' 0) < 2 * Fintype.card d)
    (θ' : Params (Arch.mlp (T := T) (d := d') relu id hid') dIn dOut) :
    ∃ X : Matrix T dIn ℝ,
      eval (Arch.mlp relu id hid) 1 θ X ≠ eval (Arch.mlp relu id hid') 0 θ' X := by
  classical
  by_contra hcon
  push Not at hcon
  -- a left inverse of `E`
  obtain ⟨B, hB⟩ : ∃ B : Matrix d dIn ℝ, B * θ.E = 1 :=
    Matrix.vecMul_surjective_iff_exists_left_inverse.1
      (Matrix.vecMul_surjective_iff_rank_eq_card.2 hθ.rank_E)
  -- the vectors of the hyperplanes: those of the residual network, and the nonzero reads
  -- `a_j = E' w'_j` of the first skipless block
  let w : ((∀ ℓ : Fin L, Finset (hid ℓ)) × (Σ ℓ : Fin L, hid ℓ)) ⊕ hid' 0 → dIn → ℝ :=
    Sum.elim (fun p => resVec θ p.1 p.2.1 p.2.2) (fun j b => (θ'.E * θ'.read 0) b j)
  -- a row `x₀` off all of them
  obtain ⟨x₀, -, hx₀⟩ := exists_dotProduct_eq_zero_and_ne_zero (n := dIn)
    (ι := {k // w k ≠ 0}) 0 (fun k => w k.1) (fun k r => by rw [smul_zero]; exact k.2)
  have hres : ∀ P k i, x₀ ⬝ᵥ resVec θ P k i ≠ 0 := fun P k i =>
    hx₀ ⟨Sum.inl (P, ⟨k, i⟩), resVec_ne_zero θ hθ hB P k i⟩
  have ha : ∀ j : hid' 0, (fun b => (θ'.E * θ'.read 0) b j) ≠ 0 →
      x₀ ⬝ᵥ (fun b => (θ'.E * θ'.read 0) b j) ≠ 0 := fun j hj => hx₀ ⟨Sum.inr j, hj⟩
  -- the units active at `x₀` and those active at `-x₀` are disjoint
  have hsum : (Finset.univ.filter fun j : hid' 0 =>
        0 < x₀ ⬝ᵥ (fun b => (θ'.E * θ'.read 0) b j)).card
      + (Finset.univ.filter fun j : hid' 0 =>
        0 < (-x₀) ⬝ᵥ (fun b => (θ'.E * θ'.read 0) b j)).card ≤ Fintype.card (hid' 0) := by
    have h1 := Finset.card_filter_add_card_filter_not (s := Finset.univ)
      (fun j : hid' 0 => 0 < x₀ ⬝ᵥ (fun b => (θ'.E * θ'.read 0) b j))
    have h2 : (Finset.univ.filter fun j : hid' 0 =>
          0 < (-x₀) ⬝ᵥ (fun b => (θ'.E * θ'.read 0) b j))
        ⊆ Finset.univ.filter fun j : hid' 0 =>
          ¬ 0 < x₀ ⬝ᵥ (fun b => (θ'.E * θ'.read 0) b j) := by
      intro j hj
      rw [Finset.mem_filter] at hj ⊢
      refine ⟨hj.1, fun h => ?_⟩
      have h3 := hj.2
      rw [neg_dotProduct] at h3
      linarith
    have h3 := Finset.card_le_card h2
    rw [Finset.card_univ] at h1
    omega
  -- so at `x₀` or at `-x₀` fewer than `d` units are active
  rcases lt_or_ge (Finset.univ.filter fun j : hid' 0 =>
      0 < x₀ ⬝ᵥ (fun b => (θ'.E * θ'.read 0) b j)).card (Fintype.card d) with h | h
  · exact false_of_card_active_lt θ hθ θ' hcon x₀ hres ha h
  · refine false_of_card_active_lt θ hθ θ' hcon (-x₀) (fun P k i => ?_) (fun j hj => ?_)
      (by omega)
    · rw [neg_dotProduct, neg_ne_zero]
      exact hres P k i
    · rw [neg_dotProduct, neg_ne_zero]
      exact ha j hj

/-- **Theorem 4.5 for ReLU.** For almost every choice of weights (`d_in, d_out ≥ d`), a residual
ReLU network equals no skipless ReLU network whose first block has fewer than `2 d` hidden units,
whatever its model dimension, its depth and its other widths. -/
theorem ae_ne_skipless_of_first_card_lt_relu [Nonempty T]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut))
    [μ.IsAddHaarMeasure]
    (hdIn : Fintype.card d ≤ Fintype.card dIn) (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, ∀ (L' : ℕ) (d' : Type) [Fintype d'] (hid' : Fin (L' + 1) → Type)
      [∀ ℓ, Fintype (hid' ℓ)], Fintype.card (hid' 0) < 2 * Fintype.card d →
      ∀ θ' : Params (Arch.mlp (T := T) (d := d') relu id hid') dIn dOut,
        ∃ X : Matrix T dIn ℝ,
          eval (Arch.mlp relu id hid) 1 θ X ≠ eval (Arch.mlp relu id hid') 0 θ' X := by
  rcases isEmpty_or_nonempty d with hd | hd
  · -- `d` empty: no first block has fewer than `0` units
    refine Eventually.of_forall fun θ L' d' _ hid' _ hcard => ?_
    have h0 : Fintype.card d = 0 := Fintype.card_eq_zero
    omega
  · filter_upwards [ae_firstBlockGeneric μ hdIn hdOut] with θ hθ
    intro L' d' _ hid' _ hcard θ'
    exact exists_ne_skipless_of_first_card_lt_relu θ hθ hid' hcard θ'

/-! ### GELU along rays -/

/-- `ReLU(t y) = t ReLU(y)` for `t > 0`. -/
private theorem relu_mul_pos {t : ℝ} (ht : 0 < t) (y : ℝ) : relu (t * y) = t * relu y := by
  rw [relu, relu, mul_max_of_nonneg _ _ ht.le, mul_zero]

/-- If `z t → z₀`, then `GELU(t z t)/t → ReLU(z₀)`. -/
private theorem tendsto_inv_mul_gelu {z : ℝ → ℝ} {z₀ : ℝ} (hz : Tendsto z atTop (𝓝 z₀)) :
    Tendsto (fun t => t⁻¹ * gelu (t * z t)) atTop (𝓝 (relu z₀)) := by
  -- `|GELU(t z) - ReLU(t z)| / t ≤ 1 / t`
  have h1 : Tendsto (fun t : ℝ => t⁻¹ * (gelu (t * z t) - relu (t * z t))) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ tendsto_inv_atTop_zero
    filter_upwards [eventually_gt_atTop 0] with t ht
    rw [Real.norm_eq_abs, abs_mul, abs_inv, abs_of_pos ht]
    exact mul_le_of_le_one_right (inv_nonneg.2 ht.le) (abs_gelu_sub_relu_le _)
  -- `ReLU(t z)/t = ReLU(z) → ReLU(z₀)`
  have h2 : Tendsto (fun t => relu (z t)) atTop (𝓝 (relu z₀)) :=
    (continuous_relu'.tendsto z₀).comp hz
  have h3 := h1.add h2
  rw [zero_add] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  rw [relu_mul_pos ht, mul_sub, ← mul_assoc, inv_mul_cancel₀ ht.ne', one_mul, sub_add_cancel]

/-- An entry of `(A t N)/t` tends to that of `A₀ N` if the entries of `A t / t` in its row tend
to those of `A₀`. -/
private theorem tendsto_inv_mul_mul_apply {p n q : Type*} [Fintype n] {A : ℝ → Matrix p n ℝ}
    {A₀ : Matrix p n ℝ} (N : Matrix n q ℝ) {i : p}
    (h : ∀ j, Tendsto (fun t => t⁻¹ * A t i j) atTop (𝓝 (A₀ i j))) (k : q) :
    Tendsto (fun t => t⁻¹ * (A t * N) i k) atTop (𝓝 ((A₀ * N) i k)) := by
  simp only [Matrix.mul_apply, Finset.mul_sum]
  refine tendsto_finsetSum _ fun j _ => ?_
  simp only [← mul_assoc]
  exact (h j).mul_const _

/-- An entry of `GELU(Y t)/t` tends to that of `ReLU(Y₀)` if the entry of `Y t / t` tends to that
of `Y₀`. -/
private theorem tendsto_inv_mul_map_gelu {p n : Type*} {Y : ℝ → Matrix p n ℝ} {Y₀ : Matrix p n ℝ}
    {i : p} {j : n} (h : Tendsto (fun t => t⁻¹ * Y t i j) atTop (𝓝 (Y₀ i j))) :
    Tendsto (fun t => t⁻¹ * (Y t).map gelu i j) atTop (𝓝 (Y₀.map relu i j)) := by
  simp only [Matrix.map_apply]
  refine (tendsto_inv_mul_gelu h).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  rw [← mul_assoc, mul_inv_cancel₀ ht.ne', one_mul]

omit [Fintype T] [Fintype dOut] [∀ ℓ, DecidableEq (hid ℓ)] in
/-- The hidden states along the ray: `h_ℓ(t X)/t → h_ℓ^ReLU(X)`, entry by entry. -/
private theorem tendsto_hidden_gelu_ray {m : Type*} [Fintype m] (S : Fin L → Matrix m m ℝ)
    (θ : Params (Arch.mlp (T := T) (d := m) gelu id hid) dIn dOut) (X : Matrix T dIn ℝ)
    (ℓ : Fin (L + 1)) :
    ∀ t₀ k, Tendsto (fun t : ℝ => t⁻¹ * hidden (Arch.mlp gelu id hid) S θ (t • X) ℓ t₀ k) atTop
      (𝓝 (hidden (Arch.mlp relu id hid) S
        (⟨θ.E, θ.read, θ.write, θ.D⟩ : Params (Arch.mlp (T := T) (d := m) relu id hid) dIn dOut)
        X ℓ t₀ k)) := by
  induction ℓ using Fin.induction with
  | zero =>
    -- `h_0(t X)/t = X E`
    intro t₀ k
    simp only [hidden_zero]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with t ht
    rw [Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ ht.ne',
      one_mul]
  | succ ℓ ih =>
    intro t₀ k
    -- the stream term, the arguments of the units, and the output of the block
    have h1 : Tendsto (fun t : ℝ => t⁻¹ *
        (hidden (Arch.mlp gelu id hid) S θ (t • X) ℓ.castSucc * S ℓ) t₀ k) atTop
        (𝓝 ((hidden (Arch.mlp relu id hid) S ⟨θ.E, θ.read, θ.write, θ.D⟩ X ℓ.castSucc * S ℓ)
          t₀ k)) :=
      tendsto_inv_mul_mul_apply (S ℓ) (ih t₀) k
    have hpre : ∀ j, Tendsto (fun t : ℝ => t⁻¹ *
        (hidden (Arch.mlp gelu id hid) S θ (t • X) ℓ.castSucc * θ.read ℓ) t₀ j) atTop
        (𝓝 ((hidden (Arch.mlp relu id hid) S ⟨θ.E, θ.read, θ.write, θ.D⟩ X ℓ.castSucc
          * θ.read ℓ) t₀ j)) :=
      fun j => tendsto_inv_mul_mul_apply (θ.read ℓ) (ih t₀) j
    have h2 : Tendsto (fun t : ℝ => t⁻¹ *
        ((hidden (Arch.mlp gelu id hid) S θ (t • X) ℓ.castSucc * θ.read ℓ).map gelu
          * θ.write ℓ) t₀ k) atTop
        (𝓝 (((hidden (Arch.mlp relu id hid) S ⟨θ.E, θ.read, θ.write, θ.D⟩ X ℓ.castSucc
          * θ.read ℓ).map relu * θ.write ℓ) t₀ k)) :=
      tendsto_inv_mul_mul_apply (θ.write ℓ) (fun j => tendsto_inv_mul_map_gelu (hpre j)) k
    simp only [hidden_succ]
    refine (h1.add h2).congr' (Eventually.of_forall fun t => ?_)
    exact (mul_add _ _ _).symm

omit [∀ ℓ, DecidableEq (hid ℓ)] in
/-- `F(t X)/t → F^ReLU(X)`, for any model dimension (a universe-polymorphic form of
`tendsto_eval_gelu_ray`). -/
private theorem tendsto_eval_gelu_ray' {m : Type*} [Fintype m] (S : Fin L → Matrix m m ℝ)
    (θ : Params (Arch.mlp (T := T) (d := m) gelu id hid) dIn dOut) (X : Matrix T dIn ℝ) :
    Tendsto (fun t : ℝ => t⁻¹ • eval (Arch.mlp gelu id hid) S θ (t • X)) atTop
      (𝓝 (eval (Arch.mlp relu id hid) S
        (⟨θ.E, θ.read, θ.write, θ.D⟩ : Params (Arch.mlp (T := T) (d := m) relu id hid) dIn dOut)
        X)) := by
  refine tendsto_pi_nhds.2 fun t₀ => tendsto_pi_nhds.2 fun o => ?_
  exact tendsto_inv_mul_mul_apply θ.D (tendsto_hidden_gelu_ray S θ X (Fin.last L) t₀) o

omit [DecidableEq d] [∀ ℓ, DecidableEq (hid ℓ)] in
/-- **GELU networks along rays** (proof of Theorem 4.5, "GELU"). Without normalization, for all
stream matrices `S` (with or without skips), the output of a GELU network at the input `t X`,
divided by `t`, tends as `t → ∞` to the output at `X` of the ReLU network with the same
weights. -/
theorem tendsto_eval_gelu_ray (S : Fin L → Matrix d d ℝ)
    (θ : Params (Arch.mlp (T := T) (d := d) gelu id hid) dIn dOut) (X : Matrix T dIn ℝ) :
    Tendsto (fun t : ℝ => t⁻¹ • eval (Arch.mlp gelu id hid) S θ (t • X)) atTop
      (𝓝 (eval (Arch.mlp relu id hid) S (θ.withActivation relu) X)) := by
  exact tendsto_eval_gelu_ray' S θ X

/-- **Theorem 4.5 for GELU, under the conditions of the proof.** A residual GELU network that
satisfies `FirstBlockGeneric` equals no skipless GELU network whose first block has fewer than
`2 d` hidden units, whatever its model dimension, its depth and its other widths. -/
theorem exists_ne_skipless_of_first_card_lt_gelu [Nonempty T]
    (θ : Params (Arch.mlp (T := T) (d := d) gelu id hid) dIn dOut) (hθ : FirstBlockGeneric θ)
    {L' : ℕ} {d' : Type*} [Fintype d'] (hid' : Fin (L' + 1) → Type) [∀ ℓ, Fintype (hid' ℓ)]
    (hcard : Fintype.card (hid' 0) < 2 * Fintype.card d)
    (θ' : Params (Arch.mlp (T := T) (d := d') gelu id hid') dIn dOut) :
    ∃ X : Matrix T dIn ℝ,
      eval (Arch.mlp gelu id hid) 1 θ X ≠ eval (Arch.mlp gelu id hid') 0 θ' X := by
  by_contra hcon
  push Not at hcon
  -- the ReLU networks with the same weights differ at some `X` (the conditions do not involve
  -- the activation)
  obtain ⟨X, hX⟩ := exists_ne_skipless_of_first_card_lt_relu (θ.withActivation relu)
    ⟨hθ.rank_E, hθ.rank_D, hθ.read_ne_zero, hθ.isUnit_det⟩ hid' hcard
    (⟨θ'.E, θ'.read, θ'.write, θ'.D⟩ : Params (Arch.mlp (T := T) (d := d') relu id hid') dIn dOut)
  apply hX
  -- but both are the limit of `F(t X)/t` along the ray
  refine tendsto_nhds_unique (tendsto_eval_gelu_ray' 1 θ X) ?_
  exact (tendsto_eval_gelu_ray' 0 θ' X).congr fun t =>
    (congrArg (fun M => t⁻¹ • M) (hcon (t • X))).symm

/-- **Theorem 4.5 for GELU.** For almost every choice of weights (`d_in, d_out ≥ d`), a residual
GELU network equals no skipless GELU network whose first block has fewer than `2 d` hidden units,
whatever its model dimension, its depth and its other widths. -/
theorem ae_ne_skipless_of_first_card_lt_gelu [Nonempty T]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) gelu id hid) dIn dOut))
    [μ.IsAddHaarMeasure]
    (hdIn : Fintype.card d ≤ Fintype.card dIn) (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, ∀ (L' : ℕ) (d' : Type) [Fintype d'] (hid' : Fin (L' + 1) → Type)
      [∀ ℓ, Fintype (hid' ℓ)], Fintype.card (hid' 0) < 2 * Fintype.card d →
      ∀ θ' : Params (Arch.mlp (T := T) (d := d') gelu id hid') dIn dOut,
        ∃ X : Matrix T dIn ℝ,
          eval (Arch.mlp gelu id hid) 1 θ X ≠ eval (Arch.mlp gelu id hid') 0 θ' X := by
  rcases isEmpty_or_nonempty d with hd | hd
  · -- `d` empty: no first block has fewer than `0` units
    refine Eventually.of_forall fun θ L' d' _ hid' _ hcard => ?_
    have h0 : Fintype.card d = 0 := Fintype.card_eq_zero
    omega
  · filter_upwards [ae_firstBlockGeneric μ hdIn hdOut] with θ hθ
    intro L' d' _ hid' _ hcard θ'
    exact exists_ne_skipless_of_first_card_lt_gelu θ hθ hid' hcard θ'

end Skips
