import SkipsLean.Depth.StepZeroTanhPath
import SkipsLean.Depth.FlatAtWriteRows
import SkipsLean.Depth.RowsAux
import SkipsLean.Depth.SuffixZeroClaim

/-!
# The step from `(D_{k+1})` to `(D_k)` for a `tanh` block under pre-RMSNorm with `ε = 0`

Paper (dimension paper): Appendix D.6, "The step for tanh on the path" and Lemma D.18.

"Let `σ = tanh`. Consider, for a block `ℓ` with `W = W_read^ℓ`, its columns `c_j`, `V = W_write^ℓ`
and `κ_ℓ` of Lemma D.14:
 (S1) any two rows of `V` are linearly independent;
 (S2) the columns of `W` are linearly independent over `ℚ`;
 (S3) there are a unit row `ξ₀` and a number `ρ ∈ (0, 1]` such that every `ξ₀c_j ≠ 0` and, with
      `s_j` the sign of `ξ₀c_j` and `s̄ = (s_1, …, s_q)`: the rows `w̃V` with `|w̃_j − s_j| ≤ ρ` for
      all `j` lie in `C_{κ_ℓ}`, and `e^{−2√d |ξ₀c_j|} < ρ/3` for every `j`."

"Lemma D.18 (The step for tanh on the path). Let `σ = tanh`, in the case (0), let `θ` be regular,
and let block `k + 1` satisfy (S1) to (S3). Then `(D_{k+1})` implies `(D_k)`."

Its proof, after the part for one pair `ξ, ξ'` (`Depth/StepZeroTanhPath.lean`): "(a) … Its
imaginary part is `ξ (Z + Zᵀ) ξ'ᵀ = 0`. This holds for every unit row `ξ'` orthogonal to `ξ`, so
`ξ (Z + Zᵀ)` is a multiple of `ξ`, for every `ξ ∈ P'` and then, by continuity, for every `ξ` in the
open set `P`. A matrix for which every row of an open set is an eigenvector is a multiple of the
identity. So `Z + Zᵀ = 2β_k I`, and `Z = Y_k + β_k I` with `Y_k` antisymmetric. (b) … so
`ξ (Y_k W + η_W) = 0` for every `ξ ∈ P'`, and `η_W = −Y_k W`. (c) … By Lemma D.3 with `A = V`,
`η_V = V Z'` and (16) holds for `k + 1` with `Z'` and `η'`. By `(D_{k+1})`, `Z' = Y_{k+1} + β_{k+1} I`
and `η'` is as in (18). With (a) and (b) this is (18) for `k`."

Here the number `κ_ℓ` of Lemma D.14 is any `κ > 0` such that `𝓑_{>ℓ}` is holomorphic on the cone
`C_κ` (`HolomorphicOnCone`, a hypothesis of the lemma); the rows `w̃` of (S3) are complex rows.
Numbering as in `Depth/StepTanh.lean`: the block is `k : Fin L`, the paper's block `k + 1`; the
hidden state before it is `k.castSucc` and after it `k.succ`.
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut] {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)] {σ : ℝ → ℝ}

/-- **Condition (S3)** for block `k` (read `W` with the columns `c_j`, write `V`) and the cone
`C_κ`: there are a unit row `ξ₀` and a number `ρ ∈ (0, 1]` such that every `ξ₀c_j ≠ 0` and, with
`s_j` the sign of `ξ₀c_j`: the rows `w̃V` with `|w̃_j − s_j| ≤ ρ` for all `j` lie in `C_κ`, and
`e^{−2√d |ξ₀c_j|} < ρ/3` for every `j`. -/
def CondS3 (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) (k : Fin L)
    (κ : ℝ) : Prop :=
  ∃ (ξ₀ : d → ℝ) (ρ : ℝ), ξ₀ ⬝ᵥ ξ₀ = 1 ∧ 0 < ρ ∧ ρ ≤ 1 ∧
    (∀ j : hid k, (ξ₀ ᵥ* θ.read k) j ≠ 0) ∧
    (∀ w : hid k → ℂ,
      (∀ j, ‖w j - ((Real.sign ((ξ₀ ᵥ* θ.read k) j) : ℝ) : ℂ)‖ ≤ ρ) →
        w ᵥ* θ.toC.2.1 k ∈ complexCone κ) ∧
    ∀ j : hid k,
      Real.exp (-(2 * (Real.sqrt (Fintype.card d) * |(ξ₀ ᵥ* θ.read k) j|))) < ρ / 3

/-- Helper: the unit row `x̂ = ‖x‖⁻¹ x` in the direction of a row `x`. -/
private noncomputable def unitRow_szt (x : d → ℝ) : d → ℝ := (Real.sqrt (x ⬝ᵥ x))⁻¹ • x

omit [Fintype d] [DecidableEq d] in
/-- Helper: `x̂ W = ‖x‖⁻¹ (x W)`. -/
private theorem unitRow_vecMul_szt [Fintype d] {q : Type*} (x : d → ℝ) (W : Matrix d q ℝ) :
    unitRow_szt x ᵥ* W = (Real.sqrt (x ⬝ᵥ x))⁻¹ • (x ᵥ* W) := by
  unfold unitRow_szt
  rw [Matrix.smul_vecMul]

omit [DecidableEq d] in
/-- Helper: `x̂` is a unit row when `x ≠ 0`. -/
private theorem unitRow_dot_self_szt {x : d → ℝ} (hx : 0 < x ⬝ᵥ x) :
    unitRow_szt x ⬝ᵥ unitRow_szt x = 1 := by
  unfold unitRow_szt
  rw [smul_dotProduct, dotProduct_smul, smul_smul, smul_eq_mul, ← _root_.mul_inv,
    Real.mul_self_sqrt hx.le, inv_mul_cancel₀ hx.ne']

omit [DecidableEq d] in
/-- Helper: `x ↦ x̂` is continuous on the rows `x ≠ 0`. -/
private theorem continuousOn_unitRow_szt :
    ContinuousOn (unitRow_szt (d := d)) {x | 0 < x ⬝ᵥ x} := by
  have h1 : Continuous fun x : d → ℝ => x ⬝ᵥ x := by simp only [dotProduct]; fun_prop
  have h2 : ContinuousOn (fun x : d → ℝ => (Real.sqrt (x ⬝ᵥ x))⁻¹) {x | 0 < x ⬝ᵥ x} :=
    (Real.continuous_sqrt.comp h1).continuousOn.inv₀ fun x hx => (Real.sqrt_pos.2 hx).ne'
  exact h2.smul continuousOn_id

omit [DecidableEq d] in
/-- Helper: a nonzero row has `x ⬝ x > 0`. -/
private theorem dotProduct_self_pos_szt {x : d → ℝ} (hx : x ≠ 0) : 0 < x ⬝ᵥ x :=
  lt_of_le_of_ne (Finset.sum_nonneg fun j _ => mul_self_nonneg (x j))
    (Ne.symm (fun h => hx (dotProduct_self_eq_zero.1 h)))

/-- Helper: with `d ≥ 2`, every row has a unit row orthogonal to it. -/
private theorem exists_unit_orth_szt (hd : 2 ≤ Fintype.card d) (ξ : d → ℝ) :
    ∃ ξ' : d → ℝ, ξ' ⬝ᵥ ξ' = 1 ∧ ξ ⬝ᵥ ξ' = 0 := by
  obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card (by omega : 1 < Fintype.card d)
  by_cases ha : ξ a = 0
  · -- the unit row `e_a`
    refine ⟨Pi.single a 1, ?_, ?_⟩
    · rw [dotProduct_single, Pi.single_eq_same, one_mul]
    · rw [dotProduct_single, ha, zero_mul]
  · -- the row `y = ξ_b e_a − ξ_a e_b`, normalized
    set y : d → ℝ := ξ b • Pi.single a 1 - ξ a • Pi.single b 1 with hy
    have hyb : y b = -ξ a := by
      simp only [hy, Pi.sub_apply, Pi.smul_apply, Pi.single_eq_same, Pi.single_eq_of_ne hab.symm,
        smul_eq_mul, mul_zero, mul_one, zero_sub]
    have hy0 : y ≠ 0 := fun h => ha (by
      have := congrFun h b
      rw [hyb, Pi.zero_apply] at this
      linarith)
    have hξy : ξ ⬝ᵥ y = 0 := by
      rw [hy, dotProduct_sub, dotProduct_smul, dotProduct_smul, dotProduct_single,
        dotProduct_single, smul_eq_mul, smul_eq_mul]
      ring
    refine ⟨unitRow_szt y, unitRow_dot_self_szt (dotProduct_self_pos_szt hy0), ?_⟩
    unfold unitRow_szt
    rw [dotProduct_smul, hξy, smul_zero]

/-- Helper: over `ℚ`, the linear independence of `(u_j)_j` passes to `(c u_j)_j`, `c ≠ 0` real. -/
private theorem linearIndependent_mul_szt {q : Type*} {u : q → ℝ} (hu : LinearIndependent ℚ u)
    {c : ℝ} (hc : c ≠ 0) : LinearIndependent ℚ (fun j => c * u j) :=
  hu.map' (LinearMap.mulLeft ℚ c) (LinearMap.ker_eq_bot.2 (mul_right_injective₀ hc))

/-- Helper: a continuous function that is constant on `C ∩ Q`, with `C` open and `Q` dense, is
constant on `C`. -/
private theorem eq_on_open_of_dense_szt {E F : Type*} [TopologicalSpace E] [TopologicalSpace F]
    [T1Space F] {C Q : Set E} (hC : IsOpen C) (hQ : Dense Q) {f : E → F} (hf : Continuous f)
    (c : F) (h : ∀ x ∈ C, x ∈ Q → f x = c) : ∀ x ∈ C, f x = c := by
  intro x hx
  by_contra hne
  obtain ⟨y, ⟨hyC, hy⟩, hyQ⟩ := hQ.inter_open_nonempty (C ∩ f ⁻¹' {c}ᶜ)
    (hC.inter (isOpen_compl_singleton.preimage hf)) ⟨x, hx, hne⟩
  exact hy (h y hyC hyQ)

/-- Helper: if `u ⬝ y = 0` for every row `y` orthogonal to `x`, all the minors `u_i x_j − u_j x_i`
vanish (take `y = x_j e_i − x_i e_j`). -/
private theorem minor_eq_of_orth_szt (u x : d → ℝ)
    (h : ∀ y : d → ℝ, x ⬝ᵥ y = 0 → u ⬝ᵥ y = 0) (i j : d) : u i * x j = u j * x i := by
  have e := h (x j • Pi.single i 1 - x i • Pi.single j 1) (by
    rw [dotProduct_sub, dotProduct_smul, dotProduct_smul, dotProduct_single, dotProduct_single,
      smul_eq_mul, smul_eq_mul]
    ring)
  rw [dotProduct_sub, dotProduct_smul, dotProduct_smul, dotProduct_single, dotProduct_single,
    smul_eq_mul, smul_eq_mul] at e
  linarith

omit [DecidableEq d] in
/-- Helper: `ξZyᵀ + yZξᵀ = ξ(Z + Zᵀ)yᵀ`. -/
private theorem dot_sym_szt (Z : Matrix d d ℝ) (x y : d → ℝ) :
    (x ᵥ* Z) ⬝ᵥ y + (y ᵥ* Z) ⬝ᵥ x = (x ᵥ* (Z + Zᵀ)) ⬝ᵥ y := by
  rw [Matrix.vecMul_add, add_dotProduct, Matrix.vecMul_transpose, dotProduct_comm (Z *ᵥ x) y,
    Matrix.dotProduct_mulVec]

/-- Helper: the cone of good rows `x ≠ 0`: `s_j (xW)_j > 0` and `e^{−2a|x̂ W_j|} < b` for all
`j`. -/
private def coneRows_szt {q : Type*} [Fintype q] (W : Matrix d q ℝ) (s : q → ℝ) (a b : ℝ) :
    Set (d → ℝ) :=
  {x | 0 < x ⬝ᵥ x ∧ (∀ j, 0 < s j * (x ᵥ* W) j) ∧
    ∀ j, Real.exp (-(2 * (a * |(unitRow_szt x ᵥ* W) j|))) < b}

omit [DecidableEq d] in
/-- Helper: the cone of good rows is open. -/
private theorem isOpen_coneRows_szt {q : Type*} [Fintype q] (W : Matrix d q ℝ) (s : q → ℝ)
    (a b : ℝ) : IsOpen (coneRows_szt W s a b) := by
  have h1 : Continuous fun x : d → ℝ => x ⬝ᵥ x := by simp only [dotProduct]; fun_prop
  have hW : Continuous fun x : d → ℝ => x ᵥ* W := continuous_id.matrix_vecMul continuous_const
  have hS : IsOpen {x : d → ℝ | 0 < x ⬝ᵥ x} := isOpen_lt continuous_const h1
  have hT : IsOpen {u : q → ℝ | ∀ j, Real.exp (-(2 * (a * |u j|))) < b} := by
    have e : {u : q → ℝ | ∀ j, Real.exp (-(2 * (a * |u j|))) < b}
        = ⋂ j, {u : q → ℝ | Real.exp (-(2 * (a * |u j|))) < b} := by
      ext u; simp only [Set.mem_iInter]; rfl
    rw [e]
    exact isOpen_iInter_of_finite fun j => isOpen_lt (by fun_prop) continuous_const
  have hU : IsOpen {x : d → ℝ | ∀ j, 0 < s j * (x ᵥ* W) j} := by
    have e : {x : d → ℝ | ∀ j, 0 < s j * (x ᵥ* W) j} = ⋂ j, {x : d → ℝ | 0 < s j * (x ᵥ* W) j} := by
      ext x; simp only [Set.mem_iInter]; rfl
    rw [e]
    exact isOpen_iInter_of_finite fun j =>
      isOpen_lt continuous_const (continuous_const.mul ((continuous_apply j).comp hW))
  have hf : ContinuousOn (fun x : d → ℝ => unitRow_szt x ᵥ* W) {x | 0 < x ⬝ᵥ x} := by
    have hv : Continuous fun y : d → ℝ => y ᵥ* W := hW
    exact hv.comp_continuousOn continuousOn_unitRow_szt
  have ho := (hf.isOpen_inter_preimage hS hT).inter hU
  convert ho using 1
  ext x
  simp only [coneRows_szt, Set.mem_inter_iff, Set.mem_preimage]
  constructor
  · rintro ⟨h0, hs, hd⟩; exact ⟨⟨h0, hd⟩, hs⟩
  · rintro ⟨⟨h0, hd⟩, hs⟩; exact ⟨h0, hs, hd⟩

omit [DecidableEq d] in
/-- Helper: for a row `x` of the cone with `xc_1, …, xc_q` linearly independent over `ℚ`, the unit
row `x̂` is a unit row with the sign, decay and independence hypotheses of the path. -/
private theorem good_unitRow_szt {q : Type*} [Fintype q] (W : Matrix d q ℝ) (s : q → ℝ)
    (a b : ℝ) {x : d → ℝ} (hx : x ∈ coneRows_szt W s a b)
    (hxQ : LinearIndependent ℚ fun j => (x ᵥ* W) j) :
    unitRow_szt x ⬝ᵥ unitRow_szt x = 1 ∧ (∀ j, 0 < s j * (unitRow_szt x ᵥ* W) j) ∧
      (∀ j, Real.exp (-(2 * (a * |(unitRow_szt x ᵥ* W) j|))) < b) ∧
      LinearIndependent ℚ (fun j => (unitRow_szt x ᵥ* W) j) := by
  obtain ⟨hx0, hxs, hxd⟩ := hx
  have ha : 0 < (Real.sqrt (x ⬝ᵥ x))⁻¹ := inv_pos.2 (Real.sqrt_pos.2 hx0)
  refine ⟨unitRow_dot_self_szt hx0, fun j => ?_, hxd, ?_⟩
  · rw [unitRow_vecMul_szt, Pi.smul_apply, smul_eq_mul, mul_left_comm]
    exact mul_pos ha (hxs j)
  · rw [unitRow_vecMul_szt]
    exact linearIndependent_mul_szt hxQ ha.ne'

omit [DecidableEq d] in
/-- Helper: `ξ₀` (a unit row with every `ξ₀c_j ≠ 0`, signs `s_j`, and the decay) is in the cone. -/
private theorem mem_coneRows_szt {q : Type*} [Fintype q] (W : Matrix d q ℝ) (a b : ℝ)
    {ξ₀ : d → ℝ} (h1 : ξ₀ ⬝ᵥ ξ₀ = 1) (hne : ∀ j, (ξ₀ ᵥ* W) j ≠ 0)
    (hdec : ∀ j, Real.exp (-(2 * (a * |(ξ₀ ᵥ* W) j|))) < b) :
    ξ₀ ∈ coneRows_szt W (fun j => Real.sign ((ξ₀ ᵥ* W) j)) a b := by
  have hu : unitRow_szt ξ₀ = ξ₀ := by
    unfold unitRow_szt
    rw [h1, Real.sqrt_one, inv_one, one_smul]
  refine ⟨by rw [h1]; exact one_pos, fun j => Real.sign_mul_pos_of_ne_zero _ (hne j), ?_⟩
  rw [hu]
  exact hdec

/-- Helper: the rows `r` with `|r_j − s_j| < ρ/4` for all `j` form an open set. -/
private theorem isOpen_rows_near_szt {q : Type*} [Fintype q] (s : q → ℝ) (ρ : ℝ) :
    IsOpen {r : q → ℝ | ∀ j, |r j - s j| < ρ / 4} := by
  have e : {r : q → ℝ | ∀ j, |r j - s j| < ρ / 4} = ⋂ j, {r : q → ℝ | |r j - s j| < ρ / 4} := by
    ext r; simp only [Set.mem_iInter]; rfl
  rw [e]
  exact isOpen_iInter_of_finite fun j => isOpen_lt (by fun_prop) continuous_const

/-- **Lemma D.18 of the dimension paper (the step for `tanh` on the path).** Let `σ = tanh`, in the
case (0), `d ≥ 2`, let `θ` be regular, let `𝓑_{>k+1}` be holomorphic on the cone `C_κ`, `κ > 0`
(Lemma D.14), and let block `k` satisfy (S1), any two rows of its write are linearly independent,
(S2), the columns of its read are linearly independent over `ℚ`, and (S3) for `C_κ`. Then
`(D_{k+1})` implies `(D_k)`. -/
theorem claimZero_castSucc_tanh [Nonempty T]
    {θ : Params (Arch.mlp (T := T) (d := d) Real.tanh (rmsNorm 0) hid) dIn dOut}
    (hθ : RegularZero (Arch.mlp Real.tanh (rmsNorm 0) hid) θ) (hd : 2 ≤ Fintype.card d)
    (k : Fin L)
    (hS1 : ∀ i j : hid k, i ≠ j → ∀ a c : ℝ, a • θ.write k i + c • θ.write k j = 0 →
      a = 0 ∧ c = 0)
    (hS2 : LinearIndependent ℚ (fun j : hid k => fun i : d => θ.read k i j))
    {κ : ℝ} (hκ : 0 < κ) (hhol : HolomorphicOnCone Complex.tanh θ k.succ κ)
    (hS3 : CondS3 θ k κ)
    (hk : ClaimZero (Arch.mlp Real.tanh (rmsNorm 0) hid) θ k.succ) :
    ClaimZero (Arch.mlp Real.tanh (rmsNorm 0) hid) θ k.castSucc := by
  classical
  intro Z η hZη
  have hf : ∀ ℓ, AnalyticOnNhd ℝ ((Arch.mlp (T := T) (d := d) Real.tanh (rmsNorm 0) hid).f ℓ)
      Set.univ := fun ℓ => analyticOnNhd_f_mlp analyticOnNhd_tanh ℓ
  obtain ⟨ξ₀, ρ, hξ₀, hρ, hρ1, hne0, hcone, hdec⟩ := hS3
  -- the signs `s_j` of `ξ₀c_j`
  let s : hid k → ℝ := fun j => Real.sign ((ξ₀ ᵥ* θ.read k) j)
  have hs : ∀ j, s j = 1 ∨ s j = -1 := fun j =>
    (Real.sign_apply_eq_of_ne_zero _ (hne0 j)).symm
  -- the open cone `C` of good rows around `ξ₀`, and the dense set `Q` of (S2)
  let C := coneRows_szt (θ.read k) s (Real.sqrt (Fintype.card d)) (ρ / 3)
  have hCo : IsOpen C := isOpen_coneRows_szt _ _ _ _
  have hξ₀C : ξ₀ ∈ C := mem_coneRows_szt _ _ _ hξ₀ hne0 hdec
  let Q := {x : d → ℝ | LinearIndependent ℚ (fun j => (x ᵥ* θ.read k) j)}
  have hQ : Dense Q := dense_setOf_linearIndependent_vecMul (θ.read k) hS2
  -- the part for one pair `x̂, ξ'` of rows, for `x ∈ C ∩ Q`
  have hP := fun (x : d → ℝ) (hx : x ∈ C) (hxQ : x ∈ Q) (ξ' : d → ℝ) (h1 : ξ' ⬝ᵥ ξ' = 1)
      (h2 : unitRow_szt x ⬝ᵥ ξ' = 0) =>
    have hg := good_unitRow_szt _ _ _ _ hx hxQ
    tanh_path_step θ hθ hd k hS1 hκ hhol s hs hρ hρ1 hcone Z η hZη (unitRow_szt x) ξ' hg.1 h1
      h2 hg.2.1 hg.2.2.1 hg.2.2.2
  -- (a) for `x ∈ C ∩ Q`: `x (Z + Zᵀ) yᵀ = 0` for every `y ⊥ x` (scale `x`, `y` to unit rows)
  have horth : ∀ x ∈ C, x ∈ Q → ∀ y : d → ℝ, x ⬝ᵥ y = 0 → (x ᵥ* (Z + Zᵀ)) ⬝ᵥ y = 0 := by
    intro x hx hxQ y hy
    by_cases hy0 : y = 0
    · rw [hy0, dotProduct_zero]
    have hyy := dotProduct_self_pos_szt hy0
    have h2 : unitRow_szt x ⬝ᵥ unitRow_szt y = 0 := by
      unfold unitRow_szt
      rw [smul_dotProduct, dotProduct_smul, hy, smul_zero, smul_zero]
    have e := (hP x hx hxQ (unitRow_szt y) (unitRow_dot_self_szt hyy) h2).1.1
    rw [dot_sym_szt] at e
    unfold unitRow_szt at e
    rw [Matrix.smul_vecMul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul] at e
    obtain ⟨hxx, -, -⟩ := hx
    have ha := (inv_pos.2 (Real.sqrt_pos.2 hxx)).ne'
    have hb := (inv_pos.2 (Real.sqrt_pos.2 hyy)).ne'
    exact (mul_eq_zero.1 ((mul_eq_zero.1 e).resolve_left ha)).resolve_left hb
  -- so the minors of `x (Z + Zᵀ)` and `x` vanish on `C ∩ Q`, hence on `C` (continuity) ...
  have hmin : ∀ x ∈ C, ∀ i j, (x ᵥ* (Z + Zᵀ)) i * x j = (x ᵥ* (Z + Zᵀ)) j * x i := by
    intro x hx i j
    have hcont : Continuous fun x : d → ℝ =>
        (x ᵥ* (Z + Zᵀ)) i * x j - (x ᵥ* (Z + Zᵀ)) j * x i := by fun_prop
    exact sub_eq_zero.1 (eq_on_open_of_dense_szt hCo hQ hcont 0 (fun y hy hyQ =>
      sub_eq_zero.2 (minor_eq_of_orth_szt _ _ (horth y hy hyQ) i j)) x hx)
  -- ... and `Z + Zᵀ = c I`: `Z = Y₀ + β₀ I` with `β₀ = c / 2` and `Y₀` antisymmetric
  obtain ⟨c, hc⟩ := exists_eq_smul_one_of_vecMul_parallel (Z + Zᵀ) C hCo ⟨ξ₀, hξ₀C⟩ hmin
  have hZt : Zᵀ = c • (1 : Matrix d d ℝ) - Z := eq_sub_of_add_eq' hc
  have hY₀ : Z - (c / 2) • (1 : Matrix d d ℝ) ∈ antisymmetric d := by
    show (Z - (c / 2) • (1 : Matrix d d ℝ))ᵀ = -(Z - (c / 2) • (1 : Matrix d d ℝ))
    rw [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_one, hZt]
    module
  have hdiag : ∀ ξ : d → ℝ, ξ ⬝ᵥ ξ = 1 → (ξ ᵥ* Z) ⬝ᵥ ξ = c / 2 := by
    intro ξ h1
    have e := dot_sym_szt Z ξ ξ
    rw [hc, Matrix.vecMul_smul, Matrix.vecMul_one, smul_dotProduct, h1, smul_eq_mul,
      mul_one] at e
    linarith
  -- (b) for `x ∈ C ∩ Q`: `x̂ (Z W + η_W) = β₀ x̂ W`, so `x (Y₀ W + η_W) = 0`; then on `C`
  have hread0 : ∀ x ∈ C,
      x ᵥ* ((Z - (c / 2) • (1 : Matrix d d ℝ)) * θ.read k + η.read k) = 0 := by
    refine eq_on_open_of_dense_szt hCo hQ (by fun_prop) 0 fun x hx hxQ => ?_
    obtain ⟨ξ', h1, h2⟩ := exists_unit_orth_szt hd (unitRow_szt x)
    have hg := good_unitRow_szt _ _ _ _ hx hxQ
    have e := (hP x hx hxQ ξ' h1 h2).2.1.1
    rw [hdiag _ hg.1] at e
    have hsplit : (Z - (c / 2) • (1 : Matrix d d ℝ)) * θ.read k + η.read k
        = (Z * θ.read k + η.read k) - (c / 2) • θ.read k := by
      rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul]; abel
    have e2 : unitRow_szt x ᵥ* ((Z - (c / 2) • (1 : Matrix d d ℝ)) * θ.read k + η.read k)
        = 0 := by
      rw [hsplit, Matrix.vecMul_sub, Matrix.vecMul_smul, e, sub_self]
    obtain ⟨hxx, -, -⟩ := hx
    rw [unitRow_vecMul_szt] at e2
    exact (smul_eq_zero.1 e2).resolve_left (inv_pos.2 (Real.sqrt_pos.2 hxx)).ne'
  have hreadM := eq_zero_of_vecMul_eq_zero_of_isOpen _ C hCo ⟨ξ₀, hξ₀C⟩ hread0
  have hread : η.read k = -((Z - (c / 2) • (1 : Matrix d d ℝ)) * θ.read k) :=
    eq_neg_of_add_eq_zero_right hreadM
  -- (c) one row `x₁ ∈ C ∩ Q`: the identity at the rows near `s̄`, then Lemma D.3 at the write
  obtain ⟨x₁, hx₁C, hx₁Q⟩ := hQ.inter_open_nonempty C hCo ⟨ξ₀, hξ₀C⟩
  obtain ⟨ξ', h1, h2⟩ := exists_unit_orth_szt hd (unitRow_szt x₁)
  have hc3 := (hP x₁ hx₁C hx₁Q ξ' h1 h2).2.2
  have hOne : ({r : hid k → ℝ | ∀ j, |r j - s j| < ρ / 4}).Nonempty :=
    ⟨s, fun j => by rw [sub_self, abs_zero]; positivity⟩
  have hflat := flat_at_write_of_isOpen_rows analyticOnNhd_tanh θ hθ hd k η _
    (isOpen_rows_near_szt s ρ) hOne hc3
  obtain ⟨Z', hZ', hflat'⟩ := suffixFlatZero_of_flat_at_write
    (Arch.mlp (T := T) (d := d) Real.tanh (rmsNorm 0) hid) θ rfl hf hθ hd k.succ (θ.write k)
    (hθ.rank_write k) (η.write k) η hflat
  -- `(D_{k+1})` gives the antisymmetric changes of basis after the block
  obtain ⟨Y', β', hYa, hZ'eq, hY, hYD⟩ := hk Z' η hflat'
  -- put `Y₀`, `β₀` at the hidden state before the block
  refine ⟨Function.update Y' k.castSucc (Z - (c / 2) • (1 : Matrix d d ℝ)),
    Function.update β' k.castSucc (c / 2), fun ℓ hℓ => ?_, ?_, fun ℓ hℓ => ?_, ?_⟩
  · -- antisymmetric: `Y₀` by (a), the later ones by `(D_{k+1})`
    rcases eq_or_ne ℓ k.castSucc with rfl | hne
    · rw [Function.update_self]
      exact hY₀
    · rw [Function.update_of_ne hne]
      refine hYa ℓ ?_
      have hlt : k.castSucc < ℓ := lt_of_le_of_ne hℓ (Ne.symm hne)
      rw [Fin.lt_def, Fin.val_castSucc] at hlt
      rw [Fin.le_def, Fin.val_succ]
      omega
  · rw [Function.update_self, Function.update_self, sub_add_cancel]
  · rcases eq_or_ne ℓ k with rfl | hne
    · -- the block itself: (b) and (c)
      rw [Function.update_self, Function.update_of_ne (Fin.castSucc_lt_succ).ne',
        Function.update_of_ne (Fin.castSucc_lt_succ).ne', ← hZ'eq]
      exact ⟨hread, hZ'⟩
    · -- a later block: `(D_{k+1})`
      have hlt : k < ℓ := lt_of_le_of_ne (Fin.castSucc_le_castSucc_iff.1 hℓ) (Ne.symm hne)
      have hle : k.succ ≤ ℓ.castSucc := by
        rw [Fin.le_def, Fin.val_succ, Fin.val_castSucc]
        exact hlt
      have h1 : ℓ.castSucc ≠ k.castSucc := fun h => hne (Fin.castSucc_injective _ h)
      have h2 : ℓ.succ ≠ k.castSucc := by
        intro h
        have := congrArg Fin.val h
        rw [Fin.val_succ, Fin.val_castSucc] at this
        have := Fin.lt_def.1 hlt
        omega
      rw [Function.update_of_ne h1, Function.update_of_ne h2, Function.update_of_ne h2]
      exact hY ℓ hle
  · -- the readout
    rw [Function.update_of_ne (Fin.castSucc_lt_last k).ne']
    exact hYD

end Skips
