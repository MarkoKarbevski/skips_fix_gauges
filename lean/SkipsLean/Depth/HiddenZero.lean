import SkipsLean.Depth.SuffixZero
import SkipsLean.Network.Analytic

/-!
# The hidden states as functions of the weights, in the case (0)

Paper (dimension paper): Appendix D.6, proof of Lemma D.20 (The domain). "Let `ℓ ≥ 1` and `x ∈ X`.
On `O^{ℓ−1}`, `h_ℓ = w̃_ℓ W_write^ℓ` with `w̃_ℓ = σ(N(h_{ℓ−1}) W_read^ℓ)`, and `h_{ℓ−1}` does not
depend on the weights of block `ℓ`. […] `w̃_ℓ = 0` exactly where `N(h_{ℓ−1}) W_read^ℓ = 0`, a closed
submanifold of `O^{ℓ−1}` of codimension at least `d_model ≥ 2`, because the derivative with respect
to `W_read^ℓ` is onto. Where `w̃_ℓ ≠ 0`, the derivative of `h_ℓ` with respect to `W_write^ℓ` is onto
`ℝ^{1×d_model}`".

Stated here, for networks of MLP blocks under pre-RMSNorm with `ε = 0` and a real-analytic
activation `σ`, at an input `x` and a token `t` (a hidden state has the rows `T`; "nonzero" is "no
row vanishes"):

* a hidden state `h_j` depends only on `E` and on the blocks before it;
* `h_j` is real-analytic in the weights at a parameter at which no row of `h_0, …, h_{j−1}`
  vanishes, and so are what block `ℓ` reads and the output;
* at a parameter at which no row of `h_0, …, h_ℓ` vanishes (the paper's `h_0, …, h_{ℓ−1}`), the
  derivative in the weights of row `t` of `N(h_ℓ) W_read` is onto; and where this row is not zero
  and `σ` vanishes only at `0`, the derivative in the weights of row `t` of the next hidden state is
  onto.

Numbering: the block `ℓ : Fin L` is the paper's block `ℓ + 1`, between the hidden states
`ℓ.castSucc` and `ℓ.succ`.
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut] {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)] {σ : ℝ → ℝ}

/-- **"`h_{ℓ−1}` does not depend on the weights of block `ℓ`":** the hidden state `h_j` depends only
on `E` and on the reads and writes of the blocks before it. -/
theorem hidden_congr (A : Arch T d L) (S : Fin L → Matrix d d ℝ) (θ θ' : Params A dIn dOut)
    (x : Matrix T dIn ℝ) (j : Fin (L + 1)) (hE : θ'.E = θ.E)
    (hr : ∀ ℓ : Fin L, ℓ.castSucc < j → θ'.read ℓ = θ.read ℓ)
    (hw : ∀ ℓ : Fin L, ℓ.castSucc < j → θ'.write ℓ = θ.write ℓ) :
    hidden A S θ' x j = hidden A S θ x j := by
  induction j using Fin.induction with
  | zero =>
    -- `h_0 = x E`
    rw [hidden_zero, hidden_zero, hE]
  | succ ℓ ih =>
    -- `h_{ℓ+1}` is built from `h_ℓ` and the read and write of block `ℓ`
    have hlt : ℓ.castSucc < ℓ.succ := Fin.castSucc_lt_succ
    rw [hidden_succ, hidden_succ, ih (fun ℓ' h' => hr ℓ' (h'.trans hlt))
      (fun ℓ' h' => hw ℓ' (h'.trans hlt)), hr ℓ hlt, hw ℓ hlt]

omit [Fintype T] [DecidableEq d] in
/-- Helper: a linear map of the parameters is analytic at every point (it is continuous, the space
being finite-dimensional). -/
private theorem analyticAt_params_linear_hz {A : Arch T d L} {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (l : Params A dIn dOut →ₗ[ℝ] F) (θ : Params A dIn dOut) :
    AnalyticAt ℝ l θ := by
  rw [← LinearMap.coe_toContinuousLinearMap' l]
  exact (LinearMap.toContinuousLinearMap l).analyticAt θ

omit [Fintype T] [DecidableEq d] in
/-- Helper: the embedding `θ ↦ E` is analytic. -/
private theorem analyticAt_E_hz {A : Arch T d L} (θ : Params A dIn dOut) :
    AnalyticAt ℝ (fun θ' : Params A dIn dOut => θ'.E) θ :=
  analyticAt_params_linear_hz (F := Matrix dIn d ℝ)
    { toFun := fun θ => θ.E, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl } θ

omit [Fintype T] [DecidableEq d] in
/-- Helper: the read `θ ↦ W_read^ℓ` is analytic. -/
private theorem analyticAt_read_hz {A : Arch T d L} (θ : Params A dIn dOut) (ℓ : Fin L) :
    AnalyticAt ℝ (fun θ' : Params A dIn dOut => θ'.read ℓ) θ :=
  analyticAt_params_linear_hz (F := Matrix d (A.r ℓ) ℝ)
    { toFun := fun θ => θ.read ℓ, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl } θ

omit [Fintype T] [DecidableEq d] in
/-- Helper: the write `θ ↦ W_write^ℓ` is analytic. -/
private theorem analyticAt_write_hz {A : Arch T d L} (θ : Params A dIn dOut) (ℓ : Fin L) :
    AnalyticAt ℝ (fun θ' : Params A dIn dOut => θ'.write ℓ) θ :=
  analyticAt_params_linear_hz (F := Matrix (A.w ℓ) d ℝ)
    { toFun := fun θ => θ.write ℓ, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl } θ

omit [Fintype T] [DecidableEq d] in
/-- Helper: the readout `θ ↦ D` is analytic. -/
private theorem analyticAt_D_hz {A : Arch T d L} (θ : Params A dIn dOut) :
    AnalyticAt ℝ (fun θ' : Params A dIn dOut => θ'.D) θ :=
  analyticAt_params_linear_hz (F := Matrix d dOut ℝ)
    { toFun := fun θ => θ.D, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl } θ

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the product of two matrix-valued maps analytic at a point is analytic there (matrix
multiplication is a continuous bilinear map). -/
private theorem analyticAt_matMul_hz {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
    {f : E → Matrix m n ℝ} {g : E → Matrix n p ℝ} {y : E}
    (hf : AnalyticAt ℝ f y) (hg : AnalyticAt ℝ g y) :
    AnalyticAt ℝ (fun y => f y * g y) y := by
  -- matrix multiplication as a bilinear map
  let B : Matrix m n ℝ →ₗ[ℝ] Matrix n p ℝ →ₗ[ℝ] Matrix m p ℝ :=
    LinearMap.mk₂ ℝ (fun a b => a * b) Matrix.add_mul (fun c a b => Matrix.smul_mul c a b)
      Matrix.mul_add (fun c a b => Matrix.mul_smul a c b)
  -- the same map with continuous linear maps (all spaces are finite-dimensional)
  let B' : Matrix m n ℝ →L[ℝ] Matrix n p ℝ →L[ℝ] Matrix m p ℝ :=
    LinearMap.toContinuousLinearMap
      ((LinearMap.toContinuousLinearMap :
        (Matrix n p ℝ →ₗ[ℝ] Matrix m p ℝ) ≃ₗ[ℝ] (Matrix n p ℝ →L[ℝ] Matrix m p ℝ)).toLinearMap ∘ₗ B)
  have hB : (fun y => f y * g y) = fun y => B' (f y) (g y) := rfl
  rw [hB]
  exact (B'.analyticAt_bilinear (f y, g y)).comp₂ hf hg


omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: `σ` entrywise after a matrix-valued map analytic at a point is analytic there. -/
private theorem analyticAt_map_hz {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m n : Type*} [Fintype m] [Fintype n] (hσa : AnalyticOnNhd ℝ σ Set.univ)
    {f : E → Matrix m n ℝ} {y : E} (hf : AnalyticAt ℝ f y) :
    AnalyticAt ℝ (fun y => (f y).map σ) y := by
  show AnalyticAt ℝ (fun y => fun i => fun j => σ (f y i j)) y
  exact AnalyticAt.pi fun i => AnalyticAt.pi fun j =>
    (hσa _ trivial).comp ((analyticOnNhd_matrix_entry i j (f y) trivial).comp hf)

omit [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: `rmsNorm 0` after a map analytic at a point is analytic there if the value at the
point has no zero row. -/
private theorem analyticAt_rmsNorm_zero_comp_hz {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : E → Matrix T d ℝ} {y : E} (hf : AnalyticAt ℝ f y)
    (h0 : ∀ t, f y t ≠ 0) : AnalyticAt ℝ (fun y => rmsNorm 0 (f y)) y :=
  (analyticAt_rmsNorm_zero (f y) h0).comp hf

/-- **The hidden states are real-analytic in the weights where the earlier ones do not vanish:**
for a real-analytic `σ`, if no row of `h_i`, `i < j`, vanishes at `θ`, then `θ' ↦ h_j` is
real-analytic at `θ`. -/
theorem analyticAt_hidden_rmsNorm_zero (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) (x : Matrix T dIn ℝ)
    (j : Fin (L + 1))
    (h : ∀ i : Fin (L + 1), i < j → ∀ t, hidden (Arch.mlp σ (rmsNorm 0) hid) 0 θ x i t ≠ 0) :
    AnalyticAt ℝ (fun θ' : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut =>
      hidden (Arch.mlp σ (rmsNorm 0) hid) 0 θ' x j) θ := by
  induction j using Fin.induction with
  | zero =>
    -- `h_0 = x E`
    simp only [hidden_zero]
    exact analyticAt_matMul_hz analyticAt_const (analyticAt_E_hz θ)
  | succ ℓ ih =>
    have hlt : ℓ.castSucc < ℓ.succ := Fin.castSucc_lt_succ
    -- `h_ℓ` is analytic at `θ`, and `N = rmsNorm 0` is analytic at `h_ℓ(θ)` (no zero row)
    have hh := ih fun i hi t => h i (hi.trans hlt) t
    have hN := analyticAt_rmsNorm_zero_comp_hz hh (h ℓ.castSucc hlt)
    -- `h_{ℓ+1} = h_ℓ S_ℓ + σ(N(h_ℓ) W_read) W_write`: products, compositions and a sum
    simp only [hidden_succ]
    exact (analyticAt_matMul_hz hh analyticAt_const).add
      (analyticAt_matMul_hz (analyticAt_map_hz hσa
        (analyticAt_matMul_hz hN (analyticAt_read_hz θ ℓ))) (analyticAt_write_hz θ ℓ))

/-- What block `ℓ` reads, `N(h_ℓ) W_read`, is real-analytic in the weights at a parameter at which
no row of `h_0, …, h_ℓ` vanishes. -/
theorem analyticAt_preactivation_rmsNorm_zero (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) (x : Matrix T dIn ℝ)
    (ℓ : Fin L)
    (h : ∀ i : Fin (L + 1), i ≤ ℓ.castSucc →
      ∀ t, hidden (Arch.mlp σ (rmsNorm 0) hid) 0 θ x i t ≠ 0) :
    AnalyticAt ℝ (fun θ' : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut =>
      (rmsNorm 0 (hidden (Arch.mlp σ (rmsNorm 0) hid) 0 θ' x ℓ.castSucc) * θ'.read ℓ :
        Matrix T (hid ℓ) ℝ)) θ := by
  -- `h_ℓ` is analytic at `θ`, and `N = rmsNorm 0` is analytic at `h_ℓ(θ)` (no zero row)
  have hh := analyticAt_hidden_rmsNorm_zero hσa θ x ℓ.castSucc fun i hi => h i hi.le
  have hN := analyticAt_rmsNorm_zero_comp_hz hh (h ℓ.castSucc le_rfl)
  exact analyticAt_matMul_hz hN (analyticAt_read_hz θ ℓ)

/-- **"the outputs `F_X` on the batch are real-analytic on `O_X`", one input:** the output at `x` is
real-analytic in the weights at a parameter at which no row of a hidden state of `x` vanishes. -/
theorem analyticAt_eval_rmsNorm_zero (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) (x : Matrix T dIn ℝ)
    (h : ∀ (i : Fin (L + 1)) (t : T), hidden (Arch.mlp σ (rmsNorm 0) hid) 0 θ x i t ≠ 0) :
    AnalyticAt ℝ (fun θ' : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut =>
      eval (Arch.mlp σ (rmsNorm 0) hid) 0 θ' x) θ := by
  -- `h_L` is analytic at `θ`, and `N = rmsNorm 0` is analytic at `h_L(θ)` (no zero row)
  have hh := analyticAt_hidden_rmsNorm_zero hσa θ x (Fin.last L) fun i _ => h i
  have hN := analyticAt_rmsNorm_zero_comp_hz hh (h (Fin.last L))
  -- the output `N(h_L) D`
  exact analyticAt_matMul_hz hN (analyticAt_D_hz θ)

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: a nonzero row vector `v` times a matrix reaches every row vector `y`
(take `M_{ij} = v_i y_j / (v ⬝ v)`). -/
private theorem exists_vecMul_eq_hz {m n : Type*} [Fintype m] (v : m → ℝ) (hv : v ≠ 0)
    (y : n → ℝ) : ∃ M : Matrix m n ℝ, v ᵥ* M = y := by
  have hvv : v ⬝ᵥ v ≠ 0 := fun h0 => hv (dotProduct_self_eq_zero.1 h0)
  refine ⟨Matrix.of fun i j => (v ⬝ᵥ v)⁻¹ * v i * y j, ?_⟩
  funext j
  have e : (v ᵥ* Matrix.of fun i j => (v ⬝ᵥ v)⁻¹ * v i * y j) j
      = ((v ⬝ᵥ v)⁻¹ * y j) * ∑ i, v i * v i := by
    simp only [Matrix.vecMul, dotProduct, Matrix.of_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e, ← dotProduct, mul_comm, ← mul_assoc, mul_inv_cancel₀ hvv, one_mul]

omit [Fintype T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: RMSNorm with `ε = 0` maps a nonzero row to a nonzero row (a positive multiple). -/
private theorem rmsRow_zero_ne_zero_hz (v : d → ℝ) (hv : v ≠ 0) : rmsRow 0 v ≠ 0 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hv
  have hcard : (0 : ℝ) < Fintype.card d := Nat.cast_pos.2 (Fintype.card_pos_iff.2 ⟨i⟩)
  have hvv : 0 < v ⬝ᵥ v := by
    refine lt_of_le_of_ne (Finset.sum_nonneg fun j _ => mul_self_nonneg (v j)) ?_
    exact fun h0 => hv (dotProduct_self_eq_zero.1 h0.symm)
  have hx : 0 < (v ⬝ᵥ v) / (Fintype.card d : ℝ) + 0 := by
    rw [add_zero]; exact div_pos hvv hcard
  exact smul_ne_zero (inv_ne_zero (Real.sqrt_pos.2 hx).ne') hv

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: if `G` is differentiable at `θ` and is affine along the line `θ + s η`,
`G (θ + s η) = a + s y`, then `𝐃G(θ) η = y`. -/
private theorem fderiv_apply_eq_of_line_hz {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {G : E → F} {θ η : E} {a y : F}
    (hG : DifferentiableAt ℝ G θ) (hline : ∀ s : ℝ, G (θ + s • η) = a + s • y) :
    fderiv ℝ G θ η = y := by
  -- the line `s ↦ θ + s η` has the velocity `η`
  have hl : HasDerivAt (fun s : ℝ => θ + s • η) η 0 := by
    have h := ((hasDerivAt_id (0 : ℝ)).smul_const η).const_add θ
    rw [one_smul] at h
    exact h
  -- the chain rule
  have h1 : HasDerivAt (fun s : ℝ => G (θ + s • η)) (fderiv ℝ G θ η) 0 :=
    hG.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hl (by rw [zero_smul, add_zero])
  -- the explicit formula
  have h2 : HasDerivAt (fun s : ℝ => G (θ + s • η)) y 0 := by
    have h := ((hasDerivAt_id (0 : ℝ)).smul_const y).const_add a
    rw [one_smul] at h
    have e : (fun s : ℝ => G (θ + s • η)) = fun s => a + id s • y := funext hline
    rw [e]
    exact h
  exact h1.unique h2


/-- **"because the derivative with respect to `W_read^ℓ` is onto":** at a parameter at which no row
of `h_0, …, h_ℓ` vanishes, the derivative in the weights of row `t` of `N(h_ℓ) W_read` is onto. -/
theorem surjective_fderiv_preactivation (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) (x : Matrix T dIn ℝ)
    (ℓ : Fin L) (t : T)
    (h : ∀ i : Fin (L + 1), i ≤ ℓ.castSucc →
      ∀ t, hidden (Arch.mlp σ (rmsNorm 0) hid) 0 θ x i t ≠ 0) :
    Function.Surjective
      (fderiv ℝ (fun θ' : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut =>
        (rmsNorm 0 (hidden (Arch.mlp σ (rmsNorm 0) hid) 0 θ' x ℓ.castSucc) * θ'.read ℓ :
          Matrix T (hid ℓ) ℝ) t) θ) := by
  sorry

/-- **"Where `w̃_ℓ ≠ 0`, the derivative of `h_ℓ` with respect to `W_write^ℓ` is onto":** let `σ`
vanish only at `0`. At a parameter at which no row of `h_0, …, h_ℓ` vanishes and row `t` of
`N(h_ℓ) W_read` is not zero, the derivative in the weights of row `t` of `h_{ℓ+1}` is onto. -/
theorem surjective_fderiv_hidden_succ (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (hσ0 : ∀ z : ℝ, σ z = 0 → z = 0)
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) (x : Matrix T dIn ℝ)
    (ℓ : Fin L) (t : T)
    (h : ∀ i : Fin (L + 1), i ≤ ℓ.castSucc →
      ∀ t, hidden (Arch.mlp σ (rmsNorm 0) hid) 0 θ x i t ≠ 0)
    (hg : (rmsNorm 0 (hidden (Arch.mlp σ (rmsNorm 0) hid) 0 θ x ℓ.castSucc) * θ.read ℓ :
      Matrix T (hid ℓ) ℝ) t ≠ 0) :
    Function.Surjective
      (fderiv ℝ (fun θ' : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut =>
        hidden (Arch.mlp σ (rmsNorm 0) hid) 0 θ' x ℓ.succ t) θ) := by
  sorry

end Skips
