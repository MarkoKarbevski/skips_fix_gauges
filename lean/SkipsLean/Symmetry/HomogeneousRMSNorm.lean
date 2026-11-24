import SkipsLean.Symmetry.AtOneState
import SkipsLean.Dimension.ExpOrbit
import SkipsLean.Network.Blocks

/-!
# Positively homogeneous blocks under pre-RMSNorm: more changes of basis

Paper (skips paper): Appendix A.2, Lemma A.3.

"For positively homogeneous blocks and `ε = 0`, more changes of basis preserve the function: every
invertible one before the last hidden state. The next lemma shows this and measures how `ε > 0`
breaks it; Theorem A.17, Theorem B.1 (iv) and the checks of Appendix E use it.

Lemma A.3 (Homogeneous blocks under RMSNorm). Let a skipless network with pre-RMSNorm,
`h_ℓ = B_ℓ(N_ε(h_{ℓ−1}))` for `ℓ = 1, …, L` and `y = N_ε(h_L) D`, have blocks that are positively
homogeneous of degree `k`, and let `r_i² = ‖h_i‖²/d_model`. Apply the change of basis
`G ∈ GL(d_model)` at `h_ℓ` with `ℓ < L`, or the scaling `G = cI` at `h_L` with its read `D`
unchanged. At every input whose hidden states are nonzero, the output becomes `Λy` with a scalar
`Λ > 0`, and (i) `Λ = 1` if `ε = 0` or `G` is orthogonal; (ii) for `G = e^{tS}` with `S`
symmetric and `ℓ < L`,
`d/dt log Λ |_{t=0} = − k^{L−ℓ} (h_ℓ S h_ℓ^⊤)/(d_model (r_ℓ² + ε)) ∏_{i=ℓ+1}^{L} ε/(r_i² + ε)`,
and for the scaling `c = e^t` at `h_L` it is `ε/(r_L² + ε)`."

Stated here, for a skipless network (stream matrices `0`) with `χ = rmsNorm ε` whose fixed maps
are positively homogeneous of degree `k` row by row (`RowHomogeneous`: scaling row `t` of the
input of `f_ℓ` by `c_t > 0` scales row `t` of its output by `c_t^k`; MLP blocks with a positively
homogeneous activation and gated blocks with a positively homogeneous gate are of this kind):

* the scalar `Λ`, one per token, for `ε ≥ 0`: for the change of basis `G` at `h_ℓ`, `ℓ < L`
  (`θ.cobAt ℓ.castSucc G`), and for the scaling at `h_L` with `D` unchanged;
* (i) for `ε = 0`: both leave the function unchanged. (For an orthogonal `G` this is
  `eval_cobAt_rmsNorm`, `Symmetry/AtOneState.lean`, for any blocks.)
* (ii) for `ε > 0`, as the derivative of the output at `t = 0`: since `Λ = 1` at `t = 0`, the
  derivative of `t ↦ Λ(t) y` is `(d/dt log Λ) y`.

Lean has no hypothesis on the hidden states: with Lean's total `N_0` (`N_0(0) = 0`) a zero row
stays a zero row, and for `ε > 0` every factor is positive. In (ii) Lean takes any matrix `S`:
only `h_ℓ S h_ℓ^⊤` enters, which vanishes for an antisymmetric `S`. The formula was checked
numerically (`claude/homogeneous_rmsnorm_check_2026-11-24.py`).
-/

namespace Skips

open Matrix

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]

/-- The fixed maps of the blocks are positively homogeneous of degree `k`, row by row: scaling
row `t` of the input by `c t > 0` scales row `t` of the output by `(c t) ^ k`. -/
def RowHomogeneous (A : Arch T d L) (k : ℕ) : Prop :=
  ∀ (ℓ : Fin L) (c : T → ℝ), (∀ t, 0 < c t) → ∀ M : Matrix T (A.r ℓ) ℝ,
    A.f ℓ (Matrix.of fun t i => c t * M t i) = Matrix.of fun t i => c t ^ k * A.f ℓ M t i

/-- `r² = ‖v‖² / d` for a row `v`. -/
noncomputable def meanSq (v : d → ℝ) : ℝ := (v ⬝ᵥ v) / (Fintype.card d : ℝ)

omit [Fintype T] [Fintype d] [DecidableEq d] in
/-- MLP blocks with an activation that is positively homogeneous of degree `k` (ReLU: `k = 1`,
ReLU²: `k = 2`) are positively homogeneous of degree `k`, row by row. -/
theorem rowHomogeneous_mlp {σ : ℝ → ℝ} {k : ℕ}
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (χ : Matrix T d ℝ → Matrix T d ℝ) (hid : Fin L → Type) [∀ ℓ, Fintype (hid ℓ)] :
    RowHomogeneous (Arch.mlp (T := T) (d := d) σ χ hid) k := by
  -- entry by entry: `σ (c_t m) = c_t^k σ(m)`
  intro ℓ c hc M
  ext t i
  show σ (c t * M t i) = c t ^ k * σ (M t i)
  exact hσ (c t) (M t i) (hc t)

omit [Fintype T] [Fintype d] [DecidableEq d] in
/-- Gated blocks with a gate activation that is positively homogeneous of degree `k` (ReGLU:
`k = 1`) are positively homogeneous of degree `k + 1`, row by row. -/
theorem rowHomogeneous_gated {σ : ℝ → ℝ} {k : ℕ}
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (χ : Matrix T d ℝ → Matrix T d ℝ) (hid : Fin L → Type) [∀ ℓ, Fintype (hid ℓ)] :
    RowHomogeneous (Arch.gated (T := T) (d := d) σ χ hid) (k + 1) := by
  -- entry by entry: `σ (c_t g) (c_t v) = c_t^k σ(g) c_t v = c_t^(k+1) σ(g) v`
  intro ℓ c hc M
  ext t i
  show σ (c t * M t (Sum.inl i)) * (c t * M t (Sum.inr i))
    = c t ^ (k + 1) * (σ (M t (Sum.inl i)) * M t (Sum.inr i))
  rw [hσ _ _ (hc t)]
  ring

variable {A : Arch T d L}

/-! ### One row: the scalars `β` and `γ` -/

omit [DecidableEq d] in
/-- Helper: `N_ε(v) = (√(r² + ε))⁻¹ v`. -/
private theorem rmsRow_eq_hom (ε : ℝ) (v : d → ℝ) :
    rmsRow ε v = (Real.sqrt (meanSq v + ε))⁻¹ • v := rfl

omit [DecidableEq d] in
/-- Helper: `r² ≥ 0`. -/
private theorem meanSq_nonneg_hom (v : d → ℝ) : 0 ≤ meanSq v :=
  div_nonneg (Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)) (Nat.cast_nonneg _)

omit [DecidableEq d] in
/-- Helper: `r² > 0` for a nonzero row. -/
private theorem meanSq_pos_hom {v : d → ℝ} (hv : v ≠ 0) : 0 < meanSq v := by
  obtain ⟨i, -⟩ := Function.ne_iff.mp hv
  have h1 : v ⬝ᵥ v ≠ 0 := fun h => hv (dotProduct_self_eq_zero.mp h)
  have h2 : 0 < (Fintype.card d : ℝ) := Nat.cast_pos.2 (Fintype.card_pos_iff.2 ⟨i⟩)
  exact div_pos (lt_of_le_of_ne (Finset.sum_nonneg fun j _ => mul_self_nonneg (v j)) h1.symm) h2

omit [DecidableEq d] in
/-- Helper: `r²(μ v) = μ² r²(v)`. -/
private theorem meanSq_smul_hom (μ : ℝ) (v : d → ℝ) : meanSq (μ • v) = μ ^ 2 * meanSq v := by
  unfold meanSq
  rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  ring

/-- The scalar of RMSNorm on a row scaled by `μ`: `β = μ √(r² + ε) / √(μ² r² + ε)`. -/
private noncomputable def betaF_hom (ε s μ : ℝ) : ℝ :=
  μ * Real.sqrt (s + ε) / Real.sqrt (μ ^ 2 * s + ε)

/-- Helper: `β > 0` for `μ > 0`, `ε > 0`. -/
private theorem betaF_pos_hom {ε s μ : ℝ} (hε : 0 < ε) (hs : 0 ≤ s) (hμ : 0 < μ) :
    0 < betaF_hom ε s μ :=
  div_pos (mul_pos hμ (Real.sqrt_pos.2 (by linarith)))
    (Real.sqrt_pos.2 (add_pos_of_nonneg_of_pos (mul_nonneg (sq_nonneg μ) hs) hε))

/-- Helper: `β = 1` at `μ = 1`. -/
private theorem betaF_one_hom {ε s : ℝ} (hε : 0 < ε) (hs : 0 ≤ s) : betaF_hom ε s 1 = 1 := by
  unfold betaF_hom
  rw [one_pow, one_mul, one_mul, div_self (Real.sqrt_pos.2 (by linarith)).ne']

omit [DecidableEq d] in
/-- Helper: `N_ε(μ v) = β N_ε(v)` for `ε > 0`. -/
private theorem rmsRow_smul_hom {ε : ℝ} (hε : 0 < ε) (μ : ℝ) (v : d → ℝ) :
    rmsRow ε (μ • v) = betaF_hom ε (meanSq v) μ • rmsRow ε v := by
  have hs := meanSq_nonneg_hom v
  have h1 : 0 < Real.sqrt (meanSq v + ε) := Real.sqrt_pos.2 (by linarith)
  have h2 : 0 < Real.sqrt (μ ^ 2 * meanSq v + ε) :=
    Real.sqrt_pos.2 (add_pos_of_nonneg_of_pos (mul_nonneg (sq_nonneg μ) hs) hε)
  rw [rmsRow_eq_hom, rmsRow_eq_hom, meanSq_smul_hom, smul_smul, smul_smul]
  congr 1
  unfold betaF_hom
  field_simp

omit [DecidableEq d] in
/-- Helper: `N_0(c w) = N_0(w)` for `c > 0` (a copy of the private `rmsRow_zero_smul`). -/
private theorem rmsRow_zero_smul_hom {c : ℝ} (hc : 0 < c) (w : d → ℝ) :
    rmsRow 0 (c • w) = rmsRow 0 w := by
  rw [rmsRow_eq_hom, rmsRow_eq_hom, meanSq_smul_hom, add_zero, add_zero,
    Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc.le, mul_inv, smul_smul]
  congr 1
  rw [mul_comm c⁻¹, mul_assoc, inv_mul_cancel₀ hc.ne', mul_one]

/-- The scalar of RMSNorm after a change of basis `G`: `γ = √(r² + ε) / √(‖v G‖²/d + ε)`. -/
private noncomputable def gammaF_hom (ε s q : ℝ) : ℝ := Real.sqrt (s + ε) / Real.sqrt (q + ε)

/-- Helper: `γ > 0`. -/
private theorem gammaF_pos_hom {ε s q : ℝ} (hs : 0 < s + ε) (hq : 0 < q + ε) :
    0 < gammaF_hom ε s q :=
  div_pos (Real.sqrt_pos.2 hs) (Real.sqrt_pos.2 hq)

/-- Helper: `N_ε(v G) G⁻¹ = γ N_ε(v)`. -/
private theorem rmsRow_vecMul_inv_hom (ε : ℝ) (G : GL d ℝ) (v : d → ℝ)
    (hs : 0 < meanSq v + ε) :
    rmsRow ε (v ᵥ* (G : Matrix d d ℝ)) ᵥ* (↑G⁻¹ : Matrix d d ℝ) =
      gammaF_hom ε (meanSq v) (meanSq (v ᵥ* (G : Matrix d d ℝ))) • rmsRow ε v := by
  have h1 : 0 < Real.sqrt (meanSq v + ε) := Real.sqrt_pos.2 hs
  -- `N_ε(v G) G⁻¹ = (√(‖vG‖²/d + ε))⁻¹ v`
  rw [rmsRow_eq_hom, rmsRow_eq_hom, Matrix.smul_vecMul, Matrix.vecMul_vecMul, Units.mul_inv,
    Matrix.vecMul_one, smul_smul]
  congr 1
  unfold gammaF_hom
  rw [div_eq_mul_inv, mul_right_comm, mul_inv_cancel₀ h1.ne', one_mul]

/-- Helper: for `ε ≥ 0` there is `γ > 0` with `N_ε(v G) G⁻¹ = γ N_ε(v)` (`γ = 1` for `v = 0`). -/
private theorem exists_rmsRow_vecMul_inv_hom {ε : ℝ} (hε : 0 ≤ ε) (G : GL d ℝ) (v : d → ℝ) :
    ∃ γ : ℝ, 0 < γ ∧
      rmsRow ε (v ᵥ* (G : Matrix d d ℝ)) ᵥ* (↑G⁻¹ : Matrix d d ℝ) = γ • rmsRow ε v := by
  by_cases hv : v = 0
  · -- a zero row stays zero
    refine ⟨1, one_pos, ?_⟩
    simp only [hv, Matrix.zero_vecMul, rmsRow_eq_hom, smul_zero]
  · -- `v ≠ 0` and `v G ≠ 0`, so both norms are positive
    have hvG : v ᵥ* (G : Matrix d d ℝ) ≠ 0 := by
      intro h
      apply hv
      have h' := congrArg (· ᵥ* (↑G⁻¹ : Matrix d d ℝ)) h
      simpa only [Matrix.vecMul_vecMul, Units.mul_inv, Matrix.vecMul_one,
        Matrix.zero_vecMul] using h'
    have hs := meanSq_pos_hom hv
    have hq := meanSq_pos_hom hvG
    exact ⟨_, gammaF_pos_hom (by linarith) (by linarith),
      rmsRow_vecMul_inv_hom ε G v (by linarith)⟩

/-! ### Hidden states: rows scaled by positive numbers -/

/-- Row `t` of `M` scaled by `μ t`. -/
private def rowScale_hom {n : Type*} (μ : T → ℝ) (M : Matrix T n ℝ) : Matrix T n ℝ :=
  Matrix.of fun t i => μ t * M t i

omit [Fintype T] in
/-- Helper: scaling rows commutes with a product on the right. -/
private theorem rowScale_mul_hom {n p : Type*} [Fintype n] (μ : T → ℝ) (M : Matrix T n ℝ)
    (W : Matrix n p ℝ) : rowScale_hom μ M * W = rowScale_hom μ (M * W) := by
  ext t j
  simp only [rowScale_hom, Matrix.mul_apply, Matrix.of_apply, Finset.mul_sum, mul_assoc]

omit [Fintype T] [Fintype d] [DecidableEq d] in
/-- Helper: `RowHomogeneous` with `rowScale_hom`. -/
private theorem f_rowScale_hom {k : ℕ} (hf : RowHomogeneous A k) (j : Fin L) (β : T → ℝ)
    (hβ : ∀ t, 0 < β t) (M : Matrix T (A.r j) ℝ) :
    A.f j (rowScale_hom β M) = rowScale_hom (fun t => β t ^ k) (A.f j M) :=
  hf j β hβ M

omit [Fintype T] [DecidableEq d] in
/-- Helper: `N_ε(diag(μ) h) = diag(β) N_ε(h)` for `ε > 0`. -/
private theorem rmsNorm_rowScale_hom {ε : ℝ} (hε : 0 < ε) (μ : T → ℝ) (h : Matrix T d ℝ) :
    rmsNorm ε (rowScale_hom μ h) =
      rowScale_hom (fun t => betaF_hom ε (meanSq (h t)) (μ t)) (rmsNorm ε h) := by
  ext t i
  show rmsRow ε (μ t • h t) i = betaF_hom ε (meanSq (h t)) (μ t) * rmsRow ε (h t) i
  rw [rmsRow_smul_hom hε]
  rfl

omit [Fintype T] [DecidableEq d] in
/-- Helper: `N_0(diag(μ) h) = N_0(h)` for `μ > 0`. -/
private theorem rmsNorm_zero_rowScale_hom (μ : T → ℝ) (hμ : ∀ t, 0 < μ t) (h : Matrix T d ℝ) :
    rmsNorm 0 (rowScale_hom μ h) = rmsNorm 0 h := by
  ext t i
  show rmsRow 0 (μ t • h t) i = rmsRow 0 (h t) i
  rw [rmsRow_zero_smul_hom (hμ t)]

omit [Fintype T] in
/-- Helper: for `ε ≥ 0`, `N_ε(h G) G⁻¹ = diag(γ) N_ε(h)` with `γ > 0`. -/
private theorem exists_rmsNorm_mul_inv_hom {ε : ℝ} (hε : 0 ≤ ε) (G : GL d ℝ)
    (h : Matrix T d ℝ) : ∃ γ : T → ℝ, (∀ t, 0 < γ t) ∧
      rmsNorm ε (h * (G : Matrix d d ℝ)) * (↑G⁻¹ : Matrix d d ℝ) =
        rowScale_hom γ (rmsNorm ε h) := by
  choose γ hγ heq using fun t => exists_rmsRow_vecMul_inv_hom hε G (h t)
  refine ⟨γ, hγ, ?_⟩
  ext t i
  exact congrFun (heq t) i

omit [Fintype T] in
/-- Helper: for `ε > 0`, `N_ε(h G) G⁻¹ = diag(γ) N_ε(h)` with the explicit `γ`. -/
private theorem rmsNorm_mul_inv_hom {ε : ℝ} (hε : 0 < ε) (G : GL d ℝ) (h : Matrix T d ℝ) :
    rmsNorm ε (h * (G : Matrix d d ℝ)) * (↑G⁻¹ : Matrix d d ℝ) =
      rowScale_hom (fun t => gammaF_hom ε (meanSq (h t)) (meanSq (h t ᵥ* (G : Matrix d d ℝ))))
        (rmsNorm ε h) := by
  ext t i
  exact congrFun (rmsRow_vecMul_inv_hom ε G (h t) (by linarith [meanSq_nonneg_hom (h t)])) i

omit [Fintype T] [DecidableEq d] in
/-- Helper: a block whose normalized input is scaled row by row by `β > 0` writes its hidden
state scaled by `β^k`. -/
private theorem hidden_succ_of_read_hom {k : ℕ} (hf : RowHomogeneous A k)
    (θ θ' : Params A dIn dOut) (x : Matrix T dIn ℝ) (j : Fin L) (β : T → ℝ)
    (hβ : ∀ t, 0 < β t)
    (hin : A.χ (hidden A 0 θ' x j.castSucc) * θ'.read j =
      rowScale_hom β (A.χ (hidden A 0 θ x j.castSucc) * θ.read j))
    (hw : θ'.write j = θ.write j) :
    hidden A 0 θ' x j.succ = rowScale_hom (fun t => β t ^ k) (hidden A 0 θ x j.succ) := by
  rw [hidden_succ, hidden_succ, hin, hw, f_rowScale_hom hf j β hβ, rowScale_mul_hom]
  simp only [Pi.zero_apply, Matrix.mul_zero, zero_add]

omit [Fintype T] in
/-- Helper: before the hidden state `h_j`, the change of basis at `h_j` changes nothing. -/
private theorem hidden_cobAt_of_lt_hom (θ : Params A dIn dOut) (x : Matrix T dIn ℝ)
    (j : Fin (L + 1)) (G : GL d ℝ) :
    ∀ i : Fin (L + 1), i < j → hidden A 0 (θ.cobAt j G) x i = hidden A 0 θ x i := by
  intro i
  induction i using Fin.induction with
  | zero =>
    intro hj
    rw [hidden_zero, hidden_zero, θ.cobAt_E_of_ne G hj.ne']
  | succ i ih =>
    intro hj
    have h1 : i.castSucc < j := lt_trans (Fin.castSucc_lt_succ (i := i)) hj
    rw [hidden_succ, hidden_succ, ih h1, θ.cobAt_read_of_ne G i h1.ne',
      θ.cobAt_write_of_ne G i hj.ne']

omit [Fintype T] in
/-- Helper: the change of basis `G` at `h_j` turns `h_j` into `h_j G`. -/
private theorem hidden_cobAt_self_hom (θ : Params A dIn dOut) (x : Matrix T dIn ℝ)
    (j : Fin (L + 1)) (G : GL d ℝ) :
    hidden A 0 (θ.cobAt j G) x j = hidden A 0 θ x j * (G : Matrix d d ℝ) := by
  cases j using Fin.cases with
  | zero => rw [hidden_zero, hidden_zero, θ.cobAt_E_zero, Matrix.mul_assoc]
  | succ i =>
    rw [hidden_succ, hidden_succ,
      hidden_cobAt_of_lt_hom θ x i.succ G i.castSucc (Fin.castSucc_lt_succ (i := i)),
      θ.cobAt_read_of_ne G i (Fin.castSucc_lt_succ (i := i)).ne', θ.cobAt_write_succ]
    simp only [Pi.zero_apply, Matrix.mul_zero, zero_add, Matrix.mul_assoc]

omit [Fintype T] [Fintype dIn] in
/-- Helper: after block `ℓ`, the change of basis at `h_ℓ` changes no weight. -/
private theorem cobAt_read_write_hom (θ : Params A dIn dOut) (ℓ : Fin L) (G : GL d ℝ)
    (j : Fin L) (hj : ℓ.succ ≤ j.castSucc) :
    (θ.cobAt ℓ.castSucc G).read j = θ.read j ∧ (θ.cobAt ℓ.castSucc G).write j = θ.write j := by
  rw [Fin.le_iff_val_le_val, Fin.val_succ, Fin.val_castSucc] at hj
  refine ⟨θ.cobAt_read_of_ne G j ?_, θ.cobAt_write_of_ne G j ?_⟩
  · rw [ne_eq, Fin.ext_iff, Fin.val_castSucc, Fin.val_castSucc]; omega
  · rw [ne_eq, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ]; omega

omit [Fintype T] in
/-- Helper: block `ℓ` after the change of basis `G` at `h_ℓ`: it reads `N(h G) G⁻¹ W`; if
`N(h G) G⁻¹ = diag(γ) N(h)`, it writes `diag(γ^k) h_{ℓ+1}`. -/
private theorem hidden_succ_cobAt_hom {k : ℕ} (hf : RowHomogeneous A k)
    (θ : Params A dIn dOut) (x : Matrix T dIn ℝ) (ℓ : Fin L) (G : GL d ℝ) (γ : T → ℝ)
    (hγ : ∀ t, 0 < γ t)
    (heq : A.χ (hidden A 0 θ x ℓ.castSucc * (G : Matrix d d ℝ)) * (↑G⁻¹ : Matrix d d ℝ) =
      rowScale_hom γ (A.χ (hidden A 0 θ x ℓ.castSucc))) :
    hidden A 0 (θ.cobAt ℓ.castSucc G) x ℓ.succ =
      rowScale_hom (fun t => γ t ^ k) (hidden A 0 θ x ℓ.succ) := by
  refine hidden_succ_of_read_hom hf θ _ x ℓ γ hγ ?_
    (θ.cobAt_write_of_ne G ℓ (Fin.castSucc_lt_succ (i := ℓ)).ne)
  rw [hidden_cobAt_self_hom, θ.cobAt_read_castSucc, ← Matrix.mul_assoc, heq, rowScale_mul_hom]

omit [Fintype T] [DecidableEq d] in
/-- Helper: if `χ` agrees on `h_{i₀}` and the later weights agree, `χ` agrees on every later
hidden state (`i = i₀ + m`). -/
private theorem chi_hidden_eq_hom (θ θ' : Params A dIn dOut) (x : Matrix T dIn ℝ)
    (i₀ : Fin (L + 1))
    (hrw : ∀ j : Fin L, i₀ ≤ j.castSucc → θ'.read j = θ.read j ∧ θ'.write j = θ.write j)
    (h₀ : A.χ (hidden A 0 θ' x i₀) = A.χ (hidden A 0 θ x i₀)) :
    ∀ (m : ℕ) (i : Fin (L + 1)), (i : ℕ) = i₀ + m →
      A.χ (hidden A 0 θ' x i) = A.χ (hidden A 0 θ x i) := by
  intro m
  induction m with
  | zero =>
    intro i hi
    rw [show i = i₀ from Fin.ext hi]
    exact h₀
  | succ m ih =>
    intro i hi
    have hi' := i.isLt
    obtain ⟨j, hj⟩ : ∃ j : Fin L, (j : ℕ) = i₀ + m := ⟨⟨i₀ + m, by omega⟩, rfl⟩
    have hle : i₀ ≤ j.castSucc := by rw [Fin.le_iff_val_le_val, Fin.val_castSucc]; omega
    rw [show i = j.succ from Fin.ext (by rw [Fin.val_succ]; omega), hidden_succ, hidden_succ]
    simp only [Pi.zero_apply, Matrix.mul_zero, zero_add]
    rw [ih j.castSucc (by rw [Fin.val_castSucc]; omega), (hrw j hle).1, (hrw j hle).2]

omit [Fintype T] in
/-- Helper, Lemma A.3 (i) for `ε = 0`: the change of basis `G` at `h_ℓ`, `ℓ < L`. -/
private theorem eval_cobAt_zero_hom (hA : A.χ = rmsNorm 0) {k : ℕ} (hf : RowHomogeneous A k)
    (θ : Params A dIn dOut) (ℓ : Fin L) (G : GL d ℝ) (x : Matrix T dIn ℝ) :
    eval A 0 (θ.cobAt ℓ.castSucc G) x = eval A 0 θ x := by
  -- block `ℓ` reads `N_0(h G) G⁻¹ = diag(γ) N_0(h)` and writes `diag(γ^k) h_{ℓ+1}`
  obtain ⟨γ, hγ, heq⟩ := exists_rmsNorm_mul_inv_hom le_rfl G (hidden A 0 θ x ℓ.castSucc)
  rw [← hA] at heq
  have h1 := hidden_succ_cobAt_hom hf θ x ℓ G γ hγ heq
  -- `N_0` forgets the positive scalars; from then on the hidden states agree
  have h2 : A.χ (hidden A 0 (θ.cobAt ℓ.castSucc G) x ℓ.succ) = A.χ (hidden A 0 θ x ℓ.succ) := by
    rw [h1, hA, rmsNorm_zero_rowScale_hom _ fun t => pow_pos (hγ t) k]
  have hL := ℓ.isLt
  have h3 := chi_hidden_eq_hom θ _ x ℓ.succ (cobAt_read_write_hom θ ℓ G) h2 (L - (ℓ + 1))
    (Fin.last L) (by rw [Fin.val_last, Fin.val_succ]; omega)
  rw [eval, eval, h3, θ.cobAt_D_of_ne G (Fin.castSucc_lt_last ℓ).ne]

omit [Fintype T] in
/-- Helper: `h (c I) = diag(c) h`. -/
private theorem mul_smul_one_hom (h : Matrix T d ℝ) (c : ℝ) :
    h * (c • (1 : Matrix d d ℝ)) = rowScale_hom (fun _ => c) h := by
  ext t i
  simp only [Matrix.mul_smul, Matrix.mul_one, rowScale_hom, Matrix.of_apply, Matrix.smul_apply,
    smul_eq_mul]

omit [Fintype T] in
/-- Helper: the output after the change of basis `G` at `h_L` with `D` unchanged. -/
private theorem eval_scale_last_eq_hom (θ : Params A dIn dOut) (G : GL d ℝ)
    (x : Matrix T dIn ℝ) :
    eval A 0 { θ.cobAt (Fin.last L) G with D := θ.D } x =
      A.χ (hidden A 0 θ x (Fin.last L) * (G : Matrix d d ℝ)) * θ.D := by
  rw [← hidden_cobAt_self_hom θ x (Fin.last L) G]
  rfl

omit [Fintype T] in
/-- Helper, Lemma A.3 (i) for `ε = 0`: the scaling at `h_L`. -/
private theorem eval_scale_last_zero_hom (hA : A.χ = rmsNorm 0) (θ : Params A dIn dOut) {c : ℝ}
    (hc : 0 < c) (G : GL d ℝ) (hG : (G : Matrix d d ℝ) = c • (1 : Matrix d d ℝ))
    (x : Matrix T dIn ℝ) :
    eval A 0 { θ.cobAt (Fin.last L) G with D := θ.D } x = eval A 0 θ x := by
  rw [eval_scale_last_eq_hom, eval, hG, mul_smul_one_hom, hA,
    rmsNorm_zero_rowScale_hom _ fun _ => hc]


/-! ### The scalars along the network, for `ε > 0` -/

omit [Fintype T] [DecidableEq d] in
/-- Helper: `β` has the derivative `ε/(r² + ε)` at `μ = 1`. -/
private theorem hasDerivAt_betaF_hom {ε s : ℝ} (hε : 0 < ε) (hs : 0 ≤ s) :
    HasDerivAt (betaF_hom ε s) (ε / (s + ε)) 1 := by
  have hp : 0 < s + ε := by linarith
  have hr : 0 < Real.sqrt (s + ε) := Real.sqrt_pos.2 hp
  -- `a ↦ a² s + ε` has the derivative `2 s` at `1`
  have h1 : HasDerivAt (fun a : ℝ => a ^ 2 * s + ε) (2 * s) 1 := by
    have h := ((hasDerivAt_pow 2 (1 : ℝ)).mul_const s).add_const ε
    convert h using 1
    norm_num
  have h2 := h1.sqrt (by simp only [one_pow, one_mul]; exact hp.ne')
  have h3 := ((hasDerivAt_id' (1 : ℝ)).mul_const (Real.sqrt (s + ε))).fun_div h2
    (by simp only [one_pow, one_mul]; exact hr.ne')
  refine (h3 : HasDerivAt (betaF_hom ε s) _ 1).congr_deriv ?_
  have hsq : Real.sqrt (s + ε) ^ 2 = s + ε := Real.sq_sqrt hp.le
  simp only [one_pow, one_mul]
  field_simp
  rw [hsq]
  ring

omit [Fintype T] [DecidableEq d] in
/-- Helper: the scalars along the network for `ε > 0`. If a hidden state `h_{i₀}` becomes
`diag(μ) h_{i₀}` with `μ > 0` and the later weights are unchanged, then `h_i`, `i = i₀ + m`,
becomes `diag(F(μ)) h_i`, where `F` (one function per token) depends only on `θ` and `x`:
`F = 1` at `1`, with the derivative `k^m ∏_{i₀ ≤ j < i} ε/(r_j² + ε)` there. -/
private theorem exists_scale_fun_hom {ε : ℝ} (hε : 0 < ε) (hA : A.χ = rmsNorm ε) {k : ℕ}
    (hf : RowHomogeneous A k) (θ : Params A dIn dOut) (x : Matrix T dIn ℝ)
    (i₀ : Fin (L + 1)) :
    ∀ (m : ℕ) (i : Fin (L + 1)), (i : ℕ) = i₀ + m → ∃ F : T → ℝ → ℝ,
      (∀ t a, 0 < a → 0 < F t a) ∧ (∀ t, F t 1 = 1) ∧
      (∀ t, HasDerivAt (F t) ((k : ℝ) ^ m * ∏ j ∈ Finset.univ.filter
          (fun j : Fin (L + 1) => i₀ ≤ j ∧ j < i),
          ε / (meanSq (hidden A 0 θ x j t) + ε)) 1) ∧
      ∀ (θ' : Params A dIn dOut) (μ : T → ℝ), (∀ t, 0 < μ t) →
        (∀ j : Fin L, i₀ ≤ j.castSucc → θ'.read j = θ.read j ∧ θ'.write j = θ.write j) →
        hidden A 0 θ' x i₀ = rowScale_hom μ (hidden A 0 θ x i₀) →
        hidden A 0 θ' x i = rowScale_hom (fun t => F t (μ t)) (hidden A 0 θ x i) := by
  intro m
  induction m with
  | zero =>
    -- `i = i₀`: `F(a) = a`
    intro i hi
    obtain rfl : i = i₀ := Fin.ext hi
    refine ⟨fun _ a => a, fun _ _ ha => ha, fun _ => rfl, fun t => ?_,
      fun θ' μ _ _ h0 => h0⟩
    have hP : ∏ j ∈ Finset.univ.filter (fun j : Fin (L + 1) => i ≤ j ∧ j < i),
        ε / (meanSq (hidden A 0 θ x j t) + ε) = 1 :=
      Finset.prod_eq_one fun j hj => absurd (Finset.mem_filter.1 hj).2.2
        (not_lt.2 (Finset.mem_filter.1 hj).2.1)
    rw [hP, pow_zero, one_mul]
    exact hasDerivAt_id' 1
  | succ m ih =>
    -- `i = j + 1` for the block `j` that reads `h_{i₀ + m}`
    intro i hi
    have hi' := i.isLt
    obtain ⟨j, hj⟩ : ∃ j : Fin L, (j : ℕ) = i₀ + m := ⟨⟨i₀ + m, by omega⟩, rfl⟩
    obtain rfl : i = j.succ := Fin.ext (by rw [Fin.val_succ]; omega)
    obtain ⟨F, hFpos, hF1, hFd, hFrel⟩ := ih j.castSucc (by rw [Fin.val_castSucc]; omega)
    have hle : i₀ ≤ j.castSucc := by rw [Fin.le_iff_val_le_val, Fin.val_castSucc]; omega
    -- the new scalar is `β(F(μ))^k`
    refine ⟨fun t a => betaF_hom ε (meanSq (hidden A 0 θ x j.castSucc t)) (F t a) ^ k,
      fun t a ha => pow_pos (betaF_pos_hom hε (meanSq_nonneg_hom _) (hFpos t a ha)) k,
      fun t => by dsimp only; rw [hF1, betaF_one_hom hε (meanSq_nonneg_hom _), one_pow],
      fun t => ?_, ?_⟩
    · -- the chain rule: one more factor `k ε/(r_j² + ε)`
      have hb := hasDerivAt_betaF_hom hε (meanSq_nonneg_hom (hidden A 0 θ x j.castSucc t))
      have h2 := (hb.comp_of_eq 1 (hFd t) (hF1 t).symm).fun_pow k
      refine (h2 : HasDerivAt (fun a => betaF_hom ε (meanSq (hidden A 0 θ x j.castSucc t))
        (F t a) ^ k) _ 1).congr_deriv ?_
      have hfil : Finset.univ.filter (fun j' : Fin (L + 1) => i₀ ≤ j' ∧ j' < j.succ) =
          insert j.castSucc
            (Finset.univ.filter (fun j' : Fin (L + 1) => i₀ ≤ j' ∧ j' < j.castSucc)) := by
        ext j'
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
          Fin.ext_iff, Fin.le_iff_val_le_val, Fin.lt_def, Fin.val_succ,
          Fin.val_castSucc]
        omega
      have hnot : j.castSucc ∉
          Finset.univ.filter (fun j' : Fin (L + 1) => i₀ ≤ j' ∧ j' < j.castSucc) := by
        simp
      rw [hfil, Finset.prod_insert hnot, Function.comp_apply, hF1,
        betaF_one_hom hε (meanSq_nonneg_hom _), one_pow, pow_succ]
      ring
    · -- block `j` reads `N_ε(diag(F(μ)) h) W = diag(β) N_ε(h) W`
      intro θ' μ hμ hrw h0
      have h := hFrel θ' μ hμ hrw h0
      exact hidden_succ_of_read_hom hf θ θ' x j
        (fun t => betaF_hom ε (meanSq (hidden A 0 θ x j.castSucc t)) (F t (μ t)))
        (fun t => betaF_pos_hom hε (meanSq_nonneg_hom _) (hFpos t _ (hμ t)))
        (by rw [hA, h, rmsNorm_rowScale_hom hε, (hrw j hle).1, rowScale_mul_hom])
        (hrw j hle).2

omit [Fintype T] in
/-- **Lemma A.3, the scalar `Λ`, for a change of basis before the last hidden state:** for
`ε ≥ 0` and blocks that are positively homogeneous of degree `k`, the change of basis `G` at
`h_ℓ`, `ℓ < L`, multiplies the output at every token by a positive number. -/
theorem exists_pos_smul_eval_cobAt_of_rowHomogeneous {ε : ℝ} (hε : 0 ≤ ε)
    (hA : A.χ = rmsNorm ε) {k : ℕ} (hf : RowHomogeneous A k) (θ : Params A dIn dOut)
    (ℓ : Fin L) (G : GL d ℝ) (x : Matrix T dIn ℝ) :
    ∃ Λ : T → ℝ, (∀ t, 0 < Λ t) ∧
      ∀ t, eval A 0 (θ.cobAt ℓ.castSucc G) x t = Λ t • eval A 0 θ x t := by
  rcases hε.eq_or_lt with h0 | hpos
  · -- `ε = 0`: the function is unchanged (part (i)), `Λ = 1`
    subst h0
    exact ⟨fun _ => 1, fun _ => one_pos,
      fun t => by rw [eval_cobAt_zero_hom hA hf θ ℓ G x, one_smul]⟩
  · -- block `ℓ` reads `N_ε(h G) G⁻¹ W = diag(γ) N_ε(h) W` and writes `diag(γ^k) h_{ℓ+1}`
    obtain ⟨γ, hγ, heq⟩ := exists_rmsNorm_mul_inv_hom hε G (hidden A 0 θ x ℓ.castSucc)
    rw [← hA] at heq
    have h1 := hidden_succ_cobAt_hom hf θ x ℓ G γ hγ heq
    -- the later blocks give `h_L ↦ diag(μ_L) h_L`, and the readout reads `diag(β_L) N_ε(h_L)`
    have hL := ℓ.isLt
    obtain ⟨F, hFpos, -, -, hFrel⟩ := exists_scale_fun_hom hpos hA hf θ x ℓ.succ (L - (ℓ + 1))
      (Fin.last L) (by rw [Fin.val_last, Fin.val_succ]; omega)
    have h2 := hFrel _ _ (fun t => pow_pos (hγ t) k) (cobAt_read_write_hom θ ℓ G) h1
    refine ⟨fun t => betaF_hom ε (meanSq (hidden A 0 θ x (Fin.last L) t)) (F t (γ t ^ k)),
      fun t => betaF_pos_hom hpos (meanSq_nonneg_hom _) (hFpos t _ (pow_pos (hγ t) k)),
      fun t => ?_⟩
    rw [eval, eval, h2, hA, rmsNorm_rowScale_hom hpos,
      θ.cobAt_D_of_ne G (Fin.castSucc_lt_last ℓ).ne, rowScale_mul_hom]
    rfl

omit [Fintype T] in
/-- **Lemma A.3, the scalar `Λ`, for the scaling at the last hidden state:** for `ε ≥ 0`, the
scaling `G = cI`, `c > 0`, at `h_L` with the readout `D` unchanged multiplies the output at every
token by a positive number. -/
theorem exists_pos_smul_eval_scale_last {ε : ℝ} (hε : 0 ≤ ε) (hA : A.χ = rmsNorm ε)
    (θ : Params A dIn dOut) {c : ℝ} (hc : 0 < c) (G : GL d ℝ)
    (hG : (G : Matrix d d ℝ) = c • (1 : Matrix d d ℝ)) (x : Matrix T dIn ℝ) :
    ∃ Λ : T → ℝ, (∀ t, 0 < Λ t) ∧
      ∀ t, eval A 0 { θ.cobAt (Fin.last L) G with D := θ.D } x t = Λ t • eval A 0 θ x t := by
  rcases hε.eq_or_lt with h0 | hpos
  · -- `ε = 0`: the function is unchanged (part (i)), `Λ = 1`
    subst h0
    exact ⟨fun _ => 1, fun _ => one_pos,
      fun t => by rw [eval_scale_last_zero_hom hA θ hc G hG x, one_smul]⟩
  · -- `h_L ↦ diag(c) h_L`, and the readout reads `diag(β_L) N_ε(h_L)`
    refine ⟨fun t => betaF_hom ε (meanSq (hidden A 0 θ x (Fin.last L) t)) c,
      fun t => betaF_pos_hom hpos (meanSq_nonneg_hom _) hc, fun t => ?_⟩
    rw [eval_scale_last_eq_hom, hG, mul_smul_one_hom, hA, rmsNorm_rowScale_hom hpos,
      rowScale_mul_hom, eval, hA]
    rfl

omit [Fintype T] in
/-- **Lemma A.3 (i) for `ε = 0`, a change of basis before the last hidden state:** for blocks
that are positively homogeneous of degree `k` under pre-RMSNorm with `ε = 0`, every invertible
change of basis at `h_ℓ`, `ℓ < L`, preserves the function. -/
theorem eval_cobAt_rmsNorm_zero_of_rowHomogeneous (hA : A.χ = rmsNorm 0) {k : ℕ}
    (hf : RowHomogeneous A k) (θ : Params A dIn dOut) (ℓ : Fin L) (G : GL d ℝ)
    (x : Matrix T dIn ℝ) :
    eval A 0 (θ.cobAt ℓ.castSucc G) x = eval A 0 θ x := by
  exact eval_cobAt_zero_hom hA hf θ ℓ G x

omit [Fintype T] in
/-- **Lemma A.3 (i) for `ε = 0`, the scaling at the last hidden state:** under pre-RMSNorm with
`ε = 0`, the scaling `G = cI`, `c > 0`, at `h_L` with the readout `D` unchanged preserves the
function. -/
theorem eval_scale_last_rmsNorm_zero (hA : A.χ = rmsNorm 0) (θ : Params A dIn dOut) {c : ℝ}
    (hc : 0 < c) (G : GL d ℝ) (hG : (G : Matrix d d ℝ) = c • (1 : Matrix d d ℝ))
    (x : Matrix T dIn ℝ) :
    eval A 0 { θ.cobAt (Fin.last L) G with D := θ.D } x = eval A 0 θ x := by
  exact eval_scale_last_zero_hom hA θ hc G hG x

/-! ### Lemma A.3 (ii): the derivatives -/

set_option backward.isDefEq.respectTransparency false in
/-- Helper: the derivative at `τ = 0` of an entry of `exp (τ Y)` is the entry of `Y` (a copy of
the private `hasDerivAt_exp_smul_apply` of `Dimension/UpperBoundRMSNorm.lean`). -/
private theorem hasDerivAt_exp_smul_apply_hom (Y : Matrix d d ℝ) (i j : d) :
    HasDerivAt (fun τ : ℝ => NormedSpace.exp (τ • Y) i j) (Y i j) 0 := by
  let _ : NormedRing (Matrix d d ℝ) := Matrix.linftyOpNormedRing
  let _ : NormedAlgebra ℝ (Matrix d d ℝ) := Matrix.linftyOpNormedAlgebra
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) Y (0 : ℝ)
  rw [zero_smul, NormedSpace.exp_zero, one_mul] at h
  exact (LinearMap.toContinuousLinearMap
    (Matrix.entryLinearMap ℝ ℝ i j)).hasFDerivAt.comp_hasDerivAt 0 h

/-- Helper: `τ ↦ r²(v e^{τ S})` has the derivative `2 v S vᵀ / d` at `0`. -/
private theorem hasDerivAt_meanSq_exp_hom (v : d → ℝ) (S : Matrix d d ℝ) :
    HasDerivAt (fun τ : ℝ => meanSq (v ᵥ* NormedSpace.exp (τ • S)))
      (2 * (v ⬝ᵥ (S *ᵥ v)) / (Fintype.card d : ℝ)) 0 := by
  -- each entry of `v e^{τ S}` has the derivative `(v S)_j`
  have hw : ∀ j, HasDerivAt (fun τ : ℝ => (v ᵥ* NormedSpace.exp (τ • S)) j)
      ((v ᵥ* S) j) 0 := by
    intro j
    simp only [Matrix.vecMul, dotProduct]
    exact HasDerivAt.fun_sum fun i _ => (hasDerivAt_exp_smul_apply_hom S i j).const_mul (v i)
  -- `r² = (∑_j w_j w_j) / d`
  have hs := (HasDerivAt.fun_sum fun j (_ : j ∈ Finset.univ) => (hw j).fun_mul (hw j)).div_const
    (Fintype.card d : ℝ)
  refine (hs : HasDerivAt (fun τ : ℝ => meanSq (v ᵥ* NormedSpace.exp (τ • S))) _ 0).congr_deriv
    ?_
  simp only [zero_smul, NormedSpace.exp_zero, Matrix.vecMul_one]
  rw [Matrix.dotProduct_mulVec, dotProduct, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by ring

/-- Helper: `γ(τ) = √(r² + ε)/√(q(τ) + ε)` has the derivative `-q'/(2 (r² + ε))` at `0` if
`q(0) = r²`. -/
private theorem hasDerivAt_gammaF_hom {ε s : ℝ} (hp : 0 < s + ε) {q : ℝ → ℝ} {q' : ℝ}
    (hq : HasDerivAt q q' 0) (hq0 : q 0 = s) :
    HasDerivAt (fun τ => gammaF_hom ε s (q τ)) (-q' / (2 * (s + ε))) 0 := by
  have hr : 0 < Real.sqrt (s + ε) := Real.sqrt_pos.2 hp
  have h1 := (hq.add_const ε).sqrt (by simp only [hq0]; exact hp.ne')
  have h2 := (hasDerivAt_const (0 : ℝ) (Real.sqrt (s + ε))).fun_div h1
    (by simp only [hq0]; exact hr.ne')
  refine (h2 : HasDerivAt (fun τ => gammaF_hom ε s (q τ)) _ 0).congr_deriv ?_
  have hsq : Real.sqrt (s + ε) ^ 2 = s + ε := Real.sq_sqrt hp.le
  rw [hq0, hsq]
  field_simp
  ring

/-- Helper: `τ ↦ c(τ) y` has the derivative `c' y` at `0`. The space `n → ℝ` need not be normed
(`n` need not be finite), so the chain rule is the one for a continuous linear map into a
topological vector space. -/
private theorem hasDerivAt_smul_const_hom {n : Type*} {c : ℝ → ℝ} {c' : ℝ}
    (hc : HasDerivAt c c' 0) (y : n → ℝ) : HasDerivAt (fun τ => c τ • y) (c' • y) 0 := by
  have h := (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) y).hasFDerivAt.comp (0 : ℝ)
    (hasDerivAt_iff_hasFDerivAt.1 hc)
  have e1 : (fun τ => c τ • y) = ⇑(ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) y) ∘ c := by
    funext τ
    simp
  have e2 : ContinuousLinearMap.toSpanSingleton ℝ (c' • y) =
      (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) y).comp
        (ContinuousLinearMap.toSpanSingleton ℝ c') := by
    ext
    simp
  rw [hasDerivAt_iff_hasFDerivAt, e1, e2]
  exact h

omit [Fintype T] in
/-- Helper, Lemma A.3 (ii) for a curve `G(τ)` of changes of basis at `h_ℓ`, `ℓ < L`, along which
`r²(h_ℓ G(τ))` (token `t`) has the derivative `q'` at `0` and `G(0)` keeps `r_ℓ²`. -/
private theorem hasDerivAt_eval_cobAt_hom {ε : ℝ} (hε : 0 < ε) (hA : A.χ = rmsNorm ε) {k : ℕ}
    (hf : RowHomogeneous A k) (θ : Params A dIn dOut) (ℓ : Fin L) (G : ℝ → GL d ℝ)
    (x : Matrix T dIn ℝ) (t : T) {q' : ℝ}
    (hq : HasDerivAt
      (fun τ => meanSq (hidden A 0 θ x ℓ.castSucc t ᵥ* (G τ : Matrix d d ℝ))) q' 0)
    (hq0 : meanSq (hidden A 0 θ x ℓ.castSucc t ᵥ* (G 0 : Matrix d d ℝ)) =
      meanSq (hidden A 0 θ x ℓ.castSucc t)) :
    HasDerivAt (fun τ => eval A 0 (θ.cobAt ℓ.castSucc (G τ)) x t)
      (((k : ℝ) ^ (L - (ℓ : ℕ)) * (-q' / (2 * (meanSq (hidden A 0 θ x ℓ.castSucc t) + ε)))
          * ∏ i ∈ Finset.univ.filter (fun i : Fin (L + 1) => ℓ.castSucc < i),
              ε / (meanSq (hidden A 0 θ x i t) + ε))
        • eval A 0 θ x t) 0 := by
  have hL := ℓ.isLt
  -- block `ℓ` reads `N_ε(h G) G⁻¹ = diag(γ) N_ε(h)` and writes `diag(γ^k) h_{ℓ+1}`
  let γ : ℝ → T → ℝ := fun τ t' => gammaF_hom ε (meanSq (hidden A 0 θ x ℓ.castSucc t'))
    (meanSq (hidden A 0 θ x ℓ.castSucc t' ᵥ* (G τ : Matrix d d ℝ)))
  have hγ : ∀ τ t', 0 < γ τ t' := fun τ t' =>
    gammaF_pos_hom (by linarith [meanSq_nonneg_hom (hidden A 0 θ x ℓ.castSucc t')])
      (by linarith [meanSq_nonneg_hom (hidden A 0 θ x ℓ.castSucc t' ᵥ* (G τ : Matrix d d ℝ))])
  have h1 : ∀ τ, hidden A 0 (θ.cobAt ℓ.castSucc (G τ)) x ℓ.succ =
      rowScale_hom (fun t' => γ τ t' ^ k) (hidden A 0 θ x ℓ.succ) := fun τ => by
    have heq := rmsNorm_mul_inv_hom hε (G τ) (hidden A 0 θ x ℓ.castSucc)
    rw [← hA] at heq
    exact hidden_succ_cobAt_hom hf θ x ℓ (G τ) (γ τ) (hγ τ) heq
  -- the later blocks and the readout: `y ↦ β_L(F(γ^k)) y`
  obtain ⟨F, hFpos, hF1, hFd, hFrel⟩ := exists_scale_fun_hom hε hA hf θ x ℓ.succ
    (L - (ℓ + 1)) (Fin.last L) (by rw [Fin.val_last, Fin.val_succ]; omega)
  have hout : ∀ τ, eval A 0 (θ.cobAt ℓ.castSucc (G τ)) x t =
      (betaF_hom ε (meanSq (hidden A 0 θ x (Fin.last L) t)) ∘ (F t ∘ fun τ => γ τ t ^ k)) τ
        • eval A 0 θ x t := fun τ => by
    have h2 := hFrel _ _ (fun t' => pow_pos (hγ τ t') k) (cobAt_read_write_hom θ ℓ (G τ))
      (h1 τ)
    rw [eval, eval, h2, hA, rmsNorm_rowScale_hom hε,
      θ.cobAt_D_of_ne _ (Fin.castSucc_lt_last ℓ).ne, rowScale_mul_hom]
    rfl
  -- the chain rule along `γ ↦ γ^k ↦ F ↦ β_L`
  have hs := meanSq_nonneg_hom (hidden A 0 θ x ℓ.castSucc t)
  have hγ0 : γ 0 t = 1 := by
    show gammaF_hom ε _ _ = 1
    rw [hq0]
    exact div_self (Real.sqrt_pos.2 (by linarith)).ne'
  have hγd : HasDerivAt (fun τ => γ τ t)
      (-q' / (2 * (meanSq (hidden A 0 θ x ℓ.castSucc t) + ε))) 0 :=
    hasDerivAt_gammaF_hom (by linarith) hq hq0
  have hF := (hFd t).comp_of_eq 0 (hγd.fun_pow k) (by simp only [hγ0, one_pow])
  have hB := (hasDerivAt_betaF_hom hε
    (meanSq_nonneg_hom (hidden A 0 θ x (Fin.last L) t))).comp_of_eq 0 hF
    (by simp only [Function.comp_apply, hγ0, one_pow, hF1])
  have hfun : (fun τ => eval A 0 (θ.cobAt ℓ.castSucc (G τ)) x t) = fun τ =>
      (betaF_hom ε (meanSq (hidden A 0 θ x (Fin.last L) t)) ∘ (F t ∘ fun τ => γ τ t ^ k)) τ
        • eval A 0 θ x t := funext hout
  rw [hfun]
  convert hasDerivAt_smul_const_hom hB (eval A 0 θ x t) using 2
  -- the scalar: `ε/(r_L² + ε) · k^{L-ℓ-1} ∏_{ℓ < j < L} ε/(r_j² + ε) · k γ'`
  have hfil : Finset.univ.filter (fun i : Fin (L + 1) => ℓ.castSucc < i) =
      insert (Fin.last L) (Finset.univ.filter
        (fun j : Fin (L + 1) => ℓ.succ ≤ j ∧ j < Fin.last L)) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff,
      Fin.le_iff_val_le_val, Fin.lt_def, Fin.val_succ, Fin.val_castSucc, Fin.val_last]
    have := j.isLt
    omega
  have hnot : Fin.last L ∉ Finset.univ.filter
      (fun j : Fin (L + 1) => ℓ.succ ≤ j ∧ j < Fin.last L) := by simp
  have hk : L - (ℓ : ℕ) = (L - (ℓ + 1)) + 1 := by omega
  rw [hfil, Finset.prod_insert hnot, hk, pow_succ, hγ0, one_pow]
  ring

omit [Fintype T] in
/-- **Lemma A.3 (ii), a change of basis before the last hidden state:** for `ε > 0`, blocks that
are positively homogeneous of degree `k` and `G = e^{τ S}` at `h_ℓ`, `ℓ < L`, the derivative of
the output at token `t` at `τ = 0` is the output times
`− k^{L−ℓ} (h_ℓ S h_ℓ^⊤)/(d (r_ℓ² + ε)) ∏_{i > ℓ} ε/(r_i² + ε)`. -/
theorem hasDerivAt_eval_cobAt_exp_of_rowHomogeneous {ε : ℝ} (hε : 0 < ε)
    (hA : A.χ = rmsNorm ε) {k : ℕ} (hf : RowHomogeneous A k) (θ : Params A dIn dOut)
    (ℓ : Fin L) (S : Matrix d d ℝ) (x : Matrix T dIn ℝ) (t : T) :
    HasDerivAt (fun τ : ℝ => eval A 0 (θ.cobAt ℓ.castSucc (expGL (τ • S))) x t)
      ((-((k : ℝ) ^ (L - (ℓ : ℕ)))
          * ((hidden A 0 θ x ℓ.castSucc t ⬝ᵥ (S *ᵥ hidden A 0 θ x ℓ.castSucc t))
            / ((Fintype.card d : ℝ) * (meanSq (hidden A 0 θ x ℓ.castSucc t) + ε)))
          * ∏ i ∈ Finset.univ.filter (fun i : Fin (L + 1) => ℓ.castSucc < i),
              ε / (meanSq (hidden A 0 θ x i t) + ε))
        • eval A 0 θ x t) 0 := by
  -- `q(τ) = r²(h_ℓ e^{τ S})` has the derivative `2 h_ℓ S h_ℓᵀ / d` at `0`, and `q(0) = r_ℓ²`
  have hq := hasDerivAt_meanSq_exp_hom (hidden A 0 θ x ℓ.castSucc t) S
  have hq0 : meanSq (hidden A 0 θ x ℓ.castSucc t ᵥ* (expGL ((0 : ℝ) • S) : Matrix d d ℝ)) =
      meanSq (hidden A 0 θ x ℓ.castSucc t) := by
    rw [coe_expGL, zero_smul, NormedSpace.exp_zero, Matrix.vecMul_one]
  have h := hasDerivAt_eval_cobAt_hom hε hA hf θ ℓ (fun τ => expGL (τ • S)) x t hq hq0
  convert h using 2
  simp only [div_mul_eq_div_div]
  ring

omit [Fintype T] in
/-- Helper: `e^{τ I} = e^τ I`. -/
private theorem exp_smul_one_hom (τ : ℝ) :
    NormedSpace.exp (τ • (1 : Matrix d d ℝ)) = Real.exp τ • (1 : Matrix d d ℝ) := by
  rw [Matrix.smul_one_eq_diagonal, Matrix.exp_diagonal, Matrix.smul_one_eq_diagonal]
  congr 1
  funext i
  rw [Pi.coe_exp, Real.exp_eq_exp_ℝ]

omit [Fintype T] in
/-- **Lemma A.3 (ii), the scaling at the last hidden state:** for `ε > 0` and the scaling
`c = e^τ` at `h_L` with the readout `D` unchanged, the derivative of the output at token `t` at
`τ = 0` is the output times `ε/(r_L² + ε)`. -/
theorem hasDerivAt_eval_scale_last_exp {ε : ℝ} (hε : 0 < ε) (hA : A.χ = rmsNorm ε)
    (θ : Params A dIn dOut) (x : Matrix T dIn ℝ) (t : T) :
    HasDerivAt
      (fun τ : ℝ => eval A 0
        { θ.cobAt (Fin.last L) (expGL (τ • (1 : Matrix d d ℝ))) with D := θ.D } x t)
      ((ε / (meanSq (hidden A 0 θ x (Fin.last L) t) + ε)) • eval A 0 θ x t) 0 := by
  -- `h_L ↦ h_L e^τ = diag(e^τ) h_L`, and the readout reads `diag(β_L(e^τ)) N_ε(h_L)`
  have hout : ∀ τ : ℝ, eval A 0
      { θ.cobAt (Fin.last L) (expGL (τ • (1 : Matrix d d ℝ))) with D := θ.D } x t =
        (betaF_hom ε (meanSq (hidden A 0 θ x (Fin.last L) t)) ∘ Real.exp) τ
          • eval A 0 θ x t := fun τ => by
    rw [eval_scale_last_eq_hom, coe_expGL, exp_smul_one_hom, mul_smul_one_hom, hA,
      rmsNorm_rowScale_hom hε, rowScale_mul_hom, eval, hA]
    rfl
  -- the chain rule: `β_L'(1) e^0 = ε/(r_L² + ε)`
  have hB := (hasDerivAt_betaF_hom hε
    (meanSq_nonneg_hom (hidden A 0 θ x (Fin.last L) t))).comp_of_eq 0 (Real.hasDerivAt_exp 0)
    Real.exp_zero.symm
  have hfun : (fun τ : ℝ => eval A 0
      { θ.cobAt (Fin.last L) (expGL (τ • (1 : Matrix d d ℝ))) with D := θ.D } x t) =
        fun τ => (betaF_hom ε (meanSq (hidden A 0 θ x (Fin.last L) t)) ∘ Real.exp) τ
          • eval A 0 θ x t := funext hout
  rw [hfun]
  convert hasDerivAt_smul_const_hom hB (eval A 0 θ x t) using 2
  rw [Real.exp_zero, mul_one]

end Skips
