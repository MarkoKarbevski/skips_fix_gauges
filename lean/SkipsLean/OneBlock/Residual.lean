import SkipsLean.OneBlock.Tanh
import SkipsLean.OneBlock.GELU
import SkipsLean.OneBlock.SwiGLU
import SkipsLean.OneBlock.GeGLU

/-!
# The one-block theorem with a skip connection

Paper (skips paper): Theorem 4.6 (i) (Theorem B.1 (i) in the appendix), without normalization and
without biases, for the `tanh`, GELU, SwiGLU and GeGLU blocks: with one block of width at least
`d`, at generic parameters the residual network `x ↦ (x E + f(x E W_read) W_write) D` has the
functional dimension `P - d² - s`, and the skip raises the functional dimension by exactly `d²`.

With `M = E D`, `C = E W_read` and `A = W_write D` the residual network computes
`x ↦ x M + f(x C) A`. Lemma C.3 of the dimension paper is stated with a linear term `x M`, so a
flat direction keeps `M`, `C` and `A` to first order, up to the rescalings inside the block. The
directions that keep `C` and `A` are those of two changes of basis `X` at `h_0` and `Y` at `h_1`
(Lemma C.2), and such a direction keeps `M` only if `E (X - Y) D = 0`, that is, `X = Y`
(Lemma B.2 of the skips paper): one change of basis is left.

As for the networks without skips, the theorem is stated for every activation that satisfies the
conclusion of Lemma C.3 (`UnitsRigid`, `GatedUnitsRescale`), under the conditions of
`OneBlockGeneric` and `OneBlockGenericGated`; the four kinds of block follow.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {hid : Fin 1 → Type} [∀ ℓ, Fintype (hid ℓ)]
variable {σ σ' : ℝ → ℝ}

/-! ### Helpers: linear algebra, and Lemma B.2 of the skips paper -/

/-- Helper (as `cancel_left_of_rank` of `Factorization.lean`): a matrix whose rank is its number
of columns cancels on the left, via a left inverse. -/
private theorem cancel_left_of_rank_res {m n k : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (M : Matrix m n ℝ) (hM : M.rank = Fintype.card n) {X Y : Matrix n k ℝ}
    (h : M * X = M * Y) : X = Y := by
  obtain ⟨B, hB⟩ := Matrix.vecMul_surjective_iff_exists_left_inverse.mp
    (Matrix.vecMul_surjective_iff_rank_eq_card.mpr hM)
  have := congrArg (B * ·) h
  simpa only [← Matrix.mul_assoc, hB, Matrix.one_mul] using this

/-- Helper: a matrix whose rank is its number of rows cancels on the right, via a right
inverse. -/
private theorem cancel_right_of_rank_res {m n k : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    (M : Matrix m n ℝ) (hM : M.rank = Fintype.card m) {X Y : Matrix k m ℝ}
    (h : X * M = Y * M) : X = Y := by
  obtain ⟨R, hR⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.mp
    (Matrix.mulVec_surjective_iff_rank_eq_card.mpr hM)
  have := congrArg (· * R) h
  simpa only [Matrix.mul_assoc, hR, Matrix.mul_one] using this

/-- Helper: `M = E D`, the linear part of the residual network `x ↦ x M + f(x C) A`. -/
private def Mm {A : Arch T d 1} (θ : Params A dIn dOut) : Matrix dIn dOut ℝ :=
  θ.E * θ.D

/-- Helper: the derivative `∂M = η_E D + E η_D` of `M` along `η`. -/
private def dMm {A : Arch T d 1} (θ η : Params A dIn dOut) : Matrix dIn dOut ℝ :=
  η.E * θ.D + θ.E * η.D

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: along the line, `M(τ) = M + τ ∂M + τ² η_E η_D`. -/
private theorem Mm_line {A : Arch T d 1} (θ η : Params A dIn dOut) (τ : ℝ) :
    Mm (θ + τ • η) = Mm θ + τ • dMm θ η + (τ * τ) • Mm η := by
  simp only [Mm, dMm, Params.add_E, Params.smul_E, Params.add_D, Params.smul_D, Matrix.mul_add,
    Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, smul_add, smul_smul]
  abel

omit [Fintype T] [Nonempty T] in
/-- Helper (Lemma B.2 of the skips paper): if `E` and `D` have rank `d`, the direction of the two
changes of basis `X_0` at `h_0` and `X_1` at `h_1` keeps `M = E D` to first order only if
`X_0 = X_1`, since `∂M = E X_0 D - E X_1 D`. -/
private theorem eq_const_of_keeps_ED {A : Arch T d 1} (θ : Params A dIn dOut)
    (X : Fin 2 → Matrix d d ℝ) (hE : θ.E.rank = Fintype.card d)
    (hD : θ.D.rank = Fintype.card d) (hM : dMm θ (cobDir θ X) = 0) :
    X = fun _ => X 0 := by
  -- `∂M = E X_0 D - E X_1 D = 0`
  have h1 : θ.E * (X 0 * θ.D) = θ.E * (X 1 * θ.D) := by
    have h : θ.E * X 0 * θ.D + θ.E * -(X 1 * θ.D) = 0 := hM
    rw [Matrix.mul_neg, Matrix.mul_assoc, add_neg_eq_zero] at h
    exact h
  -- cancel `E` on the left and `D` on the right
  have h01 : X 0 = X 1 :=
    cancel_right_of_rank_res θ.D hD (cancel_left_of_rank_res θ.E hE h1)
  exact funext (Fin.forall_fin_two.2 ⟨rfl, h01.symm⟩)

/-! ### Helpers: the function of one residual MLP block and its derivative -/

/-- Helper: the read of the block, with its columns indexed by the hidden units. -/
private def rd (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) :
    Matrix d (hid 0) ℝ :=
  θ.read 0

/-- Helper: the write of the block, with its rows indexed by the hidden units. -/
private def wr (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) :
    Matrix (hid 0) d ℝ :=
  θ.write 0

/-- Helper: `C = E W_read`. -/
private def Cm (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) :
    Matrix dIn (hid 0) ℝ :=
  θ.E * rd θ

/-- Helper: `A = W_write D`. -/
private def Am (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) :
    Matrix (hid 0) dOut ℝ :=
  wr θ * θ.D

/-- Helper: the derivative `∂C = η_E W_read + E η_read` of `C` along `η`. -/
private def dCm (θ η : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) :
    Matrix dIn (hid 0) ℝ :=
  η.E * rd θ + θ.E * rd η

/-- Helper: the derivative `∂A = η_write D + W_write η_D` of `A` along `η`. -/
private def dAm (θ η : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) :
    Matrix (hid 0) dOut ℝ :=
  wr η * θ.D + wr θ * η.D

omit [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the read is linear in the parameters. -/
private theorem rd_line (θ η : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)
    (τ : ℝ) : rd (θ + τ • η) = rd θ + τ • rd η := rfl

omit [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the write is linear in the parameters. -/
private theorem wr_line (θ η : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)
    (τ : ℝ) : wr (θ + τ • η) = wr θ + τ • wr η := rfl

omit [Fintype T] [Nonempty T] [Fintype dOut] in
/-- Helper: the function of one residual MLP block, `F_θ(x) = x M + σ(x C) A` (the stream matrix
is `1`). -/
private theorem eval_mlp_res_eq (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)
    (x : Matrix T dIn ℝ) :
    eval (Arch.mlp σ id hid) 1 θ x = x * Mm θ + (x * Cm θ).map σ * Am θ := by
  have h1 : (Fin.last 1 : Fin 2) = (0 : Fin 1).succ := rfl
  have hχ : (Arch.mlp (T := T) (d := d) σ id hid).χ = id := rfl
  have hf : (Arch.mlp (T := T) (d := d) σ id hid).f 0 = fun M => M.map σ := rfl
  -- `h_1 = h_0 1 + σ(h_0 W_read) W_write` with `h_0 = x E`
  rw [eval, h1, hidden_succ, Fin.castSucc_zero, hidden_zero, hχ, hf]
  simp only [Pi.one_apply, Matrix.mul_one, id_eq, Matrix.add_mul]
  rw [Matrix.mul_assoc x θ.E θ.D, Matrix.mul_assoc x θ.E (θ.read 0)]
  congr 1
  exact Matrix.mul_assoc _ _ _

omit [Fintype T] [Nonempty T] [Fintype dOut] in
/-- Helper: the entries of `F_θ(x)`, `(x M)_{t o} + ∑_i σ((x C)_{t i}) A_{i o}`. -/
private theorem eval_mlp_res_apply
    (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)
    (x : Matrix T dIn ℝ) (t : T) (o : dOut) :
    eval (Arch.mlp σ id hid) 1 θ x t o
      = (x * Mm θ) t o + ∑ i : hid 0, σ ((x * Cm θ) t i) * Am θ i o := by
  rw [eval_mlp_res_eq]
  rfl

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: along the line, `C(τ) = C + τ ∂C + τ² η_E η_read`. -/
private theorem Cm_line (θ η : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)
    (τ : ℝ) :
    Cm (θ + τ • η) = Cm θ + τ • dCm θ η + (τ * τ) • Cm η := by
  simp only [Cm, dCm, rd_line, Params.add_E, Params.smul_E, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_smul, Matrix.smul_mul, smul_add, smul_smul]
  abel

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: along the line, `A(τ) = A + τ ∂A + τ² η_write η_D`. -/
private theorem Am_line (θ η : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)
    (τ : ℝ) :
    Am (θ + τ • η) = Am θ + τ • dAm θ η + (τ * τ) • Am η := by
  simp only [Am, dAm, wr_line, Params.add_D, Params.smul_D, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_smul, Matrix.smul_mul, smul_add, smul_smul]
  abel

omit [Fintype T] [Nonempty T] [Fintype dOut] in
/-- Helper: the entries of `F_{θ + τ η}(x)` as functions of `τ`. -/
private theorem eval_line_apply
    (θ η : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)
    (x : Matrix T dIn ℝ) (t : T) (o : dOut) (τ : ℝ) :
    eval (Arch.mlp σ id hid) 1 (θ + τ • η) x t o
      = ((x * Mm θ) t o + τ * (x * dMm θ η) t o + τ * τ * (x * Mm η) t o) + ∑ i : hid 0,
        σ ((x * Cm θ) t i + τ * (x * dCm θ η) t i + τ * τ * (x * Cm η) t i) *
          (Am θ i o + τ * dAm θ η i o + τ * τ * Am η i o) := by
  rw [eval_mlp_res_apply, Mm_line, Cm_line, Am_line]
  simp only [Matrix.mul_add, Matrix.mul_smul]
  rfl

omit [Nonempty T] in
/-- Helper (Step 3 of the paper, the chain rule): the derivative of `θ ↦ F_θ(x)` along `η` has
the entries `(x ∂M)_{t o} + ∑_i [σ(z_i) (∂A)_{i o} + σ'(z_i) (x ∂C)_{t i} A_{i o}]`,
`z_i = (x C)_{t i}`. -/
private theorem fderiv_eval_apply (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (θ η : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)
    (x : Matrix T dIn ℝ) (t : T) (o : dOut) :
    fderiv ℝ (fun θ' => eval (Arch.mlp σ id hid) 1 θ' x) θ η t o
      = (x * dMm θ η) t o + ∑ i : hid 0,
        (σ ((x * Cm θ) t i) * dAm θ η i o
          + σ' ((x * Cm θ) t i) * (x * dCm θ η) t i * Am θ i o) := by
  have hdiff := differentiable_eval (A := Arch.mlp (T := T) (d := d) σ id hid) (S := 1)
    (dIn := dIn) (dOut := dOut)
    (fun ℓ => differentiable_f_mlp (fun z => (hσ z).differentiableAt) ℓ) differentiable_id x
  -- the chain rule along the line `τ ↦ θ + τ η`
  have h1 := hasDerivAt_eval_line (A := Arch.mlp (T := T) (d := d) σ id hid) 1 θ η x (hdiff θ)
  have h2 := hasDerivAt_pi.1 (hasDerivAt_pi.1 h1 t) o
  -- the same derivative computed entrywise: a polynomial in `τ`, plus products and sums of real
  -- functions of `τ`
  have h3 : HasDerivAt (fun τ : ℝ => eval (Arch.mlp σ id hid) 1 (θ + τ • η) x t o)
      ((x * dMm θ η) t o + ∑ i : hid 0, (σ ((x * Cm θ) t i) * dAm θ η i o
        + σ' ((x * Cm θ) t i) * (x * dCm θ η) t i * Am θ i o)) 0 := by
    rw [funext fun τ => eval_line_apply θ η x t o τ]
    refine (hasDerivAt_quad _ _ _).add (HasDerivAt.fun_sum fun i _ => ?_)
    have hu := hasDerivAt_quad ((x * Cm θ) t i) ((x * dCm θ η) t i) ((x * Cm η) t i)
    have hv := hasDerivAt_quad (Am θ i o) (dAm θ η i o) (Am η i o)
    have h := ((hσ _).comp (0 : ℝ) hu).mul hv
    convert h using 1
    · rfl
    · simp only [Function.comp_apply, zero_mul, mul_zero, add_zero]
      ring
  exact h2.unique h3

/-! ### MLP blocks without symmetries inside the hidden units -/

/-- Under the conditions, every flat direction of one residual MLP block whose activation
satisfies Lemma C.3 without rescalings is the direction of one change of basis, the same at `h_0`
and at `h_1`. -/
theorem flat_le_range_cobDir_const_mlp_residual (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hU : UnitsRigid σ σ' dIn dOut (hid 0))
    (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) (hθ : OneBlockGeneric θ)
    (η : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)
    (hη : η ∈ flat (Arch.mlp σ id hid) 1 θ) :
    ∃ X : Matrix d d ℝ, η = cobDir θ (fun _ => X) := by
  -- Step 3: the derivative of `F(θ, x)` along `η` vanishes at every input, entry by entry
  have hzero : ∀ (x : Matrix T dIn ℝ) (t : T) (o : dOut), (x * dMm θ η) t o + ∑ i : hid 0,
      (σ ((x * Cm θ) t i) * dAm θ η i o
        + σ' ((x * Cm θ) t i) * (x * dCm θ η) t i * Am θ i o) = 0 := by
    intro x t o
    rw [← fderiv_eval_apply hσ θ η x t o]
    have h := LinearMap.mem_ker.1 ((Submodule.mem_iInf _).1 hη x)
    exact congrFun (congrFun h t) o
  -- Step 2, Lemma C.3 with the linear term `x ∂M` (inputs `x` with all rows equal to `v`):
  -- `∂M = 0`, `∂C = 0` and `∂A = 0`
  obtain ⟨hm, -, hc, -, ha⟩ := hU (fun i => (Cm θ)ᵀ i) 0 (fun i => Am θ i)
    (dMm θ η) 0 (fun i => (dCm θ η)ᵀ i) 0 (fun i => dAm θ η i) (fun i => hθ.row_ne_zero i)
    (fun i => hθ.col_ne_zero i) (fun i j hij => hθ.col_not_collinear i j hij) (by
      intro v
      funext o
      have h := hzero (Matrix.of fun _ => v) (Classical.arbitrary T) o
      simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
        add_zero]
      exact h)
  -- Step 1, Lemma C.2: a direction that keeps `C` and `A` is that of two changes of basis
  have hC : η.E * θ.read 0 + θ.E * η.read 0 = 0 := by
    ext a i
    exact congrFun (congrFun hc i) a
  have hA : η.write 0 * θ.D + θ.write 0 * η.D = 0 := by
    ext i o
    exact congrFun (congrFun ha i) o
  obtain ⟨X, rfl⟩ := (keeps_products_iff_mem_range_cobDir θ η hθ.rank_E hθ.rank_D
    hθ.rank_read hθ.rank_write).1 ⟨hC, hA⟩
  -- Lemma B.2 of the skips paper: the direction keeps `M = E D` only if `X_0 = X_1`
  exact ⟨X 0, congrArg (cobDir θ) (eq_const_of_keeps_ED θ X hθ.rank_E hθ.rank_D hm)⟩

/-- **Theorem 4.6 (i) of the skips paper for a residual MLP block with `s = 0`, under the
conditions of its proof:** the functional dimension is `P - d²`. -/
theorem funDim_mlp_oneBlock_residual (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hU : UnitsRigid σ σ' dIn dOut (hid 0))
    (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) (hθ : OneBlockGeneric θ) :
    funDim (Arch.mlp σ id hid) 1 θ + Fintype.card d ^ 2
      = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) := by
  have hσd : Differentiable ℝ σ := fun z => (hσ z).differentiableAt
  have hdiff : ∀ x : Matrix T dIn ℝ, DifferentiableAt ℝ
      (fun θ' : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut =>
        eval (Arch.mlp σ id hid) 1 θ' x) θ := fun x =>
    (differentiable_eval (A := Arch.mlp (T := T) (d := d) σ id hid) (S := 1)
      (fun ℓ => differentiable_f_mlp hσd ℓ) differentiable_id x).differentiableAt
  -- the directions of one change of basis, `X ↦ cobDir θ (X, X)`
  let Φ : Matrix d d ℝ →ₗ[ℝ] Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut :=
    (cobDirLin θ).comp (LinearMap.pi fun _ => LinearMap.id)
  -- the flat directions are exactly these directions: `⊆` is the previous theorem, `⊇` holds
  -- since one change of basis at all hidden states is a symmetry of the residual network
  have hflat : flat (Arch.mlp σ id hid) 1 θ = LinearMap.range Φ := by
    apply le_antisymm
    · intro η hη
      obtain ⟨X, rfl⟩ := flat_le_range_cobDir_const_mlp_residual hσ hU θ hθ η hη
      exact LinearMap.mem_range.2 ⟨X, rfl⟩
    · rintro _ ⟨X, rfl⟩
      exact cobDir_const_mem_flat_residual θ rfl (fun ℓ => differentiable_f_mlp hσd ℓ) X
  -- `X ↦ cobDir θ (X, X)` is injective: the embedding component `E X` determines `X`
  have hinj : Function.Injective Φ := by
    intro X Y hXY
    have hEq : θ.E * X = θ.E * Y := congrArg Params.E hXY
    exact cancel_left_of_rank_res θ.E hθ.rank_E hEq
  -- `fd(θ) = P - dim K(θ)` (Appendix C), and `dim K(θ) = d²`
  have h := funDim_add_finrank_flat θ hdiff
  rwa [hflat, LinearMap.finrank_range_of_inj hinj, Module.finrank_matrix, Module.finrank_self,
    mul_one, ← sq] at h

/-- **Theorem 4.6 (i) of the skips paper for an MLP block with `s = 0`:** with
`d_in, d_out, d_hidden ≥ d ≥ 2`, at generic parameters the residual network has the functional
dimension `P - d²`. -/
theorem ae_funDim_mlp_oneBlock_residual (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hU : UnitsRigid σ σ' dIn dOut (hid 0))
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ θ ∂μ, funDim (Arch.mlp σ id hid) 1 θ + Fintype.card d ^ 2
      = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) :=
  (ae_oneBlockGeneric μ hd hdIn hdOut hhid).mono fun θ hθ =>
    funDim_mlp_oneBlock_residual hσ hU θ hθ

/-- **The skip raises the functional dimension by exactly `d²`** (Theorem 4.6 (i) of the skips
paper), for one MLP block with `s = 0`, at generic parameters. -/
theorem ae_funDim_mlp_oneBlock_residual_eq_add (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hU : UnitsRigid σ σ' dIn dOut (hid 0))
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ θ ∂μ, funDim (Arch.mlp σ id hid) 1 θ
      = funDim (Arch.mlp σ id hid) 0 θ + Fintype.card d ^ 2 := by
  -- `fd_1 + d² = P` with the skip, `fd_0 + 2 d² = P` without (Theorem 5.1)
  filter_upwards [ae_funDim_mlp_oneBlock_residual hσ hU μ hd hdIn hdOut hhid,
    ae_funDim_mlp_oneBlock hσ hU μ hd hdIn hdOut hhid] with θ h1 h2
  omega

/-! ### Helpers: the function of one residual gated block and its derivative -/

/-- Helper: the read of the gated block, with its columns indexed by the gates and values. -/
private def rdG (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) :
    Matrix d (hid 0 ⊕ hid 0) ℝ :=
  θ.read 0

/-- Helper: the write of the gated block, with its rows indexed by the hidden units. -/
private def wrG (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) :
    Matrix (hid 0) d ℝ :=
  θ.write 0

/-- Helper: `C = E W_read` for the gated block. -/
private def CmG (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) :
    Matrix dIn (hid 0 ⊕ hid 0) ℝ :=
  θ.E * rdG θ

/-- Helper: `A = W_write D` for the gated block. -/
private def AmG (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) :
    Matrix (hid 0) dOut ℝ :=
  wrG θ * θ.D

/-- Helper: the derivative `∂C = η_E W_read + E η_read` of `C` along `η`. -/
private def dCmG (θ η : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) :
    Matrix dIn (hid 0 ⊕ hid 0) ℝ :=
  η.E * rdG θ + θ.E * rdG η

/-- Helper: the derivative `∂A = η_write D + W_write η_D` of `A` along `η`. -/
private def dAmG (θ η : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) :
    Matrix (hid 0) dOut ℝ :=
  wrG η * θ.D + wrG θ * η.D

omit [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the read is linear in the parameters. -/
private theorem rdG_line (θ η : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (τ : ℝ) : rdG (θ + τ • η) = rdG θ + τ • rdG η := rfl

omit [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the write is linear in the parameters. -/
private theorem wrG_line (θ η : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (τ : ℝ) : wrG (θ + τ • η) = wrG θ + τ • wrG η := rfl

omit [Fintype T] [Nonempty T] [Fintype dOut] in
/-- Helper: the function of one residual gated block, `F_θ(x) = x M + (σ(x C_g) ⊙ (x C_v)) A`
(the stream matrix is `1`). -/
private theorem eval_gated_res_eq
    (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) (x : Matrix T dIn ℝ) :
    eval (Arch.gated σ id hid) 1 θ x
      = x * Mm θ + (Matrix.of fun t i => σ ((x * CmG θ) t (Sum.inl i))
          * (x * CmG θ) t (Sum.inr i)) * AmG θ := by
  have h1 : (Fin.last 1 : Fin 2) = (0 : Fin 1).succ := rfl
  have hχ : (Arch.gated (T := T) (d := d) σ id hid).χ = id := rfl
  have hf : (Arch.gated (T := T) (d := d) σ id hid).f 0
      = fun M => Matrix.of fun t i => σ (M t (Sum.inl i)) * M t (Sum.inr i) := rfl
  -- `h_1 = h_0 1 + f(h_0 W_read) W_write` with `h_0 = x E`
  rw [eval, h1, hidden_succ, Fin.castSucc_zero, hidden_zero, hχ, hf]
  simp only [Pi.one_apply, Matrix.mul_one, id_eq, Matrix.add_mul]
  rw [Matrix.mul_assoc x θ.E θ.D, Matrix.mul_assoc x θ.E (θ.read 0)]
  congr 1
  exact Matrix.mul_assoc _ _ _

omit [Fintype T] [Nonempty T] [Fintype dOut] in
/-- Helper: the entries of `F_θ(x)`,
`(x M)_{t o} + ∑_i σ((x C)_{t, g i}) (x C)_{t, v i} A_{i o}`. -/
private theorem eval_gated_res_apply
    (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (x : Matrix T dIn ℝ) (t : T) (o : dOut) :
    eval (Arch.gated σ id hid) 1 θ x t o
      = (x * Mm θ) t o + ∑ i : hid 0,
        σ ((x * CmG θ) t (Sum.inl i)) * (x * CmG θ) t (Sum.inr i) * AmG θ i o := by
  rw [eval_gated_res_eq]
  rfl

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: along the line, `C(τ) = C + τ ∂C + τ² η_E η_read`. -/
private theorem CmG_line (θ η : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (τ : ℝ) :
    CmG (θ + τ • η) = CmG θ + τ • dCmG θ η + (τ * τ) • CmG η := by
  simp only [CmG, dCmG, rdG_line, Params.add_E, Params.smul_E, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_smul, Matrix.smul_mul, smul_add, smul_smul]
  abel

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: along the line, `A(τ) = A + τ ∂A + τ² η_write η_D`. -/
private theorem AmG_line (θ η : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (τ : ℝ) :
    AmG (θ + τ • η) = AmG θ + τ • dAmG θ η + (τ * τ) • AmG η := by
  simp only [AmG, dAmG, wrG_line, Params.add_D, Params.smul_D, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_smul, Matrix.smul_mul, smul_add, smul_smul]
  abel

omit [Fintype T] [Nonempty T] [Fintype dOut] in
/-- Helper: the entries of `F_{θ + τ η}(x)` as functions of `τ`, for the gated block. -/
private theorem evalG_line_apply
    (θ η : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (x : Matrix T dIn ℝ) (t : T) (o : dOut) (τ : ℝ) :
    eval (Arch.gated σ id hid) 1 (θ + τ • η) x t o
      = ((x * Mm θ) t o + τ * (x * dMm θ η) t o + τ * τ * (x * Mm η) t o) + ∑ i : hid 0,
        σ ((x * CmG θ) t (Sum.inl i) + τ * (x * dCmG θ η) t (Sum.inl i)
            + τ * τ * (x * CmG η) t (Sum.inl i)) *
          ((x * CmG θ) t (Sum.inr i) + τ * (x * dCmG θ η) t (Sum.inr i)
            + τ * τ * (x * CmG η) t (Sum.inr i)) *
          (AmG θ i o + τ * dAmG θ η i o + τ * τ * AmG η i o) := by
  rw [eval_gated_res_apply, Mm_line, CmG_line, AmG_line]
  simp only [Matrix.mul_add, Matrix.mul_smul]
  rfl

omit [Nonempty T] in
/-- Helper (Step 3 of the paper, the chain rule): the derivative of `θ ↦ F_θ(x)` along `η` has
the entries `(x ∂M)_{t o} + ∑_i [σ(z_i) w_i (∂A)_{i o} + σ'(z_i) (x ∂C)_{t, g i} w_i A_{i o}
+ σ(z_i) (x ∂C)_{t, v i} A_{i o}]`, with `z_i = (x C)_{t, g i}` and `w_i = (x C)_{t, v i}`. -/
private theorem fderivG_eval_apply (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (θ η : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (x : Matrix T dIn ℝ) (t : T) (o : dOut) :
    fderiv ℝ (fun θ' => eval (Arch.gated σ id hid) 1 θ' x) θ η t o
      = (x * dMm θ η) t o + ∑ i : hid 0,
        (σ ((x * CmG θ) t (Sum.inl i)) * (x * CmG θ) t (Sum.inr i) * dAmG θ η i o
          + σ' ((x * CmG θ) t (Sum.inl i)) * (x * dCmG θ η) t (Sum.inl i)
              * (x * CmG θ) t (Sum.inr i) * AmG θ i o
          + σ ((x * CmG θ) t (Sum.inl i)) * (x * dCmG θ η) t (Sum.inr i) * AmG θ i o) := by
  have hdiff := differentiable_eval (A := Arch.gated (T := T) (d := d) σ id hid) (S := 1)
    (dIn := dIn) (dOut := dOut)
    (differentiable_f_gated fun z => (hσ z).differentiableAt) differentiable_id x
  -- the chain rule along the line `τ ↦ θ + τ η`
  have h1 := hasDerivAt_eval_line (A := Arch.gated (T := T) (d := d) σ id hid) 1 θ η x (hdiff θ)
  have h2 := hasDerivAt_pi.1 (hasDerivAt_pi.1 h1 t) o
  -- the same derivative computed entrywise: a polynomial in `τ`, plus products and sums of real
  -- functions of `τ`
  have h3 : HasDerivAt (fun τ : ℝ => eval (Arch.gated σ id hid) 1 (θ + τ • η) x t o)
      ((x * dMm θ η) t o + ∑ i : hid 0,
        (σ ((x * CmG θ) t (Sum.inl i)) * (x * CmG θ) t (Sum.inr i) * dAmG θ η i o
          + σ' ((x * CmG θ) t (Sum.inl i)) * (x * dCmG θ η) t (Sum.inl i)
              * (x * CmG θ) t (Sum.inr i) * AmG θ i o
          + σ ((x * CmG θ) t (Sum.inl i)) * (x * dCmG θ η) t (Sum.inr i) * AmG θ i o)) 0 := by
    rw [funext fun τ => evalG_line_apply θ η x t o τ]
    refine (hasDerivAt_quad _ _ _).add (HasDerivAt.fun_sum fun i _ => ?_)
    have hu := hasDerivAt_quad ((x * CmG θ) t (Sum.inl i)) ((x * dCmG θ η) t (Sum.inl i))
      ((x * CmG η) t (Sum.inl i))
    have hw := hasDerivAt_quad ((x * CmG θ) t (Sum.inr i)) ((x * dCmG θ η) t (Sum.inr i))
      ((x * CmG η) t (Sum.inr i))
    have hv := hasDerivAt_quad (AmG θ i o) (dAmG θ η i o) (AmG η i o)
    have h := (((hσ _).comp (0 : ℝ) hu).mul hw).mul hv
    convert h using 1
    · rfl
    · simp only [Pi.mul_apply, Function.comp_apply, zero_mul, mul_zero, add_zero]
      ring
  exact h2.unique h3

/-! ### Helpers: the derivative of `C` and `A` along a rescaling -/

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: `∂C` is linear in the direction. -/
private theorem dCmG_sub (θ η ρ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) :
    dCmG θ (η - ρ) = dCmG θ η - dCmG θ ρ := by
  show (η.E - ρ.E) * rdG θ + θ.E * (rdG η - rdG ρ)
    = (η.E * rdG θ + θ.E * rdG η) - (ρ.E * rdG θ + θ.E * rdG ρ)
  rw [Matrix.sub_mul, Matrix.mul_sub]
  abel

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: `∂A` is linear in the direction. -/
private theorem dAmG_sub (θ η ρ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) :
    dAmG θ (η - ρ) = dAmG θ η - dAmG θ ρ := by
  show (wrG η - wrG ρ) * θ.D + wrG θ * (η.D - ρ.D)
    = (wrG η * θ.D + wrG θ * η.D) - (wrG ρ * θ.D + wrG θ * ρ.D)
  rw [Matrix.sub_mul, Matrix.mul_sub]
  abel

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: along a rescaling, the gate columns of `C` do not move. -/
private theorem dCmG_rescale_inl
    (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) (α : ∀ ℓ, hid ℓ → ℝ)
    (a : dIn) (i : hid 0) :
    dCmG θ (rescaleDir θ α) a (Sum.inl i) = 0 := by
  show ((0 : Matrix dIn d ℝ) * rdG θ + θ.E * rdG (rescaleDir θ α)) a (Sum.inl i) = 0
  rw [Matrix.zero_mul, zero_add, Matrix.mul_apply]
  exact Finset.sum_eq_zero fun k _ => mul_eq_zero_of_right _ rfl

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: along a rescaling, the value column `e_i` of `C` moves by `-α_i e_i`. -/
private theorem dCmG_rescale_inr
    (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) (α : ∀ ℓ, hid ℓ → ℝ)
    (a : dIn) (i : hid 0) :
    dCmG θ (rescaleDir θ α) a (Sum.inr i) = -(α 0 i) * CmG θ a (Sum.inr i) := by
  show ((0 : Matrix dIn d ℝ) * rdG θ + θ.E * rdG (rescaleDir θ α)) a (Sum.inr i)
    = -(α 0 i) * (θ.E * rdG θ) a (Sum.inr i)
  rw [Matrix.zero_mul, zero_add, Matrix.mul_apply, Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  show θ.E a k * (-(α 0 i) * θ.read 0 k (Sum.inr i))
    = -(α 0 i) * (θ.E a k * θ.read 0 k (Sum.inr i))
  ring

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: along a rescaling, the row `a_i` of `A` moves by `α_i a_i`. -/
private theorem dAmG_rescale
    (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) (α : ∀ ℓ, hid ℓ → ℝ)
    (i : hid 0) (o : dOut) :
    dAmG θ (rescaleDir θ α) i o = α 0 i * AmG θ i o := by
  show (wrG (rescaleDir θ α) * θ.D + wrG θ * (0 : Matrix d dOut ℝ)) i o
    = α 0 i * (wrG θ * θ.D) i o
  rw [Matrix.mul_zero, add_zero, Matrix.mul_apply, Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  show α 0 i * θ.write 0 i k * θ.D k o = α 0 i * (θ.write 0 i k * θ.D k o)
  ring

/-! ### Gated blocks -/

/-- Under the conditions, every flat direction of one residual gated block whose gate activation
satisfies Lemma C.3 is the sum of the direction of one change of basis and of the direction of a
rescaling of the values of the hidden units. -/
theorem flat_le_cobDir_const_add_rescaleDir_gated_residual (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hU : GatedUnitsRescale σ σ' dIn dOut (hid 0))
    (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) (hθ : OneBlockGenericGated θ)
    (η : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (hη : η ∈ flat (Arch.gated σ id hid) 1 θ) :
    ∃ (X : Matrix d d ℝ) (α : ∀ ℓ, hid ℓ → ℝ), η = cobDir θ (fun _ => X) + rescaleDir θ α := by
  -- Step 3: the derivative of `F(θ, x)` along `η` vanishes at every input, entry by entry
  have hzero : ∀ (x : Matrix T dIn ℝ) (t : T) (o : dOut), (x * dMm θ η) t o + ∑ i : hid 0,
      (σ ((x * CmG θ) t (Sum.inl i)) * (x * CmG θ) t (Sum.inr i) * dAmG θ η i o
        + σ' ((x * CmG θ) t (Sum.inl i)) * (x * dCmG θ η) t (Sum.inl i)
            * (x * CmG θ) t (Sum.inr i) * AmG θ i o
        + σ ((x * CmG θ) t (Sum.inl i)) * (x * dCmG θ η) t (Sum.inr i) * AmG θ i o) = 0 := by
    intro x t o
    rw [← fderivG_eval_apply hσ θ η x t o]
    have h := LinearMap.mem_ker.1 ((Submodule.mem_iInf _).1 hη x)
    exact congrFun (congrFun h t) o
  -- Step 2, Lemma C.3 with the linear term `x ∂M` (inputs `x` with all rows equal to `v`):
  -- `∂M = 0`, the gate columns of `∂C` vanish, and every unit only rescales its value,
  -- `∂e_i = -α_i e_i`, `∂a_i = α_i a_i`
  obtain ⟨hm, -, hc, -, α, hα⟩ := hU
    (fun i => (CmG θ)ᵀ (Sum.inl i)) 0 (fun i => (CmG θ)ᵀ (Sum.inr i)) 0 (fun i => AmG θ i)
    (dMm θ η) 0 (fun i => (dCmG θ η)ᵀ (Sum.inl i)) 0 (fun i => (dCmG θ η)ᵀ (Sum.inr i)) 0
    (fun i => dAmG θ η i) (fun i => hθ.row_ne_zero i) (fun i => hθ.gate_ne_zero i)
    (fun i j hij => hθ.gate_not_collinear i j hij) (fun i => hθ.value_ne_zero i) (by
      intro v
      funext o
      have h := hzero (Matrix.of fun _ => v) (Classical.arbitrary T) o
      simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
        add_zero]
      exact h)
  -- the rescaling with these `α_i` (one block: `ℓ = 0`)
  let α' : ∀ ℓ : Fin 1, hid ℓ → ℝ := fun ℓ => Fin.cases α (fun l => l.elim0) ℓ
  -- `η - rescaleDir θ α` keeps `C` and `A` to first order
  have hC : dCmG θ (η - rescaleDir θ α') = 0 := by
    ext a j
    rcases j with i | i
    · rw [dCmG_sub, Matrix.sub_apply, dCmG_rescale_inl, sub_zero]
      exact congrFun (congrFun hc i) a
    · rw [dCmG_sub, Matrix.sub_apply, dCmG_rescale_inr, Matrix.zero_apply, sub_eq_zero]
      exact congrFun (hα i).1 a
  have hA : dAmG θ (η - rescaleDir θ α') = 0 := by
    ext i o
    rw [dAmG_sub, Matrix.sub_apply, dAmG_rescale, Matrix.zero_apply, sub_eq_zero]
    exact congrFun (hα i).2.2 o
  -- Step 1, Lemma C.2: a direction that keeps `C` and `A` is that of two changes of basis
  obtain ⟨X, hX⟩ := (keeps_products_iff_mem_range_cobDir θ (η - rescaleDir θ α') hθ.rank_E
    hθ.rank_D hθ.rank_read hθ.rank_write).1 ⟨hC, hA⟩
  -- the rescaling leaves `E` and `D` alone, so `cobDir θ X` keeps `M = E D` as `η` does
  have hM : dMm θ (cobDir θ X) = 0 := by
    rw [← hX]
    show (η.E - 0) * θ.D + θ.E * (η.D - 0) = 0
    rw [sub_zero, sub_zero]
    exact hm
  -- Lemma B.2 of the skips paper: then `X_0 = X_1`
  have hXc := eq_const_of_keeps_ED θ X hθ.rank_E hθ.rank_D hM
  exact ⟨X 0, α', (sub_eq_iff_eq_add.1 hX).trans
    (congrArg (fun Y => cobDir θ Y + rescaleDir θ α') hXc)⟩

/-- Helper (the private `rescaleDirLin` of `Dimension/Rescaling.lean`): `α ↦ rescaleDir θ α` is
linear. -/
private noncomputable def rescaleDirLinG
    (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) :
    (∀ ℓ : Fin 1, hid ℓ → ℝ) →ₗ[ℝ] Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut where
  toFun := rescaleDir θ
  map_add' α β := by
    apply Params.ext'
    · exact (add_zero 0).symm
    · intro ℓ
      ext k j
      rcases j with i | i
      · exact (add_zero 0).symm
      · show -((α + β) ℓ i) * θ.read ℓ k (Sum.inr i)
          = -(α ℓ i) * θ.read ℓ k (Sum.inr i) + -(β ℓ i) * θ.read ℓ k (Sum.inr i)
        rw [Pi.add_apply, Pi.add_apply]
        ring
    · intro ℓ
      ext i k
      show (α + β) ℓ i * θ.write ℓ i k = α ℓ i * θ.write ℓ i k + β ℓ i * θ.write ℓ i k
      rw [Pi.add_apply, Pi.add_apply]
      ring
    · exact (add_zero 0).symm
  map_smul' c α := by
    apply Params.ext'
    · exact (smul_zero c).symm
    · intro ℓ
      ext k j
      rcases j with i | i
      · exact (smul_zero c).symm
      · show -((c • α) ℓ i) * θ.read ℓ k (Sum.inr i) = c * (-(α ℓ i) * θ.read ℓ k (Sum.inr i))
        rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul]
        ring
    · intro ℓ
      ext i k
      show (c • α) ℓ i * θ.write ℓ i k = c * (α ℓ i * θ.write ℓ i k)
      rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul]
      ring
    · exact (smul_zero c).symm

/-- **Theorem 4.6 (i) of the skips paper for a residual SwiGLU or GeGLU block, under the
conditions of its proof:** the functional dimension is `P - d² - d_hidden`. -/
theorem funDim_gated_oneBlock_residual (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hU : GatedUnitsRescale σ σ' dIn dOut (hid 0))
    (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) (hθ : OneBlockGenericGated θ) :
    funDim (Arch.gated σ id hid) 1 θ + (Fintype.card d ^ 2 + Fintype.card (hid 0))
      = Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) := by
  have hσd : Differentiable ℝ σ := fun z => (hσ z).differentiableAt
  have hdiff : ∀ x : Matrix T dIn ℝ, DifferentiableAt ℝ
      (fun θ' : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut =>
        eval (Arch.gated σ id hid) 1 θ' x) θ := fun x =>
    (differentiable_eval (A := Arch.gated (T := T) (d := d) σ id hid) (S := 1)
      (differentiable_f_gated hσd) differentiable_id x).differentiableAt
  -- the directions of one change of basis and of the rescalings,
  -- `(X, α) ↦ cobDir θ (X, X) + rescaleDir θ α`
  let Φ : (Matrix d d ℝ × (∀ ℓ : Fin 1, hid ℓ → ℝ)) →ₗ[ℝ]
      Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut :=
    ((cobDirLin θ).comp (LinearMap.pi fun _ => LinearMap.id)).coprod (rescaleDirLinG θ)
  -- the flat directions are exactly these directions: `⊆` is the previous theorem, `⊇` holds
  -- since one change of basis at all hidden states and the rescalings are symmetries
  have hflat : flat (Arch.gated σ id hid) 1 θ = LinearMap.range Φ := by
    apply le_antisymm
    · intro η hη
      obtain ⟨X, α, rfl⟩ := flat_le_cobDir_const_add_rescaleDir_gated_residual hσ hU θ hθ η hη
      exact LinearMap.mem_range.2 ⟨(X, α), rfl⟩
    · rintro _ ⟨p, rfl⟩
      rw [LinearMap.coprod_apply]
      exact add_mem (cobDir_const_mem_flat_residual θ rfl (differentiable_f_gated hσd) p.1)
        (rescaleDir_mem_flat_stream θ 1 hσd differentiable_id p.2)
  -- no value column of `W_read` vanishes, since the value columns of `C = E W_read` do not
  have hv : ∀ ℓ i, (fun k => θ.read ℓ k (Sum.inr i)) ≠ 0 := by
    intro ℓ i h0
    obtain rfl := Subsingleton.elim ℓ 0
    apply hθ.value_ne_zero i
    funext a
    show ∑ k, θ.E a k * θ.read 0 k (Sum.inr i) = 0
    exact Finset.sum_eq_zero fun k _ => by
      rw [show θ.read 0 k (Sum.inr i) = 0 from congrFun h0 k, mul_zero]
  -- `(X, α) ↦ cobDir θ (X, X) + rescaleDir θ α` is injective (Lemma B.1 for gated blocks, on the
  -- constant families)
  have hinj0 := cobDir_add_rescaleDir_injective θ hθ.rank_E
    (fun ℓ => by obtain rfl := Subsingleton.elim ℓ 0; exact hθ.rank_write) hv
  have hinj : Function.Injective Φ := by
    intro p q hpq
    rw [LinearMap.coprod_apply, LinearMap.coprod_apply] at hpq
    have h' : cobDir θ (fun _ : Fin (1 + 1) => p.1) + rescaleDir θ p.2
        = cobDir θ (fun _ : Fin (1 + 1) => q.1) + rescaleDir θ q.2 := hpq
    have h2 : ((fun _ : Fin (1 + 1) => p.1), p.2) = ((fun _ : Fin (1 + 1) => q.1), q.2) :=
      hinj0 h'
    have h3 := Prod.mk.inj h2
    exact Prod.ext (congrFun h3.1 0) h3.2
  -- the domain has dimension `d² + d_hidden`
  have hdim : Module.finrank ℝ (Matrix d d ℝ × (∀ ℓ : Fin 1, hid ℓ → ℝ))
      = Fintype.card d ^ 2 + Fintype.card (hid 0) := by
    rw [Module.finrank_prod, Module.finrank_matrix, Module.finrank_self, mul_one, ← sq,
      Module.finrank_pi_fintype]
    simp only [Module.finrank_fintype_fun_eq_card, Finset.univ_unique, Fin.default_eq_zero,
      Finset.sum_singleton]
  -- `fd(θ) = P - dim K(θ)` (Appendix C)
  have h := funDim_add_finrank_flat θ hdiff
  rwa [hflat, LinearMap.finrank_range_of_inj hinj, hdim] at h

/-- **Theorem 4.6 (i) of the skips paper for a SwiGLU or GeGLU block:** with
`d_in, d_out, d_hidden ≥ d ≥ 2`, at generic parameters the residual network has the functional
dimension `P - d² - d_hidden`. -/
theorem ae_funDim_gated_oneBlock_residual (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hU : GatedUnitsRescale σ σ' dIn dOut (hid 0))
    (μ : Measure (Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ θ ∂μ, funDim (Arch.gated σ id hid) 1 θ + (Fintype.card d ^ 2 + Fintype.card (hid 0))
      = Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) :=
  (ae_oneBlockGenericGated μ hd hdIn hdOut hhid).mono fun θ hθ =>
    funDim_gated_oneBlock_residual hσ hU θ hθ

/-- **The skip raises the functional dimension by exactly `d²`** (Theorem 4.6 (i) of the skips
paper), for one SwiGLU or GeGLU block, at generic parameters. -/
theorem ae_funDim_gated_oneBlock_residual_eq_add (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hU : GatedUnitsRescale σ σ' dIn dOut (hid 0))
    (μ : Measure (Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ θ ∂μ, funDim (Arch.gated σ id hid) 1 θ
      = funDim (Arch.gated σ id hid) 0 θ + Fintype.card d ^ 2 := by
  -- `fd_1 + d² + s = P` with the skip, `fd_0 + 2 d² + s = P` without (Theorem 5.1)
  filter_upwards [ae_funDim_gated_oneBlock_residual hσ hU μ hd hdIn hdOut hhid,
    ae_funDim_gated_oneBlock hσ hU μ hd hdIn hdOut hhid] with θ h1 h2
  omega

/-! ### The four kinds of block -/

/-- **Theorem 4.6 (i) of the skips paper for a `tanh` block:** the skip raises the functional
dimension by exactly `d²`, at generic parameters. -/
theorem ae_funDim_tanh_oneBlock_residual_eq_add
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) Real.tanh id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ θ ∂μ, funDim (Arch.mlp Real.tanh id hid) 1 θ
      = funDim (Arch.mlp Real.tanh id hid) 0 θ + Fintype.card d ^ 2 :=
  ae_funDim_mlp_oneBlock_residual_eq_add hasDerivAt_tanh (tanh_unitsRigid _ _ _) μ hd hdIn hdOut
    hhid

/-- **Theorem 4.6 (i) of the skips paper for a GELU block.** -/
theorem ae_funDim_gelu_oneBlock_residual_eq_add
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) gelu id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ θ ∂μ, funDim (Arch.mlp gelu id hid) 1 θ
      = funDim (Arch.mlp gelu id hid) 0 θ + Fintype.card d ^ 2 :=
  ae_funDim_mlp_oneBlock_residual_eq_add hasDerivAt_gelu (gelu_unitsRigid _ _ _) μ hd hdIn hdOut
    hhid

/-- **Theorem 4.6 (i) of the skips paper for a SwiGLU block.** -/
theorem ae_funDim_swiglu_oneBlock_residual_eq_add
    (μ : Measure (Params (Arch.gated (T := T) (d := d) silu id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ θ ∂μ, funDim (Arch.gated silu id hid) 1 θ
      = funDim (Arch.gated silu id hid) 0 θ + Fintype.card d ^ 2 :=
  ae_funDim_gated_oneBlock_residual_eq_add hasDerivAt_silu (silu_gatedUnitsRescale _ _ _) μ hd
    hdIn hdOut hhid

/-- **Theorem 4.6 (i) of the skips paper for a GeGLU block.** -/
theorem ae_funDim_geglu_oneBlock_residual_eq_add
    (μ : Measure (Params (Arch.gated (T := T) (d := d) gelu id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ θ ∂μ, funDim (Arch.gated gelu id hid) 1 θ
      = funDim (Arch.gated gelu id hid) 0 θ + Fintype.card d ^ 2 :=
  ae_funDim_gated_oneBlock_residual_eq_add hasDerivAt_gelu (gelu_gatedUnitsRescale _ _ _) μ hd
    hdIn hdOut hhid

end Skips
