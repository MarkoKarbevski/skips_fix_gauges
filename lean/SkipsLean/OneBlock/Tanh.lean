import SkipsLean.Network.Blocks
import SkipsLean.OneBlock.Factorization
import SkipsLean.OneBlock.UnitsTanh
import SkipsLean.Generic.Params

/-!
# The one-block theorem for a tanh block

Paper (dimension paper): Theorem 5.1 (Theorem C.1 in the appendix), for a `tanh` block: with one
block, without normalization and without biases, at generic parameters the functional dimension is
`P - 2 d²`.

The network is `x ↦ tanh(x E W_read) W_write D`. With `C = E W_read` and `A = W_write D`, let `c_i`
be the columns of `C` and `a_i` the rows of `A`. The conditions that the proof uses are: `E`, `D`,
`W_read` and `W_write` have rank `d`, every `a_i` is nonzero, and the `c_i` are nonzero and pairwise
non-collinear. Under them the flat directions are exactly the directions of the two changes of
basis (Lemma C.2 and Lemma C.3), and they hold at generic parameters when
`d_in, d_out, d_hidden ≥ d ≥ 2`.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {hid : Fin 1 → Type} [∀ ℓ, Fintype (hid ℓ)]

/-- The conditions on the parameters of one MLP block that the proof of the one-block theorem
uses. -/
structure OneBlockGeneric (θ : Params (Arch.mlp (T := T) (d := d) Real.tanh id hid) dIn dOut) :
    Prop where
  rank_E : θ.E.rank = Fintype.card d
  rank_D : θ.D.rank = Fintype.card d
  rank_read : (θ.read 0).rank = Fintype.card d
  rank_write : (θ.write 0).rank = Fintype.card d
  /-- every row `a_i` of `A = W_write D` is nonzero -/
  row_ne_zero : ∀ i, (θ.write 0 * θ.D) i ≠ 0
  /-- every column `c_i` of `C = E W_read` is nonzero -/
  col_ne_zero : ∀ i, (θ.E * θ.read 0)ᵀ i ≠ 0
  /-- the columns of `C` are pairwise non-collinear -/
  col_not_collinear : ∀ i j, i ≠ j → ∀ r : ℝ, (θ.E * θ.read 0)ᵀ i ≠ r • (θ.E * θ.read 0)ᵀ j

/-! ### Helpers: the function of one `tanh` block and its derivative -/

/-- Helper: the read of the block, with its columns indexed by the hidden units. -/
private def rd (θ : Params (Arch.mlp (T := T) (d := d) Real.tanh id hid) dIn dOut) :
    Matrix d (hid 0) ℝ :=
  θ.read 0

/-- Helper: the write of the block, with its rows indexed by the hidden units. -/
private def wr (θ : Params (Arch.mlp (T := T) (d := d) Real.tanh id hid) dIn dOut) :
    Matrix (hid 0) d ℝ :=
  θ.write 0

/-- Helper: `C = E W_read`. -/
private def Cm (θ : Params (Arch.mlp (T := T) (d := d) Real.tanh id hid) dIn dOut) :
    Matrix dIn (hid 0) ℝ :=
  θ.E * rd θ

/-- Helper: `A = W_write D`. -/
private def Am (θ : Params (Arch.mlp (T := T) (d := d) Real.tanh id hid) dIn dOut) :
    Matrix (hid 0) dOut ℝ :=
  wr θ * θ.D

/-- Helper: the derivative `∂C = η_E W_read + E η_read` of `C` along `η`. -/
private def dCm (θ η : Params (Arch.mlp (T := T) (d := d) Real.tanh id hid) dIn dOut) :
    Matrix dIn (hid 0) ℝ :=
  η.E * rd θ + θ.E * rd η

/-- Helper: the derivative `∂A = η_write D + W_write η_D` of `A` along `η`. -/
private def dAm (θ η : Params (Arch.mlp (T := T) (d := d) Real.tanh id hid) dIn dOut) :
    Matrix (hid 0) dOut ℝ :=
  wr η * θ.D + wr θ * η.D

omit [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the read is linear in the parameters. -/
private theorem rd_line (θ η : Params (Arch.mlp (T := T) (d := d) Real.tanh id hid) dIn dOut)
    (τ : ℝ) : rd (θ + τ • η) = rd θ + τ • rd η := rfl

omit [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the write is linear in the parameters. -/
private theorem wr_line (θ η : Params (Arch.mlp (T := T) (d := d) Real.tanh id hid) dIn dOut)
    (τ : ℝ) : wr (θ + τ • η) = wr θ + τ • wr η := rfl

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dOut] in
/-- Helper: the function of one `tanh` block, `F_θ(x) = tanh(x C) A` (the stream matrix is `0`). -/
private theorem eval_tanh_eq (θ : Params (Arch.mlp (T := T) (d := d) Real.tanh id hid) dIn dOut)
    (x : Matrix T dIn ℝ) :
    eval (Arch.mlp Real.tanh id hid) 0 θ x = (x * Cm θ).map Real.tanh * Am θ := by
  have h1 : (Fin.last 1 : Fin 2) = (0 : Fin 1).succ := rfl
  have hχ : (Arch.mlp (T := T) (d := d) Real.tanh id hid).χ = id := rfl
  have hf : (Arch.mlp (T := T) (d := d) Real.tanh id hid).f 0 = fun M => M.map Real.tanh := rfl
  -- `h_1 = h_0 0 + tanh(h_0 W_read) W_write` with `h_0 = x E`
  rw [eval, h1, hidden_succ, Fin.castSucc_zero, hidden_zero, hχ, hf]
  simp only [Pi.zero_apply, Matrix.mul_zero, zero_add, id_eq]
  rw [Matrix.mul_assoc x θ.E (θ.read 0)]
  exact Matrix.mul_assoc _ _ _

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dOut] in
/-- Helper: the entries of `F_θ(x)`, `∑_i tanh((x C)_{t i}) A_{i o}`. -/
private theorem eval_tanh_apply
    (θ : Params (Arch.mlp (T := T) (d := d) Real.tanh id hid) dIn dOut)
    (x : Matrix T dIn ℝ) (t : T) (o : dOut) :
    eval (Arch.mlp Real.tanh id hid) 0 θ x t o
      = ∑ i : hid 0, Real.tanh ((x * Cm θ) t i) * Am θ i o := by
  rw [eval_tanh_eq, Matrix.mul_apply]
  rfl

/-- Helper: `tanh' = 1 - tanh²` (from `tanh = sinh / cosh` and `cosh² - sinh² = 1`). -/
private theorem hasDerivAt_tanh (y : ℝ) :
    HasDerivAt Real.tanh (1 - Real.tanh y ^ 2) y := by
  have hfun : Real.tanh = fun z => Real.sinh z / Real.cosh z := by
    funext z; exact Real.tanh_eq_sinh_div_cosh z
  have h := (Real.hasDerivAt_sinh y).div (Real.hasDerivAt_cosh y) (Real.cosh_pos y).ne'
  have hc := (Real.cosh_pos y).ne'
  have heq : 1 - Real.tanh y ^ 2
      = (Real.cosh y * Real.cosh y - Real.sinh y * Real.sinh y) / Real.cosh y ^ 2 := by
    rw [Real.tanh_eq_sinh_div_cosh]
    field_simp
  rw [heq, hfun]
  exact h

/-- Helper: `tanh` is differentiable. -/
private theorem differentiable_tanh : Differentiable ℝ Real.tanh :=
  fun y => (hasDerivAt_tanh y).differentiableAt

/-- Helper: `tanh` on every entry of a matrix is differentiable. -/
private theorem differentiable_map_tanh {m n : Type*} [Fintype m] [Fintype n] :
    Differentiable ℝ (fun M : Matrix m n ℝ => M.map Real.tanh) :=
  differentiable_pi.2 fun i => differentiable_pi.2 fun j =>
    differentiable_tanh.comp (differentiable_pi.1 (differentiable_pi.1 differentiable_id i) j)

omit [Nonempty T] [DecidableEq d] [Fintype d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the fixed map of the `tanh` block is differentiable. -/
private theorem differentiable_f_tanh :
    ∀ ℓ, Differentiable ℝ ((Arch.mlp (T := T) (d := d) Real.tanh id hid).f ℓ) :=
  fun _ => differentiable_map_tanh

/-- Helper: a polynomial `a + τ b + τ² c` has derivative `b` at `τ = 0`. -/
private theorem hasDerivAt_quad (a b c : ℝ) :
    HasDerivAt (fun τ : ℝ => a + τ * b + τ * τ * c) b 0 := by
  have h := ((hasDerivAt_id' (x := (0 : ℝ))).mul_const b).const_add a |>.add
    (((hasDerivAt_id' (x := (0 : ℝ))).mul (hasDerivAt_id' (x := (0 : ℝ)))).mul_const c)
  convert h using 1
  ring

omit [Fintype T] [Nonempty T] [DecidableEq d] in
/-- Helper: the line `τ ↦ θ + τ η` has velocity `η`. -/
private theorem hasDerivAt_line
    (θ η : Params (Arch.mlp (T := T) (d := d) Real.tanh id hid) dIn dOut) :
    HasDerivAt (fun τ : ℝ => θ + τ • η) η 0 := by
  have h := ((hasDerivAt_id (0 : ℝ)).smul_const η).const_add θ
  rw [one_smul] at h
  exact h

omit [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the line `τ ↦ θ + τ η` passes through `θ` at `τ = 0`. -/
private theorem line_zero (θ η : Params (Arch.mlp (T := T) (d := d) Real.tanh id hid) dIn dOut) :
    θ = θ + (0 : ℝ) • η := by
  apply Params.ext' <;> intros <;> simp

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: along the line, `C(τ) = C + τ ∂C + τ² η_E η_read`. -/
private theorem Cm_line (θ η : Params (Arch.mlp (T := T) (d := d) Real.tanh id hid) dIn dOut)
    (τ : ℝ) :
    Cm (θ + τ • η) = Cm θ + τ • dCm θ η + (τ * τ) • Cm η := by
  simp only [Cm, dCm, rd_line, Params.add_E, Params.smul_E, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_smul, Matrix.smul_mul, smul_add, smul_smul]
  abel

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: along the line, `A(τ) = A + τ ∂A + τ² η_write η_D`. -/
private theorem Am_line (θ η : Params (Arch.mlp (T := T) (d := d) Real.tanh id hid) dIn dOut)
    (τ : ℝ) :
    Am (θ + τ • η) = Am θ + τ • dAm θ η + (τ * τ) • Am η := by
  simp only [Am, dAm, wr_line, Params.add_D, Params.smul_D, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_smul, Matrix.smul_mul, smul_add, smul_smul]
  abel

omit [Fintype T] [Nonempty T] [DecidableEq d] in
/-- Helper: the entries of `F_{θ + τ η}(x)` as functions of `τ`. -/
private theorem eval_line_apply
    (θ η : Params (Arch.mlp (T := T) (d := d) Real.tanh id hid) dIn dOut)
    (x : Matrix T dIn ℝ) (t : T) (o : dOut) (τ : ℝ) :
    eval (Arch.mlp Real.tanh id hid) 0 (θ + τ • η) x t o = ∑ i : hid 0,
      Real.tanh ((x * Cm θ) t i + τ * (x * dCm θ η) t i + τ * τ * (x * Cm η) t i) *
        (Am θ i o + τ * dAm θ η i o + τ * τ * Am η i o) := by
  rw [eval_tanh_apply, Cm_line, Am_line]
  simp only [Matrix.mul_add, Matrix.mul_smul]
  rfl

omit [Nonempty T] [DecidableEq d] in
/-- Helper (Step 3 of the paper, the chain rule): the derivative of `θ ↦ F_θ(x)` along `η` has
the entries `∑_i [tanh(z_i) (∂A)_{i o} + tanh'(z_i) (x ∂C)_{t i} A_{i o}]`, `z_i = (x C)_{t i}`. -/
private theorem fderiv_eval_apply
    (θ η : Params (Arch.mlp (T := T) (d := d) Real.tanh id hid) dIn dOut)
    (x : Matrix T dIn ℝ) (t : T) (o : dOut) :
    fderiv ℝ (fun θ' => eval (Arch.mlp Real.tanh id hid) 0 θ' x) θ η t o = ∑ i : hid 0,
      (Real.tanh ((x * Cm θ) t i) * dAm θ η i o
        + (1 - Real.tanh ((x * Cm θ) t i) ^ 2) * (x * dCm θ η) t i * Am θ i o) := by
  have hdiff := differentiable_eval (A := Arch.mlp (T := T) (d := d) Real.tanh id hid) (S := 0)
    (dIn := dIn) (dOut := dOut) differentiable_f_tanh differentiable_id x
  -- the chain rule along the line `τ ↦ θ + τ η`
  have h1 : HasDerivAt (fun τ : ℝ => eval (Arch.mlp Real.tanh id hid) 0 (θ + τ • η) x)
      (fderiv ℝ (fun θ' => eval (Arch.mlp Real.tanh id hid) 0 θ' x) θ η) 0 :=
    (hdiff θ).hasFDerivAt.comp_hasDerivAt_of_eq 0 (hasDerivAt_line θ η) (line_zero θ η)
  have h2 := hasDerivAt_pi.1 (hasDerivAt_pi.1 h1 t) o
  -- the same derivative computed entrywise: products and sums of real functions of `τ`
  have h3 : HasDerivAt (fun τ : ℝ => eval (Arch.mlp Real.tanh id hid) 0 (θ + τ • η) x t o)
      (∑ i : hid 0, (Real.tanh ((x * Cm θ) t i) * dAm θ η i o
        + (1 - Real.tanh ((x * Cm θ) t i) ^ 2) * (x * dCm θ η) t i * Am θ i o)) 0 := by
    rw [funext fun τ => eval_line_apply θ η x t o τ]
    refine HasDerivAt.fun_sum fun i _ => ?_
    have hu := hasDerivAt_quad ((x * Cm θ) t i) ((x * dCm θ η) t i) ((x * Cm η) t i)
    have hv := hasDerivAt_quad (Am θ i o) (dAm θ η i o) (Am η i o)
    have h := ((hasDerivAt_tanh _).comp (0 : ℝ) hu).mul hv
    convert h using 1
    · rfl
    · simp only [Function.comp_apply, zero_mul, mul_zero, add_zero]
      ring
  exact h2.unique h3

variable (θ : Params (Arch.mlp (T := T) (d := d) Real.tanh id hid) dIn dOut)

/-- Under the conditions, every flat direction of one `tanh` block is the direction of two changes
of basis (Steps 1 to 3 of the proof of Theorem C.1). -/
theorem flat_le_range_cobDir_tanh (hθ : OneBlockGeneric θ) (η : Params _ dIn dOut)
    (hη : η ∈ flat (Arch.mlp Real.tanh id hid) 0 θ) :
    ∃ X : Fin 2 → Matrix d d ℝ, η = cobDir θ X := by
  -- Step 3: the derivative of `F(θ, x)` along `η` vanishes at every input, entry by entry
  have hzero : ∀ (x : Matrix T dIn ℝ) (t : T) (o : dOut), ∑ i : hid 0,
      (Real.tanh ((x * Cm θ) t i) * dAm θ η i o
        + (1 - Real.tanh ((x * Cm θ) t i) ^ 2) * (x * dCm θ η) t i * Am θ i o) = 0 := by
    intro x t o
    rw [← fderiv_eval_apply θ η x t o]
    have h := LinearMap.mem_ker.1 ((Submodule.mem_iInf _).1 hη x)
    exact congrFun (congrFun h t) o
  -- Step 2, Lemma C.3 for `tanh` (inputs `x` with all rows equal to `v`): `∂C = 0` and `∂A = 0`
  obtain ⟨-, -, hc, -, ha⟩ := tanh_units_flat_eq_zero (fun i => (Cm θ)ᵀ i) 0 (fun i => Am θ i)
    0 0 (fun i => (dCm θ η)ᵀ i) 0 (fun i => dAm θ η i) (fun i => hθ.row_ne_zero i)
    (fun i => hθ.col_ne_zero i) (fun i j hij => hθ.col_not_collinear i j hij) (by
      intro v
      funext o
      have h := hzero (Matrix.of fun _ => v) (Classical.arbitrary T) o
      simp only [Matrix.vecMul_zero, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        Pi.zero_apply, add_zero, zero_add]
      exact h)
  -- Step 1, Lemma C.2: a direction that keeps `C` and `A` is that of two changes of basis
  have hC : η.E * θ.read 0 + θ.E * η.read 0 = 0 := by
    ext a i
    exact congrFun (congrFun hc i) a
  have hA : η.write 0 * θ.D + θ.write 0 * η.D = 0 := by
    ext i o
    exact congrFun (congrFun ha i) o
  exact (keeps_products_iff_mem_range_cobDir θ η hθ.rank_E hθ.rank_D hθ.rank_read
    hθ.rank_write).1 ⟨hC, hA⟩

/-- **Theorem 5.1 for a `tanh` block, under the conditions of its proof:** the functional
dimension is `P - 2 d²`. -/
theorem funDim_tanh_oneBlock (hθ : OneBlockGeneric θ) :
    funDim (Arch.mlp Real.tanh id hid) 0 θ + 2 * Fintype.card d ^ 2
      = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) Real.tanh id hid) dIn dOut) := by
  sorry

/-- The conditions hold at generic parameters, when `d_in, d_out, d_hidden ≥ d ≥ 2`. -/
theorem ae_oneBlockGeneric
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) Real.tanh id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ θ ∂μ, OneBlockGeneric θ := by
  sorry

/-- **Theorem 5.1 for a `tanh` block:** with one block, without normalization and without biases,
with `d_in, d_out, d_hidden ≥ d ≥ 2`, the functional dimension is `P - 2 d²` at generic
parameters. -/
theorem ae_funDim_tanh_oneBlock
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) Real.tanh id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ θ ∂μ, funDim (Arch.mlp Real.tanh id hid) 0 θ + 2 * Fintype.card d ^ 2
      = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) Real.tanh id hid) dIn dOut) := by
  sorry

end Skips
