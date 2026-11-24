import SkipsLean.OneBlock.Rescale
import SkipsLean.OneBlock.Residual
import SkipsLean.Residual.UpperBoundSymmetries

/-!
# The one-block theorem with a skip, for ReLU and ReLU² blocks

Paper (skips): Theorem 4.6 (i) (Theorem B.1 (i) in the appendix) for a ReLU and for a ReLU² block.
"Let `L = 1` … Without normalization, the residual network satisfies the equality condition. So
does the skipless network, and the skip raises the functional dimension by exactly `d²`."
For these blocks the equality condition with a skip is `fd = P - d² - d_hidden` at generic
parameters, and without a skip `fd = P - 2 d² - d_hidden` (`OneBlock/Rescale.lean`).

As in `OneBlock/Rescale.lean`, two statements are made for each kind of block: the value of
`funDim`, and a batch of inputs with no hidden unit at its kink on which the Jacobian has that
rank. The skip does not change the arguments of the hidden units of the one block, so the inputs
with no hidden unit at its kink are the same set `noKink θ`.

The proof is stated once, for every activation that is positively homogeneous of degree `k`,
differentiable away from `0`, and satisfies Lemma C.3 with the rescalings (`UnitsRescale`), whose
statement includes the linear term `x M` of the skip (`M = E D`).
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {hid : Fin 1 → Type} [∀ ℓ, Fintype (hid ℓ)]
variable {σ σ' : ℝ → ℝ}

/-! ### Helpers: linear algebra, and Lemma B.2 of the skips paper (as in `Residual.lean`) -/

/-- Helper (copy of `cancel_left_of_rank_res` of `Residual.lean`): a matrix whose rank is its
number of columns cancels on the left, via a left inverse. -/
private theorem cancel_left_of_rank_rr {m n k : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (M : Matrix m n ℝ) (hM : M.rank = Fintype.card n) {X Y : Matrix n k ℝ}
    (h : M * X = M * Y) : X = Y := by
  obtain ⟨B, hB⟩ := Matrix.vecMul_surjective_iff_exists_left_inverse.mp
    (Matrix.vecMul_surjective_iff_rank_eq_card.mpr hM)
  have := congrArg (B * ·) h
  simpa only [← Matrix.mul_assoc, hB, Matrix.one_mul] using this

/-- Helper (copy of `cancel_right_of_rank_res`): a matrix whose rank is its number of rows cancels
on the right, via a right inverse. -/
private theorem cancel_right_of_rank_rr {m n k : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    (M : Matrix m n ℝ) (hM : M.rank = Fintype.card m) {X Y : Matrix k m ℝ}
    (h : X * M = Y * M) : X = Y := by
  obtain ⟨R, hR⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.mp
    (Matrix.mulVec_surjective_iff_rank_eq_card.mpr hM)
  have := congrArg (· * R) h
  simpa only [Matrix.mul_assoc, hR, Matrix.mul_one] using this

/-- Helper: `M = E D`, the linear part of the residual network `x ↦ x M + σ(x C) A`. -/
private def MmR {A : Arch T d 1} (θ : Params A dIn dOut) : Matrix dIn dOut ℝ :=
  θ.E * θ.D

/-- Helper: the derivative `∂M = η_E D + E η_D` of `M` along `η`. -/
private def dMmR {A : Arch T d 1} (θ η : Params A dIn dOut) : Matrix dIn dOut ℝ :=
  η.E * θ.D + θ.E * η.D

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: along the line, `M(τ) = M + τ ∂M + τ² η_E η_D`. -/
private theorem MmR_line {A : Arch T d 1} (θ η : Params A dIn dOut) (τ : ℝ) :
    MmR (θ + τ • η) = MmR θ + τ • dMmR θ η + (τ * τ) • MmR η := by
  simp only [MmR, dMmR, Params.add_E, Params.smul_E, Params.add_D, Params.smul_D, Matrix.mul_add,
    Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, smul_add, smul_smul]
  abel

omit [Fintype T] [Nonempty T] in
/-- Helper (Lemma B.2 of the skips paper, copy of `eq_const_of_keeps_ED`): if `E` and `D` have
rank `d`, the direction of the two changes of basis `X_0` at `h_0` and `X_1` at `h_1` keeps
`M = E D` to first order only if `X_0 = X_1`, since `∂M = E X_0 D - E X_1 D`. -/
private theorem eq_const_of_keeps_ED_rr {A : Arch T d 1} (θ : Params A dIn dOut)
    (X : Fin 2 → Matrix d d ℝ) (hE : θ.E.rank = Fintype.card d)
    (hD : θ.D.rank = Fintype.card d) (hM : dMmR θ (cobDir θ X) = 0) :
    X = fun _ => X 0 := by
  -- `∂M = E X_0 D - E X_1 D = 0`
  have h1 : θ.E * (X 0 * θ.D) = θ.E * (X 1 * θ.D) := by
    have h : θ.E * X 0 * θ.D + θ.E * -(X 1 * θ.D) = 0 := hM
    rw [Matrix.mul_neg, Matrix.mul_assoc, add_neg_eq_zero] at h
    exact h
  -- cancel `E` on the left and `D` on the right
  have h01 : X 0 = X 1 :=
    cancel_right_of_rank_rr θ.D hD (cancel_left_of_rank_rr θ.E hE h1)
  exact funext (Fin.forall_fin_two.2 ⟨rfl, h01.symm⟩)

/-! ### Helpers: the function of one residual MLP block and its derivative -/

/-- Helper: the read of the block, with its columns indexed by the hidden units. -/
private def rdR (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) :
    Matrix d (hid 0) ℝ :=
  θ.read 0

/-- Helper: the write of the block, with its rows indexed by the hidden units. -/
private def wrR (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) :
    Matrix (hid 0) d ℝ :=
  θ.write 0

/-- Helper: `C = E W_read`. -/
private def CmR (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) :
    Matrix dIn (hid 0) ℝ :=
  θ.E * rdR θ

/-- Helper: `A = W_write D`. -/
private def AmR (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) :
    Matrix (hid 0) dOut ℝ :=
  wrR θ * θ.D

/-- Helper: the derivative `∂C = η_E W_read + E η_read` of `C` along `η`. -/
private def dCmR (θ η : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) :
    Matrix dIn (hid 0) ℝ :=
  η.E * rdR θ + θ.E * rdR η

/-- Helper: the derivative `∂A = η_write D + W_write η_D` of `A` along `η`. -/
private def dAmR (θ η : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) :
    Matrix (hid 0) dOut ℝ :=
  wrR η * θ.D + wrR θ * η.D

omit [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the read is linear in the parameters. -/
private theorem rdR_line (θ η : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)
    (τ : ℝ) : rdR (θ + τ • η) = rdR θ + τ • rdR η := rfl

omit [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the write is linear in the parameters. -/
private theorem wrR_line (θ η : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)
    (τ : ℝ) : wrR (θ + τ • η) = wrR θ + τ • wrR η := rfl

omit [Fintype T] [Nonempty T] [Fintype dOut] in
/-- Helper: the function of one residual MLP block, `F_θ(x) = x M + σ(x C) A` (the stream matrix
is `1`). -/
private theorem eval_res_eq (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)
    (x : Matrix T dIn ℝ) :
    eval (Arch.mlp σ id hid) 1 θ x = x * MmR θ + (x * CmR θ).map σ * AmR θ := by
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
private theorem eval_res_apply
    (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)
    (x : Matrix T dIn ℝ) (t : T) (o : dOut) :
    eval (Arch.mlp σ id hid) 1 θ x t o
      = (x * MmR θ) t o + ∑ i : hid 0, σ ((x * CmR θ) t i) * AmR θ i o := by
  rw [eval_res_eq]
  rfl

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: along the line, `C(τ) = C + τ ∂C + τ² η_E η_read`. -/
private theorem CmR_line (θ η : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)
    (τ : ℝ) :
    CmR (θ + τ • η) = CmR θ + τ • dCmR θ η + (τ * τ) • CmR η := by
  simp only [CmR, dCmR, rdR_line, Params.add_E, Params.smul_E, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_smul, Matrix.smul_mul, smul_add, smul_smul]
  abel

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: along the line, `A(τ) = A + τ ∂A + τ² η_write η_D`. -/
private theorem AmR_line (θ η : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)
    (τ : ℝ) :
    AmR (θ + τ • η) = AmR θ + τ • dAmR θ η + (τ * τ) • AmR η := by
  simp only [AmR, dAmR, wrR_line, Params.add_D, Params.smul_D, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_smul, Matrix.smul_mul, smul_add, smul_smul]
  abel

omit [Fintype T] [Nonempty T] [Fintype dOut] in
/-- Helper: the entries of `F_{θ + τ η}(x)` as functions of `τ`. -/
private theorem eval_res_line_apply
    (θ η : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)
    (x : Matrix T dIn ℝ) (t : T) (o : dOut) (τ : ℝ) :
    eval (Arch.mlp σ id hid) 1 (θ + τ • η) x t o
      = ((x * MmR θ) t o + τ * (x * dMmR θ η) t o + τ * τ * (x * MmR η) t o) + ∑ i : hid 0,
        σ ((x * CmR θ) t i + τ * (x * dCmR θ η) t i + τ * τ * (x * CmR η) t i) *
          (AmR θ i o + τ * dAmR θ η i o + τ * τ * AmR η i o) := by
  rw [eval_res_apply, MmR_line, CmR_line, AmR_line]
  simp only [Matrix.mul_add, Matrix.mul_smul]
  rfl

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dOut] in
/-- Helper: at an input of `noKink θ`, every entry of `x C` is nonzero. -/
private theorem noKinkR_apply {θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut}
    {x : Matrix T dIn ℝ} (hx : x ∈ noKink θ) (t : T) (i : hid 0) : (x * CmR θ) t i ≠ 0 := by
  have h := hx t i
  rwa [Matrix.mul_assoc] at h

/-- At an input with no hidden unit at its kink, the output of a residual network of one block is
differentiable in the parameters, when `σ` is differentiable away from `0`. -/
theorem differentiableAt_eval_residual_of_mem_noKink (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) (x : Matrix T dIn ℝ)
    (hx : x ∈ noKink θ) :
    DifferentiableAt ℝ
      (fun θ' : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut =>
        eval (Arch.mlp σ id hid) 1 θ' x) θ := by
  -- the entries of `M = E D`, `C = E W_read` and `A = W_write D` are polynomials in the
  -- parameters
  have hM : ∀ (a : dIn) (o : dOut), DifferentiableAt ℝ
      (fun θ' : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut => MmR θ' a o) θ :=
    fun a o => (analyticOnNhd_mul_apply (Params.linE (A := Arch.mlp (T := T) (d := d) σ id hid)
      (dIn := dIn) (dOut := dOut)) Params.linD a o θ (Set.mem_univ _)).differentiableAt
  have hC : ∀ (a : dIn) (i : hid 0), DifferentiableAt ℝ
      (fun θ' : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut => CmR θ' a i) θ :=
    fun a i => (analyticOnNhd_E_mul_read (A := Arch.mlp (T := T) (d := d) σ id hid)
      (dOut := dOut) 0 a i θ (Set.mem_univ _)).differentiableAt
  have hA : ∀ (i : hid 0) (o : dOut), DifferentiableAt ℝ
      (fun θ' : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut => AmR θ' i o) θ :=
    fun i o => (analyticOnNhd_write_mul_D (A := Arch.mlp (T := T) (d := d) σ id hid)
      (dIn := dIn) 0 i o θ (Set.mem_univ _)).differentiableAt
  -- so are the entries of `x M` and of `x C`
  have hxM : ∀ (t : T) (o : dOut), DifferentiableAt ℝ
      (fun θ' : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut => (x * MmR θ') t o) θ := by
    intro t o
    simp only [Matrix.mul_apply]
    exact DifferentiableAt.fun_sum fun a _ => (hM a o).const_mul (x t a)
  have hxC : ∀ (t : T) (i : hid 0), DifferentiableAt ℝ
      (fun θ' : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut => (x * CmR θ') t i) θ := by
    intro t i
    simp only [Matrix.mul_apply]
    exact DifferentiableAt.fun_sum fun a _ => (hC a i).const_mul (x t a)
  -- the entry `(t, o)` of `F_θ'(x)` is `(x M)_{t o} + ∑_i σ((x C)_{t i}) A_{i o}`, and `σ` is
  -- differentiable at every `(x C)_{t i}`, which is not `0`
  refine differentiableAt_pi.2 fun t => differentiableAt_pi.2 fun o => ?_
  simp only [eval_res_apply]
  exact (hxM t o).add (DifferentiableAt.fun_sum fun i _ =>
    ((hσ _ (noKinkR_apply hx t i)).differentiableAt.comp θ (hxC t i)).mul (hA i o))

/-- Helper (Step 3 of the paper, the chain rule, at an input of `noKink θ`): the derivative of
`θ ↦ F_θ(x)` along `η` has the entries
`(x ∂M)_{t o} + ∑_i [σ(z_i) (∂A)_{i o} + σ'(z_i) (x ∂C)_{t i} A_{i o}]`, `z_i = (x C)_{t i}`. -/
private theorem fderiv_eval_res_apply_of_mem (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (θ η : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)
    (x : Matrix T dIn ℝ) (hx : x ∈ noKink θ) (t : T) (o : dOut) :
    fderiv ℝ (fun θ' => eval (Arch.mlp σ id hid) 1 θ' x) θ η t o
      = (x * dMmR θ η) t o + ∑ i : hid 0,
        (σ ((x * CmR θ) t i) * dAmR θ η i o
          + σ' ((x * CmR θ) t i) * (x * dCmR θ η) t i * AmR θ i o) := by
  -- the chain rule along the line `τ ↦ θ + τ η`
  have h1 := hasDerivAt_eval_line (A := Arch.mlp (T := T) (d := d) σ id hid) 1 θ η x
    (differentiableAt_eval_residual_of_mem_noKink hσ θ x hx)
  have h2 := hasDerivAt_pi.1 (hasDerivAt_pi.1 h1 t) o
  -- the same derivative computed entrywise: a polynomial in `τ`, plus products and sums of real
  -- functions of `τ`
  have h3 : HasDerivAt (fun τ : ℝ => eval (Arch.mlp σ id hid) 1 (θ + τ • η) x t o)
      ((x * dMmR θ η) t o + ∑ i : hid 0, (σ ((x * CmR θ) t i) * dAmR θ η i o
        + σ' ((x * CmR θ) t i) * (x * dCmR θ η) t i * AmR θ i o)) 0 := by
    rw [funext fun τ => eval_res_line_apply θ η x t o τ]
    refine (hasDerivAt_quad _ _ _).add (HasDerivAt.fun_sum fun i _ => ?_)
    have hu := hasDerivAt_quad ((x * CmR θ) t i) ((x * dCmR θ η) t i) ((x * CmR η) t i)
    have hv := hasDerivAt_quad (AmR θ i o) (dAmR θ η i o) (AmR η i o)
    -- `σ` is differentiable at `(x C)_{t i}`, which is not `0`
    have h := ((hσ _ (noKinkR_apply hx t i)).comp_of_eq (0 : ℝ) hu
      (by simp only [zero_mul, add_zero])).mul hv
    convert h using 1
    · rfl
    · simp only [Function.comp_apply, zero_mul, mul_zero, add_zero]
      ring
  exact h2.unique h3

/-! ### Helpers: the derivative of `C` and `A` along a rescaling (as in `Rescale.lean`) -/

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: `∂C` is linear in the direction. -/
private theorem dCmR_sub (θ η ρ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) :
    dCmR θ (η - ρ) = dCmR θ η - dCmR θ ρ := by
  show (η.E - ρ.E) * rdR θ + θ.E * (rdR η - rdR ρ)
    = (η.E * rdR θ + θ.E * rdR η) - (ρ.E * rdR θ + θ.E * rdR ρ)
  rw [Matrix.sub_mul, Matrix.mul_sub]
  abel

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: `∂A` is linear in the direction. -/
private theorem dAmR_sub (θ η ρ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) :
    dAmR θ (η - ρ) = dAmR θ η - dAmR θ ρ := by
  show (wrR η - wrR ρ) * θ.D + wrR θ * (η.D - ρ.D)
    = (wrR η * θ.D + wrR θ * η.D) - (wrR ρ * θ.D + wrR θ * ρ.D)
  rw [Matrix.sub_mul, Matrix.mul_sub]
  abel

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: along a rescaling, the column `c_i` of `C` moves by `α_i c_i`. -/
private theorem dCmR_rescale (k : ℕ)
    (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) (α : ∀ ℓ, hid ℓ → ℝ)
    (a : dIn) (i : hid 0) :
    dCmR θ (rescaleDirMlp k θ α) a i = α 0 i * CmR θ a i := by
  show ((0 : Matrix dIn d ℝ) * rdR θ + θ.E * rdR (rescaleDirMlp k θ α)) a i
    = α 0 i * (θ.E * rdR θ) a i
  rw [Matrix.zero_mul, zero_add, Matrix.mul_apply, Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  show θ.E a j * (α 0 i * θ.read 0 j i) = α 0 i * (θ.E a j * θ.read 0 j i)
  ring

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: along a rescaling, the row `a_i` of `A` moves by `-k α_i a_i`. -/
private theorem dAmR_rescale (k : ℕ)
    (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) (α : ∀ ℓ, hid ℓ → ℝ)
    (i : hid 0) (o : dOut) :
    dAmR θ (rescaleDirMlp k θ α) i o = -((k : ℝ) * α 0 i) * AmR θ i o := by
  show (wrR (rescaleDirMlp k θ α) * θ.D + wrR θ * (0 : Matrix d dOut ℝ)) i o
    = -((k : ℝ) * α 0 i) * (wrR θ * θ.D) i o
  rw [Matrix.mul_zero, add_zero, Matrix.mul_apply, Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  show -((k : ℝ) * α 0 i) * θ.write 0 i j * θ.D j o
    = -((k : ℝ) * α 0 i) * (θ.write 0 i j * θ.D j o)
  ring

/-- **Steps 1 to 3 of the proof of Theorem B.1 (i) for an activation with the rescalings.** Under
the conditions `OneBlockGeneric`, a direction that is flat for the residual network at every
input with no hidden unit at its kink is the sum of the direction of one change of basis, the
same at both hidden states, and a direction of the rescalings of the hidden units. -/
theorem flatOn_noKink_le_mlp_rescale_residual {k : ℕ}
    (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (hU : UnitsRescale σ σ' k dIn dOut (hid 0))
    (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) (hθ : OneBlockGeneric θ)
    (η : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)
    (hη : η ∈ flatOn (Arch.mlp σ id hid) 1 θ (noKink θ)) :
    ∃ (X : Matrix d d ℝ) (α : ∀ ℓ, hid ℓ → ℝ),
      η = cobDir θ (fun _ => X) + rescaleDirMlp k θ α := by
  -- Step 3: at every input with no hidden unit at its kink, the derivative of `F(θ, x)` along
  -- `η` vanishes, entry by entry
  have hzero : ∀ x ∈ noKink θ, ∀ (t : T) (o : dOut), (x * dMmR θ η) t o + ∑ i : hid 0,
      (σ ((x * CmR θ) t i) * dAmR θ η i o
        + σ' ((x * CmR θ) t i) * (x * dCmR θ η) t i * AmR θ i o) = 0 := by
    intro x hx t o
    rw [← fderiv_eval_res_apply_of_mem hσ θ η x hx t o]
    have h := LinearMap.mem_ker.1 ((Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hη x) hx)
    exact congrFun (congrFun h t) o
  -- Step 2, Lemma C.3 with the linear term `x ∂M` (inputs `x` with all rows equal to a `v` with
  -- `v c_i ≠ 0` for all `i`): `∂M = 0`, and every unit is only rescaled, `∂c_i = λ_i c_i` and
  -- `∂a_i = -k λ_i a_i`
  obtain ⟨hm, -, lam, hlam⟩ := hU (fun i => (CmR θ)ᵀ i) 0 (fun i => AmR θ i)
    (dMmR θ η) 0 (fun i => (dCmR θ η)ᵀ i) 0 (fun i => dAmR θ η i) (fun i => hθ.row_ne_zero i)
    (fun i => hθ.col_ne_zero i) (fun i j hij => hθ.col_not_collinear i j hij) (by
      intro v hv
      have hx : (Matrix.of fun _ : T => v) ∈ noKink θ := by
        intro t i
        have h := hv i
        simp only [Pi.zero_apply, add_zero] at h
        rw [Matrix.mul_assoc]
        exact h
      funext o
      have h := hzero _ hx (Classical.arbitrary T) o
      simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
        add_zero]
      exact h)
  -- the rescaling with these `λ_i` (one block: `ℓ = 0`)
  let α' : ∀ ℓ : Fin 1, hid ℓ → ℝ := fun ℓ => Fin.cases lam (fun l => l.elim0) ℓ
  -- `η - rescaleDirMlp k θ α'` keeps `C` and `A` to first order
  have hC : dCmR θ (η - rescaleDirMlp k θ α') = 0 := by
    ext a i
    rw [dCmR_sub, Matrix.sub_apply, dCmR_rescale, Matrix.zero_apply, sub_eq_zero]
    exact congrFun (hlam i).1 a
  have hA : dAmR θ (η - rescaleDirMlp k θ α') = 0 := by
    ext i o
    rw [dAmR_sub, Matrix.sub_apply, dAmR_rescale, Matrix.zero_apply, sub_eq_zero]
    exact congrFun (hlam i).2.2 o
  -- Step 1, Lemma C.2: a direction that keeps `C` and `A` is that of two changes of basis
  obtain ⟨X, hX⟩ := (keeps_products_iff_mem_range_cobDir θ (η - rescaleDirMlp k θ α')
    hθ.rank_E hθ.rank_D hθ.rank_read hθ.rank_write).1 ⟨hC, hA⟩
  -- the rescaling leaves `E` and `D` alone, so `cobDir θ X` keeps `M = E D` as `η` does
  have hM : dMmR θ (cobDir θ X) = 0 := by
    rw [← hX]
    show (η.E - 0) * θ.D + θ.E * (η.D - 0) = 0
    rw [sub_zero, sub_zero]
    exact hm
  -- Lemma B.2 of the skips paper: then `X_0 = X_1`
  have hXc := eq_const_of_keeps_ED_rr θ X hθ.rank_E hθ.rank_D hM
  exact ⟨X 0, α', (sub_eq_iff_eq_add.1 hX).trans
    (congrArg (fun Y => cobDir θ Y + rescaleDirMlp k θ α') hXc)⟩

/-! ### Helpers: the space of the directions of one change of basis and of the rescalings -/

omit [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (copy of `rescaleDirMlpLin` of `Rescale.lean`): `α ↦ rescaleDirMlp k θ α` is
linear. -/
private noncomputable def rescaleDirMlpLinRR (k : ℕ)
    (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) :
    (∀ ℓ : Fin 1, hid ℓ → ℝ) →ₗ[ℝ] Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut where
  toFun := rescaleDirMlp k θ
  map_add' α β := by
    apply Params.ext'
    · exact (add_zero 0).symm
    · intro ℓ
      ext a i
      show (α + β) ℓ i * θ.read ℓ a i = α ℓ i * θ.read ℓ a i + β ℓ i * θ.read ℓ a i
      rw [Pi.add_apply, Pi.add_apply]
      ring
    · intro ℓ
      ext i a
      show -((k : ℝ) * (α + β) ℓ i) * θ.write ℓ i a
        = -((k : ℝ) * α ℓ i) * θ.write ℓ i a + -((k : ℝ) * β ℓ i) * θ.write ℓ i a
      rw [Pi.add_apply, Pi.add_apply]
      ring
    · exact (add_zero 0).symm
  map_smul' c α := by
    apply Params.ext'
    · exact (smul_zero c).symm
    · intro ℓ
      ext a i
      show (c • α) ℓ i * θ.read ℓ a i = c * (α ℓ i * θ.read ℓ a i)
      rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul]
      ring
    · intro ℓ
      ext i a
      show -((k : ℝ) * (c • α) ℓ i) * θ.write ℓ i a = c * (-((k : ℝ) * α ℓ i) * θ.write ℓ i a)
      rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul]
      ring
    · exact (smul_zero c).symm

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the directions of one change of basis and of the rescalings,
`(X, α) ↦ cobDir θ (X, X) + rescaleDirMlp k θ α`, as a linear map. -/
private noncomputable def dirRR (k : ℕ)
    (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) :
    (Matrix d d ℝ × (∀ ℓ : Fin 1, hid ℓ → ℝ)) →ₗ[ℝ]
      Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut :=
  ((cobDirLin θ).comp (LinearMap.pi fun _ => LinearMap.id)).coprod (rescaleDirMlpLinRR k θ)

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the values of `dirRR`. -/
private theorem dirRR_apply (k : ℕ)
    (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)
    (p : Matrix d d ℝ × (∀ ℓ : Fin 1, hid ℓ → ℝ)) :
    dirRR k θ p = cobDir θ (fun _ => p.1) + rescaleDirMlp k θ p.2 := rfl

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the pairs `(X, α)` of one `d × d` matrix and one number per hidden unit form a space
of dimension `d² + d_hidden`. -/
private theorem finrank_dirDomainRR :
    Module.finrank ℝ (Matrix d d ℝ × (∀ ℓ : Fin 1, hid ℓ → ℝ))
      = Fintype.card d ^ 2 + Fintype.card (hid 0) := by
  rw [Module.finrank_prod, Module.finrank_matrix, Module.finrank_self, mul_one, ← sq,
    Module.finrank_pi_fintype]
  simp only [Module.finrank_fintype_fun_eq_card, Finset.univ_unique, Fin.default_eq_zero,
    Finset.sum_singleton]

omit [Nonempty T] in
/-- Helper: the directions `cobDir θ (X, X) + rescaleDirMlp k θ α` are flat for the residual
network (one change of basis at both hidden states and the rescalings are symmetries; no
differentiability of `σ` is used). -/
private theorem range_dirRR_le_flat {k : ℕ}
    (hhom : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) :
    LinearMap.range (dirRR k θ) ≤ flat (Arch.mlp σ id hid) 1 θ := by
  rintro _ ⟨p, rfl⟩
  rw [dirRR_apply]
  exact add_mem (cobDir_const_mem_flat_residual' θ rfl p.1) (rescaleDirMlp_mem_flat hhom θ 1 p.2)

/-- Helper: the directions that are flat for the residual network at every input of `noKink θ`
are among the directions `cobDir θ (X, X) + rescaleDirMlp k θ α`. -/
private theorem flatOn_noKink_le_range_dirRR {k : ℕ}
    (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (hU : UnitsRescale σ σ' k dIn dOut (hid 0))
    (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) (hθ : OneBlockGeneric θ) :
    flatOn (Arch.mlp σ id hid) 1 θ (noKink θ) ≤ LinearMap.range (dirRR k θ) := by
  intro η hη
  obtain ⟨X, α, rfl⟩ := flatOn_noKink_le_mlp_rescale_residual hσ hU θ hθ η hη
  exact LinearMap.mem_range.2 ⟨(X, α), rfl⟩

omit [Nonempty T] in
/-- Helper (Lemma B.1 for these blocks, on the constant families): under the conditions, the
directions `cobDir θ (X, X) + rescaleDirMlp k θ α` form a space of dimension `d² + d_hidden`. -/
private theorem finrank_range_dirRR (k : ℕ)
    (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) (hθ : OneBlockGeneric θ) :
    Module.finrank ℝ (LinearMap.range (dirRR k θ))
      = Fintype.card d ^ 2 + Fintype.card (hid 0) := by
  -- no column of `W_read` vanishes, since the columns of `C = E W_read` do not
  have hv : ∀ ℓ i, (fun a => θ.read ℓ a i) ≠ 0 := by
    intro ℓ i h0
    obtain rfl := Subsingleton.elim ℓ 0
    apply hθ.col_ne_zero i
    funext a
    show ∑ j, θ.E a j * θ.read 0 j i = 0
    exact Finset.sum_eq_zero fun j _ => by
      rw [show θ.read 0 j i = 0 from congrFun h0 j, mul_zero]
  -- `(X, α) ↦ cobDir θ (X, X) + rescaleDirMlp k θ α` is injective: the `E` component gives `X`,
  -- then the read gives `α`
  have hinj0 := cobDir_add_rescaleDirMlp_injective k θ hθ.rank_E
    (fun ℓ => by obtain rfl := Subsingleton.elim ℓ 0; exact hθ.rank_write) hv
  have hinj : Function.Injective (dirRR k θ) := by
    intro p q hpq
    rw [dirRR_apply, dirRR_apply] at hpq
    have h' : cobDir θ (fun _ : Fin (1 + 1) => p.1) + rescaleDirMlp k θ p.2
        = cobDir θ (fun _ : Fin (1 + 1) => q.1) + rescaleDirMlp k θ q.2 := hpq
    have h2 : ((fun _ : Fin (1 + 1) => p.1), p.2) = ((fun _ : Fin (1 + 1) => q.1), q.2) :=
      hinj0 h'
    have h3 := Prod.mk.inj h2
    exact Prod.ext (congrFun h3.1 0) h3.2
  rw [LinearMap.finrank_range_of_inj hinj, finrank_dirDomainRR]

/-- **Theorem 4.6 (i) / B.1 (i) for an activation with the rescalings, under the conditions of
the proof:** with a skip, `fd = P - d² - d_hidden`. -/
theorem funDim_mlp_oneBlock_rescale_residual {k : ℕ}
    (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (hhom : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (hU : UnitsRescale σ σ' k dIn dOut (hid 0))
    (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) (hθ : OneBlockGeneric θ) :
    funDim (Arch.mlp σ id hid) 1 θ + (Fintype.card d ^ 2 + Fintype.card (hid 0))
      = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) := by
  -- the sandwich: the directions `cobDir θ (X, X) + rescaleDirMlp k θ α` ≤ `K(θ)` ≤ the
  -- directions flat on `noKink θ` ≤ the directions `cobDir θ (X, X) + rescaleDirMlp k θ α`
  have hflat : flat (Arch.mlp σ id hid) 1 θ = LinearMap.range (dirRR k θ) :=
    le_antisymm ((flat_le_flatOn θ (noKink θ)).trans (flatOn_noKink_le_range_dirRR hσ hU θ hθ))
      (range_dirRR_le_flat hhom θ)
  -- `fd(θ) = P - dim K(θ)` (Appendix C), and `dim K(θ) = d² + d_hidden`
  have h := funDim_add_finrank_flat' (S := 1) θ
  rwa [hflat, finrank_range_dirRR k θ hθ] at h

/-- The same rank on a batch of inputs with no hidden unit at its kink. -/
theorem exists_jacobianRank_mlp_oneBlock_rescale_residual {k : ℕ}
    (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (hhom : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (hU : UnitsRescale σ σ' k dIn dOut (hid 0))
    (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) (hθ : OneBlockGeneric θ) :
    ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i, X i ∈ noKink θ) ∧
      jacobianRank (Arch.mlp σ id hid) 1 X θ + (Fintype.card d ^ 2 + Fintype.card (hid 0))
        = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) := by
  -- a batch of inputs of `noKink θ`, where the network is differentiable in `θ`, with the rank
  -- `P - dim K_U(θ)`, `U = noKink θ`
  obtain ⟨n, X, hX, h⟩ := exists_jacobianRank_add_finrank_flatOn (S := 1) θ (noKink θ)
    (fun x hx => differentiableAt_eval_residual_of_mem_noKink hσ θ x hx)
  -- the same sandwich: `K_U(θ)` is the space of the directions
  -- `cobDir θ (X, X) + rescaleDirMlp k θ α`
  have hflatOn : flatOn (Arch.mlp σ id hid) 1 θ (noKink θ) = LinearMap.range (dirRR k θ) :=
    le_antisymm (flatOn_noKink_le_range_dirRR hσ hU θ hθ)
      ((range_dirRR_le_flat hhom θ).trans (flat_le_flatOn θ (noKink θ)))
  refine ⟨n, X, hX, ?_⟩
  rwa [hflatOn, finrank_range_dirRR k θ hθ] at h

/-- **Theorem 4.6 (i) for a ReLU block, with a skip:** for `d_in, d_out, d_hidden ≥ d ≥ 2`, at
generic parameters, `fd = P - d² - d_hidden`. -/
theorem ae_funDim_relu_oneBlock_residual
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ θ ∂μ, funDim (Arch.mlp relu id hid) 1 θ
        + (Fintype.card d ^ 2 + Fintype.card (hid 0))
      = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut) := by
  -- the conditions of the proof hold at generic parameters (`Mlp.lean`, for every `σ`)
  exact (ae_oneBlockGeneric μ hd hdIn hdOut hhid).mono fun θ hθ =>
    funDim_mlp_oneBlock_rescale_residual (fun _ hz => hasDerivAt_relu hz) relu_homogeneous
      (relu_unitsRescale dIn dOut (hid 0)) θ hθ

/-- Theorem 4.6 (i) for a ReLU block with a skip, on the paper's inputs: at generic parameters the
Jacobian has the rank `P - d² - d_hidden` on a batch of inputs with no hidden unit at its kink. -/
theorem ae_exists_jacobianRank_relu_oneBlock_residual
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ θ ∂μ, ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i, X i ∈ noKink θ) ∧
      jacobianRank (Arch.mlp relu id hid) 1 X θ
          + (Fintype.card d ^ 2 + Fintype.card (hid 0))
        = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut) := by
  -- the conditions of the proof hold at generic parameters (`Mlp.lean`, for every `σ`)
  exact (ae_oneBlockGeneric μ hd hdIn hdOut hhid).mono fun θ hθ =>
    exists_jacobianRank_mlp_oneBlock_rescale_residual (fun _ hz => hasDerivAt_relu hz)
      relu_homogeneous (relu_unitsRescale dIn dOut (hid 0)) θ hθ

/-- **Theorem 4.6 (i) for a ReLU block:** at generic parameters the skip raises the functional
dimension by exactly `d²`. -/
theorem ae_funDim_relu_oneBlock_residual_eq_add
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ θ ∂μ, funDim (Arch.mlp relu id hid) 1 θ
      = funDim (Arch.mlp relu id hid) 0 θ + Fintype.card d ^ 2 := by
  -- `fd_1 + d² + d_hidden = P` with the skip, `fd_0 + 2 d² + d_hidden = P` without
  -- (Theorem 5.1 of the dimension paper)
  filter_upwards [ae_funDim_relu_oneBlock_residual μ hd hdIn hdOut hhid,
    ae_funDim_relu_oneBlock μ hd hdIn hdOut hhid] with θ h1 h2
  omega

/-- **Theorem 4.6 (i) for a ReLU² block, with a skip:** for `d_in, d_out, d_hidden ≥ d ≥ 2`, at
generic parameters, `fd = P - d² - d_hidden`. -/
theorem ae_funDim_reluSq_oneBlock_residual
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) reluSq id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ θ ∂μ, funDim (Arch.mlp reluSq id hid) 1 θ
        + (Fintype.card d ^ 2 + Fintype.card (hid 0))
      = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) reluSq id hid) dIn dOut) := by
  -- the conditions of the proof hold at generic parameters (`Mlp.lean`, for every `σ`)
  exact (ae_oneBlockGeneric μ hd hdIn hdOut hhid).mono fun θ hθ =>
    funDim_mlp_oneBlock_rescale_residual (fun z _ => hasDerivAt_reluSq z) reluSq_homogeneous
      (reluSq_unitsRescale dIn dOut (hid 0)) θ hθ

/-- Theorem 4.6 (i) for a ReLU² block with a skip, on the paper's inputs. -/
theorem ae_exists_jacobianRank_reluSq_oneBlock_residual
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) reluSq id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ θ ∂μ, ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i, X i ∈ noKink θ) ∧
      jacobianRank (Arch.mlp reluSq id hid) 1 X θ
          + (Fintype.card d ^ 2 + Fintype.card (hid 0))
        = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) reluSq id hid) dIn dOut) := by
  -- the conditions of the proof hold at generic parameters (`Mlp.lean`, for every `σ`)
  exact (ae_oneBlockGeneric μ hd hdIn hdOut hhid).mono fun θ hθ =>
    exists_jacobianRank_mlp_oneBlock_rescale_residual (fun z _ => hasDerivAt_reluSq z)
      reluSq_homogeneous (reluSq_unitsRescale dIn dOut (hid 0)) θ hθ

/-- **Theorem 4.6 (i) for a ReLU² block:** at generic parameters the skip raises the functional
dimension by exactly `d²`. -/
theorem ae_funDim_reluSq_oneBlock_residual_eq_add
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) reluSq id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ θ ∂μ, funDim (Arch.mlp reluSq id hid) 1 θ
      = funDim (Arch.mlp reluSq id hid) 0 θ + Fintype.card d ^ 2 := by
  -- `fd_1 + d² + d_hidden = P` with the skip, `fd_0 + 2 d² + d_hidden = P` without
  -- (Theorem 5.1 of the dimension paper)
  filter_upwards [ae_funDim_reluSq_oneBlock_residual μ hd hdIn hdOut hhid,
    ae_funDim_reluSq_oneBlock μ hd hdIn hdOut hhid] with θ h1 h2
  omega

end Skips
