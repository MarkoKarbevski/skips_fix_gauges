import SkipsLean.Dimension.RescalingGate
import SkipsLean.OneBlock.Gated
import SkipsLean.OneBlock.UnitsReGLU
import SkipsLean.OneBlock.Residual
import SkipsLean.Residual.UpperBoundSymmetries

/-!
# The one-block theorem for a ReGLU block, without and with a skip

Paper (dimension): Theorem 5.1 (Theorem C.1 in the appendix) for a ReGLU block: with one block,
without normalization and without biases, at generic parameters the functional dimension is
`P - 2 d² - s` with `s = 2 d_hidden`, one rescaling of the gate and one of the value for each
hidden unit.

Paper (skips): Theorem 4.6 (i) (Theorem B.1 (i) in the appendix) for a ReGLU block: "For generic
parameters the skipless network has functional dimension `P - 2 d² - s` and the residual network
`P - d² - s` … and the skip raises the functional dimension by exactly `d²`."

The network is `x ↦ f(x E W_read) W_write D`, or `x ↦ (x E + f(x E W_read) W_write) D` with the
skip, with `W_read = [W_g | W_v]` and `f(z, w)_i = max(z_i, 0) w_i`. With `C = E W_read` and
`A = W_write D`, hidden unit `i` has the gate column `c_i` (column `Sum.inl i` of `C`), the value
column `e_i` (column `Sum.inr i` of `C`) and the write row `a_i` (row `i` of `A`).

The conditions that the proof uses are those of the other gated blocks (`OneBlockGenericGated`)
and one more, which Lemma C.3 assumes for the gated blocks and uses only for ReGLU: no value
column `e_i` is proportional to the gate column `c_i` of the same hidden unit
(`OneBlockGenericReGLU`). Under them a direction that is flat at every input with no gate at its
kink is the sum of a direction of the changes of basis, a direction of the rescalings of the
values and a direction of the rescalings of the gates (`relu_gated_units_flat`, Lemma C.3 for
ReGLU).

As for ReLU blocks (`OneBlock/Rescale.lean`), two statements are made in each case: the value of
`funDim`, and a batch of inputs with no gate at its kink on which the Jacobian has that rank. The
skip does not change the arguments of the hidden units of the one block, so these inputs are the
same set `noKinkGate θ` with and without the skip.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {hid : Fin 1 → Type} [∀ ℓ, Fintype (hid ℓ)]
variable {σ : ℝ → ℝ}

/-- The conditions on the parameters of one ReGLU block that the proof of the one-block theorem
uses: those of the other gated blocks, and no value column `e_i` of `C = E W_read` is
proportional to the gate column `c_i` of the same hidden unit. They do not involve the gate
activation. -/
structure OneBlockGenericReGLU
    (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) : Prop where
  /-- the conditions of the other gated blocks -/
  gated : OneBlockGenericGated θ
  /-- no value column `e_i` of `C` is proportional to the gate column `c_i` of the same unit -/
  value_not_gate : ∀ (i : hid 0) (r : ℝ),
    (θ.E * θ.read 0)ᵀ (Sum.inr i) ≠ r • (θ.E * θ.read 0)ᵀ (Sum.inl i)

/-- The inputs at which no gate of the block sits at its kink: every entry of the gate columns of
`x E W_read` (one per token and hidden unit) is nonzero. -/
def noKinkGate (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) :
    Set (Matrix T dIn ℝ) :=
  {x | ∀ (t : T) (i : hid 0), (x * θ.E * θ.read 0) t (Sum.inl i) ≠ 0}

/-- The conditions of the proof hold at generic parameters, for `d_in, d_out, d_hidden ≥ d ≥ 2`:
each is the nonvanishing of polynomials in the weights that do not vanish identically. -/
theorem ae_oneBlockGenericReGLU
    (μ : Measure (Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ θ ∂μ, OneBlockGenericReGLU θ := by
  classical
  -- two distinct coordinates of `h` and two distinct input coordinates
  obtain ⟨k₁, k₂, hk⟩ := Fintype.exists_pair_of_one_lt_card (show 1 < Fintype.card d by omega)
  obtain ⟨a₁, a₂, ha⟩ := Fintype.exists_pair_of_one_lt_card (show 1 < Fintype.card dIn by omega)
  -- the value column `e_i` and the gate column `c_i` of one unit are not proportional: a `2 × 2`
  -- minor of the two columns does not vanish (as `gate_not_collinear` in `Gated.lean`)
  have h6 : ∀ᵐ θ ∂μ, ∀ i : hid 0,
      (θ.E * θ.read 0) a₁ (Sum.inr i) * (θ.E * θ.read 0) a₂ (Sum.inl i)
        - (θ.E * θ.read 0) a₁ (Sum.inl i) * (θ.E * θ.read 0) a₂ (Sum.inr i) ≠ 0 := by
    refine ae_all_iff.2 fun i => ?_
    obtain ⟨E₀, W₀, hEW⟩ := exists_minor_ne_zero (q := hid 0 ⊕ hid 0) (i := Sum.inr i)
      (j := Sum.inl i) ha hk Sum.inr_ne_inl
    let θ₀ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut :=
      ⟨E₀, fun ℓ => Fin.cases W₀ (fun l => l.elim0) ℓ, 0, 0⟩
    have hC : ∀ (a : dIn) (j : hid 0 ⊕ hid 0), AnalyticOnNhd ℝ
        (fun θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut =>
          (θ.E * θ.read 0) a j) Set.univ := fun a j =>
      analyticOnNhd_E_mul_read (A := Arch.gated (T := T) (d := d) σ id hid) (dOut := dOut) 0 a j
    have hg : AnalyticOnNhd ℝ
        (fun θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut =>
          (θ.E * θ.read 0) a₁ (Sum.inr i) * (θ.E * θ.read 0) a₂ (Sum.inl i)
            - (θ.E * θ.read 0) a₁ (Sum.inl i) * (θ.E * θ.read 0) a₂ (Sum.inr i)) Set.univ :=
      ((hC a₁ (Sum.inr i)).mul (hC a₂ (Sum.inl i))).sub
        ((hC a₁ (Sum.inl i)).mul (hC a₂ (Sum.inr i)))
    exact ae_ne_zero_of_analytic μ hg ⟨θ₀, hEW⟩
  -- the conditions of the other gated blocks hold at generic parameters (`Gated.lean`)
  filter_upwards [ae_oneBlockGenericGated μ hd hdIn hdOut hhid, h6] with θ hg h6
  refine ⟨hg, fun i r hr => h6 i ?_⟩
  -- if `e_i = r c_i`, the minor vanishes
  have e1 : (θ.E * θ.read 0) a₁ (Sum.inr i) = r * (θ.E * θ.read 0) a₁ (Sum.inl i) :=
    congrFun hr a₁
  have e2 : (θ.E * θ.read 0) a₂ (Sum.inr i) = r * (θ.E * θ.read 0) a₂ (Sum.inl i) :=
    congrFun hr a₂
  rw [e1, e2]
  ring

/-! ### Helpers: the function of one ReGLU block with a stream matrix `S`, and its derivative -/

/-- Helper: the read of the block, with its columns indexed by the gates and values. -/
private def rdQ (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) :
    Matrix d (hid 0 ⊕ hid 0) ℝ :=
  θ.read 0

/-- Helper: the write of the block, with its rows indexed by the hidden units. -/
private def wrQ (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) :
    Matrix (hid 0) d ℝ :=
  θ.write 0

/-- Helper: `C = E W_read`. -/
private def CmQ (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) :
    Matrix dIn (hid 0 ⊕ hid 0) ℝ :=
  θ.E * rdQ θ

/-- Helper: `A = W_write D`. -/
private def AmQ (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) :
    Matrix (hid 0) dOut ℝ :=
  wrQ θ * θ.D

/-- Helper: `M_S = E S_0 D`, the linear part of the network `x ↦ x M_S + f(x C) A` (`0` without
the skip, `E D` with it). -/
private def MmQ (S : Fin 1 → Matrix d d ℝ)
    (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) : Matrix dIn dOut ℝ :=
  θ.E * S 0 * θ.D

/-- Helper: the derivative `∂C = η_E W_read + E η_read` of `C` along `η`. -/
private def dCmQ (θ η : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) :
    Matrix dIn (hid 0 ⊕ hid 0) ℝ :=
  η.E * rdQ θ + θ.E * rdQ η

/-- Helper: the derivative `∂A = η_write D + W_write η_D` of `A` along `η`. -/
private def dAmQ (θ η : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) :
    Matrix (hid 0) dOut ℝ :=
  wrQ η * θ.D + wrQ θ * η.D

/-- Helper: the derivative `∂M_S = η_E S_0 D + E S_0 η_D` of `M_S` along `η`. -/
private def dMmQ (S : Fin 1 → Matrix d d ℝ)
    (θ η : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) : Matrix dIn dOut ℝ :=
  η.E * S 0 * θ.D + θ.E * S 0 * η.D

omit [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the read is linear in the parameters. -/
private theorem rdQ_line (θ η : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (τ : ℝ) : rdQ (θ + τ • η) = rdQ θ + τ • rdQ η := rfl

omit [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the write is linear in the parameters. -/
private theorem wrQ_line (θ η : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (τ : ℝ) : wrQ (θ + τ • η) = wrQ θ + τ • wrQ η := rfl

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dOut] in
/-- Helper: the function of one ReGLU block with the stream matrix `S`,
`F_θ(x) = x M_S + (σ(x C_g) ⊙ (x C_v)) A`. -/
private theorem eval_Q_eq (S : Fin 1 → Matrix d d ℝ)
    (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) (x : Matrix T dIn ℝ) :
    eval (Arch.gated σ id hid) S θ x
      = x * MmQ S θ + (Matrix.of fun t i => σ ((x * CmQ θ) t (Sum.inl i))
          * (x * CmQ θ) t (Sum.inr i)) * AmQ θ := by
  have h1 : (Fin.last 1 : Fin 2) = (0 : Fin 1).succ := rfl
  have hχ : (Arch.gated (T := T) (d := d) σ id hid).χ = id := rfl
  have hf : (Arch.gated (T := T) (d := d) σ id hid).f 0
      = fun M => Matrix.of fun t i => σ (M t (Sum.inl i)) * M t (Sum.inr i) := rfl
  -- `h_1 = h_0 S_0 + f(h_0 W_read) W_write` with `h_0 = x E`
  rw [eval, h1, hidden_succ, Fin.castSucc_zero, hidden_zero, hχ, hf]
  simp only [id_eq, Matrix.add_mul]
  rw [Matrix.mul_assoc x θ.E (θ.read 0),
    show x * θ.E * S 0 * θ.D = x * MmQ S θ by simp only [MmQ, Matrix.mul_assoc]]
  congr 1
  exact Matrix.mul_assoc _ _ _

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dOut] in
/-- Helper: the entries of `F_θ(x)`,
`(x M_S)_{t o} + ∑_i σ((x C)_{t, g i}) (x C)_{t, v i} A_{i o}`. -/
private theorem eval_Q_apply (S : Fin 1 → Matrix d d ℝ)
    (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (x : Matrix T dIn ℝ) (t : T) (o : dOut) :
    eval (Arch.gated σ id hid) S θ x t o
      = (x * MmQ S θ) t o + ∑ i : hid 0,
        σ ((x * CmQ θ) t (Sum.inl i)) * (x * CmQ θ) t (Sum.inr i) * AmQ θ i o := by
  rw [eval_Q_eq]
  rfl

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: along the line, `C(τ) = C + τ ∂C + τ² η_E η_read`. -/
private theorem CmQ_line (θ η : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (τ : ℝ) :
    CmQ (θ + τ • η) = CmQ θ + τ • dCmQ θ η + (τ * τ) • CmQ η := by
  simp only [CmQ, dCmQ, rdQ_line, Params.add_E, Params.smul_E, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_smul, Matrix.smul_mul, smul_add, smul_smul]
  abel

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: along the line, `A(τ) = A + τ ∂A + τ² η_write η_D`. -/
private theorem AmQ_line (θ η : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (τ : ℝ) :
    AmQ (θ + τ • η) = AmQ θ + τ • dAmQ θ η + (τ * τ) • AmQ η := by
  simp only [AmQ, dAmQ, wrQ_line, Params.add_D, Params.smul_D, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_smul, Matrix.smul_mul, smul_add, smul_smul]
  abel

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: along the line, `M_S(τ) = M_S + τ ∂M_S + τ² η_E S_0 η_D`. -/
private theorem MmQ_line (S : Fin 1 → Matrix d d ℝ)
    (θ η : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) (τ : ℝ) :
    MmQ S (θ + τ • η) = MmQ S θ + τ • dMmQ S θ η + (τ * τ) • MmQ S η := by
  simp only [MmQ, dMmQ, Params.add_E, Params.smul_E, Params.add_D, Params.smul_D, Matrix.mul_add,
    Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, smul_add, smul_smul]
  abel

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dOut] in
/-- Helper: the entries of `F_{θ + τ η}(x)` as functions of `τ`. -/
private theorem evalQ_line_apply (S : Fin 1 → Matrix d d ℝ)
    (θ η : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (x : Matrix T dIn ℝ) (t : T) (o : dOut) (τ : ℝ) :
    eval (Arch.gated σ id hid) S (θ + τ • η) x t o
      = ((x * MmQ S θ) t o + τ * (x * dMmQ S θ η) t o + τ * τ * (x * MmQ S η) t o)
        + ∑ i : hid 0,
          σ ((x * CmQ θ) t (Sum.inl i) + τ * (x * dCmQ θ η) t (Sum.inl i)
              + τ * τ * (x * CmQ η) t (Sum.inl i)) *
            ((x * CmQ θ) t (Sum.inr i) + τ * (x * dCmQ θ η) t (Sum.inr i)
              + τ * τ * (x * CmQ η) t (Sum.inr i)) *
            (AmQ θ i o + τ * dAmQ θ η i o + τ * τ * AmQ η i o) := by
  rw [eval_Q_apply, MmQ_line, CmQ_line, AmQ_line]
  simp only [Matrix.mul_add, Matrix.mul_smul]
  rfl

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dOut] in
/-- Helper: at an input of `noKinkGate θ`, every gate entry of `x C` is nonzero. -/
private theorem noKinkGate_apply
    {θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut}
    {x : Matrix T dIn ℝ} (hx : x ∈ noKinkGate θ) (t : T) (i : hid 0) :
    (x * CmQ θ) t (Sum.inl i) ≠ 0 := by
  have h := hx t i
  rwa [Matrix.mul_assoc] at h

/-- Helper: `θ ↦ E S_0`, a linear map of the parameters. -/
private def linES (S : Fin 1 → Matrix d d ℝ) :
    Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut →ₗ[ℝ] Matrix dIn d ℝ where
  toFun θ := θ.E * S 0
  map_add' θ η := by simp only [Params.add_E, Matrix.add_mul]
  map_smul' c θ := by simp only [Params.smul_E, Matrix.smul_mul, RingHom.id_apply]

/-- At an input with no gate at its kink, the output of a network of one ReGLU block is
differentiable in the parameters, for all stream matrices `S` (with or without the skip). -/
theorem differentiableAt_eval_of_mem_noKinkGate (S : Fin 1 → Matrix d d ℝ)
    (θ : Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut) (x : Matrix T dIn ℝ)
    (hx : x ∈ noKinkGate θ) :
    DifferentiableAt ℝ
      (fun θ' : Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut =>
        eval (Arch.gated relu id hid) S θ' x) θ := by
  -- the entries of `M_S = E S_0 D`, `C = E W_read` and `A = W_write D` are polynomials in the
  -- parameters
  have hM : ∀ (a : dIn) (o : dOut), DifferentiableAt ℝ
      (fun θ' : Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut => MmQ S θ' a o) θ :=
    fun a o => (analyticOnNhd_mul_apply
      (linES (T := T) (σ := relu) (hid := hid) (dIn := dIn) (dOut := dOut) S)
      (Params.linD (A := Arch.gated (T := T) (d := d) relu id hid) (dIn := dIn) (dOut := dOut))
      a o θ (Set.mem_univ _)).differentiableAt
  have hC : ∀ (a : dIn) (j : hid 0 ⊕ hid 0), DifferentiableAt ℝ
      (fun θ' : Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut => CmQ θ' a j) θ :=
    fun a j => (analyticOnNhd_E_mul_read (A := Arch.gated (T := T) (d := d) relu id hid)
      (dOut := dOut) 0 a j θ (Set.mem_univ _)).differentiableAt
  have hA : ∀ (i : hid 0) (o : dOut), DifferentiableAt ℝ
      (fun θ' : Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut => AmQ θ' i o) θ :=
    fun i o => (analyticOnNhd_write_mul_D (A := Arch.gated (T := T) (d := d) relu id hid)
      (dIn := dIn) 0 i o θ (Set.mem_univ _)).differentiableAt
  -- so are the entries of `x M_S` and of `x C`
  have hxM : ∀ (t : T) (o : dOut), DifferentiableAt ℝ
      (fun θ' : Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut =>
        (x * MmQ S θ') t o) θ := by
    intro t o
    simp only [Matrix.mul_apply]
    exact DifferentiableAt.fun_sum fun a _ => (hM a o).const_mul (x t a)
  have hxC : ∀ (t : T) (j : hid 0 ⊕ hid 0), DifferentiableAt ℝ
      (fun θ' : Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut =>
        (x * CmQ θ') t j) θ := by
    intro t j
    simp only [Matrix.mul_apply]
    exact DifferentiableAt.fun_sum fun a _ => (hC a j).const_mul (x t a)
  -- the entry `(t, o)` of `F_θ'(x)` is `(x M_S)_{t o} + ∑_i relu(z_i) w_i A_{i o}`, and `relu` is
  -- differentiable at every gate `z_i = (x C)_{t, g i}`, which is not `0`
  refine differentiableAt_pi.2 fun t => differentiableAt_pi.2 fun o => ?_
  simp only [eval_Q_apply]
  have hr : ∀ i : hid 0, DifferentiableAt ℝ
      (fun θ' : Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut =>
        relu ((x * CmQ θ') t (Sum.inl i))) θ := by
    intro i
    have hz : DifferentiableAt ℝ relu ((x * CmQ θ) t (Sum.inl i)) :=
      (hasDerivAt_relu (noKinkGate_apply hx t i)).differentiableAt
    -- named first: against the goal, `?g ∘ ?f` would be unified with `relu` unfolded
    have hc := hz.comp θ (hxC t (Sum.inl i))
    exact hc
  have hu : ∀ i : hid 0, DifferentiableAt ℝ
      (fun θ' : Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut =>
        relu ((x * CmQ θ') t (Sum.inl i)) * (x * CmQ θ') t (Sum.inr i) * AmQ θ' i o) θ :=
    fun i => ((hr i).mul (hxC t (Sum.inr i))).mul (hA i o)
  exact (hxM t o).add (DifferentiableAt.fun_sum fun i _ => hu i)

/-- Helper (Step 3 of the paper, the chain rule, at an input of `noKinkGate θ`): the derivative of
`θ ↦ F_θ(x)` along `η` has the entries `(x ∂M_S)_{t o} + ∑_i [relu(z_i) w_i (∂A)_{i o}
+ 1[z_i > 0] (x ∂C)_{t, g i} w_i A_{i o} + relu(z_i) (x ∂C)_{t, v i} A_{i o}]`, with
`z_i = (x C)_{t, g i}` and `w_i = (x C)_{t, v i}`. -/
private theorem fderiv_eval_Q_apply_of_mem (S : Fin 1 → Matrix d d ℝ)
    (θ η : Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut)
    (x : Matrix T dIn ℝ) (hx : x ∈ noKinkGate θ) (t : T) (o : dOut) :
    fderiv ℝ (fun θ' => eval (Arch.gated relu id hid) S θ' x) θ η t o
      = (x * dMmQ S θ η) t o + ∑ i : hid 0,
        (relu ((x * CmQ θ) t (Sum.inl i)) * (x * CmQ θ) t (Sum.inr i) * dAmQ θ η i o
          + reluDeriv ((x * CmQ θ) t (Sum.inl i)) * (x * dCmQ θ η) t (Sum.inl i)
              * (x * CmQ θ) t (Sum.inr i) * AmQ θ i o
          + relu ((x * CmQ θ) t (Sum.inl i)) * (x * dCmQ θ η) t (Sum.inr i) * AmQ θ i o) := by
  -- the chain rule along the line `τ ↦ θ + τ η`
  have h1 := hasDerivAt_eval_line (A := Arch.gated (T := T) (d := d) relu id hid) S θ η x
    (differentiableAt_eval_of_mem_noKinkGate S θ x hx)
  have h2 := hasDerivAt_pi.1 (hasDerivAt_pi.1 h1 t) o
  -- the same derivative computed entrywise: a polynomial in `τ`, plus products and sums of real
  -- functions of `τ`
  have h3 : HasDerivAt (fun τ : ℝ => eval (Arch.gated relu id hid) S (θ + τ • η) x t o)
      ((x * dMmQ S θ η) t o + ∑ i : hid 0,
        (relu ((x * CmQ θ) t (Sum.inl i)) * (x * CmQ θ) t (Sum.inr i) * dAmQ θ η i o
          + reluDeriv ((x * CmQ θ) t (Sum.inl i)) * (x * dCmQ θ η) t (Sum.inl i)
              * (x * CmQ θ) t (Sum.inr i) * AmQ θ i o
          + relu ((x * CmQ θ) t (Sum.inl i)) * (x * dCmQ θ η) t (Sum.inr i) * AmQ θ i o)) 0 := by
    rw [funext fun τ => evalQ_line_apply S θ η x t o τ]
    refine (hasDerivAt_quad _ _ _).add (HasDerivAt.fun_sum fun i _ => ?_)
    have hu := hasDerivAt_quad ((x * CmQ θ) t (Sum.inl i)) ((x * dCmQ θ η) t (Sum.inl i))
      ((x * CmQ η) t (Sum.inl i))
    have hw := hasDerivAt_quad ((x * CmQ θ) t (Sum.inr i)) ((x * dCmQ θ η) t (Sum.inr i))
      ((x * CmQ η) t (Sum.inr i))
    have hv := hasDerivAt_quad (AmQ θ i o) (dAmQ θ η i o) (AmQ η i o)
    -- `relu` is differentiable at the gate `(x C)_{t, g i}`, which is not `0`
    have h := (((hasDerivAt_relu (noKinkGate_apply hx t i)).comp_of_eq (0 : ℝ) hu
      (by simp only [zero_mul, add_zero])).mul hw).mul hv
    convert h using 1
    · rfl
    · simp only [Pi.mul_apply, Function.comp_apply, zero_mul, mul_zero, add_zero]
      ring
  exact h2.unique h3

/-! ### Helpers: the derivative of `C` and `A` along the two rescalings -/

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: `∂C` is linear in the direction. -/
private theorem dCmQ_sub (θ η ρ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) :
    dCmQ θ (η - ρ) = dCmQ θ η - dCmQ θ ρ := by
  show (η.E - ρ.E) * rdQ θ + θ.E * (rdQ η - rdQ ρ)
    = (η.E * rdQ θ + θ.E * rdQ η) - (ρ.E * rdQ θ + θ.E * rdQ ρ)
  rw [Matrix.sub_mul, Matrix.mul_sub]
  abel

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: `∂A` is linear in the direction. -/
private theorem dAmQ_sub (θ η ρ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) :
    dAmQ θ (η - ρ) = dAmQ θ η - dAmQ θ ρ := by
  show (wrQ η - wrQ ρ) * θ.D + wrQ θ * (η.D - ρ.D)
    = (wrQ η * θ.D + wrQ θ * η.D) - (wrQ ρ * θ.D + wrQ θ * ρ.D)
  rw [Matrix.sub_mul, Matrix.mul_sub]
  abel

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: along a rescaling of the values, the gate columns of `C` do not move. -/
private theorem dCmQ_value_inl
    (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) (α : ∀ ℓ, hid ℓ → ℝ)
    (a : dIn) (i : hid 0) :
    dCmQ θ (rescaleDir θ α) a (Sum.inl i) = 0 := by
  show ((0 : Matrix dIn d ℝ) * rdQ θ + θ.E * rdQ (rescaleDir θ α)) a (Sum.inl i) = 0
  rw [Matrix.zero_mul, zero_add, Matrix.mul_apply]
  exact Finset.sum_eq_zero fun k _ => mul_eq_zero_of_right _ rfl

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: along a rescaling of the values, the value column `e_i` of `C` moves by
`-α_i e_i`. -/
private theorem dCmQ_value_inr
    (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) (α : ∀ ℓ, hid ℓ → ℝ)
    (a : dIn) (i : hid 0) :
    dCmQ θ (rescaleDir θ α) a (Sum.inr i) = -(α 0 i) * CmQ θ a (Sum.inr i) := by
  show ((0 : Matrix dIn d ℝ) * rdQ θ + θ.E * rdQ (rescaleDir θ α)) a (Sum.inr i)
    = -(α 0 i) * (θ.E * rdQ θ) a (Sum.inr i)
  rw [Matrix.zero_mul, zero_add, Matrix.mul_apply, Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  show θ.E a k * (-(α 0 i) * θ.read 0 k (Sum.inr i))
    = -(α 0 i) * (θ.E a k * θ.read 0 k (Sum.inr i))
  ring

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: along a rescaling of the values, the row `a_i` of `A` moves by `α_i a_i`. -/
private theorem dAmQ_value
    (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) (α : ∀ ℓ, hid ℓ → ℝ)
    (i : hid 0) (o : dOut) :
    dAmQ θ (rescaleDir θ α) i o = α 0 i * AmQ θ i o := by
  show (wrQ (rescaleDir θ α) * θ.D + wrQ θ * (0 : Matrix d dOut ℝ)) i o
    = α 0 i * (wrQ θ * θ.D) i o
  rw [Matrix.mul_zero, add_zero, Matrix.mul_apply, Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  show α 0 i * θ.write 0 i k * θ.D k o = α 0 i * (θ.write 0 i k * θ.D k o)
  ring

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: along a rescaling of the gates, the gate column `c_i` of `C` moves by `β_i c_i`. -/
private theorem dCmQ_gate_inl (k : ℕ)
    (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) (β : ∀ ℓ, hid ℓ → ℝ)
    (a : dIn) (i : hid 0) :
    dCmQ θ (rescaleDirGate k θ β) a (Sum.inl i) = β 0 i * CmQ θ a (Sum.inl i) := by
  show ((0 : Matrix dIn d ℝ) * rdQ θ + θ.E * rdQ (rescaleDirGate k θ β)) a (Sum.inl i)
    = β 0 i * (θ.E * rdQ θ) a (Sum.inl i)
  rw [Matrix.zero_mul, zero_add, Matrix.mul_apply, Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  show θ.E a j * (β 0 i * θ.read 0 j (Sum.inl i))
    = β 0 i * (θ.E a j * θ.read 0 j (Sum.inl i))
  ring

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: along a rescaling of the gates, the value columns of `C` do not move. -/
private theorem dCmQ_gate_inr (k : ℕ)
    (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) (β : ∀ ℓ, hid ℓ → ℝ)
    (a : dIn) (i : hid 0) :
    dCmQ θ (rescaleDirGate k θ β) a (Sum.inr i) = 0 := by
  show ((0 : Matrix dIn d ℝ) * rdQ θ + θ.E * rdQ (rescaleDirGate k θ β)) a (Sum.inr i) = 0
  rw [Matrix.zero_mul, zero_add, Matrix.mul_apply]
  exact Finset.sum_eq_zero fun j _ => mul_eq_zero_of_right _ rfl

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: along a rescaling of the gates (`k = 1`), the row `a_i` of `A` moves by
`-β_i a_i`. -/
private theorem dAmQ_gate
    (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) (β : ∀ ℓ, hid ℓ → ℝ)
    (i : hid 0) (o : dOut) :
    dAmQ θ (rescaleDirGate 1 θ β) i o = -(β 0 i) * AmQ θ i o := by
  show (wrQ (rescaleDirGate 1 θ β) * θ.D + wrQ θ * (0 : Matrix d dOut ℝ)) i o
    = -(β 0 i) * (wrQ θ * θ.D) i o
  rw [Matrix.mul_zero, add_zero, Matrix.mul_apply, Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  show -(((1 : ℕ) : ℝ) * β 0 i) * θ.write 0 i j * θ.D j o
    = -(β 0 i) * (θ.write 0 i j * θ.D j o)
  rw [Nat.cast_one]
  ring

/-- Helper (Steps 2 and 3 of the proof, for all stream matrices `S`): under the conditions, a
direction `η` that is flat at every input of `noKinkGate θ` keeps `M_S` to first order, and after
the removal of a rescaling of the values and one of the gates it keeps `C` and `A` to first order,
so it is the direction of two changes of basis (Lemma C.2). -/
private theorem flatOn_noKinkGate_aux (S : Fin 1 → Matrix d d ℝ)
    (θ : Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut)
    (hθ : OneBlockGenericReGLU θ)
    (η : Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut)
    (hη : η ∈ flatOn (Arch.gated relu id hid) S θ (noKinkGate θ)) :
    dMmQ S θ η = 0 ∧ ∃ (X : Fin 2 → Matrix d d ℝ) (α β : ∀ ℓ, hid ℓ → ℝ),
      η - rescaleDir θ α - rescaleDirGate 1 θ β = cobDir θ X := by
  -- Step 3: at every input with no gate at its kink, the derivative of `F(θ, x)` along `η`
  -- vanishes, entry by entry
  have hzero : ∀ x ∈ noKinkGate θ, ∀ (t : T) (o : dOut), (x * dMmQ S θ η) t o + ∑ i : hid 0,
      (relu ((x * CmQ θ) t (Sum.inl i)) * (x * CmQ θ) t (Sum.inr i) * dAmQ θ η i o
        + reluDeriv ((x * CmQ θ) t (Sum.inl i)) * (x * dCmQ θ η) t (Sum.inl i)
            * (x * CmQ θ) t (Sum.inr i) * AmQ θ i o
        + relu ((x * CmQ θ) t (Sum.inl i)) * (x * dCmQ θ η) t (Sum.inr i) * AmQ θ i o) = 0 := by
    intro x hx t o
    rw [← fderiv_eval_Q_apply_of_mem S θ η x hx t o]
    have h := LinearMap.mem_ker.1 ((Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hη x) hx)
    exact congrFun (congrFun h t) o
  -- Step 2, Lemma C.3 for ReGLU with the linear term `x ∂M_S` (inputs `x` with all rows equal to
  -- a `v` with `v c_i ≠ 0` for all `i`): `∂M_S = 0`, `∂c_i = λ_i c_i`, `∂e_i = -α_i e_i` and
  -- `∂a_i = (α_i - λ_i) a_i`
  obtain ⟨hm, -, lam, α, hlam⟩ := relu_gated_units_flat
    (fun i => (CmQ θ)ᵀ (Sum.inl i)) 0 (fun i => (CmQ θ)ᵀ (Sum.inr i)) 0 (fun i => AmQ θ i)
    (dMmQ S θ η) 0 (fun i => (dCmQ θ η)ᵀ (Sum.inl i)) 0 (fun i => (dCmQ θ η)ᵀ (Sum.inr i)) 0
    (fun i => dAmQ θ η i) (fun i => hθ.gated.row_ne_zero i) (fun i => hθ.gated.gate_ne_zero i)
    (fun i j hij => hθ.gated.gate_not_collinear i j hij) (fun i => hθ.gated.value_ne_zero i)
    (fun i r h => hθ.value_not_gate i r (by have h1 := congrArg Prod.fst h; exact h1)) (by
      intro v hv
      have hx : (Matrix.of fun _ : T => v) ∈ noKinkGate θ := by
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
  refine ⟨hm, ?_⟩
  -- the rescalings with these `α_i` and `λ_i` (one block: `ℓ = 0`)
  obtain ⟨α', hα'⟩ : ∃ α' : ∀ ℓ : Fin 1, hid ℓ → ℝ, α' 0 = α :=
    ⟨fun ℓ => Fin.cases α (fun l => l.elim0) ℓ, rfl⟩
  obtain ⟨β', hβ'⟩ : ∃ β' : ∀ ℓ : Fin 1, hid ℓ → ℝ, β' 0 = lam :=
    ⟨fun ℓ => Fin.cases lam (fun l => l.elim0) ℓ, rfl⟩
  -- `η - rescaleDir θ α' - rescaleDirGate 1 θ β'` keeps `C` and `A` to first order
  have hC : dCmQ θ (η - rescaleDir θ α' - rescaleDirGate 1 θ β') = 0 := by
    ext a j
    rcases j with i | i
    · rw [dCmQ_sub, dCmQ_sub, Matrix.sub_apply, Matrix.sub_apply, dCmQ_value_inl, dCmQ_gate_inl,
        sub_zero, Matrix.zero_apply, sub_eq_zero, hβ']
      exact congrFun (hlam i).1 a
    · rw [dCmQ_sub, dCmQ_sub, Matrix.sub_apply, Matrix.sub_apply, dCmQ_value_inr, dCmQ_gate_inr,
        sub_zero, Matrix.zero_apply, sub_eq_zero, hα']
      exact congrFun (hlam i).2.2.1 a
  have hA : dAmQ θ (η - rescaleDir θ α' - rescaleDirGate 1 θ β') = 0 := by
    ext i o
    rw [dAmQ_sub, dAmQ_sub, Matrix.sub_apply, Matrix.sub_apply, dAmQ_value, dAmQ_gate,
      Matrix.zero_apply, hα', hβ']
    have h : dAmQ θ η i o = (α i - lam i) * AmQ θ i o := congrFun (hlam i).2.2.2.2 o
    rw [h]
    ring
  -- Step 1, Lemma C.2: a direction that keeps `C` and `A` is that of two changes of basis
  obtain ⟨X, hX⟩ := (keeps_products_iff_mem_range_cobDir θ
    (η - rescaleDir θ α' - rescaleDirGate 1 θ β') hθ.gated.rank_E hθ.gated.rank_D
    hθ.gated.rank_read hθ.gated.rank_write).1 ⟨hC, hA⟩
  exact ⟨X, α', β', hX⟩

/-! ### Helpers: the space of the directions of the changes of basis and of the rescalings -/

/-- Helper (as `rescaleDirLin` of `Gated.lean`): `α ↦ rescaleDir θ α` is linear. -/
private noncomputable def rescaleDirLinQ
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

/-- Helper (as `rescaleDirGateLin` of `Dimension/RescalingGate.lean`): `β ↦ rescaleDirGate k θ β`
is linear. -/
private noncomputable def rescaleDirGateLinQ (k : ℕ)
    (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) :
    (∀ ℓ : Fin 1, hid ℓ → ℝ) →ₗ[ℝ] Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut where
  toFun := rescaleDirGate k θ
  map_add' α β := by
    apply Params.ext'
    · exact (add_zero 0).symm
    · intro ℓ
      ext a j
      rcases j with i | i
      · show (α + β) ℓ i * θ.read ℓ a (Sum.inl i)
          = α ℓ i * θ.read ℓ a (Sum.inl i) + β ℓ i * θ.read ℓ a (Sum.inl i)
        rw [Pi.add_apply, Pi.add_apply]
        ring
      · exact (add_zero 0).symm
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
      ext a j
      rcases j with i | i
      · show (c • α) ℓ i * θ.read ℓ a (Sum.inl i) = c * (α ℓ i * θ.read ℓ a (Sum.inl i))
        rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul]
        ring
      · exact (smul_zero c).symm
    · intro ℓ
      ext i a
      show -((k : ℝ) * (c • α) ℓ i) * θ.write ℓ i a = c * (-((k : ℝ) * α ℓ i) * θ.write ℓ i a)
      rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul]
      ring
    · exact (smul_zero c).symm

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] in
/-- Helper: under the conditions of the gated blocks, no value column of `W_read` vanishes, since
the value columns of `C = E W_read` do not. -/
private theorem read_value_ne_zero_Q
    (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (hθ : OneBlockGenericGated θ) : ∀ ℓ i, (fun a => θ.read ℓ a (Sum.inr i)) ≠ 0 := by
  intro ℓ i h0
  obtain rfl := Subsingleton.elim ℓ 0
  apply hθ.value_ne_zero i
  funext a
  show ∑ k, θ.E a k * θ.read 0 k (Sum.inr i) = 0
  exact Finset.sum_eq_zero fun k _ => by
    rw [show θ.read 0 k (Sum.inr i) = 0 from congrFun h0 k, mul_zero]

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] in
/-- Helper: likewise no gate column of `W_read` vanishes. -/
private theorem read_gate_ne_zero_Q
    (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (hθ : OneBlockGenericGated θ) : ∀ ℓ i, (fun a => θ.read ℓ a (Sum.inl i)) ≠ 0 := by
  intro ℓ i h0
  obtain rfl := Subsingleton.elim ℓ 0
  apply hθ.gate_ne_zero i
  funext a
  show ∑ k, θ.E a k * θ.read 0 k (Sum.inl i) = 0
  exact Finset.sum_eq_zero fun k _ => by
    rw [show θ.read 0 k (Sum.inl i) = 0 from congrFun h0 k, mul_zero]

/-! ### Without a skip: Theorem 5.1 of the dimension paper for a ReGLU block -/

/-- **Steps 1 to 3 of the proof of Theorem 5.1 for a ReGLU block.** Under the conditions
`OneBlockGenericReGLU`, a direction that is flat at every input with no gate at its kink is the
sum of a direction of the changes of basis at the two hidden states, a direction of the
rescalings of the values and a direction of the rescalings of the gates. -/
theorem flatOn_noKinkGate_le_reglu
    (θ : Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut)
    (hθ : OneBlockGenericReGLU θ)
    (η : Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut)
    (hη : η ∈ flatOn (Arch.gated relu id hid) 0 θ (noKinkGate θ)) :
    ∃ (X : Fin 2 → Matrix d d ℝ) (α β : ∀ ℓ, hid ℓ → ℝ),
      η = cobDir θ X + rescaleDir θ α + rescaleDirGate 1 θ β := by
  -- Steps 2 and 3 with the stream matrix `0`, then Lemma C.2
  obtain ⟨-, X, α, β, hX⟩ := flatOn_noKinkGate_aux 0 θ hθ η hη
  exact ⟨X, α, β, by rw [← hX]; abel⟩

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the directions of the changes of basis and of the two rescalings,
`(X, α, β) ↦ cobDir θ X + rescaleDir θ α + rescaleDirGate 1 θ β`, as a linear map. -/
private noncomputable def dirQ
    (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) :
    ((Fin (1 + 1) → Matrix d d ℝ) × (∀ ℓ : Fin 1, hid ℓ → ℝ) × (∀ ℓ : Fin 1, hid ℓ → ℝ)) →ₗ[ℝ]
      Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut :=
  (cobDirLin θ).coprod ((rescaleDirLinQ θ).coprod (rescaleDirGateLinQ 1 θ))

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the values of `dirQ`. -/
private theorem dirQ_apply (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (p : (Fin (1 + 1) → Matrix d d ℝ) × (∀ ℓ : Fin 1, hid ℓ → ℝ) × (∀ ℓ : Fin 1, hid ℓ → ℝ)) :
    dirQ θ p = cobDir θ p.1 + (rescaleDir θ p.2.1 + rescaleDirGate 1 θ p.2.2) := rfl

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the triples `(X, α, β)` of two `d × d` matrices and two numbers per hidden unit form a
space of dimension `2 d² + 2 d_hidden`. -/
private theorem finrank_dirDomainQ :
    Module.finrank ℝ
        ((Fin (1 + 1) → Matrix d d ℝ) × (∀ ℓ : Fin 1, hid ℓ → ℝ) × (∀ ℓ : Fin 1, hid ℓ → ℝ))
      = 2 * Fintype.card d ^ 2 + 2 * Fintype.card (hid 0) := by
  rw [Module.finrank_prod, Module.finrank_prod, finrank_cobDomain (L := 1) (d := d),
    Module.finrank_pi_fintype]
  simp only [Module.finrank_fintype_fun_eq_card, Finset.univ_unique, Fin.default_eq_zero,
    Finset.sum_singleton]
  ring

omit [Nonempty T] in
/-- Helper: the directions `cobDir θ X + rescaleDir θ α + rescaleDirGate 1 θ β` are flat (changes
of basis and both rescalings are symmetries; no differentiability of `relu` is used). -/
private theorem range_dirQ_le_flat
    (θ : Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut) :
    LinearMap.range (dirQ θ) ≤ flat (Arch.gated relu id hid) 0 θ := by
  rintro _ ⟨p, rfl⟩
  rw [dirQ_apply]
  exact add_mem (cobDir_mem_flat_skipless' θ rfl p.1)
    (add_mem (rescaleDir_mem_flat' θ 0 p.2.1) (rescaleDirGate_mem_flat relu_homogeneous θ 0 p.2.2))

/-- Helper: the directions that are flat at every input of `noKinkGate θ` are among the directions
`cobDir θ X + rescaleDir θ α + rescaleDirGate 1 θ β` (the previous theorem). -/
private theorem flatOn_le_range_dirQ
    (θ : Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut)
    (hθ : OneBlockGenericReGLU θ) :
    flatOn (Arch.gated relu id hid) 0 θ (noKinkGate θ) ≤ LinearMap.range (dirQ θ) := by
  intro η hη
  obtain ⟨X, α, β, rfl⟩ := flatOn_noKinkGate_le_reglu θ hθ η hη
  refine LinearMap.mem_range.2 ⟨(X, α, β), ?_⟩
  rw [dirQ_apply]
  exact (add_assoc _ _ _).symm

omit [Nonempty T] in
/-- Helper (Lemma B.1 for ReGLU blocks): under the conditions, the directions
`cobDir θ X + rescaleDir θ α + rescaleDirGate 1 θ β` form a space of dimension
`2 d² + 2 d_hidden`. -/
private theorem finrank_range_dirQ
    (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (hθ : OneBlockGenericGated θ) :
    Module.finrank ℝ (LinearMap.range (dirQ θ))
      = 2 * Fintype.card d ^ 2 + 2 * Fintype.card (hid 0) := by
  -- `(X, α, β) ↦ cobDir θ X + rescaleDir θ α + rescaleDirGate 1 θ β` is injective
  have hinj0 := cobDir_add_rescaleDir_add_rescaleDirGate_injective 1 θ hθ.rank_E
    (fun ℓ => by obtain rfl := Subsingleton.elim ℓ 0; exact hθ.rank_write)
    (read_value_ne_zero_Q θ hθ) (read_gate_ne_zero_Q θ hθ)
  have hinj : Function.Injective (dirQ θ) := by
    intro p q hpq
    rw [dirQ_apply, dirQ_apply, ← add_assoc, ← add_assoc] at hpq
    exact hinj0 hpq
  rw [LinearMap.finrank_range_of_inj hinj, finrank_dirDomainQ]

/-- **Theorem 5.1 / C.1 for a ReGLU block, under the conditions of the proof:**
`fd = P - 2 d² - 2 d_hidden`. -/
theorem funDim_reglu_oneBlock
    (θ : Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut)
    (hθ : OneBlockGenericReGLU θ) :
    funDim (Arch.gated relu id hid) 0 θ
        + (2 * Fintype.card d ^ 2 + 2 * Fintype.card (hid 0))
      = Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut) := by
  -- the sandwich: the directions `cobDir + rescaleDir + rescaleDirGate` ≤ `K(θ)` ≤ the directions
  -- flat on `noKinkGate θ` ≤ the directions `cobDir + rescaleDir + rescaleDirGate`
  have hflat : flat (Arch.gated relu id hid) 0 θ = LinearMap.range (dirQ θ) :=
    le_antisymm ((flat_le_flatOn θ (noKinkGate θ)).trans (flatOn_le_range_dirQ θ hθ))
      (range_dirQ_le_flat θ)
  -- `fd(θ) = P - dim K(θ)` (Appendix C), and `dim K(θ) = 2 d² + 2 d_hidden`
  have h := funDim_add_finrank_flat' (S := 0) θ
  rwa [hflat, finrank_range_dirQ θ hθ.gated] at h

/-- The same rank on a batch of inputs with no gate at its kink, as the paper takes the Jacobian
for ReGLU blocks. -/
theorem exists_jacobianRank_reglu_oneBlock
    (θ : Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut)
    (hθ : OneBlockGenericReGLU θ) :
    ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i, X i ∈ noKinkGate θ) ∧
      jacobianRank (Arch.gated relu id hid) 0 X θ
          + (2 * Fintype.card d ^ 2 + 2 * Fintype.card (hid 0))
        = Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut) := by
  -- a batch of inputs of `noKinkGate θ`, where the network is differentiable in `θ`, with the
  -- rank `P - dim K_U(θ)`, `U = noKinkGate θ`
  obtain ⟨n, X, hX, h⟩ := exists_jacobianRank_add_finrank_flatOn (S := 0) θ (noKinkGate θ)
    (fun x hx => differentiableAt_eval_of_mem_noKinkGate 0 θ x hx)
  -- the same sandwich: `K_U(θ)` is the space of the directions
  -- `cobDir θ X + rescaleDir θ α + rescaleDirGate 1 θ β`
  have hflatOn : flatOn (Arch.gated relu id hid) 0 θ (noKinkGate θ)
      = LinearMap.range (dirQ θ) :=
    le_antisymm (flatOn_le_range_dirQ θ hθ)
      ((range_dirQ_le_flat θ).trans (flat_le_flatOn θ (noKinkGate θ)))
  refine ⟨n, X, hX, ?_⟩
  rwa [hflatOn, finrank_range_dirQ θ hθ.gated] at h

/-- **Theorem 5.1 / C.1 for a ReGLU block:** for `d_in, d_out, d_hidden ≥ d ≥ 2`, at generic
parameters, `fd = P - 2 d² - 2 d_hidden`. -/
theorem ae_funDim_reglu_oneBlock
    (μ : Measure (Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ θ ∂μ, funDim (Arch.gated relu id hid) 0 θ
        + (2 * Fintype.card d ^ 2 + 2 * Fintype.card (hid 0))
      = Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut) := by
  -- the conditions of the proof hold at generic parameters
  exact (ae_oneBlockGenericReGLU μ hd hdIn hdOut hhid).mono fun θ hθ =>
    funDim_reglu_oneBlock θ hθ

/-- **Theorem 5.1 / C.1 for a ReGLU block, on the paper's inputs:** at generic parameters the
Jacobian has the rank `P - 2 d² - 2 d_hidden` on a batch of inputs with no gate at its kink. -/
theorem ae_exists_jacobianRank_reglu_oneBlock
    (μ : Measure (Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ θ ∂μ, ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i, X i ∈ noKinkGate θ) ∧
      jacobianRank (Arch.gated relu id hid) 0 X θ
          + (2 * Fintype.card d ^ 2 + 2 * Fintype.card (hid 0))
        = Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut) := by
  -- the conditions of the proof hold at generic parameters
  exact (ae_oneBlockGenericReGLU μ hd hdIn hdOut hhid).mono fun θ hθ =>
    exists_jacobianRank_reglu_oneBlock θ hθ

/-! ### Helpers: linear algebra, and Lemma B.2 of the skips paper (as in `Residual.lean`) -/

/-- Helper (copy of `cancel_left_of_rank_res` of `Residual.lean`): a matrix whose rank is its
number of columns cancels on the left, via a left inverse. -/
private theorem cancel_left_of_rank_Q {m n k : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (M : Matrix m n ℝ) (hM : M.rank = Fintype.card n) {X Y : Matrix n k ℝ}
    (h : M * X = M * Y) : X = Y := by
  obtain ⟨B, hB⟩ := Matrix.vecMul_surjective_iff_exists_left_inverse.mp
    (Matrix.vecMul_surjective_iff_rank_eq_card.mpr hM)
  have := congrArg (B * ·) h
  simpa only [← Matrix.mul_assoc, hB, Matrix.one_mul] using this

/-- Helper (copy of `cancel_right_of_rank_res`): a matrix whose rank is its number of rows cancels
on the right, via a right inverse. -/
private theorem cancel_right_of_rank_Q {m n k : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    (M : Matrix m n ℝ) (hM : M.rank = Fintype.card m) {X Y : Matrix k m ℝ}
    (h : X * M = Y * M) : X = Y := by
  obtain ⟨R, hR⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.mp
    (Matrix.mulVec_surjective_iff_rank_eq_card.mpr hM)
  have := congrArg (· * R) h
  simpa only [Matrix.mul_assoc, hR, Matrix.mul_one] using this

omit [Fintype T] [Nonempty T] in
/-- Helper (Lemma B.2 of the skips paper, as `eq_const_of_keeps_ED` of `Residual.lean`): if `E`
and `D` have rank `d`, the direction of the two changes of basis `X_0` at `h_0` and `X_1` at `h_1`
keeps `M = E D` to first order only if `X_0 = X_1`, since `∂M = E X_0 D - E X_1 D`. -/
private theorem eq_const_of_keeps_ED_Q
    (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (X : Fin 2 → Matrix d d ℝ) (hE : θ.E.rank = Fintype.card d)
    (hD : θ.D.rank = Fintype.card d)
    (hM : (cobDir θ X).E * θ.D + θ.E * (cobDir θ X).D = 0) :
    X = fun _ => X 0 := by
  -- `∂M = E X_0 D - E X_1 D = 0`
  have h1 : θ.E * (X 0 * θ.D) = θ.E * (X 1 * θ.D) := by
    have h : θ.E * X 0 * θ.D + θ.E * -(X 1 * θ.D) = 0 := hM
    rw [Matrix.mul_neg, Matrix.mul_assoc, add_neg_eq_zero] at h
    exact h
  -- cancel `E` on the left and `D` on the right
  have h01 : X 0 = X 1 :=
    cancel_right_of_rank_Q θ.D hD (cancel_left_of_rank_Q θ.E hE h1)
  exact funext (Fin.forall_fin_two.2 ⟨rfl, h01.symm⟩)

/-! ### With a skip: Theorem 4.6 (i) of the skips paper for a ReGLU block -/

/-- **Steps 1 to 3 of the proof of Theorem B.1 (i) for a ReGLU block.** Under the conditions
`OneBlockGenericReGLU`, a direction that is flat for the residual network at every input with no
gate at its kink is the sum of the direction of one change of basis, the same at both hidden
states, a direction of the rescalings of the values and a direction of the rescalings of the
gates. -/
theorem flatOn_noKinkGate_le_reglu_residual
    (θ : Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut)
    (hθ : OneBlockGenericReGLU θ)
    (η : Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut)
    (hη : η ∈ flatOn (Arch.gated relu id hid) 1 θ (noKinkGate θ)) :
    ∃ (X : Matrix d d ℝ) (α β : ∀ ℓ, hid ℓ → ℝ),
      η = cobDir θ (fun _ => X) + rescaleDir θ α + rescaleDirGate 1 θ β := by
  -- Steps 2 and 3 with the stream matrix `1`: `η` keeps `M = E D`, and up to the two rescalings
  -- it is the direction of two changes of basis `X_0`, `X_1`
  obtain ⟨hm, X, α, β, hX⟩ := flatOn_noKinkGate_aux 1 θ hθ η hη
  -- the rescalings leave `E` and `D` alone, so `cobDir θ X` keeps `M = E D` as `η` does
  have hM : (cobDir θ X).E * θ.D + θ.E * (cobDir θ X).D = 0 := by
    rw [← hX]
    show (η.E - 0 - 0) * θ.D + θ.E * (η.D - 0 - 0) = 0
    rw [sub_zero, sub_zero, sub_zero, sub_zero]
    simpa only [dMmQ, Pi.one_apply, Matrix.mul_one] using hm
  -- Lemma B.2 of the skips paper: then `X_0 = X_1`
  have hXc := eq_const_of_keeps_ED_Q θ X hθ.gated.rank_E hθ.gated.rank_D hM
  have h1 : η = cobDir θ X + rescaleDir θ α + rescaleDirGate 1 θ β := by
    rw [← hX]
    abel
  exact ⟨X 0, α, β, h1.trans
    (congrArg (fun Y => cobDir θ Y + rescaleDir θ α + rescaleDirGate 1 θ β) hXc)⟩

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the directions of one change of basis and of the two rescalings,
`(X, α, β) ↦ cobDir θ (X, X) + rescaleDir θ α + rescaleDirGate 1 θ β`, as a linear map. -/
private noncomputable def dirQR
    (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) :
    (Matrix d d ℝ × (∀ ℓ : Fin 1, hid ℓ → ℝ) × (∀ ℓ : Fin 1, hid ℓ → ℝ)) →ₗ[ℝ]
      Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut :=
  ((cobDirLin θ).comp (LinearMap.pi fun _ => LinearMap.id)).coprod
    ((rescaleDirLinQ θ).coprod (rescaleDirGateLinQ 1 θ))

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the values of `dirQR`. -/
private theorem dirQR_apply (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (p : Matrix d d ℝ × (∀ ℓ : Fin 1, hid ℓ → ℝ) × (∀ ℓ : Fin 1, hid ℓ → ℝ)) :
    dirQR θ p = cobDir θ (fun _ => p.1) + (rescaleDir θ p.2.1 + rescaleDirGate 1 θ p.2.2) := rfl

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the triples `(X, α, β)` of one `d × d` matrix and two numbers per hidden unit form a
space of dimension `d² + 2 d_hidden`. -/
private theorem finrank_dirDomainQR :
    Module.finrank ℝ (Matrix d d ℝ × (∀ ℓ : Fin 1, hid ℓ → ℝ) × (∀ ℓ : Fin 1, hid ℓ → ℝ))
      = Fintype.card d ^ 2 + 2 * Fintype.card (hid 0) := by
  rw [Module.finrank_prod, Module.finrank_prod, Module.finrank_matrix, Module.finrank_self,
    mul_one, Module.finrank_pi_fintype]
  simp only [Module.finrank_fintype_fun_eq_card, Finset.univ_unique, Fin.default_eq_zero,
    Finset.sum_singleton]
  ring

omit [Nonempty T] in
/-- Helper: the directions `cobDir θ (X, X) + rescaleDir θ α + rescaleDirGate 1 θ β` are flat for
the residual network (one change of basis at both hidden states and both rescalings are
symmetries; no differentiability of `relu` is used). -/
private theorem range_dirQR_le_flat
    (θ : Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut) :
    LinearMap.range (dirQR θ) ≤ flat (Arch.gated relu id hid) 1 θ := by
  rintro _ ⟨p, rfl⟩
  rw [dirQR_apply]
  exact add_mem (cobDir_const_mem_flat_residual' θ rfl p.1)
    (add_mem (rescaleDir_mem_flat' θ 1 p.2.1) (rescaleDirGate_mem_flat relu_homogeneous θ 1 p.2.2))

/-- Helper: the directions that are flat for the residual network at every input of
`noKinkGate θ` are among the directions `cobDir θ (X, X) + rescaleDir θ α + rescaleDirGate 1 θ β`
(the previous theorem). -/
private theorem flatOn_le_range_dirQR
    (θ : Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut)
    (hθ : OneBlockGenericReGLU θ) :
    flatOn (Arch.gated relu id hid) 1 θ (noKinkGate θ) ≤ LinearMap.range (dirQR θ) := by
  intro η hη
  obtain ⟨X, α, β, rfl⟩ := flatOn_noKinkGate_le_reglu_residual θ hθ η hη
  refine LinearMap.mem_range.2 ⟨(X, α, β), ?_⟩
  rw [dirQR_apply]
  exact (add_assoc _ _ _).symm

omit [Nonempty T] in
/-- Helper (Lemma B.1 for ReGLU blocks, on the constant families): under the conditions, the
directions `cobDir θ (X, X) + rescaleDir θ α + rescaleDirGate 1 θ β` form a space of dimension
`d² + 2 d_hidden`. -/
private theorem finrank_range_dirQR
    (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (hθ : OneBlockGenericGated θ) :
    Module.finrank ℝ (LinearMap.range (dirQR θ))
      = Fintype.card d ^ 2 + 2 * Fintype.card (hid 0) := by
  have hinj0 := cobDir_add_rescaleDir_add_rescaleDirGate_injective 1 θ hθ.rank_E
    (fun ℓ => by obtain rfl := Subsingleton.elim ℓ 0; exact hθ.rank_write)
    (read_value_ne_zero_Q θ hθ) (read_gate_ne_zero_Q θ hθ)
  -- `(X, α, β) ↦ cobDir θ (X, X) + rescaleDir θ α + rescaleDirGate 1 θ β` is injective: the
  -- injectivity on all families, restricted to the constant ones
  have hinj : Function.Injective (dirQR θ) := by
    intro p q hpq
    rw [dirQR_apply, dirQR_apply, ← add_assoc, ← add_assoc] at hpq
    have h' : cobDir θ (fun _ : Fin (1 + 1) => p.1) + rescaleDir θ p.2.1
          + rescaleDirGate 1 θ p.2.2
        = cobDir θ (fun _ : Fin (1 + 1) => q.1) + rescaleDir θ q.2.1
          + rescaleDirGate 1 θ q.2.2 := hpq
    have h2 : ((fun _ : Fin (1 + 1) => p.1), p.2.1, p.2.2)
        = ((fun _ : Fin (1 + 1) => q.1), q.2.1, q.2.2) := hinj0 h'
    have h3 := Prod.mk.inj h2
    have h4 := Prod.mk.inj h3.2
    exact Prod.ext (congrFun h3.1 0) (Prod.ext h4.1 h4.2)
  rw [LinearMap.finrank_range_of_inj hinj, finrank_dirDomainQR]

/-- **Theorem 4.6 (i) / B.1 (i) for a ReGLU block with a skip, under the conditions of the
proof:** `fd = P - d² - 2 d_hidden`. -/
theorem funDim_reglu_oneBlock_residual
    (θ : Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut)
    (hθ : OneBlockGenericReGLU θ) :
    funDim (Arch.gated relu id hid) 1 θ + (Fintype.card d ^ 2 + 2 * Fintype.card (hid 0))
      = Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut) := by
  -- the sandwich, with one change of basis
  have hflat : flat (Arch.gated relu id hid) 1 θ = LinearMap.range (dirQR θ) :=
    le_antisymm ((flat_le_flatOn θ (noKinkGate θ)).trans (flatOn_le_range_dirQR θ hθ))
      (range_dirQR_le_flat θ)
  -- `fd(θ) = P - dim K(θ)` (Appendix C), and `dim K(θ) = d² + 2 d_hidden`
  have h := funDim_add_finrank_flat' (S := 1) θ
  rwa [hflat, finrank_range_dirQR θ hθ.gated] at h

/-- The same rank on a batch of inputs with no gate at its kink. -/
theorem exists_jacobianRank_reglu_oneBlock_residual
    (θ : Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut)
    (hθ : OneBlockGenericReGLU θ) :
    ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i, X i ∈ noKinkGate θ) ∧
      jacobianRank (Arch.gated relu id hid) 1 X θ
          + (Fintype.card d ^ 2 + 2 * Fintype.card (hid 0))
        = Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut) := by
  -- a batch of inputs of `noKinkGate θ` with the rank `P - dim K_U(θ)`
  obtain ⟨n, X, hX, h⟩ := exists_jacobianRank_add_finrank_flatOn (S := 1) θ (noKinkGate θ)
    (fun x hx => differentiableAt_eval_of_mem_noKinkGate 1 θ x hx)
  -- the same sandwich: `K_U(θ)` is the space of the directions
  -- `cobDir θ (X, X) + rescaleDir θ α + rescaleDirGate 1 θ β`
  have hflatOn : flatOn (Arch.gated relu id hid) 1 θ (noKinkGate θ)
      = LinearMap.range (dirQR θ) :=
    le_antisymm (flatOn_le_range_dirQR θ hθ)
      ((range_dirQR_le_flat θ).trans (flat_le_flatOn θ (noKinkGate θ)))
  refine ⟨n, X, hX, ?_⟩
  rwa [hflatOn, finrank_range_dirQR θ hθ.gated] at h

/-- **Theorem 4.6 (i) for a ReGLU block, with a skip:** for `d_in, d_out, d_hidden ≥ d ≥ 2`, at
generic parameters, `fd = P - d² - 2 d_hidden`. -/
theorem ae_funDim_reglu_oneBlock_residual
    (μ : Measure (Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ θ ∂μ, funDim (Arch.gated relu id hid) 1 θ
        + (Fintype.card d ^ 2 + 2 * Fintype.card (hid 0))
      = Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut) := by
  -- the conditions of the proof hold at generic parameters
  exact (ae_oneBlockGenericReGLU μ hd hdIn hdOut hhid).mono fun θ hθ =>
    funDim_reglu_oneBlock_residual θ hθ

/-- Theorem 4.6 (i) for a ReGLU block with a skip, on the paper's inputs: at generic parameters
the Jacobian has the rank `P - d² - 2 d_hidden` on a batch of inputs with no gate at its kink. -/
theorem ae_exists_jacobianRank_reglu_oneBlock_residual
    (μ : Measure (Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ θ ∂μ, ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i, X i ∈ noKinkGate θ) ∧
      jacobianRank (Arch.gated relu id hid) 1 X θ
          + (Fintype.card d ^ 2 + 2 * Fintype.card (hid 0))
        = Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut) := by
  -- the conditions of the proof hold at generic parameters
  exact (ae_oneBlockGenericReGLU μ hd hdIn hdOut hhid).mono fun θ hθ =>
    exists_jacobianRank_reglu_oneBlock_residual θ hθ

/-- **Theorem 4.6 (i) for a ReGLU block:** at generic parameters the skip raises the functional
dimension by exactly `d²`. -/
theorem ae_funDim_reglu_oneBlock_residual_eq_add
    (μ : Measure (Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ θ ∂μ, funDim (Arch.gated relu id hid) 1 θ
      = funDim (Arch.gated relu id hid) 0 θ + Fintype.card d ^ 2 := by
  -- `fd_1 + d² + 2 d_hidden = P` with the skip, `fd_0 + 2 d² + 2 d_hidden = P` without
  filter_upwards [ae_funDim_reglu_oneBlock_residual μ hd hdIn hdOut hhid,
    ae_funDim_reglu_oneBlock μ hd hdIn hdOut hhid] with θ h1 h2
  omega

end Skips
