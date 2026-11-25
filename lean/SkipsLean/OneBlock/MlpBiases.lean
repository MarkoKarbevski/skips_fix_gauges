import SkipsLean.OneBlock.Residual
import SkipsLean.Symmetry.BiasesFlat

/-!
# The one-block theorem with biases, for MLP blocks without symmetries inside the hidden units

Paper (skips paper), Theorem B.1 (i): "Let the network have no normalization, with or without
biases, and let the block have width at least `d_model` […]. For generic parameters the skipless
network has functional dimension `P − 2 d_model² − s` and the residual network
`P − d_model² − s`; with biases on the embedding, the block and the readout, counted in `P`, both
values are `2 d_model` lower […]. Both networks satisfy the equality condition, and the skip
raises the functional dimension by exactly `d_model²`."

Appendix B, "Reduction": "With biases `b_E`, `b_read`, `b_write` and `b_D`, the skipless network
computes `F(θ, x) = f(xC + β)A + γ_0` and the residual network `F(θ, x) = xM + f(xC + β)A + γ`,
where `M = ED`, `C = E W_read`, `A = W_write D`, `β = b_E W_read + b_read`,
`γ_0 = b_write D + b_D`, `γ = b_E D + γ_0`." Lemma B.2: "With biases, it keeps `β` and `γ_0`,
respectively `β` and `γ`, fixed as well if and only if moreover `η_{b_E} = b_E X + g_0`,
`η_{b_read} = −g_0 W_read`, `η_{b_write} = b_write Y + g_1` and `η_{b_D} = −g_1 D`, respectively
`η_{b_D} = −(g_0 + g_1) D`, for some row vectors `g_0, g_1`."

Here, for one MLP block `Arch.mlp σ id hid` with biases (`Network/Biases.lean`), an activation
with the conclusion of Lemma B.3 with `s = 0` (`UnitsRigid`, whose statement has the biases `β`
and `γ`; tanh and GELU), under the conditions `OneBlockGeneric` on the weights (they do not
involve the biases):

* `flatB_le_range_mlp_skipless`, `flatB_le_range_mlp_residual`: a flat direction is the direction
  of changes of basis and translations (Lemma B.2 with biases, after Lemma B.3): without the
  skip `cobDirB p X + (0, translateAtDir θ g)` with `X_0, X_1` and `g_0, g_1`; with it
  `cobDirB p (X, X) + (0, translateDir θ g)`.
* `funDimB_mlp_oneBlock`, `funDimB_mlp_oneBlock_residual`: `fd = P − 2 d² − 2 d` without the
  skip and `fd = P − d² − 2 d` with it, `P` counting the biases.
* `ae_paramsB_of_forall_ae`: a property of the weights that holds at generic weights holds at
  generic `(θ, b)`.
* `ae_funDimB_mlp_oneBlock`, `ae_funDimB_mlp_oneBlock_residual`,
  `ae_funDimB_mlp_oneBlock_residual_eq_add`: the same at generic `(θ, b)` for
  `d_in, d_out, d_hidden ≥ d ≥ 2`, and "the skip raises the functional dimension by exactly
  `d_model²`"; named for tanh and GELU.

Numeric check (tanh, `d = 2`, one block of 3 units: 21 and 17 of 29):
`biases_count_check_2026-11-25.py`. Not stated here: ReLU, ReLU², ReGLU, SwiGLU, GeGLU blocks and
attention blocks with biases.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {hid : Fin 1 → Type} [∀ ℓ, Fintype (hid ℓ)]
variable {σ σ' : ℝ → ℝ}

/-! ### Helpers: the function of one MLP block with biases and its derivative -/

/-- Helper: the read of the block, with its columns indexed by the hidden units. -/
private def rd_mlb (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) :
    Matrix d (hid 0) ℝ :=
  θ.read 0

/-- Helper: the write of the block, with its rows indexed by the hidden units. -/
private def wr_mlb (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) :
    Matrix (hid 0) d ℝ :=
  θ.write 0

/-- Helper: `C = E W_read`. -/
private def Cm_mlb (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) :
    Matrix dIn (hid 0) ℝ :=
  θ.E * rd_mlb θ

/-- Helper: `A = W_write D`. -/
private def Am_mlb (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) :
    Matrix (hid 0) dOut ℝ :=
  wr_mlb θ * θ.D

/-- Helper: `β = b_E W_read + b_read`. -/
private def βm_mlb (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)
    (b : Biases (Arch.mlp (T := T) (d := d) σ id hid) dOut) : hid 0 → ℝ :=
  b.E ᵥ* rd_mlb θ + b.read 0

/-- Helper: `γ_0 = b_write D + b_D`. -/
private def γm_mlb (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)
    (b : Biases (Arch.mlp (T := T) (d := d) σ id hid) dOut) : dOut → ℝ :=
  b.write 0 ᵥ* θ.D + b.D

/-- Helper: the derivative `∂C = η_E W_read + E η_read` of `C` along `η`. -/
private def dCm_mlb (θ η : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) :
    Matrix dIn (hid 0) ℝ :=
  η.E * rd_mlb θ + θ.E * rd_mlb η

/-- Helper: the derivative `∂A = η_write D + W_write η_D` of `A` along `η`. -/
private def dAm_mlb (θ η : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) :
    Matrix (hid 0) dOut ℝ :=
  wr_mlb η * θ.D + wr_mlb θ * η.D

/-- Helper: the derivative `∂β = η_{b_E} W_read + b_E η_read + η_{b_read}` of `β`. -/
private def dβm_mlb (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)
    (b : Biases (Arch.mlp (T := T) (d := d) σ id hid) dOut)
    (η : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)
    (ηb : Biases (Arch.mlp (T := T) (d := d) σ id hid) dOut) : hid 0 → ℝ :=
  ηb.E ᵥ* rd_mlb θ + b.E ᵥ* rd_mlb η + ηb.read 0

/-- Helper: the derivative `∂γ_0 = η_{b_write} D + b_write η_D + η_{b_D}` of `γ_0`. -/
private def dγm_mlb (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)
    (b : Biases (Arch.mlp (T := T) (d := d) σ id hid) dOut)
    (η : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)
    (ηb : Biases (Arch.mlp (T := T) (d := d) σ id hid) dOut) : dOut → ℝ :=
  ηb.write 0 ᵥ* θ.D + b.write 0 ᵥ* η.D + ηb.D

omit [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the read is linear in the parameters. -/
private theorem rd_line_mlb (θ η : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)
    (τ : ℝ) : rd_mlb (θ + τ • η) = rd_mlb θ + τ • rd_mlb η := rfl

omit [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the write is linear in the parameters. -/
private theorem wr_line_mlb (θ η : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)
    (τ : ℝ) : wr_mlb (θ + τ • η) = wr_mlb θ + τ • wr_mlb η := rfl

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: along the line, `C(τ) = C + τ ∂C + τ² η_E η_read`. -/
private theorem Cm_line_mlb (θ η : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)
    (τ : ℝ) :
    Cm_mlb (θ + τ • η) = Cm_mlb θ + τ • dCm_mlb θ η + (τ * τ) • Cm_mlb η := by
  simp only [Cm_mlb, dCm_mlb, rd_line_mlb, Params.add_E, Params.smul_E, Matrix.mul_add,
    Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, smul_add, smul_smul]
  abel

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: along the line, `A(τ) = A + τ ∂A + τ² η_write η_D`. -/
private theorem Am_line_mlb (θ η : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)
    (τ : ℝ) :
    Am_mlb (θ + τ • η) = Am_mlb θ + τ • dAm_mlb θ η + (τ * τ) • Am_mlb η := by
  simp only [Am_mlb, dAm_mlb, wr_line_mlb, Params.add_D, Params.smul_D, Matrix.mul_add,
    Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, smul_add, smul_smul]
  abel

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: along the line, `β(τ) = β + τ ∂β + τ² η_{b_E} η_read`. -/
private theorem βm_line_mlb (θ η : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)
    (b ηb : Biases (Arch.mlp (T := T) (d := d) σ id hid) dOut) (τ : ℝ) :
    βm_mlb (θ + τ • η) (b + τ • ηb)
      = βm_mlb θ b + τ • dβm_mlb θ b η ηb + (τ * τ) • (ηb.E ᵥ* rd_mlb η) := by
  simp only [βm_mlb, dβm_mlb, rd_line_mlb, Biases.add_E, Biases.smul_E, Biases.add_read,
    Biases.smul_read, Matrix.vecMul_add, Matrix.add_vecMul, Matrix.vecMul_smul,
    Matrix.smul_vecMul, smul_add, smul_smul]
  abel

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: along the line, `γ_0(τ) = γ_0 + τ ∂γ_0 + τ² η_{b_write} η_D`. -/
private theorem γm_line_mlb (θ η : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)
    (b ηb : Biases (Arch.mlp (T := T) (d := d) σ id hid) dOut) (τ : ℝ) :
    γm_mlb (θ + τ • η) (b + τ • ηb)
      = γm_mlb θ b + τ • dγm_mlb θ b η ηb + (τ * τ) • (ηb.write 0 ᵥ* η.D) := by
  simp only [γm_mlb, dγm_mlb, Params.add_D, Params.smul_D, Biases.add_D, Biases.smul_D,
    Biases.add_write, Biases.smul_write, Matrix.vecMul_add, Matrix.add_vecMul,
    Matrix.vecMul_smul, Matrix.smul_vecMul, smul_add, smul_smul]
  abel

omit [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the matrix whose rows are all `v`, times `M`, has all rows `v M`. -/
private theorem of_const_mul_mlb {m n : Type*} [Fintype m] (v : m → ℝ) (M : Matrix m n ℝ) :
    (Matrix.of fun _ : T => v) * M = Matrix.of fun _ : T => v ᵥ* M := by
  ext t j
  rfl

omit [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the sum of two matrices with constant rows has constant rows. -/
private theorem of_const_add_mlb {n : Type*} (u v : n → ℝ) :
    (Matrix.of fun _ : T => u) + (Matrix.of fun _ : T => v) = Matrix.of fun _ : T => u + v :=
  rfl

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dOut] in
/-- Helper: the skipless network with biases, `F(θ, x) = γ_0 + σ(x C + β) A` (stream matrix
`0`). -/
private theorem evalB_mlp_eq_mlb (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)
    (b : Biases (Arch.mlp (T := T) (d := d) σ id hid) dOut) (x : Matrix T dIn ℝ) :
    evalB (Arch.mlp σ id hid) 0 θ b x
      = (Matrix.of fun _ : T => γm_mlb θ b)
        + (x * Cm_mlb θ + Matrix.of fun _ : T => βm_mlb θ b).map σ * Am_mlb θ := by
  have h1 : (Fin.last 1 : Fin 2) = (0 : Fin 1).succ := rfl
  have hχ : (Arch.mlp (T := T) (d := d) σ id hid).χ = id := rfl
  have hf : (Arch.mlp (T := T) (d := d) σ id hid).f 0 = fun M => M.map σ := rfl
  -- `h_1 = h_0 0 + σ(h_0 W_read + b_read) W_write + b_write` with `h_0 = x E + b_E`
  rw [evalB, h1, hiddenB_succ, Fin.castSucc_zero, hiddenB_zero, hχ, hf]
  simp only [Pi.zero_apply, Matrix.mul_zero, zero_add, id_eq, Matrix.add_mul, Matrix.mul_assoc,
    of_const_mul_mlb]
  rw [add_assoc (x * (θ.E * θ.read 0)), of_const_add_mlb, add_assoc, of_const_add_mlb, add_comm]
  rfl

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dOut] in
/-- Helper: the entries of `F(θ, x)`, `γ_{0,o} + ∑_i σ((x C)_{t i} + β_i) A_{i o}`. -/
private theorem evalB_mlp_apply_mlb
    (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)
    (b : Biases (Arch.mlp (T := T) (d := d) σ id hid) dOut) (x : Matrix T dIn ℝ) (t : T)
    (o : dOut) :
    evalB (Arch.mlp σ id hid) 0 θ b x t o
      = γm_mlb θ b o + ∑ i : hid 0, σ ((x * Cm_mlb θ) t i + βm_mlb θ b i) * Am_mlb θ i o := by
  rw [evalB_mlp_eq_mlb]
  rfl

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dOut] in
/-- Helper: the entries of `F(θ + τ η, b + τ η_b)(x)` as functions of `τ`. -/
private theorem evalB_line_apply_mlb
    (θ η : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)
    (b ηb : Biases (Arch.mlp (T := T) (d := d) σ id hid) dOut) (x : Matrix T dIn ℝ) (t : T)
    (o : dOut) (τ : ℝ) :
    evalB (Arch.mlp σ id hid) 0 (θ + τ • η) (b + τ • ηb) x t o
      = (γm_mlb θ b o + τ * dγm_mlb θ b η ηb o + τ * τ * (ηb.write 0 ᵥ* η.D) o)
        + ∑ i : hid 0,
          σ (((x * Cm_mlb θ) t i + τ * (x * dCm_mlb θ η) t i + τ * τ * (x * Cm_mlb η) t i)
              + (βm_mlb θ b i + τ * dβm_mlb θ b η ηb i + τ * τ * (ηb.E ᵥ* rd_mlb η) i))
            * (Am_mlb θ i o + τ * dAm_mlb θ η i o + τ * τ * Am_mlb η i o) := by
  rw [evalB_mlp_apply_mlb, Cm_line_mlb, Am_line_mlb, βm_line_mlb, γm_line_mlb]
  simp only [Matrix.mul_add, Matrix.mul_smul]
  rfl

omit [Nonempty T] [DecidableEq d] in
/-- Helper (the chain rule): the derivative of `(θ, b) ↦ F(θ, b, x)` along `η` has the entries
`∂γ_{0,o} + ∑_i [σ(z_i) (∂A)_{i o} + σ'(z_i) ((x ∂C)_{t i} + ∂β_i) A_{i o}]`,
`z_i = (x C)_{t i} + β_i`. -/
private theorem fderiv_evalB_apply_mlb (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (p η : ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)
    (x : Matrix T dIn ℝ) (t : T) (o : dOut) :
    fderiv ℝ (fun q : ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut =>
        evalB (Arch.mlp σ id hid) 0 q.1 q.2 x) p η t o
      = dγm_mlb p.1 p.2 η.1 η.2 o + ∑ i : hid 0,
        (σ ((x * Cm_mlb p.1) t i + βm_mlb p.1 p.2 i) * dAm_mlb p.1 η.1 i o
          + σ' ((x * Cm_mlb p.1) t i + βm_mlb p.1 p.2 i)
            * ((x * dCm_mlb p.1 η.1) t i + dβm_mlb p.1 p.2 η.1 η.2 i) * Am_mlb p.1 i o) := by
  have hdiff := differentiable_evalB (A := Arch.mlp (T := T) (d := d) σ id hid) (S := 0)
    (dIn := dIn) (dOut := dOut)
    (fun ℓ => differentiable_f_mlp (fun z => (hσ z).differentiableAt) ℓ) differentiable_id x
  -- the line `τ ↦ (θ + τ η, b + τ η_b)` has velocity `η` and passes through `p` at `τ = 0`
  have hline : HasDerivAt (fun τ : ℝ => (p.1 + τ • η.1, p.2 + τ • η.2)) η 0 := by
    have h1 := ((hasDerivAt_id (0 : ℝ)).smul_const η.1).const_add p.1
    have h2 := ((hasDerivAt_id (0 : ℝ)).smul_const η.2).const_add p.2
    rw [one_smul] at h1 h2
    exact h1.prodMk h2
  have h0 : p = (p.1 + (0 : ℝ) • η.1, p.2 + (0 : ℝ) • η.2) := by
    rw [zero_smul, zero_smul, add_zero, add_zero]
  -- the chain rule along the line
  have h1 := (hdiff p).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hline h0
  have h2 := hasDerivAt_pi.1 (hasDerivAt_pi.1 h1 t) o
  -- the same derivative computed entrywise: products and sums of real functions of `τ`
  have h3 : HasDerivAt (fun τ : ℝ =>
      evalB (Arch.mlp σ id hid) 0 (p.1 + τ • η.1) (p.2 + τ • η.2) x t o)
      (dγm_mlb p.1 p.2 η.1 η.2 o + ∑ i : hid 0,
        (σ ((x * Cm_mlb p.1) t i + βm_mlb p.1 p.2 i) * dAm_mlb p.1 η.1 i o
          + σ' ((x * Cm_mlb p.1) t i + βm_mlb p.1 p.2 i)
            * ((x * dCm_mlb p.1 η.1) t i + dβm_mlb p.1 p.2 η.1 η.2 i) * Am_mlb p.1 i o)) 0 := by
    rw [funext fun τ => evalB_line_apply_mlb p.1 η.1 p.2 η.2 x t o τ]
    refine (hasDerivAt_quad _ _ _).add (HasDerivAt.fun_sum fun i _ => ?_)
    have hu := (hasDerivAt_quad ((x * Cm_mlb p.1) t i) ((x * dCm_mlb p.1 η.1) t i)
      ((x * Cm_mlb η.1) t i)).add (hasDerivAt_quad (βm_mlb p.1 p.2 i)
        (dβm_mlb p.1 p.2 η.1 η.2 i) ((η.2.E ᵥ* rd_mlb η.1) i))
    have hv := hasDerivAt_quad (Am_mlb p.1 i o) (dAm_mlb p.1 η.1 i o) (Am_mlb η.1 i o)
    have h := ((hσ _).comp (0 : ℝ) hu).mul hv
    convert h using 1
    · rfl
    · simp only [Function.comp_apply, Pi.add_apply, zero_mul, mul_zero, add_zero]
      ring
  exact h2.unique h3

/-- **Lemma B.2 with biases, after Lemma B.3, for one skipless MLP block with `s = 0`:** under the
conditions `OneBlockGeneric` on the weights, every flat direction of the skipless network with
biases is the direction of changes of basis `X_0, X_1` and translations `g_0, g_1` of the two
hidden states. -/
theorem flatB_le_range_mlp_skipless (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hU : UnitsRigid σ σ' dIn dOut (hid 0))
    (p : ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) (hp : OneBlockGeneric p.1)
    (η : ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)
    (hη : η ∈ flatB (Arch.mlp σ id hid) 0 p) :
    ∃ (X : Fin 2 → Matrix d d ℝ) (g : Fin 2 → d → ℝ),
      η = cobDirB p X + (0, translateAtDir p.1 g) := by
  -- the derivative of `F(θ, b, x)` along `η` vanishes at every input, entry by entry
  have hzero : ∀ (x : Matrix T dIn ℝ) (t : T) (o : dOut), dγm_mlb p.1 p.2 η.1 η.2 o
      + ∑ i : hid 0, (σ ((x * Cm_mlb p.1) t i + βm_mlb p.1 p.2 i) * dAm_mlb p.1 η.1 i o
        + σ' ((x * Cm_mlb p.1) t i + βm_mlb p.1 p.2 i)
          * ((x * dCm_mlb p.1 η.1) t i + dβm_mlb p.1 p.2 η.1 η.2 i) * Am_mlb p.1 i o) = 0 := by
    intro x t o
    rw [← fderiv_evalB_apply_mlb hσ p η x t o]
    have h := LinearMap.mem_ker.1 ((Submodule.mem_iInf _).1 hη x)
    exact congrFun (congrFun h t) o
  -- Lemma B.3 (inputs `x` with all rows equal to `v`): `∂γ_0 = 0`, `∂C = 0`, `∂β = 0`, `∂A = 0`
  obtain ⟨-, hγ, hc, hβ, ha⟩ := hU (fun i => (Cm_mlb p.1)ᵀ i) (βm_mlb p.1 p.2)
    (fun i => Am_mlb p.1 i) 0 (dγm_mlb p.1 p.2 η.1 η.2) (fun i => (dCm_mlb p.1 η.1)ᵀ i)
    (dβm_mlb p.1 p.2 η.1 η.2) (fun i => dAm_mlb p.1 η.1 i) (fun i => hp.row_ne_zero i)
    (fun i => hp.col_ne_zero i) (fun i j hij => hp.col_not_collinear i j hij) (by
      intro v
      funext o
      have h := hzero (Matrix.of fun _ => v) (Classical.arbitrary T) o
      simp only [Matrix.vecMul_zero, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        Pi.zero_apply, zero_add]
      exact h)
  -- Lemma C.2: a direction that keeps `C` and `A` moves the weights by two changes of basis
  have hC : η.1.E * p.1.read 0 + p.1.E * η.1.read 0 = 0 := by
    ext a i
    exact congrFun (congrFun hc i) a
  have hA : η.1.write 0 * p.1.D + p.1.write 0 * η.1.D = 0 := by
    ext i o
    exact congrFun (congrFun ha i) o
  obtain ⟨X, hX⟩ := (keeps_products_iff_mem_range_cobDir p.1 η.1 hp.rank_E hp.rank_D
    hp.rank_read hp.rank_write).1 ⟨hC, hA⟩
  have hR : η.1.read 0 = -(X 0 * p.1.read 0) := by rw [hX]; rfl
  have hD : η.1.D = -(X 1 * p.1.D) := by rw [hX]; rfl
  -- `∂β = 0`: `η_{b_read} = −g_0 W_read` with `g_0 = η_{b_E} − b_E X_0`
  have hbR : η.2.read 0 = -((η.2.E - p.2.E ᵥ* X 0) ᵥ* p.1.read 0) := by
    have h : η.2.E ᵥ* p.1.read 0 + p.2.E ᵥ* η.1.read 0 + η.2.read 0 = 0 := hβ
    rw [hR, Matrix.vecMul_neg, ← Matrix.vecMul_vecMul] at h
    rw [Matrix.sub_vecMul]
    linear_combination h
  -- `∂γ_0 = 0`: `η_{b_D} = −g_1 D` with `g_1 = η_{b_write} − b_write X_1`
  have hbD : η.2.D = -((η.2.write 0 - p.2.write 0 ᵥ* X 1) ᵥ* p.1.D) := by
    have h : η.2.write 0 ᵥ* p.1.D + p.2.write 0 ᵥ* η.1.D + η.2.D = 0 := hγ
    rw [hD, Matrix.vecMul_neg, ← Matrix.vecMul_vecMul] at h
    rw [Matrix.sub_vecMul]
    linear_combination h
  -- so `η` is the direction of the changes of basis `X` and of the translations `g_0, g_1`
  refine ⟨X, ![η.2.E - p.2.E ᵥ* X 0, η.2.write 0 - p.2.write 0 ᵥ* X 1], ?_⟩
  refine Prod.ext ?_ ?_
  · show η.1 = cobDir p.1 X + 0
    rw [add_zero]
    exact hX
  · apply Biases.ext'
    · show η.2.E = p.2.E ᵥ* X 0 + (η.2.E - p.2.E ᵥ* X 0)
      abel
    · intro ℓ
      obtain rfl : ℓ = 0 := Subsingleton.elim ℓ 0
      show η.2.read 0 = 0 + -((η.2.E - p.2.E ᵥ* X 0) ᵥ* p.1.read 0)
      rw [zero_add]
      exact hbR
    · intro ℓ
      obtain rfl : ℓ = 0 := Subsingleton.elim ℓ 0
      show η.2.write 0 = p.2.write 0 ᵥ* X 1 + (η.2.write 0 - p.2.write 0 ᵥ* X 1)
      abel
    · show η.2.D = 0 + -((η.2.write 0 - p.2.write 0 ᵥ* X 1) ᵥ* p.1.D)
      rw [zero_add]
      exact hbD

/-- **Theorem B.1 (i) of the skips paper with biases, the skipless network, at one parameter, for
an MLP block with `s = 0`:** under the conditions `OneBlockGeneric` on the weights, the skipless
network with biases has `fd = P − 2 d² − 2 d`, with `P` counting the biases. -/
theorem funDimB_mlp_oneBlock (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hU : UnitsRigid σ σ' dIn dOut (hid 0))
    (p : ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) (hp : OneBlockGeneric p.1) :
    funDimB (Arch.mlp σ id hid) 0 p + (2 * Fintype.card d ^ 2 + 2 * Fintype.card d)
      = Module.finrank ℝ (ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) := by
  sorry

/-- **Lemma B.2 with biases, after Lemma B.3, for one residual MLP block with `s = 0`:** under
the conditions `OneBlockGeneric` on the weights, every flat direction of the residual network
with biases is the direction of one change of basis `X` of both hidden states and of the
translations `g_0, g_1` of Lemma A.8. -/
theorem flatB_le_range_mlp_residual (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hU : UnitsRigid σ σ' dIn dOut (hid 0))
    (p : ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) (hp : OneBlockGeneric p.1)
    (η : ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)
    (hη : η ∈ flatB (Arch.mlp σ id hid) 1 p) :
    ∃ (X : Matrix d d ℝ) (g : Fin 2 → d → ℝ),
      η = cobDirB p (fun _ => X) + (0, translateDir p.1 g) := by
  sorry

/-- **Theorem B.1 (i) of the skips paper with biases, the residual network, at one parameter, for
an MLP block with `s = 0`:** under the conditions `OneBlockGeneric` on the weights, the residual
network with biases has `fd = P − d² − 2 d`, with `P` counting the biases. -/
theorem funDimB_mlp_oneBlock_residual (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hU : UnitsRigid σ σ' dIn dOut (hid 0))
    (p : ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) (hp : OneBlockGeneric p.1) :
    funDimB (Arch.mlp σ id hid) 1 p + (Fintype.card d ^ 2 + 2 * Fintype.card d)
      = Module.finrank ℝ (ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) := by
  sorry

omit [Nonempty T] [DecidableEq d] in
/-- **A property of the weights that holds at generic weights holds at generic weights and
biases:** if `P θ` holds at almost every `θ` for every Haar measure on the weights, then
`P p.1` holds at almost every `p = (θ, b)` for every Haar measure on the pairs. -/
theorem ae_paramsB_of_forall_ae {L : ℕ} {A : Arch T d L} {P : Params A dIn dOut → Prop}
    (h : ∀ (ν : Measure (Params A dIn dOut)) [ν.IsAddHaarMeasure], ∀ᵐ θ ∂ν, P θ)
    (μ : Measure (ParamsB A dIn dOut)) [μ.IsAddHaarMeasure] :
    ∀ᵐ p ∂μ, P p.1 := by
  -- the product of Haar measures on the weights and on the biases is a Haar measure on the pairs
  let ν : Measure (Params A dIn dOut) := Measure.addHaar
  let ν' : Measure (Biases A dOut) := Measure.addHaar
  -- `μ` is absolutely continuous with respect to it (uniqueness of Haar measure)
  have hac : μ ≪ ν.prod ν' := Measure.absolutelyContinuous_isAddHaarMeasure μ (ν.prod ν')
  -- under `ν × ν'`, the weights `p.1` are distributed by `ν`, so `P p.1` holds almost everywhere
  exact hac.ae_le (Measure.quasiMeasurePreserving_fst.ae (h ν))

/-- **Theorem B.1 (i) of the skips paper with biases, the skipless network, for an MLP block with
`s = 0`:** for `d_in, d_out, d_hidden ≥ d ≥ 2`, at generic weights and biases the skipless
network has `fd = P − 2 d² − 2 d`. -/
theorem ae_funDimB_mlp_oneBlock (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hU : UnitsRigid σ σ' dIn dOut (hid 0))
    (μ : Measure (ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ p ∂μ, funDimB (Arch.mlp σ id hid) 0 p + (2 * Fintype.card d ^ 2 + 2 * Fintype.card d)
      = Module.finrank ℝ (ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) :=
  (ae_paramsB_of_forall_ae (fun ν _ => ae_oneBlockGeneric ν hd hdIn hdOut hhid) μ).mono
    fun p hp => funDimB_mlp_oneBlock hσ hU p hp

/-- **Theorem B.1 (i) of the skips paper with biases, the residual network, for an MLP block with
`s = 0`:** for `d_in, d_out, d_hidden ≥ d ≥ 2`, at generic weights and biases the residual
network has `fd = P − d² − 2 d`. -/
theorem ae_funDimB_mlp_oneBlock_residual (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hU : UnitsRigid σ σ' dIn dOut (hid 0))
    (μ : Measure (ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ p ∂μ, funDimB (Arch.mlp σ id hid) 1 p + (Fintype.card d ^ 2 + 2 * Fintype.card d)
      = Module.finrank ℝ (ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) :=
  (ae_paramsB_of_forall_ae (fun ν _ => ae_oneBlockGeneric ν hd hdIn hdOut hhid) μ).mono
    fun p hp => funDimB_mlp_oneBlock_residual hσ hU p hp

/-- **Theorem B.1 (i) of the skips paper with biases, "the skip raises the functional dimension
by exactly `d_model²`", for an MLP block with `s = 0`:** for `d_in, d_out, d_hidden ≥ d ≥ 2`, at
generic weights and biases. -/
theorem ae_funDimB_mlp_oneBlock_residual_eq_add (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hU : UnitsRigid σ σ' dIn dOut (hid 0))
    (μ : Measure (ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ p ∂μ, funDimB (Arch.mlp σ id hid) 1 p
      = funDimB (Arch.mlp σ id hid) 0 p + Fintype.card d ^ 2 := by
  filter_upwards [ae_funDimB_mlp_oneBlock hσ hU μ hd hdIn hdOut hhid,
    ae_funDimB_mlp_oneBlock_residual hσ hU μ hd hdIn hdOut hhid] with p h0 h1
  omega

/-- **Theorem B.1 (i) with biases for one `tanh` block:** the skip raises the functional dimension
by exactly `d²`. -/
theorem ae_funDimB_tanh_oneBlock_residual_eq_add
    (μ : Measure (ParamsB (Arch.mlp (T := T) (d := d) Real.tanh id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ p ∂μ, funDimB (Arch.mlp Real.tanh id hid) 1 p
      = funDimB (Arch.mlp Real.tanh id hid) 0 p + Fintype.card d ^ 2 :=
  ae_funDimB_mlp_oneBlock_residual_eq_add hasDerivAt_tanh (tanh_unitsRigid _ _ _) μ hd hdIn hdOut
    hhid

/-- **Theorem B.1 (i) with biases for one GELU block:** the skip raises the functional dimension
by exactly `d²`. -/
theorem ae_funDimB_gelu_oneBlock_residual_eq_add
    (μ : Measure (ParamsB (Arch.mlp (T := T) (d := d) gelu id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ p ∂μ, funDimB (Arch.mlp gelu id hid) 1 p
      = funDimB (Arch.mlp gelu id hid) 0 p + Fintype.card d ^ 2 :=
  ae_funDimB_mlp_oneBlock_residual_eq_add hasDerivAt_gelu (gelu_unitsRigid _ _ _) μ hd hdIn hdOut
    hhid

end Skips
