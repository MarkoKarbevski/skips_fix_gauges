import SkipsLean.OneBlock.MlpBiases
import SkipsLean.Symmetry.BiasesRescaleCount

/-!
# The one-block theorem with biases, for SwiGLU and GeGLU blocks

Paper (skips paper), Theorem B.1 (i): "Let the network have no normalization, with or without
biases, and let the block have width at least `d_model` […]. For generic parameters the skipless
network has functional dimension `P − 2 d_model² − s` and the residual network
`P − d_model² − s`; with biases on the embedding, the block and the readout, counted in `P`, both
values are `2 d_model` lower […]. Both networks satisfy the equality condition, and the skip
raises the functional dimension by exactly `d_model²`."

Appendix B, "Reduction": "For the gated blocks ReGLU, SwiGLU and GeGLU, in the same way, the value
weights `(e_i, β_i′)` of each unit, introduced below, have `e_i ≠ 0` and are not proportional to
its gate weights `(c_i, β_i)`." Step 3: "A rescaling of the units by numbers `λ_i` is also a
direction in parameter space […], and similarly for ReGLU and for the values of SwiGLU and GeGLU
[…]. So every flat direction is the sum of a direction of the changes of basis and translations
of Lemma B.2 and a rescaling of the units".

Here, for one gated block `Arch.gated σ id hid` with biases (`Network/Biases.lean`), a gate
activation with the conclusion of Lemma B.3 for SwiGLU and GeGLU (`GatedUnitsRescale`, whose
statement has the biases `β`, `β′` and `γ`), under the conditions `OneBlockGenericGated` on the
weights (they do not involve the biases); `s = d_hidden`, the rescalings of the values. The twin
for MLP blocks with `s = 0` is `OneBlock/MlpBiases.lean`; without biases: `OneBlock/Gated.lean`
and `OneBlock/Residual.lean`.

* `flatB_le_range_gated_skipless`, `flatB_le_range_gated_residual`: a flat direction is the sum of
  a direction of changes of basis and translations and a direction of the rescalings of the
  values with their biases (`rescaleDirB`).
* `funDimB_gated_oneBlock`, `funDimB_gated_oneBlock_residual`: `fd = P − 2 d² − 2 d − d_hidden`
  without the skip and `fd = P − d² − 2 d − d_hidden` with it, `P` counting the biases.
* The same at generic `(θ, b)` for `d_in, d_out, d_hidden ≥ d ≥ 2`, and "the skip raises the
  functional dimension by exactly `d_model²`"; named for SwiGLU and GeGLU.

Numeric check (SwiGLU, `d = d_in = d_out = 2`, one block of 2 units, `P = 30`: 16 and 20):
`ai_notes/biases_inside_blocks_check_2026-11-25.py`.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {hid : Fin 1 → Type} [∀ ℓ, Fintype (hid ℓ)]
variable {σ σ' : ℝ → ℝ}

/-! ### Helpers: the function of one gated block with biases and its derivative -/

/-- Helper: the read of the block, with its columns indexed by the gates and the values. -/
private def rd_gbi (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) :
    Matrix d (hid 0 ⊕ hid 0) ℝ :=
  θ.read 0

/-- Helper: the write of the block, with its rows indexed by the hidden units. -/
private def wr_gbi (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) :
    Matrix (hid 0) d ℝ :=
  θ.write 0

/-- Helper: `C = E W_read`, with the gate columns `c_i` and the value columns `e_i`. -/
private def Cm_gbi (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) :
    Matrix dIn (hid 0 ⊕ hid 0) ℝ :=
  θ.E * rd_gbi θ

/-- Helper: `A = W_write D`, with the rows `a_i`. -/
private def Am_gbi (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) :
    Matrix (hid 0) dOut ℝ :=
  wr_gbi θ * θ.D

/-- Helper: `β = b_E W_read + b_read`, with the gate biases `β_i` and the value biases `β'_i`. -/
private def βm_gbi (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (b : Biases (Arch.gated (T := T) (d := d) σ id hid) dOut) : hid 0 ⊕ hid 0 → ℝ :=
  b.E ᵥ* rd_gbi θ + b.read 0

/-- Helper: `γ_0 = b_write D + b_D`. -/
private def γm_gbi (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (b : Biases (Arch.gated (T := T) (d := d) σ id hid) dOut) : dOut → ℝ :=
  b.write 0 ᵥ* θ.D + b.D

/-- Helper: the derivative `∂C = η_E W_read + E η_read` of `C` along `η`. -/
private def dCm_gbi (θ η : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) :
    Matrix dIn (hid 0 ⊕ hid 0) ℝ :=
  η.E * rd_gbi θ + θ.E * rd_gbi η

/-- Helper: the derivative `∂A = η_write D + W_write η_D` of `A` along `η`. -/
private def dAm_gbi (θ η : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) :
    Matrix (hid 0) dOut ℝ :=
  wr_gbi η * θ.D + wr_gbi θ * η.D

/-- Helper: the derivative `∂β = η_{b_E} W_read + b_E η_read + η_{b_read}` of `β`. -/
private def dβm_gbi (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (b : Biases (Arch.gated (T := T) (d := d) σ id hid) dOut)
    (η : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (ηb : Biases (Arch.gated (T := T) (d := d) σ id hid) dOut) : hid 0 ⊕ hid 0 → ℝ :=
  ηb.E ᵥ* rd_gbi θ + b.E ᵥ* rd_gbi η + ηb.read 0

/-- Helper: the derivative `∂γ_0 = η_{b_write} D + b_write η_D + η_{b_D}` of `γ_0`. -/
private def dγm_gbi (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (b : Biases (Arch.gated (T := T) (d := d) σ id hid) dOut)
    (η : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (ηb : Biases (Arch.gated (T := T) (d := d) σ id hid) dOut) : dOut → ℝ :=
  ηb.write 0 ᵥ* θ.D + b.write 0 ᵥ* η.D + ηb.D

omit [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the read is linear in the parameters. -/
private theorem rd_line_gbi (θ η : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (τ : ℝ) : rd_gbi (θ + τ • η) = rd_gbi θ + τ • rd_gbi η := rfl

omit [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the write is linear in the parameters. -/
private theorem wr_line_gbi (θ η : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (τ : ℝ) : wr_gbi (θ + τ • η) = wr_gbi θ + τ • wr_gbi η := rfl

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: along the line, `C(τ) = C + τ ∂C + τ² η_E η_read`. -/
private theorem Cm_line_gbi (θ η : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (τ : ℝ) :
    Cm_gbi (θ + τ • η) = Cm_gbi θ + τ • dCm_gbi θ η + (τ * τ) • Cm_gbi η := by
  simp only [Cm_gbi, dCm_gbi, rd_line_gbi, Params.add_E, Params.smul_E, Matrix.mul_add,
    Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, smul_add, smul_smul]
  abel

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: along the line, `A(τ) = A + τ ∂A + τ² η_write η_D`. -/
private theorem Am_line_gbi (θ η : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (τ : ℝ) :
    Am_gbi (θ + τ • η) = Am_gbi θ + τ • dAm_gbi θ η + (τ * τ) • Am_gbi η := by
  simp only [Am_gbi, dAm_gbi, wr_line_gbi, Params.add_D, Params.smul_D, Matrix.mul_add,
    Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, smul_add, smul_smul]
  abel

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: along the line, `β(τ) = β + τ ∂β + τ² η_{b_E} η_read`. -/
private theorem βm_line_gbi (θ η : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (b ηb : Biases (Arch.gated (T := T) (d := d) σ id hid) dOut) (τ : ℝ) :
    βm_gbi (θ + τ • η) (b + τ • ηb)
      = βm_gbi θ b + τ • dβm_gbi θ b η ηb + (τ * τ) • (ηb.E ᵥ* rd_gbi η) := by
  simp only [βm_gbi, dβm_gbi, rd_line_gbi, Biases.add_E, Biases.smul_E, Biases.add_read,
    Biases.smul_read, Matrix.vecMul_add, Matrix.add_vecMul, Matrix.vecMul_smul,
    Matrix.smul_vecMul, smul_add, smul_smul]
  abel

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: along the line, `γ_0(τ) = γ_0 + τ ∂γ_0 + τ² η_{b_write} η_D`. -/
private theorem γm_line_gbi (θ η : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (b ηb : Biases (Arch.gated (T := T) (d := d) σ id hid) dOut) (τ : ℝ) :
    γm_gbi (θ + τ • η) (b + τ • ηb)
      = γm_gbi θ b + τ • dγm_gbi θ b η ηb + (τ * τ) • (ηb.write 0 ᵥ* η.D) := by
  simp only [γm_gbi, dγm_gbi, Params.add_D, Params.smul_D, Biases.add_D, Biases.smul_D,
    Biases.add_write, Biases.smul_write, Matrix.vecMul_add, Matrix.add_vecMul,
    Matrix.vecMul_smul, Matrix.smul_vecMul, smul_add, smul_smul]
  abel

omit [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the matrix whose rows are all `v`, times `M`, has all rows `v M`. -/
private theorem of_const_mul_gbi {m n : Type*} [Fintype m] (v : m → ℝ) (M : Matrix m n ℝ) :
    (Matrix.of fun _ : T => v) * M = Matrix.of fun _ : T => v ᵥ* M := by
  ext t j
  rfl

omit [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the sum of two matrices with constant rows has constant rows. -/
private theorem of_const_add_gbi {n : Type*} (u v : n → ℝ) :
    (Matrix.of fun _ : T => u) + (Matrix.of fun _ : T => v) = Matrix.of fun _ : T => u + v :=
  rfl

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dOut] in
/-- Helper: the skipless network with biases, `F(θ, x) = γ_0 + (σ(x C_g + β) ⊙ (x C_v + β')) A`
(stream matrix `0`). -/
private theorem evalB_gated_eq_gbi
    (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (b : Biases (Arch.gated (T := T) (d := d) σ id hid) dOut) (x : Matrix T dIn ℝ) :
    evalB (Arch.gated σ id hid) 0 θ b x
      = (Matrix.of fun _ : T => γm_gbi θ b)
        + (Matrix.of fun t i => σ ((x * Cm_gbi θ) t (Sum.inl i) + βm_gbi θ b (Sum.inl i))
          * ((x * Cm_gbi θ) t (Sum.inr i) + βm_gbi θ b (Sum.inr i))) * Am_gbi θ := by
  have h1 : (Fin.last 1 : Fin 2) = (0 : Fin 1).succ := rfl
  have hχ : (Arch.gated (T := T) (d := d) σ id hid).χ = id := rfl
  have hf : (Arch.gated (T := T) (d := d) σ id hid).f 0
      = fun M => Matrix.of fun t i => σ (M t (Sum.inl i)) * M t (Sum.inr i) := rfl
  -- `h_1 = h_0 0 + f(h_0 W_read + b_read) W_write + b_write` with `h_0 = x E + b_E`
  rw [evalB, h1, hiddenB_succ, Fin.castSucc_zero, hiddenB_zero, hχ, hf]
  simp only [Pi.zero_apply, Matrix.mul_zero, zero_add, id_eq, Matrix.add_mul, Matrix.mul_assoc,
    of_const_mul_gbi]
  rw [add_assoc (x * (θ.E * θ.read 0)), of_const_add_gbi, add_assoc, of_const_add_gbi, add_comm]
  rfl

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dOut] in
/-- Helper: the entries of `F(θ, x)`, `γ_{0,o} + ∑_i σ(z_i) w_i A_{i o}` with
`z_i = (x C)_{t, g i} + β_i` and `w_i = (x C)_{t, v i} + β'_i`. -/
private theorem evalB_gated_apply_gbi
    (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (b : Biases (Arch.gated (T := T) (d := d) σ id hid) dOut) (x : Matrix T dIn ℝ) (t : T)
    (o : dOut) :
    evalB (Arch.gated σ id hid) 0 θ b x t o
      = γm_gbi θ b o + ∑ i : hid 0, σ ((x * Cm_gbi θ) t (Sum.inl i) + βm_gbi θ b (Sum.inl i))
        * ((x * Cm_gbi θ) t (Sum.inr i) + βm_gbi θ b (Sum.inr i)) * Am_gbi θ i o := by
  rw [evalB_gated_eq_gbi]
  rfl

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dOut] in
/-- Helper: the entries of `F(θ + τ η, b + τ η_b)(x)` as functions of `τ`. -/
private theorem evalB_line_apply_gbi
    (θ η : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (b ηb : Biases (Arch.gated (T := T) (d := d) σ id hid) dOut) (x : Matrix T dIn ℝ) (t : T)
    (o : dOut) (τ : ℝ) :
    evalB (Arch.gated σ id hid) 0 (θ + τ • η) (b + τ • ηb) x t o
      = (γm_gbi θ b o + τ * dγm_gbi θ b η ηb o + τ * τ * (ηb.write 0 ᵥ* η.D) o)
        + ∑ i : hid 0,
          σ (((x * Cm_gbi θ) t (Sum.inl i) + τ * (x * dCm_gbi θ η) t (Sum.inl i)
                + τ * τ * (x * Cm_gbi η) t (Sum.inl i))
              + (βm_gbi θ b (Sum.inl i) + τ * dβm_gbi θ b η ηb (Sum.inl i)
                + τ * τ * (ηb.E ᵥ* rd_gbi η) (Sum.inl i)))
            * (((x * Cm_gbi θ) t (Sum.inr i) + τ * (x * dCm_gbi θ η) t (Sum.inr i)
                + τ * τ * (x * Cm_gbi η) t (Sum.inr i))
              + (βm_gbi θ b (Sum.inr i) + τ * dβm_gbi θ b η ηb (Sum.inr i)
                + τ * τ * (ηb.E ᵥ* rd_gbi η) (Sum.inr i)))
            * (Am_gbi θ i o + τ * dAm_gbi θ η i o + τ * τ * Am_gbi η i o) := by
  rw [evalB_gated_apply_gbi, Cm_line_gbi, Am_line_gbi, βm_line_gbi, γm_line_gbi]
  simp only [Matrix.mul_add, Matrix.mul_smul]
  rfl

omit [Nonempty T] [DecidableEq d] in
/-- Helper (the chain rule): the derivative of `(θ, b) ↦ F(θ, b, x)` along `η` has the entries
`∂γ_{0,o} + ∑_i [σ(z_i) w_i (∂A)_{i o} + σ'(z_i) ((x ∂C)_{t, g i} + ∂β_i) w_i A_{i o}
+ σ(z_i) ((x ∂C)_{t, v i} + ∂β'_i) A_{i o}]`, `z_i = (x C)_{t, g i} + β_i`,
`w_i = (x C)_{t, v i} + β'_i`. -/
private theorem fderiv_evalB_apply_gbi (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (p η : ParamsB (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (x : Matrix T dIn ℝ) (t : T) (o : dOut) :
    fderiv ℝ (fun q : ParamsB (Arch.gated (T := T) (d := d) σ id hid) dIn dOut =>
        evalB (Arch.gated σ id hid) 0 q.1 q.2 x) p η t o
      = dγm_gbi p.1 p.2 η.1 η.2 o + ∑ i : hid 0,
        (σ ((x * Cm_gbi p.1) t (Sum.inl i) + βm_gbi p.1 p.2 (Sum.inl i))
            * ((x * Cm_gbi p.1) t (Sum.inr i) + βm_gbi p.1 p.2 (Sum.inr i))
            * dAm_gbi p.1 η.1 i o
          + σ' ((x * Cm_gbi p.1) t (Sum.inl i) + βm_gbi p.1 p.2 (Sum.inl i))
            * ((x * dCm_gbi p.1 η.1) t (Sum.inl i) + dβm_gbi p.1 p.2 η.1 η.2 (Sum.inl i))
            * ((x * Cm_gbi p.1) t (Sum.inr i) + βm_gbi p.1 p.2 (Sum.inr i)) * Am_gbi p.1 i o
          + σ ((x * Cm_gbi p.1) t (Sum.inl i) + βm_gbi p.1 p.2 (Sum.inl i))
            * ((x * dCm_gbi p.1 η.1) t (Sum.inr i) + dβm_gbi p.1 p.2 η.1 η.2 (Sum.inr i))
            * Am_gbi p.1 i o) := by
  have hdiff := differentiable_evalB (A := Arch.gated (T := T) (d := d) σ id hid) (S := 0)
    (dIn := dIn) (dOut := dOut)
    (fun ℓ => differentiable_f_gated (fun z => (hσ z).differentiableAt) ℓ) differentiable_id x
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
  refine h2.unique ?_
  -- the same derivative computed entrywise: products and sums of real functions of `τ`
  show HasDerivAt (fun τ : ℝ =>
    evalB (Arch.gated σ id hid) 0 (p.1 + τ • η.1) (p.2 + τ • η.2) x t o) _ 0
  rw [funext fun τ => evalB_line_apply_gbi p.1 η.1 p.2 η.2 x t o τ]
  refine (hasDerivAt_quad _ _ _).add (HasDerivAt.fun_sum fun i _ => ?_)
  have hu := (hasDerivAt_quad ((x * Cm_gbi p.1) t (Sum.inl i))
    ((x * dCm_gbi p.1 η.1) t (Sum.inl i)) ((x * Cm_gbi η.1) t (Sum.inl i))).add
    (hasDerivAt_quad (βm_gbi p.1 p.2 (Sum.inl i)) (dβm_gbi p.1 p.2 η.1 η.2 (Sum.inl i))
      ((η.2.E ᵥ* rd_gbi η.1) (Sum.inl i)))
  have hw := (hasDerivAt_quad ((x * Cm_gbi p.1) t (Sum.inr i))
    ((x * dCm_gbi p.1 η.1) t (Sum.inr i)) ((x * Cm_gbi η.1) t (Sum.inr i))).add
    (hasDerivAt_quad (βm_gbi p.1 p.2 (Sum.inr i)) (dβm_gbi p.1 p.2 η.1 η.2 (Sum.inr i))
      ((η.2.E ᵥ* rd_gbi η.1) (Sum.inr i)))
  have hv := hasDerivAt_quad (Am_gbi p.1 i o) (dAm_gbi p.1 η.1 i o) (Am_gbi η.1 i o)
  have h := (((hσ _).comp (0 : ℝ) hu).mul hw).mul hv
  convert h using 1
  · rfl
  · simp only [Pi.mul_apply, Pi.add_apply, Function.comp_apply, zero_mul, mul_zero, add_zero]
    ring

/-! ### Helpers: the derivatives of `C`, `A`, `β` and `γ_0` along a rescaling -/

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: `∂C` is linear in the direction. -/
private theorem dCm_sub_gbi (θ η ρ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) :
    dCm_gbi θ (η - ρ) = dCm_gbi θ η - dCm_gbi θ ρ := by
  show (η.E - ρ.E) * rd_gbi θ + θ.E * (rd_gbi η - rd_gbi ρ)
    = (η.E * rd_gbi θ + θ.E * rd_gbi η) - (ρ.E * rd_gbi θ + θ.E * rd_gbi ρ)
  rw [Matrix.sub_mul, Matrix.mul_sub]
  abel

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: `∂A` is linear in the direction. -/
private theorem dAm_sub_gbi (θ η ρ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) :
    dAm_gbi θ (η - ρ) = dAm_gbi θ η - dAm_gbi θ ρ := by
  show (wr_gbi η - wr_gbi ρ) * θ.D + wr_gbi θ * (η.D - ρ.D)
    = (wr_gbi η * θ.D + wr_gbi θ * η.D) - (wr_gbi ρ * θ.D + wr_gbi θ * ρ.D)
  rw [Matrix.sub_mul, Matrix.mul_sub]
  abel

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: `∂β` is linear in the direction. -/
private theorem dβm_sub_gbi (θ η ρ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (b ηb ρb : Biases (Arch.gated (T := T) (d := d) σ id hid) dOut) :
    dβm_gbi θ b (η - ρ) (ηb - ρb) = dβm_gbi θ b η ηb - dβm_gbi θ b ρ ρb := by
  show (ηb.E - ρb.E) ᵥ* rd_gbi θ + b.E ᵥ* (rd_gbi η - rd_gbi ρ) + (ηb.read 0 - ρb.read 0)
    = (ηb.E ᵥ* rd_gbi θ + b.E ᵥ* rd_gbi η + ηb.read 0)
      - (ρb.E ᵥ* rd_gbi θ + b.E ᵥ* rd_gbi ρ + ρb.read 0)
  rw [Matrix.sub_vecMul, Matrix.vecMul_sub]
  abel

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: `∂γ_0` is linear in the direction. -/
private theorem dγm_sub_gbi (θ η ρ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (b ηb ρb : Biases (Arch.gated (T := T) (d := d) σ id hid) dOut) :
    dγm_gbi θ b (η - ρ) (ηb - ρb) = dγm_gbi θ b η ηb - dγm_gbi θ b ρ ρb := by
  show (ηb.write 0 - ρb.write 0) ᵥ* θ.D + b.write 0 ᵥ* (η.D - ρ.D) + (ηb.D - ρb.D)
    = (ηb.write 0 ᵥ* θ.D + b.write 0 ᵥ* η.D + ηb.D)
      - (ρb.write 0 ᵥ* θ.D + b.write 0 ᵥ* ρ.D + ρb.D)
  rw [Matrix.sub_vecMul, Matrix.vecMul_sub]
  abel

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: along a rescaling, the gate columns of `C` do not move. -/
private theorem dCm_rescale_inl_gbi
    (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) (α : ∀ ℓ, hid ℓ → ℝ)
    (a : dIn) (i : hid 0) :
    dCm_gbi θ (rescaleDir θ α) a (Sum.inl i) = 0 := by
  show ((0 : Matrix dIn d ℝ) * rd_gbi θ + θ.E * rd_gbi (rescaleDir θ α)) a (Sum.inl i) = 0
  rw [Matrix.zero_mul, zero_add, Matrix.mul_apply]
  exact Finset.sum_eq_zero fun k _ => mul_eq_zero_of_right _ rfl

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: along a rescaling, the value column `e_i` of `C` moves by `-α_i e_i`. -/
private theorem dCm_rescale_inr_gbi
    (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) (α : ∀ ℓ, hid ℓ → ℝ)
    (a : dIn) (i : hid 0) :
    dCm_gbi θ (rescaleDir θ α) a (Sum.inr i) = -(α 0 i) * Cm_gbi θ a (Sum.inr i) := by
  show ((0 : Matrix dIn d ℝ) * rd_gbi θ + θ.E * rd_gbi (rescaleDir θ α)) a (Sum.inr i)
    = -(α 0 i) * (θ.E * rd_gbi θ) a (Sum.inr i)
  rw [Matrix.zero_mul, zero_add, Matrix.mul_apply, Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  show θ.E a k * (-(α 0 i) * θ.read 0 k (Sum.inr i))
    = -(α 0 i) * (θ.E a k * θ.read 0 k (Sum.inr i))
  ring

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: along a rescaling, the row `a_i` of `A` moves by `α_i a_i`. -/
private theorem dAm_rescale_gbi
    (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) (α : ∀ ℓ, hid ℓ → ℝ)
    (i : hid 0) (o : dOut) :
    dAm_gbi θ (rescaleDir θ α) i o = α 0 i * Am_gbi θ i o := by
  show (wr_gbi (rescaleDir θ α) * θ.D + wr_gbi θ * (0 : Matrix d dOut ℝ)) i o
    = α 0 i * (wr_gbi θ * θ.D) i o
  rw [Matrix.mul_zero, add_zero, Matrix.mul_apply, Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  show α 0 i * θ.write 0 i k * θ.D k o = α 0 i * (θ.write 0 i k * θ.D k o)
  ring

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: a row vector times the read of a rescaling has no gate entries. -/
private theorem vecMul_rescale_inl_gbi
    (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) (α : ∀ ℓ, hid ℓ → ℝ)
    (v : d → ℝ) (i : hid 0) :
    (v ᵥ* rd_gbi (rescaleDir θ α)) (Sum.inl i) = 0 :=
  Finset.sum_eq_zero fun _ _ => mul_eq_zero_of_right _ rfl

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: a row vector times the read of a rescaling has the value entries times `-α_i`. -/
private theorem vecMul_rescale_inr_gbi
    (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) (α : ∀ ℓ, hid ℓ → ℝ)
    (v : d → ℝ) (i : hid 0) :
    (v ᵥ* rd_gbi (rescaleDir θ α)) (Sum.inr i) = -(α 0 i) * (v ᵥ* rd_gbi θ) (Sum.inr i) := by
  show ∑ k, v k * (-(α 0 i) * θ.read 0 k (Sum.inr i))
    = -(α 0 i) * ∑ k, v k * θ.read 0 k (Sum.inr i)
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: along a rescaling with biases, the gate biases `β_i` do not move. -/
private theorem dβm_rescale_inl_gbi
    (p : ParamsB (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) (α : ∀ ℓ, hid ℓ → ℝ)
    (i : hid 0) :
    dβm_gbi p.1 p.2 (rescaleDirB p α).1 (rescaleDirB p α).2 (Sum.inl i) = 0 := by
  show ((0 : d → ℝ) ᵥ* rd_gbi p.1) (Sum.inl i) + (p.2.E ᵥ* rd_gbi (rescaleDir p.1 α)) (Sum.inl i)
    + 0 = 0
  rw [Matrix.zero_vecMul, vecMul_rescale_inl_gbi, Pi.zero_apply, add_zero, add_zero]

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: along a rescaling with biases, the value bias `β'_i` moves by `-α_i β'_i`. -/
private theorem dβm_rescale_inr_gbi
    (p : ParamsB (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) (α : ∀ ℓ, hid ℓ → ℝ)
    (i : hid 0) :
    dβm_gbi p.1 p.2 (rescaleDirB p α).1 (rescaleDirB p α).2 (Sum.inr i)
      = -(α 0 i) * βm_gbi p.1 p.2 (Sum.inr i) := by
  show ((0 : d → ℝ) ᵥ* rd_gbi p.1) (Sum.inr i) + (p.2.E ᵥ* rd_gbi (rescaleDir p.1 α)) (Sum.inr i)
      + -(α 0 i) * p.2.read 0 (Sum.inr i)
    = -(α 0 i) * ((p.2.E ᵥ* rd_gbi p.1) (Sum.inr i) + p.2.read 0 (Sum.inr i))
  rw [Matrix.zero_vecMul, vecMul_rescale_inr_gbi, Pi.zero_apply, zero_add]
  ring

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: along a rescaling with biases, `γ_0` does not move. -/
private theorem dγm_rescale_gbi
    (p : ParamsB (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) (α : ∀ ℓ, hid ℓ → ℝ) :
    dγm_gbi p.1 p.2 (rescaleDirB p α).1 (rescaleDirB p α).2 = 0 := by
  show (0 : d → ℝ) ᵥ* p.1.D + p.2.write 0 ᵥ* (0 : Matrix d dOut ℝ) + 0 = 0
  rw [Matrix.zero_vecMul, Matrix.vecMul_zero, add_zero, add_zero]

omit [Fintype T] [Nonempty T] in
/-- Helper (the end of the proof of `flatB_le_range_mlp_skipless`): a direction that keeps `C`,
`A`, `β` and `γ_0` to first order is the direction of two changes of basis `X_0, X_1` and of the
translations `g_0 = ρ_{b_E} − b_E X_0`, `g_1 = ρ_{b_write} − b_write X_1`. -/
private theorem cobTrAt_of_keeps_gbi
    (p : ParamsB (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) (hp : OneBlockGenericGated p.1)
    (ρ : ParamsB (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (hC : dCm_gbi p.1 ρ.1 = 0) (hA : dAm_gbi p.1 ρ.1 = 0)
    (hβ : dβm_gbi p.1 p.2 ρ.1 ρ.2 = 0) (hγ : dγm_gbi p.1 p.2 ρ.1 ρ.2 = 0) :
    ∃ (X : Fin 2 → Matrix d d ℝ) (g : Fin 2 → d → ℝ),
      ρ = cobDirB p X + (0, translateAtDir p.1 g) := by
  -- Lemma C.2: a direction that keeps `C` and `A` moves the weights by two changes of basis
  obtain ⟨X, hX⟩ := (keeps_products_iff_mem_range_cobDir p.1 ρ.1 hp.rank_E hp.rank_D
    hp.rank_read hp.rank_write).1 ⟨hC, hA⟩
  have hR : ρ.1.read 0 = -(X 0 * p.1.read 0) := by rw [hX]; rfl
  have hD : ρ.1.D = -(X 1 * p.1.D) := by rw [hX]; rfl
  -- `∂β = 0`: `ρ_{b_read} = −g_0 W_read` with `g_0 = ρ_{b_E} − b_E X_0`
  have hbR : ρ.2.read 0 = -((ρ.2.E - p.2.E ᵥ* X 0) ᵥ* p.1.read 0) := by
    have h : ρ.2.E ᵥ* p.1.read 0 + p.2.E ᵥ* ρ.1.read 0 + ρ.2.read 0 = 0 := hβ
    rw [hR, Matrix.vecMul_neg, ← Matrix.vecMul_vecMul] at h
    rw [Matrix.sub_vecMul]
    linear_combination h
  -- `∂γ_0 = 0`: `ρ_{b_D} = −g_1 D` with `g_1 = ρ_{b_write} − b_write X_1`
  have hbD : ρ.2.D = -((ρ.2.write 0 - p.2.write 0 ᵥ* X 1) ᵥ* p.1.D) := by
    have h : ρ.2.write 0 ᵥ* p.1.D + p.2.write 0 ᵥ* ρ.1.D + ρ.2.D = 0 := hγ
    rw [hD, Matrix.vecMul_neg, ← Matrix.vecMul_vecMul] at h
    rw [Matrix.sub_vecMul]
    linear_combination h
  -- so `ρ` is the direction of the changes of basis `X` and of the translations `g_0, g_1`
  refine ⟨X, ![ρ.2.E - p.2.E ᵥ* X 0, ρ.2.write 0 - p.2.write 0 ᵥ* X 1], ?_⟩
  refine Prod.ext ?_ ?_
  · show ρ.1 = cobDir p.1 X + 0
    rw [add_zero]
    exact hX
  · apply Biases.ext'
    · show ρ.2.E = p.2.E ᵥ* X 0 + (ρ.2.E - p.2.E ᵥ* X 0)
      abel
    · intro ℓ
      obtain rfl : ℓ = 0 := Subsingleton.elim ℓ 0
      show ρ.2.read 0 = 0 + -((ρ.2.E - p.2.E ᵥ* X 0) ᵥ* p.1.read 0)
      rw [zero_add]
      exact hbR
    · intro ℓ
      obtain rfl : ℓ = 0 := Subsingleton.elim ℓ 0
      show ρ.2.write 0 = p.2.write 0 ᵥ* X 1 + (ρ.2.write 0 - p.2.write 0 ᵥ* X 1)
      abel
    · show ρ.2.D = 0 + -((ρ.2.write 0 - p.2.write 0 ᵥ* X 1) ᵥ* p.1.D)
      rw [zero_add]
      exact hbD

/-- **Lemma B.2 with biases, after Lemma B.3, for one skipless SwiGLU or GeGLU block:** under the
conditions `OneBlockGenericGated` on the weights, every flat direction of the skipless network
with biases is the sum of the direction of changes of basis `X_0, X_1` and translations
`g_0, g_1` of the two hidden states and of a direction of the rescalings of the values. -/
theorem flatB_le_range_gated_skipless (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hU : GatedUnitsRescale σ σ' dIn dOut (hid 0))
    (p : ParamsB (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (hp : OneBlockGenericGated p.1)
    (η : ParamsB (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (hη : η ∈ flatB (Arch.gated σ id hid) 0 p) :
    ∃ (X : Fin 2 → Matrix d d ℝ) (g : Fin 2 → d → ℝ) (α : ∀ ℓ, hid ℓ → ℝ),
      η = cobDirB p X + (0, translateAtDir p.1 g) + rescaleDirB p α := by
  -- the derivative of `F(θ, b, x)` along `η` vanishes at every input, entry by entry
  have hzero : ∀ (x : Matrix T dIn ℝ) (t : T) (o : dOut), dγm_gbi p.1 p.2 η.1 η.2 o
      + ∑ i : hid 0,
        (σ ((x * Cm_gbi p.1) t (Sum.inl i) + βm_gbi p.1 p.2 (Sum.inl i))
            * ((x * Cm_gbi p.1) t (Sum.inr i) + βm_gbi p.1 p.2 (Sum.inr i))
            * dAm_gbi p.1 η.1 i o
          + σ' ((x * Cm_gbi p.1) t (Sum.inl i) + βm_gbi p.1 p.2 (Sum.inl i))
            * ((x * dCm_gbi p.1 η.1) t (Sum.inl i) + dβm_gbi p.1 p.2 η.1 η.2 (Sum.inl i))
            * ((x * Cm_gbi p.1) t (Sum.inr i) + βm_gbi p.1 p.2 (Sum.inr i)) * Am_gbi p.1 i o
          + σ ((x * Cm_gbi p.1) t (Sum.inl i) + βm_gbi p.1 p.2 (Sum.inl i))
            * ((x * dCm_gbi p.1 η.1) t (Sum.inr i) + dβm_gbi p.1 p.2 η.1 η.2 (Sum.inr i))
            * Am_gbi p.1 i o) = 0 := by
    intro x t o
    rw [← fderiv_evalB_apply_gbi hσ p η x t o]
    have h := LinearMap.mem_ker.1 ((Submodule.mem_iInf _).1 hη x)
    exact congrFun (congrFun h t) o
  -- Lemma B.3 (inputs `x` with all rows equal to `v`, `ψ_M = 0`): `∂γ_0 = 0`, the gate columns
  -- and the gate biases do not move, and every unit only rescales its value,
  -- `∂(e_i, β'_i) = −α_i (e_i, β'_i)`, `∂a_i = α_i a_i`
  obtain ⟨-, hγ, hc, hβ, α, hα⟩ := hU (fun i => (Cm_gbi p.1)ᵀ (Sum.inl i))
    (fun i => βm_gbi p.1 p.2 (Sum.inl i)) (fun i => (Cm_gbi p.1)ᵀ (Sum.inr i))
    (fun i => βm_gbi p.1 p.2 (Sum.inr i)) (fun i => Am_gbi p.1 i) 0 (dγm_gbi p.1 p.2 η.1 η.2)
    (fun i => (dCm_gbi p.1 η.1)ᵀ (Sum.inl i)) (fun i => dβm_gbi p.1 p.2 η.1 η.2 (Sum.inl i))
    (fun i => (dCm_gbi p.1 η.1)ᵀ (Sum.inr i)) (fun i => dβm_gbi p.1 p.2 η.1 η.2 (Sum.inr i))
    (fun i => dAm_gbi p.1 η.1 i) (fun i => hp.row_ne_zero i) (fun i => hp.gate_ne_zero i)
    (fun i j hij => hp.gate_not_collinear i j hij) (fun i => hp.value_ne_zero i) (by
      intro v
      funext o
      have h := hzero (Matrix.of fun _ => v) (Classical.arbitrary T) o
      simp only [Matrix.vecMul_zero, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        Pi.zero_apply, zero_add]
      exact h)
  -- the rescaling with these `α_i` (one block: `ℓ = 0`)
  let α' : ∀ ℓ : Fin 1, hid ℓ → ℝ := fun ℓ => Fin.cases α (fun l => l.elim0) ℓ
  -- `η − rescaleDirB p α` keeps `C`, `A`, `β` and `γ_0` to first order
  have hC : dCm_gbi p.1 (η.1 - rescaleDir p.1 α') = 0 := by
    ext a j
    rcases j with i | i
    · rw [dCm_sub_gbi, Matrix.sub_apply, dCm_rescale_inl_gbi, sub_zero]
      exact congrFun (congrFun hc i) a
    · rw [dCm_sub_gbi, Matrix.sub_apply, dCm_rescale_inr_gbi, Matrix.zero_apply, sub_eq_zero]
      exact congrFun (hα i).1 a
  have hA : dAm_gbi p.1 (η.1 - rescaleDir p.1 α') = 0 := by
    ext i o
    rw [dAm_sub_gbi, Matrix.sub_apply, dAm_rescale_gbi, Matrix.zero_apply, sub_eq_zero]
    exact congrFun (hα i).2.2 o
  have hβ' : dβm_gbi p.1 p.2 (η.1 - (rescaleDirB p α').1) (η.2 - (rescaleDirB p α').2) = 0 := by
    funext j
    rcases j with i | i
    · rw [dβm_sub_gbi, Pi.sub_apply, dβm_rescale_inl_gbi, sub_zero]
      exact congrFun hβ i
    · rw [dβm_sub_gbi, Pi.sub_apply, dβm_rescale_inr_gbi, Pi.zero_apply, sub_eq_zero]
      exact (hα i).2.1
  have hγ' : dγm_gbi p.1 p.2 (η.1 - (rescaleDirB p α').1) (η.2 - (rescaleDirB p α').2) = 0 := by
    rw [dγm_sub_gbi, dγm_rescale_gbi, sub_zero]
    exact hγ
  -- Lemma C.2 and Lemma B.2 with biases: `η − rescaleDirB p α` is a direction of changes of
  -- basis and translations
  obtain ⟨X, g, hX⟩ := cobTrAt_of_keeps_gbi p hp (η - rescaleDirB p α') hC hA hβ' hγ'
  exact ⟨X, g, α', sub_eq_iff_eq_add.1 hX⟩

/-! ### Helpers: the directions of the changes of basis, translations and rescalings, as linear
maps -/

omit [Fintype T] [Nonempty T] in
/-- Helper: `(X, g) ↦ cobDirB p X + (0, translateAtDir θ g)`, as a linear map. -/
private noncomputable def cobTrAtLin_gbi {L : ℕ} {A : Arch T d L} (p : ParamsB A dIn dOut) :
    (Fin (L + 1) → Matrix d d ℝ) × (Fin (L + 1) → d → ℝ) →ₗ[ℝ] ParamsB A dIn dOut where
  toFun Xg := cobDirB p Xg.1 + (0, translateAtDir p.1 Xg.2)
  map_add' Xg Yg := by
    refine Prod.ext ?_ ?_
    · show cobDir p.1 (Xg.1 + Yg.1) + 0 = cobDir p.1 Xg.1 + 0 + (cobDir p.1 Yg.1 + 0)
      rw [add_zero, add_zero, add_zero]
      exact (cobDirLin p.1).map_add Xg.1 Yg.1
    · apply Biases.ext' <;> intros <;>
        simp only [cobDirB, translateAtDir, Prod.snd_add, Biases.add_E, Biases.add_read,
          Biases.add_write, Biases.add_D, Prod.fst_add, Prod.snd_add, Pi.add_apply,
          Matrix.vecMul_add, Matrix.add_vecMul, neg_add, zero_add] <;> abel
  map_smul' c Xg := by
    refine Prod.ext ?_ ?_
    · show cobDir p.1 (c • Xg.1) + 0 = c • (cobDir p.1 Xg.1 + 0)
      rw [add_zero, add_zero]
      exact (cobDirLin p.1).map_smul c Xg.1
    · apply Biases.ext' <;> intros <;>
        simp only [cobDirB, translateAtDir, Prod.smul_snd, Prod.smul_fst, Biases.smul_E,
          Biases.smul_read, Biases.smul_write, Biases.smul_D, Biases.add_E, Biases.add_read,
          Biases.add_write, Biases.add_D, Prod.snd_add, Pi.smul_apply, Matrix.vecMul_smul,
          Matrix.smul_vecMul, smul_neg, smul_add, smul_zero, zero_add, RingHom.id_apply]

omit [Fintype T] [Nonempty T] in
/-- Helper: `(X, g) ↦ cobDirB p (X, …, X) + (0, translateDir θ g)`, as a linear map. -/
private noncomputable def cobTrLin_gbi {L : ℕ} {A : Arch T d L} (p : ParamsB A dIn dOut) :
    Matrix d d ℝ × (Fin (L + 1) → d → ℝ) →ₗ[ℝ] ParamsB A dIn dOut where
  toFun Xg := cobDirB p (fun _ => Xg.1) + (0, translateDir p.1 Xg.2)
  map_add' Xg Yg := by
    refine Prod.ext ?_ ?_
    · show cobDir p.1 (fun _ => Xg.1 + Yg.1) + 0
        = cobDir p.1 (fun _ => Xg.1) + 0 + (cobDir p.1 (fun _ => Yg.1) + 0)
      rw [add_zero, add_zero, add_zero]
      exact (cobDirLin p.1).map_add (fun _ => Xg.1) (fun _ => Yg.1)
    · apply Biases.ext' <;> intros <;>
        simp only [cobDirB, translateDir, Prod.snd_add, Biases.add_E, Biases.add_read,
          Biases.add_write, Biases.add_D, Prod.fst_add, Prod.snd_add, Pi.add_apply,
          Finset.sum_add_distrib, Matrix.vecMul_add, Matrix.add_vecMul, neg_add,
          zero_add] <;> abel
  map_smul' c Xg := by
    refine Prod.ext ?_ ?_
    · show cobDir p.1 (fun _ => c • Xg.1) + 0 = c • (cobDir p.1 (fun _ => Xg.1) + 0)
      rw [add_zero, add_zero]
      exact (cobDirLin p.1).map_smul c (fun _ => Xg.1)
    · apply Biases.ext' <;> intros <;>
        simp only [cobDirB, translateDir, Prod.smul_snd, Prod.smul_fst, Biases.smul_E,
          Biases.smul_read, Biases.smul_write, Biases.smul_D, Biases.add_E, Biases.add_read,
          Biases.add_write, Biases.add_D, Prod.snd_add, Pi.smul_apply, ← Finset.smul_sum,
          Matrix.vecMul_smul, Matrix.smul_vecMul, smul_neg, smul_add, smul_zero, zero_add,
          RingHom.id_apply]

/-- Helper (the private `rescaleDirLin` of `OneBlock/Gated.lean`): `α ↦ rescaleDir θ α` is
linear. -/
private noncomputable def rescaleDirLin_gbi
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

/-- Helper: `α ↦ rescaleDirB p α` is linear. -/
private noncomputable def rescaleDirBLin_gbi
    (p : ParamsB (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) :
    (∀ ℓ : Fin 1, hid ℓ → ℝ) →ₗ[ℝ] ParamsB (Arch.gated (T := T) (d := d) σ id hid) dIn dOut where
  toFun := rescaleDirB p
  map_add' α β := by
    refine Prod.ext ?_ ?_
    · exact (rescaleDirLin_gbi p.1).map_add α β
    · apply Biases.ext'
      · exact (add_zero 0).symm
      · intro ℓ
        funext j
        rcases j with i | i
        · exact (add_zero 0).symm
        · show -((α + β) ℓ i) * p.2.read ℓ (Sum.inr i)
            = -(α ℓ i) * p.2.read ℓ (Sum.inr i) + -(β ℓ i) * p.2.read ℓ (Sum.inr i)
          rw [Pi.add_apply, Pi.add_apply]
          ring
      · intro ℓ
        exact (add_zero 0).symm
      · exact (add_zero 0).symm
  map_smul' c α := by
    refine Prod.ext ?_ ?_
    · exact (rescaleDirLin_gbi p.1).map_smul c α
    · apply Biases.ext'
      · exact (smul_zero c).symm
      · intro ℓ
        funext j
        rcases j with i | i
        · exact (smul_zero c).symm
        · show -((c • α) ℓ i) * p.2.read ℓ (Sum.inr i) = c * (-(α ℓ i) * p.2.read ℓ (Sum.inr i))
          rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul]
          ring
      · intro ℓ
        exact (smul_zero c).symm
      · exact (smul_zero c).symm

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the pairs `(X, g)` of `L + 1` changes of basis and `L + 1` translations form a space
of dimension `(L + 1) d² + (L + 1) d`. -/
private theorem finrank_cobTrAtDomain_gbi (L : ℕ) :
    Module.finrank ℝ ((Fin (L + 1) → Matrix d d ℝ) × (Fin (L + 1) → d → ℝ))
      = (L + 1) * Fintype.card d ^ 2 + (L + 1) * Fintype.card d := by
  rw [Module.finrank_prod, finrank_cobDomain, Module.finrank_pi_fintype]
  simp only [Module.finrank_fintype_fun_eq_card, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul]

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the pairs `(X, g)` of one change of basis and `L + 1` translations form a space of
dimension `d² + (L + 1) d`. -/
private theorem finrank_cobTrDomain_gbi (L : ℕ) :
    Module.finrank ℝ (Matrix d d ℝ × (Fin (L + 1) → d → ℝ))
      = Fintype.card d ^ 2 + (L + 1) * Fintype.card d := by
  rw [Module.finrank_prod, Module.finrank_matrix, Module.finrank_pi_fintype]
  simp only [Module.finrank_self, Module.finrank_fintype_fun_eq_card, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one, sq]

/-- Helper: the numbers `α_i`, one per hidden unit, form a space of dimension `d_hidden`. -/
private theorem finrank_rescaleDomain_gbi :
    Module.finrank ℝ (∀ ℓ : Fin 1, hid ℓ → ℝ) = Fintype.card (hid 0) := by
  rw [Module.finrank_pi_fintype]
  simp only [Module.finrank_fintype_fun_eq_card, Finset.univ_unique, Fin.default_eq_zero,
    Finset.sum_singleton]

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the triples `(X, g, α)` of two changes of basis, two translations and one number per
hidden unit form a space of dimension `2 d² + 2 d + d_hidden`. -/
private theorem finrank_dirAtDomain_gbi :
    Module.finrank ℝ (((Fin (1 + 1) → Matrix d d ℝ) × (Fin (1 + 1) → d → ℝ))
        × (∀ ℓ : Fin 1, hid ℓ → ℝ))
      = (1 + 1) * Fintype.card d ^ 2 + (1 + 1) * Fintype.card d + Fintype.card (hid 0) := by
  rw [Module.finrank_prod, finrank_cobTrAtDomain_gbi 1, finrank_rescaleDomain_gbi]

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the triples `(X, g, α)` of one change of basis, two translations and one number per
hidden unit form a space of dimension `d² + 2 d + d_hidden`. -/
private theorem finrank_dirDomain_gbi :
    Module.finrank ℝ ((Matrix d d ℝ × (Fin (1 + 1) → d → ℝ)) × (∀ ℓ : Fin 1, hid ℓ → ℝ))
      = Fintype.card d ^ 2 + (1 + 1) * Fintype.card d + Fintype.card (hid 0) := by
  rw [Module.finrank_prod, finrank_cobTrDomain_gbi 1, finrank_rescaleDomain_gbi]

/-- **Theorem B.1 (i) of the skips paper with biases, the skipless network, at one parameter, for
a SwiGLU or GeGLU block:** under the conditions `OneBlockGenericGated` on the weights, the
skipless network with biases has `fd = P − 2 d² − 2 d − d_hidden`, with `P` counting the
biases. -/
theorem funDimB_gated_oneBlock (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hU : GatedUnitsRescale σ σ' dIn dOut (hid 0))
    (p : ParamsB (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (hp : OneBlockGenericGated p.1) :
    funDimB (Arch.gated σ id hid) 0 p
        + (2 * Fintype.card d ^ 2 + 2 * Fintype.card d + Fintype.card (hid 0))
      = Module.finrank ℝ (ParamsB (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) := by
  have hσd : Differentiable ℝ σ := fun z => (hσ z).differentiableAt
  have hf : ∀ ℓ, Differentiable ℝ ((Arch.gated (T := T) (d := d) σ id hid).f ℓ) :=
    fun ℓ => differentiable_f_gated hσd ℓ
  have hdiff : ∀ x : Matrix T dIn ℝ, DifferentiableAt ℝ
      (fun q : ParamsB (Arch.gated (T := T) (d := d) σ id hid) dIn dOut =>
        evalB (Arch.gated σ id hid) 0 q.1 q.2 x) p := fun x =>
    differentiable_evalB (A := Arch.gated (T := T) (d := d) σ id hid) (S := 0) hf
      differentiable_id x p
  -- no value column of `W_read` vanishes, since the value columns of `C = E W_read` do not
  have hv : ∀ ℓ i, (fun a => p.1.read ℓ a (Sum.inr i)) ≠ 0 := by
    intro ℓ i h0
    obtain rfl := Subsingleton.elim ℓ 0
    apply hp.value_ne_zero i
    funext a
    show ∑ k, p.1.E a k * p.1.read 0 k (Sum.inr i) = 0
    exact Finset.sum_eq_zero fun k _ => by
      rw [show p.1.read 0 k (Sum.inr i) = 0 from congrFun h0 k, mul_zero]
  -- `≤`: the changes of basis, the translations and the rescalings are flat and independent
  -- (Lemma A.8 with `s = d_hidden`)
  have hle := funDimB_add_le_skipless_gated p hp.rank_E (fun ℓ => by
    obtain rfl := Subsingleton.elim ℓ 0
    exact hp.rank_write) hv
  have hs : ∑ ℓ : Fin 1, Fintype.card (hid ℓ) = Fintype.card (hid 0) := Fin.sum_univ_one _
  -- `≥`: every flat direction is one of them (the first theorem), and they span a space of
  -- dimension at most `2 d² + 2 d + d_hidden`
  let Φ := (cobTrAtLin_gbi p).coprod (rescaleDirBLin_gbi p)
  have hflat : flatB (Arch.gated σ id hid) 0 p ≤ LinearMap.range Φ := by
    intro η hη
    obtain ⟨X, g, α, rfl⟩ := flatB_le_range_gated_skipless hσ hU p hp η hη
    exact LinearMap.mem_range.2 ⟨((X, g), α), rfl⟩
  have h1 := Submodule.finrank_mono hflat
  have h2 := (LinearMap.finrank_range_le Φ).trans_eq (finrank_dirAtDomain_gbi (d := d))
  -- `fd(θ, b) = P − dim K(θ, b)`
  have h3 := funDimB_add_finrank_flatB p hdiff
  omega

/-! ### Helpers: the residual network with biases and its derivative -/

omit [Fintype T] [Nonempty T] [Fintype dIn] [Fintype dOut] in
/-- Helper: a matrix whose rank is its number of columns cancels on the left, via a left
inverse. -/
private theorem cancel_left_of_rank_gbi {m n k : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (M : Matrix m n ℝ) (hM : M.rank = Fintype.card n) {X Y : Matrix n k ℝ}
    (h : M * X = M * Y) : X = Y := by
  obtain ⟨B, hB⟩ := Matrix.vecMul_surjective_iff_exists_left_inverse.mp
    (Matrix.vecMul_surjective_iff_rank_eq_card.mpr hM)
  have := congrArg (B * ·) h
  simpa only [← Matrix.mul_assoc, hB, Matrix.one_mul] using this

omit [Fintype T] [Nonempty T] [Fintype dIn] [Fintype dOut] in
/-- Helper: a matrix whose rank is its number of rows cancels on the right, via a right
inverse. -/
private theorem cancel_right_of_rank_gbi {m n k : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    (M : Matrix m n ℝ) (hM : M.rank = Fintype.card m) {X Y : Matrix k m ℝ}
    (h : X * M = Y * M) : X = Y := by
  obtain ⟨R, hR⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.mp
    (Matrix.mulVec_surjective_iff_rank_eq_card.mpr hM)
  have := congrArg (· * R) h
  simpa only [Matrix.mul_assoc, hR, Matrix.mul_one] using this

/-- Helper: `M = E D`, the linear part of the residual network. -/
private def Mm_gbi (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) :
    Matrix dIn dOut ℝ :=
  θ.E * θ.D

/-- Helper: the derivative `∂M = η_E D + E η_D` of `M` along `η`. -/
private def dMm_gbi (θ η : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) :
    Matrix dIn dOut ℝ :=
  η.E * θ.D + θ.E * η.D

/-- Helper: `γ = b_E D + γ_0`. -/
private def γr_gbi (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (b : Biases (Arch.gated (T := T) (d := d) σ id hid) dOut) : dOut → ℝ :=
  b.E ᵥ* θ.D + γm_gbi θ b

/-- Helper: the derivative `∂γ = η_{b_E} D + b_E η_D + ∂γ_0` of `γ`. -/
private def dγr_gbi (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (b : Biases (Arch.gated (T := T) (d := d) σ id hid) dOut)
    (η : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (ηb : Biases (Arch.gated (T := T) (d := d) σ id hid) dOut) : dOut → ℝ :=
  ηb.E ᵥ* θ.D + b.E ᵥ* η.D + dγm_gbi θ b η ηb

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: along the line, `M(τ) = M + τ ∂M + τ² η_E η_D`. -/
private theorem Mm_line_gbi (θ η : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (τ : ℝ) :
    Mm_gbi (θ + τ • η) = Mm_gbi θ + τ • dMm_gbi θ η + (τ * τ) • Mm_gbi η := by
  simp only [Mm_gbi, dMm_gbi, Params.add_E, Params.smul_E, Params.add_D, Params.smul_D,
    Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, smul_add, smul_smul]
  abel

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: along the line, `γ(τ) = γ + τ ∂γ + τ² (η_{b_E} + η_{b_write}) η_D`. -/
private theorem γr_line_gbi (θ η : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (b ηb : Biases (Arch.gated (T := T) (d := d) σ id hid) dOut) (τ : ℝ) :
    γr_gbi (θ + τ • η) (b + τ • ηb)
      = γr_gbi θ b + τ • dγr_gbi θ b η ηb
        + (τ * τ) • (ηb.E ᵥ* η.D + ηb.write 0 ᵥ* η.D) := by
  simp only [γr_gbi, dγr_gbi, γm_line_gbi, Params.add_D, Params.smul_D, Biases.add_E,
    Biases.smul_E, Matrix.vecMul_add, Matrix.add_vecMul, Matrix.vecMul_smul, Matrix.smul_vecMul,
    smul_add, smul_smul]
  abel

omit [Fintype T] [Nonempty T] [Fintype dOut] in
/-- Helper: the residual network with biases,
`F(θ, x) = x M + γ + (σ(x C_g + β) ⊙ (x C_v + β')) A` (stream matrix `1`). -/
private theorem evalB_gated_res_eq_gbi
    (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (b : Biases (Arch.gated (T := T) (d := d) σ id hid) dOut) (x : Matrix T dIn ℝ) :
    evalB (Arch.gated σ id hid) 1 θ b x
      = x * Mm_gbi θ + (Matrix.of fun _ : T => γr_gbi θ b)
        + (Matrix.of fun t i => σ ((x * Cm_gbi θ) t (Sum.inl i) + βm_gbi θ b (Sum.inl i))
          * ((x * Cm_gbi θ) t (Sum.inr i) + βm_gbi θ b (Sum.inr i))) * Am_gbi θ := by
  have h1 : (Fin.last 1 : Fin 2) = (0 : Fin 1).succ := rfl
  have hχ : (Arch.gated (T := T) (d := d) σ id hid).χ = id := rfl
  have hf : (Arch.gated (T := T) (d := d) σ id hid).f 0
      = fun M => Matrix.of fun t i => σ (M t (Sum.inl i)) * M t (Sum.inr i) := rfl
  -- `h_1 = h_0 1 + f(h_0 W_read + b_read) W_write + b_write` with `h_0 = x E + b_E`
  rw [evalB, h1, hiddenB_succ, Fin.castSucc_zero, hiddenB_zero, hχ, hf]
  simp only [Pi.one_apply, Matrix.mul_one, id_eq, Matrix.add_mul, Matrix.mul_assoc,
    of_const_mul_gbi, Mm_gbi, Cm_gbi, Am_gbi, rd_gbi, wr_gbi, γr_gbi, γm_gbi, βm_gbi]
  rw [add_assoc (x * (θ.E * θ.read 0)), of_const_add_gbi]
  ext t o
  simp only [Matrix.add_apply, Matrix.of_apply, Pi.add_apply]
  ring

omit [Fintype T] [Nonempty T] [Fintype dOut] in
/-- Helper: the entries of `F(θ, x)` of the residual network,
`(x M)_{t o} + γ_o + ∑_i σ(z_i) w_i A_{i o}`. -/
private theorem evalB_gated_res_apply_gbi
    (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (b : Biases (Arch.gated (T := T) (d := d) σ id hid) dOut) (x : Matrix T dIn ℝ) (t : T)
    (o : dOut) :
    evalB (Arch.gated σ id hid) 1 θ b x t o
      = (x * Mm_gbi θ) t o + γr_gbi θ b o
        + ∑ i : hid 0, σ ((x * Cm_gbi θ) t (Sum.inl i) + βm_gbi θ b (Sum.inl i))
          * ((x * Cm_gbi θ) t (Sum.inr i) + βm_gbi θ b (Sum.inr i)) * Am_gbi θ i o := by
  rw [evalB_gated_res_eq_gbi]
  rfl

omit [Fintype T] [Nonempty T] [Fintype dOut] in
/-- Helper: the entries of `F(θ + τ η, b + τ η_b)(x)` of the residual network as functions of
`τ`. -/
private theorem evalB_res_line_apply_gbi
    (θ η : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (b ηb : Biases (Arch.gated (T := T) (d := d) σ id hid) dOut) (x : Matrix T dIn ℝ) (t : T)
    (o : dOut) (τ : ℝ) :
    evalB (Arch.gated σ id hid) 1 (θ + τ • η) (b + τ • ηb) x t o
      = ((x * Mm_gbi θ) t o + τ * (x * dMm_gbi θ η) t o + τ * τ * (x * Mm_gbi η) t o)
        + (γr_gbi θ b o + τ * dγr_gbi θ b η ηb o
          + τ * τ * (ηb.E ᵥ* η.D + ηb.write 0 ᵥ* η.D) o)
        + ∑ i : hid 0,
          σ (((x * Cm_gbi θ) t (Sum.inl i) + τ * (x * dCm_gbi θ η) t (Sum.inl i)
                + τ * τ * (x * Cm_gbi η) t (Sum.inl i))
              + (βm_gbi θ b (Sum.inl i) + τ * dβm_gbi θ b η ηb (Sum.inl i)
                + τ * τ * (ηb.E ᵥ* rd_gbi η) (Sum.inl i)))
            * (((x * Cm_gbi θ) t (Sum.inr i) + τ * (x * dCm_gbi θ η) t (Sum.inr i)
                + τ * τ * (x * Cm_gbi η) t (Sum.inr i))
              + (βm_gbi θ b (Sum.inr i) + τ * dβm_gbi θ b η ηb (Sum.inr i)
                + τ * τ * (ηb.E ᵥ* rd_gbi η) (Sum.inr i)))
            * (Am_gbi θ i o + τ * dAm_gbi θ η i o + τ * τ * Am_gbi η i o) := by
  rw [evalB_gated_res_apply_gbi, Mm_line_gbi, Cm_line_gbi, Am_line_gbi, βm_line_gbi,
    γr_line_gbi]
  simp only [Matrix.mul_add, Matrix.mul_smul]
  rfl

omit [Nonempty T] in
/-- Helper (the chain rule): the derivative of `(θ, b) ↦ F(θ, b, x)` of the residual network
along `η` has the entries `(x ∂M)_{t o} + ∂γ_o` plus those of the skipless network. -/
private theorem fderiv_evalB_res_apply_gbi (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (p η : ParamsB (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (x : Matrix T dIn ℝ) (t : T) (o : dOut) :
    fderiv ℝ (fun q : ParamsB (Arch.gated (T := T) (d := d) σ id hid) dIn dOut =>
        evalB (Arch.gated σ id hid) 1 q.1 q.2 x) p η t o
      = (x * dMm_gbi p.1 η.1) t o + dγr_gbi p.1 p.2 η.1 η.2 o + ∑ i : hid 0,
        (σ ((x * Cm_gbi p.1) t (Sum.inl i) + βm_gbi p.1 p.2 (Sum.inl i))
            * ((x * Cm_gbi p.1) t (Sum.inr i) + βm_gbi p.1 p.2 (Sum.inr i))
            * dAm_gbi p.1 η.1 i o
          + σ' ((x * Cm_gbi p.1) t (Sum.inl i) + βm_gbi p.1 p.2 (Sum.inl i))
            * ((x * dCm_gbi p.1 η.1) t (Sum.inl i) + dβm_gbi p.1 p.2 η.1 η.2 (Sum.inl i))
            * ((x * Cm_gbi p.1) t (Sum.inr i) + βm_gbi p.1 p.2 (Sum.inr i)) * Am_gbi p.1 i o
          + σ ((x * Cm_gbi p.1) t (Sum.inl i) + βm_gbi p.1 p.2 (Sum.inl i))
            * ((x * dCm_gbi p.1 η.1) t (Sum.inr i) + dβm_gbi p.1 p.2 η.1 η.2 (Sum.inr i))
            * Am_gbi p.1 i o) := by
  have hdiff := differentiable_evalB (A := Arch.gated (T := T) (d := d) σ id hid) (S := 1)
    (dIn := dIn) (dOut := dOut)
    (fun ℓ => differentiable_f_gated (fun z => (hσ z).differentiableAt) ℓ) differentiable_id x
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
  refine h2.unique ?_
  -- the same derivative computed entrywise: polynomials, products and sums of real functions
  show HasDerivAt (fun τ : ℝ =>
    evalB (Arch.gated σ id hid) 1 (p.1 + τ • η.1) (p.2 + τ • η.2) x t o) _ 0
  rw [funext fun τ => evalB_res_line_apply_gbi p.1 η.1 p.2 η.2 x t o τ]
  refine ((hasDerivAt_quad _ _ _).add (hasDerivAt_quad _ _ _)).add
    (HasDerivAt.fun_sum fun i _ => ?_)
  have hu := (hasDerivAt_quad ((x * Cm_gbi p.1) t (Sum.inl i))
    ((x * dCm_gbi p.1 η.1) t (Sum.inl i)) ((x * Cm_gbi η.1) t (Sum.inl i))).add
    (hasDerivAt_quad (βm_gbi p.1 p.2 (Sum.inl i)) (dβm_gbi p.1 p.2 η.1 η.2 (Sum.inl i))
      ((η.2.E ᵥ* rd_gbi η.1) (Sum.inl i)))
  have hw := (hasDerivAt_quad ((x * Cm_gbi p.1) t (Sum.inr i))
    ((x * dCm_gbi p.1 η.1) t (Sum.inr i)) ((x * Cm_gbi η.1) t (Sum.inr i))).add
    (hasDerivAt_quad (βm_gbi p.1 p.2 (Sum.inr i)) (dβm_gbi p.1 p.2 η.1 η.2 (Sum.inr i))
      ((η.2.E ᵥ* rd_gbi η.1) (Sum.inr i)))
  have hv := hasDerivAt_quad (Am_gbi p.1 i o) (dAm_gbi p.1 η.1 i o) (Am_gbi η.1 i o)
  have h := (((hσ _).comp (0 : ℝ) hu).mul hw).mul hv
  convert h using 1
  · rfl
  · simp only [Pi.mul_apply, Pi.add_apply, Function.comp_apply, zero_mul, mul_zero, add_zero]
    ring

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: `∂γ` is linear in the direction. -/
private theorem dγr_sub_gbi (θ η ρ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (b ηb ρb : Biases (Arch.gated (T := T) (d := d) σ id hid) dOut) :
    dγr_gbi θ b (η - ρ) (ηb - ρb) = dγr_gbi θ b η ηb - dγr_gbi θ b ρ ρb := by
  show (ηb.E - ρb.E) ᵥ* θ.D + b.E ᵥ* (η.D - ρ.D) + dγm_gbi θ b (η - ρ) (ηb - ρb)
    = (ηb.E ᵥ* θ.D + b.E ᵥ* η.D + dγm_gbi θ b η ηb)
      - (ρb.E ᵥ* θ.D + b.E ᵥ* ρ.D + dγm_gbi θ b ρ ρb)
  rw [dγm_sub_gbi, Matrix.sub_vecMul, Matrix.vecMul_sub]
  abel

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: along a rescaling with biases, `γ` does not move. -/
private theorem dγr_rescale_gbi
    (p : ParamsB (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) (α : ∀ ℓ, hid ℓ → ℝ) :
    dγr_gbi p.1 p.2 (rescaleDirB p α).1 (rescaleDirB p α).2 = 0 := by
  show (0 : d → ℝ) ᵥ* p.1.D + p.2.E ᵥ* (0 : Matrix d dOut ℝ)
    + dγm_gbi p.1 p.2 (rescaleDirB p α).1 (rescaleDirB p α).2 = 0
  rw [dγm_rescale_gbi, Matrix.zero_vecMul, Matrix.vecMul_zero, add_zero, add_zero]

omit [Fintype T] [Nonempty T] in
/-- Helper (the end of the proof of `flatB_le_range_mlp_residual`): a direction that keeps `M`,
`C`, `A`, `β` and `γ` to first order is the direction of one change of basis `X` of both hidden
states and of the translations `g_0 = ρ_{b_E} − b_E X`, `g_1 = ρ_{b_write} − b_write X`. -/
private theorem cobTr_of_keeps_gbi
    (p : ParamsB (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) (hp : OneBlockGenericGated p.1)
    (ρ : ParamsB (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (hC : dCm_gbi p.1 ρ.1 = 0) (hA : dAm_gbi p.1 ρ.1 = 0) (hM : dMm_gbi p.1 ρ.1 = 0)
    (hβ : dβm_gbi p.1 p.2 ρ.1 ρ.2 = 0) (hγ : dγr_gbi p.1 p.2 ρ.1 ρ.2 = 0) :
    ∃ (X : Matrix d d ℝ) (g : Fin 2 → d → ℝ),
      ρ = cobDirB p (fun _ => X) + (0, translateDir p.1 g) := by
  -- Lemma C.2: a direction that keeps `C` and `A` moves the weights by two changes of basis
  obtain ⟨X, hX⟩ := (keeps_products_iff_mem_range_cobDir p.1 ρ.1 hp.rank_E hp.rank_D
    hp.rank_read hp.rank_write).1 ⟨hC, hA⟩
  have hE : ρ.1.E = p.1.E * X 0 := by rw [hX]; rfl
  have hR : ρ.1.read 0 = -(X 0 * p.1.read 0) := by rw [hX]; rfl
  have hD : ρ.1.D = -(X 1 * p.1.D) := by rw [hX]; rfl
  -- Lemma B.2: `∂M = E X_0 D − E X_1 D = 0`, so `X_0 = X_1` (`E` and `D` have rank `d`)
  have h01 : X 0 = X 1 := by
    have h : ρ.1.E * p.1.D + p.1.E * ρ.1.D = 0 := hM
    rw [hE, hD, Matrix.mul_neg, Matrix.mul_assoc, add_neg_eq_zero] at h
    exact cancel_right_of_rank_gbi p.1.D hp.rank_D (cancel_left_of_rank_gbi p.1.E hp.rank_E h)
  have hX' : ρ.1 = cobDir p.1 (fun _ => X 0) := by
    rw [hX]
    exact congrArg (cobDir p.1) (funext (Fin.forall_fin_two.2 ⟨rfl, h01.symm⟩))
  rw [← h01] at hD
  -- `∂β = 0`: `ρ_{b_read} = −g_0 W_read` with `g_0 = ρ_{b_E} − b_E X`
  have hbR : ρ.2.read 0 = -((ρ.2.E - p.2.E ᵥ* X 0) ᵥ* p.1.read 0) := by
    have h : ρ.2.E ᵥ* p.1.read 0 + p.2.E ᵥ* ρ.1.read 0 + ρ.2.read 0 = 0 := hβ
    rw [hR, Matrix.vecMul_neg, ← Matrix.vecMul_vecMul] at h
    rw [Matrix.sub_vecMul]
    linear_combination h
  -- `∂γ = 0`: `ρ_{b_D} = −(g_0 + g_1) D` with `g_1 = ρ_{b_write} − b_write X`
  have hbD : ρ.2.D = -(((ρ.2.E - p.2.E ᵥ* X 0) + (ρ.2.write 0 - p.2.write 0 ᵥ* X 0))
      ᵥ* p.1.D) := by
    have h : ρ.2.E ᵥ* p.1.D + p.2.E ᵥ* ρ.1.D
        + (ρ.2.write 0 ᵥ* p.1.D + p.2.write 0 ᵥ* ρ.1.D + ρ.2.D) = 0 := hγ
    simp only [hD, Matrix.vecMul_neg, ← Matrix.vecMul_vecMul] at h
    rw [Matrix.add_vecMul, Matrix.sub_vecMul, Matrix.sub_vecMul]
    linear_combination h
  -- so `ρ` is the direction of the change of basis `X` and of the translations `g_0, g_1`
  have hI : Finset.Iic (0 : Fin 1).castSucc = {0} := by decide
  refine ⟨X 0, ![ρ.2.E - p.2.E ᵥ* X 0, ρ.2.write 0 - p.2.write 0 ᵥ* X 0], ?_⟩
  refine Prod.ext ?_ ?_
  · show ρ.1 = cobDir p.1 (fun _ => X 0) + 0
    rw [add_zero]
    exact hX'
  · apply Biases.ext'
    · show ρ.2.E = p.2.E ᵥ* X 0 + (ρ.2.E - p.2.E ᵥ* X 0)
      abel
    · intro ℓ
      obtain rfl : ℓ = 0 := Subsingleton.elim ℓ 0
      show ρ.2.read 0 = 0 + -((∑ k ∈ Finset.Iic (0 : Fin 1).castSucc,
        ![ρ.2.E - p.2.E ᵥ* X 0, ρ.2.write 0 - p.2.write 0 ᵥ* X 0] k) ᵥ* p.1.read 0)
      rw [hI, Finset.sum_singleton, zero_add]
      exact hbR
    · intro ℓ
      obtain rfl : ℓ = 0 := Subsingleton.elim ℓ 0
      show ρ.2.write 0 = p.2.write 0 ᵥ* X 0 + (ρ.2.write 0 - p.2.write 0 ᵥ* X 0)
      abel
    · show ρ.2.D = 0 + -((∑ k, ![ρ.2.E - p.2.E ᵥ* X 0, ρ.2.write 0 - p.2.write 0 ᵥ* X 0] k)
        ᵥ* p.1.D)
      rw [Fin.sum_univ_two, zero_add]
      exact hbD

/-- **Lemma B.2 with biases, after Lemma B.3, for one residual SwiGLU or GeGLU block:** under the
conditions `OneBlockGenericGated` on the weights, every flat direction of the residual network
with biases is the sum of the direction of one change of basis `X` of both hidden states and of
the translations `g_0, g_1` of Lemma A.8 and of a direction of the rescalings of the values. -/
theorem flatB_le_range_gated_residual (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hU : GatedUnitsRescale σ σ' dIn dOut (hid 0))
    (p : ParamsB (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (hp : OneBlockGenericGated p.1)
    (η : ParamsB (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (hη : η ∈ flatB (Arch.gated σ id hid) 1 p) :
    ∃ (X : Matrix d d ℝ) (g : Fin 2 → d → ℝ) (α : ∀ ℓ, hid ℓ → ℝ),
      η = cobDirB p (fun _ => X) + (0, translateDir p.1 g) + rescaleDirB p α := by
  -- the derivative of `F(θ, b, x)` along `η` vanishes at every input, entry by entry
  have hzero : ∀ (x : Matrix T dIn ℝ) (t : T) (o : dOut), (x * dMm_gbi p.1 η.1) t o
      + dγr_gbi p.1 p.2 η.1 η.2 o + ∑ i : hid 0,
        (σ ((x * Cm_gbi p.1) t (Sum.inl i) + βm_gbi p.1 p.2 (Sum.inl i))
            * ((x * Cm_gbi p.1) t (Sum.inr i) + βm_gbi p.1 p.2 (Sum.inr i))
            * dAm_gbi p.1 η.1 i o
          + σ' ((x * Cm_gbi p.1) t (Sum.inl i) + βm_gbi p.1 p.2 (Sum.inl i))
            * ((x * dCm_gbi p.1 η.1) t (Sum.inl i) + dβm_gbi p.1 p.2 η.1 η.2 (Sum.inl i))
            * ((x * Cm_gbi p.1) t (Sum.inr i) + βm_gbi p.1 p.2 (Sum.inr i)) * Am_gbi p.1 i o
          + σ ((x * Cm_gbi p.1) t (Sum.inl i) + βm_gbi p.1 p.2 (Sum.inl i))
            * ((x * dCm_gbi p.1 η.1) t (Sum.inr i) + dβm_gbi p.1 p.2 η.1 η.2 (Sum.inr i))
            * Am_gbi p.1 i o) = 0 := by
    intro x t o
    rw [← fderiv_evalB_res_apply_gbi hσ p η x t o]
    have h := LinearMap.mem_ker.1 ((Submodule.mem_iInf _).1 hη x)
    exact congrFun (congrFun h t) o
  -- Lemma B.3 with the linear term (inputs `x` with all rows equal to `v`): `∂M = 0`, `∂γ = 0`,
  -- the gate columns and the gate biases do not move, and every unit only rescales its value,
  -- `∂(e_i, β'_i) = −α_i (e_i, β'_i)`, `∂a_i = α_i a_i`
  obtain ⟨hm, hγ, hc, hβ, α, hα⟩ := hU (fun i => (Cm_gbi p.1)ᵀ (Sum.inl i))
    (fun i => βm_gbi p.1 p.2 (Sum.inl i)) (fun i => (Cm_gbi p.1)ᵀ (Sum.inr i))
    (fun i => βm_gbi p.1 p.2 (Sum.inr i)) (fun i => Am_gbi p.1 i) (dMm_gbi p.1 η.1)
    (dγr_gbi p.1 p.2 η.1 η.2) (fun i => (dCm_gbi p.1 η.1)ᵀ (Sum.inl i))
    (fun i => dβm_gbi p.1 p.2 η.1 η.2 (Sum.inl i)) (fun i => (dCm_gbi p.1 η.1)ᵀ (Sum.inr i))
    (fun i => dβm_gbi p.1 p.2 η.1 η.2 (Sum.inr i)) (fun i => dAm_gbi p.1 η.1 i)
    (fun i => hp.row_ne_zero i) (fun i => hp.gate_ne_zero i)
    (fun i j hij => hp.gate_not_collinear i j hij) (fun i => hp.value_ne_zero i) (by
      intro v
      funext o
      have h := hzero (Matrix.of fun _ => v) (Classical.arbitrary T) o
      simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      exact h)
  -- the rescaling with these `α_i` (one block: `ℓ = 0`)
  let α' : ∀ ℓ : Fin 1, hid ℓ → ℝ := fun ℓ => Fin.cases α (fun l => l.elim0) ℓ
  -- `η − rescaleDirB p α` keeps `C`, `A`, `M`, `β` and `γ` to first order
  have hC : dCm_gbi p.1 (η.1 - rescaleDir p.1 α') = 0 := by
    ext a j
    rcases j with i | i
    · rw [dCm_sub_gbi, Matrix.sub_apply, dCm_rescale_inl_gbi, sub_zero]
      exact congrFun (congrFun hc i) a
    · rw [dCm_sub_gbi, Matrix.sub_apply, dCm_rescale_inr_gbi, Matrix.zero_apply, sub_eq_zero]
      exact congrFun (hα i).1 a
  have hA : dAm_gbi p.1 (η.1 - rescaleDir p.1 α') = 0 := by
    ext i o
    rw [dAm_sub_gbi, Matrix.sub_apply, dAm_rescale_gbi, Matrix.zero_apply, sub_eq_zero]
    exact congrFun (hα i).2.2 o
  -- the rescaling leaves `E` and `D` alone
  have hM : dMm_gbi p.1 (η.1 - rescaleDir p.1 α') = 0 := by
    show (η.1.E - 0) * p.1.D + p.1.E * (η.1.D - 0) = 0
    rw [sub_zero, sub_zero]
    exact hm
  have hβ' : dβm_gbi p.1 p.2 (η.1 - (rescaleDirB p α').1) (η.2 - (rescaleDirB p α').2) = 0 := by
    funext j
    rcases j with i | i
    · rw [dβm_sub_gbi, Pi.sub_apply, dβm_rescale_inl_gbi, sub_zero]
      exact congrFun hβ i
    · rw [dβm_sub_gbi, Pi.sub_apply, dβm_rescale_inr_gbi, Pi.zero_apply, sub_eq_zero]
      exact (hα i).2.1
  have hγ' : dγr_gbi p.1 p.2 (η.1 - (rescaleDirB p α').1) (η.2 - (rescaleDirB p α').2) = 0 := by
    rw [dγr_sub_gbi, dγr_rescale_gbi, sub_zero]
    exact hγ
  -- Lemma C.2 and Lemma B.2 with biases: `η − rescaleDirB p α` is a direction of one change of
  -- basis and of translations
  obtain ⟨X, g, hX⟩ := cobTr_of_keeps_gbi p hp (η - rescaleDirB p α') hC hA hM hβ' hγ'
  exact ⟨X, g, α', sub_eq_iff_eq_add.1 hX⟩

/-- **Theorem B.1 (i) of the skips paper with biases, the residual network, at one parameter, for
a SwiGLU or GeGLU block:** under the conditions `OneBlockGenericGated` on the weights, the
residual network with biases has `fd = P − d² − 2 d − d_hidden`, with `P` counting the
biases. -/
theorem funDimB_gated_oneBlock_residual (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hU : GatedUnitsRescale σ σ' dIn dOut (hid 0))
    (p : ParamsB (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (hp : OneBlockGenericGated p.1) :
    funDimB (Arch.gated σ id hid) 1 p
        + (Fintype.card d ^ 2 + 2 * Fintype.card d + Fintype.card (hid 0))
      = Module.finrank ℝ (ParamsB (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) := by
  have hσd : Differentiable ℝ σ := fun z => (hσ z).differentiableAt
  have hf : ∀ ℓ, Differentiable ℝ ((Arch.gated (T := T) (d := d) σ id hid).f ℓ) :=
    fun ℓ => differentiable_f_gated hσd ℓ
  have hdiff : ∀ x : Matrix T dIn ℝ, DifferentiableAt ℝ
      (fun q : ParamsB (Arch.gated (T := T) (d := d) σ id hid) dIn dOut =>
        evalB (Arch.gated σ id hid) 1 q.1 q.2 x) p := fun x =>
    differentiable_evalB (A := Arch.gated (T := T) (d := d) σ id hid) (S := 1) hf
      differentiable_id x p
  -- no value column of `W_read` vanishes, since the value columns of `C = E W_read` do not
  have hv : ∀ ℓ i, (fun a => p.1.read ℓ a (Sum.inr i)) ≠ 0 := by
    intro ℓ i h0
    obtain rfl := Subsingleton.elim ℓ 0
    apply hp.value_ne_zero i
    funext a
    show ∑ k, p.1.E a k * p.1.read 0 k (Sum.inr i) = 0
    exact Finset.sum_eq_zero fun k _ => by
      rw [show p.1.read 0 k (Sum.inr i) = 0 from congrFun h0 k, mul_zero]
  -- `≤`: one change of basis, the translations and the rescalings are flat and independent
  -- (Lemma A.8 with `s = d_hidden`)
  have hle := funDimB_add_le_residual_gated p hp.rank_E hv
  have hs : ∑ ℓ : Fin 1, Fintype.card (hid ℓ) = Fintype.card (hid 0) := Fin.sum_univ_one _
  -- `≥`: every flat direction is one of them (the previous theorem), and they span a space of
  -- dimension at most `d² + 2 d + d_hidden`
  let Φ := (cobTrLin_gbi p).coprod (rescaleDirBLin_gbi p)
  have hflat : flatB (Arch.gated σ id hid) 1 p ≤ LinearMap.range Φ := by
    intro η hη
    obtain ⟨X, g, α, rfl⟩ := flatB_le_range_gated_residual hσ hU p hp η hη
    exact LinearMap.mem_range.2 ⟨((X, g), α), rfl⟩
  have h1 := Submodule.finrank_mono hflat
  have h2 := (LinearMap.finrank_range_le Φ).trans_eq (finrank_dirDomain_gbi (d := d))
  -- `fd(θ, b) = P − dim K(θ, b)`
  have h3 := funDimB_add_finrank_flatB p hdiff
  omega

/-- **Theorem B.1 (i) of the skips paper with biases, the skipless network, for a SwiGLU or GeGLU
block:** for `d_in, d_out, d_hidden ≥ d ≥ 2`, at generic weights and biases the skipless network
has `fd = P − 2 d² − 2 d − d_hidden`. -/
theorem ae_funDimB_gated_oneBlock (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hU : GatedUnitsRescale σ σ' dIn dOut (hid 0))
    (μ : Measure (ParamsB (Arch.gated (T := T) (d := d) σ id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ p ∂μ, funDimB (Arch.gated σ id hid) 0 p
        + (2 * Fintype.card d ^ 2 + 2 * Fintype.card d + Fintype.card (hid 0))
      = Module.finrank ℝ (ParamsB (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) :=
  (ae_paramsB_of_forall_ae (fun ν _ => ae_oneBlockGenericGated ν hd hdIn hdOut hhid) μ).mono
    fun p hp => funDimB_gated_oneBlock hσ hU p hp

/-- **Theorem B.1 (i) of the skips paper with biases, the residual network, for a SwiGLU or GeGLU
block:** for `d_in, d_out, d_hidden ≥ d ≥ 2`, at generic weights and biases the residual network
has `fd = P − d² − 2 d − d_hidden`. -/
theorem ae_funDimB_gated_oneBlock_residual (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hU : GatedUnitsRescale σ σ' dIn dOut (hid 0))
    (μ : Measure (ParamsB (Arch.gated (T := T) (d := d) σ id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ p ∂μ, funDimB (Arch.gated σ id hid) 1 p
        + (Fintype.card d ^ 2 + 2 * Fintype.card d + Fintype.card (hid 0))
      = Module.finrank ℝ (ParamsB (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) :=
  (ae_paramsB_of_forall_ae (fun ν _ => ae_oneBlockGenericGated ν hd hdIn hdOut hhid) μ).mono
    fun p hp => funDimB_gated_oneBlock_residual hσ hU p hp

/-- **Theorem B.1 (i) of the skips paper with biases, "the skip raises the functional dimension
by exactly `d_model²`", for a SwiGLU or GeGLU block:** for `d_in, d_out, d_hidden ≥ d ≥ 2`, at
generic weights and biases. -/
theorem ae_funDimB_gated_oneBlock_residual_eq_add (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hU : GatedUnitsRescale σ σ' dIn dOut (hid 0))
    (μ : Measure (ParamsB (Arch.gated (T := T) (d := d) σ id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ p ∂μ, funDimB (Arch.gated σ id hid) 1 p
      = funDimB (Arch.gated σ id hid) 0 p + Fintype.card d ^ 2 := by
  filter_upwards [ae_funDimB_gated_oneBlock hσ hU μ hd hdIn hdOut hhid,
    ae_funDimB_gated_oneBlock_residual hσ hU μ hd hdIn hdOut hhid] with p h0 h1
  omega

/-- **Theorem B.1 (i) with biases for one SwiGLU block:** the skip raises the functional
dimension by exactly `d²`. -/
theorem ae_funDimB_swiglu_oneBlock_residual_eq_add
    (μ : Measure (ParamsB (Arch.gated (T := T) (d := d) silu id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ p ∂μ, funDimB (Arch.gated silu id hid) 1 p
      = funDimB (Arch.gated silu id hid) 0 p + Fintype.card d ^ 2 :=
  ae_funDimB_gated_oneBlock_residual_eq_add hasDerivAt_silu (silu_gatedUnitsRescale _ _ _) μ hd
    hdIn hdOut hhid

/-- **Theorem B.1 (i) with biases for one GeGLU block:** the skip raises the functional dimension
by exactly `d²`. -/
theorem ae_funDimB_geglu_oneBlock_residual_eq_add
    (μ : Measure (ParamsB (Arch.gated (T := T) (d := d) gelu id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ p ∂μ, funDimB (Arch.gated gelu id hid) 1 p
      = funDimB (Arch.gated gelu id hid) 0 p + Fintype.card d ^ 2 :=
  ae_funDimB_gated_oneBlock_residual_eq_add hasDerivAt_gelu (gelu_gatedUnitsRescale _ _ _) μ hd
    hdIn hdOut hhid

end Skips
