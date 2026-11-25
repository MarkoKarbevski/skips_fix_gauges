import SkipsLean.OneBlock.ReGLU
import SkipsLean.OneBlock.MlpBiases
import SkipsLean.Symmetry.BiasesRescaleCount
import SkipsLean.Dimension.FunctionalBiasesOn

/-!
# The one-block theorem with biases, for a ReGLU block

Paper (skips paper), Theorem B.1 (i): "Let the network have no normalization, with or without
biases, and let the block have width at least `d_model` […]. For generic parameters the skipless
network has functional dimension `P − 2 d_model² − s` and the residual network
`P − d_model² − s`; with biases on the embedding, the block and the readout, counted in `P`, both
values are `2 d_model` lower […]. Both networks satisfy the equality condition, and the skip
raises the functional dimension by exactly `d_model²`."

Appendix B, "Reduction": "For the gated blocks ReGLU, SwiGLU and GeGLU, in the same way, the value
weights `(e_i, β_i′)` of each unit, introduced below, have `e_i ≠ 0` and are not proportional to
its gate weights `(c_i, β_i)`." Step 3: "`s` is the number of rescalings: `d_hidden` for ReLU,
ReLU², SwiGLU and GeGLU, `2 d_hidden` for ReGLU, none for tanh and GELU."

Here, for one ReGLU block `Arch.gated relu id hid` with biases (`Network/Biases.lean`), under the
conditions `OneBlockGenericReGLU` on the weights (no value column of `E W_read` is proportional
to the gate column of the same unit; then the pair of the value column and the value bias is not
proportional to the pair of the gate column and the gate bias, which is what Lemma B.3 for ReGLU,
`relu_gated_units_flat`, asks); `s = 2 d_hidden`. The twins: `OneBlock/ReGLU.lean` without
biases; `OneBlock/RescaleBiases.lean` and `OneBlock/GatedBiases.lean` with biases.

* `noKinkGateB p`: the inputs at which no gate sits at its kink: every gate pre-activation
  `(x E W_read)_{t, gate i} + β_i`, `β = b_E W_read + b_read`, is nonzero.
* `differentiableAt_evalB_of_mem_noKinkGateB`: at such an input the output is differentiable in
  the weights and biases, with the skip and without it.
* `flatOnB_noKinkGateB_le_reglu`, `flatOnB_noKinkGateB_le_reglu_residual`: a direction that is
  flat at every such input is the sum of a direction of changes of basis and translations, a
  direction of the rescalings of the values and a direction of the rescalings of the gates, with
  their biases (`rescaleDirB`, `rescaleDirGateB 1`).
* `funDimB_reglu_oneBlock`, `funDimB_reglu_oneBlock_residual`: `fd = P − 2 d² − 2 d − 2 d_hidden`
  without the skip and `fd = P − d² − 2 d − 2 d_hidden` with it, `P` counting the biases; each
  with the same rank on a finite batch of inputs with no gate at its kink
  (`exists_jacobianRankB_reglu_oneBlock`, `exists_jacobianRankB_reglu_oneBlock_residual`), as in
  `OneBlock/RescaleBiases.lean`.
* The same at generic `(θ, b)` for `d_in, d_out, d_hidden ≥ d ≥ 2`, and "the skip raises the
  functional dimension by exactly `d_model²`".

Numeric check (`d = d_in = d_out = 2`, one block of 2 units, `P = 30`: 14 and 18):
`ai_notes/biases_inside_blocks_check_2026-11-25.py`.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {hid : Fin 1 → Type} [∀ ℓ, Fintype (hid ℓ)]
variable {σ : ℝ → ℝ}

/-- The inputs at which no gate of the block with biases sits at its kink: every gate
pre-activation `(x E W_read)_{t, gate i} + (b_E W_read + b_read)_{gate i}` (one per token and
hidden unit) is nonzero. -/
def noKinkGateB (p : ParamsB (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) :
    Set (Matrix T dIn ℝ) :=
  {x | ∀ (t : T) (i : hid 0),
    (x * p.1.E * p.1.read 0) t (Sum.inl i) + (p.2.E ᵥ* p.1.read 0 + p.2.read 0) (Sum.inl i) ≠ 0}

/-! ### Helpers: the function of one ReGLU block with biases and its derivative -/

/-- Helper: the read of the block, with its columns indexed by the gates and values. -/
private def rd_rgb (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) :
    Matrix d (hid 0 ⊕ hid 0) ℝ :=
  θ.read 0

/-- Helper: the write of the block, with its rows indexed by the hidden units. -/
private def wr_rgb (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) :
    Matrix (hid 0) d ℝ :=
  θ.write 0

/-- Helper: `C = E W_read`. -/
private def Cm_rgb (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) :
    Matrix dIn (hid 0 ⊕ hid 0) ℝ :=
  θ.E * rd_rgb θ

/-- Helper: `A = W_write D`. -/
private def Am_rgb (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) :
    Matrix (hid 0) dOut ℝ :=
  wr_rgb θ * θ.D

/-- Helper: `M_S = E S_0 D`, the linear part of the network (`0` without the skip, `E D` with
it). -/
private def Mm_rgb (S : Fin 1 → Matrix d d ℝ)
    (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) : Matrix dIn dOut ℝ :=
  θ.E * S 0 * θ.D

/-- Helper: `β = b_E W_read + b_read`, the gate biases and the value biases. -/
private def βm_rgb (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (b : Biases (Arch.gated (T := T) (d := d) σ id hid) dOut) : hid 0 ⊕ hid 0 → ℝ :=
  b.E ᵥ* rd_rgb θ + b.read 0

/-- Helper: `γ_S = b_E S_0 D + b_write D + b_D` (`γ_0` without the skip, `γ` with it). -/
private def γm_rgb (S : Fin 1 → Matrix d d ℝ)
    (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (b : Biases (Arch.gated (T := T) (d := d) σ id hid) dOut) : dOut → ℝ :=
  b.E ᵥ* (S 0 * θ.D) + (b.write 0 ᵥ* θ.D + b.D)

/-- Helper: the derivative `∂C = η_E W_read + E η_read` of `C` along `η`. -/
private def dCm_rgb (θ η : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) :
    Matrix dIn (hid 0 ⊕ hid 0) ℝ :=
  η.E * rd_rgb θ + θ.E * rd_rgb η

/-- Helper: the derivative `∂A = η_write D + W_write η_D` of `A` along `η`. -/
private def dAm_rgb (θ η : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) :
    Matrix (hid 0) dOut ℝ :=
  wr_rgb η * θ.D + wr_rgb θ * η.D

/-- Helper: the derivative `∂M_S = η_E S_0 D + E S_0 η_D` of `M_S` along `η`. -/
private def dMm_rgb (S : Fin 1 → Matrix d d ℝ)
    (θ η : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) : Matrix dIn dOut ℝ :=
  η.E * S 0 * θ.D + θ.E * S 0 * η.D

/-- Helper: the derivative `∂β = η_{b_E} W_read + b_E η_read + η_{b_read}` of `β`. -/
private def dβm_rgb (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (b : Biases (Arch.gated (T := T) (d := d) σ id hid) dOut)
    (η : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (ηb : Biases (Arch.gated (T := T) (d := d) σ id hid) dOut) : hid 0 ⊕ hid 0 → ℝ :=
  ηb.E ᵥ* rd_rgb θ + b.E ᵥ* rd_rgb η + ηb.read 0

/-- Helper: the derivative of `γ_S` along `(η, η_b)`. -/
private def dγm_rgb (S : Fin 1 → Matrix d d ℝ)
    (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (b : Biases (Arch.gated (T := T) (d := d) σ id hid) dOut)
    (η : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (ηb : Biases (Arch.gated (T := T) (d := d) σ id hid) dOut) : dOut → ℝ :=
  ηb.E ᵥ* (S 0 * θ.D) + b.E ᵥ* (S 0 * η.D) + (ηb.write 0 ᵥ* θ.D + b.write 0 ᵥ* η.D + ηb.D)

omit [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the read is linear in the parameters. -/
private theorem rd_line_rgb (θ η : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (τ : ℝ) : rd_rgb (θ + τ • η) = rd_rgb θ + τ • rd_rgb η := rfl

omit [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the write is linear in the parameters. -/
private theorem wr_line_rgb (θ η : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (τ : ℝ) : wr_rgb (θ + τ • η) = wr_rgb θ + τ • wr_rgb η := rfl

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: along the line, `C(τ) = C + τ ∂C + τ² η_E η_read`. -/
private theorem Cm_line_rgb (θ η : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (τ : ℝ) :
    Cm_rgb (θ + τ • η) = Cm_rgb θ + τ • dCm_rgb θ η + (τ * τ) • Cm_rgb η := by
  simp only [Cm_rgb, dCm_rgb, rd_line_rgb, Params.add_E, Params.smul_E, Matrix.mul_add,
    Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, smul_add, smul_smul]
  abel

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: along the line, `A(τ) = A + τ ∂A + τ² η_write η_D`. -/
private theorem Am_line_rgb (θ η : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (τ : ℝ) :
    Am_rgb (θ + τ • η) = Am_rgb θ + τ • dAm_rgb θ η + (τ * τ) • Am_rgb η := by
  simp only [Am_rgb, dAm_rgb, wr_line_rgb, Params.add_D, Params.smul_D, Matrix.mul_add,
    Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, smul_add, smul_smul]
  abel

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: along the line, `M_S(τ) = M_S + τ ∂M_S + τ² η_E S_0 η_D`. -/
private theorem Mm_line_rgb (S : Fin 1 → Matrix d d ℝ)
    (θ η : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) (τ : ℝ) :
    Mm_rgb S (θ + τ • η) = Mm_rgb S θ + τ • dMm_rgb S θ η + (τ * τ) • Mm_rgb S η := by
  simp only [Mm_rgb, dMm_rgb, Params.add_E, Params.smul_E, Params.add_D, Params.smul_D,
    Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, smul_add, smul_smul]
  abel

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: along the line, `β(τ) = β + τ ∂β + τ² η_{b_E} η_read`. -/
private theorem βm_line_rgb (θ η : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (b ηb : Biases (Arch.gated (T := T) (d := d) σ id hid) dOut) (τ : ℝ) :
    βm_rgb (θ + τ • η) (b + τ • ηb)
      = βm_rgb θ b + τ • dβm_rgb θ b η ηb + (τ * τ) • (ηb.E ᵥ* rd_rgb η) := by
  simp only [βm_rgb, dβm_rgb, rd_line_rgb, Biases.add_E, Biases.smul_E, Biases.add_read,
    Biases.smul_read, Matrix.vecMul_add, Matrix.add_vecMul, Matrix.vecMul_smul,
    Matrix.smul_vecMul, smul_add, smul_smul]
  abel

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: along the line, `γ_S(τ) = γ_S + τ ∂γ_S + τ² (η_{b_E} S_0 + η_{b_write}) η_D`. -/
private theorem γm_line_rgb (S : Fin 1 → Matrix d d ℝ)
    (θ η : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (b ηb : Biases (Arch.gated (T := T) (d := d) σ id hid) dOut) (τ : ℝ) :
    γm_rgb S (θ + τ • η) (b + τ • ηb)
      = γm_rgb S θ b + τ • dγm_rgb S θ b η ηb
        + (τ * τ) • (ηb.E ᵥ* (S 0 * η.D) + ηb.write 0 ᵥ* η.D) := by
  simp only [γm_rgb, dγm_rgb, Params.add_D, Params.smul_D, Biases.add_E, Biases.smul_E,
    Biases.add_write, Biases.smul_write, Biases.add_D, Biases.smul_D, Matrix.mul_add,
    Matrix.mul_smul, Matrix.vecMul_add, Matrix.add_vecMul, Matrix.vecMul_smul,
    Matrix.smul_vecMul, smul_add, smul_smul]
  abel

omit [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the matrix whose rows are all `v`, times `M`, has all rows `v M`. -/
private theorem of_const_mul_rgb {m n : Type*} [Fintype m] (v : m → ℝ) (M : Matrix m n ℝ) :
    (Matrix.of fun _ : T => v) * M = Matrix.of fun _ : T => v ᵥ* M := by
  ext t j
  rfl

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dOut] in
/-- Helper: the network of one gated block with biases and the stream matrix `S`,
`F(θ, b, x) = x M_S + γ_S + (σ(x C_g + β_g) ⊙ (x C_v + β_v)) A`. -/
private theorem evalB_eq_rgb (S : Fin 1 → Matrix d d ℝ)
    (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (b : Biases (Arch.gated (T := T) (d := d) σ id hid) dOut) (x : Matrix T dIn ℝ) :
    evalB (Arch.gated σ id hid) S θ b x
      = x * Mm_rgb S θ + (Matrix.of fun _ : T => γm_rgb S θ b)
        + (Matrix.of fun t i =>
            σ ((x * Cm_rgb θ + Matrix.of fun _ : T => βm_rgb θ b) t (Sum.inl i))
              * (x * Cm_rgb θ + Matrix.of fun _ : T => βm_rgb θ b) t (Sum.inr i)) * Am_rgb θ := by
  have h1 : (Fin.last 1 : Fin 2) = (0 : Fin 1).succ := rfl
  have hχ : (Arch.gated (T := T) (d := d) σ id hid).χ = id := rfl
  have hf : (Arch.gated (T := T) (d := d) σ id hid).f 0
      = fun M => Matrix.of fun t i => σ (M t (Sum.inl i)) * M t (Sum.inr i) := rfl
  -- `h_1 = h_0 S_0 + f(h_0 W_read + b_read) W_write + b_write` with `h_0 = x E + b_E`
  rw [evalB, h1, hiddenB_succ, Fin.castSucc_zero, hiddenB_zero, hχ, hf]
  simp only [id_eq, Matrix.add_mul, Matrix.mul_assoc, of_const_mul_rgb, Mm_rgb, Cm_rgb, Am_rgb,
    rd_rgb, wr_rgb, γm_rgb, βm_rgb]
  ext t o
  simp only [Matrix.add_apply, Matrix.of_apply, Pi.add_apply, Matrix.vecMul_vecMul, add_assoc]
  ring

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dOut] in
/-- Helper: the entries of `F(θ, b, x)`,
`(x M_S)_{t o} + γ_{S,o} + ∑_i σ((x C)_{t, g i} + β_{g i}) ((x C)_{t, v i} + β_{v i}) A_{i o}`. -/
private theorem evalB_apply_rgb (S : Fin 1 → Matrix d d ℝ)
    (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (b : Biases (Arch.gated (T := T) (d := d) σ id hid) dOut) (x : Matrix T dIn ℝ) (t : T)
    (o : dOut) :
    evalB (Arch.gated σ id hid) S θ b x t o
      = (x * Mm_rgb S θ) t o + γm_rgb S θ b o + ∑ i : hid 0,
        σ ((x * Cm_rgb θ) t (Sum.inl i) + βm_rgb θ b (Sum.inl i))
          * ((x * Cm_rgb θ) t (Sum.inr i) + βm_rgb θ b (Sum.inr i)) * Am_rgb θ i o := by
  rw [evalB_eq_rgb]
  rfl

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dOut] in
/-- Helper: the entries of `F(θ + τ η, b + τ η_b)(x)` as functions of `τ`. -/
private theorem evalB_line_apply_rgb (S : Fin 1 → Matrix d d ℝ)
    (θ η : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (b ηb : Biases (Arch.gated (T := T) (d := d) σ id hid) dOut) (x : Matrix T dIn ℝ) (t : T)
    (o : dOut) (τ : ℝ) :
    evalB (Arch.gated σ id hid) S (θ + τ • η) (b + τ • ηb) x t o
      = ((x * Mm_rgb S θ) t o + τ * (x * dMm_rgb S θ η) t o + τ * τ * (x * Mm_rgb S η) t o)
        + (γm_rgb S θ b o + τ * dγm_rgb S θ b η ηb o
          + τ * τ * (ηb.E ᵥ* (S 0 * η.D) + ηb.write 0 ᵥ* η.D) o)
        + ∑ i : hid 0,
          σ (((x * Cm_rgb θ) t (Sum.inl i) + τ * (x * dCm_rgb θ η) t (Sum.inl i)
                + τ * τ * (x * Cm_rgb η) t (Sum.inl i))
              + (βm_rgb θ b (Sum.inl i) + τ * dβm_rgb θ b η ηb (Sum.inl i)
                + τ * τ * (ηb.E ᵥ* rd_rgb η) (Sum.inl i)))
            * (((x * Cm_rgb θ) t (Sum.inr i) + τ * (x * dCm_rgb θ η) t (Sum.inr i)
                + τ * τ * (x * Cm_rgb η) t (Sum.inr i))
              + (βm_rgb θ b (Sum.inr i) + τ * dβm_rgb θ b η ηb (Sum.inr i)
                + τ * τ * (ηb.E ᵥ* rd_rgb η) (Sum.inr i)))
            * (Am_rgb θ i o + τ * dAm_rgb θ η i o + τ * τ * Am_rgb η i o) := by
  rw [evalB_apply_rgb, Mm_line_rgb, Cm_line_rgb, Am_line_rgb, βm_line_rgb, γm_line_rgb]
  simp only [Matrix.mul_add, Matrix.mul_smul]
  rfl

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dOut] in
/-- Helper: at an input of `noKinkGateB p`, every gate pre-activation `(x C)_{t, g i} + β_{g i}`
is nonzero. -/
private theorem noKinkGateB_apply_rgb
    {p : ParamsB (Arch.gated (T := T) (d := d) σ id hid) dIn dOut}
    {x : Matrix T dIn ℝ} (hx : x ∈ noKinkGateB p) (t : T) (i : hid 0) :
    (x * Cm_rgb p.1) t (Sum.inl i) + βm_rgb p.1 p.2 (Sum.inl i) ≠ 0 := by
  have h := hx t i
  rwa [Matrix.mul_assoc] at h

omit [Fintype T] [Nonempty T] [DecidableEq d] in
/-- At an input with no gate at its kink, the output of a network of one ReGLU block with biases
is differentiable in the weights and biases, for every stream matrix (with the skip and without
it). -/
theorem differentiableAt_evalB_of_mem_noKinkGateB (S : Fin 1 → Matrix d d ℝ)
    (p : ParamsB (Arch.gated (T := T) (d := d) relu id hid) dIn dOut)
    (x : Matrix T dIn ℝ) (hx : x ∈ noKinkGateB p) :
    DifferentiableAt ℝ
      (fun q : ParamsB (Arch.gated (T := T) (d := d) relu id hid) dIn dOut =>
        evalB (Arch.gated relu id hid) S q.1 q.2 x) p := by
  -- every entry of the weights and of the biases is a linear function of `(θ, b)`
  have hlin : ∀ l : ParamsB (Arch.gated (T := T) (d := d) relu id hid) dIn dOut →ₗ[ℝ] ℝ,
      DifferentiableAt ℝ l p := fun l => by
    rw [← LinearMap.coe_toContinuousLinearMap' l]
    exact (LinearMap.toContinuousLinearMap l).differentiableAt
  have hE : ∀ (a : dIn) (k : d), DifferentiableAt ℝ
      (fun q : ParamsB (Arch.gated (T := T) (d := d) relu id hid) dIn dOut => q.1.E a k) p :=
    fun a k => hlin
      { toFun := fun q => q.1.E a k, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hR : ∀ (k : d) (j : hid 0 ⊕ hid 0), DifferentiableAt ℝ
      (fun q : ParamsB (Arch.gated (T := T) (d := d) relu id hid) dIn dOut => q.1.read 0 k j) p :=
    fun k j => hlin
      { toFun := fun q => q.1.read 0 k j, map_add' := fun _ _ => rfl,
        map_smul' := fun _ _ => rfl }
  have hW : ∀ (i : hid 0) (k : d), DifferentiableAt ℝ
      (fun q : ParamsB (Arch.gated (T := T) (d := d) relu id hid) dIn dOut => q.1.write 0 i k) p :=
    fun i k => hlin
      { toFun := fun q => q.1.write 0 i k, map_add' := fun _ _ => rfl,
        map_smul' := fun _ _ => rfl }
  have hD : ∀ (k : d) (o : dOut), DifferentiableAt ℝ
      (fun q : ParamsB (Arch.gated (T := T) (d := d) relu id hid) dIn dOut => q.1.D k o) p :=
    fun k o => hlin
      { toFun := fun q => q.1.D k o, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hbE : ∀ k : d, DifferentiableAt ℝ
      (fun q : ParamsB (Arch.gated (T := T) (d := d) relu id hid) dIn dOut => q.2.E k) p :=
    fun k => hlin
      { toFun := fun q => q.2.E k, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hbR : ∀ j : hid 0 ⊕ hid 0, DifferentiableAt ℝ
      (fun q : ParamsB (Arch.gated (T := T) (d := d) relu id hid) dIn dOut => q.2.read 0 j) p :=
    fun j => hlin
      { toFun := fun q => q.2.read 0 j, map_add' := fun _ _ => rfl,
        map_smul' := fun _ _ => rfl }
  have hbW : ∀ k : d, DifferentiableAt ℝ
      (fun q : ParamsB (Arch.gated (T := T) (d := d) relu id hid) dIn dOut => q.2.write 0 k) p :=
    fun k => hlin
      { toFun := fun q => q.2.write 0 k, map_add' := fun _ _ => rfl,
        map_smul' := fun _ _ => rfl }
  have hbD : ∀ o : dOut, DifferentiableAt ℝ
      (fun q : ParamsB (Arch.gated (T := T) (d := d) relu id hid) dIn dOut => q.2.D o) p :=
    fun o => hlin
      { toFun := fun q => q.2.D o, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  -- so the entries of `x M_S`, `x C`, `A`, `β` and `γ_S` are polynomials in `(θ, b)`
  have hxM : ∀ (t : T) (o : dOut), DifferentiableAt ℝ
      (fun q : ParamsB (Arch.gated (T := T) (d := d) relu id hid) dIn dOut =>
        (x * Mm_rgb S q.1) t o) p := by
    intro t o
    show DifferentiableAt ℝ (fun q : ParamsB (Arch.gated (T := T) (d := d) relu id hid) dIn dOut =>
      ∑ a, x t a * ∑ m, (∑ k, q.1.E a k * S 0 k m) * q.1.D m o) p
    exact DifferentiableAt.fun_sum fun a _ => (DifferentiableAt.fun_sum fun m _ =>
      (DifferentiableAt.fun_sum fun k _ => (hE a k).mul_const (S 0 k m)).mul (hD m o)).const_mul
        (x t a)
  have hxC : ∀ (t : T) (j : hid 0 ⊕ hid 0), DifferentiableAt ℝ
      (fun q : ParamsB (Arch.gated (T := T) (d := d) relu id hid) dIn dOut =>
        (x * Cm_rgb q.1) t j) p := by
    intro t j
    show DifferentiableAt ℝ (fun q : ParamsB (Arch.gated (T := T) (d := d) relu id hid) dIn dOut =>
      ∑ a, x t a * ∑ k, q.1.E a k * q.1.read 0 k j) p
    exact DifferentiableAt.fun_sum fun a _ =>
      (DifferentiableAt.fun_sum fun k _ => (hE a k).mul (hR k j)).const_mul (x t a)
  have hA : ∀ (i : hid 0) (o : dOut), DifferentiableAt ℝ
      (fun q : ParamsB (Arch.gated (T := T) (d := d) relu id hid) dIn dOut =>
        Am_rgb q.1 i o) p := by
    intro i o
    show DifferentiableAt ℝ (fun q : ParamsB (Arch.gated (T := T) (d := d) relu id hid) dIn dOut =>
      ∑ k, q.1.write 0 i k * q.1.D k o) p
    exact DifferentiableAt.fun_sum fun k _ => (hW i k).mul (hD k o)
  have hβ : ∀ j : hid 0 ⊕ hid 0, DifferentiableAt ℝ
      (fun q : ParamsB (Arch.gated (T := T) (d := d) relu id hid) dIn dOut =>
        βm_rgb q.1 q.2 j) p := by
    intro j
    show DifferentiableAt ℝ (fun q : ParamsB (Arch.gated (T := T) (d := d) relu id hid) dIn dOut =>
      ∑ k, q.2.E k * q.1.read 0 k j + q.2.read 0 j) p
    exact (DifferentiableAt.fun_sum fun k _ => (hbE k).mul (hR k j)).add (hbR j)
  have hγ : ∀ o : dOut, DifferentiableAt ℝ
      (fun q : ParamsB (Arch.gated (T := T) (d := d) relu id hid) dIn dOut =>
        γm_rgb S q.1 q.2 o) p := by
    intro o
    show DifferentiableAt ℝ (fun q : ParamsB (Arch.gated (T := T) (d := d) relu id hid) dIn dOut =>
      ∑ k, q.2.E k * ∑ m, S 0 k m * q.1.D m o + (∑ k, q.2.write 0 k * q.1.D k o + q.2.D o)) p
    exact (DifferentiableAt.fun_sum fun k _ => (hbE k).mul (DifferentiableAt.fun_sum fun m _ =>
      (hD m o).const_mul (S 0 k m))).add
        ((DifferentiableAt.fun_sum fun k _ => (hbW k).mul (hD k o)).add (hbD o))
  -- the entry `(t, o)` is `(x M_S)_{t o} + γ_{S,o} + ∑_i relu(z_i) w_i A_{i o}`, and `relu` is
  -- differentiable at every gate pre-activation `z_i`, which is not `0`
  refine differentiableAt_pi.2 fun t => differentiableAt_pi.2 fun o => ?_
  simp only [evalB_apply_rgb]
  have hr : ∀ i : hid 0, DifferentiableAt ℝ
      (fun q : ParamsB (Arch.gated (T := T) (d := d) relu id hid) dIn dOut =>
        relu ((x * Cm_rgb q.1) t (Sum.inl i) + βm_rgb q.1 q.2 (Sum.inl i))) p := by
    intro i
    have hz : DifferentiableAt ℝ relu
        ((x * Cm_rgb p.1) t (Sum.inl i) + βm_rgb p.1 p.2 (Sum.inl i)) :=
      (hasDerivAt_relu (noKinkGateB_apply_rgb hx t i)).differentiableAt
    -- named first: against the goal, `?g ∘ ?f` would be unified with `relu` unfolded
    have hc := hz.comp p ((hxC t (Sum.inl i)).add (hβ (Sum.inl i)))
    exact hc
  have hu : ∀ i : hid 0, DifferentiableAt ℝ
      (fun q : ParamsB (Arch.gated (T := T) (d := d) relu id hid) dIn dOut =>
        relu ((x * Cm_rgb q.1) t (Sum.inl i) + βm_rgb q.1 q.2 (Sum.inl i))
          * ((x * Cm_rgb q.1) t (Sum.inr i) + βm_rgb q.1 q.2 (Sum.inr i)) * Am_rgb q.1 i o) p :=
    fun i => ((hr i).mul ((hxC t (Sum.inr i)).add (hβ (Sum.inr i)))).mul (hA i o)
  exact ((hxM t o).add (hγ o)).add (DifferentiableAt.fun_sum fun i _ => hu i)

omit [Nonempty T] [DecidableEq d] in
/-- Helper (the chain rule, at an input of `noKinkGateB p`): the derivative of
`(θ, b) ↦ F(θ, b, x)` along `η` has the entries `(x ∂M_S)_{t o} + ∂γ_{S,o} + ∑_i [relu(z_i) w_i
(∂A)_{i o} + 1[z_i > 0] ((x ∂C)_{t, g i} + ∂β_{g i}) w_i A_{i o} + relu(z_i) ((x ∂C)_{t, v i}
+ ∂β_{v i}) A_{i o}]`, with `z_i = (x C)_{t, g i} + β_{g i}` and
`w_i = (x C)_{t, v i} + β_{v i}`. -/
private theorem fderiv_evalB_apply_rgb (S : Fin 1 → Matrix d d ℝ)
    (p η : ParamsB (Arch.gated (T := T) (d := d) relu id hid) dIn dOut)
    (x : Matrix T dIn ℝ) (hx : x ∈ noKinkGateB p) (t : T) (o : dOut) :
    fderiv ℝ (fun q : ParamsB (Arch.gated (T := T) (d := d) relu id hid) dIn dOut =>
        evalB (Arch.gated relu id hid) S q.1 q.2 x) p η t o
      = (x * dMm_rgb S p.1 η.1) t o + dγm_rgb S p.1 p.2 η.1 η.2 o + ∑ i : hid 0,
        (relu ((x * Cm_rgb p.1) t (Sum.inl i) + βm_rgb p.1 p.2 (Sum.inl i))
            * ((x * Cm_rgb p.1) t (Sum.inr i) + βm_rgb p.1 p.2 (Sum.inr i))
            * dAm_rgb p.1 η.1 i o
          + reluDeriv ((x * Cm_rgb p.1) t (Sum.inl i) + βm_rgb p.1 p.2 (Sum.inl i))
            * ((x * dCm_rgb p.1 η.1) t (Sum.inl i) + dβm_rgb p.1 p.2 η.1 η.2 (Sum.inl i))
            * ((x * Cm_rgb p.1) t (Sum.inr i) + βm_rgb p.1 p.2 (Sum.inr i)) * Am_rgb p.1 i o
          + relu ((x * Cm_rgb p.1) t (Sum.inl i) + βm_rgb p.1 p.2 (Sum.inl i))
            * ((x * dCm_rgb p.1 η.1) t (Sum.inr i) + dβm_rgb p.1 p.2 η.1 η.2 (Sum.inr i))
            * Am_rgb p.1 i o) := by
  -- the line `τ ↦ (θ + τ η, b + τ η_b)` has velocity `η` and passes through `p` at `τ = 0`
  have hline : HasDerivAt (fun τ : ℝ => (p.1 + τ • η.1, p.2 + τ • η.2)) η 0 := by
    have h1 := ((hasDerivAt_id (0 : ℝ)).smul_const η.1).const_add p.1
    have h2 := ((hasDerivAt_id (0 : ℝ)).smul_const η.2).const_add p.2
    rw [one_smul] at h1 h2
    exact h1.prodMk h2
  have h0 : p = (p.1 + (0 : ℝ) • η.1, p.2 + (0 : ℝ) • η.2) := by
    rw [zero_smul, zero_smul, add_zero, add_zero]
  -- the chain rule along the line
  have h1 := (differentiableAt_evalB_of_mem_noKinkGateB S p x hx).hasFDerivAt.comp_hasDerivAt_of_eq
    (0 : ℝ) hline h0
  have h2 := hasDerivAt_pi.1 (hasDerivAt_pi.1 h1 t) o
  -- the same derivative computed entrywise: polynomials in `τ`, products and sums of real
  -- functions of `τ`
  have h3 : HasDerivAt (fun τ : ℝ =>
      evalB (Arch.gated relu id hid) S (p.1 + τ • η.1) (p.2 + τ • η.2) x t o)
      ((x * dMm_rgb S p.1 η.1) t o + dγm_rgb S p.1 p.2 η.1 η.2 o + ∑ i : hid 0,
        (relu ((x * Cm_rgb p.1) t (Sum.inl i) + βm_rgb p.1 p.2 (Sum.inl i))
            * ((x * Cm_rgb p.1) t (Sum.inr i) + βm_rgb p.1 p.2 (Sum.inr i))
            * dAm_rgb p.1 η.1 i o
          + reluDeriv ((x * Cm_rgb p.1) t (Sum.inl i) + βm_rgb p.1 p.2 (Sum.inl i))
            * ((x * dCm_rgb p.1 η.1) t (Sum.inl i) + dβm_rgb p.1 p.2 η.1 η.2 (Sum.inl i))
            * ((x * Cm_rgb p.1) t (Sum.inr i) + βm_rgb p.1 p.2 (Sum.inr i)) * Am_rgb p.1 i o
          + relu ((x * Cm_rgb p.1) t (Sum.inl i) + βm_rgb p.1 p.2 (Sum.inl i))
            * ((x * dCm_rgb p.1 η.1) t (Sum.inr i) + dβm_rgb p.1 p.2 η.1 η.2 (Sum.inr i))
            * Am_rgb p.1 i o)) 0 := by
    rw [funext fun τ => evalB_line_apply_rgb S p.1 η.1 p.2 η.2 x t o τ]
    refine ((hasDerivAt_quad _ _ _).add (hasDerivAt_quad _ _ _)).add
      (HasDerivAt.fun_sum fun i _ => ?_)
    have hu := (hasDerivAt_quad ((x * Cm_rgb p.1) t (Sum.inl i))
      ((x * dCm_rgb p.1 η.1) t (Sum.inl i)) ((x * Cm_rgb η.1) t (Sum.inl i))).add
        (hasDerivAt_quad (βm_rgb p.1 p.2 (Sum.inl i)) (dβm_rgb p.1 p.2 η.1 η.2 (Sum.inl i))
          ((η.2.E ᵥ* rd_rgb η.1) (Sum.inl i)))
    have hw := (hasDerivAt_quad ((x * Cm_rgb p.1) t (Sum.inr i))
      ((x * dCm_rgb p.1 η.1) t (Sum.inr i)) ((x * Cm_rgb η.1) t (Sum.inr i))).add
        (hasDerivAt_quad (βm_rgb p.1 p.2 (Sum.inr i)) (dβm_rgb p.1 p.2 η.1 η.2 (Sum.inr i))
          ((η.2.E ᵥ* rd_rgb η.1) (Sum.inr i)))
    have hv := hasDerivAt_quad (Am_rgb p.1 i o) (dAm_rgb p.1 η.1 i o) (Am_rgb η.1 i o)
    -- `relu` is differentiable at the gate pre-activation, which is not `0`
    have h := (((hasDerivAt_relu (noKinkGateB_apply_rgb hx t i)).comp_of_eq (0 : ℝ) hu
      (by simp only [Pi.add_apply, zero_mul, add_zero])).mul hw).mul hv
    convert h using 1
    · rfl
    · simp only [Pi.mul_apply, Pi.add_apply, Function.comp_apply, zero_mul, mul_zero, add_zero]
      ring
  exact h2.unique h3

omit [Fintype T] [Nonempty T] [DecidableEq d] in
/-- Helper: a direction that is flat at every input of `noKinkGateB p` has a vanishing derivative
there, entry by entry. -/
private theorem flat_apply_rgb (S : Fin 1 → Matrix d d ℝ)
    (p η : ParamsB (Arch.gated (T := T) (d := d) relu id hid) dIn dOut)
    (hη : η ∈ flatOnB (Arch.gated relu id hid) S p (noKinkGateB p))
    (x : Matrix T dIn ℝ) (hx : x ∈ noKinkGateB p) (t : T) (o : dOut) :
    fderiv ℝ (fun q : ParamsB (Arch.gated (T := T) (d := d) relu id hid) dIn dOut =>
        evalB (Arch.gated relu id hid) S q.1 q.2 x) p η t o = 0 := by
  have h := LinearMap.mem_ker.1 ((Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hη x) hx)
  exact congrFun (congrFun h t) o

/-! ### Helpers: the derivatives of `C`, `A` and `β` along the two rescalings -/

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: `∂C` is linear in the direction. -/
private theorem dCm_sub_rgb (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (η ρ : ParamsB (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) :
    dCm_rgb θ (η - ρ).1 = dCm_rgb θ η.1 - dCm_rgb θ ρ.1 := by
  show (η.1.E - ρ.1.E) * rd_rgb θ + θ.E * (rd_rgb η.1 - rd_rgb ρ.1)
    = (η.1.E * rd_rgb θ + θ.E * rd_rgb η.1) - (ρ.1.E * rd_rgb θ + θ.E * rd_rgb ρ.1)
  rw [Matrix.sub_mul, Matrix.mul_sub]
  abel

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: `∂A` is linear in the direction. -/
private theorem dAm_sub_rgb (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (η ρ : ParamsB (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) :
    dAm_rgb θ (η - ρ).1 = dAm_rgb θ η.1 - dAm_rgb θ ρ.1 := by
  show (wr_rgb η.1 - wr_rgb ρ.1) * θ.D + wr_rgb θ * (η.1.D - ρ.1.D)
    = (wr_rgb η.1 * θ.D + wr_rgb θ * η.1.D) - (wr_rgb ρ.1 * θ.D + wr_rgb θ * ρ.1.D)
  rw [Matrix.sub_mul, Matrix.mul_sub]
  abel

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: `∂β` is linear in the direction. -/
private theorem dβm_sub_rgb (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (b : Biases (Arch.gated (T := T) (d := d) σ id hid) dOut)
    (η ρ : ParamsB (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) :
    dβm_rgb θ b (η - ρ).1 (η - ρ).2 = dβm_rgb θ b η.1 η.2 - dβm_rgb θ b ρ.1 ρ.2 := by
  show (η.2.E - ρ.2.E) ᵥ* rd_rgb θ + b.E ᵥ* (rd_rgb η.1 - rd_rgb ρ.1)
      + (η.2.read 0 - ρ.2.read 0)
    = (η.2.E ᵥ* rd_rgb θ + b.E ᵥ* rd_rgb η.1 + η.2.read 0)
      - (ρ.2.E ᵥ* rd_rgb θ + b.E ᵥ* rd_rgb ρ.1 + ρ.2.read 0)
  rw [Matrix.sub_vecMul, Matrix.vecMul_sub]
  abel

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: along a rescaling of the values, the gate columns of `C` do not move. -/
private theorem dCm_value_inl_rgb (p : ParamsB (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (α : ∀ ℓ, hid ℓ → ℝ) (a : dIn) (i : hid 0) :
    dCm_rgb p.1 (rescaleDirB p α).1 a (Sum.inl i) = 0 := by
  show ((0 : Matrix dIn d ℝ) * rd_rgb p.1 + p.1.E * rd_rgb (rescaleDir p.1 α)) a (Sum.inl i) = 0
  rw [Matrix.zero_mul, zero_add, Matrix.mul_apply]
  exact Finset.sum_eq_zero fun k _ => mul_eq_zero_of_right _ rfl

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: along a rescaling of the values, the value column `e_i` of `C` moves by
`-α_i e_i`. -/
private theorem dCm_value_inr_rgb (p : ParamsB (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (α : ∀ ℓ, hid ℓ → ℝ) (a : dIn) (i : hid 0) :
    dCm_rgb p.1 (rescaleDirB p α).1 a (Sum.inr i) = -(α 0 i) * Cm_rgb p.1 a (Sum.inr i) := by
  show ((0 : Matrix dIn d ℝ) * rd_rgb p.1 + p.1.E * rd_rgb (rescaleDir p.1 α)) a (Sum.inr i)
    = -(α 0 i) * (p.1.E * rd_rgb p.1) a (Sum.inr i)
  rw [Matrix.zero_mul, zero_add, Matrix.mul_apply, Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  show p.1.E a k * (-(α 0 i) * p.1.read 0 k (Sum.inr i))
    = -(α 0 i) * (p.1.E a k * p.1.read 0 k (Sum.inr i))
  ring

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: along a rescaling of the values, the row `a_i` of `A` moves by `α_i a_i`. -/
private theorem dAm_value_rgb (p : ParamsB (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (α : ∀ ℓ, hid ℓ → ℝ) (i : hid 0) (o : dOut) :
    dAm_rgb p.1 (rescaleDirB p α).1 i o = α 0 i * Am_rgb p.1 i o := by
  show (wr_rgb (rescaleDir p.1 α) * p.1.D + wr_rgb p.1 * (0 : Matrix d dOut ℝ)) i o
    = α 0 i * (wr_rgb p.1 * p.1.D) i o
  rw [Matrix.mul_zero, add_zero, Matrix.mul_apply, Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  show α 0 i * p.1.write 0 i k * p.1.D k o = α 0 i * (p.1.write 0 i k * p.1.D k o)
  ring

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: along a rescaling of the gates, the gate column `c_i` of `C` moves by `β_i c_i`. -/
private theorem dCm_gate_inl_rgb (k : ℕ)
    (p : ParamsB (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (β : ∀ ℓ, hid ℓ → ℝ) (a : dIn) (i : hid 0) :
    dCm_rgb p.1 (rescaleDirGateB k p β).1 a (Sum.inl i) = β 0 i * Cm_rgb p.1 a (Sum.inl i) := by
  show ((0 : Matrix dIn d ℝ) * rd_rgb p.1 + p.1.E * rd_rgb (rescaleDirGate k p.1 β)) a (Sum.inl i)
    = β 0 i * (p.1.E * rd_rgb p.1) a (Sum.inl i)
  rw [Matrix.zero_mul, zero_add, Matrix.mul_apply, Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  show p.1.E a j * (β 0 i * p.1.read 0 j (Sum.inl i))
    = β 0 i * (p.1.E a j * p.1.read 0 j (Sum.inl i))
  ring

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: along a rescaling of the gates, the value columns of `C` do not move. -/
private theorem dCm_gate_inr_rgb (k : ℕ)
    (p : ParamsB (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (β : ∀ ℓ, hid ℓ → ℝ) (a : dIn) (i : hid 0) :
    dCm_rgb p.1 (rescaleDirGateB k p β).1 a (Sum.inr i) = 0 := by
  show ((0 : Matrix dIn d ℝ) * rd_rgb p.1 + p.1.E * rd_rgb (rescaleDirGate k p.1 β)) a (Sum.inr i)
    = 0
  rw [Matrix.zero_mul, zero_add, Matrix.mul_apply]
  exact Finset.sum_eq_zero fun j _ => mul_eq_zero_of_right _ rfl

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: along a rescaling of the gates (`k = 1`), the row `a_i` of `A` moves by
`-β_i a_i`. -/
private theorem dAm_gate_rgb (p : ParamsB (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (β : ∀ ℓ, hid ℓ → ℝ) (i : hid 0) (o : dOut) :
    dAm_rgb p.1 (rescaleDirGateB 1 p β).1 i o = -(β 0 i) * Am_rgb p.1 i o := by
  show (wr_rgb (rescaleDirGate 1 p.1 β) * p.1.D + wr_rgb p.1 * (0 : Matrix d dOut ℝ)) i o
    = -(β 0 i) * (wr_rgb p.1 * p.1.D) i o
  rw [Matrix.mul_zero, add_zero, Matrix.mul_apply, Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  show -(((1 : ℕ) : ℝ) * β 0 i) * p.1.write 0 i j * p.1.D j o
    = -(β 0 i) * (p.1.write 0 i j * p.1.D j o)
  rw [Nat.cast_one]
  ring

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: along a rescaling of the values, the gate biases `β_i` do not move. -/
private theorem dβm_value_inl_rgb (p : ParamsB (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (α : ∀ ℓ, hid ℓ → ℝ) (i : hid 0) :
    dβm_rgb p.1 p.2 (rescaleDirB p α).1 (rescaleDirB p α).2 (Sum.inl i) = 0 := by
  show (0 ᵥ* rd_rgb p.1) (Sum.inl i)
      + ∑ k, p.2.E k * (rescaleDir p.1 α).read 0 k (Sum.inl i) + 0 = 0
  rw [Matrix.zero_vecMul, Pi.zero_apply, zero_add, add_zero]
  exact Finset.sum_eq_zero fun k _ => mul_eq_zero_of_right _ rfl

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: along a rescaling of the values, the value bias `β'_i` moves by `-α_i β'_i`. -/
private theorem dβm_value_inr_rgb (p : ParamsB (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (α : ∀ ℓ, hid ℓ → ℝ) (i : hid 0) :
    dβm_rgb p.1 p.2 (rescaleDirB p α).1 (rescaleDirB p α).2 (Sum.inr i)
      = -(α 0 i) * βm_rgb p.1 p.2 (Sum.inr i) := by
  show (0 ᵥ* rd_rgb p.1) (Sum.inr i)
      + ∑ k, p.2.E k * (-(α 0 i) * p.1.read 0 k (Sum.inr i)) + -(α 0 i) * p.2.read 0 (Sum.inr i)
    = -(α 0 i) * (∑ k, p.2.E k * p.1.read 0 k (Sum.inr i) + p.2.read 0 (Sum.inr i))
  rw [Matrix.zero_vecMul, Pi.zero_apply, zero_add, mul_add, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun k _ => by ring

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: along a rescaling of the gates, the gate bias `β_i` moves by `β_i` times itself. -/
private theorem dβm_gate_inl_rgb (k : ℕ)
    (p : ParamsB (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (β : ∀ ℓ, hid ℓ → ℝ) (i : hid 0) :
    dβm_rgb p.1 p.2 (rescaleDirGateB k p β).1 (rescaleDirGateB k p β).2 (Sum.inl i)
      = β 0 i * βm_rgb p.1 p.2 (Sum.inl i) := by
  show (0 ᵥ* rd_rgb p.1) (Sum.inl i)
      + ∑ a, p.2.E a * (β 0 i * p.1.read 0 a (Sum.inl i)) + β 0 i * p.2.read 0 (Sum.inl i)
    = β 0 i * (∑ a, p.2.E a * p.1.read 0 a (Sum.inl i) + p.2.read 0 (Sum.inl i))
  rw [Matrix.zero_vecMul, Pi.zero_apply, zero_add, mul_add, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun a _ => by ring

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: along a rescaling of the gates, the value biases do not move. -/
private theorem dβm_gate_inr_rgb (k : ℕ)
    (p : ParamsB (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (β : ∀ ℓ, hid ℓ → ℝ) (i : hid 0) :
    dβm_rgb p.1 p.2 (rescaleDirGateB k p β).1 (rescaleDirGateB k p β).2 (Sum.inr i) = 0 := by
  show (0 ᵥ* rd_rgb p.1) (Sum.inr i)
      + ∑ a, p.2.E a * (rescaleDirGate k p.1 β).read 0 a (Sum.inr i) + 0 = 0
  rw [Matrix.zero_vecMul, Pi.zero_apply, zero_add, add_zero]
  exact Finset.sum_eq_zero fun a _ => mul_eq_zero_of_right _ rfl

/-- Helper (Steps 2 and 3 of the proof, for every stream matrix `S`): under the conditions, a
direction `η` that is flat at every input of `noKinkGateB p` keeps `M_S` and `γ_S` to first
order, and after the removal of a rescaling of the values and one of the gates (with their
biases) it keeps `C`, `A` and `β` to first order; its weights are then two changes of basis
(Lemma C.2). -/
private theorem flatOnB_aux_rgb (S : Fin 1 → Matrix d d ℝ)
    (p : ParamsB (Arch.gated (T := T) (d := d) relu id hid) dIn dOut)
    (hp : OneBlockGenericReGLU p.1)
    (η : ParamsB (Arch.gated (T := T) (d := d) relu id hid) dIn dOut)
    (hη : η ∈ flatOnB (Arch.gated relu id hid) S p (noKinkGateB p)) :
    dMm_rgb S p.1 η.1 = 0 ∧ dγm_rgb S p.1 p.2 η.1 η.2 = 0 ∧
      ∃ (α β : ∀ ℓ, hid ℓ → ℝ) (X : Fin 2 → Matrix d d ℝ),
        (η - rescaleDirB p α - rescaleDirGateB 1 p β).1 = cobDir p.1 X ∧
        dβm_rgb p.1 p.2 (η - rescaleDirB p α - rescaleDirGateB 1 p β).1
          (η - rescaleDirB p α - rescaleDirGateB 1 p β).2 = 0 := by
  -- Lemma B.3 for ReGLU with the linear term `x ∂M_S` and the constant `∂γ_S` (inputs `x` with
  -- all rows equal to a `v` with `v c_i + β_i ≠ 0` for all `i`): `∂M_S = 0`, `∂γ_S = 0`,
  -- `(∂c_i, ∂β_i) = λ_i (c_i, β_i)`, `(∂e_i, ∂β'_i) = -α_i (e_i, β'_i)`, `∂a_i = (α_i - λ_i) a_i`
  obtain ⟨hm, hγ, lam, α, hlam⟩ := relu_gated_units_flat
    (fun i => (Cm_rgb p.1)ᵀ (Sum.inl i)) (fun i => βm_rgb p.1 p.2 (Sum.inl i))
    (fun i => (Cm_rgb p.1)ᵀ (Sum.inr i)) (fun i => βm_rgb p.1 p.2 (Sum.inr i))
    (fun i => Am_rgb p.1 i) (dMm_rgb S p.1 η.1) (dγm_rgb S p.1 p.2 η.1 η.2)
    (fun i => (dCm_rgb p.1 η.1)ᵀ (Sum.inl i)) (fun i => dβm_rgb p.1 p.2 η.1 η.2 (Sum.inl i))
    (fun i => (dCm_rgb p.1 η.1)ᵀ (Sum.inr i)) (fun i => dβm_rgb p.1 p.2 η.1 η.2 (Sum.inr i))
    (fun i => dAm_rgb p.1 η.1 i) (fun i => hp.gated.row_ne_zero i)
    (fun i => hp.gated.gate_ne_zero i) (fun i j hij => hp.gated.gate_not_collinear i j hij)
    (fun i => hp.gated.value_ne_zero i)
    (fun i r h => hp.value_not_gate i r (by have h1 := congrArg Prod.fst h; exact h1)) (by
      intro v hv
      have hx : (Matrix.of fun _ : T => v) ∈ noKinkGateB p := by
        intro t i
        have h := hv i
        rw [Matrix.mul_assoc]
        exact h
      funext o
      have h := flat_apply_rgb S p η hη _ hx (Classical.arbitrary T) o
      rw [fderiv_evalB_apply_rgb S p η _ hx] at h
      simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      exact h)
  refine ⟨hm, hγ, ?_⟩
  -- the rescalings with these `α_i` and `λ_i` (one block: `ℓ = 0`)
  obtain ⟨α', hα'⟩ : ∃ α' : ∀ ℓ : Fin 1, hid ℓ → ℝ, α' 0 = α :=
    ⟨fun ℓ => Fin.cases α (fun l => l.elim0) ℓ, rfl⟩
  obtain ⟨β', hβ'⟩ : ∃ β' : ∀ ℓ : Fin 1, hid ℓ → ℝ, β' 0 = lam :=
    ⟨fun ℓ => Fin.cases lam (fun l => l.elim0) ℓ, rfl⟩
  -- `η - rescaleDirB p α' - rescaleDirGateB 1 p β'` keeps `C`, `A` and `β` to first order
  have hC : dCm_rgb p.1 (η - rescaleDirB p α' - rescaleDirGateB 1 p β').1 = 0 := by
    ext a j
    rcases j with i | i
    · rw [dCm_sub_rgb, dCm_sub_rgb, Matrix.sub_apply, Matrix.sub_apply, dCm_value_inl_rgb,
        dCm_gate_inl_rgb, sub_zero, Matrix.zero_apply, sub_eq_zero, hβ']
      exact congrFun (hlam i).1 a
    · rw [dCm_sub_rgb, dCm_sub_rgb, Matrix.sub_apply, Matrix.sub_apply, dCm_value_inr_rgb,
        dCm_gate_inr_rgb, sub_zero, Matrix.zero_apply, sub_eq_zero, hα']
      exact congrFun (hlam i).2.2.1 a
  have hA : dAm_rgb p.1 (η - rescaleDirB p α' - rescaleDirGateB 1 p β').1 = 0 := by
    ext i o
    rw [dAm_sub_rgb, dAm_sub_rgb, Matrix.sub_apply, Matrix.sub_apply, dAm_value_rgb, dAm_gate_rgb,
      Matrix.zero_apply, hα', hβ']
    have h : dAm_rgb p.1 η.1 i o = (α i - lam i) * Am_rgb p.1 i o := congrFun (hlam i).2.2.2.2 o
    rw [h]
    ring
  have hb : dβm_rgb p.1 p.2 (η - rescaleDirB p α' - rescaleDirGateB 1 p β').1
      (η - rescaleDirB p α' - rescaleDirGateB 1 p β').2 = 0 := by
    funext j
    rcases j with i | i
    · rw [dβm_sub_rgb, dβm_sub_rgb, Pi.sub_apply, Pi.sub_apply, dβm_value_inl_rgb,
        dβm_gate_inl_rgb, sub_zero, Pi.zero_apply, sub_eq_zero, hβ']
      exact (hlam i).2.1
    · rw [dβm_sub_rgb, dβm_sub_rgb, Pi.sub_apply, Pi.sub_apply, dβm_value_inr_rgb,
        dβm_gate_inr_rgb, sub_zero, Pi.zero_apply, sub_eq_zero, hα']
      exact (hlam i).2.2.2.1
  -- Lemma C.2: a direction that keeps `C` and `A` moves the weights by two changes of basis
  obtain ⟨X, hX⟩ := (keeps_products_iff_mem_range_cobDir p.1
    (η - rescaleDirB p α' - rescaleDirGateB 1 p β').1 hp.gated.rank_E hp.gated.rank_D
    hp.gated.rank_read hp.gated.rank_write).1 ⟨hC, hA⟩
  exact ⟨α', β', X, hX, hb⟩

/-- **Lemma B.2 with biases, after Lemma B.3, for one skipless ReGLU block:** under the conditions
`OneBlockGenericReGLU` on the weights, a direction that is flat at every input with no gate at
its kink is the sum of the direction of changes of basis `X_0, X_1` and translations `g_0, g_1`
of the two hidden states, a direction of the rescalings of the values and a direction of the
rescalings of the gates, with their biases. -/
theorem flatOnB_noKinkGateB_le_reglu
    (p : ParamsB (Arch.gated (T := T) (d := d) relu id hid) dIn dOut)
    (hp : OneBlockGenericReGLU p.1)
    (η : ParamsB (Arch.gated (T := T) (d := d) relu id hid) dIn dOut)
    (hη : η ∈ flatOnB (Arch.gated relu id hid) 0 p (noKinkGateB p)) :
    ∃ (X : Fin 2 → Matrix d d ℝ) (g : Fin 2 → d → ℝ) (α β : ∀ ℓ, hid ℓ → ℝ),
      η = cobDirB p X + (0, translateAtDir p.1 g) + rescaleDirB p α + rescaleDirGateB 1 p β := by
  -- Steps 2 and 3 with the stream matrix `0`: after the two rescalings, `ρ` keeps `C`, `A`, `β`
  -- and `γ_0`, and its weights are the changes of basis `X_0, X_1`
  obtain ⟨-, hγ, α, β, X, hX, hβ⟩ := flatOnB_aux_rgb 0 p hp η hη
  obtain ⟨ρ, hρ⟩ : ∃ ρ, ρ = η - rescaleDirB p α - rescaleDirGateB 1 p β := ⟨_, rfl⟩
  rw [← hρ] at hX hβ
  -- the rescalings do not move `D`, `b_E`, `b_write`, `b_D`
  have hρE : ρ.2.E = η.2.E := by
    rw [hρ]
    show η.2.E - 0 - 0 = η.2.E
    rw [sub_zero, sub_zero]
  have hρW : ρ.2.write 0 = η.2.write 0 := by
    rw [hρ]
    show η.2.write 0 - 0 - 0 = η.2.write 0
    rw [sub_zero, sub_zero]
  have hρD : ρ.2.D = η.2.D := by
    rw [hρ]
    show η.2.D - 0 - 0 = η.2.D
    rw [sub_zero, sub_zero]
  have hρ1D : ρ.1.D = η.1.D := by
    rw [hρ]
    show η.1.D - 0 - 0 = η.1.D
    rw [sub_zero, sub_zero]
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
    have h : ρ.2.write 0 ᵥ* p.1.D + p.2.write 0 ᵥ* ρ.1.D + ρ.2.D = 0 := by
      rw [hρW, hρ1D, hρD]
      simpa only [dγm_rgb, Pi.zero_apply, Matrix.zero_mul, Matrix.vecMul_zero, zero_add]
        using hγ
    rw [hD, Matrix.vecMul_neg, ← Matrix.vecMul_vecMul] at h
    rw [Matrix.sub_vecMul]
    linear_combination h
  -- so `ρ` is the direction of the changes of basis `X` and of the translations `g_0, g_1`
  have key : ρ = cobDirB p X
      + (0, translateAtDir p.1 ![ρ.2.E - p.2.E ᵥ* X 0, ρ.2.write 0 - p.2.write 0 ᵥ* X 1]) := by
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
  refine ⟨X, ![ρ.2.E - p.2.E ᵥ* X 0, ρ.2.write 0 - p.2.write 0 ᵥ* X 1], α, β, ?_⟩
  rw [← key, hρ]
  abel

/-! ### Helpers: the directions of changes of basis, translations and rescalings, as linear
maps -/

omit [Fintype T] [Nonempty T] in
/-- Helper (copy of `cobTrAtLin_mlb` of `MlpBiases.lean`): `(X, g) ↦ cobDirB p X +
(0, translateAtDir θ g)`, as a linear map. -/
private noncomputable def cobTrAtLin_rgb {L : ℕ} {A : Arch T d L} (p : ParamsB A dIn dOut) :
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
/-- Helper (copy of `cobTrLin_mlb` of `MlpBiases.lean`): `(X, g) ↦ cobDirB p (X, …, X) +
(0, translateDir θ g)`, as a linear map. -/
private noncomputable def cobTrLin_rgb {L : ℕ} {A : Arch T d L} (p : ParamsB A dIn dOut) :
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

/-- Helper (copy of `rescaleDirBLin_brc` of `BiasesRescaleCount.lean`): `α ↦ rescaleDirB p α` is
linear. -/
private noncomputable def rescaleDirBLin_rgb
    (p : ParamsB (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) :
    (∀ ℓ, hid ℓ → ℝ) →ₗ[ℝ] ParamsB (Arch.gated (T := T) (d := d) σ id hid) dIn dOut where
  toFun := rescaleDirB p
  map_add' α β := by
    refine Prod.ext (Params.ext' ?_ (fun ℓ => ?_) (fun ℓ => ?_) ?_)
      (Biases.ext' ?_ (fun ℓ => ?_) (fun ℓ => ?_) ?_)
    · simp [rescaleDirB, rescaleDir]
    · ext a j
      cases j with
      | inl i => simp [rescaleDirB, rescaleDir]
      | inr i =>
        simp only [rescaleDirB, rescaleDir, Prod.fst_add, Params.add_read, Pi.add_apply,
          Matrix.add_apply, Matrix.of_apply, Sum.elim_inr]
        ring
    · ext i a
      simp only [rescaleDirB, rescaleDir, Prod.fst_add, Params.add_write, Pi.add_apply,
        Matrix.add_apply, Matrix.of_apply]
      ring
    · simp [rescaleDirB, rescaleDir]
    · simp [rescaleDirB]
    · funext j
      cases j with
      | inl i => simp [rescaleDirB]
      | inr i =>
        simp only [rescaleDirB, Prod.snd_add, Biases.add_read, Pi.add_apply, Sum.elim_inr]
        ring
    · simp [rescaleDirB]
    · simp [rescaleDirB]
  map_smul' c α := by
    refine Prod.ext (Params.ext' ?_ (fun ℓ => ?_) (fun ℓ => ?_) ?_)
      (Biases.ext' ?_ (fun ℓ => ?_) (fun ℓ => ?_) ?_)
    · simp [rescaleDirB, rescaleDir]
    · ext a j
      cases j with
      | inl i => simp [rescaleDirB, rescaleDir]
      | inr i =>
        simp only [rescaleDirB, rescaleDir, Prod.smul_fst, Params.smul_read, Pi.smul_apply,
          Matrix.smul_apply, Matrix.of_apply, Sum.elim_inr, smul_eq_mul, RingHom.id_apply]
        ring
    · ext i a
      simp only [rescaleDirB, rescaleDir, Prod.smul_fst, Params.smul_write, Pi.smul_apply,
        Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, RingHom.id_apply]
      ring
    · simp [rescaleDirB, rescaleDir]
    · simp [rescaleDirB]
    · funext j
      cases j with
      | inl i => simp [rescaleDirB]
      | inr i =>
        simp only [rescaleDirB, Prod.smul_snd, Biases.smul_read, Pi.smul_apply, Sum.elim_inr,
          smul_eq_mul, RingHom.id_apply]
        ring
    · simp [rescaleDirB]
    · simp [rescaleDirB]

/-- Helper (copy of `rescaleDirGateBLin_brc` of `BiasesRescaleCount.lean`):
`β ↦ rescaleDirGateB k p β` is linear. -/
private noncomputable def rescaleDirGateBLin_rgb (k : ℕ)
    (p : ParamsB (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) :
    (∀ ℓ, hid ℓ → ℝ) →ₗ[ℝ] ParamsB (Arch.gated (T := T) (d := d) σ id hid) dIn dOut where
  toFun := rescaleDirGateB k p
  map_add' α β := by
    refine Prod.ext (Params.ext' ?_ (fun ℓ => ?_) (fun ℓ => ?_) ?_)
      (Biases.ext' ?_ (fun ℓ => ?_) (fun ℓ => ?_) ?_)
    · simp [rescaleDirGateB, rescaleDirGate]
    · ext a j
      cases j with
      | inl i =>
        simp only [rescaleDirGateB, rescaleDirGate, Prod.fst_add, Params.add_read, Pi.add_apply,
          Matrix.add_apply, Matrix.of_apply, Sum.elim_inl]
        ring
      | inr i => simp [rescaleDirGateB, rescaleDirGate]
    · ext i a
      simp only [rescaleDirGateB, rescaleDirGate, Prod.fst_add, Params.add_write, Pi.add_apply,
        Matrix.add_apply, Matrix.of_apply]
      ring
    · simp [rescaleDirGateB, rescaleDirGate]
    · simp [rescaleDirGateB]
    · funext j
      cases j with
      | inl i =>
        simp only [rescaleDirGateB, Prod.snd_add, Biases.add_read, Pi.add_apply, Sum.elim_inl]
        ring
      | inr i => simp [rescaleDirGateB]
    · simp [rescaleDirGateB]
    · simp [rescaleDirGateB]
  map_smul' c α := by
    refine Prod.ext (Params.ext' ?_ (fun ℓ => ?_) (fun ℓ => ?_) ?_)
      (Biases.ext' ?_ (fun ℓ => ?_) (fun ℓ => ?_) ?_)
    · simp [rescaleDirGateB, rescaleDirGate]
    · ext a j
      cases j with
      | inl i =>
        simp only [rescaleDirGateB, rescaleDirGate, Prod.smul_fst, Params.smul_read,
          Pi.smul_apply, Matrix.smul_apply, Matrix.of_apply, Sum.elim_inl, smul_eq_mul,
          RingHom.id_apply]
        ring
      | inr i => simp [rescaleDirGateB, rescaleDirGate]
    · ext i a
      simp only [rescaleDirGateB, rescaleDirGate, Prod.smul_fst, Params.smul_write,
        Pi.smul_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, RingHom.id_apply]
      ring
    · simp [rescaleDirGateB, rescaleDirGate]
    · simp [rescaleDirGateB]
    · funext j
      cases j with
      | inl i =>
        simp only [rescaleDirGateB, Prod.smul_snd, Biases.smul_read, Pi.smul_apply,
          Sum.elim_inl, smul_eq_mul, RingHom.id_apply]
        ring
      | inr i => simp [rescaleDirGateB]
    · simp [rescaleDirGateB]
    · simp [rescaleDirGateB]

/-- Helper: `((X, g), (α, β)) ↦ cobDirB p X + (0, translateAtDir θ g) + rescaleDirB p α
+ rescaleDirGateB 1 p β`, as a linear map. -/
private noncomputable def dirB_rgb
    (p : ParamsB (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) :
    ((Fin (1 + 1) → Matrix d d ℝ) × (Fin (1 + 1) → d → ℝ))
      × ((∀ ℓ : Fin 1, hid ℓ → ℝ) × (∀ ℓ : Fin 1, hid ℓ → ℝ)) →ₗ[ℝ]
      ParamsB (Arch.gated (T := T) (d := d) σ id hid) dIn dOut :=
  (cobTrAtLin_rgb p).coprod ((rescaleDirBLin_rgb p).coprod (rescaleDirGateBLin_rgb 1 p))

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the values of `dirB_rgb`. -/
private theorem dirB_apply_rgb (p : ParamsB (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (v : ((Fin (1 + 1) → Matrix d d ℝ) × (Fin (1 + 1) → d → ℝ))
      × ((∀ ℓ : Fin 1, hid ℓ → ℝ) × (∀ ℓ : Fin 1, hid ℓ → ℝ))) :
    dirB_rgb p v = cobDirB p v.1.1 + (0, translateAtDir p.1 v.1.2)
      + (rescaleDirB p v.2.1 + rescaleDirGateB 1 p v.2.2) := rfl

/-- Helper: `((X, g), (α, β)) ↦ cobDirB p (X, X) + (0, translateDir θ g) + rescaleDirB p α
+ rescaleDirGateB 1 p β`, as a linear map. -/
private noncomputable def dirBR_rgb
    (p : ParamsB (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) :
    (Matrix d d ℝ × (Fin (1 + 1) → d → ℝ))
      × ((∀ ℓ : Fin 1, hid ℓ → ℝ) × (∀ ℓ : Fin 1, hid ℓ → ℝ)) →ₗ[ℝ]
      ParamsB (Arch.gated (T := T) (d := d) σ id hid) dIn dOut :=
  (cobTrLin_rgb p).coprod ((rescaleDirBLin_rgb p).coprod (rescaleDirGateBLin_rgb 1 p))

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the values of `dirBR_rgb`. -/
private theorem dirBR_apply_rgb (p : ParamsB (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (v : (Matrix d d ℝ × (Fin (1 + 1) → d → ℝ))
      × ((∀ ℓ : Fin 1, hid ℓ → ℝ) × (∀ ℓ : Fin 1, hid ℓ → ℝ))) :
    dirBR_rgb p v = cobDirB p (fun _ => v.1.1) + (0, translateDir p.1 v.1.2)
      + (rescaleDirB p v.2.1 + rescaleDirGateB 1 p v.2.2) := rfl

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (copy of `finrank_cobTrAtDomain_mlb`): the pairs `(X, g)` of `L + 1` changes of basis
and `L + 1` translations form a space of dimension `(L + 1) d² + (L + 1) d`. -/
private theorem finrank_cobTrAtDomain_rgb (L : ℕ) :
    Module.finrank ℝ ((Fin (L + 1) → Matrix d d ℝ) × (Fin (L + 1) → d → ℝ))
      = (L + 1) * Fintype.card d ^ 2 + (L + 1) * Fintype.card d := by
  rw [Module.finrank_prod, finrank_cobDomain, Module.finrank_pi_fintype]
  simp only [Module.finrank_fintype_fun_eq_card, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul]

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (copy of `finrank_cobTrDomain_mlb`): the pairs `(X, g)` of one change of basis and
`L + 1` translations form a space of dimension `d² + (L + 1) d`. -/
private theorem finrank_cobTrDomain_rgb (L : ℕ) :
    Module.finrank ℝ (Matrix d d ℝ × (Fin (L + 1) → d → ℝ))
      = Fintype.card d ^ 2 + (L + 1) * Fintype.card d := by
  rw [Module.finrank_prod, Module.finrank_matrix, Module.finrank_pi_fintype]
  simp only [Module.finrank_self, Module.finrank_fintype_fun_eq_card, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one, sq]

omit [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the numbers `α` on the hidden units of the one block form a space of dimension
`d_hidden`. -/
private theorem finrank_hidFun_rgb :
    Module.finrank ℝ (∀ ℓ : Fin 1, hid ℓ → ℝ) = Fintype.card (hid 0) := by
  rw [Module.finrank_pi_fintype]
  simp only [Module.finrank_fintype_fun_eq_card, Finset.univ_unique, Fin.default_eq_zero,
    Finset.sum_singleton]

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the domain of `dirB_rgb` has dimension `2 d² + 2 d + 2 d_hidden`. -/
private theorem finrank_dirBDomain_rgb :
    Module.finrank ℝ (((Fin (1 + 1) → Matrix d d ℝ) × (Fin (1 + 1) → d → ℝ))
        × ((∀ ℓ : Fin 1, hid ℓ → ℝ) × (∀ ℓ : Fin 1, hid ℓ → ℝ)))
      = 2 * Fintype.card d ^ 2 + 2 * Fintype.card d + 2 * Fintype.card (hid 0) := by
  rw [Module.finrank_prod, finrank_cobTrAtDomain_rgb, Module.finrank_prod, finrank_hidFun_rgb]
  ring

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the domain of `dirBR_rgb` has dimension `d² + 2 d + 2 d_hidden`. -/
private theorem finrank_dirBRDomain_rgb :
    Module.finrank ℝ ((Matrix d d ℝ × (Fin (1 + 1) → d → ℝ))
        × ((∀ ℓ : Fin 1, hid ℓ → ℝ) × (∀ ℓ : Fin 1, hid ℓ → ℝ)))
      = Fintype.card d ^ 2 + 2 * Fintype.card d + 2 * Fintype.card (hid 0) := by
  rw [Module.finrank_prod, finrank_cobTrDomain_rgb, Module.finrank_prod, finrank_hidFun_rgb]
  ring

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] in
/-- Helper (copy of `read_value_ne_zero_Q` of `ReGLU.lean`): under the conditions of the gated
blocks, no value column of `W_read` vanishes, since the value columns of `C = E W_read` do not. -/
private theorem read_value_ne_zero_rgb
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
/-- Helper (copy of `read_gate_ne_zero_Q`): likewise no gate column of `W_read` vanishes. -/
private theorem read_gate_ne_zero_rgb
    (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (hθ : OneBlockGenericGated θ) : ∀ ℓ i, (fun a => θ.read ℓ a (Sum.inl i)) ≠ 0 := by
  intro ℓ i h0
  obtain rfl := Subsingleton.elim ℓ 0
  apply hθ.gate_ne_zero i
  funext a
  show ∑ k, θ.E a k * θ.read 0 k (Sum.inl i) = 0
  exact Finset.sum_eq_zero fun k _ => by
    rw [show θ.read 0 k (Sum.inl i) = 0 from congrFun h0 k, mul_zero]

/-- Helper: the directions that are flat at every input of `noKinkGateB p` are among the
directions of `dirB_rgb p` (the previous theorem). -/
private theorem flatOnB_le_range_dirB_rgb
    (p : ParamsB (Arch.gated (T := T) (d := d) relu id hid) dIn dOut)
    (hp : OneBlockGenericReGLU p.1) :
    flatOnB (Arch.gated relu id hid) 0 p (noKinkGateB p) ≤ LinearMap.range (dirB_rgb p) := by
  intro η hη
  obtain ⟨X, g, α, β, rfl⟩ := flatOnB_noKinkGateB_le_reglu p hp η hη
  refine LinearMap.mem_range.2 ⟨((X, g), (α, β)), ?_⟩
  rw [dirB_apply_rgb]
  exact (add_assoc _ _ _).symm

/-- **Theorem B.1 (i) of the skips paper with biases, the skipless network, at one parameter, for
a ReGLU block:** under the conditions `OneBlockGenericReGLU` on the weights,
`fd = P − 2 d² − 2 d − 2 d_hidden`, with `P` counting the biases. -/
theorem funDimB_reglu_oneBlock
    (p : ParamsB (Arch.gated (T := T) (d := d) relu id hid) dIn dOut)
    (hp : OneBlockGenericReGLU p.1) :
    funDimB (Arch.gated relu id hid) 0 p
        + (2 * Fintype.card d ^ 2 + 2 * Fintype.card d + 2 * Fintype.card (hid 0))
      = Module.finrank ℝ (ParamsB (Arch.gated (T := T) (d := d) relu id hid) dIn dOut) := by
  -- `≤`: the changes of basis, the translations and the two rescalings are flat and independent
  -- (Lemma A.8 with `s = 2 d_hidden`)
  have hle := funDimB_add_le_skipless_gated_gate relu_homogeneous p hp.gated.rank_E
    (fun ℓ => by obtain rfl := Subsingleton.elim ℓ 0; exact hp.gated.rank_write)
    (read_value_ne_zero_rgb p.1 hp.gated) (read_gate_ne_zero_rgb p.1 hp.gated)
  rw [Fin.sum_univ_one] at hle
  -- `≥`: every flat direction is flat on `noKinkGateB p`, hence one of them (the previous
  -- theorem), and they span a space of dimension at most `2 d² + 2 d + 2 d_hidden`
  have h1 := Submodule.finrank_mono ((flatB_le_flatOnB (S := 0) p (noKinkGateB p)).trans
    (flatOnB_le_range_dirB_rgb p hp))
  have h2 := (LinearMap.finrank_range_le (dirB_rgb p)).trans_eq
    (finrank_dirBDomain_rgb (d := d) (hid := hid))
  -- `fd(θ, b) = P − dim K(θ, b)`
  have h3 := funDimB_add_finrank_flatB' (S := 0) p
  omega

/-- The same rank on a batch of inputs with no gate at its kink, as the paper takes the Jacobian
for ReGLU blocks. -/
theorem exists_jacobianRankB_reglu_oneBlock
    (p : ParamsB (Arch.gated (T := T) (d := d) relu id hid) dIn dOut)
    (hp : OneBlockGenericReGLU p.1) :
    ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i, X i ∈ noKinkGateB p) ∧
      jacobianRankB (Arch.gated relu id hid) 0 X p
          + (2 * Fintype.card d ^ 2 + 2 * Fintype.card d + 2 * Fintype.card (hid 0))
        = Module.finrank ℝ (ParamsB (Arch.gated (T := T) (d := d) relu id hid) dIn dOut) := by
  -- a batch of inputs of `noKinkGateB p`, where the output is differentiable in `(θ, b)`, with the
  -- rank `P − dim K_U(θ, b)`, `U = noKinkGateB p`
  obtain ⟨n, X, hX, h⟩ := exists_jacobianRankB_add_finrank_flatOnB (S := 0) p (noKinkGateB p)
    (fun x hx => differentiableAt_evalB_of_mem_noKinkGateB 0 p x hx)
  -- `dim K_U(θ, b) = 2 d² + 2 d + 2 d_hidden`: at most that (the previous theorem), at least
  -- `dim K(θ, b)`, which is that by the functional dimension
  have h1 := Submodule.finrank_mono (flatOnB_le_range_dirB_rgb p hp)
  have h2 := (LinearMap.finrank_range_le (dirB_rgb p)).trans_eq
    (finrank_dirBDomain_rgb (d := d) (hid := hid))
  have h3 := Submodule.finrank_mono (flatB_le_flatOnB (S := 0) p (noKinkGateB p))
  have h4 := funDimB_add_finrank_flatB' (S := 0) p
  have h5 := funDimB_reglu_oneBlock p hp
  exact ⟨n, X, hX, by omega⟩

/-! ### Helpers: linear algebra for the residual network -/

omit [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (copy of `cancel_left_of_rank_Q` of `ReGLU.lean`): a matrix whose rank is its number of
columns cancels on the left, via a left inverse. -/
private theorem cancel_left_of_rank_rgb {m n k : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (M : Matrix m n ℝ) (hM : M.rank = Fintype.card n) {X Y : Matrix n k ℝ}
    (h : M * X = M * Y) : X = Y := by
  obtain ⟨B, hB⟩ := Matrix.vecMul_surjective_iff_exists_left_inverse.mp
    (Matrix.vecMul_surjective_iff_rank_eq_card.mpr hM)
  have := congrArg (B * ·) h
  simpa only [← Matrix.mul_assoc, hB, Matrix.one_mul] using this

omit [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (copy of `cancel_right_of_rank_Q`): a matrix whose rank is its number of rows cancels
on the right, via a right inverse. -/
private theorem cancel_right_of_rank_rgb {m n k : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    (M : Matrix m n ℝ) (hM : M.rank = Fintype.card m) {X Y : Matrix k m ℝ}
    (h : X * M = Y * M) : X = Y := by
  obtain ⟨R, hR⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.mp
    (Matrix.mulVec_surjective_iff_rank_eq_card.mpr hM)
  have := congrArg (· * R) h
  simpa only [Matrix.mul_assoc, hR, Matrix.mul_one] using this

/-- **Lemma B.2 with biases, after Lemma B.3, for one residual ReGLU block:** under the conditions
`OneBlockGenericReGLU` on the weights, a direction that is flat for the residual network at every
input with no gate at its kink is the sum of the direction of one change of basis `X` of both
hidden states and of the translations `g_0, g_1` of Lemma A.8, a direction of the rescalings of
the values and a direction of the rescalings of the gates, with their biases. -/
theorem flatOnB_noKinkGateB_le_reglu_residual
    (p : ParamsB (Arch.gated (T := T) (d := d) relu id hid) dIn dOut)
    (hp : OneBlockGenericReGLU p.1)
    (η : ParamsB (Arch.gated (T := T) (d := d) relu id hid) dIn dOut)
    (hη : η ∈ flatOnB (Arch.gated relu id hid) 1 p (noKinkGateB p)) :
    ∃ (X : Matrix d d ℝ) (g : Fin 2 → d → ℝ) (α β : ∀ ℓ, hid ℓ → ℝ),
      η = cobDirB p (fun _ => X) + (0, translateDir p.1 g) + rescaleDirB p α
        + rescaleDirGateB 1 p β := by
  -- Steps 2 and 3 with the stream matrix `1`: `η` keeps `M = E D` and `γ`; after the two
  -- rescalings, `ρ` keeps `C`, `A`, `β`, and its weights are the changes of basis `X_0, X_1`
  obtain ⟨hm, hγ, α, β, X, hX, hβ⟩ := flatOnB_aux_rgb 1 p hp η hη
  obtain ⟨ρ, hρ⟩ : ∃ ρ, ρ = η - rescaleDirB p α - rescaleDirGateB 1 p β := ⟨_, rfl⟩
  rw [← hρ] at hX hβ
  -- the rescalings do not move `E`, `D`, `b_E`, `b_write`, `b_D`
  have hρE : ρ.2.E = η.2.E := by
    rw [hρ]
    show η.2.E - 0 - 0 = η.2.E
    rw [sub_zero, sub_zero]
  have hρW : ρ.2.write 0 = η.2.write 0 := by
    rw [hρ]
    show η.2.write 0 - 0 - 0 = η.2.write 0
    rw [sub_zero, sub_zero]
  have hρD : ρ.2.D = η.2.D := by
    rw [hρ]
    show η.2.D - 0 - 0 = η.2.D
    rw [sub_zero, sub_zero]
  have hρ1E : ρ.1.E = η.1.E := by
    rw [hρ]
    show η.1.E - 0 - 0 = η.1.E
    rw [sub_zero, sub_zero]
  have hρ1D : ρ.1.D = η.1.D := by
    rw [hρ]
    show η.1.D - 0 - 0 = η.1.D
    rw [sub_zero, sub_zero]
  have hE : ρ.1.E = p.1.E * X 0 := by rw [hX]; rfl
  have hR : ρ.1.read 0 = -(X 0 * p.1.read 0) := by rw [hX]; rfl
  have hD : ρ.1.D = -(X 1 * p.1.D) := by rw [hX]; rfl
  -- Lemma B.2: `∂M = E X_0 D − E X_1 D = 0`, so `X_0 = X_1` (`E` and `D` have rank `d`)
  have h01 : X 0 = X 1 := by
    have h : ρ.1.E * p.1.D + p.1.E * ρ.1.D = 0 := by
      rw [hρ1E, hρ1D]
      simpa only [dMm_rgb, Pi.one_apply, Matrix.mul_one] using hm
    rw [hE, hD, Matrix.mul_neg, Matrix.mul_assoc, add_neg_eq_zero] at h
    exact cancel_right_of_rank_rgb p.1.D hp.gated.rank_D
      (cancel_left_of_rank_rgb p.1.E hp.gated.rank_E h)
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
        + (ρ.2.write 0 ᵥ* p.1.D + p.2.write 0 ᵥ* ρ.1.D + ρ.2.D) = 0 := by
      rw [hρE, hρ1D, hρW, hρD]
      simpa only [dγm_rgb, Pi.one_apply, Matrix.one_mul] using hγ
    simp only [hD, Matrix.vecMul_neg, ← Matrix.vecMul_vecMul] at h
    rw [Matrix.add_vecMul, Matrix.sub_vecMul, Matrix.sub_vecMul]
    linear_combination h
  -- so `ρ` is the direction of the change of basis `X` and of the translations `g_0, g_1`
  have hI : Finset.Iic (0 : Fin 1).castSucc = {0} := by decide
  have key : ρ = cobDirB p (fun _ => X 0)
      + (0, translateDir p.1 ![ρ.2.E - p.2.E ᵥ* X 0, ρ.2.write 0 - p.2.write 0 ᵥ* X 0]) := by
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
  refine ⟨X 0, ![ρ.2.E - p.2.E ᵥ* X 0, ρ.2.write 0 - p.2.write 0 ᵥ* X 0], α, β, ?_⟩
  rw [← key, hρ]
  abel

/-- Helper: the directions that are flat for the residual network at every input of
`noKinkGateB p` are among the directions of `dirBR_rgb p` (the previous theorem). -/
private theorem flatOnB_le_range_dirBR_rgb
    (p : ParamsB (Arch.gated (T := T) (d := d) relu id hid) dIn dOut)
    (hp : OneBlockGenericReGLU p.1) :
    flatOnB (Arch.gated relu id hid) 1 p (noKinkGateB p) ≤ LinearMap.range (dirBR_rgb p) := by
  intro η hη
  obtain ⟨X, g, α, β, rfl⟩ := flatOnB_noKinkGateB_le_reglu_residual p hp η hη
  refine LinearMap.mem_range.2 ⟨((X, g), (α, β)), ?_⟩
  rw [dirBR_apply_rgb]
  exact (add_assoc _ _ _).symm

/-- **Theorem B.1 (i) of the skips paper with biases, the residual network, at one parameter, for
a ReGLU block:** under the conditions `OneBlockGenericReGLU` on the weights,
`fd = P − d² − 2 d − 2 d_hidden`, with `P` counting the biases. -/
theorem funDimB_reglu_oneBlock_residual
    (p : ParamsB (Arch.gated (T := T) (d := d) relu id hid) dIn dOut)
    (hp : OneBlockGenericReGLU p.1) :
    funDimB (Arch.gated relu id hid) 1 p
        + (Fintype.card d ^ 2 + 2 * Fintype.card d + 2 * Fintype.card (hid 0))
      = Module.finrank ℝ (ParamsB (Arch.gated (T := T) (d := d) relu id hid) dIn dOut) := by
  -- `≤`: one change of basis, the translations and the two rescalings are flat and independent
  have hle := funDimB_add_le_residual_gated_gate relu_homogeneous p hp.gated.rank_E
    (read_value_ne_zero_rgb p.1 hp.gated) (read_gate_ne_zero_rgb p.1 hp.gated)
  rw [Fin.sum_univ_one] at hle
  -- `≥`: every flat direction is one of them, and they span a space of dimension at most
  -- `d² + 2 d + 2 d_hidden`
  have h1 := Submodule.finrank_mono ((flatB_le_flatOnB (S := 1) p (noKinkGateB p)).trans
    (flatOnB_le_range_dirBR_rgb p hp))
  have h2 := (LinearMap.finrank_range_le (dirBR_rgb p)).trans_eq
    (finrank_dirBRDomain_rgb (d := d) (hid := hid))
  -- `fd(θ, b) = P − dim K(θ, b)`
  have h3 := funDimB_add_finrank_flatB' (S := 1) p
  omega

/-- The same rank on a batch of inputs with no gate at its kink. -/
theorem exists_jacobianRankB_reglu_oneBlock_residual
    (p : ParamsB (Arch.gated (T := T) (d := d) relu id hid) dIn dOut)
    (hp : OneBlockGenericReGLU p.1) :
    ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i, X i ∈ noKinkGateB p) ∧
      jacobianRankB (Arch.gated relu id hid) 1 X p
          + (Fintype.card d ^ 2 + 2 * Fintype.card d + 2 * Fintype.card (hid 0))
        = Module.finrank ℝ (ParamsB (Arch.gated (T := T) (d := d) relu id hid) dIn dOut) := by
  -- a batch of inputs of `noKinkGateB p` with the rank `P − dim K_U(θ, b)`
  obtain ⟨n, X, hX, h⟩ := exists_jacobianRankB_add_finrank_flatOnB (S := 1) p (noKinkGateB p)
    (fun x hx => differentiableAt_evalB_of_mem_noKinkGateB 1 p x hx)
  -- `dim K_U(θ, b) = d² + 2 d + 2 d_hidden`, as without the skip
  have h1 := Submodule.finrank_mono (flatOnB_le_range_dirBR_rgb p hp)
  have h2 := (LinearMap.finrank_range_le (dirBR_rgb p)).trans_eq
    (finrank_dirBRDomain_rgb (d := d) (hid := hid))
  have h3 := Submodule.finrank_mono (flatB_le_flatOnB (S := 1) p (noKinkGateB p))
  have h4 := funDimB_add_finrank_flatB' (S := 1) p
  have h5 := funDimB_reglu_oneBlock_residual p hp
  exact ⟨n, X, hX, by omega⟩

/-! ### At generic weights and biases -/

/-- **Theorem B.1 (i) with biases for one ReGLU block, without the skip:** for
`d_in, d_out, d_hidden ≥ d ≥ 2`, at generic weights and biases
`fd = P − 2 d² − 2 d − 2 d_hidden`. -/
theorem ae_funDimB_reglu_oneBlock
    (μ : Measure (ParamsB (Arch.gated (T := T) (d := d) relu id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ p ∂μ, funDimB (Arch.gated relu id hid) 0 p
        + (2 * Fintype.card d ^ 2 + 2 * Fintype.card d + 2 * Fintype.card (hid 0))
      = Module.finrank ℝ (ParamsB (Arch.gated (T := T) (d := d) relu id hid) dIn dOut) :=
  (ae_paramsB_of_forall_ae (fun ν _ => ae_oneBlockGenericReGLU ν hd hdIn hdOut hhid) μ).mono
    fun p hp => funDimB_reglu_oneBlock p hp

/-- **Theorem B.1 (i) with biases for one ReGLU block, without the skip, on the paper's inputs:**
the rank `P − 2 d² − 2 d − 2 d_hidden` on a batch of inputs with no gate at its kink. -/
theorem ae_exists_jacobianRankB_reglu_oneBlock
    (μ : Measure (ParamsB (Arch.gated (T := T) (d := d) relu id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ p ∂μ, ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i, X i ∈ noKinkGateB p) ∧
      jacobianRankB (Arch.gated relu id hid) 0 X p
          + (2 * Fintype.card d ^ 2 + 2 * Fintype.card d + 2 * Fintype.card (hid 0))
        = Module.finrank ℝ (ParamsB (Arch.gated (T := T) (d := d) relu id hid) dIn dOut) :=
  (ae_paramsB_of_forall_ae (fun ν _ => ae_oneBlockGenericReGLU ν hd hdIn hdOut hhid) μ).mono
    fun p hp => exists_jacobianRankB_reglu_oneBlock p hp

/-- **Theorem B.1 (i) with biases for one ReGLU block, with the skip:** for
`d_in, d_out, d_hidden ≥ d ≥ 2`, at generic weights and biases `fd = P − d² − 2 d − 2 d_hidden`. -/
theorem ae_funDimB_reglu_oneBlock_residual
    (μ : Measure (ParamsB (Arch.gated (T := T) (d := d) relu id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ p ∂μ, funDimB (Arch.gated relu id hid) 1 p
        + (Fintype.card d ^ 2 + 2 * Fintype.card d + 2 * Fintype.card (hid 0))
      = Module.finrank ℝ (ParamsB (Arch.gated (T := T) (d := d) relu id hid) dIn dOut) :=
  (ae_paramsB_of_forall_ae (fun ν _ => ae_oneBlockGenericReGLU ν hd hdIn hdOut hhid) μ).mono
    fun p hp => funDimB_reglu_oneBlock_residual p hp

/-- **Theorem B.1 (i) with biases for one ReGLU block, with the skip, on the paper's inputs:** the
rank `P − d² − 2 d − 2 d_hidden` on a batch of inputs with no gate at its kink. -/
theorem ae_exists_jacobianRankB_reglu_oneBlock_residual
    (μ : Measure (ParamsB (Arch.gated (T := T) (d := d) relu id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ p ∂μ, ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i, X i ∈ noKinkGateB p) ∧
      jacobianRankB (Arch.gated relu id hid) 1 X p
          + (Fintype.card d ^ 2 + 2 * Fintype.card d + 2 * Fintype.card (hid 0))
        = Module.finrank ℝ (ParamsB (Arch.gated (T := T) (d := d) relu id hid) dIn dOut) :=
  (ae_paramsB_of_forall_ae (fun ν _ => ae_oneBlockGenericReGLU ν hd hdIn hdOut hhid) μ).mono
    fun p hp => exists_jacobianRankB_reglu_oneBlock_residual p hp

/-- **Theorem B.1 (i) with biases for one ReGLU block:** at generic weights and biases the skip
raises the functional dimension by exactly `d²`. -/
theorem ae_funDimB_reglu_oneBlock_residual_eq_add
    (μ : Measure (ParamsB (Arch.gated (T := T) (d := d) relu id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ p ∂μ, funDimB (Arch.gated relu id hid) 1 p
      = funDimB (Arch.gated relu id hid) 0 p + Fintype.card d ^ 2 := by
  filter_upwards [ae_funDimB_reglu_oneBlock μ hd hdIn hdOut hhid,
    ae_funDimB_reglu_oneBlock_residual μ hd hdIn hdOut hhid] with p h0 h1
  omega

end Skips
