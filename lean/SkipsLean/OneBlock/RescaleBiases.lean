import SkipsLean.OneBlock.ResidualRescale
import SkipsLean.OneBlock.MlpBiases
import SkipsLean.Symmetry.BiasesRescaleCount
import SkipsLean.Dimension.FunctionalBiasesOn

/-!
# The one-block theorem with biases, for ReLU and ReLU² blocks

Paper (skips paper), Theorem B.1 (i): "Let the network have no normalization, with or without
biases, and let the block have width at least `d_model` […]. For generic parameters the skipless
network has functional dimension `P − 2 d_model² − s` and the residual network
`P − d_model² − s`; with biases on the embedding, the block and the readout, counted in `P`, both
values are `2 d_model` lower […]. Both networks satisfy the equality condition, and the skip
raises the functional dimension by exactly `d_model²`."

Appendix B, "Notation and flat directions": "For the ReLU-type activations, `F(θ, x)` is
differentiable in `θ` at the inputs `x` at which no hidden unit sits at its kink, which form an
open set of full measure, and "every input" means every such input." Step 3: "A rescaling of the
units by numbers `λ_i` is also a direction in parameter space: it scales column `i` of `W_read`
and entry `i` of `b_read` by `λ_i` and row `i` of `W_write` by `−λ_i` for ReLU, by `−2 λ_i` for
ReLU² […]. So every flat direction is the sum of a direction of the changes of basis and
translations of Lemma B.2 and a rescaling of the units".

Here, for one MLP block `Arch.mlp σ id hid` with biases (`Network/Biases.lean`) and an activation
that is positively homogeneous of degree `k`, differentiable away from `0`, with the conclusion
of Lemma B.3 with the rescalings (`UnitsRescale`, whose statement has the biases; ReLU with
`k = 1`, ReLU² with `k = 2`), under the conditions `OneBlockGeneric` on the weights;
`s = d_hidden`. The twins: `OneBlock/Rescale.lean` and `OneBlock/ResidualRescale.lean` without
biases, `OneBlock/MlpBiases.lean` for `s = 0` with biases.

* `noKinkB p`: the inputs at which no hidden unit sits at its kink: every pre-activation
  `(x E W_read)_{t,i} + β_i`, `β = b_E W_read + b_read`, is nonzero. With biases the kinks are
  hyperplanes that need not pass through the origin.
* `differentiableAt_evalB_of_mem_noKinkB`: at such an input the output is differentiable in the
  weights and biases, with the skip and without it.
* `flatOnB_noKinkB_le_mlp_rescale`, `flatOnB_noKinkB_le_mlp_rescale_residual`: a direction that is
  flat at every such input is the sum of a direction of changes of basis and translations and of
  a direction of the rescalings of the units with their biases (`rescaleDirMlpB`).
* `funDimB_mlp_oneBlock_rescale`, `funDimB_mlp_oneBlock_rescale_residual`:
  `fd = P − 2 d² − 2 d − d_hidden` without the skip and `fd = P − d² − 2 d − d_hidden` with it,
  `P` counting the biases. As without biases, Lean's functional dimension uses every input at
  which the output is differentiable in the parameters, a set that contains `noKinkB p`; so the
  value is stated together with
* `exists_jacobianRankB_mlp_oneBlock_rescale`, `exists_jacobianRankB_mlp_oneBlock_rescale_residual`:
  the same rank on a finite batch of inputs with no hidden unit at its kink (the paper's inputs).
* The same at generic `(θ, b)` for `d_in, d_out, d_hidden ≥ d ≥ 2`, and "the skip raises the
  functional dimension by exactly `d_model²`"; named for ReLU and ReLU².

Numeric check (ReLU and ReLU², `d = d_in = d_out = 2`, one block of 2 units, `P = 24`: 10 and
14): `ai_notes/biases_inside_blocks_check_2026-11-25.py`.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {hid : Fin 1 → Type} [∀ ℓ, Fintype (hid ℓ)]
variable {σ σ' : ℝ → ℝ}

/-- The inputs at which no hidden unit of the block with biases sits at its kink: every
pre-activation `(x E W_read)_{t,i} + (b_E W_read + b_read)_i` (one per token and hidden unit) is
nonzero. -/
def noKinkB (p : ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) :
    Set (Matrix T dIn ℝ) :=
  {x | ∀ (t : T) (i : hid 0),
    (x * p.1.E * p.1.read 0) t i + (p.2.E ᵥ* p.1.read 0 + p.2.read 0) i ≠ 0}

/-! ### Helpers: the function of one MLP block with biases and its derivative -/

/-- Helper: the read of the block, with its columns indexed by the hidden units. -/
private def rd_rlb (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) :
    Matrix d (hid 0) ℝ :=
  θ.read 0

/-- Helper: the write of the block, with its rows indexed by the hidden units. -/
private def wr_rlb (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) :
    Matrix (hid 0) d ℝ :=
  θ.write 0

/-- Helper: `C = E W_read`. -/
private def Cm_rlb (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) :
    Matrix dIn (hid 0) ℝ :=
  θ.E * rd_rlb θ

/-- Helper: `A = W_write D`. -/
private def Am_rlb (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) :
    Matrix (hid 0) dOut ℝ :=
  wr_rlb θ * θ.D

/-- Helper: `β = b_E W_read + b_read`. -/
private def βm_rlb (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)
    (b : Biases (Arch.mlp (T := T) (d := d) σ id hid) dOut) : hid 0 → ℝ :=
  b.E ᵥ* rd_rlb θ + b.read 0

/-- Helper: `γ_0 = b_write D + b_D`. -/
private def γm_rlb (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)
    (b : Biases (Arch.mlp (T := T) (d := d) σ id hid) dOut) : dOut → ℝ :=
  b.write 0 ᵥ* θ.D + b.D

/-- Helper: the derivative `∂C = η_E W_read + E η_read` of `C` along `η`. -/
private def dCm_rlb (θ η : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) :
    Matrix dIn (hid 0) ℝ :=
  η.E * rd_rlb θ + θ.E * rd_rlb η

/-- Helper: the derivative `∂A = η_write D + W_write η_D` of `A` along `η`. -/
private def dAm_rlb (θ η : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) :
    Matrix (hid 0) dOut ℝ :=
  wr_rlb η * θ.D + wr_rlb θ * η.D

/-- Helper: the derivative `∂β = η_{b_E} W_read + b_E η_read + η_{b_read}` of `β`. -/
private def dβm_rlb (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)
    (b : Biases (Arch.mlp (T := T) (d := d) σ id hid) dOut)
    (η : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)
    (ηb : Biases (Arch.mlp (T := T) (d := d) σ id hid) dOut) : hid 0 → ℝ :=
  ηb.E ᵥ* rd_rlb θ + b.E ᵥ* rd_rlb η + ηb.read 0

/-- Helper: the derivative `∂γ_0 = η_{b_write} D + b_write η_D + η_{b_D}` of `γ_0`. -/
private def dγm_rlb (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)
    (b : Biases (Arch.mlp (T := T) (d := d) σ id hid) dOut)
    (η : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)
    (ηb : Biases (Arch.mlp (T := T) (d := d) σ id hid) dOut) : dOut → ℝ :=
  ηb.write 0 ᵥ* θ.D + b.write 0 ᵥ* η.D + ηb.D

omit [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the read is linear in the parameters. -/
private theorem rd_line_rlb (θ η : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)
    (τ : ℝ) : rd_rlb (θ + τ • η) = rd_rlb θ + τ • rd_rlb η := rfl

omit [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the write is linear in the parameters. -/
private theorem wr_line_rlb (θ η : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)
    (τ : ℝ) : wr_rlb (θ + τ • η) = wr_rlb θ + τ • wr_rlb η := rfl

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: along the line, `C(τ) = C + τ ∂C + τ² η_E η_read`. -/
private theorem Cm_line_rlb (θ η : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)
    (τ : ℝ) :
    Cm_rlb (θ + τ • η) = Cm_rlb θ + τ • dCm_rlb θ η + (τ * τ) • Cm_rlb η := by
  simp only [Cm_rlb, dCm_rlb, rd_line_rlb, Params.add_E, Params.smul_E, Matrix.mul_add,
    Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, smul_add, smul_smul]
  abel

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: along the line, `A(τ) = A + τ ∂A + τ² η_write η_D`. -/
private theorem Am_line_rlb (θ η : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)
    (τ : ℝ) :
    Am_rlb (θ + τ • η) = Am_rlb θ + τ • dAm_rlb θ η + (τ * τ) • Am_rlb η := by
  simp only [Am_rlb, dAm_rlb, wr_line_rlb, Params.add_D, Params.smul_D, Matrix.mul_add,
    Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, smul_add, smul_smul]
  abel

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: along the line, `β(τ) = β + τ ∂β + τ² η_{b_E} η_read`. -/
private theorem βm_line_rlb (θ η : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)
    (b ηb : Biases (Arch.mlp (T := T) (d := d) σ id hid) dOut) (τ : ℝ) :
    βm_rlb (θ + τ • η) (b + τ • ηb)
      = βm_rlb θ b + τ • dβm_rlb θ b η ηb + (τ * τ) • (ηb.E ᵥ* rd_rlb η) := by
  simp only [βm_rlb, dβm_rlb, rd_line_rlb, Biases.add_E, Biases.smul_E, Biases.add_read,
    Biases.smul_read, Matrix.vecMul_add, Matrix.add_vecMul, Matrix.vecMul_smul,
    Matrix.smul_vecMul, smul_add, smul_smul]
  abel

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: along the line, `γ_0(τ) = γ_0 + τ ∂γ_0 + τ² η_{b_write} η_D`. -/
private theorem γm_line_rlb (θ η : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)
    (b ηb : Biases (Arch.mlp (T := T) (d := d) σ id hid) dOut) (τ : ℝ) :
    γm_rlb (θ + τ • η) (b + τ • ηb)
      = γm_rlb θ b + τ • dγm_rlb θ b η ηb + (τ * τ) • (ηb.write 0 ᵥ* η.D) := by
  simp only [γm_rlb, dγm_rlb, Params.add_D, Params.smul_D, Biases.add_D, Biases.smul_D,
    Biases.add_write, Biases.smul_write, Matrix.vecMul_add, Matrix.add_vecMul,
    Matrix.vecMul_smul, Matrix.smul_vecMul, smul_add, smul_smul]
  abel

omit [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the matrix whose rows are all `v`, times `M`, has all rows `v M`. -/
private theorem of_const_mul_rlb {m n : Type*} [Fintype m] (v : m → ℝ) (M : Matrix m n ℝ) :
    (Matrix.of fun _ : T => v) * M = Matrix.of fun _ : T => v ᵥ* M := by
  ext t j
  rfl

omit [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the sum of two matrices with constant rows has constant rows. -/
private theorem of_const_add_rlb {n : Type*} (u v : n → ℝ) :
    (Matrix.of fun _ : T => u) + (Matrix.of fun _ : T => v) = Matrix.of fun _ : T => u + v :=
  rfl

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dOut] in
/-- Helper: the skipless network with biases, `F(θ, x) = γ_0 + σ(x C + β) A` (stream matrix
`0`). -/
private theorem evalB_mlp_eq_rlb (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)
    (b : Biases (Arch.mlp (T := T) (d := d) σ id hid) dOut) (x : Matrix T dIn ℝ) :
    evalB (Arch.mlp σ id hid) 0 θ b x
      = (Matrix.of fun _ : T => γm_rlb θ b)
        + (x * Cm_rlb θ + Matrix.of fun _ : T => βm_rlb θ b).map σ * Am_rlb θ := by
  have h1 : (Fin.last 1 : Fin 2) = (0 : Fin 1).succ := rfl
  have hχ : (Arch.mlp (T := T) (d := d) σ id hid).χ = id := rfl
  have hf : (Arch.mlp (T := T) (d := d) σ id hid).f 0 = fun M => M.map σ := rfl
  -- `h_1 = h_0 0 + σ(h_0 W_read + b_read) W_write + b_write` with `h_0 = x E + b_E`
  rw [evalB, h1, hiddenB_succ, Fin.castSucc_zero, hiddenB_zero, hχ, hf]
  simp only [Pi.zero_apply, Matrix.mul_zero, zero_add, id_eq, Matrix.add_mul, Matrix.mul_assoc,
    of_const_mul_rlb]
  rw [add_assoc (x * (θ.E * θ.read 0)), of_const_add_rlb, add_assoc, of_const_add_rlb, add_comm]
  rfl

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dOut] in
/-- Helper: the entries of `F(θ, x)`, `γ_{0,o} + ∑_i σ((x C)_{t i} + β_i) A_{i o}`. -/
private theorem evalB_mlp_apply_rlb
    (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)
    (b : Biases (Arch.mlp (T := T) (d := d) σ id hid) dOut) (x : Matrix T dIn ℝ) (t : T)
    (o : dOut) :
    evalB (Arch.mlp σ id hid) 0 θ b x t o
      = γm_rlb θ b o + ∑ i : hid 0, σ ((x * Cm_rlb θ) t i + βm_rlb θ b i) * Am_rlb θ i o := by
  rw [evalB_mlp_eq_rlb]
  rfl

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dOut] in
/-- Helper: the entries of `F(θ + τ η, b + τ η_b)(x)` as functions of `τ`. -/
private theorem evalB_line_apply_rlb
    (θ η : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)
    (b ηb : Biases (Arch.mlp (T := T) (d := d) σ id hid) dOut) (x : Matrix T dIn ℝ) (t : T)
    (o : dOut) (τ : ℝ) :
    evalB (Arch.mlp σ id hid) 0 (θ + τ • η) (b + τ • ηb) x t o
      = (γm_rlb θ b o + τ * dγm_rlb θ b η ηb o + τ * τ * (ηb.write 0 ᵥ* η.D) o)
        + ∑ i : hid 0,
          σ (((x * Cm_rlb θ) t i + τ * (x * dCm_rlb θ η) t i + τ * τ * (x * Cm_rlb η) t i)
              + (βm_rlb θ b i + τ * dβm_rlb θ b η ηb i + τ * τ * (ηb.E ᵥ* rd_rlb η) i))
            * (Am_rlb θ i o + τ * dAm_rlb θ η i o + τ * τ * Am_rlb η i o) := by
  rw [evalB_mlp_apply_rlb, Cm_line_rlb, Am_line_rlb, βm_line_rlb, γm_line_rlb]
  simp only [Matrix.mul_add, Matrix.mul_smul]
  rfl

/-! ### Helpers: the output of one block with biases is differentiable off the kinks -/

omit [Fintype T] [Nonempty T] [DecidableEq d] in
/-- Helper: a linear map on the parameters with biases is differentiable: the space is
finite-dimensional, so the map is continuous. -/
private theorem differentiable_linear_rlb {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (l : ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut →ₗ[ℝ] F) :
    Differentiable ℝ l := by
  rw [← LinearMap.coe_toContinuousLinearMap' l]
  exact (LinearMap.toContinuousLinearMap l).differentiable

omit [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the product of two matrix-valued maps that are differentiable at a point is
differentiable there (matrix multiplication is a continuous bilinear map). -/
private theorem differentiableAt_matMul_rlb {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m n q : Type*} [Fintype m] [Fintype n] [Fintype q]
    {f : E → Matrix m n ℝ} {g : E → Matrix n q ℝ} {y₀ : E}
    (hf : DifferentiableAt ℝ f y₀) (hg : DifferentiableAt ℝ g y₀) :
    DifferentiableAt ℝ (fun y => f y * g y) y₀ := by
  -- matrix multiplication as a bilinear map
  let B : Matrix m n ℝ →ₗ[ℝ] Matrix n q ℝ →ₗ[ℝ] Matrix m q ℝ :=
    LinearMap.mk₂ ℝ (fun a b => a * b) Matrix.add_mul (fun c a b => Matrix.smul_mul c a b)
      Matrix.mul_add (fun c a b => Matrix.mul_smul a c b)
  -- the same map with continuous linear maps (all spaces are finite-dimensional)
  let B' : Matrix m n ℝ →L[ℝ] Matrix n q ℝ →L[ℝ] Matrix m q ℝ :=
    LinearMap.toContinuousLinearMap
      ((LinearMap.toContinuousLinearMap :
        (Matrix n q ℝ →ₗ[ℝ] Matrix m q ℝ) ≃ₗ[ℝ] (Matrix n q ℝ →L[ℝ] Matrix m q ℝ)).toLinearMap ∘ₗ B)
  have hB : (fun y => f y * g y) = fun y => B' (f y) (g y) := rfl
  rw [hB]
  exact (B'.differentiableAt.comp y₀ hf).clm_apply hg

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dOut] in
/-- Helper: the network of one block with biases, for any stream matrix `S`:
`F = (h_0 S_0 + σ(h_0 W_read + b_read) W_write + b_write) D + b_D` with `h_0 = x E + b_E`. -/
private theorem evalB_mlp_S_eq_rlb (S : Fin 1 → Matrix d d ℝ)
    (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)
    (b : Biases (Arch.mlp (T := T) (d := d) σ id hid) dOut) (x : Matrix T dIn ℝ) :
    evalB (Arch.mlp σ id hid) S θ b x
      = ((x * θ.E + Matrix.of fun _ => b.E) * S 0
          + (((x * θ.E + Matrix.of fun _ => b.E) * θ.read 0
              + Matrix.of fun _ => b.read 0).map σ * θ.write 0
            + Matrix.of fun _ => b.write 0)) * θ.D + Matrix.of fun _ => b.D := by
  have h1 : (Fin.last 1 : Fin 2) = (0 : Fin 1).succ := rfl
  -- `h_1 = h_0 S_0 + σ(h_0 W_read + b_read) W_write + b_write` with `h_0 = x E + b_E`
  rw [evalB, h1, hiddenB_succ, Fin.castSucc_zero, hiddenB_zero]
  rfl

omit [Nonempty T] [DecidableEq d] in
/-- At an input with no hidden unit at its kink, the output of a network of one block with biases
is differentiable in the weights and biases, when `σ` is differentiable away from `0`; for every
stream matrix (with the skip and without it). -/
theorem differentiableAt_evalB_of_mem_noKinkB (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (p : ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) (S : Fin 1 → Matrix d d ℝ)
    (x : Matrix T dIn ℝ) (hx : x ∈ noKinkB p) :
    DifferentiableAt ℝ
      (fun q : ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut =>
        evalB (Arch.mlp σ id hid) S q.1 q.2 x) p := by
  -- the weights, and the matrices whose rows are the biases, are linear in `(θ, b)`
  have hE : Differentiable ℝ
      (fun q : ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut => q.1.E) :=
    differentiable_linear_rlb (F := Matrix dIn d ℝ)
      { toFun := fun q => q.1.E, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hR : Differentiable ℝ
      (fun q : ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut => q.1.read 0) :=
    differentiable_linear_rlb (F := Matrix d (hid 0) ℝ)
      { toFun := fun q => q.1.read 0, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hW : Differentiable ℝ
      (fun q : ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut => q.1.write 0) :=
    differentiable_linear_rlb (F := Matrix (hid 0) d ℝ)
      { toFun := fun q => q.1.write 0, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hD : Differentiable ℝ
      (fun q : ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut => q.1.D) :=
    differentiable_linear_rlb (F := Matrix d dOut ℝ)
      { toFun := fun q => q.1.D, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hbE : Differentiable ℝ (fun q : ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut =>
      Matrix.of fun _ : T => q.2.E) :=
    differentiable_linear_rlb (F := Matrix T d ℝ)
      { toFun := fun q => Matrix.of fun _ : T => q.2.E, map_add' := fun _ _ => rfl,
        map_smul' := fun _ _ => rfl }
  have hbR : Differentiable ℝ (fun q : ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut =>
      Matrix.of fun _ : T => q.2.read 0) :=
    differentiable_linear_rlb (F := Matrix T (hid 0) ℝ)
      { toFun := fun q => Matrix.of fun _ : T => q.2.read 0, map_add' := fun _ _ => rfl,
        map_smul' := fun _ _ => rfl }
  have hbW : Differentiable ℝ (fun q : ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut =>
      Matrix.of fun _ : T => q.2.write 0) :=
    differentiable_linear_rlb (F := Matrix T d ℝ)
      { toFun := fun q => Matrix.of fun _ : T => q.2.write 0, map_add' := fun _ _ => rfl,
        map_smul' := fun _ _ => rfl }
  have hbD : Differentiable ℝ (fun q : ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut =>
      Matrix.of fun _ : T => q.2.D) :=
    differentiable_linear_rlb (F := Matrix T dOut ℝ)
      { toFun := fun q => Matrix.of fun _ : T => q.2.D, map_add' := fun _ _ => rfl,
        map_smul' := fun _ _ => rfl }
  -- `h_0 = x E + b_E` and the pre-activations `h_0 W_read + b_read` are differentiable
  have h0 : DifferentiableAt ℝ (fun q : ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut =>
      x * q.1.E + Matrix.of fun _ : T => q.2.E) p :=
    (differentiableAt_matMul_rlb (differentiableAt_const x) (hE p)).add (hbE p)
  have hpre := (differentiableAt_matMul_rlb h0 (hR p)).add (hbR p)
  -- `σ` is differentiable at every pre-activation `(x C)_{t i} + β_i`, which is not `0`
  have hmap : DifferentiableAt ℝ (fun M : Matrix T (hid 0) ℝ => M.map σ)
      ((x * p.1.E + Matrix.of fun _ : T => p.2.E) * p.1.read 0
        + Matrix.of fun _ : T => p.2.read 0) := by
    refine differentiableAt_pi.2 fun t => differentiableAt_pi.2 fun i => ?_
    have hz : ((x * p.1.E + Matrix.of fun _ : T => p.2.E) * p.1.read 0
        + Matrix.of fun _ : T => p.2.read 0) t i ≠ 0 := by
      rw [Matrix.add_mul, Matrix.add_apply, Matrix.add_apply, add_assoc]
      exact hx t i
    have he : DifferentiableAt ℝ (fun M : Matrix T (hid 0) ℝ => M t i)
        ((x * p.1.E + Matrix.of fun _ : T => p.2.E) * p.1.read 0
          + Matrix.of fun _ : T => p.2.read 0) :=
      differentiableAt_pi.1 (differentiableAt_pi.1 differentiableAt_id t) i
    have hc := DifferentiableAt.comp (g := σ) (f := fun M : Matrix T (hid 0) ℝ => M t i)
      ((x * p.1.E + Matrix.of fun _ : T => p.2.E) * p.1.read 0
        + Matrix.of fun _ : T => p.2.read 0) (hσ _ hz).differentiableAt he
    exact hc
  have hsig := DifferentiableAt.comp (g := fun M : Matrix T (hid 0) ℝ => M.map σ) p hmap hpre
  -- the hidden state `h_1` and the output `h_1 D + b_D`: products and sums
  have h1 := (differentiableAt_matMul_rlb h0 (differentiableAt_const (S 0))).add
    ((differentiableAt_matMul_rlb hsig (hW p)).add (hbW p))
  have h2 := (differentiableAt_matMul_rlb h1 (hD p)).add (hbD p)
  simp only [evalB_mlp_S_eq_rlb]
  exact h2

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dOut] in
/-- Helper: at an input of `noKinkB p`, every pre-activation `(x C)_{t i} + β_i` is nonzero. -/
private theorem noKinkB_apply_rlb {p : ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut}
    {x : Matrix T dIn ℝ} (hx : x ∈ noKinkB p) (t : T) (i : hid 0) :
    (x * Cm_rlb p.1) t i + βm_rlb p.1 p.2 i ≠ 0 := by
  have h := hx t i
  rwa [Matrix.mul_assoc] at h

omit [Nonempty T] [DecidableEq d] in
/-- Helper (the chain rule, at an input of `noKinkB p`): the derivative of
`(θ, b) ↦ F(θ, b, x)` along `η` has the entries
`∂γ_{0,o} + ∑_i [σ(z_i) (∂A)_{i o} + σ'(z_i) ((x ∂C)_{t i} + ∂β_i) A_{i o}]`,
`z_i = (x C)_{t i} + β_i`, which is not `0`. -/
private theorem fderiv_evalB_apply_rlb (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (p η : ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)
    (x : Matrix T dIn ℝ) (hx : x ∈ noKinkB p) (t : T) (o : dOut) :
    fderiv ℝ (fun q : ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut =>
        evalB (Arch.mlp σ id hid) 0 q.1 q.2 x) p η t o
      = dγm_rlb p.1 p.2 η.1 η.2 o + ∑ i : hid 0,
        (σ ((x * Cm_rlb p.1) t i + βm_rlb p.1 p.2 i) * dAm_rlb p.1 η.1 i o
          + σ' ((x * Cm_rlb p.1) t i + βm_rlb p.1 p.2 i)
            * ((x * dCm_rlb p.1 η.1) t i + dβm_rlb p.1 p.2 η.1 η.2 i) * Am_rlb p.1 i o) := by
  have hdiff := differentiableAt_evalB_of_mem_noKinkB hσ p 0 x hx
  -- the line `τ ↦ (θ + τ η, b + τ η_b)` has velocity `η` and passes through `p` at `τ = 0`
  have hline : HasDerivAt (fun τ : ℝ => (p.1 + τ • η.1, p.2 + τ • η.2)) η 0 := by
    have h1 := ((hasDerivAt_id (0 : ℝ)).smul_const η.1).const_add p.1
    have h2 := ((hasDerivAt_id (0 : ℝ)).smul_const η.2).const_add p.2
    rw [one_smul] at h1 h2
    exact h1.prodMk h2
  have h0 : p = (p.1 + (0 : ℝ) • η.1, p.2 + (0 : ℝ) • η.2) := by
    rw [zero_smul, zero_smul, add_zero, add_zero]
  -- the chain rule along the line
  have h1 := hdiff.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hline h0
  have h2 := hasDerivAt_pi.1 (hasDerivAt_pi.1 h1 t) o
  -- the same derivative computed entrywise: products and sums of real functions of `τ`, with
  -- `σ` differentiable at `z_i ≠ 0`
  have h3 : HasDerivAt (fun τ : ℝ =>
      evalB (Arch.mlp σ id hid) 0 (p.1 + τ • η.1) (p.2 + τ • η.2) x t o)
      (dγm_rlb p.1 p.2 η.1 η.2 o + ∑ i : hid 0,
        (σ ((x * Cm_rlb p.1) t i + βm_rlb p.1 p.2 i) * dAm_rlb p.1 η.1 i o
          + σ' ((x * Cm_rlb p.1) t i + βm_rlb p.1 p.2 i)
            * ((x * dCm_rlb p.1 η.1) t i + dβm_rlb p.1 p.2 η.1 η.2 i) * Am_rlb p.1 i o)) 0 := by
    rw [funext fun τ => evalB_line_apply_rlb p.1 η.1 p.2 η.2 x t o τ]
    refine (hasDerivAt_quad _ _ _).add (HasDerivAt.fun_sum fun i _ => ?_)
    have hu := (hasDerivAt_quad ((x * Cm_rlb p.1) t i) ((x * dCm_rlb p.1 η.1) t i)
      ((x * Cm_rlb η.1) t i)).add (hasDerivAt_quad (βm_rlb p.1 p.2 i)
        (dβm_rlb p.1 p.2 η.1 η.2 i) ((η.2.E ᵥ* rd_rlb η.1) i))
    have hv := hasDerivAt_quad (Am_rlb p.1 i o) (dAm_rlb p.1 η.1 i o) (Am_rlb η.1 i o)
    have h := ((hσ _ (noKinkB_apply_rlb hx t i)).comp_of_eq (0 : ℝ) hu
      (by simp only [Pi.add_apply, zero_mul, add_zero])).mul hv
    convert h using 1
    · rfl
    · simp only [Function.comp_apply, Pi.add_apply, zero_mul, mul_zero, add_zero]
      ring
  exact h2.unique h3

/-! ### Helpers: the residual network with biases and its derivative -/

omit [Fintype T] [Nonempty T] [Fintype dIn] [Fintype dOut] in
/-- Helper: a matrix whose rank is its number of columns cancels on the left, via a left
inverse. -/
private theorem cancel_left_of_rank_rlb {m n k : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (M : Matrix m n ℝ) (hM : M.rank = Fintype.card n) {X Y : Matrix n k ℝ}
    (h : M * X = M * Y) : X = Y := by
  obtain ⟨B, hB⟩ := Matrix.vecMul_surjective_iff_exists_left_inverse.mp
    (Matrix.vecMul_surjective_iff_rank_eq_card.mpr hM)
  have := congrArg (B * ·) h
  simpa only [← Matrix.mul_assoc, hB, Matrix.one_mul] using this

omit [Fintype T] [Nonempty T] [Fintype dIn] [Fintype dOut] in
/-- Helper: a matrix whose rank is its number of rows cancels on the right, via a right
inverse. -/
private theorem cancel_right_of_rank_rlb {m n k : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    (M : Matrix m n ℝ) (hM : M.rank = Fintype.card m) {X Y : Matrix k m ℝ}
    (h : X * M = Y * M) : X = Y := by
  obtain ⟨R, hR⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.mp
    (Matrix.mulVec_surjective_iff_rank_eq_card.mpr hM)
  have := congrArg (· * R) h
  simpa only [Matrix.mul_assoc, hR, Matrix.mul_one] using this

/-- Helper: `M = E D`, the linear part of the residual network. -/
private def Mm_rlb (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) :
    Matrix dIn dOut ℝ :=
  θ.E * θ.D

/-- Helper: the derivative `∂M = η_E D + E η_D` of `M` along `η`. -/
private def dMm_rlb (θ η : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) :
    Matrix dIn dOut ℝ :=
  η.E * θ.D + θ.E * η.D

/-- Helper: `γ = b_E D + γ_0`. -/
private def γr_rlb (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)
    (b : Biases (Arch.mlp (T := T) (d := d) σ id hid) dOut) : dOut → ℝ :=
  b.E ᵥ* θ.D + γm_rlb θ b

/-- Helper: the derivative `∂γ = η_{b_E} D + b_E η_D + ∂γ_0` of `γ`. -/
private def dγr_rlb (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)
    (b : Biases (Arch.mlp (T := T) (d := d) σ id hid) dOut)
    (η : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)
    (ηb : Biases (Arch.mlp (T := T) (d := d) σ id hid) dOut) : dOut → ℝ :=
  ηb.E ᵥ* θ.D + b.E ᵥ* η.D + dγm_rlb θ b η ηb

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: along the line, `M(τ) = M + τ ∂M + τ² η_E η_D`. -/
private theorem Mm_line_rlb (θ η : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)
    (τ : ℝ) :
    Mm_rlb (θ + τ • η) = Mm_rlb θ + τ • dMm_rlb θ η + (τ * τ) • Mm_rlb η := by
  simp only [Mm_rlb, dMm_rlb, Params.add_E, Params.smul_E, Params.add_D, Params.smul_D,
    Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, smul_add, smul_smul]
  abel

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: along the line, `γ(τ) = γ + τ ∂γ + τ² (η_{b_E} + η_{b_write}) η_D`. -/
private theorem γr_line_rlb (θ η : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)
    (b ηb : Biases (Arch.mlp (T := T) (d := d) σ id hid) dOut) (τ : ℝ) :
    γr_rlb (θ + τ • η) (b + τ • ηb)
      = γr_rlb θ b + τ • dγr_rlb θ b η ηb
        + (τ * τ) • (ηb.E ᵥ* η.D + ηb.write 0 ᵥ* η.D) := by
  simp only [γr_rlb, dγr_rlb, γm_line_rlb, Params.add_D, Params.smul_D, Biases.add_E,
    Biases.smul_E, Matrix.vecMul_add, Matrix.add_vecMul, Matrix.vecMul_smul, Matrix.smul_vecMul,
    smul_add, smul_smul]
  abel

omit [Fintype T] [Nonempty T] [Fintype dOut] in
/-- Helper: the residual network with biases, `F(θ, x) = x M + γ + σ(x C + β) A` (stream matrix
`1`). -/
private theorem evalB_mlp_res_eq_rlb
    (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)
    (b : Biases (Arch.mlp (T := T) (d := d) σ id hid) dOut) (x : Matrix T dIn ℝ) :
    evalB (Arch.mlp σ id hid) 1 θ b x
      = x * Mm_rlb θ + (Matrix.of fun _ : T => γr_rlb θ b)
        + (x * Cm_rlb θ + Matrix.of fun _ : T => βm_rlb θ b).map σ * Am_rlb θ := by
  have h1 : (Fin.last 1 : Fin 2) = (0 : Fin 1).succ := rfl
  have hχ : (Arch.mlp (T := T) (d := d) σ id hid).χ = id := rfl
  have hf : (Arch.mlp (T := T) (d := d) σ id hid).f 0 = fun M => M.map σ := rfl
  -- `h_1 = h_0 1 + σ(h_0 W_read + b_read) W_write + b_write` with `h_0 = x E + b_E`
  rw [evalB, h1, hiddenB_succ, Fin.castSucc_zero, hiddenB_zero, hχ, hf]
  simp only [Pi.one_apply, Matrix.mul_one, id_eq, Matrix.add_mul, Matrix.mul_assoc,
    of_const_mul_rlb, Mm_rlb, Cm_rlb, Am_rlb, rd_rlb, wr_rlb, γr_rlb, γm_rlb, βm_rlb]
  rw [add_assoc (x * (θ.E * θ.read 0)), of_const_add_rlb]
  ext t o
  simp only [Matrix.add_apply, Matrix.of_apply, Pi.add_apply]
  ring

omit [Fintype T] [Nonempty T] [Fintype dOut] in
/-- Helper: the entries of `F(θ, x)`, `(x M)_{t o} + γ_o + ∑_i σ((x C)_{t i} + β_i) A_{i o}`. -/
private theorem evalB_mlp_res_apply_rlb
    (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)
    (b : Biases (Arch.mlp (T := T) (d := d) σ id hid) dOut) (x : Matrix T dIn ℝ) (t : T)
    (o : dOut) :
    evalB (Arch.mlp σ id hid) 1 θ b x t o
      = (x * Mm_rlb θ) t o + γr_rlb θ b o
        + ∑ i : hid 0, σ ((x * Cm_rlb θ) t i + βm_rlb θ b i) * Am_rlb θ i o := by
  rw [evalB_mlp_res_eq_rlb]
  rfl

omit [Fintype T] [Nonempty T] [Fintype dOut] in
/-- Helper: the entries of `F(θ + τ η, b + τ η_b)(x)` of the residual network as functions of
`τ`. -/
private theorem evalB_res_line_apply_rlb
    (θ η : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)
    (b ηb : Biases (Arch.mlp (T := T) (d := d) σ id hid) dOut) (x : Matrix T dIn ℝ) (t : T)
    (o : dOut) (τ : ℝ) :
    evalB (Arch.mlp σ id hid) 1 (θ + τ • η) (b + τ • ηb) x t o
      = ((x * Mm_rlb θ) t o + τ * (x * dMm_rlb θ η) t o + τ * τ * (x * Mm_rlb η) t o)
        + (γr_rlb θ b o + τ * dγr_rlb θ b η ηb o
          + τ * τ * (ηb.E ᵥ* η.D + ηb.write 0 ᵥ* η.D) o)
        + ∑ i : hid 0,
          σ (((x * Cm_rlb θ) t i + τ * (x * dCm_rlb θ η) t i + τ * τ * (x * Cm_rlb η) t i)
              + (βm_rlb θ b i + τ * dβm_rlb θ b η ηb i + τ * τ * (ηb.E ᵥ* rd_rlb η) i))
            * (Am_rlb θ i o + τ * dAm_rlb θ η i o + τ * τ * Am_rlb η i o) := by
  rw [evalB_mlp_res_apply_rlb, Mm_line_rlb, Cm_line_rlb, Am_line_rlb, βm_line_rlb,
    γr_line_rlb]
  simp only [Matrix.mul_add, Matrix.mul_smul]
  rfl

omit [Nonempty T] in
/-- Helper (the chain rule, at an input of `noKinkB p`): the derivative of
`(θ, b) ↦ F(θ, b, x)` of the residual network along `η` has the entries
`(x ∂M)_{t o} + ∂γ_o + ∑_i [σ(z_i) (∂A)_{i o} + σ'(z_i) ((x ∂C)_{t i} + ∂β_i) A_{i o}]`,
`z_i = (x C)_{t i} + β_i`, which is not `0`. -/
private theorem fderiv_evalB_res_apply_rlb (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (p η : ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)
    (x : Matrix T dIn ℝ) (hx : x ∈ noKinkB p) (t : T) (o : dOut) :
    fderiv ℝ (fun q : ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut =>
        evalB (Arch.mlp σ id hid) 1 q.1 q.2 x) p η t o
      = (x * dMm_rlb p.1 η.1) t o + dγr_rlb p.1 p.2 η.1 η.2 o + ∑ i : hid 0,
        (σ ((x * Cm_rlb p.1) t i + βm_rlb p.1 p.2 i) * dAm_rlb p.1 η.1 i o
          + σ' ((x * Cm_rlb p.1) t i + βm_rlb p.1 p.2 i)
            * ((x * dCm_rlb p.1 η.1) t i + dβm_rlb p.1 p.2 η.1 η.2 i) * Am_rlb p.1 i o) := by
  have hdiff := differentiableAt_evalB_of_mem_noKinkB hσ p 1 x hx
  -- the line `τ ↦ (θ + τ η, b + τ η_b)` has velocity `η` and passes through `p` at `τ = 0`
  have hline : HasDerivAt (fun τ : ℝ => (p.1 + τ • η.1, p.2 + τ • η.2)) η 0 := by
    have h1 := ((hasDerivAt_id (0 : ℝ)).smul_const η.1).const_add p.1
    have h2 := ((hasDerivAt_id (0 : ℝ)).smul_const η.2).const_add p.2
    rw [one_smul] at h1 h2
    exact h1.prodMk h2
  have h0 : p = (p.1 + (0 : ℝ) • η.1, p.2 + (0 : ℝ) • η.2) := by
    rw [zero_smul, zero_smul, add_zero, add_zero]
  -- the chain rule along the line
  have h1 := hdiff.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hline h0
  have h2 := hasDerivAt_pi.1 (hasDerivAt_pi.1 h1 t) o
  -- the same derivative computed entrywise: polynomials, products and sums of real functions,
  -- with `σ` differentiable at `z_i ≠ 0`
  have h3 : HasDerivAt (fun τ : ℝ =>
      evalB (Arch.mlp σ id hid) 1 (p.1 + τ • η.1) (p.2 + τ • η.2) x t o)
      ((x * dMm_rlb p.1 η.1) t o + dγr_rlb p.1 p.2 η.1 η.2 o + ∑ i : hid 0,
        (σ ((x * Cm_rlb p.1) t i + βm_rlb p.1 p.2 i) * dAm_rlb p.1 η.1 i o
          + σ' ((x * Cm_rlb p.1) t i + βm_rlb p.1 p.2 i)
            * ((x * dCm_rlb p.1 η.1) t i + dβm_rlb p.1 p.2 η.1 η.2 i) * Am_rlb p.1 i o)) 0 := by
    rw [funext fun τ => evalB_res_line_apply_rlb p.1 η.1 p.2 η.2 x t o τ]
    refine ((hasDerivAt_quad _ _ _).add (hasDerivAt_quad _ _ _)).add
      (HasDerivAt.fun_sum fun i _ => ?_)
    have hu := (hasDerivAt_quad ((x * Cm_rlb p.1) t i) ((x * dCm_rlb p.1 η.1) t i)
      ((x * Cm_rlb η.1) t i)).add (hasDerivAt_quad (βm_rlb p.1 p.2 i)
        (dβm_rlb p.1 p.2 η.1 η.2 i) ((η.2.E ᵥ* rd_rlb η.1) i))
    have hv := hasDerivAt_quad (Am_rlb p.1 i o) (dAm_rlb p.1 η.1 i o) (Am_rlb η.1 i o)
    have h := ((hσ _ (noKinkB_apply_rlb hx t i)).comp_of_eq (0 : ℝ) hu
      (by simp only [Pi.add_apply, zero_mul, add_zero])).mul hv
    convert h using 1
    · rfl
    · simp only [Function.comp_apply, Pi.add_apply, zero_mul, mul_zero, add_zero]
      ring
  exact h2.unique h3

/-! ### Helpers: the derivatives of `C`, `A`, `β`, `γ_0`, `M`, `γ` along a rescaling -/

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: `∂C` is linear in the direction. -/
private theorem dCm_sub_rlb (θ η ρ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) :
    dCm_rlb θ (η - ρ) = dCm_rlb θ η - dCm_rlb θ ρ := by
  show (η.E - ρ.E) * rd_rlb θ + θ.E * (rd_rlb η - rd_rlb ρ)
    = (η.E * rd_rlb θ + θ.E * rd_rlb η) - (ρ.E * rd_rlb θ + θ.E * rd_rlb ρ)
  rw [Matrix.sub_mul, Matrix.mul_sub]
  abel

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: `∂A` is linear in the direction. -/
private theorem dAm_sub_rlb (θ η ρ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) :
    dAm_rlb θ (η - ρ) = dAm_rlb θ η - dAm_rlb θ ρ := by
  show (wr_rlb η - wr_rlb ρ) * θ.D + wr_rlb θ * (η.D - ρ.D)
    = (wr_rlb η * θ.D + wr_rlb θ * η.D) - (wr_rlb ρ * θ.D + wr_rlb θ * ρ.D)
  rw [Matrix.sub_mul, Matrix.mul_sub]
  abel

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: along a rescaling, the column `c_i` of `C` moves by `α_i c_i`. -/
private theorem dCm_rescale_rlb (k : ℕ)
    (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) (α : ∀ ℓ, hid ℓ → ℝ)
    (a : dIn) (i : hid 0) :
    dCm_rlb θ (rescaleDirMlp k θ α) a i = α 0 i * Cm_rlb θ a i := by
  show ((0 : Matrix dIn d ℝ) * rd_rlb θ + θ.E * rd_rlb (rescaleDirMlp k θ α)) a i
    = α 0 i * (θ.E * rd_rlb θ) a i
  rw [Matrix.zero_mul, zero_add, Matrix.mul_apply, Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  show θ.E a j * (α 0 i * θ.read 0 j i) = α 0 i * (θ.E a j * θ.read 0 j i)
  ring

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: along a rescaling, the row `a_i` of `A` moves by `-k α_i a_i`. -/
private theorem dAm_rescale_rlb (k : ℕ)
    (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) (α : ∀ ℓ, hid ℓ → ℝ)
    (i : hid 0) (o : dOut) :
    dAm_rlb θ (rescaleDirMlp k θ α) i o = -((k : ℝ) * α 0 i) * Am_rlb θ i o := by
  show (wr_rlb (rescaleDirMlp k θ α) * θ.D + wr_rlb θ * (0 : Matrix d dOut ℝ)) i o
    = -((k : ℝ) * α 0 i) * (wr_rlb θ * θ.D) i o
  rw [Matrix.mul_zero, add_zero, Matrix.mul_apply, Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  show -((k : ℝ) * α 0 i) * θ.write 0 i j * θ.D j o
    = -((k : ℝ) * α 0 i) * (θ.write 0 i j * θ.D j o)
  ring

omit [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: `v (W diag(c)) = (v W) diag(c)`, entry by entry. -/
private theorem vecMul_of_mul_rlb {m n : Type*} [Fintype m] (v : m → ℝ) (c : n → ℝ)
    (W : Matrix m n ℝ) (j : n) :
    (v ᵥ* Matrix.of fun a i => c i * W a i) j = c j * (v ᵥ* W) j := by
  simp only [Matrix.vecMul, dotProduct, Matrix.of_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => by ring

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: along `η` minus a rescaling with its biases, `∂β_i` moves by `−α_i β_i`. -/
private theorem dβm_sub_rescale_rlb (k : ℕ)
    (p η : ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) (α : ∀ ℓ, hid ℓ → ℝ)
    (i : hid 0) :
    dβm_rlb p.1 p.2 (η.1 - rescaleDirMlp k p.1 α) (η.2 - (rescaleDirMlpB k p α).2) i
      = dβm_rlb p.1 p.2 η.1 η.2 i - α 0 i * βm_rlb p.1 p.2 i := by
  show ((η.2.E - 0) ᵥ* p.1.read 0) i
      + (p.2.E ᵥ* (η.1.read 0 - Matrix.of fun a j => α 0 j * p.1.read 0 a j)) i
      + (η.2.read 0 i - α 0 i * p.2.read 0 i)
    = (η.2.E ᵥ* p.1.read 0) i + (p.2.E ᵥ* η.1.read 0) i + η.2.read 0 i
      - α 0 i * ((p.2.E ᵥ* p.1.read 0) i + p.2.read 0 i)
  rw [sub_zero, Matrix.vecMul_sub, Pi.sub_apply, vecMul_of_mul_rlb]
  ring

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: a rescaling with its biases does not move `γ_0`. -/
private theorem dγm_sub_rescale_rlb (k : ℕ)
    (p η : ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) (α : ∀ ℓ, hid ℓ → ℝ) :
    dγm_rlb p.1 p.2 (η.1 - rescaleDirMlp k p.1 α) (η.2 - (rescaleDirMlpB k p α).2)
      = dγm_rlb p.1 p.2 η.1 η.2 := by
  show (η.2.write 0 - 0) ᵥ* p.1.D + p.2.write 0 ᵥ* (η.1.D - 0) + (η.2.D - 0)
    = η.2.write 0 ᵥ* p.1.D + p.2.write 0 ᵥ* η.1.D + η.2.D
  rw [sub_zero, sub_zero, sub_zero]

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: a rescaling does not move `M = E D`. -/
private theorem dMm_sub_rescale_rlb (k : ℕ)
    (θ η : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) (α : ∀ ℓ, hid ℓ → ℝ) :
    dMm_rlb θ (η - rescaleDirMlp k θ α) = dMm_rlb θ η := by
  show (η.E - 0) * θ.D + θ.E * (η.D - 0) = η.E * θ.D + θ.E * η.D
  rw [sub_zero, sub_zero]

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: a rescaling with its biases does not move `γ = b_E D + γ_0`. -/
private theorem dγr_sub_rescale_rlb (k : ℕ)
    (p η : ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) (α : ∀ ℓ, hid ℓ → ℝ) :
    dγr_rlb p.1 p.2 (η.1 - rescaleDirMlp k p.1 α) (η.2 - (rescaleDirMlpB k p α).2)
      = dγr_rlb p.1 p.2 η.1 η.2 := by
  show (η.2.E - 0) ᵥ* p.1.D + p.2.E ᵥ* (η.1.D - 0)
      + dγm_rlb p.1 p.2 (η.1 - rescaleDirMlp k p.1 α) (η.2 - (rescaleDirMlpB k p α).2)
    = η.2.E ᵥ* p.1.D + p.2.E ᵥ* η.1.D + dγm_rlb p.1 p.2 η.1 η.2
  rw [dγm_sub_rescale_rlb, sub_zero, sub_zero]

omit [Fintype T] [Nonempty T] in
/-- Helper (Lemma B.2 with biases, the argument of `flatB_le_range_mlp_skipless`): under the
conditions `OneBlockGeneric`, a direction that keeps `C`, `A`, `β` and `γ_0` to first order is the
direction of changes of basis `X_0, X_1` and translations `g_0, g_1`. -/
private theorem range_of_keeps_rlb
    (p : ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) (hp : OneBlockGeneric p.1)
    (η : ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)
    (hC : η.1.E * p.1.read 0 + p.1.E * η.1.read 0 = 0)
    (hA : η.1.write 0 * p.1.D + p.1.write 0 * η.1.D = 0)
    (hβ : η.2.E ᵥ* p.1.read 0 + p.2.E ᵥ* η.1.read 0 + η.2.read 0 = 0)
    (hγ : η.2.write 0 ᵥ* p.1.D + p.2.write 0 ᵥ* η.1.D + η.2.D = 0) :
    ∃ (X : Fin 2 → Matrix d d ℝ) (g : Fin 2 → d → ℝ),
      η = cobDirB p X + (0, translateAtDir p.1 g) := by
  -- Lemma C.2: a direction that keeps `C` and `A` moves the weights by two changes of basis
  obtain ⟨X, hX⟩ := (keeps_products_iff_mem_range_cobDir p.1 η.1 hp.rank_E hp.rank_D
    hp.rank_read hp.rank_write).1 ⟨hC, hA⟩
  have hR : η.1.read 0 = -(X 0 * p.1.read 0) := by rw [hX]; rfl
  have hD : η.1.D = -(X 1 * p.1.D) := by rw [hX]; rfl
  -- `∂β = 0`: `η_{b_read} = −g_0 W_read` with `g_0 = η_{b_E} − b_E X_0`
  have hbR : η.2.read 0 = -((η.2.E - p.2.E ᵥ* X 0) ᵥ* p.1.read 0) := by
    have h := hβ
    rw [hR, Matrix.vecMul_neg, ← Matrix.vecMul_vecMul] at h
    rw [Matrix.sub_vecMul]
    linear_combination h
  -- `∂γ_0 = 0`: `η_{b_D} = −g_1 D` with `g_1 = η_{b_write} − b_write X_1`
  have hbD : η.2.D = -((η.2.write 0 - p.2.write 0 ᵥ* X 1) ᵥ* p.1.D) := by
    have h := hγ
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

/-- **Lemma B.2 with biases, after Lemma B.3, for one skipless block with the rescalings:** under
the conditions `OneBlockGeneric` on the weights, a direction that is flat at every input with no
hidden unit at its kink is the sum of the direction of changes of basis `X_0, X_1` and
translations `g_0, g_1` of the two hidden states and of a direction of the rescalings of the
hidden units with their biases. -/
theorem flatOnB_noKinkB_le_mlp_rescale {k : ℕ} (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (hU : UnitsRescale σ σ' k dIn dOut (hid 0))
    (p : ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) (hp : OneBlockGeneric p.1)
    (η : ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)
    (hη : η ∈ flatOnB (Arch.mlp σ id hid) 0 p (noKinkB p)) :
    ∃ (X : Fin 2 → Matrix d d ℝ) (g : Fin 2 → d → ℝ) (α : ∀ ℓ, hid ℓ → ℝ),
      η = cobDirB p X + (0, translateAtDir p.1 g) + rescaleDirMlpB k p α := by
  -- Step 3: at every input with no hidden unit at its kink, the derivative of `F(θ, b, x)` along
  -- `η` vanishes, entry by entry
  have hzero : ∀ x ∈ noKinkB p, ∀ (t : T) (o : dOut), dγm_rlb p.1 p.2 η.1 η.2 o
      + ∑ i : hid 0, (σ ((x * Cm_rlb p.1) t i + βm_rlb p.1 p.2 i) * dAm_rlb p.1 η.1 i o
        + σ' ((x * Cm_rlb p.1) t i + βm_rlb p.1 p.2 i)
          * ((x * dCm_rlb p.1 η.1) t i + dβm_rlb p.1 p.2 η.1 η.2 i) * Am_rlb p.1 i o) = 0 := by
    intro x hx t o
    rw [← fderiv_evalB_apply_rlb hσ p η x hx t o]
    have h := LinearMap.mem_ker.1 ((Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hη x) hx)
    exact congrFun (congrFun h t) o
  -- Lemma B.3 with the rescalings (inputs `x` with all rows equal to a `v` with
  -- `v c_i + β_i ≠ 0` for all `i`): `∂γ_0 = 0`, `∂c_i = λ_i c_i`, `∂β_i = λ_i β_i`,
  -- `∂a_i = −k λ_i a_i`
  obtain ⟨-, hγ, lam, hlam⟩ := hU (fun i => (Cm_rlb p.1)ᵀ i) (βm_rlb p.1 p.2)
    (fun i => Am_rlb p.1 i) 0 (dγm_rlb p.1 p.2 η.1 η.2) (fun i => (dCm_rlb p.1 η.1)ᵀ i)
    (dβm_rlb p.1 p.2 η.1 η.2) (fun i => dAm_rlb p.1 η.1 i) (fun i => hp.row_ne_zero i)
    (fun i => hp.col_ne_zero i) (fun i j hij => hp.col_not_collinear i j hij) (by
      intro v hv
      have hx : (Matrix.of fun _ : T => v) ∈ noKinkB p := by
        intro t i
        rw [Matrix.mul_assoc]
        exact hv i
      funext o
      have h := hzero _ hx (Classical.arbitrary T) o
      simp only [Matrix.vecMul_zero, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        Pi.zero_apply, zero_add]
      exact h)
  -- the rescaling with these `λ_i` (one block: `ℓ = 0`)
  let α' : ∀ ℓ : Fin 1, hid ℓ → ℝ := fun ℓ => Fin.cases lam (fun l => l.elim0) ℓ
  -- `η` minus the rescaling keeps `C`, `A`, `β` and `γ_0` to first order
  have hC : dCm_rlb p.1 (η.1 - rescaleDirMlp k p.1 α') = 0 := by
    ext a i
    rw [dCm_sub_rlb, Matrix.sub_apply, dCm_rescale_rlb, Matrix.zero_apply, sub_eq_zero]
    exact congrFun (hlam i).1 a
  have hA : dAm_rlb p.1 (η.1 - rescaleDirMlp k p.1 α') = 0 := by
    ext i o
    rw [dAm_sub_rlb, Matrix.sub_apply, dAm_rescale_rlb, Matrix.zero_apply, sub_eq_zero]
    exact congrFun (hlam i).2.2 o
  have hβ : dβm_rlb p.1 p.2 (η.1 - rescaleDirMlp k p.1 α') (η.2 - (rescaleDirMlpB k p α').2)
      = 0 := by
    funext i
    rw [dβm_sub_rescale_rlb, Pi.zero_apply, sub_eq_zero]
    exact (hlam i).2.1
  have hγ' : dγm_rlb p.1 p.2 (η.1 - rescaleDirMlp k p.1 α') (η.2 - (rescaleDirMlpB k p α').2)
      = 0 := by
    rw [dγm_sub_rescale_rlb]
    exact hγ
  -- Lemma B.2 with biases: `η` minus the rescaling is a direction of changes of basis and
  -- translations
  obtain ⟨X, g, hXg⟩ := range_of_keeps_rlb p hp (η - rescaleDirMlpB k p α') hC hA hβ hγ'
  exact ⟨X, g, α', sub_eq_iff_eq_add.1 hXg⟩

/-! ### Helpers: the directions of the changes of basis and the translations, as linear maps -/

omit [Fintype T] [Nonempty T] in
/-- Helper: `(X, g) ↦ cobDirB p X + (0, translateAtDir θ g)`, as a linear map. -/
private noncomputable def cobTrAtLin_rlb {L : ℕ} {A : Arch T d L} (p : ParamsB A dIn dOut) :
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
private noncomputable def cobTrLin_rlb {L : ℕ} {A : Arch T d L} (p : ParamsB A dIn dOut) :
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

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the pairs `(X, g)` of `L + 1` changes of basis and `L + 1` translations form a space
of dimension `(L + 1) d² + (L + 1) d`. -/
private theorem finrank_cobTrAtDomain_rlb (L : ℕ) :
    Module.finrank ℝ ((Fin (L + 1) → Matrix d d ℝ) × (Fin (L + 1) → d → ℝ))
      = (L + 1) * Fintype.card d ^ 2 + (L + 1) * Fintype.card d := by
  rw [Module.finrank_prod, finrank_cobDomain, Module.finrank_pi_fintype]
  simp only [Module.finrank_fintype_fun_eq_card, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul]

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the pairs `(X, g)` of one change of basis and `L + 1` translations form a space of
dimension `d² + (L + 1) d`. -/
private theorem finrank_cobTrDomain_rlb (L : ℕ) :
    Module.finrank ℝ (Matrix d d ℝ × (Fin (L + 1) → d → ℝ))
      = Fintype.card d ^ 2 + (L + 1) * Fintype.card d := by
  rw [Module.finrank_prod, Module.finrank_matrix, Module.finrank_pi_fintype]
  simp only [Module.finrank_self, Module.finrank_fintype_fun_eq_card, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one, sq]

/-- Helper: `α ↦ rescaleDirMlpB k p α` is linear. -/
private noncomputable def rescaleDirMlpBLin_rlb (k : ℕ)
    (p : ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) :
    (∀ ℓ : Fin 1, hid ℓ → ℝ) →ₗ[ℝ] ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut where
  toFun := rescaleDirMlpB k p
  map_add' α β := by
    refine Prod.ext ?_ ?_
    · apply Params.ext'
      · exact (add_zero 0).symm
      · intro ℓ
        ext a i
        show (α + β) ℓ i * p.1.read ℓ a i = α ℓ i * p.1.read ℓ a i + β ℓ i * p.1.read ℓ a i
        rw [Pi.add_apply, Pi.add_apply]
        ring
      · intro ℓ
        ext i a
        show -((k : ℝ) * (α + β) ℓ i) * p.1.write ℓ i a
          = -((k : ℝ) * α ℓ i) * p.1.write ℓ i a + -((k : ℝ) * β ℓ i) * p.1.write ℓ i a
        rw [Pi.add_apply, Pi.add_apply]
        ring
      · exact (add_zero 0).symm
    · apply Biases.ext'
      · exact (add_zero 0).symm
      · intro ℓ
        funext i
        show (α + β) ℓ i * p.2.read ℓ i = α ℓ i * p.2.read ℓ i + β ℓ i * p.2.read ℓ i
        rw [Pi.add_apply, Pi.add_apply]
        ring
      · intro ℓ
        exact (add_zero 0).symm
      · exact (add_zero 0).symm
  map_smul' c α := by
    refine Prod.ext ?_ ?_
    · apply Params.ext'
      · exact (smul_zero c).symm
      · intro ℓ
        ext a i
        show (c • α) ℓ i * p.1.read ℓ a i = c * (α ℓ i * p.1.read ℓ a i)
        rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul]
        ring
      · intro ℓ
        ext i a
        show -((k : ℝ) * (c • α) ℓ i) * p.1.write ℓ i a
          = c * (-((k : ℝ) * α ℓ i) * p.1.write ℓ i a)
        rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul]
        ring
      · exact (smul_zero c).symm
    · apply Biases.ext'
      · exact (smul_zero c).symm
      · intro ℓ
        funext i
        show (c • α) ℓ i * p.2.read ℓ i = c * (α ℓ i * p.2.read ℓ i)
        rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul]
        ring
      · intro ℓ
        exact (smul_zero c).symm
      · exact (smul_zero c).symm

omit [DecidableEq d] in
/-- Helper: the triples `(X, g, α)` of two changes of basis, two translations and one number
per hidden unit form a space of dimension `2 d² + 2 d + d_hidden`. -/
private theorem finrank_dirDomainB_rlb :
    Module.finrank ℝ (((Fin (1 + 1) → Matrix d d ℝ) × (Fin (1 + 1) → d → ℝ))
        × (∀ ℓ : Fin 1, hid ℓ → ℝ))
      = (1 + 1) * Fintype.card d ^ 2 + (1 + 1) * Fintype.card d + Fintype.card (hid 0) := by
  rw [Module.finrank_prod, finrank_cobTrAtDomain_rlb, Module.finrank_pi_fintype]
  simp only [Module.finrank_fintype_fun_eq_card, Finset.univ_unique, Fin.default_eq_zero,
    Finset.sum_singleton]

omit [DecidableEq d] in
/-- Helper: the triples `(X, g, α)` of one change of basis, two translations and one number per
hidden unit form a space of dimension `d² + 2 d + d_hidden`. -/
private theorem finrank_dirDomainRB_rlb :
    Module.finrank ℝ ((Matrix d d ℝ × (Fin (1 + 1) → d → ℝ)) × (∀ ℓ : Fin 1, hid ℓ → ℝ))
      = Fintype.card d ^ 2 + (1 + 1) * Fintype.card d + Fintype.card (hid 0) := by
  rw [Module.finrank_prod, finrank_cobTrDomain_rlb, Module.finrank_pi_fintype]
  simp only [Module.finrank_fintype_fun_eq_card, Finset.univ_unique, Fin.default_eq_zero,
    Finset.sum_singleton]

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] in
/-- Helper: no column of `W_read` vanishes, since the columns of `C = E W_read` do not. -/
private theorem read_col_ne_zero_rlb
    (p : ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) (hp : OneBlockGeneric p.1) :
    ∀ ℓ i, (fun a => p.1.read ℓ a i) ≠ 0 := by
  intro ℓ i h0
  obtain rfl := Subsingleton.elim ℓ 0
  apply hp.col_ne_zero i
  funext a
  show ∑ j, p.1.E a j * p.1.read 0 j i = 0
  exact Finset.sum_eq_zero fun j _ => by
    rw [show p.1.read 0 j i = 0 from congrFun h0 j, mul_zero]

/-- Helper: the directions that are flat at every input of `noKinkB p` are among the directions
`cobDirB p X + (0, translateAtDir θ g) + rescaleDirMlpB k p α` (the previous theorem). -/
private theorem flatOnB_le_range_rlb {k : ℕ} (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (hU : UnitsRescale σ σ' k dIn dOut (hid 0))
    (p : ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) (hp : OneBlockGeneric p.1) :
    flatOnB (Arch.mlp σ id hid) 0 p (noKinkB p)
      ≤ LinearMap.range ((cobTrAtLin_rlb p).coprod (rescaleDirMlpBLin_rlb k p)) := by
  intro η hη
  obtain ⟨X, g, α, rfl⟩ := flatOnB_noKinkB_le_mlp_rescale hσ hU p hp η hη
  exact LinearMap.mem_range.2 ⟨((X, g), α), rfl⟩

/-- **Theorem B.1 (i) of the skips paper with biases, the skipless network, at one parameter, for
a block with the rescalings:** under the conditions `OneBlockGeneric` on the weights,
`fd = P − 2 d² − 2 d − d_hidden`, with `P` counting the biases. -/
theorem funDimB_mlp_oneBlock_rescale {k : ℕ} (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (hhom : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (hU : UnitsRescale σ σ' k dIn dOut (hid 0))
    (p : ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) (hp : OneBlockGeneric p.1) :
    funDimB (Arch.mlp σ id hid) 0 p
        + (2 * Fintype.card d ^ 2 + 2 * Fintype.card d + Fintype.card (hid 0))
      = Module.finrank ℝ (ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) := by
  -- `≤`: the changes of basis, the translations and the rescalings are flat and independent
  -- (Lemma A.8 with `s = d_hidden`)
  have hle := funDimB_add_le_skipless_mlp_rescale hhom p hp.rank_E (fun ℓ => by
    obtain rfl := Subsingleton.elim ℓ 0
    exact hp.rank_write) (read_col_ne_zero_rlb p hp)
  rw [Fin.sum_univ_one] at hle
  -- `≥`: a flat direction is flat at every input off the kinks, hence one of these directions,
  -- and they span a space of dimension at most `2 d² + 2 d + d_hidden`
  have h1 := Submodule.finrank_mono ((flatB_le_flatOnB (S := 0) p (noKinkB p)).trans
    (flatOnB_le_range_rlb hσ hU p hp))
  have h2 := (LinearMap.finrank_range_le ((cobTrAtLin_rlb p).coprod
    (rescaleDirMlpBLin_rlb k p))).trans_eq (finrank_dirDomainB_rlb (d := d) (hid := hid))
  -- `fd(θ, b) = P − dim K(θ, b)`
  have h3 := funDimB_add_finrank_flatB' (S := 0) p
  omega

/-- The same rank on a batch of inputs with no hidden unit at its kink, as the paper takes the
Jacobian for ReLU blocks. -/
theorem exists_jacobianRankB_mlp_oneBlock_rescale {k : ℕ}
    (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (hhom : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (hU : UnitsRescale σ σ' k dIn dOut (hid 0))
    (p : ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) (hp : OneBlockGeneric p.1) :
    ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i, X i ∈ noKinkB p) ∧
      jacobianRankB (Arch.mlp σ id hid) 0 X p
          + (2 * Fintype.card d ^ 2 + 2 * Fintype.card d + Fintype.card (hid 0))
        = Module.finrank ℝ (ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) := by
  -- a batch of inputs off the kinks, where the network is differentiable in `(θ, b)`, with the
  -- rank `P − dim K_U(θ, b)`, `U = noKinkB p`
  obtain ⟨n, X, hX, h⟩ := exists_jacobianRankB_add_finrank_flatOnB (S := 0) p (noKinkB p)
    (fun x hx => differentiableAt_evalB_of_mem_noKinkB hσ p 0 x hx)
  refine ⟨n, X, hX, ?_⟩
  -- `dim K(θ, b) ≤ dim K_U(θ, b) ≤ 2 d² + 2 d + d_hidden = dim K(θ, b)`
  have hfd := funDimB_mlp_oneBlock_rescale hσ hhom hU p hp
  have h1 := Submodule.finrank_mono (flatB_le_flatOnB (S := 0) p (noKinkB p))
  have h2 := Submodule.finrank_mono (flatOnB_le_range_rlb hσ hU p hp)
  have h3 := (LinearMap.finrank_range_le ((cobTrAtLin_rlb p).coprod
    (rescaleDirMlpBLin_rlb k p))).trans_eq (finrank_dirDomainB_rlb (d := d) (hid := hid))
  have h4 := funDimB_add_finrank_flatB' (S := 0) p
  omega

omit [Fintype T] [Nonempty T] in
/-- Helper (Lemma B.2 with biases, the argument of `flatB_le_range_mlp_residual`): under the
conditions `OneBlockGeneric`, a direction that keeps `M`, `C`, `A`, `β` and `γ` to first order is
the direction of one change of basis `X` of both hidden states and of the translations
`g_0, g_1`. -/
private theorem range_of_keeps_res_rlb
    (p : ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) (hp : OneBlockGeneric p.1)
    (η : ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)
    (hm : η.1.E * p.1.D + p.1.E * η.1.D = 0)
    (hC : η.1.E * p.1.read 0 + p.1.E * η.1.read 0 = 0)
    (hA : η.1.write 0 * p.1.D + p.1.write 0 * η.1.D = 0)
    (hβ : η.2.E ᵥ* p.1.read 0 + p.2.E ᵥ* η.1.read 0 + η.2.read 0 = 0)
    (hγ : η.2.E ᵥ* p.1.D + p.2.E ᵥ* η.1.D
      + (η.2.write 0 ᵥ* p.1.D + p.2.write 0 ᵥ* η.1.D + η.2.D) = 0) :
    ∃ (X : Matrix d d ℝ) (g : Fin 2 → d → ℝ),
      η = cobDirB p (fun _ => X) + (0, translateDir p.1 g) := by
  -- Lemma C.2: a direction that keeps `C` and `A` moves the weights by two changes of basis
  obtain ⟨X, hX⟩ := (keeps_products_iff_mem_range_cobDir p.1 η.1 hp.rank_E hp.rank_D
    hp.rank_read hp.rank_write).1 ⟨hC, hA⟩
  have hE : η.1.E = p.1.E * X 0 := by rw [hX]; rfl
  have hR : η.1.read 0 = -(X 0 * p.1.read 0) := by rw [hX]; rfl
  have hD : η.1.D = -(X 1 * p.1.D) := by rw [hX]; rfl
  -- Lemma B.2: `∂M = E X_0 D − E X_1 D = 0`, so `X_0 = X_1` (`E` and `D` have rank `d`)
  have h01 : X 0 = X 1 := by
    have h := hm
    rw [hE, hD, Matrix.mul_neg, Matrix.mul_assoc, add_neg_eq_zero] at h
    exact cancel_right_of_rank_rlb p.1.D hp.rank_D (cancel_left_of_rank_rlb p.1.E hp.rank_E h)
  have hX' : η.1 = cobDir p.1 (fun _ => X 0) := by
    rw [hX]
    exact congrArg (cobDir p.1) (funext (Fin.forall_fin_two.2 ⟨rfl, h01.symm⟩))
  rw [← h01] at hD
  -- `∂β = 0`: `η_{b_read} = −g_0 W_read` with `g_0 = η_{b_E} − b_E X`
  have hbR : η.2.read 0 = -((η.2.E - p.2.E ᵥ* X 0) ᵥ* p.1.read 0) := by
    have h := hβ
    rw [hR, Matrix.vecMul_neg, ← Matrix.vecMul_vecMul] at h
    rw [Matrix.sub_vecMul]
    linear_combination h
  -- `∂γ = 0`: `η_{b_D} = −(g_0 + g_1) D` with `g_1 = η_{b_write} − b_write X`
  have hbD : η.2.D = -(((η.2.E - p.2.E ᵥ* X 0) + (η.2.write 0 - p.2.write 0 ᵥ* X 0))
      ᵥ* p.1.D) := by
    have h := hγ
    simp only [hD, Matrix.vecMul_neg, ← Matrix.vecMul_vecMul] at h
    rw [Matrix.add_vecMul, Matrix.sub_vecMul, Matrix.sub_vecMul]
    linear_combination h
  -- so `η` is the direction of the change of basis `X` and of the translations `g_0, g_1`
  have hI : Finset.Iic (0 : Fin 1).castSucc = {0} := by decide
  refine ⟨X 0, ![η.2.E - p.2.E ᵥ* X 0, η.2.write 0 - p.2.write 0 ᵥ* X 0], ?_⟩
  refine Prod.ext ?_ ?_
  · show η.1 = cobDir p.1 (fun _ => X 0) + 0
    rw [add_zero]
    exact hX'
  · apply Biases.ext'
    · show η.2.E = p.2.E ᵥ* X 0 + (η.2.E - p.2.E ᵥ* X 0)
      abel
    · intro ℓ
      obtain rfl : ℓ = 0 := Subsingleton.elim ℓ 0
      show η.2.read 0 = 0 + -((∑ k ∈ Finset.Iic (0 : Fin 1).castSucc,
        ![η.2.E - p.2.E ᵥ* X 0, η.2.write 0 - p.2.write 0 ᵥ* X 0] k) ᵥ* p.1.read 0)
      rw [hI, Finset.sum_singleton, zero_add]
      exact hbR
    · intro ℓ
      obtain rfl : ℓ = 0 := Subsingleton.elim ℓ 0
      show η.2.write 0 = p.2.write 0 ᵥ* X 0 + (η.2.write 0 - p.2.write 0 ᵥ* X 0)
      abel
    · show η.2.D = 0 + -((∑ k, ![η.2.E - p.2.E ᵥ* X 0, η.2.write 0 - p.2.write 0 ᵥ* X 0] k)
        ᵥ* p.1.D)
      rw [Fin.sum_univ_two, zero_add]
      exact hbD

/-- **Lemma B.2 with biases, after Lemma B.3, for one residual block with the rescalings:** under
the conditions `OneBlockGeneric` on the weights, a direction that is flat for the residual
network at every input with no hidden unit at its kink is the sum of the direction of one change
of basis `X` of both hidden states and of the translations `g_0, g_1` of Lemma A.8 and of a
direction of the rescalings of the hidden units with their biases. -/
theorem flatOnB_noKinkB_le_mlp_rescale_residual {k : ℕ}
    (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (hU : UnitsRescale σ σ' k dIn dOut (hid 0))
    (p : ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) (hp : OneBlockGeneric p.1)
    (η : ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)
    (hη : η ∈ flatOnB (Arch.mlp σ id hid) 1 p (noKinkB p)) :
    ∃ (X : Matrix d d ℝ) (g : Fin 2 → d → ℝ) (α : ∀ ℓ, hid ℓ → ℝ),
      η = cobDirB p (fun _ => X) + (0, translateDir p.1 g) + rescaleDirMlpB k p α := by
  -- Step 3: at every input with no hidden unit at its kink, the derivative of `F(θ, b, x)` along
  -- `η` vanishes, entry by entry
  have hzero : ∀ x ∈ noKinkB p, ∀ (t : T) (o : dOut), (x * dMm_rlb p.1 η.1) t o
      + dγr_rlb p.1 p.2 η.1 η.2 o
      + ∑ i : hid 0, (σ ((x * Cm_rlb p.1) t i + βm_rlb p.1 p.2 i) * dAm_rlb p.1 η.1 i o
        + σ' ((x * Cm_rlb p.1) t i + βm_rlb p.1 p.2 i)
          * ((x * dCm_rlb p.1 η.1) t i + dβm_rlb p.1 p.2 η.1 η.2 i) * Am_rlb p.1 i o) = 0 := by
    intro x hx t o
    rw [← fderiv_evalB_res_apply_rlb hσ p η x hx t o]
    have h := LinearMap.mem_ker.1 ((Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hη x) hx)
    exact congrFun (congrFun h t) o
  -- Lemma B.3 with the rescalings and the linear term: `∂M = 0`, `∂γ = 0`, `∂c_i = λ_i c_i`,
  -- `∂β_i = λ_i β_i`, `∂a_i = −k λ_i a_i`
  obtain ⟨hm, hγ, lam, hlam⟩ := hU (fun i => (Cm_rlb p.1)ᵀ i) (βm_rlb p.1 p.2)
    (fun i => Am_rlb p.1 i) (dMm_rlb p.1 η.1) (dγr_rlb p.1 p.2 η.1 η.2)
    (fun i => (dCm_rlb p.1 η.1)ᵀ i) (dβm_rlb p.1 p.2 η.1 η.2) (fun i => dAm_rlb p.1 η.1 i)
    (fun i => hp.row_ne_zero i) (fun i => hp.col_ne_zero i)
    (fun i j hij => hp.col_not_collinear i j hij) (by
      intro v hv
      have hx : (Matrix.of fun _ : T => v) ∈ noKinkB p := by
        intro t i
        rw [Matrix.mul_assoc]
        exact hv i
      funext o
      have h := hzero _ hx (Classical.arbitrary T) o
      simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      exact h)
  -- the rescaling with these `λ_i` (one block: `ℓ = 0`)
  let α' : ∀ ℓ : Fin 1, hid ℓ → ℝ := fun ℓ => Fin.cases lam (fun l => l.elim0) ℓ
  -- `η` minus the rescaling keeps `M`, `C`, `A`, `β` and `γ` to first order
  have hM : dMm_rlb p.1 (η.1 - rescaleDirMlp k p.1 α') = 0 := by
    rw [dMm_sub_rescale_rlb]
    exact hm
  have hC : dCm_rlb p.1 (η.1 - rescaleDirMlp k p.1 α') = 0 := by
    ext a i
    rw [dCm_sub_rlb, Matrix.sub_apply, dCm_rescale_rlb, Matrix.zero_apply, sub_eq_zero]
    exact congrFun (hlam i).1 a
  have hA : dAm_rlb p.1 (η.1 - rescaleDirMlp k p.1 α') = 0 := by
    ext i o
    rw [dAm_sub_rlb, Matrix.sub_apply, dAm_rescale_rlb, Matrix.zero_apply, sub_eq_zero]
    exact congrFun (hlam i).2.2 o
  have hβ : dβm_rlb p.1 p.2 (η.1 - rescaleDirMlp k p.1 α') (η.2 - (rescaleDirMlpB k p α').2)
      = 0 := by
    funext i
    rw [dβm_sub_rescale_rlb, Pi.zero_apply, sub_eq_zero]
    exact (hlam i).2.1
  have hγ' : dγr_rlb p.1 p.2 (η.1 - rescaleDirMlp k p.1 α') (η.2 - (rescaleDirMlpB k p α').2)
      = 0 := by
    rw [dγr_sub_rescale_rlb]
    exact hγ
  -- Lemma B.2 with biases: `η` minus the rescaling is a direction of one change of basis and of
  -- the translations
  obtain ⟨X, g, hXg⟩ := range_of_keeps_res_rlb p hp (η - rescaleDirMlpB k p α') hM hC hA hβ hγ'
  exact ⟨X, g, α', sub_eq_iff_eq_add.1 hXg⟩

/-- Helper: the directions that are flat for the residual network at every input of `noKinkB p`
are among the directions `cobDirB p (X, X) + (0, translateDir θ g) + rescaleDirMlpB k p α` (the
previous theorem). -/
private theorem flatOnB_le_range_res_rlb {k : ℕ} (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (hU : UnitsRescale σ σ' k dIn dOut (hid 0))
    (p : ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) (hp : OneBlockGeneric p.1) :
    flatOnB (Arch.mlp σ id hid) 1 p (noKinkB p)
      ≤ LinearMap.range ((cobTrLin_rlb p).coprod (rescaleDirMlpBLin_rlb k p)) := by
  intro η hη
  obtain ⟨X, g, α, rfl⟩ := flatOnB_noKinkB_le_mlp_rescale_residual hσ hU p hp η hη
  exact LinearMap.mem_range.2 ⟨((X, g), α), rfl⟩

/-- **Theorem B.1 (i) of the skips paper with biases, the residual network, at one parameter, for
a block with the rescalings:** under the conditions `OneBlockGeneric` on the weights,
`fd = P − d² − 2 d − d_hidden`, with `P` counting the biases. -/
theorem funDimB_mlp_oneBlock_rescale_residual {k : ℕ}
    (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (hhom : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (hU : UnitsRescale σ σ' k dIn dOut (hid 0))
    (p : ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) (hp : OneBlockGeneric p.1) :
    funDimB (Arch.mlp σ id hid) 1 p
        + (Fintype.card d ^ 2 + 2 * Fintype.card d + Fintype.card (hid 0))
      = Module.finrank ℝ (ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) := by
  -- `≤`: one change of basis, the translations and the rescalings are flat and independent
  -- (Lemma A.8 with `s = d_hidden`)
  have hle := funDimB_add_le_residual_mlp_rescale hhom p hp.rank_E (read_col_ne_zero_rlb p hp)
  rw [Fin.sum_univ_one] at hle
  -- `≥`: a flat direction is flat at every input off the kinks, hence one of these directions,
  -- and they span a space of dimension at most `d² + 2 d + d_hidden`
  have h1 := Submodule.finrank_mono ((flatB_le_flatOnB (S := 1) p (noKinkB p)).trans
    (flatOnB_le_range_res_rlb hσ hU p hp))
  have h2 := (LinearMap.finrank_range_le ((cobTrLin_rlb p).coprod
    (rescaleDirMlpBLin_rlb k p))).trans_eq (finrank_dirDomainRB_rlb (d := d) (hid := hid))
  -- `fd(θ, b) = P − dim K(θ, b)`
  have h3 := funDimB_add_finrank_flatB' (S := 1) p
  omega

/-- The same rank on a batch of inputs with no hidden unit at its kink. -/
theorem exists_jacobianRankB_mlp_oneBlock_rescale_residual {k : ℕ}
    (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (hhom : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (hU : UnitsRescale σ σ' k dIn dOut (hid 0))
    (p : ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) (hp : OneBlockGeneric p.1) :
    ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i, X i ∈ noKinkB p) ∧
      jacobianRankB (Arch.mlp σ id hid) 1 X p
          + (Fintype.card d ^ 2 + 2 * Fintype.card d + Fintype.card (hid 0))
        = Module.finrank ℝ (ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) := by
  -- a batch of inputs off the kinks, where the network is differentiable in `(θ, b)`, with the
  -- rank `P − dim K_U(θ, b)`, `U = noKinkB p`
  obtain ⟨n, X, hX, h⟩ := exists_jacobianRankB_add_finrank_flatOnB (S := 1) p (noKinkB p)
    (fun x hx => differentiableAt_evalB_of_mem_noKinkB hσ p 1 x hx)
  refine ⟨n, X, hX, ?_⟩
  -- `dim K(θ, b) ≤ dim K_U(θ, b) ≤ d² + 2 d + d_hidden = dim K(θ, b)`
  have hfd := funDimB_mlp_oneBlock_rescale_residual hσ hhom hU p hp
  have h1 := Submodule.finrank_mono (flatB_le_flatOnB (S := 1) p (noKinkB p))
  have h2 := Submodule.finrank_mono (flatOnB_le_range_res_rlb hσ hU p hp)
  have h3 := (LinearMap.finrank_range_le ((cobTrLin_rlb p).coprod
    (rescaleDirMlpBLin_rlb k p))).trans_eq (finrank_dirDomainRB_rlb (d := d) (hid := hid))
  have h4 := funDimB_add_finrank_flatB' (S := 1) p
  omega

/-! ### At generic weights and biases -/

/-- **Theorem B.1 (i) of the skips paper with biases, the skipless network, for a block with the
rescalings:** for `d_in, d_out, d_hidden ≥ d ≥ 2`, at generic weights and biases
`fd = P − 2 d² − 2 d − d_hidden`. -/
theorem ae_funDimB_mlp_oneBlock_rescale {k : ℕ}
    (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (hhom : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (hU : UnitsRescale σ σ' k dIn dOut (hid 0))
    (μ : Measure (ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ p ∂μ, funDimB (Arch.mlp σ id hid) 0 p
        + (2 * Fintype.card d ^ 2 + 2 * Fintype.card d + Fintype.card (hid 0))
      = Module.finrank ℝ (ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) :=
  (ae_paramsB_of_forall_ae (fun ν _ => ae_oneBlockGeneric ν hd hdIn hdOut hhid) μ).mono
    fun p hp => funDimB_mlp_oneBlock_rescale hσ hhom hU p hp

/-- The same on the paper's inputs: at generic weights and biases the Jacobian of the skipless
network has the rank `P − 2 d² − 2 d − d_hidden` on a batch of inputs with no hidden unit at its
kink. -/
theorem ae_exists_jacobianRankB_mlp_oneBlock_rescale {k : ℕ}
    (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (hhom : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (hU : UnitsRescale σ σ' k dIn dOut (hid 0))
    (μ : Measure (ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ p ∂μ, ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i, X i ∈ noKinkB p) ∧
      jacobianRankB (Arch.mlp σ id hid) 0 X p
          + (2 * Fintype.card d ^ 2 + 2 * Fintype.card d + Fintype.card (hid 0))
        = Module.finrank ℝ (ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) :=
  (ae_paramsB_of_forall_ae (fun ν _ => ae_oneBlockGeneric ν hd hdIn hdOut hhid) μ).mono
    fun p hp => exists_jacobianRankB_mlp_oneBlock_rescale hσ hhom hU p hp

/-- **Theorem B.1 (i) of the skips paper with biases, the residual network, for a block with the
rescalings:** for `d_in, d_out, d_hidden ≥ d ≥ 2`, at generic weights and biases
`fd = P − d² − 2 d − d_hidden`. -/
theorem ae_funDimB_mlp_oneBlock_rescale_residual {k : ℕ}
    (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (hhom : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (hU : UnitsRescale σ σ' k dIn dOut (hid 0))
    (μ : Measure (ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ p ∂μ, funDimB (Arch.mlp σ id hid) 1 p
        + (Fintype.card d ^ 2 + 2 * Fintype.card d + Fintype.card (hid 0))
      = Module.finrank ℝ (ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) :=
  (ae_paramsB_of_forall_ae (fun ν _ => ae_oneBlockGeneric ν hd hdIn hdOut hhid) μ).mono
    fun p hp => funDimB_mlp_oneBlock_rescale_residual hσ hhom hU p hp

/-- The same on the paper's inputs: at generic weights and biases the Jacobian of the residual
network has the rank `P − d² − 2 d − d_hidden` on a batch of inputs with no hidden unit at its
kink. -/
theorem ae_exists_jacobianRankB_mlp_oneBlock_rescale_residual {k : ℕ}
    (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (hhom : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (hU : UnitsRescale σ σ' k dIn dOut (hid 0))
    (μ : Measure (ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ p ∂μ, ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i, X i ∈ noKinkB p) ∧
      jacobianRankB (Arch.mlp σ id hid) 1 X p
          + (Fintype.card d ^ 2 + 2 * Fintype.card d + Fintype.card (hid 0))
        = Module.finrank ℝ (ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) :=
  (ae_paramsB_of_forall_ae (fun ν _ => ae_oneBlockGeneric ν hd hdIn hdOut hhid) μ).mono
    fun p hp => exists_jacobianRankB_mlp_oneBlock_rescale_residual hσ hhom hU p hp

/-- **Theorem B.1 (i) of the skips paper with biases, "the skip raises the functional dimension
by exactly `d_model²`", for a block with the rescalings:** for `d_in, d_out, d_hidden ≥ d ≥ 2`,
at generic weights and biases. -/
theorem ae_funDimB_mlp_oneBlock_rescale_residual_eq_add {k : ℕ}
    (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (hhom : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (hU : UnitsRescale σ σ' k dIn dOut (hid 0))
    (μ : Measure (ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ p ∂μ, funDimB (Arch.mlp σ id hid) 1 p
      = funDimB (Arch.mlp σ id hid) 0 p + Fintype.card d ^ 2 := by
  filter_upwards [ae_funDimB_mlp_oneBlock_rescale hσ hhom hU μ hd hdIn hdOut hhid,
    ae_funDimB_mlp_oneBlock_rescale_residual hσ hhom hU μ hd hdIn hdOut hhid] with p h0 h1
  omega

/-! ### ReLU -/

/-- **Theorem B.1 (i) with biases for one ReLU block, without the skip:** for
`d_in, d_out, d_hidden ≥ d ≥ 2`, at generic weights and biases `fd = P − 2 d² − 2 d − d_hidden`. -/
theorem ae_funDimB_relu_oneBlock
    (μ : Measure (ParamsB (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ p ∂μ, funDimB (Arch.mlp relu id hid) 0 p
        + (2 * Fintype.card d ^ 2 + 2 * Fintype.card d + Fintype.card (hid 0))
      = Module.finrank ℝ (ParamsB (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut) :=
  ae_funDimB_mlp_oneBlock_rescale (fun _ hz => hasDerivAt_relu hz)
    relu_homogeneous (relu_unitsRescale dIn dOut (hid 0)) μ hd hdIn hdOut hhid

/-- **Theorem B.1 (i) with biases for one ReLU block, without the skip, on the paper's inputs:**
the rank `P − 2 d² − 2 d − d_hidden` on a batch of inputs with no hidden unit at its kink. -/
theorem ae_exists_jacobianRankB_relu_oneBlock
    (μ : Measure (ParamsB (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ p ∂μ, ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i, X i ∈ noKinkB p) ∧
      jacobianRankB (Arch.mlp relu id hid) 0 X p
          + (2 * Fintype.card d ^ 2 + 2 * Fintype.card d + Fintype.card (hid 0))
        = Module.finrank ℝ (ParamsB (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut) :=
  ae_exists_jacobianRankB_mlp_oneBlock_rescale (fun _ hz => hasDerivAt_relu hz)
    relu_homogeneous (relu_unitsRescale dIn dOut (hid 0)) μ hd hdIn hdOut hhid

/-- **Theorem B.1 (i) with biases for one ReLU block, with the skip:** for
`d_in, d_out, d_hidden ≥ d ≥ 2`, at generic weights and biases `fd = P − d² − 2 d − d_hidden`. -/
theorem ae_funDimB_relu_oneBlock_residual
    (μ : Measure (ParamsB (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ p ∂μ, funDimB (Arch.mlp relu id hid) 1 p
        + (Fintype.card d ^ 2 + 2 * Fintype.card d + Fintype.card (hid 0))
      = Module.finrank ℝ (ParamsB (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut) :=
  ae_funDimB_mlp_oneBlock_rescale_residual (fun _ hz => hasDerivAt_relu hz)
    relu_homogeneous (relu_unitsRescale dIn dOut (hid 0)) μ hd hdIn hdOut hhid

/-- **Theorem B.1 (i) with biases for one ReLU block, with the skip, on the paper's inputs:** the
rank `P − d² − 2 d − d_hidden` on a batch of inputs with no hidden unit at its kink. -/
theorem ae_exists_jacobianRankB_relu_oneBlock_residual
    (μ : Measure (ParamsB (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ p ∂μ, ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i, X i ∈ noKinkB p) ∧
      jacobianRankB (Arch.mlp relu id hid) 1 X p
          + (Fintype.card d ^ 2 + 2 * Fintype.card d + Fintype.card (hid 0))
        = Module.finrank ℝ (ParamsB (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut) :=
  ae_exists_jacobianRankB_mlp_oneBlock_rescale_residual (fun _ hz => hasDerivAt_relu hz)
    relu_homogeneous (relu_unitsRescale dIn dOut (hid 0)) μ hd hdIn hdOut hhid

/-- **Theorem B.1 (i) with biases for one ReLU block:** the skip raises the functional dimension
by exactly `d²`. -/
theorem ae_funDimB_relu_oneBlock_residual_eq_add
    (μ : Measure (ParamsB (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ p ∂μ, funDimB (Arch.mlp relu id hid) 1 p
      = funDimB (Arch.mlp relu id hid) 0 p + Fintype.card d ^ 2 :=
  ae_funDimB_mlp_oneBlock_rescale_residual_eq_add (fun _ hz => hasDerivAt_relu hz)
    relu_homogeneous (relu_unitsRescale dIn dOut (hid 0)) μ hd hdIn hdOut hhid

/-! ### ReLU² -/

/-- **Theorem B.1 (i) with biases for one ReLU² block, without the skip:** for
`d_in, d_out, d_hidden ≥ d ≥ 2`, at generic weights and biases `fd = P − 2 d² − 2 d − d_hidden`. -/
theorem ae_funDimB_reluSq_oneBlock
    (μ : Measure (ParamsB (Arch.mlp (T := T) (d := d) reluSq id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ p ∂μ, funDimB (Arch.mlp reluSq id hid) 0 p
        + (2 * Fintype.card d ^ 2 + 2 * Fintype.card d + Fintype.card (hid 0))
      = Module.finrank ℝ (ParamsB (Arch.mlp (T := T) (d := d) reluSq id hid) dIn dOut) :=
  ae_funDimB_mlp_oneBlock_rescale (fun z _ => hasDerivAt_reluSq z)
    reluSq_homogeneous (reluSq_unitsRescale dIn dOut (hid 0)) μ hd hdIn hdOut hhid

/-- **Theorem B.1 (i) with biases for one ReLU² block, without the skip, on the paper's inputs:**
the rank `P − 2 d² − 2 d − d_hidden` on a batch of inputs with no hidden unit at its kink. -/
theorem ae_exists_jacobianRankB_reluSq_oneBlock
    (μ : Measure (ParamsB (Arch.mlp (T := T) (d := d) reluSq id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ p ∂μ, ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i, X i ∈ noKinkB p) ∧
      jacobianRankB (Arch.mlp reluSq id hid) 0 X p
          + (2 * Fintype.card d ^ 2 + 2 * Fintype.card d + Fintype.card (hid 0))
        = Module.finrank ℝ (ParamsB (Arch.mlp (T := T) (d := d) reluSq id hid) dIn dOut) :=
  ae_exists_jacobianRankB_mlp_oneBlock_rescale (fun z _ => hasDerivAt_reluSq z)
    reluSq_homogeneous (reluSq_unitsRescale dIn dOut (hid 0)) μ hd hdIn hdOut hhid

/-- **Theorem B.1 (i) with biases for one ReLU² block, with the skip:** for
`d_in, d_out, d_hidden ≥ d ≥ 2`, at generic weights and biases `fd = P − d² − 2 d − d_hidden`. -/
theorem ae_funDimB_reluSq_oneBlock_residual
    (μ : Measure (ParamsB (Arch.mlp (T := T) (d := d) reluSq id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ p ∂μ, funDimB (Arch.mlp reluSq id hid) 1 p
        + (Fintype.card d ^ 2 + 2 * Fintype.card d + Fintype.card (hid 0))
      = Module.finrank ℝ (ParamsB (Arch.mlp (T := T) (d := d) reluSq id hid) dIn dOut) :=
  ae_funDimB_mlp_oneBlock_rescale_residual (fun z _ => hasDerivAt_reluSq z)
    reluSq_homogeneous (reluSq_unitsRescale dIn dOut (hid 0)) μ hd hdIn hdOut hhid

/-- **Theorem B.1 (i) with biases for one ReLU² block, with the skip, on the paper's inputs:** the
rank `P − d² − 2 d − d_hidden` on a batch of inputs with no hidden unit at its kink. -/
theorem ae_exists_jacobianRankB_reluSq_oneBlock_residual
    (μ : Measure (ParamsB (Arch.mlp (T := T) (d := d) reluSq id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ p ∂μ, ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i, X i ∈ noKinkB p) ∧
      jacobianRankB (Arch.mlp reluSq id hid) 1 X p
          + (Fintype.card d ^ 2 + 2 * Fintype.card d + Fintype.card (hid 0))
        = Module.finrank ℝ (ParamsB (Arch.mlp (T := T) (d := d) reluSq id hid) dIn dOut) :=
  ae_exists_jacobianRankB_mlp_oneBlock_rescale_residual (fun z _ => hasDerivAt_reluSq z)
    reluSq_homogeneous (reluSq_unitsRescale dIn dOut (hid 0)) μ hd hdIn hdOut hhid

/-- **Theorem B.1 (i) with biases for one ReLU² block:** the skip raises the functional dimension
by exactly `d²`. -/
theorem ae_funDimB_reluSq_oneBlock_residual_eq_add
    (μ : Measure (ParamsB (Arch.mlp (T := T) (d := d) reluSq id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ p ∂μ, funDimB (Arch.mlp reluSq id hid) 1 p
      = funDimB (Arch.mlp reluSq id hid) 0 p + Fintype.card d ^ 2 :=
  ae_funDimB_mlp_oneBlock_rescale_residual_eq_add (fun z _ => hasDerivAt_reluSq z)
    reluSq_homogeneous (reluSq_unitsRescale dIn dOut (hid 0)) μ hd hdIn hdOut hhid

end Skips
