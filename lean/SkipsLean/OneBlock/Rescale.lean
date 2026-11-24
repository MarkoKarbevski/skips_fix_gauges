import SkipsLean.Dimension.RescalingMlp
import SkipsLean.OneBlock.Mlp
import SkipsLean.OneBlock.UnitsReLU

/-!
# The one-block theorem for ReLU and ReLU² blocks

Paper (dimension): Theorem 5.1 (Theorem C.1 in the appendix) for a ReLU and for a ReLU² block:
at generic parameters the functional dimension of a network of one block without normalization is
`P - 2 d² - s`, where `s = d_hidden` counts the rescalings of the hidden units.

For ReLU blocks the paper takes the Jacobian at the inputs at which no hidden unit sits at its
kink (Appendix C, "Notation and flat directions"). In Lean the functional dimension `funDim` is
the largest rank of the Jacobian over all finite batches, and a batch with an input at which the
network is not differentiable in `θ` has rank `0` (`Dimension/Functional.lean`, last section). So
two statements are made for each kind of block: the value of `funDim`, and a batch of inputs with
no hidden unit at its kink on which the Jacobian has that rank. Together they give the paper's
maximum over such batches.

The proof is stated once, for every activation `σ` that is positively homogeneous of degree `k`,
differentiable away from `0`, and satisfies Lemma C.3 with the rescalings (`UnitsRescale`).
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

/-- **The conclusion of Lemma C.3 for an activation whose hidden units have the rescaling
`(c_i, a_i) ↦ (λ c_i, a_i / λ^k)`** (ReLU with `k = 1`, ReLU² with `k = 2`), as a property of `σ`
and of its derivative `σ'` away from the kink. The function is
`G(φ, x) = x M + γ + ∑_i σ(x c_i + β_i) a_i`; if every `a_i` is nonzero and the `c_i` are nonzero
and pairwise non-collinear, then a direction `ψ` of the weights along which the derivative of `G`
vanishes at every input `x` with no hidden unit at its kink only rescales each hidden unit:
`(ψ_c, ψ_β) = λ (c, β)` and `ψ_a = -k λ a`, with `ψ_M = 0` and `ψ_γ = 0`. -/
def UnitsRescale (σ σ' : ℝ → ℝ) (k : ℕ) (n m q : Type*) [Fintype n] [Fintype m] [Fintype q] :
    Prop :=
  ∀ (c : q → n → ℝ) (β : q → ℝ) (a : q → m → ℝ)
    (ψM : Matrix n m ℝ) (ψγ : m → ℝ) (ψc : q → n → ℝ) (ψβ : q → ℝ) (ψa : q → m → ℝ),
    (∀ i, a i ≠ 0) → (∀ i, c i ≠ 0) → (∀ i j, i ≠ j → ∀ r : ℝ, c i ≠ r • c j) →
    (∀ x : n → ℝ, (∀ i, x ⬝ᵥ c i + β i ≠ 0) →
      x ᵥ* ψM + ψγ + ∑ i, (σ (x ⬝ᵥ c i + β i) • ψa i
        + (σ' (x ⬝ᵥ c i + β i) * (x ⬝ᵥ ψc i + ψβ i)) • a i) = 0) →
    ψM = 0 ∧ ψγ = 0 ∧
      ∃ lam : q → ℝ, ∀ i, ψc i = lam i • c i ∧ ψβ i = lam i * β i ∧
        ψa i = -((k : ℝ) * lam i) • a i

/-- Lemma C.3 for ReLU, in the form `UnitsRescale` with `k = 1`. -/
theorem relu_unitsRescale (n m q : Type*) [Fintype n] [Fintype m] [Fintype q] :
    UnitsRescale relu reluDeriv 1 n m q := by
  intro c β a ψM ψγ ψc ψβ ψa ha hc hcol h
  obtain ⟨hM, hγ, lam, hlam⟩ := relu_units_flat c β a ψM ψγ ψc ψβ ψa ha hc hcol h
  refine ⟨hM, hγ, lam, fun i => ⟨(hlam i).1, (hlam i).2.1, ?_⟩⟩
  -- `k = 1`: the write row moves by `-λ_i a_i`
  rw [(hlam i).2.2, Nat.cast_one, one_mul]

/-- Lemma C.3 for ReLU², in the form `UnitsRescale` with `k = 2`. -/
theorem reluSq_unitsRescale (n m q : Type*) [Fintype n] [Fintype m] [Fintype q] :
    UnitsRescale reluSq reluSqDeriv 2 n m q := by
  intro c β a ψM ψγ ψc ψβ ψa ha hc hcol h
  obtain ⟨hM, hγ, lam, hlam⟩ := reluSq_units_flat c β a ψM ψγ ψc ψβ ψa ha hc hcol h
  refine ⟨hM, hγ, lam, fun i => ⟨(hlam i).1, (hlam i).2.1, ?_⟩⟩
  -- `k = 2`: the write row moves by `-2 λ_i a_i`
  rw [(hlam i).2.2, Nat.cast_ofNat]

variable {T d dIn dOut : Type*} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {hid : Fin 1 → Type} [∀ ℓ, Fintype (hid ℓ)]
variable {σ σ' : ℝ → ℝ}

/-- The inputs at which no hidden unit of the block sits at its kink: every entry of
`x E W_read` (one per token and hidden unit) is nonzero. -/
def noKink (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) :
    Set (Matrix T dIn ℝ) :=
  {x | ∀ (t : T) (i : hid 0), (x * θ.E * θ.read 0) t i ≠ 0}

/-! ### Helpers: the function of one MLP block and its derivative (as in `Mlp.lean`) -/

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

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dOut] in
/-- Helper: the function of one MLP block, `F_θ(x) = σ(x C) A` (the stream matrix is `0`). -/
private theorem eval_mlp_eq (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)
    (x : Matrix T dIn ℝ) :
    eval (Arch.mlp σ id hid) 0 θ x = (x * Cm θ).map σ * Am θ := by
  have h1 : (Fin.last 1 : Fin 2) = (0 : Fin 1).succ := rfl
  have hχ : (Arch.mlp (T := T) (d := d) σ id hid).χ = id := rfl
  have hf : (Arch.mlp (T := T) (d := d) σ id hid).f 0 = fun M => M.map σ := rfl
  -- `h_1 = h_0 0 + σ(h_0 W_read) W_write` with `h_0 = x E`
  rw [eval, h1, hidden_succ, Fin.castSucc_zero, hidden_zero, hχ, hf]
  simp only [Pi.zero_apply, Matrix.mul_zero, zero_add, id_eq]
  rw [Matrix.mul_assoc x θ.E (θ.read 0)]
  exact Matrix.mul_assoc _ _ _

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dOut] in
/-- Helper: the entries of `F_θ(x)`, `∑_i σ((x C)_{t i}) A_{i o}`. -/
private theorem eval_mlp_apply
    (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)
    (x : Matrix T dIn ℝ) (t : T) (o : dOut) :
    eval (Arch.mlp σ id hid) 0 θ x t o
      = ∑ i : hid 0, σ ((x * Cm θ) t i) * Am θ i o := by
  rw [eval_mlp_eq, Matrix.mul_apply]
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

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dOut] in
/-- Helper: the entries of `F_{θ + τ η}(x)` as functions of `τ`. -/
private theorem eval_line_apply
    (θ η : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)
    (x : Matrix T dIn ℝ) (t : T) (o : dOut) (τ : ℝ) :
    eval (Arch.mlp σ id hid) 0 (θ + τ • η) x t o = ∑ i : hid 0,
      σ ((x * Cm θ) t i + τ * (x * dCm θ η) t i + τ * τ * (x * Cm η) t i) *
        (Am θ i o + τ * dAm θ η i o + τ * τ * Am η i o) := by
  rw [eval_mlp_apply, Cm_line, Am_line]
  simp only [Matrix.mul_add, Matrix.mul_smul]
  rfl

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dOut] in
/-- Helper: at an input of `noKink θ`, every entry of `x C` is nonzero. -/
private theorem noKink_apply {θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut}
    {x : Matrix T dIn ℝ} (hx : x ∈ noKink θ) (t : T) (i : hid 0) : (x * Cm θ) t i ≠ 0 := by
  have h := hx t i
  rwa [Matrix.mul_assoc] at h

/-- At an input with no hidden unit at its kink, the output of a network of one block is
differentiable in the parameters, when `σ` is differentiable away from `0`. -/
theorem differentiableAt_eval_of_mem_noKink (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) (x : Matrix T dIn ℝ)
    (hx : x ∈ noKink θ) :
    DifferentiableAt ℝ
      (fun θ' : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut =>
        eval (Arch.mlp σ id hid) 0 θ' x) θ := by
  -- the entries of `C = E W_read` and of `A = W_write D` are polynomials in the parameters
  have hC : ∀ (a : dIn) (i : hid 0), DifferentiableAt ℝ
      (fun θ' : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut => Cm θ' a i) θ :=
    fun a i => (analyticOnNhd_E_mul_read (A := Arch.mlp (T := T) (d := d) σ id hid)
      (dOut := dOut) 0 a i θ (Set.mem_univ _)).differentiableAt
  have hA : ∀ (i : hid 0) (o : dOut), DifferentiableAt ℝ
      (fun θ' : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut => Am θ' i o) θ :=
    fun i o => (analyticOnNhd_write_mul_D (A := Arch.mlp (T := T) (d := d) σ id hid)
      (dIn := dIn) 0 i o θ (Set.mem_univ _)).differentiableAt
  -- so are the entries of `x C`
  have hxC : ∀ (t : T) (i : hid 0), DifferentiableAt ℝ
      (fun θ' : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut => (x * Cm θ') t i) θ := by
    intro t i
    simp only [Matrix.mul_apply]
    exact DifferentiableAt.fun_sum fun a _ => (hC a i).const_mul (x t a)
  -- the entry `(t, o)` of `F_θ'(x)` is `∑_i σ((x C)_{t i}) A_{i o}`, and `σ` is differentiable
  -- at every `(x C)_{t i}`, which is not `0`
  refine differentiableAt_pi.2 fun t => differentiableAt_pi.2 fun o => ?_
  simp only [eval_mlp_apply]
  exact DifferentiableAt.fun_sum fun i _ =>
    ((hσ _ (noKink_apply hx t i)).differentiableAt.comp θ (hxC t i)).mul (hA i o)

/-- Helper (Step 3 of the paper, the chain rule, at an input of `noKink θ`): the derivative of
`θ ↦ F_θ(x)` along `η` has the entries `∑_i [σ(z_i) (∂A)_{i o} + σ'(z_i) (x ∂C)_{t i} A_{i o}]`,
`z_i = (x C)_{t i}`. -/
private theorem fderiv_eval_apply_of_mem (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (θ η : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)
    (x : Matrix T dIn ℝ) (hx : x ∈ noKink θ) (t : T) (o : dOut) :
    fderiv ℝ (fun θ' => eval (Arch.mlp σ id hid) 0 θ' x) θ η t o = ∑ i : hid 0,
      (σ ((x * Cm θ) t i) * dAm θ η i o
        + σ' ((x * Cm θ) t i) * (x * dCm θ η) t i * Am θ i o) := by
  -- the chain rule along the line `τ ↦ θ + τ η`
  have h1 := hasDerivAt_eval_line (A := Arch.mlp (T := T) (d := d) σ id hid) 0 θ η x
    (differentiableAt_eval_of_mem_noKink hσ θ x hx)
  have h2 := hasDerivAt_pi.1 (hasDerivAt_pi.1 h1 t) o
  -- the same derivative computed entrywise: products and sums of real functions of `τ`
  have h3 : HasDerivAt (fun τ : ℝ => eval (Arch.mlp σ id hid) 0 (θ + τ • η) x t o)
      (∑ i : hid 0, (σ ((x * Cm θ) t i) * dAm θ η i o
        + σ' ((x * Cm θ) t i) * (x * dCm θ η) t i * Am θ i o)) 0 := by
    rw [funext fun τ => eval_line_apply θ η x t o τ]
    refine HasDerivAt.fun_sum fun i _ => ?_
    have hu := hasDerivAt_quad ((x * Cm θ) t i) ((x * dCm θ η) t i) ((x * Cm η) t i)
    have hv := hasDerivAt_quad (Am θ i o) (dAm θ η i o) (Am η i o)
    -- `σ` is differentiable at `(x C)_{t i}`, which is not `0`
    have h := ((hσ _ (noKink_apply hx t i)).comp_of_eq (0 : ℝ) hu
      (by simp only [zero_mul, add_zero])).mul hv
    convert h using 1
    · rfl
    · simp only [Function.comp_apply, zero_mul, mul_zero, add_zero]
      ring
  exact h2.unique h3

/-! ### Helpers: the derivative of `C` and `A` along a rescaling (as in `Gated.lean`) -/

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: `∂C` is linear in the direction. -/
private theorem dCm_sub (θ η ρ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) :
    dCm θ (η - ρ) = dCm θ η - dCm θ ρ := by
  show (η.E - ρ.E) * rd θ + θ.E * (rd η - rd ρ)
    = (η.E * rd θ + θ.E * rd η) - (ρ.E * rd θ + θ.E * rd ρ)
  rw [Matrix.sub_mul, Matrix.mul_sub]
  abel

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: `∂A` is linear in the direction. -/
private theorem dAm_sub (θ η ρ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) :
    dAm θ (η - ρ) = dAm θ η - dAm θ ρ := by
  show (wr η - wr ρ) * θ.D + wr θ * (η.D - ρ.D)
    = (wr η * θ.D + wr θ * η.D) - (wr ρ * θ.D + wr θ * ρ.D)
  rw [Matrix.sub_mul, Matrix.mul_sub]
  abel

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: along a rescaling, the column `c_i` of `C` moves by `α_i c_i`. -/
private theorem dCm_rescale (k : ℕ)
    (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) (α : ∀ ℓ, hid ℓ → ℝ)
    (a : dIn) (i : hid 0) :
    dCm θ (rescaleDirMlp k θ α) a i = α 0 i * Cm θ a i := by
  show ((0 : Matrix dIn d ℝ) * rd θ + θ.E * rd (rescaleDirMlp k θ α)) a i
    = α 0 i * (θ.E * rd θ) a i
  rw [Matrix.zero_mul, zero_add, Matrix.mul_apply, Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  show θ.E a j * (α 0 i * θ.read 0 j i) = α 0 i * (θ.E a j * θ.read 0 j i)
  ring

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: along a rescaling, the row `a_i` of `A` moves by `-k α_i a_i`. -/
private theorem dAm_rescale (k : ℕ)
    (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) (α : ∀ ℓ, hid ℓ → ℝ)
    (i : hid 0) (o : dOut) :
    dAm θ (rescaleDirMlp k θ α) i o = -((k : ℝ) * α 0 i) * Am θ i o := by
  show (wr (rescaleDirMlp k θ α) * θ.D + wr θ * (0 : Matrix d dOut ℝ)) i o
    = -((k : ℝ) * α 0 i) * (wr θ * θ.D) i o
  rw [Matrix.mul_zero, add_zero, Matrix.mul_apply, Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  show -((k : ℝ) * α 0 i) * θ.write 0 i j * θ.D j o
    = -((k : ℝ) * α 0 i) * (θ.write 0 i j * θ.D j o)
  ring

/-- **Steps 1 to 3 of the proof of Theorem 5.1 for an activation with the rescalings.** Under the
conditions `OneBlockGeneric`, a direction that is flat at every input with no hidden unit at its
kink is the sum of a direction of the changes of basis at the two hidden states and a direction
of the rescalings of the hidden units. -/
theorem flatOn_noKink_le_mlp_rescale {k : ℕ} (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (hU : UnitsRescale σ σ' k dIn dOut (hid 0))
    (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) (hθ : OneBlockGeneric θ)
    (η : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)
    (hη : η ∈ flatOn (Arch.mlp σ id hid) 0 θ (noKink θ)) :
    ∃ (X : Fin 2 → Matrix d d ℝ) (α : ∀ ℓ, hid ℓ → ℝ),
      η = cobDir θ X + rescaleDirMlp k θ α := by
  -- Step 3: at every input with no hidden unit at its kink, the derivative of `F(θ, x)` along
  -- `η` vanishes, entry by entry
  have hzero : ∀ x ∈ noKink θ, ∀ (t : T) (o : dOut), ∑ i : hid 0,
      (σ ((x * Cm θ) t i) * dAm θ η i o
        + σ' ((x * Cm θ) t i) * (x * dCm θ η) t i * Am θ i o) = 0 := by
    intro x hx t o
    rw [← fderiv_eval_apply_of_mem hσ θ η x hx t o]
    have h := LinearMap.mem_ker.1 ((Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hη x) hx)
    exact congrFun (congrFun h t) o
  -- Step 2, Lemma C.3 (inputs `x` with all rows equal to a `v` with `v c_i ≠ 0` for all `i`):
  -- every unit is only rescaled, `∂c_i = λ_i c_i` and `∂a_i = -k λ_i a_i`
  obtain ⟨-, -, lam, hlam⟩ := hU (fun i => (Cm θ)ᵀ i) 0 (fun i => Am θ i)
    0 0 (fun i => (dCm θ η)ᵀ i) 0 (fun i => dAm θ η i) (fun i => hθ.row_ne_zero i)
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
      simp only [Matrix.vecMul_zero, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        Pi.zero_apply, add_zero, zero_add]
      exact h)
  -- the rescaling with these `λ_i` (one block: `ℓ = 0`)
  let α' : ∀ ℓ : Fin 1, hid ℓ → ℝ := fun ℓ => Fin.cases lam (fun l => l.elim0) ℓ
  -- `η - rescaleDirMlp k θ α'` keeps `C` and `A` to first order
  have hC : dCm θ (η - rescaleDirMlp k θ α') = 0 := by
    ext a i
    rw [dCm_sub, Matrix.sub_apply, dCm_rescale, Matrix.zero_apply, sub_eq_zero]
    exact congrFun (hlam i).1 a
  have hA : dAm θ (η - rescaleDirMlp k θ α') = 0 := by
    ext i o
    rw [dAm_sub, Matrix.sub_apply, dAm_rescale, Matrix.zero_apply, sub_eq_zero]
    exact congrFun (hlam i).2.2 o
  -- Step 1, Lemma C.2: a direction that keeps `C` and `A` is that of two changes of basis
  obtain ⟨X, hX⟩ := (keeps_products_iff_mem_range_cobDir θ (η - rescaleDirMlp k θ α')
    hθ.rank_E hθ.rank_D hθ.rank_read hθ.rank_write).1 ⟨hC, hA⟩
  exact ⟨X, α', sub_eq_iff_eq_add.1 hX⟩

/-- **Theorem 5.1 / C.1 for an activation with the rescalings, under the conditions of the
proof:** `fd = P - 2 d² - d_hidden`. -/
theorem funDim_mlp_oneBlock_rescale {k : ℕ} (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (hhom : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (hU : UnitsRescale σ σ' k dIn dOut (hid 0))
    (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) (hθ : OneBlockGeneric θ) :
    funDim (Arch.mlp σ id hid) 0 θ + (2 * Fintype.card d ^ 2 + Fintype.card (hid 0))
      = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) := by
  sorry

/-- The same rank on a batch of inputs with no hidden unit at its kink, as the paper takes the
Jacobian for ReLU blocks. -/
theorem exists_jacobianRank_mlp_oneBlock_rescale {k : ℕ}
    (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (hhom : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (hU : UnitsRescale σ σ' k dIn dOut (hid 0))
    (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) (hθ : OneBlockGeneric θ) :
    ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i, X i ∈ noKink θ) ∧
      jacobianRank (Arch.mlp σ id hid) 0 X θ + (2 * Fintype.card d ^ 2 + Fintype.card (hid 0))
        = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) := by
  sorry

/-- **Theorem 5.1 / C.1 for a ReLU block:** for `d_in, d_out, d_hidden ≥ d ≥ 2`, at generic
parameters, `fd = P - 2 d² - d_hidden`. -/
theorem ae_funDim_relu_oneBlock
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ θ ∂μ, funDim (Arch.mlp relu id hid) 0 θ
        + (2 * Fintype.card d ^ 2 + Fintype.card (hid 0))
      = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut) := by
  sorry

/-- **Theorem 5.1 / C.1 for a ReLU block, on the paper's inputs:** at generic parameters the
Jacobian has the rank `P - 2 d² - d_hidden` on a batch of inputs with no hidden unit at its
kink. -/
theorem ae_exists_jacobianRank_relu_oneBlock
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ θ ∂μ, ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i, X i ∈ noKink θ) ∧
      jacobianRank (Arch.mlp relu id hid) 0 X θ
          + (2 * Fintype.card d ^ 2 + Fintype.card (hid 0))
        = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut) := by
  sorry

/-- **Theorem 5.1 / C.1 for a ReLU² block:** for `d_in, d_out, d_hidden ≥ d ≥ 2`, at generic
parameters, `fd = P - 2 d² - d_hidden`. -/
theorem ae_funDim_reluSq_oneBlock
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) reluSq id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ θ ∂μ, funDim (Arch.mlp reluSq id hid) 0 θ
        + (2 * Fintype.card d ^ 2 + Fintype.card (hid 0))
      = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) reluSq id hid) dIn dOut) := by
  sorry

/-- **Theorem 5.1 / C.1 for a ReLU² block, on the paper's inputs:** at generic parameters the
Jacobian has the rank `P - 2 d² - d_hidden` on a batch of inputs with no hidden unit at its
kink. -/
theorem ae_exists_jacobianRank_reluSq_oneBlock
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) reluSq id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ θ ∂μ, ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i, X i ∈ noKink θ) ∧
      jacobianRank (Arch.mlp reluSq id hid) 0 X θ
          + (2 * Fintype.card d ^ 2 + Fintype.card (hid 0))
        = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) reluSq id hid) dIn dOut) := by
  sorry

end Skips
