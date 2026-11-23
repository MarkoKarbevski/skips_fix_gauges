import SkipsLean.Dimension.Rescaling
import SkipsLean.OneBlock.Common
import SkipsLean.OneBlock.Factorization

/-!
# The one-block theorem for a gated block whose only symmetries inside are the rescalings

Paper (dimension paper): Theorem 5.1 (Theorem C.1 in the appendix), for the SwiGLU and the GeGLU
blocks: with one block, without normalization and without biases, at generic parameters the
functional dimension is `P - 2 d² - s`, where `s = d_hidden` counts the rescalings of the values
of the hidden units.

The network is `x ↦ f(x E W_read) W_write D` with `W_read = [W_g | W_v]` and
`f(z, w)_i = σ(z_i) w_i`. With `C = E W_read` and `A = W_write D`, hidden unit `i` has the gate
column `c_i` (column `Sum.inl i` of `C`), the value column `e_i` (column `Sum.inr i` of `C`) and
the write row `a_i` (row `i` of `A`). The conditions that the proof uses are: `E`, `D`, `W_read`
and `W_write` have rank `d`, every `a_i` and every `e_i` is nonzero, and the `c_i` are nonzero and
pairwise non-collinear (`OneBlockGenericGated`). Under them the flat directions are exactly the
sums of a direction of the two changes of basis and a direction of the rescalings.

The proof of the paper has three steps, and only Step 2 (Lemma C.3) depends on the gate
activation. So the theorem is stated here for every gate activation `σ` with derivative `σ'` for
which the conclusion of Lemma C.3 for SwiGLU and GeGLU holds (`GatedUnitsRescale σ σ'`).
`SwiGLU.lean` and `GeGLU.lean` apply it.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

/-- **The conclusion of Lemma C.3 for SwiGLU and GeGLU,** as a property of the gate activation `σ`
and of its derivative `σ'`. Rows are indexed by `n` (the coordinates of an input `x`), hidden units
by `q`, and the coordinates of the output by `k`. The function is
`G(φ, x) = x M + γ + ∑_i σ(x c_i + β_i) (x e_i + β'_i) a_i`; if every `a_i` and every `e_i` is
nonzero and the `c_i` are nonzero and pairwise non-collinear, then a direction `ψ` of the weights
along which the derivative of `G` vanishes at every input `x` only rescales the value of each
hidden unit: `ψ_M = 0`, `ψ_γ = 0`, `ψ_{c_i} = 0`, `ψ_{β_i} = 0`, and
`(ψ_{e_i}, ψ_{β'_i}) = -α_i (e_i, β'_i)`, `ψ_{a_i} = α_i a_i` for some numbers `α_i`. The paper also
assumes that `(e_i, β'_i)` is not proportional to `(c_i, β_i)`; the proofs for SwiGLU and GeGLU do
not use it. -/
def GatedUnitsRescale (σ σ' : ℝ → ℝ) (n k q : Type*) [Fintype n] [Fintype k] [Fintype q] : Prop :=
  ∀ (c : q → n → ℝ) (β : q → ℝ) (e : q → n → ℝ) (β' : q → ℝ) (a : q → k → ℝ)
    (ψM : Matrix n k ℝ) (ψγ : k → ℝ) (ψc : q → n → ℝ) (ψβ : q → ℝ) (ψe : q → n → ℝ)
    (ψβ' : q → ℝ) (ψa : q → k → ℝ),
    (∀ i, a i ≠ 0) → (∀ i, c i ≠ 0) → (∀ i j, i ≠ j → ∀ r : ℝ, c i ≠ r • c j) →
    (∀ i, e i ≠ 0) →
    (∀ x : n → ℝ,
      x ᵥ* ψM + ψγ + ∑ i,
        ((σ (x ⬝ᵥ c i + β i) * (x ⬝ᵥ e i + β' i)) • ψa i
          + (σ' (x ⬝ᵥ c i + β i) * (x ⬝ᵥ ψc i + ψβ i) * (x ⬝ᵥ e i + β' i)) • a i
          + (σ (x ⬝ᵥ c i + β i) * (x ⬝ᵥ ψe i + ψβ' i)) • a i) = 0) →
    ψM = 0 ∧ ψγ = 0 ∧ ψc = 0 ∧ ψβ = 0 ∧
      ∃ α : q → ℝ, ∀ i, ψe i = -(α i) • e i ∧ ψβ' i = -(α i) * β' i ∧ ψa i = α i • a i

variable {T d dIn dOut : Type*} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {hid : Fin 1 → Type} [∀ ℓ, Fintype (hid ℓ)]
variable {σ σ' : ℝ → ℝ}

/-- The conditions on the parameters of one gated block that the proof of the one-block theorem
uses. They do not depend on the gate activation. -/
structure OneBlockGenericGated
    (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) : Prop where
  rank_E : θ.E.rank = Fintype.card d
  rank_D : θ.D.rank = Fintype.card d
  rank_read : (θ.read 0).rank = Fintype.card d
  rank_write : (θ.write 0).rank = Fintype.card d
  /-- every row `a_i` of `A = W_write D` is nonzero -/
  row_ne_zero : ∀ i, (θ.write 0 * θ.D) i ≠ 0
  /-- every gate column `c_i` of `C = E W_read` is nonzero -/
  gate_ne_zero : ∀ i : hid 0, (θ.E * θ.read 0)ᵀ (Sum.inl i) ≠ 0
  /-- the gate columns of `C` are pairwise non-collinear -/
  gate_not_collinear : ∀ i j : hid 0, i ≠ j → ∀ r : ℝ,
    (θ.E * θ.read 0)ᵀ (Sum.inl i) ≠ r • (θ.E * θ.read 0)ᵀ (Sum.inl j)
  /-- every value column `e_i` of `C` is nonzero -/
  value_ne_zero : ∀ i : hid 0, (θ.E * θ.read 0)ᵀ (Sum.inr i) ≠ 0

/-! ### Helpers: the function of one gated block and its derivative -/

/-- Helper: the read of the block, with its columns indexed by the gates and values. -/
private def rd (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) :
    Matrix d (hid 0 ⊕ hid 0) ℝ :=
  θ.read 0

/-- Helper: the write of the block, with its rows indexed by the hidden units. -/
private def wr (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) :
    Matrix (hid 0) d ℝ :=
  θ.write 0

/-- Helper: `C = E W_read`. -/
private def Cm (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) :
    Matrix dIn (hid 0 ⊕ hid 0) ℝ :=
  θ.E * rd θ

/-- Helper: `A = W_write D`. -/
private def Am (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) :
    Matrix (hid 0) dOut ℝ :=
  wr θ * θ.D

/-- Helper: the derivative `∂C = η_E W_read + E η_read` of `C` along `η`. -/
private def dCm (θ η : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) :
    Matrix dIn (hid 0 ⊕ hid 0) ℝ :=
  η.E * rd θ + θ.E * rd η

/-- Helper: the derivative `∂A = η_write D + W_write η_D` of `A` along `η`. -/
private def dAm (θ η : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) :
    Matrix (hid 0) dOut ℝ :=
  wr η * θ.D + wr θ * η.D

omit [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the read is linear in the parameters. -/
private theorem rd_line (θ η : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (τ : ℝ) : rd (θ + τ • η) = rd θ + τ • rd η := rfl

omit [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the write is linear in the parameters. -/
private theorem wr_line (θ η : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (τ : ℝ) : wr (θ + τ • η) = wr θ + τ • wr η := rfl

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dOut] in
/-- Helper: the function of one gated block, `F_θ(x) = (σ(x C_g) ⊙ (x C_v)) A` (the stream
matrix is `0`). -/
private theorem eval_gated_eq (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (x : Matrix T dIn ℝ) :
    eval (Arch.gated σ id hid) 0 θ x
      = (Matrix.of fun t i => σ ((x * Cm θ) t (Sum.inl i)) * (x * Cm θ) t (Sum.inr i))
        * Am θ := by
  have h1 : (Fin.last 1 : Fin 2) = (0 : Fin 1).succ := rfl
  have hχ : (Arch.gated (T := T) (d := d) σ id hid).χ = id := rfl
  have hf : (Arch.gated (T := T) (d := d) σ id hid).f 0
      = fun M => Matrix.of fun t i => σ (M t (Sum.inl i)) * M t (Sum.inr i) := rfl
  -- `h_1 = h_0 0 + f(h_0 W_read) W_write` with `h_0 = x E`
  rw [eval, h1, hidden_succ, Fin.castSucc_zero, hidden_zero, hχ, hf]
  simp only [Pi.zero_apply, Matrix.mul_zero, zero_add, id_eq]
  rw [Matrix.mul_assoc x θ.E (θ.read 0)]
  exact Matrix.mul_assoc _ _ _

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dOut] in
/-- Helper: the entries of `F_θ(x)`, `∑_i σ((x C)_{t, g i}) (x C)_{t, v i} A_{i o}`. -/
private theorem eval_gated_apply
    (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (x : Matrix T dIn ℝ) (t : T) (o : dOut) :
    eval (Arch.gated σ id hid) 0 θ x t o
      = ∑ i : hid 0, σ ((x * Cm θ) t (Sum.inl i)) * (x * Cm θ) t (Sum.inr i) * Am θ i o := by
  rw [eval_gated_eq, Matrix.mul_apply]
  rfl

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: along the line, `C(τ) = C + τ ∂C + τ² η_E η_read`. -/
private theorem Cm_line (θ η : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (τ : ℝ) :
    Cm (θ + τ • η) = Cm θ + τ • dCm θ η + (τ * τ) • Cm η := by
  simp only [Cm, dCm, rd_line, Params.add_E, Params.smul_E, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_smul, Matrix.smul_mul, smul_add, smul_smul]
  abel

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: along the line, `A(τ) = A + τ ∂A + τ² η_write η_D`. -/
private theorem Am_line (θ η : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (τ : ℝ) :
    Am (θ + τ • η) = Am θ + τ • dAm θ η + (τ * τ) • Am η := by
  simp only [Am, dAm, wr_line, Params.add_D, Params.smul_D, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_smul, Matrix.smul_mul, smul_add, smul_smul]
  abel

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dOut] in
/-- Helper: the entries of `F_{θ + τ η}(x)` as functions of `τ`. -/
private theorem eval_line_apply
    (θ η : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (x : Matrix T dIn ℝ) (t : T) (o : dOut) (τ : ℝ) :
    eval (Arch.gated σ id hid) 0 (θ + τ • η) x t o = ∑ i : hid 0,
      σ ((x * Cm θ) t (Sum.inl i) + τ * (x * dCm θ η) t (Sum.inl i)
          + τ * τ * (x * Cm η) t (Sum.inl i)) *
        ((x * Cm θ) t (Sum.inr i) + τ * (x * dCm θ η) t (Sum.inr i)
          + τ * τ * (x * Cm η) t (Sum.inr i)) *
        (Am θ i o + τ * dAm θ η i o + τ * τ * Am η i o) := by
  rw [eval_gated_apply, Cm_line, Am_line]
  simp only [Matrix.mul_add, Matrix.mul_smul]
  rfl

omit [Nonempty T] [DecidableEq d] in
/-- Helper (Step 3 of the paper, the chain rule): the derivative of `θ ↦ F_θ(x)` along `η` has
the entries `∑_i [σ(z_i) w_i (∂A)_{i o} + σ'(z_i) (x ∂C)_{t, g i} w_i A_{i o}
+ σ(z_i) (x ∂C)_{t, v i} A_{i o}]`, with `z_i = (x C)_{t, g i}` and `w_i = (x C)_{t, v i}`. -/
private theorem fderiv_eval_apply (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (θ η : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (x : Matrix T dIn ℝ) (t : T) (o : dOut) :
    fderiv ℝ (fun θ' => eval (Arch.gated σ id hid) 0 θ' x) θ η t o = ∑ i : hid 0,
      (σ ((x * Cm θ) t (Sum.inl i)) * (x * Cm θ) t (Sum.inr i) * dAm θ η i o
        + σ' ((x * Cm θ) t (Sum.inl i)) * (x * dCm θ η) t (Sum.inl i)
            * (x * Cm θ) t (Sum.inr i) * Am θ i o
        + σ ((x * Cm θ) t (Sum.inl i)) * (x * dCm θ η) t (Sum.inr i) * Am θ i o) := by
  have hdiff := differentiable_eval (A := Arch.gated (T := T) (d := d) σ id hid) (S := 0)
    (dIn := dIn) (dOut := dOut)
    (differentiable_f_gated fun z => (hσ z).differentiableAt) differentiable_id x
  -- the chain rule along the line `τ ↦ θ + τ η`
  have h1 := hasDerivAt_eval_line (A := Arch.gated (T := T) (d := d) σ id hid) 0 θ η x (hdiff θ)
  have h2 := hasDerivAt_pi.1 (hasDerivAt_pi.1 h1 t) o
  -- the same derivative computed entrywise: products and sums of real functions of `τ`
  have h3 : HasDerivAt (fun τ : ℝ => eval (Arch.gated σ id hid) 0 (θ + τ • η) x t o)
      (∑ i : hid 0,
        (σ ((x * Cm θ) t (Sum.inl i)) * (x * Cm θ) t (Sum.inr i) * dAm θ η i o
          + σ' ((x * Cm θ) t (Sum.inl i)) * (x * dCm θ η) t (Sum.inl i)
              * (x * Cm θ) t (Sum.inr i) * Am θ i o
          + σ ((x * Cm θ) t (Sum.inl i)) * (x * dCm θ η) t (Sum.inr i) * Am θ i o)) 0 := by
    rw [funext fun τ => eval_line_apply θ η x t o τ]
    refine HasDerivAt.fun_sum fun i _ => ?_
    have hu := hasDerivAt_quad ((x * Cm θ) t (Sum.inl i)) ((x * dCm θ η) t (Sum.inl i))
      ((x * Cm η) t (Sum.inl i))
    have hw := hasDerivAt_quad ((x * Cm θ) t (Sum.inr i)) ((x * dCm θ η) t (Sum.inr i))
      ((x * Cm η) t (Sum.inr i))
    have hv := hasDerivAt_quad (Am θ i o) (dAm θ η i o) (Am η i o)
    have h := (((hσ _).comp (0 : ℝ) hu).mul hw).mul hv
    convert h using 1
    · rfl
    · simp only [Pi.mul_apply, Function.comp_apply, zero_mul, mul_zero, add_zero]
      ring
  exact h2.unique h3

/-! ### Helpers: the derivative of `C` and `A` along a rescaling -/

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: `∂C` is linear in the direction. -/
private theorem dCm_sub (θ η ρ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) :
    dCm θ (η - ρ) = dCm θ η - dCm θ ρ := by
  show (η.E - ρ.E) * rd θ + θ.E * (rd η - rd ρ)
    = (η.E * rd θ + θ.E * rd η) - (ρ.E * rd θ + θ.E * rd ρ)
  rw [Matrix.sub_mul, Matrix.mul_sub]
  abel

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: `∂A` is linear in the direction. -/
private theorem dAm_sub (θ η ρ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) :
    dAm θ (η - ρ) = dAm θ η - dAm θ ρ := by
  show (wr η - wr ρ) * θ.D + wr θ * (η.D - ρ.D)
    = (wr η * θ.D + wr θ * η.D) - (wr ρ * θ.D + wr θ * ρ.D)
  rw [Matrix.sub_mul, Matrix.mul_sub]
  abel

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: along a rescaling, the gate columns of `C` do not move. -/
private theorem dCm_rescale_inl
    (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) (α : ∀ ℓ, hid ℓ → ℝ)
    (a : dIn) (i : hid 0) :
    dCm θ (rescaleDir θ α) a (Sum.inl i) = 0 := by
  show ((0 : Matrix dIn d ℝ) * rd θ + θ.E * rd (rescaleDir θ α)) a (Sum.inl i) = 0
  rw [Matrix.zero_mul, zero_add, Matrix.mul_apply]
  exact Finset.sum_eq_zero fun k _ => mul_eq_zero_of_right _ rfl

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: along a rescaling, the value column `e_i` of `C` moves by `-α_i e_i`. -/
private theorem dCm_rescale_inr
    (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) (α : ∀ ℓ, hid ℓ → ℝ)
    (a : dIn) (i : hid 0) :
    dCm θ (rescaleDir θ α) a (Sum.inr i) = -(α 0 i) * Cm θ a (Sum.inr i) := by
  show ((0 : Matrix dIn d ℝ) * rd θ + θ.E * rd (rescaleDir θ α)) a (Sum.inr i)
    = -(α 0 i) * (θ.E * rd θ) a (Sum.inr i)
  rw [Matrix.zero_mul, zero_add, Matrix.mul_apply, Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  show θ.E a k * (-(α 0 i) * θ.read 0 k (Sum.inr i))
    = -(α 0 i) * (θ.E a k * θ.read 0 k (Sum.inr i))
  ring

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: along a rescaling, the row `a_i` of `A` moves by `α_i a_i`. -/
private theorem dAm_rescale
    (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) (α : ∀ ℓ, hid ℓ → ℝ)
    (i : hid 0) (o : dOut) :
    dAm θ (rescaleDir θ α) i o = α 0 i * Am θ i o := by
  show (wr (rescaleDir θ α) * θ.D + wr θ * (0 : Matrix d dOut ℝ)) i o = α 0 i * (wr θ * θ.D) i o
  rw [Matrix.mul_zero, add_zero, Matrix.mul_apply, Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  show α 0 i * θ.write 0 i k * θ.D k o = α 0 i * (θ.write 0 i k * θ.D k o)
  ring

/-- Under the conditions, every flat direction of one gated block whose gate activation satisfies
Lemma C.3 is the sum of the direction of two changes of basis and of the direction of a rescaling
of the values of the hidden units (Steps 1 to 3 of the proof of Theorem C.1). -/
theorem flat_le_cobDir_add_rescaleDir_gated (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hU : GatedUnitsRescale σ σ' dIn dOut (hid 0))
    (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) (hθ : OneBlockGenericGated θ)
    (η : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (hη : η ∈ flat (Arch.gated σ id hid) 0 θ) :
    ∃ (X : Fin 2 → Matrix d d ℝ) (α : ∀ ℓ, hid ℓ → ℝ), η = cobDir θ X + rescaleDir θ α := by
  -- Step 3: the derivative of `F(θ, x)` along `η` vanishes at every input, entry by entry
  have hzero : ∀ (x : Matrix T dIn ℝ) (t : T) (o : dOut), ∑ i : hid 0,
      (σ ((x * Cm θ) t (Sum.inl i)) * (x * Cm θ) t (Sum.inr i) * dAm θ η i o
        + σ' ((x * Cm θ) t (Sum.inl i)) * (x * dCm θ η) t (Sum.inl i)
            * (x * Cm θ) t (Sum.inr i) * Am θ i o
        + σ ((x * Cm θ) t (Sum.inl i)) * (x * dCm θ η) t (Sum.inr i) * Am θ i o) = 0 := by
    intro x t o
    rw [← fderiv_eval_apply hσ θ η x t o]
    have h := LinearMap.mem_ker.1 ((Submodule.mem_iInf _).1 hη x)
    exact congrFun (congrFun h t) o
  -- Step 2, Lemma C.3 (inputs `x` with all rows equal to `v`): the gate columns of `∂C` vanish,
  -- and every unit only rescales its value, `∂e_i = -α_i e_i`, `∂a_i = α_i a_i`
  obtain ⟨-, -, hc, -, α, hα⟩ := hU
    (fun i => (Cm θ)ᵀ (Sum.inl i)) 0 (fun i => (Cm θ)ᵀ (Sum.inr i)) 0 (fun i => Am θ i)
    0 0 (fun i => (dCm θ η)ᵀ (Sum.inl i)) 0 (fun i => (dCm θ η)ᵀ (Sum.inr i)) 0
    (fun i => dAm θ η i) (fun i => hθ.row_ne_zero i) (fun i => hθ.gate_ne_zero i)
    (fun i j hij => hθ.gate_not_collinear i j hij) (fun i => hθ.value_ne_zero i) (by
      intro v
      funext o
      have h := hzero (Matrix.of fun _ => v) (Classical.arbitrary T) o
      simp only [Matrix.vecMul_zero, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        Pi.zero_apply, add_zero, zero_add]
      exact h)
  -- the rescaling with these `α_i` (one block: `ℓ = 0`)
  let α' : ∀ ℓ : Fin 1, hid ℓ → ℝ := fun ℓ => Fin.cases α (fun l => l.elim0) ℓ
  -- `η - rescaleDir θ α` keeps `C` and `A` to first order
  have hC : dCm θ (η - rescaleDir θ α') = 0 := by
    ext a j
    rcases j with i | i
    · rw [dCm_sub, Matrix.sub_apply, dCm_rescale_inl, sub_zero]
      exact congrFun (congrFun hc i) a
    · rw [dCm_sub, Matrix.sub_apply, dCm_rescale_inr, Matrix.zero_apply, sub_eq_zero]
      exact congrFun (hα i).1 a
  have hA : dAm θ (η - rescaleDir θ α') = 0 := by
    ext i o
    rw [dAm_sub, Matrix.sub_apply, dAm_rescale, Matrix.zero_apply, sub_eq_zero]
    exact congrFun (hα i).2.2 o
  -- Step 1, Lemma C.2: a direction that keeps `C` and `A` is that of two changes of basis
  obtain ⟨X, hX⟩ := (keeps_products_iff_mem_range_cobDir θ (η - rescaleDir θ α') hθ.rank_E
    hθ.rank_D hθ.rank_read hθ.rank_write).1 ⟨hC, hA⟩
  exact ⟨X, α', sub_eq_iff_eq_add.1 hX⟩

/-- Helper (the private `rescaleDirLin` of `Dimension/Rescaling.lean`): `α ↦ rescaleDir θ α` is
linear. -/
private noncomputable def rescaleDirLin
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

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the pairs `(X, α)` of two `d × d` matrices and one number per hidden unit form a
space of dimension `2 d² + d_hidden`. -/
private theorem finrank_dirDomain :
    Module.finrank ℝ ((Fin (1 + 1) → Matrix d d ℝ) × (∀ ℓ : Fin 1, hid ℓ → ℝ))
      = 2 * Fintype.card d ^ 2 + Fintype.card (hid 0) := by
  rw [Module.finrank_prod, finrank_cobDomain (L := 1) (d := d), Module.finrank_pi_fintype]
  simp only [Module.finrank_fintype_fun_eq_card, Finset.univ_unique, Fin.default_eq_zero,
    Finset.sum_singleton, Nat.reduceAdd]

/-- **Theorem 5.1 for a SwiGLU or GeGLU block, under the conditions of its proof:** the
functional dimension is `P - 2 d² - d_hidden`. -/
theorem funDim_gated_oneBlock (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hU : GatedUnitsRescale σ σ' dIn dOut (hid 0))
    (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) (hθ : OneBlockGenericGated θ) :
    funDim (Arch.gated σ id hid) 0 θ + (2 * Fintype.card d ^ 2 + Fintype.card (hid 0))
      = Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) := by
  have hσd : Differentiable ℝ σ := fun z => (hσ z).differentiableAt
  have hdiff : ∀ x : Matrix T dIn ℝ, DifferentiableAt ℝ
      (fun θ' : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut =>
        eval (Arch.gated σ id hid) 0 θ' x) θ := fun x =>
    (differentiable_eval (A := Arch.gated (T := T) (d := d) σ id hid) (S := 0)
      (differentiable_f_gated hσd) differentiable_id x).differentiableAt
  -- the directions of the changes of basis and of the rescalings, `(X, α) ↦ cobDir + rescaleDir`
  let Φ := (cobDirLin θ).coprod (rescaleDirLin θ)
  -- the flat directions are exactly these directions: `⊆` is the previous theorem, `⊇` holds
  -- since changes of basis and rescalings are symmetries
  have hflat : flat (Arch.gated σ id hid) 0 θ = LinearMap.range Φ := by
    apply le_antisymm
    · intro η hη
      obtain ⟨X, α, rfl⟩ := flat_le_cobDir_add_rescaleDir_gated hσ hU θ hθ η hη
      exact LinearMap.mem_range.2 ⟨(X, α), rfl⟩
    · rintro _ ⟨p, rfl⟩
      rw [LinearMap.coprod_apply]
      exact add_mem (cobDir_mem_flat_skipless θ rfl (differentiable_f_gated hσd) p.1)
        (rescaleDir_mem_flat θ hσd p.2)
  -- no value column of `W_read` vanishes, since the value columns of `C = E W_read` do not
  have hv : ∀ ℓ i, (fun k => θ.read ℓ k (Sum.inr i)) ≠ 0 := by
    intro ℓ i h0
    obtain rfl := Subsingleton.elim ℓ 0
    apply hθ.value_ne_zero i
    funext a
    show ∑ k, θ.E a k * θ.read 0 k (Sum.inr i) = 0
    exact Finset.sum_eq_zero fun k _ => by
      rw [show θ.read 0 k (Sum.inr i) = 0 from congrFun h0 k, mul_zero]
  -- `(X, α) ↦ cobDir θ X + rescaleDir θ α` is injective (Lemma B.1 for gated blocks)
  have hinj0 := cobDir_add_rescaleDir_injective θ hθ.rank_E
    (fun ℓ => by obtain rfl := Subsingleton.elim ℓ 0; exact hθ.rank_write) hv
  have hinj : Function.Injective Φ := fun p q hpq => by
    rw [LinearMap.coprod_apply, LinearMap.coprod_apply] at hpq
    exact hinj0 hpq
  -- `fd(θ) = P - dim K(θ)` (Appendix C)
  have h := funDim_add_finrank_flat θ hdiff
  rwa [hflat, LinearMap.finrank_range_of_inj hinj, finrank_dirDomain] at h

/-- The conditions hold at generic parameters, when `d_in, d_out, d_hidden ≥ d ≥ 2`. -/
theorem ae_oneBlockGenericGated
    (μ : Measure (Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ θ ∂μ, OneBlockGenericGated θ := by
  classical
  -- two distinct coordinates of `h`, two distinct input coordinates, one output coordinate
  obtain ⟨k₁, k₂, hk⟩ := Fintype.exists_pair_of_one_lt_card (show 1 < Fintype.card d by omega)
  obtain ⟨a₁, a₂, ha⟩ := Fintype.exists_pair_of_one_lt_card (show 1 < Fintype.card dIn by omega)
  obtain ⟨o₀⟩ : Nonempty dOut := Fintype.card_pos_iff.1 (by omega)
  obtain ⟨cD⟩ := Function.Embedding.nonempty_of_card_le hdOut
  obtain ⟨cR⟩ := Function.Embedding.nonempty_of_card_le hhid
  -- the parameters with all entries `1`
  let θ₁ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut :=
    ⟨Matrix.of fun _ _ => 1, fun _ => Matrix.of fun _ _ => 1, fun _ => Matrix.of fun _ _ => 1,
      Matrix.of fun _ _ => 1⟩
  -- the ranks: `E` and the write (`Generic/Params.lean`), `D` and the read (invertible minors;
  -- for the read, `d` of its gate columns)
  have h1 := ae_rank_E_write μ hdIn (fun ℓ => by obtain rfl := Subsingleton.elim ℓ 0; exact hhid)
  have h2 := ae_isUnit_det_submatrix μ
  -- the rows of `A = W_write D` are nonzero: their entries at `o₀` are
  have h3 : ∀ᵐ θ ∂μ, ∀ i : hid 0, (θ.write 0 * θ.D) i o₀ ≠ 0 := by
    refine ae_all_iff.2 fun i => ?_
    exact ae_ne_zero_of_analytic μ
      (analyticOnNhd_write_mul_D (A := Arch.gated (T := T) (d := d) σ id hid) (dIn := dIn) 0 i o₀)
      ⟨θ₁, sum_one_mul_one_ne_zero hd⟩
  -- the gate and value columns of `C = E W_read` are nonzero: their entries at `a₁` are
  have h4 : ∀ᵐ θ ∂μ, ∀ j : hid 0 ⊕ hid 0, (θ.E * θ.read 0) a₁ j ≠ 0 := by
    refine ae_all_iff.2 fun j => ?_
    exact ae_ne_zero_of_analytic μ
      (analyticOnNhd_E_mul_read (A := Arch.gated (T := T) (d := d) σ id hid) (dOut := dOut) 0 a₁ j)
      ⟨θ₁, sum_one_mul_one_ne_zero hd⟩
  -- two gate columns of `C` are not collinear: a `2 × 2` minor does not vanish
  have h5 : ∀ᵐ θ ∂μ, ∀ i j : hid 0, i ≠ j →
      (θ.E * θ.read 0) a₁ (Sum.inl i) * (θ.E * θ.read 0) a₂ (Sum.inl j)
        - (θ.E * θ.read 0) a₁ (Sum.inl j) * (θ.E * θ.read 0) a₂ (Sum.inl i) ≠ 0 := by
    refine ae_all_iff.2 fun i => ae_all_iff.2 fun j => ?_
    by_cases hij : i = j
    · exact Filter.Eventually.of_forall fun _ h _ => absurd hij h
    · obtain ⟨E₀, W₀, hEW⟩ := exists_minor_ne_zero (q := hid 0 ⊕ hid 0) ha hk
        (Sum.inl_injective.ne hij)
      let θ₀ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut :=
        ⟨E₀, fun ℓ => Fin.cases W₀ (fun l => l.elim0) ℓ, 0, 0⟩
      have hC : ∀ (a : dIn) (j : hid 0 ⊕ hid 0), AnalyticOnNhd ℝ
          (fun θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut =>
            (θ.E * θ.read 0) a j) Set.univ := fun a j =>
        analyticOnNhd_E_mul_read (A := Arch.gated (T := T) (d := d) σ id hid) (dOut := dOut) 0 a j
      have hg : AnalyticOnNhd ℝ
          (fun θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut =>
            (θ.E * θ.read 0) a₁ (Sum.inl i) * (θ.E * θ.read 0) a₂ (Sum.inl j)
              - (θ.E * θ.read 0) a₁ (Sum.inl j) * (θ.E * θ.read 0) a₂ (Sum.inl i)) Set.univ :=
        ((hC a₁ (Sum.inl i)).mul (hC a₂ (Sum.inl j))).sub
          ((hC a₁ (Sum.inl j)).mul (hC a₂ (Sum.inl i)))
      exact (ae_ne_zero_of_analytic μ hg ⟨θ₀, hEW⟩).mono fun _ h _ => h
  filter_upwards [h1, h2, h3, h4, h5] with θ h1 h2 h3 h4 h5
  refine ⟨h1.1, rank_eq_card_of_isUnit_det θ.D cD (h2.2.1 cD),
    rank_eq_card_of_isUnit_det (θ.read 0) (cR.trans Function.Embedding.inl)
      (h2.1 0 (cR.trans Function.Embedding.inl)), h1.2 0,
    fun i hi => h3 i (congrFun hi o₀), fun i hi => h4 (Sum.inl i) (congrFun hi a₁), ?_,
    fun i hi => h4 (Sum.inr i) (congrFun hi a₁)⟩
  -- if `c_i = r c_j`, the minor of the gate columns `i`, `j` vanishes
  intro i j hij r hr
  have e1 : (θ.E * θ.read 0) a₁ (Sum.inl i) = r * (θ.E * θ.read 0) a₁ (Sum.inl j) :=
    congrFun hr a₁
  have e2 : (θ.E * θ.read 0) a₂ (Sum.inl i) = r * (θ.E * θ.read 0) a₂ (Sum.inl j) :=
    congrFun hr a₂
  apply h5 i j hij
  rw [e1, e2]
  ring

/-- **Theorem 5.1 for a SwiGLU or GeGLU block:** with one block, without normalization and without
biases, with `d_in, d_out, d_hidden ≥ d ≥ 2`, the functional dimension is `P - 2 d² - d_hidden` at
generic parameters. -/
theorem ae_funDim_gated_oneBlock (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hU : GatedUnitsRescale σ σ' dIn dOut (hid 0))
    (μ : Measure (Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ θ ∂μ, funDim (Arch.gated σ id hid) 0 θ
        + (2 * Fintype.card d ^ 2 + Fintype.card (hid 0))
      = Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) :=
  (ae_oneBlockGenericGated μ hd hdIn hdOut hhid).mono fun θ hθ => funDim_gated_oneBlock hσ hU θ hθ

end Skips
