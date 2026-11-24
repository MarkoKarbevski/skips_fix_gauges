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
  sorry

/-- Lemma C.3 for ReLU², in the form `UnitsRescale` with `k = 2`. -/
theorem reluSq_unitsRescale (n m q : Type*) [Fintype n] [Fintype m] [Fintype q] :
    UnitsRescale reluSq reluSqDeriv 2 n m q := by
  sorry

variable {T d dIn dOut : Type*} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {hid : Fin 1 → Type} [∀ ℓ, Fintype (hid ℓ)]
variable {σ σ' : ℝ → ℝ}

/-- The inputs at which no hidden unit of the block sits at its kink: every entry of
`x E W_read` (one per token and hidden unit) is nonzero. -/
def noKink (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) :
    Set (Matrix T dIn ℝ) :=
  {x | ∀ (t : T) (i : hid 0), (x * θ.E * θ.read 0) t i ≠ 0}

/-- At an input with no hidden unit at its kink, the output of a network of one block is
differentiable in the parameters, when `σ` is differentiable away from `0`. -/
theorem differentiableAt_eval_of_mem_noKink (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) (x : Matrix T dIn ℝ)
    (hx : x ∈ noKink θ) :
    DifferentiableAt ℝ
      (fun θ' : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut =>
        eval (Arch.mlp σ id hid) 0 θ' x) θ := by
  sorry

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
  sorry

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
