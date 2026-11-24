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
  sorry

/-- At an input with no gate at its kink, the output of a network of one ReGLU block is
differentiable in the parameters, for all stream matrices `S` (with or without the skip). -/
theorem differentiableAt_eval_of_mem_noKinkGate (S : Fin 1 → Matrix d d ℝ)
    (θ : Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut) (x : Matrix T dIn ℝ)
    (hx : x ∈ noKinkGate θ) :
    DifferentiableAt ℝ
      (fun θ' : Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut =>
        eval (Arch.gated relu id hid) S θ' x) θ := by
  sorry

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
  sorry

/-- **Theorem 5.1 / C.1 for a ReGLU block, under the conditions of the proof:**
`fd = P - 2 d² - 2 d_hidden`. -/
theorem funDim_reglu_oneBlock
    (θ : Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut)
    (hθ : OneBlockGenericReGLU θ) :
    funDim (Arch.gated relu id hid) 0 θ
        + (2 * Fintype.card d ^ 2 + 2 * Fintype.card (hid 0))
      = Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut) := by
  sorry

/-- The same rank on a batch of inputs with no gate at its kink, as the paper takes the Jacobian
for ReGLU blocks. -/
theorem exists_jacobianRank_reglu_oneBlock
    (θ : Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut)
    (hθ : OneBlockGenericReGLU θ) :
    ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i, X i ∈ noKinkGate θ) ∧
      jacobianRank (Arch.gated relu id hid) 0 X θ
          + (2 * Fintype.card d ^ 2 + 2 * Fintype.card (hid 0))
        = Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut) := by
  sorry

/-- **Theorem 5.1 / C.1 for a ReGLU block:** for `d_in, d_out, d_hidden ≥ d ≥ 2`, at generic
parameters, `fd = P - 2 d² - 2 d_hidden`. -/
theorem ae_funDim_reglu_oneBlock
    (μ : Measure (Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ θ ∂μ, funDim (Arch.gated relu id hid) 0 θ
        + (2 * Fintype.card d ^ 2 + 2 * Fintype.card (hid 0))
      = Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut) := by
  sorry

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
  sorry

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
  sorry

/-- **Theorem 4.6 (i) / B.1 (i) for a ReGLU block with a skip, under the conditions of the
proof:** `fd = P - d² - 2 d_hidden`. -/
theorem funDim_reglu_oneBlock_residual
    (θ : Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut)
    (hθ : OneBlockGenericReGLU θ) :
    funDim (Arch.gated relu id hid) 1 θ + (Fintype.card d ^ 2 + 2 * Fintype.card (hid 0))
      = Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut) := by
  sorry

/-- The same rank on a batch of inputs with no gate at its kink. -/
theorem exists_jacobianRank_reglu_oneBlock_residual
    (θ : Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut)
    (hθ : OneBlockGenericReGLU θ) :
    ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i, X i ∈ noKinkGate θ) ∧
      jacobianRank (Arch.gated relu id hid) 1 X θ
          + (Fintype.card d ^ 2 + 2 * Fintype.card (hid 0))
        = Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut) := by
  sorry

/-- **Theorem 4.6 (i) for a ReGLU block, with a skip:** for `d_in, d_out, d_hidden ≥ d ≥ 2`, at
generic parameters, `fd = P - d² - 2 d_hidden`. -/
theorem ae_funDim_reglu_oneBlock_residual
    (μ : Measure (Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ θ ∂μ, funDim (Arch.gated relu id hid) 1 θ
        + (Fintype.card d ^ 2 + 2 * Fintype.card (hid 0))
      = Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut) := by
  sorry

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
  sorry

/-- **Theorem 4.6 (i) for a ReGLU block:** at generic parameters the skip raises the functional
dimension by exactly `d²`. -/
theorem ae_funDim_reglu_oneBlock_residual_eq_add
    (μ : Measure (Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ θ ∂μ, funDim (Arch.gated relu id hid) 1 θ
      = funDim (Arch.gated relu id hid) 0 θ + Fintype.card d ^ 2 := by
  sorry

end Skips
