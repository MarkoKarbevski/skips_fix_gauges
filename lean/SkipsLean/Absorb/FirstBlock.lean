import SkipsLean.Absorb.Networks
import SkipsLean.Absorb.SameWidth
import SkipsLean.Dimension.RescalingMlp

/-!
# The first block of a skipless network needs `2 d` hidden units

Paper ("Can an MLP Absorb Its Skip Connection Exactly?"): Theorem 4.5. "Consider networks of ReLU
blocks, or of GELU blocks, without normalization. For almost every choice of weights, a residual
network with model dimension `d` equals no skipless network whose first block has fewer than
`2 d` hidden units, whatever its depth and its other widths."

The proof (Appendix A) has three parts, stated here in this order:

* the conditions on the weights of the residual network that the proof uses (`FirstBlockGeneric`),
  and that they hold for almost every choice of weights;
* the case of ReLU under these conditions: near a generic input the residual network is linear of
  rank `d`, while a skipless network whose first block has fewer than `2 d` hidden units is
  constant, near that input or near its negative, along a subspace of dimension greater than
  `d_in - d`;
* GELU: along rays, `F(t X) / t` of a GELU network tends to the output at `X` of the ReLU network
  with the same weights, with or without skips, so an equality of two GELU networks gives the
  equality of the two ReLU networks.

A skipless network that is compared with the residual one has its own model dimension `d'`, depth
`L' + 1` and widths `hid'`; only its first width `hid' 0` is constrained. Two networks are equal
if they have the same output at every input `X` (a matrix with one row per token).
-/

namespace Skips

open Matrix MeasureTheory Filter
open scoped Matrix.Norms.Elementwise Topology

variable {T dIn dOut : Type*} {d : Type} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d]
  [Fintype dIn] [Fintype dOut]
variable {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)] [∀ ℓ, DecidableEq (hid ℓ)] {σ : ℝ → ℝ}

/-- The same weights, read as the parameters of the network with another activation. -/
def Params.withActivation (σ' : ℝ → ℝ) {χ : Matrix T d ℝ → Matrix T d ℝ}
    (θ : Params (Arch.mlp (T := T) (d := d) σ χ hid) dIn dOut) :
    Params (Arch.mlp (T := T) (d := d) σ' χ hid) dIn dOut where
  E := θ.E
  read := θ.read
  write := θ.write
  D := θ.D

/-- **The conditions of the proof of Theorem 4.5** on the weights of the residual network: `E` and
`D` have rank `d`, no read of a hidden unit vanishes, and `I + W_read[:,S] W_write[S,:]` is
invertible for every block and every set `S` of its hidden units. They do not involve the
activation. -/
structure FirstBlockGeneric (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) :
    Prop where
  rank_E : θ.E.rank = Fintype.card d
  rank_D : θ.D.rank = Fintype.card d
  /-- no read column of a hidden unit vanishes -/
  read_ne_zero : ∀ ℓ (i : hid ℓ), (θ.read ℓ)ᵀ i ≠ 0
  /-- `I + W_read[:,S] W_write[S,:]` is invertible for every block and every set `S` -/
  isUnit_det : ∀ ℓ (S : Finset (hid ℓ)),
    IsUnit ((1 : Matrix d d ℝ) + subProd S (θ.read ℓ) (θ.write ℓ)).det

/-- The conditions of the proof hold for almost every choice of weights (`d_in, d_out ≥ d ≥ 1`):
each is the nonvanishing of polynomials in the weights that do not vanish identically. -/
theorem ae_firstBlockGeneric [Nonempty d]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)) [μ.IsAddHaarMeasure]
    (hdIn : Fintype.card d ≤ Fintype.card dIn) (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, FirstBlockGeneric θ := by
  sorry

/-- **Theorem 4.5 for ReLU, under the conditions of the proof.** A residual ReLU network that
satisfies `FirstBlockGeneric` equals no skipless ReLU network whose first block has fewer than
`2 d` hidden units, whatever its model dimension, its depth and its other widths. -/
theorem exists_ne_skipless_of_first_card_lt_relu [Nonempty T]
    (θ : Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut) (hθ : FirstBlockGeneric θ)
    {L' : ℕ} {d' : Type*} [Fintype d'] (hid' : Fin (L' + 1) → Type) [∀ ℓ, Fintype (hid' ℓ)]
    (hcard : Fintype.card (hid' 0) < 2 * Fintype.card d)
    (θ' : Params (Arch.mlp (T := T) (d := d') relu id hid') dIn dOut) :
    ∃ X : Matrix T dIn ℝ,
      eval (Arch.mlp relu id hid) 1 θ X ≠ eval (Arch.mlp relu id hid') 0 θ' X := by
  sorry

/-- **Theorem 4.5 for ReLU.** For almost every choice of weights (`d_in, d_out ≥ d`), a residual
ReLU network equals no skipless ReLU network whose first block has fewer than `2 d` hidden units,
whatever its model dimension, its depth and its other widths. -/
theorem ae_ne_skipless_of_first_card_lt_relu [Nonempty T]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut))
    [μ.IsAddHaarMeasure]
    (hdIn : Fintype.card d ≤ Fintype.card dIn) (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, ∀ (L' : ℕ) (d' : Type) [Fintype d'] (hid' : Fin (L' + 1) → Type)
      [∀ ℓ, Fintype (hid' ℓ)], Fintype.card (hid' 0) < 2 * Fintype.card d →
      ∀ θ' : Params (Arch.mlp (T := T) (d := d') relu id hid') dIn dOut,
        ∃ X : Matrix T dIn ℝ,
          eval (Arch.mlp relu id hid) 1 θ X ≠ eval (Arch.mlp relu id hid') 0 θ' X := by
  sorry

omit [DecidableEq d] [∀ ℓ, DecidableEq (hid ℓ)] in
/-- **GELU networks along rays** (proof of Theorem 4.5, "GELU"). Without normalization, for all
stream matrices `S` (with or without skips), the output of a GELU network at the input `t X`,
divided by `t`, tends as `t → ∞` to the output at `X` of the ReLU network with the same
weights. -/
theorem tendsto_eval_gelu_ray (S : Fin L → Matrix d d ℝ)
    (θ : Params (Arch.mlp (T := T) (d := d) gelu id hid) dIn dOut) (X : Matrix T dIn ℝ) :
    Tendsto (fun t : ℝ => t⁻¹ • eval (Arch.mlp gelu id hid) S θ (t • X)) atTop
      (𝓝 (eval (Arch.mlp relu id hid) S (θ.withActivation relu) X)) := by
  sorry

/-- **Theorem 4.5 for GELU, under the conditions of the proof.** A residual GELU network that
satisfies `FirstBlockGeneric` equals no skipless GELU network whose first block has fewer than
`2 d` hidden units, whatever its model dimension, its depth and its other widths. -/
theorem exists_ne_skipless_of_first_card_lt_gelu [Nonempty T]
    (θ : Params (Arch.mlp (T := T) (d := d) gelu id hid) dIn dOut) (hθ : FirstBlockGeneric θ)
    {L' : ℕ} {d' : Type*} [Fintype d'] (hid' : Fin (L' + 1) → Type) [∀ ℓ, Fintype (hid' ℓ)]
    (hcard : Fintype.card (hid' 0) < 2 * Fintype.card d)
    (θ' : Params (Arch.mlp (T := T) (d := d') gelu id hid') dIn dOut) :
    ∃ X : Matrix T dIn ℝ,
      eval (Arch.mlp gelu id hid) 1 θ X ≠ eval (Arch.mlp gelu id hid') 0 θ' X := by
  sorry

/-- **Theorem 4.5 for GELU.** For almost every choice of weights (`d_in, d_out ≥ d`), a residual
GELU network equals no skipless GELU network whose first block has fewer than `2 d` hidden units,
whatever its model dimension, its depth and its other widths. -/
theorem ae_ne_skipless_of_first_card_lt_gelu [Nonempty T]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) gelu id hid) dIn dOut))
    [μ.IsAddHaarMeasure]
    (hdIn : Fintype.card d ≤ Fintype.card dIn) (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, ∀ (L' : ℕ) (d' : Type) [Fintype d'] (hid' : Fin (L' + 1) → Type)
      [∀ ℓ, Fintype (hid' ℓ)], Fintype.card (hid' 0) < 2 * Fintype.card d →
      ∀ θ' : Params (Arch.mlp (T := T) (d := d') gelu id hid') dIn dOut,
        ∃ X : Matrix T dIn ℝ,
          eval (Arch.mlp gelu id hid) 1 θ X ≠ eval (Arch.mlp gelu id hid') 0 θ' X := by
  sorry

end Skips
