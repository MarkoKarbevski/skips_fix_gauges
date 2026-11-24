import SkipsLean.Absorb.NoWidth
import SkipsLean.Residual.LearnedSkips
import SkipsLean.Generic.Params
import SkipsLean.Dimension.UpperBoundRMSNorm

/-!
# Residual and skipless networks: when they are equal and when they are not

Paper ("Can an MLP Absorb Its Skip Connection Exactly?"): Proposition 4.4, Theorem 4.1 (with
Corollary A.3) and Proposition 5.4.

Networks are those of the library: `eval A S θ X` with the stream matrices `S = 1` (residual),
`S = 0` (skipless) or learned skips. Two networks are equal if they have the same output at every
input `X`. A skipless network that is compared with a residual one may have another model
dimension `d'`, another depth and other widths; it has the same `d_in`, `d_out` and tokens.

* Proposition 4.4: for `σ(z) - σ(-z) = z` (ReLU, GELU), without normalization, a residual network
  whose reads all have rank `d` equals a skipless network with `d` more hidden units in every block
  and the same embedding and readout.
* Theorem 4.1: a residual network with `E D ≠ 0` equals no skipless network of one or more blocks,
  (i) when every block of both networks vanishes at `0` with derivative `0` there (gated blocks whose
  gate vanishes at `0` and is differentiable there; blocks that are positively homogeneous of degree
  `k > 1`), without normalization or under pre-RMSNorm with `ε > 0`; (ii) for `tanh` blocks without
  normalization.
* Proposition 5.4: for `σ(z) - σ(-z) = c z`, `c ≠ 0`, without normalization, a skipless network of
  vanilla `σ` blocks equals (i) a network with learned skips, invertible at generic weights, and the
  same embedding, readout, `d` and widths, and (ii) at generic weights a residual network with the
  same readout, `d` and widths.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T dIn dOut : Type*} {d : Type} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d]
  [Fintype dIn] [Fintype dOut]
variable {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)] {σ : ℝ → ℝ} {c : ℝ}

/-! ### Proposition 4.4 -/

/-- **Proposition 4.4 (`d` more units per block suffice).** Let `σ(z) - σ(-z) = z`, as for ReLU
and GELU. Without normalization, a residual network whose reads all have rank `d` equals a skipless
network with `d` more hidden units in every block, with the same embedding and readout. -/
theorem exists_skipless_eq_residual_of_rank_read (hσ : ∀ z, σ z - σ (-z) = z)
    (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)
    (hr : ∀ ℓ, (θ.read ℓ).rank = Fintype.card d) :
    ∃ θ' : Params (Arch.mlp (T := T) (d := d) σ id (fun ℓ => hid ℓ ⊕ d)) dIn dOut,
      θ'.E = θ.E ∧ θ'.D = θ.D ∧
      ∀ X : Matrix T dIn ℝ,
        eval (Arch.mlp σ id hid) 1 θ X = eval (Arch.mlp σ id (fun ℓ => hid ℓ ⊕ d)) 0 θ' X := by
  sorry

/-! ### Theorem 4.1 -/

/-- Every block map of the architecture vanishes at `0` and has the derivative `0` there. This is
what the proof of Corollary A.3 uses of the blocks: "each such block maps `0` to `0` and has
Jacobian `0` there". -/
def Arch.FlatAtZero {d : Type*} (A : Arch T d L) : Prop :=
  ∀ ℓ, A.f ℓ 0 = 0 ∧
    HasFDerivAt (A.f ℓ) (0 : Matrix T (A.r ℓ) ℝ →L[ℝ] Matrix T (A.w ℓ) ℝ) 0

/-- Gated blocks whose gate vanishes at `0` and is differentiable there (SwiGLU, GeGLU) vanish at
`0` with derivative `0`: a hidden unit is the product of two terms that vanish at `0`. -/
theorem flatAtZero_gated {d : Type*} {χ : Matrix T d ℝ → Matrix T d ℝ} (h0 : σ 0 = 0)
    (hd : DifferentiableAt ℝ σ 0) : (Arch.gated (T := T) (d := d) σ χ hid).FlatAtZero := by
  sorry

/-- A map that is positively homogeneous of degree `k > 1` and bounded on the unit sphere vanishes
at `0` and has the derivative `0` there. -/
theorem hasFDerivAt_zero_of_homogeneous {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℝ} (hk : 1 < k) (f : E → F)
    (hf : ∀ (lam : ℝ) (x : E), 0 < lam → f (lam • x) = lam ^ k • f x)
    (hb : ∃ C : ℝ, ∀ x : E, ‖x‖ = 1 → ‖f x‖ ≤ C) :
    f 0 = 0 ∧ HasFDerivAt f (0 : E →L[ℝ] F) 0 := by
  sorry

/-- ReLU² blocks (positively homogeneous of degree `2`) vanish at `0` with derivative `0`. -/
theorem flatAtZero_mlp_reluSq {d : Type*} {χ : Matrix T d ℝ → Matrix T d ℝ} :
    (Arch.mlp (T := T) (d := d) reluSq χ hid).FlatAtZero := by
  sorry

/-- ReGLU blocks (positively homogeneous of degree `2`) vanish at `0` with derivative `0`. -/
theorem flatAtZero_gated_relu {d : Type*} {χ : Matrix T d ℝ → Matrix T d ℝ} :
    (Arch.gated (T := T) (d := d) relu χ hid).FlatAtZero := by
  sorry

/-- **Theorem 4.1 (i) / Corollary A.3, without normalization.** Let every block of a residual
network and of a skipless network of one or more blocks vanish at `0` with derivative `0` there. If
the residual network has `E D ≠ 0`, the two networks differ at some input: at `X = 0` the residual
network has the derivative `X ↦ X E D` and the skipless one the derivative `0`. -/
theorem exists_ne_residual_skipless_of_flatAtZero [Nonempty T] {L' : ℕ} {d' : Type*} [Fintype d']
    (A : Arch T d L) (A' : Arch T d' (L' + 1)) (hχ : A.χ = id) (hχ' : A'.χ = id)
    (hA : A.FlatAtZero) (hA' : A'.FlatAtZero) (θ : Params A dIn dOut) (hED : θ.E * θ.D ≠ 0)
    (θ' : Params A' dIn dOut) :
    ∃ X : Matrix T dIn ℝ, eval A 1 θ X ≠ eval A' 0 θ' X := by
  sorry

/-- **Theorem 4.1 (i) / Corollary A.3, under pre-RMSNorm with `ε > 0`:** the same, since
`N(0) = 0` and `N` has the derivative `I / √ε` at `0`. -/
theorem exists_ne_residual_skipless_of_flatAtZero_rmsNorm [Nonempty T] {L' : ℕ} {d' : Type*}
    [Fintype d'] {ε ε' : ℝ} (hε : 0 < ε) (hε' : 0 < ε')
    (A : Arch T d L) (A' : Arch T d' (L' + 1)) (hχ : A.χ = rmsNorm ε) (hχ' : A'.χ = rmsNorm ε')
    (hA : A.FlatAtZero) (hA' : A'.FlatAtZero) (θ : Params A dIn dOut) (hED : θ.E * θ.D ≠ 0)
    (θ' : Params A' dIn dOut) :
    ∃ X : Matrix T dIn ℝ, eval A 1 θ X ≠ eval A' 0 θ' X := by
  sorry

/-- **Theorem 4.1 (ii):** without normalization, a residual network of `tanh` blocks with
`E D ≠ 0` equals no skipless network of one or more `tanh` blocks, of any depth, widths and model
dimension: the residual network differs from `X E D` by a bounded map, and the skipless one is
bounded. -/
theorem exists_ne_residual_skipless_tanh [Nonempty T] {L' : ℕ} {d' : Type*} [Fintype d']
    {hid' : Fin (L' + 1) → Type} [∀ ℓ, Fintype (hid' ℓ)]
    (θ : Params (Arch.mlp (T := T) (d := d) Real.tanh id hid) dIn dOut) (hED : θ.E * θ.D ≠ 0)
    (θ' : Params (Arch.mlp (T := T) (d := d') Real.tanh id hid') dIn dOut) :
    ∃ X : Matrix T dIn ℝ,
      eval (Arch.mlp Real.tanh id hid) 1 θ X ≠ eval (Arch.mlp Real.tanh id hid') 0 θ' X := by
  sorry

/-! ### Proposition 5.4 -/

variable [∀ ℓ, DecidableEq (hid ℓ)]

/-- The parameters with the reads of the units of `S ℓ` flipped in every block `ℓ` (the blocks
`B'_ℓ` of the proof of Proposition 5.4). -/
def Params.flipReads (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)
    (S : ∀ ℓ, Finset (hid ℓ)) : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut where
  E := θ.E
  read ℓ := flipCols (S ℓ) (θ.read ℓ)
  write := θ.write
  D := θ.D

/-- **Proposition 5.4 (i), the identity of its proof.** Let `σ(z) - σ(-z) = c z`. For any sets
`S_ℓ` of units, the skipless network equals the network with the learned skips
`A_ℓ = c K_ℓ`, `K_ℓ = W_read^ℓ[:,S_ℓ] W_write^ℓ[S_ℓ,:]`, the reads of the units of `S_ℓ` flipped,
and the same embedding, writes and readout. -/
theorem eval_skipless_eq_learned_flipReads (hσ : ∀ z, σ z - σ (-z) = c * z)
    (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) (S : ∀ ℓ, Finset (hid ℓ))
    (X : Matrix T dIn ℝ) :
    eval (Arch.mlp σ id hid) 0 θ X
      = eval (Arch.mlp σ id hid) (fun ℓ => c • subProd (S ℓ) (θ.read ℓ) (θ.write ℓ))
          (θ.flipReads S) X := by
  sorry

/-- **Proposition 5.4 (i):** let `σ(z) - σ(-z) = c z` with `c ≠ 0`, and let every block have at
least `d` hidden units. Without normalization, for almost every choice of weights a skipless
network of vanilla `σ` blocks equals a network with invertible learned skips and the same
embedding, readout, `d` and widths. -/
theorem ae_exists_learned_skips_eq_skipless (hσ : ∀ z, σ z - σ (-z) = c * z) (hc : c ≠ 0)
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)) [μ.IsAddHaarMeasure]
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, ∃ (A : Fin L → Matrix d d ℝ)
      (θ' : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut),
      (∀ ℓ, IsUnit (A ℓ).det) ∧ θ'.E = θ.E ∧ θ'.D = θ.D ∧
      ∀ X : Matrix T dIn ℝ,
        eval (Arch.mlp σ id hid) 0 θ X = eval (Arch.mlp σ id hid) A θ' X := by
  sorry

/-- **Proposition 5.4 (ii):** under the same hypotheses, for almost every choice of weights the
skipless network equals a residual network with the same readout, `d` and widths, whose embedding
`E'` has `E' D ≠ 0` (by Theorem 3.2 (i) of the skips paper, `eval_learned_eq_residual`; the
embedding is `c^L E K_1 ⋯ K_L`). -/
theorem ae_exists_residual_eq_skipless [Nonempty d] [Nonempty dIn] [Nonempty dOut]
    (hσ : ∀ z, σ z - σ (-z) = c * z) (hc : c ≠ 0)
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)) [μ.IsAddHaarMeasure]
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, ∃ θ' : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut,
      θ'.D = θ.D ∧ θ'.E * θ'.D ≠ 0 ∧
      ∀ X : Matrix T dIn ℝ,
        eval (Arch.mlp σ id hid) 0 θ X = eval (Arch.mlp σ id hid) 1 θ' X := by
  sorry

end Skips
