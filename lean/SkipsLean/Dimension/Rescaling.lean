import SkipsLean.Network.Blocks
import SkipsLean.Dimension.UpperBound

/-!
# Gated blocks: the rescalings inside the blocks, and the upper bound with them

Paper (dimension paper): Appendix B, "The symmetries inside the blocks", and Theorem 4.3 for gated
blocks without normalization.

In a gated block the value column `e_i` of hidden unit `i` and its write row `a_i` can be rescaled,
`(e_i, a_i) ↦ (e_i / λ, λ a_i)` with `λ ≠ 0`, without changing the map of the block. With
`λ = e^{τ α}` this moves the parameters, to first order in `τ`, in the direction `rescaleDir θ α`:
the value columns of the read of block `ℓ` change by `-α_{ℓ,i} e_i`, the write rows by
`α_{ℓ,i} a_i`, and nothing else changes.

These directions are flat. Together with the directions `cobDir θ X` of the changes of basis they
span a space of dimension `(L + 1) d² + s`, where `s` is the number of hidden units of the network,
when `E` and the writes have rank `d` and no value column of a read vanishes (Lemma B.1). So the
functional dimension is at most `P - (L + 1) d² - s`.
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {σ : ℝ → ℝ} {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]

/-- The direction of the rescalings of the values of the hidden units of a gated network: the
rescaling `λ = e^{τ α ℓ i}` of hidden unit `i` of block `ℓ`, to first order in `τ`. -/
def rescaleDir (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (α : ∀ ℓ, hid ℓ → ℝ) : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut where
  E := 0
  read ℓ := Matrix.of fun k j => Sum.elim (fun _ => 0) (fun i => -(α ℓ i) * θ.read ℓ k (Sum.inr i)) j
  write ℓ := Matrix.of fun i k => α ℓ i * θ.write ℓ i k
  D := 0

variable (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)

/-- The rescalings of the values preserve the function: with every value column of the read of
block `ℓ` divided by `c ℓ i ≠ 0` and the write row of the same hidden unit multiplied by `c ℓ i`,
the network computes the same function. -/
theorem eval_rescale (c : ∀ ℓ, hid ℓ → ℝ) (hc : ∀ ℓ i, c ℓ i ≠ 0)
    (θ' : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (hE : θ'.E = θ.E) (hD : θ'.D = θ.D)
    (hg : ∀ ℓ k i, θ'.read ℓ k (Sum.inl i) = θ.read ℓ k (Sum.inl i))
    (hv : ∀ ℓ k i, θ'.read ℓ k (Sum.inr i) = (c ℓ i)⁻¹ * θ.read ℓ k (Sum.inr i))
    (hw : ∀ ℓ i k, θ'.write ℓ i k = c ℓ i * θ.write ℓ i k)
    (S : Fin L → Matrix d d ℝ) (x : Matrix T dIn ℝ) :
    eval (Arch.gated σ id hid) S θ' x = eval (Arch.gated σ id hid) S θ x := by
  -- the hidden states of `θ'` and `θ` agree, by induction along the network
  have hh : ∀ ℓ : Fin (L + 1),
      hidden (Arch.gated σ id hid) S θ' x ℓ = hidden (Arch.gated σ id hid) S θ x ℓ := by
    intro ℓ
    induction ℓ using Fin.induction with
    | zero => rw [hidden_zero, hidden_zero, hE]
    | succ ℓ ih =>
      -- the stream term `h S_ℓ` is the same; compare the outputs of block `ℓ`
      rw [hidden_succ, hidden_succ, ih]
      congr 1
      set h := hidden (Arch.gated σ id hid) S θ x ℓ.castSucc
      -- the gates are the same, and the values are divided by `c ℓ i`
      have hz : ∀ t i, (h * θ'.read ℓ) t (Sum.inl i) = (h * θ.read ℓ) t (Sum.inl i) := by
        intro t i
        simp only [Matrix.mul_apply, hg]
      have hu : ∀ t i,
          (h * θ'.read ℓ) t (Sum.inr i) = (c ℓ i)⁻¹ * (h * θ.read ℓ) t (Sum.inr i) := by
        intro t i
        rw [Matrix.mul_apply, Matrix.mul_apply, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hv]
        ring
      -- so hidden unit `i` contributes `σ(z_i) (w_i / c) (c a_i) = σ(z_i) w_i a_i`
      ext t k
      rw [Matrix.mul_apply, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      show σ ((h * θ'.read ℓ) t (Sum.inl i)) * (h * θ'.read ℓ) t (Sum.inr i) * θ'.write ℓ i k =
        σ ((h * θ.read ℓ) t (Sum.inl i)) * (h * θ.read ℓ) t (Sum.inr i) * θ.write ℓ i k
      rw [hz, hu, hw]
      field_simp [hc ℓ i]
  -- hence the outputs agree
  rw [eval, eval, hh, hD]

/-- Helper: `τ ↦ e^{τ a} b` has derivative `a b` at `τ = 0`. -/
private theorem hasDerivAt_exp_mul_const (a b : ℝ) :
    HasDerivAt (fun τ : ℝ => Real.exp (τ * a) * b) (a * b) 0 := by
  have h := ((hasDerivAt_id (0 : ℝ)).mul_const a).exp.mul_const b
  simpa using h

omit [Fintype d] [DecidableEq d] in
/-- Helper: the map of a gated block is differentiable if the gate activation is. -/
private theorem differentiable_gated (hσ : Differentiable ℝ σ) (ℓ : Fin L) :
    Differentiable ℝ ((Arch.gated (T := T) (d := d) σ id hid).f ℓ) := by
  -- every entry of a matrix is a differentiable (linear) function of the matrix
  have he : ∀ t j, Differentiable ℝ fun M : Matrix T (hid ℓ ⊕ hid ℓ) ℝ => M t j :=
    fun t j => differentiable_pi.1 (differentiable_pi.1 differentiable_id t) j
  -- the entry `(t, i)` of the output is `σ(M t (inl i)) * M t (inr i)`
  exact differentiable_pi.2 fun t => differentiable_pi.2 fun i =>
    (hσ.comp (he t (Sum.inl i))).mul (he t (Sum.inr i))

/-- Helper: the curve of the rescalings `λ = e^{τ α ℓ i}`: the value column of hidden unit `i` of
block `ℓ` is multiplied by `e^{-τ α ℓ i}`, its write row by `e^{τ α ℓ i}`. -/
private noncomputable def rescaleCurve (α : ∀ ℓ, hid ℓ → ℝ) (τ : ℝ) :
    Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut where
  E := θ.E
  read ℓ := Matrix.of fun k j => Sum.elim (fun i => θ.read ℓ k (Sum.inl i))
    (fun i => Real.exp (τ * -(α ℓ i)) * θ.read ℓ k (Sum.inr i)) j
  write ℓ := Matrix.of fun i k => Real.exp (τ * α ℓ i) * θ.write ℓ i k
  D := θ.D

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the curve passes through `θ` at `τ = 0`. -/
private theorem rescaleCurve_zero (α : ∀ ℓ, hid ℓ → ℝ) : rescaleCurve θ α 0 = θ := by
  apply Params.ext'
  · rfl
  · intro ℓ
    ext k j
    cases j <;> simp [rescaleCurve]
  · intro ℓ
    ext i k
    simp [rescaleCurve]
  · rfl

omit [Fintype T] [DecidableEq d] in
/-- Helper: the curve has velocity `rescaleDir θ α` at `τ = 0`. The derivative is taken entry by
entry, through the linear equivalence of the parameters with the tuples of their components. -/
private theorem hasDerivAt_rescaleCurve (α : ∀ ℓ, hid ℓ → ℝ) :
    HasDerivAt (rescaleCurve θ α) (rescaleDir θ α) 0 := by
  have hprod : HasDerivAt (fun τ : ℝ => Params.linearEquivProd (rescaleCurve θ α τ))
      (Params.linearEquivProd (rescaleDir θ α)) 0 := by
    refine HasDerivAt.prodMk ?_ (HasDerivAt.prodMk ?_ (HasDerivAt.prodMk ?_ ?_))
    · -- the embedding does not move
      exact hasDerivAt_const (0 : ℝ) θ.E
    · -- the gate entries do not move; the value entries are `e^{-τ α} w`
      refine hasDerivAt_pi.2 fun ℓ => hasDerivAt_pi.2 fun k => hasDerivAt_pi.2 fun j => ?_
      cases j with
      | inl i => exact hasDerivAt_const (0 : ℝ) (θ.read ℓ k (Sum.inl i))
      | inr i => exact hasDerivAt_exp_mul_const (-(α ℓ i)) (θ.read ℓ k (Sum.inr i))
    · -- the write entries are `e^{τ α} a`
      exact hasDerivAt_pi.2 fun ℓ => hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun k =>
        hasDerivAt_exp_mul_const (α ℓ i) (θ.write ℓ i k)
    · -- the readout does not move
      exact hasDerivAt_const (0 : ℝ) θ.D
  -- back from the tuples of components to the parameters
  exact (LinearMap.toContinuousLinearMap
    (Params.linearEquivProd (A := Arch.gated (T := T) (d := d) σ id hid) (dIn := dIn)
      (dOut := dOut)).symm.toLinearMap).hasFDerivAt.comp_hasDerivAt 0 hprod

/-- The directions of the rescalings are flat. -/
theorem rescaleDir_mem_flat (hσ : Differentiable ℝ σ) (α : ∀ ℓ, hid ℓ → ℝ) :
    rescaleDir θ α ∈ flat (Arch.gated σ id hid) 0 θ := by
  -- `θ' ↦ F_θ'(x)` is differentiable
  have hdiff : ∀ x, DifferentiableAt ℝ
      (fun θ' : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut =>
        eval (Arch.gated σ id hid) 0 θ' x) θ :=
    fun x => (differentiable_eval (differentiable_gated hσ) differentiable_id x).differentiableAt
  -- the curve passes through `θ` with velocity `rescaleDir θ α`, and at every `τ` it is the
  -- rescaling `λ = e^{τ α ℓ i}`, which preserves the function
  refine mem_flat_of_hasDerivAt θ hdiff (rescaleCurve θ α) (rescaleDir θ α)
    (hasDerivAt_rescaleCurve θ α) (rescaleCurve_zero θ α)
    (Filter.Eventually.of_forall fun τ x => ?_)
  refine eval_rescale θ (fun ℓ i => Real.exp (τ * α ℓ i)) (fun _ _ => Real.exp_ne_zero _)
    (rescaleCurve θ α τ) rfl rfl (fun _ _ _ => rfl) (fun ℓ k i => ?_) (fun _ _ _ => rfl) 0 x
  -- the value columns: `e^{-τ α} = (e^{τ α})⁻¹`
  show Real.exp (τ * -(α ℓ i)) * θ.read ℓ k (Sum.inr i) = _
  rw [mul_neg, Real.exp_neg]

/-- **Lemma B.1 for gated blocks.** If `E` and every write have rank `d` and no value column of a
read vanishes, the direction `cobDir θ X + rescaleDir θ α` determines `X` and `α`. -/
theorem cobDir_add_rescaleDir_injective (hE : θ.E.rank = Fintype.card d)
    (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d)
    (hv : ∀ ℓ i, (fun k => θ.read ℓ k (Sum.inr i)) ≠ 0) :
    Function.Injective fun p : (Fin (L + 1) → Matrix d d ℝ) × (∀ ℓ, hid ℓ → ℝ) =>
      cobDir θ p.1 + rescaleDir θ p.2 := by
  sorry

/-- **Theorem 4.3 for gated blocks, without normalization,** under the conditions of its proof:
the functional dimension is at most `P - (L + 1) d² - s`, with `s` the number of hidden units of
the network. -/
theorem funDim_add_le_skipless_gated (hσ : Differentiable ℝ σ)
    (hE : θ.E.rank = Fintype.card d) (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d)
    (hv : ∀ ℓ i, (fun k => θ.read ℓ k (Sum.inr i)) ≠ 0) :
    funDim (Arch.gated σ id hid) 0 θ + ((L + 1) * Fintype.card d ^ 2 + ∑ ℓ, Fintype.card (hid ℓ))
      ≤ Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) := by
  sorry

end Skips
