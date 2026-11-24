import SkipsLean.Depth.StepTanh
import SkipsLean.Generic.Params

/-!
# Theorem 5.2 (i) without normalization: `tanh` blocks at any depth

Paper (dimension paper): Theorem 5.2 (i), the case without normalization, and its proof in
Appendix D.7 ("The parts together", first paragraph).

A network of `L` `tanh` blocks without skip connections, without normalization and without biases,
with `d_in, d_out ≥ d` and at least `d` hidden units in every block, has the functional dimension
`P - (L + 1) d²` at generic parameters.

The proof of the paper takes `θ` with: (R1) `E`, `D` and every write of rank `d`; for every block
(T1) no row of the write vanishes and (T2) the columns of the read are linearly independent over
`ℚ`; and every `W_read W_write` invertible. Such `θ` are regular (the derivative of a block at `0`
is `v ↦ v W_read W_write`). Claim `(D_L)` holds (Lemma D.5), the step of Lemma D.7 gives `(D_k)`
for `k = L - 1, …, 0`, and Proposition D.4 gives the functional dimension. The conditions fail only
on a set of measure zero; (T2) fails on countably many proper linear subspaces.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]

/-- The conditions on the parameters of a network of `tanh` blocks that the proof of
Theorem 5.2 (i) uses in the case without normalization. -/
structure TanhDepthGeneric (θ : Params (Arch.mlp (T := T) (d := d) Real.tanh id hid) dIn dOut) :
    Prop where
  /-- (R1) -/
  rank_E : θ.E.rank = Fintype.card d
  /-- (R1) -/
  rank_D : θ.D.rank = Fintype.card d
  /-- (R1) -/
  rank_write : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d
  /-- (T1): no row of a write vanishes -/
  write_row_ne_zero : ∀ ℓ (i : hid ℓ), θ.write ℓ i ≠ 0
  /-- (T2): the columns of every read are linearly independent over `ℚ` -/
  read_cols_indep : ∀ ℓ, LinearIndependent ℚ (fun j : hid ℓ => fun i : d => θ.read ℓ i j)
  /-- every `W_read W_write` is invertible -/
  read_mul_write : ∀ ℓ, IsUnit (θ.read ℓ * θ.write ℓ).det

/-- Helper: `M ↦ M.map tanh` has the identity as its derivative at `0`, since `tanh' 0 = 1`. -/
private theorem hasFDerivAt_map_tanh_zero {m n : Type*} [Fintype m] [Fintype n] :
    HasFDerivAt (fun M : Matrix m n ℝ => M.map Real.tanh)
      (ContinuousLinearMap.id ℝ (Matrix m n ℝ)) 0 := by
  refine hasFDerivAt_pi'' fun t => hasFDerivAt_pi'' fun i => ?_
  -- the entry `(t, i)` is `tanh` of the entry `(t, i)` of `M`, and `tanh' 0 = 1 - tanh 0 ^ 2 = 1`
  have h := (hasDerivAt_tanh ((0 : Matrix m n ℝ) t i)).comp_hasFDerivAt (0 : Matrix m n ℝ)
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : n => ℝ) i).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : m => n → ℝ) t)).hasFDerivAt
  refine h.congr_fderiv (ContinuousLinearMap.ext fun M => ?_)
  show (1 - Real.tanh ((0 : Matrix m n ℝ) t i) ^ 2) * M t i = M t i
  rw [Matrix.zero_apply, Real.tanh_zero]
  ring

variable (θ : Params (Arch.mlp (T := T) (d := d) Real.tanh id hid) dIn dOut)

/-- Under the conditions `θ` is regular: the derivative of block `ℓ` at `0` is
`v ↦ v W_read W_write`, which is injective. -/
theorem regular_of_tanhDepthGeneric (hθ : TanhDepthGeneric θ) :
    Regular (Arch.mlp Real.tanh id hid) θ := by
  refine ⟨hθ.rank_E, hθ.rank_D, hθ.rank_write, fun ℓ => ⟨0, ?_⟩⟩
  -- the right multiplications by the read and by the write, as continuous linear maps
  let mR : Matrix T d ℝ →L[ℝ] Matrix T (hid ℓ) ℝ := LinearMap.toContinuousLinearMap
    { toFun := fun n' => n' * θ.read ℓ
      map_add' := fun a b => Matrix.add_mul a b _
      map_smul' := fun c a => Matrix.smul_mul c a _ }
  let mW : Matrix T (hid ℓ) ℝ →L[ℝ] Matrix T d ℝ := LinearMap.toContinuousLinearMap
    { toFun := fun M => M * θ.write ℓ
      map_add' := fun a b => Matrix.add_mul a b _
      map_smul' := fun c a => Matrix.smul_mul c a _ }
  -- the block is `n' ↦ mW ((mR n').map tanh)`; its derivative at `0` is `v ↦ v W_read W_write`
  have h1 : HasFDerivAt (fun M : Matrix T (hid ℓ) ℝ => M.map Real.tanh)
      (ContinuousLinearMap.id ℝ _) (mR 0) := by
    rw [map_zero]
    exact hasFDerivAt_map_tanh_zero
  have hf : HasFDerivAt
      (fun n' : Matrix T d ℝ => (Arch.mlp Real.tanh id hid).f ℓ (n' * θ.read ℓ) * θ.write ℓ)
      (mW.comp ((ContinuousLinearMap.id ℝ _).comp mR)) 0 :=
    mW.hasFDerivAt.comp (0 : Matrix T d ℝ) (h1.comp (0 : Matrix T d ℝ) mR.hasFDerivAt)
  rw [hf.fderiv]
  -- `v ↦ v W_read W_write` is injective: multiply on the right by `(W_read W_write)⁻¹`
  have key : ∀ v : Matrix T d ℝ, v * θ.read ℓ * θ.write ℓ * (θ.read ℓ * θ.write ℓ)⁻¹ = v := by
    intro v
    rw [Matrix.mul_assoc v, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (hθ.read_mul_write ℓ),
      Matrix.mul_one]
  intro v w hvw
  have hvw' : v * θ.read ℓ * θ.write ℓ = w * θ.read ℓ * θ.write ℓ := hvw
  rw [← key v, ← key w, hvw']

/-- Under the conditions Claim `(D_k)` holds at every hidden state: `(D_L)` by Lemma D.5, and then
`(D_k)` for `k = L - 1, …, 0` by Lemma D.7. -/
theorem claim_of_tanhDepthGeneric [Nonempty T] (hθ : TanhDepthGeneric θ) (k : Fin (L + 1)) :
    Claim (Arch.mlp Real.tanh id hid) θ k := by
  -- `(D_L)` by Lemma D.5, then `(D_{k+1}) ⇒ (D_k)` by Lemma D.7
  induction k using Fin.reverseInduction with
  | last => exact claim_last _ θ rfl
  | cast k ih =>
    exact claim_castSucc_tanh θ (regular_of_tanhDepthGeneric θ hθ) k (hθ.write_row_ne_zero k)
      (hθ.read_cols_indep k) ih

/-- **Theorem 5.2 (i) without normalization, under the conditions of its proof:** the functional
dimension of a network of `L` `tanh` blocks is `P - (L + 1) d²`. -/
theorem funDim_tanh_skipless [Nonempty T] (hθ : TanhDepthGeneric θ) :
    funDim (Arch.mlp Real.tanh id hid) 0 θ + (L + 1) * Fintype.card d ^ 2
      = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) Real.tanh id hid) dIn dOut) :=
  -- Proposition D.4, with the blocks analytic, `θ` regular and `(D_0)`
  funDim_of_claim _ θ rfl (fun ℓ => analyticOnNhd_f_mlp analyticOnNhd_tanh ℓ)
    (regular_of_tanhDepthGeneric θ hθ) (claim_of_tanhDepthGeneric θ hθ 0)

/-- The conditions hold at generic parameters, when `d_in, d_out ≥ d ≥ 1` and every block has at
least `d` hidden units. -/
theorem ae_tanhDepthGeneric [Nonempty d]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) Real.tanh id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, TanhDepthGeneric θ := by
  sorry

/-- **Theorem 5.2 (i), the case without normalization:** a network of `L` `tanh` blocks without
skip connections, without normalization and without biases, with `d_in, d_out ≥ d ≥ 2` and at
least `d` hidden units in every block, has the functional dimension `P - (L + 1) d²` at generic
parameters. (The proof uses `d ≥ 1` only.) -/
theorem ae_funDim_tanh_skipless [Nonempty T]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) Real.tanh id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, funDim (Arch.mlp Real.tanh id hid) 0 θ + (L + 1) * Fintype.card d ^ 2
      = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) Real.tanh id hid) dIn dOut) := by
  have : Nonempty d := Fintype.card_pos_iff.1 (by omega)
  -- the conclusion holds wherever the conditions of the proof hold
  filter_upwards [ae_tanhDepthGeneric μ hdIn hdOut hhid] with θ hθ
  exact funDim_tanh_skipless θ hθ

end Skips
