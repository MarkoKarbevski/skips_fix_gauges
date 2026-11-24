import SkipsLean.OneBlock.LearnedSkipTriangularRMSZeroRank
import SkipsLean.OneBlock.TurnsActiveRowsSkipLinear

/-!
# One ReLU, ReLU² or ReGLU block with an upper triangular learned skip under pre-RMSNorm with
`ε = 0`: the equality

Paper (skips paper), Theorem B.1 (iii): "Let the network be pre-RMSNorm without biases, with a
learned skip `A`, full or upper triangular. […] For `ε = 0` it exceeds that of the residual
network with `ε = 0` by at most `d_model (d_model + 1)/2 − 1`, with equality for ReLU, ReLU² and
ReGLU blocks." Its proof: "For an upper triangular `A`, view the network as the network with a
full `A` restricted to triangular skips: its flat directions are those of the full network whose
entry `η_A` is upper triangular." And in "The case `ε = 0`": "which gives at least
`d_model (d_model − 1) + 2`, respectively `d_model (d_model − 1)/2 + 2`, dimensions besides
`K_B`".

The twin for `ε = 0` of `OneBlock/LearnedSkipTriangularRescale.lean`. As there, the statements
are in the paper's own sense: `funDimSkipsOn` on the inputs at which no normalized row vanishes
and no hidden unit (no gate) sits at its kink. On a batch of such inputs the family of upper
triangular skips and the family of all skips have the same Jacobian rank
(`jacobianRankSkips_tri_eq_learned_rmsNorm_zero`, `OneBlock/LearnedSkipTriangularRMSZeroRank.lean`),
so the values for the full skip (`OneBlock/LearnedSkipRMSZeroRescale.lean`,
`OneBlock/LearnedSkipRMSZeroReGLU.lean`) carry over:
`P + d² − (d(d−1) + 2) − s = P + d(d+1)/2 − (d(d−1)/2 + 2) − s`, with `s = d_hidden` for ReLU and
ReLU² and `s = 2 d_hidden` for ReGLU. Here:

* at one parameter, under the conditions of the statements for the full skip and for an
  invertible upper triangular skip: a batch of the paper's inputs with this rank; no batch of
  such inputs has a larger rank; the value of `funDimSkipsOn`;
* for `d_in, d_out ≥ d ≥ 2`, at almost every `(θ, A)` with `A` upper triangular: the value, and
  the equality with the residual network with the weights `θ`,
  `funDimSkipsOn = funDim + d(d+1)/2 − 1` (the residual network is measured by Lean's `funDim`,
  which at almost every `θ` is also the largest rank over the batches of the paper's inputs).

The condition that the paper does not state (`TurnsActiveRowsSkip`, `TurnsActiveRowsGatedSkip`
for the skip `A`) holds at almost every `(θ, A)` with `A` upper triangular
(`OneBlock/TurnsActiveRowsSkipLinear.lean`).
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d]
  [LinearOrder d] [Fintype dIn] [Fintype dOut]
variable {hid : Fin 1 → Type} [∀ ℓ, Fintype (hid ℓ)]
variable {σ σ' : ℝ → ℝ}

/-! ### Helpers: the arithmetic, the triangular family against the full one, the supremum -/

omit [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [LinearOrder d] [Fintype dIn]
  [Fintype dOut] in
/-- Helper (a copy of the private `half_add_half_ltr`): `d (d + 1)/2 + d (d − 1)/2 = d²` (both
products are even). -/
private theorem half_add_half_ltz (n : ℕ) : n * (n + 1) / 2 + n * (n - 1) / 2 = n ^ 2 := by
  have h1 := Nat.two_mul_div_two_of_even (Nat.even_mul_succ_self n)
  have h2 := Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self n)
  have h3 : n * (n + 1) + n * (n - 1) = 2 * n ^ 2 := by
    cases n with
    | zero => rfl
    | succ m => rw [Nat.add_sub_cancel]; ring
  generalize n * (n + 1) = y at h1 h3 ⊢
  generalize n * (n - 1) = x at h2 h3 ⊢
  generalize n ^ 2 = q at h3 ⊢
  omega

omit [Nonempty T] in
/-- Helper (as the private `exists_jacobianRankSkips_tri_ltr`, for `ε = 0`): a batch of inputs of
`U ⊆ learnedZeroDomain` at which the block is differentiable at the normalized read, on which the
full family has `rank + ((d (d − 1) + 2) + s) = P + d²`, gives the triangular family
`rank + ((d (d − 1)/2 + 2) + s) = P + d (d + 1)/2` on the same batch. -/
private theorem exists_jacobianRankSkips_tri_ltz {A : Arch T d 1} (hA : A.χ = rmsNorm 0)
    (θ : Params A dIn dOut) (R : Fin 1 → upperTriangular d)
    (hR : IsUnit (R 0 : Matrix d d ℝ).det) (U : Set (Matrix T dIn ℝ))
    (hUdom : ∀ x ∈ U, x ∈ learnedZeroDomain A θ fun ℓ => (R ℓ : Matrix d d ℝ))
    (hfx : ∀ x ∈ U, DifferentiableAt ℝ (A.f 0) (rmsNorm 0 (x * θ.E) * θ.read 0)) {s : ℕ}
    (hex : ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i, X i ∈ U) ∧
      jacobianRankSkips A (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) X
          (θ, fun ℓ => (R ℓ : Matrix d d ℝ)) + ((Fintype.card d * (Fintype.card d - 1) + 2) + s)
        = Module.finrank ℝ (Params A dIn dOut) + Fintype.card d ^ 2) :
    ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i, X i ∈ U) ∧
      jacobianRankSkips A (triSkips d 1) X (θ, R)
          + ((Fintype.card d * (Fintype.card d - 1) / 2 + 2) + s)
        = Module.finrank ℝ (Params A dIn dOut) + Fintype.card d * (Fintype.card d + 1) / 2 := by
  obtain ⟨n, X, hX, hr⟩ := hex
  refine ⟨n, X, hX, ?_⟩
  -- on the batch the two families have the same rank
  rw [jacobianRankSkips_tri_eq_learned_rmsNorm_zero hA θ R hR X (fun i => hUdom (X i) (hX i))
    fun i => hfx (X i) (hX i)]
  -- `d (d + 1)/2 + d (d − 1)/2 = d²` and `2 (d (d − 1)/2) = d (d − 1)`
  have h1 := half_add_half_ltz (Fintype.card d)
  have h2 := Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self (Fintype.card d))
  generalize Fintype.card d * (Fintype.card d + 1) = y at h1 ⊢
  generalize Fintype.card d * (Fintype.card d - 1) = x at h1 h2 hr ⊢
  generalize Fintype.card d ^ 2 = q at h1 hr
  omega

omit [Nonempty T] in
/-- Helper (as the private `jacobianRankSkips_tri_add_le_ltr`, for `ε = 0`): if the full family
has the value `fd + ((d (d − 1) + 2) + s) = P + d²` at `(θ, R)`, then on every batch of inputs of
`learnedZeroDomain` at which the block is differentiable at the normalized read the triangular
family has `rank + ((d (d − 1)/2 + 2) + s) ≤ P + d (d + 1)/2`. -/
private theorem jacobianRankSkips_tri_add_le_ltz {A : Arch T d 1} (hA : A.χ = rmsNorm 0)
    (θ : Params A dIn dOut) (R : Fin 1 → upperTriangular d)
    (hR : IsUnit (R 0 : Matrix d d ℝ).det) {s : ℕ}
    (hval : funDimLearned A (θ, fun ℓ => (R ℓ : Matrix d d ℝ))
        + ((Fintype.card d * (Fintype.card d - 1) + 2) + s)
      = Module.finrank ℝ (Params A dIn dOut) + Fintype.card d ^ 2)
    {n : ℕ} (X : Fin n → Matrix T dIn ℝ)
    (hX : ∀ i, X i ∈ learnedZeroDomain A θ fun ℓ => (R ℓ : Matrix d d ℝ))
    (hfx : ∀ i, DifferentiableAt ℝ (A.f 0) (rmsNorm 0 (X i * θ.E) * θ.read 0)) :
    jacobianRankSkips A (triSkips d 1) X (θ, R)
        + ((Fintype.card d * (Fintype.card d - 1) / 2 + 2) + s)
      ≤ Module.finrank ℝ (Params A dIn dOut) + Fintype.card d * (Fintype.card d + 1) / 2 := by
  -- the rank of the full family on the batch is at most its functional dimension
  have hle : jacobianRankSkips A (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) X
      (θ, fun ℓ => (R ℓ : Matrix d d ℝ)) ≤ funDimLearned A (θ, fun ℓ => (R ℓ : Matrix d d ℝ)) :=
    le_csSup ⟨Module.finrank ℝ (Params A dIn dOut × (Fin 1 → Matrix d d ℝ)), by
      rintro _ ⟨n, X, rfl⟩
      exact LinearMap.finrank_range_le _⟩ ⟨n, X, rfl⟩
  -- on the batch the two families have the same rank
  rw [jacobianRankSkips_tri_eq_learned_rmsNorm_zero hA θ R hR X hX hfx]
  -- `d (d + 1)/2 + d (d − 1)/2 = d²` and `2 (d (d − 1)/2) = d (d − 1)`
  have h1 := half_add_half_ltz (Fintype.card d)
  have h2 := Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self (Fintype.card d))
  generalize Fintype.card d * (Fintype.card d + 1) = y at h1 ⊢
  generalize Fintype.card d * (Fintype.card d - 1) = x at h1 h2 hval ⊢
  generalize Fintype.card d ^ 2 = q at h1 hval
  omega

omit [Fintype T] [Nonempty T] [DecidableEq d] [LinearOrder d] in
/-- Helper (a copy of the private `funDimSkipsOn_add_eq_ltr`): if one batch of inputs of `U` has
`rank + k = N` and every batch of inputs of `U` has `rank + k ≤ N`, then
`funDimSkipsOn + k = N` (a set of naturals that contains its upper bound). -/
private theorem funDimSkipsOn_add_eq_ltz {L : ℕ} {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (A : Arch T d L) (ι : V →L[ℝ] (Fin L → Matrix d d ℝ))
    (p : Params A dIn dOut × V) (U : Set (Matrix T dIn ℝ)) {k N : ℕ}
    (hex : ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i, X i ∈ U) ∧
      jacobianRankSkips A ι X p + k = N)
    (hle : ∀ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i, X i ∈ U) →
      jacobianRankSkips A ι X p + k ≤ N) :
    funDimSkipsOn A ι p U + k = N := by
  obtain ⟨n, X, hX, hr⟩ := hex
  -- the rank on `X` bounds every rank on a batch of inputs of `U`
  have hb : ∀ r ∈ {r : ℕ | ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i, X i ∈ U) ∧
      r = jacobianRankSkips A ι X p}, r ≤ jacobianRankSkips A ι X p := by
    rintro _ ⟨m, Y, hY, rfl⟩
    have := hle m Y hY
    omega
  have h1 : funDimSkipsOn A ι p U ≤ jacobianRankSkips A ι X p := by
    unfold funDimSkipsOn
    exact csSup_le ⟨_, n, X, hX, rfl⟩ hb
  have h2 : jacobianRankSkips A ι X p ≤ funDimSkipsOn A ι p U := by
    unfold funDimSkipsOn
    exact le_csSup ⟨_, hb⟩ ⟨n, X, hX, rfl⟩
  omega

/-! ### Helpers: the blocks are differentiable at the normalized read of the paper's inputs -/

omit [Fintype T] [Nonempty T] [DecidableEq d] [LinearOrder d] in
/-- Helper (a copy of the private `rmsNorm_mul_apply_lzf`): `N_0` scales every row:
`(N_0(h) W)_{t i} = (‖h_t‖²/d)^{-1/2} (h W)_{t i}`. -/
private theorem rmsNorm_mul_apply_ltz {n : Type*} [Fintype n] (h : Matrix T d ℝ)
    (W : Matrix d n ℝ) (t : T) (i : n) :
    (rmsNorm 0 h * W) t i
      = (Real.sqrt ((h t ⬝ᵥ h t) / (Fintype.card d : ℝ)))⁻¹ * (h * W) t i := by
  simp only [Matrix.mul_apply, Finset.mul_sum, rmsNorm, rmsRow, Matrix.of_apply, Pi.smul_apply,
    smul_eq_mul, mul_assoc, add_zero]

omit [DecidableEq d] [LinearOrder d] in
/-- Helper (a copy of the private `inv_sqrt_pos_lzf`): the factor of `N_0` at a row `v ≠ 0` is
positive. -/
private theorem inv_sqrt_pos_ltz {v : d → ℝ} (hv : v ≠ 0) :
    0 < (Real.sqrt ((v ⬝ᵥ v) / (Fintype.card d : ℝ)))⁻¹ := by
  have h1 : 0 < v ⬝ᵥ v :=
    lt_of_le_of_ne (Finset.sum_nonneg fun j _ => mul_self_nonneg (v j))
      (fun h => hv (dotProduct_self_eq_zero.1 h.symm))
  obtain ⟨j, -⟩ := Function.ne_iff.1 hv
  have h2 : (0 : ℝ) < Fintype.card d := Nat.cast_pos.2 (Fintype.card_pos_iff.2 ⟨j⟩)
  exact inv_pos.2 (Real.sqrt_pos.2 (div_pos h1 h2))

omit [Nonempty T] [DecidableEq d] [LinearOrder d] [Fintype dOut] in
/-- Helper (as the private `differentiableAt_f_mlp_ltr`, for `ε = 0`): at an input of
`learnedZeroDomain ∩ noKinkRMS θ` the map of the block is differentiable at the normalized read
`N_0(x E) W_read`, which has no zero entry: `N_0` scales the rows of `x E`, none of which is
zero, by positive numbers. -/
private theorem differentiableAt_f_mlp_ltz (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
    (R : Fin 1 → Matrix d d ℝ) (x : Matrix T dIn ℝ)
    (hx : x ∈ learnedZeroDomain (Arch.mlp σ (rmsNorm 0) hid) θ R ∩ noKinkRMS θ) :
    DifferentiableAt ℝ ((Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid).f 0)
      (rmsNorm 0 (x * θ.E) * θ.read 0) := by
  have hP : ∀ t i, (rmsNorm 0 (x * θ.E) * θ.read 0) t i ≠ 0 := by
    intro t i
    rw [rmsNorm_mul_apply_ltz]
    exact mul_ne_zero (inv_sqrt_pos_ltz (hx.1.1 t)).ne' (hx.2 t i)
  generalize rmsNorm 0 (x * θ.E) * θ.read 0 = P at hP ⊢
  refine differentiableAt_pi.2 fun t => differentiableAt_pi.2 fun i => ?_
  have hent : Differentiable ℝ (fun M : Matrix T (hid 0) ℝ => M t i) :=
    differentiable_pi.1 (differentiable_pi.1 differentiable_id t) i
  have h := (hσ _ (hP t i)).differentiableAt.comp P (hent P)
  exact h

/-! ### MLP blocks with a positively homogeneous activation, at one parameter -/

/-- **Theorem B.1 (iii) for `ε = 0` and the upper triangular skip, in the paper's own sense, for
one MLP block with a positively homogeneous activation, at one parameter:** under the conditions
of the statement for the full skip, for an invertible upper triangular skip, a finite batch of
inputs at which no normalized row vanishes and no hidden unit sits at its kink, on which the
Jacobian in the weights and the triangular skip has the rank
`P + d(d+1)/2 − (d(d−1)/2 + 2) − s`. -/
theorem exists_jacobianRankSkips_tri_mlp_rescale_rmsNorm_zero {k : ℕ}
    (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (hhom : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (hU : UnitsRescaleSphere σ σ' k d d (hid 0))
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
    (hθ : OneBlockGenericRMS θ) (hd : 2 ≤ Fintype.card d)
    (R : Fin 1 → upperTriangular d) (hR : IsUnit (R 0 : Matrix d d ℝ).det)
    (hturn : TurnsActiveRowsSkip θ (R 0 : Matrix d d ℝ))
    (hw : ∃ v : d → ℝ, (∀ i, (v ᵥ* θ.read 0) i ≠ 0) ∧ LinearIndependent ℝ
      ![v ᵥ* (R 0 : Matrix d d ℝ), vanillaBlock σ (θ.read 0) (θ.write 0) v]) :
    ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ),
      (∀ i, X i ∈ learnedZeroDomain (Arch.mlp σ (rmsNorm 0) hid) θ
        (fun ℓ => (R ℓ : Matrix d d ℝ)) ∩ noKinkRMS θ) ∧
      jacobianRankSkips (Arch.mlp σ (rmsNorm 0) hid) (triSkips d 1) X (θ, R)
          + ((Fintype.card d * (Fintype.card d - 1) / 2 + 2) + Fintype.card (hid 0))
        = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
          + Fintype.card d * (Fintype.card d + 1) / 2 := by
  -- the batch of the paper's inputs for the full skip `R`, on which the two families have the
  -- same rank
  exact exists_jacobianRankSkips_tri_ltz (A := Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) rfl
    θ R hR (learnedZeroDomain (Arch.mlp σ (rmsNorm 0) hid) θ (fun ℓ => (R ℓ : Matrix d d ℝ))
      ∩ noKinkRMS θ) (fun _ hx => hx.1) (fun x hx => differentiableAt_f_mlp_ltz hσ θ _ x hx)
    (exists_jacobianRankSkips_mlp_oneBlock_rescale_rmsNorm_zero hσ hhom hU θ hθ hd
      (fun ℓ => (R ℓ : Matrix d d ℝ)) hR hturn hw)

/-- **No batch of the paper's inputs has a larger rank,** for one MLP block with a positively
homogeneous activation and an upper triangular learned skip, `ε = 0`, at one parameter. -/
theorem jacobianRankSkips_tri_add_le_mlp_rescale_rmsNorm_zero {k : ℕ}
    (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (hhom : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (hU : UnitsRescaleSphere σ σ' k d d (hid 0))
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
    (hθ : OneBlockGenericRMS θ) (hd : 2 ≤ Fintype.card d)
    (R : Fin 1 → upperTriangular d) (hR : IsUnit (R 0 : Matrix d d ℝ).det)
    (hturn : TurnsActiveRowsSkip θ (R 0 : Matrix d d ℝ))
    (hw : ∃ v : d → ℝ, (∀ i, (v ᵥ* θ.read 0) i ≠ 0) ∧ LinearIndependent ℝ
      ![v ᵥ* (R 0 : Matrix d d ℝ), vanillaBlock σ (θ.read 0) (θ.write 0) v])
    {n : ℕ} (X : Fin n → Matrix T dIn ℝ)
    (hX : ∀ i, X i ∈ learnedZeroDomain (Arch.mlp σ (rmsNorm 0) hid) θ
      (fun ℓ => (R ℓ : Matrix d d ℝ)) ∩ noKinkRMS θ) :
    jacobianRankSkips (Arch.mlp σ (rmsNorm 0) hid) (triSkips d 1) X (θ, R)
        + ((Fintype.card d * (Fintype.card d - 1) / 2 + 2) + Fintype.card (hid 0))
      ≤ Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
        + Fintype.card d * (Fintype.card d + 1) / 2 := by
  -- the rank of the full family on the batch, at most its value `P + d² − (d(d−1) + 2) − s`
  exact jacobianRankSkips_tri_add_le_ltz (A := Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) rfl
    θ R hR (funDimLearned_mlp_oneBlock_rescale_rmsNorm_zero hσ hhom hU θ hθ hd
      (fun ℓ => (R ℓ : Matrix d d ℝ)) hR hturn hw) X (fun i => (hX i).1)
    (fun i => differentiableAt_f_mlp_ltz hσ θ _ (X i) (hX i))

/-- **Theorem B.1 (iii) for `ε = 0` and the upper triangular skip, for one MLP block with a
positively homogeneous activation, at one parameter:** the functional dimension on the inputs at
which no normalized row vanishes and no hidden unit sits at its kink is
`P + d(d+1)/2 − (d(d−1)/2 + 2) − s`. -/
theorem funDimSkipsOn_tri_mlp_rescale_rmsNorm_zero {k : ℕ}
    (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (hhom : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (hU : UnitsRescaleSphere σ σ' k d d (hid 0))
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
    (hθ : OneBlockGenericRMS θ) (hd : 2 ≤ Fintype.card d)
    (R : Fin 1 → upperTriangular d) (hR : IsUnit (R 0 : Matrix d d ℝ).det)
    (hturn : TurnsActiveRowsSkip θ (R 0 : Matrix d d ℝ))
    (hw : ∃ v : d → ℝ, (∀ i, (v ᵥ* θ.read 0) i ≠ 0) ∧ LinearIndependent ℝ
      ![v ᵥ* (R 0 : Matrix d d ℝ), vanillaBlock σ (θ.read 0) (θ.write 0) v]) :
    funDimSkipsOn (Arch.mlp σ (rmsNorm 0) hid) (triSkips d 1) (θ, R)
        (learnedZeroDomain (Arch.mlp σ (rmsNorm 0) hid) θ (fun ℓ => (R ℓ : Matrix d d ℝ))
          ∩ noKinkRMS θ)
        + ((Fintype.card d * (Fintype.card d - 1) / 2 + 2) + Fintype.card (hid 0))
      = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
        + Fintype.card d * (Fintype.card d + 1) / 2 := by
  -- the set of the ranks contains its upper bound
  exact funDimSkipsOn_add_eq_ltz _ _ _ _
    (exists_jacobianRankSkips_tri_mlp_rescale_rmsNorm_zero hσ hhom hU θ hθ hd R hR hturn hw)
    (fun _ X hX => jacobianRankSkips_tri_add_le_mlp_rescale_rmsNorm_zero hσ hhom hU θ hθ hd R hR
      hturn hw X hX)

/-! ### Helpers: almost every `(θ, A)`, `A` upper triangular -/

omit [Fintype T] [Nonempty T] [DecidableEq d] [LinearOrder d] in
/-- Helper (a copy of the private `ae_fst_ltr`): a condition on the weights that holds at almost
every `θ` holds at almost every `(θ, v)`. -/
private theorem ae_fst_ltz {A : Arch T d 1} {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] (hB : BorelSpace V)
    (μ : Measure (Params A dIn dOut × V)) (hμ : μ.IsAddHaarMeasure) {Q : Params A dIn dOut → Prop}
    (h : ∀ᵐ θ ∂(Measure.addHaar : Measure (Params A dIn dOut)), Q θ) :
    ∀ᵐ p ∂μ, Q p.1 := by
  rw [ae_iff] at h
  obtain ⟨N, hsub, hN, hN0⟩ := exists_measurable_superset_of_null h
  have hc : ∀ᵐ θ ∂(Measure.addHaar : Measure (Params A dIn dOut)), θ ∈ Nᶜ :=
    measure_eq_zero_iff_ae_notMem.1 hN0
  have h1 := (ae_comp_linearMap_mem_iff (LinearMap.fst ℝ (Params A dIn dOut) V) μ
    Measure.addHaar (LinearMap.fst_surjective) hN.compl).2 hc
  refine h1.mono fun p hp => ?_
  by_contra hq
  exact hp (hsub hq)

omit [LinearOrder d] in
/-- Helper (a copy of the private `ae_isUnit_det_ltr`): if a square matrix that depends linearly
on a point of `E` is the identity at one point, it is invertible at almost every point. -/
private theorem ae_isUnit_det_ltz {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] (hB : BorelSpace E) (μ : Measure E)
    (hμ : μ.IsAddHaarMeasure) (Φ : E →ₗ[ℝ] Matrix d d ℝ) (x₀ : E) (h₀ : Φ x₀ = 1) :
    ∀ᵐ x ∂μ, IsUnit (Φ x).det := by
  -- the entries are linear, so the determinant is analytic
  have hentry : ∀ i j, AnalyticOnNhd ℝ (fun x => Φ x i j) Set.univ := fun i j =>
    (LinearMap.toContinuousLinearMap ((Matrix.entryLinearMap ℝ ℝ i j) ∘ₗ Φ)).analyticOnNhd _
  have hφ : AnalyticOnNhd ℝ (fun x => (Φ x).det) Set.univ := by
    simp only [Matrix.det_apply']
    exact Finset.analyticOnNhd_fun_sum _ fun σ _ => analyticOnNhd_const.mul
      (Finset.analyticOnNhd_fun_prod _ fun i _ => hentry (σ i) i)
  -- it is `1` at `x₀`, so its zero set is null
  have hnull := measure_zeroSet_of_analytic μ hφ ⟨x₀, by rw [h₀, Matrix.det_one]; exact one_ne_zero⟩
  rw [ae_iff]
  simpa only [isUnit_iff_ne_zero, not_not] using hnull

omit [Fintype T] [Nonempty T] in
/-- Helper (a copy of the private `ae_generic_tri_ltr`): at almost every `(θ, A)`, `A` upper
triangular, a condition on the weights that holds at almost every `θ` holds, and `A` is
invertible (its determinant is a polynomial in the entries, `1` at `A = 1`). -/
private theorem ae_generic_tri_ltz {A : Arch T d 1}
    (μ : Measure (Params A dIn dOut × (Fin 1 → upperTriangular d))) [hμ : μ.IsAddHaarMeasure]
    {Q : Params A dIn dOut → Prop}
    (h : ∀ᵐ θ ∂(Measure.addHaar : Measure (Params A dIn dOut)), Q θ) :
    ∀ᵐ p ∂μ, Q p.1 ∧ IsUnit (p.2 0 : Matrix d d ℝ).det := by
  have hBt : BorelSpace (Fin 1 → upperTriangular d) := inferInstance
  have hBp : BorelSpace (Params A dIn dOut × (Fin 1 → upperTriangular d)) := Prod.borelSpace
  have h1 := ae_fst_ltz hBt μ hμ h
  have h2 := ae_isUnit_det_ltz hBp μ hμ
    ((upperTriangular d).subtype ∘ₗ (LinearMap.proj (R := ℝ)
      (φ := fun _ : Fin 1 => upperTriangular d) 0)
      ∘ₗ (LinearMap.snd ℝ (Params A dIn dOut) (Fin 1 → upperTriangular d)))
    (0, fun _ => ⟨1, Matrix.blockTriangular_one⟩) rfl
  filter_upwards [h1, h2] with p hp1 hp2
  exact ⟨hp1, hp2⟩

omit [Fintype T] [Nonempty T] [Fintype dIn] [Fintype dOut] in
/-- Helper: the skip `v 0` of a family `v` of upper triangular skips, linear in `v`. -/
private noncomputable def triLin_ltz : (Fin 1 → upperTriangular d) →ₗ[ℝ] Matrix d d ℝ :=
  (upperTriangular d).subtype ∘ₗ LinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => upperTriangular d) 0

omit [Fintype T] [Nonempty T] [Fintype dIn] [Fintype dOut] in
/-- Helper: the skip of the family `v₀ = (1)` is the identity. -/
private theorem triLin_one_ltz :
    triLin_ltz (d := d) (fun _ => ⟨1, Matrix.blockTriangular_one⟩) = 1 := rfl

omit [Fintype T] [Nonempty T] [DecidableEq d] [LinearOrder d] in
/-- Helper: `d (d + 1)/2 ≥ 1` for `d ≥ 2`. -/
private theorem one_le_half_ltz (hd : 2 ≤ Fintype.card d) :
    1 ≤ Fintype.card d * (Fintype.card d + 1) / 2 := by
  have h := Nat.mul_le_mul hd (show 3 ≤ Fintype.card d + 1 by omega)
  omega

omit [LinearOrder d] in
/-- Helper (the two conditions of `OneBlock/TurnsActiveRowsSkipLinear.lean` for a ReLU block, with
the Borel and Haar instances as explicit arguments): at almost every `(θ, v)` the block turns a
dense set of the active rows and some row off the kinks, for the skip `ι v`. -/
private theorem ae_turned_relu_ltz [Nonempty (hid 0)] {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] (hB : BorelSpace V)
    (ι : V →ₗ[ℝ] Matrix d d ℝ) (v₀ : V) (hι : ι v₀ = 1)
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut × V))
    (hμ : μ.IsAddHaarMeasure) (hd : 2 ≤ Fintype.card d) :
    ∀ᵐ p ∂μ, TurnsActiveRowsSkip p.1 (ι p.2) ∧ ∃ v : d → ℝ, (∀ i, (v ᵥ* p.1.read 0) i ≠ 0) ∧
      LinearIndependent ℝ ![v ᵥ* ι p.2, vanillaBlock relu (p.1.read 0) (p.1.write 0) v] :=
  (ae_turnsActiveRowsSkip_relu_of_linear ι v₀ hι μ hd).and
    (ae_exists_turned_row_skip_relu_of_linear ι v₀ hι μ hd)

omit [LinearOrder d] in
/-- Helper (the same for a ReLU² block). -/
private theorem ae_turned_reluSq_ltz [Nonempty (hid 0)] {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] (hB : BorelSpace V)
    (ι : V →ₗ[ℝ] Matrix d d ℝ) (v₀ : V) (hι : ι v₀ = 1)
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) reluSq (rmsNorm 0) hid) dIn dOut × V))
    (hμ : μ.IsAddHaarMeasure) (hd : 2 ≤ Fintype.card d) :
    ∀ᵐ p ∂μ, TurnsActiveRowsSkip p.1 (ι p.2) ∧ ∃ v : d → ℝ, (∀ i, (v ᵥ* p.1.read 0) i ≠ 0) ∧
      LinearIndependent ℝ ![v ᵥ* ι p.2, vanillaBlock reluSq (p.1.read 0) (p.1.write 0) v] :=
  (ae_turnsActiveRowsSkip_reluSq_of_linear ι v₀ hι μ hd).and
    (ae_exists_turned_row_skip_reluSq_of_linear ι v₀ hι μ hd)

omit [LinearOrder d] in
/-- Helper (the same for a ReGLU block, with the gates). -/
private theorem ae_turned_reglu_ltz [Nonempty (hid 0)] {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] (hB : BorelSpace V)
    (ι : V →ₗ[ℝ] Matrix d d ℝ) (v₀ : V) (hι : ι v₀ = 1)
    (μ : Measure (Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut × V))
    (hμ : μ.IsAddHaarMeasure) (hd : 2 ≤ Fintype.card d) :
    ∀ᵐ p ∂μ, TurnsActiveRowsGatedSkip p.1 (ι p.2) ∧
      ∃ v : d → ℝ, (∀ i, (v ᵥ* p.1.read 0) (Sum.inl i) ≠ 0) ∧
        LinearIndependent ℝ ![v ᵥ* ι p.2, gatedBlock relu ((p.1.read 0).submatrix id Sum.inl)
          ((p.1.read 0).submatrix id Sum.inr) (p.1.write 0) v] :=
  (ae_turnsActiveRowsGatedSkip_reglu_of_linear ι v₀ hι μ hd).and
    (ae_exists_turned_row_skip_reglu_of_linear ι v₀ hι μ hd)

/-! ### ReLU and ReLU² blocks, at almost every weights and upper triangular skip -/

/-- **Theorem B.1 (iii) of the skips paper for `ε = 0`, "with equality", for one ReLU block with
a hidden unit and an upper triangular learned skip:** for `d_in, d_out ≥ d ≥ 2`, at almost every
`(θ, A)`, `A` upper triangular, the functional dimension on the inputs at which no normalized row
vanishes and no hidden unit sits at its kink is `P + d(d+1)/2 − (d(d−1)/2 + 2) − d_hidden`. -/
theorem ae_funDimSkipsOn_tri_relu_rmsNorm_zero [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut
      × (Fin 1 → upperTriangular d)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, funDimSkipsOn (Arch.mlp relu (rmsNorm 0) hid) (triSkips d 1) p
        (learnedZeroDomain (Arch.mlp relu (rmsNorm 0) hid) p.1
          (fun ℓ => (p.2 ℓ : Matrix d d ℝ)) ∩ noKinkRMS p.1)
        + ((Fintype.card d * (Fintype.card d - 1) / 2 + 2) + Fintype.card (hid 0))
      = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut)
        + Fintype.card d * (Fintype.card d + 1) / 2 := by
  -- the conditions of the proof, an invertible skip, the turned rows for the skip `A`
  have hBt : BorelSpace (Fin 1 → upperTriangular d) := inferInstance
  have hμ : μ.IsAddHaarMeasure := inferInstance
  filter_upwards [ae_generic_tri_ltz μ (ae_oneBlockGenericRMS Measure.addHaar hd hdIn hdOut),
    ae_turned_relu_ltz hBt triLin_ltz _ triLin_one_ltz μ hμ hd] with p hp hturn
  exact funDimSkipsOn_tri_mlp_rescale_rmsNorm_zero (fun _ hz => hasDerivAt_relu hz)
    relu_homogeneous (relu_unitsRescaleSphere d d (hid 0)) p.1 hp.1 hd p.2 hp.2 hturn.1 hturn.2

/-- **Theorem B.1 (iii) of the skips paper, "For `ε = 0` it exceeds that of the residual network
with `ε = 0` by at most `d_model (d_model + 1)/2 − 1`, with equality for ReLU […] blocks", for
one ReLU block with a hidden unit and an upper triangular learned skip:** at almost every
`(θ, A)`, `A` upper triangular, the functional dimension on the paper's inputs exceeds that of
the residual network with the weights `θ` by exactly `d(d+1)/2 − 1`. -/
theorem ae_funDimSkipsOn_tri_relu_rmsNorm_zero_eq_residual_add [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut
      × (Fin 1 → upperTriangular d)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, funDimSkipsOn (Arch.mlp relu (rmsNorm 0) hid) (triSkips d 1) p
        (learnedZeroDomain (Arch.mlp relu (rmsNorm 0) hid) p.1
          (fun ℓ => (p.2 ℓ : Matrix d d ℝ)) ∩ noKinkRMS p.1)
      = funDim (Arch.mlp relu (rmsNorm 0) hid) 1 p.1
        + (Fintype.card d * (Fintype.card d + 1) / 2 - 1) := by
  -- `fd + ((d(d−1)/2 + 2) + s) = P + d(d+1)/2` and `fd₁ + ((d(d−1)/2 + 1) + s) = P`
  have hBt : BorelSpace (Fin 1 → upperTriangular d) := inferInstance
  have hμ : μ.IsAddHaarMeasure := inferInstance
  filter_upwards [ae_funDimSkipsOn_tri_relu_rmsNorm_zero μ hd hdIn hdOut,
    ae_fst_ltz hBt μ hμ
      (ae_funDim_relu_oneBlock_residual_rmsNorm_zero Measure.addHaar hd hdIn hdOut)]
    with p hp hres
  have h1 := one_le_half_ltz hd
  generalize Fintype.card d * (Fintype.card d - 1) / 2 = a at hp hres
  generalize Fintype.card d * (Fintype.card d + 1) / 2 = b at hp h1 ⊢
  omega

/-- **Theorem B.1 (iii) of the skips paper for `ε = 0`, "with equality", for one ReLU² block with
a hidden unit and an upper triangular learned skip:** for `d_in, d_out ≥ d ≥ 2`, at almost every
`(θ, A)`, `A` upper triangular, the functional dimension on the inputs at which no normalized row
vanishes and no hidden unit sits at its kink is `P + d(d+1)/2 − (d(d−1)/2 + 2) − d_hidden`. -/
theorem ae_funDimSkipsOn_tri_reluSq_rmsNorm_zero [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) reluSq (rmsNorm 0) hid) dIn dOut
      × (Fin 1 → upperTriangular d)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, funDimSkipsOn (Arch.mlp reluSq (rmsNorm 0) hid) (triSkips d 1) p
        (learnedZeroDomain (Arch.mlp reluSq (rmsNorm 0) hid) p.1
          (fun ℓ => (p.2 ℓ : Matrix d d ℝ)) ∩ noKinkRMS p.1)
        + ((Fintype.card d * (Fintype.card d - 1) / 2 + 2) + Fintype.card (hid 0))
      = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) reluSq (rmsNorm 0) hid) dIn dOut)
        + Fintype.card d * (Fintype.card d + 1) / 2 := by
  -- the conditions of the proof, an invertible skip, the turned rows for the skip `A`
  have hBt : BorelSpace (Fin 1 → upperTriangular d) := inferInstance
  have hμ : μ.IsAddHaarMeasure := inferInstance
  filter_upwards [ae_generic_tri_ltz μ (ae_oneBlockGenericRMS Measure.addHaar hd hdIn hdOut),
    ae_turned_reluSq_ltz hBt triLin_ltz _ triLin_one_ltz μ hμ hd] with p hp hturn
  exact funDimSkipsOn_tri_mlp_rescale_rmsNorm_zero (fun z _ => hasDerivAt_reluSq z)
    reluSq_homogeneous (reluSq_unitsRescaleSphere d d (hid 0)) p.1 hp.1 hd p.2 hp.2 hturn.1
    hturn.2

/-- **Theorem B.1 (iii) of the skips paper, "with equality for […] ReLU² […] blocks", for one
ReLU² block with a hidden unit and an upper triangular learned skip, `ε = 0`:** at almost every
`(θ, A)`, `A` upper triangular, the functional dimension on the paper's inputs exceeds that of
the residual network with the weights `θ` by exactly `d(d+1)/2 − 1`. -/
theorem ae_funDimSkipsOn_tri_reluSq_rmsNorm_zero_eq_residual_add [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) reluSq (rmsNorm 0) hid) dIn dOut
      × (Fin 1 → upperTriangular d)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, funDimSkipsOn (Arch.mlp reluSq (rmsNorm 0) hid) (triSkips d 1) p
        (learnedZeroDomain (Arch.mlp reluSq (rmsNorm 0) hid) p.1
          (fun ℓ => (p.2 ℓ : Matrix d d ℝ)) ∩ noKinkRMS p.1)
      = funDim (Arch.mlp reluSq (rmsNorm 0) hid) 1 p.1
        + (Fintype.card d * (Fintype.card d + 1) / 2 - 1) := by
  -- `fd + ((d(d−1)/2 + 2) + s) = P + d(d+1)/2` and `fd₁ + ((d(d−1)/2 + 1) + s) = P`
  have hBt : BorelSpace (Fin 1 → upperTriangular d) := inferInstance
  have hμ : μ.IsAddHaarMeasure := inferInstance
  filter_upwards [ae_funDimSkipsOn_tri_reluSq_rmsNorm_zero μ hd hdIn hdOut,
    ae_fst_ltz hBt μ hμ
      (ae_funDim_reluSq_oneBlock_residual_rmsNorm_zero Measure.addHaar hd hdIn hdOut)]
    with p hp hres
  have h1 := one_le_half_ltz hd
  generalize Fintype.card d * (Fintype.card d - 1) / 2 = a at hp hres
  generalize Fintype.card d * (Fintype.card d + 1) / 2 = b at hp h1 ⊢
  omega

/-! ### ReGLU blocks -/

omit [Nonempty T] [DecidableEq d] [LinearOrder d] [Fintype dOut] in
/-- Helper (as the private `differentiableAt_f_reglu_ltr`, for `ε = 0`): at an input of
`learnedZeroDomain ∩ noKinkGateRMS θ` the map of the ReGLU block is differentiable at the
normalized read `N_0(x E) W_read`, whose gates are positive multiples of those of `x E W_read`
(no row of `x E` is zero), so not at the kink. -/
private theorem differentiableAt_f_reglu_ltz
    (θ : Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut)
    (R : Fin 1 → Matrix d d ℝ) (x : Matrix T dIn ℝ)
    (hx : x ∈ learnedZeroDomain (Arch.gated relu (rmsNorm 0) hid) θ R ∩ noKinkGateRMS θ) :
    DifferentiableAt ℝ ((Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid).f 0)
      (rmsNorm 0 (x * θ.E) * θ.read 0) := by
  have hM : ∀ t i, (rmsNorm 0 (x * θ.E) * θ.read 0) t (Sum.inl i) ≠ 0 := by
    intro t i
    rw [rmsNorm_mul_apply_ltz]
    exact mul_ne_zero (inv_sqrt_pos_ltz (hx.1.1 t)).ne' (hx.2 t i)
  generalize rmsNorm 0 (x * θ.E) * θ.read 0 = M at hM ⊢
  refine differentiableAt_pi.2 fun t => differentiableAt_pi.2 fun i => ?_
  have he : ∀ j, Differentiable ℝ (fun N : Matrix T (hid 0 ⊕ hid 0) ℝ => N t j) := fun j =>
    differentiable_pi.1 (differentiable_pi.1 differentiable_id t) j
  have h := ((hasDerivAt_relu (hM t i)).differentiableAt.comp M (he (Sum.inl i) M)).mul
    (he (Sum.inr i) M)
  exact h

/-- **Theorem B.1 (iii) for `ε = 0` and the upper triangular skip, in the paper's own sense, for
one ReGLU block, at one parameter:** under the conditions of the statement for the full skip, for
an invertible upper triangular skip, a finite batch of inputs at which no normalized row vanishes
and no gate sits at its kink, on which the Jacobian in the weights and the triangular skip has
the rank `P + d(d+1)/2 − (d(d−1)/2 + 2) − 2 d_hidden`. -/
theorem exists_jacobianRankSkips_tri_reglu_rmsNorm_zero
    (θ : Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut)
    (hθ : OneBlockGenericReGLURMS θ) (hd : 2 ≤ Fintype.card d)
    (R : Fin 1 → upperTriangular d) (hR : IsUnit (R 0 : Matrix d d ℝ).det)
    (hturn : TurnsActiveRowsGatedSkip θ (R 0 : Matrix d d ℝ))
    (hw : ∃ v : d → ℝ, (∀ i, (v ᵥ* θ.read 0) (Sum.inl i) ≠ 0) ∧ LinearIndependent ℝ
      ![v ᵥ* (R 0 : Matrix d d ℝ), gatedBlock relu ((θ.read 0).submatrix id Sum.inl)
        ((θ.read 0).submatrix id Sum.inr) (θ.write 0) v]) :
    ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ),
      (∀ i, X i ∈ learnedZeroDomain (Arch.gated relu (rmsNorm 0) hid) θ
        (fun ℓ => (R ℓ : Matrix d d ℝ)) ∩ noKinkGateRMS θ) ∧
      jacobianRankSkips (Arch.gated relu (rmsNorm 0) hid) (triSkips d 1) X (θ, R)
          + ((Fintype.card d * (Fintype.card d - 1) / 2 + 2) + 2 * Fintype.card (hid 0))
        = Module.finrank ℝ
            (Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut)
          + Fintype.card d * (Fintype.card d + 1) / 2 := by
  -- the batch of the paper's inputs for the full skip `R`, on which the two families have the
  -- same rank
  exact exists_jacobianRankSkips_tri_ltz (A := Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid)
    rfl θ R hR (learnedZeroDomain (Arch.gated relu (rmsNorm 0) hid) θ
      (fun ℓ => (R ℓ : Matrix d d ℝ)) ∩ noKinkGateRMS θ) (fun _ hx => hx.1)
    (fun x hx => differentiableAt_f_reglu_ltz θ _ x hx)
    (exists_jacobianRankSkips_reglu_oneBlock_rmsNorm_zero θ hθ hd
      (fun ℓ => (R ℓ : Matrix d d ℝ)) hR hturn hw)

/-- **No batch of the paper's inputs has a larger rank,** for one ReGLU block with an upper
triangular learned skip, `ε = 0`, at one parameter. -/
theorem jacobianRankSkips_tri_add_le_reglu_rmsNorm_zero
    (θ : Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut)
    (hθ : OneBlockGenericReGLURMS θ) (hd : 2 ≤ Fintype.card d)
    (R : Fin 1 → upperTriangular d) (hR : IsUnit (R 0 : Matrix d d ℝ).det)
    (hturn : TurnsActiveRowsGatedSkip θ (R 0 : Matrix d d ℝ))
    (hw : ∃ v : d → ℝ, (∀ i, (v ᵥ* θ.read 0) (Sum.inl i) ≠ 0) ∧ LinearIndependent ℝ
      ![v ᵥ* (R 0 : Matrix d d ℝ), gatedBlock relu ((θ.read 0).submatrix id Sum.inl)
        ((θ.read 0).submatrix id Sum.inr) (θ.write 0) v])
    {n : ℕ} (X : Fin n → Matrix T dIn ℝ)
    (hX : ∀ i, X i ∈ learnedZeroDomain (Arch.gated relu (rmsNorm 0) hid) θ
      (fun ℓ => (R ℓ : Matrix d d ℝ)) ∩ noKinkGateRMS θ) :
    jacobianRankSkips (Arch.gated relu (rmsNorm 0) hid) (triSkips d 1) X (θ, R)
        + ((Fintype.card d * (Fintype.card d - 1) / 2 + 2) + 2 * Fintype.card (hid 0))
      ≤ Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut)
        + Fintype.card d * (Fintype.card d + 1) / 2 := by
  -- the rank of the full family on the batch, at most its value `P + d² − (d(d−1) + 2) − 2 s`
  exact jacobianRankSkips_tri_add_le_ltz (A := Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid)
    rfl θ R hR (funDimLearned_reglu_oneBlock_rmsNorm_zero θ hθ hd
      (fun ℓ => (R ℓ : Matrix d d ℝ)) hR hturn hw) X (fun i => (hX i).1)
    (fun i => differentiableAt_f_reglu_ltz θ _ (X i) (hX i))

/-- **Theorem B.1 (iii) for `ε = 0` and the upper triangular skip, for one ReGLU block, at one
parameter:** the functional dimension on the inputs at which no normalized row vanishes and no
gate sits at its kink is `P + d(d+1)/2 − (d(d−1)/2 + 2) − 2 d_hidden`. -/
theorem funDimSkipsOn_tri_reglu_rmsNorm_zero
    (θ : Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut)
    (hθ : OneBlockGenericReGLURMS θ) (hd : 2 ≤ Fintype.card d)
    (R : Fin 1 → upperTriangular d) (hR : IsUnit (R 0 : Matrix d d ℝ).det)
    (hturn : TurnsActiveRowsGatedSkip θ (R 0 : Matrix d d ℝ))
    (hw : ∃ v : d → ℝ, (∀ i, (v ᵥ* θ.read 0) (Sum.inl i) ≠ 0) ∧ LinearIndependent ℝ
      ![v ᵥ* (R 0 : Matrix d d ℝ), gatedBlock relu ((θ.read 0).submatrix id Sum.inl)
        ((θ.read 0).submatrix id Sum.inr) (θ.write 0) v]) :
    funDimSkipsOn (Arch.gated relu (rmsNorm 0) hid) (triSkips d 1) (θ, R)
        (learnedZeroDomain (Arch.gated relu (rmsNorm 0) hid) θ (fun ℓ => (R ℓ : Matrix d d ℝ))
          ∩ noKinkGateRMS θ)
        + ((Fintype.card d * (Fintype.card d - 1) / 2 + 2) + 2 * Fintype.card (hid 0))
      = Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut)
        + Fintype.card d * (Fintype.card d + 1) / 2 := by
  -- the set of the ranks contains its upper bound
  exact funDimSkipsOn_add_eq_ltz _ _ _ _
    (exists_jacobianRankSkips_tri_reglu_rmsNorm_zero θ hθ hd R hR hturn hw)
    (fun _ X hX => jacobianRankSkips_tri_add_le_reglu_rmsNorm_zero θ hθ hd R hR hturn hw X hX)

/-- **Theorem B.1 (iii) of the skips paper for `ε = 0`, "with equality", for one ReGLU block with
a hidden unit and an upper triangular learned skip:** for `d_in, d_out ≥ d ≥ 2`, at almost every
`(θ, A)`, `A` upper triangular, the functional dimension on the inputs at which no normalized row
vanishes and no gate sits at its kink is `P + d(d+1)/2 − (d(d−1)/2 + 2) − 2 d_hidden`. -/
theorem ae_funDimSkipsOn_tri_reglu_rmsNorm_zero [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut
      × (Fin 1 → upperTriangular d)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, funDimSkipsOn (Arch.gated relu (rmsNorm 0) hid) (triSkips d 1) p
        (learnedZeroDomain (Arch.gated relu (rmsNorm 0) hid) p.1
          (fun ℓ => (p.2 ℓ : Matrix d d ℝ)) ∩ noKinkGateRMS p.1)
        + ((Fintype.card d * (Fintype.card d - 1) / 2 + 2) + 2 * Fintype.card (hid 0))
      = Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut)
        + Fintype.card d * (Fintype.card d + 1) / 2 := by
  -- the conditions of the proof, an invertible skip, the turned rows for the skip `A`
  have hBt : BorelSpace (Fin 1 → upperTriangular d) := inferInstance
  have hμ : μ.IsAddHaarMeasure := inferInstance
  filter_upwards [ae_generic_tri_ltz μ
      (ae_oneBlockGenericReGLURMS (σ := relu) (ε := 0) Measure.addHaar hd hdIn hdOut),
    ae_turned_reglu_ltz hBt triLin_ltz _ triLin_one_ltz μ hμ hd] with p hp hturn
  exact funDimSkipsOn_tri_reglu_rmsNorm_zero p.1 hp.1 hd p.2 hp.2 hturn.1 hturn.2

/-- **Theorem B.1 (iii) of the skips paper, "with equality for […] ReGLU blocks", for one ReGLU
block with a hidden unit and an upper triangular learned skip, `ε = 0`:** at almost every
`(θ, A)`, `A` upper triangular, the functional dimension on the paper's inputs exceeds that of
the residual network with the weights `θ` by exactly `d(d+1)/2 − 1`. -/
theorem ae_funDimSkipsOn_tri_reglu_rmsNorm_zero_eq_residual_add [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut
      × (Fin 1 → upperTriangular d)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, funDimSkipsOn (Arch.gated relu (rmsNorm 0) hid) (triSkips d 1) p
        (learnedZeroDomain (Arch.gated relu (rmsNorm 0) hid) p.1
          (fun ℓ => (p.2 ℓ : Matrix d d ℝ)) ∩ noKinkGateRMS p.1)
      = funDim (Arch.gated relu (rmsNorm 0) hid) 1 p.1
        + (Fintype.card d * (Fintype.card d + 1) / 2 - 1) := by
  -- `fd + ((d(d−1)/2 + 2) + 2 s) = P + d(d+1)/2` and `fd₁ + ((d(d−1)/2 + 1) + 2 s) = P`
  have hBt : BorelSpace (Fin 1 → upperTriangular d) := inferInstance
  have hμ : μ.IsAddHaarMeasure := inferInstance
  filter_upwards [ae_funDimSkipsOn_tri_reglu_rmsNorm_zero μ hd hdIn hdOut,
    ae_fst_ltz hBt μ hμ
      (ae_funDim_reglu_oneBlock_residual_rmsNorm_zero Measure.addHaar hd hdIn hdOut)]
    with p hp hres
  have h1 := one_le_half_ltz hd
  generalize Fintype.card d * (Fintype.card d - 1) / 2 = a at hp hres
  generalize Fintype.card d * (Fintype.card d + 1) / 2 = b at hp h1 ⊢
  omega

end Skips
