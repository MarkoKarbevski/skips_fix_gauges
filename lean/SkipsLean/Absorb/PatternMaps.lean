import SkipsLean.Dimension.RescalingMlp
import SkipsLean.Dimension.GenericRank
import SkipsLean.Generic.Params

/-!
# The polynomial maps of the patterns of a ReLU network

Paper (absorb paper): proof of Proposition 4.7, Steps 1 and 2. "Step 1: patterns give polynomial
maps. A pattern on `Z` labels every unit, at every input of `Z`, active or inactive. Given a
pattern `π`, replace `ReLU(z)` in the network by `z` where `π` says active and by `0` where it
says inactive. The outputs on `Z` become a polynomial map `F^π_Z` of the weights. The pattern of
`θ` labels a unit active at an input if its argument there is positive, and inactive otherwise;
with this pattern, `F_Z(θ) = F^π_Z(θ)`." Step 2, for a skipless network of `L` blocks: "Its
pattern maps `F'^π_Z` do not change under a change of basis at each of its `L + 1` hidden states,
nor under the rescalings of its […] units. […] They are linearly independent when `E` and every
write have rank `d_model` and no read of a unit vanishes […]. So every `F'^π_Z` has rank at most
`P + 2 d_model n − (L + 1) d_model² − s − n` at every point", after "A polynomial map reaches its
largest rank on a nonempty open set, so the rank is at most `r` at every `θ`."

Here a pattern on one input labels every hidden unit of every block at every token
(`∀ ℓ, T → hid ℓ → Bool`). Replacing ReLU by the pattern gives a network in the frame of this
library: `Arch.masked π`, whose fixed map of block `ℓ` keeps the entries that `π` labels active
and sets the others to `0`. The weights are the same (`Params.toMasked`).

* `reluPattern S θ x`: the pattern of `θ` at the input `x`.
* `eval_relu_eq_eval_masked`: with its own pattern, the ReLU network is the network of the
  pattern, for any stream matrices (with or without skips).
* `maskedBatch S X π`: the map `F^π_Z` on a batch `X` with one pattern per input, as a map of the
  weights of the ReLU network; it is real-analytic.
* The rank bound for skipless networks, at every parameter: `rank ≤ P − (L + 1) d² − s`, for
  `d_in ≥ d ≥ 1` and blocks of at least `d` hidden units, `s = ∑_ℓ d_hidden^ℓ`.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]

/-- **The network of a pattern** (proof of Proposition 4.7, Step 1): block `ℓ` keeps the entry of
token `t` and hidden unit `j` if the pattern labels it active, and replaces it by `0` if not.
There is no normalization. -/
abbrev Arch.masked (π : ∀ ℓ : Fin L, T → hid ℓ → Bool) : Arch T d L where
  r := hid
  w := hid
  f ℓ M := Matrix.of fun t j => if π ℓ t j then M t j else 0
  χ := id

/-- The same weights, read as the parameters of the network of a pattern. -/
def Params.toMasked {σ : ℝ → ℝ} (π : ∀ ℓ : Fin L, T → hid ℓ → Bool)
    (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) :
    Params (Arch.masked (T := T) (d := d) π) dIn dOut where
  E := θ.E
  read := θ.read
  write := θ.write
  D := θ.D

/-- **The pattern of `θ` at the input `x`** (proof of Proposition 4.7, Step 1): a unit is labelled
active at a token if its argument there is positive, and inactive otherwise. -/
noncomputable def reluPattern (S : Fin L → Matrix d d ℝ)
    (θ : Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut) (x : Matrix T dIn ℝ) :
    ∀ ℓ : Fin L, T → hid ℓ → Bool :=
  fun ℓ t j => decide (0 < (hidden (Arch.mlp relu id hid) S θ x ℓ.castSucc * θ.read ℓ) t j)

/-- Helper: `relu z` is `z` if `z > 0` and `0` otherwise. -/
private theorem relu_eq_ite_pat (z : ℝ) : (if decide (0 < z) then z else 0) = relu z := by
  by_cases hz : 0 < z
  · simp only [decide_eq_true hz, ite_true, relu, max_eq_left hz.le]
  · simp only [decide_eq_false hz, Bool.false_eq_true, ite_false, relu,
      max_eq_right (not_lt.1 hz)]

omit [Fintype T] [DecidableEq d] [Fintype dOut] in
/-- **Proof of Proposition 4.7, Step 1, "with this pattern, `F_Z(θ) = F^π_Z(θ)`", at one input:**
a ReLU network without normalization, with any stream matrices, is the network of its own
pattern. -/
theorem eval_relu_eq_eval_masked (S : Fin L → Matrix d d ℝ)
    (θ : Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut) (x : Matrix T dIn ℝ) :
    eval (Arch.mlp relu id hid) S θ x
      = eval (Arch.masked (reluPattern S θ x)) S (θ.toMasked (reluPattern S θ x)) x := by
  -- the hidden states agree, by induction along the network
  have hh : ∀ k : Fin (L + 1),
      hidden (Arch.masked (reluPattern S θ x)) S (θ.toMasked (reluPattern S θ x)) x k
        = hidden (Arch.mlp relu id hid) S θ x k := by
    intro k
    induction k using Fin.induction with
    | zero => rw [hidden_zero, hidden_zero]; rfl
    | succ ℓ ih =>
      -- the stream term is the same; in block `ℓ`, `relu z = z` where the pattern says active
      -- (`z > 0`) and `relu z = 0` where it says inactive
      rw [hidden_succ, hidden_succ, ih]
      congr 2
      ext t j
      exact relu_eq_ite_pat _
  -- hence the outputs agree
  rw [eval, eval, hh]
  rfl

/-- **The map `F^π_Z` of the proof of Proposition 4.7:** the outputs on the batch `X` of the
networks of the patterns `π i`, one pattern per input, as a map of the weights. -/
noncomputable def maskedBatch (S : Fin L → Matrix d d ℝ) {n : ℕ}
    (X : Fin n → Matrix T dIn ℝ)
    (π : Fin n → ∀ ℓ : Fin L, T → hid ℓ → Bool)
    (θ : Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut) : Fin n → Matrix T dOut ℝ :=
  fun i => eval (Arch.masked (π i)) S (θ.toMasked (π i)) (X i)

omit [Fintype T] [DecidableEq d] [Fintype dOut] in
/-- On a batch, a ReLU network is the map `F^π_Z` of its own patterns. -/
theorem evalBatch_relu_eq_maskedBatch (S : Fin L → Matrix d d ℝ) {n : ℕ}
    (X : Fin n → Matrix T dIn ℝ)
    (θ : Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut) :
    evalBatch (Arch.mlp relu id hid) S X θ
      = maskedBatch S X (fun i => reluPattern S θ (X i)) θ := by
  -- input by input, `eval_relu_eq_eval_masked`
  funext i
  exact eval_relu_eq_eval_masked S θ (X i)

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the fixed map of block `ℓ` of the network of a pattern is linear. -/
private def maskLin_pat (π : ∀ ℓ : Fin L, T → hid ℓ → Bool) (ℓ : Fin L) :
    Matrix T (hid ℓ) ℝ →ₗ[ℝ] Matrix T (hid ℓ) ℝ where
  toFun M := Matrix.of fun t j => if π ℓ t j then M t j else 0
  map_add' M N := by
    ext t j
    simp only [Matrix.of_apply, Matrix.add_apply]
    split_ifs <;> simp
  map_smul' c M := by
    ext t j
    simp only [Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> simp

omit [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the fixed map of block `ℓ` of the network of a pattern is analytic (it is linear). -/
private theorem analyticOnNhd_mask_pat (π : ∀ ℓ : Fin L, T → hid ℓ → Bool) (ℓ : Fin L) :
    AnalyticOnNhd ℝ ((Arch.masked (T := T) (d := d) π).f ℓ) Set.univ := by
  show AnalyticOnNhd ℝ (maskLin_pat π ℓ) Set.univ
  rw [← LinearMap.coe_toContinuousLinearMap' (maskLin_pat π ℓ)]
  exact (LinearMap.toContinuousLinearMap (maskLin_pat π ℓ)).analyticOnNhd _

/-- Helper: `θ ↦ θ.toMasked π`, as a continuous linear map. -/
private noncomputable def toMaskedCLM_pat (π : ∀ ℓ : Fin L, T → hid ℓ → Bool) :
    Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut →L[ℝ]
      Params (Arch.masked (T := T) (d := d) π) dIn dOut :=
  LinearMap.toContinuousLinearMap
    { toFun := fun θ => θ.toMasked π, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }

omit [DecidableEq d] in
/-- Helper: the output of the network of a pattern at one input is analytic in its weights. -/
private theorem analyticOnNhd_eval_masked_pat (S : Fin L → Matrix d d ℝ)
    (π : ∀ ℓ : Fin L, T → hid ℓ → Bool) (x : Matrix T dIn ℝ) :
    AnalyticOnNhd ℝ (fun θ' : Params (Arch.masked (T := T) (d := d) π) dIn dOut =>
      eval (Arch.masked π) S θ' x) Set.univ :=
  analyticOnNhd_eval_params (Arch.masked π) S (analyticOnNhd_mask_pat π) analyticOnNhd_id x

omit [DecidableEq d] in
/-- **Proof of Proposition 4.7, Step 1, "a polynomial map of the weights":** `F^π_Z` is
real-analytic in the weights. -/
theorem analyticOnNhd_maskedBatch (S : Fin L → Matrix d d ℝ) {n : ℕ}
    (X : Fin n → Matrix T dIn ℝ) (π : Fin n → ∀ ℓ : Fin L, T → hid ℓ → Bool) :
    AnalyticOnNhd ℝ
      (maskedBatch (d := d) (dOut := dOut) S X π :
        Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut → Fin n → Matrix T dOut ℝ)
      Set.univ := by
  -- input by input: the output of the network of `π i` (analytic) after the linear map
  -- `θ ↦ θ.toMasked (π i)`
  refine AnalyticOnNhd.pi fun i => ?_
  have hc := (analyticOnNhd_eval_masked_pat (dOut := dOut) S (π i) (X i)).comp
    ((toMaskedCLM_pat (π i)).analyticOnNhd Set.univ) (Set.mapsTo_univ _ _)
  exact hc

omit [Fintype T] [DecidableEq d] [Fintype dOut] in
/-- Helper (Step 2, the rescalings of the units): the network of a pattern keeps its function when
the read column of every hidden unit `i` is multiplied by `c_i ≠ 0` and its write row by
`c_i⁻¹`, since its fixed map is linear in each column. -/
private theorem eval_rescale_masked_pat (π : ∀ ℓ : Fin L, T → hid ℓ → Bool)
    (θ θ' : Params (Arch.masked (T := T) (d := d) π) dIn dOut)
    (c : ∀ ℓ, hid ℓ → ℝ) (hc : ∀ ℓ i, c ℓ i ≠ 0) (hE : θ'.E = θ.E) (hD : θ'.D = θ.D)
    (hr : ∀ ℓ a i, θ'.read ℓ a i = c ℓ i * θ.read ℓ a i)
    (hw : ∀ ℓ i a, θ'.write ℓ i a = (c ℓ i)⁻¹ * θ.write ℓ i a)
    (S : Fin L → Matrix d d ℝ) (x : Matrix T dIn ℝ) :
    eval (Arch.masked π) S θ' x = eval (Arch.masked π) S θ x := by
  -- the hidden states of `θ'` and `θ` agree, by induction along the network
  have hh : ∀ k : Fin (L + 1),
      hidden (Arch.masked π) S θ' x k = hidden (Arch.masked π) S θ x k := by
    intro k
    induction k using Fin.induction with
    | zero => rw [hidden_zero, hidden_zero, hE]
    | succ ℓ ih =>
      rw [hidden_succ, hidden_succ, ih]
      congr 1
      set h := hidden (Arch.masked π) S θ x ℓ.castSucc
      -- the argument of hidden unit `i` is multiplied by `c_i`
      have hu : ∀ t i, (h * θ'.read ℓ) t i = c ℓ i * (h * θ.read ℓ) t i := by
        intro t i
        rw [Matrix.mul_apply, Matrix.mul_apply, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hr]
        ring
      -- so hidden unit `i` contributes `(c_i z_i or 0) a_i / c_i = (z_i or 0) a_i`
      ext t a
      rw [Matrix.mul_apply, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      show (if π ℓ t i then (h * θ'.read ℓ) t i else 0) * θ'.write ℓ i a
        = (if π ℓ t i then (h * θ.read ℓ) t i else 0) * θ.write ℓ i a
      rw [hu, hw]
      split_ifs
      · rw [mul_mul_mul_comm, mul_inv_cancel₀ (hc ℓ i), one_mul]
      · rw [zero_mul, zero_mul]
  -- hence the outputs agree
  rw [eval, eval, hh, hD]

/-- Helper (copy of a private helper of `RescalingMlp.lean`): `τ ↦ e^{τ a} b` has derivative
`a b` at `τ = 0`. -/
private theorem hasDerivAt_exp_mul_const_pat (a b : ℝ) :
    HasDerivAt (fun τ : ℝ => Real.exp (τ * a) * b) (a * b) 0 := by
  have h := ((hasDerivAt_id (0 : ℝ)).mul_const a).exp.mul_const b
  simpa using h

/-- Helper (copy of the private `rescaleCurveMlp` of `RescalingMlp.lean`): the read column of
hidden unit `i` of block `ℓ` multiplied by `e^{τ α ℓ i}`, its write row by `e^{-τ k α ℓ i}`. -/
private noncomputable def rescaleCurve_pat (k : ℕ)
    (θ : Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut) (α : ∀ ℓ, hid ℓ → ℝ) (τ : ℝ) :
    Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut where
  E := θ.E
  read ℓ := Matrix.of fun a i => Real.exp (τ * α ℓ i) * θ.read ℓ a i
  write ℓ := Matrix.of fun i a => Real.exp (τ * -((k : ℝ) * α ℓ i)) * θ.write ℓ i a
  D := θ.D

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the curve passes through `θ` at `τ = 0`. -/
private theorem rescaleCurve_zero_pat (k : ℕ)
    (θ : Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut) (α : ∀ ℓ, hid ℓ → ℝ) :
    rescaleCurve_pat k θ α 0 = θ := by
  apply Params.ext'
  · rfl
  · intro ℓ
    ext a i
    simp [rescaleCurve_pat]
  · intro ℓ
    ext i a
    simp [rescaleCurve_pat]
  · rfl

omit [Fintype T] [DecidableEq d] in
/-- Helper: the curve has velocity `rescaleDirMlp k θ α` at `τ = 0` (entry by entry, through the
linear equivalence of the parameters with the tuples of their components). -/
private theorem hasDerivAt_rescaleCurve_pat (k : ℕ)
    (θ : Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut) (α : ∀ ℓ, hid ℓ → ℝ) :
    HasDerivAt (rescaleCurve_pat k θ α) (rescaleDirMlp k θ α) 0 := by
  have hprod : HasDerivAt (fun τ : ℝ => Params.linearEquivProd (rescaleCurve_pat k θ α τ))
      (Params.linearEquivProd (rescaleDirMlp k θ α)) 0 := by
    refine HasDerivAt.prodMk ?_ (HasDerivAt.prodMk ?_ (HasDerivAt.prodMk ?_ ?_))
    · exact hasDerivAt_const (0 : ℝ) θ.E
    · exact hasDerivAt_pi.2 fun ℓ => hasDerivAt_pi.2 fun a => hasDerivAt_pi.2 fun i =>
        hasDerivAt_exp_mul_const_pat (α ℓ i) (θ.read ℓ a i)
    · exact hasDerivAt_pi.2 fun ℓ => hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun a =>
        hasDerivAt_exp_mul_const_pat (-((k : ℝ) * α ℓ i)) (θ.write ℓ i a)
    · exact hasDerivAt_const (0 : ℝ) θ.D
  exact (LinearMap.toContinuousLinearMap
    (Params.linearEquivProd (A := Arch.mlp (T := T) (d := d) relu id hid) (dIn := dIn)
      (dOut := dOut)).symm.toLinearMap).hasFDerivAt.comp_hasDerivAt 0 hprod

omit [DecidableEq d] in
/-- Helper (Step 2, the rescalings of the units): the direction `rescaleDirMlp 1 θ α`, read as
weights of the network of a pattern, is flat there. -/
private theorem rescale_mem_flat_masked_pat (π : ∀ ℓ : Fin L, T → hid ℓ → Bool)
    (θ : Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut) (α : ∀ ℓ, hid ℓ → ℝ)
    (S : Fin L → Matrix d d ℝ) :
    (rescaleDirMlp 1 θ α).toMasked π ∈ flat (Arch.masked π) S (θ.toMasked π) := by
  -- the curve `τ ↦ c_i = e^{τ α ℓ i}` passes through `θ.toMasked π` with that velocity, and
  -- keeps the function of the network of `π`
  refine mem_flat_of_hasDerivAt' (θ.toMasked π) (fun τ => (rescaleCurve_pat 1 θ α τ).toMasked π)
    ((rescaleDirMlp 1 θ α).toMasked π) ?_ ?_ (Filter.Eventually.of_forall fun τ x => ?_)
  · exact (toMaskedCLM_pat π).hasFDerivAt.comp_hasDerivAt 0 (hasDerivAt_rescaleCurve_pat 1 θ α)
  · show (rescaleCurve_pat 1 θ α 0).toMasked π = θ.toMasked π
    rw [rescaleCurve_zero_pat]
  · refine eval_rescale_masked_pat π (θ.toMasked π) ((rescaleCurve_pat 1 θ α τ).toMasked π)
      (fun ℓ i => Real.exp (τ * α ℓ i))
      (fun _ _ => (Real.exp_pos _).ne') rfl rfl (fun _ _ _ => rfl) (fun ℓ i a => ?_) S x
    show Real.exp (τ * -(((1 : ℕ) : ℝ) * α ℓ i)) * θ.write ℓ i a
      = (Real.exp (τ * α ℓ i))⁻¹ * θ.write ℓ i a
    rw [Nat.cast_one, one_mul, mul_neg, Real.exp_neg]

omit [DecidableEq d] in
/-- Helper (the chain rule through `θ ↦ θ.toMasked (π i)`): component `i` of the derivative of
`F^π_Z` at `θ` along `η` is the derivative of the output of the network of `π i` at
`θ.toMasked (π i)` along `η.toMasked (π i)`. -/
private theorem fderiv_maskedBatch_apply_pat (S : Fin L → Matrix d d ℝ) {n : ℕ}
    (X : Fin n → Matrix T dIn ℝ) (π : Fin n → ∀ ℓ : Fin L, T → hid ℓ → Bool)
    (θ η : Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut) (i : Fin n) :
    fderiv ℝ (maskedBatch S X π) θ η i =
      fderiv ℝ (fun θ' : Params (Arch.masked (T := T) (d := d) (π i)) dIn dOut =>
        eval (Arch.masked (π i)) S θ' (X i)) (θ.toMasked (π i)) (η.toMasked (π i)) := by
  -- each component is the output of the network of `π i` after the linear map `toMasked`
  have hc : ∀ j, HasFDerivAt (fun θ' => maskedBatch S X π θ' j)
      ((fderiv ℝ (fun θ' : Params (Arch.masked (T := T) (d := d) (π j)) dIn dOut =>
        eval (Arch.masked (π j)) S θ' (X j)) (θ.toMasked (π j))).comp
          (toMaskedCLM_pat (π j))) θ := by
    intro j
    have hg := ((analyticOnNhd_eval_masked_pat (dOut := dOut) S (π j) (X j))
      (θ.toMasked (π j)) (Set.mem_univ _)).differentiableAt.hasFDerivAt
    exact hg.comp θ (toMaskedCLM_pat (π j)).hasFDerivAt
  have hG : HasFDerivAt (maskedBatch S X π)
      (ContinuousLinearMap.pi fun j =>
        (fderiv ℝ (fun θ' : Params (Arch.masked (T := T) (d := d) (π j)) dIn dOut =>
          eval (Arch.masked (π j)) S θ' (X j)) (θ.toMasked (π j))).comp
            (toMaskedCLM_pat (π j))) θ :=
    hasFDerivAt_pi.2 hc
  rw [hG.fderiv]
  rfl

omit [DecidableEq d] in
/-- Helper: a direction whose images under every `toMasked (π i)` are flat for the network of
`π i` is in the kernel of the derivative of `F^π_Z`. -/
private theorem fderiv_maskedBatch_eq_zero_pat (S : Fin L → Matrix d d ℝ) {n : ℕ}
    (X : Fin n → Matrix T dIn ℝ) (π : Fin n → ∀ ℓ : Fin L, T → hid ℓ → Bool)
    (θ η : Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut)
    (hη : ∀ i, η.toMasked (π i) ∈ flat (Arch.masked (π i)) S (θ.toMasked (π i))) :
    fderiv ℝ (maskedBatch S X π) θ η = 0 := by
  funext i
  rw [fderiv_maskedBatch_apply_pat, Pi.zero_apply]
  have h := (Submodule.mem_iInf _).1 (hη i) (X i)
  exact LinearMap.mem_ker.1 h

omit [Fintype T] [DecidableEq d] in
/-- Helper (copy of the private `rescaleDirMlpLin` of `RescalingMlp.lean`):
`α ↦ rescaleDirMlp k θ α` is linear. -/
private noncomputable def rescaleDirLin_pat (k : ℕ)
    (θ : Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut) :
    (∀ ℓ, hid ℓ → ℝ) →ₗ[ℝ] Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut where
  toFun := rescaleDirMlp k θ
  map_add' α β := by
    apply Params.ext'
    · simp [rescaleDirMlp]
    · intro ℓ
      ext a i
      simp only [rescaleDirMlp, Pi.add_apply, Params.add_read, Matrix.add_apply, Matrix.of_apply]
      ring
    · intro ℓ
      ext i a
      simp only [rescaleDirMlp, Pi.add_apply, Params.add_write, Matrix.add_apply, Matrix.of_apply]
      ring
    · simp [rescaleDirMlp]
  map_smul' c α := by
    apply Params.ext'
    · simp [rescaleDirMlp]
    · intro ℓ
      ext a i
      simp only [rescaleDirMlp, Pi.smul_apply, Params.smul_read, Matrix.smul_apply,
        Matrix.of_apply, smul_eq_mul, RingHom.id_apply]
      ring
    · intro ℓ
      ext i a
      simp only [rescaleDirMlp, Pi.smul_apply, Params.smul_write, Matrix.smul_apply,
        Matrix.of_apply, smul_eq_mul, RingHom.id_apply]
      ring
    · simp [rescaleDirMlp]

omit [Fintype T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (copy of a private helper of `RescalingMlp.lean`): the pairs `(Y, α)` form a space of
dimension `(L + 1) d² + s`. -/
private theorem finrank_dirDomain_pat :
    Module.finrank ℝ ((Fin (L + 1) → Matrix d d ℝ) × (∀ ℓ, hid ℓ → ℝ)) =
      (L + 1) * Fintype.card d ^ 2 + ∑ ℓ, Fintype.card (hid ℓ) := by
  rw [Module.finrank_prod, Module.finrank_pi_fintype, Module.finrank_matrix,
    Module.finrank_pi_fintype]
  simp [sq, Module.finrank_fintype_fun_eq_card]

/-- Helper (Step 2, the bound at a generic parameter): if `E` and every write have rank `d` and
no column of a read vanishes, the directions `cobDir θ Y + rescaleDirMlp 1 θ α` span a space of
dimension `(L + 1) d² + s` in the kernel of the derivative of `F'^π_Z` at `θ`; rank–nullity. -/
private theorem finrank_range_add_le_of_generic_pat {n : ℕ}
    (X : Fin n → Matrix T dIn ℝ) (π : Fin n → ∀ ℓ : Fin L, T → hid ℓ → Bool)
    (θ : Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d) (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d)
    (hc : ∀ ℓ i, (fun a => θ.read ℓ a i) ≠ 0) :
    Module.finrank ℝ (LinearMap.range
        (fderiv ℝ (maskedBatch (d := d) (dOut := dOut) 0 X π) θ).toLinearMap)
        + ((L + 1) * Fintype.card d ^ 2 + ∑ ℓ, Fintype.card (hid ℓ))
      ≤ Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut) := by
  -- the linear map `(Y, α) ↦ cobDir θ Y + rescaleDirMlp 1 θ α`
  let Φ := (cobDirLin θ).coprod (rescaleDirLin_pat 1 θ)
  -- its directions are in the kernel: for every pattern `π i`, the change of basis and the
  -- rescaling keep the network of `π i`
  have hV : LinearMap.range Φ ≤
      LinearMap.ker (fderiv ℝ (maskedBatch (d := d) (dOut := dOut) 0 X π) θ).toLinearMap := by
    rintro _ ⟨p, rfl⟩
    rw [LinearMap.mem_ker]
    refine fderiv_maskedBatch_eq_zero_pat 0 X π θ _ fun i => ?_
    show cobDir (θ.toMasked (π i)) p.1 + (rescaleDirMlp 1 θ p.2).toMasked (π i) ∈ _
    exact Submodule.add_mem _ (cobDir_mem_flat_skipless' (θ.toMasked (π i)) rfl p.1)
      (rescale_mem_flat_masked_pat (π i) θ p.2 0)
  -- it is injective (Lemma B.1), so its range has dimension `(L + 1) d² + s`
  have hinj : Function.Injective Φ := by
    intro p q hpq
    rw [LinearMap.coprod_apply, LinearMap.coprod_apply] at hpq
    exact cobDir_add_rescaleDirMlp_injective 1 θ hE hw hc hpq
  have h1 := LinearMap.finrank_range_add_finrank_ker
    (fderiv ℝ (maskedBatch (d := d) (dOut := dOut) 0 X π) θ).toLinearMap
  have h2 := Submodule.finrank_mono hV
  rw [LinearMap.finrank_range_of_inj hinj, finrank_dirDomain_pat] at h2
  omega

/-- **Proof of Proposition 4.7, Step 2, for a skipless network:** for `d_in ≥ d ≥ 1` and blocks
of at least `d` hidden units, the Jacobian of every pattern map `F'^π_Z` of the skipless network
has rank at most `P − (L + 1) d² − s` at every parameter, with `s` the number of hidden units. -/
theorem finrank_range_fderiv_maskedBatch_skipless_add_le [Nonempty d]
    (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) {n : ℕ}
    (X : Fin n → Matrix T dIn ℝ) (π : Fin n → ∀ ℓ : Fin L, T → hid ℓ → Bool)
    (θ : Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut) :
    Module.finrank ℝ (LinearMap.range
        (fderiv ℝ (maskedBatch (d := d) (dOut := dOut) 0 X π) θ).toLinearMap)
        + ((L + 1) * Fintype.card d ^ 2 + ∑ ℓ, Fintype.card (hid ℓ))
      ≤ Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut) := by
  -- `G = F'^π_Z` is analytic, so its derivative is continuous in the parameters
  have hGa := analyticOnNhd_maskedBatch (dOut := dOut) (hid := hid) (0 : Fin L → Matrix d d ℝ) X π
  have hJ := continuousOn_univ.mp hGa.fderiv.continuousOn
  -- `r` directions `v k` whose images at `θ` are linearly independent, `r` the rank at `θ`
  set r := Module.finrank ℝ (LinearMap.range
    (fderiv ℝ (maskedBatch (d := d) (dOut := dOut) 0 X π) θ).toLinearMap)
  let b := Module.finBasis ℝ
    (LinearMap.range (fderiv ℝ (maskedBatch (d := d) (dOut := dOut) 0 X π) θ).toLinearMap)
  have hb : ∀ k, ∃ v, fderiv ℝ (maskedBatch (d := d) (dOut := dOut) 0 X π) θ v
      = (b k : Fin n → Matrix T dOut ℝ) := fun k => LinearMap.mem_range.1 (b k).2
  choose v hv using hb
  have hli0 : LinearIndependent ℝ
      (fun k => fderiv ℝ (maskedBatch (d := d) (dOut := dOut) 0 X π) θ (v k)) := by
    have hl := b.linearIndependent.map' (LinearMap.range _).subtype (Submodule.ker_subtype _)
    convert hl using 1
    funext k
    exact hv k
  -- "a polynomial map reaches its largest rank on a nonempty open set": the images of the `v k`
  -- stay linearly independent on an open set `U` that contains `θ`
  let U := {θ' | LinearIndependent ℝ
    (fun k => fderiv ℝ (maskedBatch (d := d) (dOut := dOut) 0 X π) θ' (v k))}
  have hU : IsOpen U := isOpen_setOfPred_linearIndependent.preimage
    (continuous_pi fun k => hJ.clm_apply continuous_const)
  -- `U` has positive Haar measure, so it contains a generic parameter `θ'`
  let μ : Measure (Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut) := Measure.addHaar
  have hμU : μ U ≠ 0 := hU.measure_ne_zero μ ⟨θ, hli0⟩
  have hae := (ae_rank_E_write μ hdIn hhid).and (ae_read_col_ne_zero μ)
  obtain ⟨θ', hθ'U, hθ'⟩ :=
    Measure.exists_mem_of_measure_ne_zero_of_ae hμU (ae_restrict_of_ae hae)
  -- at `θ'` the rank is at least `r`, and at most `P - (L + 1) d² - s`
  have h1 : r ≤ Module.finrank ℝ (LinearMap.range
      (fderiv ℝ (maskedBatch (d := d) (dOut := dOut) 0 X π) θ').toLinearMap) := by
    calc r = Fintype.card (Fin r) := (Fintype.card_fin r).symm
      _ = Module.finrank ℝ (Submodule.span ℝ (Set.range
          (fun k => fderiv ℝ (maskedBatch (d := d) (dOut := dOut) 0 X π) θ' (v k)))) :=
        (finrank_span_eq_card hθ'U).symm
      _ ≤ _ := Submodule.finrank_mono
        (Submodule.span_le.2 (by rintro _ ⟨k, rfl⟩; exact ⟨_, rfl⟩))
  have h2 := finrank_range_add_le_of_generic_pat X π θ' hθ'.1.1 hθ'.1.2 hθ'.2
  omega

end Skips
