import SkipsLean.OneBlock.ResidualRMSZeroKinds

/-!
# One residual block under pre-RMSNorm with `ε = 0`: the value of the functional dimension

Paper (skips paper), proof of Theorem B.1 (v), "The residual network": "So `K(θ)` is the direct
sum of these directions and `V_θ`, and the residual network has functional dimension
`P − dim CO(d_model) − dim V_θ`."

`OneBlock/ResidualRMSZeroGain.lean` has the half "at least". Here: the half "at most" (for `E` of
rank `d ≥ 1` and an analytic map `f` of the block, the directions of `CO(d)` and of `V_θ` are flat
for the residual network at the inputs at which no normalized row vanishes, and independent), and
the equality under the conditions of the proof. The functional dimension is `funDimOn` on
`residualZeroDomain`, as in that file.

The proofs were written and compiled by the reader of the nineteenth audit of the statements; the
statements were read by the coordinator.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

noncomputable section

variable {T d dIn dOut : Type*} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
private theorem hasDerivAt_mul_rzv {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
    {P : ℝ → Matrix m n ℝ} {Q : ℝ → Matrix n p ℝ} {P' P0 : Matrix m n ℝ} {Q' Q0 : Matrix n p ℝ}
    {τ : ℝ} (hP : HasDerivAt P P' τ) (hQ : HasDerivAt Q Q' τ) (hP0 : P τ = P0) (hQ0 : Q τ = Q0) :
    HasDerivAt (fun s => P s * Q s) (P' * Q0 + P0 * Q') τ := by
  subst hP0 hQ0
  refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => ?_
  have hPe : ∀ k, HasDerivAt (fun s => P s i k) (P' i k) τ := fun k =>
    hasDerivAt_pi.1 (hasDerivAt_pi.1 hP i) k
  have hQe : ∀ k, HasDerivAt (fun s => Q s k j) (Q' k j) τ := fun k =>
    hasDerivAt_pi.1 (hasDerivAt_pi.1 hQ k) j
  have h : HasDerivAt (fun s => ∑ k, P s i k * Q s k j)
      (∑ k, (P' i k * Q τ k j + P τ i k * Q' k j)) τ :=
    HasDerivAt.fun_sum (u := Finset.univ) (A := fun k s => P s i k * Q s k j)
      fun k _ => (hPe k).mul (hQe k)
  refine h.congr_deriv ?_
  simp only [Matrix.add_apply, Matrix.mul_apply, Finset.sum_add_distrib]

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
private theorem hasDerivAt_affine_rzv {m n : Type*} [Fintype m] [Fintype n]
    (M N : Matrix m n ℝ) : HasDerivAt (fun τ : ℝ => M + τ • N) N 0 := by
  have h := ((hasDerivAt_id (0 : ℝ)).smul_const N).const_add M
  rw [one_smul] at h
  exact h

/-! ### Check 3: the condition of `blockFlatSphere` is the derivative of the block along `ψ` -/

omit [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- For a differentiable `f`: along the line `(R + τ R', W + τ W')` of weights of the block, the
output `f(n R) W` of the block at the state `n` has, at `τ = 0`, the derivative
`𝐃f(n R)(n R') W + f(n R) W'`: the expression in the definition of `blockFlatSphere`. -/
private theorem hasDerivAt_block_rzv {r w : Type*} [Fintype r] [Fintype w]
    {f : Matrix T r ℝ → Matrix T w ℝ} (hf : Differentiable ℝ f) (n : Matrix T d ℝ)
    (R R' : Matrix d r ℝ) (W W' : Matrix w d ℝ) :
    HasDerivAt (fun τ : ℝ => f (n * (R + τ • R')) * (W + τ • W'))
      (fderiv ℝ f (n * R) (n * R') * W + f (n * R) * W') 0 := by
  have hR := hasDerivAt_mul_rzv (hasDerivAt_const (0 : ℝ) n) (hasDerivAt_affine_rzv R R')
    (P0 := n) (Q0 := R) rfl (by simp)
  have hF := (hf (n * R)).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hR (by simp)
  have hFW := hasDerivAt_mul_rzv hF (hasDerivAt_affine_rzv W W') (P0 := f (n * R)) (Q0 := W)
    (by simp) (by simp)
  have e : (fun s : ℝ => (f ∘ fun s => n * (R + s • R')) s * (W + s • W'))
      = fun τ : ℝ => f (n * (R + τ • R')) * (W + τ • W') := rfl
  rw [e, Matrix.zero_mul, zero_add] at hFW
  exact hFW


/-! ### Check 6: the other direction of the residual count (not a statement of the library)

The paper: "the residual network has functional dimension `P − dim CO(d) − dim V_θ`". The library
has `P ≤ funDimOn + (d(d−1)/2 + 1) + dim V_θ`. Here: the other inequality, for `E` of rank `d`,
and the equality under the hypotheses of the library's statement. The helpers repeat private
helpers of `OneBlock/ResidualRMSZeroGain.lean`. -/

omit [Fintype T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
private theorem mem_blockFlatSphere_rzv {A : Arch T d 1} {θ ψ : Params A dIn dOut}
    (hψ : ψ ∈ blockFlatSphere A θ) :
    ψ.E = 0 ∧ ψ.D = 0 ∧ ∀ n : Matrix T d ℝ, (∀ t, n t ⬝ᵥ n t = Fintype.card d) →
      fderiv ℝ (A.f 0) (n * θ.read 0) (n * ψ.read 0) * θ.write 0
        + A.f 0 (n * θ.read 0) * ψ.write 0 = 0 := by
  induction hψ using Submodule.span_induction with
  | mem x hx => exact hx
  | zero =>
    refine ⟨rfl, rfl, fun n _ => ?_⟩
    rw [Params.zero_read, Params.zero_write, Matrix.mul_zero, map_zero, Matrix.zero_mul,
      Matrix.mul_zero, add_zero]
  | add x y _ _ hx hy =>
    refine ⟨by rw [Params.add_E, hx.1, hy.1, add_zero], by rw [Params.add_D, hx.2.1, hy.2.1,
      add_zero], fun n hn => ?_⟩
    rw [Params.add_read, Params.add_write, Matrix.mul_add, map_add, Matrix.add_mul,
      Matrix.mul_add, add_add_add_comm, hx.2.2 n hn, hy.2.2 n hn, add_zero]
  | smul c x _ hx =>
    refine ⟨by rw [Params.smul_E, hx.1, smul_zero], by rw [Params.smul_D, hx.2.1, smul_zero],
      fun n hn => ?_⟩
    rw [Params.smul_read, Params.smul_write, Matrix.mul_smul, map_smul, Matrix.smul_mul,
      Matrix.mul_smul, ← smul_add, hx.2.2 n hn, smul_zero]

omit [Fintype T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
private theorem rmsRow_zero_dotProduct_self_rzv {v : d → ℝ} (hv : v ≠ 0) :
    rmsRow 0 v ⬝ᵥ rmsRow 0 v = Fintype.card d := by
  have hw2 : 0 < v ⬝ᵥ v := lt_of_le_of_ne (Finset.sum_nonneg fun i _ => mul_self_nonneg (v i))
    (Ne.symm (dotProduct_self_eq_zero.not.mpr hv))
  have hn : (0 : ℝ) < Fintype.card d := by
    obtain ⟨i, -⟩ := Function.ne_iff.mp hv
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨i⟩
  unfold rmsRow
  rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc, ← mul_inv,
    Real.mul_self_sqrt (add_nonneg (div_nonneg hw2.le hn.le) le_rfl), add_zero, inv_div,
    div_mul_cancel₀ _ hw2.ne']

omit [Fintype T] [Fintype dOut] in
private theorem eval_residual_rzv {A : Arch T d 1} (hA : A.χ = rmsNorm 0)
    (θ : Params A dIn dOut) (x : Matrix T dIn ℝ) :
    eval A 1 θ x
      = rmsNorm 0 (x * θ.E + A.f 0 (rmsNorm 0 (x * θ.E) * θ.read 0) * θ.write 0) * θ.D := by
  have h1 : (Fin.last 1 : Fin 2) = (0 : Fin 1).succ := rfl
  rw [eval, h1, hidden_succ, Fin.castSucc_zero, hidden_zero, hA]
  simp only [Pi.one_apply, Matrix.mul_one]

/-- A direction of `V_θ` is flat for the RESIDUAL network at every input at which no normalized
row vanishes. -/
private theorem blockFlatSphere_le_flatOn_residual_rzv {A : Arch T d 1} (hA : A.χ = rmsNorm 0)
    (hf : AnalyticOnNhd ℝ (A.f 0) Set.univ) (θ : Params A dIn dOut) :
    blockFlatSphere A θ ≤ flatOn A 1 θ (residualZeroDomain A θ) := by
  intro ψ hψ
  obtain ⟨hψE, hψD, hψn⟩ := mem_blockFlatSphere_rzv hψ
  rw [flatOn, Submodule.mem_iInf]
  intro x
  rw [Submodule.mem_iInf]
  intro hx
  rw [LinearMap.mem_ker]
  show fderiv ℝ (fun θ' : Params A dIn dOut => eval A 1 θ' x) θ ψ = 0
  by_cases hdx : DifferentiableAt ℝ (fun θ' : Params A dIn dOut => eval A 1 θ' x) θ
  swap
  · rw [fderiv_zero_of_not_differentiableAt hdx]
    rfl
  have h1 := hasDerivAt_eval_line (1 : Fin 1 → Matrix d d ℝ) θ ψ x hdx
  obtain ⟨n, hn⟩ : ∃ n, n = rmsNorm 0 (x * θ.E) := ⟨_, rfl⟩
  have hsph : ∀ t, n t ⬝ᵥ n t = Fintype.card d := by
    rw [hn]
    exact fun t => rmsRow_zero_dotProduct_self_rzv (hx.1 t)
  -- the block does not move to first order
  have hg : HasDerivAt (fun τ : ℝ => A.f 0 (n * (θ.read 0 + τ • ψ.read 0))
      * (θ.write 0 + τ • ψ.write 0)) 0 0 := by
    have h := hasDerivAt_block_rzv (fun z => (hf z trivial).differentiableAt) n (θ.read 0)
      (ψ.read 0) (θ.write 0) (ψ.write 0)
    rwa [hψn n hsph] at h
  -- neither does `h_1 = x E + block`
  have hh : HasDerivAt (fun τ : ℝ => x * θ.E + A.f 0 (n * (θ.read 0 + τ • ψ.read 0))
      * (θ.write 0 + τ • ψ.write 0)) 0 0 := by
    have h := hg.const_add (x * θ.E)
    exact h
  have hrows : ∀ t, (x * θ.E + A.f 0 (n * θ.read 0) * θ.write 0) t ≠ 0 := by
    rw [hn]
    exact hx.2
  have hN := (analyticAt_rmsNorm_zero _ hrows).differentiableAt.hasFDerivAt
    |>.comp_hasDerivAt_of_eq (0 : ℝ) hh (by simp)
  have h2 := hasDerivAt_mul_rzv hN (hasDerivAt_const (0 : ℝ) θ.D)
    (P0 := rmsNorm 0 (x * θ.E + A.f 0 (n * θ.read 0) * θ.write 0)) (Q0 := θ.D) (by simp) rfl
  have e : (fun τ : ℝ => eval A 1 (θ + τ • ψ) x) = fun τ => rmsNorm 0
      (x * θ.E + A.f 0 (n * (θ.read 0 + τ • ψ.read 0)) * (θ.write 0 + τ • ψ.write 0)) * θ.D := by
    funext τ
    rw [eval_residual_rzv hA, hn]
    simp only [Params.add_E, Params.smul_E, hψE, smul_zero, add_zero, Params.add_D,
      Params.smul_D, hψD, Params.add_read, Params.smul_read, Params.add_write,
      Params.smul_write]
  rw [e] at h1
  refine h1.unique (h2.congr_deriv ?_)
  rw [map_zero, Matrix.zero_mul, Matrix.mul_zero, add_zero]

private noncomputable def scaleDirLin_rzv {L : ℕ} {A : Arch T d L} (θ : Params A dIn dOut) :
    (Fin (L + 1) → ℝ) →ₗ[ℝ] Params A dIn dOut where
  toFun := scaleDir θ
  map_add' β β' := by
    refine Params.ext' ?_ (fun ℓ => ?_) (fun ℓ => ?_) ?_ <;>
      simp only [scaleDir, Params.add_E, Params.add_read, Params.add_write, Params.add_D,
        Pi.add_apply, add_smul, add_zero]
  map_smul' c β := by
    refine Params.ext' ?_ (fun ℓ => ?_) (fun ℓ => ?_) ?_ <;>
      simp only [scaleDir, Params.smul_E, Params.smul_read, Params.smul_write, Params.smul_D,
        Pi.smul_apply, smul_eq_mul, mul_smul, smul_zero, RingHom.id_apply]

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
private theorem eq_zero_of_mul_eq_zero_rzv {m n k : Type*} [Fintype n] (M : Matrix m n ℝ)
    (hM : M.rank = Fintype.card n) {X : Matrix n k ℝ} (h : M * X = 0) : X = 0 := by
  have hinj : Function.Injective M.mulVecLin := by
    rw [← LinearMap.ker_eq_bot, ← Submodule.finrank_eq_zero]
    have := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
    rw [Module.finrank_fintype_fun_eq_card] at this
    rw [Matrix.rank] at hM
    omega
  ext i j
  have hcol : M.mulVecLin (fun l => X l j) = M.mulVecLin 0 := by
    funext p
    have := congrFun (congrFun h p) j
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
  exact congrFun (hinj hcol) i

omit [Fintype T] [Fintype d] [Fintype dIn] [Fintype dOut] in
private theorem antisymm_add_smul_one_eq_zero_rzv [Nonempty d] {Y : Matrix d d ℝ}
    (hY : Yᵀ = -Y) {b : ℝ} (h : Y + b • (1 : Matrix d d ℝ) = 0) : Y = 0 ∧ b = 0 := by
  obtain ⟨k⟩ := ‹Nonempty d›
  have hYk : Y k k = 0 := by
    have := congrFun (congrFun hY k) k
    rw [transpose_apply, Matrix.neg_apply] at this
    linarith
  have hk := congrFun (congrFun h k) k
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one, hYk,
    zero_add, Matrix.zero_apply] at hk
  subst hk
  rw [zero_smul, add_zero] at h
  exact ⟨h, rfl⟩

omit [DecidableEq d] in
private theorem jacobianRank_add_finrank_flatOn_le_rzv {L : ℕ} {A : Arch T d L}
    {S : Fin L → Matrix d d ℝ} (θ : Params A dIn dOut) {U : Set (Matrix T dIn ℝ)} {n : ℕ}
    (X : Fin n → Matrix T dIn ℝ) (hX : ∀ i, X i ∈ U) :
    jacobianRank A S X θ + Module.finrank ℝ (flatOn A S θ U)
      ≤ Module.finrank ℝ (Params A dIn dOut) := by
  have hker : flatOn A S θ U ≤ LinearMap.ker (fderiv ℝ (evalBatch A S X) θ).toLinearMap := by
    intro η hη
    rw [LinearMap.mem_ker]
    by_cases hd : ∀ i, DifferentiableAt ℝ (fun θ' : Params A dIn dOut => eval A S θ' (X i)) θ
    · have h : fderiv ℝ (evalBatch A S X) θ =
          ContinuousLinearMap.pi fun i => fderiv ℝ (fun θ' => eval A S θ' (X i)) θ :=
        fderiv_pi hd
      show fderiv ℝ (evalBatch A S X) θ η = 0
      rw [h]
      funext i
      exact LinearMap.mem_ker.1
        ((Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hη (X i)) (hX i))
    · have hnd : ¬DifferentiableAt ℝ (evalBatch A S X) θ := fun h => hd (differentiableAt_pi.1 h)
      show fderiv ℝ (evalBatch A S X) θ η = 0
      rw [fderiv_zero_of_not_differentiableAt hnd]
      rfl
  have hrn := LinearMap.finrank_range_add_finrank_ker (fderiv ℝ (evalBatch A S X) θ).toLinearMap
  have hmono := Submodule.finrank_mono hker
  unfold jacobianRank
  omega

/-- **Theorem B.1 (v) of the skips paper, the residual network, the half "at most":** for `E` of
rank `d ≥ 1` and an analytic map `f` of the block, the directions of `CO(d)` and of `V_θ` are flat
for the residual network with `ε = 0` at the inputs at which no normalized row vanishes, and
independent, so the functional dimension on these inputs is at most
`P − (d(d−1)/2 + 1) − dim V_θ`. -/
theorem funDimOn_add_le_residual_rmsNorm_zero {A : Arch T d 1} [Nonempty d]
    (hA : A.χ = rmsNorm 0) (hf : AnalyticOnNhd ℝ (A.f 0) Set.univ) (θ : Params A dIn dOut)
    (hE : θ.E.rank = Fintype.card d) :
    funDimOn A 1 θ (residualZeroDomain A θ)
        + (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
        + Module.finrank ℝ (blockFlatSphere A θ)
      ≤ Module.finrank ℝ (Params A dIn dOut) := by
  let Φ : (antisymmetric d × ℝ) × blockFlatSphere A θ →ₗ[ℝ] Params A dIn dOut :=
    (((cobDirLin θ).comp (LinearMap.pi fun _ => (antisymmetric d).subtype)).coprod
      ((scaleDirLin_rzv θ).comp (LinearMap.pi fun _ => LinearMap.id))).coprod
      (blockFlatSphere A θ).subtype
  have hflat : LinearMap.range Φ ≤ flatOn A 1 θ (residualZeroDomain A θ) := by
    rintro _ ⟨p, rfl⟩
    rw [LinearMap.coprod_apply, LinearMap.coprod_apply]
    refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_
    · exact flat_le_flatOn θ _
        (cobDir_const_mem_flat_residual_rmsNorm_zero θ hA (p.1.1 : Matrix d d ℝ) p.1.1.2)
    · exact flat_le_flatOn θ _ (scaleDir_const_mem_flat_residual_rmsNorm_zero θ hA p.1.2)
    · exact blockFlatSphere_le_flatOn_residual_rzv hA hf θ p.2.2
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨⟨Y, c⟩, ψ⟩ hp
    rw [LinearMap.coprod_apply, LinearMap.coprod_apply] at hp
    have h : cobDir θ (fun _ => (Y : Matrix d d ℝ)) + scaleDir θ (fun _ => c)
        + (ψ : Params A dIn dOut) = 0 := hp
    obtain ⟨hψE, hψD, -⟩ := mem_blockFlatSphere_rzv ψ.2
    have hE0 : θ.E * (Y : Matrix d d ℝ) + c • θ.E + (ψ : Params A dIn dOut).E = 0 :=
      congrArg Params.E h
    have hR0 : -((Y : Matrix d d ℝ) * θ.read 0) + 0 + (ψ : Params A dIn dOut).read 0 = 0 :=
      congrArg (fun η => η.read 0) h
    have hW0 : θ.write 0 * (Y : Matrix d d ℝ) + c • θ.write 0
        + (ψ : Params A dIn dOut).write 0 = 0 :=
      congrArg (fun η => η.write 0) h
    rw [hψE, add_zero] at hE0
    have hE1 : θ.E * ((Y : Matrix d d ℝ) + c • 1) = 0 := by
      rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one]
      exact hE0
    obtain ⟨hY0, hc0⟩ :=
      antisymm_add_smul_one_eq_zero_rzv Y.2 (eq_zero_of_mul_eq_zero_rzv θ.E hE hE1)
    rw [hY0, Matrix.zero_mul, neg_zero, zero_add, zero_add] at hR0
    rw [hY0, hc0, Matrix.mul_zero, zero_smul, zero_add, zero_add] at hW0
    have hψ0 : ψ = 0 := by
      refine Subtype.ext (Params.ext' hψE (fun ℓ => ?_) (fun ℓ => ?_) hψD)
      · rw [Fin.fin_one_eq_zero ℓ, hR0]
        rfl
      · rw [Fin.fin_one_eq_zero ℓ, hW0]
        rfl
    exact Prod.ext (Prod.ext (Subtype.ext hY0) hc0) hψ0
  have hdim : Module.finrank ℝ ((antisymmetric d × ℝ) × blockFlatSphere A θ)
      = (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
        + Module.finrank ℝ (blockFlatSphere A θ) := by
    rw [Module.finrank_prod, Module.finrank_prod, finrank_antisymmetric, Module.finrank_self]
  have hrange := Submodule.finrank_mono hflat
  rw [LinearMap.finrank_range_of_inj hinj, hdim] at hrange
  -- `funDimOn` is the rank on some batch of inputs of `U`
  have hne : ({r : ℕ | ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ),
      (∀ i, X i ∈ residualZeroDomain A θ) ∧ r = jacobianRank A 1 X θ}).Nonempty :=
    ⟨_, 0, Fin.elim0, fun i => i.elim0, rfl⟩
  have hbd : BddAbove {r : ℕ | ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ),
      (∀ i, X i ∈ residualZeroDomain A θ) ∧ r = jacobianRank A 1 X θ} := by
    refine ⟨Module.finrank ℝ (Params A dIn dOut), ?_⟩
    rintro _ ⟨m, Y, -, rfl⟩
    exact jacobianRank_le_finrank θ Y
  obtain ⟨n, X, hX, hEq⟩ : ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ),
      (∀ i, X i ∈ residualZeroDomain A θ) ∧
        funDimOn A 1 θ (residualZeroDomain A θ) = jacobianRank A 1 X θ := Nat.sSup_mem hne hbd
  have hrn := jacobianRank_add_finrank_flatOn_le_rzv (S := 1) θ X hX
  rw [hEq]
  generalize Fintype.card d * (Fintype.card d - 1) / 2 = q at hrange ⊢
  omega

/-- **Theorem B.1 (v) of the skips paper, the residual network, the value:** under the conditions
of `finrank_le_funDimOn_residual_rmsNorm_zero` (`d ≥ 2`, `E` and `D` of rank `d`, one input `w`
with the rows of `w E` and of `g(w)` linearly independent for every token), the functional
dimension of the residual network with `ε = 0`, on the inputs at which no normalized row
vanishes, is `P − (d(d−1)/2 + 1) − dim V_θ`. -/
theorem funDimOn_residual_rmsNorm_zero_eq {A : Arch T d 1} [Nonempty T]
    (hA : A.χ = rmsNorm 0) (hd : 2 ≤ Fintype.card d)
    (hf : AnalyticOnNhd ℝ (A.f 0) Set.univ) (θ : Params A dIn dOut)
    (hE : θ.E.rank = Fintype.card d) (hD : θ.D.rank = Fintype.card d)
    (hw : ∃ w : Matrix T dIn ℝ, ∀ t, LinearIndependent ℝ
      ![(w * θ.E) t, (A.f 0 (rmsNorm 0 (w * θ.E) * θ.read 0) * θ.write 0) t]) :
    funDimOn A 1 θ (residualZeroDomain A θ)
        + (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
        + Module.finrank ℝ (blockFlatSphere A θ)
      = Module.finrank ℝ (Params A dIn dOut) := by
  have : Nonempty d := Fintype.card_pos_iff.1 (by omega)
  exact le_antisymm (funDimOn_add_le_residual_rmsNorm_zero hA hf θ hE)
    (finrank_le_funDimOn_residual_rmsNorm_zero hA hd hf θ hE hD hw)

end

end Skips
