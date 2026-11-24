import SkipsLean.Generic.LevelSetOrbit
import SkipsLean.Generic.Params
import SkipsLean.Dimension.GenericRank
import SkipsLean.Depth.Tanh
import SkipsLean.Depth.TanhRMS
import SkipsLean.Depth.GeluGatedTheorem

/-!
# Local identifiability up to the changes of basis

Paper (dimension paper): Definition 4.5, Proposition 4.6 and Corollary 5.3.

"Definition 4.5 (Identifiability up to symmetries). A network is identifiable up to its symmetries
at `θ` if every `θ'` with `F_{θ'} = F_θ` is the image of `θ` under a symmetry: a change of basis of
Proposition 3.2, a symmetry inside a block, or a composition of these. It is locally identifiable at
`θ` if this holds for every `θ'` in some neighborhood of `θ`."

"Proposition 4.6 (The equality condition and local identifiability). Let the blocks be tanh, GELU,
SwiGLU, GeGLU or attention blocks, without normalization or under pre-RMSNorm. A network satisfies
the equality condition if and only if, at generic parameters, it is locally identifiable up to its
symmetries. Every symmetry that is needed is then close to the identity."

"Corollary 5.3 (Local identifiability). Without normalization or under pre-RMSNorm with `ε > 0`, in
the cases of Theorem 5.2, let `θ` be generic parameters. Every `θ'` near `θ` with the same function
is obtained from `θ` by matrices `G_0, …, G_L ∈ 𝒢` close to the identity, one per hidden state, as
in Proposition 3.2, and for SwiGLU and GeGLU blocks by a rescaling of the value of each hidden
unit, close to 1."

Stated here, for networks without skip connections whose blocks have no symmetries inside
(`s = 0`: tanh and GELU blocks):

* The direction of Proposition 4.6 from the equality condition to local identifiability, at one
  parameter: for real-analytic blocks, if `E` and the writes have rank `d` and the functional
  dimension at `θ` is `P − (L+1) d²` (without normalization), resp. `P − (L+1) d(d−1)/2` (under
  pre-RMSNorm with `ε > 0`), then every `θ'` near `θ` with the same function is `θ.cob G G` with
  invertible (resp. orthogonal) `G_0, …, G_L` near the identity: for every neighborhood `V` of the
  identity there is a neighborhood `U` of `θ`.
* Corollary 5.3 for tanh blocks without normalization and for tanh and GELU blocks under
  pre-RMSNorm with `ε > 0`: this holds at almost every parameter.

Not stated here: the converse direction of Proposition 4.6 (it uses Sard's theorem), the blocks
with symmetries inside (SwiGLU, GeGLU, attention), and networks with skip connections.
`θ.cob G G` is the change of basis of Proposition 3.2 (`Symmetry/ChangeOfBasis.lean`): `E G_0`,
`G_{ℓ−1}⁻¹ W_read^ℓ`, `W_write^ℓ G_ℓ`, `G_L⁻¹ D`.
-/

namespace Skips

open Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]

/-- The invertible matrix `exp Y`, with inverse `exp (-Y)`. -/
private noncomputable def expGL_li (Y : Matrix d d ℝ) : GL d ℝ where
  val := NormedSpace.exp Y
  inv := NormedSpace.exp (-Y)
  val_inv := by
    rw [← Matrix.exp_add_of_commute _ _ (Commute.refl Y).neg_right, add_neg_cancel,
      NormedSpace.exp_zero]
  inv_val := by
    rw [← Matrix.exp_add_of_commute _ _ (Commute.refl Y).neg_left, neg_add_cancel,
      NormedSpace.exp_zero]

/-- The matrix of `expGL_li Y` is `exp Y`. -/
private theorem coe_expGL_li (Y : Matrix d d ℝ) :
    (expGL_li Y : Matrix d d ℝ) = NormedSpace.exp Y := rfl

/-- The matrix of the inverse of `expGL_li Y` is `exp (-Y)`. -/
private theorem coe_expGL_li_inv (Y : Matrix d d ℝ) :
    (↑(expGL_li Y)⁻¹ : Matrix d d ℝ) = NormedSpace.exp (-Y) := rfl

/-- For antisymmetric `Y`, `exp Y` is orthogonal: `(exp Y)ᵀ = exp Yᵀ = exp (-Y)`. -/
private theorem exp_mem_orthogonalGroup_li {Y : Matrix d d ℝ} (hY : Yᵀ = -Y) :
    NormedSpace.exp Y ∈ Matrix.orthogonalGroup d ℝ := by
  rw [Matrix.mem_orthogonalGroup_iff', ← Matrix.exp_transpose, hY]
  exact (expGL_li Y).inv_val

-- As in Mathlib's `MatrixExponential.lean`: without this option the instances of the operator
-- norm (e.g. `CompleteSpace`) are not found.
set_option backward.isDefEq.respectTransparency false in
/-- The matrix exponential is strictly differentiable at `0` with derivative the identity. The
strict derivative only sees the topology, so it may be computed with the operator norm, under which
matrices form a Banach algebra. -/
private theorem hasStrictFDerivAt_exp_li :
    HasStrictFDerivAt (fun Y : Matrix d d ℝ => NormedSpace.exp Y)
      (ContinuousLinearMap.id ℝ (Matrix d d ℝ)) 0 := by
  let _ : NormedRing (Matrix d d ℝ) := Matrix.linftyOpNormedRing
  let _ : NormedAlgebra ℝ (Matrix d d ℝ) := Matrix.linftyOpNormedAlgebra
  exact hasStrictFDerivAt_exp_zero (𝕂 := ℝ)

/-- The parameters `θ.cob (exp m) (exp m)`: the change of basis `exp m_ℓ` at the hidden state
`h_ℓ`. -/
private noncomputable def cobExp_li {A : Arch T d L} (θ : Params A dIn dOut)
    (m : Fin (L + 1) → Matrix d d ℝ) : Params A dIn dOut :=
  θ.cob (fun ℓ => expGL_li (m ℓ)) (fun ℓ => expGL_li (m ℓ))

/-- `θ.cob G G` is linear in the pair `(G, G⁻¹)` of families of matrices: the map
`(P, R) ↦ (E P_0, R_{ℓ-1} W_read^ℓ, W_write^ℓ P_ℓ, R_L D)`. -/
private noncomputable def cobLin_li {A : Arch T d L} (θ : Params A dIn dOut) :
    (Fin (L + 1) → Matrix d d ℝ) × (Fin (L + 1) → Matrix d d ℝ) →ₗ[ℝ] Params A dIn dOut where
  toFun p := ⟨θ.E * p.1 0, fun ℓ => p.2 ℓ.castSucc * θ.read ℓ, fun ℓ => θ.write ℓ * p.1 ℓ.succ,
    p.2 (Fin.last L) * θ.D⟩
  map_add' p q := by
    refine Params.ext' ?_ (fun ℓ => ?_) (fun ℓ => ?_) ?_ <;>
      simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, Params.add_E, Params.add_read,
        Params.add_write, Params.add_D, Matrix.mul_add, Matrix.add_mul]
  map_smul' c p := by
    refine Params.ext' ?_ (fun ℓ => ?_) (fun ℓ => ?_) ?_ <;>
      simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, Params.smul_E, Params.smul_read,
        Params.smul_write, Params.smul_D, Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply]

omit [Fintype T] in
/-- The orbit map `m ↦ θ.cob (exp m) (exp m)` is strictly differentiable at `0`, with derivative
`m ↦ cobDir θ m`: it is the linear map `cobLin_li θ` after `m ↦ (exp m, exp (-m))`. -/
private theorem hasStrictFDerivAt_cobExp_li {A : Arch T d L} (θ : Params A dIn dOut) :
    ∃ Φ' : (Fin (L + 1) → Matrix d d ℝ) →L[ℝ] Params A dIn dOut,
      HasStrictFDerivAt (cobExp_li θ) Φ' 0 ∧ ∀ m, Φ' m = cobDir θ m := by
  -- the components `m ↦ exp (m_ℓ)` and `m ↦ exp (-m_ℓ)`
  have h1 : ∀ ℓ : Fin (L + 1), HasStrictFDerivAt
      (fun m : Fin (L + 1) → Matrix d d ℝ => NormedSpace.exp (m ℓ))
      ((ContinuousLinearMap.id ℝ (Matrix d d ℝ)).comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (L + 1) => Matrix d d ℝ) ℓ)) 0 :=
    fun ℓ => hasStrictFDerivAt_exp_li.comp (0 : Fin (L + 1) → Matrix d d ℝ)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (L + 1) => Matrix d d ℝ)
        ℓ).hasStrictFDerivAt
  have h2 : ∀ ℓ : Fin (L + 1), HasStrictFDerivAt
      (fun m : Fin (L + 1) → Matrix d d ℝ => NormedSpace.exp (-m ℓ))
      ((ContinuousLinearMap.id ℝ (Matrix d d ℝ)).comp
        (-ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (L + 1) => Matrix d d ℝ) ℓ)) 0 := by
    intro ℓ
    have hg : HasStrictFDerivAt (fun Y : Matrix d d ℝ => NormedSpace.exp Y)
        (ContinuousLinearMap.id ℝ (Matrix d d ℝ))
        ((-ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (L + 1) => Matrix d d ℝ) ℓ) 0) := by
      rw [map_zero]
      exact hasStrictFDerivAt_exp_li
    exact hg.comp (0 : Fin (L + 1) → Matrix d d ℝ)
      (-ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (L + 1) => Matrix d d ℝ)
        ℓ).hasStrictFDerivAt
  have hΨ := (hasStrictFDerivAt_pi.2 h1).prodMk (hasStrictFDerivAt_pi.2 h2)
  -- then the linear map `(P, R) ↦ (E P_0, R_{ℓ-1} W_read^ℓ, W_write^ℓ P_ℓ, R_L D)`
  let B := LinearMap.toContinuousLinearMap (cobLin_li θ)
  refine ⟨B.comp _, B.hasStrictFDerivAt.comp (0 : Fin (L + 1) → Matrix d d ℝ) hΨ, fun m => ?_⟩
  -- the derivative: `(E m_0, -m_{ℓ-1} W_read^ℓ, W_write^ℓ m_ℓ, -m_L D)`
  refine Params.ext' ?_ (fun ℓ => ?_) (fun ℓ => ?_) ?_
  · rfl
  · show -m ℓ.castSucc * θ.read ℓ = -(m ℓ.castSucc * θ.read ℓ)
    exact Matrix.neg_mul _ _
  · rfl
  · show -m (Fin.last L) * θ.D = -(m (Fin.last L) * θ.D)
    exact Matrix.neg_mul _ _

omit [Fintype T] [Fintype dIn] [Fintype dOut] in
/-- At `m = 0` the orbit map gives `θ`. -/
private theorem cobExp_zero_li {A : Arch T d L} (θ : Params A dIn dOut) : cobExp_li θ 0 = θ := by
  refine Params.ext' ?_ (fun ℓ => ?_) (fun ℓ => ?_) ?_ <;>
    simp only [cobExp_li, Params.cob, coe_expGL_li, coe_expGL_li_inv, Pi.zero_apply, neg_zero,
      NormedSpace.exp_zero, Matrix.mul_one, Matrix.one_mul]

/-- **The argument common to the two statements of Proposition 4.6.** Let the maps `f_ℓ` and `χ`
be real-analytic, `E` and the writes of rank `d`, and `ι : M → (Fin (L+1) → Matrix d d ℝ)` an
injective linear map such that the changes of basis `exp (ι m)_ℓ` preserve the function. If
`fd(θ) + dim M = P`, then for every neighborhood `V` of the identity, every `θ'` near `θ` with the
same function is `θ.cob (exp ι m) (exp ι m)` with `exp (ι m) ∈ V`. The proof: on a batch `X` where
the Jacobian has rank `fd(θ)`, its kernel has dimension `dim M`, and the orbit `m ↦ θ.cob (exp ι m)`
has an injective derivative `m ↦ cobDir θ (ι m)` (Lemma B.1); `exists_mem_orbit_of_level_set`. -/
private theorem exists_cobExp_of_eval_eq_li (A : Arch T d L)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (hχ : AnalyticOnNhd ℝ A.χ Set.univ)
    (θ : Params A dIn dOut) (hE : θ.E.rank = Fintype.card d)
    (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d)
    {M : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M] [FiniteDimensional ℝ M]
    (ι : M →L[ℝ] (Fin (L + 1) → Matrix d d ℝ)) (hι : Function.Injective ι)
    (hfd : funDim A 0 θ + Module.finrank ℝ M = Module.finrank ℝ (Params A dIn dOut))
    (hpres : ∀ (m : M) (x : Matrix T dIn ℝ), eval A 0 (cobExp_li θ (ι m)) x = eval A 0 θ x) :
    ∀ V ∈ 𝓝 (1 : Fin (L + 1) → Matrix d d ℝ), ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval A 0 θ' x = eval A 0 θ x) →
        ∃ m : M, (fun ℓ => NormedSpace.exp (ι m ℓ)) ∈ V ∧ θ' = cobExp_li θ (ι m) := by
  intro V hV
  -- a batch `X` on which the rank of the Jacobian is the functional dimension
  obtain ⟨n, X, hX⟩ := exists_jacobianRank_eq_funDim (S := 0) θ
  -- the outputs `F` on the batch are analytic in the parameters, hence strictly differentiable
  have hFa : AnalyticAt ℝ (evalBatch A 0 X) θ :=
    AnalyticAt.pi fun i => analyticOnNhd_eval_params A 0 hf hχ (X i) θ (Set.mem_univ _)
  have hF := hFa.hasStrictFDerivAt
  -- rank–nullity: the kernel of the Jacobian has the dimension of `M`
  have hdim : Module.finrank ℝ (LinearMap.ker (fderiv ℝ (evalBatch A 0 X) θ).toLinearMap)
      = Module.finrank ℝ M := by
    have h := LinearMap.finrank_range_add_finrank_ker (fderiv ℝ (evalBatch A 0 X) θ).toLinearMap
    have h' : jacobianRank A 0 X θ
        = Module.finrank ℝ (LinearMap.range (fderiv ℝ (evalBatch A 0 X) θ).toLinearMap) := rfl
    omega
  -- the orbit map `m ↦ θ.cob (exp ι m) (exp ι m)`, strictly differentiable at `0`
  obtain ⟨Φ', hΦ', hΦ'v⟩ := hasStrictFDerivAt_cobExp_li θ
  have hΦ'0 : HasStrictFDerivAt (cobExp_li θ) Φ' (ι 0) := by
    rw [map_zero]
    exact hΦ'
  have hΦ := hΦ'0.comp (0 : M) ι.hasStrictFDerivAt
  -- its derivative `m ↦ cobDir θ (ι m)` is injective (Lemma B.1)
  have hinj : Function.Injective (Φ'.comp ι) := by
    intro m₁ m₂ h
    have h' : cobDir θ (ι m₁) = cobDir θ (ι m₂) := by
      rw [← hΦ'v, ← hΦ'v]
      exact h
    exact hι (cobDir_injective θ hE hw h')
  -- it passes through `θ` and keeps the function (Proposition 3.2)
  have hΦ0 : cobExp_li θ (ι 0) = θ := by
    rw [map_zero]
    exact cobExp_zero_li θ
  have hconst : ∀ᶠ m in 𝓝 (0 : M),
      evalBatch A 0 X (cobExp_li θ (ι m)) = evalBatch A 0 X θ :=
    Eventually.of_forall fun m => funext fun i => hpres m (X i)
  -- the `m` with `exp (ι m) ∈ V` form a neighborhood of `0`
  have hexp : ContinuousAt (fun Y : Matrix d d ℝ => NormedSpace.exp Y) 0 :=
    hasStrictFDerivAt_exp_li.continuousAt
  have hcont : ContinuousAt (fun m : M => fun ℓ => NormedSpace.exp (ι m ℓ)) 0 :=
    continuousAt_pi.2 fun ℓ => ContinuousAt.comp_of_eq (f := fun m : M => ι m ℓ) hexp
      ((continuous_apply ℓ).comp ι.continuous).continuousAt (by simp only [map_zero, Pi.zero_apply])
  have hV' : (fun m : M => fun ℓ => NormedSpace.exp (ι m ℓ)) ⁻¹' V ∈ 𝓝 (0 : M) := by
    refine hcont.preimage_mem_nhds ?_
    have h1 : (fun ℓ => NormedSpace.exp (ι (0 : M) ℓ)) = (1 : Fin (L + 1) → Matrix d d ℝ) := by
      funext ℓ
      simp only [map_zero, Pi.zero_apply, NormedSpace.exp_zero, Pi.one_apply]
    rw [h1]
    exact hV
  -- the orbit fills the level set near `θ`
  obtain ⟨U, hU, hUV⟩ := exists_mem_orbit_of_level_set hF hΦ hΦ0 hinj hconst hdim _ hV'
  refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
  obtain ⟨m, hm, hmθ⟩ := hUV θ' hθ' (funext fun i => heq (X i))
  exact ⟨m, hm, hmθ.symm⟩

/-- **Proposition 4.6, from the equality condition to local identifiability, without
normalization:** for real-analytic blocks, if `E` and the writes have rank `d` and
`fd(θ) = P − (L+1) d²`, then for every neighborhood `V` of the identity there is a neighborhood `U`
of `θ` such that every `θ' ∈ U` with the same function is `θ.cob G G` with `G ∈ V`. -/
theorem exists_cob_of_eval_eq_skipless (A : Arch T d L) (hA : A.χ = id)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (θ : Params A dIn dOut)
    (hE : θ.E.rank = Fintype.card d) (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d)
    (hfd : funDim A 0 θ + (L + 1) * Fintype.card d ^ 2 = Module.finrank ℝ (Params A dIn dOut)) :
    ∀ V ∈ 𝓝 (1 : Fin (L + 1) → Matrix d d ℝ), ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval A 0 θ' x = eval A 0 θ x) →
        ∃ G : Fin (L + 1) → GL d ℝ, (fun ℓ => (G ℓ : Matrix d d ℝ)) ∈ V ∧ θ' = θ.cob G G := by
  sorry

/-- **Proposition 4.6, from the equality condition to local identifiability, under pre-RMSNorm
with `ε > 0`:** for real-analytic blocks, if `E` and the writes have rank `d` and
`fd(θ) = P − (L+1) d(d−1)/2`, then for every neighborhood `V` of the identity there is a
neighborhood `U` of `θ` such that every `θ' ∈ U` with the same function is `θ.cob Q Q` with
orthogonal `Q_ℓ`, `Q ∈ V`. -/
theorem exists_cob_of_eval_eq_skipless_rmsNorm (A : Arch T d L) {ε : ℝ} (hε : 0 < ε)
    (hA : A.χ = rmsNorm ε) (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ)
    (θ : Params A dIn dOut) (hE : θ.E.rank = Fintype.card d)
    (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d)
    (hfd : funDim A 0 θ + (L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2)
      = Module.finrank ℝ (Params A dIn dOut)) :
    ∀ V ∈ 𝓝 (1 : Fin (L + 1) → Matrix d d ℝ), ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval A 0 θ' x = eval A 0 θ x) →
        ∃ Q : Fin (L + 1) → GL d ℝ,
          (∀ ℓ, (Q ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ) ∧
          (fun ℓ => (Q ℓ : Matrix d d ℝ)) ∈ V ∧ θ' = θ.cob Q Q := by
  sorry

variable {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]

/-- **Corollary 5.3 for tanh blocks without normalization:** for `d_in, d_out ≥ d ≥ 2` and at least
`d` hidden units per block, at almost every parameter `θ`: every `θ'` near `θ` with the same
function is `θ.cob G G` with invertible `G_0, …, G_L` near the identity. -/
theorem ae_exists_cob_of_eval_eq_tanh_skipless [Nonempty T]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) Real.tanh id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, ∀ V ∈ 𝓝 (1 : Fin (L + 1) → Matrix d d ℝ), ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.mlp Real.tanh id hid) 0 θ' x
        = eval (Arch.mlp Real.tanh id hid) 0 θ x) →
        ∃ G : Fin (L + 1) → GL d ℝ, (fun ℓ => (G ℓ : Matrix d d ℝ)) ∈ V ∧ θ' = θ.cob G G := by
  sorry

/-- **Corollary 5.3 for tanh blocks under pre-RMSNorm with `ε > 0`:** at almost every parameter
`θ`, every `θ'` near `θ` with the same function is `θ.cob Q Q` with orthogonal `Q_0, …, Q_L` near
the identity. -/
theorem ae_exists_cob_of_eval_eq_tanh_skipless_rmsNorm [Nonempty T] {ε : ℝ} (hε : 0 < ε)
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) Real.tanh (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, ∀ V ∈ 𝓝 (1 : Fin (L + 1) → Matrix d d ℝ), ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.mlp Real.tanh (rmsNorm ε) hid) 0 θ' x
        = eval (Arch.mlp Real.tanh (rmsNorm ε) hid) 0 θ x) →
        ∃ Q : Fin (L + 1) → GL d ℝ,
          (∀ ℓ, (Q ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ) ∧
          (fun ℓ => (Q ℓ : Matrix d d ℝ)) ∈ V ∧ θ' = θ.cob Q Q := by
  sorry

/-- **Corollary 5.3 for GELU blocks under pre-RMSNorm with `ε > 0`:** at almost every parameter
`θ`, every `θ'` near `θ` with the same function is `θ.cob Q Q` with orthogonal `Q_0, …, Q_L` near
the identity. -/
theorem ae_exists_cob_of_eval_eq_gelu_skipless_rmsNorm [Nonempty T] {ε : ℝ} (hε : 0 < ε)
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, ∀ V ∈ 𝓝 (1 : Fin (L + 1) → Matrix d d ℝ), ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.mlp gelu (rmsNorm ε) hid) 0 θ' x
        = eval (Arch.mlp gelu (rmsNorm ε) hid) 0 θ x) →
        ∃ Q : Fin (L + 1) → GL d ℝ,
          (∀ ℓ, (Q ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ) ∧
          (fun ℓ => (Q ℓ : Matrix d d ℝ)) ∈ V ∧ θ' = θ.cob Q Q := by
  sorry

end Skips
