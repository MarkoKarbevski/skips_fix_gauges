import SkipsLean.Dimension.Functional
import SkipsLean.Symmetry.Normalized

/-!
# The upper bound from the changes of basis

Papers: dimension paper, Theorem 4.3 and Lemma B.1, for the changes of basis at the hidden states
(the symmetries inside the blocks, the number `s` of the paper, are not counted here: they depend
on the kind of block); skips paper, the bound for residual networks.

The changes of basis `I + τ X_ℓ` at the hidden states move the parameters, to first order in `τ`,
in the direction `cobDir θ X`:

  `η_E = E X_0`,  `η_read^ℓ = - X_{ℓ-1} W_read^ℓ`,  `η_write^ℓ = W_write^ℓ X_ℓ`,  `η_D = - X_L D`.

These directions are flat. If `E` and every write have rank `d`, different `X` give different
directions (Lemma B.1), so they span a space of dimension `(L + 1) d²`, and the functional
dimension is at most `P - (L + 1) d²`. In a residual network the same `X` acts at every hidden
state, and the bound is `P - d²`. The bounds under pre-RMSNorm are in `UpperBoundRMSNorm.lean`.
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise Topology

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {A : Arch T d L}

/-- The direction in which the changes of basis `I + τ X_ℓ` at the hidden states move `θ`. -/
def cobDir (θ : Params A dIn dOut) (X : Fin (L + 1) → Matrix d d ℝ) : Params A dIn dOut where
  E := θ.E * X 0
  read ℓ := -(X ℓ.castSucc * θ.read ℓ)
  write ℓ := θ.write ℓ * X ℓ.succ
  D := -(X (Fin.last L) * θ.D)

variable (θ : Params A dIn dOut)

/-- Helper: a matrix `M` of rank equal to its number of columns cancels on the left,
`M X = M Y → X = Y` (its kernel is `0` by rank–nullity). -/
private theorem mul_left_cancel_of_rank {m n k : Type*} [Fintype n] (M : Matrix m n ℝ)
    (hM : M.rank = Fintype.card n) {X Y : Matrix n k ℝ} (h : M * X = M * Y) : X = Y := by
  -- `v ↦ M v` is injective: `rank M + dim ker M = card n`
  have hinj : Function.Injective M.mulVecLin := by
    rw [← LinearMap.ker_eq_bot, ← Submodule.finrank_eq_zero]
    have := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
    rw [Module.finrank_fintype_fun_eq_card] at this
    rw [Matrix.rank] at hM
    omega
  -- compare `X` and `Y` column by column
  ext i j
  have hcol : M.mulVecLin (fun l => X l j) = M.mulVecLin (fun l => Y l j) := by
    funext p
    have := congrFun (congrFun h p) j
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
  exact congrFun (hinj hcol) i

/-- **Lemma B.1 (locally free action), for the changes of basis.** If `E` and every write have
rank `d`, the direction `cobDir θ X` determines `X`. -/
theorem cobDir_injective (hE : θ.E.rank = Fintype.card d)
    (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d) :
    Function.Injective (cobDir θ) := by
  intro X Y h
  funext ℓ
  induction ℓ using Fin.cases with
  | zero =>
    -- the embedding component: `E X_0 = E Y_0`, and `E` has rank `d`
    have h0 : θ.E * X 0 = θ.E * Y 0 := congrArg Params.E h
    exact mul_left_cancel_of_rank θ.E hE h0
  | succ ℓ =>
    -- the write component of block `ℓ + 1`: `W_write X_{ℓ+1} = W_write Y_{ℓ+1}`
    have h1 : θ.write ℓ * X ℓ.succ = θ.write ℓ * Y ℓ.succ := congrArg (fun η => η.write ℓ) h
    exact mul_left_cancel_of_rank (θ.write ℓ) (hw ℓ) h1

/-- Helper: the change of basis `exp (τ X)`, an element of `GL d ℝ` with inverse `exp (-τ X)`. -/
private noncomputable def expGL (X : Matrix d d ℝ) (τ : ℝ) : GL d ℝ where
  val := NormedSpace.exp (τ • X)
  inv := NormedSpace.exp (τ • (-X))
  val_inv := by
    rw [← Matrix.exp_add_of_commute _ _ (((Commute.refl X).neg_right.smul_left τ).smul_right τ),
      smul_neg, add_neg_cancel, NormedSpace.exp_zero]
  inv_val := by
    rw [← Matrix.exp_add_of_commute _ _ (((Commute.refl X).neg_left.smul_left τ).smul_right τ),
      smul_neg, neg_add_cancel, NormedSpace.exp_zero]

/-- Helper: at `τ = 0` the change of basis `exp (τ X)` is the identity. -/
private theorem expGL_zero (X : Matrix d d ℝ) : expGL X 0 = 1 :=
  Units.ext (by simp [expGL])

/-- Helper: `τ ↦ exp (τ X)` has derivative `X` at `0`. The derivative only sees the topology,
so it may be computed with the operator norm, under which matrices form a Banach algebra. -/
private theorem hasDerivAt_exp_smul (X : Matrix d d ℝ) :
    HasDerivAt (fun τ : ℝ => NormedSpace.exp (τ • X)) X 0 := by
  -- the derivative of `exp (τ X)` in a Banach algebra is `exp (τ X) X`, which is `X` at `τ = 0`
  have h := open scoped Matrix.Norms.Operator in hasDerivAt_exp_smul_const (𝕂 := ℝ) X (0 : ℝ)
  rw [zero_smul, NormedSpace.exp_zero, one_mul] at h
  exact h

/-- Helper: multiplying on the left by a fixed matrix keeps a derivative. -/
private theorem hasDerivAt_mul_left {m n k : Type*} [Fintype m] [Fintype n] [Fintype k]
    (M : Matrix m n ℝ) {f : ℝ → Matrix n k ℝ} {f' : Matrix n k ℝ} {t : ℝ}
    (hf : HasDerivAt f f' t) : HasDerivAt (fun τ => M * f τ) (M * f') t := by
  let φ : Matrix n k ℝ →ₗ[ℝ] Matrix m k ℝ :=
    { toFun := (M * ·), map_add' := Matrix.mul_add M,
      map_smul' := fun c N => Matrix.mul_smul M c N }
  exact (LinearMap.toContinuousLinearMap φ).hasFDerivAt.comp_hasDerivAt t hf

/-- Helper: multiplying on the right by a fixed matrix keeps a derivative. -/
private theorem hasDerivAt_mul_right {m n k : Type*} [Fintype m] [Fintype n] [Fintype k]
    (M : Matrix n k ℝ) {f : ℝ → Matrix m n ℝ} {f' : Matrix m n ℝ} {t : ℝ}
    (hf : HasDerivAt f f' t) : HasDerivAt (fun τ => f τ * M) (f' * M) t := by
  let φ : Matrix m n ℝ →ₗ[ℝ] Matrix m k ℝ :=
    { toFun := (· * M), map_add' := fun P Q => Matrix.add_mul P Q M,
      map_smul' := fun c N => Matrix.smul_mul c N M }
  exact (LinearMap.toContinuousLinearMap φ).hasFDerivAt.comp_hasDerivAt t hf

omit [Fintype T] [Fintype dIn] [Fintype dOut] in
/-- Helper: the curve `τ ↦ θ.cob (exp (τ X))` passes through `θ` at `τ = 0`. -/
private theorem cob_expGL_zero (X : Fin (L + 1) → Matrix d d ℝ) :
    θ.cob (fun ℓ => expGL (X ℓ) 0) (fun ℓ => expGL (X ℓ) 0) = θ := by
  simp only [expGL_zero]
  apply Params.ext' <;> intros <;> simp [Params.cob]

omit [Fintype T] in
/-- Helper: the curve `τ ↦ θ.cob (exp (τ X))` has velocity `cobDir θ X` at `τ = 0`. Its
components are fixed matrices times `exp (± τ X_ℓ)`; the derivative is taken componentwise,
through the linear equivalence of the parameters with the tuples of their components. -/
private theorem hasDerivAt_cob_expGL (X : Fin (L + 1) → Matrix d d ℝ) :
    HasDerivAt (fun τ : ℝ => θ.cob (fun ℓ => expGL (X ℓ) τ) (fun ℓ => expGL (X ℓ) τ))
      (cobDir θ X) 0 := by
  -- the four components: `E exp(τ X_0)`, `exp(-τ X_{ℓ-1}) W_read`, `W_write exp(τ X_ℓ)`,
  -- `exp(-τ X_L) D`
  have hprod : HasDerivAt
      (fun τ : ℝ => Params.linearEquivProd
        (θ.cob (fun ℓ => expGL (X ℓ) τ) (fun ℓ => expGL (X ℓ) τ)))
      (Params.linearEquivProd (cobDir θ X)) 0 := by
    refine HasDerivAt.prodMk ?_ (HasDerivAt.prodMk ?_ (HasDerivAt.prodMk ?_ ?_))
    · exact hasDerivAt_mul_left θ.E (hasDerivAt_exp_smul (X 0))
    · refine hasDerivAt_pi.2 fun ℓ => ?_
      have h := hasDerivAt_mul_right (θ.read ℓ) (hasDerivAt_exp_smul (-X ℓ.castSucc))
      rw [Matrix.neg_mul] at h
      exact h
    · refine hasDerivAt_pi.2 fun ℓ => ?_
      exact hasDerivAt_mul_left (θ.write ℓ) (hasDerivAt_exp_smul (X ℓ.succ))
    · have h := hasDerivAt_mul_right θ.D (hasDerivAt_exp_smul (-X (Fin.last L)))
      rw [Matrix.neg_mul] at h
      exact h
  -- back from the tuples of components to the parameters
  exact (LinearMap.toContinuousLinearMap
    (Params.linearEquivProd (A := A) (dIn := dIn) (dOut := dOut)).symm.toLinearMap).hasFDerivAt.comp_hasDerivAt
      0 hprod

/-- Without normalization and without skip connections, every direction `cobDir θ X` is flat. -/
theorem cobDir_mem_flat_skipless (hA : A.χ = id) (hf : ∀ ℓ, Differentiable ℝ (A.f ℓ))
    (X : Fin (L + 1) → Matrix d d ℝ) :
    cobDir θ X ∈ flat A 0 θ := by
  -- `θ' ↦ F_θ'(x)` is differentiable
  have hdiff : ∀ x, DifferentiableAt ℝ (fun θ' : Params A dIn dOut => eval A 0 θ' x) θ :=
    fun x => (differentiable_eval hf (by rw [hA]; exact differentiable_id) x).differentiableAt
  -- the curve `τ ↦ θ.cob (exp (τ X))` passes through `θ` with velocity `cobDir θ X`, and the
  -- changes of basis preserve the function at every `τ` (Proposition 3.2)
  exact mem_flat_of_hasDerivAt θ hdiff
    (fun τ => θ.cob (fun ℓ => expGL (X ℓ) τ) (fun ℓ => expGL (X ℓ) τ)) (cobDir θ X)
    (hasDerivAt_cob_expGL θ X) (cob_expGL_zero θ X)
    (Filter.Eventually.of_forall fun τ x => eval_cob_skipless θ _ x hA)

/-- Helper: `X ↦ cobDir θ X` is linear. -/
private noncomputable def cobDirLin : (Fin (L + 1) → Matrix d d ℝ) →ₗ[ℝ] Params A dIn dOut where
  toFun := cobDir θ
  map_add' X Y := by
    apply Params.ext' <;> intros <;>
      simp only [cobDir, Params.add_E, Params.add_read, Params.add_write, Params.add_D,
        Pi.add_apply, Matrix.mul_add, Matrix.add_mul, neg_add]
  map_smul' c X := by
    apply Params.ext' <;> intros <;>
      simp only [cobDir, Params.smul_E, Params.smul_read, Params.smul_write, Params.smul_D,
        Pi.smul_apply, Matrix.mul_smul, Matrix.smul_mul, smul_neg, RingHom.id_apply]

omit [DecidableEq d] in
/-- Helper: the families `X` of `d × d` matrices on the `L + 1` hidden states form a space of
dimension `(L + 1) d²`. -/
private theorem finrank_cobDomain :
    Module.finrank ℝ (Fin (L + 1) → Matrix d d ℝ) = (L + 1) * Fintype.card d ^ 2 := by
  rw [Module.finrank_pi_fintype, Module.finrank_matrix]
  simp [sq]

/-- **Theorem 4.3, without normalization, for the changes of basis.** If `E` and every write
have rank `d`, the functional dimension of a network without skip connections is at most
`P - (L + 1) d²`. -/
theorem funDim_add_le_skipless (hA : A.χ = id) (hf : ∀ ℓ, Differentiable ℝ (A.f ℓ))
    (hE : θ.E.rank = Fintype.card d) (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d) :
    funDim A 0 θ + (L + 1) * Fintype.card d ^ 2 ≤ Module.finrank ℝ (Params A dIn dOut) := by
  have hdiff : ∀ x, DifferentiableAt ℝ (fun θ' : Params A dIn dOut => eval A 0 θ' x) θ :=
    fun x => (differentiable_eval hf (by rw [hA]; exact differentiable_id) x).differentiableAt
  -- the directions `cobDir θ X` form a subspace of flat directions
  have hV : LinearMap.range (cobDirLin θ) ≤ flat A 0 θ := by
    rintro _ ⟨X, rfl⟩
    exact cobDir_mem_flat_skipless θ hA hf X
  have h := funDim_add_finrank_le_of_le_flat θ hdiff _ hV
  -- of dimension `(L + 1) d²`, since `X ↦ cobDir θ X` is injective (Lemma B.1)
  rwa [LinearMap.finrank_range_of_inj (f := cobDirLin θ) (cobDir_injective θ hE hw),
    finrank_cobDomain] at h

/-- Without normalization, in a residual network, the direction of one change of basis `X` at
all hidden states is flat. -/
theorem cobDir_const_mem_flat_residual (hA : A.χ = id) (hf : ∀ ℓ, Differentiable ℝ (A.f ℓ))
    (X : Matrix d d ℝ) :
    cobDir θ (fun _ => X) ∈ flat A 1 θ := by
  have hdiff : ∀ x, DifferentiableAt ℝ (fun θ' : Params A dIn dOut => eval A 1 θ' x) θ :=
    fun x => (differentiable_eval hf (by rw [hA]; exact differentiable_id) x).differentiableAt
  -- the same curve with the same `exp (τ X)` at every hidden state; with identity skips it
  -- preserves the function at every `τ`
  exact mem_flat_of_hasDerivAt θ hdiff
    (fun τ => θ.cob (fun _ => expGL X τ) (fun _ => expGL X τ)) (cobDir θ (fun _ => X))
    (hasDerivAt_cob_expGL θ (fun _ => X)) (cob_expGL_zero θ (fun _ => X))
    (Filter.Eventually.of_forall fun τ x => eval_cob_residual θ x hA (expGL X τ))

/-- Helper: `X ↦ cobDir θ (fun _ => X)` is linear. -/
private noncomputable def cobDirConstLin : Matrix d d ℝ →ₗ[ℝ] Params A dIn dOut :=
  (cobDirLin θ).comp (LinearMap.pi fun _ => LinearMap.id)

/-- **Skips paper, the upper bound for residual networks, without normalization, for the one
change of basis.** If `E` has rank `d`, the functional dimension of a residual network is at
most `P - d²`. -/
theorem funDim_add_le_residual (hA : A.χ = id) (hf : ∀ ℓ, Differentiable ℝ (A.f ℓ))
    (hE : θ.E.rank = Fintype.card d) :
    funDim A 1 θ + Fintype.card d ^ 2 ≤ Module.finrank ℝ (Params A dIn dOut) := by
  have hdiff : ∀ x, DifferentiableAt ℝ (fun θ' : Params A dIn dOut => eval A 1 θ' x) θ :=
    fun x => (differentiable_eval hf (by rw [hA]; exact differentiable_id) x).differentiableAt
  -- the directions `cobDir θ (fun _ => X)` form a subspace of flat directions
  have hV : LinearMap.range (cobDirConstLin θ) ≤ flat A 1 θ := by
    rintro _ ⟨X, rfl⟩
    exact cobDir_const_mem_flat_residual θ hA hf X
  -- of dimension `d²`: the embedding component `E X` determines `X`
  have hinj : Function.Injective (cobDirConstLin θ) := by
    intro X Y hXY
    have hEq : θ.E * X = θ.E * Y := congrArg Params.E hXY
    exact mul_left_cancel_of_rank θ.E hE hEq
  have h := funDim_add_finrank_le_of_le_flat θ hdiff _ hV
  rwa [LinearMap.finrank_range_of_inj hinj, Module.finrank_matrix, Module.finrank_self,
    mul_one, ← sq] at h

end Skips
