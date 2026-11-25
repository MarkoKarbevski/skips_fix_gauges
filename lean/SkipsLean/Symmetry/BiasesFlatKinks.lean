import SkipsLean.Symmetry.BiasesFlat
import SkipsLean.Dimension.FunctionalBiasesKinks

/-!
# Changes of basis and translations with biases are flat, for any blocks

Paper (skips paper), Lemma A.8 (Translations are not tied): "In a residual network with biases
and without normalization, adding a row `g` to the hidden states `h_ℓ, …, h_L` preserves the
function once the biases are adjusted, for every `ℓ = 0, …, L`." The lemma does not restrict the
kind of block.

`Symmetry/BiasesFlat.lean` proves that the directions of the changes of basis and of the
translations are flat for differentiable blocks. Here the same four statements without a
hypothesis on the blocks, so that they also serve ReLU, ReLU² and ReGLU blocks with biases
(twins of `cobDir_mem_flat_skipless'` and `cobDir_const_mem_flat_residual'` without biases); they
use `mem_flatB_of_hasDerivAt'` (`Dimension/FunctionalBiasesKinks.lean`). The bounds on the
functional dimension that follow, together with the symmetries inside blocks, are in
`Symmetry/InsideBlocksBiases.lean`.
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {A : Arch T d L} (p : ParamsB A dIn dOut)

/-! ### Helpers: the curves of the changes of basis (copies of `Symmetry/BiasesFlat.lean`) -/

/-- Helper: the change of basis `exp (τ X)`, an element of `GL d ℝ` with inverse `exp (-τ X)`. -/
private noncomputable def expGL_bfk (X : Matrix d d ℝ) (τ : ℝ) : GL d ℝ where
  val := NormedSpace.exp (τ • X)
  inv := NormedSpace.exp (τ • (-X))
  val_inv := by
    rw [← Matrix.exp_add_of_commute _ _ (((Commute.refl X).neg_right.smul_left τ).smul_right τ),
      smul_neg, add_neg_cancel, NormedSpace.exp_zero]
  inv_val := by
    rw [← Matrix.exp_add_of_commute _ _ (((Commute.refl X).neg_left.smul_left τ).smul_right τ),
      smul_neg, neg_add_cancel, NormedSpace.exp_zero]

/-- Helper: at `τ = 0` the change of basis `exp (τ X)` is the identity. -/
private theorem expGL_zero_bfk (X : Matrix d d ℝ) : expGL_bfk X 0 = 1 :=
  Units.ext (by simp [expGL_bfk])

/-- Helper: `τ ↦ exp (τ X)` has derivative `X` at `0` (computed with the operator norm). -/
private theorem hasDerivAt_exp_smul_bfk (X : Matrix d d ℝ) :
    HasDerivAt (fun τ : ℝ => NormedSpace.exp (τ • X)) X 0 := by
  have h := open scoped Matrix.Norms.Operator in hasDerivAt_exp_smul_const (𝕂 := ℝ) X (0 : ℝ)
  rw [zero_smul, NormedSpace.exp_zero, one_mul] at h
  exact h

/-- Helper: multiplying on the left by a fixed matrix keeps a derivative. -/
private theorem hasDerivAt_mul_left_bfk {m n k : Type*} [Fintype m] [Fintype n] [Fintype k]
    (M : Matrix m n ℝ) {f : ℝ → Matrix n k ℝ} {f' : Matrix n k ℝ} {t : ℝ}
    (hf : HasDerivAt f f' t) : HasDerivAt (fun τ => M * f τ) (M * f') t := by
  let φ : Matrix n k ℝ →ₗ[ℝ] Matrix m k ℝ :=
    { toFun := (M * ·), map_add' := Matrix.mul_add M,
      map_smul' := fun c N => Matrix.mul_smul M c N }
  exact (LinearMap.toContinuousLinearMap φ).hasFDerivAt.comp_hasDerivAt t hf

/-- Helper: multiplying on the right by a fixed matrix keeps a derivative. -/
private theorem hasDerivAt_mul_right_bfk {m n k : Type*} [Fintype m] [Fintype n] [Fintype k]
    (M : Matrix n k ℝ) {f : ℝ → Matrix m n ℝ} {f' : Matrix m n ℝ} {t : ℝ}
    (hf : HasDerivAt f f' t) : HasDerivAt (fun τ => f τ * M) (f' * M) t := by
  let φ : Matrix m n ℝ →ₗ[ℝ] Matrix m k ℝ :=
    { toFun := (· * M), map_add' := fun P Q => Matrix.add_mul P Q M,
      map_smul' := fun c N => Matrix.smul_mul c N M }
  exact (LinearMap.toContinuousLinearMap φ).hasFDerivAt.comp_hasDerivAt t hf

/-- Helper: a fixed row times a curve of matrices keeps a derivative. -/
private theorem hasDerivAt_vecMul_bfk {m n : Type*} [Fintype m] [Fintype n] (v : m → ℝ)
    {f : ℝ → Matrix m n ℝ} {f' : Matrix m n ℝ} {t : ℝ}
    (hf : HasDerivAt f f' t) : HasDerivAt (fun τ => v ᵥ* f τ) (v ᵥ* f') t := by
  let φ : Matrix m n ℝ →ₗ[ℝ] (n → ℝ) :=
    { toFun := (v ᵥ* ·), map_add' := fun P Q => Matrix.vecMul_add P Q v,
      map_smul' := fun c N => Matrix.vecMul_smul v c N }
  exact (LinearMap.toContinuousLinearMap φ).hasFDerivAt.comp_hasDerivAt t hf

omit [Fintype T] [Fintype dIn] [Fintype dOut] in
/-- Helper: the curve `τ ↦ θ.cob (exp (τ X))` passes through `θ` at `τ = 0`. -/
private theorem cob_expGL_zero_bfk (θ : Params A dIn dOut) (X : Fin (L + 1) → Matrix d d ℝ) :
    θ.cob (fun ℓ => expGL_bfk (X ℓ) 0) (fun ℓ => expGL_bfk (X ℓ) 0) = θ := by
  simp only [expGL_zero_bfk]
  apply Params.ext' <;> intros <;> simp [Params.cob]

omit [Fintype T] in
/-- Helper: the curve `τ ↦ θ.cob (exp (τ X))` has velocity `cobDir θ X` at `τ = 0`, computed
componentwise through `Params.linearEquivProd`. -/
private theorem hasDerivAt_cob_expGL_bfk (θ : Params A dIn dOut)
    (X : Fin (L + 1) → Matrix d d ℝ) :
    HasDerivAt (fun τ : ℝ => θ.cob (fun ℓ => expGL_bfk (X ℓ) τ) (fun ℓ => expGL_bfk (X ℓ) τ))
      (cobDir θ X) 0 := by
  -- `E exp(τ X_0)`, `exp(-τ X_{ℓ-1}) W_read`, `W_write exp(τ X_ℓ)`, `exp(-τ X_L) D`
  have hprod : HasDerivAt
      (fun τ : ℝ => Params.linearEquivProd
        (θ.cob (fun ℓ => expGL_bfk (X ℓ) τ) (fun ℓ => expGL_bfk (X ℓ) τ)))
      (Params.linearEquivProd (cobDir θ X)) 0 := by
    refine HasDerivAt.prodMk ?_ (HasDerivAt.prodMk ?_ (HasDerivAt.prodMk ?_ ?_))
    · exact hasDerivAt_mul_left_bfk θ.E (hasDerivAt_exp_smul_bfk (X 0))
    · refine hasDerivAt_pi.2 fun ℓ => ?_
      have h := hasDerivAt_mul_right_bfk (θ.read ℓ) (hasDerivAt_exp_smul_bfk (-X ℓ.castSucc))
      rw [Matrix.neg_mul] at h
      exact h
    · refine hasDerivAt_pi.2 fun ℓ => ?_
      exact hasDerivAt_mul_left_bfk (θ.write ℓ) (hasDerivAt_exp_smul_bfk (X ℓ.succ))
    · have h := hasDerivAt_mul_right_bfk θ.D (hasDerivAt_exp_smul_bfk (-X (Fin.last L)))
      rw [Matrix.neg_mul] at h
      exact h
  exact (LinearMap.toContinuousLinearMap
    (Params.linearEquivProd (A := A) (dIn := dIn) (dOut := dOut)).symm.toLinearMap
      ).hasFDerivAt.comp_hasDerivAt 0 hprod

omit [Fintype T] [Fintype dIn] [Fintype dOut] in
/-- Helper: the biases after the changes of basis `exp (0 X)` are the biases. -/
private theorem biasesCob_expGL_zero_bfk (b : Biases A dOut) (X : Fin (L + 1) → Matrix d d ℝ) :
    b.cob (fun ℓ => expGL_bfk (X ℓ) 0) = b := by
  simp only [expGL_zero_bfk]
  apply Biases.ext'
  · simp only [Biases.cob, Units.val_one, Matrix.vecMul_one]
  · intro ℓ; rfl
  · intro ℓ; simp only [Biases.cob, Units.val_one, Matrix.vecMul_one]
  · rfl

omit [Fintype T] [Fintype dIn] in
/-- Helper: the curve `τ ↦ b.cob (exp (τ X))` of the biases has velocity `(b_E X_0, 0,
b_write^ℓ X_ℓ, 0)` at `τ = 0`, computed componentwise through `Biases.linearEquivProd`. -/
private theorem hasDerivAt_biasesCob_bfk (b : Biases A dOut) (X : Fin (L + 1) → Matrix d d ℝ) :
    HasDerivAt (fun τ : ℝ => b.cob (fun ℓ => expGL_bfk (X ℓ) τ))
      ({ E := b.E ᵥ* X 0
         read := fun _ => 0
         write := fun ℓ => b.write ℓ ᵥ* X ℓ.succ
         D := 0 } : Biases A dOut) 0 := by
  -- `b_E exp(τ X_0)`, `b_read`, `b_write exp(τ X_ℓ)`, `b_D`
  have hprod : HasDerivAt
      (fun τ : ℝ => Biases.linearEquivProd (b.cob (fun ℓ => expGL_bfk (X ℓ) τ)))
      (Biases.linearEquivProd (A := A) (dOut := dOut)
        { E := b.E ᵥ* X 0
          read := fun _ => 0
          write := fun ℓ => b.write ℓ ᵥ* X ℓ.succ
          D := 0 }) 0 := by
    refine HasDerivAt.prodMk ?_ (HasDerivAt.prodMk ?_ (HasDerivAt.prodMk ?_ ?_))
    · exact hasDerivAt_vecMul_bfk b.E (hasDerivAt_exp_smul_bfk (X 0))
    · exact hasDerivAt_const (0 : ℝ) b.read
    · refine hasDerivAt_pi.2 fun ℓ => ?_
      exact hasDerivAt_vecMul_bfk (b.write ℓ) (hasDerivAt_exp_smul_bfk (X ℓ.succ))
    · exact hasDerivAt_const (0 : ℝ) b.D
  exact (LinearMap.toContinuousLinearMap
    (Biases.linearEquivProd (A := A) (dOut := dOut)).symm.toLinearMap
      ).hasFDerivAt.comp_hasDerivAt 0 hprod

/-- Helper: without skips the stream matrices stay `0` under the changes of basis. -/
private theorem cobSkip_zero_bfk (G : Fin (L + 1) → GL d ℝ) :
    cobSkip (0 : Fin L → Matrix d d ℝ) G = 0 := by
  funext ℓ
  simp only [cobSkip, Pi.zero_apply, Matrix.mul_zero, Matrix.zero_mul]

/-- Helper: with identity skips and one `G` at all hidden states the stream matrices stay `1`. -/
private theorem cobSkip_one_bfk (G : GL d ℝ) :
    cobSkip (1 : Fin L → Matrix d d ℝ) (fun _ => G) = 1 := by
  funext ℓ
  simp only [cobSkip, Pi.one_apply, Matrix.mul_one, Units.inv_mul]


/-- **The directions of the changes of basis are flat in a skipless network with biases,** for
any blocks, without normalization. -/
theorem cobDirB_mem_flatB_skipless' (hA : A.χ = id) (X : Fin (L + 1) → Matrix d d ℝ) :
    cobDirB p X ∈ flatB A 0 p := by
  -- the curve `τ ↦ (θ.cob (exp (τ X)), b.cob (exp (τ X)))` has velocity `cobDirB p X` at `0`
  have hγ : HasDerivAt (fun τ : ℝ => ((p.1.cob (fun ℓ => expGL_bfk (X ℓ) τ)
      (fun ℓ => expGL_bfk (X ℓ) τ), p.2.cob (fun ℓ => expGL_bfk (X ℓ) τ)) : ParamsB A dIn dOut))
      (cobDirB p X) 0 :=
    (hasDerivAt_cob_expGL_bfk p.1 X).prodMk (hasDerivAt_biasesCob_bfk p.2 X)
  refine mem_flatB_of_hasDerivAt' p _ _ hγ
    (Prod.ext (cob_expGL_zero_bfk p.1 X) (biasesCob_expGL_zero_bfk p.2 X))
    (Filter.Eventually.of_forall fun τ x => ?_)
  -- the changes of basis with biases preserve the function (`evalB_cob`, `K = G`, `0` skips)
  have h := evalB_cob 0 p.1 p.2 (fun ℓ => expGL_bfk (X ℓ) τ) (fun ℓ => expGL_bfk (X ℓ) τ) x
    (fun _ _ => by simp only [hA, id_eq])
  rw [cobSkip_zero_bfk] at h
  exact h

/-- **The direction of one change of basis at all hidden states is flat in a residual network
with biases,** for any blocks, without normalization. -/
theorem cobDirB_const_mem_flatB_residual' (hA : A.χ = id) (X : Matrix d d ℝ) :
    cobDirB p (fun _ => X) ∈ flatB A 1 p := by
  -- the same curve with the same `exp (τ X)` at every hidden state
  have hγ : HasDerivAt (fun τ : ℝ => ((p.1.cob (fun _ => expGL_bfk X τ)
      (fun _ => expGL_bfk X τ), p.2.cob (fun _ => expGL_bfk X τ)) : ParamsB A dIn dOut))
      (cobDirB p (fun _ => X)) 0 :=
    (hasDerivAt_cob_expGL_bfk p.1 (fun _ => X)).prodMk (hasDerivAt_biasesCob_bfk p.2 (fun _ => X))
  refine mem_flatB_of_hasDerivAt' p _ _ hγ
    (Prod.ext (cob_expGL_zero_bfk p.1 (fun _ => X)) (biasesCob_expGL_zero_bfk p.2 (fun _ => X)))
    (Filter.Eventually.of_forall fun τ x => ?_)
  -- with identity skips the stream matrices `G⁻¹ 1 G` are again `1`
  have h := evalB_cob 1 p.1 p.2 (fun _ => expGL_bfk X τ) (fun _ => expGL_bfk X τ) x
    (fun _ _ => by simp only [hA, id_eq])
  rw [cobSkip_one_bfk] at h
  exact h

/-! ### Helpers: the translations along a line -/

omit [Fintype T] in
/-- Helper: the rows `c + g` at every token are the sum of the rows `c` and `g`. -/
private theorem of_add_bfk {n : Type*} (c g : n → ℝ) :
    (Matrix.of fun (_ : T) => c + g) = (Matrix.of fun _ => c) + Matrix.of fun _ => g := rfl

omit [Fintype T] in
/-- Helper: the row `g` added to `H` and `g W` subtracted from the bias give the same
pre-activation `H W + c`. -/
private theorem shift_read_bfk {m n : Type*} [Fintype m] (H : Matrix T m ℝ) (g : m → ℝ)
    (W : Matrix m n ℝ) (c : n → ℝ) :
    (H + Matrix.of fun _ => g) * W + (Matrix.of fun _ => c + -(g ᵥ* W))
      = H * W + Matrix.of fun _ => c := by
  ext t j
  simp only [Matrix.add_apply, Matrix.add_mul, Matrix.of_apply, Pi.add_apply, Pi.neg_apply,
    Matrix.mul_apply, Matrix.vecMul, dotProduct]
  ring

/-- Helper: `∑_{k ≤ 0} g_k = g_0`. -/
private theorem sum_Iic_zero_bfk {V : Type*} [AddCommMonoid V] (g : Fin (L + 1) → V) :
    ∑ k ∈ Finset.Iic (0 : Fin (L + 1)), g k = g 0 := by
  have hs : Finset.Iic (0 : Fin (L + 1)) = {0} := by
    ext k
    simp only [Finset.mem_Iic, Finset.mem_singleton, Fin.le_iff_val_le_val, Fin.ext_iff,
      Fin.val_zero]
    omega
  rw [hs, Finset.sum_singleton]

/-- Helper: `∑_{k ≤ ℓ+1} g_k = ∑_{k ≤ ℓ} g_k + g_{ℓ+1}`. -/
private theorem sum_Iic_succ_bfk {V : Type*} [AddCommMonoid V] (g : Fin (L + 1) → V)
    (ℓ : Fin L) :
    ∑ k ∈ Finset.Iic ℓ.succ, g k = ∑ k ∈ Finset.Iic ℓ.castSucc, g k + g ℓ.succ := by
  have hs : Finset.Iic ℓ.succ = insert ℓ.succ (Finset.Iic ℓ.castSucc) := by
    ext k
    simp only [Finset.mem_Iic, Finset.mem_insert, Fin.le_iff_val_le_val, Fin.ext_iff,
      Fin.val_succ, Fin.val_castSucc]
    omega
  have hn : ℓ.succ ∉ Finset.Iic ℓ.castSucc := by
    simp only [Finset.mem_Iic, not_le]
    exact Fin.castSucc_lt_succ
  rw [hs, Finset.sum_insert hn, add_comm]

/-- Helper: `∑_{k ≤ L} g_k = ∑_k g_k`. -/
private theorem sum_Iic_last_bfk {V : Type*} [AddCommMonoid V] (g : Fin (L + 1) → V) :
    ∑ k ∈ Finset.Iic (Fin.last L), g k = ∑ k, g k := by
  have hs : Finset.Iic (Fin.last L) = Finset.univ := by
    ext k
    simp only [Finset.mem_Iic, Finset.mem_univ, iff_true]
    exact Fin.le_last k
  rw [hs]

omit [Fintype T] [Fintype dOut] in
/-- Helper: in a residual network without normalization, the biases moved by `translateDir θ g`
shift the hidden state `h_m` by `g_0 + ⋯ + g_m`. -/
private theorem hiddenB_add_translateDir_bfk (hA : A.χ = id) (θ : Params A dIn dOut)
    (b : Biases A dOut) (g : Fin (L + 1) → d → ℝ) (x : Matrix T dIn ℝ) (m : Fin (L + 1)) :
    hiddenB A 1 θ (b + translateDir θ g) x m
      = hiddenB A 1 θ b x m + Matrix.of fun _ => ∑ k ∈ Finset.Iic m, g k := by
  induction m using Fin.induction with
  | zero =>
    -- `h'_0 = x E + b_E + g_0`
    rw [hiddenB_zero, hiddenB_zero, sum_Iic_zero_bfk]
    show x * θ.E + (Matrix.of fun _ => b.E + g 0) = _
    rw [of_add_bfk, add_assoc]
  | succ ℓ ih =>
    -- the read removes the shift, the skip carries it, the write bias adds `g_{ℓ+1}`
    rw [hiddenB_succ, hiddenB_succ, ih, hA, sum_Iic_succ_bfk g ℓ]
    have hread : (hiddenB A 1 θ b x ℓ.castSucc
          + Matrix.of fun _ => ∑ k ∈ Finset.Iic ℓ.castSucc, g k) * θ.read ℓ
        + (Matrix.of fun _ => (b + translateDir θ g).read ℓ)
        = hiddenB A 1 θ b x ℓ.castSucc * θ.read ℓ + Matrix.of fun _ => b.read ℓ :=
      shift_read_bfk _ _ _ _
    simp only [id_eq, hread, Pi.one_apply, Matrix.mul_one]
    show _ + (_ + Matrix.of fun _ => b.write ℓ + g ℓ.succ) = _
    rw [of_add_bfk, of_add_bfk]
    abel

omit [Fintype T] [Fintype dOut] in
/-- Helper: in a residual network without normalization, the biases moved by `translateDir θ g`
give the same function. -/
private theorem evalB_add_translateDir_bfk (hA : A.χ = id) (θ : Params A dIn dOut)
    (b : Biases A dOut) (g : Fin (L + 1) → d → ℝ) (x : Matrix T dIn ℝ) :
    evalB A 1 θ (b + translateDir θ g) x = evalB A 1 θ b x := by
  -- `(h_L + ∑ g) D + b_D − (∑ g) D = h_L D + b_D`
  unfold evalB
  rw [hiddenB_add_translateDir_bfk hA θ b g x (Fin.last L), hA, sum_Iic_last_bfk]
  show id (_ + _) * θ.D + (Matrix.of fun _ => b.D + -((∑ k, g k) ᵥ* θ.D)) = _
  simp only [id_eq, shift_read_bfk]

omit [Fintype T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: `translateDir θ` is homogeneous. -/
private theorem smul_translateDir_bfk (θ : Params A dIn dOut) (g : Fin (L + 1) → d → ℝ) (c : ℝ) :
    c • translateDir θ g = translateDir θ (c • g) := by
  apply Biases.ext'
  · rfl
  · intro ℓ
    simp only [Biases.smul_read, translateDir, Pi.smul_apply, ← Finset.smul_sum,
      Matrix.smul_vecMul, smul_neg]
  · intro ℓ; rfl
  · simp only [Biases.smul_D, translateDir, Pi.smul_apply, ← Finset.smul_sum,
      Matrix.smul_vecMul, smul_neg]

/-- **Lemma A.8, first sentence, as flat directions, for any blocks:** the directions of the
translations of a residual network with biases are flat. -/
theorem translateDir_mem_flatB' (hA : A.χ = id) (g : Fin (L + 1) → d → ℝ) :
    ((0, translateDir p.1 g) : ParamsB A dIn dOut) ∈ flatB A 1 p := by
  -- the line `τ ↦ (θ, b + τ translateDir θ g)`
  have hb := (hasDerivAt_id' (x := (0 : ℝ))).smul_const (translateDir p.1 g) |>.const_add p.2
  rw [one_smul] at hb
  have hγ : HasDerivAt (fun τ : ℝ => ((p.1, p.2 + τ • translateDir p.1 g) : ParamsB A dIn dOut))
      ((0, translateDir p.1 g) : ParamsB A dIn dOut) 0 :=
    (hasDerivAt_const (0 : ℝ) p.1).prodMk hb
  refine mem_flatB_of_hasDerivAt' p _ _ hγ ?_ (Filter.Eventually.of_forall fun τ x => ?_)
  · show ((p.1, p.2 + (0 : ℝ) • translateDir p.1 g) : ParamsB A dIn dOut) = p
    rw [zero_smul, add_zero]
  · -- along the line, the biases are moved by `translateDir θ (τ g)`
    show evalB A 1 p.1 (p.2 + τ • translateDir p.1 g) x = _
    rw [smul_translateDir_bfk]
    exact evalB_add_translateDir_bfk hA p.1 p.2 (τ • g) x

omit [Fintype T] [DecidableEq d] [Fintype dOut] in
/-- Helper: in a skipless network without normalization, the biases moved by
`translateAtDir θ g` shift the hidden state `h_m` by `g_m`. -/
private theorem hiddenB_add_translateAtDir_bfk (hA : A.χ = id) (θ : Params A dIn dOut)
    (b : Biases A dOut) (g : Fin (L + 1) → d → ℝ) (x : Matrix T dIn ℝ) (m : Fin (L + 1)) :
    hiddenB A 0 θ (b + translateAtDir θ g) x m
      = hiddenB A 0 θ b x m + Matrix.of fun _ => g m := by
  induction m using Fin.induction with
  | zero =>
    -- `h'_0 = x E + b_E + g_0`
    rw [hiddenB_zero, hiddenB_zero]
    show x * θ.E + (Matrix.of fun _ => b.E + g 0) = _
    rw [of_add_bfk, add_assoc]
  | succ ℓ ih =>
    -- no skip: the read removes the shift of `h_ℓ`, the write bias adds `g_{ℓ+1}`
    rw [hiddenB_succ, hiddenB_succ, ih, hA]
    have hread : (hiddenB A 0 θ b x ℓ.castSucc + Matrix.of fun _ => g ℓ.castSucc) * θ.read ℓ
        + (Matrix.of fun _ => (b + translateAtDir θ g).read ℓ)
        = hiddenB A 0 θ b x ℓ.castSucc * θ.read ℓ + Matrix.of fun _ => b.read ℓ :=
      shift_read_bfk _ _ _ _
    simp only [id_eq, hread, Pi.zero_apply, Matrix.mul_zero, zero_add]
    show _ + (Matrix.of fun _ => b.write ℓ + g ℓ.succ) = _
    rw [of_add_bfk, add_assoc]

omit [Fintype T] [DecidableEq d] [Fintype dOut] in
/-- Helper: in a skipless network without normalization, the biases moved by
`translateAtDir θ g` give the same function. -/
private theorem evalB_add_translateAtDir_bfk (hA : A.χ = id) (θ : Params A dIn dOut)
    (b : Biases A dOut) (g : Fin (L + 1) → d → ℝ) (x : Matrix T dIn ℝ) :
    evalB A 0 θ (b + translateAtDir θ g) x = evalB A 0 θ b x := by
  -- `(h_L + g_L) D + b_D − g_L D = h_L D + b_D`
  unfold evalB
  rw [hiddenB_add_translateAtDir_bfk hA θ b g x (Fin.last L), hA]
  show id (_ + _) * θ.D + (Matrix.of fun _ => b.D + -(g (Fin.last L) ᵥ* θ.D)) = _
  simp only [id_eq, shift_read_bfk]

omit [Fintype T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: `translateAtDir θ` is homogeneous. -/
private theorem smul_translateAtDir_bfk (θ : Params A dIn dOut) (g : Fin (L + 1) → d → ℝ)
    (c : ℝ) : c • translateAtDir θ g = translateAtDir θ (c • g) := by
  apply Biases.ext'
  · rfl
  · intro ℓ
    simp only [Biases.smul_read, translateAtDir, Pi.smul_apply, Matrix.smul_vecMul, smul_neg]
  · intro ℓ; rfl
  · simp only [Biases.smul_D, translateAtDir, Pi.smul_apply, Matrix.smul_vecMul, smul_neg]

/-- **The directions of the translations of the hidden states of a skipless network with biases
are flat,** for any blocks. -/
theorem translateAtDir_mem_flatB' (hA : A.χ = id) (g : Fin (L + 1) → d → ℝ) :
    ((0, translateAtDir p.1 g) : ParamsB A dIn dOut) ∈ flatB A 0 p := by
  -- the line `τ ↦ (θ, b + τ translateAtDir θ g)`
  have hb := (hasDerivAt_id' (x := (0 : ℝ))).smul_const (translateAtDir p.1 g) |>.const_add p.2
  rw [one_smul] at hb
  have hγ : HasDerivAt
      (fun τ : ℝ => ((p.1, p.2 + τ • translateAtDir p.1 g) : ParamsB A dIn dOut))
      ((0, translateAtDir p.1 g) : ParamsB A dIn dOut) 0 :=
    (hasDerivAt_const (0 : ℝ) p.1).prodMk hb
  refine mem_flatB_of_hasDerivAt' p _ _ hγ ?_ (Filter.Eventually.of_forall fun τ x => ?_)
  · show ((p.1, p.2 + (0 : ℝ) • translateAtDir p.1 g) : ParamsB A dIn dOut) = p
    rw [zero_smul, add_zero]
  · -- along the line, the biases are moved by `translateAtDir θ (τ g)`
    show evalB A 0 p.1 (p.2 + τ • translateAtDir p.1 g) x = _
    rw [smul_translateAtDir_bfk]
    exact evalB_add_translateAtDir_bfk hA p.1 p.2 (τ • g) x

end Skips
