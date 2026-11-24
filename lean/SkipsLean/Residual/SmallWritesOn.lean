import SkipsLean.Residual.SmallWrites
import SkipsLean.Residual.SmallParameterOn

/-!
# Residual networks with small writes, for blocks that are smooth on an open set

Paper (skips paper): proof of Lemma A.30 (ReLU-type blocks with small writes), second and third
paragraph: "With the writes `τ V_ℓ`, the pre-activations of block `ℓ` are `h_{ℓ−1} W_read^ℓ` with
`h_{ℓ−1} = x E + O(τ)`. So for `|τ|` below some `τ_0 > 0`, which depends on the parameters and on
the batch, every pre-activation on the batch has the sign of its limit. The outputs on the batch
are then polynomial in the parameters and in `τ`, the Jacobian on the batch, with its read columns
divided by `τ`, tends to `J_0`, and by lower semicontinuity it has rank at least
`P − d_model² − s` for all small `τ ≠ 0`. Near such parameters the signs on the batch do not
change […]. So the rank on the batch, which is at least `P − d_model² − s` by lower
semicontinuity, is exactly `P − d_model² − s`".

Stated here for any blocks without normalization whose fixed maps `f_ℓ` are twice continuously
differentiable on open sets `V_ℓ` of pre-activations (for ReLU-type blocks: the matrices with no
entry at the kink), and a finite batch `X` of inputs whose limit pre-activations
`x E W_read^ℓ` lie in the `V_ℓ`:

* for all small `τ ≠ 0` the pre-activations on the batch at `θ_τ` stay in the `V_ℓ`, and if every
  direction that is flat for the limit `J_0` (`smallWritesLimit`, `Residual/SmallWrites.lean`) on
  the batch lies in a subspace `W`, the Jacobian on the batch at `θ_τ` has rank at least
  `P − dim W`;
* at parameters whose pre-activations on a batch lie in the `V_ℓ`, the same holds nearby, and
  the rank of the Jacobian on the batch does not drop nearby.

The first is `eventually_funDim_smallWrites_ge` of `Residual/SmallWrites.lean` (analytic blocks,
all inputs) on one batch.
-/

namespace Skips

open Matrix Filter Topology
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable (A : Arch T d L) (θ : Params A dIn dOut)

/-! ### Helpers: products of matrix-valued maps -/

/-- Helper: matrix multiplication as a continuous bilinear map. -/
private noncomputable def mulB_swo (p q r : Type*) [Fintype p] [Fintype q] [Fintype r] :
    Matrix p q ℝ →L[ℝ] Matrix q r ℝ →L[ℝ] Matrix p r ℝ :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap :
      (Matrix q r ℝ →ₗ[ℝ] Matrix p r ℝ) ≃ₗ[ℝ] (Matrix q r ℝ →L[ℝ] Matrix p r ℝ)).toLinearMap ∘ₗ
      LinearMap.mk₂ ℝ (fun a b => a * b) Matrix.add_mul (fun c a b => Matrix.smul_mul c a b)
        Matrix.mul_add (fun c a b => Matrix.mul_smul a c b))

/-- Helper: the product of two matrix-valued maps that are `C^m` at a point is `C^m` there. -/
private theorem contDiffAt_mul_swo {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {p q r : Type*} [Fintype p] [Fintype q] [Fintype r] {m : WithTop ℕ∞}
    {f : E → Matrix p q ℝ} {g : E → Matrix q r ℝ} {y : E}
    (hf : ContDiffAt ℝ m f y) (hg : ContDiffAt ℝ m g y) :
    ContDiffAt ℝ m (fun z => f z * g z) y := by
  -- entrywise: `(f g)_{ik} = ∑_j f_{ij} g_{jk}`
  refine contDiffAt_pi.2 fun i => contDiffAt_pi.2 fun k => ?_
  have hfe : ∀ j, ContDiffAt ℝ m (fun z => f z i j) y := fun j =>
    contDiffAt_pi.1 (contDiffAt_pi.1 hf i) j
  have hge : ∀ j, ContDiffAt ℝ m (fun z => g z j k) y := fun j =>
    contDiffAt_pi.1 (contDiffAt_pi.1 hg j) k
  have hs : ContDiffAt ℝ m (fun z => ∑ j, f z i j * g z j k) y :=
    ContDiffAt.sum fun j _ => (hfe j).mul (hge j)
  exact hs

/-- Helper: the product of two matrix-valued maps that are continuous at a point is continuous
there. -/
private theorem continuousAt_mul_swo {E : Type*} [TopologicalSpace E]
    {p q r : Type*} [Fintype p] [Fintype q] [Fintype r]
    {f : E → Matrix p q ℝ} {g : E → Matrix q r ℝ} {y : E}
    (hf : ContinuousAt f y) (hg : ContinuousAt g y) :
    ContinuousAt (fun z => f z * g z) y := by
  have h1 : ContinuousAt (fun z => mulB_swo p q r (f z)) y :=
    (mulB_swo p q r).continuous.continuousAt.comp hf
  exact h1.clm_apply hg

/-- Helper: the product rule for matrix-valued maps, with the value of the derivative,
`(f g)' v = f' v g + f g' v`. -/
private theorem hasFDerivAt_mul_swo {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {p q r : Type*} [Fintype p] [Fintype q] [Fintype r] {f : E → Matrix p q ℝ}
    {g : E → Matrix q r ℝ} {f' : E →L[ℝ] Matrix p q ℝ} {g' : E →L[ℝ] Matrix q r ℝ} {y : E}
    (hf : HasFDerivAt f f' y) (hg : HasFDerivAt g g' y) :
    ∃ h' : E →L[ℝ] Matrix p r ℝ, HasFDerivAt (fun z => f z * g z) h' y ∧
      ∀ v, h' v = f' v * g y + f y * g' v := by
  have h := (mulB_swo p q r).hasFDerivAt_of_bilinear hf hg
  refine ⟨_, h, fun v => ?_⟩
  show f y * g' v + f' v * g y = _
  exact add_comm _ _

/-- Helper: `y ↦ y M`, as a continuous linear map. -/
private noncomputable def mulRightCLM_swo {p q r : Type*} [Fintype p] [Fintype q] [Fintype r]
    (M : Matrix q r ℝ) : Matrix p q ℝ →L[ℝ] Matrix p r ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun Y => Y * M, map_add' := fun Y Z => Matrix.add_mul Y Z M,
      map_smul' := fun c Y => Matrix.smul_mul c Y M }

/-! ### Helpers: the entries of the parameters -/

/-- Helper: the embedding, as a continuous linear map of the parameters. -/
private noncomputable def clmE_swo : Params A dIn dOut →L[ℝ] Matrix dIn d ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun θ' => θ'.E, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }

/-- Helper: the read of block `ℓ`, as a continuous linear map of the parameters. -/
private noncomputable def clmRead_swo (ℓ : Fin L) :
    Params A dIn dOut →L[ℝ] Matrix d (A.r ℓ) ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun θ' => θ'.read ℓ, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }

/-- Helper: the write of block `ℓ`, as a continuous linear map of the parameters. -/
private noncomputable def clmWrite_swo (ℓ : Fin L) :
    Params A dIn dOut →L[ℝ] Matrix (A.w ℓ) d ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun θ' => θ'.write ℓ, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }

/-- Helper: the readout, as a continuous linear map of the parameters. -/
private noncomputable def clmD_swo : Params A dIn dOut →L[ℝ] Matrix d dOut ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun θ' => θ'.D, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }

omit [Fintype T] [DecidableEq d] in
@[simp] private theorem clmE_swo_apply (v : Params A dIn dOut) : clmE_swo A v = v.E := rfl

omit [Fintype T] [DecidableEq d] in
@[simp] private theorem clmRead_swo_apply (ℓ : Fin L) (v : Params A dIn dOut) :
    clmRead_swo A ℓ v = v.read ℓ := rfl

omit [Fintype T] [DecidableEq d] in
@[simp] private theorem clmWrite_swo_apply (ℓ : Fin L) (v : Params A dIn dOut) :
    clmWrite_swo A ℓ v = v.write ℓ := rfl

omit [Fintype T] [DecidableEq d] in
@[simp] private theorem clmD_swo_apply (v : Params A dIn dOut) : clmD_swo A v = v.D := rfl

/-! ### Helpers: the hidden states are smooth where the pre-activations lie in the `V ℓ` -/

omit [DecidableEq d] in
/-- Helper: at parameters `θ₀` whose pre-activations at the input `x` lie in the open sets
`V ℓ`, on which the `f_ℓ` are `C^m`, every hidden state is `C^m` in the parameters at `θ₀`. -/
private theorem contDiffAt_hidden_swo (hA : A.χ = id) (S : Fin L → Matrix d d ℝ)
    (V : ∀ ℓ, Set (Matrix T (A.r ℓ) ℝ)) (hVo : ∀ ℓ, IsOpen (V ℓ)) {m : WithTop ℕ∞}
    (hf : ∀ ℓ, ContDiffOn ℝ m (A.f ℓ) (V ℓ)) (θ₀ : Params A dIn dOut) (x : Matrix T dIn ℝ)
    (hx : ∀ ℓ, hidden A S θ₀ x ℓ.castSucc * θ₀.read ℓ ∈ V ℓ) (k : Fin (L + 1)) :
    ContDiffAt ℝ m (fun θ' : Params A dIn dOut => hidden A S θ' x k) θ₀ := by
  induction k using Fin.induction with
  | zero =>
    -- `h_0 = x E`
    have hE : ContDiffAt ℝ m (fun θ' : Params A dIn dOut => θ'.E) θ₀ :=
      (clmE_swo A (dIn := dIn) (dOut := dOut)).contDiff.contDiffAt
    simp only [hidden_zero]
    exact contDiffAt_mul_swo contDiffAt_const hE
  | succ k ih =>
    -- `h_{k+1} = h_k S_k + f_k(h_k W_read^k) W_write^k`, with `h_k W_read^k ∈ V k` at `θ₀`
    have hR : ContDiffAt ℝ m (fun θ' : Params A dIn dOut => θ'.read k) θ₀ :=
      (clmRead_swo A (dIn := dIn) (dOut := dOut) k).contDiff.contDiffAt
    have hWr : ContDiffAt ℝ m (fun θ' : Params A dIn dOut => θ'.write k) θ₀ :=
      (clmWrite_swo A (dIn := dIn) (dOut := dOut) k).contDiff.contDiffAt
    have hpre : ContDiffAt ℝ m
        (fun θ' : Params A dIn dOut => hidden A S θ' x k.castSucc * θ'.read k) θ₀ :=
      contDiffAt_mul_swo ih hR
    have hfk : ContDiffAt ℝ m (A.f k) (hidden A S θ₀ x k.castSucc * θ₀.read k) :=
      (hf k).contDiffAt ((hVo k).mem_nhds (hx k))
    have hc : ContDiffAt ℝ m
        (fun θ' : Params A dIn dOut => A.f k (hidden A S θ' x k.castSucc * θ'.read k)) θ₀ :=
      hfk.comp θ₀ hpre
    have hs := (contDiffAt_mul_swo ih (contDiffAt_const (c := S k))).add
      (contDiffAt_mul_swo hc hWr)
    simp only [hidden_succ, hA, id_eq]
    exact hs

omit [DecidableEq d] in
/-- Helper: at such parameters the outputs on the batch are `C^m` in the parameters. -/
private theorem contDiffAt_evalBatch_swo (hA : A.χ = id) (S : Fin L → Matrix d d ℝ)
    (V : ∀ ℓ, Set (Matrix T (A.r ℓ) ℝ)) (hVo : ∀ ℓ, IsOpen (V ℓ)) {m : WithTop ℕ∞}
    (hf : ∀ ℓ, ContDiffOn ℝ m (A.f ℓ) (V ℓ)) (θ₀ : Params A dIn dOut) {n : ℕ}
    (X : Fin n → Matrix T dIn ℝ)
    (hx : ∀ i ℓ, hidden A S θ₀ (X i) ℓ.castSucc * θ₀.read ℓ ∈ V ℓ) :
    ContDiffAt ℝ m (evalBatch A S X) θ₀ := by
  refine contDiffAt_pi.2 fun i => ?_
  have hD : ContDiffAt ℝ m (fun θ' : Params A dIn dOut => θ'.D) θ₀ :=
    (clmD_swo A (dIn := dIn) (dOut := dOut)).contDiff.contDiffAt
  have h := contDiffAt_mul_swo
    (contDiffAt_hidden_swo A hA S V hVo hf θ₀ (X i) (hx i) (Fin.last L)) hD
  simp only [evalBatch, eval, hA, id_eq]
  exact h

/-! ### Helpers: the hidden states at `θ_τ` -/

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the embedding of `θ_τ` is that of `θ`. -/
@[simp] private theorem smallWrites_E_swo (τ : ℝ) : (θ.smallWrites τ).E = θ.E := rfl

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the reads of `θ_τ` are those of `θ`. -/
@[simp] private theorem smallWrites_read_swo (τ : ℝ) (ℓ : Fin L) :
    (θ.smallWrites τ).read ℓ = θ.read ℓ := rfl

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the writes of `θ_τ` are `τ W_write^ℓ`. -/
@[simp] private theorem smallWrites_write_swo (τ : ℝ) (ℓ : Fin L) :
    (θ.smallWrites τ).write ℓ = τ • θ.write ℓ := rfl

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the readout of `θ_τ` is that of `θ`. -/
@[simp] private theorem smallWrites_D_swo (τ : ℝ) : (θ.smallWrites τ).D = θ.D := rfl

omit [Fintype T] [Fintype dOut] in
/-- Helper: the residual step at `θ_τ` without normalization,
`h_{k+1} = h_k + τ (f_k(h_k W_read^k) W_write^k)`. -/
private theorem hidden_smallWrites_succ_swo (hA : A.χ = id) (x : Matrix T dIn ℝ) (τ : ℝ)
    (k : Fin L) :
    hidden A 1 (θ.smallWrites τ) x k.succ = hidden A 1 (θ.smallWrites τ) x k.castSucc
      + τ • (A.f k (hidden A 1 (θ.smallWrites τ) x k.castSucc * θ.read k) * θ.write k) := by
  rw [hidden_succ, hA, Pi.one_apply, Matrix.mul_one, id_eq, smallWrites_read_swo,
    smallWrites_write_swo, Matrix.mul_smul]

omit [Fintype T] [Fintype dOut] in
/-- Helper: at `τ = 0` every hidden state is `x E`. -/
private theorem hidden_smallWrites_zero_swo (hA : A.χ = id) (x : Matrix T dIn ℝ)
    (k : Fin (L + 1)) : hidden A 1 (θ.smallWrites 0) x k = x * θ.E := by
  induction k using Fin.induction with
  | zero => rw [hidden_zero, smallWrites_E_swo]
  | succ k ih => rw [hidden_smallWrites_succ_swo A θ hA, ih, zero_smul, add_zero]

/-- Helper: the derivative at `0` of `τ ↦ τ g(τ)`, for `g` continuous at `0`, is `g(0)`. -/
private theorem hasDerivAt_smul_self_swo {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g : ℝ → F} (hg : ContinuousAt g 0) : HasDerivAt (fun τ : ℝ => τ • g τ) (g 0) 0 := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  refine Tendsto.congr' ?_ (hg.tendsto.mono_left nhdsWithin_le_nhds)
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [zero_add, zero_smul, sub_zero, smul_smul, inv_mul_cancel₀ ht, one_smul]

/-- Helper: a sum over the blocks before `k + 1` is the sum over the blocks before `k` plus the
term of block `k`. -/
private theorem sum_ite_lt_succ_swo {M : Type*} [AddCommMonoid M] {m : ℕ} (a : Fin m → M)
    (k : Fin m) :
    (∑ ℓ : Fin m, if (ℓ : ℕ) < (k : ℕ) + 1 then a ℓ else 0)
      = (∑ ℓ : Fin m, if (ℓ : ℕ) < (k : ℕ) then a ℓ else 0) + a k := by
  have h : ∀ ℓ : Fin m, (if (ℓ : ℕ) < (k : ℕ) + 1 then a ℓ else 0)
      = (if (ℓ : ℕ) < (k : ℕ) then a ℓ else 0) + (if ℓ = k then a ℓ else 0) := by
    intro ℓ
    by_cases h1 : (ℓ : ℕ) < k
    · have h2 : ℓ ≠ k := fun h => by rw [h] at h1; exact lt_irrefl _ h1
      have h3 : (ℓ : ℕ) < k + 1 := by omega
      simp only [h1, h2, h3, ite_true, ite_false, add_zero]
    · by_cases h2 : ℓ = k
      · subst h2
        simp only [lt_add_iff_pos_right, Order.lt_one_iff, ↓reduceIte, lt_self_iff_false, zero_add]
      · have h3 : ¬ (ℓ : ℕ) < k + 1 := fun h => h2 (Fin.ext (by omega))
        simp only [h1, h2, h3, ite_false, add_zero]
  rw [Finset.sum_congr rfl fun ℓ _ => h ℓ, Finset.sum_add_distrib]
  simp only [Fin.val_fin_lt, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

omit [Fintype dOut] in
/-- Helper: the derivative at `τ = 0` of the hidden state `h_k` at `θ_τ` is the sum over the
blocks `ℓ < k` of `f_ℓ(x E W_read^ℓ) W_write^ℓ`, when every `f_ℓ` is continuous at the limit
pre-activation `x E W_read^ℓ`. -/
private theorem hasDerivAt_hidden_smallWrites_swo (hA : A.χ = id) (x : Matrix T dIn ℝ)
    (hc : ∀ ℓ, ContinuousAt (A.f ℓ) (x * θ.E * θ.read ℓ)) (k : Fin (L + 1)) :
    HasDerivAt (fun τ : ℝ => hidden A 1 (θ.smallWrites τ) x k)
      (∑ ℓ : Fin L, if (ℓ : ℕ) < (k : ℕ) then A.f ℓ (x * θ.E * θ.read ℓ) * θ.write ℓ else 0)
      0 := by
  induction k using Fin.induction with
  | zero =>
    -- `h_0 = x E` does not depend on `τ`
    simp only [hidden_zero, smallWrites_E_swo, Fin.val_zero, Nat.not_lt_zero, ite_false,
      Finset.sum_const_zero]
    exact hasDerivAt_const _ _
  | succ k ih =>
    -- `h_{k+1}(τ) = h_k(τ) + τ g(τ)`, and the derivative of `τ g(τ)` at `0` is `g(0)`
    simp only [hidden_smallWrites_succ_swo A θ hA]
    have hpre : ContinuousAt
        (fun τ : ℝ => hidden A 1 (θ.smallWrites τ) x k.castSucc * θ.read k) 0 :=
      continuousAt_mul_swo ih.continuousAt continuousAt_const
    have hfk : ContinuousAt (A.f k) (hidden A 1 (θ.smallWrites 0) x k.castSucc * θ.read k) := by
      rw [hidden_smallWrites_zero_swo A θ hA]
      exact hc k
    have hfc : ContinuousAt
        (fun τ : ℝ => A.f k (hidden A 1 (θ.smallWrites τ) x k.castSucc * θ.read k)) 0 :=
      ContinuousAt.comp (f := fun τ : ℝ => hidden A 1 (θ.smallWrites τ) x k.castSucc * θ.read k)
        hfk hpre
    have hg : ContinuousAt (fun τ : ℝ =>
        A.f k (hidden A 1 (θ.smallWrites τ) x k.castSucc * θ.read k) * θ.write k) 0 :=
      continuousAt_mul_swo hfc continuousAt_const
    have h2 := ih.add (hasDerivAt_smul_self_swo hg)
    -- `g(0)` is the term of block `k` at `h_k(0) = x E`
    have hv : (∑ ℓ : Fin L, if (ℓ : ℕ) < (k.castSucc : ℕ)
          then A.f ℓ (x * θ.E * θ.read ℓ) * θ.write ℓ else 0)
        + A.f k (hidden A 1 (θ.smallWrites 0) x k.castSucc * θ.read k) * θ.write k
        = ∑ ℓ : Fin L, if (ℓ : ℕ) < (k.succ : ℕ)
          then A.f ℓ (x * θ.E * θ.read ℓ) * θ.write ℓ else 0 := by
      rw [hidden_smallWrites_zero_swo A θ hA, Fin.val_succ, Fin.val_castSucc]
      exact (sum_ite_lt_succ_swo (fun ℓ => A.f ℓ (x * θ.E * θ.read ℓ) * θ.write ℓ) k).symm
    rw [hv] at h2
    exact h2

/-- Helper: the term of order `τ` of the output at `θ_τ`, when every `f_ℓ` is continuous at the
limit pre-activation `x E W_read^ℓ`. -/
private theorem hasDerivAt_eval_smallWrites_swo (hA : A.χ = id) (x : Matrix T dIn ℝ)
    (hc : ∀ ℓ, ContinuousAt (A.f ℓ) (x * θ.E * θ.read ℓ)) :
    HasDerivAt (fun τ : ℝ => eval A 1 (θ.smallWrites τ) x)
      ((∑ ℓ, A.f ℓ (x * θ.E * θ.read ℓ) * θ.write ℓ) * θ.D) 0 := by
  -- the derivative of the last hidden state: every block is before `L`
  have hL := hasDerivAt_hidden_smallWrites_swo A θ hA x hc (Fin.last L)
  have hsum : (∑ ℓ : Fin L, if (ℓ : ℕ) < ((Fin.last L : Fin (L + 1)) : ℕ)
      then A.f ℓ (x * θ.E * θ.read ℓ) * θ.write ℓ else 0)
        = ∑ ℓ, A.f ℓ (x * θ.E * θ.read ℓ) * θ.write ℓ :=
    Finset.sum_congr rfl fun ℓ _ => by simp only [Fin.val_last, ℓ.isLt, ↓reduceIte]
  rw [hsum] at hL
  -- the output is `h_L D`, and `y ↦ y D` is linear
  have hc := (mulRightCLM_swo (p := T) θ.D).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hL
  simp only [eval, hA, id_eq, smallWrites_D_swo]
  exact hc

/-! ### Helpers: derivatives in the parameters -/

omit [DecidableEq d] in
/-- Helper: the derivative of `θ' ↦ x E' D'` at `θ` along `v` is `x v_E D + x E v_D`. -/
private theorem hasFDerivAt_xED_swo (x : Matrix T dIn ℝ) :
    ∃ g' : Params A dIn dOut →L[ℝ] Matrix T dOut ℝ,
      HasFDerivAt (fun θ' : Params A dIn dOut => x * θ'.E * θ'.D) g' θ ∧
        ∀ v, g' v = x * v.E * θ.D + x * θ.E * v.D := by
  obtain ⟨a', ha, hav⟩ := hasFDerivAt_mul_swo (hasFDerivAt_const x θ) (clmE_swo A).hasFDerivAt
  have hxE : HasFDerivAt (fun θ' : Params A dIn dOut => x * θ'.E) a' θ := ha
  obtain ⟨b', hb, hbv⟩ := hasFDerivAt_mul_swo hxE (clmD_swo A).hasFDerivAt
  refine ⟨b', hb, fun v => ?_⟩
  rw [hbv, hav]
  simp only [clmE_swo_apply, clmD_swo_apply, _root_.zero_apply, Matrix.zero_mul, zero_add]

omit [DecidableEq d] in
/-- Helper: the derivative of the term `θ' ↦ f_ℓ(x E' W'_read) W'_write` of block `ℓ` at `θ`
along `v`, when `f_ℓ` is differentiable at `x E W_read^ℓ`. -/
private theorem hasFDerivAt_block_swo (x : Matrix T dIn ℝ) (ℓ : Fin L)
    (hf : DifferentiableAt ℝ (A.f ℓ) (x * θ.E * θ.read ℓ)) :
    ∃ g' : Params A dIn dOut →L[ℝ] Matrix T d ℝ,
      HasFDerivAt (fun θ' : Params A dIn dOut => A.f ℓ (x * θ'.E * θ'.read ℓ) * θ'.write ℓ) g' θ ∧
        ∀ v, g' v = fderiv ℝ (A.f ℓ) (x * θ.E * θ.read ℓ)
            (x * v.E * θ.read ℓ + x * θ.E * v.read ℓ) * θ.write ℓ
          + A.f ℓ (x * θ.E * θ.read ℓ) * v.write ℓ := by
  -- `θ' ↦ x E'` and `θ' ↦ x E' W'_read`
  obtain ⟨a', ha, hav⟩ := hasFDerivAt_mul_swo (hasFDerivAt_const x θ) (clmE_swo A).hasFDerivAt
  have hxE : HasFDerivAt (fun θ' : Params A dIn dOut => x * θ'.E) a' θ := ha
  obtain ⟨b', hb, hbv⟩ := hasFDerivAt_mul_swo hxE (clmRead_swo A ℓ).hasFDerivAt
  have hxER : HasFDerivAt (fun θ' : Params A dIn dOut => x * θ'.E * θ'.read ℓ) b' θ := hb
  -- the chain rule through `f_ℓ`
  have hfl : HasFDerivAt (A.f ℓ) (fderiv ℝ (A.f ℓ) (x * θ.E * θ.read ℓ))
      (x * θ.E * θ.read ℓ) := hf.hasFDerivAt
  have hc := hfl.comp θ hxER
  have hc' : HasFDerivAt (fun θ' : Params A dIn dOut => A.f ℓ (x * θ'.E * θ'.read ℓ))
      ((fderiv ℝ (A.f ℓ) (x * θ.E * θ.read ℓ)).comp b') θ := hc
  -- the product with `W'_write`
  obtain ⟨c', hcw, hcv⟩ := hasFDerivAt_mul_swo hc' (clmWrite_swo A ℓ).hasFDerivAt
  refine ⟨c', hcw, fun v => ?_⟩
  rw [hcv, ContinuousLinearMap.comp_apply, hbv, hav]
  simp only [clmE_swo_apply, clmRead_swo_apply, clmWrite_swo_apply, _root_.zero_apply,
    Matrix.zero_mul, zero_add]

omit [DecidableEq d] in
/-- Helper: the derivative of `θ' ↦ (∑_ℓ f_ℓ(x E' W'_read) W'_write) D'` at `θ` along `v`, when
every `f_ℓ` is differentiable at `x E W_read^ℓ`. -/
private theorem hasFDerivAt_sumD_swo (x : Matrix T dIn ℝ)
    (hf : ∀ ℓ, DifferentiableAt ℝ (A.f ℓ) (x * θ.E * θ.read ℓ)) :
    ∃ g' : Params A dIn dOut →L[ℝ] Matrix T dOut ℝ,
      HasFDerivAt (fun θ' : Params A dIn dOut =>
          (∑ ℓ, A.f ℓ (x * θ'.E * θ'.read ℓ) * θ'.write ℓ) * θ'.D) g' θ ∧
        ∀ v, g' v = (∑ ℓ, (fderiv ℝ (A.f ℓ) (x * θ.E * θ.read ℓ)
            (x * v.E * θ.read ℓ + x * θ.E * v.read ℓ) * θ.write ℓ
          + A.f ℓ (x * θ.E * θ.read ℓ) * v.write ℓ)) * θ.D
          + (∑ ℓ, A.f ℓ (x * θ.E * θ.read ℓ) * θ.write ℓ) * v.D := by
  choose B hB hBv using fun ℓ => hasFDerivAt_block_swo A θ x ℓ (hf ℓ)
  have hs : HasFDerivAt (fun θ' : Params A dIn dOut =>
      ∑ ℓ, A.f ℓ (x * θ'.E * θ'.read ℓ) * θ'.write ℓ) (∑ ℓ, B ℓ) θ :=
    HasFDerivAt.fun_sum fun ℓ _ => hB ℓ
  obtain ⟨g', hg, hgv⟩ := hasFDerivAt_mul_swo hs (clmD_swo A).hasFDerivAt
  refine ⟨g', hg, fun v => ?_⟩
  rw [hgv, _root_.sum_apply]
  simp only [hBv, clmD_swo_apply]

/-! ### Helpers: the maps of the small-parameter lemma -/

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the components of a difference of parameters. -/
@[simp] private theorem sub_E_swo (v w : Params A dIn dOut) : (v - w).E = v.E - w.E := rfl

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
@[simp] private theorem sub_D_swo (v w : Params A dIn dOut) : (v - w).D = v.D - w.D := rfl

/-- Helper: the part `π η = (0, η_read, η_write, 0)` of a direction that the small-parameter lemma
divides by `τ`, as a linear map. -/
private def linPi_swo : Params A dIn dOut →ₗ[ℝ] Params A dIn dOut where
  toFun η := ⟨0, η.read, η.write, 0⟩
  map_add' _ _ := Params.ext' (add_zero 0).symm (fun _ => rfl) (fun _ => rfl) (add_zero 0).symm
  map_smul' c _ := Params.ext' (smul_zero c).symm (fun _ => rfl) (fun _ => rfl) (smul_zero c).symm

/-- Helper: `π` as a continuous linear map. -/
private noncomputable def clmPi_swo : Params A dIn dOut →L[ℝ] Params A dIn dOut :=
  LinearMap.toContinuousLinearMap (linPi_swo A)

omit [Fintype T] [DecidableEq d] in
@[simp] private theorem clmPi_swo_E (η : Params A dIn dOut) : (clmPi_swo A η).E = 0 := rfl

omit [Fintype T] [DecidableEq d] in
@[simp] private theorem clmPi_swo_read (η : Params A dIn dOut) (ℓ : Fin L) :
    (clmPi_swo A η).read ℓ = η.read ℓ := rfl

omit [Fintype T] [DecidableEq d] in
@[simp] private theorem clmPi_swo_write (η : Params A dIn dOut) (ℓ : Fin L) :
    (clmPi_swo A η).write ℓ = η.write ℓ := rfl

omit [Fintype T] [DecidableEq d] in
@[simp] private theorem clmPi_swo_D (η : Params A dIn dOut) : (clmPi_swo A η).D = 0 := rfl

/-- Helper: the writes `η ↦ (0, 0, η_write, 0)`, as a linear map. -/
private def linW_swo : Params A dIn dOut →ₗ[ℝ] Params A dIn dOut where
  toFun η := ⟨0, fun _ => 0, η.write, 0⟩
  map_add' _ _ := Params.ext' (add_zero 0).symm (fun _ => (add_zero 0).symm) (fun _ => rfl)
    (add_zero 0).symm
  map_smul' c _ := Params.ext' (smul_zero c).symm (fun _ => (smul_zero c).symm) (fun _ => rfl)
    (smul_zero c).symm

/-- Helper: `θ' ↦ θ'_τ` as a linear map, for a fixed `τ`. -/
private def linSmall_swo (τ : ℝ) : Params A dIn dOut →ₗ[ℝ] Params A dIn dOut where
  toFun θ' := θ'.smallWrites τ
  map_add' _ _ := Params.ext' rfl (fun _ => rfl) (fun _ => smul_add τ _ _) rfl
  map_smul' c _ := Params.ext' rfl (fun _ => rfl) (fun _ => smul_comm τ c _) rfl

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: `θ'_τ = (θ' - W θ') + τ W θ'`, with `W θ' = (0, 0, θ'_write, 0)`. -/
private theorem smallWrites_eq_swo (τ : ℝ) (θ' : Params A dIn dOut) :
    θ'.smallWrites τ = (θ' - linW_swo A θ') + τ • linW_swo A θ' := by
  refine Params.ext' ?_ (fun ℓ => ?_) (fun ℓ => ?_) ?_
  · show θ'.E = θ'.E - 0 + τ • 0
    rw [sub_zero, smul_zero, add_zero]
  · show θ'.read ℓ = θ'.read ℓ - 0 + τ • 0
    rw [sub_zero, smul_zero, add_zero]
  · show τ • θ'.write ℓ = θ'.write ℓ - θ'.write ℓ + τ • θ'.write ℓ
    rw [sub_self, zero_add]
  · show θ'.D = θ'.D - 0 + τ • 0
    rw [sub_zero, smul_zero, add_zero]

/-- **Proof of Lemma A.30, the rank at `θ_τ` on a batch:** blocks without normalization, `f_ℓ`
twice continuously differentiable on the open set `V ℓ`, a batch `X` with
`x E W_read^ℓ ∈ V ℓ`. For all small `τ ≠ 0` the pre-activations on the batch at `θ_τ` lie in the
`V ℓ`, and if every direction `η` with `(J_0 η)(x) = 0` on the batch lies in a subspace `W`, the
Jacobian of the residual network on the batch at `θ_τ` has rank at least `P − dim W`. -/
theorem eventually_jacobianRank_smallWrites_ge_of_contDiffOn (hA : A.χ = id)
    (V : ∀ ℓ, Set (Matrix T (A.r ℓ) ℝ)) (hVo : ∀ ℓ, IsOpen (V ℓ))
    (hf : ∀ ℓ, ContDiffOn ℝ 2 (A.f ℓ) (V ℓ))
    {n : ℕ} (X : Fin n → Matrix T dIn ℝ) (hX : ∀ i ℓ, X i * θ.E * θ.read ℓ ∈ V ℓ)
    (W : Submodule ℝ (Params A dIn dOut))
    (hW : ∀ η : Params A dIn dOut, (∀ i, smallWritesLimit A θ η (X i) = 0) → η ∈ W) :
    ∀ᶠ τ in 𝓝[≠] (0 : ℝ),
      (∀ i ℓ, hidden A 1 (θ.smallWrites τ) (X i) ℓ.castSucc * θ.read ℓ ∈ V ℓ) ∧
      Module.finrank ℝ (Params A dIn dOut)
        ≤ jacobianRank A 1 X (θ.smallWrites τ) + Module.finrank ℝ W := by
  -- `f_ℓ` is continuous and differentiable at the points of `V ℓ`
  have hfc : ∀ ℓ z, z ∈ V ℓ → ContinuousAt (A.f ℓ) z := fun ℓ z hz =>
    ((hf ℓ).contDiffAt ((hVo ℓ).mem_nhds hz)).continuousAt
  have hfd : ∀ ℓ z, z ∈ V ℓ → DifferentiableAt ℝ (A.f ℓ) z := fun ℓ z hz =>
    ((hf ℓ).contDiffAt ((hVo ℓ).mem_nhds hz)).differentiableAt (by norm_num)
  -- at `τ = 0` every hidden state is `x E`, so the pre-activations at `θ_0` are the `x E W_read^ℓ`
  have hX0 : ∀ i ℓ, hidden A 1 (θ.smallWrites 0) (X i) ℓ.castSucc
      * (θ.smallWrites 0).read ℓ ∈ V ℓ := by
    intro i ℓ
    rw [hidden_smallWrites_zero_swo A θ hA, smallWrites_read_swo]
    exact hX i ℓ
  -- the pre-activations at `θ_τ` are continuous in `τ` at `0`, so they stay in the `V ℓ`
  have hpre : ∀ᶠ τ in 𝓝 (0 : ℝ), ∀ i ℓ,
      hidden A 1 (θ.smallWrites τ) (X i) ℓ.castSucc * θ.read ℓ ∈ V ℓ := by
    refine eventually_all.2 fun i => eventually_all.2 fun ℓ => ?_
    have hd := hasDerivAt_hidden_smallWrites_swo A θ hA (X i) (fun ℓ => hfc ℓ _ (hX i ℓ))
      ℓ.castSucc
    have hc : ContinuousAt
        (fun τ : ℝ => hidden A 1 (θ.smallWrites τ) (X i) ℓ.castSucc * θ.read ℓ) 0 :=
      continuousAt_mul_swo hd.continuousAt continuousAt_const
    exact hc.eventually_mem ((hVo ℓ).mem_nhds (hX0 i ℓ))
  -- `G τ θ'` is the batch of outputs at `θ'_τ`
  set G : ℝ → Params A dIn dOut → (Fin n → Matrix T dOut ℝ) :=
    fun τ θ' => evalBatch A 1 X (θ'.smallWrites τ) with hGdef
  -- `(τ, θ') ↦ G τ θ'` is `C²` near `(0, θ)`: `θ'_τ = (θ' - W θ') + τ W θ'` is smooth in `(τ, θ')`
  have hGc : ContDiffAt ℝ 2 (fun p : ℝ × Params A dIn dOut => G p.1 p.2) ((0 : ℝ), θ) := by
    let Wl := LinearMap.toContinuousLinearMap (linW_swo A (dIn := dIn) (dOut := dOut))
    have hS : ContDiff ℝ 2 (fun p : ℝ × Params A dIn dOut => (p.2 - Wl p.2) + p.1 • Wl p.2) :=
      (contDiff_snd.sub (Wl.contDiff.comp contDiff_snd)).add
        (contDiff_fst.smul (Wl.contDiff.comp contDiff_snd))
    have hE : ContDiffAt ℝ 2 (evalBatch A 1 X) ((θ - Wl θ) + (0 : ℝ) • Wl θ) := by
      have h := contDiffAt_evalBatch_swo A hA 1 V hVo hf (θ.smallWrites 0) X hX0
      rw [smallWrites_eq_swo A 0 θ] at h
      exact h
    have hc := hE.comp ((0 : ℝ), θ) hS.contDiffAt
    have hfun : (fun p : ℝ × Params A dIn dOut => G p.1 p.2)
        = evalBatch A 1 X ∘ (fun p : ℝ × Params A dIn dOut => (p.2 - Wl p.2) + p.1 • Wl p.2) := by
      funext p
      show evalBatch A 1 X (p.2.smallWrites p.1) = evalBatch A 1 X ((p.2 - Wl p.2) + p.1 • Wl p.2)
      rw [smallWrites_eq_swo A p.1 p.2]
      rfl
    rw [hfun]
    exact hc
  obtain ⟨U, hU, hGU⟩ := hGc.contDiffOn (m := 2) le_rfl (by simp)
  -- `G 0 θ' = (X_i E' D')_i` for every `θ'`, and its derivative at `θ`
  have hG0 : G 0 = fun θ' i => X i * θ'.E * θ'.D := by
    funext θ' i
    exact eval_smallWrites_zero A θ' hA (X i)
  choose a' ha ha' using fun i => hasFDerivAt_xED_swo A θ (dOut := dOut) (X i)
  have hD0 : ∀ v, fderiv ℝ (G 0) θ v = fun i => X i * v.E * θ.D + X i * θ.E * v.D := by
    intro v
    have hd : HasFDerivAt (G 0) (ContinuousLinearMap.pi a') θ := by
      rw [hG0]
      exact hasFDerivAt_pi.2 ha
    rw [hd.fderiv]
    funext i
    exact ha' i v
  -- near `θ` the limit pre-activations `X_i E' W'_read` stay in the `V ℓ`, so there
  -- `∂_τ G(0, θ') = ((∑_ℓ f_ℓ(X_i E' W'_read) W'_write) D')_i`
  have hnear : ∀ᶠ θ' in 𝓝 θ, ∀ i ℓ, X i * θ'.E * θ'.read ℓ ∈ V ℓ := by
    refine eventually_all.2 fun i => eventually_all.2 fun ℓ => ?_
    have hE : ContDiffAt ℝ 0 (fun θ' : Params A dIn dOut => θ'.E) θ :=
      (clmE_swo A (dIn := dIn) (dOut := dOut)).contDiff.contDiffAt
    have hR : ContDiffAt ℝ 0 (fun θ' : Params A dIn dOut => θ'.read ℓ) θ :=
      (clmRead_swo A (dIn := dIn) (dOut := dOut) ℓ).contDiff.contDiffAt
    have hc : ContDiffAt ℝ 0 (fun θ' : Params A dIn dOut => X i * θ'.E * θ'.read ℓ) θ :=
      contDiffAt_mul_swo (contDiffAt_mul_swo contDiffAt_const hE) hR
    exact hc.continuousAt.eventually_mem ((hVo ℓ).mem_nhds (hX i ℓ))
  have hG1 : (fun θ' => deriv (fun τ => G τ θ') 0)
      =ᶠ[𝓝 θ] fun θ' i => (∑ ℓ, A.f ℓ (X i * θ'.E * θ'.read ℓ) * θ'.write ℓ) * θ'.D := by
    filter_upwards [hnear] with θ' hθ'
    have hd : HasDerivAt (fun τ => G τ θ')
        (fun i => (∑ ℓ, A.f ℓ (X i * θ'.E * θ'.read ℓ) * θ'.write ℓ) * θ'.D) 0 :=
      hasDerivAt_pi.2 fun i =>
        hasDerivAt_eval_smallWrites_swo A θ' hA (X i) (fun ℓ => hfc ℓ _ (hθ' i ℓ))
    exact hd.deriv
  choose b' hb hb' using fun i =>
    hasFDerivAt_sumD_swo A θ (dOut := dOut) (X i) (fun ℓ => hfd ℓ _ (hX i ℓ))
  have hD1 : ∀ v, fderiv ℝ (fun θ' => deriv (fun τ => G τ θ') 0) θ v
      = fun i => (∑ ℓ, (fderiv ℝ (A.f ℓ) (X i * θ.E * θ.read ℓ)
            (X i * v.E * θ.read ℓ + X i * θ.E * v.read ℓ) * θ.write ℓ
          + A.f ℓ (X i * θ.E * θ.read ℓ) * v.write ℓ)) * θ.D
          + (∑ ℓ, A.f ℓ (X i * θ.E * θ.read ℓ) * θ.write ℓ) * v.D := by
    intro v
    have hd : HasFDerivAt (fun θ' => deriv (fun τ => G τ θ') 0)
        (ContinuousLinearMap.pi b') θ :=
      (hasFDerivAt_pi.2 hb).congr_of_eventuallyEq hG1
    rw [hd.fderiv]
    funext i
    exact hb' i v
  -- `G 0` does not move along `π η = (0, η_read, η_write, 0)`
  have h0 : ∀ η, fderiv ℝ (G 0) θ (clmPi_swo A η) = 0 := by
    intro η
    rw [hD0]
    funext i
    simp only [clmPi_swo_E, clmPi_swo_D, Matrix.mul_zero, Matrix.zero_mul, add_zero,
      Pi.zero_apply]
  -- the limit `D_θ G(0, θ)(η - π η) + D_θ(∂_τ G(0, ·))(θ)(π η)` is `((J_0 η)(X_i))_i`, so its
  -- kernel is flat for `J_0` on the batch, hence in `W`
  have hV' : ∀ η, fderiv ℝ (G 0) θ (η - clmPi_swo A η)
      + fderiv ℝ (fun θ' => deriv (fun τ => G τ θ') 0) θ (clmPi_swo A η) = 0 → η ∈ W := by
    intro η hη
    rw [hD0, hD1] at hη
    refine hW η (fun i => ?_)
    have hi := congrFun hη i
    simp only [Pi.add_apply, Pi.zero_apply] at hi
    refine Eq.trans ?_ hi
    simp only [smallWritesLimit, sub_E_swo, sub_D_swo, clmPi_swo_E, clmPi_swo_D, clmPi_swo_read,
      clmPi_swo_write, sub_zero, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
      Matrix.mul_add, Matrix.sum_mul, Matrix.mul_assoc]
  -- the small-parameter lemma, for `G` smooth on `U`
  have key := eventually_finrank_le_of_small_parameter_of_contDiffOn G θ U hU hGU (clmPi_swo A)
    h0 W hV'
  -- `D_θ G(τ, θ) = J(θ_τ) ∘ S_τ`, so its rank is at most the rank of the Jacobian at `θ_τ`
  filter_upwards [key, hpre.filter_mono nhdsWithin_le_nhds] with τ hτ hp
  refine ⟨hp, hτ.trans (Nat.add_le_add_right ?_ _)⟩
  let S := LinearMap.toContinuousLinearMap (linSmall_swo A (dIn := dIn) (dOut := dOut) τ)
  have hEv : DifferentiableAt ℝ (evalBatch A 1 X) (S θ) :=
    (contDiffAt_evalBatch_swo A hA 1 V hVo hf (θ.smallWrites τ) X hp).differentiableAt
      (by norm_num)
  have hcomp : HasFDerivAt (G τ) ((fderiv ℝ (evalBatch A 1 X) (S θ)).comp S) θ := by
    have hc := hEv.hasFDerivAt.comp θ S.hasFDerivAt
    exact hc
  have hrank : Module.finrank ℝ (LinearMap.range (fderiv ℝ (G τ) θ).toLinearMap)
      ≤ jacobianRank A 1 X (θ.smallWrites τ) := by
    rw [hcomp.fderiv]
    exact Submodule.finrank_mono (LinearMap.range_comp_le_range _ _)
  exact hrank

/-- **Proof of Lemma A.30, "Near such parameters the signs on the batch do not change" and the
lower semicontinuity of the rank:** blocks without normalization, any stream matrices, `f_ℓ`
continuously differentiable on the open set `V ℓ`, and parameters `θ` at which the
pre-activations on a batch `X` lie in the `V ℓ`. At every `θ'` near `θ` they still do, and the
rank of the Jacobian on the batch is at least its value at `θ`. -/
theorem eventually_jacobianRank_ge_of_contDiffOn (hA : A.χ = id) (S : Fin L → Matrix d d ℝ)
    (V : ∀ ℓ, Set (Matrix T (A.r ℓ) ℝ)) (hVo : ∀ ℓ, IsOpen (V ℓ))
    (hf : ∀ ℓ, ContDiffOn ℝ 1 (A.f ℓ) (V ℓ))
    {n : ℕ} (X : Fin n → Matrix T dIn ℝ)
    (hX : ∀ i ℓ, hidden A S θ (X i) ℓ.castSucc * θ.read ℓ ∈ V ℓ) :
    ∀ᶠ θ' in 𝓝 θ,
      (∀ i ℓ, hidden A S θ' (X i) ℓ.castSucc * θ'.read ℓ ∈ V ℓ) ∧
      jacobianRank A S X θ ≤ jacobianRank A S X θ' := by
  sorry

end Skips
