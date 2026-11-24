import SkipsLean.Dimension.ExpOrbit
import SkipsLean.Symmetry.AttentionHeads

/-!
# The orbit of the symmetries of an attention network through `θ`

Paper (dimension paper): Appendix B, proof of Lemma B.1: "In an attention block, the changes of
basis inside the heads map `W_{Q,i} ↦ W_{Q,i} K_i` and `W_{V,i} ↦ W_{V,i} K'_i`" (with
`W_{K,i} ↦ W_{K,i} K_i^{-⊤}` and `W_{O,i} ↦ K'^{-1}_i W_{O,i}`); proof of Proposition 4.6: "The
changes of basis of Proposition 3.2, the rescalings and the changes of basis inside the heads form
a Lie group of dimension `k`, which acts smoothly. It acts locally freely at `θ`, so the map that
sends an element of the group to the image of `θ` under it is an immersion near the identity".

Here the orbit map for attention networks, as `Dimension/ExpOrbitGated.lean` has it for gated
blocks: `cobExpHeads θ (m, Γ, Γ')` applies the changes of basis `exp Γ_{ℓ,i}` between the queries
and keys and `exp Γ'_{ℓ,i}` between the values and outputs of every head, then the changes of
basis `exp m_ℓ` at the hidden states. It passes through `θ` at `0` and is strictly differentiable
there, with the derivative `cobDir θ m + headDirQK θ Γ + headDirVO θ Γ'`.
-/

namespace Skips

open Matrix Filter Topology
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {sees : T → T → Prop} [DecidableRel sees] {χ : Matrix T d ℝ → Matrix T d ℝ}
variable {H dh : Fin L → Type} [∀ ℓ, Fintype (H ℓ)] [∀ ℓ, Fintype (dh ℓ)]
  [∀ ℓ, DecidableEq (dh ℓ)]

/-- The parameters `((θ.headsQK (exp Γ)).headsVO (exp Γ')).cob (exp m) (exp m)` of an attention
network: the changes of basis `exp Γ_{ℓ,i}` and `exp Γ'_{ℓ,i}` inside head `i` of block `ℓ`, then
the change of basis `exp m_ℓ` at the hidden state `h_ℓ`. -/
noncomputable def cobExpHeads (θ : Params (Arch.attention sees χ H dh) dIn dOut)
    (p : (Fin (L + 1) → Matrix d d ℝ) × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)
      × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)) :
    Params (Arch.attention sees χ H dh) dIn dOut :=
  cobExp ((θ.headsQK fun ℓ i => expGL (p.2.1 ℓ i)).headsVO fun ℓ i => expGL (p.2.2 ℓ i)) p.1

variable (θ : Params (Arch.attention sees χ H dh) dIn dOut)

/-- Helper: `exp 0 = 1` in `GL`. -/
private theorem expGL_zero_eoa {n : Type*} [Fintype n] [DecidableEq n] :
    expGL (0 : Matrix n n ℝ) = 1 :=
  Units.ext (by rw [coe_expGL, NormedSpace.exp_zero, Units.val_one])

omit [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the change of basis `1` between queries and keys is the identity. -/
private theorem headsQK_one_eoa : θ.headsQK (fun _ _ => 1) = θ := by
  refine Params.ext' rfl (fun ℓ => ?_) (fun ℓ => rfl) rfl
  ext a ⟨i, k | k | k⟩
  · show ∑ k', θ.read ℓ a (i, Sum.inl k') * ((1 : GL (dh ℓ) ℝ) : Matrix (dh ℓ) (dh ℓ) ℝ) k' k
      = θ.read ℓ a (i, Sum.inl k)
    simp only [Units.val_one, Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true]
  · show ∑ k', θ.read ℓ a (i, Sum.inr (Sum.inl k'))
        * (((1 : GL (dh ℓ) ℝ)⁻¹ : GL (dh ℓ) ℝ) : Matrix (dh ℓ) (dh ℓ) ℝ) k k'
      = θ.read ℓ a (i, Sum.inr (Sum.inl k))
    simp only [inv_one, Units.val_one, Matrix.one_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  · rfl

omit [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the change of basis `1` between values and outputs is the identity. -/
private theorem headsVO_one_eoa : θ.headsVO (fun _ _ => 1) = θ := by
  refine Params.ext' rfl (fun ℓ => ?_) (fun ℓ => ?_) rfl
  · ext a ⟨i, k | k | k⟩
    · rfl
    · rfl
    · show ∑ k', θ.read ℓ a (i, Sum.inr (Sum.inr k'))
          * ((1 : GL (dh ℓ) ℝ) : Matrix (dh ℓ) (dh ℓ) ℝ) k' k
        = θ.read ℓ a (i, Sum.inr (Sum.inr k))
      simp only [Units.val_one, Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, ite_true]
  · ext ⟨i, k⟩ b
    show ∑ k', (((1 : GL (dh ℓ) ℝ)⁻¹ : GL (dh ℓ) ℝ) : Matrix (dh ℓ) (dh ℓ) ℝ) k k'
        * θ.write ℓ (i, k') b = θ.write ℓ (i, k) b
    simp only [inv_one, Units.val_one, Matrix.one_apply, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true]

omit [Fintype dIn] [Fintype dOut] in
/-- The orbit map passes through `θ` at `0`. -/
theorem cobExpHeads_zero : cobExpHeads θ 0 = θ := by
  -- `exp 0 = 1` in every head, then `exp 0 = 1` at every hidden state
  simp only [cobExpHeads, Prod.snd_zero, Prod.fst_zero, Pi.zero_apply, expGL_zero_eoa,
    headsQK_one_eoa, headsVO_one_eoa]
  exact cobExp_zero θ

/-- Helper: matrix multiplication as a continuous bilinear map. -/
private noncomputable def mulB_eoa (m n p : Type*) [Fintype m] [Fintype n] [Fintype p] :
    Matrix m n ℝ →L[ℝ] Matrix n p ℝ →L[ℝ] Matrix m p ℝ :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap :
      (Matrix n p ℝ →ₗ[ℝ] Matrix m p ℝ) ≃ₗ[ℝ] (Matrix n p ℝ →L[ℝ] Matrix m p ℝ)).toLinearMap ∘ₗ
      LinearMap.mk₂ ℝ (fun a b => a * b) Matrix.add_mul (fun c a b => Matrix.smul_mul c a b)
        Matrix.mul_add (fun c a b => Matrix.mul_smul a c b))

/-- Helper: the product rule for matrix-valued maps, strict form, with the value of the
derivative, `(f g)' v = f' v g + f g' v`. -/
private theorem hasStrictFDerivAt_mul_eoa {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m n p : Type*} [Fintype m] [Fintype n] [Fintype p] {f : E → Matrix m n ℝ}
    {g : E → Matrix n p ℝ} {f' : E →L[ℝ] Matrix m n ℝ} {g' : E →L[ℝ] Matrix n p ℝ} {y : E}
    (hf : HasStrictFDerivAt f f' y) (hg : HasStrictFDerivAt g g' y) :
    ∃ h' : E →L[ℝ] Matrix m p ℝ, HasStrictFDerivAt (fun z => f z * g z) h' y ∧
      ∀ v, h' v = f' v * g y + f y * g' v := by
  -- the derivative of the bilinear map `(a, b) ↦ a b` along `(f, g)`
  have h := (mulB_eoa m n p).hasStrictFDerivAt_of_bilinear hf hg
  refine ⟨_, h, fun v => ?_⟩
  show f y * g' v + f' v * g y = _
  exact add_comm _ _

/-- Helper: `p ↦ exp (m_ℓ)`, with derivative `v ↦ v.1 ℓ` at `0`. -/
private theorem hasStrictFDerivAt_exp_fst_eoa {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (ℓ : Fin (L + 1)) :
    ∃ D : (Fin (L + 1) → Matrix d d ℝ) × F →L[ℝ] Matrix d d ℝ,
      HasStrictFDerivAt (fun p : (Fin (L + 1) → Matrix d d ℝ) × F => NormedSpace.exp (p.1 ℓ))
        D 0 ∧ ∀ v, D v = v.1 ℓ := by
  let π := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (L + 1) => Matrix d d ℝ) ℓ).comp
    (ContinuousLinearMap.fst ℝ (Fin (L + 1) → Matrix d d ℝ) F)
  have hg : HasStrictFDerivAt (fun Y : Matrix d d ℝ => NormedSpace.exp Y)
      (ContinuousLinearMap.id ℝ (Matrix d d ℝ)) (π 0) := by
    rw [map_zero]
    exact hasStrictFDerivAt_matrix_exp_zero
  have hc := hg.comp (0 : (Fin (L + 1) → Matrix d d ℝ) × F) π.hasStrictFDerivAt
  exact ⟨_, hc, fun v => rfl⟩

/-- Helper: `p ↦ exp (-m_ℓ)`, with derivative `v ↦ -v.1 ℓ` at `0`. -/
private theorem hasStrictFDerivAt_exp_neg_fst_eoa {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (ℓ : Fin (L + 1)) :
    ∃ D : (Fin (L + 1) → Matrix d d ℝ) × F →L[ℝ] Matrix d d ℝ,
      HasStrictFDerivAt (fun p : (Fin (L + 1) → Matrix d d ℝ) × F => NormedSpace.exp (-p.1 ℓ))
        D 0 ∧ ∀ v, D v = -v.1 ℓ := by
  let π := -(ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (L + 1) => Matrix d d ℝ) ℓ).comp
    (ContinuousLinearMap.fst ℝ (Fin (L + 1) → Matrix d d ℝ) F)
  have hg : HasStrictFDerivAt (fun Y : Matrix d d ℝ => NormedSpace.exp Y)
      (ContinuousLinearMap.id ℝ (Matrix d d ℝ)) (π 0) := by
    rw [map_zero]
    exact hasStrictFDerivAt_matrix_exp_zero
  have hc := hg.comp (0 : (Fin (L + 1) → Matrix d d ℝ) × F) π.hasStrictFDerivAt
  exact ⟨_, hc, fun v => rfl⟩

/-- Helper: the entry `(a, b)` of `z ↦ exp (π z)`, for a linear map `π` into the square matrices,
with derivative `v ↦ (π v)_{a b}` at `0`. -/
private theorem hasStrictFDerivAt_exp_entry_eoa {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {n : Type*} [Fintype n] [DecidableEq n] (π : E →L[ℝ] Matrix n n ℝ)
    (a b : n) :
    ∃ D : E →L[ℝ] ℝ, HasStrictFDerivAt (fun z => NormedSpace.exp (π z) a b) D 0 ∧
      ∀ v, D v = π v a b := by
  -- `z ↦ exp (π z)` has derivative `π` at `0`, then entry by entry
  have hg : HasStrictFDerivAt (fun Y : Matrix n n ℝ => NormedSpace.exp Y)
      (ContinuousLinearMap.id ℝ (Matrix n n ℝ)) (π 0) := by
    rw [map_zero]
    exact hasStrictFDerivAt_matrix_exp_zero
  have hc := hg.comp (0 : E) π.hasStrictFDerivAt
  have he := hasStrictFDerivAt_pi'.1 (hasStrictFDerivAt_pi'.1 hc a) b
  exact ⟨_, he, fun v => rfl⟩

/-- Helper: `z ↦ ∑_{k'} c_{k'} (exp (π z))_{r k', s k'}`, with derivative
`v ↦ ∑_{k'} c_{k'} (π v)_{r k', s k'}` at `0`. -/
private theorem hasStrictFDerivAt_sum_mul_exp_eoa {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {n : Type*} [Fintype n] [DecidableEq n] (π : E →L[ℝ] Matrix n n ℝ)
    (c : n → ℝ) (r s : n → n) :
    ∃ D : E →L[ℝ] ℝ,
      HasStrictFDerivAt (fun z => ∑ k', c k' * NormedSpace.exp (π z) (r k') (s k')) D 0 ∧
      ∀ v, D v = ∑ k', c k' * π v (r k') (s k') := by
  choose D hD hDv using fun k' => hasStrictFDerivAt_exp_entry_eoa π (r k') (s k')
  refine ⟨∑ k', c k' • D k',
    HasStrictFDerivAt.fun_sum fun k' _ => (hD k').const_mul (c k'), fun v => ?_⟩
  rw [sum_apply]
  exact Finset.sum_congr rfl fun k' _ => by rw [← hDv k' v]; rfl

/-- Helper: `z ↦ ∑_{k'} (exp (π z))_{r k', s k'} c_{k'}`, with derivative
`v ↦ ∑_{k'} (π v)_{r k', s k'} c_{k'}` at `0`. -/
private theorem hasStrictFDerivAt_sum_exp_mul_eoa {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {n : Type*} [Fintype n] [DecidableEq n] (π : E →L[ℝ] Matrix n n ℝ)
    (c : n → ℝ) (r s : n → n) :
    ∃ D : E →L[ℝ] ℝ,
      HasStrictFDerivAt (fun z => ∑ k', NormedSpace.exp (π z) (r k') (s k') * c k') D 0 ∧
      ∀ v, D v = ∑ k', π v (r k') (s k') * c k' := by
  choose D hD hDv using fun k' => hasStrictFDerivAt_exp_entry_eoa π (r k') (s k')
  refine ⟨∑ k', c k' • D k',
    HasStrictFDerivAt.fun_sum fun k' _ => (hD k').mul_const (c k'), fun v => ?_⟩
  rw [sum_apply]
  exact Finset.sum_congr rfl fun k' _ => by rw [← hDv k' v, mul_comm]; rfl

omit [Fintype d] [DecidableEq d] in
/-- Helper: the projection `(m, Γ, Γ') ↦ Γ_{ℓ,i}`. -/
private noncomputable def projQ_eoa (ℓ : Fin L) (i : H ℓ) :
    (Fin (L + 1) → Matrix d d ℝ) × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)
      × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) →L[ℝ] Matrix (dh ℓ) (dh ℓ) ℝ :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : H ℓ => Matrix (dh ℓ) (dh ℓ) ℝ) i).comp
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun ℓ => H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) ℓ).comp
      ((ContinuousLinearMap.fst ℝ (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)
        (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)).comp
        (ContinuousLinearMap.snd ℝ (Fin (L + 1) → Matrix d d ℝ)
          ((∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)))))

/-- Helper: the projection `(m, Γ, Γ') ↦ Γ'_{ℓ,i}`. -/
private noncomputable def projV_eoa (ℓ : Fin L) (i : H ℓ) :
    (Fin (L + 1) → Matrix d d ℝ) × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)
      × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) →L[ℝ] Matrix (dh ℓ) (dh ℓ) ℝ :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : H ℓ => Matrix (dh ℓ) (dh ℓ) ℝ) i).comp
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun ℓ => H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) ℓ).comp
      ((ContinuousLinearMap.snd ℝ (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)
        (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)).comp
        (ContinuousLinearMap.snd ℝ (Fin (L + 1) → Matrix d d ℝ)
          ((∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)))))

omit [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the read of block `ℓ` after the changes of basis `exp Γ`, `exp Γ'` inside the heads, as
a map of `p = (m, Γ, Γ')`, with derivative `v ↦ (headDirQK θ v.2.1 + headDirVO θ v.2.2).read ℓ`
at `0`, entry by entry. -/
private theorem hasStrictFDerivAt_heads_read_eoa (ℓ : Fin L) :
    ∃ D : (Fin (L + 1) → Matrix d d ℝ) × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)
        × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) →L[ℝ] Matrix d (H ℓ × (dh ℓ ⊕ (dh ℓ ⊕ dh ℓ))) ℝ,
      HasStrictFDerivAt (fun p : (Fin (L + 1) → Matrix d d ℝ)
          × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) =>
        ((θ.headsQK fun ℓ i => expGL (p.2.1 ℓ i)).headsVO fun ℓ i => expGL (p.2.2 ℓ i)).read ℓ)
        D 0 ∧
      ∀ v, D v = (headDirQK θ v.2.1 + headDirVO θ v.2.2).read ℓ := by
  have h : ∀ (a : d) (q : H ℓ × (dh ℓ ⊕ (dh ℓ ⊕ dh ℓ))),
      ∃ D : (Fin (L + 1) → Matrix d d ℝ) × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)
          × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) →L[ℝ] ℝ,
        HasStrictFDerivAt (fun p : (Fin (L + 1) → Matrix d d ℝ)
            × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) =>
          ((θ.headsQK fun ℓ i => expGL (p.2.1 ℓ i)).headsVO fun ℓ i => expGL (p.2.2 ℓ i)).read ℓ
            a q) D 0 ∧
        ∀ v, D v = (headDirQK θ v.2.1 + headDirVO θ v.2.2).read ℓ a q := by
    rintro a ⟨i, k | k | k⟩
    · -- the queries of head `i`: `∑_{k'} W_Q a k' (exp Γ_{ℓ,i})_{k' k}`
      obtain ⟨D, hD, hDv⟩ := hasStrictFDerivAt_sum_mul_exp_eoa (projQ_eoa (d := d) ℓ i)
        (fun k' => θ.read ℓ a (i, Sum.inl k')) id (fun _ => k)
      refine ⟨D, hD, fun v => (hDv v).trans ?_⟩
      show _ = ∑ k', θ.read ℓ a (i, Sum.inl k') * v.2.1 ℓ i k' k + 0
      rw [add_zero]
      rfl
    · -- the keys of head `i`: `∑_{k'} W_K a k' (exp (-Γ_{ℓ,i}))_{k k'}`
      obtain ⟨D, hD, hDv⟩ := hasStrictFDerivAt_sum_mul_exp_eoa (-projQ_eoa (d := d) ℓ i)
        (fun k' => θ.read ℓ a (i, Sum.inr (Sum.inl k'))) (fun _ => k) id
      refine ⟨D, hD, fun v => (hDv v).trans ?_⟩
      show _ = -∑ k', θ.read ℓ a (i, Sum.inr (Sum.inl k')) * v.2.1 ℓ i k k' + 0
      rw [add_zero, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun k' _ => ?_
      show θ.read ℓ a (i, Sum.inr (Sum.inl k')) * (-(v.2.1 ℓ i)) k k' = _
      rw [Matrix.neg_apply, mul_neg]
    · -- the values of head `i`: `∑_{k'} W_V a k' (exp Γ'_{ℓ,i})_{k' k}`
      obtain ⟨D, hD, hDv⟩ := hasStrictFDerivAt_sum_mul_exp_eoa (projV_eoa (d := d) ℓ i)
        (fun k' => θ.read ℓ a (i, Sum.inr (Sum.inr k'))) id (fun _ => k)
      refine ⟨D, hD, fun v => (hDv v).trans ?_⟩
      show _ = 0 + ∑ k', θ.read ℓ a (i, Sum.inr (Sum.inr k')) * v.2.2 ℓ i k' k
      rw [zero_add]
      rfl
  choose D hD hDv using h
  exact ⟨ContinuousLinearMap.pi fun a => ContinuousLinearMap.pi fun q => D a q,
    hasStrictFDerivAt_pi.2 fun a => hasStrictFDerivAt_pi.2 fun q => hD a q,
    fun v => Matrix.ext fun a q => hDv a q v⟩

omit [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the write of block `ℓ` after the changes of basis inside the heads, as a map of
`p = (m, Γ, Γ')`, with derivative `v ↦ (headDirQK θ v.2.1 + headDirVO θ v.2.2).write ℓ` at `0`,
entry by entry. -/
private theorem hasStrictFDerivAt_heads_write_eoa (ℓ : Fin L) :
    ∃ D : (Fin (L + 1) → Matrix d d ℝ) × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)
        × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) →L[ℝ] Matrix (H ℓ × dh ℓ) d ℝ,
      HasStrictFDerivAt (fun p : (Fin (L + 1) → Matrix d d ℝ)
          × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) =>
        ((θ.headsQK fun ℓ i => expGL (p.2.1 ℓ i)).headsVO fun ℓ i => expGL (p.2.2 ℓ i)).write ℓ)
        D 0 ∧
      ∀ v, D v = (headDirQK θ v.2.1 + headDirVO θ v.2.2).write ℓ := by
  have h : ∀ (q : H ℓ × dh ℓ) (b : d),
      ∃ D : (Fin (L + 1) → Matrix d d ℝ) × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)
          × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) →L[ℝ] ℝ,
        HasStrictFDerivAt (fun p : (Fin (L + 1) → Matrix d d ℝ)
            × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) =>
          ((θ.headsQK fun ℓ i => expGL (p.2.1 ℓ i)).headsVO fun ℓ i => expGL (p.2.2 ℓ i)).write ℓ
            q b) D 0 ∧
        ∀ v, D v = (headDirQK θ v.2.1 + headDirVO θ v.2.2).write ℓ q b := by
    -- the outputs of head `i`: `∑_{k'} (exp (-Γ'_{ℓ,i}))_{k k'} W_O k' b`
    rintro ⟨i, k⟩ b
    obtain ⟨D, hD, hDv⟩ := hasStrictFDerivAt_sum_exp_mul_eoa (-projV_eoa (d := d) ℓ i)
      (fun k' => θ.write ℓ (i, k') b) (fun _ => k) id
    refine ⟨D, hD, fun v => (hDv v).trans ?_⟩
    show _ = 0 + -∑ k', v.2.2 ℓ i k k' * θ.write ℓ (i, k') b
    rw [zero_add, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k' _ => ?_
    show (-(v.2.2 ℓ i)) k k' * θ.write ℓ (i, k') b = _
    rw [Matrix.neg_apply, neg_mul]
  choose D hD hDv using h
  exact ⟨ContinuousLinearMap.pi fun q => ContinuousLinearMap.pi fun b => D q b,
    hasStrictFDerivAt_pi.2 fun q => hasStrictFDerivAt_pi.2 fun b => hD q b,
    fun v => Matrix.ext fun q b => hDv q b v⟩

omit [Fintype dOut] [∀ ℓ, DecidableEq (dh ℓ)] in
/-- Helper: the embedding `E exp (m_0)`, with derivative `v ↦ E v.1 0` at `0`. -/
private theorem hasStrictFDerivAt_E_eoa :
    ∃ D : (Fin (L + 1) → Matrix d d ℝ) × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)
        × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) →L[ℝ] Matrix dIn d ℝ,
      HasStrictFDerivAt (fun p : (Fin (L + 1) → Matrix d d ℝ)
          × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) =>
        θ.E * NormedSpace.exp (p.1 0)) D 0 ∧
      ∀ v, D v = (cobDir θ v.1 + headDirQK θ v.2.1 + headDirVO θ v.2.2).E := by
  obtain ⟨g', hg, hgv⟩ := hasStrictFDerivAt_exp_fst_eoa (d := d)
    (F := (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)) 0
  obtain ⟨D, hD, hDv⟩ := hasStrictFDerivAt_mul_eoa (hasStrictFDerivAt_const θ.E
    (0 : (Fin (L + 1) → Matrix d d ℝ) × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)
      × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ))) hg
  refine ⟨D, hD, fun v => ?_⟩
  -- `0 exp 0 + E v.1 0`, against `E v.1 0 + 0 + 0`
  refine (hDv v).trans ?_
  erw [hgv]
  show (0 : Matrix dIn d ℝ) * _ + θ.E * v.1 0 = θ.E * v.1 0 + 0 + 0
  rw [Matrix.zero_mul, zero_add, add_zero, add_zero]

omit [Fintype dIn] [Fintype dOut] in
/-- Helper: the read of block `ℓ`, `exp (-m_{ℓ-1}) R_ℓ(Γ, Γ')`, with derivative
`v ↦ -v.1 (ℓ-1) W_read + (headDirQK θ v.2.1 + headDirVO θ v.2.2).read ℓ` at `0` (product rule). -/
private theorem hasStrictFDerivAt_read_eoa (ℓ : Fin L) :
    ∃ D : (Fin (L + 1) → Matrix d d ℝ) × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)
        × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) →L[ℝ] Matrix d (H ℓ × (dh ℓ ⊕ (dh ℓ ⊕ dh ℓ))) ℝ,
      HasStrictFDerivAt (fun p : (Fin (L + 1) → Matrix d d ℝ)
          × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) =>
        NormedSpace.exp (-p.1 ℓ.castSucc)
          * ((θ.headsQK fun ℓ i => expGL (p.2.1 ℓ i)).headsVO fun ℓ i => expGL (p.2.2 ℓ i)).read ℓ)
        D 0 ∧
      ∀ v, D v = (cobDir θ v.1 + headDirQK θ v.2.1 + headDirVO θ v.2.2).read ℓ := by
  obtain ⟨f', hf, hfv⟩ := hasStrictFDerivAt_exp_neg_fst_eoa (d := d)
    (F := (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)) ℓ.castSucc
  obtain ⟨g', hg, hgv⟩ := hasStrictFDerivAt_heads_read_eoa θ ℓ
  obtain ⟨D, hD, hDv⟩ := hasStrictFDerivAt_mul_eoa hf hg
  refine ⟨D, hD, fun v => ?_⟩
  -- at `0` the factors are `exp 0 = 1` and `θ.read ℓ`
  refine (hDv v).trans ?_
  erw [hfv, hgv]
  simp only [Prod.fst_zero, Prod.snd_zero, Pi.zero_apply, neg_zero, NormedSpace.exp_zero,
    expGL_zero_eoa, headsQK_one_eoa, headsVO_one_eoa, Matrix.one_mul, Params.add_read,
    Matrix.neg_mul, add_assoc]
  rfl

omit [Fintype dIn] [Fintype dOut] in
/-- Helper: the write of block `ℓ`, `W_ℓ(Γ') exp (m_ℓ)`, with derivative
`v ↦ (headDirQK θ v.2.1 + headDirVO θ v.2.2).write ℓ + W_write v.1 ℓ` at `0` (product rule). -/
private theorem hasStrictFDerivAt_write_eoa (ℓ : Fin L) :
    ∃ D : (Fin (L + 1) → Matrix d d ℝ) × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)
        × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) →L[ℝ] Matrix (H ℓ × dh ℓ) d ℝ,
      HasStrictFDerivAt (fun p : (Fin (L + 1) → Matrix d d ℝ)
          × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) =>
        ((θ.headsQK fun ℓ i => expGL (p.2.1 ℓ i)).headsVO fun ℓ i => expGL (p.2.2 ℓ i)).write ℓ
          * NormedSpace.exp (p.1 ℓ.succ)) D 0 ∧
      ∀ v, D v = (cobDir θ v.1 + headDirQK θ v.2.1 + headDirVO θ v.2.2).write ℓ := by
  obtain ⟨f', hf, hfv⟩ := hasStrictFDerivAt_heads_write_eoa θ ℓ
  obtain ⟨g', hg, hgv⟩ := hasStrictFDerivAt_exp_fst_eoa (d := d)
    (F := (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)) ℓ.succ
  obtain ⟨D, hD, hDv⟩ := hasStrictFDerivAt_mul_eoa hf hg
  refine ⟨D, hD, fun v => ?_⟩
  -- at `0` the factors are `θ.write ℓ` and `exp 0 = 1`
  refine (hDv v).trans ?_
  erw [hfv, hgv]
  simp only [Prod.fst_zero, Prod.snd_zero, Pi.zero_apply, NormedSpace.exp_zero, expGL_zero_eoa,
    headsQK_one_eoa, headsVO_one_eoa, Matrix.mul_one, Params.add_write]
  -- `(QK + VO) + W v.1 ℓ`, against `W v.1 ℓ + QK + VO`
  rw [add_comm]
  exact (add_assoc _ _ _).symm

omit [Fintype dIn] [∀ ℓ, DecidableEq (dh ℓ)] in
/-- Helper: the readout `exp (-m_L) D`, with derivative `v ↦ -v.1 L D` at `0`. -/
private theorem hasStrictFDerivAt_D_eoa :
    ∃ D : (Fin (L + 1) → Matrix d d ℝ) × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)
        × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) →L[ℝ] Matrix d dOut ℝ,
      HasStrictFDerivAt (fun p : (Fin (L + 1) → Matrix d d ℝ)
          × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) =>
        NormedSpace.exp (-p.1 (Fin.last L)) * θ.D) D 0 ∧
      ∀ v, D v = (cobDir θ v.1 + headDirQK θ v.2.1 + headDirVO θ v.2.2).D := by
  obtain ⟨f', hf, hfv⟩ := hasStrictFDerivAt_exp_neg_fst_eoa (d := d)
    (F := (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)) (Fin.last L)
  obtain ⟨D, hD, hDv⟩ := hasStrictFDerivAt_mul_eoa hf (hasStrictFDerivAt_const θ.D
    (0 : (Fin (L + 1) → Matrix d d ℝ) × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)
      × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)))
  refine ⟨D, hD, fun v => ?_⟩
  -- `-v.1 L D + exp 0 0`, against `-(v.1 L D) + 0 + 0`
  refine (hDv v).trans ?_
  erw [hfv]
  show -v.1 (Fin.last L) * θ.D + _ * (0 : Matrix d dOut ℝ) = -(v.1 (Fin.last L) * θ.D) + 0 + 0
  rw [Matrix.mul_zero, Matrix.neg_mul, add_zero, add_zero]

/-- The orbit map `(m, Γ, Γ') ↦ cobExpHeads θ (m, Γ, Γ')` is strictly differentiable at `0`, with
the derivative `(m, Γ, Γ') ↦ cobDir θ m + headDirQK θ Γ + headDirVO θ Γ'`. -/
theorem hasStrictFDerivAt_cobExpHeads :
    ∃ Φ' : ((Fin (L + 1) → Matrix d d ℝ) × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)
          × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)) →L[ℝ]
        Params (Arch.attention sees χ H dh) dIn dOut,
      HasStrictFDerivAt (cobExpHeads θ) Φ' 0
        ∧ ∀ p, Φ' p = cobDir θ p.1 + headDirQK θ p.2.1 + headDirVO θ p.2.2 := by
  -- the four components: `E exp(m_0)`, `exp(-m_{ℓ-1}) R_ℓ(Γ, Γ')`, `W_ℓ(Γ') exp(m_ℓ)`,
  -- `exp(-m_L) D`
  obtain ⟨DE, hE, hEv⟩ := hasStrictFDerivAt_E_eoa θ
  choose DR hR hRv using hasStrictFDerivAt_read_eoa θ
  choose DW hW hWv using hasStrictFDerivAt_write_eoa θ
  obtain ⟨DD, hD, hDv⟩ := hasStrictFDerivAt_D_eoa θ
  -- the tuple of the components is strictly differentiable, hence so is the map into `Params`
  have key :=
    hE.prodMk ((hasStrictFDerivAt_pi.2 hR).prodMk ((hasStrictFDerivAt_pi.2 hW).prodMk hD))
  let e := (Params.linearEquivProd (A := Arch.attention sees χ H dh) (dIn := dIn)
    (dOut := dOut)).toContinuousLinearEquiv
  have hc := e.symm.hasStrictFDerivAt.comp
    (0 : (Fin (L + 1) → Matrix d d ℝ) × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)
      × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)) key
  exact ⟨_, hc, fun v => Params.ext' (hEv v) (fun ℓ => hRv ℓ v) (fun ℓ => hWv ℓ v) (hDv v)⟩

end Skips
