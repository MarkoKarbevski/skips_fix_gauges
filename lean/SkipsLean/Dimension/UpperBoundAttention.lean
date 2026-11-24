import SkipsLean.Symmetry.AttentionHeads
import SkipsLean.Dimension.UpperBoundRMSNorm
import SkipsLean.Residual.UpperBoundSymmetries
import SkipsLean.Generic.Params

/-!
# The upper bounds for networks of attention blocks

Paper (dimension paper): Theorem 4.3 (Upper bound): "Without normalization or under
pre-RMSNorm, at generic parameters, the functional dimension of a network of `L` blocks is at
most `P − (L + 1) dim 𝒢 − s`", for attention blocks: `s = 2 H d_h²` per block (Appendix B), with
Lemma B.1 for "attention blocks whose heads have width `d_h ≤ d_model` and total width
`H d_h ≥ d_model`", `d_in ≥ d_model`. Paper (skips paper): Theorem 4.2 (Upper bounds), with
identity skips: `P − dim 𝒢 − s`.

Stated here for `Arch.attention` (`Network/Attention.lean`), any mask, with
`s = 2 ∑_ℓ H_ℓ d_{h,ℓ}²`, as the bounds for the other kinds of block
(`Dimension/RescalingGate.lean`, `Residual/UpperBoundSymmetries.lean`): at one parameter under
the rank conditions of Lemma B.1, and at almost every parameter. Without skips: `E` and the
writes of rank `d`, the query and value matrices of every head of rank `d_h`; generic for
`d_in ≥ d`, `d_h ≤ d`, `H d_h ≥ d`. With identity skips the writes are not needed, and neither is
`H d_h ≥ d`. Under pre-RMSNorm (any `ε`) the changes of basis of the hidden states are the
antisymmetric directions, `dim 𝒢 = d(d−1)/2`.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {sees : T → T → Prop} [DecidableRel sees]
variable {H dh : Fin L → Type} [∀ ℓ, Fintype (H ℓ)] [∀ ℓ, Fintype (dh ℓ)]
  [∀ ℓ, DecidableEq (dh ℓ)]

/-- Helper: `Γ ↦ headDirQK θ Γ` is linear. -/
private noncomputable def headDirQKLin_uba {χ : Matrix T d ℝ → Matrix T d ℝ}
    (θ : Params (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut) :
    (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) →ₗ[ℝ]
      Params (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut where
  toFun := headDirQK θ
  map_add' Γ Δ := by
    apply Params.ext'
    · simp [headDirQK]
    · intro ℓ
      ext a ⟨i, k | k | k⟩
      · simp only [headDirQK, Params.add_read, Matrix.add_apply, Matrix.of_apply, Pi.add_apply,
          mul_add, Finset.sum_add_distrib]
      · simp only [headDirQK, Params.add_read, Matrix.add_apply, Matrix.of_apply, Pi.add_apply,
          mul_add, Finset.sum_add_distrib, neg_add]
      · simp [headDirQK]
    · intro ℓ
      simp [headDirQK]
    · simp [headDirQK]
  map_smul' c Γ := by
    apply Params.ext'
    · simp [headDirQK]
    · intro ℓ
      ext a ⟨i, k | k | k⟩
      · simp only [headDirQK, Params.smul_read, Matrix.smul_apply, Matrix.of_apply, Pi.smul_apply,
          smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => by ring
      · simp only [headDirQK, Params.smul_read, Matrix.smul_apply, Matrix.of_apply, Pi.smul_apply,
          smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_neg]
        exact congrArg Neg.neg (Finset.sum_congr rfl fun _ _ => by ring)
      · simp [headDirQK]
    · intro ℓ
      simp [headDirQK]
    · simp [headDirQK]

/-- Helper: `Γ' ↦ headDirVO θ Γ'` is linear. -/
private noncomputable def headDirVOLin_uba {χ : Matrix T d ℝ → Matrix T d ℝ}
    (θ : Params (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut) :
    (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) →ₗ[ℝ]
      Params (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut where
  toFun := headDirVO θ
  map_add' Γ Δ := by
    apply Params.ext'
    · simp [headDirVO]
    · intro ℓ
      ext a ⟨i, k | k | k⟩
      · simp [headDirVO]
      · simp [headDirVO]
      · simp only [headDirVO, Params.add_read, Matrix.add_apply, Matrix.of_apply, Pi.add_apply,
          mul_add, Finset.sum_add_distrib]
    · intro ℓ
      ext p b
      simp only [headDirVO, Params.add_write, Matrix.add_apply, Matrix.of_apply, Pi.add_apply,
        add_mul, Finset.sum_add_distrib, neg_add]
    · simp [headDirVO]
  map_smul' c Γ := by
    apply Params.ext'
    · simp [headDirVO]
    · intro ℓ
      ext a ⟨i, k | k | k⟩
      · simp [headDirVO]
      · simp [headDirVO]
      · simp only [headDirVO, Params.smul_read, Matrix.smul_apply, Matrix.of_apply, Pi.smul_apply,
          smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => by ring
    · intro ℓ
      ext p b
      simp only [headDirVO, Params.smul_write, Matrix.smul_apply, Matrix.of_apply, Pi.smul_apply,
        smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_neg]
      exact congrArg Neg.neg (Finset.sum_congr rfl fun _ _ => by ring)
    · simp [headDirVO]

omit [∀ ℓ, DecidableEq (dh ℓ)] in
/-- Helper: the families `Γ` of `d_h × d_h` matrices, one for each head of each block, form a
space of dimension `∑_ℓ H_ℓ d_{h,ℓ}²`. -/
private theorem finrank_headFun_uba :
    Module.finrank ℝ (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)
      = ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2 := by
  rw [Module.finrank_pi_fintype]
  simp only [Module.finrank_pi_fintype, Module.finrank_matrix, Module.finrank_self, mul_one,
    Finset.sum_const, Finset.card_univ, smul_eq_mul, sq]

/-- **Theorem 4.3 for attention blocks, without normalization, under the conditions of
Lemma B.1:** `fd ≤ P − (L + 1) d² − 2 ∑_ℓ H_ℓ d_{h,ℓ}²`. -/
theorem funDim_add_le_skipless_attention
    (θ : Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut)
    (hE : θ.E.rank = Fintype.card d) (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d)
    (hQ : ∀ ℓ (i : H ℓ), ((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k)).rank
      = Fintype.card (dh ℓ))
    (hV : ∀ ℓ (i : H ℓ),
      ((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))).rank
        = Fintype.card (dh ℓ)) :
    funDim (Arch.attention sees id H dh) 0 θ
        + ((L + 1) * Fintype.card d ^ 2
          + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
      ≤ Module.finrank ℝ (Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut) := by
  -- the linear map `(X, Γ, Γ') ↦ cobDir θ X + headDirQK θ Γ + headDirVO θ Γ'`
  let Φ := (cobDirLin θ).coprod ((headDirQKLin_uba θ).coprod (headDirVOLin_uba θ))
  -- its directions are flat, since the three summands are
  have hflat : LinearMap.range Φ ≤ flat (Arch.attention sees id H dh) 0 θ := by
    rintro _ ⟨p, rfl⟩
    rw [LinearMap.coprod_apply, LinearMap.coprod_apply]
    exact Submodule.add_mem _ (cobDir_mem_flat_skipless' θ rfl p.1)
      (Submodule.add_mem _ (headDirQK_mem_flat θ 0 p.2.1) (headDirVO_mem_flat θ 0 p.2.2))
  -- it is injective (Lemma B.1)
  have hinj : Function.Injective Φ := by
    intro p q hpq
    rw [LinearMap.coprod_apply, LinearMap.coprod_apply, LinearMap.coprod_apply,
      LinearMap.coprod_apply, ← add_assoc, ← add_assoc] at hpq
    exact cobDir_add_headDirQK_add_headDirVO_injective θ hE hw hQ hV hpq
  -- the domain has dimension `(L + 1) d² + 2 ∑_ℓ H_ℓ d_{h,ℓ}²`
  have h := funDim_add_finrank_le_of_le_flat' θ _ hflat
  rwa [LinearMap.finrank_range_of_inj hinj, Module.finrank_prod, Module.finrank_prod,
    finrank_cobDomain, finrank_headFun_uba, ← two_mul] at h

/-- **Theorem 4.3 for attention blocks, under pre-RMSNorm, under the conditions of Lemma B.1:**
`fd ≤ P − (L + 1) d(d−1)/2 − 2 ∑_ℓ H_ℓ d_{h,ℓ}²`. -/
theorem funDim_add_le_skipless_attention_rmsNorm (ε : ℝ)
    (θ : Params (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut)
    (hE : θ.E.rank = Fintype.card d) (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d)
    (hQ : ∀ ℓ (i : H ℓ), ((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k)).rank
      = Fintype.card (dh ℓ))
    (hV : ∀ ℓ (i : H ℓ),
      ((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))).rank
        = Fintype.card (dh ℓ)) :
    funDim (Arch.attention sees (rmsNorm ε) H dh) 0 θ
        + ((L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2)
          + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
      ≤ Module.finrank ℝ
          (Params (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut) := by
  -- the linear map `(X, Γ, Γ') ↦ cobDir θ X + headDirQK θ Γ + headDirVO θ Γ'`, with
  -- antisymmetric `X_ℓ`
  let Φ : ((Fin (L + 1) → antisymmetric d) × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)
        × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)) →ₗ[ℝ]
      Params (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut :=
    ((cobDirLin θ).comp (LinearMap.compLeft (antisymmetric d).subtype (Fin (L + 1)))).coprod
      ((headDirQKLin_uba θ).coprod (headDirVOLin_uba θ))
  -- its directions are flat, since the three summands are
  have hflat : LinearMap.range Φ ≤ flat (Arch.attention sees (rmsNorm ε) H dh) 0 θ := by
    rintro _ ⟨p, rfl⟩
    rw [LinearMap.coprod_apply, LinearMap.coprod_apply]
    exact Submodule.add_mem _
      (cobDir_mem_flat_skipless_rmsNorm' θ ε rfl (fun ℓ => (p.1 ℓ : Matrix d d ℝ))
        fun ℓ => (p.1 ℓ).2)
      (Submodule.add_mem _ (headDirQK_mem_flat θ 0 p.2.1) (headDirVO_mem_flat θ 0 p.2.2))
  -- it is injective (Lemma B.1)
  have hinj : Function.Injective Φ := by
    intro p q hpq
    rw [LinearMap.coprod_apply, LinearMap.coprod_apply, LinearMap.coprod_apply,
      LinearMap.coprod_apply, ← add_assoc, ← add_assoc] at hpq
    have h' : cobDir θ (fun ℓ => (p.1 ℓ : Matrix d d ℝ)) + headDirQK θ p.2.1
          + headDirVO θ p.2.2
        = cobDir θ (fun ℓ => (q.1 ℓ : Matrix d d ℝ)) + headDirQK θ q.2.1
          + headDirVO θ q.2.2 := hpq
    have h2 : ((fun ℓ => (p.1 ℓ : Matrix d d ℝ)), p.2.1, p.2.2) =
        ((fun ℓ => (q.1 ℓ : Matrix d d ℝ)), q.2.1, q.2.2) :=
      cobDir_add_headDirQK_add_headDirVO_injective θ hE hw hQ hV h'
    have h3 := Prod.mk.inj h2
    exact Prod.ext (funext fun ℓ => Subtype.ext (congrFun h3.1 ℓ)) h3.2
  -- the domain has dimension `(L + 1) d (d - 1) / 2 + 2 ∑_ℓ H_ℓ d_{h,ℓ}²`
  have hdim : Module.finrank ℝ ((Fin (L + 1) → antisymmetric d)
        × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)) =
      (L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2)
        + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2 := by
    rw [Module.finrank_prod, Module.finrank_prod,
      Module.finrank_pi_fintype (R := ℝ) (ι := Fin (L + 1)) (M := fun _ => antisymmetric d),
      finrank_antisymmetric, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
      finrank_headFun_uba, ← two_mul]
  have h := funDim_add_finrank_le_of_le_flat' θ _ hflat
  rwa [LinearMap.finrank_range_of_inj hinj, hdim] at h

/-- Helper (the private `cancel_left_of_rank_ubs` of `Residual/UpperBoundSymmetries.lean`): a
matrix `M` of rank equal to its number of columns cancels on the left, `M X = M Y → X = Y` (its
kernel is `0` by rank–nullity). -/
private theorem cancel_left_of_rank_uba {m n k : Type*} [Fintype n] (M : Matrix m n ℝ)
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

omit [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] [∀ ℓ, DecidableEq (dh ℓ)] in
/-- Helper: if the query and the value matrix of every head have rank `d_h`, the direction
`headDirQK θ Γ + headDirVO θ Γ'` determines `Γ` and `Γ'`: the query columns of head `i` move by
`W_{Q,i} Γ_i`, its value columns by `W_{V,i} Γ'_i`. -/
private theorem headDirLin_injective_uba {χ : Matrix T d ℝ → Matrix T d ℝ}
    (θ : Params (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut)
    (hQ : ∀ ℓ (i : H ℓ), ((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k)).rank
      = Fintype.card (dh ℓ))
    (hV : ∀ ℓ (i : H ℓ),
      ((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))).rank
        = Fintype.card (dh ℓ)) :
    Function.Injective ((headDirQKLin_uba θ).coprod (headDirVOLin_uba θ)) := by
  rintro ⟨Γ, Γ'⟩ ⟨Δ, Δ'⟩ h
  have h' : headDirQK θ Γ + headDirVO θ Γ' = headDirQK θ Δ + headDirVO θ Δ' := h
  -- the entry `(a, p)` of the read of block `ℓ`
  have hr : ∀ ℓ a p, (headDirQK θ Γ + headDirVO θ Γ').read ℓ a p
      = (headDirQK θ Δ + headDirVO θ Δ').read ℓ a p := fun ℓ a p => by rw [h']
  refine Prod.ext ?_ ?_ <;> funext ℓ i
  · -- the query columns of head `i`: `W_{Q,i} Γ_i = W_{Q,i} Δ_i`, and `W_{Q,i}` has rank `d_h`
    refine cancel_left_of_rank_uba _ (hQ ℓ i) (Matrix.ext fun a k => ?_)
    have := hr ℓ a (i, Sum.inl k)
    simp only [Params.add_read, Matrix.add_apply, headDirQK, headDirVO, Matrix.of_apply,
      add_zero] at this
    simpa only [Matrix.mul_apply, Matrix.submatrix_apply, id] using this
  · -- the value columns of head `i`: `W_{V,i} Γ'_i = W_{V,i} Δ'_i`
    refine cancel_left_of_rank_uba _ (hV ℓ i) (Matrix.ext fun a k => ?_)
    have := hr ℓ a (i, Sum.inr (Sum.inr k))
    simp only [Params.add_read, Matrix.add_apply, headDirQK, headDirVO, Matrix.of_apply,
      zero_add] at this
    simpa only [Matrix.mul_apply, Matrix.submatrix_apply, id] using this

/-- Helper (the private `funDim_add_le_of_cobConst_add` of `Residual/UpperBoundSymmetries.lean`):
the bound from one change of basis and the symmetries inside the blocks. Let
`ι : W → Matrix d d ℝ` be linear and injective, and `ρ : V → Params` linear and injective with
`E` component `0`. If the directions `cobDir θ (fun _ => ι w)` and `ρ v` are flat and `E` has
rank `d`, then `fd ≤ P - dim W - dim V`. -/
private theorem funDim_add_le_of_cobConst_add_uba {A : Arch T d L} (θ : Params A dIn dOut)
    {W V : Type*} [AddCommGroup W] [Module ℝ W]
    [FiniteDimensional ℝ W] [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (ι : W →ₗ[ℝ] Matrix d d ℝ) (hι : Function.Injective ι)
    (ρ : V →ₗ[ℝ] Params A dIn dOut) (hρ : Function.Injective ρ) (hρE : ∀ v, (ρ v).E = 0)
    (hE : θ.E.rank = Fintype.card d)
    (hcob : ∀ w, cobDir θ (fun _ => ι w) ∈ flat A 1 θ) (hflat : ∀ v, ρ v ∈ flat A 1 θ) :
    funDim A 1 θ + (Module.finrank ℝ W + Module.finrank ℝ V)
      ≤ Module.finrank ℝ (Params A dIn dOut) := by
  -- the linear map `(w, v) ↦ cobDir θ (fun _ => ι w) + ρ v`
  let Φ : W × V →ₗ[ℝ] Params A dIn dOut :=
    ((cobDirLin θ).comp (LinearMap.pi fun _ : Fin (L + 1) => ι)).coprod ρ
  have hΦ : ∀ w v, Φ (w, v) = cobDir θ (fun _ => ι w) + ρ v := fun _ _ => rfl
  -- its directions are flat, since both summands are
  have hV : LinearMap.range Φ ≤ flat A 1 θ := by
    rintro _ ⟨⟨w, v⟩, rfl⟩
    rw [hΦ]
    exact Submodule.add_mem _ (hcob w) (hflat v)
  -- it is injective: the `E` component `E ι(w)` gives `w`, since `E` has rank `d`; then `ρ v`
  -- gives `v`
  have hinj : Function.Injective Φ := by
    rintro ⟨w, v⟩ ⟨w', v'⟩ h
    rw [hΦ, hΦ] at h
    have h0 : θ.E * ι w = θ.E * ι w' := by
      have hE0 := congrArg Params.E h
      rw [Params.add_E, Params.add_E, hρE, hρE, add_zero, add_zero] at hE0
      exact hE0
    obtain rfl : w = w' := hι (cancel_left_of_rank_uba θ.E hE h0)
    exact Prod.ext rfl (hρ (add_left_cancel h))
  have h := funDim_add_finrank_le_of_le_flat' θ _ hV
  rwa [LinearMap.finrank_range_of_inj hinj, Module.finrank_prod] at h

/-- **Theorem 4.2 of the skips paper with identity skips, for attention blocks, without
normalization:** if `E` has rank `d` and the query and value matrices of every head have rank
`d_h`, `fd ≤ P − d² − 2 ∑_ℓ H_ℓ d_{h,ℓ}²`. -/
theorem funDim_add_le_residual_attention
    (θ : Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut)
    (hE : θ.E.rank = Fintype.card d)
    (hQ : ∀ ℓ (i : H ℓ), ((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k)).rank
      = Fintype.card (dh ℓ))
    (hV : ∀ ℓ (i : H ℓ),
      ((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))).rank
        = Fintype.card (dh ℓ)) :
    funDim (Arch.attention sees id H dh) 1 θ
        + (Fintype.card d ^ 2 + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
      ≤ Module.finrank ℝ (Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut) := by
  -- the flat directions `cobDir θ (fun _ => X) + headDirQK θ Γ + headDirVO θ Γ'`, of dimension
  -- `d² + 2 ∑_ℓ H_ℓ d_{h,ℓ}²`
  have h := funDim_add_le_of_cobConst_add_uba θ LinearMap.id Function.injective_id
    ((headDirQKLin_uba θ).coprod (headDirVOLin_uba θ)) (headDirLin_injective_uba θ hQ hV)
    (fun _ => show (0 : Matrix dIn d ℝ) + 0 = 0 from add_zero 0) hE
    (fun X => cobDir_const_mem_flat_residual' θ rfl X)
    (fun p => Submodule.add_mem _ (headDirQK_mem_flat θ 1 p.1) (headDirVO_mem_flat θ 1 p.2))
  rwa [Module.finrank_matrix, Module.finrank_self, mul_one, ← sq, Module.finrank_prod,
    finrank_headFun_uba, ← two_mul] at h

/-- **Theorem 4.2 of the skips paper with identity skips, for attention blocks, under
pre-RMSNorm:** `fd ≤ P − d(d−1)/2 − 2 ∑_ℓ H_ℓ d_{h,ℓ}²`. -/
theorem funDim_add_le_residual_attention_rmsNorm (ε : ℝ)
    (θ : Params (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut)
    (hE : θ.E.rank = Fintype.card d)
    (hQ : ∀ ℓ (i : H ℓ), ((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k)).rank
      = Fintype.card (dh ℓ))
    (hV : ∀ ℓ (i : H ℓ),
      ((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))).rank
        = Fintype.card (dh ℓ)) :
    funDim (Arch.attention sees (rmsNorm ε) H dh) 1 θ
        + (Fintype.card d * (Fintype.card d - 1) / 2
          + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
      ≤ Module.finrank ℝ
          (Params (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut) := by
  -- the same directions, with `X` antisymmetric
  have h := funDim_add_le_of_cobConst_add_uba θ (antisymmetric d).subtype
    (antisymmetric d).injective_subtype
    ((headDirQKLin_uba θ).coprod (headDirVOLin_uba θ)) (headDirLin_injective_uba θ hQ hV)
    (fun _ => show (0 : Matrix dIn d ℝ) + 0 = 0 from add_zero 0) hE
    (fun X => cobDir_const_mem_flat_residual_rmsNorm' θ ε rfl (X : Matrix d d ℝ) X.2)
    (fun p => Submodule.add_mem _ (headDirQK_mem_flat θ 1 p.1) (headDirVO_mem_flat θ 1 p.2))
  rwa [finrank_antisymmetric, Module.finrank_prod, finrank_headFun_uba, ← two_mul] at h

omit [Fintype T] [DecidableEq d] in
/-- Helper (the private `analyticOnNhd_det` of `Generic/Params.lean`): the determinant of a square
matrix that depends linearly on the parameters is an analytic function of the parameters. -/
private theorem analyticOnNhd_det_uba {A : Arch T d L} {n : Type*} [Fintype n] [DecidableEq n]
    (Φ : Params A dIn dOut →ₗ[ℝ] Matrix n n ℝ) :
    AnalyticOnNhd ℝ (fun θ => (Φ θ).det) Set.univ := by
  simp only [Matrix.det_apply']
  exact Finset.analyticOnNhd_fun_sum _ fun σ _ => analyticOnNhd_const.mul
    (Finset.analyticOnNhd_fun_prod _ fun i _ =>
      analyticOnNhd_linear ((Matrix.entryLinearMap ℝ ℝ (σ i) i).comp Φ))

/-- Helper: a matrix whose submatrix on the rows `r` and the columns `c` (both injective) is the
identity. -/
private theorem exists_submatrix_eq_one_uba {m p n : Type*} [DecidableEq n] {r : n → m}
    (hr : Function.Injective r) {c : n → p} (hc : Function.Injective c) :
    ∃ M : Matrix m p ℝ, M.submatrix r c = 1 := by
  classical
  refine ⟨Matrix.of fun a b => if ∃ x, r x = a ∧ c x = b then 1 else 0, ?_⟩
  ext x y
  simp [Matrix.one_apply, hr.eq_iff, hc.eq_iff]

omit [Fintype T] [DecidableEq d] in
/-- Helper: at generic parameters, `n ≤ d` distinct columns `c` of the read of block `ℓ` form a
matrix of rank `n`: some `n` of its rows form a matrix that is invertible at generic parameters. -/
private theorem ae_rank_read_cols_uba {A : Arch T d L} (μ : Measure (Params A dIn dOut))
    [μ.IsAddHaarMeasure] (ℓ : Fin L) {n : Type*} [Fintype n] [DecidableEq n] {c : n → A.r ℓ}
    (hc : Function.Injective c) (hn : Fintype.card n ≤ Fintype.card d) :
    ∀ᵐ θ ∂μ, ((θ.read ℓ).submatrix id c).rank = Fintype.card n := by
  -- `n` rows `ρ`, and the square submatrix of the read on the rows `ρ` and the columns `c`
  obtain ⟨ρ⟩ := Function.Embedding.nonempty_of_card_le hn
  obtain ⟨M, hM⟩ := exists_submatrix_eq_one_uba ρ.injective hc
  let Φ : Params A dIn dOut →ₗ[ℝ] Matrix n n ℝ :=
    { toFun := fun θ => ((θ.read ℓ).submatrix id c).submatrix ρ id
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  -- it is the identity at the parameter whose read `ℓ` is `M`, so its determinant is not
  -- identically zero, and it is nonzero almost everywhere
  have hne : ∃ θ, (Φ θ).det ≠ 0 := by
    refine ⟨⟨0, Pi.single ℓ M, 0, 0⟩, ?_⟩
    show ((Pi.single (M := fun ℓ => Matrix d (A.r ℓ) ℝ) ℓ M ℓ).submatrix ρ c).det ≠ 0
    rw [Pi.single_eq_same, hM, Matrix.det_one]
    exact one_ne_zero
  filter_upwards [ae_ne_zero_of_analytic μ (analyticOnNhd_det_uba Φ) hne] with θ hθ
  -- an invertible `n × n` submatrix gives rank `≥ n`, and the rank is at most the width `n`
  have h1 : (((θ.read ℓ).submatrix id c).submatrix ρ id).rank = Fintype.card n :=
    Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hθ))
  have h2 : (((θ.read ℓ).submatrix id c).submatrix ρ id).rank
      ≤ ((θ.read ℓ).submatrix id c).rank :=
    Matrix.rank_submatrix_le _ ρ id
  have h3 := Matrix.rank_le_card_width ((θ.read ℓ).submatrix id c)
  omega

omit [DecidableEq d] in
/-- Helper: at generic parameters the query matrix and the value matrix of every head have rank
`d_h`, when `d_h ≤ d`. -/
theorem ae_rank_QV_uba {χ : Matrix T d ℝ → Matrix T d ℝ}
    (μ : Measure (Params (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut))
    [μ.IsAddHaarMeasure] (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) :
    ∀ᵐ θ ∂μ, (∀ ℓ (i : H ℓ), ((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k)).rank
        = Fintype.card (dh ℓ)) ∧
      ∀ ℓ (i : H ℓ), ((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))).rank
        = Fintype.card (dh ℓ) := by
  -- finitely many conditions, two for each head of each block
  refine (ae_all_iff.2 fun ℓ => ae_all_iff.2 fun i => ?_).and
    (ae_all_iff.2 fun ℓ => ae_all_iff.2 fun i => ?_)
  · exact ae_rank_read_cols_uba μ ℓ (c := fun k : dh ℓ => (i, Sum.inl k))
      (fun _ _ h => Sum.inl_injective (Prod.mk.inj h).2) (hdh ℓ)
  · exact ae_rank_read_cols_uba μ ℓ (c := fun k : dh ℓ => (i, Sum.inr (Sum.inr k)))
      (fun _ _ h => Sum.inr_injective (Sum.inr_injective (Prod.mk.inj h).2)) (hdh ℓ)

/-- Helper (the private `ae_rank_E` of `Generic/Params.lean`): at generic parameters `E` has rank
`d`, when `d_in ≥ d`. -/
private theorem ae_rank_E_uba {A : Arch T d L} (μ : Measure (Params A dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn) :
    ∀ᵐ θ ∂μ, θ.E.rank = Fintype.card d := by
  -- `d` rows `ρ` of `E`, invertible at generic parameters
  obtain ⟨ρ⟩ := Function.Embedding.nonempty_of_card_le hdIn
  filter_upwards [ae_isUnit_det_submatrix μ] with θ hθ
  have h1 : (θ.E.submatrix ρ id).rank = Fintype.card d :=
    Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).2 (hθ.2.2.1 ρ))
  have h2 := Matrix.rank_submatrix_le θ.E ρ id
  have h3 := Matrix.rank_le_card_width θ.E
  omega

/-- **Theorem 4.3 for attention blocks at generic parameters, without normalization:** for
`d_in ≥ d`, heads of width `d_h ≤ d` and total width `H d_h ≥ d` in every block. -/
theorem ae_funDim_add_le_skipless_attention
    (μ : Measure (Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d)
    (hH : ∀ ℓ, Fintype.card d ≤ Fintype.card (H ℓ) * Fintype.card (dh ℓ)) :
    ∀ᵐ θ ∂μ, funDim (Arch.attention sees id H dh) 0 θ
        + ((L + 1) * Fintype.card d ^ 2
          + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
      ≤ Module.finrank ℝ (Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut) := by
  -- the writes have `H_ℓ d_{h,ℓ} ≥ d` rows
  have hw : ∀ ℓ, Fintype.card d
      ≤ Fintype.card ((Arch.attention (T := T) (d := d) sees id H dh).w ℓ) := fun ℓ => by
    show Fintype.card d ≤ Fintype.card (H ℓ × dh ℓ)
    rw [Fintype.card_prod]
    exact hH ℓ
  -- the pointwise bound holds wherever `E` and the writes have rank `d` and the query and the
  -- value matrix of every head have rank `d_h`
  filter_upwards [ae_rank_E_write μ hdIn hw, ae_rank_QV_uba μ hdh] with θ h1 h2
  exact funDim_add_le_skipless_attention θ h1.1 h1.2 h2.1 h2.2

/-- **Theorem 4.3 for attention blocks at generic parameters, under pre-RMSNorm.** -/
theorem ae_funDim_add_le_skipless_attention_rmsNorm (ε : ℝ)
    (μ : Measure (Params (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d)
    (hH : ∀ ℓ, Fintype.card d ≤ Fintype.card (H ℓ) * Fintype.card (dh ℓ)) :
    ∀ᵐ θ ∂μ, funDim (Arch.attention sees (rmsNorm ε) H dh) 0 θ
        + ((L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2)
          + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
      ≤ Module.finrank ℝ
          (Params (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut) := by
  -- the writes have `H_ℓ d_{h,ℓ} ≥ d` rows
  have hw : ∀ ℓ, Fintype.card d
      ≤ Fintype.card ((Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh).w ℓ) :=
    fun ℓ => by
      show Fintype.card d ≤ Fintype.card (H ℓ × dh ℓ)
      rw [Fintype.card_prod]
      exact hH ℓ
  filter_upwards [ae_rank_E_write μ hdIn hw, ae_rank_QV_uba μ hdh] with θ h1 h2
  exact funDim_add_le_skipless_attention_rmsNorm ε θ h1.1 h1.2 h2.1 h2.2

/-- **Theorem 4.2 of the skips paper with identity skips, for attention blocks at generic
parameters, without normalization:** for `d_in ≥ d` and heads of width `d_h ≤ d`. -/
theorem ae_funDim_add_le_residual_attention
    (μ : Measure (Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) :
    ∀ᵐ θ ∂μ, funDim (Arch.attention sees id H dh) 1 θ
        + (Fintype.card d ^ 2 + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
      ≤ Module.finrank ℝ (Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut) := by
  -- the pointwise bound holds wherever `E` has rank `d` and the query and the value matrix of
  -- every head have rank `d_h`
  filter_upwards [ae_rank_E_uba μ hdIn, ae_rank_QV_uba μ hdh] with θ h1 h2
  exact funDim_add_le_residual_attention θ h1 h2.1 h2.2

/-- **Theorem 4.2 of the skips paper with identity skips, for attention blocks at generic
parameters, under pre-RMSNorm.** -/
theorem ae_funDim_add_le_residual_attention_rmsNorm (ε : ℝ)
    (μ : Measure (Params (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) :
    ∀ᵐ θ ∂μ, funDim (Arch.attention sees (rmsNorm ε) H dh) 1 θ
        + (Fintype.card d * (Fintype.card d - 1) / 2
          + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
      ≤ Module.finrank ℝ
          (Params (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut) := by
  filter_upwards [ae_rank_E_uba μ hdIn, ae_rank_QV_uba μ hdh] with θ h1 h2
  exact funDim_add_le_residual_attention_rmsNorm ε θ h1 h2.1 h2.2

end Skips
