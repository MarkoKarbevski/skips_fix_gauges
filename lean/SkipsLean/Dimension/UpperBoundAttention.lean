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
  sorry

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
  sorry

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
  sorry

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
  sorry

/-- **Theorem 4.2 of the skips paper with identity skips, for attention blocks at generic
parameters, without normalization:** for `d_in ≥ d` and heads of width `d_h ≤ d`. -/
theorem ae_funDim_add_le_residual_attention
    (μ : Measure (Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) :
    ∀ᵐ θ ∂μ, funDim (Arch.attention sees id H dh) 1 θ
        + (Fintype.card d ^ 2 + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
      ≤ Module.finrank ℝ (Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut) := by
  sorry

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
  sorry

end Skips
