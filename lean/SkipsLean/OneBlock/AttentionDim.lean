import SkipsLean.OneBlock.AttentionStepOne
import SkipsLean.OneBlock.AttentionGeneric
import SkipsLean.Dimension.UpperBoundAttention

/-!
# The one-block theorem for an attention block: the functional dimension

Paper (dimension paper): Theorem 5.1 (Theorem C.1 in the appendix) for an attention block:
"Let `d_model ≥ 2` and `d_in, d_out ≥ d_model`, let inputs range over all of `ℝ^{T × d_in}`, and
consider networks with one block, without normalization and without biases. The block is […] an
attention block of `H` heads of width `d_h ≤ d_model` with `H d_h ≥ d_model`, causal or not, on
sequences of at least two tokens. At generic parameters the functional dimension is
`P − 2 d_model² − s`", with `s = 2 H d_h²` for an attention block. Its proof, Step 3: "So
`dim K(θ) = 2 d_model² + 2 H d_h²`, and the functional dimension `P − dim K(θ)` is the value of
the theorem."

Paper (skips paper): Theorem B.1 (i) for an attention block, without biases: "Let the network
have no normalization […] and let the block have width at least `d_model`, where the width of an
attention block is `H d_h`. For generic parameters the skipless network has functional dimension
`P − 2 d_model² − s` and the residual network `P − d_model² − s` […] and the skip raises the
functional dimension by exactly `d_model²`." Its proof for the residual network: a direction that
keeps `M = E D` and every `B_i`, `C_i` has `E (X − Y) D = 0`, so `X = Y`, one change of basis.

Here, from Steps 1 and 2 (`OneBlock/Attention.lean`, `OneBlock/AttentionStepOne.lean`), the
upper bounds (`Dimension/UpperBoundAttention.lean`) and the conditions at generic parameters
(`OneBlock/AttentionGeneric.lean`), for a mask with a token `t₂` that sees itself and another
token `t₁` (two tokens at least; causal or not):

* the flat directions of the skipless and of the residual network of one attention block;
* `fd = P − 2 d² − 2 H d_h²` without the skip and `fd = P − d² − 2 H d_h²` with it, under the
  conditions of the proof and at almost every parameter;
* the skip raises the functional dimension by exactly `d²` at almost every parameter.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {sees : T → T → Prop} [DecidableRel sees]
variable {H dh : Fin 1 → Type} [∀ ℓ, Fintype (H ℓ)] [∀ ℓ, Fintype (dh ℓ)]

/-- Helper (copy of the private `headDirQKLin_uba` of `Dimension/UpperBoundAttention.lean`):
`Γ ↦ headDirQK θ Γ` is linear. -/
private noncomputable def headDirQKLin_obd
    (θ : Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut) :
    (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) →ₗ[ℝ]
      Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut where
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

/-- Helper (copy of the private `headDirVOLin_uba` of `Dimension/UpperBoundAttention.lean`):
`Γ' ↦ headDirVO θ Γ'` is linear. -/
private noncomputable def headDirVOLin_obd
    (θ : Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut) :
    (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) →ₗ[ℝ]
      Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut where
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

/-- Helper (copy of the private `finrank_headFun_uba`): the families `Γ` of `d_h × d_h`
matrices, one for each head of the one block, form a space of dimension `H d_h²`. -/
private theorem finrank_headFun_obd :
    Module.finrank ℝ (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)
      = Fintype.card (H 0) * Fintype.card (dh 0) ^ 2 := by
  rw [Module.finrank_pi_fintype]
  simp only [Module.finrank_pi_fintype, Module.finrank_matrix, Module.finrank_self, mul_one,
    Finset.sum_const, Finset.card_univ, smul_eq_mul, sq, Fin.sum_univ_one]

/-- Helper (copy of `cancel_left_of_rank_res` of `OneBlock/Residual.lean`): a matrix whose rank
is its number of columns cancels on the left, via a left inverse. -/
private theorem cancel_left_of_rank_obd {m n k : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (M : Matrix m n ℝ) (hM : M.rank = Fintype.card n) {X Y : Matrix n k ℝ}
    (h : M * X = M * Y) : X = Y := by
  obtain ⟨B, hB⟩ := Matrix.vecMul_surjective_iff_exists_left_inverse.mp
    (Matrix.vecMul_surjective_iff_rank_eq_card.mpr hM)
  have := congrArg (B * ·) h
  simpa only [← Matrix.mul_assoc, hB, Matrix.one_mul] using this

/-- Helper (copy of `cancel_right_of_rank_res` of `OneBlock/Residual.lean`): a matrix whose rank
is its number of rows cancels on the right, via a right inverse. -/
private theorem cancel_right_of_rank_obd {m n k : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    (M : Matrix m n ℝ) (hM : M.rank = Fintype.card m) {X Y : Matrix k m ℝ}
    (h : X * M = Y * M) : X = Y := by
  obtain ⟨R, hR⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.mp
    (Matrix.mulVec_surjective_iff_rank_eq_card.mpr hM)
  have := congrArg (· * R) h
  simpa only [Matrix.mul_assoc, hR, Matrix.mul_one] using this

/-- **Proof of Theorem C.1 for attention blocks, Steps 1 and 2:** under the conditions of the
proof, with a token that sees itself and another token, every flat direction of the skipless
network of one attention block is the sum of the direction of two changes of basis of the hidden
states and of the directions of the changes of basis inside the heads. -/
theorem flat_attention_oneBlock (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂)
    (hs1 : sees t₂ t₁) (θ : Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut)
    (hθ : OneBlockGenericAttention θ)
    (η : Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut)
    (hη : η ∈ flat (Arch.attention sees id H dh) 0 θ) :
    ∃ (X : Fin 2 → Matrix d d ℝ) (Γ Γ' : ∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ),
      η = cobDir θ X + headDirQK θ Γ + headDirVO θ Γ' := by
  -- Step 2 with the stream matrix `0`: `η` keeps every `B_i` and every `C_i`
  have h := (flat_attention_oneBlock_keeps 0 t₁ t₂ h12 hs2 hs1 θ hθ.exists_v η hη).2
  -- Step 1
  exact exists_cobDir_add_headDir_of_keeps θ hθ η (fun i => (h i).1) (fun i => (h i).2)

/-- **Proof of Theorem B.1 (i) of the skips paper for attention blocks, the residual network:**
under the same conditions, every flat direction of the residual network of one attention block is
the sum of the direction of one change of basis, the same at `h_0` and at `h_1`, and of the
directions of the changes of basis inside the heads. -/
theorem flat_attention_oneBlock_residual (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂)
    (hs1 : sees t₂ t₁) (θ : Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut)
    (hθ : OneBlockGenericAttention θ)
    (η : Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut)
    (hη : η ∈ flat (Arch.attention sees id H dh) 1 θ) :
    ∃ (X : Matrix d d ℝ) (Γ Γ' : ∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ),
      η = cobDir θ (fun _ => X) + headDirQK θ Γ + headDirVO θ Γ' := by
  -- Step 2 with the stream matrix `1`: `η` keeps `M = E D`, every `B_i` and every `C_i`
  obtain ⟨hM, h⟩ := flat_attention_oneBlock_keeps 1 t₁ t₂ h12 hs2 hs1 θ hθ.exists_v η hη
  -- Step 1: `η` is the direction of two changes of basis `X_0`, `X_1` and of the heads
  obtain ⟨X, Γ, Γ', rfl⟩ :=
    exists_cobDir_add_headDir_of_keeps θ hθ _ (fun i => (h i).1) (fun i => (h i).2)
  -- the head directions have `E = 0` and `D = 0`: `η_E = E X_0`, `η_D = -X_1 D`
  have hE : (cobDir θ X + headDirQK θ Γ + headDirVO θ Γ').E = θ.E * X 0 := by
    simp only [Params.add_E, cobDir, headDirQK, headDirVO, add_zero]
  have hD : (cobDir θ X + headDirQK θ Γ + headDirVO θ Γ').D = -(X 1 * θ.D) := by
    simp only [Params.add_D, cobDir, headDirQK, headDirVO, add_zero]
    rfl
  -- `∂M = E X_0 D - E X_1 D = 0`, so `X_0 = X_1` since `E` and `D` have rank `d`
  rw [hE, hD, Pi.one_apply, Matrix.mul_one, Matrix.mul_one, Matrix.mul_neg, Matrix.mul_assoc,
    add_neg_eq_zero] at hM
  have h01 : X 0 = X 1 :=
    cancel_right_of_rank_obd θ.D hθ.rank_D (cancel_left_of_rank_obd θ.E hθ.rank_E hM)
  have hX : X = fun _ => X 0 := funext (Fin.forall_fin_two.2 ⟨rfl, h01.symm⟩)
  exact ⟨X 0, Γ, Γ', by rw [← hX]⟩

/-- **Theorem C.1 for an attention block, at one parameter:** under the conditions of the proof,
with a token that sees itself and another token, the skipless network of one attention block has
`fd = P − 2 d² − 2 H d_h²`. -/
theorem funDim_attention_oneBlock (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂)
    (hs1 : sees t₂ t₁) (θ : Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut)
    (hθ : OneBlockGenericAttention θ) :
    funDim (Arch.attention sees id H dh) 0 θ
        + (2 * Fintype.card d ^ 2 + 2 * (Fintype.card (H 0) * Fintype.card (dh 0) ^ 2))
      = Module.finrank ℝ (Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut) := by
  classical
  -- `fd(θ) = P - dim K(θ)` (Appendix C)
  have hP := funDim_add_finrank_flat' (A := Arch.attention sees id H dh) (S := 0) θ
  -- the lower bound `dim K(θ) ≥ 2 d² + 2 H d_h²` (Theorem 4.3, Lemma B.1)
  have hlow := funDim_add_le_skipless_attention θ hθ.rank_E
    (fun ℓ => by obtain rfl : ℓ = 0 := Subsingleton.elim _ _; exact hθ.rank_write)
    (fun ℓ => by obtain rfl : ℓ = 0 := Subsingleton.elim _ _; exact hθ.rank_Q)
    (fun ℓ => by obtain rfl : ℓ = 0 := Subsingleton.elim _ _; exact hθ.rank_V)
  rw [Fin.sum_univ_one] at hlow
  -- the upper bound: every flat direction is `Φ (X, Γ, Γ')` (Steps 1 and 2), for the linear
  -- map `Φ (X, Γ, Γ') = cobDir θ X + headDirQK θ Γ + headDirVO θ Γ'`
  let Φ := (cobDirLin θ).coprod ((headDirQKLin_obd θ).coprod (headDirVOLin_obd θ))
  have hle : flat (Arch.attention sees id H dh) 0 θ ≤ LinearMap.range Φ := by
    intro η hη
    obtain ⟨X, Γ, Γ', rfl⟩ := flat_attention_oneBlock t₁ t₂ h12 hs2 hs1 θ hθ η hη
    exact ⟨(X, Γ, Γ'), (add_assoc _ _ _).symm⟩
  have hup := (Submodule.finrank_mono hle).trans (LinearMap.finrank_range_le Φ)
  rw [Module.finrank_prod, Module.finrank_prod, finrank_cobDomain, finrank_headFun_obd] at hup
  omega

/-- **Theorem 5.1 / C.1 for an attention block:** for `d_in, d_out ≥ d ≥ 2`, `H` heads of width
`d_h ≤ d` with `H d_h ≥ d`, and a token that sees itself and another token (two tokens at least;
causal or not), at almost every parameter the skipless network of one attention block has the
functional dimension `P − 2 d² − 2 H d_h²`. -/
theorem ae_funDim_attention_oneBlock
    (μ : Measure (Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : Fintype.card (dh 0) ≤ Fintype.card d)
    (hH : Fintype.card d ≤ Fintype.card (H 0) * Fintype.card (dh 0))
    (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ θ ∂μ, funDim (Arch.attention sees id H dh) 0 θ
        + (2 * Fintype.card d ^ 2 + 2 * (Fintype.card (H 0) * Fintype.card (dh 0) ^ 2))
      = Module.finrank ℝ (Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut) :=
  (ae_oneBlockGenericAttention μ hd hdIn hdOut hdh hH).mono fun θ hθ =>
    funDim_attention_oneBlock t₁ t₂ h12 hs2 hs1 θ hθ

/-- **Theorem B.1 (i) of the skips paper for an attention block with its skip, at one
parameter:** under the conditions of the proof, with a token that sees itself and another token,
the residual network of one attention block has `fd = P − d² − 2 H d_h²`. -/
theorem funDim_attention_oneBlock_residual (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂)
    (hs1 : sees t₂ t₁) (θ : Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut)
    (hθ : OneBlockGenericAttention θ) :
    funDim (Arch.attention sees id H dh) 1 θ
        + (Fintype.card d ^ 2 + 2 * (Fintype.card (H 0) * Fintype.card (dh 0) ^ 2))
      = Module.finrank ℝ (Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut) := by
  classical
  -- `fd(θ) = P - dim K(θ)` (Appendix C)
  have hP := funDim_add_finrank_flat' (A := Arch.attention sees id H dh) (S := 1) θ
  -- the lower bound `dim K(θ) ≥ d² + 2 H d_h²` (Theorem 4.2 of the skips paper)
  have hlow := funDim_add_le_residual_attention θ hθ.rank_E
    (fun ℓ => by obtain rfl : ℓ = 0 := Subsingleton.elim _ _; exact hθ.rank_Q)
    (fun ℓ => by obtain rfl : ℓ = 0 := Subsingleton.elim _ _; exact hθ.rank_V)
  rw [Fin.sum_univ_one] at hlow
  -- the upper bound: every flat direction is `Ψ (X, Γ, Γ')`, for the linear map
  -- `Ψ (X, Γ, Γ') = cobDir θ (fun _ => X) + headDirQK θ Γ + headDirVO θ Γ'`
  let Ψ := ((cobDirLin θ).comp (LinearMap.pi fun _ => LinearMap.id)).coprod
    ((headDirQKLin_obd θ).coprod (headDirVOLin_obd θ))
  have hle : flat (Arch.attention sees id H dh) 1 θ ≤ LinearMap.range Ψ := by
    intro η hη
    obtain ⟨X, Γ, Γ', rfl⟩ := flat_attention_oneBlock_residual t₁ t₂ h12 hs2 hs1 θ hθ η hη
    exact ⟨(X, Γ, Γ'), (add_assoc _ _ _).symm⟩
  have hup := (Submodule.finrank_mono hle).trans (LinearMap.finrank_range_le Ψ)
  rw [Module.finrank_prod, Module.finrank_prod, Module.finrank_matrix, Module.finrank_self,
    mul_one, finrank_headFun_obd] at hup
  have hsq : Fintype.card d * Fintype.card d = Fintype.card d ^ 2 := (sq _).symm
  omega

/-- **Theorem B.1 (i) of the skips paper for an attention block with its skip:** for
`d_in, d_out ≥ d ≥ 2`, `H` heads of width `d_h ≤ d` with `H d_h ≥ d`, and a token that sees
itself and another token, at almost every parameter the residual network of one attention block
has the functional dimension `P − d² − 2 H d_h²`. -/
theorem ae_funDim_attention_oneBlock_residual
    (μ : Measure (Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : Fintype.card (dh 0) ≤ Fintype.card d)
    (hH : Fintype.card d ≤ Fintype.card (H 0) * Fintype.card (dh 0))
    (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ θ ∂μ, funDim (Arch.attention sees id H dh) 1 θ
        + (Fintype.card d ^ 2 + 2 * (Fintype.card (H 0) * Fintype.card (dh 0) ^ 2))
      = Module.finrank ℝ (Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut) :=
  (ae_oneBlockGenericAttention μ hd hdIn hdOut hdh hH).mono fun θ hθ =>
    funDim_attention_oneBlock_residual t₁ t₂ h12 hs2 hs1 θ hθ

/-- **The skip raises the functional dimension by exactly `d²`** (Theorem 4.6 (i) / B.1 (i) of
the skips paper), for one attention block, at almost every parameter. -/
theorem ae_funDim_attention_oneBlock_residual_eq_add
    (μ : Measure (Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : Fintype.card (dh 0) ≤ Fintype.card d)
    (hH : Fintype.card d ≤ Fintype.card (H 0) * Fintype.card (dh 0))
    (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ θ ∂μ, funDim (Arch.attention sees id H dh) 1 θ
      = funDim (Arch.attention sees id H dh) 0 θ + Fintype.card d ^ 2 := by
  filter_upwards [ae_funDim_attention_oneBlock μ hd hdIn hdOut hdh hH t₁ t₂ h12 hs2 hs1,
    ae_funDim_attention_oneBlock_residual μ hd hdIn hdOut hdh hH t₁ t₂ h12 hs2 hs1] with θ h0 h1
  omega

end Skips
