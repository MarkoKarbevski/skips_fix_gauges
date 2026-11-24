import SkipsLean.OneBlock.ResidualRMSZeroGain
import SkipsLean.Absorb.RMSNormAttention
import SkipsLean.Absorb.AttentionBlock

/-!
# One block under pre-RMSNorm with `ε = 0`: the gain of the skip for the five kinds of block

Paper (skips paper), Theorem B.1 (v): "Let the network be pre-RMSNorm with `ε = 0`, without biases,
with a tanh, GELU, SwiGLU, GeGLU or attention block. For generic parameters the skip raises the
functional dimension by at least `d_model (d_model − 1)/2 + 1`, the dimension of `CO(d_model)`."
(Theorem B.1: "Let `d_model ≥ 2`, let the input and output dimensions be at least `d_model` […] an
attention block of `H` heads of width `d_h ≤ d_model`, causal or not, on sequences of at least two
tokens.")

Its proof uses of the parameters: `E` and `D` of rank `d`, and "For generic parameters `w E` and
`g(w)` are linearly independent for all `w` in an open set, since otherwise the block would map
every point of the sphere to a multiple of itself."

Here: this condition at almost every parameter, in the form of
`OneBlock/ResidualRMSZeroSteps.lean` (one input `w` at which, for every token, the rows of `w E`
and of `g(w)` are linearly independent), for MLP blocks whose activation is continuous and
nonzero on the positive reals, for gated blocks with such a gate, and for attention blocks; and
Theorem B.1 (v) at almost every parameter for these kinds, with tanh, GELU, SwiGLU and GeGLU by
name. The functional dimension is the one on the inputs at which no normalized row vanishes
(`funDimOn`, `residualZeroDomain`, `skiplessZeroDomain`), on both sides at the same parameter
`θ`: "the skip raises the functional dimension". The blocks may have any width with at least one
hidden unit (one head of positive width); for attention every token sees some token (the paper's
two masks), and the number of tokens is not restricted.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {hid H dh : Fin 1 → Type} [∀ ℓ, Fintype (hid ℓ)] [∀ ℓ, Fintype (H ℓ)]
  [∀ ℓ, Fintype (dh ℓ)]
variable {σ : ℝ → ℝ}

/-! ### The condition of the proof at generic parameters -/

omit [Fintype d] [DecidableEq d] in
/-- Helper: two vectors `x ≠ 0` and `y`, with `y` no multiple of `x`, are linearly independent. -/
private theorem linearIndependent_pair_rzk {x y : d → ℝ} (hx : x ≠ 0)
    (hy : ∀ c : ℝ, y ≠ c • x) : LinearIndependent ℝ ![x, y] :=
  (LinearIndependent.pair_iff' hx).2 fun a h => hy a h.symm

omit [DecidableEq d] in
/-- Helper: RMSNorm with `ε = 0` fixes a row on the sphere of radius `√d`. -/
private theorem rmsRow_zero_of_sphere_rzk {x : d → ℝ} (hx : x ⬝ᵥ x = Fintype.card d)
    (hd : (Fintype.card d : ℝ) ≠ 0) : rmsRow 0 x = x := by
  unfold rmsRow
  rw [hx, div_self hd, add_zero, Real.sqrt_one, inv_one, one_smul]

omit [DecidableEq d] in
/-- Helper: a nonzero row normalized by RMSNorm with `ε = 0` lies on the sphere of radius `√d`. -/
private theorem rmsRow_zero_dotProduct_self_rzk {u : d → ℝ} (hu : u ≠ 0) :
    rmsRow 0 u ⬝ᵥ rmsRow 0 u = Fintype.card d := by
  have hs : 0 < u ⬝ᵥ u := lt_of_le_of_ne (Finset.sum_nonneg fun i _ => mul_self_nonneg (u i))
    (Ne.symm (dotProduct_self_eq_zero.not.2 hu))
  obtain ⟨i, -⟩ := Function.ne_iff.1 hu
  have hd : (0 : ℝ) < Fintype.card d := Nat.cast_pos.2 (Fintype.card_pos_iff.2 ⟨i⟩)
  unfold rmsRow
  rw [add_zero, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc,
    ← mul_inv, Real.mul_self_sqrt (div_pos hs hd).le, inv_div, div_mul_cancel₀ _ hs.ne']

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dOut] in
/-- Helper (the input of the proof): if `E` has rank `d` and some `x` on the sphere of radius
`√d` has, at the state with every row `x`, every row of the output of the block not a multiple of
`x`, then the input `w` with every row `v`, `v E = x`, has for every token the rows of `w E` and
of `g(w)` linearly independent. -/
private theorem exists_linearIndependent_of_row_rzk (A : Arch T d 1) (θ : Params A dIn dOut)
    (hE : θ.E.rank = Fintype.card d) (hd : 0 < Fintype.card d) {x : d → ℝ}
    (hx : x ⬝ᵥ x = Fintype.card d)
    (hturn : ∀ t (c : ℝ), (A.f 0 ((Matrix.of fun _ : T => x) * θ.read 0) * θ.write 0) t ≠ c • x) :
    ∃ w : Matrix T dIn ℝ, ∀ t, LinearIndependent ℝ
      ![(w * θ.E) t, (A.f 0 (rmsNorm 0 (w * θ.E) * θ.read 0) * θ.write 0) t] := by
  have hd0 : (Fintype.card d : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hd.ne'
  -- `x ≠ 0`, since `x ⬝ᵥ x = d > 0`
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [zero_dotProduct] at hx
    exact hd0 hx.symm
  -- `v E = x` for some `v`, since `E` has rank `d`
  obtain ⟨v, hv⟩ := (Matrix.vecMul_surjective_iff_rank_eq_card.2 hE) x
  refine ⟨Matrix.of fun _ => v, fun t => ?_⟩
  -- every row of `w E` is `x`, and so is every row of `N_0(w E)`
  have hwE : (Matrix.of fun _ : T => v) * θ.E = Matrix.of fun _ : T => x := by
    ext s j
    rw [Matrix.mul_apply_eq_vecMul]
    exact congrFun hv j
  have hN : rmsNorm 0 (Matrix.of fun _ : T => x) = Matrix.of fun _ : T => x := by
    ext s j
    show rmsRow 0 x j = x j
    rw [rmsRow_zero_of_sphere_rzk hx hd0]
  rw [hwE, hN]
  exact linearIndependent_pair_rzk hx0 (hturn t)

omit [Fintype T] [Nonempty T] [DecidableEq d] in
/-- Helper: an MLP block acts row by row; row `t` of its output at the state with every row
`n t₀` is row `t₀` of its output at `n`. -/
private theorem row_mlp_rzk (χ : Matrix T d ℝ → Matrix T d ℝ) (n : Matrix T d ℝ) (t₀ t : T)
    (R : Matrix d (hid 0) ℝ) (W : Matrix (hid 0) d ℝ) :
    ((Arch.mlp σ χ hid).f 0 ((Matrix.of fun _ : T => n t₀) * R) * W) t
      = ((Arch.mlp σ χ hid).f 0 (n * R) * W) t₀ :=
  rfl

omit [Fintype T] [Nonempty T] [DecidableEq d] in
/-- Helper: the same for a gated block. -/
private theorem row_gated_rzk (χ : Matrix T d ℝ → Matrix T d ℝ) (n : Matrix T d ℝ) (t₀ t : T)
    (R : Matrix d (hid 0 ⊕ hid 0) ℝ) (W : Matrix (hid 0) d ℝ) :
    ((Arch.gated σ χ hid).f 0 ((Matrix.of fun _ : T => n t₀) * R) * W) t
      = ((Arch.gated σ χ hid).f 0 (n * R) * W) t₀ :=
  rfl

omit [Fintype T] [Nonempty T] [DecidableEq d] in
/-- Helper (MLP and gated blocks): under `TurnGeneric` for a block that acts row by row, some
input has, for every token, the rows of `w E` and of `g(w)` linearly independent. -/
private theorem exists_linearIndependent_of_turn_rzk (A : Arch T d 1) (θ : Params A dIn dOut)
    (hθ : TurnGeneric A θ) (hd : 0 < Fintype.card d)
    (hrow : ∀ (n : Matrix T d ℝ) (t₀ t : T),
      (A.f 0 ((Matrix.of fun _ : T => n t₀) * θ.read 0) * θ.write 0) t
        = (A.f 0 (n * θ.read 0) * θ.write 0) t₀) :
    ∃ w : Matrix T dIn ℝ, ∀ t, LinearIndependent ℝ
      ![(w * θ.E) t, (A.f 0 (rmsNorm 0 (w * θ.E) * θ.read 0) * θ.write 0) t] := by
  -- the state `n` on the sphere and the token `t₀` that the block turns
  obtain ⟨n, hn, t₀, ht₀⟩ := hθ.turn
  rw [Fin.sum_univ_one] at ht₀
  -- the state with every row `n t₀`: the block turns every token
  refine exists_linearIndependent_of_row_rzk A θ hθ.rank_E hd (hn t₀) fun t c => ?_
  rw [hrow]
  exact ht₀ c

/-- **Proof of Theorem B.1 (v), "For generic parameters `w E` and `g(w)` are linearly independent",
for an MLP block** whose activation is continuous and nonzero on the positive reals, with at least
one hidden unit: for almost every `θ` some input `w` has, for every token, the rows of `w E` and
of `g(w)` linearly independent. -/
theorem ae_exists_linearIndependent_rows_mlp (hσc : Continuous σ) (hσp : ∀ z, 0 < z → σ z ≠ 0)
    [Nonempty (hid 0)] (μ : Measure (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn
        dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, ∃ w : Matrix T dIn ℝ, ∀ t, LinearIndependent ℝ
      ![(w * θ.E) t,
        ((Arch.mlp σ (rmsNorm 0) hid).f 0 (rmsNorm 0 (w * θ.E) * θ.read 0) * θ.write 0) t] := by
  have : Nonempty d := Fintype.card_pos_iff.1 (by omega)
  -- the fixed map `M ↦ σ(M)` is continuous
  have hf : ∀ ℓ, Continuous ((Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid).f ℓ) :=
    fun ℓ => continuous_id.matrix_map hσc
  -- `TurnGeneric` holds for almost every `θ`
  filter_upwards [ae_turnGeneric _ hf μ hd hdIn hdOut
    (ae_someBlockNonzero_mlp hσp ⟨0, inferInstance⟩ μ)] with θ hθ
  exact exists_linearIndependent_of_turn_rzk _ θ hθ (by omega)
    fun n t₀ t => row_mlp_rzk _ n t₀ t _ _

/-- **The same for a gated block** whose gate is continuous and nonzero on the positive reals,
with at least one hidden unit. -/
theorem ae_exists_linearIndependent_rows_gated (hσc : Continuous σ) (hσp : ∀ z, 0 < z → σ z ≠ 0)
    [Nonempty (hid 0)] (μ : Measure (Params (Arch.gated (T := T) (d := d) σ (rmsNorm 0) hid) dIn
        dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, ∃ w : Matrix T dIn ℝ, ∀ t, LinearIndependent ℝ
      ![(w * θ.E) t,
        ((Arch.gated σ (rmsNorm 0) hid).f 0 (rmsNorm 0 (w * θ.E) * θ.read 0) * θ.write 0) t] := by
  have : Nonempty d := Fintype.card_pos_iff.1 (by omega)
  -- the fixed map `(z, v) ↦ σ(z) v` is continuous
  have hf : ∀ ℓ, Continuous ((Arch.gated (T := T) (d := d) σ (rmsNorm 0) hid).f ℓ) :=
    fun ℓ => continuous_matrix fun t i =>
      (hσc.comp (continuous_id.matrix_elem t (Sum.inl i))).mul
        (continuous_id.matrix_elem t (Sum.inr i))
  -- `TurnGeneric` holds for almost every `θ`
  filter_upwards [ae_turnGeneric _ hf μ hd hdIn hdOut
    (ae_someBlockNonzero_gated hσp ⟨0, inferInstance⟩ μ)] with θ hθ
  exact exists_linearIndependent_of_turn_rzk _ θ hθ (by omega)
    fun n t₀ t => row_gated_rzk _ n t₀ t _ _

omit [Nonempty T] [DecidableEq d] in
/-- Helper: on the state with every row `x`, an attention block gives every token that sees some
token the row `x ∑_i W_{V,i} W_{O,i}` (the weights of its row sum to `1` and all values are
equal). -/
private theorem row_attention_rzk (sees : T → T → Prop) [DecidableRel sees]
    (χ : Matrix T d ℝ → Matrix T d ℝ) (x : d → ℝ) (R : Matrix d (H 0 × (dh 0 ⊕ (dh 0 ⊕ dh 0))) ℝ)
    (W : Matrix (H 0 × dh 0) d ℝ) (t : T) (ht : ∃ s, sees t s) :
    ((Arch.attention sees χ H dh).f 0 ((Matrix.of fun _ : T => x) * R) * W) t
      = x ᵥ* ∑ i, R.submatrix id (fun k => (i, Sum.inr (Sum.inr k)))
          * W.submatrix (fun k => (i, k)) id := by
  rw [f_attention_mul, attentionBlock, attnHeads_const_row sees _ _ x t ht]

omit [Nonempty T] [DecidableEq d] in
/-- Helper: for `a, b` in `d`, the entry `(a, b)` of `S = ∑_i W_{V,i} W_{O,i}` is not `0` for
almost every `θ`: it is a polynomial in the weights, equal to `|H| d_h` at the weights with all
entries `1`. -/
private theorem ae_valueOutput_ne_zero_rzk (sees : T → T → Prop) [DecidableRel sees]
    [Nonempty (H 0)] [Nonempty (dh 0)]
    (μ : Measure (Params (Arch.attention (T := T) (d := d) sees (rmsNorm 0) H dh) dIn dOut))
    [μ.IsAddHaarMeasure] (a b : d) :
    ∀ᵐ θ ∂μ, (∑ i, (θ.read 0).submatrix id (fun k => (i, Sum.inr (Sum.inr k)))
      * (θ.write 0).submatrix (fun k => (i, k)) id) a b ≠ 0 := by
  -- the value matrix and the output matrix of head `i`, linear maps of the parameters
  let lV : H 0 → Params (Arch.attention (T := T) (d := d) sees (rmsNorm 0) H dh) dIn dOut
      →ₗ[ℝ] Matrix d (dh 0) ℝ := fun i =>
    { toFun := fun θ => (θ.read 0).submatrix id (fun k => (i, Sum.inr (Sum.inr k)))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let lO : H 0 → Params (Arch.attention (T := T) (d := d) sees (rmsNorm 0) H dh) dIn dOut
      →ₗ[ℝ] Matrix (dh 0) d ℝ := fun i =>
    { toFun := fun θ => (θ.write 0).submatrix (fun k => (i, k)) id
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hg : AnalyticOnNhd ℝ (fun θ : Params (Arch.attention (T := T) (d := d) sees (rmsNorm 0) H
      dh) dIn dOut => ∑ i, (lV i θ * lO i θ) a b) Set.univ :=
    Finset.analyticOnNhd_fun_sum _ fun i _ => analyticOnNhd_mul_apply (lV i) (lO i) a b
  -- at the weights with all entries `1` it is `|H| d_h ≠ 0`
  have hne : ∃ θ : Params (Arch.attention (T := T) (d := d) sees (rmsNorm 0) H dh) dIn dOut,
      ∑ i, (lV i θ * lO i θ) a b ≠ 0 := by
    refine ⟨⟨0, fun _ => Matrix.of fun _ _ => 1, fun _ => Matrix.of fun _ _ => 1, 0⟩, ?_⟩
    show ∑ _i : H 0, ∑ _k : dh 0, (1 : ℝ) * 1 ≠ 0
    simp
  -- an analytic function that is not identically zero is nonzero almost everywhere
  filter_upwards [ae_ne_zero_of_analytic μ hg hne] with θ hθ
  rw [Matrix.sum_apply]
  exact hθ

/-- **The same for an attention block** with a head of positive width, for a mask in which every
token sees some token: on an input with equal rows `v` every token gets `N_0(v E) ∑_i W_V W_O`. -/
theorem ae_exists_linearIndependent_rows_attention (sees : T → T → Prop) [DecidableRel sees]
    (hsees : ∀ t, ∃ s, sees t s) [Nonempty (H 0)] [Nonempty (dh 0)]
    (μ : Measure (Params (Arch.attention (T := T) (d := d) sees (rmsNorm 0) H dh) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, ∃ w : Matrix T dIn ℝ, ∀ t, LinearIndependent ℝ
      ![(w * θ.E) t,
        ((Arch.attention sees (rmsNorm 0) H dh).f 0 (rmsNorm 0 (w * θ.E) * θ.read 0) * θ.write 0)
            t] := by
  have : Nonempty d := Fintype.card_pos_iff.1 (by omega)
  obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card (by omega : 1 < Fintype.card d)
  obtain ⟨t₁⟩ := (inferInstance : Nonempty T)
  obtain ⟨s₁, hs₁⟩ := hsees t₁
  -- the fixed map of the block is continuous (it is analytic)
  have hf : ∀ ℓ, Continuous ((Arch.attention (T := T) (d := d) sees (rmsNorm 0) H dh).f ℓ) :=
    fun ℓ => continuousOn_univ.mp (analyticOnNhd_f_attention sees _ H dh ℓ).continuousOn
  -- for almost every `θ`: `E` has rank `d` and the entry `(a, b)` of `S` is not `0`
  filter_upwards [ae_turnGeneric _ hf μ hd hdIn hdOut
    (ae_someBlockNonzero_attention ⟨0, inferInstance, inferInstance⟩ t₁ s₁ hs₁ μ),
    ae_valueOutput_ne_zero_rzk sees μ a b] with θ hθ hS
  -- the row `x = √d e_a` on the sphere: `x S = √d S_a` is no multiple of `x`, as `S_{ab} ≠ 0`
  have hsq : Real.sqrt (Fintype.card d) ≠ 0 :=
    Real.sqrt_ne_zero'.2 (Nat.cast_pos.2 (by omega))
  have hx : (Real.sqrt (Fintype.card d) • Pi.single a 1 : d → ℝ)
      ⬝ᵥ (Real.sqrt (Fintype.card d) • Pi.single a 1) = Fintype.card d := by
    rw [smul_dotProduct, dotProduct_smul, single_dotProduct, Pi.single_eq_same, smul_eq_mul,
      smul_eq_mul, one_mul, ← mul_assoc, Real.mul_self_sqrt (Nat.cast_nonneg _), mul_one]
  refine exists_linearIndependent_of_row_rzk _ θ hθ.rank_E (by omega) hx fun t c h => hS ?_
  rw [row_attention_rzk sees _ _ _ _ t (hsees t)] at h
  -- coordinate `b` of both sides: `√d S_{ab} = c √d 0`
  have hb := congrFun h b
  rw [Matrix.smul_vecMul, Matrix.single_vecMul] at hb
  simp only [Pi.smul_apply, smul_eq_mul, Matrix.row_apply, one_mul, Pi.single_eq_of_ne' hab,
    mul_zero] at hb
  exact (mul_eq_zero.1 hb).resolve_left hsq

/-! ### Theorem B.1 (v) at generic parameters -/

/-- Helper: `funDimOn_skipless_add_le_funDimOn_residual_rmsNorm_zero` without its hypothesis
`hB`, which follows from `hw`: at the input `w` of `hw` the state `N_0(w E)` has all rows on the
sphere (no row of `w E` is `0`), and the output of the block there has a nonzero row. -/
private theorem gain_rzk {A : Arch T d 1}
    (hA : A.χ = rmsNorm 0) (hd : 2 ≤ Fintype.card d)
    (hf : AnalyticOnNhd ℝ (A.f 0) Set.univ) (θ : Params A dIn dOut)
    (hE : θ.E.rank = Fintype.card d) (hD : θ.D.rank = Fintype.card d)
    (hw : ∃ w : Matrix T dIn ℝ, ∀ t, LinearIndependent ℝ
      ![(w * θ.E) t, (A.f 0 (rmsNorm 0 (w * θ.E) * θ.read 0) * θ.write 0) t]) :
    funDimOn A 0 θ (skiplessZeroDomain A θ) + (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
      ≤ funDimOn A 1 θ (residualZeroDomain A θ) := by
  have hB : ∃ n : Matrix T d ℝ, (∀ t, n t ⬝ᵥ n t = Fintype.card d) ∧
      A.f 0 (n * θ.read 0) * θ.write 0 ≠ 0 := by
    obtain ⟨w, hw⟩ := hw
    refine ⟨rmsNorm 0 (w * θ.E), fun t => rmsRow_zero_dotProduct_self_rzk ((hw t).ne_zero 0),
      fun h => ?_⟩
    -- the row of the block at a token is the second vector of an independent pair
    obtain ⟨t₀⟩ := (inferInstance : Nonempty T)
    apply (hw t₀).ne_zero 1
    show (A.f 0 (rmsNorm 0 (w * θ.E) * θ.read 0) * θ.write 0) t₀ = 0
    rw [h]
    rfl
  exact funDimOn_skipless_add_le_funDimOn_residual_rmsNorm_zero (hA := hA) (hd := hd) (hf := hf)
    (θ := θ) (hE := hE) (hD := hD) (hw := hw) (hB := hB)

/-- **Theorem B.1 (v) of the skips paper for an MLP block** whose activation is analytic and
nonzero on the positive reals, with at least one hidden unit: with `d_in, d_out ≥ d ≥ 2`, under
pre-RMSNorm with `ε = 0`, at generic parameters the skip raises the functional dimension by at
least `d(d−1)/2 + 1`, the dimension of `CO(d)`. -/
theorem ae_funDimOn_skipless_add_le_mlp_oneBlock_residual_rmsNorm_zero
    (hσa : AnalyticOnNhd ℝ σ Set.univ) (hσp : ∀ z, 0 < z → σ z ≠ 0) [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, funDimOn (Arch.mlp σ (rmsNorm 0) hid) 0 θ (skiplessZeroDomain (Arch.mlp σ (rmsNorm 0)
        hid) θ)
        + (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
      ≤ funDimOn (Arch.mlp σ (rmsNorm 0) hid) 1 θ (residualZeroDomain (Arch.mlp σ (rmsNorm 0) hid)
          θ) := by
  have : Nonempty d := Fintype.card_pos_iff.1 (by omega)
  have hf : ∀ ℓ, AnalyticOnNhd ℝ ((Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid).f ℓ) Set.univ :=
    fun ℓ => analyticOnNhd_f_mlp hσa ℓ
  -- for almost every `θ`: `E` and `D` have rank `d`, and the input `w` of the proof exists
  filter_upwards [ae_turnGeneric _ (fun ℓ => continuousOn_univ.mp (hf ℓ).continuousOn) μ hd hdIn
    hdOut (ae_someBlockNonzero_mlp hσp ⟨0, inferInstance⟩ μ),
    ae_exists_linearIndependent_rows_mlp (continuousOn_univ.mp hσa.continuousOn) hσp μ hd hdIn
      hdOut] with θ hθ hw
  exact gain_rzk rfl hd (hf 0) θ hθ.rank_E hθ.rank_D hw

/-- **Theorem B.1 (v) of the skips paper for a tanh block.** -/
theorem ae_funDimOn_skipless_add_le_tanh_oneBlock_residual_rmsNorm_zero [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) Real.tanh (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, funDimOn (Arch.mlp Real.tanh (rmsNorm 0) hid) 0 θ (skiplessZeroDomain (Arch.mlp
        Real.tanh (rmsNorm 0) hid) θ)
        + (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
      ≤ funDimOn (Arch.mlp Real.tanh (rmsNorm 0) hid) 1 θ (residualZeroDomain (Arch.mlp Real.tanh
          (rmsNorm 0) hid) θ) := by
  exact ae_funDimOn_skipless_add_le_mlp_oneBlock_residual_rmsNorm_zero analyticOnNhd_tanh
    (fun _ hz => tanh_ne_zero_of_pos hz) μ hd hdIn hdOut

/-- **Theorem B.1 (v) of the skips paper for a GELU block.** -/
theorem ae_funDimOn_skipless_add_le_gelu_oneBlock_residual_rmsNorm_zero [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, funDimOn (Arch.mlp gelu (rmsNorm 0) hid) 0 θ (skiplessZeroDomain (Arch.mlp gelu
        (rmsNorm 0) hid) θ)
        + (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
      ≤ funDimOn (Arch.mlp gelu (rmsNorm 0) hid) 1 θ (residualZeroDomain (Arch.mlp gelu (rmsNorm 0)
          hid) θ) := by
  exact ae_funDimOn_skipless_add_le_mlp_oneBlock_residual_rmsNorm_zero analyticOnNhd_gelu
    (fun _ hz => gelu_ne_zero_of_pos hz) μ hd hdIn hdOut

/-- **Theorem B.1 (v) of the skips paper for a gated block** whose gate is analytic and nonzero on
the positive reals, with at least one hidden unit. -/
theorem ae_funDimOn_skipless_add_le_gated_oneBlock_residual_rmsNorm_zero
    (hσa : AnalyticOnNhd ℝ σ Set.univ) (hσp : ∀ z, 0 < z → σ z ≠ 0) [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.gated (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, funDimOn (Arch.gated σ (rmsNorm 0) hid) 0 θ (skiplessZeroDomain (Arch.gated σ (rmsNorm
        0) hid) θ)
        + (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
      ≤ funDimOn (Arch.gated σ (rmsNorm 0) hid) 1 θ (residualZeroDomain (Arch.gated σ (rmsNorm 0)
          hid) θ) := by
  have : Nonempty d := Fintype.card_pos_iff.1 (by omega)
  have hf : ∀ ℓ, AnalyticOnNhd ℝ ((Arch.gated (T := T) (d := d) σ (rmsNorm 0) hid).f ℓ)
      Set.univ :=
    fun ℓ => analyticOnNhd_f_gated hσa ℓ
  -- for almost every `θ`: `E` and `D` have rank `d`, and the input `w` of the proof exists
  filter_upwards [ae_turnGeneric _ (fun ℓ => continuousOn_univ.mp (hf ℓ).continuousOn) μ hd hdIn
    hdOut (ae_someBlockNonzero_gated hσp ⟨0, inferInstance⟩ μ),
    ae_exists_linearIndependent_rows_gated (continuousOn_univ.mp hσa.continuousOn) hσp μ hd hdIn
      hdOut] with θ hθ hw
  exact gain_rzk rfl hd (hf 0) θ hθ.rank_E hθ.rank_D hw

/-- **Theorem B.1 (v) of the skips paper for a SwiGLU block.** -/
theorem ae_funDimOn_skipless_add_le_swiglu_oneBlock_residual_rmsNorm_zero [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.gated (T := T) (d := d) silu (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, funDimOn (Arch.gated silu (rmsNorm 0) hid) 0 θ (skiplessZeroDomain (Arch.gated silu
        (rmsNorm 0) hid) θ)
        + (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
      ≤ funDimOn (Arch.gated silu (rmsNorm 0) hid) 1 θ (residualZeroDomain (Arch.gated silu
          (rmsNorm 0) hid) θ) := by
  exact ae_funDimOn_skipless_add_le_gated_oneBlock_residual_rmsNorm_zero analyticOnNhd_silu
    (fun _ hz => silu_ne_zero_of_pos hz) μ hd hdIn hdOut

/-- **Theorem B.1 (v) of the skips paper for a GeGLU block.** -/
theorem ae_funDimOn_skipless_add_le_geglu_oneBlock_residual_rmsNorm_zero [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.gated (T := T) (d := d) gelu (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, funDimOn (Arch.gated gelu (rmsNorm 0) hid) 0 θ (skiplessZeroDomain (Arch.gated gelu
        (rmsNorm 0) hid) θ)
        + (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
      ≤ funDimOn (Arch.gated gelu (rmsNorm 0) hid) 1 θ (residualZeroDomain (Arch.gated gelu
          (rmsNorm 0) hid) θ) := by
  exact ae_funDimOn_skipless_add_le_gated_oneBlock_residual_rmsNorm_zero analyticOnNhd_gelu
    (fun _ hz => gelu_ne_zero_of_pos hz) μ hd hdIn hdOut

/-- **Theorem B.1 (v) of the skips paper for an attention block** with a head of positive width,
for a mask in which every token sees some token (without a mask, or causal). -/
theorem ae_funDimOn_skipless_add_le_attention_oneBlock_residual_rmsNorm_zero
    (sees : T → T → Prop) [DecidableRel sees] (hsees : ∀ t, ∃ s, sees t s) [Nonempty (H 0)]
    [Nonempty (dh 0)] (μ : Measure (Params (Arch.attention (T := T) (d := d) sees (rmsNorm 0) H dh)
        dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, funDimOn (Arch.attention sees (rmsNorm 0) H dh) 0 θ (skiplessZeroDomain
        (Arch.attention sees (rmsNorm 0) H dh) θ)
        + (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
      ≤ funDimOn (Arch.attention sees (rmsNorm 0) H dh) 1 θ (residualZeroDomain (Arch.attention
          sees (rmsNorm 0) H dh) θ) := by
  have : Nonempty d := Fintype.card_pos_iff.1 (by omega)
  obtain ⟨t₁⟩ := (inferInstance : Nonempty T)
  obtain ⟨s₁, hs₁⟩ := hsees t₁
  have hf : ∀ ℓ, AnalyticOnNhd ℝ ((Arch.attention (T := T) (d := d) sees (rmsNorm 0) H dh).f ℓ)
      Set.univ :=
    fun ℓ => analyticOnNhd_f_attention sees _ H dh ℓ
  -- for almost every `θ`: `E` and `D` have rank `d`, and the input `w` of the proof exists
  filter_upwards [ae_turnGeneric _ (fun ℓ => continuousOn_univ.mp (hf ℓ).continuousOn) μ hd hdIn
    hdOut (ae_someBlockNonzero_attention ⟨0, inferInstance, inferInstance⟩ t₁ s₁ hs₁ μ),
    ae_exists_linearIndependent_rows_attention sees hsees μ hd hdIn hdOut] with θ hθ hw
  exact gain_rzk rfl hd (hf 0) θ hθ.rank_E hθ.rank_D hw

end Skips
