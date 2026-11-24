import SkipsLean.Residual.DepthAttentionRMSDim
import SkipsLean.Residual.DepthGatedRMS
import SkipsLean.Dimension.UpperBoundTransformer
import SkipsLean.Generic.Sum

/-!
# Residual networks of attention blocks and gated blocks at any depth, under pre-RMSNorm

Paper (skips paper): Lemma A.27 (Small writes), second value: "let each block, in any order and
of any width, be an attention block […] or an MLP block, with all MLP blocks tanh, all GELU, all
SwiGLU or all GeGLU blocks. […] For all small `τ ≠ 0`, the residual network has
`fd(θ_τ) = P − d_model (d_model − 1)/2 − s` (pre-RMSNorm with `ε > 0`, no biases)". Theorem 4.7:
"Let the blocks be analytic, with or without pre-RMSNorm. The residual network satisfies the
equality condition: at generic parameters its functional dimension is `P − dim G − s`. So the
skips raise the functional dimension by at least `L dim G`".

The proof of Lemma A.27 under pre-RMSNorm: "This is the equation of the proof of Theorem B.1(ii)
with `h_1 = xE` and `D_θ h_1 η = x η_E + D_θ g(n) η`, and its Steps 1 to 5 go through with three
changes. […] In Step 4, the hidden units are handled first, on inputs with equal tokens, as
above. So the flat directions are the `η^Y`, the rescalings of the units and the changes of basis
inside the heads, a space of dimension `d_model (d_model − 1)/2 + s`."

Here for `Arch.attentionGated sees σ (rmsNorm ε) H dh hid` (`Network/Transformer.lean`): `L`
blocks, block `ℓ` with the heads `H ℓ` of width `dh ℓ` and the hidden units `hid ℓ` (an attention
block if `hid ℓ` is empty, a gated block if `H ℓ` is empty), under pre-RMSNorm with `ε > 0`, with
a token `t₂` that sees itself and another token `t₁`; stated for every gate that satisfies the
conclusion of Lemma B.3 (`GatedUnitsRescale`) for the hidden units of all blocks together. The
conditions on `θ` are those of the two kinds of block, on the two parts of the parameters:
`SmallWritesGenericAttentionRMS θ.sumFst` (`Residual/DepthAttentionRMS.lean`) and
`SmallWritesGenericGatedRMS θ.sumSnd` (`Residual/DepthGatedRMS.lean`). For a block without heads
`dh ℓ` is any nonempty type. The twin without normalization:
`Residual/DepthTransformerGated.lean`.

* `smallWritesLimitNorm_eq_zero_attentionGated_rmsNorm`: the flat directions of `J_0`;
* `eventually_funDim_smallWrites_attentionGated_rmsNorm`: `fd(θ_τ) = P − d(d−1)/2 − s` for all small
  `τ ≠ 0`, `s = 2 ∑_ℓ H_ℓ d_{h,ℓ}² + ∑_ℓ d_hidden,ℓ`;
* `ae_smallWritesGeneric_attentionGated_rmsNorm`: the conditions at generic parameters;
* `ae_funDim_attentionGated_residual_rmsNorm`: Theorem 4.7, and `…_ge_add`: the gain of at least
  `L d(d−1)/2` for blocks of total width `H d_h + d_hidden ≥ d`;
* the named kinds: attention with SwiGLU blocks, attention with GeGLU blocks.
-/

namespace Skips

open Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {sees : T → T → Prop} [DecidableRel sees]
variable {H dh hid : Fin L → Type} [∀ ℓ, Fintype (H ℓ)] [∀ ℓ, Fintype (dh ℓ)]
  [∀ ℓ, Fintype (hid ℓ)] {σ σ' : ℝ → ℝ} {ε : ℝ}

/-! ### Helpers: curves of matrices -/

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (as `hasDerivAt_line_rma` of `Residual/DepthAttentionRMS.lean`): a line `τ ↦ M + τ N`
of matrices has the derivative `N`. -/
private theorem hasDerivAt_line_dtgr {m n : Type*} [Fintype m] [Fintype n] (M N : Matrix m n ℝ) :
    HasDerivAt (fun τ : ℝ => M + τ • N) N 0 := by
  have h := ((hasDerivAt_id (0 : ℝ)).smul_const N).const_add M
  rw [one_smul] at h
  exact h

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (as `hasDerivAt_mul_rma`): the product rule for two matrix curves, entry by entry. -/
private theorem hasDerivAt_mul_dtgr {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
    {A : ℝ → Matrix m n ℝ} {B : ℝ → Matrix n p ℝ} {A' : Matrix m n ℝ} {B' : Matrix n p ℝ}
    (hA : HasDerivAt A A' 0) (hB : HasDerivAt B B' 0) :
    HasDerivAt (fun τ => A τ * B τ) (A' * B 0 + A 0 * B') 0 := by
  refine hasDerivAt_pi.2 fun a => hasDerivAt_pi.2 fun c => ?_
  have h := HasDerivAt.fun_sum (u := Finset.univ) fun b _ =>
    (hasDerivAt_pi.1 (hasDerivAt_pi.1 hA a) b).fun_mul (hasDerivAt_pi.1 (hasDerivAt_pi.1 hB b) c)
  simp only [Matrix.add_apply, Matrix.mul_apply, ← Finset.sum_add_distrib]
  exact h

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (as `hasDerivAt_affine_dgr` of `Residual/DepthGatedRMS.lean`): `τ ↦ a + τ b` has the
derivative `b` at `0`. -/
private theorem hasDerivAt_affine_dtgr (a b : ℝ) : HasDerivAt (fun τ : ℝ => a + τ * b) b 0 := by
  have h := ((hasDerivAt_id' (x := (0 : ℝ))).mul_const b).const_add a
  rw [one_mul] at h
  exact h

/-! ### Helpers: the derivative of the wide block, for any blocks and for a sum of two kinds -/

/-- Helper: the derivative of the wide block `n ↦ ∑_ℓ f_ℓ(n W_read^ℓ) W_write^ℓ` along the reads
and the writes of `η`, at the input `n`:
`D_θ g(n) η = ∑_ℓ (D f_ℓ(n W_read^ℓ)(n η_read^ℓ) W_write^ℓ + f_ℓ(n W_read^ℓ) η_write^ℓ)`. -/
private noncomputable def blockSum_dtgr (A : Arch T d L) (θ η : Params A dIn dOut)
    (n : Matrix T d ℝ) : Matrix T d ℝ :=
  ∑ ℓ, (fderiv ℝ (A.f ℓ) (n * θ.read ℓ) (n * η.read ℓ) * θ.write ℓ
    + A.f ℓ (n * θ.read ℓ) * η.write ℓ)

omit [Fintype T] [DecidableEq d] [Fintype dOut] in
/-- Helper: the limit `J_0` written with `blockSum_dtgr` (by definition). -/
private theorem smallWritesLimitNorm_eq_dtgr {A : Arch T d L} (θ η : Params A dIn dOut)
    (x : Matrix T dIn ℝ) :
    smallWritesLimitNorm A θ η x
      = fderiv ℝ A.χ (x * θ.E) (x * η.E + blockSum_dtgr A θ η (A.χ (x * θ.E))) * θ.D
        + A.χ (x * θ.E) * η.D := rfl

omit [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (as `hasDerivAt_block_rma`, for any blocks): the term of block `ℓ` along a line of
reads and writes, `τ ↦ f_ℓ(n (R + τ R')) (W + τ W')`, has at `τ = 0` the derivative
`D f_ℓ(n R)(n R') W + f_ℓ(n R) W'` (chain rule). -/
private theorem hasDerivAt_block_dtgr {A : Arch T d L} (ℓ : Fin L)
    (hd : Differentiable ℝ (A.f ℓ)) (n : Matrix T d ℝ) (R R' : Matrix d (A.r ℓ) ℝ)
    (W W' : Matrix (A.w ℓ) d ℝ) :
    HasDerivAt (fun τ : ℝ => A.f ℓ (n * (R + τ • R')) * (W + τ • W'))
      (fderiv ℝ (A.f ℓ) (n * R) (n * R') * W + A.f ℓ (n * R) * W') 0 := by
  -- the line `τ ↦ n (R + τ R')` has the derivative `n R'`
  have hl : HasDerivAt (fun τ : ℝ => n * (R + τ • R')) (n * R') 0 :=
    (hasDerivAt_mul_dtgr (hasDerivAt_const (0 : ℝ) n) (hasDerivAt_line_dtgr R R')).congr_deriv
      (by simp only [Matrix.zero_mul, zero_add])
  -- the chain rule through `f_ℓ`
  have hc := (hd (n * R)).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hl
    (by rw [zero_smul, add_zero])
  have hc' : HasDerivAt (fun τ : ℝ => A.f ℓ (n * (R + τ • R')))
      (fderiv ℝ (A.f ℓ) (n * R) (n * R')) 0 := hc
  -- the product rule with the write
  have h := hasDerivAt_mul_dtgr hc' (hasDerivAt_line_dtgr W W')
  exact h.congr_deriv (by simp only [zero_smul, add_zero])

omit [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: for a network with two kinds of block, the derivative of the wide block is that of the
first part plus that of the second part (`f_sum_mul`, and the uniqueness of derivatives). -/
private theorem blockSum_sum_dtgr {A B : Arch T d L} (hA : ∀ ℓ, Differentiable ℝ (A.f ℓ))
    (hB : ∀ ℓ, Differentiable ℝ (B.f ℓ)) (θ η : Params (A.sum B) dIn dOut) (n : Matrix T d ℝ) :
    blockSum_dtgr (A.sum B) θ η n
      = blockSum_dtgr A θ.sumFst η.sumFst n + blockSum_dtgr B θ.sumSnd η.sumSnd n := by
  unfold blockSum_dtgr
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  -- along the line of reads and writes, block `ℓ` of the sum is the sum of its two parts
  have hcurve : ∀ τ : ℝ, (A.sum B).f ℓ (n * (θ.read ℓ + τ • η.read ℓ)) * (θ.write ℓ + τ • η.write ℓ)
      = A.f ℓ (n * (θ.sumFst.read ℓ + τ • η.sumFst.read ℓ))
          * (θ.sumFst.write ℓ + τ • η.sumFst.write ℓ)
        + B.f ℓ (n * (θ.sumSnd.read ℓ + τ • η.sumSnd.read ℓ))
          * (θ.sumSnd.write ℓ + τ • η.sumSnd.write ℓ) := by
    intro τ
    rw [f_sum_mul]
    rfl
  have h1 := hasDerivAt_block_dtgr ℓ (differentiable_f_sum (hA ℓ) (hB ℓ)) n (θ.read ℓ) (η.read ℓ)
    (θ.write ℓ) (η.write ℓ)
  have h2 := (hasDerivAt_block_dtgr ℓ (hA ℓ) n (θ.sumFst.read ℓ) (η.sumFst.read ℓ)
    (θ.sumFst.write ℓ) (η.sumFst.write ℓ)).add (hasDerivAt_block_dtgr ℓ (hB ℓ) n
      (θ.sumSnd.read ℓ) (η.sumSnd.read ℓ) (θ.sumSnd.write ℓ) (η.sumSnd.write ℓ))
  exact h1.unique (h2.congr_of_eventuallyEq (Filter.Eventually.of_forall hcurve))

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (as `analyticOnNhd_clm_apply_rma`): an analytic family of continuous linear maps,
applied to an analytic family of vectors, is analytic. -/
private theorem analyticOnNhd_clm_apply_dtgr {X E F : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {J : X → E →L[ℝ] F} {v : X → E} {s : Set X} (hJ : AnalyticOnNhd ℝ J s)
    (hv : AnalyticOnNhd ℝ v s) : AnalyticOnNhd ℝ (fun x => J x (v x)) s :=
  fun x hx => ((ContinuousLinearMap.id ℝ (E →L[ℝ] F)).analyticAt_bilinear (J x, v x)).comp₂
    (hJ x hx) (hv x hx)

omit [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (as `analyticOnNhd_blockDir_rma`, for any analytic blocks): `n ↦ D_θ g(n) η` is
real-analytic. -/
private theorem analyticOnNhd_blockSum_dtgr {A : Arch T d L}
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (θ η : Params A dIn dOut) :
    AnalyticOnNhd ℝ (blockSum_dtgr A θ η) Set.univ := by
  unfold blockSum_dtgr
  refine Finset.analyticOnNhd_fun_sum _ fun ℓ _ => ?_
  have hr : AnalyticOnNhd ℝ (fun n : Matrix T d ℝ => n * θ.read ℓ) Set.univ :=
    analyticOnNhd_matrix_mul analyticOnNhd_id analyticOnNhd_const
  have he : AnalyticOnNhd ℝ (fun n : Matrix T d ℝ => n * η.read ℓ) Set.univ :=
    analyticOnNhd_matrix_mul analyticOnNhd_id analyticOnNhd_const
  -- `n ↦ D f_ℓ(n W_read)(n η_read)`
  have h1 := analyticOnNhd_clm_apply_dtgr ((hf ℓ).fderiv.comp hr (Set.mapsTo_univ _ _)) he
  -- `n ↦ f_ℓ(n W_read)`
  have h2 := (hf ℓ).comp hr (Set.mapsTo_univ _ _)
  exact (analyticOnNhd_matrix_mul h1 analyticOnNhd_const).add
    (analyticOnNhd_matrix_mul h2 analyticOnNhd_const)

omit [Fintype T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (as `rmsNorm_zero_rma`): `N_ε(0) = 0`. -/
private theorem rmsNorm_zero_dtgr : rmsNorm ε (0 : Matrix T d ℝ) = 0 := by
  ext t k
  simp [rmsNorm, rmsRow]

/-! ### Helpers: the gated part -/

omit [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (the private `fderiv_f_gated_apply_dgr` of `Residual/DepthGatedRMS.lean`): the
derivative of the map of a gated block at `M` along `N`: entry `(t, i)` is
`σ'(M_{t, g i}) N_{t, g i} M_{t, v i} + σ(M_{t, g i}) N_{t, v i}`. -/
private theorem fderiv_f_gated_apply_dtgr (hσ : ∀ z, HasDerivAt σ (σ' z) z) (ℓ : Fin L)
    (M N : Matrix T (hid ℓ ⊕ hid ℓ) ℝ) (t : T) (i : hid ℓ) :
    fderiv ℝ ((Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid).f ℓ) M N t i
      = σ' (M t (Sum.inl i)) * N t (Sum.inl i) * M t (Sum.inr i)
        + σ (M t (Sum.inl i)) * N t (Sum.inr i) := by
  have hd := differentiable_f_gated (T := T) (d := d) (χ := rmsNorm ε) (hid := hid)
    (fun z => (hσ z).differentiableAt) ℓ
  -- the chain rule along the line `τ ↦ M + τ N`
  have h1 := (hd M).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) (hasDerivAt_line_dtgr M N)
    (by rw [zero_smul, add_zero])
  have h2 := hasDerivAt_pi.1 (hasDerivAt_pi.1 h1 t) i
  -- the same derivative computed on the entry `(t, i)`
  have h3 : HasDerivAt (fun τ : ℝ => σ (M t (Sum.inl i) + τ * N t (Sum.inl i))
      * (M t (Sum.inr i) + τ * N t (Sum.inr i)))
      (σ' (M t (Sum.inl i)) * N t (Sum.inl i) * M t (Sum.inr i)
        + σ (M t (Sum.inl i)) * N t (Sum.inr i)) 0 := by
    have hu := hasDerivAt_affine_dtgr (M t (Sum.inl i)) (N t (Sum.inl i))
    have hw := hasDerivAt_affine_dtgr (M t (Sum.inr i)) (N t (Sum.inr i))
    have h := ((hσ _).comp (0 : ℝ) hu).mul hw
    convert h using 1
    · rfl
    · simp only [Function.comp_apply, zero_mul, add_zero]
  exact h2.unique h3

omit [Fintype T] [Fintype dIn] [Fintype dOut] [DecidableEq d] in
/-- Helper (the private `gatedDirDGR`): the derivative of `n ↦ f(n W_read) W_write` along the
entries `R'` (of the read) and `W'` (of the write), entry by entry, at the read `R` and the write
`W`: `∑_i [σ(z_i) w_i W'_{i k} + σ'(z_i) (n R')_{t, g i} w_i W_{i k} + σ(z_i) (n R')_{t, v i}
W_{i k}]` with `z_i = (n R)_{t, g i}` and `w_i = (n R)_{t, v i}`. -/
private noncomputable def gatedDir_dtgr (σ σ' : ℝ → ℝ) {q : Type*} [Fintype q]
    (R R' : Matrix d (q ⊕ q) ℝ) (W W' : Matrix q d ℝ) (n : Matrix T d ℝ) : Matrix T d ℝ :=
  Matrix.of fun t k => ∑ i : q,
    (σ ((n * R) t (Sum.inl i)) * (n * R) t (Sum.inr i) * W' i k
      + σ' ((n * R) t (Sum.inl i)) * (n * R') t (Sum.inl i) * (n * R) t (Sum.inr i) * W i k
      + σ ((n * R) t (Sum.inl i)) * (n * R') t (Sum.inr i) * W i k)

omit [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (as `fderiv_add_eq_gatedDirDGR`): the derivative of the wide block of a network of
gated blocks is the sum over the blocks of `gatedDir_dtgr`. -/
private theorem blockSum_gated_dtgr (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (θ η : Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)
    (n : Matrix T d ℝ) :
    blockSum_dtgr (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) θ η n
      = ∑ ℓ, gatedDir_dtgr σ σ' (θ.read ℓ) (η.read ℓ) (θ.write ℓ) (η.write ℓ) n := by
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  ext t k
  rw [gatedDir_dtgr, Matrix.of_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [fderiv_f_gated_apply_dtgr hσ]
  have hf : (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid).f ℓ (n * θ.read ℓ) t i
      = σ ((n * θ.read ℓ) t (Sum.inl i)) * (n * θ.read ℓ) t (Sum.inr i) := rfl
  rw [hf]
  ring

/-! ### Helpers: the attention part on inputs with equal tokens -/

omit [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (the private `attnWeights_sum_rat` of `Absorb/RMSNormAttention.lean`): row `t` of the
weights sums to `1` when token `t` sees some token. -/
private theorem attnWeights_sum_dtgr (Z : Matrix T T ℝ) (t : T) (ht : ∃ s, sees t s) :
    ∑ s, attnWeights sees Z t s = 1 := by
  obtain ⟨s, hs⟩ := ht
  have hS : 0 < ∑ s', if sees t s' then Real.exp (Z t s') else 0 := by
    refine Finset.sum_pos' (fun s' _ => ?_) ⟨s, Finset.mem_univ _, ?_⟩
    · split_ifs
      · exact (Real.exp_pos _).le
      · exact le_rfl
    · simp only [hs, ite_true]
      exact Real.exp_pos _
  have h1 : ∀ s, attnWeights sees Z t s = (if sees t s then Real.exp (Z t s) else 0)
      / ∑ s', if sees t s' then Real.exp (Z t s') else 0 := by
    intro s
    simp only [attnWeights, Matrix.of_apply]
    split_ifs
    · rfl
    · rw [zero_div]
  simp only [h1, ← Finset.sum_div]
  exact div_self hS.ne'

omit [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: on an input `M` whose rows are all equal to `m`, entry `(t, (i, k))` of the output of
an attention block is the value coordinate `m_{(i, v k)}`, for a token `t` that sees itself
(the weights of row `t` sum to `1`, whatever the scores). -/
private theorem f_attention_const_dtgr {χ : Matrix T d ℝ → Matrix T d ℝ} (ℓ : Fin L)
    (M : Matrix T (H ℓ × (dh ℓ ⊕ (dh ℓ ⊕ dh ℓ))) ℝ) (m : H ℓ × (dh ℓ ⊕ (dh ℓ ⊕ dh ℓ)) → ℝ)
    (hM : ∀ s, M s = m) (t : T) (ht : sees t t) (p : H ℓ × dh ℓ) :
    (Arch.attention (T := T) (d := d) sees χ H dh).f ℓ M t p
      = m (p.1, Sum.inr (Sum.inr p.2)) := by
  show ∑ s', attnWeights sees _ t s' * M s' (p.1, Sum.inr (Sum.inr p.2)) = _
  simp only [hM, ← Finset.sum_mul, attnWeights_sum_dtgr _ t ⟨t, ht⟩, one_mul]

omit [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: at an input `M` with all rows equal to `m`, along a direction `N` with all rows equal
to `m'`, entry `(t, (i, k))` of the derivative of an attention block is `m'_{(i, v k)}`: along
the line `M + τ N` the rows stay equal, and the entry is `m_{(i, v k)} + τ m'_{(i, v k)}`. -/
private theorem fderiv_f_attention_const_dtgr {χ : Matrix T d ℝ → Matrix T d ℝ} (ℓ : Fin L)
    (M N : Matrix T (H ℓ × (dh ℓ ⊕ (dh ℓ ⊕ dh ℓ))) ℝ) (m m' : H ℓ × (dh ℓ ⊕ (dh ℓ ⊕ dh ℓ)) → ℝ)
    (hM : ∀ s, M s = m) (hN : ∀ s, N s = m') (t : T) (ht : sees t t) (p : H ℓ × dh ℓ) :
    fderiv ℝ ((Arch.attention (T := T) (d := d) sees χ H dh).f ℓ) M N t p
      = m' (p.1, Sum.inr (Sum.inr p.2)) := by
  have hd := differentiable_f_attention (T := T) (d := d) sees χ H dh ℓ
  -- the chain rule along the line `τ ↦ M + τ N`
  have h1 := (hd M).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) (hasDerivAt_line_dtgr M N)
    (by rw [zero_smul, add_zero])
  have h2 := hasDerivAt_pi.1 (hasDerivAt_pi.1 h1 t) p
  -- the same derivative computed on the entry: it is affine in `τ`
  have h3 : HasDerivAt (fun τ : ℝ => (Arch.attention (T := T) (d := d) sees χ H dh).f ℓ
      (M + τ • N) t p) (m' (p.1, Sum.inr (Sum.inr p.2))) 0 := by
    have e : (fun τ : ℝ => (Arch.attention (T := T) (d := d) sees χ H dh).f ℓ (M + τ • N) t p)
        = fun τ => m (p.1, Sum.inr (Sum.inr p.2)) + τ * m' (p.1, Sum.inr (Sum.inr p.2)) := by
      funext τ
      have hMN : ∀ s, (M + τ • N) s = m + τ • m' := fun s => by
        show M s + τ • N s = m + τ • m'
        rw [hM s, hN s]
      rw [f_attention_const_dtgr ℓ (M + τ • N) (m + τ • m') hMN t ht p]
      rfl
    rw [e]
    exact hasDerivAt_affine_dtgr _ _
  exact h2.unique h3

/-- Helper: the matrix `Ψ = ∑_ℓ (η_V^ℓ W_O^ℓ + W_V^ℓ η_O^ℓ)`, with `W_V^ℓ` the value columns of
all heads of the read of block `ℓ` and `W_O^ℓ` its write: the derivative of the matrices
`W_V W_O` of all heads along `η`, summed. -/
private noncomputable def psi_dtgr {χ : Matrix T d ℝ → Matrix T d ℝ}
    (θ η : Params (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut) : Matrix d d ℝ :=
  ∑ ℓ, ((η.read ℓ).submatrix id (fun p : H ℓ × dh ℓ => (p.1, Sum.inr (Sum.inr p.2)))
      * θ.write ℓ
    + (θ.read ℓ).submatrix id (fun p : H ℓ × dh ℓ => (p.1, Sum.inr (Sum.inr p.2)))
      * η.write ℓ)

omit [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: at an input whose rows all equal `u`, row `t` of the derivative of the wide block of
a network of attention blocks is `u Ψ`, for a token `t` that sees itself: every head gives row
`t` the value of the common row, whatever the scores. -/
private theorem blockSum_attention_row_dtgr {χ : Matrix T d ℝ → Matrix T d ℝ}
    (θ η : Params (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut) (u : d → ℝ) (t : T)
    (ht : sees t t) :
    blockSum_dtgr (Arch.attention (T := T) (d := d) sees χ H dh) θ η (Matrix.of fun _ => u) t
      = u ᵥ* psi_dtgr θ η := by
  funext k
  rw [psi_dtgr, Matrix.vecMul_sum, Finset.sum_apply, blockSum_dtgr, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  -- block `ℓ`: the rows of `n W_read` and of `n η_read` are `u W_read` and `u η_read`
  have h1 : ∀ p : H ℓ × dh ℓ, fderiv ℝ ((Arch.attention (T := T) (d := d) sees χ H dh).f ℓ)
      ((Matrix.of fun _ => u) * θ.read ℓ) ((Matrix.of fun _ => u) * η.read ℓ) t p
      = (u ᵥ* η.read ℓ) (p.1, Sum.inr (Sum.inr p.2)) := fun p =>
    fderiv_f_attention_const_dtgr ℓ _ _ (u ᵥ* θ.read ℓ) (u ᵥ* η.read ℓ) (fun _ => rfl)
      (fun _ => rfl) t ht p
  have h2 : ∀ p : H ℓ × dh ℓ, (Arch.attention (T := T) (d := d) sees χ H dh).f ℓ
      ((Matrix.of fun _ => u) * θ.read ℓ) t p = (u ᵥ* θ.read ℓ) (p.1, Sum.inr (Sum.inr p.2)) :=
    fun p => f_attention_const_dtgr ℓ _ (u ᵥ* θ.read ℓ) (fun _ => rfl) t ht p
  rw [Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply, Matrix.vecMul_add, Pi.add_apply,
    ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul,
    Finset.sum_congr rfl fun p _ => congrArg (· * θ.write ℓ p k) (h1 p),
    Finset.sum_congr rfl fun p _ => congrArg (· * η.write ℓ p k) (h2 p)]
  rfl

/-- **Proof of Lemma A.27, attention blocks and gated blocks under pre-RMSNorm, the flat
directions of `J_0`:** let `ε > 0` and let token `t₂` see itself and another token `t₁`. Under
the conditions of the lemma, a direction `η` with `(J_0 η)(x) = 0` at every input `x` has
`η_E = E Y` and `η_D = −Y D` for one antisymmetric matrix `Y`; in every block the reads and the
writes of its heads are those of the directions of the changes of basis inside the heads, and
it vanishes at the gate columns of the hidden units and rescales every hidden unit (the value
column of unit `i` of block `ℓ` by `−α_{ℓ,i}`, its write row by `α_{ℓ,i}`). -/
theorem smallWritesLimitNorm_eq_zero_attentionGated_rmsNorm (hε : 0 < ε)
    (hσ : ∀ z, HasDerivAt σ (σ' z) z) (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (hU : GatedUnitsRescale σ σ' d d (Σ ℓ, hid ℓ))
    (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁)
    (θ : Params (Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut)
    (hθa : SmallWritesGenericAttentionRMS θ.sumFst) (hθm : SmallWritesGenericGatedRMS θ.sumSnd)
    (η : Params (Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut)
    (hη : ∀ x, smallWritesLimitNorm (Arch.attentionGated sees σ (rmsNorm ε) H dh hid) θ η x = 0) :
    ∃ (Y : Matrix d d ℝ) (Γ Γ' : ∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) (α : ∀ ℓ, hid ℓ → ℝ),
      Yᵀ = -Y ∧ η.E = θ.E * Y ∧ η.D = -(Y * θ.D)
        ∧ (∀ ℓ, η.sumFst.read ℓ = (headDirQK θ.sumFst Γ + headDirVO θ.sumFst Γ').read ℓ)
        ∧ (∀ ℓ, η.sumFst.write ℓ = (headDirQK θ.sumFst Γ + headDirVO θ.sumFst Γ').write ℓ)
        ∧ (∀ ℓ (i : hid ℓ) a, η.sumSnd.read ℓ a (Sum.inl i) = 0)
        ∧ (∀ ℓ (i : hid ℓ) a,
          η.sumSnd.read ℓ a (Sum.inr i) = -(α ℓ i) * θ.sumSnd.read ℓ a (Sum.inr i))
        ∧ (∀ ℓ (i : hid ℓ) a, η.sumSnd.write ℓ i a = α ℓ i * θ.sumSnd.write ℓ i a) := by
  classical
  have : Nonempty T := ⟨t₁⟩
  -- the blocks of the two parts, and so those of the sum, are real-analytic
  have hfA : ∀ ℓ, AnalyticOnNhd ℝ ((Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh).f ℓ)
      Set.univ := fun ℓ => analyticOnNhd_f_attention sees (rmsNorm ε) H dh ℓ
  have hfB : ∀ ℓ, AnalyticOnNhd ℝ ((Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid).f ℓ)
      Set.univ := fun ℓ => analyticOnNhd_f_gated hσa ℓ
  have hf : ∀ ℓ, AnalyticOnNhd ℝ
      ((Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm ε) H dh hid).f ℓ) Set.univ :=
    fun ℓ => analyticOnNhd_f_sum (hfA ℓ) (hfB ℓ)
  -- Steps 1 to 3 (`Residual/SmallWritesRMSSteps.lean`): the derivative `D_θ g(n) η` of the wide
  -- block vanishes at every `n = N_ε(x E)`
  obtain ⟨-, -, -, -, hF⟩ := exists_antisymm_of_smallWritesLimitNorm_rmsNorm hε rfl
    (fun ℓ => (hf ℓ).contDiff) θ hθa.rank_E hθa.rank_D η hη
  -- so on the open range of `N_ε` (`E` has a left inverse `B`), which contains `N_ε(0) = 0`; it is
  -- real-analytic in `n`, so it vanishes at every `n`
  obtain ⟨B, hB⟩ : ∃ B : Matrix d dIn ℝ, B * θ.E = 1 :=
    Matrix.vecMul_surjective_iff_exists_left_inverse.mp
      (Matrix.vecMul_surjective_iff_rank_eq_card.mpr hθa.rank_E)
  have hev : blockSum_dtgr (Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm ε) H dh hid)
      θ η =ᶠ[𝓝 0] 0 :=
    Filter.eventually_of_mem ((isOpenMap_rmsNorm (T := T) (d := d) hε).isOpen_range.mem_nhds
      ⟨0, rmsNorm_zero_dtgr⟩) fun n hn => by
        obtain ⟨h, hh⟩ := hn
        have e := hF (h * B)
        rw [Matrix.mul_assoc h B θ.E, hB, Matrix.mul_one, hh] at e
        exact e
  have hall : ∀ n, blockSum_dtgr
      (Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) θ η n = 0 := fun n =>
    (analyticOnNhd_blockSum_dtgr hf θ η).eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (Set.mem_univ 0) hev (Set.mem_univ n)
  -- by `f_sum_mul`, it is the term of the attention part plus that of the gated part
  have hsplit : ∀ n, blockSum_dtgr
      (Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) θ η n
      = blockSum_dtgr (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) θ.sumFst
          η.sumFst n
        + blockSum_dtgr (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) θ.sumSnd η.sumSnd n :=
    blockSum_sum_dtgr (fun ℓ => differentiable_f_attention sees (rmsNorm ε) H dh ℓ)
      (fun ℓ => differentiable_f_gated (fun z => (hσ z).differentiableAt) ℓ) θ η
  -- Step 4, the hidden units first, on inputs with equal tokens: at an input whose rows all equal
  -- `v`, row `t₂` of the attention part is `v Ψ`; Lemma B.3 for the hidden units of all blocks
  -- together, with the linear term `ψ_M = Ψ`: no component at the gates, and every unit only
  -- rescales its value
  obtain ⟨-, -, hc, -, α, hα⟩ := hU
    (fun p => (θ.sumSnd.read p.1)ᵀ (Sum.inl p.2)) 0
    (fun p => (θ.sumSnd.read p.1)ᵀ (Sum.inr p.2)) 0 (fun p => θ.sumSnd.write p.1 p.2)
    (psi_dtgr θ.sumFst η.sumFst) 0 (fun p => (η.sumSnd.read p.1)ᵀ (Sum.inl p.2)) 0
    (fun p => (η.sumSnd.read p.1)ᵀ (Sum.inr p.2)) 0 (fun p => η.sumSnd.write p.1 p.2)
    (fun p => hθm.row_ne_zero p.1 p.2) (fun p => hθm.gate_ne_zero p.1 p.2)
    (fun p q hpq => hθm.gate_not_collinear p q hpq) (fun p => hθm.value_ne_zero p.1 p.2) (by
      intro v
      funext k
      have h := congrFun (congrFun (hall (Matrix.of fun _ => v)) t₂) k
      rw [hsplit, Matrix.add_apply, blockSum_attention_row_dtgr _ _ v t₂ hs2,
        blockSum_gated_dtgr hσ, Matrix.sum_apply] at h
      simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
        add_zero]
      rw [Fintype.sum_sigma]
      exact h)
  -- the terms of the units then vanish at every input: for unit `i`,
  -- `σ(z_i) w_i (α_i W_i) + σ'(z_i) · 0 · w_i W_i + σ(z_i) (−α_i w_i) W_i = 0`
  have hgz : ∀ n, blockSum_dtgr (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) θ.sumSnd
      η.sumSnd n = 0 := by
    intro n
    rw [blockSum_gated_dtgr hσ]
    ext t k
    rw [Matrix.sum_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun ℓ _ => Finset.sum_eq_zero fun i _ => ?_
    have hg : (n * η.sumSnd.read ℓ) t (Sum.inl i) = 0 := by
      rw [Matrix.mul_apply]
      refine Finset.sum_eq_zero fun a _ => ?_
      have h0 : η.sumSnd.read ℓ a (Sum.inl i) = 0 := congrFun (congrFun hc ⟨ℓ, i⟩) a
      rw [h0, mul_zero]
    have hv : (n * η.sumSnd.read ℓ) t (Sum.inr i)
        = -(α ⟨ℓ, i⟩) * (n * θ.sumSnd.read ℓ) t (Sum.inr i) := by
      rw [Matrix.mul_apply, Matrix.mul_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      have h1 : η.sumSnd.read ℓ a (Sum.inr i) = -(α ⟨ℓ, i⟩) * θ.sumSnd.read ℓ a (Sum.inr i) :=
        congrFun (hα ⟨ℓ, i⟩).1 a
      rw [h1]
      ring
    have hw : η.sumSnd.write ℓ i k = α ⟨ℓ, i⟩ * θ.sumSnd.write ℓ i k :=
      congrFun (hα ⟨ℓ, i⟩).2.2 k
    show σ ((n * θ.sumSnd.read ℓ) t (Sum.inl i)) * (n * θ.sumSnd.read ℓ) t (Sum.inr i)
          * η.sumSnd.write ℓ i k
        + σ' ((n * θ.sumSnd.read ℓ) t (Sum.inl i)) * (n * η.sumSnd.read ℓ) t (Sum.inl i)
          * (n * θ.sumSnd.read ℓ) t (Sum.inr i) * θ.sumSnd.write ℓ i k
        + σ ((n * θ.sumSnd.read ℓ) t (Sum.inl i)) * (n * η.sumSnd.read ℓ) t (Sum.inr i)
          * θ.sumSnd.write ℓ i k = 0
    rw [hg, hv, hw]
    ring
  -- so the attention part `η.sumFst` is flat for `J_0` of the network of attention blocks
  have hηA : ∀ x, smallWritesLimitNorm (Arch.attention sees (rmsNorm ε) H dh) θ.sumFst η.sumFst
      x = 0 := by
    intro x
    have e := hη x
    rw [smallWritesLimitNorm_eq_dtgr, hsplit, hgz, add_zero] at e
    rw [smallWritesLimitNorm_eq_dtgr]
    exact e
  -- Steps 1 to 5 for the network of attention blocks (`Residual/DepthAttentionRMS.lean`): `Y`,
  -- and the changes of basis inside the heads
  obtain ⟨Y, Γ, Γ', hY, hE, hD, hr, hw⟩ :=
    smallWritesLimitNorm_eq_zero_attention_rmsNorm hε t₁ t₂ h12 hs2 hs1 θ.sumFst hθa η.sumFst hηA
  refine ⟨Y, Γ, Γ', fun ℓ i => α ⟨ℓ, i⟩, hY, hE, hD, hr, hw, fun ℓ i a => ?_, fun ℓ i a => ?_,
    fun ℓ i a => ?_⟩
  · exact congrFun (congrFun hc ⟨ℓ, i⟩) a
  · exact congrFun (hα ⟨ℓ, i⟩).1 a
  · exact congrFun (hα ⟨ℓ, i⟩).2.2 a

/-! ### Helpers: the space of the flat directions of `J_0` -/

omit [Fintype T] [DecidableEq d] [Fintype dIn] in
/-- Helper (as `flatEDLin_rma` of `Residual/DepthAttentionRMS.lean`): the directions
`Y ↦ (E Y, 0, 0, −Y D)` of one change of basis at all hidden states, as a linear map. -/
private def flatEDLin_dtgr {A : Arch T d L} (θ : Params A dIn dOut) :
    Matrix d d ℝ →ₗ[ℝ] Params A dIn dOut where
  toFun X := ⟨θ.E * X, 0, 0, -(X * θ.D)⟩
  map_add' X Y := by
    apply Params.ext'
    · exact Matrix.mul_add _ _ _
    · intro ℓ
      exact (add_zero 0).symm
    · intro ℓ
      exact (add_zero 0).symm
    · show -((X + Y) * θ.D) = -(X * θ.D) + -(Y * θ.D)
      rw [Matrix.add_mul, neg_add]
  map_smul' c X := by
    apply Params.ext'
    · exact Matrix.mul_smul _ _ _
    · intro ℓ
      exact (smul_zero c).symm
    · intro ℓ
      exact (smul_zero c).symm
    · show -((c • X) * θ.D) = c • -(X * θ.D)
      rw [Matrix.smul_mul, smul_neg]

/-- Helper (as `headDirQKLin_rma`): `Γ ↦ headDirQK θ Γ` is linear. -/
private noncomputable def headDirQKLin_dtgr {χ : Matrix T d ℝ → Matrix T d ℝ}
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

/-- Helper (as `headDirVOLin_rma`): `Γ' ↦ headDirVO θ Γ'` is linear. -/
private noncomputable def headDirVOLin_dtgr {χ : Matrix T d ℝ → Matrix T d ℝ}
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

omit [Fintype T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (as `limitFlatLinRMS` of `Residual/DepthGatedRMS.lean`, without `E` and `D`): the
rescalings of the hidden units, `α ↦ (0, the reads with gate columns `0` and value columns
`-α_{ℓ,i}` times those of `W_read^ℓ`, the writes with rows `α_{ℓ,i}` times those of
`W_write^ℓ`, 0)`, as a linear map. -/
private noncomputable def rescaleLin_dtgr {χ : Matrix T d ℝ → Matrix T d ℝ}
    (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut) :
    (∀ ℓ, hid ℓ → ℝ) →ₗ[ℝ] Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut where
  toFun α := ⟨0,
    fun ℓ => Matrix.of fun k j =>
      Sum.elim (fun _ => 0) (fun i => -(α ℓ i) * θ.read ℓ k (Sum.inr i)) j,
    fun ℓ => Matrix.of fun i k => α ℓ i * θ.write ℓ i k, 0⟩
  map_add' p q := by
    apply Params.ext'
    · exact (add_zero 0).symm
    · intro ℓ
      ext k j
      rcases j with i | i
      · exact (add_zero 0).symm
      · show -((p + q) ℓ i) * θ.read ℓ k (Sum.inr i)
          = -(p ℓ i) * θ.read ℓ k (Sum.inr i) + -(q ℓ i) * θ.read ℓ k (Sum.inr i)
        rw [Pi.add_apply, Pi.add_apply]
        ring
    · intro ℓ
      ext i k
      show (p + q) ℓ i * θ.write ℓ i k = p ℓ i * θ.write ℓ i k + q ℓ i * θ.write ℓ i k
      rw [Pi.add_apply, Pi.add_apply]
      ring
    · exact (add_zero 0).symm
  map_smul' c p := by
    apply Params.ext'
    · exact (smul_zero c).symm
    · intro ℓ
      ext k j
      rcases j with i | i
      · exact (smul_zero c).symm
      · show -((c • p) ℓ i) * θ.read ℓ k (Sum.inr i) = c * (-(p ℓ i) * θ.read ℓ k (Sum.inr i))
        rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul]
        ring
    · intro ℓ
      ext i k
      show (c • p) ℓ i * θ.write ℓ i k = c * (p ℓ i * θ.write ℓ i k)
      rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul]
      ring
    · exact (smul_zero c).symm

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (the private `sumInlLin_ibl` of `Symmetry/InsideBlocksSum.lean`): `Params.sumInl`, the
lift of a direction of `A` to the sum, as a linear map. -/
private def sumInlLin_dtgr {A B : Arch T d L} :
    Params A dIn dOut →ₗ[ℝ] Params (A.sum B) dIn dOut where
  toFun := Params.sumInl
  map_add' η ζ := by
    apply Params.ext'
    · rfl
    · intro ℓ
      ext a p
      rcases p with p | p
      · rfl
      · exact (add_zero (0 : ℝ)).symm
    · intro ℓ
      ext p a
      rcases p with p | p
      · rfl
      · exact (add_zero (0 : ℝ)).symm
    · rfl
  map_smul' c η := by
    apply Params.ext'
    · rfl
    · intro ℓ
      ext a p
      rcases p with p | p
      · rfl
      · exact (smul_zero c).symm
    · intro ℓ
      ext p a
      rcases p with p | p
      · rfl
      · exact (smul_zero c).symm
    · rfl

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (the private `sumInrLin_ibl`): `Params.sumInr`, the lift of a direction of `B` to the
sum, as a linear map. -/
private def sumInrLin_dtgr {A B : Arch T d L} :
    Params B dIn dOut →ₗ[ℝ] Params (A.sum B) dIn dOut where
  toFun := Params.sumInr
  map_add' η ζ := by
    apply Params.ext'
    · rfl
    · intro ℓ
      ext a p
      rcases p with p | p
      · exact (add_zero (0 : ℝ)).symm
      · rfl
    · intro ℓ
      ext p a
      rcases p with p | p
      · exact (add_zero (0 : ℝ)).symm
      · rfl
    · rfl
  map_smul' c η := by
    apply Params.ext'
    · rfl
    · intro ℓ
      ext a p
      rcases p with p | p
      · exact (smul_zero c).symm
      · rfl
    · intro ℓ
      ext p a
      rcases p with p | p
      · exact (smul_zero c).symm
      · rfl
    · rfl

/-- Helper (as `finrank_headFun_rma`): the families `Γ` of `d_h × d_h` matrices, one for each
head of each block, form a space of dimension `∑_ℓ H_ℓ d_{h,ℓ}²`. -/
private theorem finrank_headFun_dtgr :
    Module.finrank ℝ (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)
      = ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2 := by
  rw [Module.finrank_pi_fintype]
  simp only [Module.finrank_pi_fintype, Module.finrank_matrix, Module.finrank_self, mul_one,
    Finset.sum_const, Finset.card_univ, smul_eq_mul, sq]

/-- Helper: the families `α` of numbers, one for each hidden unit of each block, form a space of
dimension `∑_ℓ d_hidden,ℓ`. -/
private theorem finrank_hidFun_dtgr :
    Module.finrank ℝ (∀ ℓ, hid ℓ → ℝ) = ∑ ℓ, Fintype.card (hid ℓ) := by
  rw [Module.finrank_pi_fintype]
  simp only [Module.finrank_fintype_fun_eq_card]


/-- **Lemma A.27 (Small writes), second value, for attention blocks and gated blocks, under the
conditions of its proof:** with `ε > 0` and a token that sees itself and another token, for all
small `τ ≠ 0` the residual network has
`fd(θ_τ) = P − d(d−1)/2 − 2 ∑_ℓ H_ℓ d_{h,ℓ}² − ∑_ℓ d_hidden,ℓ`. -/
theorem eventually_funDim_smallWrites_attentionGated_rmsNorm (hε : 0 < ε)
    (hσ : ∀ z, HasDerivAt σ (σ' z) z) (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (hU : GatedUnitsRescale σ σ' d d (Σ ℓ, hid ℓ))
    (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁)
    (θ : Params (Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut)
    (hθa : SmallWritesGenericAttentionRMS θ.sumFst) (hθm : SmallWritesGenericGatedRMS θ.sumSnd) :
    ∀ᶠ τ in 𝓝[≠] (0 : ℝ),
      funDim (Arch.attentionGated sees σ (rmsNorm ε) H dh hid) 1 (θ.smallWrites τ)
          + (Fintype.card d * (Fintype.card d - 1) / 2
            + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
              + ∑ ℓ, Fintype.card (hid ℓ)))
        = Module.finrank ℝ
            (Params
              (Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut) := by
  classical
  -- the flat directions of `J_0` lie in the range `V` of the linear map
  -- `(Y, (Γ, Γ'), α) ↦ (E Y, 0, 0, −Y D) + (headDirQK Γ + headDirVO Γ' on the attention part)
  -- + (the rescalings α on the gated part)` on antisymmetric `Y` (the first theorem)
  let Φ := ((flatEDLin_dtgr θ).comp (antisymmetric d).subtype).coprod
    (((sumInlLin_dtgr (A := Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh)
        (B := Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) (dIn := dIn) (dOut := dOut)).comp
      ((headDirQKLin_dtgr θ.sumFst).coprod (headDirVOLin_dtgr θ.sumFst))).coprod
      ((sumInrLin_dtgr (A := Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh)
        (B := Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) (dIn := dIn) (dOut := dOut)).comp
        (rescaleLin_dtgr θ.sumSnd)))
  have hV : ∀ η, (∀ x, smallWritesLimitNorm (Arch.attentionGated sees σ (rmsNorm ε) H dh hid) θ
      η x = 0) → η ∈ LinearMap.range Φ := by
    intro η hη
    obtain ⟨Y, Γ, Γ', α, hY, hE, hD, hr, hw, hg, hv, hwr⟩ :=
      smallWritesLimitNorm_eq_zero_attentionGated_rmsNorm hε hσ hσa hU t₁ t₂ h12 hs2 hs1 θ hθa
        hθm η hη
    refine ⟨(⟨Y, hY⟩, (Γ, Γ'), α), ?_⟩
    simp only [Φ, LinearMap.coprod_apply, LinearMap.comp_apply]
    apply Params.ext'
    · show θ.E * Y + (((0 : Matrix dIn d ℝ) + 0) + 0) = η.E
      rw [add_zero, add_zero, add_zero, hE]
    · intro ℓ
      ext a p
      rcases p with j | i | i
      · show (0 : ℝ) + ((headDirQK θ.sumFst Γ + headDirVO θ.sumFst Γ').read ℓ a j + 0)
          = η.read ℓ a (Sum.inl j)
        rw [zero_add, add_zero, ← hr ℓ]
        rfl
      · show (0 : ℝ) + (0 + 0) = η.read ℓ a (Sum.inr (Sum.inl i))
        rw [add_zero, add_zero]
        exact (hg ℓ i a).symm
      · show (0 : ℝ) + (0 + -(α ℓ i) * θ.sumSnd.read ℓ a (Sum.inr i))
          = η.read ℓ a (Sum.inr (Sum.inr i))
        rw [zero_add, zero_add]
        exact (hv ℓ i a).symm
    · intro ℓ
      ext p k
      rcases p with j | i
      · show (0 : ℝ) + ((headDirQK θ.sumFst Γ + headDirVO θ.sumFst Γ').write ℓ j k + 0)
          = η.write ℓ (Sum.inl j) k
        rw [zero_add, add_zero, ← hw ℓ]
        rfl
      · show (0 : ℝ) + (0 + α ℓ i * θ.sumSnd.write ℓ i k) = η.write ℓ (Sum.inr i) k
        rw [zero_add, zero_add]
        exact (hwr ℓ i k).symm
    · show -(Y * θ.D) + (((0 : Matrix d dOut ℝ) + 0) + 0) = η.D
      rw [add_zero, add_zero, add_zero, hD]
  -- `dim V ≤ d(d−1)/2 + 2 ∑_ℓ H_ℓ d_{h,ℓ}² + ∑_ℓ d_hidden,ℓ`, the dimension of the domain
  have hdim : Module.finrank ℝ (LinearMap.range Φ)
      ≤ Fintype.card d * (Fintype.card d - 1) / 2
        + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
          + ∑ ℓ, Fintype.card (hid ℓ)) := by
    have h := LinearMap.finrank_range_le Φ
    rwa [Module.finrank_prod, Module.finrank_prod, Module.finrank_prod, finrank_antisymmetric,
      finrank_headFun_dtgr, ← two_mul, finrank_hidFun_dtgr] at h
  -- `≥`: "The rank" of the proof of Lemma A.27 (`N_ε` and the blocks are analytic); `≤`: the
  -- upper bound for residual networks of attention blocks and gated blocks under pre-RMSNorm, as
  -- `θ ↦ θ_τ` changes neither `E` nor the reads
  filter_upwards [eventually_funDim_smallWrites_ge_norm
    (Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) θ
    (analyticOnNhd_rmsNorm hε) (fun ℓ => analyticOnNhd_f_sum
      (analyticOnNhd_f_attention sees (rmsNorm ε) H dh ℓ) (analyticOnNhd_f_gated hσa ℓ)) _ hV]
    with τ hτ
  have hle := funDim_add_le_residual_attentionGated_rmsNorm ε (θ.smallWrites τ) hθa.rank_E
    hθa.rank_Q hθa.rank_V (fun ℓ i => hθm.value_ne_zero ℓ i)
  generalize Fintype.card d * (Fintype.card d - 1) / 2 = N at hle hdim ⊢
  omega

omit [Fintype T] [Fintype dIn] [Fintype dOut] in
/-- Helper (as `rank_eq_of_isUnit_det_rows_dgr` of `Residual/DepthGatedRMS.lean`): a matrix
with `d` columns has rank `d` if some `d` of its rows form an invertible matrix. -/
private theorem rank_eq_of_isUnit_det_rows_dtgr {m : Type*} (M : Matrix m d ℝ) (ρ : d ↪ m)
    (h : IsUnit (M.submatrix ρ id).det) : M.rank = Fintype.card d :=
  le_antisymm (Matrix.rank_le_card_width M)
    ((Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).2 h)).symm.le.trans
      (Matrix.rank_submatrix_le M ρ id))

/-- Helper (a copy of `ae_smallWritesGenericGatedRMS` of `Residual/DepthGatedRMS.lean`, whose
statement carries `[Nonempty T]`; its proof does not use it): the conditions of Lemma A.27 under
pre-RMSNorm for gated blocks hold at generic parameters, for `d_in, d_out ≥ d ≥ 2`. -/
private theorem ae_smallWritesGenericGatedRMS_dtgr
    (μ : Measure (Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, SmallWritesGenericGatedRMS θ := by
  classical
  -- two distinct coordinates `k₁ ≠ k₂` of the hidden states, `d` rows of `E`, `d` columns of `D`
  obtain ⟨k₁, k₂, hk⟩ := Fintype.exists_pair_of_one_lt_card (show 1 < Fintype.card d by omega)
  obtain ⟨ρE⟩ := Function.Embedding.nonempty_of_card_le hdIn
  obtain ⟨cD⟩ := Function.Embedding.nonempty_of_card_le hdOut
  -- the ranks of `E` and `D`: invertible `d × d` minors (`Generic/Params.lean`)
  have h1 := ae_isUnit_det_submatrix μ
  -- an entry of a write or of a read is a linear functional of the parameters, not zero at the
  -- parameters with all entries `1`
  let θ₁ : Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut :=
    ⟨Matrix.of fun _ _ => 1, fun _ => Matrix.of fun _ _ => 1, fun _ => Matrix.of fun _ _ => 1,
      Matrix.of fun _ _ => 1⟩
  have hr : ∀ ℓ (k : d) (j : hid ℓ ⊕ hid ℓ), AnalyticOnNhd ℝ
      (fun θ : Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut =>
        θ.read ℓ k j) Set.univ := fun ℓ k j =>
    analyticOnNhd_linear ((Matrix.entryLinearMap ℝ ℝ k j).comp
      (Params.linRead (A := Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) (dIn := dIn)
        (dOut := dOut) ℓ))
  have hw : ∀ ℓ (i : hid ℓ) (k : d), AnalyticOnNhd ℝ
      (fun θ : Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut =>
        θ.write ℓ i k) Set.univ := fun ℓ i k =>
    analyticOnNhd_linear ((Matrix.entryLinearMap ℝ ℝ i k).comp
      (Params.linWrite (A := Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) (dIn := dIn)
        (dOut := dOut) ℓ))
  have h2 : ∀ᵐ θ ∂μ, ∀ ℓ (i : hid ℓ), θ.write ℓ i k₁ ≠ 0 :=
    ae_all_iff.2 fun ℓ => ae_all_iff.2 fun i =>
      ae_ne_zero_of_analytic μ (hw ℓ i k₁) ⟨θ₁, one_ne_zero⟩
  have h3 : ∀ᵐ θ ∂μ, ∀ ℓ (j : hid ℓ ⊕ hid ℓ), θ.read ℓ k₁ j ≠ 0 :=
    ae_all_iff.2 fun ℓ => ae_all_iff.2 fun j =>
      ae_ne_zero_of_analytic μ (hr ℓ k₁ j) ⟨θ₁, one_ne_zero⟩
  -- two gate columns, of the same block or of two blocks, are not collinear: a `2 × 2` minor does
  -- not vanish (it is not `0` for the reads cut out of a matrix `E₀ W₀` of `exists_minor_ne_zero`)
  have h4 : ∀ᵐ θ ∂μ, ∀ p q : (Σ ℓ, hid ℓ), p ≠ q →
      θ.read p.1 k₁ (Sum.inl p.2) * θ.read q.1 k₂ (Sum.inl q.2)
        - θ.read q.1 k₁ (Sum.inl q.2) * θ.read p.1 k₂ (Sum.inl p.2) ≠ 0 := by
    refine ae_all_iff.2 fun p => ae_all_iff.2 fun q => ?_
    by_cases hpq : p = q
    · exact Filter.Eventually.of_forall fun _ h _ => absurd hpq h
    · obtain ⟨E₀, W₀, hEW⟩ := exists_minor_ne_zero (q := Σ ℓ, hid ℓ) hk hk hpq
      -- the gate column of unit `p` of the read is column `p` of `E₀ W₀`, the values `0`
      let θ₀ : Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut :=
        ⟨0, fun ℓ => Matrix.of fun k j => Sum.elim (fun i => (E₀ * W₀) k ⟨ℓ, i⟩) (fun _ => 0) j,
          0, 0⟩
      have hg := ((hr p.1 k₁ (Sum.inl p.2)).mul (hr q.1 k₂ (Sum.inl q.2))).sub
        ((hr q.1 k₁ (Sum.inl q.2)).mul (hr p.1 k₂ (Sum.inl p.2)))
      exact (ae_ne_zero_of_analytic μ hg ⟨θ₀, hEW⟩).mono fun _ h _ => h
  filter_upwards [h1, h2, h3, h4] with θ h1 h2 h3 h4
  refine ⟨rank_eq_of_isUnit_det_rows_dtgr θ.E ρE (h1.2.2.1 ρE),
    rank_eq_card_of_isUnit_det θ.D cD (h1.2.1 cD), fun ℓ i hi => h2 ℓ i (congrFun hi k₁),
    fun ℓ i hi => h3 ℓ (Sum.inl i) (congrFun hi k₁), ?_,
    fun ℓ i hi => h3 ℓ (Sum.inr i) (congrFun hi k₁)⟩
  -- if `c_p = r c_q`, the minor of the gate columns `p`, `q` vanishes
  intro p q hpq r hr
  have e1 : θ.read p.1 k₁ (Sum.inl p.2) = r * θ.read q.1 k₁ (Sum.inl q.2) := congrFun hr k₁
  have e2 : θ.read p.1 k₂ (Sum.inl p.2) = r * θ.read q.1 k₂ (Sum.inl q.2) := congrFun hr k₂
  apply h4 p q hpq
  rw [e1, e2]
  ring


/-- **The conditions of Lemma A.27 under pre-RMSNorm hold at generic parameters,** for
`d_in, d_out ≥ d ≥ 2`, heads of width `1 ≤ d_h ≤ d` and blocks of any widths. -/
theorem ae_smallWritesGeneric_attentionGated_rmsNorm
    (μ : Measure (Params
      (Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ)) :
    ∀ᵐ θ ∂μ, SmallWritesGenericAttentionRMS θ.sumFst ∧ SmallWritesGenericGatedRMS θ.sumSnd := by
  -- the conditions on the attention part and on the gated part, each at generic parameters of
  -- its part; the parts of generic parameters of the sum are generic (`Generic/Sum.lean`)
  filter_upwards [ae_sumFst μ
      (ae_smallWritesGenericAttentionRMS Measure.addHaar hd hdIn hdOut hdh hdh0),
    ae_sumSnd μ (ae_smallWritesGenericGatedRMS_dtgr Measure.addHaar hd hdIn hdOut)] with θ h1 h2
  exact ⟨h1, h2⟩


/-- **Theorem 4.7 of the skips paper for attention blocks and gated blocks under pre-RMSNorm
(`ε > 0`):** with `d_in, d_out ≥ d ≥ 2`, heads of width `1 ≤ d_h ≤ d`, blocks of any widths and a
token that sees itself and another token, at almost every parameter the residual network has the
functional dimension `P − d(d−1)/2 − 2 ∑_ℓ H_ℓ d_{h,ℓ}² − ∑_ℓ d_hidden,ℓ`. -/
theorem ae_funDim_attentionGated_residual_rmsNorm (hε : 0 < ε)
    (hσ : ∀ z, HasDerivAt σ (σ' z) z) (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (hU : GatedUnitsRescale σ σ' d d (Σ ℓ, hid ℓ))
    (μ : Measure (Params
      (Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ θ ∂μ, funDim (Arch.attentionGated sees σ (rmsNorm ε) H dh hid) 1 θ
        + (Fintype.card d * (Fintype.card d - 1) / 2
          + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
              + ∑ ℓ, Fintype.card (hid ℓ)))
      = Module.finrank ℝ
          (Params
            (Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut) := by
  have : Nonempty d := Fintype.card_pos_iff.1 (by omega)
  -- one parameter `θ₀` with the conditions of Lemma A.27, and one small `τ ≠ 0`:
  -- `fd(θ₀_τ) = P − d(d−1)/2 − s`
  obtain ⟨θ₀, hθ₀a, hθ₀m⟩ :=
    (ae_smallWritesGeneric_attentionGated_rmsNorm μ hd hdIn hdOut hdh hdh0).exists
  obtain ⟨τ, hτ⟩ := (eventually_funDim_smallWrites_attentionGated_rmsNorm hε hσ hσa hU t₁ t₂ h12
    hs2 hs1 θ₀ hθ₀a hθ₀m).exists
  -- at almost every `θ`, `fd(θ) ≥ fd(θ₀_τ)` (analytic blocks and `N_ε`) and
  -- `fd(θ) ≤ P − d(d−1)/2 − s`
  filter_upwards [ae_funDim_ge (Arch.attentionGated sees σ (rmsNorm ε) H dh hid) 1
      (fun ℓ => analyticOnNhd_f_sum (analyticOnNhd_f_attention sees (rmsNorm ε) H dh ℓ)
        (analyticOnNhd_f_gated hσa ℓ)) (analyticOnNhd_rmsNorm hε) μ (θ₀.smallWrites τ),
    ae_funDim_add_le_residual_attentionGated_rmsNorm ε μ hdIn hdh] with θ h1 h2
  generalize Fintype.card d * (Fintype.card d - 1) / 2 = N at hτ h2 ⊢
  omega


/-- **Theorem 4.7, the gain, for attention blocks and gated blocks under pre-RMSNorm
(`ε > 0`):** if moreover every block has total width `H d_h + d_hidden ≥ d`, at almost every
parameter the skips raise the functional dimension by at least `L d(d−1)/2`. -/
theorem ae_funDim_attentionGated_residual_rmsNorm_ge_add (hε : 0 < ε)
    (hσ : ∀ z, HasDerivAt σ (σ' z) z) (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (hU : GatedUnitsRescale σ σ' d d (Σ ℓ, hid ℓ))
    (μ : Measure (Params
      (Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (hW : ∀ ℓ,
      Fintype.card d ≤ Fintype.card (H ℓ) * Fintype.card (dh ℓ) + Fintype.card (hid ℓ))
    (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ θ ∂μ, funDim (Arch.attentionGated sees σ (rmsNorm ε) H dh hid) 0 θ
        + L * (Fintype.card d * (Fintype.card d - 1) / 2)
      ≤ funDim (Arch.attentionGated sees σ (rmsNorm ε) H dh hid) 1 θ := by
  have : Nonempty d := Fintype.card_pos_iff.1 (by omega)
  -- `fd₁ = P − d(d−1)/2 − s` and `fd₀ ≤ P − (L + 1) d(d−1)/2 − s`
  filter_upwards [ae_funDim_attentionGated_residual_rmsNorm hε hσ hσa hU μ hd hdIn hdOut hdh hdh0
      t₁ t₂ h12 hs2 hs1, ae_funDim_add_le_skipless_attentionGated_rmsNorm ε μ hdIn hdh hW]
    with θ h1 h2
  rw [add_one_mul] at h2
  generalize Fintype.card d * (Fintype.card d - 1) / 2 = N at h1 h2 ⊢
  omega


/-- **Theorem 4.7 of the skips paper for attention blocks and SwiGLU blocks under pre-RMSNorm
(`ε > 0`):** at almost every parameter the residual network has the functional dimension
`P − d(d−1)/2 − 2 ∑_ℓ H_ℓ d_{h,ℓ}² − ∑_ℓ d_hidden,ℓ`. -/
theorem ae_funDim_attention_swiglu_residual_rmsNorm (hε : 0 < ε)
    (μ : Measure (Params
      (Arch.attentionGated (T := T) (d := d) sees silu (rmsNorm ε) H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ θ ∂μ, funDim (Arch.attentionGated sees silu (rmsNorm ε) H dh hid) 1 θ
        + (Fintype.card d * (Fintype.card d - 1) / 2
          + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
              + ∑ ℓ, Fintype.card (hid ℓ)))
      = Module.finrank ℝ
          (Params
            (Arch.attentionGated (T := T) (d := d) sees silu (rmsNorm ε) H dh hid) dIn dOut) := by
  exact ae_funDim_attentionGated_residual_rmsNorm hε hasDerivAt_silu analyticOnNhd_silu
    (silu_gatedUnitsRescale _ _ _) μ hd hdIn hdOut hdh hdh0 t₁ t₂ h12 hs2 hs1


/-- **Theorem 4.7 of the skips paper for attention blocks and GeGLU blocks under pre-RMSNorm
(`ε > 0`):** at almost every parameter the residual network has the functional dimension
`P − d(d−1)/2 − 2 ∑_ℓ H_ℓ d_{h,ℓ}² − ∑_ℓ d_hidden,ℓ`. -/
theorem ae_funDim_attention_geglu_residual_rmsNorm (hε : 0 < ε)
    (μ : Measure (Params
      (Arch.attentionGated (T := T) (d := d) sees gelu (rmsNorm ε) H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ θ ∂μ, funDim (Arch.attentionGated sees gelu (rmsNorm ε) H dh hid) 1 θ
        + (Fintype.card d * (Fintype.card d - 1) / 2
          + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
              + ∑ ℓ, Fintype.card (hid ℓ)))
      = Module.finrank ℝ
          (Params
            (Arch.attentionGated (T := T) (d := d) sees gelu (rmsNorm ε) H dh hid) dIn dOut) := by
  exact ae_funDim_attentionGated_residual_rmsNorm hε hasDerivAt_gelu analyticOnNhd_gelu
    (gelu_gatedUnitsRescale _ _ _) μ hd hdIn hdOut hdh hdh0 t₁ t₂ h12 hs2 hs1

end Skips
