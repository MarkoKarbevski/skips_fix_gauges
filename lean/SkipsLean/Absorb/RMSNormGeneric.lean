import SkipsLean.Absorb.RMSNormRays
import SkipsLean.Generic.Params
import SkipsLean.Generic.Gated
import SkipsLean.Dimension.RescalingMlp

/-!
# Under RMSNorm a residual network equals no skipless network: almost every choice of weights

Paper ("Can an MLP Absorb Its Skip Connection Exactly?"): Theorem 4.3. "Consider pre-RMSNorm
networks, with `ε ≥ 0` and blocks of any kind and width. For almost every choice of weights, a
residual network equals no skipless network, whatever its depth, widths and kinds of blocks."

`Absorb/RMSNormRays.lean` has the comparison along rays, under the conditions `TurnGeneric` on the
weights of the residual network. This file has the last part of the proof (Appendix A.3, "Measure
zero"): the conditions hold for almost every choice of weights. "Fix all weights but the writes.
The condition is linear in the writes, so the writes that satisfy it form a linear subspace. The
subspace is proper if some `a_ℓ(n̄)` has a nonzero entry at some `n̄` … And `a_1` vanishes for all
`n̄` only if the read of block 1 has a zero column, which happens on a set of measure zero. The
weights that satisfy the condition form a closed set … and by Fubini's theorem this set has
measure zero."

For blocks of any kind, what the argument uses of the blocks is that, for almost every choice of
weights, some block has a nonzero output at some normalized state (`SomeBlockNonzero`). The
theorem is stated first with this as a hypothesis, for arbitrary continuous maps `f_ℓ`, and then
for networks of MLP blocks and of gated blocks whose activation (or gate) `σ` is locally Lipschitz
and nonzero on the positive reals, where the hypothesis holds as soon as some block has a hidden
unit. tanh, GELU, ReLU, ReLU² and SiLU are such activations. The scope of the paper is
`d_in, d_out ≥ d ≥ 2`. The skipless network is of any kind: an arbitrary `Arch`.
-/

namespace Skips

open Matrix MeasureTheory Filter
open scoped Matrix.Norms.Elementwise Topology

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]

/-- Some block has a nonzero output at some normalized state: there are a block `ℓ` and a matrix
`n̄` whose rows have norm `√d` with `f_ℓ(n̄ W_read^ℓ) ≠ 0`. -/
def SomeBlockNonzero (A : Arch T d L) (θ : Params A dIn dOut) : Prop :=
  ∃ ℓ, ∃ n : Matrix T d ℝ, (∀ t, n t ⬝ᵥ n t = (Fintype.card d : ℝ)) ∧ A.f ℓ (n * θ.read ℓ) ≠ 0

/-! ### Blocks of any kind -/

/-- **Appendix A.3, "Measure zero".** If the maps `f_ℓ` are continuous and, for almost every choice
of weights, some block has a nonzero output at some normalized state, then the conditions
`TurnGeneric` hold for almost every choice of weights (`d_in, d_out ≥ d ≥ 2`). -/
theorem ae_turnGeneric (A : Arch T d L) (hf : ∀ ℓ, Continuous (A.f ℓ))
    (μ : Measure (Params A dIn dOut)) [μ.IsAddHaarMeasure]
    (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hA : ∀ᵐ θ ∂μ, SomeBlockNonzero A θ) :
    ∀ᵐ θ ∂μ, TurnGeneric A θ := by
  sorry

/-- **Theorem 4.3 for `ε > 0`, blocks of any kind.** For almost every choice of weights, a
pre-RMSNorm residual network with locally Lipschitz blocks equals no pre-RMSNorm skipless network
with locally Lipschitz blocks, whatever its depth, model dimension, widths, kinds of blocks and
constant `ε' > 0`. -/
theorem ae_ne_skipless_rmsNorm {ε : ℝ} (hε : 0 < ε) (A : Arch T d L) (hχ : A.χ = rmsNorm ε)
    (hf : ∀ ℓ, LocallyLipschitz (A.f ℓ))
    (μ : Measure (Params A dIn dOut)) [μ.IsAddHaarMeasure]
    (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hA : ∀ᵐ θ ∂μ, SomeBlockNonzero A θ) :
    ∀ᵐ θ ∂μ, ∀ (L' : ℕ) (d' : Type) [Fintype d'] (A' : Arch T d' L') (ε' : ℝ), 0 < ε' →
      A'.χ = rmsNorm ε' → (∀ ℓ, LocallyLipschitz (A'.f ℓ)) → ∀ θ' : Params A' dIn dOut,
        ∃ X : Matrix T dIn ℝ, eval A 1 θ X ≠ eval A' 0 θ' X := by
  -- the conditions of the proof hold for almost every choice of weights, and under them the
  -- comparison along rays separates the two networks
  filter_upwards [ae_turnGeneric A (fun ℓ => (hf ℓ).continuous) μ hd hdIn hdOut hA] with θ hθ
  intro L' d' _ A' ε' hε' hχ' hf' θ'
  exact exists_ne_skipless_rmsNorm_of_turn hε hε' A hχ hf θ hθ A' hχ' hf' θ'

/-- **Theorem 4.3 for `ε = 0`, blocks of any kind.** For almost every choice of weights, a
pre-RMSNorm residual network with `ε = 0` and locally Lipschitz blocks equals no pre-RMSNorm
skipless network with `ε = 0` and continuous blocks: there is no dense set of inputs at which both
networks are defined and agree. -/
theorem ae_not_dense_eq_skipless_rmsNorm_zero (A : Arch T d L) (hχ : A.χ = rmsNorm 0)
    (hf : ∀ ℓ, LocallyLipschitz (A.f ℓ))
    (μ : Measure (Params A dIn dOut)) [μ.IsAddHaarMeasure]
    (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hA : ∀ᵐ θ ∂μ, SomeBlockNonzero A θ) :
    ∀ᵐ θ ∂μ, ∀ (L' : ℕ) (d' : Type) [Fintype d'] (A' : Arch T d' L'), A'.χ = rmsNorm 0 →
      (∀ ℓ, Continuous (A'.f ℓ)) → ∀ θ' : Params A' dIn dOut,
        ¬ ∃ S : Set (Matrix T dIn ℝ), Dense S ∧
          ∀ X ∈ S, DefinedAt A 1 θ X ∧ DefinedAt A' 0 θ' X ∧ eval A 1 θ X = eval A' 0 θ' X := by
  -- the conditions of the proof hold for almost every choice of weights, and under them the
  -- comparison along rays separates the two networks
  filter_upwards [ae_turnGeneric A (fun ℓ => (hf ℓ).continuous) μ hd hdIn hdOut hA] with θ hθ
  intro L' d' _ A' hχ' hf' θ'
  exact not_dense_eq_skipless_rmsNorm_zero_of_turn A hχ hf θ hθ A' hχ' hf' θ'

/-! ### MLP blocks and gated blocks -/

variable {σ : ℝ → ℝ} {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]

/-- Helper: a map into a finite product of spaces, with the largest distance of the coordinates,
is locally Lipschitz if each coordinate is: on the intersection of the neighbourhoods, the sum of
the constants works for every coordinate. -/
private theorem locallyLipschitz_pi_of_forall {α ι : Type*} [PseudoEMetricSpace α] [Fintype ι]
    {β : ι → Type*} [∀ i, PseudoEMetricSpace (β i)] {g : α → ∀ i, β i}
    (h : ∀ i, LocallyLipschitz fun x => g x i) : LocallyLipschitz g := by
  intro x
  choose K t ht hK using fun i => h i x
  refine ⟨∑ i, K i, ⋂ i, t i, Filter.iInter_mem.2 ht, fun y hy z hz => ?_⟩
  rw [edist_pi_le_iff]
  intro i
  calc edist (g y i) (g z i) ≤ K i * edist y z :=
        hK i (Set.mem_iInter.1 hy i) (Set.mem_iInter.1 hz i)
    _ ≤ (∑ j, K j : NNReal) * edist y z := by
        gcongr
        exact Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_univ i)

/-- Helper: a map into matrices (elementwise norm) is locally Lipschitz if every entry is. -/
private theorem locallyLipschitz_matrix_of_forall {α m n : Type*} [PseudoEMetricSpace α]
    [Fintype m] [Fintype n] {g : α → Matrix m n ℝ}
    (h : ∀ i j, LocallyLipschitz fun x => g x i j) : LocallyLipschitz g :=
  locallyLipschitz_pi_of_forall fun i => locallyLipschitz_pi_of_forall fun j => h i j

/-- Helper: an entry of a matrix is a `1`-Lipschitz function of the matrix, hence locally
Lipschitz. -/
private theorem locallyLipschitz_entry {m n : Type*} [Fintype m] [Fintype n] (i : m) (j : n) :
    LocallyLipschitz fun M : Matrix m n ℝ => M i j :=
  ((LipschitzWith.eval (α := fun _ : n => ℝ) j).comp
    (LipschitzWith.eval (α := fun _ : m => n → ℝ) i)).locallyLipschitz

/-- Helper: the product of two locally Lipschitz real functions is locally Lipschitz
(multiplication `ℝ × ℝ → ℝ` is smooth, hence locally Lipschitz). -/
private theorem locallyLipschitz_mul_real {α : Type*} [PseudoEMetricSpace α] {f g : α → ℝ}
    (hf : LocallyLipschitz f) (hg : LocallyLipschitz g) : LocallyLipschitz fun x => f x * g x :=
  ((contDiff_mul (𝕜 := ℝ) (n := 1) (𝔸 := ℝ)).locallyLipschitz).comp (hf.prodMk hg)

omit [Fintype d] [DecidableEq d] in
/-- An MLP block with a locally Lipschitz activation is locally Lipschitz. -/
theorem locallyLipschitz_f_mlp {χ : Matrix T d ℝ → Matrix T d ℝ} (hσ : LocallyLipschitz σ)
    (ℓ : Fin L) : LocallyLipschitz ((Arch.mlp (T := T) (d := d) σ χ hid).f ℓ) := by
  -- entry `(t, i)` of the output is `σ (M t i)`
  refine locallyLipschitz_matrix_of_forall fun t i => ?_
  exact hσ.comp (locallyLipschitz_entry t i)

omit [Fintype d] [DecidableEq d] in
/-- A gated block with a locally Lipschitz gate is locally Lipschitz. -/
theorem locallyLipschitz_f_gated {χ : Matrix T d ℝ → Matrix T d ℝ} (hσ : LocallyLipschitz σ)
    (ℓ : Fin L) : LocallyLipschitz ((Arch.gated (T := T) (d := d) σ χ hid).f ℓ) := by
  -- entry `(t, i)` of the output is `σ (M t (inl i)) * M t (inr i)`
  refine locallyLipschitz_matrix_of_forall fun t i => ?_
  exact locallyLipschitz_mul_real (hσ.comp (locallyLipschitz_entry t (Sum.inl i)))
    (locallyLipschitz_entry t (Sum.inr i))

omit [DecidableEq d] in
/-- Helper: a nonzero vector `c` has `c ⬝ᵥ c > 0` and a positive multiple `λ c` with
`(λ c) ⬝ᵥ (λ c) = d`, namely `λ = √(d / c ⬝ᵥ c)`. -/
private theorem exists_pos_smul_normalized [Nonempty d] {c : d → ℝ} (hc : c ≠ 0) :
    0 < c ⬝ᵥ c ∧ ∃ lam : ℝ, 0 < lam ∧ (lam • c) ⬝ᵥ (lam • c) = (Fintype.card d : ℝ) := by
  have hs : 0 < c ⬝ᵥ c := lt_of_le_of_ne (Finset.sum_nonneg fun i _ => mul_self_nonneg (c i))
    (Ne.symm (dotProduct_self_eq_zero.not.2 hc))
  have hd : (0 : ℝ) < Fintype.card d := Nat.cast_pos.2 Fintype.card_pos
  refine ⟨hs, Real.sqrt (Fintype.card d / (c ⬝ᵥ c)), Real.sqrt_pos.2 (div_pos hd hs), ?_⟩
  rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc,
    Real.mul_self_sqrt (div_pos hd hs).le, div_mul_cancel₀ _ hs.ne']

/-- For a network of MLP blocks whose activation is nonzero on the positive reals, in which some
block has a hidden unit: for almost every choice of weights, some block has a nonzero output at
some normalized state (a read column `c ≠ 0` and the state with all rows `√d c / ‖c‖`). -/
theorem ae_someBlockNonzero_mlp [Nonempty T] [Nonempty d] {χ : Matrix T d ℝ → Matrix T d ℝ}
    (hσ : ∀ z, 0 < z → σ z ≠ 0) (hhid : ∃ ℓ, Nonempty (hid ℓ))
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) σ χ hid) dIn dOut)) [μ.IsAddHaarMeasure] :
    ∀ᵐ θ ∂μ, SomeBlockNonzero (Arch.mlp σ χ hid) θ := by
  obtain ⟨ℓ, ⟨i⟩⟩ := hhid
  obtain t₀ : T := Classical.arbitrary T
  -- no column of a read vanishes, for almost every choice of weights
  filter_upwards [ae_read_col_ne_zero μ] with θ hθ
  -- the column `c` of unit `i`, and the state `n̄` with every row `λ c`
  set c : d → ℝ := fun a => θ.read ℓ a i with hc
  obtain ⟨hs, lam, hlam, hn⟩ := exists_pos_smul_normalized (hθ ℓ i)
  refine ⟨ℓ, Matrix.of fun _ => lam • c, fun _ => hn, fun h => hσ _ (mul_pos hlam hs) ?_⟩
  -- the argument of unit `i` is `λ (c ⬝ᵥ c) > 0`, and `σ` of it would vanish
  have harg : (Matrix.of (fun _ : T => lam • c) * θ.read ℓ) t₀ i = lam * (c ⬝ᵥ c) := by
    rw [← smul_eq_mul, ← smul_dotProduct]
    rfl
  rw [← harg]
  exact congrFun (congrFun h t₀) i

omit [Fintype T] [DecidableEq d] in
/-- The same for a network of gated blocks whose gate is nonzero on the positive reals. -/
theorem ae_someBlockNonzero_gated [Nonempty T] [Nonempty d] {χ : Matrix T d ℝ → Matrix T d ℝ}
    (hσ : ∀ z, 0 < z → σ z ≠ 0) (hhid : ∃ ℓ, Nonempty (hid ℓ))
    (μ : Measure (Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut)) [μ.IsAddHaarMeasure] :
    ∀ᵐ θ ∂μ, SomeBlockNonzero (Arch.gated σ χ hid) θ := by
  obtain ⟨ℓ, ⟨i⟩⟩ := hhid
  obtain t₀ : T := Classical.arbitrary T
  -- the gate column `c` and the value column `e` of unit `i` have `c ⬝ᵥ e ≠ 0` for almost every
  -- choice of weights: `θ ↦ c ⬝ᵥ e` is a polynomial, equal to `d` at the reads with entries `1`
  have hge : ∀ᵐ θ ∂μ,
      (fun a => θ.read ℓ a (Sum.inl i)) ⬝ᵥ (fun a => θ.read ℓ a (Sum.inr i)) ≠ 0 := by
    let lg : d → Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut →ₗ[ℝ] ℝ := fun a =>
      (Matrix.entryLinearMap ℝ ℝ a (Sum.inl i)).comp
        (Params.linRead (A := Arch.gated (T := T) (d := d) σ χ hid) (dIn := dIn) (dOut := dOut) ℓ)
    let lv : d → Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut →ₗ[ℝ] ℝ := fun a =>
      (Matrix.entryLinearMap ℝ ℝ a (Sum.inr i)).comp
        (Params.linRead (A := Arch.gated (T := T) (d := d) σ χ hid) (dIn := dIn) (dOut := dOut) ℓ)
    have hg : AnalyticOnNhd ℝ
        (fun θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut => ∑ a, lg a θ * lv a θ)
        Set.univ :=
      Finset.analyticOnNhd_fun_sum _ fun a _ =>
        (analyticOnNhd_linear (lg a)).mul (analyticOnNhd_linear (lv a))
    have hne : ∃ θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut,
        ∑ a, lg a θ * lv a θ ≠ 0 := by
      refine ⟨⟨0, fun _ => Matrix.of fun _ _ => 1, 0, 0⟩, ?_⟩
      show ∑ _a : d, (1 : ℝ) * 1 ≠ 0
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, mul_one]
      exact Nat.cast_ne_zero.2 Fintype.card_ne_zero
    filter_upwards [ae_ne_zero_of_analytic μ hg hne] with θ hθ
    exact hθ
  filter_upwards [hge] with θ hθ
  set c : d → ℝ := fun a => θ.read ℓ a (Sum.inl i) with hc
  set e : d → ℝ := fun a => θ.read ℓ a (Sum.inr i) with he
  have hc0 : c ≠ 0 := fun h0 => hθ (by rw [h0, zero_dotProduct])
  -- the state `n̄` with every row `λ c`
  obtain ⟨hs, lam, hlam, hn⟩ := exists_pos_smul_normalized hc0
  refine ⟨ℓ, Matrix.of fun _ => lam • c, fun _ => hn, fun h => ?_⟩
  -- the output of unit `i` is `σ(λ (c ⬝ᵥ c)) λ (c ⬝ᵥ e) ≠ 0`
  have hgate : (Matrix.of (fun _ : T => lam • c) * θ.read ℓ) t₀ (Sum.inl i) = lam * (c ⬝ᵥ c) := by
    rw [← smul_eq_mul, ← smul_dotProduct]
    rfl
  have hval : (Matrix.of (fun _ : T => lam • c) * θ.read ℓ) t₀ (Sum.inr i) = lam * (c ⬝ᵥ e) := by
    rw [← smul_eq_mul, ← smul_dotProduct]
    rfl
  have h1 : σ ((Matrix.of (fun _ : T => lam • c) * θ.read ℓ) t₀ (Sum.inl i)) *
      (Matrix.of (fun _ : T => lam • c) * θ.read ℓ) t₀ (Sum.inr i) = 0 :=
    congrFun (congrFun h t₀) i
  rw [hgate, hval] at h1
  exact mul_ne_zero (hσ _ (mul_pos hlam hs)) (mul_ne_zero hlam.ne' hθ) h1

/-- **Theorem 4.3 for `ε > 0`, residual networks of MLP blocks** whose activation is locally
Lipschitz and nonzero on the positive reals: for almost every choice of weights
(`d_in, d_out ≥ d ≥ 2`, some block has a hidden unit), the residual network equals no pre-RMSNorm
skipless network with locally Lipschitz blocks of any kind. -/
theorem ae_ne_skipless_rmsNorm_mlp [Nonempty T] {ε : ℝ} (hε : 0 < ε)
    (hσ : ∀ z, 0 < z → σ z ≠ 0) (hσL : LocallyLipschitz σ) (hhid : ∃ ℓ, Nonempty (hid ℓ))
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure]
    (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, ∀ (L' : ℕ) (d' : Type) [Fintype d'] (A' : Arch T d' L') (ε' : ℝ), 0 < ε' →
      A'.χ = rmsNorm ε' → (∀ ℓ, LocallyLipschitz (A'.f ℓ)) → ∀ θ' : Params A' dIn dOut,
        ∃ X : Matrix T dIn ℝ,
          eval (Arch.mlp σ (rmsNorm ε) hid) 1 θ X ≠ eval A' 0 θ' X := by
  have : Nonempty d := Fintype.card_pos_iff.1 (by omega)
  exact ae_ne_skipless_rmsNorm hε _ rfl (locallyLipschitz_f_mlp hσL) μ hd hdIn hdOut
    (ae_someBlockNonzero_mlp hσ hhid μ)

/-- **Theorem 4.3 for `ε = 0`, residual networks of MLP blocks.** -/
theorem ae_not_dense_eq_skipless_rmsNorm_zero_mlp [Nonempty T]
    (hσ : ∀ z, 0 < z → σ z ≠ 0) (hσL : LocallyLipschitz σ) (hhid : ∃ ℓ, Nonempty (hid ℓ))
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure]
    (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, ∀ (L' : ℕ) (d' : Type) [Fintype d'] (A' : Arch T d' L'), A'.χ = rmsNorm 0 →
      (∀ ℓ, Continuous (A'.f ℓ)) → ∀ θ' : Params A' dIn dOut,
        ¬ ∃ S : Set (Matrix T dIn ℝ), Dense S ∧
          ∀ X ∈ S, DefinedAt (Arch.mlp σ (rmsNorm 0) hid) 1 θ X ∧ DefinedAt A' 0 θ' X ∧
            eval (Arch.mlp σ (rmsNorm 0) hid) 1 θ X = eval A' 0 θ' X := by
  have : Nonempty d := Fintype.card_pos_iff.1 (by omega)
  exact ae_not_dense_eq_skipless_rmsNorm_zero _ rfl (locallyLipschitz_f_mlp hσL) μ hd hdIn hdOut
    (ae_someBlockNonzero_mlp hσ hhid μ)

/-- **Theorem 4.3 for `ε > 0`, residual networks of gated blocks** whose gate is locally Lipschitz
and nonzero on the positive reals. -/
theorem ae_ne_skipless_rmsNorm_gated [Nonempty T] {ε : ℝ} (hε : 0 < ε)
    (hσ : ∀ z, 0 < z → σ z ≠ 0) (hσL : LocallyLipschitz σ) (hhid : ∃ ℓ, Nonempty (hid ℓ))
    (μ : Measure (Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure]
    (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, ∀ (L' : ℕ) (d' : Type) [Fintype d'] (A' : Arch T d' L') (ε' : ℝ), 0 < ε' →
      A'.χ = rmsNorm ε' → (∀ ℓ, LocallyLipschitz (A'.f ℓ)) → ∀ θ' : Params A' dIn dOut,
        ∃ X : Matrix T dIn ℝ,
          eval (Arch.gated σ (rmsNorm ε) hid) 1 θ X ≠ eval A' 0 θ' X := by
  have : Nonempty d := Fintype.card_pos_iff.1 (by omega)
  exact ae_ne_skipless_rmsNorm hε _ rfl (locallyLipschitz_f_gated hσL) μ hd hdIn hdOut
    (ae_someBlockNonzero_gated hσ hhid μ)

/-- **Theorem 4.3 for `ε = 0`, residual networks of gated blocks.** -/
theorem ae_not_dense_eq_skipless_rmsNorm_zero_gated [Nonempty T]
    (hσ : ∀ z, 0 < z → σ z ≠ 0) (hσL : LocallyLipschitz σ) (hhid : ∃ ℓ, Nonempty (hid ℓ))
    (μ : Measure (Params (Arch.gated (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure]
    (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, ∀ (L' : ℕ) (d' : Type) [Fintype d'] (A' : Arch T d' L'), A'.χ = rmsNorm 0 →
      (∀ ℓ, Continuous (A'.f ℓ)) → ∀ θ' : Params A' dIn dOut,
        ¬ ∃ S : Set (Matrix T dIn ℝ), Dense S ∧
          ∀ X ∈ S, DefinedAt (Arch.gated σ (rmsNorm 0) hid) 1 θ X ∧ DefinedAt A' 0 θ' X ∧
            eval (Arch.gated σ (rmsNorm 0) hid) 1 θ X = eval A' 0 θ' X := by
  have : Nonempty d := Fintype.card_pos_iff.1 (by omega)
  exact ae_not_dense_eq_skipless_rmsNorm_zero _ rfl (locallyLipschitz_f_gated hσL) μ hd hdIn
    hdOut (ae_someBlockNonzero_gated hσ hhid μ)

end Skips
