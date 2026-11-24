import SkipsLean.Depth.HiddenZero
import SkipsLean.Dimension.SubmersionNull
import SkipsLean.Dimension.Functional
import SkipsLean.Generic.Params

/-!
# The domain of the case (0): open, with a complement of measure zero, and the outputs analytic

Paper (dimension paper): Appendix D.6, Lemma D.20 (The domain). "In the case (0), let `X` be a
finite batch of nonzero inputs, and let `O_X ⊂ ℝ^P` be the set of parameters at which the hidden
states `h_0, …, h_L` of the network are nonzero for every `x ∈ X`. Then `O_X` is open and
connected, its complement has measure zero, and the outputs `F_X` on the batch are real-analytic
on `O_X`."

Its proof: "Let `O^0` be the set of parameters with `xE ≠ 0` for all `x ∈ X`, and for `ℓ ≥ 1` let
`O^ℓ` be the set of parameters in `O^{ℓ−1}` with `h_ℓ ≠ 0` for all `x ∈ X`. […] For tanh and GELU,
`σ(z) = 0` only at `z = 0`. […] Removing finitely many closed submanifolds of codimension at least
two, one after the other, from a connected open set leaves a connected open set and removes a set
of measure zero."

Stated here for networks of MLP blocks under pre-RMSNorm with `ε = 0` whose activation `σ` is
real-analytic and vanishes exactly at `0` (tanh and GELU are of this kind). `hiddenNonzero σ hid X k`
is the paper's `O^k`: no row of `h_0, …, h_k` vanishes at any input of the batch (a hidden state
has the rows `T`), and `O_X` is `O^L`. "Nonzero inputs": no row of an input vanishes. This file has
"open", "its complement has measure zero" and "the outputs are real-analytic"; "connected" is
`Depth/DomainZeroConnected.lean`.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut] {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)] {σ : ℝ → ℝ}

/-- **The sets `O^k` of the proof of Lemma D.20:** the parameters at which no row of the hidden
states `h_0, …, h_k` vanishes, at every input of the batch `X`. The paper's `O_X` is `O^L`,
`hiddenNonzero σ hid X (Fin.last L)`. -/
def hiddenNonzero (σ : ℝ → ℝ) (hid : Fin L → Type) [∀ ℓ, Fintype (hid ℓ)] {n : ℕ}
    (X : Fin n → Matrix T dIn ℝ) (k : Fin (L + 1)) :
    Set (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) :=
  {θ | ∀ (i : Fin n) (j : Fin (L + 1)), j ≤ k →
    ∀ t, hidden (Arch.mlp σ (rmsNorm 0) hid) 0 θ (X i) j t ≠ 0}

/-- Helper: a row of a matrix-valued map that is real-analytic at `θ` is real-analytic at `θ`. -/
private theorem analyticAt_row_dz {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m k : Type*} [Fintype m] [Fintype k] {F : E → Matrix m k ℝ} {θ : E}
    (hF : AnalyticAt ℝ F θ) (t : m) : AnalyticAt ℝ (fun θ' => F θ' t) θ :=
  analyticAt_pi_iff.1 hF t

/-- **Lemma D.20, "`O_X` is open":** for a real-analytic `σ`, every `O^k` is open. -/
theorem isOpen_hiddenNonzero (hσa : AnalyticOnNhd ℝ σ Set.univ) {n : ℕ}
    (X : Fin n → Matrix T dIn ℝ) (k : Fin (L + 1)) :
    IsOpen (hiddenNonzero σ hid X k :
      Set (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)) := by
  -- finitely many conditions, each of which holds near `θ`: `h_j` is continuous at `θ`
  refine isOpen_iff_mem_nhds.2 fun θ hθ => ?_
  have key : ∀ (i : Fin n) (j : Fin (L + 1)) (t : T), ∀ᶠ θ' in nhds θ, j ≤ k →
      hidden (Arch.mlp σ (rmsNorm 0) hid) 0 θ' (X i) j t ≠ 0 := by
    intro i j t
    by_cases hj : j ≤ k
    · have ha := analyticAt_row_dz (analyticAt_hidden_rmsNorm_zero hσa θ (X i) j
        fun i' hi' => hθ i i' (le_trans hi'.le hj)) t
      exact (ha.continuousAt.eventually_ne (hθ i j hj t)).mono fun _ h _ => h
    · exact Filter.Eventually.of_forall fun _ h => absurd h hj
  filter_upwards [Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j =>
    Filter.eventually_all.2 fun t => key i j t] with θ' h i j hj t
  exact h i j t hj

omit [Fintype T] [DecidableEq d] in
/-- Helper (the set `O^0`): if the row `t` of `x` is not zero, the parameters at which the row `t`
of `x E` vanishes form a null set. The map `θ ↦ (x E)_t` is linear and onto `ℝ^d`. -/
private theorem measure_embed_row_eq_zero_dz {A : Arch T d L} (μ : Measure (Params A dIn dOut))
    [μ.IsAddHaarMeasure] [Nonempty d] (x : Matrix T dIn ℝ) (t : T) (hx : x t ≠ 0) :
    μ {θ : Params A dIn dOut | (x * θ.E) t = 0} = 0 := by
  classical
  let f : Params A dIn dOut →ₗ[ℝ] (d → ℝ) :=
    { toFun := fun θ => (x * θ.E) t
      map_add' := fun θ η => by simp only [Params.add_E, Matrix.mul_add]; rfl
      map_smul' := fun c θ => by simp only [Params.smul_E, Matrix.mul_smul]; rfl }
  let F := LinearMap.toContinuousLinearMap f
  -- onto: put `y / x_{tc}` in the row `c` of `E`, where `x_{tc} ≠ 0`
  have hsurj : Function.Surjective F := by
    intro y
    obtain ⟨c, hc⟩ := Function.ne_iff.1 hx
    have hc' : x t c ≠ 0 := hc
    refine ⟨⟨Matrix.of fun a b => if a = c then y b / x t c else 0, fun _ => 0, fun _ => 0, 0⟩,
      ?_⟩
    funext b
    show (x * Matrix.of fun a b => if a = c then y b / x t c else 0) t b = y b
    simp only [Matrix.mul_apply, Matrix.of_apply, mul_ite, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true]
    field_simp
  -- the preimage of the null set `{0}` under a linear map onto `ℝ^d` is null
  have h := measure_inter_preimage_eq_zero_of_surjective_fderiv μ (volume : Measure (d → ℝ)) F
    Set.univ isOpen_univ F.contDiff.contDiffOn (fun θ _ => by rw [F.fderiv]; exact hsurj) {0}
    (measure_singleton 0)
  rw [Set.univ_inter] at h
  exact h

/-- **Lemma D.20, "its complement has measure zero":** let `σ` be real-analytic and vanish exactly
at `0`, `d ≥ 2`, every block with at least two hidden units, and no row of an input of the batch
zero. Then the complement of every `O^k` has measure zero. -/
theorem measure_compl_hiddenNonzero (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (hσ0 : ∀ z : ℝ, σ z = 0 ↔ z = 0) (hd : 2 ≤ Fintype.card d)
    (hhid : ∀ ℓ, 2 ≤ Fintype.card (hid ℓ)) {n : ℕ} (X : Fin n → Matrix T dIn ℝ)
    (hX : ∀ i t, X i t ≠ 0)
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (k : Fin (L + 1)) :
    μ (hiddenNonzero σ hid X k)ᶜ = 0 := by
  have : Nonempty d := Fintype.card_pos_iff.1 (by omega)
  induction k using Fin.induction with
  | zero =>
    -- `O⁰` fails only where a row of some `x E` vanishes
    have hsub : (hiddenNonzero σ hid X 0 :
        Set (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut))ᶜ ⊆
        ⋃ i, ⋃ t, {θ | (X i * θ.E) t = 0} := by
      intro θ hθ
      by_contra hne
      refine hθ fun i j hj t h => hne (Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨t, ?_⟩⟩)
      obtain rfl : j = 0 := Fin.le_zero_iff.1 hj
      rw [hidden_zero] at h
      exact h
    exact measure_mono_null hsub (measure_iUnion_null fun i => measure_iUnion_null fun t =>
      measure_embed_row_eq_zero_dz μ (X i) t (hX i t))
  | succ ℓ ih =>
    have : Nonempty (hid ℓ) := Fintype.card_pos_iff.1 (by have := hhid ℓ; omega)
    have hO := isOpen_hiddenNonzero (d := d) (dOut := dOut) (hid := hid) hσa X ℓ.castSucc
    -- `G i t`: row `t` of what block `ℓ` reads; `H i t`: row `t` of `h_{ℓ+1}`, at the input `X i`
    let G : Fin n → T → Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut →
        (hid ℓ → ℝ) := fun i t θ =>
      (rmsNorm 0 (hidden (Arch.mlp σ (rmsNorm 0) hid) 0 θ (X i) ℓ.castSucc) * θ.read ℓ :
        Matrix T (hid ℓ) ℝ) t
    let H : Fin n → T → Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut →
        (d → ℝ) := fun i t θ => hidden (Arch.mlp σ (rmsNorm 0) hid) 0 θ (X i) ℓ.succ t
    have hGa : ∀ i t, ∀ θ ∈ hiddenNonzero σ hid X ℓ.castSucc, AnalyticAt ℝ (G i t) θ :=
      fun i t θ hθ =>
        analyticAt_row_dz (analyticAt_preactivation_rmsNorm_zero hσa θ (X i) ℓ (hθ i)) t
    have hHa : ∀ i t, ∀ θ ∈ hiddenNonzero σ hid X ℓ.castSucc, AnalyticAt ℝ (H i t) θ :=
      fun i t θ hθ => analyticAt_row_dz (analyticAt_hidden_rmsNorm_zero hσa θ (X i) ℓ.succ
        fun i' hi' => hθ i i' (Fin.le_castSucc_iff.2 hi')) t
    -- outside `O^ℓ` and outside `O^{ℓ-1}`: a row of `h_ℓ` vanishes, where the read is zero or not
    have hsub : (hiddenNonzero σ hid X ℓ.succ :
        Set (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut))ᶜ ⊆
        (hiddenNonzero σ hid X ℓ.castSucc)ᶜ ∪
          ((⋃ i, ⋃ t, hiddenNonzero σ hid X ℓ.castSucc ∩ G i t ⁻¹' {0}) ∪
            ⋃ i, ⋃ t, (hiddenNonzero σ hid X ℓ.castSucc ∩ G i t ⁻¹' {0}ᶜ) ∩ H i t ⁻¹' {0}) := by
      intro θ hθ
      by_cases h0 : θ ∈ hiddenNonzero σ hid X ℓ.castSucc
      · right
        have hex : ∃ i t, H i t θ = 0 := by
          by_contra hne
          refine hθ fun i j hj t => ?_
          rcases hj.lt_or_eq with hlt | rfl
          · exact h0 i j (Fin.le_castSucc_iff.2 hlt) t
          · exact fun h => hne ⟨i, t, h⟩
        obtain ⟨i, t, hH⟩ := hex
        by_cases hG : G i t θ = 0
        · exact Or.inl (Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨t, h0, hG⟩⟩)
        · exact Or.inr (Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨t, ⟨h0, hG⟩, hH⟩⟩)
      · exact Or.inl h0
    refine measure_mono_null hsub (measure_union_null ih (measure_union_null
      (measure_iUnion_null fun i => measure_iUnion_null fun t => ?_)
      (measure_iUnion_null fun i => measure_iUnion_null fun t => ?_)))
    · -- the read vanishes: a null set, since its derivative is onto
      exact measure_inter_preimage_eq_zero_of_surjective_fderiv μ (volume : Measure (hid ℓ → ℝ))
        (G i t) _ hO (fun θ hθ => (hGa i t θ hθ).contDiffAt.contDiffWithinAt)
        (fun θ hθ => surjective_fderiv_preactivation hσa θ (X i) ℓ t (hθ i)) {0}
        (measure_singleton 0)
    · -- the read is not zero and the row of `h_{ℓ+1}` vanishes: null, its derivative is onto
      have hU : IsOpen (hiddenNonzero σ hid X ℓ.castSucc ∩ G i t ⁻¹' {0}ᶜ :
          Set (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)) :=
        ContinuousOn.isOpen_inter_preimage
          (fun θ hθ => (hGa i t θ hθ).continuousAt.continuousWithinAt) hO isOpen_compl_singleton
      exact measure_inter_preimage_eq_zero_of_surjective_fderiv μ (volume : Measure (d → ℝ))
        (H i t) _ hU (fun θ hθ => (hHa i t θ hθ.1).contDiffAt.contDiffWithinAt)
        (fun θ hθ => surjective_fderiv_hidden_succ hσa (fun z => (hσ0 z).1) θ (X i) ℓ t
          (hθ.1 i) hθ.2) {0} (measure_singleton 0)

/-- **Lemma D.20, "the outputs `F_X` on the batch are real-analytic on `O_X`":** for a
real-analytic `σ`, the outputs on the batch `X` are real-analytic on `O^L`. -/
theorem analyticOnNhd_evalBatch_hiddenNonzero (hσa : AnalyticOnNhd ℝ σ Set.univ) {n : ℕ}
    (X : Fin n → Matrix T dIn ℝ) :
    AnalyticOnNhd ℝ
      (evalBatch (Arch.mlp σ (rmsNorm 0) hid) 0 X :
        Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut →
          Fin n → Matrix T dOut ℝ)
      (hiddenNonzero σ hid X (Fin.last L)) := by
  -- at a point of `O^L` no row of a hidden state vanishes, so each output is analytic there
  intro θ hθ
  exact AnalyticAt.pi fun i => analyticAt_eval_rmsNorm_zero hσa θ (X i)
    fun j t => hθ i j (Fin.le_last j) t

end Skips
