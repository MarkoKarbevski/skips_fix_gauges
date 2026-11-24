import SkipsLean.Depth.DomainZero
import SkipsLean.Generic.ConnectedCompl

/-!
# The domain of the case (0) is connected

Paper (dimension paper): Appendix D.6, Lemma D.20 (The domain), "`O_X` is open and connected".

Its proof: "The complement of `O^0` is a finite union of subspaces of codimension `d_model ≥ 2`.
Let `ℓ ≥ 1` and `x ∈ X`. On `O^{ℓ−1}`, `h_ℓ = w̃_ℓ W_write^ℓ` with
`w̃_ℓ = σ(N(h_{ℓ−1}) W_read^ℓ)`, and `h_{ℓ−1}` does not depend on the weights of block `ℓ`. For tanh
and GELU, `σ(z) = 0` only at `z = 0`. So `w̃_ℓ = 0` exactly where `N(h_{ℓ−1}) W_read^ℓ = 0`, a
closed submanifold of `O^{ℓ−1}` of codimension at least `d_model ≥ 2`, because the derivative with
respect to `W_read^ℓ` is onto. Where `w̃_ℓ ≠ 0`, the derivative of `h_ℓ` with respect to `W_write^ℓ`
is onto `ℝ^{1×d_model}`, so there the parameters with `h_ℓ = 0` form a closed submanifold of
codimension `d_model ≥ 2`. Removing finitely many closed submanifolds of codimension at least two,
one after the other, from a connected open set leaves a connected open set".

`hiddenNonzero σ hid X k` (`Depth/DomainZero.lean`) is the paper's `O^k`. One removal is
`isPreconnected_diff_zeroSet_of_surjective` (`Generic/ConnectedCompl.lean`); the codimensions here
are the number of hidden units of the block (at least two) and `d ≥ 2`.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut] {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)] {σ : ℝ → ℝ}

/-- Helper: removing the zero sets of finitely many conditions, one at a time, from an open
preconnected set `U`, when each removal keeps an open preconnected subset of `U` open and
preconnected. -/
private theorem finset_induction_dzc {E ι : Type*} [TopologicalSpace E] {U : Set E}
    (hU : IsOpen U) (hUc : IsPreconnected U) (c : ι → Set E)
    (step : ∀ (p : ι) (V : Set E), V ⊆ U → IsOpen V → IsPreconnected V →
      IsOpen (V ∩ c p) ∧ IsPreconnected (V ∩ c p)) (s : Finset ι) :
    IsOpen (U ∩ ⋂ p ∈ s, c p) ∧ IsPreconnected (U ∩ ⋂ p ∈ s, c p) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using ⟨hU, hUc⟩
  | insert a s _ ih =>
    rw [Finset.set_biInter_insert, Set.inter_comm (c a), ← Set.inter_assoc]
    exact step a _ Set.inter_subset_left ih.1 ih.2

omit [Fintype T] [DecidableEq d] in
/-- Helper, the first removal (`k = 0`): for a nonzero row `v`, the parameters with `v E = 0`
form a subspace of codimension `d ≥ 2`, and removing it from an open preconnected set keeps it
open and preconnected. -/
private theorem removal_zero_dzc (hd : 2 ≤ Fintype.card d) (v : dIn → ℝ) (hv : v ≠ 0)
    (U : Set (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut))
    (hU : IsOpen U) (hUc : IsPreconnected U) :
    IsOpen (U ∩ {θ | v ᵥ* θ.E ≠ 0}) ∧ IsPreconnected (U ∩ {θ | v ᵥ* θ.E ≠ 0}) := by
  classical
  -- the linear map `θ ↦ v E`
  let l : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut →ₗ[ℝ] (d → ℝ) :=
    { toFun := fun θ => v ᵥ* θ.E
      map_add' := fun θ η => Matrix.vecMul_add θ.E η.E v
      map_smul' := fun c θ => Matrix.vecMul_smul v c θ.E }
  let g := LinearMap.toContinuousLinearMap l
  -- it is onto: put `y / v j` in the row `j` of `E`, where `v j ≠ 0`
  have hg : Function.Surjective g := by
    intro y
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hv
    refine ⟨⟨Matrix.of fun a b => if a = j then y b / v j else 0, 0, 0, 0⟩, ?_⟩
    ext b
    simp only [g, l, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk,
      Matrix.vecMul, dotProduct, Matrix.of_apply, mul_ite, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true]
    exact mul_div_cancel₀ _ hj
  have hset : U ∩ {θ | v ᵥ* θ.E ≠ 0} = U \ {θ | g θ = 0} := rfl
  rw [hset]
  refine ⟨hU.sdiff (isClosed_eq g.continuous continuous_const), ?_⟩
  exact isPreconnected_diff_zeroSet_of_surjective
    (by rw [Module.finrank_fintype_fun_eq_card]; exact hd) hU hUc g
    fun θ _ _ => ⟨g, g.hasStrictFDerivAt, hg⟩

/-- Helper, one removal at block `ℓ`, at the input `x` and the token `t`: on an open preconnected
set `U` of parameters at which no row of `h_0, …, h_ℓ` vanishes at `x`, removing the parameters
with `(h_{ℓ+1})_t = 0` keeps `U` open and preconnected. Row `t` of `N(h_ℓ) W_read` (`G`) vanishes
on a closed set of codimension `#hid ℓ ≥ 2`; off it, row `t` of `h_{ℓ+1}` (`H`) vanishes on a
closed set of codimension `d ≥ 2`; and `G = 0` implies `H = 0` (`σ 0 = 0`). -/
private theorem removal_succ_dzc (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (hσ0 : ∀ z : ℝ, σ z = 0 ↔ z = 0) (hd : 2 ≤ Fintype.card d) (ℓ : Fin L)
    (hh : 2 ≤ Fintype.card (hid ℓ)) (x : Matrix T dIn ℝ) (t : T)
    (U : Set (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut))
    (hU : IsOpen U) (hUc : IsPreconnected U)
    (hUO : ∀ θ ∈ U, ∀ i : Fin (L + 1), i ≤ ℓ.castSucc →
      ∀ t, hidden (Arch.mlp σ (rmsNorm 0) hid) 0 θ x i t ≠ 0) :
    IsOpen (U ∩ {θ | hidden (Arch.mlp σ (rmsNorm 0) hid) 0 θ x ℓ.succ t ≠ 0}) ∧
      IsPreconnected (U ∩ {θ | hidden (Arch.mlp σ (rmsNorm 0) hid) 0 θ x ℓ.succ t ≠ 0}) := by
  -- `G`: row `t` of what block `ℓ` reads; `H`: row `t` of the next hidden state
  let G : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut → hid ℓ → ℝ :=
    fun θ' => (rmsNorm 0 (hidden (Arch.mlp σ (rmsNorm 0) hid) 0 θ' x ℓ.castSucc) * θ'.read ℓ :
      Matrix T (hid ℓ) ℝ) t
  let H : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut → d → ℝ :=
    fun θ' => hidden (Arch.mlp σ (rmsNorm 0) hid) 0 θ' x ℓ.succ t
  -- both are analytic at the points of `U`
  have hGa : ∀ θ ∈ U, AnalyticAt ℝ G θ := fun θ hθ =>
    analyticAt_pi_iff.mp (analyticAt_preactivation_rmsNorm_zero hσa θ x ℓ (hUO θ hθ)) t
  have hHa : ∀ θ ∈ U, AnalyticAt ℝ H θ := fun θ hθ =>
    analyticAt_pi_iff.mp (analyticAt_hidden_rmsNorm_zero hσa θ x ℓ.succ
      fun i hi => hUO θ hθ i (Fin.le_castSucc_iff.mpr hi)) t
  -- `G θ = 0` implies `H θ = 0`: `H = σ(G) W_write` and `σ 0 = 0`
  have hGH : ∀ θ, G θ = 0 → H θ = 0 := by
    intro θ hG
    have hrow : ∀ j, (rmsNorm 0 (hidden (Arch.mlp σ (rmsNorm 0) hid) 0 θ x ℓ.castSucc) *
        θ.read ℓ : Matrix T (hid ℓ) ℝ) t j = 0 := fun j => congrFun hG j
    ext b
    simp only [H, hidden_succ, Pi.zero_apply, Matrix.mul_zero, zero_add, Matrix.mul_apply,
      Matrix.map_apply, hrow, (hσ0 0).2 rfl, zero_mul, Finset.sum_const_zero]
  -- the two removals
  have hGc : ContinuousOn G U := fun θ hθ => (hGa θ hθ).continuousAt.continuousWithinAt
  have hU1 : IsOpen (U \ {θ | G θ = 0}) := hGc.isOpen_inter_preimage hU isOpen_compl_singleton
  have hc1 : IsPreconnected (U \ {θ | G θ = 0}) :=
    isPreconnected_diff_zeroSet_of_surjective
      (by rw [Module.finrank_fintype_fun_eq_card]; exact hh) hU hUc G
      fun θ hθ _ => ⟨_, (hGa θ hθ).hasStrictFDerivAt,
        surjective_fderiv_preactivation hσa θ x ℓ t (hUO θ hθ)⟩
  have hHc : ContinuousOn H (U \ {θ | G θ = 0}) := fun θ hθ =>
    (hHa θ hθ.1).continuousAt.continuousWithinAt
  have hU2 : IsOpen ((U \ {θ | G θ = 0}) \ {θ | H θ = 0}) :=
    hHc.isOpen_inter_preimage hU1 isOpen_compl_singleton
  have hc2 : IsPreconnected ((U \ {θ | G θ = 0}) \ {θ | H θ = 0}) :=
    isPreconnected_diff_zeroSet_of_surjective
      (by rw [Module.finrank_fintype_fun_eq_card]; exact hd) hU1 hc1 H
      fun θ hθ _ => ⟨_, (hHa θ hθ.1).hasStrictFDerivAt,
        surjective_fderiv_hidden_succ hσa (fun z => (hσ0 z).1) θ x ℓ t (hUO θ hθ.1) hθ.2⟩
  -- the set of the statement is the twice removed set
  have hset : U ∩ {θ | H θ ≠ 0} = (U \ {θ | G θ = 0}) \ {θ | H θ = 0} := by
    ext θ
    exact ⟨fun h => ⟨⟨h.1, fun hG => h.2 (hGH θ hG)⟩, h.2⟩, fun h => ⟨h.1.1, h.2⟩⟩
  show IsOpen (U ∩ {θ | H θ ≠ 0}) ∧ IsPreconnected (U ∩ {θ | H θ ≠ 0})
  rw [hset]
  exact ⟨hU2, hc2⟩

/-- **Lemma D.20, "`O_X` is connected", the sets `O^k`:** let `σ` be real-analytic and vanish
exactly at `0`, `d ≥ 2`, every block with at least two hidden units, and no row of an input of the
batch zero. Then every `O^k` is preconnected. -/
theorem isPreconnected_hiddenNonzero (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (hσ0 : ∀ z : ℝ, σ z = 0 ↔ z = 0) (hd : 2 ≤ Fintype.card d)
    (hhid : ∀ ℓ, 2 ≤ Fintype.card (hid ℓ)) {n : ℕ} (X : Fin n → Matrix T dIn ℝ)
    (hX : ∀ i t, X i t ≠ 0) (k : Fin (L + 1)) :
    IsPreconnected (hiddenNonzero σ hid X k :
      Set (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)) := by
  induction k using Fin.induction with
  | zero =>
    -- `O^0`: remove the zero sets of the rows `(X i)_t E`, one pair `(i, t)` at a time
    have h := finset_induction_dzc isOpen_univ isPreconnected_univ
      (fun p : Fin n × T => {θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut |
        X p.1 p.2 ᵥ* θ.E ≠ 0})
      (fun p V _ hV hVc => removal_zero_dzc hd (X p.1 p.2) (hX p.1 p.2) V hV hVc) Finset.univ
    have hO : (hiddenNonzero σ hid X 0 :
        Set (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)) =
        Set.univ ∩ ⋂ p ∈ (Finset.univ : Finset (Fin n × T)), {θ | X p.1 p.2 ᵥ* θ.E ≠ 0} := by
      ext θ
      simp only [hiddenNonzero, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_univ, true_and,
        Set.mem_iInter, Finset.mem_univ, forall_const, Prod.forall]
      constructor
      · intro hθ i t
        have h0 := hθ i 0 le_rfl t
        rwa [hidden_zero, Matrix.mul_apply_eq_vecMul] at h0
      · intro hθ i j hj t
        rw [Fin.le_zero_iff.mp hj, hidden_zero, Matrix.mul_apply_eq_vecMul]
        exact hθ i t
    rw [hO]
    exact h.2
  | succ ℓ ih =>
    -- `O^{ℓ+1}`: remove from `O^ℓ` the zero sets of the rows `(h_{ℓ+1})_t` at `X i`, one pair
    -- `(i, t)` at a time
    have h := finset_induction_dzc (isOpen_hiddenNonzero hσa X ℓ.castSucc) ih
      (fun p : Fin n × T => {θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut |
        hidden (Arch.mlp σ (rmsNorm 0) hid) 0 θ (X p.1) ℓ.succ p.2 ≠ 0})
      (fun p V hVU hV hVc => removal_succ_dzc hσa hσ0 hd ℓ (hhid ℓ) (X p.1) p.2 V hV hVc
        fun θ hθ => hVU hθ p.1) Finset.univ
    have hO : (hiddenNonzero σ hid X ℓ.succ :
        Set (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)) =
        hiddenNonzero σ hid X ℓ.castSucc ∩ ⋂ p ∈ (Finset.univ : Finset (Fin n × T)),
          {θ | hidden (Arch.mlp σ (rmsNorm 0) hid) 0 θ (X p.1) ℓ.succ p.2 ≠ 0} := by
      ext θ
      simp only [hiddenNonzero, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter,
        Finset.mem_univ, forall_const, Prod.forall]
      constructor
      · intro hθ
        exact ⟨fun i j hj t => hθ i j (hj.trans (Fin.castSucc_lt_succ (i := ℓ)).le) t,
          fun i t => hθ i ℓ.succ le_rfl t⟩
      · rintro ⟨hθ, hθ'⟩ i j hj t
        rcases hj.lt_or_eq with hj | rfl
        · exact hθ i j (Fin.le_castSucc_iff.mpr hj) t
        · exact hθ' i t
    rw [hO]
    exact h.2

/-- **Lemma D.20 of the dimension paper, "`O_X` is open and connected":** under the same
hypotheses `O_X = O^L` is connected (preconnected, and not empty: its complement has measure
zero). -/
theorem isConnected_hiddenNonzero (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (hσ0 : ∀ z : ℝ, σ z = 0 ↔ z = 0) (hd : 2 ≤ Fintype.card d)
    (hhid : ∀ ℓ, 2 ≤ Fintype.card (hid ℓ)) {n : ℕ} (X : Fin n → Matrix T dIn ℝ)
    (hX : ∀ i t, X i t ≠ 0) :
    IsConnected (hiddenNonzero σ hid X (Fin.last L) :
      Set (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)) := by
  refine ⟨?_, isPreconnected_hiddenNonzero hσa hσ0 hd hhid X hX _⟩
  -- not empty: its complement is null for an additive Haar measure, the whole space is not
  by_contra hne
  rw [Set.not_nonempty_iff_eq_empty] at hne
  have h0 := measure_compl_hiddenNonzero hσa hσ0 hd hhid X hX
    (Measure.addHaar : Measure (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut))
    (Fin.last L)
  rw [hne, Set.compl_empty] at h0
  exact (isOpen_univ.measure_pos _ Set.univ_nonempty).ne' h0

end Skips
