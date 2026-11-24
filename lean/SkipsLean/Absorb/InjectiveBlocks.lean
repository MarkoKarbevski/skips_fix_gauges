import SkipsLean.Absorb.FirstBlock
import SkipsLean.Residual.Folding

/-!
# Injective residual blocks: every block of an equal skipless network has `2 d` units

Paper (absorb paper): Proposition 4.6 (Injective blocks: `2 d_model` units in every block): "Let
`σ` be ReLU or GELU, without normalization, and let `E` and `D` have rank `d_model`. Suppose that
every block of the residual network is injective on tokens when `σ` is replaced by ReLU:
`x + B_ℓ(x) ≠ x' + B_ℓ(x')` for all tokens `x ≠ x'`. Then every skipless network of `σ` blocks,
of any depth and with the same `d_model`, that equals the residual network has at least
`2 d_model` hidden units in every block." After it: "The condition holds when every block has
`‖W_read‖ ‖W_write‖ < 1`, in spectral norm".

Its proof (Appendix A.1). "GELU reduces to ReLU: if a residual GELU network equals a skipless one,
the two ReLU networks with the same weights are equal". Step 1: the residual network is injective
in `x E`. Step 2: every skipless block is injective; it uses "A continuous, positively
homogeneous, injective map `ψ` of `ℝ^{1×d_model}` to itself is onto: […] by invariance of domain
it is open". Step 3: an injective block has `2 d_model` units: "Fix `u` off the hyperplanes […]
Injectivity makes this matrix invertible, so `|S| ≥ d_model` at `u` and at `−u`. The active sets
at `u` and `−u` are disjoint".

Stated here with the block maps on one row: `blockMapRes θ ℓ` (`Residual/Folding.lean`,
`h ↦ h + σ(h W_read^ℓ) W_write^ℓ`) for the residual network, and `vanillaBlock`
(`Absorb/Block.lean`) for one skipless block. Invariance of domain is the hypothesis from the
literature `InvarianceOfDomain d` (`Literature/InvarianceOfDomain.lean`). The skipless network
has any number `L'` of blocks and any widths `hid'`, the same `d`, `d_in`, `d_out` and tokens.

* Step 2, the topological fact: under invariance of domain, a continuous, positively homogeneous,
  injective map of `ℝ^d` to itself is onto.
* Step 3: an injective ReLU block of `ℝ^d` to itself has at least `2 d` hidden units.
* The proposition for ReLU and for GELU, and with the condition `‖W_read‖ ‖W_write‖ < 1` (the
  spectral norms as Lipschitz constants in the Euclidean norm, as in
  `not_folds_of_norm_mul_norm_lt_one`).
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise

variable {T dIn dOut : Type*} {d : Type} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d]
  [Fintype dIn] [Fintype dOut]
variable {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]

/-- **Proof of Proposition 4.6, Step 2, the topological fact, under invariance of domain:** a
continuous, positively homogeneous, injective map of `ℝ^d` to itself is onto. -/
theorem surjective_of_injective_of_posHomogeneous (hinv : InvarianceOfDomain d)
    (ψ : (d → ℝ) → (d → ℝ)) (hc : Continuous ψ)
    (hh : ∀ (c : ℝ) (u : d → ℝ), 0 < c → ψ (c • u) = c • ψ u) (hi : Function.Injective ψ) :
    Function.Surjective ψ := by
  -- `ψ 0 = 2 ψ 0`, so `ψ 0 = 0`
  have h0 : ψ 0 = 0 := by
    have h2 := hh 2 0 two_pos
    rw [smul_zero, two_smul] at h2
    simpa using h2
  -- by invariance of domain the range of `ψ` is open; it contains `ψ 0 = 0`, so a ball around `0`
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (hinv ψ hc hi).isOpen_range 0 ⟨0, h0⟩
  -- the range is a cone, so it is everything: `c y` is in the ball for a small `c > 0`
  intro y
  have hy : 0 < ‖y‖ + 1 := by positivity
  obtain ⟨c, hc_def⟩ : ∃ c : ℝ, c = ε / (‖y‖ + 1) := ⟨_, rfl⟩
  have hcpos : 0 < c := hc_def ▸ div_pos hε hy
  have hmem : c • y ∈ Metric.ball (0 : d → ℝ) ε := by
    rw [mem_ball_zero_iff, norm_smul, Real.norm_of_nonneg hcpos.le, hc_def,
      div_mul_eq_mul_div, div_lt_iff₀ hy]
    nlinarith [norm_nonneg y]
  obtain ⟨x, hx⟩ := hball hmem
  refine ⟨c⁻¹ • x, ?_⟩
  rw [hh _ _ (inv_pos.2 hcpos), hx, inv_smul_smul₀ hcpos.ne']

/-- A ReLU block on a row `h` is `h W_read[:,S] W_write[S,:]` for the set `S` of its active
units (a copy of the private `vanillaBlock_relu_eq` of `Absorb/FirstBlock.lean`). -/
private theorem vanillaBlock_relu_eq_inj {p q m : Type*} [Fintype p] [Fintype m]
    [DecidableEq m] (Wr : Matrix p m ℝ) (Ww : Matrix m q ℝ) (h : p → ℝ) (S : Finset m)
    (hS : ∀ i, i ∈ S ↔ 0 < (h ᵥ* Wr) i) :
    vanillaBlock relu Wr Ww h = h ᵥ* subProd S Wr Ww := by
  have hd : (h ᵥ* Wr) ᵥ* Matrix.diagonal (fun j => if j ∈ S then (1 : ℝ) else 0)
      = fun i => relu ((h ᵥ* Wr) i) := by
    funext i
    rw [Matrix.vecMul_diagonal]
    by_cases hi : 0 < (h ᵥ* Wr) i
    · rw [ite_eq_left ((hS i).2 hi), mul_one, relu, max_eq_left hi.le]
    · rw [ite_eq_right (fun h' => hi ((hS i).1 h')), mul_zero, relu,
        max_eq_right (not_lt.1 hi)]
  rw [subProd, ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul, hd]
  rfl

open Filter Topology in
/-- If an injective map agrees with `v ↦ v N` near some row `u`, then `v ↦ v N` is injective:
`w₁ N = w₂ N` gives the same image of `u + s w₁` and `u + s w₂` for small `s ≠ 0`. -/
private theorem vecMul_injective_of_eventually_inj {n : Type*} [Fintype n]
    {f : (n → ℝ) → (n → ℝ)} (hf : Function.Injective f) {N : Matrix n n ℝ} {u : n → ℝ}
    (hev : ∀ᶠ v in 𝓝 u, f v = v ᵥ* N) : Function.Injective fun v : n → ℝ => v ᵥ* N := by
  intro w₁ w₂ hw
  have hw' : w₁ ᵥ* N = w₂ ᵥ* N := hw
  have hc : ∀ w : n → ℝ, Tendsto (fun s : ℝ => u + s • w) (𝓝 0) (𝓝 u) := by
    intro w
    have h1 : Continuous fun s : ℝ => u + s • w :=
      continuous_const.add (continuous_id.smul continuous_const)
    simpa only [zero_smul, add_zero] using h1.tendsto 0
  have h3 : ∀ᶠ s in 𝓝[≠] (0 : ℝ), (f (u + s • w₁) = (u + s • w₁) ᵥ* N
      ∧ f (u + s • w₂) = (u + s • w₂) ᵥ* N) ∧ s ≠ 0 :=
    ((((hc w₁).eventually hev).and ((hc w₂).eventually hev)).filter_mono
      nhdsWithin_le_nhds).and self_mem_nhdsWithin
  obtain ⟨s, ⟨h1, h2⟩, hs⟩ := h3.exists
  have h4 : u + s • w₁ = u + s • w₂ := hf (by
    rw [h1, h2, Matrix.add_vecMul, Matrix.add_vecMul, Matrix.smul_vecMul, Matrix.smul_vecMul, hw'])
  exact smul_right_injective (n → ℝ) hs (add_left_cancel h4)

/-- If `v ↦ v W_read[:,S] W_write[S,:]` is injective on `ℝ^n`, then `S` has at least `n` units:
`v ↦ (v W_read)|_S` is linear and injective into `ℝ^S`. -/
private theorem card_le_of_vecMul_subProd_injective_inj {n m : Type*} [Fintype n] [Fintype m]
    [DecidableEq m] (Wr : Matrix n m ℝ) (Ww : Matrix m n ℝ) (S : Finset m)
    (hi : Function.Injective fun v : n → ℝ => v ᵥ* subProd S Wr Ww) :
    Fintype.card n ≤ S.card := by
  let g : (n → ℝ) →ₗ[ℝ] (S → ℝ) :=
    { toFun := fun v i => (v ᵥ* Wr) i
      map_add' := fun v w => by funext i; simp [Matrix.add_vecMul]
      map_smul' := fun c v => by funext i; simp [Matrix.smul_vecMul] }
  have hg : Function.Injective g := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    apply hi
    -- `(v W_read) Π_S = 0`: its entries in `S` vanish, the others are multiplied by `0`
    have h0 : (v ᵥ* Wr) ᵥ* Matrix.diagonal (fun j => if j ∈ S then (1 : ℝ) else 0) = 0 := by
      funext i
      rw [Matrix.vecMul_diagonal]
      by_cases h : i ∈ S
      · have h1 := congrFun hv ⟨i, h⟩
        simp only [g, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at h1
        simp [h1]
      · simp [h]
    show v ᵥ* subProd S Wr Ww = 0 ᵥ* subProd S Wr Ww
    rw [Matrix.zero_vecMul, subProd, ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul, h0,
      Matrix.zero_vecMul]
  have h := LinearMap.finrank_le_finrank_of_injective hg
  simpa [Module.finrank_fintype_fun_eq_card] using h

omit [DecidableEq d] in
open Filter Topology in
/-- **Step 3 at one row** `u`: if every unit with a nonzero read reads a nonzero number at `u`, an
injective ReLU block has at least `d` units active at `u`. -/
private theorem card_le_card_active_inj {m : Type*} [Fintype m] [DecidableEq m]
    (Wr : Matrix d m ℝ) (Ww : Matrix m d ℝ)
    (hi : Function.Injective (vanillaBlock relu Wr Ww)) (u : d → ℝ)
    (hu : ∀ i, (u ᵥ* Wr) i = 0 → Wrᵀ i = 0) :
    Fintype.card d ≤ (Finset.univ.filter fun i => 0 < (u ᵥ* Wr) i).card := by
  obtain ⟨S, hS_def⟩ : ∃ S : Finset m, S = Finset.univ.filter fun i => 0 < (u ᵥ* Wr) i :=
    ⟨_, rfl⟩
  rw [← hS_def]
  have hS : ∀ i, i ∈ S ↔ 0 < (u ᵥ* Wr) i := fun i => by simp [hS_def]
  -- near `u` the active set is `S`
  have hev : ∀ᶠ v in 𝓝 u, ∀ i, (i ∈ S ↔ 0 < (v ᵥ* Wr) i) := by
    refine Filter.eventually_all.2 fun i => ?_
    have ht : Tendsto (fun v : d → ℝ => (v ᵥ* Wr) i) (𝓝 u) (𝓝 ((u ᵥ* Wr) i)) :=
      ((continuous_apply i).comp (continuous_id.matrix_vecMul continuous_const)).tendsto u
    rcases lt_trichotomy ((u ᵥ* Wr) i) 0 with hneg | hzero | hpos
    · filter_upwards [ht.eventually (eventually_lt_nhds hneg)] with v hv
      rw [hS]
      exact ⟨fun h => absurd (h.trans hneg) (lt_irrefl _),
        fun h => absurd (h.trans hv) (lt_irrefl _)⟩
    · refine Filter.Eventually.of_forall fun v => ?_
      have h0 : (v ᵥ* Wr) i = 0 := by
        have e : (v ᵥ* Wr) i = v ⬝ᵥ Wrᵀ i := rfl
        rw [e, hu i hzero, dotProduct_zero]
      rw [hS, hzero, h0]
    · filter_upwards [ht.eventually (eventually_gt_nhds hpos)] with v hv
      rw [hS]
      exact ⟨fun _ => hv, fun _ => hpos⟩
  -- so near `u` the block is `v ↦ v W_read[:,S] W_write[S,:]`, which is then injective
  have hev' : ∀ᶠ v in 𝓝 u, vanillaBlock relu Wr Ww v = v ᵥ* subProd S Wr Ww := by
    filter_upwards [hev] with v hv
    exact vanillaBlock_relu_eq_inj Wr Ww v S hv
  exact card_le_of_vecMul_subProd_injective_inj Wr Ww S
    (vecMul_injective_of_eventually_inj hi hev')

/-- **Proof of Proposition 4.6, Step 3:** a ReLU block `h ↦ ReLU(h W_read) W_write` of `ℝ^d` to
itself that is injective has at least `2 d` hidden units. -/
theorem two_mul_card_le_of_injective_vanillaBlock_relu {m : Type*} [Fintype m]
    (Wr : Matrix d m ℝ) (Ww : Matrix m d ℝ)
    (hi : Function.Injective (vanillaBlock relu Wr Ww)) :
    2 * Fintype.card d ≤ Fintype.card m := by
  classical
  -- a row `u` off the hyperplanes `u r_i = 0` of the units with a nonzero read `r_i`
  obtain ⟨u, -, hu⟩ := exists_dotProduct_eq_zero_and_ne_zero (n := d)
    (ι := {i : m // Wrᵀ i ≠ 0}) 0 (fun k => Wrᵀ k.1) (fun k r => by rw [smul_zero]; exact k.2)
  have hu' : ∀ i, (u ᵥ* Wr) i = 0 → Wrᵀ i = 0 := fun i h0 => by
    by_contra hne
    exact hu ⟨i, hne⟩ h0
  have hnu : ∀ i, ((-u) ᵥ* Wr) i = 0 → Wrᵀ i = 0 := fun i h0 => by
    apply hu' i
    rw [Matrix.neg_vecMul, Pi.neg_apply, neg_eq_zero] at h0
    exact h0
  -- at least `d` units are active at `u`, and at least `d` at `-u`
  have h1 := card_le_card_active_inj Wr Ww hi u hu'
  have h2 := card_le_card_active_inj Wr Ww hi (-u) hnu
  -- the two active sets are disjoint
  have hdisj : Disjoint (Finset.univ.filter fun i => 0 < (u ᵥ* Wr) i)
      (Finset.univ.filter fun i => 0 < ((-u) ᵥ* Wr) i) := by
    rw [Finset.disjoint_filter]
    intro i _ h h'
    rw [Matrix.neg_vecMul, Pi.neg_apply] at h'
    linarith
  have h3 := Finset.card_le_univ ((Finset.univ.filter fun i => 0 < (u ᵥ* Wr) i) ∪
    (Finset.univ.filter fun i => 0 < ((-u) ᵥ* Wr) i))
  rw [Finset.card_union_of_disjoint hdisj] at h3
  omega

/-- The output row of a network as a function of its hidden row after block `k`, for the blocks
`B k` on rows and the readout `D`: `H_n v = v D` and `H_k = H_{k+1} ∘ B_k`. -/
private noncomputable def suffixMap_inj {n : ℕ} (B : Fin n → (d → ℝ) → (d → ℝ))
    (D : Matrix d dOut ℝ) : Fin (n + 1) → (d → ℝ) → (dOut → ℝ) :=
  Fin.reverseInduction (motive := fun _ => (d → ℝ) → (dOut → ℝ)) (fun v => v ᵥ* D)
    (fun k H => H ∘ B k)

omit [DecidableEq d] [Fintype dOut] in
private theorem suffixMap_last_inj {n : ℕ} (B : Fin n → (d → ℝ) → (d → ℝ))
    (D : Matrix d dOut ℝ) : suffixMap_inj B D (Fin.last n) = fun v => v ᵥ* D := by
  simp only [suffixMap_inj, Fin.reverseInduction_last]

omit [DecidableEq d] [Fintype dOut] in
private theorem suffixMap_castSucc_inj {n : ℕ} (B : Fin n → (d → ℝ) → (d → ℝ))
    (D : Matrix d dOut ℝ) (k : Fin n) :
    suffixMap_inj B D k.castSucc = suffixMap_inj B D k.succ ∘ B k := by
  simp only [suffixMap_inj, Fin.reverseInduction_castSucc]

omit [DecidableEq d] [Fintype dOut] in
/-- Along the hidden rows `r k` of a network (`r (k+1) = B_k (r k)`), `H_k (r k)` is the output
row `r n D`. -/
private theorem suffixMap_rows_inj {n : ℕ} (B : Fin n → (d → ℝ) → (d → ℝ))
    (D : Matrix d dOut ℝ) (r : Fin (n + 1) → d → ℝ)
    (hr : ∀ k : Fin n, r k.succ = B k (r k.castSucc)) (k : Fin (n + 1)) :
    suffixMap_inj B D k (r k) = r (Fin.last n) ᵥ* D := by
  induction k using Fin.reverseInduction with
  | last => rw [suffixMap_last_inj]
  | cast k ih => rw [suffixMap_castSucc_inj, Function.comp_apply, ← hr, ih]

omit [Fintype T] [Fintype dOut] in
/-- A row of the output of the residual network is `G_0` of the row `x_t E`, with the block maps
`Φ_ℓ` of `Residual/Folding.lean`. -/
private theorem eval_res_row_inj (θ : Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut)
    (X : Matrix T dIn ℝ) (t : T) :
    eval (Arch.mlp relu id hid) 1 θ X t
      = suffixMap_inj (blockMapRes θ) θ.D 0 (X t ᵥ* θ.E) := by
  have h : suffixMap_inj (blockMapRes θ) θ.D 0 (hidden (Arch.mlp relu id hid) 1 θ X 0 t)
      = hidden (Arch.mlp relu id hid) 1 θ X (Fin.last L) t ᵥ* θ.D :=
    suffixMap_rows_inj (blockMapRes θ) θ.D (fun k => hidden (Arch.mlp relu id hid) 1 θ X k t)
      (fun k => hidden_succ_eq_blockMapRes θ X k t) 0
  rw [hidden_zero, Matrix.mul_apply_eq_vecMul] at h
  rw [h]
  show (hidden (Arch.mlp relu id hid) 1 θ X (Fin.last L) * θ.D) t = _
  rw [Matrix.mul_apply_eq_vecMul]

omit [Fintype T] [DecidableEq d] [Fintype dOut] in
/-- A row of the hidden state after block `k` of a skipless network (stream matrix `0`) is the
block of the row before it. -/
private theorem hidden_succ_skipless_inj
    (θ : Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut) (X : Matrix T dIn ℝ)
    (k : Fin L) (t : T) :
    hidden (Arch.mlp relu id hid) 0 θ X k.succ t
      = vanillaBlock relu (θ.read k) (θ.write k)
          (hidden (Arch.mlp relu id hid) 0 θ X k.castSucc t) := by
  rw [hidden_succ]
  show (hidden (Arch.mlp relu id hid) 0 θ X k.castSucc * (0 : Matrix d d ℝ)
    + (hidden (Arch.mlp relu id hid) 0 θ X k.castSucc * θ.read k).map relu * θ.write k) t = _
  rw [Matrix.mul_zero, zero_add]
  exact map_mul_mul_row relu (θ.read k) (θ.write k) _ t

omit [Fintype T] [DecidableEq d] [Fintype dOut] in
/-- A row of the output of the skipless network is `H_0` of the row `x_t E'`. -/
private theorem eval_skipless_row_inj
    (θ : Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut) (X : Matrix T dIn ℝ) (t : T) :
    eval (Arch.mlp relu id hid) 0 θ X t
      = suffixMap_inj (fun k => vanillaBlock relu (θ.read k) (θ.write k)) θ.D 0
          (X t ᵥ* θ.E) := by
  have h : suffixMap_inj (fun k => vanillaBlock relu (θ.read k) (θ.write k)) θ.D 0
      (hidden (Arch.mlp relu id hid) 0 θ X 0 t)
      = hidden (Arch.mlp relu id hid) 0 θ X (Fin.last L) t ᵥ* θ.D :=
    suffixMap_rows_inj _ θ.D (fun k => hidden (Arch.mlp relu id hid) 0 θ X k t)
      (fun k => hidden_succ_skipless_inj θ X k t) 0
  rw [hidden_zero, Matrix.mul_apply_eq_vecMul] at h
  rw [h]
  show (hidden (Arch.mlp relu id hid) 0 θ X (Fin.last L) * θ.D) t = _
  rw [Matrix.mul_apply_eq_vecMul]

/-- **Step 1:** if `D` has rank `d` and every block is injective, every `H_k` is injective. -/
private theorem suffixMap_injective_inj {n : ℕ} (B : Fin n → (d → ℝ) → (d → ℝ))
    (D : Matrix d dOut ℝ) (hD : D.rank = Fintype.card d) (hB : ∀ k, Function.Injective (B k))
    (k : Fin (n + 1)) : Function.Injective (suffixMap_inj B D k) := by
  induction k using Fin.reverseInduction with
  | last =>
    -- `D` has a right inverse
    obtain ⟨R, hR⟩ : ∃ R : Matrix dOut d ℝ, D * R = 1 :=
      Matrix.mulVec_surjective_iff_exists_right_inverse.1
        (Matrix.mulVec_surjective_iff_rank_eq_card.2 hD)
    rw [suffixMap_last_inj]
    intro v v' hv
    have h := congrArg (fun w => w ᵥ* R) hv
    simpa only [Matrix.vecMul_vecMul, hR, Matrix.vecMul_one] using h
  | cast k ih =>
    rw [suffixMap_castSucc_inj]
    exact ih.comp (hB k)

omit [DecidableEq d] in
/-- **Step 2, the embeddings:** if `E` has rank `d` and the kernel of `x ↦ x E'` lies in that of
`x ↦ x E`, then `x ↦ x E'` is onto `ℝ^d` and the two kernels are equal. -/
private theorem vecMul_surjective_of_ker_le_inj {E E' : Matrix dIn d ℝ}
    (hE : E.rank = Fintype.card d) (hker : ∀ x : dIn → ℝ, x ᵥ* E' = 0 → x ᵥ* E = 0) :
    Function.Surjective (fun x : dIn → ℝ => x ᵥ* E') ∧
      ∀ x : dIn → ℝ, x ᵥ* E = 0 → x ᵥ* E' = 0 := by
  have hle : LinearMap.ker E'.vecMulLinear ≤ LinearMap.ker E.vecMulLinear := fun x hx =>
    LinearMap.mem_ker.2 (hker x (LinearMap.mem_ker.1 hx))
  -- `x ↦ x E` is onto: its kernel has dimension `d_in - d`
  have hrange : LinearMap.range E.vecMulLinear = ⊤ :=
    LinearMap.range_eq_top.2 ((Matrix.vecMul_surjective_iff_rank_eq_card).2 hE)
  have h1 := LinearMap.finrank_range_add_finrank_ker E.vecMulLinear
  have h2 := LinearMap.finrank_range_add_finrank_ker E'.vecMulLinear
  rw [hrange, finrank_top] at h1
  have h3 := Submodule.finrank_le (LinearMap.range E'.vecMulLinear)
  have h4 := Submodule.finrank_mono hle
  -- so the kernel of `x ↦ x E'` has dimension `d_in - d` too, and its range is everything
  have hkeq : LinearMap.ker E'.vecMulLinear = LinearMap.ker E.vecMulLinear :=
    Submodule.eq_of_le_of_finrank_le hle (by omega)
  have hr' : LinearMap.range E'.vecMulLinear = ⊤ := Submodule.eq_top_of_finrank_eq (by omega)
  refine ⟨LinearMap.range_eq_top.1 hr', fun x hx => ?_⟩
  have h5 : x ∈ LinearMap.ker E.vecMulLinear := LinearMap.mem_ker.2 hx
  rw [← hkeq] at h5
  exact LinearMap.mem_ker.1 h5

omit [Fintype dOut] in
/-- **Step 2, the induction:** if `H_0` is injective and every block is continuous and
positively homogeneous, then every block is injective: `H_k = H_{k+1} ∘ B_k` injective makes `B_k`
injective, hence onto (invariance of domain), hence `H_{k+1}` injective. -/
private theorem injective_blocks_inj (hinv : InvarianceOfDomain d) {n : ℕ}
    (B : Fin n → (d → ℝ) → (d → ℝ)) (D : Matrix d dOut ℝ) (hc : ∀ k, Continuous (B k))
    (hh : ∀ k (c : ℝ) (u : d → ℝ), 0 < c → B k (c • u) = c • B k u)
    (h0 : Function.Injective (suffixMap_inj B D 0)) : ∀ k, Function.Injective (B k) := by
  have hall : ∀ k : Fin (n + 1), Function.Injective (suffixMap_inj B D k) := by
    intro k
    induction k using Fin.induction with
    | zero => exact h0
    | succ k ih =>
      rw [suffixMap_castSucc_inj] at ih
      have hs := surjective_of_injective_of_posHomogeneous hinv (B k) (hc k) (hh k) ih.of_comp
      exact ih.of_comp_right hs
  intro k
  have h := hall k.castSucc
  rw [suffixMap_castSucc_inj] at h
  exact h.of_comp

omit [DecidableEq d] in
/-- A ReLU block is continuous. -/
private theorem continuous_vanillaBlock_relu_inj {m : Type*} [Fintype m] (Wr : Matrix d m ℝ)
    (Ww : Matrix m d ℝ) : Continuous (vanillaBlock relu Wr Ww) := by
  have hr : Continuous relu := continuous_id.max continuous_const
  unfold vanillaBlock
  exact Continuous.matrix_vecMul (continuous_pi fun i => hr.comp ((continuous_apply i).comp
    (continuous_id.matrix_vecMul continuous_const))) continuous_const

omit [DecidableEq d] in
/-- A ReLU block is positively homogeneous. -/
private theorem vanillaBlock_relu_smul_inj {m : Type*} [Fintype m] (Wr : Matrix d m ℝ)
    (Ww : Matrix m d ℝ) {c : ℝ} (hc : 0 < c) (u : d → ℝ) :
    vanillaBlock relu Wr Ww (c • u) = c • vanillaBlock relu Wr Ww u := by
  have e : (fun i => relu (((c • u) ᵥ* Wr) i)) = c • fun i => relu ((u ᵥ* Wr) i) := by
    funext i
    simp only [Matrix.smul_vecMul, Pi.smul_apply, smul_eq_mul, relu]
    rw [mul_max_of_nonneg _ _ hc.le, mul_zero]
  simp only [vanillaBlock]
  rw [e, Matrix.smul_vecMul]

/-- **Proposition 4.6 for ReLU, under invariance of domain:** let `E` and `D` have rank `d` and
let every block of the residual ReLU network be injective on rows. Then every skipless ReLU
network with the same `d`, of any depth and any widths, that equals the residual network has at
least `2 d` hidden units in every block. -/
theorem two_mul_card_le_of_eval_eq_skipless_relu [Nonempty T] (hinv : InvarianceOfDomain d)
    (θ : Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d) (hD : θ.D.rank = Fintype.card d)
    (hinj : ∀ ℓ, Function.Injective (blockMapRes θ ℓ))
    {L' : ℕ} (hid' : Fin L' → Type) [∀ ℓ, Fintype (hid' ℓ)]
    (θ' : Params (Arch.mlp (T := T) (d := d) relu id hid') dIn dOut)
    (heq : ∀ X : Matrix T dIn ℝ,
      eval (Arch.mlp relu id hid') 0 θ' X = eval (Arch.mlp relu id hid) 1 θ X) :
    ∀ ℓ : Fin L', 2 * Fintype.card d ≤ Fintype.card (hid' ℓ) := by
  obtain ⟨t₀⟩ := ‹Nonempty T›
  -- the two networks on rows: `F'(x) = H_0(x E')` and `F(x) = G_0(x E)`
  have hrow : ∀ x : dIn → ℝ,
      suffixMap_inj (fun k => vanillaBlock relu (θ'.read k) (θ'.write k)) θ'.D 0 (x ᵥ* θ'.E)
        = suffixMap_inj (blockMapRes θ) θ.D 0 (x ᵥ* θ.E) := by
    intro x
    have h := congrFun (heq (Matrix.of fun _ => x)) t₀
    rw [eval_skipless_row_inj, eval_res_row_inj] at h
    exact h
  -- Step 1: the residual network is injective in `x E`
  have hG := suffixMap_injective_inj (blockMapRes θ) θ.D hD hinj 0
  -- Step 2: the kernel of `x ↦ x E'` lies in that of `x ↦ x E`; so `x ↦ x E'` is onto and the
  -- two kernels are equal
  have hker : ∀ x : dIn → ℝ, x ᵥ* θ'.E = 0 → x ᵥ* θ.E = 0 := by
    intro x hx
    have h1 : suffixMap_inj (blockMapRes θ) θ.D 0 (x ᵥ* θ.E)
        = suffixMap_inj (blockMapRes θ) θ.D 0 (0 ᵥ* θ.E) := by
      rw [← hrow x, ← hrow 0, hx, Matrix.zero_vecMul]
    have h2 := hG h1
    rwa [Matrix.zero_vecMul] at h2
  obtain ⟨hsurj, hker'⟩ := vecMul_surjective_of_ker_le_inj hE hker
  -- so the skipless network is injective in its first hidden row
  have hH : Function.Injective
      (suffixMap_inj (fun k => vanillaBlock relu (θ'.read k) (θ'.write k)) θ'.D 0) := by
    intro v v' hv
    obtain ⟨x, rfl⟩ := hsurj v
    obtain ⟨x', rfl⟩ := hsurj v'
    have h1 : x ᵥ* θ.E = x' ᵥ* θ.E := hG (by rw [← hrow, ← hrow]; exact hv)
    have h2 : (x - x') ᵥ* θ'.E = 0 := hker' _ (by rw [Matrix.sub_vecMul, h1, sub_self])
    rw [Matrix.sub_vecMul, sub_eq_zero] at h2
    exact h2
  -- and every skipless block is injective
  have hB := injective_blocks_inj hinv _ θ'.D
    (fun k => continuous_vanillaBlock_relu_inj (θ'.read k) (θ'.write k))
    (fun k c u hc => vanillaBlock_relu_smul_inj (θ'.read k) (θ'.write k) hc u) hH
  -- Step 3: an injective ReLU block has at least `2 d` units
  exact fun ℓ => two_mul_card_le_of_injective_vanillaBlock_relu _ _ (hB ℓ)

/-- **Proposition 4.6 for GELU, under invariance of domain:** let `E` and `D` have rank `d` and
let every block of the residual network be injective on rows when GELU is replaced by ReLU. Then
every skipless GELU network with the same `d`, of any depth and any widths, that equals the
residual GELU network has at least `2 d` hidden units in every block. -/
theorem two_mul_card_le_of_eval_eq_skipless_gelu [Nonempty T] (hinv : InvarianceOfDomain d)
    (θ : Params (Arch.mlp (T := T) (d := d) gelu id hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d) (hD : θ.D.rank = Fintype.card d)
    (hinj : ∀ ℓ, Function.Injective (blockMapRes (θ.withActivation relu) ℓ))
    {L' : ℕ} (hid' : Fin L' → Type) [∀ ℓ, Fintype (hid' ℓ)]
    (θ' : Params (Arch.mlp (T := T) (d := d) gelu id hid') dIn dOut)
    (heq : ∀ X : Matrix T dIn ℝ,
      eval (Arch.mlp gelu id hid') 0 θ' X = eval (Arch.mlp gelu id hid) 1 θ X) :
    ∀ ℓ : Fin L', 2 * Fintype.card d ≤ Fintype.card (hid' ℓ) := by
  -- GELU reduces to ReLU: the two ReLU networks with the same weights are equal, as both are the
  -- limit of `F(t X)/t` along the ray
  have heq' : ∀ X : Matrix T dIn ℝ,
      eval (Arch.mlp relu id hid') 0 (θ'.withActivation relu) X
        = eval (Arch.mlp relu id hid) 1 (θ.withActivation relu) X := by
    intro X
    refine tendsto_nhds_unique (tendsto_eval_gelu_ray 0 θ' X) ?_
    exact (tendsto_eval_gelu_ray 1 θ X).congr fun t =>
      (congrArg (fun M => t⁻¹ • M) (heq (t • X))).symm
  exact two_mul_card_le_of_eval_eq_skipless_relu hinv (θ.withActivation relu) hE hD hinj hid'
    (θ'.withActivation relu) heq'

/-- **Proposition 4.6 for ReLU with the condition `‖W_read‖ ‖W_write‖ < 1`, under invariance of
domain:** if `E` and `D` have rank `d` and every block of the residual ReLU network has Lipschitz
constants `a ℓ` of its read and `b ℓ` of its write, in the Euclidean norm, with
`a ℓ * b ℓ < 1`, every skipless ReLU network with the same `d` that equals it has at least `2 d`
hidden units in every block. -/
theorem two_mul_card_le_of_eval_eq_skipless_relu_of_norm_lt_one [Nonempty T]
    (hinv : InvarianceOfDomain d)
    (θ : Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d) (hD : θ.D.rank = Fintype.card d) (a b : Fin L → ℝ)
    (ha : ∀ ℓ (v : d → ℝ),
      Real.sqrt ((v ᵥ* θ.read ℓ) ⬝ᵥ (v ᵥ* θ.read ℓ)) ≤ a ℓ * Real.sqrt (v ⬝ᵥ v))
    (hb : ∀ ℓ (u : hid ℓ → ℝ),
      Real.sqrt ((u ᵥ* θ.write ℓ) ⬝ᵥ (u ᵥ* θ.write ℓ)) ≤ b ℓ * Real.sqrt (u ⬝ᵥ u))
    (hab : ∀ ℓ, a ℓ * b ℓ < 1)
    {L' : ℕ} (hid' : Fin L' → Type) [∀ ℓ, Fintype (hid' ℓ)]
    (θ' : Params (Arch.mlp (T := T) (d := d) relu id hid') dIn dOut)
    (heq : ∀ X : Matrix T dIn ℝ,
      eval (Arch.mlp relu id hid') 0 θ' X = eval (Arch.mlp relu id hid) 1 θ X) :
    ∀ ℓ : Fin L', 2 * Fintype.card d ≤ Fintype.card (hid' ℓ) := by
  -- no block folds (Proposition A.32 (iii))
  exact two_mul_card_le_of_eval_eq_skipless_relu hinv θ hE hD
    (fun ℓ => not_not.1 (not_folds_of_norm_mul_norm_lt_one θ ℓ (ha ℓ) (hb ℓ) (hab ℓ))) hid' θ' heq

/-- **Proposition 4.6 for GELU with the condition `‖W_read‖ ‖W_write‖ < 1`, under invariance of
domain.** -/
theorem two_mul_card_le_of_eval_eq_skipless_gelu_of_norm_lt_one [Nonempty T]
    (hinv : InvarianceOfDomain d)
    (θ : Params (Arch.mlp (T := T) (d := d) gelu id hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d) (hD : θ.D.rank = Fintype.card d) (a b : Fin L → ℝ)
    (ha : ∀ ℓ (v : d → ℝ),
      Real.sqrt ((v ᵥ* θ.read ℓ) ⬝ᵥ (v ᵥ* θ.read ℓ)) ≤ a ℓ * Real.sqrt (v ⬝ᵥ v))
    (hb : ∀ ℓ (u : hid ℓ → ℝ),
      Real.sqrt ((u ᵥ* θ.write ℓ) ⬝ᵥ (u ᵥ* θ.write ℓ)) ≤ b ℓ * Real.sqrt (u ⬝ᵥ u))
    (hab : ∀ ℓ, a ℓ * b ℓ < 1)
    {L' : ℕ} (hid' : Fin L' → Type) [∀ ℓ, Fintype (hid' ℓ)]
    (θ' : Params (Arch.mlp (T := T) (d := d) gelu id hid') dIn dOut)
    (heq : ∀ X : Matrix T dIn ℝ,
      eval (Arch.mlp gelu id hid') 0 θ' X = eval (Arch.mlp gelu id hid) 1 θ X) :
    ∀ ℓ : Fin L', 2 * Fintype.card d ≤ Fintype.card (hid' ℓ) := by
  -- no block of the ReLU network with the same weights folds (Proposition A.32 (iii))
  exact two_mul_card_le_of_eval_eq_skipless_gelu hinv θ hE hD
    (fun ℓ => not_not.1 (not_folds_of_norm_mul_norm_lt_one (θ.withActivation relu) ℓ (ha ℓ)
      (hb ℓ) (hab ℓ))) hid' θ' heq

end Skips
