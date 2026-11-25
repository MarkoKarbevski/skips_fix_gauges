import SkipsLean.Depth.Cones

/-!
# The parameters `θ†` of Lemma D.13, written out

Paper (dimension paper), Appendix D.5: "The parameters `θ†`. Let `𝟙` be the column of `d_model`
ones. Choose numbers `μ_1, μ_2, … > 0` such that `1, μ_1, μ_2, …` are linearly independent over
`ℚ`, for SwiGLU blocks, or such that `μ_1², μ_2², …` are, for GELU and GeGLU blocks. […] So the
gate column `c_j` is column `j` of `I` for `j ≤ d_model` and `c_j = −μ_{j−d_model} 𝟙` for
`j > d_model`, the write row `a_j` is row `j` of `I` for `j ≤ d_model` and `a_j = 𝟙^⊤` for
`j > d_model`, and in a gated block every value column is `e_j = 𝟙`. Let `ℝ^{1×d_model}_{>0}` be
the positive orthant, the set of the rows `n` with `n_i > 0` for every `i`."

"Lemma D.13 (`θ†` is good). `θ†` is good for the cones `C_0 = ⋯ = C_L = ℝ^{1×d_model}_{>0}`. For
every block, `A_ℓ = {1, …, d_model}`, and `g°_ℓ(n) = n` for a GELU block and `g°_ℓ(n) = (n𝟙) n`
for a gated block, where `n𝟙 = n_1 + ⋯ + n_{d_model}`."

`Depth/Cones.lean` has the lemma as an existence statement (there are cones, active sets and a
good parameter with the independence over `ℚ` of (K3)); its `θ†` is private there. Here `θ†` is a
definition and the lemma is stated with it:

* `posOrthant`: the positive orthant.
* `thetaDaggerGated`, `thetaDaggerMlp`: `θ†`. The index types are arbitrary finite types, so "the
  first `d_model` coordinates" of the inputs, of the outputs and of the hidden units of block `ℓ`
  are given by embeddings `ιE : d ↪ d_in`, `ιD : d ↪ d_out`, `c ℓ : d ↪ hid ℓ`; the number `μ ℓ j`
  is used for the units `j` outside the image of `c ℓ`.
* `exists_mu_thetaDaggerGated_cols` (SwiGLU), `exists_mu_thetaDaggerGated_outer` (GeGLU),
  `exists_mu_thetaDaggerMlp_outer` (GELU): there are numbers `μ > 0` for which `θ†` is good for
  the orthants with the active sets `A_ℓ` = the image of `c ℓ`, the frozen blocks are the paper's
  (`g°_ℓ(n) = (n𝟙) n`, respectively `n`), and the independence over `ℚ` of (K3) holds.
* The lemma for every admissible choice of `μ`, as the paper states it (last section):
  `goodForConesGated_thetaDaggerGated`, `frozenGated_thetaDaggerGated`,
  `goodForConesMlp_thetaDaggerMlp`, `frozenMlp_thetaDaggerMlp` for every `μ > 0`, and (K3) under
  the paper's condition on `μ`: `linearIndependent_gate_thetaDaggerGated` (SwiGLU: `1` and the
  `μ_j` independent over `ℚ`), `linearIndependent_outer_gate_thetaDaggerGated` (GeGLU) and
  `linearIndependent_outer_read_thetaDaggerMlp` (GELU): the `μ_j²` independent over `ℚ`, `d ≥ 2`.
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {σ : ℝ → ℝ} {χ : Matrix T d ℝ → Matrix T d ℝ} {hid : Fin L → Type}
  [∀ ℓ, Fintype (hid ℓ)]

omit [Fintype d] [DecidableEq d] in
/-- The positive orthant `ℝ^{1×d}_{>0}`: the rows with all entries positive. -/
def posOrthant (d : Type*) : Set (d → ℝ) := Set.univ.pi fun _ => Set.Ioi 0

omit [Fintype d] [DecidableEq d] in
/-- A row is in the positive orthant if and only if all its entries are positive. -/
theorem mem_posOrthant {n : d → ℝ} : n ∈ posOrthant d ↔ ∀ i, 0 < n i := by
  simp [posOrthant, Set.mem_pi]

open Classical in
omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- **The parameters `θ†` of Lemma D.13 for gated blocks.** `E` and `D` are the `0/1` matrices of
the embeddings `ιE`, `ιD` (`E = [I; 0]`, `D = [I | 0]`). In block `ℓ`, the gate column of the unit
`c ℓ i` is the unit column `e_i`, and that of a unit `j` outside the image of `c ℓ` is `−μ_j 𝟙`;
every value column is `𝟙`; the write row of the unit `c ℓ i` is the unit row `e_i`, and that of a
unit outside the image of `c ℓ` is `𝟙^⊤`. -/
noncomputable def thetaDaggerGated (ιE : d ↪ dIn) (ιD : d ↪ dOut) (c : ∀ ℓ, d ↪ hid ℓ)
    (μ : ∀ ℓ, hid ℓ → ℝ) : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut where
  E := Matrix.of fun a i => if a = ιE i then 1 else 0
  read ℓ := Matrix.of fun k (s : hid ℓ ⊕ hid ℓ) =>
    Sum.elim (fun j => if j ∈ Set.range (c ℓ) then (if j = c ℓ k then 1 else 0) else -μ ℓ j)
      (fun _ => 1) s
  write ℓ := Matrix.of fun j k =>
    if j ∈ Set.range (c ℓ) then (if j = c ℓ k then 1 else 0) else 1
  D := Matrix.of fun i b => if b = ιD i then 1 else 0

open Classical in
omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- **The parameters `θ†` of Lemma D.13 for MLP blocks** (GELU blocks): as `thetaDaggerGated`,
without value columns. -/
noncomputable def thetaDaggerMlp (ιE : d ↪ dIn) (ιD : d ↪ dOut) (c : ∀ ℓ, d ↪ hid ℓ)
    (μ : ∀ ℓ, hid ℓ → ℝ) : Params (Arch.mlp (T := T) (d := d) σ χ hid) dIn dOut where
  E := Matrix.of fun a i => if a = ιE i then 1 else 0
  read ℓ := Matrix.of fun k (j : hid ℓ) =>
    if j ∈ Set.range (c ℓ) then (if j = c ℓ k then 1 else 0) else -μ ℓ j
  write ℓ := Matrix.of fun j k =>
    if j ∈ Set.range (c ℓ) then (if j = c ℓ k then 1 else 0) else 1
  D := Matrix.of fun i b => if b = ιD i then 1 else 0

/-! ### Helpers: the private `θ†` of `Depth/Cones.lean` and its lemmas, copied -/

open Polynomial in
/-- Helper: `1` and distinct positive powers of a number `x` transcendental over `ℚ` are linearly
independent over `ℚ`: `a + ∑_j κ_j x^{k_j} = 0`, with distinct exponents `k_j ≥ 1`, forces `a = 0`
and every `κ_j = 0`. -/
private theorem eq_zero_of_transcendental_pow_tdg {ι : Type*} [Fintype ι] {x : ℝ}
    (hx : Transcendental ℚ x) {k : ι → ℕ} (hk : Function.Injective k) (hk0 : ∀ j, k j ≠ 0)
    (a : ℚ) (κ : ι → ℚ) (h : (a : ℝ) + ∑ j, (κ j : ℝ) * x ^ k j = 0) :
    a = 0 ∧ ∀ j, κ j = 0 := by
  classical
  -- the polynomial `p = a + ∑ κ_j X^{k_j}` has the root `x`, so it vanishes
  set p : ℚ[X] := C a + ∑ j, C (κ j) * X ^ k j with hp
  have hp0 : p = 0 := by
    refine (transcendental_iff.mp hx) p ?_
    simpa [hp, map_add, map_sum, aeval_C, aeval_X_pow] using h
  -- its coefficients are `a` (at `0`) and `κ_j` (at `k_j`)
  have hc : ∀ n, p.coeff n = (if n = 0 then a else 0) + ∑ j, if n = k j then κ j else 0 := by
    intro n
    simp only [hp, coeff_add, coeff_C, finsetSum_coeff, coeff_C_mul, coeff_X_pow, mul_ite,
      mul_one, mul_zero]
  refine ⟨?_, fun j => ?_⟩
  · have h0 := hc 0
    rw [hp0, coeff_zero] at h0
    have h0' : ∀ j, (0 = k j) ↔ False := fun j => ⟨fun h => hk0 j h.symm, False.elim⟩
    simpa [h0'] using h0.symm
  · have h1 := hc (k j)
    rw [hp0, coeff_zero] at h1
    simpa [hk0 j, hk.eq_iff] using h1.symm

/-- Helper: positive numbers `μ_j`, one for each `j` of a finite type, such that `1` and the `μ_j`
are linearly independent over `ℚ`, and so are `1` and the `μ_j²`: `μ_j = x^{e_j + 1}` with an
injection `e` into `ℕ` and `x = λ²`, where `λ = ∑_k 2^{-k!}` is Liouville's number,
transcendental. -/
private theorem exists_pos_indep_tdg (ι : Type*) [Fintype ι] :
    ∃ μ : ι → ℝ, (∀ j, 0 < μ j) ∧
      (∀ (a : ℚ) (κ : ι → ℚ), (a : ℝ) + ∑ j, (κ j : ℝ) * μ j = 0 → a = 0 ∧ ∀ j, κ j = 0) ∧
      (∀ (a : ℚ) (κ : ι → ℚ), (a : ℝ) + ∑ j, (κ j : ℝ) * μ j ^ 2 = 0 → a = 0 ∧ ∀ j, κ j = 0) := by
  -- Liouville's number is transcendental over `ℤ`, hence over `ℚ`, and so is its square `x > 0`
  have : Algebra.IsAlgebraic ℤ ℚ := IsLocalization.isAlgebraic ℚ (nonZeroDivisors ℤ)
  have hl : Transcendental ℚ (liouvilleNumber 2) :=
    (transcendental_liouvilleNumber le_rfl).extendScalars ℚ
  obtain ⟨x, hx, hx0⟩ : ∃ x : ℝ, Transcendental ℚ x ∧ 0 < x :=
    ⟨_, hl.pow two_pos, lt_of_le_of_ne (sq_nonneg _) (pow_ne_zero 2 hl.ne_zero).symm⟩
  -- an injection `e` of `ι` into `ℕ`
  obtain ⟨e, he⟩ : ∃ e : ι → ℕ, Function.Injective e :=
    ⟨fun j => (Fintype.equivFin ι j : ℕ), Fin.val_injective.comp (Fintype.equivFin ι).injective⟩
  refine ⟨fun j => x ^ (e j + 1), fun j => pow_pos hx0 _, fun a κ h => ?_, fun a κ h => ?_⟩
  · -- the exponents `e_j + 1`
    exact eq_zero_of_transcendental_pow_tdg hx (k := fun j => e j + 1)
      (fun i j hij => he (Nat.succ_injective hij)) (fun j => Nat.succ_ne_zero _) a κ h
  · -- the exponents `2 (e_j + 1)`, since `(x^{e_j+1})² = x^{2(e_j+1)}`
    refine eq_zero_of_transcendental_pow_tdg hx (k := fun j => 2 * (e j + 1))
      (fun i j hij => he (Nat.succ_injective (Nat.eq_of_mul_eq_mul_left two_pos hij)))
      (fun j => Nat.mul_ne_zero two_ne_zero (Nat.succ_ne_zero _)) a κ ?_
    simpa only [pow_mul'] using h

omit [DecidableEq d] in
/-- The positive orthant is an open convex cone without `0`. -/
private theorem isOpenConvexCone_orthant_tdg [Nonempty d] : IsOpenConvexCone (posOrthant d) where
  isOpen := isOpen_set_pi Set.finite_univ fun _ _ => isOpen_Ioi
  convex := convex_pi fun _ _ => convex_Ioi 0
  nonempty := ⟨1, mem_posOrthant.2 fun _ => one_pos⟩
  zero_notMem h := by
    obtain ⟨i⟩ := ‹Nonempty d›
    exact lt_irrefl _ (mem_posOrthant.1 h i)
  smul_mem n hn lam hlam := mem_posOrthant.2 fun i => mul_pos hlam (mem_posOrthant.1 hn i)

omit [DecidableEq d] in
/-- `∑_k n_k > 0` on the orthant. -/
private theorem sum_pos_of_mem_posOrthant_tdg [Nonempty d] {n : d → ℝ} (hn : n ∈ posOrthant d) :
    0 < ∑ k, n k :=
  Finset.sum_pos (fun i _ => mem_posOrthant.1 hn i) Finset.univ_nonempty

open Classical in
/-- The `0/1` matrix of an embedding `ι : d ↪ m`: the entry `(i, a)` is `1` if `a = ι i`. -/
private noncomputable def embMat_tdg {m : Type*} (ι : d ↪ m) : Matrix d m ℝ :=
  Matrix.of fun i a => if a = ι i then 1 else 0

/-- The `0/1` matrix of an embedding has rank `d`: its columns at the image are the identity. -/
private theorem rank_embMat_tdg {m : Type*} [Fintype m] (ι : d ↪ m) :
    (embMat_tdg ι).rank = Fintype.card d := by
  refine rank_eq_card_of_isUnit_det _ ι ?_
  have h : (embMat_tdg ι).submatrix id ι = 1 := by
    ext i i'
    simp [embMat_tdg, Matrix.one_apply, ι.injective.eq_iff, eq_comm]
  rw [h, det_one]
  exact isUnit_one

open Classical in
/-- The row `k ↦ [j = c k]`: the unit row `e_i` for the unit `j = c i`. -/
private noncomputable def unitRow_tdg {n : Type*} (c : d ↪ n) (j : n) : d → ℝ :=
  fun k => if j = c k then 1 else 0

omit [Fintype d] in
private theorem unitRow_emb_tdg {n : Type*} (c : d ↪ n) (i : d) :
    unitRow_tdg c (c i) = Pi.single i 1 := by
  funext k
  by_cases h : k = i
  · subst h
    simp [unitRow_tdg]
  · simp [unitRow_tdg, c.injective.eq_iff, h, Ne.symm h]

open Classical in
/-- The gate column of unit `j` in `θ†`: `e_i` for `j = c i`, and `-μ_j 𝟙` for the other units. -/
private noncomputable def gateCol_tdg {n : Type*} (c : d ↪ n) (μ : n → ℝ) (j : n) : d → ℝ :=
  if j ∈ Set.range c then unitRow_tdg c j else -μ j • 1

open Classical in
/-- The write row of unit `j` in `θ†`: `e_i` for `j = c i`, and `𝟙` for the other units. -/
private noncomputable def writeRow_tdg {n : Type*} (c : d ↪ n) (j : n) : d → ℝ :=
  if j ∈ Set.range c then unitRow_tdg c j else 1

private theorem gateCol_emb_tdg {n : Type*} (c : d ↪ n) (μ : n → ℝ) (i : d) :
    gateCol_tdg c μ (c i) = Pi.single i 1 := by
  simp [gateCol_tdg, unitRow_emb_tdg]

omit [DecidableEq d] in
private theorem gateCol_of_notMem_tdg {n : Type*} (c : d ↪ n) (μ : n → ℝ) {j : n}
    (hj : j ∉ Set.range c) : gateCol_tdg c μ j = -μ j • 1 := by
  simp [gateCol_tdg, hj]

private theorem writeRow_emb_tdg {n : Type*} (c : d ↪ n) (i : d) :
    writeRow_tdg c (c i) = Pi.single i 1 := by
  simp [writeRow_tdg, unitRow_emb_tdg]

omit [DecidableEq d] in
private theorem writeRow_of_notMem_tdg {n : Type*} (c : d ↪ n) {j : n} (hj : j ∉ Set.range c) :
    writeRow_tdg c j = 1 := by
  simp [writeRow_tdg, hj]

/-- The write rows of `θ†` have rank `d`: the rows at the image of `c` are the identity. -/
private theorem rank_writeRow_tdg {n : Type*} [Fintype n] (c : d ↪ n) :
    (Matrix.of (writeRow_tdg c)).rank = Fintype.card d := by
  rw [← Matrix.rank_transpose]
  refine rank_eq_card_of_isUnit_det _ c ?_
  have h : (Matrix.of (writeRow_tdg c))ᵀ.submatrix id c = 1 := by
    ext i i'
    change writeRow_tdg c (c i') i = (1 : Matrix d d ℝ) i i'
    rw [writeRow_emb_tdg, Pi.single_apply, Matrix.one_apply]
  rw [h, det_one]
  exact isUnit_one

/-- No write row of `θ†` vanishes. -/
private theorem writeRow_ne_zero_tdg [Nonempty d] {n : Type*} (c : d ↪ n) (j : n) :
    writeRow_tdg c j ≠ 0 := by
  by_cases hj : j ∈ Set.range c
  · obtain ⟨i, rfl⟩ := hj
    rw [writeRow_emb_tdg]
    exact fun h => by simpa using congrFun h i
  · rw [writeRow_of_notMem_tdg c hj]
    exact one_ne_zero

/-- On the orthant the gate `n ⬝ e_i = n_i` of a unit `c i` is positive. -/
private theorem gateCol_pos_tdg {n : Type*} (c : d ↪ n) (μ : n → ℝ) {j : n}
    (hj : j ∈ Finset.univ.map c) {x : d → ℝ} (hx : x ∈ posOrthant d) :
    0 < x ⬝ᵥ gateCol_tdg c μ j := by
  obtain ⟨i, _, rfl⟩ := Finset.mem_map.1 hj
  rw [gateCol_emb_tdg, dotProduct_single, mul_one]
  exact mem_posOrthant.1 hx i

omit [DecidableEq d] in
/-- On the orthant the gate `-μ_j ∑ n` of any other unit is negative. -/
private theorem gateCol_neg_tdg [Nonempty d] {n : Type*} (c : d ↪ n) {μ : n → ℝ}
    (hμ : ∀ j ∉ Set.range c, 0 < μ j)
    {j : n} (hj : j ∉ Finset.univ.map c) {x : d → ℝ} (hx : x ∈ posOrthant d) :
    x ⬝ᵥ gateCol_tdg c μ j < 0 := by
  have hj' : j ∉ Set.range c := fun ⟨i, hi⟩ => hj (Finset.mem_map.2 ⟨i, Finset.mem_univ i, hi⟩)
  rw [gateCol_of_notMem_tdg c μ hj', dotProduct_smul, dotProduct_one, smul_eq_mul]
  exact mul_neg_of_neg_of_pos (neg_neg_of_pos (hμ j hj')) (sum_pos_of_mem_posOrthant_tdg hx)

/-- Helper: the gate columns of `θ†` are linearly independent over `ℚ` when `1` and the `μ_j`
of the units outside the image of `c` are (the coefficients `κ` vanish on the image of `c`).
Coordinate `k` of a relation `∑ g_j c_j = 0` reads `g_{c k} - ∑_{j ∉ range c} g_j μ_j = 0`. -/
private theorem linearIndependent_gateCol_tdg [Nonempty d] {n : Type*} [Fintype n] (c : d ↪ n)
    (μ : n → ℝ)
    (hμ : ∀ (a : ℚ) (κ : n → ℚ), (∀ i, κ (c i) = 0) → (a : ℝ) + ∑ j, (κ j : ℝ) * μ j = 0 →
      a = 0 ∧ ∀ j, κ j = 0) :
    LinearIndependent ℚ (gateCol_tdg c μ) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hk : ∀ k, ((g (c k) : ℚ) : ℝ) +
      ∑ j, ((if j ∈ Set.range c then 0 else -g j : ℚ) : ℝ) * μ j = 0 := by
    intro k
    have h := congrFun hg k
    rw [Finset.sum_apply, Pi.zero_apply] at h
    rw [← h]
    -- termwise: `g_j (c_j)_k = g_j [j = c k] + (if j ∈ range c then 0 else -g_j) μ_j`
    have hterm : ∀ j, (g j • gateCol_tdg c μ j) k = (if c k = j then (g j : ℝ) else 0) +
        ((if j ∈ Set.range c then 0 else -g j : ℚ) : ℝ) * μ j := by
      intro j
      by_cases hj : j ∈ Set.range c
      · obtain ⟨i, rfl⟩ := hj
        simp [gateCol_emb_tdg, Rat.smul_def, Pi.single_apply, c.injective.eq_iff, eq_comm]
      · have hne : c k ≠ j := fun h => hj ⟨k, h⟩
        simp [gateCol_of_notMem_tdg c μ hj, hj, hne, Rat.smul_def]
    rw [Finset.sum_congr rfl fun j _ => hterm j, Finset.sum_add_distrib, Finset.sum_ite_eq]
    simp
  obtain ⟨k₀⟩ := ‹Nonempty d›
  intro j
  by_cases hj : j ∈ Set.range c
  · obtain ⟨k, rfl⟩ := hj
    exact (hμ _ _ (fun i => by simp) (hk k)).1
  · simpa [hj] using (hμ _ _ (fun i => by simp) (hk k₀)).2 j

/-- Helper: the matrices `c_j c_jᵀ` of the gate columns of `θ†` are linearly independent over `ℚ`
when `1` and the `μ_j²` are. The diagonal entry `(k, k)` of a relation reads
`g_{c k} + ∑_{j ∉ range c} g_j μ_j² = 0`. -/
private theorem linearIndependent_outer_gateCol_tdg [Nonempty d] {n : Type*} [Fintype n]
    (c : d ↪ n) (μ : n → ℝ)
    (hμ : ∀ (a : ℚ) (κ : n → ℚ), (a : ℝ) + ∑ j, (κ j : ℝ) * μ j ^ 2 = 0 → a = 0 ∧ ∀ j, κ j = 0) :
    LinearIndependent ℚ (fun j => vecMulVec (gateCol_tdg c μ j) (gateCol_tdg c μ j)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hk : ∀ k, ((g (c k) : ℚ) : ℝ) +
      ∑ j, ((if j ∈ Set.range c then 0 else g j : ℚ) : ℝ) * μ j ^ 2 = 0 := by
    intro k
    have h := congrFun (congrFun hg k) k
    rw [Matrix.sum_apply, Matrix.zero_apply] at h
    rw [← h]
    -- termwise: `g_j (c_j)_k² = g_j [j = c k] + (if j ∈ range c then 0 else g_j) μ_j²`
    have hterm : ∀ j, (g j • vecMulVec (gateCol_tdg c μ j) (gateCol_tdg c μ j)) k k =
        (if c k = j then (g j : ℝ) else 0) +
          ((if j ∈ Set.range c then 0 else g j : ℚ) : ℝ) * μ j ^ 2 := by
      intro j
      by_cases hj : j ∈ Set.range c
      · obtain ⟨i, rfl⟩ := hj
        by_cases hik : k = i
        · subst hik
          simp [gateCol_emb_tdg, Rat.smul_def, vecMulVec_apply]
        · simp [gateCol_emb_tdg, vecMulVec_apply, c.injective.eq_iff, hik]
      · have hne : c k ≠ j := fun h => hj ⟨k, h⟩
        rw [gateCol_of_notMem_tdg c μ hj]
        simp only [Matrix.smul_apply, vecMulVec_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul,
          Rat.smul_def, hj, hne, ↓reduceIte, zero_add]
        ring
    rw [Finset.sum_congr rfl fun j _ => hterm j, Finset.sum_add_distrib, Finset.sum_ite_eq]
    simp
  obtain ⟨k₀⟩ := ‹Nonempty d›
  intro j
  by_cases hj : j ∈ Set.range c
  · obtain ⟨k, rfl⟩ := hj
    exact (hμ _ _ (hk k)).1
  · simpa [hj] using (hμ _ _ (hk k₀)).2 j

/-- Helper: for `d ≥ 2` (two indices `k₁ ≠ k₂`) the matrices `c_j c_jᵀ` of the gate columns of
`θ†` are linearly independent over `ℚ` when the `μ_j²` of the units outside the image of `c` are.
Entry `(k, k')` of a relation reads `[k = k'] g_{c k} + ∑_{j ∉ range c} g_j μ_j² = 0`: the entries
off the diagonal give `g_j = 0` outside the image, and then the diagonal gives the others. -/
private theorem linearIndependent_outer_gateCol_of_ne_tdg {n : Type*} [Fintype n]
    (c : d ↪ n) (μ : n → ℝ) {k₁ k₂ : d} (hk : k₁ ≠ k₂)
    (hμ : ∀ κ : n → ℚ, (∀ i, κ (c i) = 0) → ∑ j, (κ j : ℝ) * μ j ^ 2 = 0 → ∀ j, κ j = 0) :
    LinearIndependent ℚ (fun j => vecMulVec (gateCol_tdg c μ j) (gateCol_tdg c μ j)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hent : ∀ k k', (if k = k' then ((g (c k) : ℚ) : ℝ) else 0) +
      ∑ j, ((if j ∈ Set.range c then 0 else g j : ℚ) : ℝ) * μ j ^ 2 = 0 := by
    intro k k'
    have h := congrFun (congrFun hg k) k'
    rw [Matrix.sum_apply, Matrix.zero_apply] at h
    refine Eq.trans ?_ h
    -- termwise: `g_j (c_j)_k (c_j)_k' = g_j [j = c k] [k = k'] + (… g_j) μ_j²`
    have hterm : ∀ j, (g j • vecMulVec (gateCol_tdg c μ j) (gateCol_tdg c μ j)) k k' =
        (if c k = j then (if k = k' then (g j : ℝ) else 0) else 0) +
          ((if j ∈ Set.range c then 0 else g j : ℚ) : ℝ) * μ j ^ 2 := by
      intro j
      by_cases hj : j ∈ Set.range c
      · obtain ⟨i, rfl⟩ := hj
        by_cases hik : k = i
        · subst hik
          by_cases hkk : k = k'
          · subst hkk
            simp [gateCol_emb_tdg, Rat.smul_def, vecMulVec_apply]
          · simp [gateCol_emb_tdg, vecMulVec_apply, hkk, Ne.symm hkk]
        · simp [gateCol_emb_tdg, vecMulVec_apply, c.injective.eq_iff, hik]
      · have hne : c k ≠ j := fun h => hj ⟨k, h⟩
        rw [gateCol_of_notMem_tdg c μ hj]
        simp only [Matrix.smul_apply, vecMulVec_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul,
          Rat.smul_def, hj, hne, ↓reduceIte, zero_add]
        ring
    rw [Finset.sum_congr rfl fun j _ => hterm j, Finset.sum_add_distrib, Finset.sum_ite_eq]
    simp
  -- off the diagonal: the coefficients outside the image vanish
  have hout : ∀ j, (if j ∈ Set.range c then 0 else g j : ℚ) = 0 := by
    have h := hent k₁ k₂
    simp only [hk, ↓reduceIte, zero_add] at h
    exact hμ _ (fun i => by simp) h
  intro j
  by_cases hj : j ∈ Set.range c
  · obtain ⟨k, rfl⟩ := hj
    have h := hent k k
    rw [Finset.sum_eq_zero (fun j _ => by rw [hout j]; simp), add_zero] at h
    simpa using h
  · simpa [hj] using hout j

omit [DecidableEq d] in
/-- Helper: `n ↦ (∑_k n_k) n` has an injective derivative at `𝟙`: it is
`v ↦ d v + (∑_k v_k) 𝟙`, and summing the coordinates of `d v + (∑ v) 𝟙 = 0` gives `2 d ∑ v = 0`. -/
private theorem injective_fderiv_sum_smul_tdg [Nonempty d] :
    Function.Injective (fderiv ℝ (fun n : d → ℝ => (∑ k, n k) • n) 1) := by
  have hs : HasFDerivAt (fun n : d → ℝ => ∑ k, n k)
      (∑ k, ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : d => ℝ) k) (1 : d → ℝ) :=
    HasFDerivAt.fun_sum fun k _ => hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : d => ℝ) k 1
  have h : HasFDerivAt (fun n : d → ℝ => (∑ k, n k) • n) _ (1 : d → ℝ) :=
    hs.smul (hasFDerivAt_id (1 : d → ℝ))
  rw [h.fderiv, injective_iff_map_eq_zero]
  intro v hv
  have hc : (0 : ℝ) < Fintype.card d := by exact_mod_cast Fintype.card_pos
  -- coordinate `i`: `d v_i + ∑_k v_k = 0`
  have hv' : ∀ i, (Fintype.card d : ℝ) * v i + ∑ k, v k = 0 := by
    intro i
    have := congrFun hv i
    simpa using this
  -- summing over `i`: `2 d ∑ v = 0`
  have hsum : ∑ k, v k = 0 := by
    have h2 := Finset.sum_eq_zero (s := Finset.univ) fun i _ => hv' i
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul] at h2
    have : (Fintype.card d : ℝ) * (2 * ∑ k, v k) = 0 := by linarith
    simpa [hc.ne'] using this
  funext i
  have := hv' i
  rw [hsum, add_zero] at this
  exact (mul_eq_zero.1 this).resolve_left hc.ne'

/-- `θ†` for gated blocks as in `Depth/Cones.lean`, from embeddings `ιE : d ↪ d_in`,
`ιD : d ↪ d_out`, `c ℓ : d ↪ hid ℓ` and numbers `μ`: `E`, `D` are the `0/1` matrices of the
embeddings, the gate columns are `gateCol_tdg`, every value column is `𝟙`, the write rows
`writeRow_tdg`. -/
private noncomputable def thetaGated_tdg (ιE : d ↪ dIn) (ιD : d ↪ dOut) (c : ∀ ℓ, d ↪ hid ℓ)
    (μ : ∀ ℓ, hid ℓ → ℝ) : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut where
  E := (embMat_tdg ιE)ᵀ
  read ℓ := Matrix.of fun k (s : hid ℓ ⊕ hid ℓ) =>
    Sum.elim (fun j => gateCol_tdg (c ℓ) (μ ℓ) j k) (fun _ => 1) s
  write ℓ := Matrix.of (writeRow_tdg (c ℓ))
  D := embMat_tdg ιD

open Classical in
omit [DecidableEq d] in
/-- The entry `k` of the gate column of unit `j`: `[j = c k]` on the image of `c`, `-μ_j`
elsewhere. -/
private theorem gateCol_apply_tdg {n : Type*} (c : d ↪ n) (μ : n → ℝ) (j : n) (k : d) :
    gateCol_tdg c μ j k =
      if j ∈ Set.range c then (if j = c k then 1 else 0) else -μ j := by
  by_cases hj : j ∈ Set.range c <;> simp [gateCol_tdg, unitRow_tdg, hj]

open Classical in
omit [DecidableEq d] in
/-- The entry `k` of the write row of unit `j`: `[j = c k]` on the image of `c`, `1` elsewhere. -/
private theorem writeRow_apply_tdg {n : Type*} (c : d ↪ n) (j : n) (k : d) :
    writeRow_tdg c j k = if j ∈ Set.range c then (if j = c k then 1 else 0) else 1 := by
  by_cases hj : j ∈ Set.range c <;> simp [writeRow_tdg, unitRow_tdg, hj]

omit [Fintype T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- `thetaDaggerGated` is `thetaGated_tdg`, the parameter of `Depth/Cones.lean`. -/
private theorem thetaDaggerGated_eq_tdg (ιE : d ↪ dIn) (ιD : d ↪ dOut) (c : ∀ ℓ, d ↪ hid ℓ)
    (μ : ∀ ℓ, hid ℓ → ℝ) :
    thetaDaggerGated (T := T) (σ := σ) (χ := χ) ιE ιD c μ =
      thetaGated_tdg (T := T) (σ := σ) (χ := χ) ιE ιD c μ := by
  simp only [thetaDaggerGated, thetaGated_tdg]
  congr 1
  · funext ℓ
    ext k s
    rcases s with j | j
    · simp only [Matrix.of_apply, Sum.elim_inl, gateCol_apply_tdg]
    · rfl
  · funext ℓ
    ext j k
    simp only [Matrix.of_apply, writeRow_apply_tdg]

omit [Fintype T] [Fintype dIn] [Fintype dOut] in
/-- The frozen gated block of `θ†` is `n ↦ ∑_i n_i (∑_k n_k) e_i = (∑_k n_k) n`. -/
private theorem frozenGated_thetaGated_tdg (ιE : d ↪ dIn) (ιD : d ↪ dOut) (c : ∀ ℓ, d ↪ hid ℓ)
    (μ : ∀ ℓ, hid ℓ → ℝ) (ℓ : Fin L) :
    frozenGated (thetaGated_tdg (T := T) (σ := σ) (χ := χ) ιE ιD c μ) ℓ
      (Finset.univ.map (c ℓ)) = fun n => (∑ k, n k) • n := by
  funext n
  rw [frozenGated, Finset.sum_map]
  change ∑ i, ((n ⬝ᵥ gateCol_tdg (c ℓ) (μ ℓ) (c ℓ i)) * (n ⬝ᵥ 1)) •
    writeRow_tdg (c ℓ) (c ℓ i) = _
  simp only [gateCol_emb_tdg, writeRow_emb_tdg, dotProduct_single, dotProduct_one, mul_one]
  funext k
  simp [Finset.sum_apply, Pi.single_apply, mul_comm]

omit [Fintype T] in
/-- `θ†` (gated) is good for the orthants, with the active sets `range c_ℓ`. -/
private theorem goodForConesGated_thetaGated_tdg [Nonempty d] (ιE : d ↪ dIn) (ιD : d ↪ dOut)
    (c : ∀ ℓ, d ↪ hid ℓ) {μ : ∀ ℓ, hid ℓ → ℝ} (hμ : ∀ ℓ, ∀ j ∉ Set.range (c ℓ), 0 < μ ℓ j) :
    GoodForConesGated (fun _ => posOrthant d) (fun ℓ => Finset.univ.map (c ℓ))
      (thetaGated_tdg (T := T) (σ := σ) (χ := χ) ιE ιD c μ) := by
  refine ⟨fun _ => isOpenConvexCone_orthant_tdg,
    (Matrix.rank_transpose _).trans (rank_embMat_tdg ιE), rank_embMat_tdg ιD,
    fun ℓ => rank_writeRow_tdg (c ℓ), fun ℓ n hn j hj => gateCol_pos_tdg (c ℓ) (μ ℓ) hj hn,
    fun ℓ n hn j hj => gateCol_neg_tdg (c ℓ) (hμ ℓ) hj hn, fun ℓ n hn => ?_, fun ℓ => ⟨1, ?_⟩,
    fun ℓ j => writeRow_ne_zero_tdg (c ℓ) j, fun ℓ j => one_ne_zero⟩
  · -- (K2): `(∑ n) n` lies in the orthant
    rw [frozenGated_thetaGated_tdg]
    exact isOpenConvexCone_orthant_tdg.smul_mem n hn _ (sum_pos_of_mem_posOrthant_tdg hn)
  · -- (K2): the derivative at `𝟙` is injective
    rw [frozenGated_thetaGated_tdg]
    exact injective_fderiv_sum_smul_tdg

/-- `θ†` for MLP blocks as in `Depth/Cones.lean`: as `thetaGated_tdg`, without value columns. -/
private noncomputable def thetaMlp_tdg (ιE : d ↪ dIn) (ιD : d ↪ dOut) (c : ∀ ℓ, d ↪ hid ℓ)
    (μ : ∀ ℓ, hid ℓ → ℝ) : Params (Arch.mlp (T := T) (d := d) σ χ hid) dIn dOut where
  E := (embMat_tdg ιE)ᵀ
  read ℓ := Matrix.of fun k j => gateCol_tdg (c ℓ) (μ ℓ) j k
  write ℓ := Matrix.of (writeRow_tdg (c ℓ))
  D := embMat_tdg ιD

omit [Fintype T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- `thetaDaggerMlp` is `thetaMlp_tdg`, the parameter of `Depth/Cones.lean`. -/
private theorem thetaDaggerMlp_eq_tdg (ιE : d ↪ dIn) (ιD : d ↪ dOut) (c : ∀ ℓ, d ↪ hid ℓ)
    (μ : ∀ ℓ, hid ℓ → ℝ) :
    thetaDaggerMlp (T := T) (σ := σ) (χ := χ) ιE ιD c μ =
      thetaMlp_tdg (T := T) (σ := σ) (χ := χ) ιE ιD c μ := by
  simp only [thetaDaggerMlp, thetaMlp_tdg]
  congr 1
  · funext ℓ
    ext k j
    simp only [Matrix.of_apply, gateCol_apply_tdg]
  · funext ℓ
    ext j k
    simp only [Matrix.of_apply, writeRow_apply_tdg]

omit [Fintype T] [Fintype dIn] [Fintype dOut] in
/-- The frozen MLP block of `θ†` is `n ↦ ∑_i n_i e_i = n`. -/
private theorem frozenMlp_thetaMlp_tdg (ιE : d ↪ dIn) (ιD : d ↪ dOut) (c : ∀ ℓ, d ↪ hid ℓ)
    (μ : ∀ ℓ, hid ℓ → ℝ) (ℓ : Fin L) :
    frozenMlp (thetaMlp_tdg (T := T) (σ := σ) (χ := χ) ιE ιD c μ) ℓ
      (Finset.univ.map (c ℓ)) = id := by
  funext n
  rw [frozenMlp, Finset.sum_map]
  change ∑ i, (n ⬝ᵥ gateCol_tdg (c ℓ) (μ ℓ) (c ℓ i)) • writeRow_tdg (c ℓ) (c ℓ i) = n
  simp only [gateCol_emb_tdg, writeRow_emb_tdg, dotProduct_single, mul_one]
  funext k
  simp [Finset.sum_apply, Pi.single_apply]

omit [Fintype T] in
/-- `θ†` (MLP) is good for the orthants, with the active sets `range c_ℓ`. -/
private theorem goodForConesMlp_thetaMlp_tdg [Nonempty d] (ιE : d ↪ dIn) (ιD : d ↪ dOut)
    (c : ∀ ℓ, d ↪ hid ℓ) {μ : ∀ ℓ, hid ℓ → ℝ} (hμ : ∀ ℓ, ∀ j ∉ Set.range (c ℓ), 0 < μ ℓ j) :
    GoodForConesMlp (fun _ => posOrthant d) (fun ℓ => Finset.univ.map (c ℓ))
      (thetaMlp_tdg (T := T) (σ := σ) (χ := χ) ιE ιD c μ) := by
  refine ⟨fun _ => isOpenConvexCone_orthant_tdg,
    (Matrix.rank_transpose _).trans (rank_embMat_tdg ιE), rank_embMat_tdg ιD,
    fun ℓ => rank_writeRow_tdg (c ℓ), fun ℓ n hn j hj => gateCol_pos_tdg (c ℓ) (μ ℓ) hj hn,
    fun ℓ n hn j hj => gateCol_neg_tdg (c ℓ) (hμ ℓ) hj hn, fun ℓ n hn => ?_, fun ℓ => ⟨1, ?_⟩,
    fun ℓ j => writeRow_ne_zero_tdg (c ℓ) j⟩
  · -- (K2): the frozen block is the identity, so it maps the orthant to itself
    rw [frozenMlp_thetaMlp_tdg]
    exact hn
  · -- (K2): its derivative is the identity
    rw [frozenMlp_thetaMlp_tdg, fderiv_id]
    exact fun v w h => h

omit [Fintype T] in
/-- **Lemma D.13 of the dimension paper for SwiGLU blocks, with `θ†` written out:** for `d ≥ 1`
there are numbers `μ > 0` such that `θ†` is good for the cones `C_0 = ⋯ = C_L = ℝ^{1×d}_{>0}` with
the active sets `A_ℓ` = the image of `c ℓ` (the paper's `{1, …, d_model}`), the frozen blocks are
`g°_ℓ(n) = (n𝟙) n`, and the gate columns of every block are linearly independent over `ℚ`. -/
theorem exists_mu_thetaDaggerGated_cols [Nonempty d] (ιE : d ↪ dIn) (ιD : d ↪ dOut)
    (c : ∀ ℓ, d ↪ hid ℓ) :
    ∃ μ : ∀ ℓ, hid ℓ → ℝ, (∀ ℓ j, 0 < μ ℓ j) ∧
      GoodForConesGated (fun _ => posOrthant d) (fun ℓ => Finset.univ.map (c ℓ))
        (thetaDaggerGated (T := T) (σ := σ) (χ := χ) ιE ιD c μ) ∧
      (∀ ℓ (n : d → ℝ), frozenGated (thetaDaggerGated (T := T) (σ := σ) (χ := χ) ιE ιD c μ) ℓ
        (Finset.univ.map (c ℓ)) n = (∑ k, n k) • n) ∧
      ∀ ℓ, LinearIndependent ℚ (fun j : hid ℓ =>
        ((thetaDaggerGated (T := T) (σ := σ) (χ := χ) ιE ιD c μ).read ℓ)ᵀ (Sum.inl j)) := by
  -- the numbers `μ` (Liouville powers); `1` and the `μ_j` are independent over `ℚ`
  choose μ hμpos hμ1 _ using fun ℓ => exists_pos_indep_tdg (hid ℓ)
  -- `θ†` is the parameter of `Depth/Cones.lean`, with the gate columns `e_i` and `-μ_j 𝟙`
  refine ⟨μ, hμpos, ?_, fun ℓ n => ?_, fun ℓ => ?_⟩ <;> rw [thetaDaggerGated_eq_tdg]
  · exact goodForConesGated_thetaGated_tdg ιE ιD c fun ℓ j _ => hμpos ℓ j
  · exact congrFun (frozenGated_thetaGated_tdg ιE ιD c μ ℓ) n
  · exact linearIndependent_gateCol_tdg (c ℓ) (μ ℓ) fun a κ _ h => hμ1 ℓ a κ h

omit [Fintype T] in
/-- **Lemma D.13 of the dimension paper for GeGLU blocks, with `θ†` written out:** for `d ≥ 2`
there are numbers `μ > 0` such that `θ†` is good for the positive orthants with the active sets
`A_ℓ` = the image of `c ℓ`, the frozen blocks are `g°_ℓ(n) = (n𝟙) n`, and the matrices
`c_j c_j^⊤` of the gate columns of every block are linearly independent over `ℚ`. -/
theorem exists_mu_thetaDaggerGated_outer (hd : 2 ≤ Fintype.card d) (ιE : d ↪ dIn)
    (ιD : d ↪ dOut) (c : ∀ ℓ, d ↪ hid ℓ) :
    ∃ μ : ∀ ℓ, hid ℓ → ℝ, (∀ ℓ j, 0 < μ ℓ j) ∧
      GoodForConesGated (fun _ => posOrthant d) (fun ℓ => Finset.univ.map (c ℓ))
        (thetaDaggerGated (T := T) (σ := σ) (χ := χ) ιE ιD c μ) ∧
      (∀ ℓ (n : d → ℝ), frozenGated (thetaDaggerGated (T := T) (σ := σ) (χ := χ) ιE ιD c μ) ℓ
        (Finset.univ.map (c ℓ)) n = (∑ k, n k) • n) ∧
      ∀ ℓ, LinearIndependent ℚ (fun j : hid ℓ => Matrix.vecMulVec
        (((thetaDaggerGated (T := T) (σ := σ) (χ := χ) ιE ιD c μ).read ℓ)ᵀ (Sum.inl j))
        (((thetaDaggerGated (T := T) (σ := σ) (χ := χ) ιE ιD c μ).read ℓ)ᵀ (Sum.inl j))) := by
  have : Nonempty d := Fintype.card_pos_iff.1 (by omega)
  -- the numbers `μ` (Liouville powers); `1` and the `μ_j²` are independent over `ℚ`
  choose μ hμpos _ hμ2 using fun ℓ => exists_pos_indep_tdg (hid ℓ)
  -- `θ†` is the parameter of `Depth/Cones.lean`; `c_j c_jᵀ` is a matrix unit or `μ_j²` times ones
  refine ⟨μ, hμpos, ?_, fun ℓ n => ?_, fun ℓ => ?_⟩ <;> rw [thetaDaggerGated_eq_tdg]
  · exact goodForConesGated_thetaGated_tdg ιE ιD c fun ℓ j _ => hμpos ℓ j
  · exact congrFun (frozenGated_thetaGated_tdg ιE ιD c μ ℓ) n
  · exact linearIndependent_outer_gateCol_tdg (c ℓ) (μ ℓ) (hμ2 ℓ)

omit [Fintype T] in
/-- **Lemma D.13 of the dimension paper for GELU blocks, with `θ†` written out:** for `d ≥ 2`
there are numbers `μ > 0` such that `θ†` is good for the positive orthants with the active sets
`A_ℓ` = the image of `c ℓ`, the frozen blocks are `g°_ℓ(n) = n`, and the matrices `c_j c_j^⊤` of
the read columns of every block are linearly independent over `ℚ`. -/
theorem exists_mu_thetaDaggerMlp_outer (hd : 2 ≤ Fintype.card d) (ιE : d ↪ dIn)
    (ιD : d ↪ dOut) (c : ∀ ℓ, d ↪ hid ℓ) :
    ∃ μ : ∀ ℓ, hid ℓ → ℝ, (∀ ℓ j, 0 < μ ℓ j) ∧
      GoodForConesMlp (fun _ => posOrthant d) (fun ℓ => Finset.univ.map (c ℓ))
        (thetaDaggerMlp (T := T) (σ := σ) (χ := χ) ιE ιD c μ) ∧
      (∀ ℓ (n : d → ℝ), frozenMlp (thetaDaggerMlp (T := T) (σ := σ) (χ := χ) ιE ιD c μ) ℓ
        (Finset.univ.map (c ℓ)) n = n) ∧
      ∀ ℓ, LinearIndependent ℚ (fun j : hid ℓ => Matrix.vecMulVec
        (((thetaDaggerMlp (T := T) (σ := σ) (χ := χ) ιE ιD c μ).read ℓ)ᵀ j)
        (((thetaDaggerMlp (T := T) (σ := σ) (χ := χ) ιE ιD c μ).read ℓ)ᵀ j)) := by
  have : Nonempty d := Fintype.card_pos_iff.1 (by omega)
  -- the numbers `μ` (Liouville powers); `1` and the `μ_j²` are independent over `ℚ`
  choose μ hμpos _ hμ2 using fun ℓ => exists_pos_indep_tdg (hid ℓ)
  -- `θ†` is the parameter of `Depth/Cones.lean`; `c_j c_jᵀ` is a matrix unit or `μ_j²` times ones
  refine ⟨μ, hμpos, ?_, fun ℓ n => ?_, fun ℓ => ?_⟩ <;> rw [thetaDaggerMlp_eq_tdg]
  · exact goodForConesMlp_thetaMlp_tdg ιE ιD c fun ℓ j _ => hμpos ℓ j
  · exact congrFun (frozenMlp_thetaMlp_tdg ιE ιD c μ ℓ) n
  · exact linearIndependent_outer_gateCol_tdg (c ℓ) (μ ℓ) (hμ2 ℓ)

/-! ## The lemma for every admissible choice of the numbers `μ`

The paper chooses any numbers `μ_1, μ_2, … > 0` with the independence over `ℚ`, one number for each
hidden unit after the first `d_model`. Here `μ ℓ j` is a number for every unit `j` of block `ℓ`,
and `θ†` uses it only for the units outside the image of `c ℓ`; so positivity and independence are
asked of those numbers only. "The `μ ℓ j` of the units outside the image of `c ℓ` are linearly
independent over `ℚ`" is written out: a combination `∑_j κ_j μ_j` with rational coefficients that
vanish on the image of `c ℓ` is zero only if all `κ_j` are zero. -/

omit [Fintype T] in
/-- **Lemma D.13 of the dimension paper for gated blocks, for every choice of the numbers
`μ > 0`:** `θ†` is good for the cones `C_0 = ⋯ = C_L = ℝ^{1×d}_{>0}` with the active sets `A_ℓ` =
the image of `c ℓ` (the paper's `{1, …, d_model}`). The independence over `ℚ` of (K3) is
`linearIndependent_gate_thetaDaggerGated` (SwiGLU) and
`linearIndependent_outer_gate_thetaDaggerGated` (GeGLU). -/
theorem goodForConesGated_thetaDaggerGated [Nonempty d] (ιE : d ↪ dIn) (ιD : d ↪ dOut)
    (c : ∀ ℓ, d ↪ hid ℓ) {μ : ∀ ℓ, hid ℓ → ℝ} (hμ : ∀ ℓ, ∀ j ∉ Set.range (c ℓ), 0 < μ ℓ j) :
    GoodForConesGated (fun _ => posOrthant d) (fun ℓ => Finset.univ.map (c ℓ))
      (thetaDaggerGated (T := T) (σ := σ) (χ := χ) ιE ιD c μ) := by
  rw [thetaDaggerGated_eq_tdg]
  exact goodForConesGated_thetaGated_tdg ιE ιD c hμ

omit [Fintype T] [Fintype dIn] [Fintype dOut] in
/-- **Lemma D.13, the frozen block of `θ†` for gated blocks:** `g°_ℓ(n) = (n𝟙) n`, for every `μ`. -/
theorem frozenGated_thetaDaggerGated (ιE : d ↪ dIn) (ιD : d ↪ dOut) (c : ∀ ℓ, d ↪ hid ℓ)
    (μ : ∀ ℓ, hid ℓ → ℝ) (ℓ : Fin L) (n : d → ℝ) :
    frozenGated (thetaDaggerGated (T := T) (σ := σ) (χ := χ) ιE ιD c μ) ℓ
      (Finset.univ.map (c ℓ)) n = (∑ k, n k) • n := by
  rw [thetaDaggerGated_eq_tdg]
  exact congrFun (frozenGated_thetaGated_tdg ιE ιD c μ ℓ) n

omit [Fintype T] [Fintype dIn] [Fintype dOut] in
/-- **Lemma D.13, (K3) for SwiGLU blocks, for every admissible `μ`:** if `1` and the numbers
`μ ℓ j` of the units outside the image of `c ℓ` are linearly independent over `ℚ`, the gate columns
of block `ℓ` of `θ†` are linearly independent over `ℚ`. -/
theorem linearIndependent_gate_thetaDaggerGated [Nonempty d] (ιE : d ↪ dIn) (ιD : d ↪ dOut)
    (c : ∀ ℓ, d ↪ hid ℓ) (μ : ∀ ℓ, hid ℓ → ℝ) (ℓ : Fin L)
    (hμ : ∀ (a : ℚ) (κ : hid ℓ → ℚ), (∀ i, κ (c ℓ i) = 0) →
      (a : ℝ) + ∑ j, (κ j : ℝ) * μ ℓ j = 0 → a = 0 ∧ ∀ j, κ j = 0) :
    LinearIndependent ℚ (fun j : hid ℓ =>
      ((thetaDaggerGated (T := T) (σ := σ) (χ := χ) ιE ιD c μ).read ℓ)ᵀ (Sum.inl j)) := by
  rw [thetaDaggerGated_eq_tdg]
  exact linearIndependent_gateCol_tdg (c ℓ) (μ ℓ) hμ

omit [Fintype T] [Fintype dIn] [Fintype dOut] in
/-- **Lemma D.13, (K3) for GeGLU blocks, for every admissible `μ`:** for `d ≥ 2`, if the numbers
`(μ ℓ j)²` of the units outside the image of `c ℓ` are linearly independent over `ℚ`, the matrices
`c_j c_j^⊤` of the gate columns of block `ℓ` of `θ†` are linearly independent over `ℚ`. -/
theorem linearIndependent_outer_gate_thetaDaggerGated (hd : 2 ≤ Fintype.card d) (ιE : d ↪ dIn)
    (ιD : d ↪ dOut) (c : ∀ ℓ, d ↪ hid ℓ) (μ : ∀ ℓ, hid ℓ → ℝ) (ℓ : Fin L)
    (hμ : ∀ κ : hid ℓ → ℚ, (∀ i, κ (c ℓ i) = 0) → ∑ j, (κ j : ℝ) * μ ℓ j ^ 2 = 0 →
      ∀ j, κ j = 0) :
    LinearIndependent ℚ (fun j : hid ℓ => Matrix.vecMulVec
      (((thetaDaggerGated (T := T) (σ := σ) (χ := χ) ιE ιD c μ).read ℓ)ᵀ (Sum.inl j))
      (((thetaDaggerGated (T := T) (σ := σ) (χ := χ) ιE ιD c μ).read ℓ)ᵀ (Sum.inl j))) := by
  obtain ⟨k₁, k₂, hk⟩ := Fintype.one_lt_card_iff.1 (show 1 < Fintype.card d by omega)
  rw [thetaDaggerGated_eq_tdg]
  exact linearIndependent_outer_gateCol_of_ne_tdg (c ℓ) (μ ℓ) hk hμ

omit [Fintype T] in
/-- **Lemma D.13 of the dimension paper for GELU blocks, for every choice of the numbers
`μ > 0`:** `θ†` is good for the positive orthants with the active sets `A_ℓ` = the image of `c ℓ`.
The independence over `ℚ` of (K3) is `linearIndependent_outer_read_thetaDaggerMlp`. -/
theorem goodForConesMlp_thetaDaggerMlp [Nonempty d] (ιE : d ↪ dIn) (ιD : d ↪ dOut)
    (c : ∀ ℓ, d ↪ hid ℓ) {μ : ∀ ℓ, hid ℓ → ℝ} (hμ : ∀ ℓ, ∀ j ∉ Set.range (c ℓ), 0 < μ ℓ j) :
    GoodForConesMlp (fun _ => posOrthant d) (fun ℓ => Finset.univ.map (c ℓ))
      (thetaDaggerMlp (T := T) (σ := σ) (χ := χ) ιE ιD c μ) := by
  rw [thetaDaggerMlp_eq_tdg]
  exact goodForConesMlp_thetaMlp_tdg ιE ιD c hμ

omit [Fintype T] [Fintype dIn] [Fintype dOut] in
/-- **Lemma D.13, the frozen block of `θ†` for GELU blocks:** `g°_ℓ(n) = n`, for every `μ`. -/
theorem frozenMlp_thetaDaggerMlp (ιE : d ↪ dIn) (ιD : d ↪ dOut) (c : ∀ ℓ, d ↪ hid ℓ)
    (μ : ∀ ℓ, hid ℓ → ℝ) (ℓ : Fin L) (n : d → ℝ) :
    frozenMlp (thetaDaggerMlp (T := T) (σ := σ) (χ := χ) ιE ιD c μ) ℓ
      (Finset.univ.map (c ℓ)) n = n := by
  rw [thetaDaggerMlp_eq_tdg]
  exact congrFun (frozenMlp_thetaMlp_tdg ιE ιD c μ ℓ) n

omit [Fintype T] [Fintype dIn] [Fintype dOut] in
/-- **Lemma D.13, (K3) for GELU blocks, for every admissible `μ`:** for `d ≥ 2`, if the numbers
`(μ ℓ j)²` of the units outside the image of `c ℓ` are linearly independent over `ℚ`, the matrices
`c_j c_j^⊤` of the read columns of block `ℓ` of `θ†` are linearly independent over `ℚ`. -/
theorem linearIndependent_outer_read_thetaDaggerMlp (hd : 2 ≤ Fintype.card d) (ιE : d ↪ dIn)
    (ιD : d ↪ dOut) (c : ∀ ℓ, d ↪ hid ℓ) (μ : ∀ ℓ, hid ℓ → ℝ) (ℓ : Fin L)
    (hμ : ∀ κ : hid ℓ → ℚ, (∀ i, κ (c ℓ i) = 0) → ∑ j, (κ j : ℝ) * μ ℓ j ^ 2 = 0 →
      ∀ j, κ j = 0) :
    LinearIndependent ℚ (fun j : hid ℓ => Matrix.vecMulVec
      (((thetaDaggerMlp (T := T) (σ := σ) (χ := χ) ιE ιD c μ).read ℓ)ᵀ j)
      (((thetaDaggerMlp (T := T) (σ := σ) (χ := χ) ιE ιD c μ).read ℓ)ᵀ j)) := by
  obtain ⟨k₁, k₂, hk⟩ := Fintype.one_lt_card_iff.1 (show 1 < Fintype.card d by omega)
  rw [thetaDaggerMlp_eq_tdg]
  exact linearIndependent_outer_gateCol_of_ne_tdg (c ℓ) (μ ℓ) hk hμ

end Skips
