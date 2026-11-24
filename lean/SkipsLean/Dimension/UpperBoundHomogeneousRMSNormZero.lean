import SkipsLean.OneBlock.SkiplessHomogeneousGatedRMSZero

/-!
# Skipless networks of positively homogeneous blocks under pre-RMSNorm with `ε = 0`: the bound
with `GL(d)` at every hidden state before the last

Paper (skips paper), Theorem A.12 (iii), last sentence: "For `ε = 0` and positively homogeneous
blocks, the skipless network does not satisfy the equality condition (Lemma A.3)." And after
Theorem A.17: "For `ε = 0` and positively homogeneous blocks, a skipless network has more
symmetries than the changes of basis in `𝒢`: all of `GL(d_model)` at `h_0, …, h_{L−1}` (Lemma
A.3). Its functional dimension then lies below the bound of (ii), so it does not satisfy the
equality condition".

Here, at any depth `L`, for a skipless network under pre-RMSNorm with `ε = 0`:
* for blocks that are positively homogeneous row by row (`RowHomogeneous`, Lemma A.3 (i) in
  `Symmetry/HomogeneousRMSNorm.lean`), the direction of a change of basis `I + τ X` at a hidden
  state before the last is flat, for every matrix `X`;
* for MLP blocks with a positively homogeneous activation (ReLU, ReLU²; `s` the number of hidden
  units) and for gated blocks with a positively homogeneous gate (ReGLU; `s` twice that number):
  `fd ≤ P − L d² − (d(d−1)/2 + 1) − s`, at one parameter under the conditions of independence
  (`E` and the writes of rank `d ≥ 1`, no read column zero) and at almost every parameter for
  `d_in ≥ d` and blocks of width at least `d`;
* for `d ≥ 2` and `L ≥ 1`, at almost every parameter the functional dimension is strictly below
  the bound `P − (L + 1) (d(d−1)/2 + 1) − s` of the changes of basis in `CO(d)`: the skipless
  network does not attain it. (Lean asks `d ≥ 2` and `L ≥ 1` for the strict form, and `d_in ≥ d`
  and widths at least `d`, the conditions of Lemma A.18 under which the directions are
  independent; Theorem A.12 and the remark after Theorem A.17 do not state them, the Scope of
  Section 2 does; for `d = 1`, `GL(1) = CO(1)` and the two bounds are equal.)
The case `L = 1` is `OneBlock/SkiplessHomogeneousRMSZero.lean` and its gated twin. The functional
dimension is Lean's `funDim` (all inputs; `rmsNorm 0` maps a zero row to `0`), which is at least
the paper's.
-/

namespace Skips

open Matrix MeasureTheory

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]

open scoped Matrix.Norms.Elementwise in
omit [Fintype T] in
/-- Helper (the private `hasDerivAt_cobExp_smul_shz` of
`OneBlock/SkiplessHomogeneousRMSZero.lean`): the curve `τ ↦ θ.cob (exp (τ m)) (exp (τ m))` has
velocity `cobDir θ m` at `τ = 0`. -/
private theorem hasDerivAt_cobExp_smul_uhz {A : Arch T d L} (θ : Params A dIn dOut)
    (m : Fin (L + 1) → Matrix d d ℝ) :
    HasDerivAt (fun τ : ℝ => cobExp θ (τ • m)) (cobDir θ m) 0 := by
  obtain ⟨Φ', hΦ, hΦm⟩ := hasStrictFDerivAt_cobExp θ
  -- the line `τ ↦ τ m` has velocity `1 • m`; the chain rule
  have hl := (hasDerivAt_id (0 : ℝ)).smul_const m
  have h := hΦ.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)
  exact h.congr_deriv ((congrArg Φ' (one_smul ℝ m)).trans (hΦm m))

omit [Fintype T] [Fintype dIn] [Fintype dOut] in
/-- Helper: `θ.cob (exp (τ m)) (exp (τ m))` for the family `m` that is `X` at the hidden state
`j` and `0` elsewhere is the change of basis `exp (τ X)` at `h_j` alone (`exp 0 = I` at the
other hidden states). -/
private theorem cobExp_smul_single_eq_cobAt_uhz {A : Arch T d L} (θ : Params A dIn dOut)
    (j : Fin (L + 1)) (X : Matrix d d ℝ) (τ : ℝ) :
    cobExp θ (τ • Pi.single j X) = θ.cobAt j (expGL (τ • X)) := by
  -- the two families of changes of basis agree: `exp (τ X)` at `h_j`, `exp (τ 0) = I` elsewhere
  have hG : (fun i => expGL ((τ • Pi.single j X : Fin (L + 1) → Matrix d d ℝ) i))
      = Function.update (fun _ => 1) j (expGL (τ • X)) := by
    funext i
    by_cases hi : i = j
    · subst hi
      rw [Function.update_self, Pi.smul_apply, Pi.single_eq_same]
    · rw [Function.update_of_ne hi, Pi.smul_apply, Pi.single_eq_of_ne hi]
      apply Units.ext
      show NormedSpace.exp (τ • (0 : Matrix d d ℝ)) = 1
      rw [smul_zero, NormedSpace.exp_zero]
  unfold cobExp Params.cobAt
  rw [hG]

/-- Helper: if the changes of basis `exp (τ m)` keep the function for every `τ`, the direction
`cobDir θ m` is flat. -/
private theorem cobDir_mem_flat_of_cobExp_uhz {A : Arch T d L} (θ : Params A dIn dOut)
    (m : Fin (L + 1) → Matrix d d ℝ)
    (hconst : ∀ τ : ℝ, ∀ x, eval A 0 (cobExp θ (τ • m)) x = eval A 0 θ x) :
    cobDir θ m ∈ flat A 0 θ :=
  -- the curve `τ ↦ θ.cob (exp (τ m))` passes through `θ` with velocity `cobDir θ m`
  mem_flat_of_hasDerivAt' θ (fun τ => cobExp θ (τ • m)) (cobDir θ m)
    (hasDerivAt_cobExp_smul_uhz θ m) (by rw [zero_smul]; exact cobExp_zero θ)
    (Filter.Eventually.of_forall fun τ x => hconst τ x)

/-- **Lemma A.3 (i) of the skips paper as a statement on directions, at any depth:** for a
skipless network under pre-RMSNorm with `ε = 0` whose blocks are positively homogeneous row by
row, the direction of the change of basis `I + τ X` at a hidden state `h_ℓ` before the last is
flat, for every matrix `X`. -/
theorem cobDir_single_mem_flat_skipless_rmsNorm_zero_of_rowHomogeneous {A : Arch T d L}
    (hA : A.χ = rmsNorm 0) {k : ℕ} (hf : RowHomogeneous A k)
    (θ : Params A dIn dOut) (ℓ : Fin L) (X : Matrix d d ℝ) :
    cobDir θ (Pi.single ℓ.castSucc X) ∈ flat A 0 θ := by
  -- the curve `τ ↦ θ.cob (exp (τ m))` for `m` equal to `X` at `h_ℓ` and `0` elsewhere passes
  -- through `θ` with velocity `cobDir θ m`; at every `τ` it is the change of basis `exp (τ X)` at
  -- `h_ℓ`, `ℓ < L`, which keeps the function (Lemma A.3 (i))
  refine cobDir_mem_flat_of_cobExp_uhz θ _ fun τ x => ?_
  rw [cobExp_smul_single_eq_cobAt_uhz]
  exact eval_cobAt_rmsNorm_zero_of_rowHomogeneous hA hf θ ℓ (expGL (τ • X)) x

variable {σ : ℝ → ℝ} {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]

omit [Fintype T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (the private `cancel_left_of_rank` of `Dimension/RescalingMlp.lean`): a matrix `M` of
rank equal to its number of columns cancels on the left, `M X = M Y → X = Y` (its kernel is `0`
by rank–nullity). -/
private theorem cancel_left_of_rank_uhz {m n k : Type*} [Fintype n] (M : Matrix m n ℝ)
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

omit [Fintype T] [Fintype d] [Fintype dIn] [Fintype dOut] in
/-- Helper: if `Y + b I = 0` with `Y` antisymmetric, then `Y = 0` and `b = 0`: the diagonal of an
antisymmetric matrix vanishes, so a diagonal entry gives `b = 0`. -/
private theorem antisymm_add_smul_one_eq_zero_uhz [Nonempty d] {Y : Matrix d d ℝ}
    (hY : Yᵀ = -Y) {b : ℝ} (h : Y + b • (1 : Matrix d d ℝ) = 0) : Y = 0 ∧ b = 0 := by
  obtain ⟨k⟩ := ‹Nonempty d›
  -- the diagonal entry `(k, k)` of `Y` vanishes
  have hd : Y k k = 0 := by
    have := congrFun (congrFun hY k) k
    rw [transpose_apply, Matrix.neg_apply] at this
    linarith
  -- so the entry `(k, k)` of `Y + b I` is `b`
  have hk := congrFun (congrFun h k) k
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one, hd,
    zero_add, Matrix.zero_apply] at hk
  subst hk
  simpa using h

omit [Fintype T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: matrices `X_0, …, X_{L−1}` and an antisymmetric matrix `Y`, as the family
`(X_0, …, X_{L−1}, Y)` of matrices on the `L + 1` hidden states, linearly. -/
private noncomputable def snocLin_uhz :
    ((Fin L → Matrix d d ℝ) × antisymmetric d) →ₗ[ℝ] (Fin (L + 1) → Matrix d d ℝ) where
  toFun p := Fin.snoc (α := fun _ => Matrix d d ℝ) p.1 (p.2 : Matrix d d ℝ)
  map_add' p q := by
    funext i
    cases i using Fin.lastCases with
    | last => simp
    | cast j => simp
  map_smul' c p := by
    funext i
    cases i using Fin.lastCases with
    | last => simp
    | cast j => simp

omit [Fintype T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the family `(X_0, …, X_{L−1}, Y)` is `X_ℓ` at `h_ℓ` for `ℓ < L` and `Y` at `h_L`. -/
private theorem snocLin_apply_uhz (X : Fin L → Matrix d d ℝ) (Y : antisymmetric d) :
    snocLin_uhz (X, Y) = Fin.snoc (α := fun _ => Matrix d d ℝ) X (Y : Matrix d d ℝ) := rfl

/-- Helper (Lemma A.3 (i) and the orthogonal changes of basis): for blocks that are positively
homogeneous row by row under pre-RMSNorm with `ε = 0`, the direction `cobDir θ Z` of a family
`Z = (X_0, …, X_{L−1}, Y)` with `Y` antisymmetric is flat. It is the sum over the hidden states
of the directions of `Z` at one hidden state: `X_ℓ` at `h_ℓ`, `ℓ < L` (Theorem 1), and `Y` at
`h_L` (an orthogonal change of basis). -/
private theorem cobDir_snoc_mem_flat_uhz {A : Arch T d L} (hA : A.χ = rmsNorm 0) {k : ℕ}
    (hf : RowHomogeneous A k) (θ : Params A dIn dOut) (X : Fin L → Matrix d d ℝ)
    (Y : antisymmetric d) :
    cobDir θ (Fin.snoc (α := fun _ => Matrix d d ℝ) X (Y : Matrix d d ℝ)) ∈ flat A 0 θ := by
  -- the family is the sum of its restrictions to one hidden state
  rw [← Finset.univ_sum_single (Fin.snoc (α := fun _ => Matrix d d ℝ) X (Y : Matrix d d ℝ)),
    ← cobDirLin_apply, map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [cobDirLin_apply]
  cases i using Fin.lastCases with
  | last =>
    -- `Y` at `h_L`: antisymmetric at every hidden state
    rw [Fin.snoc_last]
    refine cobDir_mem_flat_skipless_rmsNorm' θ 0 hA _ fun j => ?_
    by_cases hj : j = Fin.last L
    · subst hj
      rw [Pi.single_eq_same]
      exact Y.2
    · rw [Pi.single_eq_of_ne hj, Matrix.transpose_zero, neg_zero]
  | cast j =>
    -- `X_j` at `h_j`, `j < L`: Theorem 1
    rw [Fin.snoc_castSucc]
    exact cobDir_single_mem_flat_skipless_rmsNorm_zero_of_rowHomogeneous hA hf θ j (X j)

/-- Helper: `α ↦ rescaleDirMlp k θ α` is linear (a copy of the private `rescaleDirMlpLin` of
`Dimension/RescalingMlp.lean`). -/
private noncomputable def rescaleDirMlpLin_uhz (k : ℕ)
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) :
    (∀ ℓ, hid ℓ → ℝ) →ₗ[ℝ] Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut where
  toFun := rescaleDirMlp k θ
  map_add' α β := by
    apply Params.ext'
    · simp [rescaleDirMlp]
    · intro ℓ
      ext a i
      simp only [rescaleDirMlp, Pi.add_apply, Params.add_read, Matrix.add_apply, Matrix.of_apply]
      ring
    · intro ℓ
      ext i a
      simp only [rescaleDirMlp, Pi.add_apply, Params.add_write, Matrix.add_apply, Matrix.of_apply]
      ring
    · simp [rescaleDirMlp]
  map_smul' c α := by
    apply Params.ext'
    · simp [rescaleDirMlp]
    · intro ℓ
      ext a i
      simp only [rescaleDirMlp, Pi.smul_apply, Params.smul_read, Matrix.smul_apply,
        Matrix.of_apply, smul_eq_mul, RingHom.id_apply]
      ring
    · intro ℓ
      ext i a
      simp only [rescaleDirMlp, Pi.smul_apply, Params.smul_write, Matrix.smul_apply,
        Matrix.of_apply, smul_eq_mul, RingHom.id_apply]
      ring
    · simp [rescaleDirMlp]

omit [Fintype T] [Fintype dIn] [Fintype dOut] in
/-- Helper (Lemma B.1 for these directions, MLP blocks): if `E` and every write have rank `d` and
no read column is zero, and `cobDir θ Z + c scaleDir θ b + rescaleDirMlp k θ α = 0` with
`b_ℓ = 0` before `h_L`, then `Z_j + c b_j I = 0` at every hidden state `j` and `α = 0`. Along the
network: `E` gives `Z_0`; at block `ℓ`, with `Z_ℓ = 0`, its read gives `α_ℓ = 0` and then its
write gives `Z_{ℓ+1}`. -/
private theorem eq_zero_of_dir_mlp_uhz {k : ℕ}
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d) (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d)
    (hc : ∀ ℓ i, (fun a => θ.read ℓ a i) ≠ 0) (Z : Fin (L + 1) → Matrix d d ℝ) (c : ℝ)
    (b : Fin (L + 1) → ℝ) (hb : ∀ ℓ : Fin L, b ℓ.castSucc = 0) (α : ∀ ℓ, hid ℓ → ℝ)
    (h : cobDir θ Z + c • scaleDir θ b + rescaleDirMlp k θ α = 0) :
    (∀ j, Z j + (c * b j) • (1 : Matrix d d ℝ) = 0) ∧ α = 0 := by
  -- the embedding moves by `E Z_0 + c b_0 E = E (Z_0 + c b_0 I)`
  have h0 : θ.E * (Z 0 + (c * b 0) • (1 : Matrix d d ℝ)) = 0 := by
    have hE0 := congrArg Params.E h
    change θ.E * Z 0 + c • (b 0 • θ.E) + 0 = 0 at hE0
    rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one, ← smul_smul]
    rwa [add_zero] at hE0
  -- block `ℓ`: if `Z_ℓ = 0`, then `α_ℓ = 0` and `Z_{ℓ+1} + c b_{ℓ+1} I = 0`
  have key : ∀ ℓ : Fin L, Z ℓ.castSucc = 0 → α ℓ = 0 ∧
      Z ℓ.succ + (c * b ℓ.succ) • (1 : Matrix d d ℝ) = 0 := by
    intro ℓ hℓ
    -- the read column `c_i` moves by `-Z_ℓ c_i + α_i c_i = α_i c_i` (the scale leaves the reads
    -- alone); an entry `a` with `c_i a ≠ 0` gives `α_i = 0`
    have hα : α ℓ = 0 := by
      funext i
      obtain ⟨a, ha⟩ := Function.ne_iff.mp (hc ℓ i)
      have hr := congrFun (congrFun (congrArg (fun η => η.read ℓ) h) a) i
      change -(Z ℓ.castSucc * θ.read ℓ) a i + c • (0 : Matrix d (hid ℓ) ℝ) a i
        + α ℓ i * θ.read ℓ a i = 0 at hr
      rw [hℓ] at hr
      simp only [Matrix.zero_mul, neg_zero, Matrix.zero_apply, smul_zero, zero_add] at hr
      exact (mul_eq_zero.mp hr).resolve_right ha
    refine ⟨hα, ?_⟩
    -- the write moves by `W Z_{ℓ+1} + c b_{ℓ+1} W` (the rescaling is now `0`), and `W` has
    -- rank `d`
    have hw' := congrArg (fun η => η.write ℓ) h
    change θ.write ℓ * Z ℓ.succ + c • (b ℓ.succ • θ.write ℓ)
      + Matrix.of (fun i a => -((k : ℝ) * α ℓ i) * θ.write ℓ i a) = 0 at hw'
    have h0' : Matrix.of (fun i a => -((k : ℝ) * α ℓ i) * θ.write ℓ i a) = 0 := by
      ext i a
      simp [hα]
    rw [h0', add_zero] at hw'
    apply cancel_left_of_rank_uhz (θ.write ℓ) (hw ℓ)
    rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one, ← smul_smul, Matrix.mul_zero]
    exact hw'
  -- by induction along the network, `Z_j + c b_j I = 0` at every hidden state
  have hZ : ∀ j : Fin (L + 1),
      Z j + (c * b j) • (1 : Matrix d d ℝ) = 0 := by
    intro j
    induction j using Fin.induction with
    | zero => exact cancel_left_of_rank_uhz θ.E hE (h0.trans (Matrix.mul_zero _).symm)
    | succ ℓ ih =>
      refine (key ℓ ?_).2
      rwa [hb ℓ, mul_zero, zero_smul, add_zero] at ih
  -- then `α_ℓ = 0` at every block
  refine ⟨hZ, funext fun ℓ => (key ℓ ?_).1⟩
  have h1 := hZ ℓ.castSucc
  rwa [hb ℓ, mul_zero, zero_smul, add_zero] at h1

/-- **The bound for skipless networks of MLP blocks with a positively homogeneous activation
under pre-RMSNorm with `ε = 0`:** if `E` and the writes have rank `d ≥ 1` and no read column is
zero, `fd ≤ P − L d² − (d(d−1)/2 + 1) − s`, `s` the number of hidden units: `GL(d)` at
`h_0, …, h_{L−1}`, `CO(d)` at `h_L`, and the rescalings of the hidden units. -/
theorem funDim_add_le_skipless_mlp_rescale_rmsNorm_zero [Nonempty d] {k : ℕ}
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d) (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d)
    (hc : ∀ ℓ i, (fun a => θ.read ℓ a i) ≠ 0) :
    funDim (Arch.mlp σ (rmsNorm 0) hid) 0 θ
        + (L * Fintype.card d ^ 2 + (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
          + ∑ ℓ, Fintype.card (hid ℓ))
      ≤ Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) := by
  -- the linear map `(((X, Y), c), α) ↦ cobDir θ Z + c scaleDir θ e_L + rescaleDirMlp k θ α`, with
  -- `Z = (X_0, …, X_{L−1}, Y)` and antisymmetric `Y`: the changes of basis `GL(d)` at
  -- `h_0, …, h_{L−1}` and `CO(d)` at `h_L`, and the rescalings of the hidden units
  let Φ : (((Fin L → Matrix d d ℝ) × antisymmetric d) × ℝ) × (∀ ℓ, hid ℓ → ℝ) →ₗ[ℝ]
      Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut :=
    (((cobDirLin θ).comp snocLin_uhz).coprod
      (LinearMap.toSpanSingleton ℝ _ (scaleDir θ (Pi.single (Fin.last L) 1)))).coprod
      (rescaleDirMlpLin_uhz k θ)
  -- its directions are flat, since the summands are
  have hV : LinearMap.range Φ ≤ flat (Arch.mlp σ (rmsNorm 0) hid) 0 θ := by
    rintro _ ⟨p, rfl⟩
    rw [LinearMap.coprod_apply, LinearMap.coprod_apply]
    refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) (rescaleDirMlp_mem_flat hσ θ 0 p.2)
    · -- the changes of basis: `GL(d)` before `h_L` (Theorem 1), orthogonal at `h_L`
      rw [LinearMap.comp_apply, cobDirLin_apply]
      exact cobDir_snoc_mem_flat_uhz rfl (rowHomogeneous_mlp hσ (rmsNorm 0) hid) θ p.1.1.1 p.1.1.2
    · -- the scale `c` at `h_L`
      rw [LinearMap.toSpanSingleton_apply]
      exact Submodule.smul_mem _ _ (scaleDir_mem_flat_skipless_rmsNorm_zero θ rfl _)
  -- it is injective (Lemma B.1): its kernel is `0`
  have hinj : Function.Injective Φ := by
    refine (injective_iff_map_eq_zero Φ).2 fun p hp => ?_
    obtain ⟨⟨⟨X, Y⟩, c⟩, α⟩ := p
    rw [LinearMap.coprod_apply, LinearMap.coprod_apply] at hp
    have hp' : cobDir θ (Fin.snoc (α := fun _ => Matrix d d ℝ) X (Y : Matrix d d ℝ))
        + c • scaleDir θ (Pi.single (Fin.last L) 1) + rescaleDirMlp k θ α = 0 := hp
    -- along the network, `Z_j + c δ_{jL} I = 0` and `α = 0`
    obtain ⟨hZ, rfl⟩ := eq_zero_of_dir_mlp_uhz θ hE hw hc _ c _
      (fun ℓ => Pi.single_eq_of_ne (Fin.castSucc_ne_last ℓ) _) α hp'
    -- before `h_L`: `X_ℓ = 0`
    have hX : X = 0 := funext fun ℓ => by
      have h1 := hZ ℓ.castSucc
      rwa [Fin.snoc_castSucc, Pi.single_eq_of_ne (Fin.castSucc_ne_last ℓ), mul_zero, zero_smul,
        add_zero] at h1
    -- at `h_L`: `Y + c I = 0` with `Y` antisymmetric, so `Y = 0` and `c = 0`
    have h2 := hZ (Fin.last L)
    rw [Fin.snoc_last, Pi.single_eq_same, mul_one] at h2
    obtain ⟨hY, hc0⟩ := antisymm_add_smul_one_eq_zero_uhz Y.2 h2
    obtain rfl : Y = 0 := Subtype.ext hY
    subst hX hc0
    rfl
  -- the domain has dimension `L d² + (d (d - 1) / 2 + 1) + s`
  have hdim : Module.finrank ℝ
      ((((Fin L → Matrix d d ℝ) × antisymmetric d) × ℝ) × (∀ ℓ, hid ℓ → ℝ)) =
      L * Fintype.card d ^ 2 + (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
        + ∑ ℓ, Fintype.card (hid ℓ) := by
    rw [Module.finrank_prod, Module.finrank_prod, Module.finrank_prod, finrank_antisymmetric,
      Module.finrank_self, Module.finrank_pi_fintype, Module.finrank_pi_fintype]
    simp only [Module.finrank_matrix, Module.finrank_self, Module.finrank_fintype_fun_eq_card,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    ring
  have h := funDim_add_finrank_le_of_le_flat' θ _ hV
  rwa [LinearMap.finrank_range_of_inj hinj, hdim] at h

/-- Helper: `α ↦ rescaleDir θ α` is linear (a copy of the private `rescaleDirLinValue` of
`Dimension/RescalingGate.lean`). -/
private noncomputable def rescaleDirLin_uhz
    (θ : Params (Arch.gated (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) :
    (∀ ℓ, hid ℓ → ℝ) →ₗ[ℝ] Params (Arch.gated (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut where
  toFun := rescaleDir θ
  map_add' α β := by
    apply Params.ext'
    · simp [rescaleDir]
    · intro ℓ
      ext a j
      cases j with
      | inl i => simp [rescaleDir]
      | inr i =>
        simp only [rescaleDir, Pi.add_apply, Params.add_read, Matrix.add_apply, Matrix.of_apply,
          Sum.elim_inr]
        ring
    · intro ℓ
      ext i a
      simp [rescaleDir, add_mul]
    · simp [rescaleDir]
  map_smul' c α := by
    apply Params.ext'
    · simp [rescaleDir]
    · intro ℓ
      ext a j
      cases j <;> simp [rescaleDir, mul_assoc]
    · intro ℓ
      ext i a
      simp [rescaleDir, mul_assoc]
    · simp [rescaleDir]

/-- Helper: `β ↦ rescaleDirGate k θ β` is linear (a copy of the private `rescaleDirGateLin` of
`Dimension/RescalingGate.lean`). -/
private noncomputable def rescaleDirGateLin_uhz (k : ℕ)
    (θ : Params (Arch.gated (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) :
    (∀ ℓ, hid ℓ → ℝ) →ₗ[ℝ] Params (Arch.gated (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut where
  toFun := rescaleDirGate k θ
  map_add' α β := by
    apply Params.ext'
    · simp [rescaleDirGate]
    · intro ℓ
      ext a j
      cases j with
      | inl i =>
        simp only [rescaleDirGate, Pi.add_apply, Params.add_read, Matrix.add_apply,
          Matrix.of_apply, Sum.elim_inl]
        ring
      | inr i => simp [rescaleDirGate]
    · intro ℓ
      ext i a
      simp only [rescaleDirGate, Pi.add_apply, Params.add_write, Matrix.add_apply,
        Matrix.of_apply]
      ring
    · simp [rescaleDirGate]
  map_smul' c α := by
    apply Params.ext'
    · simp [rescaleDirGate]
    · intro ℓ
      ext a j
      cases j with
      | inl i =>
        simp only [rescaleDirGate, Pi.smul_apply, Params.smul_read, Matrix.smul_apply,
          Matrix.of_apply, Sum.elim_inl, smul_eq_mul, RingHom.id_apply]
        ring
      | inr i => simp [rescaleDirGate]
    · intro ℓ
      ext i a
      simp only [rescaleDirGate, Pi.smul_apply, Params.smul_write, Matrix.smul_apply,
        Matrix.of_apply, smul_eq_mul, RingHom.id_apply]
      ring
    · simp [rescaleDirGate]

omit [Fintype T] [Fintype dIn] [Fintype dOut] in
/-- Helper (Lemma B.1 for these directions, gated blocks): if `E` and every write have rank `d`
and no value column and no gate column of a read is zero, and
`cobDir θ Z + c scaleDir θ b + rescaleDir θ α + rescaleDirGate k θ β = 0` with `b_ℓ = 0` before
`h_L`, then `Z_j + c b_j I = 0` at every hidden state `j`, `α = 0` and `β = 0`. Along the
network: `E` gives `Z_0`; at block `ℓ`, with `Z_ℓ = 0`, the gate columns of its read give
`β_ℓ = 0`, the value columns `α_ℓ = 0`, and then its write gives `Z_{ℓ+1}`. -/
private theorem eq_zero_of_dir_gated_uhz {k : ℕ}
    (θ : Params (Arch.gated (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d) (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d)
    (hv : ∀ ℓ i, (fun a => θ.read ℓ a (Sum.inr i)) ≠ 0)
    (hg : ∀ ℓ i, (fun a => θ.read ℓ a (Sum.inl i)) ≠ 0) (Z : Fin (L + 1) → Matrix d d ℝ)
    (c : ℝ) (b : Fin (L + 1) → ℝ) (hb : ∀ ℓ : Fin L, b ℓ.castSucc = 0) (α β : ∀ ℓ, hid ℓ → ℝ)
    (h : cobDir θ Z + c • scaleDir θ b + (rescaleDir θ α + rescaleDirGate k θ β) = 0) :
    (∀ j, Z j + (c * b j) • (1 : Matrix d d ℝ) = 0) ∧ α = 0 ∧ β = 0 := by
  -- the embedding moves by `E Z_0 + c b_0 E = E (Z_0 + c b_0 I)`
  have h0 : θ.E * (Z 0 + (c * b 0) • (1 : Matrix d d ℝ)) = 0 := by
    have hE0 := congrArg Params.E h
    change θ.E * Z 0 + c • (b 0 • θ.E) + (0 + 0) = 0 at hE0
    rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one, ← smul_smul]
    rwa [add_zero, add_zero] at hE0
  -- block `ℓ`: if `Z_ℓ = 0`, then `α_ℓ = 0`, `β_ℓ = 0` and `Z_{ℓ+1} + c b_{ℓ+1} I = 0`
  have key : ∀ ℓ : Fin L, Z ℓ.castSucc = 0 → α ℓ = 0 ∧ β ℓ = 0 ∧
      Z ℓ.succ + (c * b ℓ.succ) • (1 : Matrix d d ℝ) = 0 := by
    intro ℓ hℓ
    -- the gate column `g_i` moves by `-Z_ℓ g_i + β_i g_i = β_i g_i`; an entry `a` with
    -- `g_i a ≠ 0` gives `β_i = 0`
    have hβ : β ℓ = 0 := by
      funext i
      obtain ⟨a, ha⟩ := Function.ne_iff.mp (hg ℓ i)
      have hr := congrFun (congrFun (congrArg (fun η => η.read ℓ) h) a) (Sum.inl i)
      change -(Z ℓ.castSucc * θ.read ℓ) a (Sum.inl i)
        + c • (0 : Matrix d (hid ℓ ⊕ hid ℓ) ℝ) a (Sum.inl i)
        + (0 + β ℓ i * θ.read ℓ a (Sum.inl i)) = 0 at hr
      rw [hℓ] at hr
      simp only [Matrix.zero_mul, neg_zero, Matrix.zero_apply, smul_zero, zero_add] at hr
      exact (mul_eq_zero.mp hr).resolve_right ha
    -- the value column `e_i` moves by `-Z_ℓ e_i - α_i e_i = -α_i e_i`; an entry `a` with
    -- `e_i a ≠ 0` gives `α_i = 0`
    have hα : α ℓ = 0 := by
      funext i
      obtain ⟨a, ha⟩ := Function.ne_iff.mp (hv ℓ i)
      have hr := congrFun (congrFun (congrArg (fun η => η.read ℓ) h) a) (Sum.inr i)
      change -(Z ℓ.castSucc * θ.read ℓ) a (Sum.inr i)
        + c • (0 : Matrix d (hid ℓ ⊕ hid ℓ) ℝ) a (Sum.inr i)
        + (-(α ℓ i) * θ.read ℓ a (Sum.inr i) + 0) = 0 at hr
      rw [hℓ] at hr
      simp only [Matrix.zero_mul, neg_zero, Matrix.zero_apply, smul_zero, zero_add,
        add_zero] at hr
      exact neg_eq_zero.mp ((mul_eq_zero.mp hr).resolve_right ha)
    refine ⟨hα, hβ, ?_⟩
    -- the write moves by `W Z_{ℓ+1} + c b_{ℓ+1} W` (the rescalings are now `0`), and `W` has
    -- rank `d`
    have hw' := congrArg (fun η => η.write ℓ) h
    change θ.write ℓ * Z ℓ.succ + c • (b ℓ.succ • θ.write ℓ)
      + (Matrix.of (fun i a => α ℓ i * θ.write ℓ i a)
        + Matrix.of (fun i a => -((k : ℝ) * β ℓ i) * θ.write ℓ i a)) = 0 at hw'
    have h0' : Matrix.of (fun i a => α ℓ i * θ.write ℓ i a)
        + Matrix.of (fun i a => -((k : ℝ) * β ℓ i) * θ.write ℓ i a) = 0 := by
      ext i a
      simp [hα, hβ]
    rw [h0', add_zero] at hw'
    apply cancel_left_of_rank_uhz (θ.write ℓ) (hw ℓ)
    rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one, ← smul_smul, Matrix.mul_zero]
    exact hw'
  -- by induction along the network, `Z_j + c b_j I = 0` at every hidden state
  have hZ : ∀ j : Fin (L + 1),
      Z j + (c * b j) • (1 : Matrix d d ℝ) = 0 := by
    intro j
    induction j using Fin.induction with
    | zero => exact cancel_left_of_rank_uhz θ.E hE (h0.trans (Matrix.mul_zero _).symm)
    | succ ℓ ih =>
      refine (key ℓ ?_).2.2
      rwa [hb ℓ, mul_zero, zero_smul, add_zero] at ih
  -- then `α_ℓ = 0` and `β_ℓ = 0` at every block
  have hZc : ∀ ℓ : Fin L, Z ℓ.castSucc = 0 := fun ℓ => by
    have h1 := hZ ℓ.castSucc
    rwa [hb ℓ, mul_zero, zero_smul, add_zero] at h1
  exact ⟨hZ, funext fun ℓ => (key ℓ (hZc ℓ)).1, funext fun ℓ => (key ℓ (hZc ℓ)).2.1⟩

/-- **The bound for skipless networks of gated blocks with a positively homogeneous gate under
pre-RMSNorm with `ε = 0`:** if `E` and the writes have rank `d ≥ 1` and no value column and no
gate column of a read is zero, `fd ≤ P − L d² − (d(d−1)/2 + 1) − s`, `s` twice the number of
hidden units. -/
theorem funDim_add_le_skipless_gated_gate_rmsNorm_zero [Nonempty d] {k : ℕ}
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (θ : Params (Arch.gated (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d) (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d)
    (hv : ∀ ℓ i, (fun a => θ.read ℓ a (Sum.inr i)) ≠ 0)
    (hg : ∀ ℓ i, (fun a => θ.read ℓ a (Sum.inl i)) ≠ 0) :
    funDim (Arch.gated σ (rmsNorm 0) hid) 0 θ
        + (L * Fintype.card d ^ 2 + (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
          + 2 * ∑ ℓ, Fintype.card (hid ℓ))
      ≤ Module.finrank ℝ
          (Params (Arch.gated (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) := by
  -- the linear map `(((X, Y), c), (α, β)) ↦ cobDir θ Z + c scaleDir θ e_L + rescaleDir θ α
  -- + rescaleDirGate k θ β`, with `Z = (X_0, …, X_{L−1}, Y)` and antisymmetric `Y`: the changes
  -- of basis `GL(d)` at `h_0, …, h_{L−1}` and `CO(d)` at `h_L`, the rescalings of the values and
  -- of the gates
  let Φ : (((Fin L → Matrix d d ℝ) × antisymmetric d) × ℝ)
        × ((∀ ℓ, hid ℓ → ℝ) × (∀ ℓ, hid ℓ → ℝ)) →ₗ[ℝ]
      Params (Arch.gated (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut :=
    (((cobDirLin θ).comp snocLin_uhz).coprod
      (LinearMap.toSpanSingleton ℝ _ (scaleDir θ (Pi.single (Fin.last L) 1)))).coprod
      ((rescaleDirLin_uhz θ).coprod (rescaleDirGateLin_uhz k θ))
  -- its directions are flat, since the summands are
  have hV : LinearMap.range Φ ≤ flat (Arch.gated σ (rmsNorm 0) hid) 0 θ := by
    rintro _ ⟨p, rfl⟩
    rw [LinearMap.coprod_apply, LinearMap.coprod_apply, LinearMap.coprod_apply]
    refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_)
      (Submodule.add_mem _ (rescaleDir_mem_flat' θ 0 p.2.1)
        (rescaleDirGate_mem_flat hσ θ 0 p.2.2))
    · -- the changes of basis: `GL(d)` before `h_L` (Theorem 1), orthogonal at `h_L`
      rw [LinearMap.comp_apply, cobDirLin_apply]
      exact cobDir_snoc_mem_flat_uhz rfl (rowHomogeneous_gated hσ (rmsNorm 0) hid) θ p.1.1.1
        p.1.1.2
    · -- the scale `c` at `h_L`
      rw [LinearMap.toSpanSingleton_apply]
      exact Submodule.smul_mem _ _ (scaleDir_mem_flat_skipless_rmsNorm_zero θ rfl _)
  -- it is injective (Lemma B.1): its kernel is `0`
  have hinj : Function.Injective Φ := by
    refine (injective_iff_map_eq_zero Φ).2 fun p hp => ?_
    obtain ⟨⟨⟨X, Y⟩, c⟩, α, β⟩ := p
    rw [LinearMap.coprod_apply, LinearMap.coprod_apply, LinearMap.coprod_apply] at hp
    have hp' : cobDir θ (Fin.snoc (α := fun _ => Matrix d d ℝ) X (Y : Matrix d d ℝ))
        + c • scaleDir θ (Pi.single (Fin.last L) 1)
        + (rescaleDir θ α + rescaleDirGate k θ β) = 0 := hp
    -- along the network, `Z_j + c δ_{jL} I = 0`, `α = 0` and `β = 0`
    obtain ⟨hZ, rfl, rfl⟩ := eq_zero_of_dir_gated_uhz θ hE hw hv hg _ c _
      (fun ℓ => Pi.single_eq_of_ne (Fin.castSucc_ne_last ℓ) _) α β hp'
    -- before `h_L`: `X_ℓ = 0`
    have hX : X = 0 := funext fun ℓ => by
      have h1 := hZ ℓ.castSucc
      rwa [Fin.snoc_castSucc, Pi.single_eq_of_ne (Fin.castSucc_ne_last ℓ), mul_zero, zero_smul,
        add_zero] at h1
    -- at `h_L`: `Y + c I = 0` with `Y` antisymmetric, so `Y = 0` and `c = 0`
    have h2 := hZ (Fin.last L)
    rw [Fin.snoc_last, Pi.single_eq_same, mul_one] at h2
    obtain ⟨hY, hc0⟩ := antisymm_add_smul_one_eq_zero_uhz Y.2 h2
    obtain rfl : Y = 0 := Subtype.ext hY
    subst hX hc0
    rfl
  -- the domain has dimension `L d² + (d (d - 1) / 2 + 1) + 2 s`
  have hdim : Module.finrank ℝ
      ((((Fin L → Matrix d d ℝ) × antisymmetric d) × ℝ)
        × ((∀ ℓ, hid ℓ → ℝ) × (∀ ℓ, hid ℓ → ℝ))) =
      L * Fintype.card d ^ 2 + (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
        + 2 * ∑ ℓ, Fintype.card (hid ℓ) := by
    rw [Module.finrank_prod, Module.finrank_prod, Module.finrank_prod, Module.finrank_prod,
      finrank_antisymmetric, Module.finrank_self, Module.finrank_pi_fintype,
      Module.finrank_pi_fintype]
    simp only [Module.finrank_matrix, Module.finrank_self, Module.finrank_fintype_fun_eq_card,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    ring
  have h := funDim_add_finrank_le_of_le_flat' θ _ hV
  rwa [LinearMap.finrank_range_of_inj hinj, hdim] at h

/-- The bound of `funDim_add_le_skipless_mlp_rescale_rmsNorm_zero` for ReLU blocks of width at
least `d` at almost every parameter, `d_in ≥ d ≥ 1`. -/
theorem ae_funDim_add_le_skipless_relu_rmsNorm_zero [Nonempty d]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, funDim (Arch.mlp relu (rmsNorm 0) hid) 0 θ
        + (L * Fintype.card d ^ 2 + (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
          + ∑ ℓ, Fintype.card (hid ℓ))
      ≤ Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut) := by
  -- the pointwise bound holds wherever `E` and the writes have rank `d` and no column of a read
  -- vanishes
  filter_upwards [ae_rank_E_write μ hdIn hhid, ae_read_col_ne_zero μ] with θ h1 h2
  exact funDim_add_le_skipless_mlp_rescale_rmsNorm_zero relu_homogeneous θ h1.1 h1.2 h2

/-- The same for ReLU² blocks. -/
theorem ae_funDim_add_le_skipless_reluSq_rmsNorm_zero [Nonempty d]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) reluSq (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, funDim (Arch.mlp reluSq (rmsNorm 0) hid) 0 θ
        + (L * Fintype.card d ^ 2 + (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
          + ∑ ℓ, Fintype.card (hid ℓ))
      ≤ Module.finrank ℝ
          (Params (Arch.mlp (T := T) (d := d) reluSq (rmsNorm 0) hid) dIn dOut) := by
  filter_upwards [ae_rank_E_write μ hdIn hhid, ae_read_col_ne_zero μ] with θ h1 h2
  exact funDim_add_le_skipless_mlp_rescale_rmsNorm_zero reluSq_homogeneous θ h1.1 h1.2 h2

/-- The bound of `funDim_add_le_skipless_gated_gate_rmsNorm_zero` for ReGLU blocks of width at
least `d` at almost every parameter, `d_in ≥ d ≥ 1`. -/
theorem ae_funDim_add_le_skipless_reglu_rmsNorm_zero [Nonempty d]
    (μ : Measure (Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, funDim (Arch.gated relu (rmsNorm 0) hid) 0 θ
        + (L * Fintype.card d ^ 2 + (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
          + 2 * ∑ ℓ, Fintype.card (hid ℓ))
      ≤ Module.finrank ℝ
          (Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut) := by
  -- the pointwise bound holds wherever `E` and the writes have rank `d` and no value column and
  -- no gate column of a read vanishes
  filter_upwards [ae_rank_E_write μ hdIn hhid, ae_value_ne_zero μ, ae_gate_ne_zero μ]
    with θ h1 h2 h3
  exact funDim_add_le_skipless_gated_gate_rmsNorm_zero relu_homogeneous θ h1.1 h1.2 h2 h3

/-- Helper (the arithmetic of Theorem A.12 (iii), last sentence): for `n ≥ 2` and `m ≥ 1`,
`q + 1 < n²` with `q = n (n − 1) / 2`, so `(m + 1) (q + 1) < m n² + (q + 1)`, and a bound
`F + (m n² + (q + 1) + s) ≤ P` gives `F + ((m + 1) (q + 1) + s) < P`. -/
private theorem add_lt_of_add_le_uhz {F P n m s : ℕ} (hd : 2 ≤ n) (hm : 1 ≤ m)
    (h : F + (m * n ^ 2 + (n * (n - 1) / 2 + 1) + s) ≤ P) :
    F + ((m + 1) * (n * (n - 1) / 2 + 1) + s) < P := by
  -- `q + 1 < n²`: `2 q ≤ n (n − 1) ≤ n²` and `n² ≥ 4`
  have hq : n * (n - 1) / 2 + 1 < n ^ 2 := by
    have h1 : n * (n - 1) ≤ n ^ 2 := by
      rw [sq]
      exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    have h2 : 2 * 2 ≤ n ^ 2 := by
      rw [sq]
      exact Nat.mul_le_mul hd hd
    omega
  -- so `m (q + 1) < m n²`, and `(m + 1) (q + 1) = m (q + 1) + (q + 1)`
  have h3 : m * (n * (n - 1) / 2 + 1) < m * n ^ 2 := Nat.mul_lt_mul_of_pos_left hq (by omega)
  have h4 : (m + 1) * (n * (n - 1) / 2 + 1) = m * (n * (n - 1) / 2 + 1) + (n * (n - 1) / 2 + 1) :=
    by ring
  omega

/-- **Theorem A.12 (iii) of the skips paper, last sentence, for ReLU blocks:** for `ε = 0`,
`d_in ≥ d ≥ 2`, `L ≥ 1` blocks of width at least `d`, at almost every parameter the functional
dimension of the skipless network is strictly below the bound `P − (L + 1) (d(d−1)/2 + 1) − s`
of the changes of basis in `CO(d)`: the skipless network does not satisfy the equality
condition. -/
theorem ae_funDim_add_lt_skipless_relu_rmsNorm_zero
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hL : 1 ≤ L)
    (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, funDim (Arch.mlp relu (rmsNorm 0) hid) 0 θ
        + ((L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
          + ∑ ℓ, Fintype.card (hid ℓ))
      < Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut) := by
  have : Nonempty d := Fintype.card_pos_iff.mp (by omega)
  -- the bound with `GL(d)` at `h_0, …, h_{L−1}`, and `L d² > L (d(d−1)/2 + 1)`
  filter_upwards [ae_funDim_add_le_skipless_relu_rmsNorm_zero μ hdIn hhid] with θ h
  exact add_lt_of_add_le_uhz hd hL h

/-- **Theorem A.12 (iii) of the skips paper, last sentence, for ReLU² blocks.** -/
theorem ae_funDim_add_lt_skipless_reluSq_rmsNorm_zero
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) reluSq (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hL : 1 ≤ L)
    (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, funDim (Arch.mlp reluSq (rmsNorm 0) hid) 0 θ
        + ((L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
          + ∑ ℓ, Fintype.card (hid ℓ))
      < Module.finrank ℝ
          (Params (Arch.mlp (T := T) (d := d) reluSq (rmsNorm 0) hid) dIn dOut) := by
  have : Nonempty d := Fintype.card_pos_iff.mp (by omega)
  filter_upwards [ae_funDim_add_le_skipless_reluSq_rmsNorm_zero μ hdIn hhid] with θ h
  exact add_lt_of_add_le_uhz hd hL h

/-- **Theorem A.12 (iii) of the skips paper, last sentence, for ReGLU blocks.** -/
theorem ae_funDim_add_lt_skipless_reglu_rmsNorm_zero
    (μ : Measure (Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hL : 1 ≤ L)
    (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, funDim (Arch.gated relu (rmsNorm 0) hid) 0 θ
        + ((L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
          + 2 * ∑ ℓ, Fintype.card (hid ℓ))
      < Module.finrank ℝ
          (Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut) := by
  have : Nonempty d := Fintype.card_pos_iff.mp (by omega)
  filter_upwards [ae_funDim_add_le_skipless_reglu_rmsNorm_zero μ hdIn hhid] with θ h
  exact add_lt_of_add_le_uhz hd hL h

end Skips
