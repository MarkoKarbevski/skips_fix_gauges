import SkipsLean.Dimension.RescalingMlp

/-!
# A hidden unit that is inactive at every input: the bound on the functional dimension

Paper (dimension paper): Appendix E, "Inactive hidden units: where the count fails",
Proposition E.1, the part "The rank" of its proof, for ReLU and ReLU² blocks.

"Proposition E.1 (Inactive hidden units). Consider networks of `L ≥ 2` ReLU, ReLU² or ReGLU blocks
without normalization, each with more than `d_model` hidden units. There is a nonempty open set of
weights on which a hidden unit of block 2 is inactive at every input. At almost every point of this
set the functional dimension is at most `P − (L+1) d_model² − s − (2 d_model − 1)`, and at most
`P − (L+1) d_model² − s − (3 d_model − 2)` for ReGLU blocks. So these networks do not satisfy the
equality condition."

"The rank. On this open set of weights, take a batch of inputs at which no hidden unit sits at its
kink. The columns of the Jacobian that belong to the weights of the inactive hidden unit vanish:
`2 d_model` columns, or `3 d_model` for ReGLU. The other columns form the Jacobian of the network
without this hidden unit, which computes the same function. That network has `P − 2 d_model`
parameters […], its blocks have at least `d_model` hidden units, and its symmetries have the
dimension `(L+1) d_model² + s − 1` […], since the inactive hidden unit had one rescaling […]. By
Lemma B.1 they move generic parameters in as many independent directions, which lie in the kernel
of the Jacobian."

Stated here, for a skipless network of MLP blocks without normalization whose activation is
positively homogeneous of degree `k` and vanishes on `z ≤ 0` (ReLU, ReLU²), and for a hidden unit
`j` of any block `m`:

* `UnitInactive θ m j`: the hidden unit reads a number `≤ 0` at every token of every input.
* `unitDir m j δr δa`: the direction that moves only the read column and the write row of the
  hidden unit. If the unit is inactive at every input at all parameters near `θ`, these `2d`
  directions are flat at `θ` (`unitDir_mem_flat`).
* The bound (`funDim_add_le_of_eventually_unitInactive`): if moreover `E` and the writes have rank
  `d`, the write of block `m` without the row of the unit still has rank `d`, and no read column
  vanishes, then `fd(θ) ≤ P − (L+1) d² − s − (2d − 1)`, with `s` the number of hidden units. The
  flat directions are the changes of basis, the rescalings of the other hidden units, and the `2d`
  directions of the inactive unit.

In Lean the Jacobian on a batch is taken at all inputs, also where a hidden unit sits at its kink
(see the note on ReLU in `STATEMENTS.md`), so the bound is on a number that is at least the paper's
functional dimension. The open set of weights and the statement of the proposition are in
`Depth/InactiveUnitRelu.lean`; ReGLU blocks in `Depth/InactiveGate.lean`.
-/

namespace Skips

open Matrix Filter Topology
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {σ : ℝ → ℝ} {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)] [∀ ℓ, DecidableEq (hid ℓ)]

/-- Hidden unit `j` of block `m` of a skipless network of MLP blocks without normalization is
inactive at every input at `θ`: it reads a number `≤ 0` at every token of every input. -/
def UnitInactive (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) (m : Fin L)
    (j : hid m) : Prop :=
  ∀ (x : Matrix T dIn ℝ) (t : T),
    (hidden (Arch.mlp σ id hid) 0 θ x m.castSucc * θ.read m) t j ≤ 0

/-- The direction that moves only hidden unit `j` of block `m`: its read column by `δr` and its
write row by `δa`. -/
def unitDir {χ : Matrix T d ℝ → Matrix T d ℝ} (m : Fin L) (j : hid m) (δr δa : d → ℝ) :
    Params (Arch.mlp (T := T) (d := d) σ χ hid) dIn dOut where
  E := 0
  read := Function.update (fun _ => 0) m
    (Matrix.of fun (a : d) (i : hid m) => if i = j then δr a else 0)
  write := Function.update (fun _ => 0) m
    (Matrix.of fun (i : hid m) (a : d) => if i = j then δa a else 0)
  D := 0

omit [Fintype T] [DecidableEq d] [Fintype dOut] in
/-- Helper: two parameters that differ only in the read column and the write row of hidden unit
`j` of block `m`, at both of which this unit is inactive at every input, have the same hidden
states at every input. -/
private theorem hidden_eq_of_unitInactive_iu (hσ0 : ∀ z : ℝ, z ≤ 0 → σ z = 0)
    (θ θ' : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) (m : Fin L) (j : hid m)
    (h1 : UnitInactive θ m j) (h2 : UnitInactive θ' m j) (hE : θ'.E = θ.E)
    (hr : ∀ ℓ, ℓ ≠ m → θ'.read ℓ = θ.read ℓ) (hw : ∀ ℓ, ℓ ≠ m → θ'.write ℓ = θ.write ℓ)
    (hrm : ∀ a i, i ≠ j → θ'.read m a i = θ.read m a i)
    (hwm : ∀ i a, i ≠ j → θ'.write m i a = θ.write m i a)
    (x : Matrix T dIn ℝ) (ℓ : Fin (L + 1)) :
    hidden (Arch.mlp σ id hid) 0 θ' x ℓ = hidden (Arch.mlp σ id hid) 0 θ x ℓ := by
  induction ℓ using Fin.induction with
  | zero => rw [hidden_zero, hidden_zero, hE]
  | succ ℓ ih =>
    -- the stream term is the same; compare the outputs of block `ℓ`
    rw [hidden_succ, hidden_succ, ih]
    congr 1
    show (hidden (Arch.mlp σ id hid) 0 θ x ℓ.castSucc * θ'.read ℓ).map σ * θ'.write ℓ =
      (hidden (Arch.mlp σ id hid) 0 θ x ℓ.castSucc * θ.read ℓ).map σ * θ.write ℓ
    by_cases hℓ : ℓ = m
    · -- block `m`: the terms of the hidden units `i ≠ j` agree, the term of `j` is `0`
      subst hℓ
      ext t a
      rw [Matrix.mul_apply, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Matrix.map_apply, Matrix.map_apply]
      by_cases hi : i = j
      · subst hi
        have e1 := h1 x t
        have e2 := h2 x t
        rw [ih] at e2
        rw [hσ0 _ e1, hσ0 _ e2, zero_mul, zero_mul]
      · have hu : (hidden (Arch.mlp σ id hid) 0 θ x ℓ.castSucc * θ'.read ℓ) t i =
            (hidden (Arch.mlp σ id hid) 0 θ x ℓ.castSucc * θ.read ℓ) t i := by
          rw [Matrix.mul_apply, Matrix.mul_apply]
          exact Finset.sum_congr rfl fun b _ => by rw [hrm b i hi]
        rw [hu, hwm i a hi]
    · -- another block: nothing changed
      rw [hr ℓ hℓ, hw ℓ hℓ]

omit [Fintype T] [DecidableEq d] in
/-- Helper: the line `τ ↦ θ + τ η` passes through `θ` at `τ = 0` with velocity `η`. -/
private theorem hasDerivAt_line_iu {A : Arch T d L} (θ η : Params A dIn dOut) :
    HasDerivAt (fun τ : ℝ => θ + τ • η) η 0 := by
  have h := ((hasDerivAt_id (0 : ℝ)).smul_const η).const_add θ
  rw [one_smul] at h
  exact h

omit [DecidableEq d] in
/-- **Proof of Proposition E.1, "The columns of the Jacobian that belong to the weights of the
inactive hidden unit vanish":** if `σ` vanishes on `z ≤ 0` and hidden unit `j` of block `m` is
inactive at every input at all parameters near `θ`, then every direction that moves only the read
column and the write row of this hidden unit is flat at `θ`. -/
theorem unitDir_mem_flat (hσ0 : ∀ z : ℝ, z ≤ 0 → σ z = 0)
    (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) (m : Fin L) (j : hid m)
    (hθ : ∀ᶠ θ' in 𝓝 θ, UnitInactive θ' m j) (δr δa : d → ℝ) :
    unitDir m j δr δa ∈ flat (Arch.mlp σ id hid) 0 θ := by
  set η : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut := unitDir m j δr δa
  -- the line `τ ↦ θ + τ η` passes through `θ` with velocity `η`
  have hline := hasDerivAt_line_iu θ η
  have h0 : θ + (0 : ℝ) • η = θ := by rw [zero_smul, add_zero]
  -- near `τ = 0` the hidden unit is inactive at every input along the line
  have hnear : ∀ᶠ τ in 𝓝 (0 : ℝ), UnitInactive (θ + τ • η) m j := by
    have ht := hline.continuousAt.tendsto
    rw [h0] at ht
    exact ht.eventually hθ
  refine mem_flat_of_hasDerivAt' θ (fun τ => θ + τ • η) η hline h0
    (hnear.mono fun τ hτ x => ?_)
  -- the line moves only the read column and the write row of the unit, so the hidden states, and
  -- then the outputs, are those of `θ`
  have hh := hidden_eq_of_unitInactive_iu hσ0 θ (θ + τ • η) m j hθ.self_of_nhds hτ
    (by simp only [η, unitDir, Params.add_E, Params.smul_E, smul_zero, add_zero])
    (fun ℓ hℓ => by
      simp only [η, unitDir, Params.add_read, Params.smul_read, Function.update_of_ne hℓ,
        smul_zero, add_zero])
    (fun ℓ hℓ => by
      simp only [η, unitDir, Params.add_write, Params.smul_write, Function.update_of_ne hℓ,
        smul_zero, add_zero])
    (fun a i hi => by
      simp only [η, unitDir, Params.add_read, Params.smul_read, Function.update_self, smul_of,
        Matrix.add_apply, of_apply, Pi.smul_apply, hi, ↓reduceIte, smul_eq_mul, mul_zero,
        add_zero])
    (fun i a hi => by
      simp only [η, unitDir, Params.add_write, Params.smul_write, Function.update_self, smul_of,
        Matrix.add_apply, of_apply, Pi.smul_apply, hi, ↓reduceIte, smul_eq_mul, mul_zero,
        add_zero])
    x (Fin.last L)
  show (Arch.mlp σ id hid).χ (hidden _ 0 (θ + τ • η) x (Fin.last L)) * (θ + τ • η).D =
    (Arch.mlp σ id hid).χ (hidden _ 0 θ x (Fin.last L)) * θ.D
  rw [hh]
  simp only [η, unitDir, Params.add_D, Params.smul_D, smul_zero, add_zero]

omit [Fintype T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (as the private `cancel_left_of_rank` of `RescalingMlp.lean`): a matrix `M` of rank
equal to its number of columns cancels on the left, `M X = M Y → X = Y`. -/
private theorem cancel_left_of_rank_iu {m n k : Type*} [Fintype n] (M : Matrix m n ℝ)
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

omit [DecidableEq d] [∀ ℓ, DecidableEq (hid ℓ)] in
/-- Helper (as the private `rescaleDirMlpLin` of `RescalingMlp.lean`): `α ↦ rescaleDirMlp k θ α`
is linear. -/
private noncomputable def rescaleDirMlpLin_iu (k : ℕ)
    (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) :
    (∀ ℓ, hid ℓ → ℝ) →ₗ[ℝ] Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut where
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

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the read of `unitDir` at a block other than `m` is `0`. -/
private theorem unitDir_read_ne_iu {χ : Matrix T d ℝ → Matrix T d ℝ} (m : Fin L) (j : hid m)
    (δr δa : d → ℝ) {ℓ : Fin L} (hℓ : ℓ ≠ m) :
    (unitDir (σ := σ) (χ := χ) (dIn := dIn) (dOut := dOut) m j δr δa).read ℓ = 0 := by
  simp only [unitDir]
  rw [Function.update_of_ne hℓ]

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the write of `unitDir` at a block other than `m` is `0`. -/
private theorem unitDir_write_ne_iu {χ : Matrix T d ℝ → Matrix T d ℝ} (m : Fin L) (j : hid m)
    (δr δa : d → ℝ) {ℓ : Fin L} (hℓ : ℓ ≠ m) :
    (unitDir (σ := σ) (χ := χ) (dIn := dIn) (dOut := dOut) m j δr δa).write ℓ = 0 := by
  simp only [unitDir]
  rw [Function.update_of_ne hℓ]

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the read of `unitDir` at block `m`. -/
private theorem unitDir_read_self_iu {χ : Matrix T d ℝ → Matrix T d ℝ} (m : Fin L) (j : hid m)
    (δr δa : d → ℝ) (a : d) (i : hid m) :
    (unitDir (σ := σ) (χ := χ) (dIn := dIn) (dOut := dOut) m j δr δa).read m a i =
      if i = j then δr a else 0 := by
  simp only [unitDir, Function.update_self, Matrix.of_apply]

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the write of `unitDir` at block `m`. -/
private theorem unitDir_write_self_iu {χ : Matrix T d ℝ → Matrix T d ℝ} (m : Fin L) (j : hid m)
    (δr δa : d → ℝ) (i : hid m) (a : d) :
    (unitDir (σ := σ) (χ := χ) (dIn := dIn) (dOut := dOut) m j δr δa).write m i a =
      if i = j then δa a else 0 := by
  simp only [unitDir, Function.update_self, Matrix.of_apply]

omit [Fintype T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: `(δr, δa) ↦ unitDir m j δr δa` is linear. -/
private noncomputable def unitDirLin_iu (m : Fin L) (j : hid m) :
    ((d → ℝ) × (d → ℝ)) →ₗ[ℝ] Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut where
  toFun p := unitDir m j p.1 p.2
  map_add' p q := by
    apply Params.ext'
    · simp [unitDir]
    · intro ℓ
      by_cases hℓ : ℓ = m
      · subst hℓ
        ext a i
        simp only [Params.add_read, Matrix.add_apply, unitDir_read_self_iu, Prod.fst_add,
          Pi.add_apply]
        split_ifs <;> simp
      · simp only [Params.add_read, unitDir_read_ne_iu m j _ _ hℓ, add_zero]
    · intro ℓ
      by_cases hℓ : ℓ = m
      · subst hℓ
        ext i a
        simp only [Params.add_write, Matrix.add_apply, unitDir_write_self_iu, Prod.snd_add,
          Pi.add_apply]
        split_ifs <;> simp
      · simp only [Params.add_write, unitDir_write_ne_iu m j _ _ hℓ, add_zero]
    · simp [unitDir]
  map_smul' c p := by
    apply Params.ext'
    · simp [unitDir]
    · intro ℓ
      by_cases hℓ : ℓ = m
      · subst hℓ
        ext a i
        simp only [Params.smul_read, Matrix.smul_apply, unitDir_read_self_iu, Prod.smul_fst,
          Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
        split_ifs <;> simp
      · simp only [Params.smul_read, unitDir_read_ne_iu m j _ _ hℓ, smul_zero]
    · intro ℓ
      by_cases hℓ : ℓ = m
      · subst hℓ
        ext i a
        simp only [Params.smul_write, Matrix.smul_apply, unitDir_write_self_iu, Prod.smul_snd,
          Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
        split_ifs <;> simp
      · simp only [Params.smul_write, unitDir_write_ne_iu m j _ _ hℓ, smul_zero]
    · simp [unitDir]

omit [Fintype T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (Lemma B.1 with the inactive unit, in the form for directions): if
`cobDir θ X + rescaleDirMlp k θ α + unitDir m j δr δa = 0` with `α m j = 0`, then `X`, `α`, `δr`
and `δa` vanish, when `E` and the writes have rank `d`, the write of block `m` without row `j` has
rank `d`, and no read column vanishes. -/
private theorem eq_zero_of_dir_eq_zero_iu (k : ℕ)
    (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) (m : Fin L) (j : hid m)
    (hE : θ.E.rank = Fintype.card d) (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d)
    (hwj : ((θ.write m).submatrix (fun i : {i : hid m // i ≠ j} => (i : hid m)) id).rank
      = Fintype.card d)
    (hc : ∀ ℓ i, (fun a => θ.read ℓ a i) ≠ 0)
    (X : Fin (L + 1) → Matrix d d ℝ) (α : ∀ ℓ, hid ℓ → ℝ) (hαj : α m j = 0) (δr δa : d → ℝ)
    (h : cobDir θ X + (rescaleDirMlp k θ α + unitDir m j δr δa) = 0) :
    X = 0 ∧ α = 0 ∧ δr = 0 ∧ δa = 0 := by
  -- the direction of the unit, with its components
  obtain ⟨U, hU⟩ : ∃ U : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut,
      U = unitDir m j δr δa := ⟨_, rfl⟩
  rw [← hU] at h
  have hUr : ∀ ℓ, ℓ ≠ m → U.read ℓ = 0 := fun ℓ hℓ => by rw [hU, unitDir_read_ne_iu m j δr δa hℓ]
  have hUw : ∀ ℓ, ℓ ≠ m → U.write ℓ = 0 := fun ℓ hℓ => by
    rw [hU, unitDir_write_ne_iu m j δr δa hℓ]
  have hUrm : ∀ a i, U.read m a i = if i = j then δr a else 0 := fun a i => by
    rw [hU, unitDir_read_self_iu]
  have hUwm : ∀ i a, U.write m i a = if i = j then δa a else 0 := fun i a => by
    rw [hU, unitDir_write_self_iu]
  -- the components of the equation: `E`, the reads and the writes
  have h0 : θ.E * X 0 = θ.E * (0 : Matrix d d ℝ) := by
    have hE0 := congrArg Params.E h
    change θ.E * X 0 + (0 + U.E) = 0 at hE0
    rw [show U.E = 0 by rw [hU]; rfl, add_zero, add_zero] at hE0
    rw [hE0, Matrix.mul_zero]
  have hr : ∀ ℓ a i,
      -(X ℓ.castSucc * θ.read ℓ) a i + (α ℓ i * θ.read ℓ a i + U.read ℓ a i) = 0 :=
    fun ℓ a i => congrFun (congrFun (congrArg (fun η => η.read ℓ) h) a) i
  have hwr : ∀ ℓ i a, (θ.write ℓ * X ℓ.succ) i a
      + (-((k : ℝ) * α ℓ i) * θ.write ℓ i a + U.write ℓ i a) = 0 :=
    fun ℓ i a => congrFun (congrFun (congrArg (fun η => η.write ℓ) h) i) a
  -- the embedding: `E X_0 = 0`, and `E` has rank `d`
  have hX0 : X 0 = 0 := cancel_left_of_rank_iu θ.E hE h0
  -- block `ℓ`: if `X_{ℓ-1} = 0`, then `α_ℓ = 0` and `X_ℓ = 0`
  have key : ∀ ℓ : Fin L, X ℓ.castSucc = 0 → α ℓ = 0 ∧ X ℓ.succ = 0 := by
    intro ℓ hℓ
    -- the read column `c_i` of hidden unit `i` moves by `α_i c_i`, and by `δr` for `(m, j)`, where
    -- `α_i = 0`; an entry `a` with `c_i a ≠ 0` gives `α_i = 0`
    have hα : α ℓ = 0 := by
      funext i
      obtain ⟨a, ha⟩ := Function.ne_iff.mp (hc ℓ i)
      have hU0 : U.read ℓ a i = 0 ∨ α ℓ i = 0 := by
        by_cases hℓm : ℓ = m
        · subst hℓm
          by_cases hi : i = j
          · right
            rw [hi]
            exact hαj
          · left
            rw [hUrm, ite_eq_right hi]
        · left
          rw [hUr ℓ hℓm]
          rfl
      rcases hU0 with h' | h'
      · have h'' := hr ℓ a i
        rw [hℓ, h', Matrix.zero_mul, Matrix.zero_apply, neg_zero, zero_add, add_zero] at h''
        exact (mul_eq_zero.mp h'').resolve_right ha
      · exact h'
    refine ⟨hα, ?_⟩
    -- the write moves by `W X_ℓ`, and by `δa` on row `j` of block `m`
    have hw0 : ∀ i a, (θ.write ℓ * X ℓ.succ) i a + U.write ℓ i a = 0 := by
      intro i a
      have h'' := hwr ℓ i a
      rwa [hα, Pi.zero_apply, mul_zero, neg_zero, zero_mul, zero_add] at h''
    by_cases hℓm : ℓ = m
    · -- block `m`: the rows `i ≠ j` of `W X_m` vanish, and they are `W' X_m` for the write `W'`
      -- without row `j`, which has rank `d`
      subst hℓm
      have hsub : (θ.write ℓ).submatrix (fun i : {i : hid ℓ // i ≠ j} => (i : hid ℓ)) id
          * X ℓ.succ =
          (θ.write ℓ).submatrix (fun i : {i : hid ℓ // i ≠ j} => (i : hid ℓ)) id
            * (0 : Matrix d d ℝ) := by
        rw [Matrix.mul_zero]
        ext ⟨i, hi⟩ a
        have h'' := hw0 i a
        rw [hUwm, ite_eq_right hi, add_zero] at h''
        exact h''
      exact cancel_left_of_rank_iu _ hwj hsub
    · -- another block: `W X_ℓ = 0`, and `W` has rank `d`
      have hsub : θ.write ℓ * X ℓ.succ = θ.write ℓ * (0 : Matrix d d ℝ) := by
        rw [Matrix.mul_zero]
        ext i a
        have h'' := hw0 i a
        rwa [hUw ℓ hℓm, Matrix.zero_apply, add_zero] at h''
      exact cancel_left_of_rank_iu _ (hw ℓ) hsub
  -- by induction along the network, `X = 0`; then `α = 0`
  have hX : ∀ ℓ : Fin (L + 1), X ℓ = 0 := by
    intro ℓ
    induction ℓ using Fin.induction with
    | zero => exact hX0
    | succ ℓ ih => exact (key ℓ ih).2
  have hα : α = 0 := funext fun ℓ => (key ℓ (hX ℓ.castSucc)).1
  refine ⟨funext hX, hα, ?_, ?_⟩
  · -- read column `j` of block `m` moves by `δr` alone
    funext a
    have h'' := hr m a j
    rw [hX, hα, hUrm, ite_eq_left rfl] at h''
    simpa only [Pi.zero_apply, Matrix.zero_mul, Matrix.zero_apply, neg_zero, zero_mul, zero_add]
      using h''
  · -- write row `j` of block `m` moves by `δa` alone
    funext a
    have h'' := hwr m j a
    rw [hX, hα, hUwm, ite_eq_left rfl] at h''
    simpa only [Pi.zero_apply, Matrix.mul_zero, Matrix.zero_apply, mul_zero, neg_zero, zero_mul,
      zero_add] using h''

/-- **Proposition E.1, the bound, at one parameter (ReLU and ReLU² blocks):** let `σ` be positively
homogeneous of degree `k` and vanish on `z ≤ 0`, and let hidden unit `j` of block `m` be inactive
at every input at all parameters near `θ`. If `E` and the writes have rank `d`, the write of block
`m` without the row of the unit has rank `d`, and no read column vanishes, then
`fd(θ) ≤ P − (L+1) d² − s − (2d − 1)`, with `s` the number of hidden units of the network. -/
theorem funDim_add_le_of_eventually_unitInactive {k : ℕ}
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (hσ0 : ∀ z : ℝ, z ≤ 0 → σ z = 0)
    (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) (m : Fin L) (j : hid m)
    (hθ : ∀ᶠ θ' in 𝓝 θ, UnitInactive θ' m j)
    (hE : θ.E.rank = Fintype.card d) (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d)
    (hwj : ((θ.write m).submatrix (fun i : {i : hid m // i ≠ j} => (i : hid m)) id).rank
      = Fintype.card d)
    (hc : ∀ ℓ i, (fun a => θ.read ℓ a i) ≠ 0) :
    funDim (Arch.mlp σ id hid) 0 θ
        + ((L + 1) * Fintype.card d ^ 2 + ∑ ℓ, Fintype.card (hid ℓ) + (2 * Fintype.card d - 1))
      ≤ Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) := by
  -- the numbers `α` of the rescalings with `α m j = 0`: the kernel `K` of `α ↦ α m j`
  let ev : (∀ ℓ, hid ℓ → ℝ) →ₗ[ℝ] ℝ :=
    (LinearMap.proj (R := ℝ) (φ := fun _ : hid m => ℝ) j).comp
      (LinearMap.proj (R := ℝ) (φ := fun ℓ => hid ℓ → ℝ) m)
  let K := LinearMap.ker ev
  -- the linear map `(X, α, δr, δa) ↦ cobDir θ X + rescaleDirMlp k θ α + unitDir m j δr δa`
  let Φ := (cobDirLin θ).coprod
    (((rescaleDirMlpLin_iu k θ).comp K.subtype).coprod (unitDirLin_iu m j))
  -- its directions are flat, since the three summands are
  have hV : LinearMap.range Φ ≤ flat (Arch.mlp σ id hid) 0 θ := by
    rintro _ ⟨p, rfl⟩
    rw [LinearMap.coprod_apply, LinearMap.coprod_apply]
    exact Submodule.add_mem _ (cobDir_mem_flat_skipless' θ rfl p.1)
      (Submodule.add_mem _ (rescaleDirMlp_mem_flat hσ θ 0 _)
        (unitDir_mem_flat hσ0 θ m j hθ _ _))
  -- it is injective (Lemma B.1 with the inactive unit)
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨X, ⟨α, hα⟩, δr, δa⟩ hp
    rw [LinearMap.coprod_apply, LinearMap.coprod_apply] at hp
    obtain ⟨h1, h2, h3, h4⟩ :=
      eq_zero_of_dir_eq_zero_iu k θ m j hE hw hwj hc X α (LinearMap.mem_ker.mp hα) δr δa hp
    exact Prod.ext h1 (Prod.ext (Subtype.ext h2) (Prod.ext h3 h4))
  -- `K` has dimension `s - 1`: `α ↦ α m j` is onto `ℝ`
  have hK : Module.finrank ℝ K + 1 = ∑ ℓ, Fintype.card (hid ℓ) := by
    have hsurj : Function.Surjective ev := fun c =>
      ⟨Function.update 0 m (Function.update 0 j c), by
        simp only [ev, LinearMap.coe_comp, LinearMap.coe_proj, Function.comp_apply,
          Function.eval, Function.update_self]⟩
    have h1 := LinearMap.finrank_range_add_finrank_ker ev
    rw [LinearMap.range_eq_top.2 hsurj, finrank_top, Module.finrank_self,
      Module.finrank_pi_fintype] at h1
    simp only [Module.finrank_fintype_fun_eq_card] at h1
    exact (add_comm _ _).trans h1
  -- `d ≥ 1`, since a read column does not vanish
  have hd : 1 ≤ Fintype.card d := by
    obtain ⟨a, -⟩ := Function.ne_iff.mp (hc m j)
    exact Fintype.card_pos_iff.2 ⟨a⟩
  -- the domain has dimension `(L + 1) d² + (s - 1) + 2d`
  have hdim : Module.finrank ℝ ((Fin (L + 1) → Matrix d d ℝ) × (K × ((d → ℝ) × (d → ℝ)))) =
      (L + 1) * Fintype.card d ^ 2 + (Module.finrank ℝ K + (Fintype.card d + Fintype.card d)) := by
    rw [Module.finrank_prod, Module.finrank_prod, Module.finrank_prod, finrank_cobDomain,
      Module.finrank_fintype_fun_eq_card]
  have h := funDim_add_finrank_le_of_le_flat' θ _ hV
  rw [LinearMap.finrank_range_of_inj hinj, hdim] at h
  generalize (L + 1) * Fintype.card d ^ 2 = c at h ⊢
  omega

end Skips
