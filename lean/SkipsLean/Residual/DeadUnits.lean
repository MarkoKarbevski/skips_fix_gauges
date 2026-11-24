import SkipsLean.Residual.Folding
import SkipsLean.Residual.UpperBoundSymmetries
import SkipsLean.Depth.InactiveUnit

/-!
# Dead units of a residual network lower the functional dimension

Paper (skips paper): Appendix A.8, Proposition A.33 (ii) and its proof.

"Proposition A.33 (Folding blocks can kill units and lower the functional dimension). Consider
residual networks of `L ≥ 2` ReLU blocks without normalization. (i) There is a nonempty open set of
weights on which block 1 folds and block 2 has a dead unit. (ii) If `ν` units are dead, then on
every batch on which no pre-activation vanishes, the Jacobian has rank at most
`P − d_model² − s − (2 d_model − 1) ν`."

"(ii) The columns of the Jacobian that belong to the read and the write of a dead unit vanish,
`2 d_model ν` columns in all. The other columns are those of the network with the dead units
deleted. That network has `P − 2 d_model ν` parameters and `s − ν` unit rescalings, since `s`
counts one rescaling per ReLU unit. Its function does not change under the change of basis of the
hidden states and these rescalings. At generic parameters they act with orbits of dimension
`d_model² + s − ν`, since `E` has rank `d_model`."

Stated here, for a residual network of MLP blocks without normalization whose activation is
positively homogeneous of degree `k` and vanishes on `z ≤ 0` (ReLU, ReLU²), and a finite set `J`
of units (pairs of a block and one of its hidden units): if every unit of `J` is dead at all
parameters near `θ` (`UnitInactiveRes`, `Residual/Folding.lean`), `E` has rank `d` and no read
column vanishes, then `fd(θ) ≤ P − d² − s − (2d − 1) ν` with `ν` the number of units of `J`. The
flat directions are the change of basis by one matrix at all hidden states (`d²`), the rescalings
of the units outside `J` (`s − ν`), and the directions that move the read column and the write row
of a unit of `J` (`2dν`).

Differences from the paper's sentence: the paper asks that the units are dead at `θ` and takes
batches on which no pre-activation vanishes; Lean's `funDim` takes the Jacobian at all inputs, and
the hypothesis is that the units are dead on a neighborhood of `θ`, as on the open set of part
(i). The twin without skip connections, for one unit, is `Depth/InactiveUnit.lean`
(Proposition E.1 of the dimension paper, Proposition A.35 of the skips paper).
-/

namespace Skips

open Matrix Filter Topology
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {σ : ℝ → ℝ} {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)] [∀ ℓ, DecidableEq (hid ℓ)]

/-! ### Step 1: one dead unit gives flat directions -/

omit [Fintype T] [Fintype dOut] in
/-- Helper (as `hidden_eq_of_unitInactive_iu` of `Depth/InactiveUnit.lean`, with the stream
matrices `1`): two parameters that differ only in the read column and the write row of unit `j`
of block `m`, at both of which this unit is dead, have the same hidden states at every input. -/
private theorem hidden_eq_of_unitInactiveRes_dead (hσ0 : ∀ z : ℝ, z ≤ 0 → σ z = 0)
    (θ θ' : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) (m : Fin L) (j : hid m)
    (h1 : UnitInactiveRes θ m j) (h2 : UnitInactiveRes θ' m j) (hE : θ'.E = θ.E)
    (hr : ∀ ℓ, ℓ ≠ m → θ'.read ℓ = θ.read ℓ) (hw : ∀ ℓ, ℓ ≠ m → θ'.write ℓ = θ.write ℓ)
    (hrm : ∀ a i, i ≠ j → θ'.read m a i = θ.read m a i)
    (hwm : ∀ i a, i ≠ j → θ'.write m i a = θ.write m i a)
    (x : Matrix T dIn ℝ) (ℓ : Fin (L + 1)) :
    hidden (Arch.mlp σ id hid) 1 θ' x ℓ = hidden (Arch.mlp σ id hid) 1 θ x ℓ := by
  induction ℓ using Fin.induction with
  | zero => rw [hidden_zero, hidden_zero, hE]
  | succ ℓ ih =>
    -- the stream term `h 1` is the same on both sides; compare the outputs of block `ℓ`
    rw [hidden_succ, hidden_succ, ih]
    congr 1
    show (hidden (Arch.mlp σ id hid) 1 θ x ℓ.castSucc * θ'.read ℓ).map σ * θ'.write ℓ =
      (hidden (Arch.mlp σ id hid) 1 θ x ℓ.castSucc * θ.read ℓ).map σ * θ.write ℓ
    by_cases hℓ : ℓ = m
    · -- block `m`: the terms of the units `i ≠ j` agree, the term of `j` is `0`
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
      · have hu : (hidden (Arch.mlp σ id hid) 1 θ x ℓ.castSucc * θ'.read ℓ) t i =
            (hidden (Arch.mlp σ id hid) 1 θ x ℓ.castSucc * θ.read ℓ) t i := by
          rw [Matrix.mul_apply, Matrix.mul_apply]
          exact Finset.sum_congr rfl fun b _ => by rw [hrm b i hi]
        rw [hu, hwm i a hi]
    · -- another block: nothing changed
      rw [hr ℓ hℓ, hw ℓ hℓ]

omit [Fintype T] [DecidableEq d] in
/-- Helper: the line `τ ↦ θ + τ η` passes through `θ` at `τ = 0` with velocity `η`. -/
private theorem hasDerivAt_line_dead {A : Arch T d L} (θ η : Params A dIn dOut) :
    HasDerivAt (fun τ : ℝ => θ + τ • η) η 0 := by
  have h := ((hasDerivAt_id (0 : ℝ)).smul_const η).const_add θ
  rw [one_smul] at h
  exact h

/-- Helper (as `unitDir_mem_flat` of `Depth/InactiveUnit.lean`, with the stream matrices `1`): if
`σ` vanishes on `z ≤ 0` and unit `j` of block `m` is dead at all parameters near `θ`, then every
direction that moves only the read column and the write row of this unit is flat at `θ`. -/
private theorem unitDir_mem_flat_dead (hσ0 : ∀ z : ℝ, z ≤ 0 → σ z = 0)
    (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) (m : Fin L) (j : hid m)
    (hθ : ∀ᶠ θ' in 𝓝 θ, UnitInactiveRes θ' m j) (δr δa : d → ℝ) :
    unitDir m j δr δa ∈ flat (Arch.mlp σ id hid) 1 θ := by
  set η : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut := unitDir m j δr δa
  -- the line `τ ↦ θ + τ η` passes through `θ` with velocity `η`
  have hline := hasDerivAt_line_dead θ η
  have h0 : θ + (0 : ℝ) • η = θ := by rw [zero_smul, add_zero]
  -- near `τ = 0` the unit is dead along the line
  have hnear : ∀ᶠ τ in 𝓝 (0 : ℝ), UnitInactiveRes (θ + τ • η) m j := by
    have ht := hline.continuousAt.tendsto
    rw [h0] at ht
    exact ht.eventually hθ
  refine mem_flat_of_hasDerivAt' θ (fun τ => θ + τ • η) η hline h0
    (hnear.mono fun τ hτ x => ?_)
  -- the line moves only the read column and the write row of the unit, so the hidden states, and
  -- then the outputs, are those of `θ`
  have hh := hidden_eq_of_unitInactiveRes_dead hσ0 θ (θ + τ • η) m j hθ.self_of_nhds hτ
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
  show (Arch.mlp σ id hid).χ (hidden _ 1 (θ + τ • η) x (Fin.last L)) * (θ + τ • η).D =
    (Arch.mlp σ id hid).χ (hidden _ 1 θ x (Fin.last L)) * θ.D
  rw [hh]
  simp only [η, unitDir, Params.add_D, Params.smul_D, smul_zero, add_zero]

/-! ### Step 2: the linear maps -/

omit [DecidableEq d] [∀ ℓ, DecidableEq (hid ℓ)] in
/-- Helper (as `rescaleDirMlpLin_iu` of `Depth/InactiveUnit.lean`): `α ↦ rescaleDirMlp k θ α` is
linear. -/
private noncomputable def rescaleDirMlpLin_dead (k : ℕ)
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
private theorem unitDir_read_ne_dead {χ : Matrix T d ℝ → Matrix T d ℝ} (m : Fin L) (j : hid m)
    (δr δa : d → ℝ) {ℓ : Fin L} (hℓ : ℓ ≠ m) :
    (unitDir (σ := σ) (χ := χ) (dIn := dIn) (dOut := dOut) m j δr δa).read ℓ = 0 := by
  simp only [unitDir]
  rw [Function.update_of_ne hℓ]

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the write of `unitDir` at a block other than `m` is `0`. -/
private theorem unitDir_write_ne_dead {χ : Matrix T d ℝ → Matrix T d ℝ} (m : Fin L) (j : hid m)
    (δr δa : d → ℝ) {ℓ : Fin L} (hℓ : ℓ ≠ m) :
    (unitDir (σ := σ) (χ := χ) (dIn := dIn) (dOut := dOut) m j δr δa).write ℓ = 0 := by
  simp only [unitDir]
  rw [Function.update_of_ne hℓ]

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the read of `unitDir` at block `m`. -/
private theorem unitDir_read_self_dead {χ : Matrix T d ℝ → Matrix T d ℝ} (m : Fin L) (j : hid m)
    (δr δa : d → ℝ) (a : d) (i : hid m) :
    (unitDir (σ := σ) (χ := χ) (dIn := dIn) (dOut := dOut) m j δr δa).read m a i =
      if i = j then δr a else 0 := by
  simp only [unitDir, Function.update_self, Matrix.of_apply]

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the write of `unitDir` at block `m`. -/
private theorem unitDir_write_self_dead {χ : Matrix T d ℝ → Matrix T d ℝ} (m : Fin L)
    (j : hid m) (δr δa : d → ℝ) (i : hid m) (a : d) :
    (unitDir (σ := σ) (χ := χ) (dIn := dIn) (dOut := dOut) m j δr δa).write m i a =
      if i = j then δa a else 0 := by
  simp only [unitDir, Function.update_self, Matrix.of_apply]

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the read of `unitDir m j` at unit `i` of block `ℓ` is `δr` if `(ℓ, i) = (m, j)`, and
`0` otherwise. -/
private theorem unitDir_read_dead {χ : Matrix T d ℝ → Matrix T d ℝ} (m : Fin L) (j : hid m)
    (δr δa : d → ℝ) (ℓ : Fin L) (a : d) (i : hid ℓ) :
    (unitDir (σ := σ) (χ := χ) (dIn := dIn) (dOut := dOut) m j δr δa).read ℓ a i =
      if (⟨m, j⟩ : Σ m, hid m) = ⟨ℓ, i⟩ then δr a else 0 := by
  by_cases hℓ : ℓ = m
  · subst hℓ
    by_cases hi : i = j
    · subst hi
      simp [unitDir_read_self_dead]
    · rw [unitDir_read_self_dead, ite_eq_right hi,
        ite_eq_right fun h => hi (sigma_mk_injective h).symm]
  · rw [unitDir_read_ne_dead m j δr δa hℓ,
      ite_eq_right fun h => hℓ (congrArg Sigma.fst h).symm]
    rfl

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the write of `unitDir m j` at unit `i` of block `ℓ` is `δa` if `(ℓ, i) = (m, j)`, and
`0` otherwise. -/
private theorem unitDir_write_dead {χ : Matrix T d ℝ → Matrix T d ℝ} (m : Fin L) (j : hid m)
    (δr δa : d → ℝ) (ℓ : Fin L) (i : hid ℓ) (a : d) :
    (unitDir (σ := σ) (χ := χ) (dIn := dIn) (dOut := dOut) m j δr δa).write ℓ i a =
      if (⟨m, j⟩ : Σ m, hid m) = ⟨ℓ, i⟩ then δa a else 0 := by
  by_cases hℓ : ℓ = m
  · subst hℓ
    by_cases hi : i = j
    · subst hi
      simp [unitDir_write_self_dead]
    · rw [unitDir_write_self_dead, ite_eq_right hi,
        ite_eq_right fun h => hi (sigma_mk_injective h).symm]
  · rw [unitDir_write_ne_dead m j δr δa hℓ,
      ite_eq_right fun h => hℓ (congrArg Sigma.fst h).symm]
    rfl

omit [Fintype T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (as `unitDirLin_iu` of `Depth/InactiveUnit.lean`): `(δr, δa) ↦ unitDir m j δr δa` is
linear. -/
private noncomputable def unitDirLin_dead (m : Fin L) (j : hid m) :
    ((d → ℝ) × (d → ℝ)) →ₗ[ℝ] Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut where
  toFun p := unitDir m j p.1 p.2
  map_add' p q := by
    apply Params.ext'
    · simp [unitDir]
    · intro ℓ
      by_cases hℓ : ℓ = m
      · subst hℓ
        ext a i
        simp only [Params.add_read, Matrix.add_apply, unitDir_read_self_dead, Prod.fst_add,
          Pi.add_apply]
        split_ifs <;> simp
      · simp only [Params.add_read, unitDir_read_ne_dead m j _ _ hℓ, add_zero]
    · intro ℓ
      by_cases hℓ : ℓ = m
      · subst hℓ
        ext i a
        simp only [Params.add_write, Matrix.add_apply, unitDir_write_self_dead, Prod.snd_add,
          Pi.add_apply]
        split_ifs <;> simp
      · simp only [Params.add_write, unitDir_write_ne_dead m j _ _ hℓ, add_zero]
    · simp [unitDir]
  map_smul' c p := by
    apply Params.ext'
    · simp [unitDir]
    · intro ℓ
      by_cases hℓ : ℓ = m
      · subst hℓ
        ext a i
        simp only [Params.smul_read, Matrix.smul_apply, unitDir_read_self_dead, Prod.smul_fst,
          Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
        split_ifs <;> simp
      · simp only [Params.smul_read, unitDir_read_ne_dead m j _ _ hℓ, smul_zero]
    · intro ℓ
      by_cases hℓ : ℓ = m
      · subst hℓ
        ext i a
        simp only [Params.smul_write, Matrix.smul_apply, unitDir_write_self_dead, Prod.smul_snd,
          Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
        split_ifs <;> simp
      · simp only [Params.smul_write, unitDir_write_ne_dead m j _ _ hℓ, smul_zero]
    · simp [unitDir]

/-! ### Step 3: injectivity -/

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the `E` of a finite sum of parameters is the sum of their `E`. -/
private theorem sum_E_dead {A : Arch T d L} {ι : Type*} (s : Finset ι)
    (f : ι → Params A dIn dOut) : (∑ p ∈ s, f p).E = ∑ p ∈ s, (f p).E :=
  map_sum (AddMonoidHom.mk' (fun η : Params A dIn dOut => η.E) fun _ _ => rfl) f s

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: an entry of the read of a finite sum of parameters is the sum of the entries. -/
private theorem sum_read_dead {A : Arch T d L} {ι : Type*} (s : Finset ι)
    (f : ι → Params A dIn dOut) (ℓ : Fin L) (a : d) (i : A.r ℓ) :
    (∑ p ∈ s, f p).read ℓ a i = ∑ p ∈ s, (f p).read ℓ a i :=
  map_sum (AddMonoidHom.mk' (fun η : Params A dIn dOut => η.read ℓ a i) fun _ _ => rfl) f s

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: an entry of the write of a finite sum of parameters is the sum of the entries. -/
private theorem sum_write_dead {A : Arch T d L} {ι : Type*} (s : Finset ι)
    (f : ι → Params A dIn dOut) (ℓ : Fin L) (i : A.w ℓ) (a : d) :
    (∑ p ∈ s, f p).write ℓ i a = ∑ p ∈ s, (f p).write ℓ i a :=
  map_sum (AddMonoidHom.mk' (fun η : Params A dIn dOut => η.write ℓ i a) fun _ _ => rfl) f s

omit [Fintype T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (as `cancel_left_of_rank_iu` of `Depth/InactiveUnit.lean`): a matrix `M` of rank equal
to its number of columns cancels on the left, `M X = M Y → X = Y`. -/
private theorem cancel_left_of_rank_dead {m n k : Type*} [Fintype n] (M : Matrix m n ℝ)
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

omit [Fintype T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (Lemma B.1 with the dead units, in the form for directions): if
`cobDir θ (fun _ => X) + rescaleDirMlp k θ α + ∑_{p ∈ J} unitDir p (δ p) = 0` with `α` zero on
the units of `J`, then `X`, `α` and `δ` vanish, when `E` has rank `d` and no read column
vanishes. -/
private theorem eq_zero_of_dir_eq_zero_dead (k : ℕ)
    (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) (J : Finset (Σ m, hid m))
    (hE : θ.E.rank = Fintype.card d) (hc : ∀ ℓ i, (fun a => θ.read ℓ a i) ≠ 0)
    (X : Matrix d d ℝ) (α : ∀ ℓ, hid ℓ → ℝ) (hαJ : ∀ p ∈ J, α p.1 p.2 = 0)
    (δ : J → (d → ℝ) × (d → ℝ))
    (h : cobDir θ (fun _ => X) + (rescaleDirMlp k θ α
      + ∑ p : J, unitDir p.1.1 p.1.2 (δ p).1 (δ p).2) = 0) :
    X = 0 ∧ α = 0 ∧ δ = 0 := by
  -- the sum of the directions of the units of `J`, with its components
  obtain ⟨U, hU⟩ : ∃ U : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut,
      U = ∑ p : J, unitDir p.1.1 p.1.2 (δ p).1 (δ p).2 := ⟨_, rfl⟩
  rw [← hU] at h
  have hUE : U.E = 0 := by
    rw [hU, sum_E_dead]
    exact Finset.sum_eq_zero fun p _ => rfl
  have hUr : ∀ ℓ a i, U.read ℓ a i = ∑ p : J, if p.1 = ⟨ℓ, i⟩ then (δ p).1 a else 0 := by
    intro ℓ a i
    rw [hU, sum_read_dead]
    exact Finset.sum_congr rfl fun p _ => unitDir_read_dead _ _ _ _ ℓ a i
  have hUw : ∀ ℓ i a, U.write ℓ i a = ∑ p : J, if p.1 = ⟨ℓ, i⟩ then (δ p).2 a else 0 := by
    intro ℓ i a
    rw [hU, sum_write_dead]
    exact Finset.sum_congr rfl fun p _ => unitDir_write_dead _ _ _ _ ℓ i a
  -- a unit outside `J` is not moved by these directions
  have hUr0 : ∀ ℓ a i, (⟨ℓ, i⟩ : Σ m, hid m) ∉ J → U.read ℓ a i = 0 := by
    intro ℓ a i hn
    rw [hUr]
    exact Finset.sum_eq_zero fun p _ => ite_eq_right fun (hp : p.1 = ⟨ℓ, i⟩) => hn (hp ▸ p.2)
  -- a unit `q` of `J` is moved by its own direction alone
  have hUrJ : ∀ (q : J) a, U.read q.1.1 a q.1.2 = (δ q).1 a := by
    intro q a
    rw [hUr]
    refine (Fintype.sum_eq_single q fun p hp =>
      ite_eq_right fun hpq => hp (Subtype.ext hpq)).trans ?_
    exact ite_eq_left rfl
  have hUwJ : ∀ (q : J) a, U.write q.1.1 q.1.2 a = (δ q).2 a := by
    intro q a
    rw [hUw]
    refine (Fintype.sum_eq_single q fun p hp =>
      ite_eq_right fun hpq => hp (Subtype.ext hpq)).trans ?_
    exact ite_eq_left rfl
  -- the components of the equation: `E`, the reads and the writes
  have h0 : θ.E * X = θ.E * (0 : Matrix d d ℝ) := by
    have hE0 := congrArg Params.E h
    change θ.E * X + (0 + U.E) = 0 at hE0
    rw [hUE, add_zero, add_zero] at hE0
    rw [hE0, Matrix.mul_zero]
  have hr : ∀ ℓ a i, -(X * θ.read ℓ) a i + (α ℓ i * θ.read ℓ a i + U.read ℓ a i) = 0 :=
    fun ℓ a i => congrFun (congrFun (congrArg (fun η => η.read ℓ) h) a) i
  have hwr : ∀ ℓ i a, (θ.write ℓ * X) i a
      + (-((k : ℝ) * α ℓ i) * θ.write ℓ i a + U.write ℓ i a) = 0 :=
    fun ℓ i a => congrFun (congrFun (congrArg (fun η => η.write ℓ) h) i) a
  -- the embedding: `E X = 0`, and `E` has rank `d`
  have hX : X = 0 := cancel_left_of_rank_dead θ.E hE h0
  -- the read column `c_i` of unit `i` moves by `α_i c_i`; for `i` outside `J` this is all, and an
  -- entry `a` with `c_i a ≠ 0` gives `α_i = 0`; for `i` in `J`, `α_i = 0` is assumed
  have hα : α = 0 := by
    funext ℓ i
    by_cases hJ : (⟨ℓ, i⟩ : Σ m, hid m) ∈ J
    · exact hαJ _ hJ
    · obtain ⟨a, ha⟩ := Function.ne_iff.mp (hc ℓ i)
      have h'' := hr ℓ a i
      rw [hX, hUr0 ℓ a i hJ, Matrix.zero_mul, Matrix.zero_apply, neg_zero, zero_add,
        add_zero] at h''
      exact (mul_eq_zero.mp h'').resolve_right ha
  -- the read column and the write row of a unit of `J` move by its `δ` alone
  have hδr : ∀ (q : J) a, (δ q).1 a = 0 := by
    intro q a
    have h'' := hr q.1.1 a q.1.2
    rw [hX, hα, hUrJ] at h''
    simpa only [Matrix.zero_mul, Matrix.zero_apply, neg_zero, Pi.zero_apply, zero_mul,
      zero_add] using h''
  have hδa : ∀ (q : J) a, (δ q).2 a = 0 := by
    intro q a
    have h'' := hwr q.1.1 q.1.2 a
    rw [hX, hα, hUwJ] at h''
    simpa only [Matrix.mul_zero, Matrix.zero_apply, Pi.zero_apply, mul_zero, neg_zero, zero_mul,
      zero_add] using h''
  exact ⟨hX, hα, funext fun q => Prod.ext (funext (hδr q)) (funext (hδa q))⟩

/-- **Proposition A.33 (ii) of the skips paper, at one parameter:** let `σ` be positively
homogeneous of degree `k` and vanish on `z ≤ 0`, and let every unit of the finite set `J` be dead
at all parameters near `θ`, in the residual network. If `E` has rank `d` and no read column
vanishes, then `fd(θ) ≤ P − d² − s − (2d − 1) ν`, with `s` the number of hidden units of the
network and `ν` the number of units of `J`. -/
theorem funDim_add_le_residual_of_eventually_unitInactive {k : ℕ}
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (hσ0 : ∀ z : ℝ, z ≤ 0 → σ z = 0)
    (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) (J : Finset (Σ m, hid m))
    (hθ : ∀ p ∈ J, ∀ᶠ θ' in 𝓝 θ, UnitInactiveRes θ' p.1 p.2)
    (hE : θ.E.rank = Fintype.card d) (hc : ∀ ℓ i, (fun a => θ.read ℓ a i) ≠ 0) :
    funDim (Arch.mlp σ id hid) 1 θ
        + (Fintype.card d ^ 2 + ∑ ℓ, Fintype.card (hid ℓ) + (2 * Fintype.card d - 1) * J.card)
      ≤ Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) := by
  -- the numbers `α` of the rescalings that vanish on the units of `J`: the kernel `K` of
  -- `α ↦ (α p)_{p ∈ J}`
  let ev : (∀ ℓ, hid ℓ → ℝ) →ₗ[ℝ] (J → ℝ) := LinearMap.pi fun p : J =>
    (LinearMap.proj (R := ℝ) (φ := fun _ : hid p.1.1 => ℝ) p.1.2).comp
      (LinearMap.proj (R := ℝ) (φ := fun ℓ => hid ℓ → ℝ) p.1.1)
  let K := LinearMap.ker ev
  -- the linear map `(X, α, δ) ↦ cobDir θ (fun _ => X) + rescaleDirMlp k θ α + ∑ unitDir p (δ p)`
  let Ψ := ((cobDirLin θ).comp (LinearMap.pi fun _ : Fin (L + 1) => LinearMap.id)).coprod
    (((rescaleDirMlpLin_dead k θ).comp K.subtype).coprod
      (∑ p : J, (unitDirLin_dead (T := T) (σ := σ) (dIn := dIn) (dOut := dOut) p.1.1 p.1.2).comp
        (LinearMap.proj (R := ℝ) (φ := fun _ : J => (d → ℝ) × (d → ℝ)) p)))
  have hΨ : ∀ (X : Matrix d d ℝ) (α : K) (δ : J → (d → ℝ) × (d → ℝ)), Ψ (X, α, δ) =
      cobDir θ (fun _ => X) + (rescaleDirMlp k θ (α : ∀ ℓ, hid ℓ → ℝ)
        + ∑ p : J, unitDir p.1.1 p.1.2 (δ p).1 (δ p).2) := by
    intro X α δ
    rw [LinearMap.coprod_apply, LinearMap.coprod_apply, LinearMap.sum_apply]
    rfl
  -- its directions are flat, since the summands are
  have hV : LinearMap.range Ψ ≤ flat (Arch.mlp σ id hid) 1 θ := by
    rintro _ ⟨⟨X, α, δ⟩, rfl⟩
    rw [hΨ]
    refine Submodule.add_mem _ (cobDir_const_mem_flat_residual' θ rfl X)
      (Submodule.add_mem _ (rescaleDirMlp_mem_flat hσ θ 1 _) (Submodule.sum_mem _ fun p _ => ?_))
    exact unitDir_mem_flat_dead hσ0 θ p.1.1 p.1.2 (hθ p.1 p.2) _ _
  -- it is injective (Lemma B.1 with the dead units)
  have hinj : Function.Injective Ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨X, ⟨α, hα⟩, δ⟩ hp
    rw [hΨ] at hp
    have hαJ : ∀ p ∈ J, α p.1 p.2 = 0 := fun p hp' =>
      congrFun (LinearMap.mem_ker.mp hα) ⟨p, hp'⟩
    obtain ⟨h1, h2, h3⟩ := eq_zero_of_dir_eq_zero_dead k θ J hE hc X α hαJ δ hp
    exact Prod.ext h1 (Prod.ext (Subtype.ext h2) h3)
  -- `K` has dimension `s - ν`: `ev` is onto `ℝ^J`
  have hK : Module.finrank ℝ K + J.card = ∑ ℓ, Fintype.card (hid ℓ) := by
    have hsurj : Function.Surjective ev := fun c =>
      ⟨fun ℓ i => if h : (⟨ℓ, i⟩ : Σ m, hid m) ∈ J then c ⟨_, h⟩ else 0,
        funext fun p => dite_eq_left p.2⟩
    change Module.finrank ℝ (LinearMap.ker ev) + J.card = _
    have h1 := LinearMap.finrank_range_add_finrank_ker ev
    rw [LinearMap.range_eq_top.2 hsurj, finrank_top, Module.finrank_fintype_fun_eq_card,
      Fintype.card_coe, Module.finrank_pi_fintype] at h1
    simp only [Module.finrank_fintype_fun_eq_card] at h1
    omega
  -- the domain has dimension `d² + (s - ν) + 2dν`
  have hdim : Module.finrank ℝ (Matrix d d ℝ × (K × (J → (d → ℝ) × (d → ℝ)))) =
      Fintype.card d * Fintype.card d
        + (Module.finrank ℝ K + J.card * (Fintype.card d + Fintype.card d)) := by
    rw [Module.finrank_prod, Module.finrank_prod, Module.finrank_matrix, Module.finrank_self,
      mul_one, Module.finrank_pi_fintype]
    simp only [Module.finrank_prod, Module.finrank_fintype_fun_eq_card, Finset.sum_const,
      Finset.card_univ, Fintype.card_coe, smul_eq_mul]
  -- the count: `ν + (2d - 1) ν = 2dν` (if `ν > 0`, a unit of `J` has a nonzero read, so `d ≥ 1`)
  have hcount : Fintype.card d ^ 2 + (Module.finrank ℝ K + J.card)
      + (2 * Fintype.card d - 1) * J.card = Fintype.card d * Fintype.card d
        + (Module.finrank ℝ K + J.card * (Fintype.card d + Fintype.card d)) := by
    rcases Nat.eq_zero_or_pos J.card with h0 | hpos
    · rw [h0]
      ring
    · obtain ⟨p, hp⟩ := Finset.card_pos.mp hpos
      obtain ⟨a, -⟩ := Function.ne_iff.mp (hc p.1 p.2)
      obtain ⟨c, hc'⟩ : ∃ c, Fintype.card d = c + 1 :=
        ⟨_, (Nat.succ_pred_eq_of_pos (Fintype.card_pos_iff.2 ⟨a⟩)).symm⟩
      rw [hc', show 2 * (c + 1) - 1 = 2 * c + 1 by omega]
      ring
  have h := funDim_add_finrank_le_of_le_flat' θ _ hV
  rw [LinearMap.finrank_range_of_inj hinj, hdim] at h
  rw [← hK, hcount]
  exact h

end Skips
