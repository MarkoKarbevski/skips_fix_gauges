import SkipsLean.Dimension.RescalingGate
import SkipsLean.Dimension.UpperBoundRMSNormZero
import SkipsLean.Dimension.UpperBoundReadout
import SkipsLean.Basic.EigenvectorsGeneralPosition

/-!
# Locally free action, the form with the readout: the symmetries inside blocks

Paper (skips paper), Lemma A.18 (Locally free action): "The same holds if the readout has rank
`d_model` and every block has width at least `d_model`." Its proof: "The second statement follows
by the mirror induction from the readout, `D ↦ G_L^{-1} D`: rescalings act freely on the rows of
a generic write, except that for ReGLU a row fixes only the product `cc′` of the gate and value
scales of its unit; each read, of rank `d_model` and with generic columns, then forces
`G_{ℓ−1} = I` and the remaining scales to be 1. With RMSNorm the changes of basis lie in
`CO(d_model)` or `O(d_model)`, and the argument is unchanged."

`Dimension/UpperBoundReadout.lean` has this sentence in infinitesimal form for the changes of
basis alone (`cobDir_injective_of_rank_D`). Here the same form with the symmetries inside blocks:
the twins of `cobDir_add_rescaleDir_injective` (gated blocks, the rescaling of the values),
`cobDir_add_rescaleDirMlp_injective` (ReLU and ReLU² blocks), of
`cobDir_add_rescaleDir_add_rescaleDirGate_injective` (ReGLU blocks) and of
`cobDir_add_scaleDir_injective` (`ε = 0`: the scaling of each hidden state), which ask `E` and
the writes of rank `d`. Each asks instead: `D` of rank `d`, every read of rank `d`, no row of a
write zero.

* For ReLU and ReLU² blocks the degree `k` is not `0` (the write row of a hidden unit moves by
  `−k α_i a_i`).
* For ReGLU blocks a write row gives only `α_i − k β_i`, and the read gives the rest when its
  columns are in general position: any `d` of the `2 d_hidden` gate and value columns are
  linearly independent, and there are more than `d` of them (so the read has rank `d`; at generic
  parameters this holds when the block has width at least `d ≥ 1`). Rank `d` alone is not enough:
  for `d = 2` and one block with two hidden units, both with the gate column `e_1` and the value
  column `e_2`, and `E = 0`, the direction of `X_0 = diag(1, −k)`, `β = (1, 1)`, `α = (k, k)`,
  `X_1 = 0` is `0`, for every degree `k`
  (`ai_notes/locally_free_readout_check_2026-11-25.py`).
* For `ε = 0` the statement asks `E ≠ 0` and every write nonzero, and nothing of the matrices
  `Y_ℓ` (the twin with the embedding asks them antisymmetric).

The statements for the group ("only the identity fixes `θ`") are in
`Symmetry/LocallyFreeEmbedding.lean` and `Symmetry/LocallyFreeReadout.lean`.
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {σ : ℝ → ℝ} {χ : Matrix T d ℝ → Matrix T d ℝ} {hid : Fin L → Type}
  [∀ ℓ, Fintype (hid ℓ)]

/-- Helper (the private `mul_right_cancel_of_rank_ubd` of `UpperBoundReadout.lean`): a matrix `M`
of rank equal to its number of rows cancels on the right, `X M = Y M → X = Y` (`v ↦ v M` is
injective by rank–nullity for `Mᵀ`). -/
private theorem mul_right_cancel_of_rank_uri {m n k : Type*} [Fintype m] [Fintype n]
    (M : Matrix m n ℝ) (hM : M.rank = Fintype.card m) {X Y : Matrix k m ℝ} (h : X * M = Y * M) :
    X = Y := by
  -- `w ↦ Mᵀ w` is injective: `rank Mᵀ + dim ker Mᵀ = card m`
  have hinj : Function.Injective Mᵀ.mulVecLin := by
    rw [← LinearMap.ker_eq_bot, ← Submodule.finrank_eq_zero]
    have := LinearMap.finrank_range_add_finrank_ker Mᵀ.mulVecLin
    rw [Module.finrank_fintype_fun_eq_card] at this
    rw [← Matrix.rank_transpose, Matrix.rank] at hM
    omega
  -- compare `X` and `Y` row by row
  ext i j
  have hrow : Mᵀ.mulVecLin (fun l => X i l) = Mᵀ.mulVecLin (fun l => Y i l) := by
    funext p
    have := congrFun (congrFun h i) p
    show (Mᵀ *ᵥ fun l => X i l) p = (Mᵀ *ᵥ fun l => Y i l) p
    rw [Matrix.mulVec_transpose, Matrix.mulVec_transpose]
    simpa [Matrix.mul_apply, Matrix.vecMul, dotProduct] using this
  exact congrFun (hinj hrow) j

omit [Fintype T] [DecidableEq d] [Fintype dIn] in
/-- **Lemma A.18, second sentence, for gated blocks, in infinitesimal form.** If `D` and every
read have rank `d` and no row of a write vanishes, the direction `cobDir θ X + rescaleDir θ α`
determines `X` and `α`. -/
theorem cobDir_add_rescaleDir_injective_of_rank_D
    (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut)
    (hD : θ.D.rank = Fintype.card d) (hr : ∀ ℓ, (θ.read ℓ).rank = Fintype.card d)
    (ha : ∀ ℓ i, (fun a => θ.write ℓ i a) ≠ 0) :
    Function.Injective fun p : (Fin (L + 1) → Matrix d d ℝ) × (∀ ℓ, hid ℓ → ℝ) =>
      cobDir θ p.1 + rescaleDir θ p.2 := by
  rintro ⟨X, α⟩ ⟨X', α'⟩ h
  -- the readout component: `X_L D = X'_L D` (the rescalings leave `D` alone), and `D` has
  -- rank `d`
  have hL : X (Fin.last L) = X' (Fin.last L) := by
    have h0 : -(X (Fin.last L) * θ.D) + 0 = -(X' (Fin.last L) * θ.D) + 0 := congrArg Params.D h
    rw [add_zero, add_zero] at h0
    exact mul_right_cancel_of_rank_uri θ.D hD (neg_injective h0)
  -- block `ℓ`: if `X_{ℓ+1} = X'_{ℓ+1}`, then `α_ℓ = α'_ℓ` and `X_ℓ = X'_ℓ`
  have key : ∀ ℓ : Fin L, X ℓ.succ = X' ℓ.succ → α ℓ = α' ℓ ∧ X ℓ.castSucc = X' ℓ.castSucc := by
    intro ℓ hℓ
    -- the write moves by `W X_{ℓ+1} + diag(α_ℓ) W`, and the first terms agree; an entry `a` with
    -- `a_i a ≠ 0` gives `α_i = α'_i`
    have hw' := congrArg (fun η => η.write ℓ) h
    change θ.write ℓ * X ℓ.succ + Matrix.of (fun i a => α ℓ i * θ.write ℓ i a) =
      θ.write ℓ * X' ℓ.succ + Matrix.of (fun i a => α' ℓ i * θ.write ℓ i a) at hw'
    rw [hℓ, add_right_inj] at hw'
    have hα : α ℓ = α' ℓ := by
      funext i
      obtain ⟨a, ha'⟩ := Function.ne_iff.mp (ha ℓ i)
      have hia : α ℓ i * θ.write ℓ i a = α' ℓ i * θ.write ℓ i a := congrFun (congrFun hw' i) a
      exact mul_right_cancel₀ ha' hia
    refine ⟨hα, ?_⟩
    -- the read moves by `-X_ℓ W_read` plus `-α_i e_i` on the value columns; the second terms
    -- agree, and the read has rank `d`
    have hr' := congrArg (fun η => η.read ℓ) h
    change -(X ℓ.castSucc * θ.read ℓ) + Matrix.of (fun a j =>
        Sum.elim (fun _ => 0) (fun i => -(α ℓ i) * θ.read ℓ a (Sum.inr i)) j) =
      -(X' ℓ.castSucc * θ.read ℓ) + Matrix.of (fun a j =>
        Sum.elim (fun _ => 0) (fun i => -(α' ℓ i) * θ.read ℓ a (Sum.inr i)) j) at hr'
    rw [hα, add_left_inj] at hr'
    exact mul_right_cancel_of_rank_uri (θ.read ℓ) (hr ℓ) (neg_injective hr')
  -- by induction down the network, `X = X'`; then `α = α'`
  have hX : ∀ ℓ : Fin (L + 1), X ℓ = X' ℓ := by
    intro ℓ
    induction ℓ using Fin.reverseInduction with
    | last => exact hL
    | cast ℓ ih => exact (key ℓ ih).2
  exact Prod.ext (funext hX) (funext fun ℓ => (key ℓ (hX ℓ.succ)).1)

omit [Fintype T] [DecidableEq d] [Fintype dIn] in
/-- **Lemma A.18, second sentence, for ReLU and ReLU² blocks, in infinitesimal form.** For
`k ≠ 0`: if `D` and every read have rank `d` and no row of a write vanishes, the direction
`cobDir θ X + rescaleDirMlp k θ α` determines `X` and `α`. -/
theorem cobDir_add_rescaleDirMlp_injective_of_rank_D (k : ℕ) (hk : k ≠ 0)
    (θ : Params (Arch.mlp (T := T) (d := d) σ χ hid) dIn dOut)
    (hD : θ.D.rank = Fintype.card d) (hr : ∀ ℓ, (θ.read ℓ).rank = Fintype.card d)
    (ha : ∀ ℓ i, (fun a => θ.write ℓ i a) ≠ 0) :
    Function.Injective fun p : (Fin (L + 1) → Matrix d d ℝ) × (∀ ℓ, hid ℓ → ℝ) =>
      cobDir θ p.1 + rescaleDirMlp k θ p.2 := by
  rintro ⟨X, α⟩ ⟨X', α'⟩ h
  -- the readout component: `X_L D = X'_L D` (the rescalings leave `D` alone), and `D` has
  -- rank `d`
  have hL : X (Fin.last L) = X' (Fin.last L) := by
    have h0 : -(X (Fin.last L) * θ.D) + 0 = -(X' (Fin.last L) * θ.D) + 0 := congrArg Params.D h
    rw [add_zero, add_zero] at h0
    exact mul_right_cancel_of_rank_uri θ.D hD (neg_injective h0)
  -- block `ℓ`: if `X_{ℓ+1} = X'_{ℓ+1}`, then `α_ℓ = α'_ℓ` and `X_ℓ = X'_ℓ`
  have key : ∀ ℓ : Fin L, X ℓ.succ = X' ℓ.succ → α ℓ = α' ℓ ∧ X ℓ.castSucc = X' ℓ.castSucc := by
    intro ℓ hℓ
    -- the write moves by `W X_{ℓ+1} - k diag(α_ℓ) W`, and the first terms agree; an entry `a`
    -- with `a_i a ≠ 0` gives `k α_i = k α'_i`, and `k ≠ 0`
    have hw' := congrArg (fun η => η.write ℓ) h
    change θ.write ℓ * X ℓ.succ + Matrix.of (fun i a => -((k : ℝ) * α ℓ i) * θ.write ℓ i a) =
      θ.write ℓ * X' ℓ.succ + Matrix.of (fun i a => -((k : ℝ) * α' ℓ i) * θ.write ℓ i a) at hw'
    rw [hℓ, add_right_inj] at hw'
    have hα : α ℓ = α' ℓ := by
      funext i
      obtain ⟨a, ha'⟩ := Function.ne_iff.mp (ha ℓ i)
      have hia : -((k : ℝ) * α ℓ i) * θ.write ℓ i a = -((k : ℝ) * α' ℓ i) * θ.write ℓ i a :=
        congrFun (congrFun hw' i) a
      exact mul_left_cancel₀ (Nat.cast_ne_zero.2 hk) (neg_inj.mp (mul_right_cancel₀ ha' hia))
    refine ⟨hα, ?_⟩
    -- the read moves by `-X_ℓ W_read + W_read diag(α_ℓ)`; the second terms agree, and the read
    -- has rank `d`
    have hr' := congrArg (fun η => η.read ℓ) h
    change -(X ℓ.castSucc * θ.read ℓ) + Matrix.of (fun a i => α ℓ i * θ.read ℓ a i) =
      -(X' ℓ.castSucc * θ.read ℓ) + Matrix.of (fun a i => α' ℓ i * θ.read ℓ a i) at hr'
    rw [hα, add_left_inj] at hr'
    exact mul_right_cancel_of_rank_uri (θ.read ℓ) (hr ℓ) (neg_injective hr')
  -- by induction down the network, `X = X'`; then `α = α'`
  have hX : ∀ ℓ : Fin (L + 1), X ℓ = X' ℓ := by
    intro ℓ
    induction ℓ using Fin.reverseInduction with
    | last => exact hL
    | cast ℓ ih => exact (key ℓ ih).2
  exact Prod.ext (funext hX) (funext fun ℓ => (key ℓ (hX ℓ.succ)).1)

/-- Helper: columns in general position, `d ≥ 1`: no column is zero (a single column is
linearly independent). -/
private theorem exists_ne_zero_col_uri {m q : Type*} [Fintype m] (R : Matrix m q ℝ)
    (hgp : ∀ S : Finset q, S.card ≤ Fintype.card m → LinearIndependent ℝ fun j : S => Rᵀ j)
    (hm : 0 < Fintype.card m) (j : q) : ∃ a, R a j ≠ 0 := by
  have h := (hgp {j} (by rw [Finset.card_singleton]; omega)).ne_zero
    ⟨j, Finset.mem_singleton_self j⟩
  obtain ⟨a, ha⟩ := Function.ne_iff.mp h
  exact ⟨a, ha⟩

omit [Fintype T] [Fintype dIn] in
/-- **Lemma A.18, second sentence, for ReGLU blocks, in infinitesimal form.** If `D` has rank
`d`, no row of a write vanishes, and the gate and value columns of every read are in general
position (any `d` of them are linearly independent, and there are more than `d`), the direction
`cobDir θ X + rescaleDir θ α + rescaleDirGate k θ β` determines `X`, `α` and `β`. -/
theorem cobDir_add_rescaleDir_add_rescaleDirGate_injective_of_rank_D (k : ℕ)
    (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut)
    (hD : θ.D.rank = Fintype.card d) (ha : ∀ ℓ i, (fun a => θ.write ℓ i a) ≠ 0)
    (hgp : ∀ ℓ (S : Finset (hid ℓ ⊕ hid ℓ)), S.card ≤ Fintype.card d →
      LinearIndependent ℝ fun j : S => (θ.read ℓ)ᵀ j)
    (hcard : ∀ ℓ, Fintype.card d < Fintype.card (hid ℓ ⊕ hid ℓ)) :
    Function.Injective
      fun p : (Fin (L + 1) → Matrix d d ℝ) × (∀ ℓ, hid ℓ → ℝ) × (∀ ℓ, hid ℓ → ℝ) =>
        cobDir θ p.1 + rescaleDir θ p.2.1 + rescaleDirGate k θ p.2.2 := by
  rintro ⟨X, α, β⟩ ⟨X', α', β'⟩ h
  -- the readout component: `X_L D = X'_L D` (the rescalings leave `D` alone), and `D` has
  -- rank `d`
  have hL : X (Fin.last L) = X' (Fin.last L) := by
    have h0 : -(X (Fin.last L) * θ.D) + 0 + 0 = -(X' (Fin.last L) * θ.D) + 0 + 0 :=
      congrArg Params.D h
    simp only [add_zero] at h0
    exact mul_right_cancel_of_rank_uri θ.D hD (neg_injective h0)
  -- block `ℓ`: if `X_{ℓ+1} = X'_{ℓ+1}`, then `α_ℓ = α'_ℓ`, `β_ℓ = β'_ℓ` and `X_ℓ = X'_ℓ`
  have key : ∀ ℓ : Fin L, X ℓ.succ = X' ℓ.succ →
      α ℓ = α' ℓ ∧ β ℓ = β' ℓ ∧ X ℓ.castSucc = X' ℓ.castSucc := by
    intro ℓ hℓ
    -- the block has a hidden unit `i₀`, and `d ≥ 1` (the write row of `i₀` is not zero)
    have hcs := hcard ℓ
    rw [Fintype.card_sum] at hcs
    obtain ⟨i₀⟩ : Nonempty (hid ℓ) := Fintype.card_pos_iff.mp (by omega)
    obtain ⟨a₀, -⟩ := Function.ne_iff.mp (ha ℓ i₀)
    have hd : 0 < Fintype.card d := Fintype.card_pos_iff.mpr ⟨a₀⟩
    -- the write moves by `W X_{ℓ+1} + diag(α_ℓ - k β_ℓ) W`, and the first terms agree; an entry
    -- `a` with `a_i a ≠ 0` gives `α_i - k β_i = α'_i - k β'_i`
    have hw' := congrArg (fun η => η.write ℓ) h
    change θ.write ℓ * X ℓ.succ + Matrix.of (fun i a => α ℓ i * θ.write ℓ i a)
        + Matrix.of (fun i a => -((k : ℝ) * β ℓ i) * θ.write ℓ i a) =
      θ.write ℓ * X' ℓ.succ + Matrix.of (fun i a => α' ℓ i * θ.write ℓ i a)
        + Matrix.of (fun i a => -((k : ℝ) * β' ℓ i) * θ.write ℓ i a) at hw'
    rw [hℓ, add_assoc, add_assoc, add_right_inj] at hw'
    have hwi : ∀ i, α ℓ i - k * β ℓ i = α' ℓ i - k * β' ℓ i := by
      intro i
      obtain ⟨a, ha'⟩ := Function.ne_iff.mp (ha ℓ i)
      have hia : α ℓ i * θ.write ℓ i a + -((k : ℝ) * β ℓ i) * θ.write ℓ i a =
          α' ℓ i * θ.write ℓ i a + -((k : ℝ) * β' ℓ i) * θ.write ℓ i a :=
        congrFun (congrFun hw' i) a
      rw [← add_mul, ← add_mul] at hia
      linear_combination mul_right_cancel₀ ha' hia
    -- the read: with `Y = X_ℓ - X'_ℓ`, `Y g_i = (β_i - β'_i) g_i` on the gate columns and
    -- `Y e_i = -(α_i - α'_i) e_i` on the value columns
    have hr' := congrArg (fun η => η.read ℓ) h
    change -(X ℓ.castSucc * θ.read ℓ) + Matrix.of (fun a j =>
          Sum.elim (fun _ => 0) (fun i => -(α ℓ i) * θ.read ℓ a (Sum.inr i)) j)
        + Matrix.of (fun a j => Sum.elim (fun i => β ℓ i * θ.read ℓ a (Sum.inl i))
          (fun _ => 0) j) =
      -(X' ℓ.castSucc * θ.read ℓ) + Matrix.of (fun a j =>
          Sum.elim (fun _ => 0) (fun i => -(α' ℓ i) * θ.read ℓ a (Sum.inr i)) j)
        + Matrix.of (fun a j => Sum.elim (fun i => β' ℓ i * θ.read ℓ a (Sum.inl i))
          (fun _ => 0) j) at hr'
    obtain ⟨Y, hY⟩ : ∃ Y, Y = X ℓ.castSucc - X' ℓ.castSucc := ⟨_, rfl⟩
    have hYR : ∀ a j, (Y * θ.read ℓ) a j =
        (X ℓ.castSucc * θ.read ℓ) a j - (X' ℓ.castSucc * θ.read ℓ) a j := by
      intro a j
      rw [hY, Matrix.sub_mul, Matrix.sub_apply]
    have hgate : ∀ a i, (Y * θ.read ℓ) a (Sum.inl i) =
        (β ℓ i - β' ℓ i) * θ.read ℓ a (Sum.inl i) := by
      intro a i
      have e := congrFun (congrFun hr' a) (Sum.inl i)
      simp only [Matrix.add_apply, Matrix.neg_apply, Matrix.of_apply, Sum.elim_inl] at e
      rw [hYR]
      linear_combination -e
    have hval : ∀ a i, (Y * θ.read ℓ) a (Sum.inr i) =
        -(α ℓ i - α' ℓ i) * θ.read ℓ a (Sum.inr i) := by
      intro a i
      have e := congrFun (congrFun hr' a) (Sum.inr i)
      simp only [Matrix.add_apply, Matrix.neg_apply, Matrix.of_apply, Sum.elim_inr] at e
      rw [hYR]
      linear_combination -e
    -- every column is an eigenvector of `Y`, so `Y = μ 1` (general position)
    obtain ⟨μ, hμ⟩ := eq_smul_one_of_eigenvectors_generalPosition (q := hid ℓ ⊕ hid ℓ)
      (fun j => (θ.read ℓ)ᵀ j) (hgp ℓ) (hcard ℓ) Y (by
        rintro (i | i)
        · exact ⟨β ℓ i - β' ℓ i, funext fun a => hgate a i⟩
        · exact ⟨-(α ℓ i - α' ℓ i), funext fun a => hval a i⟩)
    have hYμ : ∀ a j, (Y * θ.read ℓ) a j = μ * θ.read ℓ a j := by
      intro a j
      rw [hμ, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_apply, smul_eq_mul]
    -- no column is zero, so `β_i - β'_i = μ` and `-(α_i - α'_i) = μ` for every `i`
    have hβi : ∀ i, β ℓ i - β' ℓ i = μ := by
      intro i
      obtain ⟨a, ha'⟩ := exists_ne_zero_col_uri (θ.read ℓ) (hgp ℓ) hd (Sum.inl i)
      exact mul_right_cancel₀ ha' ((hgate a i).symm.trans (hYμ a _))
    have hαi : ∀ i, -(α ℓ i - α' ℓ i) = μ := by
      intro i
      obtain ⟨a, ha'⟩ := exists_ne_zero_col_uri (θ.read ℓ) (hgp ℓ) hd (Sum.inr i)
      exact mul_right_cancel₀ ha' ((hval a i).symm.trans (hYμ a _))
    -- so `-μ = k μ` at the unit `i₀`, and `μ = 0`
    have hμ0 : μ = 0 := by
      have h1 : (1 + (k : ℝ)) * μ = 0 := by
        linear_combination -(hαi i₀) - hwi i₀ - (k : ℝ) * hβi i₀
      have h2 : (1 + (k : ℝ)) ≠ 0 := by positivity
      exact (mul_eq_zero.1 h1).resolve_left h2
    refine ⟨funext fun i => ?_, funext fun i => ?_, ?_⟩
    · have := hαi i
      linarith
    · have := hβi i
      linarith
    · rw [← sub_eq_zero, ← hY, hμ, hμ0, zero_smul]
  -- by induction down the network, `X = X'`; then `α = α'` and `β = β'`
  have hX : ∀ ℓ : Fin (L + 1), X ℓ = X' ℓ := by
    intro ℓ
    induction ℓ using Fin.reverseInduction with
    | last => exact hL
    | cast ℓ ih => exact (key ℓ ih).2.2
  exact Prod.ext (funext hX) (Prod.ext (funext fun ℓ => (key ℓ (hX ℓ.succ)).1)
    (funext fun ℓ => (key ℓ (hX ℓ.succ)).2.1))

/-- Helper: a nonzero matrix cancels as the vector of a multiple, `a M = b M → a = b`. -/
private theorem smul_right_cancel_uri {m n : Type*} {M : Matrix m n ℝ} (hM : M ≠ 0) {a b : ℝ}
    (h : a • M = b • M) : a = b := by
  -- an entry of `M` that is not zero
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hM
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hi
  have hij := congrFun (congrFun h i) j
  rw [Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul] at hij
  exact mul_right_cancel₀ hj hij

omit [Fintype T] [DecidableEq d] [Fintype dIn] in
/-- **Lemma A.18, second sentence, for `ε = 0`, in infinitesimal form** (any kind of block). If
`D` and every read have rank `d`, and `E` and every write are not zero, the direction
`cobDir θ Y + scaleDir θ β` determines the matrices `Y_0, …, Y_L` and the numbers
`β_0, …, β_L`. -/
theorem cobDir_add_scaleDir_injective_of_rank_D {A : Arch T d L} (θ : Params A dIn dOut)
    (hD : θ.D.rank = Fintype.card d) (hr : ∀ ℓ, (θ.read ℓ).rank = Fintype.card d)
    (hE : θ.E ≠ 0) (hw : ∀ ℓ, θ.write ℓ ≠ 0) :
    Function.Injective fun p : (Fin (L + 1) → Matrix d d ℝ) × (Fin (L + 1) → ℝ) =>
      cobDir θ p.1 + scaleDir θ p.2 := by
  rintro ⟨Y, β⟩ ⟨Y', β'⟩ h
  -- the scales leave the readout and the reads alone: as in `cobDir_injective_of_rank_D`, the
  -- readout gives `Y_L` and the read of block `ℓ` gives `Y_ℓ`
  have hY : Y = Y' := by
    funext ℓ
    induction ℓ using Fin.lastCases with
    | last =>
      have h0 : -(Y (Fin.last L) * θ.D) + 0 = -(Y' (Fin.last L) * θ.D) + 0 :=
        congrArg Params.D h
      rw [add_zero, add_zero] at h0
      exact mul_right_cancel_of_rank_uri θ.D hD (neg_injective h0)
    | cast ℓ =>
      have h1 : -(Y ℓ.castSucc * θ.read ℓ) + 0 = -(Y' ℓ.castSucc * θ.read ℓ) + 0 :=
        congrArg (fun η => η.read ℓ) h
      rw [add_zero, add_zero] at h1
      exact mul_right_cancel_of_rank_uri (θ.read ℓ) (hr ℓ) (neg_injective h1)
  subst Y'
  -- then the embedding moves by `E Y_0 + β_0 E`, the write of block `ℓ` by
  -- `W Y_{ℓ+1} + β_{ℓ+1} W`; the first terms agree, and `E`, `W` are not zero
  have h0 : θ.E * Y 0 + β 0 • θ.E = θ.E * Y 0 + β' 0 • θ.E := congrArg Params.E h
  have hwr : ∀ ℓ : Fin L, θ.write ℓ * Y ℓ.succ + β ℓ.succ • θ.write ℓ
      = θ.write ℓ * Y ℓ.succ + β' ℓ.succ • θ.write ℓ := fun ℓ =>
    congrArg (fun η => η.write ℓ) h
  refine Prod.ext rfl (funext fun ℓ => ?_)
  cases ℓ using Fin.cases with
  | zero => exact smul_right_cancel_uri hE (add_left_cancel h0)
  | succ ℓ => exact smul_right_cancel_uri (hw ℓ) (add_left_cancel (hwr ℓ))

end Skips
