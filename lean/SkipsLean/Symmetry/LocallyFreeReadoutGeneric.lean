import SkipsLean.Symmetry.LocallyFreeReadout
import SkipsLean.Generic.Params
import SkipsLean.Generic.Gated

/-!
# Locally free action at generic parameters (the form with the readout)

Paper (skips paper), Lemma A.18 (Locally free action): "The same holds if the readout has rank
`d_model` and every block has width at least `d_model`", where "the same" is "at generic
parameters the changes of basis and the symmetries inside blocks act locally freely". Its proof:
"rescalings act freely on the rows of a generic write […]; each read, of rank `d_model` and with
generic columns, then forces `G_{ℓ−1} = I` and the remaining scales to be 1."

`Symmetry/LocallyFreeReadout.lean` states, at one parameter with rank conditions, that changes of
basis and rescalings that fix `θ` are the identity. Here the same **at almost every `θ`**, for
`d_out ≥ d ≥ 1` and blocks of width at least `d` (`Symmetry/LocallyFreeGeneric.lean` has the form
with the embedding, for `d_in ≥ d`). The conditions at generic parameters are stated first, the
twins of `ae_rank_E_write`, `ae_read_col_ne_zero`:

* `ae_rank_D_read`: `D` and every read have rank `d` (`d_out ≥ d`, reads with at least `d`
  columns);
* `ae_write_row_ne_zero`: no row of a write is zero (`d ≥ 1`);
* `ae_read_cols_generalPosition`: any `d` columns of a read are linearly independent (reads with
  at least `d` columns), from `ae_isUnit_det_submatrix`.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {σ : ℝ → ℝ} {χ : Matrix T d ℝ → Matrix T d ℝ} {hid : Fin L → Type}
  [∀ ℓ, Fintype (hid ℓ)]

/-- Helper (the column twin of the private `rank_eq_of_isUnit_det_submatrix` of
`Generic/Params.lean`): a matrix with `d` rows has rank `d` if some `d` of its columns form an
invertible matrix (rank at most the height, and at least the rank of a submatrix). -/
private theorem rank_eq_of_isUnit_det_submatrix_cols_lrg {m : Type*} [Fintype m]
    (M : Matrix d m ℝ) (c : d ↪ m) (h : IsUnit (M.submatrix id c).det) :
    M.rank = Fintype.card d :=
  le_antisymm (Matrix.rank_le_card_height M)
    ((Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).2 h)).symm.le.trans
      (Matrix.rank_submatrix_le M id c))

/-- At generic parameters `D` and every read have rank `d`, when `d_out ≥ d` and every read has
at least `d` columns (the twin of `ae_rank_E_write`). -/
theorem ae_rank_D_read {A : Arch T d L} (μ : Measure (Params A dIn dOut)) [μ.IsAddHaarMeasure]
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hr : ∀ ℓ, Fintype.card d ≤ Fintype.card (A.r ℓ)) :
    ∀ᵐ θ ∂μ, θ.D.rank = Fintype.card d ∧ ∀ ℓ, (θ.read ℓ).rank = Fintype.card d := by
  -- `d` columns of `D` and of each read, invertible at generic parameters
  obtain ⟨c⟩ := Function.Embedding.nonempty_of_card_le hdOut
  filter_upwards [ae_isUnit_det_submatrix μ] with θ hθ
  refine ⟨rank_eq_of_isUnit_det_submatrix_cols_lrg θ.D c (hθ.2.1 c), fun ℓ => ?_⟩
  obtain ⟨c'⟩ := Function.Embedding.nonempty_of_card_le (hr ℓ)
  exact rank_eq_of_isUnit_det_submatrix_cols_lrg (θ.read ℓ) c' (hθ.1 ℓ c')

/-- At generic parameters no row of a write vanishes (`d ≥ 1`; any kind of block). -/
theorem ae_write_row_ne_zero [Nonempty d] {A : Arch T d L} (μ : Measure (Params A dIn dOut))
    [μ.IsAddHaarMeasure] : ∀ᵐ θ ∂μ, ∀ ℓ i, (fun a => θ.write ℓ i a) ≠ 0 := by
  -- finitely many conditions, one for each row `i` of each write `ℓ`
  refine ae_all_iff.2 fun ℓ => ae_all_iff.2 fun i => ?_
  -- an entry `a₀` of the row
  obtain a₀ : d := Classical.arbitrary d
  -- the entry `θ ↦ θ.write ℓ i a₀` is a linear functional of the parameters
  let l : Params A dIn dOut →ₗ[ℝ] ℝ :=
    (Matrix.entryLinearMap ℝ ℝ i a₀).comp (Params.linWrite (A := A) (dIn := dIn) (dOut := dOut) ℓ)
  have hl : ∀ θ, l θ = θ.write ℓ i a₀ := fun θ => rfl
  -- it is not zero at the parameters whose writes have all entries `1`
  have h₁ : l ⟨0, 0, fun _ => Matrix.of fun _ _ => 1, 0⟩ ≠ 0 := by
    rw [hl]
    exact one_ne_zero
  -- an analytic function that is not identically zero is nonzero almost everywhere
  have hne : ∀ᵐ θ ∂μ, l θ ≠ 0 :=
    ae_ne_zero_of_analytic μ (analyticOnNhd_linear l) ⟨_, h₁⟩
  -- and a row with a nonzero entry is not zero
  filter_upwards [hne] with θ h hz
  exact h (by rw [hl]; exact congrFun hz a₀)

/-- At generic parameters the columns of every read are in general position: any `d` of them
are linearly independent, when the read has at least `d` columns. -/
theorem ae_read_cols_generalPosition {A : Arch T d L} (μ : Measure (Params A dIn dOut))
    [μ.IsAddHaarMeasure] (hr : ∀ ℓ, Fintype.card d ≤ Fintype.card (A.r ℓ)) :
    ∀ᵐ θ ∂μ, ∀ ℓ (S : Finset (A.r ℓ)), S.card ≤ Fintype.card d →
      LinearIndependent ℝ fun j : S => (θ.read ℓ)ᵀ (j : A.r ℓ) := by
  filter_upwards [ae_isUnit_det_submatrix μ] with θ hθ ℓ S hS
  classical
  -- `S` lies in a set `S'` of exactly `d` columns
  obtain ⟨S', hSS', -, hS'⟩ := Finset.exists_subsuperset_card_eq (Finset.subset_univ S) hS
    (by rw [Finset.card_univ]; exact hr ℓ)
  -- the columns `S'`, numbered by `d`
  have e : d ≃ S' := Fintype.equivOfCardEq (by rw [Fintype.card_coe, hS'])
  let c : d ↪ A.r ℓ := e.toEmbedding.trans (Function.Embedding.subtype _)
  -- the columns `c` form an invertible matrix, so they are linearly independent
  have hli : LinearIndependent ℝ fun k : d => (θ.read ℓ)ᵀ (c k) :=
    Matrix.linearIndependent_cols_of_det_ne_zero (hθ.1 ℓ c).ne_zero
  -- the columns `S` are some of them
  have hcomp : (fun j : S => (θ.read ℓ)ᵀ (j : A.r ℓ)) =
      (fun k : d => (θ.read ℓ)ᵀ (c k)) ∘ fun j : S => e.symm ⟨j, hSS' j.2⟩ := by
    funext j
    simp [c]
  rw [hcomp]
  refine hli.comp _ fun j j' hjj' => ?_
  have h := congrArg Subtype.val (e.symm.injective hjj')
  exact Subtype.ext h

/-- **Lemma A.18, second sentence, at generic parameters, the changes of basis** (any kind of
block whose read has at least `d` columns; `d_out ≥ d`): at almost every `θ`, changes of basis
that fix `θ` (`θ.cob G K = θ`) have `K = 1`. -/
theorem ae_cob_eq_self_of_dOut {A : Arch T d L} (μ : Measure (Params A dIn dOut))
    [μ.IsAddHaarMeasure] (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hr : ∀ ℓ, Fintype.card d ≤ Fintype.card (A.r ℓ)) :
    ∀ᵐ θ ∂μ, ∀ G K : Fin (L + 1) → GL d ℝ, θ.cob G K = θ → K = 1 := by
  filter_upwards [ae_rank_D_read μ hdOut hr] with θ hθ G K h
  exact cob_eq_self_of_rank_D θ G K hθ.1 hθ.2 h

/-- **Lemma A.18, second sentence, at generic parameters, ReLU and ReLU² blocks** (any
activation, degree `k ≠ 0`; `d_out ≥ d ≥ 1`, at least `d` hidden units): at almost every `θ`,
changes of basis `G` with positive rescalings `c` of the hidden units that fix `θ` are the
identity. -/
theorem ae_cob_rescaleMlp_eq_self_of_dOut [Nonempty d] (k : ℕ) (hk : k ≠ 0)
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) σ χ hid) dIn dOut)) [μ.IsAddHaarMeasure]
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hw : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, ∀ (G : Fin (L + 1) → GL d ℝ) (c : ∀ ℓ, hid ℓ → ℝ), (∀ ℓ i, 0 < c ℓ i) →
      (θ.cob G G).rescaleMlp k c = θ → G = 1 ∧ ∀ ℓ i, c ℓ i = 1 := by
  filter_upwards [ae_rank_D_read μ hdOut hw, ae_write_row_ne_zero μ] with θ hθ ha G c hc h
  exact cob_rescaleMlp_eq_self_of_rank_D k hk θ G c hc hθ.1 hθ.2 ha h

/-- **Lemma A.18, second sentence, at generic parameters, gated blocks with any gate**
(`d_out ≥ d ≥ 1`, at least `d` hidden units): at almost every `θ`, changes of basis `G` with
rescalings `c` of the values that fix `θ` are the identity. -/
theorem ae_cob_rescale_eq_self_of_dOut [Nonempty d]
    (μ : Measure (Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut)) [μ.IsAddHaarMeasure]
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hw : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, ∀ (G : Fin (L + 1) → GL d ℝ) (c : ∀ ℓ, hid ℓ → ℝ),
      (θ.cob G G).rescale c = θ → G = 1 ∧ ∀ ℓ i, c ℓ i = 1 := by
  -- the reads have the `2 s_ℓ ≥ d` columns `hid ℓ ⊕ hid ℓ`
  have hr : ∀ ℓ, Fintype.card d
      ≤ Fintype.card ((Arch.gated (T := T) (d := d) σ χ hid).r ℓ) := fun ℓ => by
    show Fintype.card d ≤ Fintype.card (hid ℓ ⊕ hid ℓ)
    rw [Fintype.card_sum]
    exact (hw ℓ).trans (Nat.le_add_right _ _)
  filter_upwards [ae_rank_D_read μ hdOut hr, ae_write_row_ne_zero μ] with θ hθ ha G c h
  exact cob_rescale_eq_self_of_rank_D θ G c hθ.1 hθ.2 ha h

/-- **Lemma A.18, second sentence, at generic parameters, ReGLU blocks** (any gate and any degree
`k`; `d_out ≥ d ≥ 1`, at least `d` hidden units): at almost every `θ`, changes of basis `G` with
rescalings `c'` of the values and positive rescalings `c` of the gates that fix `θ` are the
identity. -/
theorem ae_cob_rescale_rescaleGate_eq_self_of_dOut [Nonempty d] (k : ℕ)
    (μ : Measure (Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut)) [μ.IsAddHaarMeasure]
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hw : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, ∀ (G : Fin (L + 1) → GL d ℝ) (c c' : ∀ ℓ, hid ℓ → ℝ), (∀ ℓ i, 0 < c ℓ i) →
      ((θ.cob G G).rescale c').rescaleGate k c = θ →
        G = 1 ∧ (∀ ℓ i, c ℓ i = 1) ∧ ∀ ℓ i, c' ℓ i = 1 := by
  -- the reads have `2 s_ℓ > d` columns `hid ℓ ⊕ hid ℓ`, since `s_ℓ ≥ d ≥ 1`
  have hcard : ∀ ℓ, Fintype.card d < Fintype.card (hid ℓ ⊕ hid ℓ) := fun ℓ => by
    rw [Fintype.card_sum]
    have h0 : 0 < Fintype.card d := Fintype.card_pos
    have h1 := hw ℓ
    omega
  have hr : ∀ ℓ, Fintype.card d
      ≤ Fintype.card ((Arch.gated (T := T) (d := d) σ χ hid).r ℓ) := fun ℓ => (hcard ℓ).le
  filter_upwards [ae_rank_D_read μ hdOut hr, ae_write_row_ne_zero μ,
    ae_read_cols_generalPosition μ hr] with θ hθ ha hgp G c c' hc h
  exact cob_rescale_rescaleGate_eq_self_of_rank_D k θ G c c' hc hθ.1 ha hgp hcard h

omit [Fintype T] [DecidableEq d] in
/-- Helper: at generic parameters `E` is not zero (`d_in ≥ 1`, `d ≥ 1`): its entry `(i₀, a₀)` is
a nonzero linear functional of the parameters. -/
private theorem ae_E_ne_zero_lrg [Nonempty d] [Nonempty dIn] {A : Arch T d L}
    (μ : Measure (Params A dIn dOut)) [μ.IsAddHaarMeasure] : ∀ᵐ θ ∂μ, θ.E ≠ 0 := by
  obtain i₀ : dIn := Classical.arbitrary dIn
  obtain a₀ : d := Classical.arbitrary d
  -- the entry `θ ↦ θ.E i₀ a₀` is a linear functional of the parameters
  let l : Params A dIn dOut →ₗ[ℝ] ℝ :=
    (Matrix.entryLinearMap ℝ ℝ i₀ a₀).comp (Params.linE (A := A) (dIn := dIn) (dOut := dOut))
  have hl : ∀ θ, l θ = θ.E i₀ a₀ := fun θ => rfl
  -- it is not zero at the parameter whose embedding has all entries `1`
  have h₁ : l ⟨Matrix.of fun _ _ => 1, 0, 0, 0⟩ ≠ 0 := by
    rw [hl]
    exact one_ne_zero
  have hne : ∀ᵐ θ ∂μ, l θ ≠ 0 :=
    ae_ne_zero_of_analytic μ (analyticOnNhd_linear l) ⟨_, h₁⟩
  filter_upwards [hne] with θ h hz
  exact h (by rw [hl, hz]; rfl)

/-- **Lemma A.18, second sentence, at generic parameters, under pre-RMSNorm with `ε = 0`** (any
kind of block whose read has at least `d` columns and whose write has a row; `d_out ≥ d ≥ 1`,
`d_in ≥ 1`): at almost every `θ`, changes of basis `G_ℓ = c_ℓ Q_ℓ` (the writes multiplied by
`G_ℓ`, the reads by `Q_ℓ⁻¹`) that fix `θ` have `c_ℓ = 1` and `Q_ℓ = 1`. -/
theorem ae_cob_rmsNorm_zero_eq_self_of_dOut [Nonempty d] [Nonempty dIn] {A : Arch T d L}
    (μ : Measure (Params A dIn dOut)) [μ.IsAddHaarMeasure]
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hr : ∀ ℓ, Fintype.card d ≤ Fintype.card (A.r ℓ)) (hw : ∀ ℓ, Nonempty (A.w ℓ)) :
    ∀ᵐ θ ∂μ, ∀ (G Q : Fin (L + 1) → GL d ℝ) (c : Fin (L + 1) → ℝ),
      (∀ ℓ, (G ℓ : Matrix d d ℝ) = c ℓ • (Q ℓ : Matrix d d ℝ)) → θ.cob G Q = θ →
        (∀ ℓ, c ℓ = 1) ∧ Q = 1 := by
  -- a write with a row has a nonzero row, at generic parameters
  have hw0 : ∀ᵐ θ ∂μ, ∀ ℓ, θ.write ℓ ≠ 0 := by
    filter_upwards [ae_write_row_ne_zero μ] with θ ha ℓ h0
    obtain ⟨i⟩ := hw ℓ
    exact ha ℓ i (funext fun a => by rw [h0]; rfl)
  filter_upwards [ae_rank_D_read μ hdOut hr, ae_E_ne_zero_lrg μ, hw0] with θ hθ hE hw' G Q c hG h
  exact cob_rmsNorm_zero_eq_self_of_rank_D θ G Q c hG hθ.1 hθ.2 hE hw' h

end Skips
