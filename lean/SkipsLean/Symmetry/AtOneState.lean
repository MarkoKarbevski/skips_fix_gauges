import SkipsLean.Generic.Params

/-!
# The change of basis at one hidden state

Paper (dimension): Definition 3.1, and Proposition 3.3 with the paragraph after it, in the form of
the paper: one hidden state, and a hypothesis on the read of that hidden state only.
`Symmetry/Reduction.lean` has the reductions at all `L + 1` hidden states at once, which need the
hypothesis at every hidden state.

Indices: the Lean block `ℓ : Fin L` is the paper's block `ℓ + 1`. It reads the hidden state
`ℓ.castSucc` and writes into the hidden state `ℓ.succ`. The embedding writes into the hidden state
`0`, and the readout reads the hidden state `Fin.last L`.

A choice of `d` columns of a read is a map `c : d → r`, and the chosen columns form the square
matrix `W.submatrix id c`; a choice of `d` rows of a write is a map `ρ : d → w`, and the chosen
rows form `W.submatrix ρ id` (as in `Symmetry/Reduction.lean`). The hypothesis "the chosen columns
form an invertible matrix `W₁`" is written `(W₁ : GL d ℝ)` with
`(W₁ : Matrix d d ℝ) = W.submatrix id c`.
-/

namespace Skips

open Matrix MeasureTheory

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype d] [DecidableEq d]
variable {A : Arch T d L}

/-- **Definition 3.1.** The change of basis `G` at the hidden state `h_j`: `W ↦ W G` for the
writes into `h_j` and `W ↦ G⁻¹ W` for the reads of `h_j`; the other weights stay as they are. It
is `Params.cob` with `G` at `j` and the identity at the other hidden states. The eight statements
`Params.cobAt_*` below say what it does to each weight. -/
def Params.cobAt (θ : Params A dIn dOut) (j : Fin (L + 1)) (G : GL d ℝ) : Params A dIn dOut :=
  θ.cob (Function.update (fun _ => 1) j G) (Function.update (fun _ => 1) j G)

variable (θ : Params A dIn dOut) (G : GL d ℝ)

/-- The embedding writes into `h_0`: the change of basis `G` at `h_0` maps `E ↦ E G`. -/
theorem Params.cobAt_E_zero : (θ.cobAt 0 G).E = θ.E * (G : Matrix d d ℝ) := by
  simp [Params.cobAt, Params.cob]

/-- A change of basis at a hidden state other than `h_0` leaves the embedding as it is. -/
theorem Params.cobAt_E_of_ne {j : Fin (L + 1)} (hj : j ≠ 0) : (θ.cobAt j G).E = θ.E := by
  simp [Params.cobAt, Params.cob, Function.update_of_ne hj.symm]

/-- Block `ℓ` reads `h_{ℓ.castSucc}`: the change of basis `G` there maps its read `W ↦ G⁻¹ W`. -/
theorem Params.cobAt_read_castSucc (ℓ : Fin L) :
    (θ.cobAt ℓ.castSucc G).read ℓ = (↑G⁻¹ : Matrix d d ℝ) * θ.read ℓ := by
  simp [Params.cobAt, Params.cob]

/-- A change of basis at a hidden state that block `ℓ` does not read leaves its read as it is. -/
theorem Params.cobAt_read_of_ne {j : Fin (L + 1)} (ℓ : Fin L) (hj : j ≠ ℓ.castSucc) :
    (θ.cobAt j G).read ℓ = θ.read ℓ := by
  simp [Params.cobAt, Params.cob, Function.update_of_ne hj.symm]

/-- Block `ℓ` writes into `h_{ℓ.succ}`: the change of basis `G` there maps its write
`W ↦ W G`. -/
theorem Params.cobAt_write_succ (ℓ : Fin L) :
    (θ.cobAt ℓ.succ G).write ℓ = θ.write ℓ * (G : Matrix d d ℝ) := by
  simp [Params.cobAt, Params.cob]

/-- A change of basis at a hidden state that block `ℓ` does not write into leaves its write as it
is. -/
theorem Params.cobAt_write_of_ne {j : Fin (L + 1)} (ℓ : Fin L) (hj : j ≠ ℓ.succ) :
    (θ.cobAt j G).write ℓ = θ.write ℓ := by
  simp [Params.cobAt, Params.cob, Function.update_of_ne hj.symm]

/-- The readout reads `h_L`: the change of basis `G` at `h_L` maps `D ↦ G⁻¹ D`. -/
theorem Params.cobAt_D_last :
    (θ.cobAt (Fin.last L) G).D = (↑G⁻¹ : Matrix d d ℝ) * θ.D := by
  simp [Params.cobAt, Params.cob]

/-- A change of basis at a hidden state other than `h_L` leaves the readout as it is. -/
theorem Params.cobAt_D_of_ne {j : Fin (L + 1)} (hj : j ≠ Fin.last L) : (θ.cobAt j G).D = θ.D := by
  simp [Params.cobAt, Params.cob, Function.update_of_ne hj.symm]

variable [Fintype dIn]

/-- **Proposition 3.2 for one hidden state, without normalization:** the change of basis `G` at
`h_j` preserves the function. -/
theorem eval_cobAt_skipless (hA : A.χ = id) (j : Fin (L + 1)) (x : Matrix T dIn ℝ) :
    eval A 0 (θ.cobAt j G) x = eval A 0 θ x :=
  -- Proposition 3.2 with `G` at `j` and the identity at the other hidden states
  eval_cob_skipless θ _ x hA

/-- **Proposition 3.2 for one hidden state, under pre-RMSNorm:** the change of basis `Q` at `h_j`
preserves the function if `Q` is orthogonal. -/
theorem eval_cobAt_rmsNorm (ε : ℝ) (hA : A.χ = rmsNorm ε) (j : Fin (L + 1))
    (hG : (G : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ) (x : Matrix T dIn ℝ) :
    eval A 0 (θ.cobAt j G) x = eval A 0 θ x := by
  -- Proposition 3.2 with `G` at `j` and the identity at the other hidden states; both are
  -- orthogonal.
  refine eval_cob_rmsNorm θ x ε hA _ fun i => ?_
  by_cases h : i = j
  · subst h
    rw [Function.update_self]
    exact hG
  · rw [Function.update_of_ne h, Units.val_one]
    exact one_mem _

/-- **Proposition 3.3 (i), for the hidden state that a block reads.** Without normalization, if
the chosen `d` columns of the read of block `ℓ` form an invertible matrix `W₁`, the change of
basis `G = W₁` at the hidden state that the block reads preserves the function and turns `W₁`
into `G⁻¹ W₁ = I`. -/
theorem cobAt_read_eq_one (hA : A.χ = id) (ℓ : Fin L) (c : d → A.r ℓ) (W₁ : GL d ℝ)
    (hW : (W₁ : Matrix d d ℝ) = (θ.read ℓ).submatrix id c) :
    (∀ x : Matrix T dIn ℝ, eval A 0 (θ.cobAt ℓ.castSucc W₁) x = eval A 0 θ x) ∧
      ((θ.cobAt ℓ.castSucc W₁).read ℓ).submatrix id c = 1 := by
  refine ⟨fun x => eval_cobAt_skipless θ W₁ hA _ x, ?_⟩
  -- the chosen columns of `W₁⁻¹ W_read` are `W₁⁻¹ W₁ = 1`
  rw [θ.cobAt_read_castSucc, Matrix.submatrix_mul _ _ id id c Function.bijective_id,
    Matrix.submatrix_id_id, ← hW, Units.inv_mul]

/-- **Proposition 3.3 (i), for the last hidden state.** Without normalization, if the chosen `d`
columns of the readout `D` form an invertible matrix `W₁`, the change of basis `G = W₁` at `h_L`
preserves the function and turns `W₁` into `G⁻¹ W₁ = I`. -/
theorem cobAt_D_eq_one (hA : A.χ = id) (cD : d → dOut) (W₁ : GL d ℝ)
    (hW : (W₁ : Matrix d d ℝ) = θ.D.submatrix id cD) :
    (∀ x : Matrix T dIn ℝ, eval A 0 (θ.cobAt (Fin.last L) W₁) x = eval A 0 θ x) ∧
      (θ.cobAt (Fin.last L) W₁).D.submatrix id cD = 1 := by
  refine ⟨fun x => eval_cobAt_skipless θ W₁ hA _ x, ?_⟩
  -- the chosen columns of `W₁⁻¹ D` are `W₁⁻¹ W₁ = 1`
  rw [θ.cobAt_D_last, Matrix.submatrix_mul _ _ id id cD Function.bijective_id,
    Matrix.submatrix_id_id, ← hW, Units.inv_mul]

/-- **Proposition 3.3 (ii), for the hidden state that a block reads.** Under pre-RMSNorm, if the
chosen `d` columns of the read of block `ℓ` form a matrix `W₁ = Q R` with `Q` orthogonal, the
change of basis `Q` at the hidden state that the block reads preserves the function and turns
`W₁` into `Qᵀ W₁ = R`. The paper takes `W₁` invertible and `R` upper triangular; the statement
uses neither, and `exists_orthogonal_transpose_mul_upperTriangular` gives such `Q` and `R` for
every `W₁`. -/
theorem cobAt_read_eq_of_qr (ε : ℝ) (hA : A.χ = rmsNorm ε) (ℓ : Fin L) (c : d → A.r ℓ)
    (Q : GL d ℝ) (hQ : (Q : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ) (R : Matrix d d ℝ)
    (hQR : (θ.read ℓ).submatrix id c = (Q : Matrix d d ℝ) * R) :
    (∀ x : Matrix T dIn ℝ, eval A 0 (θ.cobAt ℓ.castSucc Q) x = eval A 0 θ x) ∧
      ((θ.cobAt ℓ.castSucc Q).read ℓ).submatrix id c = R := by
  refine ⟨fun x => eval_cobAt_rmsNorm θ Q ε hA _ hQ x, ?_⟩
  -- the chosen columns of `Q⁻¹ W_read` are `Q⁻¹ (Q R) = R`
  rw [θ.cobAt_read_castSucc, Matrix.submatrix_mul _ _ id id c Function.bijective_id,
    Matrix.submatrix_id_id, hQR, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]

/-- **Proposition 3.3 (ii), for the last hidden state.** Under pre-RMSNorm, if the chosen `d`
columns of the readout `D` form a matrix `W₁ = Q R` with `Q` orthogonal, the change of basis `Q`
at `h_L` preserves the function and turns `W₁` into `Qᵀ W₁ = R`. -/
theorem cobAt_D_eq_of_qr (ε : ℝ) (hA : A.χ = rmsNorm ε) (cD : d → dOut)
    (Q : GL d ℝ) (hQ : (Q : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ) (R : Matrix d d ℝ)
    (hQR : θ.D.submatrix id cD = (Q : Matrix d d ℝ) * R) :
    (∀ x : Matrix T dIn ℝ, eval A 0 (θ.cobAt (Fin.last L) Q) x = eval A 0 θ x) ∧
      (θ.cobAt (Fin.last L) Q).D.submatrix id cD = R := by
  refine ⟨fun x => eval_cobAt_rmsNorm θ Q ε hA _ hQ x, ?_⟩
  -- the chosen columns of `Q⁻¹ D` are `Q⁻¹ (Q R) = R`
  rw [θ.cobAt_D_last, Matrix.submatrix_mul _ _ id id cD Function.bijective_id,
    Matrix.submatrix_id_id, hQR, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]

/-- **The rows of a write, without normalization** (the paragraph after Proposition 3.3, and
Example A.2). If the chosen `d` rows of the write of block `ℓ` form an invertible matrix `W₁`, the
change of basis `G = W₁⁻¹` at the hidden state that the block writes into preserves the function
and turns `W₁` into `W₁ G = I`. -/
theorem cobAt_write_eq_one (hA : A.χ = id) (ℓ : Fin L) (ρ : d → A.w ℓ) (W₁ : GL d ℝ)
    (hW : (W₁ : Matrix d d ℝ) = (θ.write ℓ).submatrix ρ id) :
    (∀ x : Matrix T dIn ℝ, eval A 0 (θ.cobAt ℓ.succ W₁⁻¹) x = eval A 0 θ x) ∧
      ((θ.cobAt ℓ.succ W₁⁻¹).write ℓ).submatrix ρ id = 1 := by
  refine ⟨fun x => eval_cobAt_skipless θ W₁⁻¹ hA _ x, ?_⟩
  -- the chosen rows of `W_write W₁⁻¹` are `W₁ W₁⁻¹ = 1`
  rw [θ.cobAt_write_succ, Matrix.submatrix_mul _ _ ρ id id Function.bijective_id,
    Matrix.submatrix_id_id, ← hW, Units.mul_inv]

/-- **The rows of the embedding, without normalization** (the paragraph after Proposition 3.3:
"or rows of `E` if `ℓ = 0`"). If the chosen `d` rows of `E` form an invertible matrix `W₁`, the
change of basis `G = W₁⁻¹` at `h_0` preserves the function and turns `W₁` into `W₁ G = I`. -/
theorem cobAt_E_eq_one (hA : A.χ = id) (ρE : d → dIn) (W₁ : GL d ℝ)
    (hW : (W₁ : Matrix d d ℝ) = θ.E.submatrix ρE id) :
    (∀ x : Matrix T dIn ℝ, eval A 0 (θ.cobAt 0 W₁⁻¹) x = eval A 0 θ x) ∧
      (θ.cobAt 0 W₁⁻¹).E.submatrix ρE id = 1 := by
  refine ⟨fun x => eval_cobAt_skipless θ W₁⁻¹ hA _ x, ?_⟩
  -- the chosen rows of `E W₁⁻¹` are `W₁ W₁⁻¹ = 1`
  rw [θ.cobAt_E_zero, Matrix.submatrix_mul _ _ ρE id id Function.bijective_id,
    Matrix.submatrix_id_id, ← hW, Units.mul_inv]

/-- **The rows of a write, under pre-RMSNorm** (proof of Proposition 3.3: "For a write, let
`W₁ᵀ = Q R`; then `W₁ = Rᵀ Qᵀ`, and the change of basis `Q` gives `W₁ Q = Rᵀ`"). If the chosen
`d` rows of the write of block `ℓ` form a matrix `W₁` with `W₁ᵀ = Q R` and `Q` orthogonal, the
change of basis `Q` at the hidden state that the block writes into preserves the function and
turns `W₁` into `Rᵀ`, which is lower triangular when `R` is upper triangular. -/
theorem cobAt_write_eq_of_qr (ε : ℝ) (hA : A.χ = rmsNorm ε) (ℓ : Fin L) (ρ : d → A.w ℓ)
    (Q : GL d ℝ) (hQ : (Q : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ) (R : Matrix d d ℝ)
    (hQR : ((θ.write ℓ).submatrix ρ id)ᵀ = (Q : Matrix d d ℝ) * R) :
    (∀ x : Matrix T dIn ℝ, eval A 0 (θ.cobAt ℓ.succ Q) x = eval A 0 θ x) ∧
      ((θ.cobAt ℓ.succ Q).write ℓ).submatrix ρ id = Rᵀ := by
  refine ⟨fun x => eval_cobAt_rmsNorm θ Q ε hA _ hQ x, ?_⟩
  -- `W₁ = (Q R)ᵀ = Rᵀ Qᵀ`
  have hW : (θ.write ℓ).submatrix ρ id = Rᵀ * (Q : Matrix d d ℝ)ᵀ := by
    rw [← Matrix.transpose_mul, ← hQR, Matrix.transpose_transpose]
  -- `Qᵀ Q = 1`, since `Q` is orthogonal
  have hQQ : (Q : Matrix d d ℝ)ᵀ * (Q : Matrix d d ℝ) = 1 :=
    (Matrix.mem_orthogonalGroup_iff' d ℝ).mp hQ
  -- the chosen rows of `W_write Q` are `W₁ Q = Rᵀ Qᵀ Q = Rᵀ`
  rw [θ.cobAt_write_succ, Matrix.submatrix_mul _ _ ρ id id Function.bijective_id,
    Matrix.submatrix_id_id, hW, Matrix.mul_assoc, hQQ, Matrix.mul_one]

/-- **The rows of the embedding, under pre-RMSNorm.** If the chosen `d` rows of `E` form a matrix
`W₁` with `W₁ᵀ = Q R` and `Q` orthogonal, the change of basis `Q` at `h_0` preserves the function
and turns `W₁` into `Rᵀ`. -/
theorem cobAt_E_eq_of_qr (ε : ℝ) (hA : A.χ = rmsNorm ε) (ρE : d → dIn)
    (Q : GL d ℝ) (hQ : (Q : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ) (R : Matrix d d ℝ)
    (hQR : (θ.E.submatrix ρE id)ᵀ = (Q : Matrix d d ℝ) * R) :
    (∀ x : Matrix T dIn ℝ, eval A 0 (θ.cobAt 0 Q) x = eval A 0 θ x) ∧
      (θ.cobAt 0 Q).E.submatrix ρE id = Rᵀ := by
  refine ⟨fun x => eval_cobAt_rmsNorm θ Q ε hA _ hQ x, ?_⟩
  -- `W₁ = (Q R)ᵀ = Rᵀ Qᵀ`
  have hW : θ.E.submatrix ρE id = Rᵀ * (Q : Matrix d d ℝ)ᵀ := by
    rw [← Matrix.transpose_mul, ← hQR, Matrix.transpose_transpose]
  -- `Qᵀ Q = 1`, since `Q` is orthogonal
  have hQQ : (Q : Matrix d d ℝ)ᵀ * (Q : Matrix d d ℝ) = 1 :=
    (Matrix.mem_orthogonalGroup_iff' d ℝ).mp hQ
  -- the chosen rows of `E Q` are `W₁ Q = Rᵀ Qᵀ Q = Rᵀ`
  rw [θ.cobAt_E_zero, Matrix.submatrix_mul _ _ ρE id id Function.bijective_id,
    Matrix.submatrix_id_id, hW, Matrix.mul_assoc, hQQ, Matrix.mul_one]

section Generic

variable [Fintype T] [Fintype dOut]
variable (μ : Measure (Params A dIn dOut)) [μ.IsAddHaarMeasure]

/-- **Proposition 3.3, "at generic parameters every hidden state has such columns".** If every
read has at least `d` columns (for an MLP block: `d_hidden ≥ d`) and `d_out ≥ d`, then at generic
parameters every read and the readout have `d` columns that form an invertible matrix. -/
theorem ae_exists_isUnit_det_submatrix_cols
    (hr : ∀ ℓ, Fintype.card d ≤ Fintype.card (A.r ℓ))
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, (∀ ℓ : Fin L, ∃ c : d → A.r ℓ, IsUnit ((θ.read ℓ).submatrix id c).det) ∧
      ∃ cD : d → dOut, IsUnit (θ.D.submatrix id cD).det := by
  -- at generic parameters every choice of `d` distinct columns works, and there is such a choice
  filter_upwards [ae_isUnit_det_submatrix μ] with θ hθ
  obtain ⟨hread, hD, -, -⟩ := hθ
  refine ⟨fun ℓ => ?_, ?_⟩
  · obtain ⟨c⟩ := Function.Embedding.nonempty_of_card_le (hr ℓ)
    exact ⟨c, hread ℓ c⟩
  · obtain ⟨c⟩ := Function.Embedding.nonempty_of_card_le hdOut
    exact ⟨c, hD c⟩

/-- **The rows, at generic parameters** (the paragraph after Proposition 3.3). If `d_in ≥ d` and
every write has at least `d` rows, then at generic parameters the embedding and every write have
`d` rows that form an invertible matrix. -/
theorem ae_exists_isUnit_det_submatrix_rows
    (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hw : ∀ ℓ, Fintype.card d ≤ Fintype.card (A.w ℓ)) :
    ∀ᵐ θ ∂μ, (∃ ρE : d → dIn, IsUnit (θ.E.submatrix ρE id).det) ∧
      ∀ ℓ : Fin L, ∃ ρ : d → A.w ℓ, IsUnit ((θ.write ℓ).submatrix ρ id).det := by
  -- at generic parameters every choice of `d` distinct rows works, and there is such a choice
  filter_upwards [ae_isUnit_det_submatrix μ] with θ hθ
  obtain ⟨-, -, hE, hwrite⟩ := hθ
  refine ⟨?_, fun ℓ => ?_⟩
  · obtain ⟨ρ⟩ := Function.Embedding.nonempty_of_card_le hdIn
    exact ⟨ρ, hE ρ⟩
  · obtain ⟨ρ⟩ := Function.Embedding.nonempty_of_card_le (hw ℓ)
    exact ⟨ρ, hwrite ℓ ρ⟩

end Generic

end Skips
