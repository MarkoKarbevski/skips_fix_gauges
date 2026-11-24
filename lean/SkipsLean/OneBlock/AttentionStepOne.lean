import SkipsLean.OneBlock.Attention

/-!
# The one-block theorem for an attention block: Step 1

Paper (dimension paper), proof of Theorem C.1, "Attention blocks", "Step 1: the directions that
keep `B_i` and `C_i`": "For generic parameters `E` and `D` have rank `d_model`; every `W_{Q,i}`,
`W_{K,i}`, `W_{V,i}` and `W_{O,i}^⊤` has rank `d_h`, since `d_h ≤ d_model`; and the queries
`[W_{Q,1}, …, W_{Q,H}] ∈ ℝ^{d_model × H d_h}`, the keys `[W_{K,1}, …, W_{K,H}]` and the output
projection `W_O ∈ ℝ^{H d_h × d_model}` of all heads have rank `d_model`, since
`H d_h ≥ d_model`. Write `η_{Q,i}`, `η_{K,i}`, `η_{V,i}` and `η_{O,i}` for the entries of a
direction `η` at the positions of `W_{Q,i}`, `W_{K,i}`, `W_{V,i}` and `W_{O,i}`, and consider a
direction with `D_θ B_i η = 0` and `D_θ C_i η = 0` for every head. Multiplying `D_θ B_i η = 0`
on the left by the projection `I − E E^+` onto the orthogonal complement of the column space of
`E`, where `E^+` is the pseudo-inverse, leaves `(I − E E^+) η_E W_{Q,i} W_{K,i}^⊤ E^⊤ = 0`. As
`W_{K,i}^⊤ E^⊤` has full row rank, `(I − E E^+) η_E W_{Q,i} = 0` for every head, and as the
queries of all heads have rank `d_model`, `η_E = E X` with `X = E^+ η_E`. In the same way,
multiplying `D_θ C_i η = 0` on the right by the projection `I − D^+ D` gives `η_D = −Y D` with
`Y = −η_D D^+`, because `E W_{V,i}` has full column rank and the output projection has rank
`d_model`. Substituting, and cancelling `E` on the left and `E^⊤` or `D` on the right,
`(η_{Q,i} + X W_{Q,i}) W_{K,i}^⊤ + W_{Q,i} (η_{K,i} + X W_{K,i})^⊤ = 0`,
`(η_{V,i} + X W_{V,i}) W_{O,i} + W_{V,i} (η_{O,i} − W_{O,i} Y) = 0`.
If `P_1` and `P_2` have full column rank and `Z_1 P_2^⊤ + P_1 Z_2^⊤ = 0`, then multiplying on the
right by a right inverse of `P_2^⊤` gives `Z_1 = P_1 Γ` for a square matrix `Γ`, and then
`Z_2 = −P_2 Γ^⊤`. Hence
`η_{Q,i} = −X W_{Q,i} + W_{Q,i} Γ_i`, `η_{K,i} = −X W_{K,i} − W_{K,i} Γ_i^⊤`,
`η_{V,i} = −X W_{V,i} + W_{V,i} Γ'_i`, `η_{O,i} = W_{O,i} Y − Γ'_i W_{O,i}`.
These are the directions of the changes of basis `I + τ X` at `h_0` and `I + τ Y` at `h_1`, and
of `I + τ Γ_i` between the queries and keys and `I + τ Γ'_i` between the values and outputs of
head `i`."

Here: under the conditions `OneBlockGenericAttention θ` (`OneBlock/Attention.lean`; the rank of
the keys of all heads is not among them, the argument does not use it), a direction `η` with
`dAttnScore θ η i = 0` and `dAttnValue θ η i = 0` for every head is
`cobDir θ X + headDirQK θ Γ + headDirVO θ Γ'` (`Dimension/UpperBound.lean`,
`Symmetry/AttentionHeads.lean`). Pure linear algebra; no mask and no input enters.
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {sees : T → T → Prop} [DecidableRel sees]
variable {H dh : Fin 1 → Type} [∀ ℓ, Fintype (H ℓ)] [∀ ℓ, Fintype (dh ℓ)]

/-- Helper: a matrix whose rank is its number of rows has a right inverse, `M R = 1`. -/
private theorem exists_right_inverse_of_rank_ob1 {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] (M : Matrix m n ℝ) (hM : M.rank = Fintype.card m) :
    ∃ R : Matrix n m ℝ, M * R = 1 :=
  Matrix.mulVec_surjective_iff_exists_right_inverse.mp
    (Matrix.mulVec_surjective_iff_rank_eq_card.mpr hM)

/-- Helper: a matrix whose rank is its number of columns has a left inverse, `B M = 1`. -/
private theorem exists_left_inverse_of_rank_ob1 {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq n] (M : Matrix m n ℝ) (hM : M.rank = Fintype.card n) :
    ∃ B : Matrix n m ℝ, B * M = 1 :=
  Matrix.vecMul_surjective_iff_exists_left_inverse.mp
    (Matrix.vecMul_surjective_iff_rank_eq_card.mpr hM)

/-- Helper (Step 1, the part of `η_E` outside the columns of `E`): multiplying
`D_θ B_i η = 0` on the left by `I − E E^+`, which kills `E`, and on the right by the right
inverse `(E^+)^⊤ (W_K^+)^⊤` of `W_K^⊤ E^⊤` leaves `(I − E E^+) η_E W_Q = 0`. -/
private theorem proj_score_ob1 {m n k : Type*} [Fintype m] [Fintype n] [Fintype k]
    [DecidableEq m] [DecidableEq n] [DecidableEq k]
    (E ηE : Matrix m n ℝ) (E' : Matrix n m ℝ) (hE : E' * E = 1)
    (Q K ηQ ηK : Matrix n k ℝ) (K' : Matrix k n ℝ) (hK : K' * K = 1)
    (hB : ηE * Q * Kᵀ * Eᵀ + E * ηQ * Kᵀ * Eᵀ + E * Q * ηKᵀ * Eᵀ + E * Q * Kᵀ * ηEᵀ = 0) :
    (1 - E * E') * ηE * Q = 0 := by
  obtain ⟨P, hP⟩ : ∃ P : Matrix m m ℝ, P = 1 - E * E' := ⟨_, rfl⟩
  rw [← hP]
  -- `P E = E − E E^+ E = 0`
  have hPE : P * E = 0 := by
    rw [hP, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hE, Matrix.mul_one, sub_self]
  -- `P (D_θ B_i η) = P η_E W_Q W_K^⊤ E^⊤`, the other three terms start with `E`
  have h1 : P * ηE * Q * Kᵀ * Eᵀ = 0 := by
    have h := congrArg (P * ·) hB
    simp only [Matrix.mul_add, Matrix.mul_zero, ← Matrix.mul_assoc, hPE, Matrix.zero_mul,
      add_zero] at h
    exact h
  -- `W_K^⊤ E^⊤ (E^+)^⊤ (W_K^+)^⊤ = 1`
  have hEt : Eᵀ * E'ᵀ = 1 := by rw [← Matrix.transpose_mul, hE, Matrix.transpose_one]
  have hKt : Kᵀ * K'ᵀ = 1 := by rw [← Matrix.transpose_mul, hK, Matrix.transpose_one]
  have hKE : Kᵀ * Eᵀ * (E'ᵀ * K'ᵀ) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Eᵀ, hEt, Matrix.one_mul, hKt]
  calc P * ηE * Q = P * ηE * Q * (Kᵀ * Eᵀ * (E'ᵀ * K'ᵀ)) := by rw [hKE, Matrix.mul_one]
    _ = P * ηE * Q * Kᵀ * Eᵀ * (E'ᵀ * K'ᵀ) := by simp only [Matrix.mul_assoc]
    _ = 0 := by rw [h1, Matrix.zero_mul]

/-- Helper (Step 1, `η_E = E X`): if `(I − E E^+) η_E W_{Q,i} = 0` for every head `i` and the
queries `[W_{Q,1}, …]` of all heads have a right inverse, then `η_E = E (E^+ η_E)`. -/
private theorem eq_mul_of_proj_ob1 {m n ι k : Type*} [Fintype m] [Fintype n] [Fintype ι]
    [Fintype k] [DecidableEq m] [DecidableEq n]
    (E ηE : Matrix m n ℝ) (E' : Matrix n m ℝ) (Qall : Matrix n (ι × k) ℝ)
    (R : Matrix (ι × k) n ℝ) (hR : Qall * R = 1) (Q : ι → Matrix n k ℝ)
    (hQ : ∀ i b c, Q i b c = Qall b (i, c)) (h : ∀ i, (1 - E * E') * ηE * Q i = 0) :
    ηE = E * (E' * ηE) := by
  -- column `(i, c)` of `(I − E E^+) η_E [W_{Q,1}, …]` is column `c` of `(I − E E^+) η_E W_{Q,i}`
  have h0 : (1 - E * E') * ηE * Qall = 0 := by
    ext a ⟨i, c⟩
    have := congrFun (congrFun (h i) a) c
    simpa only [Matrix.mul_apply, hQ, Matrix.zero_apply] using this
  -- multiplying on the right by `R`
  have h1 : (1 - E * E') * ηE = 0 := by
    calc (1 - E * E') * ηE = (1 - E * E') * ηE * (Qall * R) := by rw [hR, Matrix.mul_one]
      _ = (1 - E * E') * ηE * Qall * R := (Matrix.mul_assoc _ _ _).symm
      _ = 0 := by rw [h0, Matrix.zero_mul]
  rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero, Matrix.mul_assoc] at h1
  exact h1

/-- Helper (Step 1, the part of `η_D` outside the rows of `D`): multiplying `D_θ C_i η = 0` on
the right by `I − D^+ D`, which kills `D`, and on the left by the left inverse `W_V^+ E^+` of
`E W_V` leaves `W_O η_D (I − D^+ D) = 0`. -/
private theorem proj_value_ob1 {m n k p : Type*} [Fintype m] [Fintype n] [Fintype k]
    [Fintype p] [DecidableEq n] [DecidableEq k] [DecidableEq p]
    (E ηE : Matrix m n ℝ) (E' : Matrix n m ℝ) (hE : E' * E = 1)
    (V ηV : Matrix n k ℝ) (V' : Matrix k n ℝ) (hV : V' * V = 1) (O ηO : Matrix k n ℝ)
    (D ηD : Matrix n p ℝ) (D' : Matrix p n ℝ) (hD : D * D' = 1)
    (hC : ηE * V * O * D + E * ηV * O * D + E * V * ηO * D + E * V * O * ηD = 0) :
    O * ηD * (1 - D' * D) = 0 := by
  obtain ⟨P, hP⟩ : ∃ P : Matrix p p ℝ, P = 1 - D' * D := ⟨_, rfl⟩
  rw [← hP]
  -- `D P = D − D D^+ D = 0`
  have hDP : D * P = 0 := by
    rw [hP, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hD, Matrix.one_mul, sub_self]
  -- `(D_θ C_i η) P = E W_V W_O η_D P`, the other three terms end with `D`
  have h1 : E * (V * (O * (ηD * P))) = 0 := by
    have h := congrArg (· * P) hC
    simp only [Matrix.add_mul, Matrix.zero_mul, Matrix.mul_assoc, hDP, Matrix.mul_zero,
      zero_add] at h
    exact h
  -- `W_V^+ E^+ E W_V = 1`
  have hVE : V' * E' * (E * V) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc E', hE, Matrix.one_mul, hV]
  calc O * ηD * P = V' * E' * (E * V) * (O * ηD * P) := by rw [hVE, Matrix.one_mul]
    _ = V' * (E' * (E * (V * (O * (ηD * P))))) := by simp only [Matrix.mul_assoc]
    _ = 0 := by rw [h1, Matrix.mul_zero, Matrix.mul_zero]

/-- Helper (Step 1, `η_D = −Y D`): if `W_{O,i} η_D (I − D^+ D) = 0` for every head `i` and the
write (which stacks the `W_{O,i}`) has a left inverse, then `η_D = −Y D` with `Y = −η_D D^+`. -/
private theorem eq_neg_mul_of_proj_ob1 {n p ι k : Type*} [Fintype n] [Fintype p] [Fintype ι]
    [Fintype k] [DecidableEq n] [DecidableEq p]
    (D ηD : Matrix n p ℝ) (D' : Matrix p n ℝ) (W : Matrix (ι × k) n ℝ)
    (W' : Matrix n (ι × k) ℝ) (hW : W' * W = 1) (O : ι → Matrix k n ℝ)
    (hO : ∀ i c b, O i c b = W (i, c) b) (h : ∀ i, O i * ηD * (1 - D' * D) = 0) :
    ηD = -(-(ηD * D') * D) := by
  -- row `(i, c)` of `W η_D (I − D^+ D)` is row `c` of `W_{O,i} η_D (I − D^+ D)`
  have h0 : W * ηD * (1 - D' * D) = 0 := by
    ext ⟨i, c⟩ b
    have := congrFun (congrFun (h i) c) b
    simpa only [Matrix.mul_apply, hO, Matrix.zero_apply] using this
  -- multiplying on the left by `W^+`
  have h1 : ηD * (1 - D' * D) = 0 := by
    calc ηD * (1 - D' * D) = W' * W * ηD * (1 - D' * D) := by rw [hW, Matrix.one_mul]
      _ = W' * (W * ηD * (1 - D' * D)) := by simp only [Matrix.mul_assoc]
      _ = 0 := by rw [h0, Matrix.mul_zero]
  rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at h1
  rw [Matrix.neg_mul, neg_neg, Matrix.mul_assoc]
  exact h1

/-- Helper (Step 1, the queries and keys of one head): if `η_E = E X` and `D_θ B_i η = 0`, then
`η_Q = −X W_Q + W_Q Γ` and `η_K = −X W_K − W_K Γ^⊤` for a square matrix `Γ`. -/
private theorem head_QK_ob1 {m n k : Type*} [Fintype m] [Fintype n] [Fintype k]
    [DecidableEq n] [DecidableEq k]
    (E ηE : Matrix m n ℝ) (E' : Matrix n m ℝ) (hE : E' * E = 1) (X : Matrix n n ℝ)
    (hX : ηE = E * X) (Q K ηQ ηK : Matrix n k ℝ) (Q' K' : Matrix k n ℝ) (hQ : Q' * Q = 1)
    (hK : K' * K = 1)
    (hB : ηE * Q * Kᵀ * Eᵀ + E * ηQ * Kᵀ * Eᵀ + E * Q * ηKᵀ * Eᵀ + E * Q * Kᵀ * ηEᵀ = 0) :
    ∃ Γ : Matrix k k ℝ, ηQ = -(X * Q) + Q * Γ ∧ ηK = -(X * K) - K * Γᵀ := by
  subst hX
  obtain ⟨Z₁, hZ₁⟩ : ∃ Z, Z = ηQ + X * Q := ⟨_, rfl⟩
  obtain ⟨Z₂, hZ₂⟩ : ∃ Z, Z = ηK + X * K := ⟨_, rfl⟩
  have hEt : Eᵀ * E'ᵀ = 1 := by rw [← Matrix.transpose_mul, hE, Matrix.transpose_one]
  have hKt : Kᵀ * K'ᵀ = 1 := by rw [← Matrix.transpose_mul, hK, Matrix.transpose_one]
  -- `D_θ B_i η = E (Z₁ W_K^⊤ + W_Q Z₂^⊤) E^⊤`; cancelling `E` and `E^⊤`
  have hM : Z₁ * Kᵀ + Q * Z₂ᵀ = 0 := by
    have h1 : E * (Z₁ * Kᵀ + Q * Z₂ᵀ) * Eᵀ = 0 := by
      rw [← hB, hZ₁, hZ₂]
      simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, Matrix.transpose_add,
        Matrix.transpose_mul]
      abel
    calc Z₁ * Kᵀ + Q * Z₂ᵀ = E' * E * (Z₁ * Kᵀ + Q * Z₂ᵀ) * (Eᵀ * E'ᵀ) := by
          rw [hE, hEt, Matrix.one_mul, Matrix.mul_one]
      _ = E' * (E * (Z₁ * Kᵀ + Q * Z₂ᵀ) * Eᵀ) * E'ᵀ := by simp only [Matrix.mul_assoc]
      _ = 0 := by rw [h1, Matrix.mul_zero, Matrix.zero_mul]
  -- multiplying on the right by `(W_K^+)^⊤`: `Z₁ = W_Q Γ`
  obtain ⟨Γ, hΓ⟩ : ∃ Γ, Γ = -(Z₂ᵀ * K'ᵀ) := ⟨_, rfl⟩
  have hZ1 : Z₁ = Q * Γ := by
    calc Z₁ = Z₁ * (Kᵀ * K'ᵀ) := by rw [hKt, Matrix.mul_one]
      _ = (Z₁ * Kᵀ + Q * Z₂ᵀ) * K'ᵀ - Q * (Z₂ᵀ * K'ᵀ) := by
          simp only [Matrix.add_mul, Matrix.mul_assoc, add_sub_cancel_right]
      _ = Q * Γ := by rw [hM, Matrix.zero_mul, zero_sub, hΓ, Matrix.mul_neg]
  -- then `W_Q (Γ W_K^⊤ + Z₂^⊤) = 0`, and cancelling `W_Q`: `Z₂ = −W_K Γ^⊤`
  have h3 : Γ * Kᵀ + Z₂ᵀ = 0 := by
    calc Γ * Kᵀ + Z₂ᵀ = Q' * Q * (Γ * Kᵀ + Z₂ᵀ) := by rw [hQ, Matrix.one_mul]
      _ = Q' * (Q * Γ * Kᵀ + Q * Z₂ᵀ) := by simp only [Matrix.mul_add, Matrix.mul_assoc]
      _ = 0 := by rw [← hZ1, hM, Matrix.mul_zero]
  have hZ2 : Z₂ = -(K * Γᵀ) := by
    rw [← Matrix.transpose_transpose Z₂, eq_neg_of_add_eq_zero_right h3, Matrix.transpose_neg,
      Matrix.transpose_mul, Matrix.transpose_transpose]
  refine ⟨Γ, ?_, ?_⟩
  · rw [← hZ1, hZ₁]
    abel
  · rw [sub_eq_add_neg, ← hZ2, hZ₂]
    abel

/-- Helper (Step 1, the values and outputs of one head): if `η_E = E X`, `η_D = −Y D` and
`D_θ C_i η = 0`, then `η_V = −X W_V + W_V Γ'` and `η_O = W_O Y − Γ' W_O` for a square matrix
`Γ'`. -/
private theorem head_VO_ob1 {m n k p : Type*} [Fintype m] [Fintype n] [Fintype k] [Fintype p]
    [DecidableEq n] [DecidableEq k] [DecidableEq p]
    (E ηE : Matrix m n ℝ) (E' : Matrix n m ℝ) (hE : E' * E = 1) (X : Matrix n n ℝ)
    (hX : ηE = E * X) (Y : Matrix n n ℝ) (D ηD : Matrix n p ℝ) (D' : Matrix p n ℝ)
    (hD : D * D' = 1) (hY : ηD = -(Y * D)) (V ηV : Matrix n k ℝ) (O ηO : Matrix k n ℝ)
    (V' : Matrix k n ℝ) (O' : Matrix n k ℝ) (hV : V' * V = 1) (hO : O * O' = 1)
    (hC : ηE * V * O * D + E * ηV * O * D + E * V * ηO * D + E * V * O * ηD = 0) :
    ∃ Γ : Matrix k k ℝ, ηV = -(X * V) + V * Γ ∧ ηO = O * Y - Γ * O := by
  subst hX hY
  obtain ⟨Z₁, hZ₁⟩ : ∃ Z, Z = ηV + X * V := ⟨_, rfl⟩
  obtain ⟨Z₂, hZ₂⟩ : ∃ Z, Z = ηO - O * Y := ⟨_, rfl⟩
  -- `D_θ C_i η = E (Z₁ W_O + W_V Z₂) D`; cancelling `E` and `D`
  have hM : Z₁ * O + V * Z₂ = 0 := by
    have h1 : E * (Z₁ * O + V * Z₂) * D = 0 := by
      rw [← hC, hZ₁, hZ₂]
      simp only [Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub,
        Matrix.mul_assoc, Matrix.mul_neg]
      abel
    calc Z₁ * O + V * Z₂ = E' * E * (Z₁ * O + V * Z₂) * (D * D') := by
          rw [hE, hD, Matrix.one_mul, Matrix.mul_one]
      _ = E' * (E * (Z₁ * O + V * Z₂) * D) * D' := by simp only [Matrix.mul_assoc]
      _ = 0 := by rw [h1, Matrix.mul_zero, Matrix.zero_mul]
  -- multiplying on the right by `W_O^+`: `Z₁ = W_V Γ'`
  obtain ⟨Γ, hΓ⟩ : ∃ Γ, Γ = -(Z₂ * O') := ⟨_, rfl⟩
  have hZ1 : Z₁ = V * Γ := by
    calc Z₁ = Z₁ * (O * O') := by rw [hO, Matrix.mul_one]
      _ = (Z₁ * O + V * Z₂) * O' - V * (Z₂ * O') := by
          simp only [Matrix.add_mul, Matrix.mul_assoc, add_sub_cancel_right]
      _ = V * Γ := by rw [hM, Matrix.zero_mul, zero_sub, hΓ, Matrix.mul_neg]
  -- then `W_V (Γ' W_O + Z₂) = 0`, and cancelling `W_V`: `Z₂ = −Γ' W_O`
  have h3 : Γ * O + Z₂ = 0 := by
    calc Γ * O + Z₂ = V' * V * (Γ * O + Z₂) := by rw [hV, Matrix.one_mul]
      _ = V' * (V * Γ * O + V * Z₂) := by simp only [Matrix.mul_add, Matrix.mul_assoc]
      _ = 0 := by rw [← hZ1, hM, Matrix.mul_zero]
  refine ⟨Γ, ?_, ?_⟩
  · rw [← hZ1, hZ₁]
    abel
  · rw [sub_eq_add_neg, ← eq_neg_of_add_eq_zero_right h3, hZ₂]
    abel

/-- **Proof of Theorem C.1 for attention blocks, Step 1:** under the conditions of the proof, a
direction `η` that keeps every `B_i` and every `C_i` to first order is the sum of the direction
of two changes of basis of the hidden states and of the directions of the changes of basis
inside the heads. -/
theorem exists_cobDir_add_headDir_of_keeps
    (θ : Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut)
    (hθ : OneBlockGenericAttention θ)
    (η : Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut)
    (hB : ∀ i, dAttnScore θ η i = 0) (hC : ∀ i, dAttnValue θ η i = 0) :
    ∃ (X : Fin 2 → Matrix d d ℝ) (Γ Γ' : ∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ),
      η = cobDir θ X + headDirQK θ Γ + headDirVO θ Γ' := by
  classical
  -- the degenerate case `d_h = 0`: the queries have no columns, so `d` is empty
  by_cases h0 : Fintype.card (dh 0) = 0
  · have hd : Fintype.card d = 0 := by
      rw [← hθ.rank_queries]
      refine Nat.le_zero.mp ((Matrix.rank_le_card_width _).trans ?_)
      rw [Fintype.card_prod, h0, Nat.mul_zero]
    have : IsEmpty d := Fintype.card_eq_zero_iff.mp hd
    refine ⟨0, fun _ _ => 0, fun _ _ => 0, ?_⟩
    apply Params.ext'
    · ext a b
      exact isEmptyElim b
    · intro ℓ
      ext a b
      exact isEmptyElim a
    · intro ℓ
      ext a b
      exact isEmptyElim b
    · ext a b
      exact isEmptyElim a
  -- otherwise `1 / √d_h ≠ 0`, and `D_θ B_i η = 0` without the factor
  have hc : (Real.sqrt (Fintype.card (dh 0)))⁻¹ ≠ 0 :=
    inv_ne_zero (Real.sqrt_ne_zero'.mpr (Nat.cast_pos.mpr (Nat.pos_of_ne_zero h0)))
  have hB' := fun i => (smul_eq_zero.mp (hB i)).resolve_left hc
  -- one-sided inverses from the ranks
  obtain ⟨E', hE'⟩ := exists_left_inverse_of_rank_ob1 θ.E hθ.rank_E
  obtain ⟨D', hD'⟩ := exists_right_inverse_of_rank_ob1 θ.D hθ.rank_D
  obtain ⟨W', hW'⟩ := exists_left_inverse_of_rank_ob1 (θ.write 0) hθ.rank_write
  obtain ⟨R, hR⟩ := exists_right_inverse_of_rank_ob1 _ hθ.rank_queries
  choose Q' hQ' using fun i => exists_left_inverse_of_rank_ob1 (attnQ θ i) (hθ.rank_Q i)
  choose K' hK' using fun i => exists_left_inverse_of_rank_ob1 (attnK θ i) (hθ.rank_K i)
  choose V' hV' using fun i => exists_left_inverse_of_rank_ob1 (attnV θ i) (hθ.rank_V i)
  choose O' hO' using fun i => exists_right_inverse_of_rank_ob1 (attnO θ i) (hθ.rank_O i)
  -- `η_E = E X` with `X = E^+ η_E`
  obtain ⟨X, hX⟩ : ∃ X, η.E = θ.E * X :=
    ⟨_, eq_mul_of_proj_ob1 θ.E η.E E' _ R hR (fun i => attnQ θ i) (fun _ _ _ => by rfl)
      fun i => proj_score_ob1 θ.E η.E E' hE' (attnQ θ i) (attnK θ i) (attnQ η i) (attnK η i)
        (K' i) (hK' i) (hB' i)⟩
  -- `η_D = −Y D` with `Y = −η_D D^+`
  obtain ⟨Y, hY⟩ : ∃ Y, η.D = -(Y * θ.D) :=
    ⟨_, eq_neg_mul_of_proj_ob1 θ.D η.D D' (θ.write 0) W' hW' (fun i => attnO θ i)
      (fun _ _ _ => by rfl) fun i => proj_value_ob1 θ.E η.E E' hE' (attnV θ i) (attnV η i) (V' i)
        (hV' i) (attnO θ i) (attnO η i) θ.D η.D D' hD' (hC i)⟩
  -- the heads
  choose Γ hΓQ hΓK using fun i => head_QK_ob1 θ.E η.E E' hE' X hX (attnQ θ i) (attnK θ i)
    (attnQ η i) (attnK η i) (Q' i) (K' i) (hQ' i) (hK' i) (hB' i)
  choose Γ' hΓV hΓO using fun i => head_VO_ob1 θ.E η.E E' hE' X hX Y θ.D η.D D' hD' hY
    (attnV θ i) (attnV η i) (attnO θ i) (attnO η i) (V' i) (O' i) (hV' i) (hO' i) (hC i)
  -- assemble
  refine ⟨![X, Y],
    fun ℓ => Fin.cases (motive := fun ℓ => H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) Γ (fun j => j.elim0) ℓ,
    fun ℓ => Fin.cases (motive := fun ℓ => H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) Γ' (fun j => j.elim0) ℓ,
    ?_⟩
  apply Params.ext'
  · show η.E = θ.E * X + 0 + 0
    rw [add_zero, add_zero, hX]
  · intro ℓ
    obtain rfl : ℓ = 0 := Subsingleton.elim ℓ 0
    ext a ⟨i, c⟩
    rcases c with k | k | k
    · have h := congrFun (congrFun (hΓQ i) a) k
      change attnQ η i a k = (-(X * attnQ θ i)) a k + (attnQ θ i * Γ i) a k + 0
      rw [add_zero]
      exact h
    · have h := congrFun (congrFun (hΓK i) a) k
      change attnK η i a k = (-(X * attnK θ i)) a k + -((attnK θ i * (Γ i)ᵀ) a k) + 0
      rw [add_zero, h, Matrix.sub_apply, sub_eq_add_neg]
    · have h := congrFun (congrFun (hΓV i) a) k
      change attnV η i a k = (-(X * attnV θ i)) a k + 0 + (attnV θ i * Γ' i) a k
      rw [add_zero]
      exact h
  · intro ℓ
    obtain rfl : ℓ = 0 := Subsingleton.elim ℓ 0
    ext ⟨i, k⟩ b
    have h := congrFun (congrFun (hΓO i) k) b
    change attnO η i k b = (attnO θ i * Y) k b + 0 + -((Γ' i * attnO θ i) k b)
    rw [add_zero, h, Matrix.sub_apply, sub_eq_add_neg]
  · show η.D = -(Y * θ.D) + 0 + 0
    rw [add_zero, add_zero, hY]

end Skips
