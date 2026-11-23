import SkipsLean.Dimension.UpperBound

/-!
# One block: the directions that keep `C = E W_read` and `A = W_write D`

Paper (dimension paper): Lemma C.2. With one block and without normalization the parameters enter
the function only through `C = E W_read` and `A = W_write D`. A direction `η` keeps `C` and `A`
fixed to first order,

  `η_E W_read + E η_read = 0`  and  `η_write D + W_write η_D = 0`,

if and only if it is the direction of two changes of basis, `X` at `h_0` and `Y` at `h_1`:
`η_E = E X`, `η_read = -X W_read`, `η_write = W_write Y`, `η_D = -Y D`, that is,
`η = cobDir θ (X, Y)`. The direction "only if" uses that `E`, `D`, `W_read` and `W_write` have
rank `d`.
-/

namespace Skips

open Matrix

variable {T d dIn dOut : Type*} [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut]
variable {A : Arch T d 1}

/-- Helper: a matrix whose rank is its number of rows has a right inverse, `M R = 1`. -/
private theorem exists_right_inverse_of_rank {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] (M : Matrix m n ℝ) (hM : M.rank = Fintype.card m) :
    ∃ R : Matrix n m ℝ, M * R = 1 :=
  Matrix.mulVec_surjective_iff_exists_right_inverse.mp
    (Matrix.mulVec_surjective_iff_rank_eq_card.mpr hM)

/-- Helper: a matrix whose rank is its number of columns has a left inverse, `B M = 1`. -/
private theorem exists_left_inverse_of_rank {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq n] (M : Matrix m n ℝ) (hM : M.rank = Fintype.card n) :
    ∃ B : Matrix n m ℝ, B * M = 1 :=
  Matrix.vecMul_surjective_iff_exists_left_inverse.mp
    (Matrix.vecMul_surjective_iff_rank_eq_card.mpr hM)

/-- Helper: a matrix whose rank is its number of columns cancels on the left, via a left inverse. -/
private theorem cancel_left_of_rank {m n k : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (M : Matrix m n ℝ) (hM : M.rank = Fintype.card n) {X Y : Matrix n k ℝ}
    (h : M * X = M * Y) : X = Y := by
  obtain ⟨B, hB⟩ := exists_left_inverse_of_rank M hM
  have := congrArg (B * ·) h
  simpa only [← Matrix.mul_assoc, hB, Matrix.one_mul] using this

/-- **Lemma C.2.** -/
theorem keeps_products_iff_mem_range_cobDir (θ η : Params A dIn dOut)
    (hE : θ.E.rank = Fintype.card d) (hD : θ.D.rank = Fintype.card d)
    (hr : (θ.read 0).rank = Fintype.card d) (hw : (θ.write 0).rank = Fintype.card d) :
    (η.E * θ.read 0 + θ.E * η.read 0 = 0 ∧ η.write 0 * θ.D + θ.write 0 * η.D = 0)
      ↔ ∃ X : Fin 2 → Matrix d d ℝ, η = cobDir θ X := by
  constructor
  · rintro ⟨h1, h2⟩
    -- `W_read` has rank `d`, so it has a right inverse `R`; likewise `D` has `R'`
    obtain ⟨R, hR⟩ := exists_right_inverse_of_rank (θ.read 0) hr
    obtain ⟨R', hR'⟩ := exists_right_inverse_of_rank θ.D hD
    -- multiplying `η_E W_read + E η_read = 0` on the right by `R` gives `η_E = E X₀`
    obtain ⟨X₀, hX₀⟩ : ∃ X₀ : Matrix d d ℝ, η.E = θ.E * X₀ := by
      refine ⟨-(η.read 0 * R), ?_⟩
      have h := congrArg (· * R) h1
      simp only [Matrix.add_mul, Matrix.zero_mul, Matrix.mul_assoc, hR, Matrix.mul_one] at h
      rw [Matrix.mul_neg]
      exact eq_neg_of_add_eq_zero_left h
    -- then `E η_read = -(E X₀ W_read)`, and cancelling `E` on the left gives `η_read = -X₀ W_read`
    have hread : η.read 0 = -(X₀ * θ.read 0) := by
      refine cancel_left_of_rank θ.E hE ?_
      rw [eq_neg_of_add_eq_zero_right h1, hX₀, Matrix.mul_neg, Matrix.mul_assoc]
    -- multiplying `η_write D + W_write η_D = 0` on the right by `R'` gives `η_write = W_write X₁`
    obtain ⟨X₁, hX₁⟩ : ∃ X₁ : Matrix d d ℝ, η.write 0 = θ.write 0 * X₁ := by
      refine ⟨-(η.D * R'), ?_⟩
      have h := congrArg (· * R') h2
      simp only [Matrix.add_mul, Matrix.zero_mul, Matrix.mul_assoc, hR', Matrix.mul_one] at h
      rw [Matrix.mul_neg]
      exact eq_neg_of_add_eq_zero_left h
    -- then `W_write η_D = -(W_write X₁ D)`, and cancelling `W_write` gives `η_D = -X₁ D`
    have hD' : η.D = -(X₁ * θ.D) := by
      refine cancel_left_of_rank (θ.write 0) hw ?_
      rw [eq_neg_of_add_eq_zero_right h2, hX₁, Matrix.mul_neg, Matrix.mul_assoc]
    -- `η` is the direction of the changes of basis `X₀` at `h_0` and `X₁` at `h_1`
    refine ⟨![X₀, X₁], ?_⟩
    apply Params.ext'
    · exact hX₀
    · intro ℓ
      obtain rfl : ℓ = 0 := Subsingleton.elim ℓ 0
      exact hread
    · intro ℓ
      obtain rfl : ℓ = 0 := Subsingleton.elim ℓ 0
      exact hX₁
    · exact hD'
  · rintro ⟨X, rfl⟩
    -- `E X₀ W_read - E X₀ W_read = 0` and `W_write X₁ D - W_write X₁ D = 0`
    constructor
    · show θ.E * X 0 * θ.read 0 + θ.E * -(X 0 * θ.read 0) = 0
      rw [Matrix.mul_neg, Matrix.mul_assoc, add_neg_cancel]
    · show θ.write 0 * X 1 * θ.D + θ.write 0 * -(X 1 * θ.D) = 0
      rw [Matrix.mul_neg, Matrix.mul_assoc, add_neg_cancel]

end Skips
