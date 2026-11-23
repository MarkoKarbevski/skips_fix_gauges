import SkipsLean.Network.Defs
import SkipsLean.Basic.RMSNorm

/-!
# Changes of basis preserve the function

Paper: Definition 3.1 and Proposition 3.2.

`G ℓ` is the change of basis at the hidden state `h_ℓ`: it multiplies the writes into `h_ℓ` on the
right. The reads of `h_ℓ` see `χ (h_ℓ G_ℓ)`, and `K ℓ` is the matrix with `χ (h G_ℓ) = χ (h) K_ℓ`,
which the reads undo on the left. Without normalization and under pre-RMSNorm `K = G`; for
`ε = 0` and `G = cQ`, `K = Q`.
-/

namespace Skips

open Matrix

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype d] [DecidableEq d] [Fintype dIn]
variable {A : Arch T d L}

/-- Definition 3.1 at all hidden states at once. -/
def Params.cob (θ : Params A dIn dOut) (G K : Fin (L + 1) → GL d ℝ) : Params A dIn dOut where
  E := θ.E * (G 0 : Matrix d d ℝ)
  read ℓ := (↑(K ℓ.castSucc)⁻¹ : Matrix d d ℝ) * θ.read ℓ
  write ℓ := θ.write ℓ * (G ℓ.succ : Matrix d d ℝ)
  D := (↑(K (Fin.last L))⁻¹ : Matrix d d ℝ) * θ.D

/-- What the changes of basis do to the stream matrices: `M_ℓ ↦ G_{ℓ-1}⁻¹ M_ℓ G_ℓ`. -/
def cobSkip (M : Fin L → Matrix d d ℝ) (G : Fin (L + 1) → GL d ℝ) : Fin L → Matrix d d ℝ :=
  fun ℓ => (↑(G ℓ.castSucc)⁻¹ : Matrix d d ℝ) * M ℓ * (G ℓ.succ : Matrix d d ℝ)

variable (M : Fin L → Matrix d d ℝ) (θ : Params A dIn dOut) (G K : Fin (L + 1) → GL d ℝ)
  (x : Matrix T dIn ℝ)

/-- Helper: `a (a⁻¹ B) = B` also for a rectangular `B` (`Units.mul_inv_cancel_left` needs a square
`B`). -/
private theorem gl_mul_inv_mul {n : Type*} (a : GL d ℝ) (B : Matrix d n ℝ) :
    (a : Matrix d d ℝ) * ((↑a⁻¹ : Matrix d d ℝ) * B) = B := by
  rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]

/-- The hidden states after the changes of basis are `h_ℓ G_ℓ`. -/
theorem hidden_cob
    (hχ : ∀ ℓ (h : Matrix T d ℝ), A.χ (h * (G ℓ : Matrix d d ℝ)) = A.χ h * (K ℓ : Matrix d d ℝ))
    (ℓ : Fin (L + 1)) :
    hidden A (cobSkip M G) (θ.cob G K) x ℓ = hidden A M θ x ℓ * (G ℓ : Matrix d d ℝ) := by
  induction ℓ using Fin.induction with
  | zero =>
    -- `h_0 = x (E G_0) = (x E) G_0`
    simp only [hidden_zero, Params.cob, Matrix.mul_assoc]
  | succ i ih =>
    -- the new hidden state is `(h G_{i}) (G_{i}⁻¹ M G_{i+1}) + f (χ(h G_{i}) K_{i}⁻¹ W_read) (W_write G_{i+1})`
    rw [hidden_succ, hidden_succ, ih, hχ]
    unfold cobSkip Params.cob
    -- `G_{i} G_{i}⁻¹ = 1` in the stream term, `K_{i} K_{i}⁻¹ = 1` in the read, then distribute
    simp only [Matrix.mul_assoc, Units.mul_inv_cancel_left, gl_mul_inv_mul, Matrix.add_mul]

/-- **Proposition 3.2 in general form.** If `χ (h G_ℓ) = χ (h) K_ℓ` at every hidden state, the
parameters `(E G_0, {K_{ℓ-1}⁻¹ W_read^ℓ, W_write^ℓ G_ℓ}, K_L⁻¹ D)` with the stream matrices
`G_{ℓ-1}⁻¹ M_ℓ G_ℓ` give the same function. -/
theorem eval_cob
    (hχ : ∀ ℓ (h : Matrix T d ℝ), A.χ (h * (G ℓ : Matrix d d ℝ)) = A.χ h * (K ℓ : Matrix d d ℝ)) :
    eval A (cobSkip M G) (θ.cob G K) x = eval A M θ x := by
  -- the last hidden state is `h_L G_L`, so `χ(h_L G_L) K_L⁻¹ D = χ(h_L) K_L K_L⁻¹ D = χ(h_L) D`
  unfold eval
  rw [hidden_cob M θ G K x hχ (Fin.last L), hχ]
  simp only [Params.cob, Matrix.mul_assoc, gl_mul_inv_mul]

/-- **Proposition 3.2, without normalization, no skip connections:** one invertible matrix per
hidden state. -/
theorem eval_cob_skipless (hA : A.χ = id) :
    eval A 0 (θ.cob G G) x = eval A 0 θ x := by
  -- special case of `eval_cob` with `K = G`; the stream matrices `G⁻¹ 0 G` are again `0`
  have hχ : ∀ ℓ (h : Matrix T d ℝ),
      A.χ (h * (G ℓ : Matrix d d ℝ)) = A.χ h * (G ℓ : Matrix d d ℝ) := by
    intro ℓ h
    simp only [hA, id_eq]
  have hskip : cobSkip (0 : Fin L → Matrix d d ℝ) G = 0 := by
    funext ℓ
    simp only [cobSkip, Pi.zero_apply, Matrix.mul_zero, Matrix.zero_mul]
  have := eval_cob 0 θ G G x hχ
  rwa [hskip] at this

/-- With identity skips (`M = 1`) the same change of basis `G` at every hidden state preserves
the function. -/
theorem eval_cob_residual (hA : A.χ = id) (G₀ : GL d ℝ) :
    eval A 1 (θ.cob (fun _ => G₀) (fun _ => G₀)) x = eval A 1 θ x := by
  -- special case of `eval_cob` with `K = G = G₀`; the stream matrices `G₀⁻¹ 1 G₀` are again `1`
  have hχ : ∀ (_ : Fin (L + 1)) (h : Matrix T d ℝ),
      A.χ (h * (G₀ : Matrix d d ℝ)) = A.χ h * (G₀ : Matrix d d ℝ) := by
    intro _ h
    simp only [hA, id_eq]
  have hskip : cobSkip (1 : Fin L → Matrix d d ℝ) (fun _ => G₀) = 1 := by
    funext ℓ
    simp only [cobSkip, Pi.one_apply, Matrix.mul_one, Units.inv_mul]
  have := eval_cob 1 θ (fun _ => G₀) (fun _ => G₀) x hχ
  rwa [hskip] at this

end Skips
