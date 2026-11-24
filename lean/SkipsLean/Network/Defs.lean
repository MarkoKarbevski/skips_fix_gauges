import SkipsLean.Imports

/-!
# Networks of blocks

Paper: Section 2 (Setup), equations (1) and (2).

Tokens are rows and weights multiply on the right, as in the paper. A block maps a hidden state
`h` to `f (χ h * W_read) * W_write`. The definition carries a matrix `M ℓ` on the stream,

  `h_ℓ = h_{ℓ-1} * M ℓ + f_ℓ (χ h_{ℓ-1} * W_read^ℓ) * W_write^ℓ`,

so that one definition serves the three papers: `M = 0` is the network without skip connections
of the dimension paper, `M = 1` the residual network, and a general `M` a learned linear skip.
-/

namespace Skips

open Matrix

/-- The fixed part of a network of `L` blocks on hidden states of `T` tokens and model dimension
`d`: the widths of the reads (`r ℓ`) and of the writes (`w ℓ`), the fixed map `f ℓ` of each block,
and the fixed map `χ` (the identity or a normalization). Nothing here is trained. -/
structure Arch (T d : Type*) (L : ℕ) where
  /-- index type of the columns of the read of block `ℓ` -/
  r : Fin L → Type
  /-- index type of the rows of the write of block `ℓ` -/
  w : Fin L → Type
  [fr : ∀ ℓ, Fintype (r ℓ)]
  [fw : ∀ ℓ, Fintype (w ℓ)]
  /-- the fixed map of block `ℓ`: an activation on every hidden unit, a gate, or attention -/
  f : ∀ ℓ, Matrix T (r ℓ) ℝ → Matrix T (w ℓ) ℝ
  /-- the fixed map applied before every read and before the readout -/
  χ : Matrix T d ℝ → Matrix T d ℝ

attribute [instance] Arch.fr Arch.fw

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype d] [Fintype dIn]

/-- The parameters `θ = (E, W_read^1, W_write^1, …, W_read^L, W_write^L, D)`. -/
structure Params (A : Arch T d L) (dIn dOut : Type*) where
  /-- the embedding -/
  E : Matrix dIn d ℝ
  /-- the read of block `ℓ` -/
  read : ∀ ℓ, Matrix d (A.r ℓ) ℝ
  /-- the write of block `ℓ` -/
  write : ∀ ℓ, Matrix (A.w ℓ) d ℝ
  /-- the readout -/
  D : Matrix d dOut ℝ

variable (A : Arch T d L)

/-- The hidden states `h_0, …, h_L` at the input `x`, with the stream matrices `M`:
`h_0 = x E` and `h_ℓ = h_{ℓ-1} M_ℓ + f_ℓ (χ h_{ℓ-1} W_read^ℓ) W_write^ℓ`. -/
def hidden (M : Fin L → Matrix d d ℝ) (θ : Params A dIn dOut) (x : Matrix T dIn ℝ) :
    Fin (L + 1) → Matrix T d ℝ :=
  Fin.induction (motive := fun _ => Matrix T d ℝ) (x * θ.E)
    (fun ℓ h => h * M ℓ + A.f ℓ (A.χ h * θ.read ℓ) * θ.write ℓ)

/-- The function of the network: `y = χ (h_L) D`. -/
def eval (M : Fin L → Matrix d d ℝ) (θ : Params A dIn dOut) (x : Matrix T dIn ℝ) :
    Matrix T dOut ℝ :=
  A.χ (hidden A M θ x (Fin.last L)) * θ.D

@[simp] theorem hidden_zero (M : Fin L → Matrix d d ℝ) (θ : Params A dIn dOut)
    (x : Matrix T dIn ℝ) : hidden A M θ x 0 = x * θ.E := by
  simp [hidden]

@[simp] theorem hidden_succ (M : Fin L → Matrix d d ℝ) (θ : Params A dIn dOut)
    (x : Matrix T dIn ℝ) (ℓ : Fin L) :
    hidden A M θ x ℓ.succ =
      hidden A M θ x ℓ.castSucc * M ℓ +
        A.f ℓ (A.χ (hidden A M θ x ℓ.castSucc) * θ.read ℓ) * θ.write ℓ := by
  simp [hidden]

end Skips
