import SkipsLean.Dimension.Space
import SkipsLean.Network.Blocks

/-!
# The number of parameters

Papers: the number `P` of parameters of a network (Setup of the dimension paper and of the skips
paper; for instance the proof of Theorem A.28 (iii) of the skips paper: "The skipless network then
has `P' = P + 2 d_model ∑_ℓ (d'_hidden,ℓ - d_hidden,ℓ)` parameters"). In this library `P` is
`Module.finrank ℝ (Params A dIn dOut)`; here it is written out: the embedding `d_in × d`, a read
`d × r_ℓ` and a write `w_ℓ × d` for each block, the readout `d × d_out`.
-/

namespace Skips

open Matrix

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype d] [Fintype dIn] [Fintype dOut]

/-- **The number of parameters of a network:** `P = d_in d + ∑_ℓ d r_ℓ + ∑_ℓ w_ℓ d + d d_out`,
with `r_ℓ` the number of columns of the read of block `ℓ` and `w_ℓ` the number of rows of its
write. -/
theorem finrank_params (A : Arch T d L) :
    Module.finrank ℝ (Params A dIn dOut) =
      Fintype.card dIn * Fintype.card d + ∑ ℓ, Fintype.card d * Fintype.card (A.r ℓ)
        + ∑ ℓ, Fintype.card (A.w ℓ) * Fintype.card d + Fintype.card d * Fintype.card dOut := by
  -- the parameters are the product of their four components
  rw [(Params.linearEquivProd (A := A) (dIn := dIn) (dOut := dOut)).finrank_eq]
  simp only [Params.Prod, Module.finrank_prod, Module.finrank_pi_fintype, Module.finrank_matrix,
    Module.finrank_self, mul_one]
  ring

/-- **The number of parameters of a network of MLP blocks:**
`P = d_in d + 2 d ∑_ℓ d_hidden,ℓ + d d_out`. -/
theorem finrank_params_mlp (σ : ℝ → ℝ) (χ : Matrix T d ℝ → Matrix T d ℝ) (hid : Fin L → Type)
    [∀ ℓ, Fintype (hid ℓ)] :
    Module.finrank ℝ (Params (Arch.mlp σ χ hid) dIn dOut) =
      Fintype.card dIn * Fintype.card d + 2 * Fintype.card d * ∑ ℓ, Fintype.card (hid ℓ)
        + Fintype.card d * Fintype.card dOut := by
  -- the reads and the writes both have `d_hidden,ℓ` columns, resp. rows
  rw [finrank_params]
  simp only [Arch.mlp]
  have h : ∑ ℓ, (Fintype.card d * Fintype.card (hid ℓ) + Fintype.card (hid ℓ) * Fintype.card d)
      = 2 * Fintype.card d * ∑ ℓ, Fintype.card (hid ℓ) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun ℓ _ => by ring
  rw [Finset.sum_add_distrib] at h
  omega

/-- **The number of parameters of a network of gated blocks** (a gate column and a value column
of the read for each hidden unit): `P = d_in d + 3 d ∑_ℓ d_hidden,ℓ + d d_out`. -/
theorem finrank_params_gated (σ : ℝ → ℝ) (χ : Matrix T d ℝ → Matrix T d ℝ) (hid : Fin L → Type)
    [∀ ℓ, Fintype (hid ℓ)] :
    Module.finrank ℝ (Params (Arch.gated σ χ hid) dIn dOut) =
      Fintype.card dIn * Fintype.card d + 3 * Fintype.card d * ∑ ℓ, Fintype.card (hid ℓ)
        + Fintype.card d * Fintype.card dOut := by
  -- the read has a gate column and a value column for each hidden unit
  rw [finrank_params]
  simp only [Arch.gated, Fintype.card_sum]
  have h : ∀ ℓ, Fintype.card d * (Fintype.card (hid ℓ) + Fintype.card (hid ℓ))
      + Fintype.card (hid ℓ) * Fintype.card d = 3 * Fintype.card d * Fintype.card (hid ℓ) :=
    fun ℓ => by ring
  have h2 : ∑ ℓ, (Fintype.card d * (Fintype.card (hid ℓ) + Fintype.card (hid ℓ))
      + Fintype.card (hid ℓ) * Fintype.card d) = 3 * Fintype.card d * ∑ ℓ, Fintype.card (hid ℓ) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun ℓ _ => h ℓ
  rw [Finset.sum_add_distrib] at h2
  omega

end Skips
