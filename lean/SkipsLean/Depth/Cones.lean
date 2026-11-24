import SkipsLean.Depth.SuffixGated

/-!
# Cones and good parameters

Paper (dimension): Appendix D.5, "Cones and good parameters". "A cone is a set of rows that
contains `λ h` for each of its rows `h` and every number `λ > 0`. Let `C_0, …, C_L` be open convex
cones in `ℝ^{1×d}` that do not contain `0`, one for each hidden state. We call `θ` good for these
cones if (R1) holds and every block `ℓ`, with its gate columns `c_j`, its write rows `a_j` and the
entries `ι_j(n)` of `ι^ℓ(n)`, satisfies:
(K1) `n c_j ≠ 0` for every `n ∈ C_{ℓ-1}` and every `j`. So every gate has one sign on `C_{ℓ-1}`.
Let `A_ℓ` be the set of the hidden units `j` with `n c_j > 0` on `C_{ℓ-1}`, the active ones, and
let `g°_ℓ(n) = ∑_{j ∈ A_ℓ} (n c_j) ι_j(n) a_j` be the block with its gates frozen. …
(K2) `g°_ℓ(n) ∈ C_ℓ` for every `n ∈ C_{ℓ-1}`, and `D g°_ℓ(n)` is invertible at some row `n`.
(K3) No `a_j` vanishes, and in a gated block no value column `e_j` vanishes. For GELU and GeGLU
blocks the matrices `c_1 c_1^⊤, …, c_q c_q^⊤` are linearly independent over `ℚ`, and for SwiGLU
blocks the columns `c_1, …, c_q` are."
Here `ι_j(n) = n e_j` in a gated block and `ι_j(n) = 1` in a GELU block.

In Lean:
* the cones are sets of rows `d → ℝ`; a cone is also required to be nonempty, which the paper uses
  without saying (its proofs take rows of the cones);
* the active sets `A_ℓ` are given as data, with (K1) in the form "`n c_j > 0` on `C_{ℓ-1}` for
  `j ∈ A_ℓ` and `n c_j < 0` for `j ∉ A_ℓ`", which is (K1) because a convex cone is connected;
* the conditions do not involve the activation, so "good" is defined once for gated networks and
  once for MLP networks (the GELU blocks); the independence over `ℚ` of (K3), which depends on the
  kind of block, is a separate hypothesis of the statements that use it.

Stated here: the sentence "A good `θ` is regular", and Lemma D.13 in the form: there are cones and
a parameter that is good for them and has the independence of (K3) (the paper's `θ†`, with the
positive orthant as every cone). Lemma D.12, the step from `(D_{k+1})` to `(D_k)` at good
parameters, is in `Depth/StepGated.lean`.
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise Topology

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {σ : ℝ → ℝ} {χ : Matrix T d ℝ → Matrix T d ℝ} {hid : Fin L → Type}
  [∀ ℓ, Fintype (hid ℓ)]

/-- An open convex cone of rows that does not contain `0` (and is not empty). -/
structure IsOpenConvexCone (C : Set (d → ℝ)) : Prop where
  isOpen : IsOpen C
  convex : Convex ℝ C
  nonempty : C.Nonempty
  zero_notMem : (0 : d → ℝ) ∉ C
  smul_mem : ∀ n ∈ C, ∀ lam : ℝ, 0 < lam → lam • n ∈ C

/-- The gated block `ℓ` with its gates frozen on the active set `A`:
`g°(n) = ∑_{j ∈ A} (n c_j) (n e_j) a_j`. -/
def frozenGated (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut) (ℓ : Fin L)
    (A : Finset (hid ℓ)) (n : d → ℝ) : d → ℝ :=
  ∑ j ∈ A, ((n ⬝ᵥ (θ.read ℓ)ᵀ (Sum.inl j)) * (n ⬝ᵥ (θ.read ℓ)ᵀ (Sum.inr j))) • θ.write ℓ j

/-- The MLP block `ℓ` with its hidden units frozen on the active set `A` (a GELU block with its
gates frozen): `g°(n) = ∑_{j ∈ A} (n c_j) a_j`. -/
def frozenMlp (θ : Params (Arch.mlp (T := T) (d := d) σ χ hid) dIn dOut) (ℓ : Fin L)
    (A : Finset (hid ℓ)) (n : d → ℝ) : d → ℝ :=
  ∑ j ∈ A, (n ⬝ᵥ (θ.read ℓ)ᵀ j) • θ.write ℓ j

/-- **`θ` is good for the cones `C_0, …, C_L`,** for a network of gated blocks, with the active
sets `A_ℓ`: (R1), (K1), (K2) and the part of (K3) that does not depend on the kind of gate. -/
structure GoodForConesGated (C : Fin (L + 1) → Set (d → ℝ)) (A : ∀ ℓ, Finset (hid ℓ))
    (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut) : Prop where
  cone : ∀ k, IsOpenConvexCone (C k)
  /-- (R1) -/
  rank_E : θ.E.rank = Fintype.card d
  /-- (R1) -/
  rank_D : θ.D.rank = Fintype.card d
  /-- (R1) -/
  rank_write : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d
  /-- (K1): the gates of the active units are positive on the cone that the block reads -/
  gate_pos : ∀ ℓ, ∀ n ∈ C ℓ.castSucc, ∀ j ∈ A ℓ, 0 < n ⬝ᵥ (θ.read ℓ)ᵀ (Sum.inl j)
  /-- (K1): the gates of the other units are negative there -/
  gate_neg : ∀ ℓ, ∀ n ∈ C ℓ.castSucc, ∀ j ∉ A ℓ, n ⬝ᵥ (θ.read ℓ)ᵀ (Sum.inl j) < 0
  /-- (K2): the frozen block maps the cone that it reads into the next cone -/
  frozen_mem : ∀ ℓ, ∀ n ∈ C ℓ.castSucc, frozenGated θ ℓ (A ℓ) n ∈ C ℓ.succ
  /-- (K2): the derivative of the frozen block is invertible at some row -/
  frozen_deriv : ∀ ℓ, ∃ n : d → ℝ, Function.Injective (fderiv ℝ (frozenGated θ ℓ (A ℓ)) n)
  /-- (K3): no write row vanishes -/
  write_ne_zero : ∀ ℓ (j : hid ℓ), θ.write ℓ j ≠ 0
  /-- (K3): no value column vanishes -/
  value_ne_zero : ∀ ℓ (j : hid ℓ), (θ.read ℓ)ᵀ (Sum.inr j) ≠ 0

/-- **`θ` is good for the cones `C_0, …, C_L`,** for a network of MLP blocks (the GELU blocks of
the paper), with the active sets `A_ℓ`: (R1), (K1), (K2) and "no `a_j` vanishes" of (K3). -/
structure GoodForConesMlp (C : Fin (L + 1) → Set (d → ℝ)) (A : ∀ ℓ, Finset (hid ℓ))
    (θ : Params (Arch.mlp (T := T) (d := d) σ χ hid) dIn dOut) : Prop where
  cone : ∀ k, IsOpenConvexCone (C k)
  /-- (R1) -/
  rank_E : θ.E.rank = Fintype.card d
  /-- (R1) -/
  rank_D : θ.D.rank = Fintype.card d
  /-- (R1) -/
  rank_write : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d
  /-- (K1) -/
  gate_pos : ∀ ℓ, ∀ n ∈ C ℓ.castSucc, ∀ j ∈ A ℓ, 0 < n ⬝ᵥ (θ.read ℓ)ᵀ j
  /-- (K1) -/
  gate_neg : ∀ ℓ, ∀ n ∈ C ℓ.castSucc, ∀ j ∉ A ℓ, n ⬝ᵥ (θ.read ℓ)ᵀ j < 0
  /-- (K2) -/
  frozen_mem : ∀ ℓ, ∀ n ∈ C ℓ.castSucc, frozenMlp θ ℓ (A ℓ) n ∈ C ℓ.succ
  /-- (K2) -/
  frozen_deriv : ∀ ℓ, ∃ n : d → ℝ, Function.Injective (fderiv ℝ (frozenMlp θ ℓ (A ℓ)) n)
  /-- (K3): no write row vanishes -/
  write_ne_zero : ∀ ℓ (j : hid ℓ), θ.write ℓ j ≠ 0

/-! ### A good `θ` is regular -/

/-- "A good `θ` is regular", SwiGLU blocks. -/
theorem regular_of_goodForConesGated_swiglu [Nonempty T] {C : Fin (L + 1) → Set (d → ℝ)}
    {A : ∀ ℓ, Finset (hid ℓ)} {θ : Params (Arch.gated (T := T) (d := d) silu χ hid) dIn dOut}
    (hθ : GoodForConesGated C A θ) : Regular (Arch.gated silu χ hid) θ := by
  sorry

/-- "A good `θ` is regular", GeGLU blocks. -/
theorem regular_of_goodForConesGated_geglu [Nonempty T] {C : Fin (L + 1) → Set (d → ℝ)}
    {A : ∀ ℓ, Finset (hid ℓ)} {θ : Params (Arch.gated (T := T) (d := d) gelu χ hid) dIn dOut}
    (hθ : GoodForConesGated C A θ) : Regular (Arch.gated gelu χ hid) θ := by
  sorry

/-- "A good `θ` is regular", GELU blocks. -/
theorem regular_of_goodForConesMlp_gelu [Nonempty T] {C : Fin (L + 1) → Set (d → ℝ)}
    {A : ∀ ℓ, Finset (hid ℓ)} {θ : Params (Arch.mlp (T := T) (d := d) gelu χ hid) dIn dOut}
    (hθ : GoodForConesMlp C A θ) : Regular (Arch.mlp gelu χ hid) θ := by
  sorry

/-! ### Lemma D.13: good parameters exist -/

/-- **Lemma D.13, for SwiGLU blocks:** for `d_in, d_out ≥ d ≥ 1` and at least `d` hidden units in
every block there are cones, active sets and a parameter that is good for them and whose gate
columns are linearly independent over `ℚ` in every block. (The conditions do not involve the gate
or the normalization.) -/
theorem exists_goodForConesGated_cols [Nonempty d]
    (hdIn : Fintype.card d ≤ Fintype.card dIn) (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∃ (C : Fin (L + 1) → Set (d → ℝ)) (A : ∀ ℓ, Finset (hid ℓ))
      (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut),
      GoodForConesGated C A θ ∧
        ∀ ℓ, LinearIndependent ℚ (fun j : hid ℓ => (θ.read ℓ)ᵀ (Sum.inl j)) := by
  sorry

/-- **Lemma D.13, for GeGLU blocks:** for `d_in, d_out ≥ d ≥ 2` and at least `d` hidden units in
every block there are cones, active sets and a parameter that is good for them and for which the
matrices `c_j c_j^⊤` of the gate columns are linearly independent over `ℚ` in every block. -/
theorem exists_goodForConesGated_outer (hd : 2 ≤ Fintype.card d)
    (hdIn : Fintype.card d ≤ Fintype.card dIn) (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∃ (C : Fin (L + 1) → Set (d → ℝ)) (A : ∀ ℓ, Finset (hid ℓ))
      (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut),
      GoodForConesGated C A θ ∧
        ∀ ℓ, LinearIndependent ℚ (fun j : hid ℓ =>
          Matrix.vecMulVec ((θ.read ℓ)ᵀ (Sum.inl j)) ((θ.read ℓ)ᵀ (Sum.inl j))) := by
  sorry

/-- **Lemma D.13, for GELU blocks:** for `d_in, d_out ≥ d ≥ 2` and at least `d` hidden units in
every block there are cones, active sets and a parameter that is good for them and for which the
matrices `c_j c_j^⊤` of the read columns are linearly independent over `ℚ` in every block. -/
theorem exists_goodForConesMlp_outer (hd : 2 ≤ Fintype.card d)
    (hdIn : Fintype.card d ≤ Fintype.card dIn) (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∃ (C : Fin (L + 1) → Set (d → ℝ)) (A : ∀ ℓ, Finset (hid ℓ))
      (θ : Params (Arch.mlp (T := T) (d := d) σ χ hid) dIn dOut),
      GoodForConesMlp C A θ ∧
        ∀ ℓ, LinearIndependent ℚ (fun j : hid ℓ =>
          Matrix.vecMulVec ((θ.read ℓ)ᵀ j) ((θ.read ℓ)ᵀ j)) := by
  sorry

end Skips
