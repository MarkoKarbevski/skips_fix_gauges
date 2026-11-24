import SkipsLean.Dimension.Functional
import SkipsLean.Dimension.ParameterCount
import SkipsLean.Generic.Params

/-!
# Networks without an embedding and a readout: the blocks alone

Paper (skips paper): Corollary 4.10 (ii): "Without an embedding and a readout, so that
`h_0 = x ∈ ℝ^{T × d_model}` and `y = h_L`, its functional dimension is `P − s`". Lemma A.27, its
fourth value: "`fd(θ_τ) = P − s` (no embedding, readout, biases or normalization)". Theorem A.28
(i): "a composition of `L ≥ 2` residual blocks equals no composition of `L` blocks without skips
of the same widths". In these statements the parameters are the reads and the writes of the
blocks, `P` is their number, and the functional dimension is that of Definition 4.1 for the family
of functions `x ↦ y` that they parametrize.

Here:

* `BlockParams A`: the reads and the writes of the blocks, written as the parameters with an
  empty embedding and an empty readout (so that they carry the vector space, the norm and the
  measures of `Params`). `finrank_blockParams`: their number is `∑_ℓ d r_ℓ + ∑_ℓ w_ℓ d`.
* `BlockParams.toParams β`: the parameters `(I, W_read^1, W_write^1, …, I)` of a network with
  `d_in = d_out = d`.
* `evalBlocks A S β`: the function of the network without an embedding and a readout,
  `h_0 = x`, `y = χ(h_L)` (`hidden_toParams_zero`, `evalBlocks_eq`); without normalization,
  `y = h_L`.
* `jacobianRankBlocks`, `funDimBlocks`: the rank of the Jacobian of
  `β ↦ (F_β(x_1), …, F_β(x_n))` and Definition 4.1 for this family: the largest such rank over
  all finite batches of inputs.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d]

/-- **The parameters of the blocks alone,** `(W_read^1, W_write^1, …, W_read^L, W_write^L)`: the
parameters with an empty embedding and an empty readout. -/
abbrev BlockParams (A : Arch T d L) : Type _ := Params A PEmpty.{1} PEmpty.{1}

/-- **The network without an embedding and a readout, as a network with `E = I` and `D = I`:**
the reads and the writes of `β`, with `d_in = d_out = d`. -/
def BlockParams.toParams {A : Arch T d L} (β : BlockParams A) : Params A d d where
  E := 1
  read := β.read
  write := β.write
  D := 1

/-- **The function of the network without an embedding and a readout:** `h_0 = x`, the blocks of
`β` with the stream matrices `S`, and `y = χ(h_L)`. -/
def evalBlocks (A : Arch T d L) (S : Fin L → Matrix d d ℝ) (β : BlockParams A)
    (x : Matrix T d ℝ) : Matrix T d ℝ :=
  eval A S β.toParams x

variable (A : Arch T d L) (S : Fin L → Matrix d d ℝ)

/-- The rank of the Jacobian of `β ↦ (F_β(x_1), …, F_β(x_n))` at `β`, for the network without an
embedding and a readout. -/
noncomputable def jacobianRankBlocks {n : ℕ} (X : Fin n → Matrix T d ℝ) (β : BlockParams A) : ℕ :=
  Module.finrank ℝ (LinearMap.range
    (fderiv ℝ (fun β' : BlockParams A => fun i : Fin n => evalBlocks A S β' (X i)) β).toLinearMap)

/-- **Definition 4.1 for the network without an embedding and a readout:** the functional
dimension at `β` is the largest rank of the Jacobian of the outputs on a finite batch of
inputs. -/
noncomputable def funDimBlocks (β : BlockParams A) : ℕ :=
  sSup {r : ℕ | ∃ (n : ℕ) (X : Fin n → Matrix T d ℝ), r = jacobianRankBlocks A S X β}

variable {A S}

omit [Fintype T] in
/-- Without an embedding, `h_0 = x`. -/
theorem hidden_toParams_zero (β : BlockParams A) (x : Matrix T d ℝ) :
    hidden A S β.toParams x 0 = x := by
  -- `h_0 = x E` with `E = I`
  rw [hidden_zero]
  exact Matrix.mul_one x

omit [Fintype T] in
/-- Without a readout, `y = χ(h_L)`. -/
theorem evalBlocks_eq (β : BlockParams A) (x : Matrix T d ℝ) :
    evalBlocks A S β x = A.χ (hidden A S β.toParams x (Fin.last L)) := by
  -- `y = χ(h_L) D` with `D = I`
  exact Matrix.mul_one _

omit [Fintype T] [DecidableEq d] in
/-- **The number of parameters of the blocks alone:** `P = ∑_ℓ d r_ℓ + ∑_ℓ w_ℓ d`. -/
theorem finrank_blockParams (A : Arch T d L) :
    Module.finrank ℝ (BlockParams A)
      = ∑ ℓ, Fintype.card d * Fintype.card (A.r ℓ)
        + ∑ ℓ, Fintype.card (A.w ℓ) * Fintype.card d := by
  -- the embedding and the readout are empty: `d_in = d_out = 0`
  rw [finrank_params]
  simp only [Fintype.card_eq_zero, zero_mul, mul_zero, zero_add, add_zero]

/-- The rank of the Jacobian on any batch is at most the number of parameters of the blocks. -/
theorem jacobianRankBlocks_le_finrank {n : ℕ} (X : Fin n → Matrix T d ℝ) (β : BlockParams A) :
    jacobianRankBlocks A S X β ≤ Module.finrank ℝ (BlockParams A) := by
  -- the range of a linear map has at most the dimension of its domain
  exact LinearMap.finrank_range_le _

/-- The ranks in the definition of `funDimBlocks` are at most the number of parameters. -/
private theorem funDimBlocks_set_bddAbove_bla (β : BlockParams A) :
    BddAbove {r : ℕ | ∃ (n : ℕ) (X : Fin n → Matrix T d ℝ), r = jacobianRankBlocks A S X β} := by
  refine ⟨Module.finrank ℝ (BlockParams A), ?_⟩
  rintro _ ⟨n, X, rfl⟩
  exact jacobianRankBlocks_le_finrank X β

/-- The rank of the Jacobian on any batch is at most the functional dimension. -/
theorem jacobianRankBlocks_le_funDimBlocks {n : ℕ} (X : Fin n → Matrix T d ℝ)
    (β : BlockParams A) : jacobianRankBlocks A S X β ≤ funDimBlocks A S β := by
  -- a member of a set of naturals bounded above is at most its supremum
  exact le_csSup (funDimBlocks_set_bddAbove_bla β) ⟨n, X, rfl⟩

/-- Some finite batch attains the functional dimension. -/
theorem exists_jacobianRankBlocks_eq_funDimBlocks (β : BlockParams A) :
    ∃ (n : ℕ) (X : Fin n → Matrix T d ℝ), jacobianRankBlocks A S X β = funDimBlocks A S β := by
  -- a nonempty set of naturals that is bounded above contains its supremum
  obtain ⟨n, X, h⟩ := Nat.sSup_mem (s := {r : ℕ | ∃ (n : ℕ) (X : Fin n → Matrix T d ℝ),
      r = jacobianRankBlocks A S X β}) ⟨_, 0, fun i => i.elim0, rfl⟩
    (funDimBlocks_set_bddAbove_bla β)
  exact ⟨n, X, h.symm⟩

end Skips
