import SkipsLean.Residual.BlocksAlone
import SkipsLean.Dimension.UpperBound
import SkipsLean.Residual.BlocksAloneGeneral

/-!
# Skipless networks without an embedding and a readout: a change of basis is left

Paper (skips paper), proof of Theorem A.28 (i): "Without an embedding, a readout and attention
blocks, for `L ≥ 2` the changes of basis at `h_1` have orbits of positive dimension, since every
block has at least one hidden unit, so Lemma A.26 applies again."

Here, for a network of `L + 2` blocks without skips, without normalization, without an embedding
and a readout (`Residual/BlocksAlone.lean`), with differentiable blocks: on every batch and at
every parameter of the blocks, the Jacobian in the reads and the writes has rank at most `P − 1`.
The direction of the scalings of `h_1`, `(W_write^1, −W_read^2)` at the write of block 1 and the
read of block 2, is in its kernel (`cobDir_mem_flat_skipless`), and it is nonzero unless
`W_write^1 = 0`; if `W_write^1 = 0`, then `h_1 = 0` whatever the read of block 1 is, so the
directions at the read of block 1 are in the kernel. The statement asks a model dimension of at
least one and at least one column in the read of block 1 (for an MLP block, one hidden unit).

Numeric check (the rank is `P − (L − 1) d²` at generic parameters of GELU blocks of width at least
`d`, and `0` at a parameter with `W_write^1 = 0`, `W_read^2 = 0`):
`blocks_alone_mlp_check_2026-11-25.py`.
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise

variable {T d : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d]

omit [Fintype T] in
/-- Helper: a nonzero direction in the kernel of the Jacobian of the family on a batch lowers its
rank by one (rank–nullity). -/
private theorem add_one_le_of_mem_ker_bas {L' : ℕ} {A : Arch T d L'} (S : Fin L' → Matrix d d ℝ)
    {n : ℕ} (X : Fin n → Matrix T d ℝ) (β : BlockParams A) {η : BlockParams A} (hη0 : η ≠ 0)
    (hη : η ∈ LinearMap.ker (fderiv ℝ
      (fun β' : BlockParams A => fun i : Fin n => evalBlocks A S β' (X i)) β).toLinearMap) :
    jacobianRankBlocks A S X β + 1 ≤ Module.finrank ℝ (BlockParams A) := by
  have hrn : jacobianRankBlocks A S X β + Module.finrank ℝ (LinearMap.ker (fderiv ℝ
      (fun β' : BlockParams A => fun i : Fin n => evalBlocks A S β' (X i)) β).toLinearMap)
      = Module.finrank ℝ (BlockParams A) :=
    LinearMap.finrank_range_add_finrank_ker _
  -- the kernel is not `0`, so it has dimension at least one
  have hpos : 0 < Module.finrank ℝ (LinearMap.ker (fderiv ℝ
      (fun β' : BlockParams A => fun i : Fin n => evalBlocks A S β' (X i)) β).toLinearMap) := by
    refine Nat.pos_of_ne_zero fun h0 => hη0 ?_
    rw [Submodule.finrank_eq_zero] at h0
    rw [h0] at hη
    exact (Submodule.mem_bot ℝ).1 hη
  omega

/-- Helper: the line `τ ↦ a + τ b` has the velocity `b`. -/
private theorem hasDerivAt_line_bas {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a b : E) : HasDerivAt (fun τ : ℝ => a + τ • b) b 0 := by
  have h := ((hasDerivAt_id (0 : ℝ)).smul_const b).const_add a
  rw [one_smul] at h
  exact h

omit [Fintype T] [DecidableEq d] in
/-- Helper: without skips, if the write of the first block is `0`, then `h_1 = 0` and the
function does not depend on the read of the first block: two parameters that differ only there
have the same hidden states. -/
private theorem hidden_eq_of_write_zero_bas {A : Arch T d (L + 2)} {dIn dOut : Type*}
    [Fintype dIn] (θ θ' : Params A dIn dOut) (hE : θ'.E = θ.E)
    (hw : ∀ ℓ, θ'.write ℓ = θ.write ℓ) (hr : ∀ ℓ, ℓ ≠ 0 → θ'.read ℓ = θ.read ℓ)
    (h0 : θ.write 0 = 0) (x : Matrix T dIn ℝ) (ℓ : Fin (L + 2 + 1)) :
    hidden A 0 θ' x ℓ = hidden A 0 θ x ℓ := by
  induction ℓ using Fin.induction with
  | zero => rw [hidden_zero, hidden_zero, hE]
  | succ ℓ ih =>
    rw [hidden_succ, hidden_succ, hw ℓ]
    by_cases hℓ : ℓ = 0
    · -- `h_1 = h_0 · 0 + f_1(…) · 0 = 0` for both
      subst hℓ
      simp only [h0, Pi.zero_apply, Matrix.mul_zero, add_zero]
    · rw [ih, hr ℓ hℓ]

omit [Fintype T] [DecidableEq d] in
/-- Helper: so they compute the same function. -/
private theorem eval_eq_of_write_zero_bas {A : Arch T d (L + 2)} {dIn dOut : Type*}
    [Fintype dIn] (θ θ' : Params A dIn dOut) (hE : θ'.E = θ.E) (hD : θ'.D = θ.D)
    (hw : ∀ ℓ, θ'.write ℓ = θ.write ℓ) (hr : ∀ ℓ, ℓ ≠ 0 → θ'.read ℓ = θ.read ℓ)
    (h0 : θ.write 0 = 0) (x : Matrix T dIn ℝ) :
    eval A 0 θ' x = eval A 0 θ x := by
  show A.χ (hidden A 0 θ' x (Fin.last (L + 2))) * θ'.D
    = A.χ (hidden A 0 θ x (Fin.last (L + 2))) * θ.D
  rw [hidden_eq_of_write_zero_bas θ θ' hE hw hr h0 x, hD]

/-- **Proof of Theorem A.28 (i) of the skips paper, "for `L ≥ 2` the changes of basis at `h_1`
have orbits of positive dimension, since every block has at least one hidden unit":** for a
network of `L + 2` differentiable blocks without skips and without normalization, without an
embedding and a readout, with `d ≥ 1` and at least one column in the read of the first block: at
every parameter of the blocks and on every batch, the Jacobian in the reads and the writes has
rank at most `P − 1`. -/
theorem jacobianRankBlocks_add_one_le_skipless {A : Arch T d (L + 2)} (hA : A.χ = id)
    (hf : ∀ ℓ, Differentiable ℝ (A.f ℓ)) [Nonempty d] (hr : Nonempty (A.r 0))
    (β : BlockParams A) {n : ℕ} (X : Fin n → Matrix T d ℝ) :
    jacobianRankBlocks A 0 X β + 1 ≤ Module.finrank ℝ (BlockParams A) := by
  have hdiff : ∀ x : Matrix T d ℝ,
      DifferentiableAt ℝ (fun θ' : Params A d d => eval A 0 θ' x) β.toParams :=
    fun x => differentiable_eval hf (by rw [hA]; exact differentiable_id) x β.toParams
  by_cases hw0 : β.write 0 = 0
  · -- `W_write^1 = 0`: `h_1 = 0` whatever the read of block 1, so the direction
    -- `(0, read := Pi.single 0 M, 0, 0)` with `M ≠ 0` is flat
    obtain ⟨k⟩ := ‹Nonempty d›
    obtain ⟨j⟩ := hr
    obtain ⟨M, hM⟩ : ∃ M : Matrix d (A.r 0) ℝ, M ≠ 0 :=
      ⟨Matrix.of fun _ _ => 1, fun h => one_ne_zero (congrFun (congrFun h k) j)⟩
    refine add_one_le_of_mem_ker_bas 0 X β
      (η := ⟨0, Pi.single (M := fun ℓ => Matrix d (A.r ℓ) ℝ) 0 M, 0, 0⟩) ?_ ?_
    · intro h
      apply hM
      have h' := congrArg (fun ξ : BlockParams A => ξ.read 0) h
      exact (Pi.single_eq_same (M := fun ℓ => Matrix d (A.r ℓ) ℝ) 0 M).symm.trans h'
    · refine mem_ker_fderiv_evalBlocks_of_mem_flat β hdiff X ?_
      refine mem_flat_of_hasDerivAt' β.toParams
        (fun τ => β.toParams + τ • blockDir A ⟨0, Pi.single (M := fun ℓ => Matrix d (A.r ℓ) ℝ)
          0 M, 0, 0⟩) _ (hasDerivAt_line_bas _ _) ?_ (Filter.Eventually.of_forall fun τ x => ?_)
      · show β.toParams + (0 : ℝ) • _ = β.toParams
        rw [zero_smul, add_zero]
      · refine eval_eq_of_write_zero_bas β.toParams _ ?_ ?_ (fun ℓ => ?_) (fun ℓ hℓ => ?_) hw0 x
        · show (1 : Matrix d d ℝ) + τ • (0 : Matrix d d ℝ) = 1
          rw [smul_zero, add_zero]
        · show (1 : Matrix d d ℝ) + τ • (0 : Matrix d d ℝ) = 1
          rw [smul_zero, add_zero]
        · show β.write ℓ + τ • (0 : ∀ ℓ, Matrix (A.w ℓ) d ℝ) ℓ = β.write ℓ
          rw [Pi.zero_apply, smul_zero, add_zero]
        · show β.read ℓ + τ • Pi.single (M := fun ℓ => Matrix d (A.r ℓ) ℝ) 0 M ℓ = β.read ℓ
          rw [Pi.single_eq_of_ne (M := fun ℓ => Matrix d (A.r ℓ) ℝ) hℓ, smul_zero, add_zero]
  · -- `W_write^1 ≠ 0`: the direction of the scalings of `h_1`,
    -- `(0, read := Pi.single 1 (-W_read^2), write := Pi.single 0 W_write^1, 0)`, is
    -- `cobDir θ (Pi.single 1 I)`, flat for the network without skips
    have hη : blockDir A ⟨0, Pi.single (M := fun ℓ => Matrix d (A.r ℓ) ℝ) 1 (-(β.read 1)),
        Pi.single (M := fun ℓ => Matrix (A.w ℓ) d ℝ) 0 (β.write 0), 0⟩
        = cobDir β.toParams (Pi.single (M := fun _ => Matrix d d ℝ) 1 1) := by
      apply Params.ext'
      · show (0 : Matrix d d ℝ) = 1 * Pi.single (M := fun _ => Matrix d d ℝ) 1 1 0
        rw [Pi.single_eq_of_ne (M := fun _ => Matrix d d ℝ) Fin.zero_ne_one', Matrix.mul_zero]
      · intro ℓ
        show Pi.single (M := fun ℓ => Matrix d (A.r ℓ) ℝ) 1 (-(β.read 1)) ℓ
          = -(Pi.single (M := fun _ => Matrix d d ℝ) 1 1 ℓ.castSucc * β.read ℓ)
        by_cases hℓ : ℓ = 1
        · subst hℓ
          rw [Pi.single_eq_same, Fin.castSucc_one, Pi.single_eq_same, Matrix.one_mul]
        · have hc : ℓ.castSucc ≠ 1 := fun h =>
            hℓ (Fin.castSucc_injective _ (h.trans Fin.castSucc_one.symm))
          rw [Pi.single_eq_of_ne (M := fun ℓ => Matrix d (A.r ℓ) ℝ) hℓ,
            Pi.single_eq_of_ne (M := fun _ => Matrix d d ℝ) hc, Matrix.zero_mul, neg_zero]
      · intro ℓ
        show Pi.single (M := fun ℓ => Matrix (A.w ℓ) d ℝ) 0 (β.write 0) ℓ
          = β.write ℓ * Pi.single (M := fun _ => Matrix d d ℝ) 1 1 ℓ.succ
        by_cases hℓ : ℓ = 0
        · subst hℓ
          rw [Pi.single_eq_same, Fin.succ_zero_eq_one, Pi.single_eq_same, Matrix.mul_one]
        · have hc : ℓ.succ ≠ 1 := fun h =>
            hℓ (Fin.succ_injective _ (h.trans Fin.succ_zero_eq_one.symm))
          rw [Pi.single_eq_of_ne (M := fun ℓ => Matrix (A.w ℓ) d ℝ) hℓ,
            Pi.single_eq_of_ne (M := fun _ => Matrix d d ℝ) hc, Matrix.mul_zero]
      · show (0 : Matrix d d ℝ)
          = -(Pi.single (M := fun _ => Matrix d d ℝ) 1 1 (Fin.last (L + 2)) * 1)
        rw [Pi.single_eq_of_ne (M := fun _ => Matrix d d ℝ) Fin.one_lt_last.ne', Matrix.zero_mul,
          neg_zero]
    refine add_one_le_of_mem_ker_bas 0 X β (η := ⟨0, Pi.single
      (M := fun ℓ => Matrix d (A.r ℓ) ℝ) 1 (-(β.read 1)),
        Pi.single (M := fun ℓ => Matrix (A.w ℓ) d ℝ) 0 (β.write 0), 0⟩) ?_ ?_
    · intro h
      apply hw0
      have h' := congrArg (fun ξ : BlockParams A => ξ.write 0) h
      exact (Pi.single_eq_same (M := fun ℓ => Matrix (A.w ℓ) d ℝ) 0 (β.write 0)).symm.trans h'
    · refine mem_ker_fderiv_evalBlocks_of_mem_flat β hdiff X ?_
      rw [hη]
      exact cobDir_mem_flat_skipless β.toParams hA hf _

end Skips
