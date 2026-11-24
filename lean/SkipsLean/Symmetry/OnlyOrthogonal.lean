import SkipsLean.Symmetry.Normalized
import SkipsLean.Basic.RMSNormConverse
import SkipsLean.Network.Blocks
import SkipsLean.Activations.Gaussian
import SkipsLean.Activations.ReLU
import SkipsLean.OneBlock.UnitsSwiGLU

/-!
# Under pre-RMSNorm only orthogonal changes of basis pass (skipless networks)

Paper: "Skip Connections Unlock at Least d_model² Parameters per Layer", Lemma A.4 (Only orthogonal
changes of basis pass), and with it the skipless half of Theorem 3.3 (ii) = Theorem A.17 (i) under
pre-RMSNorm.

Lemma A.4: "Consider a skipless pre-RMSNorm network with `ε > 0` whose blocks are those of
Section 2, and let `G_0, …, G_L` be invertible. Multiply the writes into every hidden state `h_ℓ`
by `G_ℓ` on the right and its reads by `G_ℓ⁻¹` on the left. If this preserves the function at all
parameters, every `G_ℓ` is orthogonal." Its proof uses three facts: "(a) Scaling. If
`N_ε^G(c ũ) = N_ε(c u)` for all `c > 0`, then `ũ = u` and `‖u G‖ = ‖u‖`"; "(b) Blocks separate
their inputs. If rows `a` and `a'` satisfy `B(a) = B(a')` for all parameters of a block `B`, then
`a = a'`. […] For a vanilla block, `σ(a w) = σ(a' w)` for every column `w`. If `a ≠ a'`, choose `w`
with `α = a w ≠ a' w = β`, and replace `w` by `t w`: `σ(t α) = σ(t β)` for all `t`. If `β = −α`,
`σ` is even. Otherwise `σ(z) = σ(q z)` for all `z` with some `|q| < 1`, so
`σ(z) = σ(q^k z) → σ(0)`, and `σ` is constant. None of tanh, GELU, ReLU and ReLU² is even or
constant. For a gated block, `σ(a g)(a v) = σ(a' g)(a' v)` for all columns `g` and `v`, so
`σ(a g) a = σ(a' g) a'` for all `g`. If `a = 0` then `a' = 0`. Otherwise `a' = κ a` for a number
`κ ≠ 0`, and `σ(z) = κ σ(κ z)` for all `z`. For the ReLU gate this gives `κ = 1`. The SiLU and GELU
gates have `σ'(0) = 1/2`, so `κ² = 1`, and they are not odd, so `κ = 1`"; "(c) Hidden states reach
every row"; then an induction from the last hidden state.

Theorem 3.3 (ii): "The changes of basis that preserve the function at all parameters form a group
of dimension `(L + 1) dim 𝒢` in a skipless network and `dim 𝒢` in a residual one". Under
pre-RMSNorm, for a skipless network, this is: the families `G_0, …, G_L` that preserve the function
at all parameters are exactly those with every `G_ℓ` orthogonal (`eval_cob_rmsNorm` gives "if",
Lemma A.4 "only if"). The count `(L + 1) d (d − 1)/2` is the dimension of this group; it is not a
Lean statement here. (For residual networks the two characterizations are in
`Residual/OneChangeOfBasis.lean`; without normalization every family passes in a skipless network,
`eval_cob_skipless`.)

Stated here for MLP blocks and for gated blocks, with what the proof uses of the activation or
gate as hypotheses, and then for the seven kinds of block. Every block has at least one hidden
unit (a block without hidden units writes `0`, and the hidden state after it carries no
condition). Attention blocks are not defined in this library, so the lemma is not stated for
them. A change of basis is `Params.cob θ G G`.
-/

namespace Skips

open Matrix

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]
variable {σ : ℝ → ℝ} {ε : ℝ}

/-! ### Fact (b): blocks separate their inputs -/

/-- **Fact (b) for a vanilla block:** if `σ` is continuous, not even and not constant, and
`σ(a w) = σ(a' w)` for every column `w`, then `a = a'`. -/
theorem eq_of_forall_map_dotProduct_eq (hσc : Continuous σ) (hne : ¬ ∀ z, σ (-z) = σ z)
    (hnc : ¬ ∀ z, σ z = σ 0) {a a' : d → ℝ}
    (h : ∀ w : d → ℝ, σ (a ⬝ᵥ w) = σ (a' ⬝ᵥ w)) : a = a' := by
  sorry

/-- **Fact (b) for a gated block:** if the gate `σ` is not identically zero, `σ(z) = κ σ(κ z)` for
all `z` only for `κ = 1`, and `σ(a g)(a v) = σ(a' g)(a' v)` for all columns `g` and `v`, then
`a = a'`. -/
theorem eq_of_forall_gate_mul_eq (hσ0 : ∃ z, σ z ≠ 0)
    (hκ : ∀ κ : ℝ, (∀ z, σ z = κ * σ (κ * z)) → κ = 1) {a a' : d → ℝ}
    (h : ∀ g v : d → ℝ, σ (a ⬝ᵥ g) * (a ⬝ᵥ v) = σ (a' ⬝ᵥ g) * (a' ⬝ᵥ v)) : a = a' := by
  sorry

/-! ### Lemma A.4 -/

/-- **Lemma A.4 for vanilla blocks** whose activation is continuous, not even and not constant:
if the changes of basis `G_0, …, G_L` preserve the function of the skipless pre-RMSNorm network
(`ε > 0`) for all values of the parameters, every `G_ℓ` is orthogonal. -/
theorem orthogonal_of_eval_cob_skipless_rmsNorm_mlp [Nonempty T] [Nonempty dIn] [Nonempty dOut]
    (hε : 0 < ε) (hσc : Continuous σ) (hne : ¬ ∀ z, σ (-z) = σ z) (hnc : ¬ ∀ z, σ z = σ 0)
    (hhid : ∀ ℓ, Nonempty (hid ℓ)) (G : Fin (L + 1) → GL d ℝ)
    (h : ∀ (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)
      (x : Matrix T dIn ℝ),
      eval (Arch.mlp σ (rmsNorm ε) hid) 0 (θ.cob G G) x
        = eval (Arch.mlp σ (rmsNorm ε) hid) 0 θ x) :
    ∀ ℓ, (G ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ := by
  sorry

/-- **Lemma A.4 for gated blocks** whose gate is not identically zero and satisfies
`σ(z) = κ σ(κ z)` for all `z` only for `κ = 1`. -/
theorem orthogonal_of_eval_cob_skipless_rmsNorm_gated [Nonempty T] [Nonempty dIn]
    [Nonempty dOut] (hε : 0 < ε) (hσ0 : ∃ z, σ z ≠ 0)
    (hκ : ∀ κ : ℝ, (∀ z, σ z = κ * σ (κ * z)) → κ = 1)
    (hhid : ∀ ℓ, Nonempty (hid ℓ)) (G : Fin (L + 1) → GL d ℝ)
    (h : ∀ (θ : Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)
      (x : Matrix T dIn ℝ),
      eval (Arch.gated σ (rmsNorm ε) hid) 0 (θ.cob G G) x
        = eval (Arch.gated σ (rmsNorm ε) hid) 0 θ x) :
    ∀ ℓ, (G ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ := by
  sorry

/-! ### Theorem 3.3 (ii), skipless networks under pre-RMSNorm -/

/-- **Theorem 3.3 (ii), skipless, pre-RMSNorm (`ε > 0`), vanilla blocks:** the changes of basis
`G_0, …, G_L` preserve the function for all values of the parameters if and only if every `G_ℓ` is
orthogonal. -/
theorem eval_cob_skipless_rmsNorm_iff_mlp [Nonempty T] [Nonempty dIn] [Nonempty dOut]
    (hε : 0 < ε) (hσc : Continuous σ) (hne : ¬ ∀ z, σ (-z) = σ z) (hnc : ¬ ∀ z, σ z = σ 0)
    (hhid : ∀ ℓ, Nonempty (hid ℓ)) (G : Fin (L + 1) → GL d ℝ) :
    (∀ (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)
        (x : Matrix T dIn ℝ),
        eval (Arch.mlp σ (rmsNorm ε) hid) 0 (θ.cob G G) x
          = eval (Arch.mlp σ (rmsNorm ε) hid) 0 θ x)
      ↔ ∀ ℓ, (G ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ := by
  sorry

/-- **Theorem 3.3 (ii), skipless, pre-RMSNorm (`ε > 0`), gated blocks.** -/
theorem eval_cob_skipless_rmsNorm_iff_gated [Nonempty T] [Nonempty dIn] [Nonempty dOut]
    (hε : 0 < ε) (hσ0 : ∃ z, σ z ≠ 0) (hκ : ∀ κ : ℝ, (∀ z, σ z = κ * σ (κ * z)) → κ = 1)
    (hhid : ∀ ℓ, Nonempty (hid ℓ)) (G : Fin (L + 1) → GL d ℝ) :
    (∀ (θ : Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)
        (x : Matrix T dIn ℝ),
        eval (Arch.gated σ (rmsNorm ε) hid) 0 (θ.cob G G) x
          = eval (Arch.gated σ (rmsNorm ε) hid) 0 θ x)
      ↔ ∀ ℓ, (G ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ := by
  sorry

/-! ### The activations and gates of the paper -/

/-- "None of tanh, GELU, ReLU and ReLU² is even or constant", and all four are continuous. -/
theorem tanh_not_even_not_const :
    Continuous Real.tanh ∧ (¬ ∀ z, Real.tanh (-z) = Real.tanh z) ∧
      ¬ ∀ z, Real.tanh z = Real.tanh 0 := by
  sorry

theorem gelu_not_even_not_const :
    Continuous gelu ∧ (¬ ∀ z, gelu (-z) = gelu z) ∧ ¬ ∀ z, gelu z = gelu 0 := by
  sorry

theorem relu_not_even_not_const :
    Continuous relu ∧ (¬ ∀ z, relu (-z) = relu z) ∧ ¬ ∀ z, relu z = relu 0 := by
  sorry

theorem reluSq_not_even_not_const :
    Continuous reluSq ∧ (¬ ∀ z, reluSq (-z) = reluSq z) ∧ ¬ ∀ z, reluSq z = reluSq 0 := by
  sorry

/-- The ReLU gate: `σ(z) = κ σ(κ z)` for all `z` only for `κ = 1`. -/
theorem relu_gate_scale : (∃ z, relu z ≠ 0) ∧ ∀ κ : ℝ, (∀ z, relu z = κ * relu (κ * z)) → κ = 1 := by
  sorry

/-- The SiLU gate: `σ'(0) = 1/2` and SiLU is not odd, so `σ(z) = κ σ(κ z)` only for `κ = 1`. -/
theorem silu_gate_scale : (∃ z, silu z ≠ 0) ∧ ∀ κ : ℝ, (∀ z, silu z = κ * silu (κ * z)) → κ = 1 := by
  sorry

/-- The GELU gate: `σ'(0) = 1/2` and GELU is not odd, so `σ(z) = κ σ(κ z)` only for `κ = 1`. -/
theorem gelu_gate_scale : (∃ z, gelu z ≠ 0) ∧ ∀ κ : ℝ, (∀ z, gelu z = κ * gelu (κ * z)) → κ = 1 := by
  sorry

end Skips
