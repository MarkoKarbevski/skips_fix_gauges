import SkipsLean.Depth.StepZeroTanhPath
import SkipsLean.Depth.FlatAtWriteRows
import SkipsLean.Depth.RowsAux
import SkipsLean.Depth.SuffixZeroClaim

/-!
# The step from `(D_{k+1})` to `(D_k)` for a `tanh` block under pre-RMSNorm with `ε = 0`

Paper (dimension paper): Appendix D.6, "The step for tanh on the path" and Lemma D.18.

"Let `σ = tanh`. Consider, for a block `ℓ` with `W = W_read^ℓ`, its columns `c_j`, `V = W_write^ℓ`
and `κ_ℓ` of Lemma D.14:
 (S1) any two rows of `V` are linearly independent;
 (S2) the columns of `W` are linearly independent over `ℚ`;
 (S3) there are a unit row `ξ₀` and a number `ρ ∈ (0, 1]` such that every `ξ₀c_j ≠ 0` and, with
      `s_j` the sign of `ξ₀c_j` and `s̄ = (s_1, …, s_q)`: the rows `w̃V` with `|w̃_j − s_j| ≤ ρ` for
      all `j` lie in `C_{κ_ℓ}`, and `e^{−2√d |ξ₀c_j|} < ρ/3` for every `j`."

"Lemma D.18 (The step for tanh on the path). Let `σ = tanh`, in the case (0), let `θ` be regular,
and let block `k + 1` satisfy (S1) to (S3). Then `(D_{k+1})` implies `(D_k)`."

Its proof, after the part for one pair `ξ, ξ'` (`Depth/StepZeroTanhPath.lean`): "(a) … Its
imaginary part is `ξ (Z + Zᵀ) ξ'ᵀ = 0`. This holds for every unit row `ξ'` orthogonal to `ξ`, so
`ξ (Z + Zᵀ)` is a multiple of `ξ`, for every `ξ ∈ P'` and then, by continuity, for every `ξ` in the
open set `P`. A matrix for which every row of an open set is an eigenvector is a multiple of the
identity. So `Z + Zᵀ = 2β_k I`, and `Z = Y_k + β_k I` with `Y_k` antisymmetric. (b) … so
`ξ (Y_k W + η_W) = 0` for every `ξ ∈ P'`, and `η_W = −Y_k W`. (c) … By Lemma D.3 with `A = V`,
`η_V = V Z'` and (16) holds for `k + 1` with `Z'` and `η'`. By `(D_{k+1})`, `Z' = Y_{k+1} + β_{k+1} I`
and `η'` is as in (18). With (a) and (b) this is (18) for `k`."

Here the number `κ_ℓ` of Lemma D.14 is any `κ > 0` such that `𝓑_{>ℓ}` is holomorphic on the cone
`C_κ` (`HolomorphicOnCone`, a hypothesis of the lemma); the rows `w̃` of (S3) are complex rows.
Numbering as in `Depth/StepTanh.lean`: the block is `k : Fin L`, the paper's block `k + 1`; the
hidden state before it is `k.castSucc` and after it `k.succ`.
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut] {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)] {σ : ℝ → ℝ}

/-- **Condition (S3)** for block `k` (read `W` with the columns `c_j`, write `V`) and the cone
`C_κ`: there are a unit row `ξ₀` and a number `ρ ∈ (0, 1]` such that every `ξ₀c_j ≠ 0` and, with
`s_j` the sign of `ξ₀c_j`: the rows `w̃V` with `|w̃_j − s_j| ≤ ρ` for all `j` lie in `C_κ`, and
`e^{−2√d |ξ₀c_j|} < ρ/3` for every `j`. -/
def CondS3 (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) (k : Fin L)
    (κ : ℝ) : Prop :=
  ∃ (ξ₀ : d → ℝ) (ρ : ℝ), ξ₀ ⬝ᵥ ξ₀ = 1 ∧ 0 < ρ ∧ ρ ≤ 1 ∧
    (∀ j : hid k, (ξ₀ ᵥ* θ.read k) j ≠ 0) ∧
    (∀ w : hid k → ℂ,
      (∀ j, ‖w j - ((Real.sign ((ξ₀ ᵥ* θ.read k) j) : ℝ) : ℂ)‖ ≤ ρ) →
        w ᵥ* θ.toC.2.1 k ∈ complexCone κ) ∧
    ∀ j : hid k,
      Real.exp (-(2 * (Real.sqrt (Fintype.card d) * |(ξ₀ ᵥ* θ.read k) j|))) < ρ / 3

/-- **Lemma D.18 of the dimension paper (the step for `tanh` on the path).** Let `σ = tanh`, in the
case (0), `d ≥ 2`, let `θ` be regular, let `𝓑_{>k+1}` be holomorphic on the cone `C_κ`, `κ > 0`
(Lemma D.14), and let block `k` satisfy (S1), any two rows of its write are linearly independent,
(S2), the columns of its read are linearly independent over `ℚ`, and (S3) for `C_κ`. Then
`(D_{k+1})` implies `(D_k)`. -/
theorem claimZero_castSucc_tanh [Nonempty T]
    {θ : Params (Arch.mlp (T := T) (d := d) Real.tanh (rmsNorm 0) hid) dIn dOut}
    (hθ : RegularZero (Arch.mlp Real.tanh (rmsNorm 0) hid) θ) (hd : 2 ≤ Fintype.card d)
    (k : Fin L)
    (hS1 : ∀ i j : hid k, i ≠ j → ∀ a c : ℝ, a • θ.write k i + c • θ.write k j = 0 →
      a = 0 ∧ c = 0)
    (hS2 : LinearIndependent ℚ (fun j : hid k => fun i : d => θ.read k i j))
    {κ : ℝ} (hκ : 0 < κ) (hhol : HolomorphicOnCone Complex.tanh θ k.succ κ)
    (hS3 : CondS3 θ k κ)
    (hk : ClaimZero (Arch.mlp Real.tanh (rmsNorm 0) hid) θ k.succ) :
    ClaimZero (Arch.mlp Real.tanh (rmsNorm 0) hid) θ k.castSucc := by
  sorry

end Skips
