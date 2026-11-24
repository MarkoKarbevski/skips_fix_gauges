import SkipsLean.Depth.RegularZeroGelu
import SkipsLean.Depth.StepZeroGelu
import SkipsLean.Depth.SuffixZeroBatch
import SkipsLean.Depth.DomainZeroConnected
import SkipsLean.Dimension.GenericRankOn

/-!
# Theorem 5.2 (ii) for GELU blocks under pre-RMSNorm with `ε = 0`

Paper (dimension paper): Theorem 5.2 (ii), the case `ε = 0` for GELU blocks, and Appendix D.7,
"The parts together", "The case (0)":

"By Lemma D.5 and Lemma D.18 or Lemma D.19, Claim `(D_k)` holds at `θ*` for `k = L`, then for
`k = L − 1, …, 0`. By Proposition D.4 there is a finite batch `X*`, with `xE ≠ 0` for all its
inputs, on which the Jacobian at `θ*` has the rank (13). By (R2), `θ* ∈ O_{X*}`. The sum of the
squares of the minors of this size of the Jacobian of `F_{X*}` is real-analytic on the connected
open set `O_{X*}` and does not vanish at `θ*`, so its zero set has measure zero, and so has the
complement of `O_{X*}` (Lemma D.20). Hence the rank on `X*` is at least (13) at almost every
parameter."

Theorem 5.2: "Let `d_in, d_out ≥ d_model ≥ 2`, and consider networks without biases whose blocks
are all of one kind, tanh, GELU, SwiGLU or GeGLU, each with at least `d_model` hidden units. In the
following cases the functional dimension at generic parameters is `P − (L + 1) dim 𝒢 − s` […].
(ii) GELU blocks: under pre-RMSNorm with `ε > 0` and with `ε = 0`." Here `s = 0`, and for `ε = 0`
the group is `CO(d)`, of dimension `d(d−1)/2 + 1`.

`Depth/TanhZero.lean` has the same three statements for `tanh`; the proofs differ only in the
step (Lemma D.19, `claimZero_castSucc_gelu`, in the place of Lemma D.18) and in the parameter `θ*`
(`exists_regularZero_gelu_path`). As there, `fd` is `funDim` of Lean's total network.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut] {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]

/-- **"By Lemma D.5 and […] Lemma D.19, Claim `(D_k)` holds at `θ*` for `k = L`, then for
`k = L − 1, …, 0`":** at a regular `θ` whose every block satisfies (P1), and (P2) for a
`κ ∈ (0, 1]` such that `𝓑_{>k+1}` is holomorphic on `C_κ`, the claim `(D_k)` holds for every `k`. -/
theorem claimZero_of_gelu_path [Nonempty T]
    {θ : Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm 0) hid) dIn dOut}
    (hθ : RegularZero (Arch.mlp gelu (rmsNorm 0) hid) θ) (hd : 2 ≤ Fintype.card d)
    (hblocks : ∀ k : Fin L, CondP1 θ k ∧
      ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1 ∧ HolomorphicOnCone geluC θ k.succ κ ∧ CondP2 θ k κ)
    (k : Fin (L + 1)) : ClaimZero (Arch.mlp gelu (rmsNorm 0) hid) θ k := by
  sorry

/-- **"By Proposition D.4 there is a finite batch `X*`, with `xE ≠ 0` for all its inputs, on which
the Jacobian at `θ*` has the rank (13). By (R2), `θ* ∈ O_{X*}`":** a parameter `θ*` and a finite
batch `X*` of inputs without a zero row such that `θ* ∈ O_{X*}` and the rank on `X*` at `θ*` is
`P − (L+1)(d(d−1)/2 + 1)`. -/
theorem exists_jacobianRank_gelu_rmsNorm_zero [Nonempty T] (hd : 2 ≤ Fintype.card d)
    (hdIn : Fintype.card d ≤ Fintype.card dIn) (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∃ (θ : Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm 0) hid) dIn dOut) (n : ℕ)
      (X : Fin n → Matrix T dIn ℝ), (∀ i t, X i t ≠ 0) ∧
      θ ∈ hiddenNonzero gelu hid X (Fin.last L) ∧
      jacobianRank (Arch.mlp gelu (rmsNorm 0) hid) 0 X θ
          + (L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
        = Module.finrank ℝ
            (Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm 0) hid) dIn dOut) := by
  sorry

/-- **Theorem 5.2 (ii) of the dimension paper, GELU blocks under pre-RMSNorm with `ε = 0`:** for
`d_in, d_out ≥ d ≥ 2`, a skipless network of GELU blocks with at least `d` hidden units each, and
at least one token: at almost every parameter, `fd = P − (L+1)(d(d−1)/2 + 1)`. -/
theorem ae_funDim_gelu_skipless_rmsNorm_zero [Nonempty T]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, funDim (Arch.mlp gelu (rmsNorm 0) hid) 0 θ
        + (L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
      = Module.finrank ℝ
          (Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm 0) hid) dIn dOut) := by
  sorry

end Skips
