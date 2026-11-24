import SkipsLean.Depth.RegularZeroTanh
import SkipsLean.Depth.SuffixZeroBatch
import SkipsLean.Depth.DomainZeroConnected
import SkipsLean.Dimension.GenericRankOn

/-!
# Theorem 5.2 (i) for `tanh` blocks under pre-RMSNorm with `ε = 0`

Paper (dimension paper): Theorem 5.2 (i), the case `ε = 0` for tanh blocks, and Appendix D.7, "The
parts together", "The case (0)":

"By Lemma D.5 and Lemma D.18 or Lemma D.19, Claim `(D_k)` holds at `θ*` for `k = L`, then for
`k = L − 1`, and so on down to `k = 0`. By Proposition D.4 there is a finite batch `X*`, with
`xE ≠ 0` for all its inputs, on which the Jacobian at `θ*` has the rank (13). By (R2),
`θ* ∈ O_{X*}`. The sum of the squares of the minors of this size of the Jacobian of `F_{X*}` is
real-analytic on the connected open set `O_{X*}` and does not vanish at `θ*`, so its zero set has
measure zero, and so has the complement of `O_{X*}` (Lemma D.20). Hence the rank on `X*` is at
least (13) at almost every parameter. Where `E` and every `W_write^ℓ` have rank `d_model`, it is at
most (13) on every batch. So at generic parameters the functional dimension is (13)."

In the case (0) the rank (13) is `P − (L + 1)(d(d−1)/2 + 1)`: under pre-RMSNorm with `ε = 0` every
hidden state has the symmetries of the group `CO(d)`, of dimension `d(d−1)/2 + 1`.

Stated here: the claim `(D_k)` at the parameter `θ*` of `Depth/RegularZeroTanh.lean`; a parameter
and a batch in its domain with the rank (13); and the theorem, at generic parameters (almost every
parameter, for any Lebesgue measure of the parameters).
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut] {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]

/-- **Appendix D.7, the case (0), "Claim `(D_k)` holds at `θ*` for `k = L`, then for `k = L − 1`,
and so on down to `k = 0`":** if `θ` is regular and every block satisfies (S1), (S2), and (S3) for
a cone on which the network after the block is holomorphic, then `(D_k)` holds at `θ` for every
`k` (`tanh` blocks, `d ≥ 2`). -/
theorem claimZero_of_tanh_path [Nonempty T]
    {θ : Params (Arch.mlp (T := T) (d := d) Real.tanh (rmsNorm 0) hid) dIn dOut}
    (hθ : RegularZero (Arch.mlp Real.tanh (rmsNorm 0) hid) θ) (hd : 2 ≤ Fintype.card d)
    (hblocks : ∀ k : Fin L,
      (∀ i j : hid k, i ≠ j → ∀ a c : ℝ, a • θ.write k i + c • θ.write k j = 0 →
        a = 0 ∧ c = 0) ∧
      LinearIndependent ℚ (fun j : hid k => fun i : d => θ.read k i j) ∧
      ∃ κ : ℝ, 0 < κ ∧ HolomorphicOnCone Complex.tanh θ k.succ κ ∧ CondS3 θ k κ)
    (k : Fin (L + 1)) : ClaimZero (Arch.mlp Real.tanh (rmsNorm 0) hid) θ k := by
  sorry

/-- **Appendix D.7, the case (0), "there is a finite batch `X*`, with `xE ≠ 0` for all its inputs,
on which the Jacobian at `θ*` has the rank (13). By (R2), `θ* ∈ O_{X*}`":** for
`d_in, d_out ≥ d ≥ 2` and at least `d` hidden units in every block there are a parameter `θ*` and a
finite batch `X*` of inputs without a zero row such that `θ*` is in the domain `O_{X*}` (no row of
a hidden state vanishes) and the Jacobian on `X*` at `θ*` has the rank
`P − (L + 1)(d(d−1)/2 + 1)`. -/
theorem exists_jacobianRank_tanh_rmsNorm_zero [Nonempty T] (hd : 2 ≤ Fintype.card d)
    (hdIn : Fintype.card d ≤ Fintype.card dIn) (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∃ (θ : Params (Arch.mlp (T := T) (d := d) Real.tanh (rmsNorm 0) hid) dIn dOut) (n : ℕ)
      (X : Fin n → Matrix T dIn ℝ), (∀ i t, X i t ≠ 0) ∧
      θ ∈ hiddenNonzero Real.tanh hid X (Fin.last L) ∧
      jacobianRank (Arch.mlp Real.tanh (rmsNorm 0) hid) 0 X θ
          + (L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
        = Module.finrank ℝ
            (Params (Arch.mlp (T := T) (d := d) Real.tanh (rmsNorm 0) hid) dIn dOut) := by
  sorry

/-- **Theorem 5.2 (i) of the dimension paper, the case of pre-RMSNorm with `ε = 0`, for `tanh`
blocks:** a network of `L` `tanh` blocks without skip connections and without biases, under
pre-RMSNorm with `ε = 0`, with `d_in, d_out ≥ d ≥ 2` and at least `d` hidden units in every block,
has the functional dimension `P − (L + 1)(d(d−1)/2 + 1)` at generic parameters. -/
theorem ae_funDim_tanh_skipless_rmsNorm_zero [Nonempty T]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) Real.tanh (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, funDim (Arch.mlp Real.tanh (rmsNorm 0) hid) 0 θ
        + (L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
      = Module.finrank ℝ
          (Params (Arch.mlp (T := T) (d := d) Real.tanh (rmsNorm 0) hid) dIn dOut) := by
  sorry

end Skips
