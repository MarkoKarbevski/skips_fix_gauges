import SkipsLean.Depth.SuffixZero

/-!
# The final normalization with `ε = 0` and the readout: what a flat direction does to a hidden state

Paper (skips paper), proof of Theorem B.1 (iv), "The skipless network: equality": "As in the case
`ε = 0` of part (iii), `η_D = −Y D` with `Y` antisymmetric, since `h_1` takes all values in an
open set, and `D_θ h_1 η = h_1 Y + μ h_1` with a number `μ(x)` at each input of `Ω`." The case
`ε = 0` of part (iii) says: "Now `N_ε` maps onto the sphere of radius `√d_model`", and the kernel
of the derivative of `N_0` at a row `h ≠ 0` is the line `ℝ h`.

Here this step as one statement on the map `(h, D) ↦ N_0(h) D`, with no network in it: let `g i`
be hidden states with no zero row and `k i` their variations, for `i` in any index set (the inputs
of a network), and let `δ` be a variation of the readout `D` of rank `d`. If the output
`N_0(g i) D` does not move to first order, `𝐃N_0(g i)[k i] D + N_0(g i) δ = 0` for every `i`, and
the rows of the `g i` fill a nonempty open set of rows, then `δ = −Y D` for an antisymmetric `Y`,
and every row of `k i` is the row of `g i` times `Y` plus a multiple of the row of `g i`; the
multiple is `⟨g, k⟩ / ⟨g, g⟩`.

It is used for the skipless network of one ReLU or ReLU² block
(`OneBlock/SkiplessHomogeneousRMSZeroEq.lean`), where `g` is the output of the block without the
normalization before it.
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise

variable {T d dOut : Type*} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dOut]

/-- **Proof of Theorem B.1 (iv) of the skips paper, the final normalization (equation (18)):** if
`𝐃N_0(g i)[k i] D + N_0(g i) δ = 0` for all `i`, the readout `D` has rank `d`, no row of a `g i`
is zero and the rows of the `g i` fill a nonempty open set, then `δ = −Y D` with `Y`
antisymmetric, and each row of `k i` is the row of `g i` times `Y` plus `⟨g, k⟩ / ⟨g, g⟩` times
the row of `g i`. -/
theorem exists_antisymm_of_fderiv_rmsNorm_zero_mul {ι : Type*} (g k : ι → Matrix T d ℝ)
    (D δ : Matrix d dOut ℝ) (hD : D.rank = Fintype.card d)
    (hg : ∀ i t, g i t ≠ 0)
    (hO : ∃ O : Set (d → ℝ), IsOpen O ∧ O.Nonempty ∧ ∀ v ∈ O, ∃ i t, g i t = v)
    (h : ∀ i, fderiv ℝ (rmsNorm 0 : Matrix T d ℝ → Matrix T d ℝ) (g i) (k i) * D
      + rmsNorm 0 (g i) * δ = 0) :
    ∃ Y : Matrix d d ℝ, Yᵀ = -Y ∧ δ = -(Y * D) ∧
      ∀ i t, k i t = g i t ᵥ* Y + ((g i t ⬝ᵥ k i t) / (g i t ⬝ᵥ g i t)) • g i t := by
  sorry

end Skips
