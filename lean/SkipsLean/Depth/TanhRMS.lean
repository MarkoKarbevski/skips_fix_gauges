import SkipsLean.Depth.StepTanhRMS
import SkipsLean.Depth.Tanh

/-!
# Theorem 5.2 (i) under pre-RMSNorm with `ε > 0`: `tanh` blocks at any depth

Paper (dimension paper): Theorem 5.2 (i), the case of pre-RMSNorm with `ε > 0`, and its proof in
Appendix D.7 ("The parts together", first paragraph, which treats the cases (n) and (+) together).

A network of `L` `tanh` blocks without skip connections and without biases, under pre-RMSNorm with
`ε > 0`, with `d_in, d_out ≥ d` and at least `d` hidden units in every block, has the functional
dimension `P - (L + 1) d (d - 1) / 2` at generic parameters.

The conditions on `θ` are those of the case without normalization (`TanhDepthGeneric`). Claim
`(D_L)` holds (Lemma D.5), Lemma D.7 gives `(D_k)` for `k = L - 1, …, 0`, and Proposition D.4 gives
the functional dimension.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)] {ε : ℝ}
variable (θ : Params (Arch.mlp (T := T) (d := d) Real.tanh (rmsNorm ε) hid) dIn dOut)

/-- Under the conditions Claim `(D_k)` of the case (+) holds at every hidden state: `(D_L)` by
Lemma D.5, and then `(D_k)` for `k = L - 1, …, 0` by Lemma D.7. -/
theorem claimRMS_of_tanhDepthGeneric [Nonempty T] (hε : 0 < ε) (hθ : TanhDepthGeneric θ)
    (k : Fin (L + 1)) : ClaimRMS (Arch.mlp Real.tanh (rmsNorm ε) hid) θ k := by
  -- `(D_L)` by Lemma D.5, then `(D_{k+1}) ⇒ (D_k)` by Lemma D.7
  induction k using Fin.reverseInduction with
  | last => exact claimRMS_last _ θ hε rfl hθ.rank_D
  | cast k ih =>
    exact claimRMS_castSucc_tanh θ hε (regular_of_tanhDepthGeneric θ hθ) k
      (hθ.write_row_ne_zero k) (hθ.read_cols_indep k) ih

/-- **Theorem 5.2 (i) under pre-RMSNorm with `ε > 0`, under the conditions of its proof:** the
functional dimension of a network of `L` `tanh` blocks is `P - (L + 1) d (d - 1) / 2`. -/
theorem funDim_tanh_skipless_rmsNorm [Nonempty T] (hε : 0 < ε) (hθ : TanhDepthGeneric θ) :
    funDim (Arch.mlp Real.tanh (rmsNorm ε) hid) 0 θ
        + (L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2)
      = Module.finrank ℝ
          (Params (Arch.mlp (T := T) (d := d) Real.tanh (rmsNorm ε) hid) dIn dOut) :=
  -- Proposition D.4, with the blocks analytic, `θ` regular and `(D_0)`
  funDim_of_claimRMS _ θ hε rfl (fun ℓ => analyticOnNhd_f_mlp analyticOnNhd_tanh ℓ)
    (regular_of_tanhDepthGeneric θ hθ) (claimRMS_of_tanhDepthGeneric θ hε hθ 0)

/-- **Theorem 5.2 (i), the case of pre-RMSNorm with `ε > 0`:** a network of `L` `tanh` blocks
without skip connections and without biases, under pre-RMSNorm with `ε > 0`, with
`d_in, d_out ≥ d ≥ 2` and at least `d` hidden units in every block, has the functional dimension
`P - (L + 1) d (d - 1) / 2` at generic parameters. -/
theorem ae_funDim_tanh_skipless_rmsNorm [Nonempty T] (hε : 0 < ε)
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) Real.tanh (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, funDim (Arch.mlp Real.tanh (rmsNorm ε) hid) 0 θ
        + (L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2)
      = Module.finrank ℝ
          (Params (Arch.mlp (T := T) (d := d) Real.tanh (rmsNorm ε) hid) dIn dOut) := by
  have : Nonempty d := Fintype.card_pos_iff.1 (by omega)
  -- the conclusion holds wherever the conditions of the proof hold
  filter_upwards [ae_tanhDepthGeneric μ hdIn hdOut hhid] with θ hθ
  exact funDim_tanh_skipless_rmsNorm θ hε hθ

end Skips
