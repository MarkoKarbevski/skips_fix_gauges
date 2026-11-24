import SkipsLean.Depth.RegularZeroGelu
import SkipsLean.Depth.StepZeroGelu
import SkipsLean.Depth.SuffixZeroBatch
import SkipsLean.Depth.DomainZeroConnected
import SkipsLean.Dimension.GenericRankOn
import SkipsLean.Activations.Analytic

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
  -- `(D_L)` by Lemma D.5, then `(D_{k+1}) ⇒ (D_k)` by Lemma D.19
  induction k using Fin.reverseInduction with
  | last => exact claimZero_last _ θ rfl hθ.rank_D hd
  | cast k ih =>
    obtain ⟨hP1, κ, hκ, hκ1, hhol, hP2⟩ := hblocks k
    exact claimZero_castSucc_gelu hθ hd k hP1 hκ hκ1 hhol hP2 ih

/-- Helper: GELU vanishes exactly at `0` (`gelu z = z Φ(z)` and `Φ(z) > 0`). -/
private theorem gelu_eq_zero_iff_gz (z : ℝ) : gelu z = 0 ↔ z = 0 := by
  rw [gelu, mul_eq_zero]
  exact ⟨fun h => h.resolve_right (gaussCdf_pos z).ne', Or.inl⟩

omit [Fintype T] [DecidableEq d] in
/-- Helper, (R2) of the paper: at a regular parameter no row of a hidden state vanishes at an input
`x` such that no row of `x E` vanishes (the rows of `N(h_ℓ)` lie on the sphere `‖n‖² = d`). -/
private theorem hidden_row_ne_zero_gz
    {θ : Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm 0) hid) dIn dOut}
    (hθ : RegularZero (Arch.mlp gelu (rmsNorm 0) hid) θ) (x : Matrix T dIn ℝ)
    (hx : ∀ t, (x * θ.E) t ≠ 0) (j : Fin (L + 1)) (t : T) :
    hidden (Arch.mlp gelu (rmsNorm 0) hid) 0 θ x j t ≠ 0 := by
  induction j using Fin.induction generalizing t with
  | zero => rw [hidden_zero]; exact hx t
  | succ ℓ ih =>
    -- without skips `h_{ℓ+1} = f_ℓ(N(h_ℓ) W_read) W_write`
    rw [hidden_succ, Pi.zero_apply, Matrix.mul_zero, zero_add]
    exact hθ.block_ne_zero ℓ _ (fun t' => rmsNorm_zero_dotProduct_self _ t' (ih t')) t

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
  -- `θ*` of Appendix D.6, `(D_0)` from the claim above, the batch of Proposition D.4
  obtain ⟨θ, hθ, hblocks⟩ := exists_regularZero_gelu_path (T := T) (dIn := dIn) (dOut := dOut)
    (hid := hid) hd hdIn hdOut hhid
  obtain ⟨n, X, hXE, hrank⟩ := exists_batch_jacobianRank_of_claimZero _ θ rfl
    (fun ℓ => analyticOnNhd_f_mlp analyticOnNhd_gelu ℓ) hθ hd
    (claimZero_of_gelu_path hθ hd hblocks 0)
  refine ⟨θ, n, X, fun i t hXt => hXE i t ?_, ?_, hrank⟩
  · -- a zero row of `x` gives a zero row of `x E`
    rw [Matrix.mul_apply_eq_vecMul, hXt, Matrix.zero_vecMul]
  · -- (R2): no row of a hidden state vanishes
    intro i j _ t
    exact hidden_row_ne_zero_gz hθ (X i) (hXE i) j t

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
  have : Nonempty d := Fintype.card_pos_iff.1 (by omega)
  obtain ⟨θ₀, n, X, hX, hmem, hrank⟩ :=
    exists_jacobianRank_gelu_rmsNorm_zero (T := T) (hid := hid) hd hdIn hdOut hhid
  have hhid2 : ∀ ℓ, 2 ≤ Fintype.card (hid ℓ) := fun ℓ => hd.trans (hhid ℓ)
  -- Lemma D.20: `O_X` is open, connected, of full measure, and `F_X` is analytic on it; so the
  -- rank on `X` is at least its rank at `θ*` at almost every parameter
  have h1 := ae_jacobianRank_ge_of_isPreconnected _ 0 μ X
    (isOpen_hiddenNonzero analyticOnNhd_gelu X (Fin.last L))
    (isPreconnected_hiddenNonzero analyticOnNhd_gelu gelu_eq_zero_iff_gz hd hhid2 X hX
      (Fin.last L))
    (measure_compl_hiddenNonzero analyticOnNhd_gelu gelu_eq_zero_iff_gz hd hhid2 X hX μ
      (Fin.last L))
    (analyticOnNhd_evalBatch_hiddenNonzero analyticOnNhd_gelu X) hmem
  -- the upper bound (13) where `E` and the writes have rank `d`
  have h2 := ae_funDim_add_le_skipless_rmsNorm_zero μ rfl hdIn hhid
  filter_upwards [h1, h2] with θ ha hb
  have hc := jacobianRank_le_funDim (S := 0) θ X
  generalize (L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2 + 1) = c at *
  generalize Module.finrank ℝ
    (Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm 0) hid) dIn dOut) = P at *
  omega

end Skips
