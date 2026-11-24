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
  -- `(D_L)` by Lemma D.5, then `(D_{k+1}) ⇒ (D_k)` by Lemma D.18
  induction k using Fin.reverseInduction with
  | last => exact claimZero_last _ θ rfl hθ.rank_D hd
  | cast k ih =>
    obtain ⟨κ, hκ, hhol, hS3⟩ := (hblocks k).2.2
    exact claimZero_castSucc_tanh hθ hd k (hblocks k).1 (hblocks k).2.1 hκ hhol hS3 ih

/-- Helper: `tanh` vanishes exactly at `0`. -/
private theorem tanh_eq_zero_iff_tz (z : ℝ) : Real.tanh z = 0 ↔ z = 0 := by
  rw [Real.tanh_eq_sinh_div_cosh, div_eq_zero_iff, Real.sinh_eq_zero]
  exact ⟨fun h => h.resolve_right (Real.cosh_pos z).ne', Or.inl⟩

omit [Fintype T] [DecidableEq d] in
/-- Helper, (R2) of the paper: at a regular parameter no row of a hidden state vanishes at an input
`x` such that no row of `x E` vanishes (the rows of `N(h_ℓ)` lie on the sphere `‖n‖² = d`). -/
private theorem hidden_row_ne_zero_tz
    {θ : Params (Arch.mlp (T := T) (d := d) Real.tanh (rmsNorm 0) hid) dIn dOut}
    (hθ : RegularZero (Arch.mlp Real.tanh (rmsNorm 0) hid) θ) (x : Matrix T dIn ℝ)
    (hx : ∀ t, (x * θ.E) t ≠ 0) (j : Fin (L + 1)) (t : T) :
    hidden (Arch.mlp Real.tanh (rmsNorm 0) hid) 0 θ x j t ≠ 0 := by
  induction j using Fin.induction generalizing t with
  | zero => rw [hidden_zero]; exact hx t
  | succ ℓ ih =>
    -- without skips `h_{ℓ+1} = f_ℓ(N(h_ℓ) W_read) W_write`
    rw [hidden_succ, Pi.zero_apply, Matrix.mul_zero, zero_add]
    exact hθ.block_ne_zero ℓ _ (fun t' => rmsNorm_zero_dotProduct_self _ t' (ih t')) t

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
  -- `θ*` of Appendix D.6, `(D_0)` from the claim above, the batch of Proposition D.4
  obtain ⟨θ, hθ, hblocks⟩ := exists_regularZero_tanh_path (T := T) (dIn := dIn) (dOut := dOut)
    (hid := hid) hd hdIn hdOut hhid
  obtain ⟨n, X, hXE, hrank⟩ := exists_batch_jacobianRank_of_claimZero _ θ rfl
    (fun ℓ => analyticOnNhd_f_mlp analyticOnNhd_tanh ℓ) hθ hd
    (claimZero_of_tanh_path hθ hd hblocks 0)
  refine ⟨θ, n, X, fun i t hXt => hXE i t ?_, ?_, hrank⟩
  · -- a zero row of `x` gives a zero row of `x E`
    rw [Matrix.mul_apply_eq_vecMul, hXt, Matrix.zero_vecMul]
  · -- (R2): no row of a hidden state vanishes
    intro i j _ t
    exact hidden_row_ne_zero_tz hθ (X i) (hXE i) j t

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
  have : Nonempty d := Fintype.card_pos_iff.1 (by omega)
  obtain ⟨θ₀, n, X, hX, hmem, hrank⟩ :=
    exists_jacobianRank_tanh_rmsNorm_zero (T := T) (hid := hid) hd hdIn hdOut hhid
  have hhid2 : ∀ ℓ, 2 ≤ Fintype.card (hid ℓ) := fun ℓ => hd.trans (hhid ℓ)
  -- Lemma D.20: `O_X` is open, connected, of full measure, and `F_X` is analytic on it; so the
  -- rank on `X` is at least its rank at `θ*` at almost every parameter
  have h1 := ae_jacobianRank_ge_of_isPreconnected _ 0 μ X
    (isOpen_hiddenNonzero analyticOnNhd_tanh X (Fin.last L))
    (isPreconnected_hiddenNonzero analyticOnNhd_tanh tanh_eq_zero_iff_tz hd hhid2 X hX
      (Fin.last L))
    (measure_compl_hiddenNonzero analyticOnNhd_tanh tanh_eq_zero_iff_tz hd hhid2 X hX μ
      (Fin.last L))
    (analyticOnNhd_evalBatch_hiddenNonzero analyticOnNhd_tanh X) hmem
  -- the upper bound (13) where `E` and the writes have rank `d`
  have h2 := ae_funDim_add_le_skipless_rmsNorm_zero μ rfl hdIn hhid
  filter_upwards [h1, h2] with θ ha hb
  have hc := jacobianRank_le_funDim (S := 0) θ X
  generalize (L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2 + 1) = c at *
  generalize Module.finrank ℝ
    (Params (Arch.mlp (T := T) (d := d) Real.tanh (rmsNorm 0) hid) dIn dOut) = P at *
  omega

end Skips
