import SkipsLean.Depth.SuffixZeroDeriv
import SkipsLean.Network.Analytic

/-!
# The network after a hidden state acts on every token alone

Paper (dimension paper): Appendix D takes inputs of one token, since an MLP block acts on each
token separately. Here a hidden state has the rows `T`. For MLP blocks under pre-RMSNorm, row `t` of
`𝓑_{>k}(h)` depends only on row `t` of `h`, and in the case (0) so do the rows of the derivatives
`𝐃𝓑_{>k}(h) v` and `𝐃_θ𝓑_{>k}(h) η`.

These statements carry an identity that is known at the hidden states whose rows are all equal
(the paper's one token) to every hidden state without a zero row. They are used in the step for
`tanh` on the path (Lemma D.18), where the path of Appendix D.6 is taken with the same row at every
token.
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut] {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)] {σ : ℝ → ℝ} {ε : ℝ}

/-- Helper: row `t` of `𝓑_{>k}(h)` depends only on row `t` of `h` (MLP blocks under pre-RMSNorm). -/
private theorem suffix_row_congr_rows
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut) (k : Fin (L + 1))
    (h h' : Matrix T d ℝ) (t : T) (hht : h t = h' t) :
    suffix (Arch.mlp σ (rmsNorm ε) hid) 0 θ k h t
      = suffix (Arch.mlp σ (rmsNorm ε) hid) 0 θ k h' t := by
  induction k using Fin.reverseInduction generalizing h h' with
  | last =>
    -- `𝓑_{>L}(h)_t = N(h)_t D = rmsRow(h_t) D`
    rw [suffix_last, suffix_last, Matrix.mul_apply_eq_vecMul, Matrix.mul_apply_eq_vecMul]
    show rmsRow ε (h t) ᵥ* θ.D = rmsRow ε (h' t) ᵥ* θ.D
    rw [hht]
  | cast ℓ ih =>
    -- row `t` of `h S + σ(N(h) W_read) W_write` (`S = 0`) depends only on `h_t`
    rw [suffix_castSucc, suffix_castSucc]
    apply ih
    funext j
    simp only [Pi.zero_apply, Matrix.mul_zero, zero_add, Matrix.mul_apply, Matrix.map_apply,
      rmsNorm, Matrix.of_apply]
    rw [hht]

/-- **An MLP block acts on each token separately:** for MLP blocks under pre-RMSNorm (any `ε`), row
`t` of `𝓑_{>k}(h)` is row `t` of `𝓑_{>k}` at the hidden state whose rows all equal row `t` of
`h`. -/
theorem suffix_mlp_rmsNorm_row
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut) (k : Fin (L + 1))
    (h : Matrix T d ℝ) (t : T) :
    suffix (Arch.mlp σ (rmsNorm ε) hid) 0 θ k h t
      = suffix (Arch.mlp σ (rmsNorm ε) hid) 0 θ k (Matrix.of fun _ => h t) t := by
  -- the two hidden states have the same row `t`
  exact suffix_row_congr_rows θ k h _ t rfl

/-- Helper: row `t` of a matrix, as a continuous linear map. -/
private noncomputable def rowCLM_rows {n : Type*} [Fintype n] (t : T) :
    Matrix T n ℝ →L[ℝ] (n → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => M t
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

/-- Helper: the matrix whose rows all equal row `t`, as a continuous linear map. -/
private noncomputable def constRowCLM_rows (t : T) : Matrix T d ℝ →L[ℝ] Matrix T d ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => Matrix.of fun _ => M t
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

/-- **The derivative in `h`, token by token, case (0):** for real-analytic MLP blocks and regular
`θ`, at `h` without a zero row, row `t` of `𝐃𝓑_{>k}(h) v` is row `t` of the same derivative at the
hidden state whose rows all equal row `t` of `h`, along the direction whose rows all equal row `t`
of `v`. -/
theorem fderiv_suffix_zero_row (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
    (hθ : RegularZero (Arch.mlp σ (rmsNorm 0) hid) θ) (k : Fin (L + 1))
    (h v : Matrix T d ℝ) (hh : ∀ t, h t ≠ 0) (t : T) :
    fderiv ℝ (fun h' : Matrix T d ℝ => suffix (Arch.mlp σ (rmsNorm 0) hid) 0 θ k h') h v t
      = fderiv ℝ (fun h' : Matrix T d ℝ => suffix (Arch.mlp σ (rmsNorm 0) hid) 0 θ k h')
          (Matrix.of fun _ => h t) (Matrix.of fun _ => v t) t := by
  have hf : ∀ ℓ, AnalyticOnNhd ℝ ((Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid).f ℓ) Set.univ :=
    fun ℓ => analyticOnNhd_f_mlp hσa ℓ
  set P := rowCLM_rows (n := dOut) t
  set R := constRowCLM_rows (d := d) t
  set Φ := fun h' : Matrix T d ℝ => suffix (Arch.mlp σ (rmsNorm 0) hid) 0 θ k h'
  -- `Φ = 𝓑_{>k}` is differentiable at every hidden state without a zero row
  have hd : ∀ h₀ : Matrix T d ℝ, (∀ s, h₀ s ≠ 0) → HasFDerivAt Φ (fderiv ℝ Φ h₀) h₀ := by
    intro h₀ hh₀
    have hA := (analyticAt_suffix_prod_zero (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) θ rfl
      hf hθ k h₀ hh₀).differentiableAt
    have hc := hA.hasFDerivAt.comp h₀ (hasFDerivAt_prodMk_right (𝕜 := ℝ) θ h₀)
    exact hc.differentiableAt.hasFDerivAt
  -- row `t` of `Φ` factors through `R` (the first theorem)
  have hfac : (⇑P ∘ Φ) ∘ ⇑R = ⇑P ∘ Φ := by
    funext h'
    exact (suffix_mlp_rmsNorm_row θ k h' t).symm
  -- the chain rule at `h` and at `R h`, and uniqueness of the derivative
  have h1 := P.hasFDerivAt.comp h (hd h hh)
  have h2 := (P.hasFDerivAt.comp (R h) (hd (R h) fun _ => hh t)).comp h R.hasFDerivAt
  rw [hfac] at h2
  have e := DFunLike.congr_fun (h1.unique h2) v
  exact e

/-- **The derivative in the weights, token by token, case (0):** under the same hypotheses, row
`t` of `𝐃_θ𝓑_{>k}(h) η` is row `t` of the same derivative at the hidden state whose rows all equal
row `t` of `h`. -/
theorem fderiv_param_suffix_zero_row (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
    (hθ : RegularZero (Arch.mlp σ (rmsNorm 0) hid) θ) (k : Fin (L + 1))
    (h : Matrix T d ℝ) (hh : ∀ t, h t ≠ 0)
    (η : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) (t : T) :
    fderiv ℝ (fun θ' : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut =>
        suffix (Arch.mlp σ (rmsNorm 0) hid) 0 θ' k h) θ η t
      = fderiv ℝ (fun θ' : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut =>
          suffix (Arch.mlp σ (rmsNorm 0) hid) 0 θ' k (Matrix.of fun _ => h t)) θ η t := by
  have hf : ∀ ℓ, AnalyticOnNhd ℝ ((Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid).f ℓ) Set.univ :=
    fun ℓ => analyticOnNhd_f_mlp hσa ℓ
  set P := rowCLM_rows (n := dOut) t
  -- `θ' ↦ 𝓑_{>k}(h₀)` at the weights `θ'` is differentiable at `θ` for `h₀` without a zero row
  have hd : ∀ h₀ : Matrix T d ℝ, (∀ s, h₀ s ≠ 0) →
      HasFDerivAt (fun θ' : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut =>
          suffix (Arch.mlp σ (rmsNorm 0) hid) 0 θ' k h₀)
        (fderiv ℝ (fun θ' : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut =>
          suffix (Arch.mlp σ (rmsNorm 0) hid) 0 θ' k h₀) θ) θ := by
    intro h₀ hh₀
    have hA := (analyticAt_suffix_prod_zero (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) θ rfl
      hf hθ k h₀ hh₀).differentiableAt
    have hc := hA.hasFDerivAt.comp θ (hasFDerivAt_prodMk_left (𝕜 := ℝ) θ h₀)
    exact hc.differentiableAt.hasFDerivAt
  -- row `t` of the two maps agree at every `θ'` (the first theorem)
  have hfac : (⇑P ∘ fun θ' : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut =>
        suffix (Arch.mlp σ (rmsNorm 0) hid) 0 θ' k (Matrix.of fun _ => h t))
      = ⇑P ∘ fun θ' : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut =>
        suffix (Arch.mlp σ (rmsNorm 0) hid) 0 θ' k h := by
    funext θ'
    exact (suffix_mlp_rmsNorm_row θ' k h t).symm
  -- row extraction commutes with the derivative on both sides; uniqueness of the derivative
  have h1 := P.hasFDerivAt.comp θ (hd h hh)
  have h2 := P.hasFDerivAt.comp θ (hd (Matrix.of fun _ => h t) fun _ => hh t)
  rw [hfac] at h2
  have e := DFunLike.congr_fun (h1.unique h2) η
  exact e

end Skips
