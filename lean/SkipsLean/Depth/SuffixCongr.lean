import SkipsLean.Depth.ComplexBlockIdentity

/-!
# The network after a hidden state depends only on the later blocks; `𝓛` at complex arguments

Paper (dimension paper): Appendix D.3, "The network after the block does not depend on the
weights of the block" (the derivative `𝐃_θ𝓑_{>k}(h) η` is the paper's `𝐃_θ𝓑_{>k}(h) η'`, with `η'`
the components of `η` at the blocks after `h_k` and at `D`), and Appendix D.6 (the case `ε = 0`),
"The identity on the path": "`𝓛` is holomorphic in `w̃`, affine in `w̃'` and polynomial in `n`",
together with "`𝓑_{>k}(λh) = 𝓑_{>k}(h)` for `λ > 0`" (Lemma D.14), which the proof of Lemma D.19
uses as "a derivative of order `i` of `𝓑` is homogeneous of degree `−i`".

Stated here, for networks with any stream matrices `S` and any blocks (first two statements), and
for MLP blocks with an activation extended by `σC : ℂ → ℂ` under pre-RMSNorm with `ε = 0` (the
others):

* `𝓑_{>j}` and its complex version do not change when the weights of the blocks before `h_j` and
  `E` change; so the derivative in the weights vanishes along a direction that is zero at the
  blocks after `h_j` and at `D`.
* `𝓛(w̃, w̃'; ż)` (`blockLHSC`) is holomorphic in `(w̃, w̃', ż)` where the rows of `w̃V` lie in a
  cone on which `𝓑_{>k+1}` is holomorphic.
* `𝓛(c w̃, w̃'; c ż) = 𝓛(w̃, w̃'; ż)` for `c > 0`, on such a cone `C_κ` with `κ ≤ 1`.

Numbering: block `ℓ : Fin L` lies after the hidden state `j : Fin (L + 1)` when `j ≤ ℓ.castSucc`.
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]

/-- **`𝓑_{>j}` depends only on the blocks after `h_j` and on `D`** (any blocks, any stream
matrices). -/
theorem suffix_congr (A : Arch T d L) (S : Fin L → Matrix d d ℝ) (θ θ' : Params A dIn dOut)
    (j : Fin (L + 1)) (h : Matrix T d ℝ)
    (hr : ∀ ℓ : Fin L, j ≤ ℓ.castSucc → θ'.read ℓ = θ.read ℓ)
    (hw : ∀ ℓ : Fin L, j ≤ ℓ.castSucc → θ'.write ℓ = θ.write ℓ) (hD : θ'.D = θ.D) :
    suffix A S θ' j h = suffix A S θ j h := by
  induction j using Fin.reverseInduction generalizing h with
  | last =>
    -- `𝓑_{>L}(h) = χ(h) D`, and the two `D` agree
    rw [suffix_last, suffix_last, hD]
  | cast ℓ ih =>
    -- block `ℓ` is after `h_ℓ`: its read and write agree; then the induction hypothesis
    rw [suffix_castSucc, suffix_castSucc, hr ℓ le_rfl, hw ℓ le_rfl]
    exact ih _ (fun ℓ' hℓ' => hr ℓ' ((Fin.castSucc_le_succ ℓ).trans hℓ'))
      (fun ℓ' hℓ' => hw ℓ' ((Fin.castSucc_le_succ ℓ).trans hℓ'))

/-- **The derivative of `𝓑_{>j}` in the weights vanishes along a direction that is zero at the
blocks after `h_j` and at `D`** (any blocks, any stream matrices; no differentiability is asked:
where `𝓑_{>j}` is not differentiable in the weights, Lean's derivative is `0`). -/
theorem fderiv_param_suffix_eq_zero (A : Arch T d L) (S : Fin L → Matrix d d ℝ)
    (θ η : Params A dIn dOut) (j : Fin (L + 1)) (h : Matrix T d ℝ)
    (hr : ∀ ℓ : Fin L, j ≤ ℓ.castSucc → η.read ℓ = 0)
    (hw : ∀ ℓ : Fin L, j ≤ ℓ.castSucc → η.write ℓ = 0) (hD : η.D = 0) :
    fderiv ℝ (fun θ' : Params A dIn dOut => suffix A S θ' j h) θ η = 0 := by
  by_cases hf : DifferentiableAt ℝ (fun θ' : Params A dIn dOut => suffix A S θ' j h) θ
  · -- the derivative along `η` is the derivative of `τ ↦ 𝓑_{>j}(h)` at `θ + τ η`, a constant
    have hγ : HasDerivAt (fun τ : ℝ => θ + τ • η) η 0 :=
      (((hasDerivAt_id' (0 : ℝ)).smul_const η).const_add θ).congr_deriv (one_smul ℝ η)
    have h1 := hf.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hγ (by rw [zero_smul, add_zero])
    have hc : (fun τ : ℝ => suffix A S (θ + τ • η) j h) = fun _ => suffix A S θ j h := by
      funext τ
      refine suffix_congr A S θ (θ + τ • η) j h (fun ℓ hℓ => ?_) (fun ℓ hℓ => ?_) ?_
      · rw [Params.add_read, Params.smul_read, hr ℓ hℓ, smul_zero, add_zero]
      · rw [Params.add_write, Params.smul_write, hw ℓ hℓ, smul_zero, add_zero]
      · rw [Params.add_D, Params.smul_D, hD, smul_zero, add_zero]
    have h2 : HasDerivAt (fun τ : ℝ => suffix A S (θ + τ • η) j h) 0 0 := by
      rw [hc]
      exact hasDerivAt_const _ _
    exact h1.unique h2
  · -- not differentiable: Lean's derivative is `0`
    rw [fderiv_zero_of_not_differentiableAt hf]
    rfl

variable {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)] {σ : ℝ → ℝ} {σC : ℂ → ℂ}

/-- **`𝓑_{>j}` at complex weights depends only on the blocks after `h_j` and on `D`.** -/
theorem suffixC_congr (σC : ℂ → ℂ) (ω ω' : CWeights d dOut hid) (j : Fin (L + 1))
    (h : Matrix T d ℂ)
    (hr : ∀ ℓ : Fin L, j ≤ ℓ.castSucc → ω'.1 ℓ = ω.1 ℓ)
    (hw : ∀ ℓ : Fin L, j ≤ ℓ.castSucc → ω'.2.1 ℓ = ω.2.1 ℓ) (hD : ω'.2.2 = ω.2.2) :
    suffixC σC ω' j h = suffixC σC ω j h := by
  induction j using Fin.reverseInduction generalizing h with
  | last =>
    -- `𝓑_{>L}(h) = N(h) D`, and the two `D` agree
    simp only [suffixC, Fin.reverseInduction_last]
    rw [hD]
  | cast ℓ ih =>
    -- block `ℓ` is after `h_ℓ`: its read and write agree; then the induction hypothesis
    simp only [suffixC, Fin.reverseInduction_castSucc]
    rw [hr ℓ le_rfl, hw ℓ le_rfl]
    exact ih _ (fun ℓ' hℓ' => hr ℓ' ((Fin.castSucc_le_succ ℓ).trans hℓ'))
      (fun ℓ' hℓ' => hw ℓ' ((Fin.castSucc_le_succ ℓ).trans hℓ'))

/-- **The complex derivative of `𝓑_{>j}` in the weights vanishes along a direction that is zero at
the blocks after `h_j` and at `D`.** -/
theorem fderiv_weights_suffixC_eq_zero (σC : ℂ → ℂ) (ω ζ : CWeights d dOut hid)
    (j : Fin (L + 1)) (h : Matrix T d ℂ)
    (hr : ∀ ℓ : Fin L, j ≤ ℓ.castSucc → ζ.1 ℓ = 0)
    (hw : ∀ ℓ : Fin L, j ≤ ℓ.castSucc → ζ.2.1 ℓ = 0) (hD : ζ.2.2 = 0) :
    fderiv ℂ (fun ω' : CWeights d dOut hid => suffixC σC ω' j h) ω ζ = 0 := by
  by_cases hf : DifferentiableAt ℂ (fun ω' : CWeights d dOut hid => suffixC σC ω' j h) ω
  · -- the derivative along `ζ` is the derivative of `τ ↦ 𝓑_{>j}(h)` at `ω + τ ζ`, a constant
    have hγ : HasDerivAt (fun τ : ℂ => ω + τ • ζ) ζ 0 :=
      (((hasDerivAt_id' (0 : ℂ)).smul_const ζ).const_add ω).congr_deriv (one_smul ℂ ζ)
    have h1 := hf.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℂ) hγ (by rw [zero_smul, add_zero])
    have hc : (fun τ : ℂ => suffixC σC (ω + τ • ζ) j h) = fun _ => suffixC σC ω j h := by
      funext τ
      refine suffixC_congr σC ω (ω + τ • ζ) j h (fun ℓ hℓ => ?_) (fun ℓ hℓ => ?_) ?_
      · show ω.1 ℓ + τ • ζ.1 ℓ = ω.1 ℓ
        rw [hr ℓ hℓ, smul_zero, add_zero]
      · show ω.2.1 ℓ + τ • ζ.2.1 ℓ = ω.2.1 ℓ
        rw [hw ℓ hℓ, smul_zero, add_zero]
      · show ω.2.2 + τ • ζ.2.2 = ω.2.2
        rw [hD, smul_zero, add_zero]
    have h2 : HasDerivAt (fun τ : ℂ => suffixC σC (ω + τ • ζ) j h) 0 0 := by
      rw [hc]
      exact hasDerivAt_const _ _
    exact h1.unique h2
  · -- not differentiable: Lean's derivative is `0`
    rw [fderiv_zero_of_not_differentiableAt hf]
    rfl

/-- **"`𝓛` is holomorphic in `w̃`, affine in `w̃'`"** (and in `ż`): if `𝓑_{>k+1}` is holomorphic on
the cone `C_κ` and the rows of `w̃₀V` lie in `C_κ`, then `(w̃, w̃', ż) ↦ 𝓛(w̃, w̃'; ż)` is
holomorphic at `(w̃₀, w̃'₀, ż₀)`. -/
theorem analyticAt_blockLHSC
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) (k : Fin L) {κ : ℝ}
    (hhol : HolomorphicOnCone σC θ k.succ κ)
    (η : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
    (w₀ w₀' zd₀ : Matrix T (hid k) ℂ) (hw₀ : ∀ t, (w₀ * θ.toC.2.1 k) t ∈ complexCone κ) :
    AnalyticAt ℂ
      (fun p : Matrix T (hid k) ℂ × Matrix T (hid k) ℂ × Matrix T (hid k) ℂ =>
        blockLHSC σC θ k η p.1 p.2.1 p.2.2) (w₀, w₀', zd₀) := by
  sorry

/-- **`𝓛(c w̃, w̃'; c ż) = 𝓛(w̃, w̃'; ż)` for `c > 0`:** if `𝓑_{>k+1}` is holomorphic on the cone
`C_κ`, `0 < κ ≤ 1`, and the rows of `w̃V` lie in `C_κ`. (`𝐃𝓑(ch)(cv) = 𝐃𝓑(h)v` and
`𝐃_θ𝓑(ch) = 𝐃_θ𝓑(h)`, the derivatives of `𝓑(ch) = 𝓑(h)`.) -/
theorem blockLHSC_smul
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) (k : Fin L) {κ : ℝ}
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hhol : HolomorphicOnCone σC θ k.succ κ)
    (η : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
    (w w' zd : Matrix T (hid k) ℂ) (hw : ∀ t, (w * θ.toC.2.1 k) t ∈ complexCone κ) {c : ℝ}
    (hc : 0 < c) :
    blockLHSC σC θ k η ((c : ℂ) • w) w' ((c : ℂ) • zd) = blockLHSC σC θ k η w w' zd := by
  sorry

end Skips
