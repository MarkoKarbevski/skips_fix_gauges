import SkipsLean.Depth.SuffixZero
import SkipsLean.Network.Analytic

/-!
# The hidden states as functions of the weights, in the case (0)

Paper (dimension paper): Appendix D.6, proof of Lemma D.20 (The domain). "Let `ℓ ≥ 1` and `x ∈ X`.
On `O^{ℓ−1}`, `h_ℓ = w̃_ℓ W_write^ℓ` with `w̃_ℓ = σ(N(h_{ℓ−1}) W_read^ℓ)`, and `h_{ℓ−1}` does not
depend on the weights of block `ℓ`. […] `w̃_ℓ = 0` exactly where `N(h_{ℓ−1}) W_read^ℓ = 0`, a closed
submanifold of `O^{ℓ−1}` of codimension at least `d_model ≥ 2`, because the derivative with respect
to `W_read^ℓ` is onto. Where `w̃_ℓ ≠ 0`, the derivative of `h_ℓ` with respect to `W_write^ℓ` is onto
`ℝ^{1×d_model}`".

Stated here, for networks of MLP blocks under pre-RMSNorm with `ε = 0` and a real-analytic
activation `σ`, at an input `x` and a token `t` (a hidden state has the rows `T`; "nonzero" is "no
row vanishes"):

* a hidden state `h_j` depends only on `E` and on the blocks before it;
* `h_j` is real-analytic in the weights at a parameter at which no row of `h_0, …, h_{j−1}`
  vanishes, and so are what block `ℓ` reads and the output;
* at a parameter at which no row of `h_0, …, h_ℓ` vanishes (the paper's `h_0, …, h_{ℓ−1}`), the
  derivative in the weights of row `t` of `N(h_ℓ) W_read` is onto; and where this row is not zero
  and `σ` vanishes only at `0`, the derivative in the weights of row `t` of the next hidden state is
  onto.

Numbering: the block `ℓ : Fin L` is the paper's block `ℓ + 1`, between the hidden states
`ℓ.castSucc` and `ℓ.succ`.
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut] {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)] {σ : ℝ → ℝ}

/-- **"`h_{ℓ−1}` does not depend on the weights of block `ℓ`":** the hidden state `h_j` depends only
on `E` and on the reads and writes of the blocks before it. -/
theorem hidden_congr (A : Arch T d L) (S : Fin L → Matrix d d ℝ) (θ θ' : Params A dIn dOut)
    (x : Matrix T dIn ℝ) (j : Fin (L + 1)) (hE : θ'.E = θ.E)
    (hr : ∀ ℓ : Fin L, ℓ.castSucc < j → θ'.read ℓ = θ.read ℓ)
    (hw : ∀ ℓ : Fin L, ℓ.castSucc < j → θ'.write ℓ = θ.write ℓ) :
    hidden A S θ' x j = hidden A S θ x j := by
  sorry

/-- **The hidden states are real-analytic in the weights where the earlier ones do not vanish:**
for a real-analytic `σ`, if no row of `h_i`, `i < j`, vanishes at `θ`, then `θ' ↦ h_j` is
real-analytic at `θ`. -/
theorem analyticAt_hidden_rmsNorm_zero (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) (x : Matrix T dIn ℝ)
    (j : Fin (L + 1))
    (h : ∀ i : Fin (L + 1), i < j → ∀ t, hidden (Arch.mlp σ (rmsNorm 0) hid) 0 θ x i t ≠ 0) :
    AnalyticAt ℝ (fun θ' : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut =>
      hidden (Arch.mlp σ (rmsNorm 0) hid) 0 θ' x j) θ := by
  sorry

/-- What block `ℓ` reads, `N(h_ℓ) W_read`, is real-analytic in the weights at a parameter at which
no row of `h_0, …, h_ℓ` vanishes. -/
theorem analyticAt_preactivation_rmsNorm_zero (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) (x : Matrix T dIn ℝ)
    (ℓ : Fin L)
    (h : ∀ i : Fin (L + 1), i ≤ ℓ.castSucc →
      ∀ t, hidden (Arch.mlp σ (rmsNorm 0) hid) 0 θ x i t ≠ 0) :
    AnalyticAt ℝ (fun θ' : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut =>
      (rmsNorm 0 (hidden (Arch.mlp σ (rmsNorm 0) hid) 0 θ' x ℓ.castSucc) * θ'.read ℓ :
        Matrix T (hid ℓ) ℝ)) θ := by
  sorry

/-- **"the outputs `F_X` on the batch are real-analytic on `O_X`", one input:** the output at `x` is
real-analytic in the weights at a parameter at which no row of a hidden state of `x` vanishes. -/
theorem analyticAt_eval_rmsNorm_zero (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) (x : Matrix T dIn ℝ)
    (h : ∀ (i : Fin (L + 1)) (t : T), hidden (Arch.mlp σ (rmsNorm 0) hid) 0 θ x i t ≠ 0) :
    AnalyticAt ℝ (fun θ' : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut =>
      eval (Arch.mlp σ (rmsNorm 0) hid) 0 θ' x) θ := by
  sorry

/-- **"because the derivative with respect to `W_read^ℓ` is onto":** at a parameter at which no row
of `h_0, …, h_ℓ` vanishes, the derivative in the weights of row `t` of `N(h_ℓ) W_read` is onto. -/
theorem surjective_fderiv_preactivation (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) (x : Matrix T dIn ℝ)
    (ℓ : Fin L) (t : T)
    (h : ∀ i : Fin (L + 1), i ≤ ℓ.castSucc →
      ∀ t, hidden (Arch.mlp σ (rmsNorm 0) hid) 0 θ x i t ≠ 0) :
    Function.Surjective
      (fderiv ℝ (fun θ' : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut =>
        (rmsNorm 0 (hidden (Arch.mlp σ (rmsNorm 0) hid) 0 θ' x ℓ.castSucc) * θ'.read ℓ :
          Matrix T (hid ℓ) ℝ) t) θ) := by
  sorry

/-- **"Where `w̃_ℓ ≠ 0`, the derivative of `h_ℓ` with respect to `W_write^ℓ` is onto":** let `σ`
vanish only at `0`. At a parameter at which no row of `h_0, …, h_ℓ` vanishes and row `t` of
`N(h_ℓ) W_read` is not zero, the derivative in the weights of row `t` of `h_{ℓ+1}` is onto. -/
theorem surjective_fderiv_hidden_succ (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (hσ0 : ∀ z : ℝ, σ z = 0 → z = 0)
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) (x : Matrix T dIn ℝ)
    (ℓ : Fin L) (t : T)
    (h : ∀ i : Fin (L + 1), i ≤ ℓ.castSucc →
      ∀ t, hidden (Arch.mlp σ (rmsNorm 0) hid) 0 θ x i t ≠ 0)
    (hg : (rmsNorm 0 (hidden (Arch.mlp σ (rmsNorm 0) hid) 0 θ x ℓ.castSucc) * θ.read ℓ :
      Matrix T (hid ℓ) ℝ) t ≠ 0) :
    Function.Surjective
      (fderiv ℝ (fun θ' : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut =>
        hidden (Arch.mlp σ (rmsNorm 0) hid) 0 θ' x ℓ.succ t) θ) := by
  sorry

end Skips
