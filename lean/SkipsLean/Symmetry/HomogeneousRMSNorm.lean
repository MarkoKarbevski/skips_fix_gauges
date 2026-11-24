import SkipsLean.Symmetry.AtOneState
import SkipsLean.Dimension.ExpOrbit
import SkipsLean.Network.Blocks

/-!
# Positively homogeneous blocks under pre-RMSNorm: more changes of basis

Paper (skips paper): Appendix A.2, Lemma A.3.

"For positively homogeneous blocks and `ε = 0`, more changes of basis preserve the function: every
invertible one before the last hidden state. The next lemma shows this and measures how `ε > 0`
breaks it; Theorem A.17, Theorem B.1 (iv) and the checks of Appendix E use it.

Lemma A.3 (Homogeneous blocks under RMSNorm). Let a skipless network with pre-RMSNorm,
`h_ℓ = B_ℓ(N_ε(h_{ℓ−1}))` for `ℓ = 1, …, L` and `y = N_ε(h_L) D`, have blocks that are positively
homogeneous of degree `k`, and let `r_i² = ‖h_i‖²/d_model`. Apply the change of basis
`G ∈ GL(d_model)` at `h_ℓ` with `ℓ < L`, or the scaling `G = cI` at `h_L` with its read `D`
unchanged. At every input whose hidden states are nonzero, the output becomes `Λy` with a scalar
`Λ > 0`, and (i) `Λ = 1` if `ε = 0` or `G` is orthogonal; (ii) for `G = e^{tS}` with `S`
symmetric and `ℓ < L`,
`d/dt log Λ |_{t=0} = − k^{L−ℓ} (h_ℓ S h_ℓ^⊤)/(d_model (r_ℓ² + ε)) ∏_{i=ℓ+1}^{L} ε/(r_i² + ε)`,
and for the scaling `c = e^t` at `h_L` it is `ε/(r_L² + ε)`."

Stated here, for a skipless network (stream matrices `0`) with `χ = rmsNorm ε` whose fixed maps
are positively homogeneous of degree `k` row by row (`RowHomogeneous`: scaling row `t` of the
input of `f_ℓ` by `c_t > 0` scales row `t` of its output by `c_t^k`; MLP blocks with a positively
homogeneous activation and gated blocks with a positively homogeneous gate are of this kind):

* the scalar `Λ`, one per token, for `ε ≥ 0`: for the change of basis `G` at `h_ℓ`, `ℓ < L`
  (`θ.cobAt ℓ.castSucc G`), and for the scaling at `h_L` with `D` unchanged;
* (i) for `ε = 0`: both leave the function unchanged. (For an orthogonal `G` this is
  `eval_cobAt_rmsNorm`, `Symmetry/AtOneState.lean`, for any blocks.)
* (ii) for `ε > 0`, as the derivative of the output at `t = 0`: since `Λ = 1` at `t = 0`, the
  derivative of `t ↦ Λ(t) y` is `(d/dt log Λ) y`.

Lean has no hypothesis on the hidden states: with Lean's total `N_0` (`N_0(0) = 0`) a zero row
stays a zero row, and for `ε > 0` every factor is positive. In (ii) Lean takes any matrix `S`:
only `h_ℓ S h_ℓ^⊤` enters, which vanishes for an antisymmetric `S`. The formula was checked
numerically (`claude/homogeneous_rmsnorm_check_2026-11-24.py`).
-/

namespace Skips

open Matrix

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]

/-- The fixed maps of the blocks are positively homogeneous of degree `k`, row by row: scaling
row `t` of the input by `c t > 0` scales row `t` of the output by `(c t) ^ k`. -/
def RowHomogeneous (A : Arch T d L) (k : ℕ) : Prop :=
  ∀ (ℓ : Fin L) (c : T → ℝ), (∀ t, 0 < c t) → ∀ M : Matrix T (A.r ℓ) ℝ,
    A.f ℓ (Matrix.of fun t i => c t * M t i) = Matrix.of fun t i => c t ^ k * A.f ℓ M t i

/-- `r² = ‖v‖² / d` for a row `v`. -/
noncomputable def meanSq (v : d → ℝ) : ℝ := (v ⬝ᵥ v) / (Fintype.card d : ℝ)

/-- MLP blocks with an activation that is positively homogeneous of degree `k` (ReLU: `k = 1`,
ReLU²: `k = 2`) are positively homogeneous of degree `k`, row by row. -/
theorem rowHomogeneous_mlp {σ : ℝ → ℝ} {k : ℕ}
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (χ : Matrix T d ℝ → Matrix T d ℝ) (hid : Fin L → Type) [∀ ℓ, Fintype (hid ℓ)] :
    RowHomogeneous (Arch.mlp (T := T) (d := d) σ χ hid) k := by
  sorry

/-- Gated blocks with a gate activation that is positively homogeneous of degree `k` (ReGLU:
`k = 1`) are positively homogeneous of degree `k + 1`, row by row. -/
theorem rowHomogeneous_gated {σ : ℝ → ℝ} {k : ℕ}
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (χ : Matrix T d ℝ → Matrix T d ℝ) (hid : Fin L → Type) [∀ ℓ, Fintype (hid ℓ)] :
    RowHomogeneous (Arch.gated (T := T) (d := d) σ χ hid) (k + 1) := by
  sorry

variable {A : Arch T d L}

/-- **Lemma A.3, the scalar `Λ`, for a change of basis before the last hidden state:** for
`ε ≥ 0` and blocks that are positively homogeneous of degree `k`, the change of basis `G` at
`h_ℓ`, `ℓ < L`, multiplies the output at every token by a positive number. -/
theorem exists_pos_smul_eval_cobAt_of_rowHomogeneous {ε : ℝ} (hε : 0 ≤ ε)
    (hA : A.χ = rmsNorm ε) {k : ℕ} (hf : RowHomogeneous A k) (θ : Params A dIn dOut)
    (ℓ : Fin L) (G : GL d ℝ) (x : Matrix T dIn ℝ) :
    ∃ Λ : T → ℝ, (∀ t, 0 < Λ t) ∧
      ∀ t, eval A 0 (θ.cobAt ℓ.castSucc G) x t = Λ t • eval A 0 θ x t := by
  sorry

/-- **Lemma A.3, the scalar `Λ`, for the scaling at the last hidden state:** for `ε ≥ 0`, the
scaling `G = cI`, `c > 0`, at `h_L` with the readout `D` unchanged multiplies the output at every
token by a positive number. -/
theorem exists_pos_smul_eval_scale_last {ε : ℝ} (hε : 0 ≤ ε) (hA : A.χ = rmsNorm ε)
    (θ : Params A dIn dOut) {c : ℝ} (hc : 0 < c) (G : GL d ℝ)
    (hG : (G : Matrix d d ℝ) = c • (1 : Matrix d d ℝ)) (x : Matrix T dIn ℝ) :
    ∃ Λ : T → ℝ, (∀ t, 0 < Λ t) ∧
      ∀ t, eval A 0 { θ.cobAt (Fin.last L) G with D := θ.D } x t = Λ t • eval A 0 θ x t := by
  sorry

/-- **Lemma A.3 (i) for `ε = 0`, a change of basis before the last hidden state:** for blocks
that are positively homogeneous of degree `k` under pre-RMSNorm with `ε = 0`, every invertible
change of basis at `h_ℓ`, `ℓ < L`, preserves the function. -/
theorem eval_cobAt_rmsNorm_zero_of_rowHomogeneous (hA : A.χ = rmsNorm 0) {k : ℕ}
    (hf : RowHomogeneous A k) (θ : Params A dIn dOut) (ℓ : Fin L) (G : GL d ℝ)
    (x : Matrix T dIn ℝ) :
    eval A 0 (θ.cobAt ℓ.castSucc G) x = eval A 0 θ x := by
  sorry

/-- **Lemma A.3 (i) for `ε = 0`, the scaling at the last hidden state:** under pre-RMSNorm with
`ε = 0`, the scaling `G = cI`, `c > 0`, at `h_L` with the readout `D` unchanged preserves the
function. -/
theorem eval_scale_last_rmsNorm_zero (hA : A.χ = rmsNorm 0) (θ : Params A dIn dOut) {c : ℝ}
    (hc : 0 < c) (G : GL d ℝ) (hG : (G : Matrix d d ℝ) = c • (1 : Matrix d d ℝ))
    (x : Matrix T dIn ℝ) :
    eval A 0 { θ.cobAt (Fin.last L) G with D := θ.D } x = eval A 0 θ x := by
  sorry

/-- **Lemma A.3 (ii), a change of basis before the last hidden state:** for `ε > 0`, blocks that
are positively homogeneous of degree `k` and `G = e^{τ S}` at `h_ℓ`, `ℓ < L`, the derivative of
the output at token `t` at `τ = 0` is the output times
`− k^{L−ℓ} (h_ℓ S h_ℓ^⊤)/(d (r_ℓ² + ε)) ∏_{i > ℓ} ε/(r_i² + ε)`. -/
theorem hasDerivAt_eval_cobAt_exp_of_rowHomogeneous {ε : ℝ} (hε : 0 < ε)
    (hA : A.χ = rmsNorm ε) {k : ℕ} (hf : RowHomogeneous A k) (θ : Params A dIn dOut)
    (ℓ : Fin L) (S : Matrix d d ℝ) (x : Matrix T dIn ℝ) (t : T) :
    HasDerivAt (fun τ : ℝ => eval A 0 (θ.cobAt ℓ.castSucc (expGL (τ • S))) x t)
      ((-((k : ℝ) ^ (L - (ℓ : ℕ)))
          * ((hidden A 0 θ x ℓ.castSucc t ⬝ᵥ (S *ᵥ hidden A 0 θ x ℓ.castSucc t))
            / ((Fintype.card d : ℝ) * (meanSq (hidden A 0 θ x ℓ.castSucc t) + ε)))
          * ∏ i ∈ Finset.univ.filter (fun i : Fin (L + 1) => ℓ.castSucc < i),
              ε / (meanSq (hidden A 0 θ x i t) + ε))
        • eval A 0 θ x t) 0 := by
  sorry

/-- **Lemma A.3 (ii), the scaling at the last hidden state:** for `ε > 0` and the scaling
`c = e^τ` at `h_L` with the readout `D` unchanged, the derivative of the output at token `t` at
`τ = 0` is the output times `ε/(r_L² + ε)`. -/
theorem hasDerivAt_eval_scale_last_exp {ε : ℝ} (hε : 0 < ε) (hA : A.χ = rmsNorm ε)
    (θ : Params A dIn dOut) (x : Matrix T dIn ℝ) (t : T) :
    HasDerivAt
      (fun τ : ℝ => eval A 0
        { θ.cobAt (Fin.last L) (expGL (τ • (1 : Matrix d d ℝ))) with D := θ.D } x t)
      ((ε / (meanSq (hidden A 0 θ x (Fin.last L) t) + ε)) • eval A 0 θ x t) 0 := by
  sorry

end Skips
