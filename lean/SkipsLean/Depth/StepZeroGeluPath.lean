import SkipsLean.Depth.GeluPathSeparation
import SkipsLean.Depth.SuffixCongr
import SkipsLean.Depth.CondP

/-!
# The step for GELU on the path: what one pair `ξ, ξ'` gives

Paper (dimension paper): Appendix D.6 (the case `ε = 0`), proof of Lemma D.19 (the step for GELU
on the path), its parts "The path", "The expansion", "Step 1" and the analytic part of "Step 2" and
"Step 4", for one pair of rows.

"The path. Fix `ξ ∈ P` and a unit row `ξ'` orthogonal to `ξ`, let `n(t)` be the path (41), and
`z_j(t) = n(t) c_j`, `r_j = (ξc_j)² − (ξ'c_j)² > 0`, `δ_j(t) = z_j − σ(z_j)`,
`δ'_j(t) = 1 − σ'(z_j)`. […] The real and the imaginary part of `n(t) W V` are
`√d ((t + t⁻¹)/2) ξ W V` and `√d ((t − t⁻¹)/2) ξ' W V`. By (P2), the second is shorter than `κ/2`
times the first, and by (45) `‖δ(t) V‖ ≤ ∑_j |δ_j| ‖a_j‖` is at most `κ/8` times the norm of the
first. Let `ϱ = κ √d ‖ξ W V‖ / (16 ∑_j ‖a_j‖)`. For a row `δ ∈ ℂ^{1×q}`,

  `|δ_j| ≤ ϱ t` for all `j`, or `δ = δ(t)`  ⟹  `(z(t) − δ) V = n(t) W V − δ V ∈ C_κ`,   (46)

[…]. As `σ(z) = z − δ(t)` and `σ'(z) = 1 − δ'(t)` on the path, Lemma D.15 applies:
`𝓛(z(t) − δ(t), 1 − δ'(t); n(t)) = 0` for all `t ≥ 1` (47)."

"Step 1: […] `𝓛_0(t) = 0` for large `t`, and then for all `t ≥ 1`, because it is holomorphic near
`[1, ∞)`. At `t = 1`, where `n(t)` is the row `n = √d ξ`, this reads […]
`0 = 𝓛(nW, 1; n)`." "Step 2: […] `𝓛'_j(t) = 0` and `𝓛_j(t) = 0` for large `t`, hence for all
`t ≥ 1` (50). By (21), with `ż_j` the entry `j` of `ż`, `𝓛'_j(t) = ż_j(n(t)) 𝐃𝓑(n(t) W V) a_j`."
"Step 4: […] So in the expansion (48) of `𝓛°` every term has a factor `δ_l(t)` or `δ'_l(t)` of a
unit `l` other than `j_1, …, j_{i−1}`. […] we get (50) as in Step 2."

**Stated here,** for one orthonormal pair `ξ, ξ'` with the three inequalities of (P2)
(`PathP2`, `Depth/CondP.lean`), a regular `θ`, a cone `C_κ`, `0 < κ ≤ 1`, on which `𝓑_{>k+1}` is
holomorphic, and a pair `Z, η` with the identity (16) before block `k`; the path has the same row
at every token, `n = √d ξ` is its row at `t = 1`, and `ż(n)` is (20):

* `gelu_path_step_zero` (Step 1): `𝓛(n(t)W, 1; n(t)) = 0` for all `t ≥ 1`, at complex arguments;
  `gelu_path_step_zero_real` is its case `t = 1` with the real `𝓛` (`blockLHS`).
* `gelu_path_step_unit` (Steps 2 and 4, (50) at `t = 1`): let `A` be a set of hidden units such
  that `𝓛(z(t) − δ, 1 − δ'; n(t)) = 0` for all `t ≥ 1` and all complex rows `δ, δ'` whose entries
  outside `A` vanish (for `A = ∅` this is Step 1; in Step 4, `A = {j_1, …, j_{i−1}}`), and let the
  unit `j ∉ A` have a smaller rate `r_j` than every other unit outside `A`. Then `𝓛_j(1) = 0`,
  stated as: the derivative at `τ = 0` of `τ ↦ 𝓛(nW − τ e_j, 1; n)` vanishes; and `𝓛'_j(1) = 0`,
  stated as `𝐃𝓑(n W V)(ż_j(n) a_j) = 0`.

The proof goes through the map `Ψ` of `Depth/GeluPathSeparation.lean`: with `s = 1/t`,
`m(s) = (1 + s²) ξ + i (1 − s²) ξ'` and `λ = √d t/2`, so that `n(t) = λ m(s)`, the homogeneity of
`𝓛` (`blockLHSC_smul`) gives `𝓛(λw, w'; ż(λm)) = t² Ψ(s, (x, y))` for `w = m(s)W − x`,
`w' = 1 − y`, with `Ψ = s² 𝓛(w, w'; m(ZW + η_W)) − (1/4) ⟨mZ, m⟩ 𝐃𝓑(wV)((w' ⊙ mW)V)`.
Numbering as in `Depth/StepTanh.lean`: the block is `k : Fin L`, the paper's block `k + 1`.
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut] {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]

/-- **Lemma D.19, Step 1, on the path:** `𝓛(n(t)W, 1; n(t)) = 0` for all `t ≥ 1` ("`𝓛_0(t) = 0`
for large `t`, and then for all `t ≥ 1`"). -/
theorem gelu_path_step_zero [Nonempty T]
    (θ : Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm 0) hid) dIn dOut)
    (hθ : RegularZero (Arch.mlp gelu (rmsNorm 0) hid) θ) (k : Fin L)
    {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hhol : HolomorphicOnCone geluC θ k.succ κ)
    (Z : Matrix d d ℝ) (η : Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm 0) hid) dIn dOut)
    (h16 : SuffixFlatZero (Arch.mlp gelu (rmsNorm 0) hid) θ k.castSucc Z η)
    (ξ ξ' : d → ℝ) (hξ : ξ ⬝ᵥ ξ = 1) (hξ' : ξ' ⬝ᵥ ξ' = 1) (hξξ' : ξ ⬝ᵥ ξ' = 0)
    (hP2 : PathP2 (θ.read k) (θ.write k) κ ξ ξ') :
    ∀ t : ℝ, 1 ≤ t →
      blockLHSC geluC θ k η
        (pathMatrix (Matrix.of fun _ : T => ξ) (Matrix.of fun _ : T => ξ') (t : ℂ) * θ.toC.1 k)
        (fun _ _ => 1)
        (zdotC θ k Z η
          (pathMatrix (Matrix.of fun _ : T => ξ) (Matrix.of fun _ : T => ξ') (t : ℂ))) = 0 := by
  sorry

/-- **Lemma D.19, Step 1, at `t = 1`:** "At `t = 1`, where `n(t)` is the row `n = √d ξ`, this reads
`0 = 𝓛(nW, 1; n)`", with the real `𝓛` and `ż(n)` of (20). -/
theorem gelu_path_step_zero_real [Nonempty T]
    (θ : Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm 0) hid) dIn dOut)
    (hθ : RegularZero (Arch.mlp gelu (rmsNorm 0) hid) θ) (k : Fin L)
    {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hhol : HolomorphicOnCone geluC θ k.succ κ)
    (Z : Matrix d d ℝ) (η : Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm 0) hid) dIn dOut)
    (h16 : SuffixFlatZero (Arch.mlp gelu (rmsNorm 0) hid) θ k.castSucc Z η)
    (ξ ξ' : d → ℝ) (hξ : ξ ⬝ᵥ ξ = 1) (hξ' : ξ' ⬝ᵥ ξ' = 1) (hξξ' : ξ ⬝ᵥ ξ' = 0)
    (hP2 : PathP2 (θ.read k) (θ.write k) κ ξ ξ') :
    blockLHS θ k η
      ((Matrix.of fun _ : T => Real.sqrt (Fintype.card d) • ξ) * θ.read k) (fun _ _ => 1)
      (tangentRMS Z (Matrix.of fun _ : T => Real.sqrt (Fintype.card d) • ξ) * θ.read k
        + (Matrix.of fun _ : T => Real.sqrt (Fintype.card d) • ξ) * η.read k) = 0 := by
  sorry

/-- **Lemma D.19, Steps 2 and 4, (50) at `t = 1`:** let `𝓛(z(t) − δ, 1 − δ'; n(t)) = 0` for all
`t ≥ 1` and all complex rows `δ, δ'` whose entries outside the set `A` of hidden units vanish, and
let the unit `j ∉ A` have a smaller rate `r_j = (ξc_j)² − (ξ'c_j)²` than every other unit outside
`A`. Then, at `n = √d ξ`: the derivative at `τ = 0` of `τ ↦ 𝓛(nW − τ e_j, 1; n)` vanishes
(`𝓛_j(1) = 0`), and `𝐃𝓑(n W V)(ż_j(n) a_j) = 0` (`𝓛'_j(1) = 0`). -/
theorem gelu_path_step_unit [Nonempty T]
    (θ : Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm 0) hid) dIn dOut)
    (hθ : RegularZero (Arch.mlp gelu (rmsNorm 0) hid) θ) (k : Fin L) [DecidableEq (hid k)]
    {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hhol : HolomorphicOnCone geluC θ k.succ κ)
    (Z : Matrix d d ℝ) (η : Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm 0) hid) dIn dOut)
    (h16 : SuffixFlatZero (Arch.mlp gelu (rmsNorm 0) hid) θ k.castSucc Z η)
    (ξ ξ' : d → ℝ) (hξ : ξ ⬝ᵥ ξ = 1) (hξ' : ξ' ⬝ᵥ ξ' = 1) (hξξ' : ξ ⬝ᵥ ξ' = 0)
    (hP2 : PathP2 (θ.read k) (θ.write k) κ ξ ξ')
    (A : Set (hid k)) (j : hid k) (hjA : j ∉ A)
    (hrate : ∀ i : hid k, i ∉ A → i ≠ j →
      ((ξ ᵥ* θ.read k) j) ^ 2 - ((ξ' ᵥ* θ.read k) j) ^ 2
        < ((ξ ᵥ* θ.read k) i) ^ 2 - ((ξ' ᵥ* θ.read k) i) ^ 2)
    (hA : ∀ t : ℝ, 1 ≤ t → ∀ δ δ' : hid k → ℂ, (∀ i, i ∉ A → δ i = 0 ∧ δ' i = 0) →
      blockLHSC geluC θ k η
        (Matrix.of fun τ i =>
          (pathMatrix (Matrix.of fun _ : T => ξ) (Matrix.of fun _ : T => ξ') (t : ℂ)
            * θ.toC.1 k) τ i - δ i)
        (Matrix.of fun _ i => 1 - δ' i)
        (zdotC θ k Z η
          (pathMatrix (Matrix.of fun _ : T => ξ) (Matrix.of fun _ : T => ξ') (t : ℂ))) = 0) :
    deriv (fun τ : ℝ =>
        blockLHS θ k η
          ((Matrix.of fun _ : T => Real.sqrt (Fintype.card d) • ξ) * θ.read k
            - τ • Matrix.of fun _ : T => (Pi.single j 1 : hid k → ℝ))
          (fun _ _ => 1)
          (tangentRMS Z (Matrix.of fun _ : T => Real.sqrt (Fintype.card d) • ξ) * θ.read k
            + (Matrix.of fun _ : T => Real.sqrt (Fintype.card d) • ξ) * η.read k)) 0 = 0 ∧
      fderiv ℝ (fun h' : Matrix T d ℝ => suffix (Arch.mlp gelu (rmsNorm 0) hid) 0 θ k.succ h')
        ((Matrix.of fun _ : T => Real.sqrt (Fintype.card d) • ξ) * θ.read k * θ.write k)
        (Matrix.of fun t =>
          (tangentRMS Z (Matrix.of fun _ : T => Real.sqrt (Fintype.card d) • ξ) * θ.read k
            + (Matrix.of fun _ : T => Real.sqrt (Fintype.card d) • ξ) * η.read k) t j
            • θ.write k j) = 0 := by
  sorry

end Skips
