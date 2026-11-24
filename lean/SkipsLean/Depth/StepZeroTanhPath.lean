import SkipsLean.Depth.ComplexOneSubSq
import SkipsLean.Depth.PathSeparation

/-!
# The step for `tanh` on the path: what one pair `ξ, ξ'` gives

Paper (dimension paper): Appendix D.6 (the case `ε = 0`), proof of Lemma D.18 (the step for `tanh`
on the path), its parts "The path" and "The powers of `t`", for one pair of rows.

"Fix `ξ ∈ P'` and a unit row `ξ'` orthogonal to `ξ`, and let `n(t)` be the path (41). Let

  `ζ_j(t) = e^{−2 s_j n(t) c_j} = exp(−(t + t⁻¹) √d |ξc_j| − i (t − t⁻¹) √d s_j ξ'c_j)`,

so that `|ζ_j(t)| < ρ/3` for `t ≥ 1`, and `tanh(n(t) c_j) = s_j (1 − ζ_j(t))/(1 + ζ_j(t))`,
`tanh'(n(t) c_j) = 1 − tanh²(n(t) c_j)`. For `ζ` in the polydisc `D = {|ζ_j| < ρ/3}` let `w̃(ζ)` be
the row with the entries `s_j (1 − ζ_j)/(1 + ζ_j)`. As `|w̃_j(ζ) − s_j| = 2|ζ_j|/|1 + ζ_j| ≤ 3|ζ_j|
< ρ`, (S3) gives `w̃(ζ) V ∈ C_κ`. The function `tanh` is holomorphic at `n(t) c_j`, as
`ζ_j(t) ≠ −1`. So Lemma D.15 applies:

  `𝓛(w̃(ζ(t)), 1 − w̃(ζ(t))²; n(t)) = 0` for all `t ≥ 1`.   (42)

By (20), `ż(n(t)) = t³ ż⁽³⁾ + t ż⁽¹⁾ + t⁻¹ ż⁽⁻¹⁾ + t⁻³ ż⁽⁻³⁾` with rows `ż⁽ⁱ⁾ ∈ ℂ^{1×q}` that do not
depend on `t`, and

  `ż⁽³⁾ = −(√d/8) ⟨νZ, ν⟩ νW`,
  `ż⁽¹⁾ = (√d/2) (ν (ZW + η_W) − (1/4) ((⟨νZ, ν̄⟩ + ⟨ν̄Z, ν⟩) ν + ⟨νZ, ν⟩ ν̄) W)`.   (43)

`𝓛` is affine in `ż`, so (42) reads `∑_i t^i 𝒯_i(ζ(t)) = 0` with the maps
`𝒯_i(ζ) = 𝐃𝓑(w̃(ζ)V) (((1 − w̃(ζ)²) ⊙ ż⁽ⁱ⁾) V)` (`i = ±1, ±3`),
`𝒯_0(ζ) = 𝐃𝓑(w̃(ζ)V) (w̃(ζ) η_V) + 𝐃_θ𝓑(w̃(ζ)V) η'`, which are holomorphic on `D`. By Lemma D.16,
with `u_j = √d |ξc_j|` and `ρ₀ = ρ/3`, every `𝒯_i` vanishes on `D`. For real `ζ ∈ D` the rows
`w̃(ζ)` fill a neighborhood of `s̄` in `ℝ^{1×q}`."

Then `𝒯_3 = 0` and Lemma D.17 give `⟨νZ, ν⟩ = 0` (the row `νW` is not zero); `𝒯_1 = 0` and
Lemma D.17 give `ż⁽¹⁾ = 0`; and `𝒯_0 = 0` is the identity of part (c) for real `w̃` near `s̄`.

The statement below is this, for one pair `ξ, ξ'`, in real terms. With `ν = ξ + iξ'`:
`⟨νZ, ν⟩ = (ξZξᵀ − ξ'Zξ'ᵀ) + i (ξZξ'ᵀ + ξ'Zξᵀ)`, so `⟨νZ, ν⟩ = 0` is the first pair of
equations; then `⟨νZ, ν̄⟩ + ⟨ν̄Z, ν⟩ = 2 (ξZξᵀ + ξ'Zξ'ᵀ) = 4 ξZξᵀ`, and `ż⁽¹⁾ = 0` is
`ν (ZW + η_W) = (ξZξᵀ) νW`, the second pair (its real and its imaginary part). The paper's sign
row `s̄`, the number `ρ` and the cone condition of (S3) are hypotheses on `s`, `ρ` and `ξ` here
(Lemma D.18 takes them from (S3) for the rows `ξ` near `ξ₀`). The path has the same row at every
token. Numbering as in `Depth/StepTanh.lean`: the block is `k : Fin L`, the paper's block `k + 1`.
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut] {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]

/-- **Proof of Lemma D.18, the path and the powers of `t`, for one pair `ξ, ξ'`.** Let `σ = tanh`,
in the case (0), `d ≥ 2`, `θ` regular with (S1) for block `k`, `𝓑_{>k+1}` holomorphic on `C_κ`, and
let the identity (16) hold before block `k` for `Z` and `η`. Let `s_j = ±1` and `ρ ∈ (0, 1]` be such
that the rows `w̃V` with `|w̃_j − s_j| ≤ ρ` lie in `C_κ`. Let `ξ, ξ'` be orthonormal rows such that
`ξc_j` has the sign `s_j`, `e^{−2√d |ξc_j|} < ρ/3`, and `ξc_1, …, ξc_q` are linearly independent
over `ℚ`. Then:

* `ξZξ'ᵀ + ξ'Zξᵀ = 0` and `ξZξᵀ = ξ'Zξ'ᵀ` (this is `⟨νZ, ν⟩ = 0`, from `𝒯_3 = 0`);
* `ξ (ZW + η_W) = (ξZξᵀ) ξW` and `ξ' (ZW + η_W) = (ξZξᵀ) ξ'W` (this is `ż⁽¹⁾ = 0`, from
  `𝒯_1 = 0`);
* `𝐃𝓑(w̃V)(w̃ η_V) + 𝐃_θ𝓑(w̃V) η = 0` for every real row `w̃` with `|w̃_j − s_j| < ρ/4` (from
  `𝒯_0 = 0`), at the hidden state with the row `w̃V` at every token. -/
theorem tanh_path_step [Nonempty T]
    (θ : Params (Arch.mlp (T := T) (d := d) Real.tanh (rmsNorm 0) hid) dIn dOut)
    (hθ : RegularZero (Arch.mlp Real.tanh (rmsNorm 0) hid) θ) (hd : 2 ≤ Fintype.card d)
    (k : Fin L)
    (hS1 : ∀ i j : hid k, i ≠ j → ∀ a c : ℝ, a • θ.write k i + c • θ.write k j = 0 →
      a = 0 ∧ c = 0)
    {κ : ℝ} (hκ : 0 < κ) (hhol : HolomorphicOnCone Complex.tanh θ k.succ κ)
    (s : hid k → ℝ) (hs : ∀ j, s j = 1 ∨ s j = -1) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hcone : ∀ w : hid k → ℂ, (∀ j, ‖w j - (s j : ℂ)‖ ≤ ρ) →
      w ᵥ* θ.toC.2.1 k ∈ complexCone κ)
    (Z : Matrix d d ℝ)
    (η : Params (Arch.mlp (T := T) (d := d) Real.tanh (rmsNorm 0) hid) dIn dOut)
    (h16 : SuffixFlatZero (Arch.mlp Real.tanh (rmsNorm 0) hid) θ k.castSucc Z η)
    (ξ ξ' : d → ℝ) (hξ : ξ ⬝ᵥ ξ = 1) (hξ' : ξ' ⬝ᵥ ξ' = 1) (hξξ' : ξ ⬝ᵥ ξ' = 0)
    (hsign : ∀ j : hid k, 0 < s j * (ξ ᵥ* θ.read k) j)
    (hdecay : ∀ j : hid k,
      Real.exp (-(2 * (Real.sqrt (Fintype.card d) * |(ξ ᵥ* θ.read k) j|))) < ρ / 3)
    (hind : LinearIndependent ℚ (fun j : hid k => (ξ ᵥ* θ.read k) j)) :
    ((ξ ᵥ* Z) ⬝ᵥ ξ' + (ξ' ᵥ* Z) ⬝ᵥ ξ = 0 ∧ (ξ ᵥ* Z) ⬝ᵥ ξ = (ξ' ᵥ* Z) ⬝ᵥ ξ') ∧
    (ξ ᵥ* (Z * θ.read k + η.read k) = ((ξ ᵥ* Z) ⬝ᵥ ξ) • (ξ ᵥ* θ.read k) ∧
      ξ' ᵥ* (Z * θ.read k + η.read k) = ((ξ ᵥ* Z) ⬝ᵥ ξ) • (ξ' ᵥ* θ.read k)) ∧
    ∀ r : hid k → ℝ, (∀ j, |r j - s j| < ρ / 4) →
      fderiv ℝ
          (fun h' : Matrix T d ℝ => suffix (Arch.mlp Real.tanh (rmsNorm 0) hid) 0 θ k.succ h')
          ((Matrix.of fun (_ : T) => r) * θ.write k) ((Matrix.of fun (_ : T) => r) * η.write k)
        + fderiv ℝ
            (fun θ' : Params (Arch.mlp (T := T) (d := d) Real.tanh (rmsNorm 0) hid) dIn dOut =>
              suffix (Arch.mlp Real.tanh (rmsNorm 0) hid) 0 θ' k.succ
                ((Matrix.of fun (_ : T) => r) * θ.write k)) θ η = 0 := by
  sorry

end Skips
