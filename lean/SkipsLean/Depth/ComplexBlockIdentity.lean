import SkipsLean.Depth.ComplexSuffix
import SkipsLean.Depth.StepZeroValues

/-!
# The identity for one block at complex rows, and its continuation along the path

Paper (dimension paper): Appendix D.6 (the case `ε = 0`), "The identity on the path" and
Lemma D.15 (Continuation).

"With the notation of (20) and (21), let `κ = κ_{k+1}`. The same formulas define `ż(n) ∈ ℂ^{1×q}`
for `n ∈ ℂ^{1×d}`, and `𝓛(w̃, w̃'; n)` for rows `w̃, w̃' ∈ ℂ^{1×q}` with `w̃V ∈ C_κ`. `𝓛` is
holomorphic in `w̃`, affine in `w̃'` and polynomial in `n`."

"Lemma D.15 (Continuation). In the case (0), let (22) hold, and let `ξ, ξ'` be orthonormal. Suppose
that for every real `t ≥ 1` the function `σ` is holomorphic at every `n(t) c_j` and
`σ(n(t)W) V ∈ C_κ`. Then `𝓛(σ(n(t)W), σ'(n(t)W); n(t)) = 0` for all real `t ≥ 1`."

Its proof: "The left side is a holomorphic function of `t` on an open set that contains `[1, ∞)`,
hence on a connected open neighborhood of `[1, ∞)`. This neighborhood contains an arc of the unit
circle around `t = 1`, on which `n(t) ∈ S` and the function vanishes by (22). So it vanishes on
the whole neighborhood."

Here: the formulas (20) and (21) at complex arguments are `zdotC` and `blockLHSC`, with the complex
derivatives of `suffixC` (`Depth/ComplexSuffix.lean`) in the place of the real derivatives of
`𝓑`; at real arguments they are the real `ż` and `𝓛` (`blockLHS`, `Depth/StepTanh.lean`). The
activation `σ` is extended by a map `σC : ℂ → ℂ`, and `σ'` on the path is the complex derivative
`deriv σC`. A hidden state has the rows `T`; the path is taken at every token, with a pair
`ξ, ξ'` per token (`pathMatrix`). Numbering as in `Depth/StepTanh.lean`: the block is `k : Fin L`,
the hidden state before it `k.castSucc` and after it `k.succ`.
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut] {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)] {σ σ' : ℝ → ℝ} {σC : ℂ → ℂ}

/-- The right side of equation (14) at a complex `n`, row by row: `n Z − (⟨n Z, n⟩/d) n`, with
`⟨u, v⟩ = u vᵀ` (no complex conjugation). -/
noncomputable def tangentRMSC (Z : Matrix d d ℝ) (n : Matrix T d ℂ) : Matrix T d ℂ :=
  Matrix.of fun t => (n * Z.map (fun x : ℝ => (x : ℂ))) t
    - (((n * Z.map (fun x : ℝ => (x : ℂ))) t ⬝ᵥ n t) / (Fintype.card d : ℂ)) • n t

/-- **Equation (20) at a complex `n`:** `ż(n) = (n Z − (⟨n Z, n⟩/d) n) W + n η_W`, for block `k`
with the read `W`. -/
noncomputable def zdotC (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
    (k : Fin L) (Z : Matrix d d ℝ)
    (η : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) (n : Matrix T d ℂ) :
    Matrix T (hid k) ℂ :=
  tangentRMSC Z n * θ.toC.1 k + n * η.toC.1 k

/-- **Equation (21) at complex arguments:**
`𝓛 = 𝐃𝓑(w̃ V) ((w̃' ⊙ ż) V + w̃ η_V) + 𝐃_θ 𝓑(w̃ V) η`, for block `k` with the write `V` and the
network `𝓑 = 𝓑_{>k+1}` after it, at complex `w̃`, `w̃'` and `ż`. The derivatives are the complex
derivatives of `suffixC σC`, in the hidden state and in the weights. -/
noncomputable def blockLHSC (σC : ℂ → ℂ)
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) (k : Fin L)
    (η : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
    (w w' zdot : Matrix T (hid k) ℂ) : Matrix T dOut ℂ :=
  fderiv ℂ (fun h' : Matrix T d ℂ => suffixC σC θ.toC k.succ h') (w * θ.toC.2.1 k)
      ((Matrix.of fun t j => w' t j * zdot t j) * θ.toC.2.1 k + w * η.toC.2.1 k)
    + fderiv ℂ (fun ω : CWeights d dOut hid => suffixC σC ω k.succ (w * θ.toC.2.1 k))
        θ.toC η.toC

/-- **The path at every token:** row `τ` is `n(t) = (√d/2)(t ν + ν̄/t)` for the pair `ξ = Ξ τ`,
`ξ' = Ξ' τ`. -/
noncomputable def pathMatrix (Ξ Ξ' : Matrix T d ℝ) (t : ℂ) : Matrix T d ℂ :=
  Matrix.of fun τ => pathRow (Ξ τ) (Ξ' τ) t

/-- At a real `n`, the complex `n Z − (⟨n Z, n⟩/d) n` is the real one. -/
theorem tangentRMSC_ofReal (Z : Matrix d d ℝ) (n : Matrix T d ℝ) :
    tangentRMSC Z (n.map (fun x : ℝ => (x : ℂ)))
      = (tangentRMS Z n).map (fun x : ℝ => (x : ℂ)) := by
  sorry

/-- At a real `n`, the complex `ż(n)` is the real `ż(n)` of equation (20). -/
theorem zdotC_ofReal (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
    (k : Fin L) (Z : Matrix d d ℝ)
    (η : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) (n : Matrix T d ℝ) :
    zdotC θ k Z η (n.map (fun x : ℝ => (x : ℂ)))
      = (tangentRMS Z n * θ.read k + n * η.read k).map (fun x : ℝ => (x : ℂ)) := by
  sorry

/-- **`𝐃𝓑_{>k}` extends:** if `𝓑_{>k}` is holomorphic on a cone `C_κ`, `κ > 0`, then at a real
hidden state `h` without a zero row the complex derivative of `suffixC` in the hidden state, along
a real direction `v`, is the real derivative `𝐃𝓑_{>k}(h) v`. -/
theorem fderiv_suffixC_ofReal (hσ : ∀ x : ℝ, σC (x : ℂ) = ((σ x : ℝ) : ℂ))
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) (k : Fin (L + 1))
    {κ : ℝ} (hκ : 0 < κ) (hhol : HolomorphicOnCone σC θ k κ)
    (h v : Matrix T d ℝ) (hh : ∀ t, h t ≠ 0) :
    fderiv ℂ (fun h' : Matrix T d ℂ => suffixC σC θ.toC k h')
        (h.map (fun x : ℝ => (x : ℂ))) (v.map (fun x : ℝ => (x : ℂ)))
      = (fderiv ℝ (fun h' : Matrix T d ℝ => suffix (Arch.mlp σ (rmsNorm 0) hid) 0 θ k h')
          h v).map (fun x : ℝ => (x : ℂ)) := by
  sorry

/-- **`𝐃_θ𝓑_{>k}` extends:** under the same hypotheses, the complex derivative of `suffixC` in the
weights, at the real weights `θ` and along a real direction `η`, is the real derivative
`𝐃_θ𝓑_{>k}(h) η`. -/
theorem fderiv_weights_suffixC_ofReal (hσ : ∀ x : ℝ, σC (x : ℂ) = ((σ x : ℝ) : ℂ))
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) (k : Fin (L + 1))
    {κ : ℝ} (hκ : 0 < κ) (hhol : HolomorphicOnCone σC θ k κ)
    (h : Matrix T d ℝ) (hh : ∀ t, h t ≠ 0)
    (η : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) :
    fderiv ℂ (fun ω : CWeights d dOut hid => suffixC σC ω k (h.map (fun x : ℝ => (x : ℂ))))
        θ.toC η.toC
      = (fderiv ℝ (fun θ' : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut =>
          suffix (Arch.mlp σ (rmsNorm 0) hid) 0 θ' k h) θ η).map (fun x : ℝ => (x : ℂ)) := by
  sorry

/-- **"The same formulas define `𝓛`":** at real `w̃`, `w̃'` and `ż`, with `w̃ V` without a zero
row, the complex `𝓛` is the real `𝓛` of equation (21). -/
theorem blockLHSC_ofReal (hσ : ∀ x : ℝ, σC (x : ℂ) = ((σ x : ℝ) : ℂ))
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) (k : Fin L)
    {κ : ℝ} (hκ : 0 < κ) (hhol : HolomorphicOnCone σC θ k.succ κ)
    (η : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
    (w w' zdot : Matrix T (hid k) ℝ) (hw : ∀ t, (w * θ.write k) t ≠ 0) :
    blockLHSC σC θ k η (w.map (fun x : ℝ => (x : ℂ))) (w'.map (fun x : ℝ => (x : ℂ)))
        (zdot.map (fun x : ℝ => (x : ℂ)))
      = (blockLHS θ k η w w' zdot).map (fun x : ℝ => (x : ℂ)) := by
  sorry

/-- **Lemma D.15 of the dimension paper (Continuation).** In the case (0), for an MLP block with a
real-analytic activation `σ` (derivative `σ'`) that extends to a map `σC` holomorphic at every real
point, let `θ` be regular, let `𝓑_{>k+1}` be holomorphic on the cone `C_κ`, and let the identity
(16) hold before block `k` for `Z` and `η` (equivalently (22), by
`suffixFlatZero_castSucc_iff_mlp_sphere`). Let `ξ, ξ'` be orthonormal at every token. Suppose that
for every real `t ≥ 1` the map `σC` is holomorphic at every `n(t) c_j` and every row of
`σC(n(t) W) V` is in `C_κ`. Then `𝓛(σC(n(t)W), σC'(n(t)W); n(t)) = 0` for all real `t ≥ 1`. -/
theorem blockLHSC_pathMatrix_eq_zero [Nonempty d] (hσd : ∀ z, HasDerivAt σ (σ' z) z)
    (hσa : AnalyticOnNhd ℝ σ Set.univ) (hσ : ∀ x : ℝ, σC (x : ℂ) = ((σ x : ℝ) : ℂ))
    (hσC : ∀ x : ℝ, AnalyticAt ℂ σC (x : ℂ))
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
    (hθ : RegularZero (Arch.mlp σ (rmsNorm 0) hid) θ) (k : Fin L)
    {κ : ℝ} (hκ : 0 < κ) (hhol : HolomorphicOnCone σC θ k.succ κ)
    (Z : Matrix d d ℝ) (η : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
    (h16 : SuffixFlatZero (Arch.mlp σ (rmsNorm 0) hid) θ k.castSucc Z η)
    (Ξ Ξ' : Matrix T d ℝ) (hΞ : ∀ τ, Ξ τ ⬝ᵥ Ξ τ = 1) (hΞ' : ∀ τ, Ξ' τ ⬝ᵥ Ξ' τ = 1)
    (hΞΞ' : ∀ τ, Ξ τ ⬝ᵥ Ξ' τ = 0)
    (hpath : ∀ t : ℝ, 1 ≤ t →
      (∀ τ j, AnalyticAt ℂ σC ((pathMatrix Ξ Ξ' (t : ℂ) * θ.toC.1 k) τ j)) ∧
      ∀ τ, ((pathMatrix Ξ Ξ' (t : ℂ) * θ.toC.1 k).map σC * θ.toC.2.1 k) τ ∈ complexCone κ) :
    ∀ t : ℝ, 1 ≤ t →
      blockLHSC σC θ k η ((pathMatrix Ξ Ξ' (t : ℂ) * θ.toC.1 k).map σC)
        ((pathMatrix Ξ Ξ' (t : ℂ) * θ.toC.1 k).map (deriv σC))
        (zdotC θ k Z η (pathMatrix Ξ Ξ' (t : ℂ))) = 0 := by
  sorry

end Skips
