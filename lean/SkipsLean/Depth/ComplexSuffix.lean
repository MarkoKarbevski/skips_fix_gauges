import SkipsLean.Depth.ComplexRMSNorm
import SkipsLean.Depth.SuffixZeroDeriv

/-!
# The network after a hidden state, on a complex cone

Paper (dimension paper): Appendix D.6 (the case `ε = 0`), Lemma D.14 (`𝓑_{>k}` on a complex cone).
"Let `θ` satisfy (R1) and (R2). For every `k` there is a `κ_k ∈ (0, 1]` such that `𝓑_{>k}`, with
its derivatives `𝐃𝓑_{>k}` and `𝐃_θ𝓑_{>k}`, extends to a holomorphic map on `C_{κ_k}` with
`𝓑_{>k}(λh) = 𝓑_{>k}(h)` for `λ > 0`. The number `κ_k` depends only on the weights of the blocks
`k + 1, …, L` and on `D`."

Its proof: "`𝓑_{>L}(h) = N(h) D` is holomorphic on `C_1`: `κ_L = 1`. Let `k < L`. The map `g_{k+1}`
is holomorphic near `S` and maps the compact set `S` into the real rows `h ≠ 0`, by (R2), hence
into the open set `C_{κ_{k+1}}`. So there is a `ρ > 0` such that `n ↦ 𝓑_{>k+1}(g_{k+1}(n))` is
holomorphic on the set of the `n` at distance less than `ρ` from `S`. On the compact set of the
`u + iu'` with `‖u‖ = 1` and `‖u'‖ ≤ 1/2`, `N` is uniformly continuous, and `N(u) ∈ S`. So there is
a `κ_k` such that `N` maps `C_{κ_k}` into the points at distance less than `ρ` from `S`, and
`𝓑_{>k} = 𝓑_{>k+1} ∘ g_{k+1} ∘ N` is holomorphic on `C_{κ_k}`. The weights enter holomorphically as
well."

Here, for networks of MLP blocks: the weights of the blocks and of the readout become complex
(`CWeights`), the activation `σ` is replaced by a map `σC : ℂ → ℂ` that extends it, and
`suffixC σC ω k h` is `𝓑_{>k}(h)` at the complex weights `ω` and the complex hidden state `h`. The
derivatives of the paper are the complex derivatives of this one map of `(ω, h)`, so "extends to a
holomorphic map, with its derivatives" is: `(ω, h) ↦ suffixC σC ω k h` is analytic at
`(θ, h)` for every `h` whose rows are in the cone (`HolomorphicOnCone`). A hidden state has the rows
`T`, each in the cone.
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut] {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]

/-- The complex weights of the blocks of a network of MLP blocks and of its readout: the reads
`W_read^ℓ`, the writes `W_write^ℓ` and `D`, with complex entries. -/
abbrev CWeights (d dOut : Type*) {L : ℕ} (hid : Fin L → Type) : Type _ :=
  (∀ ℓ, Matrix d (hid ℓ) ℂ) × (∀ ℓ, Matrix (hid ℓ) d ℂ) × Matrix d dOut ℂ

/-- The real weights of the blocks and of the readout, as complex weights. -/
def Params.toC {σ : ℝ → ℝ} {χ : Matrix T d ℝ → Matrix T d ℝ}
    (θ : Params (Arch.mlp (T := T) (d := d) σ χ hid) dIn dOut) : CWeights d dOut hid :=
  (fun ℓ => (θ.read ℓ).map (fun x : ℝ => (x : ℂ)), fun ℓ => (θ.write ℓ).map (fun x : ℝ => (x : ℂ)),
    θ.D.map (fun x : ℝ => (x : ℂ)))

/-- `𝓑_{>k}(h)` at complex weights and a complex hidden state, for MLP blocks with the activation
`σC : ℂ → ℂ` under pre-RMSNorm with `ε = 0`: `𝓑_{>L}(h) = N(h) D` and
`𝓑_{>k−1}(h) = 𝓑_{>k}(σC(N(h) W_read^k) W_write^k)`. -/
noncomputable def suffixC (σC : ℂ → ℂ) (ω : CWeights d dOut hid) :
    Fin (L + 1) → Matrix T d ℂ → Matrix T dOut ℂ :=
  Fin.reverseInduction (motive := fun _ => Matrix T d ℂ → Matrix T dOut ℂ)
    (fun h => rmsNormC h * ω.2.2)
    (fun ℓ B h => B ((rmsNormC h * ω.1 ℓ).map σC * ω.2.1 ℓ))


omit [Fintype T] [DecidableEq d] [Fintype dOut] in
/-- Helper: `𝓑_{>L}(h) = N(h) D` at complex weights. -/
private theorem suffixC_last_cs (σC : ℂ → ℂ) (ω : CWeights d dOut hid) (h : Matrix T d ℂ) :
    suffixC σC ω (Fin.last L) h = rmsNormC h * ω.2.2 := by
  simp only [suffixC, Fin.reverseInduction_last]

omit [Fintype T] [DecidableEq d] [Fintype dOut] in
/-- Helper: `𝓑_{>ℓ-1}(h) = 𝓑_{>ℓ}(σC(N(h) W_read^ℓ) W_write^ℓ)` at complex weights. -/
private theorem suffixC_castSucc_cs (σC : ℂ → ℂ) (ω : CWeights d dOut hid) (ℓ : Fin L)
    (h : Matrix T d ℂ) :
    suffixC σC ω ℓ.castSucc h = suffixC σC ω ℓ.succ ((rmsNormC h * ω.1 ℓ).map σC * ω.2.1 ℓ) := by
  simp only [suffixC, Fin.reverseInduction_castSucc]

omit [Fintype T] [DecidableEq d] in
/-- Helper: the complex RMSNorm of a real hidden state is the real RMSNorm (`ε = 0`), also at
zero rows (both sides are `0` there). -/
private theorem rmsNormC_map_ofReal_cs (h : Matrix T d ℝ) :
    rmsNormC (h.map (fun x : ℝ => (x : ℂ))) = (rmsNorm 0 h).map (fun x : ℝ => (x : ℂ)) := by
  ext t i
  by_cases ht : h t = 0
  · -- a zero row: both sides are `0`
    have h1 : (h.map (fun x : ℝ => (x : ℂ))) t = 0 := by
      funext j; simp [Matrix.map_apply, ht]
    simp [rmsNormC, rmsNorm, rmsRowC, rmsRow, h1, ht]
  · -- a nonzero row: `rmsRowC_ofReal`
    show rmsRowC (fun j => (h t j : ℂ)) i = ((rmsRow 0 (h t) i : ℝ) : ℂ)
    exact congrFun (rmsRowC_ofReal (h t) ht) i

omit [Fintype T] in
/-- Helper: the cast of a product of real matrices is the product of the casts. -/
private theorem map_mul_ofReal_cs {m n p : Type*} [Fintype n] (A : Matrix m n ℝ)
    (B : Matrix n p ℝ) :
    (A * B).map (fun x : ℝ => (x : ℂ))
      = A.map (fun x : ℝ => (x : ℂ)) * B.map (fun x : ℝ => (x : ℂ)) :=
  Matrix.map_mul (f := Complex.ofRealHom)

omit [Fintype T] [DecidableEq d] in
/-- Helper: `rmsNormC` multiplied rows: `N(c_t h_t) = N(h_t)` row by row. -/
private theorem rmsNormC_smul_rows_cs (h : Matrix T d ℂ) (hh : ∀ t, 0 < (h t ⬝ᵥ h t).re)
    (c : T → ℝ) (hc : ∀ t, 0 < c t) :
    rmsNormC (Matrix.of fun t => (c t : ℂ) • h t) = rmsNormC h := by
  ext t i
  show rmsRowC ((c t : ℂ) • h t) i = rmsRowC (h t) i
  rw [rmsRowC_smul (c t) (hc t) (h t) (hh t)]

/-- **`suffixC` extends `suffix`:** if `σC` extends `σ`, then at the real weights and at a real
hidden state `h`, `suffixC` is `𝓑_{>k}(h)`. -/
theorem suffixC_ofReal {σ : ℝ → ℝ} {σC : ℂ → ℂ} (hσ : ∀ x : ℝ, σC (x : ℂ) = ((σ x : ℝ) : ℂ))
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) (k : Fin (L + 1))
    (h : Matrix T d ℝ) :
    suffixC σC θ.toC k (h.map (fun x : ℝ => (x : ℂ)))
      = (suffix (Arch.mlp σ (rmsNorm 0) hid) 0 θ k h).map (fun x : ℝ => (x : ℂ)) := by
  induction k using Fin.reverseInduction generalizing h with
  | last =>
    -- `𝓑_{>L}(h) = N(h) D`
    rw [suffixC_last_cs, suffix_last, rmsNormC_map_ofReal_cs]
    exact (map_mul_ofReal_cs _ _).symm
  | cast ℓ ih =>
    -- one block: `σC` extends `σ`, and the induction hypothesis at `σ(N(h) W) V`
    rw [suffixC_castSucc_cs, suffix_castSucc]
    simp only [Pi.zero_apply, Matrix.mul_zero, zero_add]
    rw [← ih]
    congr 1
    show (rmsNormC (h.map (fun x : ℝ => (x : ℂ))) * (θ.read ℓ).map (fun x : ℝ => (x : ℂ))).map σC
        * (θ.write ℓ).map (fun x : ℝ => (x : ℂ))
      = (((rmsNorm 0 h * θ.read ℓ).map σ) * θ.write ℓ).map (fun x : ℝ => (x : ℂ))
    rw [map_mul_ofReal_cs, rmsNormC_map_ofReal_cs, ← map_mul_ofReal_cs]
    congr 1
    ext t j
    simp [hσ]

/-- "`𝓑_{>k}(λh) = 𝓑_{>k}(h)` for `λ > 0`" on the cone `C_1`: multiplying the rows of `h` by
positive numbers does not change `suffixC`, when every row of `h` has `Re⟨h, h⟩ > 0`. -/
theorem suffixC_smul_rows (σC : ℂ → ℂ) (ω : CWeights d dOut hid) (k : Fin (L + 1))
    (h : Matrix T d ℂ) (hh : ∀ t, 0 < (h t ⬝ᵥ h t).re) (c : T → ℝ) (hc : ∀ t, 0 < c t) :
    suffixC σC ω k (Matrix.of fun t => (c t : ℂ) • h t) = suffixC σC ω k h := by
  have hN := rmsNormC_smul_rows_cs h hh c hc
  refine Fin.lastCases ?_ (fun ℓ => ?_) k
  · rw [suffixC_last_cs, suffixC_last_cs, hN]
  · rw [suffixC_castSucc_cs, suffixC_castSucc_cs, hN]

/-- "`𝓑_{>k}`, with its derivatives `𝐃𝓑_{>k}` and `𝐃_θ𝓑_{>k}`, extends to a holomorphic map on
`C_κ`": the map `(ω, h) ↦ suffixC σC ω k h` is analytic at `(θ, h)` for every `h` whose rows are in
`C_κ`. -/
def HolomorphicOnCone {σ : ℝ → ℝ} (σC : ℂ → ℂ)
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) (k : Fin (L + 1))
    (κ : ℝ) : Prop :=
  ∀ h : Matrix T d ℂ, (∀ t, h t ∈ complexCone κ) →
    AnalyticAt ℂ
      (fun p : CWeights d dOut hid × Matrix T d ℂ => suffixC σC p.1 k p.2) (θ.toC, h)

/-- **Lemma D.14 of the dimension paper (`𝓑_{>k}` on a complex cone),** for MLP blocks whose
activation `σ` extends to a map `σC` that is holomorphic at every real point: if `θ` is regular
((R1) and (R2) are used), then for every `k` there is a `κ_k ∈ (0, 1]` such that `𝓑_{>k}`, with
its derivatives, extends to a holomorphic map on `C_{κ_k}`. -/
theorem exists_holomorphicOnCone {σ : ℝ → ℝ} {σC : ℂ → ℂ}
    (hσ : ∀ x : ℝ, σC (x : ℂ) = ((σ x : ℝ) : ℂ)) (hσC : ∀ x : ℝ, AnalyticAt ℂ σC (x : ℂ))
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
    (hθ : RegularZero (Arch.mlp σ (rmsNorm 0) hid) θ) (k : Fin (L + 1)) :
    ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1 ∧ HolomorphicOnCone σC θ k κ := by
  sorry

/-- The cones of Lemma D.14 may be shrunk: `HolomorphicOnCone` for `κ` gives it for every
`0 ≤ κ' ≤ κ`. -/
theorem HolomorphicOnCone.mono {σ : ℝ → ℝ} {σC : ℂ → ℂ}
    {θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut} {k : Fin (L + 1)}
    {κ κ' : ℝ} (h : HolomorphicOnCone σC θ k κ) (hκ' : 0 ≤ κ') (hle : κ' ≤ κ) :
    HolomorphicOnCone σC θ k κ' := by
  exact fun h' hh => h h' fun t => complexCone_mono hκ' hle (hh t)

end Skips
