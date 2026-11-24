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

omit [Fintype T] [DecidableEq d] [Fintype dOut] in
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

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (the complex version of `analyticOnNhd_matrix_mul` of `Depth/SuffixRMS.lean`, at a
point): the matrix product of two analytic matrix-valued maps is analytic. -/
private theorem analyticAt_matrix_mul_cs {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
    {f : E → Matrix m n ℂ} {g : E → Matrix n p ℂ} {x : E}
    (hf : AnalyticAt ℂ f x) (hg : AnalyticAt ℂ g x) :
    AnalyticAt ℂ (fun y => f y * g y) x := by
  -- matrix multiplication as a bilinear map
  let B : Matrix m n ℂ →ₗ[ℂ] Matrix n p ℂ →ₗ[ℂ] Matrix m p ℂ :=
    LinearMap.mk₂ ℂ (fun a b => a * b) Matrix.add_mul (fun c a b => Matrix.smul_mul c a b)
      Matrix.mul_add (fun c a b => Matrix.mul_smul a c b)
  -- the same map with continuous linear maps (all spaces are finite-dimensional)
  let B' : Matrix m n ℂ →L[ℂ] Matrix n p ℂ →L[ℂ] Matrix m p ℂ :=
    LinearMap.toContinuousLinearMap
      ((LinearMap.toContinuousLinearMap :
        (Matrix n p ℂ →ₗ[ℂ] Matrix m p ℂ) ≃ₗ[ℂ] (Matrix n p ℂ →L[ℂ] Matrix m p ℂ)).toLinearMap ∘ₗ B)
  have hB : (fun y => f y * g y) = fun y => B' (f y) (g y) := rfl
  rw [hB]
  exact (B'.analyticAt_bilinear (f x, g x)).comp₂ hf hg

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: if `F` is analytic at `x` and `σC` is analytic at every entry of `F x`, then
`y ↦ σC(F y)` (entrywise) is analytic at `x`. -/
private theorem analyticAt_map_cs {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {m n : Type*} [Fintype m] [Fintype n] {σC : ℂ → ℂ} {F : E → Matrix m n ℂ} {x : E}
    (hF : AnalyticAt ℂ F x) (hσ : ∀ i j, AnalyticAt ℂ σC (F x i j)) :
    AnalyticAt ℂ (fun y => (F y).map σC) x := by
  show AnalyticAt ℂ (fun y => fun i => fun j => σC (F y i j)) x
  refine AnalyticAt.pi fun i => AnalyticAt.pi fun j => ?_
  -- an entry is a continuous linear function of the matrix
  have he : AnalyticAt ℂ (fun M : Matrix m n ℂ => M i j) (F x) :=
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : n => ℂ) j).comp
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : m => n → ℂ) i)).analyticAt _
  exact AnalyticAt.comp (f := fun y => F y i j) (hσ i j) (he.comp hF)

omit [DecidableEq d] in
/-- Helper: `rmsNormC` is analytic at every hidden state whose rows have `Re⟨h, h⟩ > 0`. -/
private theorem analyticAt_rmsNormC_cs (h : Matrix T d ℂ) (hh : ∀ t, 0 < (h t ⬝ᵥ h t).re) :
    AnalyticAt ℂ (rmsNormC : Matrix T d ℂ → Matrix T d ℂ) h := by
  show AnalyticAt ℂ (fun h : Matrix T d ℂ => fun t => rmsRowC (h t)) h
  refine AnalyticAt.pi fun t => ?_
  -- row `t` is `rmsRowC` after the (continuous linear) row projection
  have hp : AnalyticAt ℂ (fun M : Matrix T d ℂ => M t) h :=
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : T => d → ℂ) t).analyticAt _
  exact AnalyticAt.comp (f := fun M : Matrix T d ℂ => M t) (analyticAt_rmsRowC (h t) (hh t)) hp

omit [Fintype T] [DecidableEq d] in
/-- Helper: the cast of `v M` for a real row `v` and a real matrix `M`. -/
private theorem vecMul_ofReal_cs {m : Type*} (v : d → ℝ) (M : Matrix d m ℝ) :
    (fun i => (v i : ℂ)) ᵥ* M.map (fun x : ℝ => (x : ℂ)) = fun j => ((v ᵥ* M) j : ℂ) := by
  funext j
  exact (RingHom.map_vecMul Complex.ofRealHom M v j).symm

omit [Fintype T] [DecidableEq d] in
/-- Helper, step (a) of the proof of Lemma D.14, at one row: at a real row `n₀` whose block value
`σ(n₀ W) V` is not `0`, the rows `v` at which `σC` is holomorphic at the entries of `v W` and at
which `σC(v W) V` is in `C_κ` form a neighbourhood of `n₀`. -/
private theorem goodRow_mem_nhds_cs {m : Type*} [Fintype m] {σ : ℝ → ℝ} {σC : ℂ → ℂ}
    (hσ : ∀ x : ℝ, σC (x : ℂ) = ((σ x : ℝ) : ℂ)) (hσC : ∀ x : ℝ, AnalyticAt ℂ σC (x : ℂ))
    (Wr : Matrix d m ℝ) (Vr : Matrix m d ℝ) {κ : ℝ} (hκ : 0 < κ) (n₀ : d → ℝ)
    (hn₀ : (fun j => σ ((n₀ ᵥ* Wr) j)) ᵥ* Vr ≠ 0) :
    {v : d → ℂ | (∀ j, AnalyticAt ℂ σC ((v ᵥ* Wr.map (fun x : ℝ => (x : ℂ))) j)) ∧
        (fun j => σC ((v ᵥ* Wr.map (fun x : ℝ => (x : ℂ))) j)) ᵥ* Vr.map (fun x : ℝ => (x : ℂ))
          ∈ complexCone κ} ∈ nhds (fun i => (n₀ i : ℂ)) := by
  -- the entries of `n₀ W` are real
  have hreal : ∀ j, ((fun i => (n₀ i : ℂ)) ᵥ* Wr.map (fun x : ℝ => (x : ℂ))) j
      = ((n₀ ᵥ* Wr) j : ℂ) := fun j => congrFun (vecMul_ofReal_cs n₀ Wr) j
  -- `v ↦ (v W)_j` is continuous
  have hcj : ∀ j, Continuous fun v : d → ℂ => (v ᵥ* Wr.map (fun x : ℝ => (x : ℂ))) j :=
    fun j => (continuous_apply j).comp (continuous_id.matrix_vecMul continuous_const)
  show ∀ᶠ v in nhds (fun i => (n₀ i : ℂ)), _ ∧ _
  refine Filter.Eventually.and ?_ ?_
  · -- holomorphy of `σC` at a point is an open condition, and it holds at the real entries
    refine Filter.eventually_all.2 fun j => ?_
    have hmem : {z | AnalyticAt ℂ σC z}
        ∈ nhds (((fun i => (n₀ i : ℂ)) ᵥ* Wr.map (fun x : ℝ => (x : ℂ))) j) := by
      refine (isOpen_analyticAt ℂ σC).mem_nhds ?_
      show AnalyticAt ℂ σC (((fun i => (n₀ i : ℂ)) ᵥ* Wr.map (fun x : ℝ => (x : ℂ))) j)
      rw [hreal j]
      exact hσC _
    exact (hcj j).continuousAt.eventually_mem hmem
  · -- the block is continuous at `n₀`, and its value there is a real row `≠ 0`, in the open `C_κ`
    have h1 : ContinuousAt (fun v : d → ℂ => fun j => σC ((v ᵥ* Wr.map (fun x : ℝ => (x : ℂ))) j))
        (fun i => (n₀ i : ℂ)) :=
      continuousAt_pi.2 fun j => (hσC _).continuousAt.comp_of_eq (hcj j).continuousAt (hreal j)
    have hcont : ContinuousAt (fun v : d → ℂ =>
        (fun j => σC ((v ᵥ* Wr.map (fun x : ℝ => (x : ℂ))) j)) ᵥ* Vr.map (fun x : ℝ => (x : ℂ)))
        (fun i => (n₀ i : ℂ)) :=
      (continuous_id.matrix_vecMul continuous_const).continuousAt.comp h1
    have hval : (fun j => σC (((fun i => (n₀ i : ℂ)) ᵥ* Wr.map (fun x : ℝ => (x : ℂ))) j))
          ᵥ* Vr.map (fun x : ℝ => (x : ℂ))
        = fun i => (((fun j => σ ((n₀ ᵥ* Wr) j)) ᵥ* Vr) i : ℂ) := by
      have h2 : (fun j => σC (((fun i => (n₀ i : ℂ)) ᵥ* Wr.map (fun x : ℝ => (x : ℂ))) j))
          = fun j => ((σ ((n₀ ᵥ* Wr) j) : ℝ) : ℂ) := funext fun j => by rw [hreal j, hσ]
      rw [h2, vecMul_ofReal_cs]
    refine hcont.eventually_mem ((isOpen_complexCone κ).mem_nhds ?_)
    rw [hval]
    exact ofReal_mem_complexCone hκ _ hn₀

omit [Fintype T] [DecidableEq d] in
/-- Helper, step (b) of the proof of Lemma D.14: if a set `O` of complex rows is a neighbourhood
of every real row on the sphere `S = {‖n‖² = d}`, then there is a `δ > 0` such that `N(u + iw) ∈ O`
for every real `u` with `‖u‖ = 1` and every real `w` with `‖w‖ < δ` (sup norm). -/
private theorem exists_delta_cs (O : Set (d → ℂ))
    (hO : ∀ n₀ : d → ℝ, n₀ ⬝ᵥ n₀ = (Fintype.card d : ℝ) → O ∈ nhds (fun i => (n₀ i : ℂ))) :
    ∃ δ > 0, ∀ u w : d → ℝ, u ⬝ᵥ u = 1 → ‖w‖ < δ →
      rmsRowC (fun i => (u i : ℂ) + (w i : ℂ) * Complex.I) ∈ O := by
  -- the unit sphere of real rows is compact (closed and bounded: `u_i² ≤ ‖u‖² = 1`)
  have hK : IsCompact {u : d → ℝ | u ⬝ᵥ u = 1} := by
    refine (isCompact_closedBall (0 : d → ℝ) 1).of_isClosed_subset ?_ ?_
    · exact isClosed_eq (continuous_id.dotProduct continuous_id) continuous_const
    · intro u hu
      rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
      intro i
      have h1 : u i * u i ≤ u ⬝ᵥ u :=
        Finset.single_le_sum (f := fun j => u j * u j) (fun j _ => mul_self_nonneg (u j))
          (Finset.mem_univ i)
      have h2 : u ⬝ᵥ u = 1 := hu
      rw [Real.norm_eq_abs]
      exact abs_le_one_iff_mul_self_le_one.2 (h2 ▸ h1)
  -- at `w = 0` the map is `N(u) ∈ S`, where `O` is a neighbourhood; compactness of the sphere
  have hev := hK.eventually_forall_of_forall_eventually (x₀ := (0 : d → ℝ))
    (P := fun w u => rmsRowC (fun i => (u i : ℂ) + (w i : ℂ) * Complex.I) ∈ O) ?_
  · obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hev
    exact ⟨δ, hδ, fun u w hu hw => hball (by rwa [dist_zero_right]) u hu⟩
  · intro u hu
    have hu1 : u ⬝ᵥ u = 1 := hu
    have hu0 : u ≠ 0 := by
      rintro rfl
      simp at hu1
    -- `Re⟨u, u⟩ = 1 > 0` at the real row `u`
    have hpos : 0 < ((fun i => (u i : ℂ)) ⬝ᵥ (fun i => (u i : ℂ))).re := by
      have h1 : ((fun i => (u i : ℂ)) ⬝ᵥ (fun i => (u i : ℂ))) = ((u ⬝ᵥ u : ℝ) : ℂ) := by
        simp [dotProduct]
      rw [h1, hu1]
      simp
    have hΦ : Continuous fun z : (d → ℝ) × (d → ℝ) =>
        fun i => (z.2 i : ℂ) + (z.1 i : ℂ) * Complex.I := by
      fun_prop
    have hΦ0 : (fun i => (((0 : d → ℝ), u).2 i : ℂ) + (((0 : d → ℝ), u).1 i : ℂ) * Complex.I)
        = fun i => (u i : ℂ) := by
      funext i
      simp
    have hcont : ContinuousAt (fun z : (d → ℝ) × (d → ℝ) =>
        rmsRowC (fun i => (z.2 i : ℂ) + (z.1 i : ℂ) * Complex.I)) ((0 : d → ℝ), u) :=
      (analyticAt_rmsRowC _ hpos).continuousAt.comp_of_eq hΦ.continuousAt hΦ0
    -- `N(u)` is the real row `rmsRow 0 u` on the sphere `S`
    have hS : rmsRow 0 u ⬝ᵥ rmsRow 0 u = (Fintype.card d : ℝ) :=
      rmsNorm_zero_dotProduct_self (T := Unit) (Matrix.of fun _ => u) () hu0
    refine hcont.eventually_mem ?_
    show O ∈ nhds (rmsRowC (fun i => (((0 : d → ℝ), u).2 i : ℂ)
      + (((0 : d → ℝ), u).1 i : ℂ) * Complex.I))
    rw [hΦ0, rmsRowC_ofReal u hu0]
    exact hO _ hS

omit [Fintype T] [DecidableEq d] in
/-- Helper, step (b) of the proof of Lemma D.14, continued: with `δ` as in `exists_delta_cs`,
`N` maps the cone `C_{min 1 δ}` into `O`. Write `v = u + iw`, scale by `c = 1/‖u‖` (`N(cv) = N(v)`):
`‖cu‖ = 1` and `‖cw‖ < min 1 δ ≤ δ`. -/
private theorem rmsRowC_mem_of_cone_cs (O : Set (d → ℂ)) {δ : ℝ} (hδ : 0 < δ)
    (hO : ∀ u w : d → ℝ, u ⬝ᵥ u = 1 → ‖w‖ < δ →
      rmsRowC (fun i => (u i : ℂ) + (w i : ℂ) * Complex.I) ∈ O)
    (v : d → ℂ) (hv : v ∈ complexCone (min 1 δ)) : rmsRowC v ∈ O := by
  set κ := min 1 δ with hκ
  have hκ0 : 0 < κ := lt_min one_pos hδ
  have hκ1 : κ ≤ 1 := min_le_left _ _
  have hκδ : κ ≤ δ := min_le_right _ _
  -- real and imaginary parts
  obtain ⟨u, hu⟩ : ∃ u : d → ℝ, u = fun i => (v i).re := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w : d → ℝ, w = fun i => (v i).im := ⟨_, rfl⟩
  have hcone : w ⬝ᵥ w < κ ^ 2 * (u ⬝ᵥ u) := by
    rw [hu, hw]; exact hv
  have hww : 0 ≤ w ⬝ᵥ w := Finset.sum_nonneg fun i _ => mul_self_nonneg (w i)
  have huu : 0 < u ⬝ᵥ u := by
    by_contra hne
    push Not at hne
    nlinarith [sq_nonneg κ]
  have hre : 0 < (v ⬝ᵥ v).re := re_dotProduct_self_pos_of_mem_complexCone hκ0.le hκ1 hv
  -- the scale `c = 1/‖u‖`
  set c := (Real.sqrt (u ⬝ᵥ u))⁻¹ with hc
  have hs : 0 < Real.sqrt (u ⬝ᵥ u) := Real.sqrt_pos.2 huu
  have hc0 : 0 < c := inv_pos.2 hs
  have hcc : c * c * (u ⬝ᵥ u) = 1 := by
    rw [hc, ← mul_inv, Real.mul_self_sqrt huu.le, inv_mul_cancel₀ huu.ne']
  -- `cv = cu + i cw`
  have hcv : (c : ℂ) • v = fun i => ((c • u) i : ℂ) + ((c • w) i : ℂ) * Complex.I := by
    funext i
    apply Complex.ext <;> simp [hu, hw]
  rw [← rmsRowC_smul c hc0 v hre, hcv]
  refine hO (c • u) (c • w) ?_ ?_
  · rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc, hcc]
  · rw [pi_norm_lt_iff hδ]
    intro i
    -- `(c w_i)² ≤ ‖cw‖² = c² ‖w‖² < c² κ² ‖u‖² = κ² ≤ δ²`
    have h1 : (c • w) i * (c • w) i ≤ (c • w) ⬝ᵥ (c • w) :=
      Finset.single_le_sum (f := fun j => (c • w) j * (c • w) j)
        (fun j _ => mul_self_nonneg ((c • w) j)) (Finset.mem_univ i)
    have h2 : (c • w) ⬝ᵥ (c • w) = c * c * (w ⬝ᵥ w) := by
      rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc]
    have h3 : c * c * (w ⬝ᵥ w) < κ ^ 2 := by
      have := mul_lt_mul_of_pos_left hcone (mul_pos hc0 hc0)
      calc c * c * (w ⬝ᵥ w) < c * c * (κ ^ 2 * (u ⬝ᵥ u)) := this
        _ = κ ^ 2 * (c * c * (u ⬝ᵥ u)) := by ring
        _ = κ ^ 2 := by rw [hcc, mul_one]
    have h4 : κ ^ 2 ≤ δ ^ 2 := pow_le_pow_left₀ hκ0.le hκδ 2
    rw [Real.norm_eq_abs]
    refine abs_lt_of_sq_lt_sq ?_ hδ.le
    nlinarith

omit [DecidableEq d] [Fintype dIn] in
/-- **Lemma D.14 of the dimension paper (`𝓑_{>k}` on a complex cone),** for MLP blocks whose
activation `σ` extends to a map `σC` that is holomorphic at every real point: if `θ` is regular
(of (R1) to (R3) the proof uses (R2) only), then for every `k` there is a `κ_k ∈ (0, 1]` such that `𝓑_{>k}`, with
its derivatives, extends to a holomorphic map on `C_{κ_k}`. -/
theorem exists_holomorphicOnCone {σ : ℝ → ℝ} {σC : ℂ → ℂ}
    (hσ : ∀ x : ℝ, σC (x : ℂ) = ((σ x : ℝ) : ℂ)) (hσC : ∀ x : ℝ, AnalyticAt ℂ σC (x : ℂ))
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
    (hθ : RegularZero (Arch.mlp σ (rmsNorm 0) hid) θ) (k : Fin (L + 1)) :
    ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1 ∧ HolomorphicOnCone σC θ k κ := by
  -- no tokens: every map into `Matrix T dOut ℂ` is constant
  rcases isEmpty_or_nonempty T with hT | ⟨⟨t₀⟩⟩
  · refine ⟨1, one_pos, le_rfl, fun h _ => ?_⟩
    have hc : (fun p : CWeights d dOut hid × Matrix T d ℂ => suffixC σC p.1 k p.2)
        = fun _ => (0 : Matrix T dOut ℂ) := funext fun p => Matrix.ext fun t => isEmptyElim t
    rw [hc]
    exact analyticAt_const
  -- the projections to the reads, the writes and the readout are continuous linear
  have hfst : ∀ x : CWeights d dOut hid × Matrix T d ℂ,
      AnalyticAt ℂ (fun p : CWeights d dOut hid × Matrix T d ℂ => p.1) x := fun x => analyticAt_fst
  have hread : ∀ (ℓ : Fin L) (x : CWeights d dOut hid × Matrix T d ℂ),
      AnalyticAt ℂ (fun p : CWeights d dOut hid × Matrix T d ℂ => p.1.1 ℓ) x := by
    intro ℓ x
    have h1 : AnalyticAt ℂ (fun ω : (∀ ℓ, Matrix d (hid ℓ) ℂ) => ω ℓ) x.1.1 :=
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun ℓ => Matrix d (hid ℓ) ℂ) ℓ).analyticAt _
    have h2 : AnalyticAt ℂ (fun ω : CWeights d dOut hid => ω.1) x.1 := analyticAt_fst
    exact AnalyticAt.comp (f := fun p : CWeights d dOut hid × Matrix T d ℂ => p.1.1) h1
      (AnalyticAt.comp (f := fun p : CWeights d dOut hid × Matrix T d ℂ => p.1) h2 (hfst x))
  have hwrite : ∀ (ℓ : Fin L) (x : CWeights d dOut hid × Matrix T d ℂ),
      AnalyticAt ℂ (fun p : CWeights d dOut hid × Matrix T d ℂ => p.1.2.1 ℓ) x := by
    intro ℓ x
    have h1 : AnalyticAt ℂ (fun ω : (∀ ℓ, Matrix (hid ℓ) d ℂ) => ω ℓ) x.1.2.1 :=
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun ℓ => Matrix (hid ℓ) d ℂ) ℓ).analyticAt _
    have h2 : AnalyticAt ℂ (fun ω : CWeights d dOut hid => ω.2.1) x.1 :=
      AnalyticAt.comp (f := fun ω : CWeights d dOut hid => ω.2) analyticAt_fst analyticAt_snd
    exact AnalyticAt.comp (f := fun p : CWeights d dOut hid × Matrix T d ℂ => p.1.2.1) h1
      (AnalyticAt.comp (f := fun p : CWeights d dOut hid × Matrix T d ℂ => p.1) h2 (hfst x))
  have hD : ∀ x : CWeights d dOut hid × Matrix T d ℂ,
      AnalyticAt ℂ (fun p : CWeights d dOut hid × Matrix T d ℂ => p.1.2.2) x := by
    intro x
    have h2 : AnalyticAt ℂ (fun ω : CWeights d dOut hid => ω.2.2) x.1 :=
      AnalyticAt.comp (f := fun ω : CWeights d dOut hid => ω.2) analyticAt_snd analyticAt_snd
    exact AnalyticAt.comp (f := fun p : CWeights d dOut hid × Matrix T d ℂ => p.1) h2 (hfst x)
  -- `N` after the projection to the hidden state, where every row has `Re⟨h, h⟩ > 0`
  have hN : ∀ h : Matrix T d ℂ, (∀ t, 0 < (h t ⬝ᵥ h t).re) →
      AnalyticAt ℂ (fun p : CWeights d dOut hid × Matrix T d ℂ => rmsNormC p.2) (θ.toC, h) := by
    intro h hh
    have hc := (analyticAt_rmsNormC_cs h hh).comp
      (analyticAt_snd (𝕜 := ℂ) (p := ((θ.toC, h) : CWeights d dOut hid × Matrix T d ℂ)))
    exact hc
  induction k using Fin.reverseInduction with
  | last =>
    -- `𝓑_{>L}(h) = N(h) D` is holomorphic on `C_1`: `κ_L = 1`
    refine ⟨1, one_pos, le_rfl, fun h hh => ?_⟩
    have hpos : ∀ t, 0 < (h t ⬝ᵥ h t).re := fun t =>
      re_dotProduct_self_pos_of_mem_complexCone zero_le_one le_rfl (hh t)
    have hc : (fun p : CWeights d dOut hid × Matrix T d ℂ => suffixC σC p.1 (Fin.last L) p.2)
        = fun p => rmsNormC p.2 * p.1.2.2 := funext fun p => suffixC_last_cs σC p.1 p.2
    rw [hc]
    exact analyticAt_matrix_mul_cs (hN h hpos) (hD _)
  | cast ℓ ih =>
    obtain ⟨κ', hκ'0, -, hκ'⟩ := ih
    -- (a) by (R2), the rows at which block `ℓ + 1` is holomorphic and lands in `C_{κ'}` form a
    -- neighbourhood of every real row on the sphere `S`
    have ha : ∀ n₀ : d → ℝ, n₀ ⬝ᵥ n₀ = (Fintype.card d : ℝ) →
        {v : d → ℂ | (∀ j, AnalyticAt ℂ σC ((v ᵥ* θ.toC.1 ℓ) j)) ∧
          (fun j => σC ((v ᵥ* θ.toC.1 ℓ) j)) ᵥ* θ.toC.2.1 ℓ ∈ complexCone κ'}
          ∈ nhds (fun i => (n₀ i : ℂ)) := by
      intro n₀ hn₀
      refine goodRow_mem_nhds_cs hσ hσC (θ.read ℓ) (θ.write ℓ) hκ'0 n₀ ?_
      have h2 := hθ.block_ne_zero ℓ (Matrix.of fun _ => n₀) (fun _ => hn₀) t₀
      rw [Matrix.mul_apply_eq_vecMul] at h2
      exact h2
    -- (b) there is a `κ` such that `N` maps `C_κ` into these rows
    obtain ⟨δ, hδ, hδO⟩ := exists_delta_cs _ ha
    refine ⟨min 1 δ, lt_min one_pos hδ, min_le_left _ _, fun h hh => ?_⟩
    have hpos : ∀ t, 0 < (h t ⬝ᵥ h t).re := fun t =>
      re_dotProduct_self_pos_of_mem_complexCone (lt_min one_pos hδ).le (min_le_left _ _) (hh t)
    have hr : ∀ t, (∀ j, AnalyticAt ℂ σC ((rmsNormC h t ᵥ* θ.toC.1 ℓ) j)) ∧
        (fun j => σC ((rmsNormC h t ᵥ* θ.toC.1 ℓ) j)) ᵥ* θ.toC.2.1 ℓ ∈ complexCone κ' :=
      fun t => rmsRowC_mem_of_cone_cs _ hδ hδO (h t) (hh t)
    -- (c) `𝓑_{>ℓ} = 𝓑_{>ℓ+1} ∘ g_{ℓ+1} ∘ N` is a composition of holomorphic maps
    have hF : AnalyticAt ℂ (fun p : CWeights d dOut hid × Matrix T d ℂ =>
        rmsNormC p.2 * p.1.1 ℓ) (θ.toC, h) :=
      analyticAt_matrix_mul_cs (hN h hpos) (hread ℓ _)
    have hG : AnalyticAt ℂ (fun p : CWeights d dOut hid × Matrix T d ℂ =>
        (rmsNormC p.2 * p.1.1 ℓ).map σC * p.1.2.1 ℓ) (θ.toC, h) := by
      refine analyticAt_matrix_mul_cs (analyticAt_map_cs hF fun t j => ?_) (hwrite ℓ _)
      show AnalyticAt ℂ σC ((rmsNormC h * θ.toC.1 ℓ) t j)
      rw [Matrix.mul_apply_eq_vecMul]
      exact (hr t).1 j
    have hval : ∀ t, ((rmsNormC h * θ.toC.1 ℓ).map σC * θ.toC.2.1 ℓ) t ∈ complexCone κ' :=
      fun t => (hr t).2
    have hB := hκ' _ hval
    have hc := hB.comp_of_eq ((hfst _).prod hG) rfl
    have heq : (fun p : CWeights d dOut hid × Matrix T d ℂ => suffixC σC p.1 ℓ.castSucc p.2)
        = (fun q : CWeights d dOut hid × Matrix T d ℂ => suffixC σC q.1 ℓ.succ q.2) ∘
          (fun p => (p.1, (rmsNormC p.2 * p.1.1 ℓ).map σC * p.1.2.1 ℓ)) :=
      funext fun p => suffixC_castSucc_cs σC p.1 ℓ p.2
    rw [heq]
    exact hc

omit [DecidableEq d] [Fintype dIn] in
/-- The cones of Lemma D.14 may be shrunk: `HolomorphicOnCone` for `κ` gives it for every
`0 ≤ κ' ≤ κ`. -/
theorem HolomorphicOnCone.mono {σ : ℝ → ℝ} {σC : ℂ → ℂ}
    {θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut} {k : Fin (L + 1)}
    {κ κ' : ℝ} (h : HolomorphicOnCone σC θ k κ) (hκ' : 0 ≤ κ') (hle : κ' ≤ κ) :
    HolomorphicOnCone σC θ k κ' := by
  exact fun h' hh => h h' fun t => complexCone_mono hκ' hle (hh t)

end Skips
