import SkipsLean.OneBlock.UnitsTanh
import SkipsLean.OneBlock.UnitsGELU
import SkipsLean.Activations.Analytic
import SkipsLean.OneBlock.UnitsReLU

/-!
# Step 4 of the proof of Theorem B.1 (iii) for tanh and GELU units: `X_s = 0`

Paper (skips paper), proof of Theorem B.1 (iii), Step 4: "The change `n X_s` of the input moves
the block as the entries `X_s W_read` at `W_read` do […] So, with `ψ` the entries of `η′` at the
weights of the block plus these,

`∂_ψ B(n) = q(n) 𝐃B(n) n` (17)

for every `n` in the image of `N_ε`, the open ball of radius `√d_model`" (with
`q(n) = n X_s nᵀ / d_model`, `X_s` symmetric), and then: "For the other blocks both sides are
analytic in `n`, so (17) holds for all `n`, and we
take `n = t n̂` with a fixed row `n̂` and `t → ∞`, as in the proof of Lemma B.3. For GELU the right
side is `t³ q(n̂) max(n̂ W_read, 0) W_write` up to terms that decay faster than any power of `t`,
and the left side is a polynomial of degree at most one in `t` up to such terms, so
`q(n̂) max(n̂ W_read, 0) W_write = 0`. […] For tanh the right side is
`4 t³ q(n̂) ∑_i (n̂ c_i) e^{−2|n̂ c_i| t} a_i` up to terms `O(t³ e^{−4|n̂ c_i| t})`; for the unit
`j` with the smallest `|n̂ c_j|`, the left side contributes a polynomial of degree one times
`e^{−2|n̂ c_j| t}` (proof of Lemma B.3), so `q(n̂)(n̂ c_j) a_j = 0`. […] In every case `q` vanishes
on an open set for generic parameters, so `X_s = 0`."

Here this step as a statement on vectors, with no network in it (a twin of Lemma B.3,
`UnitsRigid` in `OneBlock/Mlp.lean`, with the multiple `q(n) 𝐃B(n) n` on the right side in place
of `0`; the twin for positively homogeneous units and `ε = 0` is `UnitsRescaleSphere`). For units
`σ(x c_i) a_i`, `B(x) = ∑_i σ(x c_i) a_i`: with `ψc_i = X_s c_i + (ψ_read)_i` and `ψa = ψ_write`,
and with `X = X_s / d_model`, equation (17) reads

`∑_i [σ(x c_i) ψa_i + σ'(x c_i) (x ψc_i) a_i] = (x X xᵀ) ∑_i σ'(x c_i) (x c_i) a_i`.

The statement asks it on a nonempty open set of rows `x` (the paper: the ball) and concludes
`X = 0`, for at least one unit, nonzero rows `a_i`, and nonzero, pairwise non-collinear columns
`c_i` (the hypotheses of Lemma B.3; they hold at generic parameters). **No width is asked:** the
number of units and of coordinates are independent. Numeric check at 60 digits, also with fewer
units than coordinates: `units_no_symmetric_part_check_2026-11-24.py` (24 cases).
-/

namespace Skips

open Matrix
open Filter Topology

/-- **Step 4 of the proof of Theorem B.1 (iii) of the skips paper, as a property of an activation
`σ` with derivative `σ'`:** for units `σ(x c_i) a_i` with nonzero rows `a_i` and nonzero, pairwise
non-collinear columns `c_i`, a symmetric `X` and a direction `(ψc, ψa)`: if
`∑_i [σ(x c_i) ψa_i + σ'(x c_i) (x ψc_i) a_i] = (x X xᵀ) ∑_i σ'(x c_i) (x c_i) a_i` at every `x`
of a nonempty open set, then `X = 0`. Rows of the input are indexed by `n`, the coordinates of the
output by `k`, the hidden units by `q`. -/
def UnitsNoSymmetricPart (σ σ' : ℝ → ℝ) (n k q : Type*) [Fintype n] [Fintype k] [Fintype q] :
    Prop :=
  ∀ (c : q → n → ℝ) (a : q → k → ℝ) (X : Matrix n n ℝ) (ψc : q → n → ℝ) (ψa : q → k → ℝ)
    (O : Set (n → ℝ)),
    (∀ i, a i ≠ 0) → (∀ i, c i ≠ 0) → (∀ i j, i ≠ j → ∀ r : ℝ, c i ≠ r • c j) → Xᵀ = X →
    IsOpen O → O.Nonempty →
    (∀ x ∈ O, ∑ i, (σ (x ⬝ᵥ c i) • ψa i + (σ' (x ⬝ᵥ c i) * (x ⬝ᵥ ψc i)) • a i)
      = ((x ᵥ* X) ⬝ᵥ x) • ∑ i, (σ' (x ⬝ᵥ c i) * (x ⬝ᵥ c i)) • a i) →
    X = 0

/-- **Polarization.** A symmetric `X` whose quadratic form `e X eᵀ` vanishes is `0`. -/
private lemma eq_zero_of_quad_uns {n : Type*} [Fintype n] (X : Matrix n n ℝ) (hX : Xᵀ = X)
    (h : ∀ e : n → ℝ, (e ᵥ* X) ⬝ᵥ e = 0) : X = 0 := by
  classical
  -- the bilinear form `B(u, v) = (u X) vᵀ` is symmetric
  have hsym : ∀ u v : n → ℝ, (v ᵥ* X) ⬝ᵥ u = (u ᵥ* X) ⬝ᵥ v := fun u v => by
    rw [← dotProduct_mulVec, dotProduct_comm, ← hX, vecMul_transpose, hX]
  have hB : ∀ u v : n → ℝ, (u ᵥ* X) ⬝ᵥ v = 0 := fun u v => by
    have e := h (u + v)
    simp only [add_vecMul, add_dotProduct, dotProduct_add, h u, h v, hsym u v] at e
    linarith
  ext i j
  have := hB (Pi.single i 1) (Pi.single j 1)
  simpa [vecMul, dotProduct, Pi.single_apply] using this

/-- **`X = 0` from the quadratic form near one point.** If `X` is symmetric and, for every `e`,
`(ν + ε e) X (ν + ε e)ᵀ = 0` for all small `ε`, then `X = 0`: the values at `ε`, `-ε` and `0`
give `ε² e X eᵀ = 0`. -/
private lemma eq_zero_of_line_uns {n : Type*} [Fintype n] (X : Matrix n n ℝ) (hX : Xᵀ = X)
    (ν : n → ℝ)
    (h : ∀ e : n → ℝ, ∀ᶠ ε in 𝓝 (0 : ℝ), ((ν + ε • e) ᵥ* X) ⬝ᵥ (ν + ε • e) = 0) :
    X = 0 := by
  refine eq_zero_of_quad_uns X hX fun e => ?_
  have h0 := (h e).self_of_nhds
  have hneg : ∀ᶠ ε in 𝓝 (0 : ℝ), ((ν + (-ε) • e) ᵥ* X) ⬝ᵥ (ν + (-ε) • e) = 0 := by
    have ht : Tendsto (fun ε : ℝ => -ε) (𝓝 0) (𝓝 0) := by
      simpa using (continuous_neg.tendsto (0 : ℝ))
    exact ht.eventually (h e)
  obtain ⟨ε, ⟨h1, h2⟩, hε⟩ := (((h e).and hneg).filter_mono nhdsWithin_le_nhds |>.and
    (self_mem_nhdsWithin (s := ({0}ᶜ : Set ℝ)))).exists
  simp only [zero_smul, add_zero] at h0
  simp only [add_vecMul, smul_vecMul, add_dotProduct, dotProduct_add, smul_dotProduct,
    dotProduct_smul, smul_eq_mul, h0] at h1 h2
  have hε' : ε ≠ 0 := hε
  have : ε ^ 2 * ((e ᵥ* X) ⬝ᵥ e) = 0 := by linear_combination (h1 + h2) / 2
  exact (mul_eq_zero.1 this).resolve_left (pow_ne_zero 2 hε')

/-- **From the open set to every `x`.** Both sides of the identity are real-analytic in `x` when
`σ` and `σ'` are, and `n → ℝ` is connected: the identity on a nonempty open set holds at every
`x` (the identity theorem, in each output coordinate). -/
private lemma forall_of_open_uns {n k q : Type*} [Fintype n] [Fintype k] [Fintype q]
    {σ σ' : ℝ → ℝ} (hσ : ∀ z, AnalyticAt ℝ σ z) (hσ' : ∀ z, AnalyticAt ℝ σ' z)
    (c : q → n → ℝ) (a : q → k → ℝ) (X : Matrix n n ℝ) (ψc : q → n → ℝ) (ψa : q → k → ℝ)
    (O : Set (n → ℝ)) (hO : IsOpen O) (hne : O.Nonempty)
    (h : ∀ x ∈ O, ∑ i, (σ (x ⬝ᵥ c i) • ψa i + (σ' (x ⬝ᵥ c i) * (x ⬝ᵥ ψc i)) • a i)
      = ((x ᵥ* X) ⬝ᵥ x) • ∑ i, (σ' (x ⬝ᵥ c i) * (x ⬝ᵥ c i)) • a i) (x : n → ℝ) :
    ∑ i, (σ (x ⬝ᵥ c i) • ψa i + (σ' (x ⬝ᵥ c i) * (x ⬝ᵥ ψc i)) • a i)
      = ((x ᵥ* X) ⬝ᵥ x) • ∑ i, (σ' (x ⬝ᵥ c i) * (x ⬝ᵥ c i)) • a i := by
  obtain ⟨x₀, hx₀⟩ := hne
  funext o
  -- the coordinate `o` of the difference of the two sides is real-analytic in `x`
  have hp : ∀ (m : n) (y : n → ℝ), AnalyticAt ℝ (fun x : n → ℝ => x m) y := fun m y =>
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : n => ℝ) m).analyticAt y
  have hd : ∀ (v : n → ℝ) (y : n → ℝ), AnalyticAt ℝ (fun x : n → ℝ => x ⬝ᵥ v) y := fun v y => by
    show AnalyticAt ℝ (fun x : n → ℝ => ∑ m, x m * v m) y
    exact Finset.analyticAt_fun_sum _ fun m _ => (hp m y).fun_mul analyticAt_const
  have hq : ∀ y : n → ℝ, AnalyticAt ℝ (fun x : n → ℝ => (x ᵥ* X) ⬝ᵥ x) y := fun y => by
    show AnalyticAt ℝ (fun x : n → ℝ => ∑ m, (∑ l, x l * X l m) * x m) y
    exact Finset.analyticAt_fun_sum _ fun m _ =>
      (Finset.analyticAt_fun_sum _ fun l _ => (hp l y).fun_mul analyticAt_const).fun_mul (hp m y)
  have hs : ∀ (f : ℝ → ℝ), (∀ z, AnalyticAt ℝ f z) → ∀ (v : n → ℝ) (y : n → ℝ),
      AnalyticAt ℝ (fun x : n → ℝ => f (x ⬝ᵥ v)) y := fun f hf v y =>
    (hf _).comp (hd v y)
  have hg : AnalyticOnNhd ℝ (fun x : n → ℝ =>
      ∑ i, (σ (x ⬝ᵥ c i) * ψa i o + σ' (x ⬝ᵥ c i) * (x ⬝ᵥ ψc i) * a i o)
        - (x ᵥ* X) ⬝ᵥ x * ∑ i, σ' (x ⬝ᵥ c i) * (x ⬝ᵥ c i) * a i o) Set.univ := fun y _ => by
    have h1 := hs σ hσ
    have h2 := hs σ' hσ'
    have h3 := hd
    have h4 := hq
    fun_prop
  -- it vanishes near a point of `O`
  have hz : (fun x : n → ℝ =>
      ∑ i, (σ (x ⬝ᵥ c i) * ψa i o + σ' (x ⬝ᵥ c i) * (x ⬝ᵥ ψc i) * a i o)
        - (x ᵥ* X) ⬝ᵥ x * ∑ i, σ' (x ⬝ᵥ c i) * (x ⬝ᵥ c i) * a i o) =ᶠ[𝓝 x₀] 0 := by
    filter_upwards [hO.mem_nhds hx₀] with y hy
    have e := congrFun (h y hy) o
    simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e
    rw [Pi.zero_apply, e, sub_self]
  have := hg.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
    (Set.mem_univ x₀) hz (Set.mem_univ x)
  simp only [Pi.zero_apply] at this
  simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  linarith

/-- Strict inequalities `u_j < |u_i|` (`i ≠ j`) persist under a small perturbation `u + ε d` (copy
of the twin in `OneBlock/UnitsTanh.lean`). -/
private lemma eventually_lt_abs_uns {q : Type*} [Finite q] (u d : q → ℝ) (j : q)
    (h : ∀ i, i ≠ j → u j < |u i|) :
    ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ i, i ≠ j → u j + ε * d j < |u i + ε * d i| := by
  refine Filter.eventually_all.2 fun i => ?_
  by_cases hi : i = j
  · exact Filter.Eventually.of_forall fun _ h' => absurd hi h'
  · have : ∀ᶠ ε in 𝓝 (0 : ℝ), u j + ε * d j < |u i + ε * d i| :=
      ContinuousAt.eventually_lt (by fun_prop) (by fun_prop) (by simpa using h i hi)
    exact this.mono fun _ h' _ => h'

/-- The good directions for unit `j` (`0 < ν c_j < |ν c_i|` for `i ≠ j`) form an open set: from a
good `ν`, the direction `ν + ε e` is good for all small `ε` (copy of the twin). -/
private lemma eventually_good_uns {n q : Type*} [Fintype n] [Finite q] (c : q → n → ℝ) (j : q)
    (ν e : n → ℝ) (hν : 0 < ν ⬝ᵥ c j ∧ ∀ i, i ≠ j → ν ⬝ᵥ c j < |ν ⬝ᵥ c i|) :
    ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < (ν + ε • e) ⬝ᵥ c j ∧
      ∀ i, i ≠ j → (ν + ε • e) ⬝ᵥ c j < |(ν + ε • e) ⬝ᵥ c i| := by
  have h1 : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < ν ⬝ᵥ c j + ε * (e ⬝ᵥ c j) :=
    ContinuousAt.eventually_lt (f := fun _ => (0 : ℝ)) (by fun_prop) (by fun_prop)
      (by simpa using hν.1)
  have h2 := eventually_lt_abs_uns (fun i => ν ⬝ᵥ c i) (fun i => e ⬝ᵥ c i) j hν.2
  filter_upwards [h1, h2] with ε h1 h2
  simp only [add_dotProduct, smul_dotProduct, smul_eq_mul]
  exact ⟨h1, h2⟩

/-- **A good direction exists** for every unit `j`: a `ν` with `0 < ν c_j < |ν c_i|` for all
`i ≠ j` (copy of the twin). First a `ν₀` with `ν₀ c_j = 0` and `ν₀ c_i ≠ 0` for `i ≠ j` (a real
vector space is not a finite union of proper subspaces), then `ν = ν₀ + δ c_j` for a small
`δ > 0`. -/
private lemma exists_good_uns {n q : Type*} [Fintype n] [Fintype q] (c : q → n → ℝ)
    (hc : ∀ i, c i ≠ 0) (hcol : ∀ i j, i ≠ j → ∀ r : ℝ, c i ≠ r • c j) (j : q) :
    ∃ ν : n → ℝ, 0 < ν ⬝ᵥ c j ∧ ∀ i, i ≠ j → ν ⬝ᵥ c j < |ν ⬝ᵥ c i| := by
  have hjj : 0 < c j ⬝ᵥ c j :=
    lt_of_le_of_ne (Finset.sum_nonneg fun m _ => mul_self_nonneg (c j m))
      (Ne.symm (dotProduct_self_eq_zero.not.2 (hc j)))
  -- `r i`: the component of `c i` orthogonal to `c j`; it is nonzero for `i ≠ j`
  set r : q → n → ℝ := fun i => c i - ((c j ⬝ᵥ c i) / (c j ⬝ᵥ c j)) • c j with hr_def
  have hr : ∀ i, i ≠ j → r i ≠ 0 := fun i hi h0 =>
    hcol i j hi _ (sub_eq_zero.1 h0)
  -- the kernels of `ν ↦ ν r_i` are proper subspaces, so some `ν` avoids all of them
  let K : {i // i ≠ j} → Submodule ℝ (n → ℝ) := fun i =>
    { carrier := {ν | ν ⬝ᵥ r i = 0}
      add_mem' := fun {x y} hx hy => by
        simp only [Set.mem_ofPred_eq] at hx hy ⊢; rw [add_dotProduct, hx, hy, add_zero]
      zero_mem' := by simp
      smul_mem' := fun s x hx => by
        simp only [Set.mem_ofPred_eq] at hx ⊢; rw [smul_dotProduct, hx, smul_zero] }
  obtain ⟨ν, hν⟩ : ∃ ν : n → ℝ, ∀ i, i ≠ j → ν ⬝ᵥ r i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨i, hi⟩ := Subspace.exists_eq_top_of_iUnion_eq_univ (p := K) (by
      ext ν
      simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
      obtain ⟨i, hij, h0⟩ := hcon ν
      exact ⟨⟨i, hij⟩, h0⟩)
    have hmem : r i ∈ K i := hi ▸ Submodule.mem_top
    exact hr i.1 i.2 (dotProduct_self_eq_zero.1 hmem)
  -- `ν₀ = ν - (ν c_j / c_j c_j) c_j` lies on the hyperplane `ν₀ c_j = 0`, and `ν₀ c_i = ν r_i`
  set ν₀ := ν - ((ν ⬝ᵥ c j) / (c j ⬝ᵥ c j)) • c j with hν₀
  have h0j : ν₀ ⬝ᵥ c j = 0 := by
    rw [hν₀, sub_dotProduct, smul_dotProduct, smul_eq_mul]
    field_simp
    ring
  have h0i : ∀ i, i ≠ j → 0 < |ν₀ ⬝ᵥ c i| := fun i hi => by
    refine abs_pos.2 ?_
    have : ν₀ ⬝ᵥ c i = ν ⬝ᵥ r i := by
      rw [hν₀, hr_def]
      simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul]
      ring
    rw [this]; exact hν i hi
  -- move a little to the side of `c_j`
  have hev := eventually_lt_abs_uns (fun i => ν₀ ⬝ᵥ c i) (fun i => c j ⬝ᵥ c i) j
    (fun i hi => by simpa only [h0j] using h0i i hi)
  obtain ⟨δ, hδ, hδ0⟩ :=
    ((hev.filter_mono nhdsWithin_le_nhds).and (eventually_mem_nhdsWithin (s := Set.Ioi 0))).exists
  refine ⟨ν₀ + δ • c j, ?_, fun i hi => ?_⟩
  · rw [add_dotProduct, smul_dotProduct, smul_eq_mul, h0j, zero_add]
    exact mul_pos hδ0 hjj
  · simpa only [add_dotProduct, smul_dotProduct, smul_eq_mul] using hδ i hi

/-- `tanh z - 1 = -2 e^{-2z} / (1 + e^{-2z})` (copy of the twin in `OneBlock/UnitsTanh.lean`). -/
private lemma tanh_sub_one_eq_uns (z : ℝ) :
    Real.tanh z - 1 = -2 * Real.exp (-2 * z) / (1 + Real.exp (-2 * z)) := by
  have h1 : Real.exp (-2 * z) = Real.exp (-z) * Real.exp (-z) := by
    rw [← Real.exp_add]; ring_nf
  have h2 : Real.exp z * Real.exp (-z) = 1 := by rw [← Real.exp_add]; simp
  have hx := Real.exp_pos z
  have hy := Real.exp_pos (-z)
  rw [Real.tanh_eq, h1]
  field_simp
  linear_combination (2 * Real.exp (-z)) * h2

/-- `1 - tanh² z = 4 e^{-2z} / (1 + e^{-2z})²` (copy of the twin). -/
private lemma one_sub_tanh_sq_eq_uns (z : ℝ) :
    1 - Real.tanh z ^ 2 = 4 * Real.exp (-2 * z) / (1 + Real.exp (-2 * z)) ^ 2 := by
  have hT : Real.tanh z = 1 + -2 * Real.exp (-2 * z) / (1 + Real.exp (-2 * z)) := by
    rw [← tanh_sub_one_eq_uns]; ring
  have hE : 0 < 1 + Real.exp (-2 * z) := by positivity
  rw [hT]
  field_simp
  ring

/-- `e^{μ t} → 0` for `μ < 0` (copy of the twin). -/
private lemma tendsto_exp_mul_of_neg_uns {μ : ℝ} (hμ : μ < 0) :
    Tendsto (fun t => Real.exp (μ * t)) atTop (𝓝 0) := by
  have := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 (-μ) (by linarith)
  simpa using this

/-- For `u > 0`: if `g t e^{(μ - 2u) t} → ℓ`, then `g t e^{μ t} (tanh(t u + b) - 1)` and
`g t e^{μ t} (1 - tanh²(t u + b))` tend to `-2 e^{-2b} ℓ` and `4 e^{-2b} ℓ` (copy of the twin). -/
private lemma tanh_limits_pos_uns {u : ℝ} (hu : 0 < u) (b μ ℓ : ℝ) (g : ℝ → ℝ)
    (hg : Tendsto (fun t => g t * Real.exp ((μ - 2 * u) * t)) atTop (𝓝 ℓ)) :
    Tendsto (fun t => g t * Real.exp (μ * t) * (Real.tanh (t * u + b) - 1)) atTop
        (𝓝 (-2 * Real.exp (-2 * b) * ℓ)) ∧
      Tendsto (fun t => g t * Real.exp (μ * t) * (1 - Real.tanh (t * u + b) ^ 2)) atTop
        (𝓝 (4 * Real.exp (-2 * b) * ℓ)) := by
  -- `E t = e^{-2(t u + b)} → 0`
  have hE : Tendsto (fun t => Real.exp (-2 * (t * u + b))) atTop (𝓝 0) := by
    have h := (tendsto_exp_mul_of_neg_uns (μ := -2 * u) (by linarith)).const_mul
      (Real.exp (-2 * b))
    rw [mul_zero] at h
    refine h.congr fun t => ?_
    rw [← Real.exp_add]; ring_nf
  have h1E : Tendsto (fun t => 1 + Real.exp (-2 * (t * u + b))) atTop (𝓝 1) := by
    simpa using hE.const_add 1
  -- `e^{μ t} E t = e^{-2b} e^{(μ - 2u) t}`
  have key : ∀ t, Real.exp (μ * t) * Real.exp (-2 * (t * u + b))
      = Real.exp (-2 * b) * Real.exp ((μ - 2 * u) * t) := fun t => by
    rw [← Real.exp_add, ← Real.exp_add]; ring_nf
  constructor
  · have h := ((hg.const_mul (-2 * Real.exp (-2 * b)))).div h1E one_ne_zero
    rw [div_one] at h
    refine h.congr fun t => ?_
    rw [Pi.div_apply, tanh_sub_one_eq_uns]
    calc _ = -2 * g t * (Real.exp (-2 * b) * Real.exp ((μ - 2 * u) * t))
          / (1 + Real.exp (-2 * (t * u + b))) := by ring
      _ = _ := by rw [← key t]; ring
  · have h := ((hg.const_mul (4 * Real.exp (-2 * b)))).div (h1E.pow 2) (by norm_num)
    rw [one_pow, div_one] at h
    refine h.congr fun t => ?_
    rw [Pi.div_apply, one_sub_tanh_sq_eq_uns]
    calc _ = 4 * g t * (Real.exp (-2 * b) * Real.exp ((μ - 2 * u) * t))
          / (1 + Real.exp (-2 * (t * u + b))) ^ 2 := by ring
      _ = _ := by rw [← key t]; ring

/-- For `u ≠ 0`: if `g t e^{(μ - 2|u|) t} → 0`, then `g t e^{μ t} (tanh(t u + b) - sign u) → 0`
and `g t e^{μ t} (1 - tanh²(t u + b)) → 0` (copy of the twin). -/
private lemma tanh_limits_zero_uns {u : ℝ} (hu : u ≠ 0) (b μ : ℝ) (g : ℝ → ℝ)
    (hg : Tendsto (fun t => g t * Real.exp ((μ - 2 * |u|) * t)) atTop (𝓝 0)) :
    Tendsto (fun t => g t * Real.exp (μ * t) * (Real.tanh (t * u + b) - Real.sign u)) atTop
        (𝓝 0) ∧
      Tendsto (fun t => g t * Real.exp (μ * t) * (1 - Real.tanh (t * u + b) ^ 2)) atTop
        (𝓝 0) := by
  rcases hu.lt_or_gt with hneg | hpos
  · -- `u < 0`: `tanh (t u + b) = -tanh (t (-u) + (-b))`
    rw [abs_of_neg hneg] at hg
    obtain ⟨h1, h2⟩ := tanh_limits_pos_uns (neg_pos.2 hneg) (-b) μ 0 g hg
    rw [mul_zero] at h1 h2
    have hodd : ∀ t, Real.tanh (t * u + b) = -Real.tanh (t * -u + -b) := fun t => by
      rw [← Real.tanh_neg]; congr 1; ring
    constructor
    · have h1' := h1.neg
      rw [neg_zero] at h1'
      refine h1'.congr fun t => ?_
      rw [Real.sign_of_neg hneg, hodd t]; ring
    · refine h2.congr fun t => ?_
      rw [hodd t]; ring
  · rw [abs_of_pos hpos] at hg
    obtain ⟨h1, h2⟩ := tanh_limits_pos_uns hpos b μ 0 g hg
    rw [mul_zero] at h1 h2
    rw [Real.sign_of_pos hpos]
    exact ⟨h1, h2⟩

/-- `t^m e^{-a t} → 0` for `a > 0`, as a natural power. -/
private lemma tendsto_pow_mul_exp_uns (m : ℕ) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun t : ℝ => t ^ m * Real.exp (-a * t)) atTop (𝓝 0) := by
  have := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (m : ℝ) a ha
  refine this.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with t ht
  rw [Real.rpow_natCast]

/-- **The ray argument for tanh**, in one output coordinate. Along the ray `x = t ν` the identity
reads `∑ᵢ [tanh(t uᵢ) Aᵢ + (1 - tanh²(t uᵢ)) t wᵢ aᵢ] = t² Q ∑ᵢ (1 - tanh²(t uᵢ)) t uᵢ aᵢ`. If
`u_j > 0` and `u_j < |u_i|` for all `i ≠ j`, then `Q u_j a_j = 0`: the constant
`∑ᵢ sign(uᵢ) Aᵢ` vanishes, and after it the left side is `O(t e^{-2 u_j t})` while the right side
is `4 t³ Q u_j a_j e^{-2 u_j t}` up to `o(t³ e^{-2 u_j t})`. -/
private lemma ray_tanh_uns {q : Type*} [Fintype q] [DecidableEq q] (u w A a : q → ℝ) (Q : ℝ)
    (j : q) (hj : 0 < u j) (hk : ∀ i, i ≠ j → u j < |u i|)
    (hJ : ∀ t : ℝ, ∑ i, (Real.tanh (t * u i) * A i + (1 - Real.tanh (t * u i) ^ 2) * (t * w i)
      * a i) = t * (t * Q) * ∑ i, (1 - Real.tanh (t * u i) ^ 2) * (t * u i) * a i) :
    Q * u j * a j = 0 := by
  -- every `u i` is nonzero
  have hu0 : ∀ i, u i ≠ 0 := fun i => by
    by_cases hi : i = j
    · subst hi; exact hj.ne'
    · exact abs_pos.1 (hj.trans (hk i hi))
  have hpos : ∀ i, 0 < 2 * |u i| := fun i => by have := abs_pos.2 (hu0 i); linarith
  -- limits with the weight `e^{μ t}`, `μ < 2 |u i|`: `tanh → sign`, `1 - tanh² → 0`,
  -- `t (1 - tanh²) → 0`, `t³ (1 - tanh²) → 0`
  have hdec : ∀ i μ, μ < 2 * |u i| →
      Tendsto (fun t => Real.exp (μ * t) * (Real.tanh (t * u i) - Real.sign (u i))) atTop
        (𝓝 0) ∧
      Tendsto (fun t => Real.exp (μ * t) * (1 - Real.tanh (t * u i) ^ 2)) atTop (𝓝 0) ∧
      Tendsto (fun t => t * Real.exp (μ * t) * (1 - Real.tanh (t * u i) ^ 2)) atTop (𝓝 0) ∧
      Tendsto (fun t => t ^ 3 * Real.exp (μ * t) * (1 - Real.tanh (t * u i) ^ 2)) atTop
        (𝓝 0) := fun i μ hμ => by
    have hneg : 0 < 2 * |u i| - μ := by linarith
    obtain ⟨h1, h2⟩ := tanh_limits_zero_uns (hu0 i) 0 μ (fun _ => 1) (by
      simpa [neg_mul, neg_sub] using tendsto_pow_mul_exp_uns 0 hneg)
    obtain ⟨-, h3⟩ := tanh_limits_zero_uns (hu0 i) 0 μ id (by
      simpa [neg_mul, neg_sub] using tendsto_pow_mul_exp_uns 1 hneg)
    obtain ⟨-, h4⟩ := tanh_limits_zero_uns (hu0 i) 0 μ (fun t => t ^ 3) (by
      simpa [neg_mul, neg_sub] using tendsto_pow_mul_exp_uns 3 hneg)
    simp only [one_mul, add_zero, id] at h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  -- (i) the constant `K = ∑ sign(uᵢ) Aᵢ` vanishes: the left side tends to `K`, the right to `0`
  have hL : Tendsto (fun t => ∑ i, (Real.tanh (t * u i) * A i
      + (1 - Real.tanh (t * u i) ^ 2) * (t * w i) * a i)) atTop
      (𝓝 (∑ i, Real.sign (u i) * A i)) := by
    refine tendsto_finsetSum _ fun i _ => ?_
    obtain ⟨h1, -, h3, -⟩ := hdec i 0 (hpos i)
    simp only [zero_mul, Real.exp_zero, one_mul, mul_one] at h1 h3
    have := ((h1.add_const (Real.sign (u i))).mul_const (A i)).add
      ((h3.mul_const (w i)).mul_const (a i))
    simp only [zero_add, zero_mul, add_zero, sub_add_cancel] at this
    refine this.congr fun t => ?_
    ring
  have hR : Tendsto (fun t => t * (t * Q) * ∑ i, (1 - Real.tanh (t * u i) ^ 2) * (t * u i)
      * a i) atTop (𝓝 0) := by
    have h := (tendsto_finsetSum Finset.univ fun i (_ : i ∈ Finset.univ) =>
      ((hdec i 0 (hpos i)).2.2.2.mul_const (u i * a i))).const_mul Q
    simp only [zero_mul, Finset.sum_const_zero, mul_zero, Real.exp_zero, mul_one] at h
    refine h.congr fun t => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hK : ∑ i, Real.sign (u i) * A i = 0 :=
    tendsto_nhds_unique (hL.congr fun t => hJ t) hR
  -- so `G t = ∑ᵢ [(tanh - sign uᵢ) Aᵢ + (1 - tanh²) t wᵢ aᵢ]` is the right side
  have hG : ∀ t, ∑ i, ((Real.tanh (t * u i) - Real.sign (u i)) * A i
      + (1 - Real.tanh (t * u i) ^ 2) * (t * w i) * a i)
      = t * (t * Q) * ∑ i, (1 - Real.tanh (t * u i) ^ 2) * (t * u i) * a i := fun t => by
    rw [← hJ t]
    have e : ∑ i, ((Real.tanh (t * u i) - Real.sign (u i)) * A i
        + (1 - Real.tanh (t * u i) ^ 2) * (t * w i) * a i)
        = ∑ i, (Real.tanh (t * u i) * A i + (1 - Real.tanh (t * u i) ^ 2) * (t * w i) * a i)
          - ∑ i, Real.sign (u i) * A i := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [e, hK, sub_zero]
  -- weighted limits, weight `e^{2 u_j t}`: only unit `j` survives
  have hE1 : ∀ i, Tendsto (fun t => Real.exp (2 * u j * t)
      * (Real.tanh (t * u i) - Real.sign (u i))) atTop
      (𝓝 (if i = j then -2 else 0)) := fun i => by
    split_ifs with hi
    · subst hi
      obtain ⟨h1, -⟩ := tanh_limits_pos_uns hj 0 (2 * u i) 1 (fun _ => 1) (by simp)
      rw [Real.sign_of_pos hj]
      simpa using h1
    · exact (hdec i _ (by linarith [hk i hi])).1
  have hE2 : ∀ i, Tendsto (fun t => Real.exp (2 * u j * t)
      * (1 - Real.tanh (t * u i) ^ 2)) atTop
      (𝓝 (if i = j then 4 else 0)) := fun i => by
    split_ifs with hi
    · subst hi
      obtain ⟨-, h2⟩ := tanh_limits_pos_uns hj 0 (2 * u i) 1 (fun _ => 1) (by simp)
      simpa using h2
    · exact (hdec i _ (by linarith [hk i hi])).2.1
  -- (ii) weight `e^{2 u_j t} / t³`: the left side tends to `0`, the right side to `4 Q u_j a_j`
  have hlimL : Tendsto (fun t => ∑ i, Real.exp (2 * u j * t) * t⁻¹ ^ 3
      * ((Real.tanh (t * u i) - Real.sign (u i)) * A i
        + (1 - Real.tanh (t * u i) ^ 2) * (t * w i) * a i)) atTop (𝓝 0) := by
    have hi := tendsto_inv_atTop_zero (𝕜 := ℝ)
    have h := tendsto_finsetSum Finset.univ fun i (_ : i ∈ Finset.univ) =>
      (((hi.pow 3).mul (hE1 i)).mul_const (A i)).add
        ((((hi.pow 2).mul (hE2 i)).mul_const (w i)).mul_const (a i))
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul, add_zero,
      Finset.sum_const_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with t ht
    refine Finset.sum_congr rfl fun i _ => ?_
    have ht' := ht.ne'
    field_simp
  have hlimR : Tendsto (fun t => ∑ i, Real.exp (2 * u j * t) * t⁻¹ ^ 3
      * ((Real.tanh (t * u i) - Real.sign (u i)) * A i
        + (1 - Real.tanh (t * u i) ^ 2) * (t * w i) * a i)) atTop
      (𝓝 (Q * ∑ i, (if i = j then 4 else 0) * (u i * a i))) := by
    have h := (tendsto_finsetSum Finset.univ fun i (_ : i ∈ Finset.univ) =>
      ((hE2 i).mul_const (u i * a i))).const_mul Q
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with t ht
    rw [← Finset.mul_sum, hG t, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have ht' := ht.ne'
    field_simp
  have h := tendsto_nhds_unique hlimR hlimL
  rw [Finset.sum_eq_single j (fun i _ hi => by simp [hi]) (by simp)] at h
  simp only [ite_true] at h
  linear_combination h / 4

/-- **Step 4 for tanh units** (at least one unit): on a ray `x = t n̂` with distinct nonzero
`|n̂ c_i|`, the term of order `t³ e^{−2|n̂ c_j| t}`, for the unit `j` with the smallest `|n̂ c_j|`,
gives `(n̂ X n̂ᵀ)(n̂ c_j) a_j = 0`. -/
theorem tanh_unitsNoSymmetricPart (n k q : Type*) [Fintype n] [Fintype k] [Fintype q]
    [Nonempty q] : UnitsNoSymmetricPart Real.tanh (fun z => 1 - Real.tanh z ^ 2) n k q := by
  classical
  intro c a X ψc ψa O ha hc hcol hX hO hne h
  -- (17) holds at every `x`: both sides are real-analytic in `x`
  have hall := forall_of_open_uns (σ := Real.tanh) (σ' := fun z => 1 - Real.tanh z ^ 2)
    (fun z => analyticOnNhd_tanh z (Set.mem_univ z))
    (fun z => by have := analyticOnNhd_tanh z (Set.mem_univ z); fun_prop) c a X ψc ψa O hO hne h
  -- on the ray `x = t ν`, `ν` good for unit `j`: `(ν X νᵀ)(ν c_j) a_j = 0`, so `ν X νᵀ = 0`
  obtain ⟨j⟩ := ‹Nonempty q›
  have hzero : ∀ ν : n → ℝ, (0 < ν ⬝ᵥ c j ∧ ∀ i, i ≠ j → ν ⬝ᵥ c j < |ν ⬝ᵥ c i|) →
      (ν ᵥ* X) ⬝ᵥ ν = 0 := fun ν hν => by
    obtain ⟨o, ho⟩ := Function.ne_iff.1 (ha j)
    rw [Pi.zero_apply] at ho
    have e := ray_tanh_uns (fun i => ν ⬝ᵥ c i) (fun i => ν ⬝ᵥ ψc i) (fun i => ψa i o)
      (fun i => a i o) ((ν ᵥ* X) ⬝ᵥ ν) j hν.1 hν.2 (fun t => by
        simpa only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, smul_vecMul,
          smul_dotProduct, dotProduct_smul] using congrFun (hall (t • ν)) o)
    rw [mul_assoc] at e
    exact (mul_eq_zero.1 e).resolve_right (mul_ne_zero hν.1.ne' ho)
  -- the good directions for unit `j` form a nonempty open set: `X = 0`
  obtain ⟨ν, hν⟩ := exists_good_uns c hc hcol j
  exact eq_zero_of_line_uns X hX ν fun e =>
    (eventually_good_uns c j ν e hν).mono fun ε hε => hzero _ hε


/-- Gaussian decay beats `t²`: for `v² < u²`, `t² e^{-(t u + b)²/2 + (t v + d)²/2} → 0` (copy of
the twin in `OneBlock/UnitsGELU.lean`). -/
private lemma tendsto_sq_mul_exp_quad_uns {u v : ℝ} (b d : ℝ) (h : v ^ 2 < u ^ 2) :
    Tendsto (fun t => t ^ 2 * Real.exp (-(t * u + b) ^ 2 / 2 + (t * v + d) ^ 2 / 2)) atTop
      (𝓝 0) := by
  -- the exponent is `-α t² + β t + γ` with `α > 0`; it is `≤ -t + γ` once `α t ≥ β + 1`
  have hα : 0 < (u ^ 2 - v ^ 2) / 2 := by linarith
  have hexp : ∀ t, -(t * u + b) ^ 2 / 2 + (t * v + d) ^ 2 / 2
      = -((u ^ 2 - v ^ 2) / 2) * t ^ 2 + (v * d - u * b) * t + (d ^ 2 - b ^ 2) / 2 :=
    fun t => by ring
  have hlim := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).const_mul
    (Real.exp ((d ^ 2 - b ^ 2) / 2))
  rw [mul_zero] at hlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun t => by positivity) ?_
  filter_upwards [eventually_ge_atTop (max 0 ((v * d - u * b + 1) / ((u ^ 2 - v ^ 2) / 2)))]
    with t ht
  have ht0 : 0 ≤ t := le_trans (le_max_left _ _) ht
  have ht1 : v * d - u * b + 1 ≤ (u ^ 2 - v ^ 2) / 2 * t := by
    have := le_trans (le_max_right _ _) ht
    rw [div_le_iff₀ hα] at this; linarith
  have hle : -((u ^ 2 - v ^ 2) / 2) * t ^ 2 + (v * d - u * b) * t + (d ^ 2 - b ^ 2) / 2
      ≤ -t + (d ^ 2 - b ^ 2) / 2 := by nlinarith
  rw [hexp, show Real.exp ((d ^ 2 - b ^ 2) / 2) * (t ^ 2 * Real.exp (-t))
    = t ^ 2 * Real.exp (-t + (d ^ 2 - b ^ 2) / 2) by rw [Real.exp_add]; ring]
  gcongr

/-- `t φ(t u) → 0` for `u ≠ 0`. -/
private lemma tendsto_mul_gaussPdf_uns {u : ℝ} (hu : u ≠ 0) :
    Tendsto (fun t => t * gaussPdf (t * u)) atTop (𝓝 0) := by
  have hd := tendsto_sq_mul_exp_quad_uns (u := u) (v := 0) 0 0
    (by rw [sq_lt_sq, abs_zero]; exact abs_pos.2 hu)
  have h := (tendsto_inv_atTop_zero.mul hd).div_const (Real.sqrt (2 * Real.pi))
  rw [zero_mul, zero_div] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  have e : -(t * u + 0) ^ 2 / 2 + (t * 0 + 0) ^ 2 / 2 = -(t * u) ^ 2 / 2 := by ring
  rw [e, gaussPdf]
  have ht' := ht.ne'
  field_simp

/-- Along a ray, `Φ(t u)` and `σ'(t u) = Φ(t u) + t u φ(t u)` tend to the same limit `ℓ`, with
`ℓ u = max(u, 0)`: `ℓ = 1` for `u > 0`, `ℓ = 0` for `u < 0`, and both are constant for `u = 0`. -/
private lemma gelu_limits_uns (u : ℝ) :
    ∃ ℓ : ℝ, Tendsto (fun t => gaussCdf (t * u)) atTop (𝓝 ℓ) ∧
      Tendsto (fun t => geluDeriv (t * u)) atTop (𝓝 ℓ) ∧ ℓ * u = max u 0 := by
  rcases lt_trichotomy u 0 with hneg | h0 | hpos
  · -- `u < 0`: `Φ(t u) → 0`
    have hΦ : Tendsto (fun t => gaussCdf (t * u)) atTop (𝓝 0) :=
      tendsto_gaussCdf_atBot.comp (Tendsto.atTop_mul_const_of_neg hneg tendsto_id)
    refine ⟨0, hΦ, ?_, by rw [zero_mul, max_eq_right hneg.le]⟩
    have h := hΦ.add ((tendsto_mul_gaussPdf_uns hneg.ne).const_mul u)
    rw [mul_zero, add_zero] at h
    refine h.congr fun t => ?_
    simp only [geluDeriv]
    ring
  · -- `u = 0`: both are constant
    subst h0
    refine ⟨gaussCdf 0, ?_, ?_, by rw [mul_zero, max_self]⟩
    · simp only [mul_zero]; exact tendsto_const_nhds
    · simp only [mul_zero, geluDeriv, zero_mul, add_zero]; exact tendsto_const_nhds
  · -- `u > 0`: `Φ(t u) → 1`
    have hΦ : Tendsto (fun t => gaussCdf (t * u)) atTop (𝓝 1) :=
      tendsto_gaussCdf_atTop.comp (tendsto_id.atTop_mul_const hpos)
    refine ⟨1, hΦ, ?_, by rw [one_mul, max_eq_left hpos.le]⟩
    have h := hΦ.add ((tendsto_mul_gaussPdf_uns hpos.ne').const_mul u)
    rw [mul_zero, add_zero] at h
    refine h.congr fun t => ?_
    simp only [geluDeriv]
    ring

/-- **The ray argument for GELU**, in one output coordinate. Along the ray `x = t ν` the identity
reads `∑ᵢ [σ(t uᵢ) Aᵢ + σ'(t uᵢ) t wᵢ aᵢ] = t² Q ∑ᵢ σ'(t uᵢ) t uᵢ aᵢ`. Divided by `t³`, the left
side tends to `0` (it is `t ∑ᵢ [uᵢ Φ(t uᵢ) Aᵢ + σ'(t uᵢ) wᵢ aᵢ]`) and the right side to
`Q ∑ᵢ max(uᵢ, 0) aᵢ`. -/
private lemma ray_gelu_uns {q : Type*} [Fintype q] (u w A a : q → ℝ) (Q : ℝ)
    (hJ : ∀ t : ℝ, ∑ i, (gelu (t * u i) * A i + geluDeriv (t * u i) * (t * w i) * a i)
      = t * (t * Q) * ∑ i, geluDeriv (t * u i) * (t * u i) * a i) :
    Q * ∑ i, max (u i) 0 * a i = 0 := by
  choose ℓ hΦ hD hℓ using fun i => gelu_limits_uns (u i)
  have hi := tendsto_inv_atTop_zero (𝕜 := ℝ)
  -- divided by `t³`, the left side tends to `0`
  have hL : Tendsto (fun t => t⁻¹ ^ 2 * ∑ i, (u i * gaussCdf (t * u i) * A i
      + geluDeriv (t * u i) * w i * a i)) atTop (𝓝 0) := by
    have h := (hi.pow 2).mul (tendsto_finsetSum Finset.univ fun i (_ : i ∈ Finset.univ) =>
      (((hΦ i).const_mul (u i)).mul_const (A i)).add (((hD i).mul_const (w i)).mul_const (a i)))
    rwa [zero_pow two_ne_zero, zero_mul] at h
  -- and the right side to `Q ∑ᵢ ℓᵢ uᵢ aᵢ`
  have hR : Tendsto (fun t => Q * ∑ i, geluDeriv (t * u i) * (u i * a i)) atTop
      (𝓝 (Q * ∑ i, ℓ i * (u i * a i))) :=
    (tendsto_finsetSum Finset.univ fun i (_ : i ∈ Finset.univ) =>
      (hD i).mul_const (u i * a i)).const_mul Q
  have hLR : ∀ t, t ≠ 0 → t⁻¹ ^ 2 * ∑ i, (u i * gaussCdf (t * u i) * A i
      + geluDeriv (t * u i) * w i * a i) = Q * ∑ i, geluDeriv (t * u i) * (u i * a i) := by
    intro t ht
    have e1 : t * ∑ i, (u i * gaussCdf (t * u i) * A i + geluDeriv (t * u i) * w i * a i)
        = t ^ 3 * (Q * ∑ i, geluDeriv (t * u i) * (u i * a i)) :=
      calc _ = ∑ i, (gelu (t * u i) * A i + geluDeriv (t * u i) * (t * w i) * a i) := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun i _ => by simp only [gelu]; ring
        _ = t * (t * Q) * ∑ i, geluDeriv (t * u i) * (t * u i) * a i := hJ t
        _ = _ := by
            rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
            exact Finset.sum_congr rfl fun i _ => by ring
    calc _ = t⁻¹ ^ 3 * (t * ∑ i, (u i * gaussCdf (t * u i) * A i
          + geluDeriv (t * u i) * w i * a i)) := by field_simp
      _ = _ := by rw [e1]; field_simp
  have h := tendsto_nhds_unique (hR.congr' ((eventually_ne_atTop 0).mono fun t ht =>
    (hLR t ht).symm)) hL
  calc _ = Q * ∑ i, ℓ i * (u i * a i) := by
        congr 1
        exact Finset.sum_congr rfl fun i _ => by rw [← hℓ i]; ring
    _ = 0 := h

/-- **Step 4 for GELU units** (at least one unit): on a ray `x = t n̂` off the hyperplanes, the
term of order `t³` gives `(n̂ X n̂ᵀ) ∑_i max(n̂ c_i, 0) a_i = 0`, and the sum is nonzero on an open
set of directions. -/
theorem gelu_unitsNoSymmetricPart (n k q : Type*) [Fintype n] [Fintype k] [Fintype q]
    [Nonempty q] : UnitsNoSymmetricPart gelu geluDeriv n k q := by
  classical
  intro c a X ψc ψa O ha hc hcol hX hO hne h
  -- (17) holds at every `x`: both sides are real-analytic in `x`
  have hall := forall_of_open_uns (σ := gelu) (σ' := geluDeriv)
    (fun z => analyticOnNhd_gelu z (Set.mem_univ z))
    (fun z => by
      have h1 := analyticOnNhd_gaussCdf z (Set.mem_univ z)
      have h2 := analyticOnNhd_gaussPdf z (Set.mem_univ z)
      show AnalyticAt ℝ (fun z => gaussCdf z + z * gaussPdf z) z
      fun_prop) c a X ψc ψa O hO hne h
  -- on the ray `x = t ν`: `(ν X νᵀ) ∑ᵢ max(ν c_i, 0) a_i = 0`, for every `ν`
  have hzero : ∀ ν : n → ℝ, ((ν ᵥ* X) ⬝ᵥ ν) • ∑ i, max (ν ⬝ᵥ c i) 0 • a i = 0 := fun ν => by
    funext o
    have e := ray_gelu_uns (fun i => ν ⬝ᵥ c i) (fun i => ν ⬝ᵥ ψc i) (fun i => ψa i o)
      (fun i => a i o) ((ν ᵥ* X) ⬝ᵥ ν) (fun t => by
        simpa only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, smul_vecMul,
          smul_dotProduct, dotProduct_smul] using congrFun (hall (t • ν)) o)
    simpa only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, Pi.zero_apply] using e
  -- the ReLU units `max(ν c_i, 0) a_i` do not cancel (Lemma C.3 for ReLU): the sum is nonzero
  -- at some `ν`
  obtain ⟨ν, hν⟩ : ∃ ν : n → ℝ, ∑ i, max (ν ⬝ᵥ c i) 0 • a i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨-, -, lam, hlam⟩ := relu_units_flat c 0 a 0 0 0 0 a ha hc hcol (fun x _ => by
      simp only [relu, vecMul_zero, Pi.zero_apply, add_zero, dotProduct_zero, mul_zero,
        zero_smul, zero_add]
      exact hcon x)
    obtain ⟨i⟩ := ‹Nonempty q›
    obtain ⟨h1, -, h3⟩ := hlam i
    have hl : lam i = 0 := by
      rw [Pi.zero_apply] at h1
      exact (smul_eq_zero.1 h1.symm).resolve_right (hc i)
    rw [hl, neg_zero, zero_smul] at h3
    exact ha i h3
  -- near `ν` the sum stays nonzero, so `ν' X ν'ᵀ = 0` on a neighbourhood of `ν`: `X = 0`
  refine eq_zero_of_line_uns X hX ν fun e => ?_
  have hcont : Continuous fun ε : ℝ => ∑ i, max ((ν + ε • e) ⬝ᵥ c i) 0 • a i := by fun_prop
  have hev := (hcont.continuousAt (x := 0)).eventually_ne
    (by simpa only [zero_smul, add_zero] using hν)
  filter_upwards [hev] with ε hε
  exact (smul_eq_zero.1 (hzero (ν + ε • e))).resolve_right hε


end Skips
