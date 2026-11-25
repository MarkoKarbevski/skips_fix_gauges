import SkipsLean.OneBlock.UnitsNoSymmetricPart
import SkipsLean.OneBlock.UnitsSwiGLU
import SkipsLean.OneBlock.UnitsGeGLU
import SkipsLean.OneBlock.UnitsReGLU

/-!
# Step 4 of the proof of Theorem B.1 (iii) for SwiGLU and GeGLU units: `X_s = 0`

Paper (skips paper), proof of Theorem B.1 (iii), Step 4, equation (17),
`∂_ψ B(n) = q(n) 𝐃B(n) n` "for every `n` in the image of `N_ε`, the open ball of radius
`√d_model`", and then: "For the other blocks both sides are analytic in `n`, so (17) holds for all
`n`, and we take `n = t n̂` with a fixed row `n̂` and `t → ∞`, as in the proof of Lemma B.3. […]
SwiGLU and GeGLU units `σ(n c_i) (n e_i) a_i` give
`2 t⁴ q(n̂) ∑_{i: n̂ c_i > 0} (n̂ c_i)(n̂ e_i) a_i` against a polynomial of degree two. […] In every
case `q` vanishes on an open set for generic parameters, so `X_s = 0`."

Here this step as a statement on vectors, the twin for gated units of `UnitsNoSymmetricPart`
(`OneBlock/UnitsNoSymmetricPart.lean`). For units `σ(x c_i) (x e_i) a_i` with gate columns `c_i`,
value columns `e_i` and rows `a_i`, `B(x) = ∑_i σ(x c_i) (x e_i) a_i`, a direction
`(ψc, ψe, ψa)` and a symmetric `X` (the paper's `X_s / d_model`), equation (17) reads

`∑_i [σ(x c_i)(x e_i) ψa_i + σ'(x c_i)(x ψc_i)(x e_i) a_i + σ(x c_i)(x ψe_i) a_i]`
`  = (x X xᵀ) ∑_i [σ'(x c_i)(x c_i)(x e_i) + σ(x c_i)(x e_i)] a_i`.

The statement asks it on a nonempty open set of rows `x` and concludes `X = 0`, for at least one
unit, nonzero rows `a_i`, nonzero and pairwise non-collinear gate columns `c_i` and nonzero value
columns `e_i` (the hypotheses of `GatedUnitsRescale`, Lemma B.3 for gated units). No width is
asked. Numeric check at 60 digits, also with fewer units than coordinates:
`gated_units_no_symmetric_part_check_2026-11-25.py` (12 cases: the solutions are the rescalings
of the values, with `X = 0`).
-/

namespace Skips

open Matrix

/-- **Step 4 of the proof of Theorem B.1 (iii) of the skips paper for gated units, as a property
of a gate activation `σ` with derivative `σ'`:** for units `σ(x c_i) (x e_i) a_i` with nonzero rows
`a_i`, nonzero and pairwise non-collinear gate columns `c_i` and nonzero value columns `e_i`, a
symmetric `X` and a direction `(ψc, ψe, ψa)`: if the derivative of `B` along the direction equals
`(x X xᵀ)` times the derivative of `B` along `x` at every `x` of a nonempty open set, then
`X = 0`. -/
def GatedUnitsNoSymmetricPart (σ σ' : ℝ → ℝ) (n k q : Type*) [Fintype n] [Fintype k]
    [Fintype q] : Prop :=
  ∀ (c e : q → n → ℝ) (a : q → k → ℝ) (X : Matrix n n ℝ) (ψc ψe : q → n → ℝ) (ψa : q → k → ℝ)
    (O : Set (n → ℝ)),
    (∀ i, a i ≠ 0) → (∀ i, c i ≠ 0) → (∀ i j, i ≠ j → ∀ r : ℝ, c i ≠ r • c j) →
    (∀ i, e i ≠ 0) → Xᵀ = X → IsOpen O → O.Nonempty →
    (∀ x ∈ O, ∑ i, ((σ (x ⬝ᵥ c i) * (x ⬝ᵥ e i)) • ψa i
        + (σ' (x ⬝ᵥ c i) * (x ⬝ᵥ ψc i) * (x ⬝ᵥ e i)) • a i
        + (σ (x ⬝ᵥ c i) * (x ⬝ᵥ ψe i)) • a i)
      = ((x ᵥ* X) ⬝ᵥ x) • ∑ i,
          (σ' (x ⬝ᵥ c i) * (x ⬝ᵥ c i) * (x ⬝ᵥ e i) + σ (x ⬝ᵥ c i) * (x ⬝ᵥ e i)) • a i) →
    X = 0

open Filter Topology

/-- **Polarization.** A symmetric `X` whose quadratic form `e X eᵀ` vanishes is `0` (a copy of the
private `eq_zero_of_quad_uns` of `OneBlock/UnitsNoSymmetricPart.lean`). -/
private lemma eq_zero_of_quad_gun {n : Type*} [Fintype n] (X : Matrix n n ℝ) (hX : Xᵀ = X)
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

/-- **`X = 0` from the quadratic form near one point** (a copy of the private
`eq_zero_of_line_uns`): if `X` is symmetric and, for every `e`, `(ν + ε e) X (ν + ε e)ᵀ = 0` for
all small `ε`, then `X = 0`. -/
private lemma eq_zero_of_line_gun {n : Type*} [Fintype n] (X : Matrix n n ℝ) (hX : Xᵀ = X)
    (ν : n → ℝ)
    (h : ∀ e : n → ℝ, ∀ᶠ ε in 𝓝 (0 : ℝ), ((ν + ε • e) ᵥ* X) ⬝ᵥ (ν + ε • e) = 0) :
    X = 0 := by
  refine eq_zero_of_quad_gun X hX fun e => ?_
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

/-- **From the open set to every `x`** (the twin of the private `forall_of_open_uns` for gated
units): both sides of the identity are real-analytic in `x` when `σ` and `σ'` are, and `n → ℝ` is
connected, so the identity on a nonempty open set holds at every `x`. -/
private lemma forall_of_open_gun {n k q : Type*} [Fintype n] [Fintype k] [Fintype q]
    {σ σ' : ℝ → ℝ} (hσ : ∀ z, AnalyticAt ℝ σ z) (hσ' : ∀ z, AnalyticAt ℝ σ' z)
    (c e : q → n → ℝ) (a : q → k → ℝ) (X : Matrix n n ℝ) (ψc ψe : q → n → ℝ) (ψa : q → k → ℝ)
    (O : Set (n → ℝ)) (hO : IsOpen O) (hne : O.Nonempty)
    (h : ∀ x ∈ O, ∑ i, ((σ (x ⬝ᵥ c i) * (x ⬝ᵥ e i)) • ψa i
        + (σ' (x ⬝ᵥ c i) * (x ⬝ᵥ ψc i) * (x ⬝ᵥ e i)) • a i
        + (σ (x ⬝ᵥ c i) * (x ⬝ᵥ ψe i)) • a i)
      = ((x ᵥ* X) ⬝ᵥ x) • ∑ i,
          (σ' (x ⬝ᵥ c i) * (x ⬝ᵥ c i) * (x ⬝ᵥ e i) + σ (x ⬝ᵥ c i) * (x ⬝ᵥ e i)) • a i)
    (x : n → ℝ) :
    ∑ i, ((σ (x ⬝ᵥ c i) * (x ⬝ᵥ e i)) • ψa i
        + (σ' (x ⬝ᵥ c i) * (x ⬝ᵥ ψc i) * (x ⬝ᵥ e i)) • a i
        + (σ (x ⬝ᵥ c i) * (x ⬝ᵥ ψe i)) • a i)
      = ((x ᵥ* X) ⬝ᵥ x) • ∑ i,
          (σ' (x ⬝ᵥ c i) * (x ⬝ᵥ c i) * (x ⬝ᵥ e i) + σ (x ⬝ᵥ c i) * (x ⬝ᵥ e i)) • a i := by
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
      ∑ i, (σ (x ⬝ᵥ c i) * (x ⬝ᵥ e i) * ψa i o
          + σ' (x ⬝ᵥ c i) * (x ⬝ᵥ ψc i) * (x ⬝ᵥ e i) * a i o
          + σ (x ⬝ᵥ c i) * (x ⬝ᵥ ψe i) * a i o)
        - (x ᵥ* X) ⬝ᵥ x * ∑ i, (σ' (x ⬝ᵥ c i) * (x ⬝ᵥ c i) * (x ⬝ᵥ e i)
          + σ (x ⬝ᵥ c i) * (x ⬝ᵥ e i)) * a i o) Set.univ := fun y _ => by
    have h1 := hs σ hσ
    have h2 := hs σ' hσ'
    have h3 := hd
    have h4 := hq
    fun_prop
  -- it vanishes near a point of `O`
  have hz : (fun x : n → ℝ =>
      ∑ i, (σ (x ⬝ᵥ c i) * (x ⬝ᵥ e i) * ψa i o
          + σ' (x ⬝ᵥ c i) * (x ⬝ᵥ ψc i) * (x ⬝ᵥ e i) * a i o
          + σ (x ⬝ᵥ c i) * (x ⬝ᵥ ψe i) * a i o)
        - (x ᵥ* X) ⬝ᵥ x * ∑ i, (σ' (x ⬝ᵥ c i) * (x ⬝ᵥ c i) * (x ⬝ᵥ e i)
          + σ (x ⬝ᵥ c i) * (x ⬝ᵥ e i)) * a i o) =ᶠ[𝓝 x₀] 0 := by
    filter_upwards [hO.mem_nhds hx₀] with y hy
    have e := congrFun (h y hy) o
    simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e
    rw [Pi.zero_apply, e, sub_self]
  have := hg.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
    (Set.mem_univ x₀) hz (Set.mem_univ x)
  simp only [Pi.zero_apply] at this
  simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  linarith

/-- **The ray argument for a gate `σ(z) = z g(z)`**, in one output coordinate. Along the ray
`x = t ν` the identity reads
`∑ᵢ [σ(t uᵢ) t wᵢ Aᵢ + σ'(t uᵢ) t pᵢ t wᵢ aᵢ + σ(t uᵢ) t sᵢ aᵢ]
  = t² Q ∑ᵢ [σ'(t uᵢ) t uᵢ t wᵢ + σ(t uᵢ) t wᵢ] aᵢ`.
If `g(t u)` and `σ'(t u)` tend to the same `ℓ` with `ℓ u = max(u, 0)`, then, divided by `t⁴`, the
left side tends to `0` and the right side to `2 Q ∑ᵢ max(uᵢ, 0) wᵢ aᵢ`. -/
private lemma ray_gated_gun {q : Type*} [Fintype q] {σ σ' g : ℝ → ℝ}
    (hσ : ∀ z, σ z = z * g z)
    (hlim : ∀ u, ∃ ℓ : ℝ, Tendsto (fun t => g (t * u)) atTop (𝓝 ℓ) ∧
      Tendsto (fun t => σ' (t * u)) atTop (𝓝 ℓ) ∧ ℓ * u = max u 0)
    (u w p s A a : q → ℝ) (Q : ℝ)
    (hJ : ∀ t : ℝ, ∑ i, (σ (t * u i) * (t * w i) * A i
        + σ' (t * u i) * (t * p i) * (t * w i) * a i + σ (t * u i) * (t * s i) * a i)
      = t * (t * Q) * ∑ i, (σ' (t * u i) * (t * u i) * (t * w i)
        + σ (t * u i) * (t * w i)) * a i) :
    Q * ∑ i, max (u i) 0 * w i * a i = 0 := by
  choose ℓ hg hD hℓ using fun i => hlim (u i)
  have hi := tendsto_inv_atTop_zero (𝕜 := ℝ)
  -- divided by `t⁴`, the left side tends to `0` (it is `t²` times a convergent sum)
  have hL : Tendsto (fun t => t⁻¹ ^ 2 * ∑ i, (u i * g (t * u i) * w i * A i
      + σ' (t * u i) * p i * w i * a i + u i * g (t * u i) * s i * a i)) atTop (𝓝 0) := by
    have h := (hi.pow 2).mul (tendsto_finsetSum Finset.univ fun i (_ : i ∈ Finset.univ) =>
      (((((hg i).const_mul (u i)).mul_const (w i)).mul_const (A i)).add
        ((((hD i).mul_const (p i)).mul_const (w i)).mul_const (a i))).add
        ((((hg i).const_mul (u i)).mul_const (s i)).mul_const (a i)))
    rwa [zero_pow two_ne_zero, zero_mul] at h
  -- and the right side to `Q ∑ᵢ (ℓᵢ uᵢ + uᵢ ℓᵢ) wᵢ aᵢ`
  have hR : Tendsto (fun t => Q * ∑ i, (σ' (t * u i) * u i * w i
      + u i * g (t * u i) * w i) * a i) atTop
      (𝓝 (Q * ∑ i, (ℓ i * u i * w i + u i * ℓ i * w i) * a i)) :=
    (tendsto_finsetSum Finset.univ fun i (_ : i ∈ Finset.univ) =>
      (((((hD i).mul_const (u i)).mul_const (w i)).add
        (((hg i).const_mul (u i)).mul_const (w i))).mul_const (a i))).const_mul Q
  -- the identity divided by `t⁴`
  have hLR : ∀ t : ℝ, t ≠ 0 → t⁻¹ ^ 2 * ∑ i, (u i * g (t * u i) * w i * A i
      + σ' (t * u i) * p i * w i * a i + u i * g (t * u i) * s i * a i)
      = Q * ∑ i, (σ' (t * u i) * u i * w i + u i * g (t * u i) * w i) * a i := by
    intro t ht
    have e1 : t ^ 2 * ∑ i, (u i * g (t * u i) * w i * A i
        + σ' (t * u i) * p i * w i * a i + u i * g (t * u i) * s i * a i)
        = t ^ 2 * (t ^ 2 * (Q * ∑ i, (σ' (t * u i) * u i * w i
          + u i * g (t * u i) * w i) * a i)) :=
      calc _ = ∑ i, (σ (t * u i) * (t * w i) * A i
            + σ' (t * u i) * (t * p i) * (t * w i) * a i + σ (t * u i) * (t * s i) * a i) := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun i _ => by rw [hσ]; ring
        _ = t * (t * Q) * ∑ i, (σ' (t * u i) * (t * u i) * (t * w i)
            + σ (t * u i) * (t * w i)) * a i := hJ t
        _ = _ := by
            rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
            exact Finset.sum_congr rfl fun i _ => by rw [hσ]; ring
    rw [mul_left_cancel₀ (pow_ne_zero 2 ht) e1, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ ht,
      one_pow, one_mul]
  have h := tendsto_nhds_unique (hR.congr' ((eventually_ne_atTop 0).mono fun t ht =>
    (hLR t ht).symm)) hL
  have e3 : Q * ∑ i, (ℓ i * u i * w i + u i * ℓ i * w i) * a i
      = 2 * (Q * ∑ i, max (u i) 0 * w i * a i) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [← hℓ i]; ring
  linarith

/-- **Step 4 for a gate `σ(z) = z g(z)`** with `σ`, `σ'` analytic and `g(t u)`, `σ'(t u)` tending
to the same `ℓ`, `ℓ u = max(u, 0)`: the core of both theorems. -/
private lemma gatedUnitsNoSymmetricPart_of_gun {n k q : Type*} [Fintype n] [Fintype k]
    [Fintype q] [Nonempty q] {σ σ' g : ℝ → ℝ} (hσa : ∀ z, AnalyticAt ℝ σ z)
    (hσa' : ∀ z, AnalyticAt ℝ σ' z) (hσ : ∀ z, σ z = z * g z)
    (hlim : ∀ u, ∃ ℓ : ℝ, Tendsto (fun t => g (t * u)) atTop (𝓝 ℓ) ∧
      Tendsto (fun t => σ' (t * u)) atTop (𝓝 ℓ) ∧ ℓ * u = max u 0) :
    GatedUnitsNoSymmetricPart σ σ' n k q := by
  classical
  intro c e a X ψc ψe ψa O ha hc hcol he hX hO hne h
  -- (17) holds at every `x`: both sides are real-analytic in `x`
  have hall := forall_of_open_gun hσa hσa' c e a X ψc ψe ψa O hO hne h
  -- on the ray `x = t ν`: `(ν X νᵀ) ∑ᵢ max(ν c_i, 0) (ν e_i) a_i = 0`, for every `ν`
  have hzero : ∀ ν : n → ℝ,
      ((ν ᵥ* X) ⬝ᵥ ν) • ∑ i, (max (ν ⬝ᵥ c i) 0 * (ν ⬝ᵥ e i)) • a i = 0 := fun ν => by
    funext o
    have e1 := ray_gated_gun hσ hlim (fun i => ν ⬝ᵥ c i) (fun i => ν ⬝ᵥ e i)
      (fun i => ν ⬝ᵥ ψc i) (fun i => ν ⬝ᵥ ψe i) (fun i => ψa i o) (fun i => a i o)
      ((ν ᵥ* X) ⬝ᵥ ν) (fun t => by
        simpa only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, smul_vecMul,
          smul_dotProduct, dotProduct_smul] using congrFun (hall (t • ν)) o)
    simpa only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, Pi.zero_apply] using e1
  -- the ReGLU units `max(ν c_i, 0) (ν e_i) a_i` do not cancel (Lemma C.3 for ReGLU, with the
  -- values `x c_i + 1` and the direction `ψe = e`): the sum is nonzero at some `ν`
  obtain ⟨ν, hν⟩ : ∃ ν : n → ℝ, ∑ i, (max (ν ⬝ᵥ c i) 0 * (ν ⬝ᵥ e i)) • a i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨-, -, lam, α, hα⟩ := relu_gated_units_flat c 0 c (fun _ => 1) a 0 0 0 0 e 0 0 ha hc
      hcol hc (fun i r hr => by
        have h2 := congrArg Prod.snd hr
        simp at h2) (fun x _ => by
        simp only [vecMul_zero, Pi.zero_apply, add_zero, zero_add, smul_zero, dotProduct_zero,
          mul_zero, zero_mul, zero_smul, relu]
        exact hcon x)
    obtain ⟨i⟩ := ‹Nonempty q›
    obtain ⟨-, -, h3, h4, -⟩ := hα i
    have h0 : α i = 0 := by simpa using h4
    rw [h0, neg_zero, zero_smul] at h3
    exact he i h3
  -- near `ν` the sum stays nonzero, so `ν' X ν'ᵀ = 0` on a neighbourhood of `ν`: `X = 0`
  refine eq_zero_of_line_gun X hX ν fun f => ?_
  have hcont : Continuous fun ε : ℝ =>
      ∑ i, (max ((ν + ε • f) ⬝ᵥ c i) 0 * ((ν + ε • f) ⬝ᵥ e i)) • a i := by fun_prop
  have hev := (hcont.continuousAt (x := 0)).eventually_ne
    (by simpa only [zero_smul, add_zero] using hν)
  filter_upwards [hev] with ε hε
  exact (smul_eq_zero.1 (hzero (ν + ε • f))).resolve_right hε

/-- `σ'(-z) = 1 - σ'(z)` for SiLU (a copy of the private `siluDeriv_neg` of
`OneBlock/UnitsSwiGLU.lean`). -/
private lemma siluDeriv_neg_gun (z : ℝ) : siluDeriv (-z) = 1 - siluDeriv z := by
  have hx := Real.exp_pos z
  simp only [siluDeriv, neg_neg, Real.exp_neg]
  field_simp
  ring

/-- The logistic function `g(z) = (1 + e^{-z})⁻¹` (SiLU is `z g(z)`) at `-z`: `1 - g(z)`. -/
private lemma logistic_neg_gun (z : ℝ) :
    (1 + Real.exp (-(-z)))⁻¹ = 1 - (1 + Real.exp (-z))⁻¹ := by
  have hx := Real.exp_pos z
  simp only [neg_neg, Real.exp_neg]
  field_simp
  ring

/-- `σ'` of SiLU is real-analytic. -/
private lemma analyticAt_siluDeriv_gun (z : ℝ) : AnalyticAt ℝ siluDeriv z := by
  have hE : AnalyticAt ℝ (fun y : ℝ => Real.exp (-y)) z := (analyticAt_id.neg).rexp'
  have hD : AnalyticAt ℝ (fun y : ℝ => 1 + Real.exp (-y)) z := analyticAt_const.fun_add hE
  show AnalyticAt ℝ (fun y => (1 + Real.exp (-y) + y * Real.exp (-y)) / (1 + Real.exp (-y)) ^ 2) z
  exact (hD.fun_add (analyticAt_id.fun_mul hE)).fun_div (hD.fun_pow 2) (by positivity)

/-- For `u > 0`: `g(t u) = (1 + e^{-t u})⁻¹ → 1` and `σ'(t u) → 1` for SiLU. -/
private lemma silu_limits_pos_gun {u : ℝ} (hu : 0 < u) :
    Tendsto (fun t => (1 + Real.exp (-(t * u)))⁻¹) atTop (𝓝 1) ∧
      Tendsto (fun t => siluDeriv (t * u)) atTop (𝓝 1) := by
  have hz : Tendsto (fun t : ℝ => t * u) atTop atTop := tendsto_id.atTop_mul_const hu
  -- `e^{-t u} → 0` and `t u e^{-t u} → 0`
  have hE : Tendsto (fun t => Real.exp (-(t * u))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp hz
  have hZE : Tendsto (fun t => t * u * Real.exp (-(t * u))) atTop (𝓝 0) := by
    have := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hz
    simpa only [Function.comp_def, pow_one] using this
  have h1 : Tendsto (fun t => 1 + Real.exp (-(t * u))) atTop (𝓝 1) := by
    simpa using hE.const_add 1
  constructor
  · simpa using h1.inv₀ one_ne_zero
  · have h := (h1.add hZE).div (h1.pow 2) (by norm_num)
    rw [add_zero, one_pow, div_one] at h
    refine h.congr fun t => ?_
    rw [Pi.div_apply]
    rfl

/-- Along a ray, `g(t u) = (1 + e^{-t u})⁻¹` and `σ'(t u)` for SiLU tend to the same limit `ℓ`,
with `ℓ u = max(u, 0)`: `ℓ = 1` for `u > 0`, `ℓ = 0` for `u < 0`, `ℓ = 1/2` for `u = 0`. -/
private lemma silu_limits_gun (u : ℝ) :
    ∃ ℓ : ℝ, Tendsto (fun t => (1 + Real.exp (-(t * u)))⁻¹) atTop (𝓝 ℓ) ∧
      Tendsto (fun t => siluDeriv (t * u)) atTop (𝓝 ℓ) ∧ ℓ * u = max u 0 := by
  rcases lt_trichotomy u 0 with hneg | h0 | hpos
  · -- `u < 0`: from `-u > 0` by `g(-z) = 1 - g(z)` and `σ'(-z) = 1 - σ'(z)`
    obtain ⟨h1, h2⟩ := silu_limits_pos_gun (neg_pos.2 hneg)
    refine ⟨0, ?_, ?_, by rw [zero_mul, max_eq_right hneg.le]⟩
    · have h := h1.const_sub 1
      rw [sub_self] at h
      refine h.congr fun t => ?_
      rw [← logistic_neg_gun, show -(t * -u) = t * u by ring]
    · have h := h2.const_sub 1
      rw [sub_self] at h
      refine h.congr fun t => ?_
      rw [← siluDeriv_neg_gun, show -(t * -u) = t * u by ring]
  · -- `u = 0`: both are the constant `1/2`
    subst h0
    refine ⟨1 / 2, tendsto_const_nhds.congr fun t => ?_, tendsto_const_nhds.congr fun t => ?_,
      by rw [mul_zero, max_self]⟩
    · simp only [mul_zero, neg_zero, Real.exp_zero]
      norm_num
    · simp only [mul_zero, siluDeriv, neg_zero, Real.exp_zero]
      norm_num
  · obtain ⟨h1, h2⟩ := silu_limits_pos_gun hpos
    exact ⟨1, h1, h2, by rw [one_mul, max_eq_left hpos.le]⟩

/-- Gaussian decay beats `t²`: for `v² < u²`, `t² e^{-(t u + b)²/2 + (t v + d)²/2} → 0` (a copy of
the private `tendsto_sq_mul_exp_quad_uns` of `OneBlock/UnitsNoSymmetricPart.lean`). -/
private lemma tendsto_sq_mul_exp_quad_gun {u v : ℝ} (b d : ℝ) (h : v ^ 2 < u ^ 2) :
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

/-- `t φ(t u) → 0` for `u ≠ 0` (a copy of the private `tendsto_mul_gaussPdf_uns`). -/
private lemma tendsto_mul_gaussPdf_gun {u : ℝ} (hu : u ≠ 0) :
    Tendsto (fun t => t * gaussPdf (t * u)) atTop (𝓝 0) := by
  have hd := tendsto_sq_mul_exp_quad_gun (u := u) (v := 0) 0 0
    (by rw [sq_lt_sq, abs_zero]; exact abs_pos.2 hu)
  have h := (tendsto_inv_atTop_zero.mul hd).div_const (Real.sqrt (2 * Real.pi))
  rw [zero_mul, zero_div] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  have e : -(t * u + 0) ^ 2 / 2 + (t * 0 + 0) ^ 2 / 2 = -(t * u) ^ 2 / 2 := by ring
  rw [e, gaussPdf]
  have ht' := ht.ne'
  field_simp

/-- Along a ray, `Φ(t u)` and `σ'(t u) = Φ(t u) + t u φ(t u)` for GELU tend to the same limit `ℓ`,
with `ℓ u = max(u, 0)` (a copy of the private `gelu_limits_uns`). -/
private lemma gelu_limits_gun (u : ℝ) :
    ∃ ℓ : ℝ, Tendsto (fun t => gaussCdf (t * u)) atTop (𝓝 ℓ) ∧
      Tendsto (fun t => geluDeriv (t * u)) atTop (𝓝 ℓ) ∧ ℓ * u = max u 0 := by
  rcases lt_trichotomy u 0 with hneg | h0 | hpos
  · -- `u < 0`: `Φ(t u) → 0`
    have hΦ : Tendsto (fun t => gaussCdf (t * u)) atTop (𝓝 0) :=
      tendsto_gaussCdf_atBot.comp (Tendsto.atTop_mul_const_of_neg hneg tendsto_id)
    refine ⟨0, hΦ, ?_, by rw [zero_mul, max_eq_right hneg.le]⟩
    have h := hΦ.add ((tendsto_mul_gaussPdf_gun hneg.ne).const_mul u)
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
    have h := hΦ.add ((tendsto_mul_gaussPdf_gun hpos.ne').const_mul u)
    rw [mul_zero, add_zero] at h
    refine h.congr fun t => ?_
    simp only [geluDeriv]
    ring

/-- **Step 4 for SwiGLU units** (at least one unit): on a ray `x = t n̂` the term of order `t⁴`
gives `(n̂ X n̂ᵀ) ∑_i max(n̂ c_i, 0) (n̂ e_i) a_i = 0`, and the sum is nonzero on an open set of
directions. -/
theorem silu_gatedUnitsNoSymmetricPart (n k q : Type*) [Fintype n] [Fintype k] [Fintype q]
    [Nonempty q] : GatedUnitsNoSymmetricPart silu siluDeriv n k q := by
  -- SiLU is `z g(z)` with the logistic `g(z) = (1 + e^{-z})⁻¹`
  exact gatedUnitsNoSymmetricPart_of_gun (g := fun z => (1 + Real.exp (-z))⁻¹)
    (fun z => analyticOnNhd_silu z (Set.mem_univ z)) analyticAt_siluDeriv_gun
    (fun z => div_eq_mul_inv _ _) silu_limits_gun

/-- **Step 4 for GeGLU units** (at least one unit). -/
theorem gelu_gatedUnitsNoSymmetricPart (n k q : Type*) [Fintype n] [Fintype k] [Fintype q]
    [Nonempty q] : GatedUnitsNoSymmetricPart gelu geluDeriv n k q := by
  -- GELU is `z Φ(z)`
  exact gatedUnitsNoSymmetricPart_of_gun (g := gaussCdf)
    (fun z => analyticOnNhd_gelu z (Set.mem_univ z))
    (fun z => by
      have h1 := analyticOnNhd_gaussCdf z (Set.mem_univ z)
      have h2 := analyticOnNhd_gaussPdf z (Set.mem_univ z)
      show AnalyticAt ℝ (fun z => gaussCdf z + z * gaussPdf z) z
      fun_prop)
    (fun _ => rfl) gelu_limits_gun

end Skips
