import SkipsLean.Imports
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Matrix.Normed

/-!
# A real-analytic map extends to a holomorphic map on a complex neighbourhood

Paper (dimension paper), proof of Lemma D.10: "So `𝓑_{>k}(t (h° + u))` is a real-analytic function
of `(1/t, u)` near `(0, 0)`. It extends to a holomorphic and bounded function on a complex
neighborhood of `(0, 0)`, which gives `ϱ` and `t_0`."

This is a known fact (the power series of the map at the point, with complex arguments).
Mathlib does not have it at the pinned version (searched for `complexif`, for `ofReal` with
`AnalyticAt`, and for `baseChange` under `Analysis/Analytic`; it has the converse, the restriction
of a holomorphic map to the reals, `AnalyticAt.re_ofReal`), so it is proved here, for maps between
spaces of real tuples:

* `exists_analyticOnNhd_complex_extension`: a map `f : ℝ^ι → ℝ^κ` that is real-analytic at `x`
  agrees on a ball around `x` with a map `g : ℂ^ι → ℂ^κ` that is holomorphic on the ball of the
  same radius around `x`;
* `exists_holomorphic_extension_real_param`: the step of the paper, for a map `F(s, h)` of a real
  number and a real matrix that is real-analytic at `(0, H)`: there are `ϱ, s₀ > 0` and a bound
  `C` such that for every real `s` with `|s| ≤ s₀` the map `u ↦ F(s, H + u)` extends to a
  holomorphic map on the complex matrices `u` with `|u_{τ j}| ≤ ϱ` for all entries, bounded by `C`
  there. ("Holomorphic on" a closed set is `AnalyticOnNhd ℂ`: holomorphic near each of its
  points.)
-/

namespace Skips

open scoped Matrix.Norms.Elementwise Topology

/-- Helper: the term of order `n` of a real power series `p` on `ℝ^ι`, complexified:
`q_n(z_1, …, z_n) = ∑_c (∏_k z_{k, c_k}) p_n(e_{c_1}, …, e_{c_n})`, the sum over the maps
`c : Fin n → ι`, with `e_i` the basis vectors. -/
private noncomputable def cxTerm {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (p : FormalMultilinearSeries ℝ (ι → ℝ) (κ → ℝ)) (n : ℕ) :
    ContinuousMultilinearMap ℂ (fun _ : Fin n => ι → ℂ) (κ → ℂ) :=
  ∑ c : Fin n → ι, ((ContinuousMultilinearMap.mkPiAlgebra ℂ (Fin n) ℂ).compContinuousLinearMap
    (fun k => ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι => ℂ) (c k))).smulRight
    (fun j => ((p n (fun k => fun i => if c k = i then (1 : ℝ) else 0) j : ℝ) : ℂ))

/-- Helper: the value of the complexified term. -/
private theorem cxTerm_apply {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (p : FormalMultilinearSeries ℝ (ι → ℝ) (κ → ℝ)) (n : ℕ) (z : Fin n → ι → ℂ) (j : κ) :
    cxTerm p n z j = ∑ c : Fin n → ι, (∏ k, z k (c k))
      * ((p n (fun k => fun i => if c k = i then (1 : ℝ) else 0) j : ℝ) : ℂ) := by
  simp [cxTerm]

/-- Helper: at real arguments the complexified term is the real term, by multilinearity
(`v = ∑_i v_i e_i`). -/
private theorem cxTerm_real {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (p : FormalMultilinearSeries ℝ (ι → ℝ) (κ → ℝ)) (n : ℕ) (v : ι → ℝ) (j : κ) :
    cxTerm p n (fun _ => fun i => (v i : ℂ)) j = ((p n (fun _ => v) j : ℝ) : ℂ) := by
  have hv : p n (fun _ => v) = ∑ c : Fin n → ι, (∏ k, v (c k))
      • p n (fun k => fun i => if c k = i then (1 : ℝ) else 0) := by
    have he : (fun _ : Fin n => v)
        = fun _ => ∑ i, v i • fun i' => if i = i' then (1 : ℝ) else 0 :=
      funext fun _ => pi_eq_sum_univ v
    rw [he, ContinuousMultilinearMap.map_sum]
    exact Finset.sum_congr rfl fun c _ => (p n).map_smul_univ (fun k => v (c k)) _
  rw [cxTerm_apply, hv]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Complex.ofReal_sum,
    Complex.ofReal_mul, Complex.ofReal_prod]

/-- Helper: `‖q_n‖ ≤ (card ι)^n ‖p_n‖`, as `|∏_k z_{k, c_k}| ≤ ∏_k ‖z_k‖` and
`‖p_n(e_{c_1}, …, e_{c_n})‖ ≤ ‖p_n‖`. -/
private theorem norm_cxTerm_le {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (p : FormalMultilinearSeries ℝ (ι → ℝ) (κ → ℝ)) (n : ℕ) :
    ‖cxTerm p n‖ ≤ (Fintype.card ι : ℝ) ^ n * ‖p n‖ := by
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun z => ?_
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
  rw [cxTerm_apply]
  calc _ ≤ ∑ c : Fin n → ι, ‖p n‖ * ∏ k, ‖z k‖ := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => ?_)
        rw [norm_mul, norm_prod, Complex.norm_real, mul_comm]
        refine mul_le_mul ?_ (Finset.prod_le_prod₀ (fun k _ => norm_nonneg _)
          fun k _ => norm_le_pi_norm (z k) (c k)) (Finset.prod_nonneg fun k _ => norm_nonneg _)
          (norm_nonneg _)
        refine (norm_le_pi_norm _ j).trans ((p n).unit_le_opNorm ?_)
        refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun k => ?_
        refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_
        split_ifs <;> simp
    _ = (Fintype.card ι : ℝ) ^ n * ‖p n‖ * ∏ k, ‖z k‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul,
          Nat.cast_pow, mul_assoc]

/-- **A real-analytic map extends to a holomorphic map:** if `f : ℝ^ι → ℝ^κ` is real-analytic at
`x`, there are a radius `r > 0` and a map `g : ℂ^ι → ℂ^κ`, holomorphic on the ball of radius `r`
around `x`, with `g(y) = f(y)` at the real points `y` of the ball of radius `r` around `x`. -/
theorem exists_analyticOnNhd_complex_extension {ι κ : Type*} [Fintype ι] [Fintype κ]
    {f : (ι → ℝ) → (κ → ℝ)} {x : ι → ℝ} (hf : AnalyticAt ℝ f x) :
    ∃ r : ℝ, 0 < r ∧ ∃ g : (ι → ℂ) → (κ → ℂ),
      AnalyticOnNhd ℂ g (Metric.ball (fun i => (x i : ℂ)) r)
      ∧ ∀ y ∈ Metric.ball x r, g (fun i => (y i : ℂ)) = fun j => (f y j : ℂ) := by
  classical
  obtain ⟨p, r₀, hp⟩ := hf
  -- a radius `0 < r₁ < r₀`, and the bound `‖p n‖ r₁^n ≤ C`
  obtain ⟨r₁, hr₁0, hr₁⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hp.r_pos
  have hr₁0' : (0 : ℝ) < r₁ := by exact_mod_cast hr₁0
  obtain ⟨C, -, hC⟩ := p.norm_mul_pow_le_of_lt_radius (hr₁.trans_le hp.r_le)
  -- the complexified series and a lower bound `ρ = r₁ / (card ι + 1)` of its radius
  set q : FormalMultilinearSeries ℂ (ι → ℂ) (κ → ℂ) := fun n => cxTerm p n with hq_def
  set ρ : NNReal := r₁ / ((Fintype.card ι : NNReal) + 1) with hρ_def
  have hρ : (ρ : ℝ) = r₁ / ((Fintype.card ι : ℝ) + 1) := by
    rw [hρ_def, NNReal.coe_div]; push_cast; rfl
  have hN : (0 : ℝ) < (Fintype.card ι : ℝ) + 1 := by positivity
  have hρ0 : (0 : ℝ) < ρ := by rw [hρ]; positivity
  have hρr₁ : (ρ : ℝ) ≤ r₁ := by
    rw [hρ, div_le_iff₀ hN]; nlinarith [Nat.cast_nonneg (α := ℝ) (Fintype.card ι)]
  have hρq : (ρ : ENNReal) ≤ q.radius := by
    refine q.le_radius_of_bound C fun n => ?_
    have hcρ : (Fintype.card ι : ℝ) * ρ ≤ r₁ := by
      rw [hρ, ← mul_div_assoc, div_le_iff₀ hN]; nlinarith
    calc ‖q n‖ * (ρ : ℝ) ^ n ≤ (Fintype.card ι : ℝ) ^ n * ‖p n‖ * (ρ : ℝ) ^ n :=
          mul_le_mul_of_nonneg_right (norm_cxTerm_le p n) (by positivity)
      _ = ‖p n‖ * ((Fintype.card ι : ℝ) * ρ) ^ n := by rw [mul_pow]; ring
      _ ≤ ‖p n‖ * (r₁ : ℝ) ^ n :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hcρ n) (norm_nonneg _)
      _ ≤ C := hC n
  have hq0 : 0 < q.radius := lt_of_lt_of_le (by exact_mod_cast hρ0) hρq
  refine ⟨ρ, hρ0, fun z => q.sum (z - fun i => (x i : ℂ)), ?_, ?_⟩
  · -- holomorphic: the sum of a power series inside its radius
    have hs := (q.hasFPowerSeriesOnBall hq0).comp_sub (fun i => (x i : ℂ))
    refine hs.analyticOnNhd.mono fun z hz => ?_
    rw [zero_add]
    refine lt_of_lt_of_le ?_ hρq
    rw [Metric.mem_ball] at hz
    exact edist_lt_coe.2 (by rw [← NNReal.coe_lt_coe, coe_nndist]; exact hz)
  · intro y hy
    rw [Metric.mem_ball, dist_eq_norm] at hy
    set v := y - x with hv_def
    -- the real series
    have hv : v ∈ Metric.eball (0 : ι → ℝ) r₀ := by
      rw [mem_eball_zero_iff]
      refine lt_of_lt_of_le ?_ (le_of_lt hr₁)
      rw [← ofReal_norm, ← ENNReal.ofReal_coe_nnreal]
      exact (ENNReal.ofReal_lt_ofReal_iff hr₁0').2 (hy.trans_le hρr₁)
    have h1 := hp.hasSum hv
    rw [hv_def, add_sub_cancel] at h1
    set cc : (κ → ℝ) →L[ℝ] (κ → ℂ) :=
      ContinuousLinearMap.pi fun j => Complex.ofRealCLM.comp (ContinuousLinearMap.proj j)
    have h2 := h1.mapL cc
    -- the complex series
    set z : ι → ℂ := fun i => (v i : ℂ) with hz_def
    have hzn : ‖z‖ ≤ ‖v‖ :=
      (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => by
        rw [hz_def, Complex.norm_real]; exact norm_le_pi_norm v i
    have hz : z ∈ Metric.eball (0 : ι → ℂ) q.radius := by
      rw [mem_eball_zero_iff]
      refine lt_of_lt_of_le ?_ hρq
      rw [← ofReal_norm, ← ENNReal.ofReal_coe_nnreal]
      exact (ENNReal.ofReal_lt_ofReal_iff hρ0).2 (hzn.trans_lt hy)
    have h3 := q.hasSum hz
    have he : (fun n => q n fun _ => z) = fun n => cc (p n fun _ => v) :=
      funext fun n => funext fun j => cxTerm_real p n v j
    rw [he] at h3
    have hzy : (fun i => (y i : ℂ)) - (fun i => (x i : ℂ)) = z := by
      funext i; simp [hz_def, hv_def]
    show q.sum ((fun i => (y i : ℂ)) - fun i => (x i : ℂ)) = cc (f y)
    rw [hzy]
    exact h3.unique h2

/-- **Proof of Lemma D.10, "It extends to a holomorphic and bounded function on a complex
neighborhood of `(0, 0)`, which gives `ϱ` and `t_0`":** if `F(s, h)` is real-analytic at
`(0, H)`, there are `ϱ, s₀ > 0` and `C` such that, for every real `s` with `|s| ≤ s₀`, the map
`u ↦ F(s, H + u)` extends to a holomorphic map on the complex matrices `u` with
`|u_{τ j}| ≤ ϱ`, bounded by `C`. -/
theorem exists_holomorphic_extension_real_param {T d T' d' : Type*} [Fintype T] [Fintype d]
    [Fintype T'] [Fintype d'] {F : ℝ × Matrix T d ℝ → Matrix T' d' ℝ} {H : Matrix T d ℝ}
    (hF : AnalyticAt ℝ F (0, H)) :
    ∃ ϱ : ℝ, 0 < ϱ ∧ ∃ s₀ : ℝ, 0 < s₀ ∧ ∃ C : ℝ, ∀ s : ℝ, |s| ≤ s₀ →
      ∃ G : Matrix T d ℂ → Matrix T' d' ℂ,
        AnalyticOnNhd ℂ G {u | ∀ τ j, ‖u τ j‖ ≤ ϱ}
        ∧ (∀ u : Matrix T d ℝ, (∀ τ j, |u τ j| ≤ ϱ) →
            G (u.map fun a : ℝ => (a : ℂ)) = (F (s, H + u)).map fun a : ℝ => (a : ℂ))
        ∧ ∀ u : Matrix T d ℂ, (∀ τ j, ‖u τ j‖ ≤ ϱ) → ‖G u‖ ≤ C := by
  sorry

end Skips
