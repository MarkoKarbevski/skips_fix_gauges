import SkipsLean.Imports
import Mathlib.Analysis.Complex.Liouville

/-!
# A bounded holomorphic map on a ball: the first terms of its expansion

Paper (dimension paper): Appendix D.6 (the case `ε = 0`), proof of Lemma D.19, "The expansion":
"For fixed `t`, by (46) the map `(δ, δ') ↦ 𝓛(z(t) − δ, 1 − δ'; n(t))` is holomorphic in the rows
`δ` with `|δ_j| ≤ ϱ t` and affine in the row `δ'`. We expand it in powers of `δ` and `δ'`. […] So
by Cauchy's estimates on the polydisc of (46), the coefficient of a product of `i` factors `δ_j`
and of at most one factor `δ'_j` is at most a fixed power of `t` times `(ϱ t)^{−i}`. […] the sum
of any set of its terms is at most a power of `t` times `e^{−(d/8)(t − t⁻¹)² r}`, where `r` is the
smallest sum of the numbers `r_j` of the factors of a term of the set."

The proof of Lemma D.19 uses this for three sets of terms: all terms with at least one factor
(Step 1); all terms other than the two terms of first order of one hidden unit `j` (Step 2); and,
when the map vanishes on the points `x` whose entries outside a set of hidden units vanish, all
terms that have a factor outside that set, other than the two terms of unit `j` (Step 4). The
statement below gives the three bounds without the power series: for a map `f` that is holomorphic
and bounded by `M` on the ball of radius `r` of a complex normed space, and for small `x`, `y`,
`w`,

  `‖f(x + y + w) − f(x) − 𝐃f(0) y‖ ≤ 16 M (‖w‖/r + (‖y‖/r) (‖x‖/r + ‖y‖/r))`.

(`f(x + y + w) − f(x + y)` is of first order in `w`; `f(x + y) − f(x) − 𝐃f(x) y` is of second
order in `y`; `𝐃f(x) y − 𝐃f(0) y` is of first order in `x` and in `y`. Each follows from Cauchy's
estimate in one complex variable, on a line through the ball.) With the sup norm on
`ℂ^q × ℂ^q`, a ball is the paper's polydisc.
-/

namespace Skips

open Metric in
/-- Cauchy's estimate on a line: if `g` is holomorphic and bounded by `K` on the ball of radius `R`,
and the closed disc `{p + t v : |t| ≤ ρ}` lies in that ball, then `‖𝐃g(p) v‖ ≤ K / ρ`. -/
private theorem norm_fderiv_apply_le_hb {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup G] [NormedSpace ℂ G] {g : E → G} {R K ρ : ℝ}
    (hd : DifferentiableOn ℂ g (ball 0 R)) (hK : ∀ q ∈ ball (0 : E) R, ‖g q‖ ≤ K)
    (hρ : 0 < ρ) {p v : E} (hpv : ‖p‖ + ρ * ‖v‖ < R) : ‖fderiv ℂ g p v‖ ≤ K / ρ := by
  -- the line `t ↦ p + t • v` maps the closed disc of radius `ρ` into the ball
  have hmem : ∀ t : ℂ, ‖t‖ ≤ ρ → p + t • v ∈ ball (0 : E) R := by
    intro t ht
    rw [mem_ball_zero_iff]
    calc ‖p + t • v‖ ≤ ‖p‖ + ‖t‖ * ‖v‖ := (norm_add_le _ _).trans (by rw [norm_smul])
      _ ≤ ‖p‖ + ρ * ‖v‖ := by gcongr
      _ < R := hpv
  have hdiff : ∀ t : ℂ, ‖t‖ ≤ ρ → DifferentiableAt ℂ (fun s : ℂ => g (p + s • v)) t := by
    intro t ht
    have h1 : DifferentiableAt ℂ g (p + t • v) :=
      hd.differentiableAt (isOpen_ball.mem_nhds (hmem t ht))
    have h2 : DifferentiableAt ℂ (fun s : ℂ => p + s • v) t := by fun_prop
    exact h1.comp t h2
  -- Cauchy's estimate at the centre `0` of the disc
  have hdc : DiffContOnCl ℂ (fun s : ℂ => g (p + s • v)) (ball 0 ρ) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball 0 hρ.ne']
    intro t ht
    exact (hdiff t (mem_closedBall_zero_iff.mp ht)).differentiableWithinAt
  have hC := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hρ hdc
    (fun z hz => hK _ (hmem z (mem_sphere_zero_iff_norm.mp hz).le))
  -- the derivative at `0` of `t ↦ g (p + t • v)` is `𝐃g(p) v`
  have hp : p ∈ ball (0 : E) R := by simpa using hmem 0 (by simpa using hρ.le)
  have hline : HasDerivAt (fun s : ℂ => p + s • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const v).const_add p
  have hg : HasFDerivAt g (fderiv ℂ g p) p :=
    (hd.differentiableAt (isOpen_ball.mem_nhds hp)).hasFDerivAt
  have hcomp := hg.comp_hasDerivAt_of_eq (0 : ℂ) hline (by simp)
  have hder : deriv (fun s : ℂ => g (p + s • v)) 0 = fderiv ℂ g p v := hcomp.deriv
  rwa [hder] at hC

open Metric in
/-- Cauchy's estimate for the derivative: if `g` is holomorphic and bounded by `K` on the ball of
radius `R`, and `‖p‖ + ρ < R`, then `‖𝐃g(p)‖ ≤ K / ρ`. -/
private theorem norm_fderiv_le_hb {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup G] [NormedSpace ℂ G] {g : E → G} {R K ρ : ℝ}
    (hd : DifferentiableOn ℂ g (ball 0 R)) (hK : ∀ q ∈ ball (0 : E) R, ‖g q‖ ≤ K)
    (hρ : 0 < ρ) {p : E} (hpρ : ‖p‖ + ρ < R) : ‖fderiv ℂ g p‖ ≤ K / ρ := by
  have hK0 : 0 ≤ K :=
    (norm_nonneg _).trans (hK 0 (mem_ball_self (by linarith [norm_nonneg p])))
  refine ContinuousLinearMap.opNorm_le_bound _ (div_nonneg hK0 hρ.le) fun u => ?_
  rcases eq_or_ne u 0 with rfl | hu
  · simp
  have hu' : 0 < ‖u‖ := norm_pos_iff.mpr hu
  -- Cauchy's estimate on the line through `p` in the direction `u`, with radius `ρ / ‖u‖`
  have h := norm_fderiv_apply_le_hb hd hK (div_pos hρ hu') (p := p) (v := u)
    (by rwa [div_mul_cancel₀ _ hu'.ne'])
  calc ‖fderiv ℂ g p u‖ ≤ K / (ρ / ‖u‖) := h
    _ = K / ρ * ‖u‖ := by field_simp

open Metric in
/-- The mean value inequality with Cauchy's estimate: if `g` is holomorphic and bounded by `K` on
the ball of radius `R`, then it is `K / ρ`-Lipschitz on the closed ball of radius `R'`, for
`R' + ρ < R`. -/
private theorem norm_sub_le_of_bounded_hb {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup G] [NormedSpace ℂ G] {g : E → G} {R K ρ R' : ℝ}
    (hd : DifferentiableOn ℂ g (ball 0 R)) (hK : ∀ q ∈ ball (0 : E) R, ‖g q‖ ≤ K)
    (hρ : 0 < ρ) (hR' : R' + ρ < R) {p q : E} (hp : ‖p‖ ≤ R') (hq : ‖q‖ ≤ R') :
    ‖g p - g q‖ ≤ K / ρ * ‖p - q‖ := by
  have hs : ∀ z ∈ closedBall (0 : E) R', DifferentiableAt ℂ g z := fun z hz =>
    hd.differentiableAt (isOpen_ball.mem_nhds (by
      rw [mem_ball_zero_iff]; rw [mem_closedBall_zero_iff] at hz; linarith))
  exact (convex_closedBall 0 R').norm_image_sub_le_of_norm_fderiv_le hs
    (fun z hz => norm_fderiv_le_hb hd hK hρ (by rw [mem_closedBall_zero_iff] at hz; linarith))
    (mem_closedBall_zero_iff.mpr hq) (mem_closedBall_zero_iff.mpr hp)

/-- **Cauchy's estimates for the first terms of the expansion:** let `f` be holomorphic on the open
ball of radius `r` around `0` of a complex normed space, with `‖f‖ ≤ M` there. For `x`, `y`, `w`
of norm at most `r/8`,
`‖f(x + y + w) − f(x) − 𝐃f(0) y‖ ≤ 16 M (‖w‖/r + (‖y‖/r) (‖x‖/r + ‖y‖/r))`. -/
theorem norm_sub_sub_fderiv_le_of_analyticOnNhd_ball
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F]
    [NormedSpace ℂ F] [CompleteSpace F] {f : E → F} {r M : ℝ} (hr : 0 < r)
    (hf : AnalyticOnNhd ℂ f (Metric.ball 0 r)) (hM : ∀ x ∈ Metric.ball (0 : E) r, ‖f x‖ ≤ M)
    {x y w : E} (hx : ‖x‖ ≤ r / 8) (hy : ‖y‖ ≤ r / 8) (hw : ‖w‖ ≤ r / 8) :
    ‖f (x + y + w) - f x - fderiv ℂ f 0 y‖
      ≤ 16 * M * (‖w‖ / r + ‖y‖ / r * (‖x‖ / r + ‖y‖ / r)) := by
  -- `M ≥ 0`, since `‖f 0‖ ≤ M`
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (Metric.mem_ball_self hr))
  have hd : DifferentiableOn ℂ f (Metric.ball 0 r) := hf.differentiableOn
  -- `𝐃f` is holomorphic on the ball, and bounded by `M / (r/2)` on the ball of radius `r/2`
  have hdΦ : DifferentiableOn ℂ (fderiv ℂ f) (Metric.ball 0 (r / 2)) :=
    hf.fderiv.differentiableOn.mono (Metric.ball_subset_ball (by linarith))
  have hKΦ : ∀ q ∈ Metric.ball (0 : E) (r / 2), ‖fderiv ℂ f q‖ ≤ M / (r / 2) := fun q hq =>
    norm_fderiv_le_hb hd hM (by positivity) (by rw [mem_ball_zero_iff] at hq; linarith)
  -- so `𝐃f` is `L`-Lipschitz on the closed ball of radius `r/4`, with `L = 16 M / r²`
  set L := M / (r / 2) / (r / 8) with hL
  have hL0 : 0 ≤ L := by positivity
  have hLip : ∀ p q : E, ‖p‖ ≤ r / 4 → ‖q‖ ≤ r / 4 →
      ‖fderiv ℂ f p - fderiv ℂ f q‖ ≤ L * ‖p - q‖ := fun p q hp hq =>
    norm_sub_le_of_bounded_hb hdΦ hKΦ (by positivity) (by linarith) hp hq
  -- first term: `‖f(x + y + w) − f(x + y)‖ ≤ (M / (r/2)) ‖w‖`
  have h1 : ‖f (x + y + w) - f (x + y)‖ ≤ M / (r / 2) * ‖w‖ := by
    have h := norm_sub_le_of_bounded_hb hd hM (ρ := r / 2) (R' := 3 * r / 8) (by positivity)
      (by linarith) (p := x + y + w) (q := x + y) (norm_add₃_le.trans (by linarith))
      ((norm_add_le _ _).trans (by linarith))
    rwa [add_sub_cancel_left] at h
  -- second term: `‖f(x + y) − f(x) − 𝐃f(x) y‖ ≤ L ‖y‖²`, by the mean value inequality for
  -- `f − 𝐃f(x)` on the closed ball of radius `‖y‖` around `x`
  have h2 : ‖f (x + y) - f x - fderiv ℂ f x y‖ ≤ L * ‖y‖ * ‖y‖ := by
    have hs : ∀ z ∈ Metric.closedBall x ‖y‖, ‖z‖ ≤ r / 4 := by
      intro z hz
      rw [mem_closedBall_iff_norm] at hz
      calc ‖z‖ = ‖(z - x) + x‖ := by rw [sub_add_cancel]
        _ ≤ ‖z - x‖ + ‖x‖ := norm_add_le _ _
        _ ≤ r / 4 := by linarith
    have hdz : ∀ z ∈ Metric.closedBall x ‖y‖, DifferentiableAt ℂ f z := fun z hz =>
      hd.differentiableAt (Metric.isOpen_ball.mem_nhds (by
        rw [mem_ball_zero_iff]; linarith [hs z hz]))
    have hb : ∀ z ∈ Metric.closedBall x ‖y‖, ‖fderiv ℂ f z - fderiv ℂ f x‖ ≤ L * ‖y‖ := by
      intro z hz
      refine (hLip z x (hs z hz) (by linarith)).trans ?_
      gcongr
      exact mem_closedBall_iff_norm.mp hz
    have h := (convex_closedBall x ‖y‖).norm_image_sub_le_of_norm_fderiv_le' hdz hb
      (Metric.mem_closedBall_self (norm_nonneg y))
      (by rw [mem_closedBall_iff_norm, add_sub_cancel_left])
    rwa [add_sub_cancel_left] at h
  -- third term: `‖𝐃f(x) y − 𝐃f(0) y‖ ≤ L ‖x‖ ‖y‖`
  have h3 : ‖fderiv ℂ f x y - fderiv ℂ f 0 y‖ ≤ L * ‖x‖ * ‖y‖ := by
    rw [← _root_.sub_apply]
    calc _ ≤ ‖fderiv ℂ f x - fderiv ℂ f 0‖ * ‖y‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ L * ‖x - 0‖ * ‖y‖ := by
        gcongr
        exact hLip x 0 (by linarith) (by rw [norm_zero]; positivity)
      _ = L * ‖x‖ * ‖y‖ := by rw [sub_zero]
  -- the sum of the three terms
  have hsplit : f (x + y + w) - f x - fderiv ℂ f 0 y = (f (x + y + w) - f (x + y))
      + (f (x + y) - f x - fderiv ℂ f x y) + (fderiv ℂ f x y - fderiv ℂ f 0 y) := by abel
  rw [hsplit]
  refine norm_add₃_le.trans ?_
  have e : 16 * M * (‖w‖ / r + ‖y‖ / r * (‖x‖ / r + ‖y‖ / r)) = M / (r / 2) * ‖w‖
      + L * ‖y‖ * ‖y‖ + L * ‖x‖ * ‖y‖ + 14 * (M * ‖w‖ / r) := by
    rw [hL]; field_simp; ring
  have : 0 ≤ M * ‖w‖ / r := by positivity
  linarith

end Skips
