import SkipsLean.Imports
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
# Two facts about ridge functions

Paper (absorb paper), Appendix A.1, before Theorem A.7 (Identity absorption for GELU): "The GELU
case needs one classical fact about ridge functions, whose short proof we include."

Lemma A.5 (Vanishing sums of ridge functions): "Let `a_1, …, a_r ∈ ℝ^{d_model}` be nonzero and
pairwise non-collinear, and let `g_1, …, g_r : ℝ → ℝ^q` be `r − 1` times continuously
differentiable with `∑_i g_i(a_i · x) = 0` for all `x ∈ ℝ^{d_model}`. Then every `g_i` is a
polynomial of degree at most `r − 2`."

Lemma A.6 (Distinct scales): "Let `ψ : ℝ → ℝ` be real-analytic and not a polynomial. Let
`α_1, …, α_n > 0` be distinct and `a_1, …, a_n ∈ ℝ^q`. If `∑_k a_k ψ(α_k t)` is a polynomial in
`t`, then every `a_k` is zero."

Stated here as in the paper. In Lemma A.5 a function with values in `ℝ^q` is a polynomial of degree
at most `r − 2` when each of its `q` coordinates is: there is a real polynomial `P` of degree less
than `r − 1` (for `r = 1` this is the zero polynomial) that agrees with the coordinate. The step of
the paper's proof, "so `g_i^{(r−1)} = 0`", is stated as well. In Lemma A.6 "is a polynomial in `t`"
is asked of each coordinate.

The Lean proof of Theorem A.7 (`Absorb/Block.lean`) goes another way (from ReLU, along rays) and
does not use these two lemmas; they are stated because the paper numbers them.
-/

namespace Skips

open Matrix

/-- A direction `u` with `b · u = 0` and `a · u ≠ 0`, for `b ≠ 0` and `a` not a multiple of `b`:
`u = a − ((a · b)/(b · b)) b`, and then `a · u = u · u > 0`. -/
private lemma exists_dir_rf {d : Type*} [Fintype d] (a b : d → ℝ) (hb : b ≠ 0)
    (hab : ∀ c : ℝ, a ≠ c • b) : ∃ u : d → ℝ, b ⬝ᵥ u = 0 ∧ a ⬝ᵥ u ≠ 0 := by
  have hbb : b ⬝ᵥ b ≠ 0 := fun h => hb (dotProduct_self_eq_zero.1 h)
  set c : ℝ := (a ⬝ᵥ b) / (b ⬝ᵥ b) with hc
  have hu : a - c • b ≠ 0 := fun h => hab c (sub_eq_zero.1 h)
  have h1 : b ⬝ᵥ (a - c • b) = 0 := by
    rw [dotProduct_sub, dotProduct_smul, smul_eq_mul, hc, dotProduct_comm b a,
      div_mul_cancel₀ _ hbb, sub_self]
  refine ⟨a - c • b, h1, ?_⟩
  have h2 : a ⬝ᵥ (a - c • b) = (a - c • b) ⬝ᵥ (a - c • b) := by
    rw [sub_dotProduct, smul_dotProduct, h1, smul_zero, sub_zero]
  rw [h2]
  exact fun h => hu (dotProduct_self_eq_zero.1 h)

/-- If `G(a · x) = 0` for all `x` and `a ≠ 0`, then `G = 0` (`a · x` takes every real value). -/
private lemma eq_zero_of_comp_dot_rf {d F : Type*} [Fintype d] [AddCommGroup F] (a : d → ℝ)
    (ha : a ≠ 0) (G : ℝ → F) (h : ∀ x : d → ℝ, G (a ⬝ᵥ x) = 0) : G = 0 := by
  funext t
  have hbb : a ⬝ᵥ a ≠ 0 := fun h => ha (dotProduct_self_eq_zero.1 h)
  have h1 := h ((t / (a ⬝ᵥ a)) • a)
  rw [dotProduct_smul, smul_eq_mul, div_mul_cancel₀ _ hbb] at h1
  exact h1

/-- A sum over a finset contained in `{i}` vanishing identically forces `G i = 0`. -/
private lemma eq_zero_of_sum_single_rf {ι d F : Type*} [Fintype d] [AddCommGroup F]
    (a : ι → d → ℝ) (S : Finset ι) (G : ι → ℝ → F) (i : ι) (hi : i ∈ S) (ha : a i ≠ 0)
    (hS : ∀ k ∈ S, k = i) (hsum : ∀ x : d → ℝ, ∑ k ∈ S, G k (a k ⬝ᵥ x) = 0) : G i = 0 := by
  have hSi : S = {i} := Finset.eq_singleton_iff_unique_mem.2 ⟨hi, hS⟩
  refine eq_zero_of_comp_dot_rf (a i) ha _ fun x => ?_
  simpa [hSi] using hsum x

/-- The induction of Lemma A.5 on the number of terms: if `∑_{k ∈ S} G_k(a_k · x) = 0` for all
`x`, with at most `m + 1` terms of class `C^m`, nonzero and pairwise non-collinear `a_k`, then
`G_i^{(m)} = 0` for `i ∈ S`. Step: differentiate along a direction `u` with `a_j · u = 0`. -/
private lemma iteratedDeriv_eq_zero_rf {ι d F : Type*} [Fintype d] [DecidableEq ι]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (a : ι → d → ℝ) :
    ∀ (m : ℕ) (S : Finset ι) (G : ι → ℝ → F), S.card ≤ m + 1 →
    (∀ k ∈ S, a k ≠ 0) → (∀ k ∈ S, ∀ j ∈ S, k ≠ j → ∀ c : ℝ, a k ≠ c • a j) →
    (∀ k ∈ S, ContDiff ℝ m (G k)) → (∀ x : d → ℝ, ∑ k ∈ S, G k (a k ⬝ᵥ x) = 0) →
    ∀ i ∈ S, iteratedDeriv m (G i) = 0 := by
  intro m
  induction m with
  | zero =>
    intro S G hS ha _ _ hsum i hi
    rw [iteratedDeriv_zero]
    exact eq_zero_of_sum_single_rf a S G i hi (ha i hi)
      (fun k hk => Finset.card_le_one.1 hS k hk i hi) hsum
  | succ m ih =>
    intro S G hS ha hcol hG hsum i hi
    by_cases hex : ∃ j ∈ S, j ≠ i
    · obtain ⟨j, hj, hji⟩ := hex
      obtain ⟨u, hu1, hu2⟩ := exists_dir_rf (a i) (a j) (ha j hj) (hcol i hi j hj hji.symm)
      have hG' : ∀ k ∈ S, Differentiable ℝ (G k) ∧ ContDiff ℝ m (deriv (G k)) := by
        intro k hk
        have h1 : ContDiff ℝ ((m : WithTop ℕ∞) + 1) (G k) := by exact_mod_cast hG k hk
        obtain ⟨h2, -, h3⟩ := contDiff_succ_iff_deriv.1 h1
        exact ⟨h2, h3⟩
      -- differentiate the identity along the line `x + s u` at `s = 0`
      have hder : ∀ x : d → ℝ,
          ∑ k ∈ S.erase j, ((a k ⬝ᵥ u) • deriv (G k)) (a k ⬝ᵥ x) = 0 := by
        intro x
        have hd : ∀ k ∈ S, HasDerivAt (fun s : ℝ => G k (a k ⬝ᵥ (x + s • u)))
            ((a k ⬝ᵥ u) • deriv (G k) (a k ⬝ᵥ x) : F) (0 : ℝ) := by
          intro k hk
          have hl : HasDerivAt (fun s : ℝ => a k ⬝ᵥ (x + s • u)) (a k ⬝ᵥ u) 0 := by
            have he : (fun s : ℝ => a k ⬝ᵥ (x + s • u)) = fun s => a k ⬝ᵥ x + s * (a k ⬝ᵥ u) := by
              funext s
              rw [dotProduct_add, dotProduct_smul, smul_eq_mul]
            rw [he]
            simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (a k ⬝ᵥ u)).const_add (a k ⬝ᵥ x)
          have h2 := HasDerivAt.scomp (h := fun s : ℝ => a k ⬝ᵥ (x + s • u)) (0 : ℝ)
            ((hG' k hk).1 _).hasDerivAt hl
          rw [show a k ⬝ᵥ x = a k ⬝ᵥ (x + (0 : ℝ) • u) by simp]
          exact h2
        have hs := HasDerivAt.fun_sum hd
        have hc : (fun s : ℝ => ∑ k ∈ S, G k (a k ⬝ᵥ (x + s • u))) = fun _ => 0 :=
          funext fun s => hsum _
        rw [hc] at hs
        have h0 := hs.unique (hasDerivAt_const (0 : ℝ) (0 : F))
        rw [← Finset.add_sum_erase S _ hj, hu1, zero_smul, zero_add] at h0
        simpa using h0
      have hres := ih (S.erase j) (fun k => (a k ⬝ᵥ u) • deriv (G k))
        (by rw [Finset.card_erase_of_mem hj]; omega)
        (fun k hk => ha k (Finset.mem_of_mem_erase hk))
        (fun k hk l hl hkl =>
          hcol k (Finset.mem_of_mem_erase hk) l (Finset.mem_of_mem_erase hl) hkl)
        (fun k hk => (hG' k (Finset.mem_of_mem_erase hk)).2.const_smul _) hder i
        (Finset.mem_erase.2 ⟨hji.symm, hi⟩)
      funext x
      have h1 := congrFun hres x
      rw [iteratedDeriv_const_smul_field] at h1
      rw [iteratedDeriv_succ']
      exact (smul_eq_zero.1 h1).resolve_left hu2
    · push Not at hex
      rw [eq_zero_of_sum_single_rf a S G i hi (ha i hi) hex hsum]
      funext x
      exact iteratedDeriv_const_zero

/-- **Lemma A.5 of the absorb paper, as its proof obtains it:** for nonzero, pairwise
non-collinear `a_1, …, a_r` and `g_1, …, g_r : ℝ → ℝ^q` that are `r − 1` times continuously
differentiable with `∑_i g_i(a_i · x) = 0` for all `x`, the derivative of order `r − 1` of every
`g_i` vanishes. -/
theorem iteratedDeriv_eq_zero_of_sum_ridge_eq_zero {d q : Type*} [Fintype d] [Fintype q] {r : ℕ}
    (a : Fin r → d → ℝ) (ha : ∀ i, a i ≠ 0) (hcol : ∀ i j, i ≠ j → ∀ c : ℝ, a i ≠ c • a j)
    (g : Fin r → ℝ → q → ℝ) (hg : ∀ i, ContDiff ℝ (r - 1 : ℕ) (g i))
    (hsum : ∀ x : d → ℝ, ∑ i, g i (a i ⬝ᵥ x) = 0) (i : Fin r) :
    iteratedDeriv (r - 1) (g i) = 0 := by
  have hr := i.pos
  exact iteratedDeriv_eq_zero_rf a (r - 1) Finset.univ g
    (by rw [Finset.card_univ, Fintype.card_fin]; omega) (fun k _ => ha k)
    (fun k _ j _ h => hcol k j h) (fun k _ => hg k) hsum i (Finset.mem_univ i)


/-- A `C^n` function `ℝ → ℝ` whose `n`-th derivative vanishes is a polynomial of degree `< n`:
by induction, `f' = ∑_{i<n} c_i t^i`, and `f − ∑ (c_i/(i+1)) t^{i+1}` has derivative zero. -/
private lemma exists_coeffs_rf : ∀ (n : ℕ) (f : ℝ → ℝ), ContDiff ℝ n f → iteratedDeriv n f = 0 →
    ∃ c : Fin n → ℝ, ∀ t, f t = ∑ i : Fin n, c i * t ^ (i : ℕ) := by
  intro n
  induction n with
  | zero =>
    intro f _ h
    refine ⟨Fin.elim0, fun t => ?_⟩
    rw [iteratedDeriv_zero] at h
    simp [h]
  | succ n ih =>
    intro f hf h
    have h1 : ContDiff ℝ ((n : WithTop ℕ∞) + 1) f := by exact_mod_cast hf
    obtain ⟨hdiff, -, hd⟩ := contDiff_succ_iff_deriv.1 h1
    obtain ⟨c, hc⟩ := ih (deriv f) hd (by rw [← iteratedDeriv_succ']; exact h)
    set F : ℝ → ℝ := fun t => ∑ i : Fin n, c i / ((i : ℝ) + 1) * t ^ ((i : ℕ) + 1) with hFdef
    have hF : ∀ t, HasDerivAt F (deriv f t) t := by
      intro t
      have h2 := HasDerivAt.sum (u := Finset.univ) fun (i : Fin n) _ =>
        ((hasDerivAt_pow ((i : ℕ) + 1) t).const_mul (c i / ((i : ℝ) + 1)))
      rw [hc t]
      convert h2 using 1
      · funext s
        simp [hFdef]
      · refine Finset.sum_congr rfl fun i _ => ?_
        have : ((i : ℝ) + 1) ≠ 0 := by positivity
        push_cast
        rw [← mul_assoc, div_mul_cancel₀ _ this]
    have hconst : ∀ t, f t - F t = f 0 - F 0 := by
      intro t
      refine is_const_of_deriv_eq_zero (f := fun s => f s - F s)
        (fun s => ((hdiff s).hasDerivAt.fun_sub (hF s)).differentiableAt) (fun s => ?_) t 0
      rw [((hdiff s).hasDerivAt.fun_sub (hF s)).deriv, sub_self]
    have hF0 : F 0 = 0 := by simp [hFdef]
    refine ⟨Fin.cons (f 0) fun i => c i / ((i : ℝ) + 1), fun t => ?_⟩
    rw [Fin.sum_univ_succ]
    have h3 := hconst t
    rw [hF0, sub_zero] at h3
    simp only [Fin.cons_zero, Fin.cons_succ, Fin.val_zero, pow_zero, mul_one, Fin.val_succ]
    linarith [show F t = ∑ i : Fin n, c i / ((i : ℝ) + 1) * t ^ ((i : ℕ) + 1) from rfl]

/-- **Lemma A.5 of the absorb paper (Vanishing sums of ridge functions):** for nonzero, pairwise
non-collinear `a_1, …, a_r` and `g_1, …, g_r : ℝ → ℝ^q` that are `r − 1` times continuously
differentiable with `∑_i g_i(a_i · x) = 0` for all `x`, every coordinate of every `g_i` is a
polynomial of degree at most `r − 2` (of degree less than `r − 1`). -/
theorem exists_polynomial_of_sum_ridge_eq_zero {d q : Type*} [Fintype d] [Fintype q] {r : ℕ}
    (a : Fin r → d → ℝ) (ha : ∀ i, a i ≠ 0) (hcol : ∀ i j, i ≠ j → ∀ c : ℝ, a i ≠ c • a j)
    (g : Fin r → ℝ → q → ℝ) (hg : ∀ i, ContDiff ℝ (r - 1 : ℕ) (g i))
    (hsum : ∀ x : d → ℝ, ∑ i, g i (a i ⬝ᵥ x) = 0) (i : Fin r) (k : q) :
    ∃ P : Polynomial ℝ, P.degree < ((r - 1 : ℕ) : WithBot ℕ) ∧ ∀ t, g i t k = P.eval t := by
  have hr := i.pos
  have hcoord := iteratedDeriv_eq_zero_rf a (r - 1) Finset.univ (fun l t => g l t k)
    (by rw [Finset.card_univ, Fintype.card_fin]; omega) (fun l _ => ha l)
    (fun l _ j _ h => hcol l j h) (fun l _ => contDiff_pi.1 (hg l) k)
    (fun x => by simpa [Finset.sum_apply] using congrFun (hsum x) k) i (Finset.mem_univ i)
  obtain ⟨c, hc⟩ := exists_coeffs_rf (r - 1) _ (contDiff_pi.1 (hg i) k) hcoord
  refine ⟨∑ l : Fin (r - 1), Polynomial.C (c l) * Polynomial.X ^ (l : ℕ),
    Polynomial.degree_sum_fin_lt c, fun t => ?_⟩
  rw [hc t]
  simp [Polynomial.eval_finsetSum]


/-- **Lemma A.6 of the absorb paper (Distinct scales):** let `ψ` be real-analytic and not a
polynomial, `α_1, …, α_n > 0` distinct and `a_1, …, a_n ∈ ℝ^q`. If every coordinate of
`∑_k a_k ψ(α_k t)` is a polynomial in `t`, then every `a_k` is zero. -/
theorem eq_zero_of_sum_smul_scaled_eq_polynomial {q : Type*} {n : ℕ} (ψ : ℝ → ℝ)
    (hψ : AnalyticOnNhd ℝ ψ Set.univ) (hnp : ¬ ∃ P : Polynomial ℝ, ∀ t, ψ t = P.eval t)
    (α : Fin n → ℝ) (hα : ∀ k, 0 < α k) (hinj : Function.Injective α) (a : Fin n → q → ℝ)
    (hP : ∀ j : q, ∃ P : Polynomial ℝ, ∀ t, ∑ k, a k j * ψ (α k * t) = P.eval t) :
    ∀ k, a k = 0 := by
  sorry

end Skips
