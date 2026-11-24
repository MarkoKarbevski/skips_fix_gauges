import SkipsLean.Depth.SuffixRows
import SkipsLean.Depth.ComplexBlockIdentity

/-!
# Lemma D.17 for a complex row `b`

Paper (dimension paper): Appendix D.6 (the case `ε = 0`), Lemma D.17 (A change of the reads moves
the output). "In the case (0), let `θ` be regular with (S1) for block `k + 1`, let
`V = W_write^{k+1}` have the rows `a_1, …, a_q`, and let `b ∈ ℂ^{1×q}`. If

  `𝐃𝓑_{>k+1}(w̃V) (((1 − w̃²) ⊙ b) V) = 0`

for all `w̃` in a nonempty open subset of `ℝ^{1×q}`, where `1 − w̃²` is the row with the entries
`1 − w̃_j²`, then `b = 0`."

Its proof begins: "At real `w̃` the derivative is a real linear map, so the real and the imaginary
part of `b` satisfy the hypothesis: let `b` be real." The case of a real `b` is
`eq_zero_of_fderiv_suffix_one_sub_sq_zero` (`Depth/StepZeroValues.lean`).

Here `𝐃𝓑_{>k+1}` at the complex direction `((1 − w̃²) ⊙ b) V` is the complex derivative of
`suffixC σC` (`Depth/ComplexSuffix.lean`), for a map `σC` that extends the activation and a cone
`C_κ` on which `𝓑_{>k+1}` is holomorphic. The paper's rows `w̃` and `b` are rows `hid k → ℝ` and
`hid k → ℂ`, and the hidden state has the same row `w̃V` at every token. Numbering as in
`Depth/StepTanh.lean`: the block is `k : Fin L`, the paper's block `k + 1`.
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut] {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)] {σ : ℝ → ℝ} {σC : ℂ → ℂ}

/-- Helper (step 1): if `V ≠ 0`, a nonempty open set `O` of rows contains a nonempty open set of
rows `r` with `r V ≠ 0`. -/
private lemma exists_open_vecMul_ne_zero_cos {m n : Type*} [Fintype m] (V : Matrix m n ℝ)
    (hV : V ≠ 0) (O : Set (m → ℝ)) (hO : IsOpen O) (hne : O.Nonempty) :
    ∃ O' ⊆ O, IsOpen O' ∧ O'.Nonempty ∧ ∀ r ∈ O', r ᵥ* V ≠ 0 := by
  classical
  refine ⟨O ∩ {r | r ᵥ* V ≠ 0}, Set.inter_subset_left, ?_, ?_, fun r hr => hr.2⟩
  · exact hO.inter (isOpen_ne_fun (continuous_id.matrix_vecMul continuous_const) continuous_const)
  · obtain ⟨r₀, hr₀⟩ := hne
    -- a row `y` with `y V ≠ 0`, since `V ≠ 0`
    obtain ⟨y, hy⟩ : ∃ y : m → ℝ, y ᵥ* V ≠ 0 := by
      by_contra hcon
      push Not at hcon
      apply hV
      ext i j
      have := congr_fun (hcon (Pi.single i 1)) j
      simpa [Matrix.single_one_vecMul] using this
    by_cases h0 : r₀ ᵥ* V = 0
    · -- `(r₀ + s y) V = s (y V) ≠ 0` for `s ≠ 0`, and `r₀ + s y ∈ O` for small `s`
      have hc : Continuous fun s : ℝ => r₀ + s • y := by fun_prop
      have hev : ∀ᶠ s in nhds (0 : ℝ), r₀ + s • y ∈ O :=
        hc.continuousAt.preimage_mem_nhds (by simpa using hO.mem_nhds hr₀)
      have hev' : ∀ᶠ s in nhdsWithin (0 : ℝ) {0}ᶜ, r₀ + s • y ∈ O := nhdsWithin_le_nhds hev
      obtain ⟨s, hs, hs0⟩ := (hev'.and (self_mem_nhdsWithin (s := {(0 : ℝ)}ᶜ))).exists
      refine ⟨r₀ + s • y, hs, ?_⟩
      show (r₀ + s • y) ᵥ* V ≠ 0
      rw [Matrix.add_vecMul, Matrix.smul_vecMul, h0, zero_add]
      exact smul_ne_zero hs0 hy
    · exact ⟨r₀, hr₀, h0⟩

/-- Helper (step 3): for a real row `c`, if `𝐃𝓑_{>k+1}(rV)(((1 − r²) ⊙ c) V) = 0` for every row
`r` of a nonempty open set `O` with `rV ≠ 0`, then `c = 0` (the case of a real `b`, applied to the
matrices whose rows all lie in `O`, row by row). -/
private lemma eq_zero_of_rows_cos [Nonempty T] (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
    (hθ : RegularZero (Arch.mlp σ (rmsNorm 0) hid) θ) (hd : 2 ≤ Fintype.card d) (k : Fin L)
    (hS1 : ∀ i j : hid k, i ≠ j → ∀ a c : ℝ, a • θ.write k i + c • θ.write k j = 0 →
      a = 0 ∧ c = 0)
    (c : hid k → ℝ) (O : Set (hid k → ℝ)) (hO : IsOpen O) (hne : O.Nonempty)
    (hOV : ∀ r ∈ O, r ᵥ* θ.write k ≠ 0)
    (h : ∀ r ∈ O,
      fderiv ℝ (fun h' : Matrix T d ℝ => suffix (Arch.mlp σ (rmsNorm 0) hid) 0 θ k.succ h')
        ((Matrix.of fun (_ : T) => r) * θ.write k)
        ((Matrix.of fun (_ : T) (j : hid k) => (1 - r j ^ 2) * c j) * θ.write k) = 0) :
    c = 0 := by
  -- the matrices whose rows all lie in `O`: open and nonempty
  have hPo : IsOpen (Set.univ.pi fun _ : T => O : Set (Matrix T (hid k) ℝ)) :=
    isOpen_set_pi Set.finite_univ fun _ _ => hO
  obtain ⟨r₀, hr₀⟩ := hne
  have hPne : (Set.univ.pi fun _ : T => O : Set (Matrix T (hid k) ℝ)).Nonempty :=
    ⟨Matrix.of fun _ => r₀, fun _ _ => hr₀⟩
  have key := eq_zero_of_fderiv_suffix_one_sub_sq_zero hσa θ hθ hd k hS1
    (Matrix.of fun (_ : T) => c) _ hPo hPne (fun w hw => ?_)
  · obtain ⟨t₀⟩ := ‹Nonempty T›
    funext j
    exact congr_fun (congr_fun key t₀) j
  · -- row `t` of the derivative at `wV` is row `t` of the derivative at `(w_t, …, w_t) V`
    have hrow : ∀ t, w t ∈ O := fun t => hw t (Set.mem_univ t)
    have hh : ∀ t, (w * θ.write k) t ≠ 0 := fun t => hOV _ (hrow t)
    funext t
    have e := fderiv_suffix_zero_row hσa θ hθ k.succ (w * θ.write k)
      ((Matrix.of fun t j => (1 - w t j ^ 2) * c j) * θ.write k) hh t
    refine e.trans ?_
    have e1 : (Matrix.of fun _ => (w * θ.write k) t)
        = (Matrix.of fun (_ : T) => w t) * θ.write k := by
      ext s i; rfl
    have e2 : (Matrix.of fun _ =>
          ((Matrix.of fun t j => (1 - w t j ^ 2) * c j) * θ.write k : Matrix T d ℝ) t)
        = (Matrix.of fun (_ : T) (j : hid k) => (1 - w t j ^ 2) * c j) * θ.write k := by
      ext s i; rfl
    rw [e1, e2, h (w t) (hrow t)]

/-- **Lemma D.17 of the dimension paper (a change of the reads moves the output).** In the case
(0), let the blocks be real-analytic MLP blocks whose activation is extended by `σC`, `d ≥ 2`, `θ`
regular, any two rows of the write `V` of block `k` linearly independent (S1), and `𝓑_{>k+1}`
holomorphic on a cone `C_κ`. For a complex row `b`: if `𝐃𝓑(w̃ V)(((1 − w̃²) ⊙ b) V) = 0` for all
real rows `w̃` in a nonempty open set, then `b = 0`. -/
theorem eq_zero_of_fderiv_suffixC_one_sub_sq [Nonempty T] (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (hσ : ∀ x : ℝ, σC (x : ℂ) = ((σ x : ℝ) : ℂ))
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
    (hθ : RegularZero (Arch.mlp σ (rmsNorm 0) hid) θ) (hd : 2 ≤ Fintype.card d) (k : Fin L)
    (hS1 : ∀ i j : hid k, i ≠ j → ∀ a c : ℝ, a • θ.write k i + c • θ.write k j = 0 →
      a = 0 ∧ c = 0)
    {κ : ℝ} (hκ : 0 < κ) (hhol : HolomorphicOnCone σC θ k.succ κ)
    (b : hid k → ℂ) (O : Set (hid k → ℝ)) (hO : IsOpen O) (hne : O.Nonempty)
    (h : ∀ r ∈ O,
      fderiv ℂ (fun h' : Matrix T d ℂ => suffixC σC θ.toC k.succ h')
        ((Matrix.of fun (_ : T) (j : hid k) => (r j : ℂ)) * θ.toC.2.1 k)
        ((Matrix.of fun (_ : T) (j : hid k) => (1 - (r j : ℂ) ^ 2) * b j) * θ.toC.2.1 k) = 0) :
    b = 0 := by
  -- (1) `V ≠ 0` (its rank is `d ≥ 2`), so `O' := O ∩ {r | rV ≠ 0}` is open and nonempty
  have hV0 : θ.write k ≠ 0 := by
    intro h0
    have h1 := hθ.rank_write k
    rw [h0, Matrix.rank_zero] at h1
    omega
  obtain ⟨O', hO'O, hO'o, hO'ne, hO'V⟩ := exists_open_vecMul_ne_zero_cos _ hV0 O hO hne
  have hVc : θ.toC.2.1 k = (θ.write k).map (fun x : ℝ => (x : ℂ)) := rfl
  -- (2) at a real row `r ∈ O'` the complex derivative is the real one: with `b = re b + i im b`,
  -- the real and the imaginary part of `b` satisfy the hypothesis
  have hparts : ∀ r ∈ O',
      fderiv ℝ (fun h' : Matrix T d ℝ => suffix (Arch.mlp σ (rmsNorm 0) hid) 0 θ k.succ h')
        ((Matrix.of fun (_ : T) => r) * θ.write k)
        ((Matrix.of fun (_ : T) (j : hid k) => (1 - r j ^ 2) * (b j).re) * θ.write k) = 0 ∧
      fderiv ℝ (fun h' : Matrix T d ℝ => suffix (Arch.mlp σ (rmsNorm 0) hid) 0 θ k.succ h')
        ((Matrix.of fun (_ : T) => r) * θ.write k)
        ((Matrix.of fun (_ : T) (j : hid k) => (1 - r j ^ 2) * (b j).im) * θ.write k) = 0 := by
    intro r hr
    have hr' := h r (hO'O hr)
    have hh : ∀ t, ((Matrix.of fun (_ : T) => r) * θ.write k) t ≠ 0 := fun _ => hO'V r hr
    -- the point is real
    have e1 : (Matrix.of fun (_ : T) (j : hid k) => (r j : ℂ)) * θ.toC.2.1 k
        = ((Matrix.of fun (_ : T) => r) * θ.write k).map (fun x : ℝ => (x : ℂ)) := by
      rw [hVc]
      ext s i
      simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.of_apply]
      push_cast
      rfl
    -- the direction is a real direction plus `i` times a real direction
    have e2 : (Matrix.of fun (_ : T) (j : hid k) => (1 - (r j : ℂ) ^ 2) * b j) * θ.toC.2.1 k
        = ((Matrix.of fun (_ : T) (j : hid k) => (1 - r j ^ 2) * (b j).re) * θ.write k).map
            (fun x : ℝ => (x : ℂ))
          + Complex.I • ((Matrix.of fun (_ : T) (j : hid k) => (1 - r j ^ 2) * (b j).im) *
            θ.write k).map (fun x : ℝ => (x : ℂ)) := by
      rw [hVc]
      ext s i
      simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply, Matrix.map_apply,
        Matrix.of_apply, smul_eq_mul]
      push_cast
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      conv_lhs => rw [← Complex.re_add_im (b j)]
      ring
    rw [e1, e2, map_add, map_smul, fderiv_suffixC_ofReal hσ θ k.succ hκ hhol _ _ hh,
      fderiv_suffixC_ofReal hσ θ k.succ hκ hhol _ _ hh] at hr'
    -- real and imaginary parts, entry by entry
    constructor
    · ext t i
      have := congr_arg Complex.re (congr_fun (congr_fun hr' t) i)
      simpa using this
    · ext t i
      have := congr_arg Complex.im (congr_fun (congr_fun hr' t) i)
      simpa using this
  -- (3) the real case, for the real and the imaginary part
  have hre := eq_zero_of_rows_cos hσa θ hθ hd k hS1 (fun j => (b j).re) O' hO'o hO'ne hO'V
    fun r hr => (hparts r hr).1
  have him := eq_zero_of_rows_cos hσa θ hθ hd k hS1 (fun j => (b j).im) O' hO'o hO'ne hO'V
    fun r hr => (hparts r hr).2
  -- (4) `b = 0`
  funext j
  exact Complex.ext (congr_fun hre j) (congr_fun him j)

end Skips
