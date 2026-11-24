import SkipsLean.Residual.SkiplessAll
import SkipsLean.Residual.DifferentClassesCriterion
import SkipsLean.Residual.PointwiseLimitUnion
import SkipsLean.Residual.DepthMlp
import SkipsLean.Dimension.ParameterCount

/-!
# Too few extra hidden units

Paper (skips paper): Theorem 4.11 (ii), which is Theorem A.28 (iii) with (iv) in the setting of
the main text (every MLP block has at least `d` hidden units, Section 2). "For networks of GELU
blocks without normalization, a residual network of `L` blocks at generic parameters equals no
skipless network of `L` blocks with, in total, fewer than `L d_model / 2` more hidden units, and is
not a pointwise limit of such networks."

The proof of Theorem A.28 (iii): "The skipless network then has
`P' = P + 2 d_model ∑_ℓ (d'_hidden,ℓ - d_hidden,ℓ)` parameters, and its changes of basis at
`h_0, …, h_L` have orbits of dimension `(L + 1) d_model²` at generic parameters (Lemma A.18). By
Lemma A.27 the residual network has functional dimension `P - d_model²` at some parameters, which
exceeds `P' - (L + 1) d_model²` exactly when `∑_ℓ (d'_hidden,ℓ - d_hidden,ℓ) < L d_model / 2`. For
each of the finitely many such choices of widths, Lemma A.26 gives a set of weights of measure
zero, and so does their union." And of (iv): "this covers the finitely many choices of widths with
every `d'_hidden,ℓ ≥ d_model`, on the same batch, and the smallest of their `δ` serves for all."

Here: the residual network has the hidden units `hid ℓ` (any widths), the skipless network the
hidden units `hid' ℓ` with `d ≤ |hid' ℓ|`, and "fewer than `L d / 2` more hidden units in total" is
`2 ∑_ℓ |hid' ℓ| < 2 ∑_ℓ |hid ℓ| + L d`. In the statements for all widths at once the skipless
network of widths `m : Fin L → ℕ` has the hidden units `Fin (m ℓ)`. Sard's theorem and the property
of definable sets are hypotheses from the literature (`Literature/Sard.lean`,
`Literature/OMinimal.lean`). Not stated: skipless blocks with fewer than `d` hidden units
(Theorem A.28 (iii), outside the setting of the main text).
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d]
  [Fintype dIn] [Fintype dOut] {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]

section OneChoiceOfWidths

variable {hid' : Fin L → Type} [∀ ℓ, Fintype (hid' ℓ)] {σ σ' : ℝ → ℝ}

/-- The two ingredients of Lemma A.26 for the proof of Theorem A.28 (iii): a bound
`r₀ = P' - (L + 1) d²` on the rank of the Jacobian of the skipless network at every parameter and
on every batch, and one residual parameter `θ₀` whose functional dimension `P - d²` exceeds it,
as `P' = P + 2 d ∑_ℓ (d'_hidden,ℓ - d_hidden,ℓ)` and `2 ∑_ℓ (d'_hidden,ℓ - d_hidden,ℓ) < L d`. -/
private theorem exists_rank_gap_mlp_fh
    (hσ : ∀ z, HasDerivAt σ (σ' z) z) (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (hU : UnitsRigid σ σ' dIn dOut (Σ ℓ, hid ℓ))
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hhid' : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid' ℓ))
    (hk : 2 * ∑ ℓ, Fintype.card (hid' ℓ) < 2 * ∑ ℓ, Fintype.card (hid ℓ) + L * Fintype.card d) :
    ∃ r₀ : ℕ, (∀ (n : ℕ) (X : Fin n → Matrix T dIn ℝ)
        (η : Params (Arch.mlp (T := T) (d := d) σ id hid') dIn dOut),
        jacobianRank (Arch.mlp σ id hid') 0 X η ≤ r₀) ∧
      ∃ θ₀ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut,
        r₀ < funDim (Arch.mlp σ id hid) 1 θ₀ := by
  have hf' : ∀ ℓ, AnalyticOnNhd ℝ ((Arch.mlp (T := T) (d := d) σ id hid').f ℓ) Set.univ :=
    fun ℓ => analyticOnNhd_f_mlp hσa ℓ
  -- one residual parameter `θ₀` of functional dimension `P - d²` (Theorem 4.7)
  obtain ⟨θ₀, hθ₀⟩ := (ae_funDim_mlp_residual hσ hσa hU μ hd hdIn hdOut).exists
  -- the skipless network has rank at most `P' - (L + 1) d²` at every parameter, on every batch
  have hbound := fun (n : ℕ) (X : Fin n → Matrix T dIn ℝ)
      (η : Params (Arch.mlp (T := T) (d := d) σ id hid') dIn dOut) =>
    jacobianRank_add_le_skipless_all rfl hf' hdIn hhid' η X
  have h0 := hbound 0 (fun i => i.elim0) 0
  -- the numbers of parameters `P = c + 2 d a` and `P' = c + 2 d b`
  have hP := finrank_params_mlp (T := T) (d := d) (dIn := dIn) (dOut := dOut) σ id hid
  have hP' := finrank_params_mlp (T := T) (d := d) (dIn := dIn) (dOut := dOut) σ id hid'
  -- `2 d b < 2 d a + L d²`, from `2 b < 2 a + L d`
  have hkd : 2 * Fintype.card d * ∑ ℓ, Fintype.card (hid' ℓ)
      < 2 * Fintype.card d * ∑ ℓ, Fintype.card (hid ℓ) + L * Fintype.card d ^ 2 := by
    have := Nat.mul_lt_mul_of_pos_left hk (show 0 < Fintype.card d by omega)
    nlinarith [this]
  have hL1 : (L + 1) * Fintype.card d ^ 2 = L * Fintype.card d ^ 2 + Fintype.card d ^ 2 := by
    ring
  -- so `P' - (L + 1) d² < P - d²`
  refine ⟨Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) σ id hid') dIn dOut)
    - (L + 1) * Fintype.card d ^ 2, fun n X η => ?_, θ₀, by omega⟩
  have := hbound n X η
  omega

/-- **Theorem A.28 (iii) of the skips paper for one choice of widths, for MLP blocks whose hidden
units have no symmetry, without normalization, given Sard's theorem:** with `d_in, d_out ≥ d ≥ 2`,
if every block of the skipless network has at least `d` hidden units and the skipless network has,
in total, fewer than `L d / 2` more hidden units than the residual network, then at generic
parameters the residual network computes a function that no skipless network of these widths
computes. -/
theorem ae_forall_eval_residual_ne_skipless_mlp_of_card_lt
    (hSard : ∀ r : ℕ, SardCriticalValues
      (Params (Arch.mlp (T := T) (d := d) σ id hid') dIn dOut) (Fin r → ℝ))
    (hσ : ∀ z, HasDerivAt σ (σ' z) z) (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (hU : UnitsRigid σ σ' dIn dOut (Σ ℓ, hid ℓ))
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hhid' : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid' ℓ))
    (hk : 2 * ∑ ℓ, Fintype.card (hid' ℓ) < 2 * ∑ ℓ, Fintype.card (hid ℓ) + L * Fintype.card d) :
    ∀ᵐ θ ∂μ, ∀ η : Params (Arch.mlp (T := T) (d := d) σ id hid') dIn dOut,
      eval (Arch.mlp σ id hid) 1 θ ≠ eval (Arch.mlp σ id hid') 0 η := by
  -- Lemma A.26 (i) with `F` the residual and `G` the skipless networks of widths `hid'`
  obtain ⟨r₀, hr₀, θ₀, hθ₀⟩ := exists_rank_gap_mlp_fh hσ hσa hU μ hd hdIn hdOut hhid' hk
  exact ae_forall_eval_ne_of_jacobianRank_lt (Arch.mlp (T := T) (d := d) σ id hid) 1
    (Arch.mlp (T := T) (d := d) σ id hid') 0 hSard (fun ℓ => analyticOnNhd_f_mlp hσa ℓ)
    analyticOnNhd_id (fun ℓ => analyticOnNhd_f_mlp hσa ℓ) analyticOnNhd_id r₀ hr₀ θ₀ hθ₀ μ

/-- **Theorem A.28 (iv) of the skips paper for one choice of widths, for MLP blocks whose hidden
units have no symmetry, without normalization, given Sard's theorem and the property of definable
sets:** under the same hypotheses, at generic parameters the residual network is not a pointwise
limit of the skipless networks of these widths. -/
theorem ae_not_isPointwiseLimit_skipless_mlp_of_card_lt
    (hSard : ∀ r : ℕ, SardCriticalValues
      (Params (Arch.mlp (T := T) (d := d) σ id hid') dIn dOut) (Fin r → ℝ))
    (hOmin : ∀ (n : ℕ) (X : Fin n → Matrix T dIn ℝ),
      ClosureNullOfNull
        (Set.range (evalBatch (dOut := dOut) (Arch.mlp (T := T) (d := d) σ id hid') 0 X)))
    (hσ : ∀ z, HasDerivAt σ (σ' z) z) (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (hU : UnitsRigid σ σ' dIn dOut (Σ ℓ, hid ℓ))
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hhid' : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid' ℓ))
    (hk : 2 * ∑ ℓ, Fintype.card (hid' ℓ) < 2 * ∑ ℓ, Fintype.card (hid ℓ) + L * Fintype.card d) :
    ∀ᵐ θ ∂μ, ¬ IsPointwiseLimit
      (Set.range (eval (Arch.mlp (T := T) (d := d) σ id hid') 0 :
        Params (Arch.mlp (T := T) (d := d) σ id hid') dIn dOut →
          Matrix T dIn ℝ → Matrix T dOut ℝ))
      (eval (Arch.mlp σ id hid) 1 θ) := by
  -- Theorem A.28 (iv) with `F` the residual and `G` the skipless networks of widths `hid'`
  obtain ⟨r₀, hr₀, θ₀, hθ₀⟩ := exists_rank_gap_mlp_fh hσ hσa hU μ hd hdIn hdOut hhid' hk
  exact ae_not_isPointwiseLimit_of_jacobianRank_lt (Arch.mlp (T := T) (d := d) σ id hid) 1
    (Arch.mlp (T := T) (d := d) σ id hid') 0 hSard hOmin (fun ℓ => analyticOnNhd_f_mlp hσa ℓ)
    analyticOnNhd_id (fun ℓ => analyticOnNhd_f_mlp hσa ℓ) analyticOnNhd_id r₀ hr₀ θ₀ hθ₀ μ

end OneChoiceOfWidths

/-! ### GELU blocks, all widths at once -/

/-- **Theorem 4.11 (ii) of the skips paper, "equals no skipless network of `L` blocks with, in
total, fewer than `L d_model / 2` more hidden units", for GELU blocks without normalization, given
Sard's theorem** (Theorem A.28 (iii) for skipless blocks of at least `d` hidden units): with
`d_in, d_out ≥ d ≥ 2`, at generic parameters of the residual network, for all widths
`m_1, …, m_L ≥ d` with `2 ∑_ℓ m_ℓ < 2 ∑_ℓ d_hidden,ℓ + L d`, no skipless network of GELU blocks of
the widths `m` computes the function of the residual network. -/
theorem ae_forall_widths_eval_residual_ne_skipless_gelu
    (hSard : ∀ (m : Fin L → ℕ) (r : ℕ), SardCriticalValues
      (Params (Arch.mlp (T := T) (d := d) gelu id (fun ℓ => Fin (m ℓ))) dIn dOut) (Fin r → ℝ))
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) gelu id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, ∀ m : Fin L → ℕ, (∀ ℓ, Fintype.card d ≤ m ℓ) →
      2 * ∑ ℓ, m ℓ < 2 * ∑ ℓ, Fintype.card (hid ℓ) + L * Fintype.card d →
      ∀ η : Params (Arch.mlp (T := T) (d := d) gelu id (fun ℓ => Fin (m ℓ))) dIn dOut,
        eval (Arch.mlp gelu id hid) 1 θ ≠ eval (Arch.mlp gelu id (fun ℓ => Fin (m ℓ))) 0 η := by
  -- countably many widths `m`: it suffices to treat each one
  rw [ae_all_iff]
  intro m
  by_cases h1 : ∀ ℓ, Fintype.card d ≤ m ℓ
  · by_cases h2 : 2 * ∑ ℓ, m ℓ < 2 * ∑ ℓ, Fintype.card (hid ℓ) + L * Fintype.card d
    · -- Theorem A.28 (iii) for GELU blocks and the hidden units `Fin (m ℓ)`
      have h := ae_forall_eval_residual_ne_skipless_mlp_of_card_lt
        (hid' := fun ℓ => Fin (m ℓ)) (hSard m) hasDerivAt_gelu analyticOnNhd_gelu
        (gelu_unitsRigid _ _ _) μ hd hdIn hdOut (fun ℓ => by simpa using h1 ℓ) (by simpa using h2)
      filter_upwards [h] with θ hθ _ _ using hθ
    · exact Filter.Eventually.of_forall fun _ _ h => absurd h h2
  · exact Filter.Eventually.of_forall fun _ h => absurd h h1

/-- **Theorem 4.11 (ii) of the skips paper, "and is not a pointwise limit of such networks", for
GELU blocks without normalization, given Sard's theorem and the property of definable sets**
(Theorem A.28 (iv)): with `d_in, d_out ≥ d ≥ 2`, at generic parameters the residual network is not
a pointwise limit (Definition A.29) of the set of all skipless networks of GELU blocks of widths
`m_1, …, m_L ≥ d` with `2 ∑_ℓ m_ℓ < 2 ∑_ℓ d_hidden,ℓ + L d`. -/
theorem ae_not_isPointwiseLimit_skipless_gelu_widths
    (hSard : ∀ (m : Fin L → ℕ) (r : ℕ), SardCriticalValues
      (Params (Arch.mlp (T := T) (d := d) gelu id (fun ℓ => Fin (m ℓ))) dIn dOut) (Fin r → ℝ))
    (hOmin : ∀ (m : Fin L → ℕ) (n : ℕ) (X : Fin n → Matrix T dIn ℝ),
      ClosureNullOfNull
        (Set.range (evalBatch (dOut := dOut)
          (Arch.mlp (T := T) (d := d) gelu id (fun ℓ => Fin (m ℓ))) 0 X)))
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) gelu id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, ¬ IsPointwiseLimit
      (⋃ m ∈ {m : Fin L → ℕ | (∀ ℓ, Fintype.card d ≤ m ℓ) ∧
          2 * ∑ ℓ, m ℓ < 2 * ∑ ℓ, Fintype.card (hid ℓ) + L * Fintype.card d},
        Set.range (eval (Arch.mlp (T := T) (d := d) gelu id (fun ℓ => Fin (m ℓ))) 0 :
          Params (Arch.mlp (T := T) (d := d) gelu id (fun ℓ => Fin (m ℓ))) dIn dOut →
            Matrix T dIn ℝ → Matrix T dOut ℝ))
      (eval (Arch.mlp gelu id hid) 1 θ) := by
  set B := 2 * ∑ ℓ, Fintype.card (hid ℓ) + L * Fintype.card d
  set s := {m : Fin L → ℕ | (∀ ℓ, Fintype.card d ≤ m ℓ) ∧ 2 * ∑ ℓ, m ℓ < B}
  -- finitely many widths: every `m ∈ s` has `m ℓ ≤ ∑ m < B`
  have hs : s.Finite := by
    refine (Set.Finite.pi (t := fun _ : Fin L => Set.Iic B) fun _ => Set.finite_Iic B).subset ?_
    intro m hm ℓ _
    have := Finset.single_le_sum (f := m) (fun i _ => Nat.zero_le (m i)) (Finset.mem_univ ℓ)
    show m ℓ ≤ B
    have := hm.2
    omega
  -- for almost every `θ`, the residual network is a pointwise limit of no family of widths `m ∈ s`
  have hall : ∀ᵐ θ ∂μ, ∀ m : Fin L → ℕ, m ∈ s → ¬ IsPointwiseLimit
      (Set.range (eval (Arch.mlp (T := T) (d := d) gelu id (fun ℓ => Fin (m ℓ))) 0 :
        Params (Arch.mlp (T := T) (d := d) gelu id (fun ℓ => Fin (m ℓ))) dIn dOut →
          Matrix T dIn ℝ → Matrix T dOut ℝ))
      (eval (Arch.mlp gelu id hid) 1 θ) := by
    rw [ae_all_iff]
    intro m
    by_cases hm : m ∈ s
    · -- Theorem A.28 (iv) for GELU blocks and the hidden units `Fin (m ℓ)`
      have h := ae_not_isPointwiseLimit_skipless_mlp_of_card_lt
        (hid' := fun ℓ => Fin (m ℓ)) (hSard m) (hOmin m) hasDerivAt_gelu analyticOnNhd_gelu
        (gelu_unitsRigid _ _ _) μ hd hdIn hdOut (fun ℓ => by simpa using hm.1 ℓ)
        (by simpa using hm.2)
      filter_upwards [h] with θ hθ _ using hθ
    · exact Filter.Eventually.of_forall fun _ h => absurd h hm
  -- a pointwise limit of the finite union is a pointwise limit of one family
  filter_upwards [hall] with θ hθ hlim
  obtain ⟨m, hm, hm'⟩ := exists_isPointwiseLimit_of_biUnion_finite hs hlim
  exact hθ m hm hm'

end Skips
