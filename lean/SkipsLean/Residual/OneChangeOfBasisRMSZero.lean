import SkipsLean.Residual.OneChangeOfBasis
import SkipsLean.Dimension.UpperBoundResidualRMSNormZero

/-!
# One change of basis is left in a residual network, under pre-RMSNorm with `ε = 0`

Paper (skips paper), Theorem A.5 (iii): "One change of basis is left. Let `d_model ≥ 2`, and let
every block be nonzero for some value of its parameters. […] The map `T_G` of the embedding, the
reads, the writes and the readout preserves the function of every residual network if and only if
`G_0 = G_1 = ⋯ = G_L ∈ 𝒢`. Under RMSNorm with `ε = 0`, the same holds for
`G_ℓ = c_ℓ Q_ℓ ∈ CO(d_model)`, with `c_ℓ > 0` and `Q_ℓ` orthogonal, when `T_G` multiplies the reads
and the readout by `Q_{ℓ−1}^⊤` and `Q_L^⊤` in place of `G_{ℓ−1}^{−1}` and `G_L^{−1}`."
Theorem A.17 (i) has the same claim: "For `ε = 0`, the changes of basis in `𝒢` at the hidden
states […] preserve that of every residual network only if they agree at all hidden states."

Its proof, "Part (iii) under RMSNorm with `ε = 0`": "Fix a token, and an input and reads at which
the row of `f(N_ε(h) W_read^ℓ)` of this token is nonzero. As the write varies, the row `b` of this
token takes every value. So, with `u = h + b`, the row `c_ℓ u R + (c h − c_ℓ h R)` is a positive
multiple of `u` for every `u ≠ 0`. Large `u` give `R = I`. Then `(c − c_ℓ) h` is parallel to
every `u`, so `c_ℓ = c`."

Here, for arbitrary maps `f_ℓ`: the map `T_G` is `θ.cob G Q` (the embedding and the writes times
`G_ℓ`, the reads and the readout times `Q_ℓ⁻¹ = Q_ℓ^⊤`), with `G_ℓ = c_ℓ Q_ℓ`. The twin for
`ε > 0` is `eval_cob_residual_rmsNorm_iff` (`Residual/OneChangeOfBasis.lean`). The hypothesis on
the blocks is the one that the proof uses: for every block there are an input, an embedding, a
read and a token at which the row of `x E` and the row of the block are both nonzero. (The
paper's "nonzero for some value of its parameters" is this for the blocks of the paper; for an
arbitrary map `f_ℓ` whose output is nonzero only at tokens with a zero row of `x E`, the scale
`c_ℓ` would not be determined.) Lean's `rmsNorm 0` maps a zero row to `0`; both directions hold
with it.
-/

namespace Skips

open Matrix

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype d] [DecidableEq d] [Fintype dIn]
variable {A : Arch T d L}

/-! ### Helpers on matrices (copies of private helpers of `Residual/OneChangeOfBasis.lean`) -/

/-- Helper: `a⁻¹ (a B) = B` also for a rectangular `B`. -/
private theorem cob_inv_mul_mul_ocz {n : Type*} (a : GL d ℝ) (B : Matrix d n ℝ) :
    (↑a⁻¹ : Matrix d d ℝ) * ((a : Matrix d d ℝ) * B) = B := by
  rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]

/-- Helper: `a (a⁻¹ B) = B` also for a rectangular `B`. -/
private theorem cob_mul_inv_mul_ocz {n : Type*} (a : GL d ℝ) (B : Matrix d n ℝ) :
    (a : Matrix d d ℝ) * ((↑a⁻¹ : Matrix d d ℝ) * B) = B := by
  rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]

omit [DecidableEq d] in
/-- Helper: two hidden states with the same output for every readout `D` are equal. -/
private theorem eq_of_forall_mul_right_ocz [Nonempty dOut] {X Y : Matrix T d ℝ}
    (h : ∀ D : Matrix d dOut ℝ, X * D = Y * D) : X = Y := by
  classical
  obtain ⟨o⟩ := ‹Nonempty dOut›
  ext t k
  -- the readout `e_k e_oᵀ` reads off the column `k`
  have := congrFun (congrFun (h (Matrix.single k o 1)) t) o
  simpa only [mul_single_apply_same, mul_one] using this

omit [Fintype d] [DecidableEq d] in
/-- Helper: an input `x` and an embedding `E` such that the row of `x E` at the token `t` is
`v`. -/
private theorem exists_row_ocz [Nonempty dIn] (t : T) (v : d → ℝ) :
    ∃ (x : Matrix T dIn ℝ) (E : Matrix dIn d ℝ), (x * E) t = v := by
  classical
  obtain ⟨i⟩ := ‹Nonempty dIn›
  refine ⟨Matrix.of fun _ => Pi.single i 1, Matrix.of fun _ => v, ?_⟩
  funext k
  simp only [Matrix.mul_apply, Matrix.of_apply, Pi.single_apply, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

omit [Fintype d] [DecidableEq d] in
/-- Helper: a nonzero row `a` reaches every row `w` as `a V` for a suitable matrix `V`. -/
private theorem exists_vecMul_eq_ocz {n : Type*} [Fintype n] {a : n → ℝ} (ha : a ≠ 0)
    (w : d → ℝ) : ∃ V : Matrix n d ℝ, a ᵥ* V = w := by
  classical
  obtain ⟨j, hj⟩ := Function.ne_iff.mp ha
  have hj' : a j ≠ 0 := hj
  -- `V = e_j wᵀ / a_j`
  refine ⟨Matrix.of fun j' k => if j' = j then w k / a j else 0, ?_⟩
  funext k
  simp only [Matrix.vecMul, dotProduct, Matrix.of_apply, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  field_simp

/-! ### Hidden states when all writes but one vanish (copies from `OneChangeOfBasis.lean`) -/

/-- Helper: in a residual network whose writes are all zero, every hidden state is `x E`. -/
private theorem hidden_of_write_eq_zero_ocz (θ : Params A dIn dOut) (x : Matrix T dIn ℝ)
    (hw : ∀ k, θ.write k = 0) (j : Fin (L + 1)) : hidden A 1 θ x j = x * θ.E := by
  induction j using Fin.induction with
  | zero => exact hidden_zero A 1 θ x
  | succ k ih =>
    rw [hidden_succ, ih, hw k, Matrix.mul_zero, add_zero, Pi.one_apply, Matrix.mul_one]

/-- Helper: in a residual network whose writes vanish except that of block `ℓ₀`, the hidden
states are `x E` up to block `ℓ₀` and `x E + f_ℓ₀(χ(x E) W_read^ℓ₀) W_write^ℓ₀` after it. -/
private theorem hidden_single_write_ocz (θ : Params A dIn dOut) (x : Matrix T dIn ℝ)
    (ℓ₀ : Fin L) (hw : ∀ k, k ≠ ℓ₀ → θ.write k = 0) (j : Fin (L + 1)) :
    hidden A 1 θ x j = if (j : ℕ) ≤ ℓ₀ then x * θ.E
      else x * θ.E + A.f ℓ₀ (A.χ (x * θ.E) * θ.read ℓ₀) * θ.write ℓ₀ := by
  induction j using Fin.induction with
  | zero => simp only [hidden_zero, Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_le, ↓reduceIte]
  | succ k ih =>
    rw [hidden_succ, ih, Pi.one_apply, Matrix.mul_one]
    by_cases hk : k = ℓ₀
    · -- block `ℓ₀` itself: its input is `x E`
      subst hk
      simp only [Fin.val_castSucc, Std.le_refl, ↓reduceIte, Fin.val_succ, add_le_iff_nonpos_right,
        nonpos_iff_eq_zero, one_ne_zero]
    · -- another block writes nothing
      rw [hw k hk, Matrix.mul_zero, add_zero]
      have e : (k : ℕ) ≠ ℓ₀ := fun e => hk (Fin.ext e)
      have e1 : ((k.castSucc : Fin (L + 1)) : ℕ) = k := Fin.val_castSucc k
      have e2 : ((k.succ : Fin (L + 1)) : ℕ) = k + 1 := Fin.val_succ k
      split_ifs <;> first | rfl | (exfalso; omega)

/-- Helper: the last hidden state when all writes but that of block `ℓ₀` vanish. -/
private theorem hidden_last_single_write_ocz (θ : Params A dIn dOut) (x : Matrix T dIn ℝ)
    (ℓ₀ : Fin L) (hw : ∀ k, k ≠ ℓ₀ → θ.write k = 0) :
    hidden A 1 θ x (Fin.last L) =
      x * θ.E + A.f ℓ₀ (A.χ (x * θ.E) * θ.read ℓ₀) * θ.write ℓ₀ := by
  rw [hidden_single_write_ocz θ x ℓ₀ hw, Fin.val_last]
  exact ite_eq_right (not_le.mpr ℓ₀.isLt)

/-! ### Rows (copies of private helpers of `Basic/RMSNormConverse.lean`, and new ones) -/

omit [Fintype d] in
/-- Helper: the basis row `e_i` is nonzero. -/
private theorem single_one_ne_zero_ocz (i : d) : (Pi.single i (1 : ℝ) : d → ℝ) ≠ 0 := by
  intro h0
  have h1 := congrFun h0 i
  rw [Pi.single_eq_same, Pi.zero_apply] at h1
  exact one_ne_zero h1

/-- Helper: an invertible matrix sends nonzero rows to nonzero rows. -/
private theorem vecMul_GL_ne_zero_ocz (G : GL d ℝ) {v : d → ℝ} (hv : v ≠ 0) :
    v ᵥ* (G : Matrix d d ℝ) ≠ 0 := by
  intro h0
  apply hv
  -- `v = (vG) G⁻¹ = 0`
  have hvG : v ᵥ* (G : Matrix d d ℝ) ᵥ* (↑G⁻¹ : Matrix d d ℝ) = v := by
    rw [Matrix.vecMul_vecMul, Units.mul_inv, Matrix.vecMul_one]
  rw [← hvG, h0, Matrix.zero_vecMul]

/-- Helper: if every row is a left eigenvector of `N`, then `N` is a multiple of `1`. -/
private theorem eq_smul_one_of_vecMul_eq_smul_ocz {N : Matrix d d ℝ}
    (h : ∀ v : d → ℝ, ∃ r : ℝ, v ᵥ* N = r • v) (i₀ : d) :
    N = N i₀ i₀ • (1 : Matrix d d ℝ) := by
  -- `e_i N = r e_i`: the row `i` of `N` vanishes off the diagonal
  have hoff : ∀ i j, i ≠ j → N i j = 0 := by
    intro i j hij
    obtain ⟨r, hr⟩ := h (Pi.single i 1)
    have hj := congrFun hr j
    rw [single_one_vecMul, Matrix.row_apply, Pi.smul_apply, Pi.single_eq_of_ne hij.symm,
      smul_zero] at hj
    exact hj
  -- `(e_i + e_j) N = μ (e_i + e_j)`: the diagonal entries at `i` and `j` both equal `μ`
  have hdiag : ∀ i j, N i i = N j j := by
    intro i j
    by_cases hij : i = j
    · rw [hij]
    obtain ⟨μ, hμ⟩ := h (Pi.single i 1 + Pi.single j 1)
    rw [Matrix.add_vecMul, single_one_vecMul, single_one_vecMul] at hμ
    have hi := congrFun hμ i
    have hj := congrFun hμ j
    simp only [Pi.add_apply, Pi.smul_apply, Matrix.row_apply, Pi.single_eq_same,
      Pi.single_eq_of_ne hij, Pi.single_eq_of_ne (Ne.symm hij), smul_eq_mul, add_zero, zero_add,
      mul_one] at hi hj
    linarith [hoff i j hij, hoff j i (Ne.symm hij)]
  ext i j
  rw [Matrix.smul_apply, smul_eq_mul]
  by_cases hij : i = j
  · subst hij
    rw [Matrix.one_apply_eq, mul_one, hdiag i i₀]
  · rw [Matrix.one_apply_ne hij, mul_zero, hoff i j hij]

omit [DecidableEq d] in
/-- Helper: the factor `(sqrt (‖v‖² / d_model))⁻¹` of `rmsRow 0` at a nonzero row is nonzero. -/
private theorem rms_scale_ne_zero_ocz {v : d → ℝ} (hv : v ≠ 0) :
    (Real.sqrt ((v ⬝ᵥ v) / (Fintype.card d : ℝ) + 0))⁻¹ ≠ 0 := by
  have h1 : 0 < v ⬝ᵥ v :=
    lt_of_le_of_ne (Finset.sum_nonneg fun i _ => mul_self_nonneg (v i))
      (Ne.symm (dotProduct_self_eq_zero.not.mpr hv))
  obtain ⟨i, -⟩ := Function.ne_iff.mp hv
  have h2 : (0 : ℝ) < Fintype.card d := by exact_mod_cast Fintype.card_pos_iff.mpr ⟨i⟩
  exact (inv_pos.mpr (Real.sqrt_pos.mpr (by positivity))).ne'

omit [DecidableEq d] in
/-- Helper: two rows with the same `rmsRow 0`, the second nonzero, are proportional. -/
private theorem exists_smul_of_rmsRow_zero_eq_ocz {p q : d → ℝ} (hq : q ≠ 0)
    (h : rmsRow 0 p = rmsRow 0 q) : ∃ r : ℝ, p = r • q := by
  unfold rmsRow at h
  have hb := rms_scale_ne_zero_ocz hq
  generalize (Real.sqrt ((p ⬝ᵥ p) / (Fintype.card d : ℝ) + 0))⁻¹ = a at h
  generalize (Real.sqrt ((q ⬝ᵥ q) / (Fintype.card d : ℝ) + 0))⁻¹ = b at h hb
  by_cases ha : a = 0
  · -- then `rmsRow 0 q = 0`, impossible for `q ≠ 0`
    rw [ha, zero_smul] at h
    exact absurd (smul_eq_zero.mp h.symm) (not_or.mpr ⟨hb, hq⟩)
  · exact ⟨a⁻¹ * b, by rw [mul_smul, ← h, smul_smul, inv_mul_cancel₀ ha, one_smul]⟩

/-- Helper (the step of Part (iii) under RMSNorm with `ε = 0`): let `d ≥ 2`, `h ≠ 0`, `G₀`
invertible, and `N_0(h G₀ + w G₁) = N_0((h + w) G₀)` for every row `w`. Then `G₁ = G₀`. -/
private theorem eq_of_rmsRow_zero_add_ocz (hd : 2 ≤ Fintype.card d) {h : d → ℝ} (hh : h ≠ 0)
    (G₀ : GL d ℝ) (G₁ : Matrix d d ℝ)
    (H : ∀ w : d → ℝ, rmsRow 0 (h ᵥ* (G₀ : Matrix d d ℝ) + w ᵥ* G₁)
      = rmsRow 0 ((h + w) ᵥ* (G₀ : Matrix d d ℝ))) :
    G₁ = (G₀ : Matrix d d ℝ) := by
  -- (1) with `u = h + w ≠ 0`: `h G₀ + (u − h) G₁` is a multiple of `u G₀ ≠ 0`
  have h1 : ∀ u : d → ℝ, u ≠ 0 →
      ∃ r : ℝ, h ᵥ* (G₀ : Matrix d d ℝ) + (u - h) ᵥ* G₁ = r • (u ᵥ* (G₀ : Matrix d d ℝ)) := by
    intro u hu
    have e := H (u - h)
    rw [show h + (u - h) = u by abel] at e
    exact exists_smul_of_rmsRow_zero_eq_ocz (vecMul_GL_ne_zero_ocz G₀ hu) e
  -- (2) at `u` and at `2u`: `u G₁ = μ (u G₀)` and `h G₀ − h G₁ = α (u G₀)`
  have h2 : ∀ u : d → ℝ, u ≠ 0 →
      (∃ μ : ℝ, u ᵥ* G₁ = μ • (u ᵥ* (G₀ : Matrix d d ℝ))) ∧
      ∃ α : ℝ, h ᵥ* (G₀ : Matrix d d ℝ) - h ᵥ* G₁ = α • (u ᵥ* (G₀ : Matrix d d ℝ)) := by
    intro u hu
    obtain ⟨r₁, e₁⟩ := h1 u hu
    obtain ⟨r₂, e₂⟩ := h1 ((2 : ℝ) • u) (smul_ne_zero two_ne_zero hu)
    rw [Matrix.sub_vecMul] at e₁ e₂
    rw [Matrix.smul_vecMul, Matrix.smul_vecMul, smul_smul] at e₂
    refine ⟨⟨2 * r₂ - r₁, funext fun k => ?_⟩, ⟨2 * r₁ - 2 * r₂, funext fun k => ?_⟩⟩
    · have a₁ := congrFun e₁ k
      have a₂ := congrFun e₂ k
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at a₁ a₂ ⊢
      linear_combination a₂ - a₁
    · have a₁ := congrFun e₁ k
      have a₂ := congrFun e₂ k
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at a₁ a₂ ⊢
      linear_combination 2 * a₁ - a₂
  -- (3) `h G₀ − h G₁ = 0`: times `G₀⁻¹` it is a multiple of `e_i` and of `e_j`, `i ≠ j`
  obtain ⟨i, j, hij⟩ := Fintype.exists_pair_of_one_lt_card (show 1 < Fintype.card d by omega)
  have hz : h ᵥ* (G₀ : Matrix d d ℝ) - h ᵥ* G₁ = 0 := by
    have hmul : ∀ u : d → ℝ, u ≠ 0 → ∃ α : ℝ,
        (h ᵥ* (G₀ : Matrix d d ℝ) - h ᵥ* G₁) ᵥ* (↑G₀⁻¹ : Matrix d d ℝ) = α • u := by
      intro u hu
      obtain ⟨-, α, hα⟩ := h2 u hu
      refine ⟨α, ?_⟩
      rw [hα, Matrix.smul_vecMul, Matrix.vecMul_vecMul, Units.mul_inv, Matrix.vecMul_one]
    obtain ⟨α, hα⟩ := hmul _ (single_one_ne_zero_ocz i)
    obtain ⟨β, hβ⟩ := hmul _ (single_one_ne_zero_ocz j)
    -- at the coordinate `i`: `α = β ⋅ 0`
    have hα0 : α = 0 := by
      have e := congrFun (hα.symm.trans hβ) i
      simpa only [Pi.smul_apply, Pi.single_eq_same, Pi.single_eq_of_ne hij, smul_eq_mul,
        mul_one, mul_zero] using e
    calc h ᵥ* (G₀ : Matrix d d ℝ) - h ᵥ* G₁
        = (h ᵥ* (G₀ : Matrix d d ℝ) - h ᵥ* G₁) ᵥ* (↑G₀⁻¹ : Matrix d d ℝ)
            ᵥ* (G₀ : Matrix d d ℝ) := by
          rw [Matrix.vecMul_vecMul, Units.inv_mul, Matrix.vecMul_one]
      _ = 0 := by rw [hα, hα0, zero_smul, Matrix.zero_vecMul]
  -- (4) every row is a left eigenvector of `G₁ G₀⁻¹`, so `G₁ G₀⁻¹ = μ 1` and `G₁ = μ G₀`
  have hall : ∀ u : d → ℝ, ∃ μ : ℝ, u ᵥ* (G₁ * (↑G₀⁻¹ : Matrix d d ℝ)) = μ • u := by
    intro u
    by_cases hu : u = 0
    · exact ⟨0, by rw [hu, Matrix.zero_vecMul, smul_zero]⟩
    obtain ⟨⟨μ, hμ⟩, -⟩ := h2 u hu
    refine ⟨μ, ?_⟩
    rw [← Matrix.vecMul_vecMul, hμ, Matrix.smul_vecMul, Matrix.vecMul_vecMul, Units.mul_inv,
      Matrix.vecMul_one]
  have hN := eq_smul_one_of_vecMul_eq_smul_ocz hall i
  generalize (G₁ * (↑G₀⁻¹ : Matrix d d ℝ)) i i = μ at hN
  have hG₁ : G₁ = μ • (G₀ : Matrix d d ℝ) := by
    calc G₁ = G₁ * (↑G₀⁻¹ : Matrix d d ℝ) * (G₀ : Matrix d d ℝ) := by
          rw [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
      _ = μ • (G₀ : Matrix d d ℝ) := by rw [hN, Matrix.smul_mul, Matrix.one_mul]
  -- (5) `h G₀ = h G₁ = μ (h G₀)` with `h G₀ ≠ 0`, so `μ = 1`
  rw [hG₁, Matrix.vecMul_smul, sub_eq_zero] at hz
  have hμ : (1 - μ) • (h ᵥ* (G₀ : Matrix d d ℝ)) = 0 := by
    rw [sub_smul, one_smul, ← hz, sub_self]
  have hμ1 : μ = 1 := by
    have := (smul_eq_zero.mp hμ).resolve_right (vecMul_GL_ne_zero_ocz G₀ hh)
    linarith
  rw [hG₁, hμ1, one_smul]

/-! ### The theorems -/

/-- **Theorem A.5 (iii) of the skips paper under RMSNorm with `ε = 0`, "only if" (also the last
clause of Theorem A.17 (i)):** let `d ≥ 2`, let every block have an input, an embedding, a read
and a token at which the row of `x E` and the row of the block are nonzero, and let
`G_ℓ = c_ℓ Q_ℓ` with `c_ℓ > 0` and `Q_ℓ` orthogonal. If `θ.cob G Q` has the same function as `θ`
for every residual network `θ`, then `G_0 = G_1 = ⋯ = G_L`. -/
theorem cob_eq_of_eval_cob_residual_rmsNorm_zero [Nonempty T] [Nonempty dIn] [Nonempty dOut]
    (hA : A.χ = rmsNorm 0) (hd : 2 ≤ Fintype.card d)
    (hne : ∀ ℓ, ∃ (x : Matrix T dIn ℝ) (E : Matrix dIn d ℝ) (W : Matrix d (A.r ℓ) ℝ) (t : T),
      (x * E) t ≠ 0 ∧ A.f ℓ (rmsNorm 0 (x * E) * W) t ≠ 0)
    (G Q : Fin (L + 1) → GL d ℝ) (c : Fin (L + 1) → ℝ) (hc : ∀ ℓ, 0 < c ℓ)
    (hQ : ∀ ℓ, (Q ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ)
    (hG : ∀ ℓ, (G ℓ : Matrix d d ℝ) = c ℓ • (Q ℓ : Matrix d d ℝ))
    (h : ∀ (θ : Params A dIn dOut) (x : Matrix T dIn ℝ),
      eval A 1 (θ.cob G Q) x = eval A 1 θ x) :
    ∀ ℓ, G ℓ = G 0 := by
  classical
  obtain ⟨t₀⟩ := ‹Nonempty T›
  -- (a) With all writes zero the outputs are `N_0(x E G_0) Q_L⁻¹ D = N_0(x E) Q_0 Q_L⁻¹ D` and
  -- `N_0(x E) D`, so `Q_L = Q_0`: compare the rows `N_0(e_k) Q_0` and `N_0(e_k) Q_L`.
  have hL : Q (Fin.last L) = Q 0 := by
    apply Units.ext
    refine Matrix.ext_of_single_vecMul fun k => ?_
    obtain ⟨x, E, hxE⟩ := exists_row_ocz (dIn := dIn) t₀ (Pi.single k (1 : ℝ))
    have hmat : rmsNorm 0 (x * E) * (Q (Fin.last L) : Matrix d d ℝ)
        = rmsNorm 0 (x * E) * (Q 0 : Matrix d d ℝ) := by
      refine eq_of_forall_mul_right_ocz (dOut := dOut) fun D => ?_
      -- the readout `Q_L D`
      let θ : Params A dIn dOut := ⟨E, 0, 0, (Q (Fin.last L) : Matrix d d ℝ) * D⟩
      have hw : ∀ j, θ.write j = 0 := fun _ => rfl
      have hw' : ∀ j, (θ.cob G Q).write j = 0 := fun _ => Matrix.zero_mul _
      have he := h θ x
      rw [eval, eval, hidden_of_write_eq_zero_ocz _ x hw', hidden_of_write_eq_zero_ocz θ x hw]
        at he
      simp only [θ, Params.cob, hA, cob_inv_mul_mul_ocz] at he
      -- `N_0(x E G_0) = N_0(x E (c_0 Q_0)) = N_0(x E) Q_0`
      rw [← Matrix.mul_assoc x E, hG 0, rmsNorm_zero_mul_smul_orthogonal (hc 0) (hQ 0)] at he
      rw [he, Matrix.mul_assoc]
    -- the row `t₀`: `N_0(e_k) Q_L = N_0(e_k) Q_0`, and `N_0(e_k)` is a nonzero multiple of `e_k`
    have hr := congrFun hmat t₀
    change rmsRow 0 ((x * E) t₀) ᵥ* (Q (Fin.last L) : Matrix d d ℝ)
      = rmsRow 0 ((x * E) t₀) ᵥ* (Q 0 : Matrix d d ℝ) at hr
    rw [hxE] at hr
    unfold rmsRow at hr
    rw [Matrix.smul_vecMul, Matrix.smul_vecMul] at hr
    exact (smul_right_inj (rms_scale_ne_zero_ocz (single_one_ne_zero_ocz k))).mp hr
  -- (b) Induction over the blocks: if `G_{k-1} = G_0`, the block `k` alone gives `G_k = G_0`.
  intro ℓ
  induction ℓ using Fin.induction with
  | zero => rfl
  | succ k ih =>
    obtain ⟨x, E, W, t, hxt, hft⟩ := hne k
    apply Units.ext
    -- `N_0(x E G_0 + F V G_k) = N_0((x E + F V) G_0)` for every write `V`, `F` the block's output
    have hmat : ∀ V : Matrix (A.w k) d ℝ,
        rmsNorm 0 (x * E * (G 0 : Matrix d d ℝ)
            + A.f k (rmsNorm 0 (x * E) * W) * V * (G k.succ : Matrix d d ℝ))
          = rmsNorm 0 ((x * E + A.f k (rmsNorm 0 (x * E) * W) * V) * (G 0 : Matrix d d ℝ)) := by
      intro V
      have hmat' : rmsNorm 0 (x * E * (G 0 : Matrix d d ℝ)
            + A.f k (rmsNorm 0 (x * E) * W) * V * (G k.succ : Matrix d d ℝ))
          = rmsNorm 0 (x * E + A.f k (rmsNorm 0 (x * E) * W) * V)
            * (Q (Fin.last L) : Matrix d d ℝ) := by
        refine eq_of_forall_mul_right_ocz (dOut := dOut) fun D => ?_
        -- only block `k` writes, with the read `W` and the write `V`; the readout is `Q_L D`
        let θ : Params A dIn dOut :=
          ⟨E, Pi.single k W, Pi.single k V, (Q (Fin.last L) : Matrix d d ℝ) * D⟩
        have hw : ∀ j, j ≠ k → θ.write j = 0 := fun j hj =>
          Pi.single_eq_of_ne (M := fun ℓ => Matrix (A.w ℓ) d ℝ) hj V
        have hw' : ∀ j, j ≠ k → (θ.cob G Q).write j = 0 := fun j hj => by
          show θ.write j * _ = 0
          rw [hw j hj, Matrix.zero_mul]
        have he := h θ x
        rw [eval, eval, hidden_last_single_write_ocz _ x k hw',
          hidden_last_single_write_ocz θ x k hw] at he
        simp only [θ, Params.cob, hA, Pi.single_eq_same, cob_inv_mul_mul_ocz] at he
        -- the block reads `N_0(x E G_0) Q_k⁻¹ W = N_0(x E (c_k Q_k)) Q_k⁻¹ W = N_0(x E) W`
        have key : rmsNorm 0 (x * (E * (G 0 : Matrix d d ℝ)))
            * ((↑(Q k.castSucc)⁻¹ : Matrix d d ℝ) * W) = rmsNorm 0 (x * E) * W := by
          rw [← Matrix.mul_assoc x E, ← ih, hG k.castSucc,
            rmsNorm_zero_mul_smul_orthogonal (hc _) (hQ _), Matrix.mul_assoc,
            cob_mul_inv_mul_ocz]
        rw [key] at he
        simpa only [Matrix.mul_assoc] using he
      -- `N_0(h) Q_L = N_0(h) Q_0 = N_0(h (c_0 Q_0)) = N_0(h G_0)`
      rw [hmat', hL, hG 0, rmsNorm_zero_mul_smul_orthogonal (hc 0) (hQ 0)]
    -- the row `t`: as `V` varies, the row `w = F_t V` of the write takes every value
    have hrow : ∀ w : d → ℝ, rmsRow 0 ((x * E) t ᵥ* (G 0 : Matrix d d ℝ)
          + w ᵥ* (G k.succ : Matrix d d ℝ))
        = rmsRow 0 (((x * E) t + w) ᵥ* (G 0 : Matrix d d ℝ)) := by
      intro w
      obtain ⟨V, hV⟩ := exists_vecMul_eq_ocz hft w
      have hr := congrFun (hmat V) t
      change rmsRow 0 ((x * E) t ᵥ* (G 0 : Matrix d d ℝ)
          + A.f k (rmsNorm 0 (x * E) * W) t ᵥ* V ᵥ* (G k.succ : Matrix d d ℝ))
        = rmsRow 0 (((x * E) t + A.f k (rmsNorm 0 (x * E) * W) t ᵥ* V)
          ᵥ* (G 0 : Matrix d d ℝ)) at hr
      rwa [hV] at hr
    -- the step lemma, with the nonzero row `h = (x E)_t`
    exact eq_of_rmsRow_zero_add_ocz hd hxt (G 0) _ hrow

/-- **Theorem A.5 (iii) of the skips paper under RMSNorm with `ε = 0`:** under the hypotheses of
`cob_eq_of_eval_cob_residual_rmsNorm_zero`, the map `θ ↦ θ.cob G Q` with `G_ℓ = c_ℓ Q_ℓ`
preserves the function of every residual network if and only if `G_0 = G_1 = ⋯ = G_L`. -/
theorem eval_cob_residual_rmsNorm_zero_iff [Nonempty T] [Nonempty dIn] [Nonempty dOut]
    (hA : A.χ = rmsNorm 0) (hd : 2 ≤ Fintype.card d)
    (hne : ∀ ℓ, ∃ (x : Matrix T dIn ℝ) (E : Matrix dIn d ℝ) (W : Matrix d (A.r ℓ) ℝ) (t : T),
      (x * E) t ≠ 0 ∧ A.f ℓ (rmsNorm 0 (x * E) * W) t ≠ 0)
    (G Q : Fin (L + 1) → GL d ℝ) (c : Fin (L + 1) → ℝ) (hc : ∀ ℓ, 0 < c ℓ)
    (hQ : ∀ ℓ, (Q ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ)
    (hG : ∀ ℓ, (G ℓ : Matrix d d ℝ) = c ℓ • (Q ℓ : Matrix d d ℝ)) :
    (∀ (θ : Params A dIn dOut) (x : Matrix T dIn ℝ), eval A 1 (θ.cob G Q) x = eval A 1 θ x)
      ↔ ∀ ℓ, G ℓ = G 0 := by
  refine ⟨cob_eq_of_eval_cob_residual_rmsNorm_zero hA hd hne G Q c hc hQ hG,
    fun hGe θ x => ?_⟩
  -- `N_0(h G_ℓ) = N_0(h (c_ℓ Q_ℓ)) = N_0(h) Q_ℓ` at every hidden state (Lemma A.1, `ε = 0`)
  have hχ : ∀ ℓ (h : Matrix T d ℝ),
      A.χ (h * (G ℓ : Matrix d d ℝ)) = A.χ h * (Q ℓ : Matrix d d ℝ) := by
    intro ℓ h
    rw [hA, hG ℓ]
    exact rmsNorm_zero_mul_smul_orthogonal (hc ℓ) (hQ ℓ) h
  -- all `G_ℓ` equal `G_0`: the identity skips stay `G_{ℓ-1}⁻¹ I G_ℓ = I`
  have hskip : cobSkip (1 : Fin L → Matrix d d ℝ) G = 1 := by
    funext ℓ
    simp only [cobSkip, Pi.one_apply, Matrix.mul_one, hGe ℓ.castSucc, hGe ℓ.succ, Units.inv_mul]
  -- Proposition 3.2 in general form
  have he := eval_cob (M := 1) (θ := θ) (G := G) (K := Q) (x := x) hχ
  rwa [hskip] at he

end Skips
