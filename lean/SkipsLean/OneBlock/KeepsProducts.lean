import SkipsLean.OneBlock.Factorization

/-!
# One block: the directions that keep `M`, `A` and `C`

Paper (skips paper), Lemma B.2 (The directions that keep `M`, `A` and `C`): "Let `E`, `D`,
`W_read` and `W_write` have rank `d_model`. A direction `η` keeps `C` and `A` fixed to first
order, `D_θ C η = 0` and `D_θ A η = 0`, if and only if

`η_E = E X`, `η_read = −X W_read`, `η_write = W_write Y`, `η_D = −Y D`

for some `X, Y ∈ ℝ^{d_model × d_model}`, and it keeps `M` fixed as well, `D_θ M η = 0`, if and only
if moreover `X = Y`. […] The matrices `X`, `Y` and vectors `g_0`, `g_1` are determined by the
direction, so these directions form a space of dimension `2 d_model²` without the skip and
`d_model²` with it, and `2 d_model` more with biases."

Here `C = E W_read`, `A = W_write D` and, in the residual network, `M = E D`, with the derivatives
`D_θ C η = η_E W_read + E η_read`, `D_θ A η = η_write D + W_write η_D` and
`D_θ M η = η_E D + E η_D`. The first "if and only if" is `keeps_products_iff_mem_range_cobDir`
(`OneBlock/Factorization.lean`, Lemma C.2 of the dimension paper), with
`η = cobDir θ ![X, Y]`. In this file: the second "if and only if", and the two dimensions (the
dimension of the span of the set of these directions, which is a subspace). Not stated: the
clauses with biases.
-/

namespace Skips

open Matrix

variable {T d dIn dOut : Type*} [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut]
variable {A : Arch T d 1}

/-- Helper: a matrix whose rank is its number of rows has a right inverse, `M R = 1`. -/
private theorem exists_right_inverse_of_rank_kpr {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] (M : Matrix m n ℝ) (hM : M.rank = Fintype.card m) :
    ∃ R : Matrix n m ℝ, M * R = 1 :=
  Matrix.mulVec_surjective_iff_exists_right_inverse.mp
    (Matrix.mulVec_surjective_iff_rank_eq_card.mpr hM)

/-- Helper: a matrix whose rank is its number of columns has a left inverse, `B M = 1`. -/
private theorem exists_left_inverse_of_rank_kpr {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq n] (M : Matrix m n ℝ) (hM : M.rank = Fintype.card n) :
    ∃ B : Matrix n m ℝ, B * M = 1 :=
  Matrix.vecMul_surjective_iff_exists_left_inverse.mp
    (Matrix.vecMul_surjective_iff_rank_eq_card.mpr hM)

/-- Helper: a matrix whose rank is its number of columns cancels on the left, via a left inverse. -/
private theorem cancel_left_of_rank_kpr {m n k : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (M : Matrix m n ℝ) (hM : M.rank = Fintype.card n) {X Y : Matrix n k ℝ}
    (h : M * X = M * Y) : X = Y := by
  obtain ⟨B, hB⟩ := exists_left_inverse_of_rank_kpr M hM
  have := congrArg (B * ·) h
  simpa only [← Matrix.mul_assoc, hB, Matrix.one_mul] using this

/-- Helper: a matrix whose rank is its number of rows cancels on the right, via a right
inverse. -/
private theorem cancel_right_of_rank_kpr {m n k : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    (M : Matrix m n ℝ) (hM : M.rank = Fintype.card m) {X Y : Matrix k m ℝ}
    (h : X * M = Y * M) : X = Y := by
  obtain ⟨R, hR⟩ := exists_right_inverse_of_rank_kpr M hM
  have := congrArg (· * R) h
  simpa only [Matrix.mul_assoc, hR, Matrix.mul_one] using this

/-- **Lemma B.2 of the skips paper, "and it keeps `M` fixed as well […] if and only if moreover
`X = Y`":** for `E`, `D`, `W_read`, `W_write` of rank `d`, a direction `η` keeps `C = E W_read`,
`A = W_write D` and `M = E D` fixed to first order if and only if it is the direction of one
change of basis `X` at both hidden states: `η_E = E X`, `η_read = −X W_read`,
`η_write = W_write X`, `η_D = −X D`. -/
theorem keeps_products_and_ED_iff_mem_range_cobDir (θ η : Params A dIn dOut)
    (hE : θ.E.rank = Fintype.card d) (hD : θ.D.rank = Fintype.card d)
    (hr : (θ.read 0).rank = Fintype.card d) (hw : (θ.write 0).rank = Fintype.card d) :
    (η.E * θ.read 0 + θ.E * η.read 0 = 0 ∧ η.write 0 * θ.D + θ.write 0 * η.D = 0
        ∧ η.E * θ.D + θ.E * η.D = 0)
      ↔ ∃ X : Matrix d d ℝ, η = cobDir θ ![X, X] := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    -- by Lemma C.2, `η = cobDir θ (X₀, X₁)`
    obtain ⟨X, rfl⟩ := (keeps_products_iff_mem_range_cobDir θ η hE hD hr hw).1 ⟨h1, h2⟩
    -- `∂M = E X₀ D − E X₁ D = 0`
    have h : θ.E * (X 0 * θ.D) = θ.E * (X 1 * θ.D) := by
      have h' : θ.E * X 0 * θ.D + θ.E * -(X 1 * θ.D) = 0 := h3
      rwa [Matrix.mul_neg, Matrix.mul_assoc, add_neg_eq_zero] at h'
    -- cancel `E` on the left and `D` on the right: `X₀ = X₁`
    have h01 : X 0 = X 1 :=
      cancel_right_of_rank_kpr θ.D hD (cancel_left_of_rank_kpr θ.E hE h)
    refine ⟨X 0, congrArg (cobDir θ) ?_⟩
    funext i
    fin_cases i
    · rfl
    · exact h01.symm
  · rintro ⟨X, rfl⟩
    -- `C` and `A` are kept by Lemma C.2; `∂M = E X D − E X D = 0`
    obtain ⟨h1, h2⟩ := (keeps_products_iff_mem_range_cobDir θ (cobDir θ ![X, X]) hE hD hr hw).2
      ⟨_, rfl⟩
    refine ⟨h1, h2, ?_⟩
    show θ.E * X * θ.D + θ.E * -(X * θ.D) = 0
    rw [Matrix.mul_neg, Matrix.mul_assoc, add_neg_cancel]

/-- Helper: `X ↦ cobDir θ X` is linear. -/
private noncomputable def cobDirLin_kpr (θ : Params A dIn dOut) :
    (Fin 2 → Matrix d d ℝ) →ₗ[ℝ] Params A dIn dOut where
  toFun := cobDir θ
  map_add' X Y := by
    apply Params.ext' <;> intros <;>
      simp only [cobDir, Params.add_E, Params.add_read, Params.add_write, Params.add_D,
        Pi.add_apply, Matrix.mul_add, Matrix.add_mul, neg_add]
  map_smul' c X := by
    apply Params.ext' <;> intros <;>
      simp only [cobDir, Params.smul_E, Params.smul_read, Params.smul_write, Params.smul_D,
        Pi.smul_apply, Matrix.mul_smul, Matrix.smul_mul, smul_neg, RingHom.id_apply]

omit [Fintype dOut] in
/-- Helper: `cobDirLin_kpr θ` is injective when `E` and the write have rank `d`. -/
private theorem cobDirLin_kpr_injective (θ : Params A dIn dOut)
    (hE : θ.E.rank = Fintype.card d) (hw : (θ.write 0).rank = Fintype.card d) :
    Function.Injective (cobDirLin_kpr θ) := by
  intro X Y h
  funext i
  fin_cases i
  · -- the embedding component: `E X₀ = E Y₀`, and `E` has rank `d`
    have h0 : θ.E * X 0 = θ.E * Y 0 := congrArg Params.E h
    exact cancel_left_of_rank_kpr θ.E hE h0
  · -- the write component: `W_write X₁ = W_write Y₁`, and `W_write` has rank `d`
    have h1 : θ.write 0 * X 1 = θ.write 0 * Y 1 := congrArg (fun η => η.write 0) h
    exact cancel_left_of_rank_kpr (θ.write 0) hw h1

/-- **Lemma B.2, "these directions form a space of dimension `2 d_model²` without the skip":**
for `E`, `D`, `W_read`, `W_write` of rank `d`, the directions that keep `C` and `A` fixed to first
order span a space of dimension `2 d²` (they form a subspace; `X` and `Y` are determined by the
direction). -/
theorem finrank_span_keeps_products (θ : Params A dIn dOut)
    (hE : θ.E.rank = Fintype.card d) (hD : θ.D.rank = Fintype.card d)
    (hr : (θ.read 0).rank = Fintype.card d) (hw : (θ.write 0).rank = Fintype.card d) :
    Module.finrank ℝ (Submodule.span ℝ {η : Params A dIn dOut |
        η.E * θ.read 0 + θ.E * η.read 0 = 0 ∧ η.write 0 * θ.D + θ.write 0 * η.D = 0})
      = 2 * Fintype.card d ^ 2 := by
  -- the set is the range of `X ↦ cobDir θ X` (Lemma C.2), a subspace
  have hS : {η : Params A dIn dOut |
      η.E * θ.read 0 + θ.E * η.read 0 = 0 ∧ η.write 0 * θ.D + θ.write 0 * η.D = 0}
        = (LinearMap.range (cobDirLin_kpr θ) : Set (Params A dIn dOut)) := by
    ext η
    rw [Set.mem_ofPred_eq, keeps_products_iff_mem_range_cobDir θ η hE hD hr hw]
    exact ⟨fun ⟨X, h⟩ => ⟨X, h.symm⟩, fun ⟨X, h⟩ => ⟨X, h.symm⟩⟩
  -- the map is injective, so the dimension is that of `Fin 2 → Matrix d d ℝ`
  rw [hS, Submodule.span_eq,
    LinearMap.finrank_range_of_inj (cobDirLin_kpr_injective θ hE hw),
    Module.finrank_pi_fintype, Module.finrank_matrix]
  simp [sq]

/-- **Lemma B.2, "and `d_model²` with it":** for `E`, `D`, `W_read`, `W_write` of rank `d`, the
directions that keep `C`, `A` and `M` fixed to first order span a space of dimension `d²`. -/
theorem finrank_span_keeps_products_and_ED (θ : Params A dIn dOut)
    (hE : θ.E.rank = Fintype.card d) (hD : θ.D.rank = Fintype.card d)
    (hr : (θ.read 0).rank = Fintype.card d) (hw : (θ.write 0).rank = Fintype.card d) :
    Module.finrank ℝ (Submodule.span ℝ {η : Params A dIn dOut |
        η.E * θ.read 0 + θ.E * η.read 0 = 0 ∧ η.write 0 * θ.D + θ.write 0 * η.D = 0
          ∧ η.E * θ.D + θ.E * η.D = 0})
      = Fintype.card d ^ 2 := by
  -- the directions of one change of basis, `X ↦ cobDir θ (X, X)`
  let Φ : Matrix d d ℝ →ₗ[ℝ] Params A dIn dOut :=
    (cobDirLin_kpr θ).comp (LinearMap.pi fun _ => LinearMap.id)
  have hΦ : ∀ X, Φ X = cobDir θ ![X, X] := fun X => by
    show cobDir θ (fun _ => X) = cobDir θ ![X, X]
    congr 1
    funext i
    fin_cases i <;> rfl
  -- the set is the range of `Φ` (the first theorem)
  have hS : {η : Params A dIn dOut |
      η.E * θ.read 0 + θ.E * η.read 0 = 0 ∧ η.write 0 * θ.D + θ.write 0 * η.D = 0
        ∧ η.E * θ.D + θ.E * η.D = 0}
        = (LinearMap.range Φ : Set (Params A dIn dOut)) := by
    ext η
    rw [Set.mem_ofPred_eq, keeps_products_and_ED_iff_mem_range_cobDir θ η hE hD hr hw]
    exact ⟨fun ⟨X, h⟩ => ⟨X, (hΦ X).trans h.symm⟩, fun ⟨X, h⟩ => ⟨X, h.symm.trans (hΦ X)⟩⟩
  -- `Φ` is injective: `cobDir θ` is, and so is `X ↦ (X, X)`
  have hinj : Function.Injective Φ := fun X Y h =>
    congrFun (cobDirLin_kpr_injective θ hE hw h) 0
  rw [hS, Submodule.span_eq, LinearMap.finrank_range_of_inj hinj, Module.finrank_matrix,
    Module.finrank_self, mul_one, sq]

end Skips
