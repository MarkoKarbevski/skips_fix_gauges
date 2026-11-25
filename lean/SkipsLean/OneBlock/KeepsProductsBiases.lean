import SkipsLean.OneBlock.KeepsProducts
import SkipsLean.Symmetry.BiasesFlat

/-!
# One block with biases: the directions that keep `M`, `A`, `C`, `β` and `γ`

Paper (skips paper), Lemma B.2 (The directions that keep `M`, `A` and `C`): "With biases, it keeps
`β` and `γ_0`, respectively `β` and `γ`, fixed as well if and only if moreover
`η_{b_E} = b_E X + g_0`, `η_{b_read} = −g_0 W_read`, `η_{b_write} = b_write Y + g_1` and
`η_{b_D} = −g_1 D`, respectively `η_{b_D} = −(g_0 + g_1) D`, for some row vectors
`g_0, g_1 ∈ ℝ^{1×d_model}`. The matrices `X`, `Y` and vectors `g_0`, `g_1` are determined by the
direction, so these directions form a space of dimension `2 d_model²` without the skip and
`d_model²` with it, and `2 d_model` more with biases."

Here (Appendix B, "Reduction") `C = E W_read`, `A = W_write D`, `M = E D`,
`β = b_E W_read + b_read`, `γ_0 = b_write D + b_D`, `γ = b_E D + γ_0`, with the derivatives along
a direction `η` of weights and biases

`D β η = η_{b_E} W_read + b_E η_read + η_{b_read}`,
`D γ_0 η = η_{b_write} D + b_write η_D + η_{b_D}`,
`D γ η = η_{b_E} D + b_E η_D + D γ_0 η`.

The clauses without biases are in `OneBlock/Factorization.lean` and `OneBlock/KeepsProducts.lean`.
In this file, for one block of any kind with biases (`Network/Biases.lean`):

* `keeps_products_biases_iff`: `η` keeps `C`, `A`, `β`, `γ_0` to first order if and only if it is
  the direction of two changes of basis and two translations,
  `η = cobDirB p X + (0, translateAtDir θ g)` (`Symmetry/BiasesFlat.lean`);
* `keeps_products_and_ED_biases_iff`: `η` keeps `C`, `A`, `M`, `β`, `γ` if and only if
  `η = cobDirB p (X, X) + (0, translateDir θ g)`;
* the two dimensions with biases, `2 d² + 2 d` and `d² + 2 d` (the dimension of the span of the
  set of these directions, which is a subspace).
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {A : Arch T d 1}

/-- **Lemma B.2 of the skips paper with biases, without the skip:** for `E`, `D`, `W_read`,
`W_write` of rank `d`, a direction `η` of weights and biases keeps `C = E W_read`,
`A = W_write D`, `β = b_E W_read + b_read` and `γ_0 = b_write D + b_D` fixed to first order if and
only if it is the direction of changes of basis `X_0, X_1` and translations `g_0, g_1` of the two
hidden states: `η_E = E X_0`, `η_read = −X_0 W_read`, `η_write = W_write X_1`, `η_D = −X_1 D`,
`η_{b_E} = b_E X_0 + g_0`, `η_{b_read} = −g_0 W_read`, `η_{b_write} = b_write X_1 + g_1`,
`η_{b_D} = −g_1 D`. -/
theorem keeps_products_biases_iff (p η : ParamsB A dIn dOut)
    (hE : p.1.E.rank = Fintype.card d) (hD : p.1.D.rank = Fintype.card d)
    (hr : (p.1.read 0).rank = Fintype.card d) (hw : (p.1.write 0).rank = Fintype.card d) :
    (η.1.E * p.1.read 0 + p.1.E * η.1.read 0 = 0 ∧
      η.1.write 0 * p.1.D + p.1.write 0 * η.1.D = 0 ∧
      η.2.E ᵥ* p.1.read 0 + p.2.E ᵥ* η.1.read 0 + η.2.read 0 = 0 ∧
      η.2.write 0 ᵥ* p.1.D + p.2.write 0 ᵥ* η.1.D + η.2.D = 0) ↔
    ∃ (X : Fin 2 → Matrix d d ℝ) (g : Fin 2 → d → ℝ),
      η = cobDirB p X + (0, translateAtDir p.1 g) := by
  constructor
  · rintro ⟨h1, h2, hβ, hγ⟩
    -- Lemma C.2: the weights move by two changes of basis `X_0`, `X_1`
    obtain ⟨X, hX⟩ := (keeps_products_iff_mem_range_cobDir p.1 η.1 hE hD hr hw).1 ⟨h1, h2⟩
    have hR : η.1.read 0 = -(X 0 * p.1.read 0) := by rw [hX]; rfl
    have hD' : η.1.D = -(X 1 * p.1.D) := by rw [hX]; rfl
    -- `∂β = 0`: `η_{b_read} = −g_0 W_read` with `g_0 = η_{b_E} − b_E X_0`
    have hbR : η.2.read 0 = -((η.2.E - p.2.E ᵥ* X 0) ᵥ* p.1.read 0) := by
      rw [hR, Matrix.vecMul_neg, ← Matrix.vecMul_vecMul] at hβ
      rw [Matrix.sub_vecMul]
      linear_combination hβ
    -- `∂γ_0 = 0`: `η_{b_D} = −g_1 D` with `g_1 = η_{b_write} − b_write X_1`
    have hbD : η.2.D = -((η.2.write 0 - p.2.write 0 ᵥ* X 1) ᵥ* p.1.D) := by
      rw [hD', Matrix.vecMul_neg, ← Matrix.vecMul_vecMul] at hγ
      rw [Matrix.sub_vecMul]
      linear_combination hγ
    -- so `η` is the direction of the changes of basis `X` and of the translations `g_0, g_1`
    refine ⟨X, ![η.2.E - p.2.E ᵥ* X 0, η.2.write 0 - p.2.write 0 ᵥ* X 1], ?_⟩
    refine Prod.ext ?_ ?_
    · show η.1 = cobDir p.1 X + 0
      rw [add_zero]
      exact hX
    · apply Biases.ext'
      · show η.2.E = p.2.E ᵥ* X 0 + (η.2.E - p.2.E ᵥ* X 0)
        abel
      · intro ℓ
        obtain rfl : ℓ = 0 := Subsingleton.elim ℓ 0
        show η.2.read 0 = 0 + -((η.2.E - p.2.E ᵥ* X 0) ᵥ* p.1.read 0)
        rw [zero_add]
        exact hbR
      · intro ℓ
        obtain rfl : ℓ = 0 := Subsingleton.elim ℓ 0
        show η.2.write 0 = p.2.write 0 ᵥ* X 1 + (η.2.write 0 - p.2.write 0 ᵥ* X 1)
        abel
      · show η.2.D = 0 + -((η.2.write 0 - p.2.write 0 ᵥ* X 1) ᵥ* p.1.D)
        rw [zero_add]
        exact hbD
  · rintro ⟨X, g, rfl⟩
    -- `C` and `A` are kept by Lemma C.2
    obtain ⟨h1, h2⟩ := (keeps_products_iff_mem_range_cobDir p.1
      (cobDirB p X + (0, translateAtDir p.1 g)).1 hE hD hr hw).2 ⟨X, add_zero _⟩
    refine ⟨h1, h2, ?_, ?_⟩
    · -- `∂β = (b_E X_0 + g_0) W_read − b_E X_0 W_read − g_0 W_read = 0`
      show (p.2.E ᵥ* X 0 + g 0) ᵥ* p.1.read 0 + p.2.E ᵥ* (-(X 0 * p.1.read 0) + 0)
        + (0 + -(g 0 ᵥ* p.1.read 0)) = 0
      simp only [add_zero, zero_add, Matrix.add_vecMul, Matrix.vecMul_neg,
        ← Matrix.vecMul_vecMul]
      abel
    · -- `∂γ_0 = (b_write X_1 + g_1) D − b_write X_1 D − g_1 D = 0`
      show (p.2.write 0 ᵥ* X 1 + g 1) ᵥ* p.1.D + p.2.write 0 ᵥ* (-(X 1 * p.1.D) + 0)
        + (0 + -(g 1 ᵥ* p.1.D)) = 0
      simp only [add_zero, zero_add, Matrix.add_vecMul, Matrix.vecMul_neg,
        ← Matrix.vecMul_vecMul]
      abel

/-- **Lemma B.2 of the skips paper with biases, with the skip:** for `E`, `D`, `W_read`,
`W_write` of rank `d`, a direction `η` of weights and biases keeps `C`, `A`, `M = E D`, `β` and
`γ = b_E D + b_write D + b_D` fixed to first order if and only if it is the direction of one
change of basis `X` of both hidden states and of the translations `g_0, g_1` of Lemma A.8:
`η_{b_E} = b_E X + g_0`, `η_{b_read} = −g_0 W_read`, `η_{b_write} = b_write X + g_1`,
`η_{b_D} = −(g_0 + g_1) D`. -/
theorem keeps_products_and_ED_biases_iff (p η : ParamsB A dIn dOut)
    (hE : p.1.E.rank = Fintype.card d) (hD : p.1.D.rank = Fintype.card d)
    (hr : (p.1.read 0).rank = Fintype.card d) (hw : (p.1.write 0).rank = Fintype.card d) :
    (η.1.E * p.1.read 0 + p.1.E * η.1.read 0 = 0 ∧
      η.1.write 0 * p.1.D + p.1.write 0 * η.1.D = 0 ∧
      η.1.E * p.1.D + p.1.E * η.1.D = 0 ∧
      η.2.E ᵥ* p.1.read 0 + p.2.E ᵥ* η.1.read 0 + η.2.read 0 = 0 ∧
      η.2.E ᵥ* p.1.D + p.2.E ᵥ* η.1.D
        + (η.2.write 0 ᵥ* p.1.D + p.2.write 0 ᵥ* η.1.D + η.2.D) = 0) ↔
    ∃ (X : Matrix d d ℝ) (g : Fin 2 → d → ℝ),
      η = cobDirB p (fun _ => X) + (0, translateDir p.1 g) := by
  have hI : Finset.Iic (0 : Fin 1).castSucc = {0} := by decide
  -- on `Fin 2`, `![X, X]` is the constant family
  have hXX : ∀ X : Matrix d d ℝ, cobDir p.1 ![X, X] = cobDir p.1 (fun _ => X) := fun X => by
    congr 1
    funext i
    fin_cases i <;> rfl
  constructor
  · rintro ⟨h1, h2, h3, hβ, hγ⟩
    -- Lemma B.2 without biases: the weights move by one change of basis `X`
    obtain ⟨X, hX⟩ :=
      (keeps_products_and_ED_iff_mem_range_cobDir p.1 η.1 hE hD hr hw).1 ⟨h1, h2, h3⟩
    rw [hXX] at hX
    have hR : η.1.read 0 = -(X * p.1.read 0) := by rw [hX]; rfl
    have hD' : η.1.D = -(X * p.1.D) := by rw [hX]; rfl
    -- `∂β = 0`: `η_{b_read} = −g_0 W_read` with `g_0 = η_{b_E} − b_E X`
    have hbR : η.2.read 0 = -((η.2.E - p.2.E ᵥ* X) ᵥ* p.1.read 0) := by
      rw [hR, Matrix.vecMul_neg, ← Matrix.vecMul_vecMul] at hβ
      rw [Matrix.sub_vecMul]
      linear_combination hβ
    -- `∂γ = 0`: `η_{b_D} = −(g_0 + g_1) D` with `g_1 = η_{b_write} − b_write X`
    have hbD : η.2.D = -(((η.2.E - p.2.E ᵥ* X) + (η.2.write 0 - p.2.write 0 ᵥ* X))
        ᵥ* p.1.D) := by
      simp only [hD', Matrix.vecMul_neg, ← Matrix.vecMul_vecMul] at hγ
      rw [Matrix.add_vecMul, Matrix.sub_vecMul, Matrix.sub_vecMul]
      linear_combination hγ
    -- so `η` is the direction of the change of basis `X` and of the translations `g_0, g_1`
    refine ⟨X, ![η.2.E - p.2.E ᵥ* X, η.2.write 0 - p.2.write 0 ᵥ* X], ?_⟩
    refine Prod.ext ?_ ?_
    · show η.1 = cobDir p.1 (fun _ => X) + 0
      rw [add_zero]
      exact hX
    · apply Biases.ext'
      · show η.2.E = p.2.E ᵥ* X + (η.2.E - p.2.E ᵥ* X)
        abel
      · intro ℓ
        obtain rfl : ℓ = 0 := Subsingleton.elim ℓ 0
        show η.2.read 0 = 0 + -((∑ k ∈ Finset.Iic (0 : Fin 1).castSucc,
          ![η.2.E - p.2.E ᵥ* X, η.2.write 0 - p.2.write 0 ᵥ* X] k) ᵥ* p.1.read 0)
        rw [hI, Finset.sum_singleton, zero_add]
        exact hbR
      · intro ℓ
        obtain rfl : ℓ = 0 := Subsingleton.elim ℓ 0
        show η.2.write 0 = p.2.write 0 ᵥ* X + (η.2.write 0 - p.2.write 0 ᵥ* X)
        abel
      · show η.2.D = 0 + -((∑ k, ![η.2.E - p.2.E ᵥ* X, η.2.write 0 - p.2.write 0 ᵥ* X] k)
          ᵥ* p.1.D)
        rw [Fin.sum_univ_two, zero_add]
        exact hbD
  · rintro ⟨X, g, rfl⟩
    -- `C`, `A` and `M` are kept by Lemma B.2 without biases
    obtain ⟨h1, h2, h3⟩ := (keeps_products_and_ED_iff_mem_range_cobDir p.1
      (cobDirB p (fun _ => X) + (0, translateDir p.1 g)).1 hE hD hr hw).2
      ⟨X, (add_zero _).trans (hXX X).symm⟩
    refine ⟨h1, h2, h3, ?_, ?_⟩
    · -- `∂β = (b_E X + g_0) W_read − b_E X W_read − g_0 W_read = 0`
      show (p.2.E ᵥ* X + g 0) ᵥ* p.1.read 0 + p.2.E ᵥ* (-(X * p.1.read 0) + 0)
        + (0 + -((∑ k ∈ Finset.Iic (0 : Fin 1).castSucc, g k) ᵥ* p.1.read 0)) = 0
      rw [hI, Finset.sum_singleton]
      simp only [add_zero, zero_add, Matrix.add_vecMul, Matrix.vecMul_neg,
        ← Matrix.vecMul_vecMul]
      abel
    · -- `∂γ = (b_E X + g_0) D − b_E X D + (b_write X + g_1) D − b_write X D − (g_0 + g_1) D`
      show (p.2.E ᵥ* X + g 0) ᵥ* p.1.D + p.2.E ᵥ* (-(X * p.1.D) + 0)
        + ((p.2.write 0 ᵥ* X + g 1) ᵥ* p.1.D + p.2.write 0 ᵥ* (-(X * p.1.D) + 0)
          + (0 + -((∑ k, g k) ᵥ* p.1.D))) = 0
      rw [Fin.sum_univ_two]
      simp only [add_zero, zero_add, Matrix.add_vecMul, Matrix.vecMul_neg,
        ← Matrix.vecMul_vecMul]
      abel

/-- Helper: `(X, g) ↦ cobDirB p X + (0, translateAtDir θ g)` is linear (a copy of the private
`cobTransAtLin_bfl` of `Symmetry/BiasesFlat.lean`). -/
private noncomputable def cobTransAtLin_kpb (p : ParamsB A dIn dOut) :
    ((Fin 2 → Matrix d d ℝ) × (Fin 2 → d → ℝ)) →ₗ[ℝ] ParamsB A dIn dOut where
  toFun Xg := cobDirB p Xg.1 + ((0, translateAtDir p.1 Xg.2) : ParamsB A dIn dOut)
  map_add' Xg Yg := by
    refine Prod.ext (Params.ext' ?_ ?_ ?_ ?_) (Biases.ext' ?_ ?_ ?_ ?_) <;> (try intro ℓ) <;>
      simp only [cobDirB, cobDir, translateAtDir, Prod.fst_add, Prod.snd_add, Params.add_E,
        Params.add_read, Params.add_write, Params.add_D, Biases.add_E, Biases.add_read,
        Biases.add_write, Biases.add_D, Pi.add_apply, Matrix.mul_add, Matrix.add_mul,
        Matrix.vecMul_add, Matrix.add_vecMul, neg_add, add_zero, zero_add] <;> abel
  map_smul' c Xg := by
    refine Prod.ext (Params.ext' ?_ ?_ ?_ ?_) (Biases.ext' ?_ ?_ ?_ ?_) <;> (try intro ℓ) <;>
      simp only [cobDirB, cobDir, translateAtDir, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
        Prod.smul_snd, Params.smul_E, Params.smul_read, Params.smul_write, Params.smul_D,
        Biases.add_E, Biases.add_read, Biases.add_write, Biases.add_D, Biases.smul_E,
        Biases.smul_read, Biases.smul_write, Biases.smul_D, Pi.smul_apply, Matrix.mul_smul,
        Matrix.smul_mul, Matrix.vecMul_smul, Matrix.smul_vecMul, smul_neg, smul_add, smul_zero,
        add_zero, zero_add, RingHom.id_apply]

/-- Helper: `(X, g) ↦ cobDirB p (X, X) + (0, translateDir θ g)` is linear (a copy of the private
`cobTransLin_bfl` of `Symmetry/BiasesFlat.lean`). -/
private noncomputable def cobTransLin_kpb (p : ParamsB A dIn dOut) :
    (Matrix d d ℝ × (Fin 2 → d → ℝ)) →ₗ[ℝ] ParamsB A dIn dOut where
  toFun Xg := cobDirB p (fun _ => Xg.1) + ((0, translateDir p.1 Xg.2) : ParamsB A dIn dOut)
  map_add' Xg Yg := by
    refine Prod.ext (Params.ext' ?_ ?_ ?_ ?_) (Biases.ext' ?_ ?_ ?_ ?_) <;> (try intro ℓ) <;>
      simp only [cobDirB, cobDir, translateDir, Prod.fst_add, Prod.snd_add, Params.add_E,
        Params.add_read, Params.add_write, Params.add_D, Biases.add_E, Biases.add_read,
        Biases.add_write, Biases.add_D, Pi.add_apply, Matrix.mul_add, Matrix.add_mul,
        Matrix.vecMul_add, Matrix.add_vecMul, Finset.sum_add_distrib, neg_add, add_zero,
        zero_add] <;> abel
  map_smul' c Xg := by
    refine Prod.ext (Params.ext' ?_ ?_ ?_ ?_) (Biases.ext' ?_ ?_ ?_ ?_) <;> (try intro ℓ) <;>
      simp only [cobDirB, cobDir, translateDir, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
        Prod.smul_snd, Params.smul_E, Params.smul_read, Params.smul_write, Params.smul_D,
        Biases.add_E, Biases.add_read, Biases.add_write, Biases.add_D, Biases.smul_E,
        Biases.smul_read, Biases.smul_write, Biases.smul_D, Pi.smul_apply, Matrix.mul_smul,
        Matrix.smul_mul, Matrix.vecMul_smul, Matrix.smul_vecMul, ← Finset.smul_sum, smul_neg,
        smul_add, smul_zero, add_zero, zero_add, RingHom.id_apply]

/-- **Lemma B.2 with biases, "a space of dimension `2 d_model²` without the skip […] and
`2 d_model` more with biases":** for `E`, `D`, `W_read`, `W_write` of rank `d`, the directions
that keep `C`, `A`, `β` and `γ_0` fixed to first order span a space of dimension `2 d² + 2 d`
(they form a subspace; `X_0`, `X_1`, `g_0`, `g_1` are determined by the direction). -/
theorem finrank_span_keeps_products_biases (p : ParamsB A dIn dOut)
    (hE : p.1.E.rank = Fintype.card d) (hD : p.1.D.rank = Fintype.card d)
    (hr : (p.1.read 0).rank = Fintype.card d) (hw : (p.1.write 0).rank = Fintype.card d) :
    Module.finrank ℝ (Submodule.span ℝ {η : ParamsB A dIn dOut |
      η.1.E * p.1.read 0 + p.1.E * η.1.read 0 = 0 ∧
      η.1.write 0 * p.1.D + p.1.write 0 * η.1.D = 0 ∧
      η.2.E ᵥ* p.1.read 0 + p.2.E ᵥ* η.1.read 0 + η.2.read 0 = 0 ∧
      η.2.write 0 ᵥ* p.1.D + p.2.write 0 ᵥ* η.1.D + η.2.D = 0})
      = 2 * Fintype.card d ^ 2 + 2 * Fintype.card d := by
  -- the set is the range of `(X, g) ↦ cobDirB p X + (0, translateAtDir θ g)` (the first theorem)
  have hS : {η : ParamsB A dIn dOut |
      η.1.E * p.1.read 0 + p.1.E * η.1.read 0 = 0 ∧
      η.1.write 0 * p.1.D + p.1.write 0 * η.1.D = 0 ∧
      η.2.E ᵥ* p.1.read 0 + p.2.E ᵥ* η.1.read 0 + η.2.read 0 = 0 ∧
      η.2.write 0 ᵥ* p.1.D + p.2.write 0 ᵥ* η.1.D + η.2.D = 0}
        = (LinearMap.range (cobTransAtLin_kpb p) : Set (ParamsB A dIn dOut)) := by
    ext η
    rw [Set.mem_ofPred_eq, keeps_products_biases_iff p η hE hD hr hw]
    exact ⟨fun ⟨X, g, h⟩ => ⟨(X, g), h.symm⟩, fun ⟨Xg, h⟩ => ⟨Xg.1, Xg.2, h.symm⟩⟩
  -- the map is injective (`E` and the write have rank `d`), so the dimension is that of its
  -- domain, `2 d² + 2 d`
  have hinj : Function.Injective (cobTransAtLin_kpb p) :=
    cobDirB_add_translateAtDir_injective p hE fun ℓ => by
      obtain rfl : ℓ = 0 := Subsingleton.elim ℓ 0
      exact hw
  rw [hS, Submodule.span_eq, LinearMap.finrank_range_of_inj hinj]
  simp only [Module.finrank_prod, Module.finrank_matrix, Module.finrank_self,
    Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, mul_one, sq]

/-- **Lemma B.2 with biases, "`d_model²` with it, and `2 d_model` more with biases":** for `E`,
`D`, `W_read`, `W_write` of rank `d`, the directions that keep `C`, `A`, `M`, `β` and `γ` fixed
to first order span a space of dimension `d² + 2 d`. -/
theorem finrank_span_keeps_products_and_ED_biases (p : ParamsB A dIn dOut)
    (hE : p.1.E.rank = Fintype.card d) (hD : p.1.D.rank = Fintype.card d)
    (hr : (p.1.read 0).rank = Fintype.card d) (hw : (p.1.write 0).rank = Fintype.card d) :
    Module.finrank ℝ (Submodule.span ℝ {η : ParamsB A dIn dOut |
      η.1.E * p.1.read 0 + p.1.E * η.1.read 0 = 0 ∧
      η.1.write 0 * p.1.D + p.1.write 0 * η.1.D = 0 ∧
      η.1.E * p.1.D + p.1.E * η.1.D = 0 ∧
      η.2.E ᵥ* p.1.read 0 + p.2.E ᵥ* η.1.read 0 + η.2.read 0 = 0 ∧
      η.2.E ᵥ* p.1.D + p.2.E ᵥ* η.1.D
        + (η.2.write 0 ᵥ* p.1.D + p.2.write 0 ᵥ* η.1.D + η.2.D) = 0})
      = Fintype.card d ^ 2 + 2 * Fintype.card d := by
  -- the set is the range of `(X, g) ↦ cobDirB p (X, X) + (0, translateDir θ g)` (the second
  -- theorem)
  have hS : {η : ParamsB A dIn dOut |
      η.1.E * p.1.read 0 + p.1.E * η.1.read 0 = 0 ∧
      η.1.write 0 * p.1.D + p.1.write 0 * η.1.D = 0 ∧
      η.1.E * p.1.D + p.1.E * η.1.D = 0 ∧
      η.2.E ᵥ* p.1.read 0 + p.2.E ᵥ* η.1.read 0 + η.2.read 0 = 0 ∧
      η.2.E ᵥ* p.1.D + p.2.E ᵥ* η.1.D
        + (η.2.write 0 ᵥ* p.1.D + p.2.write 0 ᵥ* η.1.D + η.2.D) = 0}
        = (LinearMap.range (cobTransLin_kpb p) : Set (ParamsB A dIn dOut)) := by
    ext η
    rw [Set.mem_ofPred_eq, keeps_products_and_ED_biases_iff p η hE hD hr hw]
    exact ⟨fun ⟨X, g, h⟩ => ⟨(X, g), h.symm⟩, fun ⟨Xg, h⟩ => ⟨Xg.1, Xg.2, h.symm⟩⟩
  -- the map is injective (`E` has rank `d`), so the dimension is that of its domain, `d² + 2 d`
  have hinj : Function.Injective (cobTransLin_kpb p) :=
    cobDirB_const_add_translateDir_injective p hE
  rw [hS, Submodule.span_eq, LinearMap.finrank_range_of_inj hinj]
  simp only [Module.finrank_prod, Module.finrank_matrix, Module.finrank_self,
    Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, mul_one, sq]

end Skips
