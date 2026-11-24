import SkipsLean.Dimension.UpperBound
import SkipsLean.OneBlock.Common

/-!
# The network after a hidden state, the claim `(D_k)`, and how it gives the rank

Paper (dimension paper): Appendix D, "The claim, and the reduction to one step", in the case (n)
(no normalization) and for blocks without symmetries inside (`tanh`, GELU).

For `k = 0, …, L` and a hidden state `h`, `𝓑_{>k}(h)` is the output of the network when its hidden
state `h_k` is set to `h`:

  `𝓑_{>L}(h) = χ(h) D`,   `𝓑_{>k-1}(h) = 𝓑_{>k}(g_k(χ(h)))`,   so that `F_θ(x) = 𝓑_{>0}(x E)`.

It depends on the weights of the blocks `k+1, …, L` and on `D`. For a `d × d` matrix `Z` and a
direction `η` of the parameters, the identity (18) of the paper is

  `𝐃𝓑_{>k}(h) (h Z) + 𝐃_θ 𝓑_{>k}(h) η = 0`   for all `h`,

with `𝐃` the derivative in `h` and `𝐃_θ` the derivative in the weights. Claim `(D_k)` says that
every `Z` and `η` that satisfy it come from changes of basis at the hidden states `h_k, …, h_L`:
there are matrices `Z_k = Z, Z_{k+1}, …, Z_L` with

  `η_read^ℓ = - Z_{ℓ-1} W_read^ℓ`,  `η_write^ℓ = W_write^ℓ Z_ℓ`  (`ℓ = k+1, …, L`),  `η_D = - Z_L D`.

Stated here: the definitions; Lemma D.2 (the derivative of `𝓑_{>k}` is injective on an open dense
set), Lemma D.3 (a direction at a write), Proposition D.4 (the claim `(D_0)` gives the functional
dimension `P - (L + 1) d²`) and Lemma D.5 (`(D_L)` holds), all in the case (n). The paper takes
inputs of one token, since an MLP block acts on each token separately; here a hidden state has the
rows `T`, as everywhere in this library, and the paper's rows are the case of one token.

The entries of `η` at `E` and at the blocks before `k+1` play no role in the identity and are not
constrained by the claim.
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise Topology

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable (A : Arch T d L)

/-- `𝓑_{>k}(h)`: the output of the network when its hidden state `h_k` is set to `h`. (With stream
matrices `S`, as `hidden` and `eval`; the paper's networks are `S = 0`.) -/
def suffix (S : Fin L → Matrix d d ℝ) (θ : Params A dIn dOut) :
    Fin (L + 1) → Matrix T d ℝ → Matrix T dOut ℝ :=
  Fin.reverseInduction (motive := fun _ => Matrix T d ℝ → Matrix T dOut ℝ)
    (fun h => A.χ h * θ.D)
    (fun ℓ B h => B (h * S ℓ + A.f ℓ (A.χ h * θ.read ℓ) * θ.write ℓ))

variable (S : Fin L → Matrix d d ℝ) (θ : Params A dIn dOut)

/-- `𝓑_{>L}(h) = χ(h) D`. -/
theorem suffix_last (h : Matrix T d ℝ) : suffix A S θ (Fin.last L) h = A.χ h * θ.D := by
  simp only [suffix, Fin.reverseInduction_last]

/-- `𝓑_{>k-1}(h) = 𝓑_{>k}(g_k(χ(h)))` (plus the stream term `h S_k`). -/
theorem suffix_castSucc (ℓ : Fin L) (h : Matrix T d ℝ) :
    suffix A S θ ℓ.castSucc h
      = suffix A S θ ℓ.succ (h * S ℓ + A.f ℓ (A.χ h * θ.read ℓ) * θ.write ℓ) := by
  simp only [suffix, Fin.reverseInduction_castSucc]

/-- The network after `h_k`, at the hidden state `h_k` of the input `x`, is the output at `x`. -/
theorem suffix_hidden (x : Matrix T dIn ℝ) (k : Fin (L + 1)) :
    suffix A S θ k (hidden A S θ x k) = eval A S θ x := by
  induction k using Fin.reverseInduction with
  | last =>
    -- `𝓑_{>L}(h_L) = χ(h_L) D` is the output
    rw [suffix_last, eval]
  | cast ℓ ih =>
    -- `𝓑_{>ℓ}(h_ℓ) = 𝓑_{>ℓ+1}(h_{ℓ+1})`
    rw [suffix_castSucc, ← hidden_succ, ih]

/-- `F_θ(x) = 𝓑_{>0}(x E)`. -/
theorem eval_eq_suffix_zero (x : Matrix T dIn ℝ) :
    eval A S θ x = suffix A S θ 0 (x * θ.E) := by
  rw [← suffix_hidden A S θ x 0, hidden_zero]

/-- The identity (18) of the paper for `k`, `Z` and `η`, in a network without skips:
`𝐃𝓑_{>k}(h) (h Z) + 𝐃_θ 𝓑_{>k}(h) η = 0` for all `h`. -/
def SuffixFlat (k : Fin (L + 1)) (Z : Matrix d d ℝ) (η : Params A dIn dOut) : Prop :=
  ∀ h : Matrix T d ℝ,
    fderiv ℝ (fun h' : Matrix T d ℝ => suffix A 0 θ k h') h (h * Z)
      + fderiv ℝ (fun θ' : Params A dIn dOut => suffix A 0 θ' k h) θ η = 0

/-- **Claim `(D_k)`,** in the case (n), for blocks without symmetries inside: every `Z` and `η`
that satisfy the identity (18) for `k` come from changes of basis `Z_k = Z, Z_{k+1}, …, Z_L` at the
hidden states `h_k, …, h_L`. -/
def Claim (k : Fin (L + 1)) : Prop :=
  ∀ (Z : Matrix d d ℝ) (η : Params A dIn dOut), SuffixFlat A θ k Z η →
    ∃ X : Fin (L + 1) → Matrix d d ℝ, X k = Z ∧
      (∀ ℓ : Fin L, k ≤ ℓ.castSucc →
        η.read ℓ = -(X ℓ.castSucc * θ.read ℓ) ∧ η.write ℓ = θ.write ℓ * X ℓ.succ) ∧
      η.D = -(X (Fin.last L) * θ.D)

/-- "`θ` is regular", in the case (n): (R1) `E`, `D` and every write have rank `d`; (R3) the
derivative of every block `g_ℓ(n) = f_ℓ(n W_read^ℓ) W_write^ℓ` is invertible at some `n`. -/
structure Regular : Prop where
  rank_E : θ.E.rank = Fintype.card d
  rank_D : θ.D.rank = Fintype.card d
  rank_write : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d
  deriv_block : ∀ ℓ, ∃ n : Matrix T d ℝ, Function.Injective
    (fderiv ℝ (fun n' : Matrix T d ℝ => A.f ℓ (n' * θ.read ℓ) * θ.write ℓ) n)

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: `y ↦ y M`, as a linear map. -/
private def mulRightLin {m n p : Type*} [Fintype n] (M : Matrix n p ℝ) :
    Matrix m n ℝ →ₗ[ℝ] Matrix m p ℝ where
  toFun y := y * M
  map_add' a b := Matrix.add_mul a b M
  map_smul' c a := Matrix.smul_mul c a M

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: `y ↦ M y`, as a linear map. -/
private def mulLeftLin {m n p : Type*} [Fintype n] (M : Matrix m n ℝ) :
    Matrix n p ℝ →ₗ[ℝ] Matrix m p ℝ where
  toFun y := M * y
  map_add' a b := Matrix.mul_add M a b
  map_smul' c a := Matrix.mul_smul M c a

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the derivative of a linear map on a finite-dimensional space is the map itself. -/
private theorem fderiv_linMap {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (l : E →ₗ[ℝ] F)
    (x v : E) : fderiv ℝ (fun y => l y) x v = l v := by
  have h := (LinearMap.toContinuousLinearMap l).fderiv (x := x)
  rw [LinearMap.coe_toContinuousLinearMap'] at h
  change fderiv ℝ (⇑l) x v = l v
  rw [h]
  rfl

/-- **Lemma D.5, case (n):** `(D_L)` holds. -/
theorem claim_last [Nonempty T] (hχ : A.χ = id) : Claim A θ (Fin.last L) := by
  intro Z η hZ
  -- `X_L = Z`; no block comes after `L`
  refine ⟨fun _ => Z, rfl, fun ℓ hℓ => absurd hℓ (not_le.2 (Fin.castSucc_lt_last ℓ)), ?_⟩
  show η.D = -(Z * θ.D)
  -- the derivative in `h` of `𝓑_{>L}(h) = h D` along `h Z` is `h Z D`
  have h1 : ∀ h : Matrix T d ℝ,
      fderiv ℝ (fun h' : Matrix T d ℝ => suffix A 0 θ (Fin.last L) h') h (h * Z)
        = h * Z * θ.D := by
    intro h
    simp only [suffix_last, hχ, id]
    exact fderiv_linMap (mulRightLin θ.D) h (h * Z)
  -- the derivative in `θ` of `h D` along `η` is `h η_D`
  have h2 : ∀ h : Matrix T d ℝ,
      fderiv ℝ (fun θ' : Params A dIn dOut => suffix A 0 θ' (Fin.last L) h) θ η = h * η.D := by
    intro h
    simp only [suffix_last, hχ, id]
    exact fderiv_linMap ((mulLeftLin h).comp (Params.linD (A := A) (dIn := dIn) (dOut := dOut)))
      θ η
  -- so `h (Z D + η_D) = 0` for every `h`
  have key : ∀ h : Matrix T d ℝ, h * (Z * θ.D + η.D) = 0 := by
    intro h
    have e := hZ h
    rw [h1, h2] at e
    rw [Matrix.mul_add, ← Matrix.mul_assoc]
    exact e
  -- with `h` whose every row is `e_i`, row `t₀` of `h (Z D + η_D)` is row `i` of `Z D + η_D`
  obtain ⟨t₀⟩ := ‹Nonempty T›
  have hrow : Z * θ.D + η.D = 0 := by
    ext i c
    have e := congrFun (congrFun (key (Matrix.of fun _ j => if j = i then 1 else 0)) t₀) c
    simpa [Matrix.mul_apply] using e
  rw [eq_neg_iff_add_eq_zero, add_comm]
  exact hrow

/-- **Lemma D.2, case (n):** for a regular `θ` and analytic blocks there is, for every `k`, an open
dense set of hidden states `h` at which the derivative of `𝓑_{>k}` is injective. -/
theorem exists_open_dense_injective_fderiv_suffix (hχ : A.χ = id)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (hθ : Regular A θ) (k : Fin (L + 1)) :
    ∃ U : Set (Matrix T d ℝ), IsOpen U ∧ Dense U ∧
      ∀ h ∈ U, Function.Injective (fderiv ℝ (fun h' : Matrix T d ℝ => suffix A 0 θ k h') h) := by
  sorry

/-- **Lemma D.3, case (n) (a direction at a write).** Let `θ` be regular, and let `M` be a matrix
with `d` columns and rank `d`. If `𝐃𝓑_{>k}(w M) (w η_M) + 𝐃_θ 𝓑_{>k}(w M) η = 0` for all `w`, then
`η_M = M Z` for a `d × d` matrix `Z`, and the identity (18) holds for `k`, `Z` and `η`. -/
theorem suffixFlat_of_flat_at_write (hχ : A.χ = id)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (hθ : Regular A θ) (k : Fin (L + 1))
    {m : Type*} [Fintype m] (M : Matrix m d ℝ) (hM : M.rank = Fintype.card d)
    (ηM : Matrix m d ℝ) (η : Params A dIn dOut)
    (h : ∀ w : Matrix T m ℝ,
      fderiv ℝ (fun h' : Matrix T d ℝ => suffix A 0 θ k h') (w * M) (w * ηM)
        + fderiv ℝ (fun θ' : Params A dIn dOut => suffix A 0 θ' k (w * M)) θ η = 0) :
    ∃ Z : Matrix d d ℝ, ηM = M * Z ∧ SuffixFlat A θ k Z η := by
  sorry

/-- **Proposition D.4, case (n), first part:** if `θ` is regular and `(D_0)` holds at `θ`, every
flat direction is the direction of changes of basis at the hidden states. -/
theorem flat_le_range_cobDir_of_claim (hχ : A.χ = id)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (hθ : Regular A θ) (h0 : Claim A θ 0)
    (η : Params A dIn dOut) (hη : η ∈ flat A 0 θ) :
    ∃ X : Fin (L + 1) → Matrix d d ℝ, η = cobDir θ X := by
  sorry

/-- **Proposition D.4, case (n):** if `θ` is regular and `(D_0)` holds at `θ`, the functional
dimension at `θ` is `P - (L + 1) d²`. -/
theorem funDim_of_claim (hχ : A.χ = id)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (hθ : Regular A θ) (h0 : Claim A θ 0) :
    funDim A 0 θ + (L + 1) * Fintype.card d ^ 2
      = Module.finrank ℝ (Params A dIn dOut) := by
  sorry

end Skips
