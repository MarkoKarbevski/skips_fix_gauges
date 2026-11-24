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
direction `η` of the parameters, the identity (16) of the paper is

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

/-- The identity (16) of the paper for `k`, `Z` and `η`, in a network without skips:
`𝐃𝓑_{>k}(h) (h Z) + 𝐃_θ 𝓑_{>k}(h) η = 0` for all `h`. -/
def SuffixFlat (k : Fin (L + 1)) (Z : Matrix d d ℝ) (η : Params A dIn dOut) : Prop :=
  ∀ h : Matrix T d ℝ,
    fderiv ℝ (fun h' : Matrix T d ℝ => suffix A 0 θ k h') h (h * Z)
      + fderiv ℝ (fun θ' : Params A dIn dOut => suffix A 0 θ' k h) θ η = 0

/-- **Claim `(D_k)`,** in the case (n), for blocks without symmetries inside: every `Z` and `η`
that satisfy the identity (16) for `k` come from changes of basis `Z_k = Z, Z_{k+1}, …, Z_L` at the
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

/-- Helper: `y ↦ y M`, as a linear map. -/
private def mulRightLin {m n p : Type*} [Fintype n] (M : Matrix n p ℝ) :
    Matrix m n ℝ →ₗ[ℝ] Matrix m p ℝ where
  toFun y := y * M
  map_add' a b := Matrix.add_mul a b M
  map_smul' c a := Matrix.smul_mul c a M

/-- Helper: `y ↦ M y`, as a linear map. -/
private def mulLeftLin {m n p : Type*} [Fintype n] (M : Matrix m n ℝ) :
    Matrix n p ℝ →ₗ[ℝ] Matrix m p ℝ where
  toFun y := M * y
  map_add' a b := Matrix.mul_add M a b
  map_smul' c a := Matrix.mul_smul M c a

/-- Helper: the derivative of a linear map on a finite-dimensional space is the map itself. -/
private theorem fderiv_linMap {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (l : E →ₗ[ℝ] F)
    (x v : E) : fderiv ℝ (fun y => l y) x v = l v := by
  have h := (LinearMap.toContinuousLinearMap l).fderiv (x := x)
  rw [LinearMap.coe_toContinuousLinearMap'] at h
  change fderiv ℝ (⇑l) x v = l v
  rw [h]
  rfl

/-- In the case (n), the derivative of `h ↦ 𝓑_{>L}(h) = h D` along `v` is `v D`. -/
theorem fderiv_suffix_last (hχ : A.χ = id) (h v : Matrix T d ℝ) :
    fderiv ℝ (fun h' : Matrix T d ℝ => suffix A 0 θ (Fin.last L) h') h v = v * θ.D := by
  simp only [suffix_last, hχ, id]
  exact fderiv_linMap (mulRightLin θ.D) h v

/-- In the case (n), the derivative of `θ ↦ 𝓑_{>L}(h) = h D` along `η` is `h η_D`. -/
theorem fderiv_params_suffix_last (hχ : A.χ = id) (h : Matrix T d ℝ) (η : Params A dIn dOut) :
    fderiv ℝ (fun θ' : Params A dIn dOut => suffix A 0 θ' (Fin.last L) h) θ η = h * η.D := by
  simp only [suffix_last, hχ, id]
  exact fderiv_linMap ((mulLeftLin h).comp (Params.linD (A := A) (dIn := dIn) (dOut := dOut))) θ η

/-- **Lemma D.5, case (n):** `(D_L)` holds. -/
theorem claim_last [Nonempty T] (hχ : A.χ = id) : Claim A θ (Fin.last L) := by
  intro Z η hZ
  -- `X_L = Z`; no block comes after `L`
  refine ⟨fun _ => Z, rfl, fun ℓ hℓ => absurd hℓ (not_le.2 (Fin.castSucc_lt_last ℓ)), ?_⟩
  show η.D = -(Z * θ.D)
  -- the derivatives of `𝓑_{>L}(h) = h D`: `h Z D` in `h` along `h Z`, `h η_D` in `θ` along `η`;
  -- so `h (Z D + η_D) = 0` for every `h`
  have key : ∀ h : Matrix T d ℝ, h * (Z * θ.D + η.D) = 0 := by
    intro h
    have e := hZ h
    rw [fderiv_suffix_last A θ hχ, fderiv_params_suffix_last A θ hχ] at e
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

/-! ### The network after a hidden state is analytic and differentiable (case (n)) -/

/-- Helper: `y ↦ y M`, as a continuous linear map. -/
private noncomputable def mulRightCLM {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
    (M : Matrix n p ℝ) : Matrix m n ℝ →L[ℝ] Matrix m p ℝ :=
  LinearMap.toContinuousLinearMap (mulRightLin M)

/-- In the case (n), `𝓑_{>L}(h) = h D`. -/
theorem suffix_last_eq_mul (hχ : A.χ = id) : suffix A 0 θ (Fin.last L) = fun h => h * θ.D := by
  funext h
  rw [suffix_last, hχ, id_eq]

/-- In the case (n), `𝓑_{>ℓ-1} = 𝓑_{>ℓ} ∘ g_ℓ` with the block `g_ℓ(h) = f_ℓ(h W_read^ℓ) W_write^ℓ`. -/
theorem suffix_castSucc_eq_comp (hχ : A.χ = id) (ℓ : Fin L) :
    suffix A 0 θ ℓ.castSucc
      = suffix A 0 θ ℓ.succ ∘ fun h => A.f ℓ (h * θ.read ℓ) * θ.write ℓ := by
  funext h
  rw [suffix_castSucc, hχ, Function.comp_apply, Pi.zero_apply, Matrix.mul_zero, zero_add, id_eq]

omit [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- The block `g_ℓ(h) = f_ℓ(h W_read^ℓ) W_write^ℓ` is analytic in `h` if `f_ℓ` is. -/
theorem analyticOnNhd_block (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (ℓ : Fin L) :
    AnalyticOnNhd ℝ (fun h : Matrix T d ℝ => A.f ℓ (h * θ.read ℓ) * θ.write ℓ) Set.univ :=
  ((mulRightCLM (m := T) (θ.write ℓ)).analyticOnNhd _).comp
    ((hf ℓ).comp ((mulRightCLM (m := T) (θ.read ℓ)).analyticOnNhd _) (Set.mapsTo_univ _ _))
    (Set.mapsTo_univ _ _)

/-- In the case (n), with analytic blocks, `h ↦ 𝓑_{>k}(h)` is analytic. -/
theorem analyticOnNhd_suffix (hχ : A.χ = id) (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ)
    (k : Fin (L + 1)) : AnalyticOnNhd ℝ (suffix A 0 θ k) Set.univ := by
  induction k using Fin.reverseInduction with
  | last =>
    -- `𝓑_{>L}(h) = h D` is linear
    rw [suffix_last_eq_mul A θ hχ]
    exact (mulRightCLM (m := T) θ.D).analyticOnNhd _
  | cast ℓ ih =>
    -- `𝓑_{>ℓ-1} = 𝓑_{>ℓ} ∘ g_ℓ`
    rw [suffix_castSucc_eq_comp A θ hχ ℓ]
    exact ih.comp (analyticOnNhd_block A θ hf ℓ) (Set.mapsTo_univ _ _)

/-- The chain rule for `𝓑_{>ℓ-1} = 𝓑_{>ℓ} ∘ g_ℓ` (case (n), analytic blocks):
`𝐃𝓑_{>ℓ-1}(h) = 𝐃𝓑_{>ℓ}(g_ℓ(h)) ∘ 𝐃g_ℓ(h)`. -/
theorem fderiv_suffix_castSucc (hχ : A.χ = id) (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ)
    (ℓ : Fin L) (h : Matrix T d ℝ) :
    fderiv ℝ (suffix A 0 θ ℓ.castSucc) h
      = (fderiv ℝ (suffix A 0 θ ℓ.succ) (A.f ℓ (h * θ.read ℓ) * θ.write ℓ)).comp
          (fderiv ℝ (fun n : Matrix T d ℝ => A.f ℓ (n * θ.read ℓ) * θ.write ℓ) h) := by
  rw [suffix_castSucc_eq_comp A θ hχ ℓ]
  exact fderiv_comp h
    ((analyticOnNhd_suffix A θ hχ hf ℓ.succ) _ (Set.mem_univ _)).differentiableAt
    ((analyticOnNhd_block A θ hf ℓ) h (Set.mem_univ _)).differentiableAt

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the product of two differentiable matrix-valued maps is differentiable (as
`differentiable_matMul` in `Dimension/Functional.lean`, which is private there). -/
private theorem differentiable_matMul' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
    {f : E → Matrix m n ℝ} {g : E → Matrix n p ℝ}
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) :
    Differentiable ℝ (fun y => f y * g y) := by
  -- matrix multiplication as a bilinear map
  let B : Matrix m n ℝ →ₗ[ℝ] Matrix n p ℝ →ₗ[ℝ] Matrix m p ℝ :=
    LinearMap.mk₂ ℝ (fun a b => a * b) Matrix.add_mul (fun c a b => Matrix.smul_mul c a b)
      Matrix.mul_add (fun c a b => Matrix.mul_smul a c b)
  -- the same map with continuous linear maps (all spaces are finite-dimensional)
  let B' : Matrix m n ℝ →L[ℝ] Matrix n p ℝ →L[ℝ] Matrix m p ℝ :=
    LinearMap.toContinuousLinearMap
      ((LinearMap.toContinuousLinearMap :
        (Matrix n p ℝ →ₗ[ℝ] Matrix m p ℝ) ≃ₗ[ℝ] (Matrix n p ℝ →L[ℝ] Matrix m p ℝ)).toLinearMap ∘ₗ B)
  have hB : (fun y => f y * g y) = fun y => B' (f y) (g y) := rfl
  rw [hB]
  exact (B'.differentiable.comp hf).clm_apply hg

/-- In the case (n), with differentiable blocks, `(θ, h) ↦ 𝓑_{>k}(h)` (with the weights `θ`) is
jointly differentiable. -/
theorem differentiable_suffix_prod (hχ : A.χ = id) (hf : ∀ ℓ, Differentiable ℝ (A.f ℓ))
    (k : Fin (L + 1)) :
    Differentiable ℝ (fun p : Params A dIn dOut × Matrix T d ℝ => suffix A 0 p.1 k p.2) := by
  -- the weights are linear, hence differentiable, functions of the parameters
  have hD : Differentiable ℝ (fun θ' : Params A dIn dOut => θ'.D) :=
    (LinearMap.toContinuousLinearMap (Params.linD (A := A) (dIn := dIn) (dOut := dOut))).differentiable
  have hr : ∀ ℓ, Differentiable ℝ (fun θ' : Params A dIn dOut => θ'.read ℓ) := fun ℓ =>
    (LinearMap.toContinuousLinearMap
      (Params.linRead (A := A) (dIn := dIn) (dOut := dOut) ℓ)).differentiable
  have hw : ∀ ℓ, Differentiable ℝ (fun θ' : Params A dIn dOut => θ'.write ℓ) := fun ℓ =>
    (LinearMap.toContinuousLinearMap
      (Params.linWrite (A := A) (dIn := dIn) (dOut := dOut) ℓ)).differentiable
  induction k using Fin.reverseInduction with
  | last =>
    -- `(θ, h) ↦ h D`
    simp only [suffix_last, hχ, id_eq]
    exact differentiable_matMul' differentiable_snd (hD.comp differentiable_fst)
  | cast ℓ ih =>
    -- `(θ, h) ↦ 𝓑_{>ℓ}(f_ℓ(h W_read) W_write)`, with the weights `θ`
    simp only [suffix_castSucc, hχ, id_eq, Pi.zero_apply, Matrix.mul_zero, zero_add]
    exact ih.comp (differentiable_fst.prodMk (differentiable_matMul'
      ((hf ℓ).comp (differentiable_matMul' differentiable_snd ((hr ℓ).comp differentiable_fst)))
      ((hw ℓ).comp differentiable_fst)))

/-- In the case (n), with differentiable blocks, `θ ↦ 𝓑_{>k}(h)` is differentiable. -/
theorem differentiable_params_suffix (hχ : A.χ = id) (hf : ∀ ℓ, Differentiable ℝ (A.f ℓ))
    (k : Fin (L + 1)) (h : Matrix T d ℝ) :
    Differentiable ℝ (fun θ' : Params A dIn dOut => suffix A 0 θ' k h) := by
  have h1 : Differentiable ℝ (fun θ' : Params A dIn dOut => (θ', h)) :=
    differentiable_id.prodMk (differentiable_const h)
  have hc := (differentiable_suffix_prod A hχ hf k).comp h1
  exact hc

/-- In the case (n), with differentiable blocks, `h ↦ 𝓑_{>k}(h)` is differentiable. -/
theorem differentiable_suffix (hχ : A.χ = id) (hf : ∀ ℓ, Differentiable ℝ (A.f ℓ))
    (k : Fin (L + 1)) : Differentiable ℝ (fun h : Matrix T d ℝ => suffix A 0 θ k h) := by
  have h1 : Differentiable ℝ (fun h : Matrix T d ℝ => (θ, h)) :=
    (differentiable_const θ).prodMk differentiable_id
  have hc := (differentiable_suffix_prod A hχ hf k).comp h1
  exact hc

/-- The chain rule for `F_θ(x) = 𝓑_{>0}(x E)` (case (n), differentiable blocks): the derivative of
`θ ↦ F_θ(x)` along `η` is `𝐃𝓑_{>0}(x E)(x η_E) + 𝐃_θ 𝓑_{>0}(x E) η`. -/
theorem fderiv_eval_eq_fderiv_suffix (hχ : A.χ = id) (hf : ∀ ℓ, Differentiable ℝ (A.f ℓ))
    (x : Matrix T dIn ℝ) (η : Params A dIn dOut) :
    fderiv ℝ (fun θ' : Params A dIn dOut => eval A 0 θ' x) θ η
      = fderiv ℝ (fun h' : Matrix T d ℝ => suffix A 0 θ 0 h') (x * θ.E) (x * η.E)
        + fderiv ℝ (fun θ' : Params A dIn dOut => suffix A 0 θ' 0 (x * θ.E)) θ η := by
  -- `Φ(θ', h) = 𝓑_{>0}(h)` with the weights `θ'`, and its derivative `Φ'` at `(θ, x E)`
  let Φ : Params A dIn dOut × Matrix T d ℝ → Matrix T dOut ℝ := fun p => suffix A 0 p.1 0 p.2
  have hΦ : HasFDerivAt Φ (fderiv ℝ Φ (θ, x * θ.E)) (θ, x * θ.E) :=
    (differentiable_suffix_prod A hχ hf 0 _).hasFDerivAt
  -- `θ' ↦ x θ'_E`, a continuous linear map
  let lE : Params A dIn dOut →L[ℝ] Matrix T d ℝ := LinearMap.toContinuousLinearMap
    ((mulLeftLin x).comp (Params.linE (A := A) (dIn := dIn) (dOut := dOut)))
  -- three chain rules: `F_θ'(x) = Φ(θ', x θ'_E)`, `θ' ↦ Φ(θ', x E)` and `h ↦ Φ(θ, h)`
  have h1 : HasFDerivAt (fun θ' : Params A dIn dOut => eval A 0 θ' x)
      ((fderiv ℝ Φ (θ, x * θ.E)).comp ((ContinuousLinearMap.id ℝ _).prod lE)) θ := by
    have hc := hΦ.comp θ ((hasFDerivAt_id θ).prodMk lE.hasFDerivAt)
    have hfun : (fun θ' : Params A dIn dOut => eval A 0 θ' x) = Φ ∘ fun θ' => (id θ', lE θ') :=
      funext fun θ' => eval_eq_suffix_zero A 0 θ' x
    rw [hfun]
    exact hc
  have h2 : HasFDerivAt (fun θ' : Params A dIn dOut => suffix A 0 θ' 0 (x * θ.E))
      ((fderiv ℝ Φ (θ, x * θ.E)).comp (ContinuousLinearMap.inl ℝ _ _)) θ := by
    have hl : HasFDerivAt (fun θ' : Params A dIn dOut => (θ', x * θ.E))
        (ContinuousLinearMap.inl ℝ (Params A dIn dOut) (Matrix T d ℝ)) θ :=
      hasFDerivAt_prodMk_left θ (x * θ.E)
    have hc := hΦ.comp θ hl
    exact hc
  have h3 : HasFDerivAt (fun h' : Matrix T d ℝ => suffix A 0 θ 0 h')
      ((fderiv ℝ Φ (θ, x * θ.E)).comp (ContinuousLinearMap.inr ℝ _ _)) (x * θ.E) := by
    have hl : HasFDerivAt (fun h' : Matrix T d ℝ => (θ, h'))
        (ContinuousLinearMap.inr ℝ (Params A dIn dOut) (Matrix T d ℝ)) (x * θ.E) :=
      hasFDerivAt_prodMk_right θ (x * θ.E)
    have hc := hΦ.comp (x * θ.E) hl
    exact hc
  rw [h1.fderiv, h2.fderiv, h3.fderiv]
  -- `Φ'(η, x η_E) = Φ'(0, x η_E) + Φ'(η, 0)`
  show fderiv ℝ Φ (θ, x * θ.E) (η, x * η.E)
    = fderiv ℝ Φ (θ, x * θ.E) (0, x * η.E) + fderiv ℝ Φ (θ, x * θ.E) (η, 0)
  rw [← map_add (fderiv ℝ Φ (θ, x * θ.E)), Prod.mk_add_mk, zero_add, add_zero]

/-! ### Lemma D.2 -/

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: a matrix of rank its number of columns has a left inverse. -/
private theorem exists_left_inverse_of_rank {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq n] (M : Matrix m n ℝ) (hM : M.rank = Fintype.card n) :
    ∃ B : Matrix n m ℝ, B * M = 1 :=
  Matrix.vecMul_surjective_iff_exists_left_inverse.1
    (Matrix.vecMul_surjective_iff_rank_eq_card.2 hM)

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: a matrix of rank its number of rows has a right inverse. -/
private theorem exists_right_inverse_of_rank {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] (M : Matrix m n ℝ) (hM : M.rank = Fintype.card m) :
    ∃ B : Matrix n m ℝ, M * B = 1 :=
  Matrix.mulVec_surjective_iff_exists_right_inverse.1
    (Matrix.mulVec_surjective_iff_rank_eq_card.2 hM)

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: an analytic family `x ↦ J x` of linear maps between finite-dimensional spaces that is
injective at one point `x₀` is injective on an open dense set that contains `x₀`. With a left
inverse `K` of `J x₀`, the determinant `φ x` of `K ∘ J x` is analytic in `x` and `φ x₀ = 1`; by the
identity theorem its zero set has empty interior. -/
private theorem exists_open_dense_injective_of_analytic
    {X E F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {J : X → E →L[ℝ] F} (hJ : AnalyticOnNhd ℝ J Set.univ) {x₀ : X}
    (h₀ : Function.Injective (J x₀)) :
    ∃ U : Set X, IsOpen U ∧ Dense U ∧ x₀ ∈ U ∧ ∀ x ∈ U, Function.Injective (J x) := by
  -- a left inverse `K` of `J x₀`
  obtain ⟨K, hK⟩ :=
    (J x₀ : E →ₗ[ℝ] F).exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 h₀)
  -- the matrix of `K ∘ J x` in a basis `b` of `E`, a linear function of `J x`
  let b := Module.finBasis ℝ E
  let Ψ : (E →L[ℝ] F) →ₗ[ℝ]
      Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
    (LinearMap.toMatrix b b).toLinearMap ∘ₗ (LinearMap.llcomp ℝ E F E K) ∘ₗ
      (ContinuousLinearMap.coeLM ℝ)
  have hΨ : ∀ x, Ψ (J x) = LinearMap.toMatrix b b (K ∘ₗ (J x : E →ₗ[ℝ] F)) := fun x => rfl
  -- its determinant `φ x` is an analytic function of `x`: a polynomial in the entries
  let φ : X → ℝ := fun x => (Ψ (J x)).det
  have hentry : ∀ i j, AnalyticOnNhd ℝ (fun x => Ψ (J x) i j) Set.univ := fun i j =>
    ((LinearMap.toContinuousLinearMap ((Matrix.entryLinearMap ℝ ℝ i j) ∘ₗ Ψ)).analyticOnNhd
      _).comp hJ (Set.mapsTo_univ _ _)
  have hφ : AnalyticOnNhd ℝ φ Set.univ := by
    show AnalyticOnNhd ℝ (fun x => (Ψ (J x)).det) Set.univ
    simp only [Matrix.det_apply']
    exact Finset.analyticOnNhd_fun_sum _ fun σ _ => analyticOnNhd_const.mul
      (Finset.analyticOnNhd_fun_prod _ fun i _ => hentry (σ i) i)
  have hφcont : Continuous φ := continuousOn_univ.mp hφ.continuousOn
  -- `φ x₀ = det 1 = 1`
  have hφ₀ : φ x₀ = 1 := by
    show (Ψ (J x₀)).det = 1
    rw [hΨ, hK, LinearMap.toMatrix_id, Matrix.det_one]
  -- where `φ x ≠ 0`, `K ∘ J x` is invertible, so `J x` is injective
  have hφinj : ∀ x, φ x ≠ 0 → Function.Injective (J x) := by
    intro x hx
    have hdet : LinearMap.det (K ∘ₗ (J x : E →ₗ[ℝ] F)) ≠ 0 := by
      rw [← LinearMap.det_toMatrix b]
      exact hx
    have hbij := (Module.End.isUnit_iff _).1
      ((LinearMap.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hdet))
    have hinj := hbij.1
    rw [LinearMap.coe_comp] at hinj
    exact hinj.of_comp
  refine ⟨{x | φ x ≠ 0}, isOpen_ne_fun hφcont continuous_const, ?_, ?_, hφinj⟩
  · -- dense: if `φ` vanished on a nonempty open set, it would vanish everywhere
    rw [dense_iff_inter_open]
    rintro W hW ⟨z, hz⟩
    by_contra hne
    have hzero : φ =ᶠ[𝓝 z] 0 := Filter.eventually_of_mem (hW.mem_nhds hz) fun y hy => by
      by_contra hy'
      exact hne ⟨y, hy, hy'⟩
    have h1 := hφ.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
      (Set.mem_univ z) hzero (Set.mem_univ x₀)
    rw [hφ₀] at h1
    exact one_ne_zero h1
  · show φ x₀ ≠ 0
    rw [hφ₀]
    exact one_ne_zero

/-- **Lemma D.2, case (n):** for a regular `θ` and analytic blocks there is, for every `k`, an open
dense set of hidden states `h` at which the derivative of `𝓑_{>k}` is injective. -/
theorem exists_open_dense_injective_fderiv_suffix (hχ : A.χ = id)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (hθ : Regular A θ) (k : Fin (L + 1)) :
    ∃ U : Set (Matrix T d ℝ), IsOpen U ∧ Dense U ∧
      ∀ h ∈ U, Function.Injective (fderiv ℝ (fun h' : Matrix T d ℝ => suffix A 0 θ k h') h) := by
  induction k using Fin.reverseInduction with
  | last =>
    -- `𝐃𝓑_{>L}(h) v = v D` is injective for every `h`: `D` has rank `d`, so `D R = 1`
    obtain ⟨R, hR⟩ := exists_right_inverse_of_rank θ.D hθ.rank_D
    refine ⟨Set.univ, isOpen_univ, dense_univ, fun h _ v w hvw => ?_⟩
    rw [fderiv_suffix_last A θ hχ, fderiv_suffix_last A θ hχ] at hvw
    have hR' := congrArg (· * R) hvw
    simpa only [Matrix.mul_assoc, hR, Matrix.mul_one] using hR'
  | cast ℓ ih =>
    obtain ⟨U', -, hU'd, hU'⟩ := ih
    -- the block `g_ℓ` is analytic, and by (R3) `𝐃g_ℓ(n₀)` is injective
    have hg := analyticOnNhd_block A θ hf ℓ
    obtain ⟨n₀, hn₀⟩ := hθ.deriv_block ℓ
    -- an open set `V ∋ n₀` on which `𝐃g_ℓ` is injective
    obtain ⟨V, hVo, -, hn₀V, hV⟩ := exists_open_dense_injective_of_analytic hg.fderiv hn₀
    -- inverse function theorem: `𝐃g_ℓ(n₀)` is invertible, so `g_ℓ(V)` is a neighbourhood
    -- of `g_ℓ(n₀)`
    let e := (LinearEquiv.ofInjectiveEndo
      (fderiv ℝ (fun n : Matrix T d ℝ => A.f ℓ (n * θ.read ℓ) * θ.write ℓ) n₀ :
        Matrix T d ℝ →ₗ[ℝ] Matrix T d ℝ) hn₀).toContinuousLinearEquiv
    have hs : HasStrictFDerivAt (fun n : Matrix T d ℝ => A.f ℓ (n * θ.read ℓ) * θ.write ℓ)
        (e : Matrix T d ℝ →L[ℝ] Matrix T d ℝ) n₀ := by
      have he : (e : Matrix T d ℝ →L[ℝ] Matrix T d ℝ)
          = fderiv ℝ (fun n : Matrix T d ℝ => A.f ℓ (n * θ.read ℓ) * θ.write ℓ) n₀ :=
        ContinuousLinearMap.ext fun v => rfl
      rw [he]
      exact (hg n₀ (Set.mem_univ _)).hasStrictFDerivAt
    have hnhds : (fun n : Matrix T d ℝ => A.f ℓ (n * θ.read ℓ) * θ.write ℓ) '' V
        ∈ 𝓝 (A.f ℓ (n₀ * θ.read ℓ) * θ.write ℓ) := by
      have hm := Filter.image_mem_map
        (m := fun n : Matrix T d ℝ => A.f ℓ (n * θ.read ℓ) * θ.write ℓ) (hVo.mem_nhds hn₀V)
      rw [hs.map_nhds_eq_of_equiv] at hm
      exact hm
    -- it meets the dense set `U'`: some `h₁ ∈ V` has `g_ℓ(h₁) ∈ U'`
    obtain ⟨_, hyU', h₁, hh₁V, rfl⟩ := hU'd.inter_nhds_nonempty hnhds
    -- at `h₁`, `𝐃𝓑_{>ℓ-1}(h₁) = 𝐃𝓑_{>ℓ}(g_ℓ(h₁)) ∘ 𝐃g_ℓ(h₁)` is injective
    have hinj₁ : Function.Injective (fderiv ℝ (suffix A 0 θ ℓ.castSucc) h₁) := by
      rw [fderiv_suffix_castSucc A θ hχ hf ℓ h₁, ContinuousLinearMap.coe_comp]
      exact (hU' _ hyU').comp (hV h₁ hh₁V)
    -- so `𝐃𝓑_{>ℓ-1}` is injective on an open dense set
    obtain ⟨U, hUo, hUd, -, hU⟩ :=
      exists_open_dense_injective_of_analytic (analyticOnNhd_suffix A θ hχ hf ℓ.castSucc).fderiv
        hinj₁
    exact ⟨U, hUo, hUd, hU⟩

/-- **Lemma D.3, case (n) (a direction at a write).** Let `θ` be regular, and let `M` be a matrix
with `d` columns and rank `d`. If `𝐃𝓑_{>k}(w M) (w η_M) + 𝐃_θ 𝓑_{>k}(w M) η = 0` for all `w`, then
`η_M = M Z` for a `d × d` matrix `Z`, and the identity (16) holds for `k`, `Z` and `η`. -/
theorem suffixFlat_of_flat_at_write [Nonempty T] (hχ : A.χ = id)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (hθ : Regular A θ) (k : Fin (L + 1))
    {m : Type*} [Fintype m] (M : Matrix m d ℝ) (hM : M.rank = Fintype.card d)
    (ηM : Matrix m d ℝ) (η : Params A dIn dOut)
    (h : ∀ w : Matrix T m ℝ,
      fderiv ℝ (fun h' : Matrix T d ℝ => suffix A 0 θ k h') (w * M) (w * ηM)
        + fderiv ℝ (fun θ' : Params A dIn dOut => suffix A 0 θ' k (w * M)) θ η = 0) :
    ∃ Z : Matrix d d ℝ, ηM = M * Z ∧ SuffixFlat A θ k Z η := by
  classical
  -- a left inverse `M⁺` of `M` (rank `d`)
  obtain ⟨Mp, hMp⟩ := exists_left_inverse_of_rank M hM
  -- a hidden state `h₀` at which `𝐃𝓑_{>k}` is injective (Lemma D.2)
  obtain ⟨U, -, hUd, hU⟩ := exists_open_dense_injective_fderiv_suffix A θ hχ hf hθ k
  obtain ⟨h₀, hh₀⟩ := hUd.nonempty
  have hw₀ : h₀ * Mp * M = h₀ := by rw [Matrix.mul_assoc, hMp, Matrix.mul_one]
  -- `w M = 0` implies `w η_M = 0`: subtract the identities at `h₀ M⁺` and at `h₀ M⁺ + w`,
  -- two preimages of `h₀`
  have hker : ∀ w : Matrix T m ℝ, w * M = 0 → w * ηM = 0 := by
    intro w hw
    have hw₁ : (h₀ * Mp + w) * M = h₀ := by rw [Matrix.add_mul, hw, add_zero, hw₀]
    have e₀ := h (h₀ * Mp)
    have e₁ := h (h₀ * Mp + w)
    rw [hw₀] at e₀
    rw [hw₁, Matrix.add_mul, map_add, add_right_comm, e₀, zero_add] at e₁
    exact hU h₀ hh₀ (by rw [e₁, map_zero])
  -- every row of `(1 - M M⁺) η_M` vanishes (`1 - M M⁺` kills `M`; take `w` with equal rows)
  obtain ⟨t₀⟩ := ‹Nonempty T›
  have hP : (1 - M * Mp) * M = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hMp, Matrix.mul_one, sub_self]
  have hPη : (1 - M * Mp) * ηM = 0 := by
    ext i c
    have hwM : (Matrix.of fun (_ : T) j => (1 - M * Mp : Matrix m m ℝ) i j) * M = 0 := by
      ext t c'
      simpa only [Matrix.mul_apply, Matrix.of_apply, Matrix.zero_apply] using
        congrFun (congrFun hP i) c'
    simpa only [Matrix.mul_apply, Matrix.of_apply, Matrix.zero_apply] using
      congrFun (congrFun (hker _ hwM) t₀) c
  -- so `η_M = M Z` with `Z = M⁺ η_M`
  have hZ : ηM = M * (Mp * ηM) := by
    rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at hPη
    rw [← Matrix.mul_assoc]
    exact hPη
  refine ⟨Mp * ηM, hZ, ?_⟩
  -- the identity (16) at `h`: the hypothesis at `w = h M⁺`, with `w M = h` and `w η_M = h Z`
  intro h'
  have e := h (h' * Mp)
  have hw : h' * Mp * M = h' := by rw [Matrix.mul_assoc, hMp, Matrix.mul_one]
  rw [hw, Matrix.mul_assoc] at e
  exact e

/-- **Proposition D.4, case (n), first part:** if `θ` is regular and `(D_0)` holds at `θ`, every
flat direction is the direction of changes of basis at the hidden states. -/
theorem flat_le_range_cobDir_of_claim [Nonempty T] (hχ : A.χ = id)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (hθ : Regular A θ) (h0 : Claim A θ 0)
    (η : Params A dIn dOut) (hη : η ∈ flat A 0 θ) :
    ∃ X : Fin (L + 1) → Matrix d d ℝ, η = cobDir θ X := by
  have hfd : ∀ ℓ, Differentiable ℝ (A.f ℓ) := fun ℓ =>
    differentiableOn_univ.1 (hf ℓ).differentiableOn
  -- for every input `x`: `0 = 𝐃_θ F(x) η = 𝐃𝓑_{>0}(x E)(x η_E) + 𝐃_θ 𝓑_{>0}(x E) η`
  have hx : ∀ x : Matrix T dIn ℝ,
      fderiv ℝ (fun h' : Matrix T d ℝ => suffix A 0 θ 0 h') (x * θ.E) (x * η.E)
        + fderiv ℝ (fun θ' : Params A dIn dOut => suffix A 0 θ' 0 (x * θ.E)) θ η = 0 := by
    intro x
    rw [← fderiv_eval_eq_fderiv_suffix A θ hχ hfd x η]
    exact LinearMap.mem_ker.1 ((Submodule.mem_iInf _).1 hη x)
  -- Lemma D.3 at the embedding (rank `d` by (R1)): `η_E = E Z` and the identity (16) for `k = 0`
  obtain ⟨Z, hEZ, hZ⟩ := suffixFlat_of_flat_at_write A θ hχ hf hθ 0 θ.E hθ.rank_E η.E η hx
  -- the claim `(D_0)` gives the changes of basis `X` with `X_0 = Z`
  obtain ⟨X, hX0, hX, hXD⟩ := h0 Z η hZ
  refine ⟨X, Params.ext' ?_ (fun ℓ => (hX ℓ (Fin.zero_le _)).1)
    (fun ℓ => (hX ℓ (Fin.zero_le _)).2) hXD⟩
  show η.E = θ.E * X 0
  rw [hX0, hEZ]

/-- **Proposition D.4, case (n):** if `θ` is regular and `(D_0)` holds at `θ`, the functional
dimension at `θ` is `P - (L + 1) d²`. -/
theorem funDim_of_claim [Nonempty T] (hχ : A.χ = id)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (hθ : Regular A θ) (h0 : Claim A θ 0) :
    funDim A 0 θ + (L + 1) * Fintype.card d ^ 2
      = Module.finrank ℝ (Params A dIn dOut) := by
  have hfd : ∀ ℓ, Differentiable ℝ (A.f ℓ) := fun ℓ =>
    differentiableOn_univ.1 (hf ℓ).differentiableOn
  have hdiff : ∀ x : Matrix T dIn ℝ,
      DifferentiableAt ℝ (fun θ' : Params A dIn dOut => eval A 0 θ' x) θ :=
    fun x => (differentiable_eval hfd (by rw [hχ]; exact differentiable_id) x).differentiableAt
  -- `K(θ)` is the range of `X ↦ cobDir θ X`
  have hflat : flat A 0 θ = LinearMap.range (cobDirLin θ) := by
    apply le_antisymm
    · intro η hη
      obtain ⟨X, rfl⟩ := flat_le_range_cobDir_of_claim A θ hχ hf hθ h0 η hη
      exact ⟨X, rfl⟩
    · rintro _ ⟨X, rfl⟩
      exact cobDir_mem_flat_skipless θ hχ hfd X
  -- of dimension `(L + 1) d²` (Lemma B.1), and `fd(θ) + dim K(θ) = P`
  have h := funDim_add_finrank_flat θ hdiff
  rwa [hflat, LinearMap.finrank_range_of_inj (f := cobDirLin θ)
    (cobDir_injective θ hθ.rank_E hθ.rank_write), finrank_cobDomain] at h

end Skips
