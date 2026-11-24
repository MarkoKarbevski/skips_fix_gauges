import SkipsLean.Depth.SuffixGated
import Mathlib.NumberTheory.Transcendental.Liouville.LiouvilleNumber
import Mathlib.RingTheory.Algebraic.Integral

/-!
# Cones and good parameters

Paper (dimension): Appendix D.5, "Cones and good parameters". "A cone is a set of rows that
contains `λ h` for each of its rows `h` and every number `λ > 0`. Let `C_0, …, C_L` be open convex
cones in `ℝ^{1×d}` that do not contain `0`, one for each hidden state. We call `θ` good for these
cones if (R1) holds and every block `ℓ`, with its gate columns `c_j`, its write rows `a_j` and the
entries `ι_j(n)` of `ι^ℓ(n)`, satisfies:
(K1) `n c_j ≠ 0` for every `n ∈ C_{ℓ-1}` and every `j`. So every gate has one sign on `C_{ℓ-1}`.
Let `A_ℓ` be the set of the hidden units `j` with `n c_j > 0` on `C_{ℓ-1}`, the active ones, and
let `g°_ℓ(n) = ∑_{j ∈ A_ℓ} (n c_j) ι_j(n) a_j` be the block with its gates frozen. …
(K2) `g°_ℓ(n) ∈ C_ℓ` for every `n ∈ C_{ℓ-1}`, and `D g°_ℓ(n)` is invertible at some row `n`.
(K3) No `a_j` vanishes, and in a gated block no value column `e_j` vanishes. For GELU and GeGLU
blocks the matrices `c_1 c_1^⊤, …, c_q c_q^⊤` are linearly independent over `ℚ`, and for SwiGLU
blocks the columns `c_1, …, c_q` are."
Here `ι_j(n) = n e_j` in a gated block and `ι_j(n) = 1` in a GELU block.

In Lean:
* the cones are sets of rows `d → ℝ`; a cone is also required to be nonempty, which the paper uses
  without saying (its proofs take rows of the cones);
* the active sets `A_ℓ` are given as data, with (K1) in the form "`n c_j > 0` on `C_{ℓ-1}` for
  `j ∈ A_ℓ` and `n c_j < 0` for `j ∉ A_ℓ`", which is (K1) because a convex cone is connected;
* the conditions do not involve the activation, so "good" is defined once for gated networks and
  once for MLP networks (the GELU blocks); the independence over `ℚ` of (K3), which depends on the
  kind of block, is a separate hypothesis of the statements that use it.

Stated here: the sentence "A good `θ` is regular", and Lemma D.13 in the form: there are cones and
a parameter that is good for them and has the independence of (K3) (the paper's `θ†`, with the
positive orthant as every cone). Lemma D.12, the step from `(D_{k+1})` to `(D_k)` at good
parameters, is in `Depth/StepGated.lean`.
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise Topology

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {σ : ℝ → ℝ} {χ : Matrix T d ℝ → Matrix T d ℝ} {hid : Fin L → Type}
  [∀ ℓ, Fintype (hid ℓ)]

/-- An open convex cone of rows that does not contain `0` (and is not empty). -/
structure IsOpenConvexCone (C : Set (d → ℝ)) : Prop where
  isOpen : IsOpen C
  convex : Convex ℝ C
  nonempty : C.Nonempty
  zero_notMem : (0 : d → ℝ) ∉ C
  smul_mem : ∀ n ∈ C, ∀ lam : ℝ, 0 < lam → lam • n ∈ C

/-- The gated block `ℓ` with its gates frozen on the active set `A`:
`g°(n) = ∑_{j ∈ A} (n c_j) (n e_j) a_j`. -/
def frozenGated (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut) (ℓ : Fin L)
    (A : Finset (hid ℓ)) (n : d → ℝ) : d → ℝ :=
  ∑ j ∈ A, ((n ⬝ᵥ (θ.read ℓ)ᵀ (Sum.inl j)) * (n ⬝ᵥ (θ.read ℓ)ᵀ (Sum.inr j))) • θ.write ℓ j

/-- The MLP block `ℓ` with its hidden units frozen on the active set `A` (a GELU block with its
gates frozen): `g°(n) = ∑_{j ∈ A} (n c_j) a_j`. -/
def frozenMlp (θ : Params (Arch.mlp (T := T) (d := d) σ χ hid) dIn dOut) (ℓ : Fin L)
    (A : Finset (hid ℓ)) (n : d → ℝ) : d → ℝ :=
  ∑ j ∈ A, (n ⬝ᵥ (θ.read ℓ)ᵀ j) • θ.write ℓ j

/-- **`θ` is good for the cones `C_0, …, C_L`,** for a network of gated blocks, with the active
sets `A_ℓ`: (R1), (K1), (K2) and the part of (K3) that does not depend on the kind of gate. -/
structure GoodForConesGated (C : Fin (L + 1) → Set (d → ℝ)) (A : ∀ ℓ, Finset (hid ℓ))
    (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut) : Prop where
  cone : ∀ k, IsOpenConvexCone (C k)
  /-- (R1) -/
  rank_E : θ.E.rank = Fintype.card d
  /-- (R1) -/
  rank_D : θ.D.rank = Fintype.card d
  /-- (R1) -/
  rank_write : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d
  /-- (K1): the gates of the active units are positive on the cone that the block reads -/
  gate_pos : ∀ ℓ, ∀ n ∈ C ℓ.castSucc, ∀ j ∈ A ℓ, 0 < n ⬝ᵥ (θ.read ℓ)ᵀ (Sum.inl j)
  /-- (K1): the gates of the other units are negative there -/
  gate_neg : ∀ ℓ, ∀ n ∈ C ℓ.castSucc, ∀ j ∉ A ℓ, n ⬝ᵥ (θ.read ℓ)ᵀ (Sum.inl j) < 0
  /-- (K2): the frozen block maps the cone that it reads into the next cone -/
  frozen_mem : ∀ ℓ, ∀ n ∈ C ℓ.castSucc, frozenGated θ ℓ (A ℓ) n ∈ C ℓ.succ
  /-- (K2): the derivative of the frozen block is invertible at some row -/
  frozen_deriv : ∀ ℓ, ∃ n : d → ℝ, Function.Injective (fderiv ℝ (frozenGated θ ℓ (A ℓ)) n)
  /-- (K3): no write row vanishes -/
  write_ne_zero : ∀ ℓ (j : hid ℓ), θ.write ℓ j ≠ 0
  /-- (K3): no value column vanishes -/
  value_ne_zero : ∀ ℓ (j : hid ℓ), (θ.read ℓ)ᵀ (Sum.inr j) ≠ 0

/-- **`θ` is good for the cones `C_0, …, C_L`,** for a network of MLP blocks (the GELU blocks of
the paper), with the active sets `A_ℓ`: (R1), (K1), (K2) and "no `a_j` vanishes" of (K3). -/
structure GoodForConesMlp (C : Fin (L + 1) → Set (d → ℝ)) (A : ∀ ℓ, Finset (hid ℓ))
    (θ : Params (Arch.mlp (T := T) (d := d) σ χ hid) dIn dOut) : Prop where
  cone : ∀ k, IsOpenConvexCone (C k)
  /-- (R1) -/
  rank_E : θ.E.rank = Fintype.card d
  /-- (R1) -/
  rank_D : θ.D.rank = Fintype.card d
  /-- (R1) -/
  rank_write : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d
  /-- (K1) -/
  gate_pos : ∀ ℓ, ∀ n ∈ C ℓ.castSucc, ∀ j ∈ A ℓ, 0 < n ⬝ᵥ (θ.read ℓ)ᵀ j
  /-- (K1) -/
  gate_neg : ∀ ℓ, ∀ n ∈ C ℓ.castSucc, ∀ j ∉ A ℓ, n ⬝ᵥ (θ.read ℓ)ᵀ j < 0
  /-- (K2) -/
  frozen_mem : ∀ ℓ, ∀ n ∈ C ℓ.castSucc, frozenMlp θ ℓ (A ℓ) n ∈ C ℓ.succ
  /-- (K2) -/
  frozen_deriv : ∀ ℓ, ∃ n : d → ℝ, Function.Injective (fderiv ℝ (frozenMlp θ ℓ (A ℓ)) n)
  /-- (K3): no write row vanishes -/
  write_ne_zero : ∀ ℓ (j : hid ℓ), θ.write ℓ j ≠ 0

/-! ### A good `θ` is regular -/

section Regular

open Filter

omit [DecidableEq d] in
/-- `v ↦ v ⬝ c`, as a continuous linear map. -/
private noncomputable def dotCLM (c : d → ℝ) : (d → ℝ) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => v ⬝ᵥ c
      map_add' := fun v w => add_dotProduct v w c
      map_smul' := fun r v => smul_dotProduct r v c }

private theorem dotCLM_apply (c v : d → ℝ) : dotCLM c v = v ⬝ᵥ c := rfl

omit [DecidableEq d] in
/-- `v ↦ (v ⬝ c) a`, as a continuous linear map. -/
private noncomputable def dotSmul (c a : d → ℝ) : (d → ℝ) →L[ℝ] (d → ℝ) :=
  (dotCLM c).smulRight a

private theorem dotSmul_apply (c a v : d → ℝ) : dotSmul c a v = (v ⬝ᵥ c) • a := rfl

omit [DecidableEq d] in
/-- The derivative of a gated unit `x ↦ σ(x c) (x e) a`:
`v ↦ σ'(x c) (x e) (v c) a + σ(x c) (v e) a`. -/
private theorem hasFDerivAt_gatedUnit {σ' : ℝ → ℝ} (hσ : ∀ y, HasDerivAt σ (σ' y) y)
    (c e a x : d → ℝ) :
    HasFDerivAt (fun x : d → ℝ => (σ (x ⬝ᵥ c) * (x ⬝ᵥ e)) • a)
      ((σ' (x ⬝ᵥ c) * (x ⬝ᵥ e)) • dotSmul c a + σ (x ⬝ᵥ c) • dotSmul e a) x := by
  have h1 := (hσ (x ⬝ᵥ c)).comp_hasFDerivAt x (dotCLM c).hasFDerivAt
  have h2 := (h1.mul (dotCLM e).hasFDerivAt).smul_const a
  refine h2.congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
  funext k
  simp only [ContinuousLinearMap.smulRight_apply, _root_.add_apply,
    FunLike.coe_smul, Pi.smul_apply, Function.comp_apply, dotCLM_apply,
    dotSmul_apply, Pi.add_apply, smul_eq_mul]
  ring

omit [DecidableEq d] in
/-- The derivative of an MLP unit `x ↦ σ(x c) a`: `v ↦ σ'(x c) (v c) a`. -/
private theorem hasFDerivAt_mlpUnit {σ' : ℝ → ℝ} (hσ : ∀ y, HasDerivAt σ (σ' y) y)
    (c a x : d → ℝ) :
    HasFDerivAt (fun x : d → ℝ => σ (x ⬝ᵥ c) • a) (σ' (x ⬝ᵥ c) • dotSmul c a) x := by
  have h1 := ((hσ (x ⬝ᵥ c)).comp_hasFDerivAt x (dotCLM c).hasFDerivAt).smul_const a
  refine h1.congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
  funext k
  simp only [ContinuousLinearMap.smulRight_apply, FunLike.coe_smul, Pi.smul_apply,
    dotCLM_apply, dotSmul_apply, smul_eq_mul]
  ring

omit [Fintype T] [DecidableEq d] in
/-- Helper: a map acting row by row, `n ↦ (t ↦ g (n t))`, has at the matrix all of whose rows are
`x` the derivative `V ↦ (t ↦ G (V t))`, which is injective if `G` is. -/
private theorem injective_fderiv_rowwise [Finite T] {g : (d → ℝ) → (d → ℝ)}
    {G : (d → ℝ) →L[ℝ] (d → ℝ)} {x : d → ℝ} (hg : HasFDerivAt g G x)
    (hG : Function.Injective G) :
    Function.Injective (fderiv ℝ (fun n : T → d → ℝ => fun t => g (n t)) (fun _ => x)) := by
  have : Fintype T := Fintype.ofFinite T
  have h : HasFDerivAt (fun n : T → d → ℝ => fun t => g (n t))
      (ContinuousLinearMap.pi fun t => G.comp (ContinuousLinearMap.proj t)) (fun _ => x) :=
    hasFDerivAt_pi.2 fun t =>
      hg.comp (fun _ : T => x) (hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : T => d → ℝ) t _)
  rw [h.fderiv]
  intro V W hVW
  funext t
  exact hG (congrFun hVW t)

omit [Fintype T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- A gated block acts row by row: row `t` of `f(n W_read) W_write` is
`∑_j σ(n_t c_j) (n_t e_j) a_j`. -/
private theorem block_gated_eq (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut)
    (ℓ : Fin L) :
    (fun n : Matrix T d ℝ => (Arch.gated σ χ hid).f ℓ (n * θ.read ℓ) * θ.write ℓ) =
      fun n t => ∑ j, (σ (n t ⬝ᵥ (θ.read ℓ)ᵀ (Sum.inl j)) * (n t ⬝ᵥ (θ.read ℓ)ᵀ (Sum.inr j))) •
        θ.write ℓ j := by
  funext n t k
  change ((Matrix.of fun t i => σ ((n * θ.read ℓ) t (Sum.inl i)) * (n * θ.read ℓ) t (Sum.inr i)) *
    θ.write ℓ) t k = _
  simp only [Matrix.mul_apply, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    dotProduct, Matrix.transpose_apply]

omit [Fintype T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- An MLP block acts row by row: row `t` of `σ(n W_read) W_write` is `∑_j σ(n_t c_j) a_j`. -/
private theorem block_mlp_eq (θ : Params (Arch.mlp (T := T) (d := d) σ χ hid) dIn dOut)
    (ℓ : Fin L) :
    (fun n : Matrix T d ℝ => (Arch.mlp σ χ hid).f ℓ (n * θ.read ℓ) * θ.write ℓ) =
      fun n t => ∑ j, σ (n t ⬝ᵥ (θ.read ℓ)ᵀ j) • θ.write ℓ j := by
  funext n t k
  change ((n * θ.read ℓ).map σ * θ.write ℓ) t k = _
  simp only [Matrix.mul_apply, Matrix.map_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    dotProduct, Matrix.transpose_apply]


/-- Helper (a copy of the private lemma of `Depth/Suffix.lean`): an analytic family `J` of linear
maps that is injective at one point `x₀` is injective on an open dense set that contains `x₀`. With
a left inverse `K` of `J x₀`, the determinant `φ x` of `K ∘ J x` is analytic in `x` and `φ x₀ = 1`;
by the identity theorem its zero set has empty interior. -/
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

omit [DecidableEq d] in
/-- Helper: an analytic map of rows with an injective derivative at one row has an injective
derivative at some row of any nonempty open set (the paper: "take `ξ ∈ C_{ℓ-1}` with `Dg°_ℓ(ξ)`
invertible"). -/
private theorem exists_mem_injective_fderiv {g : (d → ℝ) → (d → ℝ)}
    (hg : AnalyticOnNhd ℝ g Set.univ) {C : Set (d → ℝ)} (hC : IsOpen C) (hCne : C.Nonempty)
    (h : ∃ n, Function.Injective (fderiv ℝ g n)) :
    ∃ ξ ∈ C, Function.Injective (fderiv ℝ g ξ) := by
  obtain ⟨n₀, hn₀⟩ := h
  obtain ⟨U, -, hUd, -, hU⟩ := exists_open_dense_injective_of_analytic hg.fderiv hn₀
  obtain ⟨ξ, hξC, hξU⟩ := hUd.inter_open_nonempty C hC hCne
  exact ⟨ξ, hξC, hU ξ hξU⟩

omit [Fintype T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- The frozen gated block is a polynomial, hence analytic. -/
private theorem analyticOnNhd_frozenGated
    (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut) (ℓ : Fin L) (A : Finset (hid ℓ)) :
    AnalyticOnNhd ℝ (frozenGated θ ℓ A) Set.univ := by
  show AnalyticOnNhd ℝ (fun n => ∑ j ∈ A, ((n ⬝ᵥ (θ.read ℓ)ᵀ (Sum.inl j)) *
    (n ⬝ᵥ (θ.read ℓ)ᵀ (Sum.inr j))) • θ.write ℓ j) Set.univ
  refine Finset.analyticOnNhd_fun_sum _ fun j _ => ?_
  have h := (((dotCLM ((θ.read ℓ)ᵀ (Sum.inl j))).analyticOnNhd Set.univ).mul
    ((dotCLM ((θ.read ℓ)ᵀ (Sum.inr j))).analyticOnNhd Set.univ)).smul
      (analyticOnNhd_const (v := θ.write ℓ j))
  exact h

omit [Fintype T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- The frozen MLP block is linear, hence analytic. -/
private theorem analyticOnNhd_frozenMlp
    (θ : Params (Arch.mlp (T := T) (d := d) σ χ hid) dIn dOut) (ℓ : Fin L) (A : Finset (hid ℓ)) :
    AnalyticOnNhd ℝ (frozenMlp θ ℓ A) Set.univ := by
  show AnalyticOnNhd ℝ (fun n => ∑ j ∈ A, (n ⬝ᵥ (θ.read ℓ)ᵀ j) • θ.write ℓ j) Set.univ
  refine Finset.analyticOnNhd_fun_sum _ fun j _ => ?_
  have h := (dotSmul ((θ.read ℓ)ᵀ j) (θ.write ℓ j)).analyticOnNhd Set.univ
  exact h

omit [Fintype T] [Fintype dIn] [Fintype dOut] in
/-- The derivative of the frozen gated block at `ξ`:
`v ↦ ∑_{j ∈ A} ((ξ e_j)(v c_j) + (ξ c_j)(v e_j)) a_j`. -/
private theorem hasFDerivAt_frozenGated
    (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut) (ℓ : Fin L) (A : Finset (hid ℓ))
    (ξ : d → ℝ) :
    HasFDerivAt (frozenGated θ ℓ A)
      (∑ j ∈ A, ((ξ ⬝ᵥ (θ.read ℓ)ᵀ (Sum.inr j)) • dotSmul ((θ.read ℓ)ᵀ (Sum.inl j)) (θ.write ℓ j) +
        (ξ ⬝ᵥ (θ.read ℓ)ᵀ (Sum.inl j)) • dotSmul ((θ.read ℓ)ᵀ (Sum.inr j)) (θ.write ℓ j))) ξ := by
  have h := HasFDerivAt.fun_sum (u := A) fun j _ =>
    hasFDerivAt_gatedUnit (σ := id) (fun y => hasDerivAt_id y) ((θ.read ℓ)ᵀ (Sum.inl j))
      ((θ.read ℓ)ᵀ (Sum.inr j)) (θ.write ℓ j) ξ
  simp only [id, one_mul] at h
  exact h

omit [Fintype T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- The derivative of the frozen MLP block (at any `ξ`): `v ↦ ∑_{j ∈ A} (v c_j) a_j`. -/
private theorem hasFDerivAt_frozenMlp
    (θ : Params (Arch.mlp (T := T) (d := d) σ χ hid) dIn dOut) (ℓ : Fin L) (A : Finset (hid ℓ))
    (ξ : d → ℝ) :
    HasFDerivAt (frozenMlp θ ℓ A) (∑ j ∈ A, dotSmul ((θ.read ℓ)ᵀ j) (θ.write ℓ j)) ξ :=
  HasFDerivAt.fun_sum fun _ _ => (dotSmul _ _).hasFDerivAt

/-- Helper: the injective continuous linear maps form an open set, so maps that tend to an
injective one are eventually injective. -/
private theorem eventually_injective_of_tendsto {E F ι : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {l : Filter ι} {Λ : ι → E →L[ℝ] F} {Λ₀ : E →L[ℝ] F} (h : Tendsto Λ l (𝓝 Λ₀))
    (h₀ : Function.Injective Λ₀) : ∀ᶠ s in l, Function.Injective (Λ s) :=
  h (ContinuousLinearMap.isOpen_injective.mem_nhds h₀)

omit [DecidableEq d] in
/-- Helper (the paper's limit `t → ∞`, gated blocks): if the gates `ξ c_j` are positive on `A` and
negative off `A`, and the frozen derivative `v ↦ ∑_{j ∈ A} ((ξ e_j)(v c_j) + (ξ c_j)(v e_j)) a_j` is
injective, then the derivative of the gated row map at `s ξ` is injective for some `s > 0`: divided
by `s`, it tends to the frozen derivative, since `σ'(s z) → 1`, `σ(s z)/s → z` for `z > 0` and
`σ'(s z) → 0`, `σ(s z)/s → 0` for `z < 0`. -/
private theorem exists_injective_gatedRow {ι : Type*} [Fintype ι] {σ' : ℝ → ℝ}
    (hpos : ∀ z, 0 < z → Tendsto (fun s => σ' (s * z)) atTop (𝓝 1) ∧
      Tendsto (fun s => σ (s * z) / s) atTop (𝓝 z))
    (hneg : ∀ z, z < 0 → Tendsto (fun s => σ' (s * z)) atTop (𝓝 0) ∧
      Tendsto (fun s => σ (s * z) / s) atTop (𝓝 0))
    (c e a : ι → d → ℝ) (A : Finset ι) (ξ : d → ℝ)
    (hA : ∀ j ∈ A, 0 < ξ ⬝ᵥ c j) (hA' : ∀ j ∉ A, ξ ⬝ᵥ c j < 0)
    (h0 : Function.Injective (∑ j ∈ A, ((ξ ⬝ᵥ e j) • dotSmul (c j) (a j) +
      (ξ ⬝ᵥ c j) • dotSmul (e j) (a j)) : (d → ℝ) →L[ℝ] (d → ℝ))) :
    ∃ x : d → ℝ, Function.Injective (∑ j, ((σ' (x ⬝ᵥ c j) * (x ⬝ᵥ e j)) • dotSmul (c j) (a j) +
      σ (x ⬝ᵥ c j) • dotSmul (e j) (a j)) : (d → ℝ) →L[ℝ] (d → ℝ)) := by
  classical
  -- the coefficients of the derivative at `s ξ`, divided by `s`, and their limits
  have hα : ∀ j, Tendsto (fun s => σ' (s * (ξ ⬝ᵥ c j)) * (ξ ⬝ᵥ e j)) atTop
      (𝓝 (if j ∈ A then ξ ⬝ᵥ e j else 0)) := by
    intro j
    by_cases hj : j ∈ A
    · simpa [hj] using ((hpos _ (hA j hj)).1).mul_const (ξ ⬝ᵥ e j)
    · simpa [hj] using ((hneg _ (hA' j hj)).1).mul_const (ξ ⬝ᵥ e j)
  have hβ : ∀ j, Tendsto (fun s => σ (s * (ξ ⬝ᵥ c j)) / s) atTop
      (𝓝 (if j ∈ A then ξ ⬝ᵥ c j else 0)) := by
    intro j
    by_cases hj : j ∈ A
    · simpa [hj] using (hpos _ (hA j hj)).2
    · simpa [hj] using (hneg _ (hA' j hj)).2
  have hΛ := tendsto_finsetSum (Finset.univ : Finset ι) fun j _ =>
    ((hα j).smul_const (dotSmul (c j) (a j))).add ((hβ j).smul_const (dotSmul (e j) (a j)))
  -- the limit is the frozen derivative
  have hlim : (∑ j, ((if j ∈ A then ξ ⬝ᵥ e j else 0) • dotSmul (c j) (a j) +
      (if j ∈ A then ξ ⬝ᵥ c j else 0) • dotSmul (e j) (a j))) =
      ∑ j ∈ A, ((ξ ⬝ᵥ e j) • dotSmul (c j) (a j) + (ξ ⬝ᵥ c j) • dotSmul (e j) (a j)) := by
    have h := Finset.sum_ite_mem Finset.univ A fun j =>
      (ξ ⬝ᵥ e j) • dotSmul (c j) (a j) + (ξ ⬝ᵥ c j) • dotSmul (e j) (a j)
    rw [Finset.univ_inter] at h
    rw [← h]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> simp
  rw [hlim] at hΛ
  obtain ⟨s, hsinj, hs⟩ :=
    ((eventually_injective_of_tendsto hΛ h0).and (eventually_gt_atTop 0)).exists
  refine ⟨s • ξ, ?_⟩
  -- the derivative at `s ξ` is `s` times the map at `s`
  have hD : (∑ j, ((σ' ((s • ξ) ⬝ᵥ c j) * ((s • ξ) ⬝ᵥ e j)) • dotSmul (c j) (a j) +
      σ ((s • ξ) ⬝ᵥ c j) • dotSmul (e j) (a j)) : (d → ℝ) →L[ℝ] (d → ℝ)) =
      s • ∑ j, ((σ' (s * (ξ ⬝ᵥ c j)) * (ξ ⬝ᵥ e j)) • dotSmul (c j) (a j) +
        (σ (s * (ξ ⬝ᵥ c j)) / s) • dotSmul (e j) (a j)) := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_add, smul_smul, smul_smul, smul_dotProduct, smul_dotProduct, smul_eq_mul,
      smul_eq_mul]
    congr 2
    · ring
    · field_simp
  rw [hD]
  intro v w hvw
  rw [_root_.smul_apply, _root_.smul_apply] at hvw
  exact hsinj (smul_right_injective _ hs.ne' hvw)

omit [DecidableEq d] in
/-- Helper (the limit `t → ∞`, MLP blocks): if the gates `ξ c_j` are positive on `A` and negative
off `A`, and `v ↦ ∑_{j ∈ A} (v c_j) a_j` is injective, then the derivative of the MLP row map at
`s ξ` is injective for some `s`: it tends to that map, since `σ'(s z) → 1` for `z > 0` and
`σ'(s z) → 0` for `z < 0`. -/
private theorem exists_injective_mlpRow {ι : Type*} [Fintype ι] {σ' : ℝ → ℝ}
    (hpos : ∀ z, 0 < z → Tendsto (fun s => σ' (s * z)) atTop (𝓝 1))
    (hneg : ∀ z, z < 0 → Tendsto (fun s => σ' (s * z)) atTop (𝓝 0))
    (c a : ι → d → ℝ) (A : Finset ι) (ξ : d → ℝ)
    (hA : ∀ j ∈ A, 0 < ξ ⬝ᵥ c j) (hA' : ∀ j ∉ A, ξ ⬝ᵥ c j < 0)
    (h0 : Function.Injective (∑ j ∈ A, dotSmul (c j) (a j) : (d → ℝ) →L[ℝ] (d → ℝ))) :
    ∃ x : d → ℝ, Function.Injective
      (∑ j, σ' (x ⬝ᵥ c j) • dotSmul (c j) (a j) : (d → ℝ) →L[ℝ] (d → ℝ)) := by
  classical
  have hα : ∀ j, Tendsto (fun s => σ' (s * (ξ ⬝ᵥ c j))) atTop
      (𝓝 (if j ∈ A then 1 else 0)) := by
    intro j
    by_cases hj : j ∈ A
    · simpa [hj] using hpos _ (hA j hj)
    · simpa [hj] using hneg _ (hA' j hj)
  have hΛ := tendsto_finsetSum (Finset.univ : Finset ι) fun j _ =>
    (hα j).smul_const (dotSmul (c j) (a j))
  have hlim : (∑ j, (if j ∈ A then (1 : ℝ) else 0) • dotSmul (c j) (a j)) =
      ∑ j ∈ A, dotSmul (c j) (a j) := by
    have h := Finset.sum_ite_mem Finset.univ A fun j => dotSmul (c j) (a j)
    rw [Finset.univ_inter] at h
    rw [← h]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> simp
  rw [hlim] at hΛ
  obtain ⟨s, hsinj⟩ := (eventually_injective_of_tendsto hΛ h0).exists
  refine ⟨s • ξ, ?_⟩
  simpa only [smul_dotProduct, smul_eq_mul] using hsinj


/-- `f(s z) → a` as `s → ∞`, for `z > 0`, if `f → a` at `+∞`. -/
private theorem tendsto_comp_mul_pos {f : ℝ → ℝ} {a : ℝ} (hf : Tendsto f atTop (𝓝 a)) {z : ℝ}
    (hz : 0 < z) : Tendsto (fun s => f (s * z)) atTop (𝓝 a) :=
  hf.comp (tendsto_id.atTop_mul_const hz)

/-- `f(s z) → a` as `s → ∞`, for `z < 0`, if `f → a` at `-∞`. -/
private theorem tendsto_comp_mul_neg {f : ℝ → ℝ} {a : ℝ} (hf : Tendsto f atBot (𝓝 a)) {z : ℝ}
    (hz : z < 0) : Tendsto (fun s => f (s * z)) atTop (𝓝 a) :=
  hf.comp (tendsto_id.atTop_mul_const_of_neg hz)

/-- For `σ(y) = y S(y)`: `σ(s z)/s = z S(s z)`, so it tends to `z b` if `S(s z) → b`. -/
private theorem tendsto_div_of_eq_mul {S : ℝ → ℝ} (hS : ∀ y, σ y = y * S y) {z b : ℝ}
    (h : Tendsto (fun s => S (s * z)) atTop (𝓝 b)) :
    Tendsto (fun s => σ (s * z) / s) atTop (𝓝 (z * b)) := by
  refine (h.const_mul z).congr' ?_
  filter_upwards [eventually_ne_atTop 0] with s hs
  rw [hS]
  field_simp

/-- "A good `θ` is regular", for gated blocks whose gate `σ(y) = y S(y)` has `σ' → 1`, `S → 1` at
`+∞` and `σ' → 0`, `S → 0` at `-∞`. For block `ℓ`: a row `ξ` of the cone `C_{ℓ-1}` at which the
frozen block has an injective derivative, then the row `x = s ξ` for a large `s`, then the matrix
all of whose rows are `x`. -/
private theorem regular_of_goodForConesGated_of_limits [Nonempty T] {σ' S : ℝ → ℝ}
    (hσ : ∀ y, HasDerivAt σ (σ' y) y) (hσ'1 : Tendsto σ' atTop (𝓝 1))
    (hσ'0 : Tendsto σ' atBot (𝓝 0)) (hS : ∀ y, σ y = y * S y) (hS1 : Tendsto S atTop (𝓝 1))
    (hS0 : Tendsto S atBot (𝓝 0)) {C : Fin (L + 1) → Set (d → ℝ)} {A : ∀ ℓ, Finset (hid ℓ)}
    {θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut}
    (hθ : GoodForConesGated C A θ) : Regular (Arch.gated σ χ hid) θ := by
  refine ⟨hθ.rank_E, hθ.rank_D, hθ.rank_write, fun ℓ => ?_⟩
  -- a row `ξ` of the cone read by block `ℓ` at which the frozen block has an injective derivative
  obtain ⟨ξ, hξC, hξ⟩ := exists_mem_injective_fderiv (analyticOnNhd_frozenGated θ ℓ (A ℓ))
    (hθ.cone ℓ.castSucc).isOpen (hθ.cone ℓ.castSucc).nonempty (hθ.frozen_deriv ℓ)
  rw [(hasFDerivAt_frozenGated θ ℓ (A ℓ) ξ).fderiv] at hξ
  -- the derivative of the row map at `s ξ` is injective for a large `s`
  obtain ⟨x, hx⟩ := exists_injective_gatedRow (σ := σ) (σ' := σ')
    (fun z hz => ⟨tendsto_comp_mul_pos hσ'1 hz,
      by simpa using tendsto_div_of_eq_mul hS (tendsto_comp_mul_pos hS1 hz)⟩)
    (fun z hz => ⟨tendsto_comp_mul_neg hσ'0 hz,
      by simpa using tendsto_div_of_eq_mul hS (tendsto_comp_mul_neg hS0 hz)⟩)
    (fun j => (θ.read ℓ)ᵀ (Sum.inl j)) (fun j => (θ.read ℓ)ᵀ (Sum.inr j)) (θ.write ℓ) (A ℓ) ξ
    (fun j hj => hθ.gate_pos ℓ ξ hξC j hj) (fun j hj => hθ.gate_neg ℓ ξ hξC j hj) hξ
  -- the block acts row by row: at the matrix all of whose rows are `x` its derivative is injective
  refine ⟨fun _ => x, ?_⟩
  rw [block_gated_eq]
  exact injective_fderiv_rowwise (HasFDerivAt.fun_sum fun j _ =>
    hasFDerivAt_gatedUnit hσ ((θ.read ℓ)ᵀ (Sum.inl j)) ((θ.read ℓ)ᵀ (Sum.inr j)) (θ.write ℓ j) x) hx

/-- "A good `θ` is regular", for MLP blocks whose activation has `σ' → 1` at `+∞` and `σ' → 0` at
`-∞`. -/
private theorem regular_of_goodForConesMlp_of_limits [Nonempty T] {σ' : ℝ → ℝ}
    (hσ : ∀ y, HasDerivAt σ (σ' y) y) (hσ'1 : Tendsto σ' atTop (𝓝 1))
    (hσ'0 : Tendsto σ' atBot (𝓝 0)) {C : Fin (L + 1) → Set (d → ℝ)} {A : ∀ ℓ, Finset (hid ℓ)}
    {θ : Params (Arch.mlp (T := T) (d := d) σ χ hid) dIn dOut}
    (hθ : GoodForConesMlp C A θ) : Regular (Arch.mlp σ χ hid) θ := by
  refine ⟨hθ.rank_E, hθ.rank_D, hθ.rank_write, fun ℓ => ?_⟩
  -- a row `ξ` of the cone read by block `ℓ` at which the frozen block has an injective derivative
  obtain ⟨ξ, hξC, hξ⟩ := exists_mem_injective_fderiv (analyticOnNhd_frozenMlp θ ℓ (A ℓ))
    (hθ.cone ℓ.castSucc).isOpen (hθ.cone ℓ.castSucc).nonempty (hθ.frozen_deriv ℓ)
  rw [(hasFDerivAt_frozenMlp θ ℓ (A ℓ) ξ).fderiv] at hξ
  -- the derivative of the row map at `s ξ` is injective for a large `s`
  obtain ⟨x, hx⟩ := exists_injective_mlpRow (σ' := σ') (fun z hz => tendsto_comp_mul_pos hσ'1 hz)
    (fun z hz => tendsto_comp_mul_neg hσ'0 hz) (fun j => (θ.read ℓ)ᵀ j) (θ.write ℓ) (A ℓ) ξ
    (fun j hj => hθ.gate_pos ℓ ξ hξC j hj) (fun j hj => hθ.gate_neg ℓ ξ hξC j hj) hξ
  -- the block acts row by row: at the matrix all of whose rows are `x` its derivative is injective
  refine ⟨fun _ => x, ?_⟩
  rw [block_mlp_eq]
  exact injective_fderiv_rowwise (HasFDerivAt.fun_sum fun j _ =>
    hasFDerivAt_mlpUnit hσ ((θ.read ℓ)ᵀ j) (θ.write ℓ j) x) hx

/-- `σ'(-y) = 1 - σ'(y)` for SiLU. -/
private theorem siluDeriv_neg' (y : ℝ) : siluDeriv (-y) = 1 - siluDeriv y := by
  have hx := Real.exp_pos y
  simp only [siluDeriv, neg_neg, Real.exp_neg]
  field_simp
  ring

/-- `σ'(y) → 1` at `+∞` for SiLU: `σ'(y) = (1 + e^{-y} + y e^{-y}) / (1 + e^{-y})²`. -/
private theorem tendsto_siluDeriv_atTop : Tendsto siluDeriv atTop (𝓝 1) := by
  have h1 := Real.tendsto_exp_neg_atTop_nhds_zero
  have h2 : Tendsto (fun y : ℝ => y * Real.exp (-y)) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
  have h3 : Tendsto (fun y : ℝ => 1 + Real.exp (-y)) atTop (𝓝 (1 + 0)) :=
    tendsto_const_nhds.add h1
  have h : Tendsto siluDeriv atTop (𝓝 ((1 + 0 + 0) / (1 + 0) ^ 2)) :=
    (h3.add h2).div (h3.pow 2) (by norm_num)
  simpa using h

/-- `σ'(y) → 0` at `-∞` for SiLU, since `σ'(y) = 1 - σ'(-y)`. -/
private theorem tendsto_siluDeriv_atBot : Tendsto siluDeriv atBot (𝓝 0) := by
  have h := (tendsto_siluDeriv_atTop.comp tendsto_neg_atBot_atTop).const_sub 1
  rw [sub_self] at h
  refine h.congr fun y => ?_
  rw [Function.comp_apply, siluDeriv_neg']
  ring

/-- SiLU is `y S(y)` with the logistic function `S(y) = 1/(1 + e^{-y})`. -/
private theorem silu_eq_mul (y : ℝ) : silu y = y * (1 + Real.exp (-y))⁻¹ := div_eq_mul_inv _ _

private theorem tendsto_logistic_atTop :
    Tendsto (fun y : ℝ => (1 + Real.exp (-y))⁻¹) atTop (𝓝 1) := by
  have h := ((tendsto_const_nhds (x := (1 : ℝ))).add Real.tendsto_exp_neg_atTop_nhds_zero).inv₀
    (by norm_num)
  simpa using h

private theorem tendsto_logistic_atBot :
    Tendsto (fun y : ℝ => (1 + Real.exp (-y))⁻¹) atBot (𝓝 0) := by
  have h : Tendsto (fun y : ℝ => Real.exp (-y)) atBot atTop :=
    Real.tendsto_exp_atTop.comp tendsto_neg_atBot_atTop
  exact (tendsto_atTop_add_const_left _ 1 h).inv_tendsto_atTop

/-- `y φ(y) → 0` at `+∞`: `y φ(y) = (y²/2) e^{-y²/2} · 2/(y √(2π))`. -/
private theorem tendsto_mul_gaussPdf_atTop : Tendsto (fun y => y * gaussPdf y) atTop (𝓝 0) := by
  have h1 : Tendsto (fun y : ℝ => (y ^ 2 / 2) ^ 1 * Real.exp (-(y ^ 2 / 2))) atTop (𝓝 0) :=
    (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
      ((tendsto_pow_atTop two_ne_zero).atTop_div_const two_pos)
  have hs : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  have h2 : Tendsto (fun y : ℝ => 2 / (y * Real.sqrt (2 * Real.pi))) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_id.atTop_mul_const hs)
  have h3 := h1.mul h2
  rw [zero_mul] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with y hy
  rw [gaussPdf, pow_one, show -(y ^ 2 / 2) = -y ^ 2 / 2 by ring]
  field_simp

/-- `y φ(y) → 0` at `-∞`, since `y φ(y)` is odd. -/
private theorem tendsto_mul_gaussPdf_atBot : Tendsto (fun y => y * gaussPdf y) atBot (𝓝 0) := by
  have h := (tendsto_mul_gaussPdf_atTop.comp tendsto_neg_atBot_atTop).neg
  rw [neg_zero] at h
  refine h.congr fun y => ?_
  rw [Function.comp_apply, gaussPdf_neg]
  ring

private theorem tendsto_geluDeriv_atTop :
    Tendsto (fun y => gaussCdf y + y * gaussPdf y) atTop (𝓝 1) := by
  simpa using tendsto_gaussCdf_atTop.add tendsto_mul_gaussPdf_atTop

private theorem tendsto_geluDeriv_atBot :
    Tendsto (fun y => gaussCdf y + y * gaussPdf y) atBot (𝓝 0) := by
  simpa using tendsto_gaussCdf_atBot.add tendsto_mul_gaussPdf_atBot


/-- "A good `θ` is regular", SwiGLU blocks. -/
theorem regular_of_goodForConesGated_swiglu [Nonempty T] {C : Fin (L + 1) → Set (d → ℝ)}
    {A : ∀ ℓ, Finset (hid ℓ)} {θ : Params (Arch.gated (T := T) (d := d) silu χ hid) dIn dOut}
    (hθ : GoodForConesGated C A θ) : Regular (Arch.gated silu χ hid) θ :=
  -- SiLU: `σ(y) = y S(y)` with the logistic function `S`
  regular_of_goodForConesGated_of_limits hasDerivAt_silu tendsto_siluDeriv_atTop
    tendsto_siluDeriv_atBot silu_eq_mul tendsto_logistic_atTop tendsto_logistic_atBot hθ

/-- "A good `θ` is regular", GeGLU blocks. -/
theorem regular_of_goodForConesGated_geglu [Nonempty T] {C : Fin (L + 1) → Set (d → ℝ)}
    {A : ∀ ℓ, Finset (hid ℓ)} {θ : Params (Arch.gated (T := T) (d := d) gelu χ hid) dIn dOut}
    (hθ : GoodForConesGated C A θ) : Regular (Arch.gated gelu χ hid) θ :=
  -- GELU: `σ(y) = y Φ(y)`
  regular_of_goodForConesGated_of_limits hasDerivAt_gelu tendsto_geluDeriv_atTop
    tendsto_geluDeriv_atBot (fun _ => rfl) tendsto_gaussCdf_atTop tendsto_gaussCdf_atBot hθ

/-- "A good `θ` is regular", GELU blocks. -/
theorem regular_of_goodForConesMlp_gelu [Nonempty T] {C : Fin (L + 1) → Set (d → ℝ)}
    {A : ∀ ℓ, Finset (hid ℓ)} {θ : Params (Arch.mlp (T := T) (d := d) gelu χ hid) dIn dOut}
    (hθ : GoodForConesMlp C A θ) : Regular (Arch.mlp gelu χ hid) θ :=
  regular_of_goodForConesMlp_of_limits hasDerivAt_gelu tendsto_geluDeriv_atTop
    tendsto_geluDeriv_atBot hθ

end Regular

/-! ### Lemma D.13: good parameters exist -/

open Polynomial in
/-- Helper: `1` and distinct positive powers of a number `x` transcendental over `ℚ` are linearly
independent over `ℚ`: `a + ∑_j κ_j x^{k_j} = 0`, with distinct exponents `k_j ≥ 1`, forces `a = 0`
and every `κ_j = 0`. -/
private theorem eq_zero_of_transcendental_pow {ι : Type*} [Fintype ι] {x : ℝ}
    (hx : Transcendental ℚ x) {k : ι → ℕ} (hk : Function.Injective k) (hk0 : ∀ j, k j ≠ 0)
    (a : ℚ) (κ : ι → ℚ) (h : (a : ℝ) + ∑ j, (κ j : ℝ) * x ^ k j = 0) :
    a = 0 ∧ ∀ j, κ j = 0 := by
  classical
  -- the polynomial `p = a + ∑ κ_j X^{k_j}` has the root `x`, so it vanishes
  set p : ℚ[X] := C a + ∑ j, C (κ j) * X ^ k j with hp
  have hp0 : p = 0 := by
    refine (transcendental_iff.mp hx) p ?_
    simpa [hp, map_add, map_sum, aeval_C, aeval_X_pow] using h
  -- its coefficients are `a` (at `0`) and `κ_j` (at `k_j`)
  have hc : ∀ n, p.coeff n = (if n = 0 then a else 0) + ∑ j, if n = k j then κ j else 0 := by
    intro n
    simp only [hp, coeff_add, coeff_C, finsetSum_coeff, coeff_C_mul, coeff_X_pow, mul_ite,
      mul_one, mul_zero]
  refine ⟨?_, fun j => ?_⟩
  · have h0 := hc 0
    rw [hp0, coeff_zero] at h0
    have h0' : ∀ j, (0 = k j) ↔ False := fun j => ⟨fun h => hk0 j h.symm, False.elim⟩
    simpa [h0'] using h0.symm
  · have h1 := hc (k j)
    rw [hp0, coeff_zero] at h1
    simpa [hk0 j, hk.eq_iff] using h1.symm

/-- Helper: positive numbers `μ_j`, one for each `j` of a finite type, such that `1` and the `μ_j`
are linearly independent over `ℚ`, and so are `1` and the `μ_j²`: `μ_j = x^{e_j + 1}` with an
injection `e` into `ℕ` and `x = λ²`, where `λ = ∑_k 2^{-k!}` is Liouville's number, transcendental. -/
private theorem exists_pos_indep (ι : Type*) [Fintype ι] :
    ∃ μ : ι → ℝ, (∀ j, 0 < μ j) ∧
      (∀ (a : ℚ) (κ : ι → ℚ), (a : ℝ) + ∑ j, (κ j : ℝ) * μ j = 0 → a = 0 ∧ ∀ j, κ j = 0) ∧
      (∀ (a : ℚ) (κ : ι → ℚ), (a : ℝ) + ∑ j, (κ j : ℝ) * μ j ^ 2 = 0 → a = 0 ∧ ∀ j, κ j = 0) := by
  -- Liouville's number is transcendental over `ℤ`, hence over `ℚ`, and so is its square `x > 0`
  have : Algebra.IsAlgebraic ℤ ℚ := IsLocalization.isAlgebraic ℚ (nonZeroDivisors ℤ)
  have hl : Transcendental ℚ (liouvilleNumber 2) :=
    (transcendental_liouvilleNumber le_rfl).extendScalars ℚ
  obtain ⟨x, hx, hx0⟩ : ∃ x : ℝ, Transcendental ℚ x ∧ 0 < x :=
    ⟨_, hl.pow two_pos, lt_of_le_of_ne (sq_nonneg _) (pow_ne_zero 2 hl.ne_zero).symm⟩
  -- an injection `e` of `ι` into `ℕ`
  obtain ⟨e, he⟩ : ∃ e : ι → ℕ, Function.Injective e :=
    ⟨fun j => (Fintype.equivFin ι j : ℕ), Fin.val_injective.comp (Fintype.equivFin ι).injective⟩
  refine ⟨fun j => x ^ (e j + 1), fun j => pow_pos hx0 _, fun a κ h => ?_, fun a κ h => ?_⟩
  · -- the exponents `e_j + 1`
    exact eq_zero_of_transcendental_pow hx (k := fun j => e j + 1)
      (fun i j hij => he (Nat.succ_injective hij)) (fun j => Nat.succ_ne_zero _) a κ h
  · -- the exponents `2 (e_j + 1)`, since `(x^{e_j+1})² = x^{2(e_j+1)}`
    refine eq_zero_of_transcendental_pow hx (k := fun j => 2 * (e j + 1))
      (fun i j hij => he (Nat.succ_injective (Nat.eq_of_mul_eq_mul_left two_pos hij)))
      (fun j => Nat.mul_ne_zero two_ne_zero (Nat.succ_ne_zero _)) a κ ?_
    simpa only [pow_mul'] using h

/-- The positive orthant `{n | n_i > 0 for every i}`: every cone of the paper's `θ†`. -/
private def orthant : Set (d → ℝ) := Set.univ.pi fun _ => Set.Ioi 0

omit [Fintype d] [DecidableEq d] in
private theorem mem_orthant {n : d → ℝ} : n ∈ orthant (d := d) ↔ ∀ i, 0 < n i :=
  Set.mem_univ_pi

omit [DecidableEq d] in
/-- The positive orthant is an open convex cone without `0`. -/
private theorem isOpenConvexCone_orthant [Nonempty d] : IsOpenConvexCone (orthant (d := d)) where
  isOpen := isOpen_set_pi Set.finite_univ fun _ _ => isOpen_Ioi
  convex := convex_pi fun _ _ => convex_Ioi 0
  nonempty := ⟨1, mem_orthant.2 fun _ => one_pos⟩
  zero_notMem h := by
    obtain ⟨i⟩ := ‹Nonempty d›
    exact lt_irrefl _ (mem_orthant.1 h i)
  smul_mem n hn lam hlam := mem_orthant.2 fun i => mul_pos hlam (mem_orthant.1 hn i)

omit [DecidableEq d] in
/-- `∑_k n_k > 0` on the orthant. -/
private theorem sum_pos_of_mem_orthant [Nonempty d] {n : d → ℝ} (hn : n ∈ orthant (d := d)) :
    0 < ∑ k, n k :=
  Finset.sum_pos (fun i _ => mem_orthant.1 hn i) Finset.univ_nonempty

open Classical in
/-- The `0/1` matrix of an embedding `ι : d ↪ m`: the entry `(i, a)` is `1` if `a = ι i`. -/
private noncomputable def embMat {m : Type*} (ι : d ↪ m) : Matrix d m ℝ :=
  Matrix.of fun i a => if a = ι i then 1 else 0

/-- The `0/1` matrix of an embedding has rank `d`: its columns at the image are the identity. -/
private theorem rank_embMat {m : Type*} [Fintype m] (ι : d ↪ m) :
    (embMat ι).rank = Fintype.card d := by
  refine rank_eq_card_of_isUnit_det _ ι ?_
  have h : (embMat ι).submatrix id ι = 1 := by
    ext i i'
    simp [embMat, Matrix.one_apply, ι.injective.eq_iff, eq_comm]
  rw [h, det_one]
  exact isUnit_one

open Classical in
/-- The row `k ↦ [j = c k]`: the unit row `e_i` for the unit `j = c i`. -/
private noncomputable def unitRow {n : Type*} (c : d ↪ n) (j : n) : d → ℝ :=
  fun k => if j = c k then 1 else 0

omit [Fintype d] in
private theorem unitRow_emb {n : Type*} (c : d ↪ n) (i : d) : unitRow c (c i) = Pi.single i 1 := by
  funext k
  by_cases h : k = i
  · subst h
    simp [unitRow]
  · simp [unitRow, c.injective.eq_iff, h, Ne.symm h]

open Classical in
/-- The gate column of unit `j` in `θ†`: `e_i` for `j = c i`, and `-μ_j 𝟙` for the other units. -/
private noncomputable def gateCol {n : Type*} (c : d ↪ n) (μ : n → ℝ) (j : n) : d → ℝ :=
  if j ∈ Set.range c then unitRow c j else -μ j • 1

open Classical in
/-- The write row of unit `j` in `θ†`: `e_i` for `j = c i`, and `𝟙` for the other units. -/
private noncomputable def writeRow {n : Type*} (c : d ↪ n) (j : n) : d → ℝ :=
  if j ∈ Set.range c then unitRow c j else 1

private theorem gateCol_emb {n : Type*} (c : d ↪ n) (μ : n → ℝ) (i : d) :
    gateCol c μ (c i) = Pi.single i 1 := by
  simp [gateCol, unitRow_emb]

omit [DecidableEq d] in
private theorem gateCol_of_notMem {n : Type*} (c : d ↪ n) (μ : n → ℝ) {j : n}
    (hj : j ∉ Set.range c) : gateCol c μ j = -μ j • 1 := by
  simp [gateCol, hj]

private theorem writeRow_emb {n : Type*} (c : d ↪ n) (i : d) : writeRow c (c i) = Pi.single i 1 := by
  simp [writeRow, unitRow_emb]

omit [DecidableEq d] in
private theorem writeRow_of_notMem {n : Type*} (c : d ↪ n) {j : n} (hj : j ∉ Set.range c) :
    writeRow c j = 1 := by
  simp [writeRow, hj]

/-- The write rows of `θ†` have rank `d`: the rows at the image of `c` are the identity. -/
private theorem rank_writeRow {n : Type*} [Fintype n] (c : d ↪ n) :
    (Matrix.of (writeRow c)).rank = Fintype.card d := by
  rw [← Matrix.rank_transpose]
  refine rank_eq_card_of_isUnit_det _ c ?_
  have h : (Matrix.of (writeRow c))ᵀ.submatrix id c = 1 := by
    ext i i'
    change writeRow c (c i') i = (1 : Matrix d d ℝ) i i'
    rw [writeRow_emb, Pi.single_apply, Matrix.one_apply]
  rw [h, det_one]
  exact isUnit_one

/-- No write row of `θ†` vanishes. -/
private theorem writeRow_ne_zero [Nonempty d] {n : Type*} (c : d ↪ n) (j : n) :
    writeRow c j ≠ 0 := by
  by_cases hj : j ∈ Set.range c
  · obtain ⟨i, rfl⟩ := hj
    rw [writeRow_emb]
    exact fun h => by simpa using congrFun h i
  · rw [writeRow_of_notMem c hj]
    exact one_ne_zero

/-- On the orthant the gate `n ⬝ e_i = n_i` of a unit `c i` is positive. -/
private theorem gateCol_pos {n : Type*} (c : d ↪ n) (μ : n → ℝ) {j : n}
    (hj : j ∈ Finset.univ.map c) {x : d → ℝ} (hx : x ∈ orthant (d := d)) :
    0 < x ⬝ᵥ gateCol c μ j := by
  obtain ⟨i, _, rfl⟩ := Finset.mem_map.1 hj
  rw [gateCol_emb, dotProduct_single, mul_one]
  exact mem_orthant.1 hx i

omit [DecidableEq d] in
/-- On the orthant the gate `-μ_j ∑ n` of any other unit is negative. -/
private theorem gateCol_neg [Nonempty d] {n : Type*} (c : d ↪ n) {μ : n → ℝ} (hμ : ∀ j, 0 < μ j)
    {j : n} (hj : j ∉ Finset.univ.map c) {x : d → ℝ} (hx : x ∈ orthant (d := d)) :
    x ⬝ᵥ gateCol c μ j < 0 := by
  have hj' : j ∉ Set.range c := fun ⟨i, hi⟩ => hj (Finset.mem_map.2 ⟨i, Finset.mem_univ i, hi⟩)
  rw [gateCol_of_notMem c μ hj', dotProduct_smul, dotProduct_one, smul_eq_mul]
  exact mul_neg_of_neg_of_pos (neg_neg_of_pos (hμ j)) (sum_pos_of_mem_orthant hx)

/-- Helper: the gate columns of `θ†` are linearly independent over `ℚ` when `1` and the `μ_j`
are. Coordinate `k` of a relation `∑ g_j c_j = 0` reads `g_{c k} - ∑_{j ∉ range c} g_j μ_j = 0`. -/
private theorem linearIndependent_gateCol [Nonempty d] {n : Type*} [Fintype n] (c : d ↪ n)
    (μ : n → ℝ)
    (hμ : ∀ (a : ℚ) (κ : n → ℚ), (a : ℝ) + ∑ j, (κ j : ℝ) * μ j = 0 → a = 0 ∧ ∀ j, κ j = 0) :
    LinearIndependent ℚ (gateCol c μ) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hk : ∀ k, ((g (c k) : ℚ) : ℝ) +
      ∑ j, ((if j ∈ Set.range c then 0 else -g j : ℚ) : ℝ) * μ j = 0 := by
    intro k
    have h := congrFun hg k
    rw [Finset.sum_apply, Pi.zero_apply] at h
    rw [← h]
    -- termwise: `g_j (c_j)_k = g_j [j = c k] + (if j ∈ range c then 0 else -g_j) μ_j`
    have hterm : ∀ j, (g j • gateCol c μ j) k = (if c k = j then (g j : ℝ) else 0) +
        ((if j ∈ Set.range c then 0 else -g j : ℚ) : ℝ) * μ j := by
      intro j
      by_cases hj : j ∈ Set.range c
      · obtain ⟨i, rfl⟩ := hj
        simp [gateCol_emb, Rat.smul_def, Pi.single_apply, c.injective.eq_iff, eq_comm]
      · have hne : c k ≠ j := fun h => hj ⟨k, h⟩
        simp [gateCol_of_notMem c μ hj, hj, hne, Rat.smul_def]
    rw [Finset.sum_congr rfl fun j _ => hterm j, Finset.sum_add_distrib, Finset.sum_ite_eq]
    simp
  obtain ⟨k₀⟩ := ‹Nonempty d›
  intro j
  by_cases hj : j ∈ Set.range c
  · obtain ⟨k, rfl⟩ := hj
    exact (hμ _ _ (hk k)).1
  · simpa [hj] using (hμ _ _ (hk k₀)).2 j

/-- Helper: the matrices `c_j c_jᵀ` of the gate columns of `θ†` are linearly independent over `ℚ`
when `1` and the `μ_j²` are. The diagonal entry `(k, k)` of a relation reads
`g_{c k} + ∑_{j ∉ range c} g_j μ_j² = 0`. -/
private theorem linearIndependent_outer_gateCol [Nonempty d] {n : Type*} [Fintype n] (c : d ↪ n)
    (μ : n → ℝ)
    (hμ : ∀ (a : ℚ) (κ : n → ℚ), (a : ℝ) + ∑ j, (κ j : ℝ) * μ j ^ 2 = 0 → a = 0 ∧ ∀ j, κ j = 0) :
    LinearIndependent ℚ (fun j => vecMulVec (gateCol c μ j) (gateCol c μ j)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hk : ∀ k, ((g (c k) : ℚ) : ℝ) +
      ∑ j, ((if j ∈ Set.range c then 0 else g j : ℚ) : ℝ) * μ j ^ 2 = 0 := by
    intro k
    have h := congrFun (congrFun hg k) k
    rw [Matrix.sum_apply, Matrix.zero_apply] at h
    rw [← h]
    -- termwise: `g_j (c_j)_k² = g_j [j = c k] + (if j ∈ range c then 0 else g_j) μ_j²`
    have hterm : ∀ j, (g j • vecMulVec (gateCol c μ j) (gateCol c μ j)) k k =
        (if c k = j then (g j : ℝ) else 0) +
          ((if j ∈ Set.range c then 0 else g j : ℚ) : ℝ) * μ j ^ 2 := by
      intro j
      by_cases hj : j ∈ Set.range c
      · obtain ⟨i, rfl⟩ := hj
        by_cases hik : k = i
        · subst hik
          simp [gateCol_emb, Rat.smul_def, vecMulVec_apply]
        · simp [gateCol_emb, vecMulVec_apply, c.injective.eq_iff, hik]
      · have hne : c k ≠ j := fun h => hj ⟨k, h⟩
        rw [gateCol_of_notMem c μ hj]
        simp only [Matrix.smul_apply, vecMulVec_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul,
          Rat.smul_def, hj, hne, ↓reduceIte, zero_add]
        ring
    rw [Finset.sum_congr rfl fun j _ => hterm j, Finset.sum_add_distrib, Finset.sum_ite_eq]
    simp
  obtain ⟨k₀⟩ := ‹Nonempty d›
  intro j
  by_cases hj : j ∈ Set.range c
  · obtain ⟨k, rfl⟩ := hj
    exact (hμ _ _ (hk k)).1
  · simpa [hj] using (hμ _ _ (hk k₀)).2 j

omit [DecidableEq d] in
/-- Helper: `n ↦ (∑_k n_k) n` has an injective derivative at `𝟙`: it is
`v ↦ d v + (∑_k v_k) 𝟙`, and summing the coordinates of `d v + (∑ v) 𝟙 = 0` gives `2 d ∑ v = 0`. -/
private theorem injective_fderiv_sum_smul [Nonempty d] :
    Function.Injective (fderiv ℝ (fun n : d → ℝ => (∑ k, n k) • n) 1) := by
  have hs : HasFDerivAt (fun n : d → ℝ => ∑ k, n k)
      (∑ k, ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : d => ℝ) k) (1 : d → ℝ) :=
    HasFDerivAt.fun_sum fun k _ => hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : d => ℝ) k 1
  have h : HasFDerivAt (fun n : d → ℝ => (∑ k, n k) • n) _ (1 : d → ℝ) :=
    hs.smul (hasFDerivAt_id (1 : d → ℝ))
  rw [h.fderiv, injective_iff_map_eq_zero]
  intro v hv
  have hc : (0 : ℝ) < Fintype.card d := by exact_mod_cast Fintype.card_pos
  -- coordinate `i`: `d v_i + ∑_k v_k = 0`
  have hv' : ∀ i, (Fintype.card d : ℝ) * v i + ∑ k, v k = 0 := by
    intro i
    have := congrFun hv i
    simpa using this
  -- summing over `i`: `2 d ∑ v = 0`
  have hsum : ∑ k, v k = 0 := by
    have h2 := Finset.sum_eq_zero (s := Finset.univ) fun i _ => hv' i
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul] at h2
    have : (Fintype.card d : ℝ) * (2 * ∑ k, v k) = 0 := by linarith
    simpa [hc.ne'] using this
  funext i
  have := hv' i
  rw [hsum, add_zero] at this
  exact (mul_eq_zero.1 this).resolve_left hc.ne'

/-- The parameter `θ†` of Lemma D.13 for gated blocks, from embeddings `ιE : d ↪ d_in`,
`ιD : d ↪ d_out`, `c ℓ : d ↪ hid ℓ` and numbers `μ`: `E`, `D` are the `0/1` matrices of the
embeddings, the gate columns are `gateCol`, every value column is `𝟙`, the write rows `writeRow`. -/
private noncomputable def thetaGated (ιE : d ↪ dIn) (ιD : d ↪ dOut) (c : ∀ ℓ, d ↪ hid ℓ)
    (μ : ∀ ℓ, hid ℓ → ℝ) : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut where
  E := (embMat ιE)ᵀ
  read ℓ := Matrix.of fun k (s : hid ℓ ⊕ hid ℓ) =>
    Sum.elim (fun j => gateCol (c ℓ) (μ ℓ) j k) (fun _ => 1) s
  write ℓ := Matrix.of (writeRow (c ℓ))
  D := embMat ιD

omit [Fintype T] in
/-- `θ†` (gated) is good for the orthants, with the active sets `range c_ℓ`. -/
private theorem goodForConesGated_thetaGated [Nonempty d] (ιE : d ↪ dIn) (ιD : d ↪ dOut)
    (c : ∀ ℓ, d ↪ hid ℓ) {μ : ∀ ℓ, hid ℓ → ℝ} (hμ : ∀ ℓ j, 0 < μ ℓ j) :
    GoodForConesGated (fun _ => orthant) (fun ℓ => Finset.univ.map (c ℓ))
      (thetaGated (T := T) (σ := σ) (χ := χ) ιE ιD c μ) := by
  -- the frozen block is `n ↦ ∑_i n_i (∑_k n_k) e_i = (∑_k n_k) n`
  have hfrozen : ∀ ℓ, frozenGated (thetaGated (T := T) (σ := σ) (χ := χ) ιE ιD c μ) ℓ
      (Finset.univ.map (c ℓ)) = fun n => (∑ k, n k) • n := by
    intro ℓ
    funext n
    rw [frozenGated, Finset.sum_map]
    change ∑ i, ((n ⬝ᵥ gateCol (c ℓ) (μ ℓ) (c ℓ i)) * (n ⬝ᵥ 1)) • writeRow (c ℓ) (c ℓ i) = _
    simp only [gateCol_emb, writeRow_emb, dotProduct_single, dotProduct_one, mul_one]
    funext k
    simp [Finset.sum_apply, Pi.single_apply, mul_comm]
  refine ⟨fun _ => isOpenConvexCone_orthant, (Matrix.rank_transpose _).trans (rank_embMat ιE),
    rank_embMat ιD, fun ℓ => rank_writeRow (c ℓ), fun ℓ n hn j hj => gateCol_pos (c ℓ) (μ ℓ) hj hn,
    fun ℓ n hn j hj => gateCol_neg (c ℓ) (hμ ℓ) hj hn, fun ℓ n hn => ?_, fun ℓ => ⟨1, ?_⟩,
    fun ℓ j => writeRow_ne_zero (c ℓ) j, fun ℓ j => one_ne_zero⟩
  · -- (K2): `(∑ n) n` lies in the orthant
    rw [hfrozen]
    exact isOpenConvexCone_orthant.smul_mem n hn _ (sum_pos_of_mem_orthant hn)
  · -- (K2): the derivative at `𝟙` is injective
    rw [hfrozen]
    exact injective_fderiv_sum_smul

/-- The parameter `θ†` of Lemma D.13 for MLP blocks: as `thetaGated`, without value columns. -/
private noncomputable def thetaMlp (ιE : d ↪ dIn) (ιD : d ↪ dOut) (c : ∀ ℓ, d ↪ hid ℓ)
    (μ : ∀ ℓ, hid ℓ → ℝ) : Params (Arch.mlp (T := T) (d := d) σ χ hid) dIn dOut where
  E := (embMat ιE)ᵀ
  read ℓ := Matrix.of fun k j => gateCol (c ℓ) (μ ℓ) j k
  write ℓ := Matrix.of (writeRow (c ℓ))
  D := embMat ιD

omit [Fintype T] in
/-- `θ†` (MLP) is good for the orthants, with the active sets `range c_ℓ`. -/
private theorem goodForConesMlp_thetaMlp [Nonempty d] (ιE : d ↪ dIn) (ιD : d ↪ dOut)
    (c : ∀ ℓ, d ↪ hid ℓ) {μ : ∀ ℓ, hid ℓ → ℝ} (hμ : ∀ ℓ j, 0 < μ ℓ j) :
    GoodForConesMlp (fun _ => orthant) (fun ℓ => Finset.univ.map (c ℓ))
      (thetaMlp (T := T) (σ := σ) (χ := χ) ιE ιD c μ) := by
  -- the frozen block is `n ↦ ∑_i n_i e_i = n`
  have hfrozen : ∀ ℓ, frozenMlp (thetaMlp (T := T) (σ := σ) (χ := χ) ιE ιD c μ) ℓ
      (Finset.univ.map (c ℓ)) = id := by
    intro ℓ
    funext n
    rw [frozenMlp, Finset.sum_map]
    change ∑ i, (n ⬝ᵥ gateCol (c ℓ) (μ ℓ) (c ℓ i)) • writeRow (c ℓ) (c ℓ i) = n
    simp only [gateCol_emb, writeRow_emb, dotProduct_single, mul_one]
    funext k
    simp [Finset.sum_apply, Pi.single_apply]
  refine ⟨fun _ => isOpenConvexCone_orthant, (Matrix.rank_transpose _).trans (rank_embMat ιE),
    rank_embMat ιD, fun ℓ => rank_writeRow (c ℓ), fun ℓ n hn j hj => gateCol_pos (c ℓ) (μ ℓ) hj hn,
    fun ℓ n hn j hj => gateCol_neg (c ℓ) (hμ ℓ) hj hn, fun ℓ n hn => ?_, fun ℓ => ⟨1, ?_⟩,
    fun ℓ j => writeRow_ne_zero (c ℓ) j⟩
  · rw [hfrozen]
    exact hn
  · rw [hfrozen, fderiv_id]
    exact fun v w h => h

/-- **Lemma D.13, for SwiGLU blocks:** for `d_in, d_out ≥ d ≥ 1` and at least `d` hidden units in
every block there are cones, active sets and a parameter that is good for them and whose gate
columns are linearly independent over `ℚ` in every block. (The conditions do not involve the gate
or the normalization.) -/
theorem exists_goodForConesGated_cols [Nonempty d]
    (hdIn : Fintype.card d ≤ Fintype.card dIn) (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∃ (C : Fin (L + 1) → Set (d → ℝ)) (A : ∀ ℓ, Finset (hid ℓ))
      (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut),
      GoodForConesGated C A θ ∧
        ∀ ℓ, LinearIndependent ℚ (fun j : hid ℓ => (θ.read ℓ)ᵀ (Sum.inl j)) := by
  -- embeddings `d ↪ d_in`, `d ↪ d_out`, `d ↪ hid ℓ`, and the numbers `μ` (Liouville powers)
  obtain ⟨ιE⟩ := Function.Embedding.nonempty_of_card_le hdIn
  obtain ⟨ιD⟩ := Function.Embedding.nonempty_of_card_le hdOut
  have c : ∀ ℓ, d ↪ hid ℓ := fun ℓ =>
    Classical.choice (Function.Embedding.nonempty_of_card_le (hhid ℓ))
  choose μ hμpos hμ1 _ using fun ℓ => exists_pos_indep (hid ℓ)
  -- `θ†` with the orthant as every cone; its gate columns are `e_i` and `-μ_j 𝟙`
  exact ⟨fun _ => orthant, fun ℓ => Finset.univ.map (c ℓ), thetaGated ιE ιD c μ,
    goodForConesGated_thetaGated ιE ιD c hμpos,
    fun ℓ => linearIndependent_gateCol (c ℓ) (μ ℓ) (hμ1 ℓ)⟩

/-- **Lemma D.13, for GeGLU blocks:** for `d_in, d_out ≥ d ≥ 2` and at least `d` hidden units in
every block there are cones, active sets and a parameter that is good for them and for which the
matrices `c_j c_j^⊤` of the gate columns are linearly independent over `ℚ` in every block. -/
theorem exists_goodForConesGated_outer (hd : 2 ≤ Fintype.card d)
    (hdIn : Fintype.card d ≤ Fintype.card dIn) (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∃ (C : Fin (L + 1) → Set (d → ℝ)) (A : ∀ ℓ, Finset (hid ℓ))
      (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut),
      GoodForConesGated C A θ ∧
        ∀ ℓ, LinearIndependent ℚ (fun j : hid ℓ =>
          Matrix.vecMulVec ((θ.read ℓ)ᵀ (Sum.inl j)) ((θ.read ℓ)ᵀ (Sum.inl j))) := by
  have : Nonempty d := Fintype.card_pos_iff.1 (by omega)
  -- embeddings `d ↪ d_in`, `d ↪ d_out`, `d ↪ hid ℓ`, and the numbers `μ` (Liouville powers)
  obtain ⟨ιE⟩ := Function.Embedding.nonempty_of_card_le hdIn
  obtain ⟨ιD⟩ := Function.Embedding.nonempty_of_card_le hdOut
  have c : ∀ ℓ, d ↪ hid ℓ := fun ℓ =>
    Classical.choice (Function.Embedding.nonempty_of_card_le (hhid ℓ))
  choose μ hμpos _ hμ2 using fun ℓ => exists_pos_indep (hid ℓ)
  -- `θ†` with the orthant as every cone; `c_j c_jᵀ` is a matrix unit or `μ_j²` times all ones
  exact ⟨fun _ => orthant, fun ℓ => Finset.univ.map (c ℓ), thetaGated ιE ιD c μ,
    goodForConesGated_thetaGated ιE ιD c hμpos,
    fun ℓ => linearIndependent_outer_gateCol (c ℓ) (μ ℓ) (hμ2 ℓ)⟩

/-- **Lemma D.13, for GELU blocks:** for `d_in, d_out ≥ d ≥ 2` and at least `d` hidden units in
every block there are cones, active sets and a parameter that is good for them and for which the
matrices `c_j c_j^⊤` of the read columns are linearly independent over `ℚ` in every block. -/
theorem exists_goodForConesMlp_outer (hd : 2 ≤ Fintype.card d)
    (hdIn : Fintype.card d ≤ Fintype.card dIn) (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∃ (C : Fin (L + 1) → Set (d → ℝ)) (A : ∀ ℓ, Finset (hid ℓ))
      (θ : Params (Arch.mlp (T := T) (d := d) σ χ hid) dIn dOut),
      GoodForConesMlp C A θ ∧
        ∀ ℓ, LinearIndependent ℚ (fun j : hid ℓ =>
          Matrix.vecMulVec ((θ.read ℓ)ᵀ j) ((θ.read ℓ)ᵀ j)) := by
  have : Nonempty d := Fintype.card_pos_iff.1 (by omega)
  -- embeddings `d ↪ d_in`, `d ↪ d_out`, `d ↪ hid ℓ`, and the numbers `μ` (Liouville powers)
  obtain ⟨ιE⟩ := Function.Embedding.nonempty_of_card_le hdIn
  obtain ⟨ιD⟩ := Function.Embedding.nonempty_of_card_le hdOut
  have c : ∀ ℓ, d ↪ hid ℓ := fun ℓ =>
    Classical.choice (Function.Embedding.nonempty_of_card_le (hhid ℓ))
  choose μ hμpos _ hμ2 using fun ℓ => exists_pos_indep (hid ℓ)
  -- `θ†` with the orthant as every cone; `c_j c_jᵀ` is a matrix unit or `μ_j²` times all ones
  exact ⟨fun _ => orthant, fun ℓ => Finset.univ.map (c ℓ), thetaMlp ιE ιD c μ,
    goodForConesMlp_thetaMlp ιE ιD c hμpos,
    fun ℓ => linearIndependent_outer_gateCol (c ℓ) (μ ℓ) (hμ2 ℓ)⟩

end Skips
