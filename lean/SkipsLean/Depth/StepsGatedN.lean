import SkipsLean.Depth.Frozen
import SkipsLean.Depth.SuffixFlatConverse

/-!
# Lemma D.12, steps 1 to 3, for gated blocks without normalization

Paper (dimension): Appendix D.5, proof of Lemma D.12, from equation (38) to the end, in the case
(n). After the induction on the exponents, "for all `n ∈ C_k` and all rows `w̃ ∈ ℝ^{1×q}`, with
`ŵ = w̃ ⊙ ι(n)`,

  `ż^g(n) = 0`,   `𝐃𝓑^∞(ŵ V) ((w̃ ⊙ ż^v(n)) V + ŵ η_V) + 𝐃_θ 𝓑^∞(ŵ V) η' = 0`   (38)",

where `𝓑^∞` is the frozen network in the case (n). "Step 1: the gates" gives `η_g = −Z W_g`;
"Step 2: the values and the write" gives a diagonal matrix `Δ_{k+1}` and a matrix `Z'` with
`η_V = Δ_{k+1} V + V Z'` and `η_v = −Z W_v − W_v Δ_{k+1}` (Lemmas D.3 and D.2 for the frozen
network); "Step 3: the rest", in the case (n), subtracts the direction `η♭` of the form (19) built
from `Z`, `Δ_{k+1}`, `Z'`, which satisfies (16) by the converse of the claim, and applies
`(D_{k+1})` to what is left, after extending an identity from the values of `g_{k+1}` to all rows
by (R3).

Stated here: the conclusion of `(D_k)` for one pair `Z`, `η` that satisfies (16) for `k`, from
(38). In Lean, (38) is the two hypotheses `hgate` (its first part holds on an open set of `n` and
is linear in `n`, so it says `Z W_g + η_g = 0`) and `hfro`; the second part is written with
`writeLHS` for the frozen network at `v = w̃ ⊙ ι(n)`, `vdot = w̃ ⊙ ż^v(n)`. The gate `σ` is any
real-analytic function: these steps do not look at it.
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise Topology

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]
variable {σ σ' : ℝ → ℝ}

/-- Helper: at a regular parameter, the identity (16) determines `Z`: if it holds for `Z₁` and for
`Z₂` with the same `η`, then `h Z₁` and `h Z₂` have the same image under `𝐃𝓑_{>k}(h)`, which is
injective on a dense set of `h` (Lemma D.2), so `h Z₁ = h Z₂` for all `h`. -/
private theorem eq_of_suffixFlat_of_suffixFlat [Nonempty T] (Ar : Arch T d L)
    (θ : Params Ar dIn dOut) (hχ : Ar.χ = id) (hf : ∀ ℓ, AnalyticOnNhd ℝ (Ar.f ℓ) Set.univ)
    (hθ : Regular Ar θ) (k : Fin (L + 1)) {Z₁ Z₂ : Matrix d d ℝ} {η : Params Ar dIn dOut}
    (h₁ : SuffixFlat Ar θ k Z₁ η) (h₂ : SuffixFlat Ar θ k Z₂ η) : Z₁ = Z₂ := by
  classical
  -- Lemma D.2: `𝐃𝓑_{>k}(h)` is injective for `h` in a dense set `U`
  obtain ⟨U, -, hUd, hU⟩ := exists_open_dense_injective_fderiv_suffix Ar θ hχ hf hθ k
  have hU' : Set.EqOn (fun h : Matrix T d ℝ => h * Z₁) (fun h => h * Z₂) U :=
    fun h hh => hU h hh (add_right_cancel ((h₁ h).trans (h₂ h).symm))
  -- so `h Z₁ = h Z₂` for every `h`, by continuity
  have hall : (fun h : Matrix T d ℝ => h * Z₁) = fun h => h * Z₂ :=
    Continuous.ext_on hUd (continuous_id.matrix_mul continuous_const)
      (continuous_id.matrix_mul continuous_const) hU'
  -- with `h` whose row `t₀` is the basis vector `i`, row `t₀` of `h Z` is row `i` of `Z`
  obtain ⟨t₀⟩ := ‹Nonempty T›
  ext i j
  have e := congrFun (congrFun (congrFun hall (Matrix.single t₀ i (1 : ℝ))) t₀) j
  simpa only [Matrix.single_mul_apply_same, one_mul] using e

omit [Fintype T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: for `c ≠ 0`, the rows `ν` with `ν ⬝ c ≠ 0` are dense (from a zero `x`, the rows
`x + ε c` with `ε ≠ 0` tend to `x`). -/
private theorem dense_setOf_dotProduct_ne_zero {c : d → ℝ} (hc : c ≠ 0) :
    Dense {ν : d → ℝ | ν ⬝ᵥ c ≠ 0} := by
  intro x
  by_cases hx : x ⬝ᵥ c ≠ 0
  · exact subset_closure hx
  rw [not_not] at hx
  have ht : Filter.Tendsto (fun ε : ℝ => x + ε • c) (𝓝[≠] 0) (𝓝 x) := by
    have hcont : Continuous (fun ε : ℝ => x + ε • c) :=
      continuous_const.add (continuous_id.smul continuous_const)
    have h0 := hcont.tendsto 0
    rw [zero_smul, add_zero] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  refine mem_closure_of_tendsto ht (eventually_nhdsWithin_of_forall fun ε hε => ?_)
  show (x + ε • c) ⬝ᵥ c ≠ 0
  rw [add_dotProduct, smul_dotProduct, hx, zero_add, smul_eq_mul]
  exact mul_ne_zero hε (fun h => hc (dotProduct_self_eq_zero.1 h))

omit [Fintype T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: a vector `c` with `ν ⬝ c = 0` for every row `ν` of an open nonempty set is `0` (move
`ν₀` of the set along the basis vector `i` by a small `ε ≠ 0`). -/
private theorem eq_zero_of_dotProduct_eq_zero {S : Set (d → ℝ)} (hS : IsOpen S)
    (hne : S.Nonempty) {c : d → ℝ} (h : ∀ ν ∈ S, ν ⬝ᵥ c = 0) : c = 0 := by
  classical
  obtain ⟨ν₀, hν₀⟩ := hne
  funext i
  have hcont : Continuous fun ε : ℝ => ν₀ + ε • Pi.single i (1 : ℝ) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hev : ∀ᶠ ε in 𝓝 (0 : ℝ), ν₀ + ε • Pi.single i (1 : ℝ) ∈ S := by
    refine hcont.continuousAt.preimage_mem_nhds ?_
    simpa using hS.mem_nhds hν₀
  obtain ⟨ε, hεS, hε⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and
    (eventually_mem_nhdsWithin (a := (0 : ℝ)) (s := {0}ᶜ))).exists
  have e := h _ hεS
  rw [add_dotProduct, smul_dotProduct, h ν₀ hν₀, zero_add, single_dotProduct, one_mul,
    smul_eq_mul] at e
  exact (mul_eq_zero.1 e).resolve_left hε

/-- Helper, **step 2 of the proof of Lemma D.12, case (n): the values and the write.** From (38)
for the frozen network: there are numbers `β_j` (the diagonal of `Δ̃`) and a matrix `Z'` with
`P e_j = β_j e_j` for the value columns of `P = Z W + η_W` and `Δ̃ V + η_V = V Z'`. -/
private theorem exists_values_of_frozen [Nonempty T] {C : Fin (L + 1) → Set (d → ℝ)}
    {A : ∀ ℓ, Finset (hid ℓ)} {θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut}
    (hθ : GoodForConesGated C A θ) (k : Fin L) (Z : Matrix d d ℝ)
    (η : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (hfro : ∀ n : Matrix T d ℝ, (∀ t, n t ∈ C k.castSucc) → ∀ w : Matrix T (hid k) ℝ,
      writeLHS (Arch.frozen A) (θ.toFrozen A) k (η.toFrozen A)
        (Matrix.of fun t j => w t j * (n * θ.read k) t (Sum.inr j))
        (Matrix.of fun t j => w t j * (n * (Z * θ.read k + η.read k)) t (Sum.inr j)) = 0) :
    ∃ (β : hid k → ℝ) (Z' : Matrix d d ℝ),
      (∀ j, (Z * θ.read k + η.read k)ᵀ (Sum.inr j) = β j • (θ.read k)ᵀ (Sum.inr j)) ∧
      ∀ i c, β i * θ.write k i c + η.write k i c = (θ.write k * Z') i c := by
  classical
  -- the frozen network is regular and its blocks are analytic: Lemmas D.2 and D.3 hold for it
  have hreg := regular_frozen_of_goodForConesGated hθ
  have hf := analyticOnNhd_f_frozen (T := T) (d := d) A
  -- `e ν j = ν e_j` and `p ν j = ν p_j`, with the value columns `e_j` of `W`, `p_j` of `P`
  let e : (d → ℝ) → hid k → ℝ := fun ν j => ν ⬝ᵥ (θ.read k)ᵀ (Sum.inr j)
  let p : (d → ℝ) → hid k → ℝ := fun ν j => ν ⬝ᵥ (Z * θ.read k + η.read k)ᵀ (Sum.inr j)
  -- the open set `S` of rows `ν ∈ C_k` with `ν e_j ≠ 0` for every `j`
  let S : Set (d → ℝ) := C k.castSucc ∩ ⋂ j, {ν | e ν j ≠ 0}
  have hopen : ∀ j, IsOpen {ν : d → ℝ | e ν j ≠ 0} := fun j =>
    isOpen_ne_fun (continuous_id.dotProduct continuous_const) continuous_const
  have hSo : IsOpen S := (hθ.cone _).isOpen.inter (isOpen_iInter_of_finite hopen)
  -- it is not empty: no `e_j` vanishes (K3), so the `ν` with `ν e_j ≠ 0` for all `j` are dense
  have hSne : S.Nonempty := by
    have hD : Dense (⋂ j, {ν : d → ℝ | e ν j ≠ 0}) :=
      dense_iInter_of_isOpen hopen fun j => dense_setOf_dotProduct_ne_zero (hθ.value_ne_zero k j)
    exact hD.inter_open_nonempty _ (hθ.cone _).isOpen (hθ.cone _).nonempty
  -- a matrix `n` with every row `ν`
  have hrow : ∀ (ν : d → ℝ) (M : Matrix d (hid k ⊕ hid k) ℝ) (t : T) (c : hid k ⊕ hid k),
      (Matrix.of (fun _ : T => ν) * M) t c = ν ⬝ᵥ Mᵀ c := fun _ _ _ _ => rfl
  -- for `ν ∈ S`, (38) at `n` with rows `ν` and `w̃ = v / (ν e)` is the hypothesis of Lemma D.3
  -- for the frozen network at the write `V`: `Δ̃(ν) V + η_V = V Z'(ν)` and (16) for `k + 1`
  have hZ' : ∀ ν ∈ S, ∃ Z' : Matrix d d ℝ,
      Matrix.diagonal (fun j => p ν j / e ν j) * θ.write k + η.write k = θ.write k * Z' ∧
      SuffixFlat (Arch.frozen A) (θ.toFrozen A) k.succ Z' (η.toFrozen A) := by
    intro ν hν
    have hne : ∀ j, e ν j ≠ 0 := Set.mem_iInter.1 hν.2
    refine suffixFlat_of_flat_at_write (Arch.frozen A) (θ.toFrozen A) rfl hf hreg k.succ
      (θ.write k) (hθ.rank_write k) _ (η.toFrozen A) fun v => ?_
    have h := hfro (Matrix.of fun _ => ν) (fun _ => hν.1) (Matrix.of fun t j => v t j / e ν j)
    have h1 : (Matrix.of fun t j => (Matrix.of fun t j => v t j / e ν j) t j
        * (Matrix.of (fun _ : T => ν) * θ.read k) t (Sum.inr j)) = v := by
      ext t j
      rw [Matrix.of_apply, Matrix.of_apply, hrow]
      exact div_mul_cancel₀ _ (hne j)
    have h2 : (Matrix.of fun t j => (Matrix.of fun t j => v t j / e ν j) t j
        * (Matrix.of (fun _ : T => ν) * (Z * θ.read k + η.read k)) t (Sum.inr j))
        = v * Matrix.diagonal (fun j => p ν j / e ν j) := by
      ext t j
      rw [Matrix.mul_diagonal, Matrix.of_apply, Matrix.of_apply, hrow]
      show v t j / e ν j * p ν j = v t j * (p ν j / e ν j)
      ring
    rw [h1, h2] at h
    unfold writeLHS at h
    rw [Matrix.mul_add, ← Matrix.mul_assoc]
    exact h
  -- `Z'(ν)` does not depend on `ν` (Lemma D.2 for the frozen network), so neither does
  -- `Δ̃(ν) V`; no row `a_j` of `V` vanishes (K3), so `Δ̃(ν)` does not depend on `ν`
  obtain ⟨ν₀, hν₀⟩ := hSne
  obtain ⟨Z', hZ'eq, hZ'flat⟩ := hZ' ν₀ hν₀
  have hconst : ∀ ν ∈ S, ∀ j, p ν j / e ν j = p ν₀ j / e ν₀ j := by
    intro ν hν j
    obtain ⟨Z₁, hZ₁eq, hZ₁flat⟩ := hZ' ν hν
    have hZ₁ : Z₁ = Z' := eq_of_suffixFlat_of_suffixFlat (Arch.frozen A) (θ.toFrozen A) rfl hf
      hreg k.succ hZ₁flat hZ'flat
    have hdiag : Matrix.diagonal (fun j => p ν j / e ν j) * θ.write k
        = Matrix.diagonal (fun j => p ν₀ j / e ν₀ j) * θ.write k := by
      rw [← add_left_inj (η.write k), hZ₁eq, hZ'eq, hZ₁]
    obtain ⟨c, hc⟩ : ∃ c, θ.write k j c ≠ 0 := by
      by_contra hne
      push Not at hne
      exact hθ.write_ne_zero k j (funext hne)
    have e1 := congrFun (congrFun hdiag j) c
    rw [Matrix.diagonal_mul, Matrix.diagonal_mul] at e1
    exact mul_right_cancel₀ hc e1
  refine ⟨fun j => p ν₀ j / e ν₀ j, Z', fun j => ?_, fun i c => ?_⟩
  swap
  · have h := congrFun (congrFun hZ'eq i) c
    rwa [Matrix.add_apply, Matrix.diagonal_mul] at h
  -- `ν p_j = β_j (ν e_j)` for every `ν` in the open set `S`, so `p_j = β_j e_j`
  rw [← sub_eq_zero]
  refine eq_zero_of_dotProduct_eq_zero hSo ⟨ν₀, hν₀⟩ fun ν hν => ?_
  have hne : e ν j ≠ 0 := Set.mem_iInter.1 hν.2 j
  rw [dotProduct_sub, dotProduct_smul, smul_eq_mul]
  show p ν j - p ν₀ j / e ν₀ j * e ν j = 0
  rw [← hconst ν hν j, div_mul_cancel₀ _ hne, sub_self]

/-- Helper: for `Φ` differentiable at `(x, y)`, the derivatives of its two partial maps, along `b`
and `a`, add up to its derivative along `(a, b)` (as in `Depth/StepTanh.lean`). -/
private theorem fderiv_partial_addS {E₁ E₂ F : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {Φ : E₁ → E₂ → F} {x : E₁} {y : E₂}
    (hΦ : DifferentiableAt ℝ (fun p : E₁ × E₂ => Φ p.1 p.2) (x, y)) (a : E₁) (b : E₂) :
    fderiv ℝ (fun y' => Φ x y') y b + fderiv ℝ (fun x' => Φ x' y) x a
      = fderiv ℝ (fun p : E₁ × E₂ => Φ p.1 p.2) (x, y) (a, b) := by
  have h1 : HasFDerivAt (fun x' => Φ x' y)
      ((fderiv ℝ (fun p : E₁ × E₂ => Φ p.1 p.2) (x, y)).comp
        (ContinuousLinearMap.inl ℝ E₁ E₂)) x := by
    have hc := hΦ.hasFDerivAt.comp x (hasFDerivAt_prodMk_left (𝕜 := ℝ) x y)
    exact hc
  have h2 : HasFDerivAt (fun y' => Φ x y')
      ((fderiv ℝ (fun p : E₁ × E₂ => Φ p.1 p.2) (x, y)).comp
        (ContinuousLinearMap.inr ℝ E₁ E₂)) y := by
    have hc := hΦ.hasFDerivAt.comp y (hasFDerivAt_prodMk_right (𝕜 := ℝ) x y)
    exact hc
  rw [h1.fderiv, h2.fderiv, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.inl_apply, ContinuousLinearMap.inr_apply, ← map_add, Prod.mk_add_mk,
    zero_add, add_zero]

/-- Helper: an analytic family of continuous linear maps, applied to an analytic family of vectors,
is analytic (as in `Depth/StepTanh.lean`). -/
private theorem analyticOnNhd_clm_applyS {X E F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {J : X → E →L[ℝ] F} {v : X → E} {s : Set X} (hJ : AnalyticOnNhd ℝ J s)
    (hv : AnalyticOnNhd ℝ v s) : AnalyticOnNhd ℝ (fun x => J x (v x)) s :=
  fun x hx => ((ContinuousLinearMap.id ℝ (E →L[ℝ] F)).analyticAt_bilinear (J x, v x)).comp₂
    (hJ x hx) (hv x hx)

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the matrix with all entries `0`, written with `Matrix.of`. -/
private theorem of_fun_zero {m n : Type*} : (Matrix.of fun (_ : m) (_ : n) => (0 : ℝ)) = 0 :=
  rfl

/-- Helper, **step 3 of the proof of Lemma D.12, case (n), the passage to `k + 1`:** if `η''`
satisfies (16) for `k` with `Z = 0` and vanishes at block `k`, it satisfies (16) for `k + 1` with
`Z = 0`. By (28), `𝐃_θ 𝓑(g(n)) η'' = 0` for every `n`, with the block `g`; by (R3) and the inverse
function theorem the values of `g` contain an open set, and `x ↦ 𝐃_θ 𝓑(x) η''` is analytic. -/
private theorem suffixFlat_succ_of_castSucc_gated (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (hreg : Regular (Arch.gated σ id hid) θ) (k : Fin L)
    (η : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (hflat : SuffixFlat (Arch.gated σ id hid) θ k.castSucc 0 η)
    (hr : η.read k = 0) (hw : η.write k = 0) :
    SuffixFlat (Arch.gated σ id hid) θ k.succ 0 η := by
  have hf : ∀ ℓ, AnalyticOnNhd ℝ ((Arch.gated (T := T) (d := d) σ id hid).f ℓ) Set.univ :=
    analyticOnNhd_f_gated hσa
  -- `G(x) = 𝐃_θ 𝓑_{>k+1}(x) η`
  let G : Matrix T d ℝ → Matrix T dOut ℝ := fun x =>
    fderiv ℝ (fun θ' : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut =>
      suffix (Arch.gated σ id hid) 0 θ' k.succ x) θ η
  -- (28) with `Z = 0`, `η_read = 0` (so `ż = 0`) and `η_V = 0`: `G(g(n)) = 0` for every `n`
  have h28 := (suffixFlat_castSucc_iff_gated hσ θ k 0 η).1 hflat
  have hGg : ∀ n : Matrix T d ℝ,
      G ((Arch.gated (T := T) (d := d) σ id hid).f k (n * θ.read k) * θ.write k) = 0 := by
    intro n
    have e := h28 n
    unfold blockLHSGated at e
    rw [hr, hw] at e
    simp only [Matrix.zero_mul, add_zero, Matrix.mul_zero, Matrix.zero_apply, mul_zero,
      zero_mul, of_fun_zero, map_zero, zero_add] at e
    exact e
  -- `G` is analytic: it is the derivative of `(θ', x) ↦ 𝓑_{>k+1}(x)` along `(η, 0)`
  have hΦ := analyticOnNhd_suffix_prod (Arch.gated (T := T) (d := d) σ id hid) (dIn := dIn)
    (dOut := dOut) rfl hf k.succ
  have hGeq : G = fun x => fderiv ℝ
      (fun p : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut × Matrix T d ℝ =>
        suffix (Arch.gated σ id hid) 0 p.1 k.succ p.2) (θ, x) (η, 0) := by
    funext x
    have h := fderiv_partial_addS
      (Φ := fun θ' h' => suffix (Arch.gated (T := T) (d := d) σ id hid) 0 θ' k.succ h')
      (hΦ (θ, x) (Set.mem_univ _)).differentiableAt η (0 : Matrix T d ℝ)
    rw [map_zero, zero_add] at h
    exact h
  have hG : AnalyticOnNhd ℝ G Set.univ := by
    rw [hGeq]
    exact analyticOnNhd_clm_applyS (hΦ.fderiv.comp (analyticOnNhd_const.prod analyticOnNhd_id)
      (Set.mapsTo_univ _ _)) analyticOnNhd_const
  -- (R3): `𝐃g(n₀)` is injective, hence invertible; by the inverse function theorem the values of
  -- `g` form a neighbourhood of `g(n₀)`
  obtain ⟨n₀, hn₀⟩ := hreg.deriv_block k
  have hg := analyticOnNhd_block (Arch.gated (T := T) (d := d) σ id hid) θ hf k
  let e := (LinearEquiv.ofInjectiveEndo
    (fderiv ℝ (fun n : Matrix T d ℝ =>
      (Arch.gated (T := T) (d := d) σ id hid).f k (n * θ.read k) * θ.write k) n₀ :
      Matrix T d ℝ →ₗ[ℝ] Matrix T d ℝ) hn₀).toContinuousLinearEquiv
  have hs : HasStrictFDerivAt (fun n : Matrix T d ℝ =>
      (Arch.gated (T := T) (d := d) σ id hid).f k (n * θ.read k) * θ.write k)
      (e : Matrix T d ℝ →L[ℝ] Matrix T d ℝ) n₀ := by
    have he : (e : Matrix T d ℝ →L[ℝ] Matrix T d ℝ)
        = fderiv ℝ (fun n : Matrix T d ℝ =>
          (Arch.gated (T := T) (d := d) σ id hid).f k (n * θ.read k) * θ.write k) n₀ :=
      ContinuousLinearMap.ext fun v => rfl
    rw [he]
    exact (hg n₀ (Set.mem_univ _)).hasStrictFDerivAt
  have hrange : Set.range (fun n : Matrix T d ℝ =>
      (Arch.gated (T := T) (d := d) σ id hid).f k (n * θ.read k) * θ.write k)
      ∈ 𝓝 ((Arch.gated (T := T) (d := d) σ id hid).f k (n₀ * θ.read k) * θ.write k) := by
    -- (`exact`, not `rw`: the two topologies on matrices are only definitionally equal)
    exact (hs.map_nhds_eq_of_equiv).ge Filter.range_mem_map
  -- so `G` vanishes near `g(n₀)`, hence everywhere (identity theorem)
  have hzero : G =ᶠ[𝓝 ((Arch.gated (T := T) (d := d) σ id hid).f k (n₀ * θ.read k)
      * θ.write k)] 0 :=
    Filter.eventually_of_mem hrange fun x hx => by
      obtain ⟨n, rfl⟩ := hx
      exact hGg n
  intro h
  rw [Matrix.mul_zero, map_zero, zero_add]
  exact hG.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
    (Set.mem_univ _) hzero (Set.mem_univ h)

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the read of block `ℓ` in `rescaleDir θ α` depends only on `α ℓ`. -/
private theorem rescaleDir_read_congr
    (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) (ℓ : Fin L)
    {α α' : ∀ ℓ, hid ℓ → ℝ} (h : α ℓ = α' ℓ) :
    (rescaleDir θ α).read ℓ = (rescaleDir θ α').read ℓ := by
  simp only [rescaleDir, h]

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the write of block `ℓ` in `rescaleDir θ α` depends only on `α ℓ`. -/
private theorem rescaleDir_write_congr
    (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) (ℓ : Fin L)
    {α α' : ∀ ℓ, hid ℓ → ℝ} (h : α ℓ = α' ℓ) :
    (rescaleDir θ α).write ℓ = (rescaleDir θ α').write ℓ := by
  simp only [rescaleDir, h]

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: with `α ℓ = 0`, the read of block `ℓ` in `rescaleDir θ α` is `0`. -/
private theorem rescaleDir_read_zero
    (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) (ℓ : Fin L)
    {α : ∀ ℓ, hid ℓ → ℝ} (h : α ℓ = 0) : (rescaleDir θ α).read ℓ = 0 := by
  ext i c
  cases c <;> simp [rescaleDir, h]

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: with `α ℓ = 0`, the write of block `ℓ` in `rescaleDir θ α` is `0`. -/
private theorem rescaleDir_write_zero
    (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) (ℓ : Fin L)
    {α : ∀ ℓ, hid ℓ → ℝ} (h : α ℓ = 0) : (rescaleDir θ α).write ℓ = 0 := by
  ext i c
  simp [rescaleDir, h]

/-- **Lemma D.12, steps 1 to 3, case (n).** Let `θ` be good for the cones and regular, and let
`(D_{k+1})` hold. If `Z` and `η` satisfy (16) for `k` and (38) holds for them with the frozen
network, then `η` is of the form (19) for `k` with `Z_k = Z`. -/
theorem claimGated_castSucc_of_frozen [Nonempty T] (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hσa : AnalyticOnNhd ℝ σ Set.univ) {C : Fin (L + 1) → Set (d → ℝ)}
    {A : ∀ ℓ, Finset (hid ℓ)} {θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut}
    (hθ : GoodForConesGated C A θ) (hreg : Regular (Arch.gated σ id hid) θ) (k : Fin L)
    (hk : ClaimGated ⊤ θ k.succ) (Z : Matrix d d ℝ)
    (η : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (hflat : SuffixFlat (Arch.gated σ id hid) θ k.castSucc Z η)
    (hgate : ∀ i j, (Z * θ.read k + η.read k) i (Sum.inl j) = 0)
    (hfro : ∀ n : Matrix T d ℝ, (∀ t, n t ∈ C k.castSucc) → ∀ w : Matrix T (hid k) ℝ,
      writeLHS (Arch.frozen A) (θ.toFrozen A) k (η.toFrozen A)
        (Matrix.of fun t j => w t j * (n * θ.read k) t (Sum.inr j))
        (Matrix.of fun t j => w t j * (n * (Z * θ.read k + η.read k)) t (Sum.inr j)) = 0) :
    ∃ (X : Fin (L + 1) → Matrix d d ℝ) (α : ∀ ℓ, hid ℓ → ℝ),
      X k.castSucc = Z ∧ (∀ ℓ, k.castSucc ≤ ℓ → X ℓ ∈ (⊤ : Submodule ℝ (Matrix d d ℝ))) ∧
      (∀ ℓ : Fin L, k.castSucc ≤ ℓ.castSucc →
        η.read ℓ = -(X ℓ.castSucc * θ.read ℓ) + (rescaleDir θ α).read ℓ ∧
        η.write ℓ = θ.write ℓ * X ℓ.succ + (rescaleDir θ α).write ℓ) ∧
      η.D = -(X (Fin.last L) * θ.D) := by
  classical
  -- Step 2: `P e_j = β_j e_j` for the value columns of `P = Z W + η_W`, and `Δ̃ V + η_V = V Z'`
  obtain ⟨β, Z', hβ, hZ'⟩ := exists_values_of_frozen hθ k Z η hfro
  -- so block `k` of `η` is of the form (19) with `Z_k = Z`, `Z_{k+1} = Z'`, `α_k = -β`
  -- (the gate columns by step 1, `hgate`)
  have hblock : ∀ α : ∀ ℓ, hid ℓ → ℝ, α k = -β →
      η.read k = -(Z * θ.read k) + (rescaleDir θ α).read k ∧
      η.write k = θ.write k * Z' + (rescaleDir θ α).write k := by
    intro α hα
    constructor
    · ext i c
      cases c with
      | inl j =>
        have h := hgate i j
        simp only [Matrix.add_apply] at h
        simp only [rescaleDir, Matrix.add_apply, Matrix.neg_apply, Matrix.of_apply, Sum.elim_inl]
        linarith
      | inr j =>
        have h := congrFun (hβ j) i
        simp only [Matrix.transpose_apply, Pi.smul_apply, smul_eq_mul, Matrix.add_apply] at h
        simp only [rescaleDir, Matrix.add_apply, Matrix.neg_apply, Matrix.of_apply, Sum.elim_inr,
          hα, Pi.neg_apply, neg_neg]
        linarith
    · ext i c
      have h := hZ' i c
      simp only [rescaleDir, Matrix.add_apply, Matrix.of_apply, hα, Pi.neg_apply]
      linarith
  -- Step 3: the direction `η♭ = cobDir θ X♭ + rescaleDir θ α♭` of the form (19), with
  -- `X♭_k = Z`, `X♭_{k+1} = Z'`, `α♭_k = -β` and `α♭_ℓ = 0` for the other blocks
  obtain ⟨Xb, hXbc, hXbs⟩ : ∃ Xb : Fin (L + 1) → Matrix d d ℝ, Xb k.castSucc = Z ∧ Xb k.succ = Z' :=
    ⟨Function.update (fun _ => Z') k.castSucc Z, Function.update_self _ _ _,
      Function.update_of_ne (Fin.castSucc_lt_succ).ne' _ _⟩
  obtain ⟨αb, hαbk, hαbne⟩ : ∃ αb : ∀ ℓ, hid ℓ → ℝ, αb k = -β ∧ ∀ ℓ, ℓ ≠ k → αb ℓ = 0 :=
    ⟨Function.update 0 k (-β), Function.update_self _ _ _, fun ℓ h => Function.update_of_ne h _ _⟩
  -- it satisfies (16) for `k` with `Z` (the converse of the claim)
  have hflatb : SuffixFlat (Arch.gated σ id hid) θ k.castSucc Z
      (cobDir θ Xb + rescaleDir θ αb) := by
    have h := suffixFlat_cobDir_add_rescaleDir hσ θ k.castSucc Xb αb
    rwa [hXbc] at h
  -- `η'' = η - η♭`, block by block
  obtain ⟨η'', hη''⟩ : ∃ η'', η = (cobDir θ Xb + rescaleDir θ αb) + η'' :=
    ⟨η - (cobDir θ Xb + rescaleDir θ αb), by abel⟩
  have hread : ∀ ℓ, η.read ℓ
      = (-(Xb ℓ.castSucc * θ.read ℓ) + (rescaleDir θ αb).read ℓ) + η''.read ℓ := fun ℓ => by
    rw [hη'']; rfl
  have hwrite : ∀ ℓ, η.write ℓ
      = (θ.write ℓ * Xb ℓ.succ + (rescaleDir θ αb).write ℓ) + η''.write ℓ := fun ℓ => by
    rw [hη'']; rfl
  have hDη : η.D = -(Xb (Fin.last L) * θ.D) + η''.D := by
    rw [hη'']
    show -(Xb (Fin.last L) * θ.D) + 0 + η''.D = _
    rw [add_zero]
  -- `η''` satisfies (16) for `k` with `Z = 0` (the derivatives are linear)
  have hflat'' : SuffixFlat (Arch.gated σ id hid) θ k.castSucc 0 η'' := by
    intro h
    have e1 := hflat h
    rw [hη'', map_add, ← add_assoc, hflatb h, zero_add] at e1
    rw [Matrix.mul_zero, map_zero, zero_add]
    exact e1
  -- `η''` vanishes at block `k` (step 2)
  have hr'' : η''.read k = 0 := by
    have e := hread k
    rw [hXbc, ← (hblock αb hαbk).1] at e
    exact left_eq_add.1 e
  have hw'' : η''.write k = 0 := by
    have e := hwrite k
    rw [hXbs, ← (hblock αb hαbk).2] at e
    exact left_eq_add.1 e
  -- so (16) holds for `k + 1` with `Z = 0`, and `(D_{k+1})` gives `X''`, `α''`
  have hsucc := suffixFlat_succ_of_castSucc_gated hσ hσa θ hreg k η'' hflat'' hr'' hw''
  obtain ⟨X'', α'', hX''k, -, hX'', hX''D⟩ := hk 0 η'' hsucc
  -- assembly: `X = X♭ + X''` (with `X_k = Z`), `α = α''` (with `α_k = -β`)
  refine ⟨Function.update (Xb + X'') k.castSucc Z, Function.update α'' k (-β),
    Function.update_self _ _ _, fun _ _ => Submodule.mem_top, fun ℓ hℓ => ?_, ?_⟩
  · rcases eq_or_ne ℓ k with rfl | hne
    · -- block `k`: step 2
      rw [Function.update_self, Function.update_of_ne (Fin.castSucc_lt_succ).ne', Pi.add_apply,
        hXbs, hX''k, add_zero]
      exact hblock _ (Function.update_self _ _ _)
    · -- a later block: `η = η♭ + η''`, with `α♭_ℓ = 0`
      have hlt : k < ℓ := lt_of_le_of_ne (Fin.castSucc_le_castSucc_iff.1 hℓ) (Ne.symm hne)
      have hle : k.succ ≤ ℓ.castSucc := by
        rw [Fin.le_def, Fin.val_succ, Fin.val_castSucc]
        exact hlt
      have h1 : ℓ.castSucc ≠ k.castSucc := fun h => hne (Fin.castSucc_injective _ h)
      have h2 : ℓ.succ ≠ k.castSucc := by
        intro h
        have := congrArg Fin.val h
        rw [Fin.val_succ, Fin.val_castSucc] at this
        have := Fin.lt_def.1 hlt
        omega
      obtain ⟨hr, hw⟩ := hX'' ℓ hle
      rw [Function.update_of_ne h1, Function.update_of_ne h2, Pi.add_apply, Pi.add_apply,
        rescaleDir_read_congr θ ℓ (Function.update_of_ne hne _ _),
        rescaleDir_write_congr θ ℓ (Function.update_of_ne hne _ _), hread ℓ, hwrite ℓ, hr, hw,
        rescaleDir_read_zero θ ℓ (hαbne ℓ hne), rescaleDir_write_zero θ ℓ (hαbne ℓ hne)]
      constructor
      · rw [Matrix.add_mul, neg_add]
        abel
      · rw [Matrix.mul_add]
        abel
  · -- the readout
    rw [Function.update_of_ne (Fin.castSucc_lt_last k).ne', hDη, hX''D, Pi.add_apply,
      Matrix.add_mul, neg_add]

end Skips
