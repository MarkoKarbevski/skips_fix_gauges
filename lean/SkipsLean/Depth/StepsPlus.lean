import SkipsLean.Depth.Frozen
import SkipsLean.Depth.SuffixGated
import SkipsLean.Depth.StepTanhRMS

/-!
# Lemma D.12, steps 1 to 3, under pre-RMSNorm

Paper (dimension): Appendix D.5, proof of Lemma D.12, from equation (38) to the end, in the case
(+). "Step 1: the gates. By (26), `ż^g(n)` is a polynomial in `n` that vanishes on the open set
`C_k`, so it vanishes for all `n`. […] In the case (+) its part of degree 3 is
`⟨n Z, n⟩ n W_g = 0`, so `Z` is antisymmetric, as `W_g ≠ 0`, and its part of degree 1 gives
`η_g = −Z W_g`. In both cases `Z ∈ 𝔤`, and in a gated block `ż^v(n) = n (Z W_v + η_v)`."
"Step 2: the values and the write" gives, by Lemmas D.3 and D.2, a matrix `Z'` and a diagonal
matrix `Δ_{k+1}` (`Δ_{k+1} = 0` in a GELU block) with `η_V = Δ_{k+1} V + V Z'`,
`η_v = −Z W_v − W_v Δ_{k+1}`, and the identity (16) for `k+1` with `Z'`. "Step 3: the rest. In the
case (+), `𝓑^∞ = 𝓑_{>k+1}`, and the second part of (39) is (16) for `k+1`, with `Z'` and `η'`. By
`(D_{k+1})`, `Z' ∈ 𝔤` and `η'` is of the form (19), or (17) for GELU blocks, with `Z_{k+1} = Z'`.
With Steps 1 and 2 this is (19), or (17), for `k`."

Stated here: the conclusion of `(D_k)` for one pair `Z`, `η`, from (38), for gated blocks with a
real-analytic gate (the claim `ClaimGated (antisymmetric d)`) and for MLP blocks with a
real-analytic activation (the claim `ClaimRMS`; the GELU blocks of the paper). (38) is the
hypothesis: for gated blocks `ż^g(n) = 0` and the identity with `writeLHS` at `v = w̃ ⊙ ι(n)`,
`vdot = w̃ ⊙ ż^v(n)`, for all `n` with rows in `C_k`; for MLP blocks `ż(n) = 0` for these `n` and
the identity at `v = w̃`, `vdot = 0`. Here `ż(n) = (n Z − ⟨n Z, n⟩ n / d) W_read + n η_read`
(`tangentRMS`).
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise Topology

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]
variable {σ : ℝ → ℝ} {ε : ℝ}

omit [Fintype T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: row `t` of `ż(n) = (n Z − ⟨n Z, n⟩ n / d) W + n η` (equation (20)) is
`n_t (Z W + η) − q(n_t) n_t W`, with `q(ν) = ⟨ν Z, ν⟩ / d`. -/
private theorem tangentRMS_mul_add_row (Z : Matrix d d ℝ) (n : Matrix T d ℝ) {m : Type*}
    (W η : Matrix d m ℝ) (t : T) :
    (tangentRMS Z n * W + n * η) t
      = n t ᵥ* (Z * W + η) - ((n t ᵥ* Z) ⬝ᵥ n t / (Fintype.card d : ℝ)) • (n t ᵥ* W) := by
  have h1 : (tangentRMS Z n * W + n * η) t = (tangentRMS Z n * W) t + (n * η) t := rfl
  have h2 : tangentRMS Z n t
      = n t ᵥ* Z - ((n t ᵥ* Z) ⬝ᵥ n t / (Fintype.card d : ℝ)) • n t := by
    show (n * Z) t - ((n * Z) t ⬝ᵥ n t / (Fintype.card d : ℝ)) • n t = _
    rw [Matrix.mul_apply_eq_vecMul]
  rw [h1, Matrix.mul_apply_eq_vecMul, Matrix.mul_apply_eq_vecMul, h2, Matrix.sub_vecMul,
    Matrix.smul_vecMul, Matrix.vecMul_vecMul, Matrix.vecMul_add]
  abel

omit [Fintype T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: entry `(t, x)` of `ż(n)` is `n_t ⬝ P_x − q(n_t) (n_t ⬝ W_x)`, with the columns `P_x` of
`P = Z W + η` and `W_x` of `W`. -/
private theorem tangentRMS_mul_add_apply (Z : Matrix d d ℝ) (n : Matrix T d ℝ) {m : Type*}
    (W η : Matrix d m ℝ) (t : T) (x : m) :
    (tangentRMS Z n * W + n * η) t x
      = n t ⬝ᵥ (Z * W + η)ᵀ x - ((n t ᵥ* Z) ⬝ᵥ n t / (Fintype.card d : ℝ)) * (n t ⬝ᵥ Wᵀ x) := by
  rw [tangentRMS_mul_add_row]
  rfl

omit [Fintype T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: if `⟨ν Z, ν⟩ = 0` for every row `ν`, then `ż(n)` has no part of degree 3:
`n Z − ⟨n Z, n⟩ n / d = n Z`. -/
private theorem tangentRMS_eq_mul {Z : Matrix d d ℝ} (hQ : ∀ v : d → ℝ, (v ᵥ* Z) ⬝ᵥ v = 0)
    (n : Matrix T d ℝ) : tangentRMS Z n = n * Z := by
  funext t
  show (n * Z) t - ((n * Z) t ⬝ᵥ n t / (Fintype.card d : ℝ)) • n t = (n * Z) t
  rw [Matrix.mul_apply_eq_vecMul, hQ, zero_div, zero_smul, sub_zero]

omit [Fintype T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: a vector `c` with `ν ⬝ c = 0` for every row `ν` of an open nonempty set is `0` (move
`ν₀` of the set along the basis vector `i` by a small `ε ≠ 0`; as in `Depth/StepsGatedN.lean`). -/
private theorem eq_zero_of_dotProduct_eq_zeroP {S : Set (d → ℝ)} (hS : IsOpen S)
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

omit [Fintype T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the quadratic form `ν ↦ ⟨ν Z, ν⟩` vanishes everywhere if it vanishes on an open
nonempty set (for `ν₀` in the set and small `τ ≠ 0`, the values at `ν₀ ± τ v` add up to
`2 ⟨ν₀ Z, ν₀⟩ + 2 τ² ⟨v Z, v⟩`). -/
private theorem vecMul_dotProduct_self_eq_zero {S : Set (d → ℝ)} (hS : IsOpen S)
    (hne : S.Nonempty) {Z : Matrix d d ℝ} (h : ∀ ν ∈ S, (ν ᵥ* Z) ⬝ᵥ ν = 0) (v : d → ℝ) :
    (v ᵥ* Z) ⬝ᵥ v = 0 := by
  obtain ⟨ν₀, hν₀⟩ := hne
  have hev1 : ∀ᶠ τ in 𝓝 (0 : ℝ), ν₀ + τ • v ∈ S := by
    have hcont : Continuous fun τ : ℝ => ν₀ + τ • v :=
      continuous_const.add (continuous_id.smul continuous_const)
    refine hcont.continuousAt.preimage_mem_nhds ?_
    simpa using hS.mem_nhds hν₀
  have hev2 : ∀ᶠ τ in 𝓝 (0 : ℝ), ν₀ - τ • v ∈ S := by
    have hcont : Continuous fun τ : ℝ => ν₀ - τ • v :=
      continuous_const.sub (continuous_id.smul continuous_const)
    refine hcont.continuousAt.preimage_mem_nhds ?_
    simpa using hS.mem_nhds hν₀
  obtain ⟨τ, ⟨h1, h2⟩, hτ⟩ := (((hev1.and hev2).filter_mono nhdsWithin_le_nhds).and
    (eventually_mem_nhdsWithin (a := (0 : ℝ)) (s := {0}ᶜ))).exists
  have e0 := h ν₀ hν₀
  have e1 := h _ h1
  have e2 := h _ h2
  simp only [add_vecMul, sub_vecMul, smul_vecMul, add_dotProduct, dotProduct_add, sub_dotProduct,
    dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul] at e1 e2
  have e : τ * τ * ((v ᵥ* Z) ⬝ᵥ v) = 0 := by linear_combination (e1 + e2 - 2 * e0) / 2
  exact (mul_eq_zero.1 e).resolve_left (mul_ne_zero hτ hτ)

omit [Fintype T] [Fintype dIn] [Fintype dOut] in
/-- Helper: a matrix `Z` with `⟨ξ Z, ξ⟩ = 0` for every row `ξ` is antisymmetric (polarization:
`⟨(e_j + e_i) Z, e_j + e_i⟩ = Z_{jj} + Z_{ji} + Z_{ij} + Z_{ii}`; as in `Depth/StepTanhRMS.lean`). -/
private theorem mem_antisymmetric_of_vecMul_dotProduct_selfP {Z : Matrix d d ℝ}
    (hq : ∀ ξ : d → ℝ, (ξ ᵥ* Z) ⬝ᵥ ξ = 0) : Z ∈ antisymmetric d := by
  have hd : ∀ i, Z i i = 0 := fun i => by
    simpa only [single_one_vecMul, dotProduct_single, Matrix.row_apply, mul_one] using
      hq (Pi.single i 1)
  show Zᵀ = -Z
  ext i j
  have e := hq (Pi.single j 1 + Pi.single i 1)
  simp only [add_vecMul, dotProduct_add, single_one_vecMul, dotProduct_single, mul_one,
    Pi.add_apply, Matrix.row_apply, hd, zero_add, add_zero] at e
  rw [Matrix.transpose_apply, Matrix.neg_apply]
  linarith

omit [Fintype T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: if a matrix with the columns `d` has rank `card d` and no rows, then `d` is empty. -/
private theorem isEmpty_of_rank_eq {m : Type*} [Fintype m] {M : Matrix m d ℝ}
    (hM : M.rank = Fintype.card d) (hm : IsEmpty m) : IsEmpty d := by
  have h := Matrix.rank_le_card_height M
  rw [hM, Fintype.card_eq_zero (α := m)] at h
  exact Fintype.card_eq_zero_iff.1 (by omega)

omit [Fintype T] [Fintype dIn] [Fintype dOut] in
/-- Helper, **step 1 of the proof of Lemma D.12, case (+): the gates.** Let `C` be an open convex
cone on which no `ν ⬝ c_j` vanishes, and let `ν ⬝ p_j − q(ν) (ν ⬝ c_j) = 0` for all `ν ∈ C` and all
`j`, with `q(ν) = ⟨ν Z, ν⟩ / d`. Then `Z` is antisymmetric, `⟨ν Z, ν⟩ = 0` for every row `ν`, and
every `p_j` is `0`. (With `2 ν ∈ C`: `2 a − 8 b = 0` and `a − b = 0`, so the parts `a` of degree 1
and `b` of degree 3 vanish; `b = 0` with `ν ⬝ c_j ≠ 0` gives `q = 0` on the cone.) -/
private theorem gates_of_cone {ι : Type*} {C : Set (d → ℝ)} (hC : IsOpenConvexCone C)
    {Z : Matrix d d ℝ} {p c : ι → d → ℝ} (hd : IsEmpty ι → IsEmpty d)
    (hc : ∀ ν ∈ C, ∀ j, ν ⬝ᵥ c j ≠ 0)
    (h : ∀ ν ∈ C, ∀ j, ν ⬝ᵥ p j - ((ν ᵥ* Z) ⬝ᵥ ν / (Fintype.card d : ℝ)) * (ν ⬝ᵥ c j) = 0) :
    Z ∈ antisymmetric d ∧ (∀ v : d → ℝ, (v ᵥ* Z) ⬝ᵥ v = 0) ∧ ∀ j, p j = 0 := by
  -- at `ν` and at `2 ν`: the parts of degree 1 and 3 vanish separately
  have hsplit : ∀ ν ∈ C, ∀ j, ν ⬝ᵥ p j = 0 ∧
      ((ν ᵥ* Z) ⬝ᵥ ν / (Fintype.card d : ℝ)) * (ν ⬝ᵥ c j) = 0 := by
    intro ν hν j
    have e1 := h ν hν j
    have e2 := h ((2 : ℝ) • ν) (hC.smul_mem ν hν 2 two_pos) j
    simp only [smul_vecMul, smul_dotProduct, dotProduct_smul, smul_eq_mul] at e2
    constructor
    · linear_combination (8 * e1 - e2) / 6
    · linear_combination (2 * e1 - e2) / 6
  -- the quadratic form vanishes on the cone, hence everywhere
  have hQ : ∀ v : d → ℝ, (v ᵥ* Z) ⬝ᵥ v = 0 := by
    rcases isEmpty_or_nonempty d with hd' | hd'
    · intro v
      simp only [dotProduct, Finset.univ_eq_empty, Finset.sum_empty]
    rcases isEmpty_or_nonempty ι with hι | ⟨⟨j₀⟩⟩
    · exact absurd (hd hι) (not_isEmpty_of_nonempty d)
    have hcard : (Fintype.card d : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
    refine vecMul_dotProduct_self_eq_zero hC.isOpen hC.nonempty fun ν hν => ?_
    have e := (mul_eq_zero.1 (hsplit ν hν j₀).2).resolve_right (hc ν hν j₀)
    rwa [div_eq_zero_iff, or_iff_left hcard] at e
  exact ⟨mem_antisymmetric_of_vecMul_dotProduct_selfP hQ, hQ, fun j =>
    eq_zero_of_dotProduct_eq_zeroP hC.isOpen hC.nonempty fun ν hν => (hsplit ν hν j).1⟩

/-- Helper: at a regular parameter under pre-RMSNorm with `ε > 0`, the identity (16) determines
`Z`: if it holds for `Z₁` and for `Z₂` with the same `η`, then `h Z₁` and `h Z₂` have the same image
under `𝐃𝓑_{>k}(h)`, which is injective on a dense set of `h` (Lemma D.2, case (+)). -/
private theorem eq_of_suffixFlat_of_suffixFlat_rmsNorm [Nonempty T] (hε : 0 < ε)
    (Ar : Arch T d L) (θ : Params Ar dIn dOut) (hχ : Ar.χ = rmsNorm ε)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (Ar.f ℓ) Set.univ) (hθ : Regular Ar θ) (k : Fin (L + 1))
    {Z₁ Z₂ : Matrix d d ℝ} {η : Params Ar dIn dOut}
    (h₁ : SuffixFlat Ar θ k Z₁ η) (h₂ : SuffixFlat Ar θ k Z₂ η) : Z₁ = Z₂ := by
  classical
  -- Lemma D.2: `𝐃𝓑_{>k}(h)` is injective for `h` in a dense set `U`
  obtain ⟨U, -, hUd, hU⟩ := exists_open_dense_injective_fderiv_suffix_rmsNorm Ar θ hε hχ hf hθ k
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
/-- Helper: for `c ≠ 0`, the rows `ν` with `ν ⬝ c ≠ 0` are dense (as in
`Depth/StepsGatedN.lean`). -/
private theorem dense_setOf_dotProduct_ne_zeroP {c : d → ℝ} (hc : c ≠ 0) :
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

/-- Helper, **step 2 of the proof of Lemma D.12, case (+): the values and the write.** From (38),
once `ż^v(n) = n (Z W_v + η_v)`: there are numbers `β_j` (the diagonal of `Δ̃`) and a matrix `Z'`
with `P e_j = β_j e_j` for the value columns of `P = Z W + η_W`, `Δ̃ V + η_V = V Z'`, and the
identity (16) for `k + 1` with `Z'` (Lemmas D.3 and D.2, case (+), for the network itself). -/
private theorem exists_values_rmsNorm [Nonempty T] (hε : 0 < ε)
    (hσa : AnalyticOnNhd ℝ σ Set.univ) {C : Fin (L + 1) → Set (d → ℝ)}
    {A : ∀ ℓ, Finset (hid ℓ)}
    {θ : Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut}
    (hθ : GoodForConesGated C A θ) (hreg : Regular (Arch.gated σ (rmsNorm ε) hid) θ) (k : Fin L)
    (Z : Matrix d d ℝ) (η : Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)
    (hval : ∀ n : Matrix T d ℝ, (∀ t, n t ∈ C k.castSucc) → ∀ w : Matrix T (hid k) ℝ,
      writeLHS (Arch.gated σ (rmsNorm ε) hid) θ k η
        (Matrix.of fun t j => w t j * (n * θ.read k) t (Sum.inr j))
        (Matrix.of fun t j => w t j * (n * (Z * θ.read k + η.read k)) t (Sum.inr j)) = 0) :
    ∃ (β : hid k → ℝ) (Z' : Matrix d d ℝ),
      (∀ j, (Z * θ.read k + η.read k)ᵀ (Sum.inr j) = β j • (θ.read k)ᵀ (Sum.inr j)) ∧
      (∀ i c, β i * θ.write k i c + η.write k i c = (θ.write k * Z') i c) ∧
      SuffixFlat (Arch.gated σ (rmsNorm ε) hid) θ k.succ Z' η := by
  classical
  -- the blocks are analytic: Lemmas D.2 and D.3 (case (+)) hold for the network
  have hf : ∀ ℓ, AnalyticOnNhd ℝ ((Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid).f ℓ)
      Set.univ := analyticOnNhd_f_gated hσa
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
      dense_iInter_of_isOpen hopen fun j => dense_setOf_dotProduct_ne_zeroP (hθ.value_ne_zero k j)
    exact hD.inter_open_nonempty _ (hθ.cone _).isOpen (hθ.cone _).nonempty
  -- a matrix `n` with every row `ν`
  have hrow : ∀ (ν : d → ℝ) (M : Matrix d (hid k ⊕ hid k) ℝ) (t : T) (c : hid k ⊕ hid k),
      (Matrix.of (fun _ : T => ν) * M) t c = ν ⬝ᵥ Mᵀ c := fun _ _ _ _ => rfl
  -- for `ν ∈ S`, (38) at `n` with rows `ν` and `w̃ = v / (ν e)` is the hypothesis of Lemma D.3
  -- at the write `V`: `Δ̃(ν) V + η_V = V Z'(ν)` and (16) for `k + 1`
  have hZ' : ∀ ν ∈ S, ∃ Z' : Matrix d d ℝ,
      Matrix.diagonal (fun j => p ν j / e ν j) * θ.write k + η.write k = θ.write k * Z' ∧
      SuffixFlat (Arch.gated σ (rmsNorm ε) hid) θ k.succ Z' η := by
    intro ν hν
    have hne : ∀ j, e ν j ≠ 0 := Set.mem_iInter.1 hν.2
    refine suffixFlat_of_flat_at_write_rmsNorm (Arch.gated σ (rmsNorm ε) hid) θ hε rfl hf hreg
      k.succ (θ.write k) (hθ.rank_write k) _ η fun v => ?_
    have h := hval (Matrix.of fun _ => ν) (fun _ => hν.1) (Matrix.of fun t j => v t j / e ν j)
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
  -- `Z'(ν)` does not depend on `ν` (Lemma D.2), so neither does `Δ̃(ν) V`; no row `a_j` of `V`
  -- vanishes (K3), so `Δ̃(ν)` does not depend on `ν`
  obtain ⟨ν₀, hν₀⟩ := hSne
  obtain ⟨Z', hZ'eq, hZ'flat⟩ := hZ' ν₀ hν₀
  have hconst : ∀ ν ∈ S, ∀ j, p ν j / e ν j = p ν₀ j / e ν₀ j := by
    intro ν hν j
    obtain ⟨Z₁, hZ₁eq, hZ₁flat⟩ := hZ' ν hν
    have hZ₁ : Z₁ = Z' := eq_of_suffixFlat_of_suffixFlat_rmsNorm hε
      (Arch.gated σ (rmsNorm ε) hid) θ rfl hf hreg k.succ hZ₁flat hZ'flat
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
  refine ⟨fun j => p ν₀ j / e ν₀ j, Z', fun j => ?_, fun i c => ?_, hZ'flat⟩
  swap
  · have h := congrFun (congrFun hZ'eq i) c
    rwa [Matrix.add_apply, Matrix.diagonal_mul] at h
  -- `ν p_j = β_j (ν e_j)` for every `ν` in the open set `S`, so `p_j = β_j e_j`
  rw [← sub_eq_zero]
  refine eq_zero_of_dotProduct_eq_zeroP hSo ⟨ν₀, hν₀⟩ fun ν hν => ?_
  have hne : e ν j ≠ 0 := Set.mem_iInter.1 hν.2 j
  rw [dotProduct_sub, dotProduct_smul, smul_eq_mul]
  show p ν j - p ν₀ j / e ν₀ j * e ν j = 0
  rw [← hconst ν hν j, div_mul_cancel₀ _ hne, sub_self]

omit [Fintype T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the read of block `ℓ` in `rescaleDir θ α` depends only on `α ℓ`. -/
private theorem rescaleDir_read_congrP
    (θ : Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut) (ℓ : Fin L)
    {α α' : ∀ ℓ, hid ℓ → ℝ} (h : α ℓ = α' ℓ) :
    (rescaleDir θ α).read ℓ = (rescaleDir θ α').read ℓ := by
  simp only [rescaleDir, h]

omit [Fintype T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the write of block `ℓ` in `rescaleDir θ α` depends only on `α ℓ`. -/
private theorem rescaleDir_write_congrP
    (θ : Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut) (ℓ : Fin L)
    {α α' : ∀ ℓ, hid ℓ → ℝ} (h : α ℓ = α' ℓ) :
    (rescaleDir θ α).write ℓ = (rescaleDir θ α').write ℓ := by
  simp only [rescaleDir, h]

/-- **Lemma D.12, steps 1 to 3, gated blocks, case (+).** Let `θ` be good for the cones and
regular, and let `(D_{k+1})` hold. If (38) holds for `Z` and `η`, then `Z` is antisymmetric and `η`
is of the form (19) for `k` with `Z_k = Z`. -/
theorem claimGated_castSucc_of_flat_rmsNorm [Nonempty T] (hε : 0 < ε)
    (hσa : AnalyticOnNhd ℝ σ Set.univ) {C : Fin (L + 1) → Set (d → ℝ)}
    {A : ∀ ℓ, Finset (hid ℓ)}
    {θ : Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut}
    (hθ : GoodForConesGated C A θ) (hreg : Regular (Arch.gated σ (rmsNorm ε) hid) θ) (k : Fin L)
    (hk : ClaimGated (antisymmetric d) θ k.succ) (Z : Matrix d d ℝ)
    (η : Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)
    (h38 : ∀ n : Matrix T d ℝ, (∀ t, n t ∈ C k.castSucc) →
      (∀ t j, (tangentRMS Z n * θ.read k + n * η.read k) t (Sum.inl j) = 0) ∧
      ∀ w : Matrix T (hid k) ℝ,
        writeLHS (Arch.gated σ (rmsNorm ε) hid) θ k η
          (Matrix.of fun t j => w t j * (n * θ.read k) t (Sum.inr j))
          (Matrix.of fun t j =>
            w t j * (tangentRMS Z n * θ.read k + n * η.read k) t (Sum.inr j)) = 0) :
    ∃ (X : Fin (L + 1) → Matrix d d ℝ) (α : ∀ ℓ, hid ℓ → ℝ),
      X k.castSucc = Z ∧ (∀ ℓ, k.castSucc ≤ ℓ → X ℓ ∈ antisymmetric d) ∧
      (∀ ℓ : Fin L, k.castSucc ≤ ℓ.castSucc →
        η.read ℓ = -(X ℓ.castSucc * θ.read ℓ) + (rescaleDir θ α).read ℓ ∧
        η.write ℓ = θ.write ℓ * X ℓ.succ + (rescaleDir θ α).write ℓ) ∧
      η.D = -(X (Fin.last L) * θ.D) := by
  classical
  obtain ⟨t₀⟩ := ‹Nonempty T›
  -- equation (20) on a matrix `n` whose rows are all `ν`: `ż_x = ν P_x − q(ν) (ν W_x)`
  have hrowν : ∀ (ν : d → ℝ) (x : hid k ⊕ hid k),
      (tangentRMS Z (Matrix.of fun _ : T => ν) * θ.read k
        + (Matrix.of fun _ : T => ν) * η.read k) t₀ x
      = ν ⬝ᵥ (Z * θ.read k + η.read k)ᵀ x
        - ((ν ᵥ* Z) ⬝ᵥ ν / (Fintype.card d : ℝ)) * (ν ⬝ᵥ (θ.read k)ᵀ x) :=
    fun ν x => tangentRMS_mul_add_apply Z _ _ _ t₀ x
  -- Step 1: the gates. `Z` is antisymmetric, `⟨ν Z, ν⟩ = 0`, and `η_g = −Z W_g`
  obtain ⟨hanti, hQ, hgate⟩ := gates_of_cone (hθ.cone k.castSucc) (ι := hid k)
    (p := fun j => (Z * θ.read k + η.read k)ᵀ (Sum.inl j))
    (c := fun j => (θ.read k)ᵀ (Sum.inl j))
    (fun hι => isEmpty_of_rank_eq (hθ.rank_write k) hι)
    (fun ν hν j => by
      by_cases hj : j ∈ A k
      · exact (hθ.gate_pos k ν hν j hj).ne'
      · exact (hθ.gate_neg k ν hν j hj).ne)
    (fun ν hν j => (hrowν ν (Sum.inl j)).symm.trans
      ((h38 (Matrix.of fun _ => ν) fun _ => hν).1 t₀ j))
  -- so `ż^v(n) = n (Z W_v + η_v)`, and the second part of (38) is the hypothesis of step 2
  have hval : ∀ n : Matrix T d ℝ, (∀ t, n t ∈ C k.castSucc) → ∀ w : Matrix T (hid k) ℝ,
      writeLHS (Arch.gated σ (rmsNorm ε) hid) θ k η
        (Matrix.of fun t j => w t j * (n * θ.read k) t (Sum.inr j))
        (Matrix.of fun t j => w t j * (n * (Z * θ.read k + η.read k)) t (Sum.inr j)) = 0 := by
    intro n hn w
    have hP : tangentRMS Z n * θ.read k + n * η.read k = n * (Z * θ.read k + η.read k) := by
      rw [tangentRMS_eq_mul hQ, Matrix.mul_add, Matrix.mul_assoc]
    have e := (h38 n hn).2 w
    rw [hP] at e
    exact e
  -- Step 2: `P e_j = β_j e_j` for the value columns, `Δ̃ V + η_V = V Z'`, and (16) for `k + 1`
  obtain ⟨β, Z', hβ, hZ', hflat'⟩ := exists_values_rmsNorm hε hσa hθ hreg k Z η hval
  -- so block `k` of `η` is of the form (19) with `Z_k = Z`, `Z_{k+1} = Z'`, `α_k = -β`
  have hblock : ∀ α : ∀ ℓ, hid ℓ → ℝ, α k = -β →
      η.read k = -(Z * θ.read k) + (rescaleDir θ α).read k ∧
      η.write k = θ.write k * Z' + (rescaleDir θ α).write k := by
    intro α hα
    constructor
    · ext i c
      cases c with
      | inl j =>
        have h := congrFun (hgate j) i
        simp only [Matrix.transpose_apply, Matrix.add_apply, Pi.zero_apply] at h
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
  -- Step 3: `(D_{k+1})` for `Z'` and `η` gives `X'`, `α'` from block `k + 1` on
  obtain ⟨X', α', hX'k, hX'a, hX', hX'D⟩ := hk Z' η hflat'
  -- put `Z` at the hidden state before block `k`, and `-β` at block `k`
  refine ⟨Function.update X' k.castSucc Z, Function.update α' k (-β),
    Function.update_self _ _ _, fun ℓ hℓ => ?_, fun ℓ hℓ => ?_, ?_⟩
  · -- antisymmetric: `Z` by step 1, the later ones by `(D_{k+1})`
    rcases eq_or_ne ℓ k.castSucc with rfl | hne
    · rw [Function.update_self]
      exact hanti
    · rw [Function.update_of_ne hne]
      refine hX'a ℓ ?_
      have hlt : k.castSucc < ℓ := lt_of_le_of_ne hℓ (Ne.symm hne)
      rw [Fin.lt_def, Fin.val_castSucc] at hlt
      rw [Fin.le_def, Fin.val_succ]
      omega
  · rcases eq_or_ne ℓ k with rfl | hne
    · -- block `k`: steps 1 and 2
      rw [Function.update_self, Function.update_of_ne (Fin.castSucc_lt_succ).ne', hX'k]
      exact hblock _ (Function.update_self _ _ _)
    · -- a later block: `(D_{k+1})`, with `α_ℓ = α'_ℓ`
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
      rw [Function.update_of_ne h1, Function.update_of_ne h2,
        rescaleDir_read_congrP θ ℓ (Function.update_of_ne hne _ _),
        rescaleDir_write_congrP θ ℓ (Function.update_of_ne hne _ _)]
      exact hX' ℓ hle
  · -- the readout
    rw [Function.update_of_ne (Fin.castSucc_lt_last k).ne']
    exact hX'D

/-- **Lemma D.12, steps 1 to 3, MLP blocks, case (+).** Let `θ` be good for the cones and regular,
and let `(D_{k+1})` hold. If (38) holds for `Z` and `η`, then `Z` is antisymmetric and `η` is of
the form (17) for `k` with `Z_k = Z`. -/
theorem claimRMS_castSucc_of_flat_rmsNorm [Nonempty T] (hε : 0 < ε)
    (hσa : AnalyticOnNhd ℝ σ Set.univ) {C : Fin (L + 1) → Set (d → ℝ)}
    {A : ∀ ℓ, Finset (hid ℓ)}
    {θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut}
    (hθ : GoodForConesMlp C A θ) (hreg : Regular (Arch.mlp σ (rmsNorm ε) hid) θ) (k : Fin L)
    (hk : ClaimRMS (Arch.mlp σ (rmsNorm ε) hid) θ k.succ) (Z : Matrix d d ℝ)
    (η : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)
    (hz : ∀ n : Matrix T d ℝ, (∀ t, n t ∈ C k.castSucc) →
      tangentRMS Z n * θ.read k + n * η.read k = 0)
    (hw : ∀ w : Matrix T (hid k) ℝ, writeLHS (Arch.mlp σ (rmsNorm ε) hid) θ k η w 0 = 0) :
    ∃ X : Fin (L + 1) → Matrix d d ℝ, X k.castSucc = Z ∧
      (∀ ℓ, k.castSucc ≤ ℓ → X ℓ ∈ antisymmetric d) ∧
      (∀ ℓ : Fin L, k.castSucc ≤ ℓ.castSucc →
        η.read ℓ = -(X ℓ.castSucc * θ.read ℓ) ∧ η.write ℓ = θ.write ℓ * X ℓ.succ) ∧
      η.D = -(X (Fin.last L) * θ.D) := by
  classical
  obtain ⟨t₀⟩ := ‹Nonempty T›
  have hf : ∀ ℓ, AnalyticOnNhd ℝ ((Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid).f ℓ)
      Set.univ := fun ℓ => analyticOnNhd_f_mlp hσa ℓ
  -- equation (20) on a matrix `n` whose rows are all `ν`: `ż_j = ν P_j − q(ν) (ν c_j)`
  have hrowν : ∀ (ν : d → ℝ) (x : hid k),
      (tangentRMS Z (Matrix.of fun _ : T => ν) * θ.read k
        + (Matrix.of fun _ : T => ν) * η.read k) t₀ x
      = ν ⬝ᵥ (Z * θ.read k + η.read k)ᵀ x
        - ((ν ᵥ* Z) ⬝ᵥ ν / (Fintype.card d : ℝ)) * (ν ⬝ᵥ (θ.read k)ᵀ x) :=
    fun ν x => tangentRMS_mul_add_apply Z _ _ _ t₀ x
  -- Step 1: `Z` is antisymmetric and `P = Z W + η_W = 0`
  obtain ⟨hanti, -, hP⟩ := gates_of_cone (hθ.cone k.castSucc) (ι := hid k)
    (p := fun j => (Z * θ.read k + η.read k)ᵀ j) (c := fun j => (θ.read k)ᵀ j)
    (fun hι => isEmpty_of_rank_eq (hθ.rank_write k) hι)
    (fun ν hν j => by
      by_cases hj : j ∈ A k
      · exact (hθ.gate_pos k ν hν j hj).ne'
      · exact (hθ.gate_neg k ν hν j hj).ne)
    (fun ν hν j => (hrowν ν j).symm.trans
      (congrFun (congrFun (hz (Matrix.of fun _ => ν) fun _ => hν) t₀) j))
  have hread : η.read k = -(Z * θ.read k) := by
    ext i j
    have h := congrFun (hP j) i
    simp only [Matrix.transpose_apply, Matrix.add_apply, Pi.zero_apply] at h
    rw [Matrix.neg_apply]
    linarith
  -- Step 2: the hypothesis of Lemma D.3 at the write `V` (rank `d`): `η_V = V Z'` and (16) for
  -- `k + 1`
  obtain ⟨Z', hZ', hflat'⟩ := suffixFlat_of_flat_at_write_rmsNorm
    (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) θ hε rfl hf hreg k.succ (θ.write k)
    (hθ.rank_write k) (η.write k) η fun w => by
      have e := hw w
      unfold writeLHS at e
      rw [Matrix.zero_mul, zero_add] at e
      exact e
  -- Step 3: `(D_{k+1})` gives the antisymmetric changes of basis after the block
  obtain ⟨X, hXk, hXa, hX, hXD⟩ := hk Z' η hflat'
  -- put `Z` at the hidden state before the block
  refine ⟨Function.update X k.castSucc Z, Function.update_self _ _ _, fun ℓ hℓ => ?_,
    fun ℓ hℓ => ?_, ?_⟩
  · -- antisymmetric: `Z` by step 1, the later ones by `(D_{k+1})`
    rcases eq_or_ne ℓ k.castSucc with rfl | hne
    · rw [Function.update_self]
      exact hanti
    · rw [Function.update_of_ne hne]
      refine hXa ℓ ?_
      have hlt : k.castSucc < ℓ := lt_of_le_of_ne hℓ (Ne.symm hne)
      rw [Fin.lt_def, Fin.val_castSucc] at hlt
      rw [Fin.le_def, Fin.val_succ]
      omega
  · rcases eq_or_ne ℓ k with rfl | hne
    · -- the block itself: steps 1 and 2
      rw [Function.update_self, Function.update_of_ne (Fin.castSucc_lt_succ).ne', hXk]
      exact ⟨hread, hZ'⟩
    · -- a later block: `(D_{k+1})`
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
      rw [Function.update_of_ne h1, Function.update_of_ne h2]
      exact hX ℓ hle
  · -- the readout
    rw [Function.update_of_ne (Fin.castSucc_lt_last k).ne']
    exact hXD

end Skips
