import SkipsLean.Dimension.IdentifiableConverseCob

/-!
# From local identifiability to the equality condition, with countably many further images

Paper (dimension paper, proof of Proposition 4.6; skips paper, proof of Proposition 4.5):
"Conversely, let every `θ′` in a neighborhood of `θ` in `Z` be the image of `θ` under a symmetry.
With the permutations and the sign flips, the symmetries form a Lie group of dimension `k` with
finitely many components, and the images of `θ` under it form the image of a manifold of dimension
`k` under a smooth map. By Sard's theorem this image contains no open subset of a manifold of
larger dimension, so `P − r ≤ k`". The symmetries inside the blocks are listed in Appendix B of the
dimension paper: "Permutations of hidden units or heads and sign flips of tanh hidden units are
finite and remove no parameters".

`Dimension/IdentifiableConverseCob.lean` states this direction for one family `Ψ θ : N → Params` of
images of `θ` (the continuous symmetries inside the blocks) composed with the changes of basis.
Here the same four statements for countably many families `Ψ θ i`, `i : ι`: one for each
component of the group, that is, for each composition of permutations and sign flips. A
composition of symmetries in any order is a permutation and sign flip, then a continuous symmetry
inside the blocks, then a change of basis, because the changes of basis commute with the
symmetries inside the blocks and the permutations and sign flips normalize the continuous ones.
As in `IdentifiableConverseCob.lean`, the statements do not ask that the images are symmetries.
They follow from `ae_finrank_le_funDim_add_of_ae_locally_mem_iUnion_image`
(`Dimension/IdentifiableConverse.lean`), which takes countably many maps.

The forms "equality condition if and only if locally identifiable" with these further images, for
the kinds of network of the papers: `Dimension/IdentifiableIffFamily.lean`,
`Residual/IdentifiableIffFamily.lean`, `Dimension/IdentifiableIffTransformerFamily.lean`.
-/

namespace Skips

open Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]

/-- Helper: the product of two matrices that are `C¹` on a set is `C¹` there (matrix
multiplication is bilinear). -/
private theorem contDiffOn_mul_icf {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m n p : Type*} [Fintype m] [Fintype n] [Fintype p] {s : Set E}
    {f : E → Matrix m n ℝ} {g : E → Matrix n p ℝ}
    (hf : ContDiffOn ℝ 1 f s) (hg : ContDiffOn ℝ 1 g s) :
    ContDiffOn ℝ 1 (fun y => f y * g y) s := by
  -- matrix multiplication as a bilinear map
  let B : Matrix m n ℝ →ₗ[ℝ] Matrix n p ℝ →ₗ[ℝ] Matrix m p ℝ :=
    LinearMap.mk₂ ℝ (fun a b => a * b) Matrix.add_mul (fun c a b => Matrix.smul_mul c a b)
      Matrix.mul_add (fun c a b => Matrix.mul_smul a c b)
  -- the same map with continuous linear maps (all spaces are finite-dimensional)
  let B' : Matrix m n ℝ →L[ℝ] Matrix n p ℝ →L[ℝ] Matrix m p ℝ :=
    LinearMap.toContinuousLinearMap
      ((LinearMap.toContinuousLinearMap :
        (Matrix n p ℝ →ₗ[ℝ] Matrix m p ℝ) ≃ₗ[ℝ] (Matrix n p ℝ →L[ℝ] Matrix m p ℝ)).toLinearMap
        ∘ₗ B)
  have hB : (fun y => f y * g y) = fun y => B' (f y) (g y) := rfl
  rw [hB]
  exact (B'.contDiff.comp_contDiffOn hf).clm_apply hg

/-- Helper: a square matrix as a continuous linear map on `d → ℝ`; a continuous linear
equivalence onto a complete normed algebra. -/
private noncomputable def toCLM_icf : Matrix d d ℝ ≃L[ℝ] ((d → ℝ) →L[ℝ] (d → ℝ)) :=
  LinearEquiv.toContinuousLinearEquiv (Matrix.toLin'.trans LinearMap.toContinuousLinearMap)

/-- Helper: `toCLM_icf` is multiplicative. -/
private theorem toCLM_icf_mul (X Y : Matrix d d ℝ) :
    toCLM_icf (X * Y) = toCLM_icf X * toCLM_icf Y := by
  refine ContinuousLinearMap.ext fun v => ?_
  show (X * Y) *ᵥ v = X *ᵥ (Y *ᵥ v)
  rw [Matrix.mulVec_mulVec]

/-- Helper: `toCLM_icf 1 = 1`. -/
private theorem toCLM_icf_one : toCLM_icf (1 : Matrix d d ℝ) = 1 := by
  refine ContinuousLinearMap.ext fun v => ?_
  show (1 : Matrix d d ℝ) *ᵥ v = v
  rw [Matrix.one_mulVec]

/-- Helper: an invertible matrix gives a unit of the algebra of continuous linear maps, whose
inverse is the image of the matrix inverse. -/
private theorem exists_unit_icf {X : Matrix d d ℝ} (h : IsUnit X.det) :
    ∃ u : ((d → ℝ) →L[ℝ] (d → ℝ))ˣ, (u : (d → ℝ) →L[ℝ] (d → ℝ)) = toCLM_icf X ∧
      ((u⁻¹ : ((d → ℝ) →L[ℝ] (d → ℝ))ˣ) : (d → ℝ) →L[ℝ] (d → ℝ)) = toCLM_icf X⁻¹ :=
  ⟨⟨toCLM_icf X, toCLM_icf X⁻¹,
    by rw [← toCLM_icf_mul, Matrix.mul_nonsing_inv X h, toCLM_icf_one],
    by rw [← toCLM_icf_mul, Matrix.nonsing_inv_mul X h, toCLM_icf_one]⟩, rfl, rfl⟩

/-- Helper: the inverse of an invertible matrix through the continuous linear maps,
`X⁻¹ = φ⁻¹ (Ring.inverse (φ X))`. -/
private theorem nonsing_inv_eq_icf {X : Matrix d d ℝ} (h : IsUnit X.det) :
    X⁻¹ = toCLM_icf.symm (Ring.inverse (toCLM_icf X)) := by
  obtain ⟨u, hu, hu'⟩ := exists_unit_icf h
  rw [← hu, Ring.inverse_unit, hu', ContinuousLinearEquiv.symm_apply_apply]

/-- Helper: the inverse of matrices is `C¹` on the invertible matrices (the inverse is smooth
at the units of a complete normed algebra, `contDiffAt_ringInverse`). -/
private theorem contDiffOn_inv_icf :
    ContDiffOn ℝ 1 (fun X : Matrix d d ℝ => X⁻¹) {X | IsUnit X.det} := by
  intro X hX
  obtain ⟨u, hu, -⟩ := exists_unit_icf hX
  have h1 : ContDiffAt ℝ 1 Ring.inverse (toCLM_icf X) := by
    rw [← hu]
    exact contDiffAt_ringInverse ℝ u
  have hφ : ContDiffAt ℝ 1 (toCLM_icf : Matrix d d ℝ → _) X := by
    have h := (toCLM_icf (d := d)).contDiff (n := 1)
    exact h.contDiffAt
  have hψ : ContDiffAt ℝ 1 (toCLM_icf (d := d)).symm (Ring.inverse (toCLM_icf X)) := by
    have h := (toCLM_icf (d := d)).symm.contDiff (n := 1)
    exact h.contDiffAt
  have h2 : ContDiffAt ℝ 1 (fun Y => toCLM_icf.symm (Ring.inverse (toCLM_icf Y))) X := by
    have h := hψ.comp X (h1.comp X hφ)
    exact h
  exact h2.contDiffWithinAt.congr (fun Y hY => nonsing_inv_eq_icf hY) (nonsing_inv_eq_icf hX)

omit [DecidableEq d] in
/-- Helper: the transpose of matrices is `C¹` (it is linear). -/
private theorem contDiff_transpose_icf : ContDiff ℝ 1 fun X : Matrix d d ℝ => Xᵀ := by
  have h := (Matrix.transposeLinearEquiv d d ℝ ℝ).toContinuousLinearEquiv.contDiff (n := 1)
  exact h

/-- Helper: the parameter `(E g_0, k_{ℓ-1} W_read^ℓ, W_write^ℓ g_ℓ, k_L D)` built from two
families of matrices `g` and `k`; for `g = G` and `k = G⁻¹` it is the change of basis
`θ.cob G G`. -/
private def cobMat_icf {A : Arch T d L} (θ : Params A dIn dOut)
    (g k : Fin (L + 1) → Matrix d d ℝ) : Params A dIn dOut where
  E := θ.E * g 0
  read ℓ := k ℓ.castSucc * θ.read ℓ
  write ℓ := θ.write ℓ * g ℓ.succ
  D := k (Fin.last L) * θ.D

omit [Fintype T] [Fintype dIn] [Fintype dOut] in
/-- Helper: `cobMat_icf θ g k` is the change of basis `θ.cob G G` when `g_ℓ = G_ℓ` and
`k_ℓ = G_ℓ⁻¹`. -/
private theorem cobMat_eq_cob_icf {A : Arch T d L} (θ : Params A dIn dOut)
    {g k : Fin (L + 1) → Matrix d d ℝ} (G : Fin (L + 1) → GL d ℝ)
    (hg : ∀ ℓ, g ℓ = G ℓ) (hk : ∀ ℓ, k ℓ = (↑(G ℓ)⁻¹ : Matrix d d ℝ)) :
    cobMat_icf θ g k = θ.cob G G := by
  obtain rfl : g = fun ℓ => (G ℓ : Matrix d d ℝ) := funext hg
  obtain rfl : k = fun ℓ => (↑(G ℓ)⁻¹ : Matrix d d ℝ) := funext hk
  rfl

omit [Fintype T] [DecidableEq d] in
/-- Helper: `m ↦ cobMat_icf (p m) (g m) (k m)` is `C¹` on a set on which `p`, `g` and `k` are:
its four components are products of `C¹` matrices. -/
private theorem contDiffOn_cobMat_icf {A : Arch T d L} {M : Type*} [NormedAddCommGroup M]
    [NormedSpace ℝ M] {s : Set M} {p : M → Params A dIn dOut}
    {g k : M → Fin (L + 1) → Matrix d d ℝ} (hp : ContDiffOn ℝ 1 p s)
    (hg : ContDiffOn ℝ 1 g s) (hk : ContDiffOn ℝ 1 k s) :
    ContDiffOn ℝ 1 (fun m => cobMat_icf (p m) (g m) (k m)) s := by
  -- through the continuous linear equivalence with the product of the four components
  let e := (Params.linearEquivProd (A := A) (dIn := dIn) (dOut := dOut)).toContinuousLinearEquiv
  have hpe : ContDiffOn ℝ 1 (fun m => e (p m)) s := e.contDiff.comp_contDiffOn hp
  have hE : ContDiffOn ℝ 1 (fun m => (p m).E) s := by
    have h := hpe.fst
    exact h
  have hR : ContDiffOn ℝ 1 (fun m => (p m).read) s := by
    have h := hpe.snd.fst
    exact h
  have hW : ContDiffOn ℝ 1 (fun m => (p m).write) s := by
    have h := hpe.snd.snd.fst
    exact h
  have hD : ContDiffOn ℝ 1 (fun m => (p m).D) s := by
    have h := hpe.snd.snd.snd
    exact h
  have hg' := contDiffOn_pi.1 hg
  have hk' := contDiffOn_pi.1 hk
  -- the four components of the image: products of `C¹` matrices
  have key := (contDiffOn_mul_icf hE (hg' 0)).prodMk
    ((contDiffOn_pi.2 fun ℓ => contDiffOn_mul_icf (hk' ℓ.castSucc) (contDiffOn_pi.1 hR ℓ)).prodMk
      ((contDiffOn_pi.2 fun ℓ => contDiffOn_mul_icf (contDiffOn_pi.1 hW ℓ) (hg' ℓ.succ)).prodMk
        (contDiffOn_mul_icf (hk' (Fin.last L)) hD)))
  exact e.comp_contDiffOn_iff.1 key

/-- Helper: the Cayley transform times a diagonal matrix of signs, `(1 − a)(1 + a)⁻¹ D_s`. -/
private noncomputable def cayley_icf (s : d → Bool) (a : Matrix d d ℝ) : Matrix d d ℝ :=
  (1 - a) * (1 + a)⁻¹ * Matrix.diagonal fun i => if s i then (1 : ℝ) else -1

/-- Helper: on the antisymmetric matrices, `a ↦ (1 − a)(1 + a)⁻¹ D_s` is `C¹` (`1 + a` is
invertible there). -/
private theorem contDiff_cayley_icf (s : d → Bool) :
    ContDiff ℝ 1 fun a : antisymmetric d => cayley_icf s (a : Matrix d d ℝ) := by
  have h0 : ContDiff ℝ 1 fun a : antisymmetric d => (a : Matrix d d ℝ) :=
    (antisymmetric d).subtypeL.contDiff
  have h1 : ContDiffOn ℝ 1 (fun a : antisymmetric d => (1 + (a : Matrix d d ℝ))⁻¹)
      Set.univ := by
    have h := contDiffOn_inv_icf.comp (contDiff_const.add h0).contDiffOn
      (s := Set.univ) fun a _ => isUnit_det_one_add_of_mem_antisymmetric a.2
    exact h
  rw [← contDiffOn_univ]
  exact contDiffOn_mul_icf (contDiffOn_mul_icf (contDiff_const.sub h0).contDiffOn h1)
    contDiffOn_const

/-- Helper: for an orthogonal `Q`, `Q⁻¹ = Qᵀ`. -/
private theorem coe_inv_eq_transpose_icf {Q : GL d ℝ}
    (hQ : (Q : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ) :
    (↑Q⁻¹ : Matrix d d ℝ) = (Q : Matrix d d ℝ)ᵀ := by
  rw [Matrix.coe_units_inv]
  exact Matrix.inv_eq_right_inv ((Matrix.mem_orthogonalGroup_iff d ℝ).mp hQ)

/-- **From local identifiability to the equality condition, one invertible change of basis per
hidden state, countably many families of further images:** if at almost every `θ` every `θ'` near
`θ` with the same function is `(Ψ θ i n).cob G G` with `i : ι`, `n ∈ Ω i` and invertible `G_0, …,
G_L`, then at almost every `θ` `P ≤ fd(θ) + (L + 1) d² + dim N`. -/
theorem ae_finrank_le_funDim_add_of_ae_locally_cob_family (A : Arch T d L)
    (S : Fin L → Matrix d d ℝ)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (hχ : AnalyticOnNhd ℝ A.χ Set.univ)
    (μ : Measure (Params A dIn dOut)) [μ.IsAddHaarMeasure]
    {N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N] [FiniteDimensional ℝ N]
    {ι : Type*} [Countable ι] (Ψ : Params A dIn dOut → ι → N → Params A dIn dOut)
    (Ω : ι → Set N) (hΨ : ∀ θ i, ContDiffOn ℝ 1 (Ψ θ i) (Ω i))
    (hloc : ∀ᵐ θ ∂μ, ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval A S θ' x = eval A S θ x) →
        ∃ i, ∃ n ∈ Ω i, ∃ G : Fin (L + 1) → GL d ℝ, θ' = (Ψ θ i n).cob G G) :
    ∀ᵐ θ ∂μ, Module.finrank ℝ (Params A dIn dOut)
      ≤ funDim A S θ + ((L + 1) * Fintype.card d ^ 2 + Module.finrank ℝ N) := by
  -- the space `M` of the pairs `(m, n)`, `m` a family of `L + 1` square matrices
  have hdimM : Module.finrank ℝ ((Fin (L + 1) → Matrix d d ℝ) × N)
      = (L + 1) * Fintype.card d ^ 2 + Module.finrank ℝ N := by
    rw [Module.finrank_prod, Module.finrank_pi_fintype, Module.finrank_matrix]
    simp [sq]
  -- `Φ θ i (m, n) = (Ψ θ i n).cob m m`, with the matrix inverse, on the pairs with invertible
  -- `m_ℓ` and `n ∈ Ω i`
  let Φ : Params A dIn dOut → ι → (Fin (L + 1) → Matrix d d ℝ) × N → Params A dIn dOut :=
    fun θ i q => cobMat_icf (Ψ θ i q.2) q.1 fun ℓ => (q.1 ℓ)⁻¹
  let Ω' : ι → Set ((Fin (L + 1) → Matrix d d ℝ) × N) :=
    fun i => {q | (∀ ℓ, IsUnit (q.1 ℓ).det) ∧ q.2 ∈ Ω i}
  -- `Φ θ i` is `C¹` there: products of `C¹` maps, the inverse of matrices is `C¹`
  have hΦ : ∀ θ i, ContDiffOn ℝ 1 (Φ θ i) (Ω' i) := by
    intro θ i
    have hp : ContDiffOn ℝ 1 (fun q : (Fin (L + 1) → Matrix d d ℝ) × N => Ψ θ i q.2)
        (Ω' i) := by
      have h := (hΨ θ i).comp (contDiff_snd.contDiffOn (s := Ω' i)) fun q hq => hq.2
      exact h
    have hk : ∀ ℓ, ContDiffOn ℝ 1
        (fun q : (Fin (L + 1) → Matrix d d ℝ) × N => (q.1 ℓ)⁻¹) (Ω' i) := by
      intro ℓ
      have h := contDiffOn_inv_icf.comp
        (((contDiff_apply ℝ (fun _ => Matrix d d ℝ) ℓ).comp contDiff_fst).contDiffOn
          (s := Ω' i)) fun q hq => hq.1 ℓ
      exact h
    exact contDiffOn_cobMat_icf hp contDiff_fst.contDiffOn (contDiffOn_pi.2 hk)
  -- near almost every `θ`, the parameters with the same function are values of the `Φ θ i`
  have hloc' : ∀ᵐ θ ∂μ, ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval A S θ' x = eval A S θ x) →
        ∃ i, ∃ q ∈ Ω' i, Φ θ i q = θ' := by
    filter_upwards [hloc] with θ hθ
    obtain ⟨U, hU, hUθ⟩ := hθ
    refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
    obtain ⟨i, n, hn, G, rfl⟩ := hUθ θ' hθ' heq
    refine ⟨i, (fun ℓ => (G ℓ : Matrix d d ℝ), n),
      ⟨fun ℓ => (Matrix.isUnit_iff_isUnit_det _).1 (G ℓ).isUnit, hn⟩, ?_⟩
    exact cobMat_eq_cob_icf _ G (fun ℓ => rfl) fun ℓ => (Matrix.coe_units_inv (G ℓ)).symm
  -- the converse for any family of symmetries, with `dim M = (L + 1) d² + dim N`
  filter_upwards [ae_finrank_le_funDim_add_of_ae_locally_mem_iUnion_image A S hf hχ μ Φ Ω' hΦ
    hloc'] with θ hθ
  exact hθ.trans_eq (congrArg (funDim A S θ + ·) hdimM)

/-- **From local identifiability to the equality condition, one invertible change of basis at all
hidden states, countably many families of further images:** if at almost every `θ` every `θ'` near
`θ` with the same function is `(Ψ θ i n).cob (fun _ => G) (fun _ => G)` with `i : ι`, `n ∈ Ω i` and
one invertible `G`, then at almost every `θ` `P ≤ fd(θ) + d² + dim N`. -/
theorem ae_finrank_le_funDim_add_of_ae_locally_cob_const_family (A : Arch T d L)
    (S : Fin L → Matrix d d ℝ)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (hχ : AnalyticOnNhd ℝ A.χ Set.univ)
    (μ : Measure (Params A dIn dOut)) [μ.IsAddHaarMeasure]
    {N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N] [FiniteDimensional ℝ N]
    {ι : Type*} [Countable ι] (Ψ : Params A dIn dOut → ι → N → Params A dIn dOut)
    (Ω : ι → Set N) (hΨ : ∀ θ i, ContDiffOn ℝ 1 (Ψ θ i) (Ω i))
    (hloc : ∀ᵐ θ ∂μ, ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval A S θ' x = eval A S θ x) →
        ∃ i, ∃ n ∈ Ω i, ∃ G : GL d ℝ, θ' = (Ψ θ i n).cob (fun _ => G) (fun _ => G)) :
    ∀ᵐ θ ∂μ, Module.finrank ℝ (Params A dIn dOut)
      ≤ funDim A S θ + (Fintype.card d ^ 2 + Module.finrank ℝ N) := by
  -- the space `M` of the pairs `(m, n)`, `m` a square matrix
  have hdimM : Module.finrank ℝ (Matrix d d ℝ × N)
      = Fintype.card d ^ 2 + Module.finrank ℝ N := by
    rw [Module.finrank_prod, Module.finrank_matrix, Module.finrank_self, mul_one, sq]
  -- `Φ θ i (m, n) = (Ψ θ i n).cob m m` at all hidden states, on the pairs with invertible `m`
  -- and `n ∈ Ω i`
  let Φ : Params A dIn dOut → ι → Matrix d d ℝ × N → Params A dIn dOut :=
    fun θ i q => cobMat_icf (Ψ θ i q.2) (fun _ => q.1) fun _ => q.1⁻¹
  let Ω' : ι → Set (Matrix d d ℝ × N) := fun i => {q | IsUnit q.1.det ∧ q.2 ∈ Ω i}
  -- `Φ θ i` is `C¹` there
  have hΦ : ∀ θ i, ContDiffOn ℝ 1 (Φ θ i) (Ω' i) := by
    intro θ i
    have hp : ContDiffOn ℝ 1 (fun q : Matrix d d ℝ × N => Ψ θ i q.2) (Ω' i) := by
      have h := (hΨ θ i).comp (contDiff_snd.contDiffOn (s := Ω' i)) fun q hq => hq.2
      exact h
    have hk : ContDiffOn ℝ 1 (fun q : Matrix d d ℝ × N => q.1⁻¹) (Ω' i) := by
      have h := contDiffOn_inv_icf.comp (contDiff_fst.contDiffOn (s := Ω' i)) fun q hq => hq.1
      exact h
    exact contDiffOn_cobMat_icf hp (contDiffOn_pi.2 fun _ => contDiff_fst.contDiffOn)
      (contDiffOn_pi.2 fun _ => hk)
  -- near almost every `θ`, the parameters with the same function are values of the `Φ θ i`
  have hloc' : ∀ᵐ θ ∂μ, ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval A S θ' x = eval A S θ x) →
        ∃ i, ∃ q ∈ Ω' i, Φ θ i q = θ' := by
    filter_upwards [hloc] with θ hθ
    obtain ⟨U, hU, hUθ⟩ := hθ
    refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
    obtain ⟨i, n, hn, G, rfl⟩ := hUθ θ' hθ' heq
    refine ⟨i, ((G : Matrix d d ℝ), n),
      ⟨(Matrix.isUnit_iff_isUnit_det _).1 G.isUnit, hn⟩, ?_⟩
    exact cobMat_eq_cob_icf _ (fun _ => G) (fun _ => rfl) fun _ => (Matrix.coe_units_inv G).symm
  -- the converse for any family of symmetries, with `dim M = d² + dim N`
  filter_upwards [ae_finrank_le_funDim_add_of_ae_locally_mem_iUnion_image A S hf hχ μ Φ Ω' hΦ
    hloc'] with θ hθ
  exact hθ.trans_eq (congrArg (funDim A S θ + ·) hdimM)

/-- **From local identifiability to the equality condition, one orthogonal change of basis per
hidden state, countably many families of further images:** if at almost every `θ` every `θ'` near
`θ` with the same function is `(Ψ θ i n).cob Q Q` with `i : ι`, `n ∈ Ω i` and orthogonal `Q_0, …,
Q_L`, then at almost every `θ` `P ≤ fd(θ) + (L + 1) d(d−1)/2 + dim N`. -/
theorem ae_finrank_le_funDim_add_of_ae_locally_cob_orthogonal_family (A : Arch T d L)
    (S : Fin L → Matrix d d ℝ)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (hχ : AnalyticOnNhd ℝ A.χ Set.univ)
    (μ : Measure (Params A dIn dOut)) [μ.IsAddHaarMeasure]
    {N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N] [FiniteDimensional ℝ N]
    {ι : Type*} [Countable ι] (Ψ : Params A dIn dOut → ι → N → Params A dIn dOut)
    (Ω : ι → Set N) (hΨ : ∀ θ i, ContDiffOn ℝ 1 (Ψ θ i) (Ω i))
    (hloc : ∀ᵐ θ ∂μ, ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval A S θ' x = eval A S θ x) →
        ∃ i, ∃ n ∈ Ω i, ∃ Q : Fin (L + 1) → GL d ℝ,
          (∀ ℓ, (Q ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ) ∧
            θ' = (Ψ θ i n).cob Q Q) :
    ∀ᵐ θ ∂μ, Module.finrank ℝ (Params A dIn dOut)
      ≤ funDim A S θ
        + ((L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2) + Module.finrank ℝ N) := by
  -- the space `M` of the pairs `(a, n)`, `a` a family of `L + 1` antisymmetric matrices
  have hdimM : Module.finrank ℝ ((Fin (L + 1) → antisymmetric d) × N)
      = (L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2) + Module.finrank ℝ N := by
    rw [Module.finrank_prod, Module.finrank_pi_fintype, finrank_antisymmetric, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  -- for `i : ι` and signs `σ_ℓ`, `Φ θ (i, σ) (a, n) = (Ψ θ i n).cob Q Q` with
  -- `Q_ℓ = (1 − a_ℓ)(1 + a_ℓ)⁻¹ D_{σ_ℓ}` and `Q_ℓ⁻¹ = Q_ℓᵀ`, on the pairs with `n ∈ Ω i`
  let Φ : Params A dIn dOut → ι × (Fin (L + 1) → d → Bool) →
      (Fin (L + 1) → antisymmetric d) × N → Params A dIn dOut :=
    fun θ j q => cobMat_icf (Ψ θ j.1 q.2) (fun ℓ => cayley_icf (j.2 ℓ) (q.1 ℓ))
      fun ℓ => (cayley_icf (j.2 ℓ) (q.1 ℓ))ᵀ
  let Ω' : ι × (Fin (L + 1) → d → Bool) → Set ((Fin (L + 1) → antisymmetric d) × N) :=
    fun j => {q | q.2 ∈ Ω j.1}
  -- `Φ θ j` is `C¹` there
  have hΦ : ∀ θ j, ContDiffOn ℝ 1 (Φ θ j) (Ω' j) := by
    intro θ j
    have hp : ContDiffOn ℝ 1 (fun q : (Fin (L + 1) → antisymmetric d) × N => Ψ θ j.1 q.2)
        (Ω' j) := by
      have h := (hΨ θ j.1).comp (contDiff_snd.contDiffOn (s := Ω' j)) fun q hq => hq
      exact h
    have hc : ∀ ℓ, ContDiff ℝ 1 fun q : (Fin (L + 1) → antisymmetric d) × N =>
        cayley_icf (j.2 ℓ) (q.1 ℓ : Matrix d d ℝ) := fun ℓ =>
      (contDiff_cayley_icf (j.2 ℓ)).comp
        ((contDiff_apply ℝ (fun _ => antisymmetric d) ℓ).comp contDiff_fst)
    exact contDiffOn_cobMat_icf hp (contDiff_pi.2 hc).contDiffOn
      (contDiff_pi.2 fun ℓ => contDiff_transpose_icf.comp (hc ℓ)).contDiffOn
  -- near almost every `θ`, the parameters with the same function are values of the `Φ θ j`:
  -- every orthogonal `Q_ℓ` is a Cayley transform times signs
  have hloc' : ∀ᵐ θ ∂μ, ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval A S θ' x = eval A S θ x) →
        ∃ j, ∃ q ∈ Ω' j, Φ θ j q = θ' := by
    filter_upwards [hloc] with θ hθ
    obtain ⟨U, hU, hUθ⟩ := hθ
    refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
    obtain ⟨i, n, hn, Q, hQ, rfl⟩ := hUθ θ' hθ' heq
    choose σ a ha hQa using fun ℓ => exists_cayley_mul_diagonal_of_mem_orthogonalGroup (hQ ℓ)
    refine ⟨(i, σ), (fun ℓ => ⟨a ℓ, ha ℓ⟩, n), hn, ?_⟩
    refine cobMat_eq_cob_icf _ Q (fun ℓ => (hQa ℓ).symm) fun ℓ => ?_
    rw [coe_inv_eq_transpose_icf (hQ ℓ), hQa ℓ]
    rfl
  -- the converse for any family of symmetries, with `dim M = (L + 1) d (d − 1) / 2 + dim N`
  filter_upwards [ae_finrank_le_funDim_add_of_ae_locally_mem_iUnion_image A S hf hχ μ Φ Ω' hΦ
    hloc'] with θ hθ
  exact hθ.trans_eq (congrArg (funDim A S θ + ·) hdimM)

/-- **From local identifiability to the equality condition, one orthogonal change of basis at all
hidden states, countably many families of further images:** if at almost every `θ` every `θ'` near
`θ` with the same function is `(Ψ θ i n).cob (fun _ => Q) (fun _ => Q)` with `i : ι`, `n ∈ Ω i` and
one orthogonal `Q`, then at almost every `θ` `P ≤ fd(θ) + d(d−1)/2 + dim N`. -/
theorem ae_finrank_le_funDim_add_of_ae_locally_cob_const_orthogonal_family (A : Arch T d L)
    (S : Fin L → Matrix d d ℝ)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (hχ : AnalyticOnNhd ℝ A.χ Set.univ)
    (μ : Measure (Params A dIn dOut)) [μ.IsAddHaarMeasure]
    {N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N] [FiniteDimensional ℝ N]
    {ι : Type*} [Countable ι] (Ψ : Params A dIn dOut → ι → N → Params A dIn dOut)
    (Ω : ι → Set N) (hΨ : ∀ θ i, ContDiffOn ℝ 1 (Ψ θ i) (Ω i))
    (hloc : ∀ᵐ θ ∂μ, ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval A S θ' x = eval A S θ x) →
        ∃ i, ∃ n ∈ Ω i, ∃ Q : GL d ℝ, (Q : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ ∧
          θ' = (Ψ θ i n).cob (fun _ => Q) (fun _ => Q)) :
    ∀ᵐ θ ∂μ, Module.finrank ℝ (Params A dIn dOut)
      ≤ funDim A S θ
        + (Fintype.card d * (Fintype.card d - 1) / 2 + Module.finrank ℝ N) := by
  -- the space `M` of the pairs `(a, n)`, `a` an antisymmetric matrix
  have hdimM : Module.finrank ℝ (antisymmetric d × N)
      = Fintype.card d * (Fintype.card d - 1) / 2 + Module.finrank ℝ N := by
    rw [Module.finrank_prod, finrank_antisymmetric]
  -- for `i : ι` and signs `s`, `Φ θ (i, s) (a, n) = (Ψ θ i n).cob Q Q` with
  -- `Q = (1 − a)(1 + a)⁻¹ D_s` at all hidden states and `Q⁻¹ = Qᵀ`, on the pairs with `n ∈ Ω i`
  let Φ : Params A dIn dOut → ι × (d → Bool) → antisymmetric d × N → Params A dIn dOut :=
    fun θ j q => cobMat_icf (Ψ θ j.1 q.2) (fun _ => cayley_icf j.2 q.1)
      fun _ => (cayley_icf j.2 q.1)ᵀ
  let Ω' : ι × (d → Bool) → Set (antisymmetric d × N) := fun j => {q | q.2 ∈ Ω j.1}
  -- `Φ θ j` is `C¹` there
  have hΦ : ∀ θ j, ContDiffOn ℝ 1 (Φ θ j) (Ω' j) := by
    intro θ j
    have hp : ContDiffOn ℝ 1 (fun q : antisymmetric d × N => Ψ θ j.1 q.2) (Ω' j) := by
      have h := (hΨ θ j.1).comp (contDiff_snd.contDiffOn (s := Ω' j)) fun q hq => hq
      exact h
    have hc : ContDiff ℝ 1 fun q : antisymmetric d × N => cayley_icf j.2 (q.1 : Matrix d d ℝ) :=
      (contDiff_cayley_icf j.2).comp contDiff_fst
    exact contDiffOn_cobMat_icf hp (contDiff_pi.2 fun _ => hc).contDiffOn
      (contDiff_pi.2 fun _ => contDiff_transpose_icf.comp hc).contDiffOn
  -- near almost every `θ`, the parameters with the same function are values of the `Φ θ j`:
  -- every orthogonal `Q` is a Cayley transform times signs
  have hloc' : ∀ᵐ θ ∂μ, ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval A S θ' x = eval A S θ x) →
        ∃ j, ∃ q ∈ Ω' j, Φ θ j q = θ' := by
    filter_upwards [hloc] with θ hθ
    obtain ⟨U, hU, hUθ⟩ := hθ
    refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
    obtain ⟨i, n, hn, Q, hQ, rfl⟩ := hUθ θ' hθ' heq
    obtain ⟨s, a, ha, hQa⟩ := exists_cayley_mul_diagonal_of_mem_orthogonalGroup hQ
    refine ⟨(i, s), (⟨a, ha⟩, n), hn, ?_⟩
    refine cobMat_eq_cob_icf _ (fun _ => Q) (fun _ => hQa.symm) fun _ => ?_
    rw [coe_inv_eq_transpose_icf hQ, hQa]
    rfl
  -- the converse for any family of symmetries, with `dim M = d (d − 1) / 2 + dim N`
  filter_upwards [ae_finrank_le_funDim_add_of_ae_locally_mem_iUnion_image A S hf hχ μ Φ Ω' hΦ
    hloc'] with θ hθ
  exact hθ.trans_eq (congrArg (funDim A S θ + ·) hdimM)

end Skips
