import SkipsLean.Residual.FewerHiddenUnits

/-!
# Too few extra hidden units: skipless blocks with fewer than `d` hidden units

Paper (skips paper), Theorem A.28 (iii): "Too few extra hidden units. For GELU blocks with an
embedding and a readout, without normalization, and almost every choice of weights, a residual
network of `L` blocks equals no skipless network of `L` blocks with, in total, fewer than
`L d_model / 2` more hidden units."

Its proof begins with the skipless networks that have a block with fewer than `d_model` hidden
units: "If some `d'_hidden,ℓ < d_model`, the hidden state `h_ℓ` of the skipless network lies in a
subspace of dimension `d'_hidden,ℓ`, so the Jacobian of its output with respect to the input has
rank below `d_model` at every input. That of the residual network is `ED + O(τ)` at the parameters
`θ_τ` of Lemma A.27, of rank `d_model` for small `τ`, so by analyticity it has rank `d_model` at
some input for almost every choice of weights, and the two networks differ. So let every
`d'_hidden,ℓ ≥ d_model`."

`Residual/FewerHiddenUnits.lean` has the theorem for skipless blocks of at least `d` hidden units
(the setting of the main text). Here the first case of the proof, and then the theorem for all
widths.

* `inputRank`: the rank of the Jacobian of the output with respect to the input. An input has the
  tokens `T`, and an MLP block acts on every token, so the paper's ranks `d'_hidden,ℓ` and
  `d_model`, which are for one token, are `|T| d'_hidden,ℓ` and `|T| d_model` here.
* `inputRank_skipless_le`: in a network without skips the output is a function of the outputs of
  the hidden units of block `ℓ`, so the rank is at most `|T|` times their number. Stated for every
  kind of block with a differentiable fixed map; the number is that of the rows of the write.
* `le_inputRank_residual_mlp_zero`, `ae_le_inputRank_residual_mlp_zero`: the residual network.
  The paper takes the parameters `θ_τ` and analyticity in the weights. Here the input `0`: when
  `σ(0) = 0` (GELU), every hidden state vanishes there, and the Jacobian at `0` is
  `v ↦ v E ∏_ℓ (I + σ'(0) W_read^ℓ W_write^ℓ) D`, polynomial in the weights. It has rank
  `|T| d` when `E` and `D` have rank `d` and every factor is invertible, which holds at generic
  parameters when `d_in, d_out ≥ d`.
* `ae_forall_eval_residual_ne_skipless_of_card_lt`: so at generic parameters the residual network
  computes the function of no network without skips that has a block with fewer than `d` rows in
  its write, of any depth and with any differentiable blocks.
* `ae_forall_all_widths_eval_residual_ne_skipless_gelu`: Theorem A.28 (iii) as the paper states
  it, for all widths of the skipless network, under Sard's theorem (which the case of widths at
  least `d` uses, `Literature/Sard.lean`).

Theorem A.28 (iv) is stated in the paper only for skipless networks whose blocks all have at least
`d_model` hidden units (`ae_not_isPointwiseLimit_skipless_gelu_widths`).

Numeric check of the Jacobian at `0` and of the rank bound:
`narrow_skipless_input_rank_check_2026-11-25.py`.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [Fintype dIn] [Fintype dOut]

/-- The rank of the Jacobian of the output `x ↦ F_θ(x)` with respect to the input, at the input
`x`. -/
noncomputable def inputRank (A : Arch T d L) (S : Fin L → Matrix d d ℝ) (θ : Params A dIn dOut)
    (x : Matrix T dIn ℝ) : ℕ :=
  Module.finrank ℝ (LinearMap.range (fderiv ℝ (eval A S θ) x).toLinearMap)

/-- Helper: the product of two differentiable matrix-valued maps is differentiable (as
`differentiable_matMul` in `Dimension/Functional.lean`, which is private there). -/
private theorem differentiable_matMul_fhn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
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

omit [Fintype dOut] in
/-- Helper: with differentiable blocks and `χ`, every hidden state is a differentiable function
of the input. -/
private theorem differentiable_hidden_fhn {A : Arch T d L} (hf : ∀ ℓ, Differentiable ℝ (A.f ℓ))
    (hχ : Differentiable ℝ A.χ) (S : Fin L → Matrix d d ℝ) (θ : Params A dIn dOut)
    (k : Fin (L + 1)) : Differentiable ℝ (fun x : Matrix T dIn ℝ => hidden A S θ x k) := by
  induction k using Fin.induction with
  | zero =>
    -- `h_0 = x E`
    simp only [hidden_zero]
    exact differentiable_matMul_fhn differentiable_id (differentiable_const θ.E)
  | succ ℓ ih =>
    -- `h_{ℓ+1} = h_ℓ S_ℓ + f_ℓ (χ(h_ℓ) W_read) W_write`: products, compositions and a sum
    simp only [hidden_succ]
    exact (differentiable_matMul_fhn ih (differentiable_const (S ℓ))).add
      (differentiable_matMul_fhn ((hf ℓ).comp (differentiable_matMul_fhn (hχ.comp ih)
        (differentiable_const (θ.read ℓ)))) (differentiable_const (θ.write ℓ)))

/-- Helper: in a network without skips, with differentiable blocks and `χ`, the network after
the hidden state `h_k`, `h ↦ 𝓑_{>k}(h)`, is differentiable. -/
private theorem differentiable_suffix_fhn {A : Arch T d L} (hf : ∀ ℓ, Differentiable ℝ (A.f ℓ))
    (hχ : Differentiable ℝ A.χ) (θ : Params A dIn dOut) (k : Fin (L + 1)) :
    Differentiable ℝ (fun h : Matrix T d ℝ => suffix A 0 θ k h) := by
  classical
  induction k using Fin.reverseInduction with
  | last =>
    -- `𝓑_{>L}(h) = χ(h) D`
    simp only [suffix_last]
    exact differentiable_matMul_fhn hχ (differentiable_const θ.D)
  | cast ℓ ih =>
    -- `𝓑_{>ℓ-1}(h) = 𝓑_{>ℓ}(f_ℓ(χ(h) W_read) W_write)`
    simp only [suffix_castSucc, Pi.zero_apply, Matrix.mul_zero, zero_add]
    have hc := ih.comp (differentiable_matMul_fhn ((hf ℓ).comp (differentiable_matMul_fhn hχ
      (differentiable_const (θ.read ℓ)))) (differentiable_const (θ.write ℓ)))
    exact hc

/-- **Theorem A.28 (iii) of the skips paper, "the hidden state `h_ℓ` of the skipless network lies
in a subspace of dimension `d'_hidden,ℓ`, so the Jacobian of its output with respect to the input
has rank below `d_model` at every input":** in a network without skips whose blocks and whose map
`χ` are differentiable, the Jacobian of the output with respect to the input has, at every input
and for every block `ℓ`, rank at most `|T|` times the number of rows of the write of block `ℓ`
(for an MLP block, the number of its hidden units). -/
theorem inputRank_skipless_le {A : Arch T d L} (hf : ∀ ℓ, Differentiable ℝ (A.f ℓ))
    (hχ : Differentiable ℝ A.χ) (θ : Params A dIn dOut) (x : Matrix T dIn ℝ) (ℓ : Fin L) :
    inputRank A 0 θ x ≤ Fintype.card T * Fintype.card (A.w ℓ) := by
  classical
  -- `a x`: the outputs of the hidden units of block `ℓ`; `Ψ b`: the output of the network when
  -- they are `b`, so that `F_θ = Ψ ∘ a`
  let a : Matrix T dIn ℝ → Matrix T (A.w ℓ) ℝ := fun y =>
    A.f ℓ (A.χ (hidden A 0 θ y ℓ.castSucc) * θ.read ℓ)
  let Ψ : Matrix T (A.w ℓ) ℝ → Matrix T dOut ℝ := fun b => suffix A 0 θ ℓ.succ (b * θ.write ℓ)
  have hfac : eval A 0 θ = Ψ ∘ a := by
    funext y
    rw [← suffix_hidden A 0 θ y ℓ.succ, hidden_succ]
    simp only [Pi.zero_apply, Matrix.mul_zero, zero_add]
    rfl
  have ha : Differentiable ℝ a := (hf ℓ).comp (differentiable_matMul_fhn
    (hχ.comp (differentiable_hidden_fhn hf hχ 0 θ ℓ.castSucc)) (differentiable_const (θ.read ℓ)))
  have hΨ : Differentiable ℝ Ψ := (differentiable_suffix_fhn hf hχ θ ℓ.succ).comp
    (differentiable_matMul_fhn differentiable_id (differentiable_const (θ.write ℓ)))
  -- the chain rule: the Jacobian factors through `Matrix T (A.w ℓ) ℝ`
  have hd : HasFDerivAt (eval A 0 θ) ((fderiv ℝ Ψ (a x)).comp (fderiv ℝ a x)) x := by
    rw [hfac]
    exact (hΨ (a x)).hasFDerivAt.comp x (ha x).hasFDerivAt
  have he : fderiv ℝ (eval A 0 θ) x = (fderiv ℝ Ψ (a x)).comp (fderiv ℝ a x) := hd.fderiv
  have hle : LinearMap.range ((fderiv ℝ Ψ (a x)).comp (fderiv ℝ a x)).toLinearMap
      ≤ LinearMap.range (fderiv ℝ Ψ (a x)).toLinearMap := by
    rintro _ ⟨v, rfl⟩
    exact ⟨fderiv ℝ a x v, rfl⟩
  unfold inputRank
  rw [he]
  calc Module.finrank ℝ (LinearMap.range ((fderiv ℝ Ψ (a x)).comp (fderiv ℝ a x)).toLinearMap)
      ≤ Module.finrank ℝ (LinearMap.range (fderiv ℝ Ψ (a x)).toLinearMap) :=
        Submodule.finrank_mono hle
    _ ≤ Module.finrank ℝ (Matrix T (A.w ℓ) ℝ) := LinearMap.finrank_range_le _
    _ = Fintype.card T * Fintype.card (A.w ℓ) := by
        rw [Module.finrank_matrix, Module.finrank_self, mul_one]


variable [DecidableEq d] {σ : ℝ → ℝ} {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]

/-- Helper: `y ↦ y M`, as a continuous linear map. -/
private noncomputable def mulRightCLM_fhn {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
    (M : Matrix n p ℝ) : Matrix m n ℝ →L[ℝ] Matrix m p ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun y => y * M
      map_add' := fun a b => Matrix.add_mul a b M
      map_smul' := fun c a => Matrix.smul_mul c a M }

/-- Helper: `M ↦ σ(M)` (entrywise) has the derivative `N ↦ c N` at `0`, if `σ'(0) = c`. -/
private theorem hasFDerivAt_map_zero_fhn {m n : Type*} [Fintype m] [Fintype n] {c : ℝ}
    (hσ : HasDerivAt σ c 0) :
    HasFDerivAt (fun M : Matrix m n ℝ => M.map σ)
      (c • ContinuousLinearMap.id ℝ (Matrix m n ℝ)) 0 := by
  refine hasFDerivAt_pi'' fun t => hasFDerivAt_pi'' fun i => ?_
  -- the entry `(t, i)` is `σ` of the entry `(t, i)` of `M`
  have hσ' : HasDerivAt σ c ((0 : Matrix m n ℝ) t i) := hσ
  have h := hσ'.comp_hasFDerivAt (0 : Matrix m n ℝ)
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : n => ℝ) i).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : m => n → ℝ) t)).hasFDerivAt
  refine h.congr_fderiv (ContinuousLinearMap.ext fun M => ?_)
  show c * M t i = c * M t i
  rfl

omit [Fintype dOut] in
/-- Helper: in a residual network of MLP blocks with `σ(0) = 0` and `σ'(0) = c`, at the input
`0` every hidden state vanishes, and the derivative of `x ↦ h_k(x)` there is `v ↦ v E P_k` with
`P_k = ∏_{ℓ < k} (I + c W_read^ℓ W_write^ℓ)`, invertible if every factor is. -/
private theorem hasFDerivAt_hidden_zero_fhn (hσ0 : σ 0 = 0) {c : ℝ} (hσ : HasDerivAt σ c 0)
    (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)
    (hu : ∀ ℓ, IsUnit (1 + c • (θ.read ℓ * θ.write ℓ)).det) (k : Fin (L + 1)) :
    ∃ P : Matrix d d ℝ, IsUnit P.det ∧ hidden (Arch.mlp σ id hid) 1 θ 0 k = 0 ∧
      HasFDerivAt (fun x => hidden (Arch.mlp σ id hid) 1 θ x k)
        (mulRightCLM_fhn (m := T) (θ.E * P)) 0 := by
  induction k using Fin.induction with
  | zero =>
    -- `h_0 = x E`, so `P_0 = 1`
    refine ⟨1, by rw [Matrix.det_one]; exact isUnit_one, by rw [hidden_zero, Matrix.zero_mul],
      ?_⟩
    have h1 : (fun x => hidden (Arch.mlp σ id hid) 1 θ x 0)
        = mulRightCLM_fhn (m := T) (θ.E * (1 : Matrix d d ℝ)) := by
      funext x
      rw [hidden_zero, Matrix.mul_one]
      rfl
    rw [h1]
    exact (mulRightCLM_fhn (θ.E * (1 : Matrix d d ℝ))).hasFDerivAt
  | succ ℓ ih =>
    obtain ⟨P, hP, h0, hd⟩ := ih
    refine ⟨P * (1 + c • (θ.read ℓ * θ.write ℓ)), ?_, ?_, ?_⟩
    · -- a product of invertible matrices
      rw [Matrix.det_mul]
      exact hP.mul (hu ℓ)
    · -- `h_{ℓ+1}(0) = 0 + σ(0) W_write = 0`
      rw [hidden_succ, h0]
      show (0 : Matrix T d ℝ) * 1 + ((0 : Matrix T d ℝ) * θ.read ℓ).map σ * θ.write ℓ = 0
      rw [Matrix.zero_mul, Matrix.zero_mul, Matrix.map_zero σ hσ0, Matrix.zero_mul, add_zero]
    · -- the chain rule, block by block: `x ↦ h_ℓ(x) W_read`, then `σ` at `0`, then `W_write`
      have hR := (mulRightCLM_fhn (m := T) (θ.read ℓ)).hasFDerivAt.comp (0 : Matrix T dIn ℝ) hd
      have hmap : HasFDerivAt (fun M : Matrix T (hid ℓ) ℝ => M.map σ)
          (c • ContinuousLinearMap.id ℝ (Matrix T (hid ℓ) ℝ))
          ((mulRightCLM_fhn (m := T) (θ.read ℓ))
            (hidden (Arch.mlp σ id hid) 1 θ 0 ℓ.castSucc)) := by
        have hz : (mulRightCLM_fhn (m := T) (θ.read ℓ))
            (hidden (Arch.mlp σ id hid) 1 θ 0 ℓ.castSucc) = 0 := by
          rw [h0, map_zero]
        rw [hz]
        exact hasFDerivAt_map_zero_fhn hσ
      have hB := (mulRightCLM_fhn (m := T) (θ.write ℓ)).hasFDerivAt.comp (0 : Matrix T dIn ℝ)
        (hmap.comp (0 : Matrix T dIn ℝ) hR)
      have hS := (mulRightCLM_fhn (m := T) (1 : Matrix d d ℝ)).hasFDerivAt.comp
        (0 : Matrix T dIn ℝ) hd
      have hsum := hS.add hB
      simp only [hidden_succ]
      refine hsum.congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
      show v * (θ.E * P) * (1 : Matrix d d ℝ) + (c • (v * (θ.E * P) * θ.read ℓ)) * θ.write ℓ
        = v * (θ.E * (P * (1 + c • (θ.read ℓ * θ.write ℓ))))
      simp only [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, Matrix.smul_mul,
        Matrix.mul_assoc]

/-- **The Jacobian of a residual network of MLP blocks with respect to the input, at the input
`0`, at one parameter:** if `σ(0) = 0` and `σ` is differentiable at `0`, every hidden state
vanishes at the input `0`, and the Jacobian there is
`v ↦ v E ∏_ℓ (I + σ'(0) W_read^ℓ W_write^ℓ) D`. So if `E` and `D` have rank `d` and every
`I + σ'(0) W_read^ℓ W_write^ℓ` is invertible, it has rank at least `|T| d`. -/
theorem le_inputRank_residual_mlp_zero (hσ0 : σ 0 = 0) (hσ : DifferentiableAt ℝ σ 0)
    (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d) (hD : θ.D.rank = Fintype.card d)
    (hu : ∀ ℓ, IsUnit (1 + deriv σ 0 • (θ.read ℓ * θ.write ℓ)).det) :
    Fintype.card T * Fintype.card d ≤ inputRank (Arch.mlp σ id hid) 1 θ 0 := by
  -- the Jacobian at `0` is `v ↦ v E P D` with `P` invertible
  obtain ⟨P, hP, -, hd⟩ := hasFDerivAt_hidden_zero_fhn hσ0 hσ.hasDerivAt θ hu (Fin.last L)
  have hev : HasFDerivAt (eval (Arch.mlp σ id hid) 1 θ)
      ((mulRightCLM_fhn (m := T) θ.D).comp (mulRightCLM_fhn (m := T) (θ.E * P))) 0 :=
    (mulRightCLM_fhn (m := T) θ.D).hasFDerivAt.comp (0 : Matrix T dIn ℝ) hd
  have he : fderiv ℝ (eval (Arch.mlp σ id hid) 1 θ) 0
      = (mulRightCLM_fhn (m := T) θ.D).comp (mulRightCLM_fhn (m := T) (θ.E * P)) := hev.fderiv
  -- a left inverse of `E` and a right inverse of `D`, which have rank `d`
  obtain ⟨E', hE'⟩ := Matrix.vecMul_surjective_iff_exists_left_inverse.mp
    (Matrix.vecMul_surjective_iff_rank_eq_card.mpr hE)
  obtain ⟨D', hD'⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.mp
    (Matrix.mulVec_surjective_iff_rank_eq_card.mpr hD)
  -- `u ↦ u D` is injective, and its range lies in that of the Jacobian (`v = u P⁻¹ E'`)
  let g : Matrix T d ℝ →ₗ[ℝ] Matrix T dOut ℝ :=
    { toFun := fun u => u * θ.D
      map_add' := fun a b => Matrix.add_mul a b θ.D
      map_smul' := fun c a => Matrix.smul_mul c a θ.D }
  have hg : Function.Injective g := by
    intro u u' huu
    have h1 : u * θ.D * D' = u' * θ.D * D' := congrArg (· * D') huu
    simpa only [Matrix.mul_assoc, hD', Matrix.mul_one] using h1
  have hle : LinearMap.range g ≤ LinearMap.range
      ((mulRightCLM_fhn (m := T) θ.D).comp (mulRightCLM_fhn (m := T) (θ.E * P))).toLinearMap := by
    rintro _ ⟨u, rfl⟩
    refine ⟨u * P⁻¹ * E', ?_⟩
    show u * P⁻¹ * E' * (θ.E * P) * θ.D = u * θ.D
    rw [Matrix.mul_assoc (u * P⁻¹) E', ← Matrix.mul_assoc E', hE', Matrix.one_mul,
      Matrix.mul_assoc u, Matrix.nonsing_inv_mul _ hP, Matrix.mul_one]
  unfold inputRank
  rw [he]
  calc Fintype.card T * Fintype.card d = Module.finrank ℝ (Matrix T d ℝ) := by
        rw [Module.finrank_matrix, Module.finrank_self, mul_one]
    _ = Module.finrank ℝ (LinearMap.range g) := (LinearMap.finrank_range_of_inj hg).symm
    _ ≤ _ := Submodule.finrank_mono hle

/-- Helper: a matrix with `d` columns has rank `d` if some `d` of its rows form an invertible
matrix (as `rank_eq_of_isUnit_det_submatrix` in `Generic/Params.lean`, private there). -/
private theorem rank_eq_of_isUnit_det_submatrix_fhn {m : Type*} (M : Matrix m d ℝ) (ρ : d ↪ m)
    (h : IsUnit (M.submatrix ρ id).det) : M.rank = Fintype.card d :=
  le_antisymm (Matrix.rank_le_card_width M)
    ((Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).2 h)).symm.le.trans
      (Matrix.rank_submatrix_le M ρ id))

/-- Helper: at generic parameters `E` has rank `d`, when `d_in ≥ d` (as `ae_rank_E` in
`Generic/Params.lean`, private there). -/
private theorem ae_rank_E_fhn {A : Arch T d L} (μ : Measure (Params A dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn) :
    ∀ᵐ θ ∂μ, θ.E.rank = Fintype.card d := by
  -- `d` rows of `E`, invertible at generic parameters
  obtain ⟨ρ⟩ := Function.Embedding.nonempty_of_card_le hdIn
  filter_upwards [ae_isUnit_det_submatrix μ] with θ hθ
  exact rank_eq_of_isUnit_det_submatrix_fhn θ.E ρ (hθ.2.2.1 ρ)

/-- Helper: at generic parameters `D` has rank `d`, when `d_out ≥ d`. -/
private theorem ae_rank_D_fhn {A : Arch T d L} (μ : Measure (Params A dIn dOut))
    [μ.IsAddHaarMeasure] (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, θ.D.rank = Fintype.card d := by
  -- `d` columns of `D`, invertible at generic parameters
  obtain ⟨c⟩ := Function.Embedding.nonempty_of_card_le hdOut
  filter_upwards [ae_isUnit_det_submatrix μ] with θ hθ
  exact rank_eq_card_of_isUnit_det θ.D c (hθ.2.1 c)

/-- **Theorem A.28 (iii) of the skips paper, "it has rank `d_model` at some input for almost every
choice of weights", for MLP blocks whose activation has `σ(0) = 0` and is differentiable at `0`:**
with `d_in, d_out ≥ d`, at generic parameters of the residual network the Jacobian of the output
with respect to the input has rank at least `|T| d` at the input `0`. -/
theorem ae_le_inputRank_residual_mlp_zero (hσ0 : σ 0 = 0) (hσ : DifferentiableAt ℝ σ 0)
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, Fintype.card T * Fintype.card d ≤ inputRank (Arch.mlp σ id hid) 1 θ 0 := by
  -- `E` and `D` have rank `d` at generic parameters
  have hE := ae_rank_E_fhn μ hdIn
  have hD := ae_rank_D_fhn μ hdOut
  -- the determinant of `I + σ'(0) W_read^ℓ W_write^ℓ` is a polynomial in the weights, equal to
  -- `1` at `θ = 0`, so it is nonzero at generic parameters
  have hU : ∀ᵐ θ ∂μ, ∀ ℓ, IsUnit (1 + deriv σ 0 • (θ.read ℓ * θ.write ℓ)).det := by
    refine ae_all_iff.2 fun ℓ => ?_
    have hentry : ∀ i j : d, AnalyticOnNhd ℝ
        (fun θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut =>
          (1 + deriv σ 0 • (θ.read ℓ * θ.write ℓ) : Matrix d d ℝ) i j) Set.univ := fun i j => by
      have h := analyticOnNhd_mul_apply
        (Params.linRead (A := Arch.mlp (T := T) (d := d) σ id hid) (dIn := dIn) (dOut := dOut) ℓ)
        (Params.linWrite (A := Arch.mlp (T := T) (d := d) σ id hid) (dIn := dIn) (dOut := dOut)
          ℓ) i j
      exact analyticOnNhd_const.fun_add (analyticOnNhd_const.mul h)
    have hg : AnalyticOnNhd ℝ
        (fun θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut =>
          (1 + deriv σ 0 • (θ.read ℓ * θ.write ℓ)).det) Set.univ := by
      simp only [Matrix.det_apply']
      exact Finset.analyticOnNhd_fun_sum _ fun τ _ => analyticOnNhd_const.mul
        (Finset.analyticOnNhd_fun_prod _ fun i _ => hentry (τ i) i)
    have h0 : (1 + deriv σ 0 •
        ((0 : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut).read ℓ *
          (0 : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut).write ℓ)).det ≠ 0 := by
      rw [Params.zero_read, Matrix.zero_mul, smul_zero, add_zero, Matrix.det_one]
      exact one_ne_zero
    filter_upwards [ae_ne_zero_of_analytic μ hg ⟨0, h0⟩] with θ hθ
    exact isUnit_iff_ne_zero.2 hθ
  -- the bound at one parameter
  filter_upwards [hE, hD, hU] with θ h1 h2 h3
  exact le_inputRank_residual_mlp_zero hσ0 hσ θ h1 h2 h3

/-- **Theorem A.28 (iii) of the skips paper, "If some `d'_hidden,ℓ < d_model` […] the two networks
differ", for MLP blocks whose activation has `σ(0) = 0` and is differentiable at `0`:** with
`d_in, d_out ≥ d` and at least one token, at generic parameters the residual network computes the
function of no network without skips, of any depth `L'` and with any differentiable blocks and
map `χ`, that has a block with fewer than `d` rows in its write (for an MLP block: fewer than `d`
hidden units). -/
theorem ae_forall_eval_residual_ne_skipless_of_card_lt [Nonempty T] (hσ0 : σ 0 = 0)
    (hσ : DifferentiableAt ℝ σ 0)
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, ∀ (L' : ℕ) (A' : Arch T d L'), (∀ ℓ, Differentiable ℝ (A'.f ℓ)) →
      Differentiable ℝ A'.χ → (∃ ℓ, Fintype.card (A'.w ℓ) < Fintype.card d) →
      ∀ η : Params A' dIn dOut, eval (Arch.mlp σ id hid) 1 θ ≠ eval A' 0 η := by
  filter_upwards [ae_le_inputRank_residual_mlp_zero hσ0 hσ μ hdIn hdOut] with θ hθ
  intro L' A' hf hχ hw η heq
  obtain ⟨ℓ, hℓ⟩ := hw
  -- equal functions have equal Jacobians at `0`
  have hrank : inputRank (Arch.mlp σ id hid) 1 θ 0 = inputRank A' 0 η 0 := by
    unfold inputRank
    rw [heq]
  -- `|T| d ≤ rank ≤ |T| |w_ℓ| < |T| d`
  have h1 := inputRank_skipless_le hf hχ η 0 ℓ
  have h2 : Fintype.card T * Fintype.card (A'.w ℓ) < Fintype.card T * Fintype.card d :=
    Nat.mul_lt_mul_of_pos_left hℓ Fintype.card_pos
  exact lt_irrefl _ ((hθ.trans (hrank.le.trans h1)).trans_lt h2)

/-- **Theorem A.28 (iii) of the skips paper, given Sard's theorem:** for GELU blocks without
normalization and `d_in, d_out ≥ d ≥ 2`, with at least one token, at generic parameters of the
residual network with the hidden units `hid ℓ`, for all widths `m_1, …, m_L` with
`2 ∑_ℓ m_ℓ < 2 ∑_ℓ d_hidden,ℓ + L d` ("in total, fewer than `L d_model / 2` more hidden units"),
no skipless network of GELU blocks of the widths `m` computes the function of the residual
network. (For widths `m_ℓ ≥ d` this is `ae_forall_widths_eval_residual_ne_skipless_gelu`; a
skipless network with some `m_ℓ < d` differs whatever its number of hidden units is.) -/
theorem ae_forall_all_widths_eval_residual_ne_skipless_gelu [Nonempty T]
    (hSard : ∀ (m : Fin L → ℕ) (r : ℕ), SardCriticalValues
      (Params (Arch.mlp (T := T) (d := d) gelu id (fun ℓ => Fin (m ℓ))) dIn dOut) (Fin r → ℝ))
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) gelu id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, ∀ m : Fin L → ℕ,
      2 * ∑ ℓ, m ℓ < 2 * ∑ ℓ, Fintype.card (hid ℓ) + L * Fintype.card d →
      ∀ η : Params (Arch.mlp (T := T) (d := d) gelu id (fun ℓ => Fin (m ℓ))) dIn dOut,
        eval (Arch.mlp gelu id hid) 1 θ ≠ eval (Arch.mlp gelu id (fun ℓ => Fin (m ℓ))) 0 η := by
  -- the two cases of the paper's proof: every width at least `d`, or some width below `d`
  have h1 := ae_forall_widths_eval_residual_ne_skipless_gelu (hid := hid) hSard μ hd hdIn hdOut
  have h2 := ae_forall_eval_residual_ne_skipless_of_card_lt (hid := hid)
    (show gelu 0 = 0 by rw [gelu, zero_mul]) (hasDerivAt_gelu 0).differentiableAt μ hdIn hdOut
  filter_upwards [h1, h2] with θ hθ1 hθ2 m hm η
  by_cases hw : ∀ ℓ, Fintype.card d ≤ m ℓ
  · exact hθ1 m hw hm η
  · obtain ⟨ℓ, hℓ⟩ := not_forall.mp hw
    exact hθ2 L (Arch.mlp gelu id (fun ℓ => Fin (m ℓ)))
      (fun ℓ => differentiableOn_univ.mp
        (analyticOnNhd_f_mlp analyticOnNhd_gelu ℓ).differentiableOn)
      differentiable_id
      ⟨ℓ, by show Fintype.card (Fin (m ℓ)) < Fintype.card d; simpa using hℓ⟩ η

end Skips
