import SkipsLean.Dimension.UpperBound
import SkipsLean.Dimension.UpperBoundRMSNorm
import SkipsLean.Dimension.Rescaling
import SkipsLean.Dimension.GenericRank
import SkipsLean.Generic.Params
import SkipsLean.Generic.Gated
import SkipsLean.Activations.Analytic
import SkipsLean.Depth.SuffixRMS

/-!
# Skipless networks: the changes of basis at the first and at the last hidden state

Paper (skips paper): proof of Theorem A.28 (i) and (ii). "In a skipless network of the same
widths, with embedding `E'` and readout `D'`, the changes of basis at `h_0` and `h_L`, those inside
the heads and the rescalings have orbits of dimension `2 d² + s` at generic parameters, where `E'`
and `D'` have rank `d` […]. Under pre-RMSNorm with `ε > 0` […] the orthogonal changes of basis at
`h_0` and `h_L`, which commute with the normalization, have orbits of dimension `d (d - 1) + s` in
the skipless network." And the proof of Lemma A.26: "So the Jacobian of `G_X` has rank at most
`r₀ = P' - k`; the rank is lower semicontinuous, so the bound holds at every `η`."

Here: a skipless network of `L ≥ 1` blocks of ANY widths (a block may have fewer than `d` hidden
units, so the changes of basis at the hidden states in between are not used). The directions are
`cobDir θ X` with `X` supported on the first and the last hidden state, and `rescaleDir θ α` for
gated blocks (`s` = the number of gated units; `s = 0` for MLP blocks such as `tanh` and GELU).

* `funDim_add_le_skipless_ends…`: the bound on the functional dimension where `E` and `D` have
  rank `d` (and, for gated blocks, no value column of a read vanishes).
* `jacobianRank_add_le_skipless_ends…`: the same bound for the rank of the Jacobian on every batch
  at EVERY parameter, for real-analytic blocks.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]

/-! ### Helpers: cancellation, the families supported on `h_0` and `h_L`, generic ranks -/

/-- Helper (the private `mul_left_cancel_of_rank` of `UpperBound.lean`): a matrix `M` of rank equal
to its number of columns cancels on the left, `M X = M Y → X = Y`. -/
private theorem mul_left_cancel_of_rank_se {m n k : Type*} [Fintype n] (M : Matrix m n ℝ)
    (hM : M.rank = Fintype.card n) {X Y : Matrix n k ℝ} (h : M * X = M * Y) : X = Y := by
  -- `v ↦ M v` is injective: `rank M + dim ker M = card n`
  have hinj : Function.Injective M.mulVecLin := by
    rw [← LinearMap.ker_eq_bot, ← Submodule.finrank_eq_zero]
    have := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
    rw [Module.finrank_fintype_fun_eq_card] at this
    rw [Matrix.rank] at hM
    omega
  -- compare `X` and `Y` column by column
  ext i j
  have hcol : M.mulVecLin (fun l => X l j) = M.mulVecLin (fun l => Y l j) := by
    funext p
    have := congrFun (congrFun h p) j
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
  exact congrFun (hinj hcol) i

/-- Helper: a matrix `M` of rank equal to its number of rows cancels on the right,
`X M = Y M → X = Y` (transpose, and `rank Mᵀ = rank M`). -/
private theorem mul_right_cancel_of_rank_se {m n k : Type*} [Fintype m] [Fintype n]
    (M : Matrix m n ℝ) (hM : M.rank = Fintype.card m) {X Y : Matrix k m ℝ} (h : X * M = Y * M) :
    X = Y := by
  have hT : Mᵀ * Xᵀ = Mᵀ * Yᵀ := by
    rw [← Matrix.transpose_mul, h, Matrix.transpose_mul]
  exact Matrix.transpose_injective
    (mul_left_cancel_of_rank_se Mᵀ (by rw [Matrix.rank_transpose]; exact hM) hT)

omit [Fintype d] [DecidableEq d] in
/-- Helper: the family `X` with `X_0 = p.1`, `X_L = p.2` and `X_ℓ = 0` at the hidden states in
between, as a linear map of `p = (X_0, X_L)`. -/
private noncomputable def endsLin_se (n : ℕ) :
    (Matrix d d ℝ × Matrix d d ℝ) →ₗ[ℝ] (Fin (n + 1) → Matrix d d ℝ) :=
  (LinearMap.single ℝ (fun _ : Fin (n + 1) => Matrix d d ℝ) 0).coprod
    (LinearMap.single ℝ (fun _ : Fin (n + 1) => Matrix d d ℝ) (Fin.last n))

omit [Fintype d] [DecidableEq d] in
/-- Helper: `0 ≠ L` as hidden states, for `L ≥ 1`. -/
private theorem zero_ne_last_se {n : ℕ} (hn : 0 < n) : (0 : Fin (n + 1)) ≠ Fin.last n := by
  rw [Ne, Fin.ext_iff, Fin.val_zero, Fin.val_last]
  omega

omit [Fintype d] [DecidableEq d] in
/-- Helper: the family `endsLin_se n p` at `h_0` is `p.1`. -/
private theorem endsLin_zero_se {n : ℕ} (hn : 0 < n) (p : Matrix d d ℝ × Matrix d d ℝ) :
    endsLin_se n p 0 = p.1 := by
  simp [endsLin_se, zero_ne_last_se hn]

omit [Fintype d] [DecidableEq d] in
/-- Helper: the family `endsLin_se n p` at `h_L` is `p.2`. -/
private theorem endsLin_last_se {n : ℕ} (hn : 0 < n) (p : Matrix d d ℝ × Matrix d d ℝ) :
    endsLin_se n p (Fin.last n) = p.2 := by
  simp [endsLin_se, (zero_ne_last_se hn).symm]

omit [DecidableEq d] in
/-- Helper: for antisymmetric `X_0`, `X_L`, every matrix of the family `endsLin_se n (X_0, X_L)` is
antisymmetric. -/
private theorem endsLin_mem_antisymmetric_se (n : ℕ) {a b : Matrix d d ℝ}
    (ha : a ∈ antisymmetric d) (hb : b ∈ antisymmetric d) (ℓ : Fin (n + 1)) :
    endsLin_se n (a, b) ℓ ∈ antisymmetric d := by
  simp only [endsLin_se, LinearMap.coprod_apply, LinearMap.coe_single, Pi.add_apply]
  refine Submodule.add_mem _ ?_ ?_
  · rw [Pi.single_apply]
    split_ifs
    · exact ha
    · exact Submodule.zero_mem _
  · rw [Pi.single_apply]
    split_ifs
    · exact hb
    · exact Submodule.zero_mem _

omit [Fintype T] [DecidableEq d] [Fintype dIn] in
/-- Helper: the embedding component `E X_0` determines `X_0` and the readout component `-X_L D`
determines `X_L`, when `E` and `D` have rank `d` (`L ≥ 1`, so `h_0 ≠ h_L`). -/
private theorem ends_eq_se {n : ℕ} (hn : 0 < n) {E : Matrix dIn d ℝ} {D : Matrix d dOut ℝ}
    (hE : E.rank = Fintype.card d) (hD : D.rank = Fintype.card d)
    {p q : Matrix d d ℝ × Matrix d d ℝ}
    (h0 : E * endsLin_se n p 0 = E * endsLin_se n q 0)
    (h1 : -(endsLin_se n p (Fin.last n) * D) = -(endsLin_se n q (Fin.last n) * D)) : p = q := by
  rw [endsLin_zero_se hn, endsLin_zero_se hn] at h0
  rw [endsLin_last_se hn, endsLin_last_se hn, neg_inj] at h1
  exact Prod.ext (mul_left_cancel_of_rank_se E hE h0) (mul_right_cancel_of_rank_se D hD h1)

omit [DecidableEq d] in
/-- Helper: the pairs `(X_0, X_L)` form a space of dimension `2 d²`. -/
private theorem finrank_ends_se :
    Module.finrank ℝ (Matrix d d ℝ × Matrix d d ℝ) = 2 * Fintype.card d ^ 2 := by
  rw [Module.finrank_prod, Module.finrank_matrix, Module.finrank_self]
  ring

/-- Helper: the pairs `(X_0, X_L)` of antisymmetric matrices form a space of dimension
`2 · d (d - 1) / 2 = d (d - 1)` (`d (d - 1)` is even). -/
private theorem finrank_ends_antisymmetric_se :
    Module.finrank ℝ (antisymmetric d × antisymmetric d)
      = Fintype.card d * (Fintype.card d - 1) := by
  rw [Module.finrank_prod, finrank_antisymmetric]
  have h := Nat.div_two_mul_two_of_even (Nat.even_mul_pred_self (Fintype.card d))
  generalize Fintype.card d * (Fintype.card d - 1) = k at h ⊢
  omega

omit [Fintype T] in
/-- Helper (the private `rank_eq_of_isUnit_det_submatrix` of `Generic/Params.lean`): a matrix with
`d` columns has rank `d` if some `d` of its rows form an invertible matrix. -/
private theorem rank_eq_of_isUnit_det_rows_se {m : Type*} (M : Matrix m d ℝ) (ρ : d ↪ m)
    (h : IsUnit (M.submatrix ρ id).det) : M.rank = Fintype.card d :=
  le_antisymm (Matrix.rank_le_card_width M)
    ((Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).2 h)).symm.le.trans
      (Matrix.rank_submatrix_le M ρ id))

/-- Helper: at generic parameters `E` and `D` have rank `d`, when `d_in ≥ d` and `d_out ≥ d`. -/
private theorem ae_rank_E_D_se {A : Arch T d L} (μ : Measure (Params A dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, θ.E.rank = Fintype.card d ∧ θ.D.rank = Fintype.card d := by
  -- `d` rows of `E` and `d` columns of `D`, invertible at generic parameters
  obtain ⟨ρ⟩ := Function.Embedding.nonempty_of_card_le hdIn
  obtain ⟨c⟩ := Function.Embedding.nonempty_of_card_le hdOut
  filter_upwards [ae_isUnit_det_submatrix μ] with θ hθ
  exact ⟨rank_eq_of_isUnit_det_rows_se θ.E ρ (hθ.2.2.1 ρ),
    rank_eq_card_of_isUnit_det θ.D c (hθ.2.1 c)⟩

omit [DecidableEq d] in
/-- Helper (the proof of Lemma A.26: "the rank is lower semicontinuous, so the bound holds at every
`η`"): for real-analytic `f_ℓ` and `χ`, a bound `fd(θ') + k ≤ P` at almost every `θ'` gives the
bound `rank J_X(θ) + k ≤ P` on every batch `X` at every `θ`. -/
private theorem jacobianRank_add_le_of_ae_se {A : Arch T d L}
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (hχ : AnalyticOnNhd ℝ A.χ Set.univ) {k : ℕ}
    (θ : Params A dIn dOut) {n : ℕ} (X : Fin n → Matrix T dIn ℝ)
    (h : ∀ᵐ θ' ∂(Measure.addHaar : Measure (Params A dIn dOut)),
      funDim A 0 θ' + k ≤ Module.finrank ℝ (Params A dIn dOut)) :
    jacobianRank A 0 X θ + k ≤ Module.finrank ℝ (Params A dIn dOut) := by
  -- a parameter `θ'` with `rank J_X(θ) ≤ fd(θ')` and `fd(θ') + k ≤ P`
  obtain ⟨θ', h1, h2⟩ :=
    ((ae_jacobianRank_le_funDim A 0 hf hχ Measure.addHaar X θ).and h).exists
  omega

section General

variable {A : Arch T d L}

/-- **Proof of Theorem A.28 (ii) of the skips paper, "the changes of basis at `h_0` and `h_L`",
without normalization:** for a skipless network of `L ≥ 1` blocks of any widths whose `E` and `D`
have rank `d`, the functional dimension is at most `P - 2 d²`. -/
theorem funDim_add_le_skipless_ends (hA : A.χ = id) (hf : ∀ ℓ, Differentiable ℝ (A.f ℓ))
    (hL : 0 < L) (θ : Params A dIn dOut) (hE : θ.E.rank = Fintype.card d)
    (hD : θ.D.rank = Fintype.card d) :
    funDim A 0 θ + 2 * Fintype.card d ^ 2 ≤ Module.finrank ℝ (Params A dIn dOut) := by
  -- the directions `cobDir θ X`, `X` supported on `h_0` and `h_L`: the range of `Φ`
  let Φ : (Matrix d d ℝ × Matrix d d ℝ) →ₗ[ℝ] Params A dIn dOut :=
    (cobDirLin θ).comp (endsLin_se L)
  -- they are flat (Proposition 3.2, without normalization)
  have hV : LinearMap.range Φ ≤ flat A 0 θ := by
    rintro _ ⟨p, rfl⟩
    exact cobDir_mem_flat_skipless θ hA hf (endsLin_se L p)
  -- `Φ` is injective: `E X_0` determines `X_0`, and `-X_L D` determines `X_L`
  have hinj : Function.Injective Φ := by
    intro p q h
    have h' : cobDir θ (endsLin_se L p) = cobDir θ (endsLin_se L q) := h
    exact ends_eq_se hL hE hD (congrArg Params.E h') (congrArg Params.D h')
  -- so they span a space of dimension `2 d²`
  have h := funDim_add_finrank_le_of_le_flat' θ _ hV
  rwa [LinearMap.finrank_range_of_inj hinj, finrank_ends_se] at h

/-- **The same bound at every parameter, on every batch** (proof of Lemma A.26: "the rank is lower
semicontinuous, so the bound holds at every `η`"): for real-analytic blocks, `d_in, d_out ≥ d` and
`L ≥ 1`, the Jacobian of the outputs of a skipless network on a batch has rank at most `P - 2 d²`
at every parameter. -/
theorem jacobianRank_add_le_skipless_ends (hA : A.χ = id)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (hL : 0 < L)
    (hdIn : Fintype.card d ≤ Fintype.card dIn) (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (θ : Params A dIn dOut) {n : ℕ} (X : Fin n → Matrix T dIn ℝ) :
    jacobianRank A 0 X θ + 2 * Fintype.card d ^ 2 ≤ Module.finrank ℝ (Params A dIn dOut) := by
  -- at almost every `θ'`, `E` and `D` have rank `d`, so `fd(θ') + 2 d² ≤ P`
  refine jacobianRank_add_le_of_ae_se hf (by rw [hA]; exact analyticOnNhd_id) θ X ?_
  filter_upwards [ae_rank_E_D_se Measure.addHaar hdIn hdOut] with θ' h
  exact funDim_add_le_skipless_ends hA (fun ℓ => differentiableOn_univ.1 (hf ℓ).differentiableOn)
    hL θ' h.1 h.2

/-- **Proof of Theorem A.28 (ii), "the orthogonal changes of basis at `h_0` and `h_L`", under
pre-RMSNorm with `ε > 0`:** for a skipless network of `L ≥ 1` blocks of any widths whose `E` and
`D` have rank `d`, the functional dimension is at most `P - d (d - 1)`. -/
theorem funDim_add_le_skipless_ends_rmsNorm {ε : ℝ} (hε : 0 < ε) (hA : A.χ = rmsNorm ε)
    (hf : ∀ ℓ, Differentiable ℝ (A.f ℓ)) (hL : 0 < L) (θ : Params A dIn dOut)
    (hE : θ.E.rank = Fintype.card d) (hD : θ.D.rank = Fintype.card d) :
    funDim A 0 θ + Fintype.card d * (Fintype.card d - 1)
      ≤ Module.finrank ℝ (Params A dIn dOut) := by
  -- the directions `cobDir θ X`, `X` supported on `h_0` and `h_L` and antisymmetric there
  let Φ : (antisymmetric d × antisymmetric d) →ₗ[ℝ] Params A dIn dOut :=
    ((cobDirLin θ).comp (endsLin_se L)).comp
      ((antisymmetric d).subtype.prodMap (antisymmetric d).subtype)
  -- they are flat (Proposition 3.2 under pre-RMSNorm: orthogonal changes of basis)
  have hV : LinearMap.range Φ ≤ flat A 0 θ := by
    rintro _ ⟨p, rfl⟩
    exact cobDir_mem_flat_skipless_rmsNorm θ hε hA hf
      (endsLin_se L ((p.1 : Matrix d d ℝ), (p.2 : Matrix d d ℝ)))
      fun ℓ => endsLin_mem_antisymmetric_se L p.1.2 p.2.2 ℓ
  -- `Φ` is injective: `E X_0` determines `X_0`, and `-X_L D` determines `X_L`
  have hinj : Function.Injective Φ := by
    intro p q h
    have h' : cobDir θ (endsLin_se L ((p.1 : Matrix d d ℝ), (p.2 : Matrix d d ℝ)))
        = cobDir θ (endsLin_se L ((q.1 : Matrix d d ℝ), (q.2 : Matrix d d ℝ))) := h
    have h2 : ((p.1 : Matrix d d ℝ), (p.2 : Matrix d d ℝ))
        = ((q.1 : Matrix d d ℝ), (q.2 : Matrix d d ℝ)) :=
      ends_eq_se hL hE hD (congrArg Params.E h') (congrArg Params.D h')
    exact Prod.ext (Subtype.ext (congrArg Prod.fst h2)) (Subtype.ext (congrArg Prod.snd h2))
  -- so they span a space of dimension `d (d - 1)`
  have h := funDim_add_finrank_le_of_le_flat' θ _ hV
  rwa [LinearMap.finrank_range_of_inj hinj, finrank_ends_antisymmetric_se] at h

/-- **The same bound at every parameter, on every batch, under pre-RMSNorm with `ε > 0`:** for
real-analytic blocks, `d_in, d_out ≥ d` and `L ≥ 1`, the Jacobian of the outputs of a skipless
network on a batch has rank at most `P - d (d - 1)` at every parameter. -/
theorem jacobianRank_add_le_skipless_ends_rmsNorm {ε : ℝ} (hε : 0 < ε) (hA : A.χ = rmsNorm ε)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (hL : 0 < L)
    (hdIn : Fintype.card d ≤ Fintype.card dIn) (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (θ : Params A dIn dOut) {n : ℕ} (X : Fin n → Matrix T dIn ℝ) :
    jacobianRank A 0 X θ + Fintype.card d * (Fintype.card d - 1)
      ≤ Module.finrank ℝ (Params A dIn dOut) := by
  -- at almost every `θ'`, `E` and `D` have rank `d`, so `fd(θ') + d (d - 1) ≤ P`
  refine jacobianRank_add_le_of_ae_se hf (by rw [hA]; exact analyticOnNhd_rmsNorm hε) θ X ?_
  filter_upwards [ae_rank_E_D_se Measure.addHaar hdIn hdOut] with θ' h
  exact funDim_add_le_skipless_ends_rmsNorm hε hA
    (fun ℓ => differentiableOn_univ.1 (hf ℓ).differentiableOn) hL θ' h.1 h.2

end General

section Gated

variable {σ : ℝ → ℝ} {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]


omit [Fintype T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (the private `rescaleDirLin` of `Rescaling.lean`): `α ↦ rescaleDir θ α` is linear. -/
private noncomputable def rescaleDirLin_se {χ : Matrix T d ℝ → Matrix T d ℝ}
    (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut) :
    (∀ ℓ, hid ℓ → ℝ) →ₗ[ℝ] Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut where
  toFun := rescaleDir θ
  map_add' α β := by
    apply Params.ext'
    · simp [rescaleDir]
    · intro ℓ
      ext k j
      cases j with
      | inl i => simp [rescaleDir]
      | inr i =>
        simp only [rescaleDir, Pi.add_apply, Params.add_read, Matrix.add_apply, Matrix.of_apply,
          Sum.elim_inr]
        ring
    · intro ℓ
      ext i k
      simp [rescaleDir, add_mul]
    · simp [rescaleDir]
  map_smul' c α := by
    apply Params.ext'
    · simp [rescaleDir]
    · intro ℓ
      ext k j
      cases j <;> simp [rescaleDir, mul_assoc]
    · intro ℓ
      ext i k
      simp [rescaleDir, mul_assoc]
    · simp [rescaleDir]

omit [Fintype T] [DecidableEq d] [Fintype dIn] in
/-- Helper (Lemma B.1 for gated blocks, with `X` supported on `h_0` and `h_L`): the direction
`cobDir θ X + rescaleDir θ α` determines `(X_0, X_L)` and `α`, when `E` and `D` have rank `d` and no
value column of a read vanishes. -/
private theorem ends_rescale_inj_se {χ : Matrix T d ℝ → Matrix T d ℝ}
    (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut) (hL : 0 < L)
    (hE : θ.E.rank = Fintype.card d) (hD : θ.D.rank = Fintype.card d)
    (hv : ∀ ℓ i, (fun k => θ.read ℓ k (Sum.inr i)) ≠ 0)
    {p q : Matrix d d ℝ × Matrix d d ℝ} {α β : ∀ ℓ, hid ℓ → ℝ}
    (h : cobDir θ (endsLin_se L p) + rescaleDir θ α = cobDir θ (endsLin_se L q) + rescaleDir θ β) :
    p = q ∧ α = β := by
  -- the embedding and readout components: the rescalings leave `E` and `D` alone
  have hpq : p = q := by
    refine ends_eq_se hL hE hD ?_ ?_
    · have h0 := congrArg Params.E h
      change θ.E * endsLin_se L p 0 + 0 = θ.E * endsLin_se L q 0 + 0 at h0
      rwa [add_zero, add_zero] at h0
    · have h1 := congrArg Params.D h
      change -(endsLin_se L p (Fin.last L) * θ.D) + 0
        = -(endsLin_se L q (Fin.last L) * θ.D) + 0 at h1
      rwa [add_zero, add_zero] at h1
  subst hpq
  refine ⟨rfl, funext fun ℓ => funext fun i => ?_⟩
  -- the value column `e_i` of hidden unit `i` of block `ℓ` moves by `-X_{ℓ-1} e_i - α_i e_i`, and
  -- the first terms agree; an entry `k` with `e_i k ≠ 0` gives `α_i = β_i`
  obtain ⟨k, hk⟩ := Function.ne_iff.mp (hv ℓ i)
  have hr := congrFun (congrFun (congrArg (fun η => η.read ℓ) h) k) (Sum.inr i)
  change -(endsLin_se L p ℓ.castSucc * θ.read ℓ) k (Sum.inr i) + -(α ℓ i) * θ.read ℓ k (Sum.inr i) =
    -(endsLin_se L p ℓ.castSucc * θ.read ℓ) k (Sum.inr i) + -(β ℓ i) * θ.read ℓ k (Sum.inr i) at hr
  rw [add_right_inj] at hr
  exact neg_inj.mp (mul_right_cancel₀ hk hr)

omit [Fintype T] [Fintype dIn] [Fintype dOut] [DecidableEq d] in
/-- Helper: the triples `(X_0, X_L, α)` form a space of dimension `2 d² + s`. -/
private theorem finrank_ends_rescale_se :
    Module.finrank ℝ ((Matrix d d ℝ × Matrix d d ℝ) × (∀ ℓ, hid ℓ → ℝ))
      = 2 * Fintype.card d ^ 2 + ∑ ℓ, Fintype.card (hid ℓ) := by
  rw [Module.finrank_prod, finrank_ends_se, Module.finrank_pi_fintype]
  simp only [Module.finrank_fintype_fun_eq_card]

omit [Fintype T] [Fintype dIn] [Fintype dOut] in
/-- Helper: the triples `(X_0, X_L, α)` with antisymmetric `X_0`, `X_L` form a space of dimension
`d (d - 1) + s`. -/
private theorem finrank_ends_antisymmetric_rescale_se :
    Module.finrank ℝ ((antisymmetric d × antisymmetric d) × (∀ ℓ, hid ℓ → ℝ))
      = Fintype.card d * (Fintype.card d - 1) + ∑ ℓ, Fintype.card (hid ℓ) := by
  rw [Module.finrank_prod, finrank_ends_antisymmetric_se, Module.finrank_pi_fintype]
  simp only [Module.finrank_fintype_fun_eq_card]

/-- **Proof of Theorem A.28 (ii), "the changes of basis at `h_0` and `h_L` […] and the
rescalings", for gated blocks without normalization:** for a skipless network of `L ≥ 1` gated
blocks of any widths whose `E` and `D` have rank `d` and whose reads have no vanishing value
column, the functional dimension is at most `P - 2 d² - s`, with `s` the number of hidden
units. -/
theorem funDim_add_le_skipless_ends_gated
    (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) (hσ : Differentiable ℝ σ)
    (hL : 0 < L) (hE : θ.E.rank = Fintype.card d) (hD : θ.D.rank = Fintype.card d)
    (hv : ∀ ℓ i, (fun k => θ.read ℓ k (Sum.inr i)) ≠ 0) :
    funDim (Arch.gated σ id hid) 0 θ + (2 * Fintype.card d ^ 2 + ∑ ℓ, Fintype.card (hid ℓ))
      ≤ Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) := by
  -- the directions `cobDir θ X + rescaleDir θ α`, `X` supported on `h_0` and `h_L`
  let Φ : ((Matrix d d ℝ × Matrix d d ℝ) × (∀ ℓ, hid ℓ → ℝ)) →ₗ[ℝ]
      Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut :=
    ((cobDirLin θ).comp (endsLin_se L)).coprod (rescaleDirLin_se θ)
  -- they are flat, since both summands are
  have hV : LinearMap.range Φ ≤ flat (Arch.gated σ id hid) 0 θ := by
    rintro _ ⟨p, rfl⟩
    rw [LinearMap.coprod_apply]
    exact Submodule.add_mem _
      (cobDir_mem_flat_skipless θ rfl (differentiable_f_gated hσ) (endsLin_se L p.1))
      (rescaleDir_mem_flat θ hσ p.2)
  -- `Φ` is injective (Lemma B.1 with `X` supported on `h_0` and `h_L`)
  have hinj : Function.Injective Φ := by
    rintro ⟨p, α⟩ ⟨q, β⟩ h
    have h' : cobDir θ (endsLin_se L p) + rescaleDir θ α
        = cobDir θ (endsLin_se L q) + rescaleDir θ β := h
    obtain ⟨h1, h2⟩ := ends_rescale_inj_se θ hL hE hD hv h'
    rw [h1, h2]
  -- so they span a space of dimension `2 d² + s`
  have h := funDim_add_finrank_le_of_le_flat' θ _ hV
  rwa [LinearMap.finrank_range_of_inj hinj, finrank_ends_rescale_se] at h

/-- **The same bound at every parameter, on every batch, for gated blocks without
normalization:** for a real-analytic gate, `d_in, d_out ≥ d ≥ 1` and `L ≥ 1`, the Jacobian of the
outputs of a skipless network of gated blocks on a batch has rank at most `P - 2 d² - s` at every
parameter. -/
theorem jacobianRank_add_le_skipless_ends_gated [Nonempty d] (hσ : AnalyticOnNhd ℝ σ Set.univ)
    (hL : 0 < L) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) {n : ℕ}
    (X : Fin n → Matrix T dIn ℝ) :
    jacobianRank (Arch.gated σ id hid) 0 X θ
        + (2 * Fintype.card d ^ 2 + ∑ ℓ, Fintype.card (hid ℓ))
      ≤ Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) := by
  -- at almost every `θ'`, `E` and `D` have rank `d` and no value column vanishes
  refine jacobianRank_add_le_of_ae_se (fun ℓ => analyticOnNhd_f_gated hσ ℓ) analyticOnNhd_id θ X ?_
  filter_upwards [ae_rank_E_D_se Measure.addHaar hdIn hdOut, ae_value_ne_zero Measure.addHaar]
    with θ' h hv
  exact funDim_add_le_skipless_ends_gated θ' (differentiableOn_univ.1 hσ.differentiableOn) hL
    h.1 h.2 hv

/-- **For gated blocks under pre-RMSNorm with `ε > 0`:** for a skipless network of `L ≥ 1` gated
blocks of any widths whose `E` and `D` have rank `d` and whose reads have no vanishing value
column, the functional dimension is at most `P - d (d - 1) - s`. -/
theorem funDim_add_le_skipless_ends_gated_rmsNorm {ε : ℝ} (hε : 0 < ε)
    (θ : Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)
    (hσ : Differentiable ℝ σ) (hL : 0 < L) (hE : θ.E.rank = Fintype.card d)
    (hD : θ.D.rank = Fintype.card d) (hv : ∀ ℓ i, (fun k => θ.read ℓ k (Sum.inr i)) ≠ 0) :
    funDim (Arch.gated σ (rmsNorm ε) hid) 0 θ
        + (Fintype.card d * (Fintype.card d - 1) + ∑ ℓ, Fintype.card (hid ℓ))
      ≤ Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut) := by
  -- the directions `cobDir θ X + rescaleDir θ α`, `X` supported on `h_0` and `h_L` and
  -- antisymmetric there
  let Φ : ((antisymmetric d × antisymmetric d) × (∀ ℓ, hid ℓ → ℝ)) →ₗ[ℝ]
      Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut :=
    (((cobDirLin θ).comp (endsLin_se L)).comp
        ((antisymmetric d).subtype.prodMap (antisymmetric d).subtype)).coprod
      (rescaleDirLin_se θ)
  -- they are flat, since both summands are
  have hV : LinearMap.range Φ ≤ flat (Arch.gated σ (rmsNorm ε) hid) 0 θ := by
    rintro _ ⟨p, rfl⟩
    rw [LinearMap.coprod_apply]
    exact Submodule.add_mem _
      (cobDir_mem_flat_skipless_rmsNorm θ hε rfl (differentiable_f_gated hσ)
        (endsLin_se L ((p.1.1 : Matrix d d ℝ), (p.1.2 : Matrix d d ℝ)))
        fun ℓ => endsLin_mem_antisymmetric_se L p.1.1.2 p.1.2.2 ℓ)
      (rescaleDir_mem_flat_of_differentiable θ hσ (differentiable_rmsNorm hε) p.2)
  -- `Φ` is injective (Lemma B.1 with `X` supported on `h_0` and `h_L`)
  have hinj : Function.Injective Φ := by
    rintro ⟨p, α⟩ ⟨q, β⟩ h
    have h' : cobDir θ (endsLin_se L ((p.1 : Matrix d d ℝ), (p.2 : Matrix d d ℝ)))
          + rescaleDir θ α
        = cobDir θ (endsLin_se L ((q.1 : Matrix d d ℝ), (q.2 : Matrix d d ℝ)))
          + rescaleDir θ β := h
    obtain ⟨h1, h2⟩ := ends_rescale_inj_se θ hL hE hD hv h'
    exact Prod.ext (Prod.ext (Subtype.ext (congrArg Prod.fst h1))
      (Subtype.ext (congrArg Prod.snd h1))) h2
  -- so they span a space of dimension `d (d - 1) + s`
  have h := funDim_add_finrank_le_of_le_flat' θ _ hV
  rwa [LinearMap.finrank_range_of_inj hinj, finrank_ends_antisymmetric_rescale_se] at h

/-- **The same bound at every parameter, on every batch, for gated blocks under pre-RMSNorm with
`ε > 0`:** for a real-analytic gate, `d_in, d_out ≥ d ≥ 1` and `L ≥ 1`, the Jacobian of the outputs
of a skipless network of gated blocks on a batch has rank at most `P - d (d - 1) - s` at every
parameter. -/
theorem jacobianRank_add_le_skipless_ends_gated_rmsNorm [Nonempty d] {ε : ℝ} (hε : 0 < ε)
    (hσ : AnalyticOnNhd ℝ σ Set.univ) (hL : 0 < L) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (θ : Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut) {n : ℕ}
    (X : Fin n → Matrix T dIn ℝ) :
    jacobianRank (Arch.gated σ (rmsNorm ε) hid) 0 X θ
        + (Fintype.card d * (Fintype.card d - 1) + ∑ ℓ, Fintype.card (hid ℓ))
      ≤ Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut) := by
  -- at almost every `θ'`, `E` and `D` have rank `d` and no value column vanishes
  refine jacobianRank_add_le_of_ae_se (fun ℓ => analyticOnNhd_f_gated hσ ℓ)
    (analyticOnNhd_rmsNorm hε) θ X ?_
  filter_upwards [ae_rank_E_D_se Measure.addHaar hdIn hdOut, ae_value_ne_zero Measure.addHaar]
    with θ' h hv
  exact funDim_add_le_skipless_ends_gated_rmsNorm hε θ'
    (differentiableOn_univ.1 hσ.differentiableOn) hL h.1 h.2 hv

end Gated

end Skips
