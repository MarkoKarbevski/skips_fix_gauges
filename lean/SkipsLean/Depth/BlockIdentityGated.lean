import SkipsLean.Depth.StepTanhRMS
import SkipsLean.Depth.SuffixGated

/-!
# The identity for one gated block

Paper (dimension): Appendix D.5, "The identity for one GELU or gated block", equations (26) to
(30), for a gated block.

"Fix `k < L` and write `W_g = W_g^{k+1}`, with the columns `c_1, …, c_q`, `V = W_write^{k+1}`, with
the rows `a_1, …, a_q`, `ι = ι^{k+1}` and `𝓑 = 𝓑_{>k+1}`, and in a gated block `W_v = W_v^{k+1}`,
with the columns `e_1, …, e_q`. Let `Z` and `η = (η_g, η_v, η_V, η')` be as in `(D_k)` […]. For a
row `n` let `ñ = n Z` in the case (n) and `ñ = n Z − ⟨n Z, n⟩ n / d_model` in the case (+). For
rows `n` and `w̃, w̃' ∈ ℝ^{1×q}` let

  `ż^g(n) = ñ W_g + n η_g`,   `ż^v(n) = ñ W_v + n η_v` in a gated block,   (26)

  `𝓛(w̃, w̃'; n) = 𝐃𝓑(ŵ V) ((w̃' ⊙ ż^g(n) ⊙ ι(n) + w̃ ⊙ ż^v(n)) V + ŵ η_V) + 𝐃_θ 𝓑(ŵ V) η'`,   (27)

where `ŵ = w̃ ⊙ ι(n)` […]. By the chain rule and (14), the left side of (16) at `h` is
`𝓛(σ(n W_g), σ'(n W_g); n)` at `n = χ(h)`. As in Lemma D.6, (16) for `k` therefore holds if and only
if `𝓛(σ(n W_g), σ'(n W_g); n) = 0` for every row `n ∈ ℝ^{1×d_model}` (28). We use two properties of
`𝓛`. The row `w̃'` enters only through the terms `w̃'_j ż^g_j(n) ι_j(n) a_j`, so
`∂𝓛/∂w̃'_j (w̃, w̃'; n) = ż^g_j(n) ι_j(n) 𝐃𝓑(ŵ V) a_j` (29). And in a gated block `ż^g` and `ż^v` are
odd in `n`, while `ŵ` does not change when `w̃` and `n` both change their sign, so
`𝓛(−w̃, w̃'; −n) = 𝓛(w̃, w̃'; n)` in a gated block (30)."

In Lean the read of a gated block is `[W_g | W_v]` (gate column `Sum.inl j`, value column
`Sum.inr j`), so `n W_read` holds the gates `n W_g` and the values `ι(n) = n W_v`, and one matrix
`zdot = ñ W_read + n η_read` holds `ż^g(n)` and `ż^v(n)`. A hidden state has the rows `T`; the
paper's rows are the case of one token. `blockLHSGated` takes the matrices `n W_read` and `zdot`
as arguments in the place of `n`: (29) and (30) are then statements about these arguments.
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise Topology

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]
variable {σ σ' : ℝ → ℝ} {χ : Matrix T d ℝ → Matrix T d ℝ} {ε : ℝ}

/-- **The left side of the identity for one gated block,** equation (27) of the paper:
`𝓛 = 𝐃𝓑(ŵ V) ((w̃' ⊙ ż^g ⊙ ι + w̃ ⊙ ż^v) V + ŵ η_V) + 𝐃_θ 𝓑(ŵ V) η` with `ŵ = w̃ ⊙ ι`, for block `k`
with the write `V` and the network `𝓑` after it. Here `w` stands for the gates `w̃`, `w'` for their
derivatives `w̃'`, `z` for what the hidden units read (its value columns are `ι`), and `zdot` for
the derivative of what they read (its gate columns are `ż^g`, its value columns `ż^v`). (The network
after the block does not depend on the weights of the block, so `𝐃_θ 𝓑 η` is the paper's
`𝐃_θ 𝓑 η'`.) -/
noncomputable def blockLHSGated (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut)
    (k : Fin L) (η : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut)
    (w w' : Matrix T (hid k) ℝ) (z zdot : Matrix T (hid k ⊕ hid k) ℝ) : Matrix T dOut ℝ :=
  fderiv ℝ (fun h' : Matrix T d ℝ => suffix (Arch.gated σ χ hid) 0 θ k.succ h')
      ((Matrix.of fun t j => w t j * z t (Sum.inr j)) * θ.write k)
      ((Matrix.of fun t j =>
            w' t j * zdot t (Sum.inl j) * z t (Sum.inr j) + w t j * zdot t (Sum.inr j))
          * θ.write k
        + (Matrix.of fun t j => w t j * z t (Sum.inr j)) * η.write k)
    + fderiv ℝ (fun θ' : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut =>
        suffix (Arch.gated σ χ hid) 0 θ' k.succ
          ((Matrix.of fun t j => w t j * z t (Sum.inr j)) * θ.write k)) θ η

/-- **Equation (29), in additive form:** `𝓛` is affine in `w̃'`, and a change `x'` of `w̃'` changes
`𝓛` by `𝐃𝓑(ŵ V) ((x' ⊙ ż^g ⊙ ι) V)`. -/
theorem blockLHSGated_add_right
    (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut) (k : Fin L)
    (η : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut)
    (w w' x' : Matrix T (hid k) ℝ) (z zdot : Matrix T (hid k ⊕ hid k) ℝ) :
    blockLHSGated θ k η w (w' + x') z zdot
      = blockLHSGated θ k η w w' z zdot
        + fderiv ℝ (fun h' : Matrix T d ℝ => suffix (Arch.gated σ χ hid) 0 θ k.succ h')
            ((Matrix.of fun t j => w t j * z t (Sum.inr j)) * θ.write k)
            ((Matrix.of fun t j => x' t j * zdot t (Sum.inl j) * z t (Sum.inr j)) * θ.write k) := by
  -- the direction is affine in `w̃'`: split off the part `(x' ⊙ ż^g ⊙ ι) V`
  have hsplit : (Matrix.of fun t j =>
        (w' + x') t j * zdot t (Sum.inl j) * z t (Sum.inr j) + w t j * zdot t (Sum.inr j))
      = (Matrix.of fun t j =>
          w' t j * zdot t (Sum.inl j) * z t (Sum.inr j) + w t j * zdot t (Sum.inr j))
        + Matrix.of fun t j => x' t j * zdot t (Sum.inl j) * z t (Sum.inr j) := by
    ext t j
    simp only [Matrix.of_apply, Matrix.add_apply]
    ring
  unfold blockLHSGated
  -- `𝐃𝓑(ŵ V)` is linear
  rw [hsplit, Matrix.add_mul, add_right_comm _ _
    ((Matrix.of fun t j => w t j * z t (Sum.inr j)) * η.write k), map_add]
  abel

/-- **Equation (30):** `𝓛(−w̃, w̃'; −n) = 𝓛(w̃, w̃'; n)` in a gated block. -/
theorem blockLHSGated_neg
    (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut) (k : Fin L)
    (η : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut)
    (w w' : Matrix T (hid k) ℝ) (z zdot : Matrix T (hid k ⊕ hid k) ℝ) :
    blockLHSGated θ k η (-w) w' (-z) (-zdot) = blockLHSGated θ k η w w' z zdot := by
  -- `ŵ = w̃ ⊙ ι` does not change: `(−w)(−z) = w z`
  have hw : (Matrix.of fun t j => (-w) t j * (-z) t (Sum.inr j))
      = Matrix.of fun t j => w t j * z t (Sum.inr j) := by
    ext t j
    simp only [Matrix.of_apply, Matrix.neg_apply]
    ring
  -- nor does the direction: `w' (−ż)(−z) = w' ż z` and `(−w)(−ż) = w ż`
  have hdir : (Matrix.of fun t j =>
        w' t j * (-zdot) t (Sum.inl j) * (-z) t (Sum.inr j) + (-w) t j * (-zdot) t (Sum.inr j))
      = Matrix.of fun t j =>
          w' t j * zdot t (Sum.inl j) * z t (Sum.inr j) + w t j * zdot t (Sum.inr j) := by
    ext t j
    simp only [Matrix.of_apply, Matrix.neg_apply]
    ring
  unfold blockLHSGated
  rw [hw, hdir]

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the product rule for matrix-valued functions of one real variable (as in
`Depth/StepTanh.lean`). -/
private theorem hasDerivAt_matMulG {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
    {A : ℝ → Matrix m n ℝ} {B : ℝ → Matrix n p ℝ} {A' : Matrix m n ℝ} {B' : Matrix n p ℝ}
    {τ : ℝ} (hA : HasDerivAt A A' τ) (hB : HasDerivAt B B' τ) :
    HasDerivAt (fun s => A s * B s) (A' * B τ + A τ * B') τ := by
  refine hasDerivAt_pi.2 fun t => hasDerivAt_pi.2 fun i => ?_
  -- entry `(t, i)` is `∑_j A_{t j} B_{j i}`
  have h := HasDerivAt.fun_sum (u := Finset.univ) fun j _ =>
    (hasDerivAt_pi.1 (hasDerivAt_pi.1 hA t) j).mul (hasDerivAt_pi.1 (hasDerivAt_pi.1 hB j) i)
  simp only [Matrix.mul_apply, Matrix.add_apply, ← Finset.sum_add_distrib]
  exact h

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the derivative of the map of a gated block along a curve `s ↦ P(s)` of what its hidden
units read: entry `(t, i)` of `σ(P^g) ⊙ P^v` has the derivative `σ'(P^g) Ṗ^g P^v + σ(P^g) Ṗ^v`. -/
private theorem hasDerivAt_gatedMap {m n : Type*} [Fintype m] [Fintype n]
    (hσ : ∀ z, HasDerivAt σ (σ' z) z) {P : ℝ → Matrix m (n ⊕ n) ℝ} {P' : Matrix m (n ⊕ n) ℝ}
    {τ : ℝ} (hP : HasDerivAt P P' τ) :
    HasDerivAt (fun s => Matrix.of fun t i => σ (P s t (Sum.inl i)) * P s t (Sum.inr i))
      (Matrix.of fun t i => σ' (P τ t (Sum.inl i)) * P' t (Sum.inl i) * P τ t (Sum.inr i)
        + σ (P τ t (Sum.inl i)) * P' t (Sum.inr i)) τ :=
  hasDerivAt_pi.2 fun t => hasDerivAt_pi.2 fun i =>
    ((hσ (P τ t (Sum.inl i))).comp τ (hasDerivAt_pi.1 (hasDerivAt_pi.1 hP t) (Sum.inl i))).mul
      (hasDerivAt_pi.1 (hasDerivAt_pi.1 hP t) (Sum.inr i))

/-- Helper: for `Φ` differentiable at `(x, y)`, the derivatives of its two partial maps, along `b`
and `a`, add up to its derivative along `(a, b)` (as in `Depth/StepTanh.lean`). -/
private theorem fderiv_partial_addG {E₁ E₂ F : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
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

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the line `τ ↦ a + τ b` has the velocity `b` (as in `Depth/StepTanh.lean`). -/
private theorem hasDerivAt_lineG {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (a b : E) :
    HasDerivAt (fun τ : ℝ => a + τ • b) b 0 := by
  have h := ((hasDerivAt_id (0 : ℝ)).smul_const b).const_add a
  rw [one_smul] at h
  exact h

/-- **The identity for one gated block, case (n)** (equation (28), by the chain rule): for a gated
block whose gate `σ` has the derivative `σ'`, the identity (16) for the hidden state before block
`k` holds for `Z` and `η` if and only if `𝓛(σ(n W_g), σ'(n W_g); n) = 0` for all `n`, with
`ż(n) = n (Z W_read + η_read)` (equation (26), case (n)). -/
theorem suffixFlat_castSucc_iff_gated (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) (k : Fin L)
    (Z : Matrix d d ℝ) (η : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) :
    SuffixFlat (Arch.gated σ id hid) θ k.castSucc Z η ↔
      ∀ n : Matrix T d ℝ,
        blockLHSGated θ k η (Matrix.of fun t j => σ ((n * θ.read k) t (Sum.inl j)))
          (Matrix.of fun t j => σ' ((n * θ.read k) t (Sum.inl j)))
          (n * θ.read k) (n * (Z * θ.read k + η.read k)) = 0 := by
  -- the blocks are differentiable, hence so are `(θ', h') ↦ 𝓑_{>k+1}(h')` and `𝓑_{>k}(h')`
  have hfd : ∀ ℓ, Differentiable ℝ ((Arch.gated (T := T) (d := d) σ id hid).f ℓ) :=
    differentiable_f_gated fun z => (hσ z).differentiableAt
  have hΦ := differentiable_suffix_prod (Arch.gated (T := T) (d := d) σ id hid) (dIn := dIn)
    (dOut := dOut) rfl hfd k.succ
  have hΨ := differentiable_suffix_prod (Arch.gated (T := T) (d := d) σ id hid) (dIn := dIn)
    (dOut := dOut) rfl hfd k.castSucc
  -- it suffices that the two left sides agree at every `h`
  suffices key : ∀ h : Matrix T d ℝ,
      fderiv ℝ (fun h' : Matrix T d ℝ => suffix (Arch.gated σ id hid) 0 θ k.castSucc h') h (h * Z)
        + fderiv ℝ (fun θ' : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut =>
            suffix (Arch.gated σ id hid) 0 θ' k.castSucc h) θ η
      = blockLHSGated θ k η (Matrix.of fun t j => σ ((h * θ.read k) t (Sum.inl j)))
          (Matrix.of fun t j => σ' ((h * θ.read k) t (Sum.inl j)))
          (h * θ.read k) (h * (Z * θ.read k + η.read k)) by
    exact forall_congr' fun h => by rw [key h]
  intro h
  -- the block along the line `τ ↦ (θ + τ η, h + τ h Z)`, entrywise: the derivative of entry
  -- `(t, j)` of the hidden units is `σ'(z^g) ż^g z^v + σ(z^g) ż^v`
  have hg := hasDerivAt_matMulG (hasDerivAt_gatedMap hσ (hasDerivAt_matMulG
    (hasDerivAt_lineG h (h * Z)) (hasDerivAt_lineG (θ.read k) (η.read k))))
    (hasDerivAt_lineG (θ.write k) (η.write k))
  simp only [zero_smul, add_zero] at hg
  rw [show h * Z * θ.read k + h * η.read k = h * (Z * θ.read k + η.read k) by
    rw [Matrix.mul_add, Matrix.mul_assoc]] at hg
  -- the derivative of `τ ↦ 𝓑_{>k}(h + τ h Z)` (with the weights `θ + τ η`) at `0`, directly ...
  have e1 : HasDerivAt
      (fun τ : ℝ => suffix (Arch.gated σ id hid) 0 (θ + τ • η) k.castSucc (h + τ • (h * Z)))
      (fderiv ℝ (fun p : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut × Matrix T d ℝ =>
        suffix (Arch.gated σ id hid) 0 p.1 k.castSucc p.2) (θ, h) (η, h * Z)) 0 := by
    have hc := (hΨ (θ, h)).hasFDerivAt.comp_hasDerivAt_of_eq 0
      ((hasDerivAt_lineG θ η).prodMk (hasDerivAt_lineG h (h * Z))) (by simp)
    exact hc
  -- ... and through the block: `𝓑_{>k}(h') = 𝓑_{>k+1}((σ(h' W_g) ⊙ h' W_v) V)`
  have e2 : HasDerivAt
      (fun τ : ℝ => suffix (Arch.gated σ id hid) 0 (θ + τ • η) k.castSucc (h + τ • (h * Z)))
      (fderiv ℝ (fun p : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut × Matrix T d ℝ =>
        suffix (Arch.gated σ id hid) 0 p.1 k.succ p.2)
        (θ, (Matrix.of fun t j => σ ((h * θ.read k) t (Sum.inl j)) * (h * θ.read k) t (Sum.inr j))
          * θ.write k)
        (η, (Matrix.of fun t j => σ' ((h * θ.read k) t (Sum.inl j))
              * (h * (Z * θ.read k + η.read k)) t (Sum.inl j) * (h * θ.read k) t (Sum.inr j)
            + σ ((h * θ.read k) t (Sum.inl j)) * (h * (Z * θ.read k + η.read k)) t (Sum.inr j))
            * θ.write k
          + (Matrix.of fun t j => σ ((h * θ.read k) t (Sum.inl j)) * (h * θ.read k) t (Sum.inr j))
            * η.write k)) 0 := by
    have hc := (hΦ (θ, (Matrix.of fun t j => σ ((h * θ.read k) t (Sum.inl j))
        * (h * θ.read k) t (Sum.inr j)) * θ.write k)).hasFDerivAt.comp_hasDerivAt_of_eq
      0 ((hasDerivAt_lineG θ η).prodMk hg) (by simp)
    have hfun : (fun τ : ℝ =>
        suffix (Arch.gated σ id hid) 0 (θ + τ • η) k.castSucc (h + τ • (h * Z)))
        = (fun p : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut × Matrix T d ℝ =>
            suffix (Arch.gated σ id hid) 0 p.1 k.succ p.2) ∘ fun τ : ℝ =>
          (θ + τ • η, (Matrix.of fun t i =>
              σ (((h + τ • (h * Z)) * (θ.read k + τ • η.read k)) t (Sum.inl i))
                * ((h + τ • (h * Z)) * (θ.read k + τ • η.read k)) t (Sum.inr i))
            * (θ.write k + τ • η.write k)) := by
      funext τ
      simp only [Function.comp_apply, suffix_castSucc, Pi.zero_apply, Matrix.mul_zero, zero_add]
      rfl
    rw [hfun]
    exact hc
  -- both sides are derivatives of the joint maps `(θ', h') ↦ 𝓑(h')` along `(η, ·)`
  unfold blockLHSGated
  simp only [Matrix.of_apply]
  calc _ = _ := fderiv_partial_addG
        (Φ := fun θ' h' => suffix (Arch.gated (T := T) (d := d) σ id hid) 0 θ' k.castSucc h')
        (hΨ (θ, h)) η (h * Z)
    _ = _ := e1.unique e2
    _ = _ := (fderiv_partial_addG
        (Φ := fun θ' h' => suffix (Arch.gated (T := T) (d := d) σ id hid) 0 θ' k.succ h')
        (hΦ _) η _).symm

omit [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: equation (14) along the line `τ ↦ h + τ h Z` (as in `Depth/StepTanhRMS.lean`). -/
private theorem hasDerivAt_rmsNorm_lineG (hε : 0 < ε) (Z : Matrix d d ℝ) (h : Matrix T d ℝ) :
    HasDerivAt (fun τ : ℝ => rmsNorm ε (h + τ • (h * Z))) (tangentRMS Z (rmsNorm ε h)) 0 := by
  classical
  rw [← fderiv_rmsNorm_mul hε Z h]
  have hc := (differentiable_rmsNorm (T := T) (d := d) hε h).hasFDerivAt.comp_hasDerivAt_of_eq
    (0 : ℝ) (hasDerivAt_lineG h (h * Z)) (by rw [zero_smul, add_zero])
  exact hc

/-- Helper: **the identity for one gated block at the values of `N_ε`** (equation (28) by the chain
rule and (14)): the identity (16) before block `k` holds if and only if
`𝓛(σ(n W_g), σ'(n W_g); n) = 0` at every value `n = N_ε(h)`, with
`ż(n) = (n Z − ⟨n Z, n⟩ n / d) W_read + n η_read`. -/
private theorem suffixFlat_castSucc_iff_gated_rmsNorm_valuesG (hε : 0 < ε)
    (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (θ : Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut) (k : Fin L)
    (Z : Matrix d d ℝ) (η : Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut) :
    SuffixFlat (Arch.gated σ (rmsNorm ε) hid) θ k.castSucc Z η ↔
      ∀ h : Matrix T d ℝ,
        blockLHSGated θ k η (Matrix.of fun t j => σ ((rmsNorm ε h * θ.read k) t (Sum.inl j)))
          (Matrix.of fun t j => σ' ((rmsNorm ε h * θ.read k) t (Sum.inl j)))
          (rmsNorm ε h * θ.read k)
          (tangentRMS Z (rmsNorm ε h) * θ.read k + rmsNorm ε h * η.read k) = 0 := by
  -- `N_ε` and the blocks are differentiable, hence so are `(θ', h') ↦ 𝓑_{>k+1}(h')` and
  -- `𝓑_{>k}(h')`
  have hfd : ∀ ℓ, Differentiable ℝ ((Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid).f ℓ) :=
    differentiable_f_gated fun z => (hσ z).differentiableAt
  have hχd : Differentiable ℝ (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid).χ :=
    differentiable_rmsNorm hε
  have hΦ := differentiable_suffix_prod_of_differentiable
    (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) (dIn := dIn) (dOut := dOut) hχd hfd k.succ
  have hΨ := differentiable_suffix_prod_of_differentiable
    (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) (dIn := dIn) (dOut := dOut) hχd hfd
    k.castSucc
  -- it suffices that the two left sides agree at every `h`
  suffices key : ∀ h : Matrix T d ℝ,
      fderiv ℝ (fun h' : Matrix T d ℝ => suffix (Arch.gated σ (rmsNorm ε) hid) 0 θ k.castSucc h')
          h (h * Z)
        + fderiv ℝ (fun θ' : Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut =>
            suffix (Arch.gated σ (rmsNorm ε) hid) 0 θ' k.castSucc h) θ η
      = blockLHSGated θ k η (Matrix.of fun t j => σ ((rmsNorm ε h * θ.read k) t (Sum.inl j)))
          (Matrix.of fun t j => σ' ((rmsNorm ε h * θ.read k) t (Sum.inl j)))
          (rmsNorm ε h * θ.read k)
          (tangentRMS Z (rmsNorm ε h) * θ.read k + rmsNorm ε h * η.read k) by
    exact forall_congr' fun h => by rw [key h]
  intro h
  -- the block along the line `τ ↦ (θ + τ η, h + τ h Z)`, entrywise, with (14)
  have hg := hasDerivAt_matMulG (hasDerivAt_gatedMap hσ (hasDerivAt_matMulG
    (hasDerivAt_rmsNorm_lineG hε Z h) (hasDerivAt_lineG (θ.read k) (η.read k))))
    (hasDerivAt_lineG (θ.write k) (η.write k))
  simp only [zero_smul, add_zero] at hg
  -- the derivative of `τ ↦ 𝓑_{>k}(h + τ h Z)` (with the weights `θ + τ η`) at `0`, directly ...
  have e1 : HasDerivAt
      (fun τ : ℝ => suffix (Arch.gated σ (rmsNorm ε) hid) 0 (θ + τ • η) k.castSucc
        (h + τ • (h * Z)))
      (fderiv ℝ (fun p : Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut
          × Matrix T d ℝ => suffix (Arch.gated σ (rmsNorm ε) hid) 0 p.1 k.castSucc p.2) (θ, h)
        (η, h * Z)) 0 := by
    have hc := (hΨ (θ, h)).hasFDerivAt.comp_hasDerivAt_of_eq 0
      ((hasDerivAt_lineG θ η).prodMk (hasDerivAt_lineG h (h * Z))) (by simp)
    exact hc
  -- ... and through the block: `𝓑_{>k}(h') = 𝓑_{>k+1}((σ(n W_g) ⊙ n W_v) V)` at `n = N_ε(h')`
  have e2 : HasDerivAt
      (fun τ : ℝ => suffix (Arch.gated σ (rmsNorm ε) hid) 0 (θ + τ • η) k.castSucc
        (h + τ • (h * Z)))
      (fderiv ℝ (fun p : Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut
          × Matrix T d ℝ => suffix (Arch.gated σ (rmsNorm ε) hid) 0 p.1 k.succ p.2)
        (θ, (Matrix.of fun t j => σ ((rmsNorm ε h * θ.read k) t (Sum.inl j))
            * (rmsNorm ε h * θ.read k) t (Sum.inr j)) * θ.write k)
        (η, (Matrix.of fun t j => σ' ((rmsNorm ε h * θ.read k) t (Sum.inl j))
              * (tangentRMS Z (rmsNorm ε h) * θ.read k + rmsNorm ε h * η.read k) t (Sum.inl j)
              * (rmsNorm ε h * θ.read k) t (Sum.inr j)
            + σ ((rmsNorm ε h * θ.read k) t (Sum.inl j))
              * (tangentRMS Z (rmsNorm ε h) * θ.read k + rmsNorm ε h * η.read k) t (Sum.inr j))
            * θ.write k
          + (Matrix.of fun t j => σ ((rmsNorm ε h * θ.read k) t (Sum.inl j))
            * (rmsNorm ε h * θ.read k) t (Sum.inr j)) * η.write k)) 0 := by
    have hc := (hΦ (θ, (Matrix.of fun t j => σ ((rmsNorm ε h * θ.read k) t (Sum.inl j))
        * (rmsNorm ε h * θ.read k) t (Sum.inr j)) * θ.write k)).hasFDerivAt.comp_hasDerivAt_of_eq
      0 ((hasDerivAt_lineG θ η).prodMk hg) (by simp)
    have hfun : (fun τ : ℝ =>
        suffix (Arch.gated σ (rmsNorm ε) hid) 0 (θ + τ • η) k.castSucc (h + τ • (h * Z)))
        = (fun p : Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut
            × Matrix T d ℝ => suffix (Arch.gated σ (rmsNorm ε) hid) 0 p.1 k.succ p.2) ∘
          fun τ : ℝ => (θ + τ • η, (Matrix.of fun t i =>
              σ ((rmsNorm ε (h + τ • (h * Z)) * (θ.read k + τ • η.read k)) t (Sum.inl i))
                * (rmsNorm ε (h + τ • (h * Z)) * (θ.read k + τ • η.read k)) t (Sum.inr i))
            * (θ.write k + τ • η.write k)) := by
      funext τ
      simp only [Function.comp_apply, suffix_castSucc, Pi.zero_apply, Matrix.mul_zero, zero_add]
      rfl
    rw [hfun]
    exact hc
  -- both sides are derivatives of the joint maps `(θ', h') ↦ 𝓑(h')` along `(η, ·)`
  unfold blockLHSGated
  simp only [Matrix.of_apply]
  calc _ = _ := fderiv_partial_addG
        (Φ := fun θ' h' =>
          suffix (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) 0 θ' k.castSucc h')
        (hΨ (θ, h)) η (h * Z)
    _ = _ := e1.unique e2
    _ = _ := (fderiv_partial_addG
        (Φ := fun θ' h' => suffix (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) 0 θ' k.succ h')
        (hΦ _) η _).symm

omit [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: `y ↦ y M`, as a continuous linear map (as in `Depth/StepTanhRMS.lean`). -/
private noncomputable def mulRightCLMG {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
    (M : Matrix n p ℝ) : Matrix m n ℝ →L[ℝ] Matrix m p ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun y => y * M
      map_add' := fun a b => Matrix.add_mul a b M
      map_smul' := fun c a => Matrix.smul_mul c a M }

/-- Helper: an analytic family of continuous linear maps, applied to an analytic family of vectors,
is analytic (as in `Depth/StepTanhRMS.lean`). -/
private theorem analyticOnNhd_clm_applyG {X E F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {J : X → E →L[ℝ] F} {v : X → E} {s : Set X} (hJ : AnalyticOnNhd ℝ J s)
    (hv : AnalyticOnNhd ℝ v s) : AnalyticOnNhd ℝ (fun x => J x (v x)) s :=
  fun x hx => ((ContinuousLinearMap.id ℝ (E →L[ℝ] F)).analyticAt_bilinear (J x, v x)).comp₂
    (hJ x hx) (hv x hx)

omit [DecidableEq d] in
/-- Helper: `n ↦ n Z - ⟨n Z, n⟩ n / d` (equation (14)) is a polynomial in the entries of `n`, hence
analytic (as in `Depth/StepTanhRMS.lean`). -/
private theorem analyticOnNhd_tangentRMSG (Z : Matrix d d ℝ) :
    AnalyticOnNhd ℝ (tangentRMS (T := T) Z) Set.univ := by
  have hZ : ∀ t i, AnalyticOnNhd ℝ (fun n : Matrix T d ℝ => (n * Z) t i) Set.univ := fun t i =>
    (analyticOnNhd_matrix_entry t i).comp ((mulRightCLMG (m := T) Z).analyticOnNhd Set.univ)
      (Set.mapsTo_univ _ _)
  show AnalyticOnNhd ℝ (fun n : Matrix T d ℝ => fun t i =>
    (n * Z) t i - ((n * Z) t ⬝ᵥ n t / (Fintype.card d : ℝ)) * n t i) Set.univ
  refine AnalyticOnNhd.pi fun t => AnalyticOnNhd.pi fun i =>
    (hZ t i).sub (AnalyticOnNhd.mul ?_ (analyticOnNhd_matrix_entry t i))
  show AnalyticOnNhd ℝ
    (fun n : Matrix T d ℝ => (∑ l, (n * Z) t l * n t l) / (Fintype.card d : ℝ)) Set.univ
  exact (Finset.analyticOnNhd_fun_sum _ fun l _ =>
    (hZ t l).mul (analyticOnNhd_matrix_entry t l)).div_const

/-- **The identity for one gated block, case (+)** (equation (28); as in Lemma D.6): for a
real-analytic gate, under pre-RMSNorm with `ε > 0`, the identity (16) before block `k` holds if and
only if `𝓛(σ(n W_g), σ'(n W_g); n) = 0` for every `n`, with
`ż(n) = (n Z − ⟨n Z, n⟩ n / d) W_read + n η_read` (equation (26), case (+)): the left side is
real-analytic in `n`, and the values of `N_ε` form an open set. -/
theorem suffixFlat_castSucc_iff_gated_rmsNorm (hε : 0 < ε) (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (θ : Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut) (k : Fin L)
    (Z : Matrix d d ℝ) (η : Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut) :
    SuffixFlat (Arch.gated σ (rmsNorm ε) hid) θ k.castSucc Z η ↔
      ∀ n : Matrix T d ℝ,
        blockLHSGated θ k η (Matrix.of fun t j => σ ((n * θ.read k) t (Sum.inl j)))
          (Matrix.of fun t j => σ' ((n * θ.read k) t (Sum.inl j)))
          (n * θ.read k) (tangentRMS Z n * θ.read k + n * η.read k) = 0 := by
  rw [suffixFlat_castSucc_iff_gated_rmsNorm_valuesG hε hσ θ k Z η]
  refine ⟨fun hval => ?_, fun hG h => hG (rmsNorm ε h)⟩
  -- the left side `G(n)` of (28), as a function of the row `n`
  let G : Matrix T d ℝ → Matrix T dOut ℝ := fun n =>
    blockLHSGated θ k η (Matrix.of fun t j => σ ((n * θ.read k) t (Sum.inl j)))
      (Matrix.of fun t j => σ' ((n * θ.read k) t (Sum.inl j)))
      (n * θ.read k) (tangentRMS Z n * θ.read k + n * η.read k)
  -- `σ' = deriv σ` is analytic, `N_ε` and the blocks are analytic, hence so is
  -- `(θ', h') ↦ 𝓑_{>k+1}(h')`
  have hσ'a : AnalyticOnNhd ℝ σ' Set.univ := by
    rw [show σ' = deriv σ from funext fun z => (hσ z).deriv.symm]
    exact hσa.deriv
  have hf : ∀ ℓ, AnalyticOnNhd ℝ ((Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid).f ℓ)
      Set.univ := fun ℓ => analyticOnNhd_f_gated hσa ℓ
  have hΦ := analyticOnNhd_suffix_prod_of_analytic
    (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) (dIn := dIn) (dOut := dOut)
    (analyticOnNhd_rmsNorm hε) hf k.succ
  -- the entries of `n W_read` and of `ż(n)` are analytic in `n`
  have hnW : ∀ t c, AnalyticOnNhd ℝ (fun n : Matrix T d ℝ => (n * θ.read k) t c) Set.univ :=
    fun t c => (analyticOnNhd_matrix_entry t c).comp
      ((mulRightCLMG (m := T) (θ.read k)).analyticOnNhd Set.univ) (Set.mapsTo_univ _ _)
  have hzdot : AnalyticOnNhd ℝ
      (fun n : Matrix T d ℝ => tangentRMS Z n * θ.read k + n * η.read k) Set.univ :=
    (analyticOnNhd_matrix_mul (analyticOnNhd_tangentRMSG Z) analyticOnNhd_const).add
      ((mulRightCLMG (m := T) (η.read k)).analyticOnNhd Set.univ)
  have hzd : ∀ t c, AnalyticOnNhd ℝ
      (fun n : Matrix T d ℝ => (tangentRMS Z n * θ.read k + n * η.read k) t c) Set.univ :=
    fun t c => (analyticOnNhd_matrix_entry t c).comp hzdot (Set.mapsTo_univ _ _)
  -- the point `ŵ = σ(n W_g) ⊙ n W_v` and the direction
  -- `(σ'(n W_g) ⊙ ż^g ⊙ n W_v + σ(n W_g) ⊙ ż^v) V + ŵ η_V` are analytic in `n`
  have hw : AnalyticOnNhd ℝ (fun n : Matrix T d ℝ => Matrix.of fun t j =>
      σ ((n * θ.read k) t (Sum.inl j)) * (n * θ.read k) t (Sum.inr j)) Set.univ := by
    show AnalyticOnNhd ℝ (fun n : Matrix T d ℝ => fun t j =>
      σ ((n * θ.read k) t (Sum.inl j)) * (n * θ.read k) t (Sum.inr j)) Set.univ
    exact AnalyticOnNhd.pi fun t => AnalyticOnNhd.pi fun j =>
      (hσa.comp (hnW t (Sum.inl j)) (Set.mapsTo_univ _ _)).mul (hnW t (Sum.inr j))
  have hdir : AnalyticOnNhd ℝ (fun n : Matrix T d ℝ =>
      (Matrix.of fun t j => σ' ((n * θ.read k) t (Sum.inl j))
          * (tangentRMS Z n * θ.read k + n * η.read k) t (Sum.inl j) * (n * θ.read k) t (Sum.inr j)
        + σ ((n * θ.read k) t (Sum.inl j))
          * (tangentRMS Z n * θ.read k + n * η.read k) t (Sum.inr j)) * θ.write k
      + (Matrix.of fun t j => σ ((n * θ.read k) t (Sum.inl j)) * (n * θ.read k) t (Sum.inr j))
        * η.write k) Set.univ := by
    refine (analyticOnNhd_matrix_mul ?_ analyticOnNhd_const).add
      (analyticOnNhd_matrix_mul hw analyticOnNhd_const)
    show AnalyticOnNhd ℝ (fun n : Matrix T d ℝ => fun t j => σ' ((n * θ.read k) t (Sum.inl j))
          * (tangentRMS Z n * θ.read k + n * η.read k) t (Sum.inl j) * (n * θ.read k) t (Sum.inr j)
        + σ ((n * θ.read k) t (Sum.inl j))
          * (tangentRMS Z n * θ.read k + n * η.read k) t (Sum.inr j)) Set.univ
    exact AnalyticOnNhd.pi fun t => AnalyticOnNhd.pi fun j =>
      (((hσ'a.comp (hnW t (Sum.inl j)) (Set.mapsTo_univ _ _)).mul (hzd t (Sum.inl j))).mul
        (hnW t (Sum.inr j))).add
      ((hσa.comp (hnW t (Sum.inl j)) (Set.mapsTo_univ _ _)).mul (hzd t (Sum.inr j)))
  -- `G(n)` is the derivative of `(θ', h') ↦ 𝓑_{>k+1}(h')` at `(θ, ŵ V)` along `(η, ·)`
  have hGeq : G = fun n => fderiv ℝ
      (fun p : Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut × Matrix T d ℝ =>
        suffix (Arch.gated σ (rmsNorm ε) hid) 0 p.1 k.succ p.2)
      (θ, (Matrix.of fun t j => σ ((n * θ.read k) t (Sum.inl j)) * (n * θ.read k) t (Sum.inr j))
        * θ.write k)
      (η, (Matrix.of fun t j => σ' ((n * θ.read k) t (Sum.inl j))
          * (tangentRMS Z n * θ.read k + n * η.read k) t (Sum.inl j) * (n * θ.read k) t (Sum.inr j)
        + σ ((n * θ.read k) t (Sum.inl j))
          * (tangentRMS Z n * θ.read k + n * η.read k) t (Sum.inr j)) * θ.write k
      + (Matrix.of fun t j => σ ((n * θ.read k) t (Sum.inl j)) * (n * θ.read k) t (Sum.inr j))
        * η.write k) := by
    funext n
    simp only [G, blockLHSGated, Matrix.of_apply]
    exact fderiv_partial_addG
      (Φ := fun θ' h' => suffix (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) 0 θ' k.succ h')
      (hΦ _ (Set.mem_univ _)).differentiableAt η _
  -- so `G` is analytic on the whole space
  have hG : AnalyticOnNhd ℝ G Set.univ := by
    rw [hGeq]
    exact analyticOnNhd_clm_applyG (hΦ.fderiv.comp (analyticOnNhd_const.prod
        (analyticOnNhd_matrix_mul hw analyticOnNhd_const)) (Set.mapsTo_univ _ _))
      (analyticOnNhd_const.prod hdir)
  -- `G` vanishes on the values of `N_ε`, an open set (`N_ε` is an open map)
  have hUo : IsOpen (Set.range (rmsNorm ε : Matrix T d ℝ → Matrix T d ℝ)) :=
    (isOpenMap_rmsNorm hε).isOpen_range
  have hzero : G =ᶠ[𝓝 (rmsNorm ε 0)] 0 :=
    Filter.eventually_of_mem (hUo.mem_nhds (Set.mem_range_self 0)) fun n hn => by
      obtain ⟨h, rfl⟩ := hn
      exact hval h
  -- the identity principle on the (connected) whole space
  intro n
  exact hG.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
    (Set.mem_univ (rmsNorm ε 0)) hzero (Set.mem_univ n)

end Skips
