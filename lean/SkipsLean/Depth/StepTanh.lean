import SkipsLean.Depth.Suffix
import SkipsLean.Depth.RaySeparation
import SkipsLean.Network.Analytic
import SkipsLean.OneBlock.Tanh

/-!
# The step from `(D_{k+1})` to `(D_k)` for a `tanh` block, without normalization

Paper (dimension paper): Appendix D.3, "The identity for one block" (equations (20) to (22)), and
Appendix D.4, Lemma D.7 (`lem:sbsteptanh`, "The step for tanh on rays"), in the case (n).

Fix a block, with the read `W` (columns `c_j`) and the write `V` (rows `a_j`), and let `𝓑` be the
network after this block. For a matrix `Z` and a direction `η` of the parameters, with `η_W` and
`η_V` its entries at `W` and `V`, the paper sets

  `𝓛(w̃, w̃'; n) = 𝐃𝓑(w̃ V) ((w̃' ⊙ ż(n)) V + w̃ η_V) + 𝐃_θ 𝓑(w̃ V) η`,   `ż(n) = n Z W + n η_W`,

and the identity (16) for the hidden state before the block is `𝓛(σ(n W), σ'(n W); n) = 0` for all
`n` (the chain rule). For `σ = tanh` and `n = t ξ` this is `t 𝒯_1(w̃) + 𝒯_0(w̃) = 0` at
`w̃ = tanh(t ξ W)`, and Lemma D.1 makes the outputs `w̃` of the hidden units free variables.

Conditions on the block: (T1) no row of `V` vanishes; (T2) the columns of `W` are linearly
independent over `ℚ`.

Numbering: the paper's blocks are `1, …, L` and its hidden states `h_0, …, h_L`. Here the blocks
are `k : Fin L`, the paper's block `k + 1`; the hidden state before it is `k.castSucc` (the paper's
`h_k`) and the one after it `k.succ` (the paper's `h_{k+1}`). As everywhere in this library a
hidden state has the rows `T`; the paper takes one token, and a row `ξ` of the paper is here a
matrix `Ξ` with one row per token.
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise Topology

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]
variable {σ σ' : ℝ → ℝ} {χ : Matrix T d ℝ → Matrix T d ℝ}

/-- **The left side of the identity for one block,** equation (21) of the paper:
`𝓛 = 𝐃𝓑(w̃ V) ((w̃' ⊙ ż) V + w̃ η_V) + 𝐃_θ 𝓑(w̃ V) η`, for block `k` with the write `V` and the
network `𝓑` after it (for any map `χ` before the reads of the later blocks). Here `w` stands for
the outputs `w̃` of the hidden units, `w'` for their
derivatives `w̃'`, and `zdot` for `ż`, the derivative of what the hidden units read. (The network
after the block does not depend on the weights of the block, so `𝐃_θ 𝓑 η` is the paper's
`𝐃_θ 𝓑 η'`.) -/
noncomputable def blockLHS (θ : Params (Arch.mlp (T := T) (d := d) σ χ hid) dIn dOut)
    (k : Fin L) (η : Params (Arch.mlp (T := T) (d := d) σ χ hid) dIn dOut)
    (w w' zdot : Matrix T (hid k) ℝ) : Matrix T dOut ℝ :=
  fderiv ℝ (fun h' : Matrix T d ℝ => suffix (Arch.mlp σ χ hid) 0 θ k.succ h') (w * θ.write k)
      ((Matrix.of fun t j => w' t j * zdot t j) * θ.write k + w * η.write k)
    + fderiv ℝ (fun θ' : Params (Arch.mlp (T := T) (d := d) σ χ hid) dIn dOut =>
        suffix (Arch.mlp σ χ hid) 0 θ' k.succ (w * θ.write k)) θ η

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the product rule for matrix-valued functions of one real variable. -/
private theorem hasDerivAt_matMul {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
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
/-- Helper: the derivative of `s ↦ σ(P(s))`, with `σ` applied to every entry of the matrix `P(s)`. -/
private theorem hasDerivAt_matrix_map {m n : Type*} [Fintype m] [Fintype n]
    (hσ : ∀ z, HasDerivAt σ (σ' z) z) {P : ℝ → Matrix m n ℝ} {P' : Matrix m n ℝ} {τ : ℝ}
    (hP : HasDerivAt P P' τ) :
    HasDerivAt (fun s => (P s).map σ) (Matrix.of fun t j => σ' (P τ t j) * P' t j) τ :=
  hasDerivAt_pi.2 fun t => hasDerivAt_pi.2 fun j =>
    (hσ (P τ t j)).comp τ (hasDerivAt_pi.1 (hasDerivAt_pi.1 hP t) j)

/-- Helper: for `Φ` differentiable at `(x, y)`, the derivatives of its two partial maps, along `b`
and `a`, add up to its derivative along `(a, b)`. -/
private theorem fderiv_partial_add {E₁ E₂ F : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
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
/-- Helper: the line `τ ↦ a + τ b` has the velocity `b`. -/
private theorem hasDerivAt_line {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (a b : E) :
    HasDerivAt (fun τ : ℝ => a + τ • b) b 0 := by
  have h := ((hasDerivAt_id (0 : ℝ)).smul_const b).const_add a
  rw [one_smul] at h
  exact h

/-- **The identity for one block, case (n)** (equation (22) of the paper, by the chain rule): for
an MLP block whose activation `σ` has the derivative `σ'`, the identity (16) for the hidden state
before block `k` holds for `Z` and `η` if and only if `𝓛(σ(n W), σ'(n W); n) = 0` for all `n`, with
`ż(n) = n (Z W + η_W)` (equation (20), case (n)). -/
theorem suffixFlat_castSucc_iff_mlp (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) (k : Fin L)
    (Z : Matrix d d ℝ) (η : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) :
    SuffixFlat (Arch.mlp σ id hid) θ k.castSucc Z η ↔
      ∀ n : Matrix T d ℝ,
        blockLHS θ k η ((n * θ.read k).map σ) ((n * θ.read k).map σ')
          (n * (Z * θ.read k + η.read k)) = 0 := by
  -- the blocks are differentiable, hence so are `(θ', h') ↦ 𝓑_{>k+1}(h')` and `𝓑_{>k}(h')`
  have hfd : ∀ ℓ, Differentiable ℝ ((Arch.mlp (T := T) (d := d) σ id hid).f ℓ) :=
    differentiable_f_mlp fun z => (hσ z).differentiableAt
  have hΦ := differentiable_suffix_prod (Arch.mlp (T := T) (d := d) σ id hid) (dIn := dIn)
    (dOut := dOut) rfl hfd k.succ
  have hΨ := differentiable_suffix_prod (Arch.mlp (T := T) (d := d) σ id hid) (dIn := dIn)
    (dOut := dOut) rfl hfd k.castSucc
  -- it suffices that the two left sides agree at every `h`
  suffices key : ∀ h : Matrix T d ℝ,
      fderiv ℝ (fun h' : Matrix T d ℝ => suffix (Arch.mlp σ id hid) 0 θ k.castSucc h') h (h * Z)
        + fderiv ℝ (fun θ' : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut =>
            suffix (Arch.mlp σ id hid) 0 θ' k.castSucc h) θ η
      = blockLHS θ k η ((h * θ.read k).map σ) ((h * θ.read k).map σ')
          (h * (Z * θ.read k + η.read k)) by
    exact forall_congr' fun h => by rw [key h]
  intro h
  -- the block along the line `τ ↦ (θ + τ η, h + τ h Z)`, entrywise: equation (22)
  have hg := hasDerivAt_matMul (hasDerivAt_matrix_map hσ (hasDerivAt_matMul
    (hasDerivAt_line h (h * Z)) (hasDerivAt_line (θ.read k) (η.read k))))
    (hasDerivAt_line (θ.write k) (η.write k))
  simp only [zero_smul, add_zero] at hg
  -- the derivative of `τ ↦ 𝓑_{>k}(h + τ h Z)` (with the weights `θ + τ η`) at `0`, directly ...
  have e1 : HasDerivAt
      (fun τ : ℝ => suffix (Arch.mlp σ id hid) 0 (θ + τ • η) k.castSucc (h + τ • (h * Z)))
      (fderiv ℝ (fun p : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut × Matrix T d ℝ =>
        suffix (Arch.mlp σ id hid) 0 p.1 k.castSucc p.2) (θ, h) (η, h * Z)) 0 := by
    have hc := (hΨ (θ, h)).hasFDerivAt.comp_hasDerivAt_of_eq 0
      ((hasDerivAt_line θ η).prodMk (hasDerivAt_line h (h * Z))) (by simp)
    exact hc
  -- ... and through the block: `𝓑_{>k}(h') = 𝓑_{>k+1}(σ(h' W) V)`
  have e2 : HasDerivAt
      (fun τ : ℝ => suffix (Arch.mlp σ id hid) 0 (θ + τ • η) k.castSucc (h + τ • (h * Z)))
      (fderiv ℝ (fun p : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut × Matrix T d ℝ =>
        suffix (Arch.mlp σ id hid) 0 p.1 k.succ p.2) (θ, (h * θ.read k).map σ * θ.write k)
        (η, (Matrix.of fun t j => σ' ((h * θ.read k) t j)
            * (h * Z * θ.read k + h * η.read k) t j) * θ.write k
          + (h * θ.read k).map σ * η.write k)) 0 := by
    have hc := (hΦ (θ, (h * θ.read k).map σ * θ.write k)).hasFDerivAt.comp_hasDerivAt_of_eq 0
      ((hasDerivAt_line θ η).prodMk hg) (by simp)
    have hfun : (fun τ : ℝ =>
        suffix (Arch.mlp σ id hid) 0 (θ + τ • η) k.castSucc (h + τ • (h * Z)))
        = (fun p : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut × Matrix T d ℝ =>
            suffix (Arch.mlp σ id hid) 0 p.1 k.succ p.2) ∘ fun τ : ℝ =>
          (θ + τ • η, ((h + τ • (h * Z)) * (θ.read k + τ • η.read k)).map σ
            * (θ.write k + τ • η.write k)) := by
      funext τ
      simp only [Function.comp_apply, suffix_castSucc, Pi.zero_apply, Matrix.mul_zero, zero_add]
      rfl
    rw [hfun]
    exact hc
  -- the direction of `blockLHS` is the derivative of the block
  have hX : (Matrix.of fun t j =>
      ((h * θ.read k).map σ') t j * (h * (Z * θ.read k + η.read k)) t j)
      = Matrix.of fun t j => σ' ((h * θ.read k) t j) * (h * Z * θ.read k + h * η.read k) t j := by
    ext t j
    simp only [Matrix.of_apply, Matrix.map_apply, Matrix.mul_add, Matrix.mul_assoc]
  unfold blockLHS
  rw [hX]
  -- both sides are derivatives of the joint maps `(θ', h') ↦ 𝓑(h')` along `(η, ·)`
  calc _ = _ := fderiv_partial_add
        (Φ := fun θ' h' => suffix (Arch.mlp (T := T) (d := d) σ id hid) 0 θ' k.castSucc h')
        (hΨ (θ, h)) η (h * Z)
    _ = _ := e1.unique e2
    _ = _ := (fderiv_partial_add
        (Φ := fun θ' h' => suffix (Arch.mlp (T := T) (d := d) σ id hid) 0 θ' k.succ h')
        (hΦ _) η _).symm

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the set where a nonzero additive and homogeneous function `f` does not vanish is dense
(from a zero `x` of `f`, the points `x + ε x₀` with `f x₀ ≠ 0` and `ε ≠ 0` tend to `x`). -/
private theorem dense_setOf_ne_zero_of_linear (f : Matrix T d ℝ → ℝ)
    (hadd : ∀ x y, f (x + y) = f x + f y) (hsmul : ∀ (c : ℝ) x, f (c • x) = c * f x)
    {x₀ : Matrix T d ℝ} (hx₀ : f x₀ ≠ 0) : Dense {x | f x ≠ 0} := by
  intro x
  by_cases hx : f x ≠ 0
  · exact subset_closure hx
  rw [not_not] at hx
  have ht : Filter.Tendsto (fun ε : ℝ => x + ε • x₀) (𝓝[≠] 0) (𝓝 x) := by
    have hc : Continuous (fun ε : ℝ => x + ε • x₀) :=
      continuous_const.add (continuous_id.smul continuous_const)
    have h0 := hc.tendsto 0
    rw [zero_smul, add_zero] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  refine mem_closure_of_tendsto ht (eventually_nhdsWithin_of_forall fun ε hε => ?_)
  show f (x + ε • x₀) ≠ 0
  rw [hadd, hsmul, hx, zero_add]
  exact mul_ne_zero hε hx₀

/-- **(T2) on a ray.** If the columns of `W` are linearly independent over `ℚ`, then for a dense set
of matrices `Ξ` (one row `ξ` per token) the numbers `ξ c_j`, over all tokens and all hidden units,
are linearly independent over `ℚ`. (For integers `κ` that are not all zero, `∑ κ_{t j} ξ_t c_j`
vanishes only for `Ξ` in a proper subspace, and there are countably many `κ`.) -/
theorem dense_setOf_linearIndependent_mul {q : Type*} [Fintype q] (W : Matrix d q ℝ)
    (hW : LinearIndependent ℚ (fun j : q => fun i : d => W i j)) :
    Dense {Ξ : Matrix T d ℝ | LinearIndependent ℚ (fun p : T × q => (Ξ * W) p.1 p.2)} := by
  classical
  -- for `κ : T × q → ℚ`, the functional `Ξ ↦ ∑ κ_{t j} (Ξ W)_{t j}`
  let ℓ : (T × q → ℚ) → Matrix T d ℝ → ℝ := fun κ Ξ => ∑ p : T × q, (κ p : ℝ) * (Ξ * W) p.1 p.2
  -- the set is the intersection, over `κ ≠ 0`, of the sets where `ℓ κ` does not vanish
  have hset : {Ξ : Matrix T d ℝ | LinearIndependent ℚ (fun p : T × q => (Ξ * W) p.1 p.2)}
      = ⋂ κ : {κ : T × q → ℚ // κ ≠ 0}, {Ξ | ℓ κ.1 Ξ ≠ 0} := by
    ext Ξ
    simp only [Set.mem_iInter]
    show LinearIndependent ℚ _ ↔ ∀ κ : {κ : T × q → ℚ // κ ≠ 0}, ℓ κ.1 Ξ ≠ 0
    rw [Fintype.linearIndependent_iff]
    simp only [Rat.smul_def]
    constructor
    · rintro hli ⟨κ, hκ⟩ h0
      exact hκ (funext (hli κ h0))
    · intro h κ h0
      by_contra hne
      exact h ⟨κ, fun hκ => hne fun i => by rw [hκ]; rfl⟩ h0
  rw [hset]
  -- Baire: a countable intersection of open dense sets is dense
  have : BaireSpace (Matrix T d ℝ) := inferInstanceAs (BaireSpace (T → d → ℝ))
  refine dense_iInter_of_isOpen (fun κ => isOpen_ne_fun ?_ continuous_const) (fun κ => ?_)
  · -- `ℓ κ` is continuous
    show Continuous fun Ξ : Matrix T d ℝ => ∑ p : T × q, (κ.1 p : ℝ) * (Ξ * W) p.1 p.2
    fun_prop
  -- `ℓ κ` is additive and homogeneous
  obtain ⟨κ, hκ⟩ := κ
  have hadd : ∀ x y, ℓ κ (x + y) = ℓ κ x + ℓ κ y := by
    intro x y
    simp only [ℓ, Matrix.add_mul, Matrix.add_apply, mul_add, Finset.sum_add_distrib]
  have hsmul : ∀ (c : ℝ) x, ℓ κ (c • x) = c * ℓ κ x := by
    intro c x
    simp only [ℓ, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ => by ring
  -- a token `t₀` and a hidden unit `j₀` with `κ_{t₀ j₀} ≠ 0`
  obtain ⟨⟨t₀, j₀⟩, hj₀⟩ : ∃ p, κ p ≠ 0 := by
    by_contra hne
    push Not at hne
    exact hκ (funext hne)
  -- the vector `∑_j κ_{t₀ j} W_{· j}` is not zero (`hW`): it has a nonzero entry `i₀`
  obtain ⟨i₀, hi₀⟩ : ∃ i₀, ∑ j, (κ (t₀, j) : ℝ) * W i₀ j ≠ 0 := by
    by_contra hne
    push Not at hne
    refine hj₀ (Fintype.linearIndependent_iff.1 hW (fun j => κ (t₀, j)) ?_ j₀)
    funext i
    simp only [Finset.sum_apply, Pi.smul_apply, Rat.smul_def, Pi.zero_apply]
    exact hne i
  -- `Ξ = single t₀ i₀ 1` gives `ℓ κ Ξ = ∑_j κ_{t₀ j} W_{i₀ j} ≠ 0`
  refine dense_setOf_ne_zero_of_linear (ℓ κ) hadd hsmul (x₀ := Matrix.single t₀ i₀ (1 : ℝ)) ?_
  show ∑ p : T × q, (κ p : ℝ) * (Matrix.single t₀ i₀ (1 : ℝ) * W) p.1 p.2 ≠ 0
  rw [Fintype.sum_prod_type, Finset.sum_eq_single t₀]
  · simpa only [Matrix.single_mul_apply_same, one_mul] using hi₀
  · intro t _ ht
    exact Finset.sum_eq_zero fun j _ => by rw [Matrix.single_mul_apply_of_ne _ _ _ _ _ ht, mul_zero]
  · intro h; exact absurd (Finset.mem_univ t₀) h

omit [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: `y ↦ y M`, as a continuous linear map. -/
private noncomputable def rightMulCLM {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
    (M : Matrix n p ℝ) : Matrix m n ℝ →L[ℝ] Matrix m p ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun y => y * M
      map_add' := fun a b => Matrix.add_mul a b M
      map_smul' := fun c a => Matrix.smul_mul c a M }

variable (θ : Params (Arch.mlp (T := T) (d := d) Real.tanh id hid) dIn dOut)

/-- **The fact in the proof of Lemma D.7.** Let `θ` be regular and let no row of the write `V` of
block `k` vanish (T1). If `𝐃𝓑(w̃ V) (((1 - w̃²) ⊙ b) V) = 0` for all `w̃`, then `b = 0`. -/
theorem eq_zero_of_fderiv_suffix_one_sub_sq
    (hθ : Regular (Arch.mlp Real.tanh id hid) θ) (k : Fin L)
    (hT1 : ∀ i : hid k, θ.write k i ≠ 0) (b : Matrix T (hid k) ℝ)
    (h : ∀ w : Matrix T (hid k) ℝ,
      fderiv ℝ (fun h' : Matrix T d ℝ => suffix (Arch.mlp Real.tanh id hid) 0 θ k.succ h')
        (w * θ.write k) ((Matrix.of fun t j => (1 - w t j ^ 2) * b t j) * θ.write k) = 0) :
    b = 0 := by
  classical
  -- Lemma D.2 at the hidden state after the block: `𝐃𝓑` is injective on an open dense set `U`
  obtain ⟨U, -, hUd, hU⟩ := exists_open_dense_injective_fderiv_suffix
    (Arch.mlp Real.tanh id hid) θ rfl (fun ℓ => analyticOnNhd_f_mlp analyticOnNhd_tanh ℓ) hθ k.succ
  -- `V` has rank `d`, so `V⁺ V = 1` for some `V⁺`, and `w ↦ w V` is onto, hence open
  obtain ⟨Vp, hVp⟩ : ∃ Vp : Matrix d (hid k) ℝ, Vp * θ.write k = 1 :=
    Matrix.vecMul_surjective_iff_exists_left_inverse.1
      (Matrix.vecMul_surjective_iff_rank_eq_card.2 (hθ.rank_write k))
  have hopen : IsOpenMap (rightMulCLM (m := T) (θ.write k)) :=
    (rightMulCLM (m := T) (θ.write k)).isOpenMap fun y =>
      ⟨y * Vp, by show y * Vp * θ.write k = y; rw [Matrix.mul_assoc, hVp, Matrix.mul_one]⟩
  -- so the `w` with `w V ∈ U` are dense, and there `((1 - w²) ⊙ b) V = 0`
  have hdense : Dense {w : Matrix T (hid k) ℝ | w * θ.write k ∈ U} := hUd.preimage hopen
  let F : Matrix T (hid k) ℝ → Matrix T d ℝ :=
    fun w => (Matrix.of fun t j => (1 - w t j ^ 2) * b t j) * θ.write k
  have hF : ∀ w ∈ {w : Matrix T (hid k) ℝ | w * θ.write k ∈ U}, F w = 0 :=
    fun w hw => hU _ hw (by rw [h w, map_zero])
  -- `F` is continuous (a polynomial in `w`), so it vanishes everywhere
  have hFc : Continuous F := by fun_prop
  have hF0 : F = fun _ => 0 := Continuous.ext_on hdense hFc continuous_const hF
  -- at `w = 0` and at `w = single t j 1`, row `t` of the difference is `b_{t j} a_j`
  ext t j
  obtain ⟨i, hi⟩ : ∃ i, θ.write k j i ≠ 0 := by
    by_contra hne
    push Not at hne
    exact hT1 j (funext hne)
  have e0 := congrFun (congrFun (congrFun hF0 0) t) i
  have e1 := congrFun (congrFun (congrFun hF0 (Matrix.single t j (1 : ℝ))) t) i
  simp only [F, Matrix.mul_apply, Matrix.of_apply, Matrix.zero_apply] at e0 e1
  have hdiff : ∑ j', (1 - (0 : ℝ) ^ 2) * b t j' * θ.write k j' i
      - ∑ j', (1 - Matrix.single t j (1 : ℝ) t j' ^ 2) * b t j' * θ.write k j' i
      = b t j * θ.write k j i := by
    rw [← Finset.sum_sub_distrib, Finset.sum_eq_single j]
    · rw [Matrix.single_apply_same]
      ring
    · intro j' _ hj'
      rw [Matrix.single_apply_of_ne _ _ _ _ _ (fun h => hj' h.2.symm)]
      ring
    · intro hj; exact absurd (Finset.mem_univ j) hj
  rw [e0, e1, sub_zero] at hdiff
  exact (mul_eq_zero.1 hdiff.symm).resolve_right hi

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the product of two analytic matrix-valued maps is analytic (matrix multiplication is a
continuous bilinear map). -/
private theorem analyticOnNhd_matMul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
    {f : E → Matrix m n ℝ} {g : E → Matrix n p ℝ} {s : Set E}
    (hf : AnalyticOnNhd ℝ f s) (hg : AnalyticOnNhd ℝ g s) :
    AnalyticOnNhd ℝ (fun y => f y * g y) s := by
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
  exact fun y hy => (B'.analyticAt_bilinear (f y, g y)).comp₂ (hf y hy) (hg y hy)

/-- Helper: an analytic family of continuous linear maps, applied to an analytic family of vectors,
is analytic. -/
private theorem analyticOnNhd_clm_apply {X E F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {J : X → E →L[ℝ] F} {v : X → E} {s : Set X} (hJ : AnalyticOnNhd ℝ J s)
    (hv : AnalyticOnNhd ℝ v s) : AnalyticOnNhd ℝ (fun x => J x (v x)) s :=
  fun x hx => ((ContinuousLinearMap.id ℝ (E →L[ℝ] F)).analyticAt_bilinear (J x, v x)).comp₂
    (hJ x hx) (hv x hx)

/-- In the case (n), with analytic blocks, `(θ, h) ↦ 𝓑_{>k}(h)` (with the weights `θ`) is jointly
analytic. (The same reverse induction as `analyticOnNhd_suffix` and `differentiable_suffix_prod`;
the weights are continuous linear functions of the parameters.) -/
theorem analyticOnNhd_suffix_prod (A : Arch T d L) (hχ : A.χ = id)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (k : Fin (L + 1)) :
    AnalyticOnNhd ℝ (fun p : Params A dIn dOut × Matrix T d ℝ => suffix A 0 p.1 k p.2)
      Set.univ := by
  -- the weights are linear, hence analytic, functions of the parameters
  have hD : AnalyticOnNhd ℝ (fun θ' : Params A dIn dOut => θ'.D) Set.univ :=
    (LinearMap.toContinuousLinearMap
      (Params.linD (A := A) (dIn := dIn) (dOut := dOut))).analyticOnNhd _
  have hr : ∀ ℓ, AnalyticOnNhd ℝ (fun θ' : Params A dIn dOut => θ'.read ℓ) Set.univ := fun ℓ =>
    (LinearMap.toContinuousLinearMap
      (Params.linRead (A := A) (dIn := dIn) (dOut := dOut) ℓ)).analyticOnNhd _
  have hw : ∀ ℓ, AnalyticOnNhd ℝ (fun θ' : Params A dIn dOut => θ'.write ℓ) Set.univ := fun ℓ =>
    (LinearMap.toContinuousLinearMap
      (Params.linWrite (A := A) (dIn := dIn) (dOut := dOut) ℓ)).analyticOnNhd _
  have hfst : AnalyticOnNhd ℝ (fun p : Params A dIn dOut × Matrix T d ℝ => p.1) Set.univ :=
    analyticOnNhd_fst
  have hsnd : AnalyticOnNhd ℝ (fun p : Params A dIn dOut × Matrix T d ℝ => p.2) Set.univ :=
    analyticOnNhd_snd
  induction k using Fin.reverseInduction with
  | last =>
    -- `(θ, h) ↦ h D`
    simp only [suffix_last, hχ, id_eq]
    exact analyticOnNhd_matMul hsnd (hD.comp hfst (Set.mapsTo_univ _ _))
  | cast ℓ ih =>
    -- `(θ, h) ↦ 𝓑_{>ℓ}(f_ℓ(h W_read) W_write)`, with the weights `θ`
    simp only [suffix_castSucc, hχ, id_eq, Pi.zero_apply, Matrix.mul_zero, zero_add]
    exact ih.comp (hfst.prod (analyticOnNhd_matMul
      ((hf ℓ).comp (analyticOnNhd_matMul hsnd ((hr ℓ).comp hfst (Set.mapsTo_univ _ _)))
        (Set.mapsTo_univ _ _))
      ((hw ℓ).comp hfst (Set.mapsTo_univ _ _)))) (Set.mapsTo_univ _ _)

/-- **Lemma D.7 (the step for `tanh` on rays), case (n).** Let `θ` be regular, and let block `k`
satisfy (T1), no row of its write vanishes, and (T2), the columns of its read are linearly
independent over `ℚ`. Then the claim for the hidden state after the block implies the claim for the
hidden state before it: `(D_{k+1})` implies `(D_k)`. -/
theorem claim_castSucc_tanh [Nonempty T]
    (hθ : Regular (Arch.mlp Real.tanh id hid) θ) (k : Fin L)
    (hT1 : ∀ i : hid k, θ.write k i ≠ 0)
    (hT2 : LinearIndependent ℚ (fun j : hid k => fun i : d => θ.read k i j))
    (hk : Claim (Arch.mlp Real.tanh id hid) θ k.succ) :
    Claim (Arch.mlp Real.tanh id hid) θ k.castSucc := by
  classical
  intro Z η hZη
  have hf : ∀ ℓ, AnalyticOnNhd ℝ ((Arch.mlp (T := T) (d := d) Real.tanh id hid).f ℓ) Set.univ :=
    fun ℓ => analyticOnNhd_f_mlp analyticOnNhd_tanh ℓ
  -- the identity for one block (22), with `σ = tanh` and `ż(n) = n C`, `C = Z W + η_W`
  have h22 := (suffixFlat_castSucc_iff_mlp hasDerivAt_tanh θ k Z η).1 hZη
  obtain ⟨C, hC⟩ : ∃ C : Matrix d (hid k) ℝ, C = Z * θ.read k + η.read k := ⟨_, rfl⟩
  rw [← hC] at h22
  -- the maps `𝒯_1 Ξ` and `𝒯_0` of the outputs `w` of the hidden units
  let T1 : Matrix T d ℝ → Matrix T (hid k) ℝ → Matrix T dOut ℝ := fun Ξ w =>
    fderiv ℝ (fun h' : Matrix T d ℝ => suffix (Arch.mlp Real.tanh id hid) 0 θ k.succ h')
      (w * θ.write k) ((Matrix.of fun t j => (1 - w t j ^ 2) * (Ξ * C) t j) * θ.write k)
  let T0 : Matrix T (hid k) ℝ → Matrix T dOut ℝ := fun w =>
    fderiv ℝ (fun h' : Matrix T d ℝ => suffix (Arch.mlp Real.tanh id hid) 0 θ k.succ h')
        (w * θ.write k) (w * η.write k)
      + fderiv ℝ (fun θ' : Params (Arch.mlp (T := T) (d := d) Real.tanh id hid) dIn dOut =>
          suffix (Arch.mlp Real.tanh id hid) 0 θ' k.succ (w * θ.write k)) θ η
  -- both are analytic: `𝓑` and `(θ', h') ↦ 𝓑(h')` are, hence so are their derivatives
  have hB := analyticOnNhd_suffix (Arch.mlp (T := T) (d := d) Real.tanh id hid) θ rfl hf k.succ
  have hΦ := analyticOnNhd_suffix_prod (Arch.mlp (T := T) (d := d) Real.tanh id hid)
    (dIn := dIn) (dOut := dOut) rfl hf k.succ
  -- `w ↦ 𝐃𝓑(w V)` (stated without a type: the normed structure on the derivatives comes from
  -- `AnalyticOnNhd.fderiv`)
  have hJ :=
    hB.fderiv.comp ((rightMulCLM (m := T) (θ.write k)).analyticOnNhd Set.univ)
      (Set.mapsTo_univ _ _)
  have hT1an : ∀ Ξ, AnalyticOnNhd ℝ (T1 Ξ) Set.univ := by
    intro Ξ
    -- the direction `((1 - w²) ⊙ Ξ C) V` is a polynomial in `w`
    have hdir : AnalyticOnNhd ℝ (fun w : Matrix T (hid k) ℝ =>
        (Matrix.of fun t j => (1 - w t j ^ 2) * (Ξ * C) t j) * θ.write k) Set.univ := by
      refine analyticOnNhd_matMul ?_ analyticOnNhd_const
      show AnalyticOnNhd ℝ (fun w : Matrix T (hid k) ℝ => fun t j => (1 - w t j ^ 2) * (Ξ * C) t j)
        Set.univ
      exact AnalyticOnNhd.pi fun t => AnalyticOnNhd.pi fun j =>
        (analyticOnNhd_const.sub ((analyticOnNhd_matrix_entry t j).pow 2)).mul analyticOnNhd_const
    exact analyticOnNhd_clm_apply hJ hdir
  have hT0eq : T0 = fun w => fderiv ℝ
      (fun p : Params (Arch.mlp (T := T) (d := d) Real.tanh id hid) dIn dOut × Matrix T d ℝ =>
        suffix (Arch.mlp Real.tanh id hid) 0 p.1 k.succ p.2) (θ, w * θ.write k) (η, w * η.write k) := by
    funext w
    exact fderiv_partial_add
      (Φ := fun θ' h' => suffix (Arch.mlp (T := T) (d := d) Real.tanh id hid) 0 θ' k.succ h')
      (hΦ _ (Set.mem_univ _)).differentiableAt η (w * η.write k)
  have hT0an : AnalyticOnNhd ℝ T0 Set.univ := by
    rw [hT0eq]
    exact analyticOnNhd_clm_apply (hΦ.fderiv.comp (analyticOnNhd_const.prod
        ((rightMulCLM (m := T) (θ.write k)).analyticOnNhd Set.univ)) (Set.mapsTo_univ _ _))
      (analyticOnNhd_const.prod ((rightMulCLM (m := T) (η.write k)).analyticOnNhd Set.univ))
  -- on the ray `n = t Ξ` the outputs are `w = tanh(t Ξ W)`, and (22) reads `𝒯_0(w) + t 𝒯_1(w) = 0`
  have hray : ∀ (Ξ : Matrix T d ℝ) (t : ℝ),
      T0 ((t • (Ξ * θ.read k)).map Real.tanh)
        + t • T1 Ξ ((t • (Ξ * θ.read k)).map Real.tanh) = 0 := by
    intro Ξ t
    have e := h22 (t • Ξ)
    unfold blockLHS at e
    simp only [Matrix.smul_mul] at e
    have hdir : (Matrix.of fun a j =>
        ((t • (Ξ * θ.read k)).map fun z => 1 - Real.tanh z ^ 2) a j * (t • (Ξ * C)) a j)
        = t • Matrix.of fun a j =>
          (1 - ((t • (Ξ * θ.read k)).map Real.tanh) a j ^ 2) * (Ξ * C) a j := by
      ext a j
      simp only [Matrix.of_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
      ring
    rw [hdir, Matrix.smul_mul, map_add, map_smul] at e
    show (_ + _) + t • _ = 0
    rw [add_comm, ← add_assoc]
    exact e
  -- for `Ξ` in the dense set of (T2) on a ray, Lemma D.1 makes `𝒯_0` and `𝒯_1 Ξ` vanish
  have hsep : ∀ Ξ ∈ {Ξ : Matrix T d ℝ |
      LinearIndependent ℚ (fun p : T × hid k => (Ξ * θ.read k) p.1 p.2)},
      (∀ w, T0 w = 0) ∧ ∀ w, T1 Ξ w = 0 := by
    intro Ξ hΞ
    have hs := tanh_ray_separation_matrix (Ξ * θ.read k) hΞ 1 ![T0, T1 Ξ]
      (Fin.forall_fin_two.2 ⟨hT0an, hT1an Ξ⟩) (fun t _ => by simpa using hray Ξ t)
    exact ⟨hs 0, hs 1⟩
  have hD := dense_setOf_linearIndependent_mul (T := T) (θ.read k) hT2
  -- (b): `Ξ C = 0` on the dense set (by the fact), so for every `Ξ`, so `C = 0`
  have hΞC : ∀ Ξ ∈ {Ξ : Matrix T d ℝ |
      LinearIndependent ℚ (fun p : T × hid k => (Ξ * θ.read k) p.1 p.2)}, Ξ * C = 0 :=
    fun Ξ hΞ => eq_zero_of_fderiv_suffix_one_sub_sq θ hθ k hT1 (Ξ * C) (hsep Ξ hΞ).2
  have hall : (fun Ξ : Matrix T d ℝ => Ξ * C) = fun _ => 0 :=
    Continuous.ext_on hD (continuous_id.matrix_mul continuous_const) continuous_const hΞC
  have hC0 : C = 0 := by
    obtain ⟨t₀⟩ := ‹Nonempty T›
    ext i j
    have e := congrFun (congrFun (congrFun hall (Matrix.single t₀ i (1 : ℝ))) t₀) j
    simpa only [Matrix.single_mul_apply_same, one_mul, Matrix.zero_apply] using e
  have hread : η.read k = -(Z * θ.read k) := by
    rw [hC] at hC0
    rw [eq_neg_iff_add_eq_zero, add_comm]
    exact hC0
  -- (c): `𝒯_0 = 0` is the hypothesis of Lemma D.3 at the write `V` (rank `d`)
  obtain ⟨Ξ₀, hΞ₀⟩ := hD.nonempty
  obtain ⟨Z', hZ', hflat'⟩ := suffixFlat_of_flat_at_write
    (Arch.mlp (T := T) (d := d) Real.tanh id hid) θ rfl hf hθ k.succ (θ.write k)
    (hθ.rank_write k) (η.write k) η (hsep Ξ₀ hΞ₀).1
  -- `(D_{k+1})` gives the changes of basis after the block
  obtain ⟨X, hXk, hX, hXD⟩ := hk Z' η hflat'
  -- put `Z` at the hidden state before the block
  refine ⟨Function.update X k.castSucc Z, Function.update_self _ _ _, fun ℓ hℓ => ?_, ?_⟩
  · rcases eq_or_ne ℓ k with rfl | hne
    · -- the block itself: (b) and (c)
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
