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
variable {σ σ' : ℝ → ℝ}

/-- **The left side of the identity for one block,** equation (21) of the paper:
`𝓛 = 𝐃𝓑(w̃ V) ((w̃' ⊙ ż) V + w̃ η_V) + 𝐃_θ 𝓑(w̃ V) η`, for block `k` with the write `V` and the
network `𝓑` after it. Here `w` stands for the outputs `w̃` of the hidden units, `w'` for their
derivatives `w̃'`, and `zdot` for `ż`, the derivative of what the hidden units read. (The network
after the block does not depend on the weights of the block, so `𝐃_θ 𝓑 η` is the paper's
`𝐃_θ 𝓑 η'`.) -/
noncomputable def blockLHS (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)
    (k : Fin L) (η : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)
    (w w' zdot : Matrix T (hid k) ℝ) : Matrix T dOut ℝ :=
  fderiv ℝ (fun h' : Matrix T d ℝ => suffix (Arch.mlp σ id hid) 0 θ k.succ h') (w * θ.write k)
      ((Matrix.of fun t j => w' t j * zdot t j) * θ.write k + w * η.write k)
    + fderiv ℝ (fun θ' : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut =>
        suffix (Arch.mlp σ id hid) 0 θ' k.succ (w * θ.write k)) θ η

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
  sorry

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
  sorry

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
  sorry

end Skips
