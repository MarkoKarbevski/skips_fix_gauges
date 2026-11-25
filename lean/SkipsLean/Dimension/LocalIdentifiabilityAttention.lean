import SkipsLean.Dimension.OrbitNetwork
import SkipsLean.Dimension.ExpOrbitAttention
import SkipsLean.Dimension.UpperBoundAttention
import SkipsLean.Network.AttentionAnalytic
import SkipsLean.OneBlock.AttentionDim
import SkipsLean.Residual.DepthAttentionDim

/-!
# Attention networks are locally identifiable up to their symmetries

Paper (dimension paper): Proposition 4.6 (The equality condition and local identifiability): "Let
the blocks be tanh, GELU, SwiGLU, GeGLU or attention blocks, without normalization or under
pre-RMSNorm. A network satisfies the equality condition if and only if, at generic parameters, it
is locally identifiable up to its symmetries. Every symmetry that is needed is then close to the
identity." Paper (skips paper):
Proposition 4.5, the same for skipless and residual networks, and Corollary 4.9 (Residual networks
are locally identifiable): "Let the blocks be analytic, with or without pre-RMSNorm, and let `θ`
be generic parameters of the residual network. Every `θ'` near `θ` with the same function is
obtained from `θ` by symmetries inside the blocks and by one matrix `G ∈ 𝒢`, all close to the
identity. The matrix `G` is the same at all hidden states".

Here, for attention blocks without normalization, whose symmetries inside the blocks are the
changes of basis inside the heads (`Params.headsQK`, `Params.headsVO`,
`Symmetry/AttentionHeads.lean`):

* the direction from the equality condition to local identifiability, at one parameter, for
  skipless networks (`fd(θ) = P − (L + 1) d² − s`) and for residual networks
  (`fd(θ) = P − d² − s`), `s = 2 ∑_ℓ H_ℓ d_{h,ℓ}²`;
* at almost every parameter: the skipless network of one attention block (Theorem 5.1 of the
  dimension paper gives its functional dimension) and the residual network of `L` attention
  blocks (Corollary 4.9 of the skips paper; Theorem 4.7 gives its functional dimension).

The twins for MLP blocks are `Dimension/LocalIdentifiability.lean`,
`Dimension/LocalIdentifiabilityGated.lean`, `Residual/LocalIdentifiability.lean` and
`Residual/LocalIdentifiabilityGated.lean`; all use `exists_mem_orbit_of_eval_eq`
(`Dimension/OrbitNetwork.lean`). Not stated here: the converse direction (the equivalences:
`Dimension/IdentifiableIff.lean`, `Residual/IdentifiableIff.lean`); pre-RMSNorm
(`Residual/LocalIdentifiabilityAttentionRMS.lean`).
-/

namespace Skips

open Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {sees : T → T → Prop} [DecidableRel sees]

section AnyDepth

variable {L : ℕ} {H dh : Fin L → Type} [∀ ℓ, Fintype (H ℓ)] [∀ ℓ, Fintype (dh ℓ)]
  [∀ ℓ, DecidableEq (dh ℓ)]

/-- Helper (the private `cancel_left_of_rank_uba` of `Dimension/UpperBoundAttention.lean`): a
matrix `M` of rank equal to its number of columns cancels on the left, `M X = M Y → X = Y` (its
kernel is `0` by rank–nullity). -/
private theorem cancel_left_of_rank_lia {m n k : Type*} [Fintype n] (M : Matrix m n ℝ)
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

omit [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] [∀ ℓ, DecidableEq (dh ℓ)] in
/-- Helper (the private `headDirLin_injective_uba` of `Dimension/UpperBoundAttention.lean`): if
the query and the value matrix of every head have rank `d_h`, the direction
`headDirQK θ Γ + headDirVO θ Γ'` determines `Γ` and `Γ'`: the query columns of head `i` move by
`W_{Q,i} Γ_i`, its value columns by `W_{V,i} Γ'_i`. -/
private theorem headDir_injective_lia {χ : Matrix T d ℝ → Matrix T d ℝ}
    (θ : Params (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut)
    (hQ : ∀ ℓ (i : H ℓ), ((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k)).rank
      = Fintype.card (dh ℓ))
    (hV : ∀ ℓ (i : H ℓ),
      ((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))).rank
        = Fintype.card (dh ℓ))
    {Γ Γ' Δ Δ' : ∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ}
    (h : headDirQK θ Γ + headDirVO θ Γ' = headDirQK θ Δ + headDirVO θ Δ') :
    Γ = Δ ∧ Γ' = Δ' := by
  -- the entry `(a, p)` of the read of block `ℓ`
  have hr : ∀ ℓ a p, (headDirQK θ Γ + headDirVO θ Γ').read ℓ a p
      = (headDirQK θ Δ + headDirVO θ Δ').read ℓ a p := fun ℓ a p => by rw [h]
  refine ⟨?_, ?_⟩ <;> funext ℓ i
  · -- the query columns of head `i`: `W_{Q,i} Γ_i = W_{Q,i} Δ_i`, and `W_{Q,i}` has rank `d_h`
    refine cancel_left_of_rank_lia _ (hQ ℓ i) (Matrix.ext fun a k => ?_)
    have := hr ℓ a (i, Sum.inl k)
    simp only [Params.add_read, Matrix.add_apply, headDirQK, headDirVO, Matrix.of_apply,
      add_zero] at this
    simpa only [Matrix.mul_apply, Matrix.submatrix_apply, id] using this
  · -- the value columns of head `i`: `W_{V,i} Γ'_i = W_{V,i} Δ'_i`
    refine cancel_left_of_rank_lia _ (hV ℓ i) (Matrix.ext fun a k => ?_)
    have := hr ℓ a (i, Sum.inr (Sum.inr k))
    simp only [Params.add_read, Matrix.add_apply, headDirQK, headDirVO, Matrix.of_apply,
      zero_add] at this
    simpa only [Matrix.mul_apply, Matrix.submatrix_apply, id] using this

omit [∀ ℓ, DecidableEq (dh ℓ)] in
/-- Helper (the private `finrank_headFun_uba` of `Dimension/UpperBoundAttention.lean`): the
families `Γ` of `d_h × d_h` matrices, one for each head of each block, form a space of dimension
`∑_ℓ H_ℓ d_{h,ℓ}²`. -/
private theorem finrank_headFun_lia :
    Module.finrank ℝ (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)
      = ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2 := by
  rw [Module.finrank_pi_fintype]
  simp only [Module.finrank_pi_fintype, Module.finrank_matrix, Module.finrank_self, mul_one,
    Finset.sum_const, Finset.card_univ, smul_eq_mul, sq]

/-- **The argument common to the two statements of Proposition 4.6 for attention blocks.** Let
`ι : M → (Fin (L+1) → Matrix d d ℝ) × (∀ ℓ, H ℓ → Matrix …) × (∀ ℓ, H ℓ → Matrix …)` be linear,
with `m ↦ cobDir θ (ι m).1 + headDirQK θ (ι m).2.1 + headDirVO θ (ι m).2.2` injective, such that
the changes of basis `cobExpHeads θ (ι m)` preserve the function. If `fd(θ) + dim M = P`, then
every `θ'` near `θ` with the same function is `cobExpHeads θ (ι m)` with `exp (ι m).1 ∈ V`,
`exp (ι m).2.1 ∈ W` and `exp (ι m).2.2 ∈ W`. The proof: the derivative of
`m ↦ cobExpHeads θ (ι m)` at `0` is that injective map, and `exists_mem_orbit_of_eval_eq`. -/
private theorem exists_cobExpHeads_of_eval_eq_lia (S : Fin L → Matrix d d ℝ)
    (θ : Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut)
    {M : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M] [FiniteDimensional ℝ M]
    (ι : M →L[ℝ] (Fin (L + 1) → Matrix d d ℝ) × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)
      × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ))
    (hinj : Function.Injective fun m : M =>
      cobDir θ (ι m).1 + headDirQK θ (ι m).2.1 + headDirVO θ (ι m).2.2)
    (hfd : funDim (Arch.attention sees id H dh) S θ + Module.finrank ℝ M
      = Module.finrank ℝ (Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut))
    (hpres : ∀ (m : M) (x : Matrix T dIn ℝ),
      eval (Arch.attention sees id H dh) S (cobExpHeads θ (ι m)) x
        = eval (Arch.attention sees id H dh) S θ x) :
    ∀ V ∈ 𝓝 (1 : Fin (L + 1) → Matrix d d ℝ),
      ∀ W ∈ 𝓝 (1 : ∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ), ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.attention sees id H dh) S θ' x
        = eval (Arch.attention sees id H dh) S θ x) →
        ∃ m : M, (fun ℓ => NormedSpace.exp ((ι m).1 ℓ)) ∈ V
          ∧ (fun ℓ i => NormedSpace.exp ((ι m).2.1 ℓ i)) ∈ W
          ∧ (fun ℓ i => NormedSpace.exp ((ι m).2.2 ℓ i)) ∈ W
          ∧ θ' = cobExpHeads θ (ι m) := by
  intro V hVn W hWn
  -- the orbit map `(m, Γ, Γ') ↦ ((θ.headsQK (exp Γ)).headsVO (exp Γ')).cob (exp m) (exp m)`,
  -- strictly differentiable at `0`
  obtain ⟨Φ', hΦ', hΦ'v⟩ := hasStrictFDerivAt_cobExpHeads θ
  have hΦ'0 : HasStrictFDerivAt (cobExpHeads θ) Φ' (ι 0) := by
    rw [map_zero]
    exact hΦ'
  have hΦ := hΦ'0.comp (0 : M) ι.hasStrictFDerivAt
  -- its derivative `m ↦ cobDir θ (ι m).1 + headDirQK θ (ι m).2.1 + headDirVO θ (ι m).2.2` is
  -- injective (Lemma B.1)
  have hinj' : Function.Injective (Φ'.comp ι) := by
    intro m₁ m₂ h
    refine hinj ?_
    show cobDir θ (ι m₁).1 + headDirQK θ (ι m₁).2.1 + headDirVO θ (ι m₁).2.2
      = cobDir θ (ι m₂).1 + headDirQK θ (ι m₂).2.1 + headDirVO θ (ι m₂).2.2
    rw [← hΦ'v, ← hΦ'v]
    exact h
  -- it passes through `θ` and keeps the function
  have hΦ0 : (cobExpHeads θ ∘ ι) 0 = θ := by
    rw [Function.comp_apply, map_zero]
    exact cobExpHeads_zero θ
  have hconst : ∀ᶠ m in 𝓝 (0 : M), ∀ x : Matrix T dIn ℝ,
      eval (Arch.attention sees id H dh) S ((cobExpHeads θ ∘ ι) m) x
        = eval (Arch.attention sees id H dh) S θ x :=
    Eventually.of_forall fun m x => hpres m x
  -- the `m` with `exp (ι m).1 ∈ V` form a neighborhood of `0`
  have hV' : (fun m : M => fun ℓ => NormedSpace.exp ((ι m).1 ℓ)) ⁻¹' V ∈ 𝓝 (0 : M) := by
    have hexp : ContinuousAt (fun Y : Matrix d d ℝ => NormedSpace.exp Y) 0 :=
      hasStrictFDerivAt_matrix_exp_zero.continuousAt
    have hc : ContinuousAt (fun m : M => fun ℓ => NormedSpace.exp ((ι m).1 ℓ)) 0 :=
      continuousAt_pi.2 fun ℓ => ContinuousAt.comp_of_eq (f := fun m : M => (ι m).1 ℓ) hexp
        ((continuous_apply ℓ).comp (continuous_fst.comp ι.continuous)).continuousAt
        (by simp only [map_zero, Prod.fst_zero, Pi.zero_apply])
    refine hc.preimage_mem_nhds ?_
    have h1 : (fun ℓ => NormedSpace.exp ((ι (0 : M)).1 ℓ))
        = (1 : Fin (L + 1) → Matrix d d ℝ) := by
      funext ℓ
      simp only [map_zero, Prod.fst_zero, Pi.zero_apply, NormedSpace.exp_zero, Pi.one_apply]
    rw [h1]
    exact hVn
  -- likewise for the changes of basis inside the heads
  have hhead : ∀ g : M → ∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ, Continuous g → g 0 = 0 →
      (fun m : M => fun ℓ i => NormedSpace.exp (g m ℓ i)) ⁻¹' W ∈ 𝓝 (0 : M) := by
    intro g hg hg0
    have hc : ContinuousAt (fun m : M => fun ℓ i => NormedSpace.exp (g m ℓ i)) 0 :=
      continuousAt_pi.2 fun ℓ => continuousAt_pi.2 fun i =>
        ContinuousAt.comp_of_eq (f := fun m : M => g m ℓ i)
          (hasStrictFDerivAt_matrix_exp_zero (d := dh ℓ)).continuousAt
          ((continuous_apply i).comp ((continuous_apply ℓ).comp hg)).continuousAt
          (by simp only [hg0, Pi.zero_apply])
    refine hc.preimage_mem_nhds ?_
    have h1 : (fun ℓ (i : H ℓ) => NormedSpace.exp (g 0 ℓ i))
        = (1 : ∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) := by
      funext ℓ i
      simp only [hg0, Pi.zero_apply, NormedSpace.exp_zero, Pi.one_apply]
    rw [h1]
    exact hWn
  have hW1 := hhead (fun m => (ι m).2.1) (continuous_fst.comp (continuous_snd.comp ι.continuous))
    (by simp only [map_zero, Prod.snd_zero, Prod.fst_zero])
  have hW2 := hhead (fun m => (ι m).2.2) (continuous_snd.comp (continuous_snd.comp ι.continuous))
    (by simp only [map_zero, Prod.snd_zero])
  -- the orbit fills the level set near `θ`
  obtain ⟨U, hU, hUV⟩ := exists_mem_orbit_of_eval_eq (Arch.attention sees id H dh) S
    (fun ℓ => analyticOnNhd_f_attention sees id H dh ℓ) analyticOnNhd_id θ hΦ hΦ0 hinj' hconst
    hfd _ (inter_mem hV' (inter_mem hW1 hW2))
  refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
  obtain ⟨m, ⟨hmV, hmW1, hmW2⟩, hmθ⟩ := hUV θ' hθ' heq
  exact ⟨m, hmV, hmW1, hmW2, hmθ.symm⟩

/-- **Proposition 4.6 of the dimension paper for attention blocks, from the equality condition to
local identifiability, without normalization:** if `E` and the writes have rank `d`, the query and
value matrices of every head have rank `d_h` and `fd(θ) = P − (L + 1) d² − s`, then every `θ'`
near `θ` with the same function is `θ` after changes of basis inside the heads, near the identity,
and a change of basis by invertible `G_0, …, G_L` near the identity. -/
theorem exists_cob_heads_of_eval_eq_skipless_attention
    (θ : Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut)
    (hE : θ.E.rank = Fintype.card d) (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d)
    (hQ : ∀ ℓ (i : H ℓ), ((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k)).rank
      = Fintype.card (dh ℓ))
    (hV : ∀ ℓ (i : H ℓ),
      ((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))).rank
        = Fintype.card (dh ℓ))
    (hfd : funDim (Arch.attention sees id H dh) 0 θ
        + ((L + 1) * Fintype.card d ^ 2
          + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
      = Module.finrank ℝ (Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut)) :
    ∀ V ∈ 𝓝 (1 : Fin (L + 1) → Matrix d d ℝ),
      ∀ W ∈ 𝓝 (1 : ∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ), ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.attention sees id H dh) 0 θ' x
        = eval (Arch.attention sees id H dh) 0 θ x) →
        ∃ (G : Fin (L + 1) → GL d ℝ) (K K' : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ),
          (fun ℓ => (G ℓ : Matrix d d ℝ)) ∈ V
            ∧ (fun ℓ i => (K ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)) ∈ W
            ∧ (fun ℓ i => (K' ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)) ∈ W
            ∧ θ' = ((θ.headsQK K).headsVO K').cob G G := by
  intro V hVn W hWn
  -- the triples `(m, Γ, Γ')` form a space of dimension `(L + 1) d² + 2 ∑_ℓ H_ℓ d_{h,ℓ}²`
  have hdimM : Module.finrank ℝ ((Fin (L + 1) → Matrix d d ℝ)
      × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ))
      = (L + 1) * Fintype.card d ^ 2
        + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2 := by
    rw [Module.finrank_prod, Module.finrank_prod, finrank_headFun_lia,
      Module.finrank_pi_fintype]
    simp only [Module.finrank_matrix, Module.finrank_self, mul_one, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul, sq]
    ring
  -- the changes of basis inside the heads and then at the hidden states preserve the function
  -- (Appendix B and Proposition 3.2)
  have hpres : ∀ (p : (Fin (L + 1) → Matrix d d ℝ) × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)
      × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)) (x : Matrix T dIn ℝ),
      eval (Arch.attention sees id H dh) 0 (cobExpHeads θ (ContinuousLinearMap.id ℝ _ p)) x
        = eval (Arch.attention sees id H dh) 0 θ x := by
    intro p x
    have h1 := eval_cob_skipless (A := Arch.attention sees id H dh)
      ((θ.headsQK fun ℓ i => expGL (p.2.1 ℓ i)).headsVO fun ℓ i => expGL (p.2.2 ℓ i))
      (fun ℓ => expGL (p.1 ℓ)) x rfl
    exact h1.trans ((eval_headsVO (θ.headsQK fun ℓ i => expGL (p.2.1 ℓ i))
      (fun ℓ i => expGL (p.2.2 ℓ i)) 0 x).trans (eval_headsQK θ _ 0 x))
  -- the orbit fills the level set near `θ`; its derivative is injective by Lemma B.1
  obtain ⟨U, hU, hUV⟩ := exists_cobExpHeads_of_eval_eq_lia 0 θ (ContinuousLinearMap.id ℝ _)
    (fun _ _ h => cobDir_add_headDirQK_add_headDirVO_injective θ hE hw hQ hV h)
    (by rw [hdimM]; exact hfd) hpres V hVn W hWn
  refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
  -- `G_ℓ = exp m_ℓ`, `K_{ℓ,i} = exp Γ_{ℓ,i}`, `K'_{ℓ,i} = exp Γ'_{ℓ,i}`
  obtain ⟨p, hpV, hpW1, hpW2, rfl⟩ := hUV θ' hθ' heq
  exact ⟨fun ℓ => expGL (p.1 ℓ), fun ℓ i => expGL (p.2.1 ℓ i), fun ℓ i => expGL (p.2.2 ℓ i),
    hpV, hpW1, hpW2, rfl⟩

/-- **Proposition 4.5 of the skips paper for residual networks of attention blocks, from the
equality condition to local identifiability, without normalization:** if `E` has rank `d`, the
query and value matrices of every head have rank `d_h` and `fd(θ) = P − d² − s`, then every `θ'`
near `θ` with the same function is `θ` after changes of basis inside the heads, near the identity,
and the change of basis by one invertible `G` near the identity at all hidden states. -/
theorem exists_cob_heads_of_eval_eq_residual_attention
    (θ : Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut)
    (hE : θ.E.rank = Fintype.card d)
    (hQ : ∀ ℓ (i : H ℓ), ((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k)).rank
      = Fintype.card (dh ℓ))
    (hV : ∀ ℓ (i : H ℓ),
      ((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))).rank
        = Fintype.card (dh ℓ))
    (hfd : funDim (Arch.attention sees id H dh) 1 θ
        + (Fintype.card d ^ 2 + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
      = Module.finrank ℝ (Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut)) :
    ∀ V ∈ 𝓝 (1 : Matrix d d ℝ), ∀ W ∈ 𝓝 (1 : ∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ),
      ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.attention sees id H dh) 1 θ' x
        = eval (Arch.attention sees id H dh) 1 θ x) →
        ∃ (G : GL d ℝ) (K K' : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ),
          (G : Matrix d d ℝ) ∈ V
            ∧ (fun ℓ i => (K ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)) ∈ W
            ∧ (fun ℓ i => (K' ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)) ∈ W
            ∧ θ' = ((θ.headsQK K).headsVO K').cob (fun _ => G) (fun _ => G) := by
  intro V hVn W hWn
  -- the embedding `(m, Γ, Γ') ↦ (fun _ => m, Γ, Γ')`: the same matrix at every hidden state
  let ι : (Matrix d d ℝ × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)
      × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)) →L[ℝ] (Fin (L + 1) → Matrix d d ℝ)
      × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) :=
    (ContinuousLinearMap.pi fun _ : Fin (L + 1) =>
      ContinuousLinearMap.fst ℝ (Matrix d d ℝ) _).prod (ContinuousLinearMap.snd ℝ _ _)
  -- they form a space of dimension `d² + 2 ∑_ℓ H_ℓ d_{h,ℓ}²`
  have hdimM : Module.finrank ℝ (Matrix d d ℝ × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)
      × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ))
      = Fintype.card d ^ 2 + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2 := by
    rw [Module.finrank_prod, Module.finrank_prod, finrank_headFun_lia, Module.finrank_matrix,
      Module.finrank_self, mul_one, sq, two_mul]
  -- the derivative `(m, Γ, Γ') ↦ cobDir θ (fun _ => m) + headDirQK θ Γ + headDirVO θ Γ'` is
  -- injective: the `E` component `E m` gives `m`, then the heads give `Γ` and `Γ'`
  have hinj : Function.Injective fun p : Matrix d d ℝ × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)
      × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) =>
      cobDir θ (ι p).1 + headDirQK θ (ι p).2.1 + headDirVO θ (ι p).2.2 := by
    rintro ⟨m, Γ, Γ'⟩ ⟨m', Δ, Δ'⟩ h
    have h' : cobDir θ (fun _ => m) + headDirQK θ Γ + headDirVO θ Γ'
        = cobDir θ (fun _ => m') + headDirQK θ Δ + headDirVO θ Δ' := h
    have h0 : θ.E * m = θ.E * m' := by
      have hE0 := congrArg Params.E h'
      change θ.E * m + 0 + 0 = θ.E * m' + 0 + 0 at hE0
      simpa only [add_zero] using hE0
    obtain rfl : m = m' := cancel_left_of_rank_lia θ.E hE h0
    rw [add_assoc, add_assoc] at h'
    obtain ⟨rfl, rfl⟩ := headDir_injective_lia θ hQ hV (add_left_cancel h')
    rfl
  -- the changes of basis inside the heads and then one change of basis at all hidden states
  -- preserve the function (Appendix B and Proposition 3.2 with identity skips)
  have hpres : ∀ (p : Matrix d d ℝ × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)
      × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)) (x : Matrix T dIn ℝ),
      eval (Arch.attention sees id H dh) 1 (cobExpHeads θ (ι p)) x
        = eval (Arch.attention sees id H dh) 1 θ x := by
    intro p x
    have h1 : cobExpHeads θ (ι p)
        = ((θ.headsQK fun ℓ i => expGL (p.2.1 ℓ i)).headsVO fun ℓ i => expGL (p.2.2 ℓ i)).cob
          (fun _ => expGL p.1) (fun _ => expGL p.1) := rfl
    rw [h1]
    exact (eval_cob_residual _ x rfl _).trans
      ((eval_headsVO (θ.headsQK fun ℓ i => expGL (p.2.1 ℓ i))
        (fun ℓ i => expGL (p.2.2 ℓ i)) 1 x).trans (eval_headsQK θ _ 1 x))
  -- `V` is a neighborhood of `1` in the matrices, so the families with first member in `V` form
  -- a neighborhood of `1`
  have hV0 : (fun Y : Fin (L + 1) → Matrix d d ℝ => Y 0) ⁻¹' V
      ∈ 𝓝 (1 : Fin (L + 1) → Matrix d d ℝ) :=
    (continuous_apply (0 : Fin (L + 1))).continuousAt.preimage_mem_nhds hVn
  -- the orbit fills the level set near `θ`
  obtain ⟨U, hU, hUV⟩ := exists_cobExpHeads_of_eval_eq_lia 1 θ ι hinj
    (by rw [hdimM]; exact hfd) hpres _ hV0 W hWn
  refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
  -- `G = exp m`, `K_{ℓ,i} = exp Γ_{ℓ,i}`, `K'_{ℓ,i} = exp Γ'_{ℓ,i}`
  obtain ⟨p, hpV, hpW1, hpW2, rfl⟩ := hUV θ' hθ' heq
  exact ⟨expGL p.1, fun ℓ i => expGL (p.2.1 ℓ i), fun ℓ i => expGL (p.2.2 ℓ i),
    hpV, hpW1, hpW2, rfl⟩

omit [Fintype T] [DecidableEq d] in
/-- Helper (the private `analyticOnNhd_det_uba` of `Dimension/UpperBoundAttention.lean`): the
determinant of a square matrix that depends linearly on the parameters is an analytic function of
the parameters. -/
private theorem analyticOnNhd_det_lia {A : Arch T d L} {n : Type*} [Fintype n] [DecidableEq n]
    (Φ : Params A dIn dOut →ₗ[ℝ] Matrix n n ℝ) :
    AnalyticOnNhd ℝ (fun θ => (Φ θ).det) Set.univ := by
  simp only [Matrix.det_apply']
  exact Finset.analyticOnNhd_fun_sum _ fun σ _ => analyticOnNhd_const.mul
    (Finset.analyticOnNhd_fun_prod _ fun i _ =>
      analyticOnNhd_linear ((Matrix.entryLinearMap ℝ ℝ (σ i) i).comp Φ))

/-- Helper (the private `exists_submatrix_eq_one_uba` of `Dimension/UpperBoundAttention.lean`): a
matrix whose submatrix on the rows `r` and the columns `c` (both injective) is the identity. -/
private theorem exists_submatrix_eq_one_lia {m p n : Type*} [DecidableEq n] {r : n → m}
    (hr : Function.Injective r) {c : n → p} (hc : Function.Injective c) :
    ∃ M : Matrix m p ℝ, M.submatrix r c = 1 := by
  classical
  refine ⟨Matrix.of fun a b => if ∃ x, r x = a ∧ c x = b then 1 else 0, ?_⟩
  ext x y
  simp [Matrix.one_apply, hr.eq_iff, hc.eq_iff]

omit [Fintype T] [DecidableEq d] in
/-- Helper (the private `ae_rank_read_cols_uba` of `Dimension/UpperBoundAttention.lean`): at
generic parameters, `n ≤ d` distinct columns `c` of the read of block `ℓ` form a matrix of rank
`n`: some `n` of its rows form a matrix that is invertible at generic parameters. -/
private theorem ae_rank_read_cols_lia {A : Arch T d L} (μ : Measure (Params A dIn dOut))
    [μ.IsAddHaarMeasure] (ℓ : Fin L) {n : Type*} [Fintype n] [DecidableEq n] {c : n → A.r ℓ}
    (hc : Function.Injective c) (hn : Fintype.card n ≤ Fintype.card d) :
    ∀ᵐ θ ∂μ, ((θ.read ℓ).submatrix id c).rank = Fintype.card n := by
  -- `n` rows `ρ`, and the square submatrix of the read on the rows `ρ` and the columns `c`
  obtain ⟨ρ⟩ := Function.Embedding.nonempty_of_card_le hn
  obtain ⟨M, hM⟩ := exists_submatrix_eq_one_lia ρ.injective hc
  let Φ : Params A dIn dOut →ₗ[ℝ] Matrix n n ℝ :=
    { toFun := fun θ => ((θ.read ℓ).submatrix id c).submatrix ρ id
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  -- it is the identity at the parameter whose read `ℓ` is `M`, so its determinant is not
  -- identically zero, and it is nonzero almost everywhere
  have hne : ∃ θ, (Φ θ).det ≠ 0 := by
    refine ⟨⟨0, Pi.single ℓ M, 0, 0⟩, ?_⟩
    show ((Pi.single (M := fun ℓ => Matrix d (A.r ℓ) ℝ) ℓ M ℓ).submatrix ρ c).det ≠ 0
    rw [Pi.single_eq_same, hM, Matrix.det_one]
    exact one_ne_zero
  filter_upwards [ae_ne_zero_of_analytic μ (analyticOnNhd_det_lia Φ) hne] with θ hθ
  -- an invertible `n × n` submatrix gives rank `≥ n`, and the rank is at most the width `n`
  have h1 : (((θ.read ℓ).submatrix id c).submatrix ρ id).rank = Fintype.card n :=
    Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hθ))
  have h2 : (((θ.read ℓ).submatrix id c).submatrix ρ id).rank
      ≤ ((θ.read ℓ).submatrix id c).rank :=
    Matrix.rank_submatrix_le _ ρ id
  have h3 := Matrix.rank_le_card_width ((θ.read ℓ).submatrix id c)
  omega

omit [DecidableEq d] in
/-- Helper (the private `ae_rank_QV_uba` of `Dimension/UpperBoundAttention.lean`): at generic
parameters the query matrix and the value matrix of every head have rank `d_h`, when `d_h ≤ d`. -/
private theorem ae_rank_QV_lia {χ : Matrix T d ℝ → Matrix T d ℝ}
    (μ : Measure (Params (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut))
    [μ.IsAddHaarMeasure] (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) :
    ∀ᵐ θ ∂μ, (∀ ℓ (i : H ℓ), ((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k)).rank
        = Fintype.card (dh ℓ)) ∧
      ∀ ℓ (i : H ℓ), ((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))).rank
        = Fintype.card (dh ℓ) := by
  -- finitely many conditions, two for each head of each block
  refine (ae_all_iff.2 fun ℓ => ae_all_iff.2 fun i => ?_).and
    (ae_all_iff.2 fun ℓ => ae_all_iff.2 fun i => ?_)
  · exact ae_rank_read_cols_lia μ ℓ (c := fun k : dh ℓ => (i, Sum.inl k))
      (fun _ _ h => Sum.inl_injective (Prod.mk.inj h).2) (hdh ℓ)
  · exact ae_rank_read_cols_lia μ ℓ (c := fun k : dh ℓ => (i, Sum.inr (Sum.inr k)))
      (fun _ _ h => Sum.inr_injective (Sum.inr_injective (Prod.mk.inj h).2)) (hdh ℓ)

/-- Helper (the private `ae_rank_E_uba` of `Dimension/UpperBoundAttention.lean`): at generic
parameters `E` has rank `d`, when `d_in ≥ d`. -/
private theorem ae_rank_E_lia {A : Arch T d L} (μ : Measure (Params A dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn) :
    ∀ᵐ θ ∂μ, θ.E.rank = Fintype.card d := by
  -- `d` rows `ρ` of `E`, invertible at generic parameters
  obtain ⟨ρ⟩ := Function.Embedding.nonempty_of_card_le hdIn
  filter_upwards [ae_isUnit_det_submatrix μ] with θ hθ
  have h1 : (θ.E.submatrix ρ id).rank = Fintype.card d :=
    Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).2 (hθ.2.2.1 ρ))
  have h2 := Matrix.rank_submatrix_le θ.E ρ id
  have h3 := Matrix.rank_le_card_width θ.E
  omega

/-- **Corollary 4.9 of the skips paper for attention blocks without normalization:** for
`d_in, d_out ≥ d ≥ 2`, heads of width `1 ≤ d_h ≤ d` and a mask with a token that sees itself and
another token, at almost every parameter `θ` of the residual network, every `θ'` near `θ` with
the same function is `θ` after changes of basis inside the heads, near the identity, and the
change of basis by one invertible `G` near the identity at all hidden states. -/
theorem ae_exists_cob_heads_of_eval_eq_attention_residual
    (μ : Measure (Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ θ ∂μ, ∀ V ∈ 𝓝 (1 : Matrix d d ℝ), ∀ W ∈ 𝓝 (1 : ∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ),
      ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.attention sees id H dh) 1 θ' x
        = eval (Arch.attention sees id H dh) 1 θ x) →
        ∃ (G : GL d ℝ) (K K' : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ),
          (G : Matrix d d ℝ) ∈ V
            ∧ (fun ℓ i => (K ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)) ∈ W
            ∧ (fun ℓ i => (K' ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)) ∈ W
            ∧ θ' = ((θ.headsQK K).headsVO K').cob (fun _ => G) (fun _ => G) := by
  -- at generic parameters `E` has rank `d`, the query and value matrices of every head have
  -- rank `d_h`, and `fd(θ) = P - d² - s` (Theorem 4.7)
  filter_upwards [ae_rank_E_lia μ hdIn, ae_rank_QV_lia μ hdh,
    ae_funDim_attention_residual μ hd hdIn hdOut hdh hdh0 t₁ t₂ h12 hs2 hs1] with θ hE hQV hfd
  -- Proposition 4.5 at `θ`
  exact exists_cob_heads_of_eval_eq_residual_attention θ hE hQV.1 hQV.2 hfd

end AnyDepth

section OneBlock

variable {H dh : Fin 1 → Type} [∀ ℓ, Fintype (H ℓ)] [∀ ℓ, Fintype (dh ℓ)]
  [∀ ℓ, DecidableEq (dh ℓ)]

/-- **The skipless network of one attention block is locally identifiable at generic
parameters** (Proposition 4.6 with Theorem 5.1 of the dimension paper): for `d_in, d_out ≥ d ≥ 2`,
`H` heads of width `d_h ≤ d` with `H d_h ≥ d` and a mask with a token that sees itself and another
token, at almost every parameter `θ`, every `θ'` near `θ` with the same function is `θ` after
changes of basis inside the heads, near the identity, and a change of basis by invertible `G_0`,
`G_1` near the identity. -/
theorem ae_exists_cob_heads_of_eval_eq_attention_oneBlock
    (μ : Measure (Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : Fintype.card (dh 0) ≤ Fintype.card d)
    (hH : Fintype.card d ≤ Fintype.card (H 0) * Fintype.card (dh 0))
    (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ θ ∂μ, ∀ V ∈ 𝓝 (1 : Fin 2 → Matrix d d ℝ),
      ∀ W ∈ 𝓝 (1 : ∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ), ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.attention sees id H dh) 0 θ' x
        = eval (Arch.attention sees id H dh) 0 θ x) →
        ∃ (G : Fin 2 → GL d ℝ) (K K' : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ),
          (fun ℓ => (G ℓ : Matrix d d ℝ)) ∈ V
            ∧ (fun ℓ i => (K ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)) ∈ W
            ∧ (fun ℓ i => (K' ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)) ∈ W
            ∧ θ' = ((θ.headsQK K).headsVO K').cob G G := by
  -- the write has `H d_h ≥ d` rows, and the heads have width `d_h ≤ d`
  have hw : ∀ ℓ, Fintype.card d
      ≤ Fintype.card ((Arch.attention (T := T) (d := d) sees id H dh).w ℓ) := fun ℓ => by
    obtain rfl := Subsingleton.elim ℓ 0
    show Fintype.card d ≤ Fintype.card (H 0 × dh 0)
    rw [Fintype.card_prod]
    exact hH
  have hdh' : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d := fun ℓ => by
    obtain rfl := Subsingleton.elim ℓ 0
    exact hdh
  -- at generic parameters `E` and the write have rank `d`, the query and value matrices of every
  -- head have rank `d_h`, and `fd(θ) = P - 2 d² - 2 H d_h²` (Theorem 5.1)
  filter_upwards [ae_rank_E_write μ hdIn hw, ae_rank_QV_lia μ hdh',
    ae_funDim_attention_oneBlock μ hd hdIn hdOut hdh hH t₁ t₂ h12 hs2 hs1] with θ hθ hQV hfd
  -- Proposition 4.6 at `θ`, with `L = 1`
  refine exists_cob_heads_of_eval_eq_skipless_attention θ hθ.1 hθ.2 hQV.1 hQV.2 ?_
  rw [Fin.sum_univ_one]
  exact hfd

end OneBlock

end Skips
