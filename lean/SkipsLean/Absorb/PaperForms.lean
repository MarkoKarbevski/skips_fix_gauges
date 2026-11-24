import SkipsLean.Absorb.Networks
import SkipsLean.Absorb.FewerUnits

/-!
# The statements of the absorb paper in the paper's own form

Paper: "Can an MLP Absorb Its Skip Connection Exactly?".

The files `Absorb/Block.lean` to `Absorb/Networks.lean` state the results in a more general form: a
rectangular linear term `M`, any activation with `σ(z) - σ(-z) = c z`, and blocks that vanish at
`0` with derivative `0`. This file states the cases that the paper names, each as an instance of a
general statement:

* Theorem A.4 (ReLU) and Theorem A.7 (GELU): the linear term is the identity.
* Corollary A.10: at generic weights a residual block equals no skipless block of the same width,
  and a skipless block equals no residual block of the same width.
* Theorem 3.1 (ii), first half / Proposition A.11 (i), and Proposition 4.4, for ReLU and for GELU.
* Theorem 4.1 (i): for its two classes of blocks (gated blocks whose gate vanishes at `0` and is
  differentiable there; blocks that are positively homogeneous of degree `k > 1`), and for SwiGLU,
  GeGLU, ReLU² and ReGLU networks, without normalization and under pre-RMSNorm with `ε > 0`.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

/-! ### One block: Theorems A.4, A.7, Corollary A.10, Theorem 3.1 (ii) -/

section OneBlock

variable {d m : Type*} [Fintype d] [DecidableEq d] [Fintype m] [DecidableEq m]

/-- **Theorem A.4 (identity absorption for ReLU).** For a nondegenerate block,
`x + ReLU(x W_read) W_write = ReLU(x W_read') W_write'` for all `x` has a solution of the same
width if and only if `W_read[:,S] W_write[S,:] = -I` for some set `S` of hidden units. The paper's
`d ≥ 2` is not used. -/
theorem relu_absorb_identity_iff (Wr : Matrix d m ℝ) (Ww : Matrix m d ℝ)
    (hnd : Nondegenerate Wr Ww) :
    (∃ (Wr' : Matrix d m ℝ) (Ww' : Matrix m d ℝ),
        ∀ x : d → ℝ, x + vanillaBlock relu Wr Ww x = vanillaBlock relu Wr' Ww' x)
      ↔ ∃ S : Finset m, subProd S Wr Ww = -1 := by
  -- Corollary A.9 with `M = I`
  simpa only [Matrix.vecMul_one] using relu_absorb_same_width_iff Wr Ww hnd 1

/-- **Theorem A.7 (identity absorption for GELU).** For a nondegenerate block,
`x + GELU(x W_read) W_write = GELU(x W_read') W_write'` for all `x` has a solution of the same
width if and only if `W_read[:,S] W_write[S,:] = -I` for some set `S` of hidden units. -/
theorem gelu_absorb_identity_iff (Wr : Matrix d m ℝ) (Ww : Matrix m d ℝ)
    (hnd : Nondegenerate Wr Ww) :
    (∃ (Wr' : Matrix d m ℝ) (Ww' : Matrix m d ℝ),
        ∀ x : d → ℝ, x + vanillaBlock gelu Wr Ww x = vanillaBlock gelu Wr' Ww' x)
      ↔ ∃ S : Finset m, subProd S Wr Ww = -1 := by
  -- Corollary A.9 with `M = I`
  simpa only [Matrix.vecMul_one] using gelu_absorb_same_width_iff Wr Ww hnd 1

/-- **Corollary A.10, first half, for ReLU** (`d ≥ 2`). For generic weights
`x + B(x) = B'(x)` has no solution: a residual block equals no skipless block of the same
width. -/
theorem ae_not_relu_absorb_identity (hd : 2 ≤ Fintype.card d)
    (μ : Measure (Matrix d m ℝ × Matrix m d ℝ)) [μ.IsAddHaarMeasure] :
    ∀ᵐ W ∂μ, ¬ ∃ (Wr' : Matrix d m ℝ) (Ww' : Matrix m d ℝ),
      ∀ x : d → ℝ, x + vanillaBlock relu W.1 W.2 x = vanillaBlock relu Wr' Ww' x := by
  -- Theorem 3.1 (i), second sentence, with `M = I ≠ 0`
  have : Nonempty d := Fintype.card_pos_iff.mp (by omega)
  simpa only [Matrix.vecMul_one] using
    ae_not_relu_absorb_same_width (m := m) hd (1 : Matrix d d ℝ) one_ne_zero μ

/-- **Corollary A.10, first half, for GELU** (`d ≥ 2`). For generic weights
`x + B(x) = B'(x)` has no solution: a residual block equals no skipless block of the same
width. -/
theorem ae_not_gelu_absorb_identity (hd : 2 ≤ Fintype.card d)
    (μ : Measure (Matrix d m ℝ × Matrix m d ℝ)) [μ.IsAddHaarMeasure] :
    ∀ᵐ W ∂μ, ¬ ∃ (Wr' : Matrix d m ℝ) (Ww' : Matrix m d ℝ),
      ∀ x : d → ℝ, x + vanillaBlock gelu W.1 W.2 x = vanillaBlock gelu Wr' Ww' x := by
  -- Theorem 3.1 (i), second sentence, with `M = I ≠ 0`
  have : Nonempty d := Fintype.card_pos_iff.mp (by omega)
  simpa only [Matrix.vecMul_one] using
    ae_not_gelu_absorb_same_width (m := m) hd (1 : Matrix d d ℝ) one_ne_zero μ

/-- **Corollary A.10, second half, for ReLU** (`d ≥ 2`). For generic weights a skipless block
equals no residual block of the same width: `B(x) = x + B'(x)` has no solution `B'`. -/
theorem ae_not_relu_skipless_eq_residual (hd : 2 ≤ Fintype.card d)
    (μ : Measure (Matrix d m ℝ × Matrix m d ℝ)) [μ.IsAddHaarMeasure] :
    ∀ᵐ W ∂μ, ¬ ∃ (Wr' : Matrix d m ℝ) (Ww' : Matrix m d ℝ),
      ∀ x : d → ℝ, vanillaBlock relu W.1 W.2 x = x + vanillaBlock relu Wr' Ww' x := by
  -- Theorem 3.1 (i), second sentence, with `M = -I ≠ 0`: the block absorbs the linear term `-x`
  have : Nonempty d := Fintype.card_pos_iff.mp (by omega)
  have h := ae_not_relu_absorb_same_width (m := m) hd (-1 : Matrix d d ℝ)
    (neg_ne_zero.mpr one_ne_zero) μ
  filter_upwards [h] with W hW hex
  obtain ⟨Wr', Ww', hx⟩ := hex
  refine hW ⟨Wr', Ww', fun x => ?_⟩
  -- `-x + B(x) = -x + (x + B'(x)) = B'(x)`
  rw [hx x, Matrix.vecMul_neg, Matrix.vecMul_one, neg_add_cancel_left]

/-- **Corollary A.10, second half, for GELU** (`d ≥ 2`). For generic weights a skipless block
equals no residual block of the same width: `B(x) = x + B'(x)` has no solution `B'`. -/
theorem ae_not_gelu_skipless_eq_residual (hd : 2 ≤ Fintype.card d)
    (μ : Measure (Matrix d m ℝ × Matrix m d ℝ)) [μ.IsAddHaarMeasure] :
    ∀ᵐ W ∂μ, ¬ ∃ (Wr' : Matrix d m ℝ) (Ww' : Matrix m d ℝ),
      ∀ x : d → ℝ, vanillaBlock gelu W.1 W.2 x = x + vanillaBlock gelu Wr' Ww' x := by
  -- Theorem 3.1 (i), second sentence, with `M = -I ≠ 0`: the block absorbs the linear term `-x`
  have : Nonempty d := Fintype.card_pos_iff.mp (by omega)
  have h := ae_not_gelu_absorb_same_width (m := m) hd (-1 : Matrix d d ℝ)
    (neg_ne_zero.mpr one_ne_zero) μ
  filter_upwards [h] with W hW hex
  obtain ⟨Wr', Ww', hx⟩ := hex
  refine hW ⟨Wr', Ww', fun x => ?_⟩
  -- `-x + B(x) = -x + (x + B'(x)) = B'(x)`
  rw [hx x, Matrix.vecMul_neg, Matrix.vecMul_one, neg_add_cancel_left]

omit [DecidableEq m] in
/-- **Theorem 3.1 (ii), first half / Proposition A.11 (i), for ReLU.** If `W_read` has rank `d`,
a ReLU block with `d` more hidden units computes `x M + B(x)`. The paper takes `M` invertible; the
statement holds for every `M`. -/
theorem exists_relu_block_add_linear (Wr : Matrix d m ℝ) (Ww : Matrix m d ℝ)
    (hr : Wr.rank = Fintype.card d) (M : Matrix d d ℝ) :
    ∃ (Wr' : Matrix d (m ⊕ d) ℝ) (Ww' : Matrix (m ⊕ d) d ℝ),
      ∀ x : d → ℝ, x ᵥ* M + vanillaBlock relu Wr Ww x = vanillaBlock relu Wr' Ww' x := by
  -- the general statement with `ReLU(z) - ReLU(-z) = 1 · z`
  obtain ⟨Wr', Ww', -, h⟩ := exists_vanillaBlock_add_linear (σ := relu) (c := 1)
    (fun z => by rw [one_mul]; exact relu_sub_relu_neg z) one_ne_zero Wr Ww hr M
  exact ⟨Wr', Ww', h⟩

omit [DecidableEq m] in
/-- **Theorem 3.1 (ii), first half / Proposition A.11 (i), for GELU.** If `W_read` has rank `d`,
a GELU block with `d` more hidden units computes `x M + B(x)`. The paper takes `M` invertible; the
statement holds for every `M`. -/
theorem exists_gelu_block_add_linear (Wr : Matrix d m ℝ) (Ww : Matrix m d ℝ)
    (hr : Wr.rank = Fintype.card d) (M : Matrix d d ℝ) :
    ∃ (Wr' : Matrix d (m ⊕ d) ℝ) (Ww' : Matrix (m ⊕ d) d ℝ),
      ∀ x : d → ℝ, x ᵥ* M + vanillaBlock gelu Wr Ww x = vanillaBlock gelu Wr' Ww' x := by
  -- the general statement with `GELU(z) - GELU(-z) = 1 · z`
  obtain ⟨Wr', Ww', -, h⟩ := exists_vanillaBlock_add_linear (σ := gelu) (c := 1)
    (fun z => by rw [one_mul]; exact gelu_sub_gelu_neg z) one_ne_zero Wr Ww hr M
  exact ⟨Wr', Ww', h⟩

end OneBlock

/-! ### Networks: Proposition 4.4 and Theorem 4.1 (i) -/

section Networks

variable {T dIn dOut : Type*} {d : Type} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d]
  [Fintype dIn] [Fintype dOut]
variable {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)] {σ : ℝ → ℝ}

/-- **Proposition 4.4 for ReLU.** Without normalization, a residual ReLU network whose reads all
have rank `d` equals a skipless ReLU network with `d` more hidden units in every block, with the
same embedding and readout. -/
theorem exists_skipless_eq_residual_relu
    (θ : Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut)
    (hr : ∀ ℓ, (θ.read ℓ).rank = Fintype.card d) :
    ∃ θ' : Params (Arch.mlp (T := T) (d := d) relu id (fun ℓ => hid ℓ ⊕ d)) dIn dOut,
      θ'.E = θ.E ∧ θ'.D = θ.D ∧
      ∀ X : Matrix T dIn ℝ,
        eval (Arch.mlp relu id hid) 1 θ X = eval (Arch.mlp relu id (fun ℓ => hid ℓ ⊕ d)) 0 θ' X :=
  exists_skipless_eq_residual_of_rank_read relu_sub_relu_neg θ hr

/-- **Proposition 4.4 for GELU.** Without normalization, a residual GELU network whose reads all
have rank `d` equals a skipless GELU network with `d` more hidden units in every block, with the
same embedding and readout. -/
theorem exists_skipless_eq_residual_gelu
    (θ : Params (Arch.mlp (T := T) (d := d) gelu id hid) dIn dOut)
    (hr : ∀ ℓ, (θ.read ℓ).rank = Fintype.card d) :
    ∃ θ' : Params (Arch.mlp (T := T) (d := d) gelu id (fun ℓ => hid ℓ ⊕ d)) dIn dOut,
      θ'.E = θ.E ∧ θ'.D = θ.D ∧
      ∀ X : Matrix T dIn ℝ,
        eval (Arch.mlp gelu id hid) 1 θ X = eval (Arch.mlp gelu id (fun ℓ => hid ℓ ⊕ d)) 0 θ' X :=
  exists_skipless_eq_residual_of_rank_read gelu_sub_gelu_neg θ hr

/-- The second class of blocks of Theorem 4.1 (i): if every fixed map `f_ℓ` is positively
homogeneous of degree `k > 1` and bounded on the unit sphere, every block vanishes at `0` with
derivative `0` there. The proof of Corollary A.3 uses the bound as "it is `O(‖x‖^k)`"; a
continuous `f_ℓ` has it (`flatAtZero_of_homogeneous_of_continuous`). -/
theorem flatAtZero_of_homogeneous {d : Type*} {A : Arch T d L} {k : ℝ} (hk : 1 < k)
    (hf : ∀ ℓ (lam : ℝ) (M : Matrix T (A.r ℓ) ℝ), 0 < lam → A.f ℓ (lam • M) = lam ^ k • A.f ℓ M)
    (hb : ∀ ℓ, ∃ C : ℝ, ∀ M : Matrix T (A.r ℓ) ℝ, ‖M‖ = 1 → ‖A.f ℓ M‖ ≤ C) :
    A.FlatAtZero :=
  fun ℓ => hasFDerivAt_zero_of_homogeneous hk (A.f ℓ) (hf ℓ) (hb ℓ)

/-- The same for continuous `f_ℓ`: a continuous map is bounded on the unit sphere, which is
compact. Every block whose fixed map applies a continuous activation, or a gate with a continuous
activation, is of this kind. -/
theorem flatAtZero_of_homogeneous_of_continuous {d : Type*} {A : Arch T d L} {k : ℝ} (hk : 1 < k)
    (hf : ∀ ℓ (lam : ℝ) (M : Matrix T (A.r ℓ) ℝ), 0 < lam → A.f ℓ (lam • M) = lam ^ k • A.f ℓ M)
    (hc : ∀ ℓ, Continuous (A.f ℓ)) :
    A.FlatAtZero := by
  refine flatAtZero_of_homogeneous hk hf fun ℓ => ?_
  -- the unit sphere of a finite-dimensional space is compact
  obtain ⟨C, hC⟩ := (isCompact_sphere (0 : Matrix T (A.r ℓ) ℝ) 1).exists_bound_of_continuousOn
    (hc ℓ).continuousOn
  exact ⟨C, fun M hM => hC M (by simpa using hM)⟩

variable [Nonempty T] {L' : ℕ} {d' : Type*} [Fintype d']
variable {hid' : Fin (L' + 1) → Type} [∀ ℓ, Fintype (hid' ℓ)]

/-- **Theorem 4.1 (i) for gated blocks, without normalization.** The gate vanishes at `0` and is
differentiable there. A residual network of such blocks with `E D ≠ 0` equals no skipless network
of such blocks, of any depth `≥ 1`, widths and model dimension. -/
theorem exists_ne_residual_skipless_gated (h0 : σ 0 = 0) (hσ : DifferentiableAt ℝ σ 0)
    (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) (hED : θ.E * θ.D ≠ 0)
    (θ' : Params (Arch.gated (T := T) (d := d') σ id hid') dIn dOut) :
    ∃ X : Matrix T dIn ℝ,
      eval (Arch.gated σ id hid) 1 θ X ≠ eval (Arch.gated σ id hid') 0 θ' X :=
  exists_ne_residual_skipless_of_flatAtZero _ _ rfl rfl (flatAtZero_gated h0 hσ)
    (flatAtZero_gated h0 hσ) θ hED θ'

/-- **Theorem 4.1 (i) for gated blocks, under pre-RMSNorm with `ε > 0`.** -/
theorem exists_ne_residual_skipless_gated_rmsNorm {ε : ℝ} (hε : 0 < ε) (h0 : σ 0 = 0)
    (hσ : DifferentiableAt ℝ σ 0)
    (θ : Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut) (hED : θ.E * θ.D ≠ 0)
    (θ' : Params (Arch.gated (T := T) (d := d') σ (rmsNorm ε) hid') dIn dOut) :
    ∃ X : Matrix T dIn ℝ,
      eval (Arch.gated σ (rmsNorm ε) hid) 1 θ X ≠ eval (Arch.gated σ (rmsNorm ε) hid') 0 θ' X :=
  exists_ne_residual_skipless_of_flatAtZero_rmsNorm hε hε _ _ rfl rfl (flatAtZero_gated h0 hσ)
    (flatAtZero_gated h0 hσ) θ hED θ'

/-- **Theorem 4.1 (i) for positively homogeneous blocks, without normalization.** In both networks
every fixed map `f_ℓ` is positively homogeneous of a degree greater than `1` and bounded on the
unit sphere. A residual network of such blocks with `E D ≠ 0` equals no skipless network of such
blocks, of any depth `≥ 1`, widths and model dimension. -/
theorem exists_ne_residual_skipless_homogeneous (A : Arch T d L) (A' : Arch T d' (L' + 1))
    (hχ : A.χ = id) (hχ' : A'.χ = id) {k k' : ℝ} (hk : 1 < k) (hk' : 1 < k')
    (hf : ∀ ℓ (lam : ℝ) (M : Matrix T (A.r ℓ) ℝ), 0 < lam → A.f ℓ (lam • M) = lam ^ k • A.f ℓ M)
    (hb : ∀ ℓ, ∃ C : ℝ, ∀ M : Matrix T (A.r ℓ) ℝ, ‖M‖ = 1 → ‖A.f ℓ M‖ ≤ C)
    (hf' : ∀ ℓ (lam : ℝ) (M : Matrix T (A'.r ℓ) ℝ), 0 < lam →
      A'.f ℓ (lam • M) = lam ^ k' • A'.f ℓ M)
    (hb' : ∀ ℓ, ∃ C : ℝ, ∀ M : Matrix T (A'.r ℓ) ℝ, ‖M‖ = 1 → ‖A'.f ℓ M‖ ≤ C)
    (θ : Params A dIn dOut) (hED : θ.E * θ.D ≠ 0) (θ' : Params A' dIn dOut) :
    ∃ X : Matrix T dIn ℝ, eval A 1 θ X ≠ eval A' 0 θ' X :=
  exists_ne_residual_skipless_of_flatAtZero A A' hχ hχ' (flatAtZero_of_homogeneous hk hf hb)
    (flatAtZero_of_homogeneous hk' hf' hb') θ hED θ'

/-- **Theorem 4.1 (i) for positively homogeneous blocks, under pre-RMSNorm with `ε > 0`.** -/
theorem exists_ne_residual_skipless_homogeneous_rmsNorm {ε : ℝ} (hε : 0 < ε)
    (A : Arch T d L) (A' : Arch T d' (L' + 1))
    (hχ : A.χ = rmsNorm ε) (hχ' : A'.χ = rmsNorm ε) {k k' : ℝ} (hk : 1 < k) (hk' : 1 < k')
    (hf : ∀ ℓ (lam : ℝ) (M : Matrix T (A.r ℓ) ℝ), 0 < lam → A.f ℓ (lam • M) = lam ^ k • A.f ℓ M)
    (hb : ∀ ℓ, ∃ C : ℝ, ∀ M : Matrix T (A.r ℓ) ℝ, ‖M‖ = 1 → ‖A.f ℓ M‖ ≤ C)
    (hf' : ∀ ℓ (lam : ℝ) (M : Matrix T (A'.r ℓ) ℝ), 0 < lam →
      A'.f ℓ (lam • M) = lam ^ k' • A'.f ℓ M)
    (hb' : ∀ ℓ, ∃ C : ℝ, ∀ M : Matrix T (A'.r ℓ) ℝ, ‖M‖ = 1 → ‖A'.f ℓ M‖ ≤ C)
    (θ : Params A dIn dOut) (hED : θ.E * θ.D ≠ 0) (θ' : Params A' dIn dOut) :
    ∃ X : Matrix T dIn ℝ, eval A 1 θ X ≠ eval A' 0 θ' X :=
  exists_ne_residual_skipless_of_flatAtZero_rmsNorm hε hε A A' hχ hχ'
    (flatAtZero_of_homogeneous hk hf hb) (flatAtZero_of_homogeneous hk' hf' hb') θ hED θ'

/-- **Theorem 4.1 (i) for SwiGLU networks** (gate SiLU), without normalization. -/
theorem exists_ne_residual_skipless_swiglu
    (θ : Params (Arch.gated (T := T) (d := d) silu id hid) dIn dOut) (hED : θ.E * θ.D ≠ 0)
    (θ' : Params (Arch.gated (T := T) (d := d') silu id hid') dIn dOut) :
    ∃ X : Matrix T dIn ℝ,
      eval (Arch.gated silu id hid) 1 θ X ≠ eval (Arch.gated silu id hid') 0 θ' X :=
  -- SiLU vanishes at `0` and is differentiable there
  exists_ne_residual_skipless_gated (by rw [silu, zero_div]) (hasDerivAt_silu 0).differentiableAt
    θ hED θ'

/-- **Theorem 4.1 (i) for SwiGLU networks** (gate SiLU), under pre-RMSNorm with `ε > 0`. -/
theorem exists_ne_residual_skipless_swiglu_rmsNorm {ε : ℝ} (hε : 0 < ε)
    (θ : Params (Arch.gated (T := T) (d := d) silu (rmsNorm ε) hid) dIn dOut)
    (hED : θ.E * θ.D ≠ 0)
    (θ' : Params (Arch.gated (T := T) (d := d') silu (rmsNorm ε) hid') dIn dOut) :
    ∃ X : Matrix T dIn ℝ,
      eval (Arch.gated silu (rmsNorm ε) hid) 1 θ X
        ≠ eval (Arch.gated silu (rmsNorm ε) hid') 0 θ' X :=
  exists_ne_residual_skipless_gated_rmsNorm hε (by rw [silu, zero_div])
    (hasDerivAt_silu 0).differentiableAt θ hED θ'

/-- **Theorem 4.1 (i) for GeGLU networks** (gate GELU), without normalization. -/
theorem exists_ne_residual_skipless_geglu
    (θ : Params (Arch.gated (T := T) (d := d) gelu id hid) dIn dOut) (hED : θ.E * θ.D ≠ 0)
    (θ' : Params (Arch.gated (T := T) (d := d') gelu id hid') dIn dOut) :
    ∃ X : Matrix T dIn ℝ,
      eval (Arch.gated gelu id hid) 1 θ X ≠ eval (Arch.gated gelu id hid') 0 θ' X :=
  -- GELU vanishes at `0` and is differentiable there
  exists_ne_residual_skipless_gated (by rw [gelu, zero_mul]) (hasDerivAt_gelu 0).differentiableAt
    θ hED θ'

/-- **Theorem 4.1 (i) for GeGLU networks** (gate GELU), under pre-RMSNorm with `ε > 0`. -/
theorem exists_ne_residual_skipless_geglu_rmsNorm {ε : ℝ} (hε : 0 < ε)
    (θ : Params (Arch.gated (T := T) (d := d) gelu (rmsNorm ε) hid) dIn dOut)
    (hED : θ.E * θ.D ≠ 0)
    (θ' : Params (Arch.gated (T := T) (d := d') gelu (rmsNorm ε) hid') dIn dOut) :
    ∃ X : Matrix T dIn ℝ,
      eval (Arch.gated gelu (rmsNorm ε) hid) 1 θ X
        ≠ eval (Arch.gated gelu (rmsNorm ε) hid') 0 θ' X :=
  exists_ne_residual_skipless_gated_rmsNorm hε (by rw [gelu, zero_mul])
    (hasDerivAt_gelu 0).differentiableAt θ hED θ'

/-- **Theorem 4.1 (i) for ReLU² networks**, without normalization. -/
theorem exists_ne_residual_skipless_reluSq
    (θ : Params (Arch.mlp (T := T) (d := d) reluSq id hid) dIn dOut) (hED : θ.E * θ.D ≠ 0)
    (θ' : Params (Arch.mlp (T := T) (d := d') reluSq id hid') dIn dOut) :
    ∃ X : Matrix T dIn ℝ,
      eval (Arch.mlp reluSq id hid) 1 θ X ≠ eval (Arch.mlp reluSq id hid') 0 θ' X :=
  exists_ne_residual_skipless_of_flatAtZero _ _ rfl rfl flatAtZero_mlp_reluSq
    flatAtZero_mlp_reluSq θ hED θ'

/-- **Theorem 4.1 (i) for ReLU² networks**, under pre-RMSNorm with `ε > 0`. -/
theorem exists_ne_residual_skipless_reluSq_rmsNorm {ε : ℝ} (hε : 0 < ε)
    (θ : Params (Arch.mlp (T := T) (d := d) reluSq (rmsNorm ε) hid) dIn dOut)
    (hED : θ.E * θ.D ≠ 0)
    (θ' : Params (Arch.mlp (T := T) (d := d') reluSq (rmsNorm ε) hid') dIn dOut) :
    ∃ X : Matrix T dIn ℝ,
      eval (Arch.mlp reluSq (rmsNorm ε) hid) 1 θ X
        ≠ eval (Arch.mlp reluSq (rmsNorm ε) hid') 0 θ' X :=
  exists_ne_residual_skipless_of_flatAtZero_rmsNorm hε hε _ _ rfl rfl flatAtZero_mlp_reluSq
    flatAtZero_mlp_reluSq θ hED θ'

/-- **Theorem 4.1 (i) for ReGLU networks** (gate ReLU), without normalization. -/
theorem exists_ne_residual_skipless_reglu
    (θ : Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut) (hED : θ.E * θ.D ≠ 0)
    (θ' : Params (Arch.gated (T := T) (d := d') relu id hid') dIn dOut) :
    ∃ X : Matrix T dIn ℝ,
      eval (Arch.gated relu id hid) 1 θ X ≠ eval (Arch.gated relu id hid') 0 θ' X :=
  exists_ne_residual_skipless_of_flatAtZero _ _ rfl rfl flatAtZero_gated_relu
    flatAtZero_gated_relu θ hED θ'

/-- **Theorem 4.1 (i) for ReGLU networks** (gate ReLU), under pre-RMSNorm with `ε > 0`. -/
theorem exists_ne_residual_skipless_reglu_rmsNorm {ε : ℝ} (hε : 0 < ε)
    (θ : Params (Arch.gated (T := T) (d := d) relu (rmsNorm ε) hid) dIn dOut)
    (hED : θ.E * θ.D ≠ 0)
    (θ' : Params (Arch.gated (T := T) (d := d') relu (rmsNorm ε) hid') dIn dOut) :
    ∃ X : Matrix T dIn ℝ,
      eval (Arch.gated relu (rmsNorm ε) hid) 1 θ X
        ≠ eval (Arch.gated relu (rmsNorm ε) hid') 0 θ' X :=
  exists_ne_residual_skipless_of_flatAtZero_rmsNorm hε hε _ _ rfl rfl flatAtZero_gated_relu
    flatAtZero_gated_relu θ hED θ'

end Networks

end Skips
