STATUS: complete

# Thirty-second audit, part A, of Lean statements against the papers (25 November 2026)

Subject: `Dimension/FunctionalBiasesKinks.lean`, `Symmetry/BiasesFlatKinks.lean`,
`Symmetry/InsideBlocksBiases.lean`, `Symmetry/BiasesRescaleCount.lean`,
`OneBlock/KeepsProductsBiases.lean`, `Residual/SmallWritesBiases.lean`,
`Residual/DepthMlpBiases.lean`, `Residual/DepthGatedBiases.lean` (46 theorems, 6 definitions).

Commit of `/home/claude/lp` read at the start: `49f38c2` (branch `lean-plus`; the stub of an
earlier, stopped reader named `aa7237b`; the branch had moved). None of the eight files has `sorry`
(`grep -c sorry`: 0 for each).

Rules: those of the twenty-first audit, part A. Scratch work in `/home/claude/audit32a_2/`.
Checks are saved one at a time; each says whether it was done by reading, by compiling a copy, or by
a computation.

## Part 1

### Check 7 (first half): registrations and axioms (by reading and by compiling a copy)

Public theorems of the eight files (by `grep` of the declarations, private helpers left out):
3 + 4 + 7 + 9 + 4 + 3 + 8 + 8 = 46, as the brief says; definitions `InsideBlocksB`,
`rescaleDirMlpB`, `rescaleDirB`, `rescaleDirGateB`, `smallWritesB`, `smallWritesLimitB`.

- All eight files are imported by `SkipsLean.lean` (lines 370 to 383).
- Each of the 46 theorems has exactly one line `#print axioms Skips.<name>` in
  `checks/Axioms.lean` (searched name by name; the two names `funDimB_add_le_residual_gated` and
  `funDimB_add_le_skipless_gated` are at lines 2037 and 2038, the other matches of their prefix are
  the `_gate` forms).
- A copy `/home/claude/audit32a_2/Ax32a.lean` (imports of the eight modules and the 46 `#print axioms` lines),
  compiled with `lake env lean` against the current build: every one of the 46 depends on
  `[propext, Classical.choice, Quot.sound]` only. No `sorryAx`.

Verdict: the registrations are complete and the axioms are the standard three. The sentences of the
index rows are checked in the second half of this check, after checks 1 to 6.

### Check 1. Without differentiability (`Dimension/FunctionalBiasesKinks.lean`, `Symmetry/BiasesFlatKinks.lean`)

```lean
theorem mem_flatB_of_hasDerivAt' (γ : ℝ → ParamsB A dIn dOut) (η : ParamsB A dIn dOut)
    (hγ : HasDerivAt γ η 0) (hγ0 : γ 0 = p)
    (hconst : ∀ᶠ τ in 𝓝 (0 : ℝ), ∀ x : Matrix T dIn ℝ,
      evalB A S (γ τ).1 (γ τ).2 x = evalB A S p.1 p.2 x) :
    η ∈ flatB A S p
theorem funDimB_add_finrank_flatB' :
    funDimB A S p + Module.finrank ℝ (flatB A S p) = Module.finrank ℝ (ParamsB A dIn dOut)
theorem funDimB_add_finrank_le_of_le_flatB' (V : Submodule ℝ (ParamsB A dIn dOut))
    (hV : V ≤ flatB A S p) :
    funDimB A S p + Module.finrank ℝ V ≤ Module.finrank ℝ (ParamsB A dIn dOut)
theorem cobDirB_mem_flatB_skipless' (hA : A.χ = id) (X : Fin (L + 1) → Matrix d d ℝ) :
    cobDirB p X ∈ flatB A 0 p
theorem cobDirB_const_mem_flatB_residual' (hA : A.χ = id) (X : Matrix d d ℝ) :
    cobDirB p (fun _ => X) ∈ flatB A 1 p
theorem translateDir_mem_flatB' (hA : A.χ = id) (g : Fin (L + 1) → d → ℝ) :
    ((0, translateDir p.1 g) : ParamsB A dIn dOut) ∈ flatB A 1 p
theorem translateAtDir_mem_flatB' (hA : A.χ = id) (g : Fin (L + 1) → d → ℝ) :
    ((0, translateAtDir p.1 g) : ParamsB A dIn dOut) ∈ flatB A 0 p
```

**True for every network? By reading (statements and proofs) and by compiling.** The three general
statements have no hypothesis on `A`, `S` or `p` (any `Arch`, any stream matrices, any `χ`). They are
true as stated: `flatB A S p = ⨅ x, ker (fderiv ℝ (q ↦ evalB A S q.1 q.2 x) p)`, and Mathlib's
`fderiv` is `0` at a point where the map is not differentiable, so (i) along a curve that keeps the
function the chain rule gives `0` at an input where the output is differentiable and the convention
gives `0` at the others; (ii) a batch is differentiable at `p` exactly when every one of its inputs is
(`differentiableAt_pi`), and a batch that is not has a Jacobian `0`; among the batches of
differentiable inputs one of least kernel has kernel `flatB`, and rank–nullity gives `fd + dim K = P`;
(iii) follows. The proofs are the twins of the forms with a prime of `Dimension/Functional.lean`, and
they compile with the standard axioms only (check 7).

**Which inputs Lean uses.** For Lean, an input `x` puts a condition on a flat direction exactly when
`(θ, b) ↦ F(θ, b, x)` is differentiable at `p`; `funDimB` is the largest rank over batches of such
inputs (a batch with one other input has rank `0`). The paper (Appendix B, "Notation and flat
directions"): "`F(θ, x)` is differentiable in `θ` at the inputs `x` at which no hidden unit sits at its
kink […] and "every input" means every such input". Every input of the paper's set is in Lean's set
(off the kinks the network is a composition of smooth maps near `p`). Lean's set can be larger:

- ReLU² is `C¹`, so the output of a ReLU² network is differentiable in the parameters at every input:
  Lean uses all inputs, the paper only those off the kinks;
- a ReLU unit at its kink at `x` whose output does not reach the readout (for example a row `a_i = 0`
  of `A = W_write D` in one skipless block), and a ReGLU unit whose gate and value both vanish at `x`
  (`max(z, 0) w` is differentiable at `(0, 0)`).

At such an extra input `x_0` the condition is, as far as I can see, the limit of the conditions at the
inputs of the paper's set near `x_0` (for ReLU²: `D_θ F(θ, x)` is continuous in `x`; for a ReLU or ReGLU
unit at its kink at a differentiable input, the terms of that unit tend to `0` from both sides), so
where the paper's set is dense the two spaces `K(θ)` agree. I checked this by hand for one block and
for units of a later block, not as a proof for every depth. Where the paper's set is not dense (a unit
with read column `0` and read bias `0` sits at its kink at every input) the paper's "every such input"
is an empty condition; Lean then has `flatB = ⊤` and `fd = 0` for ReLU (no input is differentiable when
the unit's row reaches the readout), and the actual kernel for ReLU² (all inputs differentiable). The
paper states its results at generic parameters, where its set is open and of full measure, so this
difference does not reach a statement of the paper. Verdict for the definitions with kinks: SAME at
parameters where no unit is at its kink on an open set of inputs; at others Lean's convention decides,
and the paper says nothing.

**The four statements on flat directions, by reading.** They are the four statements of
`Symmetry/BiasesFlat.lean` (thirty-first audit, check 5: the directions are the derivatives of the
changes of basis and translations and the directions of Lemma B.2) with the hypothesis
`hf : ∀ ℓ, Differentiable ℝ (A.f ℓ)` removed and nothing else changed; the proofs use the exact
symmetries (`evalB_cob`, the translations) through `mem_flatB_of_hasDerivAt'`. True for any blocks.
Lemma A.8 has no hypothesis on the kind of block: SAME (LEAN STRONGER than the twins, which ask
differentiable blocks).

**Is `χ = id` needed? By a computation** (`/home/claude/audit32a_2/c1c3.py`; tanh, 2 blocks of 4 units,
`d = 3`, inputs of two tokens, the derivative of the output along the direction computed by forward
mode in float64, largest entry over 6 inputs):

| | no normalization | pre-RMSNorm, `ε = 1` |
|---|---|---|
| residual, `cobDirB p (X, X, X)`, `X` random | `7.1e-15` | `2.59` |
| residual, the same with `X` antisymmetric | `1.1e-14` | `3.6e-15` |
| residual, `translateDir θ g` | `0` | `5.17` |
| skipless, `cobDirB p X`, `X_ℓ` random | `4.9e-15` | `2.76` |
| skipless, `X_ℓ` antisymmetric | `6.6e-15` | `2.7e-15` |
| skipless, `translateAtDir θ g` | `0` | `1.66` |

So under RMSNorm the translations are not flat and the changes of basis are flat only for orthogonal
directions: for the statements as written (every `X`, every `g`) `χ = id` is needed. The paper states
Lemma A.8 "without normalization".

Verdict of check 1: the three general statements are **true for every network** (SAME as the
paper's "`fd = P − dim K(θ)`" and its two uses); Lean's set of inputs contains the paper's and is
larger at some parameters (ReLU² everywhere; units at a kink that do not reach the output), with the
same flat directions wherever the paper's set is dense; the four statements on flat directions are
**SAME** as Lemma A.8 (and Proposition A.1 (ii)) for any blocks, and `χ = id` is needed.

### Check 2. `InsideBlocksB` against the paper's symmetries inside blocks with biases

```lean
def InsideBlocksB (A : Arch T d L) (p η : ParamsB A dIn dOut) : Prop :=
  ∃ γ : ℝ → ParamsB A dIn dOut, γ 0 = p ∧ HasDerivAt γ η 0 ∧
    ∀ᶠ τ in 𝓝 (0 : ℝ), (γ τ).1.E = p.1.E ∧ (γ τ).1.D = p.1.D ∧ (γ τ).2.E = p.2.E ∧
      (γ τ).2.D = p.2.D ∧
      ∀ ℓ (n : Matrix T d ℝ),
        A.f ℓ (n * (γ τ).1.read ℓ + Matrix.of fun _ => (γ τ).2.read ℓ) * (γ τ).1.write ℓ
            + Matrix.of (fun _ => (γ τ).2.write ℓ)
          = A.f ℓ (n * p.1.read ℓ + Matrix.of fun _ => p.2.read ℓ) * p.1.write ℓ
            + Matrix.of fun _ => p.2.write ℓ
theorem InsideBlocksB.mem_flatB (h : InsideBlocksB A p η) (S : Fin L → Matrix d d ℝ) :
    η ∈ flatB A S p
```

**By reading.** The definition asks an exact symmetry along a curve, differentiable at `0`, that keeps
`E`, `D`, `b_E`, `b_D` and the map of every block on every matrix `n` of normalized states. Since the
map is kept for every `n`, the hidden states `h_ℓ = S_ℓ h_{ℓ−1} + B_ℓ(χ(h_{ℓ−1}))` and the output are
kept for every stream `S` and every `χ` (the helper `evalB_eq_of_blocks_ibb` is this induction), and
`mem_flatB_of_hasDerivAt'` gives flatness with no hypothesis of differentiability.
`InsideBlocksB.mem_flatB` is true as stated, for every `S` and `χ`; the four statements
`E_eq_zero`, `D_eq_zero`, `biasE_eq_zero`, `biasD_eq_zero` are the derivative at `0` of a component
that is constant near `0`: true.

**The rescalings of Step 3 are instances** (`insideBlocksB_rescaleDirMlpB`, `insideBlocksB_rescaleDirB`,
`insideBlocksB_rescaleDirGateB`, by reading): the curves are the exact rescalings of
`Symmetry/BiasesRescale.lean` with `c_i = e^{τ α_i}`, which keep `E`, `D`, `b_E`, `b_D` and each block
map (the read column and the read bias of a unit are scaled together, so the pre-activation is scaled
as a whole; the write bias is not touched); the derivatives at `0` are the directions of check 4.

**The paper's symmetries of an attention block with biases would be instances. By reading and by a
computation** (`/home/claude/audit32a_2/attn.py`, the block map of `Arch.attention` with biases,
`n ↦ f(n W_read + b_read) W_write + b_write`, transcribed from `Network/Attention.lean`; `T = 4`,
`d = 3`, two heads of dimension 2; 20 random `n`, two values of `τ`). A shift of the key biases of a
head by `τ δ` adds `⟨q_t, δ⟩/√d_h` to every score of row `t`, which the softmax ignores: the block map
changes by at most `1.1e-14` (no mask) and `8.0e-15` (causal mask). The value biases moved into the
output bias (`b_V ↦ b_V − τ δ`, `b_write ↦ b_write + τ δ W_O`; each row of weights sums to `1`): at most
`1.1e-14`; with the write bias left as it was the map changes by `17` and `14.5`. So both curves keep
`E`, `D`, `b_E`, `b_D` and the block map, and their velocities are `InsideBlocksB` directions; the second
changes the write bias, which is why the kept map has to include `b_write`. (For a mask relation under
which a token sees no token, a row of weights is `0` and the second curve is not a symmetry; the masks
of the paper, none and causal, have every token see itself.) At `49f38c2` no statement with biases for
attention blocks used `InsideBlocksB`; at `6fab629` (the commit at the end of this audit) the new file
`Symmetry/AttentionHeadsBiases.lean` states the key shifts and the head directions as `InsideBlocksB`
directions (`keyShiftDir`, `headDirQKB`, `headDirVOB`; not read in this audit, which confirms only
that the definition admits them).

Verdict of check 2: **SAME** as the paper's "symmetries inside blocks" with biases (Lemma A.8, Step 3),
and general enough for the attention biases of the paper; `InsideBlocksB.mem_flatB` is true for every
stream and every `χ`. The definition is a Lean device (the paper has no definition of a symmetry inside
a block); it holds only exact symmetries, not directions that are flat to first order (a dead unit's
read column, for example, is flat but not an `InsideBlocksB` direction).

### Check 3. The two bounds with `V` against Lemma A.8

```lean
theorem funDimB_add_le_residual_of_insideBlocksB (hA : A.χ = id)
    (V : Submodule ℝ (ParamsB A dIn dOut))
    (hV : V ≤ Submodule.span ℝ {η | InsideBlocksB A p η})
    (hrw : ∀ η ∈ V, ∀ ℓ, η.1.read ℓ = 0 → η.2.read ℓ = 0 → η.1.write ℓ = 0 ∧ η.2.write ℓ = 0)
    (hE : p.1.E.rank = Fintype.card d) :
    funDimB A 1 p + (Fintype.card d ^ 2 + (L + 1) * Fintype.card d + Module.finrank ℝ V)
      ≤ Module.finrank ℝ (ParamsB A dIn dOut)
theorem funDimB_add_le_skipless_of_insideBlocksB (hA : A.χ = id) (V …) (hV …) (hrw …)
    (hE : p.1.E.rank = Fintype.card d) (hw : ∀ ℓ, (p.1.write ℓ).rank = Fintype.card d) :
    funDimB A 0 p + ((L + 1) * (Fintype.card d ^ 2 + Fintype.card d) + Module.finrank ℝ V)
      ≤ Module.finrank ℝ (ParamsB A dIn dOut)
```

**True as stated? By reading.** Both are proved (no `sorry`, standard axioms). The proof: the linear
map `((X, g), v) ↦ cobDirB + translate(At)Dir + v` has flat range (check 1, check 2, and `flatB` is a
subspace) and is injective: `E` of rank `d` gives `X_0` from `η_E = E X_0` (`v_E = 0`), then `g_0`
from the embedding bias (`v_{b_E} = 0`); block by block the read and the read bias give those of `v`,
`hrw` then gives the write and the write bias of `v`, and (skipless) the write of rank `d` gives
`X_{ℓ+1}`, the write bias `g_{ℓ+1}`. This is the paper's counting argument ("These `L + 1` translations
move the biases in independent directions"; Step 3: "The two kinds are independent"). Against
Lemma A.8: with `dim V = s` these are "`d_model² + (L + 1) d_model + s`, against
`(L + 1)(d_model² + d_model) + s` without skips" as upper bounds on the functional dimension (the form of
Theorem 4.2), with `P` counting the biases; the lemma's own statement (the dimension of a group) is not
stated, as the index says. Verdict: SAME as the count, in the form of bounds; PART in that the lemma's
group is not stated.

**`hE` and `hw`.** With `V = 0` (allowed: `hrw` holds trivially) the two statements are the bounds of
`Symmetry/BiasesFlat.lean` without differentiability; the thirty-first audit (check 5) gave exact
examples in which these bounds fail without `hE` (residual: rank `5` against `2`) and without `hw`
(skipless: rank `6` against `2`). So both are needed here too.

**`hrw`, skipless bound: needed. An exact example, checked by a computation.** `A = Arch.mlp 0 id hid`
(the activation `σ ≡ 0`, allowed since the statement is for any blocks), `L = 2`, `d = d_in = d_out = 1`,
one unit per block, `E = (e)`, `W_write^ℓ = (w_ℓ)` with `e, w_0, w_1 ≠ 0` (so `hE` and `hw` hold),
everything else arbitrary. Each block map is `n ↦ 0 · W_write + b_write = b_write`, so moving
`W_read^ℓ`, `b_read^ℓ` or `W_write^ℓ` along a straight line is an `InsideBlocksB` direction; let `V` be the
span of these six directions (`dim V = 6`). `P = 12`. The output is `b_write^1 D + b_D`, constant in
`x`, so `fd = 1` (computed: rank `1` on 20 inputs, next singular value `1e-16` of the first). The bound
would give `fd + (L + 1)(d² + d) + dim V = 1 + 3·2 + 6 = 13 ≤ 12`: false. Every hypothesis but `hrw` holds; `hrw`
fails (the direction of `W_write^0` has read and read bias `0`). In general, with `σ ≡ 0`,
`d_in = d_out = d` and any widths, the bound would say `(L + 1) d ≤ d_in + d_out`, false for every
`L ≥ 2`. Here the cause is that `W_write X_1` (a change of basis at `h_1`) and the free write of block `0`
are the same directions. For the blocks of the paper `hrw` holds for the rescalings when no read column
vanishes (check 4).

**`hrw`, residual bound: why it is asked, and when it is not needed. By reading.** In the residual
bound one matrix `X` serves all hidden states, and `η_E = E X` with `v_E = 0` gives `X = 0`; so the only
possible overlap of `V` with the changes of basis and translations is a translation that is also a span
of symmetries inside blocks. At the first block `ℓ` with `g_{ℓ+1} ≠ 0` such a direction has read `0`,
read bias `−(g_0 + … + g_ℓ) W_read = 0` and write `0`, and write bias `g_{ℓ+1} ≠ 0`: exactly what `hrw`
excludes. Without biases there are no translations, so after `X = 0` there is nothing left to overlap,
which is why the twin needs no such hypothesis. With biases, `hrw` is not needed whenever every block
map, at some `n`, is differentiable in the parameters of the block at `p`: each `InsideBlocksB`
direction then satisfies the linear condition `D(block map at n) η = 0`, which passes to the span, and a
direction whose only component in block `ℓ` is a write bias `c` gives `c = 0`. ReLU-type blocks are
differentiable off their kinks; at parameters where some unit has read column `0` and read bias `0`
(so that it sits at its kink at every `n`) a ReLU block still gives `c = 0`, because a two-sided
directional derivative of `∑_i max(z_i, 0) a_i` equals half of the linear term. So for the blocks of the
paper the residual bound holds without `hrw`. I did not find, and did not look long for, an exotic block
(a map not differentiable in its parameters at any `n`, as `n ↦ φ(b_read) a` with `φ` odd, positively
homogeneous and not linear) for which the residual bound fails without `hrw`: such a block puts a pure
write-bias direction into the span of `InsideBlocksB`, but in the cases I counted the flat space then
grows by more (the output is not differentiable, or invisible directions of the stream appear).

Verdict of check 3: both bounds are **true as stated** and are Lemma A.8's count with `s = dim V`, as
bounds (**SAME** in content; the group itself is not stated). `hE` and `hw` are needed; `hrw` is
**needed for the skipless bound** (exact example above, rank `1` against a bound that asks
`13 ≤ 12`); for the residual bound it is needed only for blocks whose map is nowhere differentiable in
its parameters, and not for any block of the paper.

### Check 4. The count for the kinds of block (`Symmetry/BiasesRescaleCount.lean`)

```lean
def rescaleDirMlpB (k : ℕ) (p : ParamsB (Arch.mlp σ χ hid) dIn dOut) (α : ∀ ℓ, hid ℓ → ℝ) :=
  (rescaleDirMlp k p.1 α, { E := 0, read := fun ℓ i => α ℓ i * p.2.read ℓ i, write := fun _ => 0, D := 0 })
def rescaleDirB (p : ParamsB (Arch.gated σ χ hid) dIn dOut) (α : ∀ ℓ, hid ℓ → ℝ) :=
  (rescaleDir p.1 α, { E := 0, read := fun ℓ => Sum.elim (fun _ => 0)
      (fun i => -(α ℓ i) * p.2.read ℓ (Sum.inr i)), write := fun _ => 0, D := 0 })
def rescaleDirGateB (k : ℕ) (p : ParamsB (Arch.gated σ χ hid) dIn dOut) (β : ∀ ℓ, hid ℓ → ℝ) :=
  (rescaleDirGate k p.1 β, { E := 0, read := fun ℓ => Sum.elim
      (fun i => β ℓ i * p.2.read ℓ (Sum.inl i)) (fun _ => 0), write := fun _ => 0, D := 0 })
-- on the weights (Dimension/RescalingMlp.lean, Rescaling.lean, RescalingGate.lean):
--   rescaleDirMlp k θ α : read column i × α_i, write row i × (−k α_i)
--   rescaleDir θ α      : gate column 0, value column i × (−α_i), write row i × α_i
--   rescaleDirGate k θ β: gate column i × β_i, value column 0, write row i × (−k β_i)
theorem funDimB_add_le_residual_mlp_rescale {k : ℕ}
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (p : ParamsB (Arch.mlp σ id hid) dIn dOut)
    (hE : p.1.E.rank = Fintype.card d) (hc : ∀ ℓ i, (fun a => p.1.read ℓ a i) ≠ 0) :
    funDimB (Arch.mlp σ id hid) 1 p
        + (Fintype.card d ^ 2 + (L + 1) * Fintype.card d + ∑ ℓ, Fintype.card (hid ℓ))
      ≤ Module.finrank ℝ (ParamsB (Arch.mlp σ id hid) dIn dOut)
-- skipless: + hw, and (L + 1) * (d ^ 2 + d); gated: hv (no value column vanishes), s = ∑ hid;
-- gated with a homogeneous gate: hσ, hv, hg (no gate column vanishes), s = 2 ∑ hid
```

**The three directions, by reading, against Step 3 and Lemma B.3.**

| | read column of unit `i` | read bias of unit `i` | write row of unit `i` | paper |
|---|---|---|---|---|
| `rescaleDirMlpB k p α` | `α_i c_i` | `α_i β_i` | `−k α_i a_i` | "scales column `i` of `W_read` and entry `i` of `b_read` by `λ_i` and row `i` of `W_write` by `−λ_i` for ReLU, by `−2 λ_i` for ReLU²" (`k = 1`, `k = 2`); Lemma B.3: "`(ψ_{c_i}, ψ_{β_i}) = λ_i (c_i, β_i)` and `ψ_{a_i} = −λ_i a_i`", "`−2 λ_i a_i`" |
| `rescaleDirB p α` | gate `0`; value `−α_i e_i` | gate `0`; value `−α_i β_i′` | `α_i a_i` | "for SwiGLU and GeGLU, `ψ_{c_i} = 0`, `ψ_{β_i} = 0`, `(ψ_{e_i}, ψ_{β_i′}) = −α_i (e_i, β_i′)` and `ψ_{a_i} = α_i a_i`" |
| `rescaleDirGateB k p β` | gate `β_i c_i`; value `0` | gate `β_i β_i`; value `0` | `−k β_i a_i` | ReGLU (`k = 1`): "`(ψ_{c_i}, ψ_{β_i}) = λ_i (c_i, β_i)`, `(ψ_{e_i}, ψ_{β_i′}) = −α_i (e_i, β_i′)` and `ψ_{a_i} = (α_i − λ_i) a_i`" = `rescaleDirB α + rescaleDirGateB 1 λ` |

Signs and factors agree; the bias entry that moves is the read bias of the unit (gate bias with the
gate, value bias with the value), by the factor of its read column; `E`, `D`, `b_E`, the write biases and
`b_D` do not move. (Here `a_i` is the row of `W_write`; Lemma B.3 speaks of the row of `A = W_write D`,
which moves by the same factor.) The three statements `insideBlocksB_…` are proved with the exact
curves `c_i = e^{τ α_i}` of `Symmetry/BiasesRescale.lean` (thirty-first audit, check 7, SAME), whose
velocities at `0` are these directions. SAME.

**The six bounds, by reading.** The paper (Step 3): "`s` is the number of rescalings: `d_hidden` for
ReLU, ReLU², SwiGLU and GeGLU, `2 d_hidden` for ReGLU, none for tanh and GELU", and Lemma A.8's
`d_model² + (L + 1) d_model + s`, `(L + 1)(d_model² + d_model) + s`. Lean: `s = ∑_ℓ d_hidden,ℓ` for MLP
blocks with an activation positively homogeneous of any degree `k` (ReLU, ReLU²), `s = ∑_ℓ d_hidden,ℓ`
for gated blocks with any gate (SwiGLU, GeGLU; for ReGLU this counts only the values), and
`s = 2 ∑_ℓ d_hidden,ℓ` for gated blocks with a positively homogeneous gate (ReGLU), each with skips
(`hE`) and without (`hE`, `hw`). Each is `funDimB_add_le_…_of_insideBlocksB` (check 3) with `V` the range
of `α ↦ direction`, injective under `hc` (resp. `hv`, `hv ∧ hg`), and `hrw` derived from the same
hypothesis. SAME as the count of Lemma A.8 with the paper's `s`, as upper bounds; Lean is stated for
networks of any depth and any widths, no hypothesis on the biases.

**"No read column vanishes": needed? By reading and by a computation.** It is the paper's own
condition ("because no column of `W_read` vanishes", Step 3) and holds at generic parameters. It is
used twice: for injectivity of `α ↦ direction` and for `hrw`. Both go through when the read column is
`0` but the read bias is not (a direction with `α_i c_i = 0` and `α_i β_i = 0` has `α_i = 0`), so the
weaker hypothesis "`(c_i, β_i) ≠ 0`" would serve. With `c_i = 0` and `β_i = 0` the rescaling of unit `i`
moves only its write row, `hrw` fails, but the bound stays true: for ReLU², the `d + 1` parameters
`(c_i, β_i)` are flat (`σ(0) = σ′(0) = 0`) and independent of the changes of basis and translations
(whose components there are `−X c_i = 0` and `−(∑ g) c_i = 0`), which more than replaces the one
rescaling; for ReLU, if the unit's row reaches the output, no input is differentiable and Lean's
`fd = 0`. Computed (`/home/claude/audit32a_2/c4e.py`; `d = d_in = d_out = 2`, one or two blocks of 3
units, unit `0` of block `0` with read column `0` and read bias `+1`, `−1`; two batches of spread
inputs together): every rank is below the bound (for example ReLU residual, one block: `14` against
`18`). So the hypothesis is not needed for the truth of the bounds in these cases; it is needed by the
proof as written, and it is the paper's. Not a drift.

**Ranks of small networks with biases against the bounds, by a computation**
(`/home/claude/audit32a_2/net.py`, `c4b.py`, `c4c.py`, `c4d.py`: an independent transcription of `evalB`,
exact derivatives by `torch.func.jacrev` in float64; inputs of one token drawn at four scales `0.3` to
`10` (to `4` for ReLU² and ReGLU), `15 P / d_out` inputs per batch, two batches per parameter and the
rank of both together; rank by SVD with threshold `1e-9` of the largest singular value; two random
parameters per case and two seeds; for SwiGLU `c4.py`). Sizes `(d_in, d, d_out, widths)`:
`(2,2,2,[3])`, `(3,2,3,[4])`, `(2,2,2,[3,3])`, `(3,3,3,[3,4])`, `(3,2,2,[2,3])` (in the last, block `0` has width
`2 = d`, so its write can have rank `d`), skips and none.

| network | bound (residual / skipless), `s` | largest rank found (residual / skipless) |
|---|---|---|
| ReLU, `(2,2,2,[3])` | `18 / 14`, `s = 3` | `18 / 14` |
| ReLU, `(3,2,3,[4])` | `27 / 23` | `27 / 23` |
| ReLU, `(2,2,2,[3,3])` | `30 / 22`, `s = 6` | `30 / 22` |
| ReLU, `(3,3,3,[3,4])` | `54 / 36` | `54 / 36` (skipless: `36` at 3 of 8 further parameters) |
| ReLU, `(3,2,2,[2,3])` | `28 / 20` | `28 / 20` |
| ReLU², the same five | the same | attained in four sizes; `(3,3,3,[3,4])`: `53 / 36` against `54 / 36` (`54` on one batch whose gap was poor) |
| ReGLU, `(2,2,2,[3])` | `24 / 20`, `s = 6` | `24 / 20` |
| ReGLU, `(3,2,3,[4])` | `35 / 31` | `35 / 31` |
| ReGLU, `(2,2,2,[3,3])` | `42 / 34` | `42 / 34` |
| ReGLU, `(3,3,3,[3,4])` | `75 / 57` | `75 / 57` |
| ReGLU, `(3,2,2,[2,3])` | `38 / 30` | `38 / 30` |
| SwiGLU, the five sizes | `27/23`, `39/35`, `48/40`, `82/64`, `43/35` (`s = ∑ hid`) | equal, at every parameter and both batches |

No rank is above a bound (about 160 ranks). For SwiGLU every rank equals the bound. For the ReLU-type
blocks many ranks are below the bound at some parameters (for example ReLU, skipless,
`(3,3,3,[3,4])`: `21`, `30`, `35`, `36`), stable under a second batch, which is expected: with biases, a
unit can be inactive on the whole image of the previous block on an open set of parameters. The
smallest singular value kept is between `1e-9` and `3e-2` of the largest, the next one at most
`1e-16` except in four ReLU² and ReGLU cases with scale `10` (kept and next both near `1e-9`), which
I recomputed at scales up to `4` (`c4c.py`, gaps `1e-9`/`1e-16` or better). The coordinator's script
(`biases_inside_blocks_check_2026-11-25.py`, copied and run) gives the same picture: 24 cases, ranks
at or below the bounds, the directions in the kernel to `6.5e-16`.

Verdict of check 4: the three directions are **SAME** as Step 3 and Lemma B.3 (signs, factors, the
bias that moves); the six bounds are **SAME** as the count of Lemma A.8 with the paper's `s`, as upper
bounds, true at every parameter computed and attained at random parameters for every kind of block;
"no read column vanishes" is the paper's hypothesis, needed by the proof, not by the conclusion in the
cases checked (`(c_i, β_i) ≠ 0` would do for the proof).

### Check 5. Lemma B.2 with biases (`OneBlock/KeepsProductsBiases.lean`)

```lean
theorem keeps_products_biases_iff (p η : ParamsB A dIn dOut)   -- A : Arch T d 1, any block
    (hE : p.1.E.rank = Fintype.card d) (hD : p.1.D.rank = Fintype.card d)
    (hr : (p.1.read 0).rank = Fintype.card d) (hw : (p.1.write 0).rank = Fintype.card d) :
    (η.1.E * p.1.read 0 + p.1.E * η.1.read 0 = 0 ∧
      η.1.write 0 * p.1.D + p.1.write 0 * η.1.D = 0 ∧
      η.2.E ᵥ* p.1.read 0 + p.2.E ᵥ* η.1.read 0 + η.2.read 0 = 0 ∧
      η.2.write 0 ᵥ* p.1.D + p.2.write 0 ᵥ* η.1.D + η.2.D = 0) ↔
    ∃ (X : Fin 2 → Matrix d d ℝ) (g : Fin 2 → d → ℝ), η = cobDirB p X + (0, translateAtDir p.1 g)
theorem keeps_products_and_ED_biases_iff … (same hypotheses) :
    (… C … ∧ … A … ∧ η.1.E * p.1.D + p.1.E * η.1.D = 0 ∧ … β … ∧
      η.2.E ᵥ* p.1.D + p.2.E ᵥ* η.1.D
        + (η.2.write 0 ᵥ* p.1.D + p.2.write 0 ᵥ* η.1.D + η.2.D) = 0) ↔
    ∃ (X : Matrix d d ℝ) (g : Fin 2 → d → ℝ), η = cobDirB p (fun _ => X) + (0, translateDir p.1 g)
theorem finrank_span_keeps_products_biases … :
    Module.finrank ℝ (Submodule.span ℝ {η | (the four conditions)}) = 2 * Fintype.card d ^ 2 + 2 * Fintype.card d
theorem finrank_span_keeps_products_and_ED_biases … :
    Module.finrank ℝ (Submodule.span ℝ {η | (the five conditions)}) = Fintype.card d ^ 2 + 2 * Fintype.card d
```

**The derivatives written in the statements, against the Reduction, by reading.** The Reduction:
`M = ED`, `C = E W_read`, `A = W_write D`, `β = b_E W_read + b_read`, `γ_0 = b_write D + b_D`,
`γ = b_E D + γ_0`. By the product rule `D_θ C η = η_E W_read + E η_read`, `D_θ A η = η_write D + W_write η_D`,
`D_θ M η = η_E D + E η_D`, `D_θ β η = η_{b_E} W_read + b_E η_read + η_{b_read}`,
`D_θ γ_0 η = η_{b_write} D + b_write η_D + η_{b_D}`, `D_θ γ η = η_{b_E} D + b_E η_D + D_θ γ_0 η`. These are the
conditions in the statements, term by term (`ᵥ*` for a row vector times a matrix); the proof of the
lemma writes the same three ("`D_θ β η = η_{b_E} W_read + b_E η_read + η_{b_read}`", "`D_θ γ_0 η = g_1 D + η_{b_D}`").
The skipless statement keeps `β` and `γ_0`, the residual one `M`, `β` and `γ`: the lemma's
"keeps `β` and `γ_0`, respectively `β` and `γ`". SAME.

**The two equivalences, clause by clause, by reading.** With `L = 1`, `cobDirB p X + (0, translateAtDir θ g)`
is `η_E = E X_0`, `η_read = −X_0 W_read`, `η_write = W_write X_1`, `η_D = −X_1 D`, `η_{b_E} = b_E X_0 + g_0`,
`η_{b_read} = −g_0 W_read`, `η_{b_write} = b_write X_1 + g_1`, `η_{b_D} = −g_1 D` (`translateAtDir`:
`D := −(g (Fin.last 1)) D`); the residual form has `X_0 = X_1 = X` and `η_{b_D} = −(g_0 + g_1) D`
(`translateDir`: `read 0 := −(∑_{k ≤ 0} g_k) W_read = −g_0 W_read`, `D := −(g_0 + g_1) D`). These are the
lemma's formulas with `X = X_0`, `Y = X_1` (and its clause "if and only if moreover `X = Y`" for the
residual network). The hypotheses are the lemma's "Let `E`, `D`, `W_read` and `W_write` have rank
`d_model`"; the block is any `Arch T d 1` (the lemma is about the matrices only). SAME.

**Which rank conditions each direction needs.** The direction "if" (the directions of the lemma keep
the products) needs none: it is an identity (`E X W_read − E X W_read = 0`, …). The direction "only if":

- skipless: all four. Exact examples in integers (`/home/claude/audit32a_2/c5.py`, sympy; `d = 2`; each
  direction checked to keep `C`, `A`, `β`, `γ_0` exactly and to lie outside the span of the lemma's
  directions, which has dimension `12`):
  (a) `W_read = [[1,0],[0,0]]` (rank 1), `d_in = 3`, `E = [[1,0],[0,1],[0,0]]`, `W_write = D = I`:
  `η_E = e_3 e_2^⊤`, all else `0`; (b) `E = [[1,0],[0,0]]` (rank 1), width 3: `η_read = e_2 e_3^⊤`,
  `η_{b_read} = −b_E η_read`; (c) `D = [[1,0],[0,0]]` (rank 1), width 3: `η_write = e_3 e_2^⊤`;
  (d) `W_write = [[1,0],[0,0]]` (rank 1), `d_out = 3`: `η_D = e_2 e_3^⊤`, `η_{b_D} = −b_write η_D`.
  A rank condition on `W_read` matters only when `d_in > d` (with `E` square and invertible, `C` gives
  `η_E = E X` by itself), and similarly for the other three.
- residual: only `hE` and `hD`. From `D_θ M η = 0` and a right inverse of `D`, `η_E = E X` with
  `X = −η_D D⁺`; then `E` cancels to give `η_D = −X D` and `η_read = −X W_read`, and `D` cancels to give
  `η_write = W_write X`. Checked: (e) `W_read` and `W_write` both of rank 1 (`E`, `D` of rank 2,
  `d_in = d_out = 3`, width 3): the kernel of the five conditions has dimension `8 = d² + 2d` and equals
  the span of the lemma's directions. Without `hE` (f) or `hD` (g) (the other three of rank 2), the
  kernel has dimension `11 > 8`.
- the bias clauses need no rank condition beyond these: `g_0 = η_{b_E} − b_E X`, `g_1 = η_{b_write} − b_write Y`.

So `keeps_products_and_ED_biases_iff` and `finrank_span_keeps_products_and_ED_biases` ask two
hypotheses (`hr`, `hw`) that they do not need; the paper's lemma asks them too. Not a drift (LEAN as
strong as the paper; a stronger statement was available).

**The two dimensions.** "These directions form a space of dimension `2 d_model²` without the skip and
`d_model²` with it, and `2 d_model` more with biases": `2d² + 2d` and `d² + 2d`. Lean states the
dimension of the span of each set; the set is the solution set of linear equations, hence a subspace,
and equal to its span (the proof identifies it with the range of a linear map and uses
`Submodule.span_eq`), so the span is the set itself. Injectivity: `E` of rank `d` (and the write, for
the skipless form) — `cobDirB_add_translateAtDir_injective`, `cobDirB_const_add_translateDir_injective`,
thirty-first audit check 5. Recomputed in (h) (all ranks 2, `d_in = d_out = 3`, width 3): `12` and `8`.
SAME.

Verdict of check 5: **SAME** as Lemma B.2 with biases (the derivatives, the two equivalences, the two
dimensions, the hypotheses); in the residual form `hr` and `hw` are not needed (exact check), as the
paper's lemma does not say either.

### Check 6. Lemma A.27, third value (`Residual/SmallWritesBiases.lean`, `Residual/DepthMlpBiases.lean`, `Residual/DepthGatedBiases.lean`)

```lean
def smallWritesB {A : Arch T d L} (p : ParamsB A dIn dOut) (τ : ℝ) : ParamsB A dIn dOut :=
  (p.1.smallWrites τ, { E := p.2.E, read := p.2.read, write := fun ℓ => τ • p.2.write ℓ, D := p.2.D })
noncomputable def smallWritesLimitB (A : Arch T d L) (p η : ParamsB A dIn dOut)
    (x : Matrix T dIn ℝ) : Matrix T dOut ℝ :=
  x * (η.1.E * p.1.D + p.1.E * η.1.D)
    + Matrix.of (fun _ => η.2.E ᵥ* p.1.D + p.2.E ᵥ* η.1.D + η.2.D + ∑ ℓ, η.2.write ℓ ᵥ* p.1.D)
    + ∑ ℓ, (fderiv ℝ (A.f ℓ) ((x * p.1.E + Matrix.of fun _ => p.2.E) * p.1.read ℓ + Matrix.of fun _ => p.2.read ℓ)
          ((x * p.1.E + Matrix.of fun _ => p.2.E) * η.1.read ℓ + Matrix.of fun _ => η.2.read ℓ) * p.1.write ℓ
        + A.f ℓ ((x * p.1.E + Matrix.of fun _ => p.2.E) * p.1.read ℓ + Matrix.of fun _ => p.2.read ℓ)
          * η.1.write ℓ) * p.1.D
theorem eventually_funDimB_smallWritesB_ge (hA : A.χ = id)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (V : Submodule ℝ (ParamsB A dIn dOut))
    (hV : ∀ η, (∀ x, smallWritesLimitB A p η x = 0) → η ∈ V) :
    ∀ᶠ τ in 𝓝[≠] (0 : ℝ), Module.finrank ℝ (ParamsB A dIn dOut) ≤ funDimB A 1 (smallWritesB p τ) + Module.finrank ℝ V
theorem smallWritesLimitB_eq_zero_mlp (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hU : UnitsRigid σ σ' dIn dOut (Σ ℓ, hid ℓ)) (p …) (hp : SmallWritesGeneric p.1) (η …)
    (hη : ∀ x, smallWritesLimitB (Arch.mlp σ id hid) p η x = 0) :
    ∃ X : Matrix d d ℝ, η.1.E = p.1.E * X ∧ η.1.D = -(X * p.1.D) ∧
      (∀ ℓ, η.1.read ℓ = 0) ∧ (∀ ℓ, η.1.write ℓ = 0) ∧ (∀ ℓ, η.2.read ℓ = 0) ∧
      η.2.D = -((η.2.E - p.2.E ᵥ* X + ∑ ℓ, η.2.write ℓ) ᵥ* p.1.D)
theorem ae_eventually_funDimB_smallWritesB_mlp (hσ …) (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (hU : UnitsRigid σ σ' dIn dOut (Σ ℓ, hid ℓ)) (μ …) [μ.IsAddHaarMeasure]
    (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn) (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, ∀ᶠ τ in 𝓝[≠] (0 : ℝ), funDimB (Arch.mlp σ id hid) 1 (smallWritesB p τ)
        + (Fintype.card d ^ 2 + (L + 1) * Fintype.card d) = Module.finrank ℝ (ParamsB …)
-- gated: smallWritesLimitB_eq_zero_gated (eight conclusions, below), the value with + ∑ ℓ, card (hid ℓ)
```

**`smallWritesB`, by reading.** "`θ_τ` holds `τ b_write^ℓ` in place of `b_write^ℓ`": `smallWritesB p τ`
has the writes `τ W_write^ℓ` (`Params.smallWrites`, the twin without biases, audited before) and the
write biases `τ b_write^ℓ`, and every other component of `p`. SAME.

**`smallWritesLimitB` against the paper's `(J_0 η)(x)`, term by term, by reading.** With
`h = xE + b_E`, the pre-activation of block `ℓ` is `h W_read^ℓ + b_read^ℓ`, whose columns and entries are
the paper's `z_i = x c_i + β_i` (`c_i` the columns of `E W_read`, `β_i` the entries of
`b_E W_read + b_read`), and `h η_read^ℓ + η_{b_read^ℓ} = x (E η_read) + (b_E η_read + η_{b_read}) = x ψ_C + ψ_β`.

| paper | Lean |
|---|---|
| `x ψ_M`, `ψ_M = η_E D + E η_D` | `x * (η.1.E * p.1.D + p.1.E * η.1.D)` |
| `ψ_γ = η_{b_E} D + b_E η_D + η_{b_D} + ∑_ℓ η_{b_write^ℓ} D` (the same row at every token) | `Matrix.of (fun _ => η.2.E ᵥ* D + p.2.E ᵥ* η.1.D + η.2.D + ∑ ℓ, η.2.write ℓ ᵥ* D)` |
| `∑_i σ(z_i) ψ_{a_i}`, `ψ_A = η_write D` | `∑ ℓ, f_ℓ(z) * η.1.write ℓ * D` |
| `∑_i σ′(z_i)(x ψ_{c_i} + ψ_{β_i}) a_i`, `a_i` the rows of `W_write D` | `∑ ℓ, D f_ℓ(z)(x ψ_C + ψ_β) * W_write^ℓ * D` |
| gated: `σ(z_i) w_i ψ_{a_i} + σ′(z_i)(x ψ_{c_i} + ψ_{β_i}) w_i a_i + σ(z_i)(x ψ_{e_i} + ψ_{β_i′}) a_i` | the same with `f(M) = σ(M_gate) ⊙ M_value`, whose derivative has these three terms |

For MLP blocks `D f(z)(u)` is `σ′(z) ⊙ u` entry by entry, which is the paper's unit-by-unit sum. The
write bias enters at order `1` (its coordinate is not scaled by `S_τ`, and `τ b_write` is the value of the
coordinate, whose derivative is `η_{b_write} D`); the terms of `η_E`, `η_D`, `η_{b_E}` inside the blocks
are of order `τ` and vanish in the limit. SAME, and written for any differentiable block.

**By a computation** (`/home/claude/audit32a_2/c6.py`; transcriptions of `evalB`, `smallWritesB`,
`S_τ` and `smallWritesLimitB`; tanh, 2 blocks of 3 and 4 units, and SwiGLU, 2 blocks of 2 and 3 units;
`d = 2`, `d_in = d_out = 3`, two tokens, 5 inputs, a random direction `η`): `J_τ S_τ η − (J_0 η)` has
largest entry `0.109`, `0.0107`, `1.07e-3`, `1.07e-4` at `τ = 1e-2, …, 1e-5` for tanh (limit of size
`6.7`) and `2.8`, `0.28`, `0.028`, `2.8e-3` for SwiGLU (size `370`): the difference is `O(τ)`, so
`lim J_τ S_τ = J_0` with `J_0` as in Lean. The paper's unit-by-unit formula for tanh agrees with
`smallWritesLimitB` to `4.4e-15`. The coordinator's script (copied and run) gives the same for tanh
(relative difference `1.5e-1`, `1.5e-2` at `τ = 0.1, 0.01`).

**`evalB_smallWritesB_zero`, `hasDerivAt_evalB_smallWritesB`, by reading.** "`y = xED + b_E D + b_D
+ τ ∑_ℓ (f((xE + b_E) W_read^ℓ + b_read^ℓ) W_write^ℓ + b_write^ℓ) D + O(τ²)`": the value at `τ = 0` is
`(xE + b_E) D + b_D` and the derivative at `τ = 0` is `∑_ℓ (f_ℓ(…) W_write^ℓ + b_write^ℓ) D`, for
differentiable blocks (`hf`) without normalization. These are the two terms of the expansion (the
`O(τ²)` is replaced by differentiability, which is what the expansion means). SAME.

**`eventually_funDimB_smallWritesB_ge` against "The rank".** "on some finite batch `rank J_0 = P − m`
[…] `J_τ S_τ → J_0`, so on this batch, for all small `τ ≠ 0`, `rank J_τ = rank(J_τ S_τ) ≥ rank J_0 = P − m`."
Lean: if every direction flat for `J_0` is in `V`, then eventually on `𝓝[≠] 0`, `P ≤ fd(θ_τ) + dim V`;
real-analytic blocks, no normalization. This is the lower bound with `m ≤ dim V`. The converse ("rank
`J_τ ≤ P − m` on every batch, since the symmetries …") is in the bounds of `Symmetry/BiasesFlat.lean`
and `Symmetry/BiasesRescaleCount.lean`, which the value theorems use. Analyticity is more than the
proof needs (`C²` would do, as the proof uses); for the four kinds of block it holds. SAME.

**`smallWritesLimitB_eq_zero_mlp`, the six conclusions.** The paper: "So for a flat `η` the lemma gives
`ψ_M = 0`, `ψ_γ = 0` and a rescaling at every unit [for tanh and GELU: `ψ_{a_i} = 0`, `ψ_{c_i} = 0`,
`ψ_{β_i} = 0`]. As `E` and `D` have rank `d_model`, `ψ_M = 0` gives `η_E = EX` and `η_D = −XD` […] The
rescalings determine `η_read` and `η_write` through `ψ_C` and `ψ_A`, and then `η_{b_read}` through `ψ_β`.
Finally `ψ_γ = 0` determines `η_{b_D}` once `η_{b_E}` and the `η_{b_write^ℓ}` are chosen." By hand:
`ψ_C = E η_read = 0` with `E` of rank `d` gives `η_read = 0`; `ψ_A = η_write D = 0` with `D` of rank `d`
gives `η_write = 0`; `ψ_β = b_E η_read + η_{b_read} = η_{b_read} = 0`; `ψ_γ = η_{b_E} D − b_E X D + η_{b_D}
+ ∑ η_{b_write} D = 0` gives `η_{b_D} = −(η_{b_E} − b_E X + ∑_ℓ η_{b_write^ℓ}) D`. These are the six
conclusions. The hypothesis `hU : UnitsRigid σ σ' dIn dOut (Σ ℓ, hid ℓ)` is the conclusion of Lemma
B.3 for tanh and GELU applied to the units of all blocks together ("the hypotheses of Lemma B.3 hold
for the units of all blocks together, as for one block"), and `SmallWritesGeneric p.1` asks `E`, `D` of
rank `d`, every row of `W_write^ℓ D` nonzero, every column of `E W_read^ℓ` nonzero and the columns of all
blocks pairwise non-collinear (weights only; the conditions of Lemma B.3 without the biases). The free
data `(X, η_{b_E}, η_{b_write^ℓ})` give `d² + d + L d = d² + (L + 1) d`. SAME.

**The value at one parameter and at generic parameters.** `eventually_funDimB_smallWritesB_mlp`:
`fd(θ_τ) + d² + (L + 1) d = P` for all small `τ ≠ 0`, under `hσ`, analytic `σ`, `hU`, `SmallWritesGeneric`.
`ae_eventually_funDimB_smallWritesB_mlp`: for `μ`-almost every pair (every Haar measure on the pairs of
weights and biases), with `d ≥ 2`, `d_in ≥ d`, `d_out ≥ d`, blocks of any widths. The paper: "Let
`d_model ≥ 2`, let `E` and `D` have rank `d_model`, and let each block, in any order and of any width, be …
an MLP block, with all MLP blocks tanh, all GELU, all SwiGLU or all GeGLU blocks. For generic
parameters […] For all small `τ ≠ 0`" (`E` and `D` of rank `d` at generic parameters need exactly
`d_in, d_out ≥ d`). The quantifiers are in the paper's order (generic `θ`, then small `τ`). Named for
tanh and GELU (`tanh_unitsRigid`, `gelu_unitsRigid`, the one-block statements audited in the
thirty-first audit). SAME.

**Ranks, by a computation** (`c6.py`, `c6b.py`; the rank of `J_0` from `smallWritesLimitB` on a batch,
of `J_τ` at `τ = 0.1` and `0.01`, and at `τ = 1`, i.e. at random weights and biases; two batches; SVD
threshold `1e-9`):

| network (residual, biases) | `P` | value | `J_0` | `J_{0.1}`, `J_{0.01}` | random weights and biases |
|---|---|---|---|---|---|
| tanh, `(2,2,2,[3,3])` | 46 | 36 | 36, 36 | 36, 36 | 36, 36 |
| tanh, `(3,2,3,[2,3,4])` | 68 | 56 | 56, 56 | 56, 56 | 56, 56 |
| tanh, `(2,2,2,[1,1,1])` (blocks narrower than `d`) | 33 | 21 | 21, 21 | 21, 21 | 21, 21 |
| tanh, `(3,3,3,[3,3,3])` | 96 | 75 | | | 75 at three parameters |
| GELU, `(3,3,3,[3,2])` | 65 | 47 | 47, 47 | 47, 47 | 47, 47 |
| GELU, `(2,2,3,[2,1,3])` | 51 | 39 | | | 39 at three parameters |
| SwiGLU, `(2,2,2,[3,3])` | 64 | 48 (`s = 6`) | 48, 48 | 48, 48 | 48, 48 |
| SwiGLU, `(3,2,3,[2,3,2])` | 79 | 60 (`s = 7`) | 60, 60 | 60, 60 | 60 at three parameters (weights of scale `0.6`) |
| GeGLU, `(3,3,3,[2,2])` | 74 | 52 (`s = 4`) | 52, 52 | 52, 52 | 52, 52 |
| GeGLU, `(2,2,2,[2,2,2])` | 66 | 48 (`s = 6`) | | | 48 at three parameters |

The kept singular values are at least `5e-9` of the largest and the next at most `2e-16`; one run of
SwiGLU `(3,2,3,[2,3,2])` at random weights of scale `1` (outputs of size `10⁴` after three quadratic
blocks) had no gap (`1e-9`/`9e-10`) and was repeated at scale `0.6`. Every value is attained.

**`ae_funDimB_mlp_residual` (and `ae_funDimB_gated_residual`): not a numbered statement.** True as
stated by the computation above at `τ = 1` (tanh and GELU, two and three blocks; SwiGLU and GeGLU) and
by its proof (the value at one `θ_τ`, `ae_funDimB_ge` for the lower bound at almost every pair, the
bound of Lemma A.8 for the upper). The paper: Lemma A.8 gives the count of the symmetry group,
`d_model² + (L + 1) d_model + s`, and "Table 6 confirms these counts for tanh networks with biases" (the
row with skips: `P = 286`, rank `254 = 286 − 32`, recomputed in the thirty-first audit); the paper does
not state the value at generic parameters of a residual network with biases as a theorem. Lean states
it, derived as Theorem 4.7 is derived from the first value. The index says so. LEAN STRONGER (a
statement the paper only checks numerically).

**The gated twin (`Residual/DepthGatedBiases.lean`).** The paper: "For the gated blocks, the read of a
unit has a gate and a value: `c_i` and `β_i` belong to the gate, and `e_i`, `β_i′`, `ψ_{e_i}` and `ψ_{β_i′}`
are the same quantities for the value"; Lemma B.3 for SwiGLU and GeGLU: "`ψ_{c_i} = 0`, `ψ_{β_i} = 0`,
`(ψ_{e_i}, ψ_{β_i′}) = −α_i (e_i, β_i′)` and `ψ_{a_i} = α_i a_i`". The eight conclusions of
`smallWritesLimitB_eq_zero_gated`: `η_E = E X`; `η_D = −X D`; gate columns `0` (from `E η_gate = 0`);
value columns `−α_i e_i` of the read (from `E η_value = −α_i E W_value`); write rows `α_i` times the row
(from `η_write D = α_i W_write D`, `D` right invertible); gate biases `0` (from `ψ_β = η_{b_gate} = 0`);
value biases `−α_i β_i′` (from `ψ_{β′} = b_E η_value + η_{b_value} = −α_i (b_E W_value + b_value)`); and
`η_{b_D}` as for MLP blocks. Each follows by hand from the lemma as above; signs as in Lemma B.3 and as
in `rescaleDirB` (check 4). The flat space has dimension `d² + (L + 1) d + s` with `s = ∑_ℓ d_hidden,ℓ`,
"`s` the number of hidden units" for SwiGLU and GeGLU; the value is `P − d² − (L + 1) d − s`, and the
upper bound used is `funDimB_add_le_residual_gated` (check 4). `SmallWritesGenericGated` asks `E`, `D`
of rank `d`, rows of `W_write D`, gate columns and value columns of `E W_read` nonzero and the gate
columns of all blocks pairwise non-collinear; `GatedUnitsRescale` is Lemma B.3 for these gates (with the
biases, without the paper's "`(e_i, β_i′)` not proportional to `(c_i, β_i)`", which the statements for
SiLU and GELU do not need). Hypotheses and quantifiers as for MLP blocks. SAME. The computed SwiGLU
and GeGLU networks (table) attain the value at small `τ` and at random weights and biases.

**Is the third value stated in full?** The third value is for "MLP blocks with biases, no
normalization", with the lemma's MLP blocks "all tanh, all GELU, all SwiGLU or all GeGLU blocks", of any
widths, at any depth. Lean: `Arch.mlp σ id hid` with one `σ` for all blocks (tanh, GELU) and
`Arch.gated σ id hid` (SiLU: SwiGLU; GELU: GeGLU), widths `hid ℓ` arbitrary, any `L`. All four kinds,
named. Attention blocks are not in the third value's row ("MLP blocks with biases"); the files on attention
blocks with biases added at `6fab629` (one block, and the count of Lemma A.8) are not part of this
audit. So the third value of the lemma is stated in full.

Verdict of check 6: **SAME** throughout (`smallWritesB`; `smallWritesLimitB` term by term, and the limit
recomputed; the expansion; "The rank"; the six and the eight conclusions; the value at one parameter
and at generic parameters, with the paper's hypotheses and quantifiers; the four kinds of block, so the
third value is stated in full); `ae_funDimB_mlp_residual` and `ae_funDimB_gated_residual` are true and
LEAN STRONGER (the paper checks the count in Table 6 only).

### Check 7 (second half): the index rows (by reading, against checks 1 to 6)

Rows of `/home/claude/lp/lean/STATEMENTS.md` (unchanged between `49f38c2` and `6fab629` for the eight
files, except the status paragraph):

- **"The functional dimension with biases, without a hypothesis of differentiability"**
  (`FunctionalBiasesKinks.lean`): true (check 1). It could say which inputs count: those at which the
  output is differentiable in the weights and biases, a set that contains the paper's (inputs off the
  kinks) and can be larger.
- **"Changes of basis and translations with biases are flat, for any blocks"** (`BiasesFlatKinks.lean`):
  true (check 1).
- **"Symmetries inside the blocks of a network with biases …"** (`InsideBlocksBiases.lean`): true
  (checks 2, 3), with two remarks: Lean asks `V ≤ span {InsideBlocksB directions}` ("a space `V`
  inside the span of such directions", not "spanned by"); and the condition on `V` is needed for the
  skipless bound (exact example, check 3) and, for the residual bound, only for blocks that are nowhere
  differentiable in their parameters.
- **"S Lemma A.8, the count with `s`, for ReLU-type blocks and gated blocks with biases"**
  (`BiasesRescaleCount.lean`): true (check 4). "Not named for ReLU, ReLU², ReGLU, SwiGLU, GeGLU at
  generic parameters yet" is right.
- **"S Lemma B.2 with biases"** (`KeepsProductsBiases.lean`): true (check 5). It could add that the
  residual forms do not need the ranks of `W_read` and `W_write`.
- **"Residual networks with biases and small writes: the frame of S Lemma A.27 with biases"**
  (`SmallWritesBiases.lean`): true (check 6).
- **"S Lemma A.27 (Small writes), third value, for tanh and GELU blocks"** (`DepthMlpBiases.lean`) and
  **"… for SwiGLU and GeGLU blocks"** (`DepthGatedBiases.lean`): true (check 6), including "not a
  numbered statement of the paper" for `ae_funDimB_mlp_residual`, `ae_funDimB_gated_residual`.
- Every row says "proved": right (no `sorry`, standard axioms, first half of this check).
- The status paragraph lists the eight files as not yet compared by a reader; after this report they
  are compared (thirty-second audit, part A).

Verdict of check 7: registrations complete, axioms standard, every row true of its statements; two
sentences could be more precise (the condition `hrw` and "spanned by"; the inputs of Lean's flat space).

## Part 2: the statements, file by file

| statement | paper | verdict | note |
|---|---|---|---|
| `mem_flatB_of_hasDerivAt'` | Appendix B, "Notation and flat directions" (a symmetry's direction is flat); Lemma A.8's proof | SAME | no hypothesis; Lean's inputs are those at which the output is differentiable (check 1) |
| `funDimB_add_finrank_flatB'` | "the functional dimension at `θ` is therefore `P − dim K(θ)`" | SAME | for every network, with Lean's convention for `fderiv` |
| `funDimB_add_finrank_le_of_le_flatB'` | its use in the counts | SAME | |
| `cobDirB_mem_flatB_skipless'` | Proposition A.1 (ii) with biases, skipless | SAME | any blocks; `χ = id` needed (check 1) |
| `cobDirB_const_mem_flatB_residual'` | Theorem A.5 (iii) with biases (one change of basis) | SAME | any blocks |
| `translateDir_mem_flatB'` | Lemma A.8, first sentence | SAME | any blocks; `χ = id` needed |
| `translateAtDir_mem_flatB'` | Proposition A.1 (ii), translations of a skipless network | SAME | any blocks |
| `InsideBlocksB` (def) | "the symmetries inside blocks" (Lemma A.8; Step 3) | SAME | exact symmetries along a curve; admits the attention-bias symmetries (check 2) |
| `InsideBlocksB.mem_flatB` | (they come from symmetries, so they are flat) | SAME | every stream, every `χ` |
| `InsideBlocksB.E_eq_zero`, `.D_eq_zero`, `.biasE_eq_zero`, `.biasD_eq_zero` | (used in the count) | SAME | |
| `funDimB_add_le_residual_of_insideBlocksB` | Lemma A.8: `d_model² + (L + 1) d_model + s` | SAME (bound form) | `hrw` not needed for the paper's blocks (check 3) |
| `funDimB_add_le_skipless_of_insideBlocksB` | Lemma A.8: `(L + 1)(d_model² + d_model) + s` | SAME (bound form) | `hrw` needed (exact example, `13 ≤ 12` fails) |
| `rescaleDirMlpB`, `rescaleDirB`, `rescaleDirGateB` (defs) | Step 3; Lemma B.3 | SAME | signs, factors, the bias that moves (check 4) |
| `insideBlocksB_rescaleDirMlpB`, `_rescaleDirB`, `_rescaleDirGateB` | Step 3 ("they come from symmetries") | SAME | any `χ` |
| `funDimB_add_le_residual_mlp_rescale`, `funDimB_add_le_skipless_mlp_rescale` | Lemma A.8 with `s = d_hidden` per block (ReLU, ReLU²) | SAME (bound form) | `hc` is the paper's; not needed for the conclusion in the cases checked |
| `funDimB_add_le_residual_gated`, `funDimB_add_le_skipless_gated` | Lemma A.8 with `s = d_hidden` (SwiGLU, GeGLU) | SAME (bound form) | any gate |
| `funDimB_add_le_residual_gated_gate`, `funDimB_add_le_skipless_gated_gate` | Lemma A.8 with `s = 2 d_hidden` (ReGLU) | SAME (bound form) | |
| `keeps_products_biases_iff` | Lemma B.2 with biases, skipless | SAME | all four ranks needed (exact examples) |
| `keeps_products_and_ED_biases_iff` | Lemma B.2 with biases, residual | SAME | `hr`, `hw` not needed (check 5) |
| `finrank_span_keeps_products_biases` | "`2 d_model²` … and `2 d_model` more with biases" | SAME | the span is the set |
| `finrank_span_keeps_products_and_ED_biases` | "`d_model²` with it, and `2 d_model` more" | SAME | `hr`, `hw` not needed |
| `smallWritesB` (def) | "`θ_τ` holds `τ b_write^ℓ` in place of `b_write^ℓ`" | SAME | |
| `smallWritesLimitB` (def) | `(J_0 η)(x)` with `ψ_M`, `ψ_γ`, `ψ_C`, `ψ_β`, `ψ_A` | SAME | for any differentiable block; limit recomputed |
| `evalB_smallWritesB_zero`, `hasDerivAt_evalB_smallWritesB` | the expansion of `y` | SAME | |
| `eventually_funDimB_smallWritesB_ge` | "The rank" (lower bound) | SAME | |
| `smallWritesLimitB_eq_zero_mlp` | "So for a flat `η` the lemma gives …" | SAME | six conclusions |
| `eventually_funDimB_smallWritesB_mlp` | third value, `s = 0`, at one parameter | SAME | |
| `ae_eventually_funDimB_smallWritesB_mlp`, `_tanh`, `_gelu` | Lemma A.27, third value, tanh and GELU | SAME | every Haar measure; `d ≥ 2`, `d_in, d_out ≥ d`; any widths |
| `ae_funDimB_mlp_residual`, `ae_funDimB_tanh_residual`, `ae_funDimB_gelu_residual` | not numbered; Lemma A.8 count, Table 6 | LEAN STRONGER | true (computed) |
| `smallWritesLimitB_eq_zero_gated` | "For the gated blocks …"; Lemma B.3 for SwiGLU, GeGLU | SAME | eight conclusions |
| `eventually_funDimB_smallWritesB_gated` | third value, gated, at one parameter | SAME | `s` the number of hidden units |
| `ae_eventually_funDimB_smallWritesB_gated`, `_swiglu`, `_geglu` | Lemma A.27, third value, SwiGLU and GeGLU | SAME | |
| `ae_funDimB_gated_residual`, `ae_funDimB_swiglu_residual`, `ae_funDimB_geglu_residual` | not numbered | LEAN STRONGER | true (computed) |

No statement is FALSE, vacuous or drifted. Every PART is about form (Lemma A.8's group is stated as
bounds on the functional dimension, not as the dimension of a group).

## What the authors of the papers should know

Nothing false, vacuous, drifted or misdescribed was found. Points where the paper's statement or
proof needs a word:

1. **Appendix B, "Notation and flat directions"**: "every input" means the inputs off the kinks, "an
   open set of full measure". That is true at generic parameters, not at every parameter (a unit with
   read column `0` and read bias `0` sits at its kink at every input). The library uses the inputs at
   which the output is differentiable in the parameters, a larger set (all inputs for ReLU²); where the
   paper's set is dense the flat directions agree (check 1).
2. **Lemma A.8's count with `s`, without skips**: the independence of the symmetries inside blocks from
   the changes of basis and translations needs a condition, which the paper's Step 3 gives for the
   rescalings ("because no column of `W_read` vanishes"); for symmetries inside blocks in general it
   fails (a zero block, check 3). With skips nothing beyond `E` of rank `d` is needed for the blocks of
   the paper.
3. **Lemma B.2**: the residual form ("and it keeps `M` fixed as well … if and only if moreover
   `X = Y`", with biases "respectively `β` and `γ`") needs only `E` and `D` of rank `d_model`; `M = ED`
   then gives `η_E = EX` by itself (exact check, check 5). The skipless form needs all four ranks
   (exact examples).
4. **Step 3, "no column of `W_read` vanishes"**: with biases, "no unit has both its read column and its
   read bias `0`" is enough for the independence argument.
5. **Lemma A.27, third value**: with the statements of the library, the value of the residual network
   with biases at generic parameters (not only at `θ_τ`), `P − d_model² − (L + 1) d_model − s`, follows as
   Theorem 4.7 follows from the first value; the paper checks it in Table 6 only and could state it.

## Corrections for `STATEMENTS.md`

1. Status paragraph: move the eight files of this audit from "Not yet compared by such a reader" to
   the compared files, with the report `lean-statement-audit-thirtysecond-a-2026-11-25.md`; nothing
   false, vacuous or drifted.
2. Row "Symmetries inside the blocks of a network with biases …": "for a space `V` spanned by such
   directions" → "for a space `V` inside the span of such directions"; add: "the condition on `V` is
   needed for the skipless bound (thirty-second audit, part A, check 3: a network of zero blocks); for
   the residual bound it is not needed when every block map is differentiable in its parameters at
   some input".
3. Row "S Lemma B.2 with biases": add "the residual forms hold with `E` and `D` of rank `d` alone; the
   statements ask the four ranks of the lemma".
4. Row "The functional dimension with biases, without a hypothesis of differentiability": add "the
   inputs that put a condition on a flat direction are those at which the output is differentiable in
   the weights and biases; they include the paper's inputs off the kinks, and all inputs for ReLU²".

## What could not be checked

- Whether, at every depth and for every ReLU-type parameter, Lean's flat space (inputs at which the
  output is differentiable) equals the paper's (inputs off the kinks) whenever the paper's set is
  dense: argued for one block and for units of a later block, not proved (check 1).
- Whether the residual bound with `V` can fail without `hrw` for a block that is nowhere
  differentiable in its parameters: no counterexample found, none proved impossible (check 3).
- The ranks for ReLU-type blocks are lower bounds from batches: values below the bounds at some
  parameters were not resolved into "the functional dimension is lower there" and "the batch missed a
  region"; no rank exceeded a bound.
- The files on attention blocks with biases added at `6fab629` were not read.

Commit of `/home/claude/lp` at the end: `6fab629` (branch `lean-plus`); the eight files of this audit
are the same at `49f38c2` and `6fab629` (`git diff`), and so are their index rows.
