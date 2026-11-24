STATUS: complete

# Fifteenth audit, part A, of Lean statements against the papers (24 November 2026)

Reader: an independent reader who did not write the statements. Brief:
`/home/claude/proj_up/audit15a_brief_2026-11-24.md`. I audited statements and definitions, not
proofs. I changed no repository file, ran no `lake build`, made no commit and no push. My scratch
files are in `/home/claude/audit15a/`.

Library: `/home/claude/lw/lean` (branch `lean-wip`).

- Commit that I audited: `2fc98cc7f0ea3ad4dae9a2a86e6f8334a6d4cefa` (16:04:49 UTC), the head of
  `/home/claude/lw` when I began.
- Files with `sorry` at that commit (`git grep -lw sorry 2fc98cc -- lean/SkipsLean`): two, both
  outside the brief: `Dimension/IdentifiableConverse.lean` (2) and `Generic/LevelSetImages.lean`
  (1). The thirteen files of the brief have no `sorry`, and no line with `axiom`, `admit`,
  `native_decide` or `unsafe`.
- The branch moved three times while I worked, to `b1e7014` (16:09:57), `cbee1f1` (16:18:54) and
  `591d9e4` (16:28:08 UTC). At `591d9e4` the files with `sorry` are
  `Dimension/IdentifiableIff.lean`, `Residual/IdentifiableIff.lean`, `Generic/GroupDimension.lean`,
  `Symmetry/CobGroup.lean` and `Symmetry/OnlyOrthogonalRows.lean`, all outside the brief. The
  thirteen files are the same at the four commits (`git diff --stat`, no line). Their thirteen
  index rows are word for word the same; they stand at lines 753 to 760, 766, 767, 772 to 774 of
  `STATEMENTS.md` at `2fc98cc` and at lines 756 to 763, 769, 770, 782 to 784 at `591d9e4` (by a
  script). Line numbers below are those of `2fc98cc`; each correction quotes the words to change.
- The thirteen files have 127 public names (8 definitions, 119 theorems) and 157 private helpers.
  All 127 names are covered by their index rows (62 of them by a pattern such as "each also with
  `_rmsNorm`"; I counted each pattern: 8, 2, 2, 8, 10, 3, 16, 30, 4, 6, 6, 28, 4). All 119
  theorems stand in `checks/Axioms.lean`.
- Did a statement change after it was first committed? No. For each of the 127 public names the
  text from the docstring to `:=` is the same at the first commit of its file and at `b1e7014`
  (by a script, `pub2.py cmp`, output `cmp_statements.out`). The file headers are the same too,
  except one added `import` line in `Generic/Sum.lean`.

Papers, as text: the skips paper ("S", `skips.txt`), the dimension paper ("D", `dim.txt`).

How I checked.

- "By reading": I read the thirteen Lean files (every public statement and docstring in full, and
  the private helpers that carry an almost-everywhere statement), the definitions they use
  (`Arch`, `Params`, `hidden`, `eval`, `Arch.mlp`, `Arch.gated`, `Arch.attention`, `attnWeights`,
  `evalBatch`, `jacobianRank`, `funDim`, `flat`, `IsPointwiseLimit`, `SardCriticalValues`,
  `ClosureNullOfNull`, `headDirQK`, `headDirVO`, `rescaleDir`, `rescaleDirMlp`, `rescaleDirGate`),
  the three statements of `Residual/DifferentClassesCriterion.lean` that the last files call, and
  the paper passages that the brief names.
- "By hand": a short argument of my own, written in the note.
- "By compiling": with `lean` 4.36.0, run from `/home/claude/lw/lean` with `LEAN_PATH` set to a
  copy of the compiled library of `/home/claude/lp/lean` (copied at 16:12 UTC, when `lp` was at `b1e7014`; `diff -rq` of the two
  source trees shows only files that `lp` has in addition), without `lake build`. I compiled
  copies of the thirteen files from the sources of `lw` (`compile13.out`: no error; one warning,
  see note 8 of the list for the authors) and five scratch files of my own, `Chk1.lean` to
  `Chk5.lean` (outputs `Chk*.out`, all without error and without `sorry`).
- "By a computation": Python scripts of my own in `/home/claude/audit15a/` (`net.py`,
  `thm42_check.py`, `ends_check.py`, `inside_check.py`; numpy, double precision; Jacobians in the
  parameters by the complex step, so without truncation error; ranks from the singular values).

**Short answer. Nothing false, vacuous or drifted was found.** Every "generic" is `∀ᵐ θ ∂μ` for
every additive Haar measure. Every statement uses the library's `funDim` or `jacobianRank`. The
transformer forms of Theorem 4.2 ask less than the paper's Scope and have no rank condition; the
forms of Theorem 4.11 (i) ask what the Scope gives, `L ≥ 1`, and the two hypotheses from the
literature (Sard's theorem; the property of definable sets), which are hypotheses and not axioms.
The Lean model of a transformer is wider than the paper's: a block may have heads and hidden units
side by side. The paper's networks are the case in which every block has one of the two empty, no
hypothesis excludes that case, and in that case `s` and `P` are the paper's (compiled). So the
Lean statements are **stronger** than the paper's, not different. `InsideBlocks` is wider than the
paper's list of symmetries; this makes no bound false, because every such direction is flat and the
skipless bound has a hypothesis on `V` that stops double counting (I found a case where the count
would be false without it). What needs a correction is the index: one paragraph is out of date in
two places, one quotation has a word that the paper does not have, one row says "Not stated" of
statements that are now stated, and the label "D Theorem 4.3 for networks of attention blocks and
MLP blocks" names a theorem whose Scope has one kind of block.

---------------------------------------------------------------------------------------------------

## Part 1: the drift checks

### Check 1. Generic means almost every parameter, for every Haar measure

**Verdict: yes, in every statement. None is "there is a parameter" or "on an open set".** (By
reading; the shape of all of them by a script, `check1.py`, output `check1.out`.)

The thirteen files have 82 statements that contain `∀ᵐ`: 64 public and 18 private.

| Shape | Count | Which |
|---|---|---|
| `(μ : Measure (Params …)) [μ.IsAddHaarMeasure] … : ∀ᵐ θ ∂μ, …`, with `μ` a variable of the statement and no almost-everywhere hypothesis | 56 public, 15 private | the 8 + 20 bounds `ae_funDim_add_le_…` of the two `UpperBoundTransformer` files; the 4 + 24 statements `ae_forall_eval_residual_ne_skipless_…` and `ae_not_isPointwiseLimit_skipless_…`; the private rank conditions `ae_rank_…`, `ae_value_ne_zero_…`, `ae_sumSnd_col_ne_zero_ubr` |
| `∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), ∀ᵐ θ ∂μ, ∃ δ : ℝ, 0 < δ ∧ ∀ η, ∃ i, δ ≤ ‖…‖`, same `μ` | 6 public | the six `exists_batch_ae_exists_pos_le_norm_sub_skipless_…` (Theorem A.28 (iv)); the batch is chosen before `θ` (Part 2, note D) |
| conclusion `∀ᵐ θ ∂μ, p θ.sumFst` (or `θ.sumSnd`, or `p (Φ θ)`) for every Haar `μ` on the parameters of the sum, with the hypothesis `∀ᵐ θ ∂(Measure.addHaar : Measure (Params A dIn dOut)), p θ` | 2 public, 1 private | `ae_sumFst`, `ae_sumSnd`, `ae_comp_of_surjective_gsm` (`Generic/Sum.lean`): a condition that is generic for one part is generic for the sum |
| hypothesis `∀ᵐ θ' ∂Measure.addHaar, funDim A 0 θ' + k ≤ P`, conclusion at EVERY `θ`: `jacobianRank A 0 X θ + k ≤ P` | 2 private | `jacobianRank_add_le_of_ae_sea`, `…_set`: the step "the rank is lower semicontinuous, so the bound holds at every `η`" of Lemma A.26 |

One of them in full (`Dimension/UpperBoundTransformerRescale.lean`):

```
theorem ae_funDim_add_le_skipless_attention_relu [Nonempty d]
    (μ : Measure (Params (Arch.attentionMlp (T := T) (d := d) sees relu id H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d)
    (hW : ∀ ℓ, Fintype.card d ≤ Fintype.card (H ℓ) * Fintype.card (dh ℓ) + Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, funDim (Arch.attentionMlp sees relu id H dh hid) 0 θ
        + ((L + 1) * Fintype.card d ^ 2
          + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2 + ∑ ℓ, Fintype.card (hid ℓ)))
      ≤ Module.finrank ℝ (Params (Arch.attentionMlp (T := T) (d := d) sees relu id H dh hid) dIn dOut)
```

- In the two rows with an almost-everywhere hypothesis, the hypothesis is for the measure
  `Measure.addHaar` of the part. Two additive Haar measures of a finite-dimensional space have the
  same sets of measure zero (sixth audit, Check 1, compiled there), so this is "at generic
  parameters of the part". These are steps, not paper statements.
- The statements at one parameter (`funDim_add_le_…` without `ae_`) hold for every `θ` that
  satisfies written rank conditions; with their `ae_` companions they are the generic claim. No
  `ae_` form has a rank condition (Check 3).
- The only "there is a `θ`" are inside proofs (one residual parameter of large functional
  dimension, from which Lemma A.26 gives "almost every").
- That such a `μ` exists and that the hypotheses of the final statements can hold together: by
  compiling, `Chk5.lean` applies the Lean Theorem 4.2 and the first clause of Theorem 4.11 (i) to a
  concrete network (`d = 2`, an attention block with 2 heads of width 1, then an MLP block with 2
  hidden units) with `Measure.addHaar`. The statements are not empty.

### Check 2. `funDim` is the library's functional dimension

**Verdict: yes, in every statement that speaks of a functional dimension; the statements "at every
parameter" speak of `jacobianRank` on a batch, which is the rank of the same Jacobian.** (By
reading; differentiability by compiling.)

- `funDim A S θ` (`Dimension/Functional.lean`) is `sSup {r | ∃ n (X : Fin n → Matrix T dIn ℝ),
  r = jacobianRank A S X θ}`, and `jacobianRank A S X θ` is the rank of
  `fderiv ℝ (evalBatch A S X) θ`, the Jacobian in `θ` of the outputs on the batch `X`: Definition
  4.1 of both papers, with all real `T × d_in` inputs. The 56 bounds of `Symmetry/InsideBlocks.lean`
  (4), `InsideBlocksSum.lean` (4), `Dimension/UpperBoundTransformer.lean` (16),
  `UpperBoundTransformerRescale.lean` (28), `Residual/SkiplessEndsAttention.lean` (2) and
  `SkiplessEndsTransformer.lean` (2) use `funDim … 0 θ` (no skips: all stream matrices `0`) or
  `funDim … 1 θ` (identity skips). The six statements "at every parameter" use
  `jacobianRank … 0 X θ` for every `n` and every batch `X`. None uses another quantity.
- **Analytic blocks.** For attention blocks with tanh blocks the network is differentiable in the
  parameters at every input, for every stream, without normalization and under pre-RMSNorm with
  `ε > 0` (compiled, `Chk3.lean` (3g), (3h), from `differentiable_eval`, `differentiable_f_sum`,
  `differentiable_f_attention`, `differentiable_f_mlp`, `analyticOnNhd_rmsNorm`). The same proof
  works for every differentiable activation or gate. So for attention with tanh, GELU, SwiGLU and
  GeGLU blocks `funDim` is the paper's `fd` with no difference.
- **ReLU, ReLU² and ReGLU blocks, again.** Mathlib's `fderiv` is `0` where a map is not
  differentiable. The map of a batch is differentiable at `θ` exactly when the network is
  differentiable in `θ` at every input of the batch, so a batch with an input at which the network
  is not differentiable in `θ` has rank `0`. Hence in Lean `funDim θ` is the largest rank over the
  batches of inputs at which the network is differentiable in `θ`. The paper takes the Jacobian at
  the inputs at which no hidden unit sits at its kink; the network is differentiable in `θ` at
  each of these (attention is smooth), so the paper's batches are among Lean's, and the paper's
  `fd(θ)` is at most Lean's `funDim θ`. **An upper bound on `funDim` is therefore at least as
  strong as the paper's upper bound.** This is the note "ReLU blocks and the functional dimension"
  of the index (line 522); nothing in the new files changes it. (By reading; I did not compile
  this again.)
- The forms "under pre-RMSNorm (any `ε`)" include `ε ≤ 0`. For `ε = 0` the network is not
  differentiable where a hidden state has a zero row, and the same convention applies. The paper
  has `ε > 0` (S Section 2); the Lean statements cover it.

### Check 3. No extra hypotheses in the main-text statements

**Verdict: Theorem 4.2: none; every Lean hypothesis is implied by the Scope and several Scope
conditions are not asked at all. Theorem 4.11 (i): none beyond the Scope, `L ≥ 1`, and the two
hypotheses from the literature.**

**(a) S Theorem 4.2.** "With or without pre-RMSNorm, at generic parameters, the functional
dimension is at most `P − (L + 1) dim 𝒢 − s` without skips and at most `P − dim 𝒢 − s` with
identity skips." The Lean transformer forms are the 28 `ae_` statements of the two
`UpperBoundTransformer` files. Their hypotheses, all of them:

| Lean hypothesis | In which forms | Paper |
|---|---|---|
| `(μ) [μ.IsAddHaarMeasure]`, `∀ᵐ θ ∂μ` | all | "at generic parameters" |
| `hdIn : card d ≤ card dIn` | all | Scope: "`d_in, d_out ≥ d_model ≥ 2`" |
| `hdh : ∀ ℓ, card (dh ℓ) ≤ card d` | all | Scope: "of total width `H d_h = d_model`" gives `d_h ≤ d` (compiled, `Chk3.lean`, `PaperBlocks.dh_le`); Lemma A.18: "heads have width `d_h ≤ d_model`". Lean asks less |
| `hW : ∀ ℓ, card d ≤ card (H ℓ) * card (dh ℓ) + card (hid ℓ)` | the 14 without skips only | Scope: "Every MLP block has `d_hidden ≥ d_model`", "total width `H d_h = d_model`"; Lemma A.18: "every block has width at least `d_model`". Same for a block of one kind |
| `[Nonempty d]` (`d ≥ 1`) | the 24 with gated, ReLU, ReLU² or ReGLU blocks | Scope: `d_model ≥ 2`. Lean asks less. It is needed (by hand): for `d = 0` there are no parameters and the bound with `∑ d_hidden > 0` is false |
| `hσ : ∀ lam z, 0 < lam → σ (lam * z) = lam ^ k * σ z` | the 8 general `…_rescale` forms | not in the named forms for ReLU, ReLU² and ReGLU, where it is proved (`relu_homogeneous`, `reluSq_homogeneous`) |

Not asked by Lean, although in the Scope: `d_out ≥ d`; `d ≥ 2`; "sequences of at least two
tokens" and any condition on the mask (`sees` is any relation; `T` any finite type); "All
attention blocks have the same number `H` of heads"; `H d_h = d` exactly; `ε > 0`. **The rank
conditions** (`θ.E.rank = card d`, `(θ.write ℓ).rank = card d`, the ranks `d_h` of the query and
value matrices, no vanishing value, gate or read column) stand only in the statements at one
parameter (16 in these two files, 8 more in `Symmetry/InsideBlocks.lean` and
`InsideBlocksSum.lean`); no `ae_` form has one (by reading every `ae_` statement; the table of all
hypotheses by a script).

That the Scope gives the Lean hypotheses, and that the Lean conclusion is then the paper's, I
compiled (`Chk3.lean`): for numbers `nd, nIn, nOut` and `nH, ndh, nhid : Fin L → ℕ` such that every
block is an attention block with `nH ℓ * ndh ℓ = nd` and no hidden unit, or an MLP block with
`nhid ℓ ≥ nd` and no head, with `2 ≤ nd ≤ nIn`:

- `thm42_tanh`: both bounds without normalization for attention and tanh blocks, with
  `s = 2 ∑ nH ℓ * ndh ℓ ^ 2`;
- `thm42_relu_rmsNorm`: both bounds under pre-RMSNorm for attention and ReLU blocks, with
  `s = 2 ∑ nH ℓ * ndh ℓ ^ 2 + ∑ nhid ℓ`;
- `thm42_reglu`: both bounds for attention and ReGLU blocks, with
  `s = 2 ∑ nH ℓ * ndh ℓ ^ 2 + 2 ∑ nhid ℓ`.

No hypothesis is needed beyond these. All three depend on the three standard axioms only.

**(b) S Theorem 4.11 (i).** "For analytic blocks, with or without pre-RMSNorm, a residual network
at generic parameters equals no skipless network of the same widths, and is not a pointwise limit
of such networks." The Lean transformer forms are the 28 statements of
`Residual/DifferentClassesTransformer.lean` (and the 6 of `DifferentClassesAttention.lean`). One
in full:

```
theorem ae_not_isPointwiseLimit_skipless_attention_tanh
    (hSard : ∀ r : ℕ, SardCriticalValues (Params
      (Arch.attentionMlp (T := T) (d := d) sees Real.tanh id H dh hid) dIn dOut) (Fin r → ℝ))
    (hOmin : ∀ (n : ℕ) (X : Fin n → Matrix T dIn ℝ),
      ClosureNullOfNull (Set.range (evalBatch (dOut := dOut)
        (Arch.attentionMlp (T := T) (d := d) sees Real.tanh id H dh hid) 0 X)))
    (μ : Measure (Params (Arch.attentionMlp (T := T) (d := d) sees Real.tanh id H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (hL : 0 < L) (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ θ ∂μ, ¬ IsPointwiseLimit
      (Set.range (eval (Arch.attentionMlp (T := T) (d := d) sees Real.tanh id H dh hid) 0 : …))
      (eval (Arch.attentionMlp sees Real.tanh id H dh hid) 1 θ)
```

| Lean hypothesis | Paper |
|---|---|
| `hSard` (Sard's theorem for real-analytic maps from the parameters of the skipless network to `ℝ^r`) | not a hypothesis of the paper's statement; the paper's proof of Lemma A.26 uses "Sard's theorem". A theorem from the literature, taken as a hypothesis |
| `hOmin` (only in the statements on limits and on `δ`, 16 in this file and 4 in the attention file: if a linear image of the set of outputs of the skipless networks on a batch has measure zero, so has its closure) | not a hypothesis of the paper's statement; it is what Lemma A.21 with Lemma A.23 gives, from van den Dries and Speissegger. Taken as a hypothesis |
| `(μ) [μ.IsAddHaarMeasure]`, `∀ᵐ θ ∂μ` | "at generic parameters" |
| `hd`, `hdIn`, `hdOut` | Scope: "`d_in, d_out ≥ d_model ≥ 2`" |
| `hdh`, `hdh0`: `1 ≤ d_h ≤ d` in every block | Scope: `H d_h = d` gives both (compiled, `PaperBlocks.dh_le`, `PaperBlocks.dh_pos`); Lemma A.27: "heads of width at most `d_model`". Asked of every block, also of a block without heads (Check 4 (b)) |
| `hL : 0 < L` | Theorem A.28 (ii): "any depth `L ≥ 1`". Needed: for `L = 0` the two networks are the same |
| `t₁ ≠ t₂`, `sees t₂ t₂`, `sees t₂ t₁` | Scope: attention blocks "act on sequences of at least two tokens"; Lemma A.27: "causal or not". The causal mask on `nT + 2` tokens is an instance (compiled, `thm411_gelu_causal_rmsNorm`); so is no mask. Lean asks less |
| `hε : 0 < ε` (the `_rmsNorm` forms, 14 in this file and 3 in the attention file) | "RMSNorm with the constant `ε > 0`" |
| `hσ`, `hσa`, `hU : UnitsRigid …` or `GatedUnitsRescale …` | only in the 12 general forms "for every activation with the conclusion of Lemma B.3"; the 16 named forms for tanh, GELU, SwiGLU and GeGLU have none |

Not asked by Lean, although in the Scope: `d_hidden ≥ d` ("blocks of any widths", as in Lemma A.27
"of any width"); `H d_h = d`; the same number of heads in all attention blocks.

- **The two literature hypotheses are hypotheses, not axioms.** `SardCriticalValues` and
  `ClosureNullOfNull` are definitions of type `Prop` (`Literature/Sard.lean`,
  `Literature/OMinimal.lean`); the theorems take them as arguments. By compiling (`Chk1.out`):
  each of the 127 public names of the thirteen files depends on `propext`, `Classical.choice`,
  `Quot.sound` and on nothing else.
- In the sense of the brief these two are extra hypotheses of the Lean forms of Theorem 4.11 (i);
  the index says "given Sard's theorem" and "given Sard's theorem and the property of definable
  sets" in the rows. No other hypothesis goes beyond the paper.

### Check 4. The model of a transformer

**Verdict: the Lean statements are the paper's statements and more: they also cover blocks with
heads and hidden units in parallel. They are STRONGER, not different.**

The paper (S Lemma A.27, `skips.txt` line 1866): "let each block, in any order and of any width,
be an attention block with heads of width at most `d_model`, causal or not, on sequences of at
least two tokens, or an MLP block, with all MLP blocks tanh, all GELU, all SwiGLU or all GeGLU
blocks." S Section 2: "A transformer layer has two blocks, its attention and MLP sub-layers: a
transformer of 12 layers has `L = 24`, and per block means per sub-layer"; Scope: "all MLP blocks
are of one kind".

Lean (`Network/Sum.lean`, `Network/Transformer.lean`):

```
abbrev Arch.sum (A B : Arch T d L) : Arch T d L where
  r ℓ := A.r ℓ ⊕ B.r ℓ
  w ℓ := A.w ℓ ⊕ B.w ℓ
  f ℓ M := Matrix.of fun t p =>
    Sum.elim (A.f ℓ (M.submatrix id Sum.inl) t) (B.f ℓ (M.submatrix id Sum.inr) t) p
  χ := A.χ

noncomputable abbrev Arch.attentionMlp … : Arch T d L :=
  (Arch.attention sees χ H dh).sum (Arch.mlp σ χ hid)
```

Every block `ℓ` has the heads `H ℓ` of width `dh ℓ` and the hidden units `hid ℓ`, reads the same
`χ(h)`, and its output is the sum of the outputs of the two parts (`f_sum_mul`); the network has
one skip per block. One activation `σ` serves all blocks: "all MLP blocks are of one kind".

**(a) A block with one part empty is a block of the library, as a function.** By compiling
(`Chk2.lean`):

- `eval_attentionMlp_of_hid_empty`: if no block has a hidden unit, then for every stream and every
  input `eval (Arch.attentionMlp sees σ χ H dh hid) S θ x = eval (Arch.attention sees χ H dh) S
  θ.sumFst x`: the library's network of attention blocks.
- `eval_attentionMlp_of_H_empty`: if no block has a head, it is `eval (Arch.mlp σ χ hid) S
  θ.sumSnd x`: the library's network of MLP blocks. `eval_attentionGated_of_H_empty`: the same
  with gated blocks.
- Block by block, the other blocks being anything: `block_attentionMlp_of_hid_empty` (a block
  without hidden units is equation (4), `attentionBlock`, with the query, key, value and output
  matrices of its heads) and `block_attentionMlp_of_H_empty` (a block without heads is
  `σ(h W_read) W_write`). They come from the library's `f_sum_mul_of_isEmpty_right`, `…_left`.

So the paper's networks, attention blocks and MLP blocks in any order, are exactly the case in
which every block has `hid ℓ` empty or `H ℓ` empty.

**(b) No hypothesis excludes that case.** I listed every hypothesis of the 119 theorems by a
script and read them. There is no `Nonempty`, no `0 <` and no lower bound on `H ℓ` alone or on
`hid ℓ` alone anywhere. The hypotheses that mention `H`, `dh` or `hid`:

- `hW : ∀ ℓ, card d ≤ card (H ℓ) * card (dh ℓ) + card (hid ℓ)` (bounds without skips): with
  `hid ℓ` empty it is `d ≤ H d_h`, with `H ℓ` empty it is `d ≤ d_hidden`: the paper's "width at
  least `d_model`" for each kind.
- `hdh : ∀ ℓ, card (dh ℓ) ≤ card d` and, in the two `DifferentClasses` files,
  `hdh0 : ∀ ℓ, 0 < card (dh ℓ)`. They are asked of every block, **also of a block without heads**.
  There `dh ℓ` is a free choice that changes neither the function nor the number of parameters,
  so one takes a type with one element (possible as `d ≥ 1`); `PaperBlocks` in `Chk3.lean` does
  this (`ndh ℓ = 1` for an MLP block) and the Lean theorems apply. No network is excluded; the
  index does not say that the condition is also asked of blocks without heads (correction 8).
- The rank conditions `hQ`, `hV` are `∀ ℓ (i : H ℓ), …`, and `hv`, `hc`, `hg` are `∀ ℓ i, …` over
  the hidden units: empty conditions for an empty part. `hw` is the rank of the whole write of the
  block.
- The two tokens `t₁ ≠ t₂` with `sees t₂ t₂`, `sees t₂ t₁` (the two `DifferentClasses` files) are
  asked even if no block has a head. A network of MLP blocks alone on one token is therefore not
  an instance of these statements; it is an instance of the twins `Residual/DifferentClasses.lean`
  and `DifferentClassesRMS.lean`.

**(c) The term `s` is the paper's `s` in that case.** By reading every conclusion; three of them
by compiling ((a) of Check 3).

| Blocks | Lean term | Paper (S Section 4.1 and Appendix A.6; D Appendix B) |
|---|---|---|
| heads | `2 * ∑ ℓ, card (H ℓ) * card (dh ℓ) ^ 2` | "a change of basis between its queries and keys and one between its values and outputs, of dimension `d_h²` each": `2 H d_h²` per block. A block without heads adds `0` whatever `dh ℓ` is |
| tanh, GELU (`attentionMlp`, any `σ`, first file) | nothing more | "for tanh and GELU blocks, `s = 0`" |
| SwiGLU, GeGLU (`attentionGated`, any `σ`, first file) | `+ ∑ ℓ, card (hid ℓ)` | "the rescaling of the value of a hidden unit of a gated block" |
| ReLU, ReLU² (`…_attention_relu`, `…_reluSq`, second file) | `+ ∑ ℓ, card (hid ℓ)` | "the rescaling of a hidden unit of a ReLU or ReLU² block" |
| ReGLU (`…_attention_reglu`, second file) | `+ 2 * ∑ ℓ, card (hid ℓ)` | "and, in ReGLU, its gate"; D: "`s = 2 d_hidden` for ReGLU" |

With ReLU or ReLU² as `σ` the first file's bound has `s` without the rescalings, and with ReGLU
without the rescalings of the gates: true and weaker than the paper's; the file header and the
index row say so, and the second file has the paper's value.

**(d) `P` is the paper's `P`.** By compiling (`Chk2.lean`, `finrank_params_attentionMlp`,
`finrank_params_attentionGated`): `Module.finrank ℝ (Params (Arch.attentionMlp …) dIn dOut) =
d_in d + ∑_ℓ (4 d H_ℓ d_{h,ℓ} + 2 d d_hidden,ℓ) + d d_out`, and with gated blocks `3 d d_hidden,ℓ`
in place of `2 d d_hidden,ℓ`. This is the paper's count: `E`, the read `[W_Q | W_K | W_V]` and the
write `W_O` of each head, the read and the write of each hidden unit (two read columns for a gated
unit), `D`; no biases, no skip parameters.

By the computation (`thm42_check.out`): on three networks with heads and hidden units in one block
(inside the Lean hypotheses, outside the paper's model) the rank at a random parameter is at most
the Lean bound in all 12 values, and equal to it in 11.

### Check 5. `InsideBlocks`

```
def InsideBlocks (A : Arch T d L) (θ η : Params A dIn dOut) : Prop :=
  ∃ γ : ℝ → Params A dIn dOut, γ 0 = θ ∧ HasDerivAt γ η 0 ∧
    ∀ᶠ τ in 𝓝 (0 : ℝ), (γ τ).E = θ.E ∧ (γ τ).D = θ.D ∧
      ∀ ℓ (n : Matrix T d ℝ),
        A.f ℓ (n * (γ τ).read ℓ) * (γ τ).write ℓ = A.f ℓ (n * θ.read ℓ) * θ.write ℓ
```

In words: `η` is the velocity at `τ = 0` of some curve of parameters through `θ` that, near
`τ = 0`, keeps `E`, keeps `D`, and keeps the map `n ↦ f_ℓ(n W_read^ℓ) W_write^ℓ` of every block on
every `T × d` matrix `n`.

**Verdict: every direction of a symmetry inside a block of the paper has this property; the
property is wider than the paper's list; the bounds for `V ≤ span {InsideBlocks}` are not false for
any `V` that the statements allow.**

- **The paper's symmetries have it** (by reading the five library statements; they compile):
  the changes of basis inside the heads (`insideBlocks_headDirQK`, `insideBlocks_headDirVO`), the
  rescalings of the values of gated units (`insideBlocks_rescaleDir`), of the hidden units of a
  positively homogeneous MLP block (`insideBlocks_rescaleDirMlp`: ReLU, ReLU²) and of the gates of
  a positively homogeneous gated block (`insideBlocks_rescaleDirGate`: ReGLU); for every `θ`,
  every `χ`, every mask. The directions are the paper's: `η_Q = W_Q Γ`, `η_K = −W_K Γᵀ`;
  `η_V = W_V Γ'`, `η_O = −Γ' W_O`; value column times `−α`, write row times `α`; read (gate)
  column times `α`, write row times `−k α`.
- **A direction that is not one of the paper's symmetries can have it.** The definition asks for
  a curve, not for a group of maps, and it does not ask the curve to be a rescaling or a change of
  basis. By compiling (`Chk4.lean`, `insideBlocks_dead_unit`, standard axioms only): at an MLP block
  whose activation vanishes at `0` (tanh, GELU, ReLU) and whose hidden unit `i₀` has the read
  column `0`, every move of the write row of that unit satisfies `InsideBlocks` (the unit writes
  `σ(0) = 0` whatever its write row is). This is not a rescaling, a sign flip or a permutation.
  It still fits the paper's sentence ("change the read and the write of one block and leave the
  map of that block unchanged"), and it exists only at parameters that are not generic. At generic
  parameters of a tanh block I expect no nonzero such direction, and for an attention block the
  solutions of `η_Q W_Kᵀ + W_Q η_Kᵀ = 0`, `η_V W_O + W_V η_O = 0` have dimension `2 d_h²` per
  head, the paper's count (by hand; not compiled).
- **Does this make the bounds claim too much? No.** (i) Every such direction is flat for every
  stream and every `χ` (`InsideBlocks.mem_flat`): the function does not change to first order
  along it, which is all that the count of S Theorem A.17 (ii) uses. (ii) The bound with identity
  skips, `fd + dim 𝒢 + dim V ≤ P`, asks only `rank E = d`; the directions of `V` have `E`
  component `0` and a change of basis `X` has `E X`, so the two families are independent. (iii)
  The bound without skips also asks `rank W_write^ℓ = d` and that a direction of `V` whose read of
  a block is `0` has the write of that block `0` (`hrw`). This hypothesis is needed, and it is
  what excludes the dead-unit moves of the write.
- **The recomputation the brief asks for** (by hand, then by the computation, `inside_check.out`,
  three random draws each, ranks with clean gaps):
  - (5a) One tanh block with identity skip, `d = 2`, 3 hidden units, the read column of unit 0
    zero, `V` = the moves of its write row (`dim V = d = 2`; near this `θ` these are all the
    curves that keep the block map, since the write row is not `0`). Lean: `fd ≤ P − d² − dim V =
    20 − 4 − 2 = 14`. Measured rank 12 in the three draws (also `d = 3`: 21 against 24). The
    directions of `V` are in the kernel of the Jacobian exactly (`|J v| = 0`). The bound holds.
  - (5b) One tanh block without skip, `d = 2`, 3 hidden units, the write row of unit 0 zero, `V` =
    the moves of its read column (`dim V = 2`; `hrw` holds). Lean: `fd ≤ P − 2d² − dim V = 20 − 8
    − 2 = 10`. Measured rank 10 in the three draws (`d = 3`, 4 units: 21 against 21). The bound
    holds, with equality.
  - (5c) One tanh block without skip, `d = 2`, 2 hidden units, `d_out = 1`, the read column of
    unit 0 zero, `V` = the moves of its write row. `E` and the write have rank 2, `V` is spanned
    by `InsideBlocks` directions, but `hrw` fails. By hand: the output is the number
    `tanh(x E c_1) a_1 D`, and its derivatives in the parameters span the functions
    `x ↦ tanh'(x E c_1)(x w)` for `w ∈ ℝ²` (2 dimensions, from `E` and `c_1`), `x ↦ tanh(x E c_1)`
    (1, from `a_1` and `D`) and `x ↦ x E ψ` for `ψ ∈ ℝ²` (2, from the read column of the dead
    unit, since `tanh'(0) = 1` and `a_0 D ≠ 0`); the write row of the dead unit gives nothing. So
    `fd = 5`. The count without
    `hrw` would be `P − 2d² − dim V = 14 − 8 − 2 = 4`. Measured rank 5 in the three draws. So the
    inequality **would be false without `hrw`**; the Lean statement has `hrw`, this `V` is not
    allowed, and nothing false is claimed. (The reason: with `d_out < d` a change of basis at `h_1`
    with `X D = 0` moves only the write row of the dead unit, a direction that is already in `V`.)
- In the named statements (`UpperBoundTransformer…`) `V` is the span of the paper's directions
  and `dim V` is the paper's `s` (the conclusions show the number).

---------------------------------------------------------------------------------------------------

## Part 2: the statements, file by file

Verdicts: SAME, LEAN STRONGER, LEAN WEAKER, DIFFERENT, PART, FALSE; "step" marks a statement of
the library with no sentence of its own in a paper, for which I say whether it states what its
docstring says. Unless a row says otherwise the check was by reading; all 127 names compile and
depend on the three standard axioms only (`Chk1.out`).

| File | Names | Paper sentence | Verdict |
|---|---|---|---|
| `Network/Sum.lean` | `Arch.sum` | S Section 2, "We write every block, MLP or attention, in one form"; Lemma A.27, "each block, in any order and of any width, be an attention block […] or an MLP block" | LEAN STRONGER as a model: contains the paper's blocks (one part empty) and blocks with both parts. `χ` of the sum is that of `A` (note A) |
| | `f_sum_mul` | — | step; as its docstring: the block of the sum is the sum of the two blocks |
| | `f_sum_mul_of_isEmpty_right`, `f_sum_mul_of_isEmpty_left` | Lemma A.27, same sentence | SAME: a block with one part empty is the block of the other kind (used in `Chk2.lean`) |
| | `analyticOnNhd_f_sum`, `differentiable_f_sum`, `continuous_f_sum`, `locallyLipschitz_f_sum` | — | steps; as their docstrings |
| `Network/Transformer.lean` | `Arch.attentionMlp`, `Arch.attentionGated` | S Section 2, "A transformer layer has two blocks, its attention and MLP sub-layers"; Scope, "all MLP blocks are of one kind" | LEAN STRONGER as a model (Check 4) |
| `Generic/Sum.lean` | `ae_sumFst`, `ae_sumSnd` | S Section 2, "A statement holds at generic parameters if it holds outside a set of Lebesgue measure zero" | step; as its docstring (Check 1) |
| `Symmetry/InsideBlocks.lean` | `InsideBlocks` | S Section 4.1, "the symmetries inside the blocks, which change the read and the write of one block and leave the map of that block unchanged" | LEAN STRONGER as a notion: wider than the paper's list (Check 5); the header quotes the paper with a word that it does not have (correction 4) |
| | `InsideBlocks.mem_flat` | S Section 4.1, "They preserve the function with skips and without them" | SAME, to first order; for every stream and every `χ` |
| | `InsideBlocks.E_eq_zero`, `InsideBlocks.D_eq_zero` | — | steps; as their docstrings |
| | `funDim_add_le_skipless_of_insideBlocks`, `…_rmsNorm` | S Theorem A.17 (ii) and its proof, with Lemma A.18; D Theorem 4.3 with Lemma B.1 | the proof piece at one parameter, SAME count; LEAN STRONGER in that `V` is any space of such directions with `hrw` (Check 5) and `ε` is any real |
| | `funDim_add_le_residual_of_insideBlocks`, `…_rmsNorm` | S Theorem A.17 (ii), "`P − dim 𝒢 − s` with them" | the same; only `rank E = d` is asked |
| `Symmetry/InsideBlocksSum.lean` | `Params.sumFst`, `Params.sumSnd`, `Params.sumInl`, `Params.sumInr` | — | definitions; as their docstrings |
| | `InsideBlocks.sumInl`, `InsideBlocks.sumInr` | S Section 4.1, "`s` … summed over the blocks" | step; a symmetry inside the blocks of a part is one of the sum |
| | the four `funDim_add_le_…_sum_of_insideBlocks…` | S Theorem A.17 (ii) for two kinds of block | the proof piece, with `dim V_A + dim V_B`; rank of the whole write of each block |
| `Symmetry/InsideBlocksKinds.lean` | `insideBlocks_headDirQK`, `insideBlocks_headDirVO`, `insideBlocks_rescaleDir` | S Appendix A.6, "A symmetry inside a block changes the read and the write of that block and leaves its map unchanged"; the list of D Appendix B | SAME, as directions; for every `θ`, `χ`, mask and gate activation |
| `Dimension/UpperBoundTransformer.lean` | the 8 `funDim_add_le_{skipless,residual}_attention{Mlp,Gated}{,_rmsNorm}` | S Theorem A.17 (ii) under the rank conditions of Lemma A.18 | the proof piece at one parameter; with the `ae_` forms the generic claim |
| | the 4 `ae_funDim_add_le_…_attentionMlp…` | S Theorem 4.2 for attention blocks and tanh or GELU blocks | LEAN STRONGER (Check 3 (a), Check 4; compiled `thm42_tanh`). With ReLU or ReLU² as `σ`: LEAN WEAKER than the paper's bound, as the header says; the second file has the paper's |
| | the 4 `ae_funDim_add_le_…_attentionGated…` | S Theorem 4.2 for attention blocks and SwiGLU or GeGLU blocks | LEAN STRONGER. With ReGLU: LEAN WEAKER, as the header says; the second file has the paper's |
| `Dimension/UpperBoundTransformerRescale.lean` | `insideBlocks_rescaleDirMlp`, `insideBlocks_rescaleDirGate` | S Section 4.1, "the rescaling of a hidden unit of a ReLU or ReLU² block"; A.6, "and, in ReGLU, its gate" | SAME, as directions; for every positively homogeneous `σ` of degree `k` |
| | the 8 `funDim_add_le_…_rescale…` | S Theorem A.17 (ii) under the conditions of Lemma A.18 and no vanishing read, gate or value column | the proof piece at one parameter |
| | the 8 `ae_funDim_add_le_…_rescale…` | S Theorem 4.2 | LEAN STRONGER: any positively homogeneous activation or gate |
| | the 12 named: `ae_funDim_add_le_{skipless,residual}_attention_{relu,reluSq,reglu}{,_rmsNorm}` | S Theorem 4.2 for attention blocks and ReLU, ReLU² or ReGLU blocks | LEAN STRONGER (compiled `thm42_relu_rmsNorm`, `thm42_reglu`); `funDim` as in Check 2 |
| `Residual/SkiplessEndsAttention.lean` | `funDim_add_le_skipless_ends_attention`, `…_rmsNorm` | proof of S Theorem A.28 (ii), "the changes of basis at `h_0` and `h_L`, those inside the heads … have orbits of dimension `2 d_model² + s` at generic parameters, where `E′` and `D′` have rank `d_model` and the queries and values of every head have full column rank"; "`d_model (d_model − 1) + s`" | SAME as a proof piece, at one parameter with these ranks; `L ≥ 1` |
| | `jacobianRank_add_le_skipless_ends_attention`, `…_rmsNorm` | proof of S Lemma A.26, "the rank is lower semicontinuous, so the bound holds at every `η`" | SAME (note C) |
| `Residual/SkiplessEndsTransformer.lean` | `funDim_add_le_skipless_ends_of_insideBlocks`, `…_rmsNorm` | the same proof piece | LEAN STRONGER: any architecture, any `V` spanned by `InsideBlocks` directions; `E` and `D` of rank `d`; no condition on `V` or on the writes (consistent with (5c), second case, where `D` has rank `d` and the bound holds) |
| | the 4 `jacobianRank_add_le_skipless_ends_attention{Mlp,Gated}{,_rmsNorm}` | the same, "and the rescalings" for gated units | SAME as a proof piece, in the wider model (note C) |
| `Residual/DifferentClassesAttention.lean` | `ae_forall_eval_residual_ne_skipless_attention`, `…_rmsNorm` | S Theorem 4.11 (i), "equals no skipless network of the same widths"; Theorem A.28 (ii) | SAME, given Sard's theorem as a hypothesis; fewer conditions on the heads than the Scope |
| | `exists_batch_ae_exists_pos_le_norm_sub_skipless_attention`, `…_rmsNorm` | S Theorem A.28 (iv) | LEAN STRONGER in the order of the quantifiers (note D), given the two literature hypotheses |
| | `ae_not_isPointwiseLimit_skipless_attention`, `…_rmsNorm` | S Theorem 4.11 (i), "and is not a pointwise limit of such networks"; Definition A.29 | SAME, given the two literature hypotheses |
| `Residual/DifferentClassesTransformer.lean` | the 8 `ae_forall_eval_residual_ne_skipless_attention_{tanh,gelu,swiglu,geglu}{,_rmsNorm}` and the 4 general forms | S Theorem 4.11 (i), first clause; Theorem A.28 (ii) | SAME, given Sard's theorem; LEAN STRONGER in the model and in the widths (Check 3 (b), note D) |
| | the 4 `exists_batch_ae_exists_pos_le_norm_sub_skipless_attention{Mlp,Gated}{,_rmsNorm}` | S Theorem A.28 (iv) | LEAN STRONGER in the order of the quantifiers, given the two literature hypotheses; no named form for tanh, GELU, SwiGLU, GeGLU (they are instances of the general forms) |
| | the 8 `ae_not_isPointwiseLimit_skipless_attention_{tanh,gelu,swiglu,geglu}{,_rmsNorm}` and the 4 general forms | S Theorem 4.11 (i), second clause | SAME, given the two literature hypotheses |
| `Residual/LocallyUniform.lean` | `isPointwiseLimit_of_tendstoUniformlyOn_isCompact` | S Section 4.3, "This is the case when a sequence of them converges to `F` uniformly on compact sets of inputs" | SAME |
| | `isPointwiseLimit_of_tendstoLocallyUniformly` | the same sentence, for locally uniform convergence | SAME (on `ℝ^{T×d_in}` the two notions of convergence agree; each is stated) |
| | `not_tendstoLocallyUniformly_of_not_isPointwiseLimit`, `not_tendstoUniformlyOn_isCompact_of_not_isPointwiseLimit` | S Theorem 4.11 (i), "In particular, it cannot be locally uniformly approximated by such networks" | PART: the implication for any set of functions; the sentence for the networks follows in one step (note E, compiled) |

### Notes

**A. `χ` of a sum.** `Arch.sum A B` takes `χ := A.χ` and drops `B.χ`. In `Arch.attentionMlp` and
`Arch.attentionGated` both parts are built with the same `χ`, so nothing is lost there; for a sum
of two architectures with different `χ` the second part would read `A.χ(h)`. The header of
`Network/Sum.lean` says "The map `χ` is that of `A`"; the index row does not (correction 9).

**B. Theorem 4.2 numerically** (by the computation, `thm42_check.out`; 18 networks, two random
draws each; batch of about `2P` output numbers and more; the smallest singular value counted is
`6.5 · 10⁻⁷` of the largest and the largest one not counted `9.5 · 10⁻¹⁶`, so every rank is read
off a gap of nine orders of magnitude).

| Networks | Rank without skips against `P − (L+1) dim 𝒢 − s` | Rank with identity skips against `P − dim 𝒢 − s` |
|---|---|---|
| The paper's model, inside the hypotheses, 9 networks: `d = 3`, [attention `H = 1, d_h = 3`, then tanh 3]: 27 = 27 and 45 = 45; the same with ReLU: 24 and 21 against 24, 42 = 42; [tanh 4, then attention `H = 3, d_h = 1`]: 48 = 48, 66 = 66; the same with ReLU: 44 = 44, 62 = 62; the first two under RMSNorm (`ε = 0.3`): tanh 45 = 45, 51 = 51; ReLU 42 and 30 against 42, 48 = 48; `d = 2`, attention `H = 2, d_h = 1` then ReLU² 3, SwiGLU 2, ReGLU 2: 17 = 17, 18 = 18, 16 = 16 and 25 = 25, 26 = 26, 24 = 24 | at most the bound in 18 of 18; equal in 16 (the two below are skipless ReLU networks, as S Section 4.4 expects) | equal in 18 of 18 |
| Heads and hidden units in one block (Lean only), 3 networks | at most the bound in 6 of 6; equal in 5 | equal in 6 of 6 |
| **Outside the hypotheses, `d_h > d`:** `d = 2`, one head of width 3, alone or followed by tanh 2 or ReLU 2 | the rank is the formula **plus 2** in 6 of 6 (12 against 10, 10 against 8, 8 against 6) | the formula **plus 2** in 6 of 6 (20 against 18, 18 against 16, 12 against 10) |
| Outside: total width of a skipless block below `d` (2 networks) | at most the formula in 4 of 4 | equal in 4 of 4 (no width is asked with skips) |
| Outside: `d_in < d` (1 network) | below the formula | below the formula |

So `d_h ≤ d` is needed: for `d_h = 3 > d = 2` the count `2 H d_h² = 18` is too large by 2, the
changes of basis inside the head move the parameters in only 16 independent directions (a `2 × 3`
query matrix cannot have column rank 3). I saw no case in which `hW` or `d_in ≥ d` is needed for
the truth of the inequality; the proof needs them (S Remark A.19 reports the same for narrow
attention blocks followed by a wide MLP block).

**C. "Rank `≤ P − 2d² − s` at EVERY parameter and on every batch": true?** Yes, under the written
hypotheses (`L ≥ 1`, `d_in, d_out ≥ d`, `d_h ≤ d`, a real-analytic activation or gate, `ε > 0`
under RMSNorm; `d ≥ 1` with gated blocks). The reason in one line: the rank of the Jacobian of a
continuously differentiable map cannot jump up in a limit (the set of parameters where it is at
most `r` is closed), and the bound holds on a set of full measure, which is dense. `L ≥ 1` is
needed (for `L = 0` the network is `x E D`, of rank `P − d²`). By the computation
(`ends_check.out`, 7 skipless networks: attention alone with `L = 1` and `L = 2`, with `H d_h < d`,
under RMSNorm; attention then tanh; attention then SwiGLU; the last under RMSNorm; 98 runs): at
generic parameters and at degenerate ones (a zero head; a zero query matrix; `E` of rank 1; `D` of
rank 1; a zero head and `E` of rank 1; a value matrix of rank 1; `E = 0`; all weights `0`) the
rank is at most the bound in 98 of 98. For one attention block (`d = 2`, 2 heads of width 1) it
equals the bound at a generic parameter (12 = 12; 18 = 18 under RMSNorm) and drops at the
degenerate ones (6 with a zero head, 8 with `E` of rank 1, 5 with both, 0 at zero). In 5 runs at
degenerate parameters double precision does not separate the rank cleanly; counting every singular
value above `10⁻¹³` of the largest still gives at most 12 against 16, 9 against 18, 14, 17 and 19
against 22.

**D. Theorem 4.11 (i) and Theorem A.28 (iv): the three conclusions.**

- "equals no skipless network of the same widths": `∀ᵐ θ ∂μ, ∀ η : Params (Arch.attentionMlp …)
  dIn dOut, eval (…) 1 θ ≠ eval (…) 0 η`. The two sides are functions on all inputs; `1` is the
  network with identity skips and `0` the one without. **The skipless parameter `η` is arbitrary:
  it is bound by `∀ η` inside `∀ᵐ θ`, with no measure and no condition on it.** "Of the same
  widths" is "of the same architecture": the same heads, head widths, hidden units, activation,
  mask and `χ`, hence also the same order of the blocks.
- Theorem A.28 (iv), "almost every choice of weights of the residual network `F` has a finite set
  `X` of inputs and a `δ > 0` such that every such skipless network `G` has `‖G(x) − F(x)‖ ≥ δ` at
  some `x ∈ X`": Lean has `∃ n X, ∀ᵐ θ ∂μ, ∃ δ > 0, ∀ η, ∃ i, δ ≤ ‖eval (…) 1 θ (X i) − eval (…) 0
  η (X i)‖`. One batch serves almost every `θ`; this implies the paper's order. The norm is the
  largest absolute entry; another norm changes `δ` by a constant.
- "is not a pointwise limit of such networks": `¬ IsPointwiseLimit (Set.range (eval (…) 0)) (eval
  (…) 1 θ)`, with `IsPointwiseLimit` word for word Definition A.29 (`∀ n ≥ 1, ∀ X, ∀ δ > 0, ∃ F' ∈
  𝓕, ∀ i, ‖F' (X i) − F (X i)‖ < δ`).
- **The hypotheses from the literature.** `SardCriticalValues E F`: for every Haar measure of `F`
  and every real-analytic `g : E → F`, the image of the points where the derivative of `g` is not
  onto has measure zero; asked for `E` the parameters of the skipless network and `F = ℝ^r`, every
  `r`. `ClosureNullOfNull S`: for every linear `π` to some `ℝ^r`, if `π(S)` has measure zero then
  so has its closure; asked for `S` the set of outputs of the skipless networks on each finite
  batch. Both are arguments of the theorems; no axiom is declared (compiled, Check 3). For the
  general forms with an arbitrary real-analytic `σ` the second hypothesis may fail for an
  activation that is not definable; the statement is then empty for that `σ`, not false. For
  attention, tanh, GELU, SwiGLU and GeGLU it is what S Lemma A.21 and Lemma A.23 give.
- By compiling (`Chk3.lean`, `thm411_gelu_causal_rmsNorm`; `Chk5.lean`): the first clause for the
  paper's networks of attention and GELU blocks within the Scope, causal mask, pre-RMSNorm with
  `ε > 0`, follows from the Lean statement with no hypothesis beyond the Scope, `L ≥ 1` and Sard's
  theorem.

**E. `Residual/LocallyUniform.lean` against "In particular, it cannot be locally uniformly
approximated by such networks".** The four statements are about any set `𝓕` of functions
`ℝ^{T×d_in} → ℝ^{T×d_out}` and a sequence `G : ℕ → …` with `∀ k, G k ∈ 𝓕`:

1. `isPointwiseLimit_of_tendstoUniformlyOn_isCompact`: if `G` converges to `F` uniformly on every
   compact set, `F` is a pointwise limit of `𝓕`. This is the sentence of S Section 4.3.
2. `isPointwiseLimit_of_tendstoLocallyUniformly`: the same from `TendstoLocallyUniformly G F
   atTop`.
3. `not_tendstoLocallyUniformly_of_not_isPointwiseLimit`: if `F` is not a pointwise limit of `𝓕`,
   no sequence of `𝓕` converges to `F` locally uniformly.
4. `not_tendstoUniformlyOn_isCompact_of_not_isPointwiseLimit`: the same for uniform convergence on
   every compact set.

They are true and say what the index says. Two remarks. (i) The last sentence of Theorem 4.11 (i)
is not a statement about the networks in this file; the index says so ("it is not restated kind
by kind"). The combination is one step: by compiling (`Chk3.lean`, `last_sentence_tanh`), for
attention and tanh blocks, at almost every `θ`, for every sequence `η k` of skipless parameters,
the skipless networks `eval (…) 0 (η k)` converge to the residual network neither locally
uniformly nor uniformly on every compact set. (ii) The statements speak of sequences. "Locally
uniformly approximated" can also be read without a sequence: on every compact set and for every
`δ > 0` some network of the set is `δ`-close. That reading is excluded too: it makes `F` a
pointwise limit, since a finite set is compact (compiled, `Chk3.lean`,
`isPointwiseLimit_of_forall_isCompact`).

**F. The bound without skips and the dimension paper.** The docstrings and the two index rows call
the bounds without skips "Theorem 4.3 of the dimension paper for attention blocks and MLP blocks".
D's Scope (`dim.txt` line 207) says "all blocks of a network are of one kind", so D Theorem 4.3
as stated is about networks of one kind of block. The Lean statement is S Theorem 4.2 (whose Scope
has attention blocks and MLP blocks of one kind), proved by the argument of D Lemma B.1, whose
wording ("a network whose blocks are tanh, GELU, ReLU, ReLU² or gated blocks …, or attention
blocks …") does allow both. Against D Theorem 4.3 the verdict is LEAN STRONGER (two kinds of
block); the label should say so (correction 5). The same remark applies to S itself: "The bound
without skips is Theorem 4.3 of Karbevski (2026)" (`skips.txt` line 450) is exact only for
networks of one kind of block, if D's Scope is read as written.

---------------------------------------------------------------------------------------------------

## What the authors should know

Nothing false, nothing vacuous and no statement that changed after its first commit. In order of
weight:

1. **The index is out of date in one paragraph** ("Not stated yet from the main text of the skips
   paper", line 644): it lists Theorem 4.2 for networks that mix attention and MLP blocks as not
   stated, and Theorem 4.11 (i) for transformers as "in work". Both are stated and proved in the
   files of this audit, and their rows say "proved" (corrections 1, 2).
2. **A misquotation.** The header of `Symmetry/InsideBlocks.lean` and its index row quote S
   Section 4.1 as "change only the read and the write of one block". The paper (text of the PDF and
   the current `.tex`, line 340) has "which change the read and the write of one block and leave
   the map of that block unchanged", without "only" (correction 4).
3. **A row that says "Not stated" of statements that exist.** The row of
   `Symmetry/InsideBlocksKinds.lean` ends "Not stated: the rescalings of the hidden units of ReLU
   and ReLU² blocks and of the gates of ReGLU blocks". They are stated, in
   `Dimension/UpperBoundTransformerRescale.lean` (correction 3).
4. **The label "D Theorem 4.3 for networks of attention blocks and MLP blocks"** names a theorem
   whose Scope has one kind of block (note F). The Lean statements are true; the label claims a
   little more for the dimension paper than it states. The sentence of S after Theorem 4.2 has the
   same gap.
5. **The Lean model is wider than the paper's** (a block may have heads and hidden units side by
   side). The paper's networks are the case of one empty part per block, as functions and in the
   parameter count (compiled). The statements are stronger, not different.
6. **`InsideBlocks` is wider than the paper's list of symmetries**: any curve that keeps `E`, `D`
   and the block maps. At a parameter with a dead unit the moves of that unit's write row satisfy
   it (compiled). No bound is false for this reason; the hypothesis `hrw` of the bounds without
   skips is needed and does its work (in the case (5c) the count without it gives 4 and the rank
   is 5).
7. **`1 ≤ d_h ≤ d` and the two tokens are asked of every block and of every network**, also where
   there is no head. For a block without heads the head width is a free choice (take width 1), so
   no network of the paper is excluded; a network of MLP blocks alone on one token is an instance
   of the twin files, not of these.
8. **A hypothesis that the proof does not use**: `hε : 0 < ε` in
   `funDim_add_le_skipless_ends_attention_rmsNorm` (the compiler's linter reports it,
   `compile13.out`). The general form `funDim_add_le_skipless_ends_of_insideBlocks_rmsNorm` is for
   any `ε`. Harmless: the paper's case is `ε > 0`.
9. **Theorem A.28 (iv) is stated with one batch for almost every `θ`**, which is more than the
   paper's "almost every choice of weights … has a finite set `X`". If the paper wants the stronger
   form, its proof (Lemma A.26 (ii): the batch is the one on which the Jacobian of the residual
   network reaches its rank at `θ₀`) already gives it.
10. **The two literature hypotheses** are the only hypotheses of the Lean forms of Theorem 4.11
    (i) that the paper's statement does not have. They are hypotheses, not axioms.
11. **The last sentence of Theorem 4.11 (i)** is not a named statement about the networks; it is
    one step from two named statements (compiled for attention and tanh blocks). The Lean
    statements speak of sequences; the reading without sequences follows as well (note E).
12. **Outside the hypotheses**: for `d_h > d` both Lean formulas are exceeded by the measured rank
    (by 2 for one head of width 3 on `d = 2`). The hypothesis `d_h ≤ d` is needed and present.
13. The first file's bounds with ReLU, ReLU² or ReGLU as `σ` are weaker than the paper's (no
    rescalings of the units, resp. of the gates); the header and the row say so, and the second
    file has the paper's value. A reader who looks only at `ae_funDim_add_le_skipless_attentionMlp`
    for a ReLU network gets a true and weaker bound.
14. "Under pre-RMSNorm (any `ε`)" includes `ε ≤ 0`, where the network is not the paper's; for
    `ε = 0` the paper's bound has the larger group `CO(d)` (D, after Theorem 4.3), so the Lean
    bound with `d(d−1)/2` is true and weaker there.

## Corrections for `STATEMENTS.md`

Line numbers at `2fc98cc`. At `591d9e4` the same sentences stand three lines lower from line 644
to line 767 and ten lines lower from line 772 on; the list of line 154 has not moved. The
two sentences of corrections 1 and 2 and the thirteen rows are unchanged there.

1. Line 644, paragraph "Not stated yet from the main text of the skips paper": delete "Theorem
   4.2 for networks that mix attention and MLP blocks (for networks of attention blocks it is
   proved, `Dimension/UpperBoundAttention.lean`);". It is stated and proved
   (`Dimension/UpperBoundTransformer.lean`, `Dimension/UpperBoundTransformerRescale.lean`).
2. Line 672, same paragraph: "and in work for transformers,
   `Residual/DifferentClassesTransformer.lean`" → "and for transformers,
   `Residual/DifferentClassesTransformer.lean`". The file has no `sorry` and its 28 theorems
   depend on the standard axioms only. In the same paragraph "Lemma A.27, Theorem 4.7 and
   Corollary 4.9 for networks that mix attention and MLP blocks" is listed as not stated; the
   commit messages from `540f071` to `2fc98cc` say that they are proved for transformers. Those
   files are outside this brief; I did not read them.
3. Line 757, row of `Symmetry/InsideBlocksKinds.lean`: "Not stated: the rescalings of the hidden
   units of ReLU and ReLU² blocks and of the gates of ReGLU blocks" → "The rescalings of the
   hidden units of ReLU and ReLU² blocks and of the gates of ReGLU blocks are in
   `Dimension/UpperBoundTransformerRescale.lean` (`insideBlocks_rescaleDirMlp`,
   `insideBlocks_rescaleDirGate`)".
4. Line 755, row of `Symmetry/InsideBlocks.lean`: `they "change only the read and the write of one
   block and leave the map of that block unchanged"` → `"which change the read and the write of
   one block and leave the map of that block unchanged"`. The same in the header of
   `Symmetry/InsideBlocks.lean`, lines 7 to 9. Worth adding to the row: the property is wider than
   the paper's list (any curve that keeps `E`, `D` and the map of every block; for example the
   moves of the write row of a hidden unit whose read column is `0`); every such direction is
   flat.
5. Lines 758 and 759, rows of the two `UpperBoundTransformer` files: "S Theorem 4.2 (both bounds)
   and D Theorem 4.3 for networks of attention blocks and MLP blocks" → "S Theorem 4.2 (both
   bounds) for networks of attention blocks and MLP blocks; the bound without skips is D Theorem
   4.3 carried to two kinds of block by the proof of D Lemma B.1 (D's Scope has one kind of
   block)". The same wording in the docstrings "Theorem 4.3 of the dimension paper for attention
   blocks and MLP blocks".
6. Line 758: after "(`d_in ≥ d`, `d_h ≤ d`; …)" add "and `d ≥ 1` with gated blocks" (the eight
   `ae_…attentionGated…` forms have `[Nonempty d]`, and need it). The header of
   `Dimension/UpperBoundTransformer.lean`, lines 29 to 32, lacks it too.
7. Line 766, row of `Residual/SkiplessEndsTransformer.lean`: in "(real-analytic activation or
   gate, `d_in, d_out ≥ d`, `d_h ≤ d`)" add "`L ≥ 1`" and "`d ≥ 1` with gated blocks".
8. Lines 767 and 773, rows of the two `DifferentClasses` files: add "the conditions `1 ≤ d_h ≤ d`
   are asked of every block, also of a block without heads, where the head width is a free choice;
   the two tokens are asked also when no block has a head".
9. Line 753, row of `Network/Sum.lean`: add "the map `χ` of the sum is that of `A`".
10. Line 774, row of `Residual/LocallyUniform.lean`: add "(for sequences of functions of `𝓕`)".
11. Lines 154 to 164, "Not yet compared by such a reader": take out the thirteen files of this
    audit (`Network/Sum.lean`, `Network/Transformer.lean`, `Generic/Sum.lean`,
    `Symmetry/InsideBlocks.lean`, `Symmetry/InsideBlocksSum.lean`,
    `Symmetry/InsideBlocksKinds.lean`, `Dimension/UpperBoundTransformer.lean`,
    `Dimension/UpperBoundTransformerRescale.lean`, `Residual/SkiplessEndsAttention.lean`,
    `Residual/SkiplessEndsTransformer.lean`, `Residual/DifferentClassesAttention.lean`,
    `Residual/DifferentClassesTransformer.lean`, `Residual/LocallyUniform.lean`).

Nothing is missing from the thirteen rows: all 127 public names are covered and the statuses
("proved", "definitions") are right at the audited commit.

## What I could not check

- **The proofs.** The brief is about statements. I know only that the thirteen files compile
  without `sorry` and that every public name depends on the three standard axioms.
- **The two literature hypotheses themselves.** That Sard's theorem holds in the form
  `SardCriticalValues`, and that the sets of outputs of these networks have the property
  `ClosureNullOfNull` (S Lemma A.21 with Lemma A.23), is not proved in Lean and I did not verify
  it against van den Dries or Speissegger.
- **The files that these rest on and that are outside the brief**: `Residual/DepthTransformer*.lean`
  (the residual parameter of large functional dimension used in the private helpers of
  `Residual/DifferentClassesTransformer.lean`), `Residual/DifferentClassesCriterion.lean`,
  `Dimension/UpperBoundAttention.lean`. I read the statements that are called, not the files.
- **The comparison of `funDim` with the paper's `fd` for ReLU, ReLU² and ReGLU blocks** I took
  from the index note and from reading the definitions; I did not compile it again.
- **The claim that `InsideBlocks` at generic parameters gives exactly the paper's `s`** is by
  hand for attention heads and an expectation for tanh blocks; it is not needed for any verdict.
- **The numerical checks** are small networks (`d ≤ 3`, `L ≤ 2`, at most 84 parameters), two or
  three random draws each, in double precision; they can support and refute, not prove. Five runs
  at degenerate parameters did not give a clean rank (note C).
- **The absorb paper.** The header of `Network/Sum.lean` quotes its Theorem 4.3; I checked only
  that the quoted words stand in the current `.tex` (line 360), not the statement.
- I compiled against a copy of the build of `/home/claude/lp/lean` taken at 16:12 UTC, not against
  a fresh build of `2fc98cc`; the copies of the thirteen files that I compiled are the sources of
  `lw`.
