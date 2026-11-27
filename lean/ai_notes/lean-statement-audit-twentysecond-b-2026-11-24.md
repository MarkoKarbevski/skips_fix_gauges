STATUS: complete

# Twenty-second audit, part B, of Lean statements against the papers: S Theorems A.17 (ii), (iii) and A.12 (ii), (iii) for `ε = 0`; S Theorem B.1 (iii) for `ε = 0`, "at most" (24 November 2026)

Reader: an independent reader who did not write the statements. Brief:
`audit22b_brief_2026-11-24.md` (rules of work and form of the report: `audit21a_brief_2026-11-24.md`).
I audited statements and definitions, not proofs. I changed no repository file, ran no
`lake build`, made no commit and no push. My files are in `/home/claude/audit22b/`.

Library: `/home/claude/lw/lean` (branch `lean-wip`).

- **Commit read: `38eefee4b07e0e7cd685a6553c175b738b8c62a1` (24 November 2026, 21:46:07 UTC),**
  the head when I started (21:47 UTC). The branch moved while I worked. At
  **`2b9d829009374fa5f76306b2ab8c8d285c65cfac` (22:14:34 UTC), the head when I finished,** five of
  the six files are as at `38eefee` (`git diff` is empty for them). The sixth,
  `OneBlock/LearnedSkipRMSZeroBound.lean`, got its open proof at `c63b4e1` (22:00:08 UTC): its
  header, its definition and its two public statements are the same text at `38eefee` and at
  `2b9d829` (compared by a script); 35 private helpers were added.
- **Files with `sorry`.** At `38eefee`: `OneBlock/LearnedSkipRMSZeroBound.lean` (one `sorry`, the
  proof of `funDimSkipsOn_add_le_learned_rmsNorm_zero`; the second theorem of the file,
  `funDimSkipsOn_learned_le_funDimOn_residual_add_rmsNorm_zero`, was proved from the first, so
  both rested on `sorry` at that commit), and `OneBlock/SkiplessHomogeneousRMSZeroEq.lean` (not a
  file of this audit). At `2b9d829`: no file under `SkipsLean/` contains the word.
- The six files have 50 public theorems (4 + 33 + 2 + 3 + 6 + 2) and 2 public definitions
  (`skipProdFwd`, `learnedZeroDomain`). All 52 depend on `propext`, `Classical.choice`,
  `Quot.sound` only (by compiling `Sig.lean`, output `Sig.out`, against the build of
  `/home/claude/lp/lean` at `2b9d829`, whose `SkipsLean/` was that of `/home/claude/lw` by
  `diff -rq`, with compiled files newer than the sources; for the two theorems of `LearnedSkipRMSZeroBound.lean` this is the state at `c63b4e1`
  and after).
- Written after I started and **not read by me:** `OneBlock/LearnedSkipRMSZeroBoundKinds.lean`,
  `OneBlock/LearnedSkipRMSZeroRescaleBound.lean`, `OneBlock/LearnedSkipTriangularRMSZeroBound.lean`
  (index rows 910 to 912 at `2b9d829`).

Papers, as text: the skips paper ("S", `<scratchpad>/skips.txt`) and, for one sentence, the
dimension paper ("D", `<scratchpad>/dim.txt`). Line numbers of `STATEMENTS.md` are those of
`2b9d829`: the rows of the six files are lines 839, 840, 841, 842, 843 and 909 (835 to 839 and 905
at `38eefee`, with the same text; the status of the last row was "in work" and is "proved").

**Short answer. Nothing false, nothing vacuous and nothing drifted was found.** The 28 generated
statements differ from their twins in the five listed ways and in nothing else. The counts are the
paper's. In 177 computed cases of networks with attention, gated, mixed and ReLU-type blocks no
rank is above a bound; the rank is equal to the bound in every case without a ReLU-type block
(105 of 105). Three things for the authors: (1) a skipless network with `ε = 0` in which only
some blocks are positively homogeneous (attention blocks and ReLU blocks, say) has all of `GL(d)`
at every hidden state that a ReLU-type block reads, so it does not attain the bound of
Theorem 4.2 either; the paper says this only for networks of positively homogeneous blocks;
(2) for tanh, GELU and SwiGLU blocks the "at most `d(d+1)/2 − 1`" of Theorem B.1 (iii) for `ε = 0`
is an equality in all 144 computed cases; (3) the independence of the two scalings in the proof of
that bound uses that `A` is invertible, which the paragraph for `ε = 0` does not say again. Three
sentences of the index are out of date; corrections are at the end.

How I checked.

- "By reading": every public statement, docstring and header of the six files; the definitions
  they use (`Arch`, `Params`, `hidden`, `eval`, `Arch.mlp`, `Arch.gated`, `Arch.attention`,
  `Arch.sum`, `Arch.attentionMlp`, `Arch.attentionGated`, `rmsRow`, `rmsNorm`, `jacobianRank`,
  `funDim`, `flat`, `flatOn`, `funDimOn`, `evalSkips`, `jacobianRankSkips`, `funDimSkips`,
  `funDimLearned`, `funDimSkipsOn`, `InsideBlocks`, `Params.sumFst`, `Params.sumSnd`, `cobDir`,
  `scaleDir`, `Params.cob`, `cobSkip`, `skipProd`, `blockFlatSphere`, `residualZeroDomain`); the
  statements of the library lemmas that the `ae_` statements rest on (`ae_rank_E_write`,
  `ae_rank_QV_uba`, `ae_rank_QV_ubt`, `ae_rank_E_ubt`, `ae_value_ne_zero_ubt`) and of the helpers
  `attn_part_ubt`, `gated_part_ubt`, `funDim_add_le_of_coScale_add_urz`, `sup_le_span_ibl`,
  `write_eq_zero_of_read_ibl`, `finrank_sup_ibl`; and the paper passages that the brief names
  (S Section 4.1 with Theorem 4.2 and Definition 4.3, the sentence on `G` at the head of
  Appendix A, Lemma A.3, Theorem A.12 with its proof, Appendix A.6 with Theorem A.17 and
  Lemma A.18, Theorem 3.2, Theorem B.1 with "Notation and flat directions", the proof of
  part (iii) with "The case `ε = 0`", the start of the proof of part (iv); D Theorem 4.3 with the
  sentence after it).
- "By hand": a short argument of my own, written where it is used.
- "By a script": `twins.py` (the 28 statements against their twins, and the four general bounds
  against theirs; output `twins.out`, the docstrings side by side in `twins_docs.txt`), and
  scripts of a few lines for the names in the index and in `checks/Axioms.lean`.
- "By compiling": scratch files in `/home/claude/audit22b/`, compiled with `lake env lean <file>`
  from `/home/claude/lp/lean` (nothing written there): `Sig.lean` (signatures with every instance
  argument, and axioms), `Chk.lean` (check 1: fifteen statements at `Measure.addHaar`), `Chk2.lean`
  (checks 2, 5, 6), `LSBchk.lean` (a copy of `OneBlock/LearnedSkipRMSZeroBound.lean` at `0ea49ee`,
  the same file as at `2b9d829`, with one check added). All compile without error and without
  `sorry`; every theorem of mine that I name below has the three standard axioms.
- "By a computation": my own scripts. `z22core.py`: networks of attention, MLP and gated blocks
  (one kind per block, or heads and hidden units side by side) under pre-RMSNorm with `ε = 0`,
  with no skips, identity skips or full learned skips; ball arithmetic (`python-flint`, `arb`)
  with 60 digits; exact derivatives in the weights by forward mode (dual numbers), checked
  against central differences in `z22fd.py` (they agree to `7.8·10⁻³⁵`, the error of the
  differences); the rank by elimination with complete pivoting on balls, where a pivot is taken
  only if its ball does not contain `0`. The weights and inputs are exact rationals, so the number
  of pivots is a certified lower bound of the rank of the Jacobian on the batch; the rank from the
  singular values in double precision is computed beside it. A zero row is normalized to `0`, as
  in Lean. A rank on a batch is a lower bound of the functional dimension.

---------------------------------------------------------------------------------------------------

## Part 1: the checks

### Check 1. Generic means almost every parameter, for every Haar measure

**Verdict: yes, in all 20 `ae_` statements of `Dimension/UpperBoundSymmetriesRMSNormZero.lean`;
every index type of the weights is finite; the statements apply to a concrete Haar measure.**
(By reading and by a script over the source; the shapes from the compiled signatures, `Sig.out`;
fifteen instances by compiling, `Chk.lean`.)

- The `variable` lines of the file:

  ```
  variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
    [Fintype dOut]
  variable {sees : T → T → Prop} [DecidableRel sees]
  variable {H dh hid : Fin L → Type} [∀ ℓ, Fintype (H ℓ)] [∀ ℓ, Fintype (dh ℓ)]
    [∀ ℓ, Fintype (hid ℓ)] {σ : ℝ → ℝ}
  ```
  The weights are `E : Matrix dIn d ℝ`, `read ℓ : Matrix d (r ℓ) ℝ`, `write ℓ : Matrix (w ℓ) d ℝ`,
  `D : Matrix d dOut ℝ`. For attention blocks `r ℓ = H ℓ × (dh ℓ ⊕ (dh ℓ ⊕ dh ℓ))` (queries, keys,
  values of every head) and `w ℓ = H ℓ × dh ℓ`; for MLP blocks `r ℓ = w ℓ = hid ℓ`; for gated
  blocks `r ℓ = hid ℓ ⊕ hid ℓ`, `w ℓ = hid ℓ`; for the two mixed architectures the disjoint sums of
  these. Every one of these types has `Fintype`.
- Each of the 20 statements has `(μ : Measure (Params …)) [μ.IsAddHaarMeasure]` and
  `∀ᵐ θ ∂μ`; none is "there is a parameter" or "on an open set" (a script over the 20 statement
  texts; none of the 33 statements of the file contains `∃` or `∀ᶠ`). For instance:

  ```
  theorem ae_funDim_add_le_skipless_attention_rmsNorm_zero [Nonempty d]
      (μ : Measure (Params (Arch.attention (T := T) (d := d) sees (rmsNorm 0) H dh) dIn dOut))
      [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
      (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d)
      (hH : ∀ ℓ, Fintype.card d ≤ Fintype.card (H ℓ) * Fintype.card (dh ℓ)) :
      ∀ᵐ θ ∂μ, funDim (Arch.attention sees (rmsNorm 0) H dh) 0 θ
          + ((L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
            + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
        ≤ Module.finrank ℝ
            (Params (Arch.attention (T := T) (d := d) sees (rmsNorm 0) H dh) dIn dOut)
  ```
- By compiling (`Chk.lean`): the space `Params …` of an attention network is finite-dimensional
  and carries the Borel σ-algebra of its topology; any two Haar measures on such a space have the
  same sets of measure zero (`null_iff_of_haar22`). Fifteen statements at the concrete measure
  `Measure.addHaar`, with the number of parameters computed (`finrank_params`,
  `finrank_params_mlp`, `finrank_params_gated`), so that each reads "for almost every `θ`,
  `funDim … θ ≤ n`":

  | my theorem | statement used | the network | `P` | conclusion |
  |---|---|---|---|---|
  | `skipless_attention_concrete22` | `ae_funDim_add_le_skipless_attention_rmsNorm_zero` | two tokens, no mask, `d = d_in = d_out = 2`, one block of two heads of width 1 | 24 | `funDim ≤ 16` |
  | `residual_attention_concrete22` | `ae_funDim_add_le_residual_attention_rmsNorm_zero` | the same | 24 | `funDim ≤ 18` |
  | `residual_gated_concrete22` | `ae_funDim_add_le_residual_gated_rmsNorm_zero` | one token, `d = 2`, two gated blocks of width 2, the gate tanh | 32 | `funDim ≤ 26` |
  | `skipless_attentionMlp_concrete22` | `ae_funDim_add_le_skipless_attentionMlp_rmsNorm_zero` | three tokens, causal mask, `d = 2`, `d_in = 3`, `d_out = 1`, one block with one head of width 2 and one tanh unit side by side | 28 | `funDim ≤ 16` |
  | `residual_attentionMlp_concrete22` | `ae_funDim_add_le_residual_attentionMlp_rmsNorm_zero` | the same | 28 | `funDim ≤ 18` |
  | `skipless_attentionGated_concrete22` | `ae_funDim_add_le_skipless_attentionGated_rmsNorm_zero` | two tokens, `d = 2`, one block: two heads of width 1 and two gated units | 36 | `funDim ≤ 26` |
  | `residual_attentionGated_concrete22` | `ae_funDim_add_le_residual_attentionGated_rmsNorm_zero` | the same | 36 | `funDim ≤ 28` |
  | `skipless_attention_relu_concrete22` | `ae_funDim_add_le_skipless_attention_relu_rmsNorm_zero` | two tokens, `d = 2`, two blocks, each with two heads of width 1 and three ReLU units | 64 | `funDim ≤ 44` |
  | `residual_attention_relu_concrete22` | `ae_funDim_add_le_residual_attention_relu_rmsNorm_zero` | the same | 64 | `funDim ≤ 48` |
  | `residual_attention_reluSq_concrete22` | `ae_funDim_add_le_residual_attention_reluSq_rmsNorm_zero` | `d = 2`, one block with no head and two ReLU² units (an MLP block alone) | 16 | `funDim ≤ 12` |
  | `skipless_attention_reglu_concrete22` | `ae_funDim_add_le_skipless_attention_reglu_rmsNorm_zero` | `d = 2`, one block: two heads of width 1 and two ReGLU units | 36 | `funDim ≤ 24` |
  | `residual_attentionMlp_rescale_concrete22` | `ae_funDim_add_le_residual_attentionMlp_rescale_rmsNorm_zero` | `d = 2`, one block: two heads of width 1 and three units with the activation `0`, with `k = 7` | 36 | `funDim ≤ 27` |
  | `skipless_relu_co_concrete22` | `ae_funDim_add_le_skipless_relu_rmsNorm_zero_co` | one token, `d = 2`, two ReLU blocks of width 3 | 32 | `funDim ≤ 20` |
  | `skipless_relu_strong_concrete22` | `ae_funDim_add_le_skipless_relu_rmsNorm_zero` (the bound that the `_co` form comes from) | the same | 32 | `funDim ≤ 16` |
  | `skipless_reglu_co_concrete22` | `ae_funDim_add_le_skipless_reglu_rmsNorm_zero_co` | one token, `d = 2`, one ReGLU block of width 2 | 20 | `funDim ≤ 12` |

  Every kind of network of the file has an instance. The instance with no head shows that the
  mixed statements contain the networks of MLP blocks alone; the activation `0` with `k = 7` shows
  what the general forms also cover (harmless: they are upper bounds).
- The two `ae_` statements of the other files (`ae_funDim_residual_eq_skipless_add_of_equality`,
  `ae_funDimLearned_eq_residual_add_of_equality`) take any measures, with no hypothesis on them:
  they pass an "almost every" from the hypotheses to the conclusion (check 5).

### Check 2. The 28 generated twins

**Verdict: each of the 28 differs from its twin in the five listed ways and in nothing else. The
count is the paper's `(L + 1) dim G + s`, resp. `dim G + s`, with `dim G = d(d−1)/2 + 1` and the
paper's `s`. `[Nonempty d]` is needed. The docstrings name the right theorem of the right paper.
No computed rank is above a bound (177 cases); the rank is equal to the bound in all 105 cases
without a ReLU-type block.** (The comparison by a script; the count and the docstrings by
reading; `[Nonempty d]` by compiling; the ranks by computation.)

- **The comparison** (`twins.py`). For each statement of the file whose name does not end in
  `_co`: the text from `theorem` to the `:=` that ends the statement, with white space
  normalized; in the twin's text, the name `X_rmsNorm` is replaced by `X_rmsNorm_zero`,
  ` (ε : ℝ)` is deleted, `rmsNorm ε` is replaced by `rmsNorm 0`, `[Nonempty d]` is put after the
  name if the twin does not have it, and `Fintype.card d * (Fintype.card d - 1) / 2` is replaced
  by `(Fintype.card d * (Fintype.card d - 1) / 2 + 1)`. The result is compared with the statement
  as a string. All 28 are equal; no `ε` is left in a statement.

  | statement | twin (file : line) | `(ε : ℝ)` removed | `rmsNorm ε` → `rmsNorm 0` | `[Nonempty d]` | count `+ 1` | equal after the five changes |
  |---|---|---|---|---|---|---|
  | `funDim_add_le_skipless_attention_rmsNorm_zero` | `UpperBoundAttention` : 154 | 1 | 3 | added | 1 | yes |
  | `funDim_add_le_residual_attention_rmsNorm_zero` | `UpperBoundAttention` : 322 | 1 | 3 | added | 1 | yes |
  | `ae_funDim_add_le_skipless_attention_rmsNorm_zero` | `UpperBoundAttention` : 451 | 1 | 3 | added | 1 | yes |
  | `ae_funDim_add_le_residual_attention_rmsNorm_zero` | `UpperBoundAttention` : 487 | 1 | 3 | added | 1 | yes |
  | `funDim_add_le_residual_gated_rmsNorm_zero` | `UpperBoundSymmetries` : 374 | 1 | 3 | added | 1 | yes |
  | `ae_funDim_add_le_residual_gated_rmsNorm_zero` | `UpperBoundSymmetries` : 404 | 1 | 3 | kept | 1 | yes |
  | `funDim_add_le_skipless_attentionMlp_rmsNorm_zero` | `UpperBoundTransformer` : 462 | 1 | 3 | added | 1 | yes |
  | `funDim_add_le_residual_attentionMlp_rmsNorm_zero` | `UpperBoundTransformer` : 505 | 1 | 3 | added | 1 | yes |
  | `ae_funDim_add_le_skipless_attentionMlp_rmsNorm_zero` | `UpperBoundTransformer` : 549 | 1 | 3 | added | 1 | yes |
  | `ae_funDim_add_le_residual_attentionMlp_rmsNorm_zero` | `UpperBoundTransformer` : 589 | 1 | 3 | added | 1 | yes |
  | `funDim_add_le_skipless_attentionGated_rmsNorm_zero` | `UpperBoundTransformer` : 633 | 1 | 3 | added | 1 | yes |
  | `funDim_add_le_residual_attentionGated_rmsNorm_zero` | `UpperBoundTransformer` : 681 | 1 | 3 | added | 1 | yes |
  | `ae_funDim_add_le_skipless_attentionGated_rmsNorm_zero` | `UpperBoundTransformer` : 730 | 1 | 3 | kept | 1 | yes |
  | `ae_funDim_add_le_residual_attentionGated_rmsNorm_zero` | `UpperBoundTransformer` : 774 | 1 | 3 | kept | 1 | yes |
  | `funDim_add_le_skipless_attentionMlp_rescale_rmsNorm_zero` | `UpperBoundTransformerRescale` : 818 | 1 | 3 | added | 1 | yes |
  | `funDim_add_le_residual_attentionMlp_rescale_rmsNorm_zero` | `UpperBoundTransformerRescale` : 873 | 1 | 3 | added | 1 | yes |
  | `ae_funDim_add_le_skipless_attentionMlp_rescale_rmsNorm_zero` | `UpperBoundTransformerRescale` : 929 | 1 | 3 | kept | 1 | yes |
  | `ae_funDim_add_le_residual_attentionMlp_rescale_rmsNorm_zero` | `UpperBoundTransformerRescale` : 979 | 1 | 3 | kept | 1 | yes |
  | `ae_funDim_add_le_skipless_attention_relu_rmsNorm_zero` | `UpperBoundTransformerRescale` : 1020 | 1 | 3 | kept | 1 | yes |
  | `ae_funDim_add_le_residual_attention_relu_rmsNorm_zero` | `UpperBoundTransformerRescale` : 1054 | 1 | 3 | kept | 1 | yes |
  | `ae_funDim_add_le_skipless_attention_reluSq_rmsNorm_zero` | `UpperBoundTransformerRescale` : 1090 | 1 | 3 | kept | 1 | yes |
  | `ae_funDim_add_le_residual_attention_reluSq_rmsNorm_zero` | `UpperBoundTransformerRescale` : 1124 | 1 | 3 | kept | 1 | yes |
  | `funDim_add_le_skipless_attentionGated_rescale_rmsNorm_zero` | `UpperBoundTransformerRescale` : 1171 | 1 | 3 | added | 1 | yes |
  | `funDim_add_le_residual_attentionGated_rescale_rmsNorm_zero` | `UpperBoundTransformerRescale` : 1228 | 1 | 3 | added | 1 | yes |
  | `ae_funDim_add_le_skipless_attentionGated_rescale_rmsNorm_zero` | `UpperBoundTransformerRescale` : 1286 | 1 | 3 | kept | 1 | yes |
  | `ae_funDim_add_le_residual_attentionGated_rescale_rmsNorm_zero` | `UpperBoundTransformerRescale` : 1338 | 1 | 3 | kept | 1 | yes |
  | `ae_funDim_add_le_skipless_attention_reglu_rmsNorm_zero` | `UpperBoundTransformerRescale` : 1380 | 1 | 3 | kept | 1 | yes |
  | `ae_funDim_add_le_residual_attention_reglu_rmsNorm_zero` | `UpperBoundTransformerRescale` : 1414 | 1 | 3 | kept | 1 | yes |

  Thirteen twins have `[Nonempty d]` already (they use that no read column of a hidden unit vanishes
  at generic parameters). The count is changed once in each statement, where it stands: under
  the factor `(L + 1)` without skips, alone with identity skips.
- **The count.** The paper (S, Theorem A.17 (ii)): "the functional dimension at these parameters
  is at most `P − (L + 1) dim G − s` without skips and `P − dim G − s` with them"; (head of
  Appendix A) "`G` is `GL(d_model)` without normalization, `O(d_model)` under RMSNorm with
  `ε > 0`, and `CO(d_model)`, the positive multiples of orthogonal matrices, under RMSNorm with
  `ε = 0`". `dim CO(d) = d(d−1)/2 + 1`. Lean: `(L + 1) * (card d * (card d - 1) / 2 + 1) + s`
  without skips and `(card d * (card d - 1) / 2 + 1) + s` with identity skips, written as sums
  on the left of `≤ P`, so that no subtraction of natural numbers can go wrong; `d(d−1)` is even.
  The paper's `s` (Appendix A.6): "Each hidden unit of a ReLU or ReLU² block can be rescaled, and
  so can the value of each hidden unit of a gated block and, in ReGLU, its gate […]. Each
  attention head has a change of basis between its queries and keys and one between its values
  and outputs, of dimension `d_h²` each". Lean: `2 ∑ H d_h²` for attention; `∑ d_hidden` for
  gated blocks with any gate (the values) and for MLP blocks with a positively homogeneous
  activation; `2 ∑ d_hidden` for gated blocks with a positively homogeneous gate; `0` for the MLP
  part with any activation (the paper's `s` for tanh and GELU). The same.
- **`[Nonempty d]` is needed.** By compiling (`Chk2.lean`): for `d = Fin 0` the space of the
  weights has dimension `0` (`finrank_params_of_isEmpty22`), `E` has rank `0 = card d`
  (`rank_E_of_isEmpty22`), and the conclusion of
  `funDim_add_le_residual_of_insideBlocks_rmsNorm_zero` with `V = ⊥` is false
  (`residual_conclusion_false_of_isEmpty22`): the count is `0·(0−1)/2 + 1 = 1 > 0 = P`. With
  `d` empty there are no hidden states to scale. For `d ≥ 1` the scale is a direction: the
  diagonal of an antisymmetric matrix is zero, so `Y + c I` gives `Y` and `c`.
- **The docstrings.** The twins say "Theorem 4.3 [of the dimension paper] …, under the conditions
  of Lemma B.1" (without skips) and "Theorem 4.2 of the skips paper" (with identity skips). All
  28 docstrings of the new file say "Theorem A.17 (ii) of the skips paper", with "under the
  conditions of Lemma A.18" at one parameter and "at generic parameters" for the `ae_` forms
  (`twins_docs.txt`); the words "dimension paper", "Lemma B.1" and "Theorem 4.3" do not occur in
  the file. This is right: D says after Theorem 4.3 "For `ε = 0` the same bound holds, with
  `G = CO(d_model)`, for the four kinds of block of the main result", which are not the kinds of
  this file, and S Theorem 4.2 / A.17 (ii) with Lemma A.18 ("With RMSNorm the changes of basis
  lie in `CO(d_model)` or `O(d_model)`, and the argument is unchanged") covers them all. The
  formulas in the docstrings agree with the statements (read one by one).
- **The hypotheses against Lemma A.18.** "If the embedding has rank `d_model` and every block has
  width at least `d_model` […]. With an embedding of rank `d_model`, it also holds for networks
  with attention blocks whose heads have width `d_h ≤ d_model` and total width
  `H d_h ≥ d_model`." Lean, at almost every `θ`: `d_in ≥ d`, `d_h ≤ d`, and without skips
  `d ≤ H_ℓ d_{h,ℓ}` (attention) or `d ≤ H_ℓ d_{h,ℓ} + d_hidden,ℓ` (mixed: for a block with no
  hidden unit this is the lemma's condition on an attention block, for a block with no head the
  one on an MLP block). With identity skips Lean asks no width. Nothing on `d_out`, the number
  of tokens or the mask.
- **The ranks** (`z22run.py`, outputs `z22_*.out`, summary `z22_summary.txt`). 59 networks, each
  at three parameters (entries of the weights random multiples of `10⁻⁶` in `[−1, 1]`): 177
  cases, `d = 2` and `3`, one, two or three tokens, no mask, one or two blocks, `P` from 20 to 90.
  At each parameter two batches of random inputs, each with at least `4P` output numbers (`16P`
  for the networks with a ReLU-type block); the rank of a case is the larger of the two. At every
  parameter the pointwise hypotheses of the Lean statement hold (certified with balls: `E` of
  rank `d`, without skips every write of rank `d`, every query and value matrix of rank `d_h`, no
  read column of a hidden unit zero), so there the Lean statement says `rank ≤ bound`. Over all
  cases the smallest pivot that is taken is `7.3·10⁻¹⁵` of the largest (a skipless network of an
  attention block and a tanh block; the rank from double precision is 22 there, the certified
  rank 26, which is the bound) and no entry that is left is above `1.4·10⁻⁴⁰`.

  **No rank is above a bound.** Equal to the bound: 136 cases. Below: 41 cases, all of networks
  with a ReLU, ReLU² or ReGLU block.

  | networks | cases | rank against the Lean bound |
  |---|---|---|
  | attention blocks, one or two blocks, `d = 2, 3`, `d_out = 1, 2, 3`; skipless | 21 | equal in 21 (for instance 16, 12, 22, 26, 42, 37, 14 for `P` = 24, 24, 42, 40, 66, 51, 22) |
  | the same; residual | 21 | equal in 21 (18, 14, 24, 30, 46, 41, 16) |
  | gated blocks (SiLU or GELU gate), one or two blocks; residual | 15 | equal in 15 |
  | attention and tanh or GELU blocks (in either order, or side by side); skipless | 15 | equal in 15 |
  | the same; residual | 15 | equal in 15 |
  | attention and gated blocks (SiLU or GELU gate); skipless | 9 | equal in 9 |
  | the same; residual | 9 | equal in 9 |
  | attention and ReLU or ReLU² blocks; residual | 18 | equal in 18 |
  | attention and ReGLU blocks; residual | 9 | equal in 8; 21 against 22 in one (a block with a head and two ReGLU units side by side; the other batch gave 20) |
  | an attention block and a ReLU or ReLU² block, one after the other; skipless | 15 | below in 15: by 2 for `d = 2` (12 cases), by 5 for `d = 3` (3 cases) |
  | an attention block and a ReGLU block, one after the other; skipless | 6 | below in 6: by 2 in four, by 8 and 16 in two (batches with few active units) |
  | heads and ReLU or ReGLU units side by side in one block; skipless | 6 | equal in 5; 19 against 20 in one |
  | ReLU, ReLU² or ReGLU blocks alone, one or two blocks; skipless (the `_co` forms) | 18 | below in 18 (check 4) |

  In the 105 cases without a ReLU-type block the rank is equal to the bound in every case and in
  both batches. A rank on a batch is a lower bound and the Lean statement is the upper bound at
  these weights, so there the functional dimension is the bound.
- **Where the rank is below the bound.** In a skipless network with `ε = 0`, if block `ℓ + 1` is
  a ReLU, ReLU² or ReGLU block alone, every invertible change of basis at `h_ℓ` preserves the
  function, not only those in `CO(d)`. By hand: `N_0(h G) G⁻¹ W_read = γ N_0(h) W_read` with a
  number `γ > 0` for each token; the block is positively homogeneous token by token, so `h_{ℓ+1}`
  is multiplied by a positive number for each token, and without a skip the next normalization
  removes it. Only block `ℓ + 1` has to be positively homogeneous. By a computation
  (`z22mixed.py`): with a general invertible `G` at the hidden state before a ReLU, ReLU² or
  ReGLU block that stands after or before an attention block, the output changes by at most
  `9.1·10⁻⁵⁶`; at the hidden state before a tanh block or before the attention block it changes
  by 0.14 and 1.3. This gives `d² − (d(d−1)/2 + 1) = d(d+1)/2 − 1` more flat directions for each
  such hidden state: 2 for `d = 2` and 5 for `d = 3`, which is the difference found in every one
  of the 15 cases with a ReLU or ReLU² block (for instance rank 21 against the bound 23 for
  `P = 36`, `d = 2`, and 53 against 58 for `P = 90`, `d = 3`). So the
  six skipless statements for attention with ReLU, ReLU² or ReGLU blocks, and the two general
  forms they come from, are true and are the bound of Theorem A.17 (ii) as written, but the bound
  is not attained when a block of the network is a ReLU-type block alone. The paper says this for
  networks of positively homogeneous blocks only (the remark after Theorem A.17; the last
  sentence of Theorem A.12 (iii); Lemma A.3 is stated for a network whose blocks are positively
  homogeneous). See the list for the authors.
- **A rank on a batch is a lower bound: two examples.** With heads and ReGLU units side by side,
  one parameter gave 21 and 20 on its two batches against the bound 22, and its two neighbours
  gave 22. For one ReLU block with a learned skip (check 7, outside these statements), a
  parameter with two kinks at the angles `44.0°` and `51.9°` gave rank 19 on two batches of 216
  random inputs and rank 20, the expected value, on inputs spread over the directions of `h_0`
  (`z22relu_one.py`, `z22relu_one.out`).

### Check 3. The general bounds

**Verdict: the four statements differ from their twins for any `ε` in the same five ways and in
nothing else; the hypotheses on `V` and the ranks are those of the twins; the count is
`(L + 1)(d(d−1)/2 + 1) + dim V`, resp. `(d(d−1)/2 + 1) + dim V`.** (By a script, by reading, and
by hand for the independence.)

- The Lean text:

  ```
  theorem funDim_add_le_skipless_of_insideBlocks_rmsNorm_zero [Nonempty d] (hA : A.χ = rmsNorm 0)
      (V : Submodule ℝ (Params A dIn dOut))
      (hV : V ≤ Submodule.span ℝ {η | InsideBlocks A θ η})
      (hrw : ∀ η ∈ V, ∀ ℓ, η.read ℓ = 0 → η.write ℓ = 0)
      (hE : θ.E.rank = Fintype.card d) (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d) :
      funDim A 0 θ
          + ((L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2 + 1) + Module.finrank ℝ V)
        ≤ Module.finrank ℝ (Params A dIn dOut)

  theorem funDim_add_le_residual_of_insideBlocks_rmsNorm_zero [Nonempty d] (hA : A.χ = rmsNorm 0)
      (V : Submodule ℝ (Params A dIn dOut))
      (hV : V ≤ Submodule.span ℝ {η | InsideBlocks A θ η})
      (hE : θ.E.rank = Fintype.card d) :
      funDim A 1 θ + ((Fintype.card d * (Fintype.card d - 1) / 2 + 1) + Module.finrank ℝ V)
        ≤ Module.finrank ℝ (Params A dIn dOut)
  ```
  and the two for `A.sum B` with `VA`, `VB`, the hypotheses on `θ.sumFst`, `θ.sumSnd`, and
  `Module.finrank ℝ VA + Module.finrank ℝ VB`. The twins are
  `funDim_add_le_skipless_of_insideBlocks_rmsNorm`, `funDim_add_le_residual_of_insideBlocks_rmsNorm`
  (`Symmetry/InsideBlocks.lean`, lines 222 and 311) and the two `…_sum_…` of
  `Symmetry/InsideBlocksSum.lean` (lines 387 and 418). The script of check 2 gives "equal after
  the five changes" for all four.
- `InsideBlocks A θ η`: `η` is the velocity at `θ` of a curve of parameters that keeps `E`, `D`
  and the map `n ↦ f_ℓ(n W_read^ℓ) W_write^ℓ` of every block: the paper's "A symmetry inside a
  block […] changes the read and the write of that block and leaves its map unchanged", as a
  direction. `hrw` ("read `0` gives write `0`") is the condition under which the induction of
  Lemma A.18 runs with a space `V` in place of the named rescalings.
- By hand, the independence for `ε = 0`. If `cobDir θ Y + scaleDir θ β + v = 0` with
  antisymmetric `Y_ℓ`, numbers `β_ℓ` and `v ∈ V`: at `E`, `E (Y_0 + β_0 I) = 0` (the directions of
  `V` do not move `E`), so `Y_0 = 0` and `β_0 = 0` (`E` of rank `d ≥ 1`). If `Y_ℓ = 0`: the read
  of block `ℓ + 1` moves by `−Y_ℓ W_read` plus the read of `v` (the scales do not move the
  reads), so the read of `v` is `0`, so its write is `0` (`hrw`), and the write gives
  `W_write (Y_{ℓ+1} + β_{ℓ+1} I) = 0`, so `Y_{ℓ+1} = 0`, `β_{ℓ+1} = 0` (the write of rank `d`).
  Then `v = 0`. With identity skips one `Y + β I` acts at all hidden states and `E` alone gives
  it. So the hypotheses are the ones the count needs, and the `L + 1` scales are counted once
  each without skips and once in all with identity skips, as in the paper.
- In the two statements for a sum, `hA` is on the first architecture: `(A.sum B).χ = A.χ` by
  definition, and the `χ` of `B` is not used.

### Check 4. The five `_co` corollaries

**Verdict: they are the bound of Theorem A.17 (ii) as written for skipless ReLU, ReLU² and ReGLU
networks, under the conditions of the statements they come from; and the index is right that
they are weaker than those.** (By reading; one pair by compiling; the ranks by computation.)

- Lean: `funDim … 0 θ + ((L + 1) * (card d * (card d - 1) / 2 + 1) + ∑ ℓ, card (hid ℓ)) ≤ P`
  (MLP blocks with a positively homogeneous activation, at one `θ`; ReLU and ReLU² at almost
  every `θ`), and the same with `2 * ∑ ℓ, card (hid ℓ)` (gated blocks with a positively
  homogeneous gate, at one `θ`; ReGLU at almost every `θ`). The hypotheses are those of
  `funDim_add_le_skipless_mlp_rescale_rmsNorm_zero`, `funDim_add_le_skipless_gated_gate_rmsNorm_zero`
  and of the three `ae_funDim_add_le_skipless_…_rmsNorm_zero` of
  `Dimension/UpperBoundHomogeneousRMSNormZero.lean`: `E` and every write of rank `d ≥ 1`, no read
  column zero (no value column and no gate column); at almost every `θ` for `d_in ≥ d` and
  widths at least `d`.
- The bound they come from is `P − L d² − (d(d−1)/2 + 1) − s`. The difference of the two counts
  is `L (d² − d(d−1)/2 − 1) = L (d(d+1)/2 − 1)`: zero for `d = 1` or `L = 0`, positive otherwise.
  So the `_co` forms are weaker, strictly for `d ≥ 2` and `L ≥ 1`. By compiling: for two ReLU
  blocks of width 3 with `d = 2`, the `_co` form gives `funDim ≤ 20` and the other `funDim ≤ 16`
  (`skipless_relu_co_concrete22`, `skipless_relu_strong_concrete22`).
- The paper says the same of its own bound: "Its functional dimension then lies below the bound
  of (ii), so it does not satisfy the equality condition". Computed (18 cases): for one block the
  rank is 11 against the `_co` bound 13 (`d = 2`, ReLU), 10 against 12 (`d = 2`, ReGLU), 25
  against 30 (`d = 3`, ReLU), in all three parameters each: the stronger bound exactly. For two
  blocks with `d = 2` the ranks are from 4 to 14, below the stronger bound (13, 13, 18) or equal
  to it in one case.
- The docstrings say "A consequence of the stronger bound `…`" and name the right statements.

### Check 5. Theorem A.17 (iii) and Theorem A.12 (iii) "as they are"

**Verdict: each Lean statement is the paper's sentence as a conditional, with the equality
condition written out as its equation; it has fewer hypotheses than the paper's and no content
beyond arithmetic. The count for learned skips, `P + L d² − (L + 1) g − s`, is the paper's. The
form with two measures is a fair reading. The two identities in `ℕ` are right; for `n = 0` the
second holds only because both sides are cut off at `0`.** (By reading; the identities and three
instances by compiling, `Chk2.lean`.)

- The Lean text:

  ```
  theorem funDim_residual_eq_skipless_add_of_equality (A : Arch T d L) (θ : Params A dIn dOut)
      (g s : ℕ)
      (h0 : funDim A 0 θ + ((L + 1) * g + s) = Module.finrank ℝ (Params A dIn dOut))
      (h1 : funDim A 1 θ + (g + s) = Module.finrank ℝ (Params A dIn dOut)) :
      funDim A 1 θ = funDim A 0 θ + L * g

  theorem ae_funDim_residual_eq_skipless_add_of_equality (A : Arch T d L) (g s : ℕ)
      (μ : Measure (Params A dIn dOut))
      (h0 : ∀ᵐ θ ∂μ, funDim A 0 θ + ((L + 1) * g + s) = Module.finrank ℝ (Params A dIn dOut))
      (h1 : ∀ᵐ θ ∂μ, funDim A 1 θ + (g + s) = Module.finrank ℝ (Params A dIn dOut)) :
      ∀ᵐ θ ∂μ, funDim A 1 θ = funDim A 0 θ + L * g

  theorem ae_funDimLearned_eq_residual_add_of_equality (A : Arch T d L) (g s : ℕ)
      (hg : g ≤ Fintype.card d ^ 2)
      (μ : Measure (Params A dIn dOut × (Fin L → Matrix d d ℝ))) (ν : Measure (Params A dIn dOut))
      (hl : ∀ᵐ p ∂μ, funDimLearned A p + ((L + 1) * g + s)
        = Module.finrank ℝ (Params A dIn dOut) + L * Fintype.card d ^ 2)
      (h1 : ∀ᵐ θ ∂ν, funDim A 1 θ + (g + s) = Module.finrank ℝ (Params A dIn dOut)) :
      ∀ᵐ p ∂μ, ∀ᵐ θ ∂ν, funDimLearned A p = funDim A 1 θ + L * (Fintype.card d ^ 2 - g)
  ```
- **Theorem A.17 (iii).** "If in addition both networks satisfy the equality condition, the skips
  raise the functional dimension by exactly `L dim G`, which is `L d_model²` without
  normalization." The equality condition (Definition 4.3): "its bound in Theorem 4.2 is attained
  at generic parameters". With `g = dim G` and the paper's `s`, `h0` and `h1` are the two
  equality conditions and the conclusion is the paper's. The skipless and the residual network
  have the same weights, so one `θ` for both is right. The paper's "in addition" (the symmetries
  act locally freely) is not asked: the conclusion follows from the two equations alone. Lean
  takes any numbers `g`, `s`, any architecture and any measure: nothing ties `g` to `G`. So the
  statement is the paper's sentence when it is used with `g = dim G`; all its content is in the
  hypotheses. **Not vacuous:** by compiling, with the two values of the library for tanh networks
  of any depth, without normalization (`g = d²`, `tanh_gain22`: at almost every `θ`,
  `funDim` with identity skips is `funDim` without skips plus `L d²`) and under pre-RMSNorm with
  `ε > 0` (`g = d(d−1)/2`, `tanh_gain_rmsNorm22`). For `ε = 0` I found no pair of statements of
  the library that fits `h0` and `h1`: for tanh networks the library has `h0`
  (`ae_funDim_tanh_skipless_rmsNorm_zero`) and no statement of the form `h1` (the value of the
  residual network for analytic blocks is for one block, at one parameter, on `funDimOn`); for
  ReLU-type blocks it has `h1` for one block, and `h0` is false at almost every `θ` (the row of
  `Dimension/UpperBoundHomogeneousRMSNormZero.lean`), as the paper says.
- **Theorem A.12 (iii), the first difference.** "Under the equality condition for the networks
  with learned skips, with identity skips and without skips, the functional dimension of the
  network with learned skips exceeds that of the residual network by `L (d_model² − dim G)`". The
  proof: "each of the `L + 1` hidden states carries its own copy of `G`. The network with learned
  skips has `L d_model²` more parameters than the residual network and `L` more copies of `G` in
  its symmetry group. If both satisfy the equality condition, the difference of their functional
  dimensions is therefore `L (d_model² − dim G)`". So the value for learned skips is
  `(P + L d²) − (L + 1) dim G − s`: Lean's `hl` (Table 2 has the same row without normalization:
  `P + L d²` parameters, `(L + 1) d² + s` dimensions of symmetry). `funDimLearned` is the
  functional dimension in the weights and `L` full `d × d` skips. `hg : g ≤ d²` makes the
  subtraction `d² − g` exact.
- **The two measures.** The paper compares two numbers, the functional dimension of each network
  at generic parameters; the two networks have different parameter spaces. "For almost every
  weights and skips `p` and almost every weights `θ`, `fd(p) = fd(θ) + L (d² − g)`" says exactly
  that the two generic values differ by this number. The library's statements for one block
  (`ae_funDimLearned_tanh_rmsNorm_eq_residual_add` and its like) have the same form. Not stated:
  the form "at almost every `(θ, A)`, against the residual network with the same `θ`"; for Haar
  measures it follows from `hl` and `h1` in the same way. **Not vacuous:** by compiling
  (`tanh_learned_gain22`), `ae_funDimLearned_eq_residual_add_of_equality` with `g = d(d−1)/2`,
  `s = 0`, the two values of the library for one tanh block with `ε > 0`
  (`ae_funDimLearned_tanh_rmsNorm`, `ae_funDim_tanh_residual_rmsNorm`) and
  `sq_sub_half_mul_pred` gives the library's `ae_funDimLearned_tanh_rmsNorm_eq_residual_add`.
- **The second difference** of Theorem A.12 (iii) ("that of the residual network exceeds that of
  the skipless network by `L dim G`") is Theorem A.17 (iii), as the paper's proof says; the
  header and the index say so.
- **The identities.** `sq_sub_half_mul_pred (n : ℕ) : n ^ 2 - n * (n - 1) / 2 = n * (n + 1) / 2`
  and `sq_sub_half_mul_pred_add_one (n : ℕ) : n ^ 2 - (n * (n - 1) / 2 + 1) = n * (n + 1) / 2 - 1`.
  The paper: "`L d_model (d_model + 1)/2` […] for `ε > 0`, and `L (d_model (d_model + 1)/2 − 1)`
  […] for `ε = 0`". By compiling (`decide` for `n < 12`): both hold; the values of the second at
  `n = 0, 1, 2, 3` are `0, 0, 2, 5`. For `n = 1`: `1 − 1 = 0 = 1 − 1`, true in the integers too.
  For `n = 0` the first is `0 = 0`, and the second is `0 − 1 = 0 − 1` with both sides cut off at
  `0` in `ℕ` (in the integers both sides are `−1`, so it is true there as well; with `d = 0`
  there is nothing to count).

### Check 6. Theorem A.12 (ii)

**Verdict: `skipProdFwd` is the paper's `Π_ℓ = A_1 ⋯ A_ℓ` with `Π_0 = I`; with `G_ℓ = Π_ℓ⁻¹`,
`K_ℓ = P_ℓ⁻¹` the four kinds of weight of `θ.cob G K` are the paper's, each with the right index;
"every `A_ℓ = c_ℓ Q_ℓ`" is equivalent to "every `Π_ℓ` lies in `CO(d)`"; the identity holds at
every input, also those with a zero row. Computed for depth 2 and 3: the two sides differ by at
most `3·10⁻⁵⁵`.** (By reading; the entries by compiling, `Chk2.lean`; by a computation.)

- The Lean text:

  ```
  def skipProdFwd (S : Fin L → GL d ℝ) : Fin (L + 1) → GL d ℝ :=
    Fin.induction (motive := fun _ => GL d ℝ) 1 (fun ℓ P => P * S ℓ)

  theorem eval_learned_eq_residual_rmsNorm_zero_fwd (hA : A.χ = rmsNorm 0) (S Q : Fin L → GL d ℝ)
      (c : Fin L → ℝ) (hc : ∀ ℓ, 0 < c ℓ)
      (hQ : ∀ ℓ, (Q ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ)
      (hS : ∀ ℓ, (S ℓ : Matrix d d ℝ) = c ℓ • (Q ℓ : Matrix d d ℝ)) :
      eval A (fun ℓ => (S ℓ : Matrix d d ℝ)) θ x
        = eval A 1 (θ.cob (fun ℓ => (skipProdFwd S ℓ)⁻¹) (fun ℓ => (skipProdFwd Q ℓ)⁻¹)) x
  ```
- **The products.** In `hidden`, `h_{ℓ+1} = h_ℓ * S ℓ + …` for `ℓ : Fin L`, so `S ℓ` is the
  paper's `A_{ℓ+1}`. `skipProdFwd S 0 = 1` and `skipProdFwd S ℓ.succ = skipProdFwd S ℓ.castSucc * S ℓ`
  (`skipProdFwd_zero`, `skipProdFwd_succ`): `Π_{ℓ+1} = Π_ℓ A_{ℓ+1}`. By compiling, for two blocks:
  `skipProdFwd S 1 = S 0` and `skipProdFwd S 2 = S 0 * S 1`, that is `Π_1 = A_1`,
  `Π_2 = A_1 A_2`; and for the backward products `skipProd S 0 = S 0 * S 1`, that is
  `Λ_0 = A_1 A_2`.
- **The weights.** `Params.cob θ G K` has `E := θ.E * G 0`, `read ℓ := (K ℓ.castSucc)⁻¹ * θ.read ℓ`,
  `write ℓ := θ.write ℓ * G ℓ.succ`, `D := (K (Fin.last L))⁻¹ * θ.D`. By compiling
  (`cob_fwd_entries22`), with `G ℓ = (skipProdFwd S ℓ)⁻¹` and `K ℓ = (skipProdFwd Q ℓ)⁻¹`:

  | weight | Lean | the paper |
  |---|---|---|
  | embedding | `θ.E` | "the embedding `E`" |
  | read of block `ℓ + 1` (Lean's `read ℓ`) | `skipProdFwd Q ℓ.castSucc * θ.read ℓ`, that is `P_ℓ W_read^{ℓ+1}` | "the reads `P_{ℓ−1} W_read^ℓ`" |
  | write of block `ℓ + 1` (Lean's `write ℓ`) | `θ.write ℓ * (skipProdFwd S ℓ.succ)⁻¹`, that is `W_write^{ℓ+1} Π_{ℓ+1}⁻¹` | "the writes `W_write^ℓ Π_ℓ⁻¹`" |
  | readout | `skipProdFwd Q (Fin.last L) * θ.D`, that is `P_L D` | "the readout `P_L D`" |

  with `P_ℓ = Q_1 ⋯ Q_ℓ` the forward products of the orthogonal factors. The same indices.
- **The hypothesis.** The paper: "If every `Π_ℓ` lies in `G`, write `Π_ℓ = c_ℓ P_ℓ` with `c_ℓ > 0`
  and `P_ℓ` orthogonal". Lean: every `A_ℓ = c_ℓ Q_ℓ` with `c_ℓ > 0` and `Q_ℓ` orthogonal. By
  hand: `CO(d)` is a group; if every `A_ℓ` lies in it, so does every product
  `Π_ℓ = (c_1 ⋯ c_ℓ)(Q_1 ⋯ Q_ℓ)`; if every `Π_ℓ` lies in it, so does `A_ℓ = Π_{ℓ−1}⁻¹ Π_ℓ`.
  Equivalent. The paper's `c_ℓ` is the scale of `Π_ℓ`, Lean's `c ℓ` the scale of `A_ℓ`; the
  paper's `P_ℓ`, the orthogonal factor of `Π_ℓ`, is Lean's `skipProdFwd Q ℓ` (the factor is
  unique for `d ≥ 1`). The skips are of type `GL d ℝ`: "whose skips `A_ℓ` are invertible in (i)
  and (ii)".
- **Every input.** The statement is for every `x`, with no condition. It rests on
  `rmsNorm_zero_mul_smul_orthogonal : rmsNorm 0 (h * (c • Q)) = rmsNorm 0 h * Q` for every `h`,
  also with zero rows (a zero row stays a zero row and is normalized to `0` on both sides). So
  there is no input at which the identity could fail for Lean's function; the paper leaves the
  function undefined where a normalized row vanishes.
- **The other two statements.** `eval_learned_eq_residual_rmsNorm_fwd (ε : ℝ)`: orthogonal skips,
  any `ε`, `θ.cob Π⁻¹ Π⁻¹`: the paper's case `c_ℓ = 1`, `P_ℓ = Π_ℓ`.
  `eval_learned_eq_residual_rmsNorm_zero`: `θ.cob (skipProd S) (skipProd Q)`, the form of Theorem
  3.2 with the backward products (embedding `E Λ_0`, reads `(Λ^Q_{ℓ−1})⁻¹ W_read^ℓ`, writes
  `W_write^ℓ Λ_ℓ`, readout `D`); the paper has this form for orthogonal skips only (Theorem 3.2
  (ii), "Under pre-RMSNorm, the same holds when every `A_ℓ` is orthogonal"), so for `ε = 0` it is
  that sentence for skips in `CO(d)`.
- **Computed** (`z22cob.py`, `z22cob.out`; 60 digits; the `Q_ℓ` are Cayley transforms of
  rational antisymmetric matrices, half of them times a reflection, orthogonal to `4·10⁻⁶⁰`;
  `c_ℓ` between 0.19 and 4.98; 20 inputs each). Eight networks: two tanh blocks (`d = 2`, `3`); a
  ReLU block and a SwiGLU block; an attention block and a GELU block; two attention blocks on
  three tokens; three blocks (tanh, attention, ReGLU); and two of these again with ten inputs in
  which one token is zero. Outputs up to 2.2. The network with the learned skips against the
  residual network with the paper's weights: largest difference `3.0·10⁻⁵⁵`; against the residual
  network with the weights of the backward form: `2.9·10⁻⁵⁴`. Control: against the residual
  network with the weights unchanged the difference is between 1.1 and 3.2.

### Check 7. Theorem B.1 (iii) for `ε = 0`, "at most"

**Verdict: `learnedZeroDomain` is the paper's set of inputs for `ε = 0`; the count
`d(d−1) + 2` and `blockFlatSphere` as `K_B` are the paper's; the second theorem is the paper's
"at most" at one parameter, with each network on its own inputs; "`A` invertible" is the paper's
(it holds at generic parameters, and the paper's proof uses it). For tanh, `d = 2` and `3`, the
difference of the two ranks is `2` and `5`, that is `d(d+1)/2 − 1`, in all 48 cases: at most the
bound, and equal to it.** (By reading and by hand; one identity by compiling, `LSBchk.lean`; the
ranks by computation.)

- The Lean text (the same at `38eefee`, where the first proof was `sorry`, and at `2b9d829`):

  ```
  def learnedZeroDomain (A : Arch T d 1) (θ : Params A dIn dOut) (R : Fin 1 → Matrix d d ℝ) :
      Set (Matrix T dIn ℝ) :=
    {x | (∀ t, (x * θ.E) t ≠ 0) ∧
      ∀ t, (x * θ.E * R 0 + A.f 0 (rmsNorm 0 (x * θ.E) * θ.read 0) * θ.write 0) t ≠ 0}

  theorem funDimSkipsOn_add_le_learned_rmsNorm_zero {A : Arch T d 1} [Nonempty d]
      (hA : A.χ = rmsNorm 0) (hf : AnalyticOnNhd ℝ (A.f 0) Set.univ) (θ : Params A dIn dOut)
      (R : Fin 1 → Matrix d d ℝ) (hE : θ.E.rank = Fintype.card d) (hR : IsUnit (R 0).det) :
      funDimSkipsOn A (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) (θ, R)
          (learnedZeroDomain A θ R)
          + ((Fintype.card d * (Fintype.card d - 1) + 2)
            + Module.finrank ℝ (blockFlatSphere A θ))
        ≤ Module.finrank ℝ (Params A dIn dOut) + Fintype.card d ^ 2

  theorem funDimSkipsOn_learned_le_funDimOn_residual_add_rmsNorm_zero {A : Arch T d 1}
      [Nonempty T] (hA : A.χ = rmsNorm 0) (hd : 2 ≤ Fintype.card d)
      (hf : AnalyticOnNhd ℝ (A.f 0) Set.univ) (θ : Params A dIn dOut)
      (R : Fin 1 → Matrix d d ℝ) (hE : θ.E.rank = Fintype.card d)
      (hD : θ.D.rank = Fintype.card d) (hR : IsUnit (R 0).det)
      (hw : ∃ w : Matrix T dIn ℝ, ∀ t, LinearIndependent ℝ
        ![(w * θ.E) t, (A.f 0 (rmsNorm 0 (w * θ.E) * θ.read 0) * θ.write 0) t]) :
      funDimSkipsOn A (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) (θ, R)
          (learnedZeroDomain A θ R)
        ≤ funDimOn A 1 θ (residualZeroDomain A θ)
          + (Fintype.card d * (Fintype.card d + 1) / 2 - 1)
  ```
- **The inputs.** The paper ("Notation and flat directions"): "With `ε = 0`, it also excludes the
  inputs at which a state that is normalized vanishes." The states that are normalized are `h_0`
  (before the read of the block) and `h_1 = x E A + g(x)` (before the readout). The set is "no row
  of `h_0` and no row of `h_1` is zero", with the skip `A = R 0` in `h_1`: the paper's. For
  `R = 1` it is `residualZeroDomain` (by compiling, `learnedZeroDomain_one22`), as the docstring
  says. The blocks of the file are analytic, so no kinks are to be excluded.
- **The count and `K_B`.** The paper: "For the learned skip, `η^rot` and `K_B` are flat, which
  gives at least `d_model (d_model − 1) + 2`, respectively `d_model (d_model − 1)/2 + 2`,
  dimensions besides `K_B`". Lean, for a full skip: `(card d * (card d - 1) + 2) + finrank V_θ`
  against `P + d²`, the number of parameters with a full learned skip.
  `d(d−1) + 2 = 2 (d(d−1)/2 + 1)`: the rotation and the scaling of `h_0` and of `h_1`.
  `blockFlatSphere A θ` is the span of the directions `ψ` with `ψ.E = 0`, `ψ.D = 0` and
  `fderiv (A.f 0) (n W_read) (n ψ_read) W_write + A.f 0 (n W_read) ψ_write = 0` for every `n`
  whose rows have squared norm `d`: "the space `K_B` of directions of the block along which `B`
  has derivative zero on the sphere".
- **By hand, that the hypotheses suffice.** The directions of `η^rot` are flat at every input
  (they are directions of symmetries). A direction of `V_θ` leaves `h_1` unchanged to first order
  where no row of `x E` is zero (the block then reads rows on the sphere), and `N_0` is
  differentiable at `h_1` where no row of `h_1` is zero: this is where the set of inputs is used.
  Independence: the entry at `E` is `E (X_a + c_0 I)`, which gives `X_a` and `c_0` (`E` of rank
  `d ≥ 1`); the entry at `A` is `A (Y + c I) − (X_a + c_0 I) A`, which then gives `Y` and `c`
  (`A` invertible); a direction of `V_θ` has the entries `0` at `E`, `A` and `D`. No rank of `D`,
  no `d ≥ 2`, no width.
- **The second theorem.** It is the first together with the value for the residual network
  (`funDimOn_residual_rmsNorm_zero_eq`, twentieth audit): `P + d² − (d(d−1) + 2) − dim V_θ` minus
  `P − (d(d−1)/2 + 1) − dim V_θ` is `d² − d(d−1)/2 − 1 = d(d+1)/2 − 1`. Its hypotheses are those of
  that value (`d ≥ 2`, `E` and `D` of rank `d`, one input `w` with the rows of `w E` and `g(w)`
  independent for every token) and `A` invertible. The paper: "For generic parameters […] For
  `ε = 0` it exceeds that of the residual network with `ε = 0` by at most
  `d_model (d_model + 1)/2 − 1`". The paper compares the functional dimension of the network with
  the learned skip at generic `(θ, A)` with that of the residual network at generic weights. Lean
  compares them at one `(θ, A)` and the same `θ`, each network on the inputs at which none of its
  own normalized rows vanishes, which is the set of inputs of each in the paper. Every hypothesis
  holds at generic `(θ, A)` (for the last one this was compiled for a tanh block by the twentieth
  reader), so the statement gives the paper's sentence for a full skip and an analytic block; the
  form at almost every `(θ, A)` is not in this file (the index says so; it is in a file written
  after I started, which I did not read).
- **"`A` invertible".** The paper's proof of part (iii): "Steps 1 and 2 of part (ii) run with
  `EA` in place of `E`, which has rank `d_model` since `A` is invertible for generic parameters".
  A full skip `A` is a parameter, and an invertible `A` is generic. So `hR` is the paper's
  genericity, named. In the Lean statement it is what makes the second scaling independent
  (above).
- **What is not in the file** (the header and the index say so): the upper triangular skip
  (`d(d−1)/2 + 2`); ReLU, ReLU² and ReGLU blocks, for which the paper has the equality.
- **Computed** (`z22learn.py`, outputs `z22learn_tanh.out`, `z22learn_other.out`). One block, one
  token (these blocks act on every token alone), `ε = 0`; `d = 2, 3`; `(d_in, d_out) = (d, d)` and
  `(d + 1, d)`; widths `1, d, d + 1, 2d`; at each size two random parameters with a random skip
  `A`, and the first of them again with `A = I` as the value of the learned skip. The rank of the
  Jacobian in the weights and the skip (`P + d²` columns), and the rank of the Jacobian of the
  residual network in the weights at the same weights; two batches each, at least four output
  numbers for each column. `E`, `D` and `A` have rank `d` (certified). The two batches agree in
  every case; the smallest pivot is `2.9·10⁻⁷` of the largest and no entry that is left is above
  `1.4·10⁻⁴¹`.

  | block | `d` | cases | rank with the learned skip | rank of the residual network | difference | `d(d+1)/2 − 1` |
  |---|---|---|---|---|---|---|
  | tanh | 2 | 24 | `P + 4 − 4 = P` (12 to 26) | `P − 2` (10 to 24) | 2 in all 24 | 2 |
  | tanh | 3 | 24 | `P + 9 − 8 = P + 1` (25 to 58) | `P − 4` (20 to 53) | 5 in all 24 | 5 |
  | GELU | 2 | 24 | `P` | `P − 2` | 2 in all 24 | 2 |
  | GELU | 3 | 24 | `P + 1` | `P − 4` | 5 in all 24 | 5 |
  | SwiGLU | 2 | 24 | `P − s` | `P − 2 − s` | 2 in all 24 | 2 |
  | SwiGLU | 3 | 24 | `P + 1 − s` | `P − 4 − s` | 5 in all 24 | 5 |

  (`s` the number of hidden units, the rescalings of the values.) So for tanh with `d = 2` and
  `3`: the difference is at most `d(d+1)/2 − 1`, and it is equal to it. The rank with the learned
  skip is the Lean bound with `dim V_θ = 0` (tanh, GELU) and `dim V_θ = s` (SwiGLU), and the rank
  of the residual network is the value of `funDimOn_residual_rmsNorm_zero_eq` with the same
  `dim V_θ`; the statement is now proved, so at these weights `dim V_θ` is `0`, resp. `s`, and the
  two functional dimensions are these numbers. Widths below `d` and the skip `A = I` give the
  same. The paper claims the equality for ReLU, ReLU² and ReGLU blocks only.

### Check 8. The index rows and the axiom file

**Verdict: every sentence of the six rows is true of the statements, with two sentences that
other rows have overtaken (below). Every public theorem of the six files is in its row and, for
the proved files, in `checks/Axioms.lean`; the sixteen helpers that were made public are in the
rows of their files and in `checks/Axioms.lean`.** (By reading; the names by a script.)

- The names. For each file, the public names of the source are exactly the names of the third
  cell of its row: 4, 33, 2, 3, 7 (with the definition `skipProdFwd`) and 3 (with the definition
  `learnedZeroDomain`). All 50 theorems are in `checks/Axioms.lean` at `2b9d829` (the two of
  `LearnedSkipRMSZeroBound.lean` since its proof; at `38eefee`, with the file "in work", they
  were not). The two definitions are not there; neither are the older definitions that I looked
  for (`skipProd`, `cobDir`, `scaleDir`, `residualZeroDomain`, `blockFlatSphere`).
- The sixteen helpers (`sup_le_span_ibl`, `write_eq_zero_of_read_ibl`, `finrank_sup_ibl`;
  `attn_part_ubt`, `gated_part_ubt`, `ae_rank_QV_ubt`, `ae_rank_E_ubt`, `ae_value_ne_zero_ubt`;
  `attn_part_ubr`, `mlp_part_ubr`, `gate_part_ubr`, `ae_rank_QV_ubr`, `ae_rank_E_ubr`,
  `ae_sumSnd_col_ne_zero_ubr`; `funDim_add_le_of_coScale_add_urz`; `ae_rank_QV_uba`): each is in
  the third cell of the row of its file (lines 838, 845, 846, 895, 819) and in
  `checks/Axioms.lean`. The first cells of these rows do not say what the helpers state. Two
  definitions were made public with them, `sumInlLin_ibl` and `sumInrLin_ibl`
  (`Symmetry/InsideBlocksSum.lean`; the three `_ibl` helpers are stated with them): they are in
  no row.
- Row 839 (`Symmetry/InsideBlocksRMSNormZero.lean`): each clause is true (check 3).
- Row 840 (`Dimension/UpperBoundSymmetriesRMSNormZero.lean`): each clause on the 33 statements is
  true (checks 1, 2, 4). "Every statement asks `d ≥ 1`; `d_in ≥ d`, `d_h ≤ d`, and without skips
  writes of at least `d` rows, as the twins": true of the `ae_` forms. "With the rows of […],
  part (ii) for `ε = 0` is stated for every kind of network of the paper": by the heads of those
  rows, yes. Its last sentence, "Not stated: part (iii) for `ε = 0`", was written before the next
  row: `Residual/GainUnderEquality.lean` states part (iii) for any `χ` and any number `g`, so
  also for `ε = 0` with `g = d(d−1)/2 + 1`, as a conditional. What the library does not have is
  a pair of equalities for `ε = 0` to use it with.
- Row 841 (`Residual/GainUnderEquality.lean`) and row 842
  (`Residual/LearnedGainUnderEquality.lean`): each clause is true (check 5). "for a network with
  learned skips of depth above one, and for `ε = 0`, the library has none": by the names of the
  statements on `funDimLearned` (all for one block and `ε > 0`), yes.
- Row 843 (`Residual/LearnedSkipsConformal.lean`): each clause is true (check 6). "Every `Π_ℓ`
  lies in `CO(d)` if and only if every `A_ℓ` does" is a remark, not a Lean statement; it is true.
- Row 909 (`OneBlock/LearnedSkipRMSZeroBound.lean`): each clause on the statements is true
  (check 7). Its last sentence, "Not stated: the upper triangular skip; ReLU, ReLU², ReGLU blocks
  and the equality for them; the forms at almost every parameter for the kinds of block", is
  true of the file and no longer of the library: rows 910 to 912 state the forms at almost
  every parameter, the bound for ReLU-type blocks and the upper triangular skip.
- Row 819 (`Dimension/UpperBoundAttention.lean`, the twins): "for `ε = 0` this counts `O(d)`,
  one less per hidden state than the papers' `CO(d)`, and the bound with `CO(d)` and `s` for
  attention blocks is not stated". It is stated now: the first four statements of row 840.
- Lines 238 to 253 ("Not yet compared by such a reader …") name the six files.

---------------------------------------------------------------------------------------------------

## Part 2: the statements, file by file

Verdicts: SAME, LEAN STRONGER (the paper's claim under fewer hypotheses or for more cases),
LEAN WEAKER, DIFFERENT, PART (a part of the paper's sentence), FALSE. All 50 theorems are proved
with the three standard axioms (`Sig.out`).

### `Symmetry/InsideBlocksRMSNormZero.lean` (4 theorems)

The paper sentence for all four: S Theorem 4.2 / A.17 (ii), "the functional dimension at these
parameters is at most `P − (L + 1) dim G − s` without skips and `P − dim G − s` with them", for
`ε = 0` (`G = CO(d_model)`), with Lemma A.18.

| theorem | verdict |
|---|---|
| `funDim_add_le_skipless_of_insideBlocks_rmsNorm_zero` | LEAN STRONGER: one `θ`, any architecture, any space `V` of directions of symmetries inside the blocks in place of the paper's kinds and their `s`; "locally freely at generic parameters" is replaced by "`E` and the writes have rank `d ≥ 1`, and in `V` read `0` gives write `0`" |
| `funDim_add_le_residual_of_insideBlocks_rmsNorm_zero` | LEAN STRONGER: the same with identity skips, under "`E` has rank `d ≥ 1`" alone (no width) |
| `funDim_add_le_skipless_sum_of_insideBlocks_rmsNorm_zero` | LEAN STRONGER: the same for two kinds of block in one network, with `dim V_A + dim V_B` |
| `funDim_add_le_residual_sum_of_insideBlocks_rmsNorm_zero` | LEAN STRONGER: the same with identity skips |

### `Dimension/UpperBoundSymmetriesRMSNormZero.lean` (33 theorems)

The paper sentence for all 33: the one above. The 28 generated twins:

| statement | network | `s` in Lean | form | verdict against S Theorem A.17 (ii) with Lemma A.18 |
|---|---|---|---|---|
| `funDim_add_le_skipless_attention_rmsNorm_zero` | attention blocks, skipless | `2 ∑ H d_h²` | one `θ` | LEAN STRONGER: one `θ`; "locally freely at generic parameters" is replaced by the rank conditions |
| `funDim_add_le_residual_attention_rmsNorm_zero` | attention blocks, residual | `2 ∑ H d_h²` | one `θ` | LEAN STRONGER: one `θ`; "locally freely at generic parameters" is replaced by the rank conditions (no rank of a write) |
| `ae_funDim_add_le_skipless_attention_rmsNorm_zero` | attention blocks, skipless | `2 ∑ H d_h²` | almost every `θ` | SAME, under the conditions of Lemma A.18 (`d_in ≥ d`, `d_h ≤ d`, at least `d` write rows in every block) |
| `ae_funDim_add_le_residual_attention_rmsNorm_zero` | attention blocks, residual | `2 ∑ H d_h²` | almost every `θ` | LEAN STRONGER: no width of a block (Lemma A.18 asks it) |
| `funDim_add_le_residual_gated_rmsNorm_zero` | gated blocks, any gate, residual | `∑ d_hidden` | one `θ` | LEAN STRONGER: one `θ`; "locally freely at generic parameters" is replaced by the rank conditions (no rank of a write) |
| `ae_funDim_add_le_residual_gated_rmsNorm_zero` | gated blocks, any gate, residual | `∑ d_hidden` | almost every `θ` | LEAN STRONGER: no width of a block (Lemma A.18 asks it) |
| `funDim_add_le_skipless_attentionMlp_rmsNorm_zero` | attention and MLP blocks, any activation, skipless | `2 ∑ H d_h²` | one `θ` | LEAN STRONGER: one `θ`; "locally freely at generic parameters" is replaced by the rank conditions |
| `funDim_add_le_residual_attentionMlp_rmsNorm_zero` | attention and MLP blocks, any activation, residual | `2 ∑ H d_h²` | one `θ` | LEAN STRONGER: one `θ`; "locally freely at generic parameters" is replaced by the rank conditions (no rank of a write) |
| `ae_funDim_add_le_skipless_attentionMlp_rmsNorm_zero` | attention and MLP blocks, any activation, skipless | `2 ∑ H d_h²` | almost every `θ` | SAME, under the conditions of Lemma A.18 (`d_in ≥ d`, `d_h ≤ d`, at least `d` write rows in every block) |
| `ae_funDim_add_le_residual_attentionMlp_rmsNorm_zero` | attention and MLP blocks, any activation, residual | `2 ∑ H d_h²` | almost every `θ` | LEAN STRONGER: no width of a block (Lemma A.18 asks it) |
| `funDim_add_le_skipless_attentionGated_rmsNorm_zero` | attention and gated blocks, any gate, skipless | `2 ∑ H d_h² + ∑ d_hidden` | one `θ` | LEAN STRONGER: one `θ`; "locally freely at generic parameters" is replaced by the rank conditions |
| `funDim_add_le_residual_attentionGated_rmsNorm_zero` | attention and gated blocks, any gate, residual | `2 ∑ H d_h² + ∑ d_hidden` | one `θ` | LEAN STRONGER: one `θ`; "locally freely at generic parameters" is replaced by the rank conditions (no rank of a write) |
| `ae_funDim_add_le_skipless_attentionGated_rmsNorm_zero` | attention and gated blocks, any gate, skipless | `2 ∑ H d_h² + ∑ d_hidden` | almost every `θ` | SAME, under the conditions of Lemma A.18 (`d_in ≥ d`, `d_h ≤ d`, at least `d` write rows in every block) |
| `ae_funDim_add_le_residual_attentionGated_rmsNorm_zero` | attention and gated blocks, any gate, residual | `2 ∑ H d_h² + ∑ d_hidden` | almost every `θ` | LEAN STRONGER: no width of a block (Lemma A.18 asks it) |
| `funDim_add_le_skipless_attentionMlp_rescale_rmsNorm_zero` | attention and MLP blocks, positively homogeneous activation, skipless | `2 ∑ H d_h² + ∑ d_hidden` | one `θ` | LEAN STRONGER: one `θ`; "locally freely at generic parameters" is replaced by the rank conditions |
| `funDim_add_le_residual_attentionMlp_rescale_rmsNorm_zero` | attention and MLP blocks, positively homogeneous activation, residual | `2 ∑ H d_h² + ∑ d_hidden` | one `θ` | LEAN STRONGER: one `θ`; "locally freely at generic parameters" is replaced by the rank conditions (no rank of a write) |
| `ae_funDim_add_le_skipless_attentionMlp_rescale_rmsNorm_zero` | attention and MLP blocks, positively homogeneous activation, skipless | `2 ∑ H d_h² + ∑ d_hidden` | almost every `θ` | SAME, under the conditions of Lemma A.18 (`d_in ≥ d`, `d_h ≤ d`, at least `d` write rows in every block) |
| `ae_funDim_add_le_residual_attentionMlp_rescale_rmsNorm_zero` | attention and MLP blocks, positively homogeneous activation, residual | `2 ∑ H d_h² + ∑ d_hidden` | almost every `θ` | LEAN STRONGER: no width of a block (Lemma A.18 asks it) |
| `ae_funDim_add_le_skipless_attention_relu_rmsNorm_zero` | attention and ReLU blocks, skipless | `2 ∑ H d_h² + ∑ d_hidden` | almost every `θ` | SAME, under the conditions of Lemma A.18 (`d_in ≥ d`, `d_h ≤ d`, at least `d` write rows in every block) |
| `ae_funDim_add_le_residual_attention_relu_rmsNorm_zero` | attention and ReLU blocks, residual | `2 ∑ H d_h² + ∑ d_hidden` | almost every `θ` | LEAN STRONGER: no width of a block (Lemma A.18 asks it) |
| `ae_funDim_add_le_skipless_attention_reluSq_rmsNorm_zero` | attention and ReLU² blocks, skipless | `2 ∑ H d_h² + ∑ d_hidden` | almost every `θ` | SAME, under the conditions of Lemma A.18 (`d_in ≥ d`, `d_h ≤ d`, at least `d` write rows in every block) |
| `ae_funDim_add_le_residual_attention_reluSq_rmsNorm_zero` | attention and ReLU² blocks, residual | `2 ∑ H d_h² + ∑ d_hidden` | almost every `θ` | LEAN STRONGER: no width of a block (Lemma A.18 asks it) |
| `funDim_add_le_skipless_attentionGated_rescale_rmsNorm_zero` | attention and gated blocks, positively homogeneous gate, skipless | `2 ∑ H d_h² + 2 ∑ d_hidden` | one `θ` | LEAN STRONGER: one `θ`; "locally freely at generic parameters" is replaced by the rank conditions |
| `funDim_add_le_residual_attentionGated_rescale_rmsNorm_zero` | attention and gated blocks, positively homogeneous gate, residual | `2 ∑ H d_h² + 2 ∑ d_hidden` | one `θ` | LEAN STRONGER: one `θ`; "locally freely at generic parameters" is replaced by the rank conditions (no rank of a write) |
| `ae_funDim_add_le_skipless_attentionGated_rescale_rmsNorm_zero` | attention and gated blocks, positively homogeneous gate, skipless | `2 ∑ H d_h² + 2 ∑ d_hidden` | almost every `θ` | SAME, under the conditions of Lemma A.18 (`d_in ≥ d`, `d_h ≤ d`, at least `d` write rows in every block) |
| `ae_funDim_add_le_residual_attentionGated_rescale_rmsNorm_zero` | attention and gated blocks, positively homogeneous gate, residual | `2 ∑ H d_h² + 2 ∑ d_hidden` | almost every `θ` | LEAN STRONGER: no width of a block (Lemma A.18 asks it) |
| `ae_funDim_add_le_skipless_attention_reglu_rmsNorm_zero` | attention and ReGLU blocks, skipless | `2 ∑ H d_h² + 2 ∑ d_hidden` | almost every `θ` | SAME, under the conditions of Lemma A.18 (`d_in ≥ d`, `d_h ≤ d`, at least `d` write rows in every block) |
| `ae_funDim_add_le_residual_attention_reglu_rmsNorm_zero` | attention and ReGLU blocks, residual | `2 ∑ H d_h² + 2 ∑ d_hidden` | almost every `θ` | LEAN STRONGER: no width of a block (Lemma A.18 asks it) |

Notes on the table. The general forms take any activation `σ` (for ReLU the form without the
rescalings is weaker than the paper's bound; the forms with `hσ` have them) and any `σ` with
`σ(λ z) = λ^k σ(z)` for `λ > 0`, `k : ℕ`, also the activation `0`; any mask; a block may have
heads and hidden units side by side. The skipless statements with a positively homogeneous
activation or gate are true and are the paper's bound, and the bound is not attained when a
block is of that kind alone (check 2).

The five corollaries:

| theorem | verdict |
|---|---|
| `funDim_add_le_skipless_mlp_rescale_rmsNorm_zero_co` | SAME as the bound of A.17 (ii) as written, at one `θ` (conditions: `E` and the writes of rank `d ≥ 1`, no read column zero), for any positively homogeneous activation; LEAN WEAKER than `funDim_add_le_skipless_mlp_rescale_rmsNorm_zero`, by `L (d(d+1)/2 − 1)` |
| `funDim_add_le_skipless_gated_gate_rmsNorm_zero_co` | the same for gated blocks with a positively homogeneous gate, `s = 2 ∑ d_hidden` |
| `ae_funDim_add_le_skipless_relu_rmsNorm_zero_co` | SAME as the bound of A.17 (ii) as written for skipless ReLU networks at generic parameters (`d_in ≥ d`, widths at least `d`: Lemma A.18); the paper says that the bound is not attained ("lies below the bound of (ii)") |
| `ae_funDim_add_le_skipless_reluSq_rmsNorm_zero_co` | the same for ReLU² |
| `ae_funDim_add_le_skipless_reglu_rmsNorm_zero_co` | the same for ReGLU, `s = 2 ∑ d_hidden` |

### `Residual/GainUnderEquality.lean` (2 theorems)

| theorem | paper sentence | verdict |
|---|---|---|
| `funDim_residual_eq_skipless_add_of_equality` | S Theorem A.17 (iii): "If in addition both networks satisfy the equality condition, the skips raise the functional dimension by exactly `L dim G`" | SAME as a conditional at one `θ`, when used with `g = dim G` and the paper's `s`; fewer hypotheses (no "locally freely"; any numbers `g`, `s`; any architecture). Arithmetic: the content is in the two hypotheses |
| `ae_funDim_residual_eq_skipless_add_of_equality` | the same, with the equality condition "at generic parameters" | SAME as a conditional at almost every `θ`, for any measure |

### `Residual/LearnedGainUnderEquality.lean` (3 theorems)

| theorem | paper sentence | verdict |
|---|---|---|
| `ae_funDimLearned_eq_residual_add_of_equality` | S Theorem A.12 (iii): "Under the equality condition for the networks with learned skips, with identity skips […], the functional dimension of the network with learned skips exceeds that of the residual network by `L (d_model² − dim G)`" | SAME as a conditional, when used with `g = dim G`; the equality condition for learned skips is written as `fd = P + L d² − (L + 1) g − s`, the count of the paper's proof; "for almost every `p` and almost every `θ`" for the comparison of the two generic values |
| `sq_sub_half_mul_pred` | "These are `L d_model (d_model + 1)/2` […] for `ε > 0`" | SAME (the number `d² − d(d−1)/2 = d(d+1)/2`, in `ℕ`) |
| `sq_sub_half_mul_pred_add_one` | "and `L (d_model (d_model + 1)/2 − 1)` […] for `ε = 0`" | SAME (the number `d² − (d(d−1)/2 + 1) = d(d+1)/2 − 1`; for `d = 0` both sides are cut off at `0`) |

The second difference of A.12 (iii) is the file above; the last sentence of A.12 (iii) is
`Dimension/UpperBoundHomogeneousRMSNormZero.lean` (twenty-first audit, part A).

### `Residual/LearnedSkipsConformal.lean` (1 definition, 6 theorems)

| name | paper sentence | verdict |
|---|---|---|
| `skipProdFwd` | "Let `Π_ℓ = A_1 ⋯ A_ℓ`, with `Π_0 = I`" (before Theorem A.12) | SAME |
| `skipProdFwd_zero`, `skipProdFwd_succ` | the same (`Π_0 = I`, `Π_ℓ = Π_{ℓ−1} A_ℓ`) | SAME |
| `cob_skipProdFwd_E` | A.12 (ii): "the residual network with the embedding `E`" | SAME (the embedding is unchanged, for any `K`) |
| `eval_learned_eq_residual_rmsNorm_zero_fwd` | A.12 (ii), for `ε = 0`: "If every `Π_ℓ` lies in `G`, write `Π_ℓ = c_ℓ P_ℓ` with `c_ℓ > 0` and `P_ℓ` orthogonal […]. Then the network computes the same function as the residual network with the embedding `E`, the reads `P_{ℓ−1} W_read^ℓ`, the writes `W_write^ℓ Π_ℓ⁻¹` and the readout `P_L D`" | SAME (the hypothesis on the `A_ℓ`, equivalent to the paper's on the `Π_ℓ`); at every input, also where a normalized row vanishes (Lean's `N_0(0) = 0`) |
| `eval_learned_eq_residual_rmsNorm_fwd` | the same sentence for `ε > 0` ("where `c_ℓ = 1` if `ε > 0`") | SAME; stated for any `ε` |
| `eval_learned_eq_residual_rmsNorm_zero` | Theorem 3.2 (i), (ii): "the residual network with the embedding `E Λ_0`, the reads `Λ_{ℓ−1}⁻¹ W_read^ℓ`, the writes `W_write^ℓ Λ_ℓ` and the readout `D`"; "(ii) Under pre-RMSNorm, the same holds when every `A_ℓ` is orthogonal" | LEAN STRONGER than Theorem 3.2 (ii), first sentence, for `ε = 0`: skips `c_ℓ Q_ℓ` with `c_ℓ > 0`, with the reads `(Λ^Q_{ℓ−1})⁻¹ W_read^ℓ`. Not a sentence of the paper in this form; it is A.12 (ii) with the backward products |

Not stated (the header and the index say so): the converse of A.12 (ii).

### `OneBlock/LearnedSkipRMSZeroBound.lean` (1 definition, 2 theorems)

| name | paper sentence | verdict |
|---|---|---|
| `learnedZeroDomain` | "With `ε = 0`, it also excludes the inputs at which a state that is normalized vanishes" | SAME, for one block with the learned skip `R 0` |
| `funDimSkipsOn_add_le_learned_rmsNorm_zero` | proof of B.1 (iii), "The case `ε = 0`": "For the learned skip, `η^rot` and `K_B` are flat, which gives at least `d_model (d_model − 1) + 2` […] dimensions besides `K_B`" | SAME for a full skip, at one `(θ, A)`, with "generic" replaced by "`E` of rank `d ≥ 1`, `A` invertible"; an analytic block. `sorry` at `38eefee`, proved at `c63b4e1` |
| `funDimSkipsOn_learned_le_funDimOn_residual_add_rmsNorm_zero` | B.1 (iii): "For `ε = 0` it exceeds that of the residual network with `ε = 0` by at most `d_model (d_model + 1)/2 − 1`" | PART: a full skip and an analytic block (not the upper triangular skip, not ReLU, ReLU², ReGLU, not the equality for them); at one `(θ, A)` and the same `θ`, under the conditions of the value for the residual network and `A` invertible. Proved from the first at `38eefee` |

---------------------------------------------------------------------------------------------------

## What the authors of the papers should know

Nothing false, vacuous, drifted or misdescribed was found. In order of weight:

1. **A skipless network with `ε = 0` in which some blocks, not all, are positively homogeneous
   does not attain the bound of Theorem 4.2 either.** The remark after Theorem A.17 and the last
   sentence of Theorem A.12 (iii) say it "for `ε = 0` and positively homogeneous blocks", and
   Lemma A.3 is stated for a skipless network whose blocks are positively homogeneous. For
   `ε = 0` the argument needs only that the block that reads `h_ℓ` is positively homogeneous
   token by token: `N_0(h_ℓ G) G⁻¹` is a positive multiple of `N_0(h_ℓ)` for each token, block
   `ℓ + 1` passes the multiple on, and the next normalization removes it. So in a skipless
   pre-RMSNorm network with `ε = 0` whose blocks are attention blocks and ReLU, ReLU² or ReGLU
   blocks (inside the Scope of Section 2), every hidden state that a ReLU-type block reads
   carries all of `GL(d_model)`. Computed: with a general invertible `G` there the output changes
   by less than `10⁻⁵⁵`; the rank is below the bound of Theorem A.17 (ii) by `d(d+1)/2 − 1` for
   each such hidden state (2 for `d = 2` in 12 cases, 5 for `d = 3` in 3 cases, an attention block
   and a ReLU or ReLU² block in either order; with a ReGLU block the same number in the cases
   where the batch reached it). With identity skips the same networks attain their bound in 26 of
   27 computed cases. If heads and ReLU units stand side by side in one block, the block is not
   positively homogeneous and the bound without skips was attained (5 of 6 cases).
2. **For tanh, GELU and SwiGLU blocks the "at most" of Theorem B.1 (iii) for `ε = 0` is an
   equality in every computed case.** One block, `d = 2` and `3`, widths from 1 to `2d`, a full
   learned skip: the rank with the learned skip minus the rank of the residual network at the
   same weights is `d(d+1)/2 − 1` in all 144 cases (2 and 5), and each of the two ranks is the
   value that the count of symmetries gives. The theorem claims the equality for ReLU, ReLU² and
   ReGLU blocks only.
3. **A step that the proof of B.1 (iii), "The case `ε = 0`", does not write.** "For the learned
   skip, `η^rot` and `K_B` are flat, which gives at least `d_model (d_model − 1) + 2` […]
   dimensions besides `K_B`": the count needs that these directions are independent. For
   `ε > 0` the proof gives the reason ("`η_E = E X_a` and `η_D = −Y D` determine `X_a` and `Y`").
   For `ε = 0` the scaling of `h_1` moves neither `E` nor `D`; it is seen at `A`, in
   `A (Y + c I) − (X_a + c_0 I) A`, and this determines `Y + c I` because `A` is invertible (or at
   the write, if it is not zero). Lean asks "`E` of rank `d`" and "`A` invertible" and not the
   rank of `D`.
4. **Parts (iii) of Theorems A.17 and A.12 are arithmetic.** In Lean they follow from the
   equations alone, for any numbers in the place of `dim G` and `s`; the "in addition" of
   A.17 (iii) is not used. Their content is which networks satisfy the equality conditions. For
   `ε = 0` I found in the library no network for which both equalities of A.17 (iii) are stated,
   and for learned skips the equality is stated for one block and `ε > 0` only.
5. **Theorem A.12 (ii), first two sentences, holds as written for `ε = 0`,** with the indices of
   the paper (checked in Lean's definitions and by a computation at depth 2 and 3); with Lean's
   convention `N_0(0) = 0` it holds also at inputs with a zero row.
6. **The bounds of Theorem A.17 (ii) for `ε = 0` hold with the conditions of Lemma A.18 for
   every kind of network of this file, and with identity skips without any width.** In the 105
   computed cases without a ReLU-type block (attention, gated, attention with tanh, GELU or gated
   blocks; `d = 2, 3`; one or two blocks) the rank is equal to the bound, with and without skips.

## Corrections for `STATEMENTS.md`

Line numbers at `2b9d829`.

1. **Row 819** (`Dimension/UpperBoundAttention.lean`): "and the bound with `CO(d)` and `s` for
   attention blocks is not stated" is no longer true. Write: "the bound with `CO(d)` and `s` is in
   the row of `Dimension/UpperBoundSymmetriesRMSNormZero.lean`".
2. **Row 840** (`Dimension/UpperBoundSymmetriesRMSNormZero.lean`), last sentence "Not stated:
   part (iii) for `ε = 0`": part (iii) is the next row, for any `χ` and any number `g`. Write
   what is missing: "For `ε = 0` the library has no pair of equalities to use part (iii) with."
3. **Row 840**, to add: "The skipless bounds for attention with ReLU, ReLU² or ReGLU blocks are
   not attained when a block is a ReLU-type block alone: the hidden state that it reads has all
   of `GL(d)` (computed: `d(d+1)/2 − 1` below for each such state). The library has the stronger
   bound for networks of positively homogeneous blocks only
   (`Dimension/UpperBoundHomogeneousRMSNormZero.lean`)." The row says this of the `_co` forms and
   not of these.
4. **Row 909** (`OneBlock/LearnedSkipRMSZeroBound.lean`), last sentence: write "Not stated here"
   and point to rows 910 to 912 for the forms at almost every parameter, the ReLU-type blocks
   and the upper triangular skip. Still not stated anywhere, by the heads of those rows: the
   equality for ReLU, ReLU² and ReGLU blocks.
5. **Rows 838, 845, 846, 895, 819** (the files of the sixteen helpers): the helpers are in the
   third cell and not described. Add one clause to each row, for instance for row 845: "helpers,
   public for the twins for `ε = 0`: the directions inside the heads, resp. of the rescalings of
   the values, span a space of directions of symmetries inside the blocks of the stated dimension
   in which read `0` gives write `0`; `E`, the query and value matrices and the value columns at
   almost every `θ`". Row 838 should also name the two public definitions `sumInlLin_ibl` and
   `sumInrLin_ibl`, which are in no row.
6. **Row 842** (`Residual/LearnedGainUnderEquality.lean`): after the two identities add "(for
   `d = 0` the second holds with both sides cut off at `0`)". Optional.
7. **Row 843** (`Residual/LearnedSkipsConformal.lean`): "Every `Π_ℓ` lies in `CO(d)` if and only
   if every `A_ℓ` does" could be marked as a remark that is not a Lean statement (one direction is
   in the private helpers of the file).
8. **Lines 238 to 253** ("Not yet compared by such a reader …"): the six files of this audit can
   be taken off the list, with this report as the source; `OneBlock/LearnedSkipRMSZeroBound.lean`
   was read with one proof open at `38eefee` and proved at `c63b4e1` with the same statements.

## What I could not check

- The proofs. I read statements, definitions and docstrings; that the theorems are proved is
  what the compiler and the three standard axioms say.
- The files written after I started (`OneBlock/LearnedSkipRMSZeroBoundKinds.lean`,
  `OneBlock/LearnedSkipRMSZeroRescaleBound.lean`, `OneBlock/LearnedSkipTriangularRMSZeroBound.lean`):
  not read. Where I say what their rows contain, it is from the heads of the rows.
- "Part (ii) for `ε = 0` is stated for every kind of network of the paper" (row 840): I checked
  it against the heads of the rows it names, not against the statements of those files.
- Sharpness. That a bound is attained is known here only where a certified rank on a batch is
  equal to it, at the computed weights: `d = 2` and `3`, one or two blocks, `P` up to 90. Where
  a rank is below a bound (the networks with ReLU-type blocks) it is a lower bound of the
  functional dimension and nothing more; for point 1 of the list for the authors the upper side
  is the argument by hand and the computed invariance of the output, not a Lean statement.
- The causal mask in the computations: all computed attention networks have no mask. One
  compiled instance has the causal mask.
- ReLU, ReLU² and ReGLU blocks with a learned skip (the equality of B.1 (iii)): outside these
  statements. I ran them for comparison (`z22learn_relu.out`): for `d = 3` and for ReLU² the
  difference is `d(d+1)/2 − 1` in all 96 cases; for ReLU and ReGLU with `d = 2` twelve of 48
  cases have a batch that does not reach the value, and for the one I looked at again the value
  is reached with inputs spread over the directions (check 2, last point). I draw no conclusion
  from them.
- The converse of Theorem A.12 (ii) and part (i) of that theorem: not in these files.
