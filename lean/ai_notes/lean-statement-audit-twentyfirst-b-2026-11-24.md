STATUS: complete

# Twenty-first audit of Lean statements against the papers, part B: the last sentence of D Proposition 4.6 and S Proposition 4.5 as one statement under the equality condition (24 November 2026)

Reader: an independent reader who did not write the statements. Brief:
`/home/claude/proj_up/audit21b_brief_2026-11-24.md`. I audited statements and definitions, not
proofs. I changed no repository file, ran no `lake build`, made no commit and no push. My files are
in `/home/claude/audit21b/`.

Library: `/home/claude/lw/lean` (branch `lean-wip`). The branch moved nine times while I read.

- **Commit at the start: `8084e308484f1c412eb3057f031e43ac14acdbdd` (21:01:25 UTC).** I read every
  statement of the four files at this commit.
- Then `0ac8d09` (21:05:07), `3c25980668de6d78ee7aba340308343b7460958b` (21:05:23), `4f40bcb`
  (21:07:32), `f154a51` (21:11:29), `8ce3a42` (21:11:42),
  `f21e8ed6c3a43a001c4ead9ce8b8c2b6ddd89b17` (21:15:05), `1da5f51` (21:18:46), `7a913fb`
  (21:20:34) and **`f223d48c9248ef01d62304660d88096ad2850c89` (21:21:39), the head at the end
  (21:31 UTC).** My scratch files were compiled a last time at this commit, at 21:30 UTC.
- **Did a file that I read change? No.** `git diff --stat 8084e30 f223d48` is empty for the four
  files of the brief, the three files of the equivalences, the seven files of the statements at
  one parameter, `Network/`, `Symmetry/ChangeOfBasis.lean`, `Symmetry/AttentionHeads.lean`,
  `Dimension/RescaleAction.lean`, `Dimension/Functional.lean`, `Dimension/Space.lean` and
  `Generic/Params.lean`. In `Symmetry/InsideBlocksSum.lean`, of which I read the definitions
  `Params.sumFst` and `Params.sumSnd`, five helpers lost the word `private`; the definitions did
  not change. The four index rows are the same text at `8084e30` (lines 867 to 870) and at
  `f223d48` (lines 876 to 879). Line numbers of `STATEMENTS.md` below are those of `f223d48`; the
  index was edited at almost every commit, so each correction also quotes the words to look for.
- **Files with `sorry`** (`git grep -cw sorry`, in `lean/SkipsLean`). At `8084e30`:
  `Dimension/UpperBoundHomogeneousRMSNormZero.lean` (9). At `3c25980`: none. At `4f40bcb`:
  `OneBlock/ResidualRMSZeroReGLU.lean` (3), `OneBlock/ResidualRMSZeroReGLUGeneric.lean` (2). At
  `f154a51` and `8ce3a42`: `OneBlock/ResidualRMSZeroReGLU.lean` (3). At `f21e8ed`: that file (3)
  and `Symmetry/InsideBlocksRMSNormZero.lean` (1). At `1da5f51`, `7a913fb` and `f223d48`: none.
  None of these files is in my brief. The four files of the brief have no `sorry` at any of these
  commits, and none of the 20 theorems rests on a `sorry` (no `sorryAx` among their axioms).
- The four files have 20 public theorems (2, 4, 10, 4, as the brief says) and 16 private helpers.
- All 20 depend on `propext`, `Classical.choice`, `Quot.sound` only (by compiling, `Ax.lean`,
  `Ax.out`).

Papers, as text: the dimension paper ("D", `<scratchpad>/dim.txt`; Proposition 4.6 at lines 359
to 362, its proof at lines 912 to 937) and the skips paper ("S", `<scratchpad>/skips.txt`;
Proposition 4.5 at lines 465 to 468, its proof at lines 1671 to 1696).

How I checked.

- "By reading": the four files in full; the statements and docstrings of the 20 statements at one
  parameter and of the 20 equivalences that they were built from; the definitions `Arch`, `Params`,
  `hidden`, `eval`, `Arch.mlp`, `Arch.gated`, `Arch.attention`, `Arch.sum`, `Arch.attentionMlp`,
  `Arch.attentionGated`, `Params.cob`, `Params.rescale`, `Params.headsQK`, `Params.headsVO`,
  `Params.sumFst`, `Params.sumSnd`, `Params.sumOf`, `funDim`, `jacobianRank`, the norm and the
  Borel σ-algebra of the parameters; the passages of the papers named in the brief, the Setup and
  Scope of both papers, D Theorem 5.2 and Corollary 5.3, S Theorems 4.6 and 4.7 and Corollary 4.9;
  the reports of the sixteenth reader and of the seventeenth reader (part B).
- "By a script": `compare.py` (on the source text; output `compare.out`), with the pairing of the
  names in `map.txt`.
- "By compiling": scratch files of mine, compiled with `lake env lean` from `/home/claude/lp/lean`
  (read only). `/home/claude/lw/lean` has no compiled files for the four modules, so I could not
  compile from it. For the 14 files named above the sources of `lp` and `lw` were the same (`cmp`)
  and each compiled file of `lp` was newer than its source. Files: `Ax.lean` (axioms), `Sig.lean`
  (the elaborated signatures of the 60 names), `Cmp.lean` (a Lean program that compares the
  elaborated statements), `Chk.lean` (checks 1, 2 and 6), `NonVac.lean`, `NonVac4.lean` and
  `NonVac4b.lean` (check 5). All compile without error, contain no `sorry`, and give no warning that a declaration uses
  `sorry` (`*.out`).
- "By hand": a short argument of my own, written where it is used.

**Short answer. Nothing false, nothing vacuous and no drift was found.** Each of the 20 statements
is the last sentence of D Proposition 4.6 / S Proposition 4.5 joined with the direction "equality
condition ⟹ locally identifiable" of the first sentence, for almost every parameter and every
Haar measure, with the paper's count of symmetries in the hypothesis and the symmetries of the
statement at one parameter in the conclusion. Together the 20 cover every kind of network of the
two propositions. Three things are described more broadly than they are stated or are out of date:

1. The index row of `Dimension/LocalIdentifiabilityUnderEquality.lean` (line 876) still says "Not
   stated in this form: blocks with symmetries inside (SwiGLU, GeGLU, attention), residual
   networks". The three rows below it state them.
2. The docstrings of the 14 statements for residual networks and for skipless networks with two
   kinds of block, and the index rows at lines 878 and 879, name "Proposition 4.6 of the dimension
   paper". D has only skipless networks of one kind of block; these 14 are S Proposition 4.5 alone.
3. For skipless networks that have both attention blocks and MLP or gated blocks
   (`Dimension/IdentifiableUnderEqualityTransformer.lean`), neither the library nor the papers
   prove the hypothesis `hfd`. The four statements are true and not empty (I compiled them for
   networks of these architectures that have blocks of one kind only), but for networks with both
   kinds of block they are conditional statements, as S Proposition 4.5 is.

---------------------------------------------------------------------------------------------------

## Part 1: the drift checks

### Check 1. The paper's sentence

**Verdict: yes. Each statement is the paper's sentence "Every symmetry that is needed is then close
to the identity", read as the proof of the proposition gives it.** (By reading; the meaning of the
neighborhoods by compiling, `Chk.lean`.)

The paper (D, the same words in S): "A network satisfies the equality condition if and only if, at
generic parameters, it is locally identifiable up to its symmetries. Every symmetry that is needed
is then close to the identity." The proof: "If `r = P − k`, then `O` is open in `Z`, since the two
have the same dimension. So every `θ′` close to `θ` with `F_θ′ = F_θ` is the image of `θ` under a
symmetry close to the identity." There `O` is the image of a neighborhood of the identity of the
group under `g ↦ g · θ`, and any smaller neighborhood of the identity gives a smaller open `O`. So
the sentence is: for every neighborhood of the identity there is a neighborhood of `θ` in which
every `θ′` with the same function is the image of `θ` under a symmetry of the first neighborhood.

One of the 20 (the others have the same form):

```
theorem ae_exists_cob_rescale_of_eval_eq_skipless_gated_of_ae_funDim
    [Nonempty d] (hσ : AnalyticOnNhd ℝ σ Set.univ)
    (μ : Measure (Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ))
    (hfd : ∀ᵐ θ ∂μ, funDim (Arch.gated σ id hid) 0 θ
          + ((L + 1) * Fintype.card d ^ 2 + ∑ ℓ, Fintype.card (hid ℓ))
        = Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)) :
    ∀ᵐ θ ∂μ,
      ∀ V ∈ 𝓝 (1 : Fin (L + 1) → Matrix d d ℝ), ∀ W ∈ 𝓝 (1 : ∀ ℓ, hid ℓ → ℝ), ∃ U ∈ 𝓝 θ,
        ∀ θ' ∈ U,
        (∀ x : Matrix T dIn ℝ, eval (Arch.gated σ id hid) 0 θ' x
          = eval (Arch.gated σ id hid) 0 θ x) →
          ∃ (G : Fin (L + 1) → GL d ℝ) (c : ∀ ℓ, hid ℓ → ℝ),
            (fun ℓ => (G ℓ : Matrix d d ℝ)) ∈ V ∧ c ∈ W ∧ (∀ ℓ i, 0 < c ℓ i) ∧
            θ' = (θ.rescale c).cob G G
```

- **The order of the quantifiers** is, in all 20: almost every `θ`; for all neighborhoods of the
  identity (`V`, and `W`, `Wc` where the blocks have symmetries inside); there is a neighborhood
  `U` of `θ`; for all `θ' ∈ U`. So `U` may depend on `θ` and on the neighborhoods of the identity,
  and it does not depend on `θ'`: it is chosen before `θ'`. This is the order of the paper's proof.
- **"The same function" is equality at every input:** `∀ x : Matrix T dIn ℝ, eval A S θ' x = eval A
  S θ x`, with `x` over all of `ℝ^{T × d_in}`, and `S = 0` (skipless) or `S = 1` (residual) the
  stream matrices. Not equality on a batch or on an open set.
- **The image is of `θ`:** `θ' = θ.cob G G`, `θ' = (θ.rescale c).cob G G`, `θ' = ((θ.headsQK
  K).headsVO K').cob G G`, and for two kinds of block `θ' = (Params.sumOf ((θ.sumFst.headsQK
  K).headsVO K') (θ.sumSnd.rescale c)).cob G G`. In none is `θ'` on the right side.
- **The neighborhoods are neighborhoods of the identity.** Compiled (`Chk.lean`): `(1 : Fin (L +
  1) → Matrix d d ℝ) ℓ i j` is `1` if `i = j` and `0` otherwise (the tuple of identity matrices,
  not matrices of ones); `(1 : ∀ ℓ, hid ℓ → ℝ) ℓ i = 1`; `(1 : ∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)`
  is the identity matrix in every head; `θ.cob 1 1 = θ`. One neighborhood `W` serves both changes
  of basis `K` and `K'` of the heads, which loses nothing.
- **"Close to the identity" in numbers.** Compiled (`Chk.lean`), from
  `ae_exists_cob_of_eval_eq_skipless_of_ae_funDim` with `V` a ball: at almost every `θ`, for every
  `r > 0` there is a neighborhood `U` of `θ` such that every `θ' ∈ U` with the same function is
  `θ.cob G G` with `|G_ℓ(i, j) − δ_ij| < r` for all `ℓ, i, j`.
- **The statement contains the direction "⟹" of the first sentence.** With the neighborhoods taken
  to be everything, the conclusion is the right side of the equivalence. Compiled for two kinds
  (`Chk.lean`): for skipless gated blocks and for residual attention blocks under pre-RMSNorm,
  under the other hypotheses, `hfd` holds if and only if the conclusion holds (from the new
  statement and the equivalence of the `IdentifiableIff` file). So the conclusion is not weaker
  than local identifiability and not stronger than what the equality condition gives.

### Check 2. Generic means almost every parameter, for every Haar measure

**Verdict: yes, in the hypothesis and in the conclusion of all 20; every index type has
`Fintype`.** (By a Lean program on the elaborated statements, `Cmp.lean`, `Cmp.out`; the instance
arguments from `Sig.lean`, `Sig.out`; by reading.)

- In all 20 (`Cmp.out`): the hypothesis `hfd` and the conclusion are `Filter.Eventually … (ae μ)`
  for the same `μ`; `μ` is a variable of the statement, `(μ : Measure (Params …))`, with
  `[μ.IsAddHaarMeasure]`; no other hypothesis mentions `funDim` or is an almost-everywhere
  statement. None is "there is a parameter" or "on an open set".
- **Index types.** The weights are `E : Matrix dIn d ℝ`, `read ℓ : Matrix d (A.r ℓ) ℝ`, `write ℓ :
  Matrix (A.w ℓ) d ℝ`, `D : Matrix d dOut ℝ`, `ℓ : Fin L`. All 20 have `[Fintype d] [Fintype dIn]
  [Fintype dOut]` (and `[Fintype T]`, `[DecidableEq d]`); `A.r ℓ` and `A.w ℓ` are finite by the
  fields `fr`, `fw` of `Arch`, and for the named kinds by `[∀ ℓ, Fintype (hid ℓ)]`, `[∀ ℓ, Fintype
  (H ℓ)]`, `[∀ ℓ, Fintype (dh ℓ)]` (with `[∀ ℓ, DecidableEq (dh ℓ)]`), which the statements that
  use them have (`Sig.out`, listed by a script). So the parameter space is finite-dimensional
  (`FiniteDimensional ℝ (Params A dIn dOut)` is found by instance search, compiled in `Chk.lean`),
  a Haar measure on it exists (compiled), and its Haar measures are its Lebesgue measures up to a
  positive factor.
- The 8 statements for gated blocks also have `[Nonempty d]`, as their equivalences have. The
  papers have `d ≥ 2`.

### Check 3. The hypothesis `hfd`

**Verdict: in all 20, `hfd` is the left side of the equivalence, and the number subtracted is the
paper's count; the other hypotheses are those of the equivalence and no more.** (By the script on
the source text, `compare.out`: 20 of 20; by the Lean program on the elaborated statements,
`Cmp.out`: 20 of 20; the counts by reading.)

- **`hfd` against the left side of the equivalence:** the same in all 20, in the source text and
  after elaboration (the two unify with no definition unfolded other than abbreviations such as
  `Arch.gated`).
- **`hfd` at one `θ` against the hypothesis `hfd` of the statement at one parameter:** the same in
  all 20, likewise.
- **The other hypotheses against those of the equivalence:** the same hypotheses in the same order
  in 19; in `ae_exists_cob_of_eval_eq_skipless_rmsNorm_of_ae_funDim` (written by hand) `{ε : ℝ}`
  stands after `(A : Arch T d L)` and in the equivalence before it, with the same types. No
  hypothesis is added and none is dropped.
- **The count**, `hfd : ∀ᵐ θ ∂μ, funDim A S θ + k = Module.finrank ℝ (Params A dIn dOut)`, that is
  `fd = P − k` at almost every `θ` (D Definition 4.4, S Definition 4.3, with the bounds of D
  Theorem 4.3 and S Theorem 4.2):

  | Network | `S` | `k` in Lean | The paper's count |
  |---|---|---|---|
  | skipless, analytic blocks without symmetries inside | `0` | `(L + 1) * card d ^ 2` | `(L+1) d²`, `s = 0` (tanh, GELU) |
  | the same under pre-RMSNorm, `ε > 0` | `0` | `(L + 1) * (card d * (card d - 1) / 2)` | `(L+1) d(d−1)/2` |
  | skipless gated | `0` | `(L + 1) * card d ^ 2 + ∑ ℓ, card (hid ℓ)` | `s = d_hidden` per block (SwiGLU, GeGLU) |
  | skipless attention | `0` | `(L + 1) * card d ^ 2 + 2 * ∑ ℓ, card (H ℓ) * card (dh ℓ) ^ 2` | `s = 2 H d_h²` per block |
  | skipless attention with MLP blocks | `0` | as for attention | `s` of the attention blocks (`s = 0` for tanh, GELU) |
  | skipless attention with gated blocks | `0` | `(L + 1) * card d ^ 2 + (2 * ∑ … + ∑ ℓ, card (hid ℓ))` | both |
  | residual, each kind | `1` | `card d ^ 2 + s`, under pre-RMSNorm `card d * (card d - 1) / 2 + s` | `dim 𝒢 + s`: one change of basis |

  Under pre-RMSNorm each kind has its twin with `card d * (card d - 1) / 2` in place of `card d ^
  2` and `hε : 0 < ε`. The numbers are natural numbers; `d (d −
  1)` is even, so the division is exact. The statements are for `ε > 0` only, as the propositions
  are (D: "Proposition 4.6 is stated for `ε > 0`"; S defines RMSNorm with `ε > 0`).
- **The hypotheses beside `hfd`,** as in the equivalences: `d_in ≥ d` in all 20; for skipless
  networks the widths (`hw`: writes of at least `d` rows; `hhid`: at least `d` hidden units; `hdh`,
  `hH`: `d_h ≤ d ≤ H d_h`; `hW`: `H d_h + d_hidden ≥ d` in every block, with `hdh`); for residual
  networks no width, only `d_h ≤ d` for heads; real-analytic `f_ℓ`, activation or gate. Every
  network of the Scope of D and of S satisfies them. Lean does not ask `d_out ≥ d`, `d ≥ 2` or two
  tokens.

### Check 4. The conclusion

**Verdict: in all 20, the conclusion at one `θ` is the conclusion of the statement at one parameter
of the same name: the same symmetries, the same neighborhoods.** (By the script on the source text,
20 of 20; by the Lean program on the elaborated statements, 20 of 20; the symmetries by reading.)

| Kind | The symmetries in the conclusion |
|---|---|
| skipless, without normalization | `G : Fin (L + 1) → GL d ℝ`, `(fun ℓ => (G ℓ : Matrix d d ℝ)) ∈ V`, `θ.cob G G`: one change of basis per hidden state |
| skipless, pre-RMSNorm | `Q : Fin (L + 1) → GL d ℝ` with `∀ ℓ, (Q ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ`, in `V`, `θ.cob Q Q` |
| residual | one matrix: `G : GL d ℝ`, `(G : Matrix d d ℝ) ∈ V` with `V ∈ 𝓝 (1 : Matrix d d ℝ)`, `θ.cob (fun _ => G) (fun _ => G)`; orthogonal under pre-RMSNorm |
| gated | `c : ∀ ℓ, hid ℓ → ℝ`, `c ∈ W`, `∀ ℓ i, 0 < c ℓ i`, `θ.rescale c`: the value column of every hidden unit divided by `c`, its write row multiplied by `c` |
| attention | `K K' : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ`, both in `W`, `(θ.headsQK K).headsVO K'`: `(W_Q, W_K) ↦ (W_Q K, W_K K^{−⊤})`, `(W_V, W_O) ↦ (W_V K', K'^{−1} W_O)` in every head |
| attention with MLP blocks | the changes of basis of the heads on the attention part, the MLP part unchanged: `Params.sumOf ((θ.sumFst.headsQK K).headsVO K') θ.sumSnd` |
| attention with gated blocks | in addition `c ∈ Wc`, `0 < c`, on the gated part: `θ.sumSnd.rescale c` |

These are the continuous symmetries of the papers (D Appendix B; S Section 4.1), and one matrix
for residual networks is S Theorem A.5 (iii) and Corollary 4.9 ("The matrix `G` is the same at all
hidden states").

### Check 5. Not vacuous

**Verdict: not vacuous, for each of the four files.** (By compiling, `NonVac.lean`: 12 examples;
`NonVac4.lean`: 2 examples; `NonVac4b.lean`: 2 examples.) In each example the conclusion is written
out in full and proved from the new statement and a library theorem that gives `hfd`; no
hypothesis on the functional dimension is left.

| File | Network | The library theorem that gives `hfd` |
|---|---|---|
| `Dimension/LocalIdentifiabilityUnderEquality.lean` | skipless tanh blocks, any depth, without normalization | `ae_funDim_tanh_skipless` (D Theorem 5.2 (i)) |
| the same | skipless GELU blocks, any depth, pre-RMSNorm | `ae_funDim_gelu_skipless_rmsNorm` (D Theorem 5.2 (ii)) |
| `Dimension/IdentifiableUnderEquality.lean` | skipless SwiGLU blocks, any depth, without normalization | `ae_funDim_swiglu_skipless` (D Theorem 5.2 (iii)) |
| the same | skipless SwiGLU blocks, any depth, pre-RMSNorm | `ae_funDim_swiglu_skipless_rmsNorm` |
| the same | one skipless attention block, without normalization | `ae_funDim_attention_oneBlock` (D Theorem 5.1) |
| `Residual/IdentifiableUnderEquality.lean` | residual tanh blocks, any depth | `ae_funDim_tanh_residual` (S Theorem 4.7) |
| the same | residual GELU blocks, pre-RMSNorm | `ae_funDim_gelu_residual_rmsNorm` |
| the same | residual SwiGLU blocks | `ae_funDim_swiglu_residual` |
| the same | residual attention blocks, any depth | `ae_funDim_attention_residual` |
| the same | residual attention blocks, pre-RMSNorm | `ae_funDim_attention_residual_rmsNorm` |
| the same | residual attention and tanh blocks, any depth | `ae_funDim_attention_tanh_residual` |
| the same | residual attention and SwiGLU blocks, pre-RMSNorm | `ae_funDim_attention_swiglu_residual_rmsNorm` |
| `Dimension/IdentifiableUnderEqualityTransformer.lean` | one skipless attention block and no hidden unit, in `Arch.attentionMlp` with tanh | `ae_funDim_attention_oneBlock`, carried to the sum by a lemma of mine |
| the same | the same, in `Arch.attentionGated` with SiLU | the same |
| the same | skipless tanh blocks and no head, any depth, pre-RMSNorm, in `Arch.attentionMlp` | `ae_funDim_tanh_skipless_rmsNorm` (D Theorem 5.2 (i)), carried to the sum by a lemma of mine |
| the same | skipless SwiGLU blocks and no head, any depth, pre-RMSNorm, in `Arch.attentionGated` | `ae_funDim_swiglu_skipless_rmsNorm` (D Theorem 5.2 (iii)), likewise |

- The hypotheses of the examples are those of the library theorems: `d_in, d_out ≥ d ≥ 2`, a token
  (two tokens `t₁ ≠ t₂` with `sees t₂ t₂`, `sees t₂ t₁` and `d_h ≥ 1` for attention), and the
  widths of the new statement.
- The generic statements for analytic blocks apply to tanh and GELU blocks through `rfl` (for
  `A.χ = id` or `A.χ = rmsNorm ε`) and `analyticOnNhd_f_mlp`. The first example has the
  hypotheses and the conclusion of the library's `ae_exists_cob_of_eval_eq_tanh_skipless` (D
  Corollary 5.3 for tanh; compared as text): the new statement with `ae_funDim_tanh_skipless`
  gives the corollary in one line, which is how the paper derives it ("With Proposition 4.6,
  Theorem 5.2 gives local identifiability").
- **`Dimension/IdentifiableUnderEqualityTransformer.lean`: no library theorem gives `hfd`.** The
  library has upper bounds for skipless networks of `Arch.attentionMlp` and `Arch.attentionGated`
  and no value. The papers have none either: S proves the equality condition for residual
  networks and recalls it for skipless networks of one kind of block (D Theorems 5.1 and 5.2). So
  I took networks of these architectures that have blocks of one kind only, and proved in my
  scratch files that the functional dimension, the number of parameters and "almost every
  parameter" agree with those of the network of that one kind (about 90 lines for each of the two
  parts of a sum: a linear equivalence of the parameter spaces, the functions agree, the chain
  rule, a Haar measure carried by the equivalence).
  - One block and no hidden unit (`hid ℓ` empty), which is one attention block:
    `ae_funDim_attention_oneBlock` gives `hfd`, and the conclusion follows from
    `ae_exists_cob_heads_of_eval_eq_skipless_attentionMlp_of_ae_funDim` and from
    `…_attentionGated_of_ae_funDim` (`NonVac4.lean`).
  - No head (`H ℓ` empty), any depth, under pre-RMSNorm, which is a network of tanh blocks or of
    SwiGLU blocks: `ae_funDim_tanh_skipless_rmsNorm` and `ae_funDim_swiglu_skipless_rmsNorm` give
    `hfd`, and the conclusion follows from `…_attentionMlp_rmsNorm_of_ae_funDim` and from
    `…_attentionGated_rmsNorm_of_ae_funDim` (`NonVac4b.lean`).

  So each of the four statements of this file has a compiled instance. I did not compile a case
  with both kinds of block present, because no theorem gives `hfd` there.

### Check 6. The finite symmetries

**Verdict: the conclusion needs no permutation and no sign flip, and the statements are the paper's
last sentence in full.** (By reading and by hand.)

- The paper's symmetries with the permutations and the sign flips form "a Lie group of dimension
  `k` with finitely many components" (the proof of the propositions). A small neighborhood of the
  identity of such a group lies in the component of the identity, which is the family of the
  continuous symmetries: invertible `G_ℓ` near `I` (orthogonal ones near `I` under pre-RMSNorm),
  rescalings near `1`, hence positive, and invertible `K`, `K'` near `I`. A permutation of hidden
  units or heads other than the identity, and a sign flip, are not close to the identity. So "a
  symmetry close to the identity" is a continuous one, and Lean's conclusion says exactly this.
  The clause `∀ ℓ i, 0 < c ℓ i` follows from `c ∈ W` for small `W`; it does no harm.
- The paper's proof gives it in the same way: it takes the image `O` of a neighborhood of the
  identity of the group of "the changes of basis […], the rescalings and the changes of basis
  inside the heads", without the finite symmetries, and brings these in only for the converse.
- **In full, for the last sentence and the direction "⟹".** The converse direction "locally
  identifiable ⟹ equality condition" is not in these 20 statements and is not meant to be; it is
  in the `IdentifiableIff` files, with the continuous symmetries and, in the files `…Finite.lean`,
  with all the symmetries (the seventeenth reader, part B).

### Check 7. The index rows

**Verdict: every public theorem is in a row and in `checks/Axioms.lean`; the rows are true of the
statements except one clause of the first row, which is out of date; every kind of network of the
two propositions has a statement.** (By a script on the index and on `checks/Axioms.lean`; by
reading.)

- Each of the 20 names stands once between backquotes in `STATEMENTS.md` (rows at lines 876 to
  879: 2, 4, 10, 4 names) and once in `checks/Axioms.lean` (`#print axioms Skips.…`, lines 1593 to
  1612). The status "proved" is right: no `sorry` in the four files, and the three
  standard axioms (compiled by me).
- **Row at line 876** (`Dimension/LocalIdentifiabilityUnderEquality.lean`). True of the two
  statements, except its last clause: "Not stated in this form: blocks with symmetries inside
  (SwiGLU, GeGLU, attention), residual networks; their statements at one parameter are in the rows
  of Proposition 4.6 / 4.5". The rows at lines 877 to 879 state them in this form. The header of
  the file says "Not stated here: […]", which is true of that file, and does not name the three
  files that state them.
- **Row at line 877** (`Dimension/IdentifiableUnderEquality.lean`). True. "Rescalings of the hidden
  units" is, exactly, rescalings of the values of the hidden units by positive factors. The row
  does not name the hypotheses (`d_in ≥ d`, at least `d` hidden units, `d_h ≤ d ≤ H d_h`).
- **Row at line 878** (`Residual/IdentifiableUnderEquality.lean`). True of the ten statements. It
  says "D Proposition 4.6 and S Proposition 4.5 […] for residual networks": D has no residual
  networks, so this is S Proposition 4.5 alone. The row does not name the hypotheses (`d_in ≥ d`,
  `d_h ≤ d`, no width).
- **Row at line 879** (`Dimension/IdentifiableUnderEqualityTransformer.lean`). True of the four
  statements. It names D Proposition 4.6, whose Scope has "all blocks of a network are of one
  kind": this is S Proposition 4.5 alone. It does not say that the hypothesis is not known to
  hold for these networks when both kinds of block are present (Check 5).
- **"Each statement is the form at almost every parameter of the statement at one parameter of the
  same name"** (rows at lines 877 to 879): true of the conclusion and of `hfd` (Checks 3 and 4).
  The rank conditions of the statement at one parameter (`E` and the writes of rank `d`, the query
  and value matrices of rank `d_h`, no value column zero) are replaced by the widths, under which
  they hold at almost every parameter.
- **Which kinds of network of the two propositions have no such statement: none.**

  | Network | Without normalization | Pre-RMSNorm, `ε > 0` |
  |---|---|---|
  | D, S: skipless tanh, GELU | `ae_exists_cob_of_eval_eq_skipless_of_ae_funDim` | `…_skipless_rmsNorm_of_ae_funDim` |
  | D, S: skipless SwiGLU, GeGLU | `ae_exists_cob_rescale_of_eval_eq_skipless_gated_of_ae_funDim` | `…_gated_rmsNorm_of_ae_funDim` |
  | D, S: skipless attention | `ae_exists_cob_heads_of_eval_eq_skipless_attention_of_ae_funDim` | `…_attention_rmsNorm_of_ae_funDim` |
  | S: skipless attention with tanh or GELU blocks | `ae_exists_cob_heads_of_eval_eq_skipless_attentionMlp_of_ae_funDim` | `…_attentionMlp_rmsNorm_of_ae_funDim` |
  | S: skipless attention with SwiGLU or GeGLU blocks | `ae_exists_cob_heads_of_eval_eq_skipless_attentionGated_of_ae_funDim` | `…_attentionGated_rmsNorm_of_ae_funDim` |
  | S: residual tanh, GELU | `ae_exists_cob_of_eval_eq_residual_of_ae_funDim` | `…_residual_rmsNorm_of_ae_funDim` |
  | S: residual SwiGLU, GeGLU | `ae_exists_cob_rescale_of_eval_eq_residual_gated_of_ae_funDim` | `…_gated_rmsNorm_of_ae_funDim` |
  | S: residual attention | `ae_exists_cob_heads_of_eval_eq_residual_attention_of_ae_funDim` | `…_attention_rmsNorm_of_ae_funDim` |
  | S: residual attention with tanh or GELU blocks | `ae_exists_cob_heads_of_eval_eq_residual_attentionMlp_of_ae_funDim` | `…_attentionMlp_rmsNorm_of_ae_funDim` |
  | S: residual attention with SwiGLU or GeGLU blocks | `ae_exists_cob_heads_of_eval_eq_residual_attentionGated_of_ae_funDim` | `…_attentionGated_rmsNorm_of_ae_funDim` |

  Tanh and GELU blocks have no statement by name; they are instances of the statements for
  analytic blocks (compiled, Check 5). Outside the two propositions, and without such a statement:
  pre-RMSNorm with `ε = 0`, LayerNorm, learned skips, ReLU, ReLU² and ReGLU blocks.

---------------------------------------------------------------------------------------------------

## Part 2: the statements

"One parameter" is the statement `exists_…_of_eval_eq_…` whose conclusion was used, "equivalence"
the statement whose hypotheses and left side were used. The paper sentence is in every row: "Every
symmetry that is needed is then close to the identity", with the direction "⟹" of "A network
satisfies the equality condition if and only if, at generic parameters, it is locally identifiable
up to its symmetries" (D Proposition 4.6 for rows 1 to 6; S Proposition 4.5 for all rows). Ten of
the 20 are without normalization, and ten are their twins under pre-RMSNorm with `ε > 0` (the
names with `_rmsNorm`).

| # | Lean statement (`ae_…_of_ae_funDim`) | One parameter | Equivalence | Verdict |
|---|---|---|---|---|
| 1 | `ae_exists_cob_of_eval_eq_skipless_of_ae_funDim` | `exists_cob_of_eval_eq_skipless` | `ae_funDim_skipless_iff_ae_locally_cob` | LEAN STRONGER (note 1) |
| 2 | `ae_exists_cob_of_eval_eq_skipless_rmsNorm_of_ae_funDim` | `exists_cob_of_eval_eq_skipless_rmsNorm` | `ae_funDim_skipless_iff_ae_locally_cob_rmsNorm` | LEAN STRONGER (note 1) |
| 3 | `ae_exists_cob_rescale_of_eval_eq_skipless_gated_of_ae_funDim` | `exists_cob_rescale_of_eval_eq_skipless_gated` | `ae_funDim_gated_skipless_iff_ae_locally_cob_rescale` | LEAN STRONGER (note 1) |
| 4 | `ae_exists_cob_rescale_of_eval_eq_skipless_gated_rmsNorm_of_ae_funDim` | `…_skipless_gated_rmsNorm` | `…_rescale_rmsNorm` | LEAN STRONGER (note 1) |
| 5 | `ae_exists_cob_heads_of_eval_eq_skipless_attention_of_ae_funDim` | `exists_cob_heads_of_eval_eq_skipless_attention` | `ae_funDim_attention_skipless_iff_ae_locally_cob_heads` | LEAN STRONGER (note 1) |
| 6 | `ae_exists_cob_heads_of_eval_eq_skipless_attention_rmsNorm_of_ae_funDim` | `…_skipless_attention_rmsNorm` | `…_cob_heads_rmsNorm` | LEAN STRONGER (note 1) |
| 7 | `ae_exists_cob_heads_of_eval_eq_residual_attention_of_ae_funDim` | `exists_cob_heads_of_eval_eq_residual_attention` | `ae_funDim_attention_residual_iff_ae_locally_cob_heads` | LEAN STRONGER (notes 1, 2) |
| 8 | `ae_exists_cob_of_eval_eq_residual_of_ae_funDim` | `exists_cob_of_eval_eq_residual` | `ae_funDim_residual_iff_ae_locally_cob` | LEAN STRONGER (notes 1, 2) |
| 9 | `ae_exists_cob_of_eval_eq_residual_rmsNorm_of_ae_funDim` | `exists_cob_of_eval_eq_residual_rmsNorm` | `ae_funDim_residual_iff_ae_locally_cob_rmsNorm` | LEAN STRONGER (notes 1, 2) |
| 10 | `ae_exists_cob_rescale_of_eval_eq_residual_gated_of_ae_funDim` | `exists_cob_rescale_of_eval_eq_residual_gated` | `ae_funDim_gated_residual_iff_ae_locally_cob_rescale` | LEAN STRONGER (notes 1, 2) |
| 11 | `ae_exists_cob_rescale_of_eval_eq_residual_gated_rmsNorm_of_ae_funDim` | `…_residual_gated_rmsNorm` | `…_rescale_rmsNorm` | LEAN STRONGER (notes 1, 2) |
| 12 | `ae_exists_cob_heads_of_eval_eq_residual_attention_rmsNorm_of_ae_funDim` | `…_residual_attention_rmsNorm` | `ae_funDim_attention_residual_iff_ae_locally_cob_heads_rmsNorm` | LEAN STRONGER (notes 1, 2) |
| 13 | `ae_exists_cob_heads_of_eval_eq_residual_attentionMlp_of_ae_funDim` | `exists_cob_heads_of_eval_eq_residual_attentionMlp` | `ae_funDim_attentionMlp_residual_iff_ae_locally_cob_heads` | LEAN STRONGER (notes 1, 2) |
| 14 | `ae_exists_cob_heads_of_eval_eq_residual_attentionMlp_rmsNorm_of_ae_funDim` | `…_residual_attentionMlp_rmsNorm` | `…_cob_heads_rmsNorm` | LEAN STRONGER (notes 1, 2) |
| 15 | `ae_exists_cob_heads_of_eval_eq_residual_attentionGated_of_ae_funDim` | `exists_cob_heads_of_eval_eq_residual_attentionGated` | `ae_funDim_attentionGated_residual_iff_ae_locally_cob_heads_rescale` | LEAN STRONGER (notes 1, 2) |
| 16 | `ae_exists_cob_heads_of_eval_eq_residual_attentionGated_rmsNorm_of_ae_funDim` | `…_residual_attentionGated_rmsNorm` | `…_rescale_rmsNorm` | LEAN STRONGER (notes 1, 2) |
| 17 | `ae_exists_cob_heads_of_eval_eq_skipless_attentionMlp_of_ae_funDim` | `exists_cob_heads_of_eval_eq_skipless_attentionMlp` | `ae_funDim_attentionMlp_skipless_iff_ae_locally_cob_heads` | LEAN STRONGER (notes 1, 2, 3) |
| 18 | `ae_exists_cob_heads_of_eval_eq_skipless_attentionMlp_rmsNorm_of_ae_funDim` | `…_skipless_attentionMlp_rmsNorm` | `…_cob_heads_rmsNorm` | LEAN STRONGER (notes 1, 2, 3) |
| 19 | `ae_exists_cob_heads_of_eval_eq_skipless_attentionGated_of_ae_funDim` | `exists_cob_heads_of_eval_eq_skipless_attentionGated` | `ae_funDim_attentionGated_skipless_iff_ae_locally_cob_heads_rescale` | LEAN STRONGER (notes 1, 2, 3) |
| 20 | `ae_exists_cob_heads_of_eval_eq_skipless_attentionGated_rmsNorm_of_ae_funDim` | `…_skipless_attentionGated_rmsNorm` | `…_rescale_rmsNorm` | LEAN STRONGER (notes 1, 2, 3) |

Files: rows 1, 2 `Dimension/LocalIdentifiabilityUnderEquality.lean`; rows 3 to 6
`Dimension/IdentifiableUnderEquality.lean`; rows 7 to 16 `Residual/IdentifiableUnderEquality.lean`;
rows 17 to 20 `Dimension/IdentifiableUnderEqualityTransformer.lean`.

Notes.

1. **Why "LEAN STRONGER" and not "SAME".** The sentence is the paper's: the same hypothesis (the
   equality condition, with the paper's count), the same conclusion (Checks 1, 3, 4, 6). Lean
   states it under fewer hypotheses than the Scope of the papers: `d_in ≥ d` and, for skipless
   networks, the widths, but no `d_out ≥ d`, no `d ≥ 2` (the gated statements ask that `d` is not
   empty), no token; for residual networks no width; any real-analytic activation, gate or map
   `f_ℓ` in place of the named ones. Every network of the Scope satisfies Lean's hypotheses, so
   nothing of the paper's sentence is lost. Each statement is one direction of the proposition
   with its last sentence; the other direction is in the `IdentifiableIff` files.
2. **S Proposition 4.5 alone.** D Proposition 4.6 is for skipless networks whose blocks are all of
   one kind. The docstrings of these 14 statements say "Proposition 4.6 of the dimension paper and
   4.5 of the skips paper".
3. **A hypothesis that is not proved for these networks.** For skipless networks with both
   attention blocks and MLP or gated blocks, `hfd` is a theorem neither of the library nor of the
   papers. The statements are the paper's conditional sentence. Not empty: Check 5.

---------------------------------------------------------------------------------------------------

## What the authors should know

Nothing is false, nothing is vacuous, nothing has drifted. In order of weight:

1. **The last sentence of D Proposition 4.6 and of S Proposition 4.5 is now one Lean statement
   under the equality condition, for every kind of network of the two propositions** (ten kinds,
   each without normalization and under pre-RMSNorm with `ε > 0`). This closes the item of the
   seventeenth reader (part B: "What is not covered", item 1, in its Check 3, and item 5 of its
   list; the index calls it item (c)). Hypothesis and
   conclusion were compared with the equivalences and with the statements at one parameter on the
   source text and on the elaborated statements: 20 of 20 agree.
2. **The index row at line 876 is out of date in its last clause** ("Not stated in this form:
   blocks with symmetries inside […], residual networks"), and so are the passages that say that
   the last sentence is proved "at one parameter" only (lines 646 and 851 to 853). Corrections
   below.
3. **Fourteen docstrings and two index rows name D Proposition 4.6 for networks that D does not
   have** (residual networks; skipless networks with two kinds of block). They are S Proposition
   4.5.
4. **For skipless networks with both attention blocks and MLP or gated blocks the hypothesis is
   not proved.** The library has upper bounds and no value of the functional dimension there, and S
   treats the equality condition of these networks as a hypothesis. The four statements of
   `Dimension/IdentifiableUnderEqualityTransformer.lean` say what follows if it holds. The same is
   true, inside `Dimension/IdentifiableUnderEquality.lean`, of skipless attention blocks at depth
   greater than one or under pre-RMSNorm: the library has the value for one block without
   normalization.
5. **The statements turn the theorems on the functional dimension into the corollaries in one
   line.** With `ae_funDim_tanh_skipless` the first statement gives the library's D Corollary 5.3 for
   tanh, with the same hypotheses and the same conclusion; with the residual theorems the statements of
   `Residual/IdentifiableUnderEquality.lean` give S Corollary 4.9 (compiled for seven kinds). This
   is how the papers derive the corollaries.
6. **The conclusion is equivalent to the hypothesis.** Under the other hypotheses, "at almost
   every parameter the symmetries can be taken in any neighborhoods of the identity" holds if and
   only if the equality condition holds (compiled for two kinds from the new statement and the
   equivalence). The library does not state this as an equivalence; it follows in a few lines.
7. **No permutation and no sign flip is needed** for the last sentence: a symmetry close to the
   identity is a continuous one. The statements are the sentence in full.
8. **Lean asks less than the Scope** (no `d_out ≥ d`, no `d ≥ 2`, no token; no width for residual
   networks; any real-analytic activation or gate).
9. The three files written by the script each carry private copies of the helpers "the rank
   conditions hold at almost every parameter" of the `IdentifiableIff` files (16 private lemmas in
   all). This does not touch the statements.
10. The branch moved nine times while I read; no file that I read changed in a statement or a
    definition.

## Corrections for `STATEMENTS.md` (line numbers of `f223d48`)

1. Line 876 (the row of `Dimension/LocalIdentifiabilityUnderEquality.lean`). Replace "Not stated in
   this form: blocks with symmetries inside (SwiGLU, GeGLU, attention), residual networks; their
   statements at one parameter are in the rows of Proposition 4.6 / 4.5" by "The same for blocks
   with symmetries inside, for residual networks and for networks with two kinds of block: the
   next three rows".
2. Lines 878 and 879 (the rows of `Residual/IdentifiableUnderEquality.lean` and of
   `Dimension/IdentifiableUnderEqualityTransformer.lean`). Replace "D Proposition 4.6 and S
   Proposition 4.5, last sentence" by "S Proposition 4.5, last sentence" (D Proposition 4.6 is for
   skipless networks of one kind of block).
3. Line 879. Add: "for skipless networks with both kinds of block neither the library nor the
   papers prove the hypothesis; the twenty-first reader (part B) compiled the four statements for
   networks with blocks of one kind only".
4. Lines 877 to 879. After "(the left side of the equivalences of the `IdentifiableIff` files)"
   add "under the hypotheses of the equivalence of the same kind" and name them: line 877 `d_in ≥
   d`, at least `d` hidden units, `d_h ≤ d ≤ H d_h`; line 878 `d_in ≥ d`, `d_h ≤ d`, any widths;
   line 879 `d_in ≥ d`, `d_h ≤ d`, `H d_h + d_hidden ≥ d` in every block. In line 877 replace
   "rescalings of the hidden units" by "rescalings of the values of the hidden units by positive
   factors".
5. Lines 222 to 238 ("Not yet compared by such a reader"). Take out
   `Dimension/LocalIdentifiabilityUnderEquality.lean`, `Dimension/IdentifiableUnderEquality.lean`,
   `Residual/IdentifiableUnderEquality.lean` and
   `Dimension/IdentifiableUnderEqualityTransformer.lean`, and add: "A twenty-first reader (part B,
   24 November) compared these four files (20 theorems) with the papers: nothing false, vacuous or
   drifted; each is the last sentence of D Proposition 4.6 / S Proposition 4.5 with the direction
   from the equality condition, under fewer hypotheses than the Scope; hypothesis and conclusion
   agree with the equivalences and with the statements at one parameter in all 20. Report:
   `lean-statement-audit-twentyfirst-b-2026-11-24.md`."
6. Lines 645 to 646. Replace "its last sentence is proved at one parameter" by "its last sentence
   is proved at one parameter and, as one statement under the equality condition, at almost every
   parameter (`Dimension/LocalIdentifiabilityUnderEquality.lean`,
   `Dimension/IdentifiableUnderEquality.lean`)".
7. Lines 851 to 853 (the rows of the three files `…Finite.lean`). After "(the rows of
   `Dimension/LocalIdentifiability.lean` and its siblings, at one parameter)" add "; as one
   statement under the equality condition: the rows of the four files `…UnderEquality…`". The same
   pointer fits the rows at lines 840, 841 and 845, after "the proved direction gives them close
   to it" and after "not asked to be close to the identity".
8. Lines 711 to 716 (the note on S Proposition 4.5). After "the equivalence with all the
   symmetries: the rows of […]" add "the last sentence under the equality condition: the rows of
   `Residual/IdentifiableUnderEquality.lean` and
   `Dimension/IdentifiableUnderEqualityTransformer.lean`".

Not in the index, in the sources: the header of `Dimension/LocalIdentifiabilityUnderEquality.lean`
("Not stated here: […]") could name the three files that state the rest; the docstrings of the 14
statements of note 2 could say "Proposition 4.5 of the skips paper".

## What I could not check

- **The proofs.** I read them (each is `filter_upwards` with the lemmas "the rank conditions hold
  at almost every parameter" and `hfd`, then the statement at one parameter), but the brief is the
  statements. That they are accepted by Lean with the three standard axioms I checked by compiling.
- **A case of `Dimension/IdentifiableUnderEqualityTransformer.lean` with both kinds of block
  present:** no theorem gives the hypothesis (Check 5). That the hypothesis can hold there I did
  not check in any way; I ran no numerical computation.
- **Skipless attention blocks at depth greater than one, and under pre-RMSNorm** (two statements of
  `Dimension/IdentifiableUnderEquality.lean`): compiled for one block without normalization only,
  for the same reason.
- **The statements at one parameter and the equivalences against the papers.** I compared the 20
  new statements with them and read them, but did not audit them again. The index says that
  earlier readers did (a ninth reader, part C, for `Dimension/LocalIdentifiability.lean` and its
  first siblings; the sixteenth and seventeenth readers for the equivalences); I did not check
  which reader compared each of the seven files of the statements at one parameter.
- **A build from `/home/claude/lw/lean`.** It has no compiled files for the four modules. I
  compiled against the build of `/home/claude/lp/lean`, whose sources I compared with `lw` for the
  14 files that carry the statements; I did not compare every file of the two trees at the end.
- **Whether `checks/Axioms.lean` itself compiles.** I checked that the 20 names are in it, and
  printed their axioms in a file of my own.
- The papers as PDF: I read the text files only.
