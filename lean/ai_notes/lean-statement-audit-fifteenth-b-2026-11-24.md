STATUS: complete

# Fifteenth audit, part B, of Lean statements against the papers (24 November 2026)

Reader: an independent reader who did not write the statements. Brief:
`/home/claude/proj_up/audit15b_brief_2026-11-24.md`, with one note from the coordinator during the
work (the branch moved; read the two files on the converse at the new commit; ask whether
`ContDiffOn` on an arbitrary set makes a statement false or empty). I audited statements and
definitions, not proofs. I changed no repository file, ran no `lake build`, made no commit and no
push. My files are in `/home/claude/audit15b/`.

Library: `/home/claude/lw/lean` (branch `lean-wip`).

- **Commit that I read: `679de0975904173c441a8a53f706bf799488a3a1` (16:13:41 UTC).** I began at
  16:06 UTC at `2fc98cc` (16:04:49 UTC, the commit of the brief) and ended at 16:31 UTC.
- The branch moved several times while I worked: `2fc98cc` → `679de09` (16:13:41) → `cbee1f1`
  (16:18:54) → `e33be5b` (16:24:24) → `591d9e4` (16:28:08, the last that I saw). Of the eleven
  files of the brief, **nine are the same at all these commits** (`git diff --stat`: no line).
  The two others, `Generic/LevelSetImages.lean` and `Dimension/IdentifiableConverse.lean`,
  changed once, between `2fc98cc` and `679de09`, and are the same from `679de09` to `591d9e4`.
  `Network/Sum.lean` and `Network/Transformer.lean` did not change either.
- **What changed in the two files** (`git diff 2fc98cc 679de09`): the three `sorry` are gone (the
  three statements are proved), and the hypothesis `(hΩ : ∀ i, IsOpen (Ω i))` was removed from all
  three statements; the docstrings say "subsets" where they said "open subsets"; two statements
  got `omit [DecidableEq d] in`. Nothing else in a statement changed. I first read the statements
  with `hΩ` and then compared the statements as they stand at `679de09` (Check 5).
- **Files with `sorry`.** At `2fc98cc`: `Generic/LevelSetImages.lean` (1) and
  `Dimension/IdentifiableConverse.lean` (2), and no other file. At `679de09`: none of the eleven
  files; two files outside the brief, `Generic/Cayley.lean` (4) and
  `Dimension/IdentifiableConverseCob.lean` (4). At `591d9e4`: `Dimension/IdentifiableIff.lean`,
  `Generic/GroupDimension.lean`, `Residual/IdentifiableIff.lean`, `Symmetry/CobGroup.lean`,
  `Symmetry/OnlyOrthogonalRows.lean`, all outside the brief (`git grep -l -w sorry`). I did not
  read these files.
- The eleven files have 79 public names (6 definitions, 73 theorems) and 168 private helpers. No
  line with `axiom`, `opaque`, `admit`, `native_decide` or `unsafe` in them (by `grep`).
- All 73 theorems depend on `propext`, `Classical.choice`, `Quot.sound` only (by compiling,
  `Chk1.out`, at `679de09`). All 73 stand in `checks/Axioms.lean`, and all 79 names stand in their
  index rows, written out or by a stated abbreviation ("each of the eight also with `_rmsNorm`").

Papers, as text: the skips paper ("S", `skips.txt`), the dimension paper ("D", `dim.txt`), the
absorb paper ("A", `absorb.txt`). Line numbers of `STATEMENTS.md` are those of `591d9e4`; the
rows of the eleven files have the same text at `679de09`, `e33be5b` and `591d9e4` (by `diff`), and
only their line numbers move as rows are added above them. Each correction quotes the words to
change.

How I checked.

- "By reading": the statements and docstrings of the eleven files (every public statement in
  full), the definitions they use (`Arch`, `Params`, `hidden`, `eval`, `Arch.mlp`, `Arch.gated`,
  `Arch.attention`, `attnWeights`, `Arch.sum`, `Arch.attentionMlp`, `Arch.attentionGated`,
  `Params.sumFst`, `Params.sumSnd`, `Params.sumOf`, `Params.headsQK`, `Params.headsVO`,
  `headDirQK`, `headDirVO`, `Params.cob`, `Params.rescale`, `Params.smallWrites`,
  `smallWritesLimit`, `smallWritesLimitNorm`, `funDim`, `jacobianRank`, `evalBatch`, `UnitsRigid`,
  `GatedUnitsRescale`, the six structures `SmallWritesGeneric…`, `SomeBlockNonzero`, `DefinedAt`,
  `rmsNorm`), the statements of `ae_ne_skipless_rmsNorm` and
  `ae_not_dense_eq_skipless_rmsNorm_zero`, and the paper passages that the brief names.
- "By hand": a short argument of my own, written in the note.
- "By compiling": in `/home/claude/audit15b/`, with `lean` 4.36.0 through `LEAN_PATH`, without
  `lake`, against a copy of the compiled library of `/home/claude/lp/lean` taken at 16:09 UTC
  (`lp` then at `2fc98cc`, its sources equal to those of `lw` by `diff -rq`). Into my copy I
  compiled the two changed files from the sources of `679de09` (6 and 4 seconds, no error, no
  warning, no `sorry`). Then five scratch files of my own: `Chk1.lean` (axioms), `Chk2.lean`
  (general checks), `Chk3.lean` (concrete networks), `Chk4.lean` and `Chk5.lean` (the converse).
  All compile without error (`Chk*.out`).
- "By a computation": my own script `transformer_check.py` (torch 2.14, double precision,
  Jacobians in the parameters by reverse-mode differentiation, rank from the singular values with
  the gap printed), output `transformer_check.out`. I did not use the coordinator's scripts.

**Short answer. Nothing false, vacuous or drifted was found.** Every "generic" of the 50 public
and 11 private `ae_` statements is `∀ᵐ θ ∂μ` for every additive Haar measure. Lemma A.27 for
transformers is written as two statements, and together they are "for almost every `θ`, for all
small `τ ≠ 0`" (compiled). Every statement uses the library's `funDim`, and `funDimBlocks` is the
same notion for the network with `E = D = I` and only the reads and writes as parameters. No
hypothesis excludes a block without heads or a block without hidden units, and the value has the
paper's `s` then (compiled on a network of one attention block and one tanh block: `fd = 24`
without normalization and `27` under pre-RMSNorm; the computation gives the same ranks). The
three statements on the converse are true as they stand, are proved at `679de09`, and removing
the openness of `Ω i` makes nothing false or empty. Three small things about how the transformer
is modelled are worth knowing (list at the end), and two sentences of the index are out of date.

---------------------------------------------------------------------------------------------------

## Part 1: the drift checks

### Check 1. Generic means almost every parameter, for every Haar measure

**Verdict: yes, in all 61 `ae_` statements of the eleven files (50 public, 11 private). None is
"there is a point" or "on an open set".** (By reading; the shape of all 61 by a script,
`ae_shapes.out`; the combined form of Lemma A.27 by compiling.)

Each has the shape `(μ : Measure (Params …)) [μ.IsAddHaarMeasure] … : ∀ᵐ θ ∂μ, …` (for the blocks
alone `(μ : Measure (BlockParams …)) [μ.IsAddHaarMeasure] … : ∀ᵐ β ∂μ, …`), with `μ` a variable of
the statement. One line of each kind:

| Statement | The Lean text after the hypotheses |
|---|---|
| `ae_smallWritesGeneric_attentionMlp` | `∀ᵐ θ ∂μ, SmallWritesGenericAttention θ.sumFst ∧ SmallWritesGeneric θ.sumSnd` |
| `ae_funDim_attentionMlp_residual` | `∀ᵐ θ ∂μ, funDim (Arch.attentionMlp sees σ id H dh hid) 1 θ + (Fintype.card d ^ 2 + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2) = Module.finrank ℝ (Params …)` |
| `ae_funDim_attentionGated_residual_rmsNorm` | `∀ᵐ θ ∂μ, funDim (Arch.attentionGated sees σ (rmsNorm ε) H dh hid) 1 θ + (Fintype.card d * (Fintype.card d - 1) / 2 + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2 + ∑ ℓ, Fintype.card (hid ℓ))) = Module.finrank ℝ (Params …)` |
| `ae_funDim_attentionMlp_residual_ge_add` | `∀ᵐ θ ∂μ, funDim (…) 0 θ + L * Fintype.card d ^ 2 ≤ funDim (…) 1 θ` |
| `ae_funDim_attentionMlp_residual_eq_add_of_skipless` | `∀ᵐ θ ∂μ, funDim (…) 0 θ + ((L + 1) * Fintype.card d ^ 2 + 2 * ∑ ℓ, …) = Module.finrank ℝ (Params …) → funDim (…) 1 θ = funDim (…) 0 θ + L * Fintype.card d ^ 2` |
| `ae_exists_cob_heads_of_eval_eq_attentionMlp_residual` | `∀ᵐ θ ∂μ, ∀ V ∈ 𝓝 (1 : Matrix d d ℝ), ∀ W ∈ 𝓝 (1 : ∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ), ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U, (∀ x, eval (…) 1 θ' x = eval (…) 1 θ x) → ∃ (G : GL d ℝ) (K K' : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ), … ∧ θ' = (Params.sumOf ((θ.sumFst.headsQK K).headsVO K') θ.sumSnd).cob (fun _ => G) (fun _ => G)` |
| `ae_funDimBlocks_attention_residual` | `∀ᵐ β ∂μ, funDimBlocks (Arch.attention sees id H dh) 1 β + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2 = Module.finrank ℝ (BlockParams …)` |
| `ae_ne_skipless_rmsNorm_attention` | `∀ᵐ θ ∂μ, ∀ (L' : ℕ) (d' : Type) [Fintype d'] (A' : Arch T d' L') (ε' : ℝ), 0 < ε' → A'.χ = rmsNorm ε' → (∀ ℓ, LocallyLipschitz (A'.f ℓ)) → ∀ θ' : Params A' dIn dOut, ∃ X : Matrix T dIn ℝ, eval (Arch.attention sees (rmsNorm ε) H dh) 1 θ X ≠ eval A' 0 θ' X` |
| `ae_finrank_le_funDim_add_of_ae_locally_mem_iUnion_image` | hypothesis `(hloc : ∀ᵐ θ ∂μ, ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U, (∀ x, eval A S θ' x = eval A S θ x) → ∃ i, ∃ m ∈ Ω i, Φ θ i m = θ')`, conclusion `∀ᵐ θ ∂μ, Module.finrank ℝ (Params A dIn dOut) ≤ funDim A S θ + Module.finrank ℝ M` |

- **One statement has an almost-everywhere hypothesis,** the last of the table, and it is meant
  to: "if at generic parameters it is locally identifiable, then at generic parameters the lower
  bound". The other 60 have none.
- In the four conditional statements of `Residual/ExactGainTransformer.lean` the implication
  stands inside `∀ᵐ θ ∂μ`: the hypothesis is at the parameter `θ`.
- **The order in Lemma A.27.** The four depth files have no single statement "for almost every
  `θ`, for all small `τ ≠ 0`" (the files for one kind of block have one,
  `ae_eventually_funDim_smallWrites_…`). They have two statements each:
  `eventually_funDim_smallWrites_attentionMlp … (hθa : SmallWritesGenericAttention θ.sumFst)
  (hθm : SmallWritesGeneric θ.sumSnd) : ∀ᶠ τ in 𝓝[≠] (0 : ℝ), funDim … 1 (θ.smallWrites τ) + (…) =
  Module.finrank ℝ (Params …)` at one `θ` with written conditions, and
  `ae_smallWritesGeneric_attentionMlp`, which gives the conditions at almost every `θ`. Together
  they are the paper's form: I compiled `∀ᵐ θ ∂μ, ∀ᶠ τ in 𝓝[≠] (0 : ℝ), funDim … 1 (θ.smallWrites
  τ) + … = …` from the two, for MLP blocks without normalization and for gated blocks under
  pre-RMSNorm (`Chk2.lean` (b), (b'), two lines each). `∀ᶠ τ in 𝓝[≠] 0, p τ` is `∃ δ > 0, ∀ τ,
  |τ| < δ → τ ≠ 0 → p τ` (`Chk2.lean` (a)): the `δ` may depend on `θ`, as in the paper ("For
  generic parameters `θ` … For all small `τ ≠ 0`").
- The only "there is a `θ`" are inside proofs (one `θ₀` with the conditions and one small `τ`,
  then `ae_funDim_ge` and the upper bound), as in the paper's proof of Theorem 4.7.
- That the hypotheses of the final statements can all hold at once, with `Measure.addHaar` for
  `μ`: `Chk3.lean` instantiates Theorem 4.7 (both normalizations), the gain (both), Corollary 4.9,
  Corollary 4.10 (ii) and absorb Theorem 4.3 on concrete networks.

### Check 2. `funDim` is the library's functional dimension; `funDimBlocks`

**Verdict: yes, in every statement; `funDimBlocks` is the same notion for the network without `E`
and `D`.** (By reading; the definition by compiling.)

- Every statement of the four depth files, of `ExactGainTransformer.lean`, of
  `LocalIdentifiabilityTransformer.lean` (the hypothesis `hfd`) and of
  `IdentifiableConverse.lean` uses `funDim A S θ` of `Dimension/Functional.lean`:
  `sSup {r : ℕ | ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), r = jacobianRank A S X θ}`, the largest
  rank over all finite batches of real `T × d_in` inputs. `S = 1` is the residual network and
  `S = 0` the skipless one. None uses `jacobianRank` on one batch in its place.
- The networks here are differentiable in `θ` at every input (real-analytic activations, the
  attention map, `id` or `rmsNorm ε` with `ε > 0`), so `funDim` is the paper's `fd` with nothing
  dropped (the reason is in the sixth and fourteenth reports; I did not compile it again for the
  sums. `analyticOnNhd_f_sum` gives the analyticity of the block of a sum).
- **`funDimBlocks`.** The Lean text: `abbrev BlockParams (A : Arch T d L) : Type _ := Params A
  PEmpty.{1} PEmpty.{1}`; `def BlockParams.toParams … where E := 1; read := β.read; write :=
  β.write; D := 1`; `def evalBlocks A S β x := eval A S β.toParams x`; `jacobianRankBlocks A S X β
  := Module.finrank ℝ (LinearMap.range (fderiv ℝ (fun β' : BlockParams A => fun i : Fin n =>
  evalBlocks A S β' (X i)) β).toLinearMap)`; `funDimBlocks A S β := sSup {r : ℕ | ∃ (n : ℕ) (X :
  Fin n → Matrix T d ℝ), r = jacobianRankBlocks A S X β}`. So the parameters are the reads and the
  writes alone (the embedding and the readout are matrices with no row and no column), the
  derivative is taken in them only, and the function is that of the network with `E = D = I` and
  `d_in = d_out = d`. I compiled: `jacobianRankBlocks A S X β` is the rank of the derivative in
  `β'` of `evalBatch A S X β'.toParams` (by `rfl`); without normalization `evalBlocks … 1 β x` is
  the last hidden state and `h_0 = x` (`Chk2.lean` (f)). The number of parameters is
  `∑_ℓ d r_ℓ + ∑_ℓ w_ℓ d` (`finrank_blockParams`). This is "Without an embedding and a readout, so
  that `h_0 = x ∈ ℝ^{T × d_model}` and `y = h_L`" of S Corollary 4.10 (ii).

### Check 3. No extra hypotheses in main-text statements

**Verdict: no hypothesis that the paper's statement, Setup or Scope does not have or imply, with
two remarks (a dummy type for a block without heads; the two-token hypothesis in a network
without any head).** (By reading.)

**Theorem 4.7 and Corollary 4.9 for transformers** (the same list for
`ae_funDim_attentionMlp_residual`, `ae_funDim_attentionGated_residual`, their `_rmsNorm` forms,
and the `ae_exists_cob_heads_of_eval_eq_…` statements):

| Lean hypothesis | In the paper? |
|---|---|
| `hσ : ∀ z, HasDerivAt σ (σ' z) z`, `hσa : AnalyticOnNhd ℝ σ Set.univ` | "Let the blocks be analytic". The eight named forms (tanh, GELU, SwiGLU, GeGLU; each with and without RMSNorm) do not have them |
| `hU : UnitsRigid σ σ' dIn dOut (Σ ℓ, hid ℓ)` (under RMSNorm `… d d …`), or `GatedUnitsRescale` | The conclusion of Lemma B.3 for the hidden units of all blocks together, as a hypothesis of the general form. The named forms for tanh, GELU, SwiGLU and GeGLU do not have it (`tanh_unitsRigid`, `gelu_unitsRigid`, `silu_gatedUnitsRescale`, `gelu_gatedUnitsRescale`) |
| `[μ.IsAddHaarMeasure]` | "generic" |
| `hd : 2 ≤ card d`, `hdIn : card d ≤ card dIn`, `hdOut : card d ≤ card dOut` | Scope: "`d_in, d_out ≥ d_model ≥ 2`" |
| `hdh : ∀ ℓ, card (dh ℓ) ≤ card d` | Scope: heads "of total width `H d_h = d_model`" implies it; Lemma A.27: "heads of width at most `d_model`" |
| `hdh0 : ∀ ℓ, 0 < card (dh ℓ)` | A head has a positive width. Remark 1 below |
| `(t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁)` | Scope: attention blocks "act on sequences of at least two tokens"; Lemma A.27: "causal or not". Both masks of the paper have such a pair. Remark 2 below |
| `hε : 0 < ε` (the `_rmsNorm` forms) | Setup: "RMSNorm with the constant `ε > 0`" |
| the gain only: `hW : ∀ ℓ, card d ≤ card (H ℓ) * card (dh ℓ) + card (hid ℓ)` | Proof of Theorem 4.7: "When every block has width at least `d_model`"; Scope: "Every MLP block has `d_hidden ≥ d_model`", heads of total width `d_model`. Check 4 |

Not asked by Lean, and in the Scope: the same number of heads in all attention blocks, total width
`H d_h = d` exactly, MLP blocks of width at least `d` (for the value; Lemma A.27 says "of any
width"). "All MLP blocks are of one kind" is built in (one `σ`). No biases and all inputs are
built in.

- Remark 1. `hdh0` is asked of every block, also of a block without heads, whose `dh ℓ` is a type
  that nothing uses. So such a block must be given a nonempty `dh ℓ` (the file headers say so:
  "For a block without heads `dh ℓ` is any nonempty type"). This excludes no network.
- Remark 2. The two tokens are asked also when no block has a head. A network of MLP blocks on
  one token, written as a sum with all `H ℓ` empty, is therefore outside these statements; it is
  inside `Residual/DepthMlp.lean` and its twins, written as `Arch.mlp`. The paper asks for two
  tokens only of attention blocks.

**Corollary 4.10 (ii)** (`ae_funDimBlocks_attention_residual_of_width`): `hd : 2 ≤ card d`
(Scope, with `d_in = d_out = d`), `hHn : ∀ ℓ, card (H ℓ) = Hn` and `hHd : ∀ ℓ, card (H ℓ) * card
(dh ℓ) = card d` (Scope: "the same number `H` of heads, of total width `H d_h = d_model`"), the two
tokens (Scope). No other hypothesis. The form `ae_funDimBlocks_attention_residual` has `hdh`,
`hdh0` in place of `hHn`, `hHd`.

**Absorb Theorem 4.3** ("Consider pre-RMSNorm networks, with `ε ≥ 0` and blocks of any kind and
width"):

| Lean hypothesis | In the paper? |
|---|---|
| `hε : 0 < ε`, or `rmsNorm 0` in the statement | "`ε ≥ 0`": one statement for each case |
| `hd`, `hdIn`, `hdOut` | A Scope: "`d_in, d_out ≥ d_model ≥ 2`" |
| attention: `hhead : ∃ ℓ, Nonempty (H ℓ) ∧ Nonempty (dh ℓ)`, `(t s : T) (hts : sees t s)` | Not written in the paper, and needed: without any head of positive width the residual network is `N(XE)D`, a skipless network without blocks. Every network of the paper has a head of positive width, and every token sees itself under both masks |
| transformers: `hhid : ∃ ℓ, Nonempty (hid ℓ)`, `[Nonempty T]` | A Scope: "Every MLP block has at least `d_model` hidden units" gives it. Note 6 of Part 2 |
| transformers: `hσ : ∀ z, 0 < z → σ z ≠ 0`, `hσL : LocallyLipschitz σ` | "blocks of any kind": tanh, GELU, ReLU, ReLU², SiLU satisfy both. The two named forms (GELU, SwiGLU, `ε > 0`) do not have them |
| on the skipless network: `A'.χ = rmsNorm ε'` with `0 < ε'` (or `rmsNorm 0`), `∀ ℓ, LocallyLipschitz (A'.f ℓ)` (for `ε = 0`: `Continuous`) | "a pre-RMSNorm skipless network"; the blocks of the paper are locally Lipschitz |

### Check 4. The model of a transformer

**Verdict: the statements cover the paper's networks (every block an attention block or an MLP
block, in any order) and more; no hypothesis excludes a block with `H ℓ` empty or with `hid ℓ`
empty; the value has the paper's `s`; the width hypothesis of the gain is the paper's "width at
least `d`" on the paper's blocks.** (By reading; one network by compiling; the values by a
computation.)

- Lean's block `ℓ` of `Arch.attentionMlp sees σ χ H dh hid = (Arch.attention sees χ H dh).sum
  (Arch.mlp σ χ hid)` (by `rfl`, `Chk2.lean` (d)) has the heads `H ℓ` and the hidden units `hid ℓ`
  side by side and adds their outputs. With `hid ℓ` empty it is an attention block, with `H ℓ`
  empty an MLP block (`f_sum_mul_of_isEmpty_right`, `…_left`, in the other reader's files). Lean's
  family is larger than the paper's in four ways: a block may have heads and hidden units at
  once, a block may have neither, the number and the width of the heads may change from block to
  block, and `H d_h` need not be `d`.
- **No hypothesis excludes an empty `H ℓ` or an empty `hid ℓ`.** The conditions on `θ` are
  quantified over the heads and over the hidden units (`∀ ℓ (i : H ℓ), …`, `∀ p : (Σ ℓ, H ℓ), …`,
  `∀ ℓ i, …` over `hid ℓ`), so they say nothing for a block that has none; `UnitsRigid … (Σ ℓ, hid
  ℓ)` is over the units that exist; `hdh`, `hdh0` are about the type `dh ℓ` only (Remark 1 of
  Check 3). Compiled (`Chk3.lean`): the network with two tokens, the causal mask,
  `d = d_in = d_out = 2`, block 0 with 2 heads of width 1 and no hidden unit, block 1 with 2 tanh
  units and no head (`dh 1 = Fin 1`) satisfies every hypothesis of
  `ae_funDim_attention_tanh_residual`, of its `_rmsNorm` form, of the two gain statements, and of
  `ae_exists_cob_heads_of_eval_eq_attention_tanh_residual`.
- **The value has the paper's `s`.** `s = 2 * ∑ ℓ, card (H ℓ) * card (dh ℓ) ^ 2` (plus `∑ ℓ, card
  (hid ℓ)` for gated units): a block without heads adds `0` whatever its `dh ℓ` is, a block without
  hidden units adds `0` to the second sum. This is the paper's `s`: "Each attention head has a
  change of basis between its queries and keys and one between its values and outputs, of
  dimension `d_h²` each", `s = 0` for tanh and GELU, one rescaling per hidden unit for SwiGLU and
  GeGLU (S Appendix A.6). On the network above Lean gives `P = 32`, `fd = 32 − 4 − 4 = 24` without
  normalization and `fd = 32 − 1 − 4 = 27` under pre-RMSNorm (compiled, `fd1`, `fd1r`); the
  computation gives the ranks 24 and 27 (case B2).
- **The gain.** `hW : ∀ ℓ, card d ≤ card (H ℓ) * card (dh ℓ) + card (hid ℓ)`. For an attention
  block this is `H d_h ≥ d` and for an MLP block `d_hidden ≥ d`: the paper's "When every block has
  width at least `d_model`" (S Setup: "the width of the block is `H d_h`"), and with `hdh` the
  hypothesis of S Lemma A.18 ("heads have width `d_h ≤ d_model` and total width `H d_h ≥
  d_model`"). For a block with both kinds of unit Lean asks for the total width, which the paper
  does not state because it has no such block. On the network above `hW` holds, and Lean gives a
  gain of at least `8` and of at least `2` (compiled, `gain1`, `gain1r`); the computation gives
  exactly 8 and 2 (skipless ranks 16 and 25).
- The value statements have no width hypothesis, as Lemma A.27 has none ("of any width"). The
  computation agrees on blocks narrower than `d` (cases A, B, E) and on a block with a head and
  hidden units side by side (case F) and on an empty block (case G).

### Check 5. The converse of Proposition 4.6 / 4.5

I compared the statements as they stand at `679de09`, without `hΩ`.

**(a) Is `finrank_ker_le_of_level_set_subset_iUnion_image` true as stated? Yes.** (By compiling:
it is proved at `679de09`, no `sorry`, standard axioms. By hand: I found no way to refute it, and
give the reason.)

The Lean text: `{F : P → Y} (hF : ContDiff ℝ 1 F) (θ₀ : P) {J : Type*} (g : J → P → Y') (hg : ∀ j,
ContDiff ℝ 1 (g j)) (hker : ∀ j θ, LinearMap.ker (fderiv ℝ (g j) θ).toLinearMap ≤ LinearMap.ker
(fderiv ℝ F θ).toLinearMap) (hrank : ∀ j θ, Module.finrank ℝ (LinearMap.range (fderiv ℝ (g j)
θ).toLinearMap) ≤ Module.finrank ℝ (LinearMap.range (fderiv ℝ F θ₀).toLinearMap)) {ι : Type*}
[Countable ι] (Φ : ι → M → P) (Ω : ι → Set M) (hΦ : ∀ i, ContDiffOn ℝ 1 (Φ i) (Ω i)) (hloc : ∃ U ∈
𝓝 θ₀, ∀ θ ∈ U, (∀ j, g j θ = g j θ₀) → ∃ i, ∃ m ∈ Ω i, Φ i m = θ) : Module.finrank ℝ
(LinearMap.ker (fderiv ℝ F θ₀).toLinearMap) ≤ Module.finrank ℝ M`, with `P`, `Y`, `Y'`, `M`
finite-dimensional real normed spaces.

Why it holds (by hand). Let `r = rank DF(θ₀)` and `p = dim P`. If `J` has an element: `hker` gives
`rank DF(θ) ≤ rank Dg_j(θ)` and `hrank` gives `rank Dg_j(θ) ≤ r`, so `rank DF ≤ r` everywhere; the
rank is lower semicontinuous, so `rank DF = r` near `θ₀`, and there `rank Dg_j = r` and `ker Dg_j =
ker DF` for every `j` at once (the neighbourhood comes from `F` alone, so `J` may be uncountable).
By the constant rank theorem the level set of `F` through `θ₀` is, near `θ₀`, a connected manifold
of dimension `p − r`, on which every `g j` is constant. So it lies in the countably many images
`Φ i (Ω i)`. A map that is differentiable within a set at each of its points does not raise the
Hausdorff dimension of that set (Mathlib, `DifferentiableOn.dimH_image_le`, for any set; I read
its statement), so the union of the images has Hausdorff dimension at most `dim M`, and
`p − r ≤ dim M`. If `J` is empty, `hloc` says that a whole neighbourhood of `θ₀` lies in the
images, so `p ≤ dim M`.

The small examples of the brief:

| Example | What happens |
|---|---|
| `J` empty | No condition on `F` is left; `hloc` covers a neighbourhood of `θ₀`, and the statement gives `dim ker DF(θ₀) ≤ dim P ≤ dim M`. True. Compiled as a consequence (`Chk4.lean` (iv)) |
| `F` constant | `hrank` forces `Dg_j = 0`, so every `g j` is constant, `hloc` covers a neighbourhood, `dim P ≤ dim M`. True (by hand) |
| `F` of full rank (`DF(θ₀)` injective) | The kernel is `0`; nothing to prove |
| a `g j` whose rank drops at `θ₀` | Excluded by the hypotheses: `hker` at `θ₀` gives `rank Dg_j(θ₀) ≥ r`, and `hrank` gives `rank Dg_j(θ) ≤ r` at every `θ`. Without `hrank` the statement is false: `F = g = eδ` on `ℝ²`, `θ₀ = 0`; the level set is the two axes, images of `M = ℝ`; `ker DF(0) = ℝ²`, and `2 ≤ 1` fails. `hrank` fails there at `(1, 1)` (by hand, every clause checked) |
| every `Ω i` empty, or `ι` empty | `hloc` fails at `θ = θ₀` itself, so there is no instance. Some `Ω i` empty: they add nothing |
| `M` of dimension `0` | The statement says: if the level set near `θ₀` is countable (and `θ₀` has the largest rank), `DF(θ₀)` is injective. True. Compiled as a consequence (`Chk4.lean` (iii)) |
| the hypotheses with a positive kernel | They can all hold: `F` = the first coordinate of `ℝ²`, `g = F`, `M = ℝ`, `Φ m = (0, m)`; the conclusion is `1 ≤ 1`. Compiled (`Chk4.lean` (i)) |

**The coordinator's question: `ContDiffOn` on an arbitrary set.** On a set of one point, and on any
set whose points are all isolated in it, `ContDiffOn ℝ 1 f s` holds for every map `f` (compiled:
`Chk4.lean` (ii) for one point, `Chk5.lean` for a discrete set, from Mathlib's
`contDiffWithinAt_singleton`). So with such `Ω i` the hypothesis `hΦ` says nothing about `Φ i`.
This makes no statement false and none empty: a discrete subset of `M` is countable, so each
image `Φ i (Ω i)` is countable, their union is countable, and `hloc` can then hold only if the
level set near `θ₀` is countable, in which case the conclusion is true (the row "`M` of dimension
`0`"; the hypotheses can hold, for instance for `F` the identity). The same for a countable `Ω i`
that is not discrete, such as the rationals: there `hΦ` does say something, and the image is
countable anyway. For an arbitrary uncountable `Ω i` the bound on the Hausdorff dimension still
holds (Mathlib's lemma is for any set). So removing `hΩ` gives a stronger statement, which is
proved. It is not needed for the families of the papers, whose sets `Ω i` are open or the whole
space ((c) below).

**(b) Is `finrank_le_funDim_add_of_locally_mem_iUnion_image` the paper's converse for one
parameter of the largest rank? Yes. Is `hmax` needed? Yes.** (By reading; the example by hand.)

The Lean text: `(hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (hχ : AnalyticOnNhd ℝ A.χ Set.univ) (θ
: Params A dIn dOut) (hmax : ∀ θ' : Params A dIn dOut, funDim A S θ' ≤ funDim A S θ) … (Φ : ι → M
→ Params A dIn dOut) (Ω : ι → Set M) (hΦ : ∀ i, ContDiffOn ℝ 1 (Φ i) (Ω i)) (hloc : ∃ U ∈ 𝓝 θ, ∀
θ' ∈ U, (∀ x : Matrix T dIn ℝ, eval A S θ' x = eval A S θ x) → ∃ i, ∃ m ∈ Ω i, Φ i m = θ') :
Module.finrank ℝ (Params A dIn dOut) ≤ funDim A S θ + Module.finrank ℝ M`.

- The paper (S proof of Proposition 4.5, D proof of Proposition 4.6): "let `r` be the largest rank
  that the Jacobian of `F_X` attains on any batch at any parameters … Take `θ` at which the rank
  on `X` is `r` … Conversely, let every `θ′` in a neighborhood of `θ` in `Z` be the image of `θ`
  under a symmetry. … so `P − r ≤ k`". `hmax` is "the rank at `θ` is the largest", `hloc` is "every
  `θ′` in a neighborhood of `θ` in `Z`" (`Z` is the set of parameters near `θ` with the same
  function), and the conclusion is `P − r ≤ k` with `k = dim M`. The paper also takes `θ` at which
  the symmetries act locally freely; the converse does not use this, and Lean does not ask it.
  Lean does not ask that the images are symmetries or that they have the same function, and takes
  maps of class `C¹` in place of a Lie group: a more general statement.
- **`hmax` is needed.** Take no block (`L = 0`), one token, `d_in = d = d_out = 1`, no
  normalization: `F_θ(x) = x E D`, `P = 2`. At `θ = (0, 0)` the derivative of `θ' ↦ x E' D'` is
  `0`, so `fd(θ) = 0`. The parameters with the same function are those with `E' D' = 0`: the two
  axes, the images of `m ↦ (m, 0)` and `m ↦ (0, m)` on `M = ℝ`. Every hypothesis but `hmax` holds
  (`hf` has nothing to say, `χ = id` is analytic, `ι` has two elements, the maps are linear,
  `U` is the whole space), and the conclusion `2 ≤ 0 + 1` fails. `hmax` fails: `fd(1, 1) = 1`.

**(c) Does the `ae_` form express "at generic parameters, locally identifiable up to its
symmetries ⟹ the equality condition (lower bound)"? Yes, for a family of symmetries given as
countably many maps of class `C¹` on subsets of a space of dimension `k`.** (By reading.)

The conclusion `P ≤ fd(θ) + k` at almost every `θ` is the lower bound `fd ≥ P − k`; with the upper
bound (S Theorem 4.2) it is the equality condition. The family `Φ θ` may depend on `θ` ("the
images of `θ`"), the sets `Ω i` do not. Its proof needs nothing beyond (b): almost every parameter
has the largest functional dimension (`ae_funDim_ge`).

Which families fit "countably many maps of class `C¹` on (open) subsets of a space of dimension
`k`":

| Family | Fits directly? |
|---|---|
| changes of basis in `GL(d)`: one for a residual network, `L + 1` for a skipless one | Yes: `Ω` = the invertible matrices, an open subset of the `d × d` matrices (dimension `d²`), or of `L + 1` copies; one map `G ↦ θ.cob G G`, of class `C¹` there (it uses `G⁻¹`) |
| rescalings of the values of gated units | Yes: `Ω` = the vectors without a zero entry in `ℝ^s`; one map |
| changes of basis inside the heads | Yes: `Ω` = families of invertible `d_h × d_h` matrices, two per head; dimension `2 ∑ H d_h²` |
| products of these | Yes: the product space; the dimensions add up to `k = dim 𝒢 + s` |
| the orthogonal group (pre-RMSNorm) | No: it has dimension `d(d−1)/2` and is not an open subset of a space of that dimension. As a subset of the `d × d` matrices (allowed now that `Ω i` is any set) it would give `k = d²`, a weaker bound that is not the equality condition. It needs a cover by maps from the antisymmetric matrices: finitely many Cayley transforms with sign changes, or the two maps `A ↦ exp(A)` and `A ↦ R exp(A)` with `R` a reflection. The branch states such a cover in `Generic/Cayley.lean` (outside the brief) |
| permutations of hidden units or heads, sign flips of tanh units | Not as an open subset: they are finitely many. They enter through the index `ι`, one map for each permutation and sign pattern |

If the hypothesis is taken from the library's own statements of local identifiability, whose
symmetries are near the identity, no permutation and no sign flip is needed, and one Cayley
transform covers the orthogonal matrices near the identity.

**(d) Sard's theorem. A strengthening, and no gap is hidden.** (By reading; the axioms by
compiling.) The paper: "By Sard's theorem this image contains no open subset of a manifold of
larger dimension". The Lean statements have no hypothesis that stands for a theorem of the
literature, and at `679de09` they are proved from Mathlib alone, with the Hausdorff dimension in
place of Sard's theorem and the inverse function theorem in place of the constant rank theorem
(`Chk1.out`, `Chk4.out`: `propext`, `Classical.choice`, `Quot.sound`). They are stronger than the
paper's step in three ways: maps of class `C¹`, countably many of them, on arbitrary subsets. At
the commit of the brief (`2fc98cc`) the three statements were `sorry`; that was the only gap, and
the index said so.

---------------------------------------------------------------------------------------------------

## Part 2: the statements, file by file

Verdicts: SAME, LEAN STRONGER, LEAN WEAKER, DIFFERENT, PART, FALSE. "General form" means: stated
for every activation or gate with the conclusion of Lemma B.3 as a hypothesis (`UnitsRigid`,
`GatedUnitsRescale`). All by reading unless a note says more.

### `Residual/DepthTransformer.lean`, `DepthTransformerGated.lean`, `DepthTransformerRMS.lean`, `DepthTransformerGatedRMS.lean` (28 theorems, proved)

| Statement (and its three siblings) | Paper | Verdict |
|---|---|---|
| `smallWritesLimit_eq_zero_attentionMlp`, `…_attentionGated`, `smallWritesLimitNorm_eq_zero_attentionMlp_rmsNorm`, `…_attentionGated_rmsNorm` | S proof of Lemma A.27, the flat directions of `J_0`, for a network with both kinds of block | SAME (proof piece, general form). Note 1 |
| `eventually_funDim_smallWrites_attentionMlp`, `…_attentionGated`, `…_attentionMlp_rmsNorm`, `…_attentionGated_rmsNorm` | S Lemma A.27, first and second value, at one `θ` with the conditions of the proof | SAME (general form); with the next row it is the lemma's "for generic `θ`". PART of the lemma: values 1 and 2 of 4 |
| `ae_smallWritesGeneric_attentionMlp`, `…_attentionGated`, `…_attentionMlp_rmsNorm`, `…_attentionGated_rmsNorm` | S proof of Lemma A.27: "At generic parameters the hypotheses of Lemma B.3 hold for the units of all blocks together"; "the queries and values of every head have full column rank" | SAME (proof piece) |
| `ae_funDim_attentionMlp_residual`, `ae_funDim_attentionGated_residual`, `ae_funDim_attentionMlp_residual_rmsNorm`, `ae_funDim_attentionGated_residual_rmsNorm` | S Theorem 4.7, first sentence | LEAN STRONGER (a larger family of networks, no width hypothesis; general form) |
| `ae_funDim_attentionMlp_residual_ge_add`, `…Gated…_ge_add`, `…Mlp…_rmsNorm_ge_add`, `…Gated…_rmsNorm_ge_add` | S Theorem 4.7: "So the skips raise the functional dimension by at least `L dim 𝒢`" | SAME on the paper's blocks; LEAN STRONGER (total width for a block with both kinds; general form) |
| `ae_funDim_attention_tanh_residual`, `ae_funDim_attention_gelu_residual`, `ae_funDim_attention_swiglu_residual`, `ae_funDim_attention_geglu_residual`, and the four with `_rmsNorm` | S Theorem 4.7, first sentence, for attention blocks with tanh, GELU, SwiGLU or GeGLU blocks | LEAN STRONGER (larger family, no width hypothesis); no hypothesis from Lemma B.3 |

Note 1 (the flat directions against the paper's proof for a network with both kinds of block).
The paper treats the mixed network in the paragraph "Attention blocks without normalization":
"First take an input whose tokens all equal `x` … where `i` runs over the heads and `j` over the
hidden units. This is `D_φ G(φ, x) ψ` with `M + ∑_i C_i` in place of `M`, so for a flat `η` Lemma
B.3 gives a rescaling at every unit. The terms of the units then vanish at every input … Next take
an input whose tokens other than the second all equal the first … So Step 2 for attention blocks
in Appendix B gives `ψ_M = 0`, `ψ_{B_i} = 0` and `ψ_{C_i} = 0` for every head." So the hidden
units need the hypotheses of Lemma B.3 and the heads those of Step 2, and no condition links a
head with a hidden unit. The Lean hypotheses are exactly this pair, on the two parts of the
parameters:

- on the heads, `SmallWritesGenericAttention θ.sumFst`: `E` and `D` of rank `d`; the query, key,
  value and output matrices of every head of rank `d_h`; some `v` with the columns `B_j vᵀ` of all
  heads of all blocks nonzero and pairwise non-collinear and every `v C_j` nonzero (the thirteenth
  audit compared this structure with the paper for attention blocks alone);
- on the hidden units, `SmallWritesGeneric θ.sumSnd`: `E` and `D` of rank `d`; every row of
  `W_write^ℓ D` nonzero; the columns of `E W_read^ℓ`, over all blocks, nonzero and pairwise
  non-collinear; for gated units (`SmallWritesGenericGated`) the gate columns in that place and
  every value column nonzero;
- `UnitsRigid σ σ' dIn dOut (Σ ℓ, hid ℓ)` or `GatedUnitsRescale …`: the conclusion of Lemma B.3
  for the units of all blocks together, with biases in it, as the paper needs ("The constants
  `−½ log k` act as biases of the tanh units, which Lemma B.3 allows");
- a token `t₂` that sees itself and another token `t₁`: the paper's second input.

Under pre-RMSNorm the conditions are the same "with `E` and `D` replaced by the identity"
(`SmallWritesGenericAttentionRMS`, `SmallWritesGenericRMS`, `SmallWritesGenericGatedRMS`), and
Lemma B.3 is taken with `d` inputs and `d` outputs (`UnitsRigid σ σ' d d …`), as in the files for
one kind of block. The conclusion: `η_E = E X`, `η_D = −X D` (`X` any matrix; under RMSNorm
antisymmetric, `Yᵀ = -Y`), the reads and writes of the heads are those of `headDirQK θ.sumFst Γ +
headDirVO θ.sumFst Γ'`, and the reads and writes of the hidden units vanish (gated: the gate
columns vanish, the value column of unit `i` is `−α_i` times itself and its write row `α_i` times
itself). This is the paper's space of flat directions of `J_0`, of dimension `d² + s` and
`d(d−1)/2 + s`.

Note 2 (the values, by a computation; `transformer_check.out`). Ranks of the Jacobian of the
residual network at random parameters, two draws each, without normalization and under
pre-RMSNorm (`ε = 0.3`). The rank is read from a gap in the singular values of at least nine
orders of magnitude in every residual case inside the hypotheses.

| Network | `P`, `s` | Lean value, no norm / RMS | Rank found |
|---|---|---|---|
| A: one attention block (1 head, `d_h = 1`), then one tanh block (2 units); `d = 2`, 2 tokens, no mask | 24, 2 | 18 / 21 | 18 / 21 |
| B: one tanh block (3 units), then one attention block (2 heads, `d_h = 1`); `d = 3`, `d_out = 4`, 3 tokens, causal | 63, 4 | 50 / 56 | 50 / 56 |
| B2: one attention block (2 heads, `d_h = 1`), then one tanh block (2 units); `d = 2`, causal | 32, 4 | 24 / 27 | 24 / 27 (skipless 16 / 25: gain 8 / 2 = `L dim 𝒢`) |
| C: one attention block (1 head, `d_h = 2`), then one SwiGLU block (2 units); `d = 2`, causal | 36, 10 | 22 / 25 | 22 / 25 (skipless 14 / 23) |
| E: GELU block (1 unit), attention block, GELU block (3 units); `d = 2`, `d_in = 3` | 42, 8 | 30 / 33 | 30 / 33 |
| F: a block with a head and 2 tanh units side by side, then a tanh block | 32, 2 | 26 / 29 | 26 / 29 |
| G: attention block, empty block, tanh block | 24, 2 | 18 / 21 | 18 / 21 |
| **outside**, X1: `d_h = 3 > d = 2` | 40, 18 | 18 / 21 | 20 / 23: the value fails (the head changes of basis do not act freely) |
| **outside**, X2: no token sees another token | 24, 2 | 18 / 21 | 12 / 18: fails |
| **outside**, X3: one token | 24, 2 | 18 / 21 | 12 / 18: fails |
| **outside**, X4: `d_in = 1 < d = 2` | 22, 2 | 16 / 19 | 12 or 13 / 16: fails |

So the hypotheses `hdh`, the two tokens with the mask, and `hdIn` are each needed. The skipless
ranks of the cases with a block narrower than `d` have no clear gap in double precision in some
draws; I draw no conclusion from them.

### `Residual/ExactGainTransformer.lean` (4 theorems, proved)

| Statement | Paper | Verdict |
|---|---|---|
| `ae_funDim_attentionMlp_residual_eq_add_of_skipless`, `…Gated…`, and the two with `_rmsNorm` | S Theorem 4.7: "and by exactly `L dim 𝒢` when the skipless network satisfies the equality condition too" | LEAN STRONGER in form (the hypothesis at one `θ`), general form; conditional, as the paper's clause is |

Note 3. What is claimed: at almost every `θ`, if the skipless network has `fd = P − (L+1) dim 𝒢 −
s` at this `θ`, the residual network has exactly `L dim 𝒢` more. What is not claimed: that the
skipless network has this value at any parameter. The papers do not prove it for these networks
(D Theorem 5.2 is for "blocks … all of one kind, tanh, GELU, SwiGLU or GeGLU"), and the file
header says so. The statement has no width hypothesis, and needs none: it is `fd₁ = P − dim 𝒢 − s`
minus the hypothesis. That it gives the paper's clause (the hypothesis at almost every `θ` gives
the conclusion at almost every `θ`): compiled, `Chk2.lean` (c).

### `Residual/LocalIdentifiabilityTransformer.lean` (1 definition, 17 theorems, proved)

| Statement | Paper | Verdict |
|---|---|---|
| `Params.sumOf`, `Params.sumOf_sumFst_sumSnd` | notation: the parameters of a block with both parts | SAME (a definition and its check) |
| `exists_cob_heads_of_eval_eq_residual_attentionMlp`, `…_attentionGated`, and the two with `_rmsNorm` | S Proposition 4.5, proof of the direction from the equality condition to local identifiability, at one `θ` | SAME (proof piece); PART of the proposition (one direction) |
| `ae_exists_cob_heads_of_eval_eq_attentionMlp_residual`, `…attentionGated_residual`, and the two with `_rmsNorm` | S Corollary 4.9 | LEAN STRONGER (larger family; general form) |
| `ae_exists_cob_heads_of_eval_eq_attention_tanh_residual`, `…_gelu_…`, `…_swiglu_…`, `…_geglu_…`, and the four with `_rmsNorm` | S Corollary 4.9 for attention blocks with tanh, GELU, SwiGLU, GeGLU blocks | LEAN STRONGER (larger family); no hypothesis from Lemma B.3 |

Note 4 (the conclusion). `θ' = (Params.sumOf ((θ.sumFst.headsQK K).headsVO K') θ.sumSnd).cob (fun
_ => G) (fun _ => G)` is: first the changes of basis inside the heads, `(W_Q, W_K) ↦ (W_Q K, W_K
K^{-⊤})` and `(W_V, W_O) ↦ (W_V K', K'^{-1} W_O)`, on the head part of `θ`, the hidden units as
they are (for gated blocks `θ.sumSnd.rescale c`: the value column of unit `i` divided by `c_i`,
its write row multiplied by `c_i`, `0 < c_i`); then the same `G` at all hidden states, `E ↦ E G`,
every read `↦ G⁻¹ ·`, every write `↦ · G`, `D ↦ G⁻¹ D`. Compiled (`Chk2.lean` (e)): the embedding
is `θ.E * G` and the readout `G⁻¹ * θ.D` (by `rfl`), the reads and writes of the hidden units are
`G⁻¹ * θ.sumSnd.read ℓ` and `θ.sumSnd.write ℓ * G`, those of the heads `G⁻¹ *` and `* G` of the
head part after `K`, `K'`. This is the display of S Corollary 4.9 with the symmetries inside the
blocks. Under pre-RMSNorm `Q` is orthogonal (`(Q : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ`).
That this image has the same function I checked by a computation on a network with three blocks,
for MLP and for gated units, with and without RMSNorm: the outputs differ by at most `1.5e-13`.

- **Is it "a symmetry close to the identity"?** Yes. The statement begins `∀ V ∈ 𝓝 (1 : Matrix d d
  ℝ), ∀ W ∈ 𝓝 (1 : ∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)` (for gated blocks also `∀ Wc ∈ 𝓝 (1 : ∀ ℓ,
  hid ℓ → ℝ)`), then `∃ U ∈ 𝓝 θ, ∀ θ' ∈ U, …`, and gives `G ∈ V`, `K ∈ W`, `K' ∈ W`, `c ∈ Wc`. So
  for every closeness to the identity there is a neighbourhood `U` of `θ` in which every `θ'`
  with the same function is such an image: the paper's "all close to the identity". No
  permutation and no sign flip appears, as near the identity none is needed.
- **Which direction is proved.** From the equality condition to local identifiability: the four
  statements at one `θ` take the value of `fd` at `θ` as the hypothesis `hfd`, together with what
  makes the symmetries act locally freely at `θ` (`E` of rank `d`; the query and value matrices of
  every head of rank `d_h`; for gated blocks no value column `0`), as the paper does ("Take `θ` at
  which the rank on `X` is `r` and the symmetries act locally freely"). The twelve `ae_`
  statements are Corollary 4.9: Theorem 4.7 with this direction. The other direction is in
  `Dimension/IdentifiableConverse.lean` in a general form, not yet for these networks in the
  files of the brief.

### `Residual/BlocksAlone.lean` (5 definitions, 6 theorems) and `Residual/BlocksAloneAttention.lean` (3 theorems), proved

| Statement | Paper | Verdict |
|---|---|---|
| `BlockParams`, `BlockParams.toParams`, `evalBlocks` | S Corollary 4.10 (ii): "Without an embedding and a readout, so that `h_0 = x ∈ ℝ^{T × d_model}` and `y = h_L`" | SAME (Check 2) |
| `jacobianRankBlocks`, `funDimBlocks` | D Definition 4.1 for this family | SAME (Check 2) |
| `hidden_toParams_zero`, `evalBlocks_eq` | "`h_0 = x`", "`y = h_L`" (under a normalization `y = χ(h_L)`) | SAME |
| `finrank_blockParams` | the number `P` of parameters of the blocks | SAME |
| `jacobianRankBlocks_le_finrank`, `jacobianRankBlocks_le_funDimBlocks`, `exists_jacobianRankBlocks_eq_funDimBlocks` | basic facts of the definition | SAME (not in the papers as statements) |
| `eventually_funDimBlocks_smallWrites_attention` | S Lemma A.27, fourth value ("no embedding, readout, biases or normalization"), for attention blocks, at one `β` with the conditions of the proof at `E = D = I` | SAME (proof piece); PART of the fourth value (attention blocks only; no statement that the conditions hold at almost every `β`, see Note 5) |
| `ae_funDimBlocks_attention_residual` | S Corollary 4.10 (ii), `fd = P − s` | LEAN STRONGER (any numbers of heads, widths `1 ≤ d_h ≤ d`) |
| `ae_funDimBlocks_attention_residual_of_width` | S Corollary 4.10 (ii) in the setting of the main text, `fd = L (4 d² − 2 d²/H)` | SAME |

Note 5. The network: `L` attention blocks, identity skips, no normalization, `h_0 = x`,
`y = h_L`. The parameter count: `P = ∑_ℓ d · 3 H_ℓ d_{h,ℓ} + ∑_ℓ H_ℓ d_{h,ℓ} · d`, which is
`4 L d²` when `H d_h = d`. The value: `Module.finrank` and the ranks are natural numbers, and the
main-text value is written `L * (4 * Fintype.card d ^ 2 - 2 * Fintype.card d ^ 2 / Hn)` with the
division and the subtraction of natural numbers. Under `hHn` and `hHd` they are exact for `L ≥ 1`:
`H` divides `d`, so `2 d²/H = 2 H d_h²` and `4 d² ≥ 2 d²/H` (by hand); for `L = 0` both sides are
`0`. Compiled on `L = 2`, `d = 2`, two heads of width 1 (`Chk3.lean`): `P = 32` and some `β` has
`funDimBlocks = 24`. By a computation: rank 24 there; rank 8 for `L = 1`, `H = 1`, `d = 2`; rank
60 for `L = 2`, `H = 3`, `d = 3`; rank 96 for `L = 2`, `H = 2`, `d_h = 2`, `d = 4`; all equal to
`L (4 d² − 2 d²/H)`; and rank 12 `= P − s` for two blocks of one head of width 1 with `d = 2`,
where `H d_h < d` (Lean's general form). Lemma A.27's fourth value in the form "for almost every
`β`, for all small `τ ≠ 0`" is not a public statement of the file: the conditions
`SmallWritesGenericAttention β.toParams` at almost every `β` are not stated (the proof of the
corollary takes one parameter with them). This leaves nothing of Corollary 4.10 (ii) open.

### `Absorb/RMSNormAttention.lean` (12 theorems, proved)

| Statement | Residual network | Skipless network | `ε` | Paper | Verdict |
|---|---|---|---|---|---|
| `locallyLipschitz_f_attention` | (the attention map is locally Lipschitz) | | | A Appendix A.3: the blocks are "locally Lipschitz" | SAME (a fact the proof uses) |
| `ae_someBlockNonzero_attention` | attention blocks, any `χ` | | | A proof of Theorem 4.3, "Measure zero": some `a_ℓ(n̄)` has a nonzero entry | SAME (proof piece, in the library's form `SomeBlockNonzero`) |
| `ae_ne_skipless_rmsNorm_attention` | attention blocks, `rmsNorm ε` | any `Arch T d' L'` with `χ = rmsNorm ε'`, `ε' > 0`, locally Lipschitz blocks | `> 0` | A Theorem 4.3 | SAME for this kind; LEAN STRONGER on the skipless side (own `d'`, own `ε'`) |
| `ae_not_dense_eq_skipless_rmsNorm_zero_attention` | attention blocks, `rmsNorm 0` | any `Arch T d' L'` with `χ = rmsNorm 0`, continuous blocks | `= 0` | A Theorem 4.3 | SAME for this kind; equality in the paper's sense for `ε = 0` |
| `ae_someBlockNonzero_attention_mlp` | attention and MLP blocks, any `χ` | | | as above | SAME (proof piece) |
| `ae_ne_skipless_rmsNorm_attention_mlp` | attention and MLP blocks (`Arch.sum`), `σ` locally Lipschitz and nonzero on the positive reals | as in row 3 | `> 0` | A Theorem 4.3: "The theorem covers pre-RMSNorm transformers, which alternate attention and MLP blocks" | SAME for this kind (general in `σ`) |
| `ae_not_dense_eq_skipless_rmsNorm_zero_attention_mlp` | the same, `rmsNorm 0` | as in row 4 | `= 0` | A Theorem 4.3 | SAME for this kind |
| `ae_someBlockNonzero_attention_gated` | attention and gated blocks | | | as above | SAME (proof piece) |
| `ae_ne_skipless_rmsNorm_attention_gated` | attention and gated blocks, gate locally Lipschitz and nonzero on the positive reals | as in row 3 | `> 0` | A Theorem 4.3 | SAME for this kind |
| `ae_not_dense_eq_skipless_rmsNorm_zero_attention_gated` | the same, `rmsNorm 0` | as in row 4 | `= 0` | A Theorem 4.3 | SAME for this kind |
| `ae_ne_skipless_rmsNorm_attention_gelu` | attention and GELU blocks | as in row 3 | `> 0` | A Theorem 4.3 | SAME for this kind; no hypothesis on the activation |
| `ae_ne_skipless_rmsNorm_attention_swiglu` | attention and SwiGLU blocks | as in row 3 | `> 0` | A Theorem 4.3 | SAME for this kind; no hypothesis on the gate |

Each statement is a PART of Theorem 4.3 in the sense that it fixes the kind of the residual
network; together with the rows for MLP blocks they cover the paper's kinds.

Note 6.

- **The skipless network is of any kind.** It is an arbitrary `A' : Arch T d' L'` on the same
  tokens, inputs and outputs, with any depth `L'`, any model dimension `d'` (A Scope: "A skipless
  network that is compared with a residual one may have another model dimension") and any
  widths; so it may be a network of attention blocks or a transformer, whose blocks are locally
  Lipschitz (`locallyLipschitz_f_attention`, `locallyLipschitz_f_sum`). Compiled (`Chk3.lean`,
  `abs1`): for a transformer of attention and GELU blocks, some `θ` equals no skipless network of
  the same architecture.
- **`ε > 0`:** "equals no skipless network" is `∃ X, eval … 1 θ X ≠ eval A' 0 θ' X`; the skipless
  network may have its own `ε' > 0`. **`ε = 0`:** `¬ ∃ S, Dense S ∧ ∀ X ∈ S, DefinedAt … 1 θ X ∧
  DefinedAt A' 0 θ' X ∧ eval … = eval …`, which is the paper's "Two such networks are equal if they
  agree on a dense set of inputs at which both are defined" (A Section 2), with `DefinedAt` = no
  zero row in `XE` or in a later hidden state. A residual network with `ε > 0` against a skipless
  one with `ε = 0`, or the reverse, is in no statement; the paper compares networks with one `ε`.
- **A transformer in which no block has a hidden unit** is outside the three pairs for sums
  (`hhid` fails), although it has heads. The same network written as `Arch.attention` is inside
  the first pair. The paper's transformers have MLP blocks, so nothing of the paper is lost.
- The mask enters only the attention-only pair (some token sees a token). The pairs for sums ask
  nothing of the mask, since they use a hidden unit.
- Named forms exist for GELU and SwiGLU with `ε > 0` only. For tanh, ReLU, ReLU², GeGLU, ReGLU,
  and for every kind with `ε = 0`, the general statements apply once the two hypotheses on `σ` are
  given (both hold for these functions, by hand; the file header says that
  `Absorb/RMSNormKinds.lean` states the theorem for the seven kinds of MLP block, which I did not
  read).

### `Generic/LevelSetImages.lean` (1 theorem) and `Dimension/IdentifiableConverse.lean` (2 theorems): stated with `sorry` at `2fc98cc`, proved at `679de09`

| Statement | Paper | Verdict |
|---|---|---|
| `finrank_ker_le_of_level_set_subset_iUnion_image` | S proof of Proposition 4.5 and D proof of Proposition 4.6, the converse direction: the constant rank theorem, "`θ′ ↦ F_{θ′}(x)` is constant on `Z`", and "By Sard's theorem this image contains no open subset of a manifold of larger dimension, so `P − r ≤ k`" | LEAN STRONGER (proof piece, for maps between finite-dimensional spaces; `C¹`, countably many maps, any subsets). True as stated (Check 5 (a)) |
| `finrank_le_funDim_add_of_locally_mem_iUnion_image` | the same step at one parameter of the largest rank: `P − r ≤ k` | LEAN STRONGER (any family of images, any network with analytic `f_ℓ`, `χ`, any stream matrices). `hmax` is needed (Check 5 (b)) |
| `ae_finrank_le_funDim_add_of_ae_locally_mem_iUnion_image` | S Proposition 4.5, D Proposition 4.6: "at generic parameters, it is locally identifiable up to its symmetries" ⟹ the equality condition (its lower bound) | LEAN STRONGER as a general form; PART of the propositions: one direction, the lower bound only, and the families of the papers are not put in here (Check 5 (c)) |

---------------------------------------------------------------------------------------------------

## What the authors should know

Nothing false, nothing vacuous, nothing drifted. In order of weight:

1. **The branch moved under the brief.** The two files on the converse were `sorry` at the commit
   of the brief and are proved at `679de09`, with one hypothesis fewer (`hΩ`). The statements
   without `hΩ` are true, and `ContDiffOn` on a discrete or countable `Ω i` makes nothing false or
   empty (Check 5).
2. **Lemma A.27 for transformers is two statements, not one.** The four depth files state the
   value at one `θ` under conditions, and the conditions at almost every `θ`, and no
   `ae_eventually_funDim_smallWrites_…` as the files for one kind of block do. The combined form
   is two lines (`Chk2.lean` (b)). The same for the blocks alone, where the conditions at almost
   every `β` are not a public statement either. If the index or a paper sentence is to cite one
   Lean name for "Lemma A.27 for transformers", there is none yet.
3. **The two tokens are asked of every network of the sum, also of one without any head** (Check
   3, Remark 2), and **a block without heads needs a nonempty `dh ℓ`** (Remark 1). Neither
   excludes a network of the paper.
4. **Absorb Theorem 4.3 for sums asks for a hidden unit** (`hhid`), so a sum without hidden units
   is covered only when written as `Arch.attention` (Note 6). Named forms: GELU and SwiGLU with
   `ε > 0` only.
5. **`hmax` and `hrank` are needed** in the two statements of the converse at one point (examples
   in Check 5). The form at generic parameters needs neither.
6. **The orthogonal group does not fit the general form directly**: as a subset of the `d × d`
   matrices it would give `k = d²`, not `d(d−1)/2` (Check 5 (c)). The cover by Cayley transforms
   that the branch now states is the right kind of step; I did not read it.
7. Lean's family of networks is larger than the paper's (blocks with heads and hidden units side
   by side, empty blocks, heads that vary from block to block, `H d_h ≠ d`). The values hold
   there in the cases that I computed (F, G, B, and the last blocks-alone case).

## Corrections for `STATEMENTS.md` (line numbers of `591d9e4`)

1. Line 772, row of `Generic/LevelSetImages.lean`: "The proof may use the Hausdorff dimension from
   Mathlib; no hypothesis from the literature". The statement is proved, and the file header now
   says "the proof uses". Write: "The proof uses the Hausdorff dimension from Mathlib
   (`DifferentiableOn.dimH_image_le`) and the inverse function theorem; no hypothesis from the
   literature; the sets `Ω i` need not be open."
2. Line 773, row of `Dimension/IdentifiableConverse.lean`: "The forms for the kinds of network of
   the papers (changes of basis, orthogonal ones, rescalings, head changes) are not yet stated."
   Since `679de09` this is out of date: the row of `Dimension/IdentifiableConverseCob.lean` states
   forms for the changes of basis, and since `cbee1f1` the rows of `Dimension/IdentifiableIff.lean`
   and `Residual/IdentifiableIff.lean` state the equivalence (I read these rows' titles only, not
   the files). Replace the sentence by a pointer to those rows.
3. From line 154, the list "Not yet compared by such a reader": after this audit, take out the
   eleven files of this brief (`Absorb/RMSNormAttention.lean`, `Residual/BlocksAlone.lean`,
   `Residual/BlocksAloneAttention.lean`, the four `Residual/DepthTransformer….lean`,
   `Residual/LocalIdentifiabilityTransformer.lean`, `Residual/ExactGainTransformer.lean`,
   `Generic/LevelSetImages.lean`, `Dimension/IdentifiableConverse.lean`), the last two as compared
   at `679de09`.
4. Lines 764 to 767, the four rows of the depth files: they say "`fd(θ_τ) = …` for all small
   `τ ≠ 0`; the conditions at almost every parameter". This is correct. A reader may take it for
   one statement "for almost every `θ`"; consider adding "(two statements; together: for almost
   every `θ`, for all small `τ ≠ 0`)".
5. Line 781, row of `Absorb/RMSNormAttention.lean`: correct. Consider adding that the rows for
   sums need a hidden unit, so that a sum without hidden units is covered by the attention row
   only.
6. Nothing is missing: all 79 public names are in the rows (some by the stated abbreviations), the
   statuses "proved" are right at `679de09` for all eleven files, and at `2fc98cc` the two files of
   the converse were rightly "in work".

## What I could not check

- The proofs. I read none of them as proofs; "proved" means: the file has no `sorry`, my copy
  compiles (for the two changed files) or the copied build has it (for the nine others), and
  `#print axioms` shows the three standard axioms.
- The nine unchanged files were not recompiled by me; I used the compiled library copied from
  `/home/claude/lp/lean` (at the same commit as the sources that I read, by `git log` and
  `diff -rq`).
- The coordinator's numeric scripts and their counts ("10 cases", "14 cases" in the index): not run,
  not read.
- `Network/Sum.lean` and `Network/Transformer.lean` I read for the definitions only (the other
  reader compares them). `Dimension/UpperBoundTransformer.lean`, `Symmetry/InsideBlocksSum.lean`
  and `Generic/Sum.lean`, which these files import, I did not compare with the papers, beyond the
  definitions `Params.sumFst`, `Params.sumSnd`.
- The new files of the branch (`Generic/Cayley.lean`, `Dimension/IdentifiableConverseCob.lean`,
  `Dimension/IdentifiableIff.lean`, `Residual/IdentifiableIff.lean`,
  `Symmetry/OnlyOrthogonalRows.lean`): not read.
- Whether a statement of the nine proved files changed after its first commit: not checked (the
  nine are the same at the four commits of this afternoon that I saw).
- The numerical ranks are in double precision at two random draws per case. They support the
  values; they prove nothing. The skipless ranks of networks with a block narrower than `d` were
  not decided.
- The structures `SmallWritesGenericAttention`, `SmallWritesGenericAttentionRMS` against the
  paper's Step 2 for attention blocks in S Appendix B: I relied on the thirteenth and fourteenth
  audits and did not read Appendix B again.
