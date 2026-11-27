STATUS: complete

# Twenty-eighth audit of Lean statements against the papers (25 November 2026)

Subject: S Lemma A.18 for `ε = 0` with the symmetries inside blocks, from both ends, and for attention with MLP blocks; S Lemma A.2 (ii); S Proposition A.35 for blocks of width at least `d`; the "Not stated" notes of the index. Seven files of `lean/SkipsLean/`, 36 public theorems. S is the skips paper, D the dimension paper (`<scratchpad>/skips.txt`, `<scratchpad>/dim.txt`).

(An earlier run of this audit was cut off after two minutes; it had copied the seven files at `d6becbc`. This report is written anew.)

**Result.** Nothing false, nothing vacuous, nothing drifted in the seven files. All 15 statements "at generic parameters" are for almost every parameter and every Haar measure. The actions for `ε = 0` are the paper's; each hypothesis that the Lean statements add is used, with exact counterexamples when it is dropped (two could be weaker). One finding concerns the paper: on the open set of its proof, the bound of S Proposition A.35 fails when block 2 is the last block, has exactly `d_model` units and `d_out < d_model` (exact rank 4 against the bound 3 for `d_model = 2`); the Lean statements ask `d_out ≥ d`, which is the Scope of the paper, and are proved. Seven corrections for the index, among them 19 "Not stated" notes that are out of date.


## Commits read; `sorry`

- Commits of `/home/claude/lp` (branch `lean-plus`): `127aaac` when the reading began (the seven files were copied to `/home/claude/audit28/src2/` at that commit); `76034e7` when the axioms were printed; `d67195b` for the index (check 7 and Part 3); `6f31671` at the end.
- Against the copies of the earlier run (`d6becbc`): four files are unchanged; `Dimension/UpperBoundTwoSided.lean` and `Depth/InactiveUnitTwoSided.lean` got their proofs.
- Between `127aaac` and `6f31671`, in the seven files: `Symmetry/LocallyFreeTransformer.lean` got its proofs (`348c10a`; its six statements are unchanged, compared by a script; eight private helpers were added); the header of `Depth/InactiveUnitTwoSided.lean` changed in one sentence, twice (pointers to new files). No statement changed.
- New files with statements, written while this audit ran and **not read here**: `Dimension/UpperBoundTwoSidedGated.lean`, `Depth/InactiveGateTwoSided.lean` (proved at `d67195b`), `Depth/InactiveUnitEveryPoint.lean` (5 `sorry` at `6f31671`).
- Files with `sorry` among the seven: at `127aaac`, `Symmetry/LocallyFreeTransformer.lean` (6, all of its theorems); from `348c10a` on, none.
- Compiled by the reader at `76034e7` (`Ax28.lean`, against the existing build): each of the 36 public theorems of the seven files depends on `propext`, `Classical.choice`, `Quot.sound` only; no `sorryAx`.

How each check was done is said in the check: *reading*, *compiled* (a file in `/home/claude/audit28/`, with `lake env lean` against the existing build, nothing written there), or *computed* (Python, `python3 -I`).

## Part 1: checks

### 1. Generic means almost every parameter, for every Haar measure: YES

*Reading.* The 13 statements of `Symmetry/LocallyFreeRMSZeroGeneric.lean` (7) and `Symmetry/LocallyFreeTransformerGeneric.lean` (6) all have the form

```lean
(μ : Measure (Params … dIn dOut)) [μ.IsAddHaarMeasure] … : ∀ᵐ θ ∂μ, ∀ (G Q …) …, … = θ → …
```

None says "there is a parameter" or names an open set. The two of `Depth/InactiveUnitTwoSided.lean` are

```lean
∃ U : Set (Params …), IsOpen U ∧ U.Nonempty ∧ (∀ θ ∈ U, UnitInactive θ ℓ.succ j) ∧
  ∀ᵐ θ ∂μ, θ ∈ U → funDim … 0 θ + (…) ≤ Module.finrank ℝ (Params …)
```

with `(μ : Measure (Params …)) [μ.IsAddHaarMeasure]`: the bound at almost every point of the open set, for every Haar measure; and the two `not_ae_…` statements are `¬ ∀ᵐ θ ∂μ, … = …` for every Haar measure. The index types `T`, `d`, `dIn`, `dOut`, `hid ℓ`, `H ℓ`, `dh ℓ` have `Fintype` (the `variable` lines of each file).

*Compiled* (`Chk28.lean`: 15 instances at `Measure.addHaar` with numbers):

- the seven of `LocallyFreeRMSZeroGeneric.lean`: two ReLU² blocks and two ReGLU blocks under `rmsNorm 0`, `d = 2`, width 2, with `d_in = 2`, `d_out = 1` (embedding) and `d_in = 1`, `d_out = 2` (readout); two causal attention blocks, two tokens, `d = 3`, two heads of width 2;
- the six of `LocallyFreeTransformerGeneric.lean` for a transformer in the paper's sense: block 0 an attention block (two heads of width 2, no hidden unit), block 1 an MLP block (no head, three hidden units), `d = 3`, with ReLU, gated and ReGLU units, without normalization and with `rmsNorm 0`. The hypotheses `d_h ≤ d` and `H d_h + d_hidden ≥ d` hold with an empty part (`0 ≤ 3`; `4 + 0 ≥ 3`, `0 + 3 ≥ 3`);
- two of `InactiveUnitTwoSided.lean`: two ReLU blocks of width exactly `d = 2`, `d_in = d_out = 2` (`P = 24`): a nonempty open set on which unit `j` of the second block is inactive and `funDim + 19 ≤ 24` at almost every point of it; and the `not_ae_` statement for ReLU².

All instances depend on `propext`, `Classical.choice`, `Quot.sound` only (at `127aaac` those of the second group also showed `sorryAx`, through the six statements at one parameter, which were then in work; recompiled after their proofs were merged).

### 2. `ε = 0` with the symmetries inside blocks (`Symmetry/LocallyFreeRMSZero.lean`): the action is the paper's; every hypothesis that is asked is used somewhere, with exact counterexamples; two of them could be weaker

**The action.** *Reading.* S Proposition A.1 (ii): "the map `W ↦ W G` on the matrices that write a hidden state and `W ↦ G⁻¹ W` on those that read it preserves the function for every `G ∈ G`. For `ε = 0` and `G = cQ`, a read through RMSNorm maps to `Q^⊤ W` instead"; Lemma A.2 (i): "`N_ε(hG) = N_ε(h) M` […] Then `M = Q`, where `G = cQ` with `Q` orthogonal" (D Lemma A.1 adds "with `c > 0`"). Lean: `θ.cob G Q` with `(G ℓ) = s ℓ • (Q ℓ)`, `0 < s ℓ`, `Q ℓ` orthogonal: `E ↦ E G_0`, `write ℓ ↦ write ℓ * G_{ℓ+1}`, `read ℓ ↦ Q_ℓ⁻¹ * read ℓ`, `D ↦ Q_L⁻¹ * D` (`Q⁻¹ = Q^⊤`; in a pre-RMSNorm network the blocks and the readout read `N_ε(h)`). Same. The seven statements compose it with `rescaleMlp k c`, with `rescale c`, with `rescale c'` and `rescaleGate k c`, with `headsQK K` and `headsVO K'`, the maps that the twenty-seventh audit compared with the papers (they commute with `cob`).

*Compiled* (`Chk28b.lean`, three standard axioms): for `χ = rmsNorm 0` the composed maps preserve the function,

```lean
eval (Arch.mlp σ (rmsNorm 0) hid) 0 ((θ.cob G Q).rescaleMlp k c) x = eval (Arch.mlp σ (rmsNorm 0) hid) 0 θ x
eval (Arch.gated σ (rmsNorm 0) hid) 0 (((θ.cob G Q).rescale c').rescaleGate k c) x = eval … θ x
eval (Arch.attention sees (rmsNorm 0) H dh) 0 (((θ.cob G Q).headsQK K).headsVO K') x = eval … θ x
```

for `s ℓ > 0`, `Q ℓ` orthogonal, `σ` positively homogeneous of degree `k`, `c > 0`, `c' ≠ 0` (from `eval_cob_rmsNorm_zero`, `eval_rescaleMlp_params`, `eval_rescale_params`, `eval_rescaleGate_params`, `eval_headsQK`, `eval_headsVO`). *Computed* (`c2_zero.py`, part A): at one parameter with `Q_0` a rotation with entries `3/5, 4/5`, the composed map is `E ↦ E (s_0 Q_0)`, `read ↦ Q_0^⊤ read diag(c)`, `write ↦ diag(c^{−k}) write (s_1 Q_1)`, `D ↦ Q_1^⊤ D`.

**The conclusion** `(∀ ℓ, s ℓ = 1) ∧ Q = 1 ∧ ∀ ℓ i, c ℓ i = 1` is for the whole group `CO(d)` at every hidden state, every real `c` (with the embedding) or every positive `c` (with the readout): stronger than "act locally freely", as in the twins (twenty-seventh audit, check 3).

**The hypotheses.** *Reading; computed for the counterexamples* (`c2_zero.py`, exact rational arithmetic, `d = 2`, the maps written as in the Lean definitions; in each case the hypotheses that are kept hold, the maps fix `θ` exactly, and the conclusion fails; 23 counterexamples).

With the embedding (four statements): `hE : θ.E.rank = Fintype.card d`, `hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d`, the rescaled read columns nonzero (`hcol`; `hv`; `hv`, `hg`; for attention `hQr`, `hVr`), as in the twins; and `hs : ∀ ℓ, 0 < s ℓ`, `hQ`, `hG`, `[Nonempty d]`, which say what the group is. The proof: `E G_0 = E` gives `s_0 Q_0 = 1`, hence `s_0 = 1`, `Q_0 = 1`; then the read and the write of each block as without normalization.

| Dropped | Exact counterexample |
|---|---|
| `s_ℓ > 0` (ReLU², `k = 2`) | **at a parameter with all the other hypotheses** (two blocks, random integers): `s_0 = −1`, `Q_0 = −1` (so `G_0 = 1`), `c = −1` in block 1 |
| `s_ℓ > 0` (ReLU, `k = 1`) | at the same parameter: `s_0 = s_1 = −1`, `Q_0 = −1`, `Q_1 = 1`, `c = −1` in block 1 |
| `s_ℓ > 0` (ReGLU, `k = 1`, `2`) | at a parameter with all the other hypotheses: `Q_0 = −1`, `s_0 = −1`, `c = c' = −1`, and `s_1 = 1` (`k = 1`) or `s_1 = −1` (`k = 2`) |
| `s_ℓ > 0` (gated, values only) | at a parameter whose gate columns are zero: `s_0 = s_1 = −1`, `Q_0 = −1`, `c = −1`. With nonzero gate columns these maps do not fix `θ` (*reading:* `Q_ℓ = −1` multiplies the gate columns of the block that reads `h_ℓ` by `−1`, so a counterexample needs a block without nonzero gate columns, or `D = 0` with `s_L = −1`, `Q_L = −1`). |
| `Q_ℓ` orthogonal | at a parameter with all the other hypotheses: `Q_0 = ½ · 1`, `s_0 = 2`, `c = ½`, `s_1 = ½` (`k = 1`) |
| `E` of rank `d`; a write of rank `d` | `E = [[1,0],[0,0]]`, `Q_0 = diag(1,−1)`, a read with a zero second row; write `[[1,0],[1,0]]`, `Q_1 = diag(1,−1)` |
| a read column not zero | unit 3 with a zero read column **and** a zero write row, `c_3 = 5`. With a nonzero write row at that unit the maps do not fix `θ`. |

So `s_ℓ > 0` is not a technical hypothesis: without it the statements for ReLU, ReLU² and ReGLU blocks are false at every parameter (the pair `s = −1`, `Q = −1` gives the same `G` as `s = 1`, `Q = 1` and another action on the reads; the counterexamples also use a rescaling by `−1`, which these statements allow because they are for every real `c`). It is the `c > 0` of D Lemma A.1.

With the readout (three statements): `hD : θ.D.rank = Fintype.card d`, `hr : ∀ ℓ, (θ.read ℓ).rank = Fintype.card d`, `hE : θ.E ≠ 0`, the rescaled read columns nonzero, `ha : ∀ ℓ i, (fun a => θ.write ℓ i a) ≠ 0`, positive rescalings of hidden units (`hc`, ReLU and ReLU²) and of gates (`hc`, ReGLU), `hs` for gated and ReGLU blocks, `hQ`, `hG`, `[Nonempty d]`. The proof (*reading*): `Q_L⁻¹ D = D` gives `Q_L = 1`; if `Q_{ℓ+1} = 1`, the write row `i` of block `ℓ` is multiplied by `s_{ℓ+1} / c_i^k` (by `c_i s_{ℓ+1}`; by `c'_i s_{ℓ+1} / c_i^k`), and the rescaled read column is an eigenvector of the orthogonal `Q_ℓ⁻¹` with the positive eigenvalue `1/c_i` (`c'_i`), which is therefore `1`; then `s_{ℓ+1} = 1` from one write row and `Q_ℓ = 1` from the read of rank `d`; at the end `s_0 E = E` with `E ≠ 0`.

| Dropped | Exact counterexample |
|---|---|
| `E ≠ 0` | `E = 0`, `s_0 = 3` |
| `c > 0` (ReLU, `k = 1`) | **at a parameter with all the other hypotheses**: `c = −1` in block 1, `Q_0 = −1`, `s_0 = s_1 = −1` (the statement does not ask `s > 0`) |
| `c > 0` (ReLU², `k = 2`) | at the same parameter: `c = −1` in block 1, `Q_0 = −1`, `s_0 = −1`; and with all `s_ℓ = 1`: read `1`, `Q_0 = diag(1,−1)`, `c = (1,−1)`, `E = (1,0)` |
| `c > 0` (ReGLU gates) | `k = 2`: gate columns `e_1`, value columns in the span of `e_2`, `Q_0 = diag(−1,1)`, `c = −1`, `E = (0,1)`; `k = 1`: units with gate and value `e_1`, and `e_2`, `Q_0 = diag(−1,1)`, `c = c' = (−1,1)` |
| `s_ℓ > 0` (gated) | gate columns `e_1`, value columns in the span of `e_2`, `Q_0 = diag(1,−1)`, `s_1 = −1`, `c = −1`, `E = (1,0)` |
| read of rank `d`; `D` of rank `d` | a read with a zero row, `Q_0 = diag(1,−1)`; `D` with a zero row and a write with a zero column, `Q_1 = diag(1,−1)` |
| no write row zero | a write that is zero: `s_1 = 3`. With one zero row and a nonzero read column at that unit: no fixing map other than the identity on a grid (10 orthogonal matrices, 8 × 8 scales, 4³ positive `c`). |
| no read column zero (ReLU, ReLU²) | for `k = 0`: unit 3 with a zero read column and a nonzero write row, `c_3 = 5` (the statement is for every `k : ℕ`). For `k = 1`, `2`: none on the grid; a unit with a zero read column **and** a zero write row gives one (`c_3 = 5`). |
| no value column zero (gated) | all value columns zero: `s_1 = 2`, `c = ½`. With one zero and one nonzero: none on the grid. |
| no gate column zero (ReGLU) | all gate columns zero: `s_1 = 4`, `c = 2`, `c' = 1` (`k = 2`) |

Two remarks on these hypotheses (*reading*; neither makes a statement false):

- For ReLU and ReLU² blocks with the readout and `k ≥ 1`, "no read column zero" follows the proof of the paper but is not needed beside the others: the read has rank `d ≥ 1`, so one column `i₀` is nonzero, its unit gives `c_{i₀} = 1` and then `s_{ℓ+1} = c_{i₀}^k = 1`, and every unit has `c_i^k = s_{ℓ+1} = 1` from its nonzero write row. The same holds for the gated statements with "some value column of each block is nonzero" in place of "no value column is zero". The hypotheses as asked hold at almost every parameter, so nothing is lost at generic parameters.
- `cob_rmsNorm_zero_rescaleMlp_eq_self_of_rank_D` has no hypothesis `k ≠ 0`, while its twin without normalization (`cob_rescaleMlp_eq_self_of_rank_D`) has one: here the read columns give `c = 1` without the write rows, for every `k`.

**`s_ℓ > 0` is not asked in `cob_rmsNorm_zero_rescaleMlp_eq_self_of_rank_D`: the statement is true without it.** It is proved (three standard axioms, check 7), and the reason is in the proof above: with positive `c`, `Q = 1` and `c = 1` come from the reads and the readout alone, and then each write row gives `s_{ℓ+1} = c_i^k = 1` and the embedding `s_0 = 1`, whatever the sign of `s`. *Computed:* on a grid (10 × 10 orthogonal matrices, 8 × 8 scales of both signs, 4 × 4 positive `c`, `k = 1`, `2`, two parameters with all hypotheses) the only fixing map is the identity. For the gated and ReGLU statements `s_ℓ > 0` is needed (table). So the Lean statement is slightly stronger than the paper's here: the pairs `(s, Q)` with `s < 0` are not symmetries (`N_0(h · sQ) = −N_0(h) Q`), and the statement says that none of them fixes `θ` either.

**General position is not needed for ReGLU blocks here: right.** *Reading and computed.* Without normalization the read columns of a ReGLU block are eigenvectors of `G_{ℓ−1}` with eigenvalues that are only known to be positive numbers (`1/c_i`, `c'_i`), and a diagonal `G_{ℓ−1} = diag(t, 1/t)` can fix a read of rank `d` (twenty-seventh audit). For `ε = 0` the matrix that acts on the read is the orthogonal `Q_{ℓ−1}⁻¹`, whose only positive eigenvalue is `1`: every gate column gives `c_i = 1` at once (`c_i > 0` is asked), then the write row gives `c'_i = 1/s_{ℓ+1} > 0` and the value column `c'_i = 1`. At the parameter where general position fails (gate columns `e_1, e_2`, value columns `e_2, e_1`) all hypotheses of the Lean statement hold, the family `diag(2, ½)` with `c = c' = (2, ½)` fixes it without normalization (recomputed), `diag(2, ½)` is not a multiple of an orthogonal matrix, and on a grid of 10 orthogonal `Q_0`, positive `s`, positive `c` and `c'` of both signs no map other than the identity fixes it. The same reasoning shows that for `ε > 0` (orthogonal changes of basis, `θ.cob G G`) general position is not needed either; the Lean twin `cob_rescale_rescaleGate_eq_self_of_rank_D` asks it because it is stated for all of `GL(d)`.

**Against the paper's proof.** "With RMSNorm the changes of basis lie in `CO(d_model)` or `O(d_model)`, and the argument is unchanged." With the embedding the argument is unchanged (`E G_0 = E` gives `G_0 = I`, and with it `Q_0 = I`). With the readout it changes in order and in what it uses, as the twenty-seventh audit said from the reader's reasoning and as the Lean proofs now show: the readout and the reads see only `Q_ℓ`; the rescalings do not act freely on the write rows by themselves (a row is multiplied by `s_ℓ / λ^k`); the read column comes first (an orthogonal matrix has no positive eigenvalue but 1); the scales `s_ℓ` are fixed last, by nonzero write rows and a nonzero embedding.

### 3. Attention with MLP blocks (`Symmetry/LocallyFreeTransformer.lean`): the paper's transformer is covered; "both parts fixed" is "the transformed parameter equals `θ`"; the rank hypothesis is the paper's for each kind of block

**The architecture.** *Reading.* `Arch.attentionMlp sees σ χ H dh hid` is `(Arch.attention sees χ H dh).sum (Arch.mlp σ χ hid)`, and `Arch.attentionGated` the same with `Arch.gated`. Block `ℓ` of `A.sum B` reads with `[W_read^A | W_read^B]`, applies the two fixed maps to the two parts, and writes with the two writes stacked: its output is the sum of the outputs of block `ℓ` of `A` and of `B` (`f_sum_mul`, proved). With `hid ℓ` empty it is the attention block (`f_sum_mul_of_isEmpty_right`), with `H ℓ` empty the MLP block (`f_sum_mul_of_isEmpty_left`). So the paper's networks "with attention blocks" and MLP blocks in any order (S Section 2: "A transformer layer has two blocks, its attention and MLP sub-layers"; D Lemma B.1: "a network whose blocks are tanh, GELU, ReLU, ReLU² or gated blocks […] or attention blocks") are the instances in which every block has one empty part, with widths that may differ from block to block. The sum also contains blocks with heads and hidden units side by side, which are not in the papers; the statements hold for them too. This is not the case of Remark A.19 ("heads of total width `H d_h < d_model` followed by an MLP block"), where the two are consecutive blocks with a hidden state between them: a Lean block that is an attention block alone with `H d_h < d` does not satisfy the rank hypothesis, as in the paper ("which the induction does not reach").

All MLP blocks of a network have one kind (`σ` and the kind of rescaling are the same in every block), as the Scope of S says ("all MLP blocks are of one kind"). tanh and GELU blocks are the statement for `rescaleMlp` at `c = 1`: *compiled* (`Chk28c.lean`) `θ.rescaleMlp k (fun _ _ => 1) = θ` and, from `cob_heads_rescaleMlp_eq_self_of_rank_E`, the form without rescalings (`θ.sumSnd.cob G G = θ.sumSnd` in place of `h2`; conclusion `G = 1 ∧ K = 1 ∧ K' = 1`). In this form the hypothesis "no read column of a hidden unit vanishes" stays, which the paper's argument does not need for tanh and GELU; it holds at almost every parameter.

**"Both parts of `θ` are fixed."** The Lean statements have two hypotheses,

```lean
(h1 : ((θ.sumFst.cob G G).headsQK K).headsVO K' = θ.sumFst)
(h2 : (θ.sumSnd.cob G G).rescaleMlp k c = θ.sumSnd)
```

where `θ.sumFst` and `θ.sumSnd` have the same `E` and `D` as `θ` and the read columns and write rows of the attention part, and of the MLP part. *Compiled* (`Chk28b.lean`, three standard axioms):

```lean
(θ.cob G K).sumFst = θ.sumFst.cob G K        -- by rfl
(θ.cob G K).sumSnd = θ.sumSnd.cob G K        -- by rfl
θ.sumFst = θ'.sumFst → θ.sumSnd = θ'.sumSnd → θ = θ'
```

and, for a parameter `θ'` of the whole network whose attention part is `((θ.sumFst.cob G Q).headsQK K).headsVO K'` and whose MLP part is `(θ.sumSnd.cob G Q).rescaleMlp k c` (the two have the same `E` and `D`, by `rfl`, so such a `θ'` exists and is unique): `θ' = θ ↔ h1 ∧ h2`. So the two hypotheses together say exactly that the action on the whole network (the changes of basis on all read columns and write rows, the symmetries inside the heads on the attention part, the rescalings on the MLP part) fixes `θ`. The library has no single map for this action on the sum; the statement with two parts is equivalent to one with such a map. That this action preserves the function of the sum network is not a Lean statement in these files (*reading:* it follows from `f_sum_mul` and the invariance of each part; the infinitesimal form is `InsideBlocks.sumInl`, `InsideBlocks.sumInr`).

**The rank hypothesis.** `hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d` is on the stacked write. *Compiled* (`Chk28b.lean`): for a block with no hidden unit the stacked write has the rank of the attention write, and for a block with no head the rank of the MLP write. So for the paper's blocks it is "the write, which stacks the `W_{O,i}`, […] has rank `d_model`" and "`W_write^ℓ` has rank `d_model`". At generic parameters (`LocallyFreeTransformerGeneric.lean`) it becomes `Fintype.card d ≤ Fintype.card (H ℓ) * Fintype.card (dh ℓ) + Fintype.card (hid ℓ)`: for an attention block `H d_h ≥ d`, for an MLP block `d_hidden ≥ d`, the papers' conditions; and `hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d` is `d_h ≤ d_model` (for a block with no head take `dh ℓ` empty; instance compiled in check 1). `hdIn` is D's "`d_in ≥ d_model`", S's "an embedding of rank `d_model`" at generic parameters. `[Nonempty d]` is asked where a rescaling or a scale is in the conclusion, as in the twins.

The other hypotheses (`hE`; `hQr`, `hVr`: the query and the value matrix of every head of rank `d_h`; `hcol`, `hv`, `hg`: the rescaled read columns nonzero) are those of the twins for one kind of block, which the twenty-seventh audit compared, here on the parts. For `ε = 0` the same `G`, `Q`, `s` act on both parts, with `hs`, `hQ`, `hG` as in check 2.

Verdict: the six statements are the third sentence of S Lemma A.18 and the attention case of D Lemma B.1 for a network with both kinds of block, for the whole group (LEAN STRONGER in the conclusion, as the twins), and they close the gap that the twenty-seventh audit named ("a network with both attention blocks and MLP blocks […] has the changes of basis alone").

### 4. Lemma A.2 (ii) (`Basic/RMSNormDeviation.lean`): SAME, in three statements; the paper's formula lacks two subscripts

The paper (LaTeX source, as the brief quotes it): "(ii) If `ε > 0` and `G = cQ`, then `‖N(hG) − N_ε(h)Q‖/‖N(h)‖ = (ε/(2r²)) |1 − c⁻²| + O(ε²)`, where `r² = ‖h‖²/d_model`"; proof: "`N_ε(h cQ) = c hQ/√(c²‖h‖²/d_model + ε)` and `N_ε(h)Q = hQ/√(‖h‖²/d_model + ε)` […] The expansion of the deviation is the Taylor expansion of `c√(r²+ε)/√(c²r²+ε) − 1` in `ε`."

```lean
theorem rmsRow_vecMul_smul_orthogonal {ε : ℝ} (hε : 0 < ε) (c : ℝ) {Q : Matrix d d ℝ}
    (hQ : Q ∈ Matrix.orthogonalGroup d ℝ) (v : d → ℝ) :
    rmsRow ε (v ᵥ* (c • Q))
      = (c * Real.sqrt ((v ⬝ᵥ v) / (Fintype.card d : ℝ) + ε)
          / Real.sqrt (c ^ 2 * ((v ⬝ᵥ v) / (Fintype.card d : ℝ)) + ε)) • (rmsRow ε v ᵥ* Q)

theorem sqrt_dotProduct_rmsRow_vecMul_smul_orthogonal_sub … :
    Real.sqrt ((rmsRow ε (v ᵥ* (c • Q)) - rmsRow ε v ᵥ* Q) ⬝ᵥ (rmsRow ε (v ᵥ* (c • Q)) - rmsRow ε v ᵥ* Q))
      = |c * Real.sqrt (… + ε) / Real.sqrt (c ^ 2 * … + ε) - 1| * Real.sqrt (rmsRow ε v ⬝ᵥ rmsRow ε v)

theorem abs_rmsNorm_deviation_sub_isBigO {r2 c : ℝ} (hr : 0 < r2) (hc : 0 < c) :
    (fun ε : ℝ => |c * Real.sqrt (r2 + ε) / Real.sqrt (c ^ 2 * r2 + ε) - 1|
        - ε / (2 * r2) * |1 - (c ^ 2)⁻¹|) =O[𝓝[>] 0] fun ε : ℝ => ε ^ 2
```

*Reading.*

- `rmsRow ε v = (√((v ⬝ᵥ v)/d + ε))⁻¹ • v` is the paper's `N_ε` on a row, and `(v ⬝ᵥ v)/d` its `r²`. The first statement is the two displayed formulas of the proof, divided: `N_ε(v cQ) = k · N_ε(v) Q` with `k = c√(r²+ε)/√(c²r²+ε)`. It holds for every real `c` (for `c ≤ 0` too) and every row, `v = 0` included.
- The second is the left side of (ii) with the norm written as `√(w ⬝ᵥ w)`, the Euclidean norm of a row, which is the paper's (`r² = ‖h‖²/d_model`). The paper divides by `‖N(h)‖`; Lean multiplies, so the statement also holds at `v = 0`. For `v ≠ 0` the two are the same.
- The third is the expansion of `|k − 1|`: `=O[𝓝[>] 0]` is "as `ε → 0` from above", for fixed `r² > 0` and `c > 0`; the constant may depend on `r²` and `c`. Together the three give (ii) for a row `h ≠ 0`.

**Is "`O(ε²)` for fixed `h` and `c`" what the paper means?** Yes, and it cannot mean more. The paper names `r² = ‖h‖²/d_model` in the statement and expands "in `ε`", so `h` and `c` are fixed. *Computed* (`c4_dev.py`, 60 digits): the remainder is not uniform in `h`: at `ε = 10⁻³`, `c = 2`, the deviation `|k − 1|` is `0.00037`, `0.036`, `0.77`, `0.99997` for `r² = 1, 10⁻², 10⁻⁴, 10⁻⁸` (it tends to `|c − 1|` as `h → 0`). The expansion is in `ε/r²`: the private helper of the file bounds the remainder by `|c² − 1|(3 + c²)/(8 c⁴ r⁴) · ε²`, and this constant is the exact second-order coefficient (computed: the quotient of the remainder by `ε²` tends to `−0.0280916` for `c = 2`, `−0.834721` for `c = ½`, `−0.0253666` for `c = 3`, at `r² = 29/12`; the helper's constants are `0.0280916`, `0.834721`, `0.0253666`). The public statement does not say the constant.

**Recomputed** (`c4_dev.py`): (a) the exact relation and the deviation at a rotation of `ℝ³` with rational entries, `c ∈ {2, ½, −3/2, 0, 1, −1, 7}`, `ε ∈ {1, 0.1, 0.001, 25}`: errors below `10⁻⁶⁰`. (b) From above, the remainder divided by `ε²` converges (values above); **from below it fails at first order**: the remainder divided by `ε` tends to `−|1 − c⁻²|/r²` (`−0.3103` for `c = 2`, `−1.2414` for `c = ½`, `−0.3678` for `c = 3`), because `|k − 1| ≈ |ε| |1 − c⁻²|/(2r²)` while the term of the statement changes sign with `ε`. So `𝓝[>] 0` is needed, and it is the paper's hypothesis "`ε > 0`". For `c = 1` both sides vanish. (c) `c > 0` is needed for the expansion: for `c = −2` the deviation is about `2` (then the paper's `Q` is `−Q`). The exact relation and the deviation formula do not need it.

**The two `N` without a subscript.** The paper's (ii) has `N(hG)` and `N(h)` where the proof has `N_ε`. Lean reads both as `N_ε` (header and index say so). *Computed:* this is the only reading that gives the paper's right side: with `N = N_0` the left side is `ε/(2r²) + O(ε²)` for every `c` (`2.0689 · 10⁻⁵` at `ε = 10⁻⁴` for `c = 2` and for `c = ½`, against the paper's `1.5517 · 10⁻⁵` and `6.2069 · 10⁻⁵`). The paper's formula should carry the subscripts (list for the authors).

Verdict: SAME as Lemma A.2 (ii), with the expansion stated for the scalar factor and the two exact identities that tie it to the rows.

### 5. From both ends (`Dimension/UpperBoundTwoSided.lean`): true; the hypotheses are sufficient, and each is needed at some parameter; the proof of Proposition A.35 needs this form when the block of the dead unit has exactly `d` units

```lean
theorem cobDir_injective_of_rank_E_D {A : Arch T d L} (θ : Params A dIn dOut) (m : Fin L)
    (hE : θ.E.rank = Fintype.card d) (hD : θ.D.rank = Fintype.card d)
    (hw : ∀ ℓ, ℓ < m → (θ.write ℓ).rank = Fintype.card d)
    (hr : ∀ ℓ, m < ℓ → (θ.read ℓ).rank = Fintype.card d) :
    Function.Injective (cobDir θ)

theorem cobDir_add_rescaleDirMlp_injective_of_rank_E_D (k : ℕ) (hk : k ≠ 0)
    (θ : Params (Arch.mlp (T := T) (d := d) σ χ hid) dIn dOut) (m : Fin L) … (hE) (hD) (hw) (hr)
    (hc : ∀ ℓ, ℓ ≤ m → ∀ i, (fun a => θ.read ℓ a i) ≠ 0)
    (ha : ∀ ℓ, m < ℓ → ∀ i, (fun a => θ.write ℓ i a) ≠ 0) :
    Function.Injective fun p : (Fin (L + 1) → Matrix d d ℝ) × (∀ ℓ, hid ℓ → ℝ) =>
      cobDir θ p.1 + rescaleDirMlp k θ p.2
```

*Reading.* `cobDir θ X` is `E X_0`, `−X_ℓ W_read^ℓ`, `W_write^ℓ X_{ℓ+1}`, `−X_L D`, and `rescaleDirMlp k θ α` multiplies a read column by `α` and its write row by `−kα`: the derivatives of the actions (twenty-seventh audit, check 6). The statement is the infinitesimal form of the paper's two inductions, joined at block `m`: the hidden states `h_0, …, h_m` (up to the one block `m` reads) from the embedding, `h_{m+1}, …, h_L` from the readout. Nothing is asked of the read rank or the write of block `m`, nor of the reads before it or the writes after it. This is what the paper's lemma would say for a network in which one block is narrower than `d_model` and both `E` and `D` have rank `d_model`; the paper does not state it. With `m` the last block it asks, beside the hypotheses of the form with the embedding, that `D` has rank `d`, which that form does not; with `m` the first block the same for `E`. The header says so ("close to").

*Computed* (`c5_twosided.py`, the reader's own; the map written as a matrix, exact ranks over the rationals with python-flint; random integer parameters; the hypotheses checked exactly at every draw; under one second).

- **True at every draw at which the hypotheses hold:** 27 draws (`d = 2, 3, 4`; widths such as `(3,2,3)`, `(4,1,5)`, `(2,1,2,3)`, `(4,5,3,4)` with one narrow block between wide ones; a narrow last block `(3,2)`, `(4,3,1)` with `d_out ≥ d`; a narrow first block `(2,3)` with `d_in ≥ d`): the rank is the number of unknowns for `cobDir` alone and with the rescalings for `k = 1` and `k = 2`.
- **A narrow last block with `d_out < d`:** not injective. `d = 3`, widths `(3,2)`: kernel of dimension 1 for `d_out = 2` and 2 for `d_out = 1`, that is `(d − d_hidden)(d − d_out)`: the hidden state `h_L` is written at rank 2 and read at rank `d_out`. With a wide block after the narrow one (`(3,2,3)`, `d_out = 1`) the map is injective although `D` has rank 1: the hypothesis `hD` is sufficient, not necessary.
- **A narrow first block with `d_in < d`:** kernel of dimension 1 (`d = 3`, `d_in = 2`, widths `(2,3)`); with a wide first block (`(3,2,3)`, `d_in = 2`) injective.
- **Two adjacent narrow blocks:** not injective: kernel 1 for widths `(2,2,3)` and `(3,2,2,3)`, kernel 4 for `(3,1,1,3)` at two of three draws (`d = 3`): `(d − m)²` at the hidden state between them, as Remark A.19 says. Two narrow blocks that are not adjacent (`(2,3,2)`): injective at the draws with `E` of rank `d`, though the statement does not cover it (the state between a narrow block and a wide one is written or read at rank `d`).
- **Each hypothesis is needed at some parameter** (designed parameters, `d = 2`): `E` of rank 1 with a first block of width 1: kernel 1; `D` of rank 1 with a last block of width 1: kernel 1; a write before `m` of rank 1 followed by block `m` of width 1: kernel 1; a read after `m` of rank 1 behind block `m` of width 1: kernel 1; a unit of a block up to `m` with a zero read column and a zero write row: kernel 1 (with a nonzero write row: injective); a unit of a block after `m` with a zero write row and a zero read column: kernel 1 (with a nonzero read column: injective); `k = 0`: kernel 1 at parameters where all other hypotheses hold (block 1 of width 1 writes `(1,1)` and a unit of block 2 reads `(1,−1)^⊤`), and the same parameters are injective for `k = 1`.

So the hypotheses are a sufficient set that follows the two inductions; `hc` and `ha` could be "the read column or the write row is not zero", as the twenty-seventh audit found for the twins. The coordinator's script (`ai_notes/locally_free_one_narrow_block_check_2026-11-25.py`) gives the same ranks where the cases coincide (44 of 44, 32 of 32, 30 of 32, 42 of 43, 54 of 55).

**What it says about the proofs of Proposition A.33 (ii) and A.35.**

- **A.35 (skipless).** The proof: "The other columns are those of the network without this unit, whose symmetries are the changes of basis of its `L + 1` hidden states and `s − 1` rescalings". The bound follows only if these symmetries move the parameters of that network in `(L + 1) d² + s − 1` independent directions, which is Lemma A.18 for a network whose block 2 has `d_hidden − 1` units. For `d_hidden > d_model` the lemma applies as stated (D Proposition E.1 asks "more than `d_model` hidden units" and says "its blocks have at least `d_model` hidden units"). For `d_hidden = d_model`, which the Scope allows ("`d_hidden ≥ d_model`") and the sentence before the proposition claims ("at every width"), neither sentence of the lemma applies; the form from both ends gives the count when `E` and `D` both have rank `d` (*computed:* widths `(d, d−1)` and `(d, d−1, d)`, `d = 2, 3`, `d_in = d_out = d`: injective at the 9 draws with the hypotheses). When block 2 is the last block and `d_out < d` the count is short by `d − d_out` (widths `(2,1)`, `d_out = 1`: rank 14 of 15), and check 6 shows that the bound of the proposition then fails.
- **A.33 (ii) (residual).** Here the form from both ends is not needed. In a residual network there is one change of basis for all hidden states, the embedding of rank `d` fixes it, and the rescalings are then fixed by nonzero read columns; the width of the blocks is not used. This is the paper's own reason ("At generic parameters they act with orbits of dimension `d_model² + s − ν`, since `E` has rank `d_model`"). The Lean statement of A.33 (ii) already has this form: `funDim_add_le_residual_of_eventually_unitInactive` (`Residual/DeadUnits.lean`) asks `E` of rank `d` and no zero read column, and no width. *Computed:* the map `(X, α) ↦ cobDir θ (X, …, X) + rescaleDirMlp k θ α` has rank `d² + s` at widths `(1,1,1)` and `(3,2,1)`, `d = 3`, `k = 1, 2`. The header of the Lean file names both propositions as users of the lemma "for the network without a dead unit"; for A.33 (ii) the remark applies only to the wording of Lemma A.18 ("every block has width at least `d_model`" is asked there for residual networks too, where the proof does not use it).

### 6. Proposition A.35 for width at least `d` (`Depth/InactiveUnitTwoSided.lean`): SAME as the paper within its Scope; `d_out ≥ d` is needed for the open set of the proof, and without it the bound of the paper fails there

```lean
theorem funDim_add_le_of_eventually_unitInactive_of_rank_E_D … {k : ℕ} (hk : k ≠ 0)
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z) (hσ0 : ∀ z : ℝ, z ≤ 0 → σ z = 0)
    (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) (m : Fin L) (j : hid m)
    (hθ : ∀ᶠ θ' in 𝓝 θ, UnitInactive θ' m j)
    (hE : θ.E.rank = Fintype.card d) (hD : θ.D.rank = Fintype.card d)
    (hw : ∀ ℓ, ℓ < m → (θ.write ℓ).rank = Fintype.card d)
    (hr : ∀ ℓ, m < ℓ → (θ.read ℓ).rank = Fintype.card d)
    (hc : ∀ ℓ, ℓ ≤ m → ∀ i, (fun a => θ.read ℓ a i) ≠ 0)
    (ha : ∀ ℓ, m < ℓ → ∀ i, (fun a => θ.write ℓ i a) ≠ 0) :
    funDim (Arch.mlp σ id hid) 0 θ
        + ((L + 1) * Fintype.card d ^ 2 + ∑ ℓ, Fintype.card (hid ℓ) + (2 * Fintype.card d - 1))
      ≤ Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)

theorem exists_isOpen_unitInactive_relu_of_le [Nonempty d] (μ : …) [μ.IsAddHaarMeasure]
    (hdIn : Fintype.card d ≤ Fintype.card dIn) (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hhid : ∀ m, Fintype.card d ≤ Fintype.card (hid m)) (ℓ : Fin L) (j : hid ℓ.succ) :
    ∃ U : Set (Params …), IsOpen U ∧ U.Nonempty ∧ (∀ θ ∈ U, UnitInactive θ ℓ.succ j) ∧
      ∀ᵐ θ ∂μ, θ ∈ U → funDim (Arch.mlp relu id hid) 0 θ
          + ((L + 2) * Fintype.card d ^ 2 + ∑ m, Fintype.card (hid m) + (2 * Fintype.card d - 1))
        ≤ Module.finrank ℝ (Params …)

theorem not_ae_funDim_add_eq_relu_skipless_of_le [Nonempty d] (μ : …) [μ.IsAddHaarMeasure]
    (hL : 0 < L) (hdIn) (hdOut) (hhid) :
    ¬ ∀ᵐ θ ∂μ, funDim (Arch.mlp relu id hid) 0 θ
        + ((L + 2) * Fintype.card d ^ 2 + ∑ m, Fintype.card (hid m)) = Module.finrank ℝ (Params …)
```

**What the Lean statements ask and give, against the two papers.** *Reading.*

| | S Proposition A.35 | D Proposition E.1 | Lean, this file |
|---|---|---|---|
| blocks | `L ≥ 2` ReLU, ReLU² or ReGLU, skipless, no normalization | the same | ReLU and ReLU² (`Arch.mlp relu id hid`, `reluSq`), skipless (`funDim … 0`), blocks `Fin (L + 1)` with `ℓ : Fin L`, so at least two |
| width | none named ("at every width" in the sentence before; the Scope of the main text: `d_hidden ≥ d_model`) | "each with more than `d_model` hidden units" | at least `d` in every block (`hhid`) |
| `d_in`, `d_out` | none named (Scope: `d_in, d_out ≥ d_model ≥ 2`) | none named | `d_in ≥ d`, `d_out ≥ d`, `d ≥ 1` |
| the dead unit | "a unit of block 2" | "a hidden unit of block 2" | every unit `j` of every block `ℓ.succ` after the first |
| the set | "a nonempty open set of weights on which a unit of block 2 is dead" | the same | `∃ U`, open, nonempty, `UnitInactive θ ℓ.succ j` on `U` (the unit reads a number `≤ 0` at every token of every input) |
| the bound | "On it" at most `P − (L+1) d² − s − (2d − 1)` | "At almost every point of this set" | at almost every point of `U`, every Haar measure; `(L + 2) d²` for the `L + 2` hidden states of `L + 1` blocks; `s = ∑ d_hidden`; for Lean's `funDim`, which is at least the paper's functional dimension |
| the consequence | "so the equality condition fails there" | "So these networks do not satisfy the equality condition" | not `fd = P − (L+2) d² − s` at almost every parameter, for `L ≥ 1` |

The twins `exists_isOpen_unitInactive_relu`, `…_reluSq` (`Depth/InactiveUnitRelu.lean`) ask `d_in ≥ d`, at least `d` units in every block and **more than `d` in the block of the dead unit**, and nothing of `d_out`. The new statements put `d_out ≥ d` in the place of "more than `d`". The two together are: the bound holds if the block of the dead unit has more than `d` units, or exactly `d` and `d_out ≥ d`. Within the Scope of S (`d_hidden ≥ d_model`, `d_in, d_out ≥ d_model`) the new statements are Proposition A.35 for ReLU and ReLU² blocks, at almost every point of the set in place of "On it". The statement at one parameter gives the paper's `L` blocks and `(L + 1) d²` directly (`m : Fin L`, any block, also the first if a unit is inactive there).

**`d_out ≥ d` is needed.** *Computed* (`c6_dead.py`, the reader's own: one token, the chain rule written out, integer weights and integer inputs, so the Jacobian is exact; rank over the rationals with python-flint; an input is kept only if the dead unit reads a negative number and no other pre-activation vanishes; under 5 seconds). The rank on a batch is a lower bound for the functional dimension (the paper's and Lean's), so a rank above the bound refutes the bound.

An explicit parameter: `d = d_in = 2`, two ReLU blocks of width 2, `E = 1`, `W_read^1 = 1`, `W_write^1 = [[−1, 1], [−1, 2]]`, `W_read^2 = 1`, `W_write^2 = [[1, 1], [1, 2]]`. Unit 1 of block 2 reads `−ReLU(x_1) − ReLU(x_2) ≤ 0`: it is dead, and stays dead at all weights near these (`a_k r = −1 < 0` for both units of block 1: the set `negReadSet` of the Lean proof, the set of the paper's proof).

| readout | `P` | bound `P − 3·4 − 4 − 3` | exact rank on 130 inputs |
|---|---|---|---|
| `d_out = 2`, `D = 1` | 24 | 5 | 5 |
| `d_out = 1`, `D = (1, 1)^⊤` | 22 | 3 | **4** |
| `d_out = 1`, ReLU² | 22 | 3 | **4** |
| `d_out = 1`, a third block of width 2 behind | 30 | 5 | 4 |

With `d_out = 1` the network is `x ↦ c · ReLU(q_1 ReLU(x p_1) + q_2 ReLU(x p_2))`: seven numbers and three rescalings, functional dimension 4. At this parameter every hypothesis of `funDim_add_le_of_eventually_unitInactive_of_rank_E_D` holds except `hD` (`E` and the write of block 1 have rank 2, no read column is zero, the unit is inactive at all nearby parameters), and its conclusion `funDim ≤ 3` fails: **`hD` is needed in the statement at one parameter.** The rank is lower semicontinuous on the batch, so the bound fails on an open subset of `negReadSet`, not only at one point.

Random integer weights in the same set (four draws each; many draws have other dead units and a small rank; the largest rank is shown):

| `d`, `d_in`, `d_out`, widths | bound | largest rank | |
|---|---|---|---|
| 2, 2, 2, (2,2); 2, 2, 3, (2,2) | 5; 7 | 5; 6 | holds |
| 3, 3, 3, (3,3); 3, 4, 4, (4,3) | 16; 27 | 16; 25 | holds |
| 2, 2, 1, (2,2) | 3 | **4** | exceeded by `d − d_out = 1` |
| 3, 3, 2, (3,3) | 13 | **14** | exceeded by 1 |
| 3, 3, 1, (3,3) | 10 | **12** | exceeded by 2 |
| 2, 2, 1, (2,2), ReLU²; 3, 3, 2, (3,3), ReLU² | 3; 13 | **4**; **14** | exceeded by 1 |
| 2, 2, 1, (2,3); 3, 3, 1, (3,4): more than `d` units (D E.1) | 6; 15 | 4; 14 | holds |
| 2, 2, 1, (2,2,2); 3, 3, 1, (3,3,3): a third block behind | 5; 16 | 4; 8 | holds |
| 2, 1, 2, (2,2); 3, 2, 3, (3,3); 3, 1, 3, (3,3): `d_in < d` | 3; 13; 10 | 2; 11; 4 | holds |

So the bound was exceeded only in the case that check 5 predicts: the dead unit sits in the **last** block, this block has exactly `d` units, and `d_out < d`. Then the hidden state `h_L` of the network without the dead unit is written at rank `d − 1` and read at rank `d_out`, and its changes of basis move the parameters in `d − d_out` fewer directions. With both blocks of width exactly `d` the rank exceeds the bound by `d − d_out` (rows above; again at 12 draws for `d = 3`, `d_out = 2`: largest rank 14 against 13). With a first block wider than `d` the excess is smaller or absent (`c6_more.py`, 12 draws each): widths `(4,3)`, `d = 3`: largest rank 16 against the bound 15 for `d_out = 1`, and 18 against 18 for `d_out = 2`; widths `(5,3)`, `d_out = 1`: 20 against 20; widths `(3,2)`, `d = 2`, `d_out = 1`: 6 against 6. (A reason, by the reader's count for two blocks: the last block then reads `h_1` at rank `d − 1`, so each unit of block 1 beyond `d` has a write direction that nothing reads, and the excess is `(d − d_out) − (d_hidden^1 − d)` when this is positive.) With more than `d` units in the block of the dead unit (the twins, D Proposition E.1) or with a further block of width at least `d` behind it, no condition on `d_out` was found to be needed. `d_in ≥ d` was not found to be needed either (the bound holds at the draws with `d_in < d`), which agrees with check 5 (a wide first block reads `h_0` at rank `d`); Lean asks it, as the Scope does.

**The form of the statement: an existence statement.** The two `exists_isOpen_…_of_le` statements say that *some* nonempty open set with a dead unit has the bound almost everywhere; they do not say which. The proof takes `negReadSet`. Read literally, the existence statement is weaker than what is proved and holds for another reason too: on the open set where all units of block `ℓ.succ` read negative numbers the network is identically zero, the functional dimension is 0 (*computed:* rank 0 at two such parameters), and `0 ≤ P − (L+2) d² − s − (2d − 1)` for `d_in, d_out ≥ 1`. So `hdOut` is needed for the bound on `negReadSet` (above), not for the truth of the existence statement as written. The paper's sentence has the same form ("There is a nonempty open set of weights on which a unit of block 2 is dead. On it …"), and so have the twins; the content is in the statement at one parameter and in the choice of the set, which the docstrings, the header and the index name. Nothing is false; the index row should say that `negReadSet` is the set of the proof (corrections).

**The blocks `Fin (L + 1)` and "`L ≥ 2`".** A network with the blocks `Fin (L + 1)` has `L + 1 ≥ 2` blocks exactly when a block `ℓ.succ` with `ℓ : Fin L` exists; the two `exists_` statements take such an `ℓ` (so `L ≥ 1` is implied) and the two `not_ae_` statements ask `hL : 0 < L`. The paper's block 1 and block 2 are `ℓ.castSucc` and `ℓ.succ` for `ℓ = 0`; Lean has every `ℓ`. The count `(L + 2) d²` is the paper's `(L + 1) d_model²` for its `L = ` Lean's `L + 1`. *Compiled* (check 1): the instance with two blocks, `d = 2`, `P = 24`, `funDim + 19 ≤ 24`, the bound 5 of the first row of the table above, where the exact rank is 5: the bound is attained there.

Verdict: SAME as S Proposition A.35 for ReLU and ReLU² blocks under the Scope, with "almost every point" for "On it" (as D E.1); LEAN STRONGER than D E.1 in the width (exactly `d` allowed) at the price of `d_out ≥ d`, which is needed.

### 7. The index rows: true of the statements, with four corrections; all 36 theorems registered

*Reading and a script* (the index and `checks/Axioms.lean` as committed at `d67195b`, the latest commit when this check was made; copies in `/home/claude/audit28/`). Each of the 36 public names of the seven files stands in exactly one row, the row of its file, with the status "proved"; each has its line `#print axioms Skips.<name>` in `checks/Axioms.lean`. *Compiled* (`Ax28.lean`): the 36 have the three standard axioms.

Row by row:

- `Basic/RMSNormDeviation.lean`: true of the three statements (the exact relation for every real `c`; the deviation with norms as square roots of dot products; the expansion from above for `r² > 0`, `c > 0`; "from below the two sides differ at first order": recomputed in check 4; the two `N` read as `N_ε`).
- `Symmetry/LocallyFreeRMSZero.lean`: true (the group, the action `θ.cob G Q`, the hypotheses of both forms, "the read columns are not asked in general position", "`s_ℓ > 0` is not asked" for ReLU and ReLU² with the readout).
- `Symmetry/LocallyFreeRMSZeroGeneric.lean`: true (the widths and `d_in ≥ 1` for the readout forms).
- `Symmetry/LocallyFreeTransformer.lean`: true; the status is "proved" since `8c3879f`.
- `Symmetry/LocallyFreeTransformerGeneric.lean`: the sentence "they rest on the statements at one parameter, in work" is out of date (correction 1).
- `Dimension/UpperBoundTwoSided.lean`: true of the two statements; "used by the proofs of S Proposition A.33 (ii) and A.35" says more than check 5 found for A.33 (ii) (correction 2).
- `Depth/InactiveUnitTwoSided.lean`: true; "the nonempty open set `negReadSet` and the bound at almost every point of it" describes the proof, the statement says that an open set exists (correction 3).
- The paragraph "Not yet compared by such a reader (they go to the twenty-eighth audit)" is now out of date for the seven files (correction 4).

## Part 2: the statements, file by file

| File | Name | Paper | Verdict |
|---|---|---|---|
| `Symmetry/LocallyFreeRMSZero.lean` | `cob_rmsNorm_zero_rescaleMlp_eq_self_of_rank_E` | S A.18 first sentence / D B.1, pre-RMSNorm with `ε = 0`, ReLU and ReLU² | LEAN STRONGER |
| | `cob_rmsNorm_zero_rescale_eq_self_of_rank_E` | the same, gated blocks | LEAN STRONGER |
| | `cob_rmsNorm_zero_rescale_rescaleGate_eq_self_of_rank_E` | the same, ReGLU | LEAN STRONGER |
| | `cob_rmsNorm_zero_headsQK_headsVO_eq_self_of_rank_E` | S A.18 third sentence / D B.1, `ε = 0`, attention blocks | LEAN STRONGER; PART (attention blocks only; with MLP blocks: the next file) |
| | `cob_rmsNorm_zero_rescaleMlp_eq_self_of_rank_D` | S A.18 second sentence, `ε = 0`, ReLU and ReLU² | LEAN STRONGER (also `s_ℓ` of any sign); with `E ≠ 0` and nonzero write rows, which the paper does not write |
| | `cob_rmsNorm_zero_rescale_eq_self_of_rank_D` | the same, gated blocks | LEAN STRONGER (any real `c`) |
| | `cob_rmsNorm_zero_rescale_rescaleGate_eq_self_of_rank_D` | the same, ReGLU | LEAN STRONGER; no general position, rightly |
| `Symmetry/LocallyFreeRMSZeroGeneric.lean` | three `ae_…_of_dIn`, `ae_cob_rmsNorm_zero_headsQK_headsVO_eq_self_of_dIn` | D B.1; S A.18 first and third sentence, `ε = 0`, at generic parameters | SAME (LEAN STRONGER in the conclusion) |
| | three `ae_…_of_dOut` | S A.18 second sentence, `ε = 0`, at generic parameters | SAME (LEAN STRONGER in the conclusion); `d_in ≥ 1` is asked and needed |
| `Symmetry/LocallyFreeTransformer.lean` | `cob_heads_rescaleMlp_eq_self_of_rank_E`, `cob_heads_rescale_eq_self_of_rank_E`, `cob_heads_rescale_rescaleGate_eq_self_of_rank_E` | S A.18 third sentence / D B.1 for a network with attention blocks and MLP blocks | LEAN STRONGER (the group; every `θ` with the rank conditions; blocks with both parts) |
| | the three `cob_rmsNorm_zero_heads_…_of_rank_E` | the same for `ε = 0` | LEAN STRONGER |
| `Symmetry/LocallyFreeTransformerGeneric.lean` | six `ae_cob_…heads…_of_dIn` | the same at generic parameters (`d_in ≥ d`, `d_h ≤ d`, `H d_h ≥ d` or `d_hidden ≥ d` per block) | SAME (LEAN STRONGER in the conclusion) |
| `Basic/RMSNormDeviation.lean` | `rmsRow_vecMul_smul_orthogonal` | S A.2, proof, "`N_ε(h cQ) = …` and `N_ε(h)Q = …`" | SAME (every real `c`) |
| | `sqrt_dotProduct_rmsRow_vecMul_smul_orthogonal_sub` | S A.2 (ii), the left side | SAME (a product in place of the quotient) |
| | `abs_rmsNorm_deviation_sub_isBigO` | S A.2 (ii), the expansion | SAME (`ε → 0` from above, fixed `r² > 0`, `c > 0`) |
| `Dimension/UpperBoundTwoSided.lean` | `cobDir_injective_of_rank_E_D`, `cobDir_add_rescaleDirMlp_injective_of_rank_E_D` | not a sentence of the paper: Lemma A.18 for one narrow block, as the proof of A.35 needs it for `d_hidden = d_model` | true; SAME as the use made of it |
| `Depth/InactiveUnitTwoSided.lean` | `funDim_add_le_of_eventually_unitInactive_of_rank_E_D` | S A.35, proof, "The rank", at one parameter | SAME, with the conditions written out; any block `m`, any degree `k ≠ 0` |
| | `exists_isOpen_unitInactive_relu_of_le`, `exists_isOpen_unitInactive_reluSq_of_le` | S A.35 for ReLU and ReLU², under the Scope | SAME, with "almost every point" for "On it"; PART (ReGLU is not in this file) |
| | `not_ae_funDim_add_eq_relu_skipless_of_le`, `not_ae_funDim_add_eq_reluSq_skipless_of_le` | "so the equality condition fails there" | SAME |

Notes.

- LEAN STRONGER in the rows of the group statements means, as in the twenty-seventh audit: the statement holds at every parameter with the rank conditions, not only at generic ones, and for every element of the group (`CO(d)` at every hidden state, `GL(d_h)` in every head, every real or every positive rescaling), not only near the identity.
- No statement of the seven files is vacuous: the hypotheses of the statements at one parameter hold at almost every parameter (the `ae_` statements are proved from them, and instances are compiled in check 1), and exact parameters with all hypotheses are in `c2_zero.py`, `c5_twosided.py` and `c6_dead.py`.
- The third sentence of A.18 has no form with the readout for attention blocks, in the paper or in Lean (the header and the index say so).

## Part 3: the "Not stated" notes of the index

*Reading and searching* (the index as committed at `d67195b`; a script lists every occurrence of "Not stated": 49, of which 45 stand in rows and 4 in the running text). For each note the index was searched for a row that states the thing (by the words of the note and by the names of the files in `SkipsLean/`), and for each file named below it was checked that it exists at `d67195b` and has no `sorry`. The Lean statements of those other files were not read: a note is called out of date when a row of the index says that the thing is stated.

**Result:** 19 notes are out of date, 21 are still true, 9 are of the form "Not stated here" and name the files that have the thing (all nine files exist).

### Out of date (19): the row that states the thing, and the words to put in place of the note

| Row (file) | The note now | Stated in | Words to put in its place |
|---|---|---|---|
| `Dimension/LocalIdentifiability.lean` | "Not stated: the converse direction of Proposition 4.6 and attention blocks (SwiGLU and GeGLU blocks: `Dimension/LocalIdentifiabilityGated.lean`)" | `Dimension/IdentifiableConverse.lean`, `Dimension/IdentifiableConverseCob.lean`, `Dimension/IdentifiableIff.lean`; `Dimension/LocalIdentifiabilityAttention.lean` | "Not stated here: the converse direction of Proposition 4.6 (`Dimension/IdentifiableConverse.lean`, `Dimension/IdentifiableConverseCob.lean`; the equivalence: `Dimension/IdentifiableIff.lean`); attention blocks (`Dimension/LocalIdentifiabilityAttention.lean`); SwiGLU and GeGLU blocks (`Dimension/LocalIdentifiabilityGated.lean`)" |
| `Residual/LocalIdentifiability.lean` | "Not stated: the converse direction, attention blocks, `ε = 0`" | `Residual/IdentifiableIff.lean`; `Dimension/LocalIdentifiabilityAttention.lean`, `Residual/LocalIdentifiabilityAttentionRMS.lean`, `Residual/LocalIdentifiabilityTransformer.lean` | "Not stated here: the converse direction (the equivalence: `Residual/IdentifiableIff.lean`); attention blocks (`Dimension/LocalIdentifiabilityAttention.lean`, `Residual/LocalIdentifiabilityAttentionRMS.lean`; with MLP blocks: `Residual/LocalIdentifiabilityTransformer.lean`). Not stated: `ε = 0`" |
| `Residual/ExactGain.lean` | "Not stated as a statement of its own: "by exactly `L dim 𝒢` when the skipless network satisfies the equality condition too" (its instances are Corollary 4.8)" | `Residual/GainUnderEquality.lean`, `Residual/ExactGainAttention.lean`, `Residual/ExactGainTransformer.lean` | ""By exactly `L dim 𝒢` when the skipless network satisfies the equality condition too" as a conditional statement: `Residual/GainUnderEquality.lean` (any architecture), `Residual/ExactGainAttention.lean`, `Residual/ExactGainTransformer.lean`; its instances here are Corollary 4.8" |
| `Residual/DifferentClasses.lean` | "Not stated: attention blocks; "cannot be locally uniformly approximated" (… the step is not a Lean statement)" | `Residual/DifferentClassesAttention.lean`, `Residual/DifferentClassesTransformer.lean`; `Residual/LocallyUniform.lean` | "Not stated here: attention blocks (`Residual/DifferentClassesAttention.lean`; with MLP blocks: `Residual/DifferentClassesTransformer.lean`); "cannot be locally uniformly approximated" (`Residual/LocallyUniform.lean`)" |
| `Residual/DepthAttentionDim.lean` | "Not stated: networks that mix attention and MLP blocks (pre-RMSNorm: `Residual/DepthAttentionRMSDim.lean`)" | `Residual/DepthTransformer.lean` | "Not stated here: networks of attention blocks and MLP blocks (`Residual/DepthTransformer.lean`); pre-RMSNorm (`Residual/DepthAttentionRMSDim.lean`)" |
| `Residual/DepthAttentionRMSDim.lean` | "Not stated: networks that mix attention and MLP blocks" | `Residual/DepthTransformerRMS.lean` | "Not stated here: networks of attention blocks and MLP blocks (`Residual/DepthTransformerRMS.lean`)" |
| `Dimension/LocalIdentifiabilityAttention.lean` | "Not stated: the converse direction (pre-RMSNorm: `Residual/LocalIdentifiabilityAttentionRMS.lean`)" | `Dimension/IdentifiableIff.lean`, `Residual/IdentifiableIff.lean` | "Not stated here: the converse direction (the equivalences: `Dimension/IdentifiableIff.lean`, `Residual/IdentifiableIff.lean`); pre-RMSNorm (`Residual/LocalIdentifiabilityAttentionRMS.lean`)" |
| `Residual/LocalIdentifiabilityAttentionRMS.lean` | "Not stated: the converse direction; `ε = 0`" | `Dimension/IdentifiableIff.lean`, `Residual/IdentifiableIff.lean` | "Not stated here: the converse direction (the equivalences: `Dimension/IdentifiableIff.lean`, `Residual/IdentifiableIff.lean`). Not stated: `ε = 0`" |
| `Residual/LearnedSkipsConformal.lean` | "Not stated: the converse" | `Residual/LearnedSkipsConverse.lean` | "The converse: the row of `Residual/LearnedSkipsConverse.lean`" |
| `OneBlock/LearnedSkipRescale.lean` | "Not stated: the upper triangular skip; `ε = 0`" | `OneBlock/LearnedSkipTriangularRescale.lean`; `OneBlock/LearnedSkipRMSZeroRescale.lean`, `OneBlock/LearnedSkipRMSZeroRescaleGeneric.lean`, `OneBlock/LearnedSkipTriangularRMSZeroRescale.lean` | "Not stated here: the upper triangular skip (`OneBlock/LearnedSkipTriangularRescale.lean`); `ε = 0` (`OneBlock/LearnedSkipRMSZeroRescale.lean`, `OneBlock/LearnedSkipRMSZeroRescaleGeneric.lean`; triangular: `OneBlock/LearnedSkipTriangularRMSZeroRescale.lean`)." (with the full stop that is missing before "The statements at one parameter") |
| `OneBlock/LearnedSkipReGLU.lean` | "Not stated: the upper triangular skip; `ε = 0`" | `OneBlock/LearnedSkipTriangularRescale.lean`; `OneBlock/LearnedSkipRMSZeroReGLU.lean`, `OneBlock/LearnedSkipRMSZeroReGLUGeneric.lean`, `OneBlock/LearnedSkipTriangularRMSZeroRescale.lean` | "Not stated here: the upper triangular skip (`OneBlock/LearnedSkipTriangularRescale.lean`); `ε = 0` (`OneBlock/LearnedSkipRMSZeroReGLU.lean`, `OneBlock/LearnedSkipRMSZeroReGLUGeneric.lean`; triangular: `OneBlock/LearnedSkipTriangularRMSZeroRescale.lean`)" |
| `OneBlock/LearnedSkipAttention.lean` | "Not stated: the upper triangular skip; `ε = 0`" | `OneBlock/LearnedSkipTriangularSmooth.lean`; `OneBlock/LearnedSkipRMSZeroBoundKinds.lean`, `OneBlock/LearnedSkipTriangularRMSZeroBound.lean` | "Not stated here: the upper triangular skip (`OneBlock/LearnedSkipTriangularSmooth.lean`); `ε = 0`, where the paper has "at most" for an attention block (`OneBlock/LearnedSkipRMSZeroBoundKinds.lean`; triangular: `OneBlock/LearnedSkipTriangularRMSZeroBound.lean`)." (full stop missing here too) |
| `OneBlock/LearnedSkipTriangularSmooth.lean` | "Not stated: `ε = 0`" | `OneBlock/LearnedSkipTriangularRMSZeroBound.lean` | "Not stated here: `ε = 0` ("at most": `OneBlock/LearnedSkipTriangularRMSZeroBound.lean`)." |
| `OneBlock/LearnedSkipTriangularRescale.lean` | "Not stated: `ε = 0`" | `OneBlock/LearnedSkipTriangularRMSZeroRescale.lean` | "Not stated here: `ε = 0` (`OneBlock/LearnedSkipTriangularRMSZeroRescale.lean`)" |
| `OneBlock/SkiplessHomogeneousRMSZero.lean` | "Not stated: the equality for the skipless network with ReLU and ReLU² blocks" | `OneBlock/SkiplessHomogeneousRMSZeroEq.lean`, `OneBlock/SkiplessReluWideRMSZero.lean` | "Not stated here: the equality for the skipless network (`OneBlock/SkiplessHomogeneousRMSZeroEq.lean`: ReLU and ReLU² blocks of width exactly `d`; `OneBlock/SkiplessReluWideRMSZero.lean`: ReLU blocks of width at least `d`). Not stated: the equality for ReLU² blocks wider than `d`" |
| `OneBlock/ResidualRMSZeroGainHomogeneous.lean` | "Not stated: "by exactly `d_model²` for ReLU and ReLU² blocks" (the equality for the skipless network)" | the same two files | "Not stated here: "by exactly `d_model²`" (`OneBlock/SkiplessHomogeneousRMSZeroEq.lean`: ReLU and ReLU² blocks of width exactly `d`; `OneBlock/SkiplessReluWideRMSZero.lean`: ReLU blocks of width at least `d`). Not stated: ReLU² blocks wider than `d`" |
| `OneBlock/UnitsParallel.lean` | "Not stated: the paper's argument for blocks wider than `d` (a resultant; two entries of `h_1` without a common factor)" | `OneBlock/UnitsParallelAt.lean` (ReLU units, also more units than coordinates) | "Not stated here: units of a block wider than `d` (ReLU: `OneBlock/UnitsParallelAt.lean`, with conditions on the units in place of the paper's resultant). Not stated: ReLU² units of a block wider than `d`" |
| `OneBlock/SkiplessHomogeneousRMSZeroEq.lean` | "Not stated: blocks wider than `d` (the theorem says "of width at least `d_model`")" | `OneBlock/SkiplessReluWideRMSZero.lean` | "Not stated here: ReLU blocks wider than `d` (`OneBlock/SkiplessReluWideRMSZero.lean`). Not stated: ReLU² blocks wider than `d` (the theorem says "of width at least `d_model`")" |
| `Absorb/RMSNormGeneric.lean` | "Not stated: attention blocks" | `Absorb/RMSNormAttention.lean` | "Attention blocks and transformers: the row of `Absorb/RMSNormAttention.lean`" |

Two notes moved while this part was written: "Not stated: the bound at every point of the open set" in the rows of `Depth/InactiveUnitTwoSided.lean` and `Depth/InactiveGateTwoSided.lean` was true at `d67195b`; at `a312fd2` the index has a pointer in their place to a new file `Depth/InactiveUnitEveryPoint.lean` (statements, in work; not read here).

### Still true at `d67195b` (21)

No row was found that states the thing: `Symmetry/LocallyFreeTransformer.lean` (the form with the readout for networks with attention blocks; the paper has none); `Depth/InactiveUnitTwoSided.lean` and `Depth/InactiveGateTwoSided.lean` (the bound at every point; see above); `Residual/DepthRescale.lean` and `Residual/DepthReGLU.lean` (inputs in an open set that contains `0`); `OneBlock/KeepsProducts.lean` (the clauses with biases); `Depth/ScaledSuffix.lean` (Lemma D.10: the derivatives of all orders, the holomorphic extension with uniform bounds; the row of `Depth/ComplexSuffix.lean` is Lemma D.14, the case `ε = 0`); the text note on Example 4.2 of D; `Residual/ExactReductionWrites.lean` (mixed blocks; the count of the removed parameters); `Residual/FewerHiddenUnits.lean` and the text note on S Theorem A.28 (i) and (iii) (skipless blocks with fewer than `d` hidden units); the text note on S Theorem 4.6 (i) with biases; `Absorb/InjectiveBlocks.lean` (Remark A.12 and two sentences); `Absorb/FullNetworks.lean`; `OneBlock/AttentionDim.lean` (biases, position embedding, grouped-query attention, open sets of inputs, the equality condition as a definition); `OneBlock/UnitsParallelAt.lean` (ReLU² units in general position); `OneBlock/SkiplessReluWideRMSZero.lean` (ReLU² blocks wider than `d`); `Absorb/BiasesConstructions.lean`, `Absorb/GatedBiasesLower.lean`, `Absorb/RotaryBiases.lean` and the text note of the absorb paper (the remarks of Appendix C, `n ≥ rank M` for a singular `M`, Remarks 5.2, 5.3, A.8, A.12).

### "Not stated here", with the file that has the thing (9): fine

The rows of `OneBlock/LearnedSkipRMSZeroBound.lean`, `OneBlock/LearnedSkipRMSZeroBoundKinds.lean`, `OneBlock/LearnedSkipRMSZeroRescaleBound.lean`, `OneBlock/LearnedSkipTriangularRMSZeroBound.lean`, `OneBlock/UnitsRescaleSphere.lean`, `OneBlock/LearnedSkipRMSZeroRescale.lean`, `OneBlock/LearnedSkipRMSZeroRescaleGeneric.lean`, `OneBlock/LearnedSkipRMSZeroReGLU.lean`, `OneBlock/LearnedSkipRMSZeroReGLUGeneric.lean`. Every file they name exists at `d67195b`.

## What the authors of the papers should know

Nothing false, vacuous or drifted was found in the seven files. One point concerns a statement of the skips paper itself.

1. **S Proposition A.35 needs a condition when block 2 has exactly `d_model` units and is the last block.** The proposition names no width ("at every width" in the sentence before it) and no `d_out`; the Scope of the main text has `d_hidden ≥ d_model` and `d_out ≥ d_model`, and "the appendix states each result in greater generality". On the open set that the proof builds (`r̂_k r < 0` for all `k`) the bound `P − (L + 1) d_model² − s − (2 d_model − 1)` fails when `L = 2`, both blocks have exactly `d_model` units and `d_out < d_model`: for `d_model = d_in = 2`, `d_out = 1`, at `E = I`, `W_read^1 = W_read^2 = I`, `W_write^1 = [[−1, 1], [−1, 2]]`, `W_write^2 = [[1, 1], [1, 2]]`, `D = (1, 1)^⊤`, unit 1 of block 2 is dead at all nearby weights, `P = 22`, the bound is 3, and the Jacobian has rank 4 on a batch on which no pre-activation of a live unit vanishes (exact arithmetic; ReLU and ReLU²; for `d_model = 3` the ranks are 14 against 13 for `d_out = 2` and 12 against 10 for `d_out = 1`). The cause is in the proof: "whose symmetries are the changes of basis of its `L + 1` hidden states and `s − 1` rescalings" counts `(L + 1) d_model²` directions for a network whose block 2 has `d_model − 1` units, to which Lemma A.18 does not apply; the last hidden state is then written at rank `d_model − 1` and read at rank `d_out`, and `d_model − d_out` of the directions are lost (Remark A.19). The bound holds at almost every point of that set, and is proved in Lean for ReLU and ReLU² blocks, in each of these cases (with `d_in ≥ d_model` and at least `d_model` units in every block): block 2 has more than `d_model` units (the form of D Proposition E.1, which says "each with more than `d_model` hidden units" and is not affected); or `d_out ≥ d_model` (the Scope). Read as a pure existence statement the sentence of the paper stays true for another reason (on the open set where every unit of block 2 is dead the network is zero), which is not what the proof shows. A clause "with `d_out ≥ d_model`, or with more than `d_model` units in block 2" in the proposition, and one sentence in the proof for the case `d_hidden = d_model` (the changes of basis before block 2 are fixed from the embedding, those after it from the readout), would settle it.
2. **S Lemma A.18 could say what the two inductions give together.** If the embedding and the readout both have rank `d_model`, the conclusion holds with one block narrower than `d_model` (exact ranks, and the Lean statement in infinitesimal form); with two adjacent narrow blocks it fails, as Remark A.19 says. The proof of A.35 uses exactly this case. For residual networks the proof of the lemma does not use the width at all (one change of basis, fixed by the embedding), which is why Proposition A.33 (ii) is right with its own reason "since `E` has rank `d_model`" for any number of dead units.
3. **S Lemma A.2 (ii): two subscripts are missing.** The statement has `N(hG)` and `N(h)`; both are `N_ε`. With `N = N_0` the left side would be `ε/(2r²) + O(ε²)` for every `c`. The `O(ε²)` is for fixed `h` and `c` (the expansion is in `ε/r²`, with second coefficient `−(c² − 1)(c² + 3)/(8c⁴)`; it is not uniform as `h → 0`), and `c > 0` is understood.
4. **S Lemma A.18, "With RMSNorm […] the argument is unchanged": for `ε = 0` with the readout the argument changes.** The readout and the reads see only the orthogonal part `Q_ℓ` of `G_ℓ = c_ℓ Q_ℓ`. A write row is multiplied by `c_ℓ/λ^k`, so the rescalings do not act freely on the write rows by themselves; the read column comes first (it is an eigenvector of an orthogonal matrix with a positive eigenvalue, hence eigenvalue 1), and the scales `c_ℓ` are fixed last, by a nonzero write of every block and a nonzero embedding (`d_in ≥ 1`). The same eigenvalue argument shows that under RMSNorm (`ε = 0`, and `ε > 0` by the reader's reasoning) the ReGLU case needs no general position of the read columns, which it does need without normalization (twenty-seventh audit). With the embedding the argument is unchanged, as the paper says.
5. **The positive scale in `CO(d_model)`.** S Lemma A.2 (i) says "Then `M = Q`, where `G = cQ` with `Q` orthogonal"; D Lemma A.1 adds "with `c > 0`", and the proof of S finds `c > 0`. Without it `Q` is determined only up to its sign (`G = cQ = (−c)(−Q)`), and `M = Q` is ambiguous. The Lean statements for `ε = 0` ask the positive scale, and need it: with `c = −1`, `Q = −I` the matrix `G` is the identity but the map on the reads is not, and the statements with the embedding would be false at every parameter (check 2). One word in the statement of A.2 (i) would align the two papers.
6. The third sentence of A.18 ("networks with attention blocks") is proved in Lean for networks that have attention blocks and MLP blocks in any order, with the symmetries inside both, also for `ε = 0`; nothing is missing in the paper's argument there.

## Corrections for `STATEMENTS.md`

1. Row of `Symmetry/LocallyFreeTransformerGeneric.lean`: "they rest on the statements at one parameter, in work" is out of date. Put: "they rest on the statements at one parameter (the row above), proved".
2. Row of `Dimension/UpperBoundTwoSided.lean`, and the header of that file: "used by the proofs of S Proposition A.33 (ii) and A.35" says too much for A.33 (ii). Put: "needed by the proof of S Proposition A.35 when the block of the dead unit has exactly `d` units; the proof of A.33 (ii), for a residual network, needs only `E` of rank `d` (`Residual/DeadUnits.lean` asks no width)". The row may add that nothing is asked of the read rank of block `m` either.
3. Row of `Depth/InactiveUnitTwoSided.lean`: "the nonempty open set `negReadSet` and the bound at almost every point of it" describes the proof. Put: "a nonempty open set on which the unit is inactive, and the bound at almost every point of it (the statement says that such a set exists; the proof takes `negReadSet`)". Add: "`d_out ≥ d` is needed on `negReadSet`: for two blocks of width `d = 2` and `d_out = 1` the rank is 4 against the bound 3 (twenty-eighth audit)". The same remark on the existence form applies to the rows of the twins.
4. The paragraph "Not yet compared by such a reader (they go to the twenty-eighth audit)": the seven files are now compared (this report). Not compared: `Dimension/UpperBoundTwoSidedGated.lean`, `Depth/InactiveGateTwoSided.lean`, `Depth/InactiveUnitEveryPoint.lean`.
5. Row of `Depth/InactiveUnitRelu.lean` ("S Proposition A.35 […] in part: Lean has the form of D Proposition E.1"): add a pointer: "exactly `d` hidden units in the block of the dead unit, with `d_out ≥ d`: the row of `Depth/InactiveUnitTwoSided.lean`".
6. Row of `Symmetry/LocallyFreeRMSZero.lean` (optional additions, all true of the statements): with the embedding the rescalings are any real numbers; `s_ℓ > 0` is needed there (without it the statements are false at every parameter); the statement for ReLU and ReLU² blocks with the readout has no hypothesis `k ≠ 0`, and for `k ≥ 1` its hypothesis "no read column zero" is not needed beside the others.
7. The 19 notes of Part 3, with the words given there.

## What could not be checked

- The proofs were not read. What is known of them: they compile in the existing build, and the 36 theorems have the three standard axioms (`Ax28.lean`, compiled at `76034e7`). `lake build` was not run.
- Files written after this audit began (`Dimension/UpperBoundTwoSidedGated.lean`, `Depth/InactiveGateTwoSided.lean`, `Depth/InactiveUnitEveryPoint.lean`) were not read, so Proposition A.35 for ReGLU blocks with exactly `d` units and the bound at every point of the open set are not judged here. The counterexample of check 6 is for ReLU and ReLU² blocks.
- Check 2: the statements "no fixing map other than the identity" are on finite grids (10 orthogonal matrices with rational entries, 8 scales, 4 positive rescalings); they support, and do not prove, that a hypothesis could be weaker. That "no read column zero" is not needed for `k ≥ 1` with the readout, and that general position is not needed for `ε > 0`, are the reader's reasoning, not compiled.
- Check 3: that the action on a network of the sum preserves its function was read from `f_sum_mul` and the invariance of each part; it was not compiled as one statement.
- Check 5: 27 random draws and designed parameters, exact. Check 6: the ranks are on finite batches (exact arithmetic), so they are lower bounds; where the table says "holds" this is what the Lean theorem proves (for `d_in, d_out ≥ d`) or what was seen at 4 to 12 draws (the other cases), not a proof. The formula `(d − d_out) − (d_hidden^1 − d)` for the excess is the reader's count for two blocks, seen at seven settings.
- The remark that the existence statements hold on the open set where the network is zero is the reader's reasoning, with the rank 0 computed at two such parameters; it was not compiled.
- Part 3: the notes were judged by the rows of the index and the existence of the files, not by reading the Lean statements of those files.
- Every computation took under one minute.

Scratch work: `/home/claude/audit28/` (`Chk28.lean`, `Chk28b.lean`, `Chk28c.lean`, `Ax28.lean` with their `.out`; `c2_zero.py`, `c4_dev.py`, `c5_twosided.py`, `c6_dead.py`, `c6_more.py` with their `.out`; `src2/`: the seven files at `127aaac`; `src3/`: `LocallyFreeTransformer.lean` with its proofs; `STATEMENTS_d67195b.md`, `Axioms_d67195b.lean`, `notstated.txt`).
