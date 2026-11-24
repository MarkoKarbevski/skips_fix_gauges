STATUS: complete

# Twelfth audit of Lean statements against the papers, part B (24 November 2026)

Reader: an independent reader who did not write the statements. Brief:
`/home/claude/proj_up/audit12b_brief_2026-11-24.md`. Subject: the symmetries inside attention
heads, the upper bounds for networks of attention blocks, the analyticity of the attention block,
and the one-block theorem for an attention block, with and without its skip.

Library: `/home/claude/lw/lean` (branch `lean-wip`).

- Commit when I began: `2a488da1da773d33fb1a817b15c4c3eb34bc84cc` (14:00:45 UTC).
- Commit when I ended: `169686c83d023daa1425dd59dd2babae1e3bb368` (14:17:37 UTC). The branch moved
  several times while I read. Of the seven files of the brief, three changed, and in each the
  `sorry` were replaced by proofs and private helpers were added: `OneBlock/AttentionStepOne.lean`
  (at `5a109cf`), `OneBlock/AttentionGeneric.lean` (at `b4c342d`) and `OneBlock/Attention.lean` (at
  `ef746c1`). The public statements, their docstrings and the file headers are the same: in
  these three files `git diff 2a488da 169686c` removes only the seven lines `sorry`. One change
  of form: before each of the five theorems of `OneBlock/Attention.lean` a line `omit … in` was
  added, which drops instance arguments that the statement does not use (`[DecidableEq d]` in
  all five, `[Fintype dOut]` in three). The new statements ask less and say the same. The other
  four files and `Network/Attention.lean` did not change. Two new files appeared that are not in
  the brief (`Absorb/ShortSequences.lean`, `Absorb/ShortSequencesPoly.lean`); I did not read them.
- Files with `sorry`: at `2a488da`, three: `OneBlock/Attention.lean` (5: `hasDerivAt_attnScore`,
  `hasDerivAt_attnValue`, `eval_attention_oneBlock`, `eval_attention_two_tokens`,
  `flat_attention_oneBlock_keeps`), `OneBlock/AttentionStepOne.lean` (1) and
  `OneBlock/AttentionGeneric.lean` (1); `OneBlock/AttentionDim.lean` had none of its own and
  rested on the seven. At `169686c`: none of the seven files of the brief; in the whole library
  only `Absorb/ShortSequences.lean`, outside the brief.

So I compared the statements while seven of them were unproved, and they were proved while I
wrote. What I say below "by hand" about these seven I worked out before their proofs were in
the library.

After I ended, the branch moved once more (`5414c73`, 14:20:25 UTC): four new files outside the
brief (`OneBlock/AttentionFamily.lean`, `Residual/DepthAttention.lean`,
`Residual/DepthAttentionGeneric.lean`, `Residual/DepthAttentionDim.lean`) and their index rows.
The seven files of the brief are the same at `5414c73` as at `169686c`. I did not read the new
files.

Papers, as text: the dimension paper ("D", `dim.txt`) and the skips paper ("S", `skips.txt`).
Line numbers of `STATEMENTS.md` are those of `169686c`; at `5414c73` every line named below from
line 444 on is two lines further down. Each correction quotes the words to change.

How I checked.

- "By reading": I read the seven Lean files and `Network/Attention.lean` in full at `2a488da`,
  the definitions they use (`Arch`, `Params`, `hidden`, `eval`, `funDim`, `jacobianRank`, `flat`,
  `cobDir`, `rmsRow`, `rmsNorm`, `antisymmetric`), and the paper passages: D Section 2, Section 4,
  Appendix B (to the proof of Proposition 4.6), Theorem C.1 with "Notation and flat directions",
  Lemma C.3 (statement) and the proof "Attention blocks"; S Section 2, Section 4.1 and 4.2,
  Appendix A.6 (Theorem A.17, Lemma A.18, Remark A.19), Theorem B.1 with its notation, "Part (i)
  for attention blocks", Remark B.5 and "Extensions of part (i)".
- "By hand": a short argument of my own, written in the note.
- "By compiling": scratch files of my own in `/home/claude/audit12b/` (`Chk1.lean` to `Chk5.lean`,
  outputs `Chk*.out`), compiled with `lean` 4.36.0 through `LEAN_PATH`, without `lake`, against
  copies of the compiled library of `/home/claude/lp/lean` (its sources under `SkipsLean/` were
  the same as those of `lw` by `diff -rq` each time I copied: at 14:03 with both at `2a488da`, at
  14:11 with both at `479f2f2`, at 14:18 with both at `169686c`). At the first two times that
  library had no compiled `OneBlock/AttentionDim.lean`, so I compiled a copy of that file into my
  folder (no error, no warning; twice, 7 seconds each). Six other compilations of about 3 seconds
  each. I did not run `lake build` and wrote nothing under `lw`, `lp` or the repository.
- "By a computation": `/home/claude/audit12b/attn_check.py`, `attn_check2.py`, `attn_check3.py`
  (numpy, double precision; derivatives in the parameters by the complex step), outputs
  `attn_check*.out`.

Short answer. **Nothing false, vacuous or drifted was found in a statement or a definition.** At
commit `169686c` all seven files are proved: the thirty public theorems show the three standard
axioms (`Chk5.out`). Every "generic" is `∀ᵐ θ ∂μ` for every additive Haar measure. The statements
use the library's `funDim` with all inputs `Matrix T dIn ℝ`. The final statements carry the
hypotheses of D Theorem C.1 and S Theorem B.1 (i) and nothing more; in the mask they ask less
than the papers. The one Lean statement serves both papers, and I found no difference between
the two proofs that it hides.
Three descriptions (not statements) are wrong or out of date: a citation in the header of
`Network/AttentionAnalytic.lean` and in its index row, a quotation in the header of
`OneBlock/AttentionDim.lean`, and five sentences of the index (corrections below).

---------------------------------------------------------------------------------------------------

## Part 1: the drift checks

### Check 1. Generic means almost every parameter, for every Haar measure

**Verdict: yes, in all eight statements.** None is "there is a point" or "on an open set". (By
reading; the elaborated forms by compiling, `Chk1.out`.)

Each of the eight has the shape `(μ : Measure (Params (Arch.attention sees χ H dh) dIn dOut))
[μ.IsAddHaarMeasure] … : ∀ᵐ θ ∂μ, …`, with `μ` a variable of the statement.

| Statement | The Lean text after the hypotheses |
|---|---|
| `ae_funDim_add_le_skipless_attention` | `∀ᵐ θ ∂μ, funDim (Arch.attention sees id H dh) 0 θ + ((L + 1) * Fintype.card d ^ 2 + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2) ≤ Module.finrank ℝ (Params …)` |
| `ae_funDim_add_le_skipless_attention_rmsNorm` | `∀ᵐ θ ∂μ, funDim (Arch.attention sees (rmsNorm ε) H dh) 0 θ + ((L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2) + 2 * ∑ ℓ, …) ≤ …` |
| `ae_funDim_add_le_residual_attention` | `∀ᵐ θ ∂μ, funDim (Arch.attention sees id H dh) 1 θ + (Fintype.card d ^ 2 + 2 * ∑ ℓ, …) ≤ …` |
| `ae_funDim_add_le_residual_attention_rmsNorm` | `∀ᵐ θ ∂μ, funDim (Arch.attention sees (rmsNorm ε) H dh) 1 θ + (Fintype.card d * (Fintype.card d - 1) / 2 + 2 * ∑ ℓ, …) ≤ …` |
| `ae_oneBlockGenericAttention` | `∀ᵐ θ ∂μ, OneBlockGenericAttention θ` |
| `ae_funDim_attention_oneBlock` | `∀ᵐ θ ∂μ, funDim (Arch.attention sees id H dh) 0 θ + (2 * Fintype.card d ^ 2 + 2 * (Fintype.card (H 0) * Fintype.card (dh 0) ^ 2)) = Module.finrank ℝ (Params …)` |
| `ae_funDim_attention_oneBlock_residual` | `∀ᵐ θ ∂μ, funDim (Arch.attention sees id H dh) 1 θ + (Fintype.card d ^ 2 + 2 * (Fintype.card (H 0) * Fintype.card (dh 0) ^ 2)) = …` |
| `ae_funDim_attention_oneBlock_residual_eq_add` | `∀ᵐ θ ∂μ, funDim (Arch.attention sees id H dh) 1 θ = funDim (Arch.attention sees id H dh) 0 θ + Fintype.card d ^ 2` |

- The private helpers with "almost every" (`ae_rank_read_cols_uba`, `ae_rank_QV_uba`,
  `ae_rank_E_uba`, and in the new proofs `ae_rank_read_cols_obg`, `ae_rank_write_rows_obg`) have the
  same shape. The only `∃ θ` in these files are inside proofs: a parameter at which a determinant
  or an entry is not zero, from which "almost everywhere" follows by analyticity.
- The statements at one parameter (`funDim_add_le_skipless_attention` and its three companions,
  `funDim_attention_oneBlock`, `funDim_attention_oneBlock_residual`, the two
  `flat_attention_oneBlock…`) hold for every `θ` that satisfies written conditions (ranks; the
  structure `OneBlockGenericAttention`). With their `ae_` companion they are the generic claim, as
  for the other kinds of block (sixth audit, Check 1).
- That an additive Haar measure on the parameters is a Lebesgue measure: sixth audit, Check 1; I
  did not repeat it.

### Check 2. `funDim` is the library's functional dimension, over all inputs

**Verdict: yes.** (By reading; one fact by compiling.)

- All statements above are about `funDim (Arch.attention …) S θ` of `Dimension/Functional.lean`:
  the supremum over all `n` and all batches `X : Fin n → Matrix T dIn ℝ` of the rank of the
  Jacobian in `θ` (sixth audit, Check 2). The inputs are all real `T × d_in` matrices, with the
  set of tokens `T` fixed. `S = 0` is the skipless network and `S = 1` the residual one (`1` is the
  identity matrix at the block; the proof of `flat_attention_oneBlock_residual` rewrites it with
  `Pi.one_apply`).
- Without normalization nothing is dropped by Lean's convention "`fderiv` is `0` where not
  differentiable": the network of attention blocks is differentiable in the parameters at every
  input, for every mask and all stream matrices (by compiling, `Chk4.lean`, from
  `differentiable_f_attention` and `differentiable_eval`). So for the one-block theorem and for
  the bounds without normalization `funDim` is the paper's `fd(θ)` word for word. Under
  pre-RMSNorm with `ε > 0` the same holds by the same argument (by hand; `rmsNorm ε` is
  differentiable for `ε > 0`). For `ε ≤ 0`: Check 3 (c).

### Check 3. No extra hypotheses in the main-text statements

**Verdict: none. Where Lean differs from the papers it asks less.**

**(a) D Theorem 5.1 / C.1 for an attention block.** The Lean text (by compiling, `Chk1.out`; names
of the instances left out):

```
ae_funDim_attention_oneBlock : ∀ {T d dIn dOut} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut] {sees : T → T → Prop} [DecidableRel sees] {H dh : Fin 1 → Type}
  [(ℓ : Fin 1) → Fintype (H ℓ)] [(ℓ : Fin 1) → Fintype (dh ℓ)]
  (μ : Measure (Params (Arch.attention sees id H dh) dIn dOut)) [μ.IsAddHaarMeasure],
  2 ≤ Fintype.card d → Fintype.card d ≤ Fintype.card dIn → Fintype.card d ≤ Fintype.card dOut →
  Fintype.card (dh 0) ≤ Fintype.card d → Fintype.card d ≤ Fintype.card (H 0) * Fintype.card (dh 0) →
  ∀ (t₁ t₂ : T), t₁ ≠ t₂ → sees t₂ t₂ → sees t₂ t₁ →
  ∀ᵐ θ ∂μ, funDim (Arch.attention sees id H dh) 0 θ
      + (2 * Fintype.card d ^ 2 + 2 * (Fintype.card (H 0) * Fintype.card (dh 0) ^ 2))
    = Module.finrank ℝ (Params (Arch.attention sees id H dh) dIn dOut)
```

| Paper (Theorem C.1) | Lean | Verdict |
|---|---|---|
| "`d_model ≥ 2`" | `hd` | same |
| "`d_in, d_out ≥ d_model`" | `hdIn`, `hdOut` | same |
| "inputs range over all of `ℝ^{T × d_in}`" | `funDim` (Check 2) | same |
| "one block, without normalization and without biases" | `Fin 1`, `χ = id`; `Params` has no biases | same |
| "`H` heads of width `d_h ≤ d_model` with `H d_h ≥ d_model`" | `hdh`, `hH` | same (Theorem 5.1 in the Scope has `H d_h = d_model`, a special case) |
| "causal or not, on sequences of at least two tokens" | a relation `sees` and two tokens `t₁ ≠ t₂` with `sees t₂ t₂` and `sees t₂ t₁` | Lean asks less |
| "`P − 2 d_model² − s`", `s = 2 H d_h²` | `fd + (2 d² + 2 (H d_h²)) = P` | same |

The two masks are instances (by compiling, `Chk2.lean`, no `sorry` of mine):

- no mask, at least two tokens: `sees := fun _ _ => True`, any two different tokens (they exist as
  `2 ≤ Fintype.card T`), `hs2 := trivial`, `hs1 := trivial`;
- the causal mask on `n + 2` tokens: `T := Fin (n + 2)`, `sees := fun t s => s ≤ t`, `t₁ := 0`,
  `t₂ := 1`, `h12 := Fin.zero_ne_one`, `hs2 := le_rfl`, `hs1 := Fin.zero_le _`. The same instance
  gives the residual value and "the skip raises `fd` by exactly `d²`".

What the Lean hypothesis allows beyond them: any relation on any finite set of tokens in which
one token sees itself and one other token. The other tokens may see anything, or nothing (for
example "only token `1` sees, and it sees `0` and `1`", `Chk2.lean` (c)). A token that sees no
token gets the weights `0` and the block output `0` (eleventh audit, note 1). Not covered: a mask
in which no token sees itself, such as the strict causal mask `s < t` (`Chk2.lean` (e)), and a
mask in which every token sees only itself (there the theorem would be false, the network is
linear in each token). The computation agrees with the Lean form on two masks outside the paper
("only token `1` sees", "token `1` sees all, token `0` sees nothing"): both values come out
(`attn_check.out`, part A).

**(b) D Theorem 4.3 and S Theorem 4.2 for attention blocks.** (By reading.)

| Lean statement | Lean hypotheses | Paper setting | Verdict |
|---|---|---|---|
| `ae_funDim_add_le_skipless_attention` (and `_rmsNorm`) | `d_in ≥ d`; for every block `d_h ≤ d` and `H d_h ≥ d` | D Lemma B.1: "heads have width `d_h ≤ d_model` and total width `H d_h ≥ d_model`. If `d_in ≥ d_model`"; the Scope: `H d_h = d_model`, `d_in, d_out ≥ d_model ≥ 2`, two tokens at least | the hypotheses of Lemma B.1; weaker than the Scope (`H d_h = d ≥ 1` gives `H ≥ 1`, so `d_h ≤ d` and `H d_h ≥ d`) |
| `ae_funDim_add_le_residual_attention` (and `_rmsNorm`) | `d_in ≥ d`; `d_h ≤ d` | S Lemma A.18: "With an embedding of rank `d_model` … heads have width `d_h ≤ d_model` and total width `H d_h ≥ d_model`" | weaker: no `H d_h ≥ d` |

Lean asks nothing on `d_out`, on `d ≥ 2`, on the mask or on the number of tokens, and the numbers
of heads and the head widths may differ from block to block (S Scope: "All attention blocks have
the same number `H` of heads"). All of this is weaker than the papers' settings, and the bounds
are proved (three standard axioms, `Chk1.out`, `Chk5.out`).

**(c) Pre-RMSNorm, "for every real `ε`".** `rmsNorm ε` normalizes each row by
`rmsRow ε v = (Real.sqrt (v ⬝ᵥ v / d + ε))⁻¹ • v` (`Basic/RMSNorm.lean`). (By reading.)

- `ε > 0`: the paper's `N_ε`, case (+) of D and the RMSNorm of S. The count `d(d−1)/2` per hidden
  state is `dim O(d)`. This is the paper's statement, and `funDim` is the paper's `fd`. Covered.
- `ε = 0`: Lean's map is `√d · v/‖v‖` on a row `v ≠ 0` and `0` on the zero row (the paper leaves
  the zero row out of the domain). The Lean statement is true there and counts `d(d−1)/2` per
  hidden state. The papers count more for `ε = 0`: the group is `CO(d)`, of dimension
  `d(d−1)/2 + 1` (D after Theorem 4.3, for four kinds of block, not for attention; S Theorem
  A.17 with Lemma A.18, which includes attention). So for `ε = 0` the Lean bound for attention is
  a true but weaker bound than S Theorem A.17 (ii): by `L + 1` without skips and by `1` with
  them. The bound with `CO(d)` is in Lean for any kind of block without the term `s`
  (`Dimension/UpperBoundRMSNormZero.lean`, `Dimension/UpperBoundResidualRMSNormZero.lean`); with
  both `CO(d)` and `s = 2 ∑ H d_h²` it is not stated. `funDim` at `ε = 0` is the largest rank
  over the batches at which Lean's total network is differentiable in `θ` (index, note on
  `ε = 0`).
- `ε < 0`: in Lean the square root of a negative number is `0` and `0⁻¹ = 0`, so a row with
  `‖v‖²/d ≤ −ε` is sent to `0` and a longer row to `v/√(‖v‖²/d + ε)`. No paper has this map
  (D: `ε ≥ 0`; S: `ε > 0`). The statement is true there (an orthogonal change of basis keeps the
  norm of a row) and says nothing about the papers. It is the form of the other statements "for
  every real `ε`" of the library.

**(d) S Theorem 4.6 (i) / B.1 (i) for an attention block, without biases.**
`ae_funDim_attention_oneBlock_residual` and `ae_funDim_attention_oneBlock_residual_eq_add` have the
hypotheses of (a) and no other. B.1: "Let `d_model ≥ 2`, let the input and output dimensions be at
least `d_model`, … an attention block of `H` heads of width `d_h ≤ d_model`, causal or not, on
sequences of at least two tokens. (i) … let the block have width at least `d_model`, where the
width of an attention block is `H d_h`." Same.

**Are the hypotheses needed?** A computation outside each one (`attn_check.out` part A',
`attn_check3.out`; ranks on random batches, not proofs): with one token the ranks are 4 and 4
where the formulas give 8 and 12; with `d = 1` and two heads, 3 and 3 against 4 and 5; with
`d_h > d`, 8 and 12 against 6 and 10; with `d_in < d`, 3 and 5 against 6 and 10; with
`d_out < d`, the residual rank is 8 against 10; with `H d_h < d` (`d = 4`, `d_in = 4`,
`d_out = 5`, one head of width 3) the skipless rank is 33 against 34 on two draws. So each
hypothesis excludes a case in which the value fails. (In several other draws with `H d_h < d`
the value still came out, and for `d = 1` with one head as well; the papers do not claim these
cases and neither does Lean.)

### Check 4. One statement for two papers

**Verdict: nothing differs between the two proofs that the Lean statements merge.** (By reading
both proofs side by side; the formulas by hand and by the computation.)

| Piece | D, "Attention blocks" | S, "Part (i) for attention blocks" | Lean, stream matrix `S 0` |
|---|---|---|---|
| matrices | `B_i = E W_{Q,i} W_{K,i}^⊤ E^⊤/√d_h`, `C_i = E W_{V,i} W_{O,i} D`, `S = ∑ C_i` | the same, and `M = E D` "with `M` only in the residual network" | `attnScore`, `attnValue`; `E S_0 D`, which is `0` for `S_0 = 0` and `E D` for `S_0 = 1` |
| output at token `t` | `∑_i ∑_s a_ts x_s C_i` | `x_t M + ∑_i ∑_s a_ts x_s C_i` | `x (E S_0 D) + ∑_i P_i(x) x C_i` |
| two-token formula | (8): `u S − ½ v S + ½ ∑ tanh(½(u B_i v^⊤ − log k)) v C_i` | (16): `u K − ½ v S + …`, `K = M + S` | `u (E S_0 D + ∑ C_i) − ½ v ∑ C_i + ∑ (½ tanh(½(u·B_i v − log k))) v C_i` |
| generic conditions, Step 1 | ranks of `E`, `D`, of the four matrices of every head, of the queries, the keys and the output projection of all heads | the same sentence | `OneBlockGenericAttention`, without the keys of all heads |
| generic conditions, Step 2 | "the columns `B_i v^⊤` are nonzero and pairwise non-collinear … every row `v C_i` is nonzero" | the same | field `exists_v` |
| Step 2, conclusion | `D_θ B_i η = 0`, `D_θ C_i η = 0` | the same and `D_θ M η = 0` | `η_E S_0 D + E S_0 η_D = 0 ∧ ∀ i, dAttnScore θ η i = 0 ∧ dAttnValue θ η i = 0` |
| Step 1, conclusion | the four formulas with `X`, `Y`, `Γ_i`, `Γ'_i` | the same; "In the residual network `D_θ M η = E(X − Y)D = 0` gives `X = Y`" | `exists_cobDir_add_headDir_of_keeps` (no stream matrix in it); `X_0 = X_1` in `flat_attention_oneBlock_residual` |
| values | `P − 2d² − s` | `P − 2d² − s` and `P − d² − s` | `fd + (2d² + 2Hd_h²) = P`; `fd + (d² + 2Hd_h²) = P` |
| `s` | `2 H d_h²` | `2 H d_h²` | `2 * (card (H 0) * card (dh 0) ^ 2)` |

- (8) is the Lean formula at `S_0 = 0`, (16) at `S_0 = 1`. Both by hand (note 4 below) and by the
  computation with a random matrix `S_0` (`attn_check.out` part B: largest relative error
  `2·10⁻¹⁵` over the trials).
- The first clause of `flat_attention_oneBlock_keeps` is `0 = 0` for `S_0 = 0` and
  `η_E D + E η_D = 0`, S's `D_θ M η = 0`, for `S_0 = 1` (S: "`D_θ M η = η_E D + E η_D` for
  `M = ED`").
- What S has and D does not, and Lean does not state: biases (the bias terms of (16) and the
  count `2 d_model + 2 H d_h`), the position embedding and grouped-query attention. The Lean
  statements are for the networks without biases, where the two proofs are the same text.

---------------------------------------------------------------------------------------------------

## Part 2: the statements, file by file

### Verdict table

Status. All the theorems of the table are proved at `169686c`: no `sorry` in the seven files, and
`#print axioms` shows `propext`, `Classical.choice`, `Quot.sound` only for each of the thirty
public theorems (`Chk5.out`, against the library compiled at that commit). At `2a488da`, when I
compared them, the rows marked † were unproved (`sorryAx` in `Chk1.out`) or rested on unproved
statements; I judged those by hand first.

| Paper statement or proof piece | Lean | Verdict | Difference | How checked |
|---|---|---|---|---|
| D Appendix B: `(W_Q, W_K) ↦ (W_Q K, W_K K^{-⊤})` | `Params.headsQK` (definition) | SAME | all heads of all blocks at once, one `K` per head | reading |
| D Appendix B: `(W_V, W_O) ↦ (W_V K', K'^{-1} W_O)` | `Params.headsVO` (definition) | SAME | the same | reading |
| D Section 4, S A.6: a symmetry inside a block leaves the map of that block unchanged | `eval_headsQK`, `eval_headsVO` | SAME | any depth, mask, `χ`, stream matrices | reading |
| D proof of C.1, Step 1: `η_Q = W_Q Γ`, `η_K = −W_K Γ^⊤`, `η_V = W_V Γ'`, `η_O = −Γ' W_O` | `headDirQK`, `headDirVO` (definitions) | SAME | — | reading; by hand |
| D Step 3: "Every direction of Step 1 is flat, since it comes from a symmetry" | `headDirQK_mem_flat`, `headDirVO_mem_flat` | SAME | — | reading |
| D Lemma B.1 (and S Lemma A.18) for attention blocks | `cobDir_add_headDirQK_add_headDirVO_injective` | PART | the infinitesimal form, at one `θ` under the ranks the proof uses; "no continuous family fixes `θ`" is not stated | reading |
| D Theorem 4.3, attention, no normalization | `funDim_add_le_skipless_attention`, `ae_…` | LEAN STRONGER | same count; the hypotheses of Lemma B.1, weaker than the Scope (Check 3 (b)) | reading |
| D Theorem 4.3, attention, pre-RMSNorm | `funDim_add_le_skipless_attention_rmsNorm`, `ae_…` | LEAN STRONGER for `ε > 0` | same count and the same weaker hypotheses; every real `ε`; for `ε = 0` weaker than the `CO(d)` count (Check 3 (c)) | reading |
| S Theorem 4.2 / A.17 (ii), identity skips, attention | `funDim_add_le_residual_attention`, `ae_…`, and the two `_rmsNorm` | LEAN STRONGER | same counts; no `H d_h ≥ d` | reading |
| S A.17 (ii) with Lemma A.18 for `ε = 0` and attention (`CO(d)` and `s`) | — | not stated | — | reading |
| S Section 1.1: attention blocks are real-analytic | `analyticOnNhd_attnWeights`, `analyticOnNhd_f_attention`, `differentiable_f_attention` | SAME | the block map only; on all of the space, every mask | reading |
| D, S Reduction: `B_i`, `C_i` | `attnScore`, `attnValue` (definitions) | SAME | — | reading; computation |
| `D_θ B_i η`, `D_θ C_i η` | `dAttnScore`, `dAttnValue`; `hasDerivAt_attnScore` †, `hasDerivAt_attnValue` † | SAME | — | by hand; computation |
| Reduction: "the output at token `t` is `∑_i ∑_s a_ts x_s C_i`" (S: plus `x_t M`) | `eval_attention_oneBlock` † | SAME | any stream matrix, any mask | by hand |
| Equation (8) (D), (16) (S) | `eval_attention_two_tokens` † | LEAN STRONGER | any mask in which `t₂` sees itself and `t₁`; any `S_0`; `k` any number `≥ 1` | by hand; computation |
| the generic conditions of Steps 1 and 2 | `OneBlockGenericAttention` (definition) | LEAN STRONGER | no rank of the keys of all heads; "some `v`" for "generic `v`" | reading; by hand |
| Step 2 | `flat_attention_oneBlock_keeps` † | SAME | any `S_0`; asks only for the `v` | by hand |
| Step 1 | `exists_cobDir_add_headDir_of_keeps` † | LEAN STRONGER | without the rank of the keys of all heads; one direction (a direction that keeps `B_i`, `C_i` is of this form) | by hand; computation |
| "For generic parameters …" (Steps 1 and 2) | `ae_oneBlockGenericAttention` † | SAME | the hypotheses of C.1 | by hand |
| Step 3 (D): "by Step 2 every flat direction … is one of them" | `flat_attention_oneBlock` † | SAME | — | reading |
| S: "In the residual network … gives `X = Y`" | `flat_attention_oneBlock_residual` † | SAME | — | reading |
| D Theorem 5.1 / C.1, attention | `funDim_attention_oneBlock` †, `ae_funDim_attention_oneBlock` † | SAME (LEAN STRONGER in the mask) | Check 3 (a) | reading; compiling; computation |
| S Theorem B.1 (i), attention, residual value | `funDim_attention_oneBlock_residual` †, `ae_…` † | SAME (LEAN STRONGER in the mask) | without biases | reading; computation |
| S 4.6 (i) / B.1 (i): "the skip raises the functional dimension by exactly `d_model²`" | `ae_funDim_attention_oneBlock_residual_eq_add` † | SAME | — | reading |
| S B.1 (i): with biases; "Both networks satisfy the equality condition" as a named condition; inputs in an open set; position embedding; grouped-query attention | — | not stated | the equality is written `fd + … = P` | reading |

### Notes

**1. `Symmetry/AttentionHeads.lean`.** (By reading; the algebra by hand.)

- `Params.headsQK θ K`: the query entry `(a, (i, k))` becomes `∑_{k'} W_Q[a,k'] K[k',k]`, that is
  `W_{Q,i} K_i` (on the right); the key entry becomes `∑_{k'} W_K[a,k'] K⁻¹[k,k']`, that is
  `W_{K,i} (K_i⁻¹)^⊤ = W_{K,i} K_i^{-⊤}` (on the right, inverse transposed). Values, write, `E`,
  `D` are untouched. Then `W_Q K (W_K K^{-⊤})^⊤ = W_Q W_K^⊤`. The paper's first map.
- `Params.headsVO θ K'`: the value entry becomes `(W_{V,i} K'_i)[a,k]` (on the right) and the row
  `(i, k)` of the write becomes `(K'_i⁻¹ W_{O,i})[k, ·]` (on the left, inverse). The paper's
  second map.
- `headDirQK θ Γ`: query `(W_Q Γ)[a,k]`, key `−∑_{k'} W_K[a,k'] Γ[k,k'] = −(W_K Γ^⊤)[a,k]`, zero
  elsewhere. `headDirVO θ Γ'`: value `(W_V Γ')[a,k]`, write row `−(Γ' W_O)[k, ·]`. These are the
  derivatives of the two maps at `K = I + τ Γ`, `τ = 0` (`(I + τΓ)^{-⊤} = I − τ Γ^⊤ + …`), and
  the paper's `η_{Q,i}`, `η_{K,i}`, `η_{V,i}`, `η_{O,i}` with `X = Y = 0`. Lean takes the curve
  `exp(τ Γ)`, which has the same derivative.
- The injectivity statement: hypotheses `E` of rank `d`, every write of rank `d`, every `W_{Q,i}`
  and every `W_{V,i}` of rank `d_h`. The proof of Lemma B.1 uses exactly these: "`E` has rank
  `d_model`, so `G_0 = I`"; "these matrices [`W_{Q,i}`, `W_{V,i}`] have full column rank … so
  `K_i = K'_i = I`"; "the write … has rank `d_model` … so `G_ℓ = I`". The keys and the outputs of
  a head are not asked, as in the paper. The conclusion is that `(X, Γ, Γ') ↦ cobDir θ X +
  headDirQK θ Γ + headDirVO θ Γ'` is injective, for any `χ`: the form the proof of Theorem 4.3
  needs. The index says "in infinitesimal form"; its general note on Lemma B.1 (line 444) still
  says "attention is not" covered (correction 3).

**2. `Dimension/UpperBoundAttention.lean`: the counts.** (By reading.)

- Without skips: `(L + 1) d² + 2 ∑_ℓ H_ℓ d_{h,ℓ}²` and `(L + 1)·(d(d−1)/2) + 2 ∑_ℓ …`; this is
  `(L + 1) dim 𝒢 + s` with `s = 2 H d_h²` per block (D Appendix B). With identity skips:
  `d² + 2 ∑ …` and `d(d−1)/2 + 2 ∑ …`, S's `dim 𝒢 + s`. The statements are `fd + count ≤ P` in
  natural numbers, which is `fd ≤ P − count`.
- `Fintype.card d * (Fintype.card d - 1) / 2`: a product of two consecutive numbers is even, so
  the division is exact; for `d` empty the natural subtraction gives `0 * 0 / 2 = 0`, the right
  value. `finrank_antisymmetric` gives this number as the dimension of the antisymmetric
  matrices.
- The computation, on six networks of one or two blocks, with and without RMSNorm (`ε = 0.01`),
  finds every rank equal to its bound (`attn_check.out`, part C); Lean claims only "at most".

**3. `Network/AttentionAnalytic.lean`.** (By reading.) `analyticOnNhd_attnWeights sees :
AnalyticOnNhd ℝ (attnWeights sees) Set.univ` and `analyticOnNhd_f_attention sees χ H dh ℓ :
AnalyticOnNhd ℝ ((Arch.attention sees χ H dh).f ℓ) Set.univ`: on all of the space (`Set.univ`),
for every decidable relation `sees`; the row of a token that sees no token is the constant `0`.
The third statement is differentiability everywhere. They are statements about the fixed map of
one block; that the output of a network is analytic in the weights and the input is not stated in
this file. The header and the index row cite "D Section 2, 'analytic blocks'": that phrase is not
in D. D calls four kinds of block real-analytic, without attention (introduction: "for tanh,
GELU, SwiGLU and GeGLU blocks … These four kinds of block are real-analytic"); "analytic blocks",
with attention among them, is the skips paper's term (S Section 1.1: "attention, tanh, GELU,
SwiGLU or GeGLU blocks … These five kinds of block are real-analytic, and we call them analytic
blocks"). Correction 2.

**4. `OneBlock/Attention.lean`.** (By reading and by hand; the computation where named.)

- `attnScore θ i = (√d_h)⁻¹ • (E * W_Q * W_Kᵀ * Eᵀ)`, `attnValue θ i = E * W_V * W_O * D`: the
  paper's `B_i`, `C_i`, with the factor `1/√d_h` and the transpose on `W_K` and on the second
  `E`. The four matrices are the columns `(i, query)`, `(i, key)`, `(i, value)` of the read and
  the rows `(i, ·)` of the write.
- `dAttnScore`, `dAttnValue`: along `θ + τ η`, the product rule on the four factors gives
  `(√d_h)⁻¹ (η_E Q Kᵀ Eᵀ + E η_Q Kᵀ Eᵀ + E Q η_Kᵀ Eᵀ + E Q Kᵀ η_Eᵀ)` and
  `η_E V O D + E η_V O D + E V η_O D + E V O η_D`: the Lean definitions, term by term. The
  computation agrees to `4·10⁻⁹` (central differences, 100 draws, part D).
- `eval_attention_oneBlock`: with one block and `χ = id`, `h_0 = xE`, `h_1 = h_0 S_0 +
  ∑_i P_i (xE) W_{V,i} W_{O,i}` with the scores `xE Γ_i Eᵀ xᵀ = x B_i xᵀ` (`f_attention_mul`),
  and `y = h_1 D = x E S_0 D + ∑_i P_i x C_i`. Row `t` is `x_t E S_0 D + ∑_i ∑_s a_ts x_s C_i`:
  the paper's sentence, with `x E S_0 D` added. True for every mask and in every degenerate case
  (it is an identity of matrices).
- `eval_attention_two_tokens`. The input has the row `u` at `t₂` and `u − v` at every other
  token. Token `t₂` sees itself and `k` other tokens, each with the row `u − v`. The scores of
  head `i` in row `t₂` are `u B_i uᵀ` (itself) and `u B_i uᵀ − u B_i vᵀ` (the others), so the
  weight on itself is `1/(1 + k e^{−u B_i vᵀ}) = ½ + ½ tanh(½(u B_i vᵀ − log k))`, and the output
  at `t₂` is `u E S_0 D + ∑_i (u C_i − (½ − ½ tanh(…)) v C_i)`: Lean's right side, with the
  paper's signs and both factors `½`. `u ⬝ᵥ (attnScore θ i *ᵥ v)` is `u B_i vᵀ`.
  - The input against the paper's: without a mask the paper takes "sequences whose tokens other
    than the second all equal the first"; that is Lean's input, and `k = T − 1`. With the causal
    mask the paper takes "any sequence"; Lean's input is one of them (all other tokens equal to
    `u − v`), and with `t₂ = 1` Lean's `k` is `1`. Both values of `k` by compiling
    (`Chk2.lean` (d)). So Lean's input is an instance in both cases, and the output at `t₂` does
    not depend on the tokens that `t₂` does not see.
  - `k = 0` cannot occur: `t₁` is counted, by `hs1` and `h12` (`Chk4.lean`). Without them the
    formula would be false (`Real.log 0 = 0` in Lean, while a token that sees only itself has the
    output `u (E S_0 D + ∑ C_i)`). `hs2` is needed as well (the weight on itself).
  - The computation: 400 draws over four masks, 2 to 5 tokens, dimensions 1 to 3, a random
    `S_0`: largest relative error `2·10⁻¹⁵` (part B).
- `OneBlockGenericAttention`: `E`, `D` of rank `d`; `W_{Q,i}`, `W_{K,i}`, `W_{V,i}`, `W_{O,i}` of
  rank `d_h`; the queries of all heads and the write of rank `d`; some `v` with the `B_i v`
  nonzero and pairwise non-collinear (`∀ r, B_i v ≠ r • B_j v` for `i ≠ j`) and every `v C_i`
  nonzero. Against the paper's list, one condition is left out: the rank of the keys of all
  heads. Does Step 1 of the paper use it? No. The paper lists it, and then uses: `W_{K,i}^⊤ E^⊤`
  of full row rank (the rank of each `W_{K,i}` and of `E`), "the queries of all heads have rank
  `d_model`" for `η_E = E X`, "`E W_{V,i}` has full column rank and the output projection has
  rank `d_model`" for `η_D = −Y D`, and the full column ranks of `W_Q`, `W_K`, `W_V`, `W_O^⊤` in
  the last step. S says it itself: "Step 1 uses only the queries and the output projection of
  all heads" (Extensions of part (i)). Lean's Step 1 is proved without it. The computation
  agrees: at a parameter with `K_1 = K_2` (`d = 2`, `d_h = 1`, two heads; the keys of all heads
  have rank 1) the directions of Step 1 have dimension 12 `= 2d² + 2Hd_h²` and the two ranks are
  the values of the theorem (parts A'' and E).
- "Some `v`" for "generic `v`": the conditions on `v` are open, so one `v` gives an open set of
  them, which is what Step 2 uses ("This holds for all `v` in an open set").
- `flat_attention_oneBlock_keeps`: for a flat `η`, (8) at Lean's input is the function `G` of
  Lemma C.3 in `u`, with the units `c_i = ½ B_i vᵀ`, the biases `−½ log k`, `a_i = ½ v C_i`, the
  linear term `u (E S_0 D + ∑ C_i)` and the constant `−½ v ∑ C_i`. Lemma C.3 for tanh (which
  allows biases) gives `(D_θ B_i η) vᵀ = 0`, `v (D_θ C_i η) = 0` and
  `D_θ(E S_0 D + ∑ C_i) η = 0`; on an open set of `v` the first two give `D_θ B_i η = 0` and
  `D_θ C_i η = 0`, and then the third gives the first clause. So the statement is the paper's
  Step 2, for any `S_0`.

**5. `OneBlock/AttentionStepOne.lean`.** (By hand.) `cobDir θ X` for one block has `E ↦ E X_0`,
read `↦ −X_0 W_read`, write `↦ W_write X_1`, `D ↦ −X_1 D`. So `X 0` is the paper's `X` and `X 1`
its `Y`, and `cobDir θ X + headDirQK θ Γ + headDirVO θ Γ'` has
`η_E = E X`, `η_Q = −X W_Q + W_Q Γ`, `η_K = −X W_K − W_K Γ^⊤`, `η_V = −X W_V + W_V Γ'`,
`η_O = W_O Y − Γ' W_O`, `η_D = −Y D`: the paper's six formulas, sign for sign. I redid the
paper's argument with the Lean conditions only; every step goes through (note 4).

**6. `OneBlock/AttentionGeneric.lean`.** (By hand.) Each field against the hypotheses: `E` of
rank `d` needs `d_in ≥ d`; `D`, `d_out ≥ d`; the four matrices of a head, `d_h ≤ d`; the queries
of all heads and the write, `H d_h ≥ d`; the `v`: `d ≥ 2` together with `H d_h ≥ d` gives at
least one head and `d_h ≥ 1`, so `(√d_h)⁻¹ ≠ 0`, the `B_i v` are generic vectors of the column
space of `E` (dimension `d ≥ 2`), pairwise non-collinear, and `v C_i ≠ 0`. I looked for a failing
case and found none: for `d_h = d = 2`, `H = 1`, `d_in = d_out = 2` the non-collinearity is
empty, `B` and `C` are invertible `2 × 2` matrices at generic parameters, and the computation
gives the ranks 8 and 12 `= P − 2d² − 2Hd_h²`, `P − d² − 2Hd_h²` with `P = 24` (part A, first
three lines). `d ≥ 2` is needed for two heads or more (with `d = 1` all `B_i v` are collinear).
The statement is now proved under exactly these hypotheses.

**7. `OneBlock/AttentionDim.lean`.** (By reading.) Seven statements, all derived in the file from
Steps 1 and 2, the upper bounds and the generic conditions. Both values of S Theorem B.1 (i) are
there, at one parameter and at almost every parameter, and "the skip raises the functional
dimension by exactly `d_model²`" as `fd_residual = fd_skipless + d²` at almost every parameter.
The computation gives both values on eleven configurations (two, three or four tokens; no mask,
the causal mask, two other masks; `d` from 2 to 4; one to three heads; `H d_h = d` and
`H d_h > d`), with gaps of at least ten orders of magnitude between the last kept and the first
dropped singular value (part A). Not stated from B.1 (i): the values with biases; the equality
condition as a definition (the index says it is written as the equality); "the theorem holds
for inputs in any open set"; the two extensions.

**8. Degenerate cases.** (By hand, before the proofs were in the library; the last line by
compiling.) I looked for a counterexample in the statements that were unproved at `2a488da` and
in those that rested on them.

- No head (`H 0` empty). `eval_attention_oneBlock`, `eval_attention_two_tokens`: both sides are
  the output of `x ↦ x E S_0 D`. `flat_attention_oneBlock_keeps`: `hv` holds for every `v`, and
  the conclusion is `D_θ(E S_0 D) η = 0`, true for a flat `η` (two tokens exist). The statements
  under `OneBlockGenericAttention`: the write has no row, so `rank_write` forces `d` empty.
- Head dimension 0. `B_i = 0` and `C_i = 0` (products through an empty index; also Lean's
  `(√0)⁻¹ = 0`). The two formulas hold; `hv` fails if there is a head, so Step 2 claims nothing;
  `rank_write` again forces `d` empty.
- `d` empty. Every matrix of `θ` is empty, `P = 0`, `fd = 0`, `B_i = C_i = 0`. Then
  `OneBlockGenericAttention θ` holds only with no head (`exists_v`), and the two equalities read
  `0 + 0 = 0`. The `ae_` statements exclude it (`d ≥ 2`).
- One token. Excluded by `t₁ ≠ t₂` wherever it matters; the upper bounds and the symmetries do
  not need two tokens and are true with one. With one token the value of the theorem fails
  (Check 3), so the hypothesis is needed.
- Under `OneBlockGenericAttention θ` with `d` nonempty there is a head and `d_h ≥ 1`
  (`Chk4.lean`), so the structure does not hold by accident in a degenerate case.

None is a counterexample, and the statements are now proved.

**9. The headers of the Lean files against the papers.** (By reading.) The quotations in the
headers of `Symmetry/AttentionHeads.lean`, `Dimension/UpperBoundAttention.lean`,
`OneBlock/Attention.lean`, `OneBlock/AttentionStepOne.lean` and `OneBlock/AttentionGeneric.lean`
are the papers' sentences. Two are not:

- `Network/AttentionAnalytic.lean`, lines 7–9: "Paper (dimension paper), Section 2: the attention
  block is one of the 'analytic blocks'" (note 3).
- `OneBlock/AttentionDim.lean`, lines 13–15: 'Its proof, Step 3: "So `dim K(θ) = 2 d_model² +
  2 H d_h²`, and the functional dimension `P − dim K(θ)` is the value of the theorem."' D's Step 3
  for attention reads "So `dim K(θ) = 2d_model² + 2Hd_h²`, and `s = 2Hd_h²` for an attention
  block."; the sentence "The functional dimension `P − dim K(θ)` is the value of the theorem"
  stands at the end of the count for MLP blocks. The content is right; the quotation joins two
  places.

---------------------------------------------------------------------------------------------------

## What the authors should know

Nothing false, vacuous or drifted. In order of weight:

1. **A wrong citation (a comment and an index row, not a statement).** "Analytic blocks" is the
   skips paper's term (S Section 1.1); the dimension paper's Section 2 does not have it, and its
   "four kinds of block [that] are real-analytic" do not include attention. The header of
   `Network/AttentionAnalytic.lean` and line 681 of the index say "D Section 2, 'analytic
   blocks'". Correction 2.
2. **A joined quotation** in the header of `OneBlock/AttentionDim.lean` (note 9).
3. **The index still says in five places that attention is not there, or only stated** (lines
   444, 480, 529–530, 538, 607). Corrections 3 to 6.
4. **Pre-RMSNorm with `ε = 0`.** The attention bounds "for every real `ε`" count `d(d−1)/2` per
   hidden state. For `ε = 0` this is true but one less per hidden state than the papers' count
   with `CO(d)` (S Theorem A.17 with Lemma A.18). The bound with `CO(d)` and the term `s` of
   attention blocks is not stated in Lean. For `ε < 0` the statement is about a map that no paper
   has. The index row says "(any `ε`)" and no more. Correction 7.
5. **A change of form after the statements were written.** The five theorems of
   `OneBlock/Attention.lean` lost instance arguments that they did not use (`[DecidableEq d]`,
   and `[Fintype dOut]` in three), through `omit … in` lines added with the proofs. Nothing else
   in a statement, a docstring or a header changed between `2a488da` and `169686c`.
6. **A token that sees no token** gets the weights `0` (eleventh audit). The statements of this
   audit hold "for any mask" in this sense; the one-block theorem asks one token that sees itself
   and another, and nothing of the others.
7. **For the papers: Theorems C.1 (D) and B.1 (i) (S) for an attention block hold for every mask
   in which some token sees itself and one other token**, by the papers' own proof; Lean proves
   them so. The papers say "causal or not".
8. **For the papers: Step 1 does not use the rank of the keys of all heads.** Both papers list
   "the keys `[W_{K,1}, …, W_{K,H}]`" among the matrices of rank `d_model`; the argument uses the
   queries and the output projection of all heads and the rank of each `W_{K,i}`. S says so in
   "Extensions of part (i)". Lean's Step 1 is proved without it.
9. **Lean's upper bounds for attention ask less than the papers' Scopes:** `d_h ≤ d` and
   `H d_h ≥ d` in place of `H d_h = d` (and no `H d_h ≥ d` with identity skips), nothing on
   `d_out`, `d ≥ 2`, the mask or the number of tokens, and the heads may differ from block to
   block.
10. **Lemma B.1 for attention is the infinitesimal form** at one parameter; the statement about
    the group is not in Lean, as for the other kinds of block (index, line 438).
11. **Not stated in Lean:** S Theorem B.1 (i) with biases, on an open set of inputs, with a
    position embedding and for grouped-query attention; D Proposition 4.6 and S Proposition 4.5
    for attention blocks; that the output of a network of attention blocks is analytic in the
    weights and the input; a statement that the directions of Step 1 are exactly `K(θ)` (the two
    inclusions are separate statements).

## Corrections for `STATEMENTS.md` (lines of `169686c`)

1. Lines 122–126, "Not yet compared by such a reader": take out
   `Symmetry/AttentionHeads.lean`, `Dimension/UpperBoundAttention.lean`,
   `Network/AttentionAnalytic.lean`, `OneBlock/Attention.lean`, `OneBlock/AttentionStepOne.lean`,
   `OneBlock/AttentionGeneric.lean` and `OneBlock/AttentionDim.lean`; keep
   `Absorb/ShortSequencesPoly.lean` and `Absorb/ShortSequences.lean`. Add a sentence: a twelfth
   reader (part B, 24 November) compared the seven files with D Appendix B, Lemma B.1, Theorem 4.3
   and Theorem 5.1 / C.1 and with S Theorem 4.2, A.17, Lemma A.18 and Theorem B.1 (i) (report
   `claude/lean-statement-audit-twelfth-b-2026-11-24.md`): none false, vacuous or drifted; all
   eight generic statements are `∀ᵐ θ ∂μ`; the one-block statements have the hypotheses of
   Theorem C.1 and hold for every mask with a token that sees itself and another; one statement
   for any stream matrix serves both papers; the statements of `OneBlock/Attention.lean`,
   `OneBlock/AttentionStepOne.lean` and `OneBlock/AttentionGeneric.lean` were judged by hand
   before their proofs were written.
2. Line 681 (`Network/AttentionAnalytic.lean`): replace "(D Section 2, "analytic blocks")" by
   "(S Section 1.1: "These five kinds of block are real-analytic, and we call them analytic
   blocks"; D uses it in the proof of Proposition 4.6, "The outputs are analytic in `θ`")". The
   same in the header of the Lean file, lines 7–9 (a comment in a Lean file, not the index).
3. Line 444, end of the note on Lemma B.1: replace "attention is not." by "and the changes of
   basis inside attention heads (`cobDir_add_headDirQK_add_headDirVO_injective`,
   `Symmetry/AttentionHeads.lean`)."
4. Line 480, note on Theorem 4.3: replace "Not stated: attention blocks." by "For attention
   blocks `s = 2 ∑ H d_h²` (`Dimension/UpperBoundAttention.lean`; these bounds need no `d ≥ 1`)."
5. Lines 529–530: replace "Theorem 5.1 for an attention block is stated in
   `OneBlock/AttentionDim.lean` and the three files it rests on" by "Theorem 5.1 for an attention
   block is proved, `OneBlock/AttentionDim.lean`". Line 538: delete "No attention block is defined
   in Lean yet."
6. Line 607: replace "Theorem 4.6 (i) for attention blocks and with biases" by "Theorem 4.6 (i)
   with biases (for an attention block without biases it is proved,
   `OneBlock/AttentionDim.lean`)".
7. Line 680 (`Dimension/UpperBoundAttention.lean`): after "under pre-RMSNorm (any `ε`)" add "(for
   `ε = 0` this counts `O(d)`, one less per hidden state than the papers' `CO(d)`; the bound with
   `CO(d)` and `s` for attention blocks is not stated)". Optional: "the heads may differ from
   block to block; nothing is asked of `d_out`, the mask or the number of tokens".
8. Line 685 (`OneBlock/AttentionDim.lean`): to "Not stated:" add "inputs in an open set; the
   equality condition as a definition".
9. Line 682 (`OneBlock/Attention.lean`): optional, after "equation (8)" add "((16) of the skips
   paper for `S_0 = 1`)", and after "a flat direction keeps `E S_0 D`" add "(`D_θ M η = 0` of the
   skips paper for `S_0 = 1`)".
10. No correction to lines 679, 683, 684: they describe the Lean statements correctly. The
    status "proved" of the seven rows 679 to 685 agrees with what I compiled (`Chk5.out`).
11. The header of `OneBlock/AttentionDim.lean`, lines 13–15 (a comment, not the index): quote
    Step 3 as it stands, "So `dim K(θ) = 2 d_model² + 2 H d_h²`, and `s = 2 H d_h²` for an
    attention block."

## What I could not check

- I did not run `lake build`. That the files compile and which axioms they use I saw through
  copies of the compiled library of `/home/claude/lp/lean` (same sources as `lw` by `diff -rq`
  at the three times I copied); I built nothing from the sources myself except a copy of
  `OneBlock/AttentionDim.lean`.
- The proofs. I read the statements and definitions, and of the proofs only what fixes the
  meaning of a statement (which hypotheses a proof uses, the counts). I did not read the proofs
  that were merged while I wrote (`OneBlock/Attention.lean`, `OneBlock/AttentionStepOne.lean`,
  `OneBlock/AttentionGeneric.lean`); that their statements did not change I saw from the diff,
  and for three of them from the elaborated forms (`Chk5.out` against `Chk1.out`).
- The computation is in double precision on random draws. It supports the hand computations and
  proves nothing; a rank read from singular values is a judgement (the gaps are in
  `attn_check.out`). The remarks on what happens outside the hypotheses (Check 3) rest on it
  alone; one of the three draws of `attn_check3.py` overflowed and was not used.
- That `rmsNorm ε` is differentiable for `ε > 0`, so that `funDim` is the paper's `fd` there: by
  hand, not compiled for attention.
- The equivalence of the infinitesimal form of Lemma B.1 with the statement about the group: not
  in Lean, and I did not write it out.
- `Absorb/ShortSequences.lean`, `Absorb/ShortSequencesPoly.lean` and the absorb statements on
  attention networks: not in the brief, not compared.
- The texts `dim.txt` and `skips.txt` against the PDFs.
