STATUS: complete

# Fourteenth audit of Lean statements against the papers (24 November 2026)

Reader: an independent reader who did not write the statements. Brief:
`/home/claude/proj_up/audit14_brief_2026-11-24.md`. I audited statements and definitions, not
proofs. I changed no repository file, ran no `lake build`, made no commit and no push.

Library: `/home/claude/lw/lean` (branch `lean-wip`).

- Commit that I audited: `377430e723c196a45e3cdc1beab83f58f76fd2bd` (14:51:09 UTC). I began at
  14:52 UTC and ended at 15:15 UTC.
- Files with `sorry` at that commit: **none** (`grep -rn -w sorry SkipsLean`: no line). No line
  with `axiom`, `opaque`, `admit`, `native_decide` or `unsafe` in the four files either.
- The branch moved once while I worked, to `fd99e23` (15:08:54 UTC). That commit adds six new
  files, all with `sorry` and all outside the brief, with new rows in the index:
  `Network/Sum.lean` (7 `sorry`), `Absorb/RMSNormAttention.lean` (12),
  `Residual/SkiplessEndsAttention.lean` (4), `Residual/DifferentClassesAttention.lean` (6),
  `Residual/BlocksAlone.lean` (6), `Residual/BlocksAloneAttention.lean` (3). It changes
  `STATEMENTS.md` (13 lines) and `SkipsLean.lean` and nothing else: the four files of the brief
  and every file that they import are the same at both commits (`git diff 377430e fd99e23
  --stat`). I did not read the six new files.
- The four files of the brief have 14 public names (3 definitions, 11 theorems) and 49 private
  helpers. All 14 names stand in their index rows, and the 11 theorems stand in
  `checks/Axioms.lean`.
- Did a statement change after it was first committed? No. For each of the 14 public names and
  the four file headers, the text from the docstring to `:=` is the same at the first commit of its
  file (`69432c7` for the two `DepthAttentionRMS…` files, with 2 and 4 `sorry`; `da6c6de` for
  `LocalIdentifiabilityAttentionRMS.lean`, with 3 `sorry`; `377430e` for
  `ExactGainAttention.lean`) and at the audited commit. The only lines removed since are the nine
  `sorry` (by a script, `cmp_statements.py`, and by `git diff`).

Papers, as text: the skips paper ("S", `skips.txt`), the dimension paper ("D", `dim.txt`). Line
numbers of `STATEMENTS.md` are those of `377430e`; each correction quotes the words to change. At
`fd99e23` the lines 148 to 724 lie three lines lower, and the sentences that I quote are the same
there, except the one of correction 1.

How I checked.

- "By reading": I read the four Lean files in full, the definitions they use (`Arch.attention`,
  `attnWeights`, `rmsNorm`, `Params`, `hidden`, `eval`, `funDim`, `Params.smallWrites`,
  `smallWritesLimitNorm`, `headDirQK`, `headDirVO`, `Params.headsQK`, `Params.headsVO`,
  `Params.cob`, `cobDir`, `cobExpHeads`, `antisymmetric`), the statements they import
  (`exists_antisymm_of_smallWritesLimitNorm_rmsNorm`, `attnFamily_rigid`, the four bounds of
  `Dimension/UpperBoundAttention.lean` under pre-RMSNorm, `eval_cob_rmsNorm`,
  `eval_cob_residual_rmsNorm`, `exists_mem_orbit_of_eval_eq`, `ae_funDim_ge`), and the paper
  passages that the brief names.
- "By hand": a short argument of my own, written in the note.
- "By compiling": in `/home/claude/audit14/`, with `lean` 4.36.0 through `LEAN_PATH`, without
  `lake`, against a copy of the compiled library of `/home/claude/lp/lean` taken at 14:52:54 UTC
  (`lp` at the same commit `377430e`; `diff -rq` of the two source trees `SkipsLean/` shows no
  difference). I compiled copies of the four files of the brief from the sources of `lw` into my
  copy of the library (8, 4, 7 and 3 seconds; no error, no warning; `compile4.out`), and then four
  scratch files of my own, `Chk1.lean` to `Chk4.lean` (outputs `Chk*.out`, all without error).
- "By a computation": Python scripts of my own in `/home/claude/audit14/`: `rms_check.py` (numpy,
  double precision, Jacobians in the parameters by the complex step), `rms_check_mp.py` (mpmath,
  110 digits, for the cases that double precision did not decide), `orbit_check.py`. I did not use
  the coordinator's script `attention_depth_rms_check_2026-11-24.py`.

**Short answer. Nothing false, vacuous or drifted was found.** Every "generic" of the seven public
`ae_` statements (and of the five private ones) is `∀ᵐ θ ∂μ` for every additive Haar measure;
Lemma A.27 has the order "for almost every `θ`, for all small `τ ≠ 0`". Every statement uses the
library's `funDim`, and under pre-RMSNorm with `ε > 0` the network is differentiable in the
parameters at every input (compiled), so `funDim` is the paper's `fd`. No main-text statement has a
hypothesis that the Scope does not imply. The case `L = 1` of the Lean Theorem 4.7 is Theorem B.1
(ii) for an attention block (first sentence and gain; compiled as an instance). The conditional
statements are a pointwise form that implies the paper's clause (compiled). All 11 theorems depend
on `propext`, `Classical.choice`, `Quot.sound` only (`Chk1.out`). On 12 small networks inside the
hypotheses the numerical rank is the Lean value in every draw; outside the hypotheses the value
fails for `d_h > d`, for one token and for `d_in < d`, and still holds for `d = 1` in the cases
tried. What needs a correction is the index: it is out of date in five places, and one sentence
(repeated in a file header) says too little about what the papers prove for the skipless network
under pre-RMSNorm.

---------------------------------------------------------------------------------------------------

## Part 1: the drift checks

### Check 1. Generic means almost every parameter, for every Haar measure

**Verdict: yes, in all twelve `ae_` statements of the four files (seven public, five private).
None is "there is a point" or "on an open set". No statement has an a.e. statement as a
hypothesis.** (By reading; the elaborated forms by compiling, `Chk1.out`.)

Each has the shape `(μ : Measure (Params (Arch.attention sees (rmsNorm ε) H dh) dIn dOut))
[μ.IsAddHaarMeasure] … : ∀ᵐ θ ∂μ, …`, with `μ` a variable of the statement (in
`ae_funDim_attention_residual_eq_add_of_skipless` the architecture is `Arch.attention sees id H dh`).

| Statement | The Lean text after the hypotheses |
|---|---|
| `ae_smallWritesGenericAttentionRMS` | `∀ᵐ θ ∂μ, SmallWritesGenericAttentionRMS θ` |
| `ae_eventually_funDim_smallWrites_attention_rmsNorm` | `∀ᵐ θ ∂μ, ∀ᶠ τ in 𝓝[≠] (0 : ℝ), funDim (Arch.attention sees (rmsNorm ε) H dh) 1 (θ.smallWrites τ) + (Fintype.card d * (Fintype.card d - 1) / 2 + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2) = Module.finrank ℝ (Params …)` |
| `ae_funDim_attention_residual_rmsNorm` | `∀ᵐ θ ∂μ, funDim (Arch.attention sees (rmsNorm ε) H dh) 1 θ + (Fintype.card d * (Fintype.card d - 1) / 2 + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2) = Module.finrank ℝ (Params …)` |
| `ae_funDim_attention_residual_rmsNorm_ge_add` | `∀ᵐ θ ∂μ, funDim (Arch.attention sees (rmsNorm ε) H dh) 0 θ + L * (Fintype.card d * (Fintype.card d - 1) / 2) ≤ funDim (Arch.attention sees (rmsNorm ε) H dh) 1 θ` |
| `ae_exists_cob_heads_of_eval_eq_attention_residual_rmsNorm` | `∀ᵐ θ ∂μ, ∀ V ∈ 𝓝 (1 : Matrix d d ℝ), ∀ W ∈ 𝓝 (1 : ∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ), ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U, (∀ x, eval … 1 θ' x = eval … 1 θ x) → ∃ (Q : GL d ℝ) (K K' : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ), (Q : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ ∧ (Q : Matrix d d ℝ) ∈ V ∧ … ∈ W ∧ … ∈ W ∧ θ' = ((θ.headsQK K).headsVO K').cob (fun _ => Q) (fun _ => Q)` |
| `ae_funDim_attention_residual_eq_add_of_skipless` | `∀ᵐ θ ∂μ, funDim (Arch.attention sees id H dh) 0 θ + ((L + 1) * Fintype.card d ^ 2 + 2 * ∑ ℓ, …) = Module.finrank ℝ (Params …) → funDim (Arch.attention sees id H dh) 1 θ = funDim (Arch.attention sees id H dh) 0 θ + L * Fintype.card d ^ 2` |
| `ae_funDim_attention_residual_rmsNorm_eq_add_of_skipless` | `∀ᵐ θ ∂μ, funDim (… (rmsNorm ε) …) 0 θ + ((L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2) + 2 * ∑ ℓ, …) = Module.finrank ℝ (Params …) → funDim (… (rmsNorm ε) …) 1 θ = funDim (… (rmsNorm ε) …) 0 θ + L * (Fintype.card d * (Fintype.card d - 1) / 2)` |

The five private ones (`ae_rank_read_cols_rmd`, `ae_rank_write_rows_rmd`, `ae_rank_read_cols_lir`,
`ae_rank_QV_lir`, `ae_rank_E_lir`) say that a rank is full at almost every parameter, for the same
kind of `μ`.

- **The order in Lemma A.27.** `ae_eventually_funDim_smallWrites_attention_rmsNorm` is "for almost
  every `θ` there is a `δ > 0`, which may depend on `θ`, such that the equality holds for every
  `τ ≠ 0` with `|τ| < δ`". That `∀ᶠ τ in 𝓝[≠] 0, p τ` is `∃ δ > 0, ∀ τ, τ ≠ 0 → |τ| < δ → p τ` I
  compiled (`Chk2.lean` (a)). The paper (S Lemma A.27): "For generic parameters `θ` … and a number
  `τ`, let `θ_τ = …`. For all small `τ ≠ 0`, the residual network has `fd(θ_τ) = P − d_model
  (d_model − 1)/2 − s`". Same order: first the generic `θ`, then the small `τ`. It is the form of
  the statements of Lemma A.27 for the other kinds of block (seventh audit, part A, Check 1;
  thirteenth audit, Check 1).
- The statements at one parameter (`smallWritesLimitNorm_eq_zero_attention_rmsNorm`,
  `eventually_funDim_smallWrites_attention_rmsNorm`, the two `exists_cob_heads_of_eval_eq_…`)
  hold for every `θ` that satisfies written conditions (the structure
  `SmallWritesGenericAttentionRMS`; ranks and the value of `fd`). With their `ae_` companions they
  are the generic claims.
- The only "there is a `θ`" are inside proofs: in `ae_funDim_attention_residual_rmsNorm`, one `θ₀`
  with the conditions and one small `τ`, from which "almost every" follows by `ae_funDim_ge` and
  the upper bound, as in the paper's proof of Theorem 4.7 ("Lemma A.27 gives parameters and a
  finite batch on which it equals `r`"); in `ae_smallWritesGenericAttentionRMS`, a witness at
  which a polynomial in the weights is not zero.
- In the two conditional statements the implication stands inside `∀ᵐ θ ∂μ` (Check 4).
- That an additive Haar measure on `Params` is a Lebesgue measure: sixth audit, Check 1; I did not
  compile it again. That such a measure exists and that the hypotheses of the five final
  statements can all hold at once: `Chk4.lean` instantiates three of them on a concrete network
  with `Measure.addHaar`.

### Check 2. `funDim` is the library's functional dimension

**Verdict: yes, in every statement; and under pre-RMSNorm with `ε > 0` it is the paper's `fd`
with no difference.** (By reading; the differentiability by compiling.)

- The eight statements that speak of a functional dimension
  (`eventually_funDim_smallWrites_attention_rmsNorm`, the last three of
  `Residual/DepthAttentionRMSDim.lean`, the hypothesis `hfd` of the two
  `exists_cob_heads_of_eval_eq_…_attention_rmsNorm`, and the two of
  `Residual/ExactGainAttention.lean`) use `funDim (Arch.attention sees χ H dh) S θ` of
  `Dimension/Functional.lean`: the largest rank of the Jacobian in `θ` over all `n` and all
  batches `X : Fin n → Matrix T dIn ℝ` (sixth audit, Check 2), with the set of tokens `T` fixed
  and all real `T × d_in` inputs. None uses `jacobianRank` or another quantity in its place.
  `S = 1` is the residual network and `S = 0` the skipless one: for one block,
  `eval … 1 θ x = rmsNorm ε (x * θ.E + f (rmsNorm ε (x * θ.E) * θ.read 0) * θ.write 0) * θ.D`, and
  with `0` the term `x * θ.E` is absent (compiled, `Chk2.lean` (l)). The skip reads `h` and the
  block and the readout read `N_ε(h)`, as in S Section 2.
- **Differentiability.** Mathlib's `fderiv` is `0` where a map is not differentiable, so `funDim`
  drops the batches that contain an input at which the network is not differentiable in `θ`
  (sixth audit). Here nothing is dropped: for `ε > 0`, every mask and all stream matrices,
  `θ ↦ eval (Arch.attention sees (rmsNorm ε) H dh) S θ x` is differentiable at every `x`, and so
  is the map of every batch (compiled, `Chk2.lean` (b), (b'), from `differentiable_eval`,
  `differentiable_f_attention` and `analyticOnNhd_rmsNorm`). So `funDim` is the paper's
  `fd(θ) = max_X rank DF_X(θ)` word for word, for the residual and for the skipless network.

### Check 3. No extra hypotheses in the main-text statements

**Verdict: none. Every Lean hypothesis is implied by the paper's Scope, and several are weaker.**

**(a) S Theorem 4.7 under pre-RMSNorm, attention blocks.** The Lean text (by compiling,
`Chk1.out`):

```
ae_funDim_attention_residual_rmsNorm : ∀ {T d dIn dOut} {L : ℕ} [Fintype T] [Fintype d]
  [DecidableEq d] [Fintype dIn] [Fintype dOut] {sees : T → T → Prop} [DecidableRel sees]
  {H dh : Fin L → Type} [(ℓ : Fin L) → Fintype (H ℓ)] [(ℓ : Fin L) → Fintype (dh ℓ)] {ε : ℝ},
  0 < ε → ∀ (μ : Measure (Params (Arch.attention sees (rmsNorm ε) H dh) dIn dOut))
  [μ.IsAddHaarMeasure], 2 ≤ Fintype.card d → Fintype.card d ≤ Fintype.card dIn →
  Fintype.card d ≤ Fintype.card dOut → (∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) →
  (∀ ℓ, 0 < Fintype.card (dh ℓ)) → ∀ (t₁ t₂ : T), t₁ ≠ t₂ → sees t₂ t₂ → sees t₂ t₁ →
  ∀ᵐ θ ∂μ, funDim (Arch.attention sees (rmsNorm ε) H dh) 1 θ
      + (Fintype.card d * (Fintype.card d - 1) / 2
        + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
    = Module.finrank ℝ (Params (Arch.attention sees (rmsNorm ε) H dh) dIn dOut)
```

| Paper (S Section 2, Scope; Theorem 4.7) | Lean | Verdict |
|---|---|---|
| "RMSNorm with the constant `ε > 0`"; "under RMSNorm means in a pre-RMSNorm network" | `hε : 0 < ε`, `χ = rmsNorm ε` | same |
| "`d_in, d_out ≥ d_model ≥ 2`" | `hd`, `hdIn`, `hdOut` | same |
| "All attention blocks have the same number `H` of heads, of total width `H d_h = d_model`" | `1 ≤ d_h ≤ d` in every block (`hdh0`, `hdh`); any numbers of heads, which may differ from block to block and may be `0` | Lean asks less: `H d_h = d ≥ 2` gives `1 ≤ d_h ≤ d` (compiled, `Chk2.lean` (e)) |
| "act on sequences of at least two tokens" (S Lemma A.27, Theorem B.1: "causal or not") | a relation `sees` and two tokens `t₁ ≠ t₂` with `sees t₂ t₂`, `sees t₂ t₁` | Lean asks less; the causal mask on `Fin (n + 2)` and "no mask" on at least two tokens are instances (compiled, `Chk2.lean` (d)) |
| "Networks have no biases, and their inputs range over all of `ℝ^{T×d_in}`" | no biases in `Params`; `funDim` ranges over all real inputs | same |
| "at generic parameters its functional dimension is `P − dim 𝒢 − s`", `dim 𝒢 = d(d−1)/2` under RMSNorm, `s = 2 H d_h²` per block | `fd + (d(d−1)/2 + 2 ∑_ℓ H_ℓ d_{h,ℓ}²) = P` | same |

- **The division.** `Fintype.card d * (Fintype.card d - 1) / 2` is `(d · (d − 1)) / 2` in natural
  numbers (`*` and `/` associate to the left). `d (d − 1)` is even, so the division is exact:
  `2 * (n * (n - 1) / 2) = n * (n - 1)` for every `n` (compiled, `Chk2.lean` (h)). The value is
  written as `fd + (…) = P`, with no subtraction of natural numbers.
- The statement goes beyond the Scope (heads of total width other than `d`, different heads from
  block to block). It is the generality of S Lemma A.27 ("in any order and of any width … heads
  of width at most `d_model`"). By the computation (`rms_check.out`, part A): on 12 networks, two
  random draws each, among them two with `H d_h < d`, one with `H d_h > d`, one with a block
  without heads, one with different heads in its two blocks, three masks, `ε = 0.01, 0.3, 1`, and
  one, two and three blocks, the rank at a random parameter is `P − d(d−1)/2 − s` in all 24
  draws (gaps of at least `4 · 10¹⁰` in the singular values).

**(b) "The skips raise the functional dimension by at least `L dim 𝒢`".**
`ae_funDim_attention_residual_rmsNorm_ge_add` has the hypotheses of (a) and
`hH : ∀ ℓ, Fintype.card d ≤ Fintype.card (H ℓ) * Fintype.card (dh ℓ)`. It is the paper's
hypothesis, in two places: the Scope ("of total width `H d_h = d_model`"), and the proof of
Theorem 4.7, "The gain. When every block has width at least `d_model`, the functional dimension
of the skipless network is at most `P − (L + 1) dim 𝒢 − s`", where "the width of an attention
block is `H d_h`" (S Theorem B.1). The conclusion compares the two networks at the same `θ`, for
almost every `θ`. By the computation: in the cases with `H d_h ≥ d` the difference of the two
ranks is `L d(d−1)/2` exactly (1, 1, 3, 2, 2, 6, 1, 3, 2); in the two cases with `H d_h < d` it
is larger (7 against 2; 20 against 6 in the one draw whose skipless rank double precision
decided), and with a block without heads the skipless network is the zero function. I saw no
case in which the hypothesis is needed for the truth of the inequality; the proof needs it.

**(c) S Theorem 4.6 (ii) for an attention block.** S Theorem B.1 (ii): "Let the network be
pre-RMSNorm with `ε > 0`, without biases. For generic parameters the residual network has
functional dimension `P − d_model (d_model − 1)/2 − s`, which is the equality condition. If the
block has width at least `d_model`, the skip raises the functional dimension by at least
`d_model (d_model − 1)/2`", for "an attention block of `H` heads of width `d_h ≤ d_model`, causal
or not, on sequences of at least two tokens", `d_model ≥ 2`, `d_in, d_out ≥ d_model`.

**Yes, the case `L = 1` of the two Lean statements is this.** By compiling (`Chk2.lean` (c)): for
`H dh : Fin 1 → Type`, with `d_h ≤ d`, `d_h ≥ 1` and the two tokens,

```
(∀ᵐ θ ∂μ, funDim … 1 θ + (card d * (card d - 1) / 2 + 2 * (card (H 0) * card (dh 0) ^ 2))
    = Module.finrank ℝ (Params …))
∧ (card d ≤ card (H 0) * card (dh 0) →
    ∀ᵐ θ ∂μ, funDim … 0 θ + card d * (card d - 1) / 2 ≤ funDim … 1 θ)
```

follows from `ae_funDim_attention_residual_rmsNorm` and `…_ge_add`. The hypotheses are those of
Theorem B.1 (`d_h ≥ 1` is implicit in the paper; the mask is weaker). Three remarks:

- It is an instance, not a named statement, and the index does not mention Theorem 4.6 (ii) or
  B.1 (ii) in the row of `Residual/DepthAttentionRMSDim.lean` (correction 4).
- The third sentence of Theorem 4.6 (ii), "A learned skip raises it by exactly
  `d_model (d_model + 1)/2` more than an identity skip" (B.1 (iii)), is not stated for an
  attention block.
- Lean reaches the one-block value by the route of Lemma A.27 (small writes). The paper's own
  proof of B.1 (ii) describes the flat directions at `θ` itself (Steps 4 and 5); that description
  of `K(θ)` is not a Lean statement for an attention block (for tanh, GELU and gated blocks it is,
  `OneBlock/ResidualRMSMlp.lean`, `OneBlock/ResidualRMSGated.lean`). By the computation
  (`orbit_check.out`): at a random `θ` the kernel of the Jacobian of the residual network is the
  span of the directions of one antisymmetric `Y` at all hidden states and of the heads, of
  dimension `d(d−1)/2 + s`, in the three cases tried.

**(d) S Corollary 4.9 under pre-RMSNorm.** The paper: "let `θ` be generic parameters of the
residual network. Every `θ′` near `θ` with the same function is obtained from `θ` by symmetries
inside the blocks and by one matrix `G ∈ 𝒢`, all close to the identity. The matrix `G` is the
same at all hidden states: for every block `ℓ`, `E ↦ E G`, `W_read^ℓ ↦ G⁻¹ W_read^ℓ`,
`W_write^ℓ ↦ W_write^ℓ G`, `D ↦ G⁻¹ D`", with `𝒢 = O(d_model)` under RMSNorm with `ε > 0`.
`ae_exists_cob_heads_of_eval_eq_attention_residual_rmsNorm` has exactly the hypotheses of (a) and
the conclusion quoted in Check 1.

| Paper | Lean | Verdict |
|---|---|---|
| "generic parameters of the residual network" | `∀ᵐ θ ∂μ`, `eval … 1` | same |
| "Every `θ′` near `θ` with the same function" | `∃ U ∈ 𝓝 θ, ∀ θ' ∈ U, (∀ x, eval … 1 θ' x = eval … 1 θ x) → …` | same |
| "one matrix `G ∈ 𝒢`", `𝒢 = O(d)` | one `Q : GL d ℝ` with `(Q : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ`, which is `Q * Qᵀ = 1` (compiled, `Chk2.lean` (g)) | same |
| "The matrix `G` is the same at all hidden states" with the four maps | `cob (fun _ => Q) (fun _ => Q)`, which is `E * Q`, `Q⁻¹ * read ℓ`, `write ℓ * Q`, `Q⁻¹ * D` (compiled, `Chk2.lean` (g), by `rfl`) | same |
| "symmetries inside the blocks" | `θ.headsQK K` and `.headsVO K'`: `(W_Q, W_K) ↦ (W_Q K, W_K K^{-⊤})`, `(W_V, W_O) ↦ (W_V K', K'⁻¹ W_O)` in every head | same; no permutation of heads, which is not needed near `θ` |
| "all close to the identity" | for all neighbourhoods `V` of `1` and `W` of `1`: `Q ∈ V`, `K ∈ W`, `K' ∈ W` | same |

By the computation (`orbit_check.out`, three networks): one orthogonal `Q` at all hidden states
with changes of basis inside the heads keeps the function of the residual network (`2 · 10⁻¹⁴` at
most); different orthogonal `Q_ℓ` change it (0.2 to 6); one `G` that is not orthogonal changes it
(0.3 to 6).

### Check 4. The conditional statements of `Residual/ExactGainAttention.lean`

**Verdict: the hypothesis is a faithful form of "when the skipless network satisfies the equality
condition too". It is stated at the parameter `θ`, inside "for almost every `θ`"; this form
implies the paper's clause, and for almost every `θ` it says no more than the paper's clause.**

The Lean text (pre-RMSNorm; the other statement is the same with `id` and `card d ^ 2`):

```
theorem ae_funDim_attention_residual_rmsNorm_eq_add_of_skipless (hε : 0 < ε) (μ …)
    [μ.IsAddHaarMeasure] (hd : 2 ≤ card d) (hdIn : card d ≤ card dIn) (hdOut : card d ≤ card dOut)
    (hdh : ∀ ℓ, card (dh ℓ) ≤ card d) (hdh0 : ∀ ℓ, 0 < card (dh ℓ))
    (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ θ ∂μ,
      funDim (Arch.attention sees (rmsNorm ε) H dh) 0 θ
          + ((L + 1) * (card d * (card d - 1) / 2) + 2 * ∑ ℓ, card (H ℓ) * card (dh ℓ) ^ 2)
        = Module.finrank ℝ (Params …) →
      funDim (Arch.attention sees (rmsNorm ε) H dh) 1 θ
        = funDim (Arch.attention sees (rmsNorm ε) H dh) 0 θ + L * (card d * (card d - 1) / 2)
```

The paper: "So the skips raise the functional dimension by at least `L dim 𝒢`, and by exactly
`L dim 𝒢` when the skipless network satisfies the equality condition too", where (Definition 4.3)
"A network satisfies the equality condition if its bound in Theorem 4.2 is attained at generic
parameters".

- **The paper's clause is** "if `fd_skipless(θ) = P − (L+1) dim 𝒢 − s` for almost every `θ`, then
  `fd_res(θ) = fd_skipless(θ) + L dim 𝒢` for almost every `θ`". **Lean's statement is** "for
  almost every `θ`: if `fd_skipless(θ) = P − (L+1) dim 𝒢 − s` at this `θ`, then
  `fd_res(θ) = fd_skipless(θ) + L dim 𝒢` at this `θ`".
- **Lean's form gives the paper's.** By compiling (`Chk2.lean` (f) under pre-RMSNorm, `Chk3.lean`
  (a) without normalization): from the Lean statement and the hypothesis
  `∀ᵐ θ ∂μ, fd_skipless(θ) + … = P` follows `∀ᵐ θ ∂μ, fd_res(θ) = fd_skipless(θ) + L dim 𝒢` (two
  sets of full measure intersect).
- **The hypothesis at one `θ` is the equality condition.** By compiling (`Chk2.lean` (f')): for
  `H d_h ≥ d` in every block, if `fd_skipless(θ₀) + ((L+1) d(d−1)/2 + s) = P` at ONE parameter
  `θ₀`, then the same equality holds at almost every parameter (`ae_funDim_ge` and the upper
  bound `ae_funDim_add_le_skipless_attention_rmsNorm`). So the bound is attained at one point if
  and only if it is attained generically, and outside a set of measure zero the hypothesis of the
  Lean statement is true at `θ` exactly when the skipless network satisfies the equality
  condition.
- **What is claimed.** At almost every `θ` (those at which the residual network has the value of
  Theorem 4.7): if the skipless network attains its bound at `θ`, the difference of the two
  functional dimensions is exactly `L dim 𝒢`. The proof is Theorem 4.7 and arithmetic.
- **What is not claimed.** (1) That the skipless network attains its bound at any parameter. The
  papers prove this for one attention block without normalization (D Theorem 5.1; S Theorem B.1
  (i)), and there the hypothesis holds at almost every `θ` when `H d_h ≥ d`, so the Lean statement
  gives the exact gain `d²` (compiled, `Chk3.lean` (b)). For two or more attention blocks, and
  under pre-RMSNorm for any number of attention blocks, including one, the papers do not prove it
  (S after Theorem B.1: "In part (ii), for the skipless network we prove here only the bound
  `P − d_model (d_model − 1) − s` of Theorem A.17 (ii), which our checks attain"). If the
  skipless network does not attain its bound, the Lean statement is true and says nothing.
  (2) Anything at the parameters of the exceptional set. (3) A width condition: the statements do
  not ask `H d_h ≥ d`. Without it the paper's bound for the skipless network is not available
  (Lemma A.18), and by the computation the skipless rank is then below the "bound" formula (12
  against 17; 25 against 39), so the hypothesis fails and the statement is empty there.
- **Not vacuous in practice.** By the computation (`rms_check.out`, `rms_check_mp.out`): under
  pre-RMSNorm, in every case with `H d_h ≥ d` the skipless rank at a random parameter is
  `P − (L+1) d(d−1)/2 − s`: for one block (18, 14, 42, 30), two blocks (29, 31, 60, and 29 with
  the mask in which only one token sees another) and three blocks (40). For the last two cases
  double precision decided one of its two draws and gave no clear gap in the other; two new
  draws of each with mpmath at 110 digits give 29 and 40 again, with gaps of `10⁸⁷` and more.
- The docstrings and the header say what the statements are ("at almost every parameter, if the
  skipless network has `fd = P − (L + 1) d(d−1)/2 − s`, the residual network has exactly
  `L d(d−1)/2` more"). One sentence of the header says too little (note 7).

---------------------------------------------------------------------------------------------------

## Part 2: the statements, file by file

### Verdict table

All rows are proved at `377430e` (compiled by me from the sources; three standard axioms), and
the four files are the same at `fd99e23`.

| Paper statement or proof piece | Lean | Verdict | Difference | How checked |
|---|---|---|---|---|
| S proof of B.1 (ii), Step 4: "Step 2 for attention blocks, with `E` and `D` replaced by the identity": the matrices `B_i`, `C_i` | `headScoreModel`, `headValueModel` | SAME | `(√d_h)⁻¹ • (W_Q W_K^⊤)` and `W_V W_O`, the four matrices taken from block `ℓ`: the paper's `B_i = E W_Q W_K^⊤ E^⊤/√d_h`, `C_i = E W_V W_O D` with `E = D = I` | reading; compiling (`Chk2` (i)) |
| S Lemma A.27 and its proof "Under pre-RMSNorm", attention blocks: the conditions on `θ` | `SmallWritesGenericAttentionRMS` | SAME | `E`, `D` of rank `d`; the four matrices of every head of rank `d_h`; one `v ∈ ℝ^d` for the heads of all blocks together (note 2) | reading; by hand |
| S proof of A.27, "Under pre-RMSNorm": the flat directions of `J_0`, attention blocks | `smallWritesLimitNorm_eq_zero_attention_rmsNorm` | SAME | One inclusion (flat implies this form), for networks all of whose blocks are attention blocks. `Y` antisymmetric, signs and head directions as in the paper (note 3). Step 4 by another route (note 3) | by hand; computation |
| S Lemma A.27, second value, attention blocks | `eventually_funDim_smallWrites_attention_rmsNorm`, `ae_eventually_funDim_smallWrites_attention_rmsNorm` | PART | Networks of attention blocks only; the lemma also allows MLP blocks among them. Within that: same value, same order of `θ` and `τ`; heads may differ from block to block; the mask is weaker | reading; by hand; computation |
| S Lemma A.27, "For generic parameters" | `ae_smallWritesGenericAttentionRMS` | SAME | `d_in, d_out ≥ d ≥ 2`, `1 ≤ d_h ≤ d`; nothing on tokens, mask or `ε` (note 5) | reading; by hand |
| **S Theorem 4.7**, attention blocks under pre-RMSNorm: the value | `ae_funDim_attention_residual_rmsNorm` | LEAN STRONGER | Check 3 (a): weaker than the Scope in the heads and the mask. Networks that mix attention and MLP blocks are not stated | reading; compiling; computation |
| S Theorem 4.7: "at least `L dim 𝒢`" | `ae_funDim_attention_residual_rmsNorm_ge_add` | SAME | Check 3 (b) | reading; computation |
| **S Theorem 4.6 (ii)** / B.1 (ii) for an attention block | the case `L = 1` of the two rows above (an instance, not a named statement) | PART | First sentence and gain: SAME as B.1 (ii). The sentence on a learned skip is not stated. Check 3 (c) | compiling (`Chk2` (c)); computation |
| S Theorem 4.7: "by exactly `L dim 𝒢` when the skipless network satisfies the equality condition too" | `ae_funDim_attention_residual_eq_add_of_skipless`, `ae_funDim_attention_residual_rmsNorm_eq_add_of_skipless` | LEAN STRONGER in form | The hypothesis is at the parameter `θ`; it implies the paper's clause. Attention blocks only. Check 4 | reading; compiling (`Chk2` (f), (f'), `Chk3`) |
| D Proposition 4.6, attention blocks under pre-RMSNorm (skipless) | `exists_cob_heads_of_eval_eq_skipless_attention_rmsNorm` | PART | One direction (from the equality condition to local identifiability), at one parameter. The equality is a hypothesis that the papers prove for no number of attention blocks (note 6) | reading; by hand; computation |
| S Proposition 4.5, attention blocks under pre-RMSNorm (residual) | `exists_cob_heads_of_eval_eq_residual_attention_rmsNorm` | PART | The same direction, at one parameter, with one orthogonal `Q` at all hidden states | reading; by hand; computation |
| **S Corollary 4.9**, attention blocks under pre-RMSNorm | `ae_exists_cob_heads_of_eval_eq_attention_residual_rmsNorm` | LEAN STRONGER | Check 3 (d); the hypotheses of Theorem 4.7, weaker than the Scope | reading; compiling (`Chk2` (g), `Chk4` (d)); computation |

### Notes

**1. `headScoreModel`, `headValueModel`.** (By reading; `Chk2.lean` (i), by `rfl`.)

```
noncomputable def headScoreModel (θ : Params (Arch.attention sees χ H dh) dIn dOut) (ℓ : Fin L)
    (i : H ℓ) : Matrix d d ℝ :=
  (Real.sqrt (Fintype.card (dh ℓ)))⁻¹ •
    (((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k))
      * ((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inl k)))ᵀ)
def headValueModel … : Matrix d d ℝ :=
  ((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k)))
    * ((θ.write ℓ).submatrix (fun k : dh ℓ => (i, k)) id)
```

`Sum.inl k` are the query columns, `Sum.inr (Sum.inl k)` the key columns, `Sum.inr (Sum.inr k)`
the value columns of head `i` (`Network/Attention.lean`), and the rows `(i, k)` of the write are
`W_{O,i}`. So these are `W_Q W_K^⊤/√d_h` and `W_V W_O`, the `d × d` matrices through which block
`ℓ` acts on its normalized input `n`: `f_ℓ(n W_read^ℓ) W_write^ℓ = ∑_i P(n Γ_i n^⊤) n C_i`. They
are the twins `headScore`, `headValue` of `Residual/DepthAttention.lean` without `E`, `E^⊤` and
`D`, which is what "with `E` and `D` replaced by the identity" says. For `d_h = 0` Lean's
`(√0)⁻¹` is `0` and the first matrix is `0`.

**2. `SmallWritesGenericAttentionRMS` against the hypotheses of the proof.** (By reading; by
hand.) The lemma's hypotheses: "`d_model ≥ 2`, `E` and `D` have rank `d_model`, … an attention
block with heads of width at most `d_model`, causal or not, on sequences of at least two tokens
… For generic parameters". Its proof under pre-RMSNorm runs Steps 1 to 5 of B.1 (ii). What they
use, and the field of the structure:

| The proof uses | Field |
|---|---|
| Step 1: "the row space of `D`, which has dimension `d_model`"; "`D` has full row rank" | `rank_D : θ.D.rank = card d` |
| Step 2: "`Y_s = 0` because `E` has rank `d_model`"; Step 3: `w η′_E = 0` on an open set; Step 4: "the image of `x ↦ N_ε(xE)` … is the open ball … since `E` has rank `d_model`" | `rank_E : θ.E.rank = card d` |
| Step 4: "Step 2 for attention blocks, with `E` and `D` replaced by the identity and `M = 0`", which needs "for generic parameters and generic `v` the vectors `B_i v^⊤` are nonzero and pairwise non-collinear … and every `v C_i` is nonzero"; for the heads of all blocks ("let the heads of all attention blocks form one attention block") | `exists_v`: one `v : d → ℝ` with `headScoreModel θ p.1 p.2 *ᵥ v ≠ 0` for every `p : Σ ℓ, H ℓ`; `≠ r • (headScoreModel θ q.1 q.2 *ᵥ v)` for all `p ≠ q` and all real `r`; `v ᵥ* headValueModel θ p.1 p.2 ≠ 0` |
| Step 4: "by Step 1 there, `η′` is a direction of the changes of basis inside the heads", which needs "`P_1` and `P_2` have full column rank" for `(W_Q, W_K)` and for `(W_V, W_O^⊤)` | `rank_Q`, `rank_K`, `rank_V`, `rank_O`: each of rank `card (dh ℓ)` |

- `v` lies in `ℝ^d` (in the twin without normalization it lies in `ℝ^{d_in}`, since there `B` is
  `d_in × d_in`). "Generic `v`" is "some `v`": the conditions are open in `v`, and the proof of
  `attnFamily_rigid` needs one (thirteenth audit, note 8).
- `B_p *ᵥ v` is the column `B_p v^⊤` and `v ᵥ* C_p` the row `v C_p`: in (16) the tanh unit of head
  `i` has, as a function of `u`, the input weights `½ B_i v^⊤` and the output weights `½ v C_i`.
- The pairs `p ≠ q` range over the heads of all blocks together, in the same block or not. This
  is what "the units of all blocks together" asks.
- Not asked, and rightly: "the queries of all heads have rank `d_model`" and "the output
  projection has rank `d_model`" of Step 1 for one block. There they serve to find `η_E = E X` and
  `η_D = −Y D`; here `E` and `D` are replaced by the identity and do not move, so Step 1 starts
  from `η_Q W_K^⊤ + W_Q η_K^⊤ = 0`. This is why the lemma holds for heads "of any width".
- The structure does not hold by accident in a degenerate case: under it, every block that has a
  head has `d_h ≥ 1` (compiled, `Chk2.lean` (j)); with two heads in all it forces `d ≥ 2`.

**3. `smallWritesLimitNorm_eq_zero_attention_rmsNorm`, recomputed by hand for one block and one
head.** The Lean statement: for `ε > 0`, tokens `t₁ ≠ t₂` with `sees t₂ t₂`, `sees t₂ t₁`, `θ`
with the structure, and `η` with `smallWritesLimitNorm … θ η x = 0` at every `x`:

```
∃ (Y : Matrix d d ℝ) (Γ Γ' : ∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ),
  Yᵀ = -Y ∧ η.E = θ.E * Y ∧ η.D = -(Y * θ.D)
    ∧ (∀ ℓ, η.read ℓ = (headDirQK θ Γ + headDirVO θ Γ').read ℓ)
    ∧ (∀ ℓ, η.write ℓ = (headDirQK θ Γ + headDirVO θ Γ').write ℓ)
```

*The limit.* `smallWritesLimitNorm A θ η x` is, by `rfl` (`Chk2.lean` (k)),
`𝐃N_ε(h)(x η_E + D_θ g(n) η) D + N_ε(h) η_D` with `h = x E`, `n = N_ε(h)` and
`D_θ g(n) η = ∑_ℓ (𝐃f_ℓ(n R_ℓ)(n η_{R,ℓ}) W_ℓ + f_ℓ(n R_ℓ) η_{W,ℓ})`: the paper's formula. By
hand it is the limit: `F_{θ_τ}(x) = N_ε(xE) D + τ 𝐃N_ε(xE)(g(n)) D + O(τ²)`; the derivative of
the first term along `(η_E, η_D)` is `𝐃N_ε(h)(x η_E) D + N_ε(h) η_D`, and the derivative of the
coefficient of `τ` along the reads and writes is `𝐃N_ε(h)(D_θ g(n) η) D`. By the computation
(`rms_check.out`, all 24 draws of part A): `|J_τ S_τ − J_0| / |J_0|` is between `2.8 · 10⁻⁴`
and `6.6 · 10⁻³` at `τ = 10⁻³` and ten times smaller at `τ = 10⁻⁴`.

*One block, one head.* `g(n) = P(n Γ n^⊤) n C` with `Γ = W_Q W_K^⊤/√d_h`, `C = W_V W_O`, and
`D_θ g(n) η` is the derivative at `τ = 0` of `P(n Γ(τ) n^⊤) n C(τ)` along
`Γ(τ) = (W_Q + τ η_Q)(W_K + τ η_K)^⊤/√d_h`, `C(τ) = (W_V + τ η_V)(W_O + τ η_O)`, with
`Γ̇ = (η_Q W_K^⊤ + W_Q η_K^⊤)/√d_h`, `Ċ = η_V W_O + W_V η_O`. Let `η` be flat, and write
`k = x η_E + D_θ g(n) η`.

- *Step 1.* `D` has full row rank. Split `η_D = −Y D + Z` with `Z D^⊤ = 0`. Then
  `(𝐃N_ε(h) k − N_ε(h) Y) D + N_ε(h) Z = 0`; multiplying on the right by `D^⊤ (D D^⊤)⁻¹` gives
  `𝐃N_ε(h) k = N_ε(h) Y` and then `N_ε(h) Z = 0` for all `x`. The rows `N_ε(x_t E)` span `ℝ^d`
  (`E` has rank `d`), so `Z = 0` and `η_D = −Y D`. For one row `v` with `ρ² = |v|²/d + ε`:
  `𝐃N_ε(v) k = k/ρ − v ⟨v, k⟩/(d ρ³)`, which is injective for `ε > 0`, and the solution of
  `𝐃N_ε(v) k = (v/ρ) Y` is `k = v Y + μ v` with `μ (d ρ² − |v|²) = v Y v^⊤`, that is
  `μ = v Y_s v^⊤/(d ε)`, `Y_s = ½(Y + Y^⊤)`. As in the paper.
- *Step 2.* At `x = t w` with `w_s E ≠ 0` at every token, `n` stays in the ball of radius `√d`,
  so `D_θ g(n) η` is bounded, and `k_s = t w_s η_E + O(1)`, while the right side is
  `t w_s E Y + t³ (w_s E Y_s E^⊤ w_s^⊤) w_s E/(d ε)`. So `w_s E Y_s E^⊤ w_s^⊤ = 0` on an open set,
  `E Y_s E^⊤ = 0`, and `Y_s = 0` since `E` has full column rank. `Y` is antisymmetric: Lean's
  `Yᵀ = -Y`.
- *Step 3.* Now `x η_E + D_θ g(n) η = x E Y`. At `x = t w` the terms of order `t` give
  `w (η_E − E Y) = 0` on an open set, so `η_E = E Y`: Lean's `η.E = θ.E * Y`, and
  `η.D = -(Y * θ.D)` from Step 1. Then `D_θ g(n) η = 0` at every `n = N_ε(x E)`. No term
  `−Y W_read` appears in the reads and no `W_write Y` in the writes, and that is right for `J_0`:
  "the direction `η^Y` has the entries `E Y` at `E` and `−Y D` at `D` and no others, since
  `𝐃N_ε(h)(hY) = N_ε(h) Y` for antisymmetric `Y`".
- *Step 4.* The `n = N_ε(xE)` fill a neighbourhood of `0` (every token ranges over the open ball),
  and `n ↦ D_θ g(n) η` is real-analytic, so it vanishes for all `n ∈ ℝ^{T×d}`. Take `n` with the
  row `u` at `t₂` and `u − v` at every other token; let `k ≥ 1` be the number of other tokens
  that `t₂` sees. The output at `t₂` is `u C − ½ v C + ½ tanh(½(u Γ v^⊤ − log k)) v C` (equation
  (16) with `M = 0`), and its derivative along `η` is, with `z = ½(u Γ v^⊤ − log k)`,
  `u Ċ − ½ v Ċ + ½ tanh(z) v Ċ + ¼ sech²(z) (u Γ̇ v^⊤) v C = 0` for all `u`. Let `c = Γ v^⊤ ≠ 0`
  and `a = v C ≠ 0`. For `u = s c^⊤/|c|² + u_⊥`, `u_⊥ c = 0`: `z` depends on `s` only, so the part
  linear in `u_⊥` vanishes for every `s`: `u_⊥ Ċ + ¼ sech²(z)(u_⊥ Γ̇ v^⊤) a = 0`; `sech²` is not
  constant, so `u_⊥ Ċ = 0` and `u_⊥ Γ̇ v^⊤ = 0`. On the line `u_⊥ = 0`, letting `s → +∞` and
  `s → −∞` gives `c^⊤ Ċ = 0` and `v Ċ = 0`, and what is left gives `c^⊤ Γ̇ v^⊤ = 0`. So `Ċ = 0`
  and `Γ̇ v^⊤ = 0`; the conditions on `v` are open, so `Γ̇ = 0`. Hence, as `1/√d_h ≠ 0`,
  `η_Q W_K^⊤ + W_Q η_K^⊤ = 0` and `η_V W_O + W_V η_O = 0`. With `W_Q`, `W_K`, `W_V`, `W_O^⊤` of
  full column rank: `η_Q = W_Q Γ_1` with `Γ_1 = −η_K^⊤ (W_K^+)^⊤`, then `η_K = −W_K Γ_1^⊤`; and
  `η_V = W_V Γ'`, `η_O = −Γ' W_O`. The paper: "`η_{Q,i} = W_{Q,i} Γ_i`, `η_{K,i} = −W_{K,i} Γ_i^⊤`,
  `η_{V,i} = W_{V,i} Γ′_i`, `η_{O,i} = −Γ′_i W_{O,i}`".
- *Lean's conclusion for the reads and writes*, entry by entry (compiled, `Chk2.lean` (i)): the
  query columns of `(headDirQK θ Γ + headDirVO θ Γ').read ℓ` are `W_Q Γ`, the key columns
  `−W_K Γ^⊤`, the value columns `W_V Γ'`, the rows of the write `−Γ' W_O`, and its `E` and `D`
  are `0`. Signs as in the paper.

*Route.* The paper passes from the ball to all inputs "along every line through the ball"; Lean
uses that the range of `N_ε` is open (`isOpenMap_rmsNorm`) and contains `0`, and the identity
theorem on the connected space of all `n`. The header of the file says so. The statement is the
same.

*By the computation* (`rms_check.out`, part A, 24 draws): the kernel of `J_0` on a batch has the
dimension `d(d−1)/2 + 2 ∑ H d_h²`; the directions of the Lean conclusion (`E Y`, `−Y D` for
antisymmetric `Y`, and the head directions) lie in it (`|J_0 S| ≤ 4 · 10⁻¹⁵`) and span a space of
the same dimension; the rank of the Jacobian at `θ_τ` is `P − d(d−1)/2 − s` for
`τ = 10⁻², 10⁻³, −10⁻²` (gaps of `2 · 10⁷` to `4 · 10¹²`).

**4. `eventually_funDim_smallWrites_attention_rmsNorm` against the second value.** (By reading.)
`∀ᶠ τ in 𝓝[≠] 0, funDim … 1 (θ.smallWrites τ) + (card d * (card d - 1) / 2 + 2 * ∑ ℓ, card (H ℓ)
* card (dh ℓ) ^ 2) = finrank …`, for every `θ` with the structure. The paper: "`fd(θ_τ) = P −
d_model (d_model − 1)/2 − s` pre-RMSNorm with `ε > 0`, no biases". `θ.smallWrites τ` is `θ` with
the writes `τ • θ.write ℓ`. Same value. The statement has no hypothesis `d ≥ 2`: the structure
carries what is needed. For `d = 1` with one head in all, the structure can hold, and the value
`P − 2` is then what the computation gives (4 and 6 in the two cases tried). The upper bound
inside the proof is taken at `θ_τ`, where `E` and the reads are those of `θ`.

**5. `Residual/DepthAttentionRMSDim.lean`: is `SmallWritesGenericAttentionRMS θ` true at almost
every `θ` under exactly these hypotheses?** Yes. (By reading; by hand; the statement is proved.)
The hypotheses of `ae_smallWritesGenericAttentionRMS` are `2 ≤ card d`, `card d ≤ card dIn`,
`card d ≤ card dOut`, `∀ ℓ, card (dh ℓ) ≤ card d`, `∀ ℓ, 0 < card (dh ℓ)`; nothing on the tokens,
the mask or `ε`, which the structure does not mention.

- By hand: each field is "a polynomial in the weights is not zero" for finitely many
  polynomials, none identically zero. `E` (`d_in × d`) and `D` (`d × d_out`) have rank `d` at
  some parameter because `d_in, d_out ≥ d`; each of `W_Q`, `W_K`, `W_V` (`d × d_h`) and `W_O`
  (`d_h × d`) has rank `d_h` at some parameter because `d_h ≤ d`; with `v = (1, …, 1)`, `B_p v`
  and `v C_p` are not zero at some parameter because `d_h ≥ 1`; and for `p ≠ q` the vectors
  `B_p v`, `B_q v` depend on different weights and are not collinear at some parameter because
  `d ≥ 2`.
- Is each hypothesis needed for this statement? `d_in ≥ d` and `d_out ≥ d`: yes, else `rank_E` or
  `rank_D` holds at no `θ`. `d_h ≤ d` and `d_h ≥ 1`: yes for a block that has a head (else a rank
  condition, or `B_p v ≠ 0`, holds at no `θ`); for a block without heads they are asked and not
  needed. `d ≥ 2`: needed as soon as the network has two heads in all.
- Are they needed for the truth of the final value? By the computation (`rms_check.out`, part B;
  `rms_check_mp.out`):

  | Outside the hypotheses | Lean value | Rank found | |
  |---|---|---|---|
  | `d_h > d`: `d = 2`, one head of width 3 | 13 | 15 | the value fails: `fd` is larger by `2 ∑ H (d_h − d)²` |
  | `d_h > d`: `d = 2`, blocks of 1 and 2 heads of width 3 | 25 | 31 | the same |
  | `d_h > d`: `d = 3`, two heads of width 4 | 47 | 51 | the same |
  | one token, `d = 2`, one block of two heads of width 1 | 19 | 11 | the value fails: the scores do not matter |
  | one token, two such blocks | 31 | 15 | the same |
  | two tokens, each sees itself only | 19 | 11 | the same |
  | `d_in = 1 < d = 2` | 17 | 11 | the value fails |
  | `d_out = 1 < d = 2` | 17 | 17 | the value holds in this case |
  | `d = 1`, one head in all (`d_in = d_out = 1`, and `= 2`) | 4, 6 | 4, 6 | the value holds |
  | `d = 1`, one block of two heads | 8 | 8 (double precision in one draw, no clear gap in the other; mpmath in two new draws) | the value holds |
  | `d = 1`, two blocks of one head, three tokens, no mask | 8 | 8 (double precision, two draws; mpmath, one new draw) | the value holds |
  | `d = 1`, blocks of 3 and 2 heads | 14 | 14 (mpmath, one draw; double precision gave no clear gap) | the value holds |

  So `d_h ≤ d`, the token that sees itself and another, and `d_in ≥ d` are needed for the value.
  `d ≥ 2` is the paper's hypothesis and is needed for the proof (with `d = 1` all `B_p v` are
  collinear), but I found no case with `d = 1` in which the value fails.
- The four statements. `ae_smallWritesGenericAttentionRMS`: above.
  `ae_eventually_funDim_smallWrites_attention_rmsNorm`: Lemma A.27, second value, Check 1.
  `ae_funDim_attention_residual_rmsNorm`: Check 3 (a). `…_ge_add`: Check 3 (b). A concrete
  instance (`Chk4.lean`): for two tokens with the causal mask, `d = d_in = d_out = 2`, one block
  of two heads of width 1 and `ε = 3/10`, the library gives `P = 24`, a parameter with
  `funDim … 1 θ = 19`, and a parameter with `funDim … 0 θ + 1 ≤ funDim … 1 θ`. The computation on
  this network: 19 and 18 (double precision, two draws; mpmath, one draw, gaps of `10⁹⁸` and
  more).
- For `L = 0` the statement of Theorem 4.7 says that `x ↦ N_ε(xE) D` has `fd = P − d(d−1)/2`. It
  still asks for the two tokens, which it then does not need.

**6. `Residual/LocalIdentifiabilityAttentionRMS.lean`.** (By reading; by hand.)

- *Orthogonality.* Skipless: `∃ (Q : Fin (L + 1) → GL d ℝ) …, (∀ ℓ, (Q ℓ : Matrix d d ℝ) ∈
  Matrix.orthogonalGroup d ℝ) ∧ … ∧ θ' = ((θ.headsQK K).headsVO K').cob Q Q`: one orthogonal
  matrix per hidden state, `E Q_0`, `Q_{ℓ−1}⁻¹ W_read^ℓ`, `W_write^ℓ Q_ℓ`, `Q_L⁻¹ D`
  (`Params.cob`). Residual: one `Q` with `(Q : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ` and
  `cob (fun _ => Q) (fun _ => Q)`. This is `𝒢 = O(d)` of the papers for `ε > 0` (D Proposition
  3.2; S Theorem 3.3 (i), Lemma A.4). In the proofs `Q = exp m` with `m` antisymmetric.
- *The neighbourhoods.* `∀ V ∈ 𝓝 1, ∀ W ∈ 𝓝 1, ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U, …` with `Q ∈ V` (as a family
  of matrices for the skipless network, as one matrix for the residual one), `K ∈ W`, `K' ∈ W`:
  "Every symmetry that is needed is then close to the identity". One `W` serves `K` and `K'`;
  nothing is lost. The forms are those of the twins without normalization (thirteenth audit,
  note 7) with one clause more, the orthogonality.
- *Which direction.* From the equality condition to local identifiability only, at one
  parameter: the hypothesis `hfd` is `fd(θ) + k = P` at this `θ`, with
  `k = (L + 1) d(d−1)/2 + s` without skips and `d(d−1)/2 + s` with them. The converse is not
  stated; the header and the index say so. The paper's direction "equality condition implies
  local identifiability at generic parameters" follows, since the ranks asked hold almost
  everywhere.
- *The rank hypotheses.* Skipless: `E` and every write of rank `d`, the query and the value
  matrix of every head of rank `d_h`; a write of rank `d` needs `H d_h ≥ d`. Residual: `E` and
  the query and value matrices only. These are the conditions under which the symmetries move
  `θ` in independent directions (D Lemma B.1; S Lemma A.18: "For an attention block … these have
  full column rank, as `d_h ≤ d_model` … The write … has rank `d_model`, as `H d_h ≥ d_model`").
- *True as written?* By hand: the family `(m, Γ, Γ') ↦ cobExpHeads θ (m, Γ, Γ')` with `m_ℓ`
  antisymmetric (one `m` for the residual network) passes through `θ`, keeps the function
  (`eval_headsQK`, `eval_headsVO`, and `N_ε(hQ) = N_ε(h) Q` for orthogonal `Q`), and its
  derivative `cobDir θ m + headDirQK θ Γ + headDirVO θ Γ'` is injective under the ranks asked
  (`E m_0 = 0` gives `m_0 = 0`; then the query and value columns give `Γ`, `Γ'`; then the writes
  give `m_ℓ`). Its domain has the dimension `k`. So `exists_mem_orbit_of_eval_eq` applies.
- *Not vacuous.* For the residual network `hfd` holds almost everywhere (Theorem 4.7), which is
  the third statement; a concrete instance compiles (`Chk4.lean` (d)). For the skipless network
  under pre-RMSNorm `hfd` is not a result of the papers for any number of attention blocks, not
  even one (Check 4). By the computation it holds at random parameters in every case with
  `H d_h ≥ d` that I tried, for one, two and three blocks (Check 4), and there the kernel of the
  Jacobian is the span of the directions of the statement (`orbit_check.out`: dimensions 11 and
  33). With `H d_h < d` it fails (kernel of dimension 29 against 15).
- No statement "at almost every parameter" exists for a skipless network under pre-RMSNorm (the
  twin without normalization has one for one block). That is as it should be.

**7. `Residual/ExactGainAttention.lean`.** Check 4. The header: "Whether the skipless network of
`L ≥ 2` attention blocks attains its bound is not proved in the papers; for one block without
normalization it does (`OneBlock/AttentionDim.lean`)." True, and silent on one block under
pre-RMSNorm, where the papers do not prove it either. A reader of this sentence, and of the index
row that repeats its first half, can take the case of one block under pre-RMSNorm for proved.

**8. The headers.** (By reading, against `skips.txt` and `dim.txt`.) The quotations in the four
headers are the papers' sentences: Lemma A.27 ("For all small `τ ≠ 0`, the residual network has
[…] `fd(θ_τ) = P − d_model (d_model − 1)/2 − s`", "pre-RMSNorm with `ε > 0`, no biases"); its
proof ("this is the equation of the proof of Theorem B.1 (ii) with `h_1 = x E` and `D_θ h_1 η = x
η_E + D_θ g(n) η`, and its Steps 1 to 5 go through", where the paper goes on "with three
changes"); "with `E` and `D` replaced by the identity"; Theorem 4.7 in full. The header of
`Residual/DepthAttentionRMS.lean` says how Step 4 is done in Lean.

---------------------------------------------------------------------------------------------------

## What the authors should know

Nothing false, vacuous or drifted. In order of weight:

1. **The index is out of date in five places** (corrections 1 to 3, 5 to 7): it still lists the
   four files as "not yet compared"; its paragraph "Not stated yet from the main text of the skips
   paper" still names the clause "by exactly `L dim 𝒢` …" as a conditional statement, Theorem 4.6
   (ii) for attention blocks, "Corollary 4.9 for attention blocks" and "Corollary 4.10", all of
   which are now stated at least in part; the row of `Residual/DepthAttentionDim.lean` still says
   that the clause is not stated; the rows of `OneBlock/ResidualRMSGain.lean` and
   `Residual/DepthMlp.lean` still say "Not stated: … attention blocks".
2. **One sentence says too little** (correction 8; note 7): "Whether the skipless network of two
   or more attention blocks attains its bound is not proved in the papers". Under pre-RMSNorm the
   papers do not prove it for one attention block either. The same holds for the hypothesis of
   `exists_cob_heads_of_eval_eq_skipless_attention_rmsNorm`: it is an equality that the papers
   prove for no number of attention blocks, and its index row does not say so.
3. **Theorem 4.6 (ii) for an attention block is in Lean only as the case `L = 1`** of the two
   statements for any depth (compiled as an instance). No statement and no index row names it.
   Its sentence on a learned skip is not stated for an attention block, and neither is the
   description of the flat directions at `θ` itself (Steps 4 and 5 of B.1 (ii)).
4. **The conditional statements have the hypothesis at the parameter `θ`.** This form implies the
   paper's clause, and where `H d_h ≥ d` "attained at one parameter" and "attained at almost every
   parameter" are the same (both compiled). They do not ask `H d_h ≥ d`; without it they are true
   and empty.
5. **By the computation the skipless network under pre-RMSNorm attains its bound** in every case
   with `H d_h ≥ d` that I tried (one, two and three blocks). So the conditional statements and
   the skipless statement on local identifiability are not empty in practice, and the gain is
   exactly `L d(d−1)/2` there. This is a computation on random draws, not a proof.
6. **Lemma A.27, Theorem 4.7 and Corollary 4.9 are stated for networks of attention blocks
   only.** The paper's lemma also covers networks that mix attention and MLP blocks. (As without
   normalization; the index says it.)
7. **Lean's Theorem 4.7 asks less than the Scope:** heads of width `1 ≤ d_h ≤ d`, any numbers of
   heads (different from block to block, also none in a block), any total width, any mask with a
   token that sees itself and another. The computation agrees in the cases outside the Scope that
   I tried.
8. **Which hypotheses the value needs** (by the computation): `d_h ≤ d` (for `d_h > d` the
   functional dimension is larger than the formula by `2 ∑ H (d_h − d)²`), a token that sees
   another token, and `d_in ≥ d`. For `d = 1` and for `d_out < d` the value held in the cases
   tried; the paper has `d_model ≥ 2` and `d_out ≥ d_model`, and the proof uses both.
9. **No statement changed after it was first committed** (the nine `sorry` were replaced by
   proofs; statements, docstrings and headers are the same).
10. Six files appeared while I worked (`fd99e23`), all with `sorry` and outside the brief:
    `Network/Sum.lean`, `Absorb/RMSNormAttention.lean`, `Residual/SkiplessEndsAttention.lean`,
    `Residual/DifferentClassesAttention.lean`, `Residual/BlocksAlone.lean`,
    `Residual/BlocksAloneAttention.lean`. No reader has compared them.

## Corrections for `STATEMENTS.md` (lines of `377430e`)

1. Lines 145–147 (at `fd99e23`: lines 145–150), "Not yet compared by such a reader (written after
   the thirteenth audit began): `Residual/DepthAttentionRMS.lean`,
   `Residual/DepthAttentionRMSDim.lean`, `Residual/LocalIdentifiabilityAttentionRMS.lean` and
   `Residual/ExactGainAttention.lean`" (at `fd99e23` followed by "; and (written after the
   fourteenth audit began) `Network/Sum.lean`, …"): take the four files out of the list, keep the
   six new ones, and add a sentence: a fourteenth reader (24 November) compared these four files with Lemma
   A.27 (second value), Theorems 4.6 (ii), 4.7, B.1 (ii), Proposition 4.5 and Corollary 4.9 of the
   skips paper and with Proposition 4.6 of the dimension paper (report
   `claude/lean-statement-audit-fourteenth-2026-11-24.md`) and found nothing false, vacuous or
   drifted: all seven generic statements are `∀ᵐ θ ∂μ`, Lemma A.27 in the form "for almost every
   `θ`, for all small `τ ≠ 0`"; under pre-RMSNorm with `ε > 0` the network is differentiable in
   the parameters at every input, so `funDim` is the paper's `fd`; the case `L = 1` is Theorem B.1
   (ii) for an attention block; the conditional statements imply the paper's clause; no statement
   changed after its first commit.
2. Lines 631–633, "Theorem 4.6 (ii) for ReLU, ReLU², ReGLU and attention blocks and its sentence
   on a learned skip (its first sentence and the gain are proved for tanh, GELU, SwiGLU and GeGLU
   blocks);": write "Theorem 4.6 (ii) for ReLU, ReLU² and ReGLU blocks, and its sentence on a
   learned skip for every kind of block (its first sentence and the gain are proved for tanh,
   GELU, SwiGLU and GeGLU blocks, and for an attention block as the case `L = 1` of
   `Residual/DepthAttentionRMSDim.lean`);".
3. Lines 634–644. (a) "the clause of Theorem 4.7 "by exactly `L dim 𝒢` when the skipless network
   satisfies the equality condition too" as a conditional statement, and Lemma A.27, …": the
   clause is now stated for attention blocks. Write "the clause of Theorem 4.7 "by exactly
   `L dim 𝒢` …" as a conditional statement for blocks other than attention blocks (for attention
   blocks it is stated, with the hypothesis at the parameter, `Residual/ExactGainAttention.lean`;
   for tanh, GELU, SwiGLU and GeGLU blocks its instances are Corollary 4.8), and Lemma A.27, …".
   (b) "Corollary 4.9 for attention blocks without normalization,
   `Dimension/LocalIdentifiabilityAttention.lean`": add "and under pre-RMSNorm,
   `Residual/LocalIdentifiabilityAttentionRMS.lean`". (c) Lines 642–644, "; Corollary 4.9 for
   attention blocks (it is proved for tanh, GELU, SwiGLU and GeGLU blocks, … as in the Lean
   Theorem 4.7); Corollary 4.10;": these two items are left over from before; they contradict the
   parenthesis of lines 636–640. Delete "Corollary 4.9 for attention blocks" and "Corollary
   4.10;" and keep the parenthesis on the four kinds of MLP block as a remark.
4. Line 720 (`Residual/DepthAttentionRMSDim.lean`), additions: "the case `L = 1` is Theorem 4.6
   (ii) / B.1 (ii) for an attention block, first sentence and gain (its sentence on a learned skip
   is not stated)"; "a block may have no head; a head of width `0` is excluded"; "Not stated:
   networks that mix attention and MLP blocks".
5. Line 718 (`Residual/DepthAttentionDim.lean`): in "Not stated: Corollary 4.10 (ii) (no embedding
   and no readout); the clause "by exactly `L dim 𝒢` when the skipless network satisfies the
   equality condition too"; networks that mix …" replace the middle item by "(the clause "by
   exactly `L dim 𝒢` …": `Residual/ExactGainAttention.lean`)".
6. Line 594 (`OneBlock/ResidualRMSGain.lean`): "Not stated: Theorem 4.6 (ii) for ReLU, ReLU²,
   ReGLU and attention blocks, and its sentence on a learned skip (B.1 (iii))": write "Not stated:
   Theorem 4.6 (ii) for ReLU, ReLU² and ReGLU blocks, and its sentence on a learned skip (B.1
   (iii)); for an attention block: the case `L = 1` of `Residual/DepthAttentionRMSDim.lean`".
7. Line 598 (`Residual/DepthMlp.lean`): "Not stated: attention blocks": write "Attention blocks:
   the rows of `Residual/DepthAttentionDim.lean` and `Residual/DepthAttentionRMSDim.lean`".
8. Line 721 (`Residual/ExactGainAttention.lean`): "Whether the skipless network of two or more
   attention blocks attains its bound is not proved in the papers": write "Whether the skipless
   network attains its bound is not proved in the papers for two or more attention blocks, nor
   under pre-RMSNorm for one attention block (S after Theorem B.1: "for the skipless network we
   prove here only the bound"); for one block without normalization it is
   (`OneBlock/AttentionDim.lean`)". Additions: "the hypothesis is at the parameter `θ`, and the
   statement implies the paper's clause; no width `H d_h ≥ d` is asked". The same sentence in the
   header of the Lean file could be completed in the same way (a matter for the coordinator; I edit no
   file).
9. Line 724 (`Residual/LocalIdentifiabilityAttentionRMS.lean`), additions: after "for skipless
   networks (`fd = P − (L+1) d(d−1)/2 − s`" add "; `E` and the writes of rank `d`, query and
   value matrices of rank `d_h`", and after "for residual networks (`fd = P − d(d−1)/2 − s`" add
   "; `E` of rank `d`, query and value matrices of rank `d_h`"; add "For skipless networks under
   pre-RMSNorm the equality is a hypothesis that the papers prove for no number of attention
   blocks; no permutation of heads is needed".
10. Line 719 (`Residual/DepthAttentionRMS.lean`), additions: "all blocks are attention blocks (the
    paper's lemma also allows MLP blocks among them: not stated)"; "the statement on the flat
    directions is one inclusion; the ranks of the queries of all heads and of the write are not
    asked, since `E` and `D` are replaced by the identity"; "Step 4 passes from a neighbourhood of
    `0` to all `n` by the identity theorem".
11. Lines 549–553 (dimension paper, "Not stated yet from the main text"): after "for attention
    blocks without normalization Proposition 4.6 is proved in the same direction, at one
    parameter, and at almost every parameter for one block,
    `Dimension/LocalIdentifiabilityAttention.lean`" add "; under pre-RMSNorm with `ε > 0` at one
    parameter, `Residual/LocalIdentifiabilityAttentionRMS.lean`".
12. Lines 619–621, "Proposition 4.5 (one direction) and Corollary 4.9 of the skips paper stand in
    the table of the dimension paper above, beside their twins (…)": add "; for attention blocks
    in the rows of `Dimension/LocalIdentifiabilityAttention.lean` and
    `Residual/LocalIdentifiabilityAttentionRMS.lean`, in the table of the absorb paper".
13. No correction to the names and the status of the four rows (lines 719, 720, 721, 724): each
    row lists exactly the public names of its file, and "proved" agrees with what I compiled.

## What I could not check, or did not

- The proofs: not audited, as the brief says. I read of them what fixes the meaning of a
  statement (which hypotheses are used, which imported statements are called).
- I did not run `lake build`. I compiled copies of the four files from the sources of `lw`
  against a copy of the compiled library of `/home/claude/lp/lean`. That this library was built
  from the sources of the same commit I took from the brief and from `diff -rq` of the two source
  trees; I did not compare source hashes with the build traces of the imported modules.
- That an additive Haar measure on `Params` is a Lebesgue measure: taken from the sixth report.
- The computations are on random draws, in double precision or with mpmath at 110 digits; a rank
  read from singular values is a judgement (the gaps are in the output files). They support the
  hand arguments and prove nothing. In double precision the skipless rank was not decided in
  three draws of part A (no ratio of consecutive singular values above `10⁶`); for two of these
  cases I computed new draws with mpmath, the third (`H d_h < d`, `ε = 1`) I left. The remarks on `d = 1`,
  `d_out < d` and `H d_h < d` rest on one to three draws each.
- The texts `skips.txt` and `dim.txt` against the PDFs.
- Networks that mix attention and MLP blocks, the converse directions of Propositions 4.5 and
  4.6, `ε = 0`, a learned skip with an attention block, and the flat directions at `θ` itself for
  one attention block under pre-RMSNorm: not stated in the four files, so there was nothing to
  compare.
- The other rows of the index, beyond the sentences that name the four files or attention
  blocks.
- The six files that appeared at `fd99e23` while I worked, and their index rows. By their index
  rows they state, with `sorry`, among other things Corollary 4.10 (ii) and Theorem 4.11 (i) of
  the skips paper for attention blocks and networks with two kinds of block; the paragraph "Not
  stated yet from the main text of the skips paper" (corrections 2 and 3) will need these too. No
  reader has compared them.
- I could not write this report into the project: it is the local file
  `/home/claude/proj_up/lean-statement-audit-fourteenth-2026-11-24.md` only.

Scratch files: `/home/claude/audit14/` (`compile4.sh`, `compile4.out`; `Chk1.lean` to `Chk4.lean`
and their outputs; `cmp_statements.py`, `rms_check.py`, `rms_check_mp.py`, `orbit_check.py` and
their outputs; `lib/`, the copy of the compiled library; `src/`, the copy of the sources).
