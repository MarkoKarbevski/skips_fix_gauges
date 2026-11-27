STATUS: complete

# Tenth audit of Lean statements against the papers, part B (24 November 2026)

Reader: an independent reader who did not write the statements. Brief:
`/home/claude/proj_up/audit10b_brief_2026-11-24.md`. Scratch folder: `/home/claude/audit10b/`.

Paper: the skips paper as text (`skips.txt`; statement and equation numbers from that text).

## Commit, and the files with `sorry`

The branch `lean-wip` of `/home/claude/lw` moved while I read. Three commits matter.

| Commit of `/home/claude/lw` | Time (UTC) | Files of `SkipsLean/` with `sorry` (`git grep`, whole library) |
|---|---|---|
| `4eb217a` (first read) | 12:51 | `OneBlock/ResidualRMSReGLU.lean` (7), `Residual/SmallParameterOn.lean` (1), `Residual/SmallWritesOn.lean` (2), `Residual/DepthRescale.lean` (8) |
| **`92a4512` (the commit of this report)** | 12:57 | `Residual/SmallWritesOn.lean` (2), `Residual/DepthRescale.lean` (8), `Residual/DepthReGLU.lean` (7, a new file) |
| `d4c1e26` (head when I finished) | 13:03 | `Residual/DepthReGLU.lean` (7), `Absorb/InjectiveBlocks.lean` (6, not my subject) |

All statements below are quoted from `92a4512` (a copy made with `git archive`, in
`/home/claude/audit10b/snap/`). Between `4eb217a` and `92a4512` no statement of my files changed
(by a script that compares every public statement up to `:= by`; only proofs were added). Between
`92a4512` and `d4c1e26` the public statements of `SmallWritesOn.lean` and `DepthRescale.lean` have
the same text; one of them, `eventually_jacobianRank_ge_of_contDiffOn`, lost the unused instance
`[DecidableEq d]` (`omit … in`), which makes it slightly more general.

`Residual/DepthReGLU.lean` (Lemma A.30 for ReGLU blocks) did not exist when the brief was written.
It is part of the same lemma, so I compared it too.

How I checked. "By reading": I read the Lean source and the paper. "By compiling": one scratch file,
`/home/claude/audit10b/Chk.lean` (output `Chk.out`), compiled with `lean` 4.36.0 against a copy of
the compiled library of `/home/claude/lp/lean` taken at 13:02 (`/home/claude/audit10b/lib/`); the
sources of `lp` at that time (`41ce476`) had the same public statements as `92a4512` in all seven
files that have a compiled form (by the script). I did not run `lake`, and I wrote nothing under
`lw`, `lp` or the repository. "By a computation": Python scripts in `/home/claude/audit10b/py/`.
"By hand": a derivation that I wrote out while reading.

## Short answer

**Nothing false and nothing vacuous was found. One statement says less than the paper's sentence,
and the index does not say so; one hypothesis of Lean is missing in the text of the paper's
lemma.**

1. *Lemma A.30, second sentence, on the open set `U`.* Lean states the value of the library's
   `funDim` on `U`, and nothing else there. The batch "on which no pre-activation vanishes" is stated
   at the parameters `θ_τ` only. So on `U` Lean gives the paper's functional dimension as an upper
   bound, not as a value, and the gain on `U` is in the library's sense only. The index's own note
   says that for ReLU-type blocks "neither alone is the paper's statement". A clause for the batch
   at the points of `U` would close this (see "What the authors should know", 1).
2. *`d_model ≥ 2` in Lemma A.30.* Lean has `2 ≤ Fintype.card d`. The text of Lemma A.30 does not;
   Lemma A.27 and the Scope of Section 2 do. The hypothesis is needed: for `d_model = 1` and two
   hidden units the count of the lemma fails (by hand and by a computation). So Lean is right, and
   the paper's lemma should say it.
3. Everything else is the paper's statement, or stronger in a harmless way: the batch of
   Lemma A.30 is chosen before `τ`; Lemma A.3 holds without the hypothesis on the hidden states and
   for any matrix `S`.
4. By compiling: all 36 public theorems of the seven files other than `DepthReGLU.lean` depend on
   `propext`, `Classical.choice`, `Quot.sound` only, in the library of `lp` at `41ce476`. This
   includes the ten statements of `SmallWritesOn.lean` and `DepthRescale.lean` that are `sorry` at
   `92a4512`. `DepthReGLU.lean` is not compiled anywhere that I found; I judged its seven
   statements true by hand.

---------------------------------------------------------------------------------------------------

## Part 1: drift checks

### Check 1. Generic means almost every parameter

**Verdict: yes, in all 17 statements. No hypothesis beyond the paper's, except "at least one token",
which the paper has implicitly, and `d_model ≥ 2` in Lemma A.30, which the paper's lemma needs and
does not write.**

By reading the eight files, and by compiling for the elaborated form of nine of them (`Chk.out`).
Every generic claim is `∀ᵐ θ ∂μ` with `(μ : Measure (Params …)) [μ.IsAddHaarMeasure]`, `μ` a
variable of the statement. One of them in elaborated form:

```
ae_funDim_relu_oneBlock_residual_rmsNorm : ∀ {T d dIn dOut} [Fintype T] [Nonempty T] [Fintype d]
  [DecidableEq d] [Fintype dIn] [Fintype dOut] {hid : Fin 1 → Type} [(ℓ : Fin 1) → Fintype (hid ℓ)] {ε : ℝ},
  0 < ε →
  ∀ (μ : Measure (Params (Arch.mlp relu (rmsNorm ε) hid) dIn dOut)) [μ.IsAddHaarMeasure],
  2 ≤ Fintype.card d → Fintype.card d ≤ Fintype.card dIn → Fintype.card d ≤ Fintype.card dOut →
  ∀ᵐ θ ∂μ, funDim (Arch.mlp relu (rmsNorm ε) hid) 1 θ
      + (Fintype.card d * (Fintype.card d - 1) / 2 + Fintype.card (hid 0))
    = Module.finrank ℝ (Params (Arch.mlp relu (rmsNorm ε) hid) dIn dOut)
```

**Theorem B.1 (ii).** Paper: "Let `d_model ≥ 2`, let the input and output dimensions be at least
`d_model`, let inputs range over all of `ℝ^{T×d_in}` … (ii) Let the network be pre-RMSNorm with
`ε > 0`, without biases. For generic parameters the residual network has functional dimension
`P − d_model (d_model − 1)/2 − s` … If the block has width at least `d_model`, the skip raises the
functional dimension by at least `d_model (d_model − 1)/2`."

| Lean hypothesis | In the paper | Statements |
|---|---|---|
| `[Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut]`, `hid : Fin 1 → Type`, `[∀ ℓ, Fintype (hid ℓ)]` | finite sets of tokens, coordinates and hidden units; one block | all ten |
| `[Nonempty T]` | not said; an input has at least one token | all ten |
| `hε : 0 < ε` | "pre-RMSNorm with `ε > 0`" | all but `ae_oneBlockGenericReGLURMS` (the conditions do not involve `ε`) |
| `(μ) [μ.IsAddHaarMeasure]`, conclusion `∀ᵐ θ ∂μ` | "for generic parameters" | all ten |
| `hd : 2 ≤ card d`, `hdIn : card d ≤ card dIn`, `hdOut : card d ≤ card dOut` | "`d_model ≥ 2`, input and output dimensions at least `d_model`" | all ten |
| `hhid : ∀ ℓ, card d ≤ card (hid ℓ)` | "If the block has width at least `d_model`" | only the three gains |

The ten: `ae_funDim_relu_oneBlock_residual_rmsNorm`,
`ae_exists_jacobianRank_relu_oneBlock_residual_rmsNorm`,
`ae_funDim_skipless_add_le_relu_oneBlock_residual_rmsNorm`, the same three with `reluSq`
(`OneBlock/ResidualRMSRescale.lean`), `ae_oneBlockGenericReGLURMS`,
`ae_funDim_reglu_oneBlock_residual_rmsNorm`,
`ae_exists_jacobianRank_reglu_oneBlock_residual_rmsNorm`,
`ae_funDim_skipless_add_le_reglu_oneBlock_residual_rmsNorm` (`OneBlock/ResidualRMSReGLU.lean`).
No bias appears anywhere in `Params`. The value statements have no hypothesis on the width.

**Lemma A.30.** Paper: "Let the blocks be ReLU, ReLU² or ReGLU blocks, without normalization or
biases, let `E` and `D` have rank `d_model`, and let inputs range over all of `ℝ^{1×d_in}`, or over
an open set that contains `0`. For generic parameters `θ` … For all small `τ ≠ 0` … at almost every
point of this set the skips add at least `L d_model²` when every block has width at least
`d_model`."

| Lean hypothesis | In the paper | Statements |
|---|---|---|
| the instances above, with `hid : Fin L → Type`; `[Nonempty T]` | finite sets; any `L`; the paper takes one token, Lean any nonempty finite set of tokens | all seven |
| `(μ) [μ.IsAddHaarMeasure]`, `∀ᵐ θ ∂μ` | "for generic parameters `θ`" | all seven (inside the conclusion in the three `exists_isOpen_…`) |
| `hdIn`, `hdOut` | "let `E` and `D` have rank `d_model`": a generic `E ∈ ℝ^{d_in×d}` has rank `d` exactly when `d_in ≥ d`, and the same for `D` | all seven |
| `hd : 2 ≤ card d` | **not in the text of Lemma A.30.** It is in Lemma A.27 ("Let `d_model ≥ 2`", and Lemma A.30 says "as in Lemma A.27" only for `θ_τ`) and in the Scope of Section 2 | all seven |
| `∀ᶠ τ in 𝓝[≠] (0 : ℝ)` | "for all small `τ ≠ 0`": some `τ_0 > 0`, which may depend on `θ`, and every `τ` with `0 < |τ| < τ_0` | six (not `ae_smallWritesGenericReGLU`) |
| `(∀ ℓ, card d ≤ card (hid ℓ)) →`, inside the last clause | "when every block has width at least `d_model`" | only the gain |

The seven: `ae_exists_eventually_jacobianRank_smallWrites_relu`, `…_reluSq`,
`exists_isOpen_funDim_smallWrites_relu`, `…_reluSq` (`Residual/DepthRescale.lean`),
`ae_smallWritesGenericReGLU`, `ae_exists_eventually_jacobianRank_smallWrites_reglu`,
`exists_isOpen_funDim_smallWrites_reglu` (`Residual/DepthReGLU.lean`).

*Is `2 ≤ card d` a hypothesis that the paper does not have?* In the text of the lemma, yes; in
substance, no. For `d_model = 1` every hidden state is a number, a residual ReLU block is
`h ↦ h + τ ∑_i max(h r_i, 0) w_i`, a map with one slope for `h > 0` and one for `h < 0`, and so is
every composition of such blocks for small `τ`. The network is then `x ↦ a_± (xE) D` with two
numbers `a_+`, `a_−`: at most `d_in + d_out` degrees of freedom, whatever the number of hidden
units. With two hidden units in all, `P − d² − s = d_in + d_out + 1`. So the count of Lemma A.30
fails at every `θ_τ` (by hand). By a computation (`py/a30_check.py`, ranks of Jacobians on batches
off the kinks, `τ = 0.05`): for ReLU with `(d_in, d, d_out) = (1, 1, 1)` the rank is 2 against 3,
with `(3, 1, 3)` it is 6 against 7, for one block of two units and for two blocks of one unit. For
ReLU² and `d = 1` (`py/d1_sq.py`, one block of two units) it fails where the two reads have the
same sign, an open set of weights (rank 2 against 3, and 6 against 7), and holds where they have
opposite signs. So Lean's hypothesis is necessary, and **the paper's Lemma A.30 should begin "Let
`d_model ≥ 2`"**, as Lemma A.27 does.

*The order of the quantifiers in Lemma A.30.*

```
theorem ae_exists_eventually_jacobianRank_smallWrites_relu (μ …) [μ.IsAddHaarMeasure]
    (hd : 2 ≤ Fintype.card d) (hdIn : …) (hdOut : …) :
    ∀ᵐ θ ∂μ, ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i, X i ∈ noKinkAll θ) ∧
      ∀ᶠ τ in 𝓝[≠] (0 : ℝ),
        (∀ (i : Fin n) (ℓ : Fin L) (t : T) (j : hid ℓ),
          (hidden (Arch.mlp relu id hid) 1 (θ.smallWrites τ) (X i) ℓ.castSucc * θ.read ℓ) t j ≠ 0) ∧
        jacobianRank (Arch.mlp relu id hid) 1 X (θ.smallWrites τ)
            + (Fintype.card d ^ 2 + ∑ ℓ, Fintype.card (hid ℓ))
          = Module.finrank ℝ (Params (Arch.mlp relu id hid) dIn dOut)
```

The paper's sentence reads: for generic `θ`, for all small `τ ≠ 0`, there is a batch (it may depend
on `τ`). Lean: for almost every `θ` there is one batch that serves all small `τ ≠ 0`, and it also
lies in `noKinkAll θ` (no limit pre-activation `x E W_read^ℓ` vanishes). **Lean is stronger than
the sentence, and it is what the paper's proof does** ("Fix a finite batch of such inputs … So for
`|τ|` below some `τ_0 > 0`, which depends on the parameters and on the batch").

```
theorem exists_isOpen_funDim_smallWrites_relu (hd …) (hdIn …) (hdOut …) :
    ∃ U : Set (Params (Arch.mlp relu id hid) dIn dOut), IsOpen U ∧
      (∀ θ ∈ U, funDim (Arch.mlp relu id hid) 1 θ + (Fintype.card d ^ 2 + ∑ ℓ, Fintype.card (hid ℓ))
        = Module.finrank ℝ (Params …)) ∧
      (∀ (μ …) [μ.IsAddHaarMeasure], ∀ᵐ θ ∂μ, ∀ᶠ τ in 𝓝[≠] (0 : ℝ), θ.smallWrites τ ∈ U) ∧
      (∀ (μ …) [μ.IsAddHaarMeasure], (∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) →
        ∀ᵐ θ ∂μ, θ ∈ U → funDim (Arch.mlp relu id hid) 0 θ + L * Fintype.card d ^ 2
          ≤ funDim (Arch.mlp relu id hid) 1 θ)
```

The open set `U` is chosen before the measure. This is the paper's order: "an open set of weights
that contains these" names a set of weights and no measure, and any two additive Haar measures on
the parameters have the same sets of measure zero (sixth audit, by compiling). The third clause is
"contains these" (`θ_τ` for generic `θ` and all small `τ ≠ 0`), and it makes `U` nonempty, so the
statement is not satisfied by the empty set. The fourth clause is "at almost every point of this
set". **Same order as the paper.** What the second clause says is the subject of Check 2.

### Check 2. `funDim` and the paper's functional dimension for ReLU-type blocks

**Verdict: both statements of the pair are made for Theorem B.1 (ii) (ReLU, ReLU², ReGLU) and for
Lemma A.30 at `θ_τ`. For Lemma A.30 on the open set `U` only the value of `funDim` is stated.**

The library's `funDim` is the largest rank over the batches at which the network is differentiable
in `θ` (sixth audit, Check 2); the paper's functional dimension for these blocks is the largest rank
over the batches at which no hidden unit sits at its kink, and those batches are among Lean's. So
`funDim ≥` the paper's value always, and the paper's value is reached when a batch off the kinks
has the rank `funDim`.

| Value | The value of `funDim` | A batch off the kinks with that rank |
|---|---|---|
| B.1 (ii), ReLU | `ae_funDim_relu_oneBlock_residual_rmsNorm` | `ae_exists_jacobianRank_relu_oneBlock_residual_rmsNorm` (`∀ i, X i ∈ noKinkRMS θ`) |
| B.1 (ii), ReLU² | `ae_funDim_reluSq_…` | `ae_exists_jacobianRank_reluSq_…` (`noKinkRMS`) |
| B.1 (ii), ReGLU | `ae_funDim_reglu_oneBlock_residual_rmsNorm` | `ae_exists_jacobianRank_reglu_…` (`noKinkGateRMS`) |
| B.1 (ii), the gain | `ae_funDim_skipless_add_le_{relu,reluSq,reglu}_oneBlock_residual_rmsNorm`: `funDim` only | none needed: the skipless `funDim` is at least the paper's value, and the residual `funDim` is the paper's value by the two rows above, so the Lean inequality gives the paper's |
| A.30 at `θ_τ` | `eventually_funDim_smallWrites_mlp_rescale` under `SmallWritesGeneric`; for almost every `θ` through `exists_isOpen_…` (clauses 2 and 3). ReGLU: `eventually_funDim_smallWrites_reglu` | `ae_exists_eventually_jacobianRank_smallWrites_{relu,reluSq,reglu}`: the batch, with the clause on the pre-activations at `θ_τ` |
| A.30 on `U` | `exists_isOpen_funDim_smallWrites_{relu,reluSq,reglu}`, clause 2; near `θ_τ`: `eventually_eventually_funDim_smallWrites_…` | **not stated** |
| A.30, the gain on `U` | clause 4, `funDim` only | **not stated**; with a batch on `U` the argument of the fourth row would give the paper's gain |

*The clause of Lemma A.30 on the pre-activations at `θ_τ`* (by reading `Network/Defs.lean` and
`Residual/SmallWrites.lean`): `θ.smallWrites τ` has the reads of `θ` (`read := θ.read`), block `ℓ`
reads `A.χ (hidden … ℓ.castSucc) * read ℓ`, and `χ = id`. So
`hidden (Arch.mlp σ id hid) 1 (θ.smallWrites τ) (X i) ℓ.castSucc * θ.read ℓ` is the matrix of the
pre-activations of block `ℓ` at `θ_τ` on the input `X i`, and the clause says that none of its
entries is `0`: "no pre-activation on the batch vanishes at `θ_τ`". Yes. For ReGLU the clause is on
the gate columns (`Sum.inl j`), which is where the kink is.

*Under pre-RMSNorm* (by reading `Basic/RMSNorm.lean`): the block reads `N_ε(xE) W_read`, and row
`t` of `N_ε(xE)` is `(√(‖x_t E‖²/d + ε))⁻¹ • (x_t E)`. For `ε > 0` the factor is a positive number.
So entry `(t, i)` of `N_ε(xE) W_read` is a positive multiple of entry `(t, i)` of `x E W_read`, and
"every entry of `x E W_read` is nonzero" (`noKinkRMS`) is the same set of inputs as "no
pre-activation vanishes". Yes, for `ε > 0`. (`noKinkRMS` is defined for every real `ε`; it is used
with `0 < ε` only.)

### Check 3. No extra hypotheses in the main-text statements, and the values

**Verdict: the constants and the directions of the inequalities are the paper's. No extra
hypothesis.**

Main text, Theorem 4.6 (ii): "Under RMSNorm, the residual network satisfies the equality
condition, and the skip raises the functional dimension by at least `d_model (d_model − 1)/2`",
with the Scope of Section 2 (`d_in, d_out ≥ d_model ≥ 2`, `d_hidden ≥ d_model`, no biases, `ε > 0`).

| Paper | Lean (by reading; elaborated form by compiling) | Same? |
|---|---|---|
| `fd = P − d(d−1)/2 − s`, `s = d_hidden` (ReLU, ReLU²) | `funDim … 1 θ + (card d * (card d - 1) / 2 + card (hid 0)) = finrank ℝ (Params …)` | yes |
| the same with `s = 2 d_hidden` (ReGLU) | `funDim … 1 θ + (card d * (card d - 1) / 2 + 2 * card (hid 0)) = finrank …` | yes |
| gain `≥ d(d−1)/2` for width `≥ d` | `funDim … 0 θ + card d * (card d - 1) / 2 ≤ funDim … 1 θ` (`0`: no skip, `1`: identity skip) | yes |
| Lemma A.30: rank `P − d² − s` | `jacobianRank … 1 X (θ.smallWrites τ) + (card d ^ 2 + ∑ ℓ, card (hid ℓ)) = finrank …`; ReGLU: `2 * ∑ ℓ, card (hid ℓ)` | yes |
| Lemma A.30: gain `≥ L d²` | `funDim … 0 θ + L * card d ^ 2 ≤ funDim … 1 θ` | yes |

The sum forms: `a + b = P` in `ℕ` says `a = P − b` and `b ≤ P`; `a + c ≤ b` says `b − a ≥ c`.
`card d * (card d - 1)` is even, so the division by 2 is exact; for an empty `d` it is `0`. The
stream matrices `0` and `1` are the skipless and the residual network of (2)
(`h_ℓ = h_{ℓ−1} M_ℓ + f_ℓ(χ(h_{ℓ−1}) W_read^ℓ) W_write^ℓ`, `y = χ(h_L) D`).

The gains follow from the values and from the upper bounds of Theorem 4.2 without skips
(`ae_funDim_add_le_skipless_{relu,reluSq,reglu}_rmsNorm` and, on `U`,
`ae_funDim_add_le_skipless_{relu,reluSq,reglu}`), which need `card d ≤ card dIn` and the width
hypothesis: `fd_1 + N + s = P` and `fd_0 + 2N + s ≤ P` give `fd_0 + N ≤ fd_1` (by hand).

Not stated as such: "which is the equality condition" (Definition 4.3). Lean states the value.

By a computation (`py/a30_check.py`, `float64`, singular values, batches of 400 inputs off the
kinks): the value of Theorem B.1 (ii) for `ε = 0.01` and `(d, d_hidden) = (2, 3), (3, 2), (3, 5)`,
and the value of Lemma A.30 at `τ = 0.05` for `d = 2` and `(L, d_hidden) = (1, 3), (2, 3), (3, 2)`,
for ReLU, ReLU² and ReGLU: 18 cases, the numerical rank is the stated value in all; the last
singular value that counts is at least `5 × 10^{11}` times the next one. This is a check of the
constants, not a proof.

---------------------------------------------------------------------------------------------------

## Part 2: the statements, file by file

### Verdict table

"Proved": no `sorry` at `92a4512`, and by compiling the three standard axioms only. "Proved at
`41ce476`": `sorry` at `92a4512`; the same statement is proved in `lp` at `41ce476` (by compiling).

| Paper piece | Lean | Verdict | Status |
|---|---|---|---|
| Lemma A.3, "the output becomes `Λy` with a scalar `Λ > 0`" | `exists_pos_smul_eval_cobAt_of_rowHomogeneous`, `exists_pos_smul_eval_scale_last` | LEAN STRONGER: no hypothesis on the hidden states; one `Λ` per token. The hypothesis is on the fixed maps `f_ℓ`, not on the blocks (note 1) | proved |
| Lemma A.3 (i), `ε = 0` | `eval_cobAt_rmsNorm_zero_of_rowHomogeneous`, `eval_scale_last_rmsNorm_zero` | LEAN STRONGER: also at inputs with a zero row, for Lean's total `N_0` | proved |
| Lemma A.3 (i), `G` orthogonal | `eval_cobAt_rmsNorm` (`Symmetry/AtOneState.lean`, an earlier file, any blocks) | SAME | no `sorry` in its file; I did not print its axioms |
| Lemma A.3 (ii) | `hasDerivAt_eval_cobAt_exp_of_rowHomogeneous`, `hasDerivAt_eval_scale_last_exp` | SAME, as the derivative of the output; LEAN STRONGER in that `S` is any matrix | proved |
| Theorem B.1 (ii), proof, Steps 1 to 3, ReLU-type blocks | `exists_antisymm_of_flatOn_residual_rmsNorm` | SAME, for an abstract open cone `V` of pre-activations | proved |
| Steps 4 and 5, ReLU and ReLU² | `flatOn_noKinkRMS_le_mlp_rescale_residual_rmsNorm` | SAME | proved |
| Theorem B.1 (ii) = 4.6 (ii), the value, ReLU and ReLU² | `funDim_mlp_oneBlock_rescale_residual_rmsNorm`, `exists_jacobianRank_mlp_oneBlock_rescale_residual_rmsNorm`, the four `ae_…` | SAME (the pair) | proved |
| the gain, ReLU and ReLU² | `ae_funDim_skipless_add_le_{relu,reluSq}_oneBlock_residual_rmsNorm` | SAME | proved |
| the same for ReGLU | the nine names of `OneBlock/ResidualRMSReGLU.lean` | SAME | proved |
| "which is the equality condition" | none | PART: the value is stated, the words are not | |
| Lemma A.30, proof, "tends to `J_0`, and by lower semicontinuity" | `eventually_finrank_le_of_small_parameter_of_contDiffOn`; `eventually_jacobianRank_smallWrites_ge_of_contDiffOn` | SAME, for abstract open sets `V ℓ` | proved; proved at `41ce476` |
| Lemma A.30, proof, "Near such parameters the signs on the batch do not change" | `eventually_jacobianRank_ge_of_contDiffOn` | SAME | proved at `41ce476` |
| Lemma A.30, proof, the kernel of `J_0` | `smallWritesLimit_eq_zero_mlp_rescale`; `smallWritesLimit_eq_zero_reglu` | SAME for all inputs: the kernel lies in a space of dimension `d² + s`. The step "flat on a neighborhood of `0` is flat at every input at which no pre-activation vanishes" is not stated | proved at `41ce476`; `sorry` |
| Lemma A.30, first sentence | `exists_eventually_jacobianRank_smallWrites_mlp_rescale`, `ae_exists_eventually_jacobianRank_smallWrites_{relu,reluSq}`; `…_reglu` | LEAN STRONGER: one batch for all small `τ`; Lean writes `d ≥ 2`, which the paper's lemma needs | proved at `41ce476`; `sorry` |
| Lemma A.30, second sentence, the functional dimension on an open set | `eventually_funDim_smallWrites_…`, `eventually_eventually_funDim_smallWrites_…`, `exists_isOpen_funDim_smallWrites_…`, clauses 1 to 3 | PART: the value of `funDim`; no batch off the kinks at the points of `U` | proved at `41ce476`; `sorry` (ReGLU) |
| Lemma A.30, the gain | `exists_isOpen_funDim_smallWrites_…`, clause 4 | PART, for the same reason: the gain of `funDim` | proved at `41ce476`; `sorry` (ReGLU) |
| Lemma A.30, "or over an open set that contains `0`" | none | not stated; the index says so | |

### Notes

**1. `Symmetry/HomogeneousRMSNorm.lean` (by reading; (ii) by hand and by a computation).**

- `RowHomogeneous A k`:
  `∀ ℓ (c : T → ℝ), (∀ t, 0 < c t) → ∀ M, A.f ℓ (of fun t i => c t * M t i) = of fun t i => c t ^ k * A.f ℓ M t i`.
  The paper says that the blocks are "positively homogeneous of degree `k`" and writes `h_ℓ S h_ℓ^⊤`,
  a number, so `h_ℓ` is one row: the lemma is a statement about one token. An MLP block acts on each
  token separately, and RMSNorm rescales each token by its own factor, so for `T` tokens the row by
  row notion is the right one, and `Λ` is one number per token (`Λ : T → ℝ`). Two differences, both
  harmless: the hypothesis is on `f_ℓ` at all matrices, the paper's on the block
  `n ↦ f(n W_read) W_write`; and the degree is a natural number. `rowHomogeneous_mlp` (degree `k`
  for an activation of degree `k`) and `rowHomogeneous_gated` (degree `k + 1` for a gate of degree
  `k`) are right: a ReGLU unit is `max(g, 0) · v`, of degree 2, as the paper says in part (iii)
  ("`B(λn) = λ^k B(n)` for `λ > 0`, with `k = 1` or `2`").
- `meanSq v = (v ⬝ᵥ v) / card d` is `r² = ‖v‖²/d_model`.
- `θ.cobAt ℓ.castSucc G` with `ℓ : Fin L`: `Params.cobAt` multiplies the writes into the hidden
  state by `G` on the right and its reads by `G⁻¹` on the left (Definition 3.1), and `ℓ.castSucc`
  runs over `h_0, …, h_{L−1}`: "at `h_ℓ` with `ℓ < L`". `{ θ.cobAt (Fin.last L) G with D := θ.D }`
  with `↑G = c • 1`, `0 < c`: the write into `h_L` times `c`, and `D` unchanged: "the scaling
  `G = cI` at `h_L` with its read `D` unchanged". Lean says `c > 0`; the paper does not, and needs
  it (note for the authors below).
- (i) for `ε = 0`. `rmsRow 0 0 = (√0)⁻¹ • 0 = 0`: Lean's `N_0` sends a zero row to the zero row. At
  a token whose hidden states are nonzero the Lean statement is the paper's. At a token with a zero
  hidden state it is a true statement about the total function: a zero row stays zero under `G`,
  and a nonzero row is multiplied by positive numbers, which `N_0` forgets (I followed the cases
  by hand). So the two statements hold at every input, and on the paper's inputs they are the
  paper's.
- (ii). By hand for `L = 1`: the block reads `N_ε(h_0 G) G⁻¹ W = γ N_ε(h_0) W` with
  `γ = √(r_0² + ε)/√(‖h_0 G‖²/d + ε)`, writes `γ^k h_1`, and the readout gives `Λ y` with
  `Λ = μ √(r_1² + ε)/√(μ² r_1² + ε)`, `μ = γ^k`. With `G = e^{tS}`:
  `d/dt ‖h_0 e^{tS}‖² = h_0 (S + S^⊤) h_0^⊤ = 2 h_0 S h_0^⊤` for every `S`, so
  `d log γ/dt = −h_0 S h_0^⊤/(d (r_0² + ε))`, and `d log Λ/d log μ = ε/(r_1² + ε)` at `μ = 1`. So
  `d log Λ/dt = −k (h_0 S h_0^⊤)/(d (r_0² + ε)) · ε/(r_1² + ε)`, the paper's formula and Lean's
  (`k^{L−ℓ}` with `L − ℓ = 1`, the product over `i > ℓ.castSucc`). As `Λ = 1` at `t = 0`, the
  derivative of `Λ y` is `(d log Λ/dt) y`, which is what Lean states. For an antisymmetric `S`,
  `h S h^⊤ = 0`, so Lean's derivative is `0`, as it must be (`e^{tS}` is orthogonal). Lean's
  formula is right for every `S`.
- By a computation: `py/a3_mp.py` (60 digits, `d = 3`, a general `S`, `k = 1, 2`, `L = 1, 3`,
  `ε = 0.01`): the largest relative difference between a central difference and Lean's formula is
  `2.6 × 10^{−33}`. `py/a3_check.py` (`float64`; ReLU, ReLU², ReGLU; `L = 1, 2, 3`; two tokens;
  `S` symmetric, antisymmetric and general; the scaling at `h_L`): agreement to `10^{−7}` or better
  for `ε ≥ 0.5`; for `ε = 0.01` and `L = 3` the derivative is so small that rounding dominates, and
  a fourth-order difference brings the difference from `10^{−1}` to `10^{−4}` (`a3_check2.py`),
  which the 60-digit run settles.
- Degenerate cases (by hand): no tokens, an empty `d`, `k = 0`, `L = 0` (the statements with
  `ℓ : Fin L` are then empty; the scaling at `h_0` has the derivative `ε/(r_0² + ε)`): all true.

**2. `OneBlock/ResidualRMSStepsOn.lean` (by reading).**

- The hypotheses on `V`. "Open" and "invariant under positive scalings of the rows" give: at an
  input `x` with `x E W_read ∈ V` the block is evaluated at `N_ε(xE) W_read ∈ V`, where `f` is
  differentiable, so `flatOn` at these inputs is the paper's flatness (Mathlib's `fderiv` is not
  `0` by convention there); and the rays `x = s w` stay in the set. "One input with equal rows in
  it" gives a nonempty open set of rows `w` with `wE ≠ 0`. That is what the three steps use:
  Step 1 needs the rows `N_ε(h_1)` to span `ℝ^d` (on the rays `h_1(sw)/s → wE`, and `wE` over an
  open set of `w` spans, as `E` has rank `d`), Steps 2 and 3 need "for all `w` in an open set".
  The hypothesis `hw` cannot be dropped: for `V = ∅` every `η` is flat on the empty set and the
  conclusion is false. With several tokens it asks for an input with equal rows; for the paper's
  blocks (`V` = the matrices with no zero entry, or with no zero gate entry) such an input exists
  as soon as no read column vanishes.
- The last clause, with the signs. `cobDir θ X` has `E := θ.E * X 0`,
  `read ℓ := -(X ℓ.castSucc * θ.read ℓ)`, `write ℓ := θ.write ℓ * X ℓ.succ`,
  `D := -(X (Fin.last L) * θ.D)`: with `X = fun _ => Y` it is the paper's `η^Y` ("the entries `EY`,
  `−Y W_read`, `W_write Y` and `−YD`"). So `η' = η − η^Y` has the entries `η_read + Y W_read` and
  `η_write − W_write Y` at the block, and `0` at `E` and `D` by `η.E = θ.E * Y`,
  `η.D = -(Y * θ.D)`. Lean's clause,
  `fderiv ℝ (A.f 0) (N_ε(xE) W_read) (N_ε(xE) (η.read 0 + Y * θ.read 0)) * θ.write 0 + A.f 0 (N_ε(xE) W_read) * (η.write 0 - θ.write 0 * Y) = 0`,
  is the derivative of `n ↦ f(n W_read) W_write` along these entries at `n = N_ε(xE)`: Step 4's
  condition, with the right signs.
- The header quotes the paper's "Notation and flat directions" as "For these activations, every
  input means every input at which no hidden unit sits at its kink". The paper's sentence is: "For
  the ReLU-type activations, `F(θ, x)` is differentiable in `θ` at the inputs `x` at which no hidden
  unit sits at its kink, which form an open set of full measure, and “every input” means every such
  input." The meaning is the same; the words in quotation marks are not the paper's.

**3. `OneBlock/ResidualRMSRescale.lean`, `OneBlock/ResidualRMSReGLU.lean` (by reading).**

- `OneBlockGenericRMS`: `E` and `D` of rank `d`; every row of `W_write` nonzero; the columns of
  `W_read` nonzero and pairwise non-collinear. This is Lemma B.3's "every `a_i ≠ 0` and … the `c_i`
  … nonzero and pairwise non-collinear" with `a_i` the rows of `W_write` and `c_i` the columns of
  `W_read`, that is, "with `E` and `D` replaced by the identity"; `M = 0` is the absence of a
  linear term in `UnitsRescale … d d (hid 0)`. `OneBlockGenericReGLURMS` adds every value column
  nonzero and `(θ.read 0)ᵀ (Sum.inr i) ≠ r • (θ.read 0)ᵀ (Sum.inl i)` for every `r`: "`(e_i, β_i')`
  not proportional to `(c_i, β_i)`" without biases. Both hold at almost every parameter for
  `d ≥ 2` and any width (`ae_oneBlockGenericRMS`, `ae_oneBlockGenericReGLURMS`, proved), so no
  statement is vacuous.
- The directions. `rescaleDirMlp k θ α`: read column `i` times `α_i`, write row `i` times
  `−k α_i`: Lemma B.3 for ReLU (`ψ_c = λ c`, `ψ_a = −λ a`) and ReLU² (`−2λ`).
  `rescaleDir θ α + rescaleDirGate 1 θ β`: gate column times `β_i`, value column times `−α_i`,
  write row times `α_i − β_i`: Lemma B.3 for ReGLU (`ψ_c = λ c`, `ψ_e = −α e`, `ψ_a = (α − λ) a`)
  with `λ = β`. With `cobDir θ (fun _ => Y)`, `Y` antisymmetric, this is Step 5: "those of the
  orthogonal change of basis and of the symmetries inside the block".
- Degenerate cases of the statements "at one parameter" (by hand; they are proved): no hidden
  unit (`funDim + d(d−1)/2 = P` for `x ↦ N_ε(xE) D`); `d` with one element (the conditions allow at
  most one hidden unit, and for ReGLU none); an empty `d` (no hidden unit can satisfy the
  conditions, and `P = 0`).

**4. `Residual/SmallParameterOn.lean`, `Residual/SmallWritesOn.lean`,
`Residual/DepthRescale.lean`, `Residual/DepthReGLU.lean` (by reading; truth by hand before I saw
that six of them were proved).**

- `smallWritesLimit A θ η x = x (η_E D + E η_D) + ∑_ℓ (Df_ℓ(x E W_read^ℓ)(x E η_read^ℓ) W_write^ℓ + f_ℓ(x E W_read^ℓ) η_write^ℓ) D`
  is the paper's `(J_0 η)(x) = x ψ_M + ∑_i [σ(z_i) ψ_{a_i} + σ'(z_i)(x ψ_{c_i}) a_i]` with
  `ψ_M = η_E D + E η_D`, `ψ_C = E η_read`, `ψ_A = η_write D`, `a_i` the rows of `W_write D`. On a
  batch it is used only at inputs with `x E W_read^ℓ ∈ V ℓ`, where `f_ℓ` is differentiable, so the
  `fderiv` in it is the true derivative.
- Why the kernel is not `cobDir`. `J_0` is the limit of `J_τ S_τ`, and `S_τ` divides the read
  columns by `τ`. The direction of the change of basis at `θ_τ` is `(EX, −X W_read, τ W_write X,
  −XD)`; `S_τ⁻¹` of it is `(EX, −τ X W_read, τ W_write X, −XD)`, which tends to `(EX, 0, 0, −XD)`.
  So in the kernel of `J_0` the change of basis shows at `E` and `D` only, and the reads and the
  writes carry the rescalings alone. This is the paper's proof of Lemma A.27 ("`ψ_M = 0` gives
  `η_E = EX` and `η_D = −XD` … The rescalings determine `η_read` and `η_write` through `ψ_C` and
  `ψ_A`") and the form of `smallWritesLimit_eq_zero_mlp` in `Residual/DepthMlp.lean`
  (`η.read ℓ = 0`, `η.write ℓ = 0` for tanh and GELU, where there is no rescaling). For ReLU:
  `E η_read = λ ⊙ (E W_read)` gives `η_read = λ ⊙ W_read` by cancelling `E`, and
  `η_write D = −kλ ⊙ (W_write D)` gives `η_write = −kλ ⊙ W_write` by cancelling `D`: the reads and
  writes of `rescaleDirMlp k θ α`. Lean's conclusion is right (by hand).
- `SmallWritesGeneric` (`Residual/DepthMlp.lean`): `E`, `D` of rank `d`; every row of
  `W_write^ℓ D` nonzero; the columns of `E W_read^ℓ`, over all blocks together (`Σ ℓ, hid ℓ`),
  nonzero and pairwise non-collinear. This is "the hypotheses of Lemma B.3 … for the units of all
  blocks together". `SmallWritesGenericReGLU` adds the conditions of the gated blocks and "no value
  column of `E W_read^ℓ` proportional to the gate column of the same unit".
- The statements one by one, against the proof of Lemma A.30:
  - first paragraph ("the flat directions form a space of dimension `d² + s`"):
    `smallWritesLimit_eq_zero_mlp_rescale`. It states the inclusion (a direction in the kernel has
    the form), which is the half that the lemma uses; the index and the header say "the kernel …
    is", which is more than the statement.
  - second paragraph: `eventually_jacobianRank_smallWrites_ge_of_contDiffOn` (the pre-activations
    on the batch stay in the `V ℓ` for small `τ`, and the rank at `θ_τ` is at least `P − dim W`)
    with `eventually_finrank_le_of_small_parameter_of_contDiffOn` behind it. True by hand: the
    hidden states at `θ_τ` tend to `xE`; near `(0, θ)` the outputs on the batch are `C²`; the
    limit that divides the reads and the writes by `τ` is `smallWritesLimit`.
  - third paragraph: `eventually_jacobianRank_ge_of_contDiffOn` (near `θ` the pre-activations stay
    in the `V ℓ` and the rank on the batch does not drop), and the upper bound by the symmetries,
    which is inside `eventually_funDim_…` and `eventually_eventually_funDim_…`.
  - the lemma itself: see Part 1.
- Degenerate cases (by hand): an empty batch in the two statements of `SmallWritesOn.lean` (then
  `W = ⊤` and the inequality is `P ≤ 0 + P`; the second is `0 ≤ 0`); no tokens there (the same);
  `L = 0` (the network is `x ↦ xED`, rank `P − d²`); `d` with one element (the conditions allow
  one hidden unit in all, and for ReGLU none, so the statements "at one parameter" stay true; the
  `ae_` statements ask for `d ≥ 2`); an empty `d`; a degree `k = 0` (then `UnitsRescale` cannot
  hold with a hidden unit). No counterexample.
- Not stated of Lemma A.30: inputs in an open set that contains `0` (and with it the step "the
  regions are cones with apex `0`"); a batch off the kinks at the points of `U`.

---------------------------------------------------------------------------------------------------

## What the authors should know

Drifted or misdescribed, first.

1. **Lemma A.30, second sentence: on the open set `U`, Lean states the library's `funDim` only.**
   `exists_isOpen_funDim_smallWrites_{relu,reluSq,reglu}` and
   `eventually_eventually_funDim_smallWrites_{mlp_rescale,reglu}` give `funDim = P − d² − s` on `U`
   and near `θ_τ`. The paper's functional dimension for ReLU-type blocks is at most `funDim`, and
   equals it when a batch on which no pre-activation vanishes has that rank; this batch is stated at
   `θ_τ` and not at the other points of `U`. So Lean does not yet say that the paper's functional
   dimension is `P − d² − s` on `U`, nor the gain there in the paper's sense. The docstrings call
   these statements "Lemma A.30, second sentence" without this limit, and so does the index. A
   clause would close it, for example in clause 2 of `exists_isOpen_…`:
   `∀ θ ∈ U, ∃ n X, (∀ i ℓ t j, (hidden … 1 θ (X i) ℓ.castSucc * θ.read ℓ) t j ≠ 0) ∧ jacobianRank … 1 X θ + (card d ^ 2 + ∑ ℓ, card (hid ℓ)) = finrank …`.
   It is what `eventually_jacobianRank_ge_of_contDiffOn` gives near `θ_τ` (the pre-activations on
   the batch stay nonzero and the rank does not drop), with the upper bound by the symmetries.
2. **`STATEMENTS.md`, note "ReLU blocks and the functional dimension"**, is out of date: it says
   that at depth no Lean statement defines the inputs with no hidden unit at its kink.
   `noKinkAll`, `noKinkGateAll` and the clause on the pre-activations at `θ_τ` now do.
3. `OneBlock/ResidualRMSStepsOn.lean`, header: a sentence of the paper in quotation marks that is a
   paraphrase (note 2 above).
4. `Residual/DepthRescale.lean` and `Residual/DepthReGLU.lean`, headers, and the index: "the kernel
   of `J_0` … is" where the statement is "lies in".

For the paper.

5. **Lemma A.30 needs `d_model ≥ 2` and does not say it.** For `d_model = 1` and two hidden units
   the rank is `d_in + d_out`, one less than `P − d² − s` (Check 1). Lean has the hypothesis.
6. Lemma A.3: "the scaling `G = cI` at `h_L`" needs `c > 0`. For `c = −1` the matrix `G` is
   orthogonal and the output becomes `−y`, against "`Λ > 0`" and "(i) `Λ = 1` if … `G` is
   orthogonal". The proof takes `μ_i > 0`. Lean has `0 < c`.
7. Lemma A.3 is written for one token (`h_ℓ S h_ℓ^⊤` is a number). For `T` tokens `Λ` is one number
   per token, as in Lean.
8. Proof of Lemma A.30: "With the writes `τ V_ℓ`": `V_ℓ` is not introduced in this lemma (elsewhere
   `V` is the write of the identity units of a mixed block); the lemma writes `τ W_write^ℓ`.

True and in order.

9. Theorem B.1 (ii) for ReLU, ReLU² and ReGLU: the pair of statements, the gain, the conditions
   and the directions are the paper's, with no extra hypothesis. Proved at `92a4512`.
10. Lemma A.3: proved; the formula of (ii) is right for every `S`.
11. Lemma A.30, first sentence: Lean is the statement of the paper's proof, one batch for all small
    `τ`. `SmallWritesOn.lean` and `DepthRescale.lean` are `sorry` at `92a4512` and proved at
    `41ce476` with the same statements. `DepthReGLU.lean` is `sorry`; its seven statements are
    true by hand, by the argument of `DepthRescale.lean` with `relu_gated_units_flat` and the two
    rescalings.

## Corrections for `STATEMENTS.md` (lines at `92a4512`; the same lines at `d4c1e26`)

- Lines 83 to 91 ("Not yet compared by such a reader …"): take out
  `Symmetry/HomogeneousRMSNorm.lean`, `OneBlock/ResidualRMSStepsOn.lean`,
  `OneBlock/ResidualRMSRescale.lean`, `OneBlock/ResidualRMSReGLU.lean`,
  `Residual/SmallParameterOn.lean`, `Residual/SmallWritesOn.lean`, `Residual/DepthRescale.lean`,
  `Residual/DepthReGLU.lean`, and say that a tenth reader (part B, 24 November) compared them at
  `92a4512`: nothing false or vacuous; on the open set of Lemma A.30 only `funDim` is stated.
- Line 283 (Lemma A.30, ReLU and ReLU²) and line 284 (ReGLU):
  - "an open set `U` with `funDim = P − d² − s` on it": add "(the library's `funDim`; a batch off
    the kinks with this rank is stated at `θ_τ` only, so on `U` this is the paper's value as an
    upper bound, and the gain is that of `funDim`)", until the clause of item 1 is added.
  - "the kernel of `J_0` … is `η_E = E X`, `η_D = −X D` plus a rescaling": write "a direction in
    the kernel of `J_0` … has `η_E = E X`, `η_D = −X D` and the reads and writes of a rescaling".
  - "`d_in, d_out ≥ d ≥ 2`": add "(`d ≥ 2` is in Lemma A.27 and in the Scope, not in the text of
    Lemma A.30, which needs it)".
  - "Not stated: inputs in an open set that contains `0`": add "and the step that a direction flat
    near `0` is flat at every input off the kinks".
- Lines 455 to 457 ("At depth, no Lean statement defines the inputs with no hidden unit at its
  kink; an equality for ReLU-type blocks at depth would need the second statement of the pair
  again."): replace by "At depth the pair is stated at the parameters `θ_τ` of Lemma A.30
  (`noKinkAll`, `noKinkGateAll`, and the clause on the pre-activations at `θ_τ`;
  `Residual/DepthRescale.lean`, `Residual/DepthReGLU.lean`); on the open set of that lemma only
  the value of `funDim`."
- Line 277 (Lemma A.3): correct as it is. It could add "the hypothesis is on the fixed maps `f_ℓ`;
  one `Λ` per token; `c > 0`, which the paper leaves unsaid".
- Lines 279 and 280 (Theorem B.1 (ii)): correct as they are. They could add "not stated: 'which is
  the equality condition'".
- Lines 278, 281, 282: correct as they are. Status of 282 and 283 at `92a4512`: "in work", right
  for that commit; at `d4c1e26` the index says "proved" for both, which agrees with what I compiled.

## What I could not check

- I did not build the library. The compiled library of `lw` lacks the eight files. The one scratch
  file was compiled against a copy of the library that the owners of `lp` built; I compared the
  sources of `lp` with `92a4512` by a script on the text of the statements, and read the elaborated
  statements of 22 names in `Chk.out`, which agree with the sources that I quote.
- `Residual/DepthReGLU.lean` has no compiled form that I found. Read only; its statements are
  judged true by hand, not by a proof.
- I compared statements and definitions, not proofs. Where I say "true by hand" I followed the
  paper's argument for the statement, not the Lean proof.
- The numerical checks (`py/a30_check.py`) are for small sizes, one seed each, in `float64`; they
  test constants and the case `d = 1`, and prove nothing. The case `d = 1` is also settled by hand.
- `Residual/SmallParameter.lean`, `Residual/SmallWrites.lean`, `Residual/DepthMlp.lean`,
  `Residual/DepthGated.lean` and `OneBlock/ResidualRMSSteps.lean`, `…Mlp`, `…Gated`, `…Gain` were
  compared in earlier audits; I read their definitions and the statements that my files use, and
  did not compare them with the paper again.
- I did not read the script `claude/homogeneous_rmsnorm_check_2026-11-24.py` that the header of
  `HomogeneousRMSNorm.lean` cites (a file of that name is in `/home/claude/proj_up/`); I wrote my
  own check. I cannot read the documents of the project from here, only the local copies.
- `STATEMENTS.md`: I checked the eight rows of my files, lines 83 to 91 and the note on ReLU
  blocks, not the rest.
