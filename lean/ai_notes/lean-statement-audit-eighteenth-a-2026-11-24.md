STATUS: complete

# Eighteenth audit of Lean statements against the papers, part A: the triangular skip for four kinds of block; ridge functions; attention heads on three tokens (24 November 2026)

Reader: an independent reader who did not write the statements. Brief:
`/home/claude/proj_up/audit18a_brief_2026-11-24.md`. I audited statements and definitions, not
proofs. I changed no repository file, ran no `lake build`, made no commit and no push. My files are
in `/home/claude/audit18a/`.

Library: `/home/claude/lw/lean` (branch `lean-wip`). The branch moved nine times while I read.

- **Commit at the start: `f0edc930586d188d20f9a08fda91bd13d60b7cef` (18:54:48 UTC).**
- Then `2827fc3` (18:56:49), `b09fbc3` (18:59:33), `561a967` (19:04:49), `e22b23c` (19:05:00),
  `883be8e`, `4277481`, `32c4dc4` (19:05:09) and **`20eacc66a0c537615fde8151e877bd5b3a33ff68`
  (19:09:07), the head when I made the last checks and took the line numbers of the index.** One
  more commit came while I wrote, `5951ed9` (19:11:49): the nine files are unchanged there too,
  and the four rows of the index are at lines 828, 829, 832 and 833.
- **The four files of the brief and the five files of definitions did not change at all** between
  `f0edc93` and `20eacc6`, nor at `5951ed9` (`git diff` of the nine files is empty). Of what I
  read, only `STATEMENTS.md` and `checks/Axioms.lean` changed, in rows and lines of other files.
- **Files with `sorry`.** At `f0edc93`: `Absorb/RotaryBiases.lean`, `Absorb/ReluSqBiasesCount.lean`,
  `Absorb/ReluSqBiasesLower.lean`. At `20eacc6`: `Absorb/ReluSqBiasesCount.lean`,
  `OneBlock/ResidualRMSZeroSteps.lean` (at `5951ed9` also `OneBlock/ResidualRMSZeroGain.lean`).
  None of the four files of the brief, and none of the files they use, at any of these commits.
- The four files have 25 public names: 1 definition and 24 theorems (4; 1 + 12; 3; 5, as the brief
  says).
- All 24 theorems depend on `propext`, `Classical.choice`, `Quot.sound` only (by compiling,
  `Ax.lean`, `Ax.out`, against the build of `/home/claude/lp/lean`; its nine sources are the same
  as those of `/home/claude/lw`, by `cmp`; its compiled files of the four are from 19:00 to
  19:04 UTC, after a rebuild by its owner, and newer than the sources).

Papers, as text: the skips paper ("S", `skips.txt`) and the absorb paper ("A", `absorb.txt`). Line
numbers of `STATEMENTS.md` are those of `20eacc6`; the rows of the four files are lines 827, 828,
830 and 831 there (825 to 828 at `f0edc93`). I quote the text of every place that I name.

How I checked.

- "By reading": every public statement and docstring of the four files, the definitions they use
  (`evalSkips`, `jacobianRankSkips`, `funDimSkips`, `flatSkips`, `funDimLearned`,
  `upperTriangular`, `triSkips`, `funDimLearnedTri`, `noKinkRMS`, `noKinkGateRMS`,
  `OneBlockGenericRMS`, `funDim`, `jacobianRank`, `Arch.mlp`, `Arch.gated`, `Arch.attention`,
  `attnWeights`, `attnHeads`, `attentionBlock`, `headValueModel`, `rmsRow`, `rmsNorm`), and the
  paper passages that the brief names.
- "By hand": a short argument of my own, written where it is used.
- "By compiling": scratch files in `/home/claude/audit18a/`, compiled with `lake env lean <file>`
  from `/home/claude/lp/lean` (nothing written there): `Ax.lean` (axioms), `Sig.lean` (the full
  signatures of the 24 theorems, with every instance argument), `Chk.lean`, `Chk2.lean`,
  `Chk3.lean` (checks of Part 1). All compile without error and without `sorry` (`*.out`); the
  seven theorems of mine that I name below have the three standard axioms.
- "By a computation": my own scripts (I did not run the coordinator's; I read its output).
  `ls18core.py`, `ls18run.py`, `ls18more.py`, `ls18attn2.py`: one block under pre-RMSNorm, mpmath
  with 60 digits, exact derivatives by dual numbers for all kinds, attention included (checked
  against central differences in `ls18fd.py`: they agree to `10⁻³⁹`); the rank from the
  eigenvalues of `JᵀJ`. Over all runs the smallest singular value that is kept is `1.7·10⁻⁷` of the
  largest, and no dropped one is above `5·10⁻³¹`. `ah18.py`: Lemma A.14 as a question of rank
  (40 digits). Outputs: `ls18_*.out`, `ah18.out`.

**Short answer. Nothing false, nothing vacuous and nothing drifted was found.** The 24 statements
are the papers' or stronger. Three things the authors should know: (1) in the three statements
`ae_funDimSkipsOn_tri_{relu,reluSq,reglu}_rmsNorm_eq_residual_add` the two sides are measured in
different senses (left: on the inputs off the kinks; right: Lean's `funDim`), which neither the
docstrings nor the index say; the two senses agree for the residual network at almost every
parameter by statements that the library already has, and I compiled the equality with both sides
in the paper's sense; (2) Lemma A.14 is false on two tokens, as the paper says, and I compiled a
counterexample in Lean against every clause; the hypothesis on the mask is needed too; (3) the
coordinator's numeric script has no upper triangular case for attention; my computation has 26 (16
generic, 10 special), all with the value or the gain of the statements.

---------------------------------------------------------------------------------------------------

## Part 1: the drift checks

### Check 1. Generic means almost every parameter, for every Haar measure

**Verdict: yes, in all eight `ae_` statements, on the product of the weights and the upper
triangular skips.** (By reading; the shapes from the compiled signatures, `Sig.out`; the measure
space by compiling.)

- The eight: two in `LearnedSkipTriangularSmooth.lean` (attention), six in
  `LearnedSkipTriangularRescale.lean` (two each for ReLU, ReLU², ReGLU). The two Absorb files have
  no `ae_` statement and no measure. Each of the eight has `μ` as a variable of the statement with
  `[μ.IsAddHaarMeasure]`, and `∀ᵐ p ∂μ`. None is "there is a parameter" or "on an open set".

  ```
  theorem ae_funDimSkipsOn_tri_relu_rmsNorm (hε : 0 < ε) [Nonempty (hid 0)]
      (μ : Measure (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm ε) hid) dIn dOut
        × (Fin 1 → upperTriangular d)))
      [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
      (hdOut : Fintype.card d ≤ Fintype.card dOut) :
      ∀ᵐ p ∂μ, funDimSkipsOn (Arch.mlp relu (rmsNorm ε) hid) (triSkips d 1) p (noKinkRMS p.1)
          + (Fintype.card d * (Fintype.card d - 1) / 2 + Fintype.card (hid 0))
        = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm ε) hid) dIn dOut)
          + Fintype.card d * (Fintype.card d + 1) / 2
  ```
- The four forms `…_eq_residual_add` are "for almost every `(θ, A)` and almost every `θ'`":

  ```
  theorem ae_funDimLearnedTri_attention_rmsNorm_eq_residual_add (hε : 0 < ε) [Nonempty (H 0)]
      (μ : Measure (Params (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut
        × (Fin 1 → upperTriangular d))) [μ.IsAddHaarMeasure]
      (ν : Measure (Params (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut))
      [ν.IsAddHaarMeasure] … :
      ∀ᵐ p ∂μ, ∀ᵐ θ' ∂ν, funDimLearnedTri (Arch.attention sees (rmsNorm ε) H dh) p
        = funDim (Arch.attention sees (rmsNorm ε) H dh) 1 θ'
          + Fintype.card d * (Fintype.card d + 1) / 2
  ```
  with `ν` any Haar measure on the weights of the residual network.
- By compiling (`Chk.lean`), for a ReLU block and for an attention block with `d = 2`: the space
  `Params … × (Fin 1 → upperTriangular (Fin 2))` is finite-dimensional and carries the Borel
  σ-algebra of its topology; a Haar measure on it exists, so the statements are not empty; any two
  Haar measures on it have the same sets of measure zero. The skip runs over the subspace of the
  upper triangular matrices, so "almost every `A`" is with respect to its `d(d+1)/2` entries.

### Check 2. The functional dimension for ReLU, ReLU², ReGLU with a triangular skip

**Verdict: `U` is the paper's set; the supremum is a maximum; the three statements per kind give
the paper's functional dimension of the network with the triangular skip. In the forms
`…_eq_residual_add` the two sides are measured in different senses: the left on the inputs off the
kinks, the right is Lean's `funDim` (all batches). The two senses give the same number for the
residual network at almost every `θ'`, by statements that the library has, so the equality is
also true with both sides in the paper's sense (compiled).** (By reading; four facts by
compiling.)

- The Lean text:

  ```
  noncomputable def funDimSkipsOn {L : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
      (A : Arch T d L) (ι : V →L[ℝ] (Fin L → Matrix d d ℝ)) (p : Params A dIn dOut × V)
      (U : Set (Matrix T dIn ℝ)) : ℕ :=
    sSup {r : ℕ | ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i, X i ∈ U) ∧
      r = jacobianRankSkips A ι X p}
  ```
  By compiling (`Chk.lean`): it unfolds (by `rfl`) to the supremum, over the batches of inputs of
  `U`, of the rank of the derivative of `(θ, v) ↦ (eval A (ι v) θ (X i))_i`; with `U` everything it
  is `funDimSkips`.
- **Is `U` the paper's set? Yes.** In the statements `U` is `noKinkRMS p.1`, for ReGLU
  `noKinkGateRMS p.1`:

  ```
  def noKinkRMS (θ : …) : Set (Matrix T dIn ℝ) := {x | ∀ (t : T) (i : hid 0), (x * θ.E * θ.read 0) t i ≠ 0}
  def noKinkGateRMS (θ : …) : Set (Matrix T dIn ℝ) :=
    {x | ∀ (t : T) (i : hid 0), (x * θ.E * θ.read 0) t (Sum.inl i) ≠ 0}
  ```
  The block reads `N_ε(x E)`, with or without a learned skip, and for `ε > 0` every row of
  `N_ε(x E) W_read` is a positive multiple of the row of `x E W_read`. So this is S Appendix B, "the
  inputs `x` at which no hidden unit sits at its kink", at every token. The set depends on `θ`
  only, not on the skip, rightly. For ReGLU the unit is `relu(gate) · value` with the gate in the
  column `Sum.inl i` (by `rfl`, `Chk.lean`), so its kink is where the gate vanishes.
- **Is the supremum attained and bounded? Yes** (compiled, `Chk.lean`: `ranks_nonempty`,
  `ranks_bddAbove`, `funDimSkipsOn_mem`, `le_funDimSkipsOn`). The set of ranks contains `0` (the
  empty batch) and, when the space `V` of the skips is finite-dimensional, is bounded by the number
  of parameters; then some batch of inputs of `U` has the rank `funDimSkipsOn`, and no batch of
  `U` has more. Here `V` is `Fin 1 → upperTriangular d`, finite-dimensional. (The definition itself
  does not ask for a finite-dimensional `V`; for an infinite-dimensional one the supremum could be
  `0` by convention. No statement uses it that way.) Also compiled: `funDimSkipsOn ≤ funDimSkips`.
- **The three statements per kind** (ReLU and ReLU² through the general
  `…_tri_mlp_rescale_rmsNorm`, ReGLU by name), at one parameter, under `OneBlockGenericRMS`
  (resp. `OneBlockGenericReGLURMS`), for every invertible upper triangular `R`:

  | | Lean |
  |---|---|
  | a batch off the kinks with the rank | `exists_jacobianRankSkips_tri_mlp_rescale_rmsNorm`: `∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i, X i ∈ noKinkRMS θ) ∧ jacobianRankSkips … (triSkips d 1) X (θ, R) + (card d * (card d - 1) / 2 + card (hid 0)) = finrank ℝ (Params …) + card d * (card d + 1) / 2` |
  | no batch off the kinks has more | `jacobianRankSkips_tri_add_le_mlp_rescale_rmsNorm`: for every `X` with `∀ i, X i ∈ noKinkRMS θ`, the same with `≤` |
  | the value | `funDimSkipsOn_tri_mlp_rescale_rmsNorm`: `funDimSkipsOn … (triSkips d 1) (θ, R) (noKinkRMS θ) + (…) = finrank ℝ (Params …) + card d * (card d + 1) / 2` |

  Together: the largest rank over the batches of inputs off the kinks is
  `P + d(d+1)/2 − d(d−1)/2 − s`. This is the paper's functional dimension for these blocks (S
  Definition 4.1 with S Appendix B: "'every input' means every such input", "some finite batch has
  kernel exactly `K(θ)`"). The `ae_` forms have the value only; the two other statements are at
  one parameter, under conditions that hold at almost every parameter.
- **Which functional dimension of the residual network is on the other side? Lean's `funDim`, not
  the paper's.**

  ```
  ∀ᵐ p ∂μ, ∀ᵐ θ' ∂ν, funDimSkipsOn (Arch.mlp relu (rmsNorm ε) hid) (triSkips d 1) p (noKinkRMS p.1)
    = funDim (Arch.mlp relu (rmsNorm ε) hid) 1 θ' + Fintype.card d * (Fintype.card d + 1) / 2
  ```
  **Said plainly: the left side is the largest rank over the batches of inputs off the kinks; the
  right side is Lean's `funDim`, the largest rank over all batches** (a batch with an input at
  which the output is not differentiable counts with rank `0`, so the only extra batches are those
  with an input on a kink at which the output happens to be differentiable). The docstrings ("is
  that of the residual network at `θ'` plus `d (d + 1)/2`") and the index row do not say this.
- **It does no harm.** For the residual network the library has, at almost every `θ'`, both the
  value of `funDim` (`ae_funDim_relu_oneBlock_residual_rmsNorm`) and a batch of inputs off the
  kinks with this rank (`ae_exists_jacobianRank_relu_oneBlock_residual_rmsNorm`; the same with
  `reluSq`, `reglu`). So the largest rank over the batches off the kinks of `θ'` is `funDim` there.
  I compiled the equality with both sides in the paper's sense (`Chk2.lean`: `relu_same_sense`,
  `reluSq_same_sense`, `reglu_same_sense`): at almost every `(θ, A)` and almost every `θ'` there
  is a batch `X` of inputs off the kinks of `θ'` whose rank no batch at all exceeds, and
  `funDimSkipsOn … p (noKinkRMS p.1) = jacobianRank … 1 X θ' + d(d+1)/2`. So the three statements
  do give the paper's "exceeds that of the residual network of part (ii) by exactly `d(d+1)/2`".
- A remark. The header says that the value of Lean's `funDimLearnedTri` is not stated for these
  blocks. For ReLU² it follows in a few lines, because the ReLU² block is differentiable
  everywhere: by compiling (`Chk2.lean`, `reluSq_funDimLearnedTri`), under `OneBlockGenericRMS`
  and for an invertible triangular `R`, `funDimLearnedTri … (θ, R) = funDimSkipsOn … (θ, R)
  (noKinkRMS θ)` (from `funDimLearnedTri_eq_funDimLearned` and
  `funDimLearned_mlp_rescale_rmsNorm`). For ReLU and ReGLU I did not check it.

### Check 3. No extra hypotheses against Theorem B.1 (iii) and its Scope

**Verdict: none. Every hypothesis of the eight named `ae_` statements is in Theorem B.1 or follows
from it, and Lean asks less in two places.** (By reading; the instance arguments from the compiled
signatures, `Sig.out`; two instances by compiling.)

| Lean hypothesis | In which `ae_` statements | Theorem B.1 has it or implies it? |
|---|---|---|
| `[μ.IsAddHaarMeasure]`, `[ν.IsAddHaarMeasure]` | all 8 | "For generic parameters" |
| `hε : 0 < ε` | all 8 | "(iii) … For generic parameters and `ε > 0`" |
| `hd : 2 ≤ Fintype.card d`, `hdIn`, `hdOut` | all 8 | "Let `d_model ≥ 2`, let the input and output dimensions be at least `d_model`" |
| `[Nonempty T]` (at least one token) | all 8 | implicit: an input has a token |
| `[LinearOrder d]` | all 8 | needed to say "upper triangular"; any order |
| `[Nonempty (hid 0)]` (at least one hidden unit) | the 6 for ReLU, ReLU², ReGLU | "a … ReLU, ReLU², ReGLU … block": a block has a hidden unit. No width is asked, as in part (iii) |
| `[Nonempty (H 0)]` (at least one head) | the 2 for attention | "an attention block of `H` heads" |
| `hdh : ∀ ℓ, card (dh ℓ) ≤ card d` | the 2 for attention | "of width `d_h ≤ d_model`" |
| `hdh0 : ∀ ℓ, 0 < card (dh ℓ)` | the 2 for attention | a head has width at least `1` |
| `(t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁)` | the 2 for attention | implied: "causal or not, on sequences of at least two tokens": under both masks the second token sees itself and the first |

- **Lean asks less.** (1) The mask: only one token is asked to see itself and another token; all
  other tokens may see anything or nothing. Theorem B.1 has the two masks. I computed this case
  (Check 4: a mask in which token 0 sees nothing; the values are those of the statement), and
  compiled an instance (`Chk3.lean`: two tokens, token 1 sees both, token 0 sees nothing, one head
  of width 1, `d = 2`: `funDimLearnedTri = 16` at almost every `(θ, A)`). (2) The statements at one
  parameter ask no `d ≥ 2` and, for attention, no second token and no `d_h ≤ d`.
- The hypotheses that exclude a block with no hidden unit, no head, or a head of width `0` are
  needed: the seventeenth reader computed that the gain is `0` there.
- By compiling (`Chk.lean`, `Chk3.lean`): `ae_funDimSkipsOn_tri_relu_rmsNorm` instantiates with
  one token, `d = d_in = d_out = 2` and one hidden unit (narrower than `d`) and gives the value
  `13` (`P = 12`); `…_reglu_…` with one hidden unit gives `14` (`P = 14`); `…_reluSq_…` with three
  hidden units gives `19` (`P = 20`). These are the numbers of my computation.

### Check 4. The value `P + d(d+1)/2 − d(d−1)/2 − s`

**Verdict: it is the paper's. I could not refute any of the four named statements, nor the
statements at one parameter: 67 comparisons inside the hypotheses, all with the value or the gain
of the statement.** (The value by reading; the rest by a computation.)

- **Is it the paper's? Yes.** Lean: `fd + (d(d−1)/2 + s) = P + d(d+1)/2`, with `P = finrank ℝ
  (Params …)` the number of the weights `E`, `W_read`, `W_write`, `D` without the skip, and
  `s = card (hid 0)` (ReLU, ReLU²), `2 * card (hid 0)` (ReGLU), `2 * ∑ ℓ, card (H ℓ) * card (dh
  ℓ) ^ 2` (attention). Paper, part (ii): the residual network has `P − d(d−1)/2 − s`; part (iii):
  "exceeds that of the residual network of part (ii) by exactly `d_model (d_model + 1)/2`"; Step 5:
  for an upper triangular `A` the rotations "have dimension `d_model (d_model − 1)/2`", the
  network has "`d_model (d_model + 1)/2` more parameters". The same number,
  `P + d − s`; both divisions by `2` are exact.
- **The computation.** Network `y = N_ε(h_1) D`, `h_1 = x E A + f(N_ε(x E) W_read) W_write`; the
  rank of the Jacobian in the weights (and the entries `i ≤ j` of `A`) on one batch; "res" is the
  residual network (`A = I` fixed) on the same batch. ReLU kinds: eight inputs per parameter, all
  off the kinks, two batches. Attention: exact derivatives too.

  | Statement | Cases | Result |
  |---|---|---|
  | `ae_funDimSkipsOn_tri_relu_rmsNorm` (`ls18_relu.out`) | `d = 2`, 3 units; `d = 2`, 1 unit (narrow); `d = 3`, 2 units (narrow); `d = 2`, `d_in = d_out = 3`, two tokens; two batches each | res 16, 10, 25, 17; triangular 19, 13, 31, 20: the values `P − d(d−1)/2 − s` and `P + d − s` in all 8 |
  | `…_reluSq_…` (`ls18_relusq.out`) | `d = 2`, 3 units; `d = 2`, 1 unit; `d = 3`, `d_out = 4`, 2 units; two batches each | res 16, 10, 28; triangular 19, 13, 34: right in all 6 |
  | `…_reglu_…` (`ls18_reglu.out`) | `d = 2`, 2 units; `d = 2`, 1 unit; `d = 3`, 1 unit; `d = 2`, `d_in = 3`, two tokens; two batches each | res 15, 11, 22, 17; triangular 18, 14, 28, 20: right in all 8 |
  | `ae_funDimLearnedTri_attention_rmsNorm` (`ls18_attn.out`, `ls18_attn2.out`, `ls18_attn3.out`) | `d = 2`: no mask and causal, `(H, d_h)` = (1, 1), (2, 1), (1, 2), two and three tokens, `d_in = 3`, `d_out = 4`; **a mask in which token 0 sees nothing**, `(H, d_h)` = (1, 1), (1, 2), (2, 2), also `d = 3`, `d_in = 4`; `d = 3`: (1, 2) causal, (1, 3) no mask, (2, 1) on three tokens | triangular 16, 22, 18, 16, 26, 22, 16, 16, 16, 16, 16, 18, 41, 34, 37, 39 = `P + d − 2 H d_h²` in all 16; the gain over the residual network `d(d+1)/2` in all |
  | the statements at one parameter, special invertible triangular skips (`ls18_more_skips.out`) | ReLU, ReGLU and attention with `A = I`, `diag(1, −2)`, `[[10⁻⁶, 1], [0, 1]]`, `[[1, 50], [0, 1]]`; ReLU² with `d = 3`, `A = [[1,0,0],[0,−1,3],[0,0,0.001]]` | value and gain right in all 13 |
  | the same, special weights that `OneBlockGenericRMS`, `OneBlockGenericReGLURMS` allow (`ls18_more_weights.out`) | ReLU with all rows of `W_write` equal, `d_out > d`; ReLU with the read columns `e_1, e_2, e_1 + e_2`; ReGLU with all value columns equal and all write rows equal; two batches each | value and gain right in all 6 |
  | `funDimLearnedTri_attention_rmsNorm_eq_residual_add` (one parameter: `E`, `D` of rank `d`, a token that sees a token, `S ≠ 0`; only the gain is claimed) (`ls18_more_attn.out`) | one token; `W_Q = 0`; `W_Q = W_K = 0` on three tokens; two heads with equal values and outputs (causal); a mask in which token 0 sees token 1 only and token 1 sees nothing | gain `3` in all 5 (residual, triangular: 10, 13; 12, 15; 10, 13; 19, 22; 10, 13) |
  | the statements at one parameter with `d = 1` (`ls18_more_d1.out`) | ReLU, ReGLU (two batches each), attention on two tokens | gain `1`, values right, in all 5 |

- No value came out different on a first batch, so the brief's rule of a second batch was never
  needed to settle a case.
- **Outside the hypotheses** (`ls18_more_outside.out`; not counterexamples). At the skip `A = 0`
  the triangular family has rank 15 and the full family 16 (ReLU, `d = 2`): the invertible skip is
  needed. At two triangular skips of rank one the two were equal (16). Attention with `W_O = 0`
  (`S = 0`): gain `0` (9 and 9).
- The coordinator's script (`learned_skip_relu_attention_check_2026-11-24.py`) has the triangular case
  for the three MLP kinds only, with one token; for attention it has the full skip, by central
  differences. Where its shapes and mine are the same the ranks agree (19, 31, 18, 28 for the
  triangular skip: ReLU `d = 2` and `d = 3`, ReGLU `d = 2` and `d = 3`).

### Check 5. Lemma A.5

**Verdict: SAME, for every `r`.** (By reading; `r = 1`, `r = 2` and the degree by compiling.)

```
theorem exists_polynomial_of_sum_ridge_eq_zero {d q : Type*} [Fintype d] [Fintype q] {r : ℕ}
    (a : Fin r → d → ℝ) (ha : ∀ i, a i ≠ 0) (hcol : ∀ i j, i ≠ j → ∀ c : ℝ, a i ≠ c • a j)
    (g : Fin r → ℝ → q → ℝ) (hg : ∀ i, ContDiff ℝ (r - 1 : ℕ) (g i))
    (hsum : ∀ x : d → ℝ, ∑ i, g i (a i ⬝ᵥ x) = 0) (i : Fin r) (k : q) :
    ∃ P : Polynomial ℝ, P.degree < ((r - 1 : ℕ) : WithBot ℕ) ∧ ∀ t, g i t k = P.eval t
```

- **`r = 1`: the zero polynomial.** By compiling (`Chk.lean`): `P.degree < ((1 - 1 : ℕ) : WithBot
  ℕ)` gives `P = 0`; and from the lemma with `r = 1` I derived `g 0 = 0`. The paper's "degree at
  most `r − 2 = −1`" is the zero polynomial, and indeed `g_1(a_1 · x) = 0` for all `x` with
  `a_1 ≠ 0` gives `g_1 = 0`. The same.
- **`r = 2`: a constant.** By compiling: `P.degree < ((2 - 1 : ℕ) : WithBot ℕ)` gives `P = C c`.
  For `r ≥ 2`, `P.degree < ↑(r − 1) ↔ P.degree ≤ ↑(r − 2)` (compiled): "degree at most `r − 2`".
- **"Pairwise non-collinear"** is `hcol : ∀ i j, i ≠ j → ∀ c : ℝ, a i ≠ c • a j`, with `ha` for
  "nonzero": the paper's. **The product** `a i ⬝ᵥ x` is `∑_k a_{i,k} x_k`, the paper's `a_i · x`;
  `∑ i, g i (a i ⬝ᵥ x) = 0` is an equality in `ℝ^q` (`q → ℝ`). `ContDiff ℝ (r - 1 : ℕ)` is "`r −
  1` times continuously differentiable". "Every `g_i` is a polynomial" is said of each of the `q`
  coordinates, which for finitely many coordinates is the same.
- **`r = 0`: true.** There is no `i : Fin 0`, so the statement says nothing, as the paper's does
  with no function. (The natural-number subtraction `0 − 1 = 0` is never used.)
- If `d` has one element and `r ≥ 2`, no family is pairwise non-collinear and both statements are
  empty; the same in the paper.
- `iteratedDeriv_eq_zero_of_sum_ridge_eq_zero` (`iteratedDeriv (r - 1) (g i) = 0`) is the last line
  of the paper's proof, "so `g_i^{(r−1)} = 0`".

### Check 6. Lemma A.6

**Verdict: SAME; true for `n = 0` and for an infinite index `q`.** (By reading; one instance by
compiling.)

```
theorem eq_zero_of_sum_smul_scaled_eq_polynomial {q : Type*} {n : ℕ} (ψ : ℝ → ℝ)
    (hψ : AnalyticOnNhd ℝ ψ Set.univ) (hnp : ¬ ∃ P : Polynomial ℝ, ∀ t, ψ t = P.eval t)
    (α : Fin n → ℝ) (hα : ∀ k, 0 < α k) (hinj : Function.Injective α) (a : Fin n → q → ℝ)
    (hP : ∀ j : q, ∃ P : Polynomial ℝ, ∀ t, ∑ k, a k j * ψ (α k * t) = P.eval t) :
    ∀ k, a k = 0
```

- "Real-analytic" is analytic at every point of `ℝ`; "not a polynomial" is "no real polynomial
  agrees with `ψ` everywhere"; "`α_1, …, α_n > 0` distinct" is `hα`, `hinj`; "`∑_k a_k ψ(α_k t)`
  is a polynomial in `t`" is asked of every coordinate `j`. All the paper's.
- **`n = 0`:** the conclusion is about no `k`; true.
- **`q` infinite:** the statement has no `Fintype q` (compiled with `q = ℕ`, `Chk.lean`). The
  hypothesis is then weaker than "a polynomial with coefficients in `ℝ^q`" (the degrees of the
  coordinates need not be bounded) and the conclusion is the same, so the Lean statement is
  slightly stronger than the paper's; the argument is coordinate by coordinate. For finite `q` the
  two hypotheses are the same.

### Check 7. Lemma A.14

**Verdict: the Lean statement is the paper's for both masks, and stronger: any mask in which some
token sees every token. It is false on two tokens (compiled counterexample against every clause),
as the paper says. It is true for a mask in which one token sees every token and the others see
nothing (it is an instance of the proved statement; also computed). The hypothesis on the mask
cannot simply be dropped.** (By reading; by compiling; by a computation; one step by hand.)

```
theorem attnHeads_identifiable (sees : T → T → Prop) [DecidableRel sees]
    (hT : 3 ≤ Fintype.card T) (hsees : ∃ t₀, ∀ s, sees t₀ s) {m : ℕ}
    (Γ : Fin m → Matrix d d ℝ) (hΓ : Function.Injective Γ) (C : Fin m → Matrix d d ℝ)
    (M : Matrix d d ℝ) (U : Set (Matrix T d ℝ)) (hU : IsOpen U) (hne : U.Nonempty)
    (h0 : ∀ h ∈ U, h * M + ∑ k, attnWeights sees (h * Γ k * hᵀ) * h * C k = 0) :
    M = 0 ∧ ∀ k, C k = 0
```

| Paper | Lean | |
|---|---|---|
| "Let `T ≥ 3`" | `hT : 3 ≤ Fintype.card T` | same |
| "with or without a causal mask" | `hsees : ∃ t₀, ∀ s, sees t₀ s`; by name `attnHeads_identifiable_noMask` (`fun _ _ => True`) and `attnHeads_identifiable_causal` (`Fin n`, `3 ≤ n`, `fun t s => s ≤ t`) | Lean stronger: any mask with one token that sees all. The paper's proof uses the mask through "the last row, which attends to all `T` tokens" only |
| "`Γ_1, …, Γ_m` […] distinct" | `hΓ : Function.Injective Γ` | same |
| "for all `h` in a nonempty open subset of `ℝ^{T × d_model}`" | `hU`, `hne`; the topology is the product topology of `ℝ^{T × d}` (by `rfl`, `Chk.lean`) | same |
| "`h M + ∑_k P_{Γ_k}(h) h C_k = 0`" | `h0` | same |
| "then `M = 0` and `C_1 = ⋯ = C_m = 0`" | `M = 0 ∧ ∀ k, C k = 0` | same |

- **`attnWeights sees (h * Γ k * hᵀ)` is `P_Γ(h)`, row by row, for both masks.** The Lean text:

  ```
  noncomputable def attnWeights (sees : T → T → Prop) [DecidableRel sees] (Z : Matrix T T ℝ) : Matrix T T ℝ :=
    Matrix.of fun t s =>
      if sees t s then Real.exp (Z t s) / ∑ s', if sees t s' then Real.exp (Z t s') else 0 else 0
  ```
  The entry `(t, s)` of `h Γ hᵀ` is `h_t Γ h_sᵀ` (compiled). Row `t` is the softmax of the scores
  of the tokens that `t` sees and `0` elsewhere: all tokens without a mask, the tokens `s ≤ t`
  with the causal mask. A token that sees no token has the row `0` (compiled); this does not occur
  under the paper's masks.
- **Two tokens: false.** By compiling (`Chk.lean`, `two_tokens_weights`,
  `two_tokens_counterexample`, three standard axioms): on two tokens without a mask,
  `attnWeights Z + attnWeights (−Z) = 2 • attnWeights 0` for every `Z` (the paper: "`1/(1 + e^{−z})
  + 1/(1 + e^{z}) = 1`"); and with one coordinate, the score matrices `1, −1, 0` and the
  coefficients `1, 1, −2`, `M = 0`: the `Γ_k` are distinct, a token sees every token, the set of
  all `h` is open and not empty, the identity holds at every `h`, and the coefficients are not
  zero. So every clause of `attnHeads_identifiable` holds except `3 ≤ Fintype.card T`, and the
  conclusion fails. By a computation (`ah18.out`): with `d = 2` and `Γ = G, −G, 0` the map
  `(M, C_1, C_2, C_3) ↦ (h ↦ h M + ∑ P_{Γ_k}(h) h C_k)` has a kernel of dimension `4 = d²` on two
  tokens, without a mask and with the causal mask; with `Γ = G, −G` only, or `G, 2G, 0`, it is
  injective on two tokens.
- **Three tokens and more** (`ah18.out`; 18 cases in all, two draws of `h` each): the map is
  injective for
  `Γ = G, −G, 0` without a mask and with the causal mask (three and four tokens); for
  `G, −G, 0, 2G, Gᵀ, 1.001 G`; for score matrices of rank one; for antisymmetric ones; for `d = 1`.
- **A mask in which one token sees every token and the others see nothing: true.** It is an
  instance of the proved statement. By a computation: injective when only the last token sees
  (all three tokens), when only the middle token sees, and when the others see only themselves.
  By hand, for the step of the paper's proof that uses other rows ("The first two rows give
  `x(M + C_0/T_1) = 0` and `x C_0/T_2 = 0`"): with only the row `t₀`, `h_{t₀} M + (1/T) ∑_s h_s
  C_0 = 0` for all `h`; an `h` with one nonzero row `s ≠ t₀` gives `C_0 = 0`, then `M = 0`.
- **The hypothesis on the mask is needed.** By a computation: on three tokens, if every token
  sees itself and the next one only (no token sees three tokens), `Γ = G, −G, 0` has again a
  kernel of dimension `4`. So `3 ≤ card T` alone would not do; Lean asks "some token sees every
  token", which both masks of the paper satisfy.

### Check 8. Proposition A.15

**Verdict: SAME. Blocks with different numbers of heads and different head dimensions are
allowed, and that is the paper's statement.** (By reading.)

```
theorem attentionBlock_sum_eq_of_mul_add_eq (sees : T → T → Prop) [DecidableRel sees]
    (hT : 3 ≤ Fintype.card T) (hsees : ∃ t₀, ∀ s, sees t₀ s) {H dh H' dh' : Type*} [Fintype H]
    [Fintype dh] [Fintype H'] [Fintype dh'] (WQ WK WV : H → Matrix d dh ℝ)
    (WO : H → Matrix dh d ℝ) (WQ' WK' WV' : H' → Matrix d dh' ℝ) (WO' : H' → Matrix dh' d ℝ)
    (M : Matrix d d ℝ) (U : Set (Matrix T d ℝ)) (hU : IsOpen U) (hne : U.Nonempty)
    (h0 : ∀ h ∈ U, h * M + attentionBlock sees WQ WK WV WO h
      = attentionBlock sees WQ' WK' WV' WO' h) :
    M = 0 ∧ ∀ G : Matrix d d ℝ,
      (∑ i, if (Real.sqrt (Fintype.card dh))⁻¹ • (WQ i * (WK i)ᵀ) = G then WV i * WO i else 0)
        = ∑ i, if (Real.sqrt (Fintype.card dh'))⁻¹ • (WQ' i * (WK' i)ᵀ) = G
            then WV' i * WO' i else 0
```

- "`h M + B_θ(h) = B_{θ′}(h)` for all `h` in a nonempty open set" is `h0` with `hU`, `hne`; `M` is
  on the side of `θ`, as in the paper. "Then `M = 0`" is the first conclusion.
- "For every matrix `Γ`, the heads with score matrix `Γ` have the same sum of value–output
  products in `B_θ` as in `B_{θ′}`" is the second: for every `G`, the sum of `C_i` over the heads
  `i` with `Γ_i = G`, on both sides (a sum of `if Γ i = G then C i else 0`). A matrix `G` that is
  the score matrix of no head gives `0 = 0`.
- `attentionBlock` is `attnHeads` with `Γ_i = (√d_h)⁻¹ • (W_{Q,i} W_{K,i}ᵀ)` and `C_i = W_{V,i}
  W_{O,i}` (its definition), which is A equation (4): "`Γ_i = W_{Q,i} W_{K,i}^⊤ / √d_h`", "Head `i`
  has the score matrix `Γ_i` and the value–output product `W_{V,i} W_{O,i}`".
- **Different shapes.** `H`, `dh` and `H'`, `dh'` are four independent types. The Proposition says
  "let `θ` and `θ′` be parameters of attention blocks", with no common shape; the theorem that it
  stands beside (A Theorem 3.4, A.13) says "with any numbers of heads and any head dimensions";
  and the main text describes its content as "up to merging heads that share a score matrix and
  dropping heads that output zero", which needs different numbers of heads. Within one block all
  heads have one dimension, in the paper and in Lean.
- `attnHeads_sum_eq_of_mul_add_eq` is the same for blocks given by `Γ_i` and `C_i`; the masks are
  as in Check 7 (any mask with a token that sees every token), so it is stronger than the paper's
  two masks.

---------------------------------------------------------------------------------------------------

## Part 2: the statements, file by file

Verdicts: SAME, LEAN STRONGER, LEAN WEAKER, DIFFERENT, PART, FALSE. All 24 theorems are proved (no
`sorry`, three standard axioms, `Ax.out`). None is FALSE, none DIFFERENT, none LEAN WEAKER.

### `OneBlock/LearnedSkipTriangularSmooth.lean` (4 theorems)

Paper: S Theorem B.1 (iii) and Step 5 of its proof ("For an upper triangular `A`, `A Y − X_a A`
must be upper triangular […] In both cases the functional dimension is larger by `d_model (d_model
+ 1)/2`").

| Name | Verdict |
|---|---|
| `funDimLearnedTri_eq_funDim_residual_add_of_noSymmetricPart` | LEAN STRONGER than Step 5 for the triangular skip at generic parameters: at every `θ` with `E`, `D` of rank `d`, every invertible upper triangular skip, any continuously differentiable block with Step 4 (`NoSymmetricPart` at all inputs). Another route than the paper's count (through the full skip) |
| `funDimLearnedTri_attention_rmsNorm_eq_residual_add` | LEAN STRONGER: one parameter (`E`, `D` of rank `d`, a token that sees a token, `S ≠ 0`), every invertible triangular skip, any `H`, `d_h`, mask |
| `ae_funDimLearnedTri_attention_rmsNorm` | SAME as Theorem B.1 (iii) for attention and the triangular skip, `ε > 0`: the value `P + d(d+1)/2 − d(d−1)/2 − 2 H d_h²` ("it satisfies the equality condition"). The mask is more general than the paper's two |
| `ae_funDimLearnedTri_attention_rmsNorm_eq_residual_add` | SAME: "exceeds that of the residual network of part (ii) by exactly `d(d+1)/2`"; both sides are functional dimensions over all inputs (the block is analytic) |

### `OneBlock/LearnedSkipTriangularRescale.lean` (1 definition, 12 theorems)

Paper: S Theorem B.1 (iii); S Appendix B, "Notation and flat directions".

| Name | Verdict |
|---|---|
| `funDimSkipsOn` | SAME as the paper's functional dimension of a network with ReLU-type blocks when `U` is the set of the inputs off the kinks and the family of skips is finite-dimensional (Check 2) |
| `exists_jacobianRankSkips_tri_mlp_rescale_rmsNorm`, `exists_jacobianRankSkips_tri_reglu_rmsNorm` | PART (the lower bound, in the paper's sense) and LEAN STRONGER in its range: one parameter under the conditions of the proof, every invertible triangular skip; any activation that is homogeneous of degree `k ≥ 1` with Lemma B.3 |
| `jacobianRankSkips_tri_add_le_mlp_rescale_rmsNorm`, `jacobianRankSkips_tri_add_le_reglu_rmsNorm` | PART (the upper bound on the batches off the kinks), the same range |
| `funDimSkipsOn_tri_mlp_rescale_rmsNorm`, `funDimSkipsOn_tri_reglu_rmsNorm` | LEAN STRONGER than the value of Theorem B.1 (iii) at generic parameters: at one parameter, every invertible triangular skip |
| `ae_funDimSkipsOn_tri_relu_rmsNorm`, `…_reluSq_…`, `…_reglu_…` | SAME as Theorem B.1 (iii) for the triangular skip, `ε > 0`, in the paper's sense; any width from one hidden unit on, as in the theorem; `s = d_hidden`, for ReGLU `2 d_hidden` |
| the three `…_eq_residual_add` | SAME in content as "exceeds that of the residual network of part (ii) by exactly `d(d+1)/2`". In form the two sides are in different senses (Check 2); they agree by `ae_exists_jacobianRank_{relu,reluSq,reglu}_oneBlock_residual_rmsNorm` |

### `Absorb/RidgeFunctions.lean` (3 theorems)

| Name | Verdict |
|---|---|
| `iteratedDeriv_eq_zero_of_sum_ridge_eq_zero` | SAME as the last line of the proof of Lemma A.5, "so `g_i^{(r−1)} = 0`" |
| `exists_polynomial_of_sum_ridge_eq_zero` | SAME as A Lemma A.5 (Check 5) |
| `eq_zero_of_sum_smul_scaled_eq_polynomial` | SAME as A Lemma A.6; slightly LEAN STRONGER (any index type `q`) (Check 6) |

### `Absorb/AttentionHeadsIdentifiable.lean` (5 theorems)

| Name | Verdict |
|---|---|
| `attnHeads_identifiable` | LEAN STRONGER than A Lemma A.14: any mask in which some token sees every token (Check 7) |
| `attnHeads_identifiable_noMask` | SAME as Lemma A.14 without a mask |
| `attnHeads_identifiable_causal` | SAME as Lemma A.14 with the causal mask (tokens `Fin n`, `n ≥ 3`, token `t` sees `s ≤ t`) |
| `attnHeads_sum_eq_of_mul_add_eq` | SAME as A Proposition A.15 for blocks given by score matrices and value–output products; the mask as in the lemma |
| `attentionBlock_sum_eq_of_mul_add_eq` | SAME as A Proposition A.15 for the blocks of A equation (4) (Check 8) |

### The index rows of the four files, and `checks/Axioms.lean`

By a script (`index_names18.py`, `index_names18.out`), at `20eacc6`: every one of the 25 public
names is in the row of its file (lines 827, 828, 830, 831), 18 written out and 7 by the
abbreviation "the same two with `reluSq`, and the same five with `reglu`"; all 24 theorems stand
in `checks/Axioms.lean`; all four rows say "proved", which is right. Nothing in the rows is wrong.
What is missing or thin is in the corrections below.

---------------------------------------------------------------------------------------------------

## What the authors should know

Nothing false, vacuous or drifted in the 25 names. One thing is described too briefly (item 1). In
order of weight:

1. **In `ae_funDimSkipsOn_tri_{relu,reluSq,reglu}_rmsNorm_eq_residual_add` the two sides are in
   different senses.** Left: the largest rank over the batches of inputs off the kinks. Right:
   Lean's `funDim` of the residual network, over all batches. The docstrings and the index row say
   "that of the residual network" without a word on it. The equality with both sides in the
   paper's sense is true and follows from the library (compiled, `Chk2.lean`); a sentence in the
   docstrings and the row would close the gap, or three corollaries of four lines each.
2. **Lemma A.14 on two tokens is false, and I have a compiled counterexample** (`Chk.lean`,
   `two_tokens_counterexample`: one coordinate, score matrices `1, −1, 0`, coefficients
   `1, 1, −2`). It is the paper's example, "two heads with opposite score matrices add up to a
   uniform head". The authors may want it in the library as the statement that `3 ≤ card T` cannot
   be weakened.
3. **The hypothesis `hsees` of Lemma A.14 is needed as well:** on three tokens with a mask in
   which no token sees more than two tokens the same cancellation occurs (computed). Lean's
   condition, "some token sees every token", is more general than the paper's two masks; the
   lemma holds when the other tokens see nothing (computed, and one step by hand).
4. **The triangular skip for attention had no numeric check by the coordinator** (the script has the
   full skip for attention, by central differences). My computation: 16 generic cases and 10
   special ones with exact derivatives, all with the value or the gain of the statements, among
   them a mask in which one token sees nothing, which the Lean hypotheses allow and the paper's
   masks do not include.
5. **For ReLU² the value of Lean's `funDimLearnedTri` follows in a few lines** (compiled,
   `reluSq_funDimLearnedTri`): the block is differentiable everywhere, so
   `funDimLearnedTri_eq_funDimLearned` applies. The header's "The value of Lean's
   `funDimLearnedTri` […] is not stated" is then only about ReLU and ReGLU.
6. Lean asks less than Theorem B.1 for attention (one token that sees itself and another, any
   other mask) and nothing more than it anywhere (Check 3).
7. The invertible skip is needed in the statements at one parameter (at `A = 0` the triangular
   family has one dimension less than the full one, `d = 2`); for attention `S = 0` through
   `W_O = 0` gives the gain `0`. Both are outside the hypotheses.
8. `funDimSkipsOn` is defined for any normed space `V` of skips; its supremum is a maximum only
   when `V` is finite-dimensional. All uses are finite-dimensional.
9. Lemma A.5 for `r = 1` gives the zero function and for `r = 0` says nothing; Lemma A.6 is stated
   for any index type `q`, a little more than the paper.
10. "Satisfies the equality condition" is, here as in the earlier files, the value
    `P + d(d+1)/2 − d(d−1)/2 − s`; Lean has no definition of the symmetries of a network with a
    learned skip.

## Corrections for `STATEMENTS.md` (line numbers of `20eacc6`)

1. Lines 193 to 201, "Not yet compared by such a reader […] `OneBlock/LearnedSkipTriangularSmooth.lean`,
   `OneBlock/LearnedSkipTriangularRescale.lean`, `Absorb/RidgeFunctions.lean`,
   `Absorb/AttentionHeadsIdentifiable.lean`, …": take these four out after this audit (compared at
   `f0edc93`; unchanged at `20eacc6`).
2. Line 828 (`OneBlock/LearnedSkipTriangularRescale.lean`), "and `d(d+1)/2` more than the residual
   network at almost every `θ'`": add "(the residual side is Lean's `funDim`; at almost every `θ'`
   it is the largest rank over the batches of inputs off the kinks, by
   `ae_exists_jacobianRank_{relu,reluSq,reglu}_oneBlock_residual_rmsNorm`)".
3. The same row, "The value of Lean's `funDimLearnedTri` […] is not stated for these blocks": for
   ReLU² it follows from `funDimLearnedTri_eq_funDimLearned` (the block is differentiable
   everywhere); say "for ReLU and ReGLU blocks", or state the ReLU² corollary.
4. The same row, "the same two with `reluSq`, and the same five with `reglu`": the five are not
   one substitution (three replace `mlp_rescale` by `reglu`, two replace `relu` by `reglu`). Write
   them out: `exists_jacobianRankSkips_tri_reglu_rmsNorm`,
   `jacobianRankSkips_tri_add_le_reglu_rmsNorm`, `funDimSkipsOn_tri_reglu_rmsNorm`,
   `ae_funDimSkipsOn_tri_reglu_rmsNorm`, `ae_funDimSkipsOn_tri_reglu_rmsNorm_eq_residual_add`.
5. Line 827 (`OneBlock/LearnedSkipTriangularSmooth.lean`). Nothing wrong. Could add: "the mask is
   asked of one token only (the paper: causal or not); no numeric check by the coordinator for the
   triangular skip with attention, the eighteenth reader computed 16 generic cases".
6. Line 831 (`Absorb/AttentionHeadsIdentifiable.lean`). Nothing wrong. Could add: "false on two
   tokens (the paper's example; compiled by the eighteenth reader), and false on three tokens if
   no token sees more than two".
7. Line 830 (`Absorb/RidgeFunctions.lean`). Nothing wrong. Could add: "for `r = 1` the zero
   polynomial; Lemma A.6 for any index type `q`".
8. Outside the index: the docstrings of the three `ae_funDimSkipsOn_tri_…_eq_residual_add` and the
   header of `OneBlock/LearnedSkipTriangularRescale.lean` (line 31, "`d (d + 1)/2` more than the
   residual network at almost every `θ'`"): the sentence of correction 2.

## What I could not check

- **The proofs.** I read none as a proof. "Proved" means no `sorry` in the file and the three
  standard axioms in the build of `/home/claude/lp/lean` (its sources of the nine files equal
  those of `/home/claude/lw`).
- **The build.** I did not build the library. I compiled my files against the build of
  `/home/claude/lp/lean` (its owner's), read-only. Its owner rebuilt it while I worked (19:00 to
  19:04 UTC); my compiled results are all from after that.
- **The values beyond small shapes.** The computation covers one block with `d ≤ 3`, at most three
  tokens, at most four hidden units, `H ≤ 2`, `d_h ≤ 3`, one or two draws of the weights per case,
  60 digits. A rank on a batch is a lower bound for the largest rank; it agrees with the upper
  bound of the statements in every case, which supports them and proves nothing.
- **"No batch off the kinks has a larger rank"** cannot be tested by a computation on random
  batches; I rely on the argument (the rotations and the symmetries inside the block are flat).
- **Lean's `funDimLearnedTri` for ReLU and ReGLU blocks** (all batches, with the inputs on the
  kinks at which the output happens to be differentiable): not stated, and not checked by me.
- **Lemma A.14 in general.** The computation tests the injectivity at chosen score matrices with
  `d ≤ 2` and at most four tokens, at random `h` over the whole space, not on a small open set
  (the functions are analytic, so this is the same question). That a token which sees three tokens
  would be enough in place of "sees every token": not checked.
- **The coordinator's script** `learned_skip_relu_attention_check_2026-11-24.py`: not run; I read its
  output.
- **The older statements that these files use** (`funDimLearnedTri_eq_funDimLearned`,
  `funDimLearned_eq_funDim_residual_add_of_noSymmetricPart`, the residual values, `finrank_params`
  and its forms): compared by earlier readers; I read them and did not compare them again.

Scratch files: `/home/claude/audit18a/` (`Ax.lean`, `Sig.lean`, `Chk.lean`, `Chk2.lean`,
`Chk3.lean`, `index_names18.py`, `ls18core.py`, `ls18fd.py`, `ls18run.py`, `ls18more.py`,
`ls18attn2.py`, `ah18.py`, with their outputs `*.out`).
