STATUS: complete

# Twenty-first audit, part A, of Lean statements against the papers: `ε = 0`; the value for the residual network in part (iv) of S Theorem B.1; S Theorem A.5 (iii) for `ε = 0`; the last sentence of S Theorem A.17 at any depth (24 November 2026)

Reader: an independent reader who did not write the statements. Brief:
`audit21a_brief_2026-11-24.md`. I audited statements and definitions, not proofs. I changed no
repository file, ran no `lake build`, made no commit and no push. My files are in
`/home/claude/audit21a/`.

Library: `/home/claude/lw/lean` (branch `lean-wip`).

- **Commit read: `8084e308484f1c412eb3057f031e43ac14acdbdd` (24 November 2026, 21:01:25 UTC),** the
  head when I started. The branch moved while I worked; I looked at it again at `f21e8ed`
  (21:15:05), `f223d48` (21:21:39), `1c859c6` (21:32:38), `340a1a4` (21:36:41) and
  **`72700dd3182ac9e58d58d2c394f04c213f9c99ea` (21:42:14), the head when I finished.** Four of the
  five files are byte for byte the same at all six commits (`git diff` is empty), and so is every
  file of definitions that I read. The fifth,
  `Dimension/UpperBoundHomogeneousRMSNormZero.lean`, had nine statements with `sorry` at `8084e30`;
  since commit `0ac8d09` (in `f21e8ed`) it has proofs. Its header, its `variable` lines and the
  text of its nine statements are the same before and after (compared by a script,
  `UBH_8084e30.lean` against the file at the head), and it has not changed since `0ac8d09`.
- **Files with `sorry`** (`git grep -w sorry` on `lean/SkipsLean` at each commit): at `8084e30`
  one file, `Dimension/UpperBoundHomogeneousRMSNormZero.lean` (of this audit; proved since
  `0ac8d09`). At `f21e8ed` two files (`OneBlock/ResidualRMSZeroReGLU.lean`,
  `Symmetry/InsideBlocksRMSNormZero.lean`); at `f223d48` none; at `1c859c6` three
  (`OneBlock/SkiplessHomogeneousRMSZeroEq.lean`, `OneBlock/SkiplessRMSZeroReadout.lean`,
  `OneBlock/UnitsParallel.lean`); at `72700dd` three
  (`OneBlock/SkiplessHomogeneousRMSZeroEq.lean`, `OneBlock/UnitsParallel.lean`,
  `Residual/LearnedSkipsConformal.lean`). All of these were written after I started; none is of
  this audit and none is imported by the five files.
- The five files have 23 public theorems (1 + 3 + 8 + 2 + 9) and one public definition
  (`TurnsActiveRows`). All 23 depend on `propext`, `Classical.choice`, `Quot.sound` only (by
  compiling `Sig.lean` and `UBHchk.lean` against the build of `/home/claude/lp/lean`, whose
  `SkipsLean/` was the same as that of `/home/claude/lw` each time, by `diff -rq`; the last time at
  `72700dd`).

Papers, as text: the skips paper ("S", `<scratchpad>/skips.txt`). The five files do not cite the
dimension paper, and I compared nothing with it. Line numbers of `STATEMENTS.md` are those of
`1c859c6`, where I read the rows: the rows of the five files are lines 876, 882, 883, 884 and 891
there. They have the same text (by checksum) at `f223d48` (lines 874, 880, 881, 882, 886) and at
`72700dd` (lines 883, 889, 890, 891, 898).

**Short answer. No Lean statement is false, none is vacuous, none has drifted.** The 23
statements are the paper's, with the conditions of the proofs written out, and with one condition
that the paper's proof needs and does not write: `TurnsActiveRows`. **This condition is needed.
I found a parameter of one residual ReLU block (`d = 2`, six hidden units) that has every
condition the paper's proof names (`E`, `D` invertible, the hypotheses of Lemma B.3) and at which
the functional dimension is 23, one less than `P − d(d−1)/2 − 1 − s = 24`.** (The rank is 23 at
252 inputs in exact arithmetic; a flat direction that is not a symmetry is in the kernel exactly
at these inputs, and by hand at every input of the paper, so no batch has a larger rank.) So the
sentence of the paper's proof ("a flat direction is the sum of a direction of the rotation
and scaling of all hidden states and a direction `ψ` … along which `B` has derivative zero on
the sphere") is not true at every parameter with those conditions; the theorem, which is for
generic parameters, stands, and Lean proves that the missing condition holds at almost every
parameter. In 32 computed cases inside the hypotheses of the theorem (ReLU and ReLU², `d = 2, 3`,
widths 1 to `2d + 1`) the rank was the value on both batches. In 124 computed parameters of
skipless networks no rank was above the Lean bound. One sentence of the index says more than I
could confirm ("the paper's sentence needs … `d_in ≥ d` and width at least `d`"); corrections are
at the end.

How I checked.

- "By reading": every public statement and docstring of the five files and their headers; the
  definitions (`Arch`, `Params`, `hidden`, `eval`, `evalBatch`, `jacobianRank`, `funDim`, `flat`,
  `flatOn`, `funDimOn`, `rmsRow`, `rmsNorm`, `Arch.mlp`, `Arch.gated`, `relu`, `reluSq`, `cobDir`,
  `scaleDir`, `rescaleDirMlp`, `vanillaBlock`, `noKinkRMS`, `OneBlockGenericRMS`, `UnitsRescale`,
  `residualZeroDomain`, `RowHomogeneous`, `Params.cob`, `Params.cobAt`, `cobSkip`); the statements
  of the twins (`exists_antisymm_scale_of_flatOn_residual_rmsNorm_zero`,
  `exists_antisymm_of_flatOn_residual_rmsNorm`, `eval_cob_residual_rmsNorm_iff`,
  `eval_cobAt_rmsNorm_zero_of_rowHomogeneous`); the proofs of the eight `ae_` statements of the
  Generic file (two to four lines each); and the paper: the Scope (S lines 252 to 257), Definition
  4.3, Proposition A.1, Lemma A.2, Lemma A.3, Theorem A.5 with the proof of part (iii), Theorem
  A.12 (iii) with its proof, Theorem A.17 with the remark after it and its proof, Lemma A.18,
  Theorem B.1 with "Notation and flat directions", Lemma B.2, Lemma B.3, Step 3 of part (i),
  part (ii), part (iii) with "The case `ε = 0`", part (iv), part (v).
- "By hand": a short argument of my own, written where it is used.
- "By compiling": scratch files in `/home/claude/audit21a/`, compiled with `lake env lean <file>`
  from `/home/claude/lp/lean` (nothing written there): `Sig.lean` (signatures with every instance
  argument, and axioms, of the 14 theorems of the first four files), `UBHchk.lean` (axioms of the
  nine theorems of the fifth file and checks 1 and 8), `Chk.lean` (checks 1, 2, 3, 5 and 7),
  `Chk2.lean` (check 5). All compile without error and without `sorry` (`*.out`, the last time at
  `72700dd`); every theorem of mine that I name below has the three standard axioms.
- "By a computation": my own scripts. `z21core.py`: networks of ReLU, ReLU² and ReGLU blocks
  under pre-RMSNorm with `ε = 0`, any depth, with or without skips; the derivative in the weights
  is exact (forward mode), over mpmath numbers with 60 digits or over Python fractions; checked
  against central differences (`z21fd.py`: they agree to `1.4·10⁻³⁶`, the error of the
  differences). The rank at 60 digits is by elimination with complete pivoting, and again from the
  singular values in double precision; over all runs the smallest pivot kept is `4.3·10⁻¹⁸` of the
  largest and no entry dropped is above `4.5·10⁻⁵⁷`. In exact arithmetic the rank is over the
  rationals (fraction-free elimination), and again modulo two primes. One token per input: these
  blocks act on every token alone, so the Jacobian at an input of `T` tokens is the stack of the
  Jacobians at its rows. Inputs of a batch: one third with a random direction of `h_0 = x E`, one
  third close to the kink of a random unit of the first block (relative distance `10⁻⁴` to 1,
  either side), one third on both sides of a kink of any block, found by bisection between two
  random inputs; random scales from 0.2 to 5. **A rank on a batch is a lower bound of the
  functional dimension.** I ran the coordinator's script once (16 cases, none differs); my numbers
  are from my own scripts.

---------------------------------------------------------------------------------------------------

## Part 1: the drift checks

### Check 1. Generic means almost every parameter, for every Haar measure

**Verdict: yes, in all 14 `ae_` statements (eight in `ResidualRMSZeroRescaleGeneric.lean`, six in
`UpperBoundHomogeneousRMSNormZero.lean`); every index type of the weights is finite; the
statements apply to a concrete Haar measure.** (By reading; the shapes from the compiled
signatures; 15 instances by compiling, `Chk.lean` and `UBHchk.lean`.)

- The `variable` lines:

  ```
  -- OneBlock/ResidualRMSZeroRescaleGeneric.lean
  variable {T d dIn dOut : Type*} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn]
    [Fintype dOut]
  variable {hid : Fin 1 → Type} [∀ ℓ, Fintype (hid ℓ)]
  -- Dimension/UpperBoundHomogeneousRMSNormZero.lean
  variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
    [Fintype dOut]
  variable {σ : ℝ → ℝ} {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]
  ```
  The weights are `E : Matrix dIn d ℝ`, `read ℓ : Matrix d (r ℓ) ℝ`, `write ℓ : Matrix (w ℓ) d ℝ`,
  `D : Matrix d dOut ℝ`, with `r ℓ = w ℓ = hid ℓ` (MLP) and `r ℓ = hid ℓ ⊕ hid ℓ` (gated). Each of
  these index types has `Fintype`.
- Each of the 14 statements has `μ` as a variable with `[μ.IsAddHaarMeasure]` and `∀ᵐ θ ∂μ`. None
  is "there is a parameter" or "on an open set". For instance:

  ```
  theorem ae_funDim_relu_oneBlock_residual_rmsNorm_zero [Nonempty (hid 0)]
      (μ : Measure (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut))
      [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
      (hdOut : Fintype.card d ≤ Fintype.card dOut) :
      ∀ᵐ θ ∂μ, funDim (Arch.mlp relu (rmsNorm 0) hid) 1 θ
          + ((Fintype.card d * (Fintype.card d - 1) / 2 + 1) + Fintype.card (hid 0))
        = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut)
  ```
  The four statements on the conditions (`ae_turnsActiveRows_…`, `ae_exists_turned_row_…`) have
  `omit [Fintype T] [Nonempty T]`: they do not use the tokens.
- By compiling, at the concrete measure `Measure.addHaar` on the space of the weights (which is
  finite-dimensional with its Borel σ-algebra; any two Haar measures on it have the same sets of
  measure zero, `null_iff_of_haar21`), with the number of parameters computed:

  | my theorem | statement used | the network | `P` | conclusion at almost every `θ` |
  |---|---|---|---|---|
  | `turns_relu_concrete21` | `ae_turnsActiveRows_relu` | `d = 2`, width 1 | | `TurnsActiveRows θ` |
  | `turns_reluSq_concrete21` | `ae_turnsActiveRows_reluSq` | `d = 2`, width 5 | | `TurnsActiveRows θ` |
  | `turned_relu_concrete21` | `ae_exists_turned_row_relu` | `d = 3`, width 2 | | a turned row off the kinks |
  | `turned_reluSq_concrete21` | `ae_exists_turned_row_reluSq` | `d = 2`, width 1 | | a turned row off the kinks |
  | `funDim_relu_concrete21` | `ae_funDim_relu_oneBlock_residual_rmsNorm_zero` | one token, `d = d_in = d_out = 2`, width 1 | 12 | `funDim = 9` |
  | `batch_relu_concrete21` | `ae_exists_jacobianRank_relu_oneBlock_residual_rmsNorm_zero` | two tokens, `d = d_out = 3`, `d_in = 4`, width 2 | 33 | a batch of the paper's inputs of rank 27 |
  | `funDim_reluSq_concrete21` | `ae_funDim_reluSq_oneBlock_residual_rmsNorm_zero` | `d = d_in = d_out = 2`, width 5 | 28 | `funDim = 21` |
  | `batch_reluSq_concrete21` | `ae_exists_jacobianRank_reluSq_oneBlock_residual_rmsNorm_zero` | three tokens, `d = 2`, `d_in = 3`, `d_out = 4`, width 1 | 18 | a batch of the paper's inputs of rank 15 |
  | `le_relu_concrete21` | `ae_funDim_add_le_skipless_relu_rmsNorm_zero` | two ReLU blocks of width 2, `d = 2` | 24 | `funDim ≤ 10` |
  | `le_reluSq_concrete21` | `ae_funDim_add_le_skipless_reluSq_rmsNorm_zero` | three ReLU² blocks of widths 3, 4, 5, `d = d_in = 3`, `d_out = 1` | 84 | `funDim ≤ 41` |
  | `le_reglu_concrete21` | `ae_funDim_add_le_skipless_reglu_rmsNorm_zero` | two ReGLU blocks of width 2, `d = 2` | 32 | `funDim ≤ 14` |
  | `le_relu_L0_concrete21` | `ae_funDim_add_le_skipless_relu_rmsNorm_zero` | no block (`L = 0`), `d = 2` | 8 | `funDim ≤ 6` |
  | `lt_relu_concrete21` | `ae_funDim_add_lt_skipless_relu_rmsNorm_zero` | as `le_relu_concrete21` | 24 | `funDim < 14` |
  | `lt_reluSq_concrete21` | `ae_funDim_add_lt_skipless_reluSq_rmsNorm_zero` | as `le_reluSq_concrete21` | 84 | `funDim < 56` |
  | `lt_reglu_concrete21` | `ae_funDim_add_lt_skipless_reglu_rmsNorm_zero` | as `le_reglu_concrete21` | 32 | `funDim < 18` |

### Check 2. The condition `TurnsActiveRows`

```
def TurnsActiveRows (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) : Prop :=
  ∀ v : d → ℝ, (∀ i, (v ᵥ* θ.read 0) i ≠ 0) → (∃ i, σ ((v ᵥ* θ.read 0) i) ≠ 0) →
    v ∈ closure {u : d → ℝ |
      LinearIndependent ℝ ![u, vanillaBlock σ (θ.read 0) (θ.write 0) u]}
```
with `vanillaBlock σ R W u = σ(u R) W`, the block `B` at the row `u`.

**(a) Is the reading of the paper's proof right? Yes.** (By reading and by hand.) The case
`ε = 0` of part (iii) (S lines 2862 to 2889) has: "`D_θ h_1 η = h_1 Y + μ h_1` with a number `μ`
at each input"; then, at the inputs `t w`, "The terms of order `t` give `w Λ = μ_w w E A` …
`η_E A + E η_A = E A (Y + c I)`. **The constant terms then give `μ = c` wherever `w E A` and
`g(w)` are linearly independent.**" This is the one place where the independence is used. By
hand, with `A = I`: at the input `t w` the equation is
`t (c − μ) w E + [γ(w) − g(w) Y − μ g(w)] = 0`, with `γ(w)` the derivative of the block along
`η` and `μ = μ(t w)`. If `w E` and `g(w)` are independent, comparing the parts along `w E`, along
`g(w)` and outside their span for all `t > 0` gives `μ = c` and `γ(w) = g(w)(Y + c I)`: the block
has derivative zero along `ψ` at this row. If `g(w)` is a multiple of `w E`, the equation gives
only that `γ(w) − g(w) Y` is a multiple of `w E`, and `μ` need not be `c`. The next sentences of
the paper use `μ = c` at every input: "Steps 3 and 4 run with `Y + c I` in place of `Y`", "(17)
holds … on the sphere", "Its flat directions are the rotation and the scaling of all hidden
states, and the space `K_B` of directions of the block along which `B` has derivative zero on the
sphere", and in part (iv) "a direction `ψ` of the weights of the block along which `B` has
derivative zero on the sphere of radius `√d_model`. This derivative is positively homogeneous of
degree `k` in `n`, so it vanishes for all `n ≠ 0`". For an analytic block the step from an open
set of rows to the sphere is analytic continuation. For a ReLU-type block it is not: on each
region (a set of rows with the same active units) the block is another polynomial map, and the
zero derivative on one region says nothing on another. The quotes in the headers of the files are
the paper's words (compared with S lines 2338 to 2340, 2862 to 2878 and 2898 to 2904).

**(b) Is `TurnsActiveRows` what that step needs? It is what the step uses, and it is sufficient;
it is not necessary for the conclusion at every parameter.** (By reading and by hand; the last
point by a computation.) The first statement (`OneBlock/ResidualRMSZeroStepsOn.lean`) gives the
zero derivative at the rows `N_0(x E)` off the kinks at which `x E` and `g(x)` are independent;
by homogeneity the independence of `(u, B(u))` does not depend on the length of `u`. The
derivative along `ψ` is continuous off the kinks. So it vanishes at every row off the kinks that
is a limit of rows that the block turns: this is the set that `TurnsActiveRows` asks to be
everything off the kinks with an active unit. The two exceptions in the definition are right:
- a row at which no unit is active (`σ` of every pre-activation is `0`): there the block is `0`
  on a neighbourhood, no nearby row is turned, and the derivative along every `ψ` is `0` anyway
  (a positively homogeneous `σ` that vanishes at one `z ≠ 0` vanishes on that side of `0`, with
  its derivative). Without this exception the condition would fail at every ReLU block with such
  a row.
- a row with a pre-activation at `0`: not asked (`∀ i, (v ᵥ* θ.read 0) i ≠ 0`); the paper's
  inputs have none. The closure is taken in all rows; as the rows off the kinks are an open set,
  this is the same as the closure within them.
Not necessary: at the parameter (A) below the condition fails and the conclusion holds.

**(c) Is the pointwise theorem non-vacuous? Yes.** (By compiling, `Chk.lean`.)
`ae_hypotheses_relu21` and `ae_hypotheses_reluSq21`: for `d_in, d_out ≥ d ≥ 2` and a block with a
hidden unit, the hypotheses on `σ` hold (`hasDerivAt_relu`, `relu_homogeneous`,
`relu_unitsRescale`, and the same for ReLU²), and at almost every `θ`, for every Haar measure,
`OneBlockGenericRMS θ ∧ TurnsActiveRows θ ∧ ∃ v, (∀ i, (v ᵥ* θ.read 0) i ≠ 0) ∧
LinearIndependent ℝ ![v, vanillaBlock relu (θ.read 0) (θ.write 0) v]`, from
`ae_oneBlockGenericRMS`, `ae_turnsActiveRows_relu`, `ae_exists_turned_row_relu`. And some
parameter has them (`exists_hypotheses_relu21`, `d = 2`, width 1).

**(d) Is the condition needed? Yes: without `hturn` the three pointwise statements would be false.
The conclusion can also hold where the condition fails.** (By a computation in exact arithmetic,
`z21turn.py`, output `z21turn.out`; a second computation at 60 digits with random inputs,
`z21turn2.py`; the flatness at every input by hand.) All three parameters have `d = d_in = d_out
= 2`, `E = [[2, 1], [1, 3]]`, `D = [[1, −2], [3, 1]]` (both invertible), a ReLU block, one token.
Write `c_i` for the columns of `W_read` and `a_i` for the rows of `W_write`. For `d = 2` the
regions are the sectors between the lines `u c_i = 0`; on the sector with the active set `S` the
block is `u ↦ u M_S` with `M_S = ∑_{i ∈ S} c_i a_i`, and it turns some row of the sector unless
`M_S` is a multiple of `I`.

- **(B), the condition fails and the value fails.** Six units,
  `c = (1,6), (−1,6), (6,−5), (7,4), (−7,4), (−3,−2)` and
  `a = (6,−1), (6,1), (232/59, −45/59), (−241/59, 47/59), (−61/13, −17/26), (112/13, 31/26)`.
  - Each clause of the hypotheses: `E` and `D` have rank 2; every `a_i ≠ 0`; every `c_i ≠ 0`; the
    `c_i` are pairwise non-collinear (all 15 determinants are nonzero): this is
    `OneBlockGenericRMS θ`. `d = 2 ≥ 2`. The hypotheses on `σ` are those of ReLU. `hw` holds: ten
    of the twelve sectors have an `M_S` that is not a multiple of `I`, so they contain turned rows
    off the kinks.
  - `TurnsActiveRows θ` fails: on the sector with the active units 1, 3, 4 (it contains
    `u = (1, 0)`) `M_S = I`, so `B(u) = u` on an open set of rows, and no row near `(1, 0)` is
    turned. On the opposite sector (active units 2, 5, 6) also `M_S = I`.
  - The direction `ψ`: column 1 of `W_read` moves by `(1/6, 0)`, row 1 of `W_write` by
    `(0, 1/6)`, column 2 of `W_read` by `(−1/6, 0)`, row 2 of `W_write` by `(0, −1/6)`, nothing
    else moves. Then `ψ_{c_1} a_1 + c_1 ψ_{a_1} = I` and `ψ_{c_2} a_2 + c_2 ψ_{a_2} = −I` (exact).
    On a sector the derivative of the block along `ψ` is `u Ψ_S` with
    `Ψ_S = ∑_{i ∈ S} (ψ_{c_i} a_i + c_i ψ_{a_i})`. Units 1 and 2 are both active on five sectors
    and both inactive on five (`Ψ_S = 0`); only unit 1 is active on the sector `{1, 3, 4}`
    (`Ψ_S = I`) and only unit 2 on `{2, 5, 6}` (`Ψ_S = −I`). On these two sectors
    `h_1 = x E + B(n) = (t + 1) n` is a multiple of `n`, and the derivative of `h_1` along `ψ` is
    `± n`, a multiple of `h_1`, which the last normalization removes. So `ψ` is flat at every
    input at which no normalized row vanishes and no unit is at its kink (by hand). It is not a
    sum of the rotation, the scaling and the six rescalings (exact: the nine vectors have rank 9).
  - Exact computation: at 252 rational inputs (7 directions in each of the 12 sectors, 3 scales;
    the directions are rational points of the circle `|n|² = 2`, so that every square root is
    rational) the Jacobian has rank **23** over the rationals (and modulo two primes), `P = 32`,
    and `P − (d(d−1)/2 + 1) − s = 32 − 2 − 6 = 24`. The nine vectors (rotation, scaling, six
    rescalings, `ψ`) are in the kernel exactly and are independent, so the rank of every batch of
    the paper's inputs is at most 23. At 60 digits, 320 and 640 inputs spread at random: rank 23.
  - What this refutes: not a Lean statement (each has `hturn`). At this `θ`, without `hturn`,
    `flatOn_noKink_le_mlp_rescale_residual_rmsNorm_zero` would be false (`ψ` is flat on
    `residualZeroDomain ∩ noKinkRMS θ` and not of the form), and so would
    `exists_jacobianRank_mlp_oneBlock_rescale_residual_rmsNorm_zero` (no batch of these inputs has
    rank 24). For `funDim` (all inputs): at an input with a unit at its kink where Lean's output
    is still differentiable in the weights, the derivative along `ψ` is again a multiple of `h_1`
    (by hand: the term of the unit at its kink is a multiple of its row `a_i`, and differentiability
    there needs `a_i` parallel to `h_1`), so I expect `funDim = 23` at this `θ`; I did not
    compute at such inputs.
- **(A), the condition fails and the value holds.** Two units, `c_1 = a_1 = e_1`,
  `c_2 = a_2 = e_2`: where both are active the block is the identity, so `TurnsActiveRows` fails;
  `OneBlockGenericRMS` and `hw` hold. The block directions that are flat are the two rescalings
  only (each unit is active alone on a sector), and the rank at 84 rational inputs is 12 =
  `16 − 2 − 2`, exactly. So `TurnsActiveRows` is not necessary.
- (C), the same `c_i` as (B) with other rows `a_i`: every sector is turned, the rank is 24.
- (D), ReLU² (`z21turn2.py`): `c = e_1, e_2, e_1 + e_2`, `a = (1,−1)/2, (−1,1)/2, (1,1)/2`; where
  the three units are active `B(u) = (u_1 + u_2) u`, so the condition fails; the rank at 200 and
  400 inputs is 15, the value. As (A).

### Check 3. Which functional dimension

**Verdict: the pair is the paper's functional dimension. `funDim = v` (all inputs) together with
"a batch of inputs of `residualZeroDomain ∩ noKinkRMS θ` of rank `v`" gives: the largest rank over
the batches of the paper's inputs is `v`. And `residualZeroDomain ∩ noKinkRMS θ` is the paper's
set of inputs for `ε = 0`.** (By reading; by compiling, `Chk.lean`.)

- The paper (S lines 2365 to 2371): "For the ReLU-type activations, `F(θ, x)` is differentiable in
  `θ` at the inputs `x` at which no hidden unit sits at its kink, …, and "every input" means every
  such input. With `ε = 0`, it also excludes the inputs at which a state that is normalized
  vanishes."
- The Lean text:

  ```
  def residualZeroDomain (A : Arch T d 1) (θ : Params A dIn dOut) : Set (Matrix T dIn ℝ) :=
    {x | (∀ t, (x * θ.E) t ≠ 0) ∧
      ∀ t, (x * θ.E + A.f 0 (rmsNorm 0 (x * θ.E) * θ.read 0) * θ.write 0) t ≠ 0}
  def noKinkRMS (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut) :
      Set (Matrix T dIn ℝ) :=
    {x | ∀ (t : T) (i : hid 0), (x * θ.E * θ.read 0) t i ≠ 0}
  ```
  `noKinkRMS` is written with `x E W_read`, not with the pre-activations `N_ε(x E) W_read`. For
  `ε = 0` and a row of `x E` that is not zero the two differ by a positive factor. By compiling
  (`mem_paper_inputs_iff21`): `x ∈ residualZeroDomain … θ ∩ noKinkRMS θ` if and only if no row of
  `x E` is zero, no row of `h_1` is zero, and no entry of `rmsNorm 0 (x * θ.E) * θ.read 0` is
  zero. These are the paper's inputs.
- By compiling (`funDimOn_eq_of_pair21`, for any network and any set `U` of inputs): if
  `funDim A S θ = v` and some batch of inputs of `U` has rank `v`, then `funDimOn A S θ U = v`
  (`funDimOn` is the largest rank over the batches of inputs of `U`). And
  `ae_funDimOn_relu21`: for a ReLU block with a hidden unit and `d_in, d_out ≥ d ≥ 2`, at almost
  every `θ`, `funDimOn … 1 θ (residualZeroDomain … θ ∩ noKinkRMS θ) + ((d(d−1)/2 + 1) + s) = P`,
  from the two library statements. The library does not state this form; the pair says the same.
- Why both halves are needed: `funDim` alone could be larger than the paper's value (it also uses
  inputs outside the paper's set at which Lean's output happens to be differentiable); the batch
  alone gives "at least".

### Check 4. No extra hypotheses against Theorem B.1 (iv) and its Scope

**Verdict: none. Every hypothesis of the four statements is the theorem's or follows from it.
Lean asks less in one place (a hidden unit in place of "width at least `d_model`"), and the
statements are true there (they are proved; the computed ranks agree).** (By reading and from the
compiled signatures, `Sig.out`; by a computation, `z21res.py`.)

The theorem (S lines 2319 to 2322 and 2338 to 2340): `d_model ≥ 2`; input and output dimensions at
least `d_model`; inputs range over all of `ℝ^{T × d_in}`; one block; pre-RMSNorm with `ε = 0`,
without biases; a ReLU, ReLU² or ReGLU block of width at least `d_model`; generic parameters.

| hypothesis of the four statements | in the theorem? |
|---|---|
| `[Fintype T]`, `[Fintype d]`, `[DecidableEq d]`, `[Fintype dIn]`, `[Fintype dOut]`, `[∀ ℓ, Fintype (hid ℓ)]` | yes: finite sizes |
| `[Nonempty T]` (at least one token) | yes (with no token the functional dimension is 0) |
| `[Nonempty (hid 0)]` (at least one hidden unit) | follows from "width at least `d_model`" and `d_model ≥ 2` |
| `μ` with `[μ.IsAddHaarMeasure]` | "for generic parameters" |
| `hd : 2 ≤ card d` | `d_model ≥ 2` |
| `hdIn : card d ≤ card dIn` | "the input … dimensions be at least `d_model`" |
| `hdOut : card d ≤ card dOut` | "the … output dimensions be at least `d_model`" |
| one block (`hid : Fin 1 → Type`), stream `1`, `χ = rmsNorm 0`, no biases | yes |
| ReLU, ReLU² by name | two of the theorem's three kinds; ReGLU is not in these files |

There is no hypothesis on the width beyond one hidden unit.

The computation (`z21res.py`, outputs `z21res_relu.out`, `z21res_relusq.out`; summary
`z21_summary.out`): one residual block, weights uniform in `[−1, 1]`, two batches of `4P` and `7P`
inputs (48 to 420 inputs), 60 digits.

- **Inside the hypotheses** (`d = 2` with widths 1 to 5 and `d = 3` with widths 1 to 7 at
  `d_in = d_out = d`; and `(d, d_in, d_out, width) = (2, 3, 2, 1), (2, 4, 3, 3), (3, 4, 3, 1),
  (3, 5, 4, 4)`; ReLU and ReLU²): 32 cases, `P` from 12 to 60. **Both ranks are equal to
  `P − (d(d−1)/2 + 1) − s` in all 32**, also in the 10 cases with a width below `d`. For `d_in = d_out = d`:

  | block | `d = 2`, widths 1 to 5: value = rank | `d = 3`, widths 1 to 7: value = rank |
  |---|---|---|
  | ReLU | 9, 12, 15, 18, 21 (`P` = 12, 16, 20, 24, 28) | 19, 24, 29, 34, 39, 44, 49 (`P` = 24, 30, …, 60) |
  | ReLU² | 9, 12, 15, 18, 21 | 19, 24, 29, 34, 39, 44, 49 |
- **Narrower than `d`: true** (width 1 at `d = 2`; widths 1 and 2 at `d = 3`; 10 cases): the rank
  is the value. The theorem asks the width for both networks; the residual value does not need it.
- **Outside the hypotheses** (for information): `d_in = d − 1` (4 cases): the rank is 2 and 3
  below the formula (8 against 10; 23 against 26), so `d_in ≥ d` is needed for the value.
  `d_out = d − 1` (4 cases): the rank is equal to the formula (10 and 26). So in these cases the
  value holds without `d_out ≥ d`; Lean asks it, as the theorem does, and the proof uses `D` of
  rank `d`.
- `d ≥ 2` is needed: for `d = 1`, `N_0` of a number is its sign, the output is `± D`, and the rank
  is at most `d_out` (by hand).

### Check 5. `flatOn_noKink_le_mlp_rescale_residual_rmsNorm_zero`

```
theorem flatOn_noKink_le_mlp_rescale_residual_rmsNorm_zero {k : ℕ}
    (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (hhom : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (hU : UnitsRescale σ σ' k d d (hid 0))
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
    (hθ : OneBlockGenericRMS θ) (hd : 2 ≤ Fintype.card d) (hturn : TurnsActiveRows θ)
    (hw : ∃ v : d → ℝ, (∀ i, (v ᵥ* θ.read 0) i ≠ 0) ∧
      LinearIndependent ℝ ![v, vanillaBlock σ (θ.read 0) (θ.write 0) v])
    (η : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
    (hη : η ∈ flatOn (Arch.mlp σ (rmsNorm 0) hid) 1 θ
      (residualZeroDomain (Arch.mlp σ (rmsNorm 0) hid) θ ∩ noKinkRMS θ)) :
    ∃ (Y : Matrix d d ℝ) (c : ℝ) (α : ∀ ℓ, hid ℓ → ℝ), Yᵀ = -Y ∧
      η = cobDir θ (fun _ => Y) + scaleDir θ (fun _ => c) + rescaleDirMlp k θ α
```

**Verdict: the conclusion is the paper's "sum of a direction of the rotation and scaling of all
hidden states and … a rescaling of the units", with the right signs. `hw` is not a further
condition for a block with a hidden unit: it follows from `TurnsActiveRows`, "no read column is
zero" (a field of `OneBlockGenericRMS`) and "`σ` is not zero off `0`".** (By reading; by compiling,
`Chk.lean` and `Chk2.lean`.)

- The entries, by compiling (`direction_entries21`): the direction of the conclusion has
  `E (Y + c I)` at `E`; `−(Y W_read)_{a i} + α_i (W_read)_{a i}` at `W_read`;
  `(W_write (Y + c I))_{i a} − k α_i (W_write)_{i a}` at `W_write`; `−Y D` at `D`.
- Against the symmetries (by hand). The rotation and the scaling of both hidden states is
  `θ.cob G Q` with `G = e^{τ(Y + c I)}`, `Q = e^{τ Y}` at `h_0` and at `h_1`: `E ↦ E G`,
  `W_read ↦ Q⁻¹ W_read`, `W_write ↦ W_write G`, `D ↦ Q⁻¹ D` (Theorem A.5 (iii) for `ε = 0`: the
  reads and the readout take `Q^⊤`, not `G⁻¹`). Its derivative at `τ = 0` is `E (Y + c I)`,
  `−Y W_read`, `W_write (Y + c I)`, `−Y D`: the same. The rescaling `(c_i, a_i) ↦ (λ c_i,
  a_i / λ^k)` with `λ = e^{τ α_i}` has the derivative `α_i c_i`, `−k α_i a_i`: the same, and the
  paper's "it scales column `i` of `W_read` … by `λ_i` and row `i` of `W_write` by `−λ_i` for
  ReLU, by `−2λ_i` for ReLU²". One `Y` and one `c` for both hidden states (`fun _ => Y`,
  `fun _ => c`): "of all hidden states".
- The statement is one inclusion (a flat direction has this form). The other (these directions
  are flat, and independent) is `funDim_add_le_residual_mlp_rescale_rmsNorm_zero`, read by the
  twentieth reader.
- `hw`, by compiling (`hw_of_turnsActiveRows21`): for an MLP block with a hidden unit, if no
  column of `W_read` is zero, `σ z ≠ 0` for some `z ≠ 0`, and `TurnsActiveRows θ`, then some row
  off the kinks is turned. (A row off the kinks exists; a multiple of it has an active unit;
  turned rows are dense near it.) Without a hidden unit `hw` is false, the block being `0`
  (`not_hw_of_isEmpty21`). So in the pointwise theorem `hw` says: the block has a hidden unit and
  `σ` is not zero off `0`; the second follows from `UnitsRescale` when there is a hidden unit (by
  hand: for `σ = 0` every direction is flat). The value `P − (d(d−1)/2 + 1)` for a block with no
  hidden unit is true (by hand: the network is `x ↦ N_0(x E) D`) and is not stated.

### Check 6. `OneBlock/ResidualRMSZeroStepsOn.lean`

```
theorem exists_antisymm_scale_of_flatOn_residual_rmsNorm_zero_on {A : Arch T d 1}
    (hA : A.χ = rmsNorm 0) (hd : 2 ≤ Fintype.card d)
    (V : Set (Matrix T (A.r 0) ℝ)) (hV : IsOpen V)
    (hVs : ∀ M ∈ V, ∀ c : T → ℝ, (∀ t, 0 < c t) → (Matrix.of fun t i => c t * M t i) ∈ V)
    (hf : ContDiffOn ℝ 1 (A.f 0) V) (θ : Params A dIn dOut)
    (hE : θ.E.rank = Fintype.card d) (hD : θ.D.rank = Fintype.card d)
    (hw : ∃ w : Matrix T dIn ℝ, w * θ.E * θ.read 0 ∈ V ∧ ∀ t, LinearIndependent ℝ
      ![(w * θ.E) t, (A.f 0 (rmsNorm 0 (w * θ.E) * θ.read 0) * θ.write 0) t])
    (η : Params A dIn dOut)
    (hη : η ∈ flatOn A 1 θ (residualZeroDomain A θ ∩ {x | x * θ.E * θ.read 0 ∈ V})) :
    ∃ (Y : Matrix d d ℝ) (c : ℝ), Yᵀ = -Y ∧ η.E = θ.E * (Y + c • 1) ∧ η.D = -(Y * θ.D) ∧
      ∀ x : Matrix T dIn ℝ, x * θ.E * θ.read 0 ∈ V →
        (∀ t, LinearIndependent ℝ
          ![(x * θ.E) t, (A.f 0 (rmsNorm 0 (x * θ.E) * θ.read 0) * θ.write 0) t]) →
        fderiv ℝ (A.f 0) (rmsNorm 0 (x * θ.E) * θ.read 0)
            (rmsNorm 0 (x * θ.E) * (η.read 0 + Y * θ.read 0)) * θ.write 0
          + A.f 0 (rmsNorm 0 (x * θ.E) * θ.read 0) * (η.write 0 - θ.write 0 * (Y + c • 1))
            = 0
```

**Verdict: it is the paper's step, with the conclusion on the block exactly where the paper's
argument gives it. Against the analytic twin one thing is lost, as the header says: the
conclusion at every row of the sphere.** (By reading and by hand.)

- `Y` antisymmetric with `η_D = −Y D`: Step 1. `η_E = E (Y + c I)`: "For the residual network the
  same steps give `η_E = E (Y + c I)`". The last clause: with `ψ_read = η_read + Y W_read` and
  `ψ_write = η_write − W_write (Y + c I)` (the entries of `η` minus those of the rotation and the
  scaling, check 5), the derivative of `n ↦ f(n W_read) W_write` along `ψ` at `n = N_0(x E)` is
  the left side: it is `D_θ g η − g(x)(Y + c I)`, because `D N_0(x E)(x E (Y + c I)) = N_0(x E) Y`
  (by hand). It vanishes where the rows of `x E` and `g(x)` are independent: "`μ = c` wherever
  `w E A` and `g(w)` are linearly independent".
- `V` open and invariant under positive scalings of the rows, `f` of class `C¹` on `V`: the
  pre-activations `N_0(x E) W_read` are a positive scaling, row by row, of `x E W_read`, and the
  inputs `t w` of the proof stay in the set. For a ReLU-type block `V` is "no entry is zero".
- `hw`: one input `w` with `w E W_read ∈ V` and independent rows for every token; the proof needs
  an open set of such `w` ("for all `w` in an open set"), which one such `w` gives.
- Against the twin `exists_antisymm_scale_of_flatOn_residual_rmsNorm_zero` (`f` analytic
  everywhere, read by the nineteenth reader): the same hypotheses with `V` the whole space; the
  twin concludes at every `n` with rows on the sphere, this statement at `n = N_0(x E)` for the
  inputs `x` with independent rows. Nothing else differs.
- One loss of form: the conclusion is for inputs whose rows are independent **for every token**.
  For a block that acts on every token alone nothing is lost (a row can be repeated at all
  tokens); for a general map `f` a statement token by token would say more.

### Check 7. `Residual/OneChangeOfBasisRMSZero.lean`

```
theorem eval_cob_residual_rmsNorm_zero_iff [Nonempty T] [Nonempty dIn] [Nonempty dOut]
    (hA : A.χ = rmsNorm 0) (hd : 2 ≤ Fintype.card d)
    (hne : ∀ ℓ, ∃ (x : Matrix T dIn ℝ) (E : Matrix dIn d ℝ) (W : Matrix d (A.r ℓ) ℝ) (t : T),
      (x * E) t ≠ 0 ∧ A.f ℓ (rmsNorm 0 (x * E) * W) t ≠ 0)
    (G Q : Fin (L + 1) → GL d ℝ) (c : Fin (L + 1) → ℝ) (hc : ∀ ℓ, 0 < c ℓ)
    (hQ : ∀ ℓ, (Q ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ)
    (hG : ∀ ℓ, (G ℓ : Matrix d d ℝ) = c ℓ • (Q ℓ : Matrix d d ℝ)) :
    (∀ (θ : Params A dIn dOut) (x : Matrix T dIn ℝ), eval A 1 (θ.cob G Q) x = eval A 1 θ x)
      ↔ ∀ ℓ, G ℓ = G 0
```

**Verdict: it is S Theorem A.5 (iii) for `ε = 0`, for arbitrary maps `f_ℓ`; the action is the
paper's; `hne` is the paper's "every block be nonzero for some value of its parameters" in the
form that the proof uses, and it is needed; `d ≥ 2` is the paper's hypothesis. One point of
form: the functions are compared at every input with Lean's `N_0(0) = 0`.** (By reading; by
compiling, `Chk.lean`; `d = 1` by hand.)

- The action. `Params.cob θ G K` has `E G_0` at `E`, `K_ℓ⁻¹ W_read` at the read of the block that
  reads `h_ℓ`, `W_write G_{ℓ+1}` at the write of the block that writes `h_{ℓ+1}`, `K_L⁻¹ D` at
  `D`. With `K = Q` orthogonal, `Q⁻¹ = Q^⊤`: the paper's "`T_G` multiplies the reads and the
  readout by `Q_{ℓ−1}^⊤` and `Q_L^⊤` in place of `G_{ℓ−1}^{−1}` and `G_L^{−1}`", with the
  embedding and the writes times `G_ℓ`. `G_ℓ = c_ℓ Q_ℓ`, `c_ℓ > 0`, `Q_ℓ` orthogonal: `hG`, `hc`,
  `hQ`. The conclusion `∀ ℓ, G ℓ = G 0` is "`G_0 = G_1 = ⋯ = G_L`" (they are in `CO(d)` by
  hypothesis).
- The two directions. "Only if" (`cob_eq_of_eval_cob_residual_rmsNorm_zero`) is the last clause
  of Theorem A.17 (i), "they preserve that of every residual network only if they agree at all
  hidden states". "If" is the paper's too: Theorem A.5 (iii) is "if and only if", and its proof
  begins "A single global `G` is a symmetry".
- `hne` against the paper. The proof: "Fix a token, and an input and reads at which the row of
  `f(N_ε(h) W_read^ℓ)` of this token is nonzero"; the row `h` of that token is nonzero in the
  paper (its inputs have nonzero hidden states) and the proof divides by nothing else. Lean's
  `hne` asks both. For the paper's kinds of block it follows from "nonzero for some value of its
  parameters" (by hand: for an MLP or gated block take any row `h ≠ 0` and a read that gives the
  pre-activations at which the block is not zero). By compiling, for a ReLU block with a hidden
  unit (`hne_relu21`), and the theorem at two such blocks (`iff_relu_concrete21`), so it is not
  vacuous.
- `hne` is needed, by compiling (`counterexample_without_hne21`): for one block whose map is `0`
  (`d = 2`), `G = (I, 2I)`, `Q = (I, I)`, `c = (1, 2)` preserve the function of every residual
  network, and `G_1 ≠ G_0`.
- `d ≥ 2`. The theorem has "Let `d_model ≥ 2`". For `ε = 0` it is not needed (by hand, `d = 1`,
  one block: the outputs are `sign(c_0 h + c_1 b) q_1 D` and `sign(h + b) D`; `b` takes every
  value, so `q_0 = q_1` and `c_0 = c_1`). The Lean proof uses `d ≥ 2` because it keeps "a multiple
  of `u`" from the paper's "a positive multiple of `u`".
- The point of form. The hypothesis of "only if" is the equality at every `θ` and every input
  `x`, for Lean's total `N_0` (a zero row goes to `0`). The paper's functions are not defined at
  an input with a zero hidden row. So the Lean "only if" assumes the equality at more inputs than
  the paper's sentence does, and the Lean "if" gives it at more inputs. The header says
  "Lean's `rmsNorm 0` maps a zero row to `0`; both directions hold with it". The proof uses the
  equality at inputs whose row at the chosen token is `u ≠ 0` in the network `θ`; I did not check
  whether it can be run with the paper's inputs only (other tokens of the input that `hne` gives
  may have zero rows).

### Check 8. `Dimension/UpperBoundHomogeneousRMSNormZero.lean`

```
theorem funDim_add_le_skipless_mlp_rescale_rmsNorm_zero [Nonempty d] {k : ℕ}
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d) (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d)
    (hc : ∀ ℓ i, (fun a => θ.read ℓ a i) ≠ 0) :
    funDim (Arch.mlp σ (rmsNorm 0) hid) 0 θ
        + (L * Fintype.card d ^ 2 + (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
          + ∑ ℓ, Fintype.card (hid ℓ))
      ≤ Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)

theorem ae_funDim_add_lt_skipless_relu_rmsNorm_zero
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hL : 1 ≤ L)
    (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, funDim (Arch.mlp relu (rmsNorm 0) hid) 0 θ
        + ((L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
          + ∑ ℓ, Fintype.card (hid ℓ))
      < Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut)
```

**Verdict: the count is the paper's ("all of `GL(d_model)` at `h_0, …, h_{L−1}`", `CO(d_model)` at
`h_L`, the rescalings). The strict inequality is "Its functional dimension then lies below the
bound of (ii), so it does not satisfy the equality condition", in a stronger form (at almost
every parameter). `d ≥ 2` is needed. `d_in ≥ d` and the width are the conditions of the paper's
Scope and of Lemma A.18; I found no case in which the conclusion fails without them. At depth 2
and 3 no computed rank is above the bound; the bound is attained at some parameters and not at
others.** (By reading, by hand, by compiling `UBHchk.lean`, by a computation.)

- The count. `L d²`: one `d × d` matrix `X_ℓ` at each of `h_0, …, h_{L−1}`
  (`cobDir θ (Pi.single ℓ.castSucc X)`, `ℓ : Fin L`). `d(d−1)/2 + 1`: an antisymmetric `Y` and a
  number `c` at `h_L`. `s`: the number of hidden units (MLP), twice that (gated). The paper (S
  lines 1570 to 1572): "For `ε = 0` and positively homogeneous blocks, a skipless network has
  more symmetries than the changes of basis in `𝒢`: all of `GL(d_model)` at `h_0, …, h_{L−1}`
  (Lemma A.3)"; at `h_L` Lemma A.3 gives only the scaling, and Proposition A.1 the rotations. The
  paper writes the resulting bound only for one block (Theorem B.1 (iv)); for `L = 1` the Lean
  count is that one (`d² + d(d−1)/2 + 1 + s`).
- The direction, by compiling (`cobDir_single_entries21`, two blocks, the change at `h_1`):
  `cobDir θ (Pi.single (1 : Fin 2).castSucc X)` is `0` at `E`, at the read of block 1, at the
  write of block 2 and at `D`, `W_write X` at the write of block 1 and `−X W_read` at the read of
  block 2: the derivative of the change of basis `I + τ X` at `h_1`.
- The independence under the hypotheses of the pointwise statement (by hand): if a combination
  with the numbers `(X_0, …, X_{L−1}, Y, c, α)` is zero, `E X_0 = 0` gives `X_0 = 0`; then the
  read of block 1 gives `α` there (no read column zero); then `W_write X_1 = 0` gives `X_1 = 0`
  (the write of rank `d`); and so on; at the end `W_write (Y + c I) = 0` gives `Y = 0`, `c = 0`.
  So the hypotheses are those under which the count is right.
- The strict form. `(L + 1)(d(d−1)/2 + 1) + s < L d² + (d(d−1)/2 + 1) + s` if and only if
  `L (d(d−1)/2 + 1) < L d²`, that is `L ≥ 1` and `d ≥ 2` (compiled; for `d = 1` the two sides are
  equal). Definition 4.3: "A network satisfies the equality condition if its bound in Theorem 4.2
  is attained at generic parameters". Lean says: at almost every parameter the functional
  dimension is strictly below that bound; this implies that the bound is not attained at generic
  parameters.
- **`d ≥ 2` is needed** (by hand and by a computation). For `d = d_in = d_out = 1` and one ReLU
  block of width 1, the output is `sign(w) D` where the unit is active, so the rank is 1 at every
  parameter with nonzero weights, and the bound of (ii) is `P − 2 − s = 4 − 2 − 1 = 1`: it is
  attained. Computed (`z21skip_relu_d1.out`, `z21skip_relusq_d1.out`): rank 1 = bound for widths
  `(1)` (ReLU and ReLU²) and `(1, 1)` (ReLU); in the other 9 cases with `d = 1` the rank is below.
- **`d_in ≥ d` and the width.** The paper's Scope (S lines 252 to 255): "Every MLP block has
  `d_hidden ≥ d_model` … The input and the output satisfy `d_in, d_out ≥ d_model ≥ 2`", and
  Lemma A.18 has "the embedding has rank `d_model` and every block has width at least `d_model`"
  for the bound of (ii). Theorem A.12 and the remark after Theorem A.17 do not repeat them. So the
  Lean hypotheses `d ≥ 2`, `d_in ≥ d` and the width are the paper's Scope, and Lean does not ask
  `d_out ≥ d`. Are the last two needed? Computed (22 cases with a block narrower than `d` or
  `d_in < d`, depth 1 and 2, ReLU and ReLU², `z21skip_*_outside.out`): the rank is at most the
  Lean bound in all 22 (equal in 2, both with `d_in = 2 < d = 3` and one block of width 3), and
  below the bound of (ii) by 5 or more in all 22. So these cases do not show that the two
  hypotheses are needed for either conclusion; they are needed for the argument (the independence
  above).
- **Depth 2 and 3** (`z21skip.py`, `z21skip2.py`; weights uniform in `[−1, 1]`; 60 digits). First
  pass, two batches of `6P` and `10P` inputs: 36 cases with `d ≥ 2`, `d_in ≥ d`, widths at least
  `d` (ReLU, ReLU², ReGLU; 6 of depth 1, 24 of depth 2, 6 of depth 3; `P` up to 93). **No rank is
  above the Lean bound; all are below the bound of (ii).** Depth 1: equal to the Lean bound in
  all 6. Depth 2 and 3: equal in 7 of 30 (ReLU² with widths `(4,4)` at `d = 2` and `(3,3)`,
  `(4,4)`, `(3,5)` at `d = 3`; ReGLU with `(4,4)` at `d = 2` and `(3,3)`, `(4,4)` at `d = 3`),
  below in 23 (many inputs have output `0`: units of the
  second block that no input activates). The two batches gave different ranks in 5 of the 30. For
  ReLU at depth 2: `d = 2`, widths `(2,2)`, `(3,3)`, `(2,4)`, `(4,4)`: ranks 4, 15, 12, 23
  against 10, 16, 16, 24; `d = 3`, widths `(3,3)`, `(4,4)`, `(3,5)`: 21, 30, 38 against 26, 36,
  39. Second pass, depth 2, `d = d_in = d_out = 2`, six parameters per shape, one batch of `16P`
  inputs:

  | widths | bound | ReLU: ranks at six parameters | ReLU²: ranks at six parameters |
  |---|---|---|---|
  | `(2, 2)` | 10 | 8, 8, 2, 2, 8, 0 | 0, 10, 0, 10, 2, 2 |
  | `(3, 3)` | 16 | 11, 2, 12, 11, 12, 12 | 16, 13, 16, 13, 14, 2 |
  | `(4, 4)` | 22 | 22, 18, 22, 22, 22, 11 | 22, 22, 22, 22, 10, 22 |
  | `(5, 5)` | 28 | 22, 28, 28, 28, 28, 28 | 28, 25, 28, 28, 28, 25 |

  and `d = 3`, widths `(3, 3)`, bound 26, three parameters: ReLU 25, 17, 25; ReLU² 23, 26, 18.
  So at depth 2: at most the bound in all 54 parameters; equal at 23 of them. The rank changes
  from one parameter to another at the same shape, so for these blocks at depth 2 there is no one
  value at almost every parameter that these batches could show. Lean claims the bound only, and
  the paper claims equality for one block only.

### Check 9. The index rows and the axiom file

**Verdict: every sentence of the five rows is true of the statements, except one that says more
than I could confirm (row 876: "the paper's sentence needs … `d_in ≥ d` and width at least `d`").
Every one of the 23 public theorems is in a row and in `checks/Axioms.lean`; the definition
`TurnsActiveRows` is in its row.** (By reading; the names by a script.)

- Row 882 (`OneBlock/ResidualRMSZeroStepsOn.lean`): each clause is true (check 6). "for every such
  input `x` whose rows of `x E` and `g(x)` are independent for every token": as the statement.
- Row 883 (`OneBlock/ResidualRMSZeroRescale.lean`): each clause is true (checks 2, 3, 5). "a
  condition that the paper does not state: the block turns a dense set of the rows at which some
  hidden unit is active (`TurnsActiveRows`), and some row off the kinks": true; the second
  follows from the first for a block with a hidden unit (check 5), and the row does not say that
  the first is needed (check 2 (d)). "No width is asked": true; a hidden unit is asked, through
  `hw`.
- Row 884 (`OneBlock/ResidualRMSZeroRescaleGeneric.lean`): each clause is true ("with a hidden
  unit"; "for `d ≥ 2`"; "with `d_in, d_out ≥ d ≥ 2`"; "No width is asked").
- Row 891 (`Residual/OneChangeOfBasisRMSZero.lean`): each clause is true (check 7).
- Row 876 (`Dimension/UpperBoundHomogeneousRMSNormZero.lean`): the clauses on the statements are
  true, and the status is "proved" since `0ac8d09`. "The paper's sentence needs `d ≥ 2`,
  `d_in ≥ d` and width at least `d`, which Theorem A.12 does not state": `d ≥ 2` is needed
  (check 8); for `d_in ≥ d` and the width I found no case in which the sentence fails without
  them; and the three are in the paper's Scope (Section 2), which the row does not say. The same
  sentence is in the header of the file.
- The names: the 23 public theorems and the one definition of the five files are the names of the
  five rows (1, 4, 8, 2, 9), no row lists a name that is not in its file, and the 23 theorems are
  in `checks/Axioms.lean` (lines 1613 to 1635). The five files are imported by
  `SkipsLean.lean`.
- The paragraph of the index "Not yet compared by such a reader …" (from line 222 at `1c859c6`,
  from line 229 at `72700dd`) names the five files; at `72700dd` as "with the reader of the
  twenty-first audit, part A, since 21:03 UTC".

---------------------------------------------------------------------------------------------------

## Part 2: the statements, file by file

Verdicts: SAME, LEAN STRONGER (the paper's claim under fewer hypotheses or for more cases),
LEAN WEAKER, DIFFERENT, PART (a part of the paper's sentence), FALSE. All 23 theorems are proved
with the three standard axioms (`Sig.out`, `UBHchk.out`). None is FALSE.

### `OneBlock/ResidualRMSZeroStepsOn.lean` (1 theorem)

| theorem | paper sentence | verdict |
|---|---|---|
| `exists_antisymm_scale_of_flatOn_residual_rmsNorm_zero_on` | proof of B.1 (iii), "The case `ε = 0`", with `A = I`: "`D_θ h_1 η = h_1 Y + μ h_1` … `Y` is again antisymmetric … The constant terms then give `μ = c` wherever `w E A` and `g(w)` are linearly independent … For the residual network the same steps give `η_E = E (Y + c I)`" | SAME as the step. LEAN STRONGER in the block (any map of class `C¹` on an open cone of pre-activations). Against the sentence of (iv), "`B` has derivative zero on the sphere": PART, the rows at which the argument gives it. Check 6 |

### `OneBlock/ResidualRMSZeroRescale.lean` (1 definition, 3 theorems)

| name | paper sentence | verdict |
|---|---|---|
| `TurnsActiveRows` | none: a condition on `θ` that the proof of B.1 (iv) needs and does not write | not in the paper; needed (check 2) |
| `flatOn_noKink_le_mlp_rescale_residual_rmsNorm_zero` | proof of B.1 (iv): "a flat direction is the sum of a direction of the rotation and scaling of all hidden states and a direction `ψ` … and Lemma B.3 … makes `ψ` a rescaling of the units" | SAME at one `θ`, with "generic" replaced by named conditions; one of them (`hturn`) is not in the paper. LEAN STRONGER in the activation (any `σ` differentiable off `0`, positively homogeneous, with Lemma B.3 as `UnitsRescale`) and in the width |
| `funDim_mlp_oneBlock_rescale_residual_rmsNorm_zero` | B.1 (iv): "the residual network has functional dimension `P − d_model (d_model − 1)/2 − 1 − s`"; proof: "So `dim K(θ) = d_model (d_model − 1)/2 + 1 + s`" | SAME at one `θ`, for Lean's `funDim` (all inputs) |
| `exists_jacobianRank_mlp_oneBlock_rescale_residual_rmsNorm_zero` | the same sentence, with "some finite batch has kernel exactly `K(θ)`" (Notation and flat directions) | SAME at one `θ`, on the paper's inputs |

### `OneBlock/ResidualRMSZeroRescaleGeneric.lean` (8 theorems)

| theorem | paper sentence | verdict |
|---|---|---|
| `ae_turnsActiveRows_relu`, `ae_turnsActiveRows_reluSq` | none (the condition above at generic parameters) | not in the paper; they close the gap of the proof for ReLU and ReLU² |
| `ae_exists_turned_row_relu`, `ae_exists_turned_row_reluSq` | the analogue for ReLU-type blocks of part (v): "For generic parameters `w E` and `g(w)` are linearly independent for all `w` in an open set" | SAME in content, as a statement on rows `v` off the kinks |
| `ae_funDim_relu_oneBlock_residual_rmsNorm_zero`, `ae_funDim_reluSq_oneBlock_residual_rmsNorm_zero` | B.1 (iv): "For generic parameters the residual network has functional dimension `P − d_model (d_model − 1)/2 − 1 − s`" | PART of the sentence (ReLU and ReLU²; ReGLU is in other files). For these two kinds LEAN STRONGER: one hidden unit in place of "width at least `d_model`". `funDim` over all inputs |
| `ae_exists_jacobianRank_relu_oneBlock_residual_rmsNorm_zero`, `ae_exists_jacobianRank_reluSq_oneBlock_residual_rmsNorm_zero` | the same, on the paper's inputs | the same; with the statement above it is the paper's functional dimension (check 3) |

### `Residual/OneChangeOfBasisRMSZero.lean` (2 theorems)

| theorem | paper sentence | verdict |
|---|---|---|
| `cob_eq_of_eval_cob_residual_rmsNorm_zero` | A.17 (i): "For `ε = 0`, the changes of basis in `𝒢` at the hidden states … preserve that of every residual network only if they agree at all hidden states"; A.5 (iii), "only if" for `ε = 0` | SAME, for arbitrary maps `f_ℓ` with the hypothesis that the proof uses; the functions are compared at every input with `N_0(0) = 0` (check 7) |
| `eval_cob_residual_rmsNorm_zero_iff` | A.5 (iii): "Under RMSNorm with `ε = 0`, the same holds for `G_ℓ = c_ℓ Q_ℓ ∈ CO(d_model)`, with `c_ℓ > 0` and `Q_ℓ` orthogonal, when `T_G` multiplies the reads and the readout by `Q_{ℓ−1}^⊤` and `Q_L^⊤`" | SAME, with the same notes |

### `Dimension/UpperBoundHomogeneousRMSNormZero.lean` (9 theorems)

| theorem | paper sentence | verdict |
|---|---|---|
| `cobDir_single_mem_flat_skipless_rmsNorm_zero_of_rowHomogeneous` | Lemma A.3 (i): "Apply the change of basis `G ∈ GL(d_model)` at `h_ℓ` with `ℓ < L` … At every input whose hidden states are nonzero, the output becomes `Λ y` … (i) `Λ = 1` if `ε = 0`" | PART: the derivative at `G = I` (the finite form is `eval_cobAt_rmsNorm_zero_of_rowHomogeneous`). On the inputs LEAN STRONGER (every input, for Lean's total `N_0`) |
| `funDim_add_le_skipless_mlp_rescale_rmsNorm_zero`, `funDim_add_le_skipless_gated_gate_rmsNorm_zero` | after A.17: "a skipless network has more symmetries than the changes of basis in `𝒢`: all of `GL(d_model)` at `h_0, …, h_{L−1}` (Lemma A.3)" | LEAN STRONGER: the bound that this count gives, written out, at one `θ` under named conditions; the paper writes it for one block only (B.1 (iv)) |
| `ae_funDim_add_le_skipless_relu_rmsNorm_zero`, `…_reluSq_…`, `…_reglu_…` | the same, at generic parameters | the same at almost every `θ`, for `d_in ≥ d` and widths at least `d` (the paper's Scope); nothing asked of `d_out`; `d ≥ 1` |
| `ae_funDim_add_lt_skipless_relu_rmsNorm_zero`, `…_reluSq_…`, `…_reglu_…` | after A.17: "Its functional dimension then lies below the bound of (ii), so it does not satisfy the equality condition"; A.12 (iii): "For `ε = 0` and positively homogeneous blocks, the skipless network does not satisfy the equality condition (Lemma A.3)" | SAME for the three kinds by name ("positively homogeneous blocks" in general is the pointwise bound above), in a stronger form (strictly below at almost every `θ`), with the hypotheses `d ≥ 2`, `L ≥ 1`, `d_in ≥ d`, widths at least `d`, which the two sentences do not state; `d ≥ 2` and `L ≥ 1` are needed |

### Notes

- The docstrings say what each statement is ("at one parameter", "in the paper's own sense",
  "only if", "as a statement on directions"). None claims more than its statement.
- The headers of `ResidualRMSZeroRescale.lean` and `ResidualRMSZeroRescaleGeneric.lean` say that
  the paper does not state the condition; they do not say that it is needed. Check 2 (d) shows it.
- The files fit together as the paper's proof does: the step of part (iii) for `ε = 0`
  (`…StepsOn.lean`), the density and Lemma B.3 (`…Rescale.lean`), the count from both sides and
  the conditions at almost every parameter (`…RescaleGeneric.lean`).

---------------------------------------------------------------------------------------------------

## What the authors of the papers should know

Nothing in the Lean statements is false, vacuous or drifted. In order of weight:

1. **The proof of Theorem B.1 (iv), "The residual network", and the last paragraph of part (iii)
   ("The case `ε = 0`") use a step that the text does not justify for ReLU-type blocks, and that
   fails at some parameters.** The text: "The constant terms then give `μ = c` wherever `w E A` and
   `g(w)` are linearly independent", and then `μ = c` is used at every input ("(17) holds … on
   the sphere"; "Its flat directions are the rotation and the scaling of all hidden states, and
   the space `K_B` of directions of the block along which `B` has derivative zero on the sphere";
   in (iv): "a direction `ψ` … along which `B` has derivative zero on the sphere"). For a
   ReLU-type block the step from the rows where `w E` and `g(w)` are independent to all rows
   needs: every region on which some unit is active contains a row that the block does not map to
   a multiple of itself. This holds for generic parameters (Lean: `ae_turnsActiveRows_relu`,
   `ae_turnsActiveRows_reluSq`, for `d ≥ 2`), so **the theorem stands**. It does not follow from
   the conditions that the proof names. At the parameter (B) of check 2 (one residual ReLU block,
   `d = 2`, six units, `E` and `D` invertible, every `a_i ≠ 0`, the `c_i` nonzero and pairwise
   non-collinear) the block is the identity on two opposite sectors, there is a flat direction
   that is not a symmetry, and the functional dimension is 23, not 24 (exact arithmetic). One
   sentence would close it, for instance: "For generic parameters every region on which a unit is
   active contains a row `n` with `B(n)` not parallel to `n`; on a region the derivative along `ψ`
   is a polynomial in `n`, so it vanishes on the region." I read the learned skip of part (iii)
   only for `A = I`.
2. **Theorem A.12 (iii), last sentence, and the remark after Theorem A.17 need `d_model ≥ 2`.**
   For `d_model = 1`, `GL(1) = CO(1)`, the two bounds are the same number, and for
   `d = d_in = d_out = 1` with one ReLU block of width 1 the bound of (ii) is attained (rank 1,
   by hand and computed). With the Scope of Section 2 (`d_in, d_out ≥ d_model ≥ 2`,
   `d_hidden ≥ d_model`) the sentences are covered; the two statements in the appendix do not
   repeat it. Lean asks `d ≥ 2`, `L ≥ 1`, `d_in ≥ d` and widths at least `d`, and not `d_out ≥ d`.
3. **The residual value of Theorem B.1 (iv) does not need the width.** Lean proves it for ReLU
   and ReLU² blocks with one hidden unit or more; the computed ranks agree for widths 1 to `d − 1`
   (10 cases). The theorem asks "width at least `d_model`" for both networks; only the skipless
   bound uses it.
4. **In four computed cases with `d_out = d_model − 1` the residual value still holds** (ranks 10
   and 26, the formula). So `d_out ≥ d_model` may not be needed for the value; Lean asks it, as
   the theorem does. With `d_in = d_model − 1` the rank is below the formula (4 cases).
5. **The bound for skipless networks with `ε = 0` and positively homogeneous blocks at depth `L`,
   `P − L d² − (d(d−1)/2 + 1) − s`, is now a Lean statement** (the paper writes it for one block).
   Computed at depth 2 and 3 (84 parameters inside the hypotheses): never exceeded; attained at
   some parameters and not at others of the same shape (for ReLU with `d = 2` and widths `(2, 2)`:
   at none of 7). The paper claims equality for one block only; these numbers give no reason to
   claim more.
6. **Theorem A.5 (iii) for `ε = 0`:** the Lean statement is the theorem for arbitrary maps `f_ℓ`.
   The hypothesis on the blocks is needed (a block that is zero: `G = (I, 2I)` preserves every
   function). `d_model ≥ 2` is not needed for `ε = 0` (by hand).
7. **For the numerical checks (Appendix E).** For skipless ReLU-type networks at depth 2 two
   batches of `6P` and `10P` inputs at the same parameter gave different ranks in 5 of 30 cases. A
   rank that falls short at one batch can be of this kind.

## Corrections for `STATEMENTS.md` (line numbers of `1c859c6`)

Nothing in the five rows is false about a Lean statement. Six places:

1. **Row 876** (`Dimension/UpperBoundHomogeneousRMSNormZero.lean`) and the header of the file.
   "The paper's sentence needs `d ≥ 2`, `d_in ≥ d` and width at least `d`, which Theorem A.12
   does not state" → "Lean asks `d ≥ 2` and `L ≥ 1` for the strict form (needed: for `d = 1` the
   two bounds are equal, and the bound of (ii) is attained for `d = d_in = d_out = 1` and one
   block of width 1), and `d_in ≥ d` and widths at least `d` (the conditions of Lemma A.18, under
   which the directions are independent; no computed case without them had a rank at or above the
   bound of (ii)). Theorem A.12 and the remark after Theorem A.17 do not state them; the Scope of
   Section 2 does. Nothing is asked of `d_out`." Also: "the bound `P − L d² − …` is written in the
   paper for one block only".
2. **Row 883** (`OneBlock/ResidualRMSZeroRescale.lean`). After "a condition that the paper does
   not state" add: "and that is needed: at a parameter with `OneBlockGenericRMS` at which it fails
   (`d = 2`, six ReLU units, the block is the identity on two opposite sectors) the functional
   dimension is `P − (d(d−1)/2 + 1) − s − 1`, in exact arithmetic (twenty-first audit, part A,
   check 2). It is sufficient, not necessary." And for "and some row off the kinks": "(this
   follows from `TurnsActiveRows` when the block has a hidden unit, no read column is zero and `σ`
   is not zero off `0`; it is false for a block with no hidden unit)".
3. **Row 884** (`OneBlock/ResidualRMSZeroRescaleGeneric.lean`). Add: "the two statements together
   are the functional dimension on the paper's inputs (`funDimOn` on
   `residualZeroDomain ∩ noKinkRMS θ`): the batch gives "at least", `funDim` gives "at most"".
   And "at least one token".
4. **Row 891** (`Residual/OneChangeOfBasisRMSZero.lean`). Add: "the functions are compared at
   every input, with Lean's `N_0(0) = 0`; the hypothesis on the blocks is needed (a block that is
   zero); `d ≥ 2` is the paper's hypothesis".
5. **Row 882** (`OneBlock/ResidualRMSZeroStepsOn.lean`). Add: "against the analytic twin: the
   conclusion at the rows `N_0(x E)` of these inputs, not at every row of the sphere".
6. **The paragraph "Not yet compared by such a reader …"** (from line 222; from line 229 at
   `72700dd`): the five files
   (`OneBlock/ResidualRMSZeroStepsOn.lean`, `OneBlock/ResidualRMSZeroRescale.lean`,
   `OneBlock/ResidualRMSZeroRescaleGeneric.lean`, `Residual/OneChangeOfBasisRMSZero.lean`,
   `Dimension/UpperBoundHomogeneousRMSNormZero.lean`; 1 definition, 23 theorems) were compared by
   a twenty-first reader, part A (24 November): nothing false, vacuous or drifted;
   `TurnsActiveRows` is a condition that the paper's proof needs and does not state, and it is
   needed (a parameter with every named condition at which the functional dimension is one
   lower); the pair `funDim` and a batch of the paper's inputs is the paper's functional
   dimension; 32 cases of one residual block computed at 60 digits, all equal to the value, also
   for widths below `d`; 124 parameters of skipless networks, none above the bound. Report:
   `lean-statement-audit-twentyfirst-a-2026-11-24.md`.

## What I could not check

- **The proofs.** I read statements. That the 23 statements are proved rests on the compiler and
  on the axiom check (`Sig.out`, `UBHchk.out`).
- **"For generic parameters" by computation.** The computations are at one to six random
  parameters per shape. They cannot see a set of measure zero, a rank on a batch is a lower bound,
  and there is no evidence for `d` above 3.
- **The flat direction at the parameter (B) at every input.** That `ψ` is in the kernel is exact
  at 252 inputs, and the rank is 23 at 960 other inputs at 60 digits; that `ψ` is flat at every
  input of the paper is my argument by hand (one linear identity per sector). The value of Lean's `funDim` there
  (which also uses inputs with a unit at its kink) I did not compute.
- **Whether `d_in ≥ d` and the width are needed** in the fifth file: 22 cases, none against the
  conclusions without them. This is no proof that they can be dropped.
- **More than one token in the computations.** I computed with one token per input. For MLP and
  gated blocks Lean's output at an input of `T` tokens is, row by row, the output at each row (by
  reading the definitions).
- **ReGLU for the residual value**: not in these five files (it is in files written after I
  started, which I did not read). ReGLU appears in my computations only for the skipless bound.
- **The learned skip of part (iii)** for `ε = 0`: I read it for `A = I` only.
- **The library lemmas under the `ae_` statements** (`ae_oneBlockGenericRMS`,
  `ae_ne_zero_of_analytic`, `ae_rank_E_write`): I read their statements, not their proofs.
- **The dimension paper.** None of the 23 statements cites it.

## Files of this audit (in `/home/claude/audit21a/`)

`Sig.lean`, `Sig.out` (signatures and axioms of the 14 theorems of the first four files);
`UBHchk.lean`, `UBHchk.out` (axioms of the nine theorems of the fifth file; checks 1 and 8);
`UBH_8084e30.lean` (the fifth file as it was when I started); `Chk.lean`, `Chk.out`, `Chk2.lean`,
`Chk2.out` (compiled checks 1, 2, 3, 5, 7); `z21core.py` (the networks, the exact derivative, the
ranks); `z21fd.py`, `z21fd.out` (the derivative against central differences); `z21res.py`,
`z21res_relu.out`, `z21res_relusq.out` (check 4); `z21turn.py`, `z21turn.out`, `z21turn2.py`,
`z21turn2.out` (check 2 (d)); `z21skip.py`, `z21skip2.py`, `z21skip_*.out`, `z21skip2_*.out`
(check 8); `z21sum.py`, `z21_summary.out` (summary of the ranks).
