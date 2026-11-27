STATUS: complete

# Twenty-second audit, part A, of Lean statements against the papers: S Theorem B.1 (iv) for `ε = 0`: the residual value for ReGLU, the gain, and the equality for the skipless network at width `d` (24 November 2026)

Reader: an independent reader who did not write the statements. Briefs:
`audit22a_brief_2026-11-24.md`, with the rules of `audit21a_brief_2026-11-24.md`. I audited
statements and definitions, not proofs. I changed no repository file, ran no `lake build`, made no
commit and no push. My files are in `/home/claude/audit22a/`.

Library: `/home/claude/lw/lean` (branch `lean-wip`).

- **Commit read: `38eefee4b07e0e7cd685a6553c175b738b8c62a1` (24 November 2026, 21:46:07 UTC),** the
  head when I started. The branch moved while I worked; I looked at it again at `6c173fa`
  (21:54:14), at `b7d3bf3` (22:06:24) and at **`2b9d829009374fa5f76306b2ab8c8d285c65cfac`
  (22:14:34), the head when I finished.** Five of the six files are byte for byte the same at the
  four commits (`git diff` is empty), and so is every file of definitions that I read. The sixth,
  `OneBlock/SkiplessHomogeneousRMSZeroEq.lean`, had five proofs replaced by `sorry` at `38eefee`
  and at `6c173fa`; since commit `91a490a` (22:03:41) it has proofs, and it has not changed since
  `b7d3bf3`. Its header, its `variable` lines and the text of its eleven statements are the same
  before and after (compared by a script, `Eq_38eefee.lean` against `Eq_head.lean`).
- **Statements that were `sorry` at `38eefee`** (all in `OneBlock/SkiplessHomogeneousRMSZeroEq.lean`):
  `eval_skipless_rmsNorm_zero_of_rowHomogeneous`, `flatOn_le_mlp_rescale_skipless_rmsNorm_zero`,
  `funDim_mlp_oneBlock_rescale_skipless_rmsNorm_zero`,
  `exists_jacobianRank_mlp_oneBlock_rescale_skipless_rmsNorm_zero`,
  `ae_rank_E_D_read_write_of_card_eq`. The other six statements of the file were proved from these
  five. Files with `sorry` in `lean/SkipsLean` (`git grep -w sorry`): at `38eefee` two
  (`OneBlock/LearnedSkipRMSZeroBound.lean`, not of this audit, and the file above); at `b7d3bf3`
  and at `2b9d829` none.
- The six files have 24 public theorems (3 + 4 + 3 + 1 + 2 + 11) and two public definitions
  (`TurnsActiveRowsGated`, `UnitsParallel`). All 24 depend on `propext`, `Classical.choice`,
  `Quot.sound` only: by compiling `Sig22.lean` (13 theorems of the five files) and `ChkEq22.lean`
  (11 theorems of the sixth, at `b7d3bf3` and at `2b9d829`) against the build of
  `/home/claude/lp/lean`, whose copies of the six files and of the definitions were equal to
  those of `/home/claude/lw` each time (`cmp`).

Paper, as text: the skips paper ("S", `<scratchpad>/skips.txt`). I compared nothing with the
dimension paper. Line numbers of `STATEMENTS.md` are those of `2b9d829`: the rows of the six files
are lines 903 to 908 there (lines 901 to 906 at `b7d3bf3`, 897 to 902 at `38eefee`; the first
five have the same text at the commits, by checksum; the sixth differs only in its last cell,
"in work" at `38eefee`, then "proved").

**Short answer. No Lean statement is false, none is vacuous, none has drifted.** The 24 statements
are the paper's, with the conditions of the proofs written out. Three things differ from the
paper, all said in the files:

1. the residual value for ReGLU has one condition that the paper's proof needs and does not write
   (`TurnsActiveRowsGated`, the twin of `TurnsActiveRows`), proved at almost every parameter;
2. the equality for the skipless network and "by exactly `d_model²`" are stated for a block of
   width exactly `d`, where the theorem says "of width at least `d_model`";
3. at width `d` Lean proves the equality at every parameter at which `E`, `D`, `W_read`,
   `W_write` have rank `d`, where the paper says "for generic parameters".

**The condition of point 1 is needed for ReGLU as it is for ReLU. I found a parameter of one
residual ReGLU block (`d = 2`, six hidden units) that has every condition the paper's proof names
(`E`, `D` invertible, the hypotheses of Lemma B.3 for ReGLU) and at which the functional dimension
is 29, one less than `P − d(d−1)/2 − 1 − s = 30`** (check 2 (d): the rank is 29 at 898 inputs in
exact arithmetic; a flat direction that is not a symmetry is in the kernel exactly at these
inputs, and by hand at every input of the paper). The theorem, which is for generic parameters,
stands.

In 108 computed parameters the rank was the paper's value on both batches: all 40 of the
residual ReGLU network (12 of them narrower than `d`, where only Lean claims the value), and all
68 of the skipless ReLU and ReLU² networks of width at least `d` (24 at width `d`, where Lean
claims the value; 44 at widths `d + 1` to `2d + 1`, where only the paper does). One sentence of
the index and one of a header say "false for one unit" of a statement that, as defined, is true
for one unit; corrections are at the end.

How I checked.

- "By reading": every public statement and docstring of the six files and their headers; the
  definitions (`Arch`, `Params`, `hidden`, `eval`, `evalBatch`, `jacobianRank`, `funDim`, `flat`,
  `flatOn`, `funDimOn`, `rmsRow`, `rmsNorm`, `Arch.mlp`, `Arch.gated`, `relu`, `reluSq`,
  `reluDeriv`, `reluSqDeriv`, `vanillaBlock`, `gatedBlock`, `cobDir`, `scaleDir`, `rescaleDir`,
  `rescaleDirGate`, `rescaleDirMlp`, `noKinkRMS`, `noKinkGateRMS`, `OneBlockGenericGatedRMS`,
  `OneBlockGenericReGLURMS`, `residualZeroDomain`, `skiplessZeroDomain`, `RowHomogeneous`); the
  statements of the bounds that the gain uses (`ae_funDim_add_le_skipless_relu_oneBlock_rmsNorm_zero`
  and its twins); the short proofs of the `ae_` statements; and the paper: the Scope (S lines 252
  to 257), Theorem B.1 (2319 to 2347), "Notation and flat directions" (2358 to 2383), Lemma B.2,
  Lemma B.3, Step 3 of part (i) (2600 to 2620), "The case `ε = 0`" of part (iii) (2862 to 2889),
  part (iv) (2891 to 2959), and the remarks on skipless ReGLU networks (590 to 600, 3270 to 3281).
- "By hand": a short argument of my own, written where it is used.
- "By compiling": scratch files in `/home/claude/audit22a/`, compiled with `lake env lean <file>`
  from `/home/claude/lp/lean` (nothing written there): `Sig22.lean` (signatures and axioms),
  `Chk22.lean` (checks 1, 2, 3, 5), `ChkHw22.lean` (check 2), `ChkEq22.lean` (checks 1 and 6),
  `ChkDom22.lean` (check 6). All compile without error and without `sorry` (`*.out`, the last time
  at `2b9d829`); every theorem of mine that I name below has the three standard axioms. The four
  general lemmas on `funDimOn` are those of the twenty-first reader, compiled again.
- "By a computation": my own scripts. `z22core.py`: one block under pre-RMSNorm with `ε = 0`, with
  or without the skip, ReLU, ReLU² or ReGLU; the Jacobian in the weights in closed form, over
  numbers of 60 digits (python-flint `arb`, 200 bits) or over rationals. It agrees with central
  differences of a separate plain evaluation to `2.4·10⁻⁴⁷` (`z22fd.py`: 18 networks, up to three
  inputs each, every entry).
  The rank at 60 digits is by elimination with complete pivoting, and again from the singular
  values in double precision; over the runs of `z22run.py` the smallest pivot kept is `4·10⁻⁶` of
  the largest and no entry dropped is above `3.3·10⁻⁵⁵` of it, and the two ranks agree in every
  run. In exact arithmetic the weights are random
  rationals and the inputs are chosen with `N_0(x E)` a rational point of the sphere
  `|n|² = d` (so every square root is rational; the rows of an input are scaled by a positive
  number, which does not change the rank); the rank is modulo two primes near `2⁶¹` and `2⁶²`,
  which is a lower bound of the rank over the rationals (in `z22turn.py` also over the
  rationals). One token per input: these blocks act on every token alone, so the Jacobian at an
  input of `T` tokens is the stack of the Jacobians at its rows. Inputs of a batch: one third
  with a random direction of `h_0 = x E`; one third near the kink of a random unit (distance
  `10⁻⁴` to 1, either side); one third are one input in every pattern of active units found
  among 40000 random directions; random scales from 0.2 to 5; two batches of `4P` and `7P`
  inputs. **A rank on a batch is a lower bound of the functional dimension.** For the residual
  network, and for the skipless network of width at least `d`, the upper bound is a Lean theorem,
  so "rank = value" on a batch settles the value at that parameter. I ran the coordinator's script `units_parallel_check_2026-11-24.py` once (16 cases,
  none differs from mine); my numbers are from my own scripts.

---------------------------------------------------------------------------------------------------

## Part 1: the checks

### Check 1. Generic means almost every parameter, for every Haar measure

**Verdict: yes, in all 14 `ae_` statements (four in `ResidualRMSZeroReGLUGeneric.lean`, three in
`ResidualRMSZeroGainHomogeneous.lean`, seven in `SkiplessHomogeneousRMSZeroEq.lean`); every index
type of the weights is finite; the statements apply to a concrete Haar measure.** (By reading; 14
instances by compiling, `Chk22.lean` and `ChkEq22.lean`.)

- The `variable` lines of the three files are the same:

  ```
  variable {T d dIn dOut : Type*} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn]
    [Fintype dOut]
  variable {hid : Fin 1 → Type} [∀ ℓ, Fintype (hid ℓ)]
  ```
  The weights are `E : Matrix dIn d ℝ`, `read 0 : Matrix d (hid 0) ℝ` (MLP) or
  `Matrix d (hid 0 ⊕ hid 0) ℝ` (gated), `write 0 : Matrix (hid 0) d ℝ`, `D : Matrix d dOut ℝ`.
  Each index type has `Fintype`.
- Each of the 14 statements has `μ` as a variable with `[μ.IsAddHaarMeasure]` and `∀ᵐ θ ∂μ`. None
  is "there is a parameter" or "on an open set". For instance:

  ```
  theorem ae_funDim_reglu_oneBlock_residual_rmsNorm_zero [Nonempty (hid 0)]
      (μ : Measure (Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut))
      [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
      (hdOut : Fintype.card d ≤ Fintype.card dOut) :
      ∀ᵐ θ ∂μ, funDim (Arch.gated relu (rmsNorm 0) hid) 1 θ
          + ((Fintype.card d * (Fintype.card d - 1) / 2 + 1) + 2 * Fintype.card (hid 0))
        = Module.finrank ℝ
            (Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut)
  ```
- By compiling, at the concrete measure `Measure.addHaar` on the space of the weights, with the
  number of parameters computed:

  | my theorem | statement used | the network | `P` | conclusion at almost every `θ` |
  |---|---|---|---|---|
  | `turnsGated_concrete22` | `ae_turnsActiveRowsGated_reglu` | ReGLU, `d = 2`, width 1 | | `TurnsActiveRowsGated θ` |
  | `turnedGated_concrete22` | `ae_exists_turned_row_reglu` | ReGLU, `d = 3`, width 4 | | a turned row off the kinks of the gates |
  | `funDim_reglu_concrete22` | `ae_funDim_reglu_oneBlock_residual_rmsNorm_zero` | ReGLU, one token, `d = d_in = d_out = 2`, width 1 | 14 | `funDim = 10` |
  | `batch_reglu_concrete22` | `ae_exists_jacobianRank_reglu_oneBlock_residual_rmsNorm_zero` | ReGLU, two tokens, `d = d_out = 3`, `d_in = 4`, width 4 | 57 | a batch of the paper's inputs of rank 45 |
  | `gain_relu_concrete22` | `ae_funDim_skipless_add_le_relu_oneBlock_residual_rmsNorm_zero` | ReLU, `d = 2`, width 2 | | `funDim 0 θ + 4 ≤ funDim 1 θ` |
  | `gain_reluSq_concrete22` | `ae_funDim_skipless_add_le_reluSq_oneBlock_residual_rmsNorm_zero` | ReLU², two tokens, `d = d_out = 2`, `d_in = 3`, width 3 | | `funDim 0 θ + 4 ≤ funDim 1 θ` |
  | `gain_reglu_concrete22` | `ae_funDim_skipless_add_le_reglu_oneBlock_residual_rmsNorm_zero` | ReGLU, `d = 3`, `d_in = 4`, width 4 | | `funDim 0 θ + 9 ≤ funDim 1 θ` |
  | `ranks_concrete22` | `ae_rank_E_D_read_write_of_card_eq` | ReLU, `d = d_out = 3`, `d_in = 4`, width 3 | | the four ranks are 3 |
  | `funDim_skipless_relu_concrete22` | `ae_funDim_relu_oneBlock_skipless_rmsNorm_zero` | ReLU, `d = d_in = d_out = 2`, width 2 | 16 | `funDim = 8` |
  | `batch_skipless_relu_concrete22` | `ae_exists_jacobianRank_relu_oneBlock_skipless_rmsNorm_zero` | ReLU, two tokens, `d = d_out = 3`, `d_in = 4`, width 3 | 39 | a batch of the paper's inputs of rank 23 |
  | `funDim_skipless_reluSq_concrete22` | `ae_funDim_reluSq_oneBlock_skipless_rmsNorm_zero` | ReLU², the same sizes | 39 | `funDim = 23` |
  | `batch_skipless_reluSq_concrete22` | `ae_exists_jacobianRank_reluSq_oneBlock_skipless_rmsNorm_zero` | ReLU², `d = d_in = d_out = 2`, width 2 | 16 | a batch of the paper's inputs of rank 8 |
  | `gain_eq_relu_concrete22` | `ae_funDim_relu_oneBlock_residual_rmsNorm_zero_eq_add` | ReLU, `d = 2`, width 2 | | `funDim 1 θ = funDim 0 θ + 4` |
  | `gain_eq_reluSq_concrete22` | `ae_funDim_reluSq_oneBlock_residual_rmsNorm_zero_eq_add` | ReLU², `d = 3`, `d_in = 4`, width 3 | | `funDim 1 θ = funDim 0 θ + 9` |

### Check 2. ReGLU, the residual value

```
def TurnsActiveRowsGated
    (θ : Params (Arch.gated (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) : Prop :=
  ∀ v : d → ℝ, (∀ i, (v ᵥ* θ.read 0) (Sum.inl i) ≠ 0) →
    (∃ i, σ ((v ᵥ* θ.read 0) (Sum.inl i)) ≠ 0) →
    v ∈ closure {u : d → ℝ | LinearIndependent ℝ ![u, gatedBlock σ
      ((θ.read 0).submatrix id Sum.inl) ((θ.read 0).submatrix id Sum.inr) (θ.write 0) u]}

theorem flatOn_noKinkGate_le_reglu_residual_rmsNorm_zero
    (θ : Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut)
    (hθ : OneBlockGenericReGLURMS θ) (hd : 2 ≤ Fintype.card d) (hturn : TurnsActiveRowsGated θ)
    (hw : ∃ v : d → ℝ, (∀ i, (v ᵥ* θ.read 0) (Sum.inl i) ≠ 0) ∧
      LinearIndependent ℝ ![v, gatedBlock relu ((θ.read 0).submatrix id Sum.inl)
        ((θ.read 0).submatrix id Sum.inr) (θ.write 0) v])
    (η : Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut)
    (hη : η ∈ flatOn (Arch.gated relu (rmsNorm 0) hid) 1 θ
      (residualZeroDomain (Arch.gated relu (rmsNorm 0) hid) θ ∩ noKinkGateRMS θ)) :
    ∃ (Y : Matrix d d ℝ) (c : ℝ) (α β : ∀ ℓ, hid ℓ → ℝ), Yᵀ = -Y ∧
      η = cobDir θ (fun _ => Y) + scaleDir θ (fun _ => c) + rescaleDir θ α
        + rescaleDirGate 1 θ β
```

**Verdict: the statements are the paper's for ReGLU with `s = 2 d_hidden`; `TurnsActiveRowsGated`
is the gated twin of `TurnsActiveRows`; the signs are those of the symmetries; the pair is the
paper's functional dimension; no hypothesis is extra, and Lean asks less in one place (a hidden
unit, no width). The condition `TurnsActiveRowsGated` is needed.**

**(a) The twin.** (By reading; by compiling.) `TurnsActiveRows` has the rows `v` with every
pre-activation nonzero and some `σ` of a pre-activation nonzero; `TurnsActiveRowsGated` has the
rows with every gate nonzero (`Sum.inl` columns of `v W_read`) and some `σ` of a gate nonzero, and
no condition on the values (a value has no kink). The block at a row is
`gatedBlock σ W_gate W_value W_write u = ∑_i σ(u g_i)(u v_i) a_i`, with the gate columns and the
value columns of the read. By compiling (`gated_row22`): row `t` of
`(Arch.gated σ χ hid).f 0 (n W_read) W_write` is `gatedBlock σ (W_read gate columns) (W_read
value columns) W_write (n t)`, so this is the block of the network. The two exceptions are right
for a ReLU gate (by hand): where no gate is active the block is `0` on a neighbourhood, no row
nearby is turned, and the derivative of the block along every direction is `0` there (each term
has a factor `relu(gate)` or `relu'(gate)`); a row with a gate at `0` is not asked, and the
paper's inputs have none.

**(b) The conclusion and the signs.** (By compiling, `direction_entries_gated22`; by hand.) The
direction of the conclusion has `E (Y + c I)` at `E`; `−Y W_read + β_i (gate column i)` at the
gate columns; `−Y W_read − α_i (value column i)` at the value columns;
`W_write (Y + c I) + (α_i − β_i)(row i)` at `W_write`; `−Y D` at `D`. Lemma B.3 for ReGLU
(S line 2466): "`(ψc_i, ψβ_i) = λ_i (c_i, β_i)`, `(ψe_i, ψβ′_i) = −α_i (e_i, β′_i)` and
`ψa_i = (α_i − λ_i) a_i`", with `c_i` the gate and `e_i` the value: the same with `λ = β`.
`rescaleDir θ α` is the derivative of `(v_i, a_i) ↦ (v_i / λ, λ a_i)`, `λ = e^{τ α_i}`;
`rescaleDirGate 1 θ β` that of `(g_i, a_i) ↦ (λ g_i, a_i / λ)`, `λ = e^{τ β_i}`, which preserves
`relu(u g_i)(u v_i) a_i` for `λ > 0`. One `Y` and one `c` for both hidden states: "the rotation
and scaling of all hidden states". Two rescalings per unit: `s = 2 d_hidden` (S line 2617:
"`2 d_hidden` for ReGLU"). The count in `funDim_reglu_…` is
`(d(d−1)/2 + 1) + 2 · card (hid 0)`: the paper's `d_model (d_model − 1)/2 + 1 + s`.

**(c) Which functional dimension.** (By compiling, `mem_paper_inputs_gated_iff22`,
`ae_funDimOn_reglu22`.) `x ∈ residualZeroDomain … θ ∩ noKinkGateRMS θ` if and only if no row of
`x E` is zero, no row of `h_1` is zero, and no gate `(N_0(x E) W_read)_{t, inl i}` is zero: the
paper's inputs ("no hidden unit sits at its kink … With `ε = 0`, it also excludes the inputs at
which a state that is normalized vanishes"; for ReGLU the kink is that of the gate). And at
almost every `θ`, `funDimOn … 1 θ (residualZeroDomain … θ ∩ noKinkGateRMS θ) + ((d(d−1)/2 + 1) +
2 d_hidden) = P`, from the two library statements: the largest rank over the batches of the
paper's inputs is the value.

**(d) Is `TurnsActiveRowsGated` needed? Yes: without `hturn` the three pointwise statements would
be false.** (By a computation in exact arithmetic, `z22turn.py`, output `z22turn.out`; the
flatness at every input by hand.) The parameter: `d = d_in = d_out = 2`, six hidden units, one
token, `E = [[2, 1], [1, 3]]`, `D = [[1, −2], [3, 1]]`;

- gates `g = (1,6), (−1,6), (6,−5), (7,4), (−7,4), (−3,−2)`;
  values `v = (0,1), (1,6), (2,−1), (1,3), (3,1), (−1,2)`;
  rows `a = (1,0), (6,1), (−17426/47495, 2363/20355), (−9892/28497, −9452/47495),
  (28624/1365, 13064/1365), (102334/1365, 13129/195)`.
- Each clause of the hypotheses: `E` and `D` have rank 2; every `a_i ≠ 0`; every gate is nonzero;
  the gates are pairwise non-collinear (15 determinants); every value is nonzero; no value is
  proportional to the gate of its unit (6 determinants): this is `OneBlockGenericReGLURMS θ`.
  `d = 2 ≥ 2`. `hw` holds: in ten of the twelve sectors between the kink lines `u` and `B(u)` are
  independent at the two points tried.
- `TurnsActiveRowsGated θ` fails: on the sector with the active gates 1, 3, 4 (it contains
  `u = (1, 0)`, at which no gate is zero and gate 1 is active)
  `B(u) = l(u) u` with the linear form `l = (−973556/142485, −257567/142485)`, so no row near
  `(1, 0)` is turned. On the opposite sector (active gates 2, 5, 6) also `B(u) = l′(u) u`.
- The direction `ψ`: the value column of unit 1 moves by `(1, 0)`, row 1 of `W_write` by
  `(0, 1)`, the gate column of unit 2 by `(−1/6, 0)`, row 2 of `W_write` by `(0, −1/6)`; nothing
  else moves. By hand: where gate 1 is active its terms give the derivative `(n g_1) n` of the
  block, and where gate 2 is active its terms give `−(n g_1) n` (the value of unit 2 is
  `v_2 = g_1`). Gates 1 and 2 are both active on five sectors and both inactive on five; only
  gate 1 is active on the sector `{1, 3, 4}` and only gate 2 on `{2, 5, 6}`. On these two sectors
  `h_1 = x E + B(n)` is a multiple of `n`, and the derivative of `h_1` along `ψ` is `± (n g_1) n`,
  a multiple of `h_1`, which the last normalization removes. So `ψ` is flat at every input at
  which no normalized row vanishes and no gate is at its kink. It is not a sum of the rotation,
  the scaling and the twelve rescalings (exact: the fifteen vectors have rank 15).
- Exact computation: at 898 rational inputs (all twelve gate patterns) the Jacobian has rank
  **29** over the rationals and modulo two primes; `P = 44`, and
  `P − (d(d−1)/2 + 1) − s = 44 − 2 − 12 = 30`. The fourteen symmetry directions and `ψ` are in the
  kernel exactly at every one of these inputs.
- Control: the same gates and values with other rows `a_i`: rank 30 on both batches.
- What this refutes: not a Lean statement (each has `hturn`). At this `θ`, without `hturn`,
  `flatOn_noKinkGate_le_reglu_residual_rmsNorm_zero` would be false (`ψ` is flat on
  `residualZeroDomain ∩ noKinkGateRMS θ` and not of the form) and so would
  `exists_jacobianRank_reglu_oneBlock_residual_rmsNorm_zero` (no batch of these inputs has rank
  30). I did not compute Lean's `funDim` (all inputs) at this `θ`.

**(e) `hw` and non-vacuity.** (By compiling.) `hw_of_turnsActiveRowsGated22` (`ChkHw22.lean`): for
a ReGLU block with a hidden unit, if no gate column of `W_read` is zero (a field of
`OneBlockGenericReGLURMS`) and `TurnsActiveRowsGated θ`, then `hw`. So `hw` is not a further
condition for a block with a hidden unit; without a hidden unit it is false, the block being `0`
(`not_hw_of_isEmpty22`). `ae_hypotheses_reglu22`: for `d_in, d_out ≥ d ≥ 2` and a block with a
hidden unit, at almost every `θ`, for every Haar measure, `OneBlockGenericReGLURMS θ ∧
TurnsActiveRowsGated θ ∧ hw`; and some parameter has them (`exists_hypotheses_reglu22`).

**(f) Hypotheses against Theorem B.1 (iv) and its Scope.** (By reading, from the compiled
signatures.) The theorem: `d_model ≥ 2`; input and output dimensions at least `d_model`; one
block; `ε = 0`, no biases; a ReLU, ReLU² or ReGLU block of width at least `d_model`; generic
parameters.

| hypothesis of `ae_funDim_reglu_…` and `ae_exists_jacobianRank_reglu_…` | in the theorem? |
|---|---|
| finite sizes, `[Nonempty T]` | yes |
| `[Nonempty (hid 0)]` (a hidden unit) | follows from "width at least `d_model`" and `d_model ≥ 2` |
| `μ` with `[μ.IsAddHaarMeasure]` | "for generic parameters" |
| `hd : 2 ≤ card d`, `hdIn : card d ≤ card dIn`, `hdOut : card d ≤ card dOut` | yes |
| one block, stream `1`, `χ = rmsNorm 0`, no biases, the gate `relu` | yes |

There is no hypothesis on the width beyond one hidden unit. `d ≥ 2` is needed (by hand: for
`d = 1` the output is `± D`).

**(g) The computation** (`z22run.py`; outputs `z22_reglu_res.out`). One residual ReGLU block; 20
cases: `d = 2` with widths 1 to 5 and `d = 3` with widths 1 to 7 at `d_in = d_out = d`, and
`(d, d_in, d_out, width) = (2,3,2,1), (2,3,2,3), (2,4,3,2), (2,4,3,4), (3,4,3,1), (3,4,3,4),
(3,5,4,2), (3,5,4,5)`; `P` from 14 to 81. Each case twice: random real weights at 60 digits, and
other, random rational weights in exact arithmetic. **Both ranks are equal to
`P − (d(d−1)/2 + 1) − 2 d_hidden` in all 40 parameters (80 batches)**, also in the 12 with a width
below `d`. For `d_in = d_out = d`:

| `d = 2`, widths 1 to 5: value = rank | `d = 3`, widths 1 to 7: value = rank |
|---|---|
| 10, 14, 18, 22, 26 (`P` = 14, 20, 26, 32, 38) | 21, 28, 35, 42, 49, 56, 63 (`P` = 27, 36, …, 81) |

The batches met every pattern of active gates found at random (for `d = 2`, all `2 · width`
sectors; for `d = 3` and widths 4 to 7: 14, 22, 30 or 32, 44 regions; the count of regions is
14, 22, 32, 44, so one draw at 60 digits missed two small regions).

### Check 3. The gain "at least `d²`"

```
theorem ae_funDim_skipless_add_le_reglu_oneBlock_residual_rmsNorm_zero
    (μ : Measure (Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, funDim (Arch.gated relu (rmsNorm 0) hid) 0 θ + Fintype.card d ^ 2
      ≤ funDim (Arch.gated relu (rmsNorm 0) hid) 1 θ
```
(and the same for `Arch.mlp relu` and `Arch.mlp reluSq`).

**Verdict: it is the paper's sentence "So the skip raises the functional dimension by at least
`d_model²`", for the three kinds of block, and the direction of the two notions is the right one:
the Lean statement implies the paper's.** (By reading; by compiling.)

- Both networks have the same weights `θ`; the stream matrix `0` is the skipless network, `1` the
  residual one.
- Lean's `funDim` uses all inputs. For the residual network it is the paper's functional
  dimension (check 2 (c), and the twenty-first audit for ReLU and ReLU²). For the skipless
  network it is at least the paper's: a batch of the paper's inputs is a batch
  (`funDimOn_le_funDim22`, for any network and any set of inputs). So
  paper's skipless value `+ d² ≤ funDim 0 θ + d² ≤ funDim 1 θ =` paper's residual value.
- By compiling (`ae_gain_paper_relu22`, `ae_gain_paper_reluSq22`, `ae_gain_paper_reglu22`): under
  the hypotheses of the three statements, at almost every `θ`,
  `funDimOn … 0 θ (skiplessZeroDomain … θ ∩ noKink… θ) + d² ≤
  funDimOn … 1 θ (residualZeroDomain … θ ∩ noKink… θ)`: the paper's sentence for the paper's
  functional dimensions (largest rank over the batches of the paper's inputs), from the library
  statements.
- Hypotheses: `d ≥ 2`, `d_in ≥ d`, `d_out ≥ d`, width at least `d` (`hhid`): all four are the
  theorem's. The width is asked because the bound for the skipless network is stated for it.
- The computation, at the same weights for both networks (`z22gain.py`, output `z22gain.out`; 10
  sizes, three kinds, exact and 60 digits): in the 42 parameters with a width at least `d` the
  rank with the skip minus the rank without it is `d²` on both batches (4 for `d = 2`, 9 for
  `d = 3`), ReGLU included. In the 18 with a width below `d` (outside the theorem) the rank
  computed without the skip is below `P − d² − d(d−1)/2 − 1 − s`, so the computed difference is
  above `d²`; for width 1 this is the gain (the skipless rank is at most `d_out`, see check 6);
  for `d = 3` and width 2 the skipless rank is a lower bound only, and I conclude nothing.

### Check 4. The final normalization lemma

```
theorem exists_antisymm_of_fderiv_rmsNorm_zero_mul {ι : Type*} (g k : ι → Matrix T d ℝ)
    (D δ : Matrix d dOut ℝ) (hD : D.rank = Fintype.card d)
    (hg : ∀ i t, g i t ≠ 0)
    (hO : ∃ O : Set (d → ℝ), IsOpen O ∧ O.Nonempty ∧ ∀ v ∈ O, ∃ i t, g i t = v)
    (h : ∀ i, fderiv ℝ (rmsNorm 0 : Matrix T d ℝ → Matrix T d ℝ) (g i) (k i) * D
      + rmsNorm 0 (g i) * δ = 0) :
    ∃ Y : Matrix d d ℝ, Yᵀ = -Y ∧ δ = -(Y * D) ∧
      ∀ i t, k i t = g i t ᵥ* Y + ((g i t ⬝ᵥ k i t) / (g i t ⬝ᵥ g i t)) • g i t
```

**Verdict: true as stated; it is the paper's step ("`η_D = −Y D` with `Y` antisymmetric, since
`h_1` takes all values in an open set, and `D_θ h_1 η = h_1 Y + μ h_1`"); the hypothesis `hO` is
the paper's "takes all values in an open set" and is used; the formula for the multiple is
right.** (By reading, by hand, by a computation: `z22readout.py`, output `z22readout.out`.)

- By hand. For a row `g ≠ 0`, `𝐃N_0(g)[k] = ρ⁻¹ (k − g ⟨g,k⟩/⟨g,g⟩)` with `ρ = |g|/√d`, and
  `N_0(g) = ρ⁻¹ g`. So `h` says `(k − μ g) D + g δ = 0` with `μ = ⟨g,k⟩/⟨g,g⟩`. With a right
  inverse `D⁺` of `D` and `Y = −δ D⁺`: `k = g Y + μ g`; then `⟨g Y, g⟩ = ⟨k − μ g, g⟩ = 0` on an
  open set of rows `g`, so `Y` is antisymmetric; and `g (Y D + δ) = 0` on an open set, so
  `δ = −Y D`. The multiple is `⟨g,k⟩/⟨g,g⟩` because `⟨g Y, g⟩ = 0`.
- (a) At 60 digits, 100 random cases (`d` from 2 to 5, `d_out` from `d` to `d + 2`): with `Y`
  antisymmetric, a number `μ`, `k = g Y + μ g` and `δ = −Y D`, the left side of `h`, with
  `𝐃N_0` taken by central differences of `N_0` itself, is at most `3.8·10⁻⁴³`, and
  `⟨g,k⟩/⟨g,g⟩ = μ`.
- (b) The converse, in exact arithmetic: `h` times `ρ` is a rational linear system in
  `(k_1, …, k_n, δ)`. For `n` random rational rows `g_i` (one token each) I computed all its
  solutions and tested the conclusion on a basis of them (`Y := −δ D⁺` antisymmetric,
  `δ = −Y D`, `k_i = g_i Y + (⟨g_i,k_i⟩/⟨g_i,g_i⟩) g_i`). For
  `(d, d_out) = (2,2), (2,3), (3,3), (3,4), (4,4), (4,6)` the solutions have the dimension
  `n + d(d−1)/2` of the lemma, and the conclusion holds on every basis solution, from
  `n = 4, 3, 6, 6, 10, 10` rows on (up to the largest `n` tried, `d(d+1)/2 + 3`). With fewer
  rows there are more solutions and the conclusion fails: finitely many rows do not always
  suffice, an open set does.
- (c) With rows `g_i` in a hyperplane (12 rows with first coordinate 0; not an open set) the
  conclusion fails: 15 solutions against 13 (`d = 2`), 18 against 15 (`d = 3`), 23 against 18
  (`d = 4`, `d_out = 5`). So `hO` is used.
- `hg` (no zero row) is the paper's `Ω`; `hD` holds at generic `D` for `d_out ≥ d`. The lemma has
  no network in it; in `SkiplessHomogeneousRMSZeroEq.lean` `g` is the output of the block.

### Check 5. `UnitsParallel`

```
def UnitsParallel (σ σ' : ℝ → ℝ) (k : ℕ) (n m q : Type*) [Fintype n] [Fintype m] [Fintype q] :
    Prop :=
  ∀ (c : q → n → ℝ) (a : q → m → ℝ) (ψc : q → n → ℝ) (β : q → m → ℝ),
    LinearIndependent ℝ c → LinearIndependent ℝ a → 2 ≤ Fintype.card q →
    (∀ x : n → ℝ, (∀ i, x ⬝ᵥ c i ≠ 0) → ∑ i, σ (x ⬝ᵥ c i) • a i ≠ 0 →
      ∃ μ : ℝ, ∑ i, (σ (x ⬝ᵥ c i) • β i + (σ' (x ⬝ᵥ c i) * (x ⬝ᵥ ψc i)) • a i)
        = μ • ∑ i, σ (x ⬝ᵥ c i) • a i) →
    ∃ (c₀ : ℝ) (lam : q → ℝ), ∀ i, ψc i = lam i • c i ∧ β i = (c₀ - (k : ℝ) * lam i) • a i

theorem relu_unitsParallel (n m q : Type*) [Fintype n] [Fintype m] [Fintype q] :
    UnitsParallel relu reluDeriv 1 n m q
theorem reluSq_unitsParallel (n m q : Type*) [Fintype n] [Fintype m] [Fintype q] :
    UnitsParallel reluSq reluSqDeriv 2 n m q
```

**Verdict: it is equation (18) with the two steps "The kinks stay" and "One scale", for the part
of the paper's step in which the columns `c_i` are linearly independent and the rows `a_i` are
linearly independent: a block of width exactly `d` (the smallest width of the theorem). It is not
the paper's step for wider blocks. For that part it says more than the paper: every such `c`, `a`,
not generic ones. It is true for two or more units. As defined it is also true for one unit; what
is false for one unit is the statement without the clause "at least two units".** (By reading, by
hand, by compiling, by an exact computation.)

- The roles. `c i`: the columns `c_i` of `C = E W_read` (in `ℝ^{d_in}`, the index type `n`); `a i`:
  the rows `a_i` of `W_write`; `ψc i`: the paper's `ψc_i`; `β i`: `ψa_i − a_i Y`. The hypothesis
  is (18), "`J(x) = μ(x) h_1(x)` on `Ω`", asked only off the kinks and where the output is not
  zero. The conclusion: `ψc_i = λ_i c_i` is "so `ψc_i = λ_i c_i` for a number `λ_i`"; and
  `β_i = (c₀ − k λ_i) a_i` is "`b_i = ψa_i − a_i Y + k λ_i a_i`" with "`μ = c`": the equation
  `∑ σ(x c_i)(b_i − μ a_i) = 0` with `μ = c₀` gives `b_i = c₀ a_i`.
- What part of the paper's step. The paper's hypotheses are: every `a_i ≠ 0`, the `c_i` nonzero
  and pairwise non-collinear, and generic parameters (used for "`h_1(x_0)` is not parallel to
  `a_i`" and "two entries `h_a` and `h_b` of `h_1` have no common factor"). Lean asks more:
  independent `c_i` and independent `a_i`, which allows at most `min(d_in, d)` units; with the
  theorem's "width at least `d_model`" this is width exactly `d`. In return no genericity is
  asked.
- One unit. The clause `2 ≤ Fintype.card q` is a hypothesis inside the definition, so
  `UnitsParallel σ σ' k n m q` holds for every `σ`, `σ'`, `k` when `q` has fewer than two
  elements (compiled, `unitsParallel_of_card_lt_two22`). Without the clause the statement is
  false for one unit when the input has at least two coordinates: `c = e_0`, `a = e_0`,
  `ψc = e_1`, `β = 0` in the plane, ReLU (compiled, `one_unit_counterexample22`: every clause of
  the hypothesis holds, `μ = x_1 / x_0`, and `ψc` is not a multiple of `c`). With one coordinate
  of the input it is true (computed). The header ("With one unit the statement is false") and the
  index ("False for one unit") mean the statement without the clause.
- Two or more units, in exact rational arithmetic (`z22units.py`, outputs `z22units.out`,
  `z22units_more.out`). The condition "`J(x)` is parallel to `h_1(x)`" is linear in `(ψc, β)`
  (the 2 × 2 minors), so on a batch the solutions are the kernel of a rational matrix; the
  solutions named by the statement have dimension `q + 1` and are always in it. For random
  rational independent `c` and `a`, shapes `(n, m, q)` = (2,2,2), (3,3,3), (4,4,4), (3,2,2),
  (2,3,2), (4,3,3), (3,4,3), (5,5,5), (4,6,4), (5,3,2), (6,2,2), (6,3,3), (7,4,2), (5,5,3), ReLU
  and ReLU², with six or more points in each pattern of active units found (all `2^q − 1`
  patterns with an active unit in 45 of the 48 systems; 13 of 15, 27 and 29 of 31 in the other
  three): **the solutions have dimension exactly `q + 1` in all 48 systems.** (For the shape
  (5,3,2) six points per pattern were too few, the kernel was 6; from ten points per pattern on
  it is 3. A kernel on a batch is an upper bound.)
- For information, outside the Lean statement: with more units than coordinates (the paper's
  wider blocks; `c` or `a` dependent, random rational), shapes (2,2,3), (2,2,4), (2,2,5), (3,3,4),
  (3,3,5), (3,3,7), (2,3,3), (3,2,3): the solutions have dimension `q + 1` in all 32 systems. This
  agrees with the paper's two steps for wider blocks at these weights; Lean does not state them.

### Check 6. The equality at width `d`

```
theorem eval_skipless_rmsNorm_zero_of_rowHomogeneous {A : Arch T d 1} (hA : A.χ = rmsNorm 0)
    {k : ℕ} (hf : RowHomogeneous A k) (θ : Params A dIn dOut) (x : Matrix T dIn ℝ)
    (hx : ∀ t, (x * θ.E) t ≠ 0) :
    eval A 0 θ x = rmsNorm 0 (A.f 0 (x * θ.E * θ.read 0) * θ.write 0) * θ.D

theorem flatOn_le_mlp_rescale_skipless_rmsNorm_zero {k : ℕ}
    (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (hhom : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z) (hk : k ≠ 0) (hσ1 : σ 1 ≠ 0)
    (hP : UnitsParallel σ σ' k dIn d (hid 0))
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
    (hd : 2 ≤ Fintype.card d) (hcard : Fintype.card (hid 0) = Fintype.card d)
    (hE : θ.E.rank = Fintype.card d) (hD : θ.D.rank = Fintype.card d)
    (hR : (θ.read 0).rank = Fintype.card d) (hW : (θ.write 0).rank = Fintype.card d)
    (η : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
    (hη : η ∈ flatOn (Arch.mlp σ (rmsNorm 0) hid) 0 θ
      (skiplessZeroDomain (Arch.mlp σ (rmsNorm 0) hid) θ ∩ noKinkRMS θ)) :
    ∃ (X Y : Matrix d d ℝ) (c : ℝ) (α : ∀ ℓ, hid ℓ → ℝ), Yᵀ = -Y ∧
      η = cobDir θ ![X, Y] + c • scaleDir θ ![0, 1] + rescaleDirMlp k θ α

theorem ae_funDim_relu_oneBlock_skipless_rmsNorm_zero
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hcard : Fintype.card (hid 0) = Fintype.card d) :
    ∀ᵐ θ ∂μ, funDim (Arch.mlp relu (rmsNorm 0) hid) 0 θ
        + (Fintype.card d ^ 2 + (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
          + Fintype.card (hid 0))
      = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut)

theorem ae_funDim_relu_oneBlock_residual_rmsNorm_zero_eq_add
    … (hcard : Fintype.card (hid 0) = Fintype.card d) :
    ∀ᵐ θ ∂μ, funDim (Arch.mlp relu (rmsNorm 0) hid) 1 θ
      = funDim (Arch.mlp relu (rmsNorm 0) hid) 0 θ + Fintype.card d ^ 2
```

**Verdict: the statements are "with equality for ReLU and ReLU² blocks" and "by exactly
`d_model²`" of Theorem B.1 (iv) for a block of width exactly `d`: a part of the theorem, which
says "of width at least `d_model`". Within this part the directions, the count, the set of
inputs and the two functional dimensions are the paper's, and the pointwise statements say more
than the paper (every parameter with the four ranks). The hypothesis `hx` of the first statement
is not needed.** (By reading, by hand, by compiling, by a computation.)

- **"Its normalization before the block drops out."** The paper: "`N_ε(B(N_ε(h))) = N_ε(B(h))`:
  the skipless network computes `x ↦ N_ε(B(x E)) D`". Lean: the same, for any block that is
  positively homogeneous row by row, of any degree. The hypothesis `hx` (no zero row of `x E`) is
  not needed: by compiling (`eval_skipless_no_hx22`, `ChkEq22.lean`, my own proof, which does not
  use the library statement), the equation holds at every input, because with Lean's `N_0(0) = 0`
  a zero row is its own normalization. The paper's inputs have `hx`, so nothing is lost.
- **The flat directions.** By compiling (`direction_entries_skipless22`):
  `cobDir θ ![X, Y] + c • scaleDir θ ![0, 1] + rescaleDirMlp k θ α` has `E X` at `E`;
  `−X W_read + α_i (column i)` at `W_read`; `W_write (Y + c I) − k α_i (row i)` at `W_write`;
  `−Y D` at `D`. The paper, "The skipless network: the bound" and "Counting": "the entries `E X`
  at `E` and `−X W_read` at `W_read`, with the entries `W_write (Y + c I)` at `W_write` and
  `−Y D` at `D` for an antisymmetric `Y` and a number `c`, and along the rescalings of the
  units": the same, with the same signs (`X` any matrix: `GL(d)` at `h_0`; `Y` antisymmetric and
  `c`: `CO(d)` at `h_1`; the scaling moves `W_write` only). The count
  `d² + (d(d−1)/2 + 1) + card (hid 0)` is the paper's
  `d_model² + d_model (d_model − 1)/2 + 1 + s`.
- **The inputs.** `skiplessZeroDomain A θ` is: no row of `x E` is zero and no row of the output
  of the block is zero. The paper: "The network is defined on the set `Ω` of inputs at which some
  unit is active: for generic parameters `h_1 ≠ 0` there, and `h_1 = 0` elsewhere", and the
  inputs off the kinks. By compiling (`mem_skipless_inputs_relu_iff22`, `ChkDom22.lean`): for a
  ReLU block whose rows of `W_write` are linearly independent,
  `x ∈ skiplessZeroDomain … θ ∩ noKinkRMS θ` if and only if no entry of `x E W_read` is zero and
  for every token some entry of `x E W_read` is positive. So at the parameters of the statements
  (width `d`, `W_write` of rank `d`) the set is the paper's `Ω` off the kinks, token by token.
- **The hypotheses of the pointwise statements.**

  | hypothesis | what it is |
  |---|---|
  | `hσ`, `hhom` | `σ` differentiable off `0`, positively homogeneous of degree `k`: true of ReLU (`k = 1`) and ReLU² (`k = 2`) |
  | `hk : k ≠ 0`, `hσ1 : σ 1 ≠ 0` | true of ReLU and ReLU². They make `h_1` take all values in an open set (by hand: on the inputs with all units active the hidden layer is `σ(1) z^k`, `z` in the open positive orthant); with `k = 0` it would not |
  | `hP : UnitsParallel σ σ' k dIn d (hid 0)` | "The kinks stay" and "One scale"; proved for ReLU and ReLU² (check 5) |
  | `hd : 2 ≤ card d` | the theorem's `d_model ≥ 2`. Needed (by hand: `d = 1`, `d_in = 2`, width 1: the output is `sign(W_write) D` where the unit is active, the rank is `d_out`, and the formula gives `d_out + 1`) |
  | `hcard : card (hid 0) = card d` | **restricts:** the theorem has "of width at least `d_model`" |
  | `hE`, `hD` | follow at almost every `θ` from `d_in, d_out ≥ d` |
  | `hR`, `hW` | follow at almost every `θ` for width `d` (`ae_rank_E_D_read_write_of_card_eq`); with `hcard` they say that the `c_i` and the `a_i` are independent |

  The `ae_` statements have `hd`, `hdIn`, `hdOut` (the theorem's) and `hcard` (the restriction).
- **Every parameter with the four ranks, not only generic ones.** The paper's proof uses generic
  parameters in three places ("`h_1 ≠ 0` there", by a resultant; "`h_1(x_0)` is not parallel to
  `a_i`"; "two entries `h_a` and `h_b` of `h_1` have no common factor"). At width `d` with
  independent `c_i` and `a_i` none is needed. By hand, the argument of the Lean header runs:
  the final normalization (check 4) gives (18) with `β_i = ψa_i − a_i Y`; `UnitsParallel`
  applies because `C = E W_read` has independent columns and `W_write` independent rows; then the
  half of Lemma B.2 for `C` gives `X`. By a computation in exact arithmetic (`z22special.py`,
  output `z22special.out`): at 11 special parameters of width `d` with the four ranks (all
  matrices the identity for `d = 2, 3`; a permutation as `W_write`; triangular and orthogonal
  reads and writes; `E = [I; 0]`, `D = [I 0]` with `d_in, d_out > d`), ReLU and ReLU², the rank
  is the value on both batches in all 22. Outside the hypotheses, for information: `W_write` of
  rank 1 or `W_read` of rank 1 at `d = 2` gives rank 3 or 4 against 8.
- **The value and the batch.** As in check 2 (c): `funDim = v` and a batch of inputs of
  `skiplessZeroDomain ∩ noKinkRMS θ` of rank `v` give that the largest rank over the batches of
  the paper's inputs is `v`. By compiling (`ae_gain_eq_paper_relu22`): for a ReLU block of width
  `d` and `d_in, d_out ≥ d ≥ 2`, at almost every `θ`, the functional dimension on the paper's
  inputs of the residual network is that of the skipless network plus `d²`, from the library
  statements. This is "by exactly `d_model²`" for the paper's functional dimensions, at width
  `d`.
- **The computation** (`z22run.py`; output `z22_skipless.out`). One skipless block, ReLU and
  ReLU²; 20 cases per kind: `d = 2` with widths 1 to 5 and `d = 3` with widths 1 to 7 at
  `d_in = d_out = d`, and `(d, d_in, d_out, width) = (2,3,2,2), (2,3,2,3), (2,4,3,2), (2,4,3,4),
  (3,4,3,3), (3,4,3,4), (3,5,4,3), (3,5,4,5)`. Each case twice (60 digits; exact).
  - **Width exactly `d`** (6 cases per kind, 24 parameters, 48 batches): **the rank is
    `P − d² − d(d−1)/2 − 1 − s` in all.**
  - Widths above `d`, up to `2d + 1`, for information (11 cases per kind, 44 parameters, 88
    batches): the rank is the same formula in all. For `d_in = d_out = d`, both kinds:

    | `d = 2`, widths 2 to 5: value = rank | `d = 3`, widths 3 to 7: value = rank |
    |---|---|
    | 8, 11, 14, 17 (`P` = 16, 20, 24, 28) | 20, 25, 30, 35, 40 (`P` = 36, 42, …, 60) |
  - Widths below `d`, outside the theorem (3 cases per kind): the computed rank is below the
    formula (2 against 5 at `d = 2`, width 1; 3 against 10 and 12 against 15 at `d = 3`, widths 1
    and 2). For width 1 the formula is false (by hand: where the unit is active the output is
    `N_0(a_1) D`, the same at every input, so the rank of any batch is at most `d_out`). For
    `d = 3` and width 2 the computed rank is a lower bound, and I have no upper bound.
  - The residual network with ReLU and ReLU², my own recomputation (`z22_res_mlp.out`, 64
    parameters): the rank is `P − d(d−1)/2 − 1 − s` in all, as in the twenty-first audit.
  - At the same weights (`z22gain.out`): with the skip minus without it is `d²` in the 28
    parameters with ReLU or ReLU² and a width at least `d`.

### Check 7. The index rows

**Verdict: each sentence of the six rows (lines 903 to 908 at `2b9d829`) is true of the
statements, with one sentence to reword (row 907, "False for one unit"). Every public theorem of
the six files is in its row and in `checks/Axioms.lean`.** (By reading; by a script.)

- Rows 903 and 904 (`ResidualRMSZeroReGLU.lean`, `…ReGLUGeneric.lean`): true. "the step that the
  paper's proof does not write, as for ReLU": true, and the step is needed for ReGLU too (check
  2 (d)).
- Row 905 (`ResidualRMSZeroGainHomogeneous.lean`): true, with the sentence on the two notions of
  functional dimension (check 3).
- Row 906 (`SkiplessRMSZeroReadout.lean`): true.
- Row 907 (`UnitsParallel.lean`): true except "False for one unit": `UnitsParallel` as defined
  holds for one unit, because "at least two units" is a clause of the definition; see check 5.
- Row 908 (`SkiplessHomogeneousRMSZeroEq.lean`): true; "in work" at `38eefee`, "proved" at
  `b7d3bf3` and after, which is right at each commit. "at an input with no zero row of `x E`": the
  statement has this hypothesis; it is not needed (check 6).
- Names: the 24 public theorems and the two definitions are named in their rows. In
  `checks/Axioms.lean`: at `38eefee` the 13 theorems of the five proved files; at `b7d3bf3` and at
  `2b9d829` all 24.
- The paragraph of the index that lists the files "Not yet compared by such a reader" (lines 238
  to 254 at `2b9d829`) names the six files; with this report they have been compared.

---------------------------------------------------------------------------------------------------

## Part 2: the statements, file by file

Verdict words: SAME, LEAN STRONGER, LEAN WEAKER, DIFFERENT, PART, FALSE. "Paper" is the skips
paper; (iv) is Theorem B.1 (iv).

| Lean name | paper sentence or proof piece | verdict | note |
|---|---|---|---|
| **`OneBlock/ResidualRMSZeroReGLU.lean`** | | | |
| `TurnsActiveRowsGated` (definition) | none: the step from "`μ = c` wherever `w E A` and `g(w)` are linearly independent" to "derivative zero on the sphere" | not in the paper | the condition under which that step holds for a ReGLU block; needed (check 2 (d)) |
| `flatOn_noKinkGate_le_reglu_residual_rmsNorm_zero` | (iv), "The residual network": "a flat direction is the sum of a direction of the rotation and scaling of all hidden states and a direction `ψ` … Lemma B.3 … makes `ψ` a rescaling of the units", for ReGLU | SAME, at one parameter, with the conditions of the proof and the one it does not write | one inclusion; the other is in the bound `funDim_add_le_residual_gated_gate_rmsNorm_zero` |
| `funDim_reglu_oneBlock_residual_rmsNorm_zero` | "So `dim K(θ) = d_model (d_model − 1)/2 + 1 + s`", `s = 2 d_hidden` | SAME, at one parameter | Lean's `funDim` (all inputs) |
| `exists_jacobianRank_reglu_oneBlock_residual_rmsNorm_zero` | the same, in the paper's sense of "every input" | SAME | with the line above: the paper's functional dimension |
| **`OneBlock/ResidualRMSZeroReGLUGeneric.lean`** | | | |
| `ae_turnsActiveRowsGated_reglu` | none | not in the paper | the unwritten condition at almost every parameter, `d ≥ 2` |
| `ae_exists_turned_row_reglu` | none | not in the paper | follows from the line above and a nonzero gate column (compiled) |
| `ae_funDim_reglu_oneBlock_residual_rmsNorm_zero` | (iv): "For generic parameters the residual network has functional dimension `P − d_model (d_model − 1)/2 − 1 − s`", ReGLU | LEAN STRONGER | a hidden unit in place of "width at least `d_model`" |
| `ae_exists_jacobianRank_reglu_oneBlock_residual_rmsNorm_zero` | the same, on the paper's inputs | LEAN STRONGER | as above |
| **`OneBlock/ResidualRMSZeroGainHomogeneous.lean`** | | | |
| `ae_funDim_skipless_add_le_relu_oneBlock_residual_rmsNorm_zero` | (iv): "So the skip raises the functional dimension by at least `d_model²`", ReLU | LEAN STRONGER in form | on `funDim`; implies the paper's sentence (compiled) |
| `ae_funDim_skipless_add_le_reluSq_oneBlock_residual_rmsNorm_zero` | the same, ReLU² | LEAN STRONGER in form | |
| `ae_funDim_skipless_add_le_reglu_oneBlock_residual_rmsNorm_zero` | the same, ReGLU | LEAN STRONGER in form | |
| **`OneBlock/SkiplessRMSZeroReadout.lean`** | | | |
| `exists_antisymm_of_fderiv_rmsNorm_zero_mul` | (iv), "The skipless network: equality": "`η_D = −Y D` with `Y` antisymmetric, since `h_1` takes all values in an open set, and `D_θ h_1 η = h_1 Y + μ h_1`" | SAME | a lemma on `(h, D) ↦ N_0(h) D`; also gives `μ = ⟨h_1, D_θ h_1 η⟩/⟨h_1, h_1⟩` |
| **`OneBlock/UnitsParallel.lean`** | | | |
| `UnitsParallel` (definition) | equation (18), "The kinks stay", "One scale" | PART | independent `c_i` and independent `a_i` only (width exactly `d`); there, every such `c`, `a` |
| `relu_unitsParallel` | the two steps for `k = 1` | PART | as above |
| `reluSq_unitsParallel` | the two steps for `k = 2` | PART | as above |
| **`OneBlock/SkiplessHomogeneousRMSZeroEq.lean`** | | | |
| `eval_skipless_rmsNorm_zero_of_rowHomogeneous` | (iv): "Its normalization before the block drops out" | SAME | the hypothesis `hx` is not needed (compiled) |
| `flatOn_le_mlp_rescale_skipless_rmsNorm_zero` | "The skipless network: equality" with "Counting" | PART | width exactly `d`; there at every parameter with the four ranks |
| `funDim_mlp_oneBlock_rescale_skipless_rmsNorm_zero` | "So `dim K(θ) = d_model² + d_model (d_model − 1)/2 + 1 + s` for ReLU and ReLU² blocks" | PART | width exactly `d` |
| `exists_jacobianRank_mlp_oneBlock_rescale_skipless_rmsNorm_zero` | the same, on the paper's inputs | PART | width exactly `d` |
| `ae_rank_E_D_read_write_of_card_eq` | "For generic parameters `E`, `D`, `W_read` and `W_write` have rank `d_model`" (part (i)) | SAME, for width `d` | |
| `ae_funDim_relu_oneBlock_skipless_rmsNorm_zero`, `ae_exists_jacobianRank_relu_oneBlock_skipless_rmsNorm_zero` | (iv): "the skipless network at most `P − d_model² − d_model (d_model − 1)/2 − 1 − s`, with equality for ReLU and ReLU² blocks", ReLU | PART | width exactly `d`; the theorem: width at least `d_model` |
| `ae_funDim_reluSq_oneBlock_skipless_rmsNorm_zero`, `ae_exists_jacobianRank_reluSq_oneBlock_skipless_rmsNorm_zero` | the same, ReLU² | PART | as above |
| `ae_funDim_relu_oneBlock_residual_rmsNorm_zero_eq_add`, `ae_funDim_reluSq_oneBlock_residual_rmsNorm_zero_eq_add` | (iv): "and by exactly `d_model²` for ReLU and ReLU² blocks" | PART | width exactly `d` |

Not stated in the six files (said in their headers): the equality and "by exactly `d_model²`"
for blocks wider than `d`; the last sentence of (iv) ("The redundancy is then that of the
symmetries …") as a statement of its own.

---------------------------------------------------------------------------------------------------

## What the authors of the papers should know

False, vacuous, drifted or misdescribed:

1. **Nothing in the Lean statements is false, vacuous or drifted.** One description is loose: the
   header of `OneBlock/UnitsParallel.lean` and row 907 of the index say that the statement is
   false for one unit; as defined it holds for one unit, and the statement without the clause "at
   least two units" is the one that fails (check 5).

Conditions and steps that the paper's proof needs and does not write:

2. **Part (iv), "The residual network", for ReGLU: the same unwritten step as for ReLU, and it is
   needed.** The case `ε = 0` of part (iii) gives the zero derivative of `B` only at the rows
   where `w E` and `g(w)` are linearly independent ("The constant terms then give `μ = c`
   wherever `w E A` and `g(w)` are linearly independent"), and for a block that is not analytic
   the step to all rows needs that these rows are dense among the rows with an active gate. At
   the ReGLU parameter of check 2 (d) every condition that the proof names holds (`E`, `D` of
   rank `d`; the hypotheses of Lemma B.3 for ReGLU), the block is `l(u) u` on two opposite
   sectors, and the functional dimension is 29 against `P − d(d−1)/2 − 1 − s = 30`. So the
   sentence "a flat direction is the sum of a direction of the rotation and scaling of all hidden
   states and a direction `ψ` of the weights of the block along which `B` has derivative zero on
   the sphere" is not true at every parameter with the conditions named. The theorem is for
   generic parameters and stands: Lean proves that the missing condition holds at almost every
   parameter (`ae_turnsActiveRowsGated_reglu`). What the proof does not write: for generic
   parameters, the rows `u` at which `u` and `B(u)` are linearly independent are dense among the
   rows with an active gate.
3. **The equality for the skipless network is formalized for width exactly `d_model` only.** The
   theorem says "of width at least `d_model`". For wider blocks the paper's proof uses a
   resultant ("`h_1 ≠ 0` there") and two entries of `h_1` without a common factor; none of this
   is in Lean. My computations agree with the paper there (44 parameters with widths `d + 1` to
   `2d + 1`, ReLU and ReLU²: the rank is the value; 32 exact linear systems for the two steps
   with more units than coordinates: the solutions are the `q + 1` named ones), but they are
   computations at random weights, not a proof.
4. **At width `d_model` no genericity beyond the four ranks is needed.** Lean proves the equality
   at every parameter at which `E`, `D`, `W_read`, `W_write` have rank `d_model`; the three
   generic conditions of the paper's proof (the resultant; "`h_1(x_0)` is not parallel to `a_i`";
   "no common factor") are not used. The computed ranks at 11 special parameters agree.
5. **"The kinks stay" needs a second unit.** The step fixes "a point `x_0` … at which another
   unit is active"; with one unit the conclusion `ψc_i = λ_i c_i` fails (compiled
   counterexample). The theorem has width at least `d_model ≥ 2`, so nothing is missing; the
   proof does not say where the width is used at this point.
6. **`d_model ≥ 2` is needed for the skipless equality** (by hand: `d = 1`, `d_in = 2`, width 1:
   the rank is `d_out`, the formula gives `d_out + 1`). It is a hypothesis of the theorem.
7. **Below the theorem's width the skipless formula fails**: for width 1 the functional dimension
   is at most `d_out` (by hand; computed: 2 against 5 for `d = 2`, 3 against 10 for `d = 3`), and
   for `d = 3` and width 2 the computed rank is 12 against 15 (a lower bound). The residual value
   holds for every width with a hidden unit (Lean; computed for ReGLU at widths below `d`). So
   "of width at least `d_model`" is used by the skipless half of (iv) and not by the residual
   half.

For information:

8. "Its normalization before the block drops out" holds at every input with Lean's `N_0(0) = 0`;
   the hypothesis that no row of `x E` vanishes is not needed for this step.
9. One skipless ReGLU block of width at least `d`: in 18 computed parameters (`d = 2`, widths 2
   to 5; `d = 3`, widths 3 to 7; 60 digits and exact) the rank equals the bound
   `P − d² − d(d−1)/2 − 1 − 2 d_hidden` (`z22_reglu_skipless.out`), and with the skip minus
   without it is `d²` in the 14 ReGLU parameters of `z22gain.out` with a width at least `d`. The
   theorem claims "at most" for ReGLU, and equality only for ReLU and ReLU². This agrees with the
   paper's own check at `ε = 10⁻¹²` (S lines 3277 to 3279).

---------------------------------------------------------------------------------------------------

## Corrections for `STATEMENTS.md` (line numbers of `2b9d829`) and for one file header

1. **Row 907 (`OneBlock/UnitsParallel.lean`), "False for one unit."** Write: "As defined it holds
   for fewer than two units (the clause `2 ≤ Fintype.card q` is in the definition); without the
   clause it is false for one unit when the input has at least two coordinates, and true with
   one coordinate." The same in the header of `OneBlock/UnitsParallel.lean` ("With one unit the
   statement is false (`ψc` is then arbitrary)").
2. **Rows 903 and 904 (ReGLU).** Add: "The condition `TurnsActiveRowsGated` is needed: at a
   parameter with six hidden units, `d = 2`, that has `OneBlockGenericReGLURMS` and a turned row,
   the rank on the paper's inputs is 29 against 30 (twenty-second audit, part A)."
3. **Row 908 (`OneBlock/SkiplessHomogeneousRMSZeroEq.lean`), "at an input with no zero row of
   `x E` the network is `N_0(f(x E W_read) W_write) D`".** Add "(the hypothesis is not needed
   with Lean's `N_0(0) = 0`)", or drop the hypothesis `hx` from
   `eval_skipless_rmsNorm_zero_of_rowHomogeneous`. The row could also say that the pointwise
   statements hold at every parameter with the four ranks, and that `k ≥ 1` and `σ(1) ≠ 0` are
   what makes `h_1` fill an open set.
4. **Row 907, the numeric check.** Add: "exact rational check by the twenty-second reader: 48
   systems with independent `c`, `a` and two to five units, the solutions have dimension
   `q + 1`."
5. **The paragraph "Not yet compared by such a reader"** (lines 238 to 254 at `2b9d829`): take
   out `OneBlock/ResidualRMSZeroReGLU.lean`, `OneBlock/ResidualRMSZeroReGLUGeneric.lean`,
   `OneBlock/ResidualRMSZeroGainHomogeneous.lean`, `OneBlock/SkiplessRMSZeroReadout.lean`,
   `OneBlock/UnitsParallel.lean`, `OneBlock/SkiplessHomogeneousRMSZeroEq.lean`, and name this
   report.
6. No row of the six needs a change of its list of names or of its status.

---------------------------------------------------------------------------------------------------

## What I could not check

- The proofs: I did not read them, apart from the short proofs of the `ae_` statements. I ran no
  `lake build`; the axioms are from compiling my files against the build of `/home/claude/lp/lean`.
- Lean's `funDim` (all inputs) at the ReGLU parameter of check 2 (d): I computed the rank on the
  paper's inputs only.
- The equality for the skipless network at widths above `d`: computed at 44 parameters, not
  proved, and not stated in Lean.
- The skipless network narrower than `d` with more than one hidden unit (`d = 3`, width 2): the
  computed rank is a lower bound and I have no upper bound there.
- Sizes: the network ranks are for `d = 2, 3` only; widths up to `2d + 1`; `d_in`, `d_out` up to
  `d + 2`.
- The paper's argument for wider blocks (the resultant; the common factor): not checked beyond
  the computations named.
- The dimension paper: not compared; the six files do not cite it.
