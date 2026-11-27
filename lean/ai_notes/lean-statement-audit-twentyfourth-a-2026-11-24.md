STATUS: complete

# Twenty-fourth audit, part A, of Lean statements against the papers: S Theorem B.1 (iii) for `ε = 0`, the equality for ReLU, ReLU² and ReGLU blocks with a full learned skip (24 November 2026)

An independent reader compared the statements of five files of the library `SkipsLean` with the
skips paper (`<scratchpad>/skips.txt`: Theorem B.1 at lines 2319 to 2347, the proof of part (iii)
from line 2801, equation (17) at line 2830, "The case `ε = 0`" at lines 2862 to 2889, Lemma B.3 at
line 2460). The reader did not write these statements; the writer is called "the coordinator"
below. The statements were audited, not the proofs. The rules of work are those of the
twenty-first audit, part A; the files that these five build on were compared in the twenty-third
audit, whose checks are not repeated here.

## Commits and files

- Branch of `/home/claude/lp`. I started at commit `1b0733f` (23:26 UTC). Within the first minute
  the branch moved to `cbb77d0`, which brought the proofs of the three theorems of
  `OneBlock/LearnedSkipRMSZeroReGLU.lean`; I read the five files at `cbb77d0` (a copy is in
  `/home/claude/audit24a/snap1/`). The branch moved again while I worked (`e968374`, `5adbab6` at
  23:46, `d51c1e9` at 23:52); the five files are byte for byte the same at `d51c1e9`.
- `sorry`: at `1b0733f`, three in `OneBlock/LearnedSkipRMSZeroReGLU.lean`. At `cbb77d0` and after,
  none in the five files. The definition and the three statements of that file are the same text
  at `1b0733f` and at `cbb77d0` (compared by a script).
- The 22 public theorems of the five files depend on `propext`, `Classical.choice`, `Quot.sound`
  only (compiled, `Chk1.lean`, against the build in `/home/claude/lp/lean`, whose object files of
  the five files are from 23:03 to 23:27, after their sources).
- My files are in `/home/claude/audit24a/`: `Chk1.lean`, `Chk2.lean` (compiled with
  `lake env lean`, nothing written in the repository) with `Chk1.out`, `Chk2.out`; `c23.py` (the
  core of the reader of the twenty-third audit, which I read in full and reuse: ball arithmetic of
  `python-flint` at 60 digits, exact derivatives by forward mode, rank by elimination with
  complete pivoting where a pivot is taken only if its ball does not contain `0`); my own
  `z24flat.py`, `z24turn.py`, `z24turn_hyp.py`, `z24sizes.py`, `z24units.py`,
  `z24units_replay.py`, `z24units_opp.py` and their outputs. No computation took more than two
  minutes.

## Short answer

**Nothing false, nothing vacuous and nothing drifted was found in the five files.**

- All 15 `ae_` statements are at almost every pair (weights, skip), for every Haar measure on the
  pairs; each was compiled at `Measure.addHaar` in a small size.
- `funDimLearned` with the batch of the paper's inputs is the paper's functional dimension of the
  network with the learned skip, and `funDim` of the residual network is the paper's value there:
  compiled for the three kinds (`Chk2.lean`): at almost every `(θ, A)`, the functional dimension
  on the paper's inputs with the skip equals that of the residual network on the paper's inputs
  plus `d(d+1)/2 − 1`. This is the paper's "with equality for ReLU, ReLU² and ReGLU blocks", for
  a full skip.
- The flat directions: in 108 computed cases (ReLU, ReLU², ReGLU; `d = 2, 3`) the directions that
  are flat on the batch are exactly the span of the stated ones, of dimension
  `(d(d−1) + 2) + s`.
- The condition that the paper does not state is needed, for the learned skip too, and for ReGLU:
  one ReLU and one ReGLU parameter, with an invertible skip that is not the identity, meet every
  other hypothesis, and the rank there is one below the count (25 against 26; 31 against 32).
- `reglu_unitsRescaleSphere` is true in 60 exact systems (the solutions have dimension `2q + 1`),
  and each hypothesis is needed (an exact counterexample for each).
- Of the hypotheses on the sizes, `d ≥ 2`, `d_in ≥ d` and the hidden unit are needed. In the 30
  cases computed with `d_out < d` no value changed.

---------------------------------------------------------------------------------------------------

## Part 1: the checks

### Check 1. Generic means almost every parameter, for every Haar measure

**Verdict: yes, in all 15 `ae_` statements (10 in `…RescaleGeneric.lean`, 5 in
`…ReGLUGeneric.lean`). None says "there is a parameter" or names an open set.** (By reading; all
15 by compiling an instance, `Chk1.lean`.)

- The Lean text of one statement of each form:

  ```
  theorem ae_turnsActiveRowsSkip_relu
      (μ : Measure (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut
        × (Fin 1 → Matrix d d ℝ)))
      [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) :
      ∀ᵐ p ∂μ, TurnsActiveRowsSkip p.1 (p.2 0)

  theorem ae_funDimLearned_relu_oneBlock_rmsNorm_zero [Nonempty (hid 0)]
      (μ : Measure (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut
        × (Fin 1 → Matrix d d ℝ)))
      [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
      (hdOut : Fintype.card d ≤ Fintype.card dOut) :
      ∀ᵐ p ∂μ, funDimLearned (Arch.mlp relu (rmsNorm 0) hid) p
          + ((Fintype.card d * (Fintype.card d - 1) + 2) + Fintype.card (hid 0))
        = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut)
          + Fintype.card d ^ 2

  theorem ae_funDimLearned_reglu_oneBlock_rmsNorm_zero_eq_residual_add [Nonempty (hid 0)]
      (μ : Measure (Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut
        × (Fin 1 → Matrix d d ℝ)))
      [hμ : μ.IsAddHaarMeasure] (hd : …) (hdIn : …) (hdOut : …) :
      ∀ᵐ p ∂μ, funDimLearned (Arch.gated relu (rmsNorm 0) hid) p
        = funDim (Arch.gated relu (rmsNorm 0) hid) 1 p.1
          + (Fintype.card d * (Fintype.card d + 1) / 2 - 1)
  ```
- In every one of the 15, `μ` is any measure on `Params × (Fin 1 → Matrix d d ℝ)` with
  `[μ.IsAddHaarMeasure]`: Lebesgue measure on `ℝ^(P + d²)` up to a factor. The paper's generic
  parameters of a network with a learned skip are the generic pairs `(θ, A)` (the proof counts
  the entries of `A` as parameters and says "`A` is invertible for generic parameters"; twenty-third
  audit, check 1).
- `Fintype`: `T`, `d`, `dIn`, `dOut` in the `variable` lines; `hid ℓ` by `[∀ ℓ, Fintype (hid ℓ)]`.
  The six statements on the conditions omit `[Fintype T]`: `T` indexes the tokens, not an entry of
  a weight, so every index type of the weights and of the skip has `Fintype`.
- Compiled at `Measure.addHaar`, each with the numbers written out: ReLU (`d = d_in = d_out = 2`,
  three units), ReLU² (`d = 3`, `d_out = 4`, one unit), ReGLU (`d = 2`, three units); for each:
  the condition, the turned row, the value (`funDimLearned + 7 = P + 4`, `+ 9 = P + 9`,
  `+ 10 = P + 4`), the batch, and the equality (`funDimLearned = funDim + 2`, `+ 5`, `+ 2`). All
  15 depend on the three standard axioms. As in the twenty-third audit, `Measure.addHaar` on the
  product needs two instances given by hand (`LocallyCompactSpace` and `BorelSpace` of
  `Fin 1 → Matrix d d ℝ`).

### Check 2. The functional dimension

**Verdict: the two statements together are the paper's functional dimension of the network with
the learned skip; the right side of `…_eq_residual_add` is the paper's value for the residual
network; the equality is the paper's sentence for a full skip. All three points were compiled.
The theorem names `d ≥ 2`, `d_in ≥ d`, `d_out ≥ d`; Lean asks these and a hidden unit, and no
width. `d ≥ 2`, `d_in ≥ d` and the hidden unit are needed; I found no case in which `d_out ≥ d`
is.** (By reading; by compiling, `Chk2.lean`; the sizes by computation, `z24sizes.py`, and by
hand.)

- **Lean's `funDimLearned`.** `funDimSkips A id p` is the largest rank of
  `fderiv (fun p' => fun i => evalSkips A id p' (X i)) p` over all finite batches `X`. Mathlib's
  derivative of a map that is not differentiable is `0`, so a batch with one input at which the
  output is not differentiable in `(θ, A)` counts as rank `0`: the supremum is over the batches of
  inputs at which the output is differentiable. This set contains the paper's inputs (no
  normalized row vanishes, no unit at its kink) and more (a ReLU² unit at its kink; the input
  `0`), so `funDimLearned` is at least the paper's value, and the second statement gives a batch
  inside the paper's inputs with the rank `funDimLearned`:

  ```
  theorem ae_exists_jacobianRankSkips_relu_oneBlock_rmsNorm_zero [Nonempty (hid 0)] (μ : …) … :
      ∀ᵐ p ∂μ, ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ),
        (∀ i, X i ∈ learnedZeroDomain (Arch.mlp relu (rmsNorm 0) hid) p.1 p.2 ∩ noKinkRMS p.1) ∧
        jacobianRankSkips (Arch.mlp relu (rmsNorm 0) hid)
            (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) X p
            + ((Fintype.card d * (Fintype.card d - 1) + 2) + Fintype.card (hid 0))
          = Module.finrank ℝ (Params …) + Fintype.card d ^ 2
  ```
- **The paper's inputs.** "For the ReLU-type activations […] 'every input' means every such
  input [no hidden unit at its kink]. With `ε = 0`, it also excludes the inputs at which a state
  that is normalized vanishes" (lines 2365 to 2371). `learnedZeroDomain A θ R`: no row of `x E`
  and no row of `x E A + f(N_0(x E) W_read) W_write` is zero: the two states that are normalized.
  `noKinkRMS θ`: no entry of `x E W_read` is zero; the block reads `N_0(x E) W_read`, a positive
  multiple of it row by row, so these are the kinks. `noKinkGateRMS θ`: the same for the gate
  columns; the kink of a ReGLU unit is that of its gate.
- **Compiled** (`relu_paper24`, `reluSq_paper24`, `reglu_paper24`; standard axioms only): for
  `d_in, d_out ≥ d ≥ 2` and a block with a hidden unit, at almost every `(θ, A)` for every Haar
  measure,
  - `funDimSkipsOn … p (learnedZeroDomain … ∩ noKinkRMS p.1) = funDimLearned … p`,
  - `funDimOn … 1 p.1 (residualZeroDomain … ∩ noKinkRMS p.1) = funDim … 1 p.1`,
  - `funDimSkipsOn … (the paper's inputs with the skip) = funDimOn … (the paper's inputs of the
    residual network) + (d(d+1)/2 − 1)`
  (`noKinkGateRMS` for ReGLU). The first uses the value and the batch of the files of this audit.
  The second uses the statements that show that Lean's `funDim` of the residual network is the
  paper's value: `ae_funDim_relu_oneBlock_residual_rmsNorm_zero` with
  `ae_exists_jacobianRank_relu_oneBlock_residual_rmsNorm_zero`, the same pair for `reluSq`
  (`OneBlock/ResidualRMSZeroRescaleGeneric.lean`, twenty-first audit), and
  `ae_funDim_reglu_oneBlock_residual_rmsNorm_zero` with
  `ae_exists_jacobianRank_reglu_oneBlock_residual_rmsNorm_zero`
  (`OneBlock/ResidualRMSZeroReGLUGeneric.lean`).
- **The sentence.** "For `ε = 0` it exceeds that of the residual network with `ε = 0` by at most
  `d_model (d_model + 1)/2 − 1`, with equality for ReLU, ReLU² and ReGLU blocks." Lean:
  `funDimLearned A p = funDim A 1 p.1 + (d(d+1)/2 − 1)` at almost every `(θ, A)`, the residual
  network at the same weights `θ`. A set of weights of measure zero is a set of pairs of measure
  zero, so this is the comparison of the two generic values. The count: `P + d² − (d(d−1) + 2) − s`
  minus `P − d(d−1)/2 − 1 − s` is `d² − d(d−1)/2 − 1 = d(d+1)/2 − 1`. The values are written
  with sums, so no natural-number subtraction truncates; `d(d+1)/2 − 1` is exact for `d ≥ 2`. The
  paper's sentence is for a learned skip "full or upper triangular"; these files have the full
  skip (PART), the triangular one is in `OneBlock/LearnedSkipTriangularRMSZeroRescale.lean`, which
  I did not read.
- **The hypotheses on the sizes.**

  | hypothesis | the paper | needed? | how |
  |---|---|---|---|
  | `d ≥ 2` | "Let `d_model ≥ 2`" | yes, for the values | by hand: for `d = 1`, `N_0` is the sign, the output is `± D` and does not move with the other weights or the skip, so both functional dimensions are `d_out`, while both formulas give `P − 1 − s`, which is larger; the difference `0 = d(d+1)/2 − 1` happens to hold |
  | `d_in ≥ d` | "the input and output dimensions be at least `d_model`" | yes | computed, 30 cases: no rank reached a value; the difference was `0` for `d_in = 1` (`d = 2, 3`) and `2`, not `5`, for `d = 3`, `d_in = 2`. By hand for `d = 2`, `d_in = 1`, one ReLU unit: the output depends on the weights and the skip only through `e A`, the two values of the block and `D` (10 numbers), on which `CO(2)` acts, so the rank is at most 8, below the value 9 |
  | `d_out ≥ d` | the same sentence | not in what I computed | 30 cases with `d_out = 1, 2 < d` (`d = 2, 3`, the three kinds, widths 1 to 4, two weights each): the rank with the skip is `P + d² − (d(d−1) + 2) − s`, that of the residual network `P − d(d−1)/2 − 1 − s`, the difference `d(d+1)/2 − 1`, in all 30. The bound "at most" is proved in Lean without the rank of `D` (twenty-third audit, check 3); the Lean proof of the equality uses `D` of rank `d` |
  | a hidden unit (`[Nonempty (hid 0)]`) | a block | yes | computed, 8 cases with no unit (`d = 2, 3`): rank `P − d(d−1)/2 − 1` with the skip and for the residual network, difference `0`, against the Lean value `P + d² − (d(d−1) + 2)`. By hand: without a block the network is `N_0(x E A) D`, and `A` only renames `E` |
  | a width | part (iii) asks none | not asked | the statements hold for one unit (computed for width 1) |

  The ranks are certified lower bounds on two batches each (up to `3P/d_out` inputs from every
  pattern of active units or gates); entries left after the pivots below `10⁻⁴⁸`. Outputs:
  `z24sizes_din.out`, `z24sizes_dout.out`, `z24sizes_nounit.out`, `z24sizes_ok.out` (nine cases
  with all hypotheses, as a control: every rank is the value).

### Check 3. The flat directions at one parameter

**Verdict: the conclusion is the paper's description of the flat directions for `ε = 0`
(`η^rot` with the two scalings, and the rescalings `K_B`), with the right signs and factors, and
the count is the paper's with `s = d_hidden` for ReLU, ReLU² and `s = 2 d_hidden` for ReGLU. It
holds in all 108 computed cases.** (By reading and by hand; by computation, `z24flat.py`.)

- The Lean text:

  ```
  theorem flatSkipsOn_noKink_le_mlp_rescale_learned_rmsNorm_zero {k : ℕ}
      (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
      (hhom : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
      (hU : UnitsRescaleSphere σ σ' k d d (hid 0))
      (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
      (hθ : OneBlockGenericRMS θ) (hd : 2 ≤ Fintype.card d)
      (R : Fin 1 → Matrix d d ℝ) (hR : IsUnit (R 0).det)
      (hturn : TurnsActiveRowsSkip θ (R 0))
      (hw : ∃ v : d → ℝ, (∀ i, (v ᵥ* θ.read 0) i ≠ 0) ∧
        LinearIndependent ℝ ![v ᵥ* R 0, vanillaBlock σ (θ.read 0) (θ.write 0) v])
      (η : Params …) (ρ : Fin 1 → Matrix d d ℝ)
      (hη : (η, ρ) ∈ flatSkipsOn (Arch.mlp σ (rmsNorm 0) hid)
        (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) (θ, R)
        (learnedZeroDomain (Arch.mlp σ (rmsNorm 0) hid) θ R ∩ noKinkRMS θ)) :
      ∃ (X₀ Y : Matrix d d ℝ) (c₀ c₁ : ℝ) (α : ∀ ℓ, hid ℓ → ℝ), X₀ᵀ = -X₀ ∧ Yᵀ = -Y ∧
        η = cobDir θ ![X₀, Y] + scaleDir θ ![c₀, c₁] + rescaleDirMlp k θ α ∧
        ρ 0 = R 0 * (Y + c₁ • 1) - (X₀ + c₀ • 1) * R 0

  theorem flatSkipsOn_noKinkGate_le_reglu_learned_rmsNorm_zero
      (θ : Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut)
      (hθ : OneBlockGenericReGLURMS θ) (hd : …) (R : …) (hR : …)
      (hturn : TurnsActiveRowsGatedSkip θ (R 0)) (hw : …) (η : …) (ρ : …) (hη : … ∩ noKinkGateRMS θ)) :
      ∃ (X₀ Y : Matrix d d ℝ) (c₀ c₁ : ℝ) (α β : ∀ ℓ, hid ℓ → ℝ), X₀ᵀ = -X₀ ∧ Yᵀ = -Y ∧
        η = cobDir θ ![X₀, Y] + scaleDir θ ![c₀, c₁] + rescaleDir θ α + rescaleDirGate 1 θ β ∧
        ρ 0 = R 0 * (Y + c₁ • 1) - (X₀ + c₀ • 1) * R 0
  ```
- What each direction does (from the definitions; `A = R 0`, `η_A = ρ 0`):

  | direction | `E` | `W_read` | `W_write` | `D` | `A` |
  |---|---|---|---|---|---|
  | `cobDir θ ![X₀, Y]` | `E X₀` | `−X₀ W_read` | `W_write Y` | `−Y D` | `A Y − X₀ A` |
  | `scaleDir θ ![c₀, c₁]` | `c₀ E` | `0` | `c₁ W_write` | `0` | `(c₁ − c₀) A` |
  | `rescaleDirMlp k θ α` | `0` | column `i` times `α_i` | row `i` times `−k α_i` | `0` | `0` |
  | `rescaleDir θ α` (ReGLU, values) | `0` | value column `i` times `−α_i` | row `i` times `α_i` | `0` | `0` |
  | `rescaleDirGate 1 θ β` (ReGLU, gates) | `0` | gate column `i` times `β_i` | row `i` times `−β_i` | `0` | `0` |

  The last column is the stated `ρ 0 = A (Y + c₁ I) − (X₀ + c₀ I) A` split into its two parts.
- Against the paper.
  - Step 4: "They define a flat direction `η^rot` with the entries `E X_a` at `E`, `A Y − X_a A`
    at `A`, `−X_a W_read` at `W_read`, `W_write Y` at `W_write` and `−Y D` at `D`." The first row,
    entry by entry, with Lean's `X₀` for the paper's `X_a`. (A clash of names: the paper's `X_0`
    is the symmetric part of trace zero, which the proof shows to vanish; Lean's `X₀` is the
    antisymmetric `X_a`.)
  - "The case `ε = 0`": "the scalings of `h_0` and `h_1` are symmetries too, since
    `N_ε(c h) = N_ε(h)` for `c > 0`"; "`η_E A + E η_A = E A (Y + c I)`"; "Steps 3 and 4 run with
    `Y + c I` in place of `Y` and with `X_s = c_0 I + X_0` […]; the scalings, with the derivatives
    `c_0` at `h_0` and `c` at `h_1`, join the rotations in `η^rot`". By hand: `h_0 ↦ (1 + τ c₀) h_0`
    is `E ↦ (1 + τ c₀) E`; the block reads `N_0(h_0)`, which does not move, so the read does not
    move; `h_1 = h_0 A + g ↦ (1 + τ c₁) h_1` needs `A ↦ (1 + τ (c₁ − c₀)) A` and
    `W_write ↦ (1 + τ c₁) W_write`; `D` does not move, since `N_0((1 + τ c₁) h_1) = N_0(h_1)`. This
    is the second row. With the paper's formulas, `η_E = E X`, `X = X_a + c_0 I`, and
    `η_A = A (Y + c I) − X A`: Lean's `c₀` is the paper's `c_0`, Lean's `c₁` the paper's `c`.
  - `K_B`: "a rescaling of the units by numbers `λ_i` […] scales column `i` of `W_read` […] by
    `λ_i` and row `i` of `W_write` by `−λ_i` for ReLU, by `−2λ_i` for ReLU²" (line 2604): the third
    row with `k = 1, 2`. Lemma B.3 for ReGLU: "`ψ_{c_i} = λ_i c_i`, `ψ_{e_i} = −α_i e_i` and
    `ψ_{a_i} = (α_i − λ_i) a_i`": rows four and five with `λ_i = β_i`.
  - The read under the scaling of `h_0`. In the paper, `ψ` is "the entries of `η′` at the weights
    of the block plus" `X_s W_read`, and (17) is `∂_ψ B(n) = q(n) DB(n) n`. For `X_s = c_0 I`,
    `q = c_0` on the sphere and the right side is `k c_0 B(n)`: `ψ = (c_0 W_read, 0)` solves it,
    so `η′` is `0` at the block. This is why `scaleDir` has `0` at the read, and it is the term
    `k c₀ a_i`, resp. `2 c₀ a_i`, of `UnitsRescaleSphere` and `reglu_unitsRescaleSphere`
    (`α_i = λ_i − c₀` for an MLP unit; for ReGLU `β_i^{gate} = λ_i − c₀`, `α_i = c₀ − μ_i`, and
    the write is `(α_i − β_i^{gate}) a_i = (2c₀ − λ_i − μ_i) a_i`).
- The count. Two rotations (`d(d−1)/2` each), two scalings, `s` rescalings:
  `(d(d−1) + 2) + s` against `P + d²`. The paper: "at least `d_model (d_model − 1) + 2` […]
  dimensions besides `K_B`"; `s = d_hidden` for ReLU and ReLU², and for ReGLU the gate and the
  value of each unit ("in ReGLU, its gate", line 1542; "`s − 2` for ReGLU", line 2296), so
  `2 d_hidden`. Lean: `… + ((card d * (card d - 1) + 2) + card (hid 0))`, resp.
  `+ 2 * card (hid 0)`. The same.
- **Computed** (`z24flat.py`; outputs `z24flat_*.out`). One block, one token, a full learned skip
  (a random matrix of certified rank `d`), `ε = 0`; `d = 2, 3`; `(d_in, d_out) = (d, d)` and
  `(d + 1, d + 1)`; two random weights at each size. ReLU and ReLU²: widths `1, d, d + 1, 5, 7`
  (40 cases each). ReGLU: widths `1, 2, 3, 5` for `d = 2` and `1, 3, 4` for `d = 3` (28 cases).
  The batch: `2P/d_out` inputs from every pattern of active units, resp. gates, found among 20000
  directions of `h_0` (28 to 1837 inputs, 2 to 43 patterns). For each case:
  (a) the Jacobian in the weights and the skip has the certified rank `P + d² − ((d(d−1) + 2) + s)`;
  (b) the stated directions, written as vectors from the table above (one for each antisymmetric
  unit matrix at `h_0` and at `h_1`, the two scalings, one for each `α_i`, and for ReGLU one for
  each `β_i`), have the certified rank `(d(d−1) + 2) + s`;
  (c) the Jacobian times each stated direction is zero to `1.4·10⁻⁵⁴` (relative);
  (d) a basis of the kernel of the Jacobian on the batch (what is left after the certified
  pivots, below `1.6·10⁻⁴⁶`, taken as zero) lies in the span of the stated directions: nothing
  above `2·10⁻⁵⁰` is left after reduction by them.

  | block | cases | kernel on the batch | `(d(d−1) + 2) + s` | every kernel vector of the stated form |
  |---|---|---|---|---|
  | ReLU | 40 | 5 to 15 | the same in all | yes in all |
  | ReLU² | 40 | 5 to 15 | the same in all | yes in all |
  | ReGLU | 28 | 6 to 16 | the same in all | yes in all |

  The smallest pivot is `10⁻⁸` of the largest. By (a) the kernel has at most the count as its
  dimension, certified; by (b) and (c) it contains the stated directions; so in these 108 cases
  the directions that are flat on the batch are exactly the stated ones, and every direction
  that is flat on all the paper's inputs is among them. In 11 cases, all with `d = 3` and width
  4 to 7, some pattern was seen once or twice among the 20000 directions and gave one or two
  inputs; the counts were reached all the same.

### Check 4. The condition the paper does not state

**Verdict: `TurnsActiveRowsSkip` and `TurnsActiveRowsGatedSkip` are what the step from "where
independent" to "at all rows off the kinks with an active unit" uses; they are sufficient and
not necessary. A condition of this kind is needed: at one ReLU and at one ReGLU parameter with an
invertible skip `A ≠ I`, every other hypothesis holds, the condition fails, and the rank is one
below the count. The three `ae_` statements are at almost every pair `(θ, A)`.** (By reading and
by hand; by computation, `z24turn.py`, `z24turn_hyp.py`.)

- The Lean text:

  ```
  def TurnsActiveRowsSkip (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
      (S : Matrix d d ℝ) : Prop :=
    ∀ v : d → ℝ, (∀ i, (v ᵥ* θ.read 0) i ≠ 0) → (∃ i, σ ((v ᵥ* θ.read 0) i) ≠ 0) →
      v ∈ closure {u : d → ℝ |
        LinearIndependent ℝ ![u ᵥ* S, vanillaBlock σ (θ.read 0) (θ.write 0) u]}

  def TurnsActiveRowsGatedSkip
      (θ : Params (Arch.gated (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) (S : Matrix d d ℝ) :
      Prop :=
    ∀ v : d → ℝ, (∀ i, (v ᵥ* θ.read 0) (Sum.inl i) ≠ 0) →
      (∃ i, σ ((v ᵥ* θ.read 0) (Sum.inl i)) ≠ 0) →
      v ∈ closure {u : d → ℝ | LinearIndependent ℝ ![u ᵥ* S, gatedBlock σ
        ((θ.read 0).submatrix id Sum.inl) ((θ.read 0).submatrix id Sum.inr) (θ.write 0) u]}
  ```
- Against the proof. "The constant terms then give `μ = c` wherever `w E A` and `g(w)` are
  linearly independent. Steps 3 and 4 run with `Y + c I` in place of `Y` […] and (17) holds with
  `X_0` in place of `X_s` on the sphere." Steps 1 to 3 (the statement compared in the twenty-third
  audit, check 6) give `D_θ g η = g(x)(Y + c I)` at the inputs off the kinks at which `x E A` and
  `g(x)` are independent; `g(x) = B(N_0(x E))` is a positive multiple of `B(x E)` by homogeneity,
  so this is the independence of `u A` and `B(u)` at the row `u = x E`, which is Lean's set. Off
  the kinks both sides are continuous in `u`, so the identity passes to every row off the kinks
  that is a limit of such rows. The definition asks this of every row off the kinks with an
  active unit. The two exceptions are right, as for the residual network (twenty-first audit,
  check 2): at a row with no active unit the block and its derivative vanish on a neighbourhood,
  so the identity is `0 = 0` there and no nearby row is turned; a row with a unit at its kink is
  not one of the paper's inputs. For a gated block "active" is "the gate is active"
  (`σ` of the gate is not `0`): where no gate is active the block vanishes on a neighbourhood.
  For `S = 1` the definition is `TurnsActiveRows` (compiled, `turns_one_iff24`).
- "And no more"? It is sufficient and it is the natural form; it is not necessary for the
  conclusion at every parameter: at the parameters (A′) and (R1) below it fails and the rank is
  the count.
- **Is it needed: yes.** All parameters have `d = d_in = d_out = 2`, one token,
  `E = [[2, 1], [1, 3]]`, `D = [[1, −2], [3, 1]]`, the skip `A = [[2, 1], [0, 1]]` (determinants
  5, 7, 2; `A` is not a multiple of an orthogonal matrix). Each is a parameter of the residual
  case with every row of `W_write` multiplied by `A` on the right: then `B(u)` becomes `B(u) A`,
  and `u A`, `B(u) A` are independent exactly when `u`, `B(u)` are.

  | parameter | block | the condition | rank on two batches (40, resp. 80, inputs from every pattern) | count `P + d² − ((d(d−1) + 2) + s)` |
  |---|---|---|---|---|
  | (B′) | ReLU, six units: the read columns and rows `a_i` of the parameter (B) of the twenty-first audit, `W_write` rows `a_i A` | fails: on the sector with the active units 1, 3, 4 and on the opposite one `∑ c_i a_i = I` (exact), so `B(u) = u A` | **25**, 25 | 26 |
  | (R2) | ReGLU, six units (below) | fails: `B(u) = u_1 · u A` on the quadrant `u_1 > 0 > u_2`, `B(u) = u_2 · u A` on the opposite one | **31**, 31 | 32 |
  | (A′) | ReLU, two units, `W_read = I`, `W_write = A` | fails: `B(u) = u A` where both are active | 14, 14 | 14 |
  | (R1) | ReGLU, two units, gates `e_1, e_2`, both values `(1, 1)`, `W_write = A` | fails: `B(u) = (u_1 + u_2) u A` where both gates are active | 16, 16 | 16 |

  - (R2), my own: gates `g = (1,0), (0,1), (1,−1), (2,−1), (−1,2), (−1,3)`, values
    `v = (1,−1), (1,0), (1,0), (1,0), (0,−1), (0,1)`, rows of `W_write`: `a_i A` with
    `a = (1,1), (1,0), (−2,−3), (1,1), (0,1), (0,1)`. On the quadrant `u_1 > 0 > u_2` the gates 1,
    3, 4 are active and the block before `A` is `u_1 u`; on `u_2 > 0 > u_1` the gates 2, 5, 6 are
    active and it is `u_2 u` (checked exactly at rational rows, `z24turn_hyp.out`).
  - Every other hypothesis, clause by clause (exact, `z24turn_hyp.out`): `E`, `D` of rank 2; `A`
    invertible; every row of `W_write` nonzero; (B′): the six read columns nonzero and pairwise
    non-collinear; (R2): the six gates nonzero and pairwise non-collinear, the values nonzero, no
    value a multiple of its gate; `d = 2`; `hw`: (B′) at `v = (1, 1)` no unit is at its kink and
    `v A = (2, 2)`, `B(v) = (62, 37)` are independent; (R2) at `v = (5, 1)` no gate is at its
    kink and `v A = (10, 6)`, `B(v) = (60, 35)` are independent. The hypotheses on `σ` are those
    of ReLU, and `hU` is `relu_unitsRescaleSphere`.
  - The extra flat direction. (B′): column 1 of `W_read` moves by `(1/6, 0)`, row 1 of `W_write`
    by `(0, 1/6) A`, column 2 by `(−1/6, 0)`, row 2 by `(0, −1/6) A` (the direction of the
    twenty-first audit times `A`). (R2): the value column of unit 1 moves by `(1, 0)` and row 1
    of `W_write` by `(0, −1) A`; the gate column of unit 2 moves by `(−1, 0)` and row 2 of
    `W_write` by `(0, −1) A`. By hand for (R2), before `A`: the derivative of unit 1 along it is
    `u_1 · u` where gate 1 is active, that of unit 2 is `−u_1 · u` where gate 2 is active; they
    cancel where both are active. On the two quadrants where exactly one is active, with
    `x E = t n` and `n = N_0(x E)`, `h_1 = (t + n_1) n A`, resp. `(t + n_2) n A`, and its
    derivative along the direction is `n_1 n A`, resp. `−n_1 n A`: a multiple of `h_1`, which
    the last normalization removes. So the direction is flat at every input at which no
    normalized row vanishes and no gate is at its kink. Computed: the Jacobian times it is zero
    to `10⁻⁵³`, resp. `10⁻⁵⁷`, on both batches, and it is outside the span of the stated
    directions (the stated directions have the certified rank 10, resp. 16; the kernel on the
    batch has 11, resp. 17). The rank 25, resp. 31, is a certified lower bound, and with the
    extra direction it is the rank.
  - What this refutes: no Lean statement (each has `hturn`). Without `hturn`,
    `flatSkipsOn_noKink_le_mlp_rescale_learned_rmsNorm_zero` and
    `exists_jacobianRankSkips_mlp_oneBlock_rescale_rmsNorm_zero` would be false at (B′), and the
    two ReGLU twins at (R2). For `funDimLearned` (all inputs at which the output is
    differentiable) I did not compute at inputs with a unit at its kink.
- The statements at almost every pair:

  ```
  theorem ae_turnsActiveRowsSkip_reluSq (μ : Measure (Params (Arch.mlp … reluSq (rmsNorm 0) hid)
      dIn dOut × (Fin 1 → Matrix d d ℝ))) [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) :
      ∀ᵐ p ∂μ, TurnsActiveRowsSkip p.1 (p.2 0)
  theorem ae_turnsActiveRowsGatedSkip_reglu (μ : Measure (Params (Arch.gated … relu (rmsNorm 0) hid)
      dIn dOut × (Fin 1 → Matrix d d ℝ))) [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) :
      ∀ᵐ p ∂μ, TurnsActiveRowsGatedSkip p.1 (p.2 0)
  ```
  At almost every pair, the skip of the condition is the skip of the pair (`p.2 0`), for every
  Haar measure, any width (also none: then the condition is empty, `turns_of_isEmpty24`).
  `d ≥ 2` is needed: in one coordinate two rows are never independent, so the condition fails at
  every block with an active row.

### Check 5. `reglu_unitsRescaleSphere`

**Verdict: the statement is the paper's step for ReGLU units with Lemma B.3 folded in, for any
symmetric `X`; the factor and the signs of `β_i = (2 c₀ − λ_i − μ_i) a_i` are right; it is true
in all 60 exact systems (the solutions have dimension `2q + 1`); "one unit at least", `a_i ≠ 0`,
`g_i ≠ 0`, "gates pairwise non-collinear" (opposite gates too), "`v_i` not a multiple of `g_i`"
and "`X` symmetric" are each needed. `hvg` is generic for two or more coordinates and comes from
`OneBlockGenericReGLURMS`.** (By reading and by hand; by computation in exact integer
arithmetic, `z24units.py`, `z24units_opp.py`.)

- The Lean text:

  ```
  theorem reglu_unitsRescaleSphere {n m q : Type*} [Fintype n] [DecidableEq n] [Fintype m]
      [Fintype q] [Nonempty q]
      (g v : q → n → ℝ) (a : q → m → ℝ) (X : Matrix n n ℝ) (ψg ψv : q → n → ℝ) (β : q → m → ℝ)
      (ha : ∀ i, a i ≠ 0) (hg : ∀ i, g i ≠ 0) (hgg : ∀ i j, i ≠ j → ∀ r : ℝ, g i ≠ r • g j)
      (hvg : ∀ i, ∀ r : ℝ, v i ≠ r • g i) (hX : Xᵀ = X)
      (h : ∀ x : n → ℝ, (∀ i, x ⬝ᵥ g i ≠ 0) →
        (x ⬝ᵥ x) • ∑ i, ((relu (x ⬝ᵥ g i) * (x ⬝ᵥ v i)) • β i
            + (reluDeriv (x ⬝ᵥ g i) * (x ⬝ᵥ ψg i) * (x ⬝ᵥ v i)) • a i
            + (relu (x ⬝ᵥ g i) * (x ⬝ᵥ ψv i)) • a i)
          = (2 * ((x ᵥ* X) ⬝ᵥ x)) • ∑ i, (relu (x ⬝ᵥ g i) * (x ⬝ᵥ v i)) • a i) :
      ∃ (c₀ : ℝ) (lam mu : q → ℝ), X = c₀ • (1 : Matrix n n ℝ) ∧
        ∀ i, ψg i = lam i • g i ∧ ψv i = mu i • v i ∧
          β i = (2 * c₀ - lam i - mu i) • a i
  ```
- The symbols. Lines 2882 to 2889: "`‖n‖² ∂_ψ B(n) = k d_model q(n) B(n)` for all `n ≠ 0` […]
  `‖n‖²` times a polynomial equals `k d_model q(n)` times `(n c_i) a_i`, `(n c_i)² a_i` or
  `(n c_i)(n e_i) a_i`." Lean's `x` is the paper's `n`; `g i` is the gate column `c_i`, `v i` the
  value column `e_i`, `a i` the row `a_i` of `W_write`; `k = 2` for a ReGLU block, and
  `k d_model q(x) = 2 (x X x^⊤)` with `q(x) = x X x^⊤/d_model`. The left side is the paper's
  "terms of the unit in `D_ϕ G(ϕ, x) ψ`" without biases (line 2456):
  `σ(z_i) w_i ψ_{a_i} + σ′(z_i)(x ψ_{c_i}) w_i a_i + σ(z_i)(x ψ_{e_i}) a_i`, in this order of
  Lean's three terms with `β i = ψ_{a_i}`.
- The factor and the signs, derived. Put `X = c₀ I`, `ψg_i = λ_i g_i`, `ψv_i = μ_i v_i`. Since
  `relu′(z) z = relu(z)`, the left side is `‖x‖² ∑_i relu(x g_i)(x v_i)[β_i + (λ_i + μ_i) a_i]`
  and the right side `2 c₀ ‖x‖² ∑_i relu(x g_i)(x v_i) a_i`: solved by
  `β_i = (2 c₀ − λ_i − μ_i) a_i`. Its parts are known directions: the rescaling of the gate
  (`λ_i g_i`, `−λ_i a_i`), the rescaling of the value (`μ_i v_i`, `−μ_i a_i`; Lemma B.3 for ReGLU
  with `λ_i` and `α_i = −μ_i`: `ψ_{a_i} = (α_i − λ_i) a_i`), and the scaling of the input by
  `1 + τ c₀`, which scales a block of degree 2 by `(1 + τ c₀)²`: `+ 2 c₀ a_i`.
- The hypotheses against Lemma B.3 ("Let every `a_i ≠ 0` and let the `c_i` be nonzero and
  pairwise non-collinear; for the gated blocks let also every `e_i ≠ 0`, with `(e_i, β′_i)` not
  proportional to `(c_i, β_i)`"): `ha`, `hg`, `hgg`, and `hvg` with `r = 0` for `e_i ≠ 0` and the
  other `r` for "not proportional" (without biases). `hX`: the paper's `X_0` is symmetric of
  trace zero; Lean allows any symmetric `X` and concludes `X = c₀ I`, which for trace zero is
  `X = 0`. LEAN STRONGER, as `UnitsRescaleSphere` (twenty-third audit, check 5). The input and
  the output have their own index types `n`, `m`; the network statement uses `n = m = d`.
- **Computed, the statement** (`z24units.out`). 15 shapes `(n, m, q)`: `(2,1,1)`, `(2,2,1)`,
  `(2,2,2)`, `(2,1,3)`, `(2,2,5)`, `(2,3,7)`, `(3,1,1)`, `(3,2,2)`, `(3,3,3)`, `(3,2,6)`,
  `(3,3,8)`, `(4,3,2)`, `(4,2,7)`, `(5,2,3)`, `(5,3,6)`: one, two and more units, and more units
  than coordinates; four random integer weights in `[−5, 5]` each that meet the hypotheses: 60
  systems. Unknowns: the symmetric `X`, the `ψg_i`, `ψv_i`, `β_i`; equations at six integer inputs
  per unknown and forty more, none with a gate at its kink. The kernel over the rationals has
  dimension `2q + 1` in all 60; the `2q + 1` claimed solutions (`c₀`; `λ_i`; `μ_i`) solve the
  equations exactly, also at 200 fresh inputs, and are independent. The kernel on a batch
  contains the solutions of the hypothesis, so in these 60 cases every solution has the stated
  form.
- A note on my first run (`z24units_run1.out`): with inputs from `[−7, 7]^n` one system
  (`n = 2`, `q = 7`) had a kernel of 17 against 15 on the batch. Replayed
  (`z24units_replay.py`): that batch hit 12 of the 14 patterns of gates; with inputs from
  `[−60, 60]²` (all 14 patterns) the kernel of the same system is 15. A batch that misses a
  pattern shows solutions that are none.
- **The hypotheses** (`n = m = q = 2` unless said; `g = ((1,2), (3,−1))`; each example meets
  all the other hypotheses and solves the hypothesis equation exactly at about 500 integer
  inputs, and identically by the line given):
  - *One unit at least: needed for two or more coordinates.* No unit, `X = diag(1, 0)`: both sides
    are empty sums; `X` is not `c₀ I`.
  - *`a_i ≠ 0`: needed.* `v = ((2,1), (1,1))`, `a = ((0,0), (1,2))`, `ψg_0 = (2, −1)`, all else
    `0`: `ψg_0` enters only through `a_0 = 0`, and is not a multiple of `g_0`. Kernel 7 against 5.
  - *`g_i ≠ 0`: needed, for the form of the statement.* One unit with `g_0 = 0`, `v_0 = (1, 0)`,
    `a_0 ≠ 0`: no `x` has `x g_0 ≠ 0`, the hypothesis holds for every `X`, and `X = diag(1, 0)`
    is not `c₀ I`. (By hand.)
  - *Gates pairwise non-collinear: needed.* A positive multiple: `g_1 = 2 g_0`, `v_0 = v_1 = (1,−1)`,
    `a = ((1,0), (0,1))`, `β = ((2,6), (−1,−3))`, all else `0`: `relu(2z) = 2 relu(z)` and
    `β_0 + 2β_1 = 0`; the conclusion would give `β = 0`. Kernel 7 against 5. Opposite gates: with
    one pair `g_1 = −g_0` and random other weights the kernel on the batch was `2q + 1` in 28 of
    30 systems (10 against 9 in two systems with one output); with two pairs it need not be: `n = 2`, `m = 1`, `g = (g_0, −g_0, g_2, −g_2)` with `g_0 = (1,2)`, `g_2 = (3,−1)`,
    `v = (v_0, v_0, v_2, v_2)` with `v_0 = (2,1)`, `v_2 = (1,1)`, `a = (1, −1, 1, −1)`, so that the
    block is the polynomial `(x g_0)(x v_0) + (x g_2)(x v_2)`; `ψg = (v_2, −v_2, −v_0, v_0)`, all
    else `0`: the derivative is `(x v_2)(x v_0) − (x v_0)(x v_2) = 0`, and `ψg_0 = v_2` is not a
    multiple of `g_0` (exact at 1980 inputs; kernel 12 against 9; `z24units_opp.out`).
  - *`v_i` not a multiple of `g_i`: needed.* `v_0 = 3 g_0` (the unit is then `3 relu(x g_0)² a_0`):
    `ψg_0 = (1, 0)`, `ψv_0 = (−3, 0)`, all else `0`: the two terms are `3 x_1 relu(x g_0) a_0` and
    its negative; `ψg_0` is not a multiple of `g_0`. Kernel 6 against 5. `v_0 = 0`:
    `β_0 = (1, −1)` with `a_0 = (1, 1)`, all else `0`: `β_0` enters only through `x v_0 = 0`, and
    is not a multiple of `a_0`. Kernel 7 against 5.
  - *`X` symmetric: needed.* `X = ((0,1), (−1,0))`, all else `0`: `x X x^⊤ = 0`.
- One coordinate: every `v_i` is a multiple of a nonzero `g_i`, so with a unit the hypotheses
  cannot hold and the theorem is empty for `n = 1`; it is used for `d ≥ 2`.
- **`hvg` is generic, and where it comes from.** For two or more coordinates "`v_i` is not a
  multiple of `g_i`" fails only where all `2 × 2` minors of `(g_i, v_i)` vanish. The network
  statement gets it from the field `value_not_gate` of `OneBlockGenericReGLURMS θ`
  (`∀ i r, (θ.read 0)ᵀ (Sum.inr i) ≠ r • (θ.read 0)ᵀ (Sum.inl i)`), which holds at almost every
  `θ` for `d ≥ 2` (`ae_oneBlockGenericReGLURMS`). The paper: "the value weights `(e_i, β′_i)` of
  each unit […] have `e_i ≠ 0` and are not proportional to its gate weights" (line 2410).

### Check 6. The other hypotheses of the statements at one parameter

**Verdict: all are the paper's generic conditions or steps of its proof, except the condition of
check 4; none is vacuous or contradictory; `hw` follows from the condition for a block with a
hidden unit, and `d ≥ 2` follows from `hw`.** (By reading; by compiling, `Chk2.lean`; one
parameter by hand.)

| hypothesis | the paper | note |
|---|---|---|
| `hθ.rank_E`, `hθ.rank_D` | "For generic parameters `E`, `D` […] have rank `d_model`" (line 2407); "`E A` […] has rank `d_model`"; "`D` has full row rank" (Step 1 of part (ii)) | named |
| `hθ.row_ne_zero`, `col_ne_zero`, `col_not_collinear` (MLP); `gate_ne_zero`, `gate_not_collinear`, `value_ne_zero`, `value_not_gate` (ReGLU) | the hypotheses of Lemma B.3 "with `E` and `D` replaced by the identity" (Step 4 of part (ii)); the divisibility step uses them ("at a point of no other such hyperplane") and does not name them | generic for `d ≥ 2` |
| `hR`: the skip invertible | "`A` is invertible for generic parameters" | named |
| `hturn` | not stated | check 4 |
| `hw`: one row off the kinks with `v A` and `B(v)` independent | the set is named ("wherever `w E A` and `g(w)` are linearly independent"), its being nonempty is not | follows from `hturn`, a hidden unit, no zero read column and "`σ` is not `0` off `0`" (compiled, `hw_of_turnsActiveRowsSkip24`); false without a hidden unit (`not_hw_of_isEmpty24`), which is how the statements at one parameter exclude the block without units |
| `hd`: `d ≥ 2` | "Let `d_model ≥ 2`" | follows from `hw` (two rows of `ℝ¹` are never independent) |
| `hσ`, `hhom`, `hU` (MLP form) | ReLU and ReLU² have them (`hasDerivAt_relu`, `relu_homogeneous`, `relu_unitsRescaleSphere`, and the same for ReLU²); `hU` is the divisibility step with Lemma B.3 | the statement is for any activation with the three; the paper's are the two named |

- Not vacuous, compiled (`exists_hypotheses_relu24`, `exists_hypotheses_reglu24`, standard axioms
  only): for `d = d_in = d_out = 2` and one hidden unit there is a pair `(θ, A)` with
  `OneBlockGenericRMS θ`, `IsUnit (A).det`, `TurnsActiveRowsSkip θ A` and `hw`, and
  `UnitsRescaleSphere relu reluDeriv 1` holds; the same with `OneBlockGenericReGLURMS` and
  `TurnsActiveRowsGatedSkip`.
- One parameter by hand, `d = 2`, ReLU: `E = D = I`, one unit with the read column `(1, 0)` and
  the write row `(0, 1)`, `A = [[2, 1], [0, 1]]`. Ranks 2, 2; `det A = 2`; one unit, so nothing
  to compare for collinearity. A row `u` is active when `u_1 > 0`; then `B(u) = u_1 (0, 1)` and
  `u A = (2u_1, u_1 + u_2)`, with determinant `2u_1² ≠ 0`: every active row is turned, so
  `hturn` and `hw` hold.

### Check 7. The index rows and the axiom file

**Verdict: every sentence of the five rows is true of the statements. Every public theorem of the
five files is in its row and in `checks/Axioms.lean` (all five files are proved now). The
"Not stated" sentences of four rows are true of the file and no longer of the library.** (By reading; the
names by a script; at `5adbab6`, rows at lines 943 to 947 of `STATEMENTS.md`; at `d51c1e9` the
same five rows, unchanged, are at lines 946 to 950, and the names are in its `checks/Axioms.lean`.)

- The names: for each file the public names of the source are exactly those of the third cell of
  its row: 4 (with `TurnsActiveRowsSkip`), 10, 1, 4 (with `TurnsActiveRowsGatedSkip`), 5. All 22
  theorems have a `#print axioms` line in `checks/Axioms.lean`; the two definitions have none, as
  no definition has.
- Row of `OneBlock/LearnedSkipRMSZeroRescale.lean` (943): every clause is true (checks 3, 4, 6).
  "Not stated: ReGLU blocks; the upper triangular skip" is overtaken by rows 946, 947 and 949.
- Row of `OneBlock/LearnedSkipRMSZeroRescaleGeneric.lean` (944): every clause is true (checks 1,
  2). The same "Not stated".
- Row of `OneBlock/UnitsRescaleSphereReGLU.lean` (945): every clause is true (check 5). "27
  systems": I ran the coordinator's script; 27 lines, all with `2q + 1` solutions. Its docstring
  names the statement `GatedUnitsRescaleSphere`, which is not a name of the library.
- Row of `OneBlock/LearnedSkipRMSZeroReGLU.lean` (946): every clause is true. The numeric check
  named, `learned_skip_zero_relu_check_2026-11-24.py`, has ReGLU cases (read, not run). "Not
  stated: the upper triangular skip" is overtaken by row 949.
- Row of `OneBlock/LearnedSkipRMSZeroReGLUGeneric.lean` (947): every clause is true. The same.
- Lines 261 to 267 ("Not yet compared by such a reader") name the five files. The words there,
  "the six corollaries of the second file are proved by the coordinator" and "the three
  corollaries", are about proofs; I did not check them.
- The headers of `OneBlock/LearnedSkipRMSZeroRescale.lean` (lines 45, 46) and of
  `…RescaleGeneric.lean` (line 27) carry the same overtaken "Not stated: ReGLU blocks; the upper
  triangular skip"; those of the two ReGLU files "Not stated: the upper triangular skip".

---------------------------------------------------------------------------------------------------

## Part 2: the statements, file by file

Verdict words: SAME, LEAN STRONGER, LEAN WEAKER, DIFFERENT, PART, FALSE. Every statement
formalizes a part of the sentence of Theorem B.1 (iii), "For `ε = 0` it exceeds that of the
residual network with `ε = 0` by at most `d_model (d_model + 1)/2 − 1`, with equality for ReLU,
ReLU² and ReGLU blocks", or a piece of its proof; PART says which part. All are for a full learned
skip.

| Lean | paper | verdict | note |
|---|---|---|---|
| `TurnsActiveRowsSkip` (definition) | none: a condition that the proof needs between "`μ = c` wherever `w E A` and `g(w)` are linearly independent" and "(17) holds […] on the sphere" | not in the paper | sufficient, needed in some form (check 4), generic |
| `flatSkipsOn_noKink_le_mlp_rescale_learned_rmsNorm_zero` | proof, "The case `ε = 0`" with Steps 4 and 5: the flat directions are `η^rot` with the two scalings, and `K_B` = the rescalings | SAME | at one parameter under the conditions of the proof and `hturn`; any homogeneous activation with `hU`; Lean's `X₀` is the paper's `X_a` (check 3) |
| `funDimLearned_mlp_oneBlock_rescale_rmsNorm_zero` | "Then Step 5 gives equality": the value `P + d² − (d(d−1) + 2) − s` | PART; SAME | Lean's `funDimLearned` (all inputs at which the output is differentiable) |
| `exists_jacobianRankSkips_mlp_oneBlock_rescale_rmsNorm_zero` | the same value on the paper's inputs | PART; SAME | with the line above it is the paper's functional dimension (check 2) |
| `ae_turnsActiveRowsSkip_relu`, `ae_turnsActiveRowsSkip_reluSq` | none (the condition at generic parameters) | not in the paper | they close the gap of the proof for ReLU, ReLU²; `d ≥ 2`, any width |
| `ae_exists_turned_row_skip_relu`, `ae_exists_turned_row_skip_reluSq` | none (`hw` at generic parameters) | not in the paper | a hidden unit, `d ≥ 2` |
| `ae_funDimLearned_relu_oneBlock_rmsNorm_zero`, `ae_funDimLearned_reluSq_oneBlock_rmsNorm_zero` | B.1 (iii), `ε = 0`, the value for a ReLU, ReLU² block at generic parameters | PART; SAME | `d_in, d_out ≥ d ≥ 2`, a hidden unit, no width |
| `ae_exists_jacobianRankSkips_relu_oneBlock_rmsNorm_zero`, `…_reluSq_…` | the same on the paper's inputs | PART; SAME | |
| `ae_funDimLearned_relu_oneBlock_rmsNorm_zero_eq_residual_add`, `…_reluSq_…` | B.1 (iii): "with equality for ReLU, ReLU² […] blocks" | PART (full skip); SAME | Lean's functional dimensions on all inputs; they are the paper's on the paper's inputs (compiled, check 2) |
| `reglu_unitsRescaleSphere` | proof, "The case `ε = 0`": "`‖n‖²` times a polynomial equals `k d_model q(n)` times […] `(n c_i)(n e_i) a_i`. Since `‖n‖²` has no real linear factor, it divides `q(n)`, so `X_0` is a multiple of `I`", with Lemma B.3 for ReGLU | LEAN STRONGER | any symmetric `X` (the paper: trace zero); the conclusion names the whole direction; the hypotheses are written out and each is needed (check 5) |
| `TurnsActiveRowsGatedSkip` (definition) | none, as `TurnsActiveRowsSkip` | not in the paper | for any gate activation; used for ReLU |
| `flatSkipsOn_noKinkGate_le_reglu_learned_rmsNorm_zero` | as its MLP twin, for a ReGLU block: `K_B` = the rescalings of the values and of the gates | SAME | the paper's inputs are those with no gate at its kink |
| `funDimLearned_reglu_oneBlock_rmsNorm_zero` | the value `P + d² − (d(d−1) + 2) − 2 d_hidden` | PART; SAME | |
| `exists_jacobianRankSkips_reglu_oneBlock_rmsNorm_zero` | the same on the paper's inputs | PART; SAME | |
| `ae_turnsActiveRowsGatedSkip_reglu`, `ae_exists_turned_row_skip_reglu` | none (the conditions at generic parameters) | not in the paper | |
| `ae_funDimLearned_reglu_oneBlock_rmsNorm_zero`, `ae_exists_jacobianRankSkips_reglu_oneBlock_rmsNorm_zero` | B.1 (iii), `ε = 0`, the value for a ReGLU block at generic parameters, and on the paper's inputs | PART; SAME | |
| `ae_funDimLearned_reglu_oneBlock_rmsNorm_zero_eq_residual_add` | B.1 (iii): "with equality for […] ReGLU blocks" | PART (full skip); SAME | as the ReLU form |

Notes where Lean and the paper differ:
- The theorem asks `d_out ≥ d_model`; so does Lean; in my computations it was not needed (check 2).
- Part (iii) asks no width; Lean asks one hidden unit, which is needed.
- The statements at one parameter are for any `T` (finite, nonempty); the proof uses inputs whose
  rows are equal. The paper: "for an MLP block one [token] suffices".

---------------------------------------------------------------------------------------------------

## What the authors of the papers should know

Nothing false, vacuous, drifted or misdescribed was found. The rest, in the order of its use to
the paper:

1. **The step that the proof does not write is needed with a learned skip too, and for ReGLU.**
   "The constant terms then give `μ = c` wherever `w E A` and `g(w)` are linearly independent",
   and then (17) "on the sphere". For ReLU, ReLU² and ReGLU the rows at which some unit is active
   and `g(w)` is parallel to `w E A` can fill an open set at special parameters, and then there
   can be one more flat direction: at the ReLU parameter (B′) and at the ReGLU parameter (R2) of
   check 4 (`d_model = 2`, six units, an invertible skip that is not the identity, all conditions
   of the proof met) the Jacobian has rank 25 against 26, resp. 31 against 32. The condition
   ("the rows at which `u A` and `B(u)` are independent are dense among the rows off the kinks
   with an active unit") holds for generic weights and skip, with a Lean proof for the three
   kinds, so **the theorem stands**; the proof needs one sentence for it. (For the residual
   network: twenty-first audit, part A. The ReGLU example is new.)
2. **The equality of part (iii) for `ε = 0` holds in every computed case** (ReLU, ReLU², ReGLU;
   `d_model = 2, 3`; widths 1 to 7; 108 cases), and the flat directions on the batch are exactly
   the two rotations, the two scalings and the rescalings.
3. **`d_out ≥ d_model` was not needed in any computed case** for the two values of part (iii)
   with `ε = 0` and their difference (30 cases with `d_out = 1, 2`). The theorem asks it; the
   bound "at most" is proved in Lean without the rank of `D`.
4. **`d_in ≥ d_model` and at least one hidden unit are needed.** With `d_in < d_model` the
   difference was `0` or `2` in place of `2` or `5`; without a hidden unit the learned skip adds
   nothing (`A` only renames `E`). Part (iii) asks no width, and none is needed: the equality
   holds for one unit.
5. **The conditions of the divisibility step for ReGLU** ("Across the hyperplane `n c_i = 0` […]
   it divides `q(n)`"): a unit with `a_i ≠ 0`; the gate columns nonzero and pairwise
   non-collinear, opposite gates included (two pairs of opposite gates that make a polynomial
   block give other solutions); **no value column proportional to its gate column** (if
   `e_i = r c_i` the unit is `r (n c_i)² a_i` and a direction can move the gate against the
   value); `d_model ≥ 2`. The paragraph names none; Lemma B.3 has them for ReGLU, and they hold
   for generic parameters. With them the step is true as a statement on vectors: exact check of
   60 systems, and a Lean proof.
6. A clash of names between the paper and the Lean statements: the paper's `X_0` is the symmetric
   part of trace zero of `X`, which vanishes; Lean's `X₀` is the antisymmetric part, the paper's
   `X_a`.
7. Whoever checks such statements numerically must take inputs from every pattern of active
   units or gates: in my first exact run of the ReGLU step one batch missed 2 of 14 patterns and
   showed two solutions too many (check 5).

## Corrections for `STATEMENTS.md`

No row has an error. Lines are those of `5adbab6`; at `d51c1e9` (23:52) add 3 to a row number
(rows 946 to 950, the row of the upper triangular skip at 952), and the list "Not yet compared"
is at lines 268 to 273, where a line already says that these five files are with this audit.

1. **Lines 261 to 267** ("Not yet compared by such a reader …"): the five files of this audit
   (`OneBlock/LearnedSkipRMSZeroRescale.lean`, `…RescaleGeneric.lean`,
   `OneBlock/UnitsRescaleSphereReGLU.lean`, `OneBlock/LearnedSkipRMSZeroReGLU.lean`,
   `…ReGLUGeneric.lean`; 22 public theorems, 2 definitions) can move to the compared ones, with
   this report: nothing false, vacuous or drifted; the 15 statements at almost every weights and
   skip are for every Haar measure on the pairs; the flat directions are the stated ones in 108
   computed cases; `reglu_unitsRescaleSphere` is true in 60 exact systems and each hypothesis is
   needed; the condition `TurnsActiveRowsSkip`, resp. `TurnsActiveRowsGatedSkip`, is needed (rank
   25 against 26, resp. 31 against 32, at a parameter where it fails).
2. **Rows 943 and 944**: "Not stated: ReGLU blocks; the upper triangular skip" → "Not stated
   here: ReGLU blocks (`OneBlock/LearnedSkipRMSZeroReGLU.lean`, `…ReGLUGeneric.lean`); the upper
   triangular skip (`OneBlock/LearnedSkipTriangularRMSZeroRescale.lean`)". The same sentence in
   the headers of the two files.
3. **Rows 946 and 947**: "Not stated: the upper triangular skip" → "Not stated here: the upper
   triangular skip (`OneBlock/LearnedSkipTriangularRMSZeroRescale.lean`)". The same in the two
   headers.
4. **Rows 943 and 946**, to add: "Lean's `X₀` is the paper's `X_a`, `c₀` its `c_0`, `c₁` its `c`;
   `hw` follows from the condition for a block with a hidden unit, and `d ≥ 2` from `hw`
   (twenty-fourth audit, part A, check 6); the condition is needed (check 4)".
5. **Rows 944 and 947**, to add after "`funDimLearned = funDim` of the residual network with the
   weights `θ` `+ d(d+1)/2 − 1`": "(both are the paper's functional dimensions on the paper's
   inputs: with `ae_exists_jacobianRank_relu_oneBlock_residual_rmsNorm_zero`, `…_reluSq_…`,
   resp. `…_reglu_…`; compiled in the twenty-fourth audit, part A, check 2)". And: "`d ≥ 2`,
   `d_in ≥ d` and the hidden unit are needed; no computed case with `d_out < d` changed a value".
6. **Row 945**, to add: "each hypothesis (a unit, `a_i ≠ 0`, `g_i ≠ 0`, gates pairwise
   non-collinear, `v_i` not a multiple of `g_i`, `X` symmetric) is needed: twenty-fourth audit,
   part A, check 5; empty for one coordinate". The docstring of
   `gated_units_rescale_sphere_check_2026-11-24.py` names `GatedUnitsRescaleSphere`; the
   statement is `reglu_unitsRescaleSphere`.

## What I could not check

- The proofs: not read, as the brief says. That the 22 theorems are proved rests on the axiom
  lines (`Chk1.lean`) against the build of `/home/claude/lp/lean`, which I did not rebuild.
- `funDimLearned` at the parameters (B′) and (R2): its inputs include those with a unit at its
  kink at which the output is still differentiable; I computed on the paper's inputs only.
- The ranks are for `d = 2, 3` and one token. A rank on a batch is a certified lower bound; that
  it is the full rank rests on the entries left after the pivots (below `10⁻⁴⁶` at 60 digits),
  on the two batches agreeing where two were taken, and in check 3 on the stated directions
  lying in the kernel. The kernels of check 3 are numerical at 60 digits.
- That `d_out ≥ d` is not needed: 30 cases, no proof. That the values fail for `d_in < d`: lower
  bounds on two batches, with an upper bound by hand for `d = 2`, `d_in = 1`, width 1 only.
- `reglu_unitsRescaleSphere` was computed for up to five coordinates and eight units, with
  integer weights between `−5` and `5`.
- The numeric check `learned_skip_zero_relu_check_2026-11-24.py` was read at its head, not run.
- `OneBlock/LearnedSkipTriangularRMSZeroRescale.lean`, `OneBlock/LearnedSkipTriangularRMSZeroRank.lean`,
  `OneBlock/TurnsActiveRowsSkipLinear.lean`, `Residual/LearnedSkipsConverse.lean` and the files
  written after 23:26 UTC were not read.
