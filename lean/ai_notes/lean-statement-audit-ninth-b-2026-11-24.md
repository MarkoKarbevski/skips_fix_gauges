STATUS: complete

# Ninth audit of Lean statements against the papers, part B (24 November 2026)

Reader: an independent reader who did not write the statements. Brief:
`/home/claude/proj_up/audit9b_brief_2026-11-24.md`. I edited no repository file, ran no
`lake build`, made no commit and no push.

Subject: Lemma D.19 (the step for GELU on the path) and Theorem 5.2 (ii) at `ε = 0` of the
dimension paper, with the conditions (P1), (P2), the parameter `θ*` for GELU and Appendix D.7; the
two statements "with a batch in the domain"; and the bound with identity skips at `ε = 0` of the
skips paper. Fourteen Lean files, 35 public names.

Papers: the dimension paper as text (`dim.txt`; statement and equation numbers are those of that
text) and the skips paper as text (`skips.txt`). I read the text files, not the PDFs.

## Commit, and the files with `sorry`

Library: `/home/claude/lw/lean` (branch `lean-wip`).

- The copy I read: commit `91bc064f050350fde6622209e3fa665c3f2dce30` (24 November, 11:50:04 UTC),
  taken with `git archive` into `/home/claude/audit9b/snap`.
- While I worked the branch moved twice: to `18543e53c0416c7a64ea64fb4ec6f73085c8fab2` (11:53:29
  UTC), and to `35c1a5dbe97eff9e1d84b54601df23c808403761` (12:04:48 UTC), the commit when I
  finished. None of the fourteen files changed (`git diff --quiet 91bc064 35c1a5d` on each).
  `STATEMENTS.md` changed outside the rows of this part (the paragraph on the readers from line
  89 on, rows on local identifiability and on Proposition E.1, two notes); the rows of the
  fourteen files have the same text and moved down by 12 lines. Below I give both line numbers
  where they differ, as "snapshot / head".

Files under `SkipsLean/` that contain `sorry` (`grep -w`):

| Commit | Files with `sorry` |
|---|---|
| `91bc064` | `Dimension/ExpOrbitGated.lean` (2), `Dimension/LocalIdentifiabilityGated.lean` (6), `Residual/LocalIdentifiability.lean` (6), `Residual/LocalIdentifiabilityGated.lean` (6) |
| `18543e5` | `Dimension/ExpOrbitGated.lean` (2) |
| `35c1a5d` | `Depth/InactiveGate.lean` (2), `Depth/InactiveGateOpen.lean` (1), `Depth/InactiveGateReGLU.lean` (2), `Depth/InactiveUnit.lean` (2), `Depth/InactiveUnitRelu.lean` (7), new files on Proposition E.1 |

None of them is one of the fourteen files, and none is imported by them (the fourteen compile
without `sorryAx`, below).

`grep -rn "^axiom" SkipsLean`: no line. The word "axiom" occurs in two comments
(`Literature/OMinimal.lean`, `Literature/Sard.lean`), which say that those results are hypotheses
and not axioms. No `opaque`, `unsafe`, `implemented_by`, `native_decide` or `extern` in `SkipsLean/`.

## How I checked

- "By reading": I read the Lean source of the snapshot and the papers (dimension paper: Sections 3
  to 5, Appendix D.1 to D.3, D.6 and D.7; skips paper: Theorem 4.2, Lemma A.2, Theorem A.5 (iii),
  Theorem A.17 with its proof, Theorem B.1). I read every file header, every public statement with
  its docstring, and these proofs in full: `claimZero_castSucc_gelu`,
  `exists_suffixFlatZero_succ_gelu`, the three statements of `Depth/GeluZero.lean`, the two batch
  statements, and the private helper `blockLHSC_eq_zero_szg`.
- "By compiling": scratch files of my own in `/home/claude/audit9b/scratch/` (`Chk1.lean`,
  `Ax9.lean`, `Fit9.lean`), compiled with `lean` 4.36.0. The compiled library of `/home/claude/lw`
  has none of the fourteen files, so I used the compiled library of `/home/claude/lp/lean` (branch
  `lean-plus`, at `18543e5` when I compiled, between 11:54 and 12:00 UTC) through `LEAN_PATH`,
  without `lake build`. The fourteen source files are the same in `lp`, in `lw` and in the
  snapshot (`cmp`, again at the end, when both were at `35c1a5d`), and each compiled file of `lp`
  is newer than its source. I wrote nothing under `lw`, `lp` or the repository.
- "By a computation": Python scripts in `/home/claude/audit9b/py/` (`rank_check_gelu.py`, float64
  with automatic differentiation; `rank_mp.py`, 120 digits). They support a claim; they prove
  nothing.

## Short answer

**Nothing false, vacuous or drifted was found.** All 35 public names of the fourteen files depend
on `propext`, `Classical.choice`, `Quot.sound` only (by compiling, `Ax9.lean`), and every one is in
`STATEMENTS.md` (by a script).

1. "Generic" in `ae_funDim_gelu_skipless_rmsNorm_zero` is `∀ᵐ θ ∂μ` for any additive Haar measure.
   The value is the paper's `P − (L+1)(d(d−1)/2 + 1)`. The hypotheses are the paper's and one more,
   at least one token. The three existence statements stand where the paper has an existence
   statement.
2. `funDim` is the library's `funDim` (Definition 4.1 on Lean's total network). The two statements
   `exists_batch_ae_jacobianRank_…_rmsNorm_zero` give the paper's statement in the paper's own
   sense: one batch of inputs without a zero row such that, at almost every `θ`, `θ ∈ O_X` and the
   rank on the batch is (13).
3. Lemma D.19 in Lean has the paper's hypotheses. The cone is an explicit hypothesis, `0 < κ ≤ 1`
   with `𝓑_{>k+1}` holomorphic on `C_κ`, in the place of "the `κ_ℓ` of Lemma D.14"; `κ ≤ 1` is
   harmless and every use supplies it. No hypothesis restates a conclusion. `CondP1`, `PathP2`,
   `CondP2` and `GeluPathBlock` are the paper's (P1), (P2), (R1) to (R3) clause by clause.

Small things, none of which changes a meaning: one stale sentence and two wordings in
`STATEMENTS.md`, and one sentence in quotation marks in a file header that is not a sentence of
the paper (see "What the authors should know").

---------------------------------------------------------------------------------------------------

## Part 1: the drift checks

### Check 1. "Generic" means almost every parameter

**Verdict: yes. The theorem is `∀ᵐ θ ∂μ` for any additive Haar measure, with the paper's value and
the paper's hypotheses plus "at least one token". The existence statements stand only where the
paper has an existence statement.**

The statement (`Depth/GeluZero.lean:107-115`, by reading; the elaborated form by compiling,
`Chk1.lean`):

```
theorem ae_funDim_gelu_skipless_rmsNorm_zero [Nonempty T]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, funDim (Arch.mlp gelu (rmsNorm 0) hid) 0 θ
        + (L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
      = Module.finrank ℝ
          (Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm 0) hid) dIn dOut)
```

The quantifier over parameters is `∀ᵐ θ ∂μ`. `μ` is a variable of the statement, any additive Haar
measure on the space of parameters. (That such a measure has the null sets of the Lebesgue measure
was checked by compiling in the sixth audit; I did not repeat it.) No hypothesis is an a.e.
statement or an existence statement.

The value. The paper's (13) is `P − (L + 1) dim 𝒢 − s`. For `ε = 0` the group is `CO(d_model)`, "of
dimension `d_model(d_model − 1)/2 + 1`" (Section 3), and `s = 0` for GELU blocks (Section 4). Lean:
`funDim + (L + 1) * (card d * (card d − 1) / 2 + 1) = finrank ℝ (Params …)`. `d(d−1)` is even, so
the division of natural numbers is exact. The same.

Hypotheses side by side. Paper, Theorem 5.2: "Let `d_in, d_out ≥ d_model ≥ 2`, and consider
networks without biases whose blocks are all of one kind, tanh, GELU, SwiGLU or GeGLU, each with at
least `d_model` hidden units. In the following cases the functional dimension at generic parameters
is `P − (L + 1) dim 𝒢 − s` … (ii) GELU blocks: under pre-RMSNorm with `ε > 0` and with `ε = 0`."

| Hypothesis in Lean | In the paper |
|---|---|
| `[Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut]`, `hid : Fin L → Type`, `[∀ ℓ, Fintype (hid ℓ)]` | finite sets of tokens, coordinates and hidden units; `L` blocks, each with its own width (Lean also allows `L = 0`) |
| `[Nonempty T]` | not said; an input has at least one token |
| `(μ) [μ.IsAddHaarMeasure]`, conclusion `∀ᵐ θ ∂μ` | "at generic parameters" |
| `hd : 2 ≤ Fintype.card d` | `d_model ≥ 2` |
| `hdIn`, `hdOut` | `d_in, d_out ≥ d_model` |
| `hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)` | "each with at least `d_model` hidden units" |
| the network `Arch.mlp gelu (rmsNorm 0) hid` with the stream matrices `0`; `gelu z = z * gaussCdf z` (`Activations/Gaussian.lean:28`) | GELU blocks, pre-RMSNorm with `ε = 0`, no biases, no skips |

No hypothesis on `θ` (regular, (P1), (P2), a cone, a batch, a domain) appears in the theorem.

The existence statements of these files, and the paper at the same place:

| Lean | Form | The paper at that place | Same form? |
|---|---|---|---|
| `exists_geluPathBlock` (`Depth/GeluPathBlock.lean`) | for `d ≥ 2`, `card d ≤ card q`, `κ > 0`: `∃ W V, GeluPathBlock W V κ` | D.6, "Parameters that satisfy all conditions": (R1), (P1), (R2), (R3) fail on a null set of pairs `(W, V)`, (P2) holds on a nonempty open set of pairs; "A nonempty open set minus a set of measure zero is not empty" | existence in the paper too (the paper shows more for one block; Lean states one pair, and its header says so) |
| `exists_regularZero_gelu_path` (`Depth/RegularZeroGelu.lean`) | `∃ θ, RegularZero … θ ∧ ∀ k, CondP1 θ k ∧ ∃ κ, 0 < κ ∧ κ ≤ 1 ∧ HolomorphicOnCone geluC θ k.succ κ ∧ CondP2 θ k κ` | "So there are parameters `θ*` that are regular and whose blocks all satisfy […] (P1) and (P2) for GELU" | yes |
| `exists_jacobianRank_gelu_rmsNorm_zero` (`Depth/GeluZero.lean`) | `∃ θ n X, (no row of an input is zero) ∧ θ ∈ O_X ∧ rank on X = (13)` | D.7: "there is a finite batch `X*`, with `xE ≠ 0` for all its inputs, on which the Jacobian at `θ*` has the rank (13). By (R2), `θ* ∈ O_{X*}`" | yes: one parameter, in the paper too |
| `exists_batch_ae_jacobianRank_gelu_rmsNorm_zero`, `…_tanh_…` | `∃ n X, (no zero row) ∧ ∀ᵐ θ ∂μ, …` | D.7: the batch `X*` is fixed, then "at almost every parameter" | yes: existence of the batch, "almost every" for the parameter |
| `exists_suffixFlatZero_succ_gelu` | `∃ Z'` | (49), a matrix `Z'` | yes |
| `exists_isOpen_rates_lt`, `exists_smul_of_quadratic_rows` | an open set of rows and an order; a number `β` | "Take a nonempty open set of pairs"; "for a number `β_k`" | yes: about rows, not parameters |

None stands for a claim that the paper makes at generic parameters. The passage from the one
parameter `θ*` to almost every parameter is `ae_jacobianRank_ge_of_isPreconnected` with the four
statements of Lemma D.20, in the proof of the theorem (read), as in D.7. (P2) is not generic and no
Lean statement says it is. The a.e. statements of the fourteen files are four:
`ae_funDim_gelu_skipless_rmsNorm_zero`, the two batch statements, and
`ae_funDim_add_le_residual_rmsNorm_zero`; in each `μ` is a variable with `[μ.IsAddHaarMeasure]`.

By a computation (`rank_check_gelu.py`): for nine small GELU networks of the Lean definitions
(`d` = 2, 3, 4; `L` = 0, 1, 2, 3; one and two tokens) at random parameters and `P + 6` random
inputs, the singular value number `P − (L+1)(d(d−1)/2+1)` of the Jacobian is between `10⁻⁹` and
`3·10⁻¹` of the largest, and the next one at most `1.6·10⁻¹⁶` of it. For the worst conditioned
case (`d_in = d = 2`, three blocks) at 120 digits (`rank_mp.py`, three draws): between `10⁻¹⁶` and
`4·10⁻⁸`, and the next at most `8·10⁻⁸⁰`, the size of the differencing error. This agrees with the
value. (A first run with a batch of 17 inputs showed a smaller rank in that case. The cause was my
batch: with one token and `d = 2` an input gives one equation for the weights before `D`, so the
rank on `n` inputs is at most `n + 6`.)

### Check 2. The functional dimension is the maximum over all finite batches

**Verdict: yes. `funDim` is the library's, on Lean's total network, and the two batch statements
give the paper's statement in the paper's own sense.**

`funDim` in the theorem is `Skips.funDim` of `Dimension/Functional.lean:39-40` (by reading; by
compiling, the elaborated statement names it), with the stream matrices `0`:

```
noncomputable def funDim (θ : Params A dIn dOut) : ℕ :=
  sSup {r : ℕ | ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), r = jacobianRank A S X θ}
```

This file, `Network/Defs.lean` and `Basic/RMSNorm.lean` did not change since the commit `f1ffa79`
of the eighth audit (`git diff --quiet f1ffa79 91bc064` on each). At `ε = 0` the network is total, `rmsRow 0 0 = 0`; the note "Pre-RMSNorm with `ε = 0`"
of `STATEMENTS.md` (lines 408 to 420 / 425 to 437) says so, and says that Lean's `funDim` is at least the
paper's value at every `θ` (eighth audit, part A, by reading; I did not repeat the argument). The
header of `Depth/GeluZero.lean` says "`fd` is `funDim` of Lean's total network".

The two batch statements (`Depth/GeluZeroBatch.lean:33-43`; `Depth/TanhZeroBatch.lean` is the same
text with `Real.tanh`, by `diff`):

```
theorem exists_batch_ae_jacobianRank_gelu_rmsNorm_zero [Nonempty T]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i t, X i t ≠ 0) ∧
      ∀ᵐ θ ∂μ, θ ∈ hiddenNonzero gelu hid X (Fin.last L) ∧
        jacobianRank (Arch.mlp gelu (rmsNorm 0) hid) 0 X θ
            + (L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
          = Module.finrank ℝ
              (Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm 0) hid) dIn dOut)
```

- "A batch of inputs without a zero row": `∀ i t, X i t ≠ 0` (row `t` of the input `X i`). The
  paper's Lemma D.20 has "a finite batch of nonzero inputs", for one token.
- "`θ ∈ O_X`": `hiddenNonzero σ hid X k = {θ | ∀ i, ∀ j ≤ k, ∀ t, hidden … 0 θ (X i) j t ≠ 0}` (by
  compiling, `#print`); with `k = Fin.last L` no row of `h_0, …, h_L` vanishes at any input of the
  batch. This is the paper's `O_X`, with rows `T`.
- The order of the quantifiers is the paper's: one batch, then almost every `θ`.
- The rank on `X` is equal to (13), not only at least (13).
- The batch cannot be empty: on the empty batch the rank is `0` and `P > (L+1)(d(d−1)/2+1)`.

What the pair gives. The batch statement gives, at almost every `θ`, a batch at which the paper's
network is defined, with the rank (13): the paper's lower bound. The paper's upper bound follows
from the bound on Lean's `funDim` (`ae_funDim_add_le_skipless_rmsNorm_zero`), since Lean's value is
at least the paper's. By compiling (`Fit9.lean`, `fit_paper_sense`, from the two public statements,
three standard axioms): there are `n` and `X` without a zero row such that for almost every `θ`,
`θ ∈ O_X` and `jacobianRank … X θ = funDim … θ`. The docstrings say "With the upper bound this is
the theorem in the paper's own sense", which is right.

### Check 3. No hypothesis that restates a conclusion; (P1) and (P2)

**Verdict: Lemma D.19 has the paper's hypotheses; none restates the conclusion; `κ ≤ 1` is
harmless and supplied; (P1), (P2), (R1) to (R3) are the paper's clause by clause.**

The Lean statement (`Depth/StepZeroGelu.lean:485-491`):

```
theorem claimZero_castSucc_gelu [Nonempty T]
    {θ : Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm 0) hid) dIn dOut}
    (hθ : RegularZero (Arch.mlp gelu (rmsNorm 0) hid) θ) (hd : 2 ≤ Fintype.card d)
    (k : Fin L) (hP1 : CondP1 θ k) {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hhol : HolomorphicOnCone geluC θ k.succ κ) (hP2 : CondP2 θ k κ)
    (hk : ClaimZero (Arch.mlp gelu (rmsNorm 0) hid) θ k.succ) :
    ClaimZero (Arch.mlp gelu (rmsNorm 0) hid) θ k.castSucc
```

Paper: "Let `σ` be GELU, in the case (0), let `θ` be regular, and let block `k + 1` satisfy (P1)
and (P2). Then `(D_{k+1})` implies `(D_k)`."

| Lean | Paper |
|---|---|
| the architecture `Arch.mlp gelu (rmsNorm 0) hid` | "`σ` be GELU, in the case (0)" |
| `[Nonempty T]` | implicit: Appendix D takes one token |
| `hθ : RegularZero … θ` | "let `θ` be regular" |
| `hd : 2 ≤ card d` | Theorem 5.2 and the Setup: `d_model ≥ 2` |
| `k : Fin L` | the paper's block `k + 1` |
| `hP1 : CondP1 θ k` | (P1) for block `k + 1` |
| `hκ : 0 < κ`, `hκ1 : κ ≤ 1`, `hhol : HolomorphicOnCone geluC θ k.succ κ` | "`κ_ℓ` of Lemma D.14" (in the sentence that states (P1) and (P2)), with `ℓ = k + 1`; the proof: "let `κ = κ_{k+1}`" |
| `hP2 : CondP2 θ k κ` | (P2) for block `k + 1`, with `κ_{k+1}` |
| `hk : ClaimZero … k.succ` | `(D_{k+1})` |
| conclusion `ClaimZero … k.castSucc` | `(D_k)` |

Numbering (by reading): the Lean block `k` has the read `θ.read k` and the write `θ.write k`, reads
the hidden state `k.castSucc` (the paper's `h_k`) and writes `k.succ` (the paper's `h_{k+1}`);
`HolomorphicOnCone … k.succ κ` is about `𝓑_{>k+1}`. The same in all fourteen files.

Is `κ ≤ 1` harmless? Yes. Lemma D.14 gives "a `κ_k ∈ (0, 1]`", so the paper's number satisfies
it. Lean states the lemma for every `κ ∈ (0, 1]` such that `𝓑_{>k+1}` is holomorphic on `C_κ`,
with (P2) for the same `κ`; so it holds for whatever number Lemma D.14 gives. A smaller `κ` makes
(P2) stronger (its second and third inequality have `κ` on the right) and `hhol` weaker. The bound
`κ ≤ 1` is used for `Re⟨h, h⟩ > 0` on the cone. `hhol` says that a map is analytic; it is not the
conclusion in any form.

Does every use supply it? Yes (by reading the proofs; by compiling, none depends on `sorryAx`).

- `claimZero_of_gelu_path` (`Depth/GeluZero.lean:44-55`) takes for every block
  `CondP1 θ k ∧ ∃ κ, 0 < κ ∧ κ ≤ 1 ∧ HolomorphicOnCone geluC θ k.succ κ ∧ CondP2 θ k κ` and calls
  `claimZero_castSucc_gelu hθ hd k hP1 hκ hκ1 hhol hP2 ih` after `claimZero_last`.
- `exists_regularZero_gelu_path` has exactly this conjunction in its conclusion, with `κ ≤ 1`, and
  `exists_jacobianRank_gelu_rmsNorm_zero` passes it on unchanged.
- The cones come from Lemma D.14 (`holomorphicOnCone_last`: `κ_L = 1`;
  `exists_holomorphicOnCone_castSucc`: a `κ ∈ (0, 1]`; eighth audit, part B).
- The theorem has no cone and no condition among its hypotheses.

Hypotheses of the pieces that could look like conclusions (by reading):

- `gelu_path_step_unit` has the hypothesis `hA`: "`𝓛(z(t) − δ, 1 − δ'; n(t)) = 0` for all `t ≥ 1`
  and all complex rows `δ, δ'` whose entries outside `A` vanish". It is not the conclusion (the
  conclusion is about the unit `j ∉ A`). It is the sentence that Step 4 of the paper derives from
  its induction hypothesis and (51): "If the rows `δ` and `δ'` vanish outside the entries
  `j_1, …, j_{i−1}`, then […] `𝓛°(z − δ, 1 − δ'; n) = 0`". It is discharged twice in
  `claimZero_castSucc_gelu`: for `A = ∅` by `gelu_path_step_zero` (Step 1; line 577), and for
  `A = {i' | e i' < e j}` by the private `blockLHSC_eq_zero_szg` (line 714), which takes the
  induction hypothesis (column `i` of `η°_W` and row `i` of `η°_V` vanish for `i ∈ A`), (51) and
  "`η°` is zero after the block". So the induction hypothesis of Step 4 proper is the hypothesis of
  that private helper, and `hA` is what the paper draws from it. `hA` is asked for all `δ, δ'`
  supported in `A`, without the bound `|δ_j| ≤ ϱt` of (46); it holds for all of them, because the
  direction of the derivative is then `0`.
- `exists_isOpen_rates_lt` takes `c_i ≠ −c_j` as a hypothesis; `claimZero_castSucc_gelu` proves it
  from (P2) (`ξ₀c_j > 0` for all `j`; lines 503 to 512), as the paper does ("`c_i ≠ −c_j` by (P2)").

**(P1): `CondP1`** (`Depth/CondP.lean:45-48`):

```
def CondP1 (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) (k : Fin L) :
    Prop :=
  (∀ i j : hid k, i ≠ j → (fun a : d => θ.read k a i) ≠ fun a : d => θ.read k a j) ∧
    (∀ j : hid k, θ.write k j ≠ 0) ∧ IsUnit (θ.read k * θ.write k).det
```

| Clause of the paper's (P1) | Lean | Same? |
|---|---|---|
| "the columns of `W` are pairwise different" | column `i` ≠ column `j` of `θ.read k` for `i ≠ j` | yes |
| "no row of `V` vanishes" | `θ.write k j ≠ 0` for every `j` | yes |
| "the matrix `W V` is invertible" | `IsUnit (θ.read k * θ.write k).det` (a `d × d` matrix) | yes |

**(P2): `PathP2` and `CondP2`** (`Depth/CondP.lean:54-67`):

```
def PathP2 {q : Type*} [Fintype q] (W : Matrix d q ℝ) (V : Matrix q d ℝ) (κ : ℝ)
    (ξ ξ' : d → ℝ) : Prop :=
  (∀ j : q, |(ξ' ᵥ* W) j| < (ξ ᵥ* W) j) ∧
    Real.sqrt ((ξ' ᵥ* (W * V)) ⬝ᵥ (ξ' ᵥ* (W * V)))
      < κ / 2 * Real.sqrt ((ξ ᵥ* (W * V)) ⬝ᵥ (ξ ᵥ* (W * V))) ∧
    ∑ j : q, Real.exp (-((Fintype.card d : ℝ) * ((ξ ᵥ* W) j) ^ 2 / 2)) * Real.sqrt (V j ⬝ᵥ V j)
      < κ * Real.sqrt (Fintype.card d) / 8 * Real.sqrt ((ξ ᵥ* (W * V)) ⬝ᵥ (ξ ᵥ* (W * V)))

def CondP2 (θ : …) (k : Fin L) (κ : ℝ) : Prop :=
  ∃ ξ₀ : d → ℝ, ξ₀ ⬝ᵥ ξ₀ = 1 ∧
    ∀ ξ' : d → ℝ, ξ' ⬝ᵥ ξ' = 1 → ξ₀ ⬝ᵥ ξ' = 0 → PathP2 (θ.read k) (θ.write k) κ ξ₀ ξ'
```

| Clause of the paper's (P2) | Lean | Same? |
|---|---|---|
| "there is a unit row `ξ₀`" | `ξ₀ ⬝ᵥ ξ₀ = 1` | yes |
| "for every unit row `ξ'` orthogonal to `ξ₀`" | `∀ ξ', ξ' ⬝ᵥ ξ' = 1 → ξ₀ ⬝ᵥ ξ' = 0 →` | yes |
| "`\|ξ'c_j\| < ξ₀c_j` for every `j`" | `∀ j, \|(ξ' ᵥ* W) j\| < (ξ ᵥ* W) j` | yes |
| "`‖ξ' W V‖ < (κ_ℓ/2) ‖ξ₀ W V‖`" | `√(ξ'WV ⬝ ξ'WV) < κ / 2 * √(ξWV ⬝ ξWV)` | yes; the norms are Euclidean, written with `Real.sqrt` (the norm of `d → ℝ` in Lean is the sup norm, and it is not used) |
| "`∑_j e^{−d (ξ₀c_j)²/2} ‖a_j‖ < (κ_ℓ √d / 8) ‖ξ₀ W V‖`" | `∑ j, exp(−(card d * ((ξ ᵥ* W) j)^2 / 2)) * √(V j ⬝ V j) < κ * √(card d) / 8 * √(ξWV ⬝ ξWV)` | yes |

The three inequalities are in the paper's order and with the paper's constants (`κ/2`, `κ√d/8`,
the exponent `d (ξ₀c_j)²/2`). I checked the third against the proof: with it, `∑_j |δ_j| ‖a_j‖` is
at most `κ/8` times `√d ((t + t⁻¹)/2) ‖ξWV‖`, as the paper says before (46).

The open set of `ξ`: `isOpen_setOf_pathP2` says that the rows `x ≠ 0` whose unit row
`x̂ = ‖x‖⁻¹ x` satisfies the three inequalities with every unit `ξ' ⊥ x` form an open set of rows.
The paper: "an open set `P` of unit rows around `ξ₀` such that (P2) holds for every `ξ ∈ P`". Open
sets of rows `x ≠ 0` stand for open sets of unit rows; the header says so. Same.

The rates and their order: `r_j = (ξc_j)² − (ξ'c_j)²` in the paper; in Lean
`((x̂ ᵥ* W) j)^2 − ((ξ' x ᵥ* W) j)^2` (`exists_isOpen_rates_lt`) and
`((ξ ᵥ* θ.read k) j)^2 − ((ξ' ᵥ* θ.read k) j)^2` (`hrate` of `gelu_path_step_unit`). The order
`e : q ≃ Fin (card q)` has `e i < e j → r_i < r_j`: the rates increase along `e`, the paper's
"`r_{j_1} < r_{j_2} < ⋯ < r_{j_q}`". Step 2 takes the unit with `e j = 0` (the smallest rate, "the
slowest hidden unit"), and Step 4 goes up the order; `hrate` says `r_j < r_i` for every other unit
outside `A`. Same.

**(R1) to (R3) with (P1), (P2) for one block: `GeluPathBlock W V κ`**
(`Depth/GeluPathBlock.lean:38-60`), for one read, one write and rows `d → ℝ` (the paper's one
token):

| Field | Lean text | Paper |
|---|---|---|
| `rank_write` | `V.rank = Fintype.card d` | (R1), for the write of this block |
| `ne_zero` | `∀ n : d → ℝ, n ⬝ᵥ n = (card d : ℝ) → (fun j => gelu ((n ᵥ* W) j)) ᵥ* V ≠ 0` | (R2): `g(n) = σ(nW) V ≠ 0` for every `n ∈ S` |
| `deriv` | `∃ n, n ⬝ᵥ n = (card d : ℝ) ∧ ∀ v, v ⬝ᵥ n = 0 → (∃ a : ℝ, fderiv ℝ (fun n' => (fun j => gelu ((n' ᵥ* W) j)) ᵥ* V) n v = a • ((fun j => gelu ((n ᵥ* W) j)) ᵥ* V)) → v = 0` | (R3) in the case (0): "there is an `n ∈ S` such that no row `v ≠ 0` with `⟨v, n⟩ = 0` has `𝐃g_ℓ(n) v ∈ ℝ g_ℓ(n)`" |
| `cols_ne`, `rows_ne`, `det_unit` | the three clauses of `CondP1` with `W`, `V` | (P1) |
| `p2` | the body of `CondP2` with `W`, `V`, `κ` | (P2) for `κ` |

Is the structure satisfiable only by blocks that satisfy the paper's conditions? Yes: it has seven
fields, each is one clause of the paper, and nothing else is asked. By compiling (`Fit9.lean`):
the seven clauses build a `GeluPathBlock`; a `GeluPathBlock (θ.read k) (θ.write k) κ` gives
`CondP1 θ k ∧ CondP2 θ k κ`; and with a regular `θ`, a cone and `(D_{k+1})` it gives `(D_k)`
through `claimZero_castSucc_gelu`. `GeluPathBlock` has (R1) for the write only; `E` and `D` are not
part of a block, and `exists_regularZero_gelu_path` gives `RegularZero`, which has them. Its (P2)
is for a given `κ`; in `exists_regularZero_gelu_path` this `κ` is a number in `(0, 1]` for which
the network after the block is holomorphic on `C_κ`, the role of `κ_ℓ`. `RegularZero` was compared
with (R1) to (R3) in the eighth audit; its file did not change since (`git diff`).

---------------------------------------------------------------------------------------------------

## Part 2: the statements, file by file

### Verdict table

"Proved" for every row: no `sorry` in the file, and by compiling (`Ax9.lean`) the three standard
axioms only. "T rows": Lean states it for a hidden state with one row per token, the paper for one
token; for MLP blocks and at least one token the two say the same.

| Paper | Lean (file) | Verdict | The difference |
|---|---|---|---|
| D.3: "`𝓑_{>k}` depends on the weights of the blocks `k + 1, …, L` and on `D`" | `suffix_congr`, `suffixC_congr` (`Depth/SuffixCongr.lean`) | SAME | For any blocks and any stream matrices; and for the complex version |
| (consequence; the paper writes `𝐃_θ𝓑 η'`) | `fderiv_param_suffix_eq_zero`, `fderiv_weights_suffixC_eq_zero` | piece, true | The derivative in the weights vanishes along a direction that is zero after `h_j` and at `D`. No differentiability asked |
| D.6: "`𝓛` is holomorphic in `w̃`, affine in `w̃'` and polynomial in `n`" | `analyticAt_blockLHSC` | PART | Jointly holomorphic in `(w̃, w̃', ż)` where the rows of `w̃V` are in a cone on which `𝓑_{>k+1}` is holomorphic. "Polynomial in `n`" is not stated: `ż` is a free argument |
| D.6, proof of D.19: "a derivative of order `i` of `𝓑` is homogeneous of degree `−i`" | `blockLHSC_smul` | PART | `𝓛(c w̃, w̃'; c ż) = 𝓛(w̃, w̃'; ż)` for `c > 0`, on a cone with `0 < κ ≤ 1`: the orders `i = 1` and the derivative in the weights |
| D.3: "Conversely, every `Z = Z_k ∈ 𝔤` and `η` of the form (17) […] satisfy (16)", the case (0), form (18) | `suffixFlatZero_cobDir_add_scaleDir` (`Depth/SuffixFlatZeroConverse.lean`) | SAME | For real-analytic blocks of any kind and regular `θ`. `η` is `cobDir θ Y + scaleDir θ β`, whose entries at `E` and before `h_k` play no role; `Y_ℓ` antisymmetric is asked for `ℓ ≥ k` only |
| Proof of D.19, Step 1: "it vanishes for `ξ` in the open set `P`, hence for all `n ≠ 0`" (and part (c) of D.18) | `flat_at_matrix_of_isOpen_rows` (`Depth/FlatAtMatrixRows.lean`) | PART, true | For any matrix `M` of rank `d`, after any hidden state; the same row at every token in the hypothesis; the conclusion is the hypothesis of Lemma D.3 |
| D.3 and D.6: "`𝓑_{>k}(λh) = 𝓑_{>k}(h)`", in derivatives | `fderiv_suffix_zero_smul`, `fderiv_param_suffix_zero_smul` (`Depth/SuffixZeroRows.lean`) | piece, true | The second needs no regular `θ` |
| Equation (15): `𝐃𝓑_{>k}(h) h = 0` | `fderiv_suffix_zero_apply_self` | SAME | T rows; regular `θ`, `h` without a zero row. (The eighth audit noted that (15) had no statement of its own; it has one now) |
| Lemma D.2, as Steps 2 and 4 use it: "`𝐃𝓑(n W V) a_j ≠ 0` on an open dense set of `n`" | `eq_zero_of_fderiv_suffix_zero_eq_zero_rows` | PART, true | In contrapositive form: if `𝐃𝓑(xM)(a) = 0` on a nonempty open set of rows `x`, `M` invertible, then `a = 0` |
| Proof of D.19, Step 2: from `‖n‖² n (Z c_j + η_{c_j}) = ⟨nZ, n⟩ n c_j` to `Z = Y_k + β_k I` | `exists_smul_of_quadratic_rows` | SAME | Pure algebra; `c ≠ 0` asked (from (P2)) |
| (P1) | `CondP1` (`Depth/CondP.lean`) | SAME | Check 3 |
| (P2) | `PathP2`, `CondP2` | SAME | Check 3. `κ` is an argument in the place of `κ_ℓ` |
| Proof of D.19: "there is an open set `P` of unit rows around `ξ₀` …" | `isOpen_setOf_pathP2` | SAME | Rows `x ≠ 0` stand for unit rows. For every real `κ` |
| Proof of D.19, Steps 2 and 4: "a nonempty open set of pairs […] on which `r_{j_1} < ⋯ < r_{j_q}`" | `exists_isOpen_rates_lt` | PART (the route differs a little) | One open set `N` and one order serve Step 2 and Step 4; the pairs are the graph of a map `x ↦ ξ'(x)` over `N`; `c_i ≠ ±c_j` are hypotheses. The paper's "open dense set of pairs" is not stated |
| Proof of D.19, "The path", "The expansion", Step 1 on the path | `gelu_path_step_zero` (`Depth/StepZeroGeluPath.lean`) | PART, true | `𝓛(n(t)W, 1; n(t)) = 0` for all `t ≥ 1`: the paper's "`𝓛_0(t) = 0` for large `t`, and then for all `t ≥ 1`". One pair `ξ, ξ'` with the three inequalities for this pair only; the same row at every token |
| Step 1 at `t = 1` | `gelu_path_step_zero_real` | PART, true | "`0 = 𝓛(nW, 1; n)`" at `n = √d ξ`, with the real `𝓛` (`blockLHS`) and `ż(n)` of (20) |
| Steps 2 and 4, (50) at `t = 1` | `gelu_path_step_unit` | PART, true | `𝓛_j(1) = 0` as "the derivative at `τ = 0` of `τ ↦ 𝓛(nW − τe_j, 1; n)` vanishes", `𝓛'_j(1) = 0` as `𝐃𝓑(nWV)(ż_j(n) a_j) = 0`. For any set `A` with the hypothesis `hA` (Check 3) |
| Proof of D.19, Step 1 with (49) | `exists_suffixFlatZero_succ_gelu` (`Depth/StepZeroGeluOne.lean`) | SAME | `Z'` with `ZWV + η_W V + Wη_V = WVZ'` (the paper: `Z' = (WV)⁻¹(…)`) and (16) for `k + 1` |
| **Lemma D.19** | `claimZero_castSucc_gelu` (`Depth/StepZeroGelu.lean`) | SAME | Check 3: the cone is an explicit hypothesis, for every `κ ∈ (0, 1]`; `d ≥ 2`; at least one token |
| D.6, the conditions on one GELU block | `GeluPathBlock` (`Depth/GeluPathBlock.lean`) | SAME | Check 3; one row; (R1) for the write only |
| D.6, "Parameters that satisfy all conditions", one block | `exists_geluPathBlock` | PART | Existence of one pair for every `κ > 0`; the paper: a nonempty open set minus a null set |
| "So there are parameters `θ*` that are regular and whose blocks all satisfy […] (P1) and (P2) for GELU" | `exists_regularZero_gelu_path` (`Depth/RegularZeroGelu.lean`) | SAME | With the cone of every block made explicit, `κ ∈ (0, 1]`; the paper's Setup; at least one token |
| D.7, the case (0): "Claim `(D_k)` holds at `θ*` for `k = L`, …, `k = 0`" | `claimZero_of_gelu_path` (`Depth/GeluZero.lean`) | LEAN STRONGER | At every regular `θ` whose blocks satisfy the conditions, not only at `θ*` |
| D.7: "there is a finite batch `X*` […] the rank (13). By (R2), `θ* ∈ O_{X*}`" | `exists_jacobianRank_gelu_rmsNorm_zero` | SAME | The paper's existence at `θ*` |
| **Theorem 5.2 (ii), `ε = 0`** | `ae_funDim_gelu_skipless_rmsNorm_zero` | SAME | Check 1: at least one token is added; `funDim` is that of Lean's total network (Check 2) |
| Theorem 5.2 (ii) and (i) at `ε = 0`, in the paper's own sense (D.7: "Hence the rank on `X*` is at least (13) at almost every parameter", with `O_{X*}` of full measure) | `exists_batch_ae_jacobianRank_gelu_rmsNorm_zero` (`Depth/GeluZeroBatch.lean`), `exists_batch_ae_jacobianRank_tanh_rmsNorm_zero` (`Depth/TanhZeroBatch.lean`) | SAME | Check 2. The rank on the batch is equal to (13); with the upper bound this is the theorem for the paper's functional dimension |
| S Theorem A.5 (iii), `ε = 0`, "if" direction, in infinitesimal form | `cobDir_const_mem_flat_residual_rmsNorm_zero`, `scaleDir_const_mem_flat_residual_rmsNorm_zero` (`Dimension/UpperBoundResidualRMSNormZero.lean`) | PART, true | The directions of one `G = cQ` at all hidden states are flat for a residual network; arbitrary maps `f_ℓ`, every `θ` |
| S Theorem A.17 (ii) and Theorem 4.2, the bound with identity skips, `ε = 0`, `𝒢 = CO(d)`: `fd ≤ P − dim 𝒢 − s` | `funDim_add_le_residual_rmsNorm_zero`, `ae_funDim_add_le_residual_rmsNorm_zero` | PART (the bound without the term `s`) | `fd ≤ P − (d(d−1)/2 + 1)` where `E` has rank `d ≥ 1`, then at almost every `θ` for `d_in ≥ d`. Stronger than the paper in scope (arbitrary maps `f_ℓ`, every such `θ`, no width condition, Lean's total function). Weaker for blocks with symmetries inside: `s` is not subtracted. For tanh and GELU blocks (`s = 0`) it is the paper's bound |

### (a) Are the pieces true as written?

All 35 are proved with the three standard axioms (by compiling), so they are true as written. I
also looked at the degenerate cases, by reading, to see whether a statement holds for an empty
reason or would be false without a hypothesis.

- **No tokens.** With no token every hidden state is the empty matrix, (16) holds for all `Z` and
  `η`, and `ClaimZero` is false in general. Every statement that concludes a claim, a rank, or
  "`a = 0`" from an identity has `[Nonempty T]`: `flat_at_matrix_of_isOpen_rows`,
  `eq_zero_of_fderiv_suffix_zero_eq_zero_rows`, the three of `StepZeroGeluPath`,
  `exists_suffixFlatZero_succ_gelu`, `claimZero_castSucc_gelu`, the three of `GeluZero`, the two
  batch statements, `exists_regularZero_gelu_path`. The others (`SuffixCongr`, the converse, the
  homogeneity statements, the residual bound) are true with no tokens: their conclusions are then
  about empty matrices, and in the bound `funDim = 0` and `P ≥ d_in d ≥ d² ≥ d(d−1)/2 + 1`.
- **`d` with one element.** There is no unit row orthogonal to a unit row, so `CondP2 θ k κ` holds
  for every `θ` and every `κ` (by compiling, `Fit9.lean`, example (5)); the paper's (P2) would be
  empty in the same way. Every statement that uses (P2) to conclude something has `d ≥ 2`
  (`exists_suffixFlatZero_succ_gelu`, `claimZero_castSucc_gelu`, `claimZero_of_gelu_path`,
  `exists_geluPathBlock`, `exists_regularZero_gelu_path`, the theorem), or takes an orthonormal
  pair as a hypothesis, which forces `d ≥ 2` (the three path statements).
  `exists_isOpen_rates_lt`, `flat_at_matrix_of_isOpen_rows` and
  `eq_zero_of_fderiv_suffix_zero_eq_zero_rows` have `d ≥ 2`. `exists_smul_of_quadratic_rows` is
  true for `d = 1` (then `u = βc` with `β = u/c`, and the identity gives `Z = β`). The residual
  bound has `[Nonempty d]` and is true for `d = 1` (the count is `1`, the scale; the computation
  has such a case).
- **No hidden unit.** `CondP1` is false (`WV = 0` is not invertible, `d ≥ 1`); the second
  inequality of `PathP2` is false (`0 < 0`); `exists_geluPathBlock` asks at least `d` hidden units.
  `exists_isOpen_rates_lt` is true with no hidden unit (it then gives an open set and a unit row).
  `claimZero_castSucc_gelu` derives "at least one hidden unit" from (P1).
- **`κ ≤ 0`, `κ > 1`.** `CondP2 θ k κ` is false for `κ ≤ 0` and `d ≥ 2` (the second inequality).
  The statements with a cone ask `0 < κ ≤ 1`, except `analyticAt_blockLHSC`, which asks nothing of
  `κ`: for `κ = 0` the cone is empty and its hypothesis "the rows of `w̃₀V` lie in `C_κ`" cannot
  hold with a token, and for `κ < 0` the cone is `C_{|κ|}`. True. `isOpen_setOf_pathP2` holds for
  every real `κ`.
- **`L = 0`.** The theorem is then about `x ↦ N(xE) D`; `claimZero_of_gelu_path` is Lemma D.5. The
  computation has this case.
- **Points where Lean's derivative is a convention.** `fderiv_param_suffix_eq_zero` and
  `fderiv_param_suffix_zero_smul` hold with no hypothesis of differentiability (the two functions
  compared are the same function, or do not depend on the changed weights).
  `flat_at_matrix_of_isOpen_rows` and `eq_zero_of_fderiv_suffix_zero_eq_zero_rows` take their
  hypothesis at every row of the open set, also where `rM = 0`; asking it at more points makes a
  weaker statement, and the uses give it on sets of rows `x ≠ 0` with an invertible `WV`.
  `hA` of `gelu_path_step_unit` is asked at all `δ, δ'`, also where `(z(t) − δ)V` leaves the cone;
  see Check 3.
- **The hypotheses can hold together.** Lemma D.19 and the path statements are not empty: for
  `L ≥ 1`, `exists_regularZero_gelu_path` (proved) gives a parameter with all of them at every
  block.

`gelu_path_step_unit` for an arbitrary set `A`. The paper needs it for `A = ∅` and for
`A = {j_1, …, j_{i−1}}`, the units of smaller rate. Lean states it for any `A` with `j ∉ A` and `j`
of the smallest rate outside `A`. I checked by hand that the paper's argument covers this: every
rate is positive by the first inequality of (P2), so a term with a factor of the unit `j` and a
second factor of any unit decays faster than the two terms of the unit `j`, and so does a term
with a factor of another unit outside `A`; the terms with factors of `A` only vanish together by
`hA`.

The algebra of the header of `Depth/StepZeroGeluPath.lean` (by hand): with `s = 1/t`,
`m(s) = (1 + s²)ξ + i(1 − s²)ξ'` and `λ = √d t/2` one has `n(t) = λ m(s)` and `λ²/d = t²/4`, so
`ż(λm) = λ (m(ZW + η_W) − (t²/4)⟨mZ, m⟩ mW)`, and with the homogeneity of `𝓛` and its affinity in
`ż`, `𝓛(λw, w'; ż(λm)) = t² (s² 𝓛(w, w'; m(ZW + η_W)) − (1/4)⟨mZ, m⟩ 𝐃𝓑(wV)((w' ⊙ mW)V))`: the
`Ψ` of the header.

The residual bound (by hand, and by a computation). With identity skips and the same `G = cQ` at
all hidden states, `h_ℓ ↦ h_ℓ G` for every `ℓ` (the skip carries `h_{ℓ−1} G`, the block reads
`N(h_{ℓ−1} G) Q⁻¹ W_read = N(h_{ℓ−1}) W_read` and writes through `W_write G`), and
`N(h_L G) Q⁻¹ D = N(h_L) D`; this holds for Lean's total function, zero rows included. The
directions `E(Y + βI)`, `−Y W_read^ℓ`, `W_write^ℓ (Y + βI)`, `−YD` are determined by `(Y, β)` when
`E` has rank `d ≥ 1`, which gives `d(d−1)/2 + 1`. `rank_check_gelu.py`: for residual networks at
`ε = 0` with GELU, tanh and ReLU blocks (five sizes each, one with `d = 1`), the singular value
number `P − (d(d−1)/2+1) + 1` of the Jacobian at random parameters is at most `10⁻¹⁶` of the
largest: within the bound in all fifteen cases. For GELU and tanh with `d ≥ 2` the numerical rank
is equal to the bound; for ReLU it is lower, as the paper's term `s` says it must be.

### (b) Do the docstrings say honestly what part of the paper each piece is?

Yes. Each header quotes the passage of the paper it stands for, gives the numbering, and says where
Lean differs: "the path has the same row at every token" and "the proof goes through the map `Ψ`"
(`StepZeroGeluPath`); "the `κ_ℓ` of Lemma D.14 is any `κ ∈ (0, 1]` such that `𝓑_{>k+1}` is
holomorphic on `C_κ`, as a hypothesis" (`StepZeroGelu`); "The norms of rows in (P2) are Euclidean",
"Rows are not asked to be unit rows", "the same `N` serves Step 2 (the unit `j_1`) and Step 4"
(`CondP`); "The existence needs one pair only" (`GeluPathBlock`); "they hold at every parameter and
for arbitrary maps `f_ℓ`, for Lean's total function" (`UpperBoundResidualRMSNormZero`); "Lean's
`funDim` is that of the total network […] and is at least the paper's value" (the two batch files).
The docstring of `gelu_path_step_unit` states `hA` in words and says what `A` is in Steps 2 and 4.

Four places could be more exact; none changes a meaning.

1. `Depth/SuffixCongr.lean`, header, lines 6 to 7: `Appendix D.3, "The network after the block does
   not depend on the weights of the block"`. This is in quotation marks, and it is not a sentence
   of the paper as I have it (`dim.txt`). The paper's sentence in D.3 is "`𝓑_{>k}` depends on the
   weights of the blocks `k + 1, …, L` and on `D`". The words come from the Lean docstring of
   `blockLHS`. The meaning is the paper's. The row of this file in `STATEMENTS.md` (line 213 / 225)
   repeats the quotation.
2. `Dimension/UpperBoundResidualRMSNormZero.lean`, header and the docstring of
   `ae_funDim_add_le_residual_rmsNorm_zero`: "Stated here for blocks of any kind (`s = 0`)" and
   "Theorem A.17 (ii), residual networks under pre-RMSNorm with `ε = 0`". A reader can take
   "(`s = 0`)" to mean that `s = 0` for blocks of any kind. What holds: the statement is for
   arbitrary maps `f_ℓ` and counts the change of basis only; for blocks with symmetries inside it
   is the paper's bound without the term `s`. The header also says "Theorem B.1 (iv) uses the bound
   `P − d(d−1)/2 − 1 − s`": for the ReLU, ReLU² and ReGLU blocks of B.1 (iv) the Lean statement
   gives `P − d(d−1)/2 − 1`, not that bound.
3. `Depth/GeluPathBlock.lean`, header: "the Lean proof may take an explicit one, […] the columns of
   `W` are `λ(𝟙 + ε e_i)` and `λ μ_j 𝟙`". The proof does take it, with `μ_j = j + 1`
   (`readGpb`). "May take" is from before the proof was written.
4. `Depth/GeluZero.lean`, header: the quotation from D.7 ends "then for `k = L − 1, …, 0`"; the
   paper has "then for `k = L − 1`, and so on down to `k = 0`". A shortening inside quotation
   marks.

The docstring of the theorem does say "at least one token" (the eighth audit had asked for it in
the tanh theorem).

### (c) Do the pieces fit?

Yes. The library compiles these files without `sorryAx`, so every hypothesis of every piece is
discharged with a matching form. By reading the proofs:

- `claimZero_castSucc_gelu` follows the paper's four steps. Step 1:
  `exists_suffixFlatZero_succ_gelu` gives `Z'` with (49) and (16) for `k + 1`; `(D_{k+1})` gives
  `Y'`, `β'`. Preparation: `ξ₀c_j > 0` from (P2), hence `c_i ≠ −c_j` and `c_j ≠ 0`; the open set of
  `isOpen_setOf_pathP2` around `ξ₀`; inside it `N`, `ξ'(x)` and the order `e` from
  `exists_isOpen_rates_lt`. Step 2: `gelu_path_step_unit` with `A = ∅` and the unit of smallest
  rate, its `hA` from `gelu_path_step_zero`; then `exists_smul_of_quadratic_rows` gives
  `Z = Y₀ + β₀ I`. Step 3: `suffixFlatZero_cobDir_add_scaleDir` for the symmetry with
  `β_{k+1} = β' − β₀`; `η° = η −` symmetry satisfies (16) with `Z = 0`; (51) from (49). Step 4:
  induction along `e`; `gelu_path_step_unit` with `Z = 0`, `η°`, `A = {i' | e i' < e j}`, its `hA`
  from `blockLHSC_eq_zero_szg`; the column of `η°_W` from `𝓛°'_j(1) = 0` and the row of `η°_V`
  from `𝓛°_j(1) = 0` with `eq_zero_of_fderiv_suffix_zero_eq_zero_rows` (through private helpers).
  The conclusion is (18) for `k` with `Y`, `β`.
- `exists_suffixFlatZero_succ_gelu` is proved from `gelu_path_step_zero_real` at `ξ = x̂` for
  every `x` of the open set, the homogeneity statements of `SuffixZeroRows` (to pass from
  `n = √d x̂` to the row `x`, and to drop the term `⟨nZ, n⟩/d · nWV` by (15)),
  `flat_at_matrix_of_isOpen_rows` with `M = WV`, and Lemma D.3
  (`suffixFlatZero_of_flat_at_write`) at the matrix `WV`.
- `claimZero_of_gelu_path`, `exists_jacobianRank_gelu_rmsNorm_zero`, the theorem and the batch
  statement: Check 3 and Check 2. The conclusion of `exists_regularZero_gelu_path` is, after
  `RegularZero`, word for word the hypothesis `hblocks` of `claimZero_of_gelu_path`.
- The three conclusions of `Depth/StepZeroGeluPath.lean` are what Steps 1, 2 and 4 take from the
  path, in real terms. Step 1 takes "`0 = 𝓛(nW, 1; n)` at `n = √d ξ`"
  (`gelu_path_step_zero_real`). Step 2 takes `𝓛'_j` at `t = 1`, "`ż_j(n) 𝐃𝓑(nWV) a_j = 0` at
  `n = √d ξ`" (the second part of `gelu_path_step_unit`; Lean writes `𝐃𝓑(nWV)(ż_j(n) a_j) = 0`,
  the same by linearity). Step 4 takes `𝓛°'_j` and `𝓛°_j` at `t = 1` (both parts, with `Z = 0`
  and `η°`); for `𝓛°`, by (51), `𝓛°(nW − τe_j, 1; n) = −τ 𝐃𝓑((nW − τe_j)V)(η°_{a_j})`, so the
  derivative at `τ = 0` of the first part is `−𝐃𝓑(nWV)(η°_{a_j})`, the paper's `𝓛°_j` up to the
  sign.

I did not compare the files of the chain that are not in this part (below).

---------------------------------------------------------------------------------------------------

## What the authors should know

Nothing false, nothing vacuous, nothing drifted. In order of weight:

1. **The cone of Lemma D.19 is a hypothesis in Lean, and it is discharged.** As for Lemma D.18:
   `claimZero_castSucc_gelu`, the Step 1 statement and the three path statements take
   "`𝓑_{>k+1}` holomorphic on `C_κ`, `0 < κ ≤ 1`" where the paper says "`κ_ℓ` of Lemma D.14". The
   parameter `θ*` supplies one cone per block with (P2) for that cone, and the theorem has no such
   hypothesis.
2. **`hA` of `gelu_path_step_unit` is not the induction hypothesis of Step 4 itself** but the
   sentence the paper derives from it with (51) ("`𝓛°(z − δ, 1 − δ'; n) = 0` if `δ` and `δ'`
   vanish outside `j_1, …, j_{i−1}`"). The induction hypothesis proper (columns of `η°_W` and rows
   of `η°_V`) is the hypothesis of the private helper `blockLHSC_eq_zero_szg`, which proves `hA`.
   Both uses of `hA` are discharged. Nothing to change; the docstring is exact.
3. **The residual bound at `ε = 0` has no term `s`.** For tanh and GELU blocks it is the paper's
   bound of Theorem A.17 (ii); for SwiGLU, GeGLU, ReLU, ReLU² and ReGLU blocks it is weaker than
   the paper's by `s`, and it is not the bound that Theorem B.1 (iv) uses. The header and the
   index row can be read as saying more (corrections 2 and 3 below).
4. **Theorem 5.2 (ii) at `ε = 0` is about Lean's `funDim` on the total network;** the batch
   statement beside it gives the paper's own sense. This is the pair that the eighth audit asked
   for, now for both tanh and GELU.
5. One hypothesis more than the paper in the theorem and in Lemma D.19: at least one token. Lemma
   D.19 also writes `d ≥ 2` out.
6. `claimZero_of_gelu_path` is stated for every regular `θ` whose blocks satisfy the conditions,
   which is more than "at `θ*`".
7. The four places of (b): a sentence in quotation marks that is not the paper's
   (`Depth/SuffixCongr.lean`), "(`s = 0`)" and "Theorem B.1 (iv)" in the residual file, "may take"
   in `Depth/GeluPathBlock.lean`, a shortened quotation in `Depth/GeluZero.lean`.

About the paper (I changed nothing): the Lean proof of Lemma D.19 follows the paper's Steps 1 to 4
and needed no further hypothesis. Two places where Lean does a little less work than the paper's
text, in case the authors want them: one open set of pairs and one order of the rates serve both
Step 2 and Step 4; and in Step 4 the identity `𝓛°(z − δ, 1 − δ'; n) = 0` holds for all rows
`δ, δ'` supported on the earlier units, with no bound on their size, since the direction of the
derivative is `0`.

## Corrections for `STATEMENTS.md` (lines "at `91bc064` / at `35c1a5d`")

The rows of the fourteen files (lines 180, 206, 213 to 224 / 192, 218, 225 to 236) say what the
statements say, and the status "proved" is right. Stale or inexact:

1. **Line 335 / 352** (Theorem 5.2 (ii) for `ε > 0` and (iii)): "Not stated: (ii) for `ε = 0`". It is
   stated and proved (line 223 / 235). Replace by "(ii) for `ε = 0`: the row of `Depth/GeluZero.lean`".
2. **Line 180 / 192** (the residual bound): "also the bound of Theorem B.1 (iv) for the residual
   network". Theorem B.1 (iv) is about ReLU, ReLU² and ReGLU blocks and has the term `s`; the Lean
   bound has not. Write: "for blocks without symmetries inside this is the bound of Theorem
   A.17 (ii); the term `s` is not counted, so for the blocks of Theorem B.1 (iv) it is weaker than
   the paper's bound by `s`".
3. **Line 180 / 192**, "blocks of any kind (`s = 0`)": write "arbitrary maps `f_ℓ`; the symmetries
   inside the blocks are not counted". The note at lines 413 to 415 / 430 to 432 says it well ("blocks without
   symmetries inside").
4. **Line 213 / 225** (`Depth/SuffixCongr.lean`): `"the network after the block does not depend on the
   weights of the block"` is in quotation marks and is not a sentence of the paper. Use the
   paper's "`𝓑_{>k}` depends on the weights of the blocks `k + 1, …, L` and on `D`", or drop the
   quotation marks. The same row: "`𝓛` is holomorphic in `w̃`, affine in `w̃'`" is quoted without
   "and polynomial in `n`", which is right, since that part is not stated; a word would help:
   "(not stated: polynomial in `n`)".
5. **Lines 418 to 420 / 435 to 437** (note on `ε = 0`): "Theorem 5.2 (i) for `ε = 0` gives the value of
   `funDim` at almost every `θ`, and `exists_jacobianRank_tanh_rmsNorm_zero` with the statements of
   Lemma D.20 gives a batch of the paper's inputs with that rank at almost every `θ`." Now: Theorem
   5.2 (i) and (ii) for `ε = 0` give the value of `funDim`, and
   `exists_batch_ae_jacobianRank_tanh_rmsNorm_zero`, `exists_batch_ae_jacobianRank_gelu_rmsNorm_zero`
   give the batch directly.
6. **Lines 83 to 96 / 83 to 94** ("Not yet compared by such a reader"): after this audit remove
   `Depth/SuffixCongr.lean`, `Depth/SuffixFlatZeroConverse.lean`, `Depth/FlatAtMatrixRows.lean`,
   `Depth/CondP.lean`, `Depth/StepZeroGeluPath.lean`, `Depth/SuffixZeroRows.lean`,
   `Depth/StepZeroGeluOne.lean`, `Depth/StepZeroGelu.lean`, `Depth/GeluPathBlock.lean`,
   `Depth/RegularZeroGelu.lean`, `Depth/GeluZero.lean`,
   `Dimension/UpperBoundResidualRMSNormZero.lean`, `Depth/TanhZeroBatch.lean`,
   `Depth/GeluZeroBatch.lean` (35 public names; none false, vacuous or changed in meaning). The
   other files of that list are not in this part.
7. **Line 217 / 229** (`Depth/StepZeroGeluPath.lean`): add "at least one token" and "the three
   inequalities of (P2) for this one pair". **Line 215 / 227**
   (`flat_at_matrix_of_isOpen_rows`): add "real-analytic MLP blocks". **Line 218 / 230**: the
   statement on `𝐃_θ𝓑_{>j}(ch)` needs no regular `θ`; the statement "then `a = 0`" needs regular
   `θ` and at least one token. **Line 216 / 228**: `exists_isOpen_rates_lt` gives rows `x ≠ 0` in
   `N`. All optional.
8. **Line 220 / 232** (Lemma D.19): optional, "for every `κ ∈ (0, 1]` with this property; Lemma D.14
   gives such a `κ`".

## What I could not check

- The proofs. I compared statements and definitions, and read the proofs named under "How I
  checked". That the 35 statements are proved I took from `#print axioms` against the compiled
  library of `/home/claude/lp/lean`, built by its owner; I did not build the library. I checked
  that each compiled file was newer than its source and that the sources are those of the
  snapshot, not that it was compiled from exactly that source.
- The files of the chain that are not in this part: `Activations/MillsC.lean`,
  `Activations/MillsCExpansion.lean`, `Activations/MillsAtInfinityC.lean`,
  `Generic/HolomorphicBall.lean`, `Activations/GeluOnPath.lean`, `Depth/GeluPathSeparation.lean`.
  I read `geluC` only as far as "it extends `gelu`" (`z − φ(z) z mr(z)`; the real identity
  `z − zΦ(z) = z φ(z) mr(z)` by hand). The private helpers of `Depth/StepZeroGeluPath.lean`
  (1100 lines), `Depth/GeluPathBlock.lean` and `Depth/RegularZeroGelu.lean` I did not read line by
  line; their correctness rests on the compiler.
- That an additive Haar measure on the parameters has the null sets of the Lebesgue measure: taken
  from the sixth audit (by compiling there).
- That Lean's `funDim` at `ε = 0` is at least the paper's value at every `θ`, and whether it can be
  larger at some `θ`: taken from the eighth audit, part A (by reading there; the second question
  was left open there). With the batch statements the question no longer matters for the theorem.
- `RegularZero`, `SuffixFlatZero`, `ClaimZero`, `HolomorphicOnCone`, `blockLHSC`, `zdotC`,
  `pathMatrix`, `hiddenNonzero`: compared in the eighth audit. I read their definitions again and
  checked that their files did not change, and did not compare them a second time.
- The papers as PDFs: I read the text files. Some displays are broken there ((P2), (43), (48));
  I read (P2) with the Lean docstring beside it and checked its constants against the proof.
- The skips paper beyond Theorem 4.2, Lemma A.2, Theorem A.5 (iii), Theorem A.17 and Theorem B.1.
- The computations are floating-point checks on small networks at random parameters (float64, and
  120 digits for one case). They agree with the theorem and with the bound, and prove nothing.

## Files of this audit (`/home/claude/audit9b/`)

`snap/` (the sources at `91bc064`); `scratch/Chk1.lean`, `Chk1.out` (elaborated statements,
definitions, axioms of ten names); `scratch/Ax9.lean`, `Ax9.out`, `names.txt` (axioms of the 35
public names); `scratch/Fit9.lean`, `Fit9.out` (the structure against (P1), (P2); Lemma D.19 from
one block; the two final statements together; (P2) with one coordinate); `tools/pub.py` (public
declarations of a file); `py/rank_check_gelu.py`, `rank_check_gelu.out`, `py/rank_mp.py`,
`rank_mp.out`, `py/spec.py` (the numerical checks).
