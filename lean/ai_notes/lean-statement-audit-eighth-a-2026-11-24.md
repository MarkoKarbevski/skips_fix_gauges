STATUS: complete

# Eighth audit of Lean statements against the dimension paper, part A (24 November 2026)

Reader: an independent reader who did not write the statements. Brief:
`/home/claude/proj_up/audit8a_brief_2026-11-24.md`. Subject: the case `ε = 0` of pre-RMSNorm (the
paper's case (0)) for `tanh` blocks: Theorem 5.2 (i) at `ε = 0`, with the bound of Theorem 4.3 for
the group `CO(d)`.

Paper: "On the Functional Dimension of a Family of Analytic Neural Networks", as text (`dim.txt`;
statement and equation numbers are those of that text). I read the text file, not the PDF.

## Commit, and the files with `sorry`

Library: `/home/claude/lw/lean` (branch `lean-wip`). The branch moved while I read.

| When | Commit of `/home/claude/lw` | Files of this part with `sorry` (`grep -w sorry`) |
|---|---|---|
| start | `7747aeb` (10:14:51 UTC) | `Depth/HiddenZero.lean` (6), `Depth/DomainZero.lean` (3), `Depth/DomainZeroConnected.lean` (2), `Depth/TanhZero.lean` (3); and, outside the list of the brief but in the chain, `Depth/RegularZeroTanh.lean` (1), `Depth/TanhPathBlock.lean` (1) |
| the copy I read | `0dd64fe` (10:18:43) | `Depth/HiddenZero.lean` (6), `Depth/TanhZero.lean` (3), `Depth/RegularZeroTanh.lean` (1), `Depth/TanhPathBlock.lean` (1) |
| end | `244ec8ac4dfe9219f2d1849c90274485eae53f3f` (10:27:19) | none: no file under `SkipsLean/` contains `sorry` |

What changed between the copy I read and the end (by a script, `stmts.py`, that compares the text
of every public declaration with its docstring, 902 declarations; and by `git diff`, removed
lines): the only removed lines are 11 lines `sorry`. Seven public statements got one new line
`omit [… instance …] in` before them (six in `Depth/HiddenZero.lean`, and
`exists_regularZero_tanh_path`): an instance that the statement did not use is no longer an
argument. No hypothesis, conclusion, definition or docstring changed. Between `7747aeb` and
`0dd64fe` the only removed lines are 5 lines `sorry`. So what I say below holds for `244ec8a`.

## How I checked

- "By reading": I read the Lean source (a copy made with `git archive` in
  `/home/claude/audit8a/snap`, commit `0dd64fe`; a second copy `snap2`, commit `244ec8a`) and the
  paper.
- "By compiling": scratch files of my own in `/home/claude/audit8a/scratch/`, compiled with `lean`
  (4.36.0). The compiled library of `/home/claude/lw` lacks most files, so I read the compiled
  library of `/home/claude/lp/lean` (branch `lean-plus`) through `LEAN_PATH`, without `lake`. At
  the last run `lp` was at `244ec8a` and its sources under `SkipsLean/` were the same as `snap2`
  (`diff -rq`). I did not run `lake build`. I wrote nothing under `lw`, `lp` or the repository.
- "By a computation": a Python script in `/home/claude/audit8a/py/`.

I read statements and definitions. I did not read the proofs, except a few lines where a docstring
sent me there.

## Short answer

**Nothing false, vacuous or drifted was found.**

1. "Generic" in `ae_funDim_tanh_skipless_rmsNorm_zero` is `∀ᵐ θ ∂μ` for any additive Haar
   (Lebesgue) measure `μ` on the parameters.
2. The statements use `funDim` and `jacobianRank` in the sense of Definition 4.1, on Lean's total
   network (`rmsRow 0 0 = 0`). At every `θ` the Lean `funDim` is at least the paper's functional
   dimension; at almost every `θ` the two are equal, to (13). The final statement alone gives the
   paper's upper bound; the paper's lower bound, on a batch of inputs at which the network is
   defined, is in the public statements of the proof but not in one statement (see "What the
   authors should know", 1).
3. The final statement has the paper's hypotheses and one more, at least one token. Its value is
   the paper's (13) in the case (0). No `axiom`. At `244ec8a` it depends on `propext`,
   `Classical.choice`, `Quot.sound` only.

---------------------------------------------------------------------------------------------------

## Part 1: the three drift checks

### Check 1. "Generic parameters" is "for almost every parameter"

**Verdict: yes.** By reading, and by compiling (`Sig8.lean`: a program took the type of each of
the 53 public names of the 16 files of the brief, and of 5 names of the chain, apart).

`Depth/TanhZero.lean`, at `244ec8a`:

```
theorem ae_funDim_tanh_skipless_rmsNorm_zero [Nonempty T]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) Real.tanh (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, funDim (Arch.mlp Real.tanh (rmsNorm 0) hid) 0 θ
        + (L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
      = Module.finrank ℝ
          (Params (Arch.mlp (T := T) (d := d) Real.tanh (rmsNorm 0) hid) dIn dOut)
```

The quantifier over parameters is `∀ᵐ θ ∂μ`: the set of the `θ` at which the equality fails has
`μ`-measure zero. `μ` is a variable of the statement, any additive Haar measure on the space of
parameters, which carries the Borel σ-algebra of its norm (`Generic/Params.lean:32-34`). The sixth
audit checked by compiling that such a `μ` has the null sets of the Lebesgue measure. No
hypothesis of the statement is an a.e. statement or an existence statement.

The statements of these files with a conclusion `∀ᵐ` (5; in each, `μ` is a variable with
`[μ.IsAddHaarMeasure]`, and no hypothesis is an a.e. statement):
`ae_funDim_add_le_skipless_rmsNorm_zero`, `ae_funDim_add_le_skipless_gated_rmsNorm_zero`,
`ae_finrank_range_fderiv_ge_of_isPreconnected`, `ae_jacobianRank_ge_of_isPreconnected`,
`ae_funDim_tanh_skipless_rmsNorm_zero`. Two more say "measure zero":
`measure_zeroSet_of_analyticOnNhd_of_isPreconnected` (`μ {x | x ∈ U ∧ f x = 0} = 0`) and
`measure_compl_hiddenNonzero` (`μ (hiddenNonzero σ hid X k)ᶜ = 0`).

**The existence statements** (conclusion `∃ …`), and the paper at the same place:

| Lean | Form | The paper at that place | Same form? |
|---|---|---|---|
| `exists_jacobianRank_tanh_rmsNorm_zero` (`Depth/TanhZero.lean`) | `∃ θ n X, (no row of an input is zero) ∧ θ ∈ O_X ∧ rank on X = (13)` | D.7: "there is a finite batch `X*`, with `xE ≠ 0` for all its inputs, on which the Jacobian at `θ*` has the rank (13). By (R2), `θ* ∈ O_{X*}`", for the parameters `θ*` of D.6, "So there are parameters `θ*` …" | yes: one parameter, in the paper too |
| `exists_batch_jacobianRank_of_claimZero` (`Depth/SuffixZeroBatch.lean`) | for a given regular `θ` with `(D_0)`: `∃ n X, (no row of xE is zero) ∧ rank = (13)` | Proposition D.4: "the Jacobian of the network has the rank (13) on some finite batch of such inputs" | yes: it is over batches, not over parameters |
| `exists_regularZero_tanh_path` (`Depth/RegularZeroTanh.lean`), `exists_tanhPathBlock` (`Depth/TanhPathBlock.lean`) | `∃ θ, RegularZero ∧ ∀ k, (S1) ∧ (S2) ∧ ∃ κ > 0, …`; `∃ W V, TanhPathBlock W V κ` | D.6: "A nonempty open set minus a set of measure zero is not empty. So there are parameters `θ*` that are regular and whose blocks all satisfy (S1) to (S3)" | yes: existence in the paper |
| `exists_open_dense_fderiv_suffix_zero` | `∃ U`, open and dense, of hidden states | Lemma D.2: "there is an open dense set `U_k` of rows" | yes: about hidden states |
| `suffixFlatZero_of_flat_at_write`, `flat_le_cobDir_add_scaleDir_of_claimZero`, `ClaimZero` | `∃ Z`; `∃ Y β` | Lemma D.3 "`η_A = AZ` for a matrix `Z`"; (18) "there are `Z_{k+1}, …, Z_L`" | yes |
| `exists_eq_smul_one_of_vecMul_parallel` | `∃ c, S = c • 1` | "is a multiple of the identity" | yes |

None of them stands for a claim that the paper makes at generic parameters. The generic claim,
Theorem 5.2 (i), is the `∀ᵐ` statement; the passage from the one parameter `θ*` to almost every
parameter is `ae_jacobianRank_ge_of_isPreconnected` with the four statements of Lemma D.20, as in
D.7.

### Check 2. The functional dimension is `max_X rank DF_X(θ)` over all finite batches

**Verdict: yes, on Lean's total network. The Lean `funDim` at `ε = 0` is at least the paper's
functional dimension at every `θ`, and equal to it at almost every `θ`. I found no `θ` at which it
is larger, and I did not prove that there is none.**

The definitions (`Dimension/Functional.lean:29-49`, by reading; unchanged since the sixth audit):

```
noncomputable def jacobianRank {n : ℕ} (X : Fin n → Matrix T dIn ℝ) (θ : Params A dIn dOut) : ℕ :=
  Module.finrank ℝ (LinearMap.range (fderiv ℝ (evalBatch A S X) θ).toLinearMap)
noncomputable def funDim (θ : Params A dIn dOut) : ℕ :=
  sSup {r : ℕ | ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), r = jacobianRank A S X θ}
noncomputable def flat (θ : Params A dIn dOut) : Submodule ℝ (Params A dIn dOut) :=
  ⨅ x : Matrix T dIn ℝ, LinearMap.ker (fderiv ℝ (fun θ' => eval A S θ' x) θ).toLinearMap
```

The final statement uses `funDim`; `exists_jacobianRank_tanh_rmsNorm_zero`,
`exists_batch_jacobianRank_of_claimZero` and `ae_jacobianRank_ge_of_isPreconnected` use
`jacobianRank` on a named batch. That is the sense of Definition 4.1.

How the three treat the inputs at which the paper's network is not defined (by reading). In the
paper, for `ε = 0`, "a network is defined at the inputs for which no row of a hidden state
vanishes". In Lean the network is total: `rmsRow 0 0 = 0` (`Basic/RMSNorm.lean`), so a zero row of
a hidden state gives a zero row of every later hidden state and of the output. Mathlib's `fderiv`
of a map at a point where it is not differentiable is `0`. For a parameter `θ` and an input `x`:

- (a) No row of a hidden state of `x` vanishes at `θ`. Then `θ' ↦ F_θ'(x)` is real-analytic at `θ`
  (`analyticAt_eval_rmsNorm_zero`), and Lean's derivative is the paper's.
- (b) Some row of a hidden state of `x` vanishes at `θ`, and `θ' ↦ F_θ'(x)` (the Lean function) is
  not differentiable at `θ`. Then its `fderiv` is `0`: `x` asks nothing of a direction in `flat`,
  and every batch that contains `x` has `jacobianRank = 0`, the whole batch (the tuple of the
  outputs is then not differentiable).
- (c) Some row vanishes, and the Lean function is differentiable at `θ`. This happens: if a row
  of `x` itself is zero, that row of the output is `0` at every parameter, and the other rows
  behave as in (a). Such an input counts in `flat` and in `funDim` with its Lean derivative.

So `funDim A 0 θ` is the largest rank over the batches all of whose inputs are of the kinds (a)
and (c), and:

- **Lean ≥ paper at every `θ`:** a batch of inputs of the kind (a) has in Lean its true rank.
- **Lean can exceed the paper's value only through inputs of the kind (c).** In the example above
  it does not (the nonzero rows give nothing that an input of the kind (a) with the same rows does
  not give). I looked for a `θ` and an input of the kind (c) with a derivative outside the span of
  the derivatives at the inputs of the kind (a), by hand, in the cases `xE = 0`, a write equal to
  `0`, `D = 0`, a write of rank one; in each the Lean function is not differentiable (it behaves
  like `|t|` along a line, because the network is odd in the direction of the vanishing hidden
  state) or the derivative is `0`. This is a search, not a proof.
- **Equal at almost every `θ`,** under the hypotheses of the theorem: the upper bound
  `funDim_add_le_skipless_rmsNorm_zero` is a bound on the Lean `funDim` (all batches, with no
  hypothesis of differentiability), and the lower bound is the rank on a batch of the kind (a).

What the paper's Proposition D.4 says, "the directions `η` with `𝐃_θF(θ, x) η = 0` for all `x`,
with `xE ≠ 0` in the case (0)", and Lean:

- `flat_le_cobDir_add_scaleDir_of_claimZero` takes `η ∈ flat A 0 θ` (every input, with the
  convention above) and gives a direction of the symmetries. Lean's `flat` is contained in the
  paper's set of directions (it asks at least as much), and the directions of the symmetries are in
  `flat` (`scaleDir_mem_flat_skipless_rmsNorm_zero`, `cobDir_mem_flat_skipless_rmsNorm'`). So for a
  regular `θ` with `(D_0)` the three sets are the same.
- `exists_batch_jacobianRank_of_claimZero` gives the batch with `∀ i t, (X i * θ.E) t ≠ 0`: the
  paper's "finite batch of such inputs". By (R2) these inputs are of the kind (a).

By compiling (`Fit8b.lean`, theorem `fit4`, from the public statements, three standard axioms at
`244ec8a`): under the hypotheses of the theorem there are `n` and a batch `X` with no zero row in
any input such that, for almost every `θ`, `θ ∈ hiddenNonzero Real.tanh hid X (Fin.last L)` and
`jacobianRank … X θ + (L + 1) * (d (d − 1) / 2 + 1) = P`. This is the paper's statement in the
paper's own sense: a batch at which the network is defined, with the rank (13).

By a computation (`py/rank_check.py`, my own, float64 with automatic differentiation): for ten
small networks of the Lean definitions (`d` = 2, 3, 4; `L` = 0, 1, 2, 3; one and two tokens), at
random parameters and random inputs, the singular value number `P − (L+1)(d(d−1)/2+1)` of the
Jacobian is between `2·10⁻¹¹` and `2·10⁻¹` of the largest, and the next one is at most
`2.1·10⁻¹⁶` of it. This agrees with the value of the theorem; it is not a proof. (A first run with a fixed
threshold `10⁻⁹` misjudged three cases whose Jacobians have small singular values; the gap at the
index of the theorem is the right test.) For `d = 1` the rank is `2`, not the formula's `6`: the
hypothesis `d ≥ 2` is needed.

### Check 3. The main-text statement carries no hypothesis that the paper does not have

**Verdict: none, except "at least one token" (`[Nonempty T]`), which the paper has implicitly.
The value is the paper's. No axiom, and no hypothesis restates the conclusion.**

Paper, Theorem 5.2: "Let `d_in, d_out ≥ d_model ≥ 2`, and consider networks without biases whose
blocks are all of one kind, tanh, GELU, SwiGLU or GeGLU, each with at least `d_model` hidden
units. In the following cases the functional dimension at generic parameters is
`P − (L + 1) dim 𝒢 − s` … (i) tanh blocks: without normalization, and under pre-RMSNorm with
`ε > 0` and with `ε = 0`." Setup: no biases; inputs range over all of `ℝ^{T×d_in}`; every MLP block
has `d_hidden ≥ d_model`; `d_in, d_out ≥ d_model ≥ 2`; for `ε = 0` the group is `CO(d_model)`, "of
dimension `d_model(d_model − 1)/2 + 1`"; `s = 0` for tanh blocks.

| Hypothesis in Lean | In the paper |
|---|---|
| `[Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut]`, `hid : Fin L → Type`, `[∀ ℓ, Fintype (hid ℓ)]` | finite sets of tokens, coordinates and hidden units; `L` blocks, each with its own width. Lean allows `L = 0` (then the network is `x ↦ N(xE) D`, and the statement is true; the computation above has two such cases) |
| `[Nonempty T]` | not said; an input has at least one token. Needed: with no token the output space is `0` and `funDim = 0` |
| `(μ) [μ.IsAddHaarMeasure]`, conclusion `∀ᵐ θ ∂μ` | "at generic parameters" (Section 2: outside a set of Lebesgue measure zero) |
| `hd : 2 ≤ Fintype.card d` | `d_model ≥ 2` (statement and Setup) |
| `hdIn`, `hdOut : Fintype.card d ≤ Fintype.card dIn`, `… dOut` | `d_in, d_out ≥ d_model` |
| `hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)` | "each with at least `d_model` hidden units" |
| the network `Arch.mlp Real.tanh (rmsNorm 0) hid`, with the stream matrices `0` | tanh blocks, pre-RMSNorm with `ε = 0`, no biases, no skip connections; the readout also reads `N(h_L)` (`eval`), as in equation (2) |

No hypothesis on `θ` (regular, (S1) to (S3), a cone, a batch, a domain) appears.

The formula. (13) is `P − (L + 1) dim 𝒢 − s`. In the case (0), `𝒢 = CO(d)` has dimension
`d(d−1)/2 + 1` and `s = 0` for tanh blocks: `P − (L + 1)(d(d−1)/2 + 1)`. Lean:
`funDim + (L + 1) * (card d * (card d − 1) / 2 + 1) = finrank ℝ (Params …)`. `d(d−1)` is even, so
the division of natural numbers is exact, and `finrank ℝ (Params (Arch.mlp …))` is
`d_in d + 2 d ∑ d_hidden + d d_out` (`finrank_params_mlp`, `Dimension/ParameterCount.lean`), the
paper's `P`. The same.

Axioms (at `244ec8a`): `grep -rn "^axiom" SkipsLean` gives no line, and no file has `sorry`. By
compiling (`Ax8.lean`, against the library of `lp` at `244ec8a`): each of the 53 public names of
the 16 files, and `exists_regularZero_tanh_path`, `exists_tanhPathBlock`,
`claimZero_castSucc_tanh`, `tanh_path_step`, `exists_holomorphicOnCone_of_ne_zero`,
`HolomorphicOnCone.congr`, `eq_zero_of_fderiv_suffixC_one_sub_sq`, `blockLHSC_pathMatrix_eq_zero`,
`path_separation`, depends on `propext`, `Classical.choice`, `Quot.sound` and nothing else. (An
earlier run, when the library of `lp` was between `0dd64fe` and `244ec8a`, showed `sorryAx` in 13
of the 53: the six of `Depth/HiddenZero.lean`, the five that rest on them in
`Depth/DomainZero.lean` and `Depth/DomainZeroConnected.lean`, and
`exists_jacobianRank_tanh_rmsNorm_zero`, `ae_funDim_tanh_skipless_rmsNorm_zero`.)

---------------------------------------------------------------------------------------------------

## Part 2: the statements, file by file

Sixteen files, 53 public names. Every name is in `STATEMENTS.md` (by a script).

### Verdict table

"T rows" means: Lean states it for a hidden state with one row per token, the paper for one token.
For MLP blocks and at least one token the two say the same.

| Paper | Lean (file) | Verdict | The difference |
|---|---|---|---|
| Theorem 5.2 (i), tanh, `ε = 0` | `ae_funDim_tanh_skipless_rmsNorm_zero` (`Depth/TanhZero.lean`) | SAME | At least one token is added. `funDim` is that of Lean's total network (Check 2) |
| Theorem 4.3, the sentence "For `ε = 0` the same bound holds, with `𝒢 = CO(d_model)`, for the four kinds of block", and D.2 "(13)" | `scaleDir`, `scaleDir_mem_flat_skipless_rmsNorm_zero`, `cobDir_add_scaleDir_injective`, `funDim_add_le_skipless_rmsNorm_zero`, `ae_funDim_add_le_skipless_rmsNorm_zero`, `funDim_add_le_skipless_gated_rmsNorm_zero`, `ae_funDim_add_le_skipless_gated_rmsNorm_zero` (`Dimension/UpperBoundRMSNormZero.lean`) | LEAN STRONGER | For arbitrary maps `f_ℓ` (gated: any gate `σ`), at every `θ` where `E` and the writes have rank `d ≥ 1` (gated: and no value column vanishes), then at almost every `θ`. `scaleDir` is the part `β_ℓ I` of (11): `(β_0 E, 0, β_ℓ W_write^ℓ, 0)` |
| D.3: the derivative of `N` at `h ≠ 0`; `𝐃N(h) h = 0` (the source of (15)) | `analyticAt_rmsNorm_zero`, `fderiv_rmsNorm_zero_apply`, `fderiv_rmsNorm_zero_self` (`Depth/SuffixZero.lean`) | SAME | T rows. (15) itself, `𝐃𝓑_{>k}(h) h = 0`, has no statement of its own |
| The identity (16), "for all rows `h`, with `h ≠ 0` in the case (0)" | `SuffixFlatZero` | SAME | T rows: "no row of `h` vanishes" |
| Claim `(D_k)` in the form (18) | `ClaimZero` | SAME | Block `ℓ : Fin L` is the paper's block `ℓ + 1`. `η` is a full parameter; its entries at `E` and at the blocks up to `k` are free on both sides |
| Lemma D.5, the case (0) | `claimZero_last` | SAME | At least one token; `d ≥ 2` written out; for any `Arch` with `χ = rmsNorm 0` |
| "regular", (R1) to (R3), the case (0) | `RegularZero` (`Depth/SuffixZeroDeriv.lean`) | SAME | T rows; see (d) below |
| "by (R2), it is defined and real-analytic on all rows `h ≠ 0`" | `analyticAt_suffix_prod_zero` | LEAN STRONGER | Analytic in `(θ, h)` jointly |
| "`𝓑_{>k}(λh) = 𝓑_{>k}(h)` for `λ > 0`" | `suffix_zero_smul_rows` | SAME | One positive number per row |
| (no paper statement) `N(h)` is on the sphere | `rmsNorm_zero_dotProduct_self` | piece | True |
| Lemma D.2, the case (0) | `exists_open_dense_fderiv_suffix_zero` | SAME | T rows; any real-analytic blocks; `d ≥ 2` written out. The route (no manifold `S`) is the proof's |
| Lemma D.3, the case (0) | `suffixFlatZero_of_flat_at_write` (`Depth/SuffixZeroClaim.lean`) | SAME | At least one token |
| Proposition D.4, the case (0) | `flat_le_cobDir_add_scaleDir_of_claimZero`, `funDim_of_claimZero`; `exists_batch_jacobianRank_of_claimZero` (`Depth/SuffixZeroBatch.lean`) | SAME | In three statements. The first two use Lean's `flat` and `funDim` (every input); the third names the batch of inputs with `xE` without a zero row (Check 2) |
| Equation (14), the case (0) | `fderiv_rmsNorm_zero_mul` (`Depth/StepZeroValues.lean`) | SAME | |
| Equations (20) to (22), the case (0) | `suffixFlatZero_castSucc_iff_mlp_values`, `suffixFlatZero_castSucc_iff_mlp_sphere` | SAME | For any real-analytic activation with a given derivative, regular `θ` |
| Lemma D.17 | `eq_zero_of_fderiv_suffix_one_sub_sq_zero` | PART | For a real `b` only (the docstring says so). T rows: `b` and `w̃` are matrices. The complex `b` is `eq_zero_of_fderiv_suffixC_one_sub_sq` (`Depth/ComplexOneSubSq.lean`, not in this part) |
| D.1: "An MLP block acts on each token separately" | `suffix_mlp_rmsNorm_row`, `fderiv_suffix_zero_row`, `fderiv_param_suffix_zero_row` (`Depth/SuffixRows.lean`) | PART | Lean pieces with no paper statement: row `t` of `𝓑_{>k}(h)` and of its two derivatives is that at the hidden state with all rows equal to `h_t`. True |
| Proof of D.18: "the dense set of the `ξ` for which `ξc_1, …, ξc_q` are linearly independent over `ℚ`" | `dense_setOf_linearIndependent_vecMul` (`Depth/RowsAux.lean`) | PART | Dense among all rows `ξ`, where the paper takes unit rows in `P`. The property does not change when `ξ` is multiplied by a number `≠ 0`, so the two fit |
| "A matrix for which every row of an open set is an eigenvector is a multiple of the identity" | `exists_eq_smul_one_of_vecMul_parallel` | SAME | "Eigenvector" as "`ξS` parallel to `ξ`" (2 × 2 minors); an open set of rows, not of unit rows |
| (used for `ξ (Y_k W + η_W) = 0`) | `eq_zero_of_vecMul_eq_zero_of_isOpen` | piece | True |
| Proof of D.18, part (c) | `flat_at_write_of_isOpen_rows` (`Depth/FlatAtWriteRows.lean`) | PART | From a nonempty open set of rows `w̃` (the same row at every token) to every `w` with `wV` without a zero row: the hypothesis of Lemma D.3. At least one token |
| D.7: "real-analytic on the connected open set … so its zero set has measure zero" | `measure_zeroSet_of_analyticOnNhd_of_isPreconnected` (`Generic/AnalyticZeroSetOn.lean`) | SAME | A general fact |
| D.7: "Hence the rank on `X*` is at least (13) at almost every parameter" | `ae_finrank_range_fderiv_ge_of_isPreconnected`, `ae_jacobianRank_ge_of_isPreconnected` (`Dimension/GenericRankOn.lean`) | SAME | General: analytic on an open connected set with a null complement |
| Proof of D.20: "Removing finitely many closed submanifolds of codimension at least two …" | `isPreconnected_diff_of_forall_exists_nhds`, `isPreconnected_diff_zeroSet_of_surjective` (`Generic/ConnectedCompl.lean`) | DIFFERENT (route) | One removal; the submanifold is the zero set of a map into a space of dimension `≥ 2` with an onto strict derivative at every zero. True; the docstring says the difference |
| Proof of D.20: the hidden states as functions of the weights | `hidden_congr`, `analyticAt_hidden_rmsNorm_zero`, `analyticAt_preactivation_rmsNorm_zero`, `analyticAt_eval_rmsNorm_zero`, `surjective_fderiv_preactivation`, `surjective_fderiv_hidden_succ` (`Depth/HiddenZero.lean`) | PART | Proof pieces, for any real-analytic `σ` (the last: `σ` vanishes only at `0`). True |
| Lemma D.20 | `hiddenNonzero`, `isOpen_hiddenNonzero`, `measure_compl_hiddenNonzero`, `analyticOnNhd_evalBatch_hiddenNonzero` (`Depth/DomainZero.lean`); `isPreconnected_hiddenNonzero`, `isConnected_hiddenNonzero` (`Depth/DomainZeroConnected.lean`) | LEAN STRONGER | In four statements. For every real-analytic `σ` that vanishes exactly at `0`; for every `O^k`, not only `O_X = O^L`; "at least two hidden units per block" where the paper's Scope has at least `d_model ≥ 2`. T rows: "nonzero inputs" is "no row of an input is zero" |
| D.7, the case (0): "Claim `(D_k)` holds at `θ*` for `k = L`, …, `k = 0`"; "there is a finite batch `X*` …; `θ* ∈ O_{X*}`" | `claimZero_of_tanh_path`, `exists_jacobianRank_tanh_rmsNorm_zero` (`Depth/TanhZero.lean`) | SAME | The first is for every regular `θ` whose blocks satisfy (S1) to (S3) for a cone on which the later network is holomorphic; the second is the paper's existence at `θ*` |

### (a) Are the pieces true as written?

At `244ec8a` all 53 are proved with the three standard axioms (by compiling, `Ax8.lean`), so they
are true as written. Before that I had judged the statements that were still `sorry` by hand; I
found no counterexample. The degenerate cases, by reading:

- **No tokens.** `SuffixFlatZero` then holds for every `Z` and `η`, so `ClaimZero` is false in
  general; the statements that conclude `ClaimZero`, or a rank, have `[Nonempty T]`
  (`claimZero_last`, `suffixFlatZero_of_flat_at_write`, `flat_le_…`, `funDim_of_claimZero`,
  `exists_batch_…`, `flat_at_write_of_isOpen_rows`, the three of `Depth/TanhZero.lean`). The
  statements without it (Lemma D.2, Lemma D.17 for a real `b`, the rows, Lemma D.20) are true with
  no tokens: their conclusions are then about an empty matrix or about the whole space.
- **`d` with one element, or empty.** `funDim_add_le_skipless_rmsNorm_zero` has `[Nonempty d]` and
  is true for `d = 1` (the count is then `L + 1`, the scales). The statements that need `d ≥ 2`
  have it: Lemma D.5, D.2, D.3, D.4, D.17, part (c), the connectedness of `O^k` (false for `d = 1`:
  `xE ≠ 0` cuts the line in two), and the theorem (false for `d = 1`, by the computation).
  `exists_eq_smul_one_of_vecMul_parallel` and `dense_setOf_linearIndependent_vecMul` are true for
  an empty `d` (the first gives `c = 0`; in the second the hypothesis forces no hidden unit).
- **A block with no hidden unit.** Then `h_ℓ = 0` at every parameter, `O^ℓ` is empty, and "its
  complement has measure zero" fails; `measure_compl_hiddenNonzero` and the two statements on
  connectedness ask at least two hidden units per block. `isOpen_hiddenNonzero` and
  `analyticOnNhd_evalBatch_hiddenNonzero` ask nothing and are true (the empty set).
  `surjective_fderiv_preactivation` with no hidden unit is onto the zero space: true.
- **An empty batch.** `hiddenNonzero σ hid X k` is then the whole space: open, connected, with an
  empty complement. `jacobianRank` on the empty batch is `0`.
- **`L = 0`.** `ClaimZero … (Fin.last 0)` is Lemma D.5; the theorem holds (Check 3).
- **A hidden state with a zero row.** `SuffixFlatZero`, Lemma D.3 and part (c) ask their identity
  only where no row vanishes. Lemma D.17 (real `b`) and `flat_at_write_of_isOpen_rows` take their
  hypothesis at every `w̃` of the open set, also where `w̃V = 0` (there Lean's derivative may be
  `0`); a hypothesis at more points makes a weaker statement, and whoever uses the lemma has to
  give it there. Lemma D.18 (`claimZero_castSucc_tanh`, proved) gives it on a small set around
  `s̄`, where `s̄V ≠ 0`.
- **A parameter that is not regular.** `ClaimZero` at a `θ` without (R2) uses Mathlib's derivative
  where `𝓑_{>k}` is not differentiable; nothing is stated about `ClaimZero` at such a `θ` except
  `claimZero_last`, where no block comes after the hidden state.

### (b) Do the docstrings say honestly what part of the paper each piece is?

Yes. They quote the paper, give the numbering (`k : Fin L` is the paper's block `k + 1`), say "T
rows", say "for a real `b`" (Lemma D.17), "one removal" and "regular zero sets" (Lemma D.20), "the
paper's `h_0, …, h_{ℓ−1}`" (`Depth/HiddenZero.lean`), "the codimensions here are the number of
hidden units of the block (at least two) and `d ≥ 2`" (`Depth/DomainZeroConnected.lean`), and that
`rmsNorm 0` maps a zero row to `0`. Three places could say more; none is wrong:

1. `Depth/SuffixZeroClaim.lean`, header: "at an input where the output is not differentiable in the
   parameters Lean takes the derivative to be `0`, which asks nothing of a direction". True, and
   not the whole of it: at an input at which the paper's network is not defined and Lean's total
   function is differentiable (an input with a zero row), Lean's `flat` does ask something, and
   `funDim` counts the batch (Check 2, kind (c)).
2. `ae_funDim_tanh_skipless_rmsNorm_zero`, docstring: it does not say "at least one token", and
   does not say that `funDim` is that of the total network.
3. `funDim_add_le_skipless_rmsNorm_zero` and the file header say "at every parameter"; the bound
   has the hypotheses "`E` and every write have rank `d`", which the docstring of the theorem
   gives. "At every parameter" there means "with no hypothesis of differentiability".

### (c) Do the pieces fit?

**Yes, by compiling** (`Fit8.lean`, three theorems of my own with the statements of
`Depth/TanhZero.lean` word for word, proved from the other statements; three standard axioms at
`244ec8a`):

- `claimZero_of_tanh_path` from `claimZero_last` (with `hθ.rank_D`) and `claimZero_castSucc_tanh`,
  by induction from `L` down. The hypothesis `hblocks` has the form of the conclusion of
  `exists_regularZero_tanh_path`, clause for clause: (S1), (S2), `∃ κ, 0 < κ ∧ HolomorphicOnCone
  Complex.tanh θ k.succ κ ∧ CondS3 θ k κ`.
- `exists_jacobianRank_tanh_rmsNorm_zero` from `exists_regularZero_tanh_path`,
  `claimZero_of_tanh_path` at `k = 0` and `exists_batch_jacobianRank_of_claimZero`. The two
  clauses that the batch statement does not give follow: an input with `xE` without a zero row has
  no zero row; and `θ ∈ O_X` by (R2), one hidden state after the other
  (`rmsNorm_zero_dotProduct_self`, `RegularZero.block_ne_zero`).
- `ae_funDim_tanh_skipless_rmsNorm_zero` from that statement, the four statements of Lemma D.20
  (`isOpen_hiddenNonzero`, `isPreconnected_hiddenNonzero`, `measure_compl_hiddenNonzero`,
  `analyticOnNhd_evalBatch_hiddenNonzero`, with `tanh z = 0 ↔ z = 0` and "at least two hidden
  units" from `2 ≤ d ≤ d_hidden`), `ae_jacobianRank_ge_of_isPreconnected`,
  `jacobianRank_le_funDim` and the bound `ae_funDim_add_le_skipless_rmsNorm_zero`.

By reading: `CondS3` is the paper's (S3) clause for clause (unit row `ξ₀`, `ρ ∈ (0, 1]`, every
`ξ₀c_j ≠ 0`, the complex rows `w̃V` with `|w̃_j − s_j| ≤ ρ` in the cone, `e^{−2√d|ξ₀c_j|} < ρ/3`);
`complexCone κ` is `‖u'‖² < κ²‖u‖²`. The number `κ_ℓ` of Lemma D.14 is, in Lean, any `κ > 0` for
which `𝓑_{>k+1}` is holomorphic on `C_κ`, a hypothesis that `exists_regularZero_tanh_path`
gives. `TanhPathBlock` states (R2) and (R3) for one row; `RegularZero` states them with rows `T`;
see (d). I did not compare the other statements of `Depth/StepZeroTanh.lean`,
`Depth/TanhPathBlock.lean`, `Depth/RegularZeroTanh.lean` and the complex files with the paper
beyond this: they are not in this part.

### (d) Is `RegularZero` the paper's "regular" in the case (0)?

**Yes: for MLP blocks and at least one token, `RegularZero` holds if and only if the paper's (R1),
(R2), (R3) hold** (for the network of one token). An MLP block acts on every row alone: row `t` of
`g_ℓ(n)` is `g_ℓ` of the row `n_t`, and row `t` of `𝐃g_ℓ(n) v` is `𝐃g_ℓ(n_t) v_t`.

- (R1): `rank_E`, `rank_D`, `rank_write`. The same.
- (R2): `block_ne_zero : ∀ ℓ n, (∀ t, n t ⬝ᵥ n t = d) → ∀ t, (g_ℓ(n)) t ≠ 0`. From the paper's
  (R2), row by row; to the paper's (R2), with all rows of `n` equal to a given row of the sphere.
  By compiling (`Fit8b.lean`, `r2_iff`).
- (R3): `deriv_block : ∀ ℓ, ∃ n, (rows on the sphere) ∧ ∀ v, (∀ t, v t ⬝ᵥ n t = 0) → (∀ t, ∃ a,
  (𝐃g_ℓ(n) v) t = a • (g_ℓ(n)) t) → v = 0`. From the paper's (R3) at the row `n₀`: take all rows
  of `n` equal to `n₀`. To the paper's (R3): take a token `t₀` and `v` with the row `v₀` at `t₀`
  and `0` elsewhere; the paper's condition then holds at the row `n_{t₀}`. So Lean's `n` may have
  different rows at different tokens, and each of them is a row as in the paper's (R3). By
  reading; I did not compile this one.

With no token, (R2) and (R3) of `RegularZero` hold at every `θ`; the statements that matter have
`[Nonempty T]`. For an `Arch` whose blocks do not act row by row, `RegularZero` is a condition on
matrices that the paper does not have; Lemma D.2, D.3 and Proposition D.4 are proved in Lean for
it, which is more than the paper states.

---------------------------------------------------------------------------------------------------

## What the authors should know

Nothing false, nothing vacuous, nothing drifted, nothing misdescribed. In order of weight:

1. **The final statement is about Lean's `funDim`, which counts every batch on the total network.**
   It gives the paper's upper bound at almost every `θ` (Lean's value is at least the paper's). The
   paper's lower bound, "the rank (13) on a batch of inputs at which the network is defined", is
   what the proof shows, but the final statement does not say it: a batch that attains Lean's
   maximum could in principle contain an input of the kind (c) of Check 2. The public statements
   give it: there is one batch `X`, with no zero row in any input, such that for almost every `θ`,
   `θ ∈ O_X` and the rank on `X` is (13) (`Fit8b.lean`, `fit4`, compiled from
   `exists_jacobianRank_tanh_rmsNorm_zero`, the statements of Lemma D.20,
   `ae_jacobianRank_ge_of_isPreconnected` and the bound). I suggest adding this as a public
   statement beside the theorem, as the index does for ReLU blocks ("the value of `funDim`, and a
   batch of the paper's inputs with that rank"). With it, the pair is the paper's Theorem 5.2 (i)
   for `ε = 0` with no gap.
2. **Whether the Lean `funDim` can be larger than the paper's functional dimension at some `θ`
   for `ε = 0` is open** (Check 2). I found no example. It matters only at parameters of a null
   set.
3. One hypothesis more than the paper: at least one token. The statement also covers `L = 0`.
4. Lemma D.20 is stated for every real-analytic activation that vanishes exactly at `0`, with "at
   least two hidden units per block". The paper's proof says that `{N(h_{ℓ−1}) W_read^ℓ = 0}` has
   "codimension at least `d_model`"; its codimension is the number of hidden units of the block,
   which is at least `d_model` by the Scope. Lean's hypothesis is the weaker one.
5. Theorem 4.3 for `ε = 0` is stronger in Lean than in the paper (arbitrary maps `f_ℓ`, every
   parameter with the rank conditions).
6. Lemma D.17 in `Depth/StepZeroValues.lean` is for a real `b`; the lemma for a complex `b` is in
   a file of the other part.
7. The three places of (b) where a docstring could say more.

## Corrections for `STATEMENTS.md` (lines at `244ec8a`)

The rows of the 16 files (lines 158 to 161, 165 to 167, 170, 173 to 176, 179 to 181, 183) say
what the statements say; the status "proved" is right at `244ec8a`. Stale or incomplete:

1. **Line 238:** "D eq. (14), for `ε > 0` (the case `ε = 0` is not stated)". It is stated:
   `fderiv_rmsNorm_zero_mul` (`Depth/StepZeroValues.lean`, the row at line 165). Replace the
   parenthesis by "(the case `ε = 0`: `fderiv_rmsNorm_zero_mul`)".
2. **Line 340** (note on Theorem 4.3): "Not stated: attention blocks, and the paper's form for
   `ε = 0`". The form for `ε = 0` is stated and proved (line 158). Keep "Not stated: attention
   blocks".
3. **Lines 357 to 361** (note "Pre-RMSNorm with `ε = 0`"): "The paper's bounds for `ε = 0` are not
   stated." They are, for the group `CO(d)`: `Dimension/UpperBoundRMSNormZero.lean`. The note
   should keep its first sentence (the statements "for every real `ε`" count the orthogonal group
   only), point to line 158, and add what Check 2 says, in the words of the note on ReLU blocks:
   for `ε = 0` the paper's network is defined where no row of a hidden state vanishes; Lean's
   `funDim` is the largest rank over the batches of inputs at which the total network is
   differentiable in `θ`; it is at least the paper's value at every `θ`; the theorem gives the
   value of `funDim`, and `exists_jacobianRank_tanh_rmsNorm_zero` with the statements of Lemma D.20
   gives a batch of the paper's inputs with that rank at almost every `θ`.
4. **Lines 373 to 376** ("Not stated yet from the main text"): remove "Theorem 4.3 … its form for
   `ε = 0`" and "Theorem 5.2 (i) for `ε = 0`"; both are proved. "Theorem 5.2 (ii) for `ε = 0`"
   stays (GELU blocks; also said at line 285).
5. **Lines 66 to 75** ("Not yet compared by such a reader"): the 16 files of this part are now
   compared: `Dimension/UpperBoundRMSNormZero.lean`, `Depth/SuffixZero.lean`,
   `Depth/SuffixZeroDeriv.lean`, `Depth/SuffixZeroClaim.lean`, `Depth/SuffixZeroBatch.lean`,
   `Depth/StepZeroValues.lean`, `Depth/SuffixRows.lean`, `Depth/RowsAux.lean`,
   `Depth/FlatAtWriteRows.lean`, `Generic/AnalyticZeroSetOn.lean`, `Dimension/GenericRankOn.lean`,
   `Generic/ConnectedCompl.lean`, `Depth/HiddenZero.lean`, `Depth/DomainZero.lean`,
   `Depth/DomainZeroConnected.lean`, `Depth/TanhZero.lean` (53 public names, none false, vacuous
   or changed in meaning). Of the other files of that list I read only the statements named in
   (c).
6. **Line 183** (Theorem 5.2 (i), `ε = 0`): add "at least one token", and "`fd` is `funDim` of
   Lean's total network (see the note on `ε = 0`)".
7. **Lines 159 and 161:** `claimZero_last`, `suffixFlatZero_of_flat_at_write`,
   `flat_le_cobDir_add_scaleDir_of_claimZero` and `funDim_of_claimZero` have "at least one token";
   the rows do not say it. Line 170: the same for `flat_at_write_of_isOpen_rows`.
8. **Line 167:** "the rows `ξ` … are dense (the set `P'`)": in Lean dense among all rows, in the
   paper among the unit rows of `P`. A word would do: "dense among all rows".

## What I could not check

- The proofs. I compared statements and definitions. That the 53 statements are proved I took
  from `#print axioms` against the compiled library of `/home/claude/lp/lean` at `244ec8a`, which
  its owner built; I did not build the library myself.
- Whether the Lean `funDim` can exceed the paper's functional dimension at some parameter for
  `ε = 0` (Check 2): searched by hand, not decided.
- The equivalence of (R3) of `RegularZero` with the paper's (R3): by reading only.
- The files of the chain that are not in this part (`Depth/StepZeroTanh.lean`,
  `Depth/StepZeroTanhPath.lean`, `Depth/TanhPathBlock.lean`, `Depth/RegularZeroTanh.lean`,
  `Depth/ComplexRMSNorm.lean`, `Depth/ComplexSuffix.lean`, `Depth/ComplexSuffixStep.lean`,
  `Depth/ComplexBlockIdentity.lean`, `Depth/ComplexOneSubSq.lean`, `Depth/PathSeparation.lean`):
  I read the statements that the final theorem uses (`claimZero_castSucc_tanh`, `CondS3`,
  `HolomorphicOnCone`, `complexCone`, `exists_regularZero_tanh_path`, `TanhPathBlock`,
  `exists_tanhPathBlock`) and compared `CondS3` with (S3); the rest I did not compare.
- The paper as a PDF: I read the text file; some displayed equations are broken there ((11), (18),
  (43)), and I read them with the Lean docstrings beside.
- The numerical check is in float64 on ten small networks; it agrees with the theorem and proves
  nothing.

## Files of this audit (`/home/claude/audit8a/`)

`snap/`, `snap2/` (the sources at `0dd64fe` and `244ec8a`); `scratch/Fit8.lean` (the three
statements of `Depth/TanhZero.lean` from the pieces), `scratch/Fit8b.lean` (`fit4`: the batch at
almost every parameter; `r2_iff`), `scratch/Ax8.lean` and `Ax8_final.out` (axioms of 62 names),
`scratch/Sig8.lean` and `Sig8.out` (the form of each statement); `stmts.py` (statement texts of
two commits compared); `py/rank_check.py`, `py/rank_check2.out` (the numerical check).
