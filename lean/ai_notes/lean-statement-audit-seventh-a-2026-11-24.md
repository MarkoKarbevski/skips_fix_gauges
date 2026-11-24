STATUS: complete

# Seventh audit of Lean statements against the skips paper, part A (24 November 2026)

Reader: an independent reader who did not write the statements. Brief:
`/home/claude/proj_up/audit7a_brief_2026-11-24.md`.

Library: `/home/claude/lw/lean` (branch `lean-wip`). Commit at the start:
`a969c4e29c25d6fc13b7b86cdae1dced0b4164ff`. Commit at the end:
`6c30ab8` (the branch moved four times while I read: `ab2d797`, `ee8874f`, `3f274a5`, `6c30ab8`).
Between the two (`git diff a969c4e 6c30ab8 --stat`): `STATEMENTS.md`, `SkipsLean.lean`,
`checks/Axioms.lean`, `Residual/FewerHiddenUnits.lean` and two new files,
`Dimension/UpperBoundRMSNormZero.lean` and `Depth/SuffixZero.lean`. None of the 15 files of this
part changed, and none of the 81 modules that they import. Their rows in `STATEMENTS.md` did not
change either; they moved down by three lines. Line numbers of `STATEMENTS.md` below are those of
the file at `ee8874f`, which is the same file at `6c30ab8`.

Paper: the skips paper as text (`skips.txt`; "S"). Statement and equation numbers are those of that
text.

How I checked.
- "By reading": I read the Lean source and the paper. I read every public statement, every
  definition and every docstring of the 15 files; of the proofs I read only the short ones of the
  final theorems and the comments of the long ones.
- "By compiling": I compiled scratch files of my own in `/home/claude/audit7a/` with `lean`
  (4.36.0). The compiled library of `/home/claude/lw` has none of the 15 files. So I used the
  compiled library of `/home/claude/lp/lean` through `LEAN_PATH`, without `lake`. Before that I
  checked (scripts `closure.py`, `Hash.lean`) that for each of the 81 modules in the import closure
  of the 15 files the source text in `lw` has the same Lake text hash as the one recorded in the
  build trace of `lp`. So the compiled statements are those of the sources that I read. I wrote
  nothing under `lw`, `lp` or the repository, and ran no `lake build`.
- "By a computation": a Python script in `/home/claude/audit7a/` (`rank_check.py`).

Short answer. **Nothing false, vacuous or drifted was found.** All 54 statements of this part
that state a generic claim are `∀ᵐ θ ∂μ` for an additive Haar measure `μ` on the parameters; the 12
for Lemma A.27 have the paper's form "for almost every `θ`, for all small `τ ≠ 0`". Every value
is stated with `funDim`. The 24 final statements of Theorem 4.6 (ii), Theorem 4.7 and Corollary 4.8
carry the paper's hypotheses and one more, at least one token. No `axiom`, no `sorry`: all 583
constants of the 15 files depend on the three standard axioms only. What differs from the paper is
coverage (no attention blocks; no ReLU-type blocks in Theorem 4.6 (ii); two of the four values of
Lemma A.27; no dimension count in Theorem 3.3 (ii)), and the index says it. Three notes of the
index are out of date (they say that the pre-RMSNorm statements do not exist), one sentence of its
"Not stated yet" paragraph is imprecise, and one file header claims slightly more than the file
has. See the two lists at the end.

---------------------------------------------------------------------------------------------------

## Part 1: three checks that the statements of this part have not drifted

### Check 1. "Generic parameters" is "for almost every parameter"

**Verdict: yes, in every statement of the 15 files.** No generic claim of the paper is formalized
as "there is a parameter" or "on a nonempty open set".

What I did (by compiling, `Forms.lean` and `FormsP.lean`): a program went through every theorem of
the 15 modules, public and private, took its statement apart and recorded the form of its
conclusion, whether a hypothesis is an a.e. statement, and whether it mentions `funDim`,
`jacobianRank` or `flat`. The 15 files have 98 public names: 89 theorems, 3 definitions
(`Params.smallWrites`, `smallWritesLimit`, `smallWritesLimitNorm`) and 6 structures. All 98 are in
the rows of `STATEMENTS.md` for these files, and these rows name nothing else (by a script).

| Form of the conclusion (89 public theorems) | Count |
|---|---|
| `∀ᵐ θ ∂μ, …` with `μ` a variable of the statement and `[μ.IsAddHaarMeasure]` for this `μ` | 54 |
| of these, `∀ᵐ θ ∂μ, ∀ᶠ τ in 𝓝[≠] 0, …` | 12 |
| `∀ᶠ τ in 𝓝[≠] 0, …` for a given `θ` | 8 |
| `∃ …` (a matrix `Y` or `X`, numbers `α`) | 8 |
| `↔` | 2 |
| other (equalities, implications) | 17 |

No theorem of the 15 files, public or private, has an a.e. statement as a hypothesis.

**The 54 generic statements.** In each, the quantifier over parameters is `∀ᵐ θ ∂μ`: the set of the
`θ` at which the statement fails has `μ`-measure zero. `μ` is any additive Haar measure on
`Params A dIn dOut`, which carries the Borel σ-algebra of its norm (`Generic/Params.lean:32-34`).
By compiling (`Fit.lean`, three examples, no `sorry`): any two such measures have the same sets of
measure zero; a linear change of coordinates `Params A dIn dOut ≃L[ℝ] (Fin P → ℝ)` carries `μ` to a
positive multiple of the Lebesgue measure of `ℝ^P`; and such a measure exists. So `∀ᵐ θ ∂μ` is the
paper's "outside a set of Lebesgue measure zero" (S Section 2).

| File | Count | Names |
|---|---|---|
| `OneBlock/ResidualRMSMlp.lean` | 4 | `ae_oneBlockGenericRMS`, `ae_funDim_mlp_oneBlock_residual_rmsNorm`, `ae_funDim_tanh_oneBlock_residual_rmsNorm`, `ae_funDim_gelu_oneBlock_residual_rmsNorm` |
| `OneBlock/ResidualRMSGated.lean` | 4 | `ae_oneBlockGenericGatedRMS`, `ae_funDim_gated_oneBlock_residual_rmsNorm`, `ae_funDim_swiglu_oneBlock_residual_rmsNorm`, `ae_funDim_geglu_oneBlock_residual_rmsNorm` |
| `OneBlock/ResidualRMSGain.lean` | 6 | `ae_funDim_skipless_add_le_K_oneBlock_residual_rmsNorm` for `K` = `mlp`, `tanh`, `gelu`, `gated`, `swiglu`, `geglu` |
| `Residual/DepthMlp.lean` | 7 | `ae_smallWritesGeneric`; `ae_eventually_funDim_smallWrites_K` and `ae_funDim_K_residual` for `K` = `mlp`, `tanh`, `gelu` |
| `Residual/DepthGated.lean` | 7 | `ae_smallWritesGenericGated`; `ae_eventually_funDim_smallWrites_K` and `ae_funDim_K_residual` for `K` = `gated`, `swiglu`, `geglu` |
| `Residual/ExactGain.lean` | 6 | `ae_funDim_skipless_add_le_residual_K` for `K` = `mlp`, `gelu`, `gated`; `ae_funDim_K_residual_eq_add` for `K` = `tanh`, `swiglu`, `geglu` |
| `Residual/DepthMlpRMS.lean` | 7 | `ae_smallWritesGenericRMS`; `ae_eventually_funDim_smallWrites_K_rmsNorm` and `ae_funDim_K_residual_rmsNorm` for `K` = `mlp`, `tanh`, `gelu` |
| `Residual/DepthGatedRMS.lean` | 7 | `ae_smallWritesGenericGatedRMS`; `ae_eventually_funDim_smallWrites_K_rmsNorm` and `ae_funDim_K_residual_rmsNorm` for `K` = `gated`, `swiglu`, `geglu` |
| `Residual/ExactGainRMS.lean` | 6 | `ae_funDim_skipless_add_le_residual_K_rmsNorm` for `K` = `mlp`, `gated`; `ae_funDim_K_residual_rmsNorm_eq_add` for `K` = `tanh`, `gelu`, `swiglu`, `geglu` |

One of them in full (elaborated, `Chk.lean`):

```
ae_funDim_tanh_residual_rmsNorm : ∀ {T d dIn dOut} {L : ℕ} [Fintype T] [Nonempty T] [Fintype d]
  [DecidableEq d] [Fintype dIn] [Fintype dOut] {hid : Fin L → Type} [(ℓ : Fin L) → Fintype (hid ℓ)]
  {ε : ℝ}, 0 < ε →
  ∀ (μ : MeasureTheory.Measure (Params (Arch.mlp Real.tanh (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure],
  2 ≤ Fintype.card d → Fintype.card d ≤ Fintype.card dIn → Fintype.card d ≤ Fintype.card dOut →
  ∀ᵐ (θ : Params (Arch.mlp Real.tanh (rmsNorm ε) hid) dIn dOut) ∂μ,
    funDim (Arch.mlp Real.tanh (rmsNorm ε) hid) 1 θ + Fintype.card d * (Fintype.card d - 1) / 2 =
      Module.finrank ℝ (Params (Arch.mlp Real.tanh (rmsNorm ε) hid) dIn dOut)
```

**Statements "for all small `τ ≠ 0`", and the paper's form.** S Lemma A.27: "For generic parameters
`θ` … and a number `τ`, let `θ_τ` … For all small `τ ≠ 0`, the residual network has `fd(θ_τ) = …`".

| Lean | Form | Paper's form |
|---|---|---|
| the 12 `ae_eventually_funDim_smallWrites_…` (`K` = `mlp`, `tanh`, `gelu`, `gated`, `swiglu`, `geglu`, without and with `_rmsNorm`) | `∀ᵐ θ ∂μ, ∀ᶠ τ in 𝓝[≠] (0 : ℝ), funDim … 1 (θ.smallWrites τ) + … = finrank …` | the same: for almost every `θ` there is a `δ > 0` (it may depend on `θ`) with the value at every `τ ≠ 0`, `\|τ\| < δ`. By compiling (`Fit.lean`): `(∀ᶠ τ in 𝓝[≠] 0, p τ) ↔ ∃ δ > 0, ∀ τ, τ ≠ 0 → \|τ\| < δ → p τ` |
| `eventually_funDim_smallWrites_mlp`, `…_gated`, `…_mlp_rmsNorm`, `…_gated_rmsNorm` | for every `θ` with the named conditions (`SmallWritesGeneric θ`, …): `∀ᶠ τ in 𝓝[≠] 0, funDim … (θ.smallWrites τ) + … = finrank …` | the lemma under the conditions that its proof calls generic; each has the `ae_` statement above, and an `ae_` statement that the conditions hold almost everywhere |
| `eventually_funDim_smallWrites_ge`, `eventually_funDim_smallWrites_ge_norm` | for every `θ` and every subspace `V` that contains the directions flat for `J_0`: `∀ᶠ τ in 𝓝[≠] 0, finrank … ≤ funDim … (θ.smallWrites τ) + finrank V` | the paragraph "The rank": "for all small `τ ≠ 0`, `rank J_τ = rank(J_τ S_τ) ≥ rank J_0 = P − m`". Not a generic claim |
| `eventually_finrank_range_le_of_small_parameter`, `eventually_finrank_le_of_small_parameter` | the same step for a map `G τ θ`, no networks | the same paragraph |

**Existence statements.** Eight statements have `∃` at the head. None of them is "there is a
parameter". Each says, for every `θ` with stated conditions and every flat direction `η`, that
there is a matrix (and numbers `α`) that describes `η`: `exists_antisymm_of_flat_residual_rmsNorm`,
`flat_le_cobDir_const_mlp_residual_rmsNorm`,
`flat_le_cobDir_const_add_rescaleDir_gated_residual_rmsNorm`, `smallWritesLimit_eq_zero_mlp`,
`smallWritesLimit_eq_zero_gated`, `exists_antisymm_of_smallWritesLimitNorm_rmsNorm`,
`smallWritesLimitNorm_eq_zero_mlp_rmsNorm`, `smallWritesLimitNorm_eq_zero_gated_rmsNorm`. The paper
has the same form in these places ("the unique `D_θ h_1 η` with … is `h_1 Y + …`"; "`ψ_M = 0` gives
`η_E = E X` and `η_D = −X D` for some `X`").

**Where a proof takes one parameter.** The proofs of Theorem 4.7 (`ae_funDim_mlp_residual` and the
three like it) take one `θ₀` with the conditions and one small `τ`, as the paper's proof does
("Lemma A.27 gives parameters and a finite batch on which it equals `r`"), and pass to almost every
`θ` by `ae_funDim_ge` (`∀ᵐ θ ∂μ, funDim A S θ₀ ≤ funDim A S θ`) and the upper bound. The
conclusion is the a.e. statement (by reading the proofs, `Residual/DepthMlp.lean:390-399`).

### Check 2. The functional dimension is `max_X rank DF_X(θ)` over all finite batches

**Verdict: yes.** Every value of this part is stated with `funDim`, and no statement of the 15
files puts another quantity in its place.

- `Dimension/Functional.lean` did not change since the sixth audit (`git diff 31752fa ab2d797` is
  empty for it, and it did not change after; so are `Network/*`, `Basic/*`, `Generic/*`, `Dimension/Space.lean`). There
  (by reading):
  ```
  noncomputable def jacobianRank {n : ℕ} (X : Fin n → Matrix T dIn ℝ) (θ : Params A dIn dOut) : ℕ :=
    Module.finrank ℝ (LinearMap.range (fderiv ℝ (evalBatch A S X) θ).toLinearMap)
  noncomputable def funDim (θ : Params A dIn dOut) : ℕ :=
    sSup {r : ℕ | ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), r = jacobianRank A S X θ}
  ```
  the supremum, a maximum, of the rank of the Jacobian over all `n` and all batches of `n` inputs
  (S Definition 4.1). The networks of this part are tanh, GELU, SwiGLU and GeGLU blocks without
  normalization or under pre-RMSNorm with `ε > 0`; they are differentiable in `θ` at every input,
  so nothing is dropped (sixth audit, Check 2).
- By compiling (`Forms.lean`): of the 89 public theorems, 56 mention `funDim` (all the values,
  bounds and gains), none mentions `jacobianRank`, 3 mention `flat` (`K(θ)`, as the hypothesis
  "`η` is flat"). The other statements are about the limit `J_0` (`smallWritesLimit … = 0` at every
  input `x`, the paper's "flat for `J_0`"), about changes of basis (Lemma A.4), or about a map
  without networks (`Residual/SmallParameter.lean`, where the rank is
  `Module.finrank ℝ (LinearMap.range (fderiv ℝ (G τ) θ).toLinearMap)`, the rank of a derivative).
- The residual network is `funDim A 1 θ` and the skipless one `funDim A 0 θ`. By compiling
  (`Fit.lean`): `(1 : Fin L → Matrix d d ℝ) ℓ = 1`; for one tanh block
  `eval (Arch.mlp Real.tanh (rmsNorm ε) hid) 1 θ x = rmsNorm ε (x * θ.E + (rmsNorm ε (x * θ.E) * θ.read 0).map Real.tanh * θ.write 0) * θ.D`,
  the residual network of S Appendix B; with `0` the term `x * θ.E` is absent (checked for one
  SwiGLU block); and `θ.smallWrites τ` changes the writes to `τ • θ.write ℓ` and nothing else.
- The gains compare the two networks at the same `θ`, for almost every `θ`
  (`funDim … 0 θ + L * … ≤ funDim … 1 θ`, or `=`).
- By a computation (`rank_check.py`, double precision, `d = 3`, one token, random weights and
  inputs, the rank read off at a gap of at least 9 orders of magnitude): the numerical rank of the
  Jacobian equals the value of the Lean statement in 13 cases, among them blocks narrower than `d`
  (one tanh block of 2 units under RMSNorm: 27 = `P − 3`; one SwiGLU block of 1 unit: 26 =
  `P − 3 − 1`; tanh, widths (1,2), no normalization: 27 = `P − 9`; GeGLU, widths (2,1), RMSNorm:
  39 = `P − 3 − 3`) and `θ_τ` with `τ = 0.05`. This is a check of the paper's formula for the
  network, not of Lean.

### Check 3. Theorem 4.6 (ii), Theorem 4.7 and Corollary 4.8 carry no hypothesis that the paper does not have

**Verdict: none, except "at least one token" (`[Nonempty T]`), which the paper has implicitly.**
The statements of the equality (Theorem 4.6 (ii), first sentence; Theorem 4.7, first sentence) need
less than the main text: no condition on the widths of the blocks, as in the appendix statements
(Theorem B.1 (ii), Lemma A.27 "of any width").

The paper. Setup (S Section 2): "RMSNorm with the constant `ε > 0`"; "Networks have no biases, and
their inputs range over all of `ℝ^{T×d_in}`. Every MLP block has `d_hidden ≥ d_model`, and all MLP
blocks are of one kind. … The input and the output satisfy `d_in, d_out ≥ d_model ≥ 2`"; "A
statement holds at generic parameters if it holds outside a set of Lebesgue measure zero".
Theorem 4.6: "Let `L = 1` … (ii) Under RMSNorm, the residual network satisfies the equality
condition, and the skip raises the functional dimension by at least `d_model(d_model − 1)/2`."
Theorem 4.7: "Let the blocks be analytic, with or without pre-RMSNorm. The residual network
satisfies the equality condition: at generic parameters its functional dimension is
`P − dim 𝒢 − s`. So the skips raise the functional dimension by at least `L dim 𝒢`, and by exactly
`L dim 𝒢` when the skipless network satisfies the equality condition too." Corollary 4.8: "Let all
blocks be tanh blocks, all SwiGLU blocks or all GeGLU blocks, with or without pre-RMSNorm, or all
GELU blocks under pre-RMSNorm. At generic parameters, the skips raise the functional dimension by
exactly `L dim 𝒢`".

The 24 final Lean statements, with all their hypotheses (by compiling, `Chk.lean`: the program
prints every binder; the six groups below have word for word the same list inside each group).

| Lean hypothesis | In which of the 24 | In the paper |
|---|---|---|
| `[Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut]`, `hid` with `[∀ ℓ, Fintype (hid ℓ)]` | all | Setup: finitely many tokens, coordinates and hidden units. All blocks have one activation: "all MLP blocks are of one kind" |
| `[Nonempty T]` | all | not said; an input has at least one token. Needed: with no token the functional dimension is 0 |
| `hid : Fin 1 → Type` | the 8 of Theorem 4.6 (ii) | "Let `L = 1`" |
| `L : ℕ`, `hid : Fin L → Type` | the 16 of Theorem 4.7 and Corollary 4.8 | any depth (`L = 0` is allowed in Lean and harmless) |
| `hε : 0 < ε` | the 16 with `rmsNorm ε` | Setup: "the constant `ε > 0`" |
| `(μ) [μ.IsAddHaarMeasure]`, conclusion `∀ᵐ θ ∂μ` | all | "at generic parameters" |
| `hd : 2 ≤ Fintype.card d` | all | Scope: `d_model ≥ 2` (Theorem B.1, Lemma A.27: "Let `d_model ≥ 2`") |
| `hdIn : card d ≤ card dIn`, `hdOut : card d ≤ card dOut` | all | Scope: `d_in, d_out ≥ d_model` (Theorem B.1; Lemma A.27: "`E` and `D` have rank `d_model`") |
| `hhid : ∀ ℓ, card d ≤ card (hid ℓ)` | the 12 gains only | Scope: `d_hidden ≥ d_model`; Theorem B.1 (ii): "If the block has width at least `d_model`"; proof of Theorem 4.7: "When every block has width at least `d_model`" |

| Paper | Lean names (final statements) | Conclusion `∀ᵐ θ ∂μ, …` | Hypotheses beyond the first two rows |
|---|---|---|---|
| Theorem 4.6 (ii), first sentence | `ae_funDim_K_oneBlock_residual_rmsNorm`, `K` = `tanh`, `gelu`, `swiglu`, `geglu` | `funDim … 1 θ + card d * (card d - 1) / 2 = finrank …`; gated: `+ (card d * (card d - 1) / 2 + card (hid 0))` | `hε`, `μ`, `hd`, `hdIn`, `hdOut` |
| Theorem 4.6 (ii), the gain | `ae_funDim_skipless_add_le_K_oneBlock_residual_rmsNorm`, the same four `K` | `funDim … 0 θ + card d * (card d - 1) / 2 ≤ funDim … 1 θ` | the same and `hhid` |
| Theorem 4.7, first sentence, no normalization | `ae_funDim_K_residual`, `K` = `tanh`, `gelu`, `swiglu`, `geglu` | `funDim … 1 θ + card d ^ 2 = finrank …`; gated: `+ (card d ^ 2 + ∑ ℓ, card (hid ℓ))` | `μ`, `hd`, `hdIn`, `hdOut` |
| Theorem 4.7, first sentence, pre-RMSNorm | `ae_funDim_K_residual_rmsNorm`, the same four `K` | as Theorem 4.6 (ii), with `∑ ℓ, card (hid ℓ)` | `hε`, `μ`, `hd`, `hdIn`, `hdOut` |
| Theorem 4.7, "at least `L dim 𝒢`", where the gain is not exact | `ae_funDim_skipless_add_le_residual_gelu` (GELU, no normalization) | `funDim … 0 θ + L * card d ^ 2 ≤ funDim … 1 θ` | `μ`, `hd`, `hdIn`, `hdOut`, `hhid` |
| Corollary 4.8, no normalization | `ae_funDim_K_residual_eq_add`, `K` = `tanh`, `swiglu`, `geglu` | `funDim … 1 θ = funDim … 0 θ + L * card d ^ 2` | `μ`, `hd`, `hdIn`, `hdOut`, `hhid` |
| Corollary 4.8, pre-RMSNorm | `ae_funDim_K_residual_rmsNorm_eq_add`, `K` = `tanh`, `gelu`, `swiglu`, `geglu` | `funDim … 1 θ = funDim … 0 θ + L * (card d * (card d - 1) / 2)` | `hε`, `μ`, `hd`, `hdIn`, `hdOut`, `hhid` |

`d (d − 1)` is even, so the division of natural numbers is exact. `s` is the number of hidden units
for SwiGLU and GeGLU blocks and 0 for tanh and GELU blocks, as in the paper (S proof of
Theorem B.1, Step 3). No hypothesis mentions Lemma B.3, analyticity, a batch, a rank, or a
condition on `θ`: in the general statements these are `hσ`, `hσa`, `hU : UnitsRigid …` or
`GatedUnitsRescale …`, and the statements for the four kinds discharge them with proved statements
(`hasDerivAt_tanh`, `analyticOnNhd_tanh`, `tanh_unitsRigid`, and the like; by reading the
one-line proofs).

**No hypothesis restates a conclusion.** `UnitsRigid σ σ' n k q` and `GatedUnitsRescale σ σ' n k q`
are the conclusion of Lemma B.3 as a property of the activation (they were compared in earlier
audits and their files did not change). They are hypotheses of the general statements only, and
they are not the conclusion of those statements (a value of `funDim`, or the form of a flat
direction).

**Axioms and `sorry`.**
- `grep -rn "^axiom" SkipsLean` at `6c30ab8`: no line.
- `grep -w` for `sorry`, `admit`, `native_decide`, `unsafe`, `opaque` in the 15 files: no line. In
  the whole library at `6c30ab8` the only `sorry` are four in the new file `Depth/SuffixZero.lean`,
  which is not in this part, is imported by none of the 15 files, and is marked "in work" in the
  index.
- By compiling (`Ax.lean`: `Lean.collectAxioms` on every constant of the 15 modules, public,
  private and generated): 583 constants, 507 of them theorems; every one depends on `propext`,
  `Classical.choice`, `Quot.sound` only; none is an axiom or an opaque constant. This covers
  everything that the proofs use from other files. In particular the four statements of
  Corollary 4.8 under pre-RMSNorm no longer rest on a `sorry`: the three statements of Theorem 5.2
  of the dimension paper that did at the sixth audit (`ae_funDim_gelu_skipless_rmsNorm`,
  `ae_funDim_swiglu_skipless_rmsNorm`, `ae_funDim_geglu_skipless_rmsNorm`) are proved now, and
  their file `Depth/GeluGatedTheorem.lean` did not change.

---------------------------------------------------------------------------------------------------

## Part 2: the statements, file by file

### Verdict table

"Piece" marks a statement that is a step of a proof and not a statement of the paper. "Proved"
below always means: compiled, with the three standard axioms (by compiling, `Ax.lean`).

| # | Paper | Lean | Verdict | The difference |
|---|---|---|---|---|
| 1 | S Lemma A.4, fact (b) for a vanilla block and for a gated block | `eq_of_forall_map_dotProduct_eq`, `eq_of_forall_gate_mul_eq` | SAME | Stated for any `σ` with the properties that the paper's argument uses (continuous, not even, not constant; gate not identically zero and `σ(z) = κσ(κz)` for all `z` only for `κ = 1`). Fact (b) for an attention block is not stated |
| 2 | S Lemma A.4, "None of tanh, GELU, ReLU and ReLU² is even or constant"; the ReLU, SiLU and GELU gates | `tanh_not_even_not_const`, `gelu_…`, `relu_…`, `reluSq_…`; `relu_gate_scale`, `silu_gate_scale`, `gelu_gate_scale` | SAME | Each also states continuity, resp. that the gate is not identically zero |
| 3 | S Lemma A.4 for tanh, GELU, ReLU, ReLU² blocks and for ReGLU, SwiGLU, GeGLU blocks | `orthogonal_of_eval_cob_skipless_rmsNorm_mlp`, `…_gated` | LEAN STRONGER | Lean needs one token, `d_in, d_out ≥ 1`, one hidden unit per block and any `d`; the paper's scope has `d_in, d_out, d_hidden ≥ d ≥ 2`. The lemma for each of the seven kinds is the general statement applied to the facts of row 2; it is not a named theorem (it compiles, `Fit.lean`) |
| 4 | S Lemma A.4 for attention blocks | none | PART | Not stated (no attention blocks in the library). The index says so |
| 5 | S Theorem 3.3 (ii), Theorem A.14 (ii), Theorem A.17 (i): which changes of basis preserve a skipless network under pre-RMSNorm (`ε > 0`) | `eval_cob_skipless_rmsNorm_iff_mlp`, `…_iff_gated` | PART | "Preserves the function at all parameters iff every `G_ℓ` is orthogonal" is stated (A.14 (ii): "are orthogonal"). "They form a group of dimension `(L+1) d(d−1)/2`" is not a Lean statement. The index says so |
| 6 | S proof of Theorem B.1 (ii), Steps 1 to 3 | `exists_antisymm_of_flat_residual_rmsNorm` | Piece, SAME | For any continuously differentiable `f` on hidden states of `T` tokens: this covers tanh, GELU, SwiGLU, GeGLU and ReLU² blocks, not ReLU and ReGLU blocks, for which the paper runs the same steps at the inputs away from the kinks |
| 7 | S proof of Theorem B.1 (ii), the conditions "for generic parameters" | `OneBlockGenericRMS`, `OneBlockGenericGatedRMS`, `ae_oneBlockGenericRMS`, `ae_oneBlockGenericGatedRMS` | SAME | See note (d). Lean leaves out two of the paper's generic conditions that the proof of part (ii) does not use (`W_read`, `W_write` of rank `d`; the value weights not proportional to the gate weights) |
| 8 | S proof of Theorem B.1 (ii), Step 4 | `flat_le_cobDir_const_mlp_residual_rmsNorm`, `flat_le_cobDir_const_add_rescaleDir_gated_residual_rmsNorm` | Piece, SAME statement, different route | The paper passes from the ball to all inputs along lines; Lean uses that the image of `x ↦ N_ε(xE)` contains a neighbourhood of `0` and the identity theorem. The header of the file says it |
| 9 | S proof of Theorem B.1 (ii), Step 5 (the value under the conditions) | `funDim_mlp_oneBlock_residual_rmsNorm`, `funDim_gated_oneBlock_residual_rmsNorm` | Piece, SAME | |
| 10 | **S Theorem 4.6 (ii), first sentence; Theorem B.1 (ii), first sentence**, tanh, GELU, SwiGLU, GeGLU | `ae_funDim_mlp_oneBlock_residual_rmsNorm`, `ae_funDim_gated_oneBlock_residual_rmsNorm` (general), `ae_funDim_K_oneBlock_residual_rmsNorm` for the four `K` | SAME as B.1 (ii); LEAN STRONGER than 4.6 (ii) | No condition on the width of the block, as in B.1 (ii); the main text has `d_hidden ≥ d` |
| 11 | **S Theorem 4.6 (ii), the gain; Theorem B.1 (ii), last sentence** | the six of `OneBlock/ResidualRMSGain.lean` | SAME | |
| 12 | S Theorem 4.6 (ii) for ReLU, ReLU², ReGLU and attention blocks; its sentence on a learned skip | none | PART | Not stated. The index says so |
| 13 | S proof of Lemma A.27, "`J_0 = lim J_τ S_τ`" and "The rank" | `eventually_finrank_range_le_of_small_parameter`, `eventually_finrank_le_of_small_parameter` | Piece, DIFFERENT route, true | No networks. The limit is a mixed second derivative of `G(τ, θ)`; no expansion in `τ`, no inverse. See note (a) for why it is the paper's `J_τ S_τ` |
| 14 | S Lemma A.27, `θ_τ`; the expansion of `y`; `J_0`; "The rank" (no normalization) | `Params.smallWrites`, `eval_smallWrites_zero`, `hasDerivAt_eval_smallWrites`, `smallWritesLimit`, `eventually_funDim_smallWrites_ge` | Piece, SAME | `smallWritesLimit` is the paper's `(J_0 η)(x)` with `ψ_M = η_E D + E η_D`, `ψ_C = E η_read`, `ψ_A = η_write D`, for any differentiable `f_ℓ` (compared term by term) |
| 15 | S proof of Lemma A.27, the directions flat for `J_0`, MLP blocks and gated blocks, no normalization | `SmallWritesGeneric`, `SmallWritesGenericGated`, `smallWritesLimit_eq_zero_mlp`, `smallWritesLimit_eq_zero_gated` | Piece, SAME | |
| 16 | **S Lemma A.27, first value**, tanh, GELU, SwiGLU, GeGLU | `eventually_funDim_smallWrites_mlp`, `…_gated`, `ae_smallWritesGeneric`, `ae_smallWritesGenericGated`, `ae_eventually_funDim_smallWrites_K` for the six `K` | SAME for these blocks | Form "for almost every `θ`, for all small `τ ≠ 0`". The paper's "let `E` and `D` have rank `d`" is `d_in, d_out ≥ d` together with "almost every" |
| 17 | S proof of Lemma A.27, "Under pre-RMSNorm": the expansion, `J_0`, "The rank" | `eval_smallWrites_zero_norm`, `hasDerivAt_eval_smallWrites_norm`, `smallWritesLimitNorm`, `eventually_funDim_smallWrites_ge_norm` | Piece, LEAN STRONGER | For any differentiable (resp. real-analytic) `χ` in the place of `N_ε`. `smallWritesLimitNorm` is the paper's `𝐃N_ε(h)(x η_E + D_θ g(n) η) D + N_ε(h) η_D` |
| 18 | S proof of Lemma A.27, "Under pre-RMSNorm", Steps 1 to 3 | `exists_antisymm_of_smallWritesLimitNorm_rmsNorm` | Piece, SAME | For continuously differentiable `f_ℓ`. The direction `η^Y` has entries at `E` and `D` only, as the paper says |
| 19 | S proof of Lemma A.27, "Under pre-RMSNorm", Steps 4 and 5 | `SmallWritesGenericRMS`, `SmallWritesGenericGatedRMS`, `smallWritesLimitNorm_eq_zero_mlp_rmsNorm`, `…_gated_rmsNorm` | Piece, SAME | Route of Step 4 as in row 8 |
| 20 | **S Lemma A.27, second value**, tanh, GELU, SwiGLU, GeGLU | `eventually_funDim_smallWrites_mlp_rmsNorm`, `…_gated_rmsNorm`, `ae_smallWritesGenericRMS`, `ae_smallWritesGenericGatedRMS`, `ae_eventually_funDim_smallWrites_K_rmsNorm` for the six `K` | SAME for these blocks | |
| 21 | S Lemma A.27, third and fourth value (biases; no `E`, `D`); attention blocks | none | PART | Not stated |
| 22 | **S Theorem 4.7, first sentence**, tanh, GELU, SwiGLU, GeGLU, without normalization and under pre-RMSNorm | `ae_funDim_mlp_residual`, `ae_funDim_gated_residual`, `…_rmsNorm` (general); `ae_funDim_K_residual`, `ae_funDim_K_residual_rmsNorm` for the four `K` | SAME; LEAN STRONGER in the widths | No condition on the widths (Lemma A.27: "of any width"). Attention blocks are not stated |
| 23 | **S Theorem 4.7, "at least `L dim 𝒢`"** | `ae_funDim_skipless_add_le_residual_mlp`, `…_gelu`, `…_gated`, `…_mlp_rmsNorm`, `…_gated_rmsNorm` | SAME | With widths at least `d`, as in the paper's proof |
| 24 | S Theorem 4.7, "by exactly `L dim 𝒢` when the skipless network satisfies the equality condition too" | none as a conditional | PART | Its instances are the seven statements of row 25. Neither the file headers nor the index claim more, but the index does not say that the conditional itself is not stated |
| 25 | **S Corollary 4.8**, its seven cases | `ae_funDim_K_residual_eq_add` (`tanh`, `swiglu`, `geglu`); `ae_funDim_K_residual_rmsNorm_eq_add` (`tanh`, `gelu`, `swiglu`, `geglu`) | SAME | |

### (a) Are the pieces true as written?

Every statement of the 15 files is proved (compiled, three standard axioms, no `sorry`). So a
statement could be wrong only through a definition that is not the paper's object, or be empty
through hypotheses that cannot hold. I looked for both.

- **The definitions.** `Params.smallWrites` (`E`, the reads and `D` of `θ`, the writes
  `τ • θ.write ℓ`) is `θ_τ`. `smallWritesLimit` and `smallWritesLimitNorm` are the paper's
  `(J_0 η)(x)` (rows 14 and 17; compared term by term, by reading):
  ```
  noncomputable def smallWritesLimit (A : Arch T d L) (θ η : Params A dIn dOut)
      (x : Matrix T dIn ℝ) : Matrix T dOut ℝ :=
    x * (η.E * θ.D + θ.E * η.D)
      + ∑ ℓ, (fderiv ℝ (A.f ℓ) (x * θ.E * θ.read ℓ) (x * θ.E * η.read ℓ) * θ.write ℓ
          + A.f ℓ (x * θ.E * θ.read ℓ) * η.write ℓ) * θ.D
  noncomputable def smallWritesLimitNorm (A : Arch T d L) (θ η : Params A dIn dOut)
      (x : Matrix T dIn ℝ) : Matrix T dOut ℝ :=
    fderiv ℝ A.χ (x * θ.E)
        (x * η.E + ∑ ℓ, (fderiv ℝ (A.f ℓ) (A.χ (x * θ.E) * θ.read ℓ) (A.χ (x * θ.E) * η.read ℓ)
              * θ.write ℓ
            + A.f ℓ (A.χ (x * θ.E) * θ.read ℓ) * η.write ℓ)) * θ.D
      + A.χ (x * θ.E) * η.D
  ```
  They are definitions, and Lean has no separate statement "`J_τ S_τ → J_0`" for networks; that
  they are the limit is used inside the proofs of `eventually_funDim_smallWrites_ge` and
  `…_ge_norm`. I checked the limit by hand: `∂_τ F_{θ_τ}(x)` at `0` is
  `∑_ℓ f_ℓ(x E W_read^ℓ) W_write^ℓ D` (`hasDerivAt_eval_smallWrites`, proved), its derivative along
  `(0, η_read, η_write, 0)` is the sum in the definition, and the derivative of `x E D` along
  `(η_E, 0, 0, η_D)` is the first term. The same with `χ`.
- **The step without networks** (row 13).
  ```
  theorem eventually_finrank_range_le_of_small_parameter (G : ℝ → P → Y)
      (hG : ContDiff ℝ 2 (fun p : ℝ × P => G p.1 p.2)) (π : P →L[ℝ] P) (θ : P)
      (h0 : ∀ η, fderiv ℝ (G 0) θ (π η) = 0) :
      ∀ᶠ τ in 𝓝[≠] (0 : ℝ),
        Module.finrank ℝ (LinearMap.range
            ((fderiv ℝ (G 0) θ).comp (ContinuousLinearMap.id ℝ P - π)
              + (fderiv ℝ (fun θ' => deriv (fun τ => G τ θ') 0) θ).comp π).toLinearMap)
          ≤ Module.finrank ℝ (LinearMap.range (fderiv ℝ (G τ) θ).toLinearMap)
  ```
  True: `D_θ G(τ, θ)((η − πη) + τ⁻¹ πη)` tends to the map on the left as `τ → 0`, because
  `D_θ G(0, θ)(πη) = 0` and the second derivative is symmetric, and linear independence of finitely
  many vectors is an open condition. `π` need not be a projection. In the application `G τ θ` is
  the batch of outputs at `θ_τ` and `π η = (0, η_read, η_write, 0)`: the reads **and the writes**.
  Then `D_θ G(τ, θ)((η − πη) + τ⁻¹ πη) = J_τ (η_E, η_read/τ, η_write, η_D)`, since `θ ↦ θ_τ`
  already multiplies the direction of the writes by `τ`; this is the paper's `J_τ S_τ η`. So the
  Lean limit is the paper's `J_0`, and `rank D_θ G(τ, θ) ≤ rank J_τ` gives the paper's inequality.
- **Lemma A.4** (rows 1 to 3).
  ```
  theorem orthogonal_of_eval_cob_skipless_rmsNorm_mlp [Nonempty T] [Nonempty dIn] [Nonempty dOut]
      (hε : 0 < ε) (hσc : Continuous σ) (hne : ¬ ∀ z, σ (-z) = σ z) (hnc : ¬ ∀ z, σ z = σ 0)
      (hhid : ∀ ℓ, Nonempty (hid ℓ)) (G : Fin (L + 1) → GL d ℝ)
      (h : ∀ (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)
        (x : Matrix T dIn ℝ),
        eval (Arch.mlp σ (rmsNorm ε) hid) 0 (θ.cob G G) x
          = eval (Arch.mlp σ (rmsNorm ε) hid) 0 θ x) :
      ∀ ℓ, (G ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ
  ```
  `θ.cob G G` is the paper's map (`E G_0`, `G_{ℓ−1}⁻¹ W_read^ℓ`, `W_write^ℓ G_ℓ`, `G_L⁻¹ D`), and
  `eval … 0` is the skipless network. The hypothesis `h` can hold (it does for orthogonal `G`, the
  other half of the `↔` statements), so the statement is not empty. I tried the cases outside the
  paper's scope by hand: `d_in = 1 < d` (the embedding still reaches every row, since `E` varies
  too); one hidden unit (fact (c) needs one nonzero hidden unit and a free write row); `d` empty
  or of one element (trivial, resp. `G_ℓ = ±1`). I found no counterexample. In the gated statement
  `hσ0 : ∃ z, σ z ≠ 0` follows from `hκ` at `κ = 0`; it is redundant, not wrong.
- **Steps 1 to 3** (rows 6 and 18).
  ```
  theorem exists_antisymm_of_flat_residual_rmsNorm {A : Arch T d 1} {ε : ℝ} (hε : 0 < ε)
      (hA : A.χ = rmsNorm ε) (hf : ContDiff ℝ 1 (A.f 0)) (θ : Params A dIn dOut)
      (hE : θ.E.rank = Fintype.card d) (hD : θ.D.rank = Fintype.card d)
      (η : Params A dIn dOut) (hη : η ∈ flat A 1 θ) :
      ∃ Y : Matrix d d ℝ, Yᵀ = -Y ∧ η.E = θ.E * Y ∧ η.D = -(Y * θ.D) ∧
        ∀ x : Matrix T dIn ℝ,
          fderiv ℝ (A.f 0) (rmsNorm ε (x * θ.E) * θ.read 0)
              (rmsNorm ε (x * θ.E) * (η.read 0 + Y * θ.read 0)) * θ.write 0
            + A.f 0 (rmsNorm ε (x * θ.E) * θ.read 0) * (η.write 0 - θ.write 0 * Y) = 0
  ```
  This is the end of the paper's Step 3: `η' = η − η^Y` has `η'_E = 0`, `η'_D = 0`, the entries
  `η_read + Y W_read` and `η_write − W_write Y` at the block, and `D_θ h_1 η' = 0`. I followed the
  paper's three steps for a general `C¹` map `f` on `T` tokens (boundedness of `g(tw)` and of its
  derivative needs `f` and `Df` bounded on the closed ball, which `C¹` gives). True. The statement
  for `J_0` has the block term along `η_read`, `η_write` themselves, which is right: there `η^Y`
  has no entries at the block, because `𝐃N_ε(h)(hY) = N_ε(h) Y` for antisymmetric `Y`.
- **Hypotheses that could be empty.** The conditions `OneBlockGenericRMS θ` and the five like it
  hold for almost every `θ` when `d ≥ 2` (note (d)). `UnitsRigid σ σ' …` holds for tanh and GELU
  and `GatedUnitsRescale σ σ' …` for the SiLU and GELU gates (proved statements, used by the
  statements for the four kinds). An additive Haar measure on the parameters exists (`Fit.lean`).
- **A computation** (Check 2, last item): the values agree with numerical ranks, also for blocks
  narrower than `d`, where the Lean statements go beyond the main text.

### (b) Do the docstrings say honestly what part of the paper each piece is?

Yes, with three small remarks (2 to 4 below).

1. Every file header names the paper statement, quotes the sentences it formalizes, and says where
   the route differs: `Residual/SmallParameter.lean` ("since the second derivative of `G` is
   symmetric"; "Here only 'the rank of a composition is at most the rank of the outer map' is used,
   which needs no inverse"); `Residual/SmallWrites.lean` ("That the same `τ` multiplies the
   directions of the writes as well does not change the rank for `τ ≠ 0`");
   `OneBlock/ResidualRMSMlp.lean` (Step 4: "the image of `x ↦ N_ε(x E)`, an open set of hidden
   states (the open ball of radius `√d` in the paper) … For a real-analytic activation it then
   vanishes for all `n`"). The statements under conditions say "under the conditions of the
   proof", and the general ones say for which activations they are stated.
2. `Symmetry/OnlyOrthogonal.lean`, header: "Stated here for MLP blocks and for gated blocks, with
   what the proof uses of the activation or gate as hypotheses, and then for the seven kinds of
   block." For the seven kinds the file states only the facts on the activations and gates
   (row 2); the lemma for one kind is not a statement of the file. The index row (line 353) says
   it correctly ("The facts on tanh, …").
3. `Residual/SmallParameter.lean`, header and docstring: "The coordinates that `S_τ` divides by `τ`
   are given by a continuous linear map `π`". In the two applications `π` is the projection on the
   reads and the writes, while the paper's `S_τ` divides the reads only; on the writes the factor
   `1/τ` undoes the factor `τ` of `θ ↦ θ_τ` (note (a)). The header of `Residual/SmallWrites.lean`
   says this in one sentence; the index row (line 368) repeats the short form.
4. `OneBlock/ResidualRMSSteps.lean`, header: "The steps do not depend on the kind of block: they
   are stated for an arbitrary continuously differentiable map `f`". True for the blocks of this
   part. A reader should know that ReLU and ReGLU blocks are not continuously differentiable, so
   this statement is not the paper's Steps 1 to 3 for them.

### (c) Do the pieces fit?

Yes. By compiling: the library compiles from these sources with no `sorry`, and every final
statement depends on the three standard axioms, so every hypothesis of a later statement is
discharged by an earlier one in the form in which it is stated. By reading (a search for each
name in the proofs): each piece is used.

| Piece | Used by |
|---|---|
| `eventually_finrank_range_le_of_small_parameter` | `eventually_finrank_le_of_small_parameter` |
| `eventually_finrank_le_of_small_parameter`, `eval_smallWrites_zero`, `hasDerivAt_eval_smallWrites` (and the two with `_norm`) | `eventually_funDim_smallWrites_ge` (resp. `…_ge_norm`) |
| `eventually_funDim_smallWrites_ge` + `smallWritesLimit_eq_zero_mlp` (resp. `_gated`) + the upper bound at `θ_τ` | `eventually_funDim_smallWrites_mlp` (resp. `_gated`) |
| `exists_antisymm_of_smallWritesLimitNorm_rmsNorm` | `smallWritesLimitNorm_eq_zero_mlp_rmsNorm`, `…_gated_rmsNorm` |
| `eventually_funDim_smallWrites_ge_norm` + these two | `eventually_funDim_smallWrites_mlp_rmsNorm`, `…_gated_rmsNorm` |
| `eventually_funDim_smallWrites_K` + `ae_smallWritesGeneric…` | `ae_eventually_funDim_smallWrites_K` (Lemma A.27) and, with `ae_funDim_ge` and `ae_funDim_add_le_residual…`, `ae_funDim_K_residual…` (Theorem 4.7) |
| `exists_antisymm_of_flat_residual_rmsNorm` | `flat_le_cobDir_const_mlp_residual_rmsNorm`, `flat_le_cobDir_const_add_rescaleDir_gated_residual_rmsNorm` |
| these two | `funDim_mlp_oneBlock_residual_rmsNorm`, `funDim_gated_oneBlock_residual_rmsNorm`, then with `ae_oneBlockGeneric…RMS` the statements of Theorem 4.6 (ii) |
| Theorem 4.7 / 4.6 (ii) + `ae_funDim_add_le_skipless…` (Theorem 4.2 without skips) | the gains "at least" |
| Theorem 4.7 + `ae_funDim_K_skipless…` (Theorem 5.2 of the dimension paper) | Corollary 4.8 |

### (d) Are the six named conditions generic conditions?

Yes. Each is a structure of finitely many conditions "a rank is `d`", "a row or column is not
zero", "two columns are not collinear"; each is proved to hold for almost every parameter; and each
is what the paper's proof calls generic, or less.

| Condition | What it asks | Proved for almost every `θ` by | Hypotheses of that theorem (by compiling, `Chk2.lean`) |
|---|---|---|---|
| `OneBlockGenericRMS` | `E`, `D` of rank `d`; rows of `W_write` nonzero; columns of `W_read` nonzero and pairwise non-collinear | `ae_oneBlockGenericRMS` | `μ` additive Haar, `2 ≤ card d`, `card d ≤ card dIn`, `card d ≤ card dOut` |
| `OneBlockGenericGatedRMS` | `E`, `D` of rank `d`; rows of `W_write` nonzero; gate columns of `W_read` nonzero and pairwise non-collinear; value columns nonzero | `ae_oneBlockGenericGatedRMS` | the same |
| `SmallWritesGeneric` | `E`, `D` of rank `d`; rows of `W_write^ℓ D` nonzero; columns of `E W_read^ℓ`, over all blocks together, nonzero and pairwise non-collinear | `ae_smallWritesGeneric` | the same |
| `SmallWritesGenericGated` | the same with gate columns, and value columns of `E W_read^ℓ` nonzero | `ae_smallWritesGenericGated` | the same |
| `SmallWritesGenericRMS` | `E`, `D` of rank `d`; rows of `W_write^ℓ` nonzero; columns of the `W_read^ℓ`, over all blocks together, nonzero and pairwise non-collinear | `ae_smallWritesGenericRMS` | the same |
| `SmallWritesGenericGatedRMS` | the same with gate columns, and value columns nonzero | `ae_smallWritesGenericGatedRMS` | the same |

The paper: "A statement holds for generic parameters if it fails only where some nonzero polynomial
in the parameters, or some nonzero real-analytic function of them, vanishes" (Appendix B); "For
generic parameters `E`, `D`, `W_read` and `W_write` have rank `d_model`, every `a_i` is nonzero, and
the `c_i` are nonzero and pairwise non-collinear … [gated:] `e_i ≠ 0` and are not proportional to
its gate weights" (Part (i), Reduction); "Lemma B.3, with `E` and `D` replaced by the identity"
(Part (ii), Step 4); "At generic parameters the hypotheses of Lemma B.3 hold for the units of all
blocks together" (Lemma A.27). The Lean conditions are these with `a_i`, `c_i`, `e_i` the rows of
`W_write D` and the columns of `E W_read` without normalization, and the rows of `W_write` and the
columns of `W_read` under pre-RMSNorm. Lean leaves out "`W_read`, `W_write` of rank `d`" (not used
when the block may have any width) and "not proportional" (the Lean form of Lemma B.3 for SwiGLU
and GeGLU does not need it). So the Lean conditions hold wherever the paper's do.

---------------------------------------------------------------------------------------------------

## What the authors should know

False, vacuous, drifted: nothing found. Misdescribed, in order of weight:

1. **Three notes of the index are out of date.** They say that the pre-RMSNorm statements do not
   exist, and the rows a few lines below state them: line 370 ("The other three values of the
   lemma (pre-RMSNorm; biases; no `E`, `D`) and attention blocks are not stated"), line 371 ("Not
   stated: pre-RMSNorm, attention blocks"), line 374 ("Not stated: Corollary 4.8 under
   pre-RMSNorm").
2. **The paragraph "Not stated yet from the main text of the skips paper"** (lines 392-401) says
   "Theorem 4.7 and Corollary 4.8 for attention blocks (for tanh, GELU, SwiGLU and GeGLU blocks
   they are proved, without normalization and under pre-RMSNorm with `ε > 0`)". Corollary 4.8 has
   no attention blocks, and it has no GELU blocks without normalization; all seven of its cases are
   proved. What is not stated of Theorem 4.7 is: attention blocks, and the clause "by exactly
   `L dim 𝒢` when the skipless network satisfies the equality condition too" as a conditional
   statement (only its instances, Corollary 4.8).
3. **The header of `Symmetry/OnlyOrthogonal.lean`** says that Lemma A.4 is stated "then for the
   seven kinds of block". The file states the facts on the seven activations and gates, not the
   lemma for each kind. (The seven instances compile from the two general statements.)
4. **`π` in `Residual/SmallParameter.lean`** is described as "the coordinates that `S_τ` divides by
   `τ`". In its use it is the reads and the writes; the paper's `S_τ` divides the reads only. The
   mathematics is the same (note (a)); the description is short by one clause.
5. **Lemma A.4 in Lean is more general than the index says**: one token, `d_in, d_out ≥ 1`, one
   hidden unit per block, any `d`. The paper's proof gives this too.
6. **Steps 1 to 3 of Theorem B.1 (ii)** are stated for continuously differentiable `f`, so not for
   ReLU and ReGLU blocks. Nothing in this part needs them; it matters only if Theorem 4.6 (ii) is
   later stated for those blocks.
7. **Width.** The Lean statements of the equality (Theorem 4.6 (ii) first sentence, Theorem 4.7
   first sentence) hold for blocks of any width, also narrower than `d_model`. This is what
   Theorem B.1 (ii) and Lemma A.27 say; the main text's scope has `d_hidden ≥ d_model`. Only the
   gains need the width.
8. **The branch moved during the audit** (`a969c4e` to `6c30ab8`, four pushes); the 15 files,
   their imports and their index rows did not change. At `6c30ab8` the library has four `sorry`,
   all in the new `Depth/SuffixZero.lean` (marked "in work"); the sentence "the library has no
   sorry" of the commit message of `641435d` was true at that commit, not after.

## Corrections for `STATEMENTS.md` (lines at `ee8874f`; the file is the same at `6c30ab8`)

1. **Lines 43-55** (the list "Not yet compared by such a reader"). Take out the 15 files of this
   part and add, before that sentence: "A seventh reader (24 November 2026, part A) compared
   `Symmetry/OnlyOrthogonal.lean`, `OneBlock/ResidualRMSSteps.lean`, `OneBlock/ResidualRMSMlp.lean`,
   `OneBlock/ResidualRMSGated.lean`, `OneBlock/ResidualRMSGain.lean`,
   `Residual/SmallParameter.lean`, `Residual/SmallWrites.lean`, `Residual/DepthMlp.lean`,
   `Residual/DepthGated.lean`, `Residual/ExactGain.lean`, `Residual/SmallWritesNorm.lean`,
   `Residual/SmallWritesRMSSteps.lean`, `Residual/DepthMlpRMS.lean`, `Residual/DepthGatedRMS.lean`
   and `Residual/ExactGainRMS.lean` (25 paper statements and proof pieces against 98 Lean names):
   none false, vacuous or changed in meaning; all 54 statements at generic parameters are
   `∀ᵐ θ ∂μ` for an additive Haar measure, the 12 for Lemma A.27 in the form "for almost every `θ`,
   for all small `τ ≠ 0`"; the 24 final statements of Theorem 4.6 (ii), Theorem 4.7 and
   Corollary 4.8 have no hypothesis that the paper does not have, except at least one token, and
   the statements of the equality need no condition on the widths."
2. **Line 352** (Lemma A.4). After "every block has at least one hidden unit" add: "; Lean needs
   only one token and `d_in, d_out ≥ 1` (the paper's scope has `d_in, d_out, d_hidden ≥ d ≥ 2`)".
   After "for both kinds." add: "The lemma for one of the seven kinds is the general statement
   with the facts of the next row; it is not a named theorem."
3. **Line 364** (Steps 1 to 3). After "for any continuously differentiable `f`" add: "(so not for
   ReLU and ReGLU blocks)".
4. **Line 368** (the step without networks). Replace "a continuous linear map `π` on the
   parameters (the coordinates that `S_τ` divides by `τ`)" by "a continuous linear map `π` on the
   parameters (in its use the projection on the reads and the writes; on the writes the factor
   `1/τ` undoes the factor `τ` of `θ ↦ θ_τ`, so that `D_θ G(τ, θ)((η − πη) + πη/τ)` is the paper's
   `J_τ S_τ η`)".
5. **Line 370** (Lemma A.27, first value, tanh and GELU). Replace "The other three values of the
   lemma (pre-RMSNorm; biases; no `E`, `D`) and attention blocks are not stated" by "The second
   value (pre-RMSNorm) is in the rows of `Residual/DepthMlpRMS.lean` and
   `Residual/DepthGatedRMS.lean` below. The third and the fourth value (biases; no `E`, `D`) and
   attention blocks are not stated".
6. **Line 371** (Theorem 4.7, tanh and GELU, no normalization). Replace "Not stated: pre-RMSNorm,
   attention blocks" by "Under pre-RMSNorm: the row of `Residual/DepthMlpRMS.lean` below. Not
   stated: attention blocks".
7. **Line 374** (`Residual/ExactGain.lean`). Replace "Not stated: Corollary 4.8 under pre-RMSNorm"
   by "Under pre-RMSNorm: the row of `Residual/ExactGainRMS.lean` below. Not stated as a statement
   of its own: 'by exactly `L dim 𝒢` when the skipless network satisfies the equality condition
   too' (its instances are Corollary 4.8)".
8. **Lines 397-398** (the paragraph "Not stated yet"). Replace "Theorem 4.7 and Corollary 4.8 for
   attention blocks (for tanh, GELU, SwiGLU and GeGLU blocks they are proved, without normalization
   and under pre-RMSNorm with `ε > 0`);" by "Theorem 4.7 for attention blocks, and its clause 'by
   exactly `L dim 𝒢` when the skipless network satisfies the equality condition too' as a
   conditional statement (for tanh, GELU, SwiGLU and GeGLU blocks Theorem 4.7 is proved, without
   normalization and under pre-RMSNorm with `ε > 0`, and Corollary 4.8 is proved in all its seven
   cases);".
9. Optional, lines 365, 370, 371, 372, 377: these rows say "a block of any width" or "blocks of
   any widths". One could add once, in a note for the authors: "The main text has `d_hidden ≥ d`;
   the Lean statements of the equality follow Theorem B.1 (ii) and Lemma A.27, which allow any
   width."

Not for the index, for the source (I did not edit it): the header of
`Symmetry/OnlyOrthogonal.lean`, "and then for the seven kinds of block", should read "and the facts
that the seven kinds of block satisfy these hypotheses".

## What I could not check

- I did not read the long proofs line by line. That the statements are proved rests on the compiled
  library of `/home/claude/lp/lean` and on the hash comparison of its build traces with the sources
  of `lw`; I did not rebuild anything, and I did not check that Lake would rebuild `lp` to the same
  files.
- The definitions and statements of other files that this part uses (`funDim`, `flat`, `cobDir`,
  `rescaleDir`, `UnitsRigid`, `GatedUnitsRescale`, `Params.cob`, `rmsNorm`, `silu`, `gelu`, the
  upper bounds of Theorem 4.2, Theorem 5.2 of the dimension paper, `ae_funDim_ge`) I read, but I
  did not compare them with the papers again; earlier audits did, and their files are unchanged
  since `31752fa` (by `git diff`).
- The paper is the text of the PDF. Displayed formulas are broken across lines there; the ones
  that I compared (Lemma A.4, the formulas for `J_0`, Steps 1 to 5 of Theorem B.1 (ii),
  Lemma A.27) were legible. Lemma A.2 (ii) is garbled in the text and is not in this part.
- The numerical ranks are for `d = 3`, one token and one seed per case; they are a look for a
  counterexample, not evidence of the theorems.
- Not in this part and not looked at: `Literature/*`, `Dimension/RankCriterion.lean`,
  `Dimension/SubmersionNull.lean`, `Residual/PointwiseLimit*.lean`, `Residual/SkiplessEnds.lean`,
  `Residual/SkiplessAll.lean`, `Residual/DifferentClasses*.lean`, `Residual/FewerHiddenUnits.lean`,
  `Dimension/ParameterCount.lean`, `Dimension/UpperBoundRMSNormZero.lean`.
