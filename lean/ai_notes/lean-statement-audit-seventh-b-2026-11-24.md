STATUS: complete

# Seventh audit of Lean statements against the skips paper, part B (24 November 2026)

Reader: an independent reader who did not write these statements. I edited no file of a repository,
ran no `lake build`, made no commit and no push.

## Commit, and how each check was made

**Commit of `/home/claude/lw` (branch `lean-wip`).** The worktree moved several times while I
read: `a969c4e` when I began, then `641435d`, `ab2d797`, and
`6c30ab83b74ad3ee6228bfb9a9b8c2a881607e92` when I finished (clean). The verdicts below are for
`6c30ab8`. Of the 13 files of this audit, 12 have the same text at all these commits.
`Residual/FewerHiddenUnits.lean` had four `sorry` at `a969c4e` and has none from `641435d` on; its
four statements did not change (the diff adds a private helper and replaces each `sorry` by a
proof). I read its statements at `a969c4e` and its proofs in the diff. The commits after `641435d`
add two files outside this audit (`Dimension/UpperBoundRMSNormZero.lean`, `Depth/SuffixZero.lean`)
and rows of the dimension paper to the index. Line numbers of `STATEMENTS.md` are those of
`6c30ab8`; since rows are still being added above them, I also name each row by its first words.
One more commit, `a11f6e7`, arrived as I closed this report: it adds `Depth/PathSeparation.lean`
and one row of the dimension paper, so the rows of the skips paper are one line lower there; the 13
files are byte-identical to my copies at that commit too.

**Files with `sorry`** (by a search). At `a969c4e`: only `Residual/FewerHiddenUnits.lean` (4). At
`6c30ab8`: none in the 13 files nor in the 60 modules that they import; 4 in
`Depth/SuffixZero.lean`, a file added after I began and not part of this audit.

**The three kinds of check.**

- *By reading*: the 13 Lean files in full (`Literature/Sard.lean`, `Literature/OMinimal.lean`,
  `Dimension/SubmersionNull.lean`, `Dimension/RankCriterion.lean`, `Residual/PointwiseLimit.lean`,
  `Residual/PointwiseLimitUnion.lean`, `Residual/SkiplessEnds.lean`, `Residual/SkiplessAll.lean`,
  `Residual/DifferentClassesCriterion.lean`, `Residual/DifferentClasses.lean`,
  `Residual/DifferentClassesRMS.lean`, `Dimension/ParameterCount.lean`,
  `Residual/FewerHiddenUnits.lean`), the definitions (`Network/Defs.lean`, `Network/Blocks.lean`,
  `Dimension/Functional.lean`, `Dimension/Space.lean`, the definitions of `gelu`, `silu`, `rmsRow`,
  `rmsNorm`, `UnitsRigid`, `GatedUnitsRescale`), and of the paper (text of the PDF): Section 2,
  Definition 4.1, Section 4.3, the whole reference list, Appendix A.7 from its start to the proof of
  Theorem 4.11 (Definitions A.20, A.22, A.29, Lemmas A.21, A.23, A.24, A.26, Remark A.25, the
  statement of Lemma A.27, Theorem A.28 and its proofs), and the proof of Proposition 4.5 in A.6.
- *By compiling a copy*: `/home/claude/lw` has no compiled file for any of the 13 files (its
  compiled library is from 03:44). I therefore compiled against the compiled library of
  `/home/claude/lp/lean` (branch `lean-plus`), which the brief did not name. Two checks make this
  sound: `diff -rq` of `SkipsLean/` between the two worktrees showed no difference at `641435d`, and
  for the 60 modules of the import closure of the 13 files the Lake text hash of the source in
  `/home/claude/lw` is the one recorded in the build trace of `/home/claude/lp`
  (`/home/claude/audit7b/closure_hash.py`: 60 modules, 0 problems; run at `ab2d797` and again at
  `6c30ab8`). Compiled with `lake env lean` from `/home/claude/lp/lean`: (a) a copy of each of the 13 files
  (`/home/claude/audit7b/copies/`, byte-identical to the sources at `6c30ab8`): all 13 exit 0, no
  error, no warning, no `sorry` (`run_copies.out`); (b) `/home/claude/audit7b/Ax7b.lean`:
  `#print` of the two literature definitions, five small examples, `#check` of 27 statements,
  `#print axioms` of 58 theorems (`Ax7b.out`).
- *By a computation*: `/home/claude/audit7b/rank_check2.py` (singular values of Jacobians, float64,
  autograd; output `rank_check2.out`) and two arithmetic loops quoted in Part 3 (`arith_check.py`,
  output `arith_check.out`). I also read the outputs of `different_classes_check_2026-11-24.py` and
  `fewer_hidden_units_check_2026-11-24.py` (both end with "ALL AS EXPECTED"); I did not rerun them.

**Result in one paragraph.** Nothing false, nothing vacuous, nothing changed in meaning by a
definition. The two literature hypotheses are definitions of propositions and never axioms; each is
used only where the paper's argument applies; for the concrete theorems (tanh, GELU, SwiGLU, GeGLU,
with or without pre-RMSNorm with `ε > 0`) both hold, the first by Sard's theorem and the second by
the paper's Lemmas A.21 and A.23 (which, by instruction, I did not check), so those theorems are
not vacuous. "Generic" is `∀ᵐ θ ∂μ` for an additive Haar measure everywhere, the ranks are those of
Definition 4.1, and the final statements have no hypothesis that the paper lacks, except at least
one token, which the paper leaves unsaid. The differences are of coverage and of form; they are
listed in Part 3 and under "What the authors should know".

---

## Part 1: the two hypotheses from the literature

### 1.1 Form

**Verdict: both are `def … : Prop`; there is no `axiom`; the final theorems depend on the three
standard axioms only.**

`Literature/Sard.lean:29-32` and `Literature/OMinimal.lean:35-36` (by reading; the same text is
printed by `#print` in `Ax7b.out`, by compiling):

```lean
def SardCriticalValues (E F : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F] : Prop :=
  ∀ (μ : Measure F) [μ.IsAddHaarMeasure] (g : E → F), AnalyticOnNhd ℝ g Set.univ →
    μ (g '' {x | ¬ Function.Surjective (fderiv ℝ g x)}) = 0

def ClosureNullOfNull {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] (S : Set Y) : Prop :=
  ∀ (r : ℕ) (π : Y →L[ℝ] (Fin r → ℝ)), volume (π '' S) = 0 → volume (closure (π '' S)) = 0
```

- `grep -rn "^axiom" SkipsLean`: no line (by a search, at `a969c4e` and at `6c30ab8`). A search for
  `sorry`, `admit`, `native_decide`, a line beginning with `axiom` or `unsafe`, in the 13 files and
  the 60 modules of their import closure at `6c30ab8`: no line.
- `/home/claude/proj_up/axioms_2026-11-24_z.out` (by reading): 682 names, every one with
  `[propext, Classical.choice, Quot.sound]` or fewer, no `sorryAx`. It was made before the last four
  files were proved, so it lacks 12 names. The newer `axioms_2026-11-24_aa.out` has 694 names, 693
  with the three axioms and one with `propext` only, no `sorryAx`; it contains the 12 names
  (`finrank_params…`, `IsPointwiseLimit.mono`, `isPointwiseLimit_union`,
  `exists_isPointwiseLimit_of_biUnion_finite`, `jacobianRank_add_le_skipless_all…`, the four of
  `FewerHiddenUnits.lean`).
- My own run (by compiling, `Ax7b.lean`): `#print axioms` of all 58 public theorems of the 13 files
  gives `[propext, Classical.choice, Quot.sound]` 58 times.
- The two names occur outside `Literature/` in five files only (by a search):
  `Dimension/RankCriterion.lean`, `Residual/DifferentClassesCriterion.lean`,
  `Residual/DifferentClasses.lean`, `Residual/DifferentClassesRMS.lean`,
  `Residual/FewerHiddenUnits.lean`, always as a hypothesis of a theorem. This is the list that
  `STATEMENTS.md` gives (lines 82-86).

### 1.2 Sard's theorem

**Verdict: `SardCriticalValues E F` is a correct statement of Sard's theorem for real-analytic
maps when `E` and `F` are finite-dimensional, it is true in the edge cases, and every use is for a
finite-dimensional `E` and `F = ℝ^r`. The definition itself does not ask that `E` be
finite-dimensional.**

Clause by clause (by reading):

| Clause of the definition | Sard's theorem |
|---|---|
| `g : E → F`, `AnalyticOnNhd ℝ g Set.univ` | a map that is real-analytic at every point; it is of class `C^r` for every `r`, so the condition `r > max{0, dim M − dim N}` of Sard (1942) holds |
| `{x | ¬ Function.Surjective (fderiv ℝ g x)}` | the critical points: the derivative is not onto. `g` is differentiable everywhere, so `fderiv` is its derivative |
| `g '' {…}` | the critical values |
| `∀ (μ : Measure F) [μ.IsAddHaarMeasure]`, `μ (…) = 0` | measure zero for every additive Haar measure of `F`; on a finite-dimensional `F` these are the positive multiples of Lebesgue measure, so "every Haar measure" and "Lebesgue measure" say the same |

The docstring's citation (A. Sard, Bull. Amer. Math. Soc. 48 (1942), 883–890, with the condition
`r > max{0, dim M − dim N}`) is the theorem as I know it; I did not open the source.

Edge cases, for finite-dimensional `E` and `F`:

- *Target of dimension 0.* Every linear map onto a space with one point is onto, so there is no
  critical point, and the image of the empty set has measure zero. True. By compiling: `Ax7b.lean`
  proves `SardCriticalValues E (Fin 0 → ℝ)` for every `E` (no `sorry`).
- *Source of dimension 0, target of dimension at least 1.* The one point is critical; its image is
  one point, of measure zero for a Haar measure of a space of positive dimension. True (by
  reasoning).
- *Source of smaller dimension than the target.* Every point is critical, and the statement says
  that the image of `g` has measure zero. This is the case `r > 0` of Sard's theorem (a `C¹` map
  from a space of smaller dimension has an image of measure zero). True (by reasoning).
- *What the definition does not exclude.* It has no `[FiniteDimensional ℝ E]`. For an
  infinite-dimensional `E` (and `F = ℝ`) the statement of Sard's theorem is known to fail for smooth
  maps (Kupka's example; I did not check whether a real-analytic example is in the literature). For
  an infinite-dimensional `F` there is no Haar measure and the proposition holds for the empty
  reason. Neither case is used.

Uses (by a search over the five files, and by reading): the hypothesis always has the form
`∀ r : ℕ, SardCriticalValues P' (Fin r → ℝ)` (in one private helper of `RankCriterion.lean`, for
one `r`), where `P'` is

- an abstract space with `[FiniteDimensional ℝ P']` (`RankCriterion.lean`, 3 times), or
- `Params A' dIn dOut`, the parameters of the second family (`DifferentClassesCriterion.lean`, 4
  times; `Dimension/Space.lean:107` gives `FiniteDimensional ℝ (Params A dIn dOut)`), or
- `Params (Arch.mlp σ χ hid) dIn dOut` or `Params (Arch.gated σ χ hid) dIn dOut` with `χ = id` or
  `rmsNorm ε` (`DifferentClasses.lean` 14 times, `DifferentClassesRMS.lean` 14 times,
  `FewerHiddenUnits.lean` 4 times; there with the widths `hid'` or `fun ℓ => Fin (m ℓ)` of the
  skipless network).

So it is used only for spaces where it is true. The one place where it is applied
(`RankCriterion.lean:178`, `hSard volume (fun η => π (G η)) hg`) is the paper's step "so all its
values are critical, and by Sard's theorem its image has measure zero".

The paper and Sard (by reading the text and the reference list, lines 629-816 of the text file):
the paper names "Sard's theorem" three times and gives no reference: in the proof of
Proposition 4.5 (Appendix A.6: "By Sard's theorem this image contains no open subset of a manifold
of larger dimension"), in the proof of Lemma A.24 (i), and in the proof of Lemma A.26. The reference
list has no entry for Sard. The brief and `Literature/Sard.lean` name the last two; the first is a
third place.

The docstring's sentence on Mathlib (by a search in the Mathlib sources of the toolchain,
`v4.36.0`): `MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero` exists (equal
dimensions). For a source of smaller dimension Mathlib has
`Differentiable.dense_compl_range_of_finrank_lt_finrank` ("A particular case of Sard's Theorem"),
whose conclusion is that the complement of the range is dense, not that the range has measure zero.

### 1.3 The closure property

**Verdict: `ClosureNullOfNull S`, for `S` the set of outputs of the skipless networks on a batch,
is the one sentence of the paper's proof of Lemma A.26 (ii), stated for every linear `π` instead of
the one that the proof chooses. It is true for every set to which the concrete theorems apply it,
given the paper's Lemmas A.21 and A.23. It is not true of every set, so it is a real hypothesis.**

The paper (proof of Lemma A.26): "For (ii), let `S = G_X(ℝ^{P'})`, with closure `S̄`. The image
`π(S)` of `π ∘ G_X` is definable and has measure zero, so its closure has measure zero
(Lemma A.23)."

Lean, where it is used (`RankCriterion.lean:216-219`, by reading):

```lean
  have hC : volume (closure (π '' Set.range G)) = 0 := by
    refine hcl _ π ?_
    rw [← Set.range_comp]
    exact h0
```

with `hcl : ClosureNullOfNull (Set.range G)`, `G = evalBatch A' S' X` in the applications, and `h0`
the measure zero of `π(S)` that Sard's step gives. So `S` is `Set.range (evalBatch A' S' X)`, the
paper's `G_X(ℝ^{P'})`, and `volume` on `Fin r → ℝ` is Lebesgue measure on `ℝ^r`.

What the hypothesis packages, exactly:

1. Lemma A.21: for the networks named there, the map from the weights to the outputs on a batch is
   definable, and so is the set `S` of these outputs.
2. The image of a definable set under a definable map is definable (the paragraph after
   Definition A.20; van den Dries, Chapter 1, Lemma (2.3)), applied to the linear map `π`: `π(S)` is
   definable. (Also, silently: `Fin n → Matrix T dOut ℝ` is `ℝ^k` after a linear change of
   coordinates.)
3. The last sentence of Lemma A.23: a definable set of Lebesgue measure zero has a closure of
   measure zero. Its proof in the paper uses van den Dries, Chapter 4, Theorem (1.8), the cell
   decomposition (Chapter 3, Theorem (2.11)) and an induction with Fubini's theorem.

What it does not package: that `π(S)` has measure zero (proved in Lean from Sard's hypothesis and
the bound on the rank); that `π(S̄) ⊆` the closure of `π(S)` (proved,
`image_closure_subset_closure_image`); the step back to the parameters `θ` (proved,
`Dimension/SubmersionNull.lean`). The docstring of `Literature/OMinimal.lean` lists the same sources
as the paper (van den Dries Ch. 1 (2.3), Ch. 3 (2.11), Ch. 4 (1.8); Speissegger 1997).

The instances (by a search and by reading):

| Where | The set `S` | Does the paper's argument apply? |
|---|---|---|
| `RankCriterion.lean`, `ae_notMem_closure_range_of_rank_lt` | `Set.range G`, any real-analytic `G` | it is the hypothesis "the outputs `G_η(x)` are definable functions of `η`" of Lemma A.26 (ii), in the form of its one consequence |
| `DifferentClassesCriterion.lean` (2 theorems) | `Set.range (evalBatch A' S' X)`, any architecture and stream, for every `n` and `X` | the same, for two families of networks |
| `DifferentClasses.lean`, `DifferentClassesRMS.lean`, general forms (4 + 4 theorems) | skipless networks (`S' = 0`) of MLP blocks with any real-analytic `σ` under `UnitsRigid`, or gated blocks under `GatedUnitsRescale`; `χ = id` or `rmsNorm ε` | only if `σ` is definable; for another `σ` the hypothesis may be false and the theorem then says nothing (see below) |
| the same two files, concrete forms (4 + 4 theorems with `hOmin`) | skipless networks of `Real.tanh`, `gelu`, gated `silu`, gated `gelu` blocks, `χ = id` or `rmsNorm ε` with `0 < ε` | yes: these are the networks of Lemma A.21 ("tanh, GELU, SwiGLU or GeGLU blocks, with or without pre-RMSNorm with `ε > 0`, skipless or residual, and for every batch `X`") |
| `FewerHiddenUnits.lean` | skipless `σ` blocks of widths `hid'` (general form); skipless GELU blocks of widths `m`, for every `m : Fin L → ℕ` (final form) | the GELU form: yes, Lemma A.21 has no condition on the widths |

In every instance the stream is `0`: the hypothesis is about the outputs of the skipless network
only.

The Lean definitions are the paper's formulas (by reading): `gelu z = z * gaussCdf z` with
`gaussCdf z = 1/2 + ∫₀^z φ`, `silu z = z / (1 + exp (-z))`, `Real.tanh`,
`rmsRow ε v = (√(v·v / d + ε))⁻¹ • v`. So the paper's proof of Lemma A.21 (formulas in `exp` and
`erf`, quotients, a square root of a positive number) is about these maps.

Can the hypothesis be false for an instance of a final theorem? My reasoning, without proving the
o-minimal facts:

- For the concrete theorems: no, if Lemmas A.21 and A.23 hold. `S` is the image of `ℝ^{P'}` under a
  map that Lemma A.21 says is definable; `π(S)` is its image under a linear map; if it has measure
  zero, Lemma A.23 gives a closure of measure zero. This holds for every `r`, every `π`, every `n`
  and every batch, which is what the hypothesis asks. Two corner cases need no theory: for `r = 0`
  the space `ℝ^0` is one point of measure 1, so `volume (π '' S) = 0` forces `S = ∅` (true but
  empty); for the empty batch `S` is one point.
- It is not true of every set, so it cannot be dropped: for `S = ℚ ⊂ ℝ` and `π` the identity, `π(S)`
  is countable, of measure zero, and its closure is `ℝ` (by reasoning). The paper's Remark A.25 is
  such a set of outputs of a family with a non-definable map (the curve `(sin β, sin √2 β)`).
  `ClosureNullOfNull ∅` holds (by compiling, `Ax7b.lean`).
- For the general forms with an arbitrary real-analytic `σ` the hypothesis can fail (I expect it to
  fail for some `σ` built from the sine, as in Remark A.25; I did not construct one that also
  satisfies `UnitsRigid`). A theorem with a false hypothesis is empty, not false. This is the
  paper's own condition "If the outputs … are definable" in Lemma A.26 (ii).

So no theorem instantiates it for a set to which the paper's argument does not apply and then
claims something: the general theorems carry it as their hypothesis, and the concrete ones are
exactly the cases of Lemma A.21.

### 1.4 No hidden strength

**Verdict: neither hypothesis gives more than the paper uses.**

- `hSard` is in every final theorem `∀ r, SardCriticalValues (Params (skipless architecture) dIn
  dOut) (Fin r → ℝ)` (1.2). For the theorems on the same widths the type of the parameters of the
  skipless network is that of the residual one (`Params` depends on the architecture, not on the
  stream); in `FewerHiddenUnits.lean` it is the type with the widths of the skipless network
  (`hid'`, `fun ℓ => Fin (m ℓ)`). In each case it is an instance of a theorem of the literature for
  a finite-dimensional space, so nothing follows from it that is not true. It is asked for every
  `r`, and used for one (`r` = the rank of the Jacobian of the residual network at `θ₀`).
- `hOmin` is in every final theorem `∀ n X, ClosureNullOfNull (Set.range (evalBatch (…) 0 X))`: the
  outputs of the skipless network on a batch, stream `0` (1.3). It is asked for every batch and used
  on one (the batch on which the residual network reaches its rank).
- "equals no skipless network" takes `hSard` only; "not a pointwise limit" and the statement with
  `δ` take both. This is how the paper's proof uses them (Lemma A.26 (i) against (ii)).
- Neither is used for the residual network, and neither is applied to anything else: in
  `RankCriterion.lean` `hSard` is applied once (line 178) and `hcl` once (line 217); the other
  files pass them on.

---

## Part 2: drift checks

### 2.1 "Generic parameters" is "for almost every parameter"

**Verdict: yes, in every statement of the 13 files.**

By a program on the source text (`/home/claude/audit7b/forms.py`, output `forms.out`): the 13
files have 94 declarations, 61 public. 41 contain `∀ᵐ`:

| Form | Count | Which |
|---|---|---|
| conclusion `∀ᵐ θ ∂μ, …`, with `(μ : Measure …) [μ.IsAddHaarMeasure]` among the binders and no a.e. hypothesis | 34 | 2 in `RankCriterion.lean` (+1 private), 2 in `DifferentClassesCriterion.lean`, 12 + 12 in `DifferentClasses(RMS).lean`, 4 in `FewerHiddenUnits.lean`, 1 private in `SkiplessEnds.lean` |
| conclusion `∃ (n) (X), ∀ᵐ θ ∂μ, …`, same binders | 6 | the six `exists_batch_ae_…` (one batch for almost every `θ`: stronger than the paper, see Part 3) |
| an a.e. hypothesis and a conclusion at every parameter | 1 | the private `jacobianRank_add_le_of_ae_se` ("the rank is lower semicontinuous, so the bound holds at every `η`") |

`μ` is an additive Haar measure on the parameters of the residual network (32 statements), on
`Params A dIn dOut` (5: the first family in the four statements of the criterion, and the private
helper `ae_rank_E_D_se`), or on an abstract finite-dimensional space (3). The
parameters carry the Borel σ-algebra of their norm (`Generic/Params.lean:32-34`). That such a `μ`
is a positive multiple of Lebesgue measure was checked by compiling in the sixth audit (its Part 1,
Check 1); I did not repeat it. By compiling (`Ax7b.out`), for example:

```
ae_not_isPointwiseLimit_skipless_gelu : ∀ {T d dIn dOut} {L : ℕ} [Fintype T] [Nonempty T] [Fintype d]
  [DecidableEq d] [Fintype dIn] [Fintype dOut] {hid : Fin L → Type} [(ℓ : Fin L) → Fintype (hid ℓ)],
  (∀ (r : ℕ), SardCriticalValues (Params (Arch.mlp gelu id hid) dIn dOut) (Fin r → ℝ)) →
  (∀ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), ClosureNullOfNull (Set.range (evalBatch (Arch.mlp gelu id hid) 0 X))) →
  ∀ (μ : Measure (Params (Arch.mlp gelu id hid) dIn dOut)) [μ.IsAddHaarMeasure],
  2 ≤ Fintype.card d → Fintype.card d ≤ Fintype.card dIn → Fintype.card d ≤ Fintype.card dOut → 0 < L →
  ∀ᵐ (θ : Params (Arch.mlp gelu id hid) dIn dOut) ∂μ,
    ¬IsPointwiseLimit (Set.range (eval (Arch.mlp gelu id hid) 0)) (eval (Arch.mlp gelu id hid) 1 θ)
```

Where the paper says "at generic parameters" inside a proof (the orbits of the skipless network
"at generic parameters, where `E'` and `D'` have rank `d_model`"), Lean has a statement under the
named conditions (`funDim_add_le_skipless_ends`: `θ.E.rank = card d`, `θ.D.rank = card d`) and then
the bound at every parameter (`jacobianRank_add_le_skipless_ends`), which is what the paper derives
("so the bound holds at every `η`"). The only existence statements about parameters are the
private helpers `exists_rank_gap_…` ("one residual parameter `θ₀` whose functional dimension
exceeds `r₀`"); they are the paper's "at some `θ₀`" of Lemma A.26, not a generic claim.

### 2.2 Functional dimension and rank are those of Definition 4.1

**Verdict: yes.**

By reading: every rank of a network in the 13 files is `jacobianRank A S X θ`
(`Module.finrank ℝ (LinearMap.range (fderiv ℝ (evalBatch A S X) θ).toLinearMap)`) and every
functional dimension is `funDim A S θ` (`sSup` of these ranks over all `n` and all
`X : Fin n → Matrix T dIn ℝ`), from `Dimension/Functional.lean:29-40`. The supremum is a maximum
(`exists_jacobianRank_eq_funDim`, `jacobianRank_le_funDim`). `RankCriterion.lean` writes the rank
of an abstract map as `Module.finrank ℝ (LinearMap.range (fderiv ℝ G η).toLinearMap)`; for
`G = evalBatch A' S' X` this is `jacobianRank` by definition, and
`DifferentClassesCriterion.lean:65` passes one for the other with no conversion
(`fun η => hr₀ n X η`), which compiles. The hypothesis `r₀ < funDim A S θ₀` of the criterion is the
paper's "at some `θ₀` the Jacobian … has rank greater than `P' − k` on some finite batch `X`".
All networks of these files are differentiable in the parameters (real-analytic `σ`; `χ = id` or
`rmsNorm ε` with `0 < ε`), so Mathlib's convention for the derivative of a non-differentiable map
plays no part (sixth audit, Part 1, Check 2).

### 2.3 Theorem 4.11 carries no hypothesis that the paper does not have

**Verdict: none. The final Lean statements have the paper's hypotheses, the two literature
hypotheses, and at least one token.**

The final theorems: for (i), `ae_forall_eval_residual_ne_skipless_K` and
`ae_not_isPointwiseLimit_skipless_K` for `K` = `tanh`, `gelu`, `swiglu`, `geglu`, and the same eight
with `_rmsNorm`; for (ii), `ae_forall_widths_eval_residual_ne_skipless_gelu` and
`ae_not_isPointwiseLimit_skipless_gelu_widths`. Their hypotheses (by compiling, `#check` in
`Ax7b.out`, and by reading):

| Lean hypothesis | In which theorems | Theorem 4.11 with Section 2 | Theorem A.28 | Lemma A.27 |
|---|---|---|---|---|
| `[Fintype T] [Nonempty T]` (at least one token) | all | implicit: a hidden state has `T` tokens | implicit | implicit |
| `[Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut]`, `hid : Fin L → Type` with `Fintype` | all | the dimensions are numbers | the same | the same |
| `(μ) [μ.IsAddHaarMeasure]`, conclusion `∀ᵐ θ ∂μ` | all | "at generic parameters" (Section 2: "outside a set of Lebesgue measure zero") | "almost every choice of weights" | "For generic parameters" |
| `2 ≤ Fintype.card d` | all | Scope: "`d_in, d_out ≥ d_model ≥ 2`" | proof: "as `d_model ≥ 2`" | "Let `d_model ≥ 2`" |
| `card d ≤ card dIn`, `card d ≤ card dOut` | all | Scope: "`d_in, d_out ≥ d_model`" | "With an embedding and a readout"; the proof uses `E'`, `D'` of rank `d_model` at generic parameters | "let `E` and `D` have rank `d_model`" |
| `0 < L` | (i) only | not said (for `L = 0` the two networks are the same map `x E D`, so the claim needs it) | (ii): "of any depth `L ≥ 1`" | no |
| `0 < ε` | the `_rmsNorm` theorems | Section 2: "RMSNorm with the constant `ε > 0`" | "under pre-RMSNorm with `ε > 0`" | "pre-RMSNorm with `ε > 0`" |
| `∀ ℓ, card d ≤ m ℓ` (inside the conclusion, on the skipless widths) | (ii) only | Scope: "Every MLP block has `d_hidden ≥ d_model`"; proof of Theorem 4.11: "In the main text every MLP block has at least `d_model` hidden units (Section 2)" | (iv): "in (iii) for skipless networks whose blocks all have at least `d_model` hidden units"; (iii) itself has no such condition | no |
| `2 * ∑ ℓ, m ℓ < 2 * ∑ ℓ, card (hid ℓ) + L * card d` | (ii) only | "in total, fewer than `L d_model / 2` more hidden units" | the same | no |
| `hSard`, `hOmin` | see 1.4 | from the literature | from the literature | no |

What Lean does not ask and the main text does: `d_hidden ≥ d_model` for the blocks of the residual
network, and in (i) also for the skipless network. Lean's (i) is for blocks of any widths, as
Theorem A.28 (ii) is (Lemma A.27: "of any width"). No biases and inputs in all of `ℝ^{T×d_in}`: the
same in Lean (`Params` has no biases; a batch is any `Fin n → Matrix T dIn ℝ`).

The claim of the brief on Section 2 and on the proof of Theorem 4.11 (by reading): Section 2,
"Scope", says "Every MLP block has `d_hidden ≥ d_model`, and all MLP blocks are of one kind", and
the proof of Theorem 4.11 in Appendix A.7 says "In the main text every MLP block has at least
`d_model` hidden units (Section 2). Part (i) is Theorem A.28(ii) with (iv), and part (ii) is
Theorem A.28(iii) with (iv)." So in (ii) the main text has no skipless block with fewer than
`d_model` hidden units, and the Lean condition `∀ ℓ, card d ≤ m ℓ` is the main text's own.

What of Theorem 4.11 is not stated in Lean:

1. Attention blocks ("analytic blocks" of the paper are tanh, GELU, SwiGLU, GeGLU and attention
   blocks; a transformer mixes attention and MLP blocks). The library has no attention block.
2. "In particular, it cannot be locally uniformly approximated by such networks." No Lean statement
   (a search for locally uniform convergence finds only `Absorb/Limits.lean`). It follows from "not
   a pointwise limit" by the sentence after Definition A.29, whose first half is
   `isPointwiseLimit_of_tendsto`; the step from convergence uniform on compact sets to convergence
   at every input is not written.
3. In Theorem A.28 (iii), skipless blocks with fewer than `d_model` hidden units (the paper's
   argument with the Jacobian in the input). Outside the main text, as shown above.
4. Theorem A.28 (i) (GELU blocks without embedding and readout, `L ≥ 2`). Not part of Theorem 4.11.

`STATEMENTS.md` says 1 and 2 (line 385, the row "S Theorem 4.11 (i) … without normalization"), 3
(line 390, the row "S Theorem 4.11 (ii)") and 1, 3, 4 (lines 399-400, "Not stated yet …").

---

## Part 3: the statements, file by file

### Verdict table

SAME: the Lean statement says what the paper says. LEAN STRONGER / LEAN WEAKER: it implies / is
implied by the paper's statement and differs. PART: it states a piece. DIFFERENT: another route to
the same end. No row is FALSE.

| Paper | Lean (file) | Verdict | The difference |
|---|---|---|---|
| Sard's theorem, named in the proofs of A.24 and A.26 | `SardCriticalValues` (`Literature/Sard.lean`) | SAME for finite-dimensional spaces, restricted to real-analytic maps | a definition, not a theorem; no `FiniteDimensional` in it (Part 1.2) |
| Lemmas A.21, A.23 and the image of a definable set, as used in A.26 (ii) | `ClosureNullOfNull` (`Literature/OMinimal.lean`) | PART | the one consequence that the proof uses, for every linear `π`; definable sets are not defined in Lean (Part 1.3) |
| Definitions A.20, A.22, Lemmas A.21, A.23, A.24, Remark A.25 | none | not stated | assumed from the literature; Lemma A.24 and "the argument in dimensions" are not used by the Lean route |
| Proof of A.26, "and so does its preimage under `F_X` in `U`" | `measure_inter_preimage_eq_zero_of_surjective_fderiv` (`Dimension/SubmersionNull.lean`) | DIFFERENT (a proof piece) | no constant rank theorem: the preimage of a null set under a `C¹` map with an onto derivative on an open set is null |
| Lemma A.26 (i), (ii) | `ae_notMem_range_of_rank_lt`, `ae_notMem_closure_range_of_rank_lt`, `exists_pos_le_norm_sub_of_notMem_closure` (`Dimension/RankCriterion.lean`) | PART | on one batch, for abstract maps; the bound `rank DG ≤ r₀` at every parameter is a hypothesis where the paper has the Lie group; "definable" is `ClosureNullOfNull` |
| Lemma A.26 (i), (ii) for networks | the four theorems of `Residual/DifferentClassesCriterion.lean` | PART, and LEAN STRONGER in the conclusion | the same hypothesis in place of the group; the batch `X` does not depend on `θ`; adds "not a pointwise limit" |
| Definition A.29 | `IsPointwiseLimit` (`Residual/PointwiseLimit.lean`) | SAME | a network is its function; the norm is the largest entry |
| "If a sequence of networks of `ℱ` converges to `F` at every input, then `F` is a pointwise limit of `ℱ`" | `isPointwiseLimit_of_tendsto` | SAME | the next sentence (uniform on compact sets) is not stated |
| A.28 (iv), "So `F` is not a pointwise limit of these skipless networks" | `not_isPointwiseLimit_of_exists_pos` | SAME | |
| Proof of A.28 (iv), "the smallest of their `δ` serves for all" | `IsPointwiseLimit.mono`, `isPointwiseLimit_union`, `exists_isPointwiseLimit_of_biUnion_finite` (`Residual/PointwiseLimitUnion.lean`) | SAME (a proof piece) | in terms of Definition A.29 |
| Proof of A.28 (ii), the orbits of dimension `2d² + s` (under RMSNorm `d(d−1) + s`), with "the bound holds at every `η`" | the eight theorems of `Residual/SkiplessEnds.lean` | SAME as proof pieces, DIFFERENT in form | flat directions in place of group orbits; MLP blocks (`s = 0`) and gated blocks (`s` = number of hidden units); no attention blocks |
| Proof of A.28 (iii), the orbits of dimension `(L+1) d²`, with "the bound holds at every `η`" | `jacobianRank_add_le_skipless_all`, `…_rmsNorm` (`Residual/SkiplessAll.lean`) | SAME as a proof piece | for any architecture with `χ = id`, writes of at least `d` rows, `d_in ≥ d`; the RMSNorm version is not used by the paper here |
| Theorem 4.11 (i), "equals no skipless network of the same widths"; Theorem A.28 (ii) | `ae_forall_eval_residual_ne_skipless_K` (+`_rmsNorm`), `K` = `tanh`, `gelu`, `swiglu`, `geglu` | PART of 4.11 (i) (no attention blocks); for these blocks SAME as A.28 (ii) | blocks of any widths, as in A.28 (ii); under Sard's hypothesis |
| Theorem 4.11 (i), "and is not a pointwise limit of such networks"; A.28 (iv) for (ii) | `ae_not_isPointwiseLimit_skipless_K` (+`_rmsNorm`) | PART of 4.11 (i); for these blocks SAME | under both hypotheses |
| A.28 (iv), first sentence, for (ii) ("a finite set `X` of inputs and a `δ > 0`") | `exists_batch_ae_exists_pos_le_norm_sub_skipless_mlp`, `…_gated` (+`_rmsNorm`) | LEAN STRONGER | one batch for almost every `θ`; stated in the general forms only (for `tanh` etc. give `tanh_unitsRigid` etc.) |
| Theorem 4.11 (i), "In particular, it cannot be locally uniformly approximated" | none | not stated | |
| Proof of A.28 (iii), "`P' = P + 2 d_model ∑ (d'_hidden,ℓ − d_hidden,ℓ)`" | `finrank_params`, `finrank_params_mlp`, `finrank_params_gated` (`Dimension/ParameterCount.lean`) | SAME | `P` written out; the difference of two instances is the paper's formula |
| Theorem 4.11 (ii), first half; Theorem A.28 (iii) for skipless blocks of at least `d` hidden units | `ae_forall_widths_eval_residual_ne_skipless_gelu`; for one choice of widths `ae_forall_eval_residual_ne_skipless_mlp_of_card_lt` | SAME as 4.11 (ii) in the setting of the main text; PART of A.28 (iii) | skipless widths `≥ d` only; the residual widths are free; the one-choice form is for any `σ` under `UnitsRigid` |
| Theorem 4.11 (ii), "and is not a pointwise limit of such networks"; A.28 (iv) for (iii) | `ae_not_isPointwiseLimit_skipless_gelu_widths`; for one choice of widths `ae_not_isPointwiseLimit_skipless_mlp_of_card_lt` | SAME | the set is the union over all admissible widths |

### Notes

**`Dimension/SubmersionNull.lean`.** One public theorem:

```lean
theorem measure_inter_preimage_eq_zero_of_surjective_fderiv … (μ : Measure E) [μ.IsAddHaarMeasure]
    (ν : Measure F) [ν.IsAddHaarMeasure] (f : E → F) (U : Set E) (hU : IsOpen U)
    (hf : ContDiffOn ℝ 1 f U) (hsurj : ∀ x ∈ U, Function.Surjective (fderiv ℝ f x))
    (N : Set F) (hN : ν N = 0) : μ (U ∩ f ⁻¹' N) = 0
```

A true statement of analysis (`E`, `F` finite-dimensional with their Borel σ-algebras; `N` need not
be measurable). The paper obtains the same step from the constant rank theorem; the file header and
the index (line 380) say that the Lean route differs. Edge cases by reasoning: if `F` has dimension
0, a Haar measure gives its point positive mass, so `N = ∅`; if `E` has smaller dimension than `F`,
`hsurj` forces `U = ∅`. By compiling: the copy compiles, standard axioms.

**`Dimension/RankCriterion.lean` (Lemma A.26).** The two statements:

```lean
theorem ae_notMem_range_of_rank_lt (hSard : ∀ r : ℕ, SardCriticalValues P' (Fin r → ℝ))
    (F : P → Y) (G : P' → Y) (hF : AnalyticOnNhd ℝ F Set.univ) (hG : AnalyticOnNhd ℝ G Set.univ)
    (r₀ : ℕ)
    (hGr : ∀ η, Module.finrank ℝ (LinearMap.range (fderiv ℝ G η).toLinearMap) ≤ r₀)
    (θ₀ : P) (hθ₀ : r₀ < Module.finrank ℝ (LinearMap.range (fderiv ℝ F θ₀).toLinearMap))
    (μ : Measure P) [μ.IsAddHaarMeasure] :
    ∀ᵐ θ ∂μ, F θ ∉ Set.range G

theorem ae_notMem_closure_range_of_rank_lt (hSard …) (F) (G) (hF) (hG)
    (hcl : ClosureNullOfNull (Set.range G)) (r₀ : ℕ) (hGr …) (θ₀ : P) (hθ₀ …)
    (μ : Measure P) [μ.IsAddHaarMeasure] :
    ∀ᵐ θ ∂μ, F θ ∉ closure (Set.range G)
```

Clause by clause against the paper:

| Lemma A.26 | Lean |
|---|---|
| two families, `F_θ(x)` real-analytic in `θ`, `G_η(x)` in `η` | `F`, `G` are the outputs on one batch, real-analytic on the whole parameter space |
| a Lie group `H` acts smoothly on `ℝ^{P'}`, `G_{a·η} = G_η`, orbits of dimension at least `k` at generic `η` | not in Lean; in its place the hypothesis `hGr`: the Jacobian of `G` has rank at most `r₀` at every `η` (the paper's first step: "So the Jacobian of `G_X` has rank at most `r₀ = P' − k`; … so the bound holds at every `η`") |
| "at some `θ₀` the Jacobian of `θ ↦ (F_θ(x))_{x∈X}` has rank greater than `P' − k` on some finite batch `X`" | `hθ₀`, on the batch of `F` |
| (i) "For almost every `θ`, no `η` satisfies `F_θ = G_η`" | `∀ᵐ θ ∂μ, F θ ∉ Set.range G`: the outputs on the batch are not outputs of `G`; this implies the paper's (i) |
| (ii) "If the outputs `G_η(x)`, `x ∈ X`, are definable functions of `η`" | `hcl : ClosureNullOfNull (Set.range G)` |
| (ii) "for almost every `θ` there is a `δ > 0` such that every `η` has `‖F_θ(x) − G_η(x)‖ ≥ δ` at some `x ∈ X`" | `F θ ∉ closure (Set.range G)`, and `exists_pos_le_norm_sub_of_notMem_closure`: `∃ δ, 0 < δ ∧ ∀ z ∈ S, δ ≤ ‖y − z‖`; the step to "at some `x ∈ X`" is in `DifferentClassesCriterion.lean` |

*Do the index and the docstrings say that the group is replaced by the bound on the rank?* Yes. The
file header: "In the paper the rank of the Jacobian of `G` is at most `r₀ = P' - k` at every
parameter because a Lie group acts on the parameters of `G` with orbits of dimension at least `k`
… here the bound `rank DG ≤ r₀` at every point is the hypothesis." The docstrings of both theorems
begin "if the Jacobian of `G` has rank at most `r₀` at every parameter". The index, line 381: "the
Jacobian of `G` has rank at most `r₀` at every parameter (the paper gets this from a Lie group with
orbits of dimension at least `k`, `r₀ = P' − k`) … The step from the group action to the bound on
the rank is made for each family of networks (`Residual/SkiplessEnds.lean`)". (That last sentence
should now also name `Residual/SkiplessAll.lean`; see the corrections.)

*Does the paper's Lemma A.26 follow from the Lean statement plus a statement about the group
action?* Yes (by reasoning). The missing statement is: (G) "if a Lie group `H` acts smoothly on
`ℝ^{P'}` with `G_{a·η} = G_η` and orbits of dimension at least `k` at generic `η`, then on every
finite batch the Jacobian of `G_X` has rank at most `P' − k` at EVERY `η`". With (G), take
`F = F_X`, `G = G_X` and `r₀ = P' − k` in the Lean statements: (i) gives that for almost every `θ`
the outputs of `F_θ` on `X` are not outputs of any `G_η`, hence `F_θ ≠ G_η`; (ii), with the
definability of `G_X` turned into `ClosureNullOfNull` (Part 1.3), gives a `δ` in the norm of the
batch, hence at one input of the batch. (G) is the first two sentences of the paper's proof; it is
not a Lean statement. For the skipless networks Lean proves its conclusion directly, by counting
flat directions (`SkiplessEnds.lean`, `SkiplessAll.lean`), with no Lie group.

The Lean route does not use the largest rank `r*` nor the constant rank theorem (it takes
`r` = the rank at `θ₀` and an open set of full measure on which `π ∘ DF` is onto). The header says
so. By compiling: the copy compiles; standard axioms.

**`Residual/PointwiseLimit.lean`, `Residual/PointwiseLimitUnion.lean` (Definition A.29).**

Paper: "A network `F` is a pointwise limit of `ℱ` if
`∀ n ≥ 1, ∀ (x_1, …, x_n) ∈ 𝒳ⁿ, ∀ δ > 0, ∃ F' ∈ ℱ, ∀ i ∈ {1, …, n} : ‖F'(x_i) − F(x_i)‖ < δ`."

```lean
def IsPointwiseLimit (𝓕 : Set (Matrix T dIn ℝ → Matrix T dOut ℝ))
    (F : Matrix T dIn ℝ → Matrix T dOut ℝ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ X : Fin n → Matrix T dIn ℝ, ∀ δ : ℝ, 0 < δ →
    ∃ F' ∈ 𝓕, ∀ i, ‖F' (X i) - F (X i)‖ < δ
```

| Paper | Lean | Same? |
|---|---|---|
| `𝒳 = ℝ^{T×d_in}`, `ℱ` a set of networks with inputs in `𝒳` | `𝓕 : Set (Matrix T dIn ℝ → Matrix T dOut ℝ)`, a set of functions | yes; the definition depends on a network only through its function |
| `∀ n ≥ 1` | `∀ n : ℕ, 1 ≤ n →` | yes. The clause changes nothing: the case `n = 0` asks only that `𝓕` have a member, which the case `n = 1` gives (by compiling, `Ax7b.lean`, example 5: the definition with and without `1 ≤ n` are equivalent) |
| `∀ (x_1, …, x_n) ∈ 𝒳ⁿ` | `∀ X : Fin n → Matrix T dIn ℝ` | yes (repetitions allowed in both) |
| `∀ δ > 0` | `∀ δ : ℝ, 0 < δ →` | yes |
| `∃ F' ∈ ℱ` (after `n`, the tuple and `δ`: "may depend on `n`, on `(x_1, …, x_n)` and on `δ`") | `∃ F' ∈ 𝓕` in the same place | yes |
| `∀ i ∈ {1, …, n}` | `∀ i` (`i : Fin n`) | yes |
| `‖F'(x_i) − F(x_i)‖ < δ` | `‖F' (X i) - F (X i)‖ < δ` | yes: the same order of the subtraction, strict inequality. The norm is the largest absolute value of an entry (`Matrix.Norms.Elementwise`); the paper does not fix a norm, and since `δ` ranges over all positive numbers the definition is the same for every norm on `ℝ^{T×d_out}` |

A consequence that is the same in both: no function is a pointwise limit of the empty set (by
compiling, `Ax7b.lean`, example 4). `isPointwiseLimit_of_tendsto` and
`not_isPointwiseLimit_of_exists_pos` are the two sentences of the paper word for word (the second
also for an empty batch, where its hypothesis says that `𝓕` is empty). The three statements of
`PointwiseLimitUnion.lean` are true for any sets of functions; for a finite index set the batches
are put together and the smallest `δ` taken, as in the paper. By compiling: both copies compile;
standard axioms.

**`Residual/SkiplessEnds.lean`, `Residual/SkiplessAll.lean` (bounds at every parameter).** The
statements, shortened:

```lean
theorem jacobianRank_add_le_skipless_ends (hA : A.χ = id)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (hL : 0 < L)
    (hdIn : Fintype.card d ≤ Fintype.card dIn) (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (θ : Params A dIn dOut) {n : ℕ} (X : Fin n → Matrix T dIn ℝ) :
    jacobianRank A 0 X θ + 2 * Fintype.card d ^ 2 ≤ Module.finrank ℝ (Params A dIn dOut)
-- _rmsNorm: (hε : 0 < ε) (hA : A.χ = rmsNorm ε), with  Fintype.card d * (Fintype.card d - 1)
-- _gated, _gated_rmsNorm: [Nonempty d], Arch.gated σ … hid, with  + ∑ ℓ, Fintype.card (hid ℓ)

theorem jacobianRank_add_le_skipless_all (hA : A.χ = id)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hw : ∀ ℓ, Fintype.card d ≤ Fintype.card (A.w ℓ)) (θ : Params A dIn dOut) {n : ℕ}
    (X : Fin n → Matrix T dIn ℝ) :
    jacobianRank A 0 X θ + (L + 1) * Fintype.card d ^ 2 ≤ Module.finrank ℝ (Params A dIn dOut)
-- _rmsNorm: (hε : 0 < ε), with  (L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2)
```

All ten statements are proved (the copies compile with no `sorry`; standard axioms), so none is
false. I still looked at each case of the brief, to see that the hypotheses are the right ones:

| Case | `SkiplessEnds` | `SkiplessAll` |
|---|---|---|
| a block with fewer than `d` hidden units | allowed, and true: the directions used are `E ↦ E X_0`, `W_read^1 ↦ −X_0 W_read^1` and `W_write^L ↦ W_write^L X_L`, `D ↦ −X_L D`; they are determined by `E X_0` and `X_L D`, so only the ranks of `E` and `D` matter, not the widths. By a computation (`rank_check2.out`): with `d = 2`, `hid = [1]`, tanh: `P = 12`, bound 4, rank at random parameters 4, with `E` or `D` of rank 1: 4, writes zero: 2; `hid = [1, 3]`, `[1, 1]`, `[1, 2]` gated, `[2]` with `d = 3`, a block of width 0: all at or below the bound | excluded by `hw` (the writes need rank `d`); the paper has the same condition ("So let every `d'_hidden,ℓ ≥ d_model`") |
| `L = 0` | excluded by `hL : 0 < L`, and it must be: for `L = 0` the hidden states `h_0` and `h_L` are one state and the two changes of basis are one. By a computation: `d = d_in = d_out = 2`, `L = 0`: rank 4, `P − 2d² = 0` | no hypothesis on `L`; for `L = 0` it says `rank ≤ P − d²`, which is the rank of `x ↦ x E D` (computation: 4 = 8 − 4) |
| an empty `d` | MLP forms: the bound is `rank ≤ P`, trivially true. Gated forms at every parameter: `[Nonempty d]` is a hypothesis, and it is needed: with an empty `d` every weight matrix has an empty side, `P = 0`, and the bound would read `s ≤ 0`, false as soon as a block has a hidden unit. (The forms under conditions, `funDim_add_le_skipless_ends_gated…`, ask that no value column vanish, which an empty `d` cannot satisfy.) | the bound is `rank ≤ P`, trivially true |
| `ε ≤ 0` | the RMSNorm forms have `hε : 0 < ε`; nothing is claimed for `ε ≤ 0` | the same |
| subtraction and division of natural numbers | `card d * (card d − 1)` is 0 for `card d ≤ 1`, the intended value | `d (d−1)` is even, so `/ 2` is exact |
| `d_out < d` | excluded (`hdOut`), needed for the rank of `D` | allowed; true, since the change of basis at `h_L` is pinned by the write of the last block, not by `D` |

The every-parameter forms get the bound from the bound at almost every parameter and from
`ae_jacobianRank_ge` / `ae_jacobianRank_le_funDim` (`Dimension/GenericRank.lean`: at almost every
`θ'` the rank on a batch is at least the rank at any fixed `θ`). This is the paper's "the rank is
lower semicontinuous, so the bound holds at every `η`", proved here with analyticity.

Against the paper's proof of A.28 (ii): "the changes of basis at `h_0` and `h_L`, those inside the
heads and the rescalings have orbits of dimension `2d²_model + s` at generic parameters, where `E'`
and `D'` have rank `d_model`"; "the orthogonal changes of basis at `h_0` and `h_L` … have orbits of
dimension `d_model(d_model − 1) + s`". Lean: `2 d²` and `d (d − 1)`, plus `s = ∑ ℓ, card (hid ℓ)`
for gated blocks (one rescaling of the value column per hidden unit), `s = 0` for tanh and GELU.
The same numbers. Against the proof of (iii): "its changes of basis at `h_0, …, h_L` have orbits of
dimension `(L + 1)d²_model` at generic parameters". Lean: `(L + 1) d²`. The same. By a computation
(`rank_check2.out`): 18 skipless networks with `L ≥ 1` (tanh, GELU, SiLU-gated; with and without
RMSNorm, `ε = 0.3`; widths below, at and above `d`), each at 5 parameters (random, `E` of rank 1,
`D` of rank 1, all writes zero, all weights zero), 90 points. At every point the singular value
just beyond the bound is at most `1.8e-16` times the largest, that is, zero in float64; where every
width is at least `d` the bound taken is the smaller one, `P − (L+1)k − s`. The bound of all states
is attained at random parameters in the six networks with widths `≥ d`; the bound of the ends in
the two networks of one block without normalization. The residual networks of the same 20
architectures have rank `P − k − s` (`k = d²`, or `d(d−1)/2` under RMSNorm). The outputs of the
authors' two scripts agree.

**`Residual/DifferentClassesCriterion.lean`.** Four public theorems; hypotheses, shortened:

```lean
    (A : Arch T d L) (S : Fin L → Matrix d d ℝ) (A' : Arch T d' L') (S' : Fin L' → Matrix d' d' ℝ)
    (hSard : ∀ r : ℕ, SardCriticalValues (Params A' dIn dOut) (Fin r → ℝ))
    (hOmin : ∀ (n : ℕ) (X : Fin n → Matrix T dIn ℝ),
      ClosureNullOfNull (Set.range (evalBatch (dOut := dOut) A' S' X)))        -- (ii) only
    (hf …) (hχ …) (hf' …) (hχ' …)                                             -- real-analytic blocks
    (r₀ : ℕ)
    (hr₀ : ∀ (n : ℕ) (X : Fin n → Matrix T dIn ℝ) (η : Params A' dIn dOut), jacobianRank A' S' X η ≤ r₀)
    (θ₀ : Params A dIn dOut) (hθ₀ : r₀ < funDim A S θ₀)
    (μ : Measure (Params A dIn dOut)) [μ.IsAddHaarMeasure]
```

and conclusions

```lean
    ∀ᵐ θ ∂μ, ∀ η : Params A' dIn dOut, eval A S θ ≠ eval A' S' η
    ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), ∀ᵐ θ ∂μ, ∃ δ : ℝ, 0 < δ ∧
      ∀ η : Params A' dIn dOut, ∃ i, δ ≤ ‖eval A S θ (X i) - eval A' S' η (X i)‖
    ∀ᵐ θ ∂μ, ¬ IsPointwiseLimit (Set.range (eval A' S' : Params A' dIn dOut → _)) (eval A S θ)
```

- The first is the paper's (i) word for word ("no `η` satisfies `F_θ = G_η`").
- The second has the batch before "for almost every `θ`"; the paper's (ii) has it fixed by the
  hypothesis, and A.28 (iv) lets it depend on the weights. Lean's order implies both. The index
  says so (line 384: "In Lean the batch does not depend on `θ`"). `‖F_θ(x) − G_η(x)‖ ≥ δ` is
  `δ ≤ ‖eval A S θ (X i) - eval A' S' η (X i)‖`: the same order as Lemma A.26 (ii); Theorem A.28 (iv)
  writes `‖G(x) − F(x)‖`, the same number.
- `hr₀` and `hOmin` are asked on every batch; the proof uses the one batch on which `F` has its
  rank at `θ₀`. The hypotheses are stronger than needed, not wrong, and the skipless networks
  satisfy them on every batch.
- The two families may have different model dimensions, depths and widths; only `T`, `dIn`, `dOut`
  are shared. This is what Theorem A.28 (iii) needs.

By compiling: the copy compiles; standard axioms.

**`Residual/DifferentClasses.lean`, `Residual/DifferentClassesRMS.lean` (Theorem 4.11 (i),
Theorem A.28 (ii), (iv)).** One of the 16 final statements is quoted in 2.1. The others differ in
the block (`Arch.mlp Real.tanh`, `Arch.mlp gelu`, `Arch.gated silu`, `Arch.gated gelu`), in `χ`
(`id`, or `rmsNorm ε` with `hε : 0 < ε`), and in the conclusion
(`∀ η, eval (Arch…) 1 θ ≠ eval (Arch…) 0 η` without `hOmin`, or `¬ IsPointwiseLimit …` with it).

- *"The same widths" is "the same architecture".* Checked (by reading, and in the compiled types):
  in every statement the residual and the skipless network are `eval B 1 θ` and `eval B 0 η` for
  one and the same `B` (for example `Arch.mlp gelu id hid`), and both parameters have the type
  `Params B dIn dOut`. So the skipless network has the same kind of block, the same normalization
  with the same `ε`, the same depth `L`, the same widths `hid ℓ` block by block, and the same `T`,
  `d`, `d_in`, `d_out`; its weights `η` are any. This is the paper's "skipless network of the same
  widths" (Theorem A.28: "`L` blocks without skips of the same widths"). The stream `1` is
  `fun _ => 1`, the identity skip at every block, and `0` is no skip (`Network/Defs.lean`).
- *The pointwise limit* is of the set `Set.range (eval B 0)`: all functions of skipless networks of
  this architecture.
- *The numbers* (private helpers `exists_rank_gap_…`): residual `P − d² − s` (from
  `ae_funDim_mlp_residual`, `ae_funDim_gated_residual`, Theorem 4.7) against the skipless bound
  `P − 2d² − s`; under RMSNorm `P − d(d−1)/2 − s` against `P − d(d−1) − s`, a gap because `d ≥ 2`.
  These are the paper's ("As `P − d² − s > P − 2d² − s`"; "as `d_model ≥ 2`").
- *The general forms* (`…_mlp`, `…_gated`) hold for any real-analytic `σ` with a derivative `σ'`
  under `UnitsRigid` (resp. `GatedUnitsRescale`), the library's form of Lemma B.3; the concrete
  forms supply `tanh_unitsRigid`, `gelu_unitsRigid`, `silu_gatedUnitsRescale`,
  `gelu_gatedUnitsRescale`. Without normalization the hypothesis is
  `UnitsRigid σ σ' dIn dOut (Σ ℓ, hid ℓ)`, under RMSNorm `UnitsRigid σ σ' d d (Σ ℓ, hid ℓ)`; this
  follows the two proofs of the residual value and is not visible in the concrete forms.
- *Not vacuous:* the hypotheses can be met together (for instance one token, `d = d_in = d_out = 2`,
  `L = 1`), both literature hypotheses hold there (Part 1), and the conclusion has content (a
  skipless network is a pointwise limit of the skipless networks, so the statement separates the
  two families).

By compiling: both copies compile; the 28 public theorems have the standard axioms.

**`Dimension/ParameterCount.lean`.**

```lean
theorem finrank_params (A : Arch T d L) :
    Module.finrank ℝ (Params A dIn dOut) =
      Fintype.card dIn * Fintype.card d + ∑ ℓ, Fintype.card d * Fintype.card (A.r ℓ)
        + ∑ ℓ, Fintype.card (A.w ℓ) * Fintype.card d + Fintype.card d * Fintype.card dOut
-- finrank_params_mlp:   … = card dIn * card d + 2 * card d * ∑ ℓ, card (hid ℓ) + card d * card dOut
-- finrank_params_gated: … = card dIn * card d + 3 * card d * ∑ ℓ, card (hid ℓ) + card d * card dOut
```

The paper's shapes (Section 2: `E ∈ ℝ^{d_in×d}`, a read `d × d_hidden`, a write `d_hidden × d`,
`D ∈ ℝ^{d×d_out}`; a gated read is two such matrices). SAME. For two MLP networks with the same
`d`, `d_in`, `d_out` the difference is `2d ∑ (d'_hidden,ℓ − d_hidden,ℓ)`, the paper's formula.

**`Residual/FewerHiddenUnits.lean` (Theorem 4.11 (ii), Theorem A.28 (iii), (iv)).** The two final
statements (by reading; the compiled types agree):

```lean
theorem ae_forall_widths_eval_residual_ne_skipless_gelu
    (hSard : ∀ (m : Fin L → ℕ) (r : ℕ), SardCriticalValues
      (Params (Arch.mlp (T := T) (d := d) gelu id (fun ℓ => Fin (m ℓ))) dIn dOut) (Fin r → ℝ))
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) gelu id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, ∀ m : Fin L → ℕ, (∀ ℓ, Fintype.card d ≤ m ℓ) →
      2 * ∑ ℓ, m ℓ < 2 * ∑ ℓ, Fintype.card (hid ℓ) + L * Fintype.card d →
      ∀ η : Params (Arch.mlp (T := T) (d := d) gelu id (fun ℓ => Fin (m ℓ))) dIn dOut,
        eval (Arch.mlp gelu id hid) 1 θ ≠ eval (Arch.mlp gelu id (fun ℓ => Fin (m ℓ))) 0 η

theorem ae_not_isPointwiseLimit_skipless_gelu_widths (hSard …) (hOmin : ∀ (m : Fin L → ℕ) (n : ℕ)
      (X : Fin n → Matrix T dIn ℝ), ClosureNullOfNull (Set.range (evalBatch (dOut := dOut)
          (Arch.mlp (T := T) (d := d) gelu id (fun ℓ => Fin (m ℓ))) 0 X)))
    (μ …) [μ.IsAddHaarMeasure] (hd …) (hdIn …) (hdOut …) :
    ∀ᵐ θ ∂μ, ¬ IsPointwiseLimit
      (⋃ m ∈ {m : Fin L → ℕ | (∀ ℓ, Fintype.card d ≤ m ℓ) ∧
          2 * ∑ ℓ, m ℓ < 2 * ∑ ℓ, Fintype.card (hid ℓ) + L * Fintype.card d},
        Set.range (eval (Arch.mlp (T := T) (d := d) gelu id (fun ℓ => Fin (m ℓ))) 0 : …))
      (eval (Arch.mlp gelu id hid) 1 θ)
```

- *"In total, fewer than `L d_model / 2` more hidden units"* is, with `d'_ℓ = m ℓ` and
  `d_ℓ = card (hid ℓ)`: `∑ (d'_ℓ − d_ℓ) < L d / 2`. Multiplied by 2 and with the sum of the `d_ℓ`
  moved to the right this is `2 * ∑ ℓ, m ℓ < 2 * ∑ ℓ, card (hid ℓ) + L * card d`, with no
  subtraction and no division of natural numbers. The same, also when the skipless network has
  fewer hidden units in total (a negative difference) and when `L d` is odd. By a computation
  (`arith_check.py`, loop 2): 32 400 choices of `L`, `d` and the two sums; the rational inequality
  and the Lean inequality agree in all.
- *The inequality is the one of the proof.* The paper: the residual value `P − d²` "exceeds
  `P' − (L + 1)d²` exactly when `∑ (d'_hidden,ℓ − d_hidden,ℓ) < L d_model / 2`". By a computation
  (`arith_check.py`, loop 1) with the Lean formulas for `P` and `P'` (`finrank_params_mlp`) and
  subtraction of natural numbers: 370 125 cases with `d ≥ 1`, `d_in, d_out ≥ d`, skipless widths `≥ d`; the Lean
  inequality holds exactly when `P' − (L+1)d² < P − d²`, in all.
- *The set of skipless networks in the statement on limits* is the union, over all widths
  `m : Fin L → ℕ` with every `m ℓ ≥ d` and the inequality, of the functions of the skipless GELU
  networks with `m ℓ` hidden units in block `ℓ` (hidden units indexed by `Fin (m ℓ)`; any other
  index type of the same size gives the same functions). So "not a pointwise limit of such
  networks" is about all these networks together, which is the strong reading and the one that
  Theorem A.28 (iv) proves ("the smallest of their `δ` serves for all"). If no widths satisfy the
  conditions the union is empty and the statement holds because nothing is a limit of the empty
  set, in the paper's definition too. For each `θ`, `¬ IsPointwiseLimit 𝓕 F` is, by unfolding the
  definition, "there are a batch and a `δ > 0` with `‖F'(x) − F(x)‖ ≥ δ` at some `x` of the batch
  for every `F' ∈ 𝓕`": the first sentence of A.28 (iv) for (iii).
- *The hypothesis `d ≤ m ℓ`* is the main text's (Part 2.3) and the condition of A.28 (iv). The
  widths `hid ℓ` of the residual network are free (the main text has `d_hidden ≥ d_model` there
  too; A.28 (iii) has no condition). The same `d`, `d_in`, `d_out`, `T` and `L` for both networks.
- *No hypothesis `L ≥ 1`*, and none is needed: for `L = 0` the inequality reads `0 < 0`.
- *The almost-every quantifier is outside "for all widths"* in the first statement: one null set of
  `θ` for all widths, as in the paper ("For each of the finitely many such choices of widths … a
  set of weights of measure zero, and so does their union").
- *`hSard` and `hOmin` are asked for every `m`*, also for widths that the conclusion does not use.
  Both are true for every `m` (Part 1), so this costs nothing.
- *The one-choice forms* (`…_mlp_of_card_lt`) have `hhid' : ∀ ℓ, card d ≤ card (hid' ℓ)` and
  `hk : 2 * ∑ ℓ, card (hid' ℓ) < 2 * ∑ ℓ, card (hid ℓ) + L * card d`, for any real-analytic `σ`
  under `UnitsRigid` on the units of the residual network. For tanh this is more than the paper
  states (Theorem A.28 (iii) is for GELU blocks); it is true by the same count.

Proofs (by reading the diff `a969c4e..641435d`, and by compiling the copy): the helper
`exists_rank_gap_mlp_fh` takes `r₀ = P' − (L + 1) d²` from `jacobianRank_add_le_skipless_all` and
one `θ₀` from `ae_funDim_mlp_residual`, and compares them with `finrank_params_mlp`; the statements
for all widths use `ae_all_iff` (countably many `m`) and
`exists_isPointwiseLimit_of_biUnion_finite` (the admissible `m` form a finite set). No `sorry`;
standard axioms. By reading: the output of `fewer_hidden_units_check_2026-11-24.py` (6 networks,
including two where the inequality fails and the two bounds are equal) agrees.

---

## What the authors should know

Nothing false, vacuous or drifted was found. The points below are of coverage, of form and of
wording, the more important first.

1. **The definition `SardCriticalValues E F` does not ask that `E` and `F` be finite-dimensional.**
   The docstring and the index say "between two finite-dimensional real normed spaces", and every
   use is for such spaces (parameters of a network, and `ℝ^r`), where it is Sard's theorem. For an
   infinite-dimensional `E` the named proposition would not be a theorem of the literature. If the
   definition should be the theorem and nothing more, add `[FiniteDimensional ℝ E]` and
   `[FiniteDimensional ℝ F]` to it (this changes a definition, so it is your decision; every use
   has the instances at hand).
2. **`ClosureNullOfNull` is true for the concrete theorems only through Lemmas A.21 and A.23**, and
   for the general forms (any real-analytic `σ` under `UnitsRigid` or `GatedUnitsRescale`) it is a
   condition on `σ` that can fail. For such a `σ` the general theorem is empty. The paper has the
   same condition ("If the outputs … are definable"), so this is not a difference, but a reader of
   the general forms should know it. It packages three things: Lemma A.21, the image of a definable
   set under a linear map, and the last sentence of Lemma A.23.
3. **The paper names Sard's theorem in three places, with no reference**: the proofs of
   Proposition 4.5, of Lemma A.24 (i) and of Lemma A.26. `Literature/Sard.lean` and the index name
   the last two. Of the three, only the step of Lemma A.26 is in Lean.
4. **Lemma A.26 in Lean has the bound on the rank as a hypothesis, not the Lie group.** The file
   and the index say so. The paper's lemma is the Lean statement plus the first two sentences of
   its proof (group orbits give the bound at every `η`); for the skipless networks Lean proves the
   bound by counting flat directions.
5. **In Lean the batch of Theorem A.28 (iv) does not depend on the weights** (`∃ X, ∀ᵐ θ, ∃ δ, …`),
   which is stronger than the paper's sentence. It is stated in the general forms only
   (`exists_batch_ae_exists_pos_le_norm_sub_skipless_mlp`, `…_gated`, with `_rmsNorm`), not for
   tanh, GELU, SwiGLU, GeGLU by name, and not for the statement on fewer hidden units (there the
   pointwise-limit form says the paper's sentence).
6. **Theorem 4.11 (i) in Lean is for blocks of any widths** (Theorem A.28 (ii)), and (ii) for a
   residual network of any widths; the main text has `d_hidden ≥ d_model` everywhere.
7. **Not stated**: attention blocks; "cannot be locally uniformly approximated"; Theorem A.28 (i);
   Theorem A.28 (iii) for skipless blocks with fewer than `d_model` hidden units; Lemma A.24 and
   "the argument in dimensions"; the Lie group statement of Lemma A.26.
8. **The one hypothesis that the paper does not write** is at least one token (`[Nonempty T]`). In
   (i) Lean also writes `L ≥ 1`, which Theorem A.28 (ii) has and Theorem 4.11 leaves unsaid.
9. **The pushed branch moved during this audit** (`a969c4e` → `641435d` → `ab2d797` → `6c30ab8`).
   At `a969c4e` the four statements of `Residual/FewerHiddenUnits.lean` were `sorry`; from `641435d`
   on they are proved and the index says "proved". `axioms_2026-11-24_z.out` predates that
   (682 names); `axioms_2026-11-24_aa.out` has 694 names and no `sorryAx`. At `6c30ab8`
   `checks/Axioms.lean` has 6 names more, for a file outside this audit; I saw no output for it.

## Corrections for `STATEMENTS.md` (lines at `6c30ab8`)

1. **Lines 42-55** ("Not yet compared by such a reader …"). Remove from the list
   `Literature/Sard.lean`, `Literature/OMinimal.lean`, `Dimension/SubmersionNull.lean`,
   `Dimension/RankCriterion.lean`, `Residual/PointwiseLimit.lean`, `Residual/SkiplessEnds.lean`,
   `Residual/DifferentClassesCriterion.lean`, `Residual/DifferentClasses.lean`,
   `Residual/DifferentClassesRMS.lean`, `Dimension/ParameterCount.lean`,
   `Residual/PointwiseLimitUnion.lean`, `Residual/SkiplessAll.lean` and
   `Residual/FewerHiddenUnits.lean`, and add before it, for example: "A seventh reader (24 November
   2026, part B) compared these 13 files (the proofs of Lemma A.26 and of Theorem A.28 (ii), (iii),
   (iv), Definition A.29 and Theorem 4.11 of the skips paper, against 61 public Lean names): none
   false, vacuous or changed in meaning. The two results from the literature are definitions of
   propositions, used as hypotheses only, for the parameters and for the outputs of the skipless
   network; every statement at generic parameters is `∀ᵐ θ ∂μ` for an additive Haar measure; the
   statements for Theorem 4.11 have no hypothesis that the paper does not have, except at least one
   token." (`Dimension/UpperBoundRMSNormZero.lean` and `Depth/SuffixZero.lean` were written later
   and were not read; they stay in the list.)
2. **Line 91** (the row "Sard's theorem: the critical values …"), last column: "S proofs of Lemmas A.24 and A.26" → "S proofs of
   Proposition 4.5, of Lemma A.24 and of Lemma A.26; in Lean only the step of Lemma A.26 uses it".
   And "Mathlib v4.36.0 has only the case of equal dimensions and the case of a source of smaller
   dimension" → "… and, for a source of smaller dimension, that the complement of the image is
   dense". In the first column, after "between finite-dimensional real normed spaces", add: "(the
   Lean definition does not ask for finite dimension; every use is for the parameters of a network
   and `ℝ^r`)", unless the definition is changed as in point 1 of the list above.
3. **Line 92** (the row "The closure of a definable set of measure zero …"), first column, add: "It stands for three statements of the paper:
   Lemma A.21, the image of a definable set under a linear map, and the last sentence of
   Lemma A.23. For tanh, GELU, SwiGLU and GeGLU blocks (with or without pre-RMSNorm, `ε > 0`) it is
   true by these; in the general forms, for another real-analytic activation, it is a condition
   that can fail."
4. **Line 381** (the row "S Lemma A.26 (a rank criterion), without networks"), last sentence: "(`Residual/SkiplessEnds.lean`)" →
   "(`Residual/SkiplessEnds.lean`, `Residual/SkiplessAll.lean`)".
5. **Line 385** (the row "S Theorem 4.11 (i) and Theorem A.28 (ii), (iv), without normalization"): after "`L ≥ 1` blocks of any widths" add
   "and at least one token"; and after "(under Sard's theorem and the property of definable sets)"
   add "(this form with `X` and `δ` in the general forms only)". The words "the same architecture"
   are right. For "(it follows from `isPointwiseLimit_of_tendsto`)" write "(it follows from the
   definition, or for a sequence from `isPointwiseLimit_of_tendsto`; the step is not a Lean
   statement)".
6. **Line 389** (the row "S proof of Theorem A.28 (iii), "its changes of basis at …"",
   `SkiplessAll`): after "whose writes have at least `d` rows" add "and `d_in ≥ d`
   (no condition on `d_out` or on `L`)".
7. **Line 390** (the row "S Theorem 4.11 (ii), and Theorem A.28 (iii), (iv) …"): add "at least one token; the residual blocks may have any
   widths; no hypothesis `L ≥ 1` is needed (for `L = 0` no widths satisfy the inequality); the
   pointwise-limit statement is for the union over all these widths". The rest of the row is
   right, and "proved" is right from `641435d` on.
8. **Line 383** (the row "S proof of Theorem A.28 (ii), "the changes of basis at `h_0` and
   `h_L` …"", `SkiplessEnds`): after "for gated blocks with the term `s`" add "(the bound at
   every parameter for `d ≥ 1`)". Optional.

The rows at lines 380, 382, 384, 386, 387, 388 and the paragraph of lines 80-88 need no change. Every public
name of the 13 files is in the index, by name or by the patterns "the same three with `_gated`",
"the names of the row above with the suffix `_rmsNorm`" (by a search).

## What I could not check

- The two results of the literature themselves (Sard's theorem; the o-minimal facts, Speissegger's
  structure, the cited places of van den Dries), by instruction. I did not open the sources, and my
  statement that the hypotheses are true for the concrete theorems rests on the paper's
  Lemmas A.21 and A.23.
- Whether a real-analytic counterexample to Sard's theorem on an infinite-dimensional space is in
  the literature (Part 1.2); it would only bear on a use that the library does not make.
- An activation that is real-analytic, satisfies `UnitsRigid` and makes `ClosureNullOfNull` false
  for a skipless network: I argued that the hypothesis can fail in general and did not build such
  an example.
- That the text file of the paper is the current PDF. I read the text file only.
- The compiled library of `/home/claude/lw` itself: it has no compiled file for these 13 files. My
  compilations used the compiled library of `/home/claude/lp/lean`, after checking that its build
  traces record the hashes of the sources of `/home/claude/lw` for the 60 modules involved. I did
  not run `lake build` or the full `checks/Axioms.lean`.
- The proofs of the files outside the 13 that these statements rest on (`Residual/DepthMlp.lean`,
  `DepthGated.lean`, `DepthMlpRMS.lean`, `DepthGatedRMS.lean`, `Dimension/GenericRank.lean`,
  `Generic/Params.lean`, the upper bounds): I read the statements that are used, not the files;
  part A of this audit covers the first four.
- The numeric check is in float64. An upper bound was judged by the singular value just beyond it
  (at most `1.8e-16` times the largest in all 90 points); a residual rank by a threshold of `1e-8`
  times the largest singular value (smallest ratio kept `5.4e-6`, largest ratio dropped `1.1e-16`).
  A computation of this kind supports the bounds and cannot prove them; the Lean proofs do. The
  authors' scripts use 40 digits; I read their outputs and did not rerun them.
- `Dimension/UpperBoundRMSNormZero.lean`, `Depth/SuffixZero.lean` and their rows (added after I
  began): not in the brief, not read.
