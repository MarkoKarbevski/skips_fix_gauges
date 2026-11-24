STATUS: complete

# Seventeenth audit of Lean statements against the papers, part A: the learned skip (24 November 2026)

Reader: an independent reader who did not write the statements. Brief:
`/home/claude/proj_up/audit17a_brief_2026-11-24.md`. I audited statements and definitions, not
proofs. I changed no repository file, ran no `lake build`, made no commit and no push. My files are
in `/home/claude/audit17a/`.

Library: `/home/claude/lw/lean` (branch `lean-wip`). The branch moved eight times while I read.

- **Commit at the start: `8a637fe8b9921280e1945ad477d0c9e33c4aa464` (17:57:16 UTC).** I read every
  statement of the seven files at this commit.
- Then `470c454` (17:59:36), `588a9d0535c87f1cd75374c5e8ab043fea94954f` (18:02:14; the proofs of
  `OneBlock/LearnedSkipGain.lean` were merged here), `da0be3b` (18:08:05), `137746a` (18:17:57),
  `17f6d9a` (18:19:11), `7ef6b40` (18:21:24), `175a7d6` (18:22:45; only `STATEMENTS.md` changed
  there) and **`e17b4d3` (18:23:15), the head at the end (18:25 UTC).**
- **No statement, no docstring and no `omit` line of the 44 public names changed** between
  `8a637fe` and `e17b4d3` (by a script of mine, `cmp_stmts.py`: statement text, docstring and
  `omit` lines of every public name, old file against new). Only proofs were added, in
  `OneBlock/LearnedSkipGain.lean`.
- **Files with `sorry`.** At `8a637fe`: of the seven, `OneBlock/LearnedSkipGain.lean` (2; so the
  21 statements of the three files that rest on it were not yet proved). At `588a9d0` and at
  `e17b4d3`: none of the seven. At `e17b4d3` three files of the library have `sorry`, all new and
  not in my brief: `Absorb/AttentionHeadsIdentifiable.lean`, `Absorb/BiasesConstructions.lean`,
  `Absorb/BiasesAttention.lean`.
- The seven files have 44 public names: 5 definitions and 39 theorems (3 + 11, 1 + 4, 1, 1 + 2,
  10, 7, 4, as the brief says).
- At `588a9d0` all 39 theorems depend on `propext`, `Classical.choice`, `Quot.sound` only (by
  compiling, `Ax.lean`, `Ax.out`, against the build of `/home/claude/lp/lean`; `/home/claude/lw`
  has no compiled copy of these files; the seven sources of `lp` and `lw` were the same, by
  `cmp`, and the compiled file of `LearnedSkipGain` was newer than its source).

Papers, as text: the skips paper ("S", `skips.txt`). Line numbers of `STATEMENTS.md` are those of
`175a7d6` and `e17b4d3` (the same). The index moved while I read: the rows of the seven files are lines 812 to 818 there,
809 to 815 at `7ef6b40`, 808 to 814 at `da0be3b`, 805 to 811 at `588a9d0`. I quote the text of
every place that I name, so that it can be found.

How I checked.

- "By reading": every public statement and docstring of the seven files, the definitions they use
  (`Arch`, `Params`, `hidden`, `eval`, `Arch.mlp`, `Arch.gated`, `Arch.attention`, `attnWeights`,
  `rmsRow`, `rmsNorm`, `tangentRMS`, `fderiv_rmsNorm_mul`, `Params.cob`, `cobSkip`,
  `InsideBlocks`, `funDim`, `jacobianRank`, `flatOn`, `evalSkips`, `jacobianRankSkips`,
  `funDimSkips`, `flatSkips`, `funDimLearned`, `noKinkRMS`, `noKinkGateRMS`,
  `OneBlockGenericRMS`, `OneBlockGenericGatedRMS`, `OneBlockGenericReGLURMS`, `UnitsRescale`,
  `headValueModel`, `relu`, `reluSq`), and the paper passages that the brief names.
- "By hand": a short argument of my own, written where it is used.
- "By compiling": scratch files in `/home/claude/audit17a/`, compiled with
  `lake env lean <file>` from `/home/claude/lp/lean` (nothing written there): `Ax.lean` (axioms),
  `Sig.lean` (the full signatures of the 39 theorems, with every instance argument), `Chk.lean`
  and `Chk2.lean` (checks of Part 1). All compile without error (`*.out`).
- "By a computation": my own scripts `ls17core.py`, `ls17run.py`, `ls17more.py`, `ls17replay.py`
  (mpmath, 60 or 80 digits; derivatives by dual numbers, checked against central differences in
  `ls17fd.py`: they agree to `10⁻³⁸`; rank from the eigenvalues of `JᵀJ`; over all runs the
  smallest singular value that is kept is `2·10⁻¹³` and no dropped one is above `3·10⁻²⁷`, with
  80 digits `3·10⁻³⁹`). Outputs `ls17_*.out`. I did not run the coordinator's scripts; I read their
  outputs, and the ranks that both compute agree.

**Short answer. Nothing false, nothing vacuous and nothing drifted was found.** The 39 statements
are the paper's or stronger, with gaps that the index names. The two general statements of
`OneBlock/LearnedSkipGain.lean` survived every attempt to refute them (about 180 comparisons of
ranks at weights that the hypotheses allow, most of them not generic, and at special skips), and
I believe both by hand. What the authors should correct is in the index: four rows still say
that the learned skip is not stated for ReLU, ReLU², ReGLU and attention blocks (below,
"Corrections"; a fifth place, the paragraph "Not stated yet from the main text", was corrected
at `175a7d6` while I wrote).

---------------------------------------------------------------------------------------------------

## Part 1: the drift checks

### Check 1. Generic means almost every parameter, for every Haar measure

**Verdict: yes, in all 19 `ae_` statements of the seven files, on the product of the weights and
the skips.** (By reading; the shape of all 19 from their compiled signatures, `Sig.out`,
`ae_shapes.out`; the product space by compiling.)

- 8 in `LearnedSkipTriangular.lean`, 6 in `LearnedSkipRescale.lean`, 3 in `LearnedSkipReGLU.lean`,
  2 in `LearnedSkipAttention.lean`. Each has `μ` as a variable of the statement with
  `[μ.IsAddHaarMeasure]`, and `∀ᵐ p ∂μ`. None is "there is a parameter" or "on an open set". No
  other public statement of the seven files has `∀ᵐ`.
- Full skip: `(μ : Measure (Params (Arch.mlp … relu (rmsNorm ε) hid) dIn dOut × (Fin 1 → Matrix d
  d ℝ)))`. Upper triangular skip: `(μ : Measure (Params (Arch.mlp … Real.tanh (rmsNorm ε) hid) dIn
  dOut × (Fin 1 → upperTriangular d)))`, the product with the triangular matrices.
- The eight forms `ae_…_eq_residual_add` are "for almost every `(θ, A)` and almost every `θ'`":

  ```
  theorem ae_funDimLearned_relu_rmsNorm_eq_residual_add (hε : 0 < ε) [Nonempty (hid 0)]
      (μ : Measure (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm ε) hid) dIn dOut
        × (Fin 1 → Matrix d d ℝ))) [μ.IsAddHaarMeasure]
      (ν : Measure (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm ε) hid) dIn dOut))
      [ν.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
      (hdOut : Fintype.card d ≤ Fintype.card dOut) :
      ∀ᵐ p ∂μ, ∀ᵐ θ' ∂ν, funDimLearned (Arch.mlp relu (rmsNorm ε) hid) p
        = funDim (Arch.mlp relu (rmsNorm ε) hid) 1 θ' + Fintype.card d * (Fintype.card d + 1) / 2
  ```
  with `ν` any Haar measure on the weights of the residual network.
- By compiling (`Chk.lean`): the space `Params … × (Fin 1 → upperTriangular (Fin 2))` carries the
  Borel σ-algebra of its topology; a Haar measure on it exists, so the statements are not empty;
  any two Haar measures on it have the same sets of measure zero.

### Check 2. The functional dimension

**Verdict: `funDimLearned` and `funDimLearnedTri` are `funDimSkips`. For ReLU, ReLU² and ReGLU
blocks every value statement has its batch statement, and the pair is the paper's notion.** (By
reading; the definitions by compiling.)

- The Lean text:

  ```
  noncomputable abbrev funDimLearnedTri (A : Arch T d L)
      (p : Params A dIn dOut × (Fin L → upperTriangular d)) : ℕ := funDimSkips A (triSkips d L) p
  noncomputable def triSkips (d : Type*) [Fintype d] [LinearOrder d] (L : ℕ) :
      (Fin L → upperTriangular d) →L[ℝ] (Fin L → Matrix d d ℝ) :=
    ContinuousLinearMap.pi fun ℓ => (upperTriangular d).subtypeL.comp (ContinuousLinearMap.proj ℓ)
  ```
  By compiling (`Chk.lean`, all by `rfl`): `funDimLearnedTri A p` is the supremum over all `n`
  and all batches of the rank of the derivative of `(θ, R) ↦ (eval A (R as matrices) θ (X i))_i`;
  the same for `funDimLearned` with all matrices; `triSkips d L R ℓ = (R ℓ : Matrix d d ℝ)`; and
  for one block `evalSkips A (triSkips d 1) (θ, R) x = A.χ (x * θ.E * (R 0) + A.f 0 (A.χ (x *
  θ.E) * θ.read 0) * θ.write 0) * θ.D`, the paper's `N_ε(x E A + f(N_ε(x E) W_read) W_write) D`.
- **The pairs** (value of `funDimLearned`; a batch of inputs off the kinks with this rank):

  | Block | Value | Batch |
  |---|---|---|
  | ReLU-type, one parameter | `funDimLearned_mlp_rescale_rmsNorm` | `exists_jacobianRankSkips_mlp_rescale_rmsNorm` |
  | ReLU, generic | `ae_funDimLearned_relu_rmsNorm` | `ae_exists_jacobianRankSkips_relu_rmsNorm` |
  | ReLU², generic | `ae_funDimLearned_reluSq_rmsNorm` | `ae_exists_jacobianRankSkips_reluSq_rmsNorm` |
  | ReGLU, one parameter | `funDimLearned_reglu_rmsNorm` | `exists_jacobianRankSkips_reglu_rmsNorm` |
  | ReGLU, generic | `ae_funDimLearned_reglu_rmsNorm` | `ae_exists_jacobianRankSkips_reglu_rmsNorm` |
  | any block on a cone | `funDimLearned_eq_funDim_residual_add_of_noSymmetricPart_on` has both in one conclusion | |

  The batch statement reads `∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i, X i ∈ noKinkRMS p.1) ∧
  jacobianRankSkips … X p + (card d * (card d - 1) + card (hid 0)) = finrank ℝ (Params …) + card d
  ^ 2`.
- **Is it the paper's notion? Yes.** The paper's functional dimension for these blocks is the
  largest rank over the batches of inputs with no hidden unit at its kink (S Appendix B: "'every
  input' means every such input", "some finite batch has kernel exactly `K(θ)`"). The batch
  statement gives a batch of such inputs with the rank `v`; the value statement says that no batch
  at all has a larger rank (Lean's supremum is over all batches). Together: the paper's
  functional dimension is `v`. `noKinkRMS θ` is `{x | ∀ t i, (x * θ.E * θ.read 0) t i ≠ 0}`: for
  `ε > 0` the pre-activation `N_ε(x E) W_read` is a positive multiple of `x E W_read`, row by
  row, so this is "no hidden unit at its kink", at every token. `noKinkGateRMS` asks it of the
  gate columns, where the kink of a ReGLU unit is. The set does not depend on the skip, rightly.
- The three forms `…_eq_residual_add` for these blocks have no batch statement of their own.
  None is needed: both sides have their pairs (for the residual network
  `ae_exists_jacobianRank_relu_oneBlock_residual_rmsNorm` and its siblings, rows 386, 387 of the
  index), so the equality holds in the paper's sense too.

### Check 3. No extra hypotheses in the main-text statement

**Verdict: none. Every hypothesis of the 19 named `ae_` statements is in the Scope or follows
from it, and some of the Scope is not asked. A block with no hidden unit or no head is a real
exception.** (By reading; the instance arguments from the compiled signatures, `Sig.out`; the
exception by a computation and by hand.)

| Lean hypothesis | In which `ae_` statements | Scope has it or implies it? |
|---|---|---|
| `[μ.IsAddHaarMeasure]`, `[ν.IsAddHaarMeasure]` | all 19 | "for generic parameters" |
| `hε : 0 < ε` | all 19 | Setup: "RMSNorm with the constant `ε > 0`" |
| `hd : 2 ≤ Fintype.card d`, `hdIn`, `hdOut` | all 19 | "`d_in, d_out ≥ d_model ≥ 2`" |
| `[Nonempty T]` (at least one token) | all 19 | implicit: an input has a token |
| `hhid : ∀ ℓ, card d ≤ card (hid ℓ)` | the 8 of `LearnedSkipTriangular.lean` | "Every MLP block has `d_hidden ≥ d_model`". Theorem B.1 (iii) itself has no hypothesis on the width (Check 7) |
| `[Nonempty (hid 0)]` (at least one hidden unit) | the 9 for ReLU, ReLU², ReGLU | implied: `d_hidden ≥ d ≥ 2`. Lean asks much less than the Scope here: any width from 1 on |
| `[Nonempty (H 0)]` (at least one head) | the 2 for attention | implied: `H d_h = d ≥ 2` |
| `hdh : ∀ ℓ, card (dh ℓ) ≤ card d`, `hdh0 : ∀ ℓ, 0 < card (dh ℓ)` (`1 ≤ d_h ≤ d`) | the 2 for attention | implied by `H d_h = d ≥ 2`. Lean does not ask `H d_h = d` |
| `(t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁)` | the 2 for attention | implied: "sequences of at least two tokens", and under both masks of the paper the second token sees itself and the first |
| `[LinearOrder d]` | the 8 triangular | needed to say "upper triangular"; any order |
| `k ≠ 0` | none of the `ae_` statements (ReLU has `k = 1`, ReLU² `k = 2`); it is in the four statements for a general homogeneous activation | see the note below |

- **A block with no hidden unit (or no head, or heads of width 0) is an exception: there a
  learned skip adds nothing.** By hand: the network is `x ↦ N_ε(x E A) D`. It depends on `E` and
  `A` through `E A` only, so the `d²` directions with `η_E A + E η_A = 0` are flat, and so is the
  rotation; `fd ≤ P − d(d−1)/2`, the value of the residual network `x ↦ N_ε(x E) D`. By a
  computation (`ls17_zero.out`; `d_in, d, d_out` = 2, 2, 2; 3, 3, 3; 3, 2, 4): residual 7, 15, 13;
  full learned skip, at `A = I` and at a random `A`: 7, 15, 13; upper triangular: the same. So
  the gain is `0`, not `d(d+1)/2`, and the formula `P + d² − d(d−1) − s` with `s = 0` (10, 21,
  16) is too large by `d(d+1)/2`. The hypotheses `[Nonempty (hid 0)]`, `[Nonempty (H 0)]` and
  `hdh0` are needed. The headers and the index (row 816: "A block with no hidden unit is excluded
  (the value is lower there)") say so.
- By compiling (`Chk.lean`): `ae_funDimLearned_relu_rmsNorm` instantiates with one token, `d =
  d_in = d_out = 2` and one hidden unit (a block narrower than `d`) and gives `fd = 13` there
  (`P = 12`), the value of my computation; `ae_funDimLearned_attention_rmsNorm` instantiates with
  two tokens that see each other and one head of width `1`.
- **`k ≠ 0` is needed too** (by hand): for an activation that is positively homogeneous of degree
  `0`, `B(λ n) = B(n)`, so `B(N_ε(h)) = B(h)`, and every invertible `G` at `h_0` (`E ↦ E G`,
  `A ↦ G⁻¹ A`, `W_read ↦ G⁻¹ W_read`) preserves the function with a learned skip. The paper's
  activations have `k = 1` or `2`.

### Check 4. `NoSymmetricPart` against equation (17)

**Verdict: the same condition. It is not vacuous, and it is false exactly where the conclusion
fails; for a block that is zero it is false, as it should be.** (By reading and by hand; three
facts by compiling.)

- The Lean text:

  ```
  def NoSymmetricPart (A : Arch T d 1) (ε : ℝ) (θ : Params A dIn dOut) (U : Set (Matrix T dIn ℝ)) : Prop :=
    ∀ (X : Matrix d d ℝ) (ψr : Matrix d (A.r 0) ℝ) (ψw : Matrix (A.w 0) d ℝ), Xᵀ = X →
      (∀ x ∈ U,
        fderiv ℝ (A.f 0) (rmsNorm ε (x * θ.E) * θ.read 0)
            (tangentRMS X (rmsNorm ε (x * θ.E)) * θ.read 0 + rmsNorm ε (x * θ.E) * ψr) * θ.write 0
          + A.f 0 (rmsNorm ε (x * θ.E) * θ.read 0) * ψw = 0) →
      X = 0
  ```
- **Expanding.** `tangentRMS X n` has the rows `(n X)_t − (⟨(n X)_t, n_t⟩ / d) n_t` (by `rfl`,
  `Chk.lean`), and `⟨(n X)_t, n_t⟩ = n_t X n_tᵀ` (compiled), so `tangentRMS X n = n X − q(n) n`
  with the paper's `q(n) = n X nᵀ / d`, row by row; this is also the paper's "for attention,
  `q(n) n` stands for the matrix with the rows `q(n_t) n_t`". Then the argument of `𝐃f` is
  `n (X W_read + ψr) − q(n) n W_read`, and the Lean equation is

  `𝐃f(n W_read)(n (X W_read + ψr)) W_write + f(n W_read) ψw = q(n) 𝐃f(n W_read)(n W_read) W_write`.

  The left side is `∂_ψ B(n)` for `ψ = (ψr + X W_read, ψw)`, and the right side is
  `q(n) 𝐃B(n) n`. **The term `n X W_read` goes into `ψ`:** it is the paper's "the change `n X_s` of
  the input moves the block as the entries `X_s W_read` at `W_read` do […] with `ψ` the entries
  of `η′` at the weights of the block plus these". Lean's `ψr`, `ψw` are the entries of `η′`
  itself. As `ψr` runs over all matrices, so does `ψr + X W_read`: the two families of
  conditions are the same, and `X = 0` is the paper's "`q = 0`, hence `X_s = 0`".
- **"For every `n` in the image of `N_ε`"** is `n = N_ε(x E)` for `x ∈ U`; with `U` everything and
  `E` of rank `d` the rows run over the open ball. For the ReLU-type blocks `U` is the set of the
  inputs off the kinks, as in the paper's Step 4 of part (ii).
- **It is the exact condition** (by hand). If a symmetric `X ≠ 0` and `ψr`, `ψw` satisfy the
  equation on `U`, the direction with the entries `E X`, `−X A`, `ψr`, `ψw`, `0` at `E`, `A`,
  `W_read`, `W_write`, `D` is flat on `U` (the stream has the derivative `x E X A − x E X A +
  D_θ g η = 0`), and it is not a rotation plus a direction of the block. So where
  `NoSymmetricPart` fails, the gain is smaller than `d(d+1)/2`. The hypothesis is as weak as it
  can be.
- **Not vacuous:** `X = 0`, `ψ = 0` always satisfies the equation, so the condition is a real
  implication; it is proved under conditions that hold at almost every parameter
  (`noSymmetricPart_mlp_rescale_rmsNorm`, `…_reglu_…`, `…_attention_…`).
- **A block that is zero.** By compiling (`Chk.lean`): for a ReLU block with no hidden unit
  (`hid = Empty`), `¬ NoSymmetricPart … θ Set.univ`, at every `θ`; and for any block,
  `¬ NoSymmetricPart … θ ∅` when `d = 2` (with no input the equation asks nothing). This agrees
  with Check 3: for the zero block the gain is `0`. The two general statements have
  `NoSymmetricPart` as a hypothesis, so they say nothing there, rightly; in the `_on` form `hw`
  makes the set of inputs nonempty.
- By compiling (`Chk2.lean`): for a block that is continuously differentiable everywhere, the
  statement of Steps 1 to 3 with `V` everything gives, for a direction of `flatSkips`, the last
  clause with `tangentRMS X n` in the place of `𝐃N_ε(x E)(x E X)` (by `fderiv_rmsNorm_mul`), and
  with a symmetric `X` and `Y = 0` this clause is the hypothesis of `NoSymmetricPart`. So Step 3
  and Step 4 fit together as in the paper.

### Check 5. The two general statements of `OneBlock/LearnedSkipGain.lean`

**Verdict: not refuted, in any of their consequences; I believe both by hand. For attention the
hypotheses (`E`, `D` of rank `d`, a token that sees a token, `S ≠ 0`) are enough.** Both are
proved at `588a9d0` (three standard axioms).

- The Lean text of the first:

  ```
  theorem funDimLearned_eq_funDim_residual_add_of_noSymmetricPart {A : Arch T d 1} {ε : ℝ}
      (hε : 0 < ε) (hA : A.χ = rmsNorm ε) (hf : ContDiff ℝ 1 (A.f 0)) (θ : Params A dIn dOut)
      (R : Fin 1 → Matrix d d ℝ) (hE : θ.E.rank = Fintype.card d) (hD : θ.D.rank = Fintype.card d)
      (hR : IsUnit (R 0).det) (hX : NoSymmetricPart A ε θ Set.univ) :
      funDimLearned A (θ, R) = funDim A 1 θ + Fintype.card d * (Fintype.card d + 1) / 2
  ```
  The second has an open cone `V` (`hV`, `hVs`), `hf : ContDiffOn ℝ 1 (A.f 0) V`, `hw`,
  `hX : NoSymmetricPart A ε θ {x | x * θ.E * θ.read 0 ∈ V}`, and `hK` (every direction `ψ` of the
  block, `ψ.E = 0`, `ψ.D = 0`, along which `B` has derivative zero at these inputs, lies in
  `Submodule.span ℝ {η | InsideBlocks A θ η}`), and concludes the same equality and a batch of
  inputs of the cone with this rank.
- **By hand.** Let `K_B` be the directions of the weights of the block along which `B(n)` has
  derivative zero at `n = N_ε(x E)`, `x ∈ U`. Steps 1 to 3 give for a flat direction `X`, `Y`;
  subtracting the direction of the two rotations with `X_a`, `Y` leaves `E X_s`, `−X_s A`, `0`
  and `D_θ g η′ = 0`, which is the hypothesis of `NoSymmetricPart`; so `X_s = 0` and
  `η′ ∈ K_B`. Hence the flat directions on `U` are the rotations (dimension `d(d−1)`, independent
  of `K_B` because `E X_a` and `Y D` determine `X_a` and `Y`) plus `K_B`. The same steps for the
  identity skip give one rotation plus the same `K_B` (it depends on `θ` only). So the two
  functional dimensions are `P + d² − d(d−1) − dim K_B` and `P − d(d−1)/2 − dim K_B`, at every
  such `θ` and every invertible `A`: the difference is `d(d+1)/2`. On a cone, `hK` makes the
  directions of `K_B` flat at every input, so "flat on `U`" and Lean's "flat" agree, for both
  networks. I see no clause that fails for `d = 0` (both sides `0`) or `d = 1`.
- **By a computation** (one block, `ε` between 0.2 and 0.7; skips `A = I`, `−I`, an orthogonal
  matrix, a matrix with singular values `1, …, 1, 10⁻⁷`, a random matrix; residual and learned
  network on the same batch; "gain" is the difference of the two ranks):

  | Statement | Weights (all allowed by the hypotheses) | Result |
  |---|---|---|
  | `funDimLearned_mlp_rescale_rmsNorm_eq_residual_add`, ReLU | generic (`d = 2`, 3 units); one hidden unit; a narrow block (`d = 3`, 2 units); `d_in, d_out > d`; all rows of `W_write` equal; two tokens | gain `d(d+1)/2` in all 30; values `P − d(d−1)/2 − s` and `P + d² − d(d−1) − s` in all (16, 19; 10, 13; 25, 31; 17, 20; 16, 19; 13, 16) |
  | the same, ReLU² | one hidden unit; narrow (`d = 3`); all write rows equal, `d_out > d` | gain and values right in all 15 |
  | `funDimLearned_reglu_rmsNorm_eq_residual_add` | one hidden unit (`d = 2`, `d = 3`); narrow (`d = 3`); all value columns equal and all write rows equal (`d = 2`, `d = 3`); value column of each unit equal to the gate column of the other | gain and values right in all (11, 14; 22, 28; 29, 35; 15, 18; 29, 35; 15, 18) |
  | `funDimLearned_attention_rmsNorm_eq_residual_add` | one token, `H = 1`, `d_h = 1`; zero queries with `S ≠ 0`; a causal mask (one head, two heads); `W_V` of rank one, so `S` of rank one (`d = 3`); a mask where token 0 sees token 1 only and token 1 sees none; `d_h = 3 > d = 2`; zero keys on three tokens, `d_out > d` | gain `d(d+1)/2` in all 40 (residual, learned: 10, 13; 12, 15; 13, 16; 19, 22; 30, 36; 10, 13; 15, 18; 14, 17) |
  | all three, `d = 1` (the statements at one parameter do not ask `d ≥ 2`) | ReLU, ReLU², ReGLU with one hidden unit; attention on two tokens, and on one token with `H = 2`, `d_h = 2` | gain `1` in all 30 |

  Files: `ls17_relu.out`, `ls17_relusq.out`, `ls17_reglu.out`, `ls17_reglu2.out`,
  `ls17_attn1.out`, `ls17_attn2.out`, `ls17_d1.out`. ReLU-type cases use eight inputs per
  parameter (six in the two-token case, see below); the special cases were repeated on a second
  batch.
- **Two results that looked different and are not.**
  1. ReLU, two tokens (`ls17_relu.out`): 11 and 14 for 13 and 16, on 62 inputs. At that draw the
     two columns of `W_read` are nearly parallel, and no token of the batch fell into two of the
     four sign regions (`ls17_replay.out`: 50 and 74 tokens in two regions, none in the others).
     With 400 and with 1600 inputs of the same weights: 13 and 16. With fresh weights and one,
     two and three tokens: 13 and 16 in all 18 batches (`ls17_twotok.out`). The brief's warning
     about small batches is right; six inputs per parameter were not enough here.
  2. ReGLU, the case labelled "(allowed)" at line 38 of `ls17_reglu.out` (14 and 17 for 15 and
     18): my label is wrong. In that draw the value column of unit 1 equals its own gate column,
     which `OneBlockGenericReGLURMS.value_not_gate` excludes. The corrected cases are in
     `ls17_reglu2.out`, with every clause of the structure checked on the numbers, and agree.
- **What happens outside the hypotheses** (these are not counterexamples):
  - Attention with `W_O = 0`, so `S = 0`: gain `0` (`ls17_attn3.out`, two batches). `hS` cannot
    simply be dropped. Two heads whose `W_V W_O` cancel (`S = 0`, block not zero): gain `3`. So
    `S ≠ 0` is sufficient and not necessary.
  - ReGLU with the value column of a unit proportional to its gate column: residual 14 and
    learned 17, one less than the formula each, gain still `3`. `value_not_gate` is needed for the
    values, as in the residual statement.
  - ReLU with one column of `W_read` minus another: 13 and 16, as the formula.
- **Is it enough for attention? Yes** (by hand, the argument of the file's header, which I
  checked): on inputs with all tokens equal to `v`, a token that sees some token has the output
  `v S` whatever the queries and keys are, so its row of the equation is `v (X S + ∂_ψ S) = q(v)
  v S` for all `v` in the ball: a linear map equal to a cubic one, so `q(v) v S = 0`, and
  `S ≠ 0` gives `q = 0` on an open set. No second token, no condition on `d_h`, `H` or the mask
  beyond one token that sees a token. If no token sees a token the block is zero and the gain
  is `0`.

### Check 6. Steps 1 to 3

**Verdict: SAME as the paper's text, term by term, and stated more generally (any block that is
continuously differentiable on an open cone).** (By reading; one specialization by compiling.)

```
theorem exists_of_flatSkipsOn_learned_rmsNorm {A : Arch T d 1} {ε : ℝ} (hε : 0 < ε)
    (hA : A.χ = rmsNorm ε) (V : Set (Matrix T (A.r 0) ℝ)) (hV : IsOpen V)
    (hVs : ∀ M ∈ V, ∀ c : T → ℝ, (∀ t, 0 < c t) → (Matrix.of fun t i => c t * M t i) ∈ V)
    (hf : ContDiffOn ℝ 1 (A.f 0) V) (θ : Params A dIn dOut) (R : Fin 1 → Matrix d d ℝ)
    (hE : θ.E.rank = Fintype.card d) (hD : θ.D.rank = Fintype.card d) (hR : IsUnit (R 0).det)
    (hw : ∃ w : dIn → ℝ, (Matrix.of fun _ : T => w) * θ.E * θ.read 0 ∈ V)
    (η : Params A dIn dOut) (ρ : Fin 1 → Matrix d d ℝ)
    (hη : (η, ρ) ∈ flatSkipsOn A (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) (θ, R)
      {x | x * θ.E * θ.read 0 ∈ V}) :
    ∃ X Y : Matrix d d ℝ, Yᵀ = -Y ∧ η.E = θ.E * X ∧ ρ 0 = R 0 * Y - X * R 0 ∧ η.D = -(Y * θ.D) ∧
      ∀ x : Matrix T dIn ℝ, x * θ.E * θ.read 0 ∈ V →
        fderiv ℝ (A.f 0) (rmsNorm ε (x * θ.E) * θ.read 0)
            (fderiv ℝ (rmsNorm ε : Matrix T d ℝ → Matrix T d ℝ) (x * θ.E) (x * θ.E * X) * θ.read 0
              + rmsNorm ε (x * θ.E) * η.read 0) * θ.write 0
          + A.f 0 (rmsNorm ε (x * θ.E) * θ.read 0) * η.write 0
          = A.f 0 (rmsNorm ε (x * θ.E) * θ.read 0) * θ.write 0 * Y
```

| Paper | Lean | |
|---|---|---|
| "Let `η` be flat" (for ReLU-type blocks: at the inputs off the kinks) | `hη`: `(η, ρ)` flat at the inputs with `x E W_read ∈ V` | same; `V` everything gives "flat at every input" (compiled, `Chk2.lean`) |
| "`E A` […] has rank `d_model` since `A` is invertible for generic parameters" | `hE`, `hR`; `hD` for Step 1 ("`D` has full row rank") | same, as conditions at one parameter |
| the inputs `t w` of Step 2, "`w E Y_s Eᵀ wᵀ = 0` for all `w` in an open set" | `hV` (open), `hVs` (cone: `N_ε` scales every row by a positive number, so `t w` and `N_ε(t w E) W_read` stay in `V`), `hw` (some input with equal rows in `V`) | Lean writes out what the paper uses silently for the ReLU-type blocks; for `V` everything all three are empty |
| "`η_D = −Y D` with `Y` antisymmetric" | `Yᵀ = -Y`, `η.D = -(Y * θ.D)` | same |
| "`η_E = E X` with `X = E⁺ η_E`" | `η.E = θ.E * X` | same (`X` is unique, `E` has rank `d`) |
| "`η_A = A Y − X A`" | `ρ 0 = R 0 * Y - X * R 0` | same |
| "`D_θ g η = g(x) Y`" | the last clause | same: the left side is the chain rule for `g(x) = f(N_ε(x E) W_read) W_write` along `η`, with the derivative `𝐃N_ε(x E)(x η_E)` of the input of the block and `x η_E = x E X`; the right side is `g(x) Y` |

The paper's next line, "`𝐃N_ε(x E)(x E X) = n X − q(n) n`", is `fderiv_rmsNorm_mul` (`ε > 0`), not
part of this statement. For attention the paper takes "one such row for every token"; Lean's
`hw` asks one input with equal rows, which for attention (`V` everything) is no condition.

### Check 7. The upper triangular skip

**Verdict: the definitions are right, the value is the paper's, the two general statements are
true as far as I could test, and the hypothesis of width at least `d` is one more than Theorem
B.1 (iii) has (the Scope of the main text has it).** (By reading; the definitions by compiling;
the two statements by a computation and by hand.)

- `upperTriangular d` has the carrier `{M | M.BlockTriangular id}`. By compiling (`Chk.lean`):
  `M ∈ upperTriangular d ↔ ∀ i j, j < i → M i j = 0`: the entries below the diagonal vanish (row
  index larger than column index), for the linear order on `d` that the statement is given. The
  statements hold for every linear order, so also for lower triangular matrices (the reversed
  order). The paper's `h_1 = x E A + …` multiplies rows from the right, and "upper triangular" is
  the usual sense. `finrank_upperTriangular`: `d(d+1)/2`, right.
- **The value.** Lean: `funDimLearnedTri … p + card d * (card d - 1) / 2 = finrank ℝ (Params …) +
  card d * (card d + 1) / 2` (with `+ ∑ ℓ, card (hid ℓ)` on the left for SwiGLU and GeGLU), that
  is `P + d(d+1)/2 − d(d−1)/2 − s = P + d − s`; and `funDimLearnedTri … p = funDim … 1 θ' + card d
  * (card d + 1) / 2`. Paper, Step 5: the triangular network "has […] `d(d+1)/2` more
  parameters", its rotations "have dimension `d(d−1)/2`", "In both cases the functional dimension
  is larger by `d_model (d_model + 1)/2`". The same numbers; both divisions are exact. By a
  computation (`ls17_tri.out`): 18 for tanh (`d = 2`, `P = 16`), 39 for tanh (`d = 3`, `P = 36`),
  20 for SwiGLU (`d = 2`, `P = 20`, `s = 2`).
- **`funDimLearnedTri_eq_funDimLearned`** (`hε`, `hA`, `hf : ∀ ℓ, Differentiable ℝ (A.f ℓ)`, any
  `θ`, `R : Fin 1 → upperTriangular d`, `hR : IsUnit (R 0 : Matrix d d ℝ).det`): by hand, every
  direction `a` of the skip is a triangular one plus `−X_0 R` with `X_0` antisymmetric (an
  antisymmetric `X` with `X R` upper triangular is `0` when `R` is invertible), and the rotation
  of `h_0` by `X_0` is flat at every `θ`, so the two Jacobians have the same range on every
  batch. No rank of `E` or `D` is needed, and none is asked. By a computation (`ls17_tri.out`,
  21 comparisons at an invertible `R`, all equal): tanh and SwiGLU; `R = I`, a generic triangular
  `R`, `R_00 = 10⁻⁶`; weights: generic, a narrow block, `E` of rank one (14 = 14), `W_write = 0`
  (11 = 11), `d_in = 1 < d` (12 = 12). **`hR` is needed** (`ls17_trizero.out`): at `R = 0` the
  triangular family has 17 and the full family 18 (`d = 2`), 36 and 39 (`d = 3`); at a triangular
  `R` of rank one 38 and 39 (`d = 3`). At a triangular `R` with only `R_00 = 0` the two were equal
  in my seven draws.
- **`funDimLearned_cob`** (any `L`; `Q` orthogonal; at `(θ.cob Q Q, cobSkip S Q)` the same value
  as at `(θ, S)`): by hand, the map `(θ, S) ↦ (θ.cob Q Q, cobSkip S Q)` is a linear bijection of
  the parameters that preserves the function, so the Jacobians on every batch have the same
  rank (S proof of Theorem A.5: "the two Jacobians have the same rank […] For learned skips the
  same argument applies"). The hypotheses `hε` and `hf` are not needed for this, and do no harm.
  By a computation for one block (`ls17_cob.out`, 12 comparisons, all equal): `Q_0` a rotation,
  `Q_1` of determinant `−1`; `S` random, `I`, singular; `E` of rank one; also a ReLU block.
  Several blocks: by hand only.
- **Width at least `d`.** The eight `ae_` statements have `hhid`. Theorem B.1 (iii) has none; the
  Scope has it. The cause is the route through the skip `0` (`LearnedSkipKinds.lean`). The value
  holds numerically for a narrow block too (tanh, `d = 2`, one hidden unit: 14 = `P + d`).

### Check 8. What is still not covered of Theorem B.1 (iii); Theorem 4.6

| Clause of Theorem B.1 (iii) | Covered in the seven files and `LearnedSkipKinds.lean`? |
|---|---|
| full skip, `ε > 0`, tanh, GELU, SwiGLU, GeGLU | width at least `d` only (sixteenth audit) |
| full skip, `ε > 0`, ReLU, ReLU², ReGLU | yes, any width from one hidden unit on; in the paper's sense (the batch statements) |
| full skip, `ε > 0`, attention | yes: `H ≥ 1`, `1 ≤ d_h ≤ d`, two tokens; this is the theorem's "`H` heads of width `d_h ≤ d_model` […] on sequences of at least two tokens" |
| upper triangular skip, `ε > 0`, tanh, GELU, SwiGLU, GeGLU | width at least `d` only |
| upper triangular skip, ReLU, ReLU², ReGLU, attention | not in the seven files. Stated since `da0be3b` in `OneBlock/LearnedSkipTriangularSmooth.lean` (attention) and `OneBlock/LearnedSkipTriangularRescale.lean` (ReLU, ReLU², ReGLU); neither has `sorry` at `e17b4d3`, and the index marks both proved. Not in my brief, not compared by me or, as far as the index says, by any reader |
| tanh, GELU, SwiGLU, GeGLU blocks narrower than `d` (full or triangular) | no. The general statement of `LearnedSkipGain.lean` would give them, but `NoSymmetricPart` (Step 4) is proved for ReLU, ReLU², ReGLU and attention only; for these four kinds the paper's Step 4 is the argument on rays `n = t n̂`, which has no Lean statement |
| "and it satisfies the equality condition" | in content: the value statements say `fd = (P + d²) − d(d−1) − s`, parameters minus the dimension of the symmetries. Lean has no definition of the equality condition for the network with a learned skip |
| "For `ε = 0` it exceeds that of the residual network with `ε = 0` by at most `d(d+1)/2 − 1`, with equality for ReLU, ReLU² and ReGLU blocks" | no. `funDimLearned_add_le_rmsNorm'` holds for `ε = 0` with the rotations only (two less than the paper's bound). My computation at `ε = 0` gives the paper's values (ReLU 17, ReLU² 29, two below Lean's bound; `ls17_epsle0.out`) |

- **Theorem 4.6 (ii), last sentence, of the main text: covered in full for the eight kinds under
  the Scope, and proved at `588a9d0`.** In the main text a learned skip is "a trainable
  `d_model × d_model` matrix" (Setup), the full skip. The eight statements are
  `ae_funDimLearned_{tanh,gelu,swiglu,geglu}_rmsNorm_eq_residual_add`
  (`LearnedSkipKinds.lean`) and `ae_funDimLearned_{relu,reluSq,reglu,attention}_rmsNorm_eq_residual_add`.
- **Theorem 4.6 as a whole.** By the index (rows 386, 387, 632 to 642, 763, 769; I read the rows
  and did not compare these older statements again): (i) for the eight kinds, with the skipless
  value and "exactly `d²`"; (ii), first sentence and the gain of at least `d(d−1)/2`, for the
  eight kinds. With the last sentence, every sentence of Theorem 4.6 has a statement for every
  kind, all marked proved. What remains "in content" is the phrase "satisfies the equality
  condition", which is everywhere a value, not a definition.
- **Is the index honest? The rows of the seven files are (812 to 818). Four other rows are out of
  date** and still say that the learned skip is not stated for ReLU, ReLU², ReGLU and attention
  blocks: 642, 769, 811, and the last sentence of 812 (Corrections 2 to 5). The paragraph "Not
  stated yet from the main text of the skips paper" said it too until `7ef6b40`; at `175a7d6` it
  is corrected (line 674).

---------------------------------------------------------------------------------------------------

## Part 2: the statements, file by file

Verdicts: SAME, LEAN STRONGER, LEAN WEAKER, DIFFERENT, PART, FALSE. All 39 theorems are proved at
`588a9d0` (no `sorry`, three standard axioms, `Ax.out`). None is FALSE.

### `OneBlock/LearnedSkipTriangular.lean` (3 definitions, 11 theorems)

Paper: S Appendix B, "A learned skip `A` is full or upper triangular"; Theorem B.1 (iii) and its
Step 5.

| Name | Verdict |
|---|---|
| `upperTriangular` | SAME ("upper triangular"), for any linear order on the index |
| `triSkips` | SAME (the inclusion; "view the network as the network with a full `A` restricted to triangular skips") |
| `funDimLearnedTri` | SAME: the functional dimension of the network with an upper triangular learned skip |
| `finrank_upperTriangular` | PART (proof piece: "`d(d+1)/2` more parameters") |
| `funDimLearnedTri_eq_funDimLearned` | LEAN STRONGER than the paper's "In both cases the functional dimension is larger by `d(d+1)/2`": at every `θ` and every invertible triangular skip, any differentiable block. Another route than the paper's count |
| `funDimLearned_cob` | PART (proof piece, S proof of Theorem A.5: symmetric parameters have Jacobians of the same rank); any number of blocks |
| `ae_funDimLearnedTri_tanh_rmsNorm`, `…_gelu_…`, `…_swiglu_…`, `…_geglu_…` | PART of Theorem B.1 (iii): the value ("satisfies the equality condition") for the triangular skip, four of the eight kinds, width at least `d`, `ε > 0`. Within this range SAME |
| the four `…_eq_residual_add` | PART of Theorem B.1 (iii), "exceeds that of the residual network of part (ii) by exactly `d(d+1)/2`", the same range. Within it SAME |

### `OneBlock/LearnedSkipOn.lean` (1 definition, 4 theorems)

Paper: S Appendix B, "Notation and flat directions".

| Name | Verdict |
|---|---|
| `flatSkipsOn` | SAME: the directions that are flat at the inputs of a set ("'every input' means every such input") |
| `flatSkips_le_flatSkipsOn` | PART (immediate) |
| `funDimSkips_add_finrank_flatSkips'` | LEAN STRONGER than "the functional dimension at `θ` is `P − dim K(θ)`": no hypothesis at all; `K` is Lean's `flatSkips` |
| `exists_jacobianRankSkips_add_finrank_flatSkipsOn` | SAME as "some finite batch has kernel exactly `K(θ)`", for the inputs of a set where the output is differentiable in the weights and the skips |
| `funDimLearned_add_le_rmsNorm'` | PART (the upper bound of Step 5) and LEAN STRONGER in its range: any block, any real `ε`. For `ε = 0` it is weaker than the paper's bound (no scalings); the docstring says so |

**Are the four true with no hypothesis on the blocks? Yes** (by hand).
- Mathlib's derivative at a point of non-differentiability is `0`. A batch map `p ↦ (F_p(x_i))_i`
  is differentiable at `p` exactly when every component is, so a batch with one input of
  non-differentiability has the rank `0`, and such an input puts no condition on `flatSkips`.
  Over the inputs of differentiability the usual argument runs (a decreasing chain of kernels
  stops). With no such input both sides are right too: `fd = 0`, every direction flat.
- The same for a set `U` with `hU`; with `U` empty the empty batch has rank `0` and every
  direction is flat on `U`.
- **`funDimLearned_add_le_rmsNorm'` for `ε ≤ 0`: right.** Lean's `rmsRow ε v` is `(√(v·v/d +
  ε))⁻¹ • v`, and `0` where the root is `0`. For an orthogonal `Q`, `(v Q)·(v Q) = v·v`, so
  `rmsRow ε (v Q) = rmsRow ε v Q` for every real `ε`. Hence the two rotations (with `A ↦ Q_0⁻¹ A
  Q_1`) preserve the function exactly, for any block, and a curve that preserves the function
  has a flat velocity whether or not the output is differentiable. They are independent of each
  other and of `U` (a direction of `InsideBlocks` has the entries `0` at `E` and `D`; `E X_0` and
  `X_1 D` determine `X_0`, `X_1`). By a computation (`ls17_epsle0.out`, 27 cases: ReLU, tanh,
  ReLU²; `ε = 0`, `−0.3`, `−2`; `A` random, `I`, `0`): no rank above the bound; equality for
  `ε < 0` at an invertible skip (19, 18, 31), two below it for `ε = 0` (17, 16, 29).

### `OneBlock/LearnedSkipSteps.lean` (1 theorem)

| Name | Verdict |
|---|---|
| `exists_of_flatSkipsOn_learned_rmsNorm` | SAME as Steps 1 to 3 of Part (iii) (Check 6); LEAN STRONGER in generality (any block that is `C¹` on an open cone of pre-activations) |

### `OneBlock/LearnedSkipGain.lean` (1 definition, 2 theorems)

| Name | Verdict |
|---|---|
| `NoSymmetricPart` | SAME as "equation (17) […] `q = 0`, hence `X_s = 0`", as a condition on `θ` and a set of inputs (Check 4) |
| `funDimLearned_eq_funDim_residual_add_of_noSymmetricPart` | LEAN STRONGER than Steps 3 and 5 at generic parameters: at every `θ` with `E`, `D` of rank `d`, every invertible skip, any `C¹` block with Step 4 (Check 5) |
| `funDimLearned_eq_funDim_residual_add_of_noSymmetricPart_on` | the same on a cone, with `hK` in the place of "`K_B` consists of the symmetries inside the block"; the batch is the paper's functional dimension for ReLU-type blocks |

### `OneBlock/LearnedSkipRescale.lean` (10 theorems)

| Name | Verdict |
|---|---|
| `noSymmetricPart_mlp_rescale_rmsNorm` | SAME as Step 4 for ReLU and ReLU² ("Replacing `n` by `λn` […] `q = 0` wherever `B ≠ 0`"), under `OneBlockGenericRMS`; for any activation that is homogeneous of degree `k ≥ 1` with Lemma B.3 |
| `funDimLearned_mlp_rescale_rmsNorm_eq_residual_add`, `funDimLearned_mlp_rescale_rmsNorm`, `exists_jacobianRankSkips_mlp_rescale_rmsNorm` | LEAN STRONGER: at one parameter under the conditions of the proof, every invertible skip |
| `ae_funDimLearned_relu_rmsNorm`, `ae_exists_jacobianRankSkips_relu_rmsNorm`, and with `reluSq` | SAME as Theorem B.1 (iii) for the full skip, `ε > 0` (value, "satisfies the equality condition", in the paper's sense by the pair); fewer hypotheses than the Scope (any width from 1) |
| `ae_funDimLearned_relu_rmsNorm_eq_residual_add`, and with `reluSq` | SAME as Theorem 4.6 (ii), last sentence, for ReLU and ReLU² |

### `OneBlock/LearnedSkipReGLU.lean` (7 theorems)

| Name | Verdict |
|---|---|
| `noSymmetricPart_reglu_rmsNorm` | SAME as Step 4 for ReGLU (`k = 2`), under `OneBlockGenericReGLURMS` |
| `funDimLearned_reglu_rmsNorm_eq_residual_add`, `funDimLearned_reglu_rmsNorm`, `exists_jacobianRankSkips_reglu_rmsNorm` | LEAN STRONGER (one parameter, every invertible skip); `s = 2 d_hidden`, the paper's count |
| `ae_funDimLearned_reglu_rmsNorm`, `ae_exists_jacobianRankSkips_reglu_rmsNorm` | SAME as Theorem B.1 (iii), full skip, `ε > 0` |
| `ae_funDimLearned_reglu_rmsNorm_eq_residual_add` | SAME as Theorem 4.6 (ii), last sentence, for ReGLU |

### `OneBlock/LearnedSkipAttention.lean` (4 theorems)

| Name | Verdict |
|---|---|
| `noSymmetricPart_attention_rmsNorm` | SAME conclusion as Step 4 for attention; LEAN STRONGER in its hypotheses (`E` of rank `d`, a token that sees a token, `S ≠ 0`; no two tokens, no generic condition on the heads). Another proof than the paper's two-token one |
| `funDimLearned_attention_rmsNorm_eq_residual_add` | LEAN STRONGER (one parameter, every invertible skip, any mask with one token that sees a token, any `H`, `d_h`) |
| `ae_funDimLearned_attention_rmsNorm` | SAME as Theorem B.1 (iii), full skip, `ε > 0`: `s = 2 H d_h²` |
| `ae_funDimLearned_attention_rmsNorm_eq_residual_add` | SAME as Theorem 4.6 (ii), last sentence, for attention |

### The index rows of the seven files, and `checks/Axioms.lean`

By a script (`index_names.py`, `index_names.out`), at `e17b4d3`: every one of the 44 public names
is in the row of its file (rows 812 to 818), 35 written out and 9 by a stated abbreviation ("the
same two with `gelu`, `swiglu`, `geglu`", "the same three with `reluSq`"); all 39 theorems stand
in `checks/Axioms.lean`; all seven rows say "proved", which is right since `588a9d0`. At `8a637fe`
the four rows of `LearnedSkipGain`, `…Rescale`, `…ReGLU`, `…Attention` said "in work" and their
23 theorems were not yet in `checks/Axioms.lean`, rightly. Nothing is missing in the rows. What
is out of date or thin: the corrections below.

---------------------------------------------------------------------------------------------------

## What the authors should know

Nothing false, vacuous, drifted or misdescribed in the 44 names. In order of weight:

1. **The index still says in four rows that the learned skip is not stated for ReLU, ReLU²,
   ReGLU and attention blocks.** It is stated and, since `588a9d0`, proved (Corrections 2 to 5).
2. **Theorem 4.6 (ii), last sentence, is now covered for all eight kinds under the Scope.**
   Theorem B.1 (iii) is not: tanh, GELU, SwiGLU, GeGLU blocks narrower than `d` (no Step 4 for
   these kinds in Lean), `ε = 0`; the triangular skip for the four other kinds is in two new
   files (stated at `da0be3b`, without `sorry` at `e17b4d3`), which no reader has compared.
3. **`NoSymmetricPart` is exactly the right condition.** Where it fails there is a flat direction
   with a symmetric part and the gain is smaller. It fails for a block that is zero (compiled),
   and there the gain is `0` (computed: 7, 15, 13 with and without the learned skip).
4. **The exceptions that the hypotheses exclude are real:** no hidden unit, no head, a head of
   width `0`, no token that sees a token (gain `0`); `k = 0` (every invertible change of basis at
   `h_0` passes); for attention `S = 0` through `W_O = 0` (gain `0`). `S ≠ 0` is sufficient and
   not necessary (two heads that cancel: gain `3`).
5. **Lean asks less than the Scope** for ReLU, ReLU² and ReGLU (one hidden unit is enough, as in
   Theorem B.1 (iii)) and for attention (no `H d_h = d`); the statements at one parameter ask no
   `d ≥ 2`, and hold for `d = 1` in my computation. The triangular statements ask width at least
   `d`, which Theorem B.1 (iii) does not.
6. `funDimLearnedTri_eq_funDimLearned` asks no rank of `E` or `D`, rightly, and needs the
   invertible skip (at `R = 0` the two families differ by `d(d−1)/2`). `funDimLearned_cob` has two
   hypotheses that it does not need (`hε`, `hf`).
7. **A small batch can give a lower rank for ReLU-type blocks**, as the brief warns: with two
   nearly parallel columns of `W_read`, 62 inputs of two tokens gave 11 and 14 for 13 and 16; 400
   inputs gave 13 and 16.
8. For ReGLU, `value_not_gate` is needed for the values (14 and 17 for 15 and 18 where it fails);
   the gain was still `3` there.
9. "Satisfies the equality condition" is, for every learned-skip statement, the value
   `(P + d²) − d(d−1) − s` (or `P + d(d+1)/2 − d(d−1)/2 − s`). Lean has no definition of the
   symmetries of the network with a learned skip.

## Corrections for `STATEMENTS.md` (line numbers of `175a7d6`)

1. The paragraph "Not stated yet from the main text of the skips paper" (line 674) said until
   `7ef6b40` "the sentence of Theorem 4.6 (ii) on a learned skip for ReLU, ReLU², ReGLU and
   attention blocks". **Already corrected at `175a7d6`:** "The sentence of Theorem 4.6 (ii) on a
   learned skip is proved for the eight kinds of block". Nothing more to do.
2. Line 642 (`OneBlock/ResidualRMSGain.lean`): "Not stated: its sentence on a learned skip (B.1
   (iii))". Out of date; point to rows 811 and 816 to 818.
3. Line 769 (`Residual/DepthAttentionRMSDim.lean`): "(its sentence on a learned skip is not
   stated)". Out of date; write "(its sentence on a learned skip: the row of
   `OneBlock/LearnedSkipAttention.lean`)".
4. Line 811 (`OneBlock/LearnedSkipKinds.lean`): "Not stated: ReLU, ReLU², ReGLU and attention
   blocks (the skipless value under pre-RMSNorm is not proved for them, so the route through the
   skip `0` does not reach them)". Write: "ReLU, ReLU², ReGLU and attention blocks: the rows of
   `OneBlock/LearnedSkipRescale.lean`, `…ReGLU.lean`, `…Attention.lean`, by the paper's route".
   Keep "blocks narrower than `d`" and "`ε = 0`" for these four kinds.
5. Line 812 (`OneBlock/LearnedSkipTriangular.lean`): "Not stated: ReLU, ReLU², ReGLU and
   attention blocks". Since `da0be3b` they are stated in rows 819 (attention) and 820 (ReLU,
   ReLU², ReGLU), both "proved" at `e17b4d3`; say so. Add:
   "`funDimLearnedTri_eq_funDimLearned` is for every `θ` (no rank is asked) and any
   differentiable block, and needs the invertible skip (at the skip `0` the two families differ
   by `d(d−1)/2`); `funDimLearned_cob` is for any number of blocks; width at least `d` is the
   Scope's, Theorem B.1 (iii) has no hypothesis on the width".
6. Line 815 (`OneBlock/LearnedSkipGain.lean`). Nothing wrong. Could add: "`NoSymmetricPart` is
   necessary for the conclusion (where it fails a flat direction has a symmetric part); it fails
   for a block that is zero".
7. Line 816 (`OneBlock/LearnedSkipRescale.lean`). Nothing wrong. Could add: "the statements at
   one parameter ask no `d ≥ 2`; the Scope's `d_hidden ≥ d` is not asked; `k ≥ 1` is needed".
8. Line 818 (`OneBlock/LearnedSkipAttention.lean`). Nothing wrong. Could add: "`H d_h = d` is not
   asked; `S ≠ 0` is sufficient and not necessary, and cannot be dropped (`W_O = 0`: the gain is
   `0`)".
9. Lines 186 to 191, "Not yet compared by such a reader […] (these seven are with the reader of
   the seventeenth audit, part A)": after this audit take out the seven files of this brief
   (compared at `8a637fe` and `588a9d0`; unchanged at `e17b4d3`).
10. Outside the index, the header of `OneBlock/LearnedSkipTriangular.lean`, line 36 ("Not stated
    here: ReLU, ReLU², ReGLU and attention blocks; …"): add where they are stated now. The
    headers of `OneBlock/LearnedSkipRescale.lean`, `…ReGLU.lean`, `…Attention.lean` end with "Not
    stated here: the upper triangular skip": the same.

## What I could not check

- **The proofs.** I read none as a proof. "Proved" means no `sorry` in the file and the three
  standard axioms in the build of `/home/claude/lp/lean` at `588a9d0`.
- **The build.** I did not build the library. I compiled my files against the build of
  `/home/claude/lp/lean` (its owner's), read-only; `/home/claude/lw` has no compiled copy of
  these files.
- **`OneBlock/LearnedSkipTriangularSmooth.lean` and `OneBlock/LearnedSkipTriangularRescale.lean`**
  (new at `da0be3b`, the triangular skip for attention, ReLU, ReLU², ReGLU), and the rows 819,
  820 of the index: not in my brief, not compared.
- **The older statements for Theorem 4.6 (i) and the first sentence of (ii)** (rows 386, 387, 632
  to 642, 763, 769): I read the rows of the index, not the Lean statements again.
- **The two general statements, beyond their consequences.** The computation covers one block of
  the kinds ReLU, ReLU², ReGLU and attention with `d ≤ 3`, at most three tokens, one draw of the
  weights per case (two for the special ones), 60 or 80 digits. It supports the statements and
  proves nothing. I did not test the `_on` form with a cone other than "no zero entry", and no
  tanh, GELU, SwiGLU or GeGLU block against `NoSymmetricPart` (Lean has no Step 4 for them).
- **`funDimLearned_cob` for several blocks, and the four statements of `LearnedSkipOn.lean` in
  general:** by hand only; the upper bound for `ε ≤ 0` also by 27 computed cases.
- **That `S ≠ 0` and `value_not_gate` cannot be weakened:** I showed one failure each without
  them, not the weakest sufficient condition.
- **The coordinator's scripts** `learned_skip_relu_attention_check_2026-11-24.py` and
  `learned_skip_triangular_check_2026-11-24.py`: not run; I read their outputs.

Scratch files: `/home/claude/audit17a/` (`stmts.py`, `cmp_stmts.py`, `index_names.py`,
`Ax.lean`, `Sig.lean`, `Chk.lean`, `Chk2.lean`, `ls17core.py`, `ls17run.py`, `ls17more.py`,
`ls17replay.py`, `ls17fd.py`, with their outputs `*.out`). One label in `ls17_reglu.out` is
wrong (line 38, "(allowed)": that case violates `value_not_gate`); the corrected cases are in
`ls17_reglu2.out`.
