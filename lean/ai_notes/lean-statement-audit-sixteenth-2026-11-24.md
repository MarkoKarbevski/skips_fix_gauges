STATUS: complete

# Sixteenth audit of Lean statements against the papers (24 November 2026)

Reader: an independent reader who did not write the statements. Brief:
`/home/claude/proj_up/audit16_brief_2026-11-24.md`. I audited statements and definitions, not
proofs. I changed no repository file, ran no `lake build`, made no commit and no push. My files are
in `/home/claude/audit16/`.

Library: `/home/claude/lw/lean` (branch `lean-wip`).

- **Commit at the start: `a8aa4e1312ea2efcb1df4c1ffa2182a129c6ca0b` (16:45:33 UTC).** I read every
  statement at this commit.
- **Commit at the end: `4e167890ba1bc584652d41b96ae909bbda3dc5fa` (17:01:04 UTC),** still the head
  at 17:15 UTC. Thirteen commits lie in between (among them `7df0b9b`, `a8a247d`, `c55748b`,
  `4579a24`, `111499b`). In the twelve files only proofs were added.
  Compared by a script of mine (`stmts.py`, `omits.py`: statement text, docstring, and the `omit`
  lines of every public name, old file against new): **no statement and no docstring changed, with
  one exception of form:** the three theorems of `OneBlock/LearnedSkip.lean`
  (`funDimSkips_add_finrank_flatSkips`, `ae_funDimSkips_ge`, `funDimSkips_comp_le`) got the line
  `omit [DecidableEq d] in`, so they lost one unused instance argument. Their meaning is the same.
- **Files with `sorry`.** At `a8aa4e1`: `Dimension/IdentifiableIffTransformer.lean` (8),
  `OneBlock/LearnedSkip.lean` (3), `OneBlock/LearnedSkipZero.lean` (1),
  `OneBlock/LearnedSkipBound.lean` (1), `OneBlock/LearnedSkipKinds.lean` (8); the seven other
  files of the brief had none. At `4e16789`: none of the twelve files. One file of the library has
  `sorry` there, `OneBlock/LearnedSkipTriangular.lean`, which appeared at `c55748b` (16:56:39). It
  is not in my brief and I did not compare it.
- The twelve files have 78 public names: 7 definitions and 71 theorems (4, 4, 8, 12, 8, 7, 4,
  2 + 11, 5 + 3, 1, 1, 8, as the brief says).
- At `4e16789` all 78 depend on `propext`, `Classical.choice`, `Quot.sound` only (by compiling,
  `Ax.lean`, `Ax.out`). At 16:57 UTC, with an earlier build, the two general steps
  (`funDim_add_finrank_le_funDimSkips_zero`, `funDimLearned_add_le_rmsNorm`) and the eight named
  forms still had `sorryAx`.

Papers, as text: the skips paper ("S", `skips.txt`) and the dimension paper ("D", `dim.txt`). Line
numbers of `STATEMENTS.md` are those of `4e16789`.

How I checked.

- "By reading": every public statement and docstring of the twelve files in full, the definitions
  they use (`Arch`, `Params`, `hidden`, `eval`, `Params.cob`, `cobSkip`, `Params.rescale`,
  `Params.headsQK`, `Params.headsVO`, `Params.sumOf`, `sumFst`, `sumSnd`, `Arch.mlp`, `Arch.gated`,
  `Arch.attention`, `attnWeights`, `Arch.sum`, `funDim`, `jacobianRank`, `flat`, `antisymmetric`,
  `InsideBlocks`, `rmsRow`, `rmsNorm`), and the paper passages that the brief names.
- "By hand": a short argument of my own, written where it is used.
- "By compiling": scratch files of mine in `/home/claude/audit16/`, compiled with `lean` 4.36.0
  through `LEAN_PATH` (the paths that `lake env` gives from `/home/claude/lw/lean`, with the
  library's own build replaced by a copy of `/home/claude/lp/lean/.lake/build`, taken at 17:04 UTC
  when `lp` was at `4e16789`; the sources of `lp` and `lw` were the same then, by `diff -rq`, and
  every compiled file was newer than its source). `Ax.lean` (axioms), `Chk.lean` and `Chk2.lean`
  (checks of Part 1), `Cex.lean` (the masks). All compile without error (`*.out`).
- "By a computation": my own script `learned_skip_refute.py` (mpmath, 50 digits, exact
  forward-mode derivatives, rank from the singular values with the gap printed), output
  `learned_skip_refute.out`. I did not use the coordinator's script; I read its output afterwards, and
  the ranks that both compute agree.

**Short answer. Nothing false and nothing vacuous was found. One thing is described more broadly
than it is stated:** the right side of the twenty-four `iff` statements has the continuous
symmetries of the papers only (changes of basis, rescalings by nonzero factors, changes of basis
inside the heads). The permutations of hidden units or heads and the sign flips of tanh units,
which the paper's proof of the converse counts among the symmetries, are not in it. This makes the
right side a stronger condition; every equivalence stays true (they are proved), and each is
equivalent to the paper's proposition, but the direction "locally identifiable ⟹ equality
condition" is proved in Lean for the smaller family only. The file headers and the index say "the
symmetries are those of the papers". Details in Check 4. Everything else is the paper's statement
or a stronger one, with the gaps that the index already names.

---------------------------------------------------------------------------------------------------

## Part 1: the drift checks

### Check 1. Generic means almost every parameter, for every Haar measure

**Verdict: yes, in all 37 public `ae_` statements of the twelve files. For the learned skip the
measure is on the product of the weights and the skips.** (By
reading; the shape of all 55 by a script, `ae_shapes.py`, `ae_shapes.out`; the product space by
compiling.)

- The 37 public ones: 4 in `Dimension/IdentifiableConverseCob.lean`, 8 in
  `Dimension/IdentifiableIff.lean`, 12 in `Residual/IdentifiableIff.lean`, 4 in
  `Dimension/IdentifiableIffTransformer.lean`, 1 in `OneBlock/LearnedSkip.lean`, 8 in
  `OneBlock/LearnedSkipKinds.lean`. Each has `(μ : Measure (Params …)) [μ.IsAddHaarMeasure]` with
  `μ` a variable of the statement, and `∀ᵐ θ ∂μ`. None is "there is a parameter" or "on an open
  set". Of the 18 private helpers with `∀ᵐ`, 17 are for Haar measures in the same way (four of
  `OneBlock/LearnedSkipKinds.lean` give the Haar hypothesis a name), and one
  (`ae_eq_residual_add_lsk`) is a step of arithmetic that holds for any two measures.
- The 24 `iff` statements have `∀ᵐ θ ∂μ` on both sides, with the same `μ`. One of them:

  ```
  theorem ae_funDim_mlp_skipless_iff_ae_locally_cob (hσ : AnalyticOnNhd ℝ σ Set.univ)
      (μ : Measure (Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)) [μ.IsAddHaarMeasure]
      (hdIn : Fintype.card d ≤ Fintype.card dIn) (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
      (∀ᵐ θ ∂μ, funDim (Arch.mlp σ id hid) 0 θ + (L + 1) * Fintype.card d ^ 2
        = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)) ↔
      (∀ᵐ θ ∂μ, ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
        (∀ x : Matrix T dIn ℝ, eval (Arch.mlp σ id hid) 0 θ' x = eval (Arch.mlp σ id hid) 0 θ x) →
          ∃ G : Fin (L + 1) → GL d ℝ, θ' = θ.cob G G)
  ```
- The four statements of `IdentifiableConverseCob.lean` have an almost-everywhere hypothesis
  (`hloc : ∀ᵐ θ ∂μ, ∃ U ∈ 𝓝 θ, …`) and an almost-everywhere conclusion, for the same `μ`. This is
  meant: "if at generic parameters it is locally identifiable, then at generic parameters the
  lower bound". No other public statement has one.
- **The learned skip.** `ae_funDimSkips_ge` has `(μ : Measure (Params A dIn dOut × V))
  [μ.IsAddHaarMeasure]` with `[MeasurableSpace V] [BorelSpace V]`; the eight named statements have
  `(μ : Measure (Params (Arch.mlp … Real.tanh (rmsNorm ε) hid) dIn dOut × (Fin 1 → Matrix d d ℝ)))
  [μ.IsAddHaarMeasure]`: any additive Haar measure on the space of the pairs (weights, skip). By
  compiling (`Chk.lean`, check1): this product carries the Borel σ-algebra of its topology
  (`inferInstance`), and any two additive Haar measures on it have the same sets of measure zero.
  A Haar measure on it exists, so the statements are not empty (`Chk2.lean`).
- The four statements "… more than an identity skip" compare two networks with two parameter
  spaces, and have two measures: `∀ᵐ p ∂μ, ∀ᵐ θ' ∂ν, funDimLearned … p = funDim … 1 θ' + d (d + 1)
  / 2`, with `ν` any Haar measure on the weights of the residual network. This is the right form
  of "for generic parameters, its functional dimension exceeds that of the residual network".

### Check 2. `funDim` is the library's functional dimension; `funDimSkips`, `funDimLearned`

**Verdict: yes in every statement; `funDimSkips` is the same notion for the family whose
parameters are the weights and the skips; `funDimLearned` is the functional dimension of the
paper's network `x ↦ N_ε(x E A + f(N_ε(x E) W_read) W_write) D` with `A` a parameter.** (By
reading; the definitions by compiling.)

- Every statement of the first two groups uses `funDim A 0 θ` (skipless) or `funDim A 1 θ`
  (residual) of `Dimension/Functional.lean`: `sSup {r : ℕ | ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ),
  r = jacobianRank A S X θ}`. None uses the rank on one batch in its place.
- The Lean text of the new definitions (`OneBlock/LearnedSkip.lean`):

  ```
  def evalSkips (A : Arch T d L) (ι : V →L[ℝ] (Fin L → Matrix d d ℝ))
      (p : Params A dIn dOut × V) (x : Matrix T dIn ℝ) : Matrix T dOut ℝ := eval A (ι p.2) p.1 x
  noncomputable def jacobianRankSkips … (X : Fin n → Matrix T dIn ℝ) (p : Params A dIn dOut × V) : ℕ :=
    Module.finrank ℝ (LinearMap.range (fderiv ℝ
      (fun p' : Params A dIn dOut × V => fun i : Fin n => evalSkips A ι p' (X i)) p).toLinearMap)
  noncomputable def funDimSkips … (p : Params A dIn dOut × V) : ℕ :=
    sSup {r : ℕ | ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), r = jacobianRankSkips A ι X p}
  noncomputable abbrev funDimLearned (A : Arch T d L) (p : Params A dIn dOut × (Fin L → Matrix d d ℝ)) : ℕ :=
    funDimSkips A (ContinuousLinearMap.id ℝ (Fin L → Matrix d d ℝ)) p
  ```
  The derivative is taken in the pair `(θ, v)`, the rank is that of the Jacobian on a batch, and
  the supremum is over all `n` and all batches: the shape of `funDim`, word for word, with the
  skips among the parameters. `flatSkips` is the space `K(θ)` of S Appendix B for this family.
- By compiling (`Chk.lean`, check2): `funDimLearned A p` is, by `rfl`, the supremum over all
  finite batches of the rank of the derivative of `(θ, S) ↦ (eval A S θ (X i))_i`; and for one
  block `evalSkips A id (θ, S) x = A.χ (x * θ.E * S 0 + A.f 0 (A.χ (x * θ.E) * θ.read 0) * θ.write
  0) * θ.D`, by `rfl`. With `A.χ = rmsNorm ε` this is the paper's formula; the skip reads `x E`
  itself and the block reads `N_ε(x E)`, as in S Setup ("the blocks and the readout read `N_ε(h)`,
  and the skips read `h` itself").
- The eight named statements are for `rmsNorm ε` with `ε > 0` and tanh, GELU, SiLU-gated and
  GELU-gated blocks, where the network is differentiable in `(θ, A)` at every input. So nothing
  drops out of the supremum, and `funDimLearned` is the paper's `fd` there.
- The number of parameters is written `Module.finrank ℝ (Params …) + Fintype.card d ^ 2`: the
  weights (`P`) and the `d²` entries of `A`.

### Check 3. No extra hypotheses in main-text statements

**Verdict: none. The Lean statements have the hypotheses of the paper's statement, Setup or
Scope, or fewer.** (By reading; three instances by compiling.)

**A count first.** The brief speaks of twenty-eight `iff` statements. There are twenty-four
(8 + 12 + 4). The four others of `Dimension/IdentifiableIffTransformer.lean`
(`exists_cob_heads_of_eval_eq_skipless_attentionMlp`, `…_attentionGated`, each with `_rmsNorm`) are
statements at one parameter, in one direction.

**Proposition 4.6 (D) / 4.5 (S).** D: "Let the blocks be tanh, GELU, SwiGLU, GeGLU or attention
blocks, without normalization or under pre-RMSNorm." S: "Let the blocks be analytic, with or
without pre-RMSNorm, within the scope of Section 2."

| Lean hypothesis | In which statements | In the paper? |
|---|---|---|
| `[μ.IsAddHaarMeasure]` | all 24 | "at generic parameters" |
| `hA : A.χ = id`, or `hε : 0 < ε` with `hA : A.χ = rmsNorm ε` (in the named forms the architecture has `id` or `rmsNorm ε`) | all | "without normalization or under pre-RMSNorm"; S Setup and D "case (+)": `ε > 0` |
| `hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ` (general forms), `hσ : AnalyticOnNhd ℝ σ Set.univ` (MLP, gated, transformers) | all but the attention forms | S: "Let the blocks be analytic"; D: the four kinds, all analytic |
| `hdIn : Fintype.card d ≤ Fintype.card dIn` | all 24 | Scope: `d_in ≥ d_model` |
| `hw : ∀ ℓ, card d ≤ card (A.w ℓ)`, `hhid : ∀ ℓ, card d ≤ card (hid ℓ)` | the 6 skipless general, MLP and gated forms | Scope: "Every MLP block has `d_hidden ≥ d_model`" |
| `hdh : ∀ ℓ, card (dh ℓ) ≤ card d` | attention and transformers, skipless and residual (12) | Scope: "total width `H d_h = d_model`" gives it |
| `hH : ∀ ℓ, card d ≤ card (H ℓ) * card (dh ℓ)` | skipless attention (2) | the same sentence of the Scope |
| `hW : ∀ ℓ, card d ≤ card (H ℓ) * card (dh ℓ) + card (hid ℓ)` | skipless transformers (4) | Scope: every attention block has width `d`, every MLP block at least `d` |
| `[Nonempty d]` | the gated forms (8) | Scope: `d_model ≥ 2`. It is needed: with `d` empty and a hidden unit, the left side is false and the right side true |
| residual forms: `hdIn` only, with `hdh` for heads and `[Nonempty d]` for gated units | 12 | no width is asked; the paper's Scope has it |

The four statements at one parameter have, in place of the Scope, conditions on `θ`: `hE : θ.E.rank
= card d`, `hw : ∀ ℓ, (θ.write ℓ).rank = card d`, `hQ`, `hV` (the query and the value matrix of
every head of rank `d_h`), for gated units `hv` (no value column is `0`), and `hfd` (the equality
at `θ`). These are the conditions of the paper's proof ("Take `θ` at which the rank on `X` is `r`
and the symmetries act locally freely"), and they hold at generic parameters within the Scope.

**Not asked by Lean, and in the Scope: `d_out ≥ d`, `d ≥ 2`, at least one token (two for
attention), the same number of heads in all blocks, `H d_h = d` exactly.** The brief asks whether
that is right. It is: the equivalences are proved without them, so they cannot be false there. By
compiling (`Chk.lean`, check3): `ae_funDim_mlp_skipless_iff_ae_locally_cob` instantiates with no
token (`T = Fin 0`), `d = 2`, `d_out = 1`; `ae_funDim_mlp_residual_iff_ae_locally_cob_rmsNorm`
with `d = 1`, `d_out = 0`. By hand, why: both directions use only that `E` has rank `d` and, for
skipless networks, that the writes have rank `d` (the locally free action and the upper bound of S
Lemma A.18, "If the embedding has rank `d_model` and every block has width at least `d_model`").
Where `d_out < d` or there is no token, the bound is in general not attained, and then both sides
are false together.

**Theorem 3.3 (ii) (S), `Symmetry/CobGroup.lean`.** Paper: "With or without pre-RMSNorm, let
`G_0, …, G_L` be invertible […] (ii) The changes of basis that preserve the function at all
parameters form a group of dimension `(L + 1) dim 𝒢` in a skipless network and `dim 𝒢` in a
residual one".

| Statement | Hypotheses | Where they come from |
|---|---|---|
| `exists_subgroup_eq_cobPreserving` | none (any network, any stream matrices) | |
| `cobPreserving_skipless`, `dimH_cobPreservingMat_skipless` | `hA : A.χ = id` | no normalization; any blocks, also no token |
| `dimH_cobPreservingMat_skipless_rmsNorm` | `hA : A.χ = rmsNorm ε`, `hOnly : ∀ G ∈ cobPreserving A 0 dIn dOut, ∀ ℓ, (G ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ` | `hOnly` is the conclusion of Lemma A.4. No `ε > 0` here: `hOnly` carries it |
| `…_skipless_rmsNorm_mlp` | `[Nonempty T] [Nonempty dIn] [Nonempty dOut]`, `hε : 0 < ε`, `hσc : Continuous σ`, `hne : ¬ ∀ z, σ (-z) = σ z`, `hnc : ¬ ∀ z, σ z = σ 0`, `hhid : ∀ ℓ, Nonempty (hid ℓ)` | Lemma A.4: "`ε > 0`"; its proof, fact (b): "None of tanh, GELU, ReLU and ReLU² is even or constant"; a block has a hidden unit |
| `…_skipless_rmsNorm_gated` | the same, with `hσ0 : ∃ z, σ z ≠ 0`, `hκ : ∀ κ : ℝ, (∀ z, σ z = κ * σ (κ * z)) → κ = 1` | fact (b) for a gated block: "`σ(z) = κ σ(κz)` for all `z` […] `κ = 1`" |
| `…_skipless_rmsNorm_attention` | `hsees : ∀ t, ∃ s, sees t s`, `hH : ∀ ℓ, Nonempty (H ℓ)`, `hdh : ∀ ℓ, Nonempty (dh ℓ)`, the three `Nonempty`, `hε` | not written in the paper; every mask of the paper has them (Part 2, note on the masks) |
| `…_attentionMlp`, `…_attentionGated` | the activation or gate conditions, `hsees`, `hblk : ∀ ℓ, (Nonempty (H ℓ) ∧ Nonempty (dh ℓ)) ∨ Nonempty (hid ℓ)` | the same |
| `dimH_cobPreservingMat_residual` | `[Nonempty T] [Nonempty dIn] [Nonempty dOut]`, `hA : A.χ = id`, `hne : ∀ ℓ, ∃ (x : Matrix T dIn ℝ) (E : Matrix dIn d ℝ) (W : Matrix d (A.r ℓ) ℝ), A.f ℓ (x * E * W) ≠ 0` | Theorem A.5 (iii): "let every block be nonzero for some value of its parameters" |
| `dimH_cobPreservingMat_residual_rmsNorm` | the same with `hε : 0 < ε`, `hA : A.χ = rmsNorm ε`, and `A.f ℓ (rmsNorm ε (x * E) * W) ≠ 0` | Theorem A.5 (iii): "with pre-RMSNorm and `ε > 0`" |

Theorem A.5 (iii) also has "Let `d_model ≥ 2`". The two residual statements do not: Lean is
stronger there. Every hypothesis of the table holds for the blocks and masks of the paper within
its Scope. By compiling (`Chk.lean` check5, `Chk2.lean`): the hypotheses hold for tanh blocks
(`tanh_not_even_not_const`), for SiLU gates (`silu_gate_scale`), and `hne` for a tanh block; the
values come out as `9`, `9` (skipless, `d = 3`, `L = 2`) and `9` (residual, no normalization,
`d = 3`).

**Theorem 4.6 (ii), the learned skip.** The eight named statements have `[Nonempty T]`, `hε : 0 <
ε`, `hd : 2 ≤ card d`, `hdIn`, `hdOut`, `hhid : ∀ ℓ, card d ≤ card (hid ℓ)` and the Haar measures.
All are in the Scope ("`d_in, d_out ≥ d_model ≥ 2`", "`d_hidden ≥ d_model`") or the Setup
(`ε > 0`); a token is implicit. Theorem B.1 (iii) itself has no hypothesis on the width, so
against the appendix statement `hhid` is one hypothesis more (Check 6 (c)).

### Check 4. Is each `iff` the paper's proposition?

**Verdict: the left side is Definition 4.4 (D) / 4.3 (S) exactly. The right side is Definition 4.5
(D) / 4.4 (S) for the continuous symmetries only. Each `iff` is true and is equivalent to the
paper's proposition, but its direction "⟸" is proved for a smaller family than the paper's
definition names.** (By reading; the last sentence of the brief's question by compiling.)

- **Left side.** "A network satisfies the equality condition if the bound of Theorem 4.3 is
  attained at generic parameters". Lean: `∀ᵐ θ ∂μ, funDim A 0 θ + ((L + 1) * dim 𝒢 + s) =
  Module.finrank ℝ (Params …)`, with `dim 𝒢 = card d ^ 2` or `card d * (card d - 1) / 2`, and
  `s = 0`, `∑ ℓ, card (hid ℓ)`, `2 * ∑ ℓ, card (H ℓ) * card (dh ℓ) ^ 2`, or the sum of the last
  two; for residual networks `funDim A 1 θ + (dim 𝒢 + s)`. `d (d − 1)` is even, so the division is
  exact. Same as the paper.
- **Right side.** "locally identifiable at `θ` if this holds for every `θ′` in some neighborhood
  of `θ`". Lean: `∀ᵐ θ ∂μ, ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U, (∀ x : Matrix T dIn ℝ, eval … θ' x = eval … θ x) →
  ∃ (symmetry), θ' = (image of θ)`. The symmetry is not asked to be close to the identity, as in
  the definition.
- **The family of symmetries.** It is the Lie group of the first half of the paper's proof ("The
  changes of basis of Proposition 3.2, the rescalings and the changes of basis inside the heads
  form a Lie group of dimension `k`"), all of its components:
  - changes of basis: `G : Fin (L + 1) → GL d ℝ` with `θ' = θ.cob G G` for skipless networks; one
    `G : GL d ℝ` with `θ.cob (fun _ => G) (fun _ => G)` for residual ones; under pre-RMSNorm with
    `(G ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ` (any orthogonal matrix, also of
    determinant `−1`);
  - rescalings: `c : ∀ ℓ, hid ℓ → ℝ` with `∀ ℓ i, c ℓ i ≠ 0`, and `θ.rescale c` (value column
    times `c⁻¹`, write row times `c`): D Appendix B, "`(e_i, a_i) ↦ (e_i/λ, λ a_i)`, `λ ≠ 0`";
  - head changes: `K K' : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ` with `(θ.headsQK K).headsVO K'`: D Appendix B,
    "`(W_{Q,i}, W_{K,i}) ↦ (W_{Q,i} K, W_{K,i} K^{−⊤})`, `K ∈ GL(d_h)`", and the same for values
    and outputs.
- **What is missing: the permutations of hidden units or heads and the sign flips of tanh hidden
  units.** D Appendix B and S Appendix A.6 list them under "The symmetries inside the blocks"
  ("finite and remove no parameters"), and the proof of the converse uses them: "With the
  permutations and the sign flips, the symmetries form a Lie group of dimension `k` with finitely
  many components". So they are symmetries in the sense of Definition 4.5 / 4.4.
  - Leaving them out makes the right side a **stronger** condition: fewer images are allowed.
  - "equality condition ⟹ locally identifiable": Lean gives the smaller family, which is more
    than the definition asks (and less than the paper's last sentence, "Every symmetry that is
    needed is then close to the identity", which is in the older files
    `Dimension/LocalIdentifiability….lean`, `Residual/LocalIdentifiability….lean` and in the four
    statements at one parameter of `IdentifiableIffTransformer.lean`).
  - "locally identifiable ⟹ equality condition": Lean assumes the smaller family, so this
    direction is **weaker** than the paper's. The paper's direction for the full family is not a
    consequence of the `iff` statements alone. It follows from the general statement
    `ae_finrank_le_funDim_add_of_ae_locally_mem_iUnion_image` (countably many maps: one for each
    permutation and sign pattern), which is not instantiated for it; or from the remark that at
    generic `θ` no image of `θ` under a nontrivial permutation or sign flip lies near `θ` (S proof
    of Lemma A.18: "Permutations and sign flips are isolated"), so that after shrinking `U` the
    two right sides say the same. Neither step is a Lean statement.
  - **The equivalence itself is not made false:** the smaller right side still follows from the
    left side (symmetries near the identity suffice) and still implies it. All 24 are proved.
- **The general forms** (`ae_funDim_skipless_iff_ae_locally_cob`, `ae_funDim_residual_iff_…`, with
  `_rmsNorm`) are for any real-analytic blocks with the changes of basis alone. For blocks with
  `s > 0` they are true (both sides are false) and are not the paper's proposition, whose `k`
  contains `s`. The headers say "(`s = 0`)".
- **Residual networks of tanh, GELU, SwiGLU, GeGLU and attention blocks: both sides are theorems
  of the library.** The left sides are `ae_funDim_tanh_residual`, `ae_funDim_gelu_residual`,
  `ae_funDim_swiglu_residual`, `ae_funDim_geglu_residual`, `ae_funDim_attention_residual`, their
  `_rmsNorm` forms, and for transformers `ae_funDim_attention_tanh_residual` and its siblings (S
  Theorem 4.7). The right sides, with the symmetries near the identity, are
  `ae_exists_cob_of_eval_eq_tanh_residual`, `ae_exists_cob_rescale_of_eval_eq_swiglu_residual`,
  `ae_exists_cob_heads_of_eval_eq_attention_residual` and their siblings (S Corollary 4.9). They
  hold under the hypotheses of Theorem 4.7 (`d_in, d_out ≥ d ≥ 2`, a token; for attention two
  tokens and `d_h ≥ 1`), which the `iff` statements do not need. By compiling (`Chk.lean`,
  check4): for tanh blocks without normalization and under pre-RMSNorm, for SwiGLU blocks and for
  attention blocks, the right side of the `iff` follows from the `iff` and Theorem 4.7 in one
  line.

### Check 5. "A group of dimension"

**Verdict: `cobPreserving` is the paper's set, `exists_subgroup_eq_cobPreserving` is "form a
group", and the Hausdorff dimension is a faithful reading of "of dimension" for these sets. The
four values are right.** (By reading; the values by hand and by compiling.)

- The Lean text: `def cobPreserving (A : Arch T d L) (S : Fin L → Matrix d d ℝ) (dIn dOut : Type*)
  … : Set (Fin (L + 1) → GL d ℝ) := {G | ∀ (θ : Params A dIn dOut) (x : Matrix T dIn ℝ), eval A S
  (θ.cob G G) x = eval A S θ x}`. `θ.cob G G` is `E G_0`, `G_{ℓ−1}⁻¹ W_read^ℓ`, `W_write^ℓ G_ℓ`,
  `G_L⁻¹ D`, the map of S Theorem 3.3 (i) and of Lemma A.4 ("Multiply the writes into every hidden
  state `h_ℓ` by `G_ℓ` on the right and its reads by `G_ℓ⁻¹` on the left"). "For all `θ` and `x`"
  is "preserve the function at all parameters". `S = 0` is the skipless network, `S = 1` the
  residual one (the identity skips stay in place).
- `cobPreservingMat` is the image of this set in `Fin (L + 1) → Matrix d d ℝ`, the same set written
  as families of matrices (the map is injective). It is there because the dimension needs a
  metric, and the families of matrices have one.
- `exists_subgroup_eq_cobPreserving (A) (S) : ∃ K : Subgroup (Fin (L + 1) → GL d ℝ), (K : Set _) =
  cobPreserving A S dIn dOut`: a subgroup of the families of invertible matrices under the
  product entry by entry. This is "form a group", for any network.
- **The dimension** is `dimH` of the set of families of matrices, for the metric of the entrywise
  norm (all norms give the same value). The paper means the dimension of a Lie group. For a
  nonempty smooth submanifold of a real vector space the two agree, and the four sets are such:
  all families of invertible matrices (an open set), of orthogonal matrices (`O(d)^{L+1}`), and
  the families with all entries equal to one invertible or one orthogonal matrix. Which set it is
  in each case is in other statements (`cobPreserving_skipless`, `eval_cob_skipless_rmsNorm_iff_…`,
  `eval_cob_residual_iff`, `eval_cob_residual_rmsNorm_iff`). A statement of `dimH` alone does not
  say that a set is a manifold; with these it is a faithful reading. The header of
  `Generic/GroupDimension.lean` says why this notion was taken.
- **The four values, by hand.**

  | Set | `n = 0` | `d = 0` | `d = 1` | `d = 2` | Lean |
  |---|---|---|---|---|---|
  | `n` invertible matrices | one point: 0 | one point: 0 | `(ℝ∖{0})^n`: `n` | open in `ℝ^{4n}`: `4n` | `n * card d ^ 2` |
  | `n` orthogonal matrices | 0 | 0 | `{±1}^n`, finite: 0 | `O(2)^n`, each factor two circles: `n` | `n * (card d * (card d - 1) / 2)` |
  | all equal to one invertible matrix, `n ≥ 1` | excluded | 0 | a line without a point: 1 | 4 | `card d ^ 2` |
  | all equal to one orthogonal matrix, `n ≥ 1` | excluded | 0 | two points: 0 | two circles: 1 | `card d * (card d - 1) / 2` |

  All agree (the subtraction and the division of natural numbers give `0` at `d = 0` and `d = 1`).
  By compiling (`Chk.lean`, check5): the Lean statements give `0`, `0`, `3`, `12` (first row,
  `n = 3` or `n = 0`), `0`, `3`, `9` (second row, `d = 1, 2, 3`), `4` and `1` (third and fourth
  row, `d = 2`). The hypothesis `0 < n` of the last two is needed: for `n = 0` the set is one
  point and has dimension `0`, not `d²` (compiled). In `CobGroup.lean` `n = L + 1 ≥ 1`.
- Under pre-RMSNorm with `d = 1` the group is finite and the statements give `0`. The paper has
  `d ≥ 2`.

### Check 6. The learned skip

**(a) The count, by hand.** With a full learned skip the network has `P + d²` parameters. Its
symmetries: an orthogonal change of basis at `h_0` and one at `h_1`, with `A ↦ G_0⁻¹ A G_1`, of
dimension `2 · d(d−1)/2 = d(d−1)`, and the `s` dimensions inside the block. So `fd = P + d² −
d(d−1) − s = P + d − s`. The residual network has `P − d(d−1)/2 − s` (S Theorem B.1 (ii)). The
difference is `d² − d(d−1) + d(d−1)/2 = d² − d(d−1)/2 = d(d+1)/2`. This is the paper's "exceeds
that of the residual network of part (ii) by exactly `d_model (d_model + 1)/2`", and its Step 5
("`K(θ)` is larger than for the residual network by `d_model (d_model − 1)/2` […] while the
network has `d²_model` […] more parameters"). Lean: `funDimLearned … p + Fintype.card d *
(Fintype.card d - 1) = Module.finrank ℝ (Params …) + Fintype.card d ^ 2` (tanh, GELU), with `+ ∑ ℓ,
Fintype.card (hid ℓ)` on the left for SwiGLU and GeGLU, and `funDimLearned … p = funDim … 1 θ' +
Fintype.card d * (Fintype.card d + 1) / 2`. **The same numbers.** For the upper triangular skip
the paper's count is `P + d(d+1)/2 − d(d−1)/2 − s`, the same value `P + d − s`.

**(b) The two general steps: I could not refute them, and I believe both by hand.** At `4e16789`
both are proved.

- `funDim_add_finrank_le_funDimSkips_zero`: `[Nonempty T] … (hε : 0 < ε) (hA : A.χ = rmsNorm ε) (hf
  : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (ι : V →L[ℝ] (Fin 1 → Matrix d d ℝ)) (hι :
  Function.Injective ι) (θ) (hE : θ.E.rank = Fintype.card d) (hD : θ.D.rank = Fintype.card d) :
  funDim A 0 θ + Module.finrank ℝ V ≤ funDimSkips A ι (θ, 0)`. By hand: at the skip `0` a flat
  direction `(η, a)` has `a = 0`. On the inputs `t x`, as `t → ∞`, the input `N_ε(t x E)` of the
  block converges, so the hidden state and its derivative along `η` stay bounded, while the
  derivative along `a` is `t` times `DN_ε(g)(x E (ι a)) D`. Hence `DN_ε(g_∞)(x E (ι a)) D = 0`;
  `D` has rank `d`, `DN_ε` is injective at every point for `ε > 0`, `x E` runs over a dense set
  of matrices, and `ι` is injective. So the flat directions are those of the skipless network,
  and the two sides are equal. The argument needs a token, which the statement has.
- `funDimLearned_add_le_rmsNorm`: `(hε : 0 < ε) (hA : A.χ = rmsNorm ε) (hf : ∀ ℓ, Differentiable ℝ
  (A.f ℓ)) (p) (hE : p.1.E.rank = Fintype.card d) (hD : p.1.D.rank = Fintype.card d) (U : Submodule
  ℝ (Params A dIn dOut)) (hU : U ≤ Submodule.span ℝ {η | InsideBlocks A p.1 η}) : funDimLearned A
  p + (Fintype.card d * (Fintype.card d - 1) + Module.finrank ℝ U) ≤ Module.finrank ℝ (Params A dIn
  dOut) + Fintype.card d ^ 2`. By hand: the directions of the two rotations (`E X_0`, `A X_1 −
  X_0 A`, `−X_0 W_read`, `W_write X_1`, `−X_1 D`, with `X_0`, `X_1` antisymmetric) are flat at
  every skip `A`, invertible or not. They are independent of each other and of `U`, because a
  direction of `U` has the entries `0` at `E` and at `D` (`InsideBlocks.E_eq_zero`), and `E X_0 =
  0`, `X_1 D = 0` give `X_0 = X_1 = 0`. The directions of `U` are flat for every stream
  (`InsideBlocks.mem_flat`). With `fd + dim K = P + d²` this is the bound.
- By a computation (`learned_skip_refute.out`; one token, `ε = 0.3`, 50 digits; the smallest
  singular value that is kept is at least `10⁻¹⁴` times the largest, the first that is dropped is
  below `10⁻⁵⁰` times it):
  - **At the skip `0`, 18 cases, no violation; equality in all of them.** tanh, GELU, SwiGLU and
    GeGLU blocks; `d = 1, 2, 3`; blocks narrower than `d` (five cases); `d_out = d` (most) and
    `d_out > d`; `d_in = d` and `d_in > d`; skips: all matrices, upper triangular, diagonal, a
    random family of dimension 2; three degenerate weights (`W_write = 0`, `W_read = 0`).
    Examples: tanh, `d = d_in = d_out = 2`, 2 hidden units: `14 + 4 = 18`; tanh, `d = 3`, 2 hidden
    units, all matrices: `21 + 9 = 30`; SwiGLU, `d = 2`, 1 hidden unit, upper triangular: `9 + 3 =
    12`; tanh with `W_write = 0`: `4 + 4 = 8`.
  - **The upper bound, 14 cases, no violation.** At a random skip, at `A = 0`, at `A = I` and at
    a singular `A`; blocks narrower than `d`; `U` the rescalings of a gated block (`dim U =
    d_hidden`); two degenerate weights where `U` is larger (`W_write = 0`: every direction of the
    read, `11 + 2 + 4 ≤ 20`; one write row `0`: `16 + 2 + 2 = 20`). Equality in 13 of 14.
  - **The values of the eight named statements, 9 cases, all agree:** `fd = P + d² − d(d−1) − s`
    and `fd − fd_residual = d(d+1)/2` (`3` for `d = 2`, `6` for `d = 3`), for tanh, GELU, SwiGLU
    and GeGLU blocks of width at least `d`.
  - These computations support the statements and prove nothing. I did not compute attention
    blocks or several tokens.

**(c) What the eight named statements do not cover of Theorem B.1 (iii), and the index row.**

| Clause of Theorem B.1 (iii) | Covered by the eight? |
|---|---|
| "a learned skip `A`, full or upper triangular" | the full skip only. The upper triangular skip is stated since `c55748b` in `OneBlock/LearnedSkipTriangular.lean` (`sorry` there; not in my brief, not compared) |
| the kinds of block of the theorem (tanh, GELU, ReLU, ReLU², ReGLU, SwiGLU, GeGLU, attention) | four of eight: tanh, GELU, SwiGLU, GeGLU. Not ReLU, ReLU², ReGLU, attention. The same four of the eight kinds of Theorem 4.6 (ii) |
| no hypothesis on the width | width at least `d` only (`hhid`). The main text has this in its Scope; the appendix statement does not |
| "For generic parameters and `ε > 0`, its functional dimension exceeds that of the residual network of part (ii) by exactly `d(d+1)/2`" | yes, the four `…_eq_residual_add` |
| "and it satisfies the equality condition" | yes in content: the four value statements say `fd = (P + d²) − d(d−1) − s`, the number of parameters minus the dimension of the symmetries. Lean has no definition of "the symmetries of the network with a learned skip", so this reading rests on the count of (a) |
| "For `ε = 0` it exceeds that of the residual network with `ε = 0` by at most `d(d+1)/2 − 1`, with equality for ReLU, ReLU² and ReGLU blocks" | no |

The index row (line 775) is honest: it names the four kinds, "of width at least `d`", "`ε > 0`,
full skip", points to the row of the triangular skip, and lists as not stated "ReLU, ReLU², ReGLU
and attention blocks […]; blocks narrower than `d`; `ε = 0`". It does not say that the value
statement is the paper's "and it satisfies the equality condition"; the file header does. One
remark from the computation: for a block narrower than `d` the value `P + d² − d(d−1) − s` still
holds at a generic skip (tanh, `d = 3`, 2 hidden units: 33; `d = 2`, 1 hidden unit: 16; SwiGLU,
`d = 2`, 1 hidden unit: 15), while at the skip `0` the family has less (30 in the first case). So
the route through the skip `0` cannot give the narrow blocks; the index says that they are not
stated.

---------------------------------------------------------------------------------------------------

## Part 2: the statements, file by file

Verdicts: SAME, LEAN STRONGER, LEAN WEAKER, DIFFERENT, PART, FALSE. "Proved" means: no `sorry` at
`4e16789`, and the three standard axioms only (`Ax.out`). All 71 theorems are proved in this
sense. None is FALSE.

### `Generic/Cayley.lean` (4 theorems)

Paper: S proof of Proposition 4.5 and D proof of Proposition 4.6, "the images of `θ` under it form
the image of a manifold of dimension `k` under a smooth map", for the orthogonal group. The step
is not written out in the papers.

| Statement | Verdict |
|---|---|
| `isUnit_det_one_add_of_mem_antisymmetric`: `A ∈ antisymmetric d → IsUnit (1 + A).det` | PART (proof piece); true |
| `cayley_mem_orthogonalGroup`: `(1 - A) * (1 + A)⁻¹ ∈ Matrix.orthogonalGroup d ℝ` | PART; true |
| `exists_det_one_add_mul_diagonal_ne_zero (Q) : ∃ s : d → Bool, (1 + Q * Matrix.diagonal fun i => if s i then (1 : ℝ) else -1).det ≠ 0` | PART; true, for every real square `Q` |
| `exists_cayley_mul_diagonal_of_mem_orthogonalGroup`: `Q = (1 - A) * (1 + A)⁻¹ * Matrix.diagonal …` with `A` antisymmetric | PART; true |

By hand for `d = 1`: `A = 0`, `1 + A = 1`, the Cayley transform is `1`; `1 + q s ≠ 0` for `s = 1`
or `s = −1`; `Q = ±1 = 1 · (±1)`. For `d = 2`: `A = [[0, a], [−a, 0]]`, `det(1 + A) = 1 + a² > 0`;
`(1 − A)(1 + A)⁻¹ = (1 + a²)⁻¹ [[1 − a², −2a], [2a, 1 − a²]]`, a rotation; `det(1 + Q D)` is affine
in each sign and its mean over the four sign patterns is `det 1 = 1`, so one pattern gives a
nonzero value (the same argument for every `d`); for an orthogonal `Q` take such a `D`, then `Q D`
has no eigenvalue `−1` and `A = (1 − Q D)(1 + Q D)⁻¹` is antisymmetric. I checked `Q = −I`
(`D = −I`, `A = 0`), the reflection `diag(1, −1)` (`D = diag(1, −1)`, `A = 0`) and the rotation by
a quarter turn (`D = I`, `a = 1`). `antisymmetric d` is `{X | Xᵀ = -X}`
(`Dimension/UpperBoundRMSNorm.lean`).

### `Dimension/IdentifiableConverseCob.lean` (4 theorems)

Paper: D Proposition 4.6 and S Proposition 4.5, the direction from local identifiability to the
equality condition.

| Statement | Changes of basis in `hloc` | Conclusion `∀ᵐ θ ∂μ, finrank ℝ (Params A dIn dOut) ≤ funDim A S θ + …` | Verdict |
|---|---|---|---|
| `ae_finrank_le_funDim_add_of_ae_locally_cob` | `G : Fin (L + 1) → GL d ℝ`, `θ' = (Ψ θ n).cob G G` | `(L + 1) * card d ^ 2 + finrank ℝ N` | LEAN STRONGER as a general form; PART of the proposition |
| `…_cob_const` | one `G : GL d ℝ` at all hidden states | `card d ^ 2 + finrank ℝ N` | the same |
| `…_cob_orthogonal` | `Q : Fin (L + 1) → GL d ℝ`, all orthogonal | `(L + 1) * (card d * (card d - 1) / 2) + finrank ℝ N` | the same |
| `…_cob_const_orthogonal` | one orthogonal `Q` | `card d * (card d - 1) / 2 + finrank ℝ N` | the same |

- The four counts are the paper's `(L + 1) dim 𝒢` and `dim 𝒢`, each plus `dim N` in the place of
  `s` (by reading).
- The statements do not ask that the images are symmetries, or that they have the same function:
  `Ψ : Params A dIn dOut → N → Params A dIn dOut` is any family with `hΨ : ∀ θ, ContDiffOn ℝ 1 (Ψ
  θ) Ω`, and `S` is any family of stream matrices. So they are lower bounds for the functional
  dimension for any such family, as the header and the index say.
- PART: one direction, the lower bound only; the family of the paper is put in by the `iff` files.
- By hand: they follow from the general statement of `Dimension/IdentifiableConverse.lean` with
  the space `(Fin (L + 1) → Matrix d d ℝ) × N` and the open set of invertible families, on which
  `G ↦ G⁻¹` is smooth; for orthogonal matrices with finitely many maps from the antisymmetric
  matrices (dimension `d(d−1)/2`), which is what `Generic/Cayley.lean` gives.

### `Dimension/IdentifiableIff.lean` (8), `Residual/IdentifiableIff.lean` (12), `Dimension/IdentifiableIffTransformer.lean` (8)

Paper: D Proposition 4.6 with Definitions 4.4, 4.5; S Proposition 4.5 with Definitions 4.3, 4.4.

| Statements | Network | Verdict |
|---|---|---|
| `ae_funDim_skipless_iff_ae_locally_cob`, `…_rmsNorm` | skipless, any real-analytic blocks, changes of basis alone | SAME for blocks with `s = 0`, up to the finite symmetries (note 1); true and not the paper's for `s > 0` |
| `ae_funDim_mlp_skipless_iff_ae_locally_cob`, `…_rmsNorm` | skipless MLP blocks, real-analytic activation (tanh, GELU) | SAME up to the finite symmetries: "⟹" LEAN STRONGER, "⟸" LEAN WEAKER (note 1); fewer hypotheses than the Scope |
| `ae_funDim_gated_skipless_iff_ae_locally_cob_rescale`, `…_rmsNorm` | skipless gated blocks (SwiGLU, GeGLU) | the same |
| `ae_funDim_attention_skipless_iff_ae_locally_cob_heads`, `…_rmsNorm` | skipless attention blocks | the same |
| `ae_funDim_residual_iff_ae_locally_cob`, `ae_funDim_mlp_residual_iff_ae_locally_cob`, `ae_funDim_gated_residual_iff_ae_locally_cob_rescale`, `ae_funDim_attention_residual_iff_ae_locally_cob_heads`, `ae_funDim_attentionMlp_residual_iff_ae_locally_cob_heads`, `ae_funDim_attentionGated_residual_iff_ae_locally_cob_heads_rescale`, each with `_rmsNorm` | residual networks (S only) | the same; for tanh, GELU, SwiGLU, GeGLU and attention blocks both sides are theorems |
| `ae_funDim_attentionMlp_skipless_iff_ae_locally_cob_heads`, `ae_funDim_attentionGated_skipless_iff_ae_locally_cob_heads_rescale`, each with `_rmsNorm` | skipless networks of attention blocks and MLP or gated blocks (S only) | the same |
| `exists_cob_heads_of_eval_eq_skipless_attentionMlp`, `…_attentionGated`, each with `_rmsNorm` | the same networks, at one parameter | LEAN STRONGER for the direction "⟹" with "Every symmetry that is needed is then close to the identity": at every `θ` with the conditions of the proof (note 2) |

Notes.

1. The right side has the continuous symmetries only (Check 4). The last sentence of the
   proposition is not in the `iff` statements; it is in the statements of local identifiability.
2. The four statements at one parameter conclude `∀ V ∈ 𝓝 (1 : Fin (L + 1) → Matrix d d ℝ), ∀ W ∈ 𝓝
   (1 : ∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ), ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U, (same function) → ∃ G K K', (G
   ∈ V) ∧ (K ∈ W) ∧ (K' ∈ W) ∧ θ' = …`, and for gated units `c ∈ Wc ∧ (∀ ℓ i, 0 < c ℓ i)`: the
   symmetries can be taken in any neighbourhoods of the identity. They are the twins of
   `Residual/LocalIdentifiabilityTransformer.lean`, with `G_0, …, G_L` in place of one `G` and
   with `hw` (the writes of rank `d`) added, as the skipless case needs. The file has no
   statement that the conditions hold at almost every parameter; the `iff` statements of the same
   file use it inside their proofs.
3. D Proposition 4.6 is for networks whose blocks are all of one kind (D Scope), so the files for
   transformers and for residual networks formalize S Proposition 4.5 only. The docstrings say
   so.
4. Networks of D Proposition 4.6 that have no statement by name: none. tanh and GELU are the
   statements for MLP blocks with `analyticOnNhd_tanh`, `analyticOnNhd_gelu` (compiled for tanh).

### `Symmetry/OnlyOrthogonalRows.lean` (7 theorems)

Paper: S Lemma A.4 and its proof; S Theorem 3.3 (ii), skipless, under pre-RMSNorm.

| Statement | Verdict |
|---|---|
| `orthogonal_of_eval_cob_skipless_rmsNorm_of_rows` | LEAN STRONGER as a general form of the paper's proof: any blocks with `hrows`, `hsep`, `hnz` |
| `orthogonal_of_eval_cob_skipless_rmsNorm_attention` | SAME as Lemma A.4 for attention blocks; `hsees`, `hH`, `hdh` are written out (the paper has them implicitly); no `d ≥ 2`, no second token |
| `orthogonal_of_eval_cob_skipless_rmsNorm_attentionMlp`, `…_attentionGated` | SAME as Lemma A.4 for networks of two kinds of block; Lean's blocks may have heads and hidden units side by side |
| `eval_cob_skipless_rmsNorm_iff_attention`, `…_attentionMlp`, `…_attentionGated` | PART of Theorem 3.3 (ii): which changes of basis pass (exactly the orthogonal ones). The dimension is in `Symmetry/CobGroup.lean` |

- **The general statement against the paper's proof** (by reading).
  - "Take inputs whose tokens are all equal. Then the tokens of every hidden state are equal":
    `hrows : ∀ k (a : d → ℝ) (W : Matrix d (A.r k) ℝ), ∃ b : A.w k → ℝ, A.f k ((Matrix.of fun _ : T
    => a) * W) = Matrix.of fun _ : T => b`.
  - Fact (a), scaling: no hypothesis; it is inside the proof and uses `hε : 0 < ε`.
  - Fact (b), "If rows `a` and `a′` satisfy `B(a) = B(a′)` for all parameters of a block `B`, then
    `a = a′`": `hsep : ∀ k (a a' : d → ℝ), (∀ W, A.f k ((Matrix.of fun _ : T => a') * W) = A.f k
    ((Matrix.of fun _ : T => a) * W)) → a' = a`. "For all writes" is dropped rightly: `f(aW) W_write
    = f(a′W) W_write` for all `W_write` is `f(aW) = f(a′W)`.
  - Fact (c), "If `u_{ℓ−1} ≠ 0`, some read of block `ℓ` gives hidden units that do not all vanish,
    and its write then sends them to any row": `hnz : ∀ k (a : d → ℝ), a ≠ 0 → ∃ (W) (t : T) (j :
    A.w k), A.f k ((Matrix.of fun _ : T => a) * W) t j ≠ 0`.
  - The conclusion `∀ ℓ, (G ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ` from `h : ∀ θ x, eval A
    0 (θ.cob G G) x = eval A 0 θ x` is the lemma's.
- **The hypotheses for attention.** `hsees : ∀ t, ∃ s, sees t s`, `hH : ∀ ℓ, Nonempty (H ℓ)`,
  `hdh : ∀ ℓ, Nonempty (dh ℓ)`; for transformers `hblk : ∀ ℓ, (Nonempty (H ℓ) ∧ Nonempty (dh ℓ)) ∨
  Nonempty (hid ℓ)`. The paper's Lemma A.4 says "whose blocks are those of Section 2" and states
  no condition on the mask. Under both masks of the paper every token sees itself, an attention
  block has a head of positive width and an MLP block a hidden unit, so the Lean hypotheses hold
  for the paper's networks.
- **A mask where some token sees no token: the hypothesis `hsees` cannot be dropped** (by
  compiling, `Cex.lean`; Lean's attention gives the weights `0` to a token that sees none, so its
  row of the block's output is `0`).
  1. If no token sees any token, the network with one attention block computes `0` at all
     parameters (`eval_attention_noSee`, for any tokens, sizes and heads). So every family of
     invertible matrices passes. With one token, `d = d_in = d_out = 1`, one head of width `1`,
     `ε = 1` and `G_0 = G_1 = 2`: every hypothesis of
     `orthogonal_of_eval_cob_skipless_rmsNorm_attention` holds but `hsees`, and the conclusion
     fails (compiled as one statement).
  2. `hsees` cannot be weakened to "some token sees some token": with two tokens, token 0 seeing
     token 1 only and token 1 seeing no token, the network with two blocks computes `0` at all
     parameters (`eval_attention_sees01`, any sizes and heads), so again every family passes.
  Both rest on the three standard axioms. `hsees` is sufficient and not necessary (with the mask
  of 2 and one block the conclusion may still hold; I did not decide it). By hand: `hH`, `hdh`
  and `hblk` are needed for the same reason, since a block without a head of positive width and
  without a hidden unit writes `0`.

### `Generic/GroupDimension.lean` (4 theorems)

Paper: S Theorem 3.3 (ii), the four numbers `(L + 1) d²`, `d²`, `(L + 1) d(d−1)/2`, `d(d−1)/2`.

| Statement | Verdict |
|---|---|
| `dimH_setOf_forall_isUnit_det (n : ℕ)`: the `dimH` of the set of the `m : Fin n → Matrix d d ℝ` with `∀ ℓ, IsUnit (m ℓ).det` is `((n * Fintype.card d ^ 2 : ℕ) : ℝ≥0∞)` | PART of Theorem 3.3 (ii) (the dimension of the set, as a Hausdorff dimension); the value is the paper's |
| `dimH_setOf_forall_mem_orthogonalGroup (n : ℕ)`: `n * (Fintype.card d * (Fintype.card d - 1) / 2)` | the same |
| `dimH_setOf_const_isUnit_det (hn : 0 < n)`: `Fintype.card d ^ 2` | the same; `hn` is needed |
| `dimH_setOf_const_mem_orthogonalGroup (hn : 0 < n)`: `Fintype.card d * (Fintype.card d - 1) / 2` | the same; `hn` is needed for `d ≥ 2` |

Values by hand and by compiling: Check 5.

### `Symmetry/CobGroup.lean` (2 definitions, 11 theorems)

Paper: S Theorem 3.3 (ii) and Theorem A.17 (i).

| Name | Verdict |
|---|---|
| `cobPreserving` (definition) | SAME: "the changes of basis that preserve the function at all parameters" |
| `cobPreservingMat` (definition) | SAME set, as families of matrices |
| `exists_subgroup_eq_cobPreserving` | SAME ("form a group"); for any network and any stream matrices |
| `cobPreserving_skipless` | SAME as D Proposition 3.2 without normalization: every family passes |
| `dimH_cobPreservingMat_skipless` | SAME: `(L + 1) d²`; any blocks |
| `dimH_cobPreservingMat_skipless_rmsNorm` | PART: `(L + 1) d(d−1)/2` given the conclusion of Lemma A.4 as the hypothesis `hOnly` |
| `…_skipless_rmsNorm_mlp`, `_gated`, `_attention`, `_attentionMlp`, `_attentionGated` | SAME: `(L + 1) d(d−1)/2` for the blocks of the paper, under the hypotheses of Lemma A.4 for them (Check 3) |
| `dimH_cobPreservingMat_residual` | SAME: `d²`; LEAN STRONGER than Theorem A.5 (iii) in one point (no `d ≥ 2`); for any blocks that are not identically zero |
| `dimH_cobPreservingMat_residual_rmsNorm` | SAME: `d(d−1)/2`, `ε > 0`; no `d ≥ 2` |

- "A group of dimension": Check 5.
- The docstrings of the two residual statements say "are the families with all `G_ℓ` equal, a
  group of dimension `d²`". The statements give the dimension; that the set is the families with
  all `G_ℓ` equal is `eval_cob_residual_iff` and `eval_cob_residual_rmsNorm_iff`
  (`Residual/OneChangeOfBasis.lean`).
- Not stated by name: the residual dimensions for the kinds of block of the paper (each needs
  `hne` for its blocks; compiled for one tanh network, `Chk2.lean`). "So the `L` skips remove `L
  dim 𝒢` dimensions of symmetry" (Theorem A.17 (i)) is the difference of two statements and is
  not a statement of its own.

### `OneBlock/LearnedSkip.lean` (5 definitions, 3 theorems)

Paper: S Setup ("`A_ℓ` is a trainable `d_model × d_model` matrix in a network with learned skips"),
Definition 4.1, Appendix B ("A learned skip `A ∈ ℝ^{d_model × d_model}` is full or upper
triangular", "Notation and flat directions").

| Name | Verdict |
|---|---|
| `evalSkips` | SAME for `ι` the identity (S equation (2) with trainable `A_ℓ`); with a general `ι` a restricted family of skips, as the paper's triangular skip: more general |
| `jacobianRankSkips`, `funDimSkips` | SAME: Definition 4.1 for this family (Check 2) |
| `flatSkips` | SAME: `K(θ)` of Appendix B for this family |
| `funDimLearned` | SAME: the functional dimension of the network with full learned skips |
| `funDimSkips_add_finrank_flatSkips` | PART (proof piece: "`fd = P − dim K(θ)`", used throughout Appendix B); for differentiable `f_ℓ`, `χ` |
| `ae_funDimSkips_ge` | PART (proof piece: the generic rank is the largest; S proof of Proposition 4.5, first paragraph, for this family) |
| `funDimSkips_comp_le` | PART (proof piece: "For an upper triangular `A`, view the network as the network with a full `A` restricted to triangular skips"; the inequality only) |

### `OneBlock/LearnedSkipZero.lean` (1), `OneBlock/LearnedSkipBound.lean` (1)

| Statement | Paper | Verdict |
|---|---|---|
| `funDim_add_finrank_le_funDimSkips_zero` | none: "a step that is not in the paper", as the header says | DIFFERENT (another route than Part (iii) of the paper's proof); true (Check 6 (b)) |
| `funDimLearned_add_le_rmsNorm` | S proof of Theorem B.1, Part (iii), Step 5: "The directions `η^rot` are independent of `K_B` and of each other […] For a full `A` they have dimension `d_model (d_model − 1)`" | PART (the upper bound) and LEAN STRONGER in its range: any differentiable block, any `(θ, A)` with `E` and `D` of rank `d`, also a skip that is not invertible; true (Check 6 (b)) |

### `OneBlock/LearnedSkipKinds.lean` (8 theorems)

Paper: S Theorem 4.6 (ii), last sentence; S Theorem B.1 (iii).

| Statements | Verdict |
|---|---|
| `ae_funDimLearned_tanh_rmsNorm`, `…_gelu_…`, `…_swiglu_…`, `…_geglu_…` | PART of Theorem B.1 (iii): the value and "it satisfies the equality condition", for four of the eight kinds, the full skip, width at least `d`, `ε > 0`. Within this range SAME |
| `ae_funDimLearned_tanh_rmsNorm_eq_residual_add`, `…_gelu_…`, `…_swiglu_…`, `…_geglu_…` | PART of Theorem 4.6 (ii), "A learned skip raises it by exactly `d_model (d_model + 1)/2` more than an identity skip": four of the eight kinds of the theorem. Within this range SAME |

What is not covered: Check 6 (c).

### The index rows of the twelve files

By a script (`index_names.py`): every one of the 78 public names is in the row of its file,
written out or by a stated abbreviation ("each also with `_rmsNorm`", "`…_cob_const`", "the same
with `gelu`, `swiglu`, `geglu`"); all 71 theorems stand in `checks/Axioms.lean`; all twelve rows
say "proved", which is right at `4e16789`. Nothing is missing. What is wrong or thin: the
corrections below.

---------------------------------------------------------------------------------------------------

## What the authors should know

Nothing false and nothing vacuous. In order of weight:

1. **The right side of the 24 `iff` statements leaves out the permutations and the sign flips,
   and the text does not say so.** The headers of `Dimension/IdentifiableIff.lean` and
   `Residual/IdentifiableIff.lean` say "The symmetries are those of the papers", and the index
   rows say "the image of `θ` under a symmetry". The paper's proof counts the permutations and
   the sign flips among the symmetries for the converse. Lean's direction "locally identifiable ⟹
   equality condition" is therefore proved for a stronger hypothesis than the paper's. The
   equivalences are true, and the gap is one short step (Check 4). Either the text should say it,
   or the step should be stated; or the paper's Definition 4.5 / 4.4 could say which symmetries
   it means.
2. **The brief counts twenty-eight `iff` statements; there are twenty-four,** and four statements
   at one parameter in `IdentifiableIffTransformer.lean`.
3. **Lemma A.4 for attention needs a condition on the mask, and the paper states none.** If no
   token sees a token, or if a token that is seen sees none itself, the network can compute `0`
   at all parameters and every change of basis passes (compiled, `Cex.lean`). Lean has `hsees`
   (every token sees some token). The paper's two masks satisfy it; the lemma's text ("whose
   blocks are those of Section 2") relies on that.
4. **Lean asks less than the Scope** in the `iff` statements (no `d_out ≥ d`, no `d ≥ 2`, no
   token, no width for residual networks) and in the residual group statements (no `d ≥ 2`,
   which Theorem A.5 (iii) has). These are strengthenings.
5. **Three statements changed in form while I read:** `omit [DecidableEq d] in` was added to the
   three theorems of `OneBlock/LearnedSkip.lean` when they were proved. Nothing else changed in a
   statement or docstring of the twelve files between `a8aa4e1` and `4e16789`.
6. **"Dimension" is the Hausdorff dimension of a set of families of matrices.** That is the right
   number for these sets. A reader who wants "a Lie group of dimension `k`" from Lean alone gets
   "a subgroup" and "a set of Hausdorff dimension `k`", and the description of the set from other
   files.
7. **Theorem B.1 (iii) is covered for four kinds of block, the full skip, width at least `d` and
   `ε > 0`.** The computation shows the paper's value also for narrower blocks, which the Lean
   route through the skip `0` cannot reach (Check 6 (c)).
8. `OneBlock/LearnedSkipTriangular.lean` appeared at `c55748b` and has `sorry` at `4e16789`. No
   reader has compared it.

## Corrections for `STATEMENTS.md` (line numbers of `4e16789`)

1. Lines 766, 767 and 771 (the rows of the three `iff` files). After "the image of `θ` under a
   symmetry" add: "the continuous symmetries only; the permutations of hidden units or heads and
   the sign flips of tanh units, which the paper's proof counts for the converse, are not in the
   family, so the direction from local identifiability to the equality condition is proved for
   this smaller family". Line 766 already says that the symmetries are not asked to be close to
   the identity; lines 767 and 771 could say it too.
2. Line 767 (`Residual/IdentifiableIff.lean`). "blocks of any widths": add "(heads of width `d_h ≤
   d`)", which the six statements with heads have as `hdh`. "For tanh, GELU, SwiGLU, GeGLU and
   attention blocks both sides are proved": add "under the hypotheses of Theorem 4.7 (`d_in,
   d_out ≥ d ≥ 2`, a token; two tokens and `d_h ≥ 1` for attention)".
3. Lines 766, 767, 771. Add that the statements for gated units ask `d ≥ 1` (`[Nonempty d]`), and
   that none asks `d_out ≥ d`, `d ≥ 2` or a token.
4. Lines 651 to 656, "Not stated yet from the main text of the skips paper: […] the sentence of
   Theorem 4.6 (ii) on a learned skip, for every kind of block". Out of date since `a8aa4e1`: the
   sentence is stated, and at `4e16789` proved, for tanh, GELU, SwiGLU and GeGLU blocks
   (`OneBlock/LearnedSkipKinds.lean`). Write: "the sentence of Theorem 4.6 (ii) on a learned skip
   for ReLU, ReLU², ReGLU and attention blocks".
5. Line 770 (`Symmetry/CobGroup.lean`). Add: "the two residual statements ask at least one token
   and `d_in, d_out ≥ 1`, and not `d ≥ 2` (Theorem A.5 (iii) has it); the statement with `hOnly`
   has no `ε > 0`; that the group is the set of the families with all `G_ℓ` equal is in the row
   of `Residual/OneChangeOfBasis.lean`".
6. Line 768 (`Symmetry/OnlyOrthogonalRows.lean`). Add: "the hypothesis on the mask is needed: if
   no token sees a token the network computes `0` at all parameters (checked by the sixteenth
   reader)".
7. Line 775 (`OneBlock/LearnedSkipKinds.lean`). Add: "the first statement of each kind is the
   paper's 'and it satisfies the equality condition' (`P + d²` parameters, symmetries of
   dimension `d(d−1) + s`)", and "Theorem B.1 (iii) has no hypothesis on the width".
8. Line 772 (`OneBlock/LearnedSkip.lean`). Nothing wrong. If the row is to show signatures: the
   three theorems no longer take `[DecidableEq d]`.
9. Lines 166 to 172, "Not yet compared by such a reader": after this audit take out the twelve
   files of this brief (compared at `a8aa4e1` and `4e16789`). `OneBlock/LearnedSkipTriangular.lean`
   stays.
10. Outside the index, the headers of `Dimension/IdentifiableIff.lean` and
    `Residual/IdentifiableIff.lean`: "The symmetries are those of the papers" should read "the
    continuous symmetries of the papers", with the sentence of correction 1.

## What I could not check

- **The proofs.** I read none as a proof. "Proved" means no `sorry` in the file at `4e16789` and
  the three standard axioms in the copied build.
- **The build.** I did not build the library. I used a copy of the build of `/home/claude/lp/lean`
  (its owner's), taken when its sources were those of `lw` at `4e16789`. I did not recompile the
  twelve files myself.
- **`OneBlock/LearnedSkipTriangular.lean`** and the new row of the index for it (line 776): not
  compared.
- **The step from the paper's family of symmetries to Lean's** (permutations and sign flips are
  isolated at generic parameters): by hand, a sketch; not a Lean statement and not compiled.
- **Whether `hsees` can be weakened** (for instance to "some token sees itself"): not decided.
  That `hH`, `hdh`, `hblk` are needed: by hand only.
- **The numerical ranks**: one token, MLP and gated blocks, one random draw per case, 50 digits.
  No attention block and no input of several tokens. They support the statements and prove
  nothing.
- **The Hausdorff dimension of the four sets**: by hand from "a smooth submanifold of dimension
  `k` has Hausdorff dimension `k`", and by the instances that I compiled, which only evaluate the
  formulas of the proved statements.
- **The older files** on which the twelve rest (`Dimension/LocalIdentifiability….lean`,
  `Residual/LocalIdentifiability….lean`, `Residual/OneChangeOfBasis.lean`,
  `Symmetry/OnlyOrthogonal.lean`, `Symmetry/InsideBlocks.lean`, the upper bounds, the skipless
  values of `Depth/TanhRMS.lean` and `Depth/GeluGatedTheorem.lean`): I read the definitions and
  the statements that I quote, and did not compare them with the papers again.
- **The coordinator's script** `learned_skip_oneblock_check_2026-11-24.py`: not run; I read its output.

Scratch files: `/home/claude/audit16/` (`stmts.py`, `omits.py`, `mkax.py`, `ae_shapes.py`,
`index_names.py`, `Ax.lean`, `Chk.lean`, `Chk2.lean`, `Cex.lean`, `learned_skip_refute.py`, with
their outputs; `build/`, the copied build; `env.sh`, the `LEAN_PATH`).
