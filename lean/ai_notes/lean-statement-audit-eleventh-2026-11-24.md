STATUS: complete

# Eleventh audit of Lean statements against the papers (24 November 2026)

Reader: an independent reader who did not write the statements. Brief:
`/home/claude/proj_up/audit11_brief_2026-11-24.md`. Subject: absorb Proposition 4.6, absorb
Proposition 4.7 with the definition of a full network, the attention block with absorb Theorems
3.4 and A.13, and the sentence after skips Proposition A.33.

Library: `/home/claude/lw/lean` (branch `lean-wip`).

- Commit when I began: `e5836b3fcc8fe8e3fe09d69e39d06722fb42786a` (13:23:23 UTC).
- Commit when I ended: `829f2b158efbafc6b3760b39ca9ece6c42ee9bbd` (13:34:25 UTC). The branch moved
  three times while I read (`9cf33d3`, `67dc08f`, `829f2b1`).
- Between the first and the last: six of the seven files of the brief did not change, and neither
  did the files that define what they use (`git diff --quiet e5836b3 67dc08f` on `Network/Attention`,
  `Absorb/InjectiveBlocks`, `Absorb/FullNetworks`, `Absorb/PatternMaps`,
  `Dimension/RankCriterionOn`, `Residual/FoldingDim`, `Network/Defs`, `Network/Blocks`,
  `Dimension/Functional`, `Residual/Folding`, `Literature/Sard`, `Literature/InvarianceOfDomain`,
  `Residual/DepthRescale`, `Residual/SmallWrites`, `Absorb/Block`, `Absorb/FirstBlock`; the commit
  `829f2b1` adds two new files and touches no other Lean file). In `Absorb/AttentionBlock.lean`
  the seven `sorry` were replaced by proofs (at `67dc08f`) and private helpers were added; the
  seven public statements, their docstrings and the file header are the same (the only lines that
  the diff removes are the seven `sorry`).
- Files with `sorry`: at `e5836b3`, one: `Absorb/AttentionBlock.lean` (7). At `829f2b1`, four, all
  new and outside the brief: `Absorb/AttentionZero.lean` (1), `Absorb/AttentionNetworks.lean` (6),
  `Symmetry/AttentionHeads.lean` (5) and `Dimension/UpperBoundAttention.lean` (8). None of the
  seven files of the brief has a `sorry` at `829f2b1`. I did not compare the four new files with
  the papers.

Papers, as text: the absorb paper ("A", `absorb.txt`), the skips paper ("S", `skips.txt`), the
dimension paper ("D", `dim.txt`). Line numbers of `STATEMENTS.md` are those of `829f2b1`.

How I checked.

- "By reading": I read the seven Lean files in full, the definitions they use (`Arch`, `Params`,
  `hidden`, `eval`, `Arch.mlp`, `vanillaBlock`, `blockMapRes`, `Folds`, `UnitInactiveRes`,
  `Params.withActivation`, `Params.smallWrites`, `InvarianceOfDomain`, `SardCriticalValues`,
  `jacobianRank`, `funDim`), and the paper passages (A Sections 2, 3.3, 4.4, the proofs of
  Propositions 4.6 and 4.7 and of Theorem A.13, Remark A.12; S Lemma A.30, Appendix A.8 to the
  sentence after Proposition A.33; D Appendix C, "Attention blocks", Reduction).
- "By hand": a short argument of my own, written out in the note.
- "By compiling": scratch files of my own in `/home/claude/audit11/` (`Chk.lean`, `Chk2.lean`,
  `Chk4.lean`, `Chk5.lean`; outputs `Chk*.out`), compiled with `lean` 4.36.0 through `LEAN_PATH`,
  without `lake`. The compiled library of `lw` has none of the seven files, so I read the compiled
  library of `/home/claude/lp/lean` in place (its sources under `SkipsLean/` were the same as
  those of `lw`, by `diff -rq`, at 13:29 except the proofs in progress in `AttentionBlock.lean`,
  and with no difference when both stood at `67dc08f`; the seven files and their definitions are
  the same in both at the end). I did not run `lake build` and wrote nothing under `lw`, `lp`
  or the repository. Seven compilations of 3 to 4 seconds each.
- "By a computation": `/home/claude/audit11/attention_check.py` (numpy, double precision), output
  `attention_check.out`.

Short answer. **Nothing false, vacuous or drifted was found.** Every statement at generic weights
is `∀ᵐ … ∂μ` for any additive Haar measure. `IsFull` is the paper's definition. The main
statements carry the paper's hypotheses, at least one token (Proposition 4.6 only), and the two
results from the literature as hypotheses (invariance of domain for Proposition 4.6, Sard's
theorem for Proposition 4.7). Lean's attention statements hold for more masks than the paper's
two. Two places of the index and one file header are out of date (corrections below).

---------------------------------------------------------------------------------------------------

## Part 1: the drift checks

### Check 1. Generic means almost every parameter, for every Haar measure

**Verdict: yes, in every statement of the seven files that states an "almost every".**

| Statement | Quantifier | Measure |
|---|---|---|
| `ae_isFull_imp_eval_ne_skipless_relu` (A Proposition 4.7) | `∀ᵐ θ ∂μ, IsFull θ → …` | any `μ` with `[μ.IsAddHaarMeasure]` on the weights of the residual network |
| `ae_eventually_isFull_smallWrites` ("full networks exist") | `∀ᵐ θ ∂μ, ∀ᶠ τ in 𝓝[≠] 0, IsFull (θ.smallWrites τ)` | the same |
| `ae_mul_add_attnHeads_ne`, `ae_mul_add_attentionBlock_ne` (A Theorem 3.4 (i), A.13 (i)) | `∀ᵐ h ∂μ, …` | any additive Haar `μ` on `T → d → ℝ` |
| `exists_isOpen_folds_funDim_add_le_relu` (S, after A.33) | `∃ U, … ∧ ∀ μ [Haar], ∀ᵐ θ ∂μ, θ ∈ U → …` | any additive Haar `μ` on the weights; `U` does not depend on `μ` |
| `ae_notMem_iUnion_range_of_rank_lt_on` (Step 4, without networks) | `∀ᵐ θ ∂μ, θ ∈ U → ∀ i, F θ ∉ Set.range (G i)` | any additive Haar `μ` on `P` |

**(a) Proposition 4.7.** The Lean text (by compiling, `Chk.out`: the statement as elaborated;
here with the names of the instances left out):

```
ae_isFull_imp_eval_ne_skipless_relu : ∀ {T d dIn dOut} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d]
  [Fintype dIn] [Fintype dOut] {hid : Fin L → Type} [(ℓ : Fin L) → Fintype (hid ℓ)] [Nonempty d],
  (∀ (m : Fin L → ℕ) (r : ℕ), SardCriticalValues (Params (Arch.mlp relu id fun ℓ => Fin (m ℓ)) dIn dOut) (Fin r → ℝ)) →
  ∀ (μ : Measure (Params (Arch.mlp relu id hid) dIn dOut)) [μ.IsAddHaarMeasure],
  Fintype.card d ≤ Fintype.card dIn →
  ∀ᵐ θ ∂μ, IsFull θ → ∀ (m : Fin L → ℕ), (∀ ℓ, Fintype.card d ≤ m ℓ) →
    (2 * Fintype.card d - 1) * ∑ ℓ, m ℓ < (2 * Fintype.card d - 1) * ∑ ℓ, Fintype.card (hid ℓ) + L * Fintype.card d ^ 2 →
    ∀ (η : Params (Arch.mlp relu id fun ℓ => Fin (m ℓ)) dIn dOut),
      eval (Arch.mlp relu id hid) 1 θ ≠ eval (Arch.mlp relu id fun ℓ => Fin (m ℓ)) 0 η
```

- *"For almost every full residual network".* `∀ᵐ θ ∂μ, IsFull θ → …` says: the full `θ` for which
  the conclusion fails form a set of measure zero. That is the paper's sentence. One null set
  serves all widths `m` and all weights `η` of the skipless network (the quantifiers over `m` and
  `η` are inside `∀ᵐ`), as in the paper ("every skipless network … that equals it"). The full
  networks form an open set (`isOpen_setOf_isFull`), so the sentence is not about a null set
  when a full network exists; one exists for `d_in, d_out ≥ d ≥ 2`
  (`ae_eventually_isFull_smallWrites`). Faithful. (By reading.)
- *The contrapositive.* The paper: an equal skipless network has `n ≥ L d²/(2d − 1)` more hidden
  units in total, `n = ∑ m ℓ − s`. Lean: if `(2d − 1) ∑ m ℓ < (2d − 1) s + L d²`, no network with
  the widths `m` equals `θ`. Over the integers the Lean inequality is `(2d − 1) n < L d²`, the
  negation of the paper's. Fewer hidden units in total (`∑ m ℓ < s`): then
  `(2d − 1) ∑ m ℓ < (2d − 1) s ≤ (2d − 1) s + L d²`, so Lean's condition holds and Lean concludes
  "not equal"; the paper's sentence says the same (such a network does not have "at least … more").
  The subtraction `2 * card d - 1` is a subtraction of natural numbers; `[Nonempty d]` gives
  `card d ≥ 1`, so it is the true `2d − 1 ≥ 1`. Faithful. (By hand; the private lemma
  `rank_lt_full` of the file does the same arithmetic.)
- *The condition is not empty* (by compiling, `Chk.lean` (e)): for `L ≥ 1` and the residual
  network of widths `m ℓ ≥ d`, the Lean statement gives "almost every full `θ` equals no skipless
  network of the same widths".
- *`m ℓ ≥ d`.* It is the paper's setting. A Section 2, Scope: "Every MLP block has at least
  `d_model` hidden units"; the proof of Proposition 4.7, Step 2, uses it for the skipless network
  ("each of its blocks has at least `d_model` units (Section 2), so for generic weights its writes
  have rank `d_model`"). The sentence of Proposition 4.7 in the main text does not repeat it. Lean
  does not ask it of the residual network (`hid` is any family of finite types).
- *The widths of the skipless network are `Fin (m ℓ)`.* Every finite width is one of these up to
  the names of the units, so nothing is lost; a user with another index type must rename the
  units first (no lemma for that is stated).
- *Every Lean hypothesis beside the paper's.*

| Lean | Paper |
|---|---|
| `[Nonempty d]`: `d ≥ 1` | Scope: `d_model ≥ 2` (Lean asks less) |
| `hdIn : card d ≤ card dIn` | Scope: `d_in ≥ d_model` |
| nothing on `d_out` | Scope: `d_out ≥ d_model` (Lean asks less) |
| `∀ ℓ, card d ≤ m ℓ` (skipless blocks) | Scope, and Step 2 of the proof |
| nothing on the widths of the residual network | Scope: at least `d_model` units (Lean asks less) |
| `L` any natural number, `0` included | `L ≥ 1` |
| `T` any finite type; no `[Nonempty T]` (it is omitted for this theorem) | the proof works on rows |
| `hSard`: Sard's theorem for real-analytic maps from the weights of each skipless network to `ℝ^r`, every `m` and `r` | "by Sard's theorem" (Step 4) |
| `μ` any additive Haar measure | "almost every" = outside a Lebesgue null set (Section 2) |

  `hSard` is a hypothesis, not an axiom; it is Sard's theorem, a true statement, so it removes no
  case. For an empty `T` the statement is true and says nothing (then `IsFull θ` forces `s = 0`,
  and no `m` satisfies the two conditions; by hand).

**(b) `ae_mul_add_attnHeads_ne`.** `(μ : Measure (T → d → ℝ)) [μ.IsAddHaarMeasure]`,
`∀ᵐ h ∂μ, Matrix.of h * M + attnHeads sees Γ C (Matrix.of h) ≠ attnHeads sees Γ' C' (Matrix.of h)`.
It is "for almost every `h ∈ ℝ^{T×d}`" for every Haar measure. Lebesgue measure `volume` on
`T → d → ℝ` is one of them (by compiling, `Chk2.lean`, `volume_haar`), and the statement applies
to it (`Chk2.lean`, two examples). One point of use: Lean does not find the instance
`(volume : Measure (T → d → ℝ)).IsAddHaarMeasure` by itself for this type of functions of
functions; it has to be given in two lines (`isAddHaarMeasure_volume_pi d`, then the instance for
products). This changes nothing in the statement.

### Check 2. `IsFull` against the paper's definition

**Verdict: the same notion.**

```
def IsFull (θ : Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut) : Prop :=
  ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ),
    (∀ (i : Fin n) (ℓ : Fin L) (t : T) (j : hid ℓ),
      (hidden (Arch.mlp relu id hid) 1 θ (X i) ℓ.castSucc * θ.read ℓ) t j ≠ 0) ∧
    jacobianRank (Arch.mlp relu id hid) 1 X θ + (Fintype.card d ^ 2 + ∑ ℓ, Fintype.card (hid ℓ))
      = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut)
```

Clause by clause (by reading):

- "a residual ReLU network": `Arch.mlp relu id hid` (ReLU, `χ = id`: no normalization) with the
  stream matrices `1` (the identity at every block).
- "some finite set of inputs": `n` and `X : Fin n → Matrix T dIn ℝ`. A family, so an input may
  occur twice (this changes neither the rank nor the clause on the arguments), and `n = 0` is
  allowed (it matters only when `P = d² + s`).
- "at which no unit has argument `0`": `hidden … 1 θ (X i) ℓ.castSucc` is the hidden state that
  block `ℓ` reads (`h_0 = X E` for the first block), and its product with `θ.read ℓ`, at token `t`
  and unit `j`, is the argument of unit `j` of block `ℓ` at that token. The clause asks `≠ 0` for
  every input, block, token and unit. That is the paper's clause.
- "this rank is reached": `jacobianRank + (d² + s) = P`, with `P` the dimension of the space of
  weights (`finrank_params_mlp`: `d_in d + 2 d s + d d_out`) and `s = ∑_ℓ card (hid ℓ)`. As a
  statement about natural numbers it is "rank `= P − d² − s`" (it is false when `P < d² + s`, as
  the paper's is).
- *Tokens.* The paper's proof takes rows (`T` of one element). An MLP network acts on each row
  separately, so a batch of `n` inputs with the tokens `T` is the batch of its `n·|T|` rows: the
  same rank, the same clause. With at least one token, `IsFull` with `T` is `IsFull` with one
  token (take inputs with equal rows). (By hand.)
- *Can `jacobianRank` differ from the paper's rank here?* No. `jacobianRank` is the rank of
  Mathlib's `fderiv` of `θ ↦ (F_θ(X i))_i`, which is `0` where that map is not differentiable. On
  a batch on which no unit has argument `0` at `θ`, the map is continuously differentiable near
  `θ`: the file proves it (`contDiffAt_evalBatch_full`, private, used in the proof of the
  proposition), since
  ReLU is linear near every nonzero argument. So `fderiv` is the Jacobian, and the Lean rank is
  the paper's rank. `IsFull` only uses such batches, so the convention "`0` where not
  differentiable" never enters `IsFull`. (By reading.)

### Check 3. No extra hypotheses in the main-text statements

**Proposition 4.6.** The Lean text (by compiling, `Chk.out`; names of the instances left out):

```
two_mul_card_le_of_eval_eq_skipless_relu : ∀ {T dIn dOut} {d : Type} {L : ℕ} [Fintype d] [DecidableEq d]
  [Fintype dIn] [Fintype dOut] {hid : Fin L → Type} [(ℓ : Fin L) → Fintype (hid ℓ)] [Nonempty T],
  InvarianceOfDomain d →
  ∀ (θ : Params (Arch.mlp relu id hid) dIn dOut), θ.E.rank = Fintype.card d → θ.D.rank = Fintype.card d →
  (∀ (ℓ : Fin L), Function.Injective (blockMapRes θ ℓ)) →
  ∀ {L' : ℕ} (hid' : Fin L' → Type) [(ℓ : Fin L') → Fintype (hid' ℓ)] (θ' : Params (Arch.mlp relu id hid') dIn dOut),
  (∀ (X : Matrix T dIn ℝ), eval (Arch.mlp relu id hid') 0 θ' X = eval (Arch.mlp relu id hid) 1 θ X) →
  ∀ (ℓ : Fin L'), 2 * Fintype.card d ≤ Fintype.card (hid' ℓ)
```

| Paper | Lean | Verdict |
|---|---|---|
| "`σ` ReLU or GELU, without normalization" | two theorems, `relu` and `gelu`, `χ = id` | same |
| "`E` and `D` have rank `d_model`" | `hE`, `hD` | same |
| "every block of the residual network is injective on tokens when `σ` is replaced by ReLU: `x + B_ℓ(x) ≠ x' + B_ℓ(x')` for all tokens `x ≠ x'`" | `hinj : ∀ ℓ, Function.Injective (blockMapRes θ ℓ)`; for GELU, `blockMapRes (θ.withActivation relu) ℓ` (the same four weight matrices, ReLU as activation). `blockMapRes θ ℓ h = h + σ(h W_read^ℓ) W_write^ℓ` on a row `h ∈ ℝ^d`, all rows | same |
| "every skipless network of `σ` blocks, of any depth and with the same `d_model`, that equals the residual network" | any `L'`, any widths `hid'`, the same `d`; the same `T`, `dIn`, `dOut` (needed for the two functions to be compared); equality at every input `X` | same; Lean also allows `L' = 0`, blocks with fewer than `d` units, `L = 0` |
| "has at least `2 d_model` hidden units in every block" | `∀ ℓ : Fin L', 2 * card d ≤ card (hid' ℓ)` | same |
| — | `[Nonempty T]`: at least one token | needed (with no token all networks are equal) |
| "by invariance of domain" (proof, Step 2) | `hinv : InvarianceOfDomain d`: every injective continuous map of `ℝ^d` to itself is open | a hypothesis from the literature; a true special case of Brouwer's theorem; not an axiom |

So the skipless network of the Lean statement is at least as general as the paper's. No
hypothesis restricts the paper's statement. The proposition is proved *under* `hinv`; a reader of
the index should not read "proved" as "proved outright" (the index row says "under invariance of
domain").

**Theorem 3.4.**

| Paper | Lean (`ae_mul_add_attentionBlock_ne`, `exists_row_attentionBlock_sub_ge`) | Verdict |
|---|---|---|
| "any numbers of heads and any head dimensions" | `H H' dh dh' : Type*`, each a finite type, no other condition (no head, or head dimension `0`, allowed) | same |
| "`M ≠ 0`" | `hM` in (i); (ii) has no `hM` (it is true and empty of content for `M = 0`) | same |
| "`T ≥ 2` tokens" | `hT : 2 ≤ Fintype.card T` | same |
| "with or without a causal mask" | a relation `sees` and `(t₀ : T) (ht₀ : ∀ s, sees t₀ s)`: one token sees all tokens | more general |

The two masks are instances (by compiling, `Chk2.lean`):

- no mask: `sees := fun _ _ => True`, `t₀` any token (there is one, as `card T ≥ 2`),
  `ht₀ := fun _ => trivial`;
- the causal mask on `n + 2` tokens: `T := Fin (n + 2)`, `sees := fun t s => s ≤ t`,
  `t₀ := Fin.last (n + 1)`, `ht₀ := fun s => Fin.le_last s`.

What the hypothesis allows beyond them: any relation in which one token sees every token. The
other tokens may see any set of tokens, in no order, or no token at all (`Chk2.lean` has the
example "token `0` sees all, the others see nothing"). For a token that sees no token Lean's
attention weights are the zero row, so the block gives it the output `0`; this is Lean's choice
for a case the paper does not have (see Part 2, note 1). The statements stay true there: the proof
of the paper, and Lean's proof, look only at the row of `t₀` (by hand and by the computation,
which draws such masks). Not covered: a strict causal mask `s < t`, in which no token sees all
tokens (`Chk2.lean`, last example).

---------------------------------------------------------------------------------------------------

## Part 2: the statements, file by file

### Verdict table

"Proved" below: the file has no `sorry` at `67dc08f`, and `#print axioms` on the compiled library
of `lp` shows `propext`, `Classical.choice`, `Quot.sound` only (`Chk.out` for the first six files;
`Chk4.out` for `AttentionBlock.lean`, compiled at 13:32 after its proofs were merged; in my first
compilation, a few minutes earlier, the same seven names still showed `sorryAx`).

| Paper statement or proof piece | Lean | Verdict | Difference | How checked |
|---|---|---|---|---|
| A (4): "softmax … on each of its rows, with or without a causal mask, so each row of `P_Γ(h)` is a probability vector" | `attnWeights` | LEAN STRONGER | any relation `sees`; for the paper's two masks the same; a token that sees no token gets the zero row | reading; compiling (`Chk.lean` (a)); computation |
| A (4), block from score matrices and value–output products | `attnHeads` | SAME | any `d × d` matrices `Γ_i`, `C_i` (the paper's are products through `d_h`) | reading |
| A (4) | `attentionBlock` | SAME | — | reading; computation |
| A Section 3.3 "The read of the block holds … its write …"; D Appendix C, Reduction; S Section 2 | `Arch.attention` | SAME | — | reading; computation |
| the block of `Arch.attention` is (4) | `f_attention_mul` | correct identity; proved | — | by hand; computation |
| A proof of A.13, Step 1 | `attnHeads_const_row` | SAME | for one block, at a token that sees some token; the paper states the row of `F` | by hand; computation |
| A proof of A.13, Step 2 | `attnHeads_zero_row` | LEAN STRONGER | the other rows are arbitrary, and the row is the mean of all rows times `∑ C_i`; the paper's case (other rows `y`) gives `(T−1)/T · y C` | by hand; computation |
| A Theorem A.13 (ii), 3.4 (ii) | `exists_row_attnHeads_sub_ge`, `exists_row_attentionBlock_sub_ge` | SAME (LEAN STRONGER in the mask) | "for every row `x` of norm `≤ 1`, at least `‖x M‖/3`"; equivalent to `‖M‖/3` once the largest `‖x M‖` is taken, which Lean does not do | by hand; computation |
| A Theorem A.13 (i), 3.4 (i) | `ae_mul_add_attnHeads_ne`, `ae_mul_add_attentionBlock_ne` | SAME (LEAN STRONGER in the mask) | — | reading; compiling (`Chk2.lean`) |
| A Theorem A.13 (iii) | `exists_ne_residual_skipless_attnHeads` | SAME (LEAN STRONGER in the mask) | another model dimension `d'` is the paper's convention; stated for `attnHeads` only | by hand; computation |
| A proof of 4.6, Step 2, "A continuous, positively homogeneous, injective map … is onto" | `surjective_of_injective_of_posHomogeneous` | SAME, under `InvarianceOfDomain d` | — | reading |
| A proof of 4.6, Step 3 | `two_mul_card_le_of_injective_vanillaBlock_relu` | SAME | no invariance of domain | reading |
| A proof of 4.6, Step 1 and the kernels of `E`, `E'` in Step 2 | private helpers only | PART | not public statements | reading |
| A Proposition 4.6, ReLU | `two_mul_card_le_of_eval_eq_skipless_relu` | SAME, under `InvarianceOfDomain d` | at least one token; Lean allows more (Check 3) | reading; compiling |
| A Proposition 4.6, GELU | `two_mul_card_le_of_eval_eq_skipless_gelu` | SAME, under `InvarianceOfDomain d` | the same | reading |
| A "The condition holds when every block has `‖W_read‖ ‖W_write‖ < 1`, in spectral norm" | `…_relu_of_norm_lt_one`, `…_gelu_of_norm_lt_one` | SAME | Lipschitz constants `a ℓ`, `b ℓ` with `a ℓ b ℓ < 1`: equivalent (note 6) | by hand |
| A after 4.6: "an open condition …", "exactly `d_model` extra units … by Proposition 4.4"; Remark A.12 | — | not stated | the index says so for Remark A.12 only | reading |
| A proof of 4.7, Step 1: pattern, network of a pattern, "`F_Z(θ) = F^π_Z(θ)`" | `Arch.masked`, `Params.toMasked`, `reluPattern`, `eval_relu_eq_eval_masked`, `maskedBatch`, `evalBatch_relu_eq_maskedBatch` | SAME | for any stream matrices; one pattern per input and per token | reading |
| A proof of 4.7, Step 1: "a polynomial map `F^π_Z` of the weights" | `analyticOnNhd_maskedBatch` | LEAN WEAKER | real-analytic, not polynomial; enough for the proof | reading |
| A proof of 4.7, Step 2, residual network: every `F^π_Z` has rank `≤ r` at every `θ` | `jacobianRank_add_le_residual_relu_of_ne_zero` | PART | stated for the network on a batch on which no unit has argument `0` at `θ` (there it is its own pattern map), not for every pattern | reading |
| A before 4.7: "on any finite set of inputs, the Jacobian … has rank at most `P − d² − s`" | the same theorem | LEAN WEAKER | only batches on which no unit has argument `0` at `θ` (where the Jacobian exists); `d_in ≥ d ≥ 1` | reading |
| A proof of 4.7, Step 2, skipless network: rank `≤ P + 2dn − (L+1)d² − s − n` at every point | `finrank_range_fderiv_maskedBatch_skipless_add_le` | SAME | Lean's `P`, `s` are those of the skipless network itself; `d_in ≥ d ≥ 1`, blocks of `≥ d` units | reading; by hand |
| A definition of a full network | `IsFull` | SAME | Check 2 | reading |
| A Proposition 4.7, first sentence; proof, Step 3 | `isOpen_setOf_isFull` | SAME | `d_in ≥ d ≥ 1` | reading |
| A proof of 4.7, Step 4, without networks | `ae_notMem_iUnion_range_of_rank_lt_on` | SAME in content | Lean's own form: `F` of class `C¹` on an open `U` with rank `> r₀`, countably many analytic `G i` of rank `≤ r₀`; no constant rank theorem | reading |
| A Proposition 4.7, second sentence | `ae_isFull_imp_eval_ne_skipless_relu` | SAME, given Sard's theorem | Check 1 (a) | reading; by hand; compiling |
| A after 4.7: "Full networks exist: every network with generic weights is full once all its writes are scaled by a small enough factor" | `ae_eventually_isFull_smallWrites` | SAME | `d_in, d_out ≥ d ≥ 2`; at least one token; `τ` of either sign | reading |
| A after 4.7: "Not every network is full, since on another open set of weights a unit is never active" | — | not stated | follows in a few lines (`Chk5.lean`) | compiling |
| S, the sentence after Proposition A.33 | `exists_isOpen_folds_funDim_add_le_relu` | LEAN WEAKER | "at almost every point of" the open set, where the paper says "on the open set"; the index says so. Lean gives the amount `2d − 1` and any two consecutive blocks | reading |

### Notes

**1. `attnWeights` (`Network/Attention.lean:43-46`).**
`attnWeights sees Z t s = if sees t s then exp (Z t s) / ∑ s', (if sees t s' then exp (Z t s') else 0) else 0`.

- If token `t` sees some token, row `t` has entries `≥ 0` and sum `1`: a probability vector (by
  compiling, `Chk.lean` (a), second example).
- If token `t` sees no token, row `t` is `0` (first example of `Chk.lean` (a)). It is not a
  probability vector, and the block then gives token `t` the output `0`. Under the paper's two
  masks every token sees itself, so this case does not occur in the paper. The docstring of
  `attnWeights` is right as written ("`0` at the tokens it does not see"); neither it nor the
  index says what happens to a token that sees nothing.

**2. `attnHeads`, `attentionBlock`, `Arch.attention` against equation (4).** (By reading.)

- `attnHeads sees Γ C h = ∑ i, attnWeights sees (h * Γ i * hᵀ) * h * C i`: the paper's
  `∑_i P_{Γ_i}(h) h C_i`, `P_Γ(h) = softmax(h Γ hᵀ)`. Entry `(t, s)` of `h Γ hᵀ` is `h_t Γ h_sᵀ`,
  and the softmax runs over `s` in row `t`.
- `attentionBlock`: `Γ i = (Real.sqrt (Fintype.card dh))⁻¹ • (WQ i * (WK i)ᵀ)` and
  `C i = WV i * WO i`. The transpose is on the right factor `W_K`, the scale is `1/√d_h`, the
  value–output product is `W_V W_O`: equation (4). (For an empty `dh`, Lean's `(√0)⁻¹` is `0`; the
  matrices are empty then.)
- `Arch.attention`: the read of block `ℓ` has the columns `H ℓ × (dh ℓ ⊕ (dh ℓ ⊕ dh ℓ))`, a
  query, a key and a value column for each head and each coordinate, and the write has the rows
  `H ℓ × dh ℓ`: "The read of the block holds the matrices `W_{Q,i}`, `W_{K,i}` and `W_{V,i}`, and
  its write the matrices `W_{O,i}`". Its fixed map sends the queries, keys and values `M` to
  `(t, (i, k)) ↦ ∑_s a_ts M s (i, value k)`, where `a` is `attnWeights` of the scores
  `(t', s') ↦ (1/√d_h) ∑_k M t' (i, query k) · M s' (i, key k)`.
- *Which of query and key carries the row index `t`?* The query. In `Arch.attention` the score
  of the pair `(t', s')` is `⟨query of t', key of s'⟩/√d_h`, and row `t'` is normalized over
  `s'`. In `attentionBlock`, `(h Γ hᵀ)_{ts} = (1/√d_h) ∑_k (h W_Q)_{tk} (h W_K)_{sk}`: the same.
  This is the paper's `softmax(h W_Q W_Kᵀ hᵀ/√d_h)` row by row, and D's "scores `x_t B_i x_sᵀ`
  … weights `a_ts`, their softmax over the tokens `s` that token `t` sees, and the output at token
  `t` is `∑_i ∑_s a_ts x_s C_i`" with `B_i = E W_Q W_Kᵀ Eᵀ/√d_h`, `C_i = E W_V W_O D`.
- *`f_attention_mul` by hand.* The left side at `(t, a)` is
  `∑_{(i,k)} (∑_s a^i_ts (h R)_{s,(i,value k)}) W_{(i,k),a}`. With `W_{V,i}` the value columns of
  head `i` in `R` and `W_{O,i}` the rows of head `i` in `W`, this is
  `∑_i (P_i h W_{V,i} W_{O,i})_{ta}`, and the scores of head `i` are `h Γ_i hᵀ` with
  `Γ_i = W_{Q,i} W_{K,i}ᵀ/√d_h` from the query and key columns of `R`. So the identity is right.
  The computation agrees to `5·10⁻¹⁵` over 144 random cases (six masks, 2 and 3 tokens, `d = 1`
  and `3`, one and two heads, head dimensions 1 to 3), and exchanging query and key changes the block.
- In a block all heads have one head dimension (`dh ℓ`), as in the paper ("`H` heads of
  dimension `d_h`"); two blocks that are compared may have different numbers of heads and
  different head dimensions.

**3. Theorem A.13, Steps 1 and 2 (`Absorb/AttentionBlock.lean`).** (By hand; by the computation,
972 random cases with `T ∈ {2, 3, 5}`, `d ∈ {1, 2, 4}`, 0, 1 or 3 heads against 0, 1 or 2 heads,
six masks, `M` of full rank and of rank one: largest error `2·10⁻¹⁵`.)

- Step 1: if every row of `h` is `x` and token `t` sees some token, row `t` of
  `∑_i P_i h C_i` is `∑_i (∑_s P_i(t,s)) x C_i = x ∑_i C_i`. The paper: "every row of `R_k(h) h`
  is `x`". Same; Lean needs "sees some token" because of note 1.
- Step 2: if row `t₀` of `h` is `0` and `t₀` sees all tokens, every score in row `t₀` is
  `h_{t₀} Γ h_sᵀ = 0`, the weights are `1/T`, and the row is `(1/T ∑_s h_s) ∑_i C_i`. With the
  paper's `h` (the other rows equal to `y`) the mean is `((T−1)/T) y`: the paper's constant.
  Lean's statement holds for any other rows.

**4. (ii): `‖x M‖/3` for every `x` against `‖M‖/3`.** (By hand.)

- Rows act on the left in the paper (`h M`, tokens are rows), and Lean writes `x ᵥ* M`: the
  paper's convention. The spectral norm of `M` is the largest `‖x M‖₂` over rows with
  `‖x‖₂ ≤ 1`; it is the same number for rows on the left and columns on the right (the
  computation checks `‖u M‖ = ‖M‖₂` for the first left singular vector `u`).
- Lean implies the paper: take a row `x` of norm `≤ 1` with `‖x M‖ = ‖M‖` (the maximum is
  attained on the closed unit ball). The paper implies Lean: the one `h` of the paper works for
  every `x`, as `‖x M‖ ≤ ‖M‖`. So the two are equivalent. Lean does not state the form with the
  maximum; "norm at most `1`" is `x ⬝ᵥ x ≤ 1`, and the norms are `Real.sqrt (v ⬝ᵥ v)`.
- The statement is true for each `x` by the paper's proof with `y = x`: with
  `C = ∑ C'_k − ∑ C_i`, the row at `t₀` is `x(M − C)` for equal tokens and `−((T−1)/T) x C` with
  one zero token, and `‖x(M − C)‖ < ‖x M‖/3` forces `‖x C‖ > (2/3)‖x M‖`, so the second row has
  norm above `‖x M‖/3` as `(T−1)/T ≥ 1/2`. The computation finds the ratio exactly `1` in the
  worst case (`C = (2/3) M`, two tokens), so `1/3` cannot be improved on these two inputs; and
  with one token (excluded by `hT`) absorption happens.

**5. (i) and (iii), and the degenerate cases.**

- (i): `M ≠ 0`, `T ≥ 2`, one token that sees all; for almost every `h`, the two sides differ (as
  matrices: some entry differs). True by (ii) and analyticity; `attnWeights` is analytic in the
  scores for every relation `sees` (a row is `0` or has a positive denominator).
- (iii): `E D ≠ 0`; `∃ X, (X E + B_θ(X E)) D ≠ B_θ'(X E') D'`. "Differs from every skipless
  network" is "for every `Γ'`, `C'`, `E'`, `D'` there is an input". The skipless block has its own
  model dimension `d'`. This is the paper's setting, not a stronger statement: A Section 2, "A
  skipless network that is compared with a residual one may have another model dimension, unless
  the statement says 'the same `d_model`'". The same `sees` and the same tokens serve both
  networks.
- (iii) is stated for `attnHeads` only: there is no corollary for `attentionBlock`, and none in
  the form `eval (Arch.attention …)` of a network of one block. Both are immediate
  (`attentionBlock` is an `attnHeads`, and `f_attention_mul` gives the block of `Arch.attention`),
  but they are not stated in this file.
- Degenerate cases, looked at for a counterexample (by hand, and in the computation where it
  applies): `d` of one element (`M` a nonzero number); `M` of rank one; one head; no head on
  either side (the block is `0`; (iii) against the zero network still needs `E D ≠ 0` and holds);
  two tokens; a mask in which only `t₀` sees anything; `d` empty or `d'` empty. None is a
  counterexample. The proofs are now in the library (`Chk4.out`: three standard axioms), which
  settles truth; what I checked beyond that is that the statements say what the paper says.

**6. Proposition 4.6 (`Absorb/InjectiveBlocks.lean`).** (By reading and by hand.)

- Step 2, the topological fact: `ψ` continuous, `ψ(c u) = c ψ(u)` for `c > 0`, injective, then
  onto; under `hinv`. The paper's sentence.
- Step 3: `Function.Injective (vanillaBlock relu Wr Ww)` for `Wr : d × m`, `Ww : m × d` gives
  `2 d ≤ m`. No other hypothesis.
- The condition after the proposition. Lean: numbers `a ℓ`, `b ℓ` with
  `‖v W_read^ℓ‖₂ ≤ a ℓ ‖v‖₂` for all rows `v`, `‖u W_write^ℓ‖₂ ≤ b ℓ ‖u‖₂` for all rows `u`, and
  `a ℓ b ℓ < 1`. Such numbers exist if and only if `‖W_read^ℓ‖ ‖W_write^ℓ‖ < 1` in spectral norm:
  the spectral norms are such numbers; conversely, if `d` and the block are not empty, then
  `a ℓ ≥ ‖W_read^ℓ‖ ≥ 0` and `b ℓ ≥ ‖W_write^ℓ‖ ≥ 0`, so the product of the norms is at most
  `a ℓ b ℓ < 1`; and if `d` or the block is empty both matrices are empty and the product of
  their norms is `0`. So the Lean hypothesis is the paper's. For GELU the condition is on the
  same weight matrices, as in the paper ("the ReLU block `B` is then a contraction").
- Degenerate cases. `L = 0` (the residual network is `X ↦ X E D`): `hinj` is empty and the
  statement says that an equal skipless network has `2d` units in every block; true by the same
  proof. `L' = 0`: the conclusion is empty, which is right for "every block". `d` empty: the
  conclusion is `0 ≤ …`. `d` of one element: an injective ReLU block of `ℝ` needs two units; and
  `InvarianceOfDomain` for `ℝ` is true.
- Not empty of content: by A Proposition 4.4 (in Lean, `Absorb/Networks.lean`) a residual network
  with reads of rank `d` equals a skipless network, so the hypotheses can hold together. (By
  reading; I did not compile an example.)

**7. Proposition 4.7, the pieces.** (By reading.)

- `Arch.masked π`: block `ℓ` sends `M` to `if π ℓ t j then M t j else 0`; `χ = id`. "Replace
  `ReLU(z)` … by `z` where `π` says active and by `0` where it says inactive."
- `reluPattern S θ x ℓ t j = decide (0 < (hidden … S θ x ℓ.castSucc * θ.read ℓ) t j)`: "active if
  its argument there is positive, and inactive otherwise". An argument `0` is labelled inactive,
  as in the paper.
- `maskedBatch S X π θ = fun i => eval (Arch.masked (π i)) S (θ.toMasked (π i)) (X i)`: one
  pattern per input, the same weights for all inputs. The paper's `F^π_Z`.
- The rank bound for the skipless network: `rank D F'^π_Z(θ) + ((L+1) d² + s') ≤ P'` at every
  `θ`, with `P'` and `s'` the number of weights and of hidden units of the skipless network. The
  paper writes `P' = P + 2 d n`, `s' = s + n`: the same bound. Hypotheses: `[Nonempty d]`,
  `d_in ≥ d`, every block of at least `d` units; the paper uses the same ("`E` and every write have
  rank `d_model` and no read of a unit vanishes" at generic weights).
- The count: `rank ≤ P + 2dn − (L+1)d² − s − n < P − d² − s` if and only if `(2d − 1) n < L d²`.
  Lean's inequality is this one (Check 1).
- `ae_eventually_isFull_smallWrites` has `d ≥ 2` and `d_out ≥ d` because it is S Lemma A.30 for
  ReLU blocks (`ae_exists_eventually_jacobianRank_smallWrites_relu`), which has them: "let `E`
  and `D` have rank `d_model`" needs `d_out ≥ d`, and `d ≥ 2` is needed, as the index says: for
  `d = d_in = d_out = 1`, one block and two hidden units the functions of the network are the maps
  of `ℝ` that are linear on each half-line, a family of dimension `2`, while `P − d² − s = 3`, so
  no such network is full (by hand). Both are in the Scope of
  the absorb paper (`d_in, d_out ≥ d_model ≥ 2`). The clause of `IsFull` on the arguments is
  met because `θ.smallWrites τ` has the reads of `θ`.

**8. The sentence after S Proposition A.33 (`Residual/FoldingDim.lean`).** (By reading.)
`∃ U, IsOpen U ∧ U.Nonempty ∧ (∀ θ ∈ U, Folds θ ℓ.castSucc ∧ UnitInactiveRes θ ℓ.succ j) ∧ ∀ μ
[Haar], ∀ᵐ θ ∂μ, θ ∈ U → funDim … 1 θ + (d² + s + (2d − 1)) ≤ P`, for `d_in ≥ d ≥ 1` and at least
`d` units in block `ℓ.castSucc`.

- `U` is the open set of Proposition A.33 (i) as Lean has it (`exists_isOpen_folds_unitInactiveRes_relu`):
  nonempty, open in the space of all weights, block `ℓ.castSucc` folds and unit `j` of the next
  block is dead on it. The paper has blocks 1 and 2; Lean any two consecutive blocks.
- The bound is for the library's `funDim`, with the amount `2d − 1 ≥ 1`: "below `P − d² − s`".
- Weaker than the paper in one point: at almost every point of `U`, not at every point. The file
  header and the index (line 298) say so. A nonempty open set has positive Haar measure, so the
  statement is not empty.
- For full networks the difference disappears: no point of `U` is full (`Chk5.lean`, compiled:
  the full networks form an open set, and an open set that is null is empty). So the sentence of
  the absorb paper "Not every network is full, since on another open set of weights a unit is
  never active" follows from the library for `d_in ≥ d ≥ 1`, at least two blocks and at least `d`
  units in the first of the two. It is not stated in the library.

---------------------------------------------------------------------------------------------------

## What the authors should know

Nothing false, vacuous or drifted. In order of weight:

1. **Out of date (descriptions, not statements).** Sard's theorem is now also a hypothesis of A
   Proposition 4.7 (`Dimension/RankCriterionOn.lean`, `Absorb/FullNetworks.lean`), and invariance
   of domain of A Proposition 4.6 (`Absorb/InjectiveBlocks.lean`). The header of
   `Literature/Sard.lean` (line 8: "In this library only the step of Lemma A.26 uses it"), the
   index paragraph "Assumed from the literature" (lines 176–182) and the last cell of the Sard
   row (line 187) do not say so. Corrections 1 to 3.
2. **A token that sees no token.** Lean's `attnWeights` gives it the zero row, so "each row of
   `P_Γ(h)` is a probability vector" holds only for tokens that see a token. The paper's two masks
   never produce this case, and the theorems ask only that one token sees all. The index row of
   `Network/Attention.lean` does not mention it. Correction 4.
3. **Proposition 4.6 and Proposition 4.7 are proved under a hypothesis from the literature**
   (`InvarianceOfDomain d`; `SardCriticalValues …`). Both are true theorems and neither is an
   axiom, and the index rows say "under invariance of domain" and "given Sard's theorem".
4. **For the paper: Theorem 3.4 and Theorem A.13 hold for every mask in which one token sees all
   tokens**, not only with or without a causal mask; Lean proves them in that form. The paper
   says something close after Theorem 3.4 ("The proof uses only that each row of attention weights
   sums to 1 and is uniform for a zero query").
5. **For the paper: the sentence of Proposition 4.7 in the main text does not say that the
   skipless blocks have at least `d_model` units.** It is in the Scope of Section 2 and the proof
   uses it (Step 2). Lean has it as a written hypothesis (`∀ ℓ, card d ≤ m ℓ`), and the index row
   says "Not stated: skipless blocks with fewer than `d` hidden units".
6. **Lean's Proposition 4.7 asks less than the paper's Scope** in four places: `d ≥ 1` (not `2`),
   nothing on `d_out`, nothing on the widths of the residual network, `L ≥ 0`. Only "full networks
   exist" needs `d ≥ 2` and `d_out ≥ d`.
7. **(ii) of Theorems 3.4 and A.13 is stated row by row** ("for every `x` of norm at most `1`, at
   least `‖x M‖/3`"). It is equivalent to the paper's `‖M‖/3`, but the step "take the largest
   `‖x M‖`" is not in Lean, and no Lean statement mentions a spectral norm. The same holds for the
   condition `‖W_read‖ ‖W_write‖ < 1` (Lipschitz constants).
8. **Not stated in Lean:** A.13 (iii) for `attentionBlock` or for a network `eval (Arch.attention …)`
   of one block; "Not every network is full …" after Proposition 4.7 (it follows, `Chk5.lean`);
   the two sentences after Proposition 4.6 on the open condition and on "exactly `d_model` extra
   units"; Remark A.12; the residual pattern maps of Step 2 (only their use in Step 3).
9. **The sentence after S Proposition A.33 is stated at almost every point** of the open set; the
   paper says "on the open set". The index says so.
10. **A point of use.** Lean does not find by itself that Lebesgue measure on `T → d → ℝ` is an
    additive Haar measure; to apply Theorem 3.4 (i) to `volume` the instance must be given
    (`Chk2.lean`, `volume_haar`, three lines).
11. Four files appeared during the audit and are not covered: `Absorb/AttentionZero.lean` and
    `Absorb/AttentionNetworks.lean` (statements for A Theorem 4.2; 7 `sorry`),
    `Symmetry/AttentionHeads.lean` and `Dimension/UpperBoundAttention.lean` (13 `sorry`). They
    build on `Network/Attention.lean`, so note 1 of Part 2 (a token that sees no token) matters
    for whoever compares them: their statements are "for any mask".

## Corrections for `STATEMENTS.md` (lines of `829f2b1`)

1. Lines 176–182 ("The theorems that take them as hypotheses are the rows of …"): add
   `Dimension/RankCriterionOn.lean` and `Absorb/FullNetworks.lean` (A Proposition 4.7; Sard's
   theorem), and `Residual/Folding.lean` and `Absorb/InjectiveBlocks.lean` (S Proposition A.32 (i),
   (ii); A Proposition 4.6; invariance of domain).
2. Line 187 (Sard's theorem), last cell: after "in Lean only the step of Lemma A.26 uses it" add
   "and Step 4 of the proof of A Proposition 4.7 (`Dimension/RankCriterionOn.lean`,
   `Absorb/FullNetworks.lean`)".
3. The same sentence in the header of `Literature/Sard.lean`, line 8 (a comment in a Lean file,
   not the index).
4. Line 653 (`Network/Attention.lean`): after "over the tokens that a token sees" add "(a token
   that sees no token gets the weights `0`, so its row is not a probability vector; under the
   paper's two masks every token sees itself)".
5. Lines 108–112, "Not yet compared by such a reader": take out `Residual/FoldingDim.lean`,
   `Absorb/InjectiveBlocks.lean`, `Dimension/RankCriterionOn.lean`, `Absorb/PatternMaps.lean`,
   `Absorb/FullNetworks.lean`, `Network/Attention.lean` and `Absorb/AttentionBlock.lean`; keep
   `Absorb/AttentionZero.lean`, `Absorb/AttentionNetworks.lean`, `Symmetry/AttentionHeads.lean`
   and `Dimension/UpperBoundAttention.lean`. Add a sentence: an eleventh
   reader (24 November) compared the seven files with A Propositions 4.6 and 4.7, A Theorems 3.4
   and A.13, equation (4) and the sentence after S Proposition A.33 (report
   `claude/lean-statement-audit-eleventh-2026-11-24.md`): none false, vacuous or drifted; the
   attention statements hold for every mask with a token that sees all tokens; (ii) is stated row
   by row; Proposition 4.7 has the skipless widths `≥ d` of the paper's Scope as a hypothesis.
6. Line 649 (Proposition 4.6): add "at least one token" to the hypotheses, and to "Not stated:
   Remark A.12" add "the sentences after the proposition (the open condition; exactly `d_model`
   extra units by Proposition 4.4)". Optional.
7. Line 652 (Proposition 4.7): add "the widths of the skipless network are `Fin (m ℓ)`; nothing
   is asked of `d_out` or of the widths of the residual network", and "Not stated: 'Not every
   network is full' (it follows from line 298 and the openness of the full networks)". Optional.
8. Line 654 (Theorems 3.4, A.13): add "(iii) is stated for `attnHeads` only". Optional. The
   status "proved" of this row agrees with what I compiled (`Chk4.out`).
9. No correction to lines 298, 650 and 651: they describe the Lean statements correctly.

## What I could not check

- I did not run `lake build`. That the seven files compile with no `sorry` and the three standard
  axioms I saw through the compiled library of `/home/claude/lp/lean`, whose sources were the
  same as those of `lw` when both stood at `67dc08f`. The first six files were compiled there by
  13:23:22 (dates of the compiled files); `AttentionBlock.lean` was rebuilt there at 13:32:11. I did not build
  anything from the sources myself.
- The proofs. I read the statements and definitions, and of the proofs only what fixes the
  meaning of a statement (the open sets, the counts, the use of the two hypotheses from the
  literature). I did not read the new proofs of `AttentionBlock.lean`.
- The equivalences with the spectral norm (note 4 and note 6) and the remark that `IsFull` does
  not depend on the number of tokens: by hand, not in Lean.
- That `InvarianceOfDomain` and `SardCriticalValues` are correct statements of Brouwer's and
  Sard's theorems: I read the two definitions and rely on the seventh (part B) and tenth (part A)
  audits for the comparison with the literature; I read neither article.
- That the hypotheses of Proposition 4.6 can hold together with an equal skipless network: by
  reading (Proposition 4.4), no compiled example.
- `Absorb/AttentionZero.lean`, `Absorb/AttentionNetworks.lean`, `Symmetry/AttentionHeads.lean` and
  `Dimension/UpperBoundAttention.lean`: not compared.
- The numerical checks are in double precision on random draws; they support the hand
  computations and prove nothing.
- The texts `absorb.txt`, `skips.txt` and `dim.txt` against the PDFs.
