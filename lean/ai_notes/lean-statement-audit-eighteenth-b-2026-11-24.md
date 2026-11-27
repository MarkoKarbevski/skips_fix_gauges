STATUS: complete

# Eighteenth audit of Lean statements against the papers, part B: blocks with biases (absorb paper, Appendix C) (24 November 2026)

Reader: an independent reader who did not write the statements. Brief:
`/home/claude/proj_up/audit18b_brief_2026-11-24.md`. I audited statements and definitions, not
proofs. I changed no repository file, ran no `lake build`, made no commit and no push. My files are
in `/home/claude/audit18b/r18/`.

Library: `/home/claude/lw/lean` (branch `lean-wip`).

- **Commit at the start: `bd0ca40ffd26c79d5d23ad03d04376c537ccb0c0` (18:54:48 UTC).**
- **Commits read later:** `85e666a` (18:56:49), `eafb679` (19:05:09), `f097a0e` (19:11:49),
  `7377562` (19:14:00), and at the end **`10ffbbb239e8fa82e1d6fe323dcd57af9949d3fd` (19:15:09
  UTC)**. At 19:21 UTC the head was `f0d3d9b` (19:18:27); between the two the ten files and
  `checks/Axioms.lean` did not change, and the index got one more row at line 837, so from there
  on its line numbers are one higher than those below (the ten rows: 840 to 849; the last note:
  906 to 908).
- **Files with `sorry`.**
  - At `bd0ca40`: `Absorb/ReluSqBiasesCount.lean` (3), `Absorb/ReluSqBiasesLower.lean` (5),
    `Absorb/RotaryBiases.lean` (4). The seven other files had none.
  - At `eafb679`: `Absorb/ReluSqBiasesCount.lean` (3). `ReluSqBiasesLower.lean` had no `sorry`, and
    three of its five theorems rested on the three of `ReluSqBiasesCount.lean`.
  - At `7377562` and `10ffbbb`: none of the ten files.
- **Did a statement change while I read? No.** By a script of mine (`commits_cmp.py`: statement
  text, docstring, `omit` lines and file header of every public name, `bd0ca40` against `10ffbbb`):
  no statement, no docstring and no `omit` line of a public name changed. Two `import` lines were
  added (`ReluSqBiasesLower.lean`, `RotaryBiases.lean`), and `omit [...] in` lines on private
  helpers. The elaborated signatures of all 71 public names, printed at the start and at the end,
  are the same file byte for byte (`Sig.out`, `Sig3.out`).
- The ten files have **71 public names: 12 definitions and 59 theorems** (3 + 15, 0 + 3, 0 + 9,
  4 + 4, 0 + 1, 0 + 13, 1 + 2, 2 + 3, 0 + 5, 2 + 4, as the brief says).
- **At `10ffbbb` all 59 theorems depend on `propext`, `Classical.choice`, `Quot.sound` only** (by
  compiling, `Ax.lean`, `Ax3.out`). At the start 47 did and 12 had `sorryAx`.

Paper: the absorb paper as text (`absorb.txt`; "A"), Appendix C (lines 1671 to 1979), equation (2)
(line 175), Section 3.3 (lines 310 to 345), the Scope (line 211). Line numbers of `STATEMENTS.md`
are those of `10ffbbb`.

How I checked.

- "By reading": every public statement and docstring of the ten files, their headers, the
  definitions they use (`vanillaBlock`, `gatedBlock`, `attnWeights`, `relu`, `reluSq`, `gelu`,
  `silu`, `Nondegenerate`, `ae_nondegenerate`, `ae_not_relu_absorb_of_card_lt`,
  `ae_not_relu_absorb_same_width`), and the paper passages.
- "By a script": scripts of mine on the source texts and on the elaborated signatures
  (`extract.py`, `sig_types.py`, `commits_cmp.py`, with their outputs).
- "By compiling": scratch files of mine, compiled with `lake env lean` from `/home/claude/lp/lean`
  (read only; `/home/claude/lw/lean` has no compiled files of the ten modules). The sources of `lp`
  and `lw` were the same commit each time I compared them, and the compiled files were newer than
  their sources. Files: `Sig.lean` (signatures), `Ax.lean` (axioms), `NonVac.lean` (the generic
  statements applied to a Haar measure), `OneTok.lean` (one token), `Rot.lean` (the rotary matrix),
  `Reindex.lean` (widths in every universe). All compile without error and contain no `sorry`.
- "By a computation": Python scripts (numpy, double precision; one with mpmath at 120 digits):
  `constructions_check.py`, `attention_check.py`, `rotary_span_check.py`, `gated_c8_check.py`,
  `relusq_check.py`, `relusq_check2.py`, each with its `.out`.
- "By hand": a short argument of my own, written where it is used.

**Short answer. Nothing false, nothing vacuous and no drift was found.** Every clause of Theorems
C.1 and C.2, Lemma C.8 and Proposition C.6 has a Lean statement that says what the paper says or
more, and at `10ffbbb` all are proved. What differs is coverage and form:

1. Three sentences of the proofs are stated in a weaker form than the paper's: "gives `n ≥ 2`"
   (ReLU², `M ≠ 0`) and "gives `n ≥ rank M ≥ 1`" (gated, `M ≠ 0`) are stated as "not the same
   width"; Remark C.3's "for generic `θ` fewer [than `rank M`] do not" is stated for invertible `M`
   only.
2. The statement of "Squares, Costs, Dimensions" does not name the paper's set `N`; its sets are
   existential. It contains what the "Conclusion" uses.
3. The index is out of date in three places (it still says that Appendix C is not stated).
4. Section 3.3 of the paper has `T ≥ 2` tokens; the header and the index say "the paper's theorem
   does not state a number of tokens".

---------------------------------------------------------------------------------------------------

## Part 1: the drift checks

### Check 1. The three blocks with biases; the form of every statement

**Verdict: the three definitions are the paper's formulas, term by term. Every statement is about
`∀ x, x M + B_θ(x) = B_{θ′}(x)` (or its negation at some `x`), with `B_{θ′}` of the same kind and
with biases.** (By reading; the types by compiling, `Sig.out`.)

```
def vanillaBlockB (σ : ℝ → ℝ) (Wr : Matrix p m ℝ) (b : m → ℝ) (Ww : Matrix m q ℝ) (c : q → ℝ)
    (x : p → ℝ) : q → ℝ :=
  (fun i => σ ((x ᵥ* Wr) i + b i)) ᵥ* Ww + c
def gatedBlockB (σ : ℝ → ℝ) (Wg : Matrix p m ℝ) (bg : m → ℝ) (Wv : Matrix p m ℝ) (bv : m → ℝ)
    (Ww : Matrix m q ℝ) (c : q → ℝ) (x : p → ℝ) : q → ℝ :=
  (fun j => σ ((x ᵥ* Wg) j + bg j) * ((x ᵥ* Wv) j + bv j)) ᵥ* Ww + c
noncomputable def attentionBlockB … (sees : T → T → Prop) [DecidableRel sees]
    (WQ WK WV : H → Matrix d dh ℝ) (bQ bK bV : H → dh → ℝ) (WO : H → Matrix dh d ℝ) (bO : d → ℝ)
    (h : Matrix T d ℝ) : Matrix T d ℝ :=
  (∑ i, attnWeights sees ((Real.sqrt (Fintype.card dh))⁻¹ •
        ((h * WQ i + Matrix.of fun _ => bQ i) * (h * WK i + Matrix.of fun _ => bK i)ᵀ))
      * (h * WV i + Matrix.of fun _ => bV i) * WO i)
    + Matrix.of fun _ => bO
```

| Paper | Lean | Same? |
|---|---|---|
| `f(x W_read + b) W_write + c` | `σ ((x ᵥ* Wr) i + b i)`, times `Ww`, plus `c` | yes |
| `∑_j σ(x g_j + b^g_j)(x v_j + b^v_j) ŵ_j + c` | the product of `σ ((x ᵥ* Wg) j + bg j)` and `(x ᵥ* Wv) j + bv j`, times `Ww`, plus `c` | yes |
| "a bias row to every query, key and value and to its output" | `Matrix.of fun _ => bQ i` (every row is `b_{Q,i}`: the paper's `1 b_{Q,i}`), the same for `bK`, `bV`, `bO` | yes |
| scores `(h W_Q + 1 b_Q)(h W_K + 1 b_K)^⊤ / √d_h` | `(Real.sqrt (Fintype.card dh))⁻¹ • (… * …ᵀ)` | yes |
| "softmax, row by row, […] with or without a causal mask" | `attnWeights sees`: the softmax over the tokens `s` with `sees t s`, and `0` elsewhere | yes; a token that sees no token gets the row `b_O` (under the paper's masks every token sees itself) |
| `∑_i P_i(h)(h W_{V,i} + 1 b_{V,i}) W_{O,i} + 1 b_O` | the sum over `i` of `P_i * (h * WV i + …) * WO i`, plus `bO` in every row | yes |

- The weights are rectangular in the MLP blocks (`p` inputs, `q` outputs); the paper has
  `p = q = d_model`. One head dimension `dh` for all heads of a block, as in the paper; the two
  blocks of a statement may have different numbers of heads and head dimensions.
- **Form of the statements** (all 59 signatures read):
  - 15 constructions: `∃ θ′ on m ⊕ k, ∀ x, x ᵥ* M + B σ θ x = B σ θ′ x`, the same `σ` on both
    sides.
  - 2 for tanh, 3 for attention: `∃ x, x ᵥ* M + B θ x ≠ B θ′ x` for all `θ`, `θ′` of any widths;
    attention with the same `sees` on both sides ("with the same mask").
  - 3 for the step along rays: the hypothesis is the equation with biases; the conclusion is the
    equation for the ReLU blocks without biases (`vanillaBlock relu`), as the paper says.
  - Lemma C.8 (6 statements) and the ReLU² steps (4): the equation, or its consequence on cells,
    is the hypothesis.
  - 20 statements `ae_…`: `¬ ∃ θ′, ∀ x, … = …` or `∀ θ′, ∃ x, … ≠ …` at almost every `θ`.
  - 3 for rotary embeddings: `∀ h, h * M + B_rot sees ϑ θ h = B_rot sees ϑ θ′ h`, the same mask and
    the same angles on both sides.
- "For `M ≠ 0`": the statements of (ii) and (iii) have `M ≠ 0` (or `IsUnit M.det`); the
  constructions hold for every `M`, also `M = 0`, which is more.

### Check 2. Generic means almost every parameter, for every Haar measure, on the tuples

**Verdict: yes, in all 20 statements `ae_…`; every index type of the tuple is finite in each of
them; the widths `m'` of universe 0 are every width.** (By reading; the finiteness by a script on
the elaborated signatures, `sig_types.out`; two points by compiling.)

- The 20 statements: 6 of `BiasesVanillaLower.lean`, 9 of `GatedBiasesLower.lean`, 5 of
  `ReluSqBiasesLower.lean`. Each has `(μ : Measure (tuple)) [μ.IsAddHaarMeasure]` with `μ` a
  variable, and the conclusion is `∀ᵐ θ ∂μ, …`. None is "there is a parameter" or "on an open
  set". One of them, elaborated:

  ```
  ae_not_relu_absorbB_same_width : ∀ {p : Type u_1} {q : Type u_2} {m : Type u_3} [Fintype p]
    [Fintype m] [Fintype q], 2 ≤ Fintype.card p → ∀ (M : Matrix p q ℝ), M ≠ 0 →
    ∀ (μ : Measure (Matrix p m ℝ × (m → ℝ) × Matrix m q ℝ × (q → ℝ))) [μ.IsAddHaarMeasure],
    ∀ᵐ θ ∂μ, ¬∃ Wr' b' Ww' c', ∀ (x : p → ℝ),
      x ᵥ* M + vanillaBlockB relu θ.1 θ.2.1 θ.2.2.1 θ.2.2.2 x = vanillaBlockB relu Wr' b' Ww' c' x
  ```
- **The tuples.** Vanilla: `Matrix p m ℝ × (m → ℝ) × Matrix m q ℝ × (q → ℝ)`, used as
  `vanillaBlockB σ θ.1 θ.2.1 θ.2.2.1 θ.2.2.2`: `(W_read, b, W_write, c)` in this order. Gated:
  `Matrix p m ℝ × (m → ℝ) × Matrix p m ℝ × (m → ℝ) × Matrix m q ℝ × (q → ℝ)`, used as
  `gatedBlockB σ θ.1 θ.2.1 θ.2.2.1 θ.2.2.2.1 θ.2.2.2.2.1 θ.2.2.2.2.2`:
  `(W_g, b^g, W_v, b^v, W_write, c)`. In `ReluSqBiasesLower.lean`: `sqTarget M θ.1 θ.2.1 θ.2.2.1`
  and `sqForm (θ.1ᵀ i) (θ.2.1 i)`, the read, the bias and the write.
- **Every index type is finite.** For each of the 20 the script lists the type variables of the
  elaborated signature and the instances `Fintype`: `p`, `q`, `m` (or `d`, `m`) all have one. The
  statement that was corrected at 18:39 UTC has `[Fintype q]` now, and no other one lacks it.
  (Why it matters, by hand, a sketch: for `q` infinite, the measure on the tuples that is `0` on
  the sets inside a countable union of compact sets and `∞` on all others is invariant, finite on
  compact sets and positive on open sets. Whether a block absorbs does not depend on its output
  bias `c ∈ ℝ^q`, so the set of the blocks that absorb, if it is not empty, is not null for this
  measure.)
- **Not vacuous.** By compiling (`NonVac.lean`): for 2 inputs and 3 hidden units there is an
  additive Haar measure on both kinds of tuple (`Measure.addHaar`), and
  `ae_relu_absorbB_add_card`, `ae_swiglu_absorbB_add_card`, `ae_not_geglu_absorbB_same_width`,
  `ae_not_reluSq_absorbB_same_width` apply to it with `M = 1`; for one input
  `ae_reluSq_absorbB_add_card` applies.
- **The widths `m'`.** Eleven statements have `∀ (m' : Type) [Fintype m'], Fintype.card m' < … →`
  inside `∀ᵐ θ`. So the null set does not depend on `m'` or on `θ′`, which is the paper's "for
  generic `θ` no block". Every width `n` is the type `Fin n` of universe 0. For a type of another
  universe, by compiling (`Reindex.lean`): renaming the hidden units does not change a block
  (`vanillaBlockB_reindex_r18`), so the statement for types of universe 0 gives the statement for
  finite types of every universe (`all_universes_r18`, for vanilla blocks; the gated case is the
  same argument and I did not compile it).

### Check 3. Theorem C.1 (i), Remark C.3 and the upper bounds of Theorem C.2

**Verdict: the numbers of new units are the paper's, each as an index type; the statements that
hold at every `θ` and those that ask a read of rank `d` are split as in Remark C.3.** (By reading;
each construction by a computation, `constructions_check.out`.)

| Paper | Lean statement | New units | Asks |
|---|---|---|---|
| "So `rank M ≤ d_model` units add `x M`" (gated), with `d` units | `exists_gatedBlockB_add_linear` | `m ⊕ p` | `σ 1 ≠ 0`; every `θ` |
| Remark C.3: "Every gated block absorbs `x M` with `rank M` more units" | `exists_gatedBlockB_add_linear_rank` | `m ⊕ Fin M.rank` | `σ 1 ≠ 0`; every `θ` |
| "`2 d_model` new units add `x M`" (ReLU, GELU) | `exists_vanillaBlockB_add_linear` | `m ⊕ (p ⊕ p)` | `∀ z, σ z - σ (-z) = z`; every `θ` |
| "If the read has rank `d_model` […] with `d_model` new units" | `exists_vanillaBlockB_add_linear_of_rank` | `m ⊕ p` | the same, and `Wr.rank = Fintype.card p` |
| "`4 d_model` new units add `x M`" (ReLU²) | `exists_vanillaBlockB_add_linear_reluSq` | `m ⊕ (p × Fin 4)` | every `θ` |
| "`3 d_model` new units" | `exists_vanillaBlockB_add_linear_reluSq_of_rank` | `m ⊕ (p × Fin 3)` | `Wr.rank = Fintype.card p` |

- By name: `…_reglu`, `…_swiglu`, `…_geglu` (`d` more units, with `relu 1 = 1`, `silu 1 > 0`,
  `gelu 1 = Φ(1) > 0` proved inside), `…_relu`, `…_gelu` (`2d`), `…_relu_of_rank`,
  `…_gelu_of_rank` (`d`). The form with `rank M` units has no named copies; it applies to the three
  gates through `σ 1 ≠ 0`.
- **Computation.** Each construction written unit by unit as in the Lean proof, 3 inputs, 2
  outputs, 4 hidden units, 400 random inputs: the largest difference of the two sides is at most
  `2.9 × 10⁻¹³` for all 12 cases (gated with ReLU, SiLU, GELU, `d` and `rank M` units; ReLU and
  GELU, `2d` and `d` units; ReLU², `4d` and `3d` units). Controls differ by `14.7` (a gate with
  `σ(1) = 0`) and `8.3` (tanh in the recipe with `2d` units).
- Theorem C.2's upper bounds use these: (i) at every `θ`; (ii) and (iii) at the `θ` whose read has
  rank `d`, which is almost every `θ` when the block has at least `d` hidden units (`hm` in
  `ae_relu_absorbB_add_card`, `ae_gelu_absorbB_add_card`, `ae_reluSq_absorbB_add_card`).
- Not stated: "Each construction keeps the units of `B_θ`, changes some of their writes and the
  output bias, and adds units". The statements give a block on `m ⊕ k`, not that its first `m`
  units are the old ones. The theorems do not need it.

### Check 4. Theorem C.1 (ii)

**Verdict: tanh is stated for every bounded activation and all widths. For attention the
hypothesis "some token sees another token" holds for both masks of the paper on `T ≥ 2` tokens,
which is the paper's own setting (Section 3.3). The remark for the authors is right.** (By reading;
the remark by compiling and by a computation; the odd mask by hand and by a computation.)

```
theorem forall_exists_ne_vanillaBlockB_of_bounded {σ : ℝ → ℝ} (hσ : ∃ C : ℝ, ∀ z, |σ z| ≤ C)
    (Wr : Matrix p m ℝ) (b : m → ℝ) (Ww : Matrix m q ℝ) (c : q → ℝ) (Wr' : Matrix p m' ℝ)
    (b' : m' → ℝ) (Ww' : Matrix m' q ℝ) (c' : q → ℝ) (M : Matrix p q ℝ) (hM : M ≠ 0) :
    ∃ x : p → ℝ, x ᵥ* M + vanillaBlockB σ Wr b Ww c x ≠ vanillaBlockB σ Wr' b' Ww' c' x
theorem forall_exists_ne_attentionBlockB … (sees : T → T → Prop) [DecidableRel sees]
    (hsees : ∃ t₁ t₂, t₁ ≠ t₂ ∧ sees t₂ t₁) … (M : Matrix d d ℝ) (hM : M ≠ 0) :
    ∃ h : Matrix T d ℝ, h * M + attentionBlockB sees WQ WK WV bQ bK bV WO bO h
      ≠ attentionBlockB sees WQ' WK' WV' bQ' bK' bV' WO' bO' h
```

- tanh: `m` and `m'` are any finite types ("at any width"); `forall_exists_ne_vanillaBlockB_tanh`
  is the case `Real.tanh`.
- Attention, the number of tokens. The theorem in Appendix C states none, and "attention block as
  above" is the block of Section 3.3: "The block maps `h ∈ ℝ^{T × d_model}`, whose rows are the
  `T ≥ 2` tokens". With `T ≥ 2`, without a mask every token sees every other one, and with the
  causal mask the second token sees the first. So `hsees` is what the paper has, and Lean allows
  any other mask with one such pair. The two named forms ask `2 ≤ Fintype.card T` and `2 ≤ n`.
- **One token.** By compiling (`OneTok.lean`): with one token that sees itself the weights are the
  `1 × 1` identity, `attentionBlockB … h = h * (∑ i, WV i * WO i) + constants`, and
  `h * M + B_θ(h) = B_{θ′}(h)` holds as soon as `∑ W_V′ W_O′ = ∑ W_V W_O + M` and the constants
  agree. By a computation: this is reached with `⌈rank M / d_h⌉` more heads (difference
  `8.9 × 10⁻¹⁵`). By hand: it is also reached with the same heads when `H d_h ≥ d`. So on one token
  parts (ii) and (iii) of Theorem C.1 both fail for attention, and `T ≥ 2` is needed. The remark in
  the header and in the index is right in content; it could say that Section 3.3 has `T ≥ 2`.
- **A mask in which one token sees another and all other tokens see nothing.** The Lean statement
  is true for it (it is proved for every mask with `hsees`). By hand: a token that sees nothing has
  the output row `b_O`, and the equation in its row is `h_t M + b_O = b_O′` for all `h`, so
  `M = 0`; the token `t₂` that sees `t₁` only has the row `h_{t₁} C + κ`, and the equation in its
  row is `h_{t₂} M + h_{t₁} C + κ = h_{t₁} C′ + κ′`, so `M = 0`. By a computation (3 tokens): the
  rows are these, difference `7.1 × 10⁻¹⁵`.

### Check 5. Theorem C.2 (ii) and Theorem C.1 (iii) for ReLU and GELU

**Verdict: the statements are the paper's; the step along rays and the lower bound are more
general than the paper's.** (By reading; the hypotheses against the Scope by reading.)

```
theorem relu_absorb_of_vanillaBlockB_absorb {σ : ℝ → ℝ} (hσ : ∃ κ : ℝ, ∀ z, |σ z - relu z| ≤ κ) …
    (h : ∀ x : p → ℝ, x ᵥ* M + vanillaBlockB σ Wr b Ww c x = vanillaBlockB σ Wr' b' Ww' c' x) :
    ∀ x : p → ℝ, x ᵥ* M + vanillaBlock relu Wr Ww x = vanillaBlock relu Wr' Ww' x
theorem ae_not_relu_absorbB_of_card_lt (hd : 2 ≤ Fintype.card d) (M : Matrix d d ℝ)
    (hM : IsUnit M.det) (μ : …) [μ.IsAddHaarMeasure] :
    ∀ᵐ θ ∂μ, ∀ (m' : Type) [Fintype m'], Fintype.card m' < Fintype.card m + Fintype.card d →
      ∀ (Wr' : Matrix d m' ℝ) (b' : m' → ℝ) (Ww' : Matrix m' d ℝ) (c' : d → ℝ),
        ∃ x : d → ℝ, x ᵥ* M + vanillaBlockB relu θ.1 θ.2.1 θ.2.2.1 θ.2.2.2 x
          ≠ vanillaBlockB relu Wr' b' Ww' c' x
```

- **The step along rays for "an activation at a bounded distance from ReLU".** True and proved. By
  hand: `|σ(t y + β) − t ReLU(y)| ≤ κ + |β|` for `t > 0`, so the defect of the ReLU equation times
  `t` is bounded, and the defect is `0`. The paper has ReLU (`κ = 0`) and GELU (`κ < 0.17`; Lean
  uses the bound `1`). The widths of the two blocks are any.
- **The lower bound for blocks of every width.** `ae_not_relu_absorbB_of_card_lt` and
  `ae_not_gelu_absorbB_of_card_lt` have no hypothesis `d ≤ m`. The paper's "with at least
  `d_model` hidden units" is needed for the construction only, and
  `ae_relu_absorbB_add_card`, `ae_gelu_absorbB_add_card` have it (`hm`) with both halves. So the
  lower bound is stated for more blocks than the paper's, and Theorem C.2 (ii) itself is the
  paper's.
- **`d ≥ 2`.** `hd : 2 ≤ Fintype.card d`, and `hp : 2 ≤ Fintype.card p` for the same width. This is
  the Scope's `d_model ≥ 2`.
- Theorem C.1 (iii): `ae_not_relu_absorbB_same_width`, `ae_not_gelu_absorbB_same_width`, with
  `M ≠ 0`, rectangular weights and `θ′` on the same index type `m`.
- The order of the quantifiers is the paper's: `M` first, then almost every `θ`.

### Check 6. Lemma C.8

**Verdict: (a) `gateDelta` is `Δ_j`. (b) The hypotheses and the conclusion are the paper's. (c)
ReLU, SiLU and GELU are such gates, and I could not refute the lemma or its two intermediate
identities. (d) The two intermediate statements say what the three parts of the proof say, in
another form.**

```
def NearReLU (σ : ℝ → ℝ) : Prop := ∃ K : ℝ, ∀ z, (1 + |z|) * |σ z - relu z| ≤ K
def gateDelta (Wg : Matrix p m ℝ) (bg : m → ℝ) (Wv : Matrix p m ℝ) (bv : m → ℝ)
    (Ww : Matrix m q ℝ) (j : m) : Matrix p q ℝ :=
  Matrix.of fun a o => (bg j * Wv a j + bv j * Wg a j) * Ww j o
theorem exists_rank_add_card_le_of_gatedBlockB_absorb {σ : ℝ → ℝ} (hσ : NearReLU σ) …
    (hg : ∀ j, Wgᵀ j ≠ 0) (hcol : ∀ i j, i ≠ j → ∀ r : ℝ, Wgᵀ i ≠ r • Wgᵀ j)
    (hv : ∀ j, Wvᵀ j ≠ 0) (hw : ∀ j, Ww j ≠ 0)
    (h : ∀ x : p → ℝ, x ᵥ* M + gatedBlockB σ Wg bg Wv bv Ww c x
      = gatedBlockB σ Wg' bg' Wv' bv' Ww' c' x) :
    ∃ S : Finset m, (M + ∑ i ∈ S, gateDelta Wg bg Wv bv Ww i).rank + Fintype.card m
      ≤ Fintype.card m'
```

**(a)** (By reading.) Entry `(a, o)` is `(b^g_j v_{a,j} + b^v_j g_{a,j}) ŵ_{j,o}`: the column
`b^g_j v_j + b^v_j g_j` times the row `ŵ_j`. This is `Δ_j = (b^g_j v_j + b^v_j g_j) ŵ_j`.

**(b)** (By reading.) Gate reads nonzero (`hg`), pairwise non-collinear (`hcol`, for both orders of
`i`, `j` and every factor `r`), value reads nonzero (`hv`), writes nonzero (`hw`); nothing is asked
of `B_{θ′}`. The paper's conclusion is "`M + ∑_{i∈S} Δ_i` is a sum of at most `n` matrices of rank
one", `n` the number of units that `B_{θ′}` has more. A matrix is a sum of at most `n` matrices of
rank one if and only if `n ≥ 0` and its rank is at most `n`. Lean says
`rank + card m ≤ card m'`, which is `rank ≤ n` and `n ≥ 0` in one. **Same statement.** Lean allows
rectangular weights and `M = 0`.

**(c)** (The three gates: proved in Lean, `nearReLU_relu`, `nearReLU_silu`, `nearReLU_gelu`; by a
computation the largest value of `(1 + |z|) |σ(z) − ReLU(z)|` is `0.72` for SiLU and `0.32` for
GELU. The lemma: proved in Lean for every such gate; my attempts to refute it by a computation,
`gated_c8_check.out`.)

- The paper's expansion has the remainder `o(1/t)`, "exactly for large `t`" for ReLU and
  exponentially small for SiLU and GELU. `NearReLU` asks `O(1/|z|)` only. This is enough: the
  remainder is multiplied by a value of size `O(t)`, and only the coefficients of `t²` and `t` are
  compared. So the Lean lemma is for more gates than the paper's.
- **Absorbing pairs** (3 inputs, 3 outputs; gates ReLU, SiLU, GELU; 9 pairs for each gate):
  - (A) the construction with `rank M = 1, 2, 3` units of gate read `0` and gate bias `1`, and
    with gate bias `0.3`;
  - (B) two units `(g, v, ŵ) = (a, b, w)` and `(b, a, −w)` with any biases: flipping both gates
    (`g → −g`, `b^g → −b^g`) absorbs `M = −(Δ_1 + Δ_2)` at the same width, because
    `σ(z) − σ(−z) = z` and the squares cancel;
  - (C) = (B) with two more units of gate read `0`;
  - (D) four new units on two new hyperplanes, with gate reads `±a`, `±b`;
  - (E) = (B) with a unit of `B_θ` split into two units on its hyperplane;
  - (F) mirror units of two units of `B_θ` (gate reads `−g`), the recipe of the vanilla blocks.
- **Result, 27 pairs.** Each absorbs (difference at most `3.4 × 10⁻¹³`). At every random input off
  the hyperplanes: `M + Λ_θ(x) = Λ_{θ′}(x)` to `1.8 × 10⁻¹⁵` and `Q_θ(x, y) = Q_{θ′}(x, y)` to
  `1.1 × 10⁻¹⁴`, with `gateLinear` and `gateQuadratic` written as in Lean. The conclusion holds in
  each: the smallest rank of `M + ∑_{i∈S} Δ_i` over all `S`, plus `m`, is at most `m′`, with
  equality in (A), (B), (C). In (B), (C), (E) the set is `S = {1, 2}`, the two flipped units.
- Controls: a pair that does not absorb fails the first identity (`2.3`). A block `B_θ` with
  collinear gate reads (`±a`, `±b`) is absorbed by a block with 4 units fewer, and the conclusion
  fails there (`rank + m = 5 > m′ = 1`): the hypothesis "pairwise non-collinear" is needed, and the
  statements have it.

**(d)** (By reading.)

```
theorem gateLinear_gateQuadratic_of_gatedBlockB_absorb {σ : ℝ → ℝ} (hσ : NearReLU σ) …
    (h : ∀ x : p → ℝ, x ᵥ* M + gatedBlockB σ Wg bg Wv bv Ww c x = gatedBlockB σ Wg' bg' Wv' bv' Ww' c' x)
    (x : p → ℝ) (hx : ∀ j, (x ᵥ* Wg) j = 0 → Wgᵀ j = 0) (hx' : ∀ j, (x ᵥ* Wg') j = 0 → Wg'ᵀ j = 0) :
    M + gateLinear σ Wg bg Wv bv Ww x = gateLinear σ Wg' bg' Wv' bv' Ww' x ∧
      ∀ y : p → ℝ, gateQuadratic Wg Wv Ww x y = gateQuadratic Wg' Wv' Ww' x y
```

| Paper | Lean |
|---|---|
| "Expansion along rays": a unit off its hyperplane contributes `t² ReLU(s xν)(xv) η ŵ + t(ReLU(s xν) η b^v ŵ + [s xν > 0](xv) b^g ŵ) + O(1)`; a unit with gate read `0` contributes `t σ(b^g)(xv) ŵ + O(1)` | a unit whose gate is open at `x` (`0 < (x ᵥ* Wg) j`) contributes `t² (x g_j)(x v_j) ŵ_j + t x Δ_j`, a closed one nothing: the same terms, since `x g_j = η s xν` and `x Δ_j = (b^g_j (x v_j) + b^v_j (x g_j)) ŵ_j`. The term of gate read `0` is the second sum of `gateLinear` |
| the two identities, sums over the hyperplanes, at each `x` off the hyperplanes | `M + Λ_θ(x) = Λ_{θ′}(x)` as matrices and `Q_θ(x, y) = Q_{θ′}(x, y)` for all `y`: the paper's identities on the cell of `x`, with the factor `x` taken off (the set of open gates is constant near `x`) |
| "One hyperplane at a time": `Δ_H = G_− − ν a_− = G_+ + ν a_+`; "`A_+ + A_− = 0`" | in the proof of the count: two inputs on the two sides of the hyperplane of unit `i`; the difference of the first identity gives `Δ_i = ∑_{J_i^+} Δ′_j − ∑_{J_i^−} Δ′_j`, the difference of the second gives that `B_{θ′}` has a unit on the hyperplane |
| "Counting": `S` the units `i` for which `J^+` is empty | the same `S` (the units with no unit of `B_{θ′}` whose gate read is a positive multiple of `g_i`) |

The statement of the count (`exists_rank_add_card_le_of_gateLinear_gateQuadratic`) takes the two
identities at every `x` off the hyperplanes as its hypothesis `hcell` and has the conclusion of the
lemma; its `σ` is any function. The hypothesis `hcell` has the form of the conclusion of the first
statement (with `hg`, "off the hyperplanes of `B_θ`" is `∀ j, (x ᵥ* Wg) j ≠ 0`). Faithful.

### Check 7. Theorem C.2 (i) and Theorem C.1 (iii) for gated blocks

**Verdict: the hypotheses are the paper's.** (By reading.)

```
theorem ae_reglu_absorbB_add_card (hd : 2 ≤ Fintype.card d) (M : Matrix d d ℝ) (hM : IsUnit M.det)
    (μ : Measure (Matrix d m ℝ × (m → ℝ) × Matrix d m ℝ × (m → ℝ) × Matrix m d ℝ × (d → ℝ)))
    [μ.IsAddHaarMeasure] :
    ∀ᵐ θ ∂μ, (∃ Wg' … on m ⊕ d, ∀ x, x ᵥ* M + gatedBlockB relu θ… x = gatedBlockB relu … x) ∧
      ∀ (m' : Type) [Fintype m'], Fintype.card m' < Fintype.card m + Fintype.card d → ∀ θ′, ∃ x, … ≠ …
theorem ae_not_reglu_absorbB_same_width (hp : 2 ≤ Fintype.card p) (M : Matrix p q ℝ) (hM : M ≠ 0) …
```

- Theorem C.2 (i): `M` invertible, almost every `θ`, no condition on the width, `d ≥ 2`; both
  halves in one statement; ReGLU, SwiGLU, GeGLU by name, and one form for every gate with
  `NearReLU σ` and `σ 1 ≠ 0`.
- Theorem C.1 (iii): `M ≠ 0`, `p ≥ 2`, `θ′` on the same index type; the three names and the general
  gate.
- The Scope asks at least `d_model` hidden units of every MLP block. Lean does not, which is more.
- The proof's "a minor of size `rank M` […] gives `n ≥ rank M ≥ 1`" is used with one nonzero entry
  of `M`, which gives `n ≥ 1`. See Check 10.

### Check 8. Theorem C.2 (iii) and Theorem C.1 (iii) for ReLU²

**Verdict: the definitions are the paper's; the statement with `F₁`, `F₂` contains what the
"Conclusion" uses; the generic condition is the paper's for the pairs with `|U| < 2d`, and it is
true; the statements are true for one input.** I judged the eight statements of
`ReluSqBiasesCount.lean` and `ReluSqBiasesLower.lean` by hand and by computations while they were
`sorry`; they were proved at `7377562`.

**(a)** (By reading; by a computation.)

```
noncomputable def reluSqCell (Wr : Matrix p m ℝ) (b : m → ℝ) (Ww : Matrix m q ℝ) (c : q → ℝ)
    (x₀ y : p → ℝ) : q → ℝ :=
  (∑ i, if 0 < (x₀ ᵥ* Wr) i + b i then ((y ᵥ* Wr) i + b i) ^ 2 • Ww i else 0) + c
theorem reluSqCell_eq_of_vanillaBlockB_absorb … (h : ∀ x, x ᵥ* M + vanillaBlockB reluSq Wr b Ww c x
      = vanillaBlockB reluSq Wr' b' Ww' c' x)
    (x₀ : p → ℝ) (hx : ∀ i, (x₀ ᵥ* Wr) i + b i = 0 → Wrᵀ i = 0)
    (hx' : ∀ j, (x₀ ᵥ* Wr') j + b' j = 0 → Wr'ᵀ j = 0) :
    ∀ y : p → ℝ, y ᵥ* M + reluSqCell Wr b Ww c x₀ y = reluSqCell Wr' b' Ww' c' x₀ y
```

The polynomial of the cell of `x₀`: the units whose argument is positive at `x₀`, squared. The
statement is the paper's "By (2), `B_{θ′} − B_θ` is a polynomial", read cell by cell: on the cell
of `x₀` the equation of the blocks is an equation of polynomials, so it holds at every `y`. By a
computation, on 16 absorbing pairs: the identity holds at `y` far from the cell (at most
`1.3 × 10⁻¹¹`).

**(b)** (By reading.) `sqForm ω ω₀ = (Matrix.vecMulVec ω ω, (2 * ω₀) • ω)` is
`φ(ω, ω_0) = (ω ω^⊤, 2 ω_0 ω)`. `sqTarget M Wr b Ww S o = ((0 : Matrix p p ℝ), fun a => M a o) +
∑ i ∈ S, Ww i o • sqForm (Wrᵀ i) (b i)` is `τ_o = (0, M_{:,o}) + ∑_{i∈S} ŵ_{i,o} φ(w_i, b_i)`.

**(c)** (By hand; by a computation, `relusq_check.out`, `relusq_check2.out`.)

```
theorem exists_sqTarget_mem_span_of_reluSqCell … (hr : ∀ i, Wrᵀ i ≠ 0) (hw : ∀ i, Ww i ≠ 0)
    (hH : ∀ i k, i ≠ k → ∀ r : ℝ, ¬ (Wrᵀ i = r • Wrᵀ k ∧ b i = r * b k))
    (hcell : ∀ x₀, (∀ i, (x₀ ᵥ* Wr) i + b i ≠ 0) → (∀ j, (x₀ ᵥ* Wr') j + b' j = 0 → Wr'ᵀ j = 0) →
      ∀ y, y ᵥ* M + reluSqCell Wr b Ww c x₀ y = reluSqCell Wr' b' Ww' c' x₀ y) :
    ∃ (S U : Finset m) (F₁ F₂ : Finset m'), Disjoint S U ∧ Disjoint F₁ F₂ ∧
      Fintype.card m + U.card + F₁.card + F₂.card ≤ Fintype.card m' ∧
      ∀ o : q, sqTarget M Wr b Ww S o ∈ span (φ of U) ⊔ span (φ of F₁) ∧
               sqTarget M Wr b Ww S o ∈ span (φ of U) ⊔ span (φ of F₂)
```

- **Does it contain the paper's claims?** The paper: `n ≥ |U| + 2|N|`, and the `τ_o` and
  `φ(w_i, b_i)`, `i ∈ U`, lie in the span of `|U| + |N|` vectors. Lean: `n ≥ |U| + |F₁| + |F₂|`, and
  every `τ_o` lies in the span of the `|U| + |F₁|` vectors and in the span of the `|U| + |F₂|`
  vectors. With `N′ = min(|F₁|, |F₂|)` this is `n ≥ |U| + 2N′` and "in the span of `|U| + N′`
  vectors": the paper's two claims with `N′` in the place of `|N|`. **This is what the "Conclusion"
  uses. The statement does not say that `S`, `U` are the paper's sets or that `N′ = |N|`:** the four
  sets are existential.
- **The paper's argument gives it** (by hand). With the paper's `S`, `U`, `N`: every hyperplane of
  `N` has a unit of `B_{θ′}` on each side (`μ_+ = μ_− ≠ 0` and no unit of `B_θ` on it). Let `F₁` be
  the units of `B_{θ′}` on the hyperplanes of `N` on one side and `F₂` those on the other. The
  hyperplane of unit `i` carries at least one unit of `B_{θ′}`, two for `i ∈ U`, and these
  hyperplanes are distinct (`hH`); so `m′ ≥ m + |U| + |F₁| + |F₂|`. `φ(λω, λω_0) = λ² φ(ω, ω_0)`, so
  the `φ` of one unit of each hyperplane of `N` spans the paper's `φ(ω_H, ω_{0,H})`. The step
  `μ_+ = μ_−` follows from `hcell` at two inputs on the two sides of the hyperplane. The argument
  does not need the outputs `q` to be finite, and the statement does not ask it.
- **On the construction with `3d` units** (by hand). The old unit `e(k)` gets `γ_k` and the mirror
  unit `(k, 0)` has the write `γ_k`: `μ = γ_k` on its hyperplane, so `U` is the set of the `d` units
  `e(k)`, and `S = ∅` (for `γ_k ∉ {0, −ŵ}`). The units `(k, 1)`, `(k, 2)` lie on the two sides of the
  hyperplane `x w + b − 1/2 = 0` with `μ = −γ_k`: `|N| = d`, `F₁ = {(k, 1)}`, `F₂ = {(k, 2)}`.
  Count: `3d = |U| + |F₁| + |F₂|`, with equality. Span: `∑_k γ_{k,o} (φ(w, b) − φ(w, b − 1/2)) =
  ∑_k γ_{k,o} (0, w_{e(k)}) = (0, M_{:,o}) = τ_o`.
- **By a computation**, the sets `S`, `U`, `N`, `F₁`, `F₂` read off each pair, `μ_+ = μ_−` tested,
  the count and the two spans tested by ranks: the construction with `3d` units (`d = 1, 2, 3`;
  with one `γ_k = −ŵ_i`, where `|S| = 1`; with `M` of rank 1), the construction with `4d` units
  (`U = ∅`, `|N| = 2d`; also for a block with no unit), the five mirror units of Remark C.3 for
  `d = 2` (`|U| = 5`, `N = ∅`), the same recipe for `d = 1` (two units), and three pairs changed
  without changing the function of `B_{θ′}` (units rescaled or split, units with read `0`, two
  cancelling units on a new hyperplane): 15 pairs, and the pair of (e) below. All hold.

**(d)** (By hand; the condition by a computation and proved in Lean.)

```
theorem ae_linearIndependent_sqTarget (M : Matrix d d ℝ) (hM : IsUnit M.det) (μ : …) [μ.IsAddHaarMeasure] :
    ∀ᵐ θ ∂μ, ∀ S U : Finset m, Disjoint S U → U.card < 2 * Fintype.card d →
      LinearIndependent ℝ (Sum.elim (fun o : d => sqTarget M θ.1 θ.2.1 θ.2.2.1 S o)
        (fun i : U => sqForm (θ.1ᵀ (i : m)) (θ.2.1 i)))
```

- The paper asks, for all disjoint `S`, `U`, a span of dimension at least
  `min(d(d+3)/2, d + |U|)`. For `|U| < 2d`: `d + |U| ≤ 3d − 1 ≤ d(d+3)/2`, because
  `d(d+1)/2 − (2d − 1) = (d − 1)(d − 2)/2 ≥ 0`. So the minimum is `d + |U|` and the paper's
  condition is linear independence of the `d + |U|` vectors: Lean's condition, for these pairs.
  (With equality for `d = 1` and `d = 2`: `|U| < 2d` cannot be replaced by `|U| ≤ 2d`.)
- **The route.** If `|U| ≥ 2d`, the count alone gives `n ≥ |U| ≥ 2d`. If `|U| < 2d`, the `d + |U|`
  independent vectors lie in a span of `|U| + |F₁|` vectors, so `|F₁| ≥ d`, the same for `F₂`, and
  `n ≥ |U| + 2d`. **The conclusion is the paper's `n ≥ 2d`**
  (`card_add_two_mul_card_le_of_reluSqCell`: `Fintype.card m + 2 * Fintype.card q ≤
  Fintype.card m'`, `q` the outputs).
- **The condition is true generically.** By hand: where the writes of `S` vanish, `τ_o =
  (0, M_{:,o})` span the linear parts, and for generic reads up to `d(d+1)/2` of the `w_i w_i^⊤` are
  independent; `|U| ≤ 2d − 1 ≤ d(d+1)/2`. By a computation of mine (random blocks, every pair
  `(S, U)`: `d = 1`, `m = 1, 4`; `d = 2`, `m = 3, 6`; `d = 3`, `m = 7`; `d = 4`, `m = 7`; 5093 pairs):
  the smallest ratio of the singular values is `2.1 × 10⁻⁴`, so all are independent. The coordinator's
  script does the same for other sizes. Proved in Lean at `eafb679`.

**(e)** (By hand; the instance by compiling.) `ae_not_reluSq_absorbB_of_card_lt` and
`ae_reluSq_absorbB_add_card` ask `[Nonempty d]`; `ae_not_reluSq_absorbB_same_width` asks no size.

- **One input (`d = 1`).** The paper's proof holds word for word: the hyperplanes are the points
  `−b_i / w_i`, distinct for generic `θ`; the generic condition holds (`τ` and `φ(w_u, b_u)` are two
  vectors of `ℝ²`, independent where the write of `S` vanishes); the conclusion is `n ≥ 2`. So the
  statements are true for `d = 1`. Without biases all reads are collinear for `d = 1`, which is why
  the other statements need `d ≥ 2`; with biases the points differ.
- By a computation, `d = 1`: the construction with 3 units absorbs; the recipe of Remark C.3 with
  `d(d+3)/2 = 2` mirror units absorbs (`m = 2, 4`). **So for one input the bound `2d = 2` is
  reached, and `3d` is not the least number.** This is outside the paper's Scope (`d ≥ 2`).
- `[Nonempty d]` is needed: with no input and no output all blocks are equal.
- `ae_not_reluSq_absorbB_same_width`: `M ≠ 0` gives an input and an output. With no hidden unit
  the statement says `x M + c ≠ c′` at some `x`: true.
- A block that does absorb at the same width, on a null set (by a computation): `d = 1`, two units
  with `ŵ_1 w_1² + ŵ_2 w_2² = 0`, both replaced by their mirrors with the writes negated. There
  `S` is both units and `τ(S) = 0`: the hypothesis `hG` of `card_lt_card_of_reluSqCell` fails, as it
  must.

**(f)** (By reading.) The paper's last sentence, "For `M ≠ 0` of any rank, the same argument with
`rank M` in place of `d_model` gives `n ≥ 2`", is stated as "not the same width" only:
`card_lt_card_of_reluSqCell` concludes `Fintype.card m < Fintype.card m'` (`n ≥ 1`), and
`ae_not_reluSq_absorbB_same_width` has `θ′` on the index type `m`. **Verdict for the sentence: LEAN
WEAKER. Verdict for Theorem C.1 (iii), which says "of the same width": SAME.** The header and the
index say so.

### Check 9. Proposition C.6

**Verdict: `rotaryPow` is the power of the paper's `R`; the block has the paper's score; the
statement is the proposition, for every mask in which every token sees itself.** (By reading; the
identities by compiling, `Rot.lean`; the proposition by a computation while it was `sorry`; proved
at `eafb679`.)

```
noncomputable def rotaryPow {pl : Type*} [DecidableEq pl] (ϑ : pl → ℝ) (k : ℤ) :
    Matrix (pl × Fin 2) (pl × Fin 2) ℝ :=
  Matrix.of fun x y => if x.1 = y.1 then
      (if x.2 = y.2 then Real.cos (k * ϑ x.1)
        else if x.2 = 0 then -Real.sin (k * ϑ x.1) else Real.sin (k * ϑ x.1)) else 0
theorem exists_attentionBlockRotaryB_add_linear {n : ℕ} … (sees : Fin n → Fin n → Prop)
    [DecidableRel sees] (hsees : ∀ t, sees t t) (ϑ : pl → ℝ) (c₀ : pl)
    (hϑ : ∀ k : ℕ, 0 < k → k < n → ∀ z : ℤ, (k : ℝ) * ϑ c₀ ≠ 2 * Real.pi * z) … (M : Matrix d d ℝ) :
    ∃ (K : Type) (_ : Fintype K),
      Fintype.card K ≤ n ^ 2 * ⌈(M.rank : ℚ) / (Fintype.card (pl × Fin 2) : ℚ)⌉₊ ∧
      ∃ (WQ' WK' WV' : H ⊕ K → …) …, ∀ h : Matrix (Fin n) d ℝ,
        h * M + attentionBlockRotaryB sees ϑ WQ WK WV bQ bK bV WO bO h
          = attentionBlockRotaryB sees ϑ WQ' WK' WV' bQ' bK' bV' WO' bO' h
```

- **`rotaryPow`.** On the plane `c` the block is `[[cos kϑ_c, −sin kϑ_c], [sin kϑ_c, cos kϑ_c]]`:
  the rotation by `k ϑ_c`; the head dimension is `pl × Fin 2`, so `d_h = 2 |pl|` is even. By
  compiling: `rotaryPow ϑ 0 = 1`; `rotaryPow ϑ (k + l) = rotaryPow ϑ k * rotaryPow ϑ l`;
  `rotaryPow ϑ k = rotaryPow ϑ 1 ^ k` for `k = 0, 1, 2, …`; `(rotaryPow ϑ k)ᵀ = rotaryPow ϑ (−k)`;
  `rotaryPow ϑ t * (rotaryPow ϑ s)ᵀ = rotaryPow ϑ (t − s)`; and
  `(q ᵥ* R^t) ⬝ᵥ (k ᵥ* R^s) = (q ᵥ* R^(t−s)) ⬝ᵥ k`: the paper's "the query and the key of the
  token at position `t` are multiplied by `R^t`" gives the score with `R^{t−s}`. The same by a
  computation (`2.5 × 10⁻¹⁶`), and `e R^k e^⊤ = cos(kϑ)` for the unit row `e` of the proof.
- **The score.** `(Real.sqrt (Fintype.card (pl × Fin 2)))⁻¹ * (((h t ᵥ* WQ i + bQ i) ᵥ* rotaryPow ϑ
  ((t : ℤ) - (s : ℤ))) ⬝ᵥ (h s ᵥ* WK i + bK i))`: the paper's
  `(h_t W_Q + b_Q) R^{t−s} (h_s W_K + b_K)^⊤ / √d_h`. The rest of the block is `attentionBlockB`.
- **For the angles `0` it is `attentionBlockB`.** By compiling:
  `attentionBlockRotaryB sees (fun _ => 0) … h = attentionBlockB sees … h` for every mask
  (`attentionBlockRotaryB_zero_r18`). By a computation: `1.4 × 10⁻¹⁴`; with other angles the blocks
  differ by `24`.
- **Positions.** The tokens are `Fin n`, the positions `0, …, n − 1`; only `t − s` enters.
- **The angle.** `hϑ` is "`kϑ ∉ 2πℤ` for `0 < k < T`", for one plane `c₀`. Having `c₀ : pl` makes
  `d_h > 0`.
- **The count.** `K` is a finite type with `card K ≤ n² ⌈rank M / (2|pl|)⌉` (the ceiling of a
  rational number, as a natural number), and the new block has the heads `H ⊕ K`: "at most
  `T² ⌈rank M / d_h⌉` more heads". All `M`, also `M = 0`.
- **The mask.** `hsees : ∀ t, sees t t` holds for both masks of the paper, which are stated by name.
  The proof uses the mask through "Among them, `s = t`" only.
- **By a computation.** The heads of the proof (`W_Q = W_K = 0`, `b_Q = b_K = τ d_h^{1/4} e`,
  value–output products `λ_j M_i`), with `I = ∑ λ_j P_{τ_j}` solved numerically: `T = 1, 2, 3`,
  no mask, the causal mask and a third mask, `d_h = 2, 4`: `h M + B_θ(h) = B_{θ′}(h)` to
  `6 × 10⁻⁹`, with at most `T² ⌈rank M / d_h⌉` new heads. (For `T = 4` double precision did not
  resolve the span: the `λ_j` are of size `10⁸`.) At 120 digits, `T = 2, …, 5`, both masks,
  `ϑ = 1`: the distance of `I` from the span of the `P_τ` is below `10⁻¹¹⁵`. Where the condition
  fails (`ϑ = π`, `T = 3`; `ϑ = 2π/3`, `T = 4`) the distance is `1.0` and `0.71`: the heads of the
  proof do not suffice there.
- `rotary_angle_one (k : ℕ) (hk : 0 < k) (z : ℤ) : (k : ℝ) * 1 ≠ 2 * Real.pi * z`: "`ϑ = 1` […]
  satisfies the condition for every `T`". True because `π` is irrational.

### Check 10. What is not stated of Appendix C; what is covered in full

(By reading the ten files and the index.)

**Covered in full** (a Lean statement that says the paper's clause or more, proved at `10ffbbb`):

| Paper | Lean |
|---|---|
| Theorem C.1 (i), all six kinds | `exists_gatedBlockB_add_linear_reglu`, `…_swiglu`, `…_geglu`, `exists_vanillaBlockB_add_linear_relu`, `…_gelu`, `exists_vanillaBlockB_add_linear_reluSq` |
| Theorem C.1 (ii), tanh | `forall_exists_ne_vanillaBlockB_tanh` |
| Theorem C.1 (ii), attention (`T ≥ 2`) | `forall_exists_ne_attentionBlockB_noMask`, `…_causal` |
| Theorem C.1 (iii) | ReLU, GELU: `ae_not_relu_absorbB_same_width`, `ae_not_gelu_…`; gated: `ae_not_reglu_absorbB_same_width`, `…_swiglu_…`, `…_geglu_…`; ReLU²: `ae_not_reluSq_absorbB_same_width`; tanh and attention: the case of equal widths of (ii), at every `θ` (no statement of its own; the index says so) |
| Theorem C.2 (i) | `ae_reglu_absorbB_add_card`, `ae_swiglu_…`, `ae_geglu_…` |
| Theorem C.2 (ii) | `ae_relu_absorbB_add_card`, `ae_gelu_absorbB_add_card` |
| Theorem C.2 (iii) | `ae_reluSq_absorbB_add_card` |
| Lemma C.8 | `exists_rank_add_card_le_of_reglu_absorbB`, `…_swiglu_…`, `…_geglu_…` |
| Proposition C.6, and "`ϑ = 1` […] for every `T`" | `exists_attentionBlockRotaryB_add_linear_noMask`, `…_causal`, `rotary_angle_one` |
| Remark C.3, sentences 1 (first half), 2 and 3 | the six constructions of Check 3 |

**Not stated:**

1. Remark C.3, last sentence: the construction with `d(d+3)/2` units for almost every ReLU² block.
   The header of `BiasesConstructions.lean` and the index say so.
2. **Remark C.3, first sentence, second half: "and for generic `θ` fewer [than `rank M`] do not".**
   Stated for `M` invertible (fewer than `d`: `ae_not_gatedBlockB_absorb_of_card_lt`) and for
   `M ≠ 0` as "not the same width". For `1 < rank M < d` the bound `n ≥ rank M` is not stated. The
   index does not say this.
3. The proofs' "gives `n ≥ rank M ≥ 1`" (gated) and "gives `n ≥ 2`" (ReLU²) for `M ≠ 0`: stated as
   `n ≥ 1`. The index says it for ReLU².
4. Remark C.4 (bounded sets of inputs) and Remark C.5 (networks). The index says so.
5. **Remark C.7** (`J ≤ T² − T + 1`; shorter sequences; a block that absorbs at the same width).
   The index does not name it.
6. The sentence after Proposition C.6: "every residual network of such blocks equals a skipless
   network with `T² ⌈d_model / d_h⌉` more heads per block".
7. Table 2's entry "unknown" and the open questions: nothing to state.

**Is the index honest about it?** The ten rows say rightly what each file states. Three places are
out of date and say that stated things are not stated (corrections 1, 6, 7 below).

---------------------------------------------------------------------------------------------------

## Part 2: the statements, file by file

Verdicts: SAME, LEAN STRONGER, LEAN WEAKER, DIFFERENT, PART, FALSE. All 59 theorems are proved at
`10ffbbb` (no `sorry`, three standard axioms). **None is FALSE.**

### `Absorb/BiasesConstructions.lean` (3 definitions, 15 theorems)

| Name | Paper | Verdict |
|---|---|---|
| `vanillaBlockB`, `gatedBlockB`, `attentionBlockB` | "Blocks with biases" | SAME (rectangular weights; a mask is a relation) |
| `exists_gatedBlockB_add_linear` | proof of C.1 (i), "Gated", with `d` units; upper bound of C.2 (i) | LEAN STRONGER (every `σ` with `σ(1) ≠ 0`; every `M`) |
| `exists_gatedBlockB_add_linear_rank` | Remark C.3, "with `rank M` more units" | LEAN STRONGER (the same) |
| `exists_vanillaBlockB_add_linear` | "`2 d_model` new units add `x M`" | LEAN STRONGER (every `σ` with `σ(z) − σ(−z) = z`) |
| `exists_vanillaBlockB_add_linear_of_rank` | "with `d_model` new units"; upper bound of C.2 (ii) | LEAN STRONGER (the same) |
| `exists_vanillaBlockB_add_linear_reluSq` | "`4 d_model` new units" | SAME |
| `exists_vanillaBlockB_add_linear_reluSq_of_rank` | "`3 d_model` new units"; upper bound of C.2 (iii) | SAME |
| `exists_gatedBlockB_add_linear_reglu`, `…_swiglu`, `…_geglu` | C.1 (i) for the three gated kinds; upper half of C.2 (i) | SAME |
| `exists_vanillaBlockB_add_linear_relu`, `…_gelu` | C.1 (i) for ReLU, GELU; Remark C.3 | SAME |
| `exists_vanillaBlockB_add_linear_relu_of_rank`, `…_gelu_of_rank` | Remark C.3; upper half of C.2 (ii) | SAME |
| `forall_exists_ne_vanillaBlockB_of_bounded` | C.1 (ii), tanh: "`B_{θ′} − B_θ` is bounded, and `x M` is not" | LEAN STRONGER (every bounded activation) |
| `forall_exists_ne_vanillaBlockB_tanh` | C.1 (ii), tanh | SAME |

Notes: Checks 1, 3, 4. The docstrings are right against the statements (all 18 read).

### `Absorb/BiasesAttention.lean` (3 theorems)

| Name | Paper | Verdict |
|---|---|---|
| `forall_exists_ne_attentionBlockB` | C.1 (ii), attention | LEAN STRONGER (every mask in which some token sees another token) |
| `forall_exists_ne_attentionBlockB_noMask`, `…_causal` | C.1 (ii), attention, "with or without a causal mask" | SAME (`T ≥ 2` is Section 3.3's) |

Notes: Check 4. The header says "the paper's theorem does not state a number of tokens"; Section
3.3 has `T ≥ 2`.

### `Absorb/BiasesVanillaLower.lean` (9 theorems)

| Name | Paper | Verdict |
|---|---|---|
| `relu_absorb_of_vanillaBlockB_absorb` | proof of C.2 (ii): "Put `t x` into (2), divide by `t`, and let `t → ∞`" | LEAN STRONGER (every activation at a bounded distance from ReLU) |
| `relu_absorb_of_vanillaBlockB_relu_absorb`, `…_gelu_absorb` | the same, ReLU and GELU | SAME |
| `ae_not_relu_absorbB_same_width`, `ae_not_gelu_absorbB_same_width` | C.1 (iii) for ReLU, GELU | SAME (rectangular; `p ≥ 2` is the Scope's) |
| `ae_not_relu_absorbB_of_card_lt`, `ae_not_gelu_absorbB_of_card_lt` | C.2 (ii), "and not with fewer" | LEAN STRONGER (blocks of every width) |
| `ae_relu_absorbB_add_card`, `ae_gelu_absorbB_add_card` | C.2 (ii) | SAME |

Notes: Checks 2, 5.

### `Absorb/GatedBiasesCells.lean` (4 definitions, 4 theorems)

| Name | Paper | Verdict |
|---|---|---|
| `NearReLU` | not a notion of the paper; the remainder of "Expansion along rays" | helper; asks less than the paper's `o(1/t)` |
| `nearReLU_relu`, `nearReLU_silu`, `nearReLU_gelu` | "exactly for large `t` when `σ` is ReLU, and up to terms that decay exponentially in `t` when `σ` is SiLU or GELU" | PART (a bound `O(1/|z|)`, which is what the proof needs; true) |
| `gateDelta` | `Δ_j` | SAME |
| `gateLinear`, `gateQuadratic` | not notions of the paper: the coefficients of `t` and `t²` on a cell | helpers |
| `gateLinear_gateQuadratic_of_gatedBlockB_absorb` | "Expansion along rays", the two identities | DIFFERENT in form, the same content (Check 6 (d)); for more gates |

### `Absorb/GatedBiasesCount.lean` (1 theorem)

| Name | Paper | Verdict |
|---|---|---|
| `exists_rank_add_card_le_of_gateLinear_gateQuadratic` | "One hyperplane at a time" and "Counting" | DIFFERENT in form, the same content (Check 6 (d)) |

Note: a comment inside the proof (line 204) says "`J_i` of the brief".

### `Absorb/GatedBiasesLower.lean` (13 theorems)

| Name | Paper | Verdict |
|---|---|---|
| `exists_rank_add_card_le_of_gatedBlockB_absorb` | Lemma C.8 | LEAN STRONGER (every gate with `NearReLU`) |
| `exists_rank_add_card_le_of_reglu_absorbB`, `…_swiglu_absorbB`, `…_geglu_absorbB` | Lemma C.8 | SAME (rectangular; `M` any) |
| `ae_not_gatedBlockB_absorb_same_width` | C.1 (iii), gated | LEAN STRONGER (gates) |
| `ae_not_reglu_absorbB_same_width`, `…_swiglu_…`, `…_geglu_…` | C.1 (iii), gated | SAME |
| `ae_not_gatedBlockB_absorb_of_card_lt` | C.2 (i), "and not with fewer" | LEAN STRONGER (gates) |
| `ae_gatedBlockB_absorb_add_card` | C.2 (i) | LEAN STRONGER (gates with `NearReLU σ` and `σ 1 ≠ 0`) |
| `ae_reglu_absorbB_add_card`, `ae_swiglu_…`, `ae_geglu_…` | C.2 (i) | SAME |

Notes: Checks 6, 7. Not stated: `n ≥ rank M` for `M` that is not invertible (Check 10).

### `Absorb/ReluSqBiasesCells.lean` (1 definition, 2 theorems)

| Name | Paper | Verdict |
|---|---|---|
| `reluSqCell` | not a notion of the paper | helper |
| `vanillaBlockB_reluSq_eq_reluSqCell` | none (the block at `x` is the polynomial of the cell of `x`) | PART (bookkeeping; true) |
| `reluSqCell_eq_of_vanillaBlockB_absorb` | "By (2), `B_{θ′} − B_θ` is a polynomial" | DIFFERENT in form, the same content (Check 8 (a)) |

### `Absorb/ReluSqBiasesCount.lean` (2 definitions, 3 theorems)

| Name | Paper | Verdict |
|---|---|---|
| `sqForm`, `sqTarget` | `φ`, `τ_o` | SAME |
| `exists_sqTarget_mem_span_of_reluSqCell` | "Squares", "Costs", "Dimensions" | DIFFERENT: sets `F₁`, `F₂` in the place of `N`, all four sets existential; contains what the "Conclusion" uses (Check 8 (c)) |
| `card_add_two_mul_card_le_of_reluSqCell` | "Conclusion": `n ≥ 2 d_model` | SAME conclusion, under the generic condition for `|U| < 2d` (Check 8 (d)) |
| `card_lt_card_of_reluSqCell` | "For `M ≠ 0` […] gives `n ≥ 2`" | LEAN WEAKER (`n ≥ 1`); it is what C.1 (iii) needs |

Note: the header says of the first statement "so this contains "`τ_o` lies in the span of
`|U| + |N|` vectors", and the count `n ≥ |U| + |F₁| + |F₂|` contains `n ≥ |U| + 2|N|`". This is true
of the sets as the header describes them. The statement does not describe them; it gives the two
claims with `min(|F₁|, |F₂|)` in the place of `|N|`.

### `Absorb/ReluSqBiasesLower.lean` (5 theorems)

| Name | Paper | Verdict |
|---|---|---|
| `ae_exists_sqTarget_ne_zero` | "Genericity", for `M ≠ 0` | PART (the form that the same width needs) |
| `ae_linearIndependent_sqTarget` | "Genericity" | PART: the pairs with `|U| < 2d`, where it is the paper's condition (Check 8 (d)) |
| `ae_not_reluSq_absorbB_same_width` | C.1 (iii), ReLU² | SAME; no `d ≥ 2` asked, which is more than the Scope |
| `ae_not_reluSq_absorbB_of_card_lt` | C.2 (iii), "and not with fewer than `2 d_model`" | LEAN STRONGER (blocks of every width; one input allowed) |
| `ae_reluSq_absorbB_add_card` | C.2 (iii) | SAME; one input allowed |

### `Absorb/RotaryBiases.lean` (2 definitions, 4 theorems)

| Name | Paper | Verdict |
|---|---|---|
| `rotaryPow` | "`R` rotates `d_h/2` coordinate planes by fixed angles", its powers | SAME |
| `attentionBlockRotaryB` | the block with the score `(h_t W_Q + b_Q) R^{t−s} (h_s W_K + b_K)^⊤ / √d_h` | SAME |
| `exists_attentionBlockRotaryB_add_linear` | Proposition C.6 | LEAN STRONGER (every mask in which every token sees itself) |
| `exists_attentionBlockRotaryB_add_linear_noMask`, `…_causal` | Proposition C.6 | SAME |
| `rotary_angle_one` | "`ϑ = 1`, which satisfies the condition for every `T`" | SAME |

### The index rows and `checks/Axioms.lean`

- Every public name is in its row (lines 839 to 848), by its name or by an abbreviation whose
  meaning is clear (`…_swiglu`, `…_geglu`, `…_gelu`, `…_relu_of_rank`, `…_gelu_of_rank`,
  `…_swiglu_absorbB`, `…_geglu_absorbB`). (By a script.)
- At `10ffbbb` all ten rows say "proved", rightly, and all 59 theorems are in
  `checks/Axioms.lean`. (By a script.) At `f097a0e` the rows of the two ReLU² files said "in work"
  and their eight theorems were not in `checks/Axioms.lean`, rightly.
- The rows are right in content. What is out of date: corrections 1, 6, 7.

---------------------------------------------------------------------------------------------------

## What the authors should know

Nothing is false, nothing is vacuous, nothing has drifted. In order of weight:

1. **The index says in three places that Appendix C, or parts of it, are not stated** (line 839,
   lines 199 to 206, lines 905 to 907). They are stated and proved.
2. **Three sentences are stated in a weaker form than the paper's.** "Gives `n ≥ 2`" (ReLU²,
   `M ≠ 0`) and "gives `n ≥ rank M ≥ 1`" (gated, `M ≠ 0`) are "not the same width" in Lean. Remark
   C.3's "for generic `θ` fewer [than `rank M`] do not" is stated for invertible `M` only. Theorems
   C.1 and C.2 do not need more. The index says the first of the three.
3. **`exists_sqTarget_mem_span_of_reluSqCell` does not name the paper's set `N`.** Its sets `S`,
   `U`, `F₁`, `F₂` are existential. It gives the paper's two claims with `min(|F₁|, |F₂|)` in the
   place of `|N|`, which is what the "Conclusion" uses. The header and the row describe the sets
   that the proof takes, not what the statement says.
4. **Attention, the number of tokens.** The paper has it: Section 3.3 defines the block on
   `T ≥ 2` tokens. On one token an attention block with biases is affine and absorbs `h M` with
   more heads (compiled), and at the same width when `H d_h ≥ d` (by hand). So `T ≥ 2` is needed
   for (ii) and for (iii). The header and the row say "the paper's theorem does not state a number
   of tokens".
5. **ReLU² for one input.** The statements allow `d = 1`, and they are true there (the paper's
   proof holds as written). For `d = 1` two more units suffice once the block has two (the recipe
   of Remark C.3, computed), so `2d` is reached and `3d` is not the least number. This is outside
   the Scope; within it the paper's "fewer than `3 d_model` only for `d_model = 2`" stands.
6. **Lean is more general than the paper in five ways:** every bounded activation (tanh); every
   activation with `σ(z) − σ(−z) = z` (ReLU, GELU); every gate with `σ(1) ≠ 0` (constructions);
   every activation at a bounded distance from ReLU (the step along rays); every gate with
   `(1 + |z|) |σ(z) − ReLU(z)|` bounded (Lemma C.8, C.2 (i), C.1 (iii)). Also rectangular weights,
   blocks of every width in the lower bounds, and masks given by a relation.
7. **The hypothesis "pairwise non-collinear" of Lemma C.8 is needed** (a computed example: a block
   with gate reads `±a`, `±b` is absorbed by a block with four units fewer). The statements have
   it.
8. **The condition on the rotary angle.** Where it fails (`ϑ = π` with `T = 3`), the identity is not
   in the span of the position-only attention matrices of the proof (computed). I did not study
   whether the proposition itself fails there.
9. Not stated: the construction with `d(d+3)/2` units, Remarks C.4, C.5, C.7, the sentence on
   residual networks after Proposition C.6.
10. A comment in `GatedBiasesCount.lean` (line 204) refers to "the brief".
11. The branch moved while I read (the files went from 12 `sorry` to none); no statement, docstring
    or `omit` line of a public name changed.

## Corrections for `STATEMENTS.md` (line numbers of `10ffbbb`)

1. Line 839 (the row of `Absorb/BiasesConstructions.lean`). Replace "Not stated: Theorem C.1
   (iii), the lower bounds of Theorem C.2, Lemma C.8, the construction with `d(d+3)/2` units of
   Remark C.3, Remarks C.4 and C.5, Proposition C.6 (rotary embeddings)" by: "Theorem C.1 (iii),
   the lower bounds of Theorem C.2, Lemma C.8 and Proposition C.6: the rows below. Not stated: the
   construction with `d(d+3)/2` units of Remark C.3; of Remark C.3, "for generic `θ` fewer do not"
   for an `M` that is not invertible; Remarks C.4, C.5 and C.7; the sentence on residual networks
   after Proposition C.6". In the same row, "(ReGLU, SwiGLU, GeGLU by name)" belongs to "with `d`
   more units".
2. Line 840 (`Absorb/BiasesAttention.lean`). Replace "The paper's theorem does not state a number
   of tokens: if every token sees itself only (one token, for the paper's masks), the block is
   affine in `h` and absorbs `h M` with more heads" by: "The number of tokens is that of Section
   3.3 (`T ≥ 2`). It is needed: if every token sees itself only (one token, for the paper's
   masks), the block is affine in `h` and absorbs `h M` with more heads, and with the same heads
   when `H d_h ≥ d` (compiled by the eighteenth reader, part B)".
3. Line 844 (`Absorb/GatedBiasesLower.lean`). Add: "Not stated: `n ≥ rank M` for an `M` that is not
   invertible (the proof's "gives `n ≥ rank M ≥ 1`" is used as `n ≥ 1`)".
4. Line 846 (`Absorb/ReluSqBiasesCount.lean`). After "(the paper lists the hyperplanes `N` that
   carry no unit of `B_θ`; a hyperplane of `N` has a unit in `F₁` and one in `F₂`)" add: "the
   statement gives the sets by existence and does not say this; with `N′ = min(|F₁|, |F₂|)` it gives
   `n ≥ |U| + 2N′` and the span of `|U| + N′` vectors, which is what the Conclusion uses".
5. Line 848 (`Absorb/RotaryBiases.lean`). Add: "For the angles `0` the block is `attentionBlockB`,
   and `R^t (R^s)^⊤ = R^{t−s}` (compiled by the eighteenth reader, part B). Not stated: Remark C.7;
   the sentence on residual networks after the proposition".
6. Lines 199 to 206 ("Not yet compared by such a reader"). Take out the ten files of this brief
   (compared at `bd0ca40` and `10ffbbb`). A sentence for the paragraph: "An eighteenth reader
   (part B, 24 November) compared the ten files on blocks with biases (12 definitions, 59
   theorems) with Appendix C of the absorb paper: nothing false, vacuous or drifted; generic is
   almost every tuple for every Haar measure, with every index type finite; the statements for
   ReLU² hold for one input; three sentences of the proofs are stated in a weaker form. Report:
   `lean-statement-audit-eighteenth-b-2026-11-24.md` (local copy)."
7. Lines 905 to 907. "Not stated yet: Remarks 5.2, 5.3; Lemmas A.5, A.6; Remarks A.8, A.12; Lemma
   A.14, Proposition A.15; the last sentence of the proof of Theorem 4.2 (rotary embeddings);
   Appendix C (blocks with biases)". Appendix C has the rows at lines 839 to 848; take it out and
   put what Check 10 lists. In the same sentence, Lemmas A.5, A.6 and Lemma A.14, Proposition A.15
   have rows at lines 837 and 838 (outside my brief; I saw the rows and did not compare them).
8. Outside the index. `Absorb/BiasesAttention.lean`, header: "the paper's theorem does not state a
   number of tokens" → add "(Section 3.3 has `T ≥ 2`)". `Absorb/ReluSqBiasesCount.lean`, header:
   after "so this contains […] `n ≥ |U| + 2|N|`" add that the statement gives the sets by existence.
   `Absorb/GatedBiasesCount.lean`, line 204: "of the brief" → "of the proof".

## What I could not check

- **The proofs.** I read none as a proof. "Proved" means no `sorry` in the file at `10ffbbb` and the
  three standard axioms in the build of `/home/claude/lp/lean`.
- **The build.** I did not build the library. I compiled my scratch files against the compiled
  files of `/home/claude/lp/lean`, which were newer than their sources each time; `lp` and `lw`
  were at the same commit when I compared them.
- **The numerical checks** support the reading of the definitions and prove nothing: one random
  draw per case, double precision, small blocks. The search for a counterexample to Lemma C.8 and
  to the ReLU² statements covered the pairs that I could build (constructions, flipped or mirrored
  units, split and rescaled units), not all absorbing pairs.
- **Widths in every universe** for gated blocks and for attention heads: compiled for vanilla
  blocks only; the argument is the same.
- **The same heads on one token** (`H d_h ≥ d`): by hand, from the compiled condition.
- **Whether Proposition C.6 fails where the angle condition fails**, and whether Theorem C.2 (ii)
  holds for one input: not questions of these statements.
- **The paper's condition of "Genericity" for `|U| ≥ 2d`**: Lean does not use it and I did not
  study it.
- **Remarks C.4, C.5, C.7** and the construction with `d(d+3)/2` units against the paper beyond
  the two computed cases (`d = 2` with five units, `d = 1` with two).
- **The older files** on which the ten rest (`Absorb/Block.lean`, `Absorb/SameWidth.lean`,
  `Absorb/FewerUnits.lean`, `Network/Attention.lean`, the activations): I read the definitions and
  statements that I quote and did not compare them with the paper again.
- **The paper itself** beyond the passages that the brief names.

Scratch files: `/home/claude/audit18b/r18/` (`extract.py`, `names.txt`, `sig_types.py`,
`commits_cmp.py`, `constructions_check.py`, `attention_check.py`, `rotary_span_check.py`,
`gated_c8_check.py`, `relusq_check.py`, `relusq_check2.py`, `Sig.lean`, `Ax.lean`, `NonVac.lean`,
`OneTok.lean`, `Rot.lean`, `Reindex.lean`, with their outputs).
