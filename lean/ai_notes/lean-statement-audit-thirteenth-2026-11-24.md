STATUS: complete

# Thirteenth audit of Lean statements against the papers (24 November 2026)

Reader: an independent reader who did not write the statements. Brief:
`/home/claude/proj_up/audit13_brief_2026-11-24.md`. I audited statements and definitions, not
proofs. I changed no repository file, ran no `lake build`, made no commit and no push.

Library: `/home/claude/lw/lean` (branch `lean-wip`). The branch moved several times while I
read (14 commits).

- Commit when I began: `6acdc8c936296ec86d27802929ba0b614d9ec14f` (14:29:10 UTC).
- Commit when I ended: `2d84c1601ec0f0f2b06483e7a3e19f7c3f229892` (14:44:39 UTC).
- Files with `sorry` (lines that are `sorry`, counted by a script over `SkipsLean/`):
  - at `6acdc8c`: `Residual/DepthAttention.lean` (2), `Dimension/ExpOrbitAttention.lean` (2),
    `Dimension/LocalIdentifiabilityAttention.lean` (4);
  - at `8e476d5` (14:37:15): `Dimension/ExpOrbitAttention.lean` (2), and two new files outside the
    brief, `Residual/DepthAttentionRMS.lean` (2), `Residual/DepthAttentionRMSDim.lean` (4);
  - at `2d84c16`: none of the eight files of the brief; only
    `Residual/LocalIdentifiabilityAttentionRMS.lean` (3), a new file outside the brief.
- What changed in the eight files between `6acdc8c` and `2d84c16` (by a script,
  `/home/claude/audit13/cmp_statements.py`, which compares the file headers and, for each of the 25
  public names, the text from the docstring to `:= by`; and by `git diff`): the eight `sorry` were
  replaced by proofs, private helpers were added, and **one public statement changed in form**:
  before `cobExpHeads_zero` a line `omit [Fintype dIn] [Fintype dOut] in` was added, which drops two
  instance arguments that the statement does not use. It asks less and says the same. No other
  statement, docstring, definition or header changed.

So I compared eight statements while they were unproved (the two of `Residual/DepthAttention.lean`,
the two of `Dimension/ExpOrbitAttention.lean`, the four of
`Dimension/LocalIdentifiabilityAttention.lean`) and they were proved while I wrote. What I say "by
hand" about them I worked out before I saw their proofs.

Papers, as text: the absorb paper ("A", `absorb.txt`), the skips paper ("S", `skips.txt`), the
dimension paper ("D", `dim.txt`). Line numbers of `STATEMENTS.md` are those of `2d84c16`; each
correction quotes the words to change.

How I checked.

- "By reading": I read the eight Lean files in full at `6acdc8c`, the definitions they use
  (`Arch.attention`, `attnWeights`, `Params`, `hidden`, `eval`, `Params.smallWrites`,
  `smallWritesLimit`, `Params.cob`, `cobDir`, `cobExp`, `expGL`, `Params.headsQK`,
  `Params.headsVO`, `headDirQK`, `headDirVO`, `exists_mem_orbit_of_eval_eq`), the gated twins of the
  last two files, and the paper passages that the brief names.
- "By hand": a short argument of my own, written in the note.
- "By compiling": scratch files of my own in `/home/claude/audit13/` (`Chk1.lean` to `Chk4.lean`,
  outputs `Chk*.out`), compiled with `lean` 4.36.0 through `LEAN_PATH`, without `lake`, against a
  copy of the compiled library of `/home/claude/lp/lean` taken at 14:35:04 UTC (`lp` then at
  `d140227`, whose sources of the eight files are those of `6acdc8c` except that the two `sorry` of
  `Residual/DepthAttention.lean` are proofs). Later I compiled copies of
  `Dimension/ExpOrbitAttention.lean` and `Dimension/LocalIdentifiabilityAttention.lean` of `1dd4d6c`
  into my copy of the library (11 and 8 seconds, no error, no warning). About ten other compilations
  of 3 to 16 seconds each. I wrote nothing under `lw`, `lp` or the repository.
- "By a computation": Python scripts in `/home/claude/audit13/` (`short_check.py`,
  `depth_check.py`, `orbit_check.py`, outputs `*.out`; numpy in double precision, exact rational
  arithmetic with sympy for the polynomial `Q`, Jacobians in the parameters by the complex step).

**Short answer. Nothing false, vacuous or drifted was found.** Every "generic" of the seven
statements named in the brief is `∀ᵐ θ ∂μ` for every additive Haar measure. All new statements use
the library's `funDim`. No main-text statement has a hypothesis that the paper's Scope does not
imply. The coordinator's claim about absorb Theorem 4.2 (iii) is right: for `T ≤ L` the paper's words
are also met by a residual network whose function is zero. At `2d84c16` all 25 public names of the
eight files are proved; `#print axioms` shows `propext`, `Classical.choice`, `Quot.sound` only for
each of the 20 theorems among them (`Chk1.out`, `Chk3b.out`). Five sentences of the index are out
of date, and the rows of the dimension and skips papers on attention stand under the heading
"Absorb paper" (corrections below).

---------------------------------------------------------------------------------------------------

## Part 1: the drift checks

### Check 1. Generic means almost every parameter, for every Haar measure

**Verdict: yes, in all seven statements. None is "there is a point" or "on an open set".** (By
reading; the elaborated forms by compiling, `Chk1.out`.)

Each has the shape `(μ : Measure (Params (Arch.attention sees id H dh) dIn dOut))
[μ.IsAddHaarMeasure] … : ∀ᵐ θ ∂μ, …`, with `μ` a variable of the statement.

| Statement | The Lean text after the hypotheses |
|---|---|
| `ae_smallWritesGenericAttention` | `∀ᵐ θ ∂μ, SmallWritesGenericAttention θ` |
| `ae_eventually_funDim_smallWrites_attention` | `∀ᵐ θ ∂μ, ∀ᶠ τ in 𝓝[≠] (0 : ℝ), funDim (Arch.attention sees id H dh) 1 (θ.smallWrites τ) + (Fintype.card d ^ 2 + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2) = Module.finrank ℝ (Params …)` |
| `ae_funDim_attention_residual` | `∀ᵐ θ ∂μ, funDim (Arch.attention sees id H dh) 1 θ + (Fintype.card d ^ 2 + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2) = Module.finrank ℝ (Params …)` |
| `ae_funDim_attention_residual_ge_add` | `∀ᵐ θ ∂μ, funDim (Arch.attention sees id H dh) 0 θ + L * Fintype.card d ^ 2 ≤ funDim (Arch.attention sees id H dh) 1 θ` |
| `ae_funDim_attention_residual_of_width` | `∀ᵐ θ ∂μ, funDim (Arch.attention sees id H dh) 1 θ + (Fintype.card d ^ 2 + 2 * L * Fintype.card d ^ 2 / Hn) = Module.finrank ℝ (Params …)` |
| `ae_exists_cob_heads_of_eval_eq_attention_residual` | `∀ᵐ θ ∂μ, ∀ V ∈ 𝓝 (1 : Matrix d d ℝ), ∀ W ∈ 𝓝 (1 : ∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ), ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U, (∀ x, eval … 1 θ' x = eval … 1 θ x) → ∃ (G : GL d ℝ) (K K' : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ), (G : Matrix d d ℝ) ∈ V ∧ … ∈ W ∧ … ∈ W ∧ θ' = ((θ.headsQK K).headsVO K').cob (fun _ => G) (fun _ => G)` |
| `ae_exists_cob_heads_of_eval_eq_attention_oneBlock` | `∀ᵐ θ ∂μ, ∀ V ∈ 𝓝 (1 : Fin 2 → Matrix d d ℝ), ∀ W ∈ 𝓝 1, ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U, (∀ x, eval … 0 θ' x = eval … 0 θ x) → ∃ (G : Fin 2 → GL d ℝ) (K K' …), … ∧ θ' = ((θ.headsQK K).headsVO K').cob G G` |

- **The order in `ae_eventually_funDim_smallWrites_attention`.** It is "for almost every `θ`, there
  is a `δ > 0` (which may depend on `θ`) such that the equality holds for every `τ ≠ 0` with
  `|τ| < δ`". That `∀ᶠ τ in 𝓝[≠] 0, p τ` is `∃ δ > 0, ∀ τ ≠ 0, |τ| < δ → p τ` I compiled
  (`Chk2.lean` (g)). The paper (S Lemma A.27): "For generic parameters `θ` … and a number `τ`, let
  `θ_τ = …`. For all small `τ ≠ 0`, the residual network has `fd(θ_τ) = P − d_model² − s`". Same
  order: first the generic `θ`, then the small `τ`. It is the form of the twelve statements of
  Lemma A.27 for the other kinds of block (index, line 50).
- The statements at one parameter (`smallWritesLimit_eq_zero_attention`,
  `eventually_funDim_smallWrites_attention`, the two `exists_cob_heads_of_eval_eq_…_attention`)
  hold for every `θ` that satisfies written conditions (the structure
  `SmallWritesGenericAttention`; ranks and the value of `fd`). With their `ae_` companions they are
  the generic claims, as for the other kinds of block (sixth audit, Check 1).
- The only "there is a `θ`" are inside proofs: in `ae_funDim_attention_residual`, one `θ₀` and one
  small `τ` at which the rank is reached, from which "almost every" follows by analyticity
  (`ae_funDim_ge`), as in the paper's proof of Theorem 4.7; in `ae_smallWritesGenericAttention`, a
  witness at which a polynomial in the weights is not zero. The existence statement
  `exists_residual_eq_skipless_attention_causal_short` stands for the paper's "some residual
  network", which is not a generic claim.
- That an additive Haar measure on `Params` is a Lebesgue measure: sixth audit, Check 1; I did not
  compile it again.

### Check 2. `funDim` is the library's functional dimension

**Verdict: yes, in every new statement.** (By reading.)

The nine statements that speak of a functional dimension (`eventually_funDim_smallWrites_attention`,
the four of `Residual/DepthAttentionDim.lean`, and the hypothesis `hfd` of the two
`exists_cob_heads_of_eval_eq_…_attention`) use `funDim (Arch.attention sees id H dh) S θ` of
`Dimension/Functional.lean`: the largest rank of the Jacobian in `θ` over all `n` and all batches
`X : Fin n → Matrix T dIn ℝ` (sixth audit, Check 2), with the set of tokens `T` fixed and all real
`T × d_in` inputs. `S = 1` is the residual network, `S = 0` the skipless one; `θ.smallWrites τ` is
`θ` with the writes `τ • θ.write ℓ` (compiled, `Chk2.lean` (h)). Without normalization the network
of attention blocks is differentiable in the parameters at every input (twelfth audit, part B,
Check 2), so no batch drops out and `funDim` is the paper's `fd`.

### Check 3. No extra hypotheses in the main-text statements

**Verdict: none. Every Lean hypothesis is implied by the paper's Scope, and several are weaker.**

**(a) S Theorem 4.7 for attention blocks without normalization.** The Lean text (by compiling,
`Chk1.out`):

```
ae_funDim_attention_residual : ∀ {T d dIn dOut} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d]
  [Fintype dIn] [Fintype dOut] {sees : T → T → Prop} [DecidableRel sees] {H dh : Fin L → Type}
  [(ℓ : Fin L) → Fintype (H ℓ)] [(ℓ : Fin L) → Fintype (dh ℓ)]
  (μ : Measure (Params (Arch.attention sees id H dh) dIn dOut)) [μ.IsAddHaarMeasure],
  2 ≤ Fintype.card d → Fintype.card d ≤ Fintype.card dIn → Fintype.card d ≤ Fintype.card dOut →
  (∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) → (∀ ℓ, 0 < Fintype.card (dh ℓ)) →
  ∀ (t₁ t₂ : T), t₁ ≠ t₂ → sees t₂ t₂ → sees t₂ t₁ →
  ∀ᵐ θ ∂μ, funDim (Arch.attention sees id H dh) 1 θ
      + (Fintype.card d ^ 2 + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
    = Module.finrank ℝ (Params (Arch.attention sees id H dh) dIn dOut)
```

| Paper (S Scope; Theorem 4.7) | Lean | Verdict |
|---|---|---|
| "`d_in, d_out ≥ d_model ≥ 2`" | `hd`, `hdIn`, `hdOut` | same |
| "All attention blocks have the same number `H` of heads, of total width `H d_h = d_model`" | `1 ≤ d_h ≤ d` in every block (`hdh0`, `hdh`); any numbers of heads, which may differ from block to block and may be `0` | Lean asks less: `H d_h = d ≥ 2` gives `H ≥ 1` and `1 ≤ d_h ≤ d` |
| "act on sequences of at least two tokens" (causal or not) | a relation `sees` and two tokens `t₁ ≠ t₂` with `sees t₂ t₂`, `sees t₂ t₁` | Lean asks less; the two masks are instances (compiled for Corollary 4.10 (i), `Chk2.lean` (f)) |
| "at generic parameters its functional dimension is `P − dim 𝒢 − s`", `dim 𝒢 = d²`, `s = 2 H d_h²` per block | `fd + (d² + 2 ∑_ℓ H_ℓ d_{h,ℓ}²) = P` | same |

The statement goes beyond the Scope (heads of total width other than `d`). It is the generality of
the paper's Lemma A.27 ("in any order and of any width … heads of width at most `d_model`"). By a
computation (`depth_check.out`): on nine small networks, among them two with `H d_h < d`, one with
different heads in its two blocks, one with a block that has no head, and both masks, the rank at a
random parameter is `P − d² − s` in every case.

**(b) S Corollary 4.10 (i).** `ae_funDim_attention_residual_of_width` has `hd`, `hdIn`, `hdOut`,
`hHn : ∀ ℓ, Fintype.card (H ℓ) = Hn`, `hHd : ∀ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) =
Fintype.card d`, and the two tokens. These are the Scope's hypotheses, with the mask weaker. The
conclusion has `2 * L * Fintype.card d ^ 2 / Hn`, which Lean reads as `((2 * L) * d²) / Hn` in
natural numbers.

- Is it the paper's `s = 2 L d²/H`? Yes. Is the division exact? Yes (by compiling, `Chk2.lean`
  (c)): for `L = 0` the numerator is `0` and `0 / Hn = 0` for every `Hn` (also `Hn = 0`, which
  `hHn` then does not exclude), and `s = 0` is right; for `L ≥ 1`, `d = Hn · d_h`, so
  `2 L d² = (2 L Hn d_h²) · Hn` and the quotient is `2 L Hn d_h² = 2 ∑_ℓ H d_h²`. For `L ≥ 1`,
  `Hn ≥ 1` follows from `Hn · d_h = d ≥ 2`.

**(c) "The skips raise the functional dimension by at least `L dim 𝒢`".**
`ae_funDim_attention_residual_ge_add` has the hypotheses of (a) and
`hH : ∀ ℓ, Fintype.card d ≤ Fintype.card (H ℓ) * Fintype.card (dh ℓ)`. Where does the paper ask
it? In two places: the Scope ("of total width `H d_h = d_model`"), and the proof of Theorem 4.7,
"The gain. When every block has width at least `d_model`, the functional dimension of the skipless
network is at most `P − (L + 1) dim 𝒢 − s` (Theorem A.17 (ii), Lemma A.18)", where "the width of
an attention block is `H d_h`" (S Theorem B.1). So it is the paper's hypothesis, not an extra one.
The conclusion compares the two networks at the same `θ` (they have the same parameters), for
almost every `θ`. By the computation: in the six cases with `H d_h ≥ d` the difference of the two
ranks is `L d²` exactly; in the two cases with `H d_h < d` it is larger (9 against 8, 24 against
18), so I saw no case in which the hypothesis is needed for the truth of the inequality. The proof
needs it.

**(d) A Theorem 4.2 (iii).** The Lean text (`Chk1.out`):

```
exists_residual_eq_skipless_attention_causal_short : ∀ (n L L' m a b : ℕ), 1 ≤ n →
  n ≤ L ∨ n = L + 1 ∧ L ≤ L' →
  ∃ θ θ', θ.E * θ.D ≠ 0 ∧
    (∀ (X : Matrix (Fin n) (Fin (a + 1)) ℝ),
      eval (Arch.attention (fun t s => s ≤ t) id (fun x => Fin 2) fun x => Fin 1) 1 θ X =
        eval (Arch.attention (fun t s => s ≤ t) id (fun x => Fin 2) fun x => Fin 1) 0 θ' X) ∧
    ∃ X, eval (Arch.attention (fun t s => s ≤ t) id (fun x => Fin 2) fun x => Fin 1) 1 θ X ≠ 0
```

(`θ` has `L` blocks, `θ'` has `L' + 1`; both have the tokens `Fin n`, the model dimension
`Fin (m + 2)`, inputs `Fin (a + 1)`, outputs `Fin (b + 1)`.)

| Paper | Lean | Verdict |
|---|---|---|
| "Without normalization and with a causal mask" | `χ = id`, `sees = fun t s => s ≤ t` on `Fin n`, the same mask and tokens in both networks | same |
| "in every other case, `T ≤ L` or `T = L + 1 ≤ L′`" | `n ≤ L ∨ (n = L + 1 ∧ L ≤ L')`, with the paper's `L′ = L' + 1` | same: `L + 1 ≤ L' + 1` is `L ≤ L'` |
| the complement of the cases of (i) | (i) in `Absorb/AttentionNetworks.lean` has `L + 2 ≤ n ∨ (n = L + 1 ∧ L' + 1 ≤ L)` | exactly the complement: `¬(L + 2 ≤ n ∨ (n = L + 1 ∧ L' + 1 ≤ L)) ↔ (n ≤ L ∨ (n = L + 1 ∧ L ≤ L'))` (compiled, `Chk2.lean` (b), (e)) |
| `T ≥ 2` (A Section 3.3) | `1 ≤ n` | Lean covers more (`n = 1`); for `n = 0` the last clause would be false |
| `L ≥ 1`, `L′ ≥ 1` (A Section 2; the theorem) | `L : ℕ`, the skipless network has `L' + 1 ≥ 1` blocks | Lean covers more (`L = 0`, which the condition allows only with `n = 1`) |
| "some residual network of `L` blocks with `E D ≠ 0` equals a skipless network of `L′` blocks" | `∃ θ θ', θ.E * θ.D ≠ 0 ∧ ∀ X, eval … 1 θ X = eval … 0 θ' X` | same |
| Scope: "`d_in, d_out ≥ d_model ≥ 2`" | every `d = m + 2 ≥ 2`, every `d_in = a + 1 ≥ 1`, every `d_out = b + 1 ≥ 1` | Lean covers every size of the Scope and more; it is not weaker |
| "with any numbers of heads and any head dimensions"; Scope: "all attention blocks of a network have the same number of heads" | two heads of dimension one in every block of both networks | within the Scope. The paper's statement is an existence statement, so one choice of heads suffices. The paper's proof gives more: "two heads of any dimension" |
| — | `∃ X, eval … 1 θ X ≠ 0` | one clause more than the paper (Check 4) |

Every case of the paper is covered. I found no place where the Lean statement is weaker than the
paper's words. A reader who takes (iii) to say "for every number of heads `≥ 2` and every head
dimension" (which the last sentence of the proof supports) will find only the case of two heads of
dimension one in Lean.

### Check 4. The coordinator's claim about `T ≤ L`

**Verdict: the claim is true, and the paper's wording does not exclude the example.**

By hand. Let all queries vanish, so every score is `0` and block `ℓ` is `h ↦ U h V_ℓ`. Let `E`
have the entries `E_11 = E_22 = 1` and zeros elsewhere, and `D` likewise, so `E D ≠ 0` and
`h_0 = X E` satisfies `h_0 Π = h_0`. With `V_ℓ = −ℓ Π` the residual block is
`h ↦ h − ℓ U h Π = (I − ℓ U) h` on such states, and it keeps `h Π = h`. After the first `T` blocks,
`h_T = ∏_{ℓ=1}^{T} (I − ℓ U) · X E`. The matrix `U` is diagonalizable with the eigenvalues `1/t`,
`t = 1, …, T`, and the polynomial `∏_ℓ (1 − ℓ z)` vanishes at each `1/t` (the factor `ℓ = t`), so
the product is the zero matrix. The blocks `ℓ > T` have `V_ℓ = 0` and keep `h = 0`. So the residual
network is the zero function at every input, with `E D ≠ 0`, and it equals every skipless network
that is the zero function (all `V′ = 0`, any `L′`).

By a computation (`short_check.out`, part (A)): in six configurations (`T ≤ L` from `(1, 1)` to
`(4, 4)` and `(3, 5)`, `d` from 2 to 4, two heads of dimension one per block, 200 random inputs
each) the largest output is at most `1.2 · 10⁻¹⁶`.

The paper's wording: "some residual network of `L` blocks with `E D ≠ 0` equals a skipless network
of `L′` blocks". Nothing asks that the common function is not zero; the Scope asks `E D ≠ 0` only.
So for `T ≤ L` the words are met by this pair. The paper's own construction gives more: there
`γ′ = 1` and the common function is `X ↦ U^{L′} X E D`, which is not zero. Lean states this
stronger form (the clause `∃ X, eval … ≠ 0`), and its docstring, the file header and the index row
say so.

For `T = L + 1` there is no such example: by (i) with a skipless network of one block that is the
zero function (`L′ = 1 ≤ L`), a residual network with `E D ≠ 0` is not the zero function (for
`L = 0` it is `X ↦ X E D`). So only the case `T ≤ L` of the paper's sentence has a trivial
instance.

---------------------------------------------------------------------------------------------------

## Part 2: the statements, file by file

### Verdict table

Status at `2d84c16`: all rows proved, three standard axioms. The rows marked † were `sorry` at
`6acdc8c`, when I compared them.

| Paper statement or proof piece | Lean | Verdict | Difference | How checked |
|---|---|---|---|---|
| A proof of 4.2 (iii), equation (10): `Q(z) = 1 + q_1 z + ⋯ + q_L z^L` with `Q(z_t) = γ′ z_t^{L′}`, `z_t = 1/t` | `exists_polynomial_short` | LEAN STRONGER | Same points (`1/(t+1)`, `t : Fin n`), same power (`L' + 1 = L′`), same two cases; `Q` is "degree at most `L`, `Q(0) = 1`". One clause more: `γ ≠ 0`. No `n ≥ 1` is asked | reading; computation |
| A proof of 4.2 (iii): "the real polynomial `Q` is a product of factors `1 + a z` and `1 + 2αz + (α² + β²) z²`" | `exists_complex_factors` | DIFFERENT in form | Over `ℂ`: `Q` is a product of exactly `L` factors `1 + c z`. That the `c` come in conjugate pairs is not stated. Nothing is lost for the theorem (note 1) | reading; by hand |
| A proof of 4.2 (iii): "The matrix `U` is diagonalizable with the eigenvalues `z_t`, so (10) gives `Q(U) = γ′ U^{L′}`" | `aeval_attnWeights_causal_eq_zero` | PART | The consequence that the proof uses: a real polynomial that vanishes at the `n` points vanishes at `U`. "Diagonalizable" is not stated | reading |
| A, after Theorem 4.2: "For `T = 2` … the residual block `h ↦ h − 3 U h` equals the composition `h ↦ −2 U² h` of two skipless blocks" | `one_sub_three_smul_attnWeights_causal_two` | PART | The identity of matrices `I − 3U = −2U²` for the causal `U` on two tokens. The two networks are the case `n = 2`, `L = 1`, `L' = 1` of the theorem (compiled), whose construction gives `Q = 1 − 3z`, `γ′ = −2` (computed) | reading; compiling; computation |
| **A Theorem 4.2 (iii)** | `exists_residual_eq_skipless_attention_causal_short` | LEAN STRONGER | Check 3 (d): every case of the paper; also `n = 1`, `L = 0`, any `d_in, d_out ≥ 1`; one clause more (the function is not zero). The witness has two heads of dimension one | reading; compiling; computation |
| D, S "Reduction": the inputs of equation (8) | `twoTokenInput` | SAME | The row `u` at `t₂`, `u − v` at every other token: the paper's `u = x_2`, `v = x_2 − x_1` | reading |
| D equation (8), for the heads of one block or of all blocks | `attnFamily_two_tokens` | LEAN STRONGER | Any finite family of matrices `B_j`, `C_j`, no network; any mask in which `t₂` sees itself and `t₁`; `k` the number of other tokens that `t₂` sees. No stream term, as in (8) (S (16) has `u K`, `K = M + S`) | reading |
| D, S Step 2 ("two tokens"), as used in the proof of S Lemma A.27 | `attnFamily_rigid` | LEAN STRONGER | For curves of matrices with a linear term `x M(τ)`; "some `v`" at `τ = 0` for "generic `v`"; the conclusion also gives `dM = 0` (S: `D_θ M η = 0`) | reading; by hand |
| S, D: `B_i`, `C_i`, for head `i` of block `ℓ` | `headScore`, `headValue` | SAME | `(√d_h)⁻¹ • (E W_Q W_K^⊤ E^⊤)` and `E W_V W_O D`, the four matrices taken from block `ℓ` | reading |
| S Lemma A.27 and its proof, attention blocks: the conditions on `θ` | `SmallWritesGenericAttention` | SAME | `E`, `D` of rank `d`; the four matrices of every head of rank `d_h`; some `v` for the heads of all blocks together (note 3) | reading; by hand |
| S proof of A.27, "Attention blocks without normalization": the flat directions of `J_0` | `smallWritesLimit_eq_zero_attention` † | SAME | One inclusion (flat implies this form), for networks all of whose blocks are attention blocks. Signs as in the paper (note 4) | by hand; computation |
| S Lemma A.27, first value, attention blocks | `eventually_funDim_smallWrites_attention` †, `ae_eventually_funDim_smallWrites_attention` | PART | Networks of attention blocks only; the lemma also allows MLP blocks among them, which Lean does not state. Within that: same value, same order of `θ` and `τ`, heads may differ from block to block | reading; by hand; computation |
| S Lemma A.27, "For generic parameters" | `ae_smallWritesGenericAttention` | SAME | `d_in, d_out ≥ d ≥ 2`, `1 ≤ d_h ≤ d` (note 5) | reading |
| **S Theorem 4.7**, attention blocks, no normalization: the value | `ae_funDim_attention_residual` | LEAN STRONGER | Check 3 (a) | reading; computation |
| S Theorem 4.7: "the skips raise the functional dimension by at least `L dim 𝒢`" | `ae_funDim_attention_residual_ge_add` | SAME | Check 3 (c). The clause "by exactly `L dim 𝒢` when the skipless network satisfies the equality condition too" is not stated | reading; computation |
| **S Corollary 4.10 (i)** | `ae_funDim_attention_residual_of_width` | SAME | Check 3 (b). Part (ii) is not stated | reading; compiling |
| D proof of 4.6: "the map that sends an element of the group to the image of `θ` under it" | `cobExpHeads`, `cobExpHeads_zero` †, `hasStrictFDerivAt_cobExpHeads` † | PART of the proof; true | In the chart `exp`; the three symmetries in one order (they commute); the derivative at `0` (note 6). "Immersion" is this with the injectivity of `Symmetry/AttentionHeads.lean` | reading; by hand; computation |
| D Proposition 4.6, attention blocks (skipless) | `exists_cob_heads_of_eval_eq_skipless_attention` † | PART | One direction (from the equality condition to local identifiability), at one parameter, without normalization (note 7) | reading; by hand |
| S Proposition 4.5, attention blocks (residual) | `exists_cob_heads_of_eval_eq_residual_attention` † | PART | The same, with one `G` at all hidden states | reading; by hand |
| **S Corollary 4.9**, attention blocks, no normalization | `ae_exists_cob_heads_of_eval_eq_attention_residual` † | LEAN STRONGER | The hypotheses of Check 3 (a), weaker than the Scope. "all close to the identity": for all neighbourhoods `V`, `W`. "The matrix `G` is the same at all hidden states": `cob (fun _ => G) (fun _ => G)` | reading; by hand |
| D Proposition 4.6 with Theorem 5.1, one attention block | `ae_exists_cob_heads_of_eval_eq_attention_oneBlock` † | SAME | The hypotheses of Theorem C.1 (`d_h ≤ d`, `H d_h ≥ d`); not a numbered statement of the paper, a consequence of two | reading; by hand |

### Notes

**1. `Absorb/ShortSequencesPoly.lean`.** (By reading; by hand; the computation where named.)

- `exists_polynomial_short (n L L') (hn : n ≤ L ∨ (n = L + 1 ∧ L ≤ L')) : ∃ Q γ, Q.natDegree ≤ L ∧
  Q.eval 0 = 1 ∧ γ ≠ 0 ∧ ∀ t : Fin n, Q.eval ((t + 1 : ℝ)⁻¹) = γ * ((t + 1 : ℝ)⁻¹) ^ (L' + 1)`.
  The points are `1, 1/2, …, 1/n`; the power is the paper's `L′`. `γ ≠ 0` is true: for `n ≤ L` the
  paper takes `γ′ = 1`; for `n = L + 1`, `γ = 0` would give `Q` of degree at most `L` with `L + 1`
  roots and `Q(0) = 1`. By the computation with exact rationals, for 13 triples `(T, L, L′)`, `γ′`
  is `1` in the first case and `−2, 6, 216/85, −24, 120` in five instances of the second.
- `exists_complex_factors`: is anything lost? As a sentence it says less than the paper's: complex
  linear factors, not real linear and quadratic ones, and it does not say that the non-real `c`
  come in conjugate pairs (they do, since `Q` is real, but that is not in the statement). For the
  theorem nothing is lost. Lean gives block `ℓ` the matrix `V_ℓ = (re c_ℓ) Π + (im c_ℓ) J`
  (`vmat_ssq`, which has the rows `(α, −β)` and `(β, α)`: the paper's `α Π + β J` with
  `J_12 = −1`, `J_21 = 1`). These are the paper's matrices: `a Π` for a real factor, `α Π ± β J` for
  a conjugate pair, `0` for the factors `c = 0` that fill up to `L` (the paper: "`V_ℓ = 0` in its
  other blocks"). The order of the blocks may differ; the matrices commute.
- `aeval_attnWeights_causal_eq_zero`: stated for every `n`, also `n = 0`. Row `t` of `U` is uniform
  on the tokens `s ≤ t` (twelfth audit, part A, Check 3).

**2. `Absorb/ShortSequences.lean`: degenerate cases.** (By hand; the computation, part (B): for 13
triples, among them every case below, the residual and the skipless network of the construction
agree on 100 random inputs to `7 · 10⁻¹³` at outputs of size 2 to 310, and are not zero.)

- `L = 0`: the condition holds only for `n = 1` (`n ≤ 0` contradicts `1 ≤ n`). The residual network
  is `X ↦ X E D`; with one token `U = (1)`, `Q = 1`, `γ = 1`, and the skipless network of `L' + 1`
  blocks with zero scores is `X ↦ X E Π^{L'+1} D = X E D`. True.
- `L' = 0` (one skipless block): allowed when `n ≤ L`, and when `n = 1`, `L = 0`. The case
  `n = L + 1`, `L ≥ 1`, `L' = 0` is excluded (`L ≤ 0` fails); it is a case of (i).
- `n = 1`: outside the paper (`T ≥ 2`). With one token an attention block is `h ↦ h V`, and the
  statement is true.
- `m = 0`: `d = 2`, `Π = I`. `a = 0` or `b = 0`: `d_in = 1` or `d_out = 1`; the construction uses
  the input coordinate `0` only (`E = e_0 e_0^⊤`, row `0` of `D` all ones; the paper has
  `E_11 = E_22 = D_11 = D_22 = 1`, which needs `d_in, d_out ≥ 2`). Any witness serves an existence
  statement.
- Both file headers quote the paper's theorem and proof word for word (compared with `absorb.txt`,
  lines 383–392 and 1407–1449).

**3. `Residual/DepthAttention.lean`: `SmallWritesGenericAttention` against the paper.** (By
reading.) The lemma's hypotheses are "`d_model ≥ 2`, `E` and `D` of rank `d_model`, heads of width
at most `d_model`, at least two tokens, generic `θ`". Its proof for attention blocks uses: the
conditions of Step 2 "for generic parameters and generic `v`" for the heads of all blocks together
(field `exists_v`, over the pairs `⟨ℓ, i⟩ : Σ ℓ, H ℓ`); "As `E` has full column rank and `D` has
full row rank" (`rank_E`, `rank_D`); "as in Step 1 there", which needs the full column rank of
`W_Q`, `W_K`, `W_V` and `W_O^⊤` of every head (`rank_Q`, `rank_K`, `rank_V`, `rank_O`). The ranks
"of the queries of all heads" and "of the output projection" of the one-block theorem are not
asked, and rightly: in `J_0` the matrices `E` and `D` do not move inside the blocks, so Step 1
starts from `ψ_B = E (η_Q W_K^⊤ + W_Q η_K^⊤) E^⊤/√d_h = 0` with `E` fixed. This is why the lemma
holds for heads "of any width". Under the structure every block that has a head has `d_h ≥ 1`
(compiled, `Chk3.lean`), so the structure does not hold by accident in a degenerate case.

**4. `smallWritesLimit_eq_zero_attention`, recomputed by hand for one block and one head.**
`smallWritesLimit` is `(J_0 η)(x) = x (η_E D + E η_D) + (𝐃f(x E R)(x E η_R) W + f(x E R) η_W) D`,
with `R = [W_Q | W_K | W_V]`, `W = W_O`. For an attention block `f(x E R') W' D =
P(x B' x^⊤) x C'` with `B' = E W_Q' W_K'^⊤ E^⊤/√d_h`, `C' = E W_V' W_O' D`. So `(J_0 η)(x)` is the
derivative at `τ = 0` of `x M(τ) + P(x B(τ) x^⊤) x C(τ)` along `M(τ) = τ (η_E D + E η_D)`,
`B(τ) = E (W_Q + τ η_Q)(W_K + τ η_K)^⊤ E^⊤/√d_h`, `C(τ) = E (W_V + τ η_V)(W_O + τ η_O) D`. If it
vanishes at every input, `attnFamily_rigid` gives

- `η_E D + E η_D = 0`. Multiply on the left by `I − E E⁺`: `(I − E E⁺) η_E D = 0`, and `D` has
  full row rank, so `η_E = E X` with `X = E⁺ η_E`. Then `E (X D + η_D) = 0` and `E` has full column
  rank, so `η_D = −X D`. Lean: `η.E = θ.E * X ∧ η.D = -(X * θ.D)`. Same, with the paper's signs
  ("`η_E = E X` and `η_D = −X D`").
- `E (η_Q W_K^⊤ + W_Q η_K^⊤) E^⊤ = 0` (as `1/√d_h ≠ 0`), so `η_Q W_K^⊤ + W_Q η_K^⊤ = 0`, and with
  `W_Q`, `W_K` of full column rank: `η_Q = W_Q Γ`, `η_K = −W_K Γ^⊤`.
- `E (η_V W_O + W_V η_O) D = 0`, so `η_V W_O + W_V η_O = 0`, and `η_V = W_V Γ'`,
  `η_O = −Γ' W_O`.

Lean's conclusion for the reads and writes is "those of `headDirQK θ Γ + headDirVO θ Γ'`". By
compiling (`Chk2.lean` (i)), entry by entry: query `W_Q Γ`, key `−W_K Γ^⊤`, value `W_V Γ'`, write
`−Γ' W_O`, and this sum has `E`-part and `D`-part `0`. So the conclusion is the paper's, signs
included. There is no term `−X W_read` in the reads and no `W_write X` in the writes, and that is
right for the limit `J_0`: the change of basis `I + τ X` moves the reads by `−X W_read` and the
writes of `θ_τ` by `τ W_write X`, and after `S_τ` both are of order `τ`.

By the computation (`depth_check.out`, nine networks): the kernel of `J_0` on a batch has the
dimension `d² + 2 ∑ H d_h²`; the directions of the Lean conclusion (`E X`, `−X D`, and the head
directions) lie in it (`|J_0 S| ≤ 5 · 10⁻¹⁴`) and span a space of the same dimension; the rank of
the Jacobian at `θ_τ` is `P − d² − s` for `τ = 10⁻², 10⁻³, −10⁻²` (gaps of 7 to 12 orders of
magnitude in the singular values).

`eventually_funDim_smallWrites_attention` against the first value: `∀ᶠ τ in 𝓝[≠] 0, fd(θ_τ) +
(d² + 2 ∑_ℓ H_ℓ d_{h,ℓ}²) = P`, under the structure. Degenerate cases, by hand: with `d` empty the
structure forces "no head at all" and the equality reads `0 + 0 = 0`; with `L = 0` it is the rank
of `(E, D) ↦ E D` at full rank, `P − d²`; a block with no head is allowed and adds nothing to `P`
or `s` (computed: rank 16 `= P − d² − s`).

The header of the file writes the conclusion of the paper's argument as "`D_θ B_j η = 0` and
`D_θ C_j η = 0` for the heads `j` of all blocks, where `E` and `D` do not vary inside the blocks".
The paper writes `ψ_{B_i} = 0`, `ψ_{C_i} = 0`. The sentence is not inside quotation marks and says
what it means; I note it only because `D_θ B_i η` is the paper's notation for the derivative in
which `E` does vary.

**5. `Residual/DepthAttentionGeneric.lean`.** (By reading; proved under exactly these hypotheses.)
What fails for a head of width `0`: its `B` is the zero matrix (a product through an empty index
set; also Lean's `(√0)⁻¹ = 0`), so `B v ≠ 0` fails for every `v`, the structure holds at no `θ`,
and `∀ᵐ θ, SmallWritesGenericAttention θ` would be false whenever some block has a head of width
`0`. So `hdh0` is needed for this statement. It is not needed for the truth of the final value: a
head of width `0` has no parameters and the output `0`. The paper's heads have `d_h ≥ 1` without
saying so. `d ≥ 2` is needed as soon as the network has two heads (with `d = 1` all `B_j v` are
collinear). A block with no head is allowed.

**6. `Dimension/ExpOrbitAttention.lean`.** (By reading; by hand; computation.)
`cobExpHeads θ (m, Γ, Γ') = cobExp ((θ.headsQK (exp Γ)).headsVO (exp Γ')) m`: first the change of
basis `exp Γ_{ℓ,i}` between queries and keys, then `exp Γ'_{ℓ,i}` between values and outputs, then
`exp m_ℓ` at the hidden states. The order does not matter: the first two act on different columns
of the read, and both act on the right of the read and on the left of the write, while the change
of basis of a hidden state acts on the other side. The same order stands in the conclusions of
`Dimension/LocalIdentifiabilityAttention.lean`. `expGL Y` is `exp Y` with the inverse `exp (−Y)`.
The derivative at `0`: `exp` has the derivative `I` at `0`, so `W_Q exp Γ ↦ W_Q Γ`,
`W_K (exp Γ)^{-⊤} ↦ −W_K Γ^⊤`, `W_V exp Γ' ↦ W_V Γ'`, `(exp Γ')⁻¹ W_O ↦ −Γ' W_O`, and the changes
of basis give `cobDir θ m`; the products of two small terms do not count. So the derivative is
`cobDir θ m + headDirQK θ Γ + headDirVO θ Γ'`. By the computation (`orbit_check.out`, three blocks
with different heads): the orbit is `θ` at `0`; it keeps the function of the skipless network
(`10⁻¹⁴`) and, with one `m` at all hidden states, of the residual network (`10⁻¹³`); with different
`m_ℓ` it changes the function of the residual network (44); the central difference quotient agrees
with the formula to `4 · 10⁻¹¹`.

**7. `Dimension/LocalIdentifiabilityAttention.lean`.** (By reading; by hand.)

- *"Locally identifiable up to its symmetries"* (D Definition 4.5, S Definition 4.4: "every `θ′`
  with `F_θ′ = F_θ` is the image of `θ` under a symmetry … for every `θ′` in some neighborhood of
  `θ`"): `∃ U ∈ 𝓝 θ, ∀ θ' ∈ U, (∀ x, eval … θ' x = eval … θ x) → ∃ G K K', … θ' =
  ((θ.headsQK K).headsVO K').cob G G`. Same function means equal outputs at every input.
- *"Every symmetry that is needed is then close to the identity"*: `∀ V ∈ 𝓝 1, ∀ W ∈ 𝓝 1,
  ∃ U ∈ 𝓝 θ, …` with `(G : matrices) ∈ V`, `K ∈ W`, `K' ∈ W`. The `1` are the families of identity
  matrices (compiled, `Chk2.lean` (a)). One `W` serves both `K` and `K'`; nothing is lost.
- *"The matrix `G` is the same at all hidden states"*: `cob (fun _ => G) (fun _ => G)`, which is
  `E ↦ E G`, `W_read^ℓ ↦ G⁻¹ W_read^ℓ`, `W_write^ℓ ↦ W_write^ℓ G`, `D ↦ G⁻¹ D` (`Params.cob`).
- *Which direction.* From the equality condition to local identifiability only, at one parameter:
  the hypothesis `hfd` is the equality `fd(θ) + k = P` at this `θ`, with `k = (L + 1) d² + s`
  without skips and `d² + s` with them. The converse is not stated (the header and the index say
  so). The paper's direction "equality condition implies local identifiability at generic
  parameters" follows, since the ranks hold almost everywhere.
- *Which symmetries.* Changes of basis of the hidden states and inside the heads, all near the
  identity. No permutation of heads. Are permutations needed near `θ`? No: the Lean conclusion
  without them is the stronger one, and it is what the paper's proof gives ("every `θ′` close to
  `θ` … is the image of `θ` under a symmetry close to the identity"). The permutations enter the
  paper's proof only in the converse direction.
- *True as written?* By hand, before the proofs: the family `Φ = cobExpHeads θ` (with one `m` for a
  residual network) passes through `θ`, is strictly differentiable at `0`, keeps the function
  (`eval_headsQK`, `eval_headsVO`, and the change of basis), and its derivative is injective under
  the ranks asked: `E m_0 = 0` gives `m_0 = 0` (`hE`); then `W_Q Γ = 0` and `W_V Γ' = 0` give
  `Γ = Γ' = 0` (`hQ`, `hV`); then `W_write m_ℓ = 0` gives `m_ℓ = 0` (`hw`; not needed with one `m`).
  Its domain has the dimension `k`. So `exists_mem_orbit_of_eval_eq` applies, and `exp` carries a
  neighbourhood of `0` into `V` and `W`. With `d` empty, or with no token, the statements stay true
  (the parameter space is a point; or `k = P` and the orbit map is a local diffeomorphism).
- *Not vacuous.* The hypothesis `hfd` holds almost everywhere for residual networks (Theorem 4.7)
  and for one skipless block (Theorem 5.1). For skipless networks of two or more attention blocks
  it is not a result of the papers. By the computation, the skipless rank is `P − (L + 1) d² − s`
  in the five cases of two or three blocks with `H d_h ≥ d` (20, 20, 16, 39, 28), so the hypothesis
  can hold there.

**8. `OneBlock/AttentionFamily.lean`: is `attnFamily_rigid` true as stated?** It is proved (three
standard axioms). By hand, the three cases of the brief. `J` empty: `hv` holds for every `v`, and
`hflat` says that `x M(τ)` has derivative `0` at every `x`, so `dM = 0`. One head: the
non-collinearity is empty, and Lemma C.3 for one tanh unit with a bias gives the claim. `dM ≠ 0`
compensated by the `dC_j`: on inputs with equal tokens the output is `u (M + ∑ C_j)`, so
`dM = −∑ dC_j`; the two-token inputs then give `v dC_j = 0` on an open set of `v`, so `dC_j = 0`
and `dM = 0`. The hypothesis on `v` is about `B_j(0)`, `C_j(0)`, the values at `τ = 0`. `hflat` is
`HasDerivAt (fun τ => x * Mc τ + ∑ j, attnWeights sees (x * Bc j τ * xᵀ) * x * Cc j τ) 0 0` for
every `x : Matrix T dIn ℝ`: the derivative of the whole `T × d_out` output. The proof of
`smallWritesLimit_eq_zero_attention` calls it with `J = Σ ℓ, H ℓ`, so the pieces fit.

**9. The headers.** The quotations in the eight file headers are the papers' sentences (compared
with the three texts). See note 4 for one paraphrase.

---------------------------------------------------------------------------------------------------

## What the authors should know

Nothing false, vacuous or drifted. In order of weight:

1. **The index is out of date in five sentences, and misplaces sixteen rows** (corrections 1 to 6):
   it still lists the eight files as "not yet compared"; it still says that Proposition 4.6 (D),
   Theorem 4.7, Corollary 4.9 and Corollary 4.10 (S) are not stated for attention blocks; and the
   rows of the dimension and skips papers on attention (lines 693 to 708) stand in the table under
   the heading "### Absorb paper".
2. **For the absorb paper: Theorem 4.2 (iii) is met trivially when `T ≤ L`** (Check 4): a residual
   network with `E D ≠ 0` can be the zero function there, and then equals the zero skipless
   network. The paper's proof gives a common function that is not zero, and Lean states that. The
   paper could say "and their common function is not zero". For `T = L + 1` no trivial instance
   exists.
3. **One statement changed in form after it was written:** `cobExpHeads_zero` lost two instance
   arguments that it did not use (`omit [Fintype dIn] [Fintype dOut] in`, added with the proof).
   Nothing else changed in a statement, a docstring or a header between `6acdc8c` and `2d84c16`.
4. **Lean's (iii) has one choice of heads:** two heads of dimension one in every block of both
   networks. The paper's statement is an existence statement, so this is enough; the paper's proof
   allows any two or more heads of any dimension.
5. **Lemma A.27 is stated for networks of attention blocks only.** The paper's lemma also covers
   networks that mix attention and MLP blocks ("in any order"). No Lean statement covers a mixed
   network, for Lemma A.27, Theorem 4.7 or Corollary 4.9.
6. **Lean's Theorem 4.7 for attention asks less than the Scope:** heads of width `1 ≤ d_h ≤ d`,
   any numbers of heads (different from block to block, also none in a block), any total width, and
   any mask with a token that sees itself and another. The computation agrees in the cases outside
   the Scope that I tried.
7. **The hypothesis `H d_h ≥ d` of the gain** is the paper's (Scope; proof of Theorem 4.7). In two
   computed cases with `H d_h < d` the gain was larger than `L d²`.
8. **Not stated in Lean** from the passages of this audit: the clause of Theorem 4.7 "by exactly
   `L dim 𝒢` when the skipless network satisfies the equality condition too" for attention blocks;
   Corollary 4.10 (ii); the converse direction of Propositions 4.6 (D) and 4.5 (S); the real
   factorization of `Q` (Lean has the complex one); "`U` is diagonalizable" (Lean has its
   consequence).
9. **For skipless networks of two or more attention blocks** the statement on local
   identifiability is conditional on an equality that the papers do not claim.
10. Three files appeared while I read and are outside the brief: `Residual/DepthAttentionRMS.lean`,
    `Residual/DepthAttentionRMSDim.lean`, `Residual/LocalIdentifiabilityAttentionRMS.lean`. No
    reader has compared them.

## Corrections for `STATEMENTS.md` (lines of `2d84c16`)

1. Lines 132–138, "Not yet compared by such a reader (written after the twelfth audit began)":
   take out `Absorb/ShortSequencesPoly.lean`, `Absorb/ShortSequences.lean`,
   `OneBlock/AttentionFamily.lean`, `Residual/DepthAttention.lean`,
   `Residual/DepthAttentionGeneric.lean`, `Residual/DepthAttentionDim.lean`,
   `Dimension/ExpOrbitAttention.lean` and `Dimension/LocalIdentifiabilityAttention.lean`; keep
   `Residual/DepthAttentionRMS.lean`, `Residual/DepthAttentionRMSDim.lean` and
   `Residual/LocalIdentifiabilityAttentionRMS.lean`. Add a sentence: a thirteenth reader (24
   November) compared the eight files with Theorem 4.2 (iii) of the absorb paper and its proof,
   with Lemma A.27, Theorem 4.7, Proposition 4.5 and Corollaries 4.9, 4.10 (i) of the skips paper
   and with Proposition 4.6 of the dimension paper (report
   `claude/lean-statement-audit-thirteenth-2026-11-24.md`) and found nothing false, vacuous or
   drifted: all seven generic statements are `∀ᵐ θ ∂μ`, Lemma A.27 in the form "for almost every
   `θ`, for all small `τ ≠ 0`"; the conditions of (iii) are the exact complement of those of (i);
   the division in `s = 2 L d²/H` is exact; eight statements were judged by hand before their
   proofs were written; `cobExpHeads_zero` lost two unused instance arguments with its proof.
2. Lines 539–542: in "Not stated yet from the main text: Example 4.2; the converse direction of
   Proposition 4.6 (…); Proposition 4.6 for attention blocks (Theorem 4.3 for attention blocks is
   proved, …; Theorem 5.1 for an attention block is proved, `OneBlock/AttentionDim.lean`)" delete
   "Proposition 4.6 for attention blocks (…)" and say instead: "for attention blocks without
   normalization Proposition 4.6 is proved in the same direction, at one parameter, and at almost
   every parameter for one block (`Dimension/LocalIdentifiabilityAttention.lean`)". In the sentence
   that follows (lines 545–548) add this file to the list of files.
3. Lines 609–611, "Proposition 4.5 (one direction) and Corollary 4.9 of the skips paper stand in the
   table of the dimension paper above, beside their twins (…)": add "; for attention blocks in the
   row of `Dimension/LocalIdentifiabilityAttention.lean`".
4. Lines 624–630: in the list "Not stated yet from the main text of the skips paper" replace
   "Theorem 4.7 for attention blocks, and its clause "by exactly `L dim 𝒢` …" as a conditional
   statement" by "the clause of Theorem 4.7 "by exactly `L dim 𝒢` …" as a conditional statement
   (Theorem 4.7 for attention blocks without normalization is proved,
   `Residual/DepthAttentionDim.lean`)"; replace "Corollary 4.9 for attention blocks (it is proved
   for tanh, GELU, SwiGLU and GeGLU blocks, …)" by "(Corollary 4.9 is proved for tanh, GELU, SwiGLU
   and GeGLU blocks, …, and for attention blocks without normalization,
   `Dimension/LocalIdentifiabilityAttention.lean`)"; replace "Corollary 4.10;" by "Corollary 4.10
   (ii) (part (i) is proved, `Residual/DepthAttentionDim.lean`);". Add to the list: "Lemma A.27,
   Theorem 4.7 and Corollary 4.9 for networks that mix attention and MLP blocks". The same
   paragraph should name what the three new files for pre-RMSNorm state; I did not read them.
5. Lines 615–619, the converse direction of Proposition 4.5 ("the other direction is proved at one
   parameter, …"): add `Dimension/LocalIdentifiabilityAttention.lean` to the files named.
6. Line 634 and lines 693–708: the sixteen rows from "D Appendix B, the symmetries inside the
   heads of an attention block" to the last row on attention before "A Theorem 4.3, the conditions
   of its proof" are statements of the dimension and skips papers and stand in the table headed
   "### Absorb paper". Move them, or put one sentence under the headings "### Dimension paper"
   (line 228) and "### Skips paper" (line 553): "the rows on attention blocks of this paper stand
   in the table of the absorb paper, after Theorem 4.2".
7. Line 692 (`Absorb/ShortSequences.lean`), additions: "nothing is asked of `d_in`, `d_out` (the
   Scope: `≥ d`); the paper's proof allows two or more heads of any dimension; for `n = L + 1`
   every residual network with `E D ≠ 0` is nonzero, by (i); the identity `I − 3U = −2U²` is about
   the matrix `U`, and the two networks of the sentence are the case `n = 2`, `L = 1`, `L' = 1` of
   the theorem".
8. Line 691 (`Absorb/ShortSequencesPoly.lean`), optional additions: "that the complex factors come
   in conjugate pairs is not stated"; "'`U` is diagonalizable' is stated through this consequence".
9. Line 701 (`Residual/DepthAttention.lean`), additions: "all blocks are attention blocks (the
   paper's lemma also allows MLP blocks among them: not stated)"; "the statement on the flat
   directions is one inclusion; the ranks of the queries of all heads and of the write are not
   asked, since `E` and `D` do not move inside the blocks".
10. Line 703 (`Residual/DepthAttentionDim.lean`), additions: "a block may have no head; a head of
    width `0` is excluded"; "`2 L d²/H` is written with the division of natural numbers, which is
    exact under the hypotheses (also for `L = 0`)"; to "Not stated:" add "the clause 'by exactly
    `L dim 𝒢` when the skipless network satisfies the equality condition too'".
11. Line 707 (`Dimension/LocalIdentifiabilityAttention.lean`), additions: "no permutation of heads
    is needed, the symmetries of the conclusion are near the identity"; "for skipless networks of
    two or more attention blocks the equality `fd = P − (L+1)d² − s` is a hypothesis that the
    papers do not prove".
12. No correction to lines 700, 702, 706: they describe the Lean statements correctly. The status
    "proved" of the eight rows agrees with what I compiled.

## What I could not check, or did not

- The proofs: not audited, as the brief says. I read of them only what fixes the meaning of a
  statement (which hypotheses are used; that `smallWritesLimit_eq_zero_attention` calls
  `attnFamily_rigid`).
- I did not run `lake build`. The axioms I saw through a copy of the compiled library of
  `/home/claude/lp/lean` (taken at 14:35 UTC) and through my own compilation of copies of two
  files; `Residual/DepthAttention.lean`, `Residual/DepthAttentionGeneric.lean` and
  `Residual/DepthAttentionDim.lean` I did not compile myself.
- That an additive Haar measure on `Params` is a Lebesgue measure: taken from the sixth report.
- The computations are in double precision on random draws; a rank read from singular values is a
  judgement (the gaps are in `depth_check.out`). They support the hand arguments and prove
  nothing. The remark that the gain exceeds `L d²` for `H d_h < d` rests on two draws.
- The texts `absorb.txt`, `skips.txt`, `dim.txt` against the PDFs.
- Mixed networks, pre-RMSNorm, Corollary 4.10 (ii) and the converse directions: not stated in the
  eight files, so there was nothing to compare.
- The three new files for attention under pre-RMSNorm, and the other rows of the index.

Scratch files: `/home/claude/audit13/` (`Chk1.lean` to `Chk4.lean` and their outputs,
`cmp_statements.py`, `short_check.py`, `depth_check.py`, `orbit_check.py` and their outputs).
