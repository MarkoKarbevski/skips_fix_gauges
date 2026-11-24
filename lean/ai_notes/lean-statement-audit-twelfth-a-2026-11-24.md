STATUS: complete

# Twelfth audit of Lean statements against the papers, part A (24 November 2026)

Reader: an independent reader who did not write the statements. Brief:
`/home/claude/proj_up/audit12a_brief_2026-11-24.md`. I audited statements and definitions, not
proofs. I changed no repository file, ran no `lake build`, made no commit and no push.

Library: `/home/claude/lw/lean` (branch `lean-wip`). The branch moved while I read. Commit at the
start: `2a488da1da773d33fb1a817b15c4c3eb34bc84cc` (24 November, 14:00:45 UTC). Commit at the end:
`479f2f23aea2ff02943c52676d0f91316ca04dbe` (14:10:39 UTC). Between the two
(`git diff 2a488da 479f2f2 --stat`): the proofs of `OneBlock/AttentionGeneric.lean` and
`OneBlock/AttentionStepOne.lean`; two new files with statements for Theorem 4.2 (iii),
`Absorb/ShortSequencesPoly.lean` and `Absorb/ShortSequences.lean` (in work; not in the brief, and I
did not compare them with the paper); `STATEMENTS.md`, `SkipsLean.lean`, `checks/Axioms.lean`. The
two files of this audit, `Network/Attention.lean`, `Network/Defs.lean` and `Basic/RMSNorm.lean` did
not change (empty `git diff`). In `STATEMENTS.md` the row of `Absorb/AttentionZero.lean` is
unchanged, and the row of `Absorb/AttentionNetworks.lean` changed in its last sentence only ("Not
stated: (iii) (short sequences)" became "Part (iii) (short sequences) is in
`Absorb/ShortSequences.lean`"). Line numbers of `STATEMENTS.md` below are those of `479f2f2`.

Files with `sorry` (by `grep` over `SkipsLean/`). At `2a488da`: `OneBlock/Attention.lean` (5, lines
104, 109, 120, 134, 172), `OneBlock/AttentionGeneric.lean` (1, line 38),
`OneBlock/AttentionStepOne.lean` (1, line 60). At `479f2f2`: `OneBlock/Attention.lean` (the same
5), `Absorb/ShortSequencesPoly.lean` (3, lines 50, 58, 66), `Absorb/ShortSequences.lean` (2, lines
49, 70). The two files of this audit have none, and import none of these files.

Subject: `Absorb/AttentionZero.lean` (`valueOutput`, `hasDerivAt_eval_attention_zero`) and
`Absorb/AttentionNetworks.lean` (six theorems), against Theorem 4.2 (i), (ii) of the absorb paper
and its proof (text `absorb.txt`, lines 375–403 and 1345–1451), Section 3.3 with equation (4), and
Section 2.

How I checked. "By reading": I read the Lean source and the paper's text. "By compiling": two
scratch files of my own, `/home/claude/audit12a/Chk.lean` and `/home/claude/audit12a/Chk2.lean`
(outputs `/home/claude/audit12a/Chk.out`, `/home/claude/audit12a/Chk2.out`), compiled once each
with `lean` 4.36.0 (a few seconds each, no errors) against the compiled library of `/home/claude/lp/lean` through
`LEAN_PATH`, without `lake`; the sources of the two files are the same in `lp` and `lw` (`diff`),
and their compiled files in `lp` are newer than the sources. "By a computation": a Python script,
`/home/claude/audit12a/deriv_check.py` (output `/home/claude/audit12a/deriv_check.out`).

**Short answer. Nothing false, vacuous or drifted was found.** The eight public names say what the
paper says, or slightly more. Generic is "almost every parameter" with one null set for all
skipless networks. Two places of the index are out of date (below). The public statements and both
file headers are word for word those of the statement commit `9cf33d3` (13:28:30 UTC), compared by
a script: the proving did not change them.

Conventions used below (from the sixth and the eleventh report, and reread here in
`Network/Defs.lean`, `Network/Attention.lean`, `Basic/RMSNorm.lean`): `eval A M θ X = χ(h_L) D`
with `h_0 = X E` and `h_ℓ = h_{ℓ−1} M_ℓ + f_ℓ(χ(h_{ℓ−1}) W_read) W_write`. This is the paper's `y`
(Section 2: "equality of networks, and every result below, concern `y`"). In the six theorems the
residual network has `M = 1` and the skipless one `M = 0`; by compiling, `1` is the identity matrix
in every block and `0` the zero matrix, and one step of the recursion is
`h_ℓ = h_{ℓ−1} + f(χ(h_{ℓ−1}) R) W`, respectively `h_ℓ = f(χ(h_{ℓ−1}) R) W`: the paper's
"`h_ℓ = h_{ℓ−1} + B_ℓ(χ(h_{ℓ−1}))` in a residual network and `h_ℓ = B_ℓ(χ(h_{ℓ−1}))` in a skipless
one". `rmsNorm ε` divides each row `v` by `√(v·v / d + ε)`, the paper's `N`.

---------------------------------------------------------------------------------------------------

## Part 1: the four drift checks

### Check 1. Generic means almost every parameter, for every Haar measure

**Verdict: yes.** By reading, and the elaborated statements by compiling (`Chk.out`).

Paper, Theorem 4.2 (ii): "For almost every choice of weights of the residual network, no such
skipless network equals it, whatever `L′`." Section 2: "A statement holds for generic weights, or
for almost every choice of weights, if it holds outside a set of weights of Lebesgue measure zero."

Lean (`Absorb/AttentionNetworks.lean:640-650`):

```
theorem ae_forall_ne_residual_skipless_attention_causal [Nonempty d] [Nonempty dIn]
    [Nonempty dOut] {n : ℕ} (hn : 2 ≤ n)
    (μ : Measure (Params (Arch.attention (T := Fin n) (d := d) (fun t s => s ≤ t) id H dh)
      dIn dOut)) [μ.IsAddHaarMeasure] :
    ∀ᵐ θ ∂μ, ∀ (L' : ℕ) (d' : Type) [Fintype d'] [DecidableEq d'] (H' dh' : Fin (L' + 1) → Type)
      [∀ ℓ, Fintype (H' ℓ)] [∀ ℓ, Fintype (dh' ℓ)]
      (θ' : Params (Arch.attention (T := Fin n) (d := d') (fun t s => s ≤ t) id H' dh')
        dIn dOut),
      ∃ X : Matrix (Fin n) dIn ℝ,
        eval (Arch.attention (fun t s => s ≤ t) id H dh) 1 θ X
          ≠ eval (Arch.attention (fun t s => s ≤ t) id H' dh') 0 θ' X
```

and (`:658-669`) the same under pre-RMSNorm, with `{ε : ℝ} (hε : 0 < ε)` before `μ`, the residual
network on `rmsNorm ε`, and inside the `∀ᵐ`: `… (ε' : ℝ), 0 < ε' → ∀ θ' : Params (Arch.attention …
(rmsNorm ε') H' dh') dIn dOut, ∃ X, … ≠ …`.

- The quantifier over the weights of the residual network is `∀ᵐ θ ∂μ`: the set of the `θ` at which
  what follows fails has `μ`-measure zero. `θ` ranges over all weights of the residual network
  (`E`, the reads `[W_Q | W_K | W_V]` of all heads, the writes `W_O`, `D`).
- Everything about the skipless network (its depth `L' + 1`, its model dimension `d'`, its heads
  and head dimensions, its weights `θ'`, and `ε'` under RMSNorm) is quantified **inside** the
  `∀ᵐ`. So one null set serves all skipless networks: "no such skipless network equals it,
  whatever `L′`".
- `μ` is a variable of the statement with `[μ.IsAddHaarMeasure]`: any additive Haar measure on the
  parameter space, which carries its Borel σ-algebra (`Generic/Params.lean:32-34`). That such a `μ`
  is a Lebesgue measure up to a positive factor was compiled by the sixth reader for every
  `Params A dIn dOut`; I did not compile it again.
- Nothing generic is stated as "there is a point" or on an open set. (In the proof one point `θ₀`
  serves only to show that a polynomial in the weights is not zero.) The four statements of (i) are
  for every `θ` with `E D ≠ 0`, as in the paper.

One remark, not a drift: the paper's (ii) is for both masks. Lean states it for the causal mask
only. Without a mask the paper's (ii) is its (i) ("By (i), only causal masks remain"), and so it is
in Lean: for every `θ` with `E D ≠ 0` the theorem `exists_ne_residual_skipless_attention_noMask`
gives the conclusion for all skipless networks at once (compiled in `Chk2.lean`). A statement
"for almost every `θ`, without a mask" with no hypothesis `E D ≠ 0` is not in the file.

### Check 2. No extra hypotheses

**Verdict: no extra restriction. Every hypothesis is the paper's or weaker than the paper's.** By
reading; the hypotheses are those of the elaborated statements in `Chk.out`.

| Hypothesis in Lean | In which theorems | The paper | Verdict |
|---|---|---|---|
| `hT : 2 ≤ Fintype.card T` | (i) no mask, both | Section 3.3: "whose rows are the `T ≥ 2` tokens" | In the paper. Needed: with one token every attention weight is `1`, a block is `h ↦ h V`, and the residual block with `V = 1` equals the skipless block with `V' = 2` (computed: difference `0` on 1000 inputs). |
| `hn : 2 ≤ n` | (ii), both | the same `T ≥ 2` | In the paper. Needed for the same reason. |
| no hypothesis `2 ≤ n` | (i) causal, both | `T ≥ 2` | Same: `hn` below implies `n ≥ 2` (`L + 2 ≤ n`; or `n = L + 1` and `1 ≤ L' + 1 ≤ L`). |
| `hED : θ.E * θ.D ≠ 0` | (i), all four | "let a residual network of `L` attention blocks have `ED ≠ 0`" | In the paper. |
| no hypothesis `E D ≠ 0` | (ii), both | the theorem's `ED ≠ 0` stands before (ii) too | Weaker than the paper (`E D ≠ 0` holds for almost every `θ` anyway). |
| the skipless network has `L' + 1` blocks, `L' : ℕ` | all six | "skipless networks of `L′ ≥ 1` attention blocks" | In the paper: the paper's `L′` is Lean's `L' + 1`. The paper's skipless network cannot have no block (`L′ ≥ 1` in the theorem; Section 2: "`L ≥ 1` blocks"). |
| `hn : L + 2 ≤ n ∨ (n = L + 1 ∧ L' + 1 ≤ L)` | (i) causal, both | "when `T ≥ L + 2`, and when `T = L + 1` and `L′ ≤ L`" | In the paper, clause for clause, with `L′ = L' + 1`. |
| `hε : 0 < ε`, `hε' : 0 < ε'` | the three `_rmsNorm` | "with pre-RMSNorm and `ε > 0`" | Weaker than the paper: the paper has one `ε` for both networks; Lean allows `ε' ≠ ε`. In (ii) `ε'` is quantified inside the `∀ᵐ`. |
| `[Nonempty d] [Nonempty dIn] [Nonempty dOut]` | (ii), both | Scope: "`d_in, d_out ≥ d_model ≥ 2`" | Weaker than the paper. Needed: if one of the three is empty, both networks are the zero (or the empty) function at every `θ`. In (i) they follow from `E D ≠ 0`. |
| the residual network has `L : ℕ` blocks | all six | Section 2: "`L ≥ 1` blocks" | Weaker than the paper: Lean also covers `L = 0` (the residual network `X ↦ χ(X E) D`). True there too (Part 2, degenerate cases). |
| `H dh : Fin L → Type`, `H' dh' : Fin (L' + 1) → Type`, any finite types | all six | "with any numbers of heads and any head dimensions"; Scope: "all attention blocks of a network have the same number of heads" | Weaker than the paper: the number of heads and the head dimension may change from block to block, and may be `0`. Within one block all heads have one dimension, as in equation (4). |
| `d'` any finite type (`Type*` in (i), `Type` in (ii)) | all six | Scope: "A skipless network that is compared with a residual one may have another model dimension, unless the statement says 'the same `d_model`'" | In the paper. `Type` instead of `Type*` in (ii) loses nothing (every finite type is in bijection with a `Fin k`). |
| no condition on `d`, `d_in`, `d_out` | (i), all four | Scope: "`d_in, d_out ≥ d_model ≥ 2`" | Weaker than the paper. |

So: a skipless network of another depth, with other heads and another model dimension is covered,
as in the paper.

### Check 3. The masks

**Verdict: the paper's masks, and both networks have the same mask and the same tokens.** By
reading; the two matrices `U` by compiling (`Chk.lean`).

- No mask: `sees = fun _ _ => True` on any finite type `T` of tokens. Every token sees every token.
  Compiled: `attnWeights (fun _ _ => True) 0 t s = 1 / card T`. Paper (proof): "all `T` tokens
  without a mask", "Every entry of `U` is `1/T`".
- Causal mask: `sees = fun t s => s ≤ t` on `Fin n`: token `t` sees itself and the earlier tokens.
  Compiled: `attnWeights (fun t s => s ≤ t) 0 t s = if s ≤ t then 1 / (t + 1) else 0` (tokens
  counted from `0`). Paper (proof): "row `t` is uniform on the tokens that token `t` attends to: …
  the first `t` tokens with a causal mask" (tokens counted from `1`), "`U` is lower triangular with
  the diagonal entries `1, 1/2, …, 1/T`". Computed for `n = 2, 3, 5`: the eigenvalues are
  `1, 1/2, …, 1/n`.
- In each of the six theorems the residual and the skipless network are
  `Arch.attention (T := …) sees …` with the same `sees` and the same token type (`T`, or `Fin n`
  with one `n`), and the same input `X : Matrix T dIn ℝ` and output type `Matrix T dOut ℝ`.

### Check 4. What "differs" means

**Verdict: same.** By reading; the equivalence by compiling (`Chk.lean`).

Paper (Section 1): "Two networks are equal if they compute the same function"; Section 2: equality
concerns `y = χ(h_L) D`. Lean: `∃ X : Matrix T dIn ℝ, eval … 1 θ X ≠ eval … 0 θ' X`. `X` ranges
over all of `ℝ^{T × d_in}`, and "some `X` with different outputs" is "not the same function"
(`Function.ne_iff`). With `ε > 0` RMSNorm is defined everywhere, so the paper's convention for
`ε = 0` (agreement on a dense set) does not enter.

---------------------------------------------------------------------------------------------------

## Part 2: the statements

### Verdict table

| Paper | Lean | Verdict | Difference |
|---|---|---|---|
| Proof of Theorem 4.2: "`V = ∑_i W_{V,i} W_{O,i}` is the sum of the value–output products of the heads" | `valueOutput θ ℓ` | SAME | The sum over the heads `i : H ℓ` of (columns `(i, value k)` of the read) times (rows `(i, k)` of the write). These are the `W_{V,i}`, `W_{O,i}` with which block `ℓ` is equation (4) (`f_attention_mul`); compiled in `Chk2.lean`. |
| Proof of Theorem 4.2, the Jacobians at `X = 0`: the skipless network `δ ↦ U^{L′} δ Λ′`, block `ℓ` of the residual network `δ ↦ δ + ξ U δ V_ℓ`, the residual network `δ ↦ ∑_k U^k δ Λ_k` | `hasDerivAt_eval_attention_zero` | PART | Lean has the derivative only along the lines `τ ↦ τ a b` with `U a = λ a` (the inputs on which the proof uses the Jacobians), not the derivative at `0` in every direction `δ`. On these inputs it is the paper's formula. It is more general in three ways: any mask, any `χ` with `χ(0) = 0` and the derivative `ξ I` at `0`, any stream `s I` and any `L ≥ 0`. |
| Theorem 4.2 (i), no mask, without normalization | `exists_ne_residual_skipless_attention_noMask` | LEAN STRONGER | Contains the paper's statement. Also covers `L = 0`, numbers of heads and head dimensions that change from block to block, and any `d`, `d_in`, `d_out`. |
| Theorem 4.2 (i), no mask, pre-RMSNorm, `ε > 0` | `exists_ne_residual_skipless_attention_noMask_rmsNorm` | LEAN STRONGER | As above, and the skipless network may have another `ε' > 0`. |
| Theorem 4.2 (i), causal mask, without normalization | `exists_ne_residual_skipless_attention_causal` | LEAN STRONGER | The paper's two conditions on `T`, with `L′ = L' + 1`. Also covers `L = 0` (then the condition is `n ≥ 2`), and the wider heads and dimensions. |
| Theorem 4.2 (i), causal mask, pre-RMSNorm, `ε > 0` | `exists_ne_residual_skipless_attention_causal_rmsNorm` | LEAN STRONGER | As above, and `ε' ≠ ε` allowed. |
| Theorem 4.2 (ii), causal mask, without normalization | `ae_forall_ne_residual_skipless_attention_causal` | SAME | One null set for all skipless networks. No hypothesis `E D ≠ 0`; `d`, `d_in`, `d_out` nonempty instead of the Scope's `≥ 2`; `L = 0` allowed. |
| Theorem 4.2 (ii), causal mask, pre-RMSNorm, `ε > 0` | `ae_forall_ne_residual_skipless_attention_causal_rmsNorm` | LEAN STRONGER | As above, and the one null set serves every `ε' > 0` of the skipless network. |
| Theorem 4.2 (ii), no mask | no statement of its own | PART | Given by (i) for every `θ` with `E D ≠ 0`, as in the paper's proof. No `∀ᵐ` form. |
| Theorem 4.2 (iii) (short sequences) | not in the two files (the header says so) | — | Not compared. At `479f2f2` it is stated, in work, in `Absorb/ShortSequences.lean`, which is outside this audit. By reading the index row only: its conditions (`n ≤ L`, or `n = L + 1` and `L ≤ L'`) are exactly the negation of `hn` of (i). |
| Last sentence of the proof: (i) and (ii) "also hold with rotary embeddings" | not stated | — | The index does not say so (see the corrections). |
| The text after the theorem (lines 394–403) | — | consistent | "no number of heads helps" (any `H'`); "Neither does depth, once a sequence has at least two more tokens than the residual network has blocks" (`L + 2 ≤ n`, any `L'`); "Under pre-RMSNorm, equality in the cases of (iii) fails for almost all weights, by (ii)" (`ae_…_causal_rmsNorm` has no condition on `n` beyond `2 ≤ n`). The text restates no condition that Lean lacks. Table 1 and the introduction (lines 76–78, 125–142) agree too. |

### Notes

**`hasDerivAt_eval_attention_zero`, recomputed by hand for one block and one head.** Input
`X = τ a b`, with `U a = λ a`. `h_0 = τ a (b E)`. The block reads `χ(h_0) = ξ τ a (b E) + o(τ)`.
Its scores `χ(h_0) Γ χ(h_0)^⊤` tend to `0`, so its weights tend to `U = softmax(0)`, and
`B(χ(h_0)) = P · χ(h_0) · V = U (ξ τ a (b E)) V + o(τ) = ξ λ τ a (b E V) + o(τ)`. So
`h_1 = s h_0 + B(χ(h_0)) = τ a (b E (s I + ξ λ V)) + o(τ)`, and the output is
`χ(h_1) D = ξ τ a (b E (s I + ξ λ V) D) + o(τ)`. The derivative at `τ = 0` is
`a (ξ b E (s I + ξ λ V) D)`. Lean: `vecMulVec a (ξ • (b ᵥ* (θ.E * (List.ofFn fun ℓ => s • 1 +
(ξ * lam) • valueOutput θ ℓ).prod * θ.D)))`, which for `L = 1` is this. Same.

For `L` blocks the Lean product is `M_0 M_1 ⋯ M_{L−1}` with `M_ℓ = s I + ξ λ V_ℓ`, the first block
on the left; with rows on the left this is the order of the blocks. With `s = 1` it expands to
`∑_k λ^k ξ^{k+1} E (∑_{ℓ_1 < ⋯ < ℓ_k} V_{ℓ_1} ⋯ V_{ℓ_k}) D = ∑_k λ^k Λ_k`: the paper's residual
Jacobian `δ ↦ ∑_k U^k δ Λ_k` on `δ = a b`. With `s = 0` it is `λ^{L′} ξ^{L′+1} E′ V′_1 ⋯ V′_{L′} D′
= λ^{L′} Λ′`: the paper's `δ ↦ U^{L′} δ Λ′` on `δ = a b`. (The private helper `core_atn` has
`ξ'^{L'+2}` for `L' + 1` blocks: the same.)

By a computation (`deriv_check.py`): for random weights, three tokens, both masks, `χ` the identity
and RMSNorm with `ε = 0.7`, `s = 1, 0, 0.5`, and five shapes (among them `L = 0` and a block with
no head), the central difference quotient at `τ = 0` agrees with the formula for every eigencolumn
of `U`: the largest relative error over the 60 cases is `3.4e-07`.

**`χ`, `ξ`.** `χ` is the map before every read and before the readout, `ξ` the factor of its
derivative at `0`. The hypotheses are `χ 0 = 0` and `HasFDerivAt χ (ξ • id) 0`. The identity has
them with `ξ = 1`. `N_ε` with `ε > 0` has them with `ξ = 1/√ε`: `N_ε(0) = 0`, and
`N_ε(h) = h/√ε + O(‖h‖³)` (the paper's "`N(h) = ξ h + O(‖h‖³)`"). In the file the two facts for
`rmsNorm ε`, `0 < ε`, are the private helpers `rmsNorm_zero_mat_atn` and
`hasFDerivAt_rmsNorm_zero_atn` (`(Real.sqrt ε)⁻¹ • id`), and the three public `_rmsNorm` theorems
are obtained from them. So the hypothesis on `χ` is right for `N_ε`. Lean needs less than the paper
writes: differentiability of `χ` at `0` instead of the `O(‖h‖³)` term, and continuity of the
weights at zero scores instead of "`P = U + O(‖h‖²)`".

**The header quotations.** The two file headers quote the theorem and its proof. I compared the
quotations with `absorb.txt` (lines 1345–1406): they are the paper's words.

**The polynomial of the causal case.** Paper: `p(z) = ∑_{k=0}^L Λ_k z^k − Λ′ z^{L′}` vanishes at
`1, 1/2, …, 1/T`; if `L′ ≤ L` degree at most `L` and `T ≥ L + 1` roots; if `L′ > L` then
`T ≥ L + 2` and Descartes' rule. The Lean hypothesis `hn` is exactly the union of these two cases.
I did not find a case that `hn` admits and the paper does not, other than `L = 0`.

**Degenerate cases tested for a counterexample (by hand, each clause checked; none found).**

- `L = 0`, no mask, at least two tokens: the residual network is `X ↦ χ(X E) D` (compiled for
  `χ = id`: `X E D`). Along `τ a b` with `a ≠ 0` of sum zero its derivative at `0` is `ξ a (b E D)`;
  that of a skipless network of one block or more is `0`, since `U a = 0`. So `E D = 0`. True.
- `L = 0`, causal mask: `hn` reads `n ≥ 2`. The eigenvalues `1` and `1/2` give `ξ E D = Λ′` and
  `ξ E D = 2^{−(L'+1)} Λ′`, so `Λ′ = 0` and `E D = 0`. True. (An instance of the Lean statement with
  `L = 0`, `n = 2`, `L' = 0` compiled.)
- `n = 2`, causal mask: `hn` holds only for `L = 0`, or `L = 1` with `L' = 0` (one skipless block).
  For `L = 1`, `L' = 0`: `p` has degree at most `1` and two roots, so `Λ_0 = 0`. True. The paper's
  example after the theorem (`T = 2`, the residual block `h ↦ h − 3 U h`, two skipless blocks
  `h ↦ −2 U² h`) is `L = 1`, `L' = 1`: `hn` is false there (`3 ≤ 2` no; `2 ≤ 1` no). Computed in
  the frame of `Arch.attention` (`d = 1`, zero queries): the two networks agree on 1000 random
  inputs to `7e-15`. So `hn` cannot be dropped, and the Lean statement does not claim this case.
  For (ii) this `θ` lies in the null set: `F(1/2) − F(1)/4 = −1/2 + 2/4 = 0` for `F(z) = 1 − 3z`.
- `L' = 0` (one skipless block): covered above; with `n = L + 1` it needs `L ≥ 1`, as in the paper
  (`L′ = 1 ≤ L`).
- No head in a block (`H ℓ` empty): the block is `0` and `V_ℓ = 0`. In the residual network this is
  a block that does nothing; in the skipless network the hidden state becomes `0` and the output is
  `χ'(0) D' = 0`, while the residual network is not the zero function (its derivative along some
  `τ a b` is not `0`, by the argument of the proof with `Λ′ = 0`). True.
- Head dimension `0` (`dh ℓ` empty): the head has no columns, its value–output product is the empty
  sum `0`; Lean's `1/√0` is `0` (compiled) and multiplies an empty sum. As no head. True.
- One head: nothing special. `d` with one element: nothing special; the paper's own example has
  `d_model = 1`. `d'` empty: the skipless network is `0`; as above.
- `d`, `d_in` or `d_out` empty: in (i) excluded by `E D ≠ 0`; in (ii) excluded by the three
  `Nonempty`. Without them (ii) would be false.
- One token without a mask: excluded by `2 ≤ card T`; there a counterexample exists (Check 2).

### The index rows of the two files

By reading `STATEMENTS.md` at `479f2f2`.

- Line 667 (`Absorb/AttentionZero.lean`): right. It says "any mask", "a map `χ` with `χ(0) = 0` and
  the derivative `ξ I` at `0`", "the stream matrices `s I`", "the derivative at `τ = 0` of the
  output at the input `τ • a b`". Names and status right (`#print axioms`: the three standard
  axioms).
- Line 668 (`Absorb/AttentionNetworks.lean`): right. All six names, "(`ε, ε' > 0`)", "`L' + 1`
  attention blocks", "any heads, head dimensions and model dimension", the two conditions on `n`,
  "(ii) with the causal mask on `n ≥ 2` tokens", and where (iii) is. Status right (`#print axioms`
  for the six: the three standard axioms). Missing, none of it an error: see the corrections.
- Two other places of the index are out of date: lines 116–121 and line 728 (corrections 1 and 2).

---------------------------------------------------------------------------------------------------

## What the authors should know

Nothing false, vacuous, drifted or misdescribed in the two files. In the order of weight:

1. **The index says in one place that Theorem 4.2 is not stated** (`STATEMENTS.md:728`: "Not stated
   yet: Theorems 3.4, 4.2; …"), and in another that these two files have not been compared by an
   independent reader (lines 116–121). Both are out of date.
2. **The paper's (ii) without a mask has no `∀ᵐ` statement.** It is (i) for every `θ` with
   `E D ≠ 0`. If the authors want "(ii)" to be quotable for both masks in one form, one more
   statement would be needed (with "`E D ≠ 0` for almost every `θ`"); nothing is wrong as it is.
3. **Lean covers more than the paper in four ways**, all true: `L = 0`; `ε' ≠ ε`; heads and head
   dimensions that change from block to block (and may be `0`); no bound `d_in, d_out ≥ d_model ≥ 2`
   (in (ii): nonempty).
4. **`hasDerivAt_eval_attention_zero` is a derivative along a line**, on the inputs `a b` with
   `U a = λ a`, not the paper's Jacobian in every direction. The index row and the docstring say
   "on the inputs `a b`"; the word "Jacobians" in the row title is the paper's.
5. The last sentence of the paper's proof (rotary embeddings) is not stated in Lean.
6. The public statements have not changed since they were first committed (`9cf33d3`).

## Corrections for `STATEMENTS.md`

1. Lines 116–121: take `Absorb/AttentionZero.lean` and `Absorb/AttentionNetworks.lean` out of the
   list "Not yet compared by such a reader", and add a sentence such as: "A twelfth reader (part A,
   24 November) compared `Absorb/AttentionZero.lean` and `Absorb/AttentionNetworks.lean` with
   Theorem 4.2 (i), (ii) of the absorb paper and its proof (report
   `claude/lean-statement-audit-twelfth-a-2026-11-24.md`) and found nothing false, vacuous or
   drifted: generic is almost every weight of the residual network with one null set for all
   skipless networks; the conditions on the number of tokens are the paper's with `L′ = L' + 1`;
   Lean also covers `L = 0` and `ε' ≠ ε`; the paper's (ii) without a mask is (i)."
2. Line 728: take "4.2" out of "Theorems 3.4, 4.2;" (parts (i), (ii) are proved; part (iii) is
   stated, in work, since `479f2f2`), and add "the last sentence of the proof of Theorem 4.2
   (rotary embeddings)". On the same lines, "Theorems 3.4", "Propositions 4.6, 4.7" and "Theorem
   A.13" also look out of date: rows 661, 664 and 666 carry these names as stated. I read only the
   headings of those rows, not their content.
3. Line 668, optional additions: "the residual network may have no block (`L = 0`)"; "(ii) has no
   hypothesis `E D ≠ 0` and needs `d`, `d_in`, `d_out` nonempty"; "the paper's (ii) without a mask
   is (i)"; "in (ii) the null set does not depend on `ε'`".
4. Line 667, optional addition: "(the derivative along the line `τ ↦ τ a b`, not in every
   direction; the product in the order of the blocks; `ξ = 1` for the identity, `ξ = 1/√ε` for
   RMSNorm with `ε > 0`)".

## What I could not check, or did not

- The proofs: not audited, as the brief says. I only ran `#print axioms` on the seven theorems (the
  three standard axioms each) against the compiled library of `/home/claude/lp/lean`, not against a
  build of my own.
- That an additive Haar measure on `Params` is a Lebesgue measure: taken from the sixth report, not
  compiled again.
- The paper: only the text `absorb.txt`, not the PDF. Equation and line numbers are those of the
  text.
- Theorem 4.2 (iii): its statements (`Absorb/ShortSequencesPoly.lean`,
  `Absorb/ShortSequences.lean`) were committed at 14:10 UTC, after I had finished reading; they are
  not in the brief and I did not compare them. I checked the paper's `T = 2` example of (iii)
  numerically only to see that `hn` excludes it. The sentence on rotary embeddings is not stated
  in Lean, so there is nothing to compare.
- When I compiled (about 14:05 UTC, library at `2a488da`) the working copy `/home/claude/lp` differed from `lw` in one
  file, `OneBlock/AttentionGeneric.lean` (work in progress there); it is not a file of this audit.
- The other rows of the index, and the content of rows 661–666.
