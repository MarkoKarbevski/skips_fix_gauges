STATUS: complete

# Seventeenth audit of Lean statements against the papers, part B: local identifiability up to all the symmetries (24 November 2026)

Reader: an independent reader who did not write the statements. Brief:
`/home/claude/proj_up/audit17b_brief_2026-11-24.md`. I audited statements and definitions, not
proofs. I changed no repository file, ran no `lake build`, made no commit and no push. My files are
in `/home/claude/audit17b/`.

Library: `/home/claude/lw/lean` (branch `lean-wip`).

- **Commit at the start: `8a637fe8b9921280e1945ad477d0c9e33c4aa464` (17:57:16 UTC).**
- **Commits read later: `470c4544b4ebefb97f3d6a928c548c6cef008316` (17:59:36), `588a9d0` (18:02:14),
  and at the end `da0be3b2dd85ebb35370df59e925ba5dcdc4bf37` (18:08:05 UTC),** still the head at
  18:12 UTC. Twelve commits were added after the first; the last of them is this head.
- **Did a statement change while I read? No.** By a script of mine (`commits_cmp.py`: statement
  text, docstring, `omit` lines and file header of every public name, `8a637fe` against
  `da0be3b`), for the eight files of the brief and the three earlier files
  (`Dimension/IdentifiableIff.lean`, `Residual/IdentifiableIff.lean`,
  `Dimension/IdentifiableIffTransformer.lean`): no statement, no docstring, no `omit` line and no
  header changed. Only proofs were added, in the three files `…Finite.lean`.
- **Files with `sorry`.**
  - At `8a637fe`: `Dimension/IdentifiableIffFinite.lean` (8), `Residual/IdentifiableIffFinite.lean`
    (14), `Dimension/IdentifiableIffTransformerFinite.lean` (6); the five other files of the brief
    had none. One further file of the library, `OneBlock/LearnedSkipGain.lean` (2), is not in my
    brief.
  - At `470c454` and after: none of the eight files.
  - At `da0be3b`, in the library and outside my brief: `Absorb/AttentionHeadsIdentifiable.lean`,
    `Absorb/RidgeFunctions.lean`, `OneBlock/LearnedSkipTriangularRescale.lean`,
    `OneBlock/LearnedSkipTriangularSmooth.lean`.
- The eight files have 68 public names: 4 definitions and 64 theorems (4, 8, 12, 4, 4 + 8, 8, 14,
  6, as the brief says).
- All 68 depend on `propext`, `Classical.choice`, `Quot.sound` only (by compiling, `Ax.lean`,
  `Ax.out`).

Papers, as text: the skips paper ("S", `skips.txt`) and the dimension paper ("D", `dim.txt`). Line
numbers of `STATEMENTS.md` are those of `da0be3b`.

How I checked.

- "By reading": every public statement and docstring of the eight files, their headers, the
  headers and statements of the three earlier files, the definitions used (`Arch`, `Params`,
  `hidden`, `eval`, `Arch.mlp`, `Arch.gated`, `Arch.attention`, `Arch.sum`, `Arch.attentionMlp`,
  `Arch.attentionGated`, `Params.cob`, `Params.rescale`, `Params.headsQK`, `Params.headsVO`,
  `Params.sumFst`, `Params.sumSnd`, `Params.sumOf`), and the paper passages that the brief names.
- "By a script": my own scripts on the statement texts (`extract.py`, `pair_cmp.py`,
  `ae_shapes.py`, `sig_cmp.py`, `commits_cmp.py`, with their outputs).
- "By compiling": scratch files of mine, compiled with `lake env lean` from `/home/claude/lp/lean`
  (read only; `/home/claude/lw/lean` has no compiled file of `Symmetry/FiniteSymmetries.lean`).
  The sources of `lp` and `lw` were the same (`diff -rq`, at `588a9d0` and at `da0be3b`), and the
  compiled files of the eight modules (17:50 to 17:59 UTC) were newer than their sources. Files:
  `Ax.lean` (axioms, instances), `Sig.lean` (the full signatures), `Normal.lean`, `Normal2.lean`
  (the normal form), `SumSym.lean` (networks with two kinds of block), `NonVac.lean` (the left
  sides hold for networks of the papers). All compile without error and contain no `sorry`.
- "By a computation": `finite_sym_check.py` (numpy, double precision), output
  `finite_sym_check.out`.
- "By hand": a short argument of my own, written where it is used.

**Short answer. Nothing false, nothing vacuous and no drift was found. The finding of the
sixteenth audit is closed:** the first sentence of D Proposition 4.6 and of S Proposition 4.5 is
now stated and proved in the paper's form, in both directions, for every kind of block of the
papers. Three things are described more broadly than they are stated or are out of date:

1. The index still says in six places that the form with the permutations and the sign flips "is
   not stated yet" (lines 178, 592, 678, and the rows at lines 790, 791, 795).
2. "A composition of symmetries in any order has this form" (headers of the new files) is not a
   Lean statement. I compiled the identities that it rests on (20 for the three kinds of block and
   two for networks with two kinds; all hold).
3. That the finite symmetries of a network of attention blocks and MLP or gated blocks preserve
   the function is not a Lean statement (the index says so). I compiled it (three statements).

---------------------------------------------------------------------------------------------------

## Part 1: the drift checks

### Check 1. Generic means almost every parameter, for every Haar measure, on both sides

**Verdict: yes, in all 56 statements (4 + 24 + 28).** (By reading; the shape of all 56 by a
script, `ae_shapes.py`, `ae_shapes.out`: "56 theorems; 0 not of the expected shape".)

- Each of the 52 equivalences has `(μ : Measure (Params …)) [μ.IsAddHaarMeasure]` with `μ` a
  variable, exactly one `∀ᵐ θ ∂μ` on the left of `↔` and one on the right, the same `μ`, and the
  right side begins `(∀ᵐ θ ∂μ, ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U, (∀ x : Matrix T dIn ℝ, eval …`. None is "there
  is a parameter" or "on an open set". One of them:

  ```
  theorem ae_funDim_mlp_skipless_iff_ae_locally_cob_perm_flip
      (hσ : AnalyticOnNhd ℝ σ Set.univ)
      (μ : Measure (Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut))
      [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
      (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
      (∀ᵐ θ ∂μ, funDim (Arch.mlp σ id hid) 0 θ + (L + 1) * Fintype.card d ^ 2
        = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)) ↔
      (∀ᵐ θ ∂μ, ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
        (∀ x : Matrix T dIn ℝ, eval (Arch.mlp σ id hid) 0 θ' x = eval (Arch.mlp σ id hid) 0 θ x) →
          ∃ (p : ∀ ℓ, Equiv.Perm (hid ℓ)) (s : ∀ ℓ, hid ℓ → ℤˣ), ∃ G : Fin (L + 1) → GL d ℝ,
              θ' = ((θ.permUnits p).flipUnits s).cob G G)
  ```
- The four statements of `Dimension/IdentifiableConverseFamily.lean` have an almost-everywhere
  hypothesis (`hloc : ∀ᵐ θ ∂μ, ∃ U ∈ 𝓝 θ, …`) and an almost-everywhere conclusion (`∀ᵐ θ ∂μ,
  Module.finrank ℝ (Params A dIn dOut) ≤ funDim A S θ + …`), for the same variable Haar measure.
  This is meant: "if at generic parameters it is locally identifiable, then at generic parameters
  the lower bound".

### Check 2. The left side and the hypotheses

**Verdict: the left side of each of the 52 new equivalences is, word for word, the left side of
the earlier statement of the same kind; the hypotheses are those of the earlier statement and
nothing else, apart from the family `img` in the 24 statements with `_family`.** (By a script on
the source texts, `pair_cmp.py`, `pair_cmp.out`; a second time on the elaborated signatures, which
also show the instance arguments that come from `variable` lines, `Sig.lean`, `sig_cmp.py`,
`sig_cmp.out`.)

- The script pairs each new name with the earlier name (`_family` taken off; `_perm` or
  `_perm_flip` taken off), splits each statement into hypotheses, left side and right side, and
  prints every difference, token by token.
- **Left sides: 52 of 52 identical.** They are `∀ᵐ θ ∂μ, funDim A 0 θ + ((L + 1) * dim 𝒢 + s) =
  Module.finrank ℝ (Params …)` for skipless networks and `funDim A 1 θ + (dim 𝒢 + s)` for residual
  ones, with `dim 𝒢 = card d ^ 2` or `card d * (card d - 1) / 2` and `s = 0`, `∑ ℓ, card (hid ℓ)`,
  `2 * ∑ ℓ, card (H ℓ) * card (dh ℓ) ^ 2`, or the sum of the last two. This is Definition 4.4 (D)
  / 4.3 (S), as the sixteenth reader found for the earlier files (by reading).
- **Hypotheses, the 24 statements with `_family`:** the only difference in each is the insertion
  of `{ι : Type*} [Countable ι] (img : ι → Params … → Params …) (j₀ : ι) (himg : ∀ θ, img j₀ θ =
  θ)`. No other token differs.
- **Hypotheses, the 28 statements with `_perm` or `_perm_flip`:** identical to the earlier
  statement, 28 of 28, in the source text and in the elaborated signature.
- **Right sides, every difference:**
  - `_family`: `∃ j : ι,` is put in front, and `θ` becomes `(img j θ)` in the place where the
    symmetry is applied (`θ.cob` → `(img j θ).cob`; `(θ.rescale` → `((img j θ).rescale`;
    `((θ.headsQK` → `(((img j θ).headsQK`; for the two parts `θ.sumFst`, `θ.sumSnd` → `(img j
    θ).sumFst`, `(img j θ).sumSnd`).
  - `_perm`: `∃ p : ∀ ℓ, Equiv.Perm (hid ℓ),` (MLP, gated), `∃ q : ∀ ℓ, Equiv.Perm (H ℓ),`
    (attention) or `∃ (q : ∀ ℓ, Equiv.Perm (H ℓ)) (p : ∀ ℓ, Equiv.Perm (hid ℓ)),` (two kinds of
    block) is put in front, and `θ` becomes `(θ.permUnits p)`, `(θ.permUnitsGated p)`,
    `(θ.permHeads q)`, or on the two parts `(θ.sumFst.permHeads q)` and `(θ.sumSnd.permUnits p)`,
    `(θ.sumSnd.permUnitsGated p)`.
  - `_perm_flip`: in addition `(s : ∀ ℓ, hid ℓ → ℤˣ)` and `((θ.permUnits p).flipUnits s)`,
    `((θ.sumSnd.permUnits p).flipUnits s)`.
- Earlier statements with no new form: the four general forms for any real-analytic blocks
  (`ae_funDim_skipless_iff_ae_locally_cob`, `ae_funDim_residual_iff_ae_locally_cob`, each with
  `_rmsNorm`) have a `_family` form and no `_perm` form, rightly (a general block has no named
  finite symmetry); the four statements at one parameter of
  `Dimension/IdentifiableIffTransformer.lean` have neither, rightly (they are not equivalences).
- The four statements of `IdentifiableConverseFamily.lean` against those of
  `IdentifiableConverseCob.lean` (same script, full signatures): the only differences are `{ι :
  Type*} [Countable ι]`, `Ψ : Params A dIn dOut → ι → N → Params A dIn dOut`, `Ω : ι → Set N`,
  `hΨ : ∀ θ i, ContDiffOn ℝ 1 (Ψ θ i) (Ω i)`, and in `hloc` `∃ i, ∃ n ∈ Ω i, …` with `(Ψ θ i n)`.

### Check 3. Is the right side now the paper's Definition 4.5 / 4.4 with all its symmetries?

**Verdict: yes, in the files `…Finite.lean`, for every kind of block of the papers.**

**(a) The maps of `Symmetry/FiniteSymmetries.lean` are the paper's finite symmetries, and they
preserve the function.** (By reading; by hand; by a computation; for networks with two kinds of
block by compiling.)

Paper (D Appendix B, S Appendix A.6): "Permutations of hidden units or heads and sign flips of tanh
hidden units are finite and remove no parameters".

```
def Params.permUnits (θ : Params (Arch.mlp (T := T) (d := d) σ χ hid) dIn dOut)
    (p : ∀ ℓ, Equiv.Perm (hid ℓ)) : … where
  E := θ.E
  read ℓ := Matrix.of fun a i => θ.read ℓ a (p ℓ i)
  write ℓ := Matrix.of fun i a => θ.write ℓ (p ℓ i) a
  D := θ.D
noncomputable def Params.flipUnits (θ : …) (s : ∀ ℓ, hid ℓ → ℤˣ) : … where
  read ℓ := Matrix.of fun a i => (((s ℓ i : ℤˣ) : ℤ) : ℝ) * θ.read ℓ a i
  write ℓ := Matrix.of fun i a => (((s ℓ i : ℤˣ) : ℤ) : ℝ) * θ.write ℓ i a
def Params.permUnitsGated (θ : Params (Arch.gated …) dIn dOut) (p : ∀ ℓ, Equiv.Perm (hid ℓ)) : … where
  read ℓ := Matrix.of fun a j => θ.read ℓ a (Sum.map (p ℓ) (p ℓ) j)
  write ℓ := Matrix.of fun i a => θ.write ℓ (p ℓ i) a
def Params.permHeads (θ : Params (Arch.attention …) dIn dOut) (q : ∀ ℓ, Equiv.Perm (H ℓ)) : … where
  read ℓ := Matrix.of fun a (c : H ℓ × (dh ℓ ⊕ (dh ℓ ⊕ dh ℓ))) => θ.read ℓ a (q ℓ c.1, c.2)
  write ℓ := Matrix.of fun (c : H ℓ × dh ℓ) a => θ.write ℓ (q ℓ c.1, c.2) a
```

| Kind of block | Paper's finite symmetries | Lean | Same? |
|---|---|---|---|
| MLP (tanh, GELU) | permutations of the hidden units of a block | `permUnits`: one permutation per block; read column and write row of a unit move together | yes |
| tanh | sign flips of hidden units | `flipUnits`: read column and write row of a unit times the same sign `1` or `−1` (a unit of `ℤ`) | yes |
| gated (SwiGLU, GeGLU) | permutations of the hidden units | `permUnitsGated`: gate column (`Sum.inl`), value column (`Sum.inr`) and write row move together | yes |
| attention | permutations of the heads of a block | `permHeads`: the query, key and value columns and the output rows of a head move together | yes |
| attention blocks and MLP or gated blocks | both | `Params.sumOf (θ.sumFst.permHeads q) (θ.sumSnd.permUnits p)`, with `.flipUnits s` or `permUnitsGated` on the second part | yes |

- By hand, two hidden units, the swap `p`: the block gives `∑_i σ((h R')_{t,i}) W'_{i,a} = ∑_i
  σ((h R)_{t,p i}) W_{p i,a}`, the same two terms in the other order. Sign flips: `σ(s z) (s w) =
  σ(z) w` for `s = −1` if and only if `σ(−z) = −σ(z)`. Gated: the term of unit `i` is `σ(gate_i)
  value_i W_i`, and all three move with `p`. Two heads: the block is the sum over the heads of
  `P_i h W_{V,i} W_{O,i}`, and each term moves as a whole.
- The four statements `eval_permUnits`, `eval_flipUnits (hσ : ∀ z, σ (-z) = -σ z)`,
  `eval_permUnitsGated`, `eval_permHeads` say exactly this: `eval A S (image of θ) x = eval A S θ
  x`, for all stream matrices `S`, every map `χ` and every input. They are proved. `eval_flipUnits`
  applies to tanh with `Real.tanh_neg` (compiled, `Ax.lean`).
- By a computation (`finite_sym_check.out`; two blocks, two hidden units or two heads of width 2
  per block, three tokens, causal mask for attention, streams `0`, `1` and random, with and
  without RMSNorm; the maps written index by index as in Lean): the largest difference of the
  outputs is at most `1.4 × 10⁻¹³` for `permUnits` (tanh, GELU), `flipUnits` (tanh),
  `permUnitsGated` (SwiGLU, GeGLU) and `permHeads`. Controls differ by at least `0.9`: sign flips
  for GELU, a permutation of the read columns without the write rows.
- **Networks with two kinds of block: the library has no statement that these maps preserve the
  function** (the index row says "no statement of their own"). By compiling (`SumSym.lean`): for
  every `θ`, `q`, `p`, `s`, all stream matrices and every `χ`,
  `eval (Arch.attentionMlp …) S (Params.sumOf (θ.sumFst.permHeads q) (θ.sumSnd.permUnits p)) x =
  eval … S θ x`, the same with `((θ.sumSnd.permUnits p).flipUnits s)` for an odd activation, and
  the same for `Arch.attentionGated` with `permUnitsGated`. Three standard axioms only.

**(b) Every composition of the paper's symmetries, in any order, has the normal form of the right
side.** (By compiling the identities, `Normal.lean`, `Normal2.lean`, `SumSym.lean`; the induction
over the length of a composition by hand.)

The right side is: a finite symmetry first, then a continuous symmetry inside the blocks, then a
change of basis. A composition is brought to this form by moving every change of basis to the
outside, every finite symmetry to the inside, and merging neighbours of one kind. Each step is one
of these identities, all compiled as equalities of parameters:

| Kind | Identity (my names) | What it says |
|---|---|---|
| all | `cob_cob`: `(θ.cob G K).cob G' K' = θ.cob (G * G') (K * K')` | two changes of basis are one (the products are again invertible, orthogonal, or constant along the network) |
| MLP | `cob_permUnits`, `cob_flipUnits` | a change of basis commutes with a permutation and with a sign flip |
| MLP | `flipUnits_permUnits`: `(θ.flipUnits s).permUnits p = (θ.permUnits p).flipUnits (fun ℓ i => s ℓ (p ℓ i))` | a permutation after a sign flip is a sign flip after the permutation |
| MLP | `permUnits_permUnits`, `flipUnits_flipUnits` | two of a kind are one |
| gated | `cob_permUnitsGated`, `cob_rescale` | a change of basis commutes with both |
| gated | `rescale_permUnitsGated`: `(θ.rescale c).permUnitsGated p = (θ.permUnitsGated p).rescale (fun ℓ i => c ℓ (p ℓ i))` | a permutation after a rescaling is a rescaling after the permutation; the factors stay nonzero |
| gated | `permUnitsGated_permUnitsGated`, `rescale_rescale` | two of a kind are one |
| attention | `cob_permHeads`, `cob_headsQK`, `cob_headsVO` | a change of basis commutes with all three |
| attention | `headsQK_permHeads`, `headsVO_permHeads`: `(θ.headsQK K).permHeads q = (θ.permHeads q).headsQK (fun ℓ i => K ℓ (q ℓ i))` | a permutation of the heads after a head change is a head change after the permutation |
| attention | `headsVO_headsQK` | the two head changes commute |
| attention | `permHeads_permHeads`, `headsQK_headsQK`, `headsVO_headsVO` | two of a kind are one |
| two kinds | `sumOf_cob`, `sumFst_sumOf` | a change of basis acts on the two parts; a map on the two parts composes part by part |

So for each kind the set `{cob G (continuous (finite θ))}` is closed under every symmetry of the
paper's list, and the right side is "`θ'` is the image of `θ` under a symmetry: a change of basis,
a symmetry inside a block, or a composition of these". **None of these identities is a statement
of the library;** the headers assert the normal form in words.

**(c) No symmetry of the paper's list is missing for any kind.** (By reading; the sign change by
compiling and by a computation.)

| Kind | Paper's list (D Appendix B, S Appendix A.6) | Lean right side |
|---|---|---|
| tanh | permutations, sign flips, changes of basis | `((θ.permUnits p).flipUnits s).cob G G` (`_perm_flip`) |
| GELU | permutations, changes of basis | `(θ.permUnits p).cob G G` (`_perm`) |
| SwiGLU, GeGLU | permutations, `(e_i, a_i) ↦ (e_i/λ, λ a_i)` with `λ ≠ 0`, changes of basis | `((θ.permUnitsGated p).rescale c).cob G G` with `∀ ℓ i, c ℓ i ≠ 0` |
| attention | permutations of heads, `K, K′ ∈ GL(d_h)` per head, changes of basis | `(((θ.permHeads q).headsQK K).headsVO K').cob G G` |
| attention with MLP or gated blocks (S) | all of the above on the blocks of each kind | `Params.sumOf (((θ.sumFst.permHeads q).headsQK K).headsVO K') (…)` with `θ.sumSnd.permUnits p`, `(θ.sumSnd.permUnits p).flipUnits s` or `(θ.sumSnd.permUnitsGated p).rescale c` |

- Changes of basis: `G : Fin (L + 1) → GL d ℝ` for skipless networks, one `G : GL d ℝ` at all
  hidden states for residual ones; under pre-RMSNorm every orthogonal matrix, also of determinant
  `−1`.
- **The sign change of the value of a gated unit is among the rescalings.** The rescalings are by
  nonzero factors, not by positive ones, and the factor `−1` multiplies the value column and the
  write row by `−1` (compiled, `rescale_neg_one`; computed, difference `8.5 × 10⁻¹⁴`). The sign
  change of the gate is not a symmetry (computed, difference at least `1.1`), and the paper does
  not list it.
- The head changes are by all of `GL(d_h)`, so `K = −1` is among them.

**(d) The forms `_perm_flip` for an activation that is not odd.** (By hand; the header and the
index by reading.)

For GELU the sign flips do not preserve the function: `gelu(−z) = gelu(z) − z`, so a flipped unit
gives `−gelu(z) w + z w` in place of `gelu(z) w` (computed: difference at least `0.9`). The
statement `…_perm_flip` for GELU is still true. It says: `fd = P − k` at almost every parameter if
and only if at almost every `θ` every `θ'` near `θ` with the same function lies in the set of the
images of `θ` under permutations, sign flips and continuous symmetries. For GELU this set contains
parameters that are not symmetric images of `θ`, so the right side is then a weaker condition than
the paper's, and it is not "identifiable up to its symmetries". It is equivalent to the form
`_perm` because both are equivalent to the left side. The paper's form for GELU is `_perm`; the
paper's form for tanh is `_perm_flip`. The form `_perm` for tanh is true with a stronger right
side than the paper's (no sign flips).

- The header of the three files says so: "the forms with the sign flips are the paper's for an odd
  activation (tanh), where the sign flips preserve the function (`eval_flipUnits`). As statements
  they hold for every real-analytic activation." The index row says so too.
- The docstrings of the eight `_perm_flip` statements say "with a real-analytic activation (tanh,
  GELU) […] (the finite symmetries for an odd activation: tanh)". They do not say that for GELU
  the flipped images are not symmetric. One clause more would remove the doubt.

**(e) Are D Proposition 4.6 and S Proposition 4.5 now stated in the paper's form, in both
directions?** (By reading; instances by compiling, `Ax.lean`, `NonVac.lean`.)

**Yes for the first sentence, for every kind of block; the last sentence is in the earlier files
at one parameter.**

| Network | Without normalization | Under pre-RMSNorm (`ε > 0`) |
|---|---|---|
| D, S: skipless tanh | `ae_funDim_mlp_skipless_iff_ae_locally_cob_perm_flip` | `…_cob_rmsNorm_perm_flip` |
| D, S: skipless GELU | `ae_funDim_mlp_skipless_iff_ae_locally_cob_perm` | `…_cob_rmsNorm_perm` |
| D, S: skipless SwiGLU, GeGLU | `ae_funDim_gated_skipless_iff_ae_locally_cob_rescale_perm` | `…_rescale_rmsNorm_perm` |
| D, S: skipless attention | `ae_funDim_attention_skipless_iff_ae_locally_cob_heads_perm` | `…_heads_rmsNorm_perm` |
| S: skipless attention with tanh / GELU blocks | `ae_funDim_attentionMlp_skipless_iff_ae_locally_cob_heads_perm_flip` / `…_heads_perm` | `…_heads_rmsNorm_perm_flip` / `…_heads_rmsNorm_perm` |
| S: skipless attention with SwiGLU, GeGLU blocks | `ae_funDim_attentionGated_skipless_iff_ae_locally_cob_heads_rescale_perm` | `…_rescale_rmsNorm_perm` |
| S: residual tanh / GELU | `ae_funDim_mlp_residual_iff_ae_locally_cob_perm_flip` / `…_perm` | `…_rmsNorm_perm_flip` / `…_rmsNorm_perm` |
| S: residual SwiGLU, GeGLU | `ae_funDim_gated_residual_iff_ae_locally_cob_rescale_perm` | `…_rescale_rmsNorm_perm` |
| S: residual attention | `ae_funDim_attention_residual_iff_ae_locally_cob_heads_perm` | `…_heads_rmsNorm_perm` |
| S: residual attention with tanh / GELU blocks | `ae_funDim_attentionMlp_residual_iff_ae_locally_cob_heads_perm_flip` / `…_perm` | `…_rmsNorm_perm_flip` / `…_rmsNorm_perm` |
| S: residual attention with SwiGLU, GeGLU blocks | `ae_funDim_attentionGated_residual_iff_ae_locally_cob_heads_rescale_perm` | `…_rescale_rmsNorm_perm` |

- The statements are for any real-analytic activation or gate `σ`; tanh, GELU and SiLU enter by
  `analyticOnNhd_tanh`, `analyticOnNhd_gelu`, `analyticOnNhd_silu`. Compiled for tanh without
  normalization and for GELU under pre-RMSNorm (`Ax.lean`).
- `ε = 0` is not covered, and the papers do not ask it: D says "Proposition 4.6 is stated for
  `ε > 0`", and S defines RMSNorm with `ε > 0`.
- Lean asks less than the Scope, as in the earlier files (no `d_out ≥ d`, no `d ≥ 2`, no token, no
  width for residual networks). These are strengthenings.
- **Both readings of the definition are now proved.** With the continuous symmetries alone (the
  earlier files) and with all the symmetries (the new files), each right side is equivalent to the
  equality condition, so the two right sides are equivalent to each other (compiled for skipless
  MLP blocks, `Ax.lean`).
- **What is not covered.**
  1. **"Every symmetry that is needed is then close to the identity."** It is in the earlier files
     at one parameter: for `θ` with `E` and the writes of rank `d` (and the conditions of each
     kind) and `fd(θ) = P − k`, for every neighbourhood `V` of the identity there is a
     neighbourhood `U` of `θ` such that every `θ' ∈ U` with the same function is the image of `θ`
     under continuous symmetries in `V` (`exists_cob_of_eval_eq_skipless`,
     `exists_cob_rescale_of_eval_eq_skipless_gated`, `exists_cob_heads_of_eval_eq_skipless_attention`,
     the four of `Dimension/IdentifiableIffTransformer.lean`, their residual twins, each with
     `_rmsNorm`). **In content this is enough:** under the equality condition `fd(θ) = P − k`
     holds at almost every `θ`, and the rank conditions hold at almost every `θ` within the Scope;
     and a symmetry near the identity is a continuous one, so no permutation and no sign flip is
     needed. **As one Lean statement "if the equality condition holds, then at almost every
     parameter the symmetries can be taken near the identity" it does not exist:** the lemmas "the
     rank conditions hold at almost every parameter" are private (`ae_rank_E_lia`,
     `ae_rank_E_ubt` and others). It exists unconditionally for the networks whose equality
     condition is a theorem (`ae_exists_cob_of_eval_eq_tanh_skipless` and its siblings).
  2. Definitions 4.4 and 4.5 are not Lean definitions; they are written out in each statement (the
     index says so).
  3. The normal form of (b) and the statement of (a) for two kinds of block are not library
     statements.

### Check 4. The statements with a family `img`

**Verdict: plausible, proved, and neither direction is vacuous. I could not break the direction
from local identifiability to the equality condition.** (By hand; instances by compiling.)

```
theorem ae_funDim_gated_skipless_iff_ae_locally_cob_rescale_family
    [Nonempty d] (hσ : AnalyticOnNhd ℝ σ Set.univ)
    (μ : Measure (Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ))
    {ι : Type*} [Countable ι]
    (img : ι → Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut →
      Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (j₀ : ι) (himg : ∀ θ, img j₀ θ = θ) :
    (∀ᵐ θ ∂μ, funDim (Arch.gated σ id hid) 0 θ
        + ((L + 1) * Fintype.card d ^ 2 + ∑ ℓ, Fintype.card (hid ℓ))
      = Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)) ↔
    (∀ᵐ θ ∂μ, ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.gated σ id hid) 0 θ' x = eval (Arch.gated σ id hid) 0 θ x) →
        ∃ j : ι, ∃ c : ∀ ℓ, hid ℓ → ℝ, (∀ ℓ i, c ℓ i ≠ 0) ∧
          ∃ G : Fin (L + 1) → GL d ℝ, θ' = ((img j θ).rescale c).cob G G)
```

- **Why it holds for any maps, by hand.** Fix `θ` with the largest functional dimension `r` (almost
  every `θ`, since the outputs are analytic). Near `θ` the parameters with the same function form
  a manifold of dimension `P − r`. For fixed `θ` and `j`, `img j θ` is one parameter, and its
  images under the continuous symmetries are the image of a smooth map from a manifold of
  dimension `k`. Countably many such images cover a manifold of dimension `P − r` only if `P − r ≤
  k`. With the upper bound `r ≤ P − k` this is the equality condition. How `img j θ` depends on
  `θ` plays no part: the argument is at one `θ` at a time, so `img` needs no continuity and no
  measurability, and it need not be a symmetry.
- **From the equality condition to the right side:** the earlier statement with `j = j₀`. This
  direction uses `himg` and nothing else of `img`.
- **Neither direction is vacuous.**
  - The left side holds for networks of the papers. Compiled (`NonVac.lean`): from
    `ae_funDim_tanh_skipless` (D Theorem 5.2 (i)), `ae_funDim_tanh_residual` and
    `ae_funDim_attention_residual` (S Theorem 4.7), the right sides with the permutations and the
    sign flips follow in one line each.
  - Both sides can fail. By hand: for the activation `σ = 0` (real-analytic) and `L ≥ 1`, `d ≥ 1`,
    the skipless network computes `0`, so `fd = 0 < P − (L + 1) d²` (as `P ≥ (2L + 1) d²`), and
    every `θ'` has the same function while the images of `θ` form a set of dimension at most
    `(L + 1) d²`.
- **Attempts to break "locally identifiable ⟹ equality condition".**
  - `img j θ` independent of `θ`: `ι = Option ℕ`, `img none θ = θ`, `img (some n) θ = pts n` for
    any sequence `pts` of parameters, a dense one included. The statement instantiates
    (`Ax.lean`). The right side then allows, near `θ`, the images of `θ` and of the countably many
    points `pts n`: still countably many sets of dimension at most `k`, so the argument stands.
  - `img j θ` chosen with the axiom of choice inside the set of the parameters with the function
    of `θ`: countably many points of a manifold of dimension `P − r > k` have images that cover a
    set of measure zero in it. No counterexample.
  - **`Countable ι` is the hypothesis that carries the direction.** With an uncountable family
    (one `j` for every parameter with the function of `θ`) the right side would hold always. The
    statements have `[Countable ι]`.
- The statement with `ι = Unit` and `img () θ = θ` is the earlier statement (compiled).

### Check 5. `Dimension/IdentifiableConverseFamily.lean`

**Verdict: the four counts are the paper's, `Ω i` is the set on which the `i`-th family is asked to
be `C¹` and from which its argument is taken, and the statements do not ask the images to be
symmetries.** (By reading; against the earlier file by a script.)

```
theorem ae_finrank_le_funDim_add_of_ae_locally_cob_family (A : Arch T d L)
    (S : Fin L → Matrix d d ℝ)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (hχ : AnalyticOnNhd ℝ A.χ Set.univ)
    (μ : Measure (Params A dIn dOut)) [μ.IsAddHaarMeasure]
    {N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N] [FiniteDimensional ℝ N]
    {ι : Type*} [Countable ι] (Ψ : Params A dIn dOut → ι → N → Params A dIn dOut)
    (Ω : ι → Set N) (hΨ : ∀ θ i, ContDiffOn ℝ 1 (Ψ θ i) (Ω i))
    (hloc : ∀ᵐ θ ∂μ, ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval A S θ' x = eval A S θ x) →
        ∃ i, ∃ n ∈ Ω i, ∃ G : Fin (L + 1) → GL d ℝ, θ' = (Ψ θ i n).cob G G) :
    ∀ᵐ θ ∂μ, Module.finrank ℝ (Params A dIn dOut)
      ≤ funDim A S θ + ((L + 1) * Fintype.card d ^ 2 + Module.finrank ℝ N)
```

| Statement | Changes of basis in `hloc` | Added to `funDim A S θ` | Paper |
|---|---|---|---|
| `…_cob_family` | `G : Fin (L + 1) → GL d ℝ` | `(L + 1) * card d ^ 2 + finrank ℝ N` | `(L + 1) d²`, `dim N` in the place of `s` |
| `…_cob_const_family` | one `G : GL d ℝ`, `cob (fun _ => G) (fun _ => G)` | `card d ^ 2 + finrank ℝ N` | `d²` |
| `…_cob_orthogonal_family` | `Q : Fin (L + 1) → GL d ℝ`, all in `Matrix.orthogonalGroup d ℝ` | `(L + 1) * (card d * (card d - 1) / 2) + finrank ℝ N` | `(L + 1) d(d−1)/2` |
| `…_cob_const_orthogonal_family` | one orthogonal `Q` | `card d * (card d - 1) / 2 + finrank ℝ N` | `d(d−1)/2` |

- `d (d − 1)` is even, so the division of natural numbers is exact.
- **`Ω i`.** A subset of `N` that may depend on `i` and not on `θ`. `hΨ` asks `Ψ θ i` to be `C¹` on
  `Ω i` only, and `hloc` takes `n ∈ Ω i`. In the use it is the set of the nonzero factors or of the
  invertible head matrices, where `c ↦ c⁻¹` is smooth. `Ω i` is not asked to be open or
  measurable; by hand the statement is plausible also then (a map that is `C¹` within a set is
  Lipschitz on countably many pieces of it, so its image has dimension at most `dim N`).
- **The images need not be symmetries.** `Ψ` is any family with `hΨ`; there is no hypothesis `eval
  A S (Ψ θ i n) = eval A S θ`, and `S` is any family of stream matrices. `Ψ θ i` may depend on `θ`
  in any way. The header and the index say so.
- All spaces `N` are one space for all `i`. This loses nothing: families of smaller dimension
  embed.

---------------------------------------------------------------------------------------------------

## Part 2: the statements, file by file

Verdicts: SAME, LEAN STRONGER, LEAN WEAKER, DIFFERENT, PART, FALSE. All 64 theorems are proved at
`da0be3b` (no `sorry`, three standard axioms). **None is FALSE.**

### `Dimension/IdentifiableConverseFamily.lean` (4 theorems)

Paper: D proof of Proposition 4.6, S proof of Proposition 4.5: "With the permutations and the sign
flips, the symmetries form a Lie group of dimension `k` with finitely many components, and the
images of `θ` under it form the image of a manifold of dimension `k` under a smooth map. By Sard's
theorem this image contains no open subset of a manifold of larger dimension, so `P − r ≤ k`".

| Statement | Verdict |
|---|---|
| `ae_finrank_le_funDim_add_of_ae_locally_cob_family` | LEAN STRONGER as a general form (countably many families of any images, any stream matrices, any real-analytic `χ`); PART of the proposition (one direction, the lower bound) |
| `…_cob_const_family`, `…_cob_orthogonal_family`, `…_cob_const_orthogonal_family` | the same |

Notes: Check 5. The paper has finitely many components of a group; Lean has countably many
families that need not form a group.

### `Dimension/IdentifiableIffFamily.lean` (8), `Residual/IdentifiableIffFamily.lean` (12), `Dimension/IdentifiableIffTransformerFamily.lean` (4)

Paper: D Proposition 4.6 with Definitions 4.4, 4.5; S Proposition 4.5 with Definitions 4.3, 4.4.

| Statements | Verdict |
|---|---|
| the 20 statements for MLP, gated and attention blocks and for the two kinds of transformer, each with `_family` | LEAN STRONGER as a general form: for any countably many maps `img j`, one of them the identity. The paper's first sentence is the case in which the `img j` are the finite symmetries (the files `…Finite.lean`) |
| `ae_funDim_skipless_iff_ae_locally_cob_family`, `ae_funDim_residual_iff_ae_locally_cob_family`, each with `_rmsNorm` (any real-analytic blocks, changes of basis alone) | the same for blocks with `s = 0`; true and not the paper's for blocks with `s > 0` (both sides are false there), as the sixteenth reader found for the earlier forms |

Notes.

1. Hypotheses and left sides: Check 2. Meaning: Check 4.
2. The docstrings are right against the statements (all 24 read). The last sentence of each ("the
   permutations of hidden units or heads and the sign flips of tanh units, composed, are finitely
   many such maps") is the same text for every kind, also for the general forms and for gated and
   attention blocks, where there are no tanh units.
3. The header of `Residual/IdentifiableIffFamily.lean` cites "dimension paper, Proposition 4.6" and
   "the upper bounds of Theorem 4.3 (dimension paper)". For residual networks only the skips paper
   applies; the docstrings say "Proposition 4.5 of the skips paper", rightly.

### `Symmetry/FiniteSymmetries.lean` (4 definitions, 8 theorems)

Paper: D Appendix B and S Appendix A.6, "Permutations of hidden units or heads and sign flips of
tanh hidden units are finite and remove no parameters".

| Name | Verdict |
|---|---|
| `Params.permUnits`, `Params.permUnitsGated`, `Params.permHeads` (definitions) | SAME: the permutations of the hidden units, or of the heads, of every block |
| `Params.flipUnits` (definition) | SAME: the sign flips; defined for every activation, a symmetry for an odd one |
| `eval_permUnits`, `eval_permUnitsGated`, `eval_permHeads` | LEAN STRONGER: for every activation or gate, all stream matrices, every `χ`, every mask |
| `eval_flipUnits (hσ : ∀ z, σ (-z) = -σ z)` | LEAN STRONGER: for every odd activation; tanh is one |
| `permUnits_one`, `flipUnits_one`, `permUnitsGated_one`, `permHeads_one` | PART (bookkeeping: the trivial permutation and the signs `1` give `θ` back); true |

Notes: Check 3 (a). "Finite" (finitely many) and "remove no parameters" have no statement; the
first is clear by reading (permutations of a finite type, signs on a finite type); the second is
not a statement of this file. The four definitions are not in `checks/Axioms.lean`; no
definition of the library is, so this is the convention.

### `Dimension/IdentifiableIffFinite.lean` (8), `Residual/IdentifiableIffFinite.lean` (14), `Dimension/IdentifiableIffTransformerFinite.lean` (6)

Paper: D Proposition 4.6, first sentence, with Definitions 4.4, 4.5; S Proposition 4.5, first
sentence, with Definitions 4.3, 4.4.

| Statements | For which blocks | Verdict |
|---|---|---|
| the 8 with `_perm_flip` (MLP blocks; attention with MLP blocks; skipless and residual; with and without `_rmsNorm`) | tanh | SAME as the first sentence of the proposition; fewer hypotheses than the Scope |
| the same 8 | GELU, or any activation that is not odd | DIFFERENT: true, and the right side allows images that are not symmetric (Check 3 (d)); the paper's form for GELU is `_perm` |
| the 8 with `_perm` for MLP blocks and for attention with MLP blocks | GELU | SAME |
| the same 8 | tanh | true; the right side is stronger than the paper's (no sign flips): "⟹" LEAN STRONGER, "⟸" LEAN WEAKER; the paper's form for tanh is `_perm_flip` |
| the 8 with `_rescale_perm` (gated; attention with gated blocks) | SwiGLU, GeGLU | SAME |
| the 4 with `_heads_perm` for attention blocks alone | attention | SAME |

Notes.

1. Hypotheses and left sides: Check 2. The family of symmetries: Check 3.
2. The last sentence of the proposition is not in these statements: Check 3 (e).
3. D Proposition 4.6 is for networks whose blocks are all of one kind, so the residual file and the
   transformer file formalize S Proposition 4.5 only; their docstrings say so. The header of the
   three files is one text and cites both papers.
4. The header says that each statement is the case of the `_family` statement in which the maps
   `img j` are the finite symmetries. I saw this in the proof of the first statement and did not
   read the other proofs.
5. The docstrings are right against the statements (all 28 read).

### The index rows and `checks/Axioms.lean`

- Every public name is in a row at lines 796 to 803, by its name or by a stated abbreviation ("the
  eight names of `Dimension/IdentifiableIff.lean`, each with `_family`"; "the ten names […] each
  with `_perm`, and the four […] also with `_perm_flip`": I counted 10 + 4 = 14, right).
- One abbreviation can be misread: "each also with `_rmsNorm` before the last suffix" (lines 801,
  803). For `…_perm_flip` the name is `…_rmsNorm_perm_flip`, so "before `_perm`" is exact.
- All 64 theorems are in `checks/Axioms.lean` (by a script).
- The rows are right in content. What is out of date is elsewhere in the index: see the
  corrections.

### The headers

- **Consistent in content.** The three earlier headers say "the continuous symmetries of the
  papers" and that the permutations and sign flips "are not in the family: the direction from
  local identifiability to the equality condition is proved here for this smaller family". The new
  headers say that the earlier files have the continuous symmetries only and that the new ones add
  the further images. No sentence of one contradicts another.
- **The earlier three headers do not point forward.** A reader of `Dimension/IdentifiableIff.lean`
  alone learns that the smaller family is proved "here" and not that the paper's family is in
  `…Family.lean` and `…Finite.lean`.
- The titles of the three files `…Family.lean` say "with permutations and sign flips"; the
  statements are for any countably many maps, and the header text says so.
- `Dimension/IdentifiableIffTransformerFamily.lean`, header: a stray line break ("the continuous
  symmetries" / "only. Here").
- The header of `Symmetry/FiniteSymmetries.lean` says "Each preserves the function" of the four
  maps, which is stated and proved, and names the maps on the two parts without a statement.

---------------------------------------------------------------------------------------------------

## What the authors should know

Nothing is false and nothing is vacuous. In order of weight:

1. **The index is out of date in six places.** It still says that the form with the permutations
   and the sign flips is not stated or that the propositions are "in part": lines 178 to 179, 592
   to 600, 678 to 682, and the rows at lines 790, 791 and 795 ("the form with these further images
   is not stated yet"). The rows at lines 796 to 803 state and prove it.
2. **"A composition of symmetries in any order has this form" is asserted in the headers and is not
   a Lean statement.** The reading of the right side as the paper's Definition 4.5 / 4.4 ("or a
   composition of these") rests on it. I compiled the 20 identities that it needs for the three
   kinds of block, and the two for networks with two kinds (Check 3 (b)); all hold. They are short
   and could be library statements.
3. **No Lean statement says that the finite symmetries of a network of attention blocks and MLP or
   gated blocks preserve the function.** The index says so. I compiled the three statements
   (`SumSym.lean`, about 100 lines with the helpers).
4. **The forms `_perm_flip` are the paper's for tanh only.** For GELU they are true with a right
   side that allows images that are not symmetric. The header and the index say it; the docstrings
   say "(tanh, GELU) […] (the finite symmetries for an odd activation: tanh)" and could say it in
   plain words.
5. **"Every symmetry that is needed is then close to the identity"** is in the earlier files at one
   parameter, which is enough in content. There is no public statement "under the equality
   condition, at almost every parameter"; the step that is missing ("the rank conditions hold at
   almost every parameter") is private.
6. **Lean's converse is stronger than the paper's.** It holds for any countably many further
   images of `θ`; they need not be finitely many, form a group or be symmetries. `Countable ι` is
   the hypothesis that carries it.
7. **Both readings of Definition 4.5 / 4.4 are now proved** (continuous symmetries alone; all the
   symmetries), and each right side is equivalent to the equality condition.
8. The earlier three headers do not point to the new files.
9. The branch moved while I read (twelve commits); the three files `…Finite.lean` went from `sorry`
   to proved; no statement, docstring, `omit` line or header of the eleven files changed.

## Corrections for `STATEMENTS.md` (line numbers of `da0be3b`)

1. Lines 790, 791, 795 (the rows of `Dimension/IdentifiableIff.lean`, `Residual/IdentifiableIff.lean`,
   `Dimension/IdentifiableIffTransformer.lean`). Replace "the form with these further images is not
   stated yet" by "the form with these images is stated and proved: the rows of the files
   `…Family.lean` and `…Finite.lean`".
2. Lines 178 to 179. Replace "D Proposition 4.6 and S Proposition 4.5 are "in part" until the form
   with these images is stated and proved" by: "the form with these images is stated and proved
   (`…Family.lean`, `Symmetry/FiniteSymmetries.lean`, and since `470c454` `…Finite.lean`), and a
   seventeenth reader (part B) compared it: nothing false, vacuous or drifted".
3. Lines 592 to 600 ("Not stated yet from the main text" of the dimension paper). Take out "the
   converse direction of Proposition 4.6 […] with the permutations and the sign flips among the
   symmetries". Replace "Proposition 4.6 is proved in one direction, at one parameter" by: "the
   equivalence of Proposition 4.6 is proved at generic parameters with all the symmetries
   (`Dimension/IdentifiableIffFinite.lean`); its last sentence is proved at one parameter".
4. Lines 678 to 682 ("Not stated yet" of the skips paper). Take out "Proposition 4.5 with the
   permutations and the sign flips among the symmetries, in the direction from local
   identifiability to the equality condition (…)". Line 664, "Proposition 4.5 (one direction)":
   add "the equivalence: the rows of `Residual/IdentifiableIffFinite.lean` and
   `Dimension/IdentifiableIffTransformerFinite.lean`".
5. Lines 180 to 188 ("Not yet compared by such a reader"). Take out the eight files of this brief
   (compared at `8a637fe` and `da0be3b`).
6. Lines 801 to 803 (the rows of the three files `…Finite.lean`). Add: "that a composition of the
   symmetries in any order has this form is not a Lean statement (the identities were compiled by
   the seventeenth reader, part B)"; "the last sentence of the proposition is not in these
   statements (the rows of `Dimension/LocalIdentifiability.lean` and its siblings, at one
   parameter)"; in line 801, after "the sign flips preserve the function for an odd one": "for
   GELU the form with the sign flips is true with images that are not symmetric, and the paper's
   form is the one with the permutations alone". The same sentence fits lines 802 and 803.
7. Lines 801 and 803. "each also with `_rmsNorm` before the last suffix" → "each also with
   `_rmsNorm` before `_perm`".
8. Line 800 (`Symmetry/FiniteSymmetries.lean`). After "(no statement of their own)" add: "that
   they preserve the function was compiled by the seventeenth reader, part B".
9. Lines 797 to 799 (the rows of the three files `…Family.lean`). Nothing wrong. Could add: "the
   family must be countable; nothing else is asked of it".
10. Outside the index. Headers of `Dimension/IdentifiableIff.lean`, `Residual/IdentifiableIff.lean`,
    `Dimension/IdentifiableIffTransformer.lean`: after "is proved here for this smaller family"
    add "; with all the symmetries: the files `…Family.lean` and `…Finite.lean`". Header of
    `Residual/IdentifiableIffFamily.lean` and `Residual/IdentifiableIffFinite.lean`: for residual
    networks cite S Proposition 4.5 and Theorem 4.2 only. Header of
    `Dimension/IdentifiableIffTransformerFamily.lean`: join the broken line. Docstrings of the
    eight `_perm_flip` statements: say that for an activation that is not odd the flipped images
    are not symmetric.

## What I could not check

- **The proofs.** I read none as a proof. "Proved" means no `sorry` in the file at `da0be3b` and the
  three standard axioms in the build of `/home/claude/lp/lean`.
- **The build.** I did not build the library and did not recompile the eight files. I compiled my
  scratch files against the compiled files of `/home/claude/lp/lean`, which were newer than their
  sources; the sources of `lp` and `lw` were the same when I compared them.
- **The normal form as one theorem.** I compiled the identities; that every composition reduces
  with them is an induction by hand.
- **Why the statements with a family hold** (Check 4) and why `Ω i` may be any set (Check 5): by
  hand, a sketch of the dimension argument. The statements themselves are proved in Lean.
- **The step from the one-parameter statements to "at almost every parameter"** for the last
  sentence of the proposition: by hand (full rank is generic within the Scope); the Lean lemmas
  for it are private and I did not compile the step.
- **That no further finite symmetry exists** for some kind of block: not a question of these
  statements (they are equivalences that are proved), and I did not study it. I compared with the
  paper's list only.
- **The numerical check**: one random draw per case, double precision, two blocks with two hidden
  units or two heads. It supports the reading of the four definitions and proves nothing.
- **The older files** on which the eight rest (`Dimension/IdentifiableConverse.lean`,
  `Dimension/IdentifiableConverseCob.lean`, the three earlier `iff` files, the files of local
  identifiability, the upper bounds): I read the statements that I quote and did not compare them
  with the papers again; the sixteenth reader did.
- **The papers themselves** beyond the passages that the brief names.

Scratch files: `/home/claude/audit17b/` (`extract.py`, `commits_cmp.py`, `pair_cmp.py`,
`ae_shapes.py`, `sig_cmp.py`, `finite_sym_check.py`, `Ax.lean`, `Sig.lean`, `Normal.lean`,
`Normal2.lean`, `SumSym.lean`, `NonVac.lean`, with their outputs).
