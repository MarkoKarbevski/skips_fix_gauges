STATUS: complete

# Ninth audit of Lean statements against the papers, part C: local identifiability (24 November 2026)

Reader: an independent reader who did not write the statements. Brief:
`/home/claude/proj_up/audit9c_brief_2026-11-24.md`.

Library: `/home/claude/lw/lean` (branch `lean-wip`). The branch moved while I read.

- Commit at the start: `d0d39c411506d3d866e3143452683dfbf70f5b3b` (11:50:04 UTC).
- Commit at the end: `639933f4377485e7b12eacbb0ebe306b8357f080` (11:53:29 UTC).
- Files with `sorry` at the start (whole library, `git grep`): `Dimension/ExpOrbitGated.lean` (2),
  `Dimension/LocalIdentifiabilityGated.lean` (6), `Residual/LocalIdentifiability.lean` (6),
  `Residual/LocalIdentifiabilityGated.lean` (6).
- Files with `sorry` at the end: `Dimension/ExpOrbitGated.lean` (2: `cobExpRescale_zero`,
  `hasStrictFDerivAt_cobExpRescale`). No other file of the library has one.
- Between the two commits the proofs of the three other files were written. No statement, no
  docstring and no file header of the nine files changed: a script compared every public
  declaration (statement and docstring) and every header of the nine files at `d0d39c4` and at
  `639933f` (`/home/claude/audit9c/tools/stmts.py`): all the same.

Papers: the dimension paper ("D", `dim.txt`) and the skips paper ("S", `skips.txt`); numbers from
these texts.

How I checked. "By reading": I read the Lean source and the paper. "By compiling": I compiled
scratch files of my own in `/home/claude/audit9c/` (`Chk.lean`, `Zero.lean`, `One.lean`) with
`lean` 4.36.0 against the compiled library of `/home/claude/lp/lean` (branch `lean-plus`, at
`639933f`; its sources under `SkipsLean/` were the same as those of `lw` by `diff -rq` when I
compiled; later it had two more files, `Depth/InactiveGate.lean` and `Depth/InactiveUnit.lean`,
which are not in this audit). I used `LEAN_PATH`, without `lake`; three short compiles of a few
seconds each. I wrote nothing under `lw`, `lp` or the repository. "By a computation": a Python
script, `/home/claude/audit9c/tools/deriv_check.py` (40 digits).

**Short answer. Nothing false, vacuous or drifted was found.** The nine files have 38 public
names; all are in `STATEMENTS.md`. Generic is `∀ᵐ θ ∂μ` in all 15 corollaries, with the hypotheses
of the paper and one more, at least one token. Local identifiability as Lean writes it is the
paper's definition together with "close to the identity", and is a little stronger than the
definition alone. The general statements are one direction of Proposition 4.6 (D) and
Proposition 4.5 (S), at one parameter, and in that direction they say more than the paper. At
`639933f`, 24 of the 38 names are proved with the three standard axioms; the other 14 (all for
gated blocks) depend on `sorryAx` only through the two statements of `Dimension/ExpOrbitGated.lean`,
which I judged true (one by compiling a proof of my own copy, the other by hand and by a
computation). Three notes and one section of `STATEMENTS.md` are out of date; see the corrections.

---------------------------------------------------------------------------------------------------

## Part 1: the three drift checks

### Check 1. Generic means almost every parameter

**Verdict: yes, in all 15 corollaries. No hypothesis that the papers do not have, except at least
one token (`[Nonempty T]`). For residual networks Lean has one hypothesis fewer than the paper.**

By compiling (`Chk.lean`, the elaborated statements, so that hypotheses from `variable` lines
show). One of them in full:

```
ae_exists_cob_rescale_of_eval_eq_swiglu_skipless :
  ∀ {T d dIn dOut} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut]
    {hid : Fin L → Type} [(ℓ : Fin L) → Fintype (hid ℓ)] [Nonempty T]
    (μ : Measure (Params (Arch.gated silu id hid) dIn dOut)) [μ.IsAddHaarMeasure],
    2 ≤ Fintype.card d → Fintype.card d ≤ Fintype.card dIn → Fintype.card d ≤ Fintype.card dOut →
    (∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) →
    ∀ᵐ θ ∂μ, ∀ V ∈ 𝓝 1, ∀ W ∈ 𝓝 1, ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.gated silu id hid) 0 θ' x = eval (Arch.gated silu id hid) 0 θ x) →
      ∃ G c, (fun ℓ => ↑(G ℓ)) ∈ V ∧ c ∈ W ∧ (∀ ℓ i, 0 < c ℓ i) ∧ θ' = (θ.rescale c).cob G G
```

`μ` is a variable of the statement and any additive Haar measure on the parameters (a Lebesgue
measure: sixth audit, Check 1). The quantifier `∀ᵐ θ ∂μ` stands before `∀ V` and `∀ W`: one set of
measure zero serves for all neighborhoods. No hypothesis is an a.e. statement.

**D Corollary 5.3** ("Without normalization or under pre-RMSNorm with `ε > 0`, in the cases of
Theorem 5.2, let `θ` be generic parameters"; Theorem 5.2: `d_in, d_out ≥ d_model ≥ 2`, blocks of one
kind, "each with at least `d_model` hidden units").

| Hypothesis in Lean (all seven) | In the paper |
|---|---|
| `[Fintype …]`, `[DecidableEq d]`, `hid : Fin L → Type` | finite sets; any `L` |
| `[Nonempty T]` | not said; an input has at least one token (without it the statement is false: with no token every `θ'` has the same function) |
| `(μ) [μ.IsAddHaarMeasure]`, conclusion `∀ᵐ θ ∂μ` | "let `θ` be generic parameters" |
| `hd : 2 ≤ card d`, `hdIn : card d ≤ card dIn`, `hdOut : card d ≤ card dOut` | `d_in, d_out ≥ d_model ≥ 2` |
| `hhid : ∀ ℓ, card d ≤ card (hid ℓ)` | "each with at least `d_model` hidden units" |
| `hε : 0 < ε` (the four with `rmsNorm ε`) | "under pre-RMSNorm with `ε > 0`" |

| Case of Corollary 5.3 | Lean name | File | At `639933f` |
|---|---|---|---|
| (i) tanh, no normalization | `ae_exists_cob_of_eval_eq_tanh_skipless` | `Dimension/LocalIdentifiability.lean` | proved |
| (i) tanh, `ε > 0` | `ae_exists_cob_of_eval_eq_tanh_skipless_rmsNorm` | same | proved |
| (ii) GELU, `ε > 0` | `ae_exists_cob_of_eval_eq_gelu_skipless_rmsNorm` | same | proved |
| (iii) SwiGLU, no normalization | `ae_exists_cob_rescale_of_eval_eq_swiglu_skipless` | `Dimension/LocalIdentifiabilityGated.lean` | rests on the two `sorry` |
| (iii) SwiGLU, `ε > 0` | `…_swiglu_skipless_rmsNorm` | same | rests on the two `sorry` |
| (iii) GeGLU, no normalization | `ae_exists_cob_rescale_of_eval_eq_geglu_skipless` | same | rests on the two `sorry` |
| (iii) GeGLU, `ε > 0` | `…_geglu_skipless_rmsNorm` | same | rests on the two `sorry` |

All seven cases of Corollary 5.3 are stated; none is missing. The corollary itself has no case
for `ε = 0` ("For `ε = 0` we state no such corollary") and none for attention blocks (they are not
in Theorem 5.2). The width hypothesis `hhid` is the one of Theorem 5.2: each proof takes the
functional dimension from the library's statement of Theorem 5.2 with the same four hypotheses
(`ae_funDim_tanh_skipless μ hd hdIn hdOut hhid`, and so on; by reading), and `hhid` is also what
gives the writes the rank `d` at almost every parameter (`ae_rank_E_write μ hdIn hhid`).

**S Corollary 4.9** ("Let the blocks be analytic, with or without pre-RMSNorm, and let `θ` be
generic parameters of the residual network"; analytic blocks are attention, tanh, GELU, SwiGLU and
GeGLU blocks; the scope of Section 2 has `d_hidden ≥ d_model`, `d_in, d_out ≥ d_model ≥ 2`, and
RMSNorm there has `ε > 0`).

| Hypothesis in Lean (all eight) | In the paper |
|---|---|
| `[Nonempty T]` | not said |
| `(μ) [μ.IsAddHaarMeasure]`, conclusion `∀ᵐ θ ∂μ` | "generic parameters" |
| `hd`, `hdIn`, `hdOut` | `d_in, d_out ≥ d_model ≥ 2` |
| `hε : 0 < ε` (the four with `rmsNorm ε`) | RMSNorm of Section 2 |
| no hypothesis on the number of hidden units | the scope has `d_hidden ≥ d_model` |

| Case of Corollary 4.9 | Lean name | File | At `639933f` |
|---|---|---|---|
| tanh, no normalization | `ae_exists_cob_of_eval_eq_tanh_residual` | `Residual/LocalIdentifiability.lean` | proved |
| GELU, no normalization | `ae_exists_cob_of_eval_eq_gelu_residual` | same | proved |
| tanh, `ε > 0` | `ae_exists_cob_of_eval_eq_tanh_residual_rmsNorm` | same | proved |
| GELU, `ε > 0` | `ae_exists_cob_of_eval_eq_gelu_residual_rmsNorm` | same | proved |
| SwiGLU, no normalization | `ae_exists_cob_rescale_of_eval_eq_swiglu_residual` | `Residual/LocalIdentifiabilityGated.lean` | rests on the two `sorry` |
| SwiGLU, `ε > 0` | `…_swiglu_residual_rmsNorm` | same | rests on the two `sorry` |
| GeGLU, no normalization | `ae_exists_cob_rescale_of_eval_eq_geglu_residual` | same | rests on the two `sorry` |
| GeGLU, `ε > 0` | `…_geglu_residual_rmsNorm` | same | rests on the two `sorry` |

Missing: attention blocks (no attention block is defined in Lean). The case `ε = 0` is not a case
of the corollary. There is no width hypothesis, and this is the form of the theorem that gives
the functional dimension: the Lean statements of S Theorem 4.7 (`ae_funDim_tanh_residual`,
`ae_funDim_gelu_residual`, `ae_funDim_swiglu_residual`, `ae_funDim_geglu_residual` and the four
with `_rmsNorm`; `Residual/DepthMlp.lean`, `DepthMlpRMS.lean`, `DepthGated.lean`,
`DepthGatedRMS.lean`) have exactly `hd`, `hdIn`, `hdOut` (and `hε`), for blocks of any widths, and
each corollary calls the one of its kind (by reading the proofs). The constants agree term by
term: `funDim … 1 θ + card d ^ 2`, `+ card d * (card d - 1) / 2`,
`+ (card d ^ 2 + ∑ ℓ, card (hid ℓ))`, `+ (card d * (card d - 1) / 2 + ∑ ℓ, card (hid ℓ))`, equal to
`finrank ℝ (Params …)`: the paper's `P − d² − s` and `P − d(d−1)/2 − s` with `s` the number of
hidden units (`d(d−1)` is even, so the division is exact). So for residual networks Lean says a
little more than the paper: also for blocks with fewer than `d` hidden units.

### Check 2. Local identifiability as written in Lean is the paper's definition

**Verdict: yes. It is Definition 4.5 (D) and Definition 4.4 (S) together with the sentence
"Every symmetry that is needed is then close to the identity", and it implies the definition.**

The Lean text (`exists_cob_of_eval_eq_skipless`, conclusion; by compiling, `Chk.lean`):

```
∀ V ∈ 𝓝 (1 : Fin (L + 1) → Matrix d d ℝ), ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
  (∀ x : Matrix T dIn ℝ, eval A 0 θ' x = eval A 0 θ x) →
    ∃ G : Fin (L + 1) → GL d ℝ, (fun ℓ => (G ℓ : Matrix d d ℝ)) ∈ V ∧ θ' = θ.cob G G
```

and for gated blocks `∀ V ∈ 𝓝 1, ∀ W ∈ 𝓝 (1 : ∀ ℓ, hid ℓ → ℝ), ∃ U ∈ 𝓝 θ, … ∃ G c, … ∈ V ∧ c ∈ W ∧
(∀ ℓ i, 0 < c ℓ i) ∧ θ' = (θ.rescale c).cob G G`.

- *The definition.* With `V` (and `W`) the whole space, this is "there is a neighborhood `U` of
  `θ` such that every `θ' ∈ U` with `F_{θ'} = F_θ` is the image of `θ` under a symmetry": the
  paper's "locally identifiable at `θ`". The symmetries that Lean allows are the changes of basis
  and the positive rescalings only; the paper's definition also allows the finite ones
  (permutations, sign flips, negative rescalings). So the Lean conclusion implies the paper's
  definition and is a little stronger.
- *"Close to the identity".* "For every neighborhood `V` of the identity there is `U`" says that
  the symmetry can be taken as close to the identity as one likes when `θ'` is close enough to
  `θ`. This is the sentence of the propositions, and the last line of the paper's proof ("is the
  image of `θ` under a symmetry close to the identity"). The `1` of `𝓝 1` is the family of
  identity matrices, and for `W` the constant `1` (by compiling, `One.lean`). `V` is a
  neighborhood in the space of all matrices; under pre-RMSNorm the statement adds that every
  `Q_ℓ` is orthogonal.
- *"The same function".* `∀ x : Matrix T dIn ℝ, eval A S θ' x = eval A S θ x`: equality at every
  input with rows `T` and columns `d_in`. This is `F_{θ'} = F_θ` (the networks of these statements,
  without normalization or with `ε > 0`, are defined at every input). `eval` is the library's
  network (`Network/Defs.lean`), with the stream matrices `0` (no skips) or `1` (identity
  matrices: residual; `One.lean`). The topology on the parameters is that of `ℝ^P`.
- *The changes of basis.* `θ.cob G G` (`Symmetry/ChangeOfBasis.lean`, by reading): `E G_0`,
  `G_{ℓ−1}⁻¹ W_read^ℓ`, `W_write^ℓ G_ℓ`, `G_L⁻¹ D`: Proposition 3.2 (D), one matrix per hidden
  state. Under pre-RMSNorm: `(∀ ℓ, ↑(Q ℓ) ∈ Matrix.orthogonalGroup d ℝ)`, the paper's
  `𝒢 = O(d_model)`. Residual networks: `θ.cob (fun _ => G) (fun _ => G)` is `E G`, `G⁻¹ W_read^ℓ`,
  `W_write^ℓ G`, `G⁻¹ D` for every block, the display of Corollary 4.9 (S), with one `G` (one
  orthogonal `Q` under pre-RMSNorm).
- *The rescalings.* `Params.rescale` (`Dimension/RescaleAction.lean`, by reading): the value column
  `Sum.inr i` of the read of block `ℓ` is multiplied by `(c ℓ i)⁻¹`, the write row `i` by `c ℓ i`;
  the gate columns, `E` and `D` stay. Appendix B (D): "SwiGLU, GeGLU, ReGLU:
  `(e_i, a_i) ↦ (e_i/λ, λ a_i)`, `λ ≠ 0`", with `e_i` the value column and `a_i` the write row. The
  same, with `c = λ`: the column is divided and the row is multiplied. "Close to 1" is `c ∈ W`;
  `0 < c ℓ i` is added (it follows for small `W`).
- *"Or a composition of these".* The Lean order is "rescale, then change the basis". The two
  commute: `(θ.rescale c).cob G G = (θ.cob G G).rescale c` (by compiling, `Zero.lean`,
  `audit_rescale_cob_comm`, three standard axioms), as the paper says in the proof of Theorem 4.3.
  A product of changes of basis is one change of basis and a product of rescalings is one
  rescaling (by reading the definitions). So every composition of changes of basis and rescalings
  has the Lean form.

### Check 3. The equality condition as a hypothesis

**Verdict: the general statements are one direction of the proposition (from the equality
condition to local identifiability), at one parameter. In that direction the pointwise form is
stronger than the paper's. The index and the docstrings say "from the equality condition to local
identifiability, at one parameter" and "Not stated: the converse direction"; this is honest.
`funDim` is the library's `funDim`.**

The eight general statements and their hypotheses (by compiling, `Chk.lean`):

| Lean name | Network | Hypotheses at the one `θ` | `k` in `funDim … θ + k = finrank ℝ (Params …)` |
|---|---|---|---|
| `exists_cob_of_eval_eq_skipless` | any `Arch` with `χ = id`, real-analytic `f_ℓ`, no skips | `E` and every write of rank `d` | `(L + 1) * card d ^ 2` |
| `exists_cob_of_eval_eq_skipless_rmsNorm` | `χ = rmsNorm ε`, `0 < ε` | the same | `(L + 1) * (card d * (card d - 1) / 2)` |
| `exists_cob_rescale_of_eval_eq_skipless_gated` | `Arch.gated σ id hid`, `σ` real-analytic | the same, and no value column of a read zero | `(L + 1) * card d ^ 2 + ∑ ℓ, card (hid ℓ)` |
| `exists_cob_rescale_of_eval_eq_skipless_gated_rmsNorm` | `Arch.gated σ (rmsNorm ε) hid` | the same | `(L + 1) * (card d * (card d - 1) / 2) + ∑ ℓ, card (hid ℓ)` |
| `exists_cob_of_eval_eq_residual` | any `Arch` with `χ = id`, identity skips | `E` of rank `d` | `card d ^ 2` |
| `exists_cob_of_eval_eq_residual_rmsNorm` | `χ = rmsNorm ε`, `0 < ε` | `E` of rank `d` | `card d * (card d - 1) / 2` |
| `exists_cob_rescale_of_eval_eq_residual_gated` | `Arch.gated σ id hid` | `E` of rank `d`, no value column zero | `card d ^ 2 + ∑ ℓ, card (hid ℓ)` |
| `exists_cob_rescale_of_eval_eq_residual_gated_rmsNorm` | `Arch.gated σ (rmsNorm ε) hid` | the same | `card d * (card d - 1) / 2 + ∑ ℓ, card (hid ℓ)` |

- `funDim A 0 θ` and `funDim A 1 θ` are the library's `funDim` of `Dimension/Functional.lean`, the
  maximum of the rank of the Jacobian over all finite batches (sixth audit, Check 2). The proof of
  `exists_mem_orbit_of_eval_eq` takes a batch on which the rank is `funDim`
  (`exists_jacobianRank_eq_funDim`).
- The rank conditions are those that the proof of Lemma B.1 (D) and of Lemma A.18 (S) uses at a
  generic `θ`: "`E` has rank `d_model`", "`W_write` has rank `d_model`", "no column of a generic
  `W_read` vanishes" (for a gated block the value columns, which the rescaling moves). For a
  residual network one `G` acts at all hidden states and `E G = E` already gives `G = I`, so the
  writes are not needed (S, proof of Lemma A.18: "In a residual network the `G_ℓ` are equal").
- **Which part of the proposition.** The paper: "A network satisfies the equality condition if and
  only if, at generic parameters, it is locally identifiable up to its symmetries. Every symmetry
  that is needed is then close to the identity." Lean has the direction "if the equality condition
  holds, then locally identifiable, with symmetries close to the identity", in this form: at
  every single `θ` that has the rank conditions and `fd(θ) + k = P`. Lean does not have the
  converse (the paper proves it with Sard's theorem), has no attention blocks, and has no
  statement of the form "if `fd(θ) + k = P` at almost every `θ`, then local identifiability at
  almost every `θ`"; the corollaries go from Theorem 5.2 (D) or Theorem 4.7 (S) to almost every
  `θ` directly.
- **Stronger or weaker.** In its direction the pointwise form is stronger than the paper's. It
  gives the paper's direction at once: if `fd(θ) + k = P` at almost every `θ`, and the rank
  conditions hold at almost every `θ` (`ae_rank_E_write` for `d_in ≥ d` and at least `d` hidden
  units, `ae_value_ne_zero`), then the conclusion holds at almost every `θ`; this is how the 15
  corollaries are proved. It says more in four ways: (1) it holds at every `θ` with the named
  conditions, not on an unnamed set of full measure; (2) it does not ask that `fd(θ)` be the
  largest rank that occurs at any parameters; (3) it is for every real-analytic `f_ℓ` (for gated
  blocks, every real-analytic gate), not only for the four kinds of block; (4) it has no hypothesis
  on `d`, `d_in`, `d_out`, the widths or the number of tokens beyond the rank conditions. It is
  not weaker than the paper's direction in any respect for MLP and gated blocks.
- **Honesty of the index and the docstrings** (by reading). Index rows 226, 231, 232, 233: "from
  the equality condition to local identifiability, at one parameter", and "Not stated: the
  converse direction". File headers: "The direction of Proposition 4.6 from the equality
  condition to local identifiability, at one parameter" and "Not stated here: the converse
  direction of Proposition 4.6 (it uses Sard's theorem)". Docstrings of the eight statements:
  "from the equality condition to local identifiability", "if `E` and the writes have rank `d`
  and `fd(θ) = P − …`". The note at lines 432-437 says that Definitions 4.4 and 4.5 are not Lean
  definitions. All honest. Three places of the index are out of date (corrections 2, 3, 4).

---------------------------------------------------------------------------------------------------

## Part 2: the statements, file by file

"Proved": no `sorry`, and `#print axioms` shows `propext`, `Classical.choice`, `Quot.sound` only
(by compiling, `Chk.lean`, at `639933f`).

| Paper statement or proof piece | Lean names (file) | Verdict | The difference |
|---|---|---|---|
| D proof of Proposition 4.6 (and S proof of Proposition 4.5), "By the constant rank theorem … `O` is open in `Z`, since the two have the same dimension" | `exists_mem_orbit_of_level_set` (`Generic/LevelSetOrbit.lean`) | **DIFFERENT in form, LEAN STRONGER as a proof piece**; true (proved) | No manifolds. `F` strictly differentiable at the one point `θ₀`; no constant rank near `θ₀`. Note 1. |
| D proof of Proposition 4.6 and S proof of Proposition 4.5, from the equality condition to local identifiability, for any family of symmetries | `exists_mem_orbit_of_eval_eq` (`Dimension/OrbitNetwork.lean`) | **PART** (one direction, one parameter); in it **LEAN STRONGER**; true (proved) | Any stream matrices, any real-analytic `f_ℓ`, `χ`; a family `Φ` with an injective strict derivative at `0` in the place of the Lie group. |
| D proof of Proposition 4.6, "the map that sends an element of the group to the image of `θ` under it is an immersion near the identity", changes of basis | `expGL`, `coe_expGL`, `coe_expGL_inv`, `exp_mem_orthogonalGroup_of_transpose_eq_neg`, `hasStrictFDerivAt_matrix_exp_zero`, `cobExp`, `hasStrictFDerivAt_cobExp`, `cobExp_zero` (`Dimension/ExpOrbit.lean`) | **PART** of the proof; true (proved) | The group in the chart `m ↦ exp m`. The derivative at `0` is `cobDir θ m` = `(E m_0, −m_{ℓ−1} W_read^ℓ, W_write^ℓ m_ℓ, −m_L D)`; by hand the same. That the derivative is injective is `cobDir_injective` (Lemma B.1, an older file). |
| D Appendix B, "The symmetries inside the blocks", SwiGLU and GeGLU: `(e_i, a_i) ↦ (e_i/λ, λ a_i)`, `λ ≠ 0` | `Params.rescale`, `eval_rescale_params` (`Dimension/RescaleAction.lean`) | **SAME** (proved) | For every gate `σ`, every `χ` and all stream matrices. |
| The same proof piece for gated blocks, with the rescalings | `cobExpRescale`, `cobExpRescale_zero`, `hasStrictFDerivAt_cobExpRescale` (`Dimension/ExpOrbitGated.lean`) | **PART** of the proof; **not proved** (`sorry`, two); judged true. Note 2. | Chart `(m, α) ↦ (exp m_ℓ, e^{α_{ℓ,i}})`; derivative `cobDir θ m + rescaleDir θ α`. |
| D Definition 4.5, S Definition 4.4 | no Lean definition; written out in each statement | **SAME**, with "close to the identity" built in | Check 2. |
| **D Proposition 4.6**, tanh and GELU blocks (`s = 0`) | `exists_cob_of_eval_eq_skipless`, `exists_cob_of_eval_eq_skipless_rmsNorm` (`Dimension/LocalIdentifiability.lean`) | **PART**: one direction, at one parameter; in it **LEAN STRONGER**; true (proved) | Check 3. Not stated: the converse; attention blocks. |
| **D Proposition 4.6**, SwiGLU and GeGLU blocks | `exists_cob_rescale_of_eval_eq_skipless_gated`, `…_gated_rmsNorm` (`Dimension/LocalIdentifiabilityGated.lean`) | **PART**, as above; proofs written, rest on the two `sorry` | Any real-analytic gate. |
| **D Corollary 5.3**, tanh (n), tanh (+), GELU (+) | the three `ae_exists_cob_of_eval_eq_…` (`Dimension/LocalIdentifiability.lean`) | **SAME** (proved) | One hypothesis more: at least one token. |
| **D Corollary 5.3**, SwiGLU and GeGLU, (n) and (+) | the four `ae_exists_cob_rescale_of_eval_eq_…_skipless…` (`Dimension/LocalIdentifiabilityGated.lean`) | **SAME**; proofs written, rest on the two `sorry` | At least one token; `0 < c` added. |
| **S Proposition 4.5**, residual networks, tanh and GELU blocks | `exists_cob_of_eval_eq_residual`, `exists_cob_of_eval_eq_residual_rmsNorm` (`Residual/LocalIdentifiability.lean`) | **PART**: one direction, at one parameter; in it **LEAN STRONGER**; true (proved) | Only `E` of rank `d`. The skipless half of S Proposition 4.5 is D Proposition 4.6 (rows above). |
| **S Proposition 4.5**, residual networks of SwiGLU and GeGLU blocks | `exists_cob_rescale_of_eval_eq_residual_gated`, `…_gated_rmsNorm` (`Residual/LocalIdentifiabilityGated.lean`) | **PART**, as above; proofs written, rest on the two `sorry` | Any real-analytic gate. |
| **S Corollary 4.9**, tanh and GELU blocks | the four `ae_exists_cob_of_eval_eq_…_residual…` (`Residual/LocalIdentifiability.lean`) | **PART** of the corollary (no attention blocks); for these blocks **LEAN STRONGER**; true (proved) | Blocks of any widths; at least one token. |
| **S Corollary 4.9**, SwiGLU and GeGLU blocks | the four `ae_exists_cob_rescale_of_eval_eq_…_residual…` (`Residual/LocalIdentifiabilityGated.lean`) | **PART**, as above; proofs written, rest on the two `sorry` | The same. |

### Notes

**Note 1. `exists_mem_orbit_of_level_set` is true as written, and it needs less than the paper's
proof uses.** Statement (by compiling):

```
HasStrictFDerivAt F F' θ₀ → HasStrictFDerivAt Φ Φ' 0 → Φ 0 = θ₀ → Function.Injective Φ' →
  (∀ᶠ m in 𝓝 0, F (Φ m) = F θ₀) → finrank ℝ (ker F') = finrank ℝ M →
  ∀ V ∈ 𝓝 0, ∃ U ∈ 𝓝 θ₀, ∀ θ' ∈ U, F θ' = F θ₀ → ∃ m ∈ V, Φ m = θ'
```

for finite-dimensional real spaces `P`, `M`, `Y`. It is proved with the three standard axioms. I
also read the proof and followed it by hand: `F' ∘ Φ' = 0`, so the range of `Φ'` is the kernel of
`F'` (equal dimensions); with a left inverse `Λ` of `Φ'`, the map `θ ↦ (F θ, Λ(θ − θ₀))` has an
injective strict derivative at `θ₀` and is injective near `θ₀`; `m ↦ Λ(Φ m − θ₀)` has the
derivative `id` and covers a neighborhood of `0`; so a `θ'` near `θ₀` on the level set has the
same image as some `Φ m`, and is `Φ m`. The hypotheses against the paper's proof:

- `hinj` (the derivative of the orbit map at `0` is injective) is "It acts locally freely at `θ`,
  so the map … is an immersion near the identity". Lemma B.1 in Lean is this injectivity
  (`cobDir_injective`, `cobDir_add_rescaleDir_injective`).
- `hconst` (`F ∘ Φ` is constant near `0`) is "`O ⊂ Z`": the symmetries preserve the function.
- `hdim` (the kernel of the Jacobian at `θ₀` has the dimension of `M`) is "`r = P − k`", at the
  one point `θ₀`.
- Not needed, though the paper's proof uses them: that `r` is the largest rank at any parameters,
  the lower semicontinuity of the rank, the constant rank theorem, and the step "for any further
  input `x`, the Jacobian on `X ∪ {x}` has rank `r` on `U` as well". The Lean proof of
  `exists_mem_orbit_of_eval_eq` uses the equality of the functions only on one finite batch on
  which the rank is `fd(θ)` (by reading: `heq (X i)`).

The hypotheses can hold together (they hold in the proved corollaries), so the statement is not
vacuous.

**Note 2. The two statements of `Dimension/ExpOrbitGated.lean` (`sorry` at `639933f`).**

- `cobExpRescale_zero : cobExpRescale θ 0 = θ`. True. By compiling: my own copy of the statement
  is proved in `/home/claude/audit9c/Zero.lean` (`audit_cobExpRescale_zero`, eleven lines, three
  standard axioms): `e^0 = 1`, the rescaling by `1` is the identity, then `cobExp_zero`.
- `hasStrictFDerivAt_cobExpRescale`: "strictly differentiable at `0` with the derivative
  `(m, α) ↦ cobDir θ m + rescaleDir θ α`". By hand, component by component, from the definitions
  (`cobExpRescale θ (m, α) = (θ.rescale (e^α)).cob (exp m) (exp m)`):
  - `E`: `E exp(m_0)`; derivative `E m_0`. `cobDir`: `θ.E * X 0`; `rescaleDir`: `0`.
  - read of block `ℓ`: `exp(−m_{ℓ−1}) R(α)`, with `R(α)` the read whose value column `i` is
    `e^{−α_{ℓ,i}} e_i`; derivative `−m_{ℓ−1} W_read^ℓ` plus, on the value column `i`,
    `−α_{ℓ,i} e_i`. `cobDir`: `−(X ℓ.castSucc * θ.read ℓ)`; `rescaleDir`: `0` on the gate columns,
    `−(α ℓ i) * θ.read ℓ k (Sum.inr i)` on the value columns.
  - write of block `ℓ`: `diag(e^{α_ℓ}) W_write^ℓ exp(m_ℓ)`; derivative `W_write^ℓ m_ℓ` plus, on
    row `i`, `α_{ℓ,i} a_i`. `cobDir`: `θ.write ℓ * X ℓ.succ`; `rescaleDir`:
    `α ℓ i * θ.write ℓ i k`.
  - `D`: `exp(−m_L) D`; derivative `−m_L D`. `cobDir`: `−(X (Fin.last L) * θ.D)`; `rescaleDir`: `0`.

  The claimed derivative is right. The map is a composition of the two exponentials, an inverse
  at `1` and products, so it is strictly differentiable at `0`. By a computation
  (`deriv_check.py`: `d = 3`, `d_in = 4`, `d_out = 2`, `L = 2`, 2 and 4 hidden units, random `θ`,
  `m`, `α`): the largest entry of `(Φ(t p) − θ)/t − (cobDir θ m + rescaleDir θ α)` is
  `1.2·10⁻³, 1.2·10⁻⁶, 1.2·10⁻⁹, 1.2·10⁻¹²` for `t = 10⁻³, 10⁻⁶, 10⁻⁹, 10⁻¹²`. This agrees with
  the statement and does not prove it. No machine proof of this statement yet.

The twelve statements for gated blocks (`Dimension/LocalIdentifiabilityGated.lean`,
`Residual/LocalIdentifiabilityGated.lean`) have no `sorry` of their own at `639933f` and depend on
`sorryAx` only through these two (by compiling: `#print axioms`; and no other `sorry` is in the
library).

**Note 3. Degenerate cases.** The six general statements without rescalings are proved for all
index types, so they are true in every degenerate case; the six with rescalings follow from the
same proved statements and from Note 2, with no case distinction. What they say there (by hand):

- *No token.* Every `θ'` has the same function and `fd(θ) = 0`, so the hypothesis says `k = P`;
  then the orbit map is a local homeomorphism and every `θ'` near `θ` is in the orbit. True, and
  of no interest. The corollaries have `[Nonempty T]`; without it they would be false.
- *`L = 0`.* The network is `x ↦ χ(xE) D`, the families `G` have one member, and a network without
  skips and a residual one are the same. Without normalization the statement is the uniqueness of
  a factorization of rank `d` up to one invertible matrix. The corollaries hold for `L = 0` (so do
  Theorems 5.2 and 4.7 in Lean).
- *`d` with one element.* Without normalization `G_ℓ` is a nonzero number near `1`; nothing
  special. Under pre-RMSNorm `card d * (card d - 1) / 2 = 0`, the space of antisymmetric matrices
  is `0`, and the only orthogonal matrix near the identity is `1`. For blocks without rescalings
  the hypothesis is `fd(θ) = P` and the conclusion says: every `θ'` near `θ` with the same
  function is `θ` itself. This is true (a map with an injective derivative is injective near the
  point), and it is what the Lean proof gives (the orbit is the point `θ`). The finite group
  `O(1) = {±1}` does not enter: `−1` is not near the identity. The corollaries have `d ≥ 2`.
- *`d` empty.* The parameters form one point; trivially true.
- *No hidden unit in a block.* Without skips the write of that block has rank `0`, so the
  hypothesis on the writes forces `d` to be empty; trivially true. With identity skips the block
  is the identity, has no parameter and no rescaling, and the statement is that of the network
  without it. The corollaries for residual networks allow this (no width hypothesis), as the Lean
  Theorem 4.7 does.
- Natural-number arithmetic: `card d * (card d - 1) / 2` is exact, also for `card d = 0`
  (`0 - 1 = 0`).

**Note 4. Private copies.** `Dimension/LocalIdentifiability.lean` has private copies (`expGL_li`,
`cobExp_li`, `hasStrictFDerivAt_cobExp_li`, `exists_cobExp_of_eval_eq_li`, …) of what
`Dimension/ExpOrbit.lean` and `Dimension/OrbitNetwork.lean` now state publicly; the header of
`ExpOrbit.lean` says so. The public statements are the same in content. This is housekeeping, not
a matter of statements.

---------------------------------------------------------------------------------------------------

## What the authors should know

Nothing false, vacuous or drifted. In order of weight:

1. **Two statements are still `sorry`** (`cobExpRescale_zero`, `hasStrictFDerivAt_cobExpRescale`),
   and the twelve statements for SwiGLU and GeGLU blocks rest on them: Corollary 5.3 (iii) in its
   four cases, Corollary 4.9 for SwiGLU and GeGLU in its four cases, and the four general
   statements. Both are true as far as I can check (Note 2). The index says "in work" for these
   three files, which is right.
2. **The index is out of date in three places** (corrections 2, 3, 4): the skips section still
   says that Proposition 4.5 and Corollary 4.9 are not stated, and the two rows for the skips paper
   stand in the section of the dimension paper.
3. **For the papers: the direction from the equality condition to local identifiability holds at
   every single parameter, with a shorter proof.** The Lean proof needs `fd(θ) = P − k` and the
   rank conditions of Lemma B.1 at the one `θ`, and the inverse function theorem. It does not use
   the constant rank theorem, the lower semicontinuity of the rank, the largest rank `r` over all
   parameters, or the step with a further input `x`; and it shows that equality of the outputs on
   one finite batch (one on which the rank is `fd(θ)`) is enough. The papers may want to say this,
   or keep their proof.
4. **For residual networks Lean has no width hypothesis** (Corollary 4.9 for blocks of any
   widths, as the Lean Theorem 4.7), and the general statements need only `E` of rank `d` (and no
   zero value column). The paper's scope has `d_hidden ≥ d_model`.
5. **The 15 corollaries have one hypothesis that the papers do not say: at least one token.** It
   is needed.
6. **Not in Lean:** the converse direction of Proposition 4.6 (D) and Proposition 4.5 (S);
   attention blocks (Proposition 4.6, Proposition 4.5, Corollary 4.9). All seven cases of
   Corollary 5.3 are stated.
7. The general statements are for every real-analytic `f_ℓ` and every real-analytic gate. So they
   also apply to GELU blocks without normalization: at every `θ` with `E` and the writes of rank
   `d` and `fd(θ) = P − (L+1)d²` (the equality that Conjecture 1 of D asserts at generic
   parameters), local identifiability at `θ` follows from `exists_cob_of_eval_eq_skipless`.

## Corrections for `STATEMENTS.md` (lines at `639933f`)

1. Lines 83-96, "Not yet compared by such a reader …": remove from the list
   `Generic/LevelSetOrbit.lean`, `Dimension/LocalIdentifiability.lean`,
   `Dimension/OrbitNetwork.lean`, `Dimension/RescaleAction.lean`,
   `Residual/LocalIdentifiability.lean`, `Dimension/LocalIdentifiabilityGated.lean`,
   `Residual/LocalIdentifiabilityGated.lean`, `Dimension/ExpOrbit.lean` and
   `Dimension/ExpOrbitGated.lean`. They are compared now (ninth reader, part C, 24 November 2026:
   14 paper statements and proof pieces against 38 Lean names; none false, vacuous or changed in
   meaning; the two statements of `Dimension/ExpOrbitGated.lean` are `sorry` and were judged by
   hand, by a computation, and one of them by compiling a copy).
2. Lines 498-506 (skips paper, "Not stated yet from the main text"): "Definitions 4.3, 4.4 and
   Proposition 4.5" and "Corollaries 4.9 and 4.10" are out of date. Say instead: Definitions 4.3
   and 4.4 are not Lean definitions (they are written out, as in the dimension paper);
   Proposition 4.5 is stated in one direction, at one parameter (rows of
   `Residual/LocalIdentifiability.lean` and `Residual/LocalIdentifiabilityGated.lean`; the skipless
   half is the rows for D Proposition 4.6); not stated: its converse, and attention blocks;
   Corollary 4.9 is stated for tanh, GELU, SwiGLU and GeGLU blocks and not for attention blocks;
   Corollary 4.10 is not stated.
3. Lines 231 and 233: these two rows are statements of the skips paper and stand in the section
   "Dimension paper" (lines 143-441). Move them to the section "Skips paper", or point to them
   from there.
4. Lines 432-437 (dimension paper, "Not stated yet"): "Proposition 4.6 and Corollary 5.3 for
   attention blocks": Corollary 5.3 has no case for attention blocks (it is "in the cases of
   Theorem 5.2"). Say "Theorem 4.3, Theorem 5.1 and Proposition 4.6 for attention blocks", and add:
   "Proposition 4.6 is stated in one direction, at one parameter; Corollary 5.3 is stated in all
   its seven cases". Add `Residual/LocalIdentifiability.lean` and
   `Residual/LocalIdentifiabilityGated.lean` to the files that write out local identifiability.
5. Line 226: "Not stated: the converse direction of Proposition 4.6, SwiGLU, GeGLU and attention
   blocks". SwiGLU and GeGLU blocks are in the row of `Dimension/LocalIdentifiabilityGated.lean`
   (line 232). Say "Not stated: the converse direction, attention blocks; SwiGLU and GeGLU blocks:
   the row of `Dimension/LocalIdentifiabilityGated.lean`".
6. Lines 226, 231, 232, 233: add "at least one token" for the corollaries (`[Nonempty T]`), as
   other rows of the index do.
7. Lines 231 and 233: add "blocks of any widths (no hypothesis on the number of hidden units), as
   in the Lean statements of Theorem 4.7; the paper's scope has `d_hidden ≥ d_model`".
8. Lines 232 and 233, status "in work": more exactly, "proofs written at `639933f`; they rest on
   the two `sorry` of `Dimension/ExpOrbitGated.lean`".
9. Lines 226, 231, 232, 233 (or one note): the general statements hold at every `θ` with the
   named conditions and for every real-analytic `f_ℓ` or gate; they have no hypothesis on `d`,
   `d_in`, `d_out` or the widths; "the same function" is equality at every input; the Lean
   conclusion allows only changes of basis and positive rescalings near the identity, which
   implies Definition 4.5 (D) and 4.4 (S).
10. Line 225: add "no constant rank near `θ₀` is assumed: `F` is strictly differentiable at the
    one point `θ₀`".
11. Line 232 or 228: add "the rescaling and the change of basis commute, so the order in
    `(θ.rescale c).cob G G` does not matter" (checked by compiling in the audit; not a statement
    of the library).

## What I could not check

- **`hasStrictFDerivAt_cobExpRescale`**: by hand and by a computation only; no machine proof. The
  twelve statements for gated blocks are therefore "proved from two statements of which one is
  judged true by hand".
- **The proofs** of the proved files: I read the proofs of `exists_mem_orbit_of_level_set` and
  `exists_mem_orbit_of_eval_eq` and the last steps of the corollaries (which statements of
  Theorem 5.2 and Theorem 4.7 they call). The rest I did not read line by line; I rely on Lean and
  on the axiom check.
- **Older statements that these rest on** (`cobDir`, `cobDir_injective`, `rescaleDir`,
  `eval_rescale`, `cobDir_add_rescaleDir_injective`, `eval_cob_skipless`, `eval_cob_rmsNorm`,
  `eval_cob_residual`, `Params.cob`, `eval`, `funDim`, `ae_rank_E_write`, `ae_value_ne_zero`, the
  statements of Theorem 5.2 and of S Theorem 4.7): I read their definitions and statements, and
  `#print axioms` gives the three standard axioms for the fifteen `ae_funDim_…` statements that
  the corollaries call. I did not compare them with the papers again (earlier audits did).
- **`eval_cob_residual_rmsNorm`** (`Residual/LearnedSkips.lean`, used by the residual statements
  under pre-RMSNorm): I read its statement (one orthogonal `Q` at all hidden states preserves the
  function of a residual network with `χ = rmsNorm ε`); I did not compare it with the paper again.
- **The converse direction** and **attention blocks**: not in Lean, so nothing to compare.
- **`lake build`**: not run, as the brief asks. What I compiled, I compiled against the library
  of `/home/claude/lp/lean`, which its owner built.
- **The PDFs**: I read the text files `dim.txt` and `skips.txt`, not the PDFs.

Scratch files: `/home/claude/audit9c/` (`Chk.lean`, `Chk.out`, `Zero.lean`, `One.lean`,
`tools/stmts.py`, `tools/deriv_check.py`, `snap_d0d39c4/`).
