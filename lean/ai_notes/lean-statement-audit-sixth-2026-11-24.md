STATUS: complete

# Sixth audit of Lean statements against the papers (24 November 2026)

Reader: an independent reader who did not write the statements. Brief:
`/home/claude/proj_up/audit6_brief_2026-11-24.md`.

Library: `/home/claude/lw/lean` (branch `lean-wip`). Commit at the start: `6480ce9`. Commit at the
end: `0d967ff`. Between the two (`git -C /home/claude/lw diff 6480ce9 HEAD --stat -- lean`):

- `Depth/RayInduction.lean` and `Depth/FrozenFar.lean`: the proofs were written. The three public
  statements (`ray_induction`, `ray_induction_matrix`, `exists_far_frozen_bounds`), their
  docstrings and the two file headers are word for word the same (compared by a script, old file
  against new).
- `Symmetry/OnlyOrthogonal.lean`: a new file (statements of the skips paper, 13 `sorry`). It is
  not in the brief and I did not compare it with the paper.
- `STATEMENTS.md` (rows of these files), `SkipsLean.lean`, `checks/Axioms.lean`.

No statement and no definition that I judged changed. Line numbers of `STATEMENTS.md` below are
those of the file at `0d967ff`.

Paper: the dimension paper as text (`dim.txt`; "D"). Equation numbers are those of that text.

How I checked. "By reading": I read the Lean source and the paper. "By compiling": I compiled a
scratch file of my own in `/home/claude/audit6/` with `lean` (4.36.0). The compiled library of
`/home/claude/lw` lacks 35 of the 87 files, so I read the compiled library of `/home/claude/lp/lean`
(branch `lean-plus`, the same commit `0d967ff`; its tracked sources under `SkipsLean/` are the same, by `diff -rq`; its
owner built it at that commit), through
`LEAN_PATH`, without `lake`. I wrote nothing under `lw`, `lp` or the repository. "By a
computation": a Python script in `/home/claude/audit6/`.

Short answer. **Nothing false, vacuous or drifted was found.** "Generic" is `∀ᵐ θ ∂μ` for a
Lebesgue measure in every one of the 110 public statements that state a generic claim. `funDim` is
the maximum of Definition 4.1. The five statements of Theorem 5.2 (ii) for `ε > 0` and (iii) carry
the paper's hypotheses and one more, at least one token; the change to a real variable did not
touch them. At `0d967ff`, two of the five are proved with the three standard axioms (SwiGLU and
GeGLU without normalization); the three under pre-RMSNorm rest on seven statements that are still
`sorry` (`Depth/RayGatedPlus.lean`, `Depth/RayMlpPlus.lean`), which I judged true by hand and whose
forms I checked by compiling.

---------------------------------------------------------------------------------------------------

## Part 1: three checks that the statements have not drifted

### Check 1. "Generic parameters" is "for almost every parameter"

**Verdict: yes, everywhere.** No generic claim of a paper is formalized as "there is a parameter" or
"on a nonempty open set".

What I did (by compiling, `Sig3.lean`): a program went through every theorem of the library whose
name begins with `ae_` or whose statement contains `∀ᵐ`. There are 121: 110 public and 11 private.
For each one it took the statement apart and tested four things.

| Result | Count |
|---|---|
| The conclusion is `∀ᵐ θ ∂μ, …`, `μ` is a variable of the statement (`∀ μ`), and the statement has `[μ.IsAddHaarMeasure]` for this `μ`; no hypothesis is an a.e. statement | 117 |
| The same, with one hypothesis `∀ᵐ θ ∂μ, SomeBlockNonzero A θ` (for the same `μ`) | 3: `ae_turnGeneric`, `ae_ne_skipless_rmsNorm`, `ae_not_dense_eq_skipless_rmsNorm_zero` |
| Not an a.e. conclusion | 1: the private helper `measure_null_of_slices` (a Fubini step; its hypothesis is a.e., its conclusion is "measure zero") |

One of them in full (elaborated, `Chk.lean`):

```
ae_funDim_swiglu_skipless : ∀ {T d dIn dOut} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut] {hid : Fin L → Type} [(ℓ : Fin L) → Fintype (hid ℓ)] [Nonempty T]
  (μ : MeasureTheory.Measure (Params (Arch.gated silu id hid) dIn dOut)) [μ.IsAddHaarMeasure],
  2 ≤ Fintype.card d → Fintype.card d ≤ Fintype.card dIn → Fintype.card d ≤ Fintype.card dOut →
  (∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) →
  ∀ᵐ (θ : Params (Arch.gated silu id hid) dIn dOut) ∂μ,
    funDim (Arch.gated silu id hid) 0 θ + ((L + 1) * Fintype.card d ^ 2 + ∑ ℓ, Fintype.card (hid ℓ)) =
      Module.finrank ℝ (Params (Arch.gated silu id hid) dIn dOut)
```

The quantifier over parameters is `∀ᵐ θ ∂μ`: the set of the `θ` at which the statement fails has
`μ`-measure zero. The measure `μ` is any additive Haar measure:

- in 104 statements, on the parameters `Params A dIn dOut` of the network. This space carries the
  Borel σ-algebra of its norm (`Generic/Params.lean:32-34`: `MeasurableSpace := borel _`,
  `BorelSpace := ⟨rfl⟩`);
- in 13 statements of the absorb paper for one block, on the pairs `(W_read, W_write)`
  (`Matrix d m ℝ × Matrix m d ℝ`);
- in 3 helpers, on an abstract finite-dimensional real normed space with its Borel σ-algebra.

That such a `μ` is a Lebesgue measure I checked by compiling (`Haar.lean`, two statements, no
`sorry`): any two additive Haar measures on `Params A dIn dOut` have the same sets of measure zero;
and a linear change of coordinates `Params A dIn dOut ≃L[ℝ] (Fin P → ℝ)` carries `μ` to a positive
multiple of the Lebesgue measure `volume` of `ℝ^P`. So `∀ᵐ θ ∂μ` is the paper's "outside a set of
Lebesgue measure zero" (D Section 2).

The 121 statements by file (`†`: has the a.e. hypothesis named above):

| File | Count | Names | `μ` is an additive Haar measure on |
|---|---|---|---|
| `Absorb/FewerUnits.lean` | 4 | `ae_forall_isUnit_det_add_subProd`, `ae_ne_zero_of_analytic_pair` (private), `ae_not_gelu_absorb_of_card_lt`, `ae_not_relu_absorb_of_card_lt` | the pairs `(W_read, W_write)` |
| `Absorb/FirstBlock.lean` | 4 | `ae_firstBlockGeneric`, `ae_isUnit_det_one_add_subProd` (private), `ae_ne_skipless_of_first_card_lt_gelu`, `ae_ne_skipless_of_first_card_lt_relu` | the parameters |
| `Absorb/Networks.lean` | 2 | `ae_exists_learned_skips_eq_skipless`, `ae_exists_residual_eq_skipless` | the parameters |
| `Absorb/PaperForms.lean` | 4 | `ae_not_gelu_absorb_identity`, `ae_not_gelu_skipless_eq_residual`, `ae_not_relu_absorb_identity`, `ae_not_relu_skipless_eq_residual` | the pairs |
| `Absorb/RMSNormGeneric.lean` | 10 | `ae_ne_skipless_rmsNorm` †, `ae_ne_skipless_rmsNorm_gated`, `ae_ne_skipless_rmsNorm_mlp`, `ae_not_dense_eq_skipless_rmsNorm_zero` †, `ae_not_dense_eq_skipless_rmsNorm_zero_gated`, `ae_not_dense_eq_skipless_rmsNorm_zero_mlp`, `ae_someBlockNonzero_gated`, `ae_someBlockNonzero_mlp`, `ae_turnGeneric` †, `measure_null_of_slices` (private, no a.e. conclusion) | the parameters |
| `Absorb/RMSNormKinds.lean` | 14 | `ae_ne_skipless_rmsNorm_K` and `ae_not_dense_eq_skipless_rmsNorm_zero_K` for `K` = `tanh`, `gelu`, `relu`, `reluSq`, `swiglu`, `geglu`, `reglu` | the parameters |
| `Absorb/SameWidth.lean` | 9 | `ae_forall_subProd_ne_neg`, `ae_ne_skipless_oneBlock_gelu`, `ae_ne_skipless_oneBlock_of` (private), `ae_ne_skipless_oneBlock_relu`, `ae_ne_zero_of_analytic_prod` (private), `ae_nondegenerate`, `ae_not_gelu_absorb_same_width`, `ae_not_relu_absorb_same_width`, `ae_subProd_ne_neg_oneBlock` (private) | the pairs; the parameters (the four `…_oneBlock…`) |
| `Depth/GeluGatedTheorem.lean` | 5 | `ae_funDim_geglu_skipless`, `ae_funDim_geglu_skipless_rmsNorm`, `ae_funDim_gelu_skipless_rmsNorm`, `ae_funDim_swiglu_skipless`, `ae_funDim_swiglu_skipless_rmsNorm` | the parameters |
| `Depth/Tanh.lean`, `Depth/TanhRMS.lean` | 3 | `ae_funDim_tanh_skipless`, `ae_tanhDepthGeneric`, `ae_funDim_tanh_skipless_rmsNorm` | the parameters |
| `Dimension/GenericRank.lean` | 5 | `ae_finrank_range_ge` (private), `ae_funDim_ge`, `ae_injective_comp_of_analytic` (private), `ae_jacobianRank_ge`, `ae_jacobianRank_le_funDim` | the parameters; an abstract space (the two private ones) |
| `Dimension/RescalingGate.lean` | 3 | `ae_funDim_add_le_skipless_reglu`, `ae_funDim_add_le_skipless_reglu_rmsNorm`, `ae_gate_ne_zero` | the parameters |
| `Dimension/RescalingMlp.lean` | 5 | `ae_funDim_add_le_skipless_relu`, `ae_funDim_add_le_skipless_reluSq`, `ae_funDim_add_le_skipless_reluSq_rmsNorm`, `ae_funDim_add_le_skipless_relu_rmsNorm`, `ae_read_col_ne_zero` | the parameters |
| `Generic/Gated.lean` | 3 | `ae_funDim_add_le_skipless_gated`, `ae_funDim_add_le_skipless_gated_rmsNorm`, `ae_value_ne_zero` | the parameters |
| `Generic/Params.lean` | 8 | `ae_funDim_add_le_residual`, `ae_funDim_add_le_residual_rmsNorm`, `ae_funDim_add_le_skipless`, `ae_funDim_add_le_skipless_rmsNorm`, `ae_isUnit_det_of_linear` (private), `ae_isUnit_det_submatrix`, `ae_rank_E` (private), `ae_rank_E_write` | the parameters |
| `OneBlock/Common.lean` | 1 | `ae_ne_zero_of_analytic` | an abstract space |
| `OneBlock/GELU.lean`, `GeGLU.lean`, `SwiGLU.lean`, `Tanh.lean` | 4 | `ae_funDim_gelu_oneBlock`, `ae_funDim_geglu_oneBlock`, `ae_funDim_swiglu_oneBlock`, `ae_funDim_tanh_oneBlock` | the parameters |
| `OneBlock/Gated.lean`, `OneBlock/Mlp.lean` | 4 | `ae_funDim_gated_oneBlock`, `ae_oneBlockGenericGated`, `ae_funDim_mlp_oneBlock`, `ae_oneBlockGeneric` | the parameters |
| `OneBlock/ReGLU.lean` | 6 | `ae_exists_jacobianRank_reglu_oneBlock`, `ae_exists_jacobianRank_reglu_oneBlock_residual`, `ae_funDim_reglu_oneBlock`, `ae_funDim_reglu_oneBlock_residual`, `ae_funDim_reglu_oneBlock_residual_eq_add`, `ae_oneBlockGenericReGLU` | the parameters |
| `OneBlock/Rescale.lean` | 4 | `ae_exists_jacobianRank_reluSq_oneBlock`, `ae_exists_jacobianRank_relu_oneBlock`, `ae_funDim_reluSq_oneBlock`, `ae_funDim_relu_oneBlock` | the parameters |
| `OneBlock/Residual.lean` | 8 | `ae_funDim_gated_oneBlock_residual`, `ae_funDim_gated_oneBlock_residual_eq_add`, `ae_funDim_geglu_oneBlock_residual_eq_add`, `ae_funDim_gelu_oneBlock_residual_eq_add`, `ae_funDim_mlp_oneBlock_residual`, `ae_funDim_mlp_oneBlock_residual_eq_add`, `ae_funDim_swiglu_oneBlock_residual_eq_add`, `ae_funDim_tanh_oneBlock_residual_eq_add` | the parameters |
| `OneBlock/ResidualRescale.lean` | 6 | `ae_exists_jacobianRank_reluSq_oneBlock_residual`, `ae_exists_jacobianRank_relu_oneBlock_residual`, `ae_funDim_reluSq_oneBlock_residual`, `ae_funDim_reluSq_oneBlock_residual_eq_add`, `ae_funDim_relu_oneBlock_residual`, `ae_funDim_relu_oneBlock_residual_eq_add` | the parameters |
| `Residual/UpperBoundSymmetries.lean` | 7 | `ae_funDim_add_le_residual_gated`, `ae_funDim_add_le_residual_gated_gate`, `ae_funDim_add_le_residual_gated_gate_rmsNorm`, `ae_funDim_add_le_residual_gated_rmsNorm`, `ae_funDim_add_le_residual_mlp_rescale`, `ae_funDim_add_le_residual_mlp_rescale_rmsNorm`, `ae_rank_E_ubs` (private) | the parameters |
| `Symmetry/AtOneState.lean` | 2 | `ae_exists_isUnit_det_submatrix_cols`, `ae_exists_isUnit_det_submatrix_rows` | the parameters |

Statements with `∀ᵐ θ, ∃ …` inside (`ae_exists_…`) say "for almost every `θ` there is a batch, or a
choice of columns": the paper's meaning.

**Other statements that the index maps to a generic clause** (by reading the index, every row with
"generic", "almost every", Theorem 4.3 of D or Theorem 4.2 of S):

1. *Statements under explicit conditions on `θ`.* The paper's upper bounds are "at generic
   parameters". Lean states each first for every `θ` that satisfies named conditions (`E` and the
   writes of rank `d`, no vanishing value column, the structures `OneBlockGeneric`,
   `OneBlockGenericGated`, `OneBlockGenericReGLU`, `TanhDepthGeneric`, `FirstBlockGeneric`,
   `TurnGeneric`, `Nondegenerate`), and then has an `ae_` statement that the conditions hold almost
   everywhere. For example (`Chk3.lean`): `funDim_add_le_skipless (θ) : A.χ = id → (∀ ℓ,
   Differentiable ℝ (A.f ℓ)) → θ.E.rank = card d → (∀ ℓ, (θ.write ℓ).rank = card d) → funDim A 0 θ +
   (L + 1) * card d ^ 2 ≤ finrank …`. These are neither existence statements nor statements on an
   open set; with their `ae_` companion they are the generic claim. The index says "under the
   conditions of the proof" in most of these rows, and in the note on Theorem 4.3. Six rows do not
   say it in the row itself: lines 99, 100, 114, 162 (D Theorem 4.3) and 306, 307 (S Theorem 4.2).
   See the corrections.
2. *Measure zero.* `volume_zeroSet_of_analytic_pi` (`volume {x | f x = 0} = 0` on `ι → ℝ`) and
   `measure_zeroSet_of_analytic` (`μ {x | f x = 0} = 0` for an additive Haar `μ`).
3. *"Dense" and "open and dense".* `exists_open_dense_injective_fderiv_suffix` (and `_rmsNorm`),
   `dense_setOf_linearIndependent_mul`, the two statements of `Depth/RayDense.lean`, and the
   hypotheses `hdense`. They are about hidden states and rays, not about parameters, and the paper
   says "open dense set" (Lemma D.2) and "these `ξ` are dense in `C_k`" (proof of Lemma D.12) in
   the same places. "A generic ray" of the paper is one `ξ` with (i), (ii), (iii); Lean writes the
   three conditions out.

**Existence statements beside a generic claim.** I found no statement that the index maps to a
paper statement *about generic parameters* and that is only an existence statement. The existence
statements of Appendix D stand for the paper's statements about the explicit `θ†`, which are not
generic claims:

| Paper | Lean | Form | Does the index say so? |
|---|---|---|---|
| D Lemma D.13 (`θ†` is good) | `exists_goodForConesGated_cols`, `exists_goodForConesGated_outer`, `exists_goodForConesMlp_outer` | `∃ C A θ, GoodForCones… C A θ ∧ (independence over ℚ)` | yes (line 181: "as existence … The explicit `θ†` … are not stated") |
| D Appendix D.7, "`(D_0)` holds at `θ†`" | `exists_regular_claimRMS_gelu`, `exists_regular_claimGated_swiglu`, `…_swiglu_rmsNorm`, `…_geglu`, `…_geglu_rmsNorm` | `∃ θ, Regular … θ ∧ (no value column vanishes) ∧ Claim… θ 0` | yes (line 201: "there is a regular parameter … at which Claim `(D_0)` holds") |

The generic claim that rests on them, Theorem 5.2, is the five `ae_funDim_…` statements; the
passage from one parameter to almost every parameter is `ae_funDim_ge`
(`∀ᵐ θ ∂μ, funDim A S θ₀ ≤ funDim A S θ`).

### Check 2. The functional dimension is `max_X rank DF_X(θ)` over all finite batches

**Verdict: yes.** For the blocks of Theorem 5.2 it is the paper's Definition 4.1 with no
difference. For blocks that are not differentiable everywhere it is the maximum over the batches
of inputs at which the network is differentiable in `θ`; the index says this (note "ReLU blocks and
the functional dimension").

`Dimension/Functional.lean:29-49` (by reading):

```
def evalBatch {n : ℕ} (X : Fin n → Matrix T dIn ℝ) (θ : Params A dIn dOut) :
    Fin n → Matrix T dOut ℝ := fun i => eval A S θ (X i)

noncomputable def jacobianRank {n : ℕ} (X : Fin n → Matrix T dIn ℝ) (θ : Params A dIn dOut) : ℕ :=
  Module.finrank ℝ (LinearMap.range (fderiv ℝ (evalBatch A S X) θ).toLinearMap)

noncomputable def funDim (θ : Params A dIn dOut) : ℕ :=
  sSup {r : ℕ | ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), r = jacobianRank A S X θ}

noncomputable def redundancy (θ : Params A dIn dOut) : ℕ :=
  Module.finrank ℝ (Params A dIn dOut) - funDim A S θ

noncomputable def flat (θ : Params A dIn dOut) : Submodule ℝ (Params A dIn dOut) :=
  ⨅ x : Matrix T dIn ℝ, LinearMap.ker (fderiv ℝ (fun θ' => eval A S θ' x) θ).toLinearMap
```

What `funDim` is, exactly.

- `evalBatch A S X θ` is `F_X(θ) = (F_θ(x_1), …, F_θ(x_n))`. `jacobianRank` is the rank of its
  Fréchet derivative in `θ` at `θ` (the dimension of the range), the paper's `rank DF_X(θ)`. The
  derivative does not depend on the norms (finite dimension).
- `funDim A S θ` is the supremum in `ℕ` of these ranks over all `n : ℕ` and all batches
  `X : Fin n → Matrix T dIn ℝ` (every finite batch, the empty one included, with the token set `T`
  fixed, as in the paper). The set is not empty and is bounded by `P`, so the supremum is a
  maximum: `exists_jacobianRank_eq_funDim` and `jacobianRank_le_funDim` (proved; the two together
  compile as one statement in my `FD.lean`). It is `max_X rank DF_X(θ)`.
- `redundancy` is `P − funDim` (subtraction of natural numbers; `funDim ≤ P` always). `flat` is
  `K(θ)`.
- Where the network is not differentiable in the parameters: Mathlib's `fderiv` of a map at a point
  where it is not differentiable is `0`. So a batch that contains one input `x` at which
  `θ' ↦ F_θ'(x)` is not differentiable at `θ` has `jacobianRank = 0`, the whole batch, not only the
  one input (by compiling, `FD.lean`, examples (2) and (3)). The batches all of whose inputs are
  points of differentiability keep their true rank. So `funDim` is the largest rank over the
  batches of inputs at which the network is differentiable in `θ` at `θ`, and
  `funDim + dim K(θ) = P` holds with no hypothesis (`funDim_add_finrank_flat'`), where `K(θ)` asks
  nothing at the other inputs.
- For which kinds of block this matters.
  - **It does not matter** for tanh, GELU, SwiGLU and GeGLU blocks without normalization or under
    pre-RMSNorm with `ε > 0`, that is, for every network of Theorem 5.2 that Lean states. There
    `f_ℓ` and `χ` are differentiable, so every batch is differentiable in `θ` (`differentiable_eval`;
    `FD.lean`, example (4)), and `funDim` is the paper's `fd(θ)` word for word.
  - **It matters** for ReLU and ReGLU blocks (the activation or gate has a kink): the inputs at
    which the network is not differentiable in `θ` drop out. The paper drops the inputs at which a
    hidden unit sits at its kink; Lean's set of kept inputs is larger (it contains, for example, the
    input `0`). For ReLU² the network is differentiable everywhere, so Lean keeps every input while
    the paper drops the kink inputs. Hence Lean's `funDim` is at least the paper's value, and the
    one-block theorems for these kinds give two statements each (the value, and a batch of the
    paper's inputs with that rank). The index says all of this (lines 255-270).
  - **Pre-RMSNorm with `ε = 0`**: `rmsRow 0` is total in Lean (`rmsRow 0 0 = 0`) and is not
    differentiable at a zero row. No equality for `ε = 0` is stated in Lean; the upper bounds "for
    every real `ε`" are the statements marked with a prime, which need no differentiability. The
    index says so (lines 271-275).

### Check 3. Theorem 5.2 (ii) for `ε > 0` and (iii) carry no hypothesis that the paper does not have

**Verdict: none, except "at least one token" (`[Nonempty T]`), which the paper has implicitly.** The
change from complex to real variables in the proofs changed nothing in the five final statements
and in the five statements of Lemma D.12.

How I know that nothing changed. `git diff 19f888c HEAD` (`19f888c` is the commit at which the fifth
audit ended): `Depth/GeluGatedTheorem.lean` is unchanged; in `Depth/StepGated.lean` the five
statements are unchanged and only `sorry` was replaced by proofs, with new imports and a new
header; in `Depth/GeluGatedExplicit.lean` three lines of the header changed; `Depth/Cones.lean`,
`Depth/SuffixGated.lean`, `Depth/Suffix.lean`, `Depth/SuffixRMS.lean`, `Dimension/*`, `Network/*`,
`Basic/*`, `Generic/*` are unchanged. I also read the ten statements again in elaborated form
(`Chk.lean`).

**The five final statements** (`Depth/GeluGatedTheorem.lean`). Paper (D Theorem 5.2 and Scope):
"Let `d_in, d_out ≥ d_model ≥ 2`, and consider networks without biases whose blocks are all of one
kind, tanh, GELU, SwiGLU or GeGLU, each with at least `d_model` hidden units. In the following cases
the functional dimension at generic parameters is `P − (L + 1) dim G − s` … (ii) GELU blocks: under
pre-RMSNorm with `ε > 0` and with `ε = 0`. (iii) SwiGLU blocks, and GeGLU blocks: without
normalization, and under pre-RMSNorm with `ε > 0`."

| Hypothesis in Lean (all five) | In the paper |
|---|---|
| `[Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut]`, `hid : Fin L → Type` with `[∀ ℓ, Fintype (hid ℓ)]` | finite sets of tokens, coordinates and hidden units; any `L` (also `L = 0`) |
| `[Nonempty T]` | not said; an input has at least one token |
| `(μ) [μ.IsAddHaarMeasure]`, conclusion `∀ᵐ θ ∂μ` | "at generic parameters" |
| `hd : 2 ≤ Fintype.card d` | `d_model ≥ 2` |
| `hdIn : card d ≤ card dIn`, `hdOut : card d ≤ card dOut` | `d_in, d_out ≥ d_model` |
| `hhid : ∀ ℓ, card d ≤ card (hid ℓ)` | "each with at least `d_model` hidden units" |
| `hε : 0 < ε` (the three with `rmsNorm ε`) | "pre-RMSNorm with `ε > 0`" |

| Lean name | Network | Conclusion `∀ᵐ θ ∂μ, funDim … 0 θ + … = finrank ℝ (Params …)` with | Paper |
|---|---|---|---|
| `ae_funDim_gelu_skipless_rmsNorm` | `Arch.mlp gelu (rmsNorm ε) hid`, no skips (`0`) | `(L + 1) * (card d * (card d - 1) / 2)` | (ii), `ε > 0`: `P − (L+1) d(d−1)/2` |
| `ae_funDim_swiglu_skipless` | `Arch.gated silu id hid` | `(L + 1) * card d ^ 2 + ∑ ℓ, card (hid ℓ)` | (iii), no normalization |
| `ae_funDim_swiglu_skipless_rmsNorm` | `Arch.gated silu (rmsNorm ε) hid` | `(L + 1) * (card d * (card d - 1) / 2) + ∑ ℓ, card (hid ℓ)` | (iii), `ε > 0` |
| `ae_funDim_geglu_skipless` | `Arch.gated gelu id hid` | as SwiGLU | (iii), no normalization |
| `ae_funDim_geglu_skipless_rmsNorm` | `Arch.gated gelu (rmsNorm ε) hid` | as SwiGLU | (iii), `ε > 0` |

`d (d − 1)` is even, so the division of natural numbers is exact. No hypothesis mentions cones,
rays, a gate "far from zero", analyticity or a real variable. Not stated, as before: (ii) for
`ε = 0`, and "so the network satisfies the equality condition".

One hypothesis is not used by a proof: for SwiGLU blocks without normalization the proofs use
`d ≥ 1` only. By compiling (`D1.lean`): a copy of `ae_funDim_swiglu_skipless` with `[Nonempty d]` in
the place of `2 ≤ card d` compiles from the library's statements with the three standard axioms.
The paper's `d ≥ 2` is kept in the statement, as for tanh blocks.

**The five statements of Lemma D.12** (`Depth/StepGated.lean`). Paper: "Let the blocks be GELU
blocks in the case (+), or gated blocks in the case (n) or (+). Let `θ` be good for the cones
`C_0, …, C_L`, and let `k < L`. Then `(D_{k+1})` implies `(D_k)`."

| Hypothesis in Lean | In the paper |
|---|---|
| `[Nonempty T]` | one token |
| `hε : 0 < ε` (the three with `rmsNorm ε`) | the case (+) |
| `hθ : GoodForConesGated C A θ` (SwiGLU, GeGLU) or `GoodForConesMlp C A θ` (GELU) | "good": (R1), (K1), (K2), and of (K3) "no `a_j` vanishes, and in a gated block no value column `e_j` vanishes"; Lean adds that the cones are not empty (fifth audit) |
| `hQ : ∀ ℓ, LinearIndependent ℚ (fun j => (θ.read ℓ)ᵀ (Sum.inl j))` (SwiGLU); `∀ ℓ, LinearIndependent ℚ (fun j => Matrix.vecMulVec c_j c_j)` with `c_j` the gate column (GeGLU) or the read column (GELU) | the rest of (K3) |
| `k : Fin L`, `hk : ClaimGated ⊤ θ k.succ` / `ClaimGated (antisymmetric d) θ k.succ` / `ClaimRMS … θ k.succ` | `k < L`, `(D_{k+1})` |
| Conclusion: the same claim at `k.castSucc` | `(D_k)` |

Names: `claimGated_castSucc_swiglu`, `claimGated_castSucc_swiglu_rmsNorm`,
`claimGated_castSucc_geglu`, `claimGated_castSucc_geglu_rmsNorm`, `claimRMS_castSucc_gelu`. Nothing
of the real-variable proofs appears in them: no `GateFar`, no "one small factor", no density.

**The chain, and what each link assumes** (by reading the statements; by compiling for the forms).

| Link | Assumes beyond the scope | Is an assumption the conclusion in other words? |
|---|---|---|
| `GeluGatedTheorem.lean`: the five `ae_funDim_…` | nothing; uses `exists_regular_claim…`, `funDim_of_claim…` (Proposition D.4), `ae_funDim_ge`, `ae_funDim_add_le_skipless_…` (Theorem 4.3) | no |
| `GeluGatedExplicit.lean`: the five `exists_regular_claim…` | nothing; uses Lemma D.13 (`exists_goodForCones…`), "good is regular", Lemma D.5, Lemma D.12 | no |
| `StepGated.lean`: Lemma D.12 | good `θ`, (K3), `(D_{k+1})` | no |
| `RayGatedN.lean` (case (n), to (38)) | `GateFar σ σ' p`; on one ray (i), (ii), (iii); then `hdense`; then (K3) for block `k` | no: (i) to (iii) are the paper's "generic ray"; `hdense` is proved in `RayDense.lean` |
| `StepsGatedN.lean`, `StepsPlus.lean` (steps 1 to 3) | (38) as hypotheses (`hgate`, `hfro`; `h38`; `hz`, `hw`), `(D_{k+1})`, good and regular `θ` | no: (38) is the output of the ray files, and the steps are a real argument (Lemmas D.2, D.3, the converse of the claim) |
| `RayGatedPlus.lean`, `RayMlpPlus.lean` (case (+), to (38)) | `GateFar`, `hone` ("one small factor"), `hreg`, `hdense` | no: `hone` is proved for GELU and for SiLU in `OneSmallFactor.lean`, `hreg` in `Cones.lean`, `hdense` in `RayDense.lean` (the forms fit: `Fit.lean` compiles) |
| `RayInduction.lean` | `hid` (fact (b)) and `hstep`: "if `∂G₀/∂y_j(1/t, 0) + ν_j(t) G_j(1/t, 0)` tends to `0` faster than every power, then `G_j` vanishes near `(0,0)`" | `hstep` has a part of the conclusion as its conclusion, but under a premise that the theorem must establish, hidden unit by hidden unit in the order of the exponents. In the case (n) it is discharged by a proved argument (`RayGatedN.lean`). The index calls it "a hypothesis". Not a restatement |
| `FrozenFar.lean` (Lemma D.11) | good `θ`, `GateFar` | no |

**Axioms and `sorry`** (by compiling, `Ax2.lean`: `Lean.collectAxioms` on every theorem and
definition constant of the library, public, private and generated; 2524 constants).

- `grep -rn "^axiom" SkipsLean`: no line. No constant of the library is an axiom or an opaque
  constant.
- 2492 constants depend on `propext`, `Classical.choice`, `Quot.sound` only. 32 depend on
  `sorryAx`, and on no other axiom.
- With `sorry` in their own proof (7, all in the chain): `flat_at_generic_ray_gated_rmsNorm`,
  `flat_of_suffixFlat_gated_rmsNorm`, `flat_of_suffixFlat_swiglu_rmsNorm`,
  `flat_of_suffixFlat_geglu_rmsNorm` (`Depth/RayGatedPlus.lean`);
  `flat_at_generic_ray_mlp_rmsNorm`, `flat_of_suffixFlat_mlp_rmsNorm`,
  `flat_of_suffixFlat_gelu_rmsNorm` (`Depth/RayMlpPlus.lean`).
- Resting on them (12): `claimGated_castSucc_swiglu_rmsNorm`, `claimGated_castSucc_geglu_rmsNorm`,
  `claimRMS_castSucc_gelu`; `exists_regular_claimRMS_gelu`,
  `exists_regular_claimGated_swiglu_rmsNorm`, `exists_regular_claimGated_geglu_rmsNorm` and three
  private helpers of that file; `ae_funDim_gelu_skipless_rmsNorm`,
  `ae_funDim_swiglu_skipless_rmsNorm`, `ae_funDim_geglu_skipless_rmsNorm`.
- Outside the chain: the 13 of `Symmetry/OnlyOrthogonal.lean`.
- Proved with the three standard axioms at `0d967ff`: `ae_funDim_swiglu_skipless`,
  `ae_funDim_geglu_skipless` (Theorem 5.2 (iii) without normalization),
  `claimGated_castSucc_swiglu`, `claimGated_castSucc_geglu`, `exists_regular_claimGated_swiglu`,
  `exists_regular_claimGated_geglu`, `exists_far_frozen_bounds`, `ray_induction`,
  `ray_induction_matrix`, and every statement of the other files of Part 2. At the start commit
  `6480ce9` the last three were `sorry` and the whole case (n) rested on them.

---------------------------------------------------------------------------------------------------

## Part 2: the statements written after the fifth audit began

Seventeen files, 79 public names. Every public name is in `STATEMENTS.md`, and every name that the
rows of these files give exists (by a script).

### Verdict table

"Proved" means: no `sorry`, and the three standard axioms only (`Ax2.lean`).

| Paper statement or proof piece | Lean names (file) | Verdict | The difference |
|---|---|---|---|
| D "GELU and the Mills ratio", Lemma D.8 | `millsRatio`, `gelu_eq_sub_millsRatio`, `geluDeriv_eq_sub_millsRatio`, `abs_millsRatio_sub_sum_le` (`Activations/FarFromZero.lean`) | **LEAN WEAKER** (proved) | Real `z` only: (i) for all real `z`, (ii) for real `z > 0`. `millsRatio z = (1 − Φ(z))/φ(z)`, which is the paper's `√(π/2) e^{z²/2}(1 − erf(z/√2))` for real `z`. The header says so. |
| D "A gate on a ray": (24), `δ`, `δ'`, (25), the bounds after (25) | `gelu_neg_eq`, `silu_neg_eq`, `gelu_gap_eq`, `silu_gap_eq`, `gelu_gap_bounds`, `silu_gap_bounds`, `silu_gap_bounds'`, `millsRatio_pos_le`, `abs_millsRatio_sub_inv_le`, `mul_millsRatio_bounds` (same file) | **SAME** (proved) | (24) is stated for every real `y` (the paper: `y > 0`; the same identities). `mr(y) ≤ 1/y` and `|mr(y) − 1/y| ≤ 1/y³` for `y > 0`. |
| D "meromorphic at infinity", "faster than every power of `1/t`", "such a map vanishes identically" | `MeromorphicAtInfinity`, `FasterThanPowers`, `fasterThanPowers_iff`, `FasterThanPowers.congr`, `.mono`, `.add`, `.smul_of_le_pow`, `fasterThanPowers_of_le_pow_mul_exp`, `eventually_nhds_eq_zero_of_fasterThanPowers`, `MeromorphicAtInfinity.eventually_eq_zero` (`Activations/MillsAtInfinity.lean`) | **SAME in content, DIFFERENT in form** (proved) | `Θ₀` real-analytic at `0` (paper: holomorphic near `0`); the exponent `l` is a natural number (paper: an integer; a negative one goes into `Θ₀`); "vanishes identically" is "vanishes for all large `t`". Values in any real normed space. |
| D Lemma D.9 | `eventually_eq_zero_of_millsRatio_smul_add` (same file) | **LEAN WEAKER** (proved) | Real `ω > 0` and `ω' = 0` only. This is the case that the proof of Lemma D.12 uses ("with `z(t) = |ξ c_j| t`"). The case (0) of the paper needs complex `ω`, `ω'`. |
| What the proofs on rays use of a gate (not a paper statement) | `GateFar`, `gateFar_silu`, `gateFar_gelu` (`Activations/GateFar.lean`) | piece; true (proved for both gates) | A structure: real-analytic, derivative `σ'`, (24), (25) with the exponent `p`, and `y|δ'(y)|/δ(y) → ∞`. The header says "It is not a notion of the paper". The last clause is used only in the case (n) (see note 1). |
| D proof of Lemma D.12, "One small factor, `α = 1_j`" | `one_small_factor_gelu`, `one_small_factor_silu` (`Activations/OneSmallFactor.lean`) | **PART** of the proof; true (proved) | Without the network, in the variable `s = 1/t`: `a`, `b` real-analytic at `0`, `ν(t) = t δ'(tu)/δ(tu)`; if `a(1/t) + ν(t) b(1/t)` tends to `0` faster than every power, `b = 0` near `0`. GELU by Lemma D.9; SiLU if `a`, `b` are even near `0`. |
| D "The identity for one GELU or gated block", (26) to (30), gated block | `blockLHSGated`, `blockLHSGated_add_right`, `blockLHSGated_neg`, `suffixFlat_castSucc_iff_gated`, `suffixFlat_castSucc_iff_gated_rmsNorm` (`Depth/BlockIdentityGated.lean`) | **SAME** (proved) | Rows `T`; `𝓛` takes `n W_read` and `ż` as arguments in the place of `n`; (29) in additive form. (28) in the case (n) for any differentiable gate, in the case (+) for a real-analytic gate. |
| D proof of Lemma D.12, "A generic ray", (i): "These `ξ` are dense" | `dense_setOf_linearIndependent_abs_dotProduct`, `dense_setOf_linearIndependent_sq_dotProduct` (`Depth/RayDense.lean`) | **LEAN STRONGER** than this part (proved) | For the hidden units of all tokens at once, and dense among all matrices `Ξ`. Only (i); the density of (ii) and (iii) is inside the proofs of `RayGatedN.lean`. |
| D "The frozen network" | `Arch.frozen`, `Params.toFrozen`, `writeLHS`, `blockLHSGated_eq_writeLHS`, `frozen_block_apply`, `analyticOnNhd_f_frozen`, `regular_frozen_of_goodForConesGated`, `suffix_frozen_smul`, `fderiv_suffix_frozen_smul`, `fderiv_params_suffix_frozen_smul`, `writeLHS_frozen_smul` (`Depth/Frozen.lean`) | **SAME**, with additions (proved) | `𝓑°_{>k}` is the `suffix` of an architecture of its own (`χ = id`, block `ℓ`: `z_i w_i` on `A ℓ`, `0` elsewhere). "Lemmas D.2 and D.3 hold for it" is "a good `θ` is regular for it". Added: the frozen network is homogeneous of the degree `2^{L−k}`. "Polynomial" is stated as "real-analytic". |
| D Lemma D.11 | `exists_far_frozen_bounds` (`Depth/FrozenFar.lean`) | **DIFFERENT** (proved at `0d967ff`) | Real `U` with `‖U‖ ≤ ϱ` (all entries); no holomorphic extension. One clause more, the bound for the derivative in the hidden state, which the paper gets later by Cauchy's estimate. Rows `T`; any gate with `GateFar`; `t₀` any real number. |
| D Appendix D.3, "Conversely, every `Z = Z_k ∈ 𝔤` and `η` of the form (17), or (19) …, satisfy (16)" | `suffixFlat_cobDir_add_rescaleDir` (`Depth/SuffixFlatConverse.lean`) | **PART** (proved) | Gated blocks, case (n) only, any differentiable gate. The case (+) and the form (17) are not stated; the proof of Lemma D.12 uses the converse in the case (n) only. |
| D Lemma D.10 | `suffixPost`, `suffix_eq_suffixPost`, `scaledSuffix`, `suffix_pow_smul_eq_scaledSuffix`, `scaledSuffix_neg`, `analyticAt_scaledSuffix`, `fderiv_suffix_pow_smul`, `fderiv_params_suffix_pow_smul` (`Depth/ScaledSuffix.lean`) | **DIFFERENT**: the core of the proof, not the lemma's statement (proved) | `(θ, s, h) ↦ 𝓑^♯(N_{ε s^{2m}}(h))` is real-analytic at every `(θ, s, H)` with no zero row of `H`, also at `s = 0`; it is `𝓑_{>k}(t^m h)` at `s = 1/t`, `t > 0`; it is even in `s`. Not stated: derivatives of all orders, "meromorphic at infinity", the holomorphic extension with bounds uniform in `t`. The header says so. |
| D proof of Lemma D.12, "The expansion" and "The induction", (34) to (36), facts (a) to (c) | `ray_induction`, `ray_induction_matrix` (`Depth/RayInduction.lean`) | **PART** of the proof; true (proved at `0d967ff`) | Without the network. Fact (a) is "`G₀`, `G_j` real-analytic at `(0,0)`", fact (b) the hypothesis `hid`, fact (c) inside the proof; "one small factor" is the hypothesis `hstep`. Values in a complete space. |
| D proof of Lemma D.12 from (28) to (38), case (n) | `frozen_flat_at_generic_ray`, `frozen_flat_of_suffixFlat`, `frozen_flat_of_suffixFlat_swiglu`, `frozen_flat_of_suffixFlat_geglu` (`Depth/RayGatedN.lean`) | **PART** of the proof; true (proved at `0d967ff`) | Rows `T`; any gate with `GateFar` in the first two. In the last three the first part of (38) is `Z W_g + η_g = 0` (Step 1 of the paper for this case). "One small factor" is proved without Lemma D.9 and without the parity (30) (note 1). |
| D proof of Lemma D.12, steps 1 to 3, case (n) | `claimGated_castSucc_of_frozen` (`Depth/StepsGatedN.lean`) | **PART** of the proof; true (proved) | Any real-analytic gate. Hypotheses: (16) for `k`, (38) with the frozen network, `(D_{k+1})`, good and regular `θ`. |
| D proof of Lemma D.12 from (28) to (38), case (+), gated blocks | `flat_at_generic_ray_gated_rmsNorm`, `flat_of_suffixFlat_gated_rmsNorm`, `flat_of_suffixFlat_swiglu_rmsNorm`, `flat_of_suffixFlat_geglu_rmsNorm` (`Depth/RayGatedPlus.lean`) | **PART** of the proof; **not proved** (`sorry`); I found no counterexample and judged them true by hand (note 2) | Any gate with `GateFar` and with `hone` in the first two; (iii) with the network itself; `ż(n) = (nZ − ⟨nZ, n⟩ n/d) W_read + n η_read`. |
| D proof of Lemma D.12 from (28) to (38), case (+), GELU blocks | `flat_at_generic_ray_mlp_rmsNorm`, `flat_of_suffixFlat_mlp_rmsNorm`, `flat_of_suffixFlat_gelu_rmsNorm` (`Depth/RayMlpPlus.lean`) | **PART** of the proof; **not proved** (`sorry`); judged true by hand for GELU; the first two say more than the paper (note 3) | Stated for an MLP block with any activation that has `GateFar` and `hone`. No (ii). |
| D proof of Lemma D.12, steps 1 to 3, case (+) | `claimGated_castSucc_of_flat_rmsNorm`, `claimRMS_castSucc_of_flat_rmsNorm` (`Depth/StepsPlus.lean`) | **PART** of the proof; true (proved) | Hypothesis (38) only (no (16)), as in the paper's Step 3 for the case (+). Any real-analytic gate or activation. |
| **D Lemma D.12** | `claimGated_castSucc_swiglu`, `claimGated_castSucc_swiglu_rmsNorm`, `claimGated_castSucc_geglu`, `claimGated_castSucc_geglu_rmsNorm`, `claimRMS_castSucc_gelu` (`Depth/StepGated.lean`) | **SAME** | The statements are those of the fifth audit. Case (n): proved. Case (+): the proofs are written and rest on the seven `sorry`. |

### (a) Are the pieces true as written?

- The proved pieces are true: no `sorry`, three standard axioms (by compiling). This now includes
  `ray_induction`, `ray_induction_matrix` and `exists_far_frozen_bounds`, which were `sorry` at the
  start. Before their proofs arrived I had worked through both by hand and found no counterexample:
  for `ray_induction` I went through the empty index set, `A ≤ 0` (then `hζl` or `hζu` fails and the
  statement is empty), the order of the exponents and the tail of the series; for
  `exists_far_frozen_bounds` the induction on `L − k` goes through for real `U` when the bound for
  the derivative in the hidden state is carried along, which is why that clause is in the
  statement.
- Note 2, the four statements of `RayGatedPlus.lean` (by hand; not by machine). I followed the
  paper's proof with the Lean objects. With `y = δ/t` and `s = 1/t`, `s²` times the left side of
  (33) is `G₀(s, y) + ∑ ν ζ G(s, y)` with `ζ = δ/t`, `ν = t δ'/δ`, and `G₀`, `G` real-analytic at
  `(0, 0)` and even in `s`, because `𝓑(t² h) = scaledSuffix(s, h)` depends on `s` through `s⁴` and
  `ż(tΞ)/t = z₁ + t² z₃`. So `ray_induction_matrix` applies, `hone` applies with even `a`, `b`, and
  (ii), (iii) give `ż^g = 0`. The density argument for `flat_of_suffixFlat_gated_rmsNorm` uses
  `hdense`, `value_ne_zero`, `frozen_deriv` and Lemma D.2 for the case (+) (which needs `hreg`).
  Edge cases: with no token every conclusion is trivially true (so the missing `[Nonempty T]` is
  harmless); `d`, `hid k` or `A k` empty contradict a good `θ`. The two statements "from (K3)"
  follow from the general one and from proved statements: this I checked by compiling (`Fit.lean`).
- Note 3, the three statements of `RayMlpPlus.lean`. For GELU the same derivation goes through
  (`m = 1`, `scaledSuffix` depends on `s` through `s²`), and `flat_of_suffixFlat_gelu_rmsNorm`
  follows from the general statement and proved ones (`Fit.lean`). But the two general statements
  are for every activation with `GateFar` and `hone`, and SiLU has both (`gateFar_silu`,
  `one_small_factor_silu`; `Fit.lean` compiles this instance). So they also say: (38) holds for
  **MLP blocks with the SiLU activation** under pre-RMSNorm. The paper does not treat this case, and
  its parity (30) is "in a gated block". By hand I think the claim is true: in the variable `s` the
  maps `a`, `b` are even for an MLP block too. By a computation (`silu_mlp_rank.py`, 40 digits):
  for small skipless pre-RMSNorm networks of MLP blocks with random weights (`ε = 0.1`, one token;
  `d = 2`, 3 hidden units, `L = 2`; `d = 3`, 4 hidden units, `L = 2`; `d = 2`, `d_in = 3`, 2 hidden
  units, `L = 3`) the Jacobian has the rank `P − (L+1) d(d−1)/2` for SiLU as for GELU (29 of 32,
  57 of 66, 30 of 34), with the next singular value below `10⁻⁴⁰`. This agrees with the general
  statement and does not prove it. Only the GELU instance is needed for Theorem 5.2.

### (b) Do the docstrings say honestly what part of the paper each piece is?

Yes, in every file. Each header quotes the paper's passage and then says what is stated: the real
variable (`FarFromZero`, `MillsAtInfinity`, `ScaledSuffix`, `FrozenFar`), existence or a clause in
the place of an explicit object (`FrozenFar`: the clause for the derivative in the place of the
holomorphic extension), the rows `T` in the place of one token (`BlockIdentityGated`, `RayDense`,
`RayGatedN`, `RayGatedPlus`, `RayMlpPlus`, `FrozenFar`), and the variable `s = 1/t`
(`OneSmallFactor`, `ScaledSuffix`, `RayInduction`). Four places could say more:

1. `Depth/RayGatedN.lean` (header) and `STATEMENTS.md` line 193 do not say how "one small factor"
   is done in the case (n). The Lean proof does not use Lemma D.9 and does not use the parity (30):
   the frozen network is homogeneous, so the coefficients of (34) are constants times powers of
   `t`, and (36) for `α = 1_j` reads `c + ν_j(t) c' → 0` with `|ν_j(t)| → ∞` (the last clause of
   `GateFar`), which gives `c' = 0`. By reading the proof and by `grep`: the file uses neither
   `millsRatio` nor `one_small_factor_…`, and its theorems have the three standard axioms. The
   header of `Depth/StepGated.lean` is right about this ("which uses Lemmas D.8 and D.11, the
   frozen network and the induction on the exponents").
2. `Depth/StepGated.lean`, header: "`Depth/RayGatedPlus.lean` and `Depth/RayMlpPlus.lean` (which use
   Lemmas D.8, D.9 and D.10 and the induction on the exponents)". These two files have no proofs
   yet, so they use nothing; and for SwiGLU blocks the step is the parity, not Lemma D.9.
3. `Activations/OneSmallFactor.lean`, header: the evenness of `a` and `b` "is what the parity (30)
   gives in this variable". For gated blocks that is right. For the Lean proofs under pre-RMSNorm
   the evenness comes from the form of the coefficient maps (they depend on `s` through `s²`), for
   MLP blocks as well; see note 3.
4. `Depth/RayMlpPlus.lean`, header: it says "for an MLP block whose activation `σ` has
   `GateFar σ σ' p`", and does not say that this takes in an activation that the paper does not
   treat (SiLU).

### (c) Do the pieces fit?

Yes.

- The final assembly `Depth/StepGated.lean` compiles in the library with the current sources: each
  of its five proofs is "the ray up to (38)" followed by "steps 1 to 3", and the hypotheses of the
  second are the conclusions of the first, in the same form. Case (n):
  `frozen_flat_of_suffixFlat_swiglu/_geglu` give `hgate` and `hfro` of
  `claimGated_castSucc_of_frozen`; "regular" comes from `regular_of_goodForConesGated_swiglu/_geglu`.
  Case (+): `flat_of_suffixFlat_swiglu_rmsNorm/_geglu_rmsNorm` give `h38` of
  `claimGated_castSucc_of_flat_rmsNorm`, and `flat_of_suffixFlat_gelu_rmsNorm` gives `hz`, `hw` of
  `claimRMS_castSucc_of_flat_rmsNorm`.
- Inside the case (+), by compiling (`Fit.lean`, three examples with `[Nonempty T]`): the three
  statements "from (K3)" follow from `flat_of_suffixFlat_gated_rmsNorm` or
  `flat_of_suffixFlat_mlp_rmsNorm` with `gateFar_silu` or `gateFar_gelu`, with
  `one_small_factor_silu` or `one_small_factor_gelu` as `hone`, with
  `regular_of_goodForCones…` as `hreg`, and with the two statements of `RayDense.lean` as `hdense`
  (after `pow_one` or `sq_abs`). So what is left to prove is the two general statements for gated
  blocks and the two for MLP blocks.
- The copies of `Depth/StepsPlus.lean` and `Depth/RayGatedN.lean` that I compiled alone at the start
  commit gave no error and no warning.

---------------------------------------------------------------------------------------------------

## What the authors should know

Nothing false, vacuous or drifted was found. In order of weight:

1. **`RayMlpPlus.lean` says more than the paper** (note 3): its two general statements cover MLP
   blocks with the SiLU activation under pre-RMSNorm. If their proof succeeds, Lean will have
   proved a step that the paper does not claim. If it does not, only the generality has to be
   given up (state them for GELU, or drop the evenness from `hone` for MLP blocks); Theorem 5.2 is
   not touched.
2. **Seven statements are still `sorry`**, and three of the five final theorems rest on them:
   Theorem 5.2 (ii) for `ε > 0` and (iii) under pre-RMSNorm. Theorem 5.2 (iii) without
   normalization, for SwiGLU and for GeGLU blocks, is proved with the three standard axioms.
3. **In the case (n) the Lean proof of "one small factor" is shorter than the paper's**: it needs
   neither Lemma D.9 nor the parity (30), only the homogeneity of the frozen network and
   `y|δ'(y)|/δ(y) → ∞`. The paper may want to say this, or keep one argument for both cases.
4. **For SwiGLU blocks without normalization the Lean proofs use `d ≥ 1` only** (`D1.lean`). The
   paper's `d ≥ 2` is kept in the statement. GeGLU and GELU blocks need `d ≥ 2` (the matrices
   `c_j c_j^⊤`).
5. The three statements "from (K3)" of the case (+) have no `[Nonempty T]`, while those of the case
   (n) have it. Both are true; the difference is only one of form.
6. `Symmetry/OnlyOrthogonal.lean` appeared while I read. It is not in my brief; no reader has
   compared it.

## Corrections for `STATEMENTS.md` (lines at `0d967ff`)

1. Lines 28-34, "Not yet compared by such a reader …": the sixteen files named there and the
   header and proofs of `Depth/StepGated.lean` are now compared (sixth reader, 24 November 2026:
   19 paper statements and proof pieces against 79 Lean names; none false, vacuous or changed in
   meaning; `Depth/RayGatedPlus.lean` and `Depth/RayMlpPlus.lean` judged by hand, their proofs are
   `sorry`). Not yet compared: `Symmetry/OnlyOrthogonal.lean`.
2. Line 193 (`Depth/RayGatedN.lean`). Add: the first two statements are for every gate with
   `GateFar`; in the last three the first part of (38) is stated as `Z W_g + η_g = 0` (Step 1 of
   the paper in the case (n)) and they need at least one token; "one small factor" needs no
   hypothesis here, because the proof gets it from the homogeneity of the frozen network and from
   `y|δ'(y)|/δ(y) → ∞`, not from Lemma D.9 or the parity (30).
3. Line 188 (`GateFar`). Add: the clause `y|δ'(y)|/δ(y) → ∞` is used in the case (n) only, in the
   place of Lemma D.9 and of the parity.
4. Line 198 (`Depth/RayMlpPlus.lean`). Add: the first two statements hold for every activation with
   `GateFar` and "one small factor"; SiLU has both, so they also state (38) for MLP blocks with the
   SiLU activation, which is not a case of the paper.
5. Line 195 (`Activations/OneSmallFactor.lean`). "(the parity (30) in this variable)": say "for
   gated blocks this evenness is the parity (30); in the variable `s` it holds because the
   coefficient maps depend on `s` through `s²` (`scaledSuffix_neg`)".
6. Line 184 (`MeromorphicAtInfinity`). Add: the exponent `l` is a natural number (the paper: an
   integer), and "vanishes identically" is stated as "vanishes for all large `t`".
7. Line 191 (Lemma D.11). Add: for every gate with `GateFar`.
8. Lines 99, 100, 114, 162 (D Theorem 4.3) and 306, 307 (S Theorem 4.2). The paper's statements
   are "at generic parameters"; the Lean names of these rows hold for every `θ` under explicit
   conditions (`E` and every write of rank `d`; for line 114 also no vanishing value column; for
   306, 307 `E` of rank `d`). Add "under the conditions of the proof" to the rows, as the
   neighbouring rows and the note on Theorem 4.3 have it.
9. Notes, after "Theorem 5.2 (i) … the proof uses `d ≥ 1` only": add "Theorem 5.2 (iii) for SwiGLU
   blocks without normalization: the proof uses `d ≥ 1` only; the paper's `d ≥ 2` is kept in the
   statement".
10. Note "At generic parameters" (lines 222-224): it can now say "checked by machine by the sixth
    reader: two additive Haar measures on the parameter space have the same sets of measure zero,
    and linear coordinates carry one to a positive multiple of the Lebesgue measure of `ℝ^P`".

One correction outside the index: the header of `Depth/StepGated.lean` (see (b), item 2).

## What I could not check

- **The seven statements with `sorry`** (`Depth/RayGatedPlus.lean`, `Depth/RayMlpPlus.lean`): by
  hand, by the fit of their forms (compiled), and by a rank computation on three small networks.
  No machine proof.
- **`Symmetry/OnlyOrthogonal.lean`**: not read against the skips paper.
- **The proofs** of the proved files: I did not read them line by line. I rely on Lean and on the
  axiom check. I read the proof of `frozen_flat_core` in `RayGatedN.lean` only far enough to see
  how "one small factor" is done.
- **Private helpers**: not compared with the paper one by one. Their axioms are checked.
- **Older files of the chain** (`Depth/Cones.lean`, `Depth/SuffixGated.lean`, `Depth/Suffix.lean`,
  `Depth/SuffixRMS.lean`, `Dimension/GenericRank.lean`, `Generic/*`, `Activations/Analytic.lean`,
  `Activations/Gaussian.lean`, `Activations/GeluExpansion.lean`, `Activations/ReLU.lean`): I read
  the definitions that the new statements use (`suffix`, `SuffixFlat`, `Claim`, `ClaimRMS`,
  `Regular`, `IsOpenConvexCone`, `frozenGated`, `frozenMlp`, `GoodForConesGated`, `GoodForConesMlp`,
  `tangentRMS`, `rmsRow`, `rmsNorm`, `gaussPdf`, `gaussCdf`, `gelu`, `geluDeriv`, `silu`,
  `siluDeriv`) and the elaborated forms of the statements that the chain calls, and I checked that
  none of these files changed since the fifth audit. I did not compare them with the paper again.
- **`millsRatio` against the paper's formula with `erf`**: by reading (a line of algebra), not by
  machine.
- **`lake build`**: not run, as the brief asks. What I compiled, I compiled against the library of
  `/home/claude/lp/lean`, which its owner built at `0d967ff`.
- **That the claim for rows `T` is the claim for one token**: not a Lean statement, as the index
  says; I did not prove it.

Scratch files: `/home/claude/audit6/` (`Sig3.lean`, `Ax2.lean`, `Chk.lean`, `Chk2.lean`,
`Chk3.lean`, `Fit.lean`, `D1.lean`, `Haar.lean`, `FD.lean`, `silu_mlp_rank.py`,
`silu_mlp_rank2.py`, with their outputs).
