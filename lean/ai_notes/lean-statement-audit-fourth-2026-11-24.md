STATUS: complete

# Fourth audit of Lean statements against the papers (24 November 2026)

Reader: an independent reader who did not write the statements. Brief:
`/home/claude/proj_up/audit4_brief_2026-11-24.md`. Nothing under `/home/claude/lw`,
`/home/claude/lp` or `/home/claude/skips_fix_gauges` was changed; no `git commit`, no push, no
`lake build`. Scratch files and their outputs are in `/home/claude/audit4/`.

"D" is the dimension paper, "S" the skips paper, "A" the absorb paper. Statement and equation
numbers are those of the PDFs (text by `pdftotext -layout`); "tex n" is a line of the `.tex`.
Lean line numbers are those of the sources on the branch `lean-plus` during the audit.

What was read. In full: `Dimension/Functional.lean`, `Dimension/UpperBound.lean`,
`Dimension/RescalingMlp.lean`, `OneBlock/Rescale.lean`, `OneBlock/ReGLU.lean` (the version with
`sorry`, 212 lines); every public statement with its docstring, and the definitions, of
`Dimension/UpperBoundRMSNorm.lean`, `Dimension/Rescaling.lean`, `Dimension/RescalingGate.lean`,
`Residual/UpperBoundSymmetries.lean`, `OneBlock/ResidualRescale.lean`, `Absorb/FirstBlock.lean`;
`STATEMENTS.md` in full. Of the papers: D Sections 2, 4 and 5.1, Appendix B, Appendix C up to the
end of Step 3; S Section 2, Sections 4.1 and 4.2, Appendix A.6, Appendix B up to Lemma B.2; A
Section 2, Theorem 4.5 and its proof in Appendix A.1. The sections on definitions of the three
earlier audits were relied on for `Arch`, `Params`, `eval`, `funDim`, `flat`, `cobDir`,
`rescaleDir`, "generic", `OneBlockGeneric`, `OneBlockGenericGated`, `subProd`.

The library changed while I read. `OneBlock/ReGLU.lean` had 13 statements with `sorry` when I
read it; commit `7b016f3` then filled in the 13 proofs and changed no statement (its diff removes
13 lines, all `sorry`). The first run of `#print axioms` showed `sorryAx` for these 13 names; after
the library was rebuilt by its authors (05:26 UTC) the second run shows the three standard axioms
for all 94 names of the scope, and `#check @` gives the same 94 statements as before, character
for character (`Check1_first.out` against `Check1.out`).

---------------------------------------------------------------------------------------------------

## (1) Summary table

Verdicts: SAME, LEAN STRONGER, LEAN WEAKER, DIFFERENT, PART, as in the brief. "Pair" means the two
Lean statements that are made for a block with a kink: the value of `funDim`, and a batch of inputs
with no hidden unit at its kink on which the Jacobian has that rank.

| # | Paper statement | Lean names | Verdict | The difference in one line |
|---|---|---|---|---|
| 1 | D Definition 4.1 with the convention of Appendix C for ReLU, ReLU², ReGLU ("every input" means every input with no hidden unit at its kink) | `funDim`, `flat`, `jacobianRank` (as used in the new files), `flatOn`, `noKink`, `noKinkGate` | **DIFFERENT (by definition), with no effect on the theorems in scope** | Lean takes the batches of inputs at which the network is differentiable in `θ`, a set that contains the no-kink inputs. `funDim ≥` the paper's value at every `θ`; equal at generic `θ` for one block (the pairs); larger at some non-generic `θ` (machine-checked example). |
| 2 | D Appendix C: "some finite batch has the kernel `K(θ)`", `fd = P − dim K(θ)` | `funDim_add_finrank_flat'`, `exists_jacobianRank_add_finrank_flatOn`, `flat_le_flatOn` | **SAME in form; LEAN STRONGER in hypotheses** | No differentiability is assumed. With the Lean `K(θ)` (inputs where differentiable). For the no-kink inputs only the existence of a batch of rank `P − dim K_U(θ)` is public. |
| 3 | D Section 4: the directions in which a symmetry moves `θ` are in the kernel of every Jacobian | `mem_flat_of_hasDerivAt'`, `funDim_add_finrank_le_of_le_flat'` | **LEAN STRONGER** | The hypothesis of differentiability is dropped. |
| 4 | D Theorem 4.3, changes of basis only (no `s`), cases (n) and (+) | `cobDir_mem_flat_skipless'`, `funDim_add_le_skipless'`, `cobDir_mem_flat_skipless_rmsNorm'`, `funDim_add_le_skipless_rmsNorm'` | **PART** (of 4.3), **LEAN STRONGER** than the unprimed forms | Arbitrary maps `f_ℓ`, every real `ε`; pointwise under "`E` and the writes of rank `d`"; no statement "at generic parameters" for arbitrary `f_ℓ`. |
| 5 | D Appendix B: rescaling of a ReLU unit, of a ReLU² unit | `relu_homogeneous`, `reluSq_homogeneous`, `eval_rescale_mlp`, `rescaleDirMlp`, `rescaleDirMlp_mem_flat` | **LEAN STRONGER** | `λ > 0` as in the paper; all units at once; any `σ` with `σ(λz) = λ^k σ(z)`; any `χ`, any stream matrices. |
| 6 | D Appendix B: "ReGLU, in addition", the rescaling of the gate | `eval_rescale_gate`, `rescaleDirGate`, `rescaleDirGate_mem_flat` | **LEAN STRONGER** | The same generality. |
| 7 | D Appendix B: the rescaling of the value of a gated unit is a flat direction | `rescaleDir_mem_flat'` | **LEAN STRONGER** | No differentiability of the gate or of `χ`; all stream matrices. |
| 8 | D Lemma B.1 for ReLU, ReLU², ReGLU blocks | `cobDir_add_rescaleDirMlp_injective`, `cobDir_add_rescaleDir_add_rescaleDirGate_injective`, `ae_read_col_ne_zero`, `ae_gate_ne_zero` | **DIFFERENT in form** (as in the first audit) | Lean: the directions determine `(X, α)` resp. `(X, α, β)` under the conditions of the paper's proof. The statement on the group ("act locally freely") is not stated. |
| 9 | D Theorem 4.3 for ReLU and ReLU² blocks, with `s = ∑ d_hidden`, cases (n) and (+) | `funDim_add_le_skipless_mlp_rescale`, `funDim_add_le_skipless_mlp_rescale_rmsNorm`, `ae_funDim_add_le_skipless_relu`, `ae_funDim_add_le_skipless_reluSq`, `ae_funDim_add_le_skipless_relu_rmsNorm`, `ae_funDim_add_le_skipless_reluSq_rmsNorm` | **LEAN STRONGER** | Same bound for a quantity that is at least the paper's; needs only `d_in ≥ d ≥ 1` and widths `≥ d` (not `d_out ≥ d`, not `d ≥ 2`); every real `ε`. |
| 10 | D Theorem 4.3 for ReGLU blocks, with `s = 2 ∑ d_hidden` | `funDim_add_le_skipless_gated_gate`, `funDim_add_le_skipless_gated_gate_rmsNorm`, `ae_funDim_add_le_skipless_reglu`, `ae_funDim_add_le_skipless_reglu_rmsNorm` | **LEAN STRONGER** | As row 9. |
| 11 | D Lemma C.3 for ReLU and ReLU² | `UnitsRescale`, `relu_unitsRescale`, `reluSq_unitsRescale` | **SAME** | A restatement of `relu_units_flat`, `reluSq_units_flat` with the exponent `k`. |
| 12 | D Theorem 5.1 / C.1 for a ReLU block | `ae_funDim_relu_oneBlock` with `ae_exists_jacobianRank_relu_oneBlock`; under the conditions of the proof `funDim_mlp_oneBlock_rescale`, `exists_jacobianRank_mlp_oneBlock_rescale`, `flatOn_noKink_le_mlp_rescale`, `differentiableAt_eval_of_mem_noKink` | **SAME** (the pair) | Each statement alone is not the paper's: the pair is (machine-checked, `TestA.lean`). |
| 13 | D Theorem 5.1 / C.1 for a ReLU² block | `ae_funDim_reluSq_oneBlock`, `ae_exists_jacobianRank_reluSq_oneBlock` | **SAME** (the pair) | As row 12. |
| 14 | D Theorem 5.1 / C.1 for a ReGLU block, and the generic conditions of Appendix C for gated blocks | `OneBlockGenericReGLU`, `ae_oneBlockGenericReGLU`, `noKinkGate`, `differentiableAt_eval_of_mem_noKinkGate`, `flatOn_noKinkGate_le_reglu`, `funDim_reglu_oneBlock`, `exists_jacobianRank_reglu_oneBlock`, `ae_funDim_reglu_oneBlock`, `ae_exists_jacobianRank_reglu_oneBlock` | **SAME** (the pair) | The extra condition is the paper's "`e_i` … is not proportional to `c_i`". |
| 15 | S Theorem 4.2, the bound with identity skips, changes of basis only | `cobDir_const_mem_flat_residual'`, `cobDir_const_mem_flat_residual_rmsNorm'`, `funDim_add_le_residual'`, `funDim_add_le_residual_rmsNorm'` | **PART** (no `s`), **LEAN STRONGER** than the unprimed forms | Arbitrary `f_ℓ`, every real `ε`, only `E` of rank `d`. |
| 16 | S Theorem 4.2, the bound with identity skips, with `s` (Theorem A.17 (ii), Lemma A.18) | `funDim_add_le_residual_gated`, `funDim_add_le_residual_mlp_rescale`, `funDim_add_le_residual_gated_gate`, each with `_rmsNorm`, and the six with `ae_` | **LEAN STRONGER** for gated, ReLU, ReLU², ReGLU blocks; **PART** of the theorem | Only `d_in ≥ d ≥ 1`; no condition on the widths or on `d_out`. Not stated: attention blocks. The bound without skips is in the files for D Theorem 4.3. |
| 17 | S Theorem 4.6 (i) / B.1 (i) for a ReLU and for a ReLU² block | `ae_funDim_relu_oneBlock_residual`, `ae_exists_jacobianRank_relu_oneBlock_residual`, `ae_funDim_relu_oneBlock_residual_eq_add`, the three with `reluSq`; `funDim_mlp_oneBlock_rescale_residual`, `exists_jacobianRank_mlp_oneBlock_rescale_residual`, `flatOn_noKink_le_mlp_rescale_residual`, `differentiableAt_eval_residual_of_mem_noKink` | **SAME** for 4.6 (i) (the pairs); **PART** of B.1 (i) | Not stated: the clause of B.1 (i) with biases. |
| 18 | S Theorem 4.6 (i) / B.1 (i) for a ReGLU block | `flatOn_noKinkGate_le_reglu_residual`, `funDim_reglu_oneBlock_residual`, `exists_jacobianRank_reglu_oneBlock_residual`, `ae_funDim_reglu_oneBlock_residual`, `ae_exists_jacobianRank_reglu_oneBlock_residual`, `ae_funDim_reglu_oneBlock_residual_eq_add` | **SAME** (the pairs); **PART** of B.1 (i) | As row 17. |
| 19 | A Theorem 4.5, the conditions of its proof | `FirstBlockGeneric`, `ae_firstBlockGeneric` | **SAME** | The three conditions of the first sentences of the proof, one for one. |
| 20 | A Theorem 4.5 for ReLU | `exists_ne_skipless_of_first_card_lt_relu`, `ae_ne_skipless_of_first_card_lt_relu` | **LEAN STRONGER** | No `d ≥ 2`, no minimal widths in either network, the residual network may have no block; one null set for all skipless networks. |
| 21 | A Theorem 4.5 for GELU | `exists_ne_skipless_of_first_card_lt_gelu`, `ae_ne_skipless_of_first_card_lt_gelu` | **LEAN STRONGER** | As row 20. |
| 22 | A proof of Theorem 4.5, "GELU": `F(tX)/t` tends to the output of the ReLU network with the same weights | `Params.withActivation`, `tendsto_eval_gelu_ray` | **SAME** for the limit; the rate is **not stated** | Lean: any stream matrices. The paper's `O(1/t)` and `κ < 0.17` are not in the statement. |

No Lean statement in scope was found false or vacuous. One definition changes the object (row 1);
section (5) says what follows from it and what does not.

---------------------------------------------------------------------------------------------------

## (2) Definitions new in these files, and old definitions used in a new way

### 2.1 `funDim`, `jacobianRank`, `flat` at a network with a kink (scope 1; D Definition 4.1, tex 255-261; D Appendix C, "Notation and flat directions", tex 535; S the same paragraph, tex 1227)

Paper. Definition 4.1: "`fd(θ) = max_X rank 𝐃F_X(θ)` … where the maximum is over all finite batches
`X`." Appendix C: "Call `η` flat if `𝐃_θ F(θ, x) η = 0` for every input `x`, and let `K(θ)` be the
space of flat directions. For ReLU, ReLU² and ReGLU blocks, `F(θ, x)` is differentiable in `θ` at the
inputs `x` at which no hidden unit sits at its kink, which form an open set of full measure, and
'every input' means every such input. … some finite batch has the kernel `K(θ)`. By rank–nullity,
the functional dimension at `θ` is therefore `P − dim K(θ)`."

So for a ReLU, ReLU² or ReGLU network the paper's objects are, with `N(θ)` the set of the inputs
at which no hidden unit sits at its kink:
`K_N(θ) = {η : 𝐃_θF(θ, x)η = 0 for all x ∈ N(θ)}` and
`fd_paper(θ) = P − dim K_N(θ)` = the largest rank of the Jacobian over the finite batches of inputs
of `N(θ)`.

Lean (`Dimension/Functional.lean:34-49`, unchanged since the first audit):
```
jacobianRank A S X θ = finrank (range (fderiv ℝ (evalBatch A S X) θ))
funDim A S θ        = sSup {r | ∃ n (X : Fin n → Matrix T dIn ℝ), r = jacobianRank A S X θ}
flat A S θ          = ⨅ x, ker (fderiv ℝ (fun θ' => eval A S θ' x) θ)
```
Mathlib's `fderiv` is the Fréchet derivative where the map is differentiable and `0` elsewhere.
Write `U(θ)` for the set of the inputs `x` at which `θ' ↦ F_θ'(x)` is Fréchet differentiable at `θ`.
Then, clause by clause:

| Object | What it is in Lean | Source of the claim |
|---|---|---|
| `flat A S θ` | `K_U(θ)`: the directions that are flat at every input of `U(θ)`. An input outside `U(θ)` contributes the kernel of the zero map, which is everything. | definition; `fderiv_zero_of_not_differentiableAt` |
| `jacobianRank A S X θ` | the rank of the true Jacobian if every input of the batch is in `U(θ)`; `0` if one input of the batch is not (the tuple of outputs is differentiable only if every component is). | `differentiableAt_pi`; private `flat_le_ker'` |
| `funDim A S θ` | the largest rank of the true Jacobian over the finite batches of inputs of `U(θ)`, and it equals `P − dim K_U(θ)`. | `funDim_add_finrank_flat'` (proved, no hypothesis) |

Comparison with the paper.

1. **`N(θ) ⊆ U(θ)`.** The paper says so ("`F(θ, x)` is differentiable in `θ` at the inputs `x` at
   which no hidden unit sits at its kink"). Lean states it for one block:
   `differentiableAt_eval_of_mem_noKink` (MLP block, any `σ` differentiable away from `0`, no skip),
   `differentiableAt_eval_residual_of_mem_noKink` (with the skip),
   `differentiableAt_eval_of_mem_noKinkGate` (ReGLU, all stream matrices). For networks of two or
   more blocks Lean has no definition of "no hidden unit at its kink" and no such statement.
2. **Hence `fd_paper(θ) ≤ funDim(θ)` at every `θ`.** A batch of inputs of `N(θ)` is a batch of
   inputs of `U(θ)`; its Lean `jacobianRank` is the rank of the true Jacobian (scratch `TestA.lean`,
   example A1) and is at most `funDim` (`jacobianRank_le_funDim`; scratch A2 states
   `fdNoKink θ ≤ funDim θ` for every `θ`, where `fdNoKink` is the supremum over the batches of
   inputs of `noKink θ`).
3. **Can a batch that contains an input with a unit at its kink lower the Lean value?** No. The
   value is a supremum over all batches, and the same batch without that input is also a batch.
   If the network is not differentiable in `θ` at that input the whole batch has rank `0` and is
   simply lost.
4. **Can it raise the Lean value?** Yes, when the network is differentiable in `θ` at that input
   (the input is in `U(θ)` and not in `N(θ)`): the batch then counts with its true Jacobian. Such
   inputs exist at every `θ`:
   - the input `0`, or an input with a zero row: every hidden unit of that token sits at its kink,
     and the output of that token is `0` for all weights (scratch `TestE.lean`: for a one-block ReLU
     network `eval θ' 0 = 0` for all `θ'`, so the output at `0` is differentiable in `θ`, and
     `0 ∉ noKink θ`);
   - for ReLU², every input (ReLU² is differentiable everywhere, `hasDerivAt_reluSq`);
   - for ReGLU, an input at which the gate and the value of a unit vanish together (the term
     `max(z, 0) w a` of the unit is then of second order in the change of the weights);
   - for ReLU, an input at a kink of a hidden unit whose write row is `0`.
   At an input of one of these kinds the derivative is the limit of the derivatives at the no-kink
   inputs near it, when there are such inputs, and then it puts no new condition on flat
   directions (my computation for one block, not a Lean statement). But at a weight at which a
   hidden unit sits at its kink at **every** input, the paper's set `N(θ)` is empty and, read
   literally, `fd_paper(θ) = 0`, while the Lean value can be positive. Machine-checked
   example (`TestB.lean`, standard axioms only): a ReLU² block with one token,
   `d = d_in = d_out = 1`, two hidden units, `E = D = 1`, read `(1, 0)`, write `(1, 1)ᵀ`. The read
   column of the second unit is `0`, so `noKink θ₀ = ∅` (`noKink_θ₀`), every batch of inputs of
   `noKink θ₀` has `jacobianRank = 0` (`jacobianRank_noKink_θ₀`), and `0 < funDim θ₀`
   (`funDim_θ₀_pos`; the direction that scales the readout is not flat, since the output at
   `x = 1` is `1`). The same happens for a ReLU block when the read column and the write row of a
   hidden unit are both `0` (not machine-checked; the term of that unit is of second order). These
   weights form a set of measure zero.
5. **At generic parameters, one block:** the two values are equal. This is not a property of the
   definitions; it is what the pair of Lean theorems gives (2.1.1 below).
6. **At generic parameters, two or more blocks:** no Lean statement compares the two values, and
   I did not prove that they are equal. For the statements in scope this does not matter: the only
   statements for two or more blocks are upper bounds on `funDim`, and by point 2 an upper bound on
   `funDim` is an upper bound on the paper's value.
7. **"Which form an open set of full measure"** (the paper, of the no-kink inputs): no Lean
   statement says that `noKink θ` is open, has full measure or is not empty. (It is true at the
   parameters of `OneBlockGeneric`; at `θ₀` above the set is empty.)

#### 2.1.1 What the pair of statements gives

For a one-block network with a ReLU, ReLU² or ReGLU block, with or without the skip, Lean makes
two statements at almost every `θ` (and under the explicit conditions of the proof), with `v` the
value of the paper (`P − 2d² − s` or `P − d² − s`):

- (a) `funDim A S θ + (P − v) = P`: the largest rank over the batches of inputs of `U(θ)` is `v`;
- (b) `∃ n X, (∀ i, X i ∈ noKink θ) ∧ jacobianRank A S X θ + (P − v) = P`: one batch of no-kink
  inputs has rank `v` (and on such a batch `jacobianRank` is the rank of the true Jacobian).

From (a): every batch of no-kink inputs has rank at most `v`, so `fd_paper(θ) ≤ v`. From (b):
`fd_paper(θ) ≥ v`. Together: `fd_paper(θ) = v`, which is the paper's statement, and also
`K_N(θ) = K_U(θ)` at these `θ`. Scratch `TestA.lean`, example A3, proves from the two Lean theorems
for ReLU that `∀ᵐ θ, fdNoKink θ + (2d² + d_hidden) = P`.

Statement (a) alone says less than the paper in one direction (it does not exclude that the rank
`v` is reached only with inputs of `U(θ) ∖ N(θ)`) and more in the other (the bound holds on the
larger set of inputs). Statement (b) alone gives `fd_paper(θ) ≥ v`; with the upper bound of
Theorem 4.3, which Lean has for these blocks, (b) alone already gives the paper's value (scratch
A4). So (a) is needed for the value of the Lean `funDim`, and (b) for the paper's set of inputs.

**Verdict for the definition: DIFFERENT** (the set of inputs is `U(θ)`, not `N(θ)`), in a way
that the statements in scope absorb: the upper bounds are bounds for a quantity that is at least
the paper's, and the equalities come as pairs.

A correction to the first audit (its section 2.4): it says that "Lean's convention drops every
batch that contains one such input [with a unit at its kink], which gives the same maximum". The
batch is dropped only if the network is not differentiable in `θ` at that input, and "the same
maximum" is a theorem at generic parameters for one block, not a consequence of the definitions
(point 4).

### 2.2 `flatOn` (`Dimension/Functional.lean:312-314`)
```
flatOn A S θ U = ⨅ x ∈ U, ker (fderiv ℝ (fun θ' => eval A S θ' x) θ)
```
The directions that are flat at every input of a set `U` of inputs, with the same convention for
`fderiv`. With `U = noKink θ` (where the network is differentiable in `θ`) this is the paper's
`K(θ)` for ReLU and ReLU² blocks, `K_N(θ)` above; with `U = noKinkGate θ` for ReGLU. `U = ∅` gives
the whole space. `flat A S θ = flatOn A S θ Set.univ` in content, and `flat_le_flatOn` is the
inclusion `flat ≤ flatOn U`. Same as the paper's `K(θ)` when `U` is the paper's set of inputs.

### 2.3 `rescaleDirMlp k θ α` (`Dimension/RescalingMlp.lean:50-55`) against D Appendix B (tex 480-489)
Paper: "ReLU: `(c_i, a_i) ↦ (λc_i, a_i/λ)`, `λ > 0`; ReLU²: `(c_i, a_i) ↦ (λc_i, a_i/λ²)`, `λ > 0`",
`c_i` the read column and `a_i` the write row of hidden unit `i`.
Lean: `E := 0`, `D := 0`, read entry `(a, i)` of block `ℓ` is `α ℓ i * θ.read ℓ a i`, write entry
`(i, a)` is `-(k * α ℓ i) * θ.write ℓ i a`.
- This is the derivative at `τ = 0` of the rescaling with `λ_i = e^{τ α_i}` and exponent `k`:
  the column `c_i` moves by `α_i c_i`, the row `a_i` by `−k α_i a_i`. For `k = 1` it is the direction
  of the ReLU rescaling, for `k = 2` that of the ReLU² rescaling. Same.
- All hidden units of all blocks at once, one number `α ℓ i` per unit: the span over `α` is the
  span of the paper's one-unit directions. Same.
- `k : ℕ` is a free argument and `σ` does not enter the definition.

### 2.4 `rescaleDirGate k θ β` (`Dimension/RescalingGate.lean:37-43`) against D Appendix B, "ReGLU, in addition" (tex 485)
Paper: "`(c_i, a_i) ↦ (λc_i, a_i/λ)`, `λ > 0`", `c_i` the gate column.
Lean: `E := 0`, `D := 0`; gate column `Sum.inl i` of block `ℓ` times `β ℓ i`; value columns
`Sum.inr i` get `0`; write row `i` times `−k β ℓ i`. For `k = 1` this is the derivative of the
paper's rescaling at `λ = e^{τβ}`. Same. Gate and value columns are not exchanged (`inl` is the gate
in `Arch.gated`: `f M = σ (M t (inl i)) * M t (inr i)`).

### 2.5 The hypothesis "positively homogeneous of degree `k`"
`hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z`, with `k : ℕ`. `relu_homogeneous` has
`lam ^ 1`, `reluSq_homogeneous` has `lam ^ 2`. Only `λ > 0` is used, as in the paper (ReLU is not
homogeneous for `λ < 0`). The hypothesis also holds for activations that the paper does not treat
here: the identity (`k = 1`), the Heaviside step (`k = 0`), leaky ReLU (`k = 1`), `z ↦ |z|^k`
(scratch `TestC.lean`, C2, for the first two). The statements that take `hσ` are therefore stated
for more activations than ReLU and ReLU²; they are upper bounds and identities, true for all of
them.

### 2.6 `UnitsRescale σ σ' k n m q` (`OneBlock/Rescale.lean:36-46`) against D Lemma C.3, ReLU and ReLU² (tex 576-583, eq. (7))
Paper: "Let every `a_i ≠ 0` and let the `c_i` be nonzero and pairwise non-collinear … If
`𝐃_φ G(φ, x)ψ = 0` for all `x`, then `ψ_M = 0`, `ψ_γ = 0`, and … for ReLU, `(ψ_{c_i}, ψ_{β_i}) =
λ_i (c_i, β_i)` and `ψ_{a_i} = −λ_i a_i` for some number `λ_i`; for ReLU², … `ψ_{a_i} = −2λ_i a_i`",
with `𝐃_φ G(φ, x)ψ = xψ_M + ψ_γ + Σ_i [σ(z_i)ψ_{a_i} + σ'(z_i)(xψ_{c_i} + ψ_{β_i}) a_i]` (eq. (7)).

| Clause | Lean | Same? |
|---|---|---|
| `a_i ≠ 0` | `∀ i, a i ≠ 0` | same |
| `c_i` nonzero | `∀ i, c i ≠ 0` | same |
| pairwise non-collinear | `∀ i j, i ≠ j → ∀ r : ℝ, c i ≠ r • c j` | same |
| the identity "for all `x`" | `∀ x, (∀ i, x ⬝ᵥ c i + β i ≠ 0) → x ᵥ* ψM + ψγ + ∑ i, (σ(z_i) • ψa i + (σ'(z_i) * (x ⬝ᵥ ψc i + ψβ i)) • a i) = 0` | the paper's convention: only at the inputs with no unit at its kink. A weaker hypothesis, so a stronger statement than one "for all `x`". |
| conclusion | `ψM = 0 ∧ ψγ = 0 ∧ ∃ lam, ∀ i, ψc i = lam i • c i ∧ ψβ i = lam i * β i ∧ ψa i = -(k * lam i) • a i` | same: `k = 1` gives `−λ_i a_i`, `k = 2` gives `−2λ_i a_i` |

`σ'` is a separate argument (the derivative away from the kink); `relu_unitsRescale` uses
`reluDeriv = 1[z > 0]`, `reluSq_unitsRescale` uses `reluSqDeriv = 2 max(z, 0)`. With no hidden unit
(`q` empty) the statement is "`xψ_M + ψ_γ = 0` for all `x` gives `ψ_M = 0`, `ψ_γ = 0`". **SAME.**

### 2.7 `noKink θ` (`OneBlock/Rescale.lean:73-75`)
`{x | ∀ (t : T) (i : hid 0), (x * θ.E * θ.read 0) t i ≠ 0}`, for one MLP block without
normalization. The entry `(t, i)` of `x E W_read` is the argument of hidden unit `i` at token `t`,
and the kink of ReLU and of ReLU² is at `0`. This is the paper's "inputs `x` at which no hidden unit
sits at its kink", for all tokens of the input. Same. The same set serves with and without the
skip (the skip does not change the arguments of the units of the one block). Notes: the set
depends on `θ`; it does not depend on `σ` (the kink is assumed at `0`); with no token or no hidden
unit it is the set of all inputs; it never contains the input `0` when there is a token and a
hidden unit.

### 2.8 `noKinkGate θ` (`OneBlock/ReGLU.lean:62-64`)
`{x | ∀ (t : T) (i : hid 0), (x * θ.E * θ.read 0) t (Sum.inl i) ≠ 0}`: only the **gates** are
required to be nonzero. The value `(x E W_read) t (inr i)` may vanish. This is the paper's set: the
kink of a ReGLU unit `σ(z_i) w_i a_i` is that of `σ = max(·, 0)` at the gate `z_i = 0`; in the proof
of Lemma C.3 for ReGLU the hyperplanes are `H_i = {z_i = 0}`, and the Lean form of the lemma
(`relu_gated_units_flat`) has its hypothesis at the `x` with `∀ i, x ⬝ᵥ c i + β i ≠ 0`. Where a
value vanishes and the gate does not, the network is differentiable in `θ`
(`differentiableAt_eval_of_mem_noKinkGate`). Same.

### 2.9 `OneBlockGenericReGLU θ` (`OneBlock/ReGLU.lean:52-58`) against D Appendix C, "Reduction" (tex 545) and Lemma C.3 (tex 576)
Paper, "Reduction": "For generic parameters `E`, `D`, `W_read` and `W_write` have rank `d_model`,
every `a_i` is nonzero, and the `c_i` are nonzero and pairwise non-collinear … In a gated block, in
the same way, every `e_i` is nonzero and is not proportional to `c_i`." Lemma C.3: "for the gated
blocks let also every `e_i ≠ 0`, with `(e_i, β'_i)` not proportional to `(c_i, β_i)`."

Lean: the two fields
- `gated : OneBlockGenericGated θ` (first audit: the four ranks, rows `a_i` of `A = W_write D`
  nonzero, gate columns `c_i` of `C = E W_read` nonzero and pairwise non-collinear, value columns
  `e_i` nonzero);
- `value_not_gate : ∀ (i : hid 0) (r : ℝ), (θ.E * θ.read 0)ᵀ (inr i) ≠ r • (θ.E * θ.read 0)ᵀ (inl i)`.

The second field is "`e_i` is not proportional to `c_i`", for the columns of `C = E W_read` in
`ℝ^{d_in}`, of the same hidden unit `i`. With zero biases the hypothesis of Lemma C.3,
`(e_i, 0) ≠ r (c_i, 0)` for all `r`, is this clause (scratch C4). So `OneBlockGenericReGLU` is the
paper's list of generic conditions for a gated block, complete; it is `OneBlockGenericGated` that
leaves one of them out (first audit). `r = 0` repeats `e_i ≠ 0`. **SAME.**

Is the extra clause generic under the stated hypotheses? Yes: `e_i = E v_i` and `c_i = E g_i` with
`v_i, g_i ∈ ℝ^d` the value and gate columns of `W_read`; `E` has rank `d` at generic parameters
(`d_in ≥ d`), and two generic vectors of `ℝ^d` are not proportional when `d ≥ 2`.
`ae_oneBlockGenericReGLU` states it under `2 ≤ d`, `d ≤ d_in`, `d ≤ d_out`, `d ≤ d_hidden` and is
proved. `d ≥ 2` is needed: for `d = 1` the condition fails at **every** `θ` when the block has a
hidden unit (scratch `TestC.lean`, C3), as the paper's "of dimension `d_model ≥ 2`" says.

### 2.10 `Params.withActivation σ' θ` (`Absorb/FirstBlock.lean:40-46`)
The same four weights `E`, `read`, `write`, `D`, as parameters of the MLP network with the
activation `σ'` (scratch D6: the four components are equal by `rfl`). This is the paper's "the ReLU
network with the same weights". Same.

### 2.11 `FirstBlockGeneric θ` (`Absorb/FirstBlock.lean:52-60`) against A proof of Theorem 4.5 (tex 648)
Paper: "Outside a set of weights of measure zero, `E` and `D` have rank `d_model`, no read of a unit
vanishes, and `I + W_read^ℓ[:, S] W_write^ℓ[S, :]` is invertible for every block `ℓ` and every set `S`
of its units".

| Clause | Lean | Same? |
|---|---|---|
| `E` has rank `d` | `rank_E : θ.E.rank = Fintype.card d` | same |
| `D` has rank `d` | `rank_D : θ.D.rank = Fintype.card d` | same |
| no read of a unit vanishes | `read_ne_zero : ∀ ℓ (i : hid ℓ), (θ.read ℓ)ᵀ i ≠ 0` (column `i` of `W_read^ℓ`) | same |
| `I + W_read^ℓ[:,S] W_write^ℓ[S,:]` invertible for every `ℓ`, `S` | `isUnit_det : ∀ ℓ (S : Finset (hid ℓ)), IsUnit (1 + subProd S (θ.read ℓ) (θ.write ℓ)).det`, with `subProd S Wr Ww = Wr * diagonal(1_S) * Ww` | same; `S = ∅` is included and trivial |

The structure is stated for any activation `σ` and for `χ = id`. It is a condition on the residual
network only. The paper's scope condition `E D ≠ 0` follows from `rank_E` and `rank_D` when `d` is
not empty (scratch `TestD.lean`, D5). **SAME** as the conditions of the paper's proof.

### 2.12 `ε : ℝ` arbitrary in the statements under pre-RMSNorm
The primed statements and those of `RescalingMlp.lean`, `RescalingGate.lean`,
`UpperBoundSymmetries.lean` take `(ε : ℝ)` with no hypothesis, where the earlier statements had
`0 < ε`. `rmsNorm ε` is a total function for every real `ε` (first audit, 2.2: `rmsRow 0 0 = 0`;
for `‖v‖²/d + ε ≤ 0` the row is sent to `0`). What these statements say:
- `ε > 0`: the paper's case (+) (D: "'under pre-RMSNorm' means in the case (+)", tex 187; S: "RMSNorm
  with the constant `ε > 0`", tex 225). Same.
- `ε = 0`: a true statement about the Lean total function, with the bound of the group `O(d)`,
  `dim = d(d−1)/2`. It is **not** the paper's statement for `ε = 0`, which has the group `CO(d)` of
  dimension `d(d−1)/2 + 1` (D, the sentence after Theorem 4.3, for `tanh`, GELU, SwiGLU, GeGLU; S
  Theorem A.17 and Theorem B.1 (iv), where for positively homogeneous blocks without skips the
  group is larger still). The Lean bound for `ε = 0` is weaker than the paper's by `L + 1` (without
  skips) or `1` (with identity skips), and it is about a function that is also defined where the
  paper's network is not.
- `ε < 0`: outside the papers.

### 2.13 Instance arguments, elaborated forms, degenerate cases
From `Check1.out` (`#check @` on the 94 names):
- The one-block statements (`OneBlock/Rescale.lean`, `ResidualRescale.lean`, `ReGLU.lean`) carry
  `[Fintype T] [Nonempty T]`, `hid : Fin 1 → Type`, and the four hypotheses `2 ≤ card d`,
  `card d ≤ card dIn`, `card d ≤ card dOut`, `card d ≤ card (hid 0)` in the statements "for almost
  every `θ`". These are the hypotheses of D Theorem C.1 and S Theorem B.1 (i), one for one.
- The upper bounds carry no `[Nonempty T]`. Those "for almost every `θ`" with the term `s` carry
  `[Nonempty d]` (through `ae_read_col_ne_zero`, `ae_gate_ne_zero`, `ae_value_ne_zero`): with `d`
  empty every matrix is empty, `P = 0`, and the bound with `s > 0` would be false.
- `funDim A 0 θ` is the network without skips, `funDim A 1 θ` the network with identity skips: the
  stream matrices are `Fin L → Matrix d d ℝ`, and `1` elaborates to the family of identity
  matrices (first audit, 2.10). The stream matrices are fixed, not parameters: `Params` has no
  skip. So no `funDim` in the library is the functional dimension of a network with learned skips.
- `L = 0` is allowed in every statement with a general `L`: the network is `x ↦ χ(xE)D`.
- Natural-number arithmetic: every statement is an addition, `funDim + (…) ≤ P` or `= P`; the only
  division is `card d * (card d - 1) / 2` (first audit, 2.10: the right number for every `d`).
  `2 * ∑ ℓ, card (hid ℓ)` is `s` for ReGLU.
- `Absorb/FirstBlock.lean`: `d : Type` (universe `0`) for the residual network, while `T dIn dOut :
  Type*`. The skipless network has `d' : Type*` in the two statements under `FirstBlockGeneric`
  (scratch D3 applies one with `d' : Type 3`) and `d' : Type` in the two statements "for almost
  every", where `d'` is bound inside `∀ᵐ θ`. No mathematical content: every finite type is
  equivalent to a `Fin n : Type`.
- An additive Haar measure exists on the parameter spaces in question (scratch A5), so the
  statements "for almost every" are not about an empty family of measures.

---------------------------------------------------------------------------------------------------

## (3) One entry per statement

Elaborated forms are those of `/home/claude/audit4/Check1.out`. In all of them
`{T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut]`
unless said otherwise, and `P` stands for `Module.finrank ℝ (Params A dIn dOut)`.

### 3.A Dimension paper

#### 3.1 D Appendix C, "Notation and flat directions" (tex 535), and D Section 4, "A continuous symmetry adds to the redundancy" (tex 263): scope 1

Paper: quoted in 2.1.

Lean (`Dimension/Functional.lean:312-498`), for every `A : Arch T d L`, every stream matrices `S`,
every `θ`, with no hypothesis on the maps `f_ℓ` and `χ`:
```
flat_le_flatOn : ∀ θ (U : Set (Matrix T dIn ℝ)), flat A S θ ≤ flatOn A S θ U
mem_flat_of_hasDerivAt' : ∀ θ (γ : ℝ → Params A dIn dOut) η, HasDerivAt γ η 0 → γ 0 = θ →
    (∀ᶠ τ in 𝓝 0, ∀ x, eval A S (γ τ) x = eval A S θ x) → η ∈ flat A S θ
funDim_add_finrank_flat' : ∀ θ, funDim A S θ + finrank ↥(flat A S θ) = P
funDim_add_finrank_le_of_le_flat' : ∀ θ, ∀ V ≤ flat A S θ, funDim A S θ + finrank ↥V ≤ P
exists_jacobianRank_add_finrank_flatOn : ∀ θ U,
    (∀ x ∈ U, DifferentiableAt ℝ (fun θ' => eval A S θ' x) θ) →
    ∃ n (X : Fin n → Matrix T dIn ℝ), (∀ i, X i ∈ U) ∧ jacobianRank A S X θ + finrank ↥(flatOn A S θ U) = P
```
Comparison, clause by clause.
- "the directions in which [a continuous family of maps that preserves the function] moves `θ` lie
  in the kernel of every such Jacobian": `mem_flat_of_hasDerivAt'`, for a curve `γ` through `θ` with
  velocity `η` that keeps the function for all `τ` near `0` and all inputs. Conclusion: `η` is flat
  at every input at which the network is differentiable in `θ`, in particular at every no-kink
  input. The unprimed form assumed differentiability at every input. **LEAN STRONGER** (a
  hypothesis dropped; the conclusion is the same sentence with the Lean `K(θ)`).
- "the functional dimension at `θ` is therefore `P − dim K(θ)`": `funDim_add_finrank_flat'`, an
  identity of the Lean objects of 2.1 (the inputs of `U(θ)`), with no hypothesis. For a
  differentiable network it is the earlier `funDim_add_finrank_flat`. For a network with a kink it
  is the paper's sentence with `U(θ)` in the place of the no-kink inputs. **SAME in form.**
- "some finite batch has the kernel `K(θ)`", for the paper's inputs:
  `exists_jacobianRank_add_finrank_flatOn` with `U = noKink θ`, in the form "some finite batch of
  inputs of `U` has the rank `P − dim K_U(θ)`". The hypothesis `hU` (differentiable on `U`) is what
  the paper asserts of the no-kink inputs. `U = ∅` is allowed (the empty batch, rank `0`,
  `K_∅ = ` everything). **SAME.** The other half, "every batch of inputs of `U` has rank at most
  `P − dim K_U(θ)`", is true by the same rank–nullity argument and has no public Lean statement;
  the one-block theorems get the bound from `funDim` instead.
- Edge cases: `n = 0` batches are allowed and have rank `0`. Empty `T`: every statement here is
  true and says nothing.

**Verdict: SAME in form, LEAN STRONGER in hypotheses; the object `funDim` differs from the paper's
for networks with a kink as said in 2.1.**

#### 3.2 D Theorem 4.3 for the changes of basis, for arbitrary maps `f_ℓ`: scope 2

Paper (tex 271-273): "Without normalization or under pre-RMSNorm, at generic parameters, the
functional dimension of a network of `L` blocks is at most `P − (L+1) dim 𝒢 − s`." `𝒢 = GL(d)`, of
dimension `d²`, without normalization, and `O(d)`, of dimension `d(d−1)/2`, under pre-RMSNorm
(tex 220). Scope of Section 2 (tex 193): `d_in, d_out ≥ d ≥ 2`, `d_hidden ≥ d`.

Lean:
```
cobDir_mem_flat_skipless' : ∀ θ, A.χ = id → ∀ X : Fin (L+1) → Matrix d d ℝ, cobDir θ X ∈ flat A 0 θ
funDim_add_le_skipless' : ∀ θ, A.χ = id → θ.E.rank = card d → (∀ ℓ, (θ.write ℓ).rank = card d) →
    funDim A 0 θ + (L + 1) * card d ^ 2 ≤ P
cobDir_mem_flat_skipless_rmsNorm' : ∀ θ (ε : ℝ), A.χ = rmsNorm ε → ∀ X, (∀ ℓ, (X ℓ)ᵀ = -X ℓ) →
    cobDir θ X ∈ flat A 0 θ
funDim_add_le_skipless_rmsNorm' : ∀ θ (ε : ℝ), A.χ = rmsNorm ε → θ.E.rank = card d →
    (∀ ℓ, (θ.write ℓ).rank = card d) → funDim A 0 θ + (L + 1) * (card d * (card d - 1) / 2) ≤ P
```
Comparison: the statements of the first audit (`cobDir_mem_flat_skipless`, `funDim_add_le_skipless`
and the two with `_rmsNorm`) without `hf : ∀ ℓ, Differentiable ℝ (A.f ℓ)` and, under pre-RMSNorm,
without `0 < ε`. They are the part of Theorem 4.3 that counts the changes of basis (`s` is not
counted), under the conditions of the proof of Lemma B.1 for them (`E` and every write of rank
`d`). For a network with a kink the bound is for the Lean `funDim`, which is at least the paper's
value (2.1), so it gives the paper's bound. There is no primed statement "at generic parameters"
for an arbitrary `A` (the unprimed `ae_funDim_add_le_skipless` assumes `hf`); it follows in one
line from the public `ae_rank_E_write` (scratch `TestF.lean`, F1).

**Verdict: PART of Theorem 4.3 (no `s`); LEAN STRONGER than the paper's theorem restricted to the
changes of basis (arbitrary maps `f_ℓ`, no `d_out ≥ d`, no `d ≥ 2`, every real `ε`; see 2.12 for
what `ε ≤ 0` means).**

#### 3.3 D Appendix B, the rescaling of the values of a gated unit (tex 484): scope 2

Paper: "SwiGLU, GeGLU, ReGLU: `(e_i, a_i) ↦ (e_i/λ, λa_i)`, `λ ≠ 0`."
Lean: `rescaleDir_mem_flat' : ∀ (θ : Params (Arch.gated σ χ hid) dIn dOut) (S : Fin L → Matrix d d ℝ)
(α : ∀ ℓ, hid ℓ → ℝ), rescaleDir θ α ∈ flat (Arch.gated σ χ hid) S θ`, for every `σ : ℝ → ℝ` and
every `χ`.
Comparison: the statement `rescaleDir_mem_flat_stream` of the first audit without
`Differentiable ℝ σ` and `Differentiable ℝ χ`. The function is preserved by `eval_rescale`
(`λ ≠ 0`, first audit: SAME); the direction is that of `λ = e^{τα} > 0`. **LEAN STRONGER** (no
differentiability; the ReLU gate is covered).

#### 3.4 D Appendix B, the rescaling of a ReLU and of a ReLU² hidden unit (tex 482-483): scope 3

Paper: "ReLU: `(c_i, a_i) ↦ (λc_i, a_i/λ)`, `λ > 0`; ReLU²: `(c_i, a_i) ↦ (λc_i, a_i/λ²)`, `λ > 0`."

Lean (`Dimension/RescalingMlp.lean`):
```
relu_homogeneous : ∀ lam z : ℝ, 0 < lam → relu (lam * z) = lam ^ 1 * relu z
reluSq_homogeneous : ∀ lam z : ℝ, 0 < lam → reluSq (lam * z) = lam ^ 2 * reluSq z
eval_rescale_mlp : (∀ lam z, 0 < lam → σ (lam * z) = lam ^ k * σ z) →
    ∀ (θ θ' : Params (Arch.mlp σ χ hid) dIn dOut) (c : ∀ ℓ, hid ℓ → ℝ), (∀ ℓ i, 0 < c ℓ i) →
    θ'.E = θ.E → θ'.D = θ.D → (∀ ℓ a i, θ'.read ℓ a i = c ℓ i * θ.read ℓ a i) →
    (∀ ℓ i a, θ'.write ℓ i a = (c ℓ i ^ k)⁻¹ * θ.write ℓ i a) →
    ∀ S x, eval (Arch.mlp σ χ hid) S θ' x = eval (Arch.mlp σ χ hid) S θ x
rescaleDirMlp_mem_flat : (same hσ) → ∀ θ S α, rescaleDirMlp k θ α ∈ flat (Arch.mlp σ χ hid) S θ
```
Comparison.
- Range of `λ`: the paper has `λ > 0`; Lean has `0 < c ℓ i`. Same. (For `λ < 0` the rescaling of a
  ReLU unit does not preserve the function, and Lean does not claim it. For ReLU² the paper has
  `λ > 0` as well, although `(λz)² = λ² z²` for all `λ` does not carry over to `max(·, 0)²`.)
- Exponent: read column times `c`, write row times `(c^k)⁻¹`; `k = 1` and `k = 2` are the paper's two
  lines. Same.
- One number per hidden unit, all units of all blocks at once: the paper's one-unit rescalings
  commute, and their composition is this map. Same.
- "Preserves the function": for every `χ` and all stream matrices `S` (no skips, identity skips,
  fixed linear skips), which S Appendix A.6 says in words ("it preserves the function of a skipless
  and of a residual network alike, with or without normalization").
- "Its direction is flat": `rescaleDirMlp_mem_flat`, with no differentiability of `σ`.

**Verdict: LEAN STRONGER** (the paper's two rescalings are the cases `relu`, `k = 1` and `reluSq`,
`k = 2`).

#### 3.5 D Appendix B, "ReGLU, in addition" (tex 485): scope 4

Paper: "`(c_i, a_i) ↦ (λc_i, a_i/λ)`, `λ > 0`", so "`s = 2 d_hidden` for ReGLU" (tex 489).
Lean (`Dimension/RescalingGate.lean:50-172`): `eval_rescale_gate`, for a gated network with a gate
`σ(λz) = λ^k σ(z)` (`λ > 0`): gate columns times `c ℓ i > 0`, value columns unchanged, write rows
times `(c ℓ i ^ k)⁻¹`, same `E` and `D`, give the same function for every `χ` and all `S`;
`rescaleDirGate_mem_flat`: the direction `rescaleDirGate k θ β` is flat.
Comparison: `λ > 0` same; `k = 1` for the ReLU gate is the paper's line; the value columns are
untouched, as in the paper. **LEAN STRONGER** (any positively homogeneous gate, any `χ`, any `S`).

#### 3.6 D Lemma B.1 (Locally free action) for ReLU, ReLU² and ReGLU blocks (tex 493-495): scopes 3 and 4

Paper: "… a network whose blocks are `tanh`, GELU, ReLU, ReLU² or gated blocks with at least
`d_model` hidden units … If `d_in ≥ d_model`, then at generic parameters the changes of basis and the
symmetries inside the blocks act locally freely." Proof: "`E` has rank `d_model`, so `G_0 = I` … No
column of a generic `W_read^ℓ` vanishes, so every entry of `λ` is 1: for a ReGLU block this fixes both
rescalings of every hidden unit … `W_write^ℓ` has rank `d_model` because the block has at least
`d_model` hidden units, so `G_ℓ = I`."

Lean:
```
cobDir_add_rescaleDirMlp_injective : ∀ (k : ℕ) (θ : Params (Arch.mlp σ χ hid) dIn dOut),
    θ.E.rank = card d → (∀ ℓ, (θ.write ℓ).rank = card d) → (∀ ℓ i, (fun a => θ.read ℓ a i) ≠ 0) →
    Function.Injective fun p : (Fin (L+1) → Matrix d d ℝ) × (∀ ℓ, hid ℓ → ℝ) =>
      cobDir θ p.1 + rescaleDirMlp k θ p.2
cobDir_add_rescaleDir_add_rescaleDirGate_injective : ∀ (k : ℕ) (θ : Params (Arch.gated σ χ hid) dIn dOut),
    θ.E.rank = card d → (∀ ℓ, (θ.write ℓ).rank = card d) →
    (∀ ℓ i, (fun a => θ.read ℓ a (inr i)) ≠ 0) → (∀ ℓ i, (fun a => θ.read ℓ a (inl i)) ≠ 0) →
    Function.Injective fun p => cobDir θ p.1 + rescaleDir θ p.2.1 + rescaleDirGate k θ p.2.2
ae_read_col_ne_zero [Nonempty d] : ∀ᵐ θ ∂μ, ∀ ℓ i, (fun a => θ.read ℓ a i) ≠ 0     (MLP networks)
ae_gate_ne_zero [Nonempty d] : ∀ᵐ θ ∂μ, ∀ ℓ i, (fun a => θ.read ℓ a (inl i)) ≠ 0   (gated networks)
```
Comparison: as in the first audit for the gated case. Lean states the infinitesimal form: the
linear map from `(X, α)` (or `(X, α, β)`) to the directions of the parameters is injective. Its
hypotheses are the three facts of the paper's proof (`E` of rank `d`; every write of rank `d`; no
column of a read zero, for ReGLU neither a gate column nor a value column), and each holds at
generic parameters under `d_in ≥ d`, widths `≥ d` (`ae_rank_E_write`) and `d ≥ 1`. The statement on
the group and its equivalence with this form are not stated. The injectivity does not use `hσ`,
and holds for every `k`. This is what the proof of Theorem 4.3 uses.

**Verdict: DIFFERENT in form (infinitesimal), with the hypotheses of the paper's proof; the cases
ReLU, ReLU² and the gate of ReGLU, which the first audit listed as missing, are now stated.**

#### 3.7 D Theorem 4.3 for ReLU and ReLU² blocks, with the term `s`: scope 3

Paper: Theorem 4.3 (3.2 above), with "a block has `s = d_hidden` for ReLU, ReLU², SwiGLU and GeGLU"
(tex 489).

Lean (`Dimension/RescalingMlp.lean:284-421`):
```
funDim_add_le_skipless_mlp_rescale : (∀ lam z, 0 < lam → σ (lam * z) = lam ^ k * σ z) →
    ∀ θ : Params (Arch.mlp σ id hid) dIn dOut, θ.E.rank = card d → (∀ ℓ, (θ.write ℓ).rank = card d) →
    (∀ ℓ i, (fun a => θ.read ℓ a i) ≠ 0) →
    funDim (Arch.mlp σ id hid) 0 θ + ((L + 1) * card d ^ 2 + ∑ ℓ, card (hid ℓ)) ≤ P
funDim_add_le_skipless_mlp_rescale_rmsNorm : the same for Arch.mlp σ (rmsNorm ε) hid, every ε : ℝ,
    with (L + 1) * (card d * (card d - 1) / 2) in the place of (L + 1) * card d ^ 2
ae_funDim_add_le_skipless_relu [Nonempty d] (μ) [μ.IsAddHaarMeasure] :
    card d ≤ card dIn → (∀ ℓ, card d ≤ card (hid ℓ)) →
    ∀ᵐ θ ∂μ, funDim (Arch.mlp relu id hid) 0 θ + ((L + 1) * card d ^ 2 + ∑ ℓ, card (hid ℓ)) ≤ P
ae_funDim_add_le_skipless_reluSq, ae_funDim_add_le_skipless_relu_rmsNorm (ε : ℝ),
ae_funDim_add_le_skipless_reluSq_rmsNorm (ε : ℝ) : the same for reluSq and under rmsNorm ε
```
Comparison, clause by clause.
- "at generic parameters": `∀ᵐ θ ∂μ` for an additive Haar measure. Same.
- "the functional dimension … is at most `P − (L+1) dim 𝒢 − s`": `funDim + ((L+1) dim 𝒢 + s) ≤ P`,
  with `dim 𝒢 = d²` resp. `d(d−1)/2`. Same form. `funDim` is the Lean object of 2.1; it is at least
  the paper's value, so the Lean bound gives the paper's bound. (For this last step one needs that
  the network is differentiable in `θ` at the no-kink inputs, which is the paper's own assertion;
  Lean states it for one block only.)
- `s = ∑_ℓ d_hidden^ℓ`: `∑ ℓ, card (hid ℓ)`, one per hidden unit, widths may differ per block. Same.
- Genericity conditions: the pointwise statements have the three conditions of 3.6; the statements
  "for almost every `θ`" have `d_in ≥ d`, every width `≥ d` and `[Nonempty d]`. The paper's scope
  has in addition `d_out ≥ d` and `d ≥ 2`, which Lean does not use. (Scratch `TestC.lean`, C1: the
  theorem at `d = d_in = 2`, `d_out = 1`, two blocks of widths 3 and 4, reads `fd + 19 ≤ P`.)
- Which `ε`: every real `ε`; `ε > 0` is the paper's case (+). For `ε = 0` see 2.12: the paper's D
  claims its `ε = 0` bound only for `tanh`, GELU, SwiGLU, GeGLU, so for these blocks there is no
  paper statement at `ε = 0` to compare with.
- Blocks: `Arch.mlp σ …` uses one `σ` for all blocks ("all blocks of a network are of one kind").
- `L = 0`: the bound `fd + d² ≤ P` for `x ↦ xED`, true when `d_in ≥ d`.
- The pointwise statement holds for every positively homogeneous `σ` (2.5), not only ReLU, ReLU².

**Verdict: LEAN STRONGER** (the paper's bound for ReLU and ReLU² blocks in the cases (n) and (+),
with fewer hypotheses and for a quantity at least the paper's). This closes two gaps of the first
audit ("ReLU²: weaker conclusion (no `s`)", "ReLU: no Lean statement applies").

#### 3.8 D Theorem 4.3 for ReGLU blocks, with `s = 2 ∑ d_hidden`: scope 4

Paper: Theorem 4.3 with "`s = 2 d_hidden` for ReGLU" (tex 489).
Lean (`Dimension/RescalingGate.lean:345-482`): `funDim_add_le_skipless_gated_gate` (a gate with
`hσ`, `Arch.gated σ id hid`, `E` and the writes of rank `d`, no value column and no gate column of a
read zero): `funDim … 0 θ + ((L + 1) * card d ^ 2 + 2 * ∑ ℓ, card (hid ℓ)) ≤ P`;
`funDim_add_le_skipless_gated_gate_rmsNorm` (every `ε : ℝ`, with `card d * (card d - 1) / 2`);
`ae_funDim_add_le_skipless_reglu`, `ae_funDim_add_le_skipless_reglu_rmsNorm`
(`[Nonempty d]`, `card d ≤ card dIn`, `∀ ℓ, card d ≤ card (hid ℓ)`, gate `relu`).
Comparison: as 3.7, with the three kinds of direction (changes of basis, rescalings of the values,
rescalings of the gates) and `s = 2 ∑ d_hidden`. The read of a gated block is `d × (hid ⊕ hid)`, so
`P` counts `2 d d_hidden` entries of each read; the write is `hid × d`, and "width `≥ d`" is on
`hid ℓ`. **Verdict: LEAN STRONGER**, as 3.7.

After 3.2, 3.7 and 3.8 (with the statements of the first audit for `tanh`, GELU, SwiGLU, GeGLU),
Theorem 4.3 is stated for every kind of block of the paper except attention, in the cases (n) and
(+). Not stated: attention blocks; the sentence after the theorem for `ε = 0` with `𝒢 = CO(d)`.

#### 3.9 D Lemma C.3 for ReLU and ReLU² in the form `UnitsRescale`: scope 5

See 2.6. `relu_unitsRescale : UnitsRescale relu reluDeriv 1 n m q` and `reluSq_unitsRescale :
UnitsRescale reluSq reluSqDeriv 2 n m q`, for all finite `n m q`. **SAME** as Lemma C.3 for these two
kinds (hypotheses: `a_i ≠ 0`, `c_i ≠ 0`, pairwise non-collinear; the identity at the inputs with no
unit at its kink; conclusion with `−λ_i a_i` resp. `−2λ_i a_i`; with the linear term, the constant
and the biases).

#### 3.10 D Theorem 5.1 (tex 319-321) and Theorem C.1 (tex 527-533) for a ReLU and for a ReLU² block: scope 5

Paper (C.1): "Let `d_model ≥ 2` and `d_in, d_out ≥ d_model`, let inputs range over all of `ℝ^{T×d_in}`,
and consider networks with one block, without normalization and without biases. The block is a
`tanh`, GELU, ReLU, ReLU², ReGLU, SwiGLU or GeGLU block with at least `d_model` hidden units … At
generic parameters the functional dimension is `P − 2d²_model − s`", `s = d_hidden` for ReLU and
ReLU².

Lean (`OneBlock/Rescale.lean`; `[Nonempty T]`, `hid : Fin 1 → Type`):
```
ae_funDim_relu_oneBlock (μ) [μ.IsAddHaarMeasure] : 2 ≤ card d → card d ≤ card dIn →
    card d ≤ card dOut → card d ≤ card (hid 0) →
    ∀ᵐ θ ∂μ, funDim (Arch.mlp relu id hid) 0 θ + (2 * card d ^ 2 + card (hid 0)) = P
ae_exists_jacobianRank_relu_oneBlock : the same hypotheses →
    ∀ᵐ θ ∂μ, ∃ n (X : Fin n → Matrix T dIn ℝ), (∀ i, X i ∈ noKink θ) ∧
      jacobianRank (Arch.mlp relu id hid) 0 X θ + (2 * card d ^ 2 + card (hid 0)) = P
ae_funDim_reluSq_oneBlock, ae_exists_jacobianRank_reluSq_oneBlock : the same with reluSq
```
and, under the conditions of the proof, for every `σ` with `hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z`,
`hhom` (2.5) and `hU : UnitsRescale σ σ' k dIn dOut (hid 0)`:
```
differentiableAt_eval_of_mem_noKink : hσ → ∀ θ x, x ∈ noKink θ →
    DifferentiableAt ℝ (fun θ' => eval (Arch.mlp σ id hid) 0 θ' x) θ
flatOn_noKink_le_mlp_rescale : hσ → hU → ∀ θ, OneBlockGeneric θ → ∀ η ∈ flatOn (Arch.mlp σ id hid) 0 θ (noKink θ),
    ∃ (X : Fin 2 → Matrix d d ℝ) (α : ∀ ℓ, hid ℓ → ℝ), η = cobDir θ X + rescaleDirMlp k θ α
funDim_mlp_oneBlock_rescale : hσ → hhom → hU → ∀ θ, OneBlockGeneric θ →
    funDim (Arch.mlp σ id hid) 0 θ + (2 * card d ^ 2 + card (hid 0)) = P
exists_jacobianRank_mlp_oneBlock_rescale : the same hypotheses → ∃ n X, (∀ i, X i ∈ noKink θ) ∧ jacobianRank … = …
```
Comparison, clause by clause.
- `d ≥ 2`, `d_in, d_out ≥ d`, at least `d` hidden units: the four hypotheses, one for one.
- one block: `Fin 1`. Without normalization: `χ = id`. Without biases: `Params` has none.
- "inputs range over all of `ℝ^{T×d_in}`": batches of arbitrary `x : Matrix T dIn ℝ`, any nonempty
  finite `T`.
- "at generic parameters": `∀ᵐ θ ∂μ`; the conditions are `OneBlockGeneric` (first audit: the
  paper's "`E`, `D`, `W_read` and `W_write` have rank `d_model`, every `a_i` is nonzero, and the `c_i`
  are nonzero and pairwise non-collinear"), which holds at generic parameters (`ae_oneBlockGeneric`).
- "the functional dimension is `P − 2d² − s`", for the paper's Jacobian at the no-kink inputs: the
  pair of statements (2.1.1). The first statement is the value of the Lean `funDim`; the second
  puts the rank on a batch of the paper's inputs. Checked: `TestA.lean`, A3, derives
  `∀ᵐ θ, fdNoKink θ + (2d² + d_hidden) = P` from the two.
- `s = d_hidden`: `card (hid 0)`.
- Steps of the proof as statements: `flatOn_noKink_le_mlp_rescale` is "every flat direction is the
  sum of a direction of the changes of basis of Lemma C.2 and of a rescaling of the hidden units"
  (tex 644), for the paper's `K(θ)` (flat at the no-kink inputs); the converse inclusion and the
  count `dim K(θ) = 2d² + s` are inside the proofs of the two theorems.
- For ReLU² the network is differentiable in `θ` at every input, so `funDim` is the largest rank
  over all batches; the statement on a no-kink batch is made as well, as the paper's convention
  also names ReLU².
- Concrete sizes (`TestA.lean`, A5): one token, `d = d_in = d_out = 2`, three hidden units: the
  theorem reads `fd + 11 = P`.
- "So the network satisfies the equality condition" (Theorem 5.1): the equality condition is not
  defined in Lean; its two halves are 3.7 with `L = 1` and this entry.

**Verdict: SAME** for ReLU and for ReLU² (as a pair of statements each). The first audit listed
both as missing.

#### 3.11 D Theorem 5.1 / C.1 for a ReGLU block: scope 6

Paper: Theorem C.1 with `s = 2 d_hidden`; the conditions of "Reduction" (2.9).

Lean (`OneBlock/ReGLU.lean`; `[Nonempty T]`, `hid : Fin 1 → Type`, gate `relu`):
```
ae_oneBlockGenericReGLU (μ) [μ.IsAddHaarMeasure] : 2 ≤ card d → card d ≤ card dIn → card d ≤ card dOut →
    card d ≤ card (hid 0) → ∀ᵐ θ ∂μ, OneBlockGenericReGLU θ        (any gate σ)
differentiableAt_eval_of_mem_noKinkGate : ∀ (S : Fin 1 → Matrix d d ℝ) θ x, x ∈ noKinkGate θ →
    DifferentiableAt ℝ (fun θ' => eval (Arch.gated relu id hid) S θ' x) θ
flatOn_noKinkGate_le_reglu : ∀ θ, OneBlockGenericReGLU θ → ∀ η ∈ flatOn (Arch.gated relu id hid) 0 θ (noKinkGate θ),
    ∃ (X : Fin 2 → Matrix d d ℝ) (α β : ∀ ℓ, hid ℓ → ℝ), η = cobDir θ X + rescaleDir θ α + rescaleDirGate 1 θ β
funDim_reglu_oneBlock : ∀ θ, OneBlockGenericReGLU θ →
    funDim (Arch.gated relu id hid) 0 θ + (2 * card d ^ 2 + 2 * card (hid 0)) = P
exists_jacobianRank_reglu_oneBlock : ∀ θ, OneBlockGenericReGLU θ →
    ∃ n X, (∀ i, X i ∈ noKinkGate θ) ∧ jacobianRank (Arch.gated relu id hid) 0 X θ + (2 * card d ^ 2 + 2 * card (hid 0)) = P
ae_funDim_reglu_oneBlock, ae_exists_jacobianRank_reglu_oneBlock : the two "for almost every θ",
    under 2 ≤ card d, card d ≤ card dIn, card d ≤ card dOut, card d ≤ card (hid 0)
```
Comparison.
- Hypotheses and conclusion: as 3.10, with `s = 2 d_hidden` (`2 * card (hid 0)`).
- The extra condition "no value column proportional to the gate column of the same unit" is the
  paper's (2.9): the "Reduction" paragraph lists it for all gated blocks, and Lemma C.3 assumes it.
  It is generic for `d ≥ 2`, and fails everywhere for `d = 1` (C3).
- Inputs: `noKinkGate` (2.8), the gates only, as in the paper.
- The form of a flat direction: Lemma C.3 for ReGLU gives `(ψ_c, ψ_β) = λ(c, β)`,
  `(ψ_e, ψ_β') = −α(e, β')`, `ψ_a = (α − λ)a`; `rescaleDir θ α` moves the value columns by `−α e` and
  the write rows by `α a`, `rescaleDirGate 1 θ β` moves the gate columns by `β c` and the write rows
  by `−β a`. With `β = λ` the sum is the direction of the lemma. Same.
- Status: the 13 proofs of this file were `sorry` when I read it and were filled in during the
  audit (commit `7b016f3`, no statement changed); the rebuilt library gives the three standard
  axioms for all of them. Before that I had checked the values numerically and independently of the
  authors' script (`reglu_rank_check4.py`: automatic differentiation in float64, inputs in every
  sector of the gate lines, `d = d_in = d_out = 2`, `d_hidden ∈ {2,3,4}`, three seeds, with and
  without the skip: the expected rank in all 18 cases; `reglu_rank_check.py`: also `d = 3` and two
  tokens, and `d = 1`, where the rank is below the formula, as it must be since the theorem needs
  `d ≥ 2`). A first version with random inputs gave a lower rank at one seed because no input fell
  into a thin sector between two gate lines: the rank is reached only on batches that meet every
  sector, which is the paper's remark that for the ReLU-type blocks the theorem does not hold for
  inputs in an arbitrary open set (S tex 1227).

**Verdict: SAME** (as a pair).

### 3.B Skips paper

#### 3.12 S Theorem 4.2 (Upper bounds), the bound with identity skips (tex 342-344; Theorem A.17 (ii), tex 823; Lemma A.18, tex 850): scope 7

Paper (4.2): "Let `𝒢` be the group of changes of basis of one hidden state, and `s` the dimension of
the symmetries inside the blocks, the same with and without skips. With or without pre-RMSNorm, at
generic parameters, the functional dimension is at most `P − (L+1) dim 𝒢 − s` without skips and at
most `P − dim 𝒢 − s` with identity skips." `𝒢 = GL(d)`, `dim = d²`, without normalization; `O(d)`,
`dim = d(d−1)/2`, under pre-RMSNorm, which in S has `ε > 0` (tex 225). Scope (tex 232):
`d_in, d_out ≥ d ≥ 2`, `d_hidden ≥ d`. Lemma A.18: "If the embedding has rank `d_model` and every
block has width at least `d_model`, then at generic parameters the changes of basis and the
symmetries inside blocks act locally freely."

Lean (`Residual/UpperBoundSymmetries.lean`), all for the stream matrices `1`:

| Blocks | Pointwise statement | Hypotheses | Conclusion | "For almost every `θ`" |
|---|---|---|---|---|
| arbitrary `f_ℓ`, `χ = id` | `funDim_add_le_residual'` | `θ.E.rank = card d` | `funDim A 1 θ + card d ^ 2 ≤ P` | not in this file (for differentiable `f_ℓ`: `ae_funDim_add_le_residual`, earlier) |
| arbitrary `f_ℓ`, `χ = rmsNorm ε`, `ε : ℝ` | `funDim_add_le_residual_rmsNorm'` | the same | `… + card d * (card d - 1) / 2 ≤ P` | not in this file |
| gated, any gate `σ` | `funDim_add_le_residual_gated`, `…_rmsNorm` | `E` of rank `d`; no value column of a read zero | `… + (dim 𝒢 + ∑ ℓ, card (hid ℓ)) ≤ P` | `ae_funDim_add_le_residual_gated`, `…_rmsNorm`: `[Nonempty d]`, `card d ≤ card dIn` |
| MLP, `σ(λz) = λ^k σ(z)` | `funDim_add_le_residual_mlp_rescale`, `…_rmsNorm` | `E` of rank `d`; no column of a read zero | `… + (dim 𝒢 + ∑ ℓ, card (hid ℓ)) ≤ P` | `ae_funDim_add_le_residual_mlp_rescale`, `…_rmsNorm`: the same two |
| gated, gate with `σ(λz) = λ^k σ(z)` | `funDim_add_le_residual_gated_gate`, `…_rmsNorm` | `E` of rank `d`; no value column and no gate column of a read zero | `… + (dim 𝒢 + 2 * ∑ ℓ, card (hid ℓ)) ≤ P` | `ae_funDim_add_le_residual_gated_gate`, `…_rmsNorm`: the same two |

and the two statements on directions, `cobDir_const_mem_flat_residual'` (`χ = id`: for every
`X : Matrix d d ℝ`, `cobDir θ (fun _ => X) ∈ flat A 1 θ`) and
`cobDir_const_mem_flat_residual_rmsNorm'` (`χ = rmsNorm ε`, `Xᵀ = −X`).

Comparison, clause by clause.
- The group and its dimension: one change of basis for the whole network, `X` at all hidden states
  (`cobDir θ (fun _ => X)`); all matrices without normalization (`d²`), the antisymmetric ones under
  pre-RMSNorm (`d(d−1)/2`, `finrank_antisymmetric`). Same as "`P − dim 𝒢 − s`".
- `s`: `∑ d_hidden` for gated blocks with any gate (SwiGLU, GeGLU: the rescalings of the values),
  `∑ d_hidden` for ReLU and ReLU², `2 ∑ d_hidden` for ReGLU. Same as the paper's numbers. `tanh` and
  GELU (`s = 0`): the first two rows.
- "the same with and without skips": the directions of the symmetries inside the blocks are flat
  for all stream matrices (`rescaleDir_mem_flat'`, `rescaleDirMlp_mem_flat`,
  `rescaleDirGate_mem_flat` take an arbitrary `S`). Same.
- Which `ε`: every real `ε`. `ε > 0` is the paper's. For `ε = 0` the paper's group with identity
  skips is `CO(d)`, of dimension `d(d−1)/2 + 1` (Theorem A.17 (i) and the end of its proof); the
  Lean bound for `ε = 0` does not have the `+1` (2.12).
- Genericity conditions: Lean needs only `E` of rank `d` (so `d_in ≥ d`) and the nonzero columns
  (so `d ≥ 1`). It needs **no condition on the widths of the blocks**, no `d_out ≥ d`, no `d ≥ 2`.
  The paper's Lemma A.18 assumes width at least `d` for both networks; its proof for the residual
  network does not use it either ("In a residual network the `G_ℓ` are equal"), so this is a
  hypothesis of the paper's lemma that the residual case does not need. Scratch C6, C7: the
  statements for ReLU without normalization and for ReGLU under `rmsNorm 1`, with no hypothesis on
  the widths.
- Learned skips: Theorem 4.2 has two clauses, without skips and with identity skips. It says
  nothing about learned skips, and neither does Theorem A.17 (ii). (The paper treats learned skips
  in Theorem 3.2, in Table 2 and in Theorem A.12 (iii).) The Lean file states nothing for learned
  skips, and could not with the present definitions: the stream matrices of `eval` are fixed, and
  `Params` has no skip (2.13).

What of Theorem 4.2 is not stated in Lean: (a) attention blocks, with `s = 2Hd_h²` per block (no
attention block is defined); (b) in this file, the clause "without skips", which is D Theorem 4.3
(3.2, 3.7, 3.8 and the first audit); (c) for arbitrary maps `f_ℓ` (rows 1 and 2 of the table) the
statement "at generic parameters" has no primed form (it follows from the public
`ae_isUnit_det_submatrix`: scratch `TestF.lean`, F2); (d) Theorem A.17 (i), the dimension of the
group of all changes of basis, and (iii).

**Verdict: PART of Theorem 4.2 (the clause with identity skips; all kinds of block except
attention). For that clause and those kinds: LEAN STRONGER** (fewer hypotheses: only
`d_in ≥ d ≥ 1`; arbitrary positively homogeneous activations and gates; a quantity at least the
paper's for blocks with a kink).

#### 3.13 S Theorem 4.6 (i) (tex 374-378) and Theorem B.1 (i) (tex 1216-1223) for a ReLU and for a ReLU² block: scope 8

Paper (4.6): "Let `L = 1`, with a `tanh`, GELU, ReLU, ReLU², ReGLU, SwiGLU, GeGLU or attention block.
(i) Without normalization, the residual network satisfies the equality condition. So does the
skipless network (Karbevski, 2026, Theorem 5.1), and the skip raises the functional dimension by
exactly `d²_model`." Paper (B.1 (i)): "Let `d_model ≥ 2`, let the input and output dimensions be at
least `d_model`, let inputs range over all of `ℝ^{T×d_in}` … Let the network have no normalization,
with or without biases, and let the block have width at least `d_model` … For generic parameters the
skipless network has functional dimension `P − 2d² − s` and the residual network `P − d² − s`; with
biases … both values are `2d_model` lower … and the skip raises the functional dimension by exactly
`d²_model`."

Lean (`OneBlock/ResidualRescale.lean`; `[Nonempty T]`, `hid : Fin 1 → Type`):
```
ae_funDim_relu_oneBlock_residual (μ) : 2 ≤ card d → card d ≤ card dIn → card d ≤ card dOut →
    card d ≤ card (hid 0) →
    ∀ᵐ θ ∂μ, funDim (Arch.mlp relu id hid) 1 θ + (card d ^ 2 + card (hid 0)) = P
ae_exists_jacobianRank_relu_oneBlock_residual : … → ∀ᵐ θ ∂μ, ∃ n X, (∀ i, X i ∈ noKink θ) ∧
    jacobianRank (Arch.mlp relu id hid) 1 X θ + (card d ^ 2 + card (hid 0)) = P
ae_funDim_relu_oneBlock_residual_eq_add : … →
    ∀ᵐ θ ∂μ, funDim (Arch.mlp relu id hid) 1 θ = funDim (Arch.mlp relu id hid) 0 θ + card d ^ 2
```
the three with `reluSq`, and under the conditions of the proof (`hσ`, `hhom`, `hU`,
`OneBlockGeneric θ`): `differentiableAt_eval_residual_of_mem_noKink`,
`flatOn_noKink_le_mlp_rescale_residual` (a direction flat on `noKink θ` for the stream matrices `1`
is `cobDir θ (fun _ => X) + rescaleDirMlp k θ α`), `funDim_mlp_oneBlock_rescale_residual`,
`exists_jacobianRank_mlp_oneBlock_rescale_residual`.

Comparison.
- Hypotheses `d ≥ 2`, `d_in, d_out ≥ d`, width `≥ d`, one block, no normalization: one for one.
- "the residual network [has functional dimension] `P − d² − s`": the pair, as in 3.10, with the
  same set `noKink θ` (the skip does not change the arguments of the hidden units). `s = d_hidden`.
- "the skipless network `P − 2d² − s`": 3.10.
- "the skip raises the functional dimension by exactly `d²`": `…_residual_eq_add`, for the Lean
  `funDim` of the two networks at the same `θ`, for almost every `θ`. By the two pairs the same
  holds for the paper's values.
- The conditions: `OneBlockGeneric` (ranks of `E`, `D`, `W_read`, `W_write`; `a_i ≠ 0`; `c_i`
  nonzero and pairwise non-collinear), which is the paper's list for part (i) (tex 1241).
- "Both networks satisfy the equality condition": not a Lean notion; the bound is 3.12 with
  `L = 1` and the equality is this entry.
- **Not stated:** B.1 (i) "with biases" ("both values are `2d_model` lower"); the library has no
  biases. Parts (ii) to (v) of B.1 and Theorem 4.6 (ii) are outside the scope and are not stated
  for these blocks.

**Verdict: SAME for Theorem 4.6 (i) for a ReLU and for a ReLU² block (as pairs); PART of Theorem
B.1 (i) (the clause without biases).**

#### 3.14 S Theorem 4.6 (i) / B.1 (i) for a ReGLU block: scope 6

Lean (`OneBlock/ReGLU.lean:825-1012`): `flatOn_noKinkGate_le_reglu_residual` (a direction flat on
`noKinkGate θ` for the stream matrices `1` is `cobDir θ (fun _ => X) + rescaleDir θ α +
rescaleDirGate 1 θ β`), `funDim_reglu_oneBlock_residual`
(`funDim (Arch.gated relu id hid) 1 θ + (card d ^ 2 + 2 * card (hid 0)) = P` under
`OneBlockGenericReGLU θ`), `exists_jacobianRank_reglu_oneBlock_residual`,
`ae_funDim_reglu_oneBlock_residual`, `ae_exists_jacobianRank_reglu_oneBlock_residual`,
`ae_funDim_reglu_oneBlock_residual_eq_add`
(`funDim … 1 θ = funDim … 0 θ + card d ^ 2` for almost every `θ`).
Comparison: as 3.13 with `s = 2 d_hidden`, the conditions `OneBlockGenericReGLU` (the paper's for
gated blocks, S tex 1241: "the value weights `(e_i, β'_i)` of each unit … have `e_i ≠ 0` and are not
proportional to its gate weights `(c_i, β_i)`") and the inputs `noKinkGate`. The third statement is
the difference of the equalities with and without the skip (scratch C5). Status as in 3.11.
**Verdict: SAME for Theorem 4.6 (i) for a ReGLU block (as pairs); PART of B.1 (i).**

### 3.C Absorb paper

#### 3.15 A Theorem 4.5 (The first block needs `2 d_model` units) (tex 373; proof tex 645-652): scope 9

Paper: "Consider networks of ReLU blocks, or of GELU blocks, without normalization. For almost
every choice of weights, a residual network with model dimension `d_model` equals no skipless
network whose first block has fewer than `2d_model` hidden units, whatever its depth and its other
widths." Scope (tex 214): "Every MLP block has at least `d_model` hidden units … Residual networks
have `ED ≠ 0` … `d_in, d_out ≥ d_model ≥ 2` … A skipless network that is compared with a residual one
may have another model dimension". Networks have `L ≥ 1` blocks; equality is equality of the
outputs `y`.

Lean (`Absorb/FirstBlock.lean`; `d : Type`, `[Nonempty T]`, `[∀ ℓ, DecidableEq (hid ℓ)]`):
```
ae_firstBlockGeneric [Nonempty d] (μ : Measure (Params (Arch.mlp σ id hid) dIn dOut)) [μ.IsAddHaarMeasure] :
    card d ≤ card dIn → card d ≤ card dOut → ∀ᵐ θ ∂μ, FirstBlockGeneric θ
exists_ne_skipless_of_first_card_lt_relu : ∀ θ : Params (Arch.mlp relu id hid) dIn dOut, FirstBlockGeneric θ →
    ∀ {L' : ℕ} {d' : Type*} [Fintype d'] (hid' : Fin (L' + 1) → Type) [∀ ℓ, Fintype (hid' ℓ)],
    card (hid' 0) < 2 * card d → ∀ θ' : Params (Arch.mlp relu id hid') dIn dOut,
    ∃ X : Matrix T dIn ℝ, eval (Arch.mlp relu id hid) 1 θ X ≠ eval (Arch.mlp relu id hid') 0 θ' X
ae_ne_skipless_of_first_card_lt_relu (μ) [μ.IsAddHaarMeasure] : card d ≤ card dIn → card d ≤ card dOut →
    ∀ᵐ θ ∂μ, ∀ (L' : ℕ) (d' : Type) [Fintype d'] (hid' : Fin (L' + 1) → Type) [∀ ℓ, Fintype (hid' ℓ)],
      card (hid' 0) < 2 * card d → ∀ θ' : Params (Arch.mlp relu id hid') dIn dOut,
      ∃ X : Matrix T dIn ℝ, eval (Arch.mlp relu id hid) 1 θ X ≠ eval (Arch.mlp relu id hid') 0 θ' X
exists_ne_skipless_of_first_card_lt_gelu, ae_ne_skipless_of_first_card_lt_gelu : the same with gelu
tendsto_eval_gelu_ray : ∀ (S : Fin L → Matrix d d ℝ) (θ : Params (Arch.mlp gelu id hid) dIn dOut) (X : Matrix T dIn ℝ),
    Tendsto (fun t : ℝ => t⁻¹ • eval (Arch.mlp gelu id hid) S θ (t • X)) atTop
      (𝓝 (eval (Arch.mlp relu id hid) S (θ.withActivation relu) X))
```
Comparison, clause by clause.
- "networks of ReLU blocks, or of GELU blocks": both networks have the same activation, `relu` or
  `gelu` (`Arch.mlp relu …` twice, `Arch.mlp gelu …` twice). Same. A residual ReLU network against a
  skipless GELU network is claimed by neither.
- "without normalization": `χ = id` in both. Same.
- "a residual network with model dimension `d_model`": `eval (Arch.mlp σ id hid) 1 θ`, `L` blocks of
  any widths `hid ℓ`, `L = 0` included (scratch D4), where the paper has `L ≥ 1` and widths `≥ d`.
- "a skipless network whose first block has fewer than `2d_model` hidden units, whatever its depth
  and its other widths": `eval (Arch.mlp σ id hid') 0 θ'` with `hid' : Fin (L' + 1) → Type`, so at
  least one block, `card (hid' 0) < 2 * card d`, the other widths free, and its own model dimension
  `d'` (as the paper's scope allows). Its embedding `θ'.E : Matrix dIn d' ℝ` and readout
  `θ'.D : Matrix d' dOut ℝ` are its own, arbitrary; the two networks share only the tokens `T`, the
  input dimension and the output dimension. No minimal width is asked of the skipless network
  (the first block may have no hidden unit).
- "equals no": `∃ X, eval … θ X ≠ eval … θ' X`, with `X` a matrix of `T` rows; `T` not empty. Same.
- Order of the quantifiers: in `ae_ne_skipless_…` the depth `L'`, the model dimension `d'`, the
  widths `hid'` and the weights `θ'` of the skipless network are all quantified **inside**
  `∀ᵐ θ`: one set of measure zero of weights of the residual network serves all skipless
  networks. This is the paper's order ("For almost every choice of weights, a residual network …
  equals no skipless network …"). The form with the skipless network fixed first follows (scratch
  D2), not conversely.
- "For almost every choice of weights": `∀ᵐ θ ∂μ` for an additive Haar measure on the weights of
  the residual network. Same.
- Hypotheses: Lean has `d_in ≥ d` and `d_out ≥ d`. It does **not** have `d ≥ 2` (for `d` empty the
  statement is true and empty: no width is `< 0`), widths `≥ d` in the residual network, or
  `ED ≠ 0` (which follows from `FirstBlockGeneric` for `d ≥ 1`, scratch D5).
- The conditions `FirstBlockGeneric` are those of the paper's proof, one for one (2.11), and hold
  for almost every choice of weights (`ae_firstBlockGeneric`, `d_in, d_out ≥ d ≥ 1`).
- Universes: 2.13.
- GELU: "as `t → ∞` the output of a GELU network at the input `tX`, divided by `t`, tends to the
  output at `X` of the ReLU network with the same weights" (tex 378), "with or without the skip"
  (tex 652): `tendsto_eval_gelu_ray`, for all stream matrices. The limit is stated, not the rate:
  the paper's proof has `h_ℓ(t)/t = h_ℓ^R + O(1/t)` and `|GELU(ty)/t − ReLU(y)| ≤ κ/t` with
  `κ < 0.17`; Lean has the bound `1` in place of `κ` (`abs_gelu_sub_relu_le`, earlier audit) and no
  rate for networks. The theorem needs only the limit.

**Verdict: LEAN STRONGER** for ReLU and for GELU (the paper's statement is the case `d ≥ 2`, `L ≥ 1`,
widths `≥ d`); the conditions of the proof **SAME**; the limit along rays **SAME**, its rate not
stated.

---------------------------------------------------------------------------------------------------

## (4) Lists

### (4a) Clauses of the paper's statements in scope that have no Lean statement

Dimension paper.
1. Definition 4.1 with the convention of Appendix C as one object: the largest rank over the
   batches of no-kink inputs is not a Lean definition (it is `fdNoKink` in my scratch file). The
   paper's value is reached through the pairs of statements, for one block only.
2. Appendix C: the no-kink inputs "form an open set of full measure". Not stated.
3. Appendix C: "every batch of no-kink inputs has rank at most `P − dim K(θ)`" for the paper's
   `K(θ)` (the upper half of "`fd = P − dim K(θ)`" for the set `N(θ)`): no public statement for a
   set `U` of inputs (private `flat_le_ker'` is the form for all inputs).
4. "No hidden unit at its kink" for networks of two or more blocks: no definition, and no
   statement that the network is differentiable in `θ` at such inputs.
5. Lemma B.1 as a statement on the group ("no continuous family of them, other than the identity,
   fixes `θ`"), and attention blocks.
6. Theorem 4.3: attention blocks (`s = 2Hd_h²`); the sentence after it for `ε = 0` with
   `𝒢 = CO(d)`; a statement "at generic parameters" of the bound from the changes of basis alone
   for arbitrary maps `f_ℓ` (a one-line corollary, scratch F1).
7. Theorem 5.1 / C.1: an attention block. "So the network satisfies the equality condition"
   (Definition 4.4 is not in Lean).
8. Appendix B: the changes of basis inside an attention head.

Skips paper.
9. Theorem 4.2: attention blocks; Theorem A.17 (i) and (iii); Lemma A.18 as a statement on the
   group, and its second statement ("the same holds if the readout has rank `d_model` …").
10. Theorem 4.6 (i) / B.1 (i): an attention block; the clause with biases; "both networks satisfy
    the equality condition" as such. Theorem 4.6 (ii) and B.1 (ii) to (v) for ReLU, ReLU², ReGLU.

Absorb paper.
11. Theorem 4.5: nothing of the statement is missing. Of its proof, not stated on their own: "the
    inputs near which the network is linear of rank `d_model` form an open dense set `Ω`" (inside the
    proof, private), the rate `O(1/t)` along rays, the constant `κ < 0.17`.

### (4b) Rows and notes of `STATEMENTS.md` that are inaccurate or incomplete

`STATEMENTS.md` was edited by its authors several times during the audit. Line numbers are those
of the version of 375 lines (checked last against sha256 `bddfaffc…`); each note is also named by
its first words.

Rows (the table "Dimension paper", lines 147-159; "Skips paper", lines 258-262; "Absorb paper",
lines 319-322). Every Lean name in these rows exists and elaborates, and the numbers in them
(`s = ∑ d_hidden`, `2 ∑ d_hidden`, `d²`, `d(d−1)/2`, `2d² + d_hidden`, `d² + 2d_hidden`, "fewer than
`2d`") are those of the Lean statements. Incomplete in small ways:
1. Line 147 (`flatOn`, …, `exists_jacobianRank_add_finrank_flatOn`): "a batch of inputs of `U` on
   which the Jacobian has the rank `P − dim K_U(θ)`" leaves out the hypothesis that the network is
   differentiable in `θ` at the inputs of `U`. And "`fd(θ) = P − dim K(θ)` … with no hypothesis of
   differentiability" is true for the Lean `K(θ)` (the inputs where the network is differentiable),
   which the row does not say; the note at line 216 does.
2. Lines 151, 154 (Theorem 4.3 for ReLU, ReLU², ReGLU at generic parameters) and line 259
   (Theorem 4.2 with `s`, "at generic parameters (`d_in ≥ d`)"): the statements also need `d ≥ 1`
   (`[Nonempty d]`). The row for Theorem 4.5 (line 319, "`d_in, d_out ≥ d ≥ 1`") says it.
3. Lines 151, 154, 259: the statements are for every positively homogeneous activation or gate
   (the rows say so) and bound the Lean `funDim`; "every real `ε`" should not be read as "the
   paper's case `ε = 0` is covered" (2.12): for `ε = 0` the paper's group and bound are different.
4. Lines 158, 159 and the row "S Theorem 4.6 (i) for a ReGLU block" are marked *proved*. This is
   right for the sources and for the library as rebuilt at 05:26 UTC (three standard axioms for the
   13 names). At my first check, some minutes earlier, the compiled library still had `sorryAx`
   for them.
5. Line 320 (Theorem 4.5 for ReLU) is accurate. It could add that the residual network may have
   any widths and no block, and that one null set serves all skipless networks.

Notes that are out of date after the new files:
6. "Lemma B.1: …" (line 183): "ReLU, ReLU², the gate of ReGLU and attention are not covered." Now
   only attention is not covered (rows at lines 150 and 153).
7. "Theorem 4.3 is stated under the conditions that its proof uses (… the maps `f_ℓ` are
   differentiable) … Not stated yet: the blocks with `s > 0` other than SwiGLU and GeGLU (ReLU,
   ReLU², ReGLU, attention)" (line 210). Now the primed statements need no differentiability, and
   only attention is not stated (rows at lines 148, 151, 154).
8. "The Jacobian needs a norm …" (line 225): "so the statements on the functional dimension assume
   that `θ ↦ F_θ(x)` is differentiable at `θ`." This contradicts the note before it (line 216) for
   the primed statements and for all statements on ReLU, ReLU² and ReGLU blocks.
9. "Not stated yet from the main text: …" (line 235): "Theorem 4.3 for ReLU, ReGLU and attention
   blocks, with the term `s` for ReLU², and its remark for `ε = 0`; Theorem 5.1 for ReLU, ReLU², ReGLU
   and attention blocks". Now: Theorem 4.3 for attention blocks and its remark for `ε = 0`;
   Theorem 5.1 for an attention block.
10. "Not stated yet from the main text of the skips paper: …" (line 268): "Theorem 4.6 (i) for ReGLU
    and attention blocks and with biases". ReGLU is now stated and proved (the row at line 262);
    what remains is an attention block and the clause with biases.
11. "ReLU blocks and the functional dimension" (line 216) is accurate. Two things it could add:
    that "a set that contains the paper's" is a Lean statement for one block only, and that at
    some weights (a set of measure zero) the Lean value is larger than the paper's (2.1, point 4).
    "For each kind of block two statements are made" holds for the one-block equalities; the upper
    bounds are single statements, which is enough for them.
12. Line 46: "The branch `main` holds only what is proved; statements in work are on the branch
    `lean-wip`." The library that I was given is on the branch `lean-plus`, and it held a file with
    `sorry` during the audit. I did not look at the other branches.
13. Lines 13-20 (who compared what): after this audit, the files `Absorb/FirstBlock.lean`,
    `Residual/UpperBoundSymmetries.lean`, `OneBlock/ResidualRescale.lean`, `OneBlock/ReGLU.lean`,
    `Dimension/RescalingMlp.lean`, `Dimension/RescalingGate.lean`, `OneBlock/Rescale.lean`, the last
    section of `Dimension/Functional.lean` and the statements marked with a prime have been
    compared. The five files named there as written after this audit began were not.

---------------------------------------------------------------------------------------------------

## (5) What the authors should know, most serious first

### Anything false, vacuous or changed in meaning

1. **No Lean statement in scope is false or vacuous.** All 94 names elaborate; in the rebuilt
   library all 94 depend on `propext`, `Classical.choice`, `Quot.sound` only. The hypotheses can be
   met (the generic conditions hold for almost every `θ`, and a Haar measure exists).

2. **One definition changes the object for networks with a kink: the Lean `funDim` is not the
   paper's functional dimension by definition.** The paper takes the Jacobian at the inputs at
   which no hidden unit sits at its kink. The Lean `funDim` (unchanged: `fderiv` is `0` where a map
   is not differentiable) is the largest rank over the batches of inputs at which the network is
   differentiable in `θ`. That set contains the no-kink inputs and is larger at every `θ` (it
   contains the input `0`; for ReLU² it is all inputs; for ReGLU it contains inputs where a gate
   and its value vanish together). What follows, exactly:
   - `funDim ≥` the paper's value at every `θ`. A batch with a kink input can never lower the Lean
     value; it can raise it.
   - At generic parameters, for one block, the two are equal, and this is a theorem: the pair
     "value of `funDim`" and "a batch of no-kink inputs with that rank" gives the paper's statement
     (machine-checked for ReLU in `TestA.lean`; the same two-line argument serves the other five
     pairs). Each statement of a pair alone is not the paper's statement.
   - At some non-generic weights the Lean value is strictly larger than the paper's, read
     literally: when a hidden unit sits at its kink at every input (a zero read column), the paper
     has no input left, and Lean still counts the inputs at which the network is differentiable.
     Machine-checked for a ReLU² block (`TestB.lean`: `noKink θ₀ = ∅` and `0 < funDim θ₀`). This
     has no effect on a statement "at generic parameters".
   - For networks of two or more blocks, Lean has no notion of a no-kink input and no statement
     that compares the two values. The statements in scope for such networks are upper bounds on
     `funDim`, and an upper bound on the larger quantity gives the paper's bound. A future
     **equality** for ReLU-type blocks at depth would again need the second statement of a pair,
     and for that a definition of the no-kink inputs of a deep network.
   - The sentence of the first audit, that Lean "drops every batch that contains one such input,
     which gives the same maximum", is not right as it stands (2.1).

3. **"Every real `ε`" does not include the paper's case `ε = 0`.** The statements under
   pre-RMSNorm in `RescalingMlp.lean`, `RescalingGate.lean`, `UpperBoundSymmetries.lean` and the
   primed ones hold for all real `ε`, with the group `O(d)`. For `ε = 0` they are true statements
   about the Lean function `rmsNorm 0` (defined at zero rows too), with a bound that is weaker
   than the paper's for `ε = 0` (group `CO(d)`, one more dimension per copy; for positively
   homogeneous blocks without skips more still, S Theorem B.1 (iv)). Nothing is wrong; the words
   "every real `ε`" in `STATEMENTS.md` should not be read as coverage of the case (0).

### Differences of form

4. The one-block equalities for ReLU, ReLU² and ReGLU are pairs of statements (point 2). The
   third statement of each residual family, `fd(residual) = fd(skipless) + d²`, is about the Lean
   `funDim` of the two networks; by the pairs it holds for the paper's values as well.
5. Lemma B.1 is stated in infinitesimal form (the directions determine `X`, `α`, `β`), as in the
   earlier audits; now also for ReLU, ReLU² and ReGLU.
6. Theorem 4.3 and Theorem 4.2 are stated twice: under the explicit conditions of the proof, and
   for almost every `θ`. All bounds are additions in `ℕ`.
7. The stream matrices of `eval` are fixed. "With learned skips" in a docstring means "for every
   fixed linear skip": no `funDim` of the library is the functional dimension of a network whose
   skips are parameters. Theorem 4.2 of the skips paper makes no claim on learned skips, so nothing
   of that theorem is lost.
8. `noKinkGate` asks only that the gates are nonzero; the value of a unit may vanish. This is the
   paper's notion.
9. Theorem 4.5 of the absorb paper: the skipless network (depth, model dimension, widths, weights)
   is quantified inside "for almost every `θ`", so one null set serves all skipless networks, as in
   the paper. Its model dimension is in `Type` there, in any universe in the pointwise statements.

### Hypotheses that Lean shows unnecessary

10. D Theorem 4.3 for ReLU, ReLU², ReGLU: `d_out ≥ d` and `d ≥ 2` are not used (`d ≥ 1` is); no
    differentiability of the blocks; any positively homogeneous activation (resp. gate) of any
    degree `k`.
11. S Theorem 4.2 with identity skips: **no condition on the widths of the blocks**, on `d_out` or
    `d ≥ 2`: only `d_in ≥ d ≥ 1`. The paper's Lemma A.18 assumes width at least `d_model` for the
    residual network too.
12. A Theorem 4.5: `d ≥ 2`, the minimal widths `≥ d` of both networks, and `L ≥ 1` for the residual
    network are not used; `ED ≠ 0` follows from the ranks.
13. D Section 4 and Appendix C: "a direction of a symmetry is flat" and "`fd = P − dim K(θ)`" hold
    with no hypothesis of differentiability, for the Lean objects.
14. Hypotheses that are needed, for the record: `d ≥ 2` for the conditions of the ReGLU block
    (`OneBlockGenericReGLU` fails at every `θ` for `d = 1`, scratch C3), as in the paper; `d ≥ 1`
    for the bounds with `s`; at least one token for the equalities.

### What was checked by machine, and what was not

15. By machine (Lean, in `/home/claude/audit4/`, each compiled with
    `lake env lean` against the built library; none uses `sorry`):
    - `Check1.lean`: `#check @` on the 94 names (output identical before and after the rebuild).
    - `Axioms.lean`: `#print axioms` on the 94 names. First run: 81 names with the three standard
      axioms, 13 names of `OneBlock/ReGLU.lean` with `sorryAx` in addition (expected by the brief:
      `ae_oneBlockGenericReGLU`, `differentiableAt_eval_of_mem_noKinkGate`,
      `flatOn_noKinkGate_le_reglu`, `funDim_reglu_oneBlock`, `exists_jacobianRank_reglu_oneBlock`,
      `ae_funDim_reglu_oneBlock`, `ae_exists_jacobianRank_reglu_oneBlock`,
      `flatOn_noKinkGate_le_reglu_residual`, `funDim_reglu_oneBlock_residual`,
      `exists_jacobianRank_reglu_oneBlock_residual`, `ae_funDim_reglu_oneBlock_residual`,
      `ae_exists_jacobianRank_reglu_oneBlock_residual`, `ae_funDim_reglu_oneBlock_residual_eq_add`;
      output kept as `Axioms_first.out`). Second run, after the authors' rebuild at 05:26 UTC: all
      94 names with exactly the three standard axioms (`Axioms.out`). In between I compiled a
      scratch copy of the new `OneBlock/ReGLU.lean` (`ReGLUCopy.lean`, sha256 of the source
      `19a08c19…`) with the same result for the 13 names.
    - `TestA.lean`: on a batch of no-kink inputs the outputs are differentiable in `θ`; the
      supremum over no-kink batches is at most `funDim` at every `θ`; the pair of theorems for ReLU
      gives the paper's value for almost every `θ`; the second statement with the upper bound
      gives it too; the theorem at concrete sizes; a Haar measure exists.
    - `TestB.lean`: a ReLU² weight with `noKink = ∅`, rank `0` on every no-kink batch, and
      `funDim > 0`; a general lemma (`funDim > 0` when the output at some input is differentiable in
      `θ` and not zero).
    - `TestC.lean`: Theorem 4.3 for ReLU at concrete sizes with `d_out < d`; the homogeneity
      hypothesis for the identity and the step function; `OneBlockGenericReGLU` fails for `d = 1`;
      its extra clause gives the hypothesis of Lemma C.3 with zero biases; the third ReGLU
      statement is the difference of the other two; Theorem 4.2 with identity skips for ReLU and
      for ReGLU under `rmsNorm 1` with no hypothesis on the widths.
    - `TestD.lean`: Theorem 4.5 gives the one-block case and the weaker order of quantifiers; the
      pointwise statement with `d' : Type 3`; the residual network with no block;
      `FirstBlockGeneric` gives `ED ≠ 0`; `withActivation` keeps the weights.
    - `TestE.lean`: the input `0` is not in `noKink θ` and the network is differentiable in `θ`
      there.
    - `TestF.lean`: the two primed bounds "at generic parameters" for arbitrary `f_ℓ` follow from
      public statements.
16. By numerical computation, not by Lean: the ranks of the ReGLU block with and without the skip
    (`reglu_rank_check.py`, `reglu_rank_check4.py`), done while the proofs were still `sorry`.
17. By reading only, not by machine: every comparison of a Lean statement with the paper's
    sentence; that `OneBlockGenericReGLU`, `FirstBlockGeneric`, `noKink`, `noKinkGate`,
    `rescaleDirMlp`, `rescaleDirGate` are the paper's objects; the claims of 2.1, point 4, about
    ReGLU and ReLU inputs at a kink at which the network is differentiable in `θ` (ReLU²: by
    machine); that the Lean `funDim` equals the paper's value at generic parameters for two or
    more blocks was **not proved** and is not stated anywhere.
18. Not done: `lake build` (forbidden by the brief), so "the whole library compiles" rests on the
    authors' build; I compiled only scratch files against it. The private lemmas and the proofs
    were not judged. The five files written after this audit began (`Absorb/RMSNormRays.lean`,
    `Absorb/RMSNormGeneric.lean`, `Dimension/GenericRank.lean`, `Activations/Analytic.lean`,
    `Depth/SuffixGated.lean`) were not read.

---------------------------------------------------------------------------------------------------

## (6) Count

Paper statements and definitions compared: **22** (the rows of the table in (1)): 14 of the
dimension paper (Definition 4.1 with the convention of Appendix C; "Notation and flat directions";
the sentence of Section 4 on symmetries; Theorem 4.3 in three groups of blocks; three kinds of
rescaling of the list of Appendix B; Lemma B.1; Lemma C.3 for ReLU and ReLU²; Theorem 5.1 / C.1 for
three kinds of block, the last with the generic conditions of Appendix C), 4 of the skips paper
(Theorem 4.2 with identity skips, without and with `s`; Theorem 4.6 (i) / B.1 (i) for ReLU and
ReLU², and for ReGLU), 4 of the absorb paper (the conditions of the proof of Theorem 4.5; Theorem
4.5 for ReLU; for GELU; the limit along rays).

Against **94 Lean names**: 9 definitions (`flatOn`, `rescaleDirMlp`, `rescaleDirGate`,
`UnitsRescale`, `noKink`, `OneBlockGenericReGLU`, `noKinkGate`, `Params.withActivation`,
`FirstBlockGeneric`) and 85 theorems, in 11 files: `Dimension/Functional.lean` 6,
`Dimension/UpperBound.lean` 2, `Dimension/UpperBoundRMSNorm.lean` 2, `Dimension/Rescaling.lean` 1,
`Dimension/RescalingMlp.lean` 13, `Dimension/RescalingGate.lean` 9, `OneBlock/Rescale.lean` 12,
`OneBlock/ReGLU.lean` 15, `Residual/UpperBoundSymmetries.lean` 16, `OneBlock/ResidualRescale.lean`
10, `Absorb/FirstBlock.lean` 8.

Verdicts over the 22 rows: SAME 9 (rows 2, 11, 12, 13, 14, 17, 18, 19, 22; rows 17 and 18 are
SAME for Theorem 4.6 (i) and PART of Theorem B.1 (i), and row 22 is SAME for the limit, with the
rate not stated); LEAN STRONGER 9 (rows 3, 5, 6, 7, 9, 10, 16 for its clause, 20, 21); PART 2
(rows 4 and 15, each also stronger than the unprimed form); DIFFERENT 2 (row 1 by a definition,
row 8 in form). No row is LEAN WEAKER, and no statement is false.

Scratch files: 8 Lean files (`Check1`, `Axioms`, `TestA` to `TestF`) and the copy `ReGLUCopy`; 4
Python files for the numerical check.
