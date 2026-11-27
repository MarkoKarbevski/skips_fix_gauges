STATUS: complete

# Thirty-second audit, part B, of Lean statements against the papers (25 November 2026)

Subject: S Theorem B.1 (i) with biases for one SwiGLU, GeGLU, ReLU, ReLU² or ReGLU block, and the two values for one tanh and one GELU block by name. Files (all under `/home/claude/lp/lean/SkipsLean/`): `OneBlock/GatedBiases.lean`, `OneBlock/GatedBiasesNamed.lean`, `OneBlock/MlpBiasesNamed.lean`, `Dimension/FunctionalBiasesOn.lean`, `OneBlock/RescaleBiases.lean`, `OneBlock/ReGLUBiases.lean`.

Commit of `/home/claude/lp` (branch `lean-plus`) read at the start: `49f38c2`. (A stub left by a stopped first reader named `aa7237b`; this report is a fresh reading and uses nothing of it.)

Paper: `<scratchpad>/skips.txt`. Scratch work: `/home/claude/audit32b_2/`.

Commit at the end: `e0c9eaf`. The checks were done in the order 5, 1, 6, 3, 4, 2 and are given here in the order of the brief. During the work `HEAD` moved to `cb6eee1`; between `49f38c2` and `cb6eee1` none of the six files, nor `checks/Axioms.lean`, changed; `STATEMENTS.md` changed in two lines of its list of files not yet compared (the start time of this audit), not in the rows of the six files. At the end `HEAD` was `e0c9eaf`; between `cb6eee1` and `e0c9eaf` again none of the six files and not `checks/Axioms.lean` changed; `STATEMENTS.md` gained rows for the attention block with biases and one changed sentence in row 1003 (check 6).

No file of the subject has `sorry` (all 53 theorems depend on `propext`, `Classical.choice`, `Quot.sound` only, check 6).

How each check was done: check 1 by reading, by compiling a copy and by a computation; check 2 by reading and by a computation; check 3 by reading and by a computation; check 4 by reading; check 5 by reading (and the named statements compiled at a concrete Haar measure in check 1); check 6 by reading and by compiling a copy. The scripts and the Lean copies are in `/home/claude/audit32b_2/`.

## Part 1

### Check 1. Generic means almost every pair of weights and biases, for every Haar measure; the conditions on the weights alone (by reading, by compiling a copy, by a computation)

**The form, by reading.** Every `∀ᵐ` statement of the six files (`grep '∀ᵐ'`: 4 in `MlpBiasesNamed.lean`, 4 in `GatedBiasesNamed.lean`, 5 in `GatedBiases.lean`, 15 in `RescaleBiases.lean`, 5 in `ReGLUBiases.lean`; none in `FunctionalBiasesOn.lean`) has

```lean
(μ : Measure (ParamsB (Arch.… σ id hid) dIn dOut)) [μ.IsAddHaarMeasure] … : ∀ᵐ p ∂μ, …
```

with `ParamsB A dIn dOut = Params A dIn dOut × Biases A dOut`: every Haar measure on the pairs `(θ, b)`. Each is proved as `(ae_paramsB_of_forall_ae (fun ν _ => ae_oneBlockGeneric… ν hd hdIn hdOut hhid) μ).mono …` (or `filter_upwards` of two such), i.e. from a property of the weights `p.1` that holds at almost every `θ` for every Haar measure `ν` on the weights; `ae_paramsB_of_forall_ae` was found true by the thirty-first audit (check 2). `T`, `d`, `dIn`, `dOut` have `Fintype` in the `variable` line of every file, `hid` has `[∀ ℓ, Fintype (hid ℓ)]`, and `A.r ℓ`, `A.w ℓ` (for the gated block `hid 0 ⊕ hid 0` and `hid 0`) are finite as fields of `Arch`: every index type of the weights and of the biases is finite.

**By compiling a copy** (`/home/claude/audit32b_2/Check1.lean`, no error, 27 s): the named statements at the concrete measure `Measure.addHaar` on `ParamsB A (Fin 2) (Fin 2)`, `T = d = Fin 2`, three hidden units, and from them with `finrank_paramsB`, `finrank_params_mlp`, `finrank_params_gated` the numbers: ReLU and ReLU², `P = 29`, `funDimB … 0 p = 14`, `funDimB … 1 p = 18` at almost every `p`, and a batch in `noKinkB p` of rank `14`; ReGLU, `P = 38`, `20` and `24`, and a batch in `noKinkGateB p` of rank `24` with the skip; SwiGLU, `P = 38`, `23` and `27`; GeGLU `23` and the gain `+4`; tanh, `P = 29`, `17`. A copy with `15` in place of `14` for ReLU fails (`Check1neg.lean`), as it should. (With two hidden units and `T = d = Fin 2` the instance search for `BorelSpace (ParamsB …)` timed out even at 400000 heartbeats; with three hidden units it is found at once. This concerns the elaboration of my copy only.)

**Are the conditions on the weights alone right for each kind of block?** The paper's Reduction: "For generic parameters `E`, `D`, `W_read` and `W_write` have rank `d_model`, every `a_i` is nonzero, and the `c_i` are nonzero and pairwise non-collinear […]. For the gated blocks ReGLU, SwiGLU and GeGLU, in the same way, the value weights `(e_i, β_i′)` of each unit, introduced below, have `e_i ≠ 0` and are not proportional to its gate weights `(c_i, β_i)`." Lemma B.3 asks exactly these ("let also every `e_i ≠ 0`, with `(e_i, β_i′)` not proportional to `(c_i, β_i)`").

- ReLU, ReLU² (`OneBlockGeneric p.1`: four ranks, rows of `W_write D` nonzero, columns of `E W_read` nonzero and pairwise non-collinear): the paper's list. No condition on the biases is needed: the proof for ReLU and ReLU² uses the hyperplanes `H_i = {x c_i + β_i = 0}`, which are hyperplanes for every `β_i` since `c_i ≠ 0`, pairwise non-parallel since the `c_i` are non-collinear; `UnitsRescale` (`OneBlock/Rescale.lean`) has `β` as a free argument and no hypothesis on it. Step 3's "no column of `W_read` vanishes" follows from `c_i ≠ 0`. Right.
- SwiGLU, GeGLU (`OneBlockGenericGated p.1`: four ranks, rows of `A` nonzero, gate columns nonzero and pairwise non-collinear, value columns `e_i ≠ 0`): the paper's list without "not proportional to `(c_i, β_i)`". `GatedUnitsRescale` (`OneBlock/Gated.lean`) has no such hypothesis, and its docstring says "the proofs for SwiGLU and GeGLU do not use it". By reading the paper's proof for SwiGLU and GeGLU ("SwiGLU and GeGLU. Take a ray …"): it uses `e_j ≠ 0` ("as `e_j ≠ 0`, also `v_j ≠ 0` on an open set of such `n`") and never the non-proportionality. So the library's remark is right, and the Lean statements need less than the paper. **By a computation** (`special_check.py`): SwiGLU with the value column of `W_read` twice the gate column and the value bias chosen so that `(e_i, β_i′) = 2 (c_i, β_i)` for every unit, `d = 2`, sizes `(d_in, d_out, d_hidden) = (2,2,2)` and `(3,2,3)`, two batches each: ranks `16`, `20` (of `P = 30`) and `25`, `29` (of `P = 40`), the formulas; smallest pivot kept `3e-5` of the first, largest dropped `3e-41`. So at these parameters (which satisfy `OneBlockGenericGated` and violate the paper's condition) the Lean values hold, as the Lean statements at one parameter say.
- ReGLU (`OneBlockGenericReGLU p.1`: `OneBlockGenericGated` and `value_not_gate : ∀ i r, (E W_read)ᵀ (inr i) ≠ r • (E W_read)ᵀ (inl i)`): if `(e_i, β_i′) = r (c_i, β_i)` then `e_i = r c_i`, which `value_not_gate` excludes; so the condition on the columns alone gives the paper's condition on the pairs, for every bias. It is stronger than the paper's (it also excludes `e_i = r c_i` with `β_i′ ≠ r β_i`), but holds at almost every `θ` (`ae_oneBlockGenericReGLU`), so the generic statements lose nothing. `relu_gated_units_flat` (`OneBlock/UnitsReGLU.lean`) asks `hec : ∀ i r, (e i, β' i) ≠ r • (c i, β i)`, the paper's condition on the pairs. **The condition is needed** (`special_check.py`, exact rational arithmetic): ReGLU with `(e_i, β_i′) = 2 (c_i, β_i)` for every unit gives, on two batches each, ranks `10` and `14` for `(2,2,2)` (formulas `14`, `18`) and `16` and `20` for `(3,2,3)` (formulas `22`, `26`): two more flat directions per unit. So "only for ReGLU" (the library's remark) is right.

Verdict of check 1: generic is **almost every pair of weights and biases, for every Haar measure** (compiled at `Measure.addHaar`); every index type is finite; the conditions on the weights alone are right for each kind of block: the paper's for ReLU and ReLU², less than the paper's for SwiGLU and GeGLU (the non-proportionality is not used, and is not needed, computed), and for ReGLU a condition on the columns that implies the paper's condition on the pairs at every bias (needed, computed).

### Check 2. The values (by reading; by a computation)

**By reading.** Theorem B.1 (i): "For generic parameters the skipless network has functional dimension `P − 2 d_model² − s` and the residual network `P − d_model² − s`; with biases on the embedding, the block and the readout, counted in `P`, both values are `2 d_model` lower"; Step 3: "`s` is the number of rescalings: `d_hidden` for ReLU, ReLU², SwiGLU and GeGLU, `2 d_hidden` for ReGLU, none for tanh and GELU". Lean (check 5): `fd + (2d² + 2d + s) = P` and `fd + (d² + 2d + s) = P` with `P = finrank (ParamsB …)`, which counts `b_E`, `b_read` (one per read column: `d_hidden` for MLP blocks, `2 d_hidden` for gated blocks), `b_write` and `b_D` (`finrank_paramsB`): the embedding, the block and the readout. `s = d_hidden` for ReLU, ReLU², SwiGLU, GeGLU and `2 d_hidden` for ReGLU. The gain: `funDimB … 1 p = funDimB … 0 p + d²`. The hypotheses: `2 ≤ d`, `d ≤ d_in`, `d ≤ d_out`, `d ≤ d_hidden`, `χ = id`, all inputs (for ReLU-type blocks the pair of check 4), one block. The paper's: "`d_model ≥ 2`", "the input and output dimensions be at least `d_model`", "the block have width at least `d_model`", "no normalization", "inputs range over all of `ℝ^{T × d_in}`". SAME, no extra hypothesis (`[Nonempty T]`: at least one token).

**By a computation** (`/home/claude/audit32b_2/rank_check.py` for SwiGLU and GeGLU, `rank_check2.py` for ReLU, ReLU², ReGLU; outputs `ranks.out`, `ranks2.out`). One block with biases as in `Network/Biases.lean` (`h_0 = x E + b_E`, the block `f(h_0 W_read + b_read) W_write + b_write`, `h_1 = S h_0 + block`, `y = h_1 D + b_D`, `S = 0` or `I`), inputs of two tokens. The Jacobian in all weights and biases by forward differentiation along each parameter, with the exact derivative of the activation: for ReLU, ReLU², ReGLU in exact rational arithmetic (random parameters on a grid of step `1/200` in `[−2, 2]`) with `8 P` inputs per batch, inputs with a pre-activation (gate) at exactly `0` discarded, and an exact rank; for SwiGLU (`z/(1 + e^{−z})`) and GeGLU (`z Φ(z)`) at 40 digits with `P` inputs per batch (`4P` to `6P` rows) and a rank by elimination with complete pivoting, threshold `1e-25` of the first pivot. Each parameter with two batches (inputs of scale 3 and of scale 10; for the smooth blocks 3 and 6). Sizes `(d, d_in, d_out, d_hidden)` = `(2,2,2,2)`, `(2,3,2,3)`, `(2,2,3,2)`, `(3,3,3,3)`; skipless and residual; with random biases and with all biases `0` (still counted in `P`). 80 parameters, 160 ranks.

| block | `(2,2,2,2)` skipless / residual | `(2,3,2,3)` | `(2,2,3,2)` | `(3,3,3,3)` |
|---|---|---|---|---|
| ReLU, ReLU² (`P` = 24, 31, 27, 48) | 10 / 14 | 16 / 20 | 13 / 17 | 21 / 30 |
| ReGLU (`P` = 30, 40, 33, 60) | 14 / 18 | 22 / 26 | 17 / 21 | 30 / 39 |
| SwiGLU, GeGLU (`P` = 30, 40, 33, 60) | 16 / 20 | 25 / 29 | 19 / 23 | 33 / 42 |

Every one of the 160 ranks equals the theorem's value (`P − 2d² − 2d − s`, `P − d² − 2d − s`), with random biases and with all biases `0`, on both batches. For the smooth blocks the smallest pivot kept is `3.8e-5` of the first and the largest dropped `4.9e-41`. On the ReLU-type batches every unit was on at 89 or more inputs and off at 106 or more inputs of each batch (the counts are in the output). The computations took about ten minutes in all.

Two remarks on the method, both from runs that I then replaced. (1) In a first run with inputs of scale 1 to 6, a batch for `(2,2,3,2)` with biases had a unit that was on at every input (one bias large against `x c`), and its rank fell short of the value by one or four; the second batch, and the replacement run with inputs of scale 10, gave the value. A rank on a batch is a lower bound; a batch must meet both sides of every kink. (2) In the first run, parameters drawn on a grid of step `1/20` gave, for ReGLU `(2,3,2,3)` with zero biases, the ranks `20` and `24` (two below the values) on both batches: there the value column of `W_read` of one unit was `−(6/37)` times its gate column, a coincidence of the coarse grid, so `OneBlockGenericReGLU` fails at that parameter and the deficit is the one of check 1. With the finer grid, and with two other seeds on the coarse grid, the values hold.

**The gain `d²`** follows in every computed case from the two values (the two columns of the table differ by `d² = 4` or `9`).

**Outside the hypotheses** (`outside.py`, output `outside_all.out`; random biases, two batches each; a rank below the formula is an upper bound only when the free numbers of the function bound it, as noted):

| case | `(d, d_in, d_out, d_hidden)` | ReLU: skipless / residual, rank (formula) | ReGLU | SwiGLU |
|---|---|---|---|---|
| `d = 1` | `(1,1,1,2)` | 5 (5) / 6 (6) | 7 (7) / 8 (8) | 9 (9) / 10 (10) |
| `d = 1` | `(1,2,2,3)` | 10 (10) / 11 (11) | 13 (13) / 14 (14) | 16 (16) / 17 (17) |
| `d_hidden < d` | `(2,2,2,1)` | 6 (6) / 10 (10) | 8 (8) / 12 (12) | 9 (9) / 13 (13) |
| `d_hidden < d` | `(3,3,3,2)` | 15 (15) / 24 (24) | 21 (21) / 30 (30) | 23 (23) / 32 (32) |
| `d_hidden < d` | `(3,4,3,2)` | 17 (18) / 27 (27) | 24 (24) / 33 (33) | 26 (26) / 35 (35) |
| `d_hidden < d` | `(2,3,3,1)` | 9 (11) / 15 (15) | 12 (13) / 17 (17) | 13 (14) / 18 (18) |
| `d_in < d` | `(2,1,2,3)` | 11 (12) / 13 (16) | 14 (18) / 16 (22) | 17 (21) / 19 (25) |
| `d_out < d` | `(2,2,1,3)` | 10 (11) / 12 (15) | 16 (17) / 18 (21) | 19 (20) / 21 (24) |

(For `d = 1` the first batch at scale 3 gave lower ranks for ReLU and ReGLU, the batch at scale 10 the formula; the table gives the larger.) So `d_in ≥ d` and `d_out ≥ d` are needed for both values; `d_hidden ≥ d` is needed for the skipless value in some cases (for ReLU `(2,3,3,1)` the skipless function `γ_0 + max(x c + β, 0) a` has `3 + 1 + 3 + 3 = 10` free numbers less one rescaling, so its functional dimension is at most `9 < 11`), but not in others: for `d_in = d_out = d` the skipless count of free numbers of a narrow ReLU block, `d_hidden (d_in + d_out) + d_out`, equals the formula, `(d − d_hidden)(d_in + d_out − 2d)` being `0`. For `d = 1`, which the theorem and Lean exclude, the values hold in the cases computed (as for tanh and GELU in the thirty-first audit). The Lean statements ask all four hypotheses, the paper's.

Verdict of check 2: the two values with biases, the gain `d²` and the hypotheses are **SAME** as the paper's for SwiGLU, GeGLU, ReLU, ReLU² and ReGLU; the computed ranks agree with the values in all 160 cases inside the hypotheses, with the skip and without it, with random and with zero biases.

### Check 3. The flat directions (by reading; by a computation)

```lean
theorem flatB_le_range_gated_skipless (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hU : GatedUnitsRescale σ σ' dIn dOut (hid 0)) (p : ParamsB (Arch.gated σ id hid) dIn dOut)
    (hp : OneBlockGenericGated p.1) (η : ParamsB …) (hη : η ∈ flatB (Arch.gated σ id hid) 0 p) :
    ∃ (X : Fin 2 → Matrix d d ℝ) (g : Fin 2 → d → ℝ) (α : ∀ ℓ, hid ℓ → ℝ),
      η = cobDirB p X + (0, translateAtDir p.1 g) + rescaleDirB p α
theorem flatB_le_range_gated_residual … (hη : η ∈ flatB (Arch.gated σ id hid) 1 p) :
    ∃ (X : Matrix d d ℝ) (g : Fin 2 → d → ℝ) (α : ∀ ℓ, hid ℓ → ℝ),
      η = cobDirB p (fun _ => X) + (0, translateDir p.1 g) + rescaleDirB p α
theorem flatOnB_noKinkB_le_mlp_rescale {k : ℕ} (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (hU : UnitsRescale σ σ' k dIn dOut (hid 0)) (p : …) (hp : OneBlockGeneric p.1) (η : …)
    (hη : η ∈ flatOnB (Arch.mlp σ id hid) 0 p (noKinkB p)) :
    ∃ (X : Fin 2 → Matrix d d ℝ) (g : Fin 2 → d → ℝ) (α : ∀ ℓ, hid ℓ → ℝ),
      η = cobDirB p X + (0, translateAtDir p.1 g) + rescaleDirMlpB k p α
-- `…_residual`: `cobDirB p (fun _ => X) + (0, translateDir p.1 g) + rescaleDirMlpB k p α`
theorem flatOnB_noKinkGateB_le_reglu (p : ParamsB (Arch.gated relu id hid) dIn dOut)
    (hp : OneBlockGenericReGLU p.1) (η : …)
    (hη : η ∈ flatOnB (Arch.gated relu id hid) 0 p (noKinkGateB p)) :
    ∃ (X : Fin 2 → Matrix d d ℝ) (g : Fin 2 → d → ℝ) (α β : ∀ ℓ, hid ℓ → ℝ),
      η = cobDirB p X + (0, translateAtDir p.1 g) + rescaleDirB p α + rescaleDirGateB 1 p β
-- `…_residual`: `cobDirB p (fun _ => X) + (0, translateDir p.1 g) + rescaleDirB p α + rescaleDirGateB 1 p β`
```

**Which entries move, by which factor, by reading** (`Symmetry/BiasesFlat.lean`, `Symmetry/BiasesRescaleCount.lean`, `Dimension/UpperBound.lean`, `Dimension/RescalingMlp.lean`, `Dimension/Rescaling.lean`, `Dimension/RescalingGate.lean`):

| direction | weights | biases |
|---|---|---|
| `cobDirB p X` | `η_E = E X_0`, `η_read = −X_0 W_read`, `η_write = W_write X_1`, `η_D = −X_1 D` | `η_{b_E} = b_E X_0`, `η_{b_write} = b_write X_1`, `η_{b_read} = 0`, `η_{b_D} = 0` |
| `translateAtDir θ g` (skipless) | 0 | `η_{b_E} = g_0`, `η_{b_read} = −g_0 W_read`, `η_{b_write} = g_1`, `η_{b_D} = −g_1 D` |
| `translateDir θ g` (residual, `L = 1`) | 0 | `η_{b_E} = g_0`, `η_{b_read} = −g_0 W_read`, `η_{b_write} = g_1`, `η_{b_D} = −(g_0 + g_1) D` |
| `rescaleDirMlpB k p α` | read column `i` `× α_i`, write row `i` `× (−k α_i)` | read bias `i` `× α_i` |
| `rescaleDirB p α` (values) | value column `i` `× (−α_i)`, write row `i` `× α_i` | value bias `i` `× (−α_i)` |
| `rescaleDirGateB 1 p β` (gates) | gate column `i` `× β_i`, write row `i` `× (−β_i)` | gate bias `i` `× β_i` |

Against Lemma B.2 with biases: "`η_E = EX`, `η_read = −X W_read`, `η_write = W_write Y`, `η_D = −Y D` […] `η_{b_E} = b_E X + g_0`, `η_{b_read} = −g_0 W_read`, `η_{b_write} = b_write Y + g_1` and `η_{b_D} = −g_1 D`, respectively `η_{b_D} = −(g_0 + g_1) D`", with `X = Y` in the residual network: the sum `cobDirB p X + (0, translateAtDir θ g)` is this with `X = X_0`, `Y = X_1`, and the residual form with `X_0 = X_1`. Same. Against Step 3, "it scales column `i` of `W_read` and entry `i` of `b_read` by `λ_i` and row `i` of `W_write` by `−λ_i` for ReLU, by `−2 λ_i` for ReLU², and similarly for ReGLU and for the values of SwiGLU and GeGLU": `rescaleDirMlpB 1` and `rescaleDirMlpB 2` are this (the named statements use `k = 1` for ReLU and `k = 2` for ReLU², check 5). In the reduced variables, `rescaleDirMlpB k` gives `ψ_{c_i} = λ_i c_i`, `ψ_{β_i} = b_E (λ_i W_read e_i) + λ_i b_{read,i} = λ_i β_i`, `ψ_{a_i} = −k λ_i a_i`: Lemma B.3 for ReLU and ReLU². `rescaleDirB` gives `(ψ_{e_i}, ψ_{β_i′}) = −α_i (e_i, β_i′)`, `ψ_{a_i} = α_i a_i`: Lemma B.3 for SwiGLU and GeGLU. For ReGLU the sum `rescaleDirB p α + rescaleDirGateB 1 p β` gives `(ψ_{c_i}, ψ_{β_i}) = β_i (c_i, β_i)`, `(ψ_{e_i}, ψ_{β_i′}) = −α_i (e_i, β_i′)`, `ψ_{a_i} = (α_i − β_i) a_i`: Lemma B.3 for ReGLU with `λ_i = β_i`. The embedding bias, the write bias and the readout bias do not move under the rescalings, as in the paper. Right.

**Is this the equality condition for the network with biases?** Step 3: "So every flat direction is the sum of a direction of the changes of basis and translations of Lemma B.2 and a rescaling of the units, and conversely all of these are flat, since they come from symmetries. […] The symmetries account for all of `K(θ)`, which is the equality condition". The six statements give the first half (every flat direction is such a sum), for SwiGLU and GeGLU over all inputs (`flatB`), for ReLU, ReLU² and ReGLU over the inputs off the kinks (`flatOnB … (noKinkB p)`, `flatOnB … (noKinkGateB p)`), which is stronger than over all inputs (`flatB_le_flatOnB`) and is the paper's "every input". The converse ("all of these are flat") is in the bounds of part A (`funDimB_add_le_skipless_mlp_rescale`, `funDimB_add_le_residual_mlp_rescale`, `funDimB_add_le_skipless_gated`, `…_gated_gate`, …), which the proofs of the values use; with the values (`fd = P − (2d² + 2d + s)`, `P − (d² + 2d + s)`) the flat directions are exactly these sums. So both forms of the equality condition (Definition 4.3: the bound attained at generic parameters; Step 3: the symmetries account for all of `K(θ)`) follow from the statements, as for tanh and GELU in the thirty-first audit. No statement uses the words "equality condition" for networks with biases (no definition in the library).

**By a computation** (`/home/claude/audit32b_2/directions_check.py`; `d = 2`, `d_in = 3`, `d_out = 2`, three hidden units, random biases, inputs of two tokens; the directions built entry by entry from the definitions above; exact rational arithmetic for ReLU, ReLU², ReGLU with `8 P` inputs off the kinks, 40 digits for SwiGLU):

| block | network | `P` | directions | their span | `P − rank J` | `max |J η|` over the directions | controls (`max |J η|`) |
|---|---|---|---|---|---|---|---|
| ReLU | skipless | 31 | 15 | 15 | 15 | 0 (exact) | write factor `−2` in place of `−1`: `45.1`; read bias not scaled: `0.96` |
| ReLU | residual | 31 | 11 | 11 | 11 | 0 | the same |
| ReLU² | skipless | 31 | 15 | 15 | 15 | 0 | write factor `−3` in place of `−2`: `1.3e3`; read bias not scaled: `54.1` |
| ReLU² | residual | 31 | 11 | 11 | 11 | 0 | the same |
| ReGLU | skipless | 40 | 18 | 18 | 18 | 0 | value bias not scaled: `80.7` |
| ReGLU | residual | 40 | 14 | 14 | 14 | 0 | the same |
| SwiGLU | skipless | 40 | 15 | 15 | 15 | `1.9e-37` | value bias not scaled: `32.0`; a gate rescaling (SiLU is not homogeneous): `8.5` |
| SwiGLU | residual | 40 | 11 | 11 | 11 | `2.6e-37` | the same |

So the directions of the statements are flat, independent, and fill the kernel of the Jacobian (its dimension `P − rank J` equals the dimension of their span): the kernel is exactly their span at these parameters.

Verdict of check 3: **SAME** as Step 3 and Lemmas B.2 and B.3 with biases (the three rescaling directions move the right entries by the right factors, for ReGLU the sum of a value and a gate rescaling); for ReLU, ReLU² and ReGLU the statements are over the paper's inputs off the kinks (LEAN STRONGER than over all inputs, and the paper's sense). With the values and the bounds of part A they give the equality condition for the network with biases in both of its forms.

### Check 4. ReLU-type blocks: which inputs (by reading)

```lean
def noKinkB (p : ParamsB (Arch.mlp σ id hid) dIn dOut) : Set (Matrix T dIn ℝ) :=
  {x | ∀ (t : T) (i : hid 0),
    (x * p.1.E * p.1.read 0) t i + (p.2.E ᵥ* p.1.read 0 + p.2.read 0) i ≠ 0}
def noKinkGateB (p : ParamsB (Arch.gated σ id hid) dIn dOut) : Set (Matrix T dIn ℝ) :=
  {x | ∀ (t : T) (i : hid 0),
    (x * p.1.E * p.1.read 0) t (Sum.inl i) + (p.2.E ᵥ* p.1.read 0 + p.2.read 0) (Sum.inl i) ≠ 0}
```

**The sets.** In `Network/Biases.lean`, `h_0 = x E + b_E` (the row added to every token) and the block reads `χ(h_0) W_read + b_read` with `χ = id`; so the pre-activation of unit `i` at token `t` is `(x E W_read)_{t,i} + (b_E W_read + b_read)_i`, which is what `noKinkB` asks to be nonzero for every `t` and `i`. This is the paper's "the inputs `x` at which no hidden unit sits at its kink" with the paper's `z_i = x c_i + β_i`, `β = b_E W_read + b_read` (Reduction). For ReGLU the unit computes `max(z_i, 0) w_i a_i` with the gate `z_i` and the value `w_i` affine in the parameters; only `max(·, 0)` has a kink, at `z_i = 0`, so the kink of a ReGLU unit is the zero set of its gate, and `noKinkGateB` (gate columns `Sum.inl i` only) is right. SAME.

**Differentiability.** `differentiableAt_evalB_of_mem_noKinkB (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z) p S x hx` and `differentiableAt_evalB_of_mem_noKinkGateB S p x hx` take an arbitrary stream matrix `S : Fin 1 → Matrix d d ℝ`. True as stated: the output is `(x E + b_E) S_0 D + f(u) W_write D + b_write D + b_D` with every entry of `u` a polynomial in `(θ, b)` that is nonzero at `p`, and `σ` (ReLU for the second) is differentiable at nonzero arguments; the rest is polynomial. (The proofs are not the subject; they compile with the standard axioms, check 6.)

**`flatOnB` and `exists_jacobianRankB_add_finrank_flatOnB`** (`FunctionalBiasesOn.lean`):

```lean
noncomputable def flatOnB (A : Arch T d L) (S : Fin L → Matrix d d ℝ) (p : ParamsB A dIn dOut)
    (U : Set (Matrix T dIn ℝ)) : Submodule ℝ (ParamsB A dIn dOut) :=
  ⨅ x ∈ U, LinearMap.ker (fderiv ℝ (fun q : ParamsB A dIn dOut => evalB A S q.1 q.2 x) p).toLinearMap
theorem flatB_le_flatOnB (U : Set (Matrix T dIn ℝ)) : flatB A S p ≤ flatOnB A S p U
theorem exists_jacobianRankB_add_finrank_flatOnB (U : Set (Matrix T dIn ℝ))
    (hU : ∀ x ∈ U, DifferentiableAt ℝ (fun q : ParamsB A dIn dOut => evalB A S q.1 q.2 x) p) :
    ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i, X i ∈ U) ∧
      jacobianRankB A S X p + Module.finrank ℝ (flatOnB A S p U) = Module.finrank ℝ (ParamsB A dIn dOut)
```

`flatOnB` is the paper's `K(θ)` with "every input" read as "every input of `U`" ("Call `η` flat if `D_θ F(θ, x) η = 0` for every input `x`" and "“every input” means every such input"), with the biases among the parameters; the twin of `flatOn`, word for word with `ParamsB` and `evalB`. `flatB_le_flatOnB` is true (an infimum over more inputs is smaller). `exists_jacobianRankB_add_finrank_flatOnB` is the paper's "some finite batch has kernel exactly `K(θ)`. By rank–nullity, the functional dimension at `θ` is therefore `P − dim K(θ)`" on `U`; true as stated. **The hypothesis `hU` is not needed for the truth of the statement**, by an argument of the reader: at an input of `U` where the output is not differentiable, Lean's `fderiv` is `0` and its kernel is everything, so `flatOnB … U = flatOnB … U′` with `U′ ⊆ U` the inputs of `U` where it is differentiable; the theorem for `U′` (where `hU` holds) gives a batch of `U′ ⊆ U`; and if `U′` is empty, the empty batch has rank `0` and `flatOnB` is the whole space. The hypothesis is harmless (it holds for `noKinkB` and `noKinkGateB`, where it is used), and it matches the paper, which only takes inputs where the output is differentiable.

**The pair of statements for each value.** For each kind (ReLU, ReLU², ReGLU) and each network, Lean states (a) `funDimB … + c = P` (all batches of inputs) and (b) a batch of inputs of `noKinkB p` (`noKinkGateB p`) with `jacobianRankB … + c = P`, at one parameter under the conditions on the weights and at generic `(θ, b)`. The paper's functional dimension for these blocks is the largest rank over batches of inputs at which no hidden unit sits at its kink. Every such batch is a batch at which the output is differentiable, so its Lean rank is its true rank, and the paper's value is at most `funDimB`; (a) gives `funDimB = P − c`; (b) gives a batch of the paper's inputs with rank `P − c`. So the paper's value is exactly `P − c` wherever (a) and (b) hold: at every parameter whose weights satisfy `OneBlockGeneric` (`OneBlockGenericReGLU`), whatever the biases, and so at almost every `(θ, b)`. Together the pair is the paper's statement for its functional dimension. SAME (the pair); each statement alone is not.

**Is Lean's `funDimB` larger than the paper's at some parameter?** Yes, as without biases (fourth audit, point 4 of 2.1), at parameters of measure zero, by reading (not machine-checked here): take a ReLU² block in which unit `i` has read column `0` and read bias `0` (then `c_i = 0` and `β_i = b_E W_read e_i + b_{read,i} = 0`, whatever `b_E`). Then `z_i = 0` at every input, so `noKinkB p = ∅` and the paper's value, read literally, is `0`; but ReLU² is differentiable everywhere, the output is differentiable in `(θ, b)` at every input, and the direction of the readout bias has derivative `1` in its coordinate at every input, so `funDimB ≥ 1`. For ReLU the same holds when moreover the write row of that unit is `0`. With biases the input `0` is no longer special (its pre-activations are the `β_i`), which removes one of the fourth audit's kinds of example; the others remain. At generic parameters the pair of statements settles the question: the two values are equal.

Verdict of check 4: `noKinkB` and `noKinkGateB` are the paper's inputs with biases (SAME; gate only for ReGLU, right); the two differentiability statements are true for every stream matrix; `flatOnB` is the paper's `K(θ)` on a set of inputs and the batch statement is true, its hypothesis of differentiability not needed; the pair of statements is the paper's statement for its functional dimension at generic parameters (and at every parameter whose weights satisfy the conditions), while Lean's `funDimB` alone can exceed the paper's value at parameters of measure zero.

### Check 5. The named statements: activation and degree (by reading)

Definitions read: `Network/Blocks.lean`: `Arch.mlp σ χ hid` applies `σ` to every entry; `Arch.gated σ χ hid` has read columns `hid ⊕ hid`, gate `Sum.inl i`, value `Sum.inr i`, and the map `σ(M t (inl i)) * M t (inr i)`, so `σ` is the gate activation. `Activations/ReLU.lean`: `relu z = max z 0`, `reluSq z = (max z 0)^2`. `OneBlock/UnitsSwiGLU.lean`: `silu z = z / (1 + exp(−z))`. `Activations/Gaussian.lean`: `gelu z = z * gaussCdf z` (the exact GELU `z Φ(z)`). `Dimension/RescalingMlp.lean`: `relu_homogeneous : relu (lam * z) = lam ^ 1 * relu z`, `reluSq_homogeneous : reluSq (lam * z) = lam ^ 2 * reluSq z`. `OneBlock/Rescale.lean`: `relu_unitsRescale : UnitsRescale relu reluDeriv 1 …`, `reluSq_unitsRescale : UnitsRescale reluSq reluSqDeriv 2 …` (read the first; the second by its name and use, the degree `k` is fixed by `reluSq_homogeneous` in the same call, so it cannot be another number and still type-check).

| File | Statement | Architecture in the statement | Instance used | Value | Verdict |
|---|---|---|---|---|---|
| `MlpBiasesNamed.lean` | `ae_funDimB_tanh_oneBlock` | `Arch.mlp Real.tanh id hid`, stream `0` | `hasDerivAt_tanh`, `tanh_unitsRigid` | `fd + (2d² + 2d) = P` | SAME |
| | `ae_funDimB_tanh_oneBlock_residual` | same, stream `1` | same | `fd + (d² + 2d) = P` | SAME |
| | `ae_funDimB_gelu_oneBlock` | `Arch.mlp gelu id hid`, `0` | `hasDerivAt_gelu`, `gelu_unitsRigid` | `fd + (2d² + 2d) = P` | SAME |
| | `ae_funDimB_gelu_oneBlock_residual` | same, `1` | same | `fd + (d² + 2d) = P` | SAME |
| `GatedBiasesNamed.lean` | `ae_funDimB_swiglu_oneBlock` | `Arch.gated silu id hid`, `0` | `hasDerivAt_silu`, `silu_gatedUnitsRescale` | `fd + (2d² + 2d + d_hidden) = P` | SAME |
| | `ae_funDimB_swiglu_oneBlock_residual` | same, `1` | same | `fd + (d² + 2d + d_hidden) = P` | SAME |
| | `ae_funDimB_geglu_oneBlock` | `Arch.gated gelu id hid`, `0` | `hasDerivAt_gelu`, `gelu_gatedUnitsRescale` | `fd + (2d² + 2d + d_hidden) = P` | SAME |
| | `ae_funDimB_geglu_oneBlock_residual` | same, `1` | same | `fd + (d² + 2d + d_hidden) = P` | SAME |
| `GatedBiases.lean` | `ae_funDimB_swiglu_oneBlock_residual_eq_add`, `ae_funDimB_geglu_oneBlock_residual_eq_add` | `Arch.gated silu`, `Arch.gated gelu` | as above | `fd(1) = fd(0) + d²` | SAME |
| `RescaleBiases.lean` | `ae_funDimB_relu_oneBlock`, `…_residual`, `ae_exists_jacobianRankB_relu_oneBlock`, `…_residual`, `ae_funDimB_relu_oneBlock_residual_eq_add` | `Arch.mlp relu id hid` | `hasDerivAt_relu` off `0`, `relu_homogeneous` (`k = 1`), `relu_unitsRescale … 1` | `2d² + 2d + d_hidden`, `d² + 2d + d_hidden`, gain `d²` | SAME |
| | `ae_funDimB_reluSq_oneBlock`, `…_residual`, `ae_exists_jacobianRankB_reluSq_oneBlock`, `…_residual`, `ae_funDimB_reluSq_oneBlock_residual_eq_add` | `Arch.mlp reluSq id hid` | `hasDerivAt_reluSq` (everywhere), `reluSq_homogeneous` (`k = 2`), `reluSq_unitsRescale … 2` | same | SAME |
| | the five generic ones `ae_funDimB_mlp_oneBlock_rescale`, `ae_exists_jacobianRankB_mlp_oneBlock_rescale`, `…_residual` (two), `…_residual_eq_add` | `Arch.mlp σ id hid`, any `σ` with `hσ` off `0`, `hhom` of degree `k`, `UnitsRescale σ σ' k` | — | same | SAME (general form) |
| `ReGLUBiases.lean` | `ae_funDimB_reglu_oneBlock`, `ae_exists_jacobianRankB_reglu_oneBlock`, `…_residual` (two), `ae_funDimB_reglu_oneBlock_residual_eq_add` | `Arch.gated relu id hid` | `ae_oneBlockGenericReGLU` and the pointwise theorems of the file (for `relu` only) | `2d² + 2d + 2 d_hidden`, `d² + 2d + 2 d_hidden`, gain `d²` | SAME |

Every named statement has the activation the paper names for it: SwiGLU = `Arch.gated silu`, GeGLU = `Arch.gated gelu`, ReGLU = `Arch.gated relu`, tanh = `Arch.mlp Real.tanh`, GELU = `Arch.mlp gelu`, ReLU = `Arch.mlp relu` with `k = 1`, ReLU² = `Arch.mlp reluSq` with `k = 2`. In each, `χ = id` (no normalization, as in the Scope of Theorem B.1 (i)), `L = 1`, the stream matrix is `0` for the skipless network and `1` for the residual network, every statement is `∀ᵐ p ∂μ` for an arbitrary `μ` with `[μ.IsAddHaarMeasure]` on `ParamsB …` (the pairs of weights and biases), and the hypotheses are exactly `2 ≤ d`, `d ≤ d_in`, `d ≤ d_out`, `d ≤ d_hidden`. The fifteen statements at the end of `RescaleBiases.lean` are the five generic ones plus five for ReLU and five for ReLU²; the five of `ReGLUBiases.lean` are written for `relu` directly (there is no general-gate version for ReGLU). **Verdict: SAME for all.**

### Check 6. The index rows, the registrations, the axioms (by reading; by compiling a copy)

**Registrations and axioms.** All 53 public theorems of the six files are in `checks/Axioms.lean` (lines 2012 to 2017, 2042 to 2077, 2082 to 2093 at `cb6eee1`; the three definitions `flatOnB`, `noKinkB`, `noKinkGateB` are not theorems). A copy with `#print axioms` for the 53 (`/home/claude/audit32b_2/Axioms32b.lean`, output `Axioms32b.out`, 5 s) prints `[propext, Classical.choice, Quot.sound]` for every one of them: no `sorryAx`, no other axiom.

**The rows of `STATEMENTS.md`** (lines 1003, 1004, 1009 to 1013), sentence by sentence against the statements:

| row | file | finding |
|---|---|---|
| 1003 | `OneBlock/MlpBiases.lean` (earlier audit) | its new sentences ("the two values named for tanh and GELU are in `OneBlock/MlpBiasesNamed.lean`"; "SwiGLU and GeGLU blocks with biases: `OneBlock/GatedBiases.lean`; ReLU and ReLU² blocks: `OneBlock/RescaleBiases.lean`; the ReGLU block: `OneBlock/ReGLUBiases.lean`. Not stated: attention blocks with biases") are true |
| 1004 | `MlpBiasesNamed.lean` | true; the four names are the four theorems of the file |
| 1009 | `GatedBiases.lean` | true: `GatedUnitsRescale` has the biases `β`, `β′`; `OneBlockGenericGated` on the weights; the flat directions are `cobDirB p X + (0, translateAtDir p.1 g) + rescaleDirB p α` (skipless), `cobDirB p (fun _ => X) + (0, translateDir p.1 g) + rescaleDirB p α` (residual); the two values; `d_in, d_out, d_hidden ≥ d ≥ 2`; gain `d²`; named gain for SwiGLU and GeGLU; the nine names are the nine theorems; the numeric script exists |
| 1010 | `GatedBiasesNamed.lean` | true |
| 1011 | `FunctionalBiasesOn.lean` | true. Small points: the quotation is printed with doubled quotation marks (`""every input" means every such input"`); the hypothesis of differentiability on `U` is not needed for the truth of `exists_jacobianRankB_add_finrank_flatOnB` (check 4), so the row could say "if" more weakly, but it is not false |
| 1012 | `RescaleBiases.lean` | true: the quotation of Step 3 is verbatim; `noKinkB` is the stated set; `differentiableAt_evalB_of_mem_noKinkB` holds for every stream matrix; the 23 names are `noKinkB` and the 22 theorems. "Lean's `funDimB` uses every input at which the output is differentiable in the parameters" is right in effect: `funDimB` takes every batch, and a batch with an input at which the output is not differentiable has `fderiv = 0` and rank `0` (check 4) |
| 1013 | `ReGLUBiases.lean` | true: "no value column of `E W_read` proportional to the gate column of the same unit, which gives the condition of Lemma B.3 on the pairs of column and bias" (check 1); gate-only `noKinkGateB`; the two rescalings with their biases; `2 d_hidden`; the 13 names are `noKinkGateB` and the 12 theorems |

Each row ends with `proved`, which the axioms confirm.

**What of Theorem B.1 (i) with biases is not stated.** With the six files and `OneBlock/MlpBiases.lean`, the clause "with biases on the embedding, the block and the readout, counted in `P`, both values are `2 d_model` lower" is stated, at generic parameters and with the gain `d²`, for all seven kinds of MLP block (tanh, GELU, ReLU, ReLU², ReGLU, SwiGLU, GeGLU). Not stated: "and `2 d_model + 2 H d_h` lower for attention" (the attention block with biases). At `49f38c2` and `cb6eee1` nothing on it is in the index (three files on it were on disk, untracked). At `e0c9eaf` (the commit at the end of this audit) the index has new rows for it, with `Symmetry/AttentionHeadsBiases.lean`, `Dimension/UpperBoundAttentionBiases.lean`, `OneBlock/AttentionBiases.lean`, `OneBlock/AttentionBiasesStepOne.lean` and `OneBlock/AttentionBiasesDim.lean` ("written at 09:24 UTC, 25 November", after this audit began), and row 1003 now ends "The attention block with biases: `OneBlock/AttentionBiasesDim.lean`" in place of "Not stated: attention blocks with biases". These files are not the subject of this audit and I did not read them (beyond the header of `OneBlock/AttentionBiases.lean`, which states the reduction and Step 2). Not stated either, as in the files without biases: "Both networks satisfy the equality condition" as the named property (the library has no definition of the equality condition for networks with biases; check 3 says what the statements give instead), and inputs in an open set ("For analytic blocks, any open set of inputs gives the same results").

Verdict of check 6: the six rows are **true** of the statements; all 53 theorems are registered and depend on the three standard axioms only; the only clause of Theorem B.1 (i) with biases not stated in the subject is the attention block (stated after this audit began in files not read here).


## Part 2: the statements, file by file

The paper sentences: (B1) Theorem B.1 (i), "with biases on the embedding, the block and the readout, counted in `P`, both values are `2 d_model` lower […] Both networks satisfy the equality condition, and the skip raises the functional dimension by exactly `d_model²`", with its hypotheses (`d_model ≥ 2`, `d_in, d_out ≥ d_model`, width at least `d_model`, no normalization); (NF) Appendix B, "Notation and flat directions" ("For the ReLU-type activations, `F(θ, x)` is differentiable in `θ` at the inputs `x` at which no hidden unit sits at its kink […] and “every input” means every such input"; "some finite batch has kernel exactly `K(θ)`. By rank–nullity, the functional dimension at `θ` is therefore `P − dim K(θ)`"); (S3) Step 3 ("every flat direction is the sum of a direction of the changes of basis and translations of Lemma B.2 and a rescaling of the units", with Lemma B.2 with biases and Lemma B.3); (G) "For generic parameters …" (Reduction) and "A statement holds for generic parameters if it fails only where some nonzero polynomial […] vanishes".

### `OneBlock/GatedBiases.lean` (9 theorems)

| statement | paper | verdict | note |
|---|---|---|---|
| `flatB_le_range_gated_skipless` | S3 with Lemma B.2 with biases, skipless, SwiGLU/GeGLU | SAME | under `OneBlockGenericGated` (weights only) and `GatedUnitsRescale` (Lemma B.3 for the gate, with biases); the paper's "not proportional" is not asked and not needed (check 1) |
| `flatB_le_range_gated_residual` | S3, residual | SAME | as above |
| `funDimB_gated_oneBlock` | B1, skipless value at one parameter, `s = d_hidden` | SAME | at every bias |
| `funDimB_gated_oneBlock_residual` | B1, residual value at one parameter | SAME | |
| `ae_funDimB_gated_oneBlock` | B1 + G, skipless | SAME | every Haar measure on the pairs; hypotheses exactly the paper's |
| `ae_funDimB_gated_oneBlock_residual` | B1 + G, residual | SAME | |
| `ae_funDimB_gated_oneBlock_residual_eq_add` | B1, "the skip raises … by exactly `d_model²`" | SAME | |
| `ae_funDimB_swiglu_oneBlock_residual_eq_add` | the same for SwiGLU | SAME | `Arch.gated silu` |
| `ae_funDimB_geglu_oneBlock_residual_eq_add` | the same for GeGLU | SAME | `Arch.gated gelu` |

### `OneBlock/GatedBiasesNamed.lean` (4) and `OneBlock/MlpBiasesNamed.lean` (4)

| statement | paper | verdict | note |
|---|---|---|---|
| `ae_funDimB_swiglu_oneBlock`, `ae_funDimB_swiglu_oneBlock_residual` | B1 for SwiGLU, both values | SAME | check 5 |
| `ae_funDimB_geglu_oneBlock`, `ae_funDimB_geglu_oneBlock_residual` | B1 for GeGLU | SAME | |
| `ae_funDimB_tanh_oneBlock`, `ae_funDimB_tanh_oneBlock_residual` | B1 for tanh (`s = 0`) | SAME | |
| `ae_funDimB_gelu_oneBlock`, `ae_funDimB_gelu_oneBlock_residual` | B1 for GELU (`s = 0`) | SAME | `gelu z = z Φ(z)` |

### `Dimension/FunctionalBiasesOn.lean` (1 definition, 2 theorems)

| statement | paper | verdict | note |
|---|---|---|---|
| `flatOnB` | NF: `K(θ)` with "every input" = every input of a set, with biases | SAME | the twin of `flatOn` |
| `flatB_le_flatOnB` | (a flat direction is flat on any set of inputs) | SAME | |
| `exists_jacobianRankB_add_finrank_flatOnB` | NF: a finite batch with kernel `K_U(θ)`, rank `P − dim K_U(θ)` | SAME; LEAN WEAKER in a harmless way | the hypothesis `hU` (differentiability on `U`) is not needed for the truth of the statement (check 4) |

### `OneBlock/RescaleBiases.lean` (1 definition, 22 theorems)

| statement | paper | verdict | note |
|---|---|---|---|
| `noKinkB` | NF: inputs with no hidden unit at its kink, with biases | SAME | pre-activation `(x E W_read)_{t,i} + (b_E W_read + b_read)_i` |
| `differentiableAt_evalB_of_mem_noKinkB` | NF: "`F(θ, x)` is differentiable in `θ` at the inputs …" | SAME | every stream matrix; `σ` differentiable off `0` |
| `flatOnB_noKinkB_le_mlp_rescale`, `…_residual` | S3 with Lemmas B.2, B.3 for ReLU/ReLU², with biases | SAME | over the paper's inputs; `rescaleDirMlpB k` |
| `funDimB_mlp_oneBlock_rescale`, `…_residual` | B1 at one parameter (Lean's `funDimB`) | PART alone; SAME with the next | under `OneBlockGeneric`, at every bias |
| `exists_jacobianRankB_mlp_oneBlock_rescale`, `…_residual` | B1 at one parameter on the paper's inputs | PART alone; SAME with the previous | the pair is the paper's value (check 4) |
| `ae_funDimB_mlp_oneBlock_rescale`, `ae_exists_jacobianRankB_mlp_oneBlock_rescale`, `ae_funDimB_mlp_oneBlock_rescale_residual`, `ae_exists_jacobianRankB_mlp_oneBlock_rescale_residual` | B1 + G for an activation homogeneous of degree `k` with `UnitsRescale` | SAME (the pairs) | |
| `ae_funDimB_mlp_oneBlock_rescale_residual_eq_add` | B1, the gain `d²` | SAME | for Lean's `funDimB`; with the pairs also for the paper's value |
| `ae_funDimB_relu_oneBlock`, `ae_exists_jacobianRankB_relu_oneBlock`, `ae_funDimB_relu_oneBlock_residual`, `ae_exists_jacobianRankB_relu_oneBlock_residual`, `ae_funDimB_relu_oneBlock_residual_eq_add` | B1 for ReLU | SAME (the pairs) | `k = 1` |
| the five `…_reluSq_…` | B1 for ReLU² | SAME (the pairs) | `k = 2` |

### `OneBlock/ReGLUBiases.lean` (1 definition, 12 theorems)

| statement | paper | verdict | note |
|---|---|---|---|
| `noKinkGateB` | NF for ReGLU, with biases | SAME | gate pre-activations only (right) |
| `differentiableAt_evalB_of_mem_noKinkGateB` | NF | SAME | every stream matrix |
| `flatOnB_noKinkGateB_le_reglu`, `…_residual` | S3 with Lemmas B.2, B.3 for ReGLU, with biases | SAME | `rescaleDirB p α + rescaleDirGateB 1 p β`; under `OneBlockGenericReGLU`, whose condition on the columns implies the paper's on the pairs (check 1) |
| `funDimB_reglu_oneBlock`, `exists_jacobianRankB_reglu_oneBlock`, and the two `…_residual` | B1 at one parameter, `s = 2 d_hidden` | SAME (the pairs) | |
| `ae_funDimB_reglu_oneBlock`, `ae_exists_jacobianRankB_reglu_oneBlock`, `ae_funDimB_reglu_oneBlock_residual`, `ae_exists_jacobianRankB_reglu_oneBlock_residual` | B1 + G for ReGLU | SAME (the pairs) | |
| `ae_funDimB_reglu_oneBlock_residual_eq_add` | B1, the gain `d²` | SAME | |

Of Theorem B.1 (i) with biases as a whole: **PART** (the seven kinds of MLP block are stated, with this file set and `OneBlock/MlpBiases.lean`; the attention block with biases is not).

## What the authors of the papers should know

Nothing in the subject is false, vacuous or drifted. The 53 statements compare with Theorem B.1 (i) with biases, Lemma B.2 with biases, Lemma B.3 and Step 3 as SAME (for the ReLU-type blocks: the pairs of statements), and they are proved with the standard axioms. Points for the papers:

1. **The condition "`(e_i, β_i′)` not proportional to `(c_i, β_i)`" is needed for ReGLU only.** The Reduction and Lemma B.3 ask it for all three gated blocks. The proof for SwiGLU and GeGLU does not use it (it uses `e_i ≠ 0`), the Lean statements for them do not ask it, and a computation with `(e_i, β_i′) = 2 (c_i, β_i)` for every unit gives the SwiGLU values (check 1). For ReGLU it is needed: with `(e_i, β_i′) = 2 (c_i, β_i)` the rank is two below the value per unit (`10` against `14`, `16` against `22`), and a coarse random draw hit such a parameter by chance (check 2). The paper could say "for ReGLU" in the Reduction and in the hypothesis of Lemma B.3, or keep the condition as a harmless generic one.
2. **"Which form an open set of full measure."** With biases, the inputs with no hidden unit at its kink form an open set of full measure unless some unit has `c_i = 0` and `β_i = 0`; at such a parameter the set is empty and "every input means every such input" leaves no input. Lean's `funDimB` (all inputs at which the output is differentiable) is then larger than the paper's value, read literally (check 4). This concerns parameters of measure zero only; the theorem is about generic parameters, where the two agree (the pair of statements).
3. **The hypotheses.** `d_in, d_out ≥ d_model` are needed for both values; `d_hidden ≥ d_model` is needed for the skipless value in some cases (ReLU, `(d, d_in, d_out, d_hidden) = (2,3,3,1)`: at most `9` against `11`) but not when `d_in = d_out = d_model`; for `d_model = 1` the values with biases hold in the cases computed (check 2). The theorem's hypotheses are sufficient; this is not a defect, only a note on which of them matter.

## Corrections for `STATEMENTS.md`

None is needed for truth. Small points:

- Row of `Dimension/FunctionalBiasesOn.lean` (line 1011): the quotation is printed with doubled quotation marks (`""every input" means every such input"`); one pair suffices. Optionally: the hypothesis of differentiability in `exists_jacobianRankB_add_finrank_flatOnB` is not needed for the statement to hold (check 4).
- Row of `OneBlock/GatedBiases.lean` (line 1009): it could say, as the docstring of `GatedUnitsRescale` does, that the paper's condition "`(e_i, β_i′)` not proportional to `(c_i, β_i)`" is not asked (and, by check 1, not needed) for SwiGLU and GeGLU.
- Row of `OneBlock/RescaleBiases.lean` (line 1012): "Lean's `funDimB` uses every input at which the output is differentiable in the parameters" is right in effect; it could add "and can exceed the paper's value at parameters of measure zero (a unit with read column and read bias `0`)", as the fourth audit's finding without biases.

## What could not be checked

- The proofs (not the subject). Their axioms were checked (check 6).
- The definitions and bounds of part A (`rescaleDirMlpB`, `rescaleDirB`, `rescaleDirGateB`, the bounds of `Symmetry/BiasesRescaleCount.lean`, `funDimB_add_finrank_flatB'`) were read only as far as the statements here use them; part A is another reader's. Their directions were checked numerically here (check 3).
- No Lean example was compiled for point 2 above (Lean's `funDimB` larger than the paper's value at a parameter with biases); the argument is by reading, and the fourth audit machine-checked the same phenomenon without biases.
- The computations are at small sizes (`d ≤ 3`, `d_hidden ≤ 3`, two tokens) and give ranks on finite batches (lower bounds); they agree with the values in every case inside the hypotheses.
- The files on the attention block with biases, written after this audit began (`e0c9eaf`), were not read.
