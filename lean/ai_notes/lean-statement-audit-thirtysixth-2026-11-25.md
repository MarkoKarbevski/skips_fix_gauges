STATUS: complete

# Thirty-sixth audit of Lean statements against the papers: S Theorem B.1 (iv), last sentence, at almost every parameter; S Lemma A.8 as a group of maps (25 November 2026)

Commit read at the start: `1c6ff30` of `/home/claude/lp` (branch `lean-plus`).
Files with `sorry` at `1c6ff30`: `SkipsLean/Symmetry/BiasesAffineGroupLaw.lean` (10 statements; the two `…_eq_self_iff` are proved from them); at `9e55a6c` and after: none. `SkipsLean/OneBlock/RedundancySymmetriesRMSZero.lean` has no `sorry`.
Paper: `<scratchpad>/skips.txt`. Scratch work: `/home/claude/audit36/`.

## Part 1

### Check 1. The last sentence of Theorem B.1 (iv), without the skip (by reading)

Lean (`ae_flatOn_le_relu_oneBlock_skipless_rmsNorm_zero_of_le`; the ReLU² twin with `rescaleDirMlp 2`):

```
(hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
(hdOut : Fintype.card d ≤ Fintype.card dOut) (hcard : Fintype.card d ≤ Fintype.card (hid 0)) :
∀ᵐ θ ∂μ, ∀ η ∈ flatOn (Arch.mlp relu (rmsNorm 0) hid) 0 θ
    (skiplessZeroDomain (Arch.mlp relu (rmsNorm 0) hid) θ ∩ noKinkRMS θ),
  ∃ (X Y : Matrix d d ℝ) (c : ℝ) (α : ∀ ℓ, hid ℓ → ℝ), Yᵀ = -Y ∧
    η = cobDir θ ![X, Y] + c • scaleDir θ ![0, 1] + rescaleDirMlp 1 θ α
```

(a) The directions. `cobDir θ ![X, Y]` has `E X` at `E`, `−X W_read` at the read, `W_write Y` at the write, `−Y D` at `D`; `c • scaleDir θ ![0, 1]` has `0` at `E`, `c W_write` at the write, `0` at the read and at `D`. The sum is `E X`, `−X W_read`, `W_write (Y + cI)`, `−Y D`: word for word the paper's directions in "The skipless network: the bound" ("the entries `EX` at `E` and `−XW_read` at `W_read`, with the entries `W_write(Y + cI)` at `W_write` and `−YD` at `D` for an antisymmetric `Y` and a number `c`"). With `X` arbitrary this is the tangent space of `GL(d)` at `h_0`; with `Yᵀ = −Y` and `c` it is that of `CO(d)` at `h_1` (rotation `Q` acts as `W_write Q`, `Q⁻¹ D`; the scaling `c` at `h_1` leaves `D` alone because `N_0(c h) = N_0(h)`). `rescaleDirMlp k θ α` has `α_i` times the read column of unit `i`, `−k α_i` times its write row, `0` at `E` and `D`: the derivative of `(c_i, a_i) ↦ (λ_i c_i, a_i/λ_i^k)` at `λ = e^{τα}`. Signs right. Permutations of units have no directions. SAME.

(b) The inputs. `skiplessZeroDomain θ`: no row of `x E` and no row of `h_1 = f(N_0(xE) W_read) W_write` is zero; `noKinkRMS θ`: no entry of `x E W_read` is zero (the same as no entry of `N_0(xE) W_read`, since each row of `N_0(xE)` is a positive multiple of the row of `x E`). This is the paper's set: "every input" is every input at which no hidden unit sits at its kink (Appendix C), and the network is defined where no normalized row vanishes (the set `Ω` of "The skipless network: equality", token by token). SAME.

(c) "Redundancy". The paper's `K(θ)` is the kernel of the Jacobian on all finite batches, i.e. the intersection over the inputs of the kernels of `D_θ F(x)`. `flatOn A 0 θ U` is `⨅ x ∈ U, ker (fderiv (θ' ↦ eval A 0 θ' x) θ)`: the same intersection over `U`. So "flat at these inputs" is the paper's `K(θ)` on the paper's inputs (at an input of `U` the network is differentiable in `θ`, so no input is dropped by Mathlib's convention `fderiv = 0`). Lean states the inclusion `K(θ) ⊆ symmetry directions`; the converse is check 3. As the inclusion for the set of the paper: SAME.

(d) The hypotheses: `d ≥ 2`, `d_in, d_out ≥ d`, width at least `d`, `ε = 0`, no biases, `[Nonempty T]`: the theorem's (`T` empty is excluded by the setting; see check 7). SAME.

Verdict, by reading: SAME (the inclusion; the numerical check follows below).

Computation (`/home/claude/audit36/check12.py`, numpy, exact derivative by complex step of step `1e-30`; `N_0(h) = √d h/√(Σ h²)` written analytically; ReLU as `z` for `Re z > 0`, else `0`; one token per input, Gaussian inputs, so `x E` covers all directions of `h_0`; inputs with an entry of `N_0(xE) W_read` below `1e-6` or a row of `h_1` below `1e-6` dropped; `d_in = d_out = 3`). For each network: the rank at the largest gap of the singular values, the span of the symmetry directions (`E X, −X W_read` for all `X`; `W_write Y, −Y D`, `Y` antisymmetric; `W_write` for the scaling; the rescalings), `‖J V‖/‖J‖`, and the dimension of kernel + span (equal to both iff kernel = span).

| network | P | rank (gap) | kernel | span of symmetries | `‖JV‖/‖J‖` | kernel + span |
|---|---|---|---|---|---|---|
| skipless ReLU², `d = 2`, width 3, 200 inputs | 24 | 15 (gap `1.0e13`, `4.2e11` on a second draw) | 9 | 9 | `1e-15` | 9 |
| skipless ReLU, `d = 2`, width 3, 200 / 400 inputs, 13 draws | 24 | 15 (gaps `7e11` to `1e14`) | 9 | 9 | `≤ 6e-15` | 9 |
| skipless ReLU², `d = 3`, width 4 | 42 | 25 (gap `2.5e13`) | 17 | 17 | `4e-16` | 17 |

`9 = d² + d(d−1)/2 + 1 + s = 4 + 1 + 1 + 3` and `17 = 9 + 3 + 1 + 4`: the kernel of the Jacobian on the batch is the span of the directions of `GL(d)` at `h_0`, `CO(d)` at `h_1` and the rescalings, equal. One draw of the ReLU network gave kernel 10 with 200 inputs; its read columns at angles `133.08°` and `132.48°` leave sectors of `h_0` of width `0.6°` with a different set of active units that 200 inputs missed; with 3000 inputs at the same parameter the kernel is 9 (gap `7.5e10`). A batch issue, not a counterexample.

Verdict of check 1: SAME (by reading, and by the computation).

### Check 2. With the skip (by reading, and by a computation)

Lean (`ae_flatOn_le_relu_oneBlock_residual_rmsNorm_zero`, `…_reluSq_…`):

```
[Nonempty (hid 0)] … (hd : 2 ≤ Fintype.card d) (hdIn : …) (hdOut : …) :
∀ᵐ θ ∂μ, ∀ η ∈ flatOn (Arch.mlp relu (rmsNorm 0) hid) 1 θ
    (residualZeroDomain (Arch.mlp relu (rmsNorm 0) hid) θ ∩ noKinkRMS θ),
  ∃ (Y : Matrix d d ℝ) (c : ℝ) (α : ∀ ℓ, hid ℓ → ℝ), Yᵀ = -Y ∧
    η = cobDir θ (fun _ => Y) + scaleDir θ (fun _ => c) + rescaleDirMlp 1 θ α
```

and for ReGLU (`Arch.gated relu`, inputs `residualZeroDomain ∩ noKinkGateRMS θ`):
`η = cobDir θ (fun _ => Y) + scaleDir θ (fun _ => c) + rescaleDir θ α + rescaleDirGate 1 θ β`.

(a) `cobDir θ (fun _ => Y) + scaleDir θ (fun _ => c)` is `E (Y + cI)` at `E`, `−Y W_read` at the read, `W_write (Y + cI)` at the write, `−Y D` at `D`: the derivative of the change of basis `G = c' Q` at both `h_0` and `h_1` with the correction `K = Q` before the read and the readout (`Params.cob θ G K`: `E G`, `K⁻¹ W_read`, `W_write G`, `K⁻¹ D`), with `Q = e^{τY}`, `c' = e^{τc}`. One rotation and one scaling, shared: the paper's "rotation and scaling of all hidden states" and "one `CO(d_model)`" (the paper's proof: "`η_E = E(Y + cI)`, so `X_s = cI`"). SAME.

(b) The rescalings inside the block: MLP, `rescaleDirMlp k` as in check 1. ReGLU (`read` indexed by `Sum` of gates `inl` and values `inr`; the block `σ(gate) · value`): `rescaleDir θ α` has `−α_i` at the value column of unit `i` and `+α_i` at its write row (the values are linear, any `λ ≠ 0`); `rescaleDirGate 1 θ β` has `β_i` at the gate column and `−β_i` at the write row (ReLU gate, degree 1). Two per unit, `s = 2 · width`: the paper's "values and gates". `noKinkGateRMS θ`: no gate entry of `x E W_read` is zero; the values have no kink. The paper's inputs. SAME.

(c) Hypotheses: `d ≥ 2`, `d_in, d_out ≥ d`, a hidden unit, any width. The theorem asks width at least `d_model`; Lean asks only one unit. LEAN STRONGER on the width (the computation below confirms width 1 for ReLU). `[Nonempty (hid 0)]`: with no unit the read and write are empty matrices, the network is `x ↦ N_0(xE) D`, and (by reading, for `E` and `D` of rank `d`) its flat directions are `E(Y + cI)`, `−Y D`, which is again the conclusion; so the hypothesis is probably not needed, and it only excludes a block outside the theorem's scope (width at least `d ≥ 2`). Harmless.

Computation (same script):

| network | P | rank (gap) | kernel | span of symmetries | `‖JV‖/‖J‖` | kernel + span |
|---|---|---|---|---|---|---|
| residual ReLU, `d = 2`, width 3 | 24 | 19 (gap `1.1e14`, `1.3e14`) | 5 | 5 | `3e-16` | 5 |
| residual ReLU², `d = 2`, width 3 | 24 | 19 (gap `1.2e14`, `9.8e11`) | 5 | 5 | `2e-16` | 5 |
| residual ReLU, `d = 2`, width 1 | 16 | 13 (gap `9.6e14`, `6.6e14`) | 3 | 3 | `2e-16` | 3 |

`5 = d(d−1)/2 + 1 + s = 1 + 1 + 3`. Equal.

Verdict of check 2: SAME (LEAN STRONGER on the width).

ReGLU (`/home/claude/audit36/reglu.py`, same method; the read has gate and value columns, the block `relu(n W_g) ⊙ (n W_v) W_write`; symmetry directions: two rescalings per unit, the rotation, the scaling, and without the skip `E X, −X W_g, −X W_v`):

| network | P | rank (gap) | kernel | span | `‖JV‖/‖J‖` | kernel + span |
|---|---|---|---|---|---|---|
| residual ReGLU, `d = 2`, width 3, two draws | 30 | 22 (gaps `2.6e13`, `3.1e12`) | 8 | 8 | `2e-16` | 8 |
| residual ReGLU, `d = 2`, width 1, two draws | 18 | 14 (gaps `1.7e14`, `2.6e14`) | 4 | 4 | `1e-16` | 4 |

`8 = 1 + 1 + 2·3`. Equal.

### Check 3. Is the converse stated; is all of part (iv), and of Theorem B.1, stated (by reading the index and the sources)

**The converse** (the directions of the symmetries are flat at every input, `∈ flat A S θ`, which lies inside `flatOn` of any set by `flat_le_flatOn`), at every parameter:
- skipless, `GL(d)` at `h_0`: `cobDir_single_mem_flat_skipless_rmsNorm_zero_of_rowHomogeneous` (`Dimension/UpperBoundHomogeneousRMSNormZero.lean`; `cobDir θ (Pi.single ℓ.castSucc X) ∈ flat A 0 θ` for every `X`, blocks `RowHomogeneous`, which `rowHomogeneous_mlp` gives for ReLU and ReLU²), and `cobDir_zero_mem_flat_skipless_rmsNorm_zero_of_rowHomogeneous` (`OneBlock/SkiplessHomogeneousRMSZero.lean`, the same at `L = 1`);
- skipless, the rotation at `h_1`: `cobDir_mem_flat_skipless_rmsNorm'` (`Dimension/UpperBoundRMSNorm.lean`, every real `ε`, antisymmetric `X_ℓ`, so `![0, Y]`); the scaling at `h_1`: `scaleDir_mem_flat_skipless_rmsNorm_zero` (every `β`, so `![0, 1]`);
- residual: `cobDir_const_mem_flat_residual_rmsNorm_zero` (`Yᵀ = −Y`), `scaleDir_const_mem_flat_residual_rmsNorm_zero`;
- inside the block: `rescaleDirMlp_mem_flat` (any `χ`, any stream matrices, `σ` positively homogeneous of degree `k`), `rescaleDir_mem_flat'` (values, any gate), `rescaleDirGate_mem_flat` (gates).

`flat` is a subspace, so with the five statements: at almost every parameter, `flat = flatOn U = span of the symmetry directions` with `U` the paper's inputs, for the five networks. The equality is not written as one statement; it is two lines from these. The index row of the file says "That the directions of these symmetries are flat is in the upper bounds" without naming the statements; the names above should be given (corrections).

**Part (iv), sentence by sentence, at almost every parameter** (the table of the thirty-fifth reader, part A, check 5c, with this file):

| sentence of (iv) | ReLU | ReLU² | ReGLU |
|---|---|---|---|
| residual value, with a batch of the paper's inputs | `OneBlock/ResidualRMSZeroRescaleGeneric.lean` | same | `OneBlock/ResidualRMSZeroReGLUGeneric.lean` |
| skipless "at most" | `OneBlock/SkiplessHomogeneousRMSZero.lean` | same | `OneBlock/SkiplessHomogeneousGatedRMSZero.lean` |
| "with equality" (width at least `d`) | `OneBlock/SkiplessReluWideRMSZero.lean` | `OneBlock/SkiplessReluSqWideRMSZero.lean` | not claimed |
| "by at least `d_model²`" | `OneBlock/ResidualRMSZeroGainHomogeneous.lean` | same | same |
| "by exactly `d_model²`" | `OneBlock/SkiplessReluWideRMSZero.lean` | `OneBlock/SkiplessReluSqWideRMSZero.lean` | not claimed |
| "The redundancy is then that of the symmetries" | **this file** (skipless and residual) | **this file** (both) | **this file** (residual); skipless: not claimed (see below) |

So every sentence of part (iv) is now stated at almost every parameter, for each kind of block for which the paper claims it. The last sentence's "then" refers to the equality cases; for a skipless ReGLU block the theorem claims only the bound, and Lean states nothing there (the module docstring says so). My computation (`/home/claude/audit36/reglu.py`) suggests that the sentence is true there too: skipless ReGLU, `d = 2`, widths 2 and 3, two draws each: kernel `10` and `12`, equal to the span of the symmetries (`d² + 1 + 1 + 2·width`), `‖JV‖/‖J‖ < 4e-15`, gaps `2.4e10` to `1.4e12`. With the bound, this is equality for a skipless ReGLU block at these parameters (for the authors).

**The rest of Theorem B.1.** The dossier of 24 November (`/home/claude/proj_up/dossier-B1-what-is-left-2026-11-24.md`) listed four missing cases; each now has rows in the index (`proved`): M1, part (i) with biases for the seven MLP and gated kinds (rows of `OneBlock/MlpBiases.lean`, `OneBlock/GatedBiases.lean`, `OneBlock/RescaleBiases.lean`, `OneBlock/ReGLUBiases.lean`, and the named files); M2, part (i) with biases for attention (`OneBlock/AttentionBiases.lean`, `…StepOne.lean`, `…Dim.lean`); M3, part (iii) for `ε > 0` and tanh, GELU, SwiGLU, GeGLU narrower than `d` (`OneBlock/LearnedSkipNarrowMlp.lean`, `…NarrowGated.lean`, `…TriangularNarrow.lean`); M4, ReLU² wider than `d` (`OneBlock/SkiplessReluSqWideRMSZero.lean`); and (iv-e) is this file. By the rows of the index (I did not re-read those files' statements), nothing of Theorem B.1 (i) to (v) is left unstated; what remains is in the form of the statements: the equality condition is an equation, not a definition, and the last sentence of (iv) is two statements (the inclusion here and the flatness of the symmetries), as said above.

Verdict of check 3: the converse is stated (in pieces, at every parameter); part (iv) is stated in full at almost every parameter.

**Note on the commit.** At 12:09 UTC the branch had moved to `9e55a6c` ("merge the group of the changes of basis and translations of Lemma A.8 […] as a group of maps"): `Symmetry/BiasesAffineGroupLaw.lean` is now without `sorry`. `git diff 1c6ff30 9e55a6c` on the two files removes only `sorry` lines and adds private helpers; no public statement or definition changed. Checks 4 to 6 compare the statements, which are the same at both commits.

### Check 4. The maps of the pairs (by reading, and by a computation)

Definitions (`Symmetry/BiasesAffineGroupLaw.lean`, with `Params.cob θ G K`: `E G_0`, `K_{ℓ−1}⁻¹ W_read^ℓ`, `W_write^ℓ G_ℓ`, `K_L⁻¹ D`; `Biases.cob b G`: `b_E G_0`, `b_write^ℓ G_ℓ`, read and readout biases unchanged; `Biases.translateAllAt b θ g`: `b_E + g_0`, `b_read^ℓ − g_{ℓ−1} W_read^ℓ`, `b_write^ℓ + g_ℓ`, `b_D − g_L D`; `Biases.translateAll b θ g`: the same with `g_{ℓ−1}`, `g_L` replaced by the partial sums `S_m = g_0 + … + g_m`):

```
def affActSkipless p q := (q.1.cob p.1 p.1, (q.2.translateAllAt q.1 p.2).cob p.1)
def affActResidual p q := (q.1.cob p.1 p.1, (q.2.translateAll q.1 p.2).cob p.1)
def affMul p p' := (fun ℓ => p.1 ℓ * p'.1 ℓ, fun ℓ => p.2 ℓ + p'.2 ℓ ᵥ* (↑(p.1 ℓ)⁻¹ : Matrix d d ℝ))
```

The translation uses the read and the readout of `q` before the change of basis, then the change of basis acts: the hidden state `h_m` becomes `(h_m + g_m) G_m` (skipless) or `(h_m + S_m) G_m` (residual). The pair `(G, g)` followed by `(G', g')` sends `h_m` to `((h_m + g_m) G_m + g'_m) G'_m = (h_m + g_m + g'_m G_m⁻¹) G_m G'_m`: the thirty-fifth reader's `(G G', g + g' G⁻¹)`, which is `affMul`. As a law on pairs it is associative, with unit `(1, 0)` and inverse `(G⁻¹, −g G)`; `p ↦ affAct p` reverses the order (`affAct p' ∘ affAct p = affAct (affMul p p')`), which is the convention of a right action and changes nothing for the image being a subgroup.

By hand, entry by entry:
- skipless: `E'' = E G_0 G'_0`, `b_E'' = (b_E + g_0 + g'_0 G_0⁻¹) G_0 G'_0`, `W_read'' = (G_{ℓ−1} G'_{ℓ−1})⁻¹ W_read`, `b_read'' = b_read − (g_{ℓ−1} + g'_{ℓ−1} G_{ℓ−1}⁻¹) W_read`, the same pattern at the writes and the readout: `affActSkipless_affActSkipless` holds for all pairs. TRUE.
- residual: the read bias of block `ℓ` and the readout bias carry the partial sums; the composite has `S_m + S'_m G_m⁻¹` where `affMul` gives `S_m + ∑_{k ≤ m} g'_k G_k⁻¹`. They agree for every `g'` iff `G_k = G_m` for `k ≤ m`, i.e. iff the `G` of the **first** pair is constant; the second pair is arbitrary. So `hp : ∀ ℓ, p.1 ℓ = p.1 0` is needed and asking it of `p` only is right. TRUE.
- `…_one`: `cob 1 1` and the translation by `0` are the identity. TRUE.
- `…_bijective`: skipless, from the composition and `…_one` with the inverse pair. Residual, for every pair (also unequal `G_ℓ`): the map is triangular (the weights by invertible matrices, then each bias by an invertible matrix plus a term in the weights), with explicit inverse `E = E' G_0⁻¹`, `b_E = b_E' G_0⁻¹ − g_0`, `W_read = G_{ℓ−1} W_read'`, `b_read = b_read' + S_{ℓ−1} G_{ℓ−1} W_read'`, `W_write = W_write' G_ℓ⁻¹`, `b_write = b_write' G_ℓ⁻¹ − g_ℓ`, `D = G_L D'`, `b_D = b_D' + S_L G_L D'`. TRUE.

Computation (`/home/claude/audit36/affine.py`: the maps written entry by entry as in the Lean definitions; `L = 2`, `d = 2`, width 3, `d_in = 3`, `d_out = 2`, two tokens, tanh blocks with biases, random pairs):

| test | max. difference |
|---|---|
| `(1, 0)` moves nothing, skipless / residual | `0` / `0` |
| skipless, `affAct p' ∘ affAct p = affAct (affMul p p')`, unequal `G_ℓ` in both | `2.7e-15` |
| residual, `p` with equal `G_ℓ`, `p'` unequal | `5.3e-15` |
| residual, `p` unequal, `p'` arbitrary | `0.45` (read biases and readout bias differ); `p` unequal, `p'` equal: `0.77` |
| residual, explicit inverse, unequal `G_ℓ`, left and right | `7.2e-16`, `7.2e-16` |
| skipless function kept by a pair with unequal `G_ℓ` | `8.9e-16` |
| residual function kept by a pair with equal `G_ℓ` / changed with unequal | `4.9e-15` / `4.17` |

Verdict of check 4: the four statements of each kind are TRUE; the hypothesis `hp` is needed, on the first pair only. SAME as the thirty-fifth reader's composition (and as "A skip ties only the linear part of `Aff(d_model)`").

### Check 5. "The symmetry group" (by reading, and by the computation above)

```
theorem exists_subgroup_affActSkipless (A : Arch T d L) :
    ∃ K : Subgroup (Equiv.Perm (Params A dIn dOut × Biases A dOut)),
      ∀ φ, φ ∈ K ↔ ∃ p ∈ affPreservingSkipless A dIn dOut, ⇑φ = affActSkipless p
theorem exists_subgroup_affActResidual [Nonempty T] [Nonempty dOut] (A : Arch T d L) (hA : A.χ = id) : … affPreservingResidual … affActResidual p
```

`affPreservingSkipless A` is the set of pairs whose map keeps `evalB A 0` at **all** weights, biases and inputs; it is closed under `affMul` and the inverse pair, by the composition law (if `F ∘ φ_p = F` and `F ∘ φ_{p'} = F` then `F ∘ φ_{p'} ∘ φ_p = F`; `φ_{p⁻¹} = φ_p⁻¹`), and contains `(1, 0)`. So its image is a subgroup, whatever `A` (also with a normalization, where the set may be smaller than all pairs). TRUE with no hypothesis on the network, as stated.

Residual: by `mem_affPreservingResidual_iff` (`Symmetry/BiasesAffineGroup.lean`, under `[Nonempty T] [Nonempty dOut]` and `χ = id`) the set is the pairs with all `G_ℓ` equal, which is closed under `affMul` and the inverse, and on which the composition law holds (`hp`). TRUE. The hypotheses are needed for the statement as written: for `T` empty (or `d_out` empty and `L ≥ 2`) every pair preserves the function (an output with no rows, or no columns), and the maps of all pairs are not closed under composition: for `p` with unequal `G_ℓ`, the composite `affAct p' ∘ affAct p` agrees with the only candidate `affAct (affMul p p')` (forced by `E`, the reads, the writes, `D`, the embedding and write biases) everywhere but at the read biases and the readout bias, where it differs (the `0.45` above), so it is the map of no pair, and no subgroup has exactly these elements. So the statement would be false without `[Nonempty T]`; the hypotheses are the setting of the paper, not an extra condition.

Is this "the maps form a group"? Yes: `K` has exactly the maps of the preserving pairs, and since `affAct (G, g) = affAct (G, 0) ∘ affAct (1, g)` (`affMul (1, g) (G, 0) = (G, g)`), `K` is also the group generated by the preserving changes of basis and the translations: the paper's "symmetry group generated by changes of basis, translations", without the symmetries inside blocks. Vacuity: `K` contains the identity (`p = (1, 0)`), and every map of a pair is a bijection (`…_bijective`), so `K` is exactly the image, never empty, and a wrong reason (no map a bijection) is excluded.

Verdict of check 5: SAME (for the group of the changes of basis and translations).

### Check 6. Where the group meets the symmetries inside the blocks (by reading, and by the computation above)

```
theorem eq_one_of_affActSkipless_keeps (q) (p)
    (hE : q.1.E.rank = Fintype.card d) (hw : ∀ ℓ, (q.1.write ℓ).rank = Fintype.card d)
    (h1 : (affActSkipless p q).1.E = q.1.E) (h2 : (affActSkipless p q).2.E = q.2.E)
    (h3 : ∀ ℓ, (affActSkipless p q).1.read ℓ = q.1.read ℓ → (affActSkipless p q).2.read ℓ = q.2.read ℓ →
      (affActSkipless p q).1.write ℓ = q.1.write ℓ ∧ (affActSkipless p q).2.write ℓ = q.2.write ℓ) :
    p = (1, 0)
```
and `eq_one_of_affActResidual_keeps` with `hp : ∀ ℓ, p.1 ℓ = p.1 0` in place of `hw`; `…_eq_self_iff`: `affAct p q = q ↔ p = (1, 0)` under the same rank hypotheses (and `hp`).

**The hypotheses as "the map of the pair agrees at `q` with a symmetry inside the blocks".** If `affAct p q = ψ(q)` for a symmetry `ψ` inside the blocks, then `h1`, `h2` say that `ψ` keeps `E` and `b_E`, and `h3` says that `ψ`, at `q`, keeps the write and write bias of every block whose read and read bias it keeps. Against the paper's list (Section 4.1, Appendix A.6 "The symmetries inside the blocks, with their sources", and with biases Appendix B, part (i) for attention):
- rescaling of a ReLU or ReLU² unit (`c_i, β_i ↦ λ c_i, λ β_i`, `a_i ↦ a_i/λ^k`): keeps `E`, `b_E`; keeping the read column `c_i ≠ 0` forces `λ = 1`, so the write row is kept. Gated: values `1/λ` and write `λ`, ReGLU gates `λ` and write `1/λ`: the same, for nonzero columns;
- changes of basis inside a head (`W_Q M`, `W_K M⁻ᵀ`, `W_V N`, `N⁻¹ W_O`, the biases with them): keeping `W_Q, W_V` of rank `d_h` (`d_h ≤ d`) forces `M = N = I`, so `W_O` is kept;
- the value biases moved into the output bias (`b_V + δ`, `b_write − δ W_O`): keeping the read bias forces `δ = 0`; the shifts of the key biases change only the read bias;
- permutations of units or heads and sign flips of tanh units (finite): keeping the read with pairwise distinct (and not opposite) columns forces the identity.

So every symmetry inside the blocks of the paper has the property at generic parameters (nonzero, pairwise non-collinear read columns; heads of full rank); at degenerate ones it can fail (a ReLU unit with read column `0` and read bias `0` contributes `σ(0) a_i = 0`, and its write row `a_i` can be changed with the read kept). This is exactly the condition `hrw` of `finrank_span_symmetryDirs_residual` (a direction inside the blocks with read and read bias of block `ℓ` zero has write and write bias of block `ℓ` zero) for maps: `h3` is its counterpart, as the docstring says. Lean asks of the symmetry only that it keep `E` and `b_E`, not also `D` and `b_D` as `InsideBlocksB` does: a weaker hypothesis, so a stronger statement.

**Truth, by hand** (the map entries of check 4):
- skipless: `h1`: `E G_0 = E` and `rank E = d` give `G_0 = 1`; `h2`: `(b_E + g_0) G_0 = b_E` gives `g_0 = 0`. Induction on `ℓ`: if `G_{ℓ} = 1`, `g_{ℓ} = 0` at the state read by block `ℓ + 1`, its read `G_ℓ⁻¹ W_read = W_read` and read bias `b_read − g_ℓ W_read = b_read` are kept, so by `h3` `W_write G_{ℓ+1} = W_write`, hence `G_{ℓ+1} = 1` by `rank W_write = d`, and `(b_write + g_{ℓ+1}) G_{ℓ+1} = b_write` gives `g_{ℓ+1} = 0`. So `p = (1, 0)`. TRUE (also `L = 0`, `d` empty).
- residual: `hp` and `h1` give all `G_ℓ = 1`; `h2` gives `g_0 = 0`; the induction runs on the partial sums (`S_ℓ = 0` keeps the read bias `b_read − S_ℓ W_read`; `h3` then gives `g_{ℓ+1} = 0` from the write bias) and needs no rank of the writes. TRUE.
- `…_eq_self_iff`: from these and `…_one`. TRUE. This is "act freely" (no element but the identity fixes `q`), stronger than the paper's "act locally freely at `θ`" ("no continuous family of them, other than the identity, fixes `θ`").

**Trying to break them.**
- `E` of lower rank: `E = 0`, any `b_E`, `G_ℓ = 2I` for all `ℓ`, `g_0 = −b_E/2`, other `g_ℓ` arbitrary: `h1` (`0 = 0`), `h2` (`(b_E/2)·2 = b_E`) hold and every read changes (`W_read/2`), so `h3` holds vacuously, and `p ≠ (1, 0)`. `hE` is needed (skipless and residual).
- a write of lower rank without skips (`/home/claude/audit36/affine.py`, last line): `L = 2`, block 1 with `W_write = 0`, `b_write = 0`, the pair `G = (1, G_1, 1)`, `g = 0`, `G_1` random: `E`, `b_E`, the read and read bias of block 1 and its write and write bias are kept (differences `0`), the read of block 2 changes (`4.6`), so `h3` holds, and `p ≠ (1, 0)`. `hw` is needed.
- unequal `G_ℓ` with skips: excluded by `hp`; with `hp`, true by the hand proof. Asking `hp` is right, since the group has only pairs with all `G_ℓ` equal.
No counterexample to the statements as written.

**Is the second sentence of Lemma A.8 stated?** "The symmetry group generated by changes of basis, translations and the symmetries inside blocks therefore has dimension `d_model² + (L + 1) d_model + s`, against `(L + 1)(d_model² + d_model) + s` without skips, and the skips remove `L d_model²` dimensions." With `Symmetry/BiasesAffineGroup.lean` (the sets of preserving pairs, of Hausdorff dimension `d² + (L + 1) d` and `(L + 1)(d² + d)`, difference `L d²`), this file (they form a group of maps; it meets the symmetries inside the blocks that have the property `h3` only in the identity at weights with `rank E = d` (and writes of rank `d` without skips); it acts freely there) and `Symmetry/BiasesSymmetryCount.lean` (the span of the directions of the changes of basis, the translations and a space `V` of directions inside the blocks with `hrw` has dimension `d² + (L + 1) d + dim V`, resp. `(L + 1)(d² + d) + dim V`): what is stated is the group of the changes of basis and translations with its dimension, its trivial meeting with the symmetries inside the blocks, and the dimension with `s` as the dimension of the orbit's tangent directions at one parameter. What is not stated: the group generated together with the symmetries inside the blocks, as a group, and its dimension as a group. Verdict: PART (closer than at the thirty-fifth audit: the group structure is now stated).

The statement that would close it, for the kinds of block the paper names: *define the group `𝒮` of the symmetries inside the blocks as maps (e.g. `(ℝ_{>0})^{hidden units}` acting by rescaling, `GL(d_h)²` per head), and state that `(p, σ) ↦ affAct p ∘ act σ` is an injective (anti-)homomorphism from the preserving pairs `× 𝒮` onto the subgroup of `Equiv.Perm` they generate, so that the generated group is the product, of dimension `d² + (L + 1) d + dim 𝒮` (resp. `(L + 1)(d² + d) + dim 𝒮`), with `dim 𝒮 = s` kind by kind.* For a general block, the paper's sentence has no precise meaning as the dimension of a group: the paper defines `s` only kind by kind, and for an arbitrary block map the symmetries inside it need not form a finite-dimensional Lie group. The precise reading for a general block is the dimension of the span of the directions of the symmetries at a parameter where they act locally freely, which is what `Symmetry/BiasesSymmetryCount.lean` states. I judge that reading sufficient for the paper's purpose (the count enters only the upper bound on the functional dimension), and the PART concerns only the word "group".

### Check 7. Drift checks (by reading, and by compiling a copy)

Signatures printed with `#check` from a copy (`/home/claude/audit36/Sig36.lean`, compiled with `lake env lean` from `/home/claude/lp/lean` at `9e55a6c`, after `pgrep -f "lake build"` printed nothing):
- **Generic = almost every parameter.** The five `ae_` statements are `∀ᵐ θ ∂μ` for every `μ` with `[μ.IsAddHaarMeasure]` on `Params …` (all index types `Fintype`: `T`, `d`, `dIn`, `dOut`, `hid 0`). The copy also applies `ae_flatOn_le_relu_oneBlock_residual_rmsNorm_zero` to `MeasureTheory.Measure.addHaar` with `T = d = dIn = dOut = Fin 2`, one hidden unit, the size hypotheses by `simp`: it compiles.
- **Hypotheses not in the paper.** `[Nonempty T]` (all five): needed, since for `T` empty every direction is flat (outputs with no rows) and the conclusion fails; the paper's inputs are sequences of tokens. `[Nonempty (hid 0)]` (residual): not needed by my reading (check 2), outside the paper's scope (width at least `d ≥ 2`). For the group file: `hE`, `hw` (needed, check 6), `hp` (the group's own pairs), `[Nonempty T] [Nonempty dOut]`, `A.χ = id` for the residual subgroup (needed, check 5; "without normalization" is the lemma's).
- **The paper's hypotheses not in Lean.** Residual statements: width at least `d_model` is not asked (LEAN STRONGER). Skipless: all asked.
- **Degenerate cases.** `d` empty or `d = 1`: excluded by `2 ≤ card d` (the paper's `d_model ≥ 2`). No hidden unit: excluded (skipless by `card d ≤ card (hid 0)`, residual by `Nonempty`). `T` empty: excluded. `L = 0` for the group file: one hidden state, skipless and residual maps agree, `hp` is trivial, the statements hold (check 6 by hand). `d` empty for the group file: `GL` of the empty type is trivial and every statement holds.

Verdict of check 7: nothing drifted.

### Check 8. The index rows, the registrations, the axioms (by reading, and by compiling a copy)

- Row of `OneBlock/RedundancySymmetriesRMSZero.lean` (`STATEMENTS.md` line 1144, `proved`): every sentence is true of the five statements. Two omissions: the residual statements ask no width (the row says "with a hidden unit" but not "of any width", which is where Lean is stronger than the theorem); and "That the directions of these symmetries are flat is in the upper bounds" names no statement (the names are in check 3).
- Row of `Symmetry/BiasesAffineGroupLaw.lean` (line 1092, `proved` at `9e55a6c`, `in work` at `1c6ff30`): true of the statements. "with skips for all `G_ℓ` equal" should say "for all `G_ℓ` of the first pair equal" (the second pair is arbitrary). It could add that the subgroup is also the group generated by the preserving changes of basis and the translations (`affAct (G, g) = affAct (G, 0) ∘ affAct (1, g)`).
- Rows that point to them (lines 1062, 1090, 1091): true. The paragraph on the thirty-fifth reader, part B (lines 393 to 397), says "the group with the symmetries inside the blocks, and the group structure, are not stated": the group structure is now stated; only the group with the symmetries inside the blocks remains. Line 406 ("Not yet compared, written after the thirty-fifth audit began: …") should now point to this report.
- `checks/Axioms.lean` (lines 2270 to 2286) registers the 5 theorems of `OneBlock/RedundancySymmetriesRMSZero.lean` and the 12 public theorems of `Symmetry/BiasesAffineGroupLaw.lean`; `SkipsLean.lean` imports both modules (lines 414, 415).
- Axioms, from a copy (`/home/claude/audit36/Ax36.lean`, `#print axioms` of all 17, at `9e55a6c`): each depends on `[propext, Classical.choice, Quot.sound]` only; no `sorryAx`.

Verdict of check 8: the rows are true; three small corrections (below).

## Part 2: the statements, one by one

| file | name | paper sentence | verdict | note |
|---|---|---|---|---|
| `OneBlock/RedundancySymmetriesRMSZero.lean` | `ae_flatOn_le_relu_oneBlock_skipless_rmsNorm_zero_of_le` | S Theorem B.1 (iv), "The redundancy is then that of the symmetries: besides those inside the block, `GL(d_model)` at `h_0` and `CO(d_model)` at `h_1` without the skip", ReLU | SAME | the inclusion; the converse in the flatness statements (check 3); kernel = span computed |
| | `ae_flatOn_le_reluSq_oneBlock_skipless_rmsNorm_zero_of_le` | the same, ReLU² | SAME | kernel = span computed (`d = 2, 3`) |
| | `ae_flatOn_le_relu_oneBlock_residual_rmsNorm_zero` | "and one `CO(d_model)` with it", ReLU | LEAN STRONGER | any width with one unit (computed at width 1) |
| | `ae_flatOn_le_reluSq_oneBlock_residual_rmsNorm_zero` | the same, ReLU² | LEAN STRONGER | any width |
| | `ae_flatOn_le_reglu_oneBlock_residual_rmsNorm_zero` | the same, ReGLU (values and gates) | LEAN STRONGER | any width (computed at widths 1 and 3) |
| `Symmetry/BiasesAffineGroupLaw.lean` | `affActSkipless`, `affActResidual` | Lemma A.8, the translations then the changes of basis, as maps of the weights and biases | SAME | (the residual map uses the partial sums `S_m`) |
| | `affMul` | "`Aff(d_model)`", the product `(G, g)(G', g') = (G G', g + g' G⁻¹)` | SAME | per hidden state |
| | `affActSkipless_one`, `affActResidual_one` | (the unit of the group) | SAME | |
| | `affActSkipless_affActSkipless` | the composition, without skips | SAME | all pairs |
| | `affActResidual_affActResidual` | the composition, with skips | SAME | `hp` on the first pair, needed (computed) |
| | `affActSkipless_bijective`, `affActResidual_bijective` | (the maps are invertible) | SAME | the residual one for all pairs |
| | `exists_subgroup_affActSkipless` | "The symmetry group generated by changes of basis, translations", without skips | SAME | any network; the group generated, without the symmetries inside blocks |
| | `exists_subgroup_affActResidual` | the same, with skips | SAME | `T`, `d_out` nonempty needed; `χ = id` the lemma's |
| | `eq_one_of_affActSkipless_keeps`, `eq_one_of_affActResidual_keeps` | (the group meets the symmetries inside the blocks only in the identity: the step from the two counts to the sum) | SAME as the step the paper's count needs | `h3` is `hrw` for maps; `hE` and, without skips, `hw` needed |
| | `affActSkipless_eq_self_iff`, `affActResidual_eq_self_iff` | "act locally freely at `θ`" (Appendix A.6), for this group | LEAN STRONGER | freely, not only locally freely |
| (the two files together with `Symmetry/BiasesAffineGroup.lean` and `Symmetry/BiasesSymmetryCount.lean`) | | Lemma A.8, second sentence | PART | the group generated with the symmetries inside the blocks, and its dimension as a group, are not stated; the dimension with `s` is stated as a dimension of directions |

## For the authors of the papers

Nothing in the two files is false, vacuous or drifted.

1. **Theorem B.1 (iv), last sentence, "The redundancy is then that of the symmetries".** It is now stated at almost every parameter for the skipless ReLU and ReLU² block (width at least `d_model`) and the residual ReLU, ReLU² and ReGLU block, and the computations agree: the kernel of the Jacobian on a large batch is exactly the span of the directions of `GL(d_model)` at `h_0`, `CO(d_model)` at `h_1` and the rescalings (skipless), and of one `CO(d_model)` and the rescalings (residual). For the residual network it holds for any width with one hidden unit (computed at width 1); the theorem's "of width at least `d_model`" is needed only for the skipless network.
2. **The sentence's scope.** The sentence follows "with equality for ReLU and ReLU² blocks" and does not say for which blocks it holds. Read literally it covers the skipless ReGLU block too, for which the theorem claims only the bound. In my computations (`d = 2`, widths 2 and 3, two draws each) the skipless ReGLU network also has kernel equal to the span of its symmetries, i.e. it attains the bound. The authors may want to say either "for ReLU and ReLU² blocks" or claim equality for ReGLU too (which would need a proof).
3. **A sample of inputs can miss a thin region.** In one ReLU draw two read columns at `0.6°` from each other made a narrow sector of `h_0` with its own set of active units; 200 inputs missed it and gave a kernel one larger than the symmetries, 3000 found it. This does not affect the paper (it claims nothing of a batch), but it matters for the numerical checks of Appendix E: a rank computed on a sample is a lower bound.
4. **Lemma A.8, "The symmetry group generated by changes of basis, translations and the symmetries inside blocks therefore has dimension …".** The group of the changes of basis and translations is now stated as a group of maps, with the law `(G, g)(G', g') = (G G', g + g' G⁻¹)` per hidden state, its dimension, and its trivial meeting with the symmetries inside the blocks. The trivial meeting needs the hypothesis that a symmetry inside a block that keeps the read and read bias of that block keeps its write and write bias, and, without skips, writes of rank `d_model`. Both hold at generic parameters for every kind of block in the paper but fail at degenerate ones (a unit with zero read column). The paper's proof ("A skip ties only the linear part of `Aff(d_model)`, which gives the counts") assumes them silently. The word "dimension" of a group generated with the symmetries inside the blocks has a precise meaning only kind by kind; for a general block the precise statement is the dimension of the span of the directions at a parameter where the action is locally free, which is what Lean states.

## Corrections for `STATEMENTS.md`

1. Line 1144 (`OneBlock/RedundancySymmetriesRMSZero.lean`): after "for the residual network of one ReLU, ReLU² or ReGLU block with a hidden unit" add "of any width (the theorem asks at least `d`)". Replace "That the directions of these symmetries are flat is in the upper bounds" by "That the directions of these symmetries are flat, at every parameter: `cobDir_single_mem_flat_skipless_rmsNorm_zero_of_rowHomogeneous` (`GL(d)` at `h_0`), `cobDir_mem_flat_skipless_rmsNorm'` and `scaleDir_mem_flat_skipless_rmsNorm_zero` (`CO(d)` at `h_1`), `cobDir_const_mem_flat_residual_rmsNorm_zero`, `scaleDir_const_mem_flat_residual_rmsNorm_zero`, `rescaleDirMlp_mem_flat`, `rescaleDir_mem_flat'`, `rescaleDirGate_mem_flat`; with them the flat directions at the paper's inputs equal the span of the symmetries".
2. Line 1092 (`Symmetry/BiasesAffineGroupLaw.lean`): "with skips for all `G_ℓ` equal" → "with skips when all `G_ℓ` of the first pair are equal (the second pair is arbitrary)". Optionally add: "the subgroup is the group generated by the preserving changes of basis and the translations, since `affAct (G, g) = affAct (G, 0) ∘ affAct (1, g)`".
3. Lines 393 to 397 and 406: the group structure of Lemma A.8 is now stated (`Symmetry/BiasesAffineGroupLaw.lean`); what remains in part is the group generated with the symmetries inside the blocks as a group. Replace the "Not yet compared" sentence of line 406 with a note on this report (`ai_notes/lean-statement-audit-thirtysixth-2026-11-25.md` once copied there): nothing false, vacuous or drifted; part (iv) of S Theorem B.1 stated in full at almost every parameter; the second sentence of S Lemma A.8 still in part (the group with the symmetries inside the blocks).

## What I could not check

- I did not re-read the statements of the files that the rows for parts (i), (iii) and (v) of Theorem B.1 point to. The claim in check 3 that nothing of Theorem B.1 is left unstated rests on the index rows and on the earlier reports.
- The computations are in double precision with complex-step derivatives. Each kernel dimension is read at a gap of at least `7e10`, and the networks are small (`d = 2`, one with `d = 3`; widths 1 to 4; one hidden block). I did not compute in exact arithmetic or at larger `d`.
- I did not prove that `[Nonempty (hid 0)]` can be dropped from the residual statements; check 2 argues it by reading only.
- I did not read the proofs, only the statements and definitions, as the brief asks. The axioms are those of the compiled copy at `9e55a6c`.

Commit read at the end: `27da9a5` (it adds only notes after `9e55a6c`; the two files and their statements are the same as at `1c6ff30`, with the `sorry`s of `Symmetry/BiasesAffineGroupLaw.lean` proved since `9e55a6c`).
