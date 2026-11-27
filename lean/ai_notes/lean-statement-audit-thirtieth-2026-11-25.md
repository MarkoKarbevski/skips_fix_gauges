STATUS: complete

# Thirtieth audit of Lean statements against the papers (25 November 2026)

Subject: S Lemma A.27, fourth value (networks without an embedding and a readout); S Theorem A.28 (i); S Lemma A.30 with inputs in an open set that contains `0`; S Proposition A.1 (iii); D Lemma D.13 with `θ†` written out.

**Result.** Nothing false, nothing vacuous, nothing drifted in the ten files. Every statement at "almost every parameter" is for every Haar measure, and each was compiled at a concrete measure. `funDimBlocks` is the paper's functional dimension without an embedding and a readout, and the values of the fourth line of Lemma A.27 were found in all 107 networks computed (tanh, GELU: `P`; SwiGLU, GeGLU: `P − s`; attention with them: `P − 2 ∑ H d_h²`, with gated units `− ∑ d_hidden`), 20 of them at `d = 1`, outside the hypotheses. The general lemma from the first value to the fourth is true, and its hypotheses `χ = id` and "the directions of `R` are flat" are needed (two counterexamples without them). Theorem A.28 (i) is the paper's statement, given Sard's theorem as a hypothesis, with weaker conditions on the widths; the rank bound for the skipless network holds at every parameter computed. Lemma A.30 with inputs in an open set that contains `0` is the paper's, the step along rays is true for every degree `k`, and the statement gives the functional dimension with inputs in `Ω` (compiled). Proposition A.1 (iii) is stated for the maps of (ii) only (PART). For Lemma D.13 the definitions of `θ†` are the paper's entry by entry; the three statements are weaker than the paper in one point: they say that suitable `μ` exist, where the paper proves the lemma for every `μ` with the stated independence over `ℚ`. The index rows are true of the statements, with small corrections.

The statements and the definitions were read, not the proofs. Each check says how it was done: by reading, by compiling a copy (a file in `/home/claude/audit30/`, with `lake env lean` against the existing build, nothing written there), by a computation (Python, `python3 -I`, scripts in `/home/claude/audit30/`), or by an argument of the reader, written out and checked by nobody else. The papers were read as the text files `skips.txt` and `dim.txt` in `<scratchpad>`.

## Commits and `sorry`

The branch `lean-plus` of `/home/claude/lp` moved during the audit.

- At the start: `135b098`. All ten subject files were read at this commit. Three had `sorry` then: `Residual/DepthRescaleOpen.lean` (5 statements), `Residual/DepthReGLUOpen.lean` (4), `Depth/ThetaDagger.lean` (3).
- During the work the branch went to `5a23c38` and then `6d55f29` (02:46 UTC). These commits added the proofs of the three files. The three files at `135b098` were compared with `6d55f29`: no statement and no definition changed; the only lines removed are the lines `sorry`. The proving commits put `omit … in` lines before some theorems, which drop instance arguments that the statement does not use (for example `smallWritesLimit_eq_zero_of_forall_mem_isOpen_mlp_rescale` no longer asks `[Nonempty T]`, `[DecidableEq d]`, `[Fintype dOut]`). This makes the statements slightly more general and changes nothing else.
- At `6d55f29` none of the ten files contains `sorry` (by `grep`), and all have a build output newer than the source. The compiled checks were run against this build.
- At the end: `33b475e` (03:00 UTC). Between `6d55f29` and `33b475e` none of the ten files changed, and no index row of the ten files changed; the index rows were read at `5a82a4e`. The commits in between add other files (networks with biases), which were not read.

## Part 1: checks

### Check 1. Generic means almost every parameter, for every Haar measure

**By reading.** Every statement with `∀ᵐ` in the ten files has the form `(μ : Measure …) [μ.IsAddHaarMeasure] … : ∀ᵐ β ∂μ, …` with `μ` universally quantified. There are 15 such statements: `ae_funDimBlocks_ge` (`BlocksAloneGeneral.lean`); `ae_funDimBlocks_mlp_residual`, `…_tanh_…`, `…_gelu_…` (`BlocksAloneMlp.lean`); `ae_funDimBlocks_gated_residual`, `…_swiglu_…`, `…_geglu_…` (`BlocksAloneGated.lean`); `ae_funDimBlocks_attentionMlp_residual`, `ae_funDimBlocks_attentionGated_residual` and the four named kinds (`BlocksAloneTransformer.lean`); `ae_forall_evalBlocks_residual_ne_skipless_mlp`, `…_gelu` (`BlocksAloneDifferent.lean`). Three more statements have the quantifier inside, twice each: `exists_isOpen_jacobianRank_smallWrites_relu_of_isOpen`, `…_reluSq_…`, `…_reglu_…` have the clauses `∀ (μ) [μ.IsAddHaarMeasure], ∀ᵐ θ ∂μ, …`. The measure is on the parameters of the blocks (`BlockParams A`) in the files `BlocksAlone*`, and on all parameters `(E, reads, writes, D)` in the two files on Lemma A.30. In `ae_forall_evalBlocks_residual_ne_skipless_*` the measure is on the weights of the residual blocks, and the skipless weights are quantified by `∀ β'` inside: "almost every choice of weights" is of the residual network, and "equals no composition" is for every skipless parameter.

`Fintype`: the index types of the weights are `d`, `hid ℓ`, `H ℓ`, `dh ℓ` and, in the files on Lemma A.30, `dIn`, `dOut`; each has `[Fintype …]` in the `variable` lines. The embedding and the readout of `BlockParams A` are indexed by `PEmpty`, which has a `Fintype` instance.

**By compiling a copy** (`/home/claude/audit30/Check1.lean`, compiled with `lake env lean` against the build of `6d55f29`, no error): each named statement was applied to the concrete measure `Measure.addHaar` and concrete index types: one token, `d = Fin 2`, three blocks with 3, 1 and 0 hidden units (`ae_funDimBlocks_tanh_residual`, `…_gelu_…`, `…_swiglu_…`, `…_geglu_…`, `ae_funDimBlocks_ge`, `ae_forall_evalBlocks_residual_ne_skipless_gelu` with `L + 2 = 3` and Sard's theorem as a hypothesis); two tokens with the causal mask, blocks with 0, 1 and 2 heads of width 1 beside the hidden units (`ae_funDimBlocks_attention_tanh_residual`, `…_gelu_…`, `…_swiglu_…`, `…_geglu_…`); and the clause "`U` contains `θ_τ` for generic `θ`" of `exists_isOpen_jacobianRank_smallWrites_relu_of_isOpen` with `Ω` the unit ball. All compile.

Verdict: generic is "almost every parameter, for every additive Haar measure" in every statement with `∀ᵐ`. No drift.

### Check 2. The fourth value

**(a) Is `funDimBlocks` the paper's functional dimension "without an embedding and a readout"? By reading: yes.**

```lean
abbrev BlockParams (A : Arch T d L) : Type _ := Params A PEmpty.{1} PEmpty.{1}
def BlockParams.toParams {A : Arch T d L} (β : BlockParams A) : Params A d d where
  E := 1
  read := β.read
  write := β.write
  D := 1
def evalBlocks (A : Arch T d L) (S : Fin L → Matrix d d ℝ) (β : BlockParams A)
    (x : Matrix T d ℝ) : Matrix T d ℝ := eval A S β.toParams x
noncomputable def jacobianRankBlocks {n : ℕ} (X : Fin n → Matrix T d ℝ) (β : BlockParams A) : ℕ :=
  Module.finrank ℝ (LinearMap.range
    (fderiv ℝ (fun β' : BlockParams A => fun i : Fin n => evalBlocks A S β' (X i)) β).toLinearMap)
noncomputable def funDimBlocks (β : BlockParams A) : ℕ :=
  sSup {r : ℕ | ∃ (n : ℕ) (X : Fin n → Matrix T d ℝ), r = jacobianRankBlocks A S X β}
```

The parameters are the reads and the writes only (the embedding and the readout of `BlockParams A` are matrices with no rows, respectively no columns). The function is `h_0 = x`, `y = χ(h_L)` (`hidden_toParams_zero`, `evalBlocks_eq`), and `y = h_L` in every statement of the subject, which all take `χ = id`. The derivative is in the reads and the writes, the inputs are all of `ℝ^{T×d}`, and the functional dimension is the largest rank over finite batches: Definition 4.1 for this family. The number of parameters is `∑_ℓ d r_ℓ + ∑_ℓ w_ℓ d` (`finrank_blockParams`): `2 d m` for an MLP block with `m` hidden units, `3 d m` for a gated block, `4 H d d_h` for an attention block, which is the paper's `P = 4 L d²` in Corollary 4.10 (ii) when `H d_h = d`. Verdict: SAME.

**(b) `funDimBlocks_add_finrank_eq_of_funDim_toParams`.**

```lean
theorem funDimBlocks_add_finrank_eq_of_funDim_toParams {A : Arch T d L} (hA : A.χ = id)
    (hf : ∀ ℓ, Differentiable ℝ (A.f ℓ)) (β : BlockParams A)
    (R : Submodule ℝ (BlockParams A))
    (hR : ∀ η ∈ R, blockDir A η ∈ flat A 1 β.toParams)
    (hfd : funDim A 1 β.toParams + (Fintype.card d ^ 2 + Module.finrank ℝ R)
      = Module.finrank ℝ (Params A d d)) :
    funDimBlocks A 1 β + Module.finrank ℝ R = Module.finrank ℝ (BlockParams A)
```

True as stated (by reading, with the argument redone by hand; the file compiles without `sorry` and with the three standard axioms). On a batch that attains `fd(β.toParams)`, the kernel of the Jacobian of the network with `E = D = I` has dimension `d² + dim R`. It contains the `d²` directions `(E Y, −Y W_read, W_write Y, −Y D)` of the one change of basis of the residual network, whose component at `E = I` is `Y`, and the directions of `R`, whose component at `E` is `0`; these are `d² + dim R` independent directions, so they are the whole kernel. A direction of the blocks has component `0` at `E`, so it lies in this kernel only if it lies in `R`. Hence the Jacobian in the reads and the writes has kernel `R` on this batch, and its kernel contains `R` on every batch. This is the paper's sentence "Without an embedding and a readout, `M = I` is fixed, so `ψ_M = 0` for every direction, and the flat directions are the rescalings alone", in a form that serves every kind of block: the paper's `ψ_M = η_E D + E η_D = 0` is here "the component at `E` is `0`".

Are the hypotheses needed?

- `χ = id`: needed. It gives the `d²` flat directions of the change of basis. Under pre-RMSNorm with `ε > 0` only the antisymmetric `Y` are flat, and the statement with `d²` is then false. Computed (`check2_chi.py`, 40 digits, two parameters): one token, `d = 2`, `χ = N_1`, one SwiGLU block with 3 hidden units, `E = D = I`. The Jacobian in all parameters has rank `22 = P − d²` (`P = 26`; this is also `P − d(d−1)/2 − s`, the second value of Lemma A.27, and the rotation and the three rescalings bound the rank by 22 on every batch). So `hfd` holds with `R = 0`, for which `hR` is empty. The conclusion would read `funDimBlocks = P_blocks = 18`; the rank in the reads and the writes is `15 = P_blocks − s`, and the three rescalings bound it by 15 on every batch. So the hypothesis is not decoration; it is "no normalization" of the fourth value.
- `hR` (the directions of `R` are flat): needed for arbitrary differentiable blocks. Example, checked by hand against every clause: one token, `d = 1`, one block with one hidden unit and the activation `σ(z) = z`. The network with an embedding and a readout computes `x E (1 + r w) D`; at `E = D = 1` and `(r, w) ≠ 0` it has `fd = 1` and `P = 4`, so `hfd` holds with `R` the whole space of the blocks (`dim R = 2`), but the conclusion would say `funDimBlocks = 0`, and `x (1 + r w)` has rank `1` in `(r, w)`. Here a direction at `D` cancels a direction of the blocks, which `hR` excludes. For the paper's blocks `hR` is the statement that the rescalings (or the changes of basis inside the heads) are symmetries.
- The value at `β.toParams`: the hypothesis `hfd` is the first value of the lemma at the particular parameter with `E = D = I`. This is the right place: the network without an embedding and a readout is the network with `E = D = I`, and the files that use the lemma get `hfd` from the first value under the conditions of the proof at `E = D = I` (next point). The parameters with `E = D = I` form a set of measure zero among all parameters, so the first value "at generic parameters" would not give it; the statements at generic parameters of the blocks therefore go through one parameter `β₀ = (E W_read, W_write D)` built from a generic `θ₀`, and through analyticity.
- `hf` (differentiable blocks): the lemma is for smooth blocks. ReLU-type blocks are not covered, as in the paper (the fourth value is a line of Lemma A.27 only).

**(c) The conditions "at `E = D = I`".** By reading. `SmallWritesGeneric β.toParams` unfolds to: the rows of every `W_write^ℓ` are nonzero; the columns of all `W_read^ℓ` together are nonzero and pairwise non-collinear (and `rank I = d`, which holds). The paper's proof asks the hypotheses of Lemma B.3 "for the units of all blocks together" with `c_i` the columns of `E W_read` and `a_i` the rows of `W_write D`; without an embedding and a readout these are the columns of the reads and the rows of the writes. So the condition is what the proof asks, neither more nor less. The same holds for `SmallWritesGenericGated β.toParams` (also: no value column vanishes) and for the two parts in `BlocksAloneTransformer.lean` (`SmallWritesGenericAttention β.toParams.sumFst` and `SmallWritesGeneric`/`SmallWritesGenericGated β.toParams.sumSnd`). `β.smallWrites τ` multiplies the writes by `τ` and `(β.smallWrites τ).toParams = (β.toParams).smallWrites τ` by definition, so `β_τ` is the paper's `θ_τ` without `E` and `D`.

By a computation (`check2_point.py`, exact derivatives at 40 digits, two batches each): at a parameter that is not random but satisfies the conditions (`d = 2`, read columns `(1,0), (0,1) | (1,1), (1,−1), (1,2)`, write rows nonzero), the rank at `β_τ` is `P = 20` for tanh and for GELU at `τ = 1/10` and `τ = 1/1000`, and `P − s = 25` of `P = 30` for SwiGLU and GeGLU. The conditions are sufficient and not necessary: with two parallel or two equal read columns in different blocks the rank at `β_τ` is still `20` (the limit `J_0` loses rank there, the Jacobian at `τ ≠ 0` does not).

**(d) The values, by a computation** (`netlib.py`, `check2_values.py`; the networks are written from the Lean definitions; derivatives in the reads and the writes by the complex step at 40 digits, which is exact to the working precision for these entire activations; rank by elimination with complete pivoting; two independent parameters and batches per case; the kept pivots are above `10⁻¹¹` of the largest and the dropped ones below `10⁻²⁵`). All 107 cases give the stated value:

| network (residual, blocks alone) | cases | value found |
|---|---|---|
| tanh blocks and GELU blocks, `d = 2, 3`, widths `[1]`, `[2,3]`, `[1,2,1]`, `[5]`, `[2,4]`, `[3,3]`; two tokens once | 13 | `P` |
| SwiGLU and GeGLU blocks, `d = 2, 3`, widths `[1]`, `[2,2]`, `[1,3]`, `[4]` | 10 | `P − s`, `s` the number of hidden units |
| one attention block and one tanh or GELU block, both orders, causal and full mask, `(d, H, d_h, T)` = `(2,1,1,2)`, `(2,1,2,2)`, `(2,2,1,2)`, `(2,1,1,3)`, `(3,1,2,2)` | 40 | `P − 2 H d_h²` |
| one attention block and one SwiGLU or GeGLU block, both orders, both masks, `(d, H, d_h, T)` = `(2,1,1,2)`, `(2,1,2,2)`, `(2,2,1,2)` | 24 | `P − 2 H d_h² − d_hidden` |
| `d = 1` (outside the hypothesis `d ≥ 2`): tanh, GELU widths `[1]`, `[2]`, `[2,2]`, `[3,1]`; SwiGLU, GeGLU widths `[2]`, `[2,1]`; attention (`H = d_h = 1`, two tokens) with a GELU or a SwiGLU block, both orders, both masks | 20 | the same formulas |

**(e) `d ≥ 2`: needed?** For the route, yes; for the value, the computation says no. At `d = 1` any two read columns are collinear, so the conditions of the proof (`SmallWritesGeneric`) hold only for networks with at most one hidden unit in all, and Lemma B.3 cannot be applied. The values at `d = 1` in the last row of the table are nevertheless the stated ones in all 20 cases. The paper has `d_model ≥ 2` in Lemma A.27, so the Lean hypothesis is the paper's.

**Hypotheses of the statements at generic parameters against Lemma A.27.** `d ≥ 2` (paper: the same); blocks of any widths, in any order (the same; in `BlocksAloneTransformer.lean` a block may also hold heads and hidden units side by side, which is more than the paper says); heads of width `1 ≤ d_h ≤ d` (paper: "at most `d_model`"; a head of width `0` has no parameters); a token that sees itself and another token (paper: "causal or not, on sequences of at least two tokens": both masks are cases); at least one token for MLP and gated blocks; no normalization; no hypothesis on `E`, `D`, which are absent. Verdict for the fourth value: SAME for tanh, GELU, SwiGLU, GeGLU blocks and for attention with them; the pointwise statements under the conditions of the proof are the paper's "for all small `τ ≠ 0`" statement, and the statements at almost every parameter are its consequence for generic parameters (the paper states this consequence in the proof of Theorem A.28: "a network of GELU blocks without an embedding and a readout has functional dimension `P`").

### Check 3. Theorem A.28 (i)

```lean
theorem ae_forall_evalBlocks_residual_ne_skipless_gelu
    (hSard : ∀ r : ℕ, SardCriticalValues
      (BlockParams (Arch.mlp (T := T) (d := d) gelu id hid)) (Fin r → ℝ))
    (μ : Measure (BlockParams (Arch.mlp (T := T) (d := d) gelu id hid))) [μ.IsAddHaarMeasure]
    (hd : 2 ≤ Fintype.card d) (h0 : Nonempty (hid 0)) :
    ∀ᵐ β ∂μ, ∀ β' : BlockParams (Arch.mlp (T := T) (d := d) gelu id hid),
      evalBlocks (Arch.mlp gelu id hid) 1 β ≠ evalBlocks (Arch.mlp gelu id hid) 0 β'
```
with `hid : Fin (L + 2) → Type` and `[Nonempty T]`.

**Clause by clause, by reading.**

| paper | Lean |
|---|---|
| "For GELU blocks" | `Arch.mlp gelu id hid`: MLP blocks with GELU, no normalization, no biases |
| "a composition of `L ≥ 2` residual blocks" | the blocks are indexed by `Fin (L + 2)`; `evalBlocks … 1 β` is `h_0 = x`, `h_ℓ = h_{ℓ−1} + f(h_{ℓ−1} W_read) W_write`, `y = h_L` |
| "almost every choice of weights" | `∀ᵐ β ∂μ` for every Haar measure on the reads and writes of the residual blocks |
| "equals no composition of `L` blocks without skips" | `∀ β'`, the two functions on all of `ℝ^{T×d}` differ; `evalBlocks … 0 β'` has the stream matrix `0` |
| "of the same widths" | the same `hid` in both networks |
| (Scope) `d_model ≥ 2` | `hd` |
| (proof) "every block has at least one hidden unit" | `h0`: the first block only |
| (proof, inside Lemma A.26) "by Sard's theorem" | the hypothesis `hSard` |

The general form `ae_forall_evalBlocks_residual_ne_skipless_mlp` is the same statement for every activation with the conclusion of Lemma B.3 with `s = 0` (`UnitsRigid`, analytic). Verdict: SAME, given Sard's theorem as a hypothesis; LEAN STRONGER in the widths (any widths, one hidden unit in the first block; any number of tokens).

**Which hypotheses are needed?** By reasoning and by a computation (`check3.py`, `check3_L1.py`; 40 digits, as in check 2).

- *At least one hidden unit in the first block* (`h0`): not needed for the claim. If some block has no hidden unit, the skipless network computes the function `0` (its hidden state after that block is `0`, and `GELU(0) = 0`), while the residual network is not the zero function for almost every weight (at one input it is a nonzero analytic function of the weights). Computed: skipless widths `[0,2,2]`, `[2,0,2]`, `[2,2,0]` have rank `0`; residual widths `[0,2,2]`, `[2,0,2]` have rank `P = 16`. The hypothesis is needed only by the route through the rank bound. The Lean hypothesis is weaker than the paper's "every block has at least one hidden unit".
- *`d ≥ 2`*: comes from Lemma A.27 (the conditions of its proof cannot hold for `d = 1`). The computation gives rank `P` for the residual network at `d = 1` (widths `[2,2]`, `[1,1]`, `[3,2,1]`: ranks 8, 4, 12 of 8, 4, 12) and rank `P − 1` for the skipless one (`[2,2]`: 7 of 8; `[1,1]`: 3 of 4), and the bound `P − 1` of the Lean statement holds for `d = 1`. So the claim is very likely true for `d = 1` too, by the same criterion; the Lean statement does not have it, and neither does the paper.
- *Sard's theorem*: a hypothesis taken from the literature, as in the other statements that use Lemma A.26.
- *`L = 1`, which the paper excludes*: the claim is not false there, but the paper's argument cannot give it. Computed: for one GELU block the skipless and the residual network both have rank `P` (`d = 2`, widths `[3]`, `[1]`: 12 and 4; `d = 3`, `[2]`: 12; `d = 1`, `[2]`: 4), so the rank criterion says nothing. A direct argument (of the reader, not the paper's; the two facts it uses were checked numerically) shows that the claim still holds for almost every weight: `GELU(z) = z/2 + e(z)` with `e` even; the functions `x ↦ e(x c)` for columns `c` that are pairwise different up to sign are linearly independent modulo linear functions (ranks 6 of 6, 9 of 9, 9 of 9, 5 of 5 in `check3_L1.py`); so, when every `a_i ≠ 0` and the `c_i` are nonzero and pairwise different up to sign (almost every weight), a skipless block of the same width that equals the residual block `x + ∑_i GELU(x c_i) a_i` has the columns `± c_i` and the same `a_i`, and the linear parts then force `I + ∑_{i ∈ S} c_i a_i = 0` for the set `S` of units with the sign `−`, which fails for almost every weight. On the exceptional set equality does occur: by `GELU(z) − GELU(−z) = z`, the residual block with `W_read = I`, `W_write = −I` (width `d`) is the skipless block with `W_read = −I`, `W_write = −I` (difference `5·10⁻⁴¹` on 20 inputs at 40 digits). Compositions of such blocks give residual networks of any depth that equal skipless networks of the same widths, so "almost every" in the theorem cannot be "every".

**`jacobianRankBlocks_add_one_le_skipless`.**

```lean
theorem jacobianRankBlocks_add_one_le_skipless {A : Arch T d (L + 2)} (hA : A.χ = id)
    (hf : ∀ ℓ, Differentiable ℝ (A.f ℓ)) [Nonempty d] (hr : Nonempty (A.r 0))
    (β : BlockParams A) {n : ℕ} (X : Fin n → Matrix T d ℝ) :
    jacobianRankBlocks A 0 X β + 1 ≤ Module.finrank ℝ (BlockParams A)
```

True at every parameter, by reading: if `W_write^1 ≠ 0`, the direction `(W_write^1, −W_read^2)` of the scalings of `h_1` is nonzero and flat for the skipless network without normalization; if `W_write^1 = 0`, then `h_1 = 0` whatever `W_read^1` is, and any nonzero direction at `W_read^1` is flat (one exists because `d` and the read of block 1 are not empty). By a computation (`check3.py`), for GELU blocks:

| parameter | `d`, widths | `P` | rank |
|---|---|---|---|
| generic (two parameters each) | 2, `[2,3]` | 20 | 16 = `P − (L−1) d²` |
| | 2, `[1,2]` | 12 | 8 |
| | 2, `[3,1]` | 16 | 11 |
| | 2, `[1,1]` | 8 | 5 |
| | 3, `[3,3]` | 36 | 27 = `P − (L−1) d²` |
| | 2, `[2,2,2]` | 24 | 16 = `P − (L−1) d²` |
| | 1, `[2,2]` | 8 | 7 |
| | 1, `[1,1]` | 4 | 3 |
| `W_write^1 = 0` | 2, `[2,3]` | 20 | 4 |
| | 3, `[3,3]` | 36 | 9 |
| | 2, `[2,2,2]` | 24 | 4 |
| | 1, `[2,2]` | 8 | 2 |
| `W_write^1 = 0`, `W_read^2 = 0` | the same four | | 0 |
| `W_read^2 = 0` only | 2, `[2,3]`; 2, `[2,2,2]` | 20; 24 | 4; 4 |

Every rank is at most `P − 1`. The bound is attained only for `d = 1` in these cases; for `d ≥ 2` the scalings are one of `d²` directions of the changes of basis at `h_1`, and the paper's "orbits of positive dimension" asks no more than one.

Hypotheses: `χ = id` (the scaling of `h_1` is a symmetry without normalization); differentiable blocks; `d` not empty (for `d` empty, `P = 0` and the claim `0 + 1 ≤ 0` is false); `Nonempty (A.r 0)`. The last one is sufficient, and some hypothesis of this kind is needed for a general `Arch`: with `A.r 0`, `A.w 0`, `A.r 1` empty, `A.w 1` one row, `f_1` the constant `1`, one token and `d = 1`, the network computes `y = W_write^2`, so `P = 1` and the rank is `1` (by hand, against every clause; not compiled). For MLP blocks "some block has a hidden unit" would be enough, and the paper's "every block has at least one hidden unit" is more than the Lean statement asks.

The paper's sentence is about orbits "at generic parameters" (as Lemma A.26 is stated), and the Lean statement gives the bound at every parameter, which is what the Lean form of Lemma A.26 (i) (`ae_notMem_range_of_rank_lt`) takes. The paper's proof of Lemma A.26 passes from generic parameters to all by lower semicontinuity of the rank; the Lean statement needs no such step. Verdict: SAME as the proof piece; LEAN STRONGER (every parameter, every batch, any differentiable blocks, one hypothesis on the first block).

### Check 4. Lemma A.30 with inputs in an open set that contains `0`

**(a) The step "a direction that is flat on a neighborhood of `0` is flat at every input at which no pre-activation vanishes".**

```lean
theorem smallWritesLimit_eq_zero_of_forall_mem_isOpen_mlp_rescale {k : ℕ}
    (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (hhom : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (θ η : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)
    {Ω : Set (Matrix T dIn ℝ)} (hΩ : IsOpen Ω) (h0 : (0 : Matrix T dIn ℝ) ∈ Ω)
    (hη : ∀ x ∈ Ω, x ∈ noKinkAll θ → smallWritesLimit (Arch.mlp σ id hid) θ η x = 0) :
    ∀ x ∈ noKinkAll θ, smallWritesLimit (Arch.mlp σ id hid) θ η x = 0
```
and `smallWritesLimit_eq_zero_of_forall_mem_isOpen_reglu`, the same for `Arch.gated relu id hid` with `noKinkGateAll θ` (no pre-activation of a gate vanishes).

Recomputed by hand and by a computation (`check4.py`, from the Lean definition of `smallWritesLimit`). With `A(x) = x (η_E D + E η_D)` and `B(x)` the terms of the units, for `c > 0` and an input `x` at which no pre-activation vanishes:

`(J_0 η)(c x) = c · A(x) + c^k · B(x)` for MLP blocks (from `σ(c z) = c^k σ(z)` and `σ'(c z) · c = c^k σ'(z)` at `z ≠ 0`), and `(J_0 η)(c x) = c · A(x) + c² · B(x)` for ReGLU blocks (`relu(c g) (c v) = c² relu(g) v`).

Computed at 40 digits for two tokens, `d_in = 3`, `d = 2`, `d_out = 3`, widths `[2, 3]`, random `θ`, `η`, `x`, and `c = 0.001, 0.37, 1, 5`: the relative defect of the identity is below `2·10⁻⁴⁰` for `k = 0, 1, 2, 3` with `σ = 0` on the negative axis, for `k = 1` with `σ(z) = 0.3 |z|` there, for `k = 2` with `−0.5 z²`, for `k = 0` with the value `2`, and for ReGLU. `A` and `B` are both of size 1 to 25 in these cases, so the identity is not trivial.

The inputs at which no pre-activation vanishes form a cone, and `c x ∈ Ω` for all small `c > 0` because `Ω` is open and contains `0`. So `c A(x) + c^k B(x) = 0` for all small `c > 0`. For `k ≠ 1` two values of `c` give `A(x) = 0` and `B(x) = 0`; for `k = 1` one value gives `A(x) + B(x) = 0`. In both cases `(J_0 η)(x) = A(x) + B(x) = 0`. So the statement is true for every `k : ℕ`, also `k = 0` (a step function, `σ' = 0` off `0`: `c A + B = 0` for all small `c`) and `k = 1` (ReLU, and also `σ(z) = z`).

Is "open and contains `0`" what is needed? What the step uses is that `Ω` is a neighbourhood of `0`. That hypothesis is equivalent in use: the form with `Ω ∈ 𝓝 0` follows from the Lean statement applied to the interior of `Ω` (compiled, `/home/claude/audit30/Check4.lean`). `0 ∈ Ω` cannot be dropped: for one ReLU unit with read column `(1, 0)` (one token, `E = D = I`) and `η` at its write row only, `(J_0 η)(x) = relu(x_1) η_a` vanishes on the open set `{x_1 < 0}` and equals `1` at `x = (1, 0)` (computed). Openness cannot be replaced by `0 ∈ Ω` alone (for `Ω = {0}` the hypothesis is empty when the network has a hidden unit).

Against the paper: the paper's "flat on a neighborhood of `0`" is, for ReLU and ReGLU, vanishing of `J_0 η` at the inputs of the neighbourhood where `J_0` exists; the Lean hypothesis asks it at the inputs of `Ω` at which no (gate) pre-activation vanishes. For ReLU² this is a weaker hypothesis than vanishing on all of `Ω`. Verdict: SAME (LEAN STRONGER in that it holds for every degree `k`, any `θ` and any number of tokens).

**(b) The statements with the batch inside `Ω`.**

`exists_eventually_jacobianRank_smallWrites_mlp_rescale_of_isOpen` (and `…_reglu_of_isOpen`): under `SmallWritesGeneric θ` (ReGLU: `SmallWritesGenericReGLU θ`) there are `n` and `X` with `∀ i, X i ∈ Ω`, `∀ i, X i ∈ noKinkAll θ`, and for all small `τ ≠ 0`: no pre-activation on the batch vanishes at `θ_τ`, and `jacobianRank … X θ_τ + (d² + s) = P`. This is "For all small `τ ≠ 0`, the Jacobian of the residual network at `θ_τ` has rank `P − d² − s` on some finite batch on which no pre-activation vanishes", with the proof's "Fix a finite batch of such inputs, inside the set of inputs". The batch does not depend on `τ` (the paper's sentence allows it to; its proof also fixes it first). It differs from the twin for all inputs (`exists_eventually_jacobianRank_smallWrites_mlp_rescale`, tenth audit) only by the clause `∀ i, X i ∈ Ω`. SAME.

`exists_eventually_eventually_jacobianRank_smallWrites_mlp_rescale_of_isOpen` (and `…_reglu…`): one batch inside `Ω` such that for all small `τ ≠ 0` and every `θ'` near `θ_τ`, no pre-activation on the batch vanishes at `θ'` and the rank on the batch is `P − d² − s`. This is the last paragraph of the proof ("Near such parameters the signs on the batch do not change … So the rank on the batch … is exactly `P − d² − s`"). SAME.

`exists_isOpen_jacobianRank_smallWrites_relu_of_isOpen`, `…_reluSq_…`, `…_reglu_…`: for `d_in, d_out ≥ d ≥ 2` and `Ω` open with `0 ∈ Ω` there is an open set `U` of weights with
1. at every `θ ∈ U`: `funDim … 1 θ + (d² + s) = P`, and a batch inside `Ω` on which no pre-activation vanishes at `θ` and on which the rank is `P − d² − s`;
2. for every Haar measure, for almost every `θ`: `θ_τ ∈ U` for all small `τ ≠ 0`;
3. for every Haar measure, if every block has at least `d` hidden units: for almost every `θ`, `θ ∈ U → funDim … 0 θ + L d² ≤ funDim … 1 θ`.

Against "So the residual network has functional dimension `P − d² − s` on an open set of weights that contains these, and at almost every point of this set the skips add at least `L d²` when every block has width at least `d_model`", with inputs in `Ω`: clause 2 is "that contains these"; clause 1 is the functional dimension; clause 3 is the gain.

*The question of the brief: `funDim` is for all inputs and the batch is inside `Ω`; together, is that the functional dimension with inputs in `Ω`?* Yes (compiled: `/home/claude/audit30/Check4.lean`, no error). With `funDimOn A S θ Ω` the largest rank over the finite batches inside `Ω` (the library's definition in `OneBlock/ResidualRMSZeroGain.lean`), the rank on the batch of clause 1 is at most `funDimOn … 1 θ Ω`, which is at most `funDim … 1 θ`; so for the same `U`:

- at every `θ ∈ U`: `funDimOn (Arch.mlp relu id hid) 1 θ Ω + (d² + s) = P`;
- at almost every `θ`, `θ ∈ U → funDimOn … 0 θ Ω + L d² ≤ funDimOn … 1 θ Ω` (widths at least `d`), because the skipless functional dimension with inputs in `Ω` is at most the one with all inputs.

Both follow from the Lean statement by a few lines (derived for ReLU; the other two statements have the same shape). The paper's functional dimension with inputs in `Ω` takes the Jacobian on batches inside `Ω` on which it exists; on such batches Lean's `jacobianRank` is that Jacobian's rank, and on the other batches Lean's convention (derivative `0` where the output is not differentiable) can only add ranks that the statement bounds as well. So the pair of clauses is the paper's value with inputs in `Ω`, and the bound holds on more batches than the paper's sentence needs. With `Ω` all inputs the statement gives the twin `exists_isOpen_funDim_smallWrites_relu` of the tenth audit (compiled in the same file). Verdict: SAME for ReLU, ReLU², ReGLU; LEAN STRONGER in the tokens (any finite number against one) and in the widths of clauses 1 and 2 (any widths).

Hypotheses against the lemma: no normalization, no biases (the `Arch`); "`E` and `D` have rank `d_model`" is inside the generic conditions, and `d_in, d_out ≥ d` makes them hold almost everywhere; `d ≥ 2` is the paper's Scope. Nothing extra.

### Check 5. Proposition A.1 (iii)

```lean
def Params.cob (θ : Params A dIn dOut) (G K : Fin (L + 1) → GL d ℝ) : Params A dIn dOut where
  E := θ.E * (G 0 : Matrix d d ℝ)
  read ℓ := (↑(K ℓ.castSucc)⁻¹ : Matrix d d ℝ) * θ.read ℓ
  write ℓ := θ.write ℓ * (G ℓ.succ : Matrix d d ℝ)
  D := (↑(K (Fin.last L))⁻¹ : Matrix d d ℝ) * θ.D

theorem cob_comm_of_commute {A : Arch T d L} (θ : Params A dIn dOut)
    (G K G' K' : Fin (L + 1) → GL d ℝ) (hG : ∀ ℓ, Commute (G ℓ) (G' ℓ))
    (hK : ∀ ℓ, Commute (K ℓ) (K' ℓ)) :
    (θ.cob G K).cob G' K' = (θ.cob G' K').cob G K

theorem cob_mulSingle_comm {A : Arch T d L} (θ : Params A dIn dOut) {ℓ ℓ' : Fin (L + 1)}
    (h : ℓ ≠ ℓ') (g k g' k' : GL d ℝ) :
    (θ.cob (Pi.mulSingle ℓ g) (Pi.mulSingle ℓ k)).cob (Pi.mulSingle ℓ' g') (Pi.mulSingle ℓ' k')
      = (θ.cob (Pi.mulSingle ℓ' g') (Pi.mulSingle ℓ' k')).cob
          (Pi.mulSingle ℓ g) (Pi.mulSingle ℓ k)
```

By reading. `θ.cob G K` multiplies the matrices that write `h_ℓ` (the embedding for `ℓ = 0`, the write of block `ℓ` otherwise) by `G_ℓ` on the right, and the matrices that read `h_ℓ` (the read of block `ℓ + 1`, the readout for `ℓ = L`) by `K_ℓ⁻¹` on the left. This is the map of Proposition A.1 (ii), "`W ↦ W G` on the matrices that write a hidden state and `W ↦ G⁻¹ W` on those that read it", with its three cases of normalization as choices of `K`: `K = G` without normalization and for `ε > 0` (then `G` orthogonal); `G = c Q`, `K = Q` for `ε = 0`, where `K⁻¹ W = Q^⊤ W` is "a read through RMSNorm maps to `Q^⊤ W` instead". `Pi.mulSingle ℓ g` is `g` at the hidden state `ℓ` and the identity elsewhere, so `θ.cob (Pi.mulSingle ℓ g) (Pi.mulSingle ℓ k)` is the map of (ii) at the one junction `h_ℓ`. The statement holds for all invertible `g, k, g', k'`, so it covers the three cases at once, and it is an equality of parameters, which is what "the maps commute" says. Both statements are true (two changes of basis compose to the change of basis with the products, hidden state by hidden state: `cob_cob`).

What is not there, and the file and the index say so: the maps of (i) (the identity units of a mixed block) and the pairs of a map of (i) with a map of (ii); in a network of mixed blocks the maps of (ii) also act on the reads `U` and writes `V` of the identity units, which the library's parameters do not have. The second sentence of (iii) ("one copy of `G` per hidden state") is in `Symmetry/CobGroup.lean`, outside the subject.

Verdict: PART of the first sentence of (iii): SAME for two maps of (ii) in a network whose parameters are the embedding, the reads, the writes and the readout (skipless networks; any kind of block).

### Check 6. `θ†` of D Lemma D.13

**The definitions, entry by entry, by reading.**

| paper | Lean (`thetaDaggerGated ιE ιD c μ`; `thetaDaggerMlp` the same without values) |
|---|---|
| `E = [I; 0] ∈ ℝ^{d_in × d}` | `E a i = 1` if `a = ιE i`, else `0` |
| `D = [I  0] ∈ ℝ^{d × d_out}` | `D i b = 1` if `b = ιD i`, else `0` |
| gate column `c_j` = column `j` of `I` for `j ≤ d` | `read ℓ k (Sum.inl j) = [j = c ℓ k]` if `j` is in the image of `c ℓ` |
| `c_j = −μ_{j−d} 𝟙` for `j > d` | `read ℓ k (Sum.inl j) = −μ ℓ j` if `j` is not in the image of `c ℓ` |
| every value column `e_j = 𝟙` (gated blocks only) | `read ℓ k (Sum.inr j) = 1` |
| write row `a_j` = row `j` of `I` for `j ≤ d`, `a_j = 𝟙^⊤` for `j > d` | `write ℓ j k = [j = c ℓ k]` if `j` is in the image of `c ℓ`, else `1` |
| GELU block: `W_g = W_read` | `thetaDaggerMlp`: `read ℓ k j` as the gate column above |
| `ℝ^{1×d}_{>0}`: the rows `n` with `n_i > 0` for every `i` | `posOrthant d = Set.univ.pi fun _ => Set.Ioi 0`; `mem_posOrthant` |

The embeddings `ιE : d ↪ d_in`, `ιD : d ↪ d_out`, `c ℓ : d ↪ hid ℓ` stand for "the first `d_model` coordinates"; with the index types `Fin` and the inclusions of the first `d` indices the matrices are the paper's. The number `μ ℓ j` is attached to the unit `j` itself and may depend on the block; the paper numbers the units outside the first `d` and uses the same `μ_1, μ_2, …` in every block, which is one choice of `μ ℓ j`. The values `μ ℓ j` at the units in the image of `c ℓ` are not used. Definitions: SAME.

**The statements.** `exists_mu_thetaDaggerGated_cols` (`d ≥ 1`), `exists_mu_thetaDaggerGated_outer` (`d ≥ 2`), `exists_mu_thetaDaggerMlp_outer` (`d ≥ 2`) each say: there is `μ` with `0 < μ ℓ j` for all `ℓ, j` such that

- `GoodForConesGated (fun _ => posOrthant d) (fun ℓ => Finset.univ.map (c ℓ)) θ†` (respectively `GoodForConesMlp`): the cones are `C_0 = ⋯ = C_L = ℝ^{1×d}_{>0}`, the active set `A_ℓ` is the image of `c ℓ` (the paper's `{1, …, d_model}`), and (R1), (K1), (K2), "no `a_j` and no `e_j` vanishes" of (K3) hold;
- `frozenGated θ† ℓ (A ℓ) n = (∑ k, n k) • n` for every row `n` (the paper's `g°_ℓ(n) = (n𝟙) n`), respectively `frozenMlp θ† ℓ (A ℓ) n = n`;
- the independence over `ℚ` of (K3): the gate columns of every block (`…_cols`, for SwiGLU), the matrices `c_j c_j^⊤` of every block (`…_outer`, for GeGLU and for GELU).

Every clause of Lemma D.13 is there: the cones, `A_ℓ`, the two formulas for `g°_ℓ`, and all of "good". The one difference is the quantifier on `μ`. The paper fixes `μ` by a property ("`1, μ_1, μ_2, …` are linearly independent over `ℚ`, for SwiGLU blocks, or such that `μ_1², μ_2², …` are, for GELU and GeGLU blocks") and proves the lemma for every such choice. The Lean statements say that suitable `μ` exist and do not say which. (R1), (K1), (K2), the formulas for `g°_ℓ` and the non-vanishing in (K3) hold for every `μ > 0`; only the independence depends on the choice. What the paper uses later is the existence of a good parameter, which the Lean statements give. Verdict: **LEAN WEAKER** in the choice of `μ` (existence; the paper: every choice with the stated independence), SAME in every other clause.

"Linearly independent over `ℚ`": of which numbers, for which blocks? Recomputed by hand. SwiGLU: a relation `∑_j κ_j c_j = 0` reads, in coordinate `k`, `κ_{c k} = ∑_{j outside} κ_j μ_j`; so the gate columns are independent exactly when `1` and the `μ_j` of the block are (for every `d ≥ 1`). GELU and GeGLU, `d ≥ 2`: the entries off the diagonal give `∑_{j outside} κ_j μ_j² = 0`; so the matrices are independent exactly when the `μ_j²` of the block are, without the number `1` (the paper's wording). The numbers are those of one block at a time. For `d = 1` there are no entries off the diagonal and one needs `1` and the `μ_j²` independent: the paper's choice is then not enough (`μ_1² = 2`: `2 · 1 − 1 · μ_1² = 0`), and the paper's proof says "which exist because `d_model ≥ 2`". The Lean hypotheses `d ≥ 1` (SwiGLU) and `d ≥ 2` (GELU, GeGLU) are the paper's. Since the Lean statements only assert existence, `d ≥ 2` could be `d ≥ 1` in the two `…_outer` statements; this is not a defect.

**By a computation** (`check6.py`): `θ†` built from the Lean definitions for six sizes, each for gated and for MLP blocks: `(d, d_in, d_out, q)` = `(2,3,4,2)`, `(2,2,2,4)` (the paper's layout), `(2,3,3,5)`, `(3,4,3,3)`, `(3,5,4,6)`, `(1,2,1,3)`, with embeddings that are not the inclusions of the first indices, and `μ_j = √2, √3, √5, …`. In all 12 cases: `E`, `D` and the write have rank `d` (exact); on 200 rows of the positive orthant every gate in the image of `c` is positive and every other gate is negative (K1); the frozen block computed from `frozenGated`/`frozenMlp` equals `(n𝟙) n`, respectively `n`, with defect `0` at 40 digits, also at 50 rows outside the orthant; its values on the orthant lie in the orthant, and for gated blocks the determinant of its derivative is `2 (n𝟙)^d` (K2); no write row vanishes (K3). For the independence: no integer relation with coefficients up to `10⁶` among `1, √2, √3, √5`; the choice `μ = (√2, 1 + √2)` has the relation `1 + μ_1 − μ_2 = 0`, which is a relation `e_1 + e_2 − c_3 + c_4 = 0` between gate columns for `d = 2`, so not every `μ > 0` will do; `μ² = (2, √2)` has no relation, although `1, 2` do; for `d = 1` and `μ_1² = 2` the two `1 × 1` matrices are dependent.

### Check 7. The index rows, the registrations, the axioms

**Axioms, by compiling a copy** (`/home/claude/audit30/Axioms30.lean`, against the build of `6d55f29`): `#print axioms` of the 40 public theorems and the 4 public definitions of the ten files. All 44 depend on `propext`, `Classical.choice`, `Quot.sound` and on nothing else; no `sorryAx`.

**Registrations, by `grep`** in `checks/Axioms.lean` at `6d55f29`: each of the 40 public theorems of the ten files is registered exactly once. The four definitions `blockDir`, `posOrthant`, `thetaDaggerGated`, `thetaDaggerMlp` are not registered; other definitions of the library (for example `funDimBlocks`, `noKinkAll`, `frozenGated`) are not registered either, so this follows the convention of the file. Each of the 44 names is in a row of `STATEMENTS.md`.

**The rows, by reading** (`STATEMENTS.md` at `5a82a4e`; the ten files did not change after `6d55f29`). Every row names the right file, lists all public names of its file, and has the status "proved", which is true at `6d55f29`. Sentence by sentence:

| row of | true of the statements? |
|---|---|
| `Residual/BlocksAloneGeneral.lean` | Yes. Two imprecisions: the title says "without normalization", but `ae_funDimBlocks_ge` and `analyticOnNhd_evalBlocks_batch` are for any real-analytic `χ`, and the chain rule and the kernel lemma are for any `χ` (they ask that the outputs be differentiable in the parameters at `β.toParams`, which the row does not say); only `jacobianRankBlocks_add_finrank_le` and the main lemma ask `χ = id`. |
| `Residual/BlocksAloneMlp.lean` | Yes, with one correction: `d ≥ 2` is a hypothesis of the three statements at almost every parameter only. `eventually_funDimBlocks_smallWrites_mlp` does not ask it (its condition `SmallWritesGeneric β.toParams` cannot hold for `d = 1` with two hidden units). |
| `Residual/BlocksAloneGated.lean` | Yes, with the same correction for `eventually_funDimBlocks_smallWrites_gated`. |
| `Residual/BlocksAloneTransformer.lean` | Yes, with the same correction for the two `eventually_…` statements. A block may hold heads and hidden units side by side, which the row could say (the paper has one or the other). |
| `Residual/BlocksAloneSkipless.lean` | Yes, all of it, including "The paper's sentence is on orbits at generic parameters; Lemma A.26 is applied with the bound at every parameter". |
| `Residual/BlocksAloneDifferent.lean` | Yes. "For every activation under `UnitsRigid`" leaves out that the activation is also real-analytic (a hypothesis of the general statement). |
| `Residual/DepthRescaleOpen.lean` | Yes. The two statements with a batch also assume the conclusion of Lemma B.3 for the activation (`UnitsRescale`), which the row does not name (the row of the twin `Residual/DepthRescale.lean` does not either). |
| `Residual/DepthReGLUOpen.lean` | Yes. |
| `Symmetry/JunctionsCommute.lean` | Yes, including what is not stated (the maps of (i)). |
| `Depth/ThetaDagger.lean` | Yes: the row says "there are numbers `μ > 0` such that", which is the existence form of the statements. |

The paragraph of the index that lists the ten files as "Not yet compared by such a reader" is to be updated (see the corrections).

## Part 2: the statements, file by file

Verdict words: SAME, LEAN STRONGER, LEAN WEAKER, DIFFERENT, PART, FALSE. "aux." marks a statement that the paper does not write and that the other statements use; for these the verdict says whether the statement is true as stated.

| file | statement | paper sentence | verdict | note |
|---|---|---|---|---|
| `Residual/BlocksAloneGeneral.lean` | `blockDir` (def) | none (aux.) | fine | `η ↦ (0, η_read, η_write, 0)`, the linear part of `β ↦ β.toParams` |
| | `hasFDerivAt_evalBlocks_batch` | none (aux.; written by a proving agent) | true | States: if the outputs of the network on a batch are differentiable in the parameters at `β.toParams`, the family `β' ↦ (F_{β'}(x_i))_i` has at `β` the derivative of these outputs composed with `blockDir`. True: `β' ↦ β'.toParams` is affine with linear part `blockDir` (chain rule). Any stream matrices, any `χ` |
| | `mem_ker_fderiv_evalBlocks_of_mem_flat` | none (aux.; proving agent) | true | States: if the outputs are differentiable in the parameters at `β.toParams` for every input and `blockDir η` is flat for the network there, then `η` is in the kernel of the Jacobian of the family on every batch. True by the previous statement |
| | `jacobianRankBlocks_add_finrank_le` | S Lemma A.27, proof, "The rank": "Conversely `rank J_τ ≤ P − m` on every batch, since the symmetries … move `θ_τ` in `m` independent directions", for the blocks alone (proving agent) | SAME; true | States: `χ = id`, differentiable blocks, `R` a space of directions of the blocks with `blockDir η` flat at `β.toParams`: rank on every batch `+ dim R ≤ P_blocks`. True by rank and nullity. Any stream matrices |
| | `funDimBlocks_add_finrank_eq_of_funDim_toParams` | S Lemma A.27, proof: "Without an embedding and a readout, `M = I` is fixed, so `ψ_M = 0` for every direction, and the flat directions are the rescalings alone, of dimension `s`"; for attention: "and of dimension `s` without an embedding and a readout" | SAME in content; LEAN STRONGER (any differentiable blocks) | true; the route is from the first value at `E = D = I`, not from `J_0` again; `χ = id` and `hR` are needed (check 2 (b)) |
| | `analyticOnNhd_evalBlocks_batch` | none (aux.; proving agent) | true | States: for real-analytic blocks and `χ` the family on a batch is real-analytic in the reads and writes (any stream matrices). True: composition of the analytic outputs with an affine map |
| | `ae_funDimBlocks_ge` | the step from one parameter to generic parameters (as Theorem 4.7 from Lemma A.27) | true; for every Haar measure | real-analytic blocks and `χ`, any stream matrices |
| `Residual/BlocksAloneMlp.lean` | `eventually_funDimBlocks_smallWrites_mlp` | S Lemma A.27, fourth value, "`fd(θ_τ) = P − s` (no embedding, readout, biases or normalization)", `s = 0` | SAME | under the conditions of the proof at `E = D = I`; no hypothesis on `d` |
| | `ae_funDimBlocks_mlp_residual`, `…_tanh_…`, `…_gelu_…` | proof of S Theorem A.28: "a network of GELU blocks without an embedding and a readout has functional dimension `P`" | SAME; LEAN STRONGER (almost every parameter; the paper needs one) | `d ≥ 2` as in the lemma; the value holds at `d = 1` in the cases computed |
| `Residual/BlocksAloneGated.lean` | `eventually_funDimBlocks_smallWrites_gated` | S Lemma A.27, fourth value, SwiGLU and GeGLU, `s` = number of hidden units | SAME | |
| | `ae_funDimBlocks_gated_residual`, `…_swiglu_…`, `…_geglu_…` | the same at generic parameters | SAME | |
| `Residual/BlocksAloneTransformer.lean` | `eventually_funDimBlocks_smallWrites_attentionMlp`, `…_attentionGated` | S Lemma A.27, fourth value, "each block, in any order and of any width, … an attention block … or an MLP block" | SAME; LEAN STRONGER (a block may hold heads and hidden units) | `s = 2 ∑ H d_h²`, with gated units `+ ∑ d_hidden` |
| | `ae_funDimBlocks_attentionMlp_residual`, `ae_funDimBlocks_attentionGated_residual`, `ae_funDimBlocks_attention_tanh_residual`, `…_gelu_…`, `…_swiglu_…`, `…_geglu_…` | the same at generic parameters | SAME | heads of width `1 ≤ d_h ≤ d`; `hdh0` is also asked of blocks without heads, where any nonempty type serves |
| `Residual/BlocksAloneSkipless.lean` | `jacobianRankBlocks_add_one_le_skipless` | proof of S Theorem A.28 (i): "for `L ≥ 2` the changes of basis at `h_1` have orbits of positive dimension, since every block has at least one hidden unit" | SAME; LEAN STRONGER (every parameter, any differentiable blocks, a hypothesis on the first block only) | true at every parameter (check 3) |
| `Residual/BlocksAloneDifferent.lean` | `ae_forall_evalBlocks_residual_ne_skipless_mlp` | S Theorem A.28 (i), for every analytic activation with the conclusion of Lemma B.3 with `s = 0` | LEAN STRONGER, given Sard's theorem | |
| | `ae_forall_evalBlocks_residual_ne_skipless_gelu` | S Theorem A.28 (i) | SAME, given Sard's theorem as a hypothesis | `d ≥ 2` (Scope); one hidden unit in the first block (not needed for the claim) |
| `Residual/DepthRescaleOpen.lean` | `smallWritesLimit_eq_zero_of_forall_mem_isOpen_mlp_rescale` | S Lemma A.30, proof: "So a direction that is flat on a neighborhood of `0` is flat at every input at which no pre-activation vanishes" | SAME | true for every `k : ℕ`; needs only a neighbourhood of `0` |
| | `exists_eventually_jacobianRank_smallWrites_mlp_rescale_of_isOpen` | S Lemma A.30, first sentence, with "Fix a finite batch of such inputs, inside the set of inputs" | SAME | the batch does not depend on `τ` |
| | `exists_eventually_eventually_jacobianRank_smallWrites_mlp_rescale_of_isOpen` | S Lemma A.30, proof, last paragraph ("Near such parameters …") | SAME | |
| | `exists_isOpen_jacobianRank_smallWrites_relu_of_isOpen`, `…_reluSq_…` | S Lemma A.30, second sentence, with inputs in an open set that contains `0` | SAME | gives the functional dimension with inputs in `Ω` and the gain for it (compiled, check 4) |
| `Residual/DepthReGLUOpen.lean` | `smallWritesLimit_eq_zero_of_forall_mem_isOpen_reglu` | the same step for ReGLU | SAME | degree 2 in gate and value together |
| | `exists_eventually_jacobianRank_smallWrites_reglu_of_isOpen`, `exists_eventually_eventually_jacobianRank_smallWrites_reglu_of_isOpen`, `exists_isOpen_jacobianRank_smallWrites_reglu_of_isOpen` | S Lemma A.30 for ReGLU with inputs in an open set that contains `0` | SAME | `s = 2 ∑ d_hidden` |
| `Symmetry/JunctionsCommute.lean` | `cob_comm_of_commute` | none (aux.) | true | two changes of basis commute when their matrices commute at every hidden state |
| | `cob_mulSingle_comm` | S Proposition A.1 (iii): "The maps of (i) and (ii) commute when they act at different junctions" | PART | SAME for two maps of (ii); the maps of (i) are not in the library |
| `Depth/ThetaDagger.lean` | `posOrthant` (def), `mem_posOrthant` | D: "the positive orthant, the set of the rows `n` with `n_i > 0` for every `i`" | SAME | |
| | `thetaDaggerGated`, `thetaDaggerMlp` (defs) | D: "The parameters `θ†`" | SAME | entry by entry (check 6); embeddings for "the first `d_model` coordinates"; `μ` may depend on the block |
| | `exists_mu_thetaDaggerGated_cols` | D Lemma D.13 for SwiGLU blocks, with the choice "`1, μ_1, μ_2, …` linearly independent over `ℚ`" | LEAN WEAKER in `μ` (existence), SAME otherwise | `d ≥ 1` |
| | `exists_mu_thetaDaggerGated_outer`, `exists_mu_thetaDaggerMlp_outer` | D Lemma D.13 for GeGLU and for GELU blocks, with the choice "`μ_1², μ_2², …` are" | LEAN WEAKER in `μ` (existence), SAME otherwise | `d ≥ 2` as in the paper's proof; for the existence form `d ≥ 1` would do |

## What the authors of the papers should know

Nothing in the ten files is false, vacuous or drifted. Where the Lean statements and the papers differ, the Lean statement is stronger, except for Lemma D.13 (the choice of `μ`) and Proposition A.1 (iii) (part).

Places where a statement or a proof of the papers needs a condition or a step that it does not write, or could say more:

1. **S Theorem A.28 (i): "almost every" cannot be "every", and `L = 1` is not a counterexample.** By `GELU(z) − GELU(−z) = z`, the residual block `x ↦ x − GELU(x)` (entrywise; `W_read = I`, `W_write = −I`) is the skipless block `x ↦ −GELU(−x)` of the same width (checked at 40 digits). So residual networks of GELU blocks of width `d_model` of any depth equal skipless networks of the same widths on a set of weights of measure zero. For `L = 1` the paper's rank argument cannot apply (both networks have functional dimension `P`, computed), but the claim "for almost every weight, no skipless block of the same width" still holds by the even part of GELU (an argument of the reader, check 3; not formalized). The theorem excludes `L = 1` because of its proof, not because the claim fails.
2. **S Theorem A.28 (i), "since every block has at least one hidden unit":** the condition is not needed for the claim (a skipless network with a block without hidden units computes `0`), and the Lean proof needs it of the first block only. Neither the theorem nor Lemma A.26 says it; the Scope implies it.
3. **S Theorem A.28 (i) and S Lemma A.27, fourth value, at `d_model = 1`:** the proof of the lemma cannot work there (two read columns are always collinear), but the values of the fourth line hold in all 20 cases computed at `d = 1` (tanh, GELU, SwiGLU, GeGLU, attention with them), and the residual rank `P` against the skipless bound `P − 1` gives part (i) of the theorem there too. This is a computation, not a proof.
4. **S Lemma A.27, fourth value: the generic conditions are on the reads and the writes themselves.** Without an embedding and a readout, "the hypotheses of Lemma B.3 hold for the units of all blocks together" is about the columns of the reads and the rows of the writes. The parameters with `E = D = I` have measure zero among all parameters, so the fourth value at generic reads and writes is not the first value "at generic parameters" with `E = D = I` put in. The paper's proof is right (it fixes `M = I` in the same argument); the Lean proof goes through a parameter `(E W_read, W_write D)` built from a generic one. Nothing to change.
5. **S Lemma A.30, "an open set that contains `0`":** the hypothesis is the right one. A neighbourhood of `0` is what the step uses, and `0` cannot be dropped: a direction at the write of one ReLU unit is flat on the open half space where the unit is off and not flat elsewhere (computed). Along a ray, `(J_0 η)(c x) = c · x ψ_M + c^k · (terms of the units)` for `c > 0`, which is the paper's "polynomial on each cone" read on one ray; in this form the step also holds for positively homogeneous activations that are not polynomial on the half lines.
6. **D Lemma D.13: the choice of `μ` for GELU and GeGLU blocks ("`μ_1², μ_2², …` are" independent over `ℚ`) is right for `d_model ≥ 2` only**, as the proof says ("which exist because `d_model ≥ 2`"); for `d_model = 1` one would need `1, μ_1², μ_2², …` (example `μ_1² = 2`). The sentence that chooses the `μ` does not name `d_model ≥ 2`; the surrounding results assume it.
7. **S Proposition A.1 (iii)** is formalized for two changes of basis at hidden states only. The maps of (i) and the networks of mixed blocks are not in the library.

## Corrections for `STATEMENTS.md`

1. The paragraph "Not yet compared by such a reader (they go to the thirtieth audit, …)": the ten files `Residual/BlocksAloneGeneral.lean`, `Residual/BlocksAloneMlp.lean`, `Residual/BlocksAloneGated.lean`, `Residual/BlocksAloneTransformer.lean`, `Residual/BlocksAloneSkipless.lean`, `Residual/BlocksAloneDifferent.lean`, `Residual/DepthRescaleOpen.lean`, `Residual/DepthReGLUOpen.lean`, `Symmetry/JunctionsCommute.lean`, `Depth/ThetaDagger.lean` were compared by the thirtieth audit (report `lean-statement-audit-thirtieth-2026-11-25.md`): nothing false, vacuous or drifted.
2. Rows of `Residual/BlocksAloneMlp.lean`, `Residual/BlocksAloneGated.lean`, `Residual/BlocksAloneTransformer.lean`: say that `d ≥ 2` is a hypothesis of the statements at almost every parameter only; the statements under the conditions of the proof (`eventually_funDimBlocks_smallWrites_…`) do not ask it.
3. Row of `Residual/BlocksAloneGeneral.lean`: `ae_funDimBlocks_ge` and `analyticOnNhd_evalBlocks_batch` are for any real-analytic `χ`; the chain rule and the kernel lemma are for any `χ` and ask that the outputs be differentiable in the parameters at `β.toParams`; `jacobianRankBlocks_add_finrank_le` and the main lemma ask `χ = id`. Add: without `χ = id` the main lemma is false (pre-RMSNorm, `ε = 1`, `d = 2`, one SwiGLU block of 3 hidden units: ranks 22 of 26 and 15 of 18), and without `hR` it is false for a linear activation.
4. Row of `Residual/BlocksAloneTransformer.lean`: a block may hold heads and hidden units side by side.
5. Row of `Residual/BlocksAloneDifferent.lean`: "for every real-analytic activation under `UnitsRigid`". One may add: the hypothesis on the first block is not needed for the claim; the claim also holds for `L = 1` for almost every weight by another argument, and fails on a set of measure zero for every `L`.
6. Row of `Residual/DepthRescaleOpen.lean`: the two statements with a batch assume `UnitsRescale` (the conclusion of Lemma B.3 for the activation). One may add: the pair "`funDim` on `U`" and "a batch inside `Ω`" gives the functional dimension with inputs in `Ω` (`funDimOn … Ω`) and the gain for it.
7. Row of `Depth/ThetaDagger.lean`: one may add that the statements are weaker than the paper in the choice of `μ` (existence against "every choice with the independence"), and that (R1), (K1), (K2), the formulas for `g°_ℓ` and the non-vanishing of (K3) hold for every `μ > 0`.
8. Row of `Symmetry/JunctionsCommute.lean`: no correction.

## What could not be checked

- The proofs were not read. The library was not built by the reader; single files were compiled against the existing build (`Check1.lean`, `Axioms30.lean`, `Check4.lean`).
- A rank computed on a batch is a lower bound for a functional dimension. The values of check 2 (d) agree with the Lean theorems where these apply (`d ≥ 2`); at `d = 1` they are computations only, with two parameters and two batches per case, and they prove nothing about every case.
- The argument for `L = 1` in check 3 and the example of a general `Arch` without a column in the read of block 1 are arguments of the reader, checked by nobody else; the first uses two facts that were checked numerically, the second was checked by hand against every clause and not compiled.
- Sard's theorem is a hypothesis of the two statements of `Residual/BlocksAloneDifferent.lean` (`SardCriticalValues`, `Literature/Sard.lean`); it was not looked at again.
- The conditions and hypotheses that the statements take from earlier files (`UnitsRigid`, `GatedUnitsRescale`, `UnitsRescale`, `SmallWritesGeneric`, `SmallWritesGenericGated`, `SmallWritesGenericAttention`, `SmallWritesGenericReGLU`, and the first value of Lemma A.27 in `Residual/DepthMlp.lean`, `DepthGated.lean`, `DepthTransformer.lean`, `DepthTransformerGated.lean`) were compared by earlier audits and not again; here only their use at `E = D = I` was read.
- The derivation of the functional dimension with inputs in `Ω` (check 4) was compiled for ReLU; ReLU² and ReGLU have statements of the same shape and were read only.
- Whether the fourth value holds for attention blocks on one token was not looked at (the paper and the Lean statements ask two tokens).
- For Proposition A.1 (iii) nothing could be compared for the maps of (i): the library has no mixed blocks.
- The branch moved during the audit (see "Commits"); files written after the audit began (`Network/Biases.lean` and others) were not read.
