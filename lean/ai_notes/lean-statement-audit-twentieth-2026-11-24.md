STATUS: complete

# Twentieth audit of Lean statements against the papers: one block with `ε = 0`, part (iv) of S Theorem B.1 (the two upper bounds); the value of part (v) for the residual network (24 November 2026)

Reader: an independent reader who did not write the statements. Brief:
`audit20_brief_2026-11-24.md`. I audited statements and definitions, not proofs. I changed no
repository file, ran no `lake build`, made no commit and no push. My files are in
`/home/claude/audit20/`.

Library: `/home/claude/lw/lean` (branch `lean-wip`).

- **Commit read: `d12a43b19e0241a3a74424c016acf5c32b67a2c3` (24 November 2026, 20:14:54 UTC),**
  the head when I started (20:15 UTC). The branch moved while I worked. At
  `490f0169d550dbb8a8b6c7ae96eac86b305356d9` (20:23:36) one of the four files,
  `OneBlock/SkiplessHomogeneousRMSZero.lean`, has other proofs (commit `cd811de`: the flat
  direction at `h_0` is now proved from `eval_cobAt_rmsNorm_zero_of_rowHomogeneous`, and the
  private copy of Lemma A.3 (i) is gone); its header, its `variable` lines and its five public
  statements are unchanged, and the other three files are identical (by `git diff`, and by
  compiling the signatures against both builds: the two outputs are the same file). At
  **`a23c3884c621fe0361f0d3a14876e9e3f3c05ec8` (20:53:42), the head when I finished,** the four
  files and every file of definitions that I read are as at `490f016` (`git diff` is empty for
  them); the four index rows have the same text and are lines 860, 861, 862 and 864.
- **Files with `sorry`:** none at `d12a43b` and none at `490f016` (no file under `SkipsLean/`
  contains the word). At `a23c388` three files, all written after I started, none of this audit
  and none imported by the four files: `Dimension/UpperBoundHomogeneousRMSNormZero.lean`,
  `OneBlock/ResidualRMSZeroRescale.lean`, `OneBlock/ResidualRMSZeroRescaleGeneric.lean`.
- The four files have 17 public theorems (5 + 3 + 7 + 2) and no public definition. All 17 depend
  on `propext`, `Classical.choice`, `Quot.sound` only (by compiling `Sig.lean`, output `Sig.out`,
  against the build of `/home/claude/lp/lean`, at `d12a43b`, at `490f016` and at `a23c388`; its
  `SkipsLean/` was the same as that of `/home/claude/lw` each time, by `diff -rq`, and the
  compiled files of the four modules were newer than their sources; the three outputs are the
  same file).

Papers, as text: the skips paper ("S", `<scratchpad>/skips.txt`); the dimension paper
(`<scratchpad>/dim.txt`) is not cited by the four files. Line numbers of `STATEMENTS.md` are
those of `d12a43b`: the rows of the four files are lines 851 to 854 there (860, 861, 862 and 864
at `a23c388`).

**Short answer. Nothing false, nothing vacuous and nothing drifted was found.** The 17 statements
are the paper's, or the paper's with fewer hypotheses, with two exceptions of form that the files
and the index name themselves: for the residual network of part (iv) Lean has the half "at most"
of the paper's value, and for the skipless network it has the bound without the paper's "with
equality for ReLU and ReLU² blocks". In 180 computed cases inside the Scope of Theorem B.1 (iv)
the rank on the batch was equal to the bound every time, for the three kinds of block and both
networks; no batch of 261 cases had a rank above a bound. Two sentences of the index are less
plain than they could be (the two notions of functional dimension side by side; "at any depth"
against the one block of the theorem); corrections are at the end.

How I checked.

- "By reading": every public statement and docstring of the four files and their headers; the
  definitions they use (`Arch`, `Params`, `hidden`, `eval`, `evalBatch`, `jacobianRank`, `funDim`,
  `flat`, `flatOn`, `funDimOn`, `rmsRow`, `rmsNorm`, `Arch.mlp`, `Arch.gated`, `relu`, `reluSq`,
  `cobDir`, `scaleDir`, `rescaleDirMlp`, `rescaleDir`, `rescaleDirGate`, `RowHomogeneous`,
  `blockFlatSphere`, `residualZeroDomain`); the statements of the library lemmas that the `ae_`
  statements rest on (`ae_rank_E_write`, `ae_isUnit_det_submatrix`, `ae_read_col_ne_zero`,
  `ae_value_ne_zero`, `ae_gate_ne_zero`); and the paper passages that the brief names (S lines
  2319 to 2385, 2862 to 3010, Lemma A.3 with its proof, Theorem 4.2, Theorem A.17, Lemma A.18,
  Appendix A.6 and the end of the proof of part (i) for the number `s`).
- "By hand": a short argument of my own, written where it is used.
- "By compiling": scratch files in `/home/claude/audit20/`, compiled with `lake env lean <file>`
  from `/home/claude/lp/lean` (nothing written there): `Sig.lean` (the full signatures of the 17
  theorems, with every instance argument, and their axioms), `Chk.lean` (checks 1, 2 and 5),
  `Chk2.lean` (checks 2 and 7). All compile without error and without `sorry` (`*.out`; the
  last time against the build at `a23c388`); every theorem of mine that I name below has the
  three standard axioms.
- "By a computation": my own scripts (I did not run the coordinator's script; I read its output).
  `z20core.py`, `z20run.py`, `z20sum.py`: networks of ReLU, ReLU² and ReGLU blocks under
  pre-RMSNorm with `ε = 0`, mpmath with 60 digits, exact derivatives in the weights by forward
  mode (dual numbers), checked against central differences in `z20fd.py` (they agree to
  `3.5·10⁻³⁸`, the error of the differences); the rank by elimination with complete pivoting, and
  again from the singular values in double precision. One token per input: these blocks act on
  every token alone, so the Jacobian at an input of `T` tokens is the stack of the Jacobians at
  its rows. A rank on a batch is a lower bound of the functional dimension.

---------------------------------------------------------------------------------------------------

## Part 1: the drift checks

### Check 1. Generic means almost every parameter, for every Haar measure

**Verdict: yes, in all eight `ae_` statements; every index type of the weights is finite; the
statements apply to a concrete Haar measure.** (By reading; the shapes from the compiled
signatures, `Sig.out`; the measure space and eight instances by compiling, `Chk.lean`.)

- The `variable` lines:

  ```
  -- OneBlock/SkiplessHomogeneousRMSZero.lean and OneBlock/SkiplessHomogeneousGatedRMSZero.lean
  variable {T d dIn dOut : Type*} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
    [Fintype dOut]
  variable {σ : ℝ → ℝ} {hid : Fin 1 → Type} [∀ ℓ, Fintype (hid ℓ)]
  -- Residual/UpperBoundRescaleRMSNormZero.lean
  variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
    [Fintype dOut]
  variable {σ : ℝ → ℝ} {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]
  ```
  The weights are `E : Matrix dIn d ℝ`, `read ℓ : Matrix d (r ℓ) ℝ`, `write ℓ : Matrix (w ℓ) d ℝ`,
  `D : Matrix d dOut ℝ`, with `r ℓ = w ℓ = hid ℓ` (MLP) and `r ℓ = hid ℓ ⊕ hid ℓ`, `w ℓ = hid ℓ`
  (gated). Every one of these index types has `Fintype`, so the space of the weights is
  finite-dimensional.
- Each of the eight statements has `μ` as a variable of the statement with
  `[μ.IsAddHaarMeasure]`, and `∀ᵐ θ ∂μ`. None is "there is a parameter" or "on an open set". For
  instance:

  ```
  theorem ae_funDim_add_le_skipless_relu_oneBlock_rmsNorm_zero [Nonempty d]
      (μ : Measure (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut))
      [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
      (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
      ∀ᵐ θ ∂μ, funDim (Arch.mlp relu (rmsNorm 0) hid) 0 θ
          + (Fintype.card d ^ 2 + (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
            + Fintype.card (hid 0))
        ≤ Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut)
  ```
- By compiling (`Chk.lean`): the space `Params …` of a ReLU block and of a ReGLU network is
  finite-dimensional and carries the Borel σ-algebra of its topology; a Haar measure on it exists
  (`exists_haar20`); any two Haar measures on it have the same sets of measure zero
  (`null_iff_of_haar20`). Each of the eight statements at the concrete measure `Measure.addHaar`,
  with the number of parameters computed (`finrank_params_mlp`, `finrank_params_gated`), so that
  each reads "for almost every `θ`, `funDim … θ ≤ n`":

  | my theorem | statement used | the network | `P` | conclusion |
  |---|---|---|---|---|
  | `skipless_relu_concrete20` | `ae_funDim_add_le_skipless_relu_oneBlock_rmsNorm_zero` | one token, `d = d_in = 2`, `d_out = 1`, width 2 | 14 | `funDim ≤ 6` |
  | `skipless_reluSq_concrete20` | `ae_funDim_add_le_skipless_reluSq_oneBlock_rmsNorm_zero` | two tokens, `d = d_out = 3`, `d_in = 4`, width 5 | 51 | `funDim ≤ 33` |
  | `skipless_reglu_concrete20` | `ae_funDim_add_le_skipless_reglu_oneBlock_rmsNorm_zero` | `d = d_in = d_out = 1`, width 1 | 5 | `funDim ≤ 1` |
  | `residual_relu_concrete20` | `ae_funDim_add_le_residual_relu_rmsNorm_zero` | `d = d_in = d_out = 3`, two blocks of widths 1 and 2 | 36 | `funDim ≤ 29` |
  | `residual_reluSq_concrete20` | `ae_funDim_add_le_residual_reluSq_rmsNorm_zero` | `d = d_in = d_out = 2`, no block (`L = 0`) | 8 | `funDim ≤ 6` |
  | `residual_reglu_concrete20` | `ae_funDim_add_le_residual_reglu_rmsNorm_zero` | `d = d_in = d_out = 2`, three blocks of width 1 | 26 | `funDim ≤ 18` |
  | `residual_mlp_zero_concrete20` | `ae_funDim_add_le_residual_mlp_rescale_rmsNorm_zero` | `d = 2`, one block of width 3, the activation `0`, with `k = 5` | 20 | `funDim ≤ 15` |
  | `residual_gated_step_concrete20` | `ae_funDim_add_le_residual_gated_gate_rmsNorm_zero` | `d = 2`, one gated block of width 1, the gate `1` for `z > 0` and `0` otherwise, `k = 0` | 14 | `funDim ≤ 10` |

  The last two show what the two general statements also cover: the activation `0` is positively
  homogeneous of every degree, and a degree `k = 0` is allowed. Both are harmless (the statements
  are upper bounds), and the paper's kinds are the three named ones.

### Check 2. Which functional dimension

**Verdict: the claim of the three headers is true. At an input of the paper the network is
differentiable in the weights, every batch of the paper's inputs is a batch for Lean with the
true derivative, and Lean's `funDim` is at least the largest rank over such batches. So a bound
on `funDim` is a bound on the paper's functional dimension. `OneBlock/ResidualRMSZeroValue.lean`
uses the other notion (`funDimOn` on `residualZeroDomain`); each index row says which notion it
uses, but no sentence of the index sets the two side by side (a correction below).** (By reading
and by compiling, `Chk.lean` and `Chk2.lean`.)

- The Lean text (`Dimension/Functional.lean`, `Basic/RMSNorm.lean`):

  ```
  noncomputable def jacobianRank {n : ℕ} (X : Fin n → Matrix T dIn ℝ) (θ : Params A dIn dOut) : ℕ :=
    Module.finrank ℝ (LinearMap.range (fderiv ℝ (evalBatch A S X) θ).toLinearMap)
  noncomputable def funDim (θ : Params A dIn dOut) : ℕ :=
    sSup {r : ℕ | ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), r = jacobianRank A S X θ}
  noncomputable def rmsRow (ε : ℝ) (v : d → ℝ) : d → ℝ :=
    (Real.sqrt ((v ⬝ᵥ v) / (Fintype.card d : ℝ) + ε))⁻¹ • v
  ```
  All inputs; Mathlib's `fderiv` is `0` where the map is not differentiable; `rmsRow 0 0 = 0`. On
  a row that is not zero, `rmsRow 0 v = √d v/‖v‖`, the paper's `N_0` (by reading).
- The paper (S, "Notation and flat directions", lines 2365 to 2371): "For the ReLU-type
  activations, `F(θ, x)` is differentiable in `θ` at the inputs `x` at which no hidden unit sits
  at its kink, which form an open set of full measure, and "every input" means every such input.
  With `ε = 0`, it also excludes the inputs at which a state that is normalized vanishes."
- **At such an input Lean's output is differentiable in the weights.** By compiling
  (`Chk2.lean`), for any depth `L`, any stream matrices `S` (`0` skipless, `1` residual) and any
  number of tokens:

  ```
  theorem differentiableAt_eval_relu20 (S : Fin L → Matrix d d ℝ)
      (θ : Params (Arch.mlp (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut) (x : Matrix T dIn ℝ)
      (hrows : ∀ (ℓ : Fin (L + 1)) (t : T),
        hidden (Arch.mlp relu (rmsNorm 0) hid) S θ x ℓ t ≠ 0)
      (hkink : ∀ (ℓ : Fin L) (t : T) (i : hid ℓ),
        (rmsNorm 0 (hidden (Arch.mlp relu (rmsNorm 0) hid) S θ x ℓ.castSucc) * θ.read ℓ) t i ≠ 0) :
      DifferentiableAt ℝ (fun θ' : Params (Arch.mlp (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut
        => eval (Arch.mlp relu (rmsNorm 0) hid) S θ' x) θ
  ```
  and the same for ReLU² (`differentiableAt_eval_reluSq20`, with no condition on the hidden
  units: ReLU² is differentiable) and for ReGLU (`differentiableAt_eval_reglu20`, with "no gate
  at its kink"). `hrows`: no row of a hidden state `h_0, …, h_L` is zero; these are the states
  that are normalized. `hkink`: no pre-activation is `0`.
- **So Lean's Jacobian on a batch of such inputs is the true one**
  (`fderiv_evalBatch20`: the derivative of the batch is the tuple of the derivatives), **and
  `funDim` is at least the paper's functional dimension:**

  ```
  theorem funDimOn_eq_and_le20 {A : Arch T d L} (S : Fin L → Matrix d d ℝ) (θ : Params A dIn dOut)
      (U : Set (Matrix T dIn ℝ))
      (hU : ∀ x ∈ U, DifferentiableAt ℝ (fun θ' : Params A dIn dOut => eval A S θ' x) θ) :
      funDimOn A S θ U + Module.finrank ℝ (flatOn A S θ U) = Module.finrank ℝ (Params A dIn dOut)
        ∧ funDimOn A S θ U ≤ funDim A S θ
  ```
  With `U` the set of the paper's inputs: the largest rank over the batches of inputs of `U` is
  `P − dim K(θ)`, with `K(θ)` the directions flat at every input of `U` (the paper's functional
  dimension), and it is at most `funDim`. (`funDimOn A S θ U ≤ funDim A S θ` holds for every set
  `U` with no hypothesis: `funDimOn_le_funDim20`, `Chk.lean`.)
- What Lean's `funDim` uses in addition: the inputs outside `U` at which Lean's output happens
  to be differentiable in the weights (for instance an input of a skipless ReLU network at which
  no unit is active: `h_1 = 0`, Lean's output is `0` there and at all nearby weights, and the
  derivative is `0`). They can only add rank, and the bound is proved with them.
- **The mix of the two notions.** The three files of part (iv) bound `funDim` (all inputs). The
  file of part (v) uses `funDimOn A 1 θ (residualZeroDomain A θ)` (the inputs at which no row of
  `h_0` and of `h_1` vanishes), and says so in its header ("The functional dimension is
  `funDimOn` on `residualZeroDomain`, as in that file") and in its two docstrings ("at the inputs
  at which no normalized row vanishes"). In the index, row 851 says "the functional dimension of
  the residual network on the inputs at which no normalized row vanishes", and rows 852 to 854
  say "The functional dimension is Lean's `funDim`". Each row is true. What is not said: that
  these are two notions, and how they compare (`funDimOn … U ≤ funDim` for every `U`; so an upper
  bound on `funDim` gives one on `funDimOn`, and a lower bound on `funDimOn` gives one on
  `funDim`, but the "at most" of row 851 does not bound `funDim`). Row 851 also does not name
  `funDimOn` and `residualZeroDomain`; the row two above it does.

### Check 3. No extra hypotheses against Theorem B.1 (iv) and its Scope

**Verdict: none. Every hypothesis of the eight `ae_` statements is the theorem's or follows from
it. Lean asks less in five places, and the statements are true there (they are proved; and
computed cases agree).** (By reading and from the compiled signatures, `Sig.out`; the wider cases
by compiling instances, `Chk.lean`, and by computation, check 4.)

The theorem (S, lines 2319 to 2322 and 2338 to 2341): `d_model ≥ 2`; input and output dimensions
at least `d_model`; inputs range over all of `ℝ^{T × d_in}`; one block; pre-RMSNorm with `ε = 0`,
without biases; a ReLU, ReLU² or ReGLU block of width at least `d_model`; generic parameters.

| hypothesis in Lean | in which statements | in the theorem? |
|---|---|---|
| `[Fintype T]`, `[Fintype d]`, `[DecidableEq d]`, `[Fintype dIn]`, `[Fintype dOut]`, `[∀ ℓ, Fintype (hid ℓ)]` | all eight | yes: finite sizes |
| `[Nonempty d]` (`d ≥ 1`) | all eight | follows from `d_model ≥ 2` |
| `μ` with `[μ.IsAddHaarMeasure]` | all eight | "for generic parameters" |
| `hdIn : card d ≤ card dIn` | all eight | "the input … dimensions be at least `d_model`" |
| `hhid : ∀ ℓ, card d ≤ card (hid ℓ)` | the three skipless ones | "block of width at least `d_model`" |
| `hσ : ∀ lam z, 0 < lam → σ (lam * z) = lam ^ k * σ z` | `ae_funDim_add_le_residual_mlp_rescale_rmsNorm_zero`, `ae_funDim_add_le_residual_gated_gate_rmsNorm_zero` | holds for ReLU (`k = 1`), ReLU² (`k = 2`) and the gate of ReGLU (`k = 1`): `relu_homogeneous`, `reluSq_homogeneous`; the paper's "`B(λ n) = λ^k B(n)` for `λ > 0`" |
| one block (`hid : Fin 1 → Type`), stream `0` | the three skipless ones | yes |
| `χ = rmsNorm 0`, no biases (the definition of `eval` has none) | all eight | yes |

There is no hypothesis on the number of tokens (`T` may even be empty; the statement is then
`0 + … ≤ P`), none on `d_out`, and the functional dimension is over all inputs, as in the Scope.

Where Lean asks less than the theorem:

1. **No `d_out ≥ d`** (all eight). True: the independence of the directions uses `E`, the reads
   and, without the skip, the write, never `D` (check 6). Compiled instance with `d_out = 1 < d`
   (`skipless_relu_concrete20`). Computed: 15 cases with `d_out = 1` or `2` below `d`, both
   networks, the three kinds: the rank is equal to the bound in all 15.
2. **`d ≥ 1` in place of `d ≥ 2`** (all eight). True; for `d = 1` the bound is not sharp
   (`N_0` of a number is its sign, so the output is `±D` and the rank is at most `d_out`).
   Compiled instance with `d = 1` (`skipless_reglu_concrete20`). Computed: 12 cases with
   `d = 1`: the rank is `d_out` (1 or 2), equal to the bound in 3 cases and below it, by 1 to 4,
   in 9.
3. **No width in the residual bound** (the five residual ones). True: with the skip one and the
   same `Y + cI` acts at all hidden states, and `η_E = E (Y + cI)` alone gives `Y` and `c`; the
   writes are not needed. (S Lemma A.18 asks "the embedding has rank `d_model` and every block
   has width at least `d_model`" for both networks; for the residual network its argument does
   not need the width: "In a residual network the `G_ℓ` are equal", so `G_0 = I` from the
   embedding gives every `G_ℓ = I`.) Compiled instance with
   widths 1 and 2 below `d = 3` (`residual_relu_concrete20`). Computed: 12 cases of one
   residual block of width 1 or 2 below `d`: the rank is equal to the bound in all 12.
4. **Any depth in the residual bound** (`hid : Fin L → Type`, also `L = 0`). True, and it is a
   statement of the paper: S Theorem 4.2 and Theorem A.17 (ii) with identity skips, "at most
   `P − dim 𝒢 − s`", for `ε = 0` (`𝒢 = CO(d_model)`) and these three kinds of block. Theorem
   B.1 (iv) itself is for one block. Compiled instances with `L = 0, 2, 3`. Computed: 15 cases
   of two blocks and 6 of three blocks: the rank is equal to the bound in all 21.
5. **Any positively homogeneous activation or gate, of any degree `k : ℕ`** (the two general
   residual statements and the pointwise statements). True; wider than the paper's three kinds.

### Check 4. The values

**Verdict: the values are the paper's, and `s` is the paper's `s`. No batch has a rank above a
bound (261 cases). In all 180 cases inside the Scope of the theorem the rank is equal to the
bound: for the residual network with the three kinds of block, for the skipless network with
ReLU and ReLU² blocks (the paper claims equality in these), and also for the skipless network
with a ReGLU block (the paper claims only "at most").** (The values by reading; the ranks by
computation.)

- Lean: `funDim … 0 θ + (card d ^ 2 + (card d * (card d - 1) / 2 + 1) + card (hid 0)) ≤ P`
  (skipless, MLP), the same with `2 * card (hid 0)` (skipless, gated);
  `funDim … 1 θ + ((card d * (card d - 1) / 2 + 1) + ∑ ℓ, card (hid ℓ)) ≤ P` (residual, MLP), the
  same with `2 * ∑ ℓ, card (hid ℓ)` (residual, gated). `P` is
  `Module.finrank ℝ (Params …)`, the number of weights (`finrank_params`; no biases). The
  inequalities are written as sums, so no subtraction of natural numbers can go wrong, and
  `d (d − 1)` is even, so the division by 2 is exact.
- The paper (S, lines 2339 to 2341): "the residual network has functional dimension
  `P − d_model (d_model − 1)/2 − 1 − s`, and the skipless network at most
  `P − d_model² − d_model (d_model − 1)/2 − 1 − s`". The same numbers.
- **`s`.** The paper: "Let `s` be the total dimension of the symmetries inside the blocks, summed
  over the blocks" (S, lines 440 to 441); "Each hidden unit of a ReLU or ReLU² block can be
  rescaled, and so can the value of each hidden unit of a gated block and, in ReGLU, its gate"
  (Appendix A.6); "`s` is the number of rescalings: `d_hidden` for ReLU, ReLU², SwiGLU and GeGLU,
  `2 d_hidden` for ReGLU" (lines 2616 to 2617). Lean: the number of hidden units for MLP blocks
  (`rescaleDirMlp`: read column `i` times `α_i`, write row `i` times `−k α_i`), twice that for
  gated blocks with a positively homogeneous gate (`rescaleDir`: value column times `−α_i`, write
  row times `α_i`; `rescaleDirGate`: gate column times `β_i`, write row times `−k β_i`). The same.
- **The computation** (`z20run.py`, outputs `z20_skipless.out`, `z20_residual.out`,
  `z20_wider.out`, `z20_outside.out`, summary `z20_summary.out`). At random weights (entries
  uniform in `[−1, 1]`), the Jacobian in the weights at `4P` inputs and, as a second batch, at
  `8P` other inputs (16 to 792 inputs); 60 digits; the derivative is exact (forward mode). Half of
  the inputs have a random direction of `h_0 = x E`, half lie close to the kink of a random unit
  (relative distance `10⁻⁴` to 1, either side), all with a random scale from 0.2 to 5. In every
  case the two batches give the same rank, and the rank from the singular values in double
  precision is the same. Over all cases the smallest pivot that is kept is `1.4·10⁻⁸` of the
  largest and no entry that is dropped is above `10⁻⁵⁶`. An input of a skipless network at which
  no unit is active has `h_1 = 0`; as in Lean its output is `0` with derivative `0` (86 cases
  have such inputs). At the weights of the 240 cases inside the hypotheses of the pointwise Lean
  statements these hypotheses hold (`z20cond.py`: `E` and, without the skip, the write have rank
  `d`, no read column is zero), so there the pointwise statements say `rank ≤ bound`.
- **Inside the Scope of Theorem B.1 (iv)** (one block; `d = 2` with widths 2, 3, 4, 5 and `d = 3`
  with widths 3, 4, 5, 7; `(d_in, d_out) = (d, d)` at two parameters, `(d+1, d+1)`, `(d+2, d)`):
  30 cases for each kind of block and each network, 180 cases, `P` from 16 to 87. **The rank is
  equal to the bound in all 180.** For `d_in = d_out = d`:

  | network | block | `d = 2`, widths 2, 3, 4, 5: bound = rank | `d = 3`, widths 3, 4, 5, 7: bound = rank |
  |---|---|---|---|
  | skipless | ReLU | 8, 11, 14, 17 (`P` = 16, 20, 24, 28) | 20, 25, 30, 40 (`P` = 36, 42, 48, 60) |
  | skipless | ReLU² | 8, 11, 14, 17 | 20, 25, 30, 40 |
  | skipless | ReGLU | 10, 14, 18, 22 (`P` = 20, 26, 32, 38) | 26, 33, 40, 54 (`P` = 45, 54, 63, 81) |
  | residual | ReLU | 12, 15, 18, 21 | 29, 34, 39, 49 |
  | residual | ReLU² | 12, 15, 18, 21 | 29, 34, 39, 49 |
  | residual | ReGLU | 14, 18, 22, 26 | 35, 42, 49, 63 |

  The difference between the two networks is `d²` (4 and 9) in every pair. A rank on a batch is a
  lower bound of the functional dimension, and the Lean statement is the upper bound at these
  weights, so at these weights the functional dimension is the bound (as far as a rank at 60
  digits can show).
- **Wider than the Scope, inside the Lean hypotheses** (60 cases): `d_out < d` (15 cases, both
  networks): equal to the bound in all; `d = 1` (12 cases): the rank is `d_out`, equal in 3 and
  below the bound in 9; one residual block of width below `d` (12 cases): equal in all; two and
  three residual blocks (21 cases, `P` up to 99): equal in all. None above.
- **Outside the Lean hypotheses** (21 cases, for information; the formula is not claimed there):
  a skipless block of width below `d` (9 cases) and `d_in < d` (12 cases, both networks). The rank
  is below the formula in all 21, by 1 to 9. So these cases do not show that the width or
  `d_in ≥ d` is needed for the inequality; they are needed for the argument.
- **A rank on a batch is a lower bound: one example.** My first batches were plain random inputs.
  For a skipless ReLU block with `d = d_in = d_out = 2`, width 3, at weights with `det E = −0.008`,
  80, 160 and 400 such inputs all gave rank 7 against the bound 11: the three kinks are almost
  parallel in the space of inputs, and the inputs fell in two of the six regions. With the inputs
  spread over the directions of `h_0` the rank is 11 (`z20first.py`, `z20first.out`). All numbers
  above are from the spread inputs.

### Check 5. The direction `cobDir θ ![X, 0]`

**Verdict: it is "`E X` at `E`, `−X W_read` at `W_read`", and `0` at the write and at `D`.
`cobDir_zero_mem_flat_skipless_rmsNorm_zero_of_rowHomogeneous` is Lemma A.3 (i) for the change of
basis at `h_0` of a skipless network of one block with `ε = 0`, as a derivative at `G = I`.
Lost against the lemma: the finite form and the depth (both are in another file of the
library). Added: the inputs with a zero hidden row, for Lean's total `N_0`.** (By reading; the
entries by compiling, `Chk.lean`.)

- The Lean text (`Dimension/UpperBound.lean`) and the statement:

  ```
  def cobDir (θ : Params A dIn dOut) (X : Fin (L + 1) → Matrix d d ℝ) : Params A dIn dOut where
    E := θ.E * X 0
    read ℓ := -(X ℓ.castSucc * θ.read ℓ)
    write ℓ := θ.write ℓ * X ℓ.succ
    D := -(X (Fin.last L) * θ.D)

  theorem cobDir_zero_mem_flat_skipless_rmsNorm_zero_of_rowHomogeneous {A : Arch T d 1}
      (hA : A.χ = rmsNorm 0) {k : ℕ} (hf : RowHomogeneous A k)
      (θ : Params A dIn dOut) (X : Matrix d d ℝ) :
      cobDir θ ![X, 0] ∈ flat A 0 θ
  ```
- By compiling (`cobDir_zero_entries20`): for one block,
  `(cobDir θ ![X, 0]).E = θ.E * X`, `(cobDir θ ![X, 0]).read 0 = -(X * θ.read 0)`,
  `(cobDir θ ![X, 0]).write 0 = 0`, `(cobDir θ ![X, 0]).D = 0`. And the direction that the
  proofs of the two skipless bounds use (`bound_direction_entries20`):
  `cobDir θ ![X, Y] + c • scaleDir θ ![0, 1]` has the entries `E X` at `E`, `−X W_read` at
  `W_read`, `W_write (Y + c I)` at `W_write` and `−Y D` at `D`: the paper's "the entries `E X`
  at `E` and `−X W_read` at `W_read`, with the entries `W_write (Y + cI)` at `W_write` and `−Y D`
  at `D`".
- Lemma A.3 (S, lines 920 to 925): "Let a skipless network with pre-RMSNorm … have blocks that
  are positively homogeneous of degree `k` … Apply the change of basis `G ∈ GL(d_model)` at `h_ℓ`
  with `ℓ < L`, or the scaling `G = cI` at `h_L` with its read `D` unchanged. At every input whose
  hidden states are nonzero, the output becomes `Λy` with a scalar `Λ > 0`, and (i) `Λ = 1` if
  `ε = 0` or `G` is orthogonal". For `L = 1`, `ℓ = 0`, `ε = 0`: `E ↦ E G`,
  `W_read ↦ G⁻¹ W_read` leaves the output unchanged. Its derivative along `G = exp(τ X)` at
  `τ = 0` is the Lean statement, for every matrix `X` (the tangent space of `GL(d)` at `I`).
  `RowHomogeneous A k` is "scaling row `t` of the input of `f_ℓ` by `c_t > 0` scales row `t` of
  its output by `c_t^k`", the paper's "positively homogeneous of degree `k`" token by token.
- **Lost.** (a) The finite form (the output is unchanged for every `G ∈ GL(d)`, also far from
  `I`): it is `eval_cobAt_rmsNorm_zero_of_rowHomogeneous` of `Symmetry/HomogeneousRMSNorm.lean`,
  at any depth, and since `cd811de` the proof of the direction statement uses it. (b) Depth
  `L > 1` and `ℓ < L`: the direction statement is for one block only. (c) The scaling at `h_L`:
  its direction is `scaleDir_mem_flat_skipless_rmsNorm_zero` (`Dimension/UpperBoundRMSNormZero.lean`,
  for arbitrary `f_ℓ`). (d) The case "`G` orthogonal" and part (ii) are not for this file. The
  docstring says "as a statement on directions, for one block", which is accurate.
- **Added.** The lemma is for "every input whose hidden states are nonzero". Lean's `flat` asks
  the derivative to vanish at every input. At an input with a zero row of `h_0` or `h_1` the
  finite invariance still holds for Lean's function (`N_0(0) = 0`: a zero row stays a zero row,
  as the header of `Symmetry/HomogeneousRMSNorm.lean` says), so the Lean statement covers these
  inputs too; the paper leaves the function undefined there. At an input at which Lean's output
  is not differentiable in the weights (a unit at its kink), Lean's derivative is `0` and the
  membership in `flat` says nothing; the paper's flat directions do not use such inputs either.

### Check 6. The conditions of the pointwise statements

**Verdict: they are the conditions under which the paper's directions are independent, each
holds at generic parameters, and the `ae_` statements get them from `d_in ≥ d` and (without the
skip) the width.** (By reading; the independence by hand.)

- The statements:

  ```
  theorem funDim_add_le_skipless_mlp_homogeneous_rmsNorm_zero [Nonempty d] {k : ℕ}
      (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
      (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
      (hE : θ.E.rank = Fintype.card d) (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d)
      (hc : ∀ ℓ i, (fun a => θ.read ℓ a i) ≠ 0) : …
  theorem funDim_add_le_skipless_gated_homogeneous_rmsNorm_zero [Nonempty d] {k : ℕ} …
      (hE : θ.E.rank = Fintype.card d) (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d)
      (hv : ∀ ℓ i, (fun a => θ.read ℓ a (Sum.inr i)) ≠ 0)
      (hg : ∀ ℓ i, (fun a => θ.read ℓ a (Sum.inl i)) ≠ 0) : …
  theorem funDim_add_le_residual_mlp_rescale_rmsNorm_zero [Nonempty d] {k : ℕ} …
      (hE : θ.E.rank = Fintype.card d) (hc : ∀ ℓ i, (fun a => θ.read ℓ a i) ≠ 0) : …
  theorem funDim_add_le_residual_gated_gate_rmsNorm_zero [Nonempty d] {k : ℕ} …
      (hE : θ.E.rank = Fintype.card d)
      (hv : ∀ ℓ i, (fun a => θ.read ℓ a (Sum.inr i)) ≠ 0)
      (hg : ∀ ℓ i, (fun a => θ.read ℓ a (Sum.inl i)) ≠ 0) : …
  ```
- The paper (S, lines 2909 and 2610 to 2614): "For generic parameters these directions are
  independent, as in Step 3 of part (i)", and Step 3 there: "a rescaling that is also a direction
  of Lemma B.2 has `η_E = EX = 0`, so `X = 0`, and then `W_read diag(λ) = 0`, so every `λ_i = 0`,
  because no column of `W_read` vanishes."
- By hand, the skipless network. A combination of the directions with the numbers
  `(X, Y, c, α)` has the entries `E X` at `E`; `−X W_read + W_read diag(α)` at `W_read`;
  `W_write (Y + cI) − k diag(α) W_write` at `W_write`; `−Y D` at `D`. If it is zero: `E X = 0`
  gives `X = 0` (`E` of rank `d`); then `α_i` times read column `i` is zero, so `α = 0` (no read
  column zero); then `W_write (Y + cI) = 0` gives `Y + cI = 0` (the write of rank `d`), and
  `Y = 0`, `c = 0` because the diagonal of an antisymmetric matrix is zero (this is where
  `d ≥ 1` is used). For a gated block the gate column `i` moves by `β_i` times itself and the
  value column `i` by `−α_i` times itself, so "no gate column and no value column zero" gives
  `α = β = 0`. With the skip the same `Y + cI` acts at every hidden state, the entry at `E` is
  `E (Y + cI)`, and `E` of rank `d` gives `Y` and `c`; the rescalings do not move `E`, and the
  reads give `α` (and `β`). So the conditions are sufficient, and they are the ones that the
  paper's argument names. (They are not all necessary: without the skip, `D` of rank `d` and a
  nonzero write would do in place of the write of rank `d`.)
- The `ae_` statements: `ae_rank_E_write μ hdIn hhid` gives "`E` and every write have rank `d`"
  from `d_in ≥ d` and "every write has at least `d` rows"; `ae_read_col_ne_zero μ`,
  `ae_value_ne_zero μ`, `ae_gate_ne_zero μ` give the columns (they need `d ≥ 1`); for the
  residual statements a private copy gives "`E` has rank `d`" from `d_in ≥ d` and
  `ae_isUnit_det_submatrix`. (By reading these statements and the two-line proofs of the `ae_`
  statements.)

### Check 7. `OneBlock/ResidualRMSZeroValue.lean`

**Verdict: the two statements are the two readings of the proof's sentence. The half "at most"
is true under its hypotheses alone; the equality is the paper's value at one `θ` under the
conditions of the proof, and its hypotheses hold at almost every `θ` for a tanh block.** (By
reading; the last point by compiling, `Chk2.lean`.)

- The Lean text:

  ```
  theorem funDimOn_add_le_residual_rmsNorm_zero {A : Arch T d 1} [Nonempty d]
      (hA : A.χ = rmsNorm 0) (hf : AnalyticOnNhd ℝ (A.f 0) Set.univ) (θ : Params A dIn dOut)
      (hE : θ.E.rank = Fintype.card d) :
      funDimOn A 1 θ (residualZeroDomain A θ)
          + (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
          + Module.finrank ℝ (blockFlatSphere A θ)
        ≤ Module.finrank ℝ (Params A dIn dOut)

  theorem funDimOn_residual_rmsNorm_zero_eq {A : Arch T d 1} [Nonempty T]
      (hA : A.χ = rmsNorm 0) (hd : 2 ≤ Fintype.card d)
      (hf : AnalyticOnNhd ℝ (A.f 0) Set.univ) (θ : Params A dIn dOut)
      (hE : θ.E.rank = Fintype.card d) (hD : θ.D.rank = Fintype.card d)
      (hw : ∃ w : Matrix T dIn ℝ, ∀ t, LinearIndependent ℝ
        ![(w * θ.E) t, (A.f 0 (rmsNorm 0 (w * θ.E) * θ.read 0) * θ.write 0) t]) :
      funDimOn A 1 θ (residualZeroDomain A θ)
          + (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
          + Module.finrank ℝ (blockFlatSphere A θ)
        = Module.finrank ℝ (Params A dIn dOut)
  ```
- The paper (S, lines 2998 to 3000): "The directions of `CO(d_model)` move `E` by `E(Y + cI)`,
  which vanishes only for `Y = 0` and `c = 0`. So `K(θ)` is the direct sum of these directions
  and `V_θ`, and the residual network has functional dimension
  `P − dim CO(d_model) − dim V_θ`."
- **The half "at most".** It says: the directions of `CO(d)` and those of `V_θ` are flat at the
  inputs of `residualZeroDomain` and independent. Under its hypotheses alone this is true (it is
  proved, with the three standard axioms; and by reading, each step needs no more): the
  directions of `CO(d)` are flat at every input for arbitrary `f`
  (`cobDir_const_mem_flat_residual_rmsNorm_zero`, `scaleDir_const_mem_flat_residual_rmsNorm_zero`);
  a direction of `V_θ` leaves the output of the block unchanged to first order at every `n` with
  rows on the sphere, the rows of `N_0(x E)` are on the sphere when no row of `x E` is zero, and
  `N_0` is differentiable at `h_1` when no row of `h_1` is zero (this is where the set of inputs
  and the differentiability of `f` are used); the sum is direct because a direction of `V_θ` has
  `η_E = 0` and `E (Y + cI) = 0` gives `Y = 0`, `c = 0` for `E` of rank `d ≥ 1`. No `d ≥ 2`, no
  rank of `D`, no input `w`, no condition on the tokens. For `d = 1` it is true and not sharp (by
  hand, for one token and a tanh block: the output is `±D`, the rank is `d_out`, and
  `dim V_θ = 2 d_hidden − 1`, so the bound is `d_in + d_out`).
- **The equality.** It is the "at most" together with `finrank_le_funDimOn_residual_rmsNorm_zero`
  (the "at least" of `OneBlock/ResidualRMSZeroGain.lean`, read by the nineteenth reader), under
  the hypotheses of the latter: `d ≥ 2`, `E` and `D` of rank `d`, one input `w` with the rows of
  `w E` and of `g(w)` linearly independent for every token ("For generic parameters `w E` and
  `g(w)` are linearly independent for all `w` in an open set"). The value is the paper's:
  `P − dim CO(d) − dim V_θ` with `dim CO(d) = d(d−1)/2 + 1` and `V_θ = blockFlatSphere A θ`; the
  functional dimension is the paper's for `ε = 0` and an analytic block (no kinks; the inputs at
  which a normalized row vanishes are excluded). It is stated at one `θ`, not "for generic
  parameters"; the index says so ("under the conditions of the proof").
- **Not vacuous.** By compiling (`ae_funDimOn_residual_tanh_eq20`, `Chk2.lean`): for a tanh
  block with at least one hidden unit and `d_in, d_out ≥ d ≥ 2`, the equality holds at almost
  every `θ` for every Haar measure (from `ae_turnGeneric`, `ae_exists_linearIndependent_rows_mlp`
  and the statement). The library does not state this `ae_` form.
- The file still has two section comments from the scratch file it came from: "Check 3: the
  condition of `blockFlatSphere` is the derivative of the block along `ψ`" and "Check 6: the
  other direction of the residual count (not a statement of the library) … The library has
  `P ≤ funDimOn + …`. Here: the other inequality". The second is no longer true as worded: the
  statement is now in the library. They are comments, not docstrings of public theorems.

### Check 8. The index rows and the axiom file

**Verdict: every sentence of the four rows is true of the statements; every one of the 17 public
theorems is in a row and in `checks/Axioms.lean`. "At any depth" is said in the row of the
residual bound, but the row does not say that this is more than Theorem B.1 (iv) asks, nor that
at depth `L` it is a statement of the paper (Theorem 4.2).** (By reading; the names by a script.)

- Row 851 (`OneBlock/ResidualRMSZeroValue.lean`): "for `ε = 0`, `E` of rank `d ≥ 1` and an
  analytic map `f` of the block, the functional dimension of the residual network on the inputs
  at which no normalized row vanishes is at most `P − (d(d−1)/2 + 1) − dim V_θ`; under the
  conditions of the proof (`d ≥ 2`, `E`, `D` of rank `d`, one input `w` with the rows of `w E`
  and `g(w)` independent for every token) it is equal to it." True of the two statements
  (check 7). The row does not name `funDimOn` and `residualZeroDomain` (check 2).
- Row 852 (`OneBlock/SkiplessHomogeneousRMSZero.lean`): each clause is true: the direction at
  `h_0` for an MLP block with a positively homogeneous activation, and for any one block that is
  `RowHomogeneous`; the bound at one `θ` under "`E` and the write have rank `d ≥ 1` and no read
  column is zero"; the same at almost every `θ` for ReLU and ReLU² blocks of width at least `d`
  with `d_in ≥ d`; "Lean's `funDim` (all inputs; a zero row is normalized to `0`), which is at
  least the paper's" (check 2). The file `skipless_homogeneous_zero_check_2026-11-24.py` and its
  output are in `ai_notes/` (I read the output: largest difference of the outputs
  `5.5·10⁻¹⁴` over 1200 inputs, and `3.6·10⁻¹⁴` over 600 for ReGLU; I did not run it). "Not
  stated: the value for the residual network; the equality for ReLU and ReLU² blocks": true of the
  file; of the library it is true for the value (an equality) but the half "at most" of that
  value is two rows below, which the row could say.
- Row 853 (`OneBlock/SkiplessHomogeneousGatedRMSZero.lean`): each clause is true (`s` twice the
  number of hidden units; "no gate column and no value column of the read is zero"; a ReGLU block
  of width at least `d`, `d_in ≥ d`). The same remark on "Not stated: the value for the residual
  network".
- Row 854 (`Residual/UpperBoundRescaleRMSNormZero.lean`): each clause is true: "at any depth";
  "if `E` has rank `d ≥ 1` and no column of a read is zero" (for gated blocks: no value column and
  no gate column); "the same at almost every `θ` for `d_in ≥ d` (general activation or gate, and
  ReLU, ReLU², ReGLU by name)"; "No width of the blocks is asked"; "Not stated: the half "at
  least"". The row is headed "S Theorem B.1 (iv), the residual network, the half "at most" …, at
  any depth". It does not say that Theorem B.1 (iv) is for one block, and it does not say that at
  depth `L` the statement is S Theorem 4.2 and Theorem A.17 (ii) with identity skips for `ε = 0`
  with the term `s` (the row of the twin for `ε > 0`, `Residual/UpperBoundSymmetries.lean`, is
  headed "S Theorem 4.2 with identity skips, with the term `s`").
- The names. The 17 public theorems of the four files (`pub_*.txt`, from the sources) are the 17
  names of the four rows (2 + 5 + 3 + 7), and the 17 lines 1576 to 1592 of `checks/Axioms.lean`.
  The four files are imported by `SkipsLean.lean` (lines 58 and 284 to 286).
- Lines 215 to 220 of the index ("Not yet compared by such a reader …") name the four files; at
  `a23c388` they add "these four are with the reader of the twentieth audit since 20:14 UTC".

---------------------------------------------------------------------------------------------------

## Part 2: the statements, file by file

Verdicts: SAME, LEAN STRONGER (the paper's claim under fewer hypotheses or for more cases),
LEAN WEAKER, DIFFERENT, PART (a part of the paper's sentence), FALSE. All 17 are proved with the
three standard axioms (`Sig.out`).

### `OneBlock/SkiplessHomogeneousRMSZero.lean` (5 theorems)

| theorem | paper sentence | verdict |
|---|---|---|
| `cobDir_zero_mem_flat_skipless_rmsNorm_zero_of_rowHomogeneous` | S Lemma A.3 (i): "Apply the change of basis `G ∈ GL(d_model)` at `h_ℓ` with `ℓ < L` … At every input whose hidden states are nonzero, the output becomes `Λy` … (i) `Λ = 1` if `ε = 0`" | PART: one block, `ℓ = 0`, as the derivative at `G = I`. On the inputs LEAN STRONGER (no condition on the hidden states, for Lean's total `N_0`). Check 5 |
| `cobDir_zero_mem_flat_skipless_mlp_homogeneous_rmsNorm_zero` | proof of B.1 (iv): "Its normalization before the block drops out, which leaves the changes of basis `GL(d_model)` at `h_0`"; "They move the parameters along the directions with the entries `E X` at `E` and `−X W_read` at `W_read`" | SAME as a statement on directions; LEAN STRONGER in the activation (any `σ` with `σ(λ z) = λ^k σ(z)` for `λ > 0`, `k : ℕ`) |
| `funDim_add_le_skipless_mlp_homogeneous_rmsNorm_zero` | proof of B.1 (iv): "For generic parameters these directions are independent, as in Step 3 of part (i). So `dim K(θ) ≥ d_model² + d_model (d_model − 1)/2 + 1 + s`, which is the bound." | LEAN STRONGER: at one `θ`, with "generic" replaced by three named conditions (`E` and the write of rank `d`, no read column zero); any positively homogeneous activation; `d ≥ 1`; nothing on `d_out` |
| `ae_funDim_add_le_skipless_relu_oneBlock_rmsNorm_zero` | B.1 (iv): "For generic parameters … the skipless network at most `P − d_model² − d_model (d_model − 1)/2 − 1 − s`, with equality for ReLU and ReLU² blocks" | PART of the sentence: the bound, not the equality. The bound itself LEAN STRONGER (no `d_out ≥ d`, `d ≥ 1`, Lean's `funDim` over more inputs) |
| `ae_funDim_add_le_skipless_reluSq_oneBlock_rmsNorm_zero` | the same, for ReLU² | the same |

### `OneBlock/SkiplessHomogeneousGatedRMSZero.lean` (3 theorems)

| theorem | paper sentence | verdict |
|---|---|---|
| `cobDir_zero_mem_flat_skipless_gated_homogeneous_rmsNorm_zero` | as the second row above, for a ReGLU block ("`B(λ n) = λ^k B(n)`", here of degree `k + 1` in the input) | SAME as a statement on directions; LEAN STRONGER in the gate (any positively homogeneous gate) |
| `funDim_add_le_skipless_gated_homogeneous_rmsNorm_zero` | as the third row above, with `s` twice the number of hidden units | LEAN STRONGER: at one `θ` under named conditions (`E` and the write of rank `d`, no value column and no gate column zero) |
| `ae_funDim_add_le_skipless_reglu_oneBlock_rmsNorm_zero` | B.1 (iv): "the skipless network at most `P − d_model² − d_model (d_model − 1)/2 − 1 − s`" for a ReGLU block (the paper claims no equality for ReGLU) | LEAN STRONGER (the whole claim for the skipless ReGLU network, with no `d_out ≥ d` and `d ≥ 1`) |

### `Residual/UpperBoundRescaleRMSNormZero.lean` (7 theorems)

The paper sentence for all seven: B.1 (iv), "For generic parameters the residual network has
functional dimension `P − d_model (d_model − 1)/2 − 1 − s`", and its proof, "So
`dim K(θ) = d_model (d_model − 1)/2 + 1 + s`". At depth `L` the same statements are S Theorem
4.2 and Theorem A.17 (ii), "at most … `P − dim 𝒢 − s` with identity skips", for `ε = 0`.

| theorem | verdict |
|---|---|
| `funDim_add_le_residual_mlp_rescale_rmsNorm_zero` | PART of B.1 (iv): the half "at most" (`dim K(θ) ≥ …`), at one `θ` under named conditions (`E` of rank `d`, no read column zero). Wider: any depth, no width, any positively homogeneous activation, `d ≥ 1`, nothing on `d_out`. Against Theorem 4.2 at depth `L`: LEAN STRONGER (the same bound, with no width; Lemma A.18 asks the width) |
| `ae_funDim_add_le_residual_mlp_rescale_rmsNorm_zero` | the same at almost every `θ`, for `d_in ≥ d` |
| `ae_funDim_add_le_residual_relu_rmsNorm_zero` | the same, for ReLU by name |
| `ae_funDim_add_le_residual_reluSq_rmsNorm_zero` | the same, for ReLU² by name |
| `funDim_add_le_residual_gated_gate_rmsNorm_zero` | PART (the half "at most"), at one `θ` (`E` of rank `d`, no value column and no gate column of a read zero), `s` twice the number of hidden units; wider as above (any positively homogeneous gate) |
| `ae_funDim_add_le_residual_gated_gate_rmsNorm_zero` | the same at almost every `θ`, for `d_in ≥ d` |
| `ae_funDim_add_le_residual_reglu_rmsNorm_zero` | the same, for ReGLU by name |

### `OneBlock/ResidualRMSZeroValue.lean` (2 theorems)

| theorem | paper sentence | verdict |
|---|---|---|
| `funDimOn_add_le_residual_rmsNorm_zero` | proof of B.1 (v): "The directions of `CO(d_model)` move `E` by `E(Y + cI)`, which vanishes only for `Y = 0` and `c = 0`. So `K(θ)` is the direct sum of these directions and `V_θ`, and the residual network has functional dimension `P − dim CO(d_model) − dim V_θ`" | PART: the half "at most" (the directions of `CO(d)` and of `V_θ` are flat and independent), under fewer conditions than the proof has (`E` of rank `d ≥ 1`, `f` analytic) |
| `funDimOn_residual_rmsNorm_zero_eq` | the same sentence | SAME, at one `θ`, with "for generic parameters" replaced by the conditions that the proof uses (`d ≥ 2`, `E` and `D` of rank `d`, one input `w` with the rows of `w E` and `g(w)` independent for every token) |

### Notes

- The docstrings say what part of the paper each statement is: "the bound, under the conditions
  of the proof", "the half "at most"", "as a statement on directions, for one block". None claims
  the equality of part (iv), and the headers list what is not stated.
- The headers quote the paper word for word (I compared the quotes of the four headers with S
  lines 2338 to 2341, 2893 to 2910 and 2999 to 3000).
- The three files of part (iv) fit together as the paper's proof does: the directions (`E X`,
  `−X W_read`), (`W_write (Y + cI)`, `−Y D`) and the rescalings are each flat, and the pointwise
  bound counts them when they are independent. What part (iv) still needs beyond them is listed
  below.

---------------------------------------------------------------------------------------------------

## What the authors of the papers should know

Nothing false, vacuous, drifted or misdescribed was found. In order of weight:

1. **Of S Theorem B.1 (iv), Lean has the two upper bounds, and no more.** In the four files
   there is: the skipless network has at most `P − d² − d(d−1)/2 − 1 − s` (ReLU, ReLU², ReGLU);
   the residual network has at most `P − d(d−1)/2 − 1 − s`. Not in these files: that the residual
   network has at least this value (so its value); "with equality for ReLU and ReLU² blocks";
   "So the skip raises the functional dimension by at least `d_model²`, and by exactly
   `d_model²` for ReLU and ReLU² blocks" (the first of these needs the "at least" for the residual
   network together with the skipless bound; the second needs both equalities); and "The
   redundancy is then that of the symmetries". Files written after I started
   (`OneBlock/ResidualRMSZeroStepsOn.lean`, `OneBlock/ResidualRMSZeroRescale.lean`,
   `OneBlock/ResidualRMSZeroRescaleGeneric.lean`) are, by their commit messages, about the
   residual value; I did not read them.
2. **The computed ranks agree with every claim of part (iv), and go one step further for
   ReGLU.** In 180 cases inside the Scope (`d = 2, 3`, widths from `d` to `2d + 1`, the three
   kinds, both networks) the rank on the batch is equal to the bound. For the residual network
   and for the skipless network with ReLU and ReLU² blocks this is the paper's equality. For the
   skipless network with a ReGLU block the paper says only "at most"; the bound was attained in
   all 30 computed cases. This is a computation at 30 parameters, not a proof.
3. **Lean asks less than the theorem in four places, and the statements hold there**: no
   `d_out ≥ d` (the bound was attained in 15 computed cases with `d_out < d`); `d ≥ 1` (for
   `d = 1` the bound holds and is not sharp); no width for the residual bound (attained in 12
   computed cases of width below `d`); any depth for the residual bound (attained in 21 computed
   cases of two and three blocks).
4. **S Lemma A.18 asks "every block has width at least `d_model`" for the residual network too.
   Its argument does not need the width there** ("In a residual network the `G_ℓ` are equal":
   once `E` of rank `d_model` gives `G_0 = I`, all `G_ℓ` are `I`, and the reads give the
   rescalings). The Lean residual bound has no width, at any depth. So for these three kinds of
   block and `ε = 0` the bound with identity skips of Theorem 4.2 and Theorem A.17 (ii) holds
   with `d_in ≥ d_model` alone.
5. **Which functional dimension.** The three files of part (iv) use Lean's `funDim` (all inputs,
   Lean's total `N_0`). It is at least the paper's functional dimension (compiled: at the paper's
   inputs the network is differentiable in the weights), so the Lean bounds hold for the paper's.
   The file of part (v) uses the functional dimension on the inputs at which no normalized row
   vanishes, which for an analytic block is the paper's.
6. **The value of part (v) for the residual network** is in Lean as an equality at one `θ` under
   the conditions of the proof. That these conditions hold at almost every `θ` for a tanh block
   I compiled from the library's statements (`ae_funDimOn_residual_tanh_eq20`); the library
   (at `d12a43b`) does not state the equality at generic parameters.
7. **For the numerical checks of the paper (Appendix E).** A random batch can miss thin regions
   of a ReLU-type network when `E` is badly conditioned: at one random parameter with
   `det E = −0.008` (`d = 2`, width 3, skipless) 400 random inputs gave rank 7, and inputs spread
   over the directions of `h_0` gave 11, the value of the theorem. A rank that falls short of a
   claimed value at one seed can be of this kind.
8. The general Lean statements also cover activations and gates that are positively homogeneous
   of degree `0` (a step function) and the activation `0`. This is harmless for upper bounds.

## Corrections for `STATEMENTS.md` (line numbers of `d12a43b`; at `a23c388` the rows are lines 860, 861, 862 and 864)

Nothing in the four rows is false. Five places where the index can be plainer:

1. **Row 854** (`Residual/UpperBoundRescaleRMSNormZero.lean`). After "at any depth" add: "(the
   theorem is for one block; at depth `L` this is S Theorem 4.2 and Theorem A.17 (ii) with
   identity skips for `ε = 0`, `𝒢 = CO(d)`, with the term `s`, and without the width that Lemma
   A.18 asks)". Also "nothing is asked of `d_out`".
2. **Row 851** (`OneBlock/ResidualRMSZeroValue.lean`). Name the notion: "the functional dimension
   on the inputs at which no normalized row vanishes (`funDimOn` on `residualZeroDomain`, not
   `funDim`)". And once, in this row or before the four rows: "The rows of part (iv) below bound
   `funDim` (all inputs). `funDimOn A S θ U ≤ funDim A S θ` for every set `U`, so an upper bound
   on `funDim` gives one on `funDimOn`, and a lower bound on `funDimOn` gives one on `funDim`; the
   "at most" of this row does not bound `funDim`."
3. **Rows 852 and 853.** "Not stated: the value for the residual network" → "The half "at most"
   of the value for the residual network is in the row of
   `Residual/UpperBoundRescaleRMSNormZero.lean`. Not stated: its half "at least"; the equality for
   ReLU and ReLU² blocks; "the skip raises the functional dimension by at least `d_model²`"." (As
   the row stands, a reader can take "not stated" for the whole library, also for the half that
   is stated.) If the files written after `d12a43b` state some of these, the sentence should
   point to them instead.
4. **Row 852.** "(also stated for any one block that is positively homogeneous row by row,
   `RowHomogeneous`: S Lemma A.3 (i) as a statement on directions)" → add "for one block, for the
   change of basis at `h_0`; the finite form at any depth is
   `eval_cobAt_rmsNorm_zero_of_rowHomogeneous`". Rows 852 and 853 can also say that nothing is
   asked of `d_out`.
5. **Lines 215 to 220** ("Not yet compared by such a reader …"): the four files were compared by
   a twentieth reader (24 November): nothing false, vacuous or drifted; the bounds are the
   paper's with fewer hypotheses (no `d_out ≥ d`, `d ≥ 1`, no width and any depth for the residual
   bound); Lean's `funDim` is at least the paper's functional dimension; 261 cases computed at 60
   digits, none above a bound, 180 inside the Scope all equal to the bound. Report:
   `lean-statement-audit-twentieth-2026-11-24.md`.

Not for the index, for the file: `OneBlock/ResidualRMSZeroValue.lean` has two section comments
left from the scratch file it came from, "### Check 3: …" and "### Check 6: the other direction
of the residual count (not a statement of the library) … The library has `P ≤ funDimOn + …`.
Here: the other inequality". The words "not a statement of the library" are no longer true of a
file of the library.

## What I could not check

- **The proofs.** I read statements. That the 17 statements are proved rests on the compiler and
  on the axiom check (`Sig.out`), at `d12a43b`, `490f016` and `a23c388`.
- **"For generic parameters" by computation.** The computations are at one or two random
  parameters per case, 261 cases. They cannot see a set of measure zero, and a rank on a batch is
  a lower bound. The equalities that I report are equalities of a rank on two batches with a
  bound that Lean proves; they are evidence for the paper's equalities at these parameters, not
  proofs of them, and no evidence at all for `d` above 3.
- **The paper's equalities of part (iv)** (the residual value, the skipless value for ReLU and
  ReLU², the gain `d²`) are not Lean statements in these four files; I compared them only with
  the computed ranks.
- **More than one token in the computations.** I computed with one token per input. For MLP and
  gated blocks Lean's output at an input of `T` tokens is, row by row, the output at each row (by
  reading the definitions), so the rank over batches of `T`-token inputs is the rank over batches
  of rows.
- **The library lemmas under the `ae_` statements** (`ae_rank_E_write`, `ae_read_col_ne_zero`,
  `ae_value_ne_zero`, `ae_gate_ne_zero`, `ae_isUnit_det_submatrix`): I read their statements, not
  their proofs.
- **The coordinator's script** `skipless_homogeneous_zero_check_2026-11-24.py`: I read its output
  and did not run it.
- **The dimension paper.** None of the 17 statements cites the dimension paper, and I compared
  nothing with it.

## Files of this audit (in `/home/claude/audit20/`)

`Sig.lean`, `Sig.out` (at `a23c388`), `Sig_d12a43b.out` (signatures and axioms of the 17
theorems); `Chk.lean`, `Chk.out`, `Chk2.lean`, `Chk2.out` (compiled checks); `pub_*.txt` (the
public names); `z20core.py`, `z20run.py`, `z20sum.py`, `z20cond.py`, `z20fd.py`, `z20first.py`
(computations) with the outputs `z20_skipless.out`, `z20_residual.out`, `z20_wider.out`,
`z20_outside.out`, `z20_summary.out`, `z20fd.out`, `z20first.out`
(`z20_outside_first_try.out` is a run that stopped at the first case with `d_in < d`, where my
sampler divided by a singular matrix; the sampler was corrected and the group run again).
