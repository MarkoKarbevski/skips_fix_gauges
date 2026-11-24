STATUS: complete

# Nineteenth audit of Lean statements against the papers: one block with `ε = 0`, part (v) of S Theorem B.1; the identities of the finite symmetries (24 November 2026)

Reader: an independent reader who did not write the statements. Brief:
`audit19_brief_2026-11-24.md`. I audited statements and definitions, not proofs. I changed no
repository file, ran no `lake build`, made no commit and no push. My files are in
`/home/claude/audit19/`.

Library: `/home/claude/lw/lean` (branch `lean-wip`).

- **Commit read: `65a02a6ec273536e98b1cac8defdf278a6e908ba` (24 November 2026, 19:40:18 UTC),**
  the head when I started (about 19:42 UTC) and when I made the compiled checks and the
  computations (until 19:57 UTC). The branch then moved three times: `b2eecce` (19:58:32),
  `d703b9d` (20:00:03) and **`27b81a1860cf9e581d292809b1a6b803cf5f4e9a` (20:00:20), the head when
  I finished.** Between `65a02a6` and `27b81a1` the four files of the brief, `checks/Axioms.lean`
  and every file of definitions that I read are unchanged (`git diff` is empty for them); what
  changed is `STATEMENTS.md` (two places, see below), `SkipsLean.lean` (one import), one new file
  `OneBlock/SkiplessHomogeneousRMSZero.lean` and three files of `ai_notes/`.
- **Files with `sorry`.** At `65a02a6`: none (no file under `SkipsLean/` contains the word). At
  `27b81a1`: `OneBlock/SkiplessHomogeneousRMSZero.lean` (four), which is not a file of this
  audit and which none of the four files uses.
- The four files have 50 public names: 4 definitions and 46 theorems (1 + 1; 3 + 3; 0 + 10;
  0 + 32, as the brief says).
- All 46 theorems depend on `propext`, `Classical.choice`, `Quot.sound` only (by compiling
  `Sig.lean`, output `Sig.out`, against the build of `/home/claude/lp/lean`, which was at commit
  `65a02a6` when I compiled; its four source files are the same as those of `/home/claude/lw`, by `cmp`, and its
  compiled files are newer than the sources).

Papers, as text: the skips paper ("S", `<scratchpad>/skips.txt`) and the dimension paper ("D",
`<scratchpad>/dim.txt`). Line numbers of `STATEMENTS.md` are those of `65a02a6`: the rows of the
four files are lines 825, 839, 840 and 841 there. At `27b81a1` the same four rows, with the same
text, are lines 826, 840, 841 and 842, and the sentence of lines 207 to 211 is lines 207 to 212,
with the addition that the four files "are with the reader of the nineteenth audit".

How I checked.

- "By reading": every public statement and docstring of the four files, the definitions they use
  (`Arch`, `Params`, `hidden`, `eval`, `evalBatch`, `jacobianRank`, `funDim`, `flat`, `flatOn`,
  `rmsRow`, `rmsNorm`, `cobDir`, `scaleDir`, `antisymmetric`, `TurnGeneric`, `Arch.mlp`,
  `Arch.gated`, `Arch.attention`, `attnWeights`, `Arch.sum`, `Arch.attentionMlp`,
  `Arch.attentionGated`, `Params.cob`, `permUnits`, `flipUnits`, `permUnitsGated`, `permHeads`,
  `headsQK`, `headsVO`, `rescale`, `sumOf`, `sumFst`, `sumSnd`, `gelu`, `silu`), and the paper
  passages that the brief names.
- "By hand": a short argument of my own, written where it is used.
- "By compiling": scratch files in `/home/claude/audit19/`, compiled with `lake env lean <file>`
  from `/home/claude/lp/lean` (nothing written there): `Sig.lean` (the full signatures of the 50
  names, with every instance argument, and their axioms), `Chk.lean`, `Chk2.lean` (the checks of
  Part 1). All compile without error and without `sorry` (`*.out`); the theorems of mine that I
  name below have the three standard axioms.
- "By a computation": my own scripts (I did not run the coordinator's; I read its output, and my
  values agree with it where the cases coincide). `rz19core.py`, `rz19run.py`, `rz19special.py`:
  one block under pre-RMSNorm with `ε = 0`, mpmath with 60 digits, exact derivatives in the weights
  by forward mode written by hand (checked against central differences in `rz19fd.py`: they agree
  to `3·10⁻³⁷`); the rank from the eigenvalues of `JᵀJ`. Over all 93 cases the smallest singular
  value that is kept is `1.7·10⁻¹⁵` of the largest, and no dropped one is above `5.9·10⁻³¹`; every
  rank was computed on two independent batches of inputs (the second about twice as large) and was
  the same on both. Outputs: `rz19_*.out`, `rz19fd.out`. A rank on a batch is a lower bound of the
  functional dimension; a kernel dimension on a batch is an upper bound of `dim V_θ`.

**Short answer. Nothing false, nothing vacuous and nothing drifted was found.** The 46 statements
are the papers', or the papers' with a wider scope, with one exception of form: the count for the
residual network is one of the two inequalities of the paper's equality (the one that the theorem
needs). Six things the authors should know are listed after Part 2; the first three: (1) the
paper's "the residual network has functional dimension `P − dim CO(d) − dim V_θ`" is in Lean as
"at least"; the other inequality is true (I compiled it, and the equality held in all 93 computed
cases); (2) the hypothesis `d ≥ 2` of the three statements at one parameter follows from their
hypothesis on the input `w` (compiled), so the header's sentence that it "is needed" should say
that it is implied; (3) the paragraph "Generic parameters" of the paper's proof (the smallest value
`v` of `dim V_θ`, the two generic functional dimensions) is not a Lean statement, and is not
needed: Lean compares the two networks at the same `θ`, with the same `V_θ`.

---------------------------------------------------------------------------------------------------

## Part 1: the drift checks

### Check 1. Generic means almost every parameter, for every Haar measure

**Verdict: yes, in all ten `ae_` statements of the Kinds file; every index type is finite; the
statements apply to a concrete Haar measure.** (By reading; the shapes from the compiled
signatures, `Sig.out`; the measure space and three instances by compiling, `Chk.lean`.)

- The `variable` lines of `OneBlock/ResidualRMSZeroKinds.lean`:

  ```
  variable {T d dIn dOut : Type*} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn]
    [Fintype dOut]
  variable {hid H dh : Fin 1 → Type} [∀ ℓ, Fintype (hid ℓ)] [∀ ℓ, Fintype (H ℓ)]
    [∀ ℓ, Fintype (dh ℓ)]
  ```
  The weights are `E : Matrix dIn d ℝ`, `read 0 : Matrix d (r 0) ℝ`, `write 0 : Matrix (w 0) d ℝ`,
  `D : Matrix d dOut ℝ`, with `r 0 = w 0 = hid 0` (MLP), `r 0 = hid 0 ⊕ hid 0`, `w 0 = hid 0`
  (gated), `r 0 = H 0 × (dh 0 ⊕ (dh 0 ⊕ dh 0))`, `w 0 = H 0 × dh 0` (attention). Every one of
  these index types has `Fintype`, so the space of the weights is finite-dimensional.
- Each of the ten statements has `μ` as a variable of the statement with `[μ.IsAddHaarMeasure]`,
  and `∀ᵐ θ ∂μ`. None is "there is a parameter" or "on an open set". For instance:

  ```
  theorem ae_funDimOn_skipless_add_le_tanh_oneBlock_residual_rmsNorm_zero [Nonempty (hid 0)]
      (μ : Measure (Params (Arch.mlp (T := T) (d := d) Real.tanh (rmsNorm 0) hid) dIn dOut))
      [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
      (hdOut : Fintype.card d ≤ Fintype.card dOut) :
      ∀ᵐ θ ∂μ, funDimOn (Arch.mlp Real.tanh (rmsNorm 0) hid) 0 θ (skiplessZeroDomain (Arch.mlp
          Real.tanh (rmsNorm 0) hid) θ)
          + (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
        ≤ funDimOn (Arch.mlp Real.tanh (rmsNorm 0) hid) 1 θ (residualZeroDomain (Arch.mlp Real.tanh
            (rmsNorm 0) hid) θ)
  ```
- By compiling (`Chk.lean`): for a tanh block (`d = 2`, one token, one hidden unit) and two
  attention blocks, the space `Params …` is finite-dimensional and carries the Borel σ-algebra of
  its topology; a Haar measure on it exists (`exists_haar19`); any two Haar measures on it have the
  same sets of measure zero (`null_iff_of_haar19`). Three statements at the concrete measure
  `Measure.addHaar`: `tanh_concrete19` (one token, `d = d_in = d_out = 2`, one hidden unit),
  `attn_one_token_concrete19` (one token, one head of width `3 > d = 2`, no mask),
  `attn_other_mask_concrete19` (two tokens, every token sees only the last token: neither of the
  paper's two masks). Each reads "for almost every `θ`, `funDimOn` skipless `+ 2 ≤ funDimOn`
  residual".

### Check 2. The functional dimension for `ε = 0`

**Verdict: `funDimOn` is a maximum; the two sets are the paper's sets of inputs; the functional
dimension at `θ` on the set `U_θ` is the paper's; on rows that are not zero `rmsNorm 0` is the
paper's `N_0`; the gain is the paper's sentence, at each generic `θ`.** (By reading; six facts by
compiling.)

- The Lean text:

  ```
  noncomputable def funDimOn {L : ℕ} (A : Arch T d L) (S : Fin L → Matrix d d ℝ)
      (θ : Params A dIn dOut) (U : Set (Matrix T dIn ℝ)) : ℕ :=
    sSup {r : ℕ | ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i, X i ∈ U) ∧ r = jacobianRank A S X θ}
  def residualZeroDomain (A : Arch T d 1) (θ : Params A dIn dOut) : Set (Matrix T dIn ℝ) :=
    {x | (∀ t, (x * θ.E) t ≠ 0) ∧
      ∀ t, (x * θ.E + A.f 0 (rmsNorm 0 (x * θ.E) * θ.read 0) * θ.write 0) t ≠ 0}
  def skiplessZeroDomain (A : Arch T d 1) (θ : Params A dIn dOut) : Set (Matrix T dIn ℝ) :=
    {x | (∀ t, (x * θ.E) t ≠ 0) ∧
      ∀ t, (A.f 0 (rmsNorm 0 (x * θ.E) * θ.read 0) * θ.write 0) t ≠ 0}
  ```
- **Is `sSup` a maximum? Yes.** By compiling (`Chk.lean`): `funDimOn` unfolds (by `rfl`) to the
  supremum, over the batches of inputs of `U`, of the rank of the derivative of
  `θ' ↦ (eval A S θ' (X i))_i` at `θ`; the set of the ranks contains the rank of the empty batch
  (`ranks_nonempty19`) and is bounded by `P` (`ranks_bddAbove19`); so `funDimOn` is the rank on
  some batch of inputs of `U`, is at least the rank on every batch of inputs of `U`, and is at
  most `P` (`funDimOn_attained19`). With `U` all inputs it is `funDim` (`funDimOn_univ19`). It is
  never `0` "by convention": for an empty `U` it is the rank of the empty batch, which is `0`
  because there is no input.
- **Are the two sets the paper's? Yes.** The paper's networks of one block under pre-RMSNorm are
  `x ↦ N_ε(f(N_ε(xE) W_read) W_write) D` and `x ↦ N_ε(xE + f(N_ε(xE) W_read) W_write) D`
  (Appendix B, first display). In both, `N` is applied to two hidden states: `h_0 = xE`, before
  the read of the block, and `h_1`, before the readout; `h_1` is the output of the block without
  the skip, and `xE` plus it with the skip. By compiling (`mem_residualZeroDomain19`,
  `mem_skiplessZeroDomain19`): for `χ = rmsNorm 0`, `x ∈ residualZeroDomain A θ` if and only if no
  row of `hidden A 1 θ x 0` and no row of `hidden A 1 θ x 1` is zero, and the same for
  `skiplessZeroDomain` with the stream matrix `0`; and the outputs are `rmsNorm 0 (hidden … 1) * D`.
  The paper (S line 2367): "With `ε = 0`, it also excludes the inputs at which a state that is
  normalized vanishes." Lean reads this row by row (no row of a normalized state is zero). That is
  the reading under which `N_0` is defined, since it normalizes each token (S line 2963: "ignores
  the length of each token"); for one token the two readings are the same.
- **The set depends on `θ`, and the Jacobian is taken at the same `θ`: is that the paper's
  functional dimension at `θ`? Yes.** The paper's functional dimension at `θ` is the largest rank
  of the Jacobian at `θ` over the batches of inputs, where "every input" excludes the inputs at
  which a normalized state of the network at `θ` vanishes (S lines 2364 to 2380). By hand: for `x`
  in the set at `θ`, the rows of `xE'` and of `h_1` at `θ'` stay nonzero for `θ'` near `θ` (both
  are continuous in `θ'`), so near `θ` Lean's `eval` at `x` is the paper's network, and Lean's
  derivative at `θ` is the paper's. (The library proves the differentiability in private helpers;
  I did not audit those.)
- **On rows that are not zero, is `rmsNorm 0` the paper's `N_0`? Yes.** By compiling
  (`rmsRow_zero19`): `rmsRow 0 v = (√d / √(v ⬝ᵥ v)) • v`, the paper's `√d_model h/‖h‖` on each
  row. `rmsRow 0 0 = 0` is Lean's convention; no input of the two sets meets it.
- **The gain.** The Lean statement (seven forms, one per kind of block) is

  ```
  ∀ᵐ θ ∂μ, funDimOn A 0 θ (skiplessZeroDomain A θ) + (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
      ≤ funDimOn A 1 θ (residualZeroDomain A θ)
  ```
  **Plainly: for almost every `θ`, the functional dimension of the residual network at `θ` is at
  least that of the skipless network at the same `θ` plus `d(d−1)/2 + 1`.** The paper (S line
  2345): "For generic parameters the skip raises the functional dimension by at least
  `d_model (d_model − 1)/2 + 1`". The two networks have the same parameters, and "for generic
  parameters" is "off a set of measure zero" (S line 2383), so this is the paper's sentence: SAME.
  It is not weaker: it implies the comparison of the two generic values of the paper's proof
  ("The generic functional dimensions are therefore …", S line 3008) whenever each functional
  dimension is constant off a set of measure zero, and is equivalent to it then. It does not say
  that the two functional dimensions are generically constant, nor what they are; the paper's
  part (v) does not say it either.

### Check 3. `blockFlatSphere` (`V_θ`)

**Verdict: it is the paper's `V_θ`; the set is already a subspace, so the span adds nothing; the
condition is the derivative of `n ↦ f(n W_read) W_write` along `ψ`.** (By reading; both facts by
compiling.)

- The Lean text:

  ```
  noncomputable def blockFlatSphere (A : Arch T d 1) (θ : Params A dIn dOut) :
      Submodule ℝ (Params A dIn dOut) :=
    Submodule.span ℝ {ψ | ψ.E = 0 ∧ ψ.D = 0 ∧
      ∀ n : Matrix T d ℝ, (∀ t, n t ⬝ᵥ n t = Fintype.card d) →
        fderiv ℝ (A.f 0) (n * θ.read 0) (n * ψ.read 0) * θ.write 0
          + A.f 0 (n * θ.read 0) * ψ.write 0 = 0}
  ```
  The paper (S line 2964): "Let `V_θ` be the space of directions that move only the weights of the
  block and leave its output unchanged to first order at every input whose rows lie on this
  sphere". `ψ.E = 0 ∧ ψ.D = 0` is "move only the weights of the block"; `n t ⬝ᵥ n t = card d` for
  every `t` is "rows on the sphere of radius `√d`".
- By compiling (`mem_blockFlatSphere19`): `ψ ∈ blockFlatSphere A θ` if and only if `ψ` satisfies
  the three conditions. So the set is a subspace and the span is the set.
- By compiling (`hasDerivAt_block_19` in `Chk2.lean`): for a differentiable `f`, the map
  `τ ↦ f(n (R + τ R')) (W + τ W')` has at `τ = 0` the derivative
  `fderiv ℝ f (n R) (n R') W + f(n R) W'`. So the condition is "the output of the block at the
  state `n` does not move to first order along `ψ`".
- By a computation (the upper bound of `dim V_θ` on two batches of states on the sphere): `0` for
  tanh and GELU blocks, the number of hidden units for SwiGLU and GeGLU blocks, `2 H d_h²` for
  attention blocks on two tokens with `d_h ≤ d` (8 for `H = 1, d_h = 2`; 4 for `H = 2, d_h = 1`;
  16 for `H = 2, d_h = 2, d = 3`). These are the paper's numbers `s` of the continuous symmetries
  inside the block (D Appendix B), as "it contains the symmetries inside the block" says. That
  sentence itself is not a statement of these files.

### Check 4. No extra hypotheses against Theorem B.1 (v) and its Scope

**Verdict: none. Every hypothesis of the seven statements is the theorem's or is implied by it.
Lean's scope is wider in four ways (any number of hidden units from one; any number of tokens from
one; heads of any positive width; any mask in which every token sees some token), and the
statements hold there: they are proved, three instances were compiled, and 93 computed cases agree.**
(By reading; by compiling; by a computation.)

The hypotheses of the seven named statements `ae_funDimOn_skipless_add_le_…_oneBlock_residual_rmsNorm_zero`:

| Hypothesis | In which | The theorem has it or implies it? |
|---|---|---|
| `[Fintype T] [Nonempty T]` | all seven | Implied: sequences of `T` tokens, at least one. The paper asks for at least two tokens for attention; Lean does not (wider) |
| `[Fintype d] [DecidableEq d]`, `hd : 2 ≤ card d` | all seven | Has it: "Let `d_model ≥ 2`" |
| `[Fintype dIn] [Fintype dOut]`, `hdIn : card d ≤ card dIn`, `hdOut : card d ≤ card dOut` | all seven | Has it: "let the input and output dimensions be at least `d_model`" |
| `χ = rmsNorm 0` (in the architecture) | all seven | Has it: "pre-RMSNorm with `ε = 0`" |
| no biases (`Params` has none) | all seven | Has it: "without biases" |
| `[Nonempty (hid 0)]` | `mlp`, `tanh`, `gelu`, `gated`, `swiglu`, `geglu` | Implied: a block has a hidden unit. No condition on the width beyond that, as in part (v) |
| `hσa : AnalyticOnNhd ℝ σ Set.univ`, `hσp : ∀ z, 0 < z → σ z ≠ 0` | `mlp`, `gated` (the two general forms) | Wider than the theorem: every analytic activation, or gate, that is nonzero on the positive reals; tanh, GELU and SiLU are such, and the four forms by name have no such hypothesis |
| `sees`, `hsees : ∀ t, ∃ s, sees t s` | `attention` | Implied: both of the paper's masks ("causal or not") have it. Wider: other masks |
| `[Nonempty (H 0)] [Nonempty (dh 0)]` | `attention` | Implied: "`H` heads of width `d_h`". The paper's `d_h ≤ d_model` is not asked (wider) |
| `μ`, `[μ.IsAddHaarMeasure]` | all seven | "For generic parameters" (Check 1) |

`gelu z = z · Φ(z)` and `silu z = z / (1 + e^{−z})` in the library (by reading), so "GELU",
"SwiGLU" (gate SiLU) and "GeGLU" (gate GELU) are the paper's.

The wider cases, by a computation (`rz19run.py`; for each case the rank of the Jacobian with and
without the skip on two batches, and the upper bound of `dim V_θ` on two batches; `co` is
`d(d−1)/2 + 1`):

| Case | `P` | `co` | residual | skipless | `dim V_θ ≤` | gain |
|---|---|---|---|---|---|---|
| tanh, `d = 2`, **one hidden unit**, one token | 12 | 2 | 10 | 2 | 0 | 8 |
| tanh, `d = 2`, 2 hidden units | 16 | 2 | 14 | 12 | 0 | 2 |
| tanh, `d = 2`, 3 hidden units | 20 | 2 | 18 | 16 | 0 | 2 |
| tanh, `d = 2`, 2 hidden units, two tokens | 16 | 2 | 14 | 12 | 0 | 2 |
| tanh, `d = 3`, **one hidden unit** | 24 | 4 | 20 | 3 | 0 | 17 |
| tanh, `d = 3`, 2 hidden units | 30 | 4 | 26 | 19 | 0 | 7 |
| tanh, `d = 3`, 3 hidden units | 36 | 4 | 32 | 28 | 0 | 4 |
| tanh, `d = 3`, 4 hidden units | 42 | 4 | 38 | 34 | 0 | 4 |
| attention, **one token**, `d = 2`, `H = 1`, `d_h = 1` | 16 | 2 | 9 | 2 | 5 | 7 |
| attention, **one token**, `d = 2`, `H = 1`, `d_h = 2` | 24 | 2 | 10 | 6 | 12 | 4 |
| attention, **one token**, `d = 2`, `H = 1`, **`d_h = 3 > d`** | 32 | 2 | 10 | 6 | 20 | 4 |
| attention, **one token**, `d = 3`, `H = 1`, **`d_h = 4 > d`** | 66 | 4 | 23 | 14 | 39 | 9 |
| attention, two tokens, no mask, `d = 2`, `H = 1`, `d_h = 1` | 16 | 2 | 12 | 2 | 2 | 10 |
| attention, two tokens, no mask, `d = 2`, `H = 1`, `d_h = 2` | 24 | 2 | 14 | 12 | 8 | 2 |
| attention, two tokens, no mask, `d = 2`, `H = 1`, **`d_h = 3 > d`** | 32 | 2 | 14 | 12 | 16 | 2 |
| attention, two tokens, causal, `d = 2`, `H = 2`, `d_h = 1` | 24 | 2 | 18 | 16 | 4 | 2 |
| attention, two tokens, causal, `d = 3`, `H = 2`, `d_h = 2` | 66 | 4 | 46 | 42 | 16 | 4 |
| attention, two tokens, **every token sees only the last**, `d = 2`, `H = 1`, `d_h = 2` | 24 | 2 | 10 | 6 | 12 | 4 |
| attention, three tokens, causal, `d = 2`, `H = 1`, `d_h = 2` | 24 | 2 | 14 | 12 | 8 | 2 |

In all 74 cases at random parameters (26 tanh: 13 shapes with two seeds each; 4 GELU; 12 SwiGLU
and GeGLU; 11 attention on one token; 21 attention on two or three tokens; `d = 2, 3`; also
`d_in > d` and `d_out > d`): the gain is at least `co`. It is exactly `co` in the 39 cases whose
block has width at least `d` and, for attention, at least two tokens and one of the paper's two
masks; it is larger in the other 35 (narrower blocks; attention on one token, or with the mask in
which every token sees only the last token). With one hidden unit the skipless network has every
row of `h_1` on one line, so its output takes two values per token and its rank is `d_out`. With
one token the attention block is the linear map `n ↦ n S`, `S = ∑_i W_{V,i} W_{O,i}`: the skipless
network is `x ↦ N_0(x E S) D`, and the gain is `d²` when `H d_h ≥ d`. I found no case against the
statements. (A computed rank is a lower bound: a computation can support these
inequalities but not prove them; the proof is Lean's.)

### Check 5. The Steps theorem against the proof's passage

**Verdict: it is the passage, with "for generic parameters" replaced by the three conditions that
the passage uses. The signs are those of the symmetry. `hw` is the proof's condition. `d ≥ 2` is
implied by `hw`, so it is not an extra hypothesis but also not "needed" as one. The theorem holds
for every finite nonempty set of tokens, one token included.** (By reading; by hand; three facts
by compiling.)

- The Lean text:

  ```
  theorem exists_antisymm_scale_of_flatOn_residual_rmsNorm_zero {A : Arch T d 1}
      (hA : A.χ = rmsNorm 0) (hd : 2 ≤ Fintype.card d)
      (hf : AnalyticOnNhd ℝ (A.f 0) Set.univ) (θ : Params A dIn dOut)
      (hE : θ.E.rank = Fintype.card d) (hD : θ.D.rank = Fintype.card d)
      (hw : ∃ w : Matrix T dIn ℝ, ∀ t, LinearIndependent ℝ
        ![(w * θ.E) t, (A.f 0 (rmsNorm 0 (w * θ.E) * θ.read 0) * θ.write 0) t])
      (η : Params A dIn dOut) (hη : η ∈ flatOn A 1 θ (residualZeroDomain A θ)) :
      ∃ (Y : Matrix d d ℝ) (c : ℝ), Yᵀ = -Y ∧ η.E = θ.E * (Y + c • 1) ∧ η.D = -(Y * θ.D) ∧
        ∀ n : Matrix T d ℝ, (∀ t, n t ⬝ᵥ n t = Fintype.card d) →
          fderiv ℝ (A.f 0) (n * θ.read 0) (n * (η.read 0 + Y * θ.read 0)) * θ.write 0
            + A.f 0 (n * θ.read 0) * (η.write 0 - θ.write 0 * (Y + c • 1)) = 0
  ```
- **The signs.** By hand: the orthogonal change of basis `Q = I + τY + …` of the stream is
  `E ↦ E Q`, `W_read ↦ Q⁻¹ W_read`, `W_write ↦ W_write Q`, `D ↦ Q⁻¹ D`; it keeps the function,
  since `N_0(h Q) = N_0(h) Q` for an orthogonal `Q`. Its derivative at `τ = 0` is
  `(E Y, −Y W_read, W_write Y, −Y D)`. The paper's scale (S line 2991) "`E ↦ (1 + τ)E`,
  `W_write ↦ (1 + τ)W_write`" has the derivative `(E, 0, W_write, 0)`. So the direction of the
  symmetry is `(E (Y + c I), −Y W_read, W_write (Y + c I), −Y D)`, and `η` minus it has the
  `E`-part `η_E − E (Y + c I)`, the `D`-part `η_D + Y D`, the read `η_read + Y W_read` and the
  write `η_write − W_write (Y + c I)`: the four expressions of the statement, the first two being
  zero. By compiling (`Chk.lean`): the four components of
  `cobDir θ (fun _ => Y) + scaleDir θ (fun _ => c)`, the direction that the library's proof
  subtracts, are `θ.E * (Y + c • 1)`, `-(Y * θ.read 0)`, `θ.write 0 * (Y + c • 1)`,
  `-(Y * θ.D)`.
- **The conclusion** is the passage's: `Y_s = 0` (`Yᵀ = -Y`), `η′_E = c E`, and `η″ ∈ V_θ` (the
  last clause is membership in `blockFlatSphere` of the direction with `E`-part and `D`-part `0`,
  by Check 3).
- **`hw`.** The paper (S line 2984): "For generic parameters `w E` and `g(w)` are linearly
  independent for all `w` in an open set". Lean asks for one `w` at which, for every token, row
  `t` of `w E` and row `t` of `g(w)` are linearly independent. By hand: for a continuous `f` the
  set of such `w` is open, so one `w` gives the open set (the library proves this inside the
  proof). "For every token" is what the passage needs for attention ("with a number `μ(x)`, for
  attention one per token": the comparison is made in each row). `hE` and `hD` are the proof's
  "`E`, `D` … have rank `d_model`" for generic parameters.
- **`d ≥ 2`.** By compiling (`two_le_card_of_hw19`): `hw` implies `2 ≤ Fintype.card d` (two
  linearly independent rows of length `d`). So `hd` is a consequence of `hw`, in this theorem and
  in the two statements of the Gain file that have both; I compiled the gain at one parameter
  without `hd` (`gain_without_hd19`). The header of the Steps file says "`d ≥ 2` is the Scope's
  and is needed (for `d = 1` the step "`η′_E = c E`" fails)": for `d = 1` no `w` satisfies `hw`,
  so the statement says nothing there, with or without `hd`. Nothing is wrong in the statement;
  the sentence of the header should say that `hd` is implied by `hw`.
- **One token.** The statement is for every `T` with `[Fintype T] [Nonempty T]`, so it holds for
  one token. By a computation: the count that follows from it (Check 6) is an equality in the
  computed cases with one, two and three tokens.

### Check 6. The two counts

**Verdict: the skipless count is the paper's claim, in the paper's direction. The residual count
is one inequality of the paper's equality: "at least". The other inequality is true (compiled by
me; it is not in the library). `card d * (card d - 1) / 2` in `ℕ` is `d(d−1)/2`. The gain needs
no hypothesis on the block being nonzero: it follows from `hw`.** (By reading; three facts by
compiling; by a computation.)

- The Lean text of the conclusions:

  ```
  -- finrank_le_funDimOn_residual_rmsNorm_zero (hA hd hf θ hE hD hw)
  Module.finrank ℝ (Params A dIn dOut)
    ≤ funDimOn A 1 θ (residualZeroDomain A θ)
      + (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
      + Module.finrank ℝ (blockFlatSphere A θ)
  -- funDimOn_add_le_skipless_rmsNorm_zero (hA hf θ hE hD hB)
  funDimOn A 0 θ (skiplessZeroDomain A θ)
      + 2 * (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
      + Module.finrank ℝ (blockFlatSphere A θ)
    ≤ Module.finrank ℝ (Params A dIn dOut)
  ```
  with `hB : ∃ n, (∀ t, n t ⬝ᵥ n t = Fintype.card d) ∧ A.f 0 (n * θ.read 0) * θ.write 0 ≠ 0`.
- **The residual count.** The paper (S line 2999): "So `K(θ)` is the direct sum of these
  directions and `V_θ`, and the residual network has functional dimension
  `P − dim CO(d_model) − dim V_θ`." Lean: `P − co − dim V_θ ≤` the functional dimension. This is
  the inequality that the gain needs. The other one ("the directions of `CO(d)` and of `V_θ` are
  flat for the residual network and independent") is not a statement of the library. It is true:
  by compiling (`Chk2.lean`), `blockFlatSphere_le_flatOn_residual_19` (a direction of `V_θ` is
  flat for the residual network at every input of `residualZeroDomain`),
  `funDimOn_add_le_residual_19` (for `E` of rank `d`: `funDimOn + co + dim V_θ ≤ P`) and
  `funDimOn_residual_eq_19` (under the hypotheses of the library's statement:
  `funDimOn + co + dim V_θ = P`). By a computation: in all 93 cases the rank of the residual
  network was `P − co −` (the bound of `dim V_θ`).
- **The skipless count.** The paper (S line 3001 to 3006): "the directions of `V_θ` are flat, and
  so are the changes of basis in `CO(d_model)` at `h_0` and at `h_1` … the scaling lies in `V_θ`
  only if the block vanishes on the sphere. So the skipless network has functional dimension at
  most `P − 2 dim CO(d_model) − dim V_θ`." Lean: the same inequality, with the paper's condition
  as `hB` ("the block is not zero at some `n` on the sphere") and `E`, `D` of rank `d` (the
  paper's "so `Y_0 = 0`, `c_0 = 0` and `Y_1 = 0`" uses them). SAME. This statement has no
  hypothesis on `d`.
- **`d(d−1)/2` in `ℕ`.** By compiling (`two_mul_choose19`): `2 * (n * (n - 1) / 2) = n * (n - 1)`
  for every natural `n`, so the division is exact (also for `n = 0`, where the truncated `0 - 1`
  is `0`). `co` is 2, 4 for `d = 2, 3`.
- **The gain at one parameter** (`funDimOn_skipless_add_le_funDimOn_residual_rmsNorm_zero`) has
  the hypotheses of the residual count and no `hB`. By reading: at the `w` of `hw` every row of
  `w E` is nonzero, so the rows of `n = N_0(w E)` are on the sphere, and every row of
  `f(n W_read) W_write` is nonzero (each is a member of an independent pair), so the block is not
  zero at `n` (a token exists: `[Nonempty T]`). The two counts then give
  `fd_skipless + 2 co + dim V_θ ≤ P ≤ fd_residual + co + dim V_θ`, with the same `V_θ` on both
  sides. This is the paper's "The bound then holds whatever `V_θ` is".
- By a computation, at parameters that are not generic but satisfy the hypotheses
  (`rz19special.py`, 19 cases; `E`, `D` of rank `d` and the independence of `hw` checked in each):
  two equal hidden units, a hidden unit with write row zero, with read column zero, all write rows
  on one line, two tanh units that cancel, attention with all queries zero, with a head whose
  values are zero. In all 19 the three inequalities hold with the computed numbers; `dim V_θ` is
  larger there (for instance 4 for two equal tanh units at `d = 2`) and the residual rank is lower
  by the same amount.

### Check 7. `Symmetry/FiniteSymmetriesCompose.lean`

**Verdict: all 32 are identities between the stated definitions, or statements that a finite
symmetry preserves the function, with natural hypotheses. None is vacuous. The five named in the
brief say what the row of the index says. One phrase of the row is loose (see the corrections).**
(By reading the statements and the definitions; the signatures from `Sig.out`.)

- The sentences they serve. D Definition 4.5 (line 352) and S Definition 4.4 (line 457): "the
  image of `θ` under a symmetry: a change of basis …, a symmetry inside a block, or a composition
  of these." D line 933: "With the permutations and the sign flips, the symmetries form a Lie
  group of dimension `k` with finitely many components". D lines 840 to 841: "Permutations of
  hidden units or heads and sign flips of tanh hidden units are finite and remove no parameters".
  The library's equivalences have the symmetries in one order (a finite symmetry, then the
  continuous symmetries inside the blocks, then a change of basis); the 21 identities of
  composition are what brings a composition in any order to that order. For each kind of block
  the set is complete, by reading: MLP (`permUnits_permUnits`, `flipUnits_flipUnits`,
  `flipUnits_permUnits`, `cob_permUnits`, `cob_flipUnits`, `cob_cob`); gated
  (`permUnitsGated_permUnitsGated`, `rescale_rescale`, `rescale_permUnitsGated`,
  `cob_permUnitsGated`, `cob_rescale`, `cob_cob`); attention (`permHeads_permHeads`,
  `headsQK_headsQK`, `headsVO_headsVO`, `headsVO_headsQK`, `headsQK_permHeads`,
  `headsVO_permHeads`, `cob_permHeads`, `cob_headsQK`, `cob_headsVO`, `cob_cob`). That every
  composition is reduced by them is an induction that is not a Lean statement, as the header and
  the row say.
- The five named in the brief:
  - `eval_sumOf_of_blocks`: for `θ` of `A.sum B`, `a` of `A` and `b` of `B` with `a.E = θ.E`,
    `a.D = θ.D`, if `a` gives every block of `A` the output that `θ.sumFst` gives and `b` every
    block of `B` the output that `θ.sumSnd` gives (on every state `h`), then
    `eval (A.sum B) S (sumOf a b) x = eval (A.sum B) S θ x` for all `S`, `x`. The row: "the lemma
    that maps on the two parts which leave every block unchanged leave the function unchanged".
    Yes. (`sumOf a b` takes `E` and `D` from `a`, so nothing is asked of `b.E`, `b.D`.)
  - `eval_attentionMlp_perm`: `eval … S (sumOf (θ.sumFst.permHeads q) (θ.sumSnd.permUnits p)) x
    = eval … S θ x`, for all permutations of heads and of hidden units, all stream matrices, all
    `χ`, `σ`. `eval_attentionMlp_perm_flip`: the same with
    `(θ.sumSnd.permUnits p).flipUnits s`, under `hσ : ∀ z, σ (-z) = -σ z` (tanh has it).
    `eval_attentionGated_perm`: with `permUnitsGated`. The row: "For networks of attention blocks
    and MLP or gated blocks the finite symmetries preserve the function (the maps on the two
    parts …)". Yes.
  - `sumOf_cob`: `(sumOf a b).cob G K = sumOf (a.cob G K) (b.cob G K)`. "A change of basis acts
    on the two parts." Yes.
- **Vacuous?** No hypothesis is unsatisfiable: the only hypotheses are `hσ` (odd activation), the
  equalities `b.E = a.E`, `b.D = a.D` of `sumFst_sumOf` (needed: `sumOf a b` forgets `b.E` and
  `b.D`), and the hypotheses of the two general lemmas. `rescale_rescale` and
  `rescale_permUnitsGated` hold for all factors, zero included (in Lean `0⁻¹ = 0`); a rescaling is
  a symmetry only for nonzero factors, and that is a hypothesis of `eval_rescale_params`, not of
  these identities. Three are proved by `rfl` (`permUnits_permUnits`, `flipUnits_permUnits`,
  `permHeads_permHeads`): the maps are defined by re-indexing, and the content is which
  permutation appears on the right (`p ℓ * p' ℓ`, that is `i ↦ p ℓ (p' ℓ i)`; the signs
  `s ℓ (p ℓ i)`). They are not trivial in the sense of the brief.

---------------------------------------------------------------------------------------------------

## Part 2: the statements, file by file

### `OneBlock/ResidualRMSZeroSteps.lean` (1 definition, 1 theorem)

| Lean name | Paper | Verdict |
|---|---|---|
| `residualZeroDomain` | S Appendix B, "Notation and flat directions" (line 2367): "With `ε = 0`, it also excludes the inputs at which a state that is normalized vanishes", for the residual network of one block | SAME (read row by row; Check 2) |
| `exists_antisymm_scale_of_flatOn_residual_rmsNorm_zero` | S proof of Theorem B.1 (v), "The residual network" (lines 2969 to 2998), up to "so `η″ ∈ V_θ`" | SAME as a proof piece: "generic parameters" is the three conditions `hE`, `hD`, `hw`; the block is any analytic map `f` (the five kinds are such), any number of tokens. `hd` is implied by `hw` (Check 5) |

### `OneBlock/ResidualRMSZeroGain.lean` (3 definitions, 3 theorems)

| Lean name | Paper | Verdict |
|---|---|---|
| `funDimOn` | S "Notation and flat directions": the functional dimension, with "every input" restricted to a set | SAME (a maximum; Check 2) |
| `skiplessZeroDomain` | the same sentence (line 2367) for the skipless network of one block | SAME |
| `blockFlatSphere` | S line 2964, `V_θ` | SAME (Check 3) |
| `finrank_le_funDimOn_residual_rmsNorm_zero` | S line 2999: "the residual network has functional dimension `P − dim CO(d_model) − dim V_θ`" | PART: the inequality "at least" of the paper's equality; LEAN WEAKER than the sentence, and what the theorem needs. The other inequality is true (compiled by me, Check 6) |
| `funDimOn_add_le_skipless_rmsNorm_zero` | S lines 3001 to 3006: "the skipless network has functional dimension at most `P − 2 dim CO(d_model) − dim V_θ`" | SAME, with the paper's conditions as hypotheses (`E`, `D` of rank `d`; the block not zero at a point of the sphere) |
| `funDimOn_skipless_add_le_funDimOn_residual_rmsNorm_zero` | S line 2968 "The bound then holds whatever `V_θ` is" and line 3010 "the skip adds at least `dim CO(d_model) = d_model (d_model − 1)/2 + 1`", at one parameter | SAME as a proof piece (at every `θ` with `hE`, `hD`, `hw`, not only at generic ones). `hd` is implied by `hw` |

### `OneBlock/ResidualRMSZeroKinds.lean` (10 theorems)

| Lean name | Paper | Verdict |
|---|---|---|
| `ae_exists_linearIndependent_rows_mlp` | S line 2984: "For generic parameters `w E` and `g(w)` are linearly independent for all `w` in an open set" | SAME in substance (one `w`, for every token; the open set follows by continuity). LEAN STRONGER in scope: every continuous activation that is nonzero on the positive reals, at least one hidden unit |
| `ae_exists_linearIndependent_rows_gated` | the same, gated blocks | the same |
| `ae_exists_linearIndependent_rows_attention` | the same, attention blocks | SAME in substance. LEAN STRONGER in scope: any mask in which every token sees some token, any number of tokens, any positive head width |
| `ae_funDimOn_skipless_add_le_mlp_oneBlock_residual_rmsNorm_zero` | S Theorem B.1 (v) | LEAN STRONGER: every analytic activation that is nonzero on the positive reals |
| `…_tanh_…` | S Theorem B.1 (v), tanh | SAME |
| `…_gelu_…` | S Theorem B.1 (v), GELU | SAME |
| `…_gated_…` | S Theorem B.1 (v) | LEAN STRONGER: every analytic gate that is nonzero on the positive reals |
| `…_swiglu_…` | S Theorem B.1 (v), SwiGLU | SAME |
| `…_geglu_…` | S Theorem B.1 (v), GeGLU | SAME |
| `…_attention_…` | S Theorem B.1 (v), attention | LEAN STRONGER: no `d_h ≤ d_model`, no "at least two tokens", any mask in which every token sees some token |

For the four SAME rows: the paper's part (v) has no condition on the width of the block, and Lean
has none beyond one hidden unit. In all seven the functional dimension is `funDimOn` on the sets
of Check 2, on both sides at the same `θ`.

### `Symmetry/FiniteSymmetriesCompose.lean` (32 theorems)

All 32: a true identity, or a statement that a map preserves the function, between the stated
definitions; hypotheses as listed; none vacuous. "Serves": C = "or a composition of these"
(D Definition 4.5, S Definition 4.4) and D line 933; F = "Permutations of hidden units or heads
and sign flips of tanh hidden units are finite" (D lines 840 to 841), as symmetries.

| Lean name | What it says | Hypotheses | Serves |
|---|---|---|---|
| `permUnits_permUnits` | `(θ.permUnits p).permUnits p' = θ.permUnits (p * p')` | none | C |
| `flipUnits_flipUnits` | two sign flips are the flip by the product of the signs | none | C |
| `flipUnits_permUnits` | `(θ.flipUnits s).permUnits p = (θ.permUnits p).flipUnits (s ∘ p)` | none | C |
| `cob_permUnits` | a change of basis commutes with a permutation of the hidden units | none | C |
| `cob_flipUnits` | a change of basis commutes with a sign flip | none | C |
| `permUnitsGated_permUnitsGated` | gated: two permutations are the product | none | C |
| `rescale_permUnitsGated` | `(θ.rescale c).permUnitsGated p = (θ.permUnitsGated p).rescale (c ∘ p)` | none | C |
| `rescale_rescale` | two rescalings are the rescaling by the product of the factors | none (all factors) | C |
| `rescale_neg_one` | the rescaling by `−1`: value column and write row times `−1`, gate column unchanged | none | C; D Appendix B, gated: "`λ ≠ 0`" contains the sign change |
| `cob_permUnitsGated` | a change of basis commutes with a permutation of gated units | none | C |
| `cob_rescale` | a change of basis commutes with a rescaling | none | C |
| `permHeads_permHeads` | two permutations of the heads are the product | none | C |
| `headsQK_permHeads` | `(θ.headsQK K).permHeads q = (θ.permHeads q).headsQK (K ∘ q)` | none | C |
| `headsVO_permHeads` | the same for values and outputs | none | C |
| `headsVO_headsQK` | the two changes of basis inside the heads commute | none | C |
| `cob_cob` | `(θ.cob G K).cob G' K' = θ.cob (G * G') (K * K')`, any architecture | none | C |
| `cob_permHeads` | a change of basis commutes with a permutation of the heads | none | C |
| `cob_headsQK` | a change of basis commutes with a change of basis between queries and keys | none | C |
| `cob_headsVO` | a change of basis commutes with a change of basis between values and outputs | none | C |
| `headsVO_headsVO` | two changes of basis between values and outputs are the product | none | C |
| `headsQK_headsQK` | two changes of basis between queries and keys are the product | none | C |
| `eval_eq_of_blocks` | same `E`, `D` and same output of every block on every state give the same function, for all stream matrices | the three equalities | F (lemma) |
| `eval_sumOf_of_blocks` | the same for maps on the two parts of `A.sum B` | `a.E = θ.E`, `a.D = θ.D`, the two block equalities | F (lemma) |
| `block_permUnits` | a permutation of the hidden units leaves every MLP block unchanged | none | F |
| `block_flipUnits` | a sign flip leaves every MLP block unchanged | `σ` odd | F ("sign flips of tanh hidden units") |
| `block_permUnitsGated` | a permutation leaves every gated block unchanged | none | F |
| `block_permHeads` | a permutation of the heads leaves every attention block unchanged | none | F |
| `eval_attentionMlp_perm` | attention and MLP blocks: permutations of heads and of hidden units preserve the function | none | F |
| `eval_attentionMlp_perm_flip` | the same with sign flips | `σ` odd | F |
| `eval_attentionGated_perm` | attention and gated blocks: permutations preserve the function | none | F |
| `sumFst_sumOf` | the two parts of `sumOf a b` are `a` and `b` | `b.E = a.E`, `b.D = a.D` | C (maps on the two parts compose part by part) |
| `sumOf_cob` | a change of basis acts on the two parts | none | C |

Verdict for the paper sentences: the sentence "or a composition of these" is served by identities
and not stated as closure under composition (PART, as the header and the row say); the sentence on
the finite symmetries is SAME for networks of attention blocks and MLP or gated blocks (for one
kind of block it is in `Symmetry/FiniteSymmetries.lean`, not audited here).

### The index and the axiom file

- Every public name of the four files is in a row of `STATEMENTS.md` (lines 825, 839, 840, 841
  at `65a02a6`).
  Six names of line 841 are written short (`…_tanh_…`, `…_gelu_…`, `…_gated_…`, `…_swiglu_…`,
  `…_geglu_…`, `…_attention_…`), as elsewhere in the index; in full they are
  `ae_funDimOn_skipless_add_le_tanh_oneBlock_residual_rmsNorm_zero` and so on.
- Every one of the 46 theorems has a `#print axioms` line in `checks/Axioms.lean` (by a search of
  the file for each name).
- The four files are imported by `SkipsLean.lean` (lines 279 to 282 at `65a02a6`).
- I found nothing wrong in the four rows. Two phrases to tighten and two additions are under
  "Corrections".

---------------------------------------------------------------------------------------------------

## What the authors of the papers should know

Nothing false, vacuous, drifted or misdescribed was found. In order of weight:

1. **The count for the residual network is one inequality.** The paper's proof says "the residual
   network has functional dimension `P − dim CO(d_model) − dim V_θ`". The library proves "at
   least". The other inequality is true and short (the directions of `CO(d)` and of `V_θ` are flat
   for the residual network at the inputs of the set, and independent when `E` has rank `d`): I
   compiled it and the equality (`Chk2.lean`: `funDimOn_add_le_residual_19`,
   `funDimOn_residual_eq_19`), and the equality held in all 93 computed cases. Part (v) itself
   needs only "at least".
2. **`d ≥ 2` is implied by the condition on the input `w`** in the three statements at one
   parameter (Steps, the residual count, the gain): two linearly independent rows need `d ≥ 2`.
   The header of `ResidualRMSZeroSteps.lean` says the hypothesis "is needed (for `d = 1` the step
   "`η′_E = c E`" fails)"; for `d = 1` the statement is empty because no `w` exists. In the seven
   statements for generic parameters `d ≥ 2` is a real hypothesis (it is the Scope's, and the
   input `w` is found from it).
3. **The paragraph "Generic parameters" of the proof is not a Lean statement, and is not used.**
   "The dimension of `V_θ` … takes its smallest value `v` for generic parameters. The generic
   functional dimensions are therefore `P − dim CO(d_model) − v` with the skip and at most
   `P − 2 dim CO(d_model) − v` without it". Lean compares the two networks at the same `θ` with
   the same `V_θ`, at every `θ` that has `E`, `D` of rank `d` and the input `w`, and then shows
   that almost every `θ` is such. So Lean's theorem is "for almost every `θ`, residual at `θ`
   ≥ skipless at `θ` + `d(d−1)/2 + 1`"; it does not say that either functional dimension is
   generically constant or what its value is. Also not a statement of these files: "it [`V_θ`]
   contains the symmetries inside the block" (the computed `dim V_θ` equals the paper's `s` in the
   cases of the paper's scope).
4. **Lean's scope is wider than the theorem's**, and the statements hold there: blocks with any
   number of hidden units from one (part (v) has no width condition either); any number of tokens
   from one, for attention too; heads of any positive width (`d_h > d_model` included); any mask
   in which every token sees some token; for MLP and gated blocks every analytic activation or
   gate that is nonzero on the positive reals. Computed: with one token the attention block is
   linear and the gain is `d²` when `H d_h ≥ d`; with one hidden unit the skipless network has rank
   `d_out`.
5. **"A state that is normalized vanishes" is read row by row:** an input is in the set if no row
   (token) of `h_0` and of `h_1` is zero. For several tokens this is the reading under which `N_0`
   is defined. The paper's sentence could say "a row of a state".
6. **The bound of part (v) is attained in the computed cases of the paper's scope whose block has
   width at least `d_model`** (for attention: at least two tokens, causal or not): there the gain
   was exactly `d(d−1)/2 + 1` (39 of 74 cases at random parameters), and the skipless rank was
   exactly `P − 2 (d(d−1)/2 + 1) − dim V_θ`. In the other 35 cases (narrower blocks; attention on
   one token or with a mask that lets every token see one token only) the gain was larger. These
   are computed ranks on batches, not proofs.

## Corrections for `STATEMENTS.md` (line numbers of `65a02a6`; at `27b81a1` each row is one line lower)

1. **Lines 207 to 211** (207 to 212 at `27b81a1`: "Not yet compared by such a reader (written
   after the eighteenth audit began): `OneBlock/ResidualRMSZeroSteps.lean`, … its statements were
   read by the coordinator only), which are with the reader of the nineteenth audit …"): the four
   files have now been compared (this report): nothing false, vacuous or drifted;
   the residual count is the lower bound of the paper's equality; `d ≥ 2` follows from the input
   `w` in the statements at one parameter.
2. **Line 825** (the row of `Symmetry/FiniteSymmetriesCompose.lean`): "a permutation or a sign
   flip moves inside past a sign flip, a rescaling, a change of basis inside the heads" should be
   "a permutation moves inside past a sign flip, a rescaling, a change of basis inside the heads".
   There is no identity in which a sign flip moves past a rescaling or a change of basis inside the
   heads, and none is needed: no block has sign flips together with either. The row could also
   say what `sumFst_sumOf` and `sumOf_cob` are for (on a network with two kinds of block, the maps
   on the two parts compose part by part, and a change of basis acts on the two parts).
3. **Line 840** (the row of `OneBlock/ResidualRMSZeroGain.lean`): after "the residual network has
   functional dimension at least `P − (d(d−1)/2 + 1) − dim V_θ`" add that the paper states an
   equality here and that the other inequality is not a Lean statement (it is true; this report,
   Check 6).
4. **Lines 839 and 840**: "for `d ≥ 2`, `E` and `D` of rank `d`, and one input `w` …": `d ≥ 2`
   follows from the input `w` (optional remark). The same remark belongs in the header of
   `OneBlock/ResidualRMSZeroSteps.lean` in place of "is needed (for `d = 1` the step … fails)".
   This is a sentence of a file header, not of the index, and I did not edit it.
5. **Line 841**: nothing to correct. The six short names could be written in full.

## What I could not check

- The proofs. I read statements and definitions. The private helpers of the library (the
  differentiability of the output at the inputs of the two sets, the membership of `V_θ` as three
  conditions) I checked only where I proved the same fact myself in a scratch file.
- Whether Lean's `funDim` (all inputs, with `rmsNorm 0` of a zero row equal to `0`) differs from
  `funDimOn` on the two sets. The index says that it may; I did not compute it. `funDimOn` is the
  quantity of the paper.
- The induction "every composition of the symmetries is reduced to the one order": it is not a
  Lean statement; I checked by reading that the identities for each kind of block are enough.
- The computations cover `d = 2, 3`, up to four hidden units, up to two heads, up to three tokens,
  93 cases. They support the inequalities and the equality of the residual count; they prove
  nothing. The rank of a Jacobian on a batch is a lower bound, and I report each rank only where
  two batches gave the same value.
- The pages of the PDFs: I read the papers as text (`skips.txt`, `dim.txt`), with the formulas as
  the text extraction gives them.

## Files of this audit (in `/home/claude/audit19/`)

`Sig.lean`, `Sig.out` (signatures and axioms of the 50 names); `Chk.lean`, `Chk.out` (Checks 1,
2, 3, 5, 6); `Chk2.lean`, `Chk2.out` (Check 3, the derivative; Check 6, the other inequality of
the residual count); `rz19core.py`, `rz19run.py`, `rz19special.py`, `rz19fd.py`; `rz19_tanh.out`,
`rz19_other.out`, `rz19_attn1.out`, `rz19_attn2.out`, `rz19_special.out`, `rz19fd.out`.
