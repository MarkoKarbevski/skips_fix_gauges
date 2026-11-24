STATUS: complete

# Tenth audit of Lean statements against the papers, part A (24 November 2026)

Reader: an independent reader who did not write the statements. Brief:
`/home/claude/proj_up/audit10a_brief_2026-11-24.md`. Subject: dead units and folding.

Library: `/home/claude/lw/lean` (branch `lean-wip`). Commit at the start: `8dc41d9`. Commit at the
end: `a2e3143`. Between the two, the nine files of the brief and the files that define what they
use (`Network/Defs.lean`, `Network/Blocks.lean`, `Dimension/Functional.lean`, `Dimension/Space.lean`,
`Generic/Params.lean`, `Generic/Gated.lean`, `Dimension/RescalingMlp.lean`,
`Dimension/RescalingGate.lean`, `Residual/UpperBoundSymmetries.lean`, `Activations/ReLU.lean`) did
not change (`git diff --quiet 8dc41d9 HEAD` on each). Line numbers of `STATEMENTS.md` below are
those of `a2e3143`.

Papers: the dimension paper ("D", `dim.txt`) and the skips paper ("S", `skips.txt`), as text.

How I checked.

- "By reading": I read the nine Lean files in full, and the paper passages (D Appendix E with
  Proposition E.1 and its proof; D Section 2 "Scope", Definitions 4.1 and 4.4, Lemma B.1; S
  Appendix A.8 with Definition A.31, Propositions A.32, A.33, A.35, Remark A.34 and the proofs; S
  Section 2 "Scope", Definition 4.3, Lemma A.18).
- "By compiling": scratch files of my own in `/home/claude/audit10a/` (`Chk.lean` to `Chk5.lean`,
  outputs `Chk*.out`), compiled with `lean` 4.36.0 through `LEAN_PATH`, without `lake`. The
  compiled library of `/home/claude/lw` has none of the nine files. I used a copy
  (`/home/claude/audit10a/snap`, made at 12:55 UTC) of the compiled library of `/home/claude/lp/lean`,
  whose sources under `SkipsLean/` were the same as those of `lw` at that time (`diff -rq`, no
  difference). I did not run `lake build` and wrote nothing under `lw`, `lp` or the repository.
- "By a computation": `/home/claude/audit10a/py/ranks.py` (numpy, double precision), output
  `ranks.out`.

Short answer. **Nothing false, vacuous or changed in meaning was found in the nine files.** The
21 public theorems have the statements that I read in the sources (`Chk.out`), and each depends on
the three standard axioms only (`#print axioms`, `Chk.out`). The open sets are open and nonempty in
the space of all parameters; "at almost every point of the set" is `∀ᵐ θ ∂μ, θ ∈ U → …` for any
additive Haar measure; the constants `2d − 1`, `3d − 2` and `(2d − 1)ν` are the papers'. Lean has
fewer hypotheses than Proposition E.1 of D. Three things differ from the skips paper and are
listed below: Proposition A.35 of S is not word for word Proposition E.1 of D (width of the block
of the dead unit; "on it" against "at almost every point"), Proposition A.33 (ii) is stated under
more hypotheses than the paper's sentence, and Proposition A.32 (i), (ii) rest on invariance of
domain as an unproved hypothesis.

---------------------------------------------------------------------------------------------------

## Part 1: the three drift checks

### Check 1. Open sets are open and nonempty in the space of all parameters; "almost every point" is `∀ᵐ`

**Verdict: yes, in every main statement. Lean has no hypothesis that Proposition E.1 of D or
Proposition A.33 (i) of S does not have.** (By reading; the signatures by compiling, `Chk.out`.)

The four statements with an open set, as in the sources:

```
theorem exists_isOpen_unitInactive_relu [Nonempty d]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut)) [μ.IsAddHaarMeasure]
    (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hhid : ∀ m, Fintype.card d ≤ Fintype.card (hid m)) (ℓ : Fin L) (j : hid ℓ.succ)
    (hj : Fintype.card d < Fintype.card (hid ℓ.succ)) :
    ∃ U : Set (Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut),
      IsOpen U ∧ U.Nonempty ∧ (∀ θ ∈ U, UnitInactive θ ℓ.succ j) ∧
      ∀ᵐ θ ∂μ, θ ∈ U → funDim (Arch.mlp relu id hid) 0 θ
          + ((L + 2) * Fintype.card d ^ 2 + ∑ m, Fintype.card (hid m) + (2 * Fintype.card d - 1))
        ≤ Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut)
```

(`exists_isOpen_unitInactive_reluSq` is the same with `reluSq`.)

```
theorem exists_isOpen_gateInactive_reglu_bound [Nonempty d]
    (μ : Measure (Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hhid : ∀ m, Fintype.card d ≤ Fintype.card (hid m)) (ℓ : Fin L) (j : hid ℓ.succ)
    (hj : Fintype.card d < Fintype.card (hid ℓ.succ)) :
    ∃ U : Set (Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut),
      IsOpen U ∧ U.Nonempty ∧ (∀ θ ∈ U, GateInactive θ ℓ.succ j) ∧
      ∀ᵐ θ ∂μ, θ ∈ U → funDim (Arch.gated relu id hid) 0 θ
          + ((L + 2) * Fintype.card d ^ 2 + 2 * ∑ m, Fintype.card (hid m)
            + (3 * Fintype.card d - 2))
        ≤ Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut)

theorem exists_isOpen_gateInactive_reglu [Nonempty d] (ℓ : Fin L) (j : hid ℓ.succ)
    (hq : Fintype.card d ≤ Fintype.card (hid ℓ.castSucc)) :
    ∃ U : Set (Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut),
      IsOpen U ∧ U.Nonempty ∧ ∀ θ ∈ U, GateInactive θ ℓ.succ j

theorem exists_isOpen_folds_unitInactiveRes_relu [Nonempty d] (ℓ : Fin L) (j : hid ℓ.succ)
    (hq : Fintype.card d ≤ Fintype.card (hid ℓ.castSucc)) :
    ∃ U : Set (Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut),
      IsOpen U ∧ U.Nonempty ∧ ∀ θ ∈ U, Folds θ ℓ.castSucc ∧ UnitInactiveRes θ ℓ.succ j
```

Here `hid : Fin (L + 1) → Type`: the network has `L + 1` blocks, and `ℓ : Fin L` exists only if
`L ≥ 1`, so there are at least two blocks. The paper's blocks 1 and 2 are `ℓ.castSucc` and
`ℓ.succ`.

What the words mean in Lean.

- **The set is a set of all parameters.** `U : Set (Params A dIn dOut)`, and `Params` holds `E`,
  every read, every write and `D` (`Network/Defs.lean:41-49`). No parameter is fixed and no
  subspace is taken.
- **Open.** `IsOpen U` in the topology of `Params A dIn dOut`, which is that of its norm
  (`Dimension/Space.lean:100-107`: a norm induced by a linear equivalence with a product of matrix
  spaces; the space has finite dimension, so this is the usual topology of `ℝ^P`).
- **Nonempty.** `U.Nonempty`. For ReLU and ReLU² the set is `negReadSet` (`a_k r < 0` for all `k`),
  with `isOpen_negReadSet` and `nonempty_negReadSet`, which ask only `d ≥ 1`. For ReGLU and for
  Proposition A.33 (i) the set is the interior of the set of weights with the property, shown
  nonempty at the weights of the paper's proof.
- **"At almost every point of this set".** `∀ᵐ θ ∂μ, θ ∈ U → …`, with `μ` any additive Haar measure
  on the parameters (`(μ) [μ.IsAddHaarMeasure]`). For an open `U` this is `∀ᵐ θ ∂(μ.restrict U), …`
  (by compiling, `Chk2.lean`, example (a)). The same `U` carries both claims of the proposition.
  A nonempty open set has positive Haar measure, so the claim is not empty.

Hypotheses, Lean beside the paper.

| Statement | Paper's hypotheses | Lean's hypotheses | Does Lean have one the paper does not? |
|---|---|---|---|
| D Proposition E.1, open set and bound, ReLU, ReLU² (`exists_isOpen_unitInactive_relu`, `…_reluSq`) | `L ≥ 2` blocks; no normalization; every block has more than `d_model` hidden units; a hidden unit of block 2; from the Scope of D: `d_in, d_out ≥ d_model ≥ 2`; `T = 1` | at least 2 blocks; `χ = id`; every block has at least `d` hidden units and block `ℓ.succ` has more than `d`; any block `ℓ.succ` after the first, any unit `j` of it; `d_in ≥ d ≥ 1`; nothing on `d_out`; any finite `T` | No. Lean asks less: `≥ d` in the other blocks, `d ≥ 1`, no condition on `d_out` |
| D Proposition E.1, ReGLU (`exists_isOpen_gateInactive_reglu_bound`) | the same | the same | No |
| D Proposition E.1, "So these networks do not satisfy the equality condition" (`not_ae_funDim_add_eq_relu_skipless`, `…_reluSq_skipless`, `…_reglu_skipless`) | the same | `0 < L` (at least 2 blocks); more than `d` hidden units in every block; `d_in ≥ d ≥ 1` | No |
| S Proposition A.33 (i) (`exists_isOpen_folds_unitInactiveRes_relu`) | residual networks of `L ≥ 2` ReLU blocks, no normalization; Scope of S: every block has `d_hidden ≥ d_model`, `d_in, d_out ≥ d_model ≥ 2` | at least 2 blocks; block `ℓ.castSucc` has at least `d` units; block `ℓ.succ` has the unit `j`; `d ≥ 1` | No. Lean asks less |
| S Proposition A.35 (the same Lean statements as for E.1) | skipless networks of `L ≥ 2` blocks; Scope of S: every block has `d_hidden ≥ d_model` | block `ℓ.succ` has **more than** `d` hidden units | **Yes, one:** more than `d` units in the block of the dead unit. And Lean's bound is at almost every point, A.35 says "On it". See Part 2, note 2 |

Instance arguments such as `[DecidableEq d]` and `[∀ ℓ, DecidableEq (hid ℓ)]` are technical.

### Check 2. `funDim` is the library's `funDim`; the bounds imply the paper's bounds

**Verdict: yes.** (By reading; three implications by compiling.)

- Every bound of the nine files is on `funDim A S θ` of `Dimension/Functional.lean:29-49`, with
  `S = 0` (no skips) or `S = 1` (identity skips). No other notion of dimension is defined in these
  files. `funDim` is the supremum over all finite batches of the rank of the Fréchet derivative of
  the outputs in `θ`, and Mathlib's derivative is `0` where the map is not differentiable (sixth
  audit, Part 1, Check 2).
- **Each Lean bound implies the paper's bound.** The paper takes the Jacobian on a batch at which
  no hidden unit sits at its kink. At such inputs the network is differentiable in `θ` (by
  reading: near `θ` the signs of the pre-activations on the batch do not change, so the outputs
  are polynomial in `θ`), so Lean's `jacobianRank` on this batch is the paper's rank, and
  `jacobianRank_le_funDim : jacobianRank A S X θ ≤ funDim A S θ` for every batch `X`. Hence a
  bound `funDim θ + c ≤ P` gives `rank DF_X(θ) + c ≤ P` on every batch of the paper. By
  compiling (`Chk2.lean`, example (d)): from `exists_isOpen_unitInactive_relu` and
  `jacobianRank_le_funDim`, the same open set with, at almost every point of it, the bound on
  `jacobianRank … X θ` for every `n` and every batch `X`.
- **"The equality condition fails."** D Definition 4.4: "A network satisfies the equality condition
  if the bound of Theorem 4.3 is attained at generic parameters". Lean:

  ```
  theorem not_ae_funDim_add_eq_relu_skipless [Nonempty d]
      (μ : Measure (Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut)) [μ.IsAddHaarMeasure]
      (hL : 0 < L) (hdIn : Fintype.card d ≤ Fintype.card dIn)
      (hhid : ∀ m, Fintype.card d < Fintype.card (hid m)) :
      ¬ ∀ᵐ θ ∂μ, funDim (Arch.mlp relu id hid) 0 θ
          + ((L + 2) * Fintype.card d ^ 2 + ∑ m, Fintype.card (hid m))
        = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut)
  ```

  This is "it is not the case that `fd = P − (L+1)d² − s` at almost every parameter" (the paper's
  `L` is Lean's `L + 1`), for Lean's `funDim`. It is the negation of Definition 4.4, word for
  word, for the library's `funDim`. For the paper's functional dimension, which is at most Lean's,
  the same negation follows, because Lean's `funDim` is at most the bound almost everywhere
  (`ae_funDim_add_le_skipless_relu`). By compiling (`Chk4.lean`, `not_ae_paper_relu`): for any
  `fdp` with `fdp θ ≤ funDim … θ` for all `θ`, `¬ ∀ᵐ θ ∂μ, fdp θ + ((L+2)d² + s) = P`, from the
  two library statements, with the three standard axioms. I compiled this for ReLU only; the
  ReLU² and ReGLU cases have the same form and the library has the same upper bounds
  (`ae_funDim_add_le_skipless_reluSq`, `ae_funDim_add_le_skipless_reglu`; by reading).
  The paper proves more than the negation (a nonempty open set on which the bound is missed);
  that is the `exists_isOpen_…` statement.

### Check 3. The definitions

**Verdict: the definitions are the papers'.** (By reading; the unfolded definitions by compiling,
`#print` in `Chk.out`.)

```
def UnitInactive (θ) (m : Fin L) (j : hid m) : Prop :=
  ∀ (x : Matrix T dIn ℝ) (t : T), (hidden (Arch.mlp σ id hid) 0 θ x m.castSucc * θ.read m) t j ≤ 0
def GateInactive (θ) (m : Fin L) (j : hid m) : Prop :=
  ∀ (x : Matrix T dIn ℝ) (t : T), (hidden (Arch.gated σ id hid) 0 θ x m.castSucc * θ.read m) t (Sum.inl j) ≤ 0
def UnitInactiveRes (θ) (m : Fin L) (j : hid m) : Prop :=
  ∀ (x : Matrix T dIn ℝ) (t : T), (hidden (Arch.mlp σ id hid) 1 θ x m.castSucc * θ.read m) t j ≤ 0
def negReadSet … (ℓ : Fin L) (j : hid ℓ.succ) : Set (Params (Arch.mlp σ χ hid) dIn dOut) :=
  {θ | ∀ k : hid ℓ.castSucc, (θ.write ℓ.castSucc *ᵥ fun a => θ.read ℓ.succ a j) k < 0}
def blockMapRes (θ) (ℓ : Fin L) (h : d → ℝ) : d → ℝ :=
  h + (fun i => σ ((h ᵥ* θ.read ℓ) i)) ᵥ* θ.write ℓ
def Folds (θ) (ℓ : Fin L) : Prop := ¬ Function.Injective (blockMapRes θ ℓ)
def InvarianceOfDomain (n : Type*) [Fintype n] : Prop :=
  ∀ f : (n → ℝ) → (n → ℝ), Continuous f → Function.Injective f → IsOpenMap f
```

- **Inactive, dead: `≤ 0`, and this is the paper.** S: "The unit is active at `x` if `z_i(x) > 0`
  … A unit is dead if it is active at no input." D: "It is positive at no input". "Active at no
  input" is `z ≤ 0` at every input: Lean's `≤ 0`. With `< 0` the definition could never hold (the
  input `0` gives `z = 0`). For ReLU and ReLU² the difference between `z = 0` and `z < 0` does not
  matter for the function: the statements assume `∀ z ≤ 0, σ z = 0`, so a unit that reads `≤ 0`
  everywhere adds nothing. `(hidden … * θ.read m) t j` is the pre-activation `h_{m−1}(x) r_j` of
  token `t`; "every token of every input" is "every input" of the paper, which takes `T = 1`. With
  no token the three definitions hold for every unit (see Part 2, degenerate cases).
- **"For parameters near `θ`" is not in the definitions.** The definitions are at `θ`. "Near `θ`"
  is the hypothesis `∀ᶠ θ' in 𝓝 θ, UnitInactive θ' m j` of the bounds at one parameter. For
  Proposition E.1 it is in the paper: "On this open set of weights … the columns of the Jacobian
  that belong to the weights of the inactive hidden unit vanish". For Proposition A.33 (ii) it is
  not in the paper's sentence ("If `ν` units are dead"); the file header and the index say so
  (Part 2, note 3).
- **`negReadSet`** is the paper's "`a_k r < 0` for all `k`": `(W_write *ᵥ r) k` is the write row
  `a_k` of unit `k` of the first of the two blocks times the read column `r` of unit `j` of the
  next.
- **`blockMapRes` and `Folds` are Definition A.31.** `Φ_ℓ(h) = h + σ(h W_read) W_write` on a row
  `h`, and "folds" is "`Φ_ℓ` is not injective". `hidden_succ_eq_blockMapRes` says that a row of
  the next hidden state of the residual network (`hidden … 1 …`) is `Φ_ℓ` of the row before: the
  definition is tied to the network and is not a separate object.
- **`InvarianceOfDomain n`** against Brouwer's theorem ("if `U` is an open subset of `ℝ^n` and
  `f : U → ℝ^n` is injective and continuous, then `f(U)` is open and `f` is a homeomorphism onto
  it"). The Lean `Prop` is the case of maps defined on all of `ℝ^n`: "an injective continuous map
  of `ℝ^n` to itself is an open map". It is a true special case: apply the theorem to the
  restriction of `f` to each open set. By compiling (`Chk2.lean`, example (b)): the statement
  "for every open `U` and every `f` continuous and injective on `U`, `f '' U` is open" gives
  `InvarianceOfDomain n`. `n → ℝ` has the product topology, the usual one of `ℝ^n`. It is a `def`
  of a `Prop`, not an `axiom`; nothing proves it. It appears only as the hypothesis `hinv`: in the
  nine files, in `exists_homeomorph_blockMapRes_of_not_folds` (A.32 (i)),
  `exists_isOpen_active_of_not_folds` and `not_unitInactiveRes_of_not_folds` (A.32 (ii)) and one
  private helper, all in `Residual/Folding.lean`. `Residual/FoldingOpen.lean` and
  `Residual/DeadUnits.lean` do not use it. At `a2e3143` a new file outside the brief,
  `Absorb/InjectiveBlocks.lean` (5 `sorry`), takes it as a hypothesis too (by `grep`; I did not
  compare that file).
- **The count of lost dimensions** (by reading the proofs' dimension counts and the paper's proof).
  ReLU, ReLU², no skips: flat directions `(L+1)d²` (changes of basis), `s − 1` (rescalings of the
  other units), `2d` (read column and write row of the unit): `fd ≤ P − (L+1)d² − s − (2d − 1)`.
  Paper: `(P − 2d) − ((L+1)d² + s − 1)`. The same number. ReGLU: `(L+1)d²`, `2(s/2 − 1) = s − 2`
  (value and gate rescalings of the other units; `s` is twice the number of hidden units, as in D
  Appendix B: "`s = 2 d_hidden` for ReGLU"), `3d`: `fd ≤ P − (L+1)d² − s − (3d − 2)`. Paper:
  `(P − 3d) − ((L+1)d² + s − 2)`. The same. Residual, `ν` dead units: `d²`, `s − ν`, `2dν`:
  `fd ≤ P − d² − s − (2d − 1)ν`. Paper: `P − 2dν − d² − (s − ν)`. The same. The subtractions
  `2 * card d - 1` and `3 * card d - 2` are of natural numbers; in every statement `d ≥ 1` holds
  (a read column is not zero, or `[Nonempty d]`), so they are exact.

---------------------------------------------------------------------------------------------------

## Part 2: the statements, file by file

### Verdict table

"SAME" is for the statement as a whole; the difference, if any, is in the last column. All rows:
proved, three standard axioms (`Chk.out`).

| Paper statement or proof piece | Lean | Verdict | Difference |
|---|---|---|---|
| D E.1, "There is a nonempty open set of weights on which a hidden unit of block 2 is inactive at every input", ReLU and ReLU² (proof, "ReLU and ReLU²") | `negReadSet`, `isOpen_negReadSet`, `nonempty_negReadSet`, `unitInactive_of_mem_negReadSet`; first three parts of `exists_isOpen_unitInactive_relu`, `…_reluSq` (`Depth/InactiveUnitRelu.lean`) | LEAN STRONGER | Any two consecutive blocks, any unit `j`, any `σ ≥ 0`, `d ≥ 1`, any number of tokens; the open set itself needs no condition on the widths |
| D E.1, the same for ReGLU (proof, "ReGLU") | `exists_isOpen_gateInactive_reglu` (`Depth/InactiveGateOpen.lean`) | LEAN STRONGER | The same; asks at least `d` hidden units in the block before, which the paper's choice of weights needs too. `δ = 1/(2qd)` is one `δ` with `0 < δ < 1/(q d)` |
| D E.1, "At almost every point of this set the functional dimension is at most `P − (L+1)d² − s − (2d − 1)`", ReLU, ReLU² | fourth part of `exists_isOpen_unitInactive_relu`, `…_reluSq` | LEAN STRONGER | Same set, same "almost every", same constant; at least `d` units in every block and more than `d` only in the block of the unit (paper: more than `d` in every block); `d ≥ 1`; nothing on `d_out`. The bound is on Lean's `funDim`, which is at least the paper's |
| D E.1, "… and at most `P − (L+1)d² − s − (3d − 2)` for ReGLU blocks" | `exists_isOpen_gateInactive_reglu_bound` (`Depth/InactiveGateReGLU.lean`) | LEAN STRONGER | The same |
| D E.1, proof, "The rank" | `UnitInactive`, `unitDir`, `unitDir_mem_flat`, `funDim_add_le_of_eventually_unitInactive` (`Depth/InactiveUnit.lean`); `GateInactive`, `unitDirGated`, `unitDirGated_mem_flat`, `funDim_add_le_of_eventually_gateInactive` (`Depth/InactiveGate.lean`) | SAME | At one `θ`, with the paper's "generic" written out: `E` and the writes of rank `d`, the write of the block without the row of the unit of rank `d`, no read column zero (for ReGLU no gate and no value column zero). "On this open set" is "inactive at all parameters near `θ`". For any `σ` positively homogeneous and zero on `z ≤ 0`, any block `m`; for the first block the hypotheses cannot all hold (note 5) |
| D E.1, "So these networks do not satisfy the equality condition" | `not_ae_funDim_add_eq_relu_skipless`, `…_reluSq_skipless`, `…_reglu_skipless` | SAME | Negation of Definition 4.4 for Lean's `funDim`; it gives the paper's claim (Check 2). `d ≥ 1`, nothing on `d_out` |
| S A.35 (Dead units without skips) | the Lean statements of E.1 above | PART | Lean asks more than `d` hidden units in the block of the dead unit; A.35 has no such clause (Scope: at least `d`). Lean's bound is at almost every point of the set; A.35 says "On it". Note 2 |
| S Definition A.31 (Folding) | `blockMapRes`, `Folds`, `hidden_succ_eq_blockMapRes` (`Residual/Folding.lean`) | SAME | Defined for any activation `σ` |
| S A.8, "A unit is dead if it is active at no input" | `UnitInactiveRes` (`Residual/Folding.lean`) | SAME | Every token of every input |
| S A.32 (i) | `exists_homeomorph_blockMapRes_of_not_folds` | SAME, under the hypothesis `InvarianceOfDomain d` | The paper cites invariance of domain in its proof; Lean takes it as a hypothesis |
| S A.32 (ii) | `exists_isOpen_active_of_not_folds`, `not_unitInactiveRes_of_not_folds` | SAME, under `InvarianceOfDomain d` | `E` of rank `d` is a hypothesis (the paper's section assumes it). For each token. The second open set has a negative pre-activation (the paper: "inactive"; its proof gives negative too). "Not dead" needs at least one token |
| S A.32 (iii) | `not_folds_of_norm_mul_norm_lt_one` | SAME | Spectral norms enter as constants `a`, `b` with `‖v W_read‖₂ ≤ a‖v‖₂`, `‖u W_write‖₂ ≤ b‖u‖₂`, `ab < 1`. No invariance of domain. The paper's form with Mathlib's spectral norm follows (by compiling, note 4) |
| S A.33 (i) | `exists_isOpen_folds_unitInactiveRes_relu` (`Residual/FoldingOpen.lean`) | LEAN STRONGER | Any two consecutive blocks, any unit `j` of the later one, `d ≥ 1`, only the folding block needs at least `d` units. No invariance of domain (the paper's proof that block 1 folds goes through A.32 (i)) |
| S A.33 (ii) | `funDim_add_le_residual_of_eventually_unitInactive` (`Residual/DeadUnits.lean`) | PART | Lean asks that the units are dead at all parameters near `θ`, that `E` has rank `d` and that no read column is zero; the paper asks only that the units are dead at `θ` (and its section, that `E` has rank `d`). Lean's conclusion is on `funDim`, the paper's on every batch on which no pre-activation vanishes. Same constant. Note 3 |
| S, after A.33: "So on the open set of Proposition A.33(i) the residual network has functional dimension below `P − d² − s`" | none | not stated | It follows from the two Lean statements at almost every point of the set (by compiling, note 6) |
| Brouwer's invariance of domain | `InvarianceOfDomain` (`Literature/InvarianceOfDomain.lean`) | a true special case, a hypothesis | Maps defined on all of `ℝ^n`. Reference: note 7 |

Not in Lean, and not asked of this audit: Remark A.34 of S (units that are always active); the
sentence of S after A.35, "With skips, no unit of a ReLU² or ReGLU block with a nonzero read is
dead"; the two example blocks (`W_read = −I, W_write = 2I` is used inside the proof of A.33 (i)
as a private lemma; `W_read = I, W_write = 2I` is not there).

### Notes

**1. Proposition A.32: which Lean statement is which part, and which rest on invariance of
domain.** (i) `exists_homeomorph_blockMapRes_of_not_folds`: rests on `InvarianceOfDomain d`.
(ii) `exists_isOpen_active_of_not_folds` (the two open sets of inputs) and
`not_unitInactiveRes_of_not_folds` ("no unit with a nonzero read is dead"): both rest on
`InvarianceOfDomain d`, through (i). (iii) `not_folds_of_norm_mul_norm_lt_one`: does not.
Lean text of (i) and (iii):

```
theorem exists_homeomorph_blockMapRes_of_not_folds (hinv : InvarianceOfDomain d)
    (θ : Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut) (ℓ : Fin L)
    (hℓ : ¬ Folds θ ℓ) :
    ∃ e : (d → ℝ) ≃ₜ (d → ℝ), ∀ h, e h = blockMapRes θ ℓ h

theorem not_folds_of_norm_mul_norm_lt_one
    (θ : Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut) (ℓ : Fin L) {a b : ℝ}
    (ha : ∀ v : d → ℝ,
      Real.sqrt ((v ᵥ* θ.read ℓ) ⬝ᵥ (v ᵥ* θ.read ℓ)) ≤ a * Real.sqrt (v ⬝ᵥ v))
    (hb : ∀ u : hid ℓ → ℝ,
      Real.sqrt ((u ᵥ* θ.write ℓ) ⬝ᵥ (u ᵥ* θ.write ℓ)) ≤ b * Real.sqrt (u ⬝ᵥ u))
    (hab : a * b < 1) : ¬ Folds θ ℓ
```

**2. Proposition A.35 of S is not word for word Proposition E.1 of D.** The brief and the index
(line 270) call them the same statement. Two clauses differ in the papers.

| | D Proposition E.1 | S Proposition A.35 |
|---|---|---|
| Widths | "each with more than `d_model` hidden units" | no clause; Scope of S: `d_hidden ≥ d_model` |
| Where the bound holds | "At almost every point of this set" | "On it the functional dimension is at most …" |

Lean has the form of E.1 (with less on the other blocks). So against A.35: when the block of the
dead unit has exactly `d` hidden units, no Lean statement gives the bound; and Lean gives it at
almost every point, not at every point of the set. For the authors, on the paper (by reading and
by a computation, not a Lean matter): the proof of A.35 says that the network without the dead
unit has as symmetries "the changes of basis of its `L + 1` hidden states and `s − 1`
rescalings", and does not say why they move the parameters in that many independent directions.
When block 2 has exactly `d_model` units, the network without the unit has a block of
`d_model − 1` units, and both statements of Lemma A.18 ask every block to have width at least
`d_model`. D avoids this with "more than `d_model`". I found no counterexample: in the six
networks with exactly `d` units that I computed (ReLU, ReLU², ReGLU, `d = 3`, `L = 2` and `3`),
the rank is at most the bound of A.35, and equals it in two of them (`ranks.out`). So the gap is
in the written proof and in the Lean coverage, not a known false statement.

**3. Proposition A.33 (ii).** Lean:

```
theorem funDim_add_le_residual_of_eventually_unitInactive {k : ℕ}
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (hσ0 : ∀ z : ℝ, z ≤ 0 → σ z = 0)
    (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) (J : Finset (Σ m, hid m))
    (hθ : ∀ p ∈ J, ∀ᶠ θ' in 𝓝 θ, UnitInactiveRes θ' p.1 p.2)
    (hE : θ.E.rank = Fintype.card d) (hc : ∀ ℓ i, (fun a => θ.read ℓ a i) ≠ 0) :
    funDim (Arch.mlp σ id hid) 1 θ
        + (Fintype.card d ^ 2 + ∑ ℓ, Fintype.card (hid ℓ) + (2 * Fintype.card d - 1) * J.card)
      ≤ Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)
```

The paper: "If `ν` units are dead, then on every batch on which no pre-activation vanishes, the
Jacobian has rank at most `P − d² − s − (2d − 1)ν`." Its proof reaches every such `θ` by lower
semicontinuity of the rank. Lean reaches the `θ` at which the units of `J` are dead on a whole
neighborhood and no read column is zero. The header of the file and the index (line 275) say
"dead near `θ`" and "all inputs"; they do not list "no read column vanishes" among the differences
(the hypothesis is in the sentence above it). The Lean statement is not empty: on the open set of
A.33 (i) its hypotheses hold at almost every point (by compiling, note 6). `J` is any finite set
of units that are dead near `θ`, not necessarily all of them.

**4. Proposition A.32 (iii) in the paper's words.** By compiling (`Chk3.lean`, `a32_iii_paper`,
three standard axioms): with Mathlib's spectral norm of a matrix (`Matrix.Norms.L2Operator`),
`‖θ.read ℓ‖ * ‖θ.write ℓ‖ < 1 → ¬ Folds θ ℓ` follows from the Lean statement, with `a` and `b`
the two norms. So the form with Lipschitz constants loses nothing.

**5. Degenerate cases.** All statements are proved, so none is false in a degenerate case; the
question is what they say there. (By reading, except where "by compiling" is written.)

| Case | What the statements say |
|---|---|
| No tokens (`T` empty) | `UnitInactive`, `GateInactive`, `UnitInactiveRes` hold for every unit, and `funDim = 0` (the output space is a point). The open-set statements and the bounds are true and say nothing. `not_ae_…` then says only that `P ≠ (L+2)d² + s`. `not_unitInactiveRes_of_not_folds` has `[Nonempty T]`, as it must. The papers have at least one token |
| One block | `ℓ : Fin L` and `0 < L` exclude it: every open-set statement has at least two blocks, as the papers. The bounds at one parameter allow one block and are then empty for a token (next line) |
| The dead unit in the first block | By compiling (`Chk5.lean`): with at least one token, `E` of rank `d` and a nonzero read column, a unit of the first block is not inactive at every input, without skips and with them. So for the first block the hypotheses of `funDim_add_le_of_eventually_unitInactive`, `funDim_add_le_of_eventually_gateInactive` (the same argument, by reading) and `funDim_add_le_residual_of_eventually_unitInactive` cannot all hold: "any block `m`" has content only after the first block. The open-set statements take block `ℓ.succ`, never the first |
| `d` with one element | Allowed (`[Nonempty d]`); the bounds lose `2d − 1 = 1` and `3d − 2 = 1`. The paper has `d_model ≥ 2`. Computed for one ReLU network with `d = 1`: rank 2, bound 2 (`ranks.out`) |
| `d` empty | Excluded by `[Nonempty d]` or by a nonzero read column |
| No hidden unit in a block | The statements with `hhid` exclude it (`d ≥ 1`). In `negReadSet`, if block `ℓ.castSucc` has no unit the set is everything, and the unit of the next block reads `0` at every input: inactive, as claimed. In A.33 (i) the blocks other than the two named may be empty |
| `J` empty (`Residual/DeadUnits.lean`) | The statement is `fd(θ) ≤ P − d² − s` for `E` of rank `d` and no zero read column: the upper bound for residual networks with rescalings (`funDim_add_le_residual_mlp_rescale`). Consistent |
| A unit of `J` in the first block | Hypotheses cannot hold with a token (above) |
| A dead unit with a zero read column | Excluded by `hc`. In the paper such a unit is dead and no batch avoids its kink, so the paper's (ii) says nothing about it either |
| `a` or `b` negative in A.32 (iii) | Possible only if `d` is empty or the block has no unit; the block is then the identity and does not fold. The statement stays true |

**6. A.33 (i) and (ii) together.** By compiling (`Chk2.lean`, `a33_together` and
`not_ae_residual`, three standard axioms), from the two Lean statements and
`ae_isUnit_det_submatrix`, `ae_read_col_ne_zero`: for `d_in ≥ d ≥ 1` and at least `d` units in
block `ℓ.castSucc`, there is a nonempty open set on which block `ℓ.castSucc` folds and unit `j` of
block `ℓ.succ` is dead, and at almost every point of it
`funDim (residual) + d² + s + (2d − 1) ≤ P`; hence it is not the case that `fd = P − d² − s` at
almost every parameter of a residual ReLU network with at least two blocks. This is the paper's
sentence after Proposition A.33 and the sentence of S Section 4.4, "For ReLU blocks the condition
fails on an open set of weights with skips as well". The library does not state it.

**7. The reference for invariance of domain.** `Literature/InvarianceOfDomain.lean` and the index
(line 168) give Brouwer, Math. Ann. 71 (1912), 305–315, taken from Wikipedia, and say that the
original was not read. The records of the article at EuDML (https://eudml.org/doc/158534) and at
Mathdoc (https://geodesic.mathdoc.fr/item/MAN_1912__71_158534) give pages 305–313; Wikipedia
(https://en.wikipedia.org/wiki/Invariance_of_domain) gives 305–315 (looked up on 24 November 2026;
I did not read the article either). The statement of the theorem in the file is the classical
one.

**8. The computation** (`py/ranks.py`, `ranks.out`). 18 networks with one token, one draw each:
skipless ReLU and ReLU² networks with `a_k r < 0` for all `k`; skipless ReGLU networks at the
weights of the proof of E.1 moved by `10⁻³`; residual ReLU networks at the weights of the proof of
A.33 (i) moved by `10⁻²`, with one or two dead units. For each: the largest pre-activation of the
unit on 200000 random inputs (never positive), and the rank of the Jacobian on a batch of more
than `3P/d_out` inputs (complex-step derivative, singular values above `10⁻⁸` times the largest;
the counts at `10⁻⁶`, `10⁻¹⁰`, `10⁻¹²` are printed and differ by at most one). In all 18 the rank
is at most the bound of the proposition; in 6 it equals the bound. This is a check that the
constants are reasonable, not a proof.

---------------------------------------------------------------------------------------------------

## What the authors should know

Nothing false or vacuous. In order of weight:

1. **S Proposition A.35 and D Proposition E.1 are not the same statement, and Lean has E.1's.**
   A.35 has no "more than `d_model` hidden units" and says "On it"; E.1 has "more than `d_model`"
   and "at almost every point". Lean: more than `d` units in the block of the dead unit, at almost
   every point. The written proof of A.35 does not cover a block 2 with exactly `d_model` units
   (the network without the dead unit is then outside Lemma A.18); the bound held in my six
   computed networks of that kind (note 2).
2. **S Proposition A.33 (ii) is formalized under more hypotheses than the paper's sentence:** the
   units dead at all parameters near `θ`, and no read column zero (note 3). At almost every point
   of the open set of (i) these hold.
3. **S Proposition A.32 (i) and (ii) are proved under invariance of domain, an unproved
   hypothesis** (`InvarianceOfDomain d`, a true special case of Brouwer's theorem). (iii),
   A.33 (i), A.33 (ii) and all of E.1 do not use it.
4. **Not stated in Lean:** the sentence after A.33 ("So on the open set of Proposition A.33(i) the
   residual network has functional dimension below `P − d² − s`") and with it "the equality
   condition fails with skips as well" for ReLU. Both follow from the library in a few lines
   (note 6; my proofs are in `/home/claude/audit10a/Chk2.lean`).
5. **The bounds at one parameter are for "any block `m`" but say something only after the first
   block** (note 5).
6. **The page range of Brouwer's article:** 305–313 in two library records, 305–315 in Wikipedia
   and in the Lean file and index (note 7).
7. The bounds are on Lean's `funDim`. The file headers say "Lean's `funDim` takes the Jacobian at
   all inputs". More exactly: it takes every batch, and a batch with an input at which the network
   is not differentiable in `θ` counts with rank `0` (the note "ReLU blocks and the functional
   dimension" of the index says this correctly). The conclusion drawn in the headers, that the
   bounds hold for the paper's functional dimension, is right (Check 2).
8. Lean's E.1 is stronger than the paper's in three ways that the paper could take over if wanted:
   only the block of the inactive unit needs more than `d_model` units; `d_model = 1` is allowed;
   nothing is asked of `d_out`.

## Corrections for `STATEMENTS.md` (lines of `a2e3143`)

1. Lines 83–91, "Not yet compared by such a reader": take out the nine files
   `Depth/InactiveUnit.lean`, `Depth/InactiveUnitRelu.lean`, `Depth/InactiveGate.lean`,
   `Depth/InactiveGateOpen.lean`, `Depth/InactiveGateReGLU.lean`,
   `Literature/InvarianceOfDomain.lean`, `Residual/Folding.lean`, `Residual/DeadUnits.lean`,
   `Residual/FoldingOpen.lean`, and add a sentence: a tenth reader (part A, 24 November) compared
   them (D Proposition E.1; S Definition A.31, Propositions A.32, A.33, A.35; 21 public theorems
   and 9 definitions): none false, vacuous or changed in meaning; A.35 of S differs from E.1 of D
   in two clauses and Lean has E.1's; A.33 (ii) has two hypotheses more than the paper's sentence.
2. Line 270 (and line 273 for ReGLU): replace "S Proposition A.35 (Dead units without skips), the
   same statement, with the bound at almost every point of the open set" by: "S Proposition A.35
   (Dead units without skips) in part: A.35 has no 'more than `d_model` hidden units' (Lean asks
   more than `d` in the block of the dead unit) and gives the bound on the whole open set (Lean:
   at almost every point of it)".
3. Line 275 (A.33 (ii)): in the last sentence add the third difference: "… Lean's `funDim` takes
   every batch, asks the units dead near `θ`, and asks that no read column is zero".
4. Lines 269 and 271 (the bounds at one parameter): after "hidden unit `j` of block `m`" add "(for
   the first block the hypotheses cannot all hold when there is a token)". The same for line 275
   and a unit of `J` in the first block. Optional.
5. Line 276 (A.33 (i)), or a new line: say that the paper's sentence after Proposition A.33, "So on
   the open set of Proposition A.33(i) the residual network has functional dimension below
   `P − d² − s`", is not stated, or state it.
6. Line 168 (invariance of domain): check the page range, 305–313 or 305–315 (and the same in
   the header of `Literature/InvarianceOfDomain.lean`, lines 12–13).
7. No correction to lines 272, 274 and 276 as they stand: they describe the Lean statements
   correctly.

## What I could not check

- I did not run `lake build`. That the nine files compile, with no `sorry` and the three standard
  axioms, I saw through a copy of the compiled library of `/home/claude/lp/lean` (same sources as
  `lw` when copied); the 21 signatures printed from it are those of the sources that I read. I did
  not build the library from the sources myself. The sources contain no `sorry`, `axiom`,
  `native_decide` or `unsafe` (by `grep`).
- The proofs. I read the statements and definitions, and of the proofs only what fixes the
  meaning of a statement (the choice of the open set, the dimension counts).
- That the network is differentiable in `θ` at the inputs at which no pre-activation vanishes, used
  in Check 2 to pass from Lean's `funDim` to the paper's rank: by reading, not in Lean.
- "The equality condition fails" for the paper's functional dimension: compiled for ReLU only
  (`Chk4.lean`); ReLU² and ReGLU by reading.
- Whether S Proposition A.35 is true when the block of the dead unit has exactly `d_model` units,
  and whether its bound holds at every point of the open set: a computation on six networks, one
  draw each, for the first; the paper's lower-semicontinuity argument, by reading, for the second.
- Brouwer's article and the Wikipedia article were not read in full; the page range is from
  library records.
- `Absorb/InjectiveBlocks.lean`, which appeared during the audit and also takes
  `InvarianceOfDomain d` as a hypothesis: not compared.
- The texts `dim.txt` and `skips.txt` against the PDFs.
