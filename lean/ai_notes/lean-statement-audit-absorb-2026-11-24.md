STATUS: complete

# Audit of the Lean statements for the paper "Can an MLP Absorb Its Skip Connection Exactly?" (2026-11-24)

Auditor: an independent reader of the Lean statements; the proofs were not audited, only the
statements. Nothing in a git repository was changed.

Compared:
- the paper, `/home/claude/lw/paper docs/new_paper_absorb_skip/new_paper_absorb_skip.tex` (line
  numbers "tex l.N" below) and its PDF (statement and equation numbers are those of the PDF, read
  with `pdftotext -layout`);
- the Lean library `/home/claude/lw/lean/SkipsLean/` as compiled on 24 November 2026 (Lean 4.36,
  Mathlib): `Absorb/Block.lean`, `Absorb/NoWidth.lean`, `Absorb/Networks.lean`,
  `Absorb/SameWidth.lean`, `Absorb/FewerUnits.lean`, and the definitions they use. Elaborated
  statements were read with `#check @…` and `#print` in `/home/claude/audit_abs/Check.lean`
  (output in `/home/claude/audit_abs/Check.out`), and again for `FewerUnits.lean` in
  `Check5.lean` / `Check5.out`.

**The tree changed during the audit.** At 03:05 UTC `Absorb/FewerUnits.lean` held five statements
with `sorry` (compiled 02:49; `STATEMENTS.md` said "in work"). At 03:23 UTC the file was replaced in
the audited worktree by a version with proofs (commits `5979922`, `65b6f83`, `19c32aa`, `fd99513`
of branch `lean-wip`), and `STATEMENTS.md` was changed to "proved"; the library was recompiled by
another process at 03:25 UTC. Entry 3.4 describes both versions. The four other files
of `Absorb/` did not change (`Block.lean` 02:02, `NoWidth.lean` 02:16, `Networks.lean` 02:30,
`SameWidth.lean` 02:48 UTC). Line numbers of `FewerUnits.lean` below are those of the 03:23 version.

Verdicts: SAME, LEAN STRONGER, LEAN WEAKER, DIFFERENT, PART, as defined in the task.

## 1. Summary table

All Lean statements below are proved with the axioms `propext`, `Classical.choice`, `Quot.sound`
only (`FewerUnits.lean` since 03:23 UTC; see the note above). "Stronger" always means: fewer
hypotheses or a more general setting, with the paper's statement as the special case.

| Paper statement | Lean names | Verdict | The difference in one line |
|---|---|---|---|
| Definition: vanilla block, eq. (1) | `vanillaBlock`, `map_mul_mul_row` | SAME | Lean is rectangular (`p` inputs, `q` outputs); rows on the left, as in the paper |
| Definition: gated block | `gatedBlock`, `Arch.gated` | SAME | two Lean definitions (one block; networks) that no lemma connects |
| Definition: `W_read[:,S] W_write[S,:]`, flipped reads | `subProd`, `flipCols` | SAME | `subProd` is `W_read Π_S W_write`; equality with the submatrix product checked (T1, T2) |
| Definition: nondegenerate | `Nondegenerate` | SAME | none |
| (not in the paper) blocks flat at `0` | `Arch.FlatAtZero` | — | a condition on the fixed map `f_ℓ`; replaces the paper's two classes of blocks in Theorem 4.1 (i) |
| Blocks `B′_ℓ` of the proof of Prop. 5.4 | `Params.flipReads` | SAME | none |
| eq. (3) | `relu_sub_relu_neg`, `gelu_sub_gelu_neg` | SAME | none |
| Section 3.1, flips change the block by `−x W_read[:,S] W_write[S,:]` | `vanillaBlock_flipCols`, `vanillaBlock_flipCols_of_subProd` | LEAN STRONGER | any `c` in `σ(z) − σ(−z) = cz` |
| Theorem 3.1 (i), equivalence | `relu_absorb_same_width_iff`, `gelu_absorb_same_width_iff`, `exists_subProd_eq_neg_of_relu_absorb`, `exists_subProd_eq_neg_of_gelu_absorb` | LEAN STRONGER | rectangular `M`, `M = 0` allowed, no `d ≥ 2`, no `m ≥ d` |
| Theorem 3.1 (i), generic `θ` | `ae_not_relu_absorb_same_width`, `ae_not_gelu_absorb_same_width`, `ae_nondegenerate`, `ae_forall_subProd_ne_neg` | SAME | at `p = q = d`; `d ≥ 2` kept (needed); `m ≥ d` not assumed |
| Theorem 3.1 (ii), `d` more units suffice | `exists_vanillaBlock_add_linear` | LEAN STRONGER | any `M`, any `σ` with `σ(z) − σ(−z) = cz`, `c ≠ 0`; no theorem names ReLU or GELU |
| Theorem 3.1 (ii), fewer do not | `ae_not_relu_absorb_of_card_lt`, `ae_not_gelu_absorb_of_card_lt` (with `exists_ne_of_relu_card_lt`, `exists_ne_of_gelu_card_lt`, `ae_forall_isUnit_det_add_subProd`) | SAME | `m ≥ d` not assumed; `m' : Type`; was `sorry` at the start of the audit, proved since 03:23 UTC |
| Proposition 3.2 | `ae_ne_skipless_oneBlock_relu`, `ae_ne_skipless_oneBlock_gelu` | SAME | no condition on the skipless network; `d' : Type` |
| Theorem 3.3 | `exists_ne_of_homogeneous`, `exists_ne_reluSq`, `exists_ne_reglu`, `exists_ne_of_gated`, `exists_ne_swiglu`, `exists_ne_geglu`, `exists_ne_tanh` | LEAN STRONGER | rectangular; arbitrary homogeneous maps; two gates may differ |
| Theorem 4.1 (i) | `exists_ne_residual_skipless_of_flatAtZero`, `exists_ne_residual_skipless_of_flatAtZero_rmsNorm`, `flatAtZero_gated`, `flatAtZero_mlp_reluSq`, `flatAtZero_gated_relu`, `hasFDerivAt_zero_of_homogeneous` | LEAN STRONGER; PART for one class | hypothesis is `FlatAtZero`, not the paper's classes; gated blocks, ReLU², ReGLU covered; "positively homogeneous of degree `k > 1`" in general is not stated (a lemma with a boundedness hypothesis); kinds and `ε` may differ |
| Theorem 4.1 (ii) | `exists_ne_residual_skipless_tanh` | SAME | `L = 0` allowed, no Scope |
| Proposition 4.4 | `exists_skipless_eq_residual_of_rank_read` | LEAN STRONGER | any `σ` with `σ(z) − σ(−z) = z`; same `E`, `D`, `d` in the conclusion; no `ED ≠ 0` |
| Proposition 5.4 (i) | `ae_exists_learned_skips_eq_skipless`, `eval_skipless_eq_learned_flipReads` | SAME | no `d_in, d_out ≥ d ≥ 2`; keeps "at least `d` hidden units" |
| Proposition 5.4 (ii) | `ae_exists_residual_eq_skipless` | SAME | nonempty index types instead of `d_in, d_out ≥ d ≥ 2`; `E′D ≠ 0` in the conclusion |
| Proposition A.1 | `exists_ne_of_homogeneous` | LEAN STRONGER | `B`, `B′` arbitrary maps |
| Proposition A.2 | `exists_ne_of_gated` | SAME | rectangular |
| Corollary A.3 | the three theorems of Theorem 4.1 | LEAN STRONGER; PART for one class | as Theorem 4.1; the first sentence (compositions) only as the instance `E = D = I` |
| Theorem A.4 | instance `M = I` of `relu_absorb_same_width_iff` | LEAN STRONGER | no statement of its own; no `d ≥ 2` |
| Corollary A.9 | the two equivalences, `ae_forall_subProd_ne_neg` | LEAN STRONGER | `p ≥ 2` dropped in the equivalence |
| Corollary A.10 | instances `M = I` and `M = −I` of `ae_not_relu_absorb_same_width`, `ae_not_gelu_absorb_same_width` | SAME | no statement of its own; `STATEMENTS.md` says the second half is not stated |
| Proposition A.11 (i) | `exists_vanillaBlock_add_linear` | LEAN STRONGER | `M` need not be invertible |
| Proposition A.11 (ii) | as Theorem 3.1 (ii), second half | SAME | proved since 03:23 UTC |
| Proof of Theorem 4.5, GELU step | `gelu_sub_relu`, `abs_gelu_sub_relu_le`, `relu_absorb_of_gelu_absorb` | PART | one block, not networks; bound `1`, not `κ < 0.17` |

## 2. Definitions, clause by clause

Paper: Section 2 (tex l.188-216) and Appendix A, "Setting" (tex l.475-478).

### 2.1 Rows, columns, and the side on which weights multiply

| Paper | Lean | Same? |
|---|---|---|
| "A hidden state is a matrix `h ∈ ℝ^{T×d_model}` whose rows are the `T` tokens" (tex l.191) | `Matrix T d ℝ`, with `T` and `d` finite index types (`Network/Defs.lean` l.24, l.55) | same |
| "On a row `x ∈ ℝ^{1×d_model}` that it reads it computes `B_θ(x) = f(x W_read) W_write`" (eq. (1), tex l.191-194) | `vanillaBlock σ Wr Ww x = (fun i => σ ((x ᵥ* Wr) i)) ᵥ* Ww` (`Absorb/Block.lean` l.34-35). `x ᵥ* Wr` is the row `x` times the matrix: `(x ᵥ* Wr) i = ∑ a, x a * Wr a i`. Weights multiply on the right. | same |
| "so on a row `x` of a hidden state it computes `B_θ(χ(x))`" (tex l.195) | in a network, block `ℓ` adds `A.f ℓ (A.χ h * θ.read ℓ) * θ.write ℓ` (`Network/Defs.lean` l.58); `map_mul_mul_row` (`Absorb/Block.lean` l.42-44, proved) says that row `t` of `(h * Wr).map σ * Ww` is `vanillaBlock σ Wr Ww (h t)` | same for vanilla blocks; for gated blocks see 2.2 |
| `w_i` is column `i` of `W_read`, `ŵ_i` is row `i` of `W_write` (tex l.475) | `Wrᵀ i` and `Ww i` (in `Nondegenerate`, `Absorb/SameWidth.lean` l.34-37) | same |

### 2.2 Blocks and kinds of block

| Paper | Lean | Same? |
|---|---|---|
| vanilla block with `m` hidden units: `W_read ∈ ℝ^{d×m}`, `W_write ∈ ℝ^{m×d}`, `f` applies `σ` to each unit (tex l.196) | `Wr : Matrix p m ℝ`, `Ww : Matrix m q ℝ`: rectangular, `p` inputs and `q` outputs; the paper's block is `p = q = d`. `m` is an index type with `[Fintype m]`. | Lean more general |
| activations ReLU, GELU, tanh, ReLU² | `relu z = max z 0`, `reluSq z = (max z 0)^2` (`Activations/ReLU.lean` l.15, l.21); `gelu z = z * gaussCdf z`, `gaussCdf z = 1/2 + ∫₀^z gaussPdf`, `gaussPdf z = exp(-z²/2)/√(2π)` (`Activations/Gaussian.lean` l.22-28); `Real.tanh` | same (the paper: `GELU(z) = zΦ(z)`, tex l.507) |
| gated block: the read has two halves `W_g`, `W_v` side by side, "the unit multiplies `σ((xW_g)_i)` by its value `(xW_v)_i`" (tex l.196) | on a row: `gatedBlock σ Wg Wv Ww x = (fun i => σ ((x ᵥ* Wg) i) * (x ᵥ* Wv) i) ᵥ* Ww` (`Absorb/Block.lean` l.38-39). In a network: `Arch.gated σ χ hid`, read columns `hid ℓ ⊕ hid ℓ` (gate `Sum.inl i`, value `Sum.inr i`), `f M = of fun t i => σ (M t (inl i)) * M t (inr i)` (`Network/Blocks.lean` l.31-36) | same. Remark: no Lean lemma links `gatedBlock` (used by Theorem 3.3, Proposition A.2) to `Arch.gated` (used by Theorem 4.1); for vanilla blocks `map_mul_mul_row` does this. The two definitions agree by inspection. |
| gates: ReLU (ReGLU), SiLU (SwiGLU), GELU (GeGLU) | `relu`, `silu z = z / (1 + exp(-z))` (`OneBlock/UnitsSwiGLU.lean` l.27), `gelu` | same |
| "Two MLP blocks are of the same kind if they are of the same type, vanilla or gated, and have the same activation" (tex l.196) | no definition; "of the same kind" is the same function on both sides of an equation (`vanillaBlock relu … = vanillaBlock relu …`, `Arch.mlp σ …` twice). Several Lean statements allow two different kinds (two gates `σ₁`, `σ₂` in `exists_ne_of_gated`; two arbitrary architectures in Theorem 4.1 (i)). | same or Lean more general |

### 2.3 Absorbing a linear term, widths

| Paper | Lean | Same? |
|---|---|---|
| eq. (2): `xM + B_θ(x) = B_θ′(x)` for all `x ∈ ℝ^{1×d_model}`, `M` a `d×d` matrix, `M ≠ 0` (tex l.198-201) | `∀ x : p → ℝ, x ᵥ* M + vanillaBlock σ Wr Ww x = vanillaBlock σ Wr' Ww' x`, `M : Matrix p q ℝ` (rectangular); `M ≠ 0` is a hypothesis only where a statement needs it | same at `p = q = d` |
| "a block of the same kind, and of any width" | a second index type: `{m' : Type*} [Fintype m']` in the pointwise statements (`NoWidth.lean` l.24, `FewerUnits.lean` l.58, `SameWidth.lean` l.93), universe-polymorphic; under a `∀ᵐ` it is `∀ (m' : Type) [Fintype m']`, universe 0 only (`FewerUnits.lean` l.308, l.322) | same: every finite type is in bijection with a `Fin n : Type`, and a block can be re-indexed (this re-indexing is not a Lean lemma) |
| "of the same width" | the same index type `m` for `Wr'`, `Ww'` (`SameWidth.lean` l.309-310, l.452) ; in Proposition 3.2 the same `hid` | same up to re-indexing |
| "with `d_model` more hidden units" | index type `m ⊕ p` (`Block.lean` l.141), `hid ℓ ⊕ d` (`Networks.lean` l.48) | same |
| "with fewer" (than `m + d`) | `Fintype.card m' < Fintype.card m + Fintype.card d` (`FewerUnits.lean` l.58, l.308) | same |

### 2.4 Flips, `W_read[:,S] W_write[S,:]`, nondegenerate

| Paper | Lean | Same? |
|---|---|---|
| "For `S ⊆ {1,…,m}`, `W_read[:,S]` is the submatrix of columns in `S`, `W_write[S,:]` the submatrix of rows in `S`, and `Π_S` the diagonal projector …, so that `W_read Π_S W_write = W_read[:,S] W_write[S,:]`" (tex l.475) | `subProd S Wr Ww = Wr * Matrix.diagonal (fun j => if j ∈ S then 1 else 0) * Ww`, `S : Finset m`, `[DecidableEq m]` (`Block.lean` l.55-57): this is `W_read Π_S W_write` | same (checked in Lean, tests T1 and T2 of 2.10) |
| flipping the reads of the units in `S`: `W_read′ = W_read F`, `F = I − 2Π_S` (tex l.231, l.522) | `flipCols S Wr = of fun i j => if j ∈ S then -Wr i j else Wr i j` (`Block.lean` l.50-51) | same |
| "A block is nondegenerate if the columns of `W_read` are nonzero and pairwise non-collinear and the rows of `W_write` are nonzero" (tex l.233, l.475); "pairwise non-collinear if no one of them is a scalar multiple of another" | `structure Nondegenerate (Wr) (Ww) : Prop` with `col_ne_zero : ∀ i, Wrᵀ i ≠ 0`, `col_not_collinear : ∀ i j, i ≠ j → ∀ r : ℝ, Wrᵀ i ≠ r • Wrᵀ j`, `row_ne_zero : ∀ i, Ww i ≠ 0` (`SameWidth.lean` l.34-37) | same. Corner cases: with no hidden units every block is nondegenerate (vacuous) in both; with `p = 0` or `q = 0` a nondegenerate block has no hidden units. |
| eq. (5): `x + σ(x W_read) W_write = σ(x W_read′) W_write′` for all `x` (tex l.476-478) | the case `M = 1` of the Lean equation (`x ᵥ* 1 = x`); no separate Lean statement | same |

### 2.5 Networks

| Paper | Lean | Same? |
|---|---|---|
| embedding `E ∈ ℝ^{d_in×d}`, `L ≥ 1` blocks, readout `D ∈ ℝ^{d×d_out}` (tex l.204) | `Params A dIn dOut` with `E : Matrix dIn d ℝ`, `read ℓ : Matrix d (A.r ℓ) ℝ`, `write ℓ : Matrix (A.w ℓ) d ℝ`, `D : Matrix d dOut ℝ` (`Network/Defs.lean` l.41-49); `Arch T d L` holds the index types of the reads and writes, the maps `f ℓ` and `χ` (l.24-34) | same, except `L`: see next row |
| `L ≥ 1` | `L : ℕ`, so `L = 0` is allowed (a "network" `X ↦ χ(XE) D`). In Theorem 4.1 the skipless network has `L' + 1` blocks, as it must (with no block the statement would be false); the residual network may have `L = 0`. In Propositions 4.4 and 5.4, `L = 0` is allowed and trivial. | Lean more general; `L = 0` is not a network of the paper |
| hidden states `h_0 = XE`, `h_ℓ = B_ℓ(χ(h_{ℓ−1}))` (skipless), `h_ℓ = h_{ℓ−1} + B_ℓ(χ(h_{ℓ−1}))` (residual) (tex l.208) | `hidden A S θ x` : `h_0 = x * θ.E`, `h_{ℓ+1} = h_ℓ * S ℓ + A.f ℓ (A.χ h_ℓ * θ.read ℓ) * θ.write ℓ` (`Defs.lean` l.55-58), with stream matrices `S = 0` (skipless), `S = 1` (residual, `1 = fun _ => 1`) or any `S : Fin L → Matrix d d ℝ` (learned skips, tex l.426) | same; the skip carries `h` itself, not `χ(h)`, as in the paper |
| "the readout gives `y = χ(h_L) D`" | `eval A S θ x = A.χ (hidden A S θ x (Fin.last L)) * θ.D` (l.61-63): `χ` is applied before the readout | same |
| the output function `C` is ignored (tex l.208) | absent | same |
| "Two networks are equal if they compute the same function" (tex l.128) | `∀ X : Matrix T dIn ℝ, eval … X = eval … X`; "not equal" is `∃ X, eval … X ≠ eval … X` | same (all statements in scope are without normalization or with `ε > 0`, where both networks are defined everywhere) |
| "A skipless network that is compared with a residual one may have another model dimension" (tex l.214) | a second type `d'` with `[Fintype d']`, its own `L'`, `hid'` and parameters; the same `T`, `dIn`, `dOut` (`Networks.lean` l.393-396, l.517-520; `SameWidth.lean` l.744-745). In Proposition 3.2 `d'` is quantified under the `∀ᵐ` as `∀ (d' : Type) [Fintype d']` (universe 0). | same up to re-indexing |
| MLP network of one kind | `Arch.mlp σ χ hid` (`r = w = hid`, `f _ M = M.map σ`), `Arch.gated σ χ hid` (`Network/Blocks.lean`) | same |
| type restrictions | `Arch.r, Arch.w : Fin L → Type` (universe 0), so `hid : Fin L → Type`; in `Absorb/Networks.lean` also `d : Type` (l.36), because `hid ℓ ⊕ d` is a width in Proposition 4.4. `T`, `dIn`, `dOut` are `Type*`. | no loss: finite types |

### 2.6 Normalization, biases

| Paper | Lean | Same? |
|---|---|---|
| "RMSNorm, written `N`, divides each row `v` of a hidden state by `√(‖v‖²/d_model + ε)`, with a constant `ε ≥ 0`" (tex l.210) | `rmsRow ε v = (Real.sqrt ((v ⬝ᵥ v) / (Fintype.card d : ℝ) + ε))⁻¹ • v`, `rmsNorm ε h = of fun t => rmsRow ε (h t)` (`Basic/RMSNorm.lean` l.22-27); `ε : ℝ` is any real in the definition | same for `ε > 0` |
| "For `ε = 0`, `N` is defined only on hidden states without zero rows … Two such networks are equal if they agree on a dense set of inputs at which both are defined." | `rmsRow 0 0 = 0`. No statement in scope uses `ε = 0`: RMSNorm occurs only in `exists_ne_residual_skipless_of_flatAtZero_rmsNorm`, with `0 < ε` and `0 < ε'`. | no effect on the statements in scope |
| "Blocks have no biases" | no biases in `vanillaBlock`, `gatedBlock`, `hidden` | same |

### 2.7 Scope assumptions of the paper (tex l.214) and where Lean carries them

| Assumption | Carried in Lean | Dropped in Lean |
|---|---|---|
| "Every MLP block has at least `d_model` hidden units" | Proposition 3.2 (`hhid`, `SameWidth.lean` l.743, l.757), for the residual network only; Proposition 5.4 (`hhid`, `Networks.lean` l.635, l.724) | Theorem 3.1 (all parts), Theorem 3.3, Theorem 4.1, Proposition 4.4 (there the rank of the reads implies it), and the skipless network of Proposition 3.2 |
| "Residual networks have `ED ≠ 0`" | Theorem 4.1: hypothesis `hED : θ.E * θ.D ≠ 0` (`Networks.lean` l.395, l.451, l.519); Proposition 5.4 (ii): conclusion `θ'.E * θ'.D ≠ 0` (l.726) | Proposition 4.4 (true without it); in Proposition 3.2 it is part of the exceptional null set |
| "`d_in, d_out ≥ d_model ≥ 2`" | Proposition 3.2: `hd`, `hdIn`, `hdOut`; generic clause of Theorem 3.1 (i): `2 ≤ Fintype.card p` only; Theorem 3.1 (ii) second half: `2 ≤ Fintype.card d` | the equivalence of Theorem 3.1 (i); Theorem 3.1 (ii) first half; Theorem 3.3; Theorem 4.1; Proposition 4.4; Proposition 5.4 (i); Proposition 5.4 (ii) keeps only `[Nonempty d] [Nonempty dIn] [Nonempty dOut]` |
| "all MLP blocks of a network are of one kind" | `Arch.mlp σ`, `Arch.gated σ` | Theorem 4.1 (i) is stated for arbitrary architectures |

Every dropped assumption makes the Lean statement more general; none is replaced by something
else.

### 2.8 Generic weights

Paper (tex l.216): "A statement holds for generic weights, or for almost every choice of weights,
if it holds outside a set of weights of Lebesgue measure zero."

Lean: `∀ᵐ W ∂μ, …` for **every** measure `μ` with `[μ.IsAddHaarMeasure]`,
- for one block on the pairs `Matrix p m ℝ × Matrix m q ℝ` = `(W_read, W_write)`
  (`SameWidth.lean` l.516-518, l.562-564, l.592-595; `FewerUnits.lean` l.270-272, l.306-310);
- for a network on `Params A dIn dOut` = `(E, reads, writes, D)`, with the Borel σ-algebra of its
  norm topology (`Generic/Params.lean` l.32-34) and the vector-space structure of the four
  components (`Dimension/Space.lean`).

On a finite-dimensional real vector space the additive Haar measures are the positive multiples of
the Lebesgue measure of any linear coordinates, so the null sets are those of the paper. Same.
Checked in Lean for one block of sizes `2 × 3`, `3 × 2`: the product of the Lebesgue measures of the
entries, `(Measure.pi fun _ => volume).prod (Measure.pi fun _ => volume)`, satisfies
`IsAddHaarMeasure` for the instances that the statements use, and `ae_not_relu_absorb_same_width`
applies to it (test W2 of 2.10). For the parameters of a network a Haar measure is found by instance
search (`MeasureTheory.Measure.addHaar`, test V4); I did not check in Lean that the Lebesgue measure
of the entries of `(E, reads, writes, D)` is one, which is the same standard fact.

Technical remark: `Measure (Matrix p m ℝ × Matrix m q ℝ)` uses the σ-algebra
`Prod.instMeasurableSpace` of the σ-algebras of the two matrix spaces (each the product σ-algebra
of the entries) and the product topology. Mathlib's instance search does not find `BorelSpace` or
`LocallyCompactSpace` for this product by itself (`Matrix` is not unfolded); the library supplies
them by hand inside its proofs (`ae_ne_zero_of_analytic_prod`, `SameWidth.lean` l.506-513). A user
who applies the one-block generic statements has to supply the instance `μ.IsAddHaarMeasure` in the
same way. This does not change what the statements say.

The order of the quantifiers is the paper's: in every `∀ᵐ` statement the absorbing block or the
skipless network (`Wr'`, `Ww'`, `m'`, `d'`, `θ'`) is quantified **inside** the `∀ᵐ`, so the
exceptional null set does not depend on it. `M` is fixed before the `∀ᵐ` ("fix a matrix `M ≠ 0`").

Degenerate case: if the space of weights is `{0}` (for instance no hidden units), an additive Haar
measure is a positive multiple of the Dirac mass at `0` and "generic" means "at the zero weights".
The statements in scope remain true there (e.g. with `m` empty, no block of width `0` computes `xM`
for `M ≠ 0`).

### 2.9 Definitions of the Lean files that are not definitions of the paper

- `Arch.FlatAtZero A` (`Networks.lean` l.93-95): for every block `ℓ`, `A.f ℓ 0 = 0` and
  `HasFDerivAt (A.f ℓ) 0 0`. This is a condition on the **fixed map** `f_ℓ` of the block (a map
  between the matrices `T × r_ℓ` and `T × w_ℓ`), not on the block `h ↦ f_ℓ(h W_read) W_write`. It
  implies, for every choice of weights, what the proof of Corollary A.3 uses: "Each such block maps
  `0` to `0` and has Jacobian `0` there" (tex l.504). See the entry for Theorem 4.1 for how the
  paper's two classes of blocks enter.
- `Params.flipReads θ S` (`Networks.lean` l.571-576): `E`, the writes and `D` of `θ`, and the reads
  `flipCols (S ℓ) (θ.read ℓ)`. These are the blocks `B′_ℓ` of the proof of Proposition 5.4 (tex
  l.898: "`B′_ℓ` be block `ℓ` with the read `w_i` replaced by `−w_i` for every `i ∈ S_ℓ`"). Same.

### 2.10 Checks run in Lean by the auditor

Files `/home/claude/audit_abs/Check.lean`, `Check2.lean`, `Check3.lean`, `Check5.lean` (outputs
`.out` beside them; `Check4` could not run because the library was being recompiled). Each test is
an `example` that elaborates against the compiled library without `sorry`.

| Test | What it states | Result |
|---|---|---|
| T1 | `subProd S Wr Ww i j = ∑ k ∈ S, Wr i k * Ww k j` | elaborates |
| T2 | `subProd S Wr Ww = Wr.submatrix id (Subtype.val : S → m) * Ww.submatrix (Subtype.val : S → m) id` | elaborates |
| T3 | the coordinates of `vanillaBlock` and `gatedBlock` (`rfl`) | elaborates |
| T4 | Theorem 3.1 (ii), first half, for `relu` and for `gelu`, with `p = q = d` | elaborates |
| T5 | Theorem 4.1 (i) for SwiGLU networks without normalization | elaborates |
| T6 | Theorem 4.1 (i) for ReLU² networks under pre-RMSNorm, `ε > 0` | elaborates |
| T8 | Corollary A.10, second half, for ReLU, from `ae_not_relu_absorb_same_width` with `M = −1` | elaborates |
| T9a | with no hidden units every block is nondegenerate | elaborates |
| U3 | with `L = 0` and `χ = id`, `eval A 1 θ X = X * θ.E * θ.D` | elaborates |
| U4 | Theorem A.4 in the paper's form, from `relu_absorb_same_width_iff` with `M = 1` | elaborates |
| U6 | Corollary A.3, first sentence (compositions: `E = D = E′ = D′ = 1`, `d` nonempty) | elaborates |
| U7 | Theorem 4.1 (i) for `Arch.mlp σ` with any `σ`, given `FlatAtZero` for both architectures | elaborates |
| V3 | Proposition 3.2 with `d = d_in = d_out = width = 2`, one token: the hypotheses can be met | elaborates |
| V4 | a Haar measure exists on the parameters of that network | elaborates |
| W2 | the product of the Lebesgue measures of the entries is an admissible `μ` for one block, and Theorem 3.1 (i), generic clause, applies to it | elaborates |
| X1 | "exactly `d` units" for ReLU and `M = I` (both halves of Theorem 3.1 (ii) in one statement) | elaborates |

Tests that failed because of my own test code, not of the library (instance search does not unfold
`Matrix`; an implicit `L` that my example did not determine; a wrong `simp` argument): T7a, T7c,
T9b, U1, U2, U5, V1, V2, W1. They were replaced by V3, V4, U3, W2 and say nothing about the
library.

## 3. The statements, one by one

Elaborated Lean statements are quoted from `/home/claude/audit_abs/Check.out` (`#check @…`), with
the instance arguments shortened. `#print axioms` gives `[propext, Classical.choice, Quot.sound]`
for every statement of `Block.lean`, `NoWidth.lean`, `Networks.lean` and `SameWidth.lean` below. For
`FewerUnits.lean` see 3.4.

### 3.1 Theorem 3.1 (i), first sentence (the equivalence)

Paper (tex l.235-237): "Let σ be ReLU or GELU, and fix a matrix `M ≠ 0`. (i) If `B_θ` is
nondegenerate, some block `B_θ′` of the same width satisfies (2) if and only if some set `S` of
hidden units has `W_read[:,S] W_write[S,:] = −M`."

Lean (`Absorb/SameWidth.lean` l.450-454 and l.463-467; the two directions are l.308-312, l.438-442
and `Absorb/Block.lean` l.103-106):

```
relu_absorb_same_width_iff : ∀ {p q m} [Fintype p] [Fintype m] [DecidableEq m]
  (Wr : Matrix p m ℝ) (Ww : Matrix m q ℝ), Nondegenerate Wr Ww → ∀ (M : Matrix p q ℝ),
  (∃ Wr' Ww', ∀ (x : p → ℝ), x ᵥ* M + vanillaBlock relu Wr Ww x = vanillaBlock relu Wr' Ww' x)
    ↔ ∃ S, subProd S Wr Ww = -M
gelu_absorb_same_width_iff : the same with gelu
```

Here `Wr' : Matrix p m ℝ`, `Ww' : Matrix m q ℝ` (the same index type `m`: the same width) and
`S : Finset m`.

| | Paper | Lean |
|---|---|---|
| activation | ReLU or GELU | two theorems, `relu` and `gelu` |
| block | nondegenerate | `Nondegenerate Wr Ww` |
| `M` | `d×d`, `M ≠ 0` | `p×q`, any `M` (for `M = 0` both sides hold, with `S = ∅`) |
| sizes | `d ≥ 2`, `m ≥ d` (Scope) | none |
| conclusion | "some block of the same width satisfies (2) iff some set `S` …" | the same `↔` |

Verdict: **LEAN STRONGER** (rectangular `M` and weights, `M = 0` allowed, no condition on `d` or
`m`); at `p = q = d`, `M ≠ 0` it is the paper's statement. The "if" direction
(`vanillaBlock_flipCols_of_subProd`) holds for every `σ` with `σ(z) − σ(−z) = z` and without
nondegeneracy, as in the paper's text before the theorem (tex l.231).

### 3.2 Theorem 3.1 (i), second sentence (generic `θ`)

Paper (tex l.237): "For generic θ, no block of the same width does." (`M ≠ 0` fixed.)

Lean (`SameWidth.lean` l.592-595, l.606-609):

```
ae_not_relu_absorb_same_width : ∀ {p q m} [Fintype p] [Fintype m] [DecidableEq m] [Fintype q],
  2 ≤ Fintype.card p → ∀ (M : Matrix p q ℝ), M ≠ 0 →
  ∀ (μ : Measure (Matrix p m ℝ × Matrix m q ℝ)) [μ.IsAddHaarMeasure],
  ∀ᵐ (W : Matrix p m ℝ × Matrix m q ℝ) ∂μ,
    ¬∃ Wr' Ww', ∀ (x : p → ℝ), x ᵥ* M + vanillaBlock relu W.1 W.2 x = vanillaBlock relu Wr' Ww' x
ae_not_gelu_absorb_same_width : the same with gelu
```

with the two ingredients `ae_nondegenerate` (l.516-518: `2 ≤ card p`, `[Nonempty q]`, generic
blocks are nondegenerate) and `ae_forall_subProd_ne_neg` (l.562-564: for `M ≠ 0`,
`∀ᵐ W, ∀ S, subProd S W.1 W.2 ≠ -M`).

| | Paper | Lean |
|---|---|---|
| `M` | fixed, `M ≠ 0`, `d×d` | fixed before the `∀ᵐ`, `M ≠ 0`, `p×q` |
| `d ≥ 2` | Scope | `2 ≤ Fintype.card p` |
| `m ≥ d` | Scope | not assumed |
| generic | Lebesgue null set of `θ = (W_read, W_write)` | `∀ᵐ` for every additive Haar measure on the pairs |
| order | "for generic θ, no block" | `∀ᵐ W, ¬∃ Wr' Ww'`: the null set does not depend on `θ′` |

The hypothesis `2 ≤ card p` cannot be dropped: for `d = 1` and `m ≥ 2` every ReLU block absorbs
every `xM` at the same width (`xM + B(x) = α·ReLU(x) + β·ReLU(−x)`, and two units compute that).

Verdict: **SAME** at `p = q = d` (Lean also covers rectangular `M` and `m < d`).

### 3.3 Theorem 3.1 (ii), first half (`d` more units suffice)

Paper (tex l.238): "(ii) If `M` is invertible and `W_read` has rank `d_model`, some block `B_θ′`
with `d_model` more hidden units satisfies (2)". Also Proposition A.11 (i) (tex l.606).

Lean (`Absorb/Block.lean` l.138-143):

```
exists_vanillaBlock_add_linear : ∀ {p q m} [Fintype p] [Fintype m] {σ : ℝ → ℝ} {c : ℝ} [DecidableEq p],
  (∀ (z : ℝ), σ z - σ (-z) = c * z) → c ≠ 0 →
  ∀ (Wr : Matrix p m ℝ) (Ww : Matrix m q ℝ), Wr.rank = Fintype.card p → ∀ (M : Matrix p q ℝ),
  ∃ Wr' Ww', (∀ (i : p) (j : m), Wr' i (Sum.inl j) = Wr i j) ∧
    ∀ (x : p → ℝ), x ᵥ* M + vanillaBlock σ Wr Ww x = vanillaBlock σ Wr' Ww' x
```

with `Wr' : Matrix p (m ⊕ p) ℝ`, `Ww' : Matrix (m ⊕ p) q ℝ`.

| | Paper | Lean |
|---|---|---|
| activation | ReLU or GELU | any `σ` with `σ(z) − σ(−z) = c z`, `c ≠ 0`; ReLU and GELU are `c = 1`, through `relu_sub_relu_neg` (`Block.lean` l.60) and `gelu_sub_gelu_neg` (`Activations/Gaussian.lean` l.198) |
| `M` | invertible, `d×d` (`M ≠ 0`) | any `p×q` matrix |
| read | rank `d` | `Wr.rank = Fintype.card p` |
| conclusion | a block with `d` more hidden units satisfies (2) | a block indexed by `m ⊕ p` satisfies (2), and it keeps the reads of the old units |

There is no Lean theorem that names ReLU or GELU here; the two instances are one line each (I
checked that they elaborate: test T4 in `Check.lean`).

Verdict: **LEAN STRONGER** (`M` need not be invertible; more activations; rectangular output; a
further conclusion). The paper's case is the special case `p = q = d`, `c = 1`.

### 3.4 Theorem 3.1 (ii), second half (fewer than `d` more units do not suffice)

Paper (tex l.238): "… and for generic θ none with fewer does." Also Proposition A.11 (ii) (tex
l.607): "For generic weights no block of width less than `m + d_model` does."

Lean (`Absorb/FewerUnits.lean`, version of 03:23 UTC, l.306-310 and l.320-324; elaborated in
`Check5.out`):

```
ae_not_relu_absorb_of_card_lt : ∀ {d m} [Fintype d] [DecidableEq d] [Fintype m] [DecidableEq m],
  2 ≤ Fintype.card d → ∀ (M : Matrix d d ℝ), IsUnit M.det →
  ∀ (μ : Measure (Matrix d m ℝ × Matrix m d ℝ)) [μ.IsAddHaarMeasure],
  ∀ᵐ (W : Matrix d m ℝ × Matrix m d ℝ) ∂μ,
    ∀ (m' : Type) [Fintype m'], Fintype.card m' < Fintype.card m + Fintype.card d →
      ∀ (Wr' : Matrix d m' ℝ) (Ww' : Matrix m' d ℝ),
        ∃ x, x ᵥ* M + vanillaBlock relu W.1 W.2 x ≠ vanillaBlock relu Wr' Ww' x
ae_not_gelu_absorb_of_card_lt : the same with gelu
```

| | Paper | Lean |
|---|---|---|
| `M` | invertible | `IsUnit M.det` |
| `d ≥ 2` | Scope; stated in A.11 | `2 ≤ Fintype.card d` |
| `m ≥ d`, read of rank `d` | Scope / first half of the sentence | not assumed |
| generic | null set of `θ` | `∀ᵐ W` for every Haar measure on the pairs |
| "none with fewer" | no block of width `< m + d` (A.11 (ii)) | `∀ m' : Type`, `card m' < card m + card d`, all `Wr'`, `Ww'`; `m'` and the block are inside the `∀ᵐ` |
| width type | any width | `m' : Type`, universe 0 (no loss: finite types) |

The hypothesis `2 ≤ card d` is needed in this generic form: for `d = 1` and `m ≥ 2` a ReLU block
absorbs `xM` at the same width `m < m + 1`.

The file also states the claim "under the conditions of its proof":

```
exists_ne_of_relu_card_lt (l.55-60) : ∀ {d m} [Fintype d] [DecidableEq d] [Fintype m] [DecidableEq m]
  (Wr : Matrix d m ℝ) (Ww : Matrix m d ℝ), Nondegenerate Wr Ww → ∀ (M : Matrix d d ℝ),
  (∀ (S : Finset m), IsUnit (M + subProd S Wr Ww).det) →
  ∀ {m'} [Fintype m'], Fintype.card m' < Fintype.card m + Fintype.card d →
  ∀ (Wr' : Matrix d m' ℝ) (Ww' : Matrix m' d ℝ),
    ∃ x, x ᵥ* M + vanillaBlock relu Wr Ww x ≠ vanillaBlock relu Wr' Ww' x
exists_ne_of_gelu_card_lt (l.218-223) : the same with gelu
ae_forall_isUnit_det_add_subProd (l.270-272) : IsUnit M.det → ∀ μ [μ.IsAddHaarMeasure],
  ∀ᵐ W ∂μ, ∀ (S : Finset m), IsUnit (M + subProd S W.1 W.2).det
```

These are the two conditions that the paper's proof excludes on a null set (tex l.614: "Outside a
set of measure zero the block is nondegenerate, and for each of the finitely many sets `S` of units
the determinant of `M + W_read[:,S] W_write[S,:]` is nonzero"). I went through the paper's argument
with these two conditions only and found no further condition used, and no degenerate case in which
the pointwise statements fail (`m` empty: a block with fewer than `d` units has rank `< d` and `M`
is invertible; `d` empty: no `m'` satisfies the bound).

What changed during the audit:
- 03:05 UTC (file of 02:03, compiled 02:49): all five statements had `sorry` as proof (`Check.out`:
  `sorryAx` in `#print axioms`), and the two pointwise statements had the further hypothesis
  `2 ≤ Fintype.card d`.
- 03:23 UTC: the file has proofs and no `sorry`; the two pointwise statements no longer assume
  `2 ≤ Fintype.card d` (commit `fd99513`); the three `∀ᵐ` statements
  are word for word as before; a public helper `exists_ne_zero_forall_dotProduct_eq_zero` (l.38-40)
  was added. After the recompilation of 03:25 UTC, `#print axioms` gives
  `[propext, Classical.choice, Quot.sound]` for all six (`Check5.out`).

Together with 3.3 the two halves give "exactly `d_model` units" (test X1 in `Check5.lean` states,
for ReLU and `M = I`: at generic weights, if the read has rank `d`, some block with `d` more units
computes `x + B(x)` and no block with fewer than `m + d` units does; it elaborates).

Verdict: **SAME** (Lean slightly stronger: `m ≥ d` is not assumed); proved since 03:23 UTC.

### 3.5 Proposition 3.2 (networks of one block)

Paper (tex l.250-252): "Let σ be ReLU or GELU. For almost every choice of weights, a residual
network of one block equals no skipless network of one block of the same width." (Without
normalization: "it computes `X ↦ XED + f(XE W_read) W_write D`", tex l.248.)

Lean (`SameWidth.lean` l.740-747, l.754-761):

```
ae_ne_skipless_oneBlock_relu : ∀ {T dIn dOut d} [Fintype T] [Fintype d] [DecidableEq d]
  [Fintype dIn] [Fintype dOut] {hid : Fin 1 → Type} [(ℓ : Fin 1) → Fintype (hid ℓ)] [Nonempty T]
  (μ : Measure (Params (Arch.mlp relu id hid) dIn dOut)) [μ.IsAddHaarMeasure],
  2 ≤ Fintype.card d → Fintype.card d ≤ Fintype.card dIn → Fintype.card d ≤ Fintype.card dOut →
  Fintype.card d ≤ Fintype.card (hid 0) →
  ∀ᵐ (θ : Params (Arch.mlp relu id hid) dIn dOut) ∂μ,
    ∀ (d' : Type) [Fintype d'] (θ' : Params (Arch.mlp relu id hid) dIn dOut),
      ∃ X, eval (Arch.mlp relu id hid) 1 θ X ≠ eval (Arch.mlp relu id hid) 0 θ' X
ae_ne_skipless_oneBlock_gelu : the same with gelu
```

(In the last two lines the second `Arch.mlp relu id hid` has the model dimension `d'`; the printer
hides it. Source: `θ' : Params (Arch.mlp (T := T) (d := d') relu id hid) dIn dOut`.)

| | Paper | Lean |
|---|---|---|
| residual network | one block, no normalization | `eval (Arch.mlp relu id hid) 1 θ`, `hid : Fin 1 → Type`, `χ = id` |
| its sizes | `d_in, d_out ≥ d ≥ 2`, at least `d` hidden units (Scope) | `hd`, `hdIn`, `hdOut`, `hhid` |
| `ED ≠ 0` | Scope | not a hypothesis: holds at generic weights |
| generic | weights `(E, W_read, W_write, D)` of the residual network | `∀ᵐ θ ∂μ`, `μ` any Haar measure on its parameters |
| skipless network | one block, the same width, any model dimension | `θ'` with any `d' : Type`, the same `hid`, the same `T`, `dIn`, `dOut`; quantified inside the `∀ᵐ` |
| sizes of the skipless network | Scope (`d_in, d_out ≥ d′ ≥ 2`, width `≥ d′`) | none |
| tokens | `T` tokens | `[Fintype T] [Nonempty T]` |

Verdict: **SAME**; Lean is slightly stronger (no condition on the skipless network; `d' = ∅` is
allowed and then says that the residual network is not the zero function). `d'` is in universe 0.
The hypotheses can be met (test V3 in `Check3.lean`: `d = d_in = d_out = width = 2`, one token).

### 3.6 Theorem 3.3 (no width suffices)

Paper (tex l.295-297): "Let `B_θ` be (a) a block that is positively homogeneous of degree
`k ≠ 1`, (b) a gated block whose gate vanishes at `0` and is differentiable there, or (c) a tanh
block. ReLU² and ReGLU blocks fall under (a), SwiGLU and GeGLU blocks under (b). For every
`M ≠ 0`, no block `B_θ′` of the same kind and of any width satisfies (2)."

Lean (`Absorb/NoWidth.lean`):

```
(a) exists_ne_of_homogeneous (l.40-44) : ∀ {p q} [Fintype p] {k : ℝ}, k ≠ 1 →
      ∀ (B B' : (p → ℝ) → q → ℝ),
      (∀ (lam : ℝ) (x : p → ℝ), 0 < lam → B (lam • x) = lam ^ k • B x) →
      (∀ (lam : ℝ) (x : p → ℝ), 0 < lam → B' (lam • x) = lam ^ k • B' x) →
      ∀ (M : Matrix p q ℝ), M ≠ 0 → ∃ x, x ᵥ* M + B x ≠ B' x
    exists_ne_reluSq (l.149-151), exists_ne_reglu (l.158-160): for
      vanillaBlock reluSq and gatedBlock relu, with widths m and m'
(b) exists_ne_of_gated (l.97-101) : σ₁ 0 = 0 → DifferentiableAt ℝ σ₁ 0 → σ₂ 0 = 0 →
      DifferentiableAt ℝ σ₂ 0 → ∀ Wg Wv Ww Wg' Wv' Ww' (M : Matrix p q ℝ), M ≠ 0 →
      ∃ x, x ᵥ* M + gatedBlock σ₁ Wg Wv Ww x ≠ gatedBlock σ₂ Wg' Wv' Ww' x
    exists_ne_swiglu (l.167-169), exists_ne_geglu (l.176-178): gates silu, gelu
(c) exists_ne_tanh (l.197-199) : M ≠ 0 →
      ∃ x, x ᵥ* M + vanillaBlock Real.tanh Wr Ww x ≠ vanillaBlock Real.tanh Wr' Ww' x
```

In all of them `m` and `m'` are two independent index types (`{m m' : Type*}`): "of any width".

| | Paper | Lean |
|---|---|---|
| (a) | both blocks of the same kind, positively homogeneous of degree `k ≠ 1` | `B`, `B'` arbitrary maps, both positively homogeneous of the same real degree `k ≠ 1` (`lam ^ k` is the real power, `lam > 0`) |
| (a) examples | ReLU², ReGLU: degree 2 | `vanillaBlock_reluSq_smul` (l.122), `gatedBlock_relu_smul` (l.134), and the two corollaries |
| (b) | gated, gate vanishes at 0 and is differentiable there, same kind | two gates `σ₁`, `σ₂`, which may differ |
| (c) | tanh | `Real.tanh` |
| `M` | `M ≠ 0`, `d×d` | `M ≠ 0`, `p×q` |
| conclusion | "no block `B_θ′` … satisfies (2)" | `∃ x, x ᵥ* M + B x ≠ B' x` for every `B'` |

Verdict: **LEAN STRONGER** (rectangular; arbitrary homogeneous maps in (a); two different gates in
(b)). Nothing of the paper's statement is missing.

### 3.7 Theorem 4.1 (i) (ReLU², gated networks: never equal)

Paper (tex l.328-330): "Let the residual network have `ED ≠ 0`. (i) Without normalization or with
pre-RMSNorm and `ε > 0`, let the blocks be gated blocks whose gate vanishes at `0` and is
differentiable there, or blocks that are positively homogeneous of degree `k > 1`. No skipless
network of blocks of the same kind, of any depth and widths, equals the residual network."

Lean (`Absorb/Networks.lean` l.393-397 and l.448-453):

```
exists_ne_residual_skipless_of_flatAtZero : ∀ {T dIn dOut} {d : Type} {L : ℕ} [Fintype T]
  [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] [Nonempty T] {L' : ℕ} {d'} [Fintype d']
  (A : Arch T d L) (A' : Arch T d' (L' + 1)),
  A.χ = id → A'.χ = id → A.FlatAtZero → A'.FlatAtZero →
  ∀ (θ : Params A dIn dOut), θ.E * θ.D ≠ 0 → ∀ (θ' : Params A' dIn dOut),
    ∃ X, eval A 1 θ X ≠ eval A' 0 θ' X
exists_ne_residual_skipless_of_flatAtZero_rmsNorm : the same with {ε ε' : ℝ}, 0 < ε → 0 < ε' →
  A.χ = rmsNorm ε → A'.χ = rmsNorm ε' → …
```

where `Arch.FlatAtZero A := ∀ ℓ, A.f ℓ 0 = 0 ∧ HasFDerivAt (A.f ℓ) 0 0` (l.93-95), and

```
flatAtZero_gated (l.99-100) : σ 0 = 0 → DifferentiableAt ℝ σ 0 → (Arch.gated σ χ hid).FlatAtZero
flatAtZero_mlp_reluSq (l.191-192) : (Arch.mlp reluSq χ hid).FlatAtZero
flatAtZero_gated_relu (l.213-214) : (Arch.gated relu χ hid).FlatAtZero
hasFDerivAt_zero_of_homogeneous (l.163-167) : 1 < k → ∀ (f : E → F),
  (∀ (lam : ℝ) (x : E), 0 < lam → f (lam • x) = lam ^ k • f x) →
  (∃ C, ∀ (x : E), ‖x‖ = 1 → ‖f x‖ ≤ C) → f 0 = 0 ∧ HasFDerivAt f 0 0
```

| | Paper | Lean |
|---|---|---|
| `ED ≠ 0` | hypothesis | `θ.E * θ.D ≠ 0` |
| normalization | none, or pre-RMSNorm with `ε > 0` (both networks) | two theorems: `χ = id` in both; `χ = rmsNorm ε` and `χ = rmsNorm ε'` with possibly different `ε, ε' > 0`. The mixed case (one network normalized, the other not) is not stated; the paper does not state it either. |
| blocks of the residual network | gated with a gate that vanishes at 0 and is differentiable there, or positively homogeneous of degree `k > 1` | any architecture `A` with `A.FlatAtZero` |
| blocks of the skipless network | "of the same kind" | any architecture `A'` with `A'.FlatAtZero`: it need not be of the same kind |
| depths | residual `L ≥ 1`, skipless any depth `≥ 1` | residual `L ≥ 0`, skipless `L' + 1` |
| widths, `d′` | any | any (`d'` its own type) |
| Scope (`d ≥ 2`, widths `≥ d`, `d_in, d_out ≥ d`) | assumed | not assumed |
| conclusion | no such skipless network equals the residual one | `∃ X, eval A 1 θ X ≠ eval A' 0 θ' X` for every `θ'` |

How the paper's two classes of blocks enter:
1. Gated blocks whose gate vanishes at `0` and is differentiable there: `flatAtZero_gated` has
   exactly these two hypotheses on the gate. The paper's statement for this class follows by one
   application (I checked that it elaborates for SwiGLU networks without normalization: test T5).
2. "Blocks that are positively homogeneous of degree `k > 1`": there is **no** Lean statement for
   this class as such. `FlatAtZero` is proved for ReLU² and for ReGLU only (test T6: ReLU² networks
   under pre-RMSNorm elaborate). For any other homogeneous block one has to prove `FlatAtZero`
   (test U7 shows the shape of what remains); the lemma `hasFDerivAt_zero_of_homogeneous` helps, but
   it is about a map `f`, it is not connected to `Arch`, and it has a hypothesis the paper does not
   state: `f` is bounded on the unit sphere. (The paper's proof uses it silently, tex l.504: "because
   it is `O(‖x‖^k)` with `k > 1`". For a vanilla or gated block with a scalar activation, homogeneity
   of degree `k > 1` forces `σ(z) = a·max(z,0)^k + b·max(−z,0)^k`, respectively a gate of this form
   of degree `k − 1`, which is continuous, so the hypothesis holds; this step is not in Lean.)
3. No Lean theorem states the conclusion for a named kind of network ("a residual SwiGLU network
   with `ED ≠ 0` equals no skipless SwiGLU network"); each is two applications.

`FlatAtZero` is a condition on the fixed map `f_ℓ`, not on the block; it implies "maps `0` to `0` and
has Jacobian `0` there" for the block with any weights, which is what the proof of Corollary A.3
uses.

Verdict: **LEAN STRONGER** in its conclusion (the two networks need not be of the same kind, may
have different `ε`, `L = 0` allowed, no Scope), with the hypothesis on the blocks replaced by
`FlatAtZero`. For the paper's classes: gated blocks, ReLU² and ReGLU are covered; the general class
"positively homogeneous of degree `k > 1`" is covered only through these two instances (**PART** for
that class).

### 3.8 Theorem 4.1 (ii) (tanh networks)

Paper (tex l.329-331): "Let the residual network have `ED ≠ 0`. … (ii) Without normalization, no
skipless network of tanh blocks, of any depth and widths, equals a residual network of tanh
blocks."

Lean (`Networks.lean` l.517-522):

```
exists_ne_residual_skipless_tanh : ∀ {T dIn dOut} {d : Type} {L : ℕ} [Fintype T] [Fintype d]
  [DecidableEq d] [Fintype dIn] [Fintype dOut] {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]
  [Nonempty T] {L' : ℕ} {d'} [Fintype d'] {hid' : Fin (L' + 1) → Type} [∀ ℓ, Fintype (hid' ℓ)]
  (θ : Params (Arch.mlp Real.tanh id hid) dIn dOut), θ.E * θ.D ≠ 0 →
  ∀ (θ' : Params (Arch.mlp Real.tanh id hid') dIn dOut),
    ∃ X, eval (Arch.mlp Real.tanh id hid) 1 θ X ≠ eval (Arch.mlp Real.tanh id hid') 0 θ' X
```

Hypotheses and conclusion are the paper's: `ED ≠ 0`, no normalization (`id`), tanh blocks in both
networks, the skipless network with its own depth `L' + 1 ≥ 1`, widths `hid'` and model dimension
`d'`. Lean allows `L = 0` and does not assume the Scope.

Verdict: **SAME** (Lean slightly stronger: `L = 0`, no Scope).

### 3.9 Proposition 4.4 (`d_model` more units per block suffice)

Paper (tex l.366-368): "Let σ be ReLU or GELU. Without normalization, a residual network whose
reads all have rank `d_model` equals a skipless network with `d_model` more hidden units in every
block." (Proof, tex l.659: "… with the same embedding and readout …".)

Lean (`Networks.lean` l.45-51):

```
exists_skipless_eq_residual_of_rank_read : ∀ {T dIn dOut} {d : Type} {L : ℕ} [Fintype T]
  [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] {hid : Fin L → Type}
  [∀ ℓ, Fintype (hid ℓ)] {σ : ℝ → ℝ}, (∀ (z : ℝ), σ z - σ (-z) = z) →
  ∀ (θ : Params (Arch.mlp σ id hid) dIn dOut), (∀ (ℓ : Fin L), (θ.read ℓ).rank = Fintype.card d) →
  ∃ θ', θ'.E = θ.E ∧ θ'.D = θ.D ∧
    ∀ (X : Matrix T dIn ℝ), eval (Arch.mlp σ id hid) 1 θ X = eval (Arch.mlp σ id fun ℓ => hid ℓ ⊕ d) 0 θ' X
```

| | Paper | Lean |
|---|---|---|
| activation | ReLU or GELU | any `σ` with `σ(z) − σ(−z) = z` (ReLU, GELU by `relu_sub_relu_neg`, `gelu_sub_gelu_neg`) |
| normalization | none | `χ = id` |
| reads | all of rank `d` | `∀ ℓ, (θ.read ℓ).rank = Fintype.card d` |
| `ED ≠ 0`, `d ≥ 2`, `d_in, d_out ≥ d` | Scope | not assumed |
| conclusion | equals a skipless network with `d` more hidden units in every block | a skipless network with the widths `hid ℓ ⊕ d`, the same model dimension, and moreover the same `E` and `D` |

Verdict: **LEAN STRONGER** (more activations; the same `E`, `D` and `d` in the conclusion; no
Scope; `L = 0` allowed).

### 3.10 Proposition 5.4 (i) (skipless network = network with invertible learned skips)

Paper (tex l.428-430): "Let σ satisfy `σ(z) − σ(−z) = cz` for a constant `c ≠ 0`, as ReLU and GELU
do with `c = 1`. Without normalization, for almost every choice of weights, a skipless network `F`
of vanilla σ blocks equals (i) a network with invertible learned skips and the same embedding,
readout, `d_model` and widths".

Lean (`Networks.lean` l.633-640, with the identity l.582-587):

```
ae_exists_learned_skips_eq_skipless : ∀ {T dIn dOut} {d : Type} {L : ℕ} [Fintype T] [Fintype d]
  [DecidableEq d] [Fintype dIn] [Fintype dOut] {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]
  {σ : ℝ → ℝ} {c : ℝ} [∀ ℓ, DecidableEq (hid ℓ)],
  (∀ (z : ℝ), σ z - σ (-z) = c * z) → c ≠ 0 →
  ∀ (μ : Measure (Params (Arch.mlp σ id hid) dIn dOut)) [μ.IsAddHaarMeasure],
  (∀ (ℓ : Fin L), Fintype.card d ≤ Fintype.card (hid ℓ)) →
  ∀ᵐ (θ : Params (Arch.mlp σ id hid) dIn dOut) ∂μ,
    ∃ A θ', (∀ (ℓ : Fin L), IsUnit (A ℓ).det) ∧ θ'.E = θ.E ∧ θ'.D = θ.D ∧
      ∀ (X : Matrix T dIn ℝ), eval (Arch.mlp σ id hid) 0 θ X = eval (Arch.mlp σ id hid) A θ' X

eval_skipless_eq_learned_flipReads : (∀ z, σ z - σ (-z) = c * z) → ∀ θ (S : ∀ ℓ, Finset (hid ℓ)) X,
  eval (Arch.mlp σ id hid) 0 θ X
    = eval (Arch.mlp σ id hid) (fun ℓ => c • subProd (S ℓ) (θ.read ℓ) (θ.write ℓ)) (θ.flipReads S) X
```

| | Paper | Lean |
|---|---|---|
| activation | `σ(z) − σ(−z) = cz`, `c ≠ 0` | the same |
| normalization | none | `χ = id` |
| at least `d` hidden units per block | Scope (used by the proof, tex l.896) | `hhid` |
| `d_in, d_out ≥ d ≥ 2` | Scope | not assumed |
| generic | weights of the skipless network | `∀ᵐ θ ∂μ` |
| conclusion | a network with invertible learned skips, the same embedding, readout, `d`, widths | `A : Fin L → Matrix d d ℝ` with `IsUnit (A ℓ).det`, `θ'` of the same architecture with `θ'.E = θ.E`, `θ'.D = θ.D`, equal outputs at every `X` |

The second Lean statement is the identity of the paper's proof (tex l.898-902), for every choice of
the sets `S_ℓ` and without genericity.

Verdict: **SAME** (Lean slightly stronger: no `d_in, d_out ≥ d ≥ 2`, `L = 0` allowed).

### 3.11 Proposition 5.4 (ii) (skipless network = residual network)

Paper (tex l.431): "(ii) a residual network with the same readout, `d_model` and widths." (Proof,
tex l.904: "Its embedding is `E A_{>0} = c^L E K_1⋯K_L`, and `E A_{>0} D ≠ 0`.")

Lean (`Networks.lean` l.721-728):

```
ae_exists_residual_eq_skipless : ∀ {T dIn dOut} {d : Type} {L : ℕ} … [Nonempty d] [Nonempty dIn]
  [Nonempty dOut], (∀ (z : ℝ), σ z - σ (-z) = c * z) → c ≠ 0 →
  ∀ (μ : Measure (Params (Arch.mlp σ id hid) dIn dOut)) [μ.IsAddHaarMeasure],
  (∀ (ℓ : Fin L), Fintype.card d ≤ Fintype.card (hid ℓ)) →
  ∀ᵐ (θ : Params (Arch.mlp σ id hid) dIn dOut) ∂μ,
    ∃ θ', θ'.D = θ.D ∧ θ'.E * θ'.D ≠ 0 ∧
      ∀ (X : Matrix T dIn ℝ), eval (Arch.mlp σ id hid) 0 θ X = eval (Arch.mlp σ id hid) 1 θ' X
```

| | Paper | Lean |
|---|---|---|
| hypotheses | as in (i) | as in (i), plus `[Nonempty d] [Nonempty dIn] [Nonempty dOut]` (weaker than the Scope `d_in, d_out ≥ d ≥ 2`; needed for `E′D ≠ 0`) |
| conclusion | a residual network with the same readout, `d`, widths; a residual network of the paper has `ED ≠ 0` (Scope) | `θ'` of the same architecture, `θ'.D = θ.D`, `θ'.E * θ'.D ≠ 0`, equal outputs at every `X` |

Verdict: **SAME** (Lean slightly stronger: nonempty index types instead of `d_in, d_out ≥ d ≥ 2`).

### 3.12 Proposition A.1 (homogeneous blocks)

Paper (tex l.480-482): "Let `B` and `B′` be blocks that are positively homogeneous of degree
`k ≠ 1`, of any widths, and let `M ≠ 0`. Then `xM + B(x) = B′(x)` fails for some `x`."

Lean: `exists_ne_of_homogeneous` (`NoWidth.lean` l.40-44, quoted in 3.6). `B`, `B'` are arbitrary
maps `(p → ℝ) → (q → ℝ)` with `B (lam • x) = lam ^ k • B x` for `lam > 0` (the same `k : ℝ` for
both), `M : Matrix p q ℝ`, `M ≠ 0`; conclusion `∃ x, x ᵥ* M + B x ≠ B' x`.

Verdict: **LEAN STRONGER** (the maps need not be blocks; rectangular `M`). Same hypotheses
otherwise, same conclusion.

### 3.13 Proposition A.2 (gated blocks)

Paper (tex l.490-492): "Let `B` and `B′` be gated blocks without biases, of any widths, whose gates
are differentiable at `0` and vanish there, and let `M ≠ 0`. Then `xM + B(x) = B′(x)` fails for
some `x`."

Lean: `exists_ne_of_gated` (`NoWidth.lean` l.97-101, quoted in 3.6): gates `σ₁`, `σ₂` with
`σᵢ 0 = 0` and `DifferentiableAt ℝ σᵢ 0`, widths `m`, `m'`, `M ≠ 0`.

Verdict: **SAME** (the paper's "gates" also allows two gates), with rectangular weights in Lean.

### 3.14 Corollary A.3 (any depth)

Paper (tex l.500-502): "Let every block be as in Proposition A.1 with `k > 1` or as in Proposition
A.2, of any widths. Let `F` be a composition of residual blocks `h ↦ h + B_ℓ(h)` and `H` a
composition of one or more skipless blocks. Then `F ≠ H`. With embeddings and readouts, the residual
network `X ↦ F(XE)D` differs from the skipless network `X ↦ H(XE′)D′` whenever `ED ≠ 0`, also with
pre-RMSNorm and `ε > 0`. Without normalization the same holds for tanh blocks."

Lean: the three theorems of 3.7 and 3.8.

| Clause of the paper | Lean |
|---|---|
| "every block as in Proposition A.1 with `k > 1` or as in Proposition A.2" | `A.FlatAtZero`, `A'.FlatAtZero`; see 3.7 for the two classes (gated: `flatAtZero_gated`; homogeneous: only ReLU², ReGLU, and a lemma with a boundedness hypothesis) |
| "`F ≠ H`" for compositions, without embedding and readout | no separate statement; it is the case `dIn = dOut = d' = d`, `E = D = E′ = D′ = 1` of `exists_ne_residual_skipless_of_flatAtZero`, which needs `d` nonempty for `ED = I ≠ 0` (test U6) |
| with `E`, `D`, `ED ≠ 0` | `exists_ne_residual_skipless_of_flatAtZero` |
| "also with pre-RMSNorm and `ε > 0`" | `exists_ne_residual_skipless_of_flatAtZero_rmsNorm` (`ε`, `ε'` may differ) |
| "Without normalization the same holds for tanh blocks" | `exists_ne_residual_skipless_tanh` |

Verdict: as Theorem 4.1: **LEAN STRONGER** in the conclusion; **PART** for the class "as in
Proposition A.1 with `k > 1`" (instances ReLU², ReGLU). The first sentence is only an instance.

### 3.15 Theorem A.4 (identity absorption for ReLU)

Paper (tex l.513-518): "Let σ = ReLU, `d_model ≥ 2`, and let the block be nondegenerate. Then (5)
has a solution if and only if `W_read[:,S] W_write[S,:] = −I_{d_model}` for some `S`."

Lean: no statement of its own; it is `relu_absorb_same_width_iff` (3.1) with `p = q = d`,
`M = 1`, after `x ᵥ* 1 = x` (test U4 states it in the paper's form and derives it in one line). The
row of `STATEMENTS.md` for the "only if" (`exists_subProd_eq_neg_of_relu_absorb`) is the general-`M`
form too.

Verdict: **LEAN STRONGER** (any `M`, no `d ≥ 2`); the paper's statement is the instance `M = I`.
The same holds for Theorem A.7 (GELU), which is `gelu_absorb_same_width_iff` at `M = 1`.

### 3.16 Corollary A.9 (linear terms of any shape)

Paper (tex l.583-589): "Let σ be ReLU or GELU. Let `p ≥ 2`, let `W_read ∈ ℝ^{p×m}` have nonzero,
pairwise non-collinear columns, let `W_write ∈ ℝ^{m×q}` have nonzero rows, and let `M ∈ ℝ^{p×q}`.
Some `W_read′ ∈ ℝ^{p×m}` and `W_write′ ∈ ℝ^{m×q}` satisfy `xM + σ(xW_read)W_write =
σ(xW_read′)W_write′` for all `x ∈ ℝ^{1×p}` if and only if `W_read[:,S] W_write[S,:] = −M` for some
`S`. For fixed `M ≠ 0`, this holds only on a set of weights `(W_read, W_write)` of measure zero."

Lean: first sentence: `relu_absorb_same_width_iff`, `gelu_absorb_same_width_iff` (3.1), which have
exactly these `p`, `q`, `m` and no hypothesis `p ≥ 2`. Second sentence:

```
ae_forall_subProd_ne_neg (SameWidth.lean l.562-564) : ∀ (M : Matrix p q ℝ), M ≠ 0 →
  ∀ (μ : Measure (Matrix p m ℝ × Matrix m q ℝ)) [μ.IsAddHaarMeasure],
  ∀ᵐ (W : Matrix p m ℝ × Matrix m q ℝ) ∂μ, ∀ (S : Finset m), subProd S W.1 W.2 ≠ -M
```

(the condition on `S`), and `ae_not_relu_absorb_same_width`, `ae_not_gelu_absorb_same_width` (3.2)
for the existence of `W_read′`, `W_write′`, with `2 ≤ card p` as in the corollary.

Verdict: **LEAN STRONGER** for the equivalence (`p ≥ 2` dropped); **SAME** for the last sentence.

### 3.17 Corollary A.10 (generic disjointness for one block)

Paper (tex l.595-597): "Let σ be ReLU or GELU and `d_model ≥ 2`. For generic weights, (5) has no
solution, and a skipless block equals no residual block of the same width."

Lean: no statement of its own, and no row in `STATEMENTS.md` (its notes say "Not stated yet:
Corollary A.10, second half"). Both halves are instances of the generic clause of 3.2:
- first half: `ae_not_relu_absorb_same_width` / `…gelu…` with `p = q = d`, `M = 1`;
- second half: the same theorems with `M = −1`: for generic `(W_read, W_write)`, no block
  `(W_r, W_w)` of the same width has `x(−I) + σ(xW_read)W_write = σ(xW_r)W_w`, that is,
  `σ(xW_read)W_write = x + σ(xW_r)W_w`. Test T8 in `Check.lean` states the second half for ReLU in
  the paper's form and derives it from `ae_not_relu_absorb_same_width`; it elaborates.

Verdict: **SAME** as two instances (`M = I`, `M = −I`) of a proved, more general statement; not
stated under its own name. The note in `STATEMENTS.md` is too pessimistic.

### 3.18 Proposition A.11 (`d_model` extra units)

Paper (tex l.604-608): "Let σ be ReLU or GELU, let `d_model ≥ 2`, and let `M ∈ ℝ^{d×d}` be
invertible. (i) If `W_read` has rank `d_model`, a block `B′` of width `m + d_model` satisfies
`xM + B(x) = B′(x)` for all `x`. (ii) For generic weights no block of width less than
`m + d_model` does."

Lean: (i) `exists_vanillaBlock_add_linear` (3.3): **LEAN STRONGER** (`M` need not be invertible,
no `d ≥ 2`, any `σ` with `σ(z) − σ(−z) = cz`, `c ≠ 0`). (ii) `ae_not_relu_absorb_of_card_lt`,
`ae_not_gelu_absorb_of_card_lt` (3.4): **SAME**, with the pointwise forms
`exists_ne_of_relu_card_lt`, `exists_ne_of_gelu_card_lt` and `ae_forall_isUnit_det_add_subProd`;
proved since 03:23 UTC (they were `sorry` when the audit began).

### 3.19 Other rows of `STATEMENTS.md` (text and proofs)

| Paper | Lean | Verdict |
|---|---|---|
| eq. (3) (tex l.223-226): "ReLU and GELU both satisfy `σ(z) − σ(−z) = z`" | `relu_sub_relu_neg` (`Block.lean` l.60), `gelu_sub_gelu_neg` (`Activations/Gaussian.lean` l.198) | SAME |
| "Flipping the reads of the units in `S` changes the block by `−x W_read[:,S] W_write[S,:]`" (tex l.231) | `vanillaBlock_flipCols` (`Block.lean` l.70-73): if `σ(z) − σ(−z) = c z` then `vanillaBlock σ (flipCols S Wr) Ww x = vanillaBlock σ Wr Ww x - c • x ᵥ* subProd S Wr Ww` | LEAN STRONGER (any `c`; the paper's case is `c = 1`, and general `c` is the proof of Proposition 5.4, tex l.898-900) |
| "generic blocks are nondegenerate" (tex l.631) | `ae_nondegenerate` (`SameWidth.lean` l.516-518): `2 ≤ card p`, `[Nonempty q]` | SAME (`d ≥ 2`; at least one output is needed and is automatic for `q = d`) |
| proof of Theorem 4.5 (tex l.652): "`GELU(y) − ReLU(y) = −abs(y) Φ(−abs(y))`" (written with `abs` here) | `gelu_sub_relu` (`SameWidth.lean` l.42) | SAME |
| ibid.: "`abs(GELU(ty)/t − ReLU(y)) ≤ κ/t` …, where `κ = max_{u≥0} u Φ(−u) < 0.17`" (and tex l.378: "`abs(GELU(tz) − t·ReLU(z)) < 0.17`") | `abs_gelu_sub_relu_le`: `abs (gelu y - relu y) ≤ 1` (l.62) | LEAN WEAKER as a number (bound `1`, not `0.17`); enough for the reduction. The constant `0.17` is not checked in Lean. |
| ibid.: "If a residual GELU network equals a skipless one, the two ReLU networks with the same weights are therefore equal." | `relu_absorb_of_gelu_absorb` (l.93-96): for one block with a linear term, of any two widths: the GELU equation `xM + B(x) = B′(x)` for all `x` implies the ReLU equation with the same weights | PART: one block (so networks of one block); the paper's reduction for networks of any depth is not stated |

## 4. Lists

### 4.1 Numbered statements of the paper with no Lean statement in the audited tree

Main text:
- Theorem 3.4 (no absorption in attention blocks), tex l.312-316. No attention block is defined in
  `Absorb/`.
- Theorem 4.2 (attention networks on long and short sequences), tex l.341-346.
- Theorem 4.3 (almost no equality under RMSNorm), tex l.355-357.
- Theorem 4.5 (the first block needs `2 d_model` units), tex l.373-375. Only a one-block form of the
  GELU-to-ReLU step of its proof is stated (3.19).
- Proposition 4.6 (injective blocks), tex l.384-386.
- Proposition 4.7 (a lower bound from counting dimensions), tex l.397-399.
- Proposition 5.1 (skipless networks as limits of residual networks), tex l.407-411; Remark 5.2
  (tex l.418); Remark 5.3 (tex l.422). (During the audit another process was compiling a module
  `SkipsLean.Absorb.Limits` in another worktree; there is no such file in `/home/claude/lw/lean`.)

Appendix A:
- Lemma A.5 (vanishing sums of ridge functions), tex l.540; Lemma A.6 (distinct scales), tex l.547.
  The Lean route for GELU (reduction to ReLU along rays) does not use them.
- Remark A.8 (the even part), tex l.579; Remark A.12, tex l.674; Theorem A.13 (attention and linear
  terms), tex l.698; Lemma A.14, tex l.734; Proposition A.15, tex l.769; Remark A.16, tex l.878.

Appendix C (blocks with biases): Theorem C.1 (tex l.930), Theorem C.2 (l.939), Remarks C.3, C.4,
C.5 (l.967, l.971, l.975), Proposition C.6 (l.985), Remark C.7 (l.999), Lemma C.8 (l.1029).
Appendix B has no numbered statement.

Stated only as an instance of a more general Lean statement, with no statement under their own
name: Theorem A.4 and Theorem A.7 (`M = I` in the equivalence); Corollary A.10 (`M = I` and
`M = −I` in the generic clause); the first sentence of Corollary A.3 (`E = D = E′ = D′ = I`); the
ReLU and GELU cases of Theorem 3.1 (ii), first half, and of Proposition 4.4 (`c = 1`); Theorem 4.1
(i) for each named kind of network (SwiGLU, GeGLU, ReLU², ReGLU).

### 4.2 Rows of `STATEMENTS.md` (section "Absorb paper") that are inaccurate

No row gives a wrong number of the paper, and no row misstates a hypothesis of the paper in a way
that changes a verdict. The following are imprecise:

1. Notes, last item: "Not stated yet: Corollary A.10, second half". It is the instance `M = −I` of
   `ae_not_relu_absorb_same_width` / `ae_not_gelu_absorb_same_width` (3.17; test T8). The first half
   (instance `M = I`) has no row either. The same note omits what else is not stated: Lemmas A.5,
   A.6 (mentioned in another note), Theorem A.13, Lemma A.14, Proposition A.15, the remarks, and
   Appendix B has nothing to state.
2. Row "A Corollary A.9 / Theorem A.4, 'only if' (ReLU, GELU; …)": for GELU the paper's theorem is
   Theorem A.7, not A.4.
3. Row "A eq. (1): … on a hidden state a block acts on each token | `vanillaBlock`, `gatedBlock`,
   `map_mul_mul_row`": `map_mul_mul_row` is for vanilla blocks only. No lemma relates `gatedBlock`
   to the block map of `Arch.gated`.
4. Row "A 'nondegenerate' …; generic blocks are nondegenerate (`p ≥ 2`)": `ae_nondegenerate` also
   needs at least one output, `[Nonempty q]`.
5. Row "A Theorem 3.1 (i), second sentence: for `M ≠ 0` and generic θ, no block of the same width":
   the Lean statements also assume `2 ≤ Fintype.card p` (said only in the notes).
6. Row for Theorem 3.1 (ii), second half: the two generic Lean statements also assume
   `2 ≤ Fintype.card d` (the paper's `d_model ≥ 2`); the row does not say so. The status of the two
   rows of `FewerUnits.lean` was "in work" when the audit began and is "proved" since 03:23 UTC;
   both were right at their time (`sorryAx` at 03:05, the three standard axioms after the
   recompilation of 03:25).
7. Introductory paragraph: "The one-block statements are for rectangular weights (`p` inputs, `q`
   outputs)": true of `Block.lean`, `NoWidth.lean`, `SameWidth.lean`; the statements of
   `FewerUnits.lean` are for square `d × d` (as the paper's).
8. Row "A proof of Theorem 4.5, 'GELU' …": accurate ("bounded"), but note that the paper's reduction
   is for networks of any depth and its constant is `κ < 0.17`; Lean has one block and the bound `1`.
9. Note "Theorem 3.1 for GELU: … The Lean statements for GELU are to be proved from the case of
   ReLU": out of date, they are proved (by that route).
10. Note on the public helper lemmas: `exists_ne_zero_forall_dotProduct_eq_zero`
    (`FewerUnits.lean` l.38-40, public since 03:23 UTC) is not listed.

## 5. What the authors should know (most serious first)

1. **Theorem 4.1 (i) and Corollary A.3: "positively homogeneous of degree `k > 1`" is not a Lean
   hypothesis.** Lean assumes `Arch.FlatAtZero` (every fixed map `f_ℓ` vanishes at `0` and has
   derivative `0` there). It proves this for gated blocks under the paper's condition on the gate,
   and for ReLU² and ReGLU. For another homogeneous block there is only the lemma
   `hasFDerivAt_zero_of_homogeneous`, which needs one more hypothesis, "bounded on the unit sphere",
   and is not connected to networks. The paper's proof of Corollary A.3 uses this bound without
   stating it (tex l.504, "because it is `O(‖x‖^k)`"). It holds for every continuous block map, so
   for every vanilla or gated block with a scalar activation; the paper could say so, and Lean could
   add the corollary. Also, no Lean theorem states Theorem 4.1 (i) for a named kind of network;
   each takes two applications (3.7).
2. **No Lean statement in scope says something different from the paper's statement, and none is
   weaker in the paper's own setting**, apart from item 1 and the constant of item 4. Every other
   difference is a generalization on the Lean side: rectangular weights and `M`; `M = 0` or singular
   `M` where the paper asks for `M ≠ 0` or invertible `M`; `σ(z) − σ(−z) = cz` in place of ReLU and
   GELU; two gates or two kinds of network where the paper has one; two values of `ε`; `L = 0`; the
   Scope assumptions that a statement does not need (table in 2.7). In each case the paper's
   statement is the special case, and for the cases listed in 2.10 this was checked in Lean. The
   quantifiers are in the paper's order: in every generic statement the absorbing block or the
   skipless network, with its width or model dimension, is quantified inside the `∀ᵐ`.
3. **"Exactly `d_model` units" was half proved when the audit began and is proved now.** The five
   statements of `Absorb/FewerUnits.lean` (Theorem 3.1 (ii), second half; Proposition A.11 (ii)) had
   `sorry` at 03:05 UTC; the file was replaced at 03:23 UTC and after recompilation `#print axioms`
   shows the three standard axioms only. The statements match the paper's (3.4). All other
   statements in scope were proved throughout.
4. **GELU to ReLU along rays** is stated for one block with a linear term
   (`relu_absorb_of_gelu_absorb`), with the bound `|GELU(y) − ReLU(y)| ≤ 1`. The paper states it for
   networks of any depth (proof of Theorem 4.5, tex l.652) and with the constant `κ < 0.17` (also in
   the main text, tex l.378). The one-block form is all that the statements in scope use; Theorem 4.5
   and Proposition 4.6 will need the network form. The number `0.17` is not checked in Lean.
5. **Several statements of the paper exist only as instances of a more general Lean statement**:
   Theorems A.4 and A.7 (`M = I`), Corollary A.10 (both halves, `M = I` and `M = −I`;
   `STATEMENTS.md` says the second half is not stated), the first sentence of Corollary A.3, the
   ReLU and GELU cases of Theorem 3.1 (ii), first half, and of Proposition 4.4, and Theorem 4.1 (i)
   for SwiGLU, GeGLU, ReLU², ReGLU networks. A reader who looks for them by name does not find
   them. One-line corollaries would close this; the tests T4, T5, T6, T8, U4, U6, X1 of 2.10 are
   such corollaries and they elaborate.
6. **"Generic" in Lean** is `∀ᵐ` for every additive Haar measure, on the pairs
   `(W_read, W_write)` for one block and on `(E, reads, writes, D)` for a network. This has the
   paper's null sets. For one block the product of the Lebesgue measures of the entries was checked
   to be such a measure (test W2). To apply a one-block generic statement, the instance
   `μ.IsAddHaarMeasure` has to be given by hand, because Mathlib's instance search does not see
   through `Matrix` (2.8).
7. **Conventions that differ from the paper without changing its cases.** `L = 0` is allowed (not
   a network of the paper); in Theorem 4.1 the skipless network has `L' + 1` blocks. A width is an
   index type and "the same width" is the same index type. Under a `∀ᵐ` the other width `m'` and
   the other model dimension `d'` range over `Type` (universe 0). In `Absorb/Networks.lean` the model
   dimension `d` of the first network is in `Type`, and the widths of every network are
   `Fin L → Type`. `gatedBlock` (one block) and `Arch.gated` (networks) are two definitions that no
   lemma connects. RMSNorm with `ε = 0`, where Lean's `rmsRow 0 0 = 0` differs from the paper's
   "undefined", occurs in no statement in scope.
8. **Hypotheses of the paper that the Lean statements show to be unnecessary**: `p ≥ 2` in the
   equivalence of Corollary A.9 and `d_model ≥ 2` in Theorem A.4 (the generic clauses do need
   `d ≥ 2`: for `d = 1`, `m ≥ 2` every ReLU block absorbs every `xM` at the same width); `M`
   invertible in Proposition A.11 (i) and in the first half of Theorem 3.1 (ii); `d_in, d_out ≥
   d_model ≥ 2` in Proposition 5.4 (nothing for (i), nonempty index sets for (ii)); "of the same
   kind" and one `ε` in Theorem 4.1 (i); `ED ≠ 0` and `d_model ≥ 2` in Proposition 4.4; `m ≥ d_model`
   in Theorem 3.1.
9. `STATEMENTS.md`, section "Absorb paper": no wrong number of the paper; ten imprecise rows or
   notes are listed in 4.2.
10. Not stated in Lean yet (4.1): Theorems 3.4, 4.2, 4.3, 4.5, Propositions 4.6, 4.7, 5.1, Remarks
    5.2, 5.3, Lemmas A.5, A.6, Remarks A.8, A.12, A.16, Theorem A.13, Lemma A.14, Proposition A.15,
    Appendix C.

## 6. Count

Compared: 19 statements or parts of statements of the paper (Theorem 3.1 in four parts, Proposition
3.2, Theorem 3.3, Theorem 4.1 in two parts, Proposition 4.4, Proposition 5.4 in two parts,
Propositions A.1, A.2, Proposition A.11 in two parts, Corollaries A.3, A.9, A.10, Theorem A.4), 7
definitions, and 3 statements of the text and of proofs (eq. (3), the flips of Section 3.1, the
GELU step of the proof of Theorem 4.5), against 46 Lean theorems and 7 Lean definitions of the five
files of `Absorb/`.
