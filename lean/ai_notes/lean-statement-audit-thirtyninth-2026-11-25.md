STATUS: complete

# Thirty-ninth audit of Lean statements against the papers: S Lemma A.8, the generated group for transformers (25 November 2026)

Commit read at the start: `7fe3cb0` (branch `lean-plus`, `/home/claude/lp`), 13:38 UTC. Commit at the end: `3f5e61c` (13:49 UTC). Between them no public statement or definition of the five files changed (`git diff 7fe3cb0 3f5e61c -- lean/SkipsLean`: nine `sorry` replaced by proofs, private helpers, two `omit … in`); at `3f5e61c` none of the five files has `sorry`.

Files with `sorry` at the start: `BiasesGeneratedGroupSum.lean` (5), `BiasesGeneratedGroupLocalRescale.lean` (3), `BiasesGeneratedGroupLocalAttention.lean` (1). `BiasesGeneratedGroupSumFree.lean` and `BiasesGeneratedGroupTransformer.lean` have none (they use the statements in work).

(Checks follow as they are done.)

Paper: `skips.txt` in `<scratchpad>`: S Lemma A.8 and its proof (lines 1258 to 1272), the Scope (lines 252 to 257), Section 2, Section 4.1 (lines 433 to 443), Appendix A.6 (lines 1538 to 1545), proof of Theorem B.1 (i) (lines 2686 to 2722). Earlier reports: the thirty-seventh and the thirty-eighth. Scratch work: `/home/claude/audit39/`.

The branch moved at once: at `a19ea67` (13:38 UTC) `insideBlocksLocal_rescaleMlp`, `insideBlocksLocal_rescale`, `insideBlocksLocal_rescaleBoth` and `insideBlocksLocal_heads` are proved; their statements are unchanged against `7fe3cb0` (compared line by line). From then on I read the files at `git show HEAD:…`, not the working tree (one file of the working tree had uncommitted changes).

## Part 1

### Check 1. The network and the family of the pairs (by reading)

Lean:

```lean
noncomputable abbrev Arch.attentionMlp sees σ χ H dh hid : Arch T d L :=
  (Arch.attention sees χ H dh).sum (Arch.mlp σ χ hid)
abbrev Arch.sum (A B : Arch T d L) : Arch T d L where
  r ℓ := A.r ℓ ⊕ B.r ℓ
  w ℓ := A.w ℓ ⊕ B.w ℓ
  f ℓ M := Matrix.of fun t p =>
    Sum.elim (A.f ℓ (M.submatrix id Sum.inl) t) (B.f ℓ (M.submatrix id Sum.inr) t) p
  χ := A.χ
structure Biases (A : Arch T d L) (dOut : Type*) where
  E : d → ℝ;  read : ∀ ℓ, A.r ℓ → ℝ;  write : Fin L → d → ℝ;  D : dOut → ℝ
-- hiddenB: h_ℓ = h_{ℓ-1} M_ℓ + (f_ℓ(χ h_{ℓ-1} W_read^ℓ + b_read^ℓ) W_write^ℓ + b_write^ℓ)
```

- **The transformer.** With `χ = id`, block `ℓ` of `Arch.attentionMlp sees σ id H dh hid` with biases maps `n` to `Att_ℓ(n [W_Q|W_K|W_V] + [b_Q|b_K|b_V]) W_O + σ(n W_1 + b_1) W_2 + b_write^ℓ`: the heads `H ℓ` (scores `⟨q_t, k_s⟩/√d_h`, softmax over the tokens `t` sees, values weighted) and the hidden units `hid ℓ` side by side, with **one** write bias per block (`Biases.write : Fin L → d → ℝ`, one row per block, not one per part). The paper's transformer (Section 2: "A transformer layer has two blocks, its attention and MLP sub-layers") is the case in which every block has heads only (`hid ℓ` empty) or hidden units only (`H ℓ` empty); then the empty part has no read column, no write row and no read bias, and the block is the attention block or the MLP block with its own output bias, so the parameters are exactly the paper's (with biases: `b_Q, b_K, b_V` per head, the output bias, the MLP read bias and write bias). The blocks with both parts (parallel attention and MLP, outside the paper) have one output bias, which is the right count: two would differ by a direction that moves neither the function nor anything else, and the sum would get one more spurious symmetry. No layer normalization (`χ = id`), as in Lemma A.8 ("without normalization"). SAME (Lean more general: parallel blocks).
- **`Biases.sumFst`, `Biases.sumSnd`**: `E`, `write`, `D` of the sum, `read ℓ j := b.read ℓ (Sum.inl j)` (resp. `Sum.inr`). **`sumReplaceFst a q`**: `E`, `D`, the embedding bias, all write biases and the readout bias from `a`; read columns, write rows and read biases from `a` at `Sum.inl`, from `q` at `Sum.inr`. `sumReplaceSnd` the mirror. What the header says. Right.
- **`sumAct actA actB (σ₁, σ₂) = sumLiftFst actA σ₁ ∘ sumLiftSnd actB σ₂`**: first `actB σ₂` on the second part of `q` (with the write bias of `q`), the result written back (the write bias becomes that of the image), then `actA σ₁` on the first part of that (with the new write bias). For `actA = headsAct`: on each head `W_Q K`, `W_K K^{-⊤}`, `b_Q K`, `b_K K^{-⊤}` (change of basis between queries and keys), `W_V K'`, `K'^{-1} W_O`, `b_V K'` (between values and outputs), `b_K + κ` (shift of the key bias), `b_V + ν` and `b_write − ∑_i ν_i (K'^{-1} W_O)_i` (value bias moved into the output bias). For `actB = rescaleMlpAct k`: column `i` of `W_1` and `b_{1,i}` times `c_i`, row `i` of `W_2` times `c_i^{-k}`, write bias kept; `rescaleAct`: value column and value bias times `c_i^{-1}`, write row times `c_i`; `rescaleBothAct k`: in addition gate column and gate bias times `c'_i`, write row times `c'_i^{-k}`. These are the paper's symmetries inside the blocks (Section 4.1: "the rescaling of a hidden unit of a ReLU or ReLU² block, the rescaling of the value of a hidden unit of a gated block, and the changes of basis inside an attention head"; A.6: "and, in ReGLU, its gate"), with biases those of the proof of Theorem B.1 (i) (line 2686: "The key biases drop out, since they shift all scores of a token equally, and the value biases enter only through `γ`, since the weights of a token sum to one"). Only the attention family touches the write bias, and by a row that depends on the writes; the composition is the composition of a symmetry of the attention parts and one of the MLP (or gated) parts. SAME. The rescalings are the positive ones (`posRescalings`: all `c_i > 0`), the identity component of the paper's nonzero rescalings (sign flips are finite for ReLU and remove nothing; A.6), and `headsSet` is `GL × GL × rows × rows`: the dimensions are those of the paper's families.

Verdict check 1: the network is the paper's transformer without normalization, with one write bias per block (also for parallel blocks); `sumAct` is the composition of the two families and acts as the paper's symmetries inside blocks do. SAME.

### Check 2. `InsideBlocksLocal` (by reading and by a computation)

Lean (`BiasesGeneratedGroupSum.lean`):

```lean
structure InsideBlocksLocal (act : F → Params A dIn dOut × Biases A dOut → …) (Sg : Set F) : Prop where
  E_eq : ∀ σ ∈ Sg, ∀ q, (act σ q).1.E = q.1.E
  D_eq : ∀ σ ∈ Sg, ∀ q, (act σ q).1.D = q.1.D
  biasE_eq : ∀ σ ∈ Sg, ∀ q, (act σ q).2.E = q.2.E
  biasD_eq : ∀ σ ∈ Sg, ∀ q, (act σ q).2.D = q.2.D
  block_eq : ∀ σ ∈ Sg, ∀ q ℓ (n : Matrix T d ℝ),
    A.f ℓ (n * (act σ q).1.read ℓ + of fun _ => (act σ q).2.read ℓ) * (act σ q).1.write ℓ
        + of (fun _ => (act σ q).2.write ℓ)
      = A.f ℓ (n * q.1.read ℓ + of fun _ => q.2.read ℓ) * q.1.write ℓ + of fun _ => q.2.write ℓ
  local_eq : ∀ σ ∈ Sg, ∀ q q', q.1.read = q'.1.read → q.1.write = q'.1.write → q.2.read = q'.2.read →
      (act σ q).1.read = (act σ q').1.read ∧ (act σ q).1.write = (act σ q').1.write ∧
      (act σ q).2.read = (act σ q').2.read ∧
      (act σ q).2.write - q.2.write = (act σ q').2.write - q'.2.write
  span_write : ∀ σ ∈ Sg, ∀ q ℓ, span (range ((act σ q).1.write ℓ).row) = span (range (q.1.write ℓ).row)
```

- **The fields against the four families** (by reading the definitions of `rescaleMlpAct`, `rescaleAct`, `rescaleBothAct`, `headsAct`): none of them reads or moves `E`, `D`, `b_E`, `b_D` (the four `_eq` fields hold by `rfl`, as the proofs at `a19ea67` use). `block_eq`: for `rescaleMlpAct k c` with `c > 0` it is `σ(c_i z_i) c_i^{-k} = σ(z_i)` (the hypothesis `hσ`), at every `n`, read bias included (`z_i = (n W_1 + b_1)_i`); for `rescaleAct` `σ(g_i)(v_i/c_i)(c_i a_i)`; for `rescaleBothAct k` both; for `headsAct` `(n W_Q + b_Q) K ((n W_K + b_K) K^{-⊤} + κ)^⊤ = Q K^⊤ + (Q K) κ^⊤`, a row shift of the scores (constant in `s`), which the softmax over the seen tokens removes; and `∑_s a_ts (v_s K' + ν) K'^{-1} W_O = ∑_s a_ts v_s W_O + ν K'^{-1} W_O` when `∑_s a_ts = 1`, which the write bias `− ∑_i ν_i (K'^{-1} W_O)_i` cancels. That needs every token to see a token (hypothesis `hsee`). `local_eq`: the new reads, writes and read biases are computed from the old reads, writes and read biases and `σ` alone; the write bias moves by `0` (rescalings) or by `− ∑_i ν_i (K_i'^{-1} W_{O,i})`, which depends on the writes alone. `span_write`: every write row is multiplied by a nonzero number (`c_i^{-k}`, `c_i`, `c_{1,i} c_{2,i}^{-k}`) or the rows of head `i` by the invertible `K_i'^{-1}`; the rows of head `i` and the rows of other heads span the same space before and after.
- **For some `σ ∈ Sg`?** `posRescalings` asks `c_i > 0`, so `c_i^{-k}` is defined and nonzero (also for `k = 0`); `headsSet` asks `IsUnit det` for both matrices of every head, so `glOfMatrix` is the matrix itself. No field fails at a point of `Sg`.
- **Computation** (`/home/claude/audit39/check2_local.py` with the model `model39.py`, float64; for every family a random `σ ∈ Sg`, random weights and biases, random `n`; `local_eq` with a second `q'` that has the same reads, writes and read biases and other `E`, `D`, `b_E`, `b_D` and write biases): largest errors

| case | `block_eq` | `local_eq` (write bias) | `local_eq` (reads, writes, read biases) | `E, D, b_E, b_D` | `span_write` | function (skips / no skips) |
|---|---|---|---|---|---|---|
| heads, full mask, `T = 4`, blocks `(H, d_h, hid) = (2,2,3), (1,3,0), (0,2,2)` | 2e-14 | 2e-15 | 0 | 0 | yes | 2e-14 |
| heads, causal mask | 6e-15 | 1e-16 | 0 | 0 | yes | 4e-14 |
| heads of width `0` | 4e-15 | 1e-16 | 0 | 0 | yes | 1e-14 |
| heads, `T = 1` | 2e-15 | 4e-16 | 0 | 0 | yes | 4e-15 |
| no head in any block | 0 | 0 | 0 | 0 | yes | 0 |
| ReLU rescalings (a block without hidden units among them) | 4e-15 | 0 | 0 | 0 | yes | 7e-15 |
| ReLU² rescalings | 4e-15 | 0 | 0 | 0 | yes | 1e-13 |
| ReLU, `T = 1` | 9e-16 | 0 | 0 | 0 | yes | 0 |
| SiLU gated, values | 1e-14 | 0 | 0 | 0 | yes | 1e-14 |
| ReGLU, values and gates (a block with heads of width `0`) | 4e-15 | 0 | 0 | 0 | yes | 7e-12 (outputs of order 10³) |

  `hsee` is needed: with a token that sees no token and `ν = 1` (`K = K' = 1`, `κ = 0`), `block_eq` for `headsAct` fails by `0.93` (same script, last line). The paper's attention always lets a token see itself, so `hsee` is implied.
- **Stronger than needed, or vacuous?** `block_eq` at every `n` (not only at reachable hidden states) and `local_eq` for every pair `q, q'` are what the four families give (proved at `a19ea67` for all four); neither is vacuous (`Sg` is not empty in all four, and the identity family satisfies the structure). `span_write` is more than `rank_write` of `InsideBlocksAction` and is what the sum needs: the rank of the stacked write `[W_A; W_B]` is the dimension of the sum of the two row spaces, which the ranks of `W_A` and `W_B` alone do not fix.

Verdict check 2: each field is true of the four families for every `σ ∈ Sg` (attention: when every token sees a token, needed and implied by the paper); nothing is vacuous or stronger than the families give.

### Check 3. `sumAct_parts`, `insideBlocksAction_sumAct`, `insideBlocksFreeAt_sumAct` (by reading and by a computation)

Lean (the first two still `sorry` at `a19ea67`; the third proved from them):

```lean
theorem sumAct_parts (lA : InsideBlocksLocal actA SgA) (lB : InsideBlocksLocal actB SgB)
    {σ : F₁ × F₂} (hσ : σ ∈ SgA ×ˢ SgB) (q) :
    (sumAct actA actB σ q).1.sumFst.read = (actA σ.1 (q.1.sumFst, q.2.sumFst)).1.read ∧ … (writes, read biases; the same for B) ∧
    (sumAct actA actB σ q).2.write
      = (actA σ.1 (q.1.sumFst, q.2.sumFst)).2.write + (actB σ.2 (q.1.sumSnd, q.2.sumSnd)).2.write - q.2.write ∧
    (sumAct actA actB σ q).1.E = q.1.E ∧ … D, b_E, b_D
theorem insideBlocksAction_sumAct (hA : InsideBlocksAction actA SgA) (lA : InsideBlocksLocal actA SgA)
    (hB : InsideBlocksAction actB SgB) (lB : InsideBlocksLocal actB SgB) :
    InsideBlocksAction (sumAct actA actB) (SgA ×ˢ SgB)
theorem insideBlocksFreeAt_sumAct (hA lA hB lB) (q)
    (fA : InsideBlocksFreeAt actA SgA (q.1.sumFst, q.2.sumFst))
    (fB : InsideBlocksFreeAt actB SgB (q.1.sumSnd, q.2.sumSnd)) :
    InsideBlocksFreeAt (sumAct actA actB) (SgA ×ˢ SgB) q
```

**`sumAct_parts`: true** (by reading). `sumLiftSnd actB σ₂ q` has the second part `b = actB σ₂ (q.sumSnd)`, the first part of `q`, write bias `b.w` and `E, D, b_E, b_D` of `b` (equal to those of `q`). Its first part has the reads, writes and read biases of `q.sumFst` and the write bias `b.w`; by `local_eq` of `A`, `actA σ₁` of it has the reads, writes and read biases of `a = actA σ₁ (q.sumFst)` and the write bias `b.w + (a.w − q.w)`. `sumReplaceFst` writes these back and keeps the second part. So the write bias is `a.w + b.w − q.w`, as stated, also when both families move it. `local_eq` is the hypothesis that makes this true: for a family whose write-bias move depended on the write bias itself (or on `E`), the order of the two lifts would matter and the formula would fail.

**`insideBlocksAction_sumAct`: true** (by reading, field by field).
- `one`: the pair of the two identities; `sumReplaceSnd (q.sumSnd) q = q` and the same for the first part.
- `mul`: with `actA τ₁ = actA σ₁ ∘ actA σ₁'` and `actB τ₂ = …`, `sumAct σ ∘ sumAct σ' = sumAct (τ₁, τ₂)`: by `sumAct_parts` twice and `local_eq` (the reads, writes and read biases of `actA σ₁` at the first part of `sumAct σ' q` are those at `actA σ₁' (q.sumFst)`, whose write bias differs), and the write-bias moves add: `Δ_A(τ₁, q) = Δ_A(σ₁, actA σ₁' q_A) + Δ_A(σ₁', q_A)`. `inv` the same with `τ` the inverses.
- `comm_residual`, `comm_skipless` (every pair `p`, not only those that preserve the function): `affAct p` acts on the first part of the sum as on a network of `A` (the columns `Sum.inl` of `G_ℓ^{-1} W_read` are `G_ℓ^{-1}` times those of `W_read`; the read biases move by `−(∑ g) W_read` column by column; the write bias, `E`, `D`, `b_E`, `b_D` are shared), so `affAct p ∘ sumReplaceFst a = sumReplaceFst (affAct p a) ∘ affAct p` and `(affAct p q).sumFst = affAct p (q.sumFst)`; with the commutation of each family this gives that of `sumAct`. (This field does not even need `local_eq`.)
- `evalB_eq` for every stream `S`: block `ℓ` of the sum is `f_A(n R_A + β_A) W_A + f_B(n R_B + β_B) W_B + b_w` (`f_sum_mul` with the read biases); with `sumAct_parts` and `block_eq` of both parts at `n`, the new block is `[f_A W_A + q.w] + [f_B W_B + q.w] − q.w`, the old block; `E`, `D`, `b_E`, `b_D` are kept.
- `rank_write`: the write of the sum stacks `W_A` over `W_B`; its rank is `dim(row W_A + row W_B)`, kept by `span_write` of both.

So `InsideBlocksAction (sumAct actA actB) (SgA ×ˢ SgB)` is the structure that `generatedGroup_residual` and `generatedGroup_skipless` take (the same structure, at `A.sum B`): identity, products, inverses, commutation with the maps of all pairs `(G, g)`, the function kept for every stream, the rank of every write kept. SAME.

**`insideBlocksFreeAt_sumAct`: true** (by reading its statement). `E`, `b_E` kept: from `sumAct_parts`. `write_eq_of_read_eq`: if the read and read bias of block `ℓ` of the sum are kept, both parts keep theirs, so by `fA`, `fB` both parts keep their writes and `a.w ℓ = b.w ℓ = q.w ℓ`, so the write bias `a.w + b.w − q.w` is kept at `ℓ`. `injOn`: equal images give parts with equal reads, writes and read biases; with `inv`, `mul` and `local_eq` the quotient `σ₁'^{-1} σ₁` keeps the reads and read biases of `q_A`, so (by `write_eq_of_read_eq` of `fA`) fixes `q_A`, so `actA σ₁ q_A = actA σ₁' q_A` and `σ₁ = σ₁'` by `fA.injOn`; the same for `B`. The hypotheses (both `InsideBlocksLocal`, both `InsideBlocksAction`, free at the two parts) are those used.

**Computation** (`/home/claude/audit39/check3_sum.py`: the Lean definitions `sumFst`, `sumSnd`, `sumReplaceFst`, `sumReplaceSnd`, `sumLiftFst`, `sumLiftSnd`, `sumAct` written out literally, float64, `d = 3`, `d_in = 4`, `T = 4`):
- attention with ReLU MLP, blocks `(H, d_h, d_hidden) = (2, 2, 3), (0, 2, 4), (1, 3, 2)` (a parallel block, an MLP block, a parallel block): `sumAct_parts` reads/writes/read biases `0`, write bias `4e-16`, `E, D, b_E, b_D` `0`; `one` `0`; `mul` (against `sumAct` of the composed pair, `τ = (K₁K₂, N₁N₂, κ₁K₂^{-⊤} + κ₂, ν₁N₂ + ν₂)`, `c c'`) `4e-15`; `comm_residual` with untied `G` `7e-15`; function with and without skips `8e-15`.
- **two families that both move the write bias** (attention parts on both sides: `Arch.attention.sum Arch.attention`, `sumAct headsAct headsAct`): write bias of `sumAct_parts` `9e-16`; `mul` `7e-12` on entries of size `2·10²` (relative `3e-14`); `comm_residual` `3e-14`; function `4e-13`. No counterexample.

Verdict check 3: the three statements are true as stated; `insideBlocksAction_sumAct` concludes exactly the structure used by the generated-group statements. SAME.

Commit after checks 1 to 3: the branch moved to `3f5e61c` (13:49 UTC); `sumAct_parts`, `insideBlocksAction_sumAct` and the three statements of the identity family are now proved. `git diff 7fe3cb0 3f5e61c -- lean/SkipsLean` removes nine lines `sorry` and adds proofs, private helpers and two `omit … in` lines; no public statement or definition changed. The index rows of the five files changed from "in work" to "proved".

### Check 4. `GeneratedGroupResidual`, `GeneratedGroupSkipless` (by reading and by compiling a copy)

Lean:

```lean
def GeneratedGroupResidual (A : Arch T d L) {F} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (act : F → Params A dIn dOut × Biases A dOut → Params A dIn dOut × Biases A dOut)
    (Sg : Set F) (μ : Measure (Params A dIn dOut)) (n : ℕ) : Prop :=
  (∀ φ, φ ∈ Subgroup.closure ({φ | ∃ p ∈ affPreservingResidual A dIn dOut, ⇑φ = affActResidual p}
            ∪ {φ | ∃ σ ∈ Sg, ⇑φ = act σ})
        ↔ ∃ p ∈ affPreservingResidual A dIn dOut, ∃ σ ∈ Sg, ⇑φ = affActResidual p ∘ act σ) ∧
    (∀ᵐ θ ∂μ, ∀ b : Biases A dOut, Set.InjOn (fun x => affActResidual x.1 (act x.2 (θ, b)))
      (affPreservingResidual A dIn dOut ×ˢ Sg)) ∧
    dimH (affMat (affPreservingResidual A dIn dOut) ×ˢ Sg) = ((n : ℕ) : ℝ≥0∞)
```

The three conjuncts are, character for character, the conclusion of `generatedGroup_residual` (quoted in the thirty-eighth report) with `n` in place of `d² + (L + 1) d + finrank F`; `GeneratedGroupSkipless` is the conclusion of `generatedGroup_skipless` with `affPreservingSkipless`, `affActSkipless` and `n` in place of `(L + 1)(d² + d) + finrank F`. Compiled (`/home/claude/audit39/Inst39.lean`, an `example` whose proof is the term `generatedGroup_residual hA hact hS hne μ hdIn hfree` at the type `GeneratedGroupResidual A act Sg μ (card d ^ 2 + (L + 1) * card d + finrank F)`): the definition unfolds to the theorem's conclusion by definition, no rewriting. `generatedGroupResidual_of_free` and `generatedGroupSkipless_of_free` are these terms. Drift: "at almost every weight, for every bias" (`∀ᵐ θ ∂μ, ∀ b`) and the Hausdorff dimension of the set of the pairs `(p, σ)` (matrices of `G`, rows `g`, points of `Sg`) are kept as the thirty-eighth reader compared them; the definition has no hypothesis of its own (no `χ = id`, no Haar measure: these stay in the theorems).

Verdict check 4: the same three statements with `n`. SAME; no drift.

### Check 5. The eight transformer statements (by reading, by compiling a copy, by a computation)

Lean (one of the eight; the others differ as listed below):

```lean
theorem generatedGroupResidual_attentionMlp [Nonempty T] [Nonempty dOut] [Nonempty d] {k : ℕ}
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (hsee : ∀ t, ∃ s, sees t s)
    (μ : Measure (Params (Arch.attentionMlp (T := T) (d := d) sees σ id H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) :
    GeneratedGroupResidual (Arch.attentionMlp (T := T) (d := d) sees σ id H dh hid)
      (sumAct headsAct (rescaleMlpAct k)) (headsSet H dh ×ˢ posRescalings hid) μ
      (card d ^ 2 + (L + 1) * card d
        + (2 * ∑ ℓ, card (H ℓ) * card (dh ℓ) ^ 2 + 2 * ∑ ℓ, card (H ℓ) * card (dh ℓ) + ∑ ℓ, card (hid ℓ)))
```

| statement | network, family | `n` | hypotheses beyond `hsee`, `μ` Haar, `d_in ≥ d`, `d_h ≤ d` |
|---|---|---|---|
| `generatedGroupResidual_attentionMlp` | `attentionMlp`, `headsAct` × `rescaleMlpAct k` | `d² + (L+1)d + 2∑Hd_h² + 2∑Hd_h + ∑d_hidden` | `T`, `d_out`, `d` not empty; `σ` homogeneous of degree `k` |
| `generatedGroupSkipless_attentionMlp` | same | `(L+1)(d²+d) + same s` | `d` not empty; `hσ`; `H d_h + d_hidden ≥ d` in every block |
| `generatedGroupResidual_attentionMlp_id` | `attentionMlp`, any `σ`, `headsAct` × identity on `Fin 0 → ℝ` | `d² + (L+1)d + 2∑Hd_h² + 2∑Hd_h` | `T`, `d_out` not empty |
| `generatedGroupSkipless_attentionMlp_id` | same | `(L+1)(d²+d) + same s` | `H d_h + d_hidden ≥ d` |
| `generatedGroupResidual_attentionGated` | `attentionGated`, any gate, `headsAct` × `rescaleAct` | `d² + (L+1)d + 2∑Hd_h² + 2∑Hd_h + ∑d_hidden` | `T`, `d_out`, `d` not empty |
| `generatedGroupSkipless_attentionGated` | same | `(L+1)(d²+d) + same s` | `d` not empty; `H d_h + d_hidden ≥ d` |
| `generatedGroupResidual_attentionGated_both` | `attentionGated`, gate homogeneous of degree `k`, `headsAct` × `rescaleBothAct k` | `d² + (L+1)d + 2∑Hd_h² + 2∑Hd_h + 2∑d_hidden` | `T`, `d_out`, `d` not empty; `hσ` |
| `generatedGroupSkipless_attentionGated_both` | same | `(L+1)(d²+d) + same s` | `d` not empty; `hσ`; `H d_h + d_hidden ≥ d` |

- **The number `s`.** `2 ∑ H d_h²`: the paper's changes of basis between queries and keys and between values and outputs, "of dimension `d_h²` each" per head (A.6; Table 6: "each attention block has `2 H d_h²` symmetries inside"). `∑ d_hidden`: one rescaling per hidden unit of a ReLU or ReLU² block or per value of a gated unit; `2 ∑ d_hidden` for ReGLU (values and gates) (A.6). `0` for tanh and GELU MLP blocks (Section 4.1: "for tanh and GELU blocks, `s = 0`"). `2 ∑ H d_h`: the shifts of the key biases and the value biases moved into the output bias, which the paper names in the proof of Theorem B.1 (i) (lines 2686, 2721: "the shifts of the key biases and the value biases moved into the output bias") but does not put into its `s`. So Lean's `n` is the dimension of the group generated by changes of basis, translations and **all** the symmetries inside the blocks with biases (computed below), and the paper's sentence, read with the paper's `s = 2 ∑ H d_h² + …`, is short by `2 ∑ H d_h` for transformers with biases (the thirty-eighth reader's point, unchanged here). This is a point for the authors, not a defect of Lean: Lean states the true dimension.
- **Hypotheses against the Scope** (`d_in, d_out ≥ d_model ≥ 2`; `d_hidden ≥ d_model`; `H d_h = d_model`; sequences of at least two tokens; Lemma A.8: "without normalization"):
  - `hsee` (every token sees a token): implied (the causal mask lets a token see itself; no mask: all); needed for `block_eq` of the value-bias move (check 2, computed).
  - `d_in ≥ d`: implied; sufficient, not necessary (thirty-seventh reader).
  - `[Nonempty d]` where a rescaling family is used: implied by `d_model ≥ 2`; needed for "every bias" (with `d` empty and a hidden unit, at the bias `0` every rescaling fixes `(θ, 0)`, so `injOn` fails: thirty-eighth reader, by reading). Not asked for the `_id` statements, where it is not needed (`d_h ≤ d = 0` leaves heads of width `0` and a space `HeadsSpace` of dimension `0`).
  - `d_h ≤ d`: implied by `H d_h = d_model`; needed exactly. With `d_h = d + 1` take `a ≠ 0` with `W_{V,i} a = 0` and `b ≠ 0` with `b^⊤ W_{O,i} = 0`, `N = ½ a b^⊤`, and `σ = (1, 1 + N, 0, −b_{V,i} N)` (one head; `det(1 + N) = 1 + ½ b^⊤a ≠ 0` generically): then `W_V(1 + N) = W_V`, `(1 + N)^{-1} W_O = W_O`, `b_V(1 + N) − b_V N = b_V`, and the write bias moves by `b_V N W_O = 0`, so `headsAct σ` fixes `(θ, b)` for every `θ`, `b` while `σ ≠ (1, 1, 0, 0)`; `injOn` fails and so does the second conjunct. Computed (`/home/claude/audit39/dh_needed.py`, `d = 2`, `d_h = 3`): `det = 1.19`, `|N| = 0.38`, `|headsAct σ q − q| = 2e-16`.
  - With skips `T`, `d_out` not empty: implied (sequences; `d_out ≥ 2`); needed to tie the `G_ℓ`.
  - Without skips `H d_h + d_hidden ≥ d` in every block: implied (every block of the paper's transformer is an attention block with `H d_h = d_model` or an MLP block with `d_hidden ≥ d_model`); used to make every write of rank `d` at almost every weight; not necessary for the dimension (thirty-seventh reader), but outside the Scope.
  - `hσ` (positively homogeneous of degree `k`): ReLU `k = 1`, ReLU² `k = 2`, the ReGLU gate `k = 1`: what the paper's rescaling needs.
  - `χ = id` is built into the statements (`Arch.attentionMlp … σ id …`): Lemma A.8 is "without normalization", so nothing is lost.
- **Empty index types** (by reading each statement once with each empty):
  - `T` empty: the residual statements ask `[Nonempty T]`; the skipless ones do not, `hsee` is then vacuous, and the conclusion is still true and meaningful (in a skipless network every pair preserves the function, empty `T` or not). Not vacuous, not false.
  - `d` empty: excluded where a rescaling is used; for `_id` it forces `d_h = 0`, `n = 0`, true. `d_in` empty: `hdIn` forces `d` empty (with `[Nonempty d]` the hypotheses are then contradictory, a corner outside the Scope only). `d_out` empty: excluded with skips; harmless without.
  - `H ℓ` empty in every block: an MLP (or gated) network, `s` reduces to `∑ d_hidden` (or `2 ∑`), the statements of the thirty-eighth report; `hid ℓ` empty in every block: an attention network, `s = 2 ∑ H d_h² + 2 ∑ H d_h`; `dh ℓ` empty: heads of width `0`, with no parameter, add `0`. `L = 0`: `n = d² + d` with skips and without, true. None is vacuous: the hypotheses are met by every transformer of the Scope.
- **Compiled instances** (`/home/claude/audit39/Inst39.lean`, `lake env lean` from `/home/claude/lp/lean` after checking that no `lake build` ran): `inst_residual` (ReLU transformer, `relu_homogeneous`, `Measure.addHaar`, any mask with `hsee`, with skips), `inst_skipless_both` (ReGLU transformer without skips), `inst_tanh` (tanh MLP blocks, the attention family alone), each `[propext, Classical.choice, Quot.sound]`. `#print axioms` of all fifteen public theorems of `BiasesGeneratedGroupTransformer.lean`, of `insideBlocksFreeAt_sumAct` and of the four `insideBlocksLocal_*`: `[propext, Classical.choice, Quot.sound]` (after the merges of 13:45 to 13:47; at 13:40 the transformer statements still depended on `sorryAx`). An instance with the causal mask written as `fun t s => s ≤ t` on a concrete `Fin 3` timed out at elaboration (`whnf`, also at 2,000,000 heartbeats) and an instance with concrete `Fin` index families too; with the mask and the families as variables (the theorems are stated for any `sees` with `[DecidableRel sees]`) everything compiles. I did not find the cause; it is a matter of elaboration, not of the statements.
- **Computation** (`/home/claude/audit39/orbit39.py`, the Lean definitions of `sumAct`, `headsAct`, `rescaleMlpAct 1`, `affActResidual`, `affActSkipless` written out; complex step, `h = 10^{-30}`): `d = 3`, `d_in = 4`, `d_out = 3`, `T = 4`, `L = 3` blocks `(H, d_h, d_hidden) = (2, 2, 0)` (attention), `(0, ·, 4)` (ReLU MLP), `(2, 1, 3)` (both), random weights and biases, two seeds. Rank of the derivative at the identity of `(p, σ) ↦ affActResidual p (sumAct headsAct (rescaleMlpAct 1) σ (θ, b))`: **60 of 60** with skips (smallest singular value `0.32` and `0.30`, no singular value below it, largest ratio of consecutive singular values `1.7`: the gap is to `0`), and `n = 9 + 12 + 2(8 + 2) + 2(4 + 2) + 7 = 60`. Without skips (`G_0, …, G_3` independent, `affActSkipless`): **87 of 87** (`σ_min = 0.30`, `0.15`), `n = 4·12 + 39 = 87`. A finite group element (all coordinates `0.2·N(0,1)`, rescalings `exp`) keeps the function of the ReLU transformer with the causal mask to `5e-14` with skips and `3e-14` without, so the model of the maps is right. The `2 ∑ H d_h = 12` bias directions are independent of the others.

Verdict check 5: the eight numbers are the dimensions of the groups generated with all symmetries inside the blocks with biases; every hypothesis is implied by the Scope, and those that are needed are needed; nothing is false or vacuous with an index type empty. Against the paper's own `s` the count has `2 ∑ H d_h` more (a point for the paper).

### Check 6. Verdict for the second sentence of Lemma A.8 (by reading, with checks 1 to 5)

The lemma (line 1259): "In a residual network with biases and without normalization, … The symmetry group generated by changes of basis, translations and the symmetries inside blocks therefore has dimension `d_model² + (L+1) d_model + s`, against `(L+1)(d_model² + d_model) + s` without skips, and the skips remove `L d_model²` dimensions, as without biases."

- **Transformers: SAME** (within the Scope). The eight statements give the three parts of the sentence (the generated group is the set of products; it is parametrized injectively by the pairs at almost every weight and every bias; the set of pairs has the stated dimension) for networks of attention blocks with biases and MLP blocks (ReLU, ReLU²; tanh, GELU with `s = 0` for the MLP blocks) or gated blocks (SwiGLU, GeGLU values; ReGLU values and gates), in any order, with and without skips; "the skips remove `L d_model²`" is the difference of the two numbers. Lean is more general than the paper in places (blocks with heads and hidden units side by side; any number of heads per block; any `d_h ≤ d`; no width with skips). The verdict is SAME and not DIFFERENT although the numbers differ from the paper's by `2 ∑ H d_h`: the `s` of Lean counts, beyond the paper's `2 ∑ H d_h²`, the `2 ∑ H d_h` shifts of the key and value biases; these are symmetries inside the blocks of the network with biases (the proof of Theorem B.1 (i) names them), so Lean's number is the dimension of the group the sentence describes, and the paper's `s` is the one to fix (point 1 below).
- **Normalization** is outside the lemma ("without normalization"), so "networks with normalization" is not a gap of this sentence.
- **Left without a statement**, all outside the Scope: skipless networks with a block whose writes have fewer than `d` rows in all (`H d_h + d_hidden < d`); networks with `d_in < d`; heads wider than `d_model` (where the statement would be false: check 5); networks that mix MLP and gated blocks (the Scope: "all MLP blocks are of one kind").
- **Overall for the second sentence of Lemma A.8, with the thirty-eighth report** (networks of one kind of block: SAME): **SAME within the Scope**, for every kind of block of the paper and for transformers; PART only outside the Scope (the cases just listed).

### Check 7. The index rows (by reading `STATEMENTS.md` at `3f5e61c`)

- Row of `BiasesGeneratedGroupSum.lean` (line 1129): every clause is true. It does not say what `sumAct_parts` says of the write bias (`a.w + b.w − q.w`), the one non-obvious formula; harmless.
- Row of `BiasesGeneratedGroupSumFree.lean` (line 1130): true.
- Rows of `BiasesGeneratedGroupLocalRescale.lean`, `…LocalAttention.lean`: true (the attention row has "when every token sees a token").
- Row of `BiasesGeneratedGroupTransformer.lean` (line 1133): every clause is true of the statements (the hypotheses list is exact, including "`d ≥ 1` not asked for the family of the attention blocks alone"). Missing: that `s` with attention blocks counts `2 ∑ H d_h` beyond the paper's `s`; that the `_id` statements hold for any activation, the full group for tanh and GELU; "Not stated" lists "networks with normalization", which Lemma A.8 excludes, and omits `d_in < d`; heads wider than `d` are excluded because the statement would be false there.
- Lines 429 to 434 ("Not yet compared, written after the thirty-eighth audit: …") are out of date after this report, and have a stray full stop ("(written at 13:30 UTC, 25 November).\nand …").
- `checks/Axioms.lean`: each of the 23 public theorems of the five files appears once; `ai_notes/axioms-check-latest.out` shows no `sorryAx`; my compiled copy agrees (check 5).

Verdict check 7: true where they speak; additions below.

## Part 2: the statements

`BiasesGeneratedGroupTransformer.lean` has 2 definitions and 13 public theorems (the brief's "15" counts the 15 public names of the index row).

| Lean | Paper sentence it serves | Verdict | Note |
|---|---|---|---|
| `GeneratedGroupResidual` (def) | S Lemma A.8, second sentence, with skips | SAME | the conclusion of `generatedGroup_residual` with `n` (definitional, compiled) |
| `GeneratedGroupSkipless` (def) | the same, "against … without skips" | SAME | the conclusion of `generatedGroup_skipless` with `n` |
| `generatedGroupResidual_of_free` | the same, for any family | SAME | `generatedGroup_residual` itself |
| `generatedGroupSkipless_of_free` | the same without skips | SAME | `generatedGroup_skipless` itself |
| `ae_insideBlocksFreeAt_sumAct` | the free action at generic parameters (Theorem A.17 (ii) hypothesis), for two kinds of block | SAME | hypotheses on the parts with `Measure.addHaar`, conclusion for any Haar `μ` on the sum (all are equivalent) |
| `generatedGroupResidual_sum` | Lemma A.8 for a network with two kinds of block | SAME | `n = d² + (L+1)d + dim F₁ + dim F₂` |
| `generatedGroupSkipless_sum` | the same without skips | SAME within the Scope | total write rows `≥ d` per block |
| `generatedGroupResidual_attentionMlp` | Lemma A.8, ReLU/ReLU² transformers, with skips | SAME | `s` includes `2 ∑ H d_h` bias shifts (paper's `s` does not); computed 60 = 60 |
| `generatedGroupSkipless_attentionMlp` | the same without skips | SAME within the Scope | `H d_h + d_hidden ≥ d`; computed 87 = 87 |
| `generatedGroupResidual_attentionMlp_id` | Lemma A.8, tanh/GELU transformers, with skips | SAME | any activation; the full group for tanh, GELU |
| `generatedGroupSkipless_attentionMlp_id` | the same without skips | SAME within the Scope | |
| `generatedGroupResidual_attentionGated` | Lemma A.8, SwiGLU/GeGLU transformers, with skips | SAME | positive value rescalings: identity component |
| `generatedGroupSkipless_attentionGated` | the same without skips | SAME within the Scope | |
| `generatedGroupResidual_attentionGated_both` | Lemma A.8, ReGLU transformers, with skips | SAME | `2 ∑ d_hidden` |
| `generatedGroupSkipless_attentionGated_both` | the same without skips | SAME within the Scope | |
| `sumAct_parts` | (tool) what a pair of symmetries inside the blocks does to each part | true | write bias `a.w + b.w − q.w`, needs `local_eq` |
| `insideBlocksAction_sumAct` | Section 4.1: symmetries inside the blocks of a transformer are those of its attention and MLP parts | SAME | the structure that the generic statements take |
| `insideBlocksAction_id` | Section 4.1: "for tanh and GELU blocks, `s = 0`" | SAME | |
| `insideBlocksLocal_id` | (tool) | true | |
| `insideBlocksFreeAt_id` | (tool) | true | singleton index space |
| `insideBlocksFreeAt_sumAct` | free action for two kinds of block | SAME | |
| `insideBlocksLocal_rescaleMlp` | Section 4.1, "the rescaling of a hidden unit of a ReLU or ReLU² block", acting block by block | SAME | any degree `k`, `c > 0` |
| `insideBlocksLocal_rescale` | "the rescaling of the value of a hidden unit of a gated block" | SAME | |
| `insideBlocksLocal_rescaleBoth` | A.6, "and, in ReGLU, its gate" | SAME | |
| `insideBlocksLocal_heads` | "the changes of basis inside an attention head"; B.1 (i) proof, key and value biases | SAME | `hsee` needed (computed) |

The definitions of `BiasesGeneratedGroupSum.lean` (`Biases.sumFst`, `Biases.sumSnd`, `sumReplaceFst`, `sumReplaceSnd`, `sumLiftFst`, `sumLiftSnd`, `sumAct`, `InsideBlocksLocal`): what their docstrings and the header say (checks 1 and 2).

## For the authors

Nothing false, vacuous or drifted.
1. (As the thirty-eighth reader, now for transformers.) With attention blocks and biases, the group of Lemma A.8 contains the shift of each key bias and the value bias moved into the output bias, `2 H d_h` dimensions per attention block, which the paper's `s` (`2 H d_h²` per block, Section 4.1, A.6, Table 6) does not count. For a transformer the sentence then reads `d_model² + (L+1) d_model + s + 2 ∑ H d_h`. Computed: orbit dimension 60 for `d = 3`, three blocks `(H, d_h, d_hidden) = (2,2,0), (0,·,4), (2,1,3)`, ReLU, with skips (87 without), equal to Lean's number with the bias shifts and 12 above the paper's. Suggested: "where, with biases, `s` also counts the `2 H d_h` shifts of the key and value biases of each attention block".
2. The heads must have width `d_h ≤ d_model` for the symmetries inside a head to act freely: at `d_h = d_model + 1` a nontrivial change of basis between values and outputs, with a value-bias move, fixes every parameter (computed). The Scope (`H d_h = d_model`) and Lemma A.18 have this; Lemma A.8 relies on it silently.
3. The value-bias move preserves the function only if every token sees some token (the weights of a token sum to one); with the paper's masks this holds.

## Corrections for `STATEMENTS.md`

- Lines 429 to 434: replace "Not yet compared, written after the thirty-eighth audit: `Symmetry/BiasesGeneratedGroupSum.lean`, `Symmetry/BiasesGeneratedGroupSumFree.lean`, `Symmetry/BiasesGeneratedGroupLocalRescale.lean`, `Symmetry/BiasesGeneratedGroupLocalAttention.lean` (written at 13:30 UTC, 25 November). and `Symmetry/BiasesGeneratedGroupTransformer.lean` (written at 13:36 UTC; statements and proofs by the coordinator from the statements of these four files)." by: "A thirty-ninth reader (25 November) compared `Symmetry/BiasesGeneratedGroupSum.lean`, `Symmetry/BiasesGeneratedGroupSumFree.lean`, `Symmetry/BiasesGeneratedGroupLocalRescale.lean`, `Symmetry/BiasesGeneratedGroupLocalAttention.lean` and `Symmetry/BiasesGeneratedGroupTransformer.lean` (read at `7fe3cb0` and `3f5e61c`; no statement changed in between): nothing false, vacuous or drifted; the orbit of a generic point of a ReLU transformer has the dimension of `generatedGroupResidual_attentionMlp` (60) and of its skipless twin (87); the second sentence of S Lemma A.8 is now stated for transformers and, with the thirty-eighth report, for every kind of network within the Scope; Lean's `s` with attention blocks counts `2 ∑ H d_h` bias shifts that the paper's `s` does not (`ai_notes/lean-statement-audit-thirtyninth-2026-11-25.md`)."
- Row of `Symmetry/BiasesGeneratedGroupTransformer.lean` (line 1133): replace "Not stated: networks with normalization, and skipless networks with a block narrower than `d`" by "Normalization is outside Lemma A.8. Not stated: skipless networks with a block whose heads and hidden units have fewer than `d` write rows in all, and networks with `d_in < d`; heads wider than `d` are excluded, and there the statement would be false (the symmetries inside a head do not act freely at `d_h = d + 1`, thirty-ninth reader)".
- Same row, after "`2 ∑ H d_h² + 2 ∑ H d_h + 2 ∑ d_hidden` with the rescalings of gated values and gates (ReGLU)." add: "The `2 ∑ H d_h` count the shifts of the key biases and the value biases moved into the output bias, which the paper's `s` (`2 ∑ H d_h²` for the attention blocks) does not. The statements with the family of the attention blocks alone hold for any activation; for tanh and GELU this is the whole group."
- Row of `Symmetry/BiasesGeneratedGroupSum.lean` (line 1129), optional: replace "what the map of a pair does to each part" by "what the map of a pair does to each part (the write bias moves by the sum of the two moves)".

## What I could not check

- An instance with the causal mask written as a concrete `fun t s => s ≤ t` on `Fin 3`, and one with concrete `Fin` index families, timed out at elaboration (`whnf`); the instances with the mask and the families as variables compile. I did not find the cause.
- `comm_skipless` of `insideBlocksAction_sumAct` I checked by reading only (the computation covered `comm_residual`, with untied `G`). `rank_write` of the sum was computed only at weights where every write has rank `d`; the general case is by reading (`span_write`).
- The orbit computation used one network shape, two seeds, ReLU only (not ReLU², the gated kinds or the `_id` family) and float64 with the complex step; the rank was full (no gap inside the spectrum, smallest singular value `0.15` or more), so the "largest gap" is the gap to `0`.
- I read the proofs only as far as their axioms (compiled copy, and the library's axiom file).
