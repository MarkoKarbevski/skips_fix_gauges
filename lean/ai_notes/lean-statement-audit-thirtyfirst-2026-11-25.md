STATUS: complete

# Thirty-first audit of Lean statements against the papers (25 November 2026)

Subject: networks with biases. The frame (`Network/Biases.lean`); changes of basis, translations and rescalings with biases, S Lemma A.8 and S Proposition A.1 (ii) (`Symmetry/BiasesSymmetries.lean`, `Symmetry/BiasesFlat.lean`, `Symmetry/BiasesRescale.lean`); the functional dimension with biases (`Dimension/FunctionalBiases.lean`); S Theorem B.1 (i) with biases for one tanh or GELU block (`OneBlock/MlpBiases.lean`); D Lemma D.13 for every admissible choice of `μ` (the last section of `Depth/ThetaDagger.lean`). 46 theorems and the definitions.

**Result.** Nothing false, nothing vacuous, nothing drifted. The frame is the paper's network with biases (each bias one row added to every token; `h_0 = xE + b_E`, `f_ℓ(h W_read + b_read) W_write + b_write`, `y = h_L D + b_D`), the Reduction of Appendix B comes out of it, and `P` with biases is the paper's (Table 6: `286`). Every statement at "almost every" is for every Haar measure on the pairs of weights and biases, and each was compiled at a concrete measure, with the numbers `17` and `21` of `29`. The changes of basis, the translations of Lemma A.8 (clause by clause) and the translations of a skipless network are the paper's maps, and they preserve the function in every network computed; `χ = id` is needed for the translations. The three directions are the derivatives of these maps and the directions of Lemma B.2's bias clause; the two upper bounds are the counts of Lemma A.8 without `s` (PART), their rank conditions are needed, and the bounds are attained by all tanh networks computed, the two rows "tanh, biases" of Table 6 included (`206` and `254`, recomputed). Theorem B.1 (i) with biases is the paper's for one tanh block and one GELU block: the two values, the gain `d²`, the equality condition in both of its forms, with the hypotheses of the theorem and conditions on the weights alone; 96 ranks computed inside the hypotheses equal the values. It is a part of the theorem (two kinds of block). The rescalings with biases scale each read bias by the factor of its read column and are the symmetries behind Step 3. The seven statements on `θ†` together are Lemma D.13 for every admissible `μ`: the verdict "LEAN WEAKER in `μ`" of the thirtieth audit no longer applies. The index rows are true of the statements, with one imprecision.

The statements and the definitions were read, not the proofs. Each check says how it was done: by reading, by compiling a copy (a file in `/home/claude/audit31/`, with `lake env lean` against the existing build, nothing written in the repository), by a computation (Python, `python3 -I`, scripts in `/home/claude/audit31/`: `netB.py` holds the network with biases written from the Lean definitions, with exact first derivatives by dual numbers), or by an argument of the reader, written out and checked by nobody else. The papers were read as the text files `skips.txt` and `dim.txt` in `<scratchpad>`. One computation was announced as possibly longer than five minutes (the two rows of Table 6); it took under two.

## Commits and `sorry`

The branch `lean-plus` of `/home/claude/lp` moved during the audit.

- At the start: `1bbd6a6` (03:14 UTC). The seven subject files were read at this commit. None contains `sorry` (by `grep`), and each has a build output newer than its source.
- At the end: `534437b` (03:36 UTC). Between `1bbd6a6` and `534437b` the seven files changed in comment lines only: 7 lines added and 4 removed in the headers of `Symmetry/BiasesSymmetries.lean`, `Symmetry/BiasesFlat.lean` and `OneBlock/MlpBiases.lean`, which now point to files written after this audit began. No statement and no definition changed (by `git diff`). The index rows were read at `534437b`.
- The commits in between add other files on networks with biases (the symmetries inside blocks in the count, SwiGLU, GeGLU, ReLU, ReLU² and ReGLU blocks, statements without differentiability), marked "in work" in the index. They are not the subject and were not read. Where this report says "not stated", it means: not stated in the seven files.

## Part 1: checks

### Check 1. The frame (`Network/Biases.lean`)

```lean
structure Biases (A : Arch T d L) (dOut : Type*) where
  E : d → ℝ
  read : ∀ ℓ, A.r ℓ → ℝ
  write : Fin L → d → ℝ
  D : dOut → ℝ

def hiddenB (M : Fin L → Matrix d d ℝ) (θ : Params A dIn dOut) (b : Biases A dOut)
    (x : Matrix T dIn ℝ) : Fin (L + 1) → Matrix T d ℝ :=
  Fin.induction (motive := fun _ => Matrix T d ℝ) (x * θ.E + Matrix.of fun _ => b.E)
    (fun ℓ h => h * M ℓ
      + (A.f ℓ (A.χ h * θ.read ℓ + Matrix.of fun _ => b.read ℓ) * θ.write ℓ
        + Matrix.of fun _ => b.write ℓ))

def evalB (M : Fin L → Matrix d d ℝ) (θ : Params A dIn dOut) (b : Biases A dOut)
    (x : Matrix T dIn ℝ) : Matrix T dOut ℝ :=
  A.χ (hiddenB A M θ b x (Fin.last L)) * θ.D + Matrix.of fun _ => b.D
```

**Where each bias enters, by reading.** The paper, Appendix A, first paragraph: "Biases, when present, enter as `B_ℓ(h) = f_ℓ(h W_read^ℓ + b_read^ℓ) W_write^ℓ + b_write^ℓ`, with row vectors `b` added to every token"; proof of Theorem A.5: "with `h_0 = xE + b_E`"; the Reduction: `γ_0 = b_write D + b_D`. Lean: `h_0 = x E + b_E`; `h_{ℓ+1} = h_ℓ M_ℓ + (f_ℓ(χ(h_ℓ) W_read^ℓ + b_read^ℓ) W_write^ℓ + b_write^ℓ)`; `y = χ(h_L) D + b_D`. Each bias is `Matrix.of fun _ => b`, the same row at every token. Without normalization (`χ = id`) this is the paper's network with biases: SAME.

**The Reduction, recomputed by hand** for one block from the two definitions. Skipless (`M = 0`): `h_1 = f((xE + b_E) W_read + b_read) W_write + b_write`, so `y = f(x E W_read + b_E W_read + b_read) W_write D + b_write D + b_D = f(xC + β) A + γ_0` with `β = b_E W_read + b_read`, `γ_0 = b_write D + b_D`. Residual (`M = 1`): `h_1 = xE + b_E + f(…) W_write + b_write`, so `y = x E D + f(xC + β) A + b_E D + b_write D + b_D = xM + f(xC + β) A + γ` with `γ = b_E D + γ_0`. These are the paper's formulas.

**By a computation** (`check1.py`, 40 digits, `d_in = 3`, `d = 2`, `d_out = 4`, 3 hidden units, two tokens, random weights and biases): `evalB` written from the Lean definition against `f(xC + β)A + γ_0` and `xM + f(xC + β)A + γ`, for a tanh block, a GELU block, a SwiGLU block and a ReGLU block: the largest difference is `1.8e-40`. With all biases `0`, `evalB` equals a separate transcription of `eval` exactly (difference `0`), which is `evalB_zero_biases`.

**Gated blocks, by reading.** For `Arch.gated` the read has the columns `hid ℓ ⊕ hid ℓ`, so `b.read ℓ` has one entry per gate (`Sum.inl i`) and one per value (`Sum.inr i`): the unit computes `σ(h c_i + β_i) · (h e_i + β_i′) a_i`. These are the paper's `β_i` and `β_i′` ("a gate `z_i = x c_i + β_i` and a value `w_i = x e_i + β_i′`"). SAME.

**With a normalization `χ`, by reading.** The read bias is added after the normalization and before the activation (`χ(h) W_read + b_read`), the readout bias after the readout (`χ(h_L) D + b_D`), and the embedding bias and the write biases are in the stream, so they are normalized with it by every later read. The paper states nothing with biases under normalization (Lemma A.8, Theorem B.1 (i) and the third value of Lemma A.27 are "without normalization"; Theorem B.1 (ii) to (v) are "without biases"), so there is nothing to compare; the placement is the usual one of a bias of a linear layer after a pre-norm. Of the six files only `evalB_cob`/`hiddenB_cob` (through the hypothesis `hχ`), the general statements of `Dimension/FunctionalBiases.lean` and the three rescalings are stated for a general `χ`.

**Attention blocks, by reading.** For `Arch.attention` the read has the columns `H ℓ × (dh ℓ ⊕ (dh ℓ ⊕ dh ℓ))` and the write the rows `H ℓ × dh ℓ`. So `Biases` gives one bias per coordinate of the query, of the key and of the value of every head (`b_{Q,i}`, `b_{K,i}`, `b_{V,i}`, added to `h W_Q`, `h W_K`, `h W_V` before the scores and the weighted sum), one row `b.write ℓ` of `d` entries added to the output of the block (`b_O`), and `b_E`, `b_D`. This is the paper's list near line 2676 ("`b_E` on the embedding, `b_{Q,i}`, `b_{K,i}`, `b_{V,i}` on the queries, keys and values, `b_O` on the output projection and `b_D` on the readout"), and the number of biases, `2d + 3 H d_h + d_out`, is the one behind the paper's "`2 d_model + 2 H d_h` lower" (the key biases and the value biases are `2 H d_h` flat directions). SAME as a frame; no theorem with biases is stated for attention blocks (check 6).

**The vector space and `P`.** `Biases A dOut` is a real vector space with the operations componentwise, linearly equivalent to the product of its four components (`linearEquivProd`), with the norm of that product; `ParamsB A dIn dOut = Params A dIn dOut × Biases A dOut`. `finrank_paramsB`: `P` with biases is the number of weights plus `d + ∑_ℓ r_ℓ + L d + d_out`. Against the paper's Table 6 ("tanh, biases", `d = 4`, `d_hidden = 8`, `L = 3`, input and output dimension 6): `240 + (4 + 24 + 12 + 6) = 286`, the paper's `P = 286`. So `P` with biases is the paper's ("counted in `P`"). SAME.

Verdict of check 1: **SAME** without normalization (frame, Reduction, gated biases, attention biases, `P`); with a normalization the paper has no network with biases to compare with.

### Check 2. Generic means almost every pair of weights and biases, for every Haar measure

**The `∀ᵐ` statements, by reading** (`grep` for `∀ᵐ` in the seven files): there are seven, one in `Dimension/FunctionalBiases.lean` (`ae_funDimB_ge`) and six in `OneBlock/MlpBiases.lean` (`ae_paramsB_of_forall_ae`, `ae_funDimB_mlp_oneBlock`, `ae_funDimB_mlp_oneBlock_residual`, `ae_funDimB_mlp_oneBlock_residual_eq_add`, `ae_funDimB_tanh_oneBlock_residual_eq_add`, `ae_funDimB_gelu_oneBlock_residual_eq_add`). Each has the form

```lean
(μ : Measure (ParamsB A dIn dOut)) [μ.IsAddHaarMeasure] … : ∀ᵐ p ∂μ, …
```

with `ParamsB A dIn dOut = Params A dIn dOut × Biases A dOut`: every Haar measure on the pairs of weights and biases. `Biases A dOut` has its Borel σ-algebra (`borel _`, with `BorelSpace`), as `Params` has; the pair has the product σ-algebra, which is the Borel σ-algebra of the product for these spaces of finite dimension. The index types: `T`, `d`, `dIn`, `dOut` have `Fintype` in the `variable` lines of both files, `hid ℓ` has `[∀ ℓ, Fintype (hid ℓ)]`, and `A.r ℓ`, `A.w ℓ` have `Fintype` as fields of `Arch`. So every index type of the weights and of the biases is finite, and the space of pairs has finite dimension (`finrank_paramsB`).

**By compiling a copy** (`/home/claude/audit31/Check2.lean`, no error): each of the statements at the concrete measure `Measure.addHaar : Measure (ParamsB A (Fin 2) (Fin 2))` for one tanh block and one GELU block with `T = Fin 2`, `d = Fin 2`, three hidden units; and, from them with `finrank_paramsB` and `finrank_params_mlp`, the numbers `P = 29`, `funDimB … 0 p = 17` and `funDimB … 1 p = 21` at almost every `p` (the header of `OneBlock/MlpBiases.lean` names 21 and 17 of 29). A copy with `22` in place of `21` fails, as it should.

**`ae_paramsB_of_forall_ae`.**

```lean
theorem ae_paramsB_of_forall_ae {L : ℕ} {A : Arch T d L} {P : Params A dIn dOut → Prop}
    (h : ∀ (ν : Measure (Params A dIn dOut)) [ν.IsAddHaarMeasure], ∀ᵐ θ ∂ν, P θ)
    (μ : Measure (ParamsB A dIn dOut)) [μ.IsAddHaarMeasure] :
    ∀ᵐ p ∂μ, P p.1
```

True as stated, by an argument of the reader: the set of the `θ` where `P` fails lies in a Borel set `N` of measure zero for the Haar measure `ν` of the weights; the set of the pairs where `P p.1` fails lies in `N × Biases`, which has measure zero for the product of `ν` and a Haar measure of the biases; every Haar measure on the pairs is a multiple of that product. `P` need not be measurable, and no hypothesis is missing (the statement also holds when there are no biases at all).

**Are the generic conditions of the paper conditions on the weights alone?** For tanh and GELU: yes. The Reduction: "For generic parameters `E`, `D`, `W_read` and `W_write` have rank `d_model`, every `a_i` is nonzero, and the `c_i` are nonzero and pairwise non-collinear". Lemma B.2 asks the four ranks; Lemma B.3 asks "every `a_i ≠ 0`" and "the `c_i` […] nonzero and pairwise non-collinear", and its proofs for tanh and GELU use the `β_i` only inside the expansions on the rays, with no condition on them; Step 3 uses "no column of `W_read` vanishes" for the rescalings, which are absent here. `OneBlockGeneric p.1` is this list (four ranks; rows of `A = W_write D` nonzero; columns of `C = E W_read` nonzero and pairwise non-collinear). So the statements at one parameter (`funDimB_mlp_oneBlock`, `funDimB_mlp_oneBlock_residual`, the two `flatB_le_range_…`) hold at every bias, the bias `0` included; check 6 computes this. A condition that involves biases appears in the paper only for the gated blocks ("`(e_i, β_i′)` not proportional to `(c_i, β_i)`"), which are not stated in Lean with biases.

**`UnitsRigid`** (`OneBlock/Mlp.lean`, compared by earlier audits):

```lean
def UnitsRigid (σ σ' : ℝ → ℝ) (n k q : Type*) [Fintype n] [Fintype k] [Fintype q] : Prop :=
  ∀ (c : q → n → ℝ) (β : q → ℝ) (a : q → k → ℝ)
    (ψM : Matrix n k ℝ) (ψγ : k → ℝ) (ψc : q → n → ℝ) (ψβ : q → ℝ) (ψa : q → k → ℝ),
    (∀ i, a i ≠ 0) → (∀ i, c i ≠ 0) → (∀ i j, i ≠ j → ∀ r : ℝ, c i ≠ r • c j) →
    (∀ x : n → ℝ,
      x ᵥ* ψM + ψγ + ∑ i, (σ (x ⬝ᵥ c i + β i) • ψa i
        + (σ' (x ⬝ᵥ c i + β i) * (x ⬝ᵥ ψc i + ψβ i)) • a i) = 0) →
    ψM = 0 ∧ ψγ = 0 ∧ ψc = 0 ∧ ψβ = 0 ∧ ψa = 0
```

This is Lemma B.3 for tanh and GELU with the biases: the sum is equation (15) with `z_i = x c_i + β_i` and the entries `ψ_M`, `ψ_γ`, `ψ_{c_i}`, `ψ_{β_i}`, `ψ_{a_i}`, the hypotheses are the lemma's, and the conclusion is "`ψ_M = 0`, `ψ_γ = 0`, and for every unit `ψ_{a_i} = 0`, `ψ_{c_i} = 0` and `ψ_{β_i} = 0`". It is in the library for both activations: `tanh_unitsRigid` (`OneBlock/Tanh.lean`, with `σ' = 1 − tanh²`) and `gelu_unitsRigid` (`OneBlock/GELU.lean`, with `geluDeriv`), for all finite index types; both depend on the three standard axioms only (check 9). The statements without biases used it with `β = 0`; the statements with biases use it with `β = b_E W_read + b_read`.

Verdict of check 2: generic is **almost every pair, for every Haar measure**; `ae_paramsB_of_forall_ae` is true; the conditions are on the weights alone, as in the paper for tanh and GELU; `UnitsRigid` is Lemma B.3 with biases and is proved for tanh and GELU.

### Check 3. Changes of basis and translations (`Symmetry/BiasesSymmetries.lean`)

```lean
def Biases.cob (b : Biases A dOut) (G : Fin (L + 1) → GL d ℝ) : Biases A dOut where
  E := b.E ᵥ* (G 0 : Matrix d d ℝ)
  read := b.read
  write ℓ := b.write ℓ ᵥ* (G ℓ.succ : Matrix d d ℝ)
  D := b.D

def Biases.translate (b : Biases A dOut) (θ : Params A dIn dOut) (k : Fin (L + 1)) (g : d → ℝ) :
    Biases A dOut where
  E := if k = 0 then b.E + g else b.E
  read ℓ := if k ≤ ℓ.castSucc then b.read ℓ - g ᵥ* θ.read ℓ else b.read ℓ
  write ℓ := if ℓ.succ = k then b.write ℓ + g else b.write ℓ
  D := b.D - g ᵥ* θ.D

def Biases.translateAt (b : Biases A dOut) (θ : Params A dIn dOut) (k : Fin (L + 1))
    (g : d → ℝ) : Biases A dOut where
  E := if k = 0 then b.E + g else b.E
  read ℓ := if ℓ.castSucc = k then b.read ℓ - g ᵥ* θ.read ℓ else b.read ℓ
  write ℓ := if ℓ.succ = k then b.write ℓ + g else b.write ℓ
  D := if k = Fin.last L then b.D - g ᵥ* θ.D else b.D

theorem evalB_cob
    (hχ : ∀ ℓ (h : Matrix T d ℝ), A.χ (h * (G ℓ : Matrix d d ℝ)) = A.χ h * (K ℓ : Matrix d d ℝ)) :
    evalB A (cobSkip M G) (θ.cob G K) (b.cob G) x = evalB A M θ b x
theorem evalB_translate (hA : A.χ = id) (k : Fin (L + 1)) (g : d → ℝ) :
    evalB A 1 θ (b.translate θ k g) x = evalB A 1 θ b x
theorem evalB_translateAt (hA : A.χ = id) (k : Fin (L + 1)) (g : d → ℝ) :
    evalB A 0 θ (b.translateAt θ k g) x = evalB A 0 θ b x
```

**`Biases.cob`, by reading.** The paper (end of the proof of Proposition A.1): "the affine change `h_ℓ ↦ h_ℓ G + g` is absorbed by `b_write ↦ b_write G + g` on the writes and by `(W, b) ↦ (G⁻¹ W, b − g G⁻¹ W)` on the reads". With `g = 0`: a bias that is written into `h_ℓ` is multiplied by `G_ℓ`, and a bias of a read does not change. In Lean the embedding bias is written into `h_0` (`b_E G_0`), the write bias of block `ℓ` into `h_{ℓ+1}` (`b_write^ℓ G_{ℓ+1}`, `G ℓ.succ`), and the read biases and the readout bias (the readout reads `h_L`) are unchanged. Right. The paper says the same for the map `Φ` of Theorem A.5: "`Φ` also sends the embedding bias `b_E` to `b_E Λ_0` and each write bias `b_write^ℓ` to `b_write^ℓ Λ_ℓ`, and keeps each read bias". The full affine change of the paper is `Biases.cob` followed by `Biases.translateAt` at the new weights (the read bias becomes `b − g (G⁻¹ W)`). `evalB_cob` has the form of `eval_cob`: any stream matrices `M`, replaced by `cobSkip M G = G_ℓ⁻¹ M_ℓ G_{ℓ+1}`, and a hypothesis `hχ` that relates `χ(h G_ℓ)` to `χ(h) K_ℓ`; with `χ = id` and `K = G` it is Proposition A.1 (ii) with biases. For the skipless network `cobSkip 0 G = 0`; for the residual network `cobSkip 1 G = 1` when all `G_ℓ` are equal. The file has no corollaries of the form of `eval_cob_skipless` and `eval_cob_residual`; they are private helpers of `Symmetry/BiasesFlat.lean`. Verdict: SAME as Proposition A.1 (ii) with biases and `g = 0`; LEAN STRONGER in that it also covers a normalization (`hχ`), which the paper states without biases only.

**`Biases.translate`, clause by clause, by reading.** Lean's block `ℓ : Fin L` reads `h_ℓ` (`ℓ.castSucc`) and writes `h_{ℓ+1}` (`ℓ.succ`); the paper's block `ℓ` (from 1) reads `h_{ℓ−1}` and writes `h_ℓ`. For the translation at `h_k`:

| paper (proof of Lemma A.8, translation at `h_ℓ`) | Lean (`b.translate θ k g`) |
|---|---|
| "Add `g` to the write bias of block `ℓ`" (the block that writes `h_ℓ`) | `write ℓ := if ℓ.succ = k then b.write ℓ + g`: the block that writes `h_k` |
| "or to the embedding bias when `ℓ = 0`" | `E := if k = 0 then b.E + g` |
| "subtract `g W_read^k` from the read bias of every block `k > ℓ`" (the blocks that read `h_ℓ, …, h_{L−1}`) | `read ℓ := if k ≤ ℓ.castSucc then b.read ℓ - g ᵥ* θ.read ℓ`: the blocks that read `h_k, …, h_{L−1}`, that is Lean's blocks `ℓ ≥ k`, the paper's blocks `ℓ + 1 > k` |
| "subtract `g D` from the readout bias" | `D := b.D - g ᵥ* θ.D` |

SAME. `hiddenB_translate` says that `h_m` is shifted by `g` at every token for `m ≥ k` and unchanged for `m < k` ("every later hidden state is shifted by `g`"), and `evalB_translate` is the first sentence of the lemma, for every `k = 0, …, L`, every `g`, any kind of block (`Arch` general), `χ = id` and the stream matrices `1`.

**`Biases.translateAt`, by reading.** "In a skipless network, where each hidden state has its own translation (Proposition A.1 (ii))": the affine change at `h_k` with `G = I`. Lean: `g` is added to the bias that enters `h_k`; `g W_read` is subtracted from the read bias of the one block that reads `h_k` (`ℓ.castSucc = k`), or `g D` from the readout bias when `k = L`. SAME. For `k = L` the two maps `translate` and `translateAt` are the same map.

**By a computation** (`check3.py`, 40 digits; three inputs of two tokens; random weights, biases, rows `g` and matrices `G`). Networks: tanh with 3 blocks (3, 2 and 4 units, `d = 2`), GELU with 2 blocks, SwiGLU with 2 blocks (`d = 3`), ReGLU with 3 blocks.

| map | network | largest change of the output |
|---|---|---|
| `translate` at each `k = 0, …, L` | residual | at most `8.9e-39` in all four networks; the hidden states `h_m`, `m ≥ k`, are shifted by `g` and the others are unchanged |
| `translate` at `k < L` | skipless (outside the statement) | between `0.31` and `787`: not a symmetry there |
| `translateAt` at each `k` | skipless | at most `3e-39`; only `h_k` is shifted |
| `translateAt` at `k < L` | residual (outside the statement) | between `0.79` and `1.5e4` |
| `cob`, `G_0, …, G_L` different | skipless | at most `9.2e-38` (ReGLU: `4.9e-36`, outputs of size `10⁴`) |
| `cob`, one `G` at all hidden states | residual | at most `8.7e-36` |
| `cob`, `G_ℓ` different, stream matrices `1` on both sides | residual (outside the statement) | between `18` and `1.7e4` |
| `cob` with random stream matrices `M` and `cobSkip M G` | general | at most `5.5e-36` |
| control: `cob` with the read biases doubled | skipless | between `3.8` and `1.3e5` |

In exact rational arithmetic (ReGLU, 2 blocks, rational weights, biases and inputs): the outputs after `translate` (residual) and after `translateAt` (skipless) at `k = 0, 1, 2` are equal to the outputs before, exactly.

**Is each hypothesis needed?** `χ = id` in the translations: under pre-RMSNorm with `ε = 1` (tanh, 2 blocks) `translate` changes the output of the residual network by `0.13`, `0.58` and `2.3` at `k = 0, 1, 2`, and `translateAt` that of the skipless network by `0.0014`, `0.051` and `1.8`. So the hypothesis is needed for these maps, as the lemma says ("without normalization"). The stream matrices (`1` for `translate`, `0` for `translateAt`): needed, by the table. `hχ` in `evalB_cob`: under RMSNorm with `ε = 1` the changes of basis by orthogonal `G_ℓ = K_ℓ` preserve the function with biases (`4.6e-41`, skipless with different `Q_ℓ` and residual with one `Q`), and for `ε = 0`, `G_ℓ = c_ℓ Q_ℓ`, `K_ℓ = Q_ℓ` too (`4.6e-41`); with general invertible `G_ℓ` the output changes by `0.37`.

Verdict of check 3: **SAME** (the three maps and the six statements); `evalB_cob` LEAN STRONGER (normalization through `hχ`, any stream matrices).

### Check 4. The functional dimension with biases (`Dimension/FunctionalBiases.lean`)

```lean
abbrev ParamsB (A : Arch T d L) (dIn dOut : Type*) : Type _ := Params A dIn dOut × Biases A dOut

def evalBatchB {n : ℕ} (X : Fin n → Matrix T dIn ℝ) (p : ParamsB A dIn dOut) :
    Fin n → Matrix T dOut ℝ := fun i => evalB A S p.1 p.2 (X i)
noncomputable def jacobianRankB {n : ℕ} (X : Fin n → Matrix T dIn ℝ) (p : ParamsB A dIn dOut) : ℕ :=
  Module.finrank ℝ (LinearMap.range (fderiv ℝ (evalBatchB A S X) p).toLinearMap)
noncomputable def funDimB (p : ParamsB A dIn dOut) : ℕ :=
  sSup {r : ℕ | ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), r = jacobianRankB A S X p}
noncomputable def flatB (p : ParamsB A dIn dOut) : Submodule ℝ (ParamsB A dIn dOut) :=
  ⨅ x : Matrix T dIn ℝ,
    LinearMap.ker (fderiv ℝ (fun q : ParamsB A dIn dOut => evalB A S q.1 q.2 x) p).toLinearMap
```

**Against Definition 4.1, by reading.** "For a finite batch `X = (x_1, …, x_n)` of inputs, let `F_X(θ) = (F_θ(x_1), …, F_θ(x_n))` […] `fd(θ) = max_X rank DF_X(θ)` […] over all finite batches `X`", with `θ ∈ ℝ^P` and, with biases, `θ` holding the biases too (Lemma A.27: "With biases, `θ` also holds `b_E`, `b_read^ℓ`, `b_write^ℓ` and `b_D`"; Theorem B.1 (i): "counted in `P`"). Lean: the parameter is the pair `p = (θ, b)`, the derivative is the Fréchet derivative in the pair, the rank is the dimension of its range, and `funDimB` is the supremum over all `n` and all batches of `n` inputs (attained: `exists_jacobianRankB_eq_funDimB`). `flatB` is the paper's `K(θ)` with the biases among the parameters ("Call `η` flat if `D_θ F(θ, x) η = 0` for every input `x`"). The four definitions are the definitions of `Dimension/Functional.lean` (`evalBatch`, `jacobianRank`, `funDim`, `flat`) with `ParamsB` for `Params` and `evalB` for `eval`, word for word. As there, `fderiv` is `0` where the map is not differentiable; for the blocks of the six files (tanh, GELU, any differentiable block) the output is differentiable everywhere. SAME.

**The nine statements, by reading, each against its twin.**

| statement | twin | true as stated? |
|---|---|---|
| `differentiable_evalB` (`f_ℓ` and `χ` differentiable ⟹ `(θ, b) ↦ F(x)` differentiable) | `differentiable_eval` | yes: sums, products and compositions of differentiable maps |
| `analyticOnNhd_evalB_params` (the same with real-analytic) | `analyticOnNhd_eval_params` | yes |
| `jacobianRankB_le_finrank` (`rank ≤ P`, biases counted) | `jacobianRank_le_finrank` | yes: the rank of a linear map is at most the dimension of its domain |
| `exists_jacobianRankB_eq_funDimB` | `exists_jacobianRank_eq_funDim` | yes: a nonempty set of natural numbers bounded by `P` has a largest element |
| `jacobianRankB_le_funDimB` | `jacobianRank_le_funDim` | yes |
| `funDimB_add_finrank_flatB` (`fd + dim K = P`, if the output at every input is differentiable in `(θ, b)` at `p`) | `funDim_add_finrank_flat` | yes: the paper's argument ("some finite batch has kernel exactly `K(θ)`. By rank–nullity …"); the hypothesis `hdiff` is the paper's implicit one |
| `funDimB_add_finrank_le_of_le_flatB` (`V ≤ K` ⟹ `fd + dim V ≤ P`) | `funDim_add_finrank_le_of_le_flat` | yes |
| `mem_flatB_of_hasDerivAt` (the velocity at `0` of a curve through `p` along which the function is the same near `0` is flat) | `mem_flat_of_hasDerivAt` | yes: the chain rule on a constant function |
| `ae_funDimB_ge` (real-analytic `f_ℓ`, `χ`; any stream matrices; every Haar measure `μ` on the pairs; `fd(p₀) ≤ fd(p)` for almost every `p`) | `ae_funDim_ge` | yes: a minor of the Jacobian on a batch that is nonzero at `p₀` is a real-analytic function of `p` that is not identically zero |

Each has the hypotheses and the conclusion of its twin, with the pair `(θ, b)` for `θ`. `ae_funDimB_ge` is for every Haar measure on the pairs (`(μ : Measure (ParamsB A dIn dOut)) [μ.IsAddHaarMeasure]`), compiled at `Measure.addHaar` in check 2.

Verdict of check 4: **SAME** (Definition 4.1 and the flat directions with the biases among the parameters); the nine statements are true as stated.

### Check 5. The directions and the two bounds (`Symmetry/BiasesFlat.lean`)

```lean
def cobDirB (p : ParamsB A dIn dOut) (X : Fin (L + 1) → Matrix d d ℝ) : ParamsB A dIn dOut :=
  (cobDir p.1 X,
    { E := p.2.E ᵥ* X 0
      read := fun _ => 0
      write := fun ℓ => p.2.write ℓ ᵥ* X ℓ.succ
      D := 0 })
def translateDir (θ : Params A dIn dOut) (g : Fin (L + 1) → d → ℝ) : Biases A dOut where
  E := g 0
  read ℓ := -((∑ k ∈ Finset.Iic ℓ.castSucc, g k) ᵥ* θ.read ℓ)
  write ℓ := g ℓ.succ
  D := -((∑ k, g k) ᵥ* θ.D)
def translateAtDir (θ : Params A dIn dOut) (g : Fin (L + 1) → d → ℝ) : Biases A dOut where
  E := g 0
  read ℓ := -(g ℓ.castSucc ᵥ* θ.read ℓ)
  write ℓ := g ℓ.succ
  D := -(g (Fin.last L) ᵥ* θ.D)

theorem cobDirB_const_add_translateDir_injective (hE : p.1.E.rank = Fintype.card d) :
    Function.Injective (fun Xg : Matrix d d ℝ × (Fin (L + 1) → d → ℝ) =>
      cobDirB p (fun _ => Xg.1) + ((0, translateDir p.1 Xg.2) : ParamsB A dIn dOut))
theorem cobDirB_add_translateAtDir_injective (hE : p.1.E.rank = Fintype.card d)
    (hw : ∀ ℓ, (p.1.write ℓ).rank = Fintype.card d) :
    Function.Injective
      (fun Xg : (Fin (L + 1) → Matrix d d ℝ) × (Fin (L + 1) → d → ℝ) =>
        cobDirB p Xg.1 + ((0, translateAtDir p.1 Xg.2) : ParamsB A dIn dOut))
theorem funDimB_add_le_residual (hA : A.χ = id) (hf : ∀ ℓ, Differentiable ℝ (A.f ℓ))
    (hE : p.1.E.rank = Fintype.card d) :
    funDimB A 1 p + (Fintype.card d ^ 2 + (L + 1) * Fintype.card d)
      ≤ Module.finrank ℝ (ParamsB A dIn dOut)
theorem funDimB_add_le_skipless (hA : A.χ = id) (hf : ∀ ℓ, Differentiable ℝ (A.f ℓ))
    (hE : p.1.E.rank = Fintype.card d) (hw : ∀ ℓ, (p.1.write ℓ).rank = Fintype.card d) :
    funDimB A 0 p + (L + 1) * (Fintype.card d ^ 2 + Fintype.card d)
      ≤ Module.finrank ℝ (ParamsB A dIn dOut)
```

**Are the directions the derivatives of the maps of check 3? Recomputed by hand and by a computation** (`check5a.py`, `dirs.py`).

- `cobDirB p X`: the derivative at `τ = 0` of `(θ.cob G G, b.cob G)` with `G_ℓ = 1 + τ X_ℓ` is `E X_0`, `−X_ℓ W_read^ℓ`, `W_write^ℓ X_{ℓ+1}`, `−X_L D` on the weights (`cobDir θ X`) and `b_E X_0`, `0`, `b_write^ℓ X_{ℓ+1}`, `0` on the biases. In exact rational arithmetic with dual numbers (two networks): equal to `cobDirB p X`, entry by entry.
- `translateDir θ g`: the translations do not move `θ`, and `b.translate θ k g − b` is linear in `g`. So the composition of the translations by `g_k` at `h_k`, `k = 0, …, L`, sends `b` to `b` plus: `g_0` on the embedding bias; `g_{ℓ+1}` on the write bias of block `ℓ`; `−(∑_{k ≤ ℓ} g_k) W_read^ℓ` on the read bias of block `ℓ` (the translations at `h_0, …, h_ℓ` reach the block that reads `h_ℓ`); `−(∑_k g_k) D` on the readout bias. This is `translateDir θ g` (`Finset.Iic ℓ.castSucc` is `{k ≤ ℓ}`), and the composition with `τ g_k` is `b + τ · translateDir θ g`, so the derivative is `translateDir θ g`. In exact rational arithmetic (3 blocks and 2 gated blocks): the composition of `Biases.translate` at `k = 0, …, L` equals `b + translateDir θ g` exactly.
- `translateAtDir θ g`: the same for the skipless network, with `−g_ℓ W_read^ℓ` on the read bias of block `ℓ` and `−g_L D` on the readout bias. The composition of `Biases.translateAt` at `k = 0, …, L` equals `b + translateAtDir θ g` exactly.

So the three directions are the derivatives at the identity of the maps of check 3. Flatness, 40 digits, the derivative of the output along the direction at three inputs of two tokens (tanh with 1 and 3 blocks, GELU with 2 blocks, SwiGLU with 2 blocks): along `cobDirB p (X, …, X) + (0, translateDir θ g)` in the residual network at most `3.1e-36`, along `cobDirB p (X_0, …, X_L) + (0, translateAtDir θ g)` in the skipless network at most `1.9e-36` (the outputs of the SwiGLU network are of size `10³`); controls: `cobDirB` with different `X_ℓ` in the residual network between `10.6` and `1.8e4`; `translateAtDir` in the residual network and `translateDir` in the skipless one between `0.15` and `1.1e3`; `cobDir` on the weights with the biases not moved between `1.5` and `6.2e3`. This agrees with the four statements `cobDirB_mem_flatB_skipless`, `cobDirB_const_mem_flatB_residual`, `translateDir_mem_flatB`, `translateAtDir_mem_flatB` (hypotheses `χ = id` and differentiable blocks).

**Against the bias clause of Lemma B.2, by reading** (one block, `X = X_0`, `Y = X_1`): "`η_{b_E} = b_E X + g_0`, `η_{b_read} = −g_0 W_read`, `η_{b_write} = b_write Y + g_1` and `η_{b_D} = −g_1 D`, respectively `η_{b_D} = −(g_0 + g_1) D`".

| | Lean, skipless: `cobDirB p X + (0, translateAtDir θ g)` | Lean, residual: `cobDirB p (X, X) + (0, translateDir θ g)` |
|---|---|---|
| `η_{b_E}` | `b_E X_0 + g_0` | `b_E X + g_0` |
| `η_{b_read}` | `0 − g_0 W_read` | `0 − g_0 W_read` (`∑_{k ≤ 0} g_k = g_0`) |
| `η_{b_write}` | `b_write X_1 + g_1` | `b_write X + g_1` |
| `η_{b_D}` | `0 − g_1 D` | `0 − (g_0 + g_1) D` |

and on the weights `η_E = E X_0`, `η_read = −X_0 W_read`, `η_write = W_write X_1`, `η_D = −X_1 D`. The same directions as the lemma's: SAME.

**The two injectivity statements.** The paper: "These `L + 1` translations move the biases in independent directions" (Lemma A.8) and "The matrices `X`, `Y` and vectors `g_0`, `g_1` are determined by the direction" (Lemma B.2, under "`E`, `D`, `W_read` and `W_write` have rank `d_model`"). Lean: `(X, g) ↦` direction is injective if `E` has rank `d` (residual: one `X`, `L + 1` rows), and if `E` and every write have rank `d` (skipless: `L + 1` matrices and `L + 1` rows). Sufficient by hand: `η_E = E X_0` gives `X_0`, `η_write^ℓ = W_write^ℓ X_{ℓ+1}` gives `X_{ℓ+1}`, and then the embedding bias and the write biases give the `g_k`. These are fewer conditions than Lemma B.2 lists (no rank of `D` or of the reads): LEAN STRONGER in the hypotheses. Needed? Exact examples in integers (`check5a.py`), checked against every hypothesis:

- Residual, `d = 2`, `E = [[1,0],[0,0]]` (rank 1), one hidden unit, `W_read = (1,0)^⊤`, `W_write = (1,0)`, `D = (1,0)^⊤`, `b_E = (1,0)`, `b_write = (3,0)`: the direction of `(X, g) = (e_2 e_2^⊤, 0)` is `0`, the direction of `(0, 0)`. Not injective without `hE`.
- Skipless, `d = 2`, `E = I` (`hE` holds), one hidden unit with `W_write = (1,0)` (rank `1`, `hw` fails), `D = (1,0)^⊤`, `b_write = (3,0)`: the direction of `(X_0, X_1, g) = (0, e_2 e_2^⊤, 0)` is `0`. Not injective without `hw`.
- Skipless, `d = 2`, two hidden units, `W_write = I` (`hw` holds), `E = 0`, `b_E = 0`, `W_read = [[1,2],[0,0]]`: the direction of `X_0 = [[0,1],[0,1]]`, `X_1 = 0`, `g = 0` is `0`. Not injective without `hE`.

**The two bounds against the count of Lemma A.8.** "The symmetry group generated by changes of basis, translations and the symmetries inside blocks therefore has dimension `d_model² + (L + 1) d_model + s`, against `(L + 1)(d_model² + d_model) + s` without skips". Lean: `fd + d² + (L + 1) d ≤ P` with skips and `fd + (L + 1)(d² + d) ≤ P` without, `P` counting the biases, for any differentiable blocks without normalization. These are the lemma's two numbers without `s`, in the form of upper bounds for the functional dimension (the form of Theorem 4.2), at every parameter with the stated ranks. The `s` of the symmetries inside blocks is not in the two statements; for tanh and GELU `s = 0`. The difference of the two bounds is `L d²` ("the skips remove `L d_model²` dimensions, as without biases"). Verdict: **PART** of the count (`s` is missing), SAME for what is stated; the lemma's own form (the dimension of a group) is not stated.

**Are the hypotheses of the bounds needed? By a computation** (`check5b.py`; a rank on a batch is a lower bound for the functional dimension, so a rank above the bound refutes the bound):

- `funDimB_add_le_residual` without `hE`: tanh, one block, `d = 4`, `d_in = 1` (so `E` has rank at most `1`), one hidden unit, `d_out = 1`: `P = 26`, the bound would give `fd ≤ 2`, the rank is `5` (two parameters). So `hE` is needed.
- `funDimB_add_le_skipless` without `hw`: tanh, one block, `d = 3 = d_in`, one hidden unit (the write has rank `1`), `d_out = 1`: `P = 26`, the bound would give `fd ≤ 2`, the rank is `6` (two parameters; `E` random of rank `3`). So `hw` is needed.
- The residual bound has no hypothesis on the width: tanh, `d = 3 = d_in = d_out`, one hidden unit: `P = 34`, rank `19`, the bound is `19`.

**Ranks of small tanh networks with biases against the bounds, by a computation** (`check5b.py`; exact derivatives by dual numbers at 40 digits; rank by elimination with complete pivoting; in every case the last pivot kept is above `1e-12` of the first and the next one below `1e-40`; two random parameters per case, each with its own batch).

| network (tanh, with biases) | `P` | residual: rank / bound `P − d² − (L+1)d` | skipless: rank / bound `P − (L+1)(d² + d)` |
|---|---|---|---|
| `L = 1`, `d = 2`, `d_in = d_out = 2`, 3 units | 29 | 21 / 21 | 17 / 17 |
| `L = 1`, `d = 3`, `d_in = d_out = 3`, 3 units | 48 | 33 / 33 | 24 / 24 |
| `L = 1`, `d = 2`, `d_in = 3`, `d_out = 4`, 5 units | 47 | 39 / 39 | 35 / 35 |
| `L = 2`, `d = 2`, `d_in = d_out = 2`, 3 and 3 units | 46 | 36 / 36 | 28 / 28 |
| `L = 2`, `d = 2`, `d_in = 3`, `d_out = 2`, 3 and 2 units | 43 | 33 / 33 | 25 / 25 |
| `L = 1`, `d = 2`, 3 units, inputs of two tokens | 29 | 21 / 21 | 17 / 17 |

In all 22 computations the rank equals the bound.

**Table 6 of the paper** ("confirms these counts for tanh networks with biases"). Its two rows "tanh, biases" can be read in `skips.txt`: `P = 286`, rank `206` without skips with the prediction `(L+1)(d_model² + d_model) = 80`, rank `254` with identity skips with the prediction `d_model² + (L+1) d_model = 32` (`d = 4`, `d_hidden = 8`, `L = 3`, input and output dimension 6). The Lean bounds for this network are `286 − 80 = 206` and `286 − 32 = 254`: the same numbers. Recomputed (`check5_table6.py`, exact derivatives at 60 digits, 80 inputs; this computation was announced as possibly longer than five minutes and took under two): rank `254` with identity skips and `206` without, next pivot below `1e-60`. A first run with 55 inputs (330 rows for 286 parameters) gave `230` with skips: outside the columns of `D` and `b_D` an input gives only `d = 4` independent rows of its 6, so a batch needs about `P/d` inputs, not `P/d_out`.

Verdict of check 5: the three directions are the derivatives of the maps and the directions of Lemma B.2: **SAME**; the injectivity statements are true with fewer rank conditions than the paper lists, and each condition is needed; the two bounds are the counts of Lemma A.8 **without `s`**, and they are attained by the tanh networks computed, the two rows of Table 6 included.

### Check 6. Theorem B.1 (i) with biases (`OneBlock/MlpBiases.lean`)

```lean
theorem flatB_le_range_mlp_skipless (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hU : UnitsRigid σ σ' dIn dOut (hid 0))
    (p : ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) (hp : OneBlockGeneric p.1)
    (η : ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)
    (hη : η ∈ flatB (Arch.mlp σ id hid) 0 p) :
    ∃ (X : Fin 2 → Matrix d d ℝ) (g : Fin 2 → d → ℝ),
      η = cobDirB p X + (0, translateAtDir p.1 g)
theorem flatB_le_range_mlp_residual … (hη : η ∈ flatB (Arch.mlp σ id hid) 1 p) :
    ∃ (X : Matrix d d ℝ) (g : Fin 2 → d → ℝ),
      η = cobDirB p (fun _ => X) + (0, translateDir p.1 g)
theorem ae_funDimB_mlp_oneBlock (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hU : UnitsRigid σ σ' dIn dOut (hid 0))
    (μ : Measure (ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ p ∂μ, funDimB (Arch.mlp σ id hid) 0 p + (2 * Fintype.card d ^ 2 + 2 * Fintype.card d)
      = Module.finrank ℝ (ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)
theorem ae_funDimB_mlp_oneBlock_residual … :
    ∀ᵐ p ∂μ, funDimB (Arch.mlp σ id hid) 1 p + (Fintype.card d ^ 2 + 2 * Fintype.card d)
      = Module.finrank ℝ (ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)
theorem ae_funDimB_tanh_oneBlock_residual_eq_add … :
    ∀ᵐ p ∂μ, funDimB (Arch.mlp Real.tanh id hid) 1 p
      = funDimB (Arch.mlp Real.tanh id hid) 0 p + Fintype.card d ^ 2
```

**The values, by reading.** The theorem: "For generic parameters the skipless network has functional dimension `P − 2 d_model² − s` and the residual network `P − d_model² − s`; with biases on the embedding, the block and the readout, counted in `P`, both values are `2 d_model` lower". For tanh and GELU `s = 0`. Lean: `fd + (2 d² + 2 d) = P` without the skip and `fd + (d² + 2 d) = P` with it, `P = finrank (ParamsB …)`, which counts `b_E`, `b_read`, `b_write`, `b_D` (check 1): the embedding, the block (read and write) and the readout. SAME. "The skip raises the functional dimension by exactly `d_model²`": `funDimB … 1 p = funDimB … 0 p + d²` at almost every `p`. SAME.

**The hypotheses, by reading.** The theorem: `d_model ≥ 2`; "the input and output dimensions be at least `d_model`"; "the block have width at least `d_model`"; "inputs range over all of `ℝ^{T × d_in}`"; no normalization. Lean: `hd : 2 ≤ card d`, `hdIn`, `hdOut`, `hhid`; `Arch.mlp σ id hid` (`χ = id`); `flatB` and `funDimB` over all inputs; `[Nonempty T]` (at least one token); and for the general statements the activation with `HasDerivAt σ (σ' z) z` for all `z` and `UnitsRigid σ σ' dIn dOut (hid 0)`, which is Lemma B.3 with biases for the activation (check 2). No extra hypothesis. The statements at one parameter (`funDimB_mlp_oneBlock`, `funDimB_mlp_oneBlock_residual`) ask `OneBlockGeneric p.1` and nothing of the biases.

**The two statements on the flat directions, by reading.** Step 3: "every flat direction is the sum of a direction of the changes of basis and translations of Lemma B.2 and a rescaling of the units […] The symmetries account for all of `K(θ)`, which is the equality condition". Definition 4.3: the equality condition holds "if its bound in Theorem 4.2 is attained at generic parameters, that is, if its symmetries are its only redundancy". For `s = 0`, Lean: every flat direction at a parameter with `OneBlockGeneric p.1` is `cobDirB p X + (0, translateAtDir θ g)` (skipless: `X_0, X_1`, `g_0, g_1`), respectively `cobDirB p (X, X) + (0, translateDir θ g)` (residual: one `X`, `g_0, g_1`); by check 5 these are the directions of the changes of basis and of the translations, which are flat. So the flat directions are exactly the directions of the symmetries: this is "its symmetries are its only redundancy" for the network with biases, in the form of Step 3. The other form of the equality condition, "the bound is attained at generic parameters", is `ae_funDimB_mlp_oneBlock` and `ae_funDimB_mlp_oneBlock_residual` together with the bounds `funDimB_add_le_skipless` and `funDimB_add_le_residual` of check 5 (for `L = 1`: `P − 2(d² + d)` and `P − d² − 2d`). Both forms are there: SAME. No statement uses the words of a definition "equality condition" for networks with biases; the library has none for them.

**Which activations are named.** `ae_funDimB_tanh_oneBlock_residual_eq_add` and `ae_funDimB_gelu_oneBlock_residual_eq_add` ("the skip raises the functional dimension by exactly `d²`") are the only statements with the activation written in. The two values for tanh and for GELU are the general statements applied to `tanh_unitsRigid` and `gelu_unitsRigid`; they compile (check 2, `Check2.lean`), but have no names of their own.

**By a computation** (`check6.py`; one block, exact derivatives by dual numbers at 40 digits, rank by elimination with complete pivoting; each parameter with two batches, the second with other inputs of twice the scale; 37 seconds).

Inside the hypotheses, sizes `(d, d_in, d_out, d_hidden)` = `(2,2,2,2)`, `(2,2,2,3)`, `(2,3,2,4)`, `(2,2,4,3)`, `(3,3,3,3)`, `(3,4,3,5)`, for tanh and for GELU, skipless and residual, with random biases and with all biases `0`: 48 parameters, 96 ranks. Every rank equals the theorem's value (`P − 2d² − 2d` without the skip, `P − d² − 2d` with it); for example `(2,2,2,3)`: `P = 29`, ranks `17` and `21`; `(3,4,3,5)`: `P = 65`, ranks `41` and `50`. The smallest pivot kept is `1.5e-8` of the first, the largest dropped `4.4e-41`. With inputs of two tokens (`(2,2,2,3)`): `17` and `21` again. The case "all biases `0`" confirms that the conditions are on the weights alone.

Where a condition on the weights fails (tanh, `(2,2,2,3)`, two hidden units with the same read column and the same read bias): ranks `15` and `19` against `17` and `21`. With the same read column and different read biases: `17` and `21`. So with biases the condition "the `c_i` are pairwise non-collinear" is sufficient and not necessary: in this example the pairs `(c_i, β_i)` differ and the values hold. The statements ask the condition of the paper.

Outside the hypotheses (two batches each, tanh and GELU give the same numbers):

| case | `(d, d_in, d_out, d_hidden)` | `P` | skipless: rank / formula | residual: rank / formula |
|---|---|---|---|---|
| `d = 1` | `(1,1,1,2)` | 11 | 7 / 7 | 8 / 8 |
| `d = 1` | `(1,2,2,3)` | 17 | 13 / 13 | 14 / 14 |
| `d_hidden < d` | `(2,2,2,1)` | 19 | 7 / 7 | 11 / 11 |
| `d_hidden < d` | `(3,4,3,1)` | 37 | 11 / 13 | 22 / 22 |
| `d_hidden < d` | `(3,3,4,2)` | 45 | 20 / 21 | 30 / 30 |
| `d_in < d` | `(2,1,2,3)` | 27 | 14 / 15 | 16 / 19 |
| `d_out < d` | `(2,2,1,3)` | 26 | 13 / 14 | 15 / 18 |

So `d_in ≥ d` and `d_out ≥ d` are needed for both values, and `d_hidden ≥ d` for the skipless value (a rank below the formula on two batches is not a proof that the functional dimension is below it, but here the rank cannot be larger: for `(3,4,3,1)` the skipless function `γ_0 + σ(xc + β) a` has `4 + 1 + 3 + 3 = 11` free numbers). For `d = 1`, which the theorem and the Lean statements exclude, the values with biases hold in the four cases computed: with biases two units of a one-dimensional network differ by their biases.

**What is not stated.** With biases, Theorem B.1 (i) is stated for one tanh block and one GELU block (and for every activation with `UnitsRigid`). Not stated with biases: ReLU, ReLU², ReGLU, SwiGLU and GeGLU blocks (the values `P − 2d² − 2d − s` and `P − d² − 2d − s` with `s > 0`; the rescalings of check 7 are there as symmetries, their directions and Lemma B.3 with biases for these activations are not); attention blocks ("`2 d_model + 2 H d_h` lower for attention"; the frame gives the biases, check 1); the third value of Lemma A.27 ("MLP blocks with biases, no normalization", any depth). The header of the file said this at `1bbd6a6` ("Not stated here: ReLU, ReLU², ReGLU, SwiGLU, GeGLU blocks and attention blocks with biases"); at `534437b` it points to files written after this audit began for the other MLP blocks (in work, not read) and says "Not stated: attention blocks with biases".

Verdict of check 6: **SAME** for one tanh block and one GELU block (the two values, the gain `d²`, the equality condition in both forms, the hypotheses); **PART** of Theorem B.1 (i) with biases (two of the seven kinds of MLP block and no attention).

### Check 7. The rescalings with biases (`Symmetry/BiasesRescale.lean`)

```lean
def Biases.rescaleMlp (b : Biases (Arch.mlp (T := T) (d := d) σ χ hid) dOut)
    (c : ∀ ℓ, hid ℓ → ℝ) : Biases (Arch.mlp (T := T) (d := d) σ χ hid) dOut where
  E := b.E
  read ℓ := fun i => c ℓ i * b.read ℓ i
  write := b.write
  D := b.D
noncomputable def Biases.rescale (b : Biases (Arch.gated (T := T) (d := d) σ χ hid) dOut)
    (c : ∀ ℓ, hid ℓ → ℝ) : Biases (Arch.gated (T := T) (d := d) σ χ hid) dOut where
  E := b.E
  read ℓ := Sum.elim (fun i => b.read ℓ (Sum.inl i)) (fun i => (c ℓ i)⁻¹ * b.read ℓ (Sum.inr i))
  write := b.write
  D := b.D
def Biases.rescaleGate … where
  read ℓ := Sum.elim (fun i => c ℓ i * b.read ℓ (Sum.inl i)) (fun i => b.read ℓ (Sum.inr i))
  …

theorem evalB_rescaleMlp {k : ℕ}
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (θ : Params (Arch.mlp (T := T) (d := d) σ χ hid) dIn dOut)
    (b : Biases (Arch.mlp (T := T) (d := d) σ χ hid) dOut) (c : ∀ ℓ, hid ℓ → ℝ)
    (hc : ∀ ℓ i, 0 < c ℓ i) (S : Fin L → Matrix d d ℝ) (x : Matrix T dIn ℝ) :
    evalB (Arch.mlp σ χ hid) S (θ.rescaleMlp k c) (b.rescaleMlp c) x
      = evalB (Arch.mlp σ χ hid) S θ b x
theorem evalB_rescale … (hc : ∀ ℓ i, c ℓ i ≠ 0) … :
    evalB (Arch.gated σ χ hid) S (θ.rescale c) (b.rescale c) x = evalB (Arch.gated σ χ hid) S θ b x
theorem evalB_rescaleGate {k : ℕ} (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z) …
    (hc : ∀ ℓ i, 0 < c ℓ i) … :
    evalB (Arch.gated σ χ hid) S (θ.rescaleGate k c) (b.rescaleGate c) x
      = evalB (Arch.gated σ χ hid) S θ b x
```

**Which entries are scaled by which factor, by reading**, with the maps on the weights (`Dimension/RescaleActionHomogeneous.lean`, `Dimension/RescaleAction.lean`):

| map | read column of unit `i` | read bias of unit `i` | write row of unit `i` | other biases |
|---|---|---|---|---|
| `rescaleMlp k c` (ReLU: `k = 1`; ReLU²: `k = 2`) | `× c_i` | `× c_i` | `× (c_i^k)⁻¹` | unchanged |
| `rescale c` (values of gated units) | gate column unchanged; value column `× c_i⁻¹` | gate bias unchanged; value bias `× c_i⁻¹` | `× c_i` | unchanged |
| `rescaleGate k c` (gates of ReGLU: `k = 1`) | gate column `× c_i`; value column unchanged | gate bias `× c_i`; value bias unchanged | `× (c_i^k)⁻¹` | unchanged |

In each map the bias of a unit is scaled by the factor of its read column, so the pre-activation `h c_i + β_i` is scaled as a whole; the embedding bias, the write biases and the readout bias do not change. The maps on the weights are those of the statements without biases, unchanged.

**Against Step 3 and Lemma B.3.** Step 3: "it scales column `i` of `W_read` and entry `i` of `b_read` by `λ_i` and row `i` of `W_write` by `−λ_i` for ReLU, by `−2λ_i` for ReLU², and similarly for ReGLU and for the values of SwiGLU and GeGLU". This is the direction; with `c_i = 1 + τ λ_i` the derivative at `τ = 0` of `rescaleMlp k c` is `λ_i` on the read column and on the read bias and `−k λ_i` on the write row: `−λ_i` for ReLU and `−2λ_i` for ReLU². For the values (`c_i = 1 + τ α_i`): `−α_i` on `(e_i, β_i′)` and `+α_i` on `a_i`, the lemma's "`(ψ_{e_i}, ψ_{β_i′}) = −α_i (e_i, β_i′)` and `ψ_{a_i} = α_i a_i`". For the gates of ReGLU: `λ_i` on `(c_i, β_i)` and `−λ_i` on `a_i`, the lemma's "`(ψ_{c_i}, ψ_{β_i}) = λ_i (c_i, β_i)` […] `ψ_{a_i} = (α_i − λ_i) a_i`" together with the value rescaling. The paper states the symmetries of the units with biases only as directions (Step 3) and in "scaling the input weights and the bias of unit `i` by `1 + τ λ_i` and its output weights by `1 − τ λ_i` changes the function only at second order"; the Lean statements give the exact symmetries, whose directions these are. SAME in content, LEAN STRONGER in form (exact maps; any depth; any `χ`; any stream matrices).

**The hypotheses.** `hσ`: `σ(λ z) = λ^k σ(z)` for all `λ > 0` and all `z` (positively homogeneous of degree `k`, a natural number), and `c_i > 0` for the units and the gates; `c_i ≠ 0` and no condition on the gate activation for the values. These are the hypotheses of the twins without biases. No hypothesis on `χ`, on the stream matrices or on the biases.

**By a computation** (`check7.py`; networks of two blocks with biases, inputs of two tokens, stream matrices `0`, `1` and a random `M`, six inputs; ReLU, ReLU² and ReGLU in exact rational arithmetic).

| network | map | result |
|---|---|---|
| ReLU, 3 and 2 units | `rescaleMlp 1 c` with `Biases.rescaleMlp c`, `c > 0` | outputs equal exactly |
| | the same without rescaling the biases | changes the output by `11.1` |
| | the degree `2` in place of `1` | `1.7e4` |
| | `c_i = −1` for one unit | `1.4e3` |
| ReLU², 3 and 2 units | `rescaleMlp 2 c` with `Biases.rescaleMlp c` | outputs equal exactly |
| | without the biases; degree `1`; `c_i = −1` | `1.5e4`; `2.2e6`; `9.3e6` |
| ReGLU, 2 and 3 units | values: `rescale c` with `Biases.rescale c`, `c ≠ 0`, some negative | outputs equal exactly |
| | the same without rescaling the value biases | `5.1e4` |
| | gates: `rescaleGate 1 c` with `Biases.rescaleGate c`, `c > 0` | outputs equal exactly |
| | without the gate biases; negative `c` on the gates | `3.1e4`; `3.1e9` |
| SwiGLU, 2 and 3 units, 40 digits | values: `rescale c` with `Biases.rescale c`, `c ≠ 0`, some negative | `3.8e-37` (outputs of size `10³`) |
| | without the value biases; the gate rescaling (SiLU is not homogeneous) | `6.8e3`; `191` |
| ReLU and SwiGLU under pre-RMSNorm with `ε = 1`, 40 digits | the same maps | `1.4e-40`; `1.8e-40` |

On the ReLU batches 13 of 60 pre-activations were positive and 47 negative (ReLU²: 21 and 39; ReGLU gates: 12 and 48), so both sides of the kinks were used.

Verdict of check 7: **SAME** as the rescalings of Step 3 and Lemma B.3 with biases; **LEAN STRONGER** in form. Each bias is scaled by the factor of its read column, and the hypotheses on `σ` and on `c` are needed (controls).

### Check 8. `θ†` for every admissible `μ` (`Depth/ThetaDagger.lean`, last section)

The thirtieth audit (its check 6) compared the definitions `thetaDaggerGated`, `thetaDaggerMlp`, `posOrthant` entry by entry (SAME) and found the three statements `exists_mu_…` weaker than the paper in the choice of `μ` (existence only). The last section adds seven statements for a given `μ`:

```lean
theorem goodForConesGated_thetaDaggerGated [Nonempty d] (ιE : d ↪ dIn) (ιD : d ↪ dOut)
    (c : ∀ ℓ, d ↪ hid ℓ) {μ : ∀ ℓ, hid ℓ → ℝ} (hμ : ∀ ℓ, ∀ j ∉ Set.range (c ℓ), 0 < μ ℓ j) :
    GoodForConesGated (fun _ => posOrthant d) (fun ℓ => Finset.univ.map (c ℓ))
      (thetaDaggerGated (T := T) (σ := σ) (χ := χ) ιE ιD c μ)
theorem frozenGated_thetaDaggerGated (ιE : d ↪ dIn) (ιD : d ↪ dOut) (c : ∀ ℓ, d ↪ hid ℓ)
    (μ : ∀ ℓ, hid ℓ → ℝ) (ℓ : Fin L) (n : d → ℝ) :
    frozenGated (thetaDaggerGated (T := T) (σ := σ) (χ := χ) ιE ιD c μ) ℓ
      (Finset.univ.map (c ℓ)) n = (∑ k, n k) • n
theorem linearIndependent_gate_thetaDaggerGated [Nonempty d] (ιE : d ↪ dIn) (ιD : d ↪ dOut)
    (c : ∀ ℓ, d ↪ hid ℓ) (μ : ∀ ℓ, hid ℓ → ℝ) (ℓ : Fin L)
    (hμ : ∀ (a : ℚ) (κ : hid ℓ → ℚ), (∀ i, κ (c ℓ i) = 0) →
      (a : ℝ) + ∑ j, (κ j : ℝ) * μ ℓ j = 0 → a = 0 ∧ ∀ j, κ j = 0) :
    LinearIndependent ℚ (fun j : hid ℓ =>
      ((thetaDaggerGated (T := T) (σ := σ) (χ := χ) ιE ιD c μ).read ℓ)ᵀ (Sum.inl j))
theorem linearIndependent_outer_gate_thetaDaggerGated (hd : 2 ≤ Fintype.card d) (ιE : d ↪ dIn)
    (ιD : d ↪ dOut) (c : ∀ ℓ, d ↪ hid ℓ) (μ : ∀ ℓ, hid ℓ → ℝ) (ℓ : Fin L)
    (hμ : ∀ κ : hid ℓ → ℚ, (∀ i, κ (c ℓ i) = 0) → ∑ j, (κ j : ℝ) * μ ℓ j ^ 2 = 0 →
      ∀ j, κ j = 0) :
    LinearIndependent ℚ (fun j : hid ℓ => Matrix.vecMulVec
      (((thetaDaggerGated (T := T) (σ := σ) (χ := χ) ιE ιD c μ).read ℓ)ᵀ (Sum.inl j))
      (((thetaDaggerGated (T := T) (σ := σ) (χ := χ) ιE ιD c μ).read ℓ)ᵀ (Sum.inl j)))
```

and `goodForConesMlp_thetaDaggerMlp`, `frozenMlp_thetaDaggerMlp` (`… = n`), `linearIndependent_outer_read_thetaDaggerMlp` for GELU blocks, of the same form.

**Positivity and independence at the units outside the image of `c ℓ` only, by reading.** The paper: "Choose numbers `μ_1, μ_2, … > 0` […] `c_j = −μ_{j−d_model} 𝟙` for `j > d_model`": the numbers `μ` belong to the hidden units after the first `d_model`. In Lean `μ ℓ j` is a number for every unit `j`, `θ†` uses it only when `j ∉ Set.range (c ℓ)`, and the hypotheses are `0 < μ ℓ j` for `j ∉ Set.range (c ℓ)` (the two statements "good") and the independence of those numbers (the three (K3) statements); nothing is asked at the units of the image. Right. The two formulas for the frozen blocks ask nothing of `μ`. The number may depend on the block and the independence is asked block by block, which the paper's one sequence `μ_1, μ_2, …` implies.

**"Linearly independent over `ℚ`" written out.** SwiGLU: for all rational `a` and all rational `κ` that vanish on the image of `c ℓ`, `a + ∑_j κ_j μ_j = 0` implies `a = 0` and `κ = 0`. Since `κ` vanishes on the image, the sum runs over the units outside it, and the statement is: the family `1, (μ_j)_{j outside}` is linearly independent over `ℚ`. GELU and GeGLU: `∑_j κ_j μ_j² = 0` implies `κ = 0`: the family `(μ_j²)_{j outside}` is linearly independent over `ℚ`, without the number `1`, as in the paper ("or such that `μ_1², μ_2², …` are"). By compiling a copy (`/home/claude/audit31/Check8.lean`, no error): Mathlib's `LinearIndependent ℚ` of the family `1, μ_j` (indexed by `Option {j // j ∉ Set.range c}`), respectively of the family `μ_j²` (indexed by `{j // j ∉ Set.range c}`), implies the hypothesis as written. So every `μ` that is admissible in the paper's sense satisfies the hypotheses.

**Each statement against its clause.**

| Lean | clause of Lemma D.13 and of its proof | verdict |
|---|---|---|
| `goodForConesGated_thetaDaggerGated`, `goodForConesMlp_thetaDaggerMlp` (`d ≥ 1`, `μ > 0` outside the image) | "`θ†` is good for the cones `C_0 = ⋯ = C_L = ℝ^{1×d_model}_{>0}`. For every block, `A_ℓ = {1, …, d_model}`": the cones are open convex cones without `0`; (R1); (K1) with the active set the image of `c ℓ` (the gates of these units positive on the orthant, the others negative); (K2); "no `a_j` and no `e_j` vanishes" of (K3) | SAME |
| `frozenGated_thetaDaggerGated`, `frozenMlp_thetaDaggerMlp` (every `μ`, every row `n`) | "`g°_ℓ(n) = n` for a GELU block and `g°_ℓ(n) = (n𝟙) n` for a gated block" | SAME |
| `linearIndependent_gate_thetaDaggerGated` (`d ≥ 1`) | (K3) "for SwiGLU blocks the columns `c_1, …, c_{q_ℓ}` are [linearly independent over `ℚ`]", under "`1, μ_1, μ_2, …` linearly independent over `ℚ`" | SAME |
| `linearIndependent_outer_gate_thetaDaggerGated`, `linearIndependent_outer_read_thetaDaggerMlp` (`d ≥ 2`) | (K3) "For GELU and GeGLU blocks the matrices `c_1 c_1^⊤, …, c_{q_ℓ} c_{q_ℓ}^⊤` are linearly independent over `ℚ`", under "`μ_1², μ_2², …` are" | SAME |

In Lean "good" is the structure `GoodForConesGated`/`GoodForConesMlp` (cones, (R1), (K1), (K2), the non-vanishing of (K3)) together with the independence over `ℚ` of (K3), which is a separate statement because it differs between SwiGLU and GeGLU; the paper's "good" is the two together. By compiling a copy (`Check8.lean`): for SwiGLU (`d ≥ 1`), for GeGLU and for GELU (`d ≥ 2`), from "`μ > 0` outside the image" and the independence written out, the seven statements give in one statement: good for the orthants with `A_ℓ` the image of `c ℓ`, the formula for the frozen block of every block at every row, and the independence of (K3) in every block. That is the whole lemma for every admissible `μ`.

**`d ≥ 1` against `d ≥ 2`.** The statements "good" and the SwiGLU statement ask `[Nonempty d]`; without a coordinate the orthant is the whole space and contains `0`. The two statements on the matrices `c_j c_j^⊤` ask `d ≥ 2`, as the paper's proof does ("the entries […] off the diagonal, which exist because `d_model ≥ 2`"), and it is needed: for `d = 1` and `μ_1² = 2`, `μ_2² = √2` the hypothesis holds and the `1 × 1` matrices `[1]`, `[2]`, `[√2]` are dependent (computed below).

**With numbers** (`check8.py`). (a) Exact rational arithmetic, `θ†` built from the Lean definitions for five sizes (`d = 1, 2, 3`), gated and MLP, with embeddings that are not the inclusions of the first indices, `μ` rational and positive outside the image (so not independent) and `0` or negative at the units of the image: (R1) (ranks `d`), (K1) on 200 rows of the orthant, the frozen block equal to `(n𝟙) n`, respectively `n`, exactly, with values in the orthant, the determinant `2 d^d` of the derivative at `n = 𝟙` for gated blocks, no zero write row: all true in the 10 cases. So "good" in Lean's sense holds for every `μ` that is positive outside the image, as stated. (b) The hypotheses, as exact linear algebra over `ℚ` in `ℚ(√2)`:

- SwiGLU, `μ = (√2, 1 + √2)`: the hypothesis fails, with `a = 1`, `κ = (1, −1)` (`1 + √2 − (1 + √2) = 0`); and the gate columns of `θ†` for `d = 2` are dependent: `e_1 + e_2 − c_3 + c_4 = 0`. PSLQ at 40 digits finds the same relation `[1, 1, −1]`.
- GELU and GeGLU, `μ² = (2, √2)`: the hypothesis holds (no rational relation between `2` and `√2`; PSLQ finds none with coefficients up to `10⁶`), although `1, 2, √2` have the relation `2 · 1 − 2 = 0`: the hypothesis is on the squares alone. The matrices `c_j c_j^⊤` of `θ†` have no rational relation for `d = 2` and `d = 3`; for `d = 1` they have the relation `2 [1] − [2] = 0`.
- Controls: `μ = (√2, 3)` fails the SwiGLU hypothesis (`3 · 1 − 3 = 0`); `μ² = (2, 8)` fails the hypothesis on the squares, and the matrices are then dependent.

Verdict of check 8: each of the seven statements is the paper's clause (**SAME**), and the seven together are **Lemma D.13 for every admissible `μ`**. The verdict "LEAN WEAKER in `μ`" of the thirtieth audit holds for the three statements `exists_mu_…` only; with the last section the lemma is formalized in full: SAME, and slightly LEAN STRONGER (`μ` may depend on the block; nothing is asked at the units of the image; independence block by block).

### Check 9. The index rows, the registrations, the axioms

**Axioms, by compiling a copy** (`/home/claude/audit31/Axioms31.lean`, against the existing build): `#print axioms` of the 46 theorems of the subject, of the two lemmas `hiddenB_zero` and `hiddenB_succ`, of the 16 public definitions (`hiddenB`, `evalB`, `Biases.linearEquivProd`, `Biases.cob`, `Biases.translate`, `Biases.translateAt`, `evalBatchB`, `jacobianRankB`, `funDimB`, `flatB`, `cobDirB`, `translateDir`, `translateAtDir`, `Biases.rescaleMlp`, `Biases.rescale`, `Biases.rescaleGate`), and of `tanh_unitsRigid`, `gelu_unitsRigid`, `ae_oneBlockGeneric`, which the statements for tanh and GELU use. All 67 depend on `propext`, `Classical.choice`, `Quot.sound` and on nothing else; no `sorryAx`. None of the seven files contains `sorry` (by `grep`).

**Registrations, by `grep`** in `checks/Axioms.lean`: each of the 46 theorems is registered exactly once (`#print axioms Skips.<name>`). The two `@[simp]` lemmas `hiddenB_zero`, `hiddenB_succ` are not registered; their twins `hidden_zero`, `hidden_succ` are not either, so this follows the convention of the file. Each of the 48 names is in a row of `STATEMENTS.md`.

**The rows, by reading** (`STATEMENTS.md` at `534437b`; the statements of the seven files did not change after `1bbd6a6`, see "Commits"). Every row names the right file, lists the public theorems of its file, and has the status "proved", which is true.

| row of | true of the statements? |
|---|---|
| `Network/Biases.lean` | Yes, every sentence: the four components, the vector space, the pair `(θ, b)`, the three formulas, "every bias added to every token", zero biases. The row does not list the auxiliary names (`Biases.Prod`, `equivProd`, `addHomProd`, `linearEquivProd`, `ext'`, the `@[simp]` lemmas on components). It could say what the frame gives for gated blocks (a gate bias and a value bias per unit) and for attention blocks (`b_Q`, `b_K`, `b_V` per head and one `b_O`), and that with a normalization the read bias is added after `χ`. |
| `Dimension/FunctionalBiases.lean` | Yes, every sentence, including "`funDimB + dim flatB = P` at a point of differentiability" (the hypothesis is differentiability in `(θ, b)` of the output at every input) and "every Haar measure". |
| `Symmetry/BiasesSymmetries.lean` | Yes. "The invariance in the form of `eval_cob`" is exact: any stream matrices with `cobSkip`, and a hypothesis on `χ`; the row could say that this also covers a normalization, and that the translations need `χ = id` (they fail under RMSNorm, check 3). |
| `Symmetry/BiasesFlat.lean` | Yes, every sentence, including the rank conditions and "not stated: […] the `s` of the lemma" in the form of the later commits (a pointer to the files written after this audit began). |
| `Symmetry/BiasesRescale.lean` | Yes, every sentence. |
| `OneBlock/MlpBiases.lean` | Yes, with one imprecision: "named for tanh and GELU" is true of the two statements on the gain `d²` only; the two values `P − 2d² − 2d` and `P − d² − 2d` are stated for every activation under `UnitsRigid` and have no statement with tanh or GELU written in (they follow by `tanh_unitsRigid`, `gelu_unitsRigid`; compiled in check 2). The row does not say that the general statements also ask `HasDerivAt σ (σ' z) z` for all `z`. |
| `Depth/ThetaDagger.lean` | Yes, both halves: the existence statements, and "the lemma for every admissible choice of `μ`" with its hypotheses (positive outside the image; `d ≥ 1` for "good" and for SwiGLU; `d ≥ 2` for the matrices; the independence written out; `μ` may depend on the block). |

The paragraph of the index "Not yet compared by such a reader" lists the six files and the seven statements; it is to be updated (see the corrections).

Verdict of check 9: the rows are true of the statements, with one imprecision (`OneBlock/MlpBiases.lean`, "named for tanh and GELU"); all 46 theorems are registered and depend on the three standard axioms only.

## Part 2: the statements, file by file

S = skips paper, D = dimension paper. "true" = an auxiliary statement without a sentence of the paper, true as stated.

| file | Lean | paper sentence | verdict | note |
|---|---|---|---|---|
| `Network/Biases.lean` | `Biases` (structure) | S Lemma A.27: "With biases, `θ` also holds `b_E`, `b_read^ℓ`, `b_write^ℓ` and `b_D`" | SAME | one row per bias; for gated blocks a gate and a value bias per unit; for attention `b_Q`, `b_K`, `b_V` per head and `b_O` |
| | `Biases.Prod`, `equivProd`, `addHomProd`, `linearEquivProd`, the instances, the `@[simp]` lemmas, `ext'` | none (aux.) | true | the vector space, the norm of the product, finite dimension |
| | `hiddenB`, `evalB` (defs) | S Appendix A: "Biases, when present, enter as `B_ℓ(h) = f_ℓ(h W_read^ℓ + b_read^ℓ) W_write^ℓ + b_write^ℓ`, with row vectors `b` added to every token"; "`h_0 = xE + b_E`"; the Reduction | SAME without normalization | with `χ`: read bias after `χ`; the paper has no such network |
| | `hiddenB_zero`, `hiddenB_succ` | none (aux.) | true | the two cases of the recursion |
| | `hiddenB_zero_biases`, `evalB_zero_biases` | S Reduction: "Without biases `β = 0` and `γ = γ_0 = 0`" | SAME | zero biases give `hidden`, `eval`; computed |
| `Symmetry/BiasesSymmetries.lean` | `Biases.cob` (def) | S proof of Proposition A.1: "absorbed by `b_write ↦ b_write G + g` on the writes and by `(W, b) ↦ (G⁻¹ W, b − g G⁻¹ W)` on the reads", `g = 0` | SAME | read biases and readout bias unchanged |
| | `hiddenB_cob`, `evalB_cob` | S Proposition A.1 (ii) with biases ("this gives `Aff(d_model)`", the linear part) | SAME; LEAN STRONGER (a normalization through `hχ`; any stream matrices) | no corollaries for `M = 0` and `M = 1` |
| | `Biases.translate` (def) | S proof of Lemma A.8: "Add `g` to the write bias of block `ℓ`, or to the embedding bias when `ℓ = 0`; subtract `g W_read^k` from the read bias of every block `k > ℓ`; subtract `g D` from the readout bias" | SAME | clause by clause, check 3 |
| | `hiddenB_translate` | "every later hidden state is shifted by `g`" | SAME | |
| | `evalB_translate` | S Lemma A.8, first sentence | SAME | any kind of block; `χ = id` needed |
| | `Biases.translateAt` (def), `hiddenB_translateAt`, `evalB_translateAt` | "in a skipless network, where each hidden state has its own translation (Proposition A.1 (ii))" | SAME | |
| `Dimension/FunctionalBiases.lean` | `ParamsB`, the Borel σ-algebra on `Biases` | "counted in `P`" | SAME | the pair `(θ, b)` |
| | `evalBatchB`, `jacobianRankB`, `funDimB` (defs) | S Definition 4.1 with the biases among the parameters | SAME | |
| | `flatB` (def) | S Appendix B: "Call `η` flat if `D_θ F(θ, x) η = 0` for every input `x`, and let `K(θ)` be the space of flat directions" | SAME | |
| | `differentiable_evalB`, `analyticOnNhd_evalB_params`, `jacobianRankB_le_finrank`, `exists_jacobianRankB_eq_funDimB`, `jacobianRankB_le_funDimB` | none (aux.) | true | twins of `Dimension/Functional.lean` |
| | `funDimB_add_finrank_flatB` | S Appendix B: "the functional dimension at `θ` is therefore `P − dim K(θ)`" | SAME | at a point of differentiability |
| | `funDimB_add_finrank_le_of_le_flatB`, `mem_flatB_of_hasDerivAt` | S after Definition 4.1: "the directions in which it moves `θ` lie in the kernel of every such Jacobian" | SAME | |
| | `ae_funDimB_ge` | the step from one parameter to generic parameters | true; every Haar measure on the pairs | real-analytic blocks and `χ` |
| `Symmetry/BiasesFlat.lean` | `cobDirB`, `translateDir`, `translateAtDir` (defs) | S Lemma B.2: "`η_{b_E} = b_E X + g_0`, `η_{b_read} = −g_0 W_read`, `η_{b_write} = b_write Y + g_1` and `η_{b_D} = −g_1 D`, respectively `η_{b_D} = −(g_0 + g_1) D`"; "the directions in which the changes of basis […] move the parameters, and, with biases, the translations at the two hidden states" | SAME | at any depth; the derivatives of the maps of check 3 (recomputed) |
| | `cobDirB_mem_flatB_skipless`, `cobDirB_const_mem_flatB_residual`, `translateDir_mem_flatB`, `translateAtDir_mem_flatB` | S Step 3: "conversely all of these are flat, since they come from symmetries"; S Lemma A.8, first sentence, in infinitesimal form | SAME | `χ = id`, differentiable blocks |
| | `cobDirB_const_add_translateDir_injective`, `cobDirB_add_translateAtDir_injective` | S Lemma A.8, proof: "These `L + 1` translations move the biases in independent directions"; S Lemma B.2: "The matrices `X`, `Y` and vectors `g_0`, `g_1` are determined by the direction" | SAME; LEAN STRONGER (fewer rank conditions than Lemma B.2) | each condition needed (exact examples) |
| | `funDimB_add_le_residual`, `funDimB_add_le_skipless` | S Lemma A.8: "dimension `d_model² + (L + 1) d_model + s`, against `(L + 1)(d_model² + d_model) + s` without skips" | PART (without `s`; as bounds on the functional dimension) | attained by the tanh networks computed and by the two rows of Table 6 |
| | `finrank_paramsB` | "counted in `P`" | SAME | Table 6: `240 + 46 = 286` |
| `OneBlock/MlpBiases.lean` | `flatB_le_range_mlp_skipless`, `flatB_le_range_mlp_residual` | S Step 3 with biases, `s = 0`: "every flat direction is the sum of a direction of the changes of basis and translations of Lemma B.2 and a rescaling of the units"; "The symmetries account for all of `K(θ)`, which is the equality condition" | SAME | under `OneBlockGeneric` on the weights; every bias |
| | `funDimB_mlp_oneBlock`, `funDimB_mlp_oneBlock_residual` | S Theorem B.1 (i) with biases, the two values, at one parameter | SAME | |
| | `ae_paramsB_of_forall_ae` | none (aux.) | true | generic weights ⟹ generic pairs |
| | `ae_funDimB_mlp_oneBlock`, `ae_funDimB_mlp_oneBlock_residual` | S Theorem B.1 (i): "with biases on the embedding, the block and the readout, counted in `P`, both values are `2 d_model` lower" (`s = 0`) | SAME for tanh and GELU; PART of the theorem (kinds of block) | every Haar measure; hypotheses those of the theorem |
| | `ae_funDimB_mlp_oneBlock_residual_eq_add`, `ae_funDimB_tanh_oneBlock_residual_eq_add`, `ae_funDimB_gelu_oneBlock_residual_eq_add` | "the skip raises the functional dimension by exactly `d_model²`" | SAME | |
| `Symmetry/BiasesRescale.lean` | `Biases.rescaleMlp`, `evalB_rescaleMlp` | S Step 3: "it scales column `i` of `W_read` and entry `i` of `b_read` by `λ_i` and row `i` of `W_write` by `−λ_i` for ReLU, by `−2λ_i` for ReLU²" | SAME in content; LEAN STRONGER in form (exact symmetry, any depth, any `χ`, any stream matrices) | |
| | `Biases.rescale`, `evalB_rescale` | "and similarly […] for the values of SwiGLU and GeGLU"; S Lemma B.3: "`(ψ_{e_i}, ψ_{β_i′}) = −α_i (e_i, β_i′)` and `ψ_{a_i} = α_i a_i`" | SAME; LEAN STRONGER in form | any gate activation, `c ≠ 0` |
| | `Biases.rescaleGate`, `evalB_rescaleGate` | "and similarly for ReGLU"; S Lemma B.3: "`(ψ_{c_i}, ψ_{β_i}) = λ_i (c_i, β_i)`" | SAME; LEAN STRONGER in form | |
| `Depth/ThetaDagger.lean`, last section | `goodForConesGated_thetaDaggerGated`, `goodForConesMlp_thetaDaggerMlp` | D Lemma D.13: "`θ†` is good for the cones `C_0 = ⋯ = C_L = ℝ^{1×d_model}_{>0}`. For every block, `A_ℓ = {1, …, d_model}`" ((R1), (K1), (K2), the non-vanishing of (K3)) | SAME | every `μ` positive outside the image of `c ℓ` |
| | `frozenGated_thetaDaggerGated`, `frozenMlp_thetaDaggerMlp` | "`g°_ℓ(n) = n` for a GELU block and `g°_ℓ(n) = (n𝟙) n` for a gated block" | SAME | every `μ` |
| | `linearIndependent_gate_thetaDaggerGated` | (K3) for SwiGLU under "`1, μ_1, μ_2, …` are linearly independent over `ℚ`" | SAME | `d ≥ 1`; block by block |
| | `linearIndependent_outer_gate_thetaDaggerGated`, `linearIndependent_outer_read_thetaDaggerMlp` | (K3) for GeGLU and GELU under "`μ_1², μ_2², …` are" | SAME | `d ≥ 2`, needed |
| | the seven together | D Lemma D.13 for every admissible `μ` | SAME (compiled as one statement, check 8) | answers "LEAN WEAKER in `μ`" of the thirtieth audit |

## What the authors of the papers should know

Nothing in the six files and in the last section of `Depth/ThetaDagger.lean` is false, vacuous or drifted. Where Lean and the papers differ, Lean is stronger, or it states a part: Lemma A.8's count without `s`, and Theorem B.1 (i) with biases for tanh and GELU only (at the commit read; later commits add statements for other blocks, which this audit did not read).

Places where a statement or a proof of the papers needs a condition that it does not write, or could say more:

1. **S Lemma A.8, the count, read as a count of redundant parameters:** the directions of the changes of basis and of the translations are independent when `E` has rank `d_model` (with skips), and when `E` and every write have rank `d_model` (without skips). Without these ranks the count fails as a bound on the functional dimension: one tanh block with biases, `d_model = 4`, `d_in = 1`, one hidden unit, `d_out = 1`, with the skip: `P = 26`, rank `5`, against `P − d² − 2d = 2`; `d_model = 3 = d_in`, one hidden unit, `d_out = 1`, without the skip: `P = 26`, rank `6`, against `P − 2d² − 2d = 2`. The lemma has no hypothesis on the dimensions; the Scope (`d_in, d_out, d_hidden ≥ d_model`) gives the ranks at generic parameters. For the counts themselves the lemma is confirmed: all tanh networks with biases computed here (22 ranks at one and two blocks, and the two rows "tanh, biases" of Table 6, recomputed at 60 digits: `206` and `254` of `286`) have exactly `P − (L+1)(d² + d)` and `P − d² − (L+1)d`.
2. **S Lemma A.8, "without normalization":** needed. The translations of the lemma change the function under pre-RMSNorm (by `0.13` to `2.3` in the example of check 3).
3. **S Theorem B.1 (i) with biases, the generic conditions:** for tanh and GELU they are conditions on the weights alone (the four ranks; `a_i ≠ 0`; the `c_i` nonzero and pairwise non-collinear), and the values hold at every bias, the bias `0` included (computed, and proved in Lean at every parameter with these conditions). With biases the condition "pairwise non-collinear" is sufficient and not necessary: two units with the same read column and different read biases still give the values (`17` and `21` of `29`), and for `d_model = 1`, which the theorem excludes, the two values with biases were found in the four cases computed. This is a computation, not a proof.
4. **S Theorem B.1 (i), "let the block have width at least `d_model`":** in the computations with biases the value of the residual network, `P − d² − 2d`, also holds for narrower blocks (`d = 2`, 1 unit: `11` of `19`; `d = 3`, 1 unit: `22` of `37`; `d = 3`, 2 units: `30` of `45`), while the value of the skipless network needs the width (`d = 3`, `d_in = 4`, 1 unit: `11` against `13`). A reason, by an argument of the reader checked by nobody else: with the skip, `D_θ M η = 0` alone gives `η_E = EX` and `η_D = −XD` from the ranks of `E` and `D`, and then `D_θ C η = 0` and `D_θ A η = 0` give `η_read = −X W_read` and `η_write = W_write X` without the ranks of `W_read` and `W_write`. The Lean statements ask the width, as the theorem does.
5. **S Appendix E, "resolving it takes far more than the minimum of about `P/d_out` inputs":** when `d_out > d_model` the minimum itself is larger. Outside the columns of `D` and `b_D`, the `d_out` rows of the Jacobian at one input span at most `d_model` dimensions, so `n` inputs give a rank of at most `n d_model + d_out (d_model + 1)`. For the row "tanh, biases, identity" of Table 6 (`d_model = 4`, `d_out = 6`, rank `254`) this needs at least 56 inputs, against `P/d_out ≈ 48`; with 55 inputs the exact rank was `230`.
6. **D Lemma D.13** is now formalized for every admissible choice of `μ`. The remark of the thirtieth report stands: the choice "`μ_1², μ_2², …` are" independent over `ℚ` is right for `d_model ≥ 2` only (for `d_model = 1` and `μ_1² = 2` the matrices `[1]` and `[2]` are dependent); the proof says "which exist because `d_model ≥ 2`", the sentence that chooses the `μ` does not.
7. **Not formalized with biases** at the commit read: Theorem B.1 (i) for ReLU, ReLU², ReGLU, SwiGLU, GeGLU and attention blocks; the `s` in the count of Lemma A.8 and the dimension of the group as such; the third value of Lemma A.27 ("MLP blocks with biases, no normalization").

## Corrections for `STATEMENTS.md`

1. The paragraph "Not yet compared by such a reader": `Network/Biases.lean`, `Symmetry/BiasesSymmetries.lean`, `Dimension/FunctionalBiases.lean`, `Symmetry/BiasesFlat.lean`, `OneBlock/MlpBiases.lean`, `Symmetry/BiasesRescale.lean` and the seven statements for every admissible `μ` at the end of `Depth/ThetaDagger.lean` (46 theorems and the definitions) were compared by the thirty-first audit (report `lean-statement-audit-thirtyfirst-2026-11-25.md`): nothing false, vacuous or drifted; the statements at generic parameters are for every Haar measure on the pairs of weights and biases; the frame is the paper's network with biases, and `P` with biases is the paper's (Table 6: `286`); the two bounds are attained by the tanh networks computed, the two rows of Table 6 included; the seven statements together are Lemma D.13 for every admissible `μ`.
2. Row of `OneBlock/MlpBiases.lean`: "named for tanh and GELU" holds for the statements on the gain `d²` only (`ae_funDimB_tanh_oneBlock_residual_eq_add`, `ae_funDimB_gelu_oneBlock_residual_eq_add`); the two values are stated for every activation under `UnitsRigid` with `HasDerivAt σ (σ' z) z`, and hold for tanh and GELU by `tanh_unitsRigid`, `gelu_unitsRigid`. One may add: the conditions are on the weights alone and the statements at one parameter hold at every bias; `d_in ≥ d` and `d_out ≥ d` are needed for both values and `d_hidden ≥ d` for the skipless one (computed).
3. Row of `Symmetry/BiasesFlat.lean`: one may add that the injectivity statements ask fewer rank conditions than Lemma B.2 lists, that each is needed (exact examples; the bounds fail without them: ranks `5` and `6` against `2`), and that `cobDirB`, `translateDir`, `translateAtDir` are the directions of Lemma B.2's bias clause for one block.
4. Row of `Symmetry/BiasesSymmetries.lean`: one may add that `evalB_cob` also covers a normalization (through its hypothesis on `χ`) and any stream matrices, that the file has no corollaries for `M = 0` and `M = 1`, and that the translations need `χ = id` (they change the function under RMSNorm).
5. Row of `Network/Biases.lean`: one may add what the frame gives for gated blocks (a gate bias and a value bias per unit) and for attention blocks (`b_Q`, `b_K`, `b_V` per head, one `b_O`), and that with a normalization the read bias is added after `χ` (the paper has no network with biases under normalization).
6. Row of `Depth/ThetaDagger.lean`: no correction. The sentence of the paragraph on the thirtieth reader ("weaker than the paper in the choice of `μ` (existence), which the statements for every admissible `μ` below now answer") is confirmed: the seven statements together are the lemma for every admissible `μ`.
7. Rows of `Dimension/FunctionalBiases.lean` and `Symmetry/BiasesRescale.lean`: no correction.

## What could not be checked

- The proofs were not read. The library was not built by the reader; single files were compiled against the existing build (`Check2.lean`, `Check8.lean`, `Axioms31.lean`).
- A rank computed on a batch is a lower bound for a functional dimension. Inside the hypotheses the ranks equal the values that Lean proves. Outside the hypotheses (`d = 1`; narrow blocks; `d_in < d`; `d_out < d`; collinear read columns) the numbers are computations on two batches and prove nothing about every case; where a rank is above a bound it refutes the bound, and where it is below a formula it does not prove that the functional dimension is below.
- The truth of `ae_paramsB_of_forall_ae` and of the nine statements of `Dimension/FunctionalBiases.lean` was judged by an argument of the reader and by the fact that they are proved in Lean with the standard axioms; the argument in item 4 of the list for the authors was checked by nobody else.
- `UnitsRigid`, `OneBlockGeneric`, `ae_oneBlockGeneric`, `tanh_unitsRigid`, `gelu_unitsRigid`, `cobDir`, `Params.cob`, `Params.rescaleMlp`, `Params.rescale`, `Params.rescaleGate`, `GoodForConesGated`, `GoodForConesMlp`, `frozenGated`, `frozenMlp` and the definitions of `θ†` were compared by earlier audits and not again; here their text was read for the use that the new statements make of them.
- The converse direction for the independence written out (the hypothesis implies Mathlib's `LinearIndependent ℚ` of the family) was not compiled; it is immediate by extending a coefficient family by `0` on the image of `c ℓ`.
- Nothing could be compared for networks with biases under a normalization: the paper has none.
- The files written after this audit began (`Dimension/FunctionalBiasesKinks.lean`, `Symmetry/BiasesFlatKinks.lean`, `Symmetry/InsideBlocksBiases.lean`, `Symmetry/BiasesRescaleCount.lean`, `OneBlock/GatedBiases.lean`, `Dimension/FunctionalBiasesOn.lean`, `OneBlock/RescaleBiases.lean`, `OneBlock/ReGLUBiases.lean`) were not read.
