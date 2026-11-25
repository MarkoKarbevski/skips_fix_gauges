STATUS: complete

# Twenty-seventh audit of Lean statements against the papers (25 November 2026)

Subject: S Lemma A.18 and D Lemma B.1 for the group and with the readout; S Theorem B.1 (iii), `ε > 0`, the upper triangular skip for blocks of any width. Nine files of `lean/SkipsLean/`: 2 definitions and 40 public theorems. S is the skips paper, D the dimension paper (`<scratchpad>/skips.txt`, `<scratchpad>/dim.txt`).

**Result.** Nothing false, nothing vacuous, nothing drifted. Every one of the 22 `ae_` statements is for almost every parameter and every Haar measure. The exact counterexamples asked for in the brief exist: each hypothesis that the Lean statements add to the paper's words is needed. Five corrections for the index, none of them about a wrong statement. Three places where the paper's proof uses a step that it does not write (list for the authors).

## Commits read; `sorry`

- Commits of `/home/claude/lp` (branch `lean-plus`): `048a13a` (with uncommitted changes in three files) when the reading began, `8b86096` when the nine files were copied to `/home/claude/audit27/src/`, `37c1a8a` at the end.
- Between `048a13a` and `8b86096` the nine files changed only by: `sorry` replaced by proofs, private helpers added, lines `omit [...] in` added before theorems (they remove unused instance arguments). Checked with `git diff`. No statement changed. After `8b86096` only two header comments changed (`LocallyFreeEmbedding.lean`, `LocallyFreeReadout.lean`: "Not stated: `ε = 0` together with rescalings" became a pointer to a new file).
- Files with `sorry` at `048a13a`: `Dimension/UpperBoundReadoutInside.lean` (4), `Basic/EigenvectorsGeneralPosition.lean` (1), `Symmetry/LocallyFreeReadoutGeneric.lean` (8). At `8b86096` and later: none of the nine.
- Compiled by the reader (`Ax27.lean`, against the existing build, nothing written there): each of the 40 theorems depends on `propext`, `Classical.choice`, `Quot.sound` only; no `sorryAx`.
- Written after this audit began and **not read here**: `Symmetry/LocallyFreeRMSZero.lean` (7 `sorry` at `37c1a8a`), `Symmetry/LocallyFreeRMSZeroGeneric.lean`, `Basic/RMSNormDeviation.lean`.

How each check was done is said in the check: *reading*, *compiled* (a copy in `/home/claude/audit27/`, with `lake env lean`), or *computed* (Python, `python3 -I`; every run took under one minute).

## Part 1: checks

### 1. Generic means almost every parameter, for every Haar measure: YES

*Reading.* The 22 statements (8 in `LearnedSkipTriangularNarrow.lean`, 6 in `LocallyFreeGeneric.lean`, 8 in `LocallyFreeReadoutGeneric.lean`) all have the form

```lean
(μ : Measure (Params A dIn dOut)) [μ.IsAddHaarMeasure] … : ∀ᵐ θ ∂μ, …
```

and the eight of the triangular skip have `μ : Measure (Params … × (Fin 1 → upperTriangular d))`. None says "there is a parameter" or names an open set. The index types `T`, `d`, `dIn`, `dOut`, `hid ℓ`, `H ℓ`, `dh ℓ` have `Fintype` (the `variable` lines), and `A.r ℓ`, `A.w ℓ` have it as fields of `Arch`.

*Compiled* (`Chk27.lean`, 8 instances at `Measure.addHaar` with numbers, all with the three standard axioms):

- `ae_cob_rescale_rescaleGate_eq_self_of_dOut`: two ReGLU blocks, `d = 2`, `d_in = 1`, `d_out = 3`, widths 2, 2, `k = 1`;
- `ae_cob_rescaleMlp_eq_self_of_dOut`: three ReLU² blocks under pre-RMSNorm with `ε = 1`, `d = 3`, `d_in = 1`, width 4, `k = 2`;
- `ae_cob_headsQK_headsVO_eq_self_of_dIn`: two causal attention blocks, two tokens, `d = 3`, two heads of width 2;
- `ae_cob_rmsNorm_zero_eq_self_of_dOut`: two GELU blocks, `ε = 0`, `d = 2`, `d_in = 1`;
- `ae_read_cols_generalPosition` for the attention network (a read with 12 columns, `d = 3`);
- three of the triangular skip (check 8).

### 2. The actions: SAME as the papers; the three maps commute

*Reading.*

| Lean | Paper |
|---|---|
| `Params.cob θ G K`: `E := θ.E * G 0`, `read ℓ := (K ℓ.castSucc)⁻¹ * θ.read ℓ`, `write ℓ := θ.write ℓ * G ℓ.succ`, `D := (K (Fin.last L))⁻¹ * θ.D` | S Definition 3.1 and the proof of A.18: `E ↦ E G_0`, `W_write^ℓ ↦ W_write^ℓ G_ℓ`, the read of block `ℓ` multiplied by `G_{ℓ−1}⁻¹` on the left, `D ↦ G_L⁻¹ D`. Lean's block `ℓ : Fin L` is the paper's block `ℓ + 1`: it reads `h_ℓ` and writes `h_{ℓ+1}`. Same. |
| `θ.rescaleMlp k c`: `read ℓ a i ↦ c ℓ i * read`, `write ℓ i a ↦ (c ℓ i ^ k)⁻¹ * write` | D Appendix B: ReLU `(c_i, a_i) ↦ (λ c_i, a_i/λ)`, ReLU² `(λ c_i, a_i/λ²)`, `λ > 0`. Same with `k = 1`, `2`: the read column is multiplied, the write row divided by `λ^k`. |
| `θ.rescale c`: value column `(c ℓ i)⁻¹ *`, write row `c ℓ i *` | D: SwiGLU, GeGLU, ReGLU `(e_i, a_i) ↦ (e_i/λ, λ a_i)`, `λ ≠ 0`. Same. |
| `θ.rescaleGate k c`: gate column `c ℓ i *`, write row `(c ℓ i ^ k)⁻¹ *`, value columns stay | D: "ReGLU, in addition: `(c_i, a_i) ↦ (λ c_i, a_i/λ)`, `λ > 0`". Same with `k = 1`. |
| `θ.headsQK K`, `θ.headsVO K'` | D: `(W_Q, W_K) ↦ (W_Q K, W_K K^{−⊤})`, `(W_V, W_O) ↦ (W_V K', K'⁻¹ W_O)`. Same. |
| `θ.cob G Q` with `(G ℓ) = c ℓ • (Q ℓ)` | S Theorem A.5 (iii) and proof of Proposition A.1: for `ε = 0`, `G_ℓ = c_ℓ Q_ℓ` on the writes, `Q_ℓ^⊤` on the reads and the readout. Same; `eval_cob_rmsNorm_zero` (`Symmetry/Normalized.lean`) states that this map preserves the function for `c_ℓ > 0`, `Q_ℓ` orthogonal. |

The signs the papers allow: positive for the hidden units of ReLU and ReLU² blocks and for the gates of ReGLU; any nonzero number for the values of a gated block (D Appendix B: `λ ≠ 0`; the proof of S A.18 takes them positive, "close to the identity"). The invariance statements ask the same: `eval_rescaleMlp_params` and `eval_rescaleGate_params` ask `0 < c ℓ i`, `eval_rescale_params` asks `c ℓ i ≠ 0`. The definitions themselves take every real `c` (`0⁻¹ = 0` in Lean).

*Compiled* (`Chk27b.lean`): the three maps commute, so the order in `((θ.cob G G).rescale c').rescaleGate k c` does not matter:

```lean
(θ.cob G K).rescale c = (θ.rescale c).cob G K
(θ.cob G K).rescaleGate k c = (θ.rescaleGate k c).cob G K
(θ.rescale c').rescaleGate k c = (θ.rescaleGate k c).rescale c'
(θ.cob G K).rescaleMlp k c = (θ.rescaleMlp k c).cob G K
```

(for every `G`, `K`, `c`, `c'`, `k`; the changes of basis multiply reads on the left and writes on the right, the rescalings on the other side).

### 3. The conclusion against the paper's definition: LEAN STRONGER, and it gives the paper's property

*Reading, with the special cases compiled in `Chk27b.lean`.* The paper: the symmetries "act locally freely at `θ` if no continuous family of them, other than the identity, fixes `θ`"; the proof ends "By induction only the identity fixes `θ`", for changes of basis and rescalings close to the identity. Lean, for example:

```lean
theorem cob_rescaleMlp_eq_self_of_rank_E … (h : (θ.cob G G).rescaleMlp k c = θ) :
    G = 1 ∧ ∀ ℓ i, c ℓ i = 1
```

says that **whatever** change of basis and rescaling fixes `θ` is the identity: all of `GL(d)` at every hidden state, not only matrices near `1`. This is more than the proof's sentence and gives the paper's property with permutations and sign flips included: a continuous family of symmetries keeps its permutation and its signs (they are finitely many), so two members of the family differ by a change of basis and a rescaling that fixes `θ`, which is the identity by the Lean statement; the family is constant. The sentence "Permutations and sign flips are isolated" itself is not in Lean (the index says so).

- `cob_eq_self_of_rank_E`: `θ.cob G K = θ → G = 1`, with `K` free. With `K = G` it is the lemma for tanh and GELU blocks without normalization; with `K = G` orthogonal the lemma for `ε > 0`; with `G` constant the lemma for a residual network (compiled: `θ.cob (fun _ => G₀) (fun _ => G₀) = θ → G₀ = 1`, also with `rescaleMlp`). With `K = G` the conclusion `G = 1` is all of the conclusion.
- `cob_eq_self_of_rank_D`: `θ.cob G K = θ → K = 1`. With `K = G` it gives `G = 1` (compiled). For `ε = 0` it gives `Q = 1` only; the scales come in `cob_rmsNorm_zero_eq_self_of_rank_D`.
- With the embedding Lean asks nothing of the numbers `c` (the paper: positive). With the readout it asks positive `c` for hidden units and gates, as the paper, and nothing of the value scalings.

### 4. The hypotheses at one parameter: what the paper's proof uses, and each is needed

*Reading* for the comparison, *computed* for the counterexamples (`c4_group.py`, exact rational arithmetic, the maps written as in the Lean definitions; 20 cases; in each the hypotheses that are kept hold, the maps fix `θ` exactly and are not the identity).

With the embedding. Lean: `hE : θ.E.rank = Fintype.card d`, `hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d`, and the rescaled read columns not zero (`hcol`; `hv` for value columns; `hg` for gate columns). The paper: "`E` has rank `d_model`", "no column of a generic `W_read^ℓ` vanishes", "`W_write^ℓ` has rank `d_model`". Same.

| Dropped | Exact counterexample (`d = 2`, one block) |
|---|---|
| `E` of rank `d` | `E = [[1,0],[0,0]]`, read with a zero second row, `G_0 = diag(1,2)` |
| write of rank `d` | write `[[1,0],[1,0]]`, `D` with a zero second row, `G_1 = diag(1,2)` |
| a read column not zero (ReLU, `k = 1`, `2`) | three units; unit 3 has a zero read column **and** a zero write row; `c_3 = 5`. With a nonzero write row at that unit the maps do not fix `θ` (computed), so the hypothesis could be "the column or the row is not zero". |
| a value column, a gate column not zero (gated, ReGLU) | the same, at the value or gate column |
| `c_ℓ > 0` in `cob_rmsNorm_zero_eq_self_of_rank_E` | `c = −1`, `Q = −1` (so `G = cQ = 1`), at reads and `D` equal to zero. With a nonzero read the maps do not fix `θ`. |

With the readout. Lean: `hD : θ.D.rank = Fintype.card d`, `hr : ∀ ℓ, (θ.read ℓ).rank = Fintype.card d`, `ha : ∀ ℓ i, (fun a => θ.write ℓ i a) ≠ 0`; `hk : k ≠ 0` and `hc : ∀ ℓ i, 0 < c ℓ i` for ReLU and ReLU²; `hc` for the gates and

```lean
(hgp : ∀ ℓ (S : Finset (hid ℓ ⊕ hid ℓ)), S.card ≤ Fintype.card d →
  LinearIndependent ℝ fun j : S => (θ.read ℓ)ᵀ j)
(hcard : ∀ ℓ, Fintype.card d < Fintype.card (hid ℓ ⊕ hid ℓ))
```

for ReGLU; `hE : θ.E ≠ 0`, `hw : ∀ ℓ, θ.write ℓ ≠ 0` for `ε = 0`. The paper: "rescalings act freely on the rows of a generic write, except that for ReGLU a row fixes only the product `cc′` of the gate and value scales of its unit; each read, of rank `d_model` and with generic columns, then forces `G_{ℓ−1} = I` and the remaining scales to be 1". Same: a write row not zero; the row gives `c^k = 1` (ReLU), `c = 1` (values), `c' = c^k` (ReGLU; the paper's "product" is of the factors on the two read columns, `c` and `1/c'`); the read of rank `d` gives the change of basis. "With generic columns" is made exact as general position for ReGLU.

| Dropped | Exact counterexample (`d = 2`, one block unless said) |
|---|---|
| `c > 0`, `k = 2` | read `1`, `G_0 = diag(1,−1)`, `c = (1,−1)`, `E = (1,0)`. With `k = 1` the same maps do not fix `θ`. (`c = −1` is not a symmetry of ReLU²; the Lean hypothesis is the paper's "positive rescalings".) |
| `k ≠ 0` | read `1`, `G_0 = diag(2,1)`, `c = (2,1)`, `E = (0,1)` |
| a write row not zero (ReLU, `k = 1`, `2`) | the same with the first write row zero |
| a write row not zero (gated) | read `[e_2 e_2 | e_1 e_2]`, first write row zero, `c_1 = 2`, `G_0 = diag(1/2,1)` |
| read of rank `d`; `D` of rank `d` | read with a zero row; `D` with a zero row and a write with a zero column |
| general position (ReGLU, `k = 1`): **the example of the header, recomputed** | gate columns `e_1, e_2`, value columns `e_2, e_1`, `E = 0`, `D` and the write invertible: the read has rank 2, no write row is zero, and `G_0 = diag(t, 1/t)`, `c = c' = (t, 1/t)` fix `θ` for every `t > 0` (checked at `t = 2, 1/3, 7/5`): a continuous family. |
| general position, every `d ≥ 2`, every `k ≥ 1` | width `d`; units 1 and 2 with gate `e_1` and value `e_2`, unit `j ≥ 3` with gate and value `e_j`; the read has rank `d`; `G_0 = diag(t, t^{−k}, 1, …)`, `c = (t, t, 1, …)`, `c' = c^k` fix `θ` (checked for `d = 2..5`, `k = 1, 2, 3`, `t = 3`). So for every `d ≥ 2` a condition beyond rank `d` is needed. For `d = 1` general position is "no column is zero". |
| `c > 0` (ReGLU) | `c = c' = −1`, `G_0 = −1`, `E = 0`, a read in general position |
| `E ≠ 0`; a write not zero (`ε = 0`) | `E = 0`: `c_0 = 3`, `Q = 1` fixes `θ`; a zero write: `c_1 = 3` fixes `θ` |

General position at generic parameters: *reading and compiled.* `ae_read_cols_generalPosition` (proved; instance compiled) gives "any `d` columns independent" for reads with at least `d` columns, and "more than `d` columns" is `2 d_hidden > d`, which holds for `d_hidden ≥ d ≥ 1` (derived inside the proof of `ae_cob_rescale_rescaleGate_eq_self_of_dOut`). So the condition is what holds at generic parameters for width at least `d ≥ 1`.

### 5. `eq_smul_one_of_eigenvectors_generalPosition`: true as stated

```lean
theorem eq_smul_one_of_eigenvectors_generalPosition {d q : Type*} [Fintype d] [DecidableEq d]
    [Fintype q] (v : q → d → ℝ)
    (hgp : ∀ S : Finset q, S.card ≤ Fintype.card d → LinearIndependent ℝ fun j : S => v j)
    (hq : Fintype.card d < Fintype.card q) (M : Matrix d d ℝ)
    (hM : ∀ j, ∃ μ : ℝ, M *ᵥ v j = μ • v j) : ∃ μ : ℝ, M = μ • (1 : Matrix d d ℝ)
```

*Reading:* `d` of the vectors are a basis of eigenvectors; one more vector has all its coordinates in that basis nonzero (else it and `d − 1` of them would be dependent), so all eigenvalues are equal. For `d = 0` the conclusion holds for the empty matrix; for `d = 1` every matrix is a multiple of `1`. *Compiled:* the proof in the repository has the three standard axioms. *Computed:* "more than `d`" is needed for `d ≥ 2`: `e_1, e_2` are eigenvectors of `diag(1, 2)`; and independence of any `d` is needed: `e_1, 2e_1, e_2` are eigenvectors of `diag(1, 2)`. Among the 625 integer `2 × 2` matrices with entries in `−2..2`, the 5 that have `e_1, e_2, e_1 + e_2` as eigenvectors are the multiples of `1`.

### 6. The infinitesimal forms: the same maps as their twins, mirrored hypotheses

*Reading.* The four statements of `Dimension/UpperBoundReadoutInside.lean` are `Function.Injective` of the same maps as their twins:

```lean
fun p => cobDir θ p.1 + rescaleDir θ p.2                              -- gated
fun p => cobDir θ p.1 + rescaleDirMlp k θ p.2                         -- ReLU, ReLU²
fun p => cobDir θ p.1 + rescaleDir θ p.2.1 + rescaleDirGate k θ p.2.2 -- ReGLU
fun p => cobDir θ p.1 + scaleDir θ p.2                                -- ε = 0
```

The directions are the derivatives of the maps of check 2 (`cobDir`: `E X_0`, `−X_ℓ W_read`, `W_write X_{ℓ+1}`, `−X_L D`; `rescaleDirMlp k`: read column times `α`, write row times `−kα`; `rescaleDir`: value column times `−α`, write row times `α`; `rescaleDirGate k`: gate column times `β`, write row times `−kβ`; `scaleDir`: `β_0 E`, `β_{ℓ+1} W_write`). The hypotheses are those of check 4 in place of "`E` and the writes of rank `d`, the rescaled read columns not zero". The twin for `ε = 0` is stated for antisymmetric `Y`, `Y'`; the new one is injective on all matrices.

*Computed* (`c6_rank.py`, the reader's own, exact ranks over the rationals; the hypotheses are checked exactly at every draw):

- 36 draws of random integer parameters with `E = 0` (for `ε = 0`: `E` of rank 1) where the hypotheses hold, `d = 1..4`, one to three blocks, gated, ReLU (`k = 1`), ReLU² (`k = 2`), ReGLU (`k = 1`, `2`), `ε = 0`: the rank is the number of unknowns in every case.
- The twins at 12 draws with `D = 0`, `E` and the writes of rank `d`: injective in every case. With `E = 0` and `D = 0` the ReLU and ReGLU maps have a kernel of dimension 1 (the gated one has none at width `d`).
- One hypothesis violated, at designed parameters (`d = 2`): `k = 0`: kernel 2; a zero write row (ReLU; gated): kernel 1; read of rank 1: kernel 2; `D` of rank 1: kernel 1. A zero write row with three units and a read in general position: still injective (the hypothesis is sufficient, and needed only at special reads).
- **The header's example:** at gate columns `e_1, e_2`, value columns `e_2, e_1`, `E = 0`, the direction of `X_0 = diag(1, −1)`, `α = β = (1, −1)`, `X_1 = 0` is exactly `0` for `k = 1`, and the map has rank 11 of 12. For `k = 2` the map is injective at these parameters: the example is for degree 1 (ReGLU). An example for every `k ≥ 1` and every `d ≥ 2`: the read of check 4 (gates `e_1, e_1, e_3, …`, values `e_2, e_2, e_3, …`): kernel 1 for `d = 2, 3, 4`, `k = 1, 2`.
- `ε = 0`, all matrices `Y`: with the readout hypotheses the rank is 30 of 30; with `E = 0` or with a zero write the kernel has dimension 1. Under the twin's hypotheses alone (reads and `D` zero) the kernel on all matrices has dimension 3 (`Y_ℓ = −β_ℓ 1`), and on antisymmetric `Y` the map is injective. So the twin needs "antisymmetric" and the new statement rightly asks nothing of `Y`: the reads and `D` determine `Y`, and `E ≠ 0`, `W ≠ 0` then determine `β`.

A copy of the coordinator's script gives the same ranks (17/17, 34/34, 47/47, 36/36 for gated, ReLU, ReLU²; 22, 41, 58, 40 for ReGLU; 11 of 12 at the example).

### 7. At generic parameters: the widths are the papers'; the extra instances are needed

*Reading; two points compiled.*

- With the embedding: `hdIn : Fintype.card d ≤ Fintype.card dIn`, `hw : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)` (for a general `Arch`: `(A.w ℓ)`), attention `hdh : card (dh ℓ) ≤ card d`, `hH : card d ≤ card (H ℓ) * card (dh ℓ)`. This is D Lemma B.1 ("`d_in ≥ d_model`", "at least `d_model` hidden units", "`d_h ≤ d_model` and total width `H d_h ≥ d_model`"), with widths that may differ from block to block.
- With the readout: `hdOut : card d ≤ card dOut` and width at least `d` (for a general `Arch`: reads with at least `d` columns). This is the second sentence of S A.18 ("the readout has rank `d_model`" holds at generic parameters when `d_out ≥ d`).
- `[Nonempty d]` stands where rescalings or the scales `c_ℓ` are in the conclusion, and is needed there. *Compiled* (`nonempty_d_needed27`): for `d = Fin 0` and one ReLU block with one hidden unit, every `c` fixes every `θ`, so "`c = 1`" fails. It does not stand in `ae_cob_eq_self_of_dIn`, `ae_cob_eq_self_of_dOut`, `ae_rank_D_read`, `ae_read_cols_generalPosition`, `ae_cob_headsQK_headsVO_eq_self_of_dIn`, which hold for `d` empty.
- `ae_cob_rmsNorm_zero_eq_self_of_dOut`: `[Nonempty dIn]` is needed (with no input coordinate `E` has no entry, and `c_0` is free: the case `E = 0` of check 4), and so is `hw : ∀ ℓ, Nonempty (A.w ℓ)` for a general `Arch` (a write with no row leaves `c_{ℓ+1}` free). For the architectures of the library (`Arch.mlp`, `Arch.gated`, `Arch.attention`) `hw` follows from `hr` and `[Nonempty d]`, because a read with a column has a hidden unit or a head.
- `ae_rank_D_read`, `ae_write_row_ne_zero`, `ae_read_cols_generalPosition` are stated for every `A : Arch T d L`; the parameters are free matrices of the shapes of `A`, so they hold for every architecture of the library. They are proved, and one is instantiated for the attention network (check 1).
- In `ae_cob_rmsNorm_zero_eq_self_of_dIn` the hypotheses `0 < c ℓ` and `Q ℓ` orthogonal are kept (needed at one parameter only when the reads and `D` vanish, check 4); in `…_of_dOut` nothing is asked of `c` and `Q` beyond `G = c • Q`.

### 8. The triangular skip for blocks of any width: SAME as Theorem B.1 (iii); "at least one hidden unit" is needed

```lean
theorem ae_funDimLearnedTri_tanh_rmsNorm_of_nonempty (hε : 0 < ε) [Nonempty (hid 0)] (μ : …)
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : card d ≤ card dIn)
    (hdOut : card d ≤ card dOut) :
    ∀ᵐ p ∂μ, funDimLearnedTri (Arch.mlp Real.tanh (rmsNorm ε) hid) p + card d * (card d - 1) / 2
      = Module.finrank ℝ (Params …) + card d * (card d + 1) / 2
```

and, for the gated kinds, `+ (card d * (card d - 1) / 2 + Fintype.card (hid 0))` on the left; the second statement of each kind is `funDimLearnedTri … p = funDim … 1 p.1 + card d * (card d + 1) / 2`.

*Reading.* The theorem: "with a learned skip `A`, full or upper triangular. For generic parameters and `ε > 0`, its functional dimension exceeds that of the residual network of part (ii) by exactly `d_model (d_model + 1)/2`, and it satisfies the equality condition"; part (ii) gives `P − d(d−1)/2 − s` for the residual network with no condition on the width. The Lean value `P + d(d+1)/2 − d(d−1)/2 − s` is the sum, and it is the equality condition for the network with `P + d(d+1)/2` parameters and symmetries of dimension `d(d−1)/2 + s` (Step 5: for an upper triangular `A` the rotations "have dimension `d_model (d_model − 1)/2`"). `d ≥ 2`, `d_in, d_out ≥ d` and at least one token (`[Nonempty T]`) are the theorem's. The four difference statements compare with the residual network **at the same weights** `p.1`.

*Compiled.* (a) The twin for width at least `d`: `ae_funDimLearnedTri_tanh_rmsNorm` and `ae_funDimLearnedTri_tanh_rmsNorm_of_nonempty` have literally the same conclusion (`rfl` between the two under both hypotheses), and the statement of the twin follows from the new one, since width at least `d ≥ 2` gives a hidden unit. (b) With numbers at `Measure.addHaar`: tanh, `d = d_in = d_out = 3`, one hidden unit: `funDimLearnedTri = 27`; SwiGLU, two hidden units: `= 37`, and `= funDim … 1 p.1 + 6`.

*Computed* (`c8_tri.py`: one token, `ε = 1/2`, the chain rule written out, 80 digits, rank from the eigenvalues of `JᵀJ`; batches of 20, 40 and 60 inputs give the same rank; the eigenvalue after the rank is below `10⁻⁷⁸`, the last one kept above `10⁻¹²`):

| block | `d`, `d_in`, `d_out` | hidden | parameters | rank | stated | residual, same weights | difference |
|---|---|---|---|---|---|---|---|
| tanh | 3, 3, 3 | 1 | 30 | 27 (two seeds) | 27 | 21 | 6 |
| tanh | 3, 3, 3 | 2 | 36 | 33 (two seeds) | 33 | 27 | 6 |
| SwiGLU | 3, 3, 3 | 1 | 33 | 29 (two seeds) | 29 | 23 | 6 |
| SwiGLU | 3, 3, 3 | 2 | 42 | 37 (two seeds) | 37 | 31 | 6 |
| tanh | 3, 4, 3 | 1 | 33 | 30 | 30 | 24 | 6 |
| SwiGLU | 2, 2, 3 | 1 | 19 | 17 | 17 | 14 | 3 |
| tanh | 3, 3, 3 | 3 | 42 | 39 | 39 | 33 | 6 |
| SwiGLU | 3, 3, 3 | 4 | 60 | 53 | 53 | 47 | 6 |

A rank on a batch is a lower bound; the stated value is also an upper bound (the rotations and rescalings are in the kernel), so the two agree.

"At least one hidden unit" is needed: with **no** hidden unit the rank is 15 of 24 parameters for `d = 3` (the formula would give 21) and 7 of 11 for `d = 2` (formula: 10), and the difference to the residual network is 0, not `d(d+1)/2`. The network is then `x ↦ N_ε(x E A) D`.

### 9. The index rows: true of the statements, with five corrections

*Reading and a script.* Each of the 42 public names of the nine files is in the row of its file, and each of the 40 theorems has its line in `checks/Axioms.lean` (lines 1837 to 1876 at `8b86096`); the two definitions need none. The sentences of the rows agree with the statements, except for the points listed under "Corrections for `STATEMENTS.md`".

## Part 2: the statements, file by file

| File | Name | Paper | Verdict |
|---|---|---|---|
| `Dimension/RescaleActionHomogeneous.lean` | `Params.rescaleMlp` | D App. B, ReLU and ReLU² lines | SAME (degree `k`) |
| | `Params.rescaleGate` | D App. B, "ReGLU, in addition" | SAME (degree `k`) |
| | `eval_rescaleMlp_params`, `eval_rescaleGate_params` | the rescalings preserve the function, `λ > 0` | LEAN STRONGER (any positively homogeneous degree, any `χ`, any stream matrices) |
| `Symmetry/LocallyFreeEmbedding.lean` | `cob_eq_self_of_rank_E` | S A.18 first sentence and D B.1, proof, the changes of basis | LEAN STRONGER |
| | `cob_rescaleMlp_eq_self_of_rank_E` | the same, ReLU and ReLU² | LEAN STRONGER |
| | `cob_rescale_eq_self_of_rank_E` | the same, gated | LEAN STRONGER |
| | `cob_rescale_rescaleGate_eq_self_of_rank_E` | the same, ReGLU | LEAN STRONGER |
| | `cob_rmsNorm_zero_eq_self_of_rank_E` | "With RMSNorm the changes of basis lie in `CO(d_model)`", `ε = 0` | SAME, PART of the lemma (no symmetries inside blocks) |
| `Symmetry/LocallyFreeAttention.lean` | `cob_headsQK_headsVO_eq_self_of_rank_E` | S A.18 third sentence, D B.1 | LEAN STRONGER; PART (attention blocks only) |
| `Symmetry/LocallyFreeReadout.lean` | `cob_eq_self_of_rank_D` | S A.18 second sentence, the changes of basis | LEAN STRONGER |
| | `cob_rescaleMlp_eq_self_of_rank_D` | the same, ReLU and ReLU² | SAME |
| | `cob_rescale_eq_self_of_rank_D` | the same, gated | LEAN STRONGER (any `c`) |
| | `cob_rescale_rescaleGate_eq_self_of_rank_D` | the same, ReGLU | SAME ("generic columns" made exact) |
| | `cob_rmsNorm_zero_eq_self_of_rank_D` | the same, `ε = 0` | SAME, PART of the lemma; with `E ≠ 0` and nonzero writes, which the paper does not write |
| `Dimension/UpperBoundReadoutInside.lean` | the four `…_injective_of_rank_D` | S A.18 second sentence, as used by A.17 (ii) ("independent directions") | SAME (infinitesimal form) |
| `Basic/EigenvectorsGeneralPosition.lean` | `eq_smul_one_of_eigenvectors_generalPosition` | a step of the proof of A.18 that the paper does not write | true; SAME as the use made of it |
| `Symmetry/LocallyFreeGeneric.lean` | six `ae_…_of_dIn` | D B.1; S A.18 first and third sentence | SAME (LEAN STRONGER in the conclusion); PART |
| `Symmetry/LocallyFreeReadoutGeneric.lean` | `ae_rank_D_read`, `ae_write_row_ne_zero`, `ae_read_cols_generalPosition` | "generic" in the proof | SAME |
| | five `ae_…_of_dOut` | S A.18 second sentence | SAME (LEAN STRONGER in the conclusion); PART |
| `OneBlock/LearnedSkipTriangularNarrow.lean` | four `…_rmsNorm_of_nonempty` | S B.1 (iii), `ε > 0`, upper triangular `A`: the value, which is the equality condition | SAME |
| | four `…_eq_residual_add_of_nonempty` | "exceeds that of the residual network of part (ii) by exactly `d_model (d_model + 1)/2`" | SAME (at the same weights) |

Notes.

- LEAN STRONGER in the first rows means: the statement is at every parameter with the rank conditions, not only at generic ones; it is for the whole group (every invertible matrix, every number), not only near the identity; and `cob_eq_self_of_rank_E` is for any kind of block.
- PART: the group statements cover networks whose blocks are all MLP blocks of one kind, or all attention blocks. A network with both attention blocks and MLP blocks ("networks with attention blocks" in S A.18, "or attention blocks" in D B.1) has the changes of basis alone (`cob_eq_self_of_rank_E` is for any `Arch`), not the symmetries inside both kinds of block together. `ε = 0` with the symmetries inside blocks is not in the nine files (it is in the new file, not read here). The third sentence of A.18 has no form with the readout, in the paper or in Lean.
- The paper's definition speaks of continuous families; Theorem A.17 (ii) uses the number of independent directions. Lean has the two forms side by side (the group here, the directions in `cobDir_…_injective` and `…_of_rank_D`), each proved from the same rank conditions; no Lean statement passes from one to the other.

## What the authors of the papers should know

Nothing false, vacuous, drifted or misdescribed was found in the nine files.

Places where the paper's proof uses a condition or a step that it does not write:

1. **S Lemma A.18, second sentence, ReGLU: "with generic columns" must mean general position.** In the first half of the proof "generic" is used as "no column vanishes". In the mirror induction for ReGLU that is not enough, and neither is rank `d_model`: for every `d_model ≥ 2` there is a read of rank `d_model` with all columns nonzero, a write with no zero row and a readout of rank `d_model` at which a continuous family of changes of basis and positive rescalings fixes the parameters (gate columns `e_1, e_2`, value columns `e_2, e_1`: `G_0 = diag(t, 1/t)`, both scales `(t, 1/t)`; check 4). What the step uses: the `2 d_hidden > d_model` gate and value columns are in general position (any `d_model` of them independent), every one of them is an eigenvector of `G_{ℓ−1}`, so `G_{ℓ−1}` is a multiple of `I`; the multiple and the scales are then 1 because the scales are positive. One clause in the proof would say it.
2. **S Lemma A.18, second sentence, `ε = 0`: "the argument is unchanged" hides two points.** (a) The readout and the reads see only the orthogonal part `Q_ℓ` of `G_ℓ = c_ℓ Q_ℓ`; the scale `c_ℓ` acts on the writes into `h_ℓ` alone, so it is fixed by a nonzero embedding (`c_0`; this needs `d_in ≥ 1`) and by nonzero writes, not by the mirror induction (`cob_rmsNorm_zero_eq_self_of_rank_D` asks `E ≠ 0` and nonzero writes, and both are needed: check 4). (b) With rescalings inside the blocks, a write row is multiplied by `c_ℓ / λ^k`, so the rescalings do not "act freely on the rows of a generic write" by themselves; the read is needed as well (a rescaled read column is an eigenvector of the orthogonal `Q_{ℓ−1}` with a positive eigenvalue, hence eigenvalue 1). Point (b) is the reader's own reasoning; the Lean statements for it are in a file written after this audit began and were not read.
3. **S Lemma A.18, second sentence, ReLU²:** the write row gives `λ² = 1`, and `λ = 1` follows because the rescalings are positive, as the proof says at its start; with `λ = −1` allowed the conclusion fails (check 4). No change needed; the Lean statement keeps the hypothesis for this reason.
4. **S Theorem B.1 (iii)** needs a block with at least one hidden unit: with none, the learned skip adds nothing to the functional dimension (check 8). The theorem's blocks have hidden units, so this is a remark, not a correction.
5. The first sentence of A.18 for ReLU blocks: a zero read column lets a rescaling fix the parameters only if the write row of that unit is zero too (check 4). The paper's condition is sufficient as written.

## Corrections for `STATEMENTS.md`

1. Row of `Symmetry/LocallyFreeGeneric.lean`: delete "five of the six rest on statements in work". All six are proved and have the three standard axioms (`Ax27.lean`).
2. The paragraph "Not yet compared by such a reader (they go to the twenty-seventh audit)": the nine files are now compared (this report). The files written after the audit began (`Symmetry/LocallyFreeRMSZero.lean`, `Symmetry/LocallyFreeRMSZeroGeneric.lean`, `Basic/RMSNormDeviation.lean`) are not.
3. Row of `Dimension/UpperBoundReadoutInside.lean`, and the headers of that file and of `Symmetry/LocallyFreeReadout.lean`: the example (gate columns `e_1, e_2`, value columns `e_2, e_1`, `α = β = (1, −1)`) is for degree `k = 1`; say so. For `k = 2` the map is injective at those parameters, while the statement is for every `k`. An example for every `k ≥ 1`: two units with gate column `e_1` and value column `e_2`, `X_0 = diag(1, −k)`, `β = (1, 1)`, `α = (k, k)`.
4. Row of `OneBlock/LearnedSkipTriangularNarrow.lean`: "The twins without a condition on the width" is exact for the four value statements. The four difference statements have another form than their twins: here the residual network has the same weights `θ = p.1`; in `OneBlock/LearnedSkipTriangular.lean` it is at almost every `θ'` of a second Haar measure. Add "at least one token" (`[Nonempty T]`), as in the twin's row.
5. Rows of `Symmetry/LocallyFreeGeneric.lean` and `Symmetry/LocallyFreeAttention.lean`: add "Not stated for the group: networks with both attention and MLP blocks, with the symmetries inside both". Row of `Symmetry/LocallyFreeEmbedding.lean`: the statement for `ε = 0` asks `c_ℓ > 0` and `Q_ℓ` orthogonal (the row of the readout says what its twin asks; this row does not).

## What could not be checked

- The proofs were not read. What is known of them: they compile in the existing build, and the 40 theorems have the three standard axioms. `lake build` was not run; the reader's files were compiled against the build as it stood between 00:55 and 01:06 UTC.
- The files written after the audit began (see above), among them the statements for `ε = 0` with the symmetries inside blocks.
- The sentence "Permutations and sign flips are isolated" has no Lean statement; the step from the Lean conclusion to the paper's definition with permutations and sign flips (check 3) is the reader's argument, not compiled.
- The ranks of checks 6 and 8 are at finitely many parameters (36 + 12 random draws, exact; 12 parameters at 80 digits). The counterexamples of check 4 are exact.
- Whether the hypotheses that are needed at one parameter (positive `c` for ReGLU, `c_ℓ > 0` and orthogonal `Q_ℓ` with the embedding for `ε = 0`) are also needed in the `ae_` statements was not examined: the counterexamples found are at special parameters (`E = 0`, zero reads).

Scratch work: `/home/claude/audit27/` (`Chk27.lean`, `Chk27b.lean`, `Ax27.lean` with their `.out`; `c4_group.py`, `c6_rank.py`, `c8_tri.py` with their `.out`; `src/`: the nine files at `8b86096`).
