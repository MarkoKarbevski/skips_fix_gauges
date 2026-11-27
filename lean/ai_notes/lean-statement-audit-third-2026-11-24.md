STATUS: complete

# Third audit of Lean statements against the papers (24 November 2026)

Auditor: an independent reader who did not write the Lean statements. Only the statements and the
definitions were judged, not the proofs. Nothing in the repository was changed: no file under
`/home/claude/lw`, `/home/claude/lp` or `/home/claude/skips_fix_gauges` was written, no commit, no
`lake build`. Scratch files and their outputs are in `/home/claude/audit3/`.

Sources.
- Lean library `/home/claude/lw/lean/SkipsLean/` at commit 1e1c5ed (clean working tree; the compiled
  files of the seven files in scope are newer than their sources, so the checks ran against the
  current statements). File names below are relative to `SkipsLean/`.
- "D": `paper docs/new_paper_functional_dimension/new_paper_functional_dimension.tex` and `.pdf`.
  "A": `paper docs/new_paper_absorb_skip/new_paper_absorb_skip.tex` and `.pdf`.
  "S": `paper docs/new_paper_skips_gain/new_paper_skips_gain.tex` and `.pdf`.
  Statement and equation numbers are those of the PDFs, read with `pdftotext -layout`; "tex N" is a
  line of the `.tex` file.
- The two earlier audits (`lean-statement-audit-dimension-skips-2026-11-24.md`,
  `lean-statement-audit-absorb-2026-11-24.md`): I rely on their sections on definitions for
  `Arch`, `Params`, `hidden`, `eval`, `rmsNorm`, `funDim`, `flat`, "generic" as `∀ᵐ` for an additive
  Haar measure, `suffix`, `SuffixFlat`, `Claim`, `Regular`, `blockLHS`, `TanhDepthGeneric`,
  `cobDir`, `Params.cob`, `vanillaBlock`, `subProd`, `Nondegenerate`, `Arch.FlatAtZero`.

Verdicts: **SAME** (same hypotheses up to notation, same conclusion), **LEAN STRONGER** (the paper's
statement is a special case), **LEAN WEAKER** (the paper's statement gives the Lean one and not
conversely), **DIFFERENT**, **PART** (only some cases or clauses are stated).

Result in one sentence: in the 91 public names of the scope I found no statement that is false,
vacuous or changed in meaning by a definition; every name depends only on the axioms `propext`,
`Classical.choice`, `Quot.sound`; the differences are of form and of coverage, and six places of
`STATEMENTS.md` are imprecise or incomplete (section (4b)).

Index shift used everywhere: the Lean block `ℓ : Fin L` is the paper's block `ℓ+1`; it reads the
hidden state `ℓ.castSucc` (the paper's `h_ℓ`) and writes the hidden state `ℓ.succ` (the paper's
`h_{ℓ+1}`).

---------------------------------------------------------------------------------------------------

## (1) Summary table

### Scope 1: Appendix D of the dimension paper, case (+), and Theorem 5.2 (i) under pre-RMSNorm

| Paper statement | Lean names | Verdict | The difference in one line |
|---|---|---|---|
| **D Theorem 5.2 (i), pre-RMSNorm with `ε > 0`** (tex 330-339) | `ae_funDim_tanh_skipless_rmsNorm` | SAME | Any nonempty finite set of tokens, any `L ≥ 0`; `d ≥ 2` is kept and only `d ≥ 1` is used. Theorem 5.2 as a whole is PART: 2 of its 7 cases are stated. |
| D proof of Theorem 5.2, "tanh blocks in the cases (n) and (+)" (tex 1574) | `funDim_tanh_skipless_rmsNorm`, `claimRMS_of_tanhDepthGeneric` (with `TanhDepthGeneric`, `regular_of_tanhDepthGeneric`, `ae_tanhDepthGeneric`) | SAME | The conditions are the paper's and do not involve `χ`. |
| D Claim `(D_k)`, case (+), eq. (17) (tex 933-936) | `ClaimRMS` | SAME | Hidden states are `T × d` matrices; `η` is a direction of all parameters and only its entries after `h_k` are constrained. Blocks without symmetries inside only. |
| D eq. (14) (tex 884-886) | `tangentRMS`, `fderiv_rmsNorm_mul` | SAME for `ε > 0` | The case (0) of eq. (14) is not stated. |
| D Lemma D.2, case (+) (tex 899-901) | `exists_open_dense_injective_fderiv_suffix_rmsNorm` | SAME | For any real-analytic maps `f_ℓ`. No `[Nonempty T]`. |
| D Lemma D.3, case (+) (tex 917-926) | `suffixFlat_of_flat_at_write_rmsNorm` | SAME | `w` is a `T × m` matrix; `[Nonempty T]` (needed). |
| D Proposition D.4, case (+) (tex 953-955) | `flat_le_range_cobDir_of_claimRMS`, `funDim_of_claimRMS` | SAME | Stated as "flat ⊆ antisymmetric changes of basis" and `fd + (L+1) d(d−1)/2 = P`; the other inclusion is `cobDir_mem_flat_skipless_rmsNorm`. No gated blocks. |
| D Lemma D.5, case (+) (tex 965-967) | `claimRMS_last` | SAME | For any maps `f_ℓ`. The rank of `D` cannot be dropped here (test D4). |
| D eqs. (20), (21), (22), case (+) (tex 984-992) | `blockLHS`, `suffixFlat_castSucc_iff_mlp_rmsNorm_values` | SAME | For any differentiable activation. |
| D Lemma D.6, case (+) (tex 994-999) | `suffixFlat_castSucc_iff_mlp_rmsNorm` | SAME | For any real-analytic activation. |
| D proof of Lemma D.7, "the fact" (tex 1051), case (+) | `eq_zero_of_fderiv_suffix_one_sub_sq_rmsNorm` | SAME | — |
| D Lemma D.7, case (+) (tex 1030-1032) | `claimRMS_castSucc_tanh` | SAME | `[Nonempty T]` is in the statement; with no tokens the implication holds vacuously (test S3). |
| D clauses of the proofs of D.2, D.4, D.5 (chain rules, `𝐃χ(h)` invertible, analyticity) | 16 helper names, see 3.11 | SAME | 13 of them are not in the index. "Diffeomorphism onto the ball" is stated only in parts. |

### Scope 2: Proposition 5.1 of the absorb paper

| Paper statement | Lean names | Verdict | The difference in one line |
|---|---|---|---|
| A Proposition 5.1 (i) with Remark A.16 (tex 407-411, 878-880) | `Params.limitScale`, `exists_bound_eval_limitScale`, `tendstoUniformlyOn_eval_limitScale` | SAME | Lean states the family `F_t` of the proof and the rate. The hypothesis is "every fixed map `f_ℓ` is locally Lipschitz", formally more than "the blocks are locally Lipschitz"; the paper's form follows from the Lean statement (test L2). |
| A Proposition 5.1 (ii) with Remark A.16 | `Params.writeScale`, `DefinedAt`, `exists_bound_eval_writeScale`, `tendstoUniformlyOn_eval_writeScale` | SAME | The same remark on the hypothesis (test L3). "`F_t` is defined" is in the statement with the bound, not in the statement of uniform convergence. |

### Scope 3: Definition 3.1 and Proposition 3.3 of the dimension paper at one hidden state

| Paper statement | Lean names | Verdict | The difference in one line |
|---|---|---|---|
| D Definition 3.1 (tex 209-214) | `Params.cobAt`, the eight `Params.cobAt_*` | SAME | — |
| D Proposition 3.2 for one hidden state | `eval_cobAt_skipless`, `eval_cobAt_rmsNorm` | SAME (a special case of 3.2) | Any real `ε`. The clauses "with the hidden states `h_ℓ G_ℓ`" and "`ε = 0`, `G = cQ`" are not stated for one state. |
| D Proposition 3.3 (i) (tex 239) | `cobAt_read_eq_one`, `cobAt_D_eq_one` | SAME | — |
| D Proposition 3.3 (ii) (tex 240) | `cobAt_read_eq_of_qr`, `cobAt_D_eq_of_qr` | LEAN STRONGER | `W_1` need not be invertible, `R` need not be triangular, any real `ε`. |
| D Proposition 3.3, "At generic parameters every hidden state has such columns" (tex 241) | `ae_exists_isUnit_det_submatrix_cols` | SAME | The sizes that the sentence needs are hypotheses: at least `d` columns in every read, `d_out ≥ d`. |
| D Proposition 3.3, "remove `(L+1) dim 𝒢` parameters" (tex 241) | none | not stated | — |
| D paragraph after 3.3 (tex 245): rows of a write or of `E`, no normalization | `cobAt_write_eq_one`, `cobAt_E_eq_one` | SAME | — |
| D proof of 3.3 (tex 423): rows of a write under pre-RMSNorm | `cobAt_write_eq_of_qr`, `cobAt_E_eq_of_qr` | LEAN STRONGER | As (ii). |
| D proof of 3.3, last sentence, and Example A.2: rows at generic parameters | `ae_exists_isUnit_det_submatrix_rows` | SAME | Existence form, with `d_in ≥ d` and at least `d` rows in every write. |

### Scope 4: the paper's forms in the absorb paper

| Paper statement | Lean names | Verdict | The difference in one line |
|---|---|---|---|
| A Theorem A.4 (tex 513-518) | `relu_absorb_identity_iff` | LEAN STRONGER | No `d ≥ 2`. |
| A Theorem A.7 (tex 554-556) | `gelu_absorb_identity_iff` | SAME | The paper's A.7 has no `d ≥ 2` either. |
| A Corollary A.10, first half (tex 595-597) | `ae_not_relu_absorb_identity`, `ae_not_gelu_absorb_identity` | SAME | — |
| A Corollary A.10, second half | `ae_not_relu_skipless_eq_residual`, `ae_not_gelu_skipless_eq_residual` | SAME | Generic in the weights of the skipless block, as in the paper's proof. |
| A Theorem 3.1 (ii), first half / Proposition A.11 (i) (tex 235-239, 604-608) | `exists_relu_block_add_linear`, `exists_gelu_block_add_linear` | LEAN STRONGER | Every `M` (also singular, also `0`); no `d ≥ 2`. |
| A Proposition 4.4 (tex 366-368) | `exists_skipless_eq_residual_relu`, `exists_skipless_eq_residual_gelu` | LEAN STRONGER | The skipless network has the same `E`, `D` and `d`; no Scope. |
| A Theorem 4.1 (i), gated blocks (tex 328-332) | `exists_ne_residual_skipless_gated`, `exists_ne_residual_skipless_gated_rmsNorm` | SAME | The residual network may have no block; no Scope. |
| A Theorem 4.1 (i), positively homogeneous blocks | `flatAtZero_of_homogeneous`, `flatAtZero_of_homogeneous_of_continuous`, `exists_ne_residual_skipless_homogeneous`, `exists_ne_residual_skipless_homogeneous_rmsNorm` | SAME for vanilla and gated blocks; an added hypothesis for arbitrary maps | Homogeneity is assumed of the fixed map `f_ℓ`, with one real degree per network, and `f_ℓ` is assumed bounded on the unit sphere. The two networks may have different degrees. |
| A Theorem 4.1 (i), SwiGLU, GeGLU, ReLU², ReGLU | the eight names `exists_ne_residual_skipless_{swiglu,geglu,reluSq,reglu}[_rmsNorm]` | SAME | One `ε` for both networks, as in the paper. |
| A Corollary A.3 (tex 500-502) | the statements of Theorem 4.1 (i) | PART | Networks that mix gated and homogeneous blocks, or degrees, are covered only by the general `exists_ne_residual_skipless_of_flatAtZero[_rmsNorm]` (earlier audit). The first sentence (compositions) has no statement of its own. |

### Scope 5: the skips paper

| Paper statement | Lean names | Verdict | The difference in one line |
|---|---|---|---|
| S Theorem 3.3 (iii), readout `D` under pre-RMSNorm (tex 305-310) | `exists_cob_residual_D_upperTriangular` | LEAN STRONGER | No invertibility, any real `ε`; "there is an orthogonal `Q`" instead of "for the factor `Q` of `W_1 = QR`". With it all four cases of (iii) are stated. |

---------------------------------------------------------------------------------------------------

## (2) Definitions new in these files, clause by clause

### 2.1 `ClaimRMS` (`Depth/SuffixRMS.lean:149`) against Claim `(D_k)`, case (+) (D tex 933-936, eq. (17); outline tex 763)

Paper: "Claim `(D_k)`, for `k = 0, …, L`. Let `Z` be a `d × d` matrix and `η` a direction of the
weights of the blocks `k+1, …, L` and of `D`. If (16) holds, then `Z ∈ 𝔤`, and with `Z_k = Z` there
are `Z_{k+1}, …, Z_L ∈ 𝔤` such that, for tanh and GELU blocks,
`η = ({−Ẑ_{ℓ−1} W_read^ℓ, W_write^ℓ Z_ℓ}_{ℓ=k+1}^L, −Ẑ_L D)`." In the case (+), `𝔤` is the set of the
antisymmetric matrices and `Ẑ = Z` (table of D.2, tex 844).

Lean:
```
def ClaimRMS (k : Fin (L + 1)) : Prop :=
  ∀ (Z : Matrix d d ℝ) (η : Params A dIn dOut), SuffixFlat A θ k Z η →
    ∃ X : Fin (L + 1) → Matrix d d ℝ, X k = Z ∧ (∀ ℓ, k ≤ ℓ → X ℓ ∈ antisymmetric d) ∧
      (∀ ℓ : Fin L, k ≤ ℓ.castSucc →
        η.read ℓ = -(X ℓ.castSucc * θ.read ℓ) ∧ η.write ℓ = θ.write ℓ * X ℓ.succ) ∧
      η.D = -(X (Fin.last L) * θ.D)
```

| Clause of the paper | Lean | Same? |
|---|---|---|
| "`Z` a `d × d` matrix" | `Z : Matrix d d ℝ`, universally quantified | Same |
| "`η` a direction of the weights of the blocks `k+1, …, L` and of `D`" | `η : Params A dIn dOut`, a direction of all parameters | Same in content: `SuffixFlat A θ k Z η` sees only the entries of `η` after `h_k`, and the conclusion constrains only these (as for `Claim`, earlier audit, 2.8) |
| "If (16) holds" | `SuffixFlat A θ k Z η`: the identity for all `h : Matrix T d ℝ` | Same; `T` rows in the place of one row (see 2.7) |
| "then `Z ∈ 𝔤`" | `X k = Z` and `X k ∈ antisymmetric d` (the clause `k ≤ ℓ` at `ℓ = k`) | Same |
| "with `Z_k = Z` there are `Z_{k+1}, …, Z_L ∈ 𝔤`" | `∃ X`, `X k = Z`, `X ℓ ∈ antisymmetric d` for every `ℓ ≥ k`. The values `X ℓ` for `ℓ < k` are not constrained and not used | Same |
| `η_read^ℓ = −Z_{ℓ−1} W_read^ℓ`, `η_write^ℓ = W_write^ℓ Z_ℓ` for the paper's `ℓ = k+1, …, L` | for the Lean blocks `ℓ` with `k ≤ ℓ.castSucc` (the paper's block `ℓ+1 ≥ k+1`): `η.read ℓ = -(X ℓ.castSucc * θ.read ℓ)`, `η.write ℓ = θ.write ℓ * X ℓ.succ` | Same; sides and indices are right |
| `η_D = −Z_L D` | `η.D = -(X (Fin.last L) * θ.D)` | Same |
| "antisymmetric" | `antisymmetric d` is the submodule `{X | Xᵀ = −X}` (`Dimension/UpperBoundRMSNorm.lean`) | Same |

`ClaimRMS` is `Claim` with the one clause "antisymmetric" added (test D5: `ClaimRMS A θ k → Claim A θ k`).
It does not mention `ε` or `χ`: `χ` is a field of `A`, and `ε` enters through the hypothesis
`A.χ = rmsNorm ε` of the theorems. The form of the claim for gated blocks (eq. (19))
and for the case (0) (eq. (18)) is not defined. The paragraph after the claim ("Conversely, every
`Z = Z_k ∈ 𝔤` and `η` of the form (17) satisfy (16)", tex 947-951) has no Lean statement for a
general `k`; for `k = 0` and the whole network it is `cobDir_mem_flat_skipless_rmsNorm`.

Verdict: **SAME**.

### 2.2 `tangentRMS` (`Depth/StepTanhRMS.lean:36`) against the right side of eq. (14) (D tex 884-886)

Paper: "In the cases (+) and (0), for a `d × d` matrix `Z` and `n = χ(h)`,
`𝐃χ(h)(hZ) = nZ − (⟨nZ, n⟩/d) n`", with `⟨u, v⟩ = uvᵀ`.

Lean: `tangentRMS Z n = Matrix.of fun t => (n * Z) t - (((n * Z) t ⬝ᵥ n t) / (Fintype.card d : ℝ)) • n t`.
Row `t` of the result is `n_t Z − (⟨n_t Z, n_t⟩/d) n_t` (test D7, by `rfl`, on one token). The
division is by the real number `d`. **SAME** as an expression; the identity itself is
`fderiv_rmsNorm_mul` (entry 3.3), for `ε > 0` only.

### 2.3 `Params.limitScale`, `Params.writeScale` (`Absorb/Limits.lean:38, 47`) against the networks `F_t` (A tex 852, PDF Appendix A.4)

Paper: "For `t ≥ 1`, let `F_t` be the residual network with the embedding `E`, the reads
`t^{1−ℓ} W_read^ℓ`, the writes `t^ℓ W_write^ℓ` and the readout `t^{−L} D`; under pre-RMSNorm with
`ε = 0`, let `F_t` keep the embedding, the reads and the readout of `F` and have the writes
`t^ℓ W_write^ℓ`."

Lean:
```
Params.limitScale θ t = { E := θ.E, read := fun ℓ => (t ^ (ℓ : ℕ))⁻¹ • θ.read ℓ,
                          write := fun ℓ => t ^ ((ℓ : ℕ) + 1) • θ.write ℓ, D := (t ^ L)⁻¹ • θ.D }
Params.writeScale θ t = { E := θ.E, read := θ.read,
                          write := fun ℓ => t ^ ((ℓ : ℕ) + 1) • θ.write ℓ, D := θ.D }
```

| Weight | Paper, block `ℓ' = ℓ+1` | Lean, block `ℓ : Fin L` | Same? |
|---|---|---|---|
| embedding | `E` | `θ.E` | Same |
| read, case (i) | `t^{1−ℓ'} = t^{−ℓ}` | `(t ^ ℓ)⁻¹` | Same |
| write, both cases | `t^{ℓ'} = t^{ℓ+1}` | `t ^ (ℓ + 1)` | Same |
| readout, case (i) | `t^{−L}` | `(t ^ L)⁻¹` | Same |
| read and readout, case (ii) | unchanged | unchanged | Same |

For two blocks the Lean reads are scaled by `t^0, t^{−1}`, the writes by `t^1, t^2`, the readout by
`t^{−2}` (test L6, by `rfl`). The definitions take any real `t`; for `t = 0` Lean's `0⁻¹ = 0` gives
weights that the paper does not define, and no statement uses `t < 1` in (i) or `t < t₀` in (ii).
The residual network is `eval A 1 (θ.limitScale t)`: the stream matrices `1` are identity matrices
(test L5), the architecture `A` (kinds and widths) is that of `F`. **SAME.**

### 2.4 `DefinedAt` (`Absorb/Limits.lean:56`) against "defined at" for `ε = 0` (A tex 210; proof of 5.1 (ii), tex 871)

Paper, Section 2: "For `ε = 0`, `N` is defined only on hidden states without zero rows. A network is
then defined at the inputs at which no state that it normalizes has a zero row." Proof of 5.1 (ii):
"a compact set of inputs at which `F` is defined, that is, at which no row of `XE` or of a hidden
state of `F` vanishes."

Lean: `DefinedAt A S θ X := ∀ (k : Fin (L + 1)) (t : T), hidden A S θ X k t ≠ 0`, for any stream
matrices `S` (`0` for `F`, `1` for `F_t`).

- The states that a network normalizes are `h_0 = XE, h_1, …, h_L` (the readout normalizes `h_L`).
  `k` runs over `0, …, L`. Same.
- In Lean `rmsRow 0 0 = 0`, so `hidden` is a total function also where the paper's network is not
  defined. This does not change the meaning of `DefinedAt`: by induction on `k`, if no row of the
  Lean states `h_0, …, h_{k−1}` vanishes, these are the paper's states and the Lean `h_k` is the
  paper's `h_k`. So `DefinedAt A S θ X` holds exactly when the paper's network is defined at `X`,
  and then `eval A S θ X` is the paper's output. This induction is my argument; it is not a Lean
  statement.
- With no block, `DefinedAt` says that no row of `XE` vanishes (test L4).

Verdict: **SAME**.

### 2.5 `Params.cobAt` (`Symmetry/AtOneState.lean:33`) against Definition 3.1 (D tex 209-214)

Paper: "The writes into the hidden state `h_ℓ` are `W_write^ℓ`, or `E` if `ℓ = 0`, and the reads of
`h_ℓ` are `W_read^{ℓ+1}`, or `D` if `ℓ = L`. For an invertible `d × d` matrix `G`, the change of basis
`G` at `h_ℓ` maps `W ↦ WG` for the writes into `h_ℓ`, `W ↦ G⁻¹W` for the reads of `h_ℓ`."

Lean: `θ.cobAt j G := θ.cob (Function.update (fun _ => 1) j G) (Function.update (fun _ => 1) j G)`,
`G : GL d ℝ`, `j : Fin (L + 1)`; and `Params.cob θ G K` has `E := θ.E * G 0`,
`read ℓ := (K ℓ.castSucc)⁻¹ * θ.read ℓ`, `write ℓ := θ.write ℓ * G ℓ.succ`, `D := (K (Fin.last L))⁻¹ * θ.D`.

The eight statements, each against the definition:

| Lean statement | Says | Clause of Definition 3.1 | Same? |
|---|---|---|---|
| `Params.cobAt_E_zero` | `(θ.cobAt 0 G).E = θ.E * G` | `E` is the write into `h_0`: `W ↦ WG` | Same |
| `Params.cobAt_E_of_ne` | `j ≠ 0 → (θ.cobAt j G).E = θ.E` | `E` writes into no other hidden state | Same |
| `Params.cobAt_read_castSucc` | `(θ.cobAt ℓ.castSucc G).read ℓ = G⁻¹ * θ.read ℓ` | the read of `h_ℓ` is `W_read^{ℓ+1}`, the Lean block `ℓ`: `W ↦ G⁻¹W` | Same |
| `Params.cobAt_read_of_ne` | `j ≠ ℓ.castSucc → (θ.cobAt j G).read ℓ = θ.read ℓ` | a read is the read of one hidden state only | Same |
| `Params.cobAt_write_succ` | `(θ.cobAt ℓ.succ G).write ℓ = θ.write ℓ * G` | the write into `h_{ℓ+1}` is `W_write^{ℓ+1}`, the Lean block `ℓ`: `W ↦ WG` | Same |
| `Params.cobAt_write_of_ne` | `j ≠ ℓ.succ → (θ.cobAt j G).write ℓ = θ.write ℓ` | a write goes into one hidden state only | Same |
| `Params.cobAt_D_last` | `(θ.cobAt (Fin.last L) G).D = G⁻¹ * θ.D` | `D` is the read of `h_L`: `W ↦ G⁻¹W` | Same |
| `Params.cobAt_D_of_ne` | `j ≠ Fin.last L → (θ.cobAt j G).D = θ.D` | `D` reads no other hidden state | Same |

The eight statements give every weight of `θ.cobAt j G` for every `j`, so they determine the
definition. Test A1: for two blocks and `j = 1`, the weights `E`, `read 0`, `write 1`, `D` stay and
`write 0 ↦ write 0 * G`, `read 1 ↦ G⁻¹ * read 1`. Test A1': with no block, `E ↦ EG` and `D ↦ G⁻¹D`.
Verdict: **SAME**. (The earlier audit found `Params.cob` to be the tuple of Proposition 3.2; `cobAt`
is now the object of Definition 3.1 itself.)

### 2.6 Objects of the earlier audits that these files use in a new way

- `SuffixFlat`, `Regular`, `blockLHS`, `TanhDepthGeneric` are used with `χ = rmsNorm ε`, `ε > 0`.
  None of the four definitions mentions `χ` except through `A`, and the paper's definitions for
  the case (+) are the same as for the case (n): the identity (16) "for all rows `h`" (tex 923-925),
  (R1) and (R3) "in the cases (n) and (+), `𝐃g_ℓ(n)` is invertible at some row `n`" (tex 893-895),
  `𝓛` of eq. (21), and the conditions of tex 1574. The only change in the case (+) is the argument
  `ż(n)` that is passed to `blockLHS`: eq. (20), `(nZ − ⟨nZ, n⟩n/d)W + nη_W`, written
  `tangentRMS Z n * θ.read k + n * η.read k`. Same.
- `antisymmetric d` plays the role of `𝔤` in the case (+); `finrank_antisymmetric` gives its dimension
  `d(d−1)/2` (natural-number division, exact because `d(d−1)` is even; test D8).
- `Arch.FlatAtZero` is now reached from a hypothesis written out in the statements:
  `∀ ℓ lam M, 0 < lam → A.f ℓ (lam • M) = lam ^ k • A.f ℓ M` with `k : ℝ` (a real power) and
  `∀ ℓ, ∃ C, ∀ M, ‖M‖ = 1 → ‖A.f ℓ M‖ ≤ C`. This is "the fixed map `f_ℓ` is positively homogeneous of
  degree `k`" and "bounded on the unit sphere" (elementwise norm; for a homogeneous map the bound
  does not depend on the norm). See entry 3.24.
- Mathlib notions that appear for the first time: `LocallyLipschitz f` (every point has a
  neighbourhood on which `f` is Lipschitz), `TendstoUniformlyOn F f Filter.atTop 𝒳` (uniform
  convergence on `𝒳` as `t → ∞` over the real numbers), `Bornology.IsBounded`, `IsCompact`. They are
  the paper's notions.
- A choice of `d` columns is a map `c : d → A.r ℓ` and the chosen columns are
  `(θ.read ℓ).submatrix id c`; a choice of rows is `ρ : d → A.w ℓ` and `(θ.write ℓ).submatrix ρ id`
  (as in `Symmetry/Reduction.lean`, earlier audit). "Upper triangular" is `Matrix.BlockTriangular id`
  for a linear order on `d`: the entry `(i, j)` vanishes when `j < i`.

### 2.7 Instance arguments, tokens, degenerate cases

- **One token against the rows `T`.** Appendix D takes "inputs [with] one token: a hidden state is a
  row `h`" (tex 750). In Lean a hidden state is a `T × d` matrix. For `T` with one element every
  Lean statement of scope 1 is the paper's statement. For a larger `T` the statements about a
  general `A : Arch T d L` (D.2, D.3, D.4, D.5) are about more maps than the paper's, and those
  about `Arch.mlp` (eq. (22), D.6, D.7) are the paper's statements for all tokens at once; for MLP
  blocks, which act on each token, the identity for all matrices is the identity for all rows when
  `T` is not empty. This last equivalence is an argument, not a Lean statement. Theorem 5.2 itself is
  stated in the paper for `T` tokens (Section 2), and so it is in Lean.
- **`[Nonempty T]`** is in D.3, D.4, D.5, D.7, `claimRMS_of_tanhDepthGeneric` and the two forms of the
  theorem; it is not in D.2, eq. (14), eq. (22), D.6 and "the fact". It is needed where the claim
  itself is concluded: with no tokens `ClaimRMS A θ k` is false for nonempty `d` (test D3), and the
  functional dimension is `0` (earlier audit). It is not needed for the truth of D.7 (test S3).
- **`0 < ε`** is a hypothesis of every statement of the case (+) that needs RMSNorm to be
  differentiable. `ε` is an implicit real number and both the hypothesis and `χ = rmsNorm ε` name
  the same `ε`.
- **`L = 0`** is allowed everywhere. For Theorem 5.2 (i) it gives the network `x ↦ N_ε(xE) D` and
  `fd + d(d−1)/2 = P`. For Proposition 5.1 it gives `F_t = F`. In Theorem 4.1 (i) the skipless
  network has `L' + 1` blocks, as it must.
- **`d`.** Theorem 5.2 (i) keeps `2 ≤ Fintype.card d`; the proof uses a nonempty `d` only (test D2).
  For `d = 1` the count is `0`. For empty `d` all matrices are empty.
- **Universes.** `hid : Fin L → Type` everywhere, and in the network statements of
  `Absorb/PaperForms.lean` also `d : Type`, because `hid ℓ ⊕ d` is a width. No loss: finite types.
- **Natural-number arithmetic.** The count is `(L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2)`
  and the statement is an addition `fd + count = P`. The truncated subtraction and division are exact
  (`n(n−1)` is even; for `n = 0` both sides are `0`), so this is the paper's `(L+1) d(d−1)/2`.

### 2.8 Checks run in Lean

Each test is an `example` (or a helper `theorem`) in a scratch file that compiles against the
library with no error and no `sorry`. Files: `/home/claude/audit3/Check1.lean`, `Check2.lean`,
`Check3.lean` (`#check @name` and `#print` of every name; outputs `.out`), `Axioms.lean` (91 names),
`TestD.lean`, `TestL.lean`, `TestA.lean`, `TestS.lean`.

| Test | What it states | Result |
|---|---|---|
| D1 | Theorem 5.2 (i) under pre-RMSNorm at one token, `d = d_in = d_out = 2`, two blocks of width 3, `ε = 1`: `fd + 3 = P` at generic parameters; a Haar measure exists on these parameters | compiles |
| D2 | the theorem with `[Nonempty d]` in the place of `2 ≤ Fintype.card d` | compiles |
| D3 | with `T = Empty` and nonempty `d`: `¬ ClaimRMS A θ k` | compiles |
| D4 | with `θ.D = 0`, nonempty `d`, any `T`: `¬ ClaimRMS A θ (Fin.last L)` (the hypothesis on `D` of Lemma D.5 cannot be dropped in the case (+)) | compiles |
| D5 | `ClaimRMS A θ k → Claim A θ k` | compiles |
| D6 | Proposition D.4 (+) as an equivalence: `η ∈ flat A 0 θ ↔ ∃ X` antisymmetric with `η = cobDir θ X` | compiles |
| D7 | row of `tangentRMS Z n` on one token is `nZ − (⟨nZ, n⟩/d) n` (`rfl`) | compiles |
| D8 | `2 * (n * (n - 1) / 2) = n * (n - 1)` in `ℕ` | compiles |
| L1 | `LocallyLipschitz ((Arch.mlp Real.tanh χ hid).f ℓ)` | compiles |
| L2 | Proposition 5.1 (i) with the rate, with the hypothesis "every block `n ↦ f_ℓ(n W_read^ℓ) W_write^ℓ` is locally Lipschitz", from `exists_bound_eval_limitScale` | compiles (for `d : Type`) |
| L3 | the same for Proposition 5.1 (ii), from `exists_bound_eval_writeScale` | compiles (for `d : Type`) |
| L4 | with no block, `DefinedAt A S θ X ↔ ∀ t, (X * θ.E) t ≠ 0` | compiles |
| L5 | the stream matrices `1` are identity matrices | compiles |
| L6 | the exponents of `limitScale` for two blocks (`rfl`) | compiles |
| A1, A1' | Definition 3.1 for two blocks at `h_1`, and for no block | compiles |
| A2 | Proposition 3.3 (ii) at one hidden state with the factorization inside: there is an orthogonal `Q` whose change of basis at that state keeps the function and makes the chosen columns upper triangular | compiles |
| A3 | Proposition 3.3 (i) with the hypothesis `IsUnit (…).det` and `G = W_1` in the conclusion | compiles |
| A4 | at generic parameters, for every hidden state there are columns and a change of basis at that state that keeps the function and turns them into `1` | compiles |
| P1 | the fixed map of a ReLU² block is positively homogeneous of degree `2` (real exponent) and continuous | compiles |
| P2 | Theorem 4.1 (i) for ReLU² networks from `exists_ne_residual_skipless_homogeneous` | compiles |
| S1 | S Theorem 3.3 (iii), readout, pre-RMSNorm, in the wording "for every `W_1 = QR` with `Q` orthogonal, the change of basis `Q` turns `W_1` into `R`", from `eval_cob_residual_rmsNorm` | compiles |
| S2 | with `T = Empty`, a regular `θ` and nonempty `d`: `¬ Claim A θ k` for every `k` | compiles |
| S3 | hence with `T = Empty` the implications `(D_{k+1}) ⇒ (D_k)` of Lemma D.7 hold, in both cases | compiles |

`#print axioms` on the 91 public names of the scope (21 of `Depth/SuffixRMS.lean`, 7 of
`Depth/StepTanhRMS.lean`, 3 of `Depth/TanhRMS.lean`, 14 of `Absorb/Limits.lean`, 21 of
`Symmetry/AtOneState.lean`, 24 of `Absorb/PaperForms.lean`, and `exists_cob_residual_D_upperTriangular`):
every one prints `[propext, Classical.choice, Quot.sound]` and nothing else. None of the seven
files contains `sorry`, `admit`, `native_decide` or an `axiom`.

---------------------------------------------------------------------------------------------------

## (3) One entry per statement

Elaborated statements are quoted from `/home/claude/audit3/Check1.out`, `Check2.out`, `Check3.out`
with the instance arguments shortened. Unless said otherwise the implicit arguments are
`{T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut]`,
and for MLP networks `{hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]`.

### 3.A Dimension paper, Appendix D in the case (+), and Theorem 5.2 (i)

#### 3.1 D Theorem 5.2 (i), under pre-RMSNorm with `ε > 0` (tex 330-339)

Paper: "Let `d_in, d_out ≥ d_model ≥ 2`, and consider networks without biases whose blocks are all of
one kind, tanh, GELU, SwiGLU or GeGLU, each with at least `d_model` hidden units. In the following
cases the functional dimension at generic parameters is `P − (L+1) dim 𝒢 − s`, so the network
satisfies the equality condition. (i) tanh blocks: without normalization, and under pre-RMSNorm with
`ε > 0` and with `ε = 0`." Under pre-RMSNorm `dim 𝒢 = d(d−1)/2` (tex 220), and `s = 0` for tanh blocks.

Lean (`Depth/TanhRMS.lean:55`):
```
theorem ae_funDim_tanh_skipless_rmsNorm {ε : ℝ} [Nonempty T] (hε : 0 < ε)
    (μ : Measure (Params (Arch.mlp Real.tanh (rmsNorm ε) hid) dIn dOut)) [μ.IsAddHaarMeasure]
    (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, funDim (Arch.mlp Real.tanh (rmsNorm ε) hid) 0 θ
        + (L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2)
      = Module.finrank ℝ (Params (Arch.mlp Real.tanh (rmsNorm ε) hid) dIn dOut)
```

| Clause | Paper | Lean | Same? |
|---|---|---|---|
| sizes | `d_in, d_out ≥ d ≥ 2` | `hdIn`, `hdOut`, `hd` | Same |
| widths | every block has at least `d` hidden units | `hhid`, for every block; the widths may differ | Same |
| blocks | all tanh, no biases | `Arch.mlp Real.tanh … hid` | Same |
| normalization | pre-RMSNorm with `ε > 0`, before every read and before the readout | `χ = rmsNorm ε`, `hε : 0 < ε` | Same |
| network | without skip connections | `funDim … 0 θ`, the stream matrices are `0` | Same |
| tokens | `T` tokens (Section 2) | any nonempty finite `T` | Same |
| generic | outside a set of Lebesgue measure zero | `∀ᵐ θ ∂μ`, every additive Haar measure `μ` | Same |
| conclusion | `fd = P − (L+1) d(d−1)/2` | `fd + (L+1) * (d(d−1)/2) = P` | Same (2.7) |
| "so the network satisfies the equality condition" | Definition 4.4 | not stated; no Lean definition of the equality condition | not stated |
| depth | `L` blocks | any `L : ℕ`, also `0` | Same or more general |

I looked for a case in which the Lean statement says more or less than the paper's: empty `T` is
excluded by `[Nonempty T]`; `d ≤ 1` by `hd`; a narrow block by `hhid`; small `d_in`, `d_out` by
`hdIn`, `hdOut`; `ε ≤ 0` by `hε`. None found. The statement is not vacuous: at one token, `d = 2`,
two blocks of width 3 it reads `fd + 3 = P`, and a Haar measure exists there (test D1). The
hypothesis `hd` is used only to make `d` nonempty: the same proof gives the statement for `d ≥ 1`
(test D2).

Verdict: **SAME**. Theorem 5.2 as a whole is **PART**: stated are (i) without normalization (earlier
audit) and (i) under pre-RMSNorm with `ε > 0`; not stated are (i) for `ε = 0`, (ii) and (iii).

#### 3.2 D proof of Theorem 5.2, "tanh blocks in the cases (n) and (+)" (tex 1574)

Paper: "Let `θ` satisfy (R1), let every block satisfy (T1) and (T2), and let every `W_read^ℓ W_write^ℓ`
be invertible. These conditions fail only on a set of measure zero … Such `θ` are regular … By
Lemma D.5 and Lemma D.7, Claim `(D_k)` holds at `θ` for `k = L`, then for `k = L − 1`, and so on down
to `k = 0`. By Proposition D.4, the Jacobian at `θ` has the rank (13) on some finite batch, and by
(R1) it has at most this rank on every batch."

Lean (`Depth/TanhRMS.lean:31, 42`), for `θ : Params (Arch.mlp Real.tanh (rmsNorm ε) hid) dIn dOut`:
```
claimRMS_of_tanhDepthGeneric [Nonempty T] : 0 < ε → TanhDepthGeneric θ →
    ∀ k : Fin (L + 1), ClaimRMS (Arch.mlp Real.tanh (rmsNorm ε) hid) θ k
funDim_tanh_skipless_rmsNorm [Nonempty T] : 0 < ε → TanhDepthGeneric θ →
    funDim (Arch.mlp Real.tanh (rmsNorm ε) hid) 0 θ + (L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2)
      = Module.finrank ℝ (Params …)
```
`TanhDepthGeneric θ` is (R1), (T1), (T2) for every block and `IsUnit (θ.read ℓ * θ.write ℓ).det`
(earlier audit, 2.8); it does not involve `χ`, as in the paper, where the same conditions serve the
cases (n) and (+). `regular_of_tanhDepthGeneric` and `ae_tanhDepthGeneric` (earlier audit) are stated
for every `χ` and are used here unchanged. The Lean statements are at every `θ` that satisfies the
conditions, with no measure. Verdict: **SAME**.

#### 3.3 D eq. (14) (tex 884-886)

Paper: "In the cases (+) and (0), for a `d × d` matrix `Z` and `n = χ(h)`: `𝐃χ(h)(hZ) = nZ − (⟨nZ, n⟩/d) n`."
Lean (`Depth/StepTanhRMS.lean:49`):
`fderiv_rmsNorm_mul : 0 < ε → ∀ (Z : Matrix d d ℝ) (h : Matrix T d ℝ), fderiv ℝ (rmsNorm ε) h (h * Z) = tangentRMS Z (rmsNorm ε h)`.
Comparison: `χ = rmsNorm ε`, the direction `hZ`, the value at `n = N_ε(h)`, row by row (2.2). The
derivative is Mathlib's `fderiv` of the map on `T × d` matrices; `N_ε` is differentiable for `ε > 0`,
so the convention for maps that are not differentiable is not in play. Verdict: **SAME for `ε > 0`**;
the case (0) of eq. (14) is not stated.

#### 3.4 D Lemma D.2, case (+) (tex 899-901)

Paper: "Let `θ` be regular. For every `k` there is an open dense set `𝒰_k` of rows such that, for
`h ∈ 𝒰_k`, `𝐃𝓑_{>k}(h) v = 0` only if `v = 0`, in the cases (n) and (+)."
Lean (`Depth/SuffixRMS.lean:431`):
```
exists_open_dense_injective_fderiv_suffix_rmsNorm (A : Arch T d L) (θ : Params A dIn dOut) {ε : ℝ} :
  0 < ε → A.χ = rmsNorm ε → (∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) → Regular A θ → ∀ k : Fin (L + 1),
    ∃ U : Set (Matrix T d ℝ), IsOpen U ∧ Dense U ∧
      ∀ h ∈ U, Function.Injective (fderiv ℝ (fun h' => suffix A 0 θ k h') h)
```
Comparison: the order of the quantifiers is the paper's (`θ`, then `k`, then the set). "Only if
`v = 0`" is injectivity of the derivative. The blocks are any real-analytic maps `f_ℓ` (the paper:
tanh, GELU, SwiGLU, GeGLU blocks, which are real-analytic). `Regular` is the paper's "regular" for
the case (+) (2.6). No `[Nonempty T]`. Verdict: **SAME** (Lean for more general blocks).

#### 3.5 D Lemma D.3, case (+) (tex 917-926)

Paper: "Let `θ` be regular, `0 ≤ k ≤ L`, and let `A` be a matrix with `d` columns and rank `d`. Let
`η_A` be a matrix of the size of `A` and `η` a direction of the weights of the blocks `k+1, …, L` and
of `D`. If `𝐃𝓑_{>k}(wA)(w η_A) + 𝐃_θ𝓑_{>k}(wA) η = 0` for all rows `w`, then `η_A = AZ` for a `d × d`
matrix `Z`, and [the identity (16) holds] for all rows `h`."
Lean (`Depth/SuffixRMS.lean:504`): `suffixFlat_of_flat_at_write_rmsNorm [Nonempty T]`, with
`0 < ε`, `A.χ = rmsNorm ε`, analytic `f_ℓ`, `Regular A θ`, `k`, `{m} [Fintype m] (M : Matrix m d ℝ)`,
`M.rank = Fintype.card d`, `ηM : Matrix m d ℝ`, `η`, and the hypothesis for all `w : Matrix T m ℝ`;
conclusion `∃ Z : Matrix d d ℝ, ηM = M * Z ∧ SuffixFlat A θ k Z η`.
Comparison: one for one; the paper's `A` is `M`. `[Nonempty T]` is needed: with no tokens the
hypothesis holds for every `ηM` and the conclusion `ηM = M * Z` does not. Verdict: **SAME**.

#### 3.6 D Proposition D.4, case (+) (tex 953-955)

Paper: "Let `θ` be regular, with no vanishing value column if the blocks are gated, and let `(D_0)`
hold at `θ`. Then the directions `η ∈ ℝ^P` with `𝐃_θ F(θ, x) η = 0` for all `x` … are the directions
`η^Z` of (11), or `η^{Z,Δ}` of (12) for gated blocks, and the Jacobian of the network has the rank
(13) on some finite batch of such inputs."
Lean (`Depth/SuffixRMS.lean:740, 763`), both with `[Nonempty T]`, `0 < ε`, `A.χ = rmsNorm ε`,
analytic `f_ℓ`, `Regular A θ`, `ClaimRMS A θ 0`:
```
flat_le_range_cobDir_of_claimRMS : ∀ η ∈ flat A 0 θ,
    ∃ X : Fin (L + 1) → Matrix d d ℝ, (∀ ℓ, X ℓ ∈ antisymmetric d) ∧ η = cobDir θ X
funDim_of_claimRMS : funDim A 0 θ + (L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2)
    = Module.finrank ℝ (Params A dIn dOut)
```
Comparison:
- "the directions … are the directions `η^Z`" with `Z_0, …, Z_L ∈ 𝔤`: Lean states the inclusion of
  the flat directions in the directions `cobDir θ X` with antisymmetric `X`. The other inclusion is
  `cobDir_mem_flat_skipless_rmsNorm` (`Dimension/UpperBoundRMSNorm.lean`, earlier audit). Together
  they give the paper's sentence as an equivalence (test D6).
- "the Jacobian has the rank (13) on some finite batch": Lean states `fd = P − (L+1) d(d−1)/2`, and
  `fd` is attained on a finite batch (`exists_jacobianRank_eq_funDim`, earlier audit). The Lean
  conclusion includes the upper bound, which the paper adds in the proof of the theorem.
- Blocks without symmetries inside only; the form for gated blocks is not stated.
Verdict: **SAME** for blocks without symmetries inside.

#### 3.7 D Lemma D.5, case (+) (tex 965-967; proof tex 972)

Paper: "If `D` has rank `d_model`, then `(D_L)` holds."
Lean (`Depth/SuffixRMS.lean:558`):
`claimRMS_last [Nonempty T] : 0 < ε → A.χ = rmsNorm ε → θ.D.rank = Fintype.card d → ClaimRMS A θ (Fin.last L)`.
Comparison: one for one; the maps `f_ℓ` are arbitrary, since `(D_L)` concerns the readout alone. In
the case (n) the Lean statement has no hypothesis on `D` (earlier audit). Here the hypothesis has a
role: with `D = 0` the identity (16) for `k = L` holds for `Z = 1`, `η = 0`, and `1` is not
antisymmetric, so `(D_L)` fails (test D4). Verdict: **SAME**.

#### 3.8 D eqs. (20), (21), (22) and Lemma D.6, case (+) (tex 984-999)

Paper: "`ż(n) = (nZ − (⟨nZ, n⟩/d) n) W + n η_W` in the cases (+) and (0)" (20);
"`𝓛(w̃, w̃'; n) = 𝐃𝓑(w̃V)((w̃' ⊙ ż(n)) V + w̃ η_V) + 𝐃_θ𝓑(w̃V) η'`" (21); "So (16) for `k` is equivalent to
`𝓛(σ(nW), σ'(nW); n) = 0` for all values `n` of `χ`, that is, … for the rows `n` with `‖n‖² < d` in the
case (+)" (22). Lemma D.6: "In the cases (n) and (+), (16) for `k` holds if and only if
`𝓛(σ(nW), σ'(nW); n) = 0` for every row `n ∈ ℝ^{1×d}`."

Lean (`Depth/StepTanhRMS.lean:218, 388`), for `θ η : Params (Arch.mlp σ (rmsNorm ε) hid) dIn dOut`,
`k : Fin L`, `Z : Matrix d d ℝ`:
```
suffixFlat_castSucc_iff_mlp_rmsNorm_values : 0 < ε → (∀ z, HasDerivAt σ (σ' z) z) →
  (SuffixFlat (Arch.mlp σ (rmsNorm ε) hid) θ k.castSucc Z η ↔
    ∀ h : Matrix T d ℝ, blockLHS θ k η ((rmsNorm ε h * θ.read k).map σ) ((rmsNorm ε h * θ.read k).map σ')
      (tangentRMS Z (rmsNorm ε h) * θ.read k + rmsNorm ε h * η.read k) = 0)
suffixFlat_castSucc_iff_mlp_rmsNorm : 0 < ε → (∀ z, HasDerivAt σ (σ' z) z) → AnalyticOnNhd ℝ σ Set.univ →
  (SuffixFlat (Arch.mlp σ (rmsNorm ε) hid) θ k.castSucc Z η ↔
    ∀ n : Matrix T d ℝ, blockLHS θ k η ((n * θ.read k).map σ) ((n * θ.read k).map σ')
      (tangentRMS Z n * θ.read k + n * η.read k) = 0)
```
Comparison:
- The Lean block `k` is the paper's block `k+1`; `k.castSucc` is the hidden state before it; `W`,
  `V`, `η_W` are `θ.read k`, `θ.write k`, `η.read k`; `η.write k` and `η'` are inside `blockLHS`
  (earlier audit, 2.8).
- (20): the third argument of `blockLHS` is `tangentRMS Z n * W + n * η_W`. Same.
- (22): Lean quantifies over the hidden states `h` and evaluates at `n = N_ε(h)`, that is, over the
  values of `χ`. The paper adds that these values are the rows of the ball; Lean does not state
  this as a lemma of its own (a private lemma shows that every `n` whose rows have `‖n_t‖² < d` is a
  value, which is the part that Lemma D.6 needs). Same.
- Lemma D.6: all `n : Matrix T d ℝ`. The activation is any real-analytic `σ` with derivative `σ'`;
  the paper has tanh or GELU blocks.
Verdict: eqs. (20) to (22) **SAME**; Lemma D.6, case (+), **SAME** (Lean for any real-analytic
activation).

#### 3.9 D Lemma D.7, case (+), and "the fact" of its proof (tex 1026-1032, 1051)

Paper: "(T1) no row of `V` vanishes; (T2) the columns of `W` are linearly independent over `ℚ`." "Let
`σ = tanh`, in the case (n) or (+), let `θ` be regular, and let block `k+1` satisfy (T1) and (T2).
Then `(D_{k+1})` implies `(D_k)`." The fact: "if a row `b ∈ ℝ^{1×q}` has
`𝐃𝓑(w̃V)(((1 − w̃²) ⊙ b) V) = 0` for all rows `w̃`, then `b = 0`."

Lean (`Depth/StepTanhRMS.lean:472, 564`), for `θ : Params (Arch.mlp Real.tanh (rmsNorm ε) hid) dIn dOut`:
```
claimRMS_castSucc_tanh [Nonempty T] : 0 < ε → Regular (Arch.mlp Real.tanh (rmsNorm ε) hid) θ →
  ∀ k : Fin L, (∀ i : hid k, θ.write k i ≠ 0) → LinearIndependent ℚ (fun j i => θ.read k i j) →
    ClaimRMS (Arch.mlp Real.tanh (rmsNorm ε) hid) θ k.succ →
      ClaimRMS (Arch.mlp Real.tanh (rmsNorm ε) hid) θ k.castSucc
eq_zero_of_fderiv_suffix_one_sub_sq_rmsNorm : 0 < ε → Regular … θ → ∀ k : Fin L,
  (∀ i : hid k, θ.write k i ≠ 0) → ∀ b : Matrix T (hid k) ℝ,
    (∀ w : Matrix T (hid k) ℝ, fderiv ℝ (fun h' => suffix … 0 θ k.succ h') (w * θ.write k)
        ((Matrix.of fun t j => (1 - w t j ^ 2) * b t j) * θ.write k) = 0) → b = 0
```
Comparison: (T1) is "no row of the write of block `k` is zero"; (T2) is linear independence over `ℚ`
of the family of the columns of the read, as vectors of `ℝ^d`; `k.succ` and `k.castSucc` are the
hidden states after and before the block. The fact assumes (T1) and regular `θ`, as the paper's
proof does. `[Nonempty T]` is in the Lean statement of D.7; with no tokens and a regular `θ` the
hypothesis `(D_{k+1})` is false for nonempty `d`, so the implication holds there too (tests S2, S3).
Verdict: **SAME** (both).

#### 3.10 D Claim `(D_k)` and eq. (16), case (+)

See 2.1 and 2.6. `ClaimRMS`: **SAME**. Eq. (16) is `SuffixFlat`, which the earlier audit compared in
the case (n); its definition is for any `χ`, and in the case (+) the paper's identity is again "for
all rows `h`": **SAME**.

#### 3.11 Public helpers of the three files

These are not numbered statements of the paper. Each is a clause of a proof or of the text of
Appendix D.3. Thirteen of the sixteen are not in `STATEMENTS.md` (marked †).

| Lean name | Says | Clause of the paper | Same? |
|---|---|---|---|
| `analyticOnNhd_rmsNorm` | for `ε > 0`, `N_ε` is real-analytic on all `T × d` matrices | "`χ` is … a diffeomorphism" (proof of D.2, tex 904), in part | Same (part) |
| `fderiv_rmsNorm_apply` † | `(𝐃N_ε(h) U)_t = U_t/s_t − (⟨h_t, U_t⟩/d) h_t/s_t³`, `s_t = √(‖h_t‖²/d + ε)` | the derivative behind eq. (14); the paper writes it only for `ε = 0` (tex 910) | Same (I checked the formula by hand) |
| `injective_fderiv_rmsNorm` † | for `ε > 0`, `𝐃N_ε(h)` is injective at every `h` | "So `𝐃χ(h)` is invertible at every `h`" (tex 904) | Same |
| `isOpenMap_rmsNorm` †, `isOpen_dense_preimage_rmsNorm` † | `N_ε` is an open map; the preimage of an open dense set is open and dense | used for "`g_{k+1} ∘ χ` [is a local diffeomorphism] on an open dense set of rows `h`" | Same (part) |
| `analyticOnNhd_suffix_of_analytic`, `analyticOnNhd_suffix_prod_of_analytic`, `analyticOnNhd_block_comp` †, `analyticOnNhd_matrix_mul` †, `differentiable_suffix_prod_of_differentiable` † | for an analytic (differentiable) `χ` and analytic (differentiable) `f_ℓ`, `𝓑_{>k}` is analytic in `h`, and in `(θ, h)` together | "In the cases (n) and (+), every `𝓑_{>k}` is real-analytic on all rows `h`" (tex 897) | Same |
| `fderiv_suffix_last_of_differentiable` † | `𝐃𝓑_{>L}(h) v = (𝐃χ(h) v) D` | "`𝐃𝓑_{>L}(h) v = 𝐃χ(h) v D`" (tex 904) | Same |
| `fderiv_params_suffix_last_eq_mul` † | `𝐃_θ𝓑_{>L}(h) η = χ(h) η_D` | the term `n η_D` in the proof of D.5 (tex 972) | Same |
| `suffix_castSucc_eq_comp_block` †, `fderiv_suffix_castSucc_of_analytic` † | `𝓑_{>ℓ−1} = 𝓑_{>ℓ} ∘ (g_ℓ ∘ χ)` and its chain rule | the displayed chain rule in the proof of D.2 (tex 906) | Same |
| `fderiv_eval_eq_fderiv_suffix_of_analytic` †, `fderiv_eval_eq_fderiv_suffix_rmsNorm` † | `𝐃_θF(θ,x) η = 𝐃𝓑_{>0}(xE)(x η_E) + 𝐃_θ𝓑_{>0}(xE) η` | the display in the proof of D.4 (tex 960) | Same (`η` in the place of `η'`) |

Not stated: that `N_ε` is injective, that its values are exactly the rows of the ball `‖n‖² < d`, and
the formula of its inverse (the last is a private lemma, in one direction). The proof of Lemma D.2
in Lean does not need them.

### 3.B Absorb paper, Proposition 5.1 and Remark A.16

#### 3.12 A Proposition 5.1 (i) with the rate of Remark A.16 (tex 407-411, 852-868, 878-880)

Paper: "Let `F` be a skipless network whose blocks are locally Lipschitz. (i) Without normalization.
The network `F` is a limit of residual networks with blocks of the same kinds and widths, uniformly
on bounded sets of inputs." Appendix A.4: "For `t ≥ 1`, let `F_t` be the residual network with the
embedding `E`, the reads `t^{1−ℓ} W_read^ℓ`, the writes `t^ℓ W_write^ℓ` and the readout `t^{−L} D`."
Remark A.16: "Without normalization, for every bounded set `𝒳` of inputs there is `C` such that
`‖F_t(X) − F(X)‖ ≤ C/t` for all `X ∈ 𝒳` and `t ≥ 1`. … The constants depend on `𝒳` and on `F`."

Lean (`Absorb/Limits.lean:334, 408`), for `(A : Arch T d L) (θ : Params A dIn dOut)`:
```
exists_bound_eval_limitScale : A.χ = id → (∀ ℓ, LocallyLipschitz (A.f ℓ)) →
  ∀ 𝒳 : Set (Matrix T dIn ℝ), Bornology.IsBounded 𝒳 →
    ∃ C : ℝ, ∀ X ∈ 𝒳, ∀ t : ℝ, 1 ≤ t → ‖eval A 1 (θ.limitScale t) X - eval A 0 θ X‖ ≤ C / t
tendstoUniformlyOn_eval_limitScale : (the same hypotheses) →
  TendstoUniformlyOn (fun t X => eval A 1 (θ.limitScale t) X) (fun X => eval A 0 θ X) Filter.atTop 𝒳
```

| Clause | Paper | Lean | Same? |
|---|---|---|---|
| `F` | a skipless network, no normalization | `eval A 0 θ`, `A.χ = id` | Same |
| the residual networks | "with blocks of the same kinds and widths"; in the proof, `F_t` | `eval A 1 (θ.limitScale t)`: the same architecture `A`, the weights of 2.3, identity skips | Same; Lean names the family, the proposition only says that one exists |
| hypothesis | "whose blocks are locally Lipschitz": the maps `B_ℓ`, with their weights | `∀ ℓ, LocallyLipschitz (A.f ℓ)`: the fixed maps `f_ℓ`, on all of their domain | Not the same sentence, see below |
| sets of inputs | bounded | `Bornology.IsBounded 𝒳` | Same |
| rate | `‖F_t(X) − F(X)‖ ≤ C/t` for all `X ∈ 𝒳`, `t ≥ 1`; `C` depends on `𝒳` and `F` | `∃ C, ∀ X ∈ 𝒳, ∀ t ≥ 1, … ≤ C / t`; `C` is chosen after `𝒳` and `θ` | Same |
| limit | uniform on bounded sets | `TendstoUniformlyOn … Filter.atTop 𝒳` for every bounded `𝒳` | Same |
| norm | Frobenius for hidden states (tex 856) | elementwise sup norm | Same statement: "there is `C`" does not depend on the norm |
| depth, tokens | `L ≥ 1` | any `L` (for `L = 0`, `F_t = F`), any finite `T` | Same or more general |

The hypothesis. A block of the paper is `B_ℓ(h) = f_ℓ(h W_read^ℓ) W_write^ℓ` (A eq. (1)). If `f_ℓ` is
locally Lipschitz, so is `B_ℓ` for every choice of weights; the converse fails (for `W_write^ℓ = 0`
the block is `0` whatever `f_ℓ` is). So the Lean hypothesis is formally the stronger one. For the
kinds of block that the paper names after the proposition ("tanh, GELU, ReLU, ReLU², gated and
attention blocks") the two agree, since there `f_ℓ` itself is locally Lipschitz; Lean has no
statement that says so for a named kind (test L1 shows it for tanh). Nothing is lost: the paper's
form, with the hypothesis on the blocks with their weights, follows from the Lean statement by
applying it to the architecture whose fixed maps are these blocks and whose reads and writes are
identity matrices; the scalings of `limitScale` commute with this (test L2, for `d : Type`).

Verdict: **SAME** as Proposition 5.1 (i) with the family of its proof and the rate of Remark A.16;
the hypothesis is put on `f_ℓ`.

#### 3.13 A Proposition 5.1 (ii) with the rate of Remark A.16 (tex 410, 852, 870-876, 878-880)

Paper: "(ii) Under pre-RMSNorm with `ε = 0`. The network `F` is a limit of residual networks with
blocks of the same kinds and widths, uniformly on compact sets of inputs at which `F` is defined."
Appendix: "under pre-RMSNorm with `ε = 0`, let `F_t` keep the embedding, the reads and the readout of
`F` and have the writes `t^ℓ W_write^ℓ`." Proof: "Let `𝒳` be a compact set of inputs at which `F` is
defined, that is, at which no row of `XE` or of a hidden state of `F` vanishes. … For `t ≥ t_0` … no
row of `s_{ℓ−1} + r_{ℓ−1}` vanishes …". Remark A.16: "Under pre-RMSNorm with `ε = 0`, the same holds
for all `t ≥ t_0`, for every compact set `𝒳` of inputs at which `F` is defined, with `t_0` depending
on `𝒳`."

Lean (`Absorb/Limits.lean:420, 554`):
```
exists_bound_eval_writeScale : A.χ = rmsNorm 0 → (∀ ℓ, LocallyLipschitz (A.f ℓ)) →
  ∀ 𝒳 : Set (Matrix T dIn ℝ), IsCompact 𝒳 → (∀ X ∈ 𝒳, DefinedAt A 0 θ X) →
    ∃ C t₀ : ℝ, ∀ X ∈ 𝒳, ∀ t : ℝ, t₀ ≤ t →
      DefinedAt A 1 (θ.writeScale t) X ∧ ‖eval A 1 (θ.writeScale t) X - eval A 0 θ X‖ ≤ C / t
tendstoUniformlyOn_eval_writeScale : (the same hypotheses) →
  TendstoUniformlyOn (fun t X => eval A 1 (θ.writeScale t) X) (fun X => eval A 0 θ X) Filter.atTop 𝒳
```

| Clause | Paper | Lean | Same? |
|---|---|---|---|
| normalization | pre-RMSNorm with `ε = 0`, in `F` and in `F_t` | `A.χ = rmsNorm 0`, the same `A` in both | Same |
| `F_t` | writes `t^ℓ W_write^ℓ`, the rest as in `F` | `θ.writeScale t` (2.3), identity skips | Same |
| sets of inputs | compact, and `F` is defined at every point | `IsCompact 𝒳`, `∀ X ∈ 𝒳, DefinedAt A 0 θ X` (2.4) | Same |
| "`F_t` is defined" | shown in the proof for `t ≥ t_0` | `DefinedAt A 1 (θ.writeScale t) X`, in the conclusion | Same; explicit in Lean |
| rate | `≤ C/t` for `t ≥ t_0`, `t_0` depending on `𝒳` | `∃ C t₀`, chosen after `𝒳` | Same. Lean does not say `t₀ ≥ 1`; since `t₀` is existential this changes nothing |
| limit | uniform on such compact sets | `TendstoUniformlyOn … Filter.atTop 𝒳` | Same, with the remark below |
| hypothesis | "blocks locally Lipschitz" | `∀ ℓ, LocallyLipschitz (A.f ℓ)` | as in 3.12; the paper's form follows (test L3) |

Remark on `rmsRow 0 0 = 0`. In Lean `eval A 1 (θ.writeScale t) X` is a value also at inputs at which
the paper's `F_t` is not defined. `tendstoUniformlyOn_eval_writeScale` alone speaks about this
total function. That it is the paper's `F_t(X)` for `X ∈ 𝒳` and `t ≥ t₀` is the first half of the
conclusion of `exists_bound_eval_writeScale`. The two statements together are the paper's.

Verdict: **SAME** as Proposition 5.1 (ii) with the family of its proof and the rate of Remark A.16.
Remarks 5.2 and 5.3 (the learned scale; `E = D = I`) are not stated.

### 3.C Dimension paper, Definition 3.1 and Proposition 3.3 at one hidden state

#### 3.14 D Definition 3.1 (tex 209-214)

See 2.5. `Params.cobAt` with the eight statements `Params.cobAt_*`: **SAME**.

#### 3.15 D Proposition 3.2 for one hidden state (tex 222-228)

Paper: "Without normalization or under pre-RMSNorm, let `G_0, …, G_L ∈ 𝒢`. The parameters
`(EG_0, {G_{ℓ−1}⁻¹ W_read^ℓ, W_write^ℓ G_ℓ}, G_L⁻¹ D)` give the same function as `θ`, with the hidden
states `h_ℓ G_ℓ`"; proof of 3.3: "a change of basis `G ∈ 𝒢` at `h_ℓ` preserves the function".
Lean (`Symmetry/AtOneState.lean:81, 88`):
```
eval_cobAt_skipless : A.χ = id → ∀ (j : Fin (L + 1)) (x : Matrix T dIn ℝ), eval A 0 (θ.cobAt j G) x = eval A 0 θ x
eval_cobAt_rmsNorm (ε : ℝ) : A.χ = rmsNorm ε → ∀ j, (G : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ →
    ∀ x, eval A 0 (θ.cobAt j G) x = eval A 0 θ x
```
Comparison: this is Proposition 3.2 with `G_j = G` and the identity elsewhere. `𝒢 = GL(d)` without
normalization (`G : GL d ℝ`), `𝒢 = O(d)` under pre-RMSNorm. Any real `ε` is allowed (for `ε = 0` the
statement is true with Lean's `N_0(0) = 0`). Not stated for one hidden state: "with the hidden
states `h_ℓ G_ℓ`" (only `hidden_cob`, for all states at once) and the clause for `ε = 0` with
`G = cQ` (`cobAt` uses the same matrix for the writes and the reads). Verdict: **SAME** as the special
case of Proposition 3.2 that Proposition 3.3 uses.

#### 3.16 D Proposition 3.3 (i) (tex 237-239)

Paper: "Let `d_model` columns of the read of `h_ℓ` (`W_read^{ℓ+1}`, or `D` if `ℓ = L`) form an invertible
matrix `W_1`. (i) Without normalization, the change of basis `G = W_1` at `h_ℓ` preserves the function
and turns `W_1` into `G⁻¹W_1 = I`."
Lean (`Symmetry/AtOneState.lean:105, 117`):
```
cobAt_read_eq_one : A.χ = id → ∀ (ℓ : Fin L) (c : d → A.r ℓ) (W₁ : GL d ℝ),
  (W₁ : Matrix d d ℝ) = (θ.read ℓ).submatrix id c →
    (∀ x : Matrix T dIn ℝ, eval A 0 (θ.cobAt ℓ.castSucc W₁) x = eval A 0 θ x) ∧
      ((θ.cobAt ℓ.castSucc W₁).read ℓ).submatrix id c = 1
cobAt_D_eq_one : A.χ = id → ∀ (cD : d → dOut) (W₁ : GL d ℝ), (W₁ : Matrix d d ℝ) = θ.D.submatrix id cD →
    (∀ x, eval A 0 (θ.cobAt (Fin.last L) W₁) x = eval A 0 θ x) ∧ (θ.cobAt (Fin.last L) W₁).D.submatrix id cD = 1
```

| Clause | Paper | Lean | Same? |
|---|---|---|---|
| one hidden state | `h_ℓ`, `0 ≤ ℓ ≤ L` | `ℓ.castSucc` for a block `ℓ : Fin L` (the states `h_0, …, h_{L−1}`), and `Fin.last L` | Same; all `L+1` states are covered |
| the read of that state | `W_read^{ℓ+1}`, or `D` | `θ.read ℓ` (the Lean block `ℓ` reads `ℓ.castSucc`), or `θ.D` | Same |
| "`d` columns … form an invertible matrix `W_1`" | a choice of columns | `c : d → A.r ℓ` and `W₁ : GL d ℝ` with `W₁ = (θ.read ℓ).submatrix id c`. `c` is any map; an invertible `W₁` forces it to be injective | Same. Equivalent to `IsUnit ((θ.read ℓ).submatrix id c).det` (test A3) |
| hypothesis elsewhere | none | none: the other reads, the writes, `E`, `D` are arbitrary | Same. This is what the simultaneous form of `Symmetry/Reduction.lean` did not have |
| "the change of basis `G = W_1` at `h_ℓ`" | Definition 3.1 | `θ.cobAt ℓ.castSucc W₁` | Same |
| "preserves the function" | for all inputs | `∀ x, eval A 0 … = eval A 0 θ x` | Same |
| "turns `W_1` into `G⁻¹W_1 = I`" | | the chosen columns of the new read are `1` | Same |
| blocks | any (Scope: Section 3 holds for blocks of different kinds) | any `A` with `A.χ = id` | Same |

Verdict: **SAME**.

#### 3.17 D Proposition 3.3 (ii) (tex 240)

Paper: "(ii) Under pre-RMSNorm, let `W_1 = QR` with `Q` orthogonal and `R` upper triangular. The change
of basis `Q` at `h_ℓ` preserves the function and turns `W_1` into `QᵀW_1 = R`." (`W_1` is invertible, by
the first sentence of the proposition.)
Lean (`Symmetry/AtOneState.lean:132, 145`):
```
cobAt_read_eq_of_qr (ε : ℝ) : A.χ = rmsNorm ε → ∀ (ℓ : Fin L) (c : d → A.r ℓ) (Q : GL d ℝ),
  (Q : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ → ∀ R : Matrix d d ℝ,
    (θ.read ℓ).submatrix id c = (Q : Matrix d d ℝ) * R →
      (∀ x, eval A 0 (θ.cobAt ℓ.castSucc Q) x = eval A 0 θ x) ∧
        ((θ.cobAt ℓ.castSucc Q).read ℓ).submatrix id c = R
cobAt_D_eq_of_qr (ε : ℝ) : the same for `θ.D`, `cD : d → dOut` and the hidden state `Fin.last L`
```
Comparison: the factorization `W_1 = QR` is a hypothesis, as in the paper; the conclusion "turns `W_1`
into `R`" is the paper's. Three hypotheses of the paper are absent: `W_1` invertible, `R` upper
triangular, `ε > 0`. With `R` upper triangular the new columns are upper triangular, which is the
paper's statement. That every square matrix has such a factorization is
`exists_orthogonal_transpose_mul_upperTriangular` (`Symmetry/Reduction.lean`, earlier audit); the two
together give "there is an orthogonal `Q` whose change of basis at `h_ℓ` keeps the function and makes
the chosen columns upper triangular" (test A2), which is not a Lean statement of its own for one
hidden state. Verdict: **LEAN STRONGER** (no invertibility, any `R`, any real `ε`).

#### 3.18 D Proposition 3.3, last sentence (tex 241)

Paper: "At generic parameters every hidden state has such columns, and these changes of basis at all
`L + 1` hidden states remove `(L+1) dim 𝒢` parameters: `(L+1)d²` in (i), and `(L+1)d(d−1)/2` in (ii)."
Lean (`Symmetry/AtOneState.lean:228`):
```
ae_exists_isUnit_det_submatrix_cols (μ : Measure (Params A dIn dOut)) [μ.IsAddHaarMeasure] :
  (∀ ℓ, Fintype.card d ≤ Fintype.card (A.r ℓ)) → Fintype.card d ≤ Fintype.card dOut →
    ∀ᵐ θ ∂μ, (∀ ℓ : Fin L, ∃ c : d → A.r ℓ, IsUnit ((θ.read ℓ).submatrix id c).det) ∧
      ∃ cD : d → dOut, IsUnit (θ.D.submatrix id cD).det
```
Comparison:
- "every hidden state has such columns": every read and `D`, that is, the reads of all `L+1` hidden
  states. Same.
- The sentence needs that every read has at least `d` columns and that `d_out ≥ d`; Lean has these
  as hypotheses. In the paper they are part of the Scope (`d_hidden ≥ d`, `d_out ≥ d`), although the
  Scope also says "The reduction of Section 3 needs none of this" (tex 193). For a gated block the
  read has `2 d_hidden` columns, and the Lean hypothesis is on the number of columns of the read.
- With `cobAt_read_eq_one` and `cobAt_D_eq_one` this gives, at generic parameters, a change of basis
  at each hidden state that keeps the function and turns `d` columns of its read into the identity
  (test A4).
- "remove `(L+1) dim 𝒢` parameters": **not stated**. There is no Lean statement that counts the
  entries that become fixed (`card_below_diagonal` counts those of one triangular matrix; that the
  reductions at all hidden states can be made together is in `Symmetry/Reduction.lean`).
Verdict: first half **SAME**; second half **not stated**.

#### 3.19 D rows of a write: the paragraph after Proposition 3.3 (tex 245), its proof (tex 423), Example A.2 (tex 428)

Paper, tex 245: "rows of the matrix `W_write^ℓ` work too, or rows of `E` if `ℓ = 0`: if `d_model` of them
form an invertible matrix `W_1`, the change of basis `G = W_1⁻¹` at `h_ℓ` turns them into `W_1 G = I`."
Proof, tex 423: "For a write, let `W_1ᵀ = QR`; then `W_1 = RᵀQᵀ`, and the change of basis `Q` gives
`W_1 Q = Rᵀ`, which is lower triangular. … At generic parameters every `d_model` columns of a read, and
every `d_model` rows of a write, form an invertible matrix."

Lean (`Symmetry/AtOneState.lean:159, 171, 185, 204, 245`):
```
cobAt_write_eq_one : A.χ = id → ∀ (ℓ : Fin L) (ρ : d → A.w ℓ) (W₁ : GL d ℝ),
  (W₁ : Matrix d d ℝ) = (θ.write ℓ).submatrix ρ id →
    (∀ x, eval A 0 (θ.cobAt ℓ.succ W₁⁻¹) x = eval A 0 θ x) ∧ ((θ.cobAt ℓ.succ W₁⁻¹).write ℓ).submatrix ρ id = 1
cobAt_E_eq_one : the same for `θ.E`, `ρE : d → dIn` and the hidden state `0`
cobAt_write_eq_of_qr (ε : ℝ) : A.χ = rmsNorm ε → ∀ ℓ ρ (Q : GL d ℝ), Q orthogonal → ∀ R,
  ((θ.write ℓ).submatrix ρ id)ᵀ = (Q : Matrix d d ℝ) * R →
    (∀ x, eval A 0 (θ.cobAt ℓ.succ Q) x = eval A 0 θ x) ∧ ((θ.cobAt ℓ.succ Q).write ℓ).submatrix ρ id = Rᵀ
cobAt_E_eq_of_qr (ε : ℝ) : the same for `θ.E` and the hidden state `0`
ae_exists_isUnit_det_submatrix_rows μ : Fintype.card d ≤ Fintype.card dIn →
  (∀ ℓ, Fintype.card d ≤ Fintype.card (A.w ℓ)) →
    ∀ᵐ θ ∂μ, (∃ ρE : d → dIn, IsUnit (θ.E.submatrix ρE id).det) ∧
      ∀ ℓ : Fin L, ∃ ρ : d → A.w ℓ, IsUnit ((θ.write ℓ).submatrix ρ id).det
```
Comparison: the write of the Lean block `ℓ` goes into the hidden state `ℓ.succ` (the paper's
`W_write^{ℓ+1}` into `h_{ℓ+1}`), `E` into `h_0`; the change of basis is `W₁⁻¹` there, and the chosen
rows become `1`. Under pre-RMSNorm: `W_1ᵀ = QR` is the hypothesis, the conclusion is `Rᵀ`; `W_1`
invertible, `R` triangular and `ε > 0` are not assumed. The generic statement is the existence form
of the last sentence of the proof, with the sizes as hypotheses. Verdict: without normalization
**SAME**; under pre-RMSNorm **LEAN STRONGER**; generic **SAME**.

### 3.D Absorb paper, the paper's forms (`Absorb/PaperForms.lean`)

#### 3.20 A Theorem A.4 (tex 513-518) and Theorem A.7 (tex 554-556)

Paper, A.4: "Let `σ = ReLU`, `d_model ≥ 2`, and let the block be nondegenerate. Then (5) has a solution
if and only if `W_read[:,S] W_write[S,:] = −I_{d_model}` for some `S`." A.7: "Let `σ = GELU` and let the
block be nondegenerate. Then (5) has a solution if and only if (6) holds." Equation (5):
`x + σ(xW_read)W_write = σ(xW_read′)W_write′` for all `x ∈ ℝ^{1×d}`, with a block of the same width.
Lean (`Absorb/PaperForms.lean:38, 49`), `{d m : Type*}` finite with decidable equality:
```
relu_absorb_identity_iff (Wr : Matrix d m ℝ) (Ww : Matrix m d ℝ) : Nondegenerate Wr Ww →
  ((∃ (Wr' : Matrix d m ℝ) (Ww' : Matrix m d ℝ),
      ∀ x : d → ℝ, x + vanillaBlock relu Wr Ww x = vanillaBlock relu Wr' Ww' x)
    ↔ ∃ S : Finset m, subProd S Wr Ww = -1)
gelu_absorb_identity_iff : the same with `gelu`
```
Comparison: the same width is the same index type `m`; "for some `S`" is `∃ S : Finset m`;
`subProd S Wr Ww` is `W_read[:,S] W_write[S,:]` and `-1` is `−I` (earlier audit). `Nondegenerate` is
the paper's notion. Lean has no `d ≥ 2` in either statement; the paper has it in A.4 and not in A.7.
Verdict: A.4 **LEAN STRONGER** (`d ≥ 2` dropped); A.7 **SAME**. The further facts of the proofs
(`W_write′ = W_write` for GELU; `|S| ≥ d`) are not stated.

#### 3.21 A Corollary A.10 (tex 595-597)

Paper: "Let `σ` be ReLU or GELU and `d_model ≥ 2`. For generic weights, (5) has no solution, and a
skipless block equals no residual block of the same width." Proof: "Conversely,
`σ(xW_read′)W_write′ = x + σ(xW_read)W_write` says that the block with weights `(W_read′, W_write′)`
absorbs the linear term `−x` … a nondegenerate skipless block is therefore a residual block of the
same width only if `W_read′[:,S] W_write′[S,:] = I` for some `S`, again on a set of measure zero."
Lean (`Absorb/PaperForms.lean:60, 72, 83, 99`), `μ : Measure (Matrix d m ℝ × Matrix m d ℝ)` additive Haar:
```
ae_not_relu_absorb_identity : 2 ≤ Fintype.card d → ∀ μ, ∀ᵐ W ∂μ, ¬ ∃ Wr' Ww',
    ∀ x : d → ℝ, x + vanillaBlock relu W.1 W.2 x = vanillaBlock relu Wr' Ww' x
ae_not_relu_skipless_eq_residual : 2 ≤ Fintype.card d → ∀ μ, ∀ᵐ W ∂μ, ¬ ∃ Wr' Ww',
    ∀ x : d → ℝ, vanillaBlock relu W.1 W.2 x = x + vanillaBlock relu Wr' Ww' x
(and the two with `gelu`)
```
Comparison: first half: generic in the weights `W` of the residual block `x + B(x)`; no block `B′` of
the same width. Second half: generic in the weights `W` of the skipless block; no block `B′` of the
same width with `B(x) = x + B′(x)`. This is the reading of the paper's proof, where the measure-zero
set is in the weights of the skipless block. `B′` is quantified inside the `∀ᵐ`, so the exceptional
set does not depend on it. `d ≥ 2` is kept; the number of hidden units is any. Verdict: **SAME**
(both halves, both activations).

#### 3.22 A Theorem 3.1 (ii), first half, and Proposition A.11 (i) (tex 235-239, 604-608)

Paper, 3.1 (ii): "If `M` is invertible and `W_read` has rank `d_model`, some block `B_θ′` with `d_model`
more hidden units satisfies (2)". A.11: "Let `σ` be ReLU or GELU, let `d_model ≥ 2`, and let `M` be
invertible. (i) If `W_read` has rank `d_model`, a block `B′` of width `m + d_model` satisfies
`xM + B(x) = B′(x)` for all `x`."
Lean (`Absorb/PaperForms.lean:117, 130`):
```
exists_relu_block_add_linear (Wr : Matrix d m ℝ) (Ww : Matrix m d ℝ) : Wr.rank = Fintype.card d →
  ∀ M : Matrix d d ℝ, ∃ (Wr' : Matrix d (m ⊕ d) ℝ) (Ww' : Matrix (m ⊕ d) d ℝ),
    ∀ x : d → ℝ, x ᵥ* M + vanillaBlock relu Wr Ww x = vanillaBlock relu Wr' Ww' x
exists_gelu_block_add_linear : the same with `gelu`
```
Comparison: the width `m + d` is the index type `m ⊕ d`; `x ᵥ* M` is `xM`. `M` is any matrix (the
paper: invertible, and `M ≠ 0` in Theorem 3.1); no `d ≥ 2`. Verdict: **LEAN STRONGER**.

#### 3.23 A Proposition 4.4 (tex 366-368)

Paper: "Let `σ` be ReLU or GELU. Without normalization, a residual network whose reads all have rank
`d_model` equals a skipless network with `d_model` more hidden units in every block." Proof: "…
Composing these blocks, with the same embedding and readout, gives a skipless network that equals
the residual one."
Lean (`Absorb/PaperForms.lean:152, 164`), `{d : Type}`:
```
exists_skipless_eq_residual_relu (θ : Params (Arch.mlp relu id hid) dIn dOut) :
  (∀ ℓ, (θ.read ℓ).rank = Fintype.card d) →
    ∃ θ' : Params (Arch.mlp relu id (fun ℓ => hid ℓ ⊕ d)) dIn dOut, θ'.E = θ.E ∧ θ'.D = θ.D ∧
      ∀ X : Matrix T dIn ℝ, eval (Arch.mlp relu id hid) 1 θ X = eval (Arch.mlp relu id (fun ℓ => hid ℓ ⊕ d)) 0 θ' X
exists_skipless_eq_residual_gelu : the same with `gelu`
```
Comparison: residual `eval … 1 θ`, skipless `eval … 0 θ'`, no normalization (`id`), reads of rank `d`,
widths `hid ℓ ⊕ d`. The conclusion also gives the same `E`, `D` and model dimension, as the paper's
proof does. No Scope hypothesis (`ED ≠ 0`, `d ≥ 2`). Verdict: **LEAN STRONGER**.

#### 3.24 A Theorem 4.1 (i) (tex 328-332) and Corollary A.3 (tex 500-502, proof tex 504)

Paper, 4.1: "Let the residual network have `ED ≠ 0`. (i) Without normalization or with pre-RMSNorm and
`ε > 0`, let the blocks be gated blocks whose gate vanishes at `0` and is differentiable there, or
blocks that are positively homogeneous of degree `k > 1`. No skipless network of blocks of the same
kind, of any depth and widths, equals the residual network." Corollary A.3: "Let every block be as in
Proposition A.1 with `k > 1` or as in Proposition A.2, of any widths. Let `F` be a composition of
residual blocks `h ↦ h + B_ℓ(h)` and `H` a composition of one or more skipless blocks. Then `F ≠ H`.
With embeddings and readouts, the residual network `X ↦ F(XE)D` differs from the skipless network
`X ↦ H(XE′)D′` whenever `ED ≠ 0`, also with pre-RMSNorm and `ε > 0`." Proof: "Each such block maps `0`
to `0` and has Jacobian `0` there, because it is `O(‖x‖^k)` with `k > 1`, respectively `O(‖x‖²)`."

Lean (`Absorb/PaperForms.lean:177-330`). Common to all: `[Nonempty T]`, `{d : Type}`, the skipless
network has `L' + 1` blocks, its own widths and its own model dimension `d'`; the conclusion is
`∃ X : Matrix T dIn ℝ, eval A 1 θ X ≠ eval A' 0 θ' X` for every `θ'`; `hED : θ.E * θ.D ≠ 0`.

(a) Gated blocks:
```
exists_ne_residual_skipless_gated : σ 0 = 0 → DifferentiableAt ℝ σ 0 →
  ∀ (θ : Params (Arch.gated σ id hid) dIn dOut), θ.E * θ.D ≠ 0 →
    ∀ θ' : Params (Arch.gated σ id hid') dIn dOut,
      ∃ X, eval (Arch.gated σ id hid) 1 θ X ≠ eval (Arch.gated σ id hid') 0 θ' X
exists_ne_residual_skipless_gated_rmsNorm {ε} : 0 < ε → (the same with `rmsNorm ε` in both networks)
```
The same gate `σ` in both networks ("blocks of the same kind"), the two hypotheses on the gate are
the paper's, one `ε` for both networks. The residual network may have no block. **SAME.**

(b) Positively homogeneous blocks:
```
flatAtZero_of_homogeneous {A : Arch T d L} {k : ℝ} : 1 < k →
  (∀ ℓ (lam : ℝ) (M : Matrix T (A.r ℓ) ℝ), 0 < lam → A.f ℓ (lam • M) = lam ^ k • A.f ℓ M) →
  (∀ ℓ, ∃ C : ℝ, ∀ M : Matrix T (A.r ℓ) ℝ, ‖M‖ = 1 → ‖A.f ℓ M‖ ≤ C) → A.FlatAtZero
flatAtZero_of_homogeneous_of_continuous : the same with `∀ ℓ, Continuous (A.f ℓ)` in the place of the bound
exists_ne_residual_skipless_homogeneous (A : Arch T d L) (A' : Arch T d' (L' + 1)) :
  A.χ = id → A'.χ = id → ∀ {k k' : ℝ}, 1 < k → 1 < k' →
  (homogeneity of degree k and the bound for every `A.f ℓ`) →
  (homogeneity of degree k' and the bound for every `A'.f ℓ`) →
  ∀ θ : Params A dIn dOut, θ.E * θ.D ≠ 0 → ∀ θ' : Params A' dIn dOut, ∃ X, eval A 1 θ X ≠ eval A' 0 θ' X
exists_ne_residual_skipless_homogeneous_rmsNorm {ε} : 0 < ε → (the same with `A.χ = rmsNorm ε`, `A'.χ = rmsNorm ε`)
```

| Point of the brief | What the Lean statements say | Against the paper |
|---|---|---|
| Is this the class "blocks that are positively homogeneous of degree `k > 1`"? | The fixed map `f_ℓ` of every block is positively homogeneous of one real degree `k > 1` (`lam ^ k` is a real power), for all blocks of the network | For a vanilla or a gated block the block is homogeneous for all weights exactly when its fixed map is, so for the paper's blocks this is the same class. The paper says it of the block |
| the homogeneity is assumed of `f_ℓ` | yes; then the block `h ↦ f_ℓ(hW_read)W_write` is homogeneous for every choice of weights | a block that is homogeneous only for its given weights is not covered; the paper's "kind" of block does not depend on the weights, so nothing of the paper is lost |
| "bounded on the unit sphere" | an added hypothesis on `f_ℓ`: `‖f_ℓ(M)‖ ≤ C` for `‖M‖ = 1`; a continuous `f_ℓ` has it | The paper's statement does not have it; its proof uses it ("it is `O(‖x‖^k)`"). It excludes homogeneous maps that are unbounded on the unit sphere; such a map need not have a derivative at `0` (for example `‖x‖^k g(x/‖x‖)` with `g` unbounded), so `FlatAtZero` cannot be had without it. For a vanilla or gated block with a scalar activation, homogeneity forces `σ(z) = a z^κ` for `z > 0` and `b |z|^κ` for `z < 0` with `κ > 0`, which is continuous, so the bound holds. This last step is my argument; Lean proves the bound for ReLU² and ReGLU directly and has no statement for a general homogeneous activation |
| degrees | `k` for the residual network, `k'` for the skipless one; they may differ, and the two architectures may be of different kinds | the paper: one kind, one `k`. Lean more general |
| one `ε` | `rmsNorm ε` in both networks | Same as the paper |

ReLU² blocks satisfy the hypotheses of the class (test P1), and Theorem 4.1 (i) for ReLU² follows
from the class statement (test P2).

(c) Named kinds: `exists_ne_residual_skipless_swiglu`, `…_geglu`, `…_reluSq`, `…_reglu`, each also
with `_rmsNorm` (`Arch.gated silu`, `Arch.gated gelu`, `Arch.mlp reluSq`, `Arch.gated relu`; the same
kind and, under pre-RMSNorm, the same `ε > 0` in both networks). These are the four kinds that the
paper names (Theorem 3.3: "ReLU² and ReGLU blocks fall under (a), SwiGLU and GeGLU blocks under
(b)"). **SAME.**

Corollary A.3. Its second sentence is Theorem 4.1 (i). It allows every block to be of either class,
so a network may mix gated and homogeneous blocks and blocks of different degrees; the class
statements (a) and (b) do not allow this, and the general statements
`exists_ne_residual_skipless_of_flatAtZero[_rmsNorm]` of `Absorb/Networks.lean` (earlier audit) do. Its
first sentence (compositions without embedding and readout) is the instance `E = D = E′ = D′ = I`
(earlier audit, test U6) and has no statement of its own. Its last sentence (tanh blocks) is
`exists_ne_residual_skipless_tanh` (earlier audit).

Verdict: Theorem 4.1 (i): **SAME** for gated blocks and for the four named kinds; for the class of
homogeneous blocks **SAME for vanilla and gated blocks**, with the hypothesis "bounded on the unit
sphere" added for arbitrary maps `f_ℓ`. Corollary A.3: **PART** in `Absorb/PaperForms.lean` (pure
classes only), complete with the general statements.

### 3.E Skips paper

#### 3.25 S Theorem 3.3 (iii), the readout under pre-RMSNorm (tex 305-310; appendix: Proposition A.9 (ii), tex 700)

Paper: "(iii) In a residual network, let `d_model` columns of one of the reads `W_read^1, …, W_read^L, D`
form an invertible matrix `W_1`. The same change of basis at all hidden states preserves the function
and turns `W_1` into the identity, for `G = W_1` without normalization, and into the upper triangular
`R`, for the factor `Q` of `W_1 = QR` under pre-RMSNorm."
Lean (`Residual/LearnedSkips.lean:190`), `[LinearOrder d]`:
```
exists_cob_residual_D_upperTriangular (ε : ℝ) : A.χ = rmsNorm ε → ∀ cD : d → dOut,
  ∃ Q : GL d ℝ, (Q : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ ∧
    (∀ x : Matrix T dIn ℝ, eval A 1 (θ.cob (fun _ => Q) (fun _ => Q)) x = eval A 1 θ x) ∧
    ((θ.cob (fun _ => Q) (fun _ => Q)).D.submatrix id cD).BlockTriangular id
```

| Clause | Paper | Lean | Same? |
|---|---|---|---|
| network | residual | `eval A 1` | Same |
| "the same change of basis at all hidden states" | one `G` | `θ.cob (fun _ => Q) (fun _ => Q)` | Same |
| columns | `d` columns of `D`, forming an invertible `W_1` | any `cD : d → dOut`; no invertibility | Lean more general |
| under pre-RMSNorm | `ε > 0` (Proposition A.9: "Under RMSNorm with `ε > 0`") | any real `ε` | Lean more general |
| conclusion | for the factor `Q` of `W_1 = QR`: the function is preserved and `W_1` becomes `R`, upper triangular | there is an orthogonal `Q` such that the function is preserved and the chosen columns of the new `D` are upper triangular | Same content; Lean in existential form. The paper's wording, for every factorization `W_1 = QR`, follows from `eval_cob_residual_rmsNorm` (test S1) |

With `exists_cob_residual_read_eq_one`, `exists_cob_residual_D_eq_one` and
`exists_cob_residual_read_upperTriangular` (earlier audit) all four cases of Theorem 3.3 (iii) are now
stated: a read of a block or the readout, without normalization or under pre-RMSNorm.
Verdict: **LEAN STRONGER**. Not stated: the rows of a write in a residual network (Proposition A.9
(ii): "in any read or write of the network"), and Theorem 3.3 (ii).

---------------------------------------------------------------------------------------------------

## (4) Lists

### (4a) Clauses of the paper's statements in scope that have no Lean statement

Dimension paper.
1. Theorem 5.2: "so the network satisfies the equality condition" (Definition 4.4 has no Lean
   definition); and, outside the case audited here, (i) for `ε = 0`, (ii) and (iii).
2. Claim `(D_k)`: its form for gated blocks (eq. (19)) and for the case (0) (eq. (18)); the paragraph
   "Conversely, every `Z = Z_k ∈ 𝔤` and `η` of the form (17) satisfy (16)" (tex 947-951) for a general
   `k` (for `k = 0` and the whole network it is `cobDir_mem_flat_skipless_rmsNorm`).
3. Eq. (14) in the case (0), and eq. (15).
4. Proposition D.4 for gated blocks ("with no vanishing value column", the directions `η^{Z,Δ}`);
   Lemmas D.2, D.3, D.5 and Proposition D.4 in the case (0); condition (R2).
5. Proof of Lemma D.2: "`χ` is … a diffeomorphism of `ℝ^{1×d}` onto the ball of the rows `n` with
   `‖n‖² < d`, with the inverse `n ↦ √ε n (1 − ‖n‖²/d)^{−1/2}`". Stated are: `N_ε` is real-analytic, its
   derivative is injective at every point, it is an open map. Not stated: `N_ε` is injective, its
   values are exactly the rows of the ball (eq. (22) names this set), the inverse.
6. Proposition 3.2 for one hidden state: the clause "with the hidden states `h_ℓ G_ℓ`", and the
   clause for `ε = 0` with `G = cQ`.
7. Proposition 3.3: "these changes of basis at all `L + 1` hidden states remove `(L+1) dim 𝒢`
   parameters: `(L+1)d²` in (i), and `(L+1)d(d−1)/2` in (ii)", and the sentence of the proof "The
   identity fixes all `d²` entries of `W_1`, and the triangular form fixes the `d(d−1)/2` entries on
   one side of its diagonal".
8. Proposition 3.3 (ii) for one hidden state as one statement with the factorization inside ("there
   is an orthogonal `Q` …"): it follows from two Lean statements (test A2) and is not a statement.

Absorb paper.
9. Proposition 5.1 with the hypothesis on the blocks with their weights: it follows from the Lean
   statements (tests L2, L3) and is not a statement. No statement says that a named kind of block
   (tanh, GELU, ReLU, ReLU², gated) satisfies the Lean hypothesis; attention blocks are not defined
   in Lean. Remarks 5.2 and 5.3. The recursion (11) for `r_ℓ`, "the hidden states of `F_t` are
   `t^ℓ(s_ℓ + r_ℓ)`" and the constants `C_ℓ`, `t_0` of the proof are inside the Lean proofs only.
10. Theorem 4.1 (i): no statement shows that a vanilla or gated block with a positively homogeneous
    activation satisfies the hypotheses of the class statement (it is shown for ReLU² and ReGLU,
    through `FlatAtZero` directly). Corollary A.3: networks that mix the two classes or several
    degrees are covered only by the general statements of `Absorb/Networks.lean`; its first sentence
    (compositions without embedding and readout) has no statement of its own.
11. Theorem 3.1 (ii), "exactly `d_model` units": two statements, one for each half (earlier audit).

Skips paper.
12. Theorem 3.3 (ii) (the dimensions of the groups). Proposition A.9 (ii) for the rows of a write in
    a residual network (the main-text Theorem 3.3 (iii) speaks of reads only, and is now complete).

### (4b) Rows and notes of `STATEMENTS.md` that are inaccurate or incomplete

Line numbers are those of `/home/claude/lw/lean/STATEMENTS.md` at commit 1e1c5ed.

1. Line 278, row "A Proposition 5.1 (i) … no normalization, locally Lipschitz blocks": the Lean
   hypothesis is `∀ ℓ, LocallyLipschitz (A.f ℓ)`, on the fixed maps `f_ℓ`, not on the blocks. Line 279,
   the row for (ii), does not name the hypothesis at all.
2. Lines 177-181, note on Appendix D: "D.3, D.5 and D.7 fail for none". D.3 and D.5 fail with no
   tokens. D.7 does not: with no tokens and a regular `θ` its hypothesis `(D_{k+1})` is false (for
   nonempty `d`), so the implication holds (tests S2, S3). `[Nonempty T]` is used by the Lean proof of
   D.7, and it is needed for D.3, D.4, D.5 and for the theorem.
3. Lines 182-183, note "Theorem 5.2 (i) without normalization: the proof uses `d ≥ 1` only": the same
   is true under pre-RMSNorm (test D2). Neither the note nor line 146 says so.
4. Line 271, row "A Theorem A.4 (ReLU) and Theorem A.7 (GELU) … (the instance `M = I`; `d ≥ 2` is not
   used)": the paper's Theorem A.7 has no hypothesis `d ≥ 2`; the remark applies to Theorem A.4 only.
5. Line 141, row "D eq. (14)": the Lean statement is for `ε > 0`. The paper's eq. (14) is for the
   cases (+) and (0); the row does not say that the case (0) is not stated.
6. The index does not list 20 public names of the files in scope. Of `Depth/SuffixRMS.lean` and
   `Depth/StepTanhRMS.lean`: `analyticOnNhd_matrix_mul`, `fderiv_rmsNorm_apply`,
   `injective_fderiv_rmsNorm`, `isOpenMap_rmsNorm`, `isOpen_dense_preimage_rmsNorm`,
   `fderiv_suffix_last_of_differentiable`, `fderiv_params_suffix_last_eq_mul`,
   `suffix_castSucc_eq_comp_block`, `analyticOnNhd_block_comp`, `fderiv_suffix_castSucc_of_analytic`,
   `fderiv_eval_eq_fderiv_suffix_of_analytic`, `fderiv_eval_eq_fderiv_suffix_rmsNorm`,
   `differentiable_suffix_prod_of_differentiable` (line 134 lists the chain rules of the case (n)
   only). Of `Absorb/Limits.lean`: `norm_mul_norm_inv_smul_sub_le`, `norm_mul_norm_rmsRow_zero_sub_le`,
   `rmsNorm_zero_smul`, `norm_rmsNorm_zero_sub_le`, `norm_rmsNorm_zero_le`, `norm_mul_le_card`,
   `lipschitzWith_mul_right` (among them the inequality of the proof of 5.1 (ii),
   `‖N(y′) − N(y)‖ ≤ 2√d ‖y′ − y‖/‖y‖`, in Lean with sup norms and the constant `2d`).

Smaller points, not errors.
- Lines 13-20 say that the files of this audit are "not yet compared by such a reader". They have
  now been compared.
- Lines 137-140 and 143-145 name the lemma and the case only ("D Lemma D.2, case (+)"); the
  hypotheses (real-analytic `f_ℓ`, regular `θ`, at least one token) are those of the rows for the
  case (n) and are not repeated.
- Line 276 and the note of lines 284-290 are accurate. They do not say that the class statement
  takes one degree `k` for all blocks of the residual network and allows another degree `k'` in
  the skipless one.

Rows that I compared and found accurate: line 32 (Definition 3.1), lines 61-65 (Propositions 3.2 and
3.3 at one hidden state, the rows, the generic clauses), 132, 135-140, 142-146, 216, 272-277, and the
notes of lines 151-157, 196-199, 284-290 and 313-315. The lists "not stated yet" (lines 200-204,
228-232, 316-318) agree with what I found for the statements in scope.

---------------------------------------------------------------------------------------------------

## (5) What the authors should know, most serious first

**False, vacuous or changed in meaning.** Nothing. In the 91 public names of the scope I found no
statement that is false, none that is vacuous, and no definition that changes the meaning of a
statement of the papers. The six new definitions (`ClaimRMS`, `tangentRMS`, `Params.limitScale`,
`Params.writeScale`, `DefinedAt`, `Params.cobAt`) are the paper's objects. All 91 names depend only
on `propext`, `Classical.choice`, `Quot.sound`.

**Differences of form.**
1. Proposition 5.1 (A): Lean assumes that the fixed maps `f_ℓ` are locally Lipschitz; the paper
   assumes it of the blocks. The Lean hypothesis is formally the stronger one. The paper's form
   follows from the Lean statements (tests L2, L3), so nothing is lost, but `STATEMENTS.md` words the
   hypothesis as the paper does (4b, item 1). Lean states the family `F_t` of the proof and the
   rate `C/t` of Remark A.16, which is more than the proposition says by itself.
2. Theorem 4.1 (i) (A), the class "positively homogeneous of degree `k > 1`": Lean assumes the
   homogeneity of the fixed map `f_ℓ`, and in addition that `f_ℓ` is bounded on the unit sphere. The
   paper's statement has no such condition; its proof of Corollary A.3 uses it in the words "it is
   `O(‖x‖^k)`". For vanilla and gated blocks the condition holds by itself, so the paper's theorem is
   not affected. A positively homogeneous map that is unbounded on the unit sphere need not have a
   derivative at `0`, so the proof does not cover such maps; if the paper means the class in that
   generality, the statement needs "continuous" or the bound.
3. Proposition 3.3 (D), "At generic parameters every hidden state has such columns": the Lean
   statement assumes at least `d` columns in every read and `d_out ≥ d`. The sentence needs this. The
   paper's Scope has `d_hidden ≥ d` and `d_out ≥ d`, and also says that the reduction of Section 3
   "needs none of this"; for this one sentence the sizes are needed.
4. Appendix D (D): Lean keeps hidden states with the rows `T`; the paper takes one token. For one
   token the Lean statements are the paper's. For the statements about a general architecture the
   Lean versions are about more maps than the paper's.
5. Proposition D.4 (D): Lean states "`fd = P − (L+1) d(d−1)/2`" and "every flat direction is a
   direction of antisymmetric changes of basis"; the paper states the set of the flat directions
   and "rank (13) on some finite batch". The two agree, with `cobDir_mem_flat_skipless_rmsNorm` for
   the other inclusion (test D6).
6. Proposition 5.1 (ii) (A): that `F_t` is defined on the compact set for `t ≥ t_0` is part of
   `exists_bound_eval_writeScale`. `tendstoUniformlyOn_eval_writeScale` alone is about Lean's total
   function (`N_0(0) = 0`).
7. Theorem 3.3 (iii) (S), readout under pre-RMSNorm, and Proposition 3.3 (ii) (D): the paper says
   "for the factor `Q` of `W_1 = QR`". The skips statement is "there is an orthogonal `Q`"; the
   dimension statements take the factorization as a hypothesis and leave its existence to
   `exists_orthogonal_transpose_mul_upperTriangular`. Each form gives the other (tests S1, A2).

**Hypotheses that Lean shows unnecessary.**
- Theorem 5.2 (i) under pre-RMSNorm (D): `d ≥ 2`. The proof uses `d ≥ 1` (test D2). The Lean
  statement keeps the paper's `d ≥ 2`.
- Proposition 3.3 (ii) and the rows of a write under pre-RMSNorm (D), Theorem 3.3 (iii) under
  pre-RMSNorm (S): that `W_1` is invertible, and `ε > 0` (the statements are algebraic identities for
  every real `ε`). In the one-state statements of the dimension paper also that `R` is triangular.
- Theorem A.4 (A): `d ≥ 2`. (Theorem A.7 does not assume it in the paper.)
- Theorem 3.1 (ii), first half, and Proposition A.11 (i) (A): that `M` is invertible, and `d ≥ 2`.
- Proposition 4.4 (A): the Scope (`ED ≠ 0`, `d ≥ 2`).

**Hypotheses that are needed, shown by a test.**
- Lemma D.5 in the case (+): the hypothesis on `D`. With `D = 0` the claim `(D_L)` fails (test D4).
  In the case (n) the Lean statement has no hypothesis on `D`.
- At least one token, for Lemmas D.3, D.5, Proposition D.4 and the theorem (test D3 and the earlier
  audit). Lemma D.7 does not need it for its truth (test S3).

**Not stated.** See (4a). For the statements in scope the main ones are: the count "remove
`(L+1) dim 𝒢` parameters" of Proposition 3.3; the clause "the equality condition" of Theorem 5.2;
Remarks 5.2 and 5.3 of the absorb paper; Theorem 3.3 (ii) of the skips paper.

**`STATEMENTS.md`.** Six places are imprecise or incomplete, see (4b): the hypothesis of
Proposition 5.1; the note that Lemma D.7 fails with no tokens; the note on `d ≥ 1`; the remark on
`d ≥ 2` for Theorem A.7; the row for eq. (14); 20 public names that the index does not list.

**What was checked by machine.**
- `#print axioms` on all 91 public names: only the three standard axioms.
- `#check @name` on all 91 names; the statements quoted in section (3) are the elaborated ones.
- 25 tests that compile against the library (section 2.8): the theorem at concrete sizes and with
  `d ≥ 1`; the failures with no tokens and with `D = 0`; the paper's form of Proposition 5.1 from the
  Lean form; Definition 3.1 on two blocks; Proposition 3.3 (ii) with the factorization inside; the
  class of homogeneous blocks on ReLU²; the wording of Theorem 3.3 (iii).
- The library was not rebuilt. The checks ran against the compiled files, which are newer than the
  sources of the seven files in scope; the working tree is clean at commit 1e1c5ed.

**What was not checked by machine.**
- The comparison itself: it is a reading of the papers against the elaborated statements.
- That for MLP blocks and at least one token the identity (16) for all `T × d` matrices is the
  identity for all rows (2.7).
- That `DefinedAt` holds exactly at the inputs at which the paper's network is defined (the
  induction of 2.4).
- That a vanilla or gated block with a positively homogeneous activation is bounded on the unit
  sphere, and that the bound cannot be dropped from `flatAtZero_of_homogeneous` (3.24).
- The formula of `fderiv_rmsNorm_apply` against the derivative of `N_ε`, which I checked by hand.
- With empty `d` the statements were not tested; all matrices are then empty.

---------------------------------------------------------------------------------------------------

## (6) Count

- Paper statements, definitions and equations compared: 39. Dimension paper, Appendix D and
  Theorem 5.2 (i): 15 (Theorem 5.2 (i) in the case (+); the first paragraph of the proof in D.7;
  Claim `(D_k)`; eqs. (14), (16), (20), (21), (22); Lemmas D.2, D.3, D.5, D.6, D.7; Proposition D.4;
  "the fact"). Absorb paper, Section 5: 6 (Proposition 5.1 (i), (ii); Remark A.16; the two families
  `F_t`; "defined at"). Dimension paper, Section 3: 9 (Definition 3.1; Proposition 3.2 at one hidden
  state; Proposition 3.3 (i), (ii), the two halves of its last sentence; the paragraph after it; the
  two sentences of its proof on the rows). Absorb paper, the paper's forms: 8 (Theorems A.4, A.7;
  Corollary A.10; Theorem 3.1 (ii) first half; Proposition A.11 (i); Proposition 4.4; Theorem 4.1 (i);
  Corollary A.3). Skips paper: 1 (Theorem 3.3 (iii), readout under pre-RMSNorm). In addition, 7
  clauses of proofs of Appendix D that public helpers state (3.11).
- Lean names compared: 91 public names (6 definitions and 85 theorems): 21 of
  `Depth/SuffixRMS.lean`, 7 of `Depth/StepTanhRMS.lean`, 3 of `Depth/TanhRMS.lean`, 14 of
  `Absorb/Limits.lean`, 21 of `Symmetry/AtOneState.lean`, 24 of `Absorb/PaperForms.lean`, 1 of
  `Residual/LearnedSkips.lean`.
- Verdicts by paper statement (summary table, 35 rows): SAME 26 (one of them "SAME for vanilla and
  gated blocks, with an added hypothesis for arbitrary maps"), LEAN STRONGER 6, PART 1, not stated 1,
  and 1 row of helper statements (SAME). No row is LEAN WEAKER or DIFFERENT.
- Rows of `STATEMENTS.md` compared: 29 rows and 12 notes or paragraphs; 6 places imprecise or
  incomplete.
- Tests: 25, all compile; `#print axioms`: 91 names, no axiom beyond the three standard ones.
