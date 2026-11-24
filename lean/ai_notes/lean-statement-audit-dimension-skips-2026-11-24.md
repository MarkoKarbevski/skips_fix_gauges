STATUS: complete

# Audit of the Lean statements against the dimension paper and the skips paper (2026-11-24)

Auditor: an independent agent that did not write the Lean statements. Read-only: no file of the
repository was changed. Papers: `/home/claude/lw/paper docs/new_paper_functional_dimension/new_paper_functional_dimension.tex`
("D", line numbers below are of this file; statement numbers are those of the PDF, read with
`pdftotext -layout`) and `/home/claude/lw/paper docs/new_paper_skips_gain/new_paper_skips_gain.tex`
("S"). Lean library: `/home/claude/lw/lean/SkipsLean/` (file names below are relative to it).
`STATEMENTS.md` was used only as an index. Verdicts: SAME, LEAN STRONGER, LEAN WEAKER, DIFFERENT,
PART (as defined in the task). Sections: (1) summary table, (2) definitions, (3) one entry per statement, (4) lists,
(5) what the authors should know.

Scratch files of the audit (the `#check`/`#print` runs and their outputs) are in `/home/claude/audit_dim/`.

---------------------------------------------------------------------------------------------------

## (1) Summary table

Scope: every row of the sections "Definitions", "Dimension paper" and "Skips paper" of
`STATEMENTS.md` (100 rows: 7 + 76 + 17, all with the status "proved" or "defined"; 221 Lean names).
The rows are grouped below by the paper's statement. "PART" lists what is stated and what is not.

### Definitions

| Paper | Lean names | Verdict | The difference in one line |
|---|---|---|---|
| D/S Section 2: blocks, networks, `F_θ`, eqs. (1), (2) | `Arch`, `Params`, `hidden`, `eval`, `Arch.mlp`, `Arch.gated` | SAME | Lean: arbitrary `f_ℓ` and `χ`; stream matrices `0`/`1`/learned. No attention block exists in Lean. |
| D/S Section 2: RMSNorm `N_ε` | `rmsRow`, `rmsNorm` | SAME for `ε > 0` | Lean: `N_0(0) = 0` (paper: undefined); any real `ε` is allowed. |
| D/S Definition 3.1 (change of basis) | `Params.cob`, `cobSkip` | DIFFERENT object, on purpose | All `L+1` hidden states at once, and two families (`G` on writes, `K` on reads). With `K = G` it is the tuple of Proposition 3.2. |
| D `θ ∈ ℝ^P` | `Params` as a normed space, `Module.finrank ℝ (Params …)` | SAME | `P` only as `finrank` (I checked that it equals the number of entries). |
| D/S Definition 4.1 (functional dimension, redundancy) | `evalBatch`, `jacobianRank`, `funDim`, `redundancy` | SAME | `fderiv` is `0` where not differentiable; not used by any result in scope. |
| D "generic parameters" | `∀ᵐ θ ∂μ`, `μ` any additive Haar measure | SAME | — |
| D Appendix C: flat directions, `fd = P − dim 𝒦(θ)` | `flat`, `funDim_add_finrank_flat`, `mem_flat_of_hasDerivAt`, `funDim_add_finrank_le_of_le_flat` | SAME | Under differentiability at every input (`hdiff`). |
| D directions of the symmetries (Step 1; eq. (11), (12)) | `cobDir`, `rescaleDir` | SAME | Only changes of basis and value rescalings of gated units. |
| Activations | `Real.tanh`, `gelu`, `geluDeriv`, `silu`, `siluDeriv`, `relu`, `reluSq`, … | SAME | Exact GELU `zΦ(z)`. |
| D Appendix D: `𝓑_{>k}`, identity (16), Claim `(D_k)`, regular, `𝓛` (21), conditions of the proof | `suffix`, `SuffixFlat`, `Claim`, `Regular`, `blockLHS`, `TanhDepthGeneric` | SAME in the case (n) | Hidden states are `T × d` matrices (paper: rows). Cases (+), (0) and gated blocks not defined. |
| S eq. (7) | `skipProd`, `skipProd_last`, `skipProd_castSucc` | SAME | — |

### Dimension paper

| Paper | Lean names | Verdict | The difference in one line |
|---|---|---|---|
| Proposition 3.2 | `eval_cob`, `eval_cob_skipless`, `eval_cob_rmsNorm`, `eval_cob_rmsNorm_zero` (+ `hidden_cob`) | SAME | Lean a little stronger (any `f_ℓ`, any real `ε`). The clause "hidden states `h_ℓ G_ℓ`" is `hidden_cob`, not in the index. |
| Proposition 3.3 (i) | `exists_cob_reads_eq_one` | LEAN WEAKER | Simultaneous form: needs invertible columns in every read and in `D`; the one-hidden-state form of the paper is not stated. |
| Proposition 3.3 (ii) | `exists_cob_reads_upperTriangular`, `exists_orthogonal_transpose_mul_upperTriangular` | LEAN STRONGER | Simultaneous form; no invertibility; any `ε`. |
| after 3.3 / Example A.2 (rows of a write) | `exists_cob_writes_eq_one` | SAME (simultaneous form) | Without normalization only; the triangular form for rows under pre-RMSNorm is not stated. |
| Proposition 3.3, last sentence | `ae_isUnit_det_submatrix`, `card_below_diagonal` | PART | The sentence of the proof ("every `d` columns …"), not existence; the count of removed parameters is not stated. |
| Appendix A.3 (ViT-B count) | `vitB_count` | SAME | Arithmetic only. |
| Lemma A.1 | `rmsNorm_mul_orthogonal`, `rmsNorm_zero_mul_smul_orthogonal`, `orthogonal_of_rmsRow_vecMul`, `conformal_of_rmsRow_zero_vecMul` | SAME | Split into four statements. |
| Proposition A.3 | `centering_mul_centering`, `sum_vecMul_centering`, `vecMul_centering_of_sum_eq_zero`, `rmsRow_vecMul_transpose_of_orthonormal` | PART | Only the computations of the proof; no LayerNorm network. |
| Appendix B (symmetries inside blocks) | `eval_rescale`, `rescaleDir_mem_flat`, `rescaleDir_mem_flat_of_differentiable` | PART | Value rescalings of gated units only (SAME); ReLU, ReLU², ReGLU gate, attention missing. |
| Lemma B.1 | `cobDir_injective`, `cobDir_add_rescaleDir_injective`, `ae_rank_E_write`, `ae_value_ne_zero` | DIFFERENT in form, PART | Infinitesimal form (the differential of the action is injective); changes of basis and value rescalings only. |
| Theorem 4.3 | `funDim_add_le_skipless`, `funDim_add_le_skipless_rmsNorm`, `ae_funDim_add_le_skipless`, `ae_funDim_add_le_skipless_rmsNorm`, `funDim_add_le_skipless_gated`, `funDim_add_le_skipless_gated_rmsNorm`, `ae_funDim_add_le_skipless_gated`, `ae_funDim_add_le_skipless_gated_rmsNorm`, `cobDir_mem_flat_skipless`, `cobDir_mem_flat_skipless_rmsNorm`, `finrank_antisymmetric`, `differentiable_rmsNorm` | PART | `tanh`, GELU, SwiGLU, GeGLU, cases (n), (+): SAME with fewer hypotheses (no `d_out ≥ d`, no `d ≥ 2`). ReLU²: no `s`. ReLU, ReGLU, attention, `ε = 0`: missing. |
| Lemma C.2 | `keeps_products_iff_mem_range_cobDir` | SAME | "`X`, `Y` determined; dimension `2d²`" is in `cobDir_injective` and inside the one-block theorems. |
| Lemma C.3 | `tanh_units_flat_eq_zero`, `gelu_units_flat_eq_zero`, `relu_units_flat`, `reluSq_units_flat`, `relu_gated_units_flat`, `silu_gated_units_flat`, `gelu_gated_units_flat` (+ `…_of_value_ne_zero`) | SAME (all seven kinds) | SwiGLU, GeGLU also without the hypothesis on proportionality (LEAN STRONGER). |
| Theorem 5.1 / C.1 | `ae_funDim_tanh_oneBlock`, `ae_funDim_gelu_oneBlock`, `ae_funDim_swiglu_oneBlock`, `ae_funDim_geglu_oneBlock` (+ `funDim_*_oneBlock`, `OneBlockGeneric(Gated)`, `ae_oneBlockGeneric(Gated)`, `funDim_mlp_oneBlock`, `funDim_gated_oneBlock`, …) | PART | 4 of 8 kinds, each SAME. ReLU, ReLU², ReGLU, attention missing. |
| **Theorem 5.2** | `ae_funDim_tanh_skipless`, `funDim_tanh_skipless`, `TanhDepthGeneric`, `ae_tanhDepthGeneric`, `regular_of_tanhDepthGeneric`, `claim_of_tanhDepthGeneric` | PART | 1 of 7 cases: (i) `tanh` without normalization, SAME. (i) `ε > 0`, `ε = 0`, (ii), (iii) missing. |
| Lemma D.1 | `tanh_ray_separation`, `tanh_ray_separation_matrix`, `eventually_eq_zero_of_sum_pow_mul_exp_ray` | SAME | Any normed target space. |
| Lemma D.2 | `exists_open_dense_injective_fderiv_suffix` | PART | Case (n) only; there SAME (any analytic blocks). |
| Lemma D.3 | `suffixFlat_of_flat_at_write` | PART | Case (n) only; there SAME. |
| Proposition D.4 | `flat_le_range_cobDir_of_claim`, `funDim_of_claim` | PART | Case (n), no gated blocks; there SAME. |
| Lemma D.5 | `claim_last` | PART, LEAN STRONGER | Case (n) only; no hypothesis on the rank of `D`. |
| eqs. (20)-(22), Lemma D.6 | `blockLHS`, `suffixFlat_castSucc_iff_mlp` | PART | Case (n); the case (+) of Lemma D.6 missing. |
| Lemma D.7 | `claim_castSucc_tanh`, `dense_setOf_linearIndependent_mul`, `eq_zero_of_fderiv_suffix_one_sub_sq` | PART | Case (n) only; there SAME. |
| proof of Theorem 5.2, conditions | `TanhDepthGeneric`, `ae_tanhDepthGeneric`, `regular_of_tanhDepthGeneric` | SAME | Stated for every `χ`. |
| helper rows (GELU, Gaussian tail, analyticity, chain rules, zero sets) | `gelu_expansion_*`, `le_one_sub_gaussCdf`, `measure_zeroSet_of_analytic`, … | SAME / LEAN STRONGER | Explicit bounds where the paper has `O(·)`. |

### Skips paper

| Paper | Lean names | Verdict | The difference in one line |
|---|---|---|---|
| eq. (6) | `eval_cob`, `hidden_cob`, `cobSkip` | SAME | For any `χ` with `χ(hG) = χ(h)K`. |
| Theorem 3.2 (i) | `eval_learned_eq_residual`, `cob_skipProd_D` | SAME | — |
| Theorem 3.2 (ii) | `eval_learned_eq_residual_rmsNorm`, `exists_cob_learned_upperTriangular`, `exists_orthogonal_mul_upperTriangular` | SAME / LEAN STRONGER | Second sentence without invertibility of the skips; any real `ε`. |
| Theorem 3.3 (i) | `eval_cob_residual`, `eval_cob_residual_rmsNorm`, `cob_eq_of_eval_cob_residual`, `eval_cob_residual_iff`, `cob_eq_orthogonal_of_eval_cob_residual_rmsNorm`, `eval_cob_residual_rmsNorm_iff` | SAME | The hypothesis of Theorem A.5 (iii) ("every block nonzero") is explicit; no `d ≥ 2`. |
| Theorem 3.3 (ii) | none | not stated | — |
| Theorem 3.3 (iii) | `exists_cob_residual_read_eq_one`, `exists_cob_residual_D_eq_one`, `exists_cob_residual_read_upperTriangular` | PART | The readout `D` under pre-RMSNorm is missing. |
| Theorem 4.2 (identity skips) | `funDim_add_le_residual`, `funDim_add_le_residual_rmsNorm`, `ae_funDim_add_le_residual`, `ae_funDim_add_le_residual_rmsNorm`, `cobDir_const_mem_flat_residual`, `rescaleDir_mem_flat_stream` | PART | Bound without `s` only (`fd ≤ P − dim 𝒢`); needs only `d_in ≥ d`. |
| Theorem 4.6 (i) / B.1 (i) | `ae_funDim_tanh_oneBlock_residual_eq_add`, `ae_funDim_gelu_oneBlock_residual_eq_add`, `ae_funDim_swiglu_oneBlock_residual_eq_add`, `ae_funDim_geglu_oneBlock_residual_eq_add`, `ae_funDim_mlp_oneBlock_residual(_eq_add)`, `ae_funDim_gated_oneBlock_residual(_eq_add)`, `funDim_*_oneBlock_residual`, `flat_le_*_residual` | PART | 4 of 8 kinds, without biases, each SAME. (ii) and B.1 (ii)-(v) missing. |
| Lemma B.2 | `keeps_products_iff_mem_range_cobDir` (+ a private helper for `M`) | PART | The clause "keeps `M` iff `X = Y`" is only a private lemma, one direction. |


---------------------------------------------------------------------------------------------------

## (2) Definitions, clause by clause

### 2.1 Networks: D Section 2 (tex 175-193), S Section 2 (tex 213-232) against `Network/Defs.lean`, `Network/Blocks.lean`

| Clause of the paper | Lean | Same? |
|---|---|---|
| "A hidden state is a matrix `h ∈ ℝ^{T×d_model}` whose rows are the `T` tokens" (D tex 175) | `Matrix T d ℝ`, `T` and `d` arbitrary types (`Type*`), finite where a statement needs it | Same. `T` and `d` may be empty in Lean; see 2.10. |
| Block: `g(n) = f(n W_read) W_write`, applied to `χ(h)` (D eq. (1)) | `Network/Defs.lean:58`: `A.f ℓ (A.χ h * θ.read ℓ) * θ.write ℓ` | Same. Tokens are rows, weights multiply on the right. |
| "`f` applies an activation to every hidden unit of every token" (MLP block) | `Arch.mlp` (`Network/Blocks.lean:20-25`): `r := hid`, `w := hid`, `f _ M := M.map σ` | Same. The read is `Matrix d (hid ℓ) ℝ` (`d × d_hidden`), the write `Matrix (hid ℓ) d ℝ`. |
| Gated block: read `[W_g, W_v]` (two `d × d_hidden` matrices side by side), `f` maps gate `z_i` and value `w_i` to `σ(z_i) w_i` | `Arch.gated` (`Network/Blocks.lean:31-36`): `r ℓ := hid ℓ ⊕ hid ℓ`, `f _ M := of fun t i => σ (M t (inl i)) * M t (inr i)` | Same. Gate columns are `Sum.inl i`, value columns `Sum.inr i`. |
| Attention block | none | **Not defined in Lean.** No statement on attention blocks exists. |
| ReLU, ReLU² blocks, ReGLU | the activations `relu`, `reluSq` exist (`Activations/ReLU.lean`), and `Arch.mlp relu …`, `Arch.gated relu …` can be formed | Can be formed, but the sections in scope state no theorem on such a network (only Lemma C.3 for the hidden units). |
| `h_0 = xE`, `h_ℓ = g_ℓ(χ(h_{ℓ-1}))`, `y = χ(h_L) D` (D eq. (2)) | `hidden A M θ x : Fin (L+1) → Matrix T d ℝ` by `Fin.induction` from `x * θ.E`, step `h ↦ h * M ℓ + A.f ℓ (A.χ h * θ.read ℓ) * θ.write ℓ`; `eval A M θ x = A.χ (hidden A M θ x (Fin.last L)) * θ.D` (`Network/Defs.lean:55-63`) | Same for `M = 0`. `χ` is applied before the readout, as in the paper ("the readout applies the same map χ as the blocks"). |
| Skips: `h_ℓ = h_{ℓ-1} A_ℓ + B_ℓ(χ(h_{ℓ-1}))`, `A_ℓ = 0`, `I` or learned (S eq. (2)) | the stream matrices `M : Fin L → Matrix d d ℝ` of `hidden`/`eval`; `0`, `1`, or `fun ℓ => (S ℓ : Matrix d d ℝ)` | Same. Under pre-RMSNorm "the skips read `h` itself" (S tex 229): in Lean the stream term is `h * M ℓ`, not `χ h * M ℓ`. Same. |
| Index shift | Lean block `ℓ : Fin L` (0,…,L−1) is the paper's block `ℓ+1`; Lean hidden state `j : Fin (L+1)` is the paper's `h_j`. Block `ℓ` reads `h_{ℓ.castSucc}` and writes `h_{ℓ.succ}`. | Checked in every statement below; no off-by-one found. |
| `θ = (E, W_read^1, W_write^1, …, D) ∈ ℝ^P` | `Params A dIn dOut` (structure with `E`, `read`, `write`, `D`), with the vector-space structure of the product of its components (`Dimension/Space.lean`); `P` is `Module.finrank ℝ (Params A dIn dOut)` | Same. No Lean statement writes `P` as the number of entries, `d_in·d + Σ_ℓ (d·#(r ℓ) + #(w ℓ)·d) + d·d_out`; all theorems use `finrank`. That the two agree is not a stated lemma; I proved it in a scratch file from `Params.linearEquivProd` (`/home/claude/audit_dim/Check2.lean`, example (b), compiles). |
| "The constant ε is fixed and is not a parameter"; a learned gain is absorbed in the read | `ε` is a parameter of `rmsNorm`, not of `Params`; no gain | Same. |
| "Networks have no biases" (Scope) | no biases in `Params` | Same. The paper's remark that Section 3 holds "with biases" has no explicit Lean form; a read bias can be put inside the arbitrary map `f_ℓ`, a write bias is a write row of a hidden unit that `f_ℓ` holds constant, so `eval_cob` covers it, but this is an argument, not a statement. |
| "all blocks of a network are of one kind" | `Arch.f` is an arbitrary family; `Arch.mlp σ …` and `Arch.gated σ …` use one `σ` for all blocks; widths `hid ℓ` may differ per block | Same or more general. |
| `hid : Fin L → Type` | universe 0 only for the index types of the hidden units (`Arch.r`, `Arch.w : Fin L → Type`), while `T d dIn dOut : Type*` | A restriction of no mathematical content: every finite type is equivalent to a `Fin n : Type`. |

Differences to know:

1. `Arch.f ℓ : Matrix T (r ℓ) ℝ → Matrix T (w ℓ) ℝ` is an arbitrary map of the whole matrix (all
   tokens together), and `Arch.χ : Matrix T d ℝ → Matrix T d ℝ` likewise. The paper's `χ` is the
   identity or RMSNorm, row by row. So the Lean statements with a general `A : Arch T d L` are
   about a larger family of networks than the paper's.
2. The same `χ` is applied before every read and before the readout (paper: same). There is no
   Lean network in which the blocks are normalized and the readout is not.

### 2.2 RMSNorm: D Section 2 "Normalization" (tex 187-191) against `Basic/RMSNorm.lean`

Paper: `N_ε(v) = v / sqrt(‖v‖²/d_model + ε)`, `ε ≥ 0`; for `ε = 0`, "a network is defined at the
inputs for which no row of a hidden state vanishes".

Lean (`Basic/RMSNorm.lean:22-27`):
```
noncomputable def rmsRow (ε : ℝ) (v : d → ℝ) : d → ℝ :=
  (Real.sqrt ((v ⬝ᵥ v) / (Fintype.card d : ℝ) + ε))⁻¹ • v
noncomputable def rmsNorm (ε : ℝ) (h : Matrix T d ℝ) : Matrix T d ℝ :=
  Matrix.of fun t => rmsRow ε (h t)
```
- Normalizing constant: `‖v‖²/d + ε` under the square root, with `d = Fintype.card d`. Same.
- Row by row. Same.
- `ε = 0`, `v = 0`: Lean gives `rmsRow 0 0 = 0` (`(sqrt 0)⁻¹ = 0`); the paper leaves it undefined.
  So in Lean a network with `χ = rmsNorm 0` is a total function, and a Lean statement "for all
  `x`" for `ε = 0` also speaks about inputs at which a hidden row vanishes. Only
  `eval_cob_rmsNorm_zero`, `rmsNorm_zero_mul_smul_orthogonal`, `conformal_of_rmsRow_zero_vecMul`
  use `ε = 0`; the first two hold at those inputs as well, the third quantifies over `v ≠ 0` as
  the paper does.
- `ε < 0` is allowed in Lean (`ε : ℝ`): then `Real.sqrt` of a negative number is `0` and the row
  is sent to `0` where `‖v‖²/d + ε ≤ 0`. The paper has `ε ≥ 0` (D) or `ε > 0` (S). The Lean
  statements that take an arbitrary `ε : ℝ` (`eval_cob_rmsNorm`, `exists_cob_reads_upperTriangular`,
  `eval_learned_eq_residual_rmsNorm`, `eval_cob_residual_rmsNorm`, `exists_cob_residual_read_upperTriangular`,
  `exists_cob_learned_upperTriangular`, `rmsRow_vecMul_transpose_of_orthonormal`) are therefore
  stated for more values of `ε` than the paper; they are algebraic identities and hold for all of them.
- `d` empty: `Fintype.card d = 0`, division by zero is zero, all rows are the empty row. Harmless.

### 2.3 Change of basis: D Definition 3.1 (tex 209-214) against `Symmetry/ChangeOfBasis.lean`

Paper: "the change of basis `G` at `h_ℓ` maps `W ↦ WG` for the writes into `h_ℓ`, `W ↦ G⁻¹W` for the
reads of `h_ℓ`", for one hidden state and one invertible `G`.

Lean (`Symmetry/ChangeOfBasis.lean:23-27`):
```
def Params.cob (θ : Params A dIn dOut) (G K : Fin (L + 1) → GL d ℝ) : Params A dIn dOut where
  E := θ.E * (G 0 : Matrix d d ℝ)
  read ℓ := (↑(K ℓ.castSucc)⁻¹ : Matrix d d ℝ) * θ.read ℓ
  write ℓ := θ.write ℓ * (G ℓ.succ : Matrix d d ℝ)
  D := (↑(K (Fin.last L))⁻¹ : Matrix d d ℝ) * θ.D
```
- This is the tuple of Proposition 3.2, `(E G_0, {G_{ℓ-1}⁻¹ W_read^ℓ, W_write^ℓ G_ℓ}, G_L⁻¹ D)`, when
  `K = G`: Lean block `ℓ` (paper `ℓ+1`) has its read multiplied by `K_ℓ⁻¹` (paper `G_{(ℓ+1)-1}⁻¹`) and
  its write by `G_{ℓ+1}`. Sides and indices are right.
- It is not literally Definition 3.1: (a) it acts at all `L+1` hidden states at once (Definition 3.1
  is recovered with `G j = 1` for `j ≠ ℓ`), and (b) it has two families, `G` on the writes and `K`
  on the reads, so that the case `ε = 0` (`G = cQ`, reads by `Qᵀ`) is `θ.cob G Q`. With `K = G` it is
  the composition of the paper's changes of basis at all hidden states.
- `cobSkip M G ℓ = G_{ℓ.castSucc}⁻¹ * M ℓ * G_{ℓ.succ}` is S "`A_ℓ ↦ G_{ℓ-1}⁻¹ A_ℓ G_ℓ`" (S eq. (6), tex 264-268). Same.

### 2.4 The parameter space, the Jacobian, the functional dimension: D Definition 4.1 (tex 255-261), S Definition 4.1 (tex 330-336), D Appendix C "Notation and flat directions" (tex 535-539) against `Dimension/Space.lean`, `Dimension/Functional.lean`

Paper: "For a finite batch `X = (x_1,…,x_n)` of inputs, let `F_X(θ) = (F_θ(x_1),…,F_θ(x_n))` … and
`𝐃F_X(θ)` the Jacobian of `θ ↦ F_X(θ)`. … `fd(θ) = max_X rank 𝐃F_X(θ)`, `red(θ) = P − fd(θ)`, where
the maximum is over all finite batches `X`."

Lean (`Dimension/Functional.lean:29-49`):
```
def evalBatch {n : ℕ} (X : Fin n → Matrix T dIn ℝ) (θ : Params A dIn dOut) : Fin n → Matrix T dOut ℝ :=
  fun i => eval A S θ (X i)
noncomputable def jacobianRank {n : ℕ} (X : Fin n → Matrix T dIn ℝ) (θ : Params A dIn dOut) : ℕ :=
  Module.finrank ℝ (LinearMap.range (fderiv ℝ (evalBatch A S X) θ).toLinearMap)
noncomputable def funDim (θ : Params A dIn dOut) : ℕ :=
  sSup {r : ℕ | ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), r = jacobianRank A S X θ}
noncomputable def redundancy (θ : Params A dIn dOut) : ℕ :=
  Module.finrank ℝ (Params A dIn dOut) - funDim A S θ
noncomputable def flat (θ : Params A dIn dOut) : Submodule ℝ (Params A dIn dOut) :=
  ⨅ x : Matrix T dIn ℝ, LinearMap.ker (fderiv ℝ (fun θ' => eval A S θ' x) θ).toLinearMap
```
- Batch: a tuple indexed by `Fin n`, any `n : ℕ`, `n = 0` included (rank `0`; it does not change the
  maximum). Same.
- Jacobian: the Fréchet derivative `fderiv ℝ (evalBatch A S X) θ` with respect to the norm that
  `Dimension/Space.lean` puts on `Params` (induced from the product of the elementwise sup norms).
  All spaces are finite-dimensional, so the derivative does not depend on the norm. Its rank is the
  dimension of its range. Same.
- Maximum: `sSup` of a set of natural numbers. The set is nonempty and bounded by `P`
  (`jacobianRank_le_finrank`), so the supremum is a maximum (`exists_jacobianRank_eq_funDim`). Same.
  (For an unbounded set `sSup` in `ℕ` would be `0`; this cannot happen here.)
- `redundancy`: natural-number subtraction, but `funDim ≤ P` always, so nothing is truncated. Same.
  No theorem in scope uses `redundancy`; all results are stated with `funDim` and an addition.
- **Where the map is not differentiable.** In Mathlib `fderiv` of a map that is not differentiable
  at the point is `0`. So in Lean a batch that contains an input `x` at which `θ ↦ F_θ(x)` is not
  differentiable at `θ` has `jacobianRank = 0` (the tuple is differentiable only if every component
  is), and `flat` gets no constraint from such an `x`. For ReLU-type blocks the paper says "'every
  input' means every such input [at which no hidden unit sits at its kink]" (D tex 535), which is
  the same convention for `flat`, and for `funDim` Lean's convention drops every batch that contains
  one such input, which gives the same maximum. For analytic blocks the question does not arise. The
  Lean results on `funDim` in scope are all for differentiable blocks (`hf : ∀ ℓ, Differentiable ℝ
  (A.f ℓ)`, or `tanh`, GELU, SiLU), so this convention is never exercised. `funDim_add_finrank_flat`
  assumes differentiability at every `x` (`hdiff`).
- `P`: `Module.finrank ℝ (Params A dIn dOut)`. Same as the number of entries (see 2.1).
- The sequence length is fixed: `T` is a parameter of `Arch`, and the batches are of inputs in
  `ℝ^{T×d_in}` for this `T`. The paper also fixes `T` ("inputs range over all of `ℝ^{T×d_in}`").
- `flat` is the paper's `𝒦(θ)` ("Call `η` flat if `𝐃_θ F(θ,x) η = 0` for every input `x`"). Same.
- `funDim_add_finrank_flat`: `funDim A S θ + finrank (flat A S θ) = finrank Params`, under `hdiff`.
  This is the paper's "the functional dimension at `θ` is therefore `P − dim 𝒦(θ)`", written as an
  addition. Same.

### 2.5 "At generic parameters": D tex 185 against `Generic/Params.lean`

Paper: "A statement holds at generic parameters if it holds outside a set of Lebesgue measure zero."
Lean: `∀ᵐ θ ∂μ, …` for an arbitrary `μ : Measure (Params A dIn dOut)` with `[μ.IsAddHaarMeasure]`,
where `Params` carries its Borel σ-algebra (`Generic/Params.lean:32-34`). On a finite-dimensional
real vector space the additive Haar measures are the positive multiples of the Lebesgue measure of
any basis, so they have the same null sets. Same. The statements are quantified over every such `μ`,
so they are not vacuous (such a measure exists; see the checks in 2.10).

### 2.6 Directions of the symmetries: D Step 1 (tex 308-311), D Appendix B (tex 480-489), D eq. (11) against `Dimension/UpperBound.lean`, `Dimension/Rescaling.lean`

- `cobDir θ X` (`Dimension/UpperBound.lean:32-36`): `E := θ.E * X 0`, `read ℓ := -(X ℓ.castSucc * θ.read ℓ)`,
  `write ℓ := θ.write ℓ * X ℓ.succ`, `D := -(X (Fin.last L) * θ.D)`. This is the paper's
  `η^Z = (E Z_0, {−Z_{ℓ-1} W_read^ℓ, W_write^ℓ Z_ℓ}, −Z_L D)` (D eq. (11), cases (n) and (+)) and, for
  `L = 1`, `η_E = EX, η_read = −X W_read, η_write = W_write Y, η_D = −YD`. Same.
- `rescaleDir θ α` (`Dimension/Rescaling.lean:35-40`): `E := 0`, gate columns `0`, value column `i` of
  block `ℓ` `−α_{ℓ,i} e_i`, write row `i` `α_{ℓ,i} a_i`, `D := 0`. This is the derivative of the paper's
  `(e_i, a_i) ↦ (e_i/λ, λ a_i)` at `λ = e^{τα}`, and the `Δ`-part of the paper's `η^{Z,Δ}` (D eq. (12):
  `−W_v Δ_ℓ`, `Δ_ℓ W_write`). Same.
- Not defined: the directions of the rescalings of ReLU and ReLU² hidden units, of the gate of a
  ReGLU unit, and of the changes of basis inside an attention head.

### 2.7 Activations

| Paper | Lean | Same? |
|---|---|---|
| `tanh` | `Real.tanh`, derivative `1 − tanh²` (`hasDerivAt_tanh`, `OneBlock/Tanh.lean:22`) | Same |
| GELU `σ(z) = zΦ(z)`, `Φ` the standard normal distribution function (D tex 605) | `gelu z = z * gaussCdf z`, `gaussCdf z = 1/2 + ∫_0^z gaussPdf`, `gaussPdf z = exp(−z²/2)/sqrt(2π)` (`Activations/Gaussian.lean:22-28`); `tendsto_gaussCdf_atTop/atBot` give the limits `1` and `0` | Same (the exact GELU, not the `tanh` approximation) |
| `σ' = Φ(z) + zφ(z)` | `geluDeriv` (`Activations/Gaussian.lean:188`), `hasDerivAt_gelu` | Same |
| SiLU `z/(1+e^{−z})` (D tex 573) | `silu z = z / (1 + Real.exp (-z))`, `siluDeriv z = (1 + e^{−z} + z e^{−z})/(1 + e^{−z})²`, `hasDerivAt_silu` (`OneBlock/UnitsSwiGLU.lean:27-33`) | Same |
| ReLU `max(z,0)`, `σ' = 1[z>0]` | `relu z = max z 0`, `reluDeriv z = if 0 < z then 1 else 0`; `hasDerivAt_relu` only for `z ≠ 0` | Same |
| ReLU² | `reluSq z = (max z 0)^2`, `reluSqDeriv z = 2 * max z 0`, `hasDerivAt_reluSq` for all `z` | Same |

### 2.8 Appendix D objects: D tex 750-760, 879-897, 933-936, 983-992, 1024-1028, 1574 against `Depth/Suffix.lean`, `Depth/StepTanh.lean`, `Depth/Tanh.lean`

- `suffix A S θ k h` (`Depth/Suffix.lean:47-51`): `Fin.reverseInduction` from `fun h => A.χ h * θ.D`
  with the step `fun ℓ B h => B (h * S ℓ + A.f ℓ (A.χ h * θ.read ℓ) * θ.write ℓ)`. For `S = 0` this is
  the paper's `𝓑_{>L}(h) = χ(h) D`, `𝓑_{>k-1}(h) = 𝓑_{>k}(g_k(χ(h)))`. Same; `eval_eq_suffix_zero` is
  "`F_θ(x) = 𝓑_{>0}(xE)`".
  Difference: the paper takes inputs of one token ("a hidden state is a row `h`"); in Lean `h` is a
  `T × d` matrix, all tokens together. For `T` with one element this is the paper's object.
- `SuffixFlat A θ k Z η` (`Depth/Suffix.lean:83-86`): `∀ h : Matrix T d ℝ, fderiv (h' ↦ suffix A 0 θ k h') h (h * Z)
  + fderiv (θ' ↦ suffix A 0 θ' k h) θ η = 0`. This is the identity (16) of the PDF in the case (n).
  `η` is a direction of all parameters; the derivative only sees its entries at the blocks after
  `h_k` and at `D`, which is the paper's "direction of the weights of the blocks `k+1,…,L` and of `D`".
  For MLP blocks (which act on each token) and nonempty `T`, the identity for all matrices `h` is
  equivalent to the identity for all rows. Same in the case (n); the cases (+) and (0) (where the
  identity has "`h ≠ 0`" or holds on the values of `χ`) are not defined.
- `Claim A θ k` (`Depth/Suffix.lean:91-96`): for all `Z`, `η` with `SuffixFlat A θ k Z η` there is
  `X : Fin (L+1) → Matrix d d ℝ` with `X k = Z`, `η.read ℓ = −(X ℓ.castSucc * θ.read ℓ)` and
  `η.write ℓ = θ.write ℓ * X ℓ.succ` for the blocks `ℓ` with `k ≤ ℓ.castSucc`, and `η.D = −(X last * θ.D)`.
  This is Claim `(D_k)` of the paper (D tex 933-936, eq. (17)) in the case (n) (`𝔤` = all matrices,
  so "`Z ∈ 𝔤`" is empty) for blocks without symmetries inside (no `Δ`). Lean block `ℓ ≥ k` is the
  paper's block `ℓ+1 ≥ k+1`. Same in that case. The form for gated blocks (eq. (19)) and the cases
  (+), (0) are not defined.
- `Regular A θ` (`Depth/Suffix.lean:100-105`): `E`, `D` and every write of rank `d` (R1); for every
  block there is `n : Matrix T d ℝ` at which `fderiv (n' ↦ A.f ℓ (n' * θ.read ℓ) * θ.write ℓ) n` is
  injective (R3). Paper (R3), cases (n) and (+): "`𝐃g_ℓ(n)` is invertible at some row `n`". The
  derivative is an endomorphism of a finite-dimensional space, so injective is invertible. Same for
  the case (n); (R2) and the form of (R3) for the case (0) are not there. `Regular` does not mention
  `χ`.
- `blockLHS θ k η w w' zdot` (`Depth/StepTanh.lean:49-55`):
  `fderiv (h' ↦ suffix … θ k.succ h') (w * θ.write k) ((w' ⊙ zdot) * θ.write k + w * η.write k)
  + fderiv (θ' ↦ suffix … θ' k.succ (w * θ.write k)) θ η`. This is `𝓛(w̃, w̃'; n)` of D eq. (21), with
  `ż(n)` passed as an argument and the whole `η` in the place of `η'` (the network after the block
  does not depend on the weights of the block). Same.
- `TanhDepthGeneric θ` (`Depth/Tanh.lean:33-46`): `E`, `D`, every write of rank `d`; no row of a write
  vanishes (T1); the columns of every read are linearly independent over `ℚ` (T2),
  `LinearIndependent ℚ (fun j : hid ℓ => fun i : d => θ.read ℓ i j)`; `IsUnit (θ.read ℓ * θ.write ℓ).det`
  for every block. Paper (D tex 1574): "Let `θ` satisfy (R1), let every block satisfy (T1) and (T2),
  and let every `W_read^ℓ W_write^ℓ` be invertible." Same.
- `OneBlockGeneric θ` (`OneBlock/Mlp.lean:49-60`) and `OneBlockGenericGated θ` (`OneBlock/Gated.lean:63-77`):
  the conditions of D tex 545, "`E`, `D`, `W_read` and `W_write` have rank `d_model`, every `a_i` is
  nonzero, and the `c_i` are nonzero and pairwise non-collinear", and for gated blocks "every `e_i`
  is nonzero". Same, except that the paper's "and is not proportional to `c_i`" for gated blocks is
  left out of `OneBlockGenericGated` (fewer conditions; see Lemma C.3 below).

### 2.9 `skipProd`: S eq. (7) (tex 278-280) against `Residual/LearnedSkips.lean:25-34`

`skipProd S : Fin (L+1) → GL d ℝ` by `Fin.reverseInduction` from `1` with the step `fun ℓ Λ => S ℓ * Λ`;
`skipProd_last : skipProd S (Fin.last L) = 1`, `skipProd_castSucc : skipProd S ℓ.castSucc = S ℓ * skipProd S ℓ.succ`.
With Lean `S ℓ` the paper's `A_{ℓ+1}`, this is `Λ_L = I`, `Λ_ℓ = A_{ℓ+1} Λ_{ℓ+1}`, so
`Λ_ℓ = A_{ℓ+1} ⋯ A_L` and "`A_ℓ Λ_ℓ = Λ_{ℓ-1}`". Same. The skips are taken in `GL d ℝ` (invertible),
as in Theorem 3.2 (i).

### 2.10 Instance arguments, elaborated forms, degenerate cases

Checked with `#check @…` / `#print …` (`/home/claude/audit_dim/Check1.lean`, output `Check1.out`).
I did not run `lake build`. The checks ran against the compiled library in `.lake/build`; for each of
the 41 source files outside `Absorb/` the content hash (`Lake.computeTextFileHash`) equals the hash
in its build trace, so the compiled statements are those of the current sources
(`/home/claude/audit_dim/HashCheck2.lean`). During the audit another process changed
`STATEMENTS.md` (two rows and one note of the section "Absorb paper") and `Absorb/FewerUnits.lean`;
nothing in the three sections of this audit changed.

- `funDim`, `jacobianRank`, `flat`, `SuffixFlat`, `Claim`, `Regular` elaborate **without** `[Fintype T]`:
  Mathlib's `fderiv` is defined on topological vector spaces, and the topology of `Matrix T d ℝ` is
  the product topology, which exists for every `T`. Every theorem that uses them assumes
  `[Fintype T]`, and then this topology is that of the elementwise norm, so nothing depends on it.
- `[Nonempty T]`: all equalities for the functional dimension carry it (`ae_funDim_*_oneBlock`,
  `funDim_tanh_skipless`, `ae_funDim_tanh_skipless`, `funDim_of_claim`, `claim_last`, …). It is
  needed: with no tokens the output is the empty matrix and the functional dimension is `0`
  (checked: `Check3.lean`, example (g)). The
  paper has `T ≥ 1` tokens tacitly. The upper bounds (`funDim_add_le_*`) do not carry it and are
  true for empty `T` as well.
- `[DecidableEq d]` (for the identity matrix and `GL d ℝ`), `[LinearOrder d]` (for "upper
  triangular", `Matrix.BlockTriangular id`: the entry `(i, j)` is `0` when `j < i`): no content.
- `L = 0` is allowed everywhere (`Fin 0` has no block): the network is `x ↦ χ(xE) D`. The paper has
  `L` blocks without saying `L ≥ 1`. For `L = 0`, `ae_funDim_tanh_skipless` says that the linear
  network `x ↦ xED` has functional dimension `P − d²`, which is right.
- Empty `d`: every matrix is empty, `GL d ℝ` is trivial, `P = 0`; the statements are true and say
  nothing. Statements that need `d ≥ 1` say `[Nonempty d]` (`ae_tanhDepthGeneric`, `ae_value_ne_zero`,
  the gated upper bounds at generic parameters); the one-block theorems and `ae_funDim_tanh_skipless`
  have `2 ≤ Fintype.card d`.
- Natural-number arithmetic: every bound and equality is written as an addition
  (`funDim + … ≤ finrank`, `funDim + … = finrank`), so no subtraction can truncate. The only
  division is `Fintype.card d * (Fintype.card d - 1) / 2`; `n(n−1)` is even, and for `n = 0`
  the truncated `0 − 1 = 0` gives `0`, the right value. `card_below_diagonal` and
  `finrank_antisymmetric` show that this number is what it should be.
- Scratch checks that compile (`/home/claude/audit_dim/Check2.lean`, `Check3.lean`): an additive Haar
  measure on `Params A dIn dOut` exists, so `∀ᵐ θ ∂μ` is not a statement about an empty family of
  measures; `Module.finrank ℝ (Params A dIn dOut)` is
  `|dIn|·|d| + Σ_ℓ |d|·|r ℓ| + Σ_ℓ |w ℓ|·|d| + |d|·|dOut|`; the stream matrices `1` are identity
  matrices; `rmsRow 0 0 = 0`; `ae_funDim_tanh_skipless` at one token, `d = d_in = d_out = 2`, two
  blocks of width 3 reads `fd + 12 = P`.

---------------------------------------------------------------------------------------------------

## (3) One entry per statement

### 3.A Dimension paper

#### D Definition 3.1 (Change of basis), tex 209-214
Paper: "For an invertible `d_model × d_model` matrix `G`, the change of basis `G` at `h_ℓ` maps `W ↦ WG`
for the writes into `h_ℓ`, `W ↦ G⁻¹W` for the reads of `h_ℓ`."
Lean: `Params.cob θ G K` (`Symmetry/ChangeOfBasis.lean:23`). See 2.3.
Verdict: **DIFFERENT object, on purpose** (all hidden states at once; separate matrices `G` for the
writes and `K` for the reads). With `K = G` and `G j = 1` for `j ≠ ℓ` it is the paper's map. No
statement is affected.

#### D Proposition 3.2 (Changes of basis preserve the function), tex 222-228
Paper: "Without normalization or under pre-RMSNorm, let `G_0, …, G_L ∈ 𝒢`. The parameters
`(E G_0, {G_{ℓ-1}⁻¹ W_read^ℓ, W_write^ℓ G_ℓ}_{ℓ=1}^L, G_L⁻¹ D)` give the same function as `θ`, with the
hidden states `h_ℓ G_ℓ`: one matrix of `𝒢` per hidden state. For `ε = 0` and `G_ℓ = c_ℓ Q_ℓ`, the same
holds with `Q_ℓᵀ` in the place of `G_ℓ⁻¹`."

Lean:
- `eval_cob` (`Symmetry/ChangeOfBasis.lean:61`): for any `A`, stream matrices `M`, `G K : Fin (L+1) → GL d ℝ`,
  `(∀ ℓ h, A.χ (h * G ℓ) = A.χ h * K ℓ) → eval A (cobSkip M G) (θ.cob G K) x = eval A M θ x`.
- `hidden_cob` (`:43`, not in the index): under the same hypothesis,
  `hidden A (cobSkip M G) (θ.cob G K) x ℓ = hidden A M θ x ℓ * G ℓ`.
- `eval_cob_skipless` (`:71`): `A.χ = id → eval A 0 (θ.cob G G) x = eval A 0 θ x`.
- `eval_cob_rmsNorm` (`Symmetry/Normalized.lean:26`): `(ε : ℝ)`, `A.χ = rmsNorm ε`, `Q ℓ` orthogonal for all `ℓ`
  `→ eval A 0 (θ.cob Q Q) x = eval A 0 θ x`.
- `eval_cob_rmsNorm_zero` (`:41`): `A.χ = rmsNorm 0`, `0 < c ℓ`, `Q ℓ` orthogonal, `G ℓ = c ℓ • Q ℓ`
  `→ eval A 0 (θ.cob G Q) x = eval A 0 θ x`.

Comparison:
- Quantifiers: all `θ`, all `x`, all families of matrices. Same.
- "Without normalization": `𝒢 = GL(d)`, `G : Fin (L+1) → GL d ℝ`. Same.
- "Under pre-RMSNorm": `𝒢 = O(d)`. Same; the reads get `Q⁻¹`, which is `Qᵀ` (`coe_inv_of_mem_orthogonalGroup`).
  Lean allows every real `ε`, the paper `ε > 0` here.
- "`ε = 0`": Lean has `c_ℓ > 0` explicitly (the paper: "for every number `c > 0`", tex 220). The
  reads are multiplied by `Q_ℓ⁻¹ = Q_ℓᵀ`. Same. The Lean statement holds for all `x`, also where a
  hidden row vanishes, with the convention `N_0(0) = 0`; the paper defines the network only where
  no row vanishes.
- "with the hidden states `h_ℓ G_ℓ`": only in `hidden_cob`, in the general form with the stream
  matrices `cobSkip M G`; the three special cases state the equality of the outputs only.
  (`cobSkip 0 G = 0` is a private lemma, so the clause for a skipless network is one rewrite away;
  checked in `/home/claude/audit_dim/Check3.lean`, example (k).)
- Blocks: arbitrary maps `f_ℓ` in Lean. More general.

Verdict: **SAME** (Lean slightly stronger: arbitrary `f_ℓ`, any real `ε`, all inputs for `ε = 0`).
The clause on the hidden states is `hidden_cob`, which the index does not list.

#### D Proposition 3.3 (Exact reduction), tex 237-242, and the paragraph after it, tex 245
Paper: "Let `d_model` columns of the read of `h_ℓ` (`W_read^{ℓ+1}`, or `D` if `ℓ = L`) form an
invertible matrix `W_1`. (i) Without normalization, the change of basis `G = W_1` at `h_ℓ` preserves
the function and turns `W_1` into `G⁻¹W_1 = I`. (ii) Under pre-RMSNorm, let `W_1 = QR` with `Q`
orthogonal and `R` upper triangular. The change of basis `Q` at `h_ℓ` preserves the function and turns
`W_1` into `QᵀW_1 = R`. At generic parameters every hidden state has such columns, and these changes
of basis at all `L+1` hidden states remove `(L+1) dim 𝒢` parameters: `(L+1)d²` in (i), and
`(L+1)d(d−1)/2` in (ii)."

Lean:
- (i) `exists_cob_reads_eq_one` (`Symmetry/Reduction.lean:37`): `A.χ = id`, a choice of columns
  `c : ∀ ℓ : Fin L, d → A.r ℓ` and `cD : d → dOut`, with
  `∀ ℓ, IsUnit ((θ.read ℓ).submatrix id (c ℓ)).det` and `IsUnit (θ.D.submatrix id cD).det`; then
  `∃ G : Fin (L+1) → GL d ℝ, (∀ x, eval A 0 (θ.cob G G) x = eval A 0 θ x) ∧ (∀ ℓ, ((θ.cob G G).read ℓ).submatrix id (c ℓ) = 1) ∧ (θ.cob G G).D.submatrix id cD = 1`.
- (ii) `exists_cob_reads_upperTriangular` (`:144`): `[LinearOrder d]`, `(ε : ℝ)`, `A.χ = rmsNorm ε`, any
  `c`, `cD` (no invertibility); then `∃ Q`, all `Q ℓ` orthogonal, the function is preserved, and
  every chosen submatrix of `(θ.cob Q Q).read ℓ` and of `(θ.cob Q Q).D` is `BlockTriangular id`.
  It rests on `exists_orthogonal_transpose_mul_upperTriangular` (`:98`): for every square `W` there
  is an orthogonal `Q` with `Qᵀ W` upper triangular.
- rows of a write (tex 245, Example A.2): `exists_cob_writes_eq_one` (`:68`), the same with rows
  `ρE : d → dIn` of `E` and `ρ ℓ : d → A.w ℓ` of the writes, `G_0 = E_1⁻¹`, `G_{ℓ} = (W_1^ℓ)⁻¹`.
- "At generic parameters every hidden state has such columns": `ae_isUnit_det_submatrix`
  (`Generic/Params.lean:91`): `∀ᵐ θ ∂μ`, for every block and every embedding `c : d ↪ A.r ℓ` the
  chosen columns of the read form an invertible matrix, and the same for `D`, for rows of `E` and
  for rows of every write.
- the counts: `card_below_diagonal` (`:181`), `(Finset.univ.filter fun p : Fin n × Fin n => p.2 < p.1).card = n * (n - 1) / 2`.

Comparison:
- The paper's statement is about **one** hidden state `h_ℓ`, with a hypothesis on the read of that
  hidden state only. The Lean statements (i) and for the rows are about **all `L+1` hidden states at
  once**, and (i) needs invertible chosen columns in every read and in `D`. For parameters at which
  one read has `d` invertible columns and another read has none, the paper's (i) applies and
  `exists_cob_reads_eq_one` does not. The paper's one-state form follows from `eval_cob_skipless`
  (take `G ℓ = W_1`, the other matrices `1`; checked by a scratch proof, `/home/claude/audit_dim/Check3.lean`,
  example (l)), but it is not a stated Lean theorem. In the other
  direction the Lean form is the paper's sentence "these changes of basis at all `L+1` hidden states"
  and the remark of the proof that "the reductions at all `L+1` hidden states can be made together".
- `c ℓ : d → A.r ℓ` is any map, not an injection. In (i) the hypothesis forces it to be injective
  (a repeated column gives determinant `0`) when `d` has at least two elements. In (ii) repeated
  columns are allowed; the statement is then about a matrix with repeated columns. More general.
- Lean says "there exist `G`" and does not say `G = W_1`. Since the new submatrix is `G⁻¹ W_1 = 1`,
  this forces `G = W_1`. Same.
- (ii): the paper takes any factorization `W_1 = QR` and assumes `W_1` invertible. Lean proves that
  an orthogonal `Q` with `Qᵀ W_1` upper triangular exists, for every `W_1`. No invertibility, any real `ε`.
- Under pre-RMSNorm, the reduction on the **rows of a write** (proof, tex 423: "For a write, let
  `W_1ᵀ = QR` … `W_1 Q = Rᵀ`, which is lower triangular") has no Lean statement.
- "every hidden state has such columns": the paper's sentence asserts existence, which needs
  `d_hidden ≥ d` and `d_out ≥ d` (the Scope). `ae_isUnit_det_submatrix` is the sentence of the proof
  ("At generic parameters every `d` columns of a read, and every `d` rows of a write, form an
  invertible matrix"), quantified over embeddings; if no embedding exists it says nothing. It has
  no hypothesis on the sizes. Existence follows from it under the Scope.
- "remove `(L+1) dim 𝒢` parameters": not a Lean statement (it is a count of fixed entries;
  `card_below_diagonal` gives the number for one triangular matrix).

Verdict: (i) **LEAN WEAKER in its hypotheses** (simultaneous form; the one-state form is not
stated). (ii) **LEAN STRONGER** (no invertibility, any `ε`), also in the simultaneous form. Rows of
a write without normalization: **SAME** up to the simultaneous form; under pre-RMSNorm: **not stated**.
Last sentence: first half stated in the form of the proof, the count **not stated**. Overall **PART**.

#### D Appendix A.3, the count for the ViT-B, tex 472-476
Paper: "`25 · 767·766/2 = 7,344,025`". Lean: `vitB_count : 25 * (767 * 766 / 2) = 7344025`
(`Symmetry/Reduction.lean:196`). The division is exact. **SAME** (arithmetic only; the claim "8.5
percent of the 86.6M parameters" is not stated).

#### D Lemma A.1 (RMSNorm and changes of basis), tex 391-393
Paper: "Let `G ∈ GL(d_model)`. There is a matrix `M` with `N_ε(hG) = N_ε(h) M` for all rows `h ≠ 0` if
and only if `G ∈ O(d_model)` when `ε > 0`, and `G ∈ CO(d_model)` when `ε = 0`. Then `M = Q`, where
`G = cQ` with `c > 0` and `Q` orthogonal."

Lean, four statements:
- "⇐", any `ε`: `rmsNorm_mul_orthogonal (ε : ℝ) (hQ : Q ∈ orthogonalGroup d ℝ) (h : Matrix T d ℝ) : rmsNorm ε (h * Q) = rmsNorm ε h * Q` (`Basic/RMSNorm.lean:49`).
- "⇐", `ε = 0`: `rmsNorm_zero_mul_smul_orthogonal (hc : 0 < c) (hQ) (h) : rmsNorm 0 (h * (c • Q)) = rmsNorm 0 h * Q` (`:83`).
- "⇒", `ε > 0`: `orthogonal_of_rmsRow_vecMul (hε : 0 < ε) (G : GL d ℝ) (M) (h : ∀ v, v ≠ 0 → rmsRow ε (v ᵥ* G) = rmsRow ε v ᵥ* M) : (G : Matrix d d ℝ) ∈ orthogonalGroup d ℝ ∧ M = G` (`Basic/RMSNormConverse.lean:169`).
- "⇒", `ε = 0`: `conformal_of_rmsRow_zero_vecMul (G : GL d ℝ) (M) (h : ∀ v, v ≠ 0 → rmsRow 0 (v ᵥ* G) = rmsRow 0 v ᵥ* M) : M ∈ orthogonalGroup d ℝ ∧ ∃ c, 0 < c ∧ (G : Matrix d d ℝ) = c • M` (`:199`).

Comparison: the hypothesis "for all rows `h ≠ 0`" is `∀ v, v ≠ 0 → …`; `G` invertible is `G : GL d ℝ`;
the conclusions give `G ∈ O(d)` and `M = G` for `ε > 0`, and `G = cM` with `M` orthogonal and `c > 0`
for `ε = 0`, which is "`G ∈ CO(d)`, `M = Q`". The two "⇐" statements hold for all `h`, the zero row
included (Lean's `N_0(0) = 0`), and for whole hidden states. `d` empty: true and empty.
Verdict: **SAME** (the "if and only if" is split into four statements; the "⇐" parts slightly stronger).

#### D Example A.2 and Proposition A.3 (LayerNorm reduces to RMSNorm), tex 428-447, 453-457
Example A.2 (a numerical example of the rows of a write): no Lean statement of the example; its
general form is `exists_cob_writes_eq_one`.
Proposition A.3: "(i) Replacing each read `W` by `diag(γ)W` with the added bias `βW`, and each write
`W`, write bias `b` and embedding `E` by `WZ`, `bZ` and `EZ`, gives a network that computes the same
function, whose hidden states lie in `𝒱`, and whose reads see `N_ε(h)`. (ii) In an orthonormal basis
of `𝒱`, this network is a pre-RMSNorm network of dimension `d_model − 1`, with every read multiplied by
`sqrt(d/(d−1))` and `ε` replaced by `ε d/(d−1)`."
Lean (`Basic/LayerNorm.lean`): `centering d = 1 − (card d)⁻¹ • J` (`:28`), `centering_mul_centering`
(`Z² = Z`, `:40`), `sum_vecMul_centering` (`∑ i, (v ᵥ* Z) i = 0`, `:66`),
`vecMul_centering_of_sum_eq_zero` (`:77`), and `rmsRow_vecMul_transpose_of_orthonormal (U : Matrix d m ℝ) (hU : Uᵀ * U = 1) (hm : 0 < card m) (ε) (y) : rmsRow ε (y ᵥ* Uᵀ) = sqrt (card d / card m) • (rmsRow (ε * card d / card m) y ᵥ* Uᵀ)` (`:85`).
Comparison: these are the two facts of the proof of (i) and the displayed identity of the proof of
(ii) (tex 466-468), the latter for any number `m ≥ 1` of orthonormal columns and any real `ε`
(`m = d − 1` in the paper). Neither part of the proposition is stated: Lean has no LayerNorm, no
gains and no biases.
Verdict: **PART** (computations of the proof only).

#### D Definition 4.1 (Functional dimension), tex 255-261
See 2.4. Lean: `evalBatch`, `jacobianRank`, `funDim`, `redundancy` (`Dimension/Functional.lean:29-44`),
with `exists_jacobianRank_eq_funDim`, `jacobianRank_le_funDim`, `jacobianRank_le_finrank`.
Verdict: **SAME**. To know: `fderiv` is `0` where the map is not differentiable (2.4); this
convention is not used by any result in scope.

#### D Section 4, "a continuous symmetry adds to the redundancy", tex 263; D Appendix C, "Notation and flat directions", tex 535-539
Paper: "if a continuous family of maps of the parameters preserves the function, the directions in
which it moves `θ` lie in the kernel of every such Jacobian"; "some finite batch has the kernel
`𝒦(θ)`. By rank-nullity, the functional dimension at `θ` is therefore `P − dim 𝒦(θ)`."
Lean: `mem_flat_of_hasDerivAt` (`Dimension/Functional.lean:279`): a curve `γ` with `γ 0 = θ`,
`HasDerivAt γ η 0` and the same function for all `τ` near `0` gives `η ∈ flat A S θ`;
`funDim_add_finrank_flat` (`:246`): `funDim A S θ + finrank (flat A S θ) = finrank Params`;
`funDim_add_finrank_le_of_le_flat` (`:267`). All three assume `hdiff : ∀ x, DifferentiableAt ℝ (fun θ' => eval A S θ' x) θ`.
Verdict: **SAME** for differentiable networks (the paper's convention for ReLU-type blocks,
"'every input' means every such input", is not covered by these three lemmas because of `hdiff`).

#### D Appendix B, the symmetries inside the blocks, tex 480-489
Paper (list): "SwiGLU, GeGLU, ReGLU: `(e_i, a_i) ↦ (e_i/λ, λ a_i)`, `λ ≠ 0`" and the others.
Lean: `eval_rescale` (`Dimension/Rescaling.lean:47`): for a gated network with any gate `σ`, any `χ`,
any stream matrices, if `θ'` has the same `E`, `D` and gate columns, value columns `(c ℓ i)⁻¹ •` those
of `θ` and write rows `c ℓ i •` those of `θ`, with `c ℓ i ≠ 0`, then `eval … θ' x = eval … θ x`.
`rescaleDir`, `rescaleDir_mem_flat`, `rescaleDir_mem_flat_of_differentiable`, `rescaleDir_mem_flat_stream`
(`:156-186`): the direction is flat when `σ` and `χ` are differentiable.
Verdict: **PART**: the rescaling of the values of gated units is stated, **SAME** (`λ ≠ 0`, any gate).
Not stated: the rescalings of ReLU and ReLU² units, the rescaling of the gate of a ReGLU unit, the
changes of basis inside an attention head, and the numbers `s` for these blocks.

#### D Lemma B.1 (Locally free action), tex 493-495
Paper: "Without normalization or under pre-RMSNorm, consider a network whose blocks are `tanh`, GELU,
ReLU, ReLU² or gated blocks with at least `d_model` hidden units, or attention blocks whose heads
have width `d_h ≤ d_model` and total width `H d_h ≥ d_model`. If `d_in ≥ d_model`, then at generic
parameters the changes of basis and the symmetries inside the blocks act locally freely." ("act
locally freely at `θ` if no continuous family of them, other than the identity, fixes `θ`", tex 491.)
Lean: `cobDir_injective` (`Dimension/UpperBound.lean:61`): `θ.E.rank = card d → (∀ ℓ, (θ.write ℓ).rank = card d) → Function.Injective (cobDir θ)`;
`cobDir_add_rescaleDir_injective` (`Dimension/Rescaling.lean:211`): the same with no vanishing value
column, for `(X, α) ↦ cobDir θ X + rescaleDir θ α`; `ae_rank_E_write` (`Generic/Params.lean:163`):
`card d ≤ card dIn → (∀ ℓ, card d ≤ card (A.w ℓ)) → ∀ᵐ θ, θ.E.rank = card d ∧ ∀ ℓ, (θ.write ℓ).rank = card d`;
`ae_value_ne_zero` (`Generic/Gated.lean:28`).
Comparison: Lean states the infinitesimal form: the linear map from the Lie algebra to the
directions of the parameters is injective. This is what the proof of Theorem 4.3 uses ("it moves `θ`
in `(L+1) dim 𝒢 + s` independent directions"). The paper's lemma is about the group ("no continuous
family … fixes `θ`"); the two are equivalent for a Lie group action, and this equivalence is not in
Lean. Lean has the hypotheses of the paper's proof (ranks; no vanishing value column) and the
statement that they hold at generic parameters under `d_in ≥ d` and widths `≥ d`. Cases: changes of
basis for any blocks; rescalings of the values of gated blocks. Not stated: ReLU, ReLU², the gate
rescaling of ReGLU, attention.
Verdict: **DIFFERENT in form (infinitesimal), PART in cases**.

#### D Theorem 4.3 (Upper bound), tex 271-273
Paper: "Without normalization or under pre-RMSNorm, at generic parameters, the functional dimension
of a network of `L` blocks is at most `P − (L+1) dim 𝒢 − s`." (Scope of Section 2: `d_in, d_out ≥ d ≥ 2`,
`d_hidden ≥ d`, blocks of one kind among `tanh`, GELU, ReLU, ReLU², ReGLU, SwiGLU, GeGLU, attention.)
And after it (tex 276): "For `ε = 0` the same bound holds, with `𝒢 = CO(d_model)`, for the four kinds
of block of the main result."

Lean:
- `funDim_add_le_skipless` (`Dimension/UpperBound.lean:191`): `A.χ = id`, `∀ ℓ, Differentiable ℝ (A.f ℓ)`,
  `θ.E.rank = card d`, `∀ ℓ, (θ.write ℓ).rank = card d` give
  `funDim A 0 θ + (L + 1) * card d ^ 2 ≤ finrank ℝ (Params A dIn dOut)`.
- `funDim_add_le_skipless_rmsNorm` (`Dimension/UpperBoundRMSNorm.lean:243`): `0 < ε`, `A.χ = rmsNorm ε`, the
  same hypotheses, `funDim A 0 θ + (L + 1) * (card d * (card d - 1) / 2) ≤ finrank …`.
- `ae_funDim_add_le_skipless`, `ae_funDim_add_le_skipless_rmsNorm` (`Generic/Params.lean:174, 185`):
  the same `∀ᵐ θ ∂μ`, under `card d ≤ card dIn` and `∀ ℓ, card d ≤ card (A.w ℓ)`.
- gated blocks: `funDim_add_le_skipless_gated`, `funDim_add_le_skipless_gated_rmsNorm`
  (`Dimension/Rescaling.lean:308, 339`), `ae_funDim_add_le_skipless_gated`,
  `ae_funDim_add_le_skipless_gated_rmsNorm` (`Generic/Gated.lean:54, 69`): for `Arch.gated σ id hid`
  resp. `Arch.gated σ (rmsNorm ε) hid` with `Differentiable ℝ σ`, `[Nonempty d]`,
  `funDim … 0 θ + ((L + 1) * card d ^ 2 + ∑ ℓ, card (hid ℓ)) ≤ finrank …` and the same with
  `card d * (card d - 1) / 2`.

Comparison:
- Conclusion: "at most `P − (L+1) dim 𝒢 − s`" as `fd + (L+1) dim 𝒢 + s ≤ P`. Same; `dim 𝒢` is `d²`
  resp. `d(d−1)/2` (`finrank_antisymmetric`).
- Hypotheses: Lean needs `d_in ≥ d` and at least `d` rows in every write (for an MLP block,
  `d_hidden ≥ d`), as Lemma B.1 does. It does **not** need `d_out ≥ d` or `d ≥ 2`. Fewer hypotheses.
- Cases:
  - `tanh` and GELU blocks (`s = 0`), cases (n) and (+): covered by the general statements with
    `A = Arch.mlp σ χ hid` (`differentiable_f_mlp` gives `hf`; checked for GELU under pre-RMSNorm,
    `Check3.lean`, example (h)). Full statement.
  - SwiGLU and GeGLU (`s` = number of hidden units), cases (n) and (+): covered by the gated
    statements, for every differentiable gate. Full statement.
  - ReLU² (`s = d_hidden` per block): the map is differentiable, so the general statements apply,
    but they give only `fd ≤ P − (L+1) dim 𝒢`, **without `s`** (`Check3.lean`, example (i)). Weaker than the paper.
  - ReLU and ReGLU: `f_ℓ` is not differentiable, so **no Lean statement applies**.
  - attention: **not stated** (no attention block in Lean).
  - `ε = 0` with `𝒢 = CO(d)` (tex 276): **not stated**.
- The general statements hold for arbitrary differentiable `f_ℓ` and blocks of different kinds,
  which the paper's Theorem 4.3 does not claim.
- Empty `T` is allowed (the inequality is true: `fd = 0`).

Verdict: **PART**. For `tanh`, GELU, SwiGLU, GeGLU, in the cases (n) and (+): **SAME, with fewer
hypotheses**. For ReLU²: weaker conclusion (no `s`). For ReLU, ReGLU, attention and `ε = 0`: missing.

#### D Lemma C.2 (The directions that keep `C` and `A`), tex 550-556
Paper: "Let `E`, `D`, `W_read` and `W_write` have rank `d_model`. A direction `η` keeps `C` and `A` fixed to
first order, `𝐃_θ C η = 0` and `𝐃_θ A η = 0`, if and only if `η_E = EX, η_read = −X W_read, η_write = W_write Y, η_D = −YD`
for some `X, Y ∈ ℝ^{d×d}`. The matrices `X` and `Y` are determined by the direction, so these
directions form a space of dimension `2d²`."
Lean: `keeps_products_iff_mem_range_cobDir` (`OneBlock/Factorization.lean:48`), for `A : Arch T d 1`:
with the four ranks equal to `card d`,
`(η.E * θ.read 0 + θ.E * η.read 0 = 0 ∧ η.write 0 * θ.D + θ.write 0 * η.D = 0) ↔ ∃ X : Fin 2 → Matrix d d ℝ, η = cobDir θ X`.
Comparison: `𝐃_θ C η = η_E W_read + E η_read` and `𝐃_θ A η = η_write D + W_write η_D` are written out;
`X 0` is `X`, `X 1` is `Y`. The "if and only if": same. "`X` and `Y` are determined by the
direction": this is `cobDir_injective` (needs `E` and the write of rank `d`; the paper's proof uses
`E` and `D`). "A space of dimension `2d²`": not a separate statement; it is used inside
`funDim_mlp_oneBlock` (`finrank_cobDomain`).
Verdict: **SAME** for the equivalence; the last sentence is in other lemmas.

#### D Lemma C.3 (A flat direction only rescales units), tex 576-583
Paper: "Let every `a_i ≠ 0` and let the `c_i` be nonzero and pairwise non-collinear; for the gated
blocks let also every `e_i ≠ 0`, with `(e_i, β'_i)` not proportional to `(c_i, β_i)`. If
`𝐃_φ G(φ, x) ψ = 0` for all `x`, then `ψ_M = 0`, `ψ_γ = 0`, and for every unit `i`:
for `tanh` and GELU, `ψ_{a_i} = 0`, `ψ_{c_i} = 0` and `ψ_{β_i} = 0`;
for ReLU, `(ψ_{c_i}, ψ_{β_i}) = λ_i (c_i, β_i)` and `ψ_{a_i} = −λ_i a_i` for some number `λ_i`;
for ReLU², `(ψ_{c_i}, ψ_{β_i}) = λ_i (c_i, β_i)` and `ψ_{a_i} = −2λ_i a_i`;
for ReGLU, `(ψ_{c_i}, ψ_{β_i}) = λ_i (c_i, β_i)`, `(ψ_{e_i}, ψ_{β'_i}) = −α_i (e_i, β'_i)` and `ψ_{a_i} = (α_i − λ_i) a_i`;
for SwiGLU and GeGLU, `ψ_{c_i} = 0`, `ψ_{β_i} = 0`, `(ψ_{e_i}, ψ_{β'_i}) = −α_i (e_i, β'_i)` and `ψ_{a_i} = α_i a_i`."
with `𝐃_φ G(φ, x) ψ = xψ_M + ψ_γ + Σ_i [σ(z_i) ψ_{a_i} + σ'(z_i)(xψ_{c_i} + ψ_{β_i}) a_i]` (eq. (7), tex 570-572)
and, for a gated unit, the terms `σ(z_i) w_i ψ_{a_i} + σ'(z_i)(xψ_{c_i} + ψ_{β_i}) w_i a_i + σ(z_i)(xψ_{e_i} + ψ_{β'_i}) a_i`.

Lean (inputs `x : n → ℝ`, hidden units `q`, outputs `k`, all finite types; `c : q → n → ℝ`, `β : q → ℝ`, `a : q → k → ℝ`):

| Kind | Lean | Hypotheses | Conclusion | Verdict |
|---|---|---|---|---|
| `tanh` | `tanh_units_flat_eq_zero` (`OneBlock/UnitsTanh.lean:404`) | `∀ i, a i ≠ 0`; `∀ i, c i ≠ 0`; `∀ i j, i ≠ j → ∀ r, c i ≠ r • c j`; the identity for all `x`, with `σ' = 1 − tanh²` | `ψM = 0 ∧ ψγ = 0 ∧ ψc = 0 ∧ ψβ = 0 ∧ ψa = 0` | **SAME** |
| GELU | `gelu_units_flat_eq_zero` (`OneBlock/UnitsGELU.lean:503`) | the same, with `gelu`, `geluDeriv` | the same | **SAME** |
| ReLU | `relu_units_flat` (`OneBlock/UnitsReLU.lean:334`) | the same, the identity only at the `x` with `∀ i, x ⬝ᵥ c i + β i ≠ 0`, with `relu`, `reluDeriv` | `ψM = 0 ∧ ψγ = 0 ∧ ∃ lam, ∀ i, ψc i = lam i • c i ∧ ψβ i = lam i * β i ∧ ψa i = -(lam i) • a i` | **SAME** (the restriction to inputs off the kinks is the paper's convention, tex 535) |
| ReLU² | `reluSq_units_flat` (`:421`) | the same, off the kinks, with `reluSq`, `reluSqDeriv` | `… ψa i = -(2 * lam i) • a i` | **SAME** (hypothesis only off the kinks; by continuity this is the hypothesis for all `x`) |
| ReGLU | `relu_gated_units_flat` (`OneBlock/UnitsReGLU.lean:426`) | also `∀ i, e i ≠ 0` and `∀ i r, (e i, β' i) ≠ r • (c i, β i)`; the identity at the `x` with no gate at `0` | `ψM = 0 ∧ ψγ = 0 ∧ ∃ lam α, ∀ i, ψc i = lam i • c i ∧ ψβ i = lam i * β i ∧ ψe i = -(α i) • e i ∧ ψβ' i = -(α i) * β' i ∧ ψa i = (α i - lam i) • a i` | **SAME** |
| SwiGLU | `silu_gated_units_flat` (`OneBlock/UnitsSwiGLU.lean:649`) | as the paper (with the hypothesis on proportionality, named `_hec`, not used) | `ψM = 0 ∧ ψγ = 0 ∧ ψc = 0 ∧ ψβ = 0 ∧ ∃ α, ∀ i, ψe i = -(α i) • e i ∧ ψβ' i = -(α i) * β' i ∧ ψa i = α i • a i` | **SAME** |
| SwiGLU | `silu_gated_units_flat_of_value_ne_zero` (`:612`) | without the hypothesis on proportionality | the same | **LEAN STRONGER** |
| GeGLU | `gelu_gated_units_flat` (`OneBlock/UnitsGeGLU.lean:682`), `gelu_gated_units_flat_of_value_ne_zero` (`:646`) | as for SwiGLU, with `gelu`, `geluDeriv` | the same | **SAME**, resp. **LEAN STRONGER** |

Notes: "pairwise non-collinear" is `c i ≠ r • c j` for all `r` and all ordered pairs `i ≠ j`. "Not
proportional" is `(e i, β' i) ≠ r • (c i, β i)` for all `r` (`r = 0` is excluded by `e i ≠ 0`
already). The derivatives used (`1 − tanh²`, `geluDeriv`, `siluDeriv`, `reluDeriv`) are the true
derivatives (`hasDerivAt_tanh`, `hasDerivAt_gelu`, `hasDerivAt_silu`, `hasDerivAt_relu` for `z ≠ 0`).
With no hidden unit (`q` empty) the statements reduce to `xψ_M + ψ_γ = 0 ⇒ ψ_M = 0, ψ_γ = 0`.
All seven kinds of the lemma are stated. The forms that the one-block theorems use are
`UnitsRigid σ σ' n k q` (`OneBlock/Mlp.lean:33`) and `GatedUnitsRescale σ σ' n k q`
(`OneBlock/Gated.lean:42`, without the hypothesis on proportionality).

#### D Theorem 5.1 (One block), tex 319-321, and Theorem C.1, tex 527-533
Paper (5.1): "Let `L = 1`, without normalization, with a `tanh`, GELU, ReLU, ReLU², ReGLU, SwiGLU,
GeGLU or attention block. At generic parameters the functional dimension is `P − 2d² − s`, so the
network satisfies the equality condition." Paper (C.1): "Let `d ≥ 2` and `d_in, d_out ≥ d`, let inputs
range over all of `ℝ^{T×d_in}`, and consider networks with one block, without normalization and
without biases. The block is a `tanh`, GELU, ReLU, ReLU², ReGLU, SwiGLU or GeGLU block with at least
`d` hidden units, or an attention block of `H` heads of width `d_h ≤ d` with `H d_h ≥ d`, causal or not,
on sequences of at least two tokens. At generic parameters the functional dimension is `P − 2d² − s`."
(`s = d_hidden` for SwiGLU and GeGLU, `0` for `tanh` and GELU, tex 648.)

Lean (`[Fintype T] [Nonempty T]`, `hid : Fin 1 → Type`, `μ` an additive Haar measure on the parameters):
- `ae_funDim_tanh_oneBlock` (`OneBlock/Tanh.lean:64`):
  `2 ≤ card d → card d ≤ card dIn → card d ≤ card dOut → card d ≤ card (hid 0) → ∀ᵐ θ ∂μ, funDim (Arch.mlp Real.tanh id hid) 0 θ + 2 * card d ^ 2 = finrank ℝ (Params (Arch.mlp Real.tanh id hid) dIn dOut)`.
- `ae_funDim_gelu_oneBlock` (`OneBlock/GELU.lean:50`): the same with `gelu`.
- `ae_funDim_swiglu_oneBlock` (`OneBlock/SwiGLU.lean:51`): the same hypotheses,
  `funDim (Arch.gated silu id hid) 0 θ + (2 * card d ^ 2 + card (hid 0)) = finrank ℝ (Params (Arch.gated silu id hid) dIn dOut)`.
- `ae_funDim_geglu_oneBlock` (`OneBlock/GeGLU.lean:51`): the same with `gelu` as the gate.
- Under the conditions of the proof: `funDim_tanh_oneBlock`, `funDim_gelu_oneBlock` (`OneBlockGeneric θ`),
  `funDim_swiglu_oneBlock`, `funDim_geglu_oneBlock` (`OneBlockGenericGated θ`); the conditions hold at
  generic parameters: `ae_oneBlockGeneric` (`OneBlock/Mlp.lean:259`), `ae_oneBlockGenericGated`
  (`OneBlock/Gated.lean:424`), both under exactly `2 ≤ card d`, `card d ≤ card dIn`, `card d ≤ card dOut`,
  `card d ≤ card (hid 0)`.
- For every activation with the conclusion of Lemma C.3: `funDim_mlp_oneBlock`, `ae_funDim_mlp_oneBlock`
  (`UnitsRigid`), `funDim_gated_oneBlock`, `ae_funDim_gated_oneBlock` (`GatedUnitsRescale`). These
  have no counterpart in the paper.

Comparison, for the four kinds: hypotheses `d ≥ 2`, `d_in, d_out ≥ d`, `d_hidden ≥ d`: same, one for
one. "`L = 1`": `Fin 1`. "Without normalization": `χ = id`. "Without biases": no biases. "Inputs range
over all of `ℝ^{T×d_in}`": the batches are of arbitrary `x : Matrix T dIn ℝ`, for any nonempty finite
`T`. Conclusion `fd = P − 2d² − s` as `fd + (2d² + s) = P`. Same. `s = card (hid 0)` for the gated
blocks. A gated block with `d_hidden` hidden units has the read `Matrix d (hid 0 ⊕ hid 0) ℝ`, so `P`
counts `2 d d_hidden` entries of the read. Same. `OneBlockGenericGated` leaves out the paper's "is
not proportional to `c_i`" (fewer conditions).
Cases: **4 of the 8 kinds of block.** Not stated: ReLU, ReLU², ReGLU (Lemma C.3 is proved for them,
but there is no theorem on the functional dimension), attention.
"So the network satisfies the equality condition": the equality condition is not defined in Lean; it
is the conjunction of this equality and Theorem 4.3.

Verdict: **PART** (`tanh`, GELU, SwiGLU, GeGLU: **SAME**; ReLU, ReLU², ReGLU, attention: missing).

#### D Theorem 5.2 (The bound is attained at any depth), tex 330-339
Paper: "Let `d_in, d_out ≥ d_model ≥ 2`, and consider networks without biases whose blocks are all of
one kind, `tanh`, GELU, SwiGLU or GeGLU, each with at least `d_model` hidden units. In the following
cases the functional dimension at generic parameters is `P − (L+1) dim 𝒢 − s`, so the network
satisfies the equality condition. (i) `tanh` blocks: without normalization, and under pre-RMSNorm
with `ε > 0` and with `ε = 0`. (ii) GELU blocks: under pre-RMSNorm with `ε > 0` and with `ε = 0`.
(iii) SwiGLU blocks, and GeGLU blocks: without normalization, and under pre-RMSNorm with `ε > 0`."

Lean (`Depth/Tanh.lean`):
```
theorem ae_funDim_tanh_skipless [Nonempty T]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) Real.tanh id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, funDim (Arch.mlp Real.tanh id hid) 0 θ + (L + 1) * Fintype.card d ^ 2
      = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) Real.tanh id hid) dIn dOut)
```
(`:223`; elaborated: `{T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)] [Nonempty T]`.)
With it: `funDim_tanh_skipless (hθ : TanhDepthGeneric θ)` (`:112`, the same equality at every `θ` that
satisfies the conditions of the proof), `TanhDepthGeneric` (`:33`, see 2.8),
`ae_tanhDepthGeneric [Nonempty d]` (`:140`): `card d ≤ card dIn → card d ≤ card dOut → (∀ ℓ, card d ≤ card (hid ℓ)) → ∀ᵐ θ ∂μ, TanhDepthGeneric θ`,
for every `χ`; `regular_of_tanhDepthGeneric` (`:65`), `claim_of_tanhDepthGeneric` (`:101`).

Comparison for (i), without normalization:
- "`d_in, d_out ≥ d ≥ 2`": `hdIn`, `hdOut`, `hd`. Same. (`funDim_tanh_skipless` and `ae_tanhDepthGeneric`
  need only `d ≥ 1`; the final statement keeps the paper's `d ≥ 2`.)
- "each with at least `d` hidden units": `hhid`, for every block; the widths may differ. Same.
- "blocks all `tanh`", "without biases", "without normalization": `Arch.mlp Real.tanh id hid`. Same.
- "at generic parameters": `∀ᵐ θ ∂μ`, `μ` any additive Haar measure. Same.
- Conclusion: `P − (L+1) dim 𝒢 − s` with `dim 𝒢 = d²`, `s = 0`, as `fd + (L+1) d² = P`. Same.
- Depth: any `L : ℕ`, also `L = 0` (the linear network; true). Tokens: any nonempty finite `T`.
- The conditions under which Lean proves the equality are those of the paper's proof (tex 1574),
  and Lean proves that they hold almost everywhere under the paper's hypotheses
  (`ae_tanhDepthGeneric`, with `d ≥ 1` in place of `d ≥ 2`).
- I looked for a degenerate case in which the Lean statement says more or less than the paper:
  empty `T` is excluded by `[Nonempty T]`; `d ≤ 1` is excluded by `hd`; a block with fewer than `d`
  hidden units is excluded by `hhid`; `d_in < d` or `d_out < d` by `hdIn`, `hdOut`. None found.

Cases of the theorem: **1 of 7.** Stated: (i) without normalization. Not stated: (i) under
pre-RMSNorm with `ε > 0` and with `ε = 0`; (ii) (GELU, `ε > 0` and `ε = 0`); (iii) (SwiGLU and GeGLU,
without normalization and `ε > 0`). (`TanhDepthGeneric`, `regular_of_tanhDepthGeneric` and
`ae_tanhDepthGeneric` are already stated for every `χ`, as a preparation for the case (+).)

Verdict: **PART**; the case "(i), `tanh`, without normalization" is **SAME**.

#### D Appendix D.1/D.3: `𝓑_{>k}`, the identity (16), Claim `(D_k)`, "regular", tex 752-760, 879-897, 933-936
See 2.8. Lean: `suffix`, `suffix_last`, `suffix_castSucc`, `suffix_hidden`, `eval_eq_suffix_zero`,
`SuffixFlat`, `Claim`, `Regular` (`Depth/Suffix.lean:47-105`).
Verdict: **SAME in the case (n) for blocks without symmetries inside** (hidden states are `T × d`
matrices in Lean, rows in the paper); the cases (+) and (0), the form (19) of the claim for gated
blocks, and (R2) are **not defined**.

#### D Lemma D.1 (Separation on a ray), tex 787-793
Paper: "Let `u_1, …, u_q` be real numbers that are linearly independent over `ℚ`, and let
`𝒯_0, …, 𝒯_K` be real-analytic maps from `ℝ^{1×q}` to `ℝ^{1×d_out}`. If
`Σ_{i=0}^K t^i 𝒯_i(tanh(tu_1), …, tanh(tu_q)) = 0` for all `t > 0`, then `𝒯_i = 0` on `ℝ^{1×q}` for every `i`."
Lean: `tanh_ray_separation` (`Depth/RaySeparation.lean:447`): `{ι} [Fintype ι] {F} [NormedAddCommGroup F] [NormedSpace ℝ F] (u : ι → ℝ) (hu : LinearIndependent ℚ u) (K : ℕ) (𝒯 : Fin (K + 1) → (ι → ℝ) → F) (h𝒯 : ∀ i, AnalyticOnNhd ℝ (𝒯 i) Set.univ) (h : ∀ t : ℝ, 0 < t → ∑ i : Fin (K + 1), t ^ (i : ℕ) • 𝒯 i (fun j => Real.tanh (t * u j)) = 0) : ∀ i w, 𝒯 i w = 0`.
Also `tanh_ray_separation_matrix` (`:551`, the `u` arranged in a matrix `T × q`) and the middle step
`eventually_eq_zero_of_sum_pow_mul_exp_ray` (`:279`).
Comparison: indices `0, …, K` are `Fin (K+1)`; the target is any real normed space `F` (the paper:
`ℝ^{1×d_out}`); "for all `t > 0`"; conclusion for all `w`. `q = 0` allowed (then the `𝒯_i` are
constants and the statement is true).
Verdict: **SAME** (target space more general).

#### D Lemma D.2 (The derivative of `𝓑_{>k}`), tex 899-901
Paper: "Let `θ` be regular. For every `k` there is an open dense set `𝒰_k` of rows such that, for
`h ∈ 𝒰_k`, `𝐃𝓑_{>k}(h) v = 0` only if `v = 0`, in the cases (n) and (+), and only if `v ∈ ℝh`, in the
case (0). In the case (0), `𝒰_k` consists of rows `h ≠ 0` and is closed under multiplication by
positive numbers."
Lean: `exists_open_dense_injective_fderiv_suffix (hχ : A.χ = id) (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (hθ : Regular A θ) (k : Fin (L + 1)) : ∃ U : Set (Matrix T d ℝ), IsOpen U ∧ Dense U ∧ ∀ h ∈ U, Function.Injective (fderiv ℝ (fun h' => suffix A 0 θ k h') h)` (`Depth/Suffix.lean:408`).
Comparison: case (n) only. "`𝐃𝓑_{>k}(h) v = 0` only if `v = 0`" is injectivity of the derivative.
The blocks are any real-analytic maps `f_ℓ` (the paper: `tanh`, GELU, SwiGLU, GeGLU blocks, which are
analytic). Hidden states are `T × d` matrices; no `[Nonempty T]` is needed.
Verdict: **PART** (case (n): **SAME**, for more general blocks; cases (+) and (0): not stated).

#### D Lemma D.3 (A direction at a write), tex 917-926
Paper: "Let `θ` be regular, `0 ≤ k ≤ L`, and let `A` be a matrix with `d_model` columns and rank
`d_model`. Let `η_A` be a matrix of the size of `A` and `η` a direction of the weights of the blocks
`k+1, …, L` and of `D`. If `𝐃𝓑_{>k}(wA)(w η_A) + 𝐃_θ𝓑_{>k}(wA) η = 0` for all rows `w`, with `wA ≠ 0`
in the case (0), then `η_A = AZ` for a `d × d` matrix `Z`, and [the identity (16) holds]."
Lean: `suffixFlat_of_flat_at_write [Nonempty T] (hχ : A.χ = id) (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (hθ : Regular A θ) (k : Fin (L + 1)) {m : Type*} [Fintype m] (M : Matrix m d ℝ) (hM : M.rank = Fintype.card d) (ηM : Matrix m d ℝ) (η : Params A dIn dOut) (h : ∀ w : Matrix T m ℝ, fderiv ℝ (fun h' => suffix A 0 θ k h') (w * M) (w * ηM) + fderiv ℝ (fun θ' => suffix A 0 θ' k (w * M)) θ η = 0) : ∃ Z : Matrix d d ℝ, ηM = M * Z ∧ SuffixFlat A θ k Z η` (`:460`).
Comparison: one for one, in the case (n), with `w` a `T × m` matrix. `[Nonempty T]` is needed (the
paper has one token).
Verdict: **PART** (case (n): **SAME**; cases (+) and (0): not stated).

#### D Proposition D.4 (The claim gives the rank), tex 953-955
Paper: "Let `θ` be regular, with no vanishing value column if the blocks are gated, and let `(D_0)`
hold at `θ`. Then the directions `η ∈ ℝ^P` with `𝐃_θ F(θ, x) η = 0` for all `x`, with `xE ≠ 0` in the
case (0), are the directions `η^Z` of (11), or `η^{Z,Δ}` of (12) for gated blocks, and the Jacobian
of the network has the rank (13) on some finite batch of such inputs."
Lean: `flat_le_range_cobDir_of_claim [Nonempty T] (hχ : A.χ = id) (hf : …analytic…) (hθ : Regular A θ) (h0 : Claim A θ 0) (η) (hη : η ∈ flat A 0 θ) : ∃ X : Fin (L + 1) → Matrix d d ℝ, η = cobDir θ X` (`:512`);
`funDim_of_claim` (same hypotheses): `funDim A 0 θ + (L + 1) * Fintype.card d ^ 2 = Module.finrank ℝ (Params A dIn dOut)` (`:536`).
Comparison: case (n), blocks without symmetries inside. "are the directions `η^Z`": Lean states the
inclusion flat ⊆ {`cobDir θ X`}; the other inclusion is `cobDir_mem_flat_skipless`. "The Jacobian has
the rank (13) on some finite batch": Lean states `fd = P − (L+1)d²`, and `fd` is attained on a finite
batch (`exists_jacobianRank_eq_funDim`). Lean's conclusion is the paper's together with the upper
bound, which the paper adds in the proof of the theorem.
Verdict: **PART** (case (n), no gated blocks: **SAME**; gated blocks and the cases (+), (0): not stated).

#### D Lemma D.5 (The readout), tex 965-967
Paper: "If `D` has rank `d_model`, then `(D_L)` holds."
Lean: `claim_last [Nonempty T] (hχ : A.χ = id) : Claim A θ (Fin.last L)` (`:144`).
Comparison: case (n) only. **No hypothesis on the rank of `D`**: in the case (n) the paper's proof
does not use it ("(16) is `hZD + h η_D = 0` for all rows `h`, so `η_D = −ZD`").
Verdict: **PART** (case (n): **LEAN STRONGER**, the rank of `D` is not assumed; cases (+), (0): not stated).

#### D equations (20)-(22) and Lemma D.6 (The identity at every real row), tex 983-999
Paper: "`ż(n) = nZW + nη_W` in the case (n)"; "`𝓛(w̃, w̃'; n) = 𝐃𝓑(w̃V)((w̃' ⊙ ż(n)) V + w̃ η_V) + 𝐃_θ𝓑(w̃V) η'`";
"So (16) for `k` is equivalent to `𝓛(σ(nW), σ'(nW); n) = 0` for all values `n` of `χ`"; Lemma D.6: "In
the cases (n) and (+), (16) for `k` holds if and only if `𝓛(σ(nW), σ'(nW); n) = 0` for every row `n`."
Lean: `blockLHS` (`Depth/StepTanh.lean:49`, see 2.8) and
`suffixFlat_castSucc_iff_mlp (hσ : ∀ z, HasDerivAt σ (σ' z) z) (θ : Params (Arch.mlp σ id hid) dIn dOut) (k : Fin L) (Z) (η) : SuffixFlat (Arch.mlp σ id hid) θ k.castSucc Z η ↔ ∀ n : Matrix T d ℝ, blockLHS θ k η ((n * θ.read k).map σ) ((n * θ.read k).map σ') (n * (Z * θ.read k + η.read k)) = 0` (`:113`).
Comparison: case (n), for an MLP block with any differentiable `σ`; Lean block `k` is the paper's
block `k+1`; `ż(n) = n(ZW + η_W)`. In the case (n), (22) and Lemma D.6 are the same statement.
Verdict: **PART** (case (n): **SAME**; the case (+) of Lemma D.6, which is its content, is not stated).

#### D Lemma D.7 (The step for `tanh` on rays), tex 1024-1032
Paper: "(T1) no row of `V` vanishes; (T2) the columns of `W` are linearly independent over `ℚ`." "Let
`σ = tanh`, in the case (n) or (+), let `θ` be regular, and let block `k+1` satisfy (T1) and (T2). Then
`(D_{k+1})` implies `(D_k)`."
Lean: `claim_castSucc_tanh [Nonempty T] (hθ : Regular (Arch.mlp Real.tanh id hid) θ) (k : Fin L) (hT1 : ∀ i : hid k, θ.write k i ≠ 0) (hT2 : LinearIndependent ℚ (fun j : hid k => fun i : d => θ.read k i j)) (hk : Claim (Arch.mlp Real.tanh id hid) θ k.succ) : Claim (Arch.mlp Real.tanh id hid) θ k.castSucc` (`Depth/StepTanh.lean:400`).
With it: `dense_setOf_linearIndependent_mul` (`:212`), `eq_zero_of_fderiv_suffix_one_sub_sq` (`:283`, "the fact").
Comparison: Lean block `k : Fin L` is the paper's block `k+1`; `k.succ`, `k.castSucc` are the hidden
states after and before it. (T1), (T2), regular: same. Case (n) only.
Verdict: **PART** (case (n): **SAME**; case (+): not stated).

#### D proof of Theorem 5.2, "`tanh` blocks in the cases (n) and (+)", tex 1574
Paper: "Let `θ` satisfy (R1), let every block satisfy (T1) and (T2), and let every `W_read^ℓ W_write^ℓ`
be invertible. These conditions fail only on a set of measure zero … Such `θ` are regular."
Lean: `TanhDepthGeneric` (`Depth/Tanh.lean:33`), `ae_tanhDepthGeneric` (`:140`),
`regular_of_tanhDepthGeneric` (`:65`). **SAME** (for every `χ`; `Regular` is the notion of the cases
(n) and (+)).

#### Helper rows of the index for the dimension paper (not statements of the paper)
`differentiable_eval`; `volume_zeroSet_of_analytic_pi`, `measure_zeroSet_of_analytic` (a real-analytic
function on a finite-dimensional space that is not identically zero vanishes on a null set of every
additive Haar measure; the paper uses this fact without a statement); `ae_rank_E_write`;
`gaussPdf`, `gaussCdf`, `gelu` and their properties; `le_one_sub_gaussCdf`, `one_sub_gaussCdf_le`
(paper, tex 605: "`φ(z)(1/z − 1/z³) ≤ Φ̄(z) ≤ φ(z)/z` for `z > 0`": **SAME**); `gelu_expansion_pos/neg`,
`geluDeriv_expansion_pos/neg` (paper, tex 606-609: `σ(z) = max(z,0) − φ(z) + O(φ(z)/z²)`,
`σ'(z) = 1[z>0] + φ(z)(z − 1/z) + O(φ(z)/|z|³)`: Lean gives explicit two-sided bounds for all `z > 0`
and all `z < 0`, **LEAN STRONGER**); `hasDerivAt_gelu`, `gelu_sub_gelu_neg` (paper, tex 805:
"`σ(z) − σ(−z) = z`": **SAME**); `relu`, `reluSq` and their derivatives; `analyticOnNhd_tanh`,
`analyticOnNhd_matrix_entry`, `analyticOnNhd_f_mlp`; the chain rules of `Depth/Suffix.lean` and
`Depth/StepTanh.lean` (paper, tex 897: "In the cases (n) and (+), every `𝓑_{>k}` is real-analytic on
all rows `h`": `analyticOnNhd_suffix`, case (n), **SAME**); the helpers of `OneBlock/Common.lean`. I
read their statements; each says what the index says, with the one exception listed in (4b).


### 3.B Skips paper

#### S Definition 3.1 (Change of basis), tex 246-252; S eq. (6), tex 264-268; S eq. (7), tex 278-280
Definition 3.1 is D Definition 3.1 with "An identity skip has no weights, and a change of basis leaves
it in place": `Params.cob` does not touch the stream matrices; see 2.3 (**DIFFERENT object, on purpose**).
Eq. (6): "the maps (4), together with `A_ℓ ↦ G_{ℓ-1}⁻¹ A_ℓ G_ℓ` for every skip, preserve the function of
the network: every hidden state `h_ℓ` becomes `h_ℓ G_ℓ`". Lean: `eval_cob` and `hidden_cob` with
`cobSkip` (`Symmetry/ChangeOfBasis.lean:30-67`), under the hypothesis `∀ ℓ h, A.χ (h * G ℓ) = A.χ h * K ℓ`
(true with `K = G` for `χ = id`, which is the paper's setting there). **SAME** (Lean more general:
any `χ` with this property).
Eq. (7): `skipProd`, `skipProd_last`, `skipProd_castSucc`; see 2.9. **SAME**.

#### S Theorem 3.2 (Learned skips reduce to identity skips), tex 287-290
Paper: "(i) Without normalization, let every learned skip `A_ℓ` be invertible, and let
`Λ_ℓ = A_{ℓ+1} ⋯ A_L`, with `Λ_L = I`. The network with learned skips computes the same function as the
residual network with the embedding `EΛ_0`, the reads `Λ_{ℓ-1}⁻¹ W_read^ℓ`, the writes `W_write^ℓ Λ_ℓ` and
the readout `D`. (ii) Under pre-RMSNorm, the same holds when every `A_ℓ` is orthogonal. When every
`A_ℓ` is invertible, there are orthogonal `Q_1, …, Q_L`, with `Q_0 = I`, such that every
`Q_{ℓ-1}ᵀ A_ℓ Q_ℓ` is upper triangular, and the network with these skips, the reads `Q_{ℓ-1}ᵀ W_read^ℓ`,
the writes `W_write^ℓ Q_ℓ` and the readout `Q_Lᵀ D` computes the same function."

Lean:
- (i) `eval_learned_eq_residual (hA : A.χ = id) (S : Fin L → GL d ℝ) : eval A (fun ℓ => (S ℓ : Matrix d d ℝ)) θ x = eval A 1 (θ.cob (skipProd S) (skipProd S)) x`
  (`Residual/LearnedSkips.lean:77`) and `cob_skipProd_D : (θ.cob (skipProd S) (skipProd S)).D = θ.D` (`:90`).
- (ii), first sentence: `eval_learned_eq_residual_rmsNorm (ε : ℝ) (hA : A.χ = rmsNorm ε) (S : Fin L → GL d ℝ) (hS : ∀ ℓ, (S ℓ : Matrix d d ℝ) ∈ orthogonalGroup d ℝ)`, the same conclusion (`:98`).
- (ii), second sentence: `exists_cob_learned_upperTriangular [LinearOrder d] (ε : ℝ) (hA : A.χ = rmsNorm ε) (S : Fin L → Matrix d d ℝ) (θ) : ∃ Q : Fin (L + 1) → GL d ℝ, Q 0 = 1 ∧ (∀ ℓ, (Q ℓ : Matrix d d ℝ) ∈ orthogonalGroup d ℝ) ∧ (∀ ℓ, (cobSkip S Q ℓ).BlockTriangular id) ∧ ∀ x, eval A (cobSkip S Q) (θ.cob Q Q) x = eval A S θ x`
  (`Residual/OneChangeOfBasis.lean:330`), with `exists_orthogonal_mul_upperTriangular` (`:313`).

Comparison: (i) "every learned skip invertible" is `S : Fin L → GL d ℝ`; `θ.cob Λ Λ` has the embedding
`E Λ_0`, the reads `Λ_{ℓ-1}⁻¹ W_read^ℓ`, the writes `W_write^ℓ Λ_ℓ` and the readout `Λ_L⁻¹ D = D`
(`cob_skipProd_D`); the residual network is `eval A 1`. One for one. (ii), first sentence: one for
one, for any real `ε` (the paper: `ε > 0`). (ii), second sentence: the new skips are
`cobSkip S Q ℓ = Q_ℓ⁻¹ A_{ℓ+1} Q_{ℓ+1}` in Lean indices, the paper's `Q_{ℓ-1}ᵀ A_ℓ Q_ℓ`; `Q 0 = 1`; the
reads, writes and readout are those of `θ.cob Q Q`. Lean does **not** assume the `A_ℓ` invertible and
allows any real `ε`.
Verdict: **SAME** ((ii), second sentence: **LEAN STRONGER**, no invertibility).

#### S Theorem 3.3 (One change of basis for the whole network), tex 305-310
Paper: "With or without pre-RMSNorm, let `G_0, …, G_L` be invertible `d × d` matrices.
(i) The map `E ↦ EG_0`, `W_read^ℓ ↦ G_{ℓ-1}⁻¹ W_read^ℓ`, `W_write^ℓ ↦ W_write^ℓ G_ℓ`, `D ↦ G_L⁻¹ D` preserves the
function of every residual network if and only if `G_0 = G_1 = ⋯ = G_L ∈ 𝒢`.
(ii) The changes of basis that preserve the function at all parameters form a group of dimension
`(L+1) dim 𝒢` in a skipless network and `dim 𝒢` in a residual one: `(L+1)d²` and `d²` without
normalization, and `(L+1)d(d−1)/2` and `d(d−1)/2` under pre-RMSNorm.
(iii) In a residual network, let `d` columns of one of the reads `W_read^1, …, W_read^L, D` form an
invertible matrix `W_1`. The same change of basis at all hidden states preserves the function and
turns `W_1` into the identity, for `G = W_1` without normalization, and into the upper triangular `R`,
for the factor `Q` of `W_1 = QR` under pre-RMSNorm."
(In the appendix, Theorem A.5 (iii), tex 597: "Let `d ≥ 2`, and let every block be nonzero for some
value of its parameters. Without normalization or with pre-RMSNorm and `ε > 0` …".)

Lean:
- (i) "if": `eval_cob_residual (hA : A.χ = id) (G₀ : GL d ℝ) : eval A 1 (θ.cob (fun _ => G₀) (fun _ => G₀)) x = eval A 1 θ x`
  (`Symmetry/ChangeOfBasis.lean:86`); `eval_cob_residual_rmsNorm (ε : ℝ) (hA : A.χ = rmsNorm ε) (Q : GL d ℝ) (hQ : orthogonal)` (`Residual/LearnedSkips.lean:115`).
- (i) "only if" and the equivalence, without normalization (`Residual/OneChangeOfBasis.lean:116, 171`):
  `eval_cob_residual_iff [Nonempty T] [Nonempty dIn] [Nonempty dOut] (hA : A.χ = id) (hne : ∀ ℓ, ∃ (x : Matrix T dIn ℝ) (E : Matrix dIn d ℝ) (W : Matrix d (A.r ℓ) ℝ), A.f ℓ (x * E * W) ≠ 0) (G : Fin (L + 1) → GL d ℝ) : (∀ (θ : Params A dIn dOut) (x : Matrix T dIn ℝ), eval A 1 (θ.cob G G) x = eval A 1 θ x) ↔ ∀ ℓ, G ℓ = G 0`.
- (i) under pre-RMSNorm (`:221, 295`): `eval_cob_residual_rmsNorm_iff … (hε : 0 < ε) (hA : A.χ = rmsNorm ε) (hne : ∀ ℓ, ∃ x E W, A.f ℓ (rmsNorm ε (x * E) * W) ≠ 0) (G) : (∀ θ x, eval A 1 (θ.cob G G) x = eval A 1 θ x) ↔ (∀ ℓ, G ℓ = G 0) ∧ (G 0 : Matrix d d ℝ) ∈ orthogonalGroup d ℝ`.
- (iii): `exists_cob_residual_read_eq_one` (read of a block, no normalization, `Residual/LearnedSkips.lean:131`),
  `exists_cob_residual_D_eq_one` (readout, no normalization, `:145`),
  `exists_cob_residual_read_upperTriangular` (read of a block, pre-RMSNorm, `:161`).

Comparison:
- (i): "`G_0, …, G_L` invertible": `G : Fin (L+1) → GL d ℝ`. The map is `θ.cob G G`. "Preserves the
  function of every residual network": in Lean, for every value `θ` of the parameters of one fixed
  architecture `A` and every input `x` (this is how the paper's proof reads it: "let `G_0, …, G_L`
  preserve the function for all parameter values", tex 619). "`= ⋯ = G_L ∈ 𝒢`": all equal to `G 0`,
  and `G 0` orthogonal under pre-RMSNorm. Same.
- The hypothesis `hne` ("every block is nonzero at some input of the form `xEW`") is the hypothesis
  of Theorem A.5 (iii), which the main-text statement leaves to the Scope. Lean does **not** assume
  `d ≥ 2` (Theorem A.5 (iii) does). `[Nonempty T]`, `[Nonempty dIn]`, `[Nonempty dOut]` are tacit in
  the paper. The blocks are arbitrary maps `f_ℓ` with `hne`.
- (i) for `ε = 0` (Theorem A.5 (iii), last sentence; not part of Theorem 3.3, whose RMSNorm has `ε > 0`): not stated.
- (ii) (the dimensions of the groups): **not stated**.
- (iii): Lean has three of the four cases; **the readout `D` under pre-RMSNorm is not stated.** In the
  two statements without normalization the hypothesis and conclusion are the paper's (`∃ G`, and the
  new submatrix is `1`, which forces `G = W_1`). The pre-RMSNorm statement needs no invertibility and
  holds for any real `ε`.

Verdict: (i) **SAME** (hypothesis of Theorem A.5 (iii) made explicit; no `d ≥ 2`). (ii) **not stated**.
(iii) **PART** (the readout under pre-RMSNorm is missing).

#### S Definition 4.1 (Functional dimension), tex 330-336
The same text as D Definition 4.1. Lean: `funDim A S θ` with the stream matrices `S` (`0` without
skips, `1` with identity skips). **SAME**.

#### S Theorem 4.2 (Upper bounds), tex 342-344
Paper: "Let `𝒢` be the group of changes of basis of one hidden state, and `s` the dimension of the
symmetries inside the blocks, the same with and without skips. With or without pre-RMSNorm, at
generic parameters, the functional dimension is at most `P − (L+1) dim 𝒢 − s` without skips and at
most `P − dim 𝒢 − s` with identity skips."

Lean, with identity skips:
- `funDim_add_le_residual (hA : A.χ = id) (hf : ∀ ℓ, Differentiable ℝ (A.f ℓ)) (hE : θ.E.rank = card d) : funDim A 1 θ + card d ^ 2 ≤ finrank ℝ (Params A dIn dOut)` (`Dimension/UpperBound.lean:226`);
- `funDim_add_le_residual_rmsNorm (hε : 0 < ε) (hA : A.χ = rmsNorm ε) (hf) (hE) : funDim A 1 θ + card d * (card d - 1) / 2 ≤ finrank …` (`Dimension/UpperBoundRMSNorm.lean:310`);
- `ae_funDim_add_le_residual`, `ae_funDim_add_le_residual_rmsNorm` (`Generic/Params.lean:196, 203`): the
  same `∀ᵐ θ ∂μ` under `card d ≤ card dIn`.
- `cobDir_const_mem_flat_residual` (`Dimension/UpperBound.lean:207`), `rescaleDir_mem_flat_stream` (`Dimension/Rescaling.lean:156`).
Without skips: the statements of D Theorem 4.3 above.

Comparison:
- With identity skips Lean states the bound **without `s`** only: `fd ≤ P − dim 𝒢`. For `tanh` and
  GELU blocks (`s = 0`) this is the paper's bound. For gated blocks the rescalings are known to be
  flat with skips (`rescaleDir_mem_flat_stream`), but no Lean statement combines them with the one
  change of basis into `fd ≤ P − dim 𝒢 − s` for a residual network of any depth (for one block the
  equality `funDim_gated_oneBlock_residual` contains it).
- Hypotheses with skips: only `d_in ≥ d` (the embedding of rank `d`). No condition on the widths,
  on `d_out` or `d ≥ 2`. Fewer hypotheses than the paper's Scope.
- ReLU, ReGLU (not differentiable), attention: no statement applies. ReLU²: bound without `s`.

Verdict: **PART**. With identity skips: `s = 0` blocks (`tanh`, GELU, and any differentiable block
if `s` is dropped): **SAME with fewer hypotheses**; the term `s` for a residual network: **not stated**
(except `L = 1`, gated). Without skips: as D Theorem 4.3.

#### S Theorem 4.6 (Equality for one block), tex 374-378, Theorem B.1, tex 1216-1223, Lemma B.2, tex 1246-1252
Paper (4.6): "Let `L = 1`, with a `tanh`, GELU, ReLU, ReLU², ReGLU, SwiGLU, GeGLU or attention block.
(i) Without normalization, the residual network satisfies the equality condition. So does the
skipless network, and the skip raises the functional dimension by exactly `d²`. (ii) Under RMSNorm,
the residual network satisfies the equality condition, and the skip raises the functional dimension
by at least `d(d−1)/2`. A learned skip raises it by exactly `d(d+1)/2` more than an identity skip."
Paper (B.1 (i)): "Let the network have no normalization, with or without biases, and let the block
have width at least `d`… For generic parameters the skipless network has functional dimension
`P − 2d² − s` and the residual network `P − d² − s`; … Both networks satisfy the equality condition,
and the skip raises the functional dimension by exactly `d²`."
Paper (B.2): "… it keeps `M` fixed as well, `𝐃_θ M η = 0`, if and only if moreover `X = Y`."

Lean (`OneBlock/Residual.lean`, `[Nonempty T]`, `hid : Fin 1 → Type`, hypotheses
`2 ≤ card d`, `card d ≤ card dIn`, `card d ≤ card dOut`, `card d ≤ card (hid 0)`):
- `ae_funDim_tanh_oneBlock_residual_eq_add` (`:729`): `∀ᵐ θ ∂μ, funDim (Arch.mlp Real.tanh id hid) 1 θ = funDim (Arch.mlp Real.tanh id hid) 0 θ + card d ^ 2`;
  `ae_funDim_gelu_oneBlock_residual_eq_add` (`:739`), `ae_funDim_swiglu_oneBlock_residual_eq_add` (`:749`),
  `ae_funDim_geglu_oneBlock_residual_eq_add` (`:759`): the same for `Arch.mlp gelu`, `Arch.gated silu`, `Arch.gated gelu`.
- `ae_funDim_mlp_oneBlock_residual` (`:304`): for `σ` with `UnitsRigid σ σ' dIn dOut (hid 0)`,
  `∀ᵐ θ ∂μ, funDim (Arch.mlp σ id hid) 1 θ + card d ^ 2 = finrank …`; `ae_funDim_gated_oneBlock_residual`
  (`:701`): for a gate with `GatedUnitsRescale`, `funDim (Arch.gated σ id hid) 1 θ + (card d ^ 2 + card (hid 0)) = finrank …`;
  and under the conditions of the proof `funDim_mlp_oneBlock_residual` (`:268`), `funDim_gated_oneBlock_residual` (`:638`),
  `flat_le_range_cobDir_const_mlp_residual` (`:229`), `flat_le_cobDir_const_add_rescaleDir_gated_residual` (`:538`).

Comparison for (i):
- "the skip raises the functional dimension by exactly `d²`": `fd(residual, θ) = fd(skipless, θ) + d²`
  at the same `θ`, almost everywhere. Same. (Both networks have the same parameter space.)
- "the residual network satisfies the equality condition": `fd + d² + s = P` at generic parameters.
  Stated for a general `σ` (`ae_funDim_mlp_oneBlock_residual`, `ae_funDim_gated_oneBlock_residual`);
  for the four named kinds there is no theorem with the name of the kind, but the four `_eq_add`
  corollaries are obtained from these with `tanh_unitsRigid`, `gelu_unitsRigid`,
  `silu_gatedUnitsRescale`, `gelu_gatedUnitsRescale`, so the statement for each kind is one
  application away (checked for `tanh`: `Check3.lean`, example (j)).
- Hypotheses: `d ≥ 2`, `d_in, d_out ≥ d`, width `≥ d`. Same as B.1 (i).
- Cases: **4 of 8 kinds** (`tanh`, GELU, SwiGLU, GeGLU). Not stated: ReLU, ReLU², ReGLU, attention.
  **Without biases only**: B.1 (i) also has "with biases … both values are `2d` lower".
- Lemma B.2: the part on `C` and `A` is `keeps_products_iff_mem_range_cobDir`; the part "keeps `M` …
  if and only if moreover `X = Y`" exists only as a private helper (`eq_const_of_keeps_ED`,
  `OneBlock/Residual.lean:78`, the direction "only if"); the statement with biases is not there.
- (ii) (under RMSNorm) and B.1 (ii)-(v): **not stated**.

Verdict: **PART**. (i) for `tanh`, GELU, SwiGLU, GeGLU without biases: **SAME**.


---------------------------------------------------------------------------------------------------

## (4) Lists

### (4a) Statements of the two main texts with no Lean statement, or with a part missing

Dimension paper, main text (Sections 2-6):

| Statement | In Lean? |
|---|---|
| Definition 3.1 | defined (`Params.cob`, all hidden states at once) |
| Proposition 3.2 | stated, all three cases |
| Proposition 3.3 | stated in the simultaneous form; missing: the one-hidden-state form of (i), the rows of a write under pre-RMSNorm, the count "remove `(L+1) dim 𝒢` parameters" |
| Definition 4.1 | defined |
| Example 4.2 (the linear network `x ↦ xM_1M_2M_3`) | **no** |
| Theorem 4.3 | part: missing the term `s` for ReLU², every statement for ReLU, ReGLU and attention blocks, and the remark for `ε = 0` with `𝒢 = CO(d)` (tex 276) |
| Definition 4.4 (Equality condition) | **no** (no definition; the equalities are stated directly) |
| Definition 4.5 (Identifiability up to symmetries) | **no** |
| Proposition 4.6 (The equality condition and local identifiability) | **no** |
| Theorem 5.1 | part: `tanh`, GELU, SwiGLU, GeGLU; missing ReLU, ReLU², ReGLU, attention |
| Theorem 5.2 | part: (i) without normalization only; missing (i) for `ε > 0` and `ε = 0`, (ii), (iii) |
| Corollary 5.3 (Local identifiability) | **no** |
| Conjecture 1 | not a statement to prove |

Dimension paper, appendices that the main results rest on, without a Lean statement: Proposition A.3
itself (only its computations); Lemma B.1 in the group form and for ReLU, ReLU², ReGLU, attention;
Remark B.2; Theorem C.1 for ReLU, ReLU², ReGLU and attention (the whole subsection "Attention
blocks"); Lemma D.2, D.3, D.5, D.7 and Proposition D.4 in the cases (+) and (0) and for gated blocks;
Lemma D.6 in the case (+); Lemmas D.8-D.20; Remarks C.4-C.7 and D.21; Proposition E.1.

Skips paper, main text (Sections 2-4):

| Statement | In Lean? |
|---|---|
| Definition 3.1, eq. (6), eq. (7) | defined / stated |
| Theorem 3.2 (i), (ii) | stated |
| Theorem 3.3 (i) | stated (both directions, without normalization and for `ε > 0`) |
| Theorem 3.3 (ii) (dimensions of the groups) | **no** |
| Theorem 3.3 (iii) | part: missing the readout `D` under pre-RMSNorm |
| Definition 4.1 | defined |
| Theorem 4.2 | part: with identity skips only the bound without `s`; ReLU, ReGLU, attention missing |
| Definition 4.3, Definition 4.4, Proposition 4.5 | **no** |
| Theorem 4.6 (i) | part: `tanh`, GELU, SwiGLU, GeGLU, without biases |
| Theorem 4.6 (ii) (under RMSNorm; learned skip) | **no** |
| Theorem 4.7 (residual networks at any depth) | **no** |
| Corollary 4.8 (Exact gain), 4.9, 4.10 | **no** |
| Theorem 4.11 (Different function classes) | **no** in these two sections of the index |

Skips paper, appendices without a Lean statement: Proposition A.1; Lemma A.2 (ii) (the expansion of
the deviation); Lemmas A.3, A.4; Theorem A.5 (ii) and (iii) for `ε = 0`; Lemma A.8; Proposition A.9
beyond the cases above; Theorems A.12, A.14 beyond (iv); Proposition A.15; Theorem A.17 (i), (iii);
Lemma A.18 in the group form; Lemmas A.21-A.30 and the rest of A.7-A.8; Theorem B.1 (i) with biases
and for ReLU, ReLU², ReGLU, attention; Theorem B.1 (ii)-(v); Lemma B.2 for `M` as a public statement
and with biases.

### (4b) Rows of `STATEMENTS.md` whose description is inaccurate or incomplete

All statement numbers and equation numbers that the rows of the three sections give (D 3.1, 3.2, 3.3,
4.1, 4.3, 5.1, 5.2, A.1, A.2, A.3, B.1, C.1, C.2, C.3, D.1-D.5, D.7, eqs. (16), (21), (22), Appendices
A.3, B, D.1, D.3; S eqs. (6), (7), 3.2, 3.3, 4.6, B.1, B.2) agree with the PDFs. All 221 Lean names of
the three sections exist (`#check`, `/home/claude/audit_dim/Check2.out`), and `#print axioms` gives
`[propext, Classical.choice, Quot.sound]` for 220 of them and `[propext]` for `vitB_count`; the
library has no `sorry`, `axiom`, `native_decide`, `notation` or `macro` outside `Absorb/` (grep).

1. Row "D Proposition 3.3, last sentence: at generic parameters any `d` columns of a read or of `D`,
   and any `d` rows of `E` or of a write, form an invertible matrix" (`ae_isUnit_det_submatrix`). The
   last sentence of the **statement** is "At generic parameters every hidden state has such columns,
   and these changes of basis at all `L + 1` hidden states remove `(L+1) dim 𝒢` parameters". The row
   quotes the last sentence of the **proof** (tex 423). The Lean statement is the proof's sentence;
   it has no hypothesis `d_hidden, d_out ≥ d`, so by itself it does not say that such columns exist.
2. Row "GELU far from the origin …" gives `geluDeriv` under the file `Activations/GeluExpansion.lean`.
   `geluDeriv` is defined in `Activations/Gaussian.lean:188`.
3. Row "D Lemma D.5, case (n): `(D_L)` holds" (`claim_last`). The paper's lemma has the hypothesis "If
   `D` has rank `d_model`"; the Lean statement has none. The row and the notes do not say so.
4. Row "D Lemma B.1, for the changes of basis: `E` and the writes of rank `d` ⇒ the direction
   determines `X`" (`cobDir_injective`). This describes the Lean statement correctly, but the paper's
   Lemma B.1 is a statement at generic parameters about a group action ("act locally freely"). The
   Lean statement is its infinitesimal form under the rank conditions of the proof.
5. Rows "S the upper bound for residual networks, changes of basis only: `fd ≤ P − d²`" and the two
   after it do not name the paper's statement: it is S Theorem 4.2 (the bound with identity skips),
   without the term `s`.
6. Row "S Theorem 3.3 (i), 'only if' …": correct, with one addition: the hypothesis "every block is
   nonzero for some value of its parameters" is that of Theorem A.5 (iii), which also has `d ≥ 2`;
   Lean does not need `d ≥ 2`.
7. Not in the index, although they carry part of a paper statement: `hidden_cob`
   (`Symmetry/ChangeOfBasis.lean:43`, the clause "with the hidden states `h_ℓ G_ℓ`" of Proposition 3.2),
   `cobSkip` (S eq. (6)), `antisymmetric` (the Lie algebra of `O(d)`), `centering` (the matrix `Z`
   of Proposition A.3), `coe_inv_of_mem_orthogonalGroup`.
8. Status column: several rows with the status "proved" list definitions among the names (`silu`,
   `siluDeriv`, `geluDeriv`, `relu`, `reluDeriv`, `reluSq`, `reluSqDeriv`, `rescaleDir`, `suffix`,
   `skipProd`, `UnitsRigid`, `GatedUnitsRescale`, `OneBlockGeneric`, `OneBlockGenericGated`,
   `TanhDepthGeneric`, `cobDirLin`, `Params.linE`, …). For a definition "proved" says nothing; whether
   it is the paper's object is what section (2) of this report checks.
9. The notes under the dimension table are accurate where I checked them (Proposition 3.3 in the
   simultaneous form; no invertibility in `exists_cob_reads_upperTriangular`; the Haar measure;
   Lemma C.3 without the hypothesis on proportionality for SwiGLU and GeGLU and with it for ReGLU;
   one token in the paper against `T` tokens in Lean; `d ≥ 1` in the proof of Theorem 5.2 (i);
   `fderiv = 0` where not differentiable; Proposition A.3 not stated for networks). One note is no
   longer needed: "'At generic parameters every hidden state has such columns' and 'removes
   `(L+1) dim 𝒢` parameters' are not stated yet" — the first is now the row of item 1.

---------------------------------------------------------------------------------------------------

## (5) What the authors should know, most serious first

I found no Lean statement that is false as a statement about the paper, none that is vacuous, and
no definition that changes the meaning of a stated result. The differences are of coverage and of
form. In order of weight:

1. **"Proved in Lean" covers a part of each headline theorem.**
   - D Theorem 5.2: 1 of its 7 cases, "(i) `tanh` blocks without normalization"
     (`ae_funDim_tanh_skipless`). Not stated: (i) under pre-RMSNorm with `ε > 0` and with `ε = 0`,
     (ii) GELU, (iii) SwiGLU and GeGLU.
   - D Theorem 5.1 / C.1 and S Theorem 4.6 (i) / B.1 (i): 4 of the 8 kinds of block (`tanh`, GELU,
     SwiGLU, GeGLU), without biases. ReLU, ReLU², ReGLU and attention have no theorem on the
     functional dimension (Lemma C.3 is proved for ReLU, ReLU², ReGLU, but nothing uses it yet; no
     attention block is defined). S Theorem 4.6 (ii) and B.1 (ii)-(v) are not stated.
   - S Theorems 3.3 (ii), 4.7, 4.11, Corollaries 4.8-4.10, D Proposition 4.6 and Corollary 5.3, and
     the definitions of the equality condition and of identifiability are not stated at all.
   For the cases that are stated, the Lean statements are the paper's, hypothesis for hypothesis
   (`d ≥ 2`, `d_in, d_out ≥ d`, width `≥ d`, generic = almost everywhere for Lebesgue measure,
   conclusion `fd + … = P`).

2. **The term `s` of the upper bounds (D Theorem 4.3, S Theorem 4.2) is there only for skipless
   gated blocks with a differentiable gate.** For `tanh` and GELU `s = 0` and the bounds are the
   paper's. For ReLU² the Lean bound is `fd ≤ P − (L+1) dim 𝒢`, without `s`. For ReLU and ReGLU no
   Lean bound applies at all, because every bound assumes `Differentiable ℝ (A.f ℓ)`. For a
   residual network of any depth the Lean bound is `fd ≤ P − dim 𝒢`, without `s`, also for gated
   blocks. The remark "for `ε = 0` the same bound holds with `𝒢 = CO(d)`" is not stated.

3. **Proposition 3.3 (i) is stated in a form that is not the paper's.** `exists_cob_reads_eq_one`
   treats all `L+1` hidden states at once and assumes invertible chosen columns in every read and
   in `D`. The paper's statement is for one hidden state, with a hypothesis on its read only. The
   one-state form follows from `eval_cob_skipless` (checked by a scratch proof, `/home/claude/audit_dim/Check3.lean`, example (l)), but it is not a theorem of the library.
   For (ii) the Lean form needs no invertibility, so there the simultaneous form loses nothing.

4. **Lemma B.1 (locally free action) is stated in its infinitesimal form** (`cobDir_injective`,
   `cobDir_add_rescaleDir_injective`: the direction determines the matrices `X` and the numbers
   `α`), under the rank conditions of the proof, with `ae_rank_E_write` and `ae_value_ne_zero` for
   generic parameters. This is what the proof of Theorem 4.3 uses. The statement about the group
   ("no continuous family … fixes `θ`") and its equivalence with the infinitesimal form are not in
   Lean. ReLU, ReLU², the gate rescaling of ReGLU and attention are not covered.

5. **Objects that are not literally the paper's, without effect on a stated result.**
   - `Params.cob θ G K` acts at all hidden states and has separate matrices for the writes and the
     reads; Definition 3.1 is its special case.
   - In `suffix`, `SuffixFlat`, `Claim`, `Regular`, Lemmas D.2-D.7 and Proposition D.4 a hidden
     state is a `T × d` matrix, the paper's is a row (one token). For MLP blocks and `T ≠ ∅` the two
     forms of the identity (16) are equivalent; this equivalence is an argument of this report, not
     a Lean statement.
   - Conventions of Lean in corner cases: `fderiv` is `0` where a map is not differentiable (never
     used: all results on `funDim` are for differentiable blocks); `N_0(0) = 0`; `ε` may be any real
     number in the algebraic statements; `T`, `d` may be empty (the equalities carry `[Nonempty T]`,
     which they need: with no tokens `fd = 0`, checked in `Check3.lean`, example (g)); `L = 0` is allowed (the statements are
     then true statements about `x ↦ χ(xE)D`).

6. **Places where the Lean statement has fewer hypotheses than the paper** (the paper's hypothesis
   is not needed for that statement):
   - Lemma C.3 for SwiGLU and GeGLU: "`(e_i, β'_i)` not proportional to `(c_i, β_i)`" is not used
     (`…_of_value_ne_zero`); it is needed for ReGLU.
   - Lemma D.5 in the case (n): the rank of `D` is not used (`claim_last`).
   - Theorem 5.2 (i) without normalization: `d ≥ 1` suffices for the conditions and for the equality
     (`ae_tanhDepthGeneric`, `funDim_tanh_skipless`); the final statement keeps `d ≥ 2`.
   - Theorem 4.3 (changes of basis; gated blocks): `d_out ≥ d` and `d ≥ 2` are not used.
   - S Theorem 4.2 with identity skips: only `d_in ≥ d` is used.
   - S Theorem 3.3 (i) / A.5 (iii): `d ≥ 2` is not used.
   - Proposition 3.3 (ii), S Theorem 3.3 (iii) under pre-RMSNorm, S Theorem 3.2 (ii), second
     sentence: no invertibility is used (a QR/RQ factorization exists for every square matrix).

7. **The index (`STATEMENTS.md`)**: numbers and names are right; the points of (4b) are small
   (one row quotes the proof instead of the statement of Proposition 3.3; `geluDeriv` is in another
   file; the dropped hypothesis of Lemma D.5 is not mentioned; `hidden_cob` is missing; one note
   says "not stated yet" about a statement that now has a row).

8. **What was checked by machine in this audit**: the compiled library that the checks ran against is
   the current source (for each of the 41 source files outside `Absorb/`, the content hash equals the
   hash recorded in its Lake build trace; six sources have a later modification time than their
   `.olean`, from a rewrite of the commit history, with unchanged content); all 221 Lean names of
   the three sections exist;
   `#print axioms` gives only `propext`, `Classical.choice`, `Quot.sound` for each; the elaborated
   forms (implicit and instance arguments) of the priority statements were read from `#check @…`
   (`/home/claude/audit_dim/Check1.out`, `Check2.out`); an additive Haar measure on the parameters
   exists (so "generic" is not vacuous); `Module.finrank ℝ (Params A dIn dOut)` is the number of
   entries of `E`, the reads, the writes and `D`; `ae_funDim_tanh_skipless` instantiates at
   concrete sizes (one token, `d = d_in = d_out = 2`, two blocks of width 3) to `fd + 12 = P`. Scratch proofs in
   `/home/claude/audit_dim/Check3.lean`, all of which compile: with no tokens `funDim = 0`; Theorem 4.3 for GELU blocks
   under pre-RMSNorm, and the bound without `s` for ReLU², follow from the general statements; the
   residual `tanh` block has `fd + d² = P` at generic parameters; the hidden-state clause of
   Proposition 3.2 for a skipless network follows from `hidden_cob`; the one-hidden-state form of
   Proposition 3.3 (i) follows from `eval_cob_skipless`.

9. **What was not checked**: the proofs (the task was the statements; Lean checks the proofs); the
   equivalence of the paper's group form of Lemma B.1 with Lean's infinitesimal form; the paper's
   own claims that are not formal statements (percentages, the sources in the literature).
