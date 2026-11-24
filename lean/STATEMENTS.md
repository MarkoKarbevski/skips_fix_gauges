# Statements: the papers beside the Lean code

For the authors. Each row puts a statement of a paper beside its Lean statement. "D" is "On the
Functional Dimension of a Family of Analytic Neural Networks", "S" is "Skip Connections Unlock
at Least d_model² Parameters per Layer" and "A" is "Can an MLP Absorb Its Skip Connection Exactly?"
(numbers of the PDFs in the repository on 24 November 2026). A row is
"proved" only when `lake build` passes with no `sorry` in the file and `#print axioms` shows the
three standard axioms. Please check the middle column against the paper: a proof of a statement
that differs from the paper's says nothing about the paper.

Conventions, as in the paper: tokens are rows, weights multiply on the right (`x * E`).

Checked against the papers by readers who did not write the statements (three comparisons, 24
November 2026): every row of this file for the statements that were in the library at commit
`46d0223`. Result: no Lean statement was found false, vacuous or changed in meaning by a
definition; the differences were of coverage and of form, and the rows and notes below say them.
Not yet compared by such a reader: Theorem 4.5 of the absorb paper (`Absorb/FirstBlock.lean`), the two
files for the skips paper `Residual/UpperBoundSymmetries.lean` and `OneBlock/ResidualRescale.lean`, the file for ReGLU blocks `OneBlock/ReGLU.lean`, the two files for Theorem 4.3 of the absorb paper (`Absorb/RMSNormRays.lean`, `Absorb/RMSNormGeneric.lean`) and `Dimension/GenericRank.lean` (the three written after the fourth audit began), and the
statements for ReLU, ReLU² and ReGLU blocks, written after that commit (`Dimension/RescalingMlp.lean`, `Dimension/RescalingGate.lean`, `OneBlock/Rescale.lean`,
the last section of `Dimension/Functional.lean` and the statements marked with a prime).

## Definitions

| Paper | Lean | File |
|---|---|---|
| Hidden state `h ∈ ℝ^{T×d_model}` | `Matrix T d ℝ` (`T`, `d` finite index types) | |
| RMSNorm `N_ε` on a row, on a hidden state (Section 2) | `Skips.rmsRow ε v`, `Skips.rmsNorm ε h` | `Basic/RMSNorm.lean` |
| The fixed part of a network: widths, the maps `f_ℓ`, the map `χ` | `Skips.Arch T d L` | `Network/Defs.lean` |
| Parameters `θ = (E, W_read^ℓ, W_write^ℓ, D)` | `Skips.Params A dIn dOut` | `Network/Defs.lean` |
| Hidden states, eq. (2): `h_0 = xE`, `h_ℓ = g_ℓ(χ(h_{ℓ-1}))` | `Skips.hidden A M θ x ℓ`, with `M = 0` | `Network/Defs.lean` |
| The function `F_θ`, eq. (2): `y = χ(h_L) D` | `Skips.eval A M θ x`, with `M = 0` | `Network/Defs.lean` |
| Definition 3.1 (change of basis `G` at the hidden state `h_j`): `W ↦ WG` for the writes into `h_j`, `W ↦ G⁻¹W` for the reads of `h_j` | `Skips.Params.cobAt θ j G`; what it does to each weight: `Params.cobAt_E_zero`, `Params.cobAt_E_of_ne`, `Params.cobAt_read_castSucc`, `Params.cobAt_read_of_ne`, `Params.cobAt_write_succ`, `Params.cobAt_write_of_ne`, `Params.cobAt_D_last`, `Params.cobAt_D_of_ne` | `Symmetry/AtOneState.lean` |
| Definition 3.1 at all hidden states at once (the tuple of Proposition 3.2), with separate matrices `G` for the writes and `K` for the reads; on the skips, `A_ℓ ↦ G_{ℓ−1}⁻¹ A_ℓ G_ℓ` (S eq. (6) and the sentence after it) | `Skips.Params.cob θ G K`, `Skips.cobSkip M G` | `Symmetry/ChangeOfBasis.lean` |

Differences from the paper, on purpose:
1. `hidden` and `eval` take stream matrices `M ℓ`: `h_ℓ = h_{ℓ-1} M_ℓ + g_ℓ(χ(h_{ℓ-1}))`. The paper's
   networks are `M = 0`. `M = 1` is a residual network (the other two papers).
2. For `ε = 0` the paper defines a network only where no row of a hidden state vanishes. In Lean
   `rmsRow 0 0 = 0`. Statements for `ε = 0` that need a nonzero row will say so.
3. The maps `f_ℓ` are arbitrary in the definitions. The kinds of block (tanh, GELU, gated,
   attention) enter as choices of `f_ℓ` in later files.

## Results

Status: *defined* (a definition), *in work* (statement compiles, proof not finished), *proved*
(compiled, no `sorry`, standard axioms only). The branch `main` holds only what is proved; statements
in work are on the branch `lean-wip`. A row marked *proved* may list definitions among its names
(`silu`, `suffix`, `OneBlockGeneric`, …): for a definition "proved" says nothing, and whether it is
the paper's object is checked by reading it.

### Dimension paper

| Paper | Lean statement | File | Status |
|---|---|---|---|
| D Lemma A.1, "⇐": `N_ε(hQ) = N_ε(h)Q` for orthogonal `Q` | `rmsNorm_mul_orthogonal` | `Basic/RMSNorm.lean` | proved |
| D Lemma A.1, "⇐" for `ε = 0`: `N_0(h·cQ) = N_0(h)Q`, `c > 0` | `rmsNorm_zero_mul_smul_orthogonal` | `Basic/RMSNorm.lean` | proved |
| D Proposition 3.2, general form (also S eq. (6)), with its clause "with the hidden states `h_ℓ G_ℓ`" | `hidden_cob`, `eval_cob` | `Symmetry/ChangeOfBasis.lean` | proved |
| D Proposition 3.2, without normalization | `eval_cob_skipless` | `Symmetry/ChangeOfBasis.lean` | proved |
| D Proposition 3.2, under pre-RMSNorm | `eval_cob_rmsNorm` | `Symmetry/Normalized.lean` | proved |
| D Proposition 3.2, `ε = 0`, `G_ℓ = c_ℓ Q_ℓ` | `eval_cob_rmsNorm_zero` | `Symmetry/Normalized.lean` | proved |
| D Proposition 3.2 for the change of basis at one hidden state, without normalization and under pre-RMSNorm (orthogonal `G`) | `eval_cobAt_skipless`, `eval_cobAt_rmsNorm` | `Symmetry/AtOneState.lean` | proved |
| **D Proposition 3.3 (i), as in the paper:** `d` columns of the read of one hidden state (`W_read^{ℓ+1}`, or `D`) form an invertible `W_1`; without normalization the change of basis `G = W_1` there preserves the function and turns `W_1` into `I` | `cobAt_read_eq_one`, `cobAt_D_eq_one` | `Symmetry/AtOneState.lean` | proved |
| **D Proposition 3.3 (ii), as in the paper:** `W_1 = QR` with `Q` orthogonal; under pre-RMSNorm the change of basis `Q` there preserves the function and turns `W_1` into `R` | `cobAt_read_eq_of_qr`, `cobAt_D_eq_of_qr` | `Symmetry/AtOneState.lean` | proved |
| D rows of a write, or of `E`, at one hidden state: `G = W_1⁻¹` gives `W_1 G = I` (the paragraph after Proposition 3.3); under pre-RMSNorm `W_1ᵀ = QR` gives `W_1 Q = Rᵀ` (proof of Proposition 3.3) | `cobAt_write_eq_one`, `cobAt_E_eq_one`, `cobAt_write_eq_of_qr`, `cobAt_E_eq_of_qr` | `Symmetry/AtOneState.lean` | proved |
| D Proposition 3.3, "At generic parameters every hidden state has such columns" (`d_out ≥ d`, at least `d` columns in every read); the same for the rows (`d_in ≥ d`, at least `d` rows in every write) | `ae_exists_isUnit_det_submatrix_cols`, `ae_exists_isUnit_det_submatrix_rows` | `Symmetry/AtOneState.lean` | proved |
| D Proposition 3.3 (i), all hidden states at once (needs the invertible columns in every read and in `D`) | `exists_cob_reads_eq_one` | `Symmetry/Reduction.lean` | proved |
| D rows of a write (after Proposition 3.3, Example A.2), all hidden states at once | `exists_cob_writes_eq_one` | `Symmetry/Reduction.lean` | proved |
| QR in the form `Qᵀ W` upper triangular (used by 3.3 (ii)) | `exists_orthogonal_transpose_mul_upperTriangular` | `Symmetry/Reduction.lean` | proved |
| D Proposition 3.3 (ii), all hidden states at once | `exists_cob_reads_upperTriangular` | `Symmetry/Reduction.lean` | proved |
| the count `d(d−1)/2` of entries below the diagonal | `card_below_diagonal` | `Symmetry/Reduction.lean` | proved |
| D Appendix A.3: `25·767·766/2 = 7,344,025` | `vitB_count` | `Symmetry/Reduction.lean` | proved |
| D Lemma A.1, "⇒", `ε > 0`: `N_ε(vG) = N_ε(v)M` for all `v ≠ 0` gives `G` orthogonal and `M = G` | `orthogonal_of_rmsRow_vecMul` | `Basic/RMSNormConverse.lean` | proved |
| D Lemma A.1, "⇒", `ε = 0`: then `M` is orthogonal and `G = cM`, `c > 0` | `conformal_of_rmsRow_zero_vecMul` | `Basic/RMSNormConverse.lean` | proved |
| D Proposition A.3 (i), its two facts: `Z² = Z`, rows `vZ` have mean zero | `centering_mul_centering`, `sum_vecMul_centering`, `vecMul_centering_of_sum_eq_zero` | `Basic/LayerNorm.lean` | proved |
| D Proposition A.3 (ii), the identity `N_ε(yŪᵀ) = sqrt(d/(d−1)) N'(y)Ūᵀ` (stated for any number `m` of orthonormal columns) | `rmsRow_vecMul_transpose_of_orthonormal` | `Basic/LayerNorm.lean` | proved |
| D parameters `θ ∈ ℝ^P` as a vector space; `P` is its dimension | `Params` with `AddCommGroup`, `Module ℝ`, a norm; `Module.finrank ℝ (Params A dIn dOut)` | `Dimension/Space.lean` | defined |
| D Definition 4.1: outputs on a batch, rank of the Jacobian, functional dimension, redundancy | `evalBatch`, `jacobianRank`, `funDim`, `redundancy` | `Dimension/Functional.lean` | defined |
| D Appendix C: flat directions `K(θ)` | `flat` | `Dimension/Functional.lean` | defined |
| differentiable `f_ℓ` and `χ` give `θ ↦ F_θ(x)` differentiable | `differentiable_eval` | `Dimension/Functional.lean` | proved |
| the maximum of Definition 4.1 is attained on a finite batch | `exists_jacobianRank_eq_funDim`, `jacobianRank_le_funDim`, `jacobianRank_le_finrank` | `Dimension/Functional.lean` | proved |
| D Appendix C: `fd(θ) = P − dim K(θ)` | `funDim_add_finrank_flat` | `Dimension/Functional.lean` | proved |
| D Section 4: a direction in which a symmetry moves `θ` is flat | `mem_flat_of_hasDerivAt`, `funDim_add_finrank_le_of_le_flat` | `Dimension/Functional.lean` | proved |
| the direction `(E X_0, −X_{ℓ−1} W_read^ℓ, W_write^ℓ X_ℓ, −X_L D)` of the changes of basis | `cobDir` | `Dimension/UpperBound.lean` | defined |
| D Lemma B.1 in infinitesimal form (the paper states it for the group action, "act locally freely"), for the changes of basis: `E` and the writes of rank `d` ⇒ the direction determines `X` | `cobDir_injective` | `Dimension/UpperBound.lean` | proved |
| D Theorem 4.3, without normalization, changes of basis only: `fd ≤ P − (L+1)d²` | `cobDir_mem_flat_skipless`, `funDim_add_le_skipless` | `Dimension/UpperBound.lean` | proved |
| D Theorem 4.3, under pre-RMSNorm (`ε > 0`), changes of basis only: `fd ≤ P − (L+1)d(d−1)/2` | `differentiable_rmsNorm`, `cobDir_mem_flat_skipless_rmsNorm`, `finrank_antisymmetric`, `funDim_add_le_skipless_rmsNorm` | `Dimension/UpperBoundRMSNorm.lean` | proved |
| a real-analytic function that is not identically zero vanishes on a set of measure zero (not in Mathlib at this version) | `volume_zeroSet_of_analytic_pi`, `measure_zeroSet_of_analytic` | `Generic/AnalyticZeroSet.lean` | proved |
| D proof of Proposition 3.3, its last sentence: at generic parameters every `d` columns of a read or of `D`, and every `d` rows of `E` or of a write, form an invertible matrix | `ae_isUnit_det_submatrix` | `Generic/Params.lean` | proved |
| at generic parameters `E` and the writes have rank `d` (`d_in ≥ d`, at least `d` rows in each write) | `ae_rank_E_write` | `Generic/Params.lean` | proved |
| D Theorem 4.3 at generic parameters, changes of basis only, without normalization and under pre-RMSNorm | `ae_funDim_add_le_skipless`, `ae_funDim_add_le_skipless_rmsNorm` | `Generic/Params.lean` | proved |
| D Lemma C.3 for tanh, with the linear term, the constant and the biases | `tanh_units_flat_eq_zero` | `OneBlock/UnitsTanh.lean` | proved |
| D Lemma C.3 for SwiGLU (gate SiLU), with the linear term, the constant and the biases: a flat direction only rescales the value of each hidden unit | `silu`, `siluDeriv`, `hasDerivAt_silu`, `silu_gated_units_flat` (the paper's form), `silu_gated_units_flat_of_value_ne_zero` (without the hypothesis on proportionality) | `OneBlock/UnitsSwiGLU.lean` | proved |
| the normal density `φ`, the distribution function `Φ = 1/2 + ∫₀^z φ`, GELU `z Φ(z)`, and `σ'(z) = Φ(z) + zφ(z)` | `gaussPdf`, `gaussCdf`, `gelu`, `geluDeriv` | `Activations/Gaussian.lean` | defined |
| `Φ' = φ`, `φ' = −zφ`, `Φ(−z) = 1 − Φ(z)`, `0 < Φ < 1`, the limits of `Φ` at `±∞` | `hasDerivAt_gaussCdf`, `hasDerivAt_gaussPdf`, `gaussCdf_neg`, `gaussCdf_pos`, `gaussCdf_lt_one`, `tendsto_gaussCdf_atTop`, `tendsto_gaussCdf_atBot` | `Activations/Gaussian.lean` | proved |
| D proof of Lemma C.3 for GELU: `φ(z)(1/z − 1/z³) ≤ 1 − Φ(z) ≤ φ(z)/z` for `z > 0` | `le_one_sub_gaussCdf`, `one_sub_gaussCdf_le` | `Activations/Gaussian.lean` | proved |
| GELU: `σ'(z) = Φ(z) + zφ(z)`, and `σ(z) − σ(−z) = z` (D Appendix D.1) | `hasDerivAt_gelu`, `gelu_sub_gelu_neg` | `Activations/Gaussian.lean` | proved |
| a network of gated blocks (Section 2, "Blocks"): read `[W_g | W_v]`, `f = σ(gate)·value` | `Arch.gated σ χ hid` | `Network/Blocks.lean` | defined |
| D Appendix B: the rescaling `(e_i, a_i) ↦ (e_i/λ, λ a_i)` of a gated hidden unit preserves the function; its direction | `eval_rescale`, `rescaleDir`, `rescaleDir_mem_flat` | `Dimension/Rescaling.lean` | proved |
| D Lemma B.1 for gated blocks, in infinitesimal form: the changes of basis and the rescalings move `θ` in independent directions | `cobDir_add_rescaleDir_injective` | `Dimension/Rescaling.lean` | proved |
| D Theorem 4.3 for gated blocks, without normalization: `fd ≤ P − (L+1)d² − s`, `s` the number of hidden units | `funDim_add_le_skipless_gated` | `Dimension/Rescaling.lean` | proved |
| the rescalings are flat for every differentiable map `χ` before the reads (identity, RMSNorm with `ε > 0`) | `rescaleDir_mem_flat_of_differentiable` | `Dimension/Rescaling.lean` | proved |
| D Theorem 4.3 for gated blocks under pre-RMSNorm (`ε > 0`), under the conditions of the proof: `fd ≤ P − (L+1)d(d−1)/2 − s` | `funDim_add_le_skipless_gated_rmsNorm` | `Dimension/Rescaling.lean` | proved |
| D Theorem 4.3 for gated blocks at generic parameters (`d_in ≥ d`, at least `d` hidden units per block), without normalization and under pre-RMSNorm | `ae_value_ne_zero`, `ae_funDim_add_le_skipless_gated`, `ae_funDim_add_le_skipless_gated_rmsNorm` | `Generic/Gated.lean` | proved |
| D Theorem 5.1 / C.1 for every gate activation `σ` for which Lemma C.3 holds with the rescalings of the values (`GatedUnitsRescale σ σ'`; Steps 1 and 3 of the proof): `fd = P − 2d² − d_hidden` under the conditions of the proof (`OneBlockGenericGated`), which hold at generic parameters | `GatedUnitsRescale`, `OneBlockGenericGated`, `flat_le_cobDir_add_rescaleDir_gated`, `funDim_gated_oneBlock`, `ae_oneBlockGenericGated`, `ae_funDim_gated_oneBlock` | `OneBlock/Gated.lean` | proved |
| D Theorem 5.1 / C.1 for a SwiGLU block: `fd = P − 2d² − d_hidden`, under the conditions of the proof and at generic parameters | `silu_gatedUnitsRescale`, `flat_le_cobDir_add_rescaleDir_swiglu`, `funDim_swiglu_oneBlock`, `ae_funDim_swiglu_oneBlock` | `OneBlock/SwiGLU.lean` | proved |
| an MLP network with activation `σ` (Section 2, "Blocks") | `Arch.mlp σ χ hid` | `Network/Blocks.lean` | defined |
| D Lemma C.2: the directions that keep `C = E W_read` and `A = W_write D` are those of two changes of basis | `keeps_products_iff_mem_range_cobDir` | `OneBlock/Factorization.lean` | proved |
| D Theorem 5.1 / C.1 for every activation `σ` for which Lemma C.3 holds with no rescaling (`UnitsRigid σ σ'`; Steps 1 and 3 of the proof): `fd = P − 2d²` under the conditions of the proof (`OneBlockGeneric`: ranks `d`; rows of `A` nonzero; columns of `C` nonzero and pairwise non-collinear), which hold at generic parameters (`d_in, d_out, d_hidden ≥ d ≥ 2`) | `UnitsRigid`, `OneBlockGeneric`, `flat_le_range_cobDir_mlp`, `funDim_mlp_oneBlock`, `ae_oneBlockGeneric`, `ae_funDim_mlp_oneBlock` | `OneBlock/Mlp.lean` | proved |
| D Theorem 5.1 / C.1 for a tanh block: `fd = P − 2d²`, under the conditions of the proof and at generic parameters | `hasDerivAt_tanh`, `tanh_unitsRigid`, `flat_le_range_cobDir_tanh`, `funDim_tanh_oneBlock`, `ae_funDim_tanh_oneBlock` | `OneBlock/Tanh.lean` | proved |
| GELU far from the origin, with explicit remainders: `0 ≤ σ(z) − max(z,0) + φ(z) ≤ φ(z)/z²`, and `σ'(z) − 1[z>0] − φ(z)(z − 1/z)` between `0` and `φ(z)/z³` (D proof of Lemma C.3 for GELU) | `gelu_expansion_pos`, `gelu_expansion_neg`, `geluDeriv_expansion_pos`, `geluDeriv_expansion_neg` | `Activations/GeluExpansion.lean` | proved |
| D Lemma C.3 for GELU, with the linear term, the constant and the biases | `gelu_units_flat_eq_zero` | `OneBlock/UnitsGELU.lean` | proved |
| D Theorem 5.1 / C.1 for a GELU block: `fd = P − 2d²`, under the conditions of the proof and at generic parameters | `gelu_unitsRigid`, `flat_le_range_cobDir_gelu`, `funDim_gelu_oneBlock`, `ae_funDim_gelu_oneBlock` | `OneBlock/GELU.lean` | proved |
| D Lemma C.3 for GeGLU (gate GELU), with the linear term, the constant and the biases: a flat direction only rescales the value of each hidden unit | `gelu_gated_units_flat` (the paper's form), `gelu_gated_units_flat_of_value_ne_zero` (without the hypothesis on proportionality) | `OneBlock/UnitsGeGLU.lean` | proved |
| D Theorem 5.1 / C.1 for a GeGLU block: `fd = P − 2d² − d_hidden`, under the conditions of the proof and at generic parameters | `gelu_gatedUnitsRescale`, `flat_le_cobDir_add_rescaleDir_geglu`, `funDim_geglu_oneBlock`, `ae_funDim_geglu_oneBlock` | `OneBlock/GeGLU.lean` | proved |
| ReLU `max(z,0)` and ReLU² `max(z,0)²`, with their derivatives `1[z>0]` (for `z ≠ 0`) and `2 max(z,0)` | `relu`, `reluDeriv`, `reluSq`, `reluSqDeriv`, `hasDerivAt_relu`, `hasDerivAt_reluSq` | `Activations/ReLU.lean` | proved |
| D Lemma C.3 for ReLU and for ReLU², with the linear term, the constant and the biases: a direction that is flat at every input with no hidden unit at its kink only rescales each hidden unit, `(ψ_c, ψ_β) = λ(c, β)`, `ψ_a = −λa` (ReLU), `ψ_a = −2λa` (ReLU²) | `relu_units_flat`, `reluSq_units_flat` | `OneBlock/UnitsReLU.lean` | proved |
| D Lemma C.3 for ReGLU: `(ψ_c, ψ_β) = λ(c, β)`, `(ψ_e, ψ_β') = −α(e, β')`, `ψ_a = (α − λ)a`, with the paper's hypothesis that `(e, β')` is not proportional to `(c, β)` | `relu_gated_units_flat` | `OneBlock/UnitsReGLU.lean` | proved |
| D Appendix D.3: `𝓑_{>k}(h)`, the output of the network when its hidden state `h_k` is set to `h`; `F_θ(x) = 𝓑_{>0}(xE)` | `suffix`, `suffix_last`, `suffix_castSucc`, `suffix_hidden`, `eval_eq_suffix_zero` | `Depth/Suffix.lean` | proved |
| D Appendix D.3, case (n): the identity (16), `𝐃𝓑_{>k}(h)(hZ) + 𝐃_θ𝓑_{>k}(h)η = 0` for all `h`; Claim `(D_k)` for blocks without symmetries inside; "regular" (R1), (R3) | `SuffixFlat`, `Claim`, `Regular` | `Depth/Suffix.lean` | defined |
| D Lemma D.2, case (n): for regular `θ` and analytic blocks the derivative of `𝓑_{>k}` is injective on an open dense set | `exists_open_dense_injective_fderiv_suffix` | `Depth/Suffix.lean` | proved |
| D Lemma D.3, case (n): a direction at a write | `suffixFlat_of_flat_at_write` | `Depth/Suffix.lean` | proved |
| D Proposition D.4, case (n): `(D_0)` at a regular `θ` gives `fd = P − (L+1)d²` | `flat_le_range_cobDir_of_claim`, `funDim_of_claim` | `Depth/Suffix.lean` | proved |
| D Lemma D.5, case (n): `(D_L)` holds (the paper's hypothesis "`D` has rank `d_model`" is not used in this case) | `claim_last` | `Depth/Suffix.lean` | proved |
| `tanh` is real-analytic; an MLP block with a real-analytic activation is real-analytic | `analyticOnNhd_tanh`, `analyticOnNhd_matrix_entry`, `analyticOnNhd_f_mlp` | `Network/Analytic.lean` | proved |
| D proof of Lemma D.1, its middle step: rates `λ_j > 0` linearly independent over `ℚ`, `G_0, …, G_K` real-analytic near `0`; if `∑_i t^i G_i(e^{−λ_1 t}, …, e^{−λ_q t}) = 0` for all large `t`, every `G_i` vanishes near `0` | `eventually_eq_zero_of_sum_pow_mul_exp_ray` | `Depth/RaySeparation.lean` | proved |
| D Lemma D.1 (separation on a ray): `u_1, …, u_q` linearly independent over `ℚ`, `𝒯_0, …, 𝒯_K` real-analytic on `ℝ^q`; if `∑_i t^i 𝒯_i(tanh(t u_1), …, tanh(t u_q)) = 0` for all `t > 0`, every `𝒯_i` vanishes. Also with the `u` arranged in a matrix (tokens × hidden units) | `tanh_ray_separation`, `tanh_ray_separation_matrix` | `Depth/RaySeparation.lean` | proved |
| D eq. (21): the left side `𝓛(w̃, w̃'; ·)` of the identity for one block (for any map `χ` before the reads) | `blockLHS` | `Depth/StepTanh.lean` | defined |
| D eq. (22), case (n), by the chain rule: the identity (16) before a block holds iff `𝓛(σ(nW), σ'(nW); n) = 0` for all `n`, with `ż(n) = n(ZW + η_W)` | `suffixFlat_castSucc_iff_mlp` | `Depth/StepTanh.lean` | proved |
| D proof of Lemma D.7: under (T2), for a dense set of rows `ξ` the numbers `ξ c_j` are linearly independent over `ℚ` (here for all tokens at once) | `dense_setOf_linearIndependent_mul` | `Depth/StepTanh.lean` | proved |
| D proof of Lemma D.7, "the fact": `θ` regular, (T1); if `𝐃𝓑(w̃V)(((1 − w̃²) ⊙ b)V) = 0` for all `w̃`, then `b = 0` | `eq_zero_of_fderiv_suffix_one_sub_sq` | `Depth/StepTanh.lean` | proved |
| D Lemma D.7 (the step for `tanh` on rays), case (n): `θ` regular, block `k+1` with (T1) and (T2); then `(D_{k+1})` implies `(D_k)` | `claim_castSucc_tanh` | `Depth/StepTanh.lean` | proved |
| D proof of Theorem 5.2 (i), cases (n) and (+): the conditions (R1), (T1), (T2), `W_read W_write` invertible (they do not involve `χ`); they make `θ` regular; they hold at generic parameters (`d_in, d_out ≥ d ≥ 1`, at least `d` hidden units per block) | `TanhDepthGeneric`, `regular_of_tanhDepthGeneric`, `ae_tanhDepthGeneric` | `Depth/Tanh.lean` | proved |
| **D Theorem 5.2 (i), without normalization:** `L` `tanh` blocks, `d_in, d_out ≥ d ≥ 2`, at least `d` hidden units per block: `fd = P − (L+1)d²`, under the conditions of the proof and at generic parameters | `claim_of_tanhDepthGeneric`, `funDim_tanh_skipless`, `ae_funDim_tanh_skipless` | `Depth/Tanh.lean` | proved |
| D Appendix D.3, case (n): `𝓑_{>k}` is real-analytic in the hidden state and differentiable in the hidden state and the weights together; the chain rules `𝐃𝓑_{>k−1}(h) = 𝐃𝓑_{>k}(g_k(h)) ∘ 𝐃g_k(h)` and `𝐃_θF(x)η = 𝐃𝓑_{>0}(xE)(xη_E) + 𝐃_θ𝓑_{>0}(xE)η` | `analyticOnNhd_block`, `analyticOnNhd_suffix`, `differentiable_suffix_prod`, `analyticOnNhd_suffix_prod` (in `Depth/StepTanh.lean`), `differentiable_params_suffix`, `differentiable_suffix`, `suffix_castSucc_eq_comp`, `fderiv_suffix_castSucc`, `fderiv_suffix_last`, `fderiv_params_suffix_last`, `suffix_last_eq_mul`, `fderiv_eval_eq_fderiv_suffix` | `Depth/Suffix.lean` | proved |
| RMSNorm with `ε > 0` is real-analytic; for a real-analytic `χ` and real-analytic blocks, `𝓑_{>k}` is real-analytic in the hidden state, and in the weights and the hidden state together | `analyticOnNhd_rmsNorm`, `analyticOnNhd_suffix_of_analytic`, `analyticOnNhd_suffix_prod_of_analytic` | `Depth/SuffixRMS.lean` | proved |
| D Appendix D.3, case (+): Claim `(D_k)` with antisymmetric `Z = Z_k, Z_{k+1}, …, Z_L` | `ClaimRMS` | `Depth/SuffixRMS.lean` | defined |
| D Lemma D.2, case (+) | `exists_open_dense_injective_fderiv_suffix_rmsNorm` | `Depth/SuffixRMS.lean` | proved |
| D Lemma D.3, case (+) | `suffixFlat_of_flat_at_write_rmsNorm` | `Depth/SuffixRMS.lean` | proved |
| D Lemma D.5, case (+): `D` of rank `d` gives `(D_L)` | `claimRMS_last` | `Depth/SuffixRMS.lean` | proved |
| D Proposition D.4, case (+): `(D_0)` at a regular `θ` gives `fd = P − (L+1)d(d−1)/2` | `flat_le_range_cobDir_of_claimRMS`, `funDim_of_claimRMS` | `Depth/SuffixRMS.lean` | proved |
| D eq. (14), for `ε > 0` (the case `ε = 0` is not stated): `𝐃N_ε(h)(hZ) = nZ − ⟨nZ, n⟩n/d` at `n = N_ε(h)`, row by row | `tangentRMS`, `fderiv_rmsNorm_mul` | `Depth/StepTanhRMS.lean` | proved |
| D eq. (22), case (+), by the chain rule: (16) before a block holds iff `𝓛(σ(nW), σ'(nW); n) = 0` at the values `n = N_ε(h)`, with `ż(n) = (nZ − ⟨nZ, n⟩n/d)W + nη_W` (eq. (20)) | `suffixFlat_castSucc_iff_mlp_rmsNorm_values` | `Depth/StepTanhRMS.lean` | proved |
| D Lemma D.6 (the identity at every real row), case (+), for a real-analytic activation | `suffixFlat_castSucc_iff_mlp_rmsNorm` | `Depth/StepTanhRMS.lean` | proved |
| D proof of Lemma D.7, "the fact", case (+) | `eq_zero_of_fderiv_suffix_one_sub_sq_rmsNorm` | `Depth/StepTanhRMS.lean` | proved |
| D Lemma D.7 (the step for `tanh` on rays), case (+) | `claimRMS_castSucc_tanh` | `Depth/StepTanhRMS.lean` | proved |
| **D Theorem 5.2 (i), under pre-RMSNorm with `ε > 0`:** `L` `tanh` blocks, `d_in, d_out ≥ d ≥ 2`, at least `d` hidden units per block: `fd = P − (L+1)d(d−1)/2`, under the conditions of the proof and at generic parameters | `claimRMS_of_tanhDepthGeneric`, `funDim_tanh_skipless_rmsNorm`, `ae_funDim_tanh_skipless_rmsNorm` | `Depth/TanhRMS.lean` | proved |
| D Appendix C, "Notation and flat directions", for blocks that are not differentiable everywhere: the directions flat at every input of a set `U`; `fd(θ) = P − dim K(θ)`, "a direction of a symmetry is flat" and the bound from a subspace of flat directions, with no hypothesis of differentiability; a batch of inputs of `U` on which the Jacobian has the rank `P − dim K_U(θ)` | `flatOn`, `flat_le_flatOn`, `mem_flat_of_hasDerivAt'`, `funDim_add_finrank_flat'`, `funDim_add_finrank_le_of_le_flat'`, `exists_jacobianRank_add_finrank_flatOn` | `Dimension/Functional.lean` | proved |
| D Theorem 4.3 for the changes of basis, for arbitrary maps `f_ℓ` (no differentiability): `fd ≤ P − (L+1)d²` without normalization, `fd ≤ P − (L+1)d(d−1)/2` under pre-RMSNorm (every real `ε`) | `cobDir_mem_flat_skipless'`, `funDim_add_le_skipless'`, `cobDir_mem_flat_skipless_rmsNorm'`, `funDim_add_le_skipless_rmsNorm'` | `Dimension/UpperBound.lean`, `Dimension/UpperBoundRMSNorm.lean` | proved |
| D Appendix B: the rescalings `(c_i, a_i) ↦ (λc_i, a_i/λ)` of a ReLU hidden unit and `(λc_i, a_i/λ²)` of a ReLU² hidden unit, `λ > 0`, preserve the function (stated for `σ(λz) = λ^k σ(z)`); their directions are flat | `relu_homogeneous`, `reluSq_homogeneous`, `eval_rescale_mlp`, `rescaleDirMlp`, `rescaleDirMlp_mem_flat` | `Dimension/RescalingMlp.lean` | proved |
| D Lemma B.1 for ReLU and ReLU² blocks, in infinitesimal form: the changes of basis and the rescalings move `θ` in independent directions (`E` and the writes of rank `d`, no column of a read zero) | `cobDir_add_rescaleDirMlp_injective` | `Dimension/RescalingMlp.lean` | proved |
| D Theorem 4.3 for ReLU and ReLU² blocks, with the term `s` (the number of hidden units), under the conditions of the proof and at generic parameters (`d_in ≥ d`, at least `d` hidden units per block), without normalization and under pre-RMSNorm (every real `ε`) | `funDim_add_le_skipless_mlp_rescale`, `funDim_add_le_skipless_mlp_rescale_rmsNorm`, `ae_read_col_ne_zero`, `ae_funDim_add_le_skipless_relu`, `ae_funDim_add_le_skipless_reluSq`, `ae_funDim_add_le_skipless_relu_rmsNorm`, `ae_funDim_add_le_skipless_reluSq_rmsNorm` | `Dimension/RescalingMlp.lean` | proved |
| D Appendix B, "ReGLU, in addition": the rescaling `(c_i, a_i) ↦ (λc_i, a_i/λ)` of the gate of a ReGLU hidden unit, `λ > 0`, preserves the function (stated for a gate with `σ(λz) = λ^k σ(z)`); its directions are flat; the directions of the rescalings of the values are flat with no hypothesis of differentiability | `eval_rescale_gate`, `rescaleDirGate`, `rescaleDirGate_mem_flat`, `rescaleDir_mem_flat'` | `Dimension/RescalingGate.lean`, `Dimension/Rescaling.lean` | proved |
| D Lemma B.1 for ReGLU blocks, in infinitesimal form: the changes of basis and the two rescalings move `θ` in independent directions (`E` and the writes of rank `d`, no gate column and no value column of a read zero) | `cobDir_add_rescaleDir_add_rescaleDirGate_injective` | `Dimension/RescalingGate.lean` | proved |
| D Theorem 4.3 for ReGLU blocks, with `s = 2 ∑ d_hidden`, under the conditions of the proof and at generic parameters, without normalization and under pre-RMSNorm (every real `ε`) | `funDim_add_le_skipless_gated_gate`, `funDim_add_le_skipless_gated_gate_rmsNorm`, `ae_gate_ne_zero`, `ae_funDim_add_le_skipless_reglu`, `ae_funDim_add_le_skipless_reglu_rmsNorm` | `Dimension/RescalingGate.lean` | proved |
| D Lemma C.3 for ReLU and ReLU² as a property of the activation (the rescaling with exponent `k`) | `UnitsRescale`, `relu_unitsRescale`, `reluSq_unitsRescale` | `OneBlock/Rescale.lean` | proved |
| D Theorem 5.1 / C.1 for every activation that is positively homogeneous of degree `k`, differentiable away from `0` and satisfies Lemma C.3 with the rescalings: the inputs with no hidden unit at its kink; differentiability there; a direction that is flat at these inputs is a direction of the two changes of basis and of the rescalings; `fd = P − 2d² − d_hidden` under the conditions of the proof; the same rank on a batch of such inputs | `noKink`, `differentiableAt_eval_of_mem_noKink`, `flatOn_noKink_le_mlp_rescale`, `funDim_mlp_oneBlock_rescale`, `exists_jacobianRank_mlp_oneBlock_rescale` | `OneBlock/Rescale.lean` | proved |
| **D Theorem 5.1 / C.1 for a ReLU block and for a ReLU² block:** `d_in, d_out, d_hidden ≥ d ≥ 2`, at generic parameters `fd = P − 2d² − d_hidden`, and the Jacobian has this rank on a batch of inputs with no hidden unit at its kink | `ae_funDim_relu_oneBlock`, `ae_exists_jacobianRank_relu_oneBlock`, `ae_funDim_reluSq_oneBlock`, `ae_exists_jacobianRank_reluSq_oneBlock` | `OneBlock/Rescale.lean` | proved |
| D Theorem 5.1 / C.1 for a ReGLU block, the conditions of the proof: those of the other gated blocks, and no value column `e_i` of `C = E W_read` proportional to the gate column `c_i` of the same hidden unit (the hypothesis of Lemma C.3 that only ReGLU uses); they hold at generic parameters (`d_in, d_out, d_hidden ≥ d ≥ 2`). The inputs with no gate at its kink; the network is differentiable in `θ` there, with or without the skip | `OneBlockGenericReGLU`, `ae_oneBlockGenericReGLU`, `noKinkGate`, `differentiableAt_eval_of_mem_noKinkGate` | `OneBlock/ReGLU.lean` | in work |
| **D Theorem 5.1 / C.1 for a ReGLU block:** a direction that is flat at the inputs with no gate at its kink is a direction of the two changes of basis, of the rescalings of the values and of the rescalings of the gates; under the conditions of the proof and at generic parameters `fd = P − 2d² − 2d_hidden`, and the Jacobian has this rank on a batch of inputs with no gate at its kink | `flatOn_noKinkGate_le_reglu`, `funDim_reglu_oneBlock`, `exists_jacobianRank_reglu_oneBlock`, `ae_funDim_reglu_oneBlock`, `ae_exists_jacobianRank_reglu_oneBlock` | `OneBlock/ReGLU.lean` | in work |
| D Appendix D.7, "The parts together" (GELU and gated blocks): for a network with real-analytic `f_ℓ` and `χ` (the cases (n) and (+)), the output at a fixed input is real-analytic in `θ`, and at generic parameters the Jacobian on a batch has at least the rank that it has at any one parameter `θ₀`; hence `fd(θ₀) ≤ fd(θ)` for almost every `θ`. Stated for all stream matrices | `analyticOnNhd_eval_params`, `ae_jacobianRank_ge`, `ae_jacobianRank_le_funDim`, `ae_funDim_ge` | `Dimension/GenericRank.lean` | in work |
| D Appendix D.3, case (+), clauses of the proofs: products of analytic matrix functions; the derivative of `N_ε` (`ε > 0`), which is injective, so `N_ε` is an open map and preimages of open dense sets under it are open and dense; the chain rules for `𝓑_{>k}` under a differentiable or analytic `χ` | `analyticOnNhd_matrix_mul`, `fderiv_rmsNorm_apply`, `injective_fderiv_rmsNorm`, `isOpenMap_rmsNorm`, `isOpen_dense_preimage_rmsNorm`, `fderiv_suffix_last_of_differentiable`, `fderiv_params_suffix_last_eq_mul`, `suffix_castSucc_eq_comp_block`, `analyticOnNhd_block_comp`, `fderiv_suffix_castSucc_of_analytic`, `fderiv_eval_eq_fderiv_suffix_of_analytic`, `fderiv_eval_eq_fderiv_suffix_rmsNorm`, `differentiable_suffix_prod_of_differentiable` | `Depth/SuffixRMS.lean`, `Depth/StepTanhRMS.lean` | proved |
| the antisymmetric matrices (the directions of the orthogonal changes of basis; their dimension is in `finrank_antisymmetric`); the centering matrix `Z` of Proposition A.3; `Q⁻¹ = Qᵀ` for an orthogonal `Q` | `antisymmetric`, `centering`, `coe_inv_of_mem_orthogonalGroup` | `Dimension/UpperBoundRMSNorm.lean`, `Basic/LayerNorm.lean`, `Symmetry/Normalized.lean` | defined / proved |
| helpers shared by the one-block theorems: `X ↦ cobDir θ X` as a linear map, the weights as linear maps of `θ`, analyticity of the entries of `E W_read` and `W_write D`, the derivative along a line `θ + τη` | `cobDirLin`, `finrank_cobDomain`, `Params.linE`, `Params.linRead`, `Params.linWrite`, `Params.linD`, `analyticOnNhd_E_mul_read`, `analyticOnNhd_write_mul_D`, `ae_ne_zero_of_analytic`, `rank_eq_card_of_isUnit_det`, `exists_minor_ne_zero`, `hasDerivAt_eval_line`, `differentiable_f_mlp`, `differentiable_f_gated` | `OneBlock/Common.lean` | proved |

Notes for the authors on these statements:
- Proposition 3.3 is stated in both forms: for one hidden state, as in the paper
  (`Symmetry/AtOneState.lean`), and at all hidden states at once (`Symmetry/Reduction.lean`), after
  the remark of the proof that the reductions can be made together. In (i) the simultaneous form
  needs the invertible columns at every hidden state, so it does not contain the paper's form.
- Proposition 3.3 (ii): the Lean statements do not assume that the chosen columns are invertible
  (a QR factorization exists for every square matrix; `exists_cob_reads_upperTriangular`), and the
  one-state form does not use that `R` is upper triangular. The paper assumes both.
- Lemma B.1: the Lean statements say that the directions of the symmetries determine the matrices
  `X` and the numbers `α`, under the rank conditions of the proof. This is what the proof of
  Theorem 4.3 uses. The statement about the group ("no continuous family fixes `θ`") and its
  equivalence with this form are not stated; ReLU, ReLU², the gate of ReGLU and attention are not
  covered.
- "At generic parameters" is written `∀ᵐ θ ∂μ` for an arbitrary additive Haar measure `μ` on the
  parameter space: a Lebesgue measure of that space, without a choice of coordinates. Any two
  differ by a positive constant, so they have the same sets of measure zero.
- Lemma C.3 for SwiGLU and for GeGLU: the paper's hypothesis "(e_i, β'_i) not proportional to
  (c_i, β_i)" is not used by the proofs; only `e_i ≠ 0` is needed. Both forms are stated and proved,
  and the conditions of the one-block theorem for gated blocks (`OneBlockGenericGated`) leave the
  hypothesis out.
- Lemma C.3 for ReGLU: the proof uses the hypothesis on proportionality (a numerical check gives a
  larger kernel without it) and does not use `e_i ≠ 0`, which that hypothesis implies for the
  multiple `0`.
- Theorem 5.1 is stated once for every activation that satisfies the conclusion of Lemma C.3
  (`OneBlock/Mlp.lean` for `s = 0`, `OneBlock/Gated.lean` for the rescalings of the values). Steps 1
  and 3 of the paper's proof do not depend on the activation; the cases tanh, GELU, SwiGLU and GeGLU
  are corollaries, with Lemma C.3 proved for each of the four in its own file.
- Appendix D takes inputs of one token, "since an MLP block acts on each token separately". The Lean
  statements keep hidden states with the rows `T` (any nonempty finite set of tokens), as the rest
  of the library: a row `ξ` of the paper is a matrix `Ξ` with one row per token, and Lemma D.1 is
  applied to the numbers `ξ_t c_j` over all tokens `t` and hidden units `j`. Lemmas D.3, D.5, D.7
  and Proposition D.4 are stated for at least one token. D.3 and D.5 fail for none. D.7 holds for
  none (its hypothesis fails then), and its Lean proof uses a token.
- Theorem 5.2 (i), without normalization and under pre-RMSNorm: the proof uses `d ≥ 1` only; the paper's `d ≥ 2` is kept in
  the final statement.
- Theorem 4.3 is stated under the conditions that its proof uses (`E` and every write have rank
  `d`, the maps `f_ℓ` are differentiable), and then at generic parameters for the changes of basis.
  The number `s` of the symmetries inside the blocks is counted for gated blocks, without
  normalization and under pre-RMSNorm, also at generic parameters (`Dimension/Rescaling.lean`,
  `Generic/Gated.lean`); for tanh and GELU blocks `s = 0`. Not stated yet: the blocks with `s > 0`
  other than SwiGLU and GeGLU (ReLU, ReLU², ReGLU, attention).
- ReLU blocks and the functional dimension. The paper takes the Jacobian of a ReLU, ReLU² or ReGLU
  network at the inputs at which no hidden unit sits at its kink. In Lean `funDim` is the largest
  rank over all finite batches, and Mathlib's derivative is `0` where a map is not differentiable,
  so a batch with an input at which the network is not differentiable in `θ` has rank `0`: `funDim`
  is the largest rank over the batches of inputs at which the network is differentiable in `θ`,
  a set that contains the paper's. For each kind of block two statements are made: the value of
  `funDim`, and a batch of the paper's inputs with that rank. Together they give the paper's
  maximum. The statements marked with a prime hold with no hypothesis of differentiability, and
  those on the upper bound under pre-RMSNorm for every real `ε`.
- The Jacobian needs a norm on the parameters and on the outputs. Matrices carry the elementwise
  norm; on finite-dimensional spaces the derivative does not depend on the norm. The derivative of
  a map that is not differentiable is `0` in Mathlib, so the statements on the functional
  dimension assume that `θ ↦ F_θ(x)` is differentiable at `θ`.
- Proposition A.3 is not stated for whole networks: it needs gains and biases, which the network
  definition does not have yet. Only the computations of its proof are stated.
- Proposition 3.3, "these changes of basis at all `L+1` hidden states remove `(L+1) dim 𝒢`
  parameters": the count has no Lean statement of its own. The entries that become fixed are those
  of an identity submatrix (`d²`), or those below the diagonal of a triangular one
  (`card_below_diagonal`), one submatrix per hidden state.
- Not stated yet from the main text: Example 4.2; Definitions 4.4 and 4.5, Proposition 4.6 and
  Corollary 5.3 (the equality condition and identifiability); Theorem 4.3 for ReLU, ReGLU and
  attention blocks, with the term `s` for ReLU², and its remark for `ε = 0`; Theorem 5.1 for ReLU,
  ReLU², ReGLU and attention blocks; Theorem 5.2 (i) for `ε = 0`, (ii) and (iii). No attention block
  is defined in Lean yet.

### Skips paper

| Paper | Lean statement | File | Status |
|---|---|---|---|
| S eq. (7): `Λ_ℓ = A_{ℓ+1}⋯A_L`, `A_ℓ Λ_ℓ = Λ_{ℓ-1}` | `skipProd`, `skipProd_last`, `skipProd_castSucc` | `Residual/LearnedSkips.lean` | proved |
| S Theorem 3.2 (i) | `eval_learned_eq_residual`, `cob_skipProd_D` | `Residual/LearnedSkips.lean` | proved |
| S Theorem 3.2 (ii), first sentence (orthogonal skips) | `eval_learned_eq_residual_rmsNorm` | `Residual/LearnedSkips.lean` | proved |
| S Theorem 3.3 (i), "if", without normalization | `eval_cob_residual` | `Symmetry/ChangeOfBasis.lean` | proved |
| S Theorem 3.3 (i), "if", under pre-RMSNorm | `eval_cob_residual_rmsNorm` | `Residual/LearnedSkips.lean` | proved |
| S Theorem 3.3 (iii), without normalization | `exists_cob_residual_read_eq_one`, `exists_cob_residual_D_eq_one` | `Residual/LearnedSkips.lean` | proved |
| S Theorem 3.3 (iii), under pre-RMSNorm, read of a block and the readout `D` (no invertibility is used) | `exists_cob_residual_read_upperTriangular`, `exists_cob_residual_D_upperTriangular` | `Residual/LearnedSkips.lean` | proved |
| S Theorem 4.2, with identity skips, without the term `s` (changes of basis only): `fd ≤ P − d²` | `cobDir_const_mem_flat_residual`, `funDim_add_le_residual` | `Dimension/UpperBound.lean` | proved |
| S Theorem 4.2, with identity skips, without the term `s`, under pre-RMSNorm (`ε > 0`): `fd ≤ P − d(d−1)/2` | `funDim_add_le_residual_rmsNorm` | `Dimension/UpperBoundRMSNorm.lean` | proved |
| S Theorem 4.2, with identity skips, without the term `s`, at generic parameters (only `d_in ≥ d` is used) | `ae_funDim_add_le_residual`, `ae_funDim_add_le_residual_rmsNorm` | `Generic/Params.lean` | proved |
| S Theorem 3.3 (i), "only if", without normalization: if every block is nonzero for some value of its parameters and `G_0, …, G_L` preserve the function of the residual network for all values of the parameters, then `G_0 = ⋯ = G_L`; and the equivalence (the hypothesis on the blocks is that of Theorem A.5 (iii); its `d ≥ 2` is not used) | `cob_eq_of_eval_cob_residual`, `eval_cob_residual_iff` | `Residual/OneChangeOfBasis.lean` | proved |
| S Theorem 3.3 (i), "only if", under pre-RMSNorm (`ε > 0`): the same, and the common matrix is orthogonal; and the equivalence | `cob_eq_orthogonal_of_eval_cob_residual_rmsNorm`, `eval_cob_residual_rmsNorm_iff` | `Residual/OneChangeOfBasis.lean` | proved |
| S Theorem 3.2 (ii), second sentence: under pre-RMSNorm, orthogonal `Q_0 = I, Q_1, …, Q_L` make every `Q_{ℓ−1}ᵀ A_ℓ Q_ℓ` upper triangular and preserve the function (RQ factorization) | `exists_orthogonal_mul_upperTriangular`, `exists_cob_learned_upperTriangular` | `Residual/OneChangeOfBasis.lean` | proved |
| S Theorem 4.2 with identity skips, for the change of basis, for arbitrary maps `f_ℓ` (no differentiability): `fd ≤ P − d²` without normalization, `fd ≤ P − d(d−1)/2` under pre-RMSNorm (every real `ε`); only `E` of rank `d` is used | `cobDir_const_mem_flat_residual'`, `cobDir_const_mem_flat_residual_rmsNorm'`, `funDim_add_le_residual'`, `funDim_add_le_residual_rmsNorm'` | `Residual/UpperBoundSymmetries.lean` | proved |
| **S Theorem 4.2 with identity skips, with the term `s`:** `fd ≤ P − dim 𝒢 − s`, without normalization and under pre-RMSNorm, under the conditions of the proof and at generic parameters (`d_in ≥ d`): gated blocks with any gate (`s = ∑ d_hidden`); MLP blocks with a positively homogeneous activation, ReLU and ReLU² (`s = ∑ d_hidden`); gated blocks with a positively homogeneous gate, ReGLU (`s = 2 ∑ d_hidden`) | `funDim_add_le_residual_gated`, `funDim_add_le_residual_mlp_rescale`, `funDim_add_le_residual_gated_gate`, each also with `_rmsNorm`, and the six names with `ae_` in front | `Residual/UpperBoundSymmetries.lean` | proved |
| S Theorem 4.6 (i) / B.1 (i) for every activation that is positively homogeneous of degree `k`, differentiable away from `0` and satisfies Lemma C.3 with the rescalings: with a skip, a direction that is flat at the inputs with no hidden unit at its kink is a direction of one change of basis and of the rescalings; `fd = P − d² − d_hidden` under the conditions of the proof; the same rank on a batch of such inputs | `differentiableAt_eval_residual_of_mem_noKink`, `flatOn_noKink_le_mlp_rescale_residual`, `funDim_mlp_oneBlock_rescale_residual`, `exists_jacobianRank_mlp_oneBlock_rescale_residual` | `OneBlock/ResidualRescale.lean` | proved |
| **S Theorem 4.6 (i) for a ReLU block and for a ReLU² block:** at generic parameters (`d_in, d_out, d_hidden ≥ d ≥ 2`) the residual network has `fd = P − d² − d_hidden`, the Jacobian has this rank on a batch of inputs with no hidden unit at its kink, and the skip raises `fd` by exactly `d²` | `ae_funDim_relu_oneBlock_residual`, `ae_exists_jacobianRank_relu_oneBlock_residual`, `ae_funDim_relu_oneBlock_residual_eq_add`, and the three names with `reluSq` | `OneBlock/ResidualRescale.lean` | proved |
| **S Theorem 4.6 (i) for a ReGLU block:** with a skip, a direction that is flat at the inputs with no gate at its kink is a direction of one change of basis and of the two kinds of rescalings; under the conditions of the proof and at generic parameters (`d_in, d_out, d_hidden ≥ d ≥ 2`) the residual network has `fd = P − d² − 2d_hidden`, the Jacobian has this rank on a batch of inputs with no gate at its kink, and the skip raises `fd` by exactly `d²` | `flatOn_noKinkGate_le_reglu_residual`, `funDim_reglu_oneBlock_residual`, `exists_jacobianRank_reglu_oneBlock_residual`, `ae_funDim_reglu_oneBlock_residual`, `ae_exists_jacobianRank_reglu_oneBlock_residual`, `ae_funDim_reglu_oneBlock_residual_eq_add` | `OneBlock/ReGLU.lean` | in work |
| the rescalings of a gated network are flat for every stream matrices (no skips, identity skips, learned skips) | `rescaleDir_mem_flat_stream` | `Dimension/Rescaling.lean` | proved |
| S Theorem 4.6 (i) / B.1 (i), without normalization and biases, for every activation that satisfies Lemma C.3 with no rescaling: one residual block has `fd = P − d²` under the conditions of the proof and at generic parameters; a flat direction is that of one change of basis (Lemma B.2: `E(X − Y)D = 0` gives `X = Y`); the skip raises `fd` by exactly `d²` | `flat_le_range_cobDir_const_mlp_residual`, `funDim_mlp_oneBlock_residual`, `ae_funDim_mlp_oneBlock_residual`, `ae_funDim_mlp_oneBlock_residual_eq_add` | `OneBlock/Residual.lean` | proved |
| S Theorem 4.6 (i) / B.1 (i) for gated blocks whose gate satisfies Lemma C.3: `fd = P − d² − d_hidden`; the skip raises `fd` by exactly `d²` | `flat_le_cobDir_const_add_rescaleDir_gated_residual`, `funDim_gated_oneBlock_residual`, `ae_funDim_gated_oneBlock_residual`, `ae_funDim_gated_oneBlock_residual_eq_add` | `OneBlock/Residual.lean` | proved |
| S Theorem 4.6 (i) for a tanh, a GELU, a SwiGLU and a GeGLU block: at generic parameters `fd(residual) = fd(skipless) + d²` | `ae_funDim_tanh_oneBlock_residual_eq_add`, `ae_funDim_gelu_oneBlock_residual_eq_add`, `ae_funDim_swiglu_oneBlock_residual_eq_add`, `ae_funDim_geglu_oneBlock_residual_eq_add` | `OneBlock/Residual.lean` | proved |

Not stated yet from the main text of the skips paper: Theorem 3.3 (ii), the dimensions of the
groups; the term `s` of attention blocks in Theorem 4.2; Definitions 4.3, 4.4 and Proposition 4.5;
Theorem 4.6 (i) for ReGLU and attention blocks and with biases, and Theorem 4.6 (ii);
Theorem 4.7; Corollaries 4.8 to 4.10; Theorem 4.11. Lemma B.2, "a direction keeps `M` if and only if
`X = Y`", is inside the proofs of `OneBlock/Residual.lean` and is not a statement of its own.

### Absorb paper

A block of the paper acts on a row `x`; a width is an index type, so "of any width" is a
quantifier over index types. Networks are those of the library (`eval`, with the stream matrices
`1`, `0` or learned skips); a skipless network that is compared with a residual one has its own
depth, widths and model dimension. The one-block statements of `Absorb/Block.lean`,
`NoWidth.lean` and `SameWidth.lean` are for rectangular weights (`p` inputs, `q` outputs), which
contains the paper's `p = q = d`; those of `Absorb/FewerUnits.lean` are square, as in the paper.
`Absorb/PaperForms.lean` states the cases that the paper names (the linear term `I`, ReLU and GELU,
the named kinds of network) as instances of the general statements.

| Paper | Lean statement | File | Status |
|---|---|---|---|
| A eq. (1): a vanilla block `B(x) = σ(x W_read) W_write`; a gated block; on a hidden state a vanilla block acts on each token (`map_mul_mul_row`; no such statement connects `gatedBlock` with the gated networks `Arch.gated`, which have the same formula) | `vanillaBlock`, `gatedBlock`, `map_mul_mul_row` | `Absorb/Block.lean` | proved |
| A eq. (3) for ReLU: `σ(z) − σ(−z) = z` (for GELU: `gelu_sub_gelu_neg`) | `relu_sub_relu_neg` | `Absorb/Block.lean` | proved |
| A Section 3.1, "At the same width": for `σ(z) − σ(−z) = cz`, flipping the reads of the units in `S` changes the block by `−c x W_read[:,S] W_write[S,:]` | `flipCols`, `subProd`, `vanillaBlock_flipCols` | `Absorb/Block.lean` | proved |
| A Theorem 3.1 (i), "if": `W_read[:,S] W_write[S,:] = −M` gives a block of the same width that computes `xM + B(x)` | `vanillaBlock_flipCols_of_subProd` | `Absorb/Block.lean` | proved |
| A Proposition A.11 (i) / Theorem 3.1 (ii), first half: read of rank `d` ⇒ a block with `d` more hidden units computes `xM + B(x)` (stated for every `M` and for `σ(z) − σ(−z) = cz`, `c ≠ 0`) | `exists_vanillaBlock_add_linear` | `Absorb/Block.lean` | proved |
| A "nondegenerate": the columns of `W_read` nonzero and pairwise non-collinear, the rows of `W_write` nonzero; generic blocks are nondegenerate (`p ≥ 2`, at least one output) | `Nondegenerate`, `ae_nondegenerate` | `Absorb/SameWidth.lean` | proved |
| A proof of Theorem 4.5, "GELU": `GELU(y) − ReLU(y) = −|y|Φ(−|y|)`, bounded by `1` (the paper: by `κ < 0.17`); a GELU block equation `xM + B(x) = B′(x)` implies the ReLU equation with the same weights (along rays; for one block, the paper has networks of any depth) | `gelu_sub_relu`, `abs_gelu_sub_relu_le`, `relu_absorb_of_gelu_absorb` | `Absorb/SameWidth.lean` | proved |
| A Corollary A.9 / Theorem A.4 (ReLU), Theorem A.7 (GELU), "only if" (nondegenerate; the paper's `p ≥ 2` is not needed): a block of the same width that computes `xM + B(x)` gives a set `S` with `W_read[:,S] W_write[S,:] = −M` | `exists_subProd_eq_neg_of_relu_absorb`, `exists_subProd_eq_neg_of_gelu_absorb` | `Absorb/SameWidth.lean` | proved |
| A Theorem 3.1 (i), first sentence / Corollary A.9: the equivalence | `relu_absorb_same_width_iff`, `gelu_absorb_same_width_iff` | `Absorb/SameWidth.lean` | proved |
| A Theorem 3.1 (i), second sentence: for `M ≠ 0` and generic `θ`, no block of the same width (`p ≥ 2`, the paper's `d ≥ 2`) | `ae_forall_subProd_ne_neg`, `ae_not_relu_absorb_same_width`, `ae_not_gelu_absorb_same_width` | `Absorb/SameWidth.lean` | proved |
| A Proposition 3.2 (ReLU, GELU; `d_in, d_out, d_hidden ≥ d ≥ 2`): at generic weights a residual network of one block equals no skipless network of one block of the same width, of any model dimension | `ae_ne_skipless_oneBlock_relu`, `ae_ne_skipless_oneBlock_gelu` | `Absorb/SameWidth.lean` | proved |
| A Proposition A.11 (ii) under the conditions of its proof (nondegenerate; `M + W_read[:,S] W_write[S,:]` invertible for every `S`): no block with fewer than `m + d` hidden units computes `xM + B(x)` | `exists_ne_of_relu_card_lt`, `exists_ne_of_gelu_card_lt` | `Absorb/FewerUnits.lean` | proved |
| A Theorem 3.1 (ii), second half / Proposition A.11 (ii): `M` invertible, `d ≥ 2`, generic `θ`: none with fewer than `d` more hidden units | `ae_forall_isUnit_det_add_subProd`, `ae_not_relu_absorb_of_card_lt`, `ae_not_gelu_absorb_of_card_lt` | `Absorb/FewerUnits.lean` | proved |
| A Proposition A.1 (homogeneous blocks, degree `k ≠ 1`) | `exists_ne_of_homogeneous` | `Absorb/NoWidth.lean` | proved |
| A Proposition A.2 (gated blocks whose gates vanish at `0` and are differentiable there) | `exists_ne_of_gated` | `Absorb/NoWidth.lean` | proved |
| A Theorem 3.3 (a): ReLU² and ReGLU blocks (homogeneous of degree 2) | `vanillaBlock_reluSq_smul`, `gatedBlock_relu_smul`, `exists_ne_reluSq`, `exists_ne_reglu` | `Absorb/NoWidth.lean` | proved |
| A Theorem 3.3 (b): SwiGLU and GeGLU blocks | `exists_ne_swiglu`, `exists_ne_geglu` | `Absorb/NoWidth.lean` | proved |
| A Theorem 3.3 (c): `tanh` blocks | `exists_ne_tanh` | `Absorb/NoWidth.lean` | proved |
| A Proposition 4.4: `σ(z) − σ(−z) = z`, no normalization, reads of rank `d` ⇒ the residual network equals a skipless network with `d` more hidden units per block and the same `E`, `D` | `exists_skipless_eq_residual_of_rank_read` | `Absorb/Networks.lean` | proved |
| A Corollary A.3, what its proof uses of the blocks: each block maps `0` to `0` and has derivative `0` there; true for gated blocks whose gate vanishes at `0` and is differentiable there, and for ReLU² and ReGLU blocks | `Arch.FlatAtZero`, `flatAtZero_gated`, `hasFDerivAt_zero_of_homogeneous`, `flatAtZero_mlp_reluSq`, `flatAtZero_gated_relu` | `Absorb/Networks.lean` | proved |
| A Theorem 4.1 (i) / Corollary A.3: `ED ≠ 0`, such blocks in both networks, no normalization or pre-RMSNorm with `ε > 0`: no skipless network of one or more blocks equals the residual one | `exists_ne_residual_skipless_of_flatAtZero`, `exists_ne_residual_skipless_of_flatAtZero_rmsNorm` | `Absorb/Networks.lean` | proved |
| A Theorem 4.1 (ii): `tanh` blocks without normalization | `exists_ne_residual_skipless_tanh` | `Absorb/Networks.lean` | proved |
| A Proposition 5.4 (i): for `σ(z) − σ(−z) = cz` the skipless network equals the network with the learned skips `cK_ℓ` and flipped reads (an identity, for any sets `S_ℓ`); at generic weights the skips are invertible | `Params.flipReads`, `eval_skipless_eq_learned_flipReads`, `ae_exists_learned_skips_eq_skipless` | `Absorb/Networks.lean` | proved |
| A Proposition 5.4 (ii): at generic weights the skipless network equals a residual network with the same `D`, `d` and widths, with `E′D ≠ 0` | `ae_exists_residual_eq_skipless` | `Absorb/Networks.lean` | proved |
| A proof of Proposition 5.1, its inequalities (sup norms; the paper's `‖N(y′) − N(y)‖ ≤ 2√d ‖y′ − y‖/‖y‖` with the constant `2d`) | `norm_mul_norm_inv_smul_sub_le`, `norm_mul_norm_rmsRow_zero_sub_le`, `rmsNorm_zero_smul`, `norm_rmsNorm_zero_sub_le`, `norm_rmsNorm_zero_le`, `norm_mul_le_card`, `lipschitzWith_mul_right` | `Absorb/Limits.lean` | proved |
| A Theorem A.4 (ReLU) and Theorem A.7 (GELU): nondegenerate block; `x + B(x) = B′(x)` has a solution of the same width iff `W_read[:,S] W_write[S,:] = −I` for some `S` (the instance `M = I`; the `d ≥ 2` of Theorem A.4 is not used) | `relu_absorb_identity_iff`, `gelu_absorb_identity_iff` | `Absorb/PaperForms.lean` | proved |
| A Corollary A.10 (ReLU, GELU; `d ≥ 2`): for generic weights `x + B(x) = B′(x)` has no solution (the instance `M = I`), and a skipless block equals no residual block of the same width (the instance `M = −I`) | `ae_not_relu_absorb_identity`, `ae_not_gelu_absorb_identity`, `ae_not_relu_skipless_eq_residual`, `ae_not_gelu_skipless_eq_residual` | `Absorb/PaperForms.lean` | proved |
| A Theorem 3.1 (ii), first half / Proposition A.11 (i), for ReLU and for GELU (for every `M`) | `exists_relu_block_add_linear`, `exists_gelu_block_add_linear` | `Absorb/PaperForms.lean` | proved |
| A Proposition 4.4 for ReLU and for GELU | `exists_skipless_eq_residual_relu`, `exists_skipless_eq_residual_gelu` | `Absorb/PaperForms.lean` | proved |
| A Theorem 4.1 (i), second class of blocks: fixed maps that are positively homogeneous of degree `k > 1` and bounded on the unit sphere (true for continuous maps) vanish at `0` with derivative `0` | `flatAtZero_of_homogeneous`, `flatAtZero_of_homogeneous_of_continuous` | `Absorb/PaperForms.lean` | proved |
| **A Theorem 4.1 (i)** for its two classes of blocks (gated blocks whose gate vanishes at `0` and is differentiable there; positively homogeneous blocks of degree `> 1`, bounded on the unit sphere), without normalization and under pre-RMSNorm with `ε > 0` | `exists_ne_residual_skipless_gated`, `exists_ne_residual_skipless_gated_rmsNorm`, `exists_ne_residual_skipless_homogeneous`, `exists_ne_residual_skipless_homogeneous_rmsNorm` | `Absorb/PaperForms.lean` | proved |
| A Theorem 4.1 (i) for SwiGLU, GeGLU, ReLU² and ReGLU networks, without normalization and under pre-RMSNorm with `ε > 0` | `exists_ne_residual_skipless_swiglu`, `exists_ne_residual_skipless_geglu`, `exists_ne_residual_skipless_reluSq`, `exists_ne_residual_skipless_reglu`, and the four names with `_rmsNorm` | `Absorb/PaperForms.lean` | proved |
| A Theorem 4.5, the conditions of its proof on the weights of the residual network (`E`, `D` of rank `d`; no read of a hidden unit zero; `I + W_read[:,S] W_write[S,:]` invertible for every block and every `S`), which hold for almost every choice of weights (`d_in, d_out ≥ d ≥ 1`) | `FirstBlockGeneric`, `ae_firstBlockGeneric` | `Absorb/FirstBlock.lean` | proved |
| **A Theorem 4.5 for ReLU:** under these conditions, and for almost every choice of weights (`d_in, d_out ≥ d`), a residual ReLU network equals no skipless ReLU network whose first block has fewer than `2d` hidden units, whatever its model dimension, depth and other widths | `exists_ne_skipless_of_first_card_lt_relu`, `ae_ne_skipless_of_first_card_lt_relu` | `Absorb/FirstBlock.lean` | proved |
| A proof of Theorem 4.5, "GELU", for networks: without normalization, with or without skips, `F(tX)/t` of a GELU network tends as `t → ∞` to the output at `X` of the ReLU network with the same weights | `Params.withActivation`, `tendsto_eval_gelu_ray` | `Absorb/FirstBlock.lean` | proved |
| **A Theorem 4.5 for GELU:** the same two statements for GELU networks | `exists_ne_skipless_of_first_card_lt_gelu`, `ae_ne_skipless_of_first_card_lt_gelu` | `Absorb/FirstBlock.lean` | proved |
| A Theorem 4.3, the conditions of its proof on the weights of the residual network (`E`, `D` of rank `d`; at some normalized state `n̄`, with every row of norm `√d`, some row of `β(n̄) = ∑_ℓ f_ℓ(n̄ W_read^ℓ) W_write^ℓ` is not a multiple of the same row of `n̄`) | `TurnGeneric` | `Absorb/RMSNormRays.lean` | defined |
| **A Theorem 4.3, under these conditions** (Appendix A.3, "The skipless network", "The residual network", "Comparison"), blocks of any kind (`f_ℓ` locally Lipschitz): for `ε > 0` the residual network differs at some input from every pre-RMSNorm skipless network with locally Lipschitz blocks, of any depth, model dimension, widths and constant `ε′ > 0`; for `ε = 0`, in the paper's sense of equality (Section 2), there is no dense set of inputs at which both networks are defined and agree (skipless blocks continuous) | `exists_ne_skipless_rmsNorm_of_turn`, `not_dense_eq_skipless_rmsNorm_zero_of_turn` | `Absorb/RMSNormRays.lean` | in work |
| A Theorem 4.3, "Measure zero": if the `f_ℓ` are continuous and for almost every choice of weights some block has a nonzero output at some normalized state, the conditions hold for almost every choice of weights (`d_in, d_out ≥ d ≥ 2`); the hypothesis holds for MLP blocks and gated blocks whose activation or gate is nonzero on the positive reals, when some block has a hidden unit | `SomeBlockNonzero`, `ae_turnGeneric`, `ae_someBlockNonzero_mlp`, `ae_someBlockNonzero_gated`, `locallyLipschitz_f_mlp`, `locallyLipschitz_f_gated` | `Absorb/RMSNormGeneric.lean` | in work |
| **A Theorem 4.3 (almost no equality under RMSNorm):** for almost every choice of weights, the residual network equals no skipless network, for `ε > 0` and for `ε = 0`: for blocks of any kind under the hypothesis above, and for residual networks of MLP blocks and of gated blocks with `σ` locally Lipschitz and nonzero on the positive reals. Not stated: the seven named kinds as corollaries (they need `LocallyLipschitz` of each activation), and attention blocks | `ae_ne_skipless_rmsNorm`, `ae_not_dense_eq_skipless_rmsNorm_zero`, `ae_ne_skipless_rmsNorm_mlp`, `ae_not_dense_eq_skipless_rmsNorm_zero_mlp`, `ae_ne_skipless_rmsNorm_gated`, `ae_not_dense_eq_skipless_rmsNorm_zero_gated` | `Absorb/RMSNormGeneric.lean` | in work |
| A Proposition 5.1 (i) with the rate of Remark A.16: no normalization, locally Lipschitz fixed maps `f_ℓ` (the paper asks it of the blocks, which follows); the residual networks `F_t` (reads `t^{1−ℓ}W_read^ℓ`, writes `t^ℓ W_write^ℓ`, readout `t^{−L}D`) satisfy `‖F_t(X) − F(X)‖ ≤ C/t` on every bounded set of inputs, for `t ≥ 1`; uniform limit | `Params.limitScale`, `exists_bound_eval_limitScale`, `tendstoUniformlyOn_eval_limitScale` | `Absorb/Limits.lean` | proved |
| A Proposition 5.1 (ii) with the rate: pre-RMSNorm with `ε = 0`, locally Lipschitz `f_ℓ`; `F_t` with the writes `t^ℓ W_write^ℓ`; on every compact set of inputs at which `F` is defined, for `t ≥ t_0`, `F_t` is defined and `‖F_t(X) − F(X)‖ ≤ C/t`; uniform limit | `Params.writeScale`, `DefinedAt`, `exists_bound_eval_writeScale`, `tendstoUniformlyOn_eval_writeScale` | `Absorb/Limits.lean` | proved |

Notes for the authors on these statements:
- Proposition A.1 is stated for arbitrary maps `B`, `B′` with `B(λx) = λ^k B(x)` for `λ > 0`: its
  proof uses nothing else.
- Theorem 4.1 (i): the general Lean statements assume that every fixed map `f_ℓ` vanishes at `0`
  with derivative `0` (`Arch.FlatAtZero`), which is what the proof of Corollary A.3 uses, and allow
  blocks of different kinds and different `ε > 0` in the two networks. The paper's "positively
  homogeneous of degree `k > 1`" gives this only for maps that are bounded on the unit sphere
  (`O(‖x‖^k)` in the proof of Corollary A.3): the Lean statements for this class carry the bound
  as a hypothesis, and a continuous map has it. ReLU² and ReGLU blocks satisfy it. The homogeneity
  is assumed of the fixed map `f_ℓ`, which makes the block homogeneous for all weights.
- Proposition A.11 (i) does not use that `M` is invertible.
- Which statements hold for every `σ` with `σ(z) − σ(−z) = cz`: only those of the direction "more
  units suffice" (Theorem 3.1 (i) "if", Theorem 3.1 (ii) first half, Propositions A.11 (i), 4.4 and
  5.4). The converse statements (Theorem 3.1 (i) "only if" and its generic clause, "none with
  fewer", Proposition 3.2) are stated for ReLU and GELU only, as in the paper, and are false for
  some such `σ`: for `σ(z) = z/2 + |z|³` (Remark A.8) the rescaling `(c_i, a_i) ↦ (λc_i, a_i/λ³)` of
  a hidden unit changes the block by a linear term, so a block of the same width absorbs `xM` for
  many `M`.
- Corollary A.9 and Theorem 3.1 (i), first sentence: the proof does not use `p ≥ 2` (for one input a
  nondegenerate read has at most one hidden unit), so the Lean statements leave it out. The generic
  clause needs it (two rows, for the columns to be pairwise non-collinear at generic weights).
- Proposition A.11 (ii): the Lean proof is shorter than the paper's. The units of the absorbing
  block that are matched to no unit of `B` number fewer than `d`, so some row `x ≠ 0` is orthogonal
  to all their reads; at this `x` the odd part of the equation gives `x (M + W_read[:,S] W_write[S,:])
  = 0`, against the invertibility. No classes of collinear reads and no count of mixed classes are
  needed. The statement under explicit conditions does not use `d ≥ 2`.
- Three helper lemmas are public. From the proof of Corollary A.9, for blocks of different widths:
  `exists_dotProduct_eq_zero_and_ne_zero` (a point of a hyperplane off finitely many others) and
  `write_eq_sum_of_abs_eq` (the write row of a unit is the sum of `|c_j|` times the write rows of the
  units of the other block whose reads are `c_j` times its read). From `Absorb/FewerUnits.lean`:
  `exists_ne_zero_forall_dotProduct_eq_zero` (fewer than `d` vectors of `ℝ^d` have a common nonzero
  orthogonal vector).
- Theorem 3.1 for GELU: the paper proves the "only if" of (i) through ridge functions (Lemmas A.5,
  A.6, Theorem A.7). The Lean statements for GELU are proved from the case of ReLU by the
  paper's reduction along rays (proof of Theorem 4.5). Lemmas A.5 and A.6, and the further
  conclusion of Theorem A.7 (`W_write′ = W_write`), are not stated yet.
- "Generic `θ`" for one block is `∀ᵐ` for an additive Haar measure on the pairs
  `(W_read, W_write)`. To apply such a statement to the product of the Lebesgue measures of the
  entries, the instance `IsAddHaarMeasure` has to be given by hand.
- The first sentence of Corollary A.3 (compositions without embedding and readout) is the instance
  `E = D = I` of the statements for networks. "Exactly `d_model` units" (Theorem 3.1 (ii)) is two
  statements, one for each half.
- Not stated yet: Theorems 3.4, 4.2, 4.3; Propositions 4.6, 4.7; Remarks 5.2, 5.3; Lemmas A.5,
  A.6; Remarks A.8, A.12; Theorem A.13, Lemma A.14, Proposition A.15; Appendix C (blocks with
  biases).

