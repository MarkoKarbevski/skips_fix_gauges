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
A fourth reader (24 November 2026) compared the statements written after that commit for ReLU,
ReLU² and ReGLU blocks, the statements marked with a prime, `Absorb/FirstBlock.lean`,
`Residual/UpperBoundSymmetries.lean`, `OneBlock/ResidualRescale.lean` and `OneBlock/ReGLU.lean`
(22 paper statements against 94 Lean names): none false or vacuous; the notes on ReLU blocks and on
`ε = 0` below say what the definitions change. A fifth reader (24 November 2026) compared
`Absorb/RMSNormRays.lean`, `Absorb/RMSNormGeneric.lean`, `Absorb/RMSNormKinds.lean`,
`Dimension/GenericRank.lean`, `Activations/Analytic.lean`, `Depth/SuffixGated.lean`,
`Depth/Cones.lean`, `Depth/StepGated.lean`, `Depth/GeluGatedExplicit.lean` and
`Depth/GeluGatedTheorem.lean` (16 paper statements and definitions against 81 Lean names): none
false, vacuous or changed in meaning; Lemma D.13 and the claim `(D_0)` at `θ†` are existence
statements in Lean, and Theorem 4.3 of the absorb paper for blocks of any kind holds under a
hypothesis that is proved for MLP blocks only. A sixth reader (24 November 2026) compared the
statements written for Lemma D.12 after the fifth audit began (`Activations/FarFromZero.lean`,
`Activations/MillsAtInfinity.lean`, `Activations/GateFar.lean`, `Activations/OneSmallFactor.lean`,
`Depth/BlockIdentityGated.lean`, `Depth/RayInduction.lean`, `Depth/RayDense.lean`, `Depth/Frozen.lean`,
`Depth/FrozenFar.lean`, `Depth/SuffixFlatConverse.lean`, `Depth/RayGatedN.lean`,
`Depth/StepsGatedN.lean`, `Depth/ScaledSuffix.lean`, `Depth/RayGatedPlus.lean`,
`Depth/RayMlpPlus.lean`, `Depth/StepsPlus.lean`, and the header and proofs of
`Depth/StepGated.lean`; 19 paper statements and proof pieces against 79 Lean names): none false,
vacuous or changed in meaning; the statements of `Depth/RayGatedPlus.lean` and
`Depth/RayMlpPlus.lean` were judged by hand, before their proofs were written. The same reader
checked three points on the whole library: every statement "at generic parameters" is `∀ᵐ θ ∂μ` for
an additive Haar measure `μ` (a program took apart all 121 such theorems; none is an existence
statement or a statement on an open set); `funDim` is the largest rank of the Jacobian over all
finite batches (Definition 4.1); and the statements of Theorem 5.2 (ii) for `ε > 0` and (iii) have
no hypothesis that the paper does not have, except at least one token. Not yet compared by such a
reader (written after the sixth audit began): `Symmetry/OnlyOrthogonal.lean`,
`Residual/SmallParameter.lean`, `Residual/SmallWrites.lean`, `Residual/DepthMlp.lean`,
`Residual/DepthGated.lean`, `Residual/ExactGain.lean`, `OneBlock/ResidualRMSSteps.lean`,
`OneBlock/ResidualRMSMlp.lean`, `OneBlock/ResidualRMSGated.lean` and `OneBlock/ResidualRMSGain.lean`.

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
in work are on the branch `lean-wip` (it follows the working branch `lean-plus`). A row marked *proved* may list definitions among its names
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
| D Theorem 4.3, without normalization, changes of basis only, under the conditions of the proof (`E` and every write of rank `d`): `fd ≤ P − (L+1)d²` | `cobDir_mem_flat_skipless`, `funDim_add_le_skipless` | `Dimension/UpperBound.lean` | proved |
| D Theorem 4.3, under pre-RMSNorm (`ε > 0`), changes of basis only, under the conditions of the proof (`E` and every write of rank `d`): `fd ≤ P − (L+1)d(d−1)/2` | `differentiable_rmsNorm`, `cobDir_mem_flat_skipless_rmsNorm`, `finrank_antisymmetric`, `funDim_add_le_skipless_rmsNorm` | `Dimension/UpperBoundRMSNorm.lean` | proved |
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
| D Theorem 4.3 for gated blocks, without normalization, under the conditions of the proof (`E` and every write of rank `d`, no vanishing value column): `fd ≤ P − (L+1)d² − s`, `s` the number of hidden units | `funDim_add_le_skipless_gated` | `Dimension/Rescaling.lean` | proved |
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
| D Appendix C, "Notation and flat directions", for blocks that are not differentiable everywhere: the directions flat at every input of a set `U`; `fd(θ) = P − dim K(θ)`, "a direction of a symmetry is flat" and the bound from a subspace of flat directions, with no hypothesis of differentiability; a batch of inputs of `U` on which the Jacobian has the rank `P − dim K_U(θ)`, if the network is differentiable in `θ` at every input of `U` | `flatOn`, `flat_le_flatOn`, `mem_flat_of_hasDerivAt'`, `funDim_add_finrank_flat'`, `funDim_add_finrank_le_of_le_flat'`, `exists_jacobianRank_add_finrank_flatOn` | `Dimension/Functional.lean` | proved |
| D Theorem 4.3 for the changes of basis, for arbitrary maps `f_ℓ` (no differentiability), under the conditions of the proof (`E` and every write of rank `d`): `fd ≤ P − (L+1)d²` without normalization, `fd ≤ P − (L+1)d(d−1)/2` under pre-RMSNorm (every real `ε`) | `cobDir_mem_flat_skipless'`, `funDim_add_le_skipless'`, `cobDir_mem_flat_skipless_rmsNorm'`, `funDim_add_le_skipless_rmsNorm'` | `Dimension/UpperBound.lean`, `Dimension/UpperBoundRMSNorm.lean` | proved |
| D Appendix B: the rescalings `(c_i, a_i) ↦ (λc_i, a_i/λ)` of a ReLU hidden unit and `(λc_i, a_i/λ²)` of a ReLU² hidden unit, `λ > 0`, preserve the function (stated for `σ(λz) = λ^k σ(z)`); their directions are flat | `relu_homogeneous`, `reluSq_homogeneous`, `eval_rescale_mlp`, `rescaleDirMlp`, `rescaleDirMlp_mem_flat` | `Dimension/RescalingMlp.lean` | proved |
| D Lemma B.1 for ReLU and ReLU² blocks, in infinitesimal form: the changes of basis and the rescalings move `θ` in independent directions (`E` and the writes of rank `d`, no column of a read zero) | `cobDir_add_rescaleDirMlp_injective` | `Dimension/RescalingMlp.lean` | proved |
| D Theorem 4.3 for ReLU and ReLU² blocks, with the term `s` (the number of hidden units), under the conditions of the proof and at generic parameters (`d_in ≥ d ≥ 1`, at least `d` hidden units per block), without normalization and under pre-RMSNorm (every real `ε`; for `ε = 0` see the note) | `funDim_add_le_skipless_mlp_rescale`, `funDim_add_le_skipless_mlp_rescale_rmsNorm`, `ae_read_col_ne_zero`, `ae_funDim_add_le_skipless_relu`, `ae_funDim_add_le_skipless_reluSq`, `ae_funDim_add_le_skipless_relu_rmsNorm`, `ae_funDim_add_le_skipless_reluSq_rmsNorm` | `Dimension/RescalingMlp.lean` | proved |
| D Appendix B, "ReGLU, in addition": the rescaling `(c_i, a_i) ↦ (λc_i, a_i/λ)` of the gate of a ReGLU hidden unit, `λ > 0`, preserves the function (stated for a gate with `σ(λz) = λ^k σ(z)`); its directions are flat; the directions of the rescalings of the values are flat with no hypothesis of differentiability | `eval_rescale_gate`, `rescaleDirGate`, `rescaleDirGate_mem_flat`, `rescaleDir_mem_flat'` | `Dimension/RescalingGate.lean`, `Dimension/Rescaling.lean` | proved |
| D Lemma B.1 for ReGLU blocks, in infinitesimal form: the changes of basis and the two rescalings move `θ` in independent directions (`E` and the writes of rank `d`, no gate column and no value column of a read zero) | `cobDir_add_rescaleDir_add_rescaleDirGate_injective` | `Dimension/RescalingGate.lean` | proved |
| D Theorem 4.3 for ReGLU blocks, with `s = 2 ∑ d_hidden`, under the conditions of the proof and at generic parameters (`d_in ≥ d ≥ 1`, at least `d` hidden units per block), without normalization and under pre-RMSNorm (every real `ε`; for `ε = 0` see the note) | `funDim_add_le_skipless_gated_gate`, `funDim_add_le_skipless_gated_gate_rmsNorm`, `ae_gate_ne_zero`, `ae_funDim_add_le_skipless_reglu`, `ae_funDim_add_le_skipless_reglu_rmsNorm` | `Dimension/RescalingGate.lean` | proved |
| D Lemma C.3 for ReLU and ReLU² as a property of the activation (the rescaling with exponent `k`) | `UnitsRescale`, `relu_unitsRescale`, `reluSq_unitsRescale` | `OneBlock/Rescale.lean` | proved |
| D Theorem 5.1 / C.1 for every activation that is positively homogeneous of degree `k`, differentiable away from `0` and satisfies Lemma C.3 with the rescalings: the inputs with no hidden unit at its kink; differentiability there; a direction that is flat at these inputs is a direction of the two changes of basis and of the rescalings; `fd = P − 2d² − d_hidden` under the conditions of the proof; the same rank on a batch of such inputs | `noKink`, `differentiableAt_eval_of_mem_noKink`, `flatOn_noKink_le_mlp_rescale`, `funDim_mlp_oneBlock_rescale`, `exists_jacobianRank_mlp_oneBlock_rescale` | `OneBlock/Rescale.lean` | proved |
| **D Theorem 5.1 / C.1 for a ReLU block and for a ReLU² block:** `d_in, d_out, d_hidden ≥ d ≥ 2`, at generic parameters `fd = P − 2d² − d_hidden`, and the Jacobian has this rank on a batch of inputs with no hidden unit at its kink | `ae_funDim_relu_oneBlock`, `ae_exists_jacobianRank_relu_oneBlock`, `ae_funDim_reluSq_oneBlock`, `ae_exists_jacobianRank_reluSq_oneBlock` | `OneBlock/Rescale.lean` | proved |
| D Theorem 5.1 / C.1 for a ReGLU block, the conditions of the proof: those of the other gated blocks, and no value column `e_i` of `C = E W_read` proportional to the gate column `c_i` of the same hidden unit (the hypothesis of Lemma C.3 that only ReGLU uses); they hold at generic parameters (`d_in, d_out, d_hidden ≥ d ≥ 2`). The inputs with no gate at its kink; the network is differentiable in `θ` there, with or without the skip | `OneBlockGenericReGLU`, `ae_oneBlockGenericReGLU`, `noKinkGate`, `differentiableAt_eval_of_mem_noKinkGate` | `OneBlock/ReGLU.lean` | proved |
| **D Theorem 5.1 / C.1 for a ReGLU block:** a direction that is flat at the inputs with no gate at its kink is a direction of the two changes of basis, of the rescalings of the values and of the rescalings of the gates; under the conditions of the proof and at generic parameters `fd = P − 2d² − 2d_hidden`, and the Jacobian has this rank on a batch of inputs with no gate at its kink | `flatOn_noKinkGate_le_reglu`, `funDim_reglu_oneBlock`, `exists_jacobianRank_reglu_oneBlock`, `ae_funDim_reglu_oneBlock`, `ae_exists_jacobianRank_reglu_oneBlock` | `OneBlock/ReGLU.lean` | proved |
| D Appendix D.7, "The parts together" (GELU and gated blocks): for a network with real-analytic `f_ℓ` and `χ` (the cases (n) and (+)), the output at a fixed input is real-analytic in `θ`, and at generic parameters the Jacobian on a batch has at least the rank that it has at any one parameter `θ₀`; hence `fd(θ₀) ≤ fd(θ)` for almost every `θ`. Stated for all stream matrices | `analyticOnNhd_eval_params`, `ae_jacobianRank_ge`, `ae_jacobianRank_le_funDim`, `ae_funDim_ge` | `Dimension/GenericRank.lean` | proved |
| D Section 1.1 ("These four kinds of block are real-analytic"), used in Appendix D: `φ`, `Φ`, GELU and SiLU are real-analytic; the map of a gated block is real-analytic if its gate is | `analyticOnNhd_gaussPdf`, `analyticOnNhd_gaussCdf`, `analyticOnNhd_gelu`, `analyticOnNhd_silu`, `analyticOnNhd_f_gated` | `Activations/Analytic.lean` | proved |
| D Claim `(D_k)` for gated blocks, eq. (19), with the changes of basis in a subspace `g` of matrices (all matrices in the case (n), the antisymmetric ones in the case (+)) and the diagonal matrices `Δ_ℓ` as the directions `rescaleDir θ α` | `ClaimGated` | `Depth/SuffixGated.lean` | defined |
| D Lemma D.5 for gated blocks: `(D_L)` holds, in the case (n) and, if `D` has rank `d`, in the case (+) | `claimGated_last`, `claimGated_last_rmsNorm` | `Depth/SuffixGated.lean` | proved |
| D Proposition D.4 for gated blocks, cases (n) and (+): if `θ` is regular and `(D_0)` holds, every flat direction is `cobDir θ X + rescaleDir θ α` (with `X_ℓ` antisymmetric in the case (+)); if moreover no value column vanishes, `fd = P − (L+1) d² − ∑ d_hidden`, resp. `P − (L+1) d(d−1)/2 − ∑ d_hidden` (the gate `σ` real-analytic) | `flat_le_cobDir_add_rescaleDir_of_claimGated`, `funDim_of_claimGated`, `flat_le_cobDir_add_rescaleDir_of_claimGated_rmsNorm`, `funDim_of_claimGated_rmsNorm` | `Depth/SuffixGated.lean` | proved |
| D Appendix D.5, "Cones and good parameters": open convex cones of rows without `0` (and nonempty, which the paper uses without saying); the block with its gates frozen on an active set, `g°(n) = ∑_{j∈A} (n c_j) ι_j(n) a_j`; "`θ` is good for the cones `C_0, …, C_L`": (R1), (K1) with the active sets as data, (K2), and the part of (K3) that does not depend on the kind of block. The independence over `ℚ` of (K3) is a separate hypothesis where it is used | `IsOpenConvexCone`, `frozenGated`, `frozenMlp`, `GoodForConesGated`, `GoodForConesMlp` | `Depth/Cones.lean` | defined |
| D Appendix D.5, "A good `θ` is regular", for SwiGLU, GeGLU and GELU blocks | `regular_of_goodForConesGated_swiglu`, `regular_of_goodForConesGated_geglu`, `regular_of_goodForConesMlp_gelu` | `Depth/Cones.lean` | proved |
| D Lemma D.13 (`θ†` is good), as existence: for `d_in, d_out ≥ d` and at least `d` hidden units per block there are cones, active sets and a parameter good for them, with the gate columns independent over `ℚ` (SwiGLU; `d ≥ 1`), or the matrices `c_j c_j^⊤` independent over `ℚ` (GeGLU, GELU; `d ≥ 2`). The explicit `θ†` and the formulas `g°_ℓ(n) = n`, `(n𝟙) n` are not stated | `exists_goodForConesGated_cols`, `exists_goodForConesGated_outer`, `exists_goodForConesMlp_outer` | `Depth/Cones.lean` | proved |
| D Lemma D.8 (the Mills ratio), for a real variable: (i) `GELU(z) = z − φ(z) z mr(z)`, `GELU'(z) = 1 − φ(z)(mr(z) − z)` for all real `z`; (ii) for `z > 0` and every `m`, `|mr(z) − ∑_{l<m} (−1)^l (2l−1)!! / z^{2l+1}| ≤ (2m−1)!! / z^{2m+1}`. The complex variable of the paper is not stated | `millsRatio`, `gelu_eq_sub_millsRatio`, `geluDeriv_eq_sub_millsRatio`, `abs_millsRatio_sub_sum_le` | `Activations/FarFromZero.lean` | proved |
| D Appendix D.5, "A gate on a ray": eq. (24) for GELU and SiLU; `δ(y) = y − σ(y)` and `δ'` for both; eq. (25) for `y ≥ 2` with `p = 2` (GELU) and `p = 1` (SiLU); `mr(y) ≤ 1/y`, `|mr(y) − 1/y| ≤ 1/y³` for `y > 0`; `3/4 ≤ y mr(y) ≤ 1`, `|mr(y) − y| ≤ 2y` for `y ≥ 2`; for SiLU `y e^{−y}/2 ≤ δ(y)`, `|δ'(y)| ≤ (2+y) e^{−y}` | `gelu_neg_eq`, `silu_neg_eq`, `gelu_gap_eq`, `silu_gap_eq`, `gelu_gap_bounds`, `silu_gap_bounds`, `silu_gap_bounds'`, `millsRatio_pos_le`, `abs_millsRatio_sub_inv_le`, `mul_millsRatio_bounds` | `Activations/FarFromZero.lean` | proved |
| D Appendix D.5, "meromorphic at infinity" (`Θ(t) = t^l Θ₀(1/t)` for large `t`, `Θ₀` real-analytic at `0`), "tends to `0` faster than every power of `1/t`", and "such a map vanishes identically if it tends to `0` faster than every power of `1/t`". The exponent `l` is a natural number (the paper: an integer), and "vanishes identically" is stated as "vanishes for all large `t`" | `MeromorphicAtInfinity`, `FasterThanPowers`, `fasterThanPowers_iff`, `FasterThanPowers.congr`, `.mono`, `.add`, `.smul_of_le_pow`, `fasterThanPowers_of_le_pow_mul_exp`, `eventually_nhds_eq_zero_of_fasterThanPowers`, `MeromorphicAtInfinity.eventually_eq_zero` | `Activations/MillsAtInfinity.lean` | proved |
| D Lemma D.9 (the Mills ratio at infinity), for real `ω > 0` and `ω' = 0`: if `Θ₁(t) mr(ω t) + Θ₂(t)` tends to `0` faster than every power of `1/t`, with `Θ₁`, `Θ₂` meromorphic at infinity, then both vanish for all large `t`. Complex `ω`, `ω'` are not stated | `eventually_eq_zero_of_millsRatio_smul_add` | `Activations/MillsAtInfinity.lean` | proved |
| D Appendix D.5, "The identity for one GELU or gated block", for a gated block: the left side `𝓛(w̃, w̃'; n)` of eq. (27), with `n W_read` and `ż = ñ W_read + n η_read` as arguments; eq. (29) in additive form (`𝓛` is affine in `w̃'`); eq. (30); eq. (28): the identity (16) before block `k` holds iff `𝓛(σ(n W_g), σ'(n W_g); n) = 0` for every `n`, in the case (n) and, for a real-analytic gate, in the case (+) | `blockLHSGated`, `blockLHSGated_add_right`, `blockLHSGated_neg`, `suffixFlat_castSucc_iff_gated`, `suffixFlat_castSucc_iff_gated_rmsNorm` | `Depth/BlockIdentityGated.lean` | proved |
| D proof of Lemma D.12, "The expansion" and "The induction" (eqs. (34) to (36), facts (a) to (c)), without the network: small terms `ζ_j(t)` between `e^{−r_j t^p}` divided and multiplied by a power of `t`, rates `r_j` independent over `ℚ`, maps `G₀`, `G_j` real-analytic at `(0, 0)` with values in a complete space; if `G₀(1/t, ζ(t)) + ∑_j ν_j(t) ζ_j(t) G_j(1/t, ζ(t))` is below `e^{−R t^p}` for every `R`, and the step "one small factor" holds for every `j` (a hypothesis), then `G₀` and every `G_j` vanish near `(0, 0)`. Also for the hidden units of several tokens | `ray_induction`, `ray_induction_matrix` | `Depth/RayInduction.lean` | proved |
| D Appendix D.5, "A gate on a ray" and "One small factor": what the proofs on rays use of a gate `σ` with the exponent `p` (real-analytic; eqs. (24), (25); `y |δ'(y)| / δ(y) → ∞`), collected in one structure, which is not a notion of the paper; SiLU has it with `p = 1`, GELU with `p = 2`. The clause `y|δ'(y)|/δ(y) → ∞` is used in the case (n) only, in the place of Lemma D.9 and of the parity | `GateFar`, `gateFar_silu`, `gateFar_gelu` | `Activations/GateFar.lean` | proved |
| D proof of Lemma D.12, "A generic ray", condition (i), for the hidden units of several tokens: if the columns `c_j` (the matrices `c_j c_j^⊤`) are independent over `ℚ`, the numbers `|ξ_t c_j|` (the numbers `(ξ_t c_j)²`) are independent over `ℚ` for a dense set of `Ξ` | `dense_setOf_linearIndependent_abs_dotProduct`, `dense_setOf_linearIndependent_sq_dotProduct` | `Depth/RayDense.lean` | proved |
| D Appendix D.5, "The frozen network": the network of gated blocks with its gates frozen on the active sets, as an architecture of its own (`𝓑°_{>k}` is its `suffix`); the weights of a gated network as its weights; the frozen block is `g°_ℓ` on every row; its maps are real-analytic; a good `θ` is regular for it (so Lemmas D.2 and D.3 hold for it); it is homogeneous, `𝓑°_{>k}(c h) = c^{2^{L−k}} 𝓑°_{>k}(h)`, with the consequences for its derivatives and for the left side of the identity for one block, written in the outputs of the hidden units (`writeLHS`; for a gated block it is `𝓛` of eq. (27)) | `Arch.frozen`, `Params.toFrozen`, `writeLHS`, `blockLHSGated_eq_writeLHS`, `frozen_block_apply`, `analyticOnNhd_f_frozen`, `regular_frozen_of_goodForConesGated`, `suffix_frozen_smul`, `fderiv_suffix_frozen_smul`, `fderiv_params_suffix_frozen_smul`, `writeLHS_frozen_smul` | `Depth/Frozen.lean` | proved |
| D Lemma D.11 (the network after `h_k` far out in its cone), for real hidden states: at `h = t (H + U)` with the rows of `H` in `C_k`, `t ≥ t₀`, `‖U‖ ≤ ϱ`, the network and the frozen network after `h_k`, their derivatives in the hidden state and their derivatives in the weights along `η` differ by at most `e^{−κ t^p}`. The paper's holomorphic extension to complex `u` is not stated; the bound for the derivative in the hidden state, which the paper gets from it by Cauchy's estimate in the proof of Lemma D.12, is a clause of the statement. Stated for every gate with `GateFar` | `exists_far_frozen_bounds` | `Depth/FrozenFar.lean` | proved |
| D Appendix D.3, after eq. (19), the converse of the claim, for gated blocks in the case (n): `cobDir θ X + rescaleDir θ α` satisfies the identity (16) for every `k`, with `Z = X k`. The case (+) and the form (17) are not stated | `suffixFlat_cobDir_add_rescaleDir` | `Depth/SuffixFlatConverse.lean` | proved |
| D proof of Lemma D.12 up to eq. (38), case (n), gated blocks: on one generic `Ξ` (rows in `C_k`; (i) the numbers `|ξ_t c_j|^p` independent over `ℚ`; (ii) no value vanishes; (iii) the derivative of the frozen network after the block is injective at `g°(Ξ)`), `ż^g(Ξ) = 0` and the second part of (38) holds for every `w̃`; then for all `n` with rows in `C_k`, if the `Ξ` with (i) are dense; then for SwiGLU and GeGLU blocks from (K3) for block `k`. The first two statements are for every gate with `GateFar`; in the last three the first part of (38) is stated as `Z W_g + η_g = 0` (Step 1 of the paper in the case (n)), and they need at least one token. "One small factor" is no hypothesis here: the proof gets it from the homogeneity of the frozen network and from `y|δ'(y)|/δ(y) → ∞`, without Lemma D.9 and without the parity (30) | `frozen_flat_at_generic_ray`, `frozen_flat_of_suffixFlat`, `frozen_flat_of_suffixFlat_swiglu`, `frozen_flat_of_suffixFlat_geglu` | `Depth/RayGatedN.lean` | proved |
| D proof of Lemma D.12, steps 1 to 3, case (n), for a real-analytic gate: if `Z`, `η` satisfy (16) for `k` and (38) holds for them with the frozen network, then `η` is of the form (19) for `k` (given `(D_{k+1})`, `θ` good for the cones and regular) | `claimGated_castSucc_of_frozen` | `Depth/StepsGatedN.lean` | proved |
| D proof of Lemma D.12, "One small factor, `α = 1_j`", without the network, in the variable `s = 1/t`: for `a`, `b` real-analytic at `0`, `u > 0` and `ν(t) = t δ'(t u)/δ(t u)`, if `a(1/t) + ν(t) b(1/t)` tends to `0` faster than every power of `1/t`, then `b` vanishes near `0`: for GELU (by Lemma D.9); for SiLU if `a` and `b` are even near `0` (for gated blocks this evenness is the parity (30); in the variable `s` it holds because the coefficient maps depend on `s` through `s²`, `scaledSuffix_neg`) | `one_small_factor_gelu`, `one_small_factor_silu` | `Activations/OneSmallFactor.lean` | proved |
| D Lemma D.10 (the rest of the network on a ray), for a real variable: the network after the normalization of `h_k` (`𝓑^♯`); the map `(s, h) ↦ 𝓑^♯(N_{ε s^{2m}}(h))`, which is `𝓑_{>k}(t^m h)` at `s = 1/t`, `t > 0`; it is real-analytic in `(θ, s, h)` at every `s`, also at `s = 0`, where no row of `h` vanishes (`ε > 0`, real-analytic blocks), and even in `s`; the derivatives of `𝓑_{>k}` in the hidden state and in the weights at `t^m h` in terms of it. Not stated: the derivatives of all orders, "meromorphic at infinity" for them, and the holomorphic extension with bounds uniform in `t` | `suffixPost`, `suffix_eq_suffixPost`, `scaledSuffix`, `suffix_pow_smul_eq_scaledSuffix`, `scaledSuffix_neg`, `analyticAt_scaledSuffix`, `fderiv_suffix_pow_smul`, `fderiv_params_suffix_pow_smul` | `Depth/ScaledSuffix.lean` | proved |
| D proof of Lemma D.12 up to eq. (38), case (+), gated blocks, for a gate with `GateFar` and with the step "one small factor" as a hypothesis: on one generic `Ξ` ((i), (ii), (iii) with the network after the block), `ż^g(Ξ) = 0` and the second part of (38) for every `w̃`; then for all `n` with rows in `C_k`, if the `Ξ` with (i) are dense and `θ` is regular; then for SwiGLU and GeGLU blocks from (K3) for block `k` | `flat_at_generic_ray_gated_rmsNorm`, `flat_of_suffixFlat_gated_rmsNorm`, `flat_of_suffixFlat_swiglu_rmsNorm`, `flat_of_suffixFlat_geglu_rmsNorm` | `Depth/RayGatedPlus.lean` | proved |
| D proof of Lemma D.12 up to eq. (38), case (+), GELU blocks (stated for an MLP block whose activation has `GateFar`, with "one small factor" as a hypothesis): on one generic `Ξ` ((i), (iii)), `ż(Ξ) = 0` and `𝐃𝓑(w̃ V)(w̃ η_V) + 𝐃_θ 𝓑(w̃ V) η = 0` for every `w̃`; then `ż(n) = 0` for all `n` with rows in `C_k`; then for GELU blocks from (K3) for block `k`. The first two statements hold for every activation with `GateFar` and "one small factor"; SiLU has both, so they also give (38) for MLP blocks with the SiLU activation under pre-RMSNorm, which is not a case of the paper | `flat_at_generic_ray_mlp_rmsNorm`, `flat_of_suffixFlat_mlp_rmsNorm`, `flat_of_suffixFlat_gelu_rmsNorm` | `Depth/RayMlpPlus.lean` | proved |
| D proof of Lemma D.12, steps 1 to 3, case (+): from (38), `Z` is antisymmetric and `η` is of the form (19) for gated blocks with a real-analytic gate, of the form (17) for MLP blocks with a real-analytic activation (given `(D_{k+1})`, `θ` good for the cones and regular) | `claimGated_castSucc_of_flat_rmsNorm`, `claimRMS_castSucc_of_flat_rmsNorm` | `Depth/StepsPlus.lean` | proved |
| **D Lemma D.12 (the step for GELU and gated blocks on rays):** at parameters good for the cones, with the independence of (K3), `(D_{k+1})` implies `(D_k)`: SwiGLU and GeGLU blocks in the cases (n) and (+), GELU blocks in the case (+). The five proofs are written from the rows above (the ray up to (38); steps 1 to 3) | `claimGated_castSucc_swiglu`, `claimGated_castSucc_swiglu_rmsNorm`, `claimGated_castSucc_geglu`, `claimGated_castSucc_geglu_rmsNorm`, `claimRMS_castSucc_gelu` | `Depth/StepGated.lean` | proved |
| D Appendix D.7 (Lemmas D.5, D.12 and D.13 together): for GELU blocks in the case (+) and for SwiGLU and GeGLU blocks in the cases (n) and (+), there is a regular parameter, with no vanishing value column for gated blocks, at which Claim `(D_0)` holds (`d_in, d_out ≥ d ≥ 2`, at least `d` hidden units per block). The proofs put together Lemma D.5 (the readout), Lemma D.12 (the step) and Lemma D.13 (good parameters) | `exists_regular_claimRMS_gelu`, `exists_regular_claimGated_swiglu`, `exists_regular_claimGated_swiglu_rmsNorm`, `exists_regular_claimGated_geglu`, `exists_regular_claimGated_geglu_rmsNorm` | `Depth/GeluGatedExplicit.lean` | proved |
| **D Theorem 5.2 (ii) for `ε > 0` and (iii):** at generic parameters `fd = P − (L+1) d(d−1)/2` for GELU blocks under pre-RMSNorm; `fd = P − (L+1) d² − ∑ d_hidden` for SwiGLU and for GeGLU blocks without normalization, and `P − (L+1) d(d−1)/2 − ∑ d_hidden` under pre-RMSNorm with `ε > 0`. Not stated: (ii) for `ε = 0` | `ae_funDim_gelu_skipless_rmsNorm`, `ae_funDim_swiglu_skipless`, `ae_funDim_swiglu_skipless_rmsNorm`, `ae_funDim_geglu_skipless`, `ae_funDim_geglu_skipless_rmsNorm` | `Depth/GeluGatedTheorem.lean` | proved |
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
  equivalence with this form are not stated. The rescalings of ReLU and ReLU² hidden units and of
  the gate of a ReGLU unit are covered in the same infinitesimal form
  (`cobDir_add_rescaleDirMlp_injective`, `cobDir_add_rescaleDir_add_rescaleDirGate_injective`);
  attention is not.
- "At generic parameters" is written `∀ᵐ θ ∂μ` for an arbitrary additive Haar measure `μ` on the
  parameter space: a Lebesgue measure of that space, without a choice of coordinates. Any two
  differ by a positive constant, so they have the same sets of measure zero. Checked by machine by
  the sixth reader: two additive Haar measures on the parameter space have the same sets of measure
  zero, and linear coordinates carry one to a positive multiple of the Lebesgue measure of `ℝ^P`.
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
  none (its hypothesis fails then), and its Lean proof uses a token. Lemma D.12 and the claims
  `(D_k)` for gated blocks are stated for the rows `T` as well, while the cones of Appendix D.5 are
  sets of single rows; that the claim for rows `T` is equivalent to the claim for one token is not a
  Lean statement.
- Theorem 5.2 (i), without normalization and under pre-RMSNorm: the proof uses `d ≥ 1` only; the paper's `d ≥ 2` is kept in
  the final statement. The same holds for Theorem 5.2 (iii) for SwiGLU blocks without normalization
  (checked by the sixth reader on a copy with `d ≥ 1`); GeGLU and GELU blocks need `d ≥ 2`.
- Theorem 4.3 is stated under the conditions that its proof uses (`E` and every write have rank
  `d`; where rescalings are counted, no read column, value column or gate column vanishes), and
  then at generic parameters. The first statements assume that the maps `f_ℓ` are differentiable;
  those marked with a prime, and those for ReLU, ReLU² and ReGLU blocks, do not. The number `s` of
  the symmetries inside the blocks is counted, without normalization and under pre-RMSNorm, for
  SwiGLU and GeGLU blocks (`s = ∑ d_hidden`), for ReLU and ReLU² blocks (`s = ∑ d_hidden`) and for
  ReGLU blocks (`s = 2 ∑ d_hidden`); for tanh and GELU blocks `s = 0`. The bounds with `s` need
  `d ≥ 1`. Not stated: attention blocks, and the paper's form for `ε = 0` (see the note on `ε = 0`).
- ReLU blocks and the functional dimension. The paper takes the Jacobian of a ReLU, ReLU² or ReGLU
  network at the inputs at which no hidden unit sits at its kink. In Lean `funDim` is the largest
  rank over all finite batches, and Mathlib's derivative is `0` where a map is not differentiable,
  so a batch with an input at which the network is not differentiable in `θ` has rank `0`: `funDim`
  is the largest rank over the batches of inputs at which the network is differentiable in `θ`.
  This set is strictly larger than the paper's: it contains the input `0`, every input for ReLU²,
  and for ReGLU the inputs at which a gate and its value both vanish. So the Lean `funDim` is not
  the paper's functional dimension by definition: it is at least the paper's value at every `θ`,
  and at parameters that are not generic it can be larger (fourth audit, 24 November 2026: a ReLU²
  block with a zero read column). An upper bound on `funDim` gives the paper's upper bound. For
  one block, two statements are made for each kind of block: the value of `funDim`, and a batch
  of the paper's inputs with that rank; together they give the paper's value at generic
  parameters, and neither alone is the paper's statement. At depth, no Lean statement defines the
  inputs with no hidden unit at its kink; an equality for ReLU-type blocks at depth would need the
  second statement of the pair again. The statements marked with a prime hold with no hypothesis
  of differentiability.
- Pre-RMSNorm with `ε = 0`. Where an upper bound is stated "for every real `ε`", the case `ε = 0`
  is a true statement about Lean's total function (`rmsRow 0 0 = 0`) with the orthogonal group. It
  is weaker than the paper's bound for `ε = 0`, which counts the group `CO(d)`, of dimension
  `d(d−1)/2 + 1` (and more for positively homogeneous blocks without skips). The paper's bounds for
  `ε = 0` are not stated.
- The Jacobian needs a norm on the parameters and on the outputs. Matrices carry the elementwise
  norm; on finite-dimensional spaces the derivative does not depend on the norm. The derivative of
  a map that is not differentiable is `0` in Mathlib; the first statements on the functional
  dimension assume that `θ ↦ F_θ(x)` is differentiable at `θ`, and those marked with a prime do not
  (see the note on ReLU blocks).
- Proposition A.3 is not stated for whole networks: it needs gains and biases, which the network
  definition does not have yet. Only the computations of its proof are stated.
- Proposition 3.3, "these changes of basis at all `L+1` hidden states remove `(L+1) dim 𝒢`
  parameters": the count has no Lean statement of its own. The entries that become fixed are those
  of an identity submatrix (`d²`), or those below the diagonal of a triangular one
  (`card_below_diagonal`), one submatrix per hidden state.
- Not stated yet from the main text: Example 4.2; Definitions 4.4 and 4.5, Proposition 4.6 and
  Corollary 5.3 (the equality condition and identifiability); Theorem 4.3 for attention blocks,
  and its form for `ε = 0`; Theorem 5.1 for attention blocks; Theorem 5.2 (i) for `ε = 0` and (ii)
  for `ε = 0`. Theorem 5.2 (ii) for `ε > 0` and (iii), without normalization and for `ε > 0`, are
  proved (`Depth/GeluGatedTheorem.lean`). No attention block is
  defined in Lean yet.

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
| S Theorem 4.2, with identity skips, without the term `s` (changes of basis only), under the condition of the proof (`E` of rank `d`): `fd ≤ P − d²` | `cobDir_const_mem_flat_residual`, `funDim_add_le_residual` | `Dimension/UpperBound.lean` | proved |
| S Theorem 4.2, with identity skips, without the term `s`, under pre-RMSNorm (`ε > 0`), under the condition of the proof (`E` of rank `d`): `fd ≤ P − d(d−1)/2` | `funDim_add_le_residual_rmsNorm` | `Dimension/UpperBoundRMSNorm.lean` | proved |
| S Theorem 4.2, with identity skips, without the term `s`, at generic parameters (only `d_in ≥ d` is used) | `ae_funDim_add_le_residual`, `ae_funDim_add_le_residual_rmsNorm` | `Generic/Params.lean` | proved |
| S Theorem 3.3 (i), "only if", without normalization: if every block is nonzero for some value of its parameters and `G_0, …, G_L` preserve the function of the residual network for all values of the parameters, then `G_0 = ⋯ = G_L`; and the equivalence (the hypothesis on the blocks is that of Theorem A.5 (iii); its `d ≥ 2` is not used) | `cob_eq_of_eval_cob_residual`, `eval_cob_residual_iff` | `Residual/OneChangeOfBasis.lean` | proved |
| S Theorem 3.3 (i), "only if", under pre-RMSNorm (`ε > 0`): the same, and the common matrix is orthogonal; and the equivalence | `cob_eq_orthogonal_of_eval_cob_residual_rmsNorm`, `eval_cob_residual_rmsNorm_iff` | `Residual/OneChangeOfBasis.lean` | proved |
| S Lemma A.4 (only orthogonal changes of basis pass), for vanilla blocks whose activation is continuous, not even and not constant, and for gated blocks whose gate is not identically zero and satisfies `σ(z) = κ σ(κ z)` for all `z` only for `κ = 1`; every block has at least one hidden unit. With fact (b), "blocks separate their inputs", for both kinds. Attention blocks are not stated | `eq_of_forall_map_dotProduct_eq`, `eq_of_forall_gate_mul_eq`, `orthogonal_of_eval_cob_skipless_rmsNorm_mlp`, `orthogonal_of_eval_cob_skipless_rmsNorm_gated` | `Symmetry/OnlyOrthogonal.lean` | proved |
| S Theorem 3.3 (ii) = A.17 (i), skipless networks under pre-RMSNorm (`ε > 0`): the changes of basis `G_0, …, G_L` preserve the function for all values of the parameters iff every `G_ℓ` is orthogonal (vanilla and gated blocks as in the row above). The dimension `(L+1) d(d−1)/2` of this group is not a Lean statement. The facts on tanh, GELU, ReLU, ReLU² ("none is even or constant") and on the ReLU, SiLU and GELU gates | `eval_cob_skipless_rmsNorm_iff_mlp`, `eval_cob_skipless_rmsNorm_iff_gated`, `tanh_not_even_not_const`, `gelu_not_even_not_const`, `relu_not_even_not_const`, `reluSq_not_even_not_const`, `relu_gate_scale`, `silu_gate_scale`, `gelu_gate_scale` | `Symmetry/OnlyOrthogonal.lean` | proved |
| S Theorem 3.2 (ii), second sentence: under pre-RMSNorm, orthogonal `Q_0 = I, Q_1, …, Q_L` make every `Q_{ℓ−1}ᵀ A_ℓ Q_ℓ` upper triangular and preserve the function (RQ factorization) | `exists_orthogonal_mul_upperTriangular`, `exists_cob_learned_upperTriangular` | `Residual/OneChangeOfBasis.lean` | proved |
| S Theorem 4.2 with identity skips, for the change of basis, for arbitrary maps `f_ℓ` (no differentiability): `fd ≤ P − d²` without normalization, `fd ≤ P − d(d−1)/2` under pre-RMSNorm (every real `ε`); only `E` of rank `d` is used | `cobDir_const_mem_flat_residual'`, `cobDir_const_mem_flat_residual_rmsNorm'`, `funDim_add_le_residual'`, `funDim_add_le_residual_rmsNorm'` | `Residual/UpperBoundSymmetries.lean` | proved |
| **S Theorem 4.2 with identity skips, with the term `s`:** `fd ≤ P − dim 𝒢 − s`, without normalization and under pre-RMSNorm, under the conditions of the proof and at generic parameters (`d_in ≥ d ≥ 1`): gated blocks with any gate (`s = ∑ d_hidden`); MLP blocks with a positively homogeneous activation, ReLU and ReLU² (`s = ∑ d_hidden`); gated blocks with a positively homogeneous gate, ReGLU (`s = 2 ∑ d_hidden`) | `funDim_add_le_residual_gated`, `funDim_add_le_residual_mlp_rescale`, `funDim_add_le_residual_gated_gate`, each also with `_rmsNorm`, and the six names with `ae_` in front | `Residual/UpperBoundSymmetries.lean` | proved |
| S Theorem 4.6 (i) / B.1 (i) for every activation that is positively homogeneous of degree `k`, differentiable away from `0` and satisfies Lemma C.3 with the rescalings: with a skip, a direction that is flat at the inputs with no hidden unit at its kink is a direction of one change of basis and of the rescalings; `fd = P − d² − d_hidden` under the conditions of the proof; the same rank on a batch of such inputs | `differentiableAt_eval_residual_of_mem_noKink`, `flatOn_noKink_le_mlp_rescale_residual`, `funDim_mlp_oneBlock_rescale_residual`, `exists_jacobianRank_mlp_oneBlock_rescale_residual` | `OneBlock/ResidualRescale.lean` | proved |
| **S Theorem 4.6 (i) for a ReLU block and for a ReLU² block:** at generic parameters (`d_in, d_out, d_hidden ≥ d ≥ 2`) the residual network has `fd = P − d² − d_hidden`, the Jacobian has this rank on a batch of inputs with no hidden unit at its kink, and the skip raises `fd` by exactly `d²` | `ae_funDim_relu_oneBlock_residual`, `ae_exists_jacobianRank_relu_oneBlock_residual`, `ae_funDim_relu_oneBlock_residual_eq_add`, and the three names with `reluSq` | `OneBlock/ResidualRescale.lean` | proved |
| **S Theorem 4.6 (i) for a ReGLU block:** with a skip, a direction that is flat at the inputs with no gate at its kink is a direction of one change of basis and of the two kinds of rescalings; under the conditions of the proof and at generic parameters (`d_in, d_out, d_hidden ≥ d ≥ 2`) the residual network has `fd = P − d² − 2d_hidden`, the Jacobian has this rank on a batch of inputs with no gate at its kink, and the skip raises `fd` by exactly `d²` | `flatOn_noKinkGate_le_reglu_residual`, `funDim_reglu_oneBlock_residual`, `exists_jacobianRank_reglu_oneBlock_residual`, `ae_funDim_reglu_oneBlock_residual`, `ae_exists_jacobianRank_reglu_oneBlock_residual`, `ae_funDim_reglu_oneBlock_residual_eq_add` | `OneBlock/ReGLU.lean` | proved |
| the rescalings of a gated network are flat for every stream matrices (no skips, identity skips, learned skips) | `rescaleDir_mem_flat_stream` | `Dimension/Rescaling.lean` | proved |
| S Theorem 4.6 (i) / B.1 (i), without normalization and biases, for every activation that satisfies Lemma C.3 with no rescaling: one residual block has `fd = P − d²` under the conditions of the proof and at generic parameters; a flat direction is that of one change of basis (Lemma B.2: `E(X − Y)D = 0` gives `X = Y`); the skip raises `fd` by exactly `d²` | `flat_le_range_cobDir_const_mlp_residual`, `funDim_mlp_oneBlock_residual`, `ae_funDim_mlp_oneBlock_residual`, `ae_funDim_mlp_oneBlock_residual_eq_add` | `OneBlock/Residual.lean` | proved |
| S Theorem 4.6 (i) / B.1 (i) for gated blocks whose gate satisfies Lemma C.3: `fd = P − d² − d_hidden`; the skip raises `fd` by exactly `d²` | `flat_le_cobDir_const_add_rescaleDir_gated_residual`, `funDim_gated_oneBlock_residual`, `ae_funDim_gated_oneBlock_residual`, `ae_funDim_gated_oneBlock_residual_eq_add` | `OneBlock/Residual.lean` | proved |
| S Theorem 4.6 (i) for a tanh, a GELU, a SwiGLU and a GeGLU block: at generic parameters `fd(residual) = fd(skipless) + d²` | `ae_funDim_tanh_oneBlock_residual_eq_add`, `ae_funDim_gelu_oneBlock_residual_eq_add`, `ae_funDim_swiglu_oneBlock_residual_eq_add`, `ae_funDim_geglu_oneBlock_residual_eq_add` | `OneBlock/Residual.lean` | proved |
| S proof of Theorem B.1 (ii), Steps 1 to 3 (the final normalization, large inputs, the skip), one residual block under pre-RMSNorm (`ε > 0`), for any continuously differentiable `f`: if `E`, `D` have rank `d` and `η` is flat, there is an antisymmetric `Y` with `η_E = E Y`, `η_D = −Y D`, and the derivative of `n ↦ f(n W_read) W_write` along `η_read + Y W_read`, `η_write − W_write Y` vanishes at every `n = N_ε(x E)` | `exists_antisymm_of_flat_residual_rmsNorm` | `OneBlock/ResidualRMSSteps.lean` | in work |
| **S Theorem 4.6 (ii), first sentence (B.1 (ii)), for a tanh and for a GELU block:** under pre-RMSNorm with `ε > 0`, at generic parameters (`d_in, d_out ≥ d ≥ 2`, a block of any width) the residual network has `fd = P − d(d−1)/2`. With the conditions of the proof as a structure (`E`, `D` of rank `d`; the hypotheses of Lemma B.3 "with `E` and `D` replaced by the identity"), and Steps 4 and 5: every flat direction is `cobDir θ (Y, Y)` with `Y` antisymmetric | `OneBlockGenericRMS`, `flat_le_cobDir_const_mlp_residual_rmsNorm`, `funDim_mlp_oneBlock_residual_rmsNorm`, `ae_oneBlockGenericRMS`, `ae_funDim_mlp_oneBlock_residual_rmsNorm`, `ae_funDim_tanh_oneBlock_residual_rmsNorm`, `ae_funDim_gelu_oneBlock_residual_rmsNorm` | `OneBlock/ResidualRMSMlp.lean` | in work: the proofs are written and rest on `exists_antisymm_of_flat_residual_rmsNorm` (`OneBlock/ResidualRMSSteps.lean`), which is in work |
| **S Theorem 4.6 (ii), first sentence (B.1 (ii)), for a SwiGLU and for a GeGLU block:** under pre-RMSNorm with `ε > 0`, at generic parameters `fd = P − d(d−1)/2 − d_hidden`; every flat direction is `cobDir θ (Y, Y)` with `Y` antisymmetric plus a rescaling of the values of the hidden units | `OneBlockGenericGatedRMS`, `flat_le_cobDir_const_add_rescaleDir_gated_residual_rmsNorm`, `funDim_gated_oneBlock_residual_rmsNorm`, `ae_oneBlockGenericGatedRMS`, `ae_funDim_gated_oneBlock_residual_rmsNorm`, `ae_funDim_swiglu_oneBlock_residual_rmsNorm`, `ae_funDim_geglu_oneBlock_residual_rmsNorm` | `OneBlock/ResidualRMSGated.lean` | in work |
| **S Theorem 4.6 (ii), the gain, for a tanh, a GELU, a SwiGLU and a GeGLU block:** with `d_hidden ≥ d`, under pre-RMSNorm with `ε > 0`, at generic parameters the skip raises `fd` by at least `d(d−1)/2`. The proofs are written; they rest on the two rows above. Not stated: Theorem 4.6 (ii) for ReLU, ReLU², ReGLU and attention blocks, and its sentence on a learned skip (B.1 (iii)) | `ae_funDim_skipless_add_le_mlp_oneBlock_residual_rmsNorm`, `ae_funDim_skipless_add_le_tanh_oneBlock_residual_rmsNorm`, `ae_funDim_skipless_add_le_gelu_oneBlock_residual_rmsNorm`, `ae_funDim_skipless_add_le_gated_oneBlock_residual_rmsNorm`, `ae_funDim_skipless_add_le_swiglu_oneBlock_residual_rmsNorm`, `ae_funDim_skipless_add_le_geglu_oneBlock_residual_rmsNorm` | `OneBlock/ResidualRMSGain.lean` | in work |
| S proof of Lemma A.27, "`J_0 = lim J_τ S_τ`" and "the rank is lower semicontinuous", without networks: for `G(τ, θ)` twice continuously differentiable, a continuous linear map `π` on the parameters (the coordinates that `S_τ` divides by `τ`) and `D_θ G(0, θ) π = 0`, the rank of `D_θ G(τ, θ)` is, for all small `τ ≠ 0`, at least the rank of `J_0 η = D_θ G(0, θ)(η − π η) + D_θ(∂_τ G(0, ·))(θ)(π η)`; and at least `dim P − dim V` if the kernel of `J_0` lies in `V` | `eventually_finrank_range_le_of_small_parameter`, `eventually_finrank_le_of_small_parameter` | `Residual/SmallParameter.lean` | proved |
| S Lemma A.27, the parameters `θ_τ` (writes `τ W_write^ℓ`), without normalization and biases: at `τ = 0` the residual network computes `x E D`; the derivative of `τ ↦ F_{θ_τ}(x)` at `0` is `∑_ℓ f_ℓ(x E W_read^ℓ) W_write^ℓ D`; the limit `(J_0 η)(x) = x(η_E D + E η_D) + ∑_ℓ (D f_ℓ(x E W_read^ℓ)(x E η_read^ℓ) W_write^ℓ + f_ℓ(x E W_read^ℓ) η_write^ℓ) D` as a definition; "The rank": if the directions that are flat for `J_0` lie in `V`, then `fd(θ_τ) ≥ P − dim V` for all small `τ ≠ 0` (any real-analytic maps `f_ℓ`) | `Params.smallWrites`, `smallWritesLimit`, `eval_smallWrites_zero`, `hasDerivAt_eval_smallWrites`, `eventually_funDim_smallWrites_ge` | `Residual/SmallWrites.lean` | proved |
| **S Lemma A.27 (Small writes), first value, for tanh and GELU blocks** (no normalization, no biases, blocks of any widths, `d_in, d_out ≥ d ≥ 2`): for generic `θ` and all small `τ ≠ 0`, `fd(θ_τ) = P − d²`. With the conditions of the proof as a structure (`E`, `D` of rank `d`; the hypotheses of Lemma B.3 for the units of all blocks together), that they hold at generic parameters, and the flat directions of `J_0`: `η_E = E X`, `η_D = −X D`, `η_read = 0`, `η_write = 0`. The other three values of the lemma (pre-RMSNorm; biases; no `E`, `D`) and attention blocks are not stated | `SmallWritesGeneric`, `smallWritesLimit_eq_zero_mlp`, `eventually_funDim_smallWrites_mlp`, `ae_smallWritesGeneric`, `ae_eventually_funDim_smallWrites_mlp`, `ae_eventually_funDim_smallWrites_tanh`, `ae_eventually_funDim_smallWrites_gelu` | `Residual/DepthMlp.lean` | proved |
| **S Theorem 4.7 (equality for residual networks at any depth), tanh and GELU blocks without normalization:** at generic parameters (`d_in, d_out ≥ d ≥ 2`, `L` blocks of any widths) `fd = P − d²`. Not stated: pre-RMSNorm, attention blocks | `ae_funDim_mlp_residual`, `ae_funDim_tanh_residual`, `ae_funDim_gelu_residual` | `Residual/DepthMlp.lean` | proved |
| **S Lemma A.27, first value, for SwiGLU and GeGLU blocks** (no normalization, no biases, any widths): for generic `θ` and all small `τ ≠ 0`, `fd(θ_τ) = P − d² − s`, `s` the number of hidden units. The flat directions of `J_0`: `η_E = E X`, `η_D = −X D`, zero at the gate columns, and one rescaling per hidden unit | `SmallWritesGenericGated`, `smallWritesLimit_eq_zero_gated`, `eventually_funDim_smallWrites_gated`, `ae_smallWritesGenericGated`, `ae_eventually_funDim_smallWrites_gated`, `ae_eventually_funDim_smallWrites_swiglu`, `ae_eventually_funDim_smallWrites_geglu` | `Residual/DepthGated.lean` | proved |
| **S Theorem 4.7, SwiGLU and GeGLU blocks without normalization:** at generic parameters `fd = P − d² − s` | `ae_funDim_gated_residual`, `ae_funDim_swiglu_residual`, `ae_funDim_geglu_residual` | `Residual/DepthGated.lean` | proved |
| **S Theorem 4.7, second sentence, and Corollary 4.8 (exact gain), without normalization:** with blocks of width at least `d`, at generic parameters the skips raise `fd` by at least `L d²` (tanh-like activations with Lemma B.3, GELU, gated blocks), and by exactly `L d²` for tanh, SwiGLU and GeGLU blocks. Not stated: Corollary 4.8 under pre-RMSNorm | `ae_funDim_skipless_add_le_residual_mlp`, `ae_funDim_skipless_add_le_residual_gelu`, `ae_funDim_skipless_add_le_residual_gated`, `ae_funDim_tanh_residual_eq_add`, `ae_funDim_swiglu_residual_eq_add`, `ae_funDim_geglu_residual_eq_add` | `Residual/ExactGain.lean` | proved |

Not stated yet from the main text of the skips paper: Theorem 3.3 (ii), the dimensions of the
groups; the term `s` of attention blocks in Theorem 4.2; Definitions 4.3, 4.4 and Proposition 4.5;
Theorem 4.6 (i) for attention blocks and with biases; Theorem 4.6 (ii) for ReLU, ReLU², ReGLU and
attention blocks and its sentence on a learned skip (its first sentence and the gain are stated for
tanh, GELU, SwiGLU and GeGLU blocks and in work);
Theorem 4.7 and Corollary 4.8 under pre-RMSNorm and for attention blocks (without normalization
they are proved for tanh, GELU, SwiGLU and GeGLU blocks); Corollaries 4.9 and 4.10;
Theorem 4.11. Lemma B.2, "a direction keeps `M` if and only if
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
| **A Theorem 4.3, under these conditions** (Appendix A.3, "The skipless network", "The residual network", "Comparison"), blocks of any kind (`f_ℓ` locally Lipschitz): for `ε > 0` the residual network differs at some input from every pre-RMSNorm skipless network with locally Lipschitz blocks, of any depth, model dimension, widths and constant `ε′ > 0`; for `ε = 0`, in the paper's sense of equality (Section 2), there is no dense set of inputs at which both networks are defined and agree (skipless blocks continuous) | `exists_ne_skipless_rmsNorm_of_turn`, `not_dense_eq_skipless_rmsNorm_zero_of_turn` | `Absorb/RMSNormRays.lean` | proved |
| A Theorem 4.3, "Measure zero": if the `f_ℓ` are continuous and for almost every choice of weights some block has a nonzero output at some normalized state, the conditions hold for almost every choice of weights (`d_in, d_out ≥ d ≥ 2`); the hypothesis holds for MLP blocks and gated blocks whose activation or gate is nonzero on the positive reals, when some block has a hidden unit | `SomeBlockNonzero`, `ae_turnGeneric`, `ae_someBlockNonzero_mlp`, `ae_someBlockNonzero_gated`, `locallyLipschitz_f_mlp`, `locallyLipschitz_f_gated` | `Absorb/RMSNormGeneric.lean` | proved |
| **A Theorem 4.3 (almost no equality under RMSNorm):** for almost every choice of weights, the residual network equals no skipless network, for `ε > 0` and for `ε = 0`: for blocks of any kind under the hypothesis above, and for residual networks of MLP blocks and of gated blocks with `σ` locally Lipschitz and nonzero on the positive reals. In the first theorem for `ε > 0` the hypothesis `0 < ε` on the residual network is not used by the proof (only `ε′ > 0` of the skipless network is). Not stated: attention blocks | `ae_ne_skipless_rmsNorm`, `ae_not_dense_eq_skipless_rmsNorm_zero`, `ae_ne_skipless_rmsNorm_mlp`, `ae_not_dense_eq_skipless_rmsNorm_zero_mlp`, `ae_ne_skipless_rmsNorm_gated`, `ae_not_dense_eq_skipless_rmsNorm_zero_gated` | `Absorb/RMSNormGeneric.lean` | proved |
| **A Theorem 4.3 for the seven kinds of MLP block** (tanh, GELU, ReLU, ReLU²; SwiGLU, GeGLU, ReGLU), `ε > 0` and `ε = 0`; the five activations are locally Lipschitz and do not vanish on the positive reals | `ae_ne_skipless_rmsNorm_tanh`, `…_gelu`, `…_relu`, `…_reluSq`, `…_swiglu`, `…_geglu`, `…_reglu`, `ae_not_dense_eq_skipless_rmsNorm_zero_tanh` (and the same six), `locallyLipschitz_tanh`, `…_gelu`, `…_silu`, `…_relu`, `…_reluSq`, `tanh_ne_zero_of_pos` (and the same four) | `Absorb/RMSNormKinds.lean` | proved |
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
- Not stated yet: Theorems 3.4, 4.2; Theorem 4.3 for attention blocks in the residual network;
  Propositions 4.6, 4.7; Remarks 5.2, 5.3; Lemmas A.5,
  A.6; Remarks A.8, A.12; Theorem A.13, Lemma A.14, Proposition A.15; Appendix C (blocks with
  biases).

