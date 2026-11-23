import SkipsLean

/-! Run with `lake env lean checks/Axioms.lean`. Every line must list only
`propext`, `Classical.choice`, `Quot.sound` (or no axioms). A `sorryAx` means an open proof. -/

-- Dimension paper
#print axioms Skips.rmsNorm_mul_orthogonal
#print axioms Skips.rmsNorm_zero_mul_smul_orthogonal
#print axioms Skips.eval_cob
#print axioms Skips.eval_cob_skipless
#print axioms Skips.eval_cob_rmsNorm
#print axioms Skips.eval_cob_rmsNorm_zero
#print axioms Skips.exists_cob_reads_eq_one
#print axioms Skips.exists_cob_writes_eq_one
#print axioms Skips.exists_orthogonal_transpose_mul_upperTriangular
#print axioms Skips.exists_cob_reads_upperTriangular
#print axioms Skips.card_below_diagonal
#print axioms Skips.vitB_count
#print axioms Skips.orthogonal_of_rmsRow_vecMul
#print axioms Skips.conformal_of_rmsRow_zero_vecMul
#print axioms Skips.centering_mul_centering
#print axioms Skips.sum_vecMul_centering
#print axioms Skips.vecMul_centering_of_sum_eq_zero
#print axioms Skips.rmsRow_vecMul_transpose_of_orthonormal
-- Skips paper
#print axioms Skips.eval_cob_residual
#print axioms Skips.eval_learned_eq_residual
#print axioms Skips.cob_skipProd_D
#print axioms Skips.eval_learned_eq_residual_rmsNorm
#print axioms Skips.eval_cob_residual_rmsNorm
#print axioms Skips.exists_cob_residual_read_eq_one
#print axioms Skips.exists_cob_residual_D_eq_one
#print axioms Skips.exists_cob_residual_read_upperTriangular
-- Functional dimension and the upper bound
#print axioms Skips.differentiable_eval
#print axioms Skips.exists_jacobianRank_eq_funDim
#print axioms Skips.funDim_add_finrank_flat
#print axioms Skips.funDim_add_finrank_le_of_le_flat
#print axioms Skips.mem_flat_of_hasDerivAt
#print axioms Skips.cobDir_injective
#print axioms Skips.funDim_add_le_skipless
#print axioms Skips.funDim_add_le_residual
#print axioms Skips.differentiable_rmsNorm
#print axioms Skips.finrank_antisymmetric
#print axioms Skips.funDim_add_le_skipless_rmsNorm
#print axioms Skips.funDim_add_le_residual_rmsNorm
-- Generic parameters and the one-block theorem
#print axioms Skips.volume_zeroSet_of_analytic_pi
#print axioms Skips.measure_zeroSet_of_analytic
#print axioms Skips.ae_isUnit_det_submatrix
#print axioms Skips.ae_rank_E_write
#print axioms Skips.ae_funDim_add_le_skipless
#print axioms Skips.ae_funDim_add_le_skipless_rmsNorm
#print axioms Skips.ae_funDim_add_le_residual
#print axioms Skips.ae_funDim_add_le_residual_rmsNorm
#print axioms Skips.tanh_units_flat_eq_zero
