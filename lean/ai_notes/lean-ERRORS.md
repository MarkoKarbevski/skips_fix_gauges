# Errors met, and how they were fixed

A shared notebook for whoever proves in this repository. Read it before you start. Add an entry
when an error cost you more than one build round and the fix could help someone else.

Rules, so that the file stays small:
- An entry has at most 4 lines: **Error**, **Cause**, **Fix**, optionally **Where**.
- Search the file first. If the error is already here, improve that entry, do not add another.
- No goal dumps, no proof scripts, no narration. One-off typos do not belong here.
- The cap is 170 lines (raised from 150 to 160 and then to 170 on 24 November). The coordinator pruned the file on 23 November 2026 (at 134) and on 24 November (at 148).

## Setup and build

- `(↑(G)⁻¹ : Matrix d d ℝ) * W` is how an element of `GL d ℝ` multiplies a matrix (the coercion
  of the inverse in `GL`, so `Units` lemmas apply); `((G)⁻¹ : GL d ℝ) * W` does not typecheck.
- Warnings to ignore: `imports Mathlib ... module system`; `automatically included section
  variable(s) unused` or `Variable name … not explicitly referenced` on a FIXED statement. On your
  own helpers, silence the first with `omit [DecidableEq d] in` before the docstring.
- `cobDirLin θ` (with `cobDirLin_apply`, `finrank_cobDomain`) is PUBLIC in `OneBlock/Common.lean`: a private copy in a file
  importing it fails with `a non-private declaration Skips.cobDirLin has already been declared`. Use the public one.
- Scratch files live in `scratch/` (ignored by git); compile with `lake env lean scratch/Foo.lean`.
  Import `SkipsLean.Imports` (the Mathlib modules the library uses, plus `Mathlib.Tactic`), never `import Mathlib`. If a lemma, instance
  or simp lemma is missing there, add its Mathlib module below YOUR file's imports, not to `Imports.lean` (that recompiles every file).
- `#print axioms` for a module that is not built (no `.olean`, no `lake build` allowed): copy the file to `scratch/`,
  append the `#print axioms` lines, and run `lake env lean` on the copy. A stale `.olean` of an import shows `sorryAx` for proofs that are done in the source: check that import from a scratch copy too. Which constant brings `sorryAx`: scan the closure with `ci.value? (allowOpaque := true)` (plain `value?` is `none` for theorems).

## Mathlib names at v4.36.0

- Deprecated here: `if_pos`/`if_neg` (use `ite_eq_left h`/`ite_eq_right h`), `dif_pos`/`dif_neg`
  (`dite_eq_left`/`dite_eq_right`), `if_true` (`ite_true`), `Set.mem_setOf_eq` (`Set.mem_ofPred_eq`),
  `push_neg` (`push Not`), `div_left_inj'` (`div_left_inj₀`), `tendsto_finset_sum` (`tendsto_finsetSum`),
  `Set.setOf_forall` (`Set.ofPred_forall`), `ContinuousLinearMap.zero_apply` (`_root_.zero_apply`),
  `Submodule.closed_of_finiteDimensional` (`isClosed_of_finiteDimensional`), `ContinuousLinearMap.smul_apply` (`_root_.smul_apply`),
  `Fin.coe_castSucc` (`Fin.val_castSucc`); renamed `continuous_finset_sum` → `continuous_finsetSum`.
- Renamed here: `Polynomial.eval_finset_sum` → `eval_finsetSum`, `Polynomial.finset_sum_coeff` → `finsetSum_coeff`,
  `coe_nnnorm` → `coe_nnNorm`, `enorm_eq_nnnorm` → `eNorm_eq_nnNorm`; `EMetric.ball` → `Metric.eball`
  (`mem_eball_zero_iff : a ∈ eball 0 r ↔ ‖a‖ₑ < r`, `Metric.eball_mem_nhds`); `Summable f` has a `SummationFilter`.
- Under `open Matrix` some names are ambiguous or resolve to `Pi`: write `_root_.mul_inv_rev`, `Matrix.neg_apply`.
- Orthogonal matrices: `(Matrix.mem_orthogonalGroup_iff d ℝ).mp hQ : Q * Qᵀ = 1` and `mem_orthogonalGroup_iff'` for `Qᵀ * Q = 1` (`n` and `R` are explicit).
  `Matrix.UnitaryGroup.toGL` lands in the linear-map group, not in `GL d ℝ`: here an orthogonal change of basis is a `Q : GL d ℝ` with `(Q : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ`.
- Submatrices: `(M * N).submatrix id c = M * N.submatrix id c` from `Matrix.submatrix_mul` with `id` bijective. Entries of `1`: `Matrix.one_apply_eq`/`one_apply_ne`.
- Rank to inverses (both need `DecidableEq`): `Matrix.vecMul_surjective_iff_rank_eq_card` then
  `Matrix.vecMul_surjective_iff_exists_left_inverse` (rank = number of columns, `B * M = 1`);
  `Matrix.mulVec_surjective_iff_rank_eq_card` then `Matrix.mulVec_surjective_iff_exists_right_inverse`
  (rank = number of rows, `M * R = 1`). Rank from an invertible square submatrix:
  `rank_le_card_width`, `rank_of_isUnit`, `rank_submatrix_le`.
- Dimensions: `Module.finrank_pi_fintype ℝ`, `Module.finrank_matrix`, `LinearMap.finrank_range_of_inj`,
  `Submodule.eq_of_le_of_finrank_le`.
- Finite union of proper subspaces is not everything: `Subspace.exists_eq_top_of_iUnion_eq_univ`.
- Limits: the rpow–exp limit `tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero` is in the root namespace.
  Also: `Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero n` (`x^n e^{-x}`), `tendsto_atTop_add_const_right`,
  `squeeze_zero_norm'`, `tendsto_of_tendsto_of_tendsto_of_le_of_le'`. The field `Finset.sum_div` lives in
  `Mathlib.Algebra.BigOperators.Field` (`Unknown constant` with short scratch imports). `le_of_tendsto` (`f → a`, eventually `f ≤ b` gives `a ≤ b`), `ge_of_tendsto` is the other way.
- Measure: `ae_all_iff` (countable index), `ae_iff`, `Measure.measure_prod_null_of_ae_null`,
  `ae_restrict_le_codiscreteWithin`, `Measure.absolutelyContinuous_isAddHaarMeasure`, `Measure.addHaar_submodule`, `ae_comp_linearMap_mem_iff` (onto linear map, `Haar.Disintegration`); null preimage under a C¹ submersion: `Skips.measure_inter_preimage_eq_zero_of_surjective_fderiv`;
  Fubini on `Params` = rest × writes: private `measure_null_of_slices`, `paramsSplit` in `Absorb/RMSNormGeneric.lean`;
  `continuousOn_univ.mp hf.continuousOn` for an `AnalyticOnNhd … univ`.
- `Pi.single` on a dependent family: `Pi.single (M := fun ℓ => …) ℓ N` (the argument is `M`). Also
  for `Pi.single_eq_of_ne (M := …) hj V` and in `show`: else `Application type mismatch … ?m k` (also `c * Pi.single j (1 : ℝ) i` in a statement: `Type mismatch … ?m i`). whnf timeout at `lem θ (Pi.single ℓ.castSucc X)`: state `lem` for any family `m`, then `refine lem θ _ …` takes it from the goal (`Dimension/UpperBoundHomogeneousRMSNormZero.lean`). A matrix
  with one nonzero row `ξ`: `Pi.single (M := fun _ : T => d → ℝ) t₀ ξ`; `Matrix.of (Pi.single t₀ ξ)` does not unify. As a write, `F * Pi.single j r` blocks `Matrix.mul_apply`: use `Matrix.of fun j' i => if j' = j then r i else 0`. A field `Function.update (fun _ => 0) m M` of a structure `def`, at `ℓ ≠ m`: `exact Function.update_of_ne h _ _` fails (`?f ℓ =?= 0`), use `simp only [myDef]; rw [Function.update_of_ne h]` (`Depth/InactiveUnit.lean`).

## Derivatives, norms, analyticity

- In this pin `HasDerivAt` and `fderiv` need only a topology and a module structure, no norm. A
  derivative proved under another norm with the same topology transfers by `exact`.
- Not in Mathlib here, proved in this repository (copy the idea if the lemma is private):
  the derivative of `Real.tanh` (`hasDerivAt_tanh` in `OneBlock/Tanh.lean`, from sinh and cosh);
  `Differentiable.matrix_mul` (`differentiable_matMul` in `Dimension/Functional.lean`: `LinearMap.mk₂`, `toContinuousLinearMap` twice,
  `Differentiable.clm_apply`; with the value `f' v * g + f * g' v`: `hasFDerivAt_mul_SW` in `Residual/SmallWrites.lean`, by `B.hasFDerivAt_of_bilinear`;
  writing `B.precompR` yourself fails: `IsNormableSpace ℝ (Matrix …)`); the null zero set of an analytic function (`Skips.measure_zeroSet_of_analytic`, public).
- Matrix inverse `X ↦ X⁻¹` differentiable: a `letI` of `Matrix.linftyOpNormedRing` beside the scoped elementwise norm fails (`HasSummableGeomSeries`). **Fix** prove it for a generic complete normed algebra (`DifferentiableAt.inverse`, `⁻¹ʳ`), rewrite by `Matrix.nonsing_inv_eq_ringInverse`, apply it with `@` to `linftyOpNormedRing`, `linftyOpNormedAlgebra`, `(inferInstance : CompleteSpace (d → d → ℝ))`.
  Also: `rw`/`erw [Module.finrank_matrix]` after `Real.dimH_of_mem_nhds` finds no pattern (module of the elementwise `NormedSpace`): `exact congrArg Nat.cast hfin`; `edist_pi_const` on matrices: `WeakPseudoEMetricSpace` not found, use `edist_le_pi_edist`. **Where:** `Generic/GroupDimension.lean`.
- Matrix exponential: `NormedSpace.exp` (no field argument), `Matrix.exp_add_of_commute`,
  `Matrix.exp_transpose`. For its derivative use, inside the proof only,
  `open scoped Matrix.Norms.Operator in hasDerivAt_exp_smul_const (𝕂 := ℝ) X 0`, with
  `set_option backward.isDefEq.respectTransparency false in` if an instance is not found; state the
  result entrywise (`Matrix.entryLinearMap`). **Where:** `expGL` in `Dimension/UpperBound*.lean`.
- Matrix-valued derivatives: `hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 (h i)` in term mode (`rw`
  finds no pattern); `HasDerivAt.prodMk` (not `.prod`); `h.hasFDerivAt` is `toSpanSingleton ℝ f'` here (`toSpanSingleton_apply_one`).
- `HasDerivAt` into `Params`: prove it for `e ∘ γ` (`e := Params.linearEquivProd.toContinuousLinearEquiv`) componentwise, then
  `exact e.symm.hasFDerivAt.comp_hasDerivAt 0 key`; `simp` lemmas about `ContinuousLinearEquiv` do not fire (two `AddCommGroup` instances on `Params`,
  only defeq). Also: a generic helper with `hline : ∀ s, G (θ + s • η) = …` leaves the normed `+`/`•` on `Params`; `show` of the `Params` form (η an anonymous
  constructor) hit a whnf timeout. **Fix** pass the curve `γ := fun s => θ + s • η` (`η` from `obtain` with its component facts). **Where:** `Depth/HiddenZero.lean`.
- Linear maps on `Params` (projections, entries) are continuous by `LinearMap.toContinuousLinearMap`;
  then `.differentiable` or `ContinuousLinearMap.analyticOnNhd`. Polynomials in `θ` are analytic by
  `Finset.analyticOnNhd_fun_sum`, `Finset.analyticOnNhd_fun_prod`, `AnalyticOnNhd.mul/.sub`.
  When such a lemma is applied to your own linear maps, name their implicit arguments
  (`linE (T := T) ..`, and inside `(A := Arch.mlp (T := T) (d := d) σ id hid)`), or they stay metavariables.
- **Error** `Application type mismatch` (`instTopologicalSpaceMatrix` vs `PseudoMetricSpace.toUniformSpace…`) on `(LinearMap.toContinuousLinearMap l).analyticOnNhd`,
  or `rw` finds no displayed `𝓝 x`/`fderiv` (from `fderiv_comp`), or `convert h using 1` on a matrix `HasDerivAt` leaves `instTopologicalSpaceMatrix = …`. **Cause** two
  defeq topologies on `Matrix`; an index left as a metavariable picks the wrong one. **Fix** name the index (`mulRightCLM (m := T) M`); rewrite in the hypothesis
  from the normed lemma, stated in a typed `have` (`h1 : fderiv … v = … := DFunLike.congr_fun hc v`), then `exact`/`e.trans hw`; or skip `rw`: `exact
  (hs.map_nhds_eq_of_equiv).ge Filter.range_mem_map`. **Where:** `Depth/Suffix.lean`, `Depth/StepsGatedN.lean`, `Residual/SmallWrites.lean`, `Depth/SuffixZeroDeriv.lean`. Same with `instTopologicalSpaceProd` in a stated `A × B →L[ℝ] M`: `rw [hv]` (`hv` from a lemma over a normed `E`) finds no `D ?v`, `zero_apply` asks `IsZeroApply`; **Fix** `(hv v).trans ?_`, `erw`, `show` (`Dimension/ExpOrbitGated.lean`).
- **Error** `Type mismatch Differentiable.comp … (?g ∘ ?f)` (or `HasFDerivAt.comp`) against a goal `fun x => …`; with `relu`
  (a `def`) it sets `?g := Real.ofCauchy`; `ContDiff.comp` against `Function.uncurry f` gives a whnf timeout (`Depth/FrozenFar.lean`), and so does the one term `continuous_finsetSum _ fun ℓ _ => (h1.matrix_mul …).add …` (state each summand, then the sum, in a typed `have`). **Cause** the goal is unified with `?g ∘ ?f` before the arguments are elaborated.
  **Fix** `have hc := hg.comp x hf; exact hc`; give the inner map's type (`have h1 : Differentiable ℝ (fun θ' => (θ', h)) := …`)
  so `Prod` instances are the normed ones (also for a heartbeat timeout of `exact h.comp_of_eq h' rfl`). **Where:** `OneBlock/ReGLU.lean`.
- **Error** `convert h using 1`, `rw [e] at h`, `rw [ContinuousLinearMap.id_comp]` or `simp only [comp_apply, map_smul] at e` fail on the CLM
  of `HasDerivAt.comp_hasFDerivAt` or `HasFDerivAt.comp` (`c • proj i ∘L proj t`, `F ∘SL (c • id)`). **Cause** its instances on `ℝ` come by another
  path. **Fix** `h.congr_fderiv (ContinuousLinearMap.ext fun M => ?_)` (a `HasDerivAt`: `h.congr_deriv e`, also `(ContinuousLinearMap.map_zero _)`), then `show` the value; or state the value in a `have` and prove it by
  defeq (`(map_smul F c v).symm.trans (DFunLike.congr_fun (h1.unique h2) v)`). **Where:** `Depth/Tanh.lean`, `Depth/Frozen.lean`.
- **Error** `Application type mismatch` (`ContinuousLinearMap.topologicalSpace` vs `PseudoMetricSpace.toUniformSpace…`) on
  `R.analyticOnNhd` for `R := (ContinuousLinearMap.compL ℝ C X F).flip N`. **Cause** `flip`/a stated `→L` type picks the strong
  topology, not the norm's. **Fix** restrict with linear maps instead: `LinearMap.lcomp ℝ F N ∘ₗ ContinuousLinearMap.coeLM ℝ`, then
  `LinearMap.toContinuousLinearMap (…).analyticOnNhd`. **Where:** `ae_injective_comp_of_analytic` in `Dimension/GenericRank.lean`.
- **Error** whnf timeout at `exact analyticAt_const.div h2 h3` against a goal `AnalyticAt ℂ (fun y => c / g y) 0`. **Cause** `AnalyticAt.div` concludes
  about the Pi quotient `f / g`. **Fix** the `fun_` versions `AnalyticAt.fun_div`, `fun_mul`, `fun_add`, `fun_pow`, `fun_neg`. **Where:** `Activations/MillsAtInfinityC.lean`.
- A primitive of a real-analytic function (e.g. `∫₀^z φ`): no real lemma here; go through ℂ: `Differentiable.isExactOn_univ`
  (`Complex/HasPrimitives`), `Differentiable.analyticAt` + `.restrictScalars`, `HasDerivAt.real_of_complex`. **Where:** `Activations/Analytic.lean`.
- **Error** `failed to synthesize ContinuousAdd (T → d → ℝ)` from `(continuous_apply t).comp (continuous_finsetSum …)` on a
  matrix-valued sum. **Fix** first `have h : Continuous fun θ => (∑ … : Matrix T d ℝ) := continuous_finsetSum …`, then `.comp h`.
- **Error** `Application type mismatch … expected ContinuousAt (HMul.hMul X₀) θ.E` (or `(Prod.mk (f x)) (g x)`, `AnalyticAt ℂ (F x i) j`) in `hg.comp hf`.
  **Cause** `hg : ContinuousAt g (X₀ * E)` is elaborated first and `?f ?x =?= X₀ * E` picks `?f := HMul.hMul X₀`. **Fix** name `f`:
  `ContinuousAt.comp (f := fun X => X * θ.E) (x := X₀) hg hf`; as an argument of another lemma, a typed `have` first. **Where:** `Absorb/RMSNormRays.lean`, `Depth/ComplexSuffix.lean`.
- **Error** whnf timeout when `hG : DifferentiableAt ℂ G (c x)` is an argument of a lemma whose `c` is a CLM `def` into a product (`CWeights`); `rw [c_apply]` then finds no pattern. **Fix** pass `?_`, close it after with `exact hG`; take the point as `(y) (hy : c x = y)`, proved by an `rfl` lemma `c_apply`. **Where:** `Depth/ComplexBlockIdentity.lean`. Also a whnf timeout reported at the declaration for `attnFamily_rigid … (fun p τ => …) … (fun p => lemma θ η p.1 p.2) …` (curves as lambdas, derivatives inline): state `hB`, `hC`, `hv` as typed `have`s and pass `_` for the curves (`Residual/DepthAttention.lean`).
- Baire: `BaireSpace (Matrix T d ℝ)` is not found; `have : BaireSpace (Matrix T d ℝ) := inferInstanceAs (BaireSpace (T → d → ℝ))`,
  then `dense_iInter_of_isOpen`. Open map: `ContinuousLinearMap.isOpenMap` (onto), then `Dense.preimage`.
- **Error** timeout when `ray_induction_matrix` is called with its types implicit: pass `(T := T) (q := hid k) (F := Matrix T dOut ℝ)`; a matrix `Tendsto` from `continuous_const.sub (continuous_const.smul …)` loops: prove it for a normed space by `fun_prop`. whnf timeout at `hasFDerivAt_apply k x` on `d → ℝ`; `Function.Injective (∑ j, L j)` (CLMs `L j`) elaborates as a sum of functions.
  **Fix** `hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : d => ℝ) k x`; ascribe `(∑ j, L j : E →L[ℝ] F)`. **Where:** `Depth/Cones.lean`.
- **Error** `failed to synthesize NormedAddCommGroup (Matrix … →L[ℝ] Matrix …)` in `have h : AnalyticOnNhd ℝ (fun w => fderiv ℝ f
  (…)) univ`. **Cause** the stated `fderiv` is elaborated with `instTopologicalSpaceMatrix`; its CLM space has no norm. **Fix**
  `have h := hB.fderiv.comp …` with no type; later `exact` accepts it for the other `fderiv`. Also: `rw [lemma]` about a normed
  `fderiv` finds no pattern in a goal from a `def` (`SuffixFlat`): close by `calc _ = _ := lemma …`. **Where:** `Depth/StepTanh.lean`.
- **Error** `failed to synthesize BorelSpace (Matrix p m ℝ × Matrix m q ℝ)` (or `BorelSpace (Fin 1 → Matrix d d ℝ)`), then `μ.IsAddHaarMeasure`, in `ae_ne_zero_of_analytic μ`, `ae_funDimSkips_ge`; `LocallyCompactSpace (Params … × (Fin 1 → Matrix d d ℝ))` for `Measure.addHaar`.
  **Cause** Matrix's Borel instance is for `instTopologicalSpaceMatrix`, the analytic side uses the norm's topology. **Fix** `inferInstanceAs (BorelSpace (Fin 1 → d → d → ℝ))` (same for `LocallyCompactSpace`,
  `SecondCountableTopology`), `Prod.borelSpace`; then pass Borel and Haar instances as EXPLICIT arguments of a private wrapper `(hB : BorelSpace V) (hμ : μ.IsAddHaarMeasure)` around the lemma
  (no `@` with positional instances). **Where:** `Absorb/SameWidth.lean`, `OneBlock/LearnedSkipKinds.lean`, `OneBlock/LearnedSkipTriangular.lean` (`ae_funDimSkips_ge_lst`).

## Tactics

- **Error** `convert h using 1` leaves `myFun = fun x => …`, or a Pi form `(fun x => x) * gaussCdf`, `-f`, `f - g`, `f ^ n` from `HasDerivAt.mul/.neg/.sub/.pow`.
  **Cause** `convert` does not unfold a `def`; those lemmas state the Pi form. **Fix** `unfold myFun` or `show HasDerivAt (fun y => …) _ z` first; use `.fun_mul/.fun_neg/.fun_sub/.fun_pow`.
  Also: `simpa` on a `Tendsto` from `tendsto_pow_atTop two_ne_zero` (type implicit) timed out: `(α := ℝ)`, `rw [mul_zero] at h`. **Where:** `Activations/Gaussian.lean`, `MillsC.lean`.
- A row `M t` of a matrix is not reached by entry lemmas (`of_apply`, `smul_apply`): state a `rfl`
  helper for the row, and use `Matrix.mul_apply_eq_vecMul` for `(A * B) i = A i ᵥ* B`. `rw [Finset.smul_sum]`, `rw [← Matrix.sum_vecMul]` on `∑ s, h s` (`h : Matrix`) fail (`function expected h s`): `exact (Finset.smul_sum (f := fun s => h s)).symm`.
- Long `rw` chains with `Matrix.sub_mul`, `mul_assoc`, `mul_comm` on scalars or matrices break on
  term order: prefer one `simp only [...]` with the full list, then `rw` on what is left; for
  `(c * s)⁻¹ • c • w` use `rw [mul_inv, smul_smul]; congr 1`.
- A constant family needs its binder type: `fun _ : Fin (L + 1) => G₀`. `field_simp` on `(f / g) t`: `rw [Pi.div_apply]` first.
- An implicit argument fixed only through a `(by linarith)`, `(by rw …)` or `rfl` argument can be assigned wrongly (`|?u|` unifies with `|0|`; `rfl : ?θ'.E = θ.E`
  sets `θ' := θ`; `congrArg Params.E h` against `a.E = a'.E` wants `h : a = a'`): pass it, `lemma (μ := 2 * u j) (by linarith)`; `have h1 := congrArg Params.E h; exact h1`.
- `Arch.mlp`, `Arch.gated`, `Arch.sum` are `abbrev`s, so `(Arch.mlp ..).r 0` reduces to `hid 0`; if `rw`/`simp` finds no pattern across the
  two forms, `show` the unfolded type, or `exact Matrix.mul_assoc _ _ _` for `rw`. `simp only [f_sum_mul]` does nothing (simp first unfolds
  `(A.sum B).f ℓ M`): `rw [f_sum_mul]` in a `have` per block, then `rw [Finset.sum_congr rfl …]` (`Residual/DepthTransformerGated.lean`).
- **Error** `Type mismatch` of `differentiable_pi.1 …` on `Matrix T n ℝ`, with `instTopologicalSpaceMatrix`
  in the expected type. **Cause** `[Fintype T]` removed by `omit`: `Differentiable` needs only a topology,
  but `differentiable_pi` needs the elementwise norm. **Fix** keep `Fintype` of both index types.
- **Error** `cannot omit referenced section variable inst✝⁴` (counts from the LAST instance variable). **Cause** `omit` of an
  instance that the statement needs, e.g. `[Fintype d]` for a lemma about a private def containing `E * W` or about `Arch.gated σ (rmsNorm ε) hid`, `[Fintype T]` for any `Params (Arch.attention …)` (its block sums over tokens), `[∀ ℓ, DecidableEq (dh ℓ)]` for `GL (dh ℓ) ℝ`, or `[DecidableEq d]`
  for one that mentions `eval A 1` (the stream `1 : Matrix d d ℝ`). **Fix** omit only what the statement does not mention.
- **Error** `rw [smul_dotProduct]` rewrites inside the body of `x₁` from `set x₁ := r • c with h`. **Cause** a `set`/`let` variable is unfolded
  by `rw`'s matching. **Fix** make it opaque: `obtain ⟨x₁, h1⟩ : ∃ x₁, P x₁ := ⟨r • c, by …⟩`, or state its facts and `clear_value x₁` (a `let`
  sign `s j := ((σ j : ℚ) : ℝ)` otherwise shows as a Cauchy structure). Also: `rw` finds no pattern in a beta-redex `(fun x => …) (x + t • v)`: `dsimp only`
  first; in the goal `f₁ s = f₂ s` of `Tendsto.congr'` (`Failed to rewrite using equation theorems`): `show` both sides. **Where:** `OneBlock/UnitsReLU.lean`, `ResidualRMSSteps.lean`.
- `field_simp` leaves `s * s⁻¹` from `(ω * s⁻¹)^n` or from a `1/t` inside a function argument, even with `s ≠ 0` in context. **Fix**
  `rw [mul_pow, inv_pow, ← div_eq_mul_inv, div_div_eq_mul_div]; ring`, or `linear_combination` with `t^l * (1/t)^l = 1`, `γ * γ⁻¹ = 1`.
  It also turns `t * u` into `u * t` inside `millsRatio (t * u)`, so `≠ 0` facts stop matching: `rw [← mul_div_assoc, div_eq_iff hne]; ring`.
- **Error** `simp made no progress` / `failed to synthesize DecidableEq d` after `omit [DecidableEq d] in`. **Cause** a lemma
  you use (e.g. `suffix_last`, `finrank_antisymmetric`) auto-included every section instance in its statement. **Fix** do not omit what callees need.
- `HasFDerivAt.comp_hasDerivAt_of_eq`, `comp_hasDerivAt` and `HasDerivAt.comp_of_eq` take the point `x : 𝕜` as their FIRST
  explicit argument: `hl.comp_hasDerivAt_of_eq (0 : ℝ) hf hy`. `comp_of_eq` also gives `σ` at a point stated as `a` when the
  inner map is `a + τ b + τ² c` (`by simp only [zero_mul, add_zero]`). Timeout at `(hG _).hasDerivAt.scomp 0 hl` (point `b ⬝ᵥ (x + 0 • u)`): name the inner map, `HasDerivAt.scomp (h := fun s => …)`. **Where:** `Absorb/Networks.lean`, `OneBlock/Rescale.lean`, `Absorb/RidgeFunctions.lean`.
- **Error** `failed to synthesize HMul (Matrix T d ℝ) ℕ …` on `h * 1`, `h * 0` or `Matrix.single a k 1 * M` in a `have`/`show`.
  **Cause** a numeral without an expected type defaults to `ℕ`. **Fix** `h * (1 : Matrix d d ℝ)`, `Matrix.single a k (1 : ℝ)`.
- `y₊`, `y₋`, `X♭`, `hλ`, `hΠ`, `Π'`, `hg°` are not identifiers (`expected token`; every later declaration is then lost); `Pi.single` in a helper needs `classical` (`DecidableEq n`).
- `have := hasSum_sum_of_ne_finset_zero …` with no stated type: `stuck SummationFilter.LeAtTop`; state the `HasSum` type. Nonnegative reals: `Finset.prod_le_prod₀ h0 h1` (`prod_le_prod` is the ordered-monoid lemma). A fibre of a sigma-sum is at most the total: `Summable.le_tsum'` + `Summable.tsum_sigma'`. **Where:** `Depth/RayInduction.lean`.
- `simp only [ite_apply]` and `split_ifs` leave a vector `if` applied to a coordinate, `(if c then f else 0) o` (from unfolding `reluSqCell`), untouched: `rw [ite_apply]` works (`Absorb/ReluSqBiasesCount.lean`).
- `simp [Matrix.of_zero]` leaves `of fun t j => 0`: add a private `rfl` lemma `(of fun (_ : m) (_ : n) => (0 : ℝ)) = 0` to the simp set.
- A local `have hid : …` shadows the section variable `hid : Fin L → Type` (`Application type mismatch: hid ↑↑k …` far below): never name a local `hid`.
- `Finset.sum_mul` does not fire on a non-square matrix product: `Matrix.sum_mul`; `(Ξ * W) t c` against `Ξ t ⬝ᵥ Wᵀ c`: state the equation by `rfl`, `simp only` it. `x ∈ s.val` (from `Multiset.le_iff_subset`): `Finset.mem_def.2 hx`; `Finset.mem_val` is an `Eq` (no `.1`).
