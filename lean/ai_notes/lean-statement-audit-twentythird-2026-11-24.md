STATUS: complete

# Twenty-third audit of Lean statements against the papers: S Theorem B.1 (iii) for `ε = 0` (24 November 2026)

An independent reader compared the statements of five files of the library `SkipsLean` with the
skips paper (`<scratchpad>/skips.txt`: Theorem B.1 at lines 2319 to 2347, the proof of part (iii)
from line 2801, "The case `ε = 0`" at lines 2862 to 2889). The reader did not write these
statements; the writer is called "the coordinator" below. The statements were audited, not the
proofs.

## Commits and files

- Branch `lean-plus` of `/home/claude/lp`. I started at commit `f4a1ef2` (22:43 UTC). The branch
  moved while I worked; I looked again at `2542854` (23:06) and at `320c6cc` (23:15).
- `OneBlock/LearnedSkipRMSZeroBoundKinds.lean`, `OneBlock/LearnedSkipRMSZeroRescaleBound.lean`,
  `OneBlock/LearnedSkipTriangularRMSZeroBound.lean`: read at `f4a1ef2`; the three files are
  byte for byte the same at `320c6cc`. No `sorry`.
- `OneBlock/UnitsRescaleSphere.lean` and `OneBlock/LearnedSkipRMSZeroSteps.lean`: read at
  `f4a1ef2`, where their three theorems were `sorry` (two in the first file, one in the second).
  Their proofs came in at `168722e` and `92b0a1b`. At `2542854` and at `320c6cc` the header, the
  definition and the three statements are the same text as at `f4a1ef2` (compared by a script),
  and the files have no `sorry`.
- The 26 public theorems of the five files depend on `propext`, `Classical.choice`, `Quot.sound`
  only (compiled, `Chk3.lean`, against the build in `/home/claude/lp/lean`, whose object files of
  the two late files are from 22:49 and 22:53, after their proofs).
- My files are in `/home/claude/audit23/`: `Chk1.lean`, `Chk2.lean`, `Chk3.lean` (compiled with
  `lake env lean`, nothing written in the repository), `c23.py` (my own core: ball arithmetic of
  `python-flint` at 60 digits, exact derivatives by forward mode, rank by elimination with
  complete pivoting where a pivot is taken only if its ball does not contain `0`), `z23tri.py`,
  `z23tri2.py`, `z23units.py`, `z23steps.py`, `z23hyp.py` and their outputs.

## Short answer

**Nothing false, nothing vacuous and nothing drifted was found in the five files.**

- The 19 `ae_` statements are at almost every pair (weights, skip) for every Haar measure on the
  product; 13 of them, one for each kind of block in each of the three proved files, were
  compiled at `Measure.addHaar` in small sizes.
- The "at most" of Theorem B.1 (iii) for `ε = 0` is stated as the paper has it: for a full
  learned skip with tanh, GELU, SwiGLU, GeGLU, attention, ReLU, ReLU², ReGLU blocks, and for an
  upper triangular learned skip with the five analytic kinds. Lean asks no width (one hidden unit
  or one head suffices) and, for attention, neither `d_h ≤ d` nor two tokens.
- For ReLU, ReLU² and ReGLU the statements use Lean's functional dimensions on all inputs. That
  they give the paper's sentence on the paper's inputs was compiled (`Chk2.lean`).
- `UnitsRescaleSphere` is true in 90 exact systems (the solutions have dimension `q + 1`), and
  each of its hypotheses that can be dropped separately is needed (a counterexample for each).
- The statement of Steps 1 to 3 holds in all 96 computed cases (tanh, GELU, ReLU, ReLU²;
  `d = 2, 3`): every direction that is flat on the batch has the stated form with one `X`, `Y`,
  `c`, and the last clause holds at every input of the batch with independent rows.
- The ranks: in 448 cases, `d = 2, 3`, seven kinds of block, full and upper triangular skip, no
  rank was above a bound, and the difference to the residual network was `d(d+1)/2 − 1` in every
  one, also for tanh, GELU, SwiGLU and GeGLU, for which the paper claims "at most" only.

---------------------------------------------------------------------------------------------------

## Part 1: the checks

### Check 1. Generic means almost every parameter, for every Haar measure

**Verdict: yes, in all 19 `ae_` statements (8 in the first file, 3 in the second, 8 in the
third). "Almost every pair `(θ, A)` for every Haar measure on the product" is a fair reading of
the paper's "generic parameters" for a network with a learned skip.** (By reading; 13 instances
by compiling, `Chk1.lean`.)

- The Lean text of one statement of each form:

  ```
  theorem ae_funDimSkipsOn_learned_le_residual_add_tanh_oneBlock_rmsNorm_zero
      [Nonempty (hid 0)]
      (μ : Measure (Params (Arch.mlp (T := T) (d := d) Real.tanh (rmsNorm 0) hid) dIn dOut
        × (Fin 1 → Matrix d d ℝ)))
      [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
      (hdOut : Fintype.card d ≤ Fintype.card dOut) :
      ∀ᵐ p ∂μ, funDimSkipsOn (Arch.mlp Real.tanh (rmsNorm 0) hid)
          (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) p
          (learnedZeroDomain (Arch.mlp Real.tanh (rmsNorm 0) hid) p.1 p.2)
        ≤ funDimOn (Arch.mlp Real.tanh (rmsNorm 0) hid) 1 p.1
            (residualZeroDomain (Arch.mlp Real.tanh (rmsNorm 0) hid) p.1)
          + (Fintype.card d * (Fintype.card d + 1) / 2 - 1)

  theorem ae_funDimLearned_le_residual_add_relu_oneBlock_rmsNorm_zero [Nonempty (hid 0)]
      (μ : Measure (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut
        × (Fin 1 → Matrix d d ℝ)))
      [μ.IsAddHaarMeasure] (hd : …) (hdIn : …) (hdOut : …) :
      ∀ᵐ p ∂μ, funDimLearned (Arch.mlp relu (rmsNorm 0) hid) p
        ≤ funDim (Arch.mlp relu (rmsNorm 0) hid) 1 p.1
          + (Fintype.card d * (Fintype.card d + 1) / 2 - 1)

  theorem ae_funDimSkipsOn_tri_le_residual_add_tanh_oneBlock_rmsNorm_zero
      [Nonempty (hid 0)]
      (μ : Measure (Params (Arch.mlp (T := T) (d := d) Real.tanh (rmsNorm 0) hid) dIn dOut
        × (Fin 1 → upperTriangular d)))
      [μ.IsAddHaarMeasure] (hd : …) (hdIn : …) (hdOut : …) :
      ∀ᵐ p ∂μ, funDimSkipsOn (Arch.mlp Real.tanh (rmsNorm 0) hid) (triSkips d 1) p
          (learnedZeroDomain (Arch.mlp Real.tanh (rmsNorm 0) hid) p.1
            fun ℓ => (p.2 ℓ : Matrix d d ℝ))
        ≤ funDimOn (Arch.mlp Real.tanh (rmsNorm 0) hid) 1 p.1
            (residualZeroDomain (Arch.mlp Real.tanh (rmsNorm 0) hid) p.1)
          + (Fintype.card d * (Fintype.card d + 1) / 2 - 1)
  ```
- In every one of the 19, `μ` is any measure on the product with `[μ.IsAddHaarMeasure]`. The two
  general statements (`ae_funDimSkipsOn_learned_le_funDimOn_residual_add_rmsNorm_zero`,
  `ae_funDimSkipsOn_tri_le_funDimOn_residual_add_rmsNorm_zero`) take their condition `hgen` at
  almost every `θ` for `Measure.addHaar` on the weights; two Haar measures of a space of finite
  dimension have the same null sets (compiled, `null_iff_of_haar23`), so this is the same
  condition for every Haar measure.
- `Fintype` on every index type: `T`, `d`, `dIn`, `dOut` in the `variable` lines; `hid ℓ`, `H ℓ`,
  `dh ℓ` by `[∀ ℓ, Fintype …]`; the reads and writes of an `Arch` carry `Fintype`. The third file
  adds `[LinearOrder d]`, which orders the coordinates for "upper triangular".
- The paper. "A statement holds for generic parameters if it fails only where some nonzero
  polynomial in the parameters, or some nonzero real-analytic function of them, vanishes, a set
  of measure zero" (line 2383), and line 227: "outside a set of Lebesgue measure zero". With a
  learned skip the entries of `A` are parameters: the proof counts them ("the network has
  `d²`, respectively `d(d+1)/2`, more parameters") and says "`A` is invertible for generic
  parameters". So the generic parameters are the generic pairs `(θ, A)`, and a Haar measure on
  `Params × (Fin 1 → Matrix d d ℝ)` is Lebesgue measure on `ℝ^(P + d²)`; on
  `Params × (Fin 1 → upperTriangular d)` it is Lebesgue measure in the weights and the
  `d(d+1)/2` entries on and above the diagonal (`finrank_upperTriangular`).
- The paper compares two generic values; Lean compares, at almost every `(θ, A)`, the network
  with the skip `A` and the residual network at the same weights `θ`. A set of weights of
  measure zero is a set of pairs of measure zero, so where the two generic values exist the Lean
  form gives the paper's.
- Compiled at `Measure.addHaar` (each ends in the bound as a number, `2` for `d = 2` and `5` for
  `d = 3`): full skip: tanh (`d = d_in = d_out = 2`, three units), GELU (`d = 3`, `d_in = 4`),
  SwiGLU, GeGLU (`d = 2`), attention (two tokens, causal mask, `d = 2`, two heads of width 1),
  ReLU (`d = 2`), ReLU² (`d = 3`, `d_out = 4`), ReGLU (`d = 2`); upper triangular skip: tanh,
  GELU (`d = 3`), SwiGLU, GeGLU, attention. All thirteen depend on the three standard axioms.
- A note for a user of the statements, not a defect: to write `Measure.addHaar` on the product I
  had to give Lean three instances by hand (`LocallyCompactSpace` of `Fin 1 → Matrix d d ℝ` and
  of `upperTriangular d`, `BorelSpace` of `Fin 1 → Matrix d d ℝ`), because a type of matrices has
  no norm until one is chosen. The library does the same inside its proofs.

### Check 2. The kinds of block (first file)

**Verdict: the conditions at almost every `θ` are those of the paper's proof, and the statements
by kind ask less than the theorem, not more. The two functional dimensions are the paper's, and
the inequality is the paper's "exceeds that of the residual network with `ε = 0` by at most
`d_model (d_model + 1)/2 − 1`" for a full learned skip.** (By reading.)

- The general statement:

  ```
  theorem ae_funDimSkipsOn_learned_le_funDimOn_residual_add_rmsNorm_zero {A : Arch T d 1}
      (hA : A.χ = rmsNorm 0) (hd : 2 ≤ Fintype.card d) (hf : AnalyticOnNhd ℝ (A.f 0) Set.univ)
      (μ : Measure (Params A dIn dOut × (Fin 1 → Matrix d d ℝ))) [μ.IsAddHaarMeasure]
      (hgen : ∀ᵐ θ ∂(Measure.addHaar : Measure (Params A dIn dOut)),
        θ.E.rank = Fintype.card d ∧ θ.D.rank = Fintype.card d ∧
        ∃ w : Matrix T dIn ℝ, ∀ t, LinearIndependent ℝ
          ![(w * θ.E) t, (A.f 0 (rmsNorm 0 (w * θ.E) * θ.read 0) * θ.write 0) t]) :
      ∀ᵐ p ∂μ, funDimSkipsOn A (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) p
          (learnedZeroDomain A p.1 p.2)
        ≤ funDimOn A 1 p.1 (residualZeroDomain A p.1)
          + (Fintype.card d * (Fintype.card d + 1) / 2 - 1)
  ```
- The conditions. `E`, `D` of rank `d` and one input `w` with the rows of `w E` and `g(w)`
  independent for every token are the conditions of the value for the residual network: the
  paper's proof for `A = I` says "`μ = c` wherever `w E` [`w E A` with `A = I`] and `g(w)` are
  linearly independent", and uses the ranks of `E` and `D` in Steps 1 to 3. The condition on the
  skip, "`A` is invertible for generic parameters", is not in `hgen`: it holds at almost every
  `A` and is added inside the proof. So `hgen` is a condition on `θ` alone, as it should be.
- The kinds. Each of the seven asks: one hidden unit (`[Nonempty (hid 0)]`), or one head of
  positive width (`[Nonempty (H 0)] [Nonempty (dh 0)]`) and a mask in which every token sees
  some token (`hsees`); `d_in, d_out ≥ d ≥ 2`. The theorem's setting is "`d_model ≥ 2`, the input
  and output dimensions at least `d_model`", one block, and for attention "`H` heads of width
  `d_h ≤ d_model`, causal or not, on sequences of at least two tokens". Part (iii) asks no width.
  So: width, none in both; depth, one block in both (`Arch T d 1`); tokens, Lean any nonempty
  finite `T` (the paper: at least two for attention); the mask, Lean any with `hsees` (the causal
  mask and no mask both have it; a token that sees nothing gets the output `0`, and then no input
  has independent rows); `d_h ≤ d`, not asked in Lean. The MLP and gated statements are for any
  analytic activation, or gate, that is nonzero on the positive reals; tanh, GELU, SiLU (SwiGLU)
  and GELU as a gate (GeGLU) are named. Verdict by kind: LEAN STRONGER for attention and for the
  two statements with a general activation, SAME for the four named ones.
- The functional dimensions. `funDimSkipsOn … p (learnedZeroDomain A p.1 p.2)` is the largest
  rank of the Jacobian in the weights and the skip over the batches of inputs at which no row of
  `x E` and no row of `x E A + g(x)` is zero; `funDimOn A 1 p.1 (residualZeroDomain A p.1)` is the
  same for the residual network (stream matrix `1`) in the weights. The paper ("Notation and flat
  directions"): the functional dimension is `P − dim K(θ)`, with "every input" meaning, for
  `ε = 0`, the inputs at which no state that is normalized vanishes. These are the two sets (the
  twenty-second audit, part B, check 7, on `learnedZeroDomain`; with `A = I` it is
  `residualZeroDomain`, compiled in `Chk2.lean`). The blocks are analytic, so there are no kinks.
- "At the same weights `θ`": see check 1.

### Check 3. ReLU, ReLU², ReGLU (second file)

**Verdict: each of the three claims of the index is right, and together they give the paper's
"at most" on the paper's inputs; this was compiled. The general bound has the paper's count and
the paper's conditions; against its twin for any `ε` it changes what it must.** (By reading; the
three claims by compiling, `Chk2.lean`; ranks by computation.)

- The Lean text of the general bound and of its twin:

  ```
  theorem funDimLearned_add_le_rmsNorm_zero' {A : Arch T d 1} [Nonempty d] (hA : A.χ = rmsNorm 0)
      (p : Params A dIn dOut × (Fin 1 → Matrix d d ℝ))
      (hE : p.1.E.rank = Fintype.card d) (hR : IsUnit (p.2 0).det)
      (U : Submodule ℝ (Params A dIn dOut))
      (hU : U ≤ Submodule.span ℝ {η | InsideBlocks A p.1 η}) :
      funDimLearned A p + ((Fintype.card d * (Fintype.card d - 1) + 2) + Module.finrank ℝ U)
        ≤ Module.finrank ℝ (Params A dIn dOut) + Fintype.card d ^ 2

  theorem funDimLearned_add_le_rmsNorm' {A : Arch T d 1} (ε : ℝ) (hA : A.χ = rmsNorm ε)
      (p : …) (hE : p.1.E.rank = Fintype.card d) (hD : p.1.D.rank = Fintype.card d)
      (U : …) (hU : …) :
      funDimLearned A p + (Fintype.card d * (Fintype.card d - 1) + Module.finrank ℝ U)
        ≤ Module.finrank ℝ (Params A dIn dOut) + Fintype.card d ^ 2
  ```
- The first claim: "for the residual network Lean's value is the paper's". Supported by
  `ae_funDim_relu_oneBlock_residual_rmsNorm_zero` with
  `ae_exists_jacobianRank_relu_oneBlock_residual_rmsNorm_zero`, the same pair for `reluSq`
  (all four in `OneBlock/ResidualRMSZeroRescaleGeneric.lean`), and
  `ae_funDim_reglu_oneBlock_residual_rmsNorm_zero` with
  `ae_exists_jacobianRank_reglu_oneBlock_residual_rmsNorm_zero`
  (`OneBlock/ResidualRMSZeroReGLUGeneric.lean`): at almost every `θ`, `funDim` has the value
  `P − d(d−1)/2 − 1 − s`, and a batch of the paper's inputs (`residualZeroDomain ∩ noKinkRMS θ`,
  resp. `∩ noKinkGateRMS θ`: no normalized row vanishes, no unit or gate at its kink) has a
  Jacobian of that rank. With `jacobianRank_le_funDim` (`Dimension/Functional.lean`) the
  functional dimension on the paper's inputs equals `funDim`. Right, at almost every `θ`.
- The second claim: "for the learned skip it is at least the paper's". `funDimLearned` is the
  supremum of the ranks over all batches; the paper's is the supremum over the batches of a
  subset of the inputs; the ranks are bounded by `P + d²`. Right, at every `(θ, A)`.
- The third: so `paper's (learned) ≤ funDimLearned ≤ funDim (residual) + (d(d+1)/2 − 1)
  = paper's (residual) + (d(d+1)/2 − 1)`. Compiled for the three kinds (`relu_paper23`,
  `reluSq_paper23`, `reglu_paper23`, standard axioms only): at almost every `(θ, A)`, for every
  Haar measure, `funDimOn` of the residual network on the paper's inputs equals `funDim`, and
  for every set `U` of inputs `funDimSkipsOn … p U ≤ funDimOn … (paper's inputs) + (d(d+1)/2 − 1)`.
- The general bound against the paper. "the scalings of `h_0` and `h_1` are symmetries too […]
  For the learned skip, `η^rot` and `K_B` are flat, which gives at least `d_model (d_model − 1)
  + 2` […] dimensions besides `K_B`". Lean: `(card d * (card d - 1) + 2) + finrank U` against
  `P + d²`: two rotations (`d(d−1)/2` each) and two scalings. The scalings in the proof are
  `scaleDir θ β` (`E ↦ β_0 E`, `W_write ↦ β_1 W_write`, the read and `D` fixed) with the skip
  moving by `(β_1 − β_0) A`: the paper's `c_0` at `h_0` and `c` at `h_1` with
  `η_A = A (Y + c I) − (X_a + c_0 I) A`. In the place of `K_B` Lean has any subspace `U` of the
  span of the directions of symmetries inside the block (`InsideBlocks`: velocities of curves
  that keep `E`, `D` and the map of the block). Such directions lie in `K_B`, and they are flat
  at every input with no differentiability asked, which is why this form suits ReLU-type blocks;
  for them `U` is the space of the rescalings (`s` dimensions).
- The hypotheses. `E` of rank `d`: the paper's generic condition; it separates the rotation and
  the scaling of `h_0` (`η_E = E (X_0 + β_0 I)`). The skip invertible: the paper's ("`A` is
  invertible for generic parameters"); it separates the rotation and the scaling of `h_1` in the
  entry at the skip, `A (X_1 + β_1 I)`. `[Nonempty d]`: needed, since for an empty `d` the count
  `0 · (0 − 1) + 2 = 2` exceeds `P + d² = 0`; it is what makes `β I = 0` give `β = 0`.
- Against the twin. The twin asks `D` of rank `d` and no invertible skip: it reads the rotation
  of `h_1` off `η_D = −X_1 D`. A scaling of `h_1` does not move `D` for `ε = 0`, so the new
  statement reads `X_1` and `β_1` off the skip, and needs the skip invertible in place of the
  rank of `D`. The other changes are `ε = 0`, `+ 2`, `[Nonempty d]`. Nothing else differs.
- The three corollaries: `d_in, d_out ≥ d ≥ 2` and one hidden unit, as the value for the residual
  network; no width, as part (iii). `P + d² − (d(d−1) + 2) − s` minus `P − d(d−1)/2 − 1 − s` is
  `d(d+1)/2 − 1`.
- Computed (`z23tri2.py`, outputs `z23tri2_relu_d2.out` to `z23tri2_reglu_d3.out`): see the
  table of check 4. For ReLU, ReLU² and ReGLU with a full learned skip, in all 96 cases the rank
  with the skip is `P + d² − (d(d−1) + 2) − s`, the rank of the residual network is
  `P − d(d−1)/2 − 1 − s`, and the difference is `d(d+1)/2 − 1`: at most the bound, and equal, as
  the paper says for these blocks.

### Check 4. The upper triangular skip (third file)

**Verdict: `upperTriangular` and `triSkips` are the paper's "upper triangular"; the comparison of
the two families is at the same `(θ, A)` on the same inputs, and "`f` differentiable" is enough
for it; the count is the paper's; the different route does not change the statement. Computed:
the difference is `d(d+1)/2 − 1` in every case, so at most the bound, and equal to it.** (By
reading; four small facts by compiling, `Chk2.lean`; the ranks by computation.)

- The Lean text:

  ```
  def upperTriangular (d : Type*) [Fintype d] [LinearOrder d] : Submodule ℝ (Matrix d d ℝ) where
    carrier := {M | M.BlockTriangular id}
  noncomputable def triSkips (d : Type*) [Fintype d] [LinearOrder d] (L : ℕ) :
      (Fin L → upperTriangular d) →L[ℝ] (Fin L → Matrix d d ℝ) :=
    ContinuousLinearMap.pi fun ℓ => (upperTriangular d).subtypeL.comp (ContinuousLinearMap.proj ℓ)

  theorem funDimSkipsOn_tri_le_learned_rmsNorm_zero {A : Arch T d 1} (hA : A.χ = rmsNorm 0)
      (hf : Differentiable ℝ (A.f 0)) (θ : Params A dIn dOut) (R : Fin 1 → upperTriangular d) :
      funDimSkipsOn A (triSkips d 1) (θ, R)
          (learnedZeroDomain A θ fun ℓ => (R ℓ : Matrix d d ℝ))
        ≤ funDimSkipsOn A (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ))
            (θ, fun ℓ => (R ℓ : Matrix d d ℝ))
            (learnedZeroDomain A θ fun ℓ => (R ℓ : Matrix d d ℝ))

  theorem funDimSkipsOn_tri_add_le_learned_rmsNorm_zero {A : Arch T d 1} [Nonempty d]
      (hA : A.χ = rmsNorm 0) (hf : AnalyticOnNhd ℝ (A.f 0) Set.univ) (θ : Params A dIn dOut)
      (R : Fin 1 → upperTriangular d) (hE : θ.E.rank = Fintype.card d)
      (hR : IsUnit (R 0 : Matrix d d ℝ).det) :
      funDimSkipsOn A (triSkips d 1) (θ, R) (learnedZeroDomain A θ fun ℓ => (R ℓ : Matrix d d ℝ))
          + ((Fintype.card d * (Fintype.card d - 1) / 2 + 2)
            + Module.finrank ℝ (blockFlatSphere A θ))
        ≤ Module.finrank ℝ (Params A dIn dOut) + Fintype.card d * (Fintype.card d + 1) / 2
  ```
- "full or upper triangular" (line 2317). `M ∈ upperTriangular d` says `M i j = 0` for `j < i`
  and nothing else (compiled): the entries below the diagonal vanish, the diagonal is free.
  `triSkips d 1 R ℓ` is the matrix `R ℓ`, and the family with `triSkips` at `(θ, R)` is the
  network with the skip `R 0` (both by `rfl`, compiled). The dimension is `d(d+1)/2`.
- The comparison. Both sides are at the weights `θ` and the skip `R`, once as a point of the
  triangular family and once as a point of the full one; both are the same network there, so
  "no normalized row vanishes" is one set of inputs, `learnedZeroDomain A θ R`, on both sides.
  This is the paper's "view the network as the network with a full `A` restricted to triangular
  skips", stated for the ranks. The paper's sentence is on the flat directions ("its flat
  directions are those of the full network whose entry `η_A` is upper triangular"); the Lean
  inequality follows from it and is weaker than it.
- "`f` differentiable" is enough: at an input of `learnedZeroDomain`, `N_0` is differentiable at
  `x E` and at `h_1` (no zero row) and `f` everywhere, so the output is a differentiable function
  of the weights and the full skip, the Jacobian of the triangular family on a batch is that of
  the full family composed with the inclusion, and its rank is not larger. The statement is
  proved. Without differentiability of `f` the argument has no chain rule (Lean's derivative of
  the full family is `0` where it does not exist); the file does not claim that case, and so has
  no statement for ReLU, ReLU², ReGLU with a triangular skip (the header and the index say so).
- The count. Lean: `fd + (d(d−1)/2 + 2) + dim V_θ ≤ P + d(d+1)/2`, with `P + d(d+1)/2` the
  number of weights and entries of the triangular skip. The paper: "at least `d_model (d_model −
  1) + 2`, respectively `d_model (d_model − 1)/2 + 2`, dimensions besides `K_B`". The same.
- The route. The paper finds `d(d−1)/2 + 2` flat directions of the triangular family: the two
  scalings, and the rotations `X_a` of `h_0` with the `Y` that makes `A Y − X_a A` upper
  triangular ("for generic `A` the map from antisymmetric `Y` to the entries of `A Y` below the
  diagonal is invertible"). Lean takes `fd_tri ≤ fd_full ≤ P + d² − (d(d−1) + 2) − dim V_θ`,
  and `d² − d(d−1) = d = d(d+1)/2 − d(d−1)/2`, so the bound is the same number. The statement is
  the same inequality with the same hypotheses (`E` of rank `d`, `A` invertible); the Lean route
  does not need the paper's condition on a generic triangular `A`.
- The statements at one parameter and at almost every `(θ, A)`, `A` upper triangular, have the
  hypotheses of their twins for the full skip (check 2), with `Fin 1 → upperTriangular d` in the
  place of `Fin 1 → Matrix d d ℝ`. An invertible triangular `A` is generic among the triangular
  ones.
- **Computed** (`z23tri2.py`; `c23.py`). One block, one token, `ε = 0`, `d = 2, 3`,
  `(d_in, d_out) = (d, d)` and `(d + 1, d + 1)`, widths `1, d, d + 1, 2d + 1`, two random
  parameters at each size: 16 cases for each kind, `d` and kind of skip. The skip is a random
  matrix (upper triangular or full) of certified rank `d`; `E` and `D` have certified rank `d`.
  The rank of the Jacobian in the weights and the entries of the skip (for the triangular skip
  the `d(d+1)/2` entries on and above the diagonal), and the rank of the Jacobian of the
  residual network in the weights at the same weights; two batches each. The inputs are spread
  over the directions of `h_0 = x E` (directions uniform on the sphere, lengths `1/3` to `5`);
  for the analytic kinds `4P/d_out` inputs in a batch; for ReLU-type blocks up to `2P/d_out`
  inputs (`d = 2`) or `P/d_out` (`d = 3`) from every pattern of active units found among 20000
  directions (up to 1220 inputs and 44 patterns in a batch).

  | block | skip | `d` | cases | rank with the skip | rank of the residual network | difference | `d(d+1)/2 − 1` |
  |---|---|---|---|---|---|---|---|
  | tanh, GELU | triangular | 2 | 16 + 16 | `P + 3 − 3 = P` | `P − 2` | 2 in all | 2 |
  | tanh, GELU | triangular | 3 | 16 + 16 | `P + 6 − 5 = P + 1` | `P − 4` | 5 in all | 5 |
  | SwiGLU, GeGLU | triangular | 2 | 16 + 16 | `P − s` | `P − 2 − s` | 2 in all | 2 |
  | SwiGLU, GeGLU | triangular | 3 | 16 + 16 | `P + 1 − s` | `P − 4 − s` | 5 in all | 5 |
  | tanh, GELU, SwiGLU, GeGLU | full | 2, 3 | 128 | `P + d² − (d(d−1) + 2) − s′` | `P − d(d−1)/2 − 1 − s′` | 2, resp. 5, in all | 2, 5 |
  | ReLU, ReLU², ReGLU | triangular | 2 | 48 | `P − s` | `P − 2 − s` | 2 in all | 2 |
  | ReLU, ReLU², ReGLU | triangular | 3 | 48 | `P + 1 − s` | `P − 4 − s` | 5 in all | 5 |
  | ReLU, ReLU², ReGLU | full | 2, 3 | 96 | `P + d² − (d(d−1) + 2) − s` | `P − d(d−1)/2 − 1 − s` | 2, resp. 5, in all | 2, 5 |

  (`s` the number of rescalings: the hidden units for ReLU, ReLU², SwiGLU, GeGLU, twice that for
  ReGLU; `s′ = 0` for tanh and GELU.) In every case both batches give the same rank, the rank
  with the skip is the Lean bound with `dim V_θ = s`, and the rank of the residual network is
  the value with the same `s`. No rank is above a bound. For the analytic kinds the smallest
  pivot is `5.6·10⁻⁹` of the largest and no entry that is left is above `6.3·10⁻³⁹`; for the
  ReLU-type kinds `7.8·10⁻⁹` and `4.8·10⁻⁴³`. A rank on a batch is a certified lower bound; that
  it is not larger rests on the size of what is left.
- So, to the question of the brief: for tanh and for GELU, SwiGLU, GeGLU, `d = 2, 3`, with an
  upper triangular skip the difference is at most `d(d+1)/2 − 1`, and it is `2`, resp. `5`:
  equal to the bound. Attention was not computed.
- A warning on such computations, from my own first runs (`z23tri.py`; `z23tri_relu.out`,
  `z23tri_relu_m12.out` and the like). There the inputs had normal coordinates, so the
  directions of `x E` were not uniform, and the batches were not sorted by pattern. For the
  analytic kinds all 256 cases gave the ranks above. For the ReLU-type kinds a batch stayed below
  its count in 31 of 192 cases with `3P/d_out` inputs and in 18 of 192 with `12P/d_out` inputs,
  most of them for `d = 2`, where a pattern of active units can be a narrow arc (one was hit by 27
  of 20000 uniform directions). With inputs from every pattern all cases reach the counts. No
  batch gave a rank above a count in any run.

### Check 5. `UnitsRescaleSphere`

**Verdict: the statement is the paper's step with Lemma B.3 folded in, for any symmetric `X`;
the factor and the sign of `β_i = k (c₀ − λ_i) a_i` are right; it is true in all 90 exact systems
(the solutions have dimension `q + 1`); "one unit at least", "`a_i ≠ 0`", "`c_i ≠ 0`", "pairwise
non-collinear" and "`X` symmetric" are each needed. One coordinate: true, and then at most one
unit can satisfy the hypotheses.** (By reading and by hand; by computation, `z23units.py`,
output `z23units.out`, exact arithmetic over the rationals.)

- The Lean text:

  ```
  def UnitsRescaleSphere (σ σ' : ℝ → ℝ) (k : ℕ) (n m q : Type*) [Fintype n] [DecidableEq n]
      [Fintype m] [Fintype q] : Prop :=
    ∀ (c : q → n → ℝ) (a : q → m → ℝ) (X : Matrix n n ℝ) (ψc : q → n → ℝ) (β : q → m → ℝ),
      (∀ i, a i ≠ 0) → (∀ i, c i ≠ 0) → (∀ i j, i ≠ j → ∀ r : ℝ, c i ≠ r • c j) → Xᵀ = X →
      (∀ x : n → ℝ, (∀ i, x ⬝ᵥ c i ≠ 0) →
        (x ⬝ᵥ x) • ∑ i, (σ (x ⬝ᵥ c i) • β i + (σ' (x ⬝ᵥ c i) * (x ⬝ᵥ ψc i)) • a i)
          = ((k : ℝ) * ((x ᵥ* X) ⬝ᵥ x)) • ∑ i, σ (x ⬝ᵥ c i) • a i) →
      ∃ (c₀ : ℝ) (lam : q → ℝ), X = c₀ • (1 : Matrix n n ℝ) ∧
        ∀ i, ψc i = lam i • c i ∧ β i = ((k : ℝ) * (c₀ - lam i)) • a i

  theorem relu_unitsRescaleSphere (n m q : Type*) [Fintype n] [DecidableEq n] [Fintype m]
      [Fintype q] [Nonempty q] : UnitsRescaleSphere relu reluDeriv 1 n m q
  theorem reluSq_unitsRescaleSphere (n m q : Type*) … [Nonempty q] :
      UnitsRescaleSphere reluSq reluSqDeriv 2 n m q
  ```
- The symbols. The paper's block is `B(n) = f(n W_read) W_write = ∑_i σ(n c_i) a_i`. Lean's `x`
  is the paper's input `n` of the block; `c i` is the paper's `c_i` (here column `i` of
  `W_read`, "with `E` and `D` replaced by the identity"); `a i` is `a_i`, row `i` of `W_write`;
  `X` is the symmetric matrix of `q(n) = n X n^⊤/d_model`, the paper's `X_0` (or `X_s`); `ψc i`
  and `β i` are the entries of the direction `ψ` at column `i` of `W_read` and at row `i` of
  `W_write`; `k` is the degree, `B(λn) = λ^k B(n)`. Lean's types `n`, `m`, `q` index the
  coordinates of the input, of the output (both `d_model` in the paper) and the hidden units.
  `σ'` is the derivative of `σ` off the kink (`reluDeriv`, `reluSqDeriv`).
- Derived. Equation (17) on the sphere `‖n‖² = d_model`: `∂_ψ B(n) = q(n) DB(n) n`. Euler:
  `DB(n) n = k B(n)`. The left side has degree `k` in `n`, the right side `k + 2`; at
  `n′ = √d_model · n/‖n‖` this gives `∂_ψ B(n) = (d_model/‖n‖²) k q(n) B(n)`, that is
  `‖n‖² ∂_ψ B(n) = k d_model q(n) B(n)` for all `n ≠ 0`: the paper's line. With
  `∂_ψ B(x) = ∑_i [σ(x c_i) β_i + σ′(x c_i) (x ψc_i) a_i]` the left side is Lean's, and
  `k d_model q(x) = k (x X x^⊤)`, which is Lean's `(k : ℝ) * ((x ᵥ* X) ⬝ᵥ x)`. Yes.
- The factor and the sign. Put `X = c₀ I` and `ψc_i = λ_i c_i`. Then `σ′(z) λ_i z = k λ_i σ(z)`
  (Euler for `σ`), and the identity becomes `∑_i σ(x c_i) [β_i + k λ_i a_i − k c₀ a_i] = 0`, which
  `β_i = k (c₀ − λ_i) a_i` solves. Its two parts are known directions: the rescaling of unit `i`
  ("scales column `i` of `W_read` […] by `λ_i` and row `i` of `W_write` by `−λ_i` for ReLU, by
  `−2λ_i` for ReLU²", line 2604: `−k λ_i a_i`), and the scaling of the input by `1 + τ c₀`,
  which is the scaling of the output by `(1 + τ c₀)^k`: `+ k c₀ a_i`.
- `X = c₀ I` and the paper's `X_0`. The paper applies the step to `X_0`, the part of trace zero
  of `X_s = c_0 I + X_0`: "it divides `q(n)`, so `X_0` is a multiple of `I`, and `X_0 = 0` because
  its trace vanishes". In Lean's words: for `X = X_0`, `X = c₀ I` and trace zero give `c₀ = 0`.
  Lean allows any symmetric `X`; applied to `X = X_s` its `c₀` is the paper's `c_0`, the scaling
  of `h_0`, and the term `k c₀ a_i` is how that scaling moves the block. So the statement is the
  paper's step and a little more, LEAN STRONGER; and it contains Lemma B.3 for the direction
  that is left (`X = 0` gives `ψc_i = λ_i c_i`, `β_i = −k λ_i a_i`).
- By hand, why it is true. Across the hyperplane `x c_i = 0`, at a point of no other hyperplane
  (the columns are pairwise non-collinear), the terms of unit `i` satisfy the identity alone, as
  polynomials: `‖x‖² [(x c_i) β_i + (x ψc_i) a_i] = (x X x^⊤)(x c_i) a_i` for ReLU, and the same
  with one more factor `x c_i` and a `2` for ReLU². In a coordinate with `a_i ≠ 0`, `‖x‖²`
  divides `(x X x^⊤)(x c_i)`; for at least two coordinates `‖x‖²` has no real linear factor, so
  it divides `x X x^⊤`, and `X = c₀ I` since `X` is symmetric. What is left is linear and gives
  `ψc_i` parallel to `c_i` and `β_i`.
- **Computed, the statement.** `k = 1` (ReLU) and `k = 2` (ReLU²); 15 shapes
  `(n, m, q)`: `(1,1,1)`, `(1,2,1)`, `(2,1,1)`, `(2,2,1)`, `(2,2,2)`, `(2,1,3)`, `(2,2,5)`,
  `(2,3,7)`, `(3,1,1)`, `(3,2,2)`, `(3,3,3)`, `(3,2,6)`, `(4,3,2)`, `(4,2,7)`, `(5,2,3)`: one,
  two and more units, and more units than coordinates; three random integer weights each (the
  `c_i` nonzero and pairwise non-collinear, the `a_i` nonzero): 90 systems. Unknowns: the
  symmetric `X`, the `ψc_i`, the `β_i`; equations at six integer inputs per unknown and forty
  more, none with a unit at its kink. The kernel over the rationals has dimension `q + 1` in
  all 90; every vector of it has the stated form (checked exactly); the `q + 1` claimed solutions
  solve the equations at fresh inputs. The kernel on a batch contains the solutions of the
  hypothesis, so in these 90 cases the statement holds.
- **The hypotheses** (each example satisfies all the others; the hypothesis equation was checked
  exactly at 500 integer inputs, and it holds identically by the line given):
  - *One unit at least: needed for two or more coordinates.* No unit, `n = 2`, `X = diag(1, 0)`:
    both sides are empty sums, and `X` is not `c₀ I`. (For one coordinate every `X` is `c₀ I`.)
    The definition does not ask a unit; the two theorems do (`[Nonempty q]`).
  - *`a_i ≠ 0`: needed.* `c = ((1,2), (3,−1))`, `a = ((0,0), (1,2))`, `X = 0`, `ψc_0 = (2,−1)`,
    `ψc_1 = 0`, `β = 0`: `ψc_0` enters only through `a_0 = 0`; it is not a multiple of `c_0`.
    The solutions on a batch have dimension 4 against `q + 1 = 3`.
  - *`c_i ≠ 0`: needed, for the form of the statement.* If `c_0 = 0`, no `x` has `x c_0 ≠ 0`, the
    hypothesis holds for every `X`, `ψc`, `β`, and the conclusion fails for `X = diag(1, 0)`.
    (For two or more units it follows from the next hypothesis with `r = 0`.)
  - *Pairwise non-collinear: needed.* A positive multiple: `c_1 = 2 c_0`, `X = 0`, `ψc = 0`,
    `β_0 = 2^k b`, `β_1 = −b` with `b ≠ 0`: `σ(2z) = 2^k σ(z)`, so the two terms cancel; the
    conclusion would give `β = 0`. Dimension 5 against 3. A negative multiple: with one pair of
    opposite units (`c_1 = −c_0`), alone or with other units, the solutions still had dimension
    `q + 1` in all 48 systems tried; with two opposite pairs they need not: for ReLU,
    `c = (e_1, −e_1, e_2, −e_2)`, `a = (1, −1, 1, −1)`, so that the block is the linear map
    `x_1 + x_2`, and `ψc = (e_2, −e_2, −e_2, e_2)`, `X = 0`, `β = 0`: the derivative is
    `x_2 − x_2 = 0`, and `ψc_0 = e_2` is not a multiple of `c_0 = e_1`. For two opposite pairs
    with one output the dimension was 7 (ReLU) and 6 (ReLU²) against `q + 1 = 5`.
  - *`X` symmetric: needed.* `x X x^⊤` sees only the symmetric part: `X = ((0,1), (−1,0))`,
    `ψc = 0`, `β = 0`. Dimension 4 against 3 with `X` any matrix.
- One coordinate. Two nonzero vectors of `ℝ¹` are collinear, so the hypotheses allow one unit
  at most; with one unit the solutions have dimension `2 = q + 1` and the stated form (computed
  for both activations). There `‖x‖² = x²` does have a linear factor, and nothing is lost: every
  `1 × 1` matrix is `c₀ I`. The theorems are proved for every finite `n`.

### Check 6. Steps 1 to 3 for `ε = 0` (fifth file)

**Verdict: the statement is the paper's Steps 1 to 3 of "The case `ε = 0`" for a full learned
skip, clause by clause, with the paper's set for the last clause. It holds in all 96 computed
cases. Of the hypotheses, `d ≥ 2` follows from the one on `w`; "`D` of rank `d`" is needed in
some form (`D = 0` is a counterexample); for the others I found no counterexample and give
examples in which the first three clauses hold without them.** (By reading and by hand; by
computation, `z23steps.py`, `z23hyp.py`.)

- The Lean text:

  ```
  theorem exists_of_flatSkipsOn_learned_rmsNorm_zero_on {A : Arch T d 1}
      (hA : A.χ = rmsNorm 0) (hd : 2 ≤ Fintype.card d)
      (V : Set (Matrix T (A.r 0) ℝ)) (hV : IsOpen V)
      (hVs : ∀ M ∈ V, ∀ c : T → ℝ, (∀ t, 0 < c t) → (Matrix.of fun t i => c t * M t i) ∈ V)
      (hf : ContDiffOn ℝ 1 (A.f 0) V) (θ : Params A dIn dOut) (R : Fin 1 → Matrix d d ℝ)
      (hE : θ.E.rank = Fintype.card d) (hD : θ.D.rank = Fintype.card d) (hR : IsUnit (R 0).det)
      (hw : ∃ w : Matrix T dIn ℝ, w * θ.E * θ.read 0 ∈ V ∧ ∀ t, LinearIndependent ℝ
        ![(w * θ.E * R 0) t, (A.f 0 (rmsNorm 0 (w * θ.E) * θ.read 0) * θ.write 0) t])
      (η : Params A dIn dOut) (ρ : Fin 1 → Matrix d d ℝ)
      (hη : (η, ρ) ∈ flatSkipsOn A (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) (θ, R)
        (learnedZeroDomain A θ R ∩ {x | x * θ.E * θ.read 0 ∈ V})) :
      ∃ (X Y : Matrix d d ℝ) (c : ℝ), Yᵀ = -Y ∧ η.E = θ.E * X ∧
        ρ 0 = R 0 * (Y + c • 1) - X * R 0 ∧ η.D = -(Y * θ.D) ∧
        ∀ x : Matrix T dIn ℝ, x * θ.E * θ.read 0 ∈ V →
          (∀ t, LinearIndependent ℝ
            ![(x * θ.E * R 0) t, (A.f 0 (rmsNorm 0 (x * θ.E) * θ.read 0) * θ.write 0) t]) →
          fderiv ℝ (A.f 0) (rmsNorm 0 (x * θ.E) * θ.read 0)
              (fderiv ℝ (rmsNorm 0 : Matrix T d ℝ → Matrix T d ℝ) (x * θ.E) (x * θ.E * X)
                  * θ.read 0
                + rmsNorm 0 (x * θ.E) * η.read 0) * θ.write 0
            + A.f 0 (rmsNorm 0 (x * θ.E) * θ.read 0) * η.write 0
            = A.f 0 (rmsNorm 0 (x * θ.E) * θ.read 0) * θ.write 0 * (Y + c • 1)
  ```
- Clause by clause, with `A = R 0`, `η_A = ρ 0`.
  - `Yᵀ = −Y`, `η_D = −Y D`: Step 1 of part (ii) ("`η_D = −Y D + Z`", "`Z = 0`"), and "`Y` is again
    antisymmetric, since `N_ε(h_1) Y` must be orthogonal to `h_1`".
  - `η_E = E X` and `η_A = A (Y + c I) − X A`: the paper has `η_E A + E η_A = E A (Y + c I)`,
    and Step 3 ("Multiplying on the left by `I − E E⁺` gives `(I − E E⁺) η_E = 0`, as `A` is
    invertible, so `η_E = E X` with `X = E⁺ η_E`, and then `η_A = A Y − X A`") "with `Y + c I`
    in place of `Y`". The same.
  - The formula of `D_θ g η`. `g(x) = f(N_0(x E) W_read) W_write`; along `η`, with
    `η_E = E X`, the input `n = N_0(x E)` of the block moves by `DN_0(x E)(x E X)`, the
    pre-activation by `DN_0(x E)(x E X) W_read + n η_read`, and the output by
    `Df(n W_read)(…) W_write + f(n W_read) η_write`. This is the Lean left side, with Mathlib's
    `fderiv` for `Df` and `DN_0`; both are true derivatives at the points in question (`f` is
    continuously differentiable on the open `V`, and no row of `x E` is zero). The right side is
    `g(x) (Y + c I)`: Step 3's "`D_θ g η = g(x) Y`" with `Y + c I`.
  - The set of the last clause. Lean: the inputs with `x E W_read ∈ V` at which, for every token,
    the rows of `x E A` and `g(x)` are linearly independent. The paper: "The constant terms then
    give `μ = c` wherever `w E A` and `g(w)` are linearly independent". The same set (inside
    `V`). Such an input lies in `learnedZeroDomain` (independence makes `x E` and `h_1` nonzero),
    so the clause is claimed only where the direction is assumed flat. Where the rows are not
    independent the paper's argument gives `D_θ g η − g(x)(Y + c I)` parallel to `h_1` and no
    more; the header says this, and the statement claims nothing there.
- By hand, that the clause is right pointwise. At `t w`, `t > 0`, the block reads
  `N_0(t w E) = N_0(w E)`, so `g` and `G = D_θ g η` do not depend on `t`. Flatness at `t w` gives
  `t w(η_E A + E η_A) + G = (t w E A + g)(Y + μ_t I)`, and with
  `η_E A + E η_A = E A (Y + c I)`: `G − g Y = t (μ_t − c) w E A + μ_t g`. The left side does not
  depend on `t`; if `w E A` and `g(w)` are independent, `μ_t` is constant and `t (μ_t − c)` is
  constant, so `μ_t = c` and `G = g (Y + c I)`. This uses flatness along the whole ray, which the
  hypothesis gives: the ray stays in `learnedZeroDomain`, and `t w E W_read ∈ V` by `hVs`.
- `V` and `hVs`. The hypothesis and the last clause name `V` through `x E W_read ∈ V`, while the
  block is evaluated at `N_0(x E) W_read`, a positive multiple of it row by row. `hVs` (invariance
  under positive scalings of the rows) makes the two the same condition. For a ReLU-type block
  `V` is the set of pre-activations with no zero entry, the paper's "inputs at which no hidden
  unit sits at its kink"; for a smooth block `V` is everything.
- The hypotheses.
  - `d ≥ 2`: the Scope's. It follows from `hw` (two vectors of `ℝ¹` are never independent), so it
    is redundant in the statement; with `d = 1` and no `hw` the conclusion would fail (`N_0` is
    the sign, every direction with `η_D = 0` is flat, and `η_E = E X` fails for `d_in ≥ 2`).
  - `E` of rank `d`: the paper's ("`E A` […] has rank `d_model`").
  - `D` of rank `d`: the paper's ("`D` has full row rank", Step 1 of part (ii)). Needed in some
    form: for `D = 0` the output is `0` at all weights with `D = 0`, every direction with
    `η_D = 0` is flat, and `(0, η_A)` with `A⁻¹ η_A = diag(1, 0, …)` is not of the stated form.
    Computed (`z23hyp.out`): with `D = 0`, 8 to 21 vectors of the kernel basis are outside the
    space of the stated triples, in all 8 cases. With `D` of rank `d − 1` all were inside.
  - `A` invertible: the paper's ("since `A` is invertible for generic parameters"). In my
    examples with `A` of rank `d − 1` and with `A = 0` the first three clauses still held.
  - One input `w` with `w E W_read ∈ V` and independent rows. The paper names the set, not the
    existence; for generic parameters it holds. Something of it is needed: without an input in
    `V` the hypothesis `hη` is empty. The independence is not what the first three clauses rest
    on, by the paper's argument, and in the example `W_write = 0` (then `g = 0` and no input has
    independent rows) they held for all 12, resp. 22, vectors of the kernel.
  - `f` continuously differentiable on an open `V` that is invariant under positive scalings of
    the rows: the paper's blocks, analytic ones with `V` everything, ReLU-type ones off the
    kinks.
  These examples are single parameters with a tanh block; they do not show that a hypothesis
  can be dropped, only that these cases do not refute the statement without it.
- **Computed, the statement** (`z23steps.py`). One MLP block, one token, a full learned skip,
  `ε = 0`; tanh, GELU, ReLU, ReLU²; `d = 2, 3`; `(d_in, d_out) = (d, d)` and `(d + 1, d + 1)`
  (so that `η_E = E X` and `η_D = −Y D` are conditions); widths `1, d, d + 1`; two random weights
  and skips: 24 cases per activation. The kernel of the Jacobian in the weights and the skip on a
  batch (inputs spread over the directions of `h_0`, from every pattern of active units; the
  entries left after the certified pivots, all below `10⁻⁴⁷`, are taken as zero). For every
  vector of a basis of the kernel: `X` from `η_E = E X` and `Y` from `η_D = −Y D` by least
  squares, `c` as the trace of `A⁻¹(η_A + X A) − Y` over `d`; then the residuals, relative to
  the largest entry of the vector.

  | block | cases | kernel | `η_E − E X` | `η_D + Y D` | `Y + Y^⊤` | `η_A − (A(Y + cI) − XA)` | inputs with independent rows | last clause there |
  |---|---|---|---|---|---|---|---|---|
  | tanh | 24 | `d(d−1) + 2` in all | `≤ 10⁻⁵¹` | `≤ 2·10⁻⁵¹` | `≤ 3·10⁻⁵¹` | `≤ 5·10⁻⁵⁰` | 1080 of 1080 | `≤ 6·10⁻⁵⁰` |
  | GELU | 24 | `d(d−1) + 2` in all | `≤ 10⁻⁵¹` | `≤ 2·10⁻⁵²` | `≤ 10⁻⁵¹` | `≤ 2·10⁻⁵⁰` | 1080 of 1080 | `≤ 2·10⁻⁵⁰` |
  | ReLU | 24 | `d(d−1) + 2 + s` in all | `≤ 3·10⁻⁵²` | `≤ 7·10⁻⁵³` | `≤ 5·10⁻⁵²` | `≤ 3·10⁻⁵¹` | 1908 of 2271 | `≤ 3·10⁻⁵¹` |
  | ReLU² | 24 | `d(d−1) + 2 + s` in all | `≤ 10⁻⁵³` | `≤ 2·10⁻⁵⁴` | `≤ 7·10⁻⁵⁴` | `≤ 2·10⁻⁵²` | 1908 of 2271 | `≤ 3·10⁻⁵²` |

  The kernel on a batch contains the directions that are flat on the whole set of inputs, and
  the stated form is a linear condition, so in these 96 cases every flat direction has the form
  with one `X`, `Y`, `c`, and the last clause holds at the inputs of the batch with independent
  rows. (For the ReLU-type blocks the other inputs are those with no active unit, where `g = 0`.)
  The last clause was computed from the Lean formula, with `DN_0(h) k = √d (k/‖h‖ − h ⟨h, k⟩/‖h‖³)`.
- The size of the kernel is `d(d−1) + 2 + s` in all 48 ReLU and ReLU² cases: no flat direction
  besides the two rotations, the two scalings and the rescalings, which is the paper's "with
  equality for ReLU, ReLU² […] blocks" for a full skip in these cases.
- My first run of this check (`z23steps_relu.out`, inputs with normal coordinates, not sorted by
  pattern) had two ReLU cases with `d = 2` in which the kernel on the batch was larger than
  `d(d−1) + 2 + s` (8 against 6, and 8 against 7), and in the second the last clause failed by
  `0.15` at inputs of the batch. Both were batches that missed a pattern of active units: at the
  same weights, with inputs from every pattern, the kernels are 6 and 7 and every residual is
  below `10⁻⁵⁴` (`z23steps_relu_d2.out`). A kernel vector of a batch that is too small is not a
  flat direction, so this is no counterexample.

### Check 7. The index rows and the axiom file

**Verdict: every sentence of the five rows is true of the statements. Every public theorem of the
five files is in its row and in `checks/Axioms.lean`. Some "Not stated" sentences are true of the
file and no longer of the library.** (By reading; the names by a script; at `320c6cc`.)

- The names. For each file the public names of the source are exactly the names of the third
  cell of its row: 8, 4, 11, 3 (with the definition `UnitsRescaleSphere`) and 1. All 26 theorems
  are in `checks/Axioms.lean` (the three of the last two files since their proofs); the
  definition is not, as no definition is.
- The rows are at lines 924 to 926, 928 and 929 of `STATEMENTS.md` at `320c6cc` (914 to 918 at
  `f4a1ef2`). Their text is unchanged between the two commits but for the status of the last
  two, "in work" then, "proved" now; both are right for their commit.
- Row of `OneBlock/LearnedSkipRMSZeroBoundKinds.lean`: every clause is true (checks 1, 2).
  "blocks of any width with at least one hidden unit": yes; for attention one head of positive
  width, as the row says before.
- Row of `OneBlock/LearnedSkipRMSZeroRescaleBound.lean`: every clause is true (check 3). "any
  space `U` spanned by directions of symmetries inside the block": the hypothesis is
  `U ≤ span {InsideBlocks}`, any subspace of the span of such directions; the docstring has the
  same words. "for the residual network it is the paper's functional dimension, for the learned
  skip it is at least the paper's, so this gives the paper's 'at most'": true, compiled.
- Row of `OneBlock/LearnedSkipTriangularRMSZeroBound.lean`: every clause is true (check 4). The
  head says "for a block with an analytic fixed map"; the first statement asks less (`f`
  differentiable).
- Row of `OneBlock/UnitsRescaleSphere.lean`: every clause is true (check 5). "(at least one
  unit)": in the two theorems, not in the definition.
- Row of `OneBlock/LearnedSkipRMSZeroSteps.lean`: every clause is true (check 6).
- Sentences that later rows have overtaken (true of the file): "Not stated: […] ReLU, ReLU²,
  ReGLU blocks and the equality for them" (first row; the bound for these blocks is in the
  second), "Not stated: the equality" (second row; for ReLU and ReLU² with a full skip it is now
  in `OneBlock/LearnedSkipRMSZeroRescale.lean` and `…RescaleGeneric.lean`, which I did not
  read), "Not stated: ReGLU units" (fourth row; now `OneBlock/UnitsRescaleSphereReGLU.lean`,
  not read).
- Lines 251 to 258 ("Not yet compared by such a reader …") name the five files.

---------------------------------------------------------------------------------------------------

## Part 2: the statements, file by file

Verdict words: SAME, LEAN STRONGER, LEAN WEAKER, DIFFERENT, PART, FALSE. Every statement below
formalizes a part of one sentence of Theorem B.1 (iii), "For `ε = 0` it exceeds that of the
residual network with `ε = 0` by at most `d_model (d_model + 1)/2 − 1`, with equality for ReLU,
ReLU² and ReGLU blocks", or a piece of its proof; PART says which part.

### The fourteen statements by kind (first and third file)

Each says: for `d_in, d_out ≥ d ≥ 2`, at almost every `(θ, A)` (every Haar measure), the
functional dimension with the learned skip `A` on its inputs is at most that of the residual
network with the weights `θ` on its inputs plus `d(d+1)/2 − 1`. Full skip:
`ae_funDimSkipsOn_learned_le_residual_add_<kind>_oneBlock_rmsNorm_zero`; upper triangular skip:
`ae_funDimSkipsOn_tri_le_residual_add_<kind>_oneBlock_rmsNorm_zero`.

| `<kind>` | block in Lean | block in the paper | full skip | triangular skip |
|---|---|---|---|---|
| `mlp` | any analytic activation that is nonzero on the positive reals, one hidden unit at least | tanh, GELU | PART ("at most", this kind); LEAN STRONGER | the same |
| `tanh` | tanh, one hidden unit at least | a tanh block | PART; SAME | PART; SAME |
| `gelu` | GELU, one hidden unit at least | a GELU block | PART; SAME | PART; SAME |
| `gated` | any analytic gate that is nonzero on the positive reals | SwiGLU, GeGLU | PART; LEAN STRONGER | the same |
| `swiglu` | gate SiLU | a SwiGLU block | PART; SAME | PART; SAME |
| `geglu` | gate GELU | a GeGLU block | PART; SAME | PART; SAME |
| `attention` | any number of heads of any positive width, any nonempty set of tokens, any mask in which every token sees some token | "`H` heads of width `d_h ≤ d_model`, causal or not, on sequences of at least two tokens" | PART; LEAN STRONGER (no `d_h ≤ d`, one token allowed, more masks) | the same |

The seven for the triangular skip are the seven for the full skip with `triSkips d 1` and
`Fin 1 → upperTriangular d` in the place of the identity map and `Fin 1 → Matrix d d ℝ`, and
`[LinearOrder d]`: after these replacements each of the seven, and the general one, is the text
of its twin (compared by a script).

### The other statements

| Lean | paper | verdict | note |
|---|---|---|---|
| `ae_funDimSkipsOn_learned_le_funDimOn_residual_add_rmsNorm_zero` (first file) | B.1 (iii), `ε = 0`, "at most", full skip | PART; SAME | any block with an analytic fixed map whose conditions hold at almost every `θ` (check 2) |
| `funDimLearned_add_le_rmsNorm_zero'` (second file) | proof: "For the learned skip, `η^rot` and `K_B` are flat, which gives at least `d_model (d_model − 1) + 2` […] dimensions besides `K_B`" | PART | the count is the paper's; in the place of `K_B`, any subspace of the span of the directions of symmetries inside the block; Lean's `funDimLearned` (all inputs); no hypothesis on the block (check 3) |
| `ae_funDimLearned_le_residual_add_relu_oneBlock_rmsNorm_zero`, `…_reluSq_…`, `…_reglu_…` (second file) | B.1 (iii), `ε = 0`, "at most", full skip, ReLU, ReLU², ReGLU | PART; SAME | with Lean's functional dimensions on all inputs; they give the paper's sentence on the paper's inputs (compiled); the equality is not in this file |
| `funDimSkipsOn_tri_le_learned_rmsNorm_zero` (third file) | proof: "view the network as the network with a full `A` restricted to triangular skips: its flat directions are those of the full network whose entry `η_A` is upper triangular" | LEAN WEAKER | the consequence for the ranks, `fd_tri ≤ fd_full`, on the inputs with no vanishing normalized row; for a differentiable `f` |
| `funDimSkipsOn_tri_add_le_learned_rmsNorm_zero` | proof: "respectively `d_model (d_model − 1)/2 + 2`, dimensions besides `K_B`" | SAME | the same bound by another route (check 4); analytic `f` |
| `funDimSkipsOn_tri_le_funDimOn_residual_add_rmsNorm_zero` | B.1 (iii), `ε = 0`, "at most", triangular skip, at one parameter | PART; SAME | analytic `f`; the conditions of the value for the residual network and an invertible triangular `A` |
| `ae_funDimSkipsOn_tri_le_funDimOn_residual_add_rmsNorm_zero` | the same at generic parameters | PART; SAME | |
| `UnitsRescaleSphere` (definition), `relu_unitsRescaleSphere`, `reluSq_unitsRescaleSphere` (fourth file) | proof, "The case `ε = 0`": "Across the hyperplane `n c_i = 0` […] Since `‖n‖²` has no real linear factor, it divides `q(n)`, so `X_0` is a multiple of `I`", with Lemma B.3 for what is left | LEAN STRONGER | any symmetric `X` (the paper: trace zero); the conclusion names the whole direction; the hypotheses are written out and each is needed (check 5); ReLU and ReLU² only |
| `exists_of_flatSkipsOn_learned_rmsNorm_zero_on` (fifth file) | proof, "The case `ε = 0`", from "In Step 1" to "Steps 3 and 4 run with `Y + c I` in place of `Y`", with Step 3 | SAME | for a full skip; for a block that is continuously differentiable on an open cone of pre-activations; the existence of one input with independent rows is a hypothesis (check 6) |

---------------------------------------------------------------------------------------------------

## What the authors of the papers should know

Nothing false, vacuous, drifted or misdescribed was found. The rest, in the order of its use to
the paper:

1. **For tanh, GELU, SwiGLU and GeGLU blocks the "at most" of part (iii) for `ε = 0` is attained
   in every case I computed**, with a full and with an upper triangular learned skip (`d = 2, 3`,
   widths `1` to `2d + 1`, 256 cases): the difference to the residual network is exactly
   `d(d+1)/2 − 1`. The theorem claims equality for ReLU, ReLU² and ReGLU only. (The twenty-second
   audit, part B, saw this for the full skip with tanh, GELU and SwiGLU; here also GeGLU and the
   triangular skip.) Attention was not computed.
2. **For ReLU, ReLU² and ReGLU the equality holds in every computed case**, full and upper
   triangular skip (192 cases), and for ReLU and ReLU² with a full skip the flat directions
   on a batch are exactly the two rotations, the two scalings and the rescalings (48 cases).
3. **Part (iii) for `ε = 0`, "at most", holds with no condition on the width** (one hidden unit,
   one head) and, for attention, with no condition `d_h ≤ d_model` and for one token too. The
   Lean statements are proved in that generality.
4. **A step that the proof does not write** (seen for the residual network in the twenty-first
   audit; the same here for the learned skip). "The constant terms then give `μ = c` wherever
   `w E A` and `g(w)` are linearly independent": so Steps 1 to 3 give `D_θ g η = g(x)(Y + c I)`,
   and then (17), at these inputs only; elsewhere the difference is a multiple of `h_1`. The next
   sentences use (17) "on the sphere". For the analytic blocks the independent rows are dense and
   continuity closes the gap. For ReLU, ReLU² and ReGLU the set of rows at which some unit is
   active and `g(w)` is parallel to `w E A` can contain an open set at special parameters, so the
   step from "where independent" to "at all rows off the kinks" needs a condition on the
   parameters. It is not stated; it holds for generic parameters, so the theorem stands (the
   twenty-first audit, part A, has the example and the condition for `A = I`). The Lean statement
   of Steps 1 to 3 claims the last clause exactly where the paper proves it.
5. **The conditions of the divisibility step.** "Across the hyperplane `n c_i = 0`, at a point of
   no other such hyperplane […] it divides `q(n)`, so `X_0` is a multiple of `I`" needs: at
   least one hidden unit with `a_i ≠ 0`; the columns `c_i` pairwise non-collinear, opposite
   columns included (two pairs of opposite ReLU units that make a linear map give other
   solutions); and `d_model ≥ 2` for "`‖n‖²` has no real linear factor" (for `d_model = 1` it has
   one, and `X_0 = 0` anyway). All hold for generic parameters and `d_model ≥ 2`; the proof names
   none. With them the step is true as a statement on vectors: exact check of 90 systems, and now
   a Lean proof.
6. **The count for the upper triangular skip needs no condition on a generic triangular `A`** if
   one only wants "at most": the bound follows from the bound for the full skip, because the
   triangular family is a restriction (`d² − d(d−1) = d(d+1)/2 − d(d−1)/2`). The paper's own
   route ("for generic `A` the map from antisymmetric `Y` to the entries of `A Y` below the
   diagonal is invertible") is needed for the equality, not for the bound.
7. **Whoever checks the ReLU-type cases numerically must take inputs from every pattern of active
   units.** With random inputs a batch of twelve times as many inputs as needed for the count
   still stayed below the true rank in 18 of 192 cases, most of them with `d_model = 2`, where a
   pattern can be a narrow arc of directions. Such a batch also shows spurious flat directions
   that are not of the form of Steps 1 to 3.
8. Of the conditions of Steps 1 to 3, "`D` of rank `d_model`" cannot be dropped (`D = 0`), and
   `d_model ≥ 2` is forced by the existence of an input with `w E A` and `g(w)` independent.

## Corrections for `STATEMENTS.md`

None of these is an error in a row; they are sentences that later work has overtaken, and small
gains in precision. Lines are those of `320c6cc`.

1. **Lines 251 to 258** ("Not yet compared by such a reader …"): the five files of this audit can
   move to the compared ones, with this report.
2. **Row of `OneBlock/LearnedSkipRMSZeroBoundKinds.lean`** (line 924): write "Not stated here"
   for "Not stated", and name the rows that state the rest (the next two rows). To add, if
   wanted: "for attention neither `d_h ≤ d` nor two tokens is asked".
3. **Row of `OneBlock/LearnedSkipRMSZeroRescaleBound.lean`** (line 925): "any space `U` spanned
   by directions of symmetries inside the block" → "any subspace `U` of the span of the
   directions of symmetries inside the block" (the docstring of
   `funDimLearned_add_le_rmsNorm_zero'` has the same words). After "the twin for `ε = 0` of
   `funDimLearned_add_le_rmsNorm'`" add "(which asks `D` of rank `d` and no invertible skip; here
   the skip invertible replaces the rank of `D`)". After "for the residual network it is the
   paper's functional dimension" add the statements that show it:
   `ae_exists_jacobianRank_relu_oneBlock_residual_rmsNorm_zero`, `…_reluSq_…`, `…_reglu_…`.
   "Not stated: the equality" → "Not stated here: the equality (for ReLU and ReLU² with a full
   skip: `OneBlock/LearnedSkipRMSZeroRescale.lean`, `…RescaleGeneric.lean`)".
4. **Row of `OneBlock/LearnedSkipTriangularRMSZeroBound.lean`** (line 926): after the first
   statement add "(for a differentiable `f`; the others for an analytic one)". "Not stated" →
   "Not stated here".
5. **Row of `OneBlock/UnitsRescaleSphere.lean`** (line 928): "Not stated: ReGLU units" → "Not
   stated here: ReGLU units (`OneBlock/UnitsRescaleSphereReGLU.lean`)". To add: "each of the
   hypotheses (a unit, `a_i ≠ 0`, `c_i ≠ 0`, pairwise non-collinear, `X` symmetric) is needed:
   twenty-third audit, check 5".
6. **Row of `OneBlock/LearnedSkipRMSZeroSteps.lean`** (line 929): to add: "`d ≥ 2` follows from
   the hypothesis on `w`".
7. A note for the header of `OneBlock/LearnedSkipRMSZeroBoundKinds.lean` and its row, if a
   concrete measure is ever to be shown: `Measure.addHaar` on `Params × (Fin 1 → Matrix d d ℝ)`
   and on `Params × (Fin 1 → upperTriangular d)` needs three instances given by hand (check 1).

## What I could not check

- The proofs: not read, as the brief says. That the 26 theorems are proved rests on the axiom
  lines (`Chk3.lean`) against the build of `/home/claude/lp/lean`, which I did not rebuild.
- Attention blocks: by reading and by compiling instances only; no rank was computed for them.
- The ranks are for `d = 2, 3` and one token. A rank on a batch is a certified lower bound; that
  it is the full rank rests on the entries left after the pivots (below `10⁻³⁸` at 60 digits) and
  on the two batches agreeing. The kernels of check 6 are numerical at 60 digits, not certified.
  The run for ReGLU with `d = 3` took a little over six minutes, more than the five asked for
  one computation.
- For ReLU-type blocks, in 13 of the 192 cases some pattern of active units was seen once among
  20000 directions and gave one input; the counts were reached all the same.
- Whether "`E` of rank `d`" and "`A` invertible" are needed in the statement of Steps 1 to 3: I
  have examples in which the first three clauses hold without them, no proof and no
  counterexample.
- `UnitsRescaleSphere` was computed for up to five coordinates and seven units, with integer
  weights between `−5` and `5`.
- The files written after `f4a1ef2` (`OneBlock/LearnedSkipRMSZeroRescale.lean`,
  `…RescaleGeneric.lean`, `OneBlock/UnitsRescaleSphereReGLU.lean`,
  `OneBlock/LearnedSkipRMSZeroReGLU*.lean`, `OneBlock/LearnedSkipTriangularRMSZeroRank.lean`,
  `OneBlock/LearnedSkipTriangularRMSZeroRescale.lean`, `OneBlock/TurnsActiveRowsSkipLinear.lean`,
  `Residual/LearnedSkipsConverse.lean`) were not read.
