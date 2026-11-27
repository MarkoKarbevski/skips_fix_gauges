STATUS: complete

# Twenty-fourth audit, part B, of Lean statements against the papers: S Theorem B.1 (iii) for `ε = 0` with an upper triangular learned skip (the equality); S Theorem A.12 (i) and the converse of (ii) (24 November 2026)

An independent reader compared the statements of five files of the library `SkipsLean` with the
skips paper (`<scratchpad>/skips.txt`: Theorem A.12 at lines 1361 to 1387, its proof to line 1439,
Remark A.13 after it; Theorem B.1 (iii) at lines 2333 to 2337, its proof from line 2801, Step 5
from line 2849, "The case `ε = 0`" at lines 2862 to 2889). The reader did not write these
statements; the writer is called "the coordinator" below. The statements were audited, not the
proofs. The bound for the triangular skip is in the report of the twenty-third audit and is not
repeated here.

## Commits and files

- Branch `lean-plus` of `/home/claude/lp`. I started at commit `cbb77d0` (23:26 UTC). The branch
  moved while I worked; I looked again at `1773275` (23:27) and at `5fe3cb3` (23:38).
- `OneBlock/LearnedSkipTriangularRMSZeroRank.lean`, `OneBlock/TurnsActiveRowsSkipLinear.lean`,
  `OneBlock/LearnedSkipTriangularRMSZeroRescale.lean`, `Residual/LearnedSkipsConverse.lean`: read
  at `cbb77d0`; byte for byte the same at `5fe3cb3`. No `sorry`.
- `Residual/LearnedSkipsPolar.lean`: read at `cbb77d0`, where its six theorems were `sorry`. Their
  proofs came in at `8ca01b3` and `b1a8491`. At `1773275` and at `5fe3cb3` the header and the six
  statements are the same text as at `cbb77d0` (compared by a script), and the file has no `sorry`.
- So at `5fe3cb3` no file of the five has a `sorry`. The 28 public theorems (2, 6, 12, 2, 6)
  depend on `propext`, `Classical.choice`, `Quot.sound` only (compiled, `ChkAx.lean`, against the
  build in `/home/claude/lp/lean`, whose object files of the five are from 23:03 to 23:27, after
  their proofs).
- My files are in `/home/claude/audit24b/`: `ChkAx.lean`, `Chk1.lean`, `Chk2.lean`, `Chk3.lean`
  (compiled with `lake env lean`, nothing written in the repository) and their outputs;
  `z24maps.py` (sympy, exact), `z24rank.py` and `z24point.py` (ball arithmetic of `python-flint`
  at 60 digits, with `c23.py`, the core of the twenty-third audit, copied: exact derivatives by
  forward mode, rank by elimination with complete pivoting where a pivot is taken only if its
  ball does not contain `0`), `z24conv.py` and `z24polar.py` (mpmath, 40 digits), and their
  outputs.

## Short answer

**Nothing false, nothing vacuous and nothing drifted was found in the five files.**

- The twelve `ae_` statements are at almost every pair (weights, parameter of the skip) for every
  Haar measure on the product; fifteen instances were compiled (nine at `Measure.addHaar` with an
  upper triangular skip, six for every Haar measure with a full skip).
- The rank equality is true at every invertible upper triangular skip, and so is the paper's own
  step: the paper's map (`Y ↦` the entries of `A Y` below the diagonal) has the determinant
  `± a_22 a_33² ⋯ a_dd^(d−1)`, so there is no invertible upper triangular `A` at which it fails.
  "For generic `A`" in Step 5 can read "for every invertible upper triangular `A`". Computed: the
  two ranks are equal in all 112 cases with an invertible triangular `A` (the identity and
  matrices with equal diagonal entries among them); at a singular triangular `A` they can differ
  (44 of 136 cases), so "invertible" cannot simply be dropped.
- The equality for the upper triangular skip is the paper's "with equality for ReLU, ReLU² and
  ReGLU blocks" on the paper's inputs on both sides; this was compiled.
- The converse of Theorem A.12 (ii) is stated as the paper's proof uses it. This reading is the
  one under which the sentence is true: read as a statement on the maps of the blocks it fails
  for a block whose write is zero (see the list for the authors).
- Theorem A.12 (i): the six statements are the paper's, and with the uniqueness statements they
  give the paper's sentence in its own form ("let … be an RQ factorization … computes the same
  function"); this was compiled.

---------------------------------------------------------------------------------------------------

## Part 1: the checks

### Check 1. Generic means almost every parameter, for every Haar measure

**Verdict: yes, in all twelve `ae_` statements (six in `TurnsActiveRowsSkipLinear.lean`, six in
`LearnedSkipTriangularRMSZeroRescale.lean`). None says "there is a parameter" or names an open
set.** (By reading; fifteen instances by compiling, `Chk1.lean`.)

- The Lean text of one statement of each file:

  ```
  theorem ae_turnsActiveRowsSkip_relu_of_linear (ι : V →ₗ[ℝ] Matrix d d ℝ) (v₀ : V)
      (hι : ι v₀ = 1)
      (μ : Measure (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut × V))
      [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) :
      ∀ᵐ p ∂μ, TurnsActiveRowsSkip p.1 (ι p.2)

  theorem ae_funDimSkipsOn_tri_relu_rmsNorm_zero [Nonempty (hid 0)]
      (μ : Measure (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut
        × (Fin 1 → upperTriangular d)))
      [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
      (hdOut : Fintype.card d ≤ Fintype.card dOut) :
      ∀ᵐ p ∂μ, funDimSkipsOn (Arch.mlp relu (rmsNorm 0) hid) (triSkips d 1) p
          (learnedZeroDomain (Arch.mlp relu (rmsNorm 0) hid) p.1
            (fun ℓ => (p.2 ℓ : Matrix d d ℝ)) ∩ noKinkRMS p.1)
          + ((Fintype.card d * (Fintype.card d - 1) / 2 + 2) + Fintype.card (hid 0))
        = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut)
          + Fintype.card d * (Fintype.card d + 1) / 2
  ```
- In every one of the twelve, `μ` is any measure on the pairs with `[μ.IsAddHaarMeasure]`, and
  the conclusion is `∀ᵐ p ∂μ`. In the first file the second factor is any real normed space `V`
  of finite dimension with its Borel σ-algebra (`[FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V]`); in the third it is `Fin 1 → upperTriangular d`, the `d(d+1)/2` entries on and
  above the diagonal. A Haar measure on the product is Lebesgue measure in the weights and in
  these entries, the paper's "generic parameters" of a network whose skip is a parameter
  (twenty-third audit, check 1).
- `Fintype` on every index type: `d`, `dIn`, `dOut` in the `variable` lines of both files,
  `hid ℓ` by `[∀ ℓ, Fintype (hid ℓ)]`; the third file has `[Fintype T] [Nonempty T]` and
  `[LinearOrder d]` (the order of the coordinates, for "upper triangular"). The six statements
  of the first file omit `[Fintype T]`: they are conditions on rows `u ∈ ℝ^d`, and no index type
  of the weights is `T`.
- Compiled at `Measure.addHaar` on `Params × (Fin 1 → upperTriangular (Fin d))`, each ending in a
  number: ReLU, `d = d_in = d_out = 2`, three units: the value `17` (`P = 20`, `20 + 3 − 3 − 3`)
  and `= funDim + 2`; ReLU², `d = 3`, `d_in = 4`, three units: `37` (`P = 39`, `39 + 6 − 5 − 3`)
  and `= funDim + 5`; ReGLU, `d = 2`, three units: `20` (`P = 26`, `26 + 3 − 3 − 6`) and
  `= funDim + 2`. Of the first file, three at `Measure.addHaar` with the upper triangular skip
  (`tri_turn_relu24`, `tri_turn_reglu24`, `tri_row_reluSq24`), and all six for every Haar measure
  on `Params × (Fin 1 → Matrix d d ℝ)` (check 3). All depend on the three standard axioms.
- A note for a user of the statements, not a defect. Applied directly to a concrete `V`
  (`Fin 1 → Matrix d d ℝ` or `Fin 1 → upperTriangular d`), the six statements of the first file
  did not elaborate for me: Lean did not find `BorelSpace V` for the topology of the norm (one
  form ran out of heartbeats). They apply through a wrapper that takes the Borel and Haar
  instances as explicit arguments, which is what the library does in its own proofs
  (`ae_turned_relu_ltz`). `Measure.addHaar` on the product with `upperTriangular d` needs the
  instance `LocallyCompactSpace (upperTriangular d)` by hand, as in the twenty-third audit.

### Check 2. The rank equality

**Verdict: the Lean statement is true at every invertible upper triangular `A`, as stated. The
paper's "for generic `A`" is about another map, and that map too is invertible at every invertible
upper triangular `A`: there is no invertible upper triangular `A` at which the paper's map fails.
Computed: the two ranks agree in all 112 cases with an invertible triangular `A`; they differ in
44 of 136 cases with a singular one. The hypotheses of the two forms are what the comparison
needs.** (By reading and by hand; the two maps exactly, `z24maps.py`; the ranks by computation,
`z24rank.py`.)

- The Lean text:

  ```
  theorem jacobianRankSkips_tri_eq_of_differentiableAt {A : Arch T d 1} {ε : ℝ}
      (hA : A.χ = rmsNorm ε) (θ : Params A dIn dOut) (R : Fin 1 → upperTriangular d)
      (hR : IsUnit (R 0 : Matrix d d ℝ).det) {n : ℕ} (X : Fin n → Matrix T dIn ℝ)
      (hdiff : ∀ i, DifferentiableAt ℝ
        (fun p' : Params A dIn dOut × (Fin 1 → Matrix d d ℝ) =>
          evalSkips A (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) p' (X i))
        (θ, fun ℓ => (R ℓ : Matrix d d ℝ))) :
      jacobianRankSkips A (triSkips d 1) X (θ, R)
        = jacobianRankSkips A (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) X
            (θ, fun ℓ => (R ℓ : Matrix d d ℝ))

  theorem jacobianRankSkips_tri_eq_learned_rmsNorm_zero {A : Arch T d 1}
      (hA : A.χ = rmsNorm 0) (θ : Params A dIn dOut) (R : Fin 1 → upperTriangular d)
      (hR : IsUnit (R 0 : Matrix d d ℝ).det) {n : ℕ} (X : Fin n → Matrix T dIn ℝ)
      (hX : ∀ i, X i ∈ learnedZeroDomain A θ fun ℓ => (R ℓ : Matrix d d ℝ))
      (hfx : ∀ i, DifferentiableAt ℝ (A.f 0) (rmsNorm 0 (X i * θ.E) * θ.read 0)) :
      jacobianRankSkips A (triSkips d 1) X (θ, R) = jacobianRankSkips A (…id…) X (θ, fun ℓ => …)
  ```
- The paper. "For an upper triangular `A`, view the network as the network with a full `A`
  restricted to triangular skips: its flat directions are those of the full network whose entry
  `η_A` is upper triangular", and Step 5: "For an upper triangular `A`, `A Y − X_a A` must be
  upper triangular, which determines `Y` from `X_a`: for generic `A` the map from antisymmetric
  `Y` to the entries of `A Y` below the diagonal is invertible, as it is for `A = I` […] In both
  cases the functional dimension is larger by `d_model (d_model + 1)/2`." So for the paper the
  functional dimensions of the two families are the same number; Lean says that the two
  Jacobians have the same rank on every batch at which the output is differentiable, which gives
  the same functional dimension on every set of such inputs. LEAN STRONGER in form (every batch,
  every invertible triangular `A`), the same in content.
- The Lean route, by hand. The rotation of `h_0` by an antisymmetric `X` (`E ↦ E + τ E X`, the
  read `↦ −X W_read`, the skip `↦ −X A`) is a symmetry for every real `ε`, because an orthogonal
  matrix keeps `v · v` and so passes through `rmsNorm ε`; its direction is flat. Every direction
  of the skip is `U − X A` with `U` upper triangular and `X` antisymmetric as soon as the map
  `(X, U) ↦ U − X A` is onto, and it is injective between spaces of the same dimension `d²`: if
  `X A` is upper triangular with `A` invertible and upper triangular, then `X = (X A) A⁻¹` is
  upper triangular (the inverse of an upper triangular matrix is upper triangular), and an
  antisymmetric upper triangular matrix is `0`. So the brief's question has the answer yes.
- **The two maps, exactly** (`z24maps.py`, output `z24maps.out`; a general upper triangular `A`
  with symbols `a_ij`, `d = 2, 3, 4, 5`):

  | map | determinant, `d = 2, 3, 4, 5` | invertible when |
  |---|---|---|
  | the paper's: antisymmetric `Y ↦` the entries of `A Y` below the diagonal (the rotation of `h_1`) | `a22`, `a22 a33²`, `a22 a33² a44³`, `a22 a33² a44³ a55⁴` | `a_22, …, a_dd ≠ 0` |
  | the Lean route's: antisymmetric `X ↦` the entries of `X A` below the diagonal (the rotation of `h_0`) | `a11`, `a11² a22`, `a11³ a22² a33`, `a11⁴ a22³ a33² a44` | `a_11, …, a_(d−1)(d−1) ≠ 0` |

  By hand, for every `d`: with `Y = L − L^⊤`, `L` strictly lower triangular, the part of `A Y`
  below the diagonal is that of `A L` (`A L^⊤` is strictly upper triangular), and
  `(A L)_ij = ∑_{k ≥ i} a_ik L_kj` is triangular in the row index with the diagonal `a_ii`, so the
  determinant is `∏_i a_ii^(i−1)` up to sign. The other map is the mirror image.
  So the two are different maps, and each is invertible at every invertible upper triangular `A`.
  **There is no invertible upper triangular `A` at which the paper's map is not invertible.** The
  paper's "for generic `A`" is true and can be sharpened to "for every invertible upper
  triangular `A`" (which the proof already has: "`A` is invertible for generic parameters").
- **Computed, the two ranks at the same weights, skip and batch** (`z24rank.py`). One block, one
  token; tanh and ReLU; `ε = 0` and `ε = 1/2` (the first statement is for every `ε`); `d = 2`
  with `(d_in, d_out) = (2, 2), (3, 3)` and widths `1, 3`; `d = 3` with `(3, 3), (4, 4)` and
  width `4`; one random weights per size, `E` and `D` of certified rank `d`; two batches each;
  inputs spread over the directions of `h_0` and, for ReLU, taken from every pattern of active
  units. 248 cases.

  | the upper triangular `A` | cases | the two ranks |
  |---|---|---|
  | invertible: `I`; `diag(1, −1)`; `[[1,5],[0,1]]`; `[[2,1],[0,2]]`; `[[−3/2, 7/10],[0, 1/3]]`; for `d = 3`: `I`, `diag(1, −1, 2)`, a unipotent one, a general one | 112 | **equal in all 112**; in all of them also equal to the generic count (`P + d(d+1)/2 − (d(d−1)/2 + 2) − s` for `ε = 0`, `P + d(d+1)/2 − d(d−1)/2 − s` for `ε > 0`) |
  | singular with one zero on the diagonal: the last entry (`diag(1,0)`, `[[1,1],[0,0]]`, `diag(1,1,0)`), the first (`diag(0,1)`, `[[0,1],[0,1]]`, `diag(0,1,1)`), or `a_22` for `d = 3` (`[[1,2,3],[0,0,4],[0,0,1]]`, where both maps of the table above are singular) | 88 | equal in all 88 |
  | singular with `a_11 = a_dd = 0`: `[[0,1],[0,0]]`; for `d = 3` `[[0,2,3],[0,1,4],[0,0,0]]` and the nilpotent `[[0,2,3],[0,0,4],[0,0,0]]` | 32 | **different in all 32**: the triangular family has rank one less |
  | the zero matrix (`d = 2`) | 16 | different in 12 (one less), equal in 4 (width 1, `ε = 0`, a degenerate network) |

  The smallest pivot is `4.4·10⁻¹¹` of the largest and no entry that is left is above
  `7.2·10⁻⁴⁸`. A rank on a batch is a certified lower bound; that it is not larger rests on the
  size of what is left. For `A = [[0,1],[0,0]]` the difference also follows by hand: `X A` and
  `A Y` are both upper triangular there, so both rotations lie in the triangular family and its
  kernel does not shrink with the family.
- So: at the invertible triangular skips with nothing generic about them (`A = I`, equal diagonal
  entries, negative entries) the equality holds, as the Lean statement says. The hypothesis
  "invertible" is sufficient and not necessary (one of `a_11 ≠ 0`, `a_22 ≠ 0` sufficed in all
  cases with `d = 2`), and it cannot be dropped without a replacement.
- The hypotheses of the two forms.
  - `hdiff` (first form): at every input of the batch the output with a full skip is a
    differentiable function of the weights and the skip at `(θ, R)`. The comparison is a chain
    rule: the Jacobian of the triangular family is that of the full family composed with the
    inclusion. Where the output is not differentiable Lean's derivative of the full family is
    `0` by convention, and the statement would be about that convention. For `ε > 0` and a
    differentiable `f` it holds at every input.
  - `hX`, `hfx` (second form, `ε = 0`): the inputs of `learnedZeroDomain` (no row of `x E` and
    no row of `h_1` is zero) at which `f` is differentiable at `N_0(x E) W_read`. These are the
    paper's inputs: "the inputs `x` at which no hidden unit sits at its kink", and "With `ε = 0`,
    it also excludes the inputs at which a state that is normalized vanishes". For an analytic
    block `hfx` is no condition.
  - One block (`Arch T d 1`), any real `ε` in the first form (for `ε < 0` Lean's `rmsNorm` is
    still a total function and the rotation is still a symmetry), any finite set of tokens.

### Check 3. The linear family

**Verdict: `ι v₀ = 1` gives the proof one point at which its polynomials are not zero (the
residual network), and it is enough. Some condition on the family is needed: for `ι = 0` the
conclusion fails at almost every weights. The six conclusions are those of the full-skip
statements with `ι p.2` in the place of `p.2 0`, and the full-skip statements follow from the
six. The instance to the upper triangular family is a statement at almost every upper triangular
skip.** (By reading; by compiling, `Chk1.lean`.)

- The six statements have the form `(ι : V →ₗ[ℝ] Matrix d d ℝ) (v₀ : V) (hι : ι v₀ = 1)
  (μ : Measure (Params … × V)) [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) : ∀ᵐ p ∂μ, …` with
  the conclusions `TurnsActiveRowsSkip p.1 (ι p.2)` (ReLU, ReLU²),
  `TurnsActiveRowsGatedSkip p.1 (ι p.2)` (ReGLU), and, with `[Nonempty (hid 0)]`,
  `∃ v, (∀ i, (v ᵥ* p.1.read 0) i ≠ 0) ∧ LinearIndependent ℝ ![v ᵥ* ι p.2, vanillaBlock σ … v]`
  (for ReGLU: the gate columns `Sum.inl i` off their kinks, and `gatedBlock relu …`).
- What `ι v₀ = 1` is for. The conditions fail only where polynomials in `(θ, v)` vanish (one for
  every nonempty set of hidden units); a polynomial that is not zero at one point is not zero
  almost everywhere. The point is taken at the skip `1`, where the statement is the one for the
  residual network (`ae_turnsActiveRows_relu` and its twins, twenty-first audit). So the
  hypothesis is used once, as a witness.
- Is it needed. Compiled (`not_turns_zero_skip24`): for the skip `0`, `TurnsActiveRowsSkip θ 0`
  fails at every `θ` that has a row off the kinks with an active unit (no pair `0, b` is linearly
  independent, and the closure of the empty set is empty). With a hidden unit and a nonzero
  column of `W_read` such a row exists, so for the family `ι = 0` the conclusion fails at almost
  every `(θ, v)`. The family `ι = 0` has every other hypothesis. I did not look for the weakest
  condition; "contains the identity" is sufficient and covers the paper's two families.
- The same as the full-skip forms. `ae_turnsActiveRowsSkip_relu` and `…_reluSq`
  (`OneBlock/LearnedSkipRMSZeroRescaleGeneric.lean`) conclude `TurnsActiveRowsSkip p.1 (p.2 0)`,
  `ae_exists_turned_row_skip_relu`, `…_reluSq` the row with `v ᵥ* p.2 0`, and the two for ReGLU
  (`OneBlock/LearnedSkipRMSZeroReGLUGeneric.lean`) the same with `TurnsActiveRowsGatedSkip` and
  `gatedBlock`. Compiled: with `ι` the projection `v ↦ v 0` of `Fin 1 → Matrix d d ℝ` and
  `v₀ = (1)`, each of the six linear statements gives its full-skip twin word for word, for
  every Haar measure (`full_from_linear_relu24` to `full_row_from_linear_reglu24`).
- The upper triangular family. Compiled for every `d` and every Haar measure `μ` on
  `Params × (Fin 1 → upperTriangular d)`, with `ι` the inclusion and `v₀ = (1)`
  (`Matrix.blockTriangular_one`): `∀ᵐ p ∂μ, TurnsActiveRowsSkip p.1 (p.2 0 : Matrix d d ℝ)`
  (`tri_from_linear_relu24`), the same for ReGLU and for the turned row of ReLU². This is "at
  almost every weights and upper triangular skip".

### Check 4. The value and the equality for the triangular skip (twelve statements)

**Verdict: the counts are the paper's; the functional dimension is the paper's on the left and,
at almost every weights, on the right; the result is the paper's "with equality for ReLU, ReLU²
and ReGLU blocks" for the upper triangular skip. The hypotheses at one parameter hold together
(a parameter with `d = 2` is given, and the ranks there are the stated ones).** (By reading;
by compiling, `Chk1.lean`, `Chk2.lean`; one parameter by hand and by computation, `z24point.py`.)

- The Lean text of the statement at one parameter (the value) and of the equality:

  ```
  theorem funDimSkipsOn_tri_mlp_rescale_rmsNorm_zero {k : ℕ}
      (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
      (hhom : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
      (hU : UnitsRescaleSphere σ σ' k d d (hid 0))
      (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
      (hθ : OneBlockGenericRMS θ) (hd : 2 ≤ Fintype.card d)
      (R : Fin 1 → upperTriangular d) (hR : IsUnit (R 0 : Matrix d d ℝ).det)
      (hturn : TurnsActiveRowsSkip θ (R 0 : Matrix d d ℝ))
      (hw : ∃ v : d → ℝ, (∀ i, (v ᵥ* θ.read 0) i ≠ 0) ∧ LinearIndependent ℝ
        ![v ᵥ* (R 0 : Matrix d d ℝ), vanillaBlock σ (θ.read 0) (θ.write 0) v]) :
      funDimSkipsOn (Arch.mlp σ (rmsNorm 0) hid) (triSkips d 1) (θ, R)
          (learnedZeroDomain (Arch.mlp σ (rmsNorm 0) hid) θ (fun ℓ => (R ℓ : Matrix d d ℝ))
            ∩ noKinkRMS θ)
          + ((Fintype.card d * (Fintype.card d - 1) / 2 + 2) + Fintype.card (hid 0))
        = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
          + Fintype.card d * (Fintype.card d + 1) / 2

  theorem ae_funDimSkipsOn_tri_relu_rmsNorm_zero_eq_residual_add [Nonempty (hid 0)]
      (μ : Measure (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut
        × (Fin 1 → upperTriangular d)))
      [μ.IsAddHaarMeasure] (hd : …) (hdIn : …) (hdOut : …) :
      ∀ᵐ p ∂μ, funDimSkipsOn (Arch.mlp relu (rmsNorm 0) hid) (triSkips d 1) p
          (learnedZeroDomain (Arch.mlp relu (rmsNorm 0) hid) p.1
            (fun ℓ => (p.2 ℓ : Matrix d d ℝ)) ∩ noKinkRMS p.1)
        = funDim (Arch.mlp relu (rmsNorm 0) hid) 1 p.1
          + (Fintype.card d * (Fintype.card d + 1) / 2 - 1)
  ```
- The counts. Lean: `fd + ((d(d−1)/2 + 2) + s) = P + d(d+1)/2`. The paper: "which gives at least
  `d_model (d_model − 1) + 2`, respectively `d_model (d_model − 1)/2 + 2`, dimensions besides
  `K_B`", "the network has `d²_model`, respectively `d_model (d_model + 1)/2`, more parameters",
  and "Then Step 5 gives equality". The same: `d(d+1)/2` entries of the triangular skip, and a
  kernel of dimension `d(d−1)/2 + 2` (the rotations, where `Y` is determined by `X_a`, and the
  two scalings) plus `s`. `s`: `Fintype.card (hid 0)` in the six statements for an MLP block,
  `2 * Fintype.card (hid 0)` in the six for ReGLU; the paper: "Each hidden unit of a ReLU or
  ReLU² block can be rescaled, and so can the value of each hidden unit of a gated block and, in
  ReGLU, its gate". The same. The divisions by `2` are exact (`d(d−1)` and `d(d+1)` are even),
  the statement has no subtraction, and in the equality `d(d+1)/2 − 1` is a true difference for
  `d ≥ 2`. The residual network has `P − d(d−1)/2 − 1 − s`, and the difference of the two
  values is `d(d+1)/2 − 1`: the paper's number.
- Which functional dimension, on the left. `funDimSkipsOn … (triSkips d 1) p U` is the largest
  rank of the Jacobian in the weights and the `d(d+1)/2` entries of the skip over the finite
  batches of inputs of `U`, and `U` is `learnedZeroDomain ∩ noKinkRMS θ` (no row of `x E` and of
  `h_1` is zero; every entry of `x E W_read` is nonzero), resp. `∩ noKinkGateRMS θ` (every entry
  of the gate columns of `x E W_read` is nonzero; the value of a ReGLU unit has no kink). The
  paper: the functional dimension is `P − dim K(θ)`, some finite batch has kernel exactly
  `K(θ)`, and "every input" means the inputs with no hidden unit at its kink and, for `ε = 0`,
  no vanishing normalized state. `x E W_read` and the pre-activation `N_0(x E) W_read` differ by
  a positive factor in every row, so the kinks are the same. The same functional dimension.
- On the right: `funDim … 1 p.1`, Lean's functional dimension of the residual network on all
  inputs (its derivative is `0` where the output is not differentiable). That it is the paper's
  value at almost every weights is shown by `ae_funDim_relu_oneBlock_residual_rmsNorm_zero` with
  `ae_exists_jacobianRank_relu_oneBlock_residual_rmsNorm_zero`, the same pair for `reluSq`
  (`OneBlock/ResidualRMSZeroRescaleGeneric.lean`), and
  `ae_funDim_reglu_oneBlock_residual_rmsNorm_zero` with
  `ae_exists_jacobianRank_reglu_oneBlock_residual_rmsNorm_zero`
  (`OneBlock/ResidualRMSZeroReGLUGeneric.lean`): a batch of the paper's inputs
  (`residualZeroDomain ∩ noKinkRMS θ`, resp. `∩ noKinkGateRMS θ`) has a Jacobian of the rank
  `funDim`. **Compiled** (`relu_tri_paper24`, `reluSq_tri_paper24`, `reglu_tri_paper24`, standard
  axioms only): for every Haar measure on the pairs, at almost every `(θ, A)` with `A` upper
  triangular,

  `funDimSkipsOn (tri) on the paper's inputs = funDimOn (residual) on the paper's inputs + (d(d+1)/2 − 1)`.

  This is the paper's "For `ε = 0` it exceeds that of the residual network with `ε = 0` by […]
  `d_model (d_model + 1)/2 − 1`, with equality for ReLU, ReLU² and ReGLU blocks", for the upper
  triangular skip, with the paper's functional dimension on both sides, at the same weights
  (a set of weights of measure zero is a set of pairs of measure zero, so this compares the two
  generic values).
- The three statements at one parameter fit together (compiled): "the value" says that the
  supremum over the batches of the paper's inputs is the count, "a batch with this rank" that it
  is attained, "no batch with a larger rank" the bound for each batch.
- Against the theorem's setting. `d ≥ 2`, `d_in, d_out ≥ d`: the theorem's. One hidden unit and
  no width: part (iii) asks no width. Any nonempty finite set of tokens. Verdict SAME for ReLU,
  ReLU², ReGLU; the three statements at one parameter for an MLP block are for any activation
  with `hσ`, `hhom`, `hU`, which ReLU (`k = 1`) and ReLU² (`k = 2`) have.
- The hypotheses at one parameter: `hσ`, `hhom`, `hU` are facts on the activation (proved for
  ReLU and ReLU²); `OneBlockGenericRMS θ` (`E`, `D` of rank `d`, rows of `W_write` nonzero,
  columns of `W_read` nonzero and pairwise non-collinear), resp. `OneBlockGenericReGLURMS θ`,
  are the paper's generic conditions; `hR` is the paper's "`A` is invertible for generic
  parameters"; `hturn` and `hw` are the condition that the paper's proof needs and does not
  state (twenty-first and twenty-third audits). They are those of the statements for the full
  skip, with `R : Fin 1 → upperTriangular d`.
- **Not vacuous together: one parameter with `d = 2`.** One token, `d_in = d_out = 2`, one hidden
  unit, `E = D = I`, the skip `A = [[1,1],[0,1]]`.
  - ReLU (and ReLU²): `W_read = (1, 0)^⊤`, `W_write = (0, 1)`. `OneBlockGenericRMS`: `E`, `D` of
    rank 2, the row `(0, 1)` and the column `(1, 0)` nonzero, one unit (nothing to compare).
    `hR`: `det A = 1`. `hturn`: a row `v` off the kink with the unit active has `v_1 > 0`; there
    `v A = (v_1, v_1 + v_2)` and the output is `σ(v_1) (0, 1)`, with the minor `v_1 σ(v_1) ≠ 0`,
    so `v` itself is turned. `hw`: `v = (1, 0)`.
  - ReGLU: gate column `(1, 0)^⊤`, value column `(0, 1)^⊤`, `W_write = (0, 1)`. The output at
    `u` with `u_1 > 0` is `u_1 u_2 (0, 1)`, the minor with `u A` is `u_1² u_2`, nonzero on a
    dense set; `hw`: `v = (1, 1)`; the value column is not a multiple of the gate column.
  - Computed there (`z24point.py`, two batches of 80 inputs from every pattern): ReLU and ReLU²
    (`P = 12`): triangular family `11`, the count `12 + 3 − 3 − 1`; full family `11`; residual
    network `9 = 12 − 2 − 1`; difference `2 = d(d+1)/2 − 1`. ReGLU (`P = 14`): `12`, `12`, `10`;
    difference `2`. Nothing left above `10⁻⁵⁶`.
  - Also compiled (`exists_hyp_relu24`): from the `ae_` statements, a parameter with `d = 2`,
    one unit, at which `OneBlockGenericRMS`, `hturn` and `hw` hold together exists.
- I computed no further ranks: the twenty-third audit has 192 cases for the triangular skip with
  these blocks, all at the count.

### Check 5. Theorem A.12 (ii), "Conversely"

**Verdict: the two statements are the paper's sentence in the reading of its proof, clause by
clause: SAME. That reading is the fair one, and it is stronger as a hypothesis than "each block
of the network in the variables `h_ℓ G_ℓ` computes what a pre-RMSNorm block computes"; with that
weaker hypothesis the sentence would fail for a block whose write is zero. The hypotheses are the
paper's, none is missing, the rank of the reads and one token are needed, and they hold together.
The numerical test of the contrapositive found no counterexample.** (By reading and by hand; by
compiling, `Chk3.lean`; by computation, `z24conv.py`.)

- The Lean text (the second statement has `{ε : ℝ} (hε : 0 < ε)`, `rmsNorm ε`, and the conclusion
  `∀ ℓ, (skipProdFwd S ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ`):

  ```
  theorem skipProdFwd_conformal_of_residual_rmsNorm_zero (θ : Params A dIn dOut)
      (S : Fin L → GL d ℝ) (G : Fin (L + 1) → GL d ℝ)
      (hG : ∀ ℓ : Fin L, (G ℓ.castSucc)⁻¹ * S ℓ * G ℓ.succ = 1)
      (hread : ∀ ℓ : Fin L, (θ.read ℓ).rank = Fintype.card d) (hD : θ.D.rank = Fintype.card d)
      (hres : ∀ ℓ : Fin L, ∃ W' : Matrix d (A.r ℓ) ℝ, ∀ h : Matrix T d ℝ,
        rmsNorm 0 (h * (↑(G ℓ.castSucc)⁻¹ : Matrix d d ℝ)) * θ.read ℓ = rmsNorm 0 h * W')
      (hresD : ∃ D' : Matrix d dOut ℝ, ∀ h : Matrix T d ℝ,
        rmsNorm 0 (h * (↑(G (Fin.last L))⁻¹ : Matrix d d ℝ)) * θ.D = rmsNorm 0 h * D') :
      ∀ ℓ, ∃ (c : ℝ) (P : Matrix d d ℝ), 0 < c ∧ P ∈ Matrix.orthogonalGroup d ℝ ∧
        (skipProdFwd S ℓ : Matrix d d ℝ) = c • P
  ```
- Clause by clause.
  - "let the reads and the readout have rank `d_model`": `hread`, `hD`.
  - "let invertible `G_0, …, G_L` turn every skip into the identity, `G_{ℓ−1}⁻¹ A_ℓ G_ℓ = I`":
    `G : Fin (L + 1) → GL d ℝ` and `hG`, with Lean's block `ℓ : Fin L` the paper's block `ℓ + 1`
    (`G ℓ.castSucc` is the paper's `G_{ℓ−1}`, `G ℓ.succ` its `G_ℓ`). The skips are elements of
    `GL d ℝ`: the theorem's "whose skips `A_ℓ` are invertible in (i) and (ii)", and `hG` forces
    it anyway.
  - "If the network, written in the variables `h_ℓ G_ℓ`, is a pre-RMSNorm residual network":
    `hres`, `hresD`. In the variables `h′_ℓ = h_ℓ G_ℓ` the recursion is
    `h′_ℓ = h′_{ℓ−1} G_{ℓ−1}⁻¹ A_ℓ G_ℓ + f(N_ε(h′_{ℓ−1} G_{ℓ−1}⁻¹) W_read^ℓ) W_write^ℓ G_ℓ`, so
    the skip is the identity, block `ℓ` reads `N_ε(h′ G_{ℓ−1}⁻¹) W_read^ℓ` and the readout reads
    `N_ε(h′ G_L⁻¹) D`. The proof: "In a pre-RMSNorm residual network every read has the form
    `N_ε(h′) W`; as the reads and the readout have rank `d_model`, this gives matrices `M_ℓ` with
    `N_ε(h′ G_0⁻¹ Π_ℓ) = N_ε(h′) M_ℓ` for all `h′`". Lean's hypothesis is this sentence: a
    matrix `W′` with `N_ε(h G_{ℓ−1}⁻¹) W_read^ℓ = N_ε(h) W′` for every `h`.
  - "then every `Π_ℓ` lies in `G`": `∀ ℓ : Fin (L + 1)`, so `ℓ = 0, …, L`, with
    `skipProdFwd S` the products `Π_0 = 1`, `Π_{ℓ+1} = Π_ℓ * S ℓ` (compiled: `Π_0 = 1`, and for
    two blocks `Π_2 = S 0 * S 1`, the paper's `A_1 A_2`). `G`: for `ε = 0` a positive multiple of
    an orthogonal matrix (`CO(d)`, Lemma A.2: "`G = cQ` with `Q` orthogonal", `c > 0`), for
    `ε > 0` orthogonal. The paper's "`ε ≥ 0`" is the two statements.
- Is the reading fair, and how strong. Lean's hypothesis is about the reads as functions of all
  `h`, as the proof says ("for all `h′`"). It implies that every block of the network in the new
  variables is, as a map of `h′`, a pre-RMSNorm block. The converse implication fails when a
  block loses what it reads. Example, by hand: `L = 2`, `A_1 = diag(2, 1)`, `A_2 = A_1⁻¹`,
  `W_write^2 = 0`, any reads and readout of rank `d`, `G_0 = I`, `G_1 = A_1⁻¹`, `G_2 = I`. Then
  `G_0⁻¹ A_1 G_1 = I`, `G_1⁻¹ A_2 G_2 = I`; in the new variables block 1 reads `N_ε(h′_0)
  W_read^1`, block 2 adds `0`, and the readout reads `N_ε(h′_2) D`: the network in these
  variables computes, block by block, a pre-RMSNorm residual network (block 2 with the write
  `0` and any read). But `Π_1 = diag(2, 1)` is not in `G`. In Lean's reading the hypothesis
  fails here, as it should: the read of block 2 is `N_ε(h′ A_1) W_read^2`, which is not
  `N_ε(h′) W′`. So the paper's sentence is true in the reading of its proof and of Lean, and
  needs that reading; see the list for the authors.
- The hypotheses.
  - The rank of the reads and of the readout: the paper's, and needed. By hand: in the example
    above take `W_write^2` anything and `W_read^2 = 0`; then `hres` holds for block 2 with
    `W′ = 0`, every other hypothesis holds, and `Π_1` is not in `G`.
  - `[Nonempty T]`: the paper has tokens; needed, since with no token every `hres` holds.
  - Not needed and not asked: nothing on `E`, on the writes, on `f`; `dIn` need not be finite;
    `L = 0` is allowed (the conclusion is then `Π_0 = I`).
  - Missing: none. The proof uses only `hG`, the ranks, and the form of the reads.
- They hold together. Compiled (`converse_hyp_sat24`): for every depth `L`, every `d`, every
  real `ε`, every `θ` and all orthogonal skips, `G_ℓ = Π_ℓ⁻¹` satisfies `hG`, `hres`
  (`W′ = Π_{ℓ−1} W_read^ℓ`) and `hresD`. An instance with `L = 2`, `d = 2`: `A_1` the rotation by
  90°, `A_2` any rotation, `G = (I, A_1⁻¹, (A_1 A_2)⁻¹)`, reads and readout of rank 2. Computed
  with random orthogonal `A_1`, `A_2` (`z24conv.py`, part (b), `d = 2` and `3`): the three
  residuals are below `2·10⁻⁴¹` for `ε = 0` and for `ε = 1/2`, and every `Π_ℓ` is orthogonal;
  for `ε = 0` also with `A_1 = 2 Q_1`, `A_2 = Q_2/3`, `G_0 = 5 Q_0`.
- **The numerical test of the contrapositive** (`z24conv.py`, mpmath, 40 digits; least squares
  for `W′` in `N_ε(h X) W = N_ε(h) W′` over 60 rows `h` of lengths `1/3` to `30`; the residual
  relative to the left side).
  - One matrix `X = G⁻¹`, a read of rank `d`, `d = 2, 3`, reads `d × d` and `d × (d + 1)`:
    `X` orthogonal (also `−Q`): residual below `2·10⁻⁴¹` for both `ε`; `X = (3/2) Q`: below
    `2·10⁻⁴¹` for `ε = 0`, `0.08` to `0.11` for `ε = 1/2`; `X = diag(2, 1, …) Q` and `X`
    random: `0.08` to `0.22` for both. So `W′` exists exactly for `X` in `G`, in these 20 cases.
  - The statement for `L = 2`, seven choices of `(A_1, A_2, G_0)`, `d = 2, 3`, both `ε`
    (28 cases): the hypothesis held in 10, and in all 10 every `Π_ℓ` was in `G`. Where some
    `Π_ℓ` was not in `G` (14 cases), a read that uses it had a residual of `0.1` to `0.5`:
    `A_2` not conformal shows at the readout; `A_1` not conformal with `A_2 = A_1⁻¹ Q_2` (so
    `Π_1 ∉ G`, `Π_2 ∈ G`) shows at the read of block 2 alone; with `G_0 = Π_1` (so `G_1 = I`)
    at the read of block 1 and at the readout; conformal skips that are not orthogonal, with
    `ε = 1/2`, at all three. With orthogonal skips and a random `G_0` (4 cases) all three
    residuals are `0.10` to `0.23`: the hypothesis fails and the conclusion holds, which the
    statement allows. No case had the hypothesis without the conclusion.

### Check 6. Theorem A.12 (i) (six statements)

**Verdict: `Matrix.PosDef` is "symmetric positive definite", `BlockTriangular id` with
`∀ i, 0 < R i i` is "upper triangular with positive diagonal", the factorizations are written as
in the paper, the uniqueness statements are true as stated with no invertibility hypothesis, and
the networks are the paper's. The existence form with the uniqueness statements covers the
paper's sentence (compiled). Invertible skips are needed for each of the two networks. The
degenerate cases are right.** (By reading; by compiling, `Chk3.lean`; the two matrix facts by
computation, `z24polar.py`.)

- The Lean text:

  ```
  theorem exists_posDef_mul_orthogonal_transpose (X : Matrix d d ℝ) (hX : IsUnit X.det) :
      ∃ S Q : Matrix d d ℝ, S.PosDef ∧ Q ∈ Matrix.orthogonalGroup d ℝ ∧ X = S * Qᵀ
  theorem posDef_mul_orthogonal_transpose_unique {S S' Q Q' : Matrix d d ℝ} (hS : S.PosDef)
      (hS' : S'.PosDef) (hQ : Q ∈ Matrix.orthogonalGroup d ℝ)
      (hQ' : Q' ∈ Matrix.orthogonalGroup d ℝ) (h : S * Qᵀ = S' * Q'ᵀ) : S = S' ∧ Q = Q'
  theorem exists_upperTriangular_pos_mul_orthogonal_transpose [LinearOrder d] (X : Matrix d d ℝ)
      (hX : IsUnit X.det) :
      ∃ R Q : Matrix d d ℝ, R.BlockTriangular id ∧ (∀ i, 0 < R i i) ∧
        Q ∈ Matrix.orthogonalGroup d ℝ ∧ X = R * Qᵀ
  theorem upperTriangular_pos_mul_orthogonal_transpose_unique [LinearOrder d]
      {R R' Q Q' : Matrix d d ℝ} (hR : R.BlockTriangular id) (hRp : ∀ i, 0 < R i i)
      (hR' : R'.BlockTriangular id) (hRp' : ∀ i, 0 < R' i i)
      (hQ : Q ∈ Matrix.orthogonalGroup d ℝ) (hQ' : Q' ∈ Matrix.orthogonalGroup d ℝ)
      (h : R * Qᵀ = R' * Q'ᵀ) : R = R' ∧ Q = Q'
  theorem exists_cob_learned_upperTriangular_pos [LinearOrder d] (ε : ℝ) (hA : A.χ = rmsNorm ε)
      (S : Fin L → Matrix d d ℝ) (hS : ∀ ℓ, IsUnit (S ℓ).det) (θ : Params A dIn dOut) :
      ∃ Q : Fin (L + 1) → GL d ℝ, Q 0 = 1 ∧
        (∀ ℓ, (Q ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ) ∧
        (∀ ℓ, (cobSkip S Q ℓ).BlockTriangular id ∧ ∀ i, 0 < cobSkip S Q ℓ i i) ∧
        ∀ x : Matrix T dIn ℝ, eval A (cobSkip S Q) (θ.cob Q Q) x = eval A S θ x
  theorem exists_cob_learned_posDef (ε : ℝ) (hA : A.χ = rmsNorm ε) … :
      ∃ Q …, Q 0 = 1 ∧ (∀ ℓ, … orthogonal) ∧ (∀ ℓ, (cobSkip S Q ℓ).PosDef) ∧ ∀ x, eval … = eval …
  ```
- `Matrix.PosDef`. In the pinned Mathlib (`Mathlib/LinearAlgebra/Matrix/PosDef.lean`, tag
  `v4.36.0`) the definition is

  ```
  def PosDef (M : Matrix n n R) :=
    M.IsHermitian ∧ ∀ ⦃x : n →₀ R⦄, x ≠ 0 → 0 < x.sum fun i xi ↦ x.sum fun j xj ↦ star xi * M i j * xj
  ```
  with vectors of finite support; for a finite index type it is `M.IsHermitian ∧ ∀ x ≠ 0,
  0 < star x ⬝ᵥ (M *ᵥ x)` (`Matrix.posDef_iff_dotProduct_mulVec`). Compiled (`posDef_iff24`): for
  a real matrix on a finite `d`, `S.PosDef ↔ Sᵀ = S ∧ ∀ x ≠ 0, 0 < x ⬝ᵥ (S *ᵥ x)`: symmetric
  positive definite. The header of the Lean file gives this second form as "Mathlib's notion";
  it is the equivalent form, not the text of the definition.
- `R.BlockTriangular id` says `R i j = 0` for `j < i` (twenty-third audit, compiled), and
  `∀ i, 0 < R i i` is "positive diagonal". `X = R * Qᵀ`, `X = S * Qᵀ` are the paper's
  `Q_{ℓ−1}ᵀ A_ℓ = R_ℓ Q_ℓᵀ`, `= S_ℓ Q_ℓᵀ` with `X = Q_{ℓ−1}ᵀ A_ℓ`.
- The uniqueness statements, by hand. Polar: `S Qᵀ = S′ Q′ᵀ` gives `S² = S′²` (multiply each
  side by its transpose), a symmetric positive definite matrix has one symmetric positive
  definite square root, so `S = S′`, and `Qᵀ = S⁻¹ S Qᵀ` gives `Q = Q′`. RQ: `R′⁻¹ R = Q′ᵀ Q` is
  upper triangular with positive diagonal and orthogonal, hence `I`. Neither needs an
  invertibility hypothesis: `S` and `R` are invertible by their hypotheses (compiled for the
  polar form: `S * Qᵀ` has a nonzero determinant). They are the paper's "exists, and is unique"
  and "uniquely". The paper's formulas `S = (X Xᵀ)^{1/2}`, `Qᵀ = S⁻¹ X` are not in the
  statements; with existence and uniqueness they say the same.
- **Computed** (`z24polar.py`, mpmath, 40 digits): 30 matrices, `d = 1, …, 5`, both signs of the
  determinant, built as `R_0 Q_0ᵀ` and as `S_0 Q_0ᵀ` from planted factors; the factors computed
  again from the product alone (RQ by Gram-Schmidt on the rows from the last one up, polar from
  the eigenvalues of `X Xᵀ`): `X − R Qᵀ ≤ 2·10⁻⁴¹`, `Q Qᵀ − I ≤ 6·10⁻³⁹`, nothing below the
  diagonal, positive diagonal, and the planted factors found again up to `5·10⁻³⁹`; for the
  polar form `X − S Qᵀ ≤ 10⁻⁴¹`, `Q Qᵀ − I ≤ 2·10⁻³⁸`, `S − Sᵀ ≤ 5·10⁻⁴¹`, the smallest
  eigenvalue of `S` positive, the planted factors found again up to `8·10⁻³⁹`. Without "positive
  diagonal" a second factorization exists (the sign of one column of `Q` flipped): the
  hypothesis `hRp` is what makes the RQ factorization unique.
- The networks. `cobSkip S Q ℓ = Q_ℓ⁻¹ S_ℓ Q_{ℓ+1}` (Lean's indices; the paper's
  `Q_{ℓ−1}ᵀ A_ℓ Q_ℓ`), and `θ.cob Q Q` has `E Q_0`, the reads `Q_{ℓ−1}⁻¹ W_read^ℓ`, the writes
  `W_write^ℓ Q_ℓ` and the readout `Q_L⁻¹ D` (`Symmetry/ChangeOfBasis.lean`: `read ℓ := (K
  ℓ.castSucc)⁻¹ * θ.read ℓ`, `write ℓ := θ.write ℓ * G ℓ.succ`, `D := (K (Fin.last L))⁻¹ * θ.D`).
  With `Q 0 = 1` the embedding is `E`, and for an orthogonal `Q` the inverse is the transpose:
  the paper's "the skips `R_ℓ`, the reads `Q_{ℓ−1}ᵀ W_read^ℓ`, the writes `W_write^ℓ Q_ℓ` and the
  readout `Q_Lᵀ D`", with `Q_0 = I`. The same.
- The existence form against the paper's sentence. The paper fixes the `Q_ℓ` by the
  factorizations and says that the network built from them computes the same function; Lean
  says that there are orthogonal `Q_ℓ` with `Q_0 = I`, the changed skips of the stated kind, and
  the same function. **Compiled, that the Lean statements give the paper's sentence in its own
  form** (`Chk3.lean`, standard axioms only):
  - `paper_i_exists24`, `paper_i_exists_polar24`: for invertible skips there are `Q_0 = I`,
    orthogonal `Q_ℓ` and `R_ℓ` upper triangular with positive diagonal (resp. `S_ℓ` positive
    definite) with `Q_{ℓ−1}ᵀ A_ℓ = R_ℓ Q_ℓᵀ` for every `ℓ`;
  - `paper_i_unique24`, `paper_i_unique_polar24`: two such families `(Q, R)`, `(Q′, R′)` are
    equal (induction on `ℓ` with the uniqueness statement for one matrix);
  - `paper_i_eval24`: for any orthogonal `Q_0, …, Q_L` and any `R_ℓ` with
    `Q_{ℓ−1}ᵀ A_ℓ = R_ℓ Q_ℓᵀ`, the changed skips are the `R_ℓ` and
    `eval A R (θ.cob Q Q) x = eval A S θ x` for every `x` and every real `ε`.
  So the Lean covers "let `Q_{ℓ−1}ᵀ A_ℓ = R_ℓ Q_ℓᵀ` be an RQ factorization […] computes the same
  function", and the same for the polar decompositions. The last of the three shows a little
  more: the function is kept for every orthogonal `Q_0, …, Q_L`, also with `Q_0 ≠ I` (the
  embedding takes `Q_0`, as Remark A.13 says), and whatever the shape of the `R_ℓ`.
- Invertibility. The paper: "whose skips `A_ℓ` are invertible in (i)". Lean: `hS : ∀ ℓ,
  IsUnit (S ℓ).det`. It is needed for each of the two networks, and exactly: compiled
  (`isUnit_of_tri_pos24`, `isUnit_of_posDef24`), if for some `Q` every `cobSkip S Q ℓ` is upper
  triangular with positive diagonal, or every one is positive definite, then every skip is
  invertible. So for a singular skip (`A_1 = 0`, any `d ≥ 1`) no such `Q` exists. The form
  without "positive diagonal", for any skips, is `exists_cob_learned_upperTriangular`
  (`Residual/OneChangeOfBasis.lean`), as the header says.
- "`ε ≥ 0`": Lean has every real `ε`, LEAN STRONGER; an orthogonal matrix passes through
  `rmsNorm ε` for every `ε` (`rmsNorm_mul_orthogonal`).
- Degenerate cases. `L = 0`: the statement gives `Q_0 = 1` and the same function (compiled).
  `d` empty: all matrices are equal and the factorizations exist (compiled). `d` with one
  element: `X = (x)`, `x ≠ 0`, `R = S = (|x|)`, `Q = (sign x)`. No hypothesis on `T`, `dOut`.

### Check 7. The index rows and the axiom file

**Verdict: every sentence of the five rows is true of the statements. Every public theorem of
the five files is in its row and in `checks/Axioms.lean`.** (By reading; the names by a script;
at `5fe3cb3`.)

- For each file the public names of the source are exactly the names of the third cell of its
  row: 6 (line 863, `Residual/LearnedSkipsPolar.lean`), 2 (line 864,
  `Residual/LearnedSkipsConverse.lean`), 2 (line 936,
  `OneBlock/LearnedSkipTriangularRMSZeroRank.lean`), 6 (line 944,
  `OneBlock/TurnsActiveRowsSkipLinear.lean`), 12 (line 945,
  `OneBlock/LearnedSkipTriangularRMSZeroRescale.lean`). All five rows say "proved", which is
  right at `5fe3cb3`. All 28 theorems have a `#print axioms` line in `checks/Axioms.lean`.
- Line 863: every clause is true (check 6). "(`Matrix.PosDef`)": see check 6 for what Mathlib's
  definition is.
- Line 864: every clause is true (check 5).
- Line 936: every clause is true (check 2). The row does not say that the statements are for one
  block, nor that "invertible" is all that is asked of the triangular skip where the paper says
  "generic".
- Line 944: every clause is true (checks 1, 3).
- Line 945: every clause is true (checks 1, 4). "`funDim` of the residual network": the row does
  not name the statements that make this the paper's value. The numeric check it names
  (`learned_skip_zero_relu_check_2026-11-24.py`) is in `ai_notes/` and has the triangular skip.
- Lines 260 to 271 ("Not yet compared by such a reader …") name the five files.
- The headers of the five files say nothing that the statements do not bear out; the one
  sentence to sharpen is the header's wording on `Matrix.PosDef` (check 6).

---------------------------------------------------------------------------------------------------

## Part 2: the statements, file by file

Verdict words: SAME, LEAN STRONGER, LEAN WEAKER, DIFFERENT, PART, FALSE.

| Lean | paper | verdict | note |
|---|---|---|---|
| `jacobianRankSkips_tri_eq_of_differentiableAt` | proof of B.1 (iii): "view the network as the network with a full `A` restricted to triangular skips"; Step 5: "for generic `A` the map […] is invertible […] In both cases the functional dimension is larger by `d_model (d_model + 1)/2`" | LEAN STRONGER | on every batch at which the output is differentiable, at every invertible upper triangular skip, every real `ε`; the paper: the two functional dimensions, for generic `A` (check 2) |
| `jacobianRankSkips_tri_eq_learned_rmsNorm_zero` | the same for `ε = 0`, on the paper's inputs | LEAN STRONGER | the inputs with no vanishing normalized row at which `f` is differentiable at the normalized read |
| `ae_turnsActiveRowsSkip_relu_of_linear`, `…_reluSq_of_linear`, `ae_turnsActiveRowsGatedSkip_reglu_of_linear` | not in the paper: the condition that the step "`μ = c` wherever `w E A` and `g(w)` are linearly independent" needs for ReLU-type blocks, at generic parameters, "full or upper triangular" | no paper sentence | true of both families of the paper (check 3); for every Haar measure |
| `ae_exists_turned_row_skip_relu_of_linear`, `…_reluSq_of_linear`, `…_reglu_of_linear` | the same: one row off the kinks that the block turns | no paper sentence | with a hidden unit |
| `exists_jacobianRankSkips_tri_mlp_rescale_rmsNorm_zero`, `exists_jacobianRankSkips_tri_reglu_rmsNorm_zero` | B.1 (iii), `ε = 0`, "with equality", triangular skip, at one parameter: a batch of the paper's inputs with the rank `P + d(d+1)/2 − (d(d−1)/2 + 2) − s` | PART; SAME | under the conditions of the proof, two of which the paper does not state (`hturn`, `hw`) |
| `jacobianRankSkips_tri_add_le_mlp_rescale_rmsNorm_zero`, `jacobianRankSkips_tri_add_le_reglu_rmsNorm_zero` | "which gives at least […] `d_model (d_model − 1)/2 + 2`, dimensions besides `K_B`" | PART; SAME | no batch of the paper's inputs has a larger rank |
| `funDimSkipsOn_tri_mlp_rescale_rmsNorm_zero`, `funDimSkipsOn_tri_reglu_rmsNorm_zero` | the value at one parameter | PART; SAME | the paper's functional dimension (check 4); `s = d_hidden`, resp. `2 d_hidden` |
| `ae_funDimSkipsOn_tri_relu_rmsNorm_zero`, `…_reluSq_…`, `…_reglu_…` | the value at generic parameters | PART; SAME | `d_in, d_out ≥ d ≥ 2`, one hidden unit, no width |
| `ae_funDimSkipsOn_tri_relu_rmsNorm_zero_eq_residual_add`, `…_reluSq_…`, `…_reglu_…` | B.1 (iii): "For `ε = 0` it exceeds that of the residual network with `ε = 0` by at most `d_model (d_model + 1)/2 − 1`, with equality for ReLU, ReLU² and ReGLU blocks", upper triangular skip | SAME | the right side is Lean's `funDim`; with the statements named in check 4 it is the paper's on the paper's inputs (compiled) |
| `skipProdFwd_conformal_of_residual_rmsNorm_zero` | A.12 (ii), "Conversely", `ε = 0` | SAME | in the reading of the proof: every read and the readout has the form `N_0(h′) W′` for all `h′` (check 5) |
| `skipProdFwd_orthogonal_of_residual_rmsNorm` | A.12 (ii), "Conversely", `ε > 0` | SAME | the same |
| `exists_posDef_mul_orthogonal_transpose` | proof of A.12 (i): "every invertible matrix `X` is `X = S Qᵀ` with `S = (X Xᵀ)^{1/2}` symmetric positive definite and `Qᵀ = S⁻¹ X` orthogonal" | SAME | the formulas for `S` and `Q` follow with the uniqueness |
| `posDef_mul_orthogonal_transpose_unique` | "uniquely" | SAME | no invertibility asked; none needed |
| `exists_upperTriangular_pos_mul_orthogonal_transpose` | "the RQ factorization of the invertible matrix `Q_{ℓ−1}ᵀ A_ℓ` exists" | SAME | |
| `upperTriangular_pos_mul_orthogonal_transpose_unique` | "and is unique" | SAME | |
| `exists_cob_learned_upperTriangular_pos` | A.12 (i), first two sentences; A.14 (iv) with "positive diagonal" | SAME | the existence form; with the uniqueness it gives the paper's form (compiled); every real `ε` |
| `exists_cob_learned_posDef` | A.12 (i), "So does the network built in the same way from the polar decompositions" | SAME | the same |

---------------------------------------------------------------------------------------------------

## What the authors of the papers should know

Nothing false, vacuous, drifted or misdescribed was found. The rest, in the order of its use to
the paper:

1. **Theorem A.12 (ii), "Conversely": the hypothesis needs the reading of the proof.** "If the
   network, written in the variables `h_ℓ G_ℓ`, is a pre-RMSNorm residual network" is used by
   the proof as "every read and the readout has the form `N_ε(h′) W` for all `h′`". Read as a
   statement on what the blocks compute, the sentence fails in a degenerate case: `L = 2`,
   `A_1 = diag(2, 1)`, `A_2 = A_1⁻¹`, `W_write^2 = 0`, reads and readout of rank `d_model`,
   `G = (I, A_1⁻¹, I)`. Every skip becomes the identity, the network in the new variables is
   block 1, a block that adds `0`, and a readout `N_ε(h′_2) D`, which is a pre-RMSNorm residual
   network; and `Π_1 = diag(2, 1)` is not in `G`. The hypothesis "the reads […] have rank
   `d_model`" does not exclude it. A wording that the proof proves as it stands: "If, in the
   variables `h_ℓ G_ℓ`, every read and the readout has the form `N_ε(h′) W′`, then every `Π_ℓ`
   lies in `G`." The Lean statements say this.
2. **Step 5 of Theorem B.1 (iii): "for generic `A`" can be "for every invertible upper
   triangular `A`".** The map from antisymmetric `Y` to the entries of `A Y` below the diagonal
   has the determinant `± a_22 a_33² ⋯ a_dd^(d−1)`. The Lean proof uses the rotation of `h_0`
   in its place (determinant `± a_11^(d−1) ⋯ a_(d−1)(d−1)`). Computed: the families of upper
   triangular and of all skips have the same Jacobian rank at every invertible triangular `A`
   tried, `A = I` among them (112 cases); at the singular triangular `A` with
   `a_11 = a_dd = 0` that I tried the triangular family has rank one less (these form a set of
   measure zero, so the theorem is not touched).
3. **Part (iii) for `ε = 0`, the equality for the upper triangular skip, is now a Lean theorem**
   for ReLU, ReLU² and ReGLU, with the paper's functional dimension on both sides, for
   `d_in, d_out ≥ d ≥ 2`, one hidden unit at least and no condition on the width.
4. **The condition that the proof of part (iii) for `ε = 0` does not state** (the rows at which
   `w E A` and `g(w)` are linearly independent are dense among the rows off the kinks with an
   active unit; twenty-first and twenty-third audits) holds at almost every weights and upper
   triangular skip too, so the theorem stands for both kinds of skip. The Lean statement is for
   any family of skips that is linear in its parameter and contains the identity.
5. **Theorem A.12 (i).** Invertible skips are exactly what "positive diagonal" and "positive
   definite" need: if the changed skips have either property, the skips are invertible. The
   function is kept for every orthogonal `Q_0, …, Q_L` and every real `ε`; the factorizations
   only choose the `Q_ℓ`. Both facts for one matrix, with uniqueness, are Lean theorems.

## Corrections for `STATEMENTS.md`

None of these is an error in a row. Lines are those of `5fe3cb3`.

1. **Lines 260 to 271** ("Not yet compared by such a reader …"): the five files of this audit
   (`Residual/LearnedSkipsConverse.lean`, `OneBlock/LearnedSkipTriangularRMSZeroRank.lean`,
   `OneBlock/TurnsActiveRowsSkipLinear.lean`,
   `OneBlock/LearnedSkipTriangularRMSZeroRescale.lean`, `Residual/LearnedSkipsPolar.lean`) can
   move to the compared ones, with this report.
2. **Line 936** (`OneBlock/LearnedSkipTriangularRMSZeroRank.lean`): after "at an invertible upper
   triangular skip `R`" add "(every invertible one; the paper's Step 5 says 'for generic `A`',
   and its map is invertible at every invertible upper triangular `A` too; at a singular
   triangular skip the two ranks can differ: twenty-fourth audit, part B, check 2)". Add "one
   block".
3. **Line 944** (`OneBlock/TurnsActiveRowsSkipLinear.lean`): after "at almost every `(θ, v)`"
   add "(for every Haar measure on the pairs)". To add: "'is the identity at one point' is
   sufficient; some condition is needed (for `ι = 0` the conclusion fails)"; and, for a user:
   "to apply the statements to a concrete `V`, pass the Borel and Haar instances through a
   wrapper with explicit arguments, as `ae_turned_relu_ltz` does".
4. **Line 945** (`OneBlock/LearnedSkipTriangularRMSZeroRescale.lean`): after "`funDim` of the
   residual network with the weights `θ`" add "(Lean's `funDim` on all inputs; at almost every
   `θ` it is the functional dimension on the paper's inputs, by
   `ae_exists_jacobianRank_relu_oneBlock_residual_rmsNorm_zero`, `…_reluSq_…`, `…_reglu_…`)".
5. **Line 864** (`Residual/LearnedSkipsConverse.lean`): to add: "the skips and the `G_ℓ` are
   elements of `GL(d)`; the hypothesis is on the reads as functions of every `h`, which is
   stronger than 'every block computes a pre-RMSNorm block' (a block whose write is zero:
   twenty-fourth audit, part B, check 5)".
6. **Line 863** (`Residual/LearnedSkipsPolar.lean`): after "(`Matrix.PosDef`)" add "(for a real
   matrix on a finite index type: symmetric with `0 < x ⬝ᵥ (S *ᵥ x)` for `x ≠ 0`,
   `Matrix.posDef_iff_dotProduct_mulVec`)". To add: "with the uniqueness statements the
   existence form gives the paper's form, in which the `Q_ℓ` are those of the factorizations;
   the function is kept for every orthogonal `Q_ℓ` (`eval_cob`)". In the header of the file,
   "`Matrix.PosDef` is Mathlib's notion: Hermitian […] with `0 < x ⬝ᵥ (M *ᵥ x)`" → "… is
   Mathlib's notion; for a finite index type it is: Hermitian […]" (Mathlib's definition is
   written with vectors of finite support).

## What I could not check

- The proofs: not read, as the brief says. That the 28 theorems are proved rests on the axiom
  lines (`ChkAx.lean`) against the build of `/home/claude/lp/lean`, which I did not rebuild.
- The ranks of check 2 are for tanh and ReLU, `d = 2, 3`, one token, `ε = 0` and `ε = 1/2`; no
  ReLU², ReGLU or attention there. A rank on a batch is a certified lower bound; that it is not
  larger rests on the entries left after the pivots (below `10⁻⁴⁷` at 60 digits) and on the two
  batches agreeing. The run for ReLU with `d = 3` took 5 minutes 6 seconds, a little more than
  the five asked for one computation; the others took 22 seconds to 3 minutes 17 seconds.
- Which singular upper triangular skips have equal ranks: seen in examples only (equal with
  `a_11 = 0` alone or `a_22 = 0` alone; different with `a_11 = a_dd = 0`), no statement.
- The weakest condition on a linear family of skips under which the conclusions of check 3 hold:
  not looked for.
- The numerics of checks 5 and 6 are at 40 digits and not certified; the least squares of check 5
  are on 60 rows.
- The statements for the full skip (`OneBlock/LearnedSkipRMSZeroRescale.lean`,
  `…RescaleGeneric.lean`, `OneBlock/LearnedSkipRMSZeroReGLU.lean`, `…ReGLUGeneric.lean`) were
  read only as far as the comparison of check 3 and the hypotheses of check 4 need; they are not
  part of this audit.
- The files written after I began (`OneBlock/UnitsParallelAt.lean`,
  `OneBlock/SkiplessHomogeneousRMSZeroEqAt.lean`) were not read.
