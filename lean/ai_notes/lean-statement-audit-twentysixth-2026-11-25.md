STATUS: complete

# Twenty-sixth audit of Lean statements against the papers (25 November 2026)

Subject: S Theorem B.1 (iii) for `ε > 0` and blocks of any width (Step 4 of its proof for tanh, GELU,
SwiGLU and GeGLU units; the network statements); S Lemma B.2; S Proposition A.9 for writes; S Lemma A.18,
the form with the readout. "S" is the skips paper (`<scratchpad>/skips.txt`).

The reader of this audit did not write the Lean statements; their writer is called "the coordinator".
The audit is of statements and definitions, not of proofs.

## Commits read, and `sorry`

- Start: `baf38e7` (`lean: ai_notes: status by statement, the check of Step 4 for gated units`). There,
  `OneBlock/GatedUnitsNoSymmetricPart.lean` had 2 `sorry` and `OneBlock/LearnedSkipNarrowGated.lean` had 5;
  the other five files had none.
- The branch moved during the audit to `b52cd65` (`… SwiGLU and GeGLU with a full learned skip, and the
  upper triangular skip …: proved, registered`). Between the two commits the seven files of the subject
  changed only in the two gated files, and there only by proofs: the removed lines are the seven `sorry`
  (checked with `git diff baf38e7 b52cd65`, the removed lines listed), the added lines are private helpers
  and proofs. The public statements and definitions are the same at both commits. At `b52cd65` none of the
  seven files has a `sorry`.
- At the end of the audit the branch was at `95e12a2` (`lean: Dimension/RescaleActionHomogeneous.lean:
  registered …`). Between `b52cd65` and `95e12a2` none of the seven files changed in a statement; the only
  change in them is the last paragraph of the header of `Dimension/UpperBoundReadout.lean` (it now points
  to the new files for the symmetries inside blocks and for the group), and its index row was edited in the
  same way. Check 7 reads the index and `checks/Axioms.lean` at `95e12a2`.
- All compiling was done on copies in the audit folder, against the build of the working copy (which holds
  the state of `b52cd65` for the seven files), with nothing written to the repository.

## Method, in one paragraph

Reading: every statement against the paper's text, clause by clause. Compiling: one file of checks
(`Chk.lean` in the audit folder, 12 s, exit code 0) with instances at a concrete Haar measure, the
comparisons between old and new statements, the entries of `cobDir` and `Params.cob`, a generic form of
Lemma A.18, and `#print axioms` for all 23 public theorems. Computing (own scripts, `mpmath` at 60 digits,
or exact fractions): `z26units.py` (Step 4 on vectors, 38 cases), `z26hyp.py` (which hypotheses are needed,
44 cases), `z26net.py` and `z26net2.py` (ranks of the networks), `z26b2.py` (dimensions in Lemma B.2).
No computation took more than three minutes.

## Part 1: checks

### Check 1. Generic means almost every parameter, for every Haar measure

By reading and by compiling. The eight `ae_` statements are

- `ae_funDimLearned_tanh_rmsNorm_eq_residual_add_of_nonempty`, `ae_funDimLearned_tanh_rmsNorm_of_nonempty`,
  `ae_funDimLearned_gelu_rmsNorm_eq_residual_add_of_nonempty`, `ae_funDimLearned_gelu_rmsNorm_of_nonempty`
  (`OneBlock/LearnedSkipNarrowMlp.lean`);
- `ae_funDimLearned_swiglu_rmsNorm_eq_residual_add_of_nonempty`, `ae_funDimLearned_swiglu_rmsNorm_of_nonempty`,
  `ae_funDimLearned_geglu_rmsNorm_eq_residual_add_of_nonempty`, `ae_funDimLearned_geglu_rmsNorm_of_nonempty`
  (`OneBlock/LearnedSkipNarrowGated.lean`).

Each has the form (tanh, the difference):

```lean
theorem ae_funDimLearned_tanh_rmsNorm_eq_residual_add_of_nonempty (hε : 0 < ε) [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) Real.tanh (rmsNorm ε) hid) dIn dOut
      × (Fin 1 → Matrix d d ℝ)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, funDimLearned (Arch.mlp Real.tanh (rmsNorm ε) hid) p
      = funDim (Arch.mlp Real.tanh (rmsNorm ε) hid) 1 p.1
        + Fintype.card d * (Fintype.card d + 1) / 2
```

- The quantifier is `∀ᵐ p ∂μ` for **every** measure `μ` with `[μ.IsAddHaarMeasure]` on the pairs
  (weights, skip) `Params … × (Fin 1 → Matrix d d ℝ)`. None of the eight says "there is a parameter" or
  speaks of an open set.
- `Fintype` on every index type: `T`, `d`, `dIn`, `dOut` (the `variable` line of each file) and
  `[∀ ℓ, Fintype (hid ℓ)]`; also `[Nonempty T]`.
- Compiled: all eight at `Measure.addHaar` with `T = Fin 1`, `d = d_in = Fin 2`, `d_out = Fin 3`, **one**
  hidden unit, `ε = 1`; for tanh the two conclusions written out with numbers (`… + 2 * (2 + 1) / 2` and
  `… + 2 * (2 − 1) = finrank … + 2 ^ 2`). As in the twenty-fourth audit, `Measure.addHaar` on the product
  needs the two instances `LocallyCompactSpace` and `BorelSpace` of `Fin 1 → Matrix d d ℝ`, given by
  `inferInstanceAs` from `Fin 1 → d → d → ℝ`; the statements themselves take any `μ`.

Verdict: **SAME** as "for generic parameters", in the sense used throughout the library.

### Check 2. `UnitsNoSymmetricPart` and `GatedUnitsNoSymmetricPart` against equation (17)

```lean
def UnitsNoSymmetricPart (σ σ' : ℝ → ℝ) (n k q : Type*) [Fintype n] [Fintype k] [Fintype q] : Prop :=
  ∀ (c : q → n → ℝ) (a : q → k → ℝ) (X : Matrix n n ℝ) (ψc : q → n → ℝ) (ψa : q → k → ℝ)
    (O : Set (n → ℝ)),
    (∀ i, a i ≠ 0) → (∀ i, c i ≠ 0) → (∀ i j, i ≠ j → ∀ r : ℝ, c i ≠ r • c j) → Xᵀ = X →
    IsOpen O → O.Nonempty →
    (∀ x ∈ O, ∑ i, (σ (x ⬝ᵥ c i) • ψa i + (σ' (x ⬝ᵥ c i) * (x ⬝ᵥ ψc i)) • a i)
      = ((x ᵥ* X) ⬝ᵥ x) • ∑ i, (σ' (x ⬝ᵥ c i) * (x ⬝ᵥ c i)) • a i) →
    X = 0

def GatedUnitsNoSymmetricPart (σ σ' : ℝ → ℝ) (n k q : Type*) [Fintype n] [Fintype k] [Fintype q] : Prop :=
  ∀ (c e : q → n → ℝ) (a : q → k → ℝ) (X : Matrix n n ℝ) (ψc ψe : q → n → ℝ) (ψa : q → k → ℝ)
    (O : Set (n → ℝ)),
    (∀ i, a i ≠ 0) → (∀ i, c i ≠ 0) → (∀ i j, i ≠ j → ∀ r : ℝ, c i ≠ r • c j) →
    (∀ i, e i ≠ 0) → Xᵀ = X → IsOpen O → O.Nonempty →
    (∀ x ∈ O, ∑ i, ((σ (x ⬝ᵥ c i) * (x ⬝ᵥ e i)) • ψa i
        + (σ' (x ⬝ᵥ c i) * (x ⬝ᵥ ψc i) * (x ⬝ᵥ e i)) • a i
        + (σ (x ⬝ᵥ c i) * (x ⬝ᵥ ψe i)) • a i)
      = ((x ᵥ* X) ⬝ᵥ x) • ∑ i,
          (σ' (x ⬝ᵥ c i) * (x ⬝ᵥ c i) * (x ⬝ᵥ e i) + σ (x ⬝ᵥ c i) * (x ⬝ᵥ e i)) • a i) →
    X = 0
```

with `tanh_unitsNoSymmetricPart`, `gelu_unitsNoSymmetricPart`, `silu_gatedUnitsNoSymmetricPart`,
`gelu_gatedUnitsNoSymmetricPart`, each with `[Nonempty q]`.

**(a) The two sides (by reading).** With `B(x) = ∑_i σ(x c_i) a_i`: the derivative of `B(x)` in the
weights along `(ψc, ψa)` is `∑_i [σ(x c_i) ψa_i + σ'(x c_i)(x ψc_i) a_i]`, the left side. The derivative of
`B` in `x` along `k` is `∑_i σ'(x c_i)(k c_i) a_i`, so `𝐃B(x) x = ∑_i σ'(x c_i)(x c_i) a_i`, and the right
side is `(x X xᵀ) 𝐃B(x) x` (`(x ᵥ* X) ⬝ᵥ x` is `x X xᵀ`). For gated units,
`B(x) = ∑_i σ(x c_i)(x e_i) a_i`: the derivative along `(ψc, ψe, ψa)` is the left side, term by term, and
`𝐃B(x) x = ∑_i [σ'(x c_i)(x c_i)(x e_i) + σ(x c_i)(x e_i)] a_i` is the sum on the right. Both are the
paper's `∂_ψ B(n) = q(n) 𝐃B(n) n`, with `X` in the place of `X_s / d_model`. **SAME.**

**(b) In the network (by reading; the Lean helpers `entry_lnm`, `entry_gun` compile).** The paper: `η′` has
the entries `E X_s` at `E`; the input `n = N_ε(x E)` of the block then has the derivative
`n X_s − q(n) n`, `q(n) = n X_s nᵀ / d_model`; so
`0 = D_θ g η′ = 𝐃B(n)(n X_s) − q(n) 𝐃B(n) n + ∂_{η′} B(n)`, and "The change `n X_s` of the input moves
the block as the entries `X_s W_read` at `W_read` do": `𝐃B(n)(n X_s) = ∂ B(n)` along the read direction
`X_s W_read`. Hence `∂_ψ B(n) = q(n) 𝐃B(n) n` with `ψ_read = η′_read + X_s W_read`, `ψ_write = η′_write`:
the sign is plus and the factor is `1/d_model`. In Lean, `NoSymmetricPart` (`OneBlock/LearnedSkipGain.lean`)
is

```lean
      fderiv ℝ (A.f 0) (rmsNorm ε (x * θ.E) * θ.read 0)
          (tangentRMS X (rmsNorm ε (x * θ.E)) * θ.read 0 + rmsNorm ε (x * θ.E) * ψr) * θ.write 0
        + A.f 0 (rmsNorm ε (x * θ.E) * θ.read 0) * ψw = 0
```

with `tangentRMS X n = n X − ((n X) · n / d) n` row by row (`Depth/StepTanhRMS.lean`), which is the paper's
`n X_s − q(n) n` for a symmetric `X`. `noSymmetricPart_mlp_rmsNorm_of_units` applies the units statement
with `c_i` the columns of `W_read`, `a_i` the rows of `W_write`, `ψc_i = X c_i + (ψ_read)_i`, `ψa = ψ_write`
and `(card d)⁻¹ • X`, on the set of the rows `v` such that the input with all rows `v` is in the image of
`N_ε` (open, contains `0`). The gated twin uses `ψc_i = X c_i + (ψ_read)_{gate i}`,
`ψe_i = X e_i + (ψ_read)_{value i}`. This is the paper's derivation: sign plus, factor `1/d`. **SAME.**

**(c) The hypotheses.** The paper says "In every case `q` vanishes on an open set for generic parameters";
the generic conditions it names are those of the start of the proof (line 2407): "every `a_i` is nonzero,
and the `c_i` are nonzero and pairwise non-collinear", and for gated blocks "the value weights […] have
`e_i ≠ 0` and are not proportional to its gate weights". "At least one unit" is implicit in "one block".
Each hypothesis, with a computation (`z26hyp.py`: the kernel of the linear system in `(X, ψ)` on rows of
the ball, 60 digits; "X free" means the kernel has a nonzero `X`-part, so the conclusion fails):

| hypothesis | named by the paper | needed? |
|---|---|---|
| at least one unit (`[Nonempty q]` in the four theorems) | implicit | **needed**: with no unit both sides are `0` for every `X` |
| `a_i ≠ 0` for all `i` | yes | **needed in part**: one unit with `a_1 = 0` leaves `X` free (tanh, GELU, SwiGLU, GeGLU). More than needed: with `a_1 = 0`, `a_2 ≠ 0`, `X = 0` is still forced |
| `c_i ≠ 0` | yes | **needed in part**: one unit with `c_1 = 0` leaves `X` free (all four kinds; `σ(0) = 0`). With `c_1 = 0`, `c_2 ≠ 0`: `X = 0` forced |
| `c_i` pairwise non-collinear | yes | **needed in part, for tanh and for GELU alike**: `c_2 = c_1`, `a_2 = −a_1` (two units that cancel, `B = 0`) leaves `X` free, with all other hypotheses true; for tanh also `c_2 = −c_1`, `a_2 = a_1`. More than needed: `X = 0` is still forced for `c_2 = 2 c_1` (with generic `a` and with `a_2 = −a_1`), for `c_2 = ±c_1` with generic `a`, for GELU with `c_2 = −c_1` and `a_2 = ±a_1`, and for a cancelling pair plus a third generic unit. What is needed is only that the units do not cancel |
| gated: `e_i ≠ 0` | yes | **needed**: one unit with `e_1 = 0` leaves `X` free |
| gated: `e_i` not proportional to `c_i` | yes (paper) | **not asked by Lean, and not needed**: with `e_1 = c_1`, with `e_i = r_i c_i`, and with `e_1 = c_2`, `e_2 = c_1`, the kernel is the `q` rescalings and its `X`-part is `0` (reason: the term of order `t⁴` is `(n̂ X n̂ᵀ) ∑_{n̂ c_i > 0} r_i (n̂ c_i)² a_i`, which does not vanish identically for non-collinear `c_i`) |
| gated: gate columns pairwise non-collinear | yes | **needed in part**: `c_2 = c_1`, `e_2 = −e_1`, `a_2 = a_1` (`B = 0`) leaves `X` free. `c_2 = c_1` with generic `e`, `a`, and `c_2 = −c_1`: `X = 0` forced |
| `Xᵀ = X` | yes (`X_s`) | **needed**: an antisymmetric `X` has `x X xᵀ = 0`, so `ψ = 0` and any antisymmetric `X` solve the equation |
| `O` open and nonempty | the paper: the open ball | needed (an empty `O` asks nothing). Lean allows any nonempty open set: more general than the ball, harmless (both sides are analytic) |

So the Lean hypotheses are the paper's generic conditions, minus "the value is not proportional to the gate",
which Step 4 does not need.

**(d) Are the four statements true (computation, `z26units.py`).** For random units, on rows of the ball of
radius `√n`, at 60 digits, the kernel of the linear system in `(X, ψ)` (unknowns: the entries of a symmetric
`X` and of `ψ`; three times as many equations as unknowns):

- tanh and GELU, `(n, k, q)` = (2,2,1), (3,3,1), (3,3,2), (4,4,2), (3,3,3), (3,3,5), (2,2,4), (4,2,3),
  (2,3,1): the kernel is `0` in all 18 cases (smallest singular value over largest between `9·10⁻⁶` and
  `5·10⁻²`). Fewer units than coordinates: (3,3,1), (3,3,2), (4,4,2), (4,2,3), (2,3,1), (2,2,1).
- SwiGLU and GeGLU, `(n, k, q)` = (2,2,1), (3,3,1), (3,3,2), (4,4,2), (3,3,3), (3,3,4), (2,2,3), (4,2,2):
  the kernel has dimension `q` (the rescalings of the values) in all 16 cases, and the largest `X`-entry of
  a kernel vector is below `10⁻⁶⁰`; the gap between the last nonzero singular value (above `6·10⁻⁴` of the
  largest) and the first zero one (below `10⁻⁶¹`) is clear.
- The same on the ball of radius `1/2` (4 cases): the same kernels.

No counterexample. The four theorems are proved in Lean at `b52cd65` (`#print axioms`: `propext`,
`Classical.choice`, `Quot.sound` only).

Verdict for the two definitions and the four theorems: **SAME** as Step 4 for these units (under the paper's
generic conditions, on any nonempty open set, with no condition on the number of units against the number of
coordinates).

### Check 3. The network statements for narrow blocks

The statements: `noSymmetricPart_mlp_rmsNorm_of_units` and `noSymmetricPart_gated_rmsNorm_of_units`
(Step 4 in the network: under `OneBlockGenericRMS θ`, resp. `OneBlockGenericGatedRMS θ`, `ε > 0`, a
differentiable activation and the units property, `NoSymmetricPart … θ Set.univ`), and the eight `ae_`
statements of Check 1. The values (SwiGLU):

```lean
    ∀ᵐ p ∂μ, funDimLearned (Arch.gated silu (rmsNorm ε) hid) p
        + (Fintype.card d * (Fintype.card d - 1) + Fintype.card (hid 0))
      = Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) silu (rmsNorm ε) hid) dIn dOut)
        + Fintype.card d ^ 2
```

**(a) The function (compiled, `rfl`).** `evalSkips A id (θ, S) x = χ(x E S_0 + f(χ(x E) W_read) W_write) D`
and `eval A 1 θ x` is the same with `S_0 = 1`: the paper's two networks of Appendix B.

**(b) The comparison at the same weights (by reading and compiling).** The paper compares two generic values.
Its proof (Step 5) compares at the same weights of the block: "`K(θ)` is spanned by the directions `η^rot`
and `K_B`, as for the residual network with its single rotation, and for generic parameters of the block
`K_B` has the same dimension in both networks." The Lean form "at almost every `(θ, A)`: `funDimLearned(θ, A)
= funDim` of the residual network at `θ`, plus `d(d+1)/2`" is this. The form of
`OneBlock/LearnedSkipKinds.lean` ("at almost every `(θ, A)` and almost every `θ′`") follows from it and
the value of the residual network: compiled for tanh at any width, from
`ae_funDimLearned_tanh_rmsNorm_of_nonempty` and `ae_funDim_tanh_oneBlock_residual_rmsNorm`. Conversely the
second form and the residual value at almost every `θ` give the first. The two forms agree. **SAME.**

**(c) The value and the equality condition (by reading).** Definition 4.3: "its symmetries are its only
redundancy". The network with a full learned skip has `P + d²` parameters (`P` counts the weights without
the skip: `Module.finrank ℝ (Params …)`), and its symmetries are the orthogonal changes of basis at `h_0`
and at `h_1`, with `A ↦ Q_0⁻¹ A Q_1` (the paper, Step 5: "For a full `A` they have dimension
`d_model (d_model − 1)`"), and those inside the block: none of positive dimension for tanh and GELU
(`s = 0`), the rescaling of the value of each hidden unit for SwiGLU and GeGLU (`s = d_hidden`). So the
equality condition is `P + d² − d(d−1) − s`, which is what the Lean value statements say (in the additive
form `funDimLearned + d(d−1) [+ d_hidden] = P + d²`). It is consistent with the difference:
`(P + d² − d(d−1) − s) − (P − d(d−1)/2 − s) = d(d+1)/2`. **SAME.**

**(d) The sizes.** `d_in, d_out ≥ d ≥ 2` are the theorem's ("Let `d_model ≥ 2`, let the input and output
dimensions be at least `d_model`"); all inputs; no width, as in part (iii). `[Nonempty T]`: implicit.
`[Nonempty (hid 0)]`, at least one hidden unit, **is needed** (computation, `z26net.py none`, and the
reason): with no hidden unit both networks compute `N_ε(x E A) D`, resp. `N_ε(x E) D`; the first depends on
`E A` only, so its rank is that of the second. Computed: `d = 3`: learned 15, residual 15 (`P − d(d−1)/2 =
15`); `d = 2`: 7 and 7; `d = 3, d_in = 4`: 18 and 18. The difference is `0`, not `d(d+1)/2`, and the value is
not `P + d² − d(d−1)`. The paper's "one block" excludes this case.

**(e) New against old where both apply (compiled).** For width at least `d` and a hidden unit, the conclusion
of `ae_funDimLearned_tanh_rmsNorm_of_nonempty` is the conclusion of `ae_funDimLearned_tanh_rmsNorm`
(`OneBlock/LearnedSkipKinds.lean`) as a type (`rfl`); for SwiGLU the old statement has
`∑ ℓ : Fin 1, card (hid ℓ)` where the new one has `card (hid 0)`, equal by `simp`, and then the types are
the same (`rfl`). GELU and GeGLU are written with the same template (by reading). The new statements have
one hypothesis less (the width) and one more (`[Nonempty (hid 0)]`, implied by width at least `d ≥ 2`).

**(f) The ranks (computation, `z26net.py`, `z26net2.py`; own script; exact forward derivatives, 60 digits,
one token, `ε = 0.3`, a random skip `A`, the residual network at the same weights; two batches each).**

| block | `d`, `d_in`, `d_out` | hidden units | learned skip | residual, same weights | difference | `d(d+1)/2` |
|---|---|---|---|---|---|---|
| tanh | 3, 3, 3 | 1 | 27 = `P + d² − d(d−1)` | 21 | 6 | 6 |
| tanh | 3, 3, 3 | 2 | 33 | 27 | 6 | 6 |
| SwiGLU | 3, 3, 3 | 1 | 29 = `P + d² − d(d−1) − 1` | 23 | 6 | 6 |
| SwiGLU | 3, 3, 3 | 2 | 37 | 31 | 6 | 6 |
| GELU | 3, 3, 3 | 1; 2 | 27; 33 | 21; 27 | 6 | 6 |
| GeGLU | 3, 3, 3 | 1; 2 | 29; 37 | 23; 31 | 6 | 6 |
| tanh; SwiGLU | 2, 2, 2 | 1 | 14; 15 | 11; 12 | 3 | 3 |
| GeGLU | 2, 3, 2 | 1 | 17 | 14 | 3 | 3 |
| GELU | 2, 2, 3 | 1 | 16 | 13 | 3 | 3 |
| tanh; SwiGLU | 3, 4, 4 | 1 | 33; 35 | 27; 29 | 6 | 6 |
| tanh; SwiGLU | 3, 3, 3 | 3 (width `d`) | 39; 45 | 33; 39 | 6 | 6 |
| tanh | 3, 3, 3 | 4 | 45 | 39 | 6 | 6 |
| tanh | 4, 4, 4 | 1 | 44 | 34 | 10 | 10 |
| GeGLU | 4, 4, 4 | 2 | 58 | 48 | 10 | 10 |
| SwiGLU | 4, 4, 4 | 1 | 47 (with 30 and with 45 inputs) | 37 | 10 | 10 |

Every value is the stated one. The stated values are upper bounds by the count of symmetries, and a rank on
a batch is a lower bound, so where they meet the value is exact. One caution, recorded as it happened: for
SwiGLU with `d = 4` and one hidden unit a batch of 20 inputs (80 rows for 60 parameters) gave rank 45, two
below the stated 47, in two independent batches; with 30 and with 45 inputs the rank is 47. A block with one
hidden unit sees its input through two numbers only, and a batch that looks large enough can still be too
small. The answer to the question of the brief: with `d = 3` and one or two hidden units the difference is
`6` for tanh and for SwiGLU.

Verdict: the ten statements of the two files are **SAME** as Theorem B.1 (iii), `ε > 0`, for these four
kinds of block with a full learned skip (PART of the theorem: not the upper triangular skip, not the other
kinds of block, not `ε = 0`). Not false; no drift.

### Check 4. Lemma B.2 (`OneBlock/KeepsProducts.lean`)

```lean
theorem keeps_products_and_ED_iff_mem_range_cobDir (θ η : Params A dIn dOut)
    (hE : θ.E.rank = Fintype.card d) (hD : θ.D.rank = Fintype.card d)
    (hr : (θ.read 0).rank = Fintype.card d) (hw : (θ.write 0).rank = Fintype.card d) :
    (η.E * θ.read 0 + θ.E * η.read 0 = 0 ∧ η.write 0 * θ.D + θ.write 0 * η.D = 0
        ∧ η.E * θ.D + θ.E * η.D = 0)
      ↔ ∃ X : Matrix d d ℝ, η = cobDir θ ![X, X]

theorem finrank_span_keeps_products … :
    Module.finrank ℝ (Submodule.span ℝ {η : Params A dIn dOut |
        η.E * θ.read 0 + θ.E * η.read 0 = 0 ∧ η.write 0 * θ.D + θ.write 0 * η.D = 0})
      = 2 * Fintype.card d ^ 2

theorem finrank_span_keeps_products_and_ED … :
    Module.finrank ℝ (Submodule.span ℝ {η | … ∧ … ∧ η.E * θ.D + θ.E * η.D = 0}) = Fintype.card d ^ 2
```

- **The derivatives (by reading).** `D_θ C η = η_E W_read + E η_read`, `D_θ A η = η_write D + W_write η_D`,
  `D_θ M η = η_E D + E η_D`: the three equations of the Lean statements, as in the paper's proof.
- **`cobDir θ ![X, Y]` (compiled, `rfl`).** Its entries are `E X`, `−(X W_read)`, `W_write Y`, `−(Y D)`:
  the paper's "`η_E = E X`, `η_read = −X W_read`, `η_write = W_write Y`, `η_D = −Y D`". With `![X, X]`:
  "if and only if moreover `X = Y`". The first equivalence is `keeps_products_iff_mem_range_cobDir`
  (compared in earlier audits). **SAME.**
- **The dimensions.** The set of the directions that keep `C` and `A` (and `M`) is the set of solutions of
  linear equations in `η`, so it is a subspace whatever the ranks are (compiled: closed under `η + c • η′`),
  and its span is itself. So "the dimension of the span" is "these directions form a space of dimension
  `2 d_model²` without the skip and `d_model²` with it". **SAME.**
- **The hypotheses.** The four ranks `d` are the lemma's ("Let `E`, `D`, `W_read` and `W_write` have rank
  `d_model`"). Needed (exact computation, `z26b2.py`, `d = 2`; "keep `C`, `A`" / "keep `C`, `A`, `M`",
  against `2d² = 8` / `d² = 4`):

  | case | keep `C`, `A` | keep `C`, `A`, `M` |
  |---|---|---|
  | all four ranks `d` (two shapes, one with the read of a gated block) | 8 | 4 |
  | `E = 0`, a block wider than `d` | 10 | 10 |
  | `D = 0`, a block wider than `d` | 10 | 10 |
  | `W_read = 0`, `d_in > d` | 10 | 4 |
  | `W_write = 0`, `d_out > d` | 10 | 4 |
  | `W_read = 0`, `d_in = d` | 8 | 4 |
  | `W_write = 0`, `d_out = d` | 8 | 4 |
  | one hidden unit (read and write of rank 1), `d_in = d_out = d` | 8 | 4 |
  | one hidden unit, `d_in, d_out > d` | 10 | 4 |

  So for the dimension `2d²` each of the four ranks is needed in general (the first four failing rows),
  although the ranks of `W_read` and `W_write` are not needed when `E` and `D` are square. For the second
  equivalence and for the dimension `d²` the ranks of `E` and `D` are needed, and those of `W_read` and
  `W_write` are **not** (reason: `D` has a right inverse `R′`, so `η_E D + E η_D = 0` gives `η_E = E X` with
  `X = −η_D R′`; then `E (X D + η_D) = 0` gives `η_D = −X D`, and the equations for `C` and `A` give
  `η_read = −X W_read` and `η_write = W_write X` by cancelling `E` and `D`). Lean keeps the lemma's four
  hypotheses in all three statements: not a difference with the paper.
- **Any block.** The three statements are about the four matrices only; `A : Arch T d 1` supplies the shapes
  (compiled: an instance for a gated block and `T = ℕ`). Right for any block. For a block narrower than `d`
  the hypotheses `hr`, `hw` cannot hold, so the statements say nothing there (see the table: the count `2d²`
  is then true only for square `E` and `D`).

Verdict: **SAME** (the three statements; PART of the lemma: the clauses with biases are not stated, as the
file says).

### Check 5. Proposition A.9 for writes (`Residual/ExactReductionWrites.lean`)

```lean
theorem exists_cob_residual_write_eq_one (hA : A.χ = id) (ℓ : Fin L) (ρ : d → A.w ℓ)
    (hρ : IsUnit ((θ.write ℓ).submatrix ρ id).det) :
    ∃ G : GL d ℝ,
      (∀ x : Matrix T dIn ℝ, eval A 1 (θ.cob (fun _ => G) (fun _ => G)) x = eval A 1 θ x) ∧
      ((θ.cob (fun _ => G) (fun _ => G)).write ℓ).submatrix ρ id = 1

theorem exists_cob_residual_write_lowerTriangular [LinearOrder d] (ε : ℝ)
    (hA : A.χ = rmsNorm ε) (ℓ : Fin L) (ρ : d → A.w ℓ) :
    ∃ Q : GL d ℝ, (Q : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ ∧
      (∀ x : Matrix T dIn ℝ, eval A 1 (θ.cob (fun _ => Q) (fun _ => Q)) x = eval A 1 θ x) ∧
      ((((θ.cob (fun _ => Q) (fun _ => Q)).write ℓ).submatrix ρ id)ᵀ).BlockTriangular id

theorem exists_cob_writes_lowerTriangular [LinearOrder d] (ε : ℝ) (hA : A.χ = rmsNorm ε)
    (ρE : d → dIn) (ρ : ∀ ℓ : Fin L, d → A.w ℓ) :
    ∃ Q : Fin (L + 1) → GL d ℝ,
      (∀ ℓ, (Q ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ) ∧
      (∀ x : Matrix T dIn ℝ, eval A 0 (θ.cob Q Q) x = eval A 0 θ x) ∧
      (((θ.cob Q Q).E.submatrix ρE id)ᵀ).BlockTriangular id ∧
      ∀ ℓ, ((((θ.cob Q Q).write ℓ).submatrix (ρ ℓ) id)ᵀ).BlockTriangular id
```

(and the twins `exists_cob_residual_E_eq_one`, `exists_cob_residual_E_lowerTriangular` for the rows `ρE` of
the embedding).

- **The map (compiled, `rfl`).** `θ.cob (fun _ => G) (fun _ => G)` has `E G`, `G⁻¹ W_read^ℓ`,
  `W_write^ℓ G`, `G⁻¹ D`: "the map `W ↦ W G` on the matrices that write `h_ℓ` and `W ↦ G⁻¹ W` on those that
  read it […] with one `G` at all hidden states". In the skipless statement `θ.cob Q Q` has `E Q_0`,
  `W_write^ℓ Q_{ℓ+1}` and `Q_ℓ⁻¹ W_read^ℓ` (Lean counts blocks from `0`): each write is multiplied by the
  matrix of the hidden state it writes.
- **`G = W_1⁻¹` for a write (by reading).** The hypothesis `hρ` is "the chosen rows are invertible" (the
  paper: "Let `W_1` be an invertible `d_model × d_model` submatrix formed […] by `d_model` rows of a matrix
  that writes it"); the conclusion "the chosen rows of the new write are the identity" is "`W_1 G = I` for
  `G = W_1⁻¹`". `ρ : d → A.w ℓ` is any map; `hρ` forces it to be injective. **SAME.**
- **The triangular matrix (compiled).** `(Mᵀ).BlockTriangular id ↔ ∀ i j, i < j → M i j = 0`: the new rows
  are lower triangular. The paper's proof: "For a write, let `W_1ᵀ = Q T` be a QR factorization; then
  `W_1 = Tᵀ Qᵀ`, and `G = Q` gives `W_1 Q = Tᵀ`, which is lower triangular." So "a triangular matrix" in the
  statement of (i) is, for a write, lower triangular, as Lean says. `Q` is orthogonal in Lean (the paper:
  `G = O(d_model)` under RMSNorm). **SAME.**
- **Every real `ε`, no invertibility (by reading and compiling).** The paper states the triangular clause
  "Under RMSNorm with `ε > 0`" and for an invertible `W_1`. Lean states it for every real `ε` (an instance
  at `ε = −1` compiles; `ε = 0` is the paper's RMSNorm without `ε`, where orthogonal changes of basis also
  preserve the function; a negative `ε` has no meaning in the paper, and the statement is true there because
  `rmsNorm ε` is a total function that commutes with orthogonal matrices) and for any `d` chosen rows,
  invertible or not, repeated or not (a QR factorization exists for every square matrix). Right, and
  **LEAN STRONGER**; nothing in it contradicts the paper.
- **The embedding as a write (by reading).** Definition 3.1: "the writes into the hidden state `h_ℓ` are
  `W_write^ℓ`, or `E` if `ℓ = 0`". So the rows of `E` are "rows of a matrix that writes" `h_0`: the paper's
  reading.
- **`exists_cob_writes_lowerTriangular` against (i) (by reading).** `eval A 0` is the skipless network.
  Orthogonal `Q_0, …, Q_L`, one per hidden state, preserve the function and make the chosen rows of `E` (at
  `h_0`) and of every write (at `h_{ℓ+1}`) lower triangular: (i) "Done at every hidden state", with the
  submatrix of every hidden state taken from the write into it. **PART** of (i): the paper allows at each
  hidden state a read or a write (all reads at once is `Symmetry/Reduction.lean`; a mixture is not stated),
  networks of mixed blocks and the count of removed parameters are not stated, as the file says.

Verdict: `…_eq_one` (2): **SAME**. `…_lowerTriangular` (3): **LEAN STRONGER** (every `ε`, no invertibility);
the skipless one is **PART** of (i).

### Check 6. Lemma A.18, the readout form (`Dimension/UpperBoundReadout.lean`)

```lean
theorem cobDir_injective_of_rank_D (θ : Params A dIn dOut) (hD : θ.D.rank = Fintype.card d)
    (hr : ∀ ℓ, (θ.read ℓ).rank = Fintype.card d) :
    Function.Injective (cobDir θ)
```

- **The hypotheses (by reading and compiling).** The paper: "The same holds if the readout has rank
  `d_model` and every block has width at least `d_model`", at generic parameters; its proof: "The second
  statement follows by the mirror induction from the readout, `D ↦ G_L⁻¹ D` […] each read, of rank
  `d_model` and with generic columns, then forces `G_{ℓ−1} = I`". So "every read of rank `d`" is the
  condition the proof uses, and it is what width at least `d` gives generically. Compiled: for `d_out ≥ d`
  and every read with at least `d` columns, at almost every `θ` (any Haar measure), `cobDir θ` is injective,
  from `ae_isUnit_det_submatrix` (`Generic/Params.lean`) and this theorem. For an MLP block the read has
  `d_hidden` columns; for a gated block `2 d_hidden`, so the Lean condition is weaker than the paper's width
  there.
- **The conclusion (by reading).** `cobDir θ X` is the direction in which the changes of basis `I + τ X_ℓ`
  move `θ`; its injectivity says that no nonzero `X` fixes `θ` to first order, the infinitesimal form of
  "act locally freely" ("no continuous family of them, other than the identity, fixes `θ`"), exactly as its
  twin `cobDir_injective` does for the first sentence. `X_L` is read off `−X_L D`, and `X_ℓ`, `ℓ < L`, off
  the read of the block that reads `h_ℓ`: the paper's mirror induction, without the induction (with no
  rescalings in play each read gives its `X_ℓ` directly).
- **Not stated in this file**: the symmetries inside blocks (rescalings; for ReGLU the paper notes that a
  row of the write fixes only the product of the two scales); the statement on the group; attention. At
  `baf38e7` and `b52cd65` the header of the file said so; at `95e12a2` it points to files written after this
  audit began (`Dimension/UpperBoundReadoutInside.lean`, `Symmetry/LocallyFreeEmbedding.lean`,
  `Symmetry/LocallyFreeReadout.lean`), which this audit did not read.
  For a residual network (one `X` at all hidden states) the injectivity of `X ↦ cobDir θ (fun _ => X)`
  follows from this theorem, and needs `D` only.

Verdict: **SAME** for the piece it states; **PART** of the lemma.

### Check 7. The index rows and the registrations

By reading, at `95e12a2` (line numbers of `STATEMENTS.md` there), with counts by `grep`.

- **Every public theorem is in a row and in `checks/Axioms.lean`.** The seven files have 2 public
  definitions and 23 public theorems (listed in Part 2). Each of the 23 names occurs once in the index and
  once as `#print axioms Skips.<name>` in `checks/Axioms.lean`; the two definitions are in their rows. The
  seven modules are imported by `SkipsLean.lean`. In the audit's own compile, `#print axioms` gives
  `propext`, `Classical.choice`, `Quot.sound` for all 23, and `sorryAx` for none. The status "proved" of the
  seven rows is true at `b52cd65` and `95e12a2` (at `baf38e7` the two gated files were in work).
- **Line 422, `Dimension/UpperBoundReadout.lean`:** true of the statement.
- **Line 524, `OneBlock/KeepsProducts.lean`:** true of the three statements.
- **Line 734, `Residual/ExactReductionWrites.lean`:** true of the five statements. One clause is shorter
  than the statement: for the skipless network the row says that the changes of basis "turn the chosen rows
  […] into lower triangular matrices"; the theorem also says that they preserve the function.
- **Line 977, `OneBlock/UnitsNoSymmetricPart.lean`:** the sentence on the statement is true; "24 cases" is
  the count of the script named (2 activations, 6 sizes, 2 seeds). Its last words, "Not stated: SwiGLU and
  GeGLU units; the networks", are **out of date**: both are stated, in the rows of lines 979 and 978, 980.
- **Line 978, `OneBlock/LearnedSkipNarrowMlp.lean`:** true of the five statements. "Not stated here: SwiGLU
  and GeGLU blocks narrower than `d`; the upper triangular skip for narrow blocks" is true of this file, but
  both are now stated elsewhere (lines 980 and 981); the header of the file has the same sentence.
- **Line 979, `OneBlock/GatedUnitsNoSymmetricPart.lean`:** true; "12 cases" is the count of the script
  named.
- **Line 980, `OneBlock/LearnedSkipNarrowGated.lean`:** true of the five statements. "Not stated here: the
  upper triangular skip for narrow blocks": now stated in the row of line 981; the header of the file has
  the same sentence.
- Outside the seven rows, found while reading: the rows of lines 932 (`OneBlock/LearnedSkipKinds.lean`) and
  933 (`OneBlock/LearnedSkipTriangular.lean`) end with "Not stated: tanh, GELU, SwiGLU, GeGLU blocks
  narrower than `d` […]"; these blocks are now stated (lines 978, 980, 981). The header of
  `OneBlock/LearnedSkipKinds.lean` says the same.

Verdict: no sentence of the seven rows is false of its statements; four "not stated" notes are out of date
(corrections below).

## Part 2: the statements, file by file

| declaration | file | paper sentence | verdict |
|---|---|---|---|
| `UnitsNoSymmetricPart` (definition) | `OneBlock/UnitsNoSymmetricPart.lean` | S, proof of Theorem B.1 (iii), Step 4: "`∂_ψ B(n) = q(n) 𝐃B(n) n` (17) for every `n` in the image of `N_ε` […] In every case `q` vanishes on an open set for generic parameters, so `X_s = 0`", for units `σ(n c_i) a_i` | SAME (note 1) |
| `tanh_unitsNoSymmetricPart` | same | "For tanh the right side is `4 t³ q(n̂) ∑_i (n̂ c_i) e^{−2|n̂ c_i| t} a_i` […] so `q(n̂)(n̂ c_j) a_j = 0`" | SAME (note 1) |
| `gelu_unitsNoSymmetricPart` | same | "For GELU the right side is `t³ q(n̂) max(n̂ W_read, 0) W_write` […] so `q(n̂) max(n̂ W_read, 0) W_write = 0`" | SAME (note 1) |
| `noSymmetricPart_mlp_rmsNorm_of_units` | `OneBlock/LearnedSkipNarrowMlp.lean` | Step 4, in the network: "The change `n X_s` of the input moves the block as the entries `X_s W_read` at `W_read` do […] We show that `q = 0`, hence `X_s = 0`" | SAME |
| `ae_funDimLearned_tanh_rmsNorm_eq_residual_add_of_nonempty` | same | Theorem B.1 (iii): "For generic parameters and `ε > 0`, its functional dimension exceeds that of the residual network of part (ii) by exactly `d_model (d_model + 1)/2`" | SAME; PART (tanh, full skip) (note 2) |
| `ae_funDimLearned_tanh_rmsNorm_of_nonempty` | same | "and it satisfies the equality condition" | SAME; PART (note 3) |
| `ae_funDimLearned_gelu_rmsNorm_eq_residual_add_of_nonempty` | same | as for tanh | SAME; PART (GELU, full skip) |
| `ae_funDimLearned_gelu_rmsNorm_of_nonempty` | same | as for tanh | SAME; PART |
| `GatedUnitsNoSymmetricPart` (definition) | `OneBlock/GatedUnitsNoSymmetricPart.lean` | Step 4, equation (17), for units `σ(n c_i)(n e_i) a_i` | SAME (note 4) |
| `silu_gatedUnitsNoSymmetricPart` | same | "SwiGLU and GeGLU units `σ(n c_i)(n e_i) a_i` give `2 t⁴ q(n̂) ∑_{i: n̂ c_i > 0} (n̂ c_i)(n̂ e_i) a_i` against a polynomial of degree two" | SAME (note 4) |
| `gelu_gatedUnitsNoSymmetricPart` | same | the same sentence, GeGLU | SAME (note 4) |
| `noSymmetricPart_gated_rmsNorm_of_units` | `OneBlock/LearnedSkipNarrowGated.lean` | Step 4, in the network, for a gated block | SAME |
| `ae_funDimLearned_swiglu_rmsNorm_eq_residual_add_of_nonempty` | same | Theorem B.1 (iii), "exceeds […] by exactly `d_model (d_model + 1)/2`" | SAME; PART (SwiGLU, full skip) (note 2) |
| `ae_funDimLearned_swiglu_rmsNorm_of_nonempty` | same | "and it satisfies the equality condition" (`s = d_hidden`) | SAME; PART (note 3) |
| `ae_funDimLearned_geglu_rmsNorm_eq_residual_add_of_nonempty` | same | as for SwiGLU | SAME; PART (GeGLU, full skip) |
| `ae_funDimLearned_geglu_rmsNorm_of_nonempty` | same | as for SwiGLU | SAME; PART |
| `keeps_products_and_ED_iff_mem_range_cobDir` | `OneBlock/KeepsProducts.lean` | Lemma B.2: "and it keeps `M` fixed as well, `D_θ M η = 0`, if and only if moreover `X = Y`" | SAME (note 5) |
| `finrank_span_keeps_products` | same | "these directions form a space of dimension `2 d_model²` without the skip" | SAME (note 5) |
| `finrank_span_keeps_products_and_ED` | same | "and `d_model²` with it" | SAME (note 5) |
| `exists_cob_residual_write_eq_one` | `Residual/ExactReductionWrites.lean` | Proposition A.9 (ii): "the same map with one `G` at all hidden states preserves the function and turns one such submatrix, in any read or write of the network, into the identity", with (i): "for `G = W_1⁻¹` if it is part of a write" | SAME |
| `exists_cob_residual_E_eq_one` | same | the same for the embedding, the write into `h_0` (Definition 3.1) | SAME |
| `exists_cob_residual_write_lowerTriangular` | same | (ii) "[…] or a triangular matrix", with (i): "Under RMSNorm with `ε > 0`, `G = Q` from a QR factorization […] `W_1ᵀ = Q T` for a write, turns `W_1` into a triangular matrix" | LEAN STRONGER (note 6) |
| `exists_cob_residual_E_lowerTriangular` | same | the same for the embedding | LEAN STRONGER (note 6) |
| `exists_cob_writes_lowerTriangular` | same | (i): "In a skipless network […] Under RMSNorm with `ε > 0` […] turns `W_1` into a triangular matrix. Done at every hidden state" | LEAN STRONGER in `ε` and invertibility; PART of (i) (note 7) |
| `cobDir_injective_of_rank_D` | `Dimension/UpperBoundReadout.lean` | Lemma A.18: "The same holds if the readout has rank `d_model` and every block has width at least `d_model`" | SAME for the changes of basis in infinitesimal form; PART (note 8) |

Notes.

1. The three declarations for tanh and GELU units. Lean states the step for all units that satisfy the
   paper's generic conditions (nonzero `a_i`; nonzero, pairwise non-collinear `c_i`; at least one unit), on
   any nonempty open set of rows, with the numbers of coordinates, of outputs and of units independent. The
   conclusion `X = 0` is the paper's "`q` vanishes on an open set […] so `X_s = 0`" (`X` is `X_s / d_model`).
2. The difference is stated at the same weights `θ` for the two networks; this is the comparison made in
   Step 5 of the paper's proof, and it agrees with the comparison between two generic values (Check 3 (b)).
3. "The equality condition" is read as the value `P + d² − d(d−1) − s`, with `P + d²` parameters, the two
   orthogonal changes of basis (`d(d−1)`) and `s = 0` (tanh, GELU) or `s = d_hidden` (SwiGLU, GeGLU). The
   statements ask at least one hidden unit, which is needed (Check 3 (d)), and no width.
4. The gated definition does not ask that the value column `e_i` is not proportional to the gate column
   `c_i`; the paper lists this among its generic conditions, and Step 4 does not need it (Check 2 (c)).
5. Lean keeps the four rank hypotheses of the lemma in all three statements. The second equivalence and the
   dimension `d²` need only the ranks of `E` and `D`; the dimension `2d²` needs all four in general
   (Check 4).
6. The paper: `ε > 0` and an invertible `W_1`. Lean: every real `ε`, any `d` chosen rows. "Lower triangular"
   is what the paper's proof gets for a write.
7. One submatrix per hidden state, each taken from the write into that hidden state (the embedding for
   `h_0`). Not stated: a read at some hidden states and a write at others; networks of mixed blocks; the
   count `d_model (d_model − 1)/2` of removed parameters per hidden state.
8. Hypotheses: `D` and every read of rank `d`, which is what the paper's proof uses ("each read, of rank
   `d_model`") and what width at least `d` gives at almost every parameter (compiled).

## What the authors of the papers should know

Nothing in the seven files is false, vacuous, drifted or misdescribed. All 23 public theorems are proved at
`b52cd65` with the three standard axioms.

Places where the paper's statement or proof needs a condition or a step that it does not write, or writes a
condition that is not needed:

1. **Theorem B.1 (iii), `ε > 0`, holds for blocks narrower than `d_model`** (tanh, GELU, SwiGLU, GeGLU with
   a full learned skip): proved in Lean with no condition on the width, and confirmed here by ranks at 60
   digits for one and two hidden units with `d = 2, 3, 4`. The theorem as printed has no width condition in
   part (iii), so this agrees with it. The only condition is the trivial one that the block has a hidden
   unit: with none, the network with a learned skip computes `N_ε(x E A) D`, and the difference to the
   residual network is `0` (computed).
2. **Step 4, gated units: "not proportional to its gate weights" is not needed there.** The proof's list of
   generic conditions (line 2407 of the text) asks that the value weights of a gated unit are not
   proportional to its gate weights. Step 4 of part (iii) holds without it (Lean does not ask it; computed
   with `e_i` parallel to `c_i`): the term `(n̂ X n̂ᵀ) ∑_{n̂ c_i > 0} (n̂ c_i)(n̂ e_i) a_i` is then a sum of
   squares `r_i (n̂ c_i)²` on half-spaces, which still does not vanish identically.
3. **Step 4: "`q` vanishes on an open set for generic parameters" uses exactly that the units do not
   cancel.** With two units `c_2 = c_1`, `a_2 = −a_1` (the block is `0`), every symmetric `X_s` satisfies
   (17) with `ψ = 0`, for all four activations; for tanh also `c_2 = −c_1`, `a_2 = a_1`. Such parameters are
   not generic, so the paper's sentence is right; the non-collinearity of the columns of `W_read` is the
   condition that excludes them, and it holds generically because `d_model ≥ 2`, at any width.
4. **Lemma B.2: the ranks of `W_read` and `W_write` are not used by the clause on `M`.** The directions that
   keep `C`, `A` and `M` are the `d_model²` directions of one change of basis as soon as `E` and `D` have
   rank `d_model` (argument in Check 4; exact computation with `W_read = 0`, with `W_write = 0`, and with a
   block of one hidden unit). The count `2 d_model²` without the skip does need all four ranks in general:
   for a block narrower than `d_model` with `d_in > d_model` or `d_out > d_model` it is larger (10 against 8
   for `d = 2`, `d_in = d_out = 3`, one hidden unit), and for square `E` and `D` it holds at any width. The
   lemma as printed, with its four hypotheses, is correct.
5. **Proposition A.9, the triangular form under RMSNorm:** it holds for `ε = 0` as well, and without the
   invertibility of `W_1` (a QR factorization exists for every square matrix). The printed statement, with
   `ε > 0` and an invertible `W_1`, is a special case. For a write the triangular matrix is lower triangular
   (the proof says so; the statement says "a triangular matrix").
6. **A caution for numerical ranks with narrow blocks** (not about the paper's text): for SwiGLU with
   `d_model = 4` and one hidden unit, 20 random inputs (80 output coordinates for 60 parameters) gave a
   Jacobian of rank 45, and 30 inputs gave the true 47. A count "more rows than parameters" is not enough
   for a block that sees its input through few numbers.

## Corrections for `STATEMENTS.md` (line numbers at `95e12a2`)

1. Line 977 (`OneBlock/UnitsNoSymmetricPart.lean`): replace "Not stated: SwiGLU and GeGLU units; the
   networks" by a pointer: SwiGLU and GeGLU units are the row of `OneBlock/GatedUnitsNoSymmetricPart.lean`;
   the networks are the rows of `OneBlock/LearnedSkipNarrowMlp.lean` and `OneBlock/LearnedSkipNarrowGated.lean`.
2. Line 978 (`OneBlock/LearnedSkipNarrowMlp.lean`): "Not stated here: SwiGLU and GeGLU blocks narrower than
   `d`; the upper triangular skip for narrow blocks": add that they are the rows of
   `OneBlock/LearnedSkipNarrowGated.lean` and `OneBlock/LearnedSkipTriangularNarrow.lean`. The same sentence
   is in the header of the Lean file.
3. Line 980 (`OneBlock/LearnedSkipNarrowGated.lean`): "Not stated here: the upper triangular skip for narrow
   blocks": add the pointer to `OneBlock/LearnedSkipTriangularNarrow.lean`. The same sentence is in the
   header of the Lean file.
4. Lines 932 and 933 (`OneBlock/LearnedSkipKinds.lean`, `OneBlock/LearnedSkipTriangular.lean`; not among the
   seven rows): "Not stated: tanh, GELU, SwiGLU, GeGLU blocks narrower than `d` […]" is out of date; these
   blocks are stated in the rows of lines 978, 980 and 981. The header of `OneBlock/LearnedSkipKinds.lean`
   ("Not stated here: […] blocks narrower than `d`") can point to them too.
5. Line 734 (`Residual/ExactReductionWrites.lean`): in the clause on the skipless network, add "preserve the
   function and" before "turn the chosen rows".
6. Optional, line 979 (`OneBlock/GatedUnitsNoSymmetricPart.lean`): say that the statement does not ask the
   paper's condition "the value is not proportional to the gate", and that it is not needed.
7. Optional, line 524 (`OneBlock/KeepsProducts.lean`): say that the set of directions is a subspace (so the
   span is the set), as the header of the file does.

No correction for line 422 (`Dimension/UpperBoundReadout.lean`).

## What was not checked

- The proofs (the audit is of statements), beyond `#print axioms` on the build of the working copy.
- The statements at dimensions larger than those computed: Step 4 on vectors up to 4 coordinates and 5
  units; network ranks up to `d = 4` and 4 hidden units; one value of `ε` (`0.3`) and one token.
- `OneBlock/LearnedSkipTriangularNarrow.lean` and the files written after the audit began
  (`Dimension/UpperBoundReadoutInside.lean`, `Symmetry/LocallyFreeEmbedding.lean`,
  `Symmetry/LocallyFreeReadout.lean`, `Symmetry/LocallyFreeAttention.lean`,
  `Dimension/RescaleActionHomogeneous.lean`, `Basic/EigenvectorsGeneralPosition.lean`): not in the subject.
- Whether the build that the copies were compiled against is byte for byte the build of `b52cd65`: the
  compiled files of the seven modules are newer than the last change of their sources, and the statements
  used in the checks elaborate against them; a full rebuild was not run (not allowed here).
- The clauses of Lemma B.2 with biases, networks of mixed blocks in Proposition A.9, and the group form of
  Lemma A.18: not stated in the seven files, so nothing to compare.
- The coordinator's two scripts were read (their systems of equations are the same as in the audit's own
  script) and not run.
