STATUS: complete

# Twenty-fifth audit of Lean statements against the papers: S Theorem B.1 (iv), the skipless equality for a ReLU block of width at least `d_model` (24 November 2026)

Reader: an independent reader who did not write the statements. Briefs:
`audit25_brief_2026-11-24.md`, with the rules of `audit21a_brief_2026-11-24.md`. I audited
statements and definitions, not proofs. I changed no repository file, ran no `lake build`, made no
commit and no push. My files are in `/home/claude/audit25/`.

**This is the second run of this audit.** A first run was interrupted before it wrote any finding.
It left scripts and outputs in `/home/claude/audit25/`. I read every script before using it and
ran them again (all but two seeds of one random search: see the last section); at each check I say
which result is taken over from the first run and which is new in this run.

**Result in short.** Nothing false, vacuous or drifted in the 12 public theorems and 2
definitions. The four statements at almost every parameter are for every Haar measure on the
weights. `UnitsParallelAt` is the conclusion of `UnitsParallel` word for word. The ReLU theorem on
units is true in 72 exact sets with more units than coordinates; of its five hypotheses `ha` is
needed, `hkink` is needed only through the case of one unit, `hcc` follows from `hkink`, and `hne`
and `hrank` were not needed in any computed set. `UnitsGeneralPosition` is the paper's "for
generic parameters" for `k = 1`, stronger than the paper needs in its clauses 3 and 4; its fourth
clause was not needed for the value at 42 computed parameters. The statements at one parameter
give back the three width-`d` statements (compiled); their rank hypothesis forces width at least
`d`. The rank of the skipless network equals the count at 12 computed parameters. Against the
paper the coverage is PART: ReLU² blocks wider than `d` are not stated.

Library: `/home/claude/lp/lean` (branch `lean-plus`).

- **Commit read: `baf38e79e89000cab24e31a860db335adf1d7988` (25 November 2026, 00:19:01 UTC),** the
  head when I started. The four files of this audit were last changed before it
  (`OneBlock/UnitsParallelAt.lean` at `4db4e7f`, 00:00:30; `OneBlock/SkiplessHomogeneousRMSZeroEqAt.lean`
  at `aab47f8`, 23:44:49; `OneBlock/UnitsGeneralPosition.lean` at `610b439`, 23:58:35;
  `OneBlock/SkiplessReluWideRMSZero.lean` at `526b1d4`, 23:52:24).
- **`sorry`:** none of the four files has a `sorry` at this commit. In `lean/SkipsLean` two files
  have one (`git grep -lw sorry`): `OneBlock/GatedUnitsNoSymmetricPart.lean` and
  `OneBlock/LearnedSkipNarrowGated.lean`, not of this audit.
- The four files have 12 public theorems (2 + 3 + 3 + 4) and two public definitions
  (`UnitsParallelAt`, `UnitsGeneralPosition`). All 12 depend on `propext`, `Classical.choice`,
  `Quot.sound` only (`#print axioms` in `Chk25.lean`, compiled with `lake env lean` against the build
  of `/home/claude/lp/lean`, whose object files of the four modules are newer than the last change of
  the sources; first run, compiled again in this run with the same output).
- The head of the branch moved while I worked: **`95e12a2f10fd37410763c2dafdb803a8957ce544`
  (00:42:01 UTC) when I finished.** The four files, `OneBlock/UnitsParallel.lean` and
  `Dimension/Functional.lean` are the same at both commits (`git diff` is empty), and so is the
  text of the four index rows (lines 949 to 952 of `STATEMENTS.md` at `baf38e7`, lines 962 to 965
  at `95e12a2`, by checksum). Line numbers of `STATEMENTS.md` below are those of `95e12a2`.

Paper, as text: the skips paper ("S", `<scratchpad>/skips.txt`): Theorem B.1 at lines 2319 to 2343,
part (iv) at lines 2338 to 2343; the proof of part (iv) at lines 2891 to 2959.


How each check was made is said in its first line: **reading**, **compiling** (a copy in
`/home/claude/audit25/`, nothing written in the repository) or **computation** (`python3 -I`, exact
rational arithmetic unless said otherwise).

## Part 1: checks

### Check 1. Generic means almost every parameter, for every Haar measure: SAME

By reading and by compiling (`Chk25.lean`: taken over from the first run, read, compiled again).

The four `ae_` statements are `ae_unitsGeneralPosition`,
`ae_funDim_relu_oneBlock_skipless_rmsNorm_zero_of_le`,
`ae_exists_jacobianRank_relu_oneBlock_skipless_rmsNorm_zero_of_le` and
`ae_funDim_relu_oneBlock_residual_rmsNorm_zero_eq_add_of_le`. Each has the form

```lean
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) … : ∀ᵐ θ ∂μ, …
```

(`σ` arbitrary in place of `relu` in the first). So: every Haar measure on the space of all the
weights `(E, W_read, W_write, D)`, and the property at almost every parameter. None of the four
says "there is a parameter" or "on an open set".

- `Fintype`: the file declares `[Fintype T] [Fintype d] [Fintype dIn] [Fintype dOut]` and
  `[∀ ℓ, Fintype (hid ℓ)]`. The weights are indexed by `dIn × d`, `d × hid 0`, `hid 0 × d`,
  `d × dOut`: all finite. `ae_unitsGeneralPosition` omits `[Fintype T]` and `[Nonempty T]`; `T`
  indexes the tokens and no weight, so nothing is lost.
- Concrete Haar measure: five instances at `Measure.addHaar` compile, with numbers. ReLU, one
  token, `d = d_in = d_out = 2`, width 3: general position at almost every parameter, and
  `funDim = 11` (`P = 20`, count `4 + 2 + 3 = 9`). ReLU, two tokens, `d = 3`, `d_in = 4`,
  `d_out = 3`, width 5: general position; a batch of the paper's inputs of rank `33` (`P = 51`,
  count `9 + 4 + 5 = 18`); `funDim` with the skip `= funDim` without it `+ 9`.

### Check 2. `UnitsParallelAt` and `relu_unitsParallelAt_of_generic`

**(a) `UnitsParallelAt` is the conclusion of `UnitsParallel` at given units: SAME, word for word.**
By reading and by compiling. The two definitions:

```lean
def UnitsParallel (σ σ' : ℝ → ℝ) (k : ℕ) (n m q : Type*) [Fintype n] [Fintype m] [Fintype q] : Prop :=
  ∀ (c : q → n → ℝ) (a : q → m → ℝ) (ψc : q → n → ℝ) (β : q → m → ℝ),
    LinearIndependent ℝ c → LinearIndependent ℝ a → 2 ≤ Fintype.card q →
    (∀ x : n → ℝ, (∀ i, x ⬝ᵥ c i ≠ 0) → ∑ i, σ (x ⬝ᵥ c i) • a i ≠ 0 →
      ∃ μ : ℝ, ∑ i, (σ (x ⬝ᵥ c i) • β i + (σ' (x ⬝ᵥ c i) * (x ⬝ᵥ ψc i)) • a i)
        = μ • ∑ i, σ (x ⬝ᵥ c i) • a i) →
    ∃ (c₀ : ℝ) (lam : q → ℝ), ∀ i, ψc i = lam i • c i ∧ β i = (c₀ - (k : ℝ) * lam i) • a i

def UnitsParallelAt (σ σ' : ℝ → ℝ) (k : ℕ) {n m q : Type*} [Fintype n] [Fintype m] [Fintype q]
    (c : q → n → ℝ) (a : q → m → ℝ) : Prop :=
  ∀ (ψc : q → n → ℝ) (β : q → m → ℝ),
    (∀ x : n → ℝ, (∀ i, x ⬝ᵥ c i ≠ 0) → ∑ i, σ (x ⬝ᵥ c i) • a i ≠ 0 →
      ∃ μ : ℝ, ∑ i, (σ (x ⬝ᵥ c i) • β i + (σ' (x ⬝ᵥ c i) * (x ⬝ᵥ ψc i)) • a i)
        = μ • ∑ i, σ (x ⬝ᵥ c i) • a i) →
    ∃ (c₀ : ℝ) (lam : q → ℝ), ∀ i, ψc i = lam i • c i ∧ β i = (c₀ - (k : ℝ) * lam i) • a i
```

The premise on `(ψc, β)` and the conclusion are the same text. Compiled
(`unitsParallel_iff25`): `UnitsParallel σ σ' k n m q` holds if and only if
`UnitsParallelAt σ σ' k c a` holds for all linearly independent `c`, linearly independent `a` and
at least two units. `unitsParallelAt_of_unitsParallel` is one direction of this.

**(b) The five hypotheses of the ReLU theorem against the paper.** By reading.

```lean
theorem relu_unitsParallelAt_of_generic {n m q : Type*} [Fintype n] [Fintype m] [Fintype q]
    (c : q → n → ℝ) (a : q → m → ℝ)
    (hcc : ∀ i j, i ≠ j → ∀ r : ℝ, c i ≠ r • c j) (ha : ∀ i, a i ≠ 0)
    (hne : ∀ x : n → ℝ, (∃ i, 0 < x ⬝ᵥ c i) → ∑ i, relu (x ⬝ᵥ c i) • a i ≠ 0)
    (hkink : ∀ i, ∃ x₀ : n → ℝ, x₀ ⬝ᵥ c i = 0 ∧ (∀ j, j ≠ i → x₀ ⬝ᵥ c j ≠ 0) ∧
      ∀ r : ℝ, ∑ j, relu (x₀ ⬝ᵥ c j) • a j ≠ r • a i)
    (hrank : ∀ x : n → ℝ, (∀ i, x ⬝ᵥ c i ≠ 0) →
      (∃ i j, i ≠ j ∧ 0 < x ⬝ᵥ c i ∧ 0 < x ⬝ᵥ c j) →
      ∃ y : n → ℝ, ∀ r : ℝ, ∑ i, (reluDeriv (x ⬝ᵥ c i) * (y ⬝ᵥ c i)) • a i
        ≠ r • ∑ i, relu (x ⬝ᵥ c i) • a i) :
    UnitsParallelAt relu reluDeriv 1 c a
```

| Hypothesis | Paper | Verdict |
|---|---|---|
| `hcc`: for `i ≠ j` and every real `r`, `c_i ≠ r c_j` | "the `c_i` are pairwise non-collinear" | SAME. `r = 0` gives `c_i ≠ 0`, `r < 0` excludes opposite columns, `r > 0` equal directions. The paper uses the word twice: for "any two of them meet" only opposite columns must be excluded (two open half-spaces are disjoint exactly when `c_i = −t c_j`, `t > 0`); for "a point `x_0` with `x_0 c_i = 0`, on no other hyperplane" every multiple must be excluded. So every real multiple is the paper's meaning. |
| `ha`: `a_i ≠ 0` | not written in this paragraph | SAME as what the proof uses: "the left side [jumps] by `(x_0 ψc_i) a_i`; both jumps vanish. […] `x_0 ψc_i = 0`" needs `a_i ≠ 0`. For generic parameters it follows from the paper's "the rows `a_i`, `i ∈ S`, are linearly independent" with one unit in `S`. |
| `hne`: `h_1(x) ≠ 0` at every `x` with an active unit | "for generic parameters `h_1 ≠ 0` there" (on `Ω`, "the set `Ω` of inputs at which some unit is active") | SAME. The paper's `Ω` contains the points of a kink at which another unit is active, and "`μ` is continuous on `Ω`" is the continuity of `⟨J, h_1⟩/‖h_1‖²`, which needs `h_1 ≠ 0` at these points too. The Lean set `{x : ∃ i, 0 < x c_i}` is `Ω`. |
| `hkink`: for every `i` ONE point `x_0` of the hyperplane of `i`, on no other hyperplane, with `h_1(x_0) ∉ ℝ a_i` | "Fix a unit `i` and a point `x_0` with `x_0 c_i = 0`, on no other hyperplane `x c_j = 0`, at which another unit is active. For generic parameters and `x_0` in an open dense set of such points, `h_1(x_0)` is not parallel to `a_i`" | LEAN WEAKER as a hypothesis (so the theorem is stronger): one point in place of an open dense set. One point is what the paper's step uses ("`x_0 ψc_i = 0` on an open subset of the hyperplane"): `h_1` is continuous and "not a multiple of `a_i`" is an open condition, so one point gives an open piece of the hyperplane. "At which another unit is active" is not written in Lean and follows: `r = 0` gives `h_1(x_0) ≠ 0`. |
| `hrank`: at every `x` off the kinks with two active units, a `y` with `∑_{i active at x} (y c_i) a_i ∉ ℝ h_1(x)` | "On a region where at least two units are active, the entries of `J` and of `h_1` are homogeneous polynomials of degree `k` in `x`, and for generic parameters two entries `h_a` and `h_b` of `h_1` have no common factor" | SAME for `k = 1`. On a region with active set `S`, `h_1(x) = x M_S` with `M_S = ∑_{i∈S} c_i a_i`; two linear forms have no common factor exactly when they are linearly independent, so the paper's clause is `rank M_S ≥ 2`. The Lean clause, asked at every `x` of the region, is also `rank M_S ≥ 2` (if the rank is 0 it fails everywhere; if it is 1, it fails at every `x` of the region with `x M_S ≠ 0`; if the rank is at least 2, a `y` exists at every `x`). |

Two remarks on the statement as a whole, by compiling (`Chk25.lean`, `Chk25b.lean`):

- `hkink` implies `hcc` (`hcc_of_hkink25`: if `c_i = r c_j`, the point `x_0` of unit `j` lies on
  the hyperplane of `i`). So `hcc` is a redundant hypothesis: harmless.
- With one unit `hkink` cannot hold (`not_hkink_one_unit25`: the output on its hyperplane is `0`).
  So the theorem speaks of at least two units (or of none), like `UnitsParallel`; and
  `UnitsParallelAt relu reluDeriv 1 c a` is false for one unit whenever some vector is not a
  multiple of `c` (`not_unitsParallelAt_one_unit25`).

**(c) Is the theorem true? Yes in all 72 sets computed (and it is proved).** By computation
(`check2_truth.py` with `units_tools.py`: scripts of the first run, written for this audit and not
the coordinator's; I read them line by line, ran them again, the output is the same).

Random integer columns `c_i ∈ [−6, 6]^n` and rows `a_i ∈ [−6, 6]^m` with MORE units than
coordinates, kept when the five hypotheses hold (each decided exactly on the cells of the
arrangement of the hyperplanes `x c_i = 0`). For `(n, m) = (2, 2), (3, 3), (3, 2), (2, 3)` and
`q = n + 1, n + 2, n + 3`, six sets each: 72 sets. The space of directions `(ψc, β)` that keep
`J` parallel to `h_1` on every region is computed twice: from the polynomial identity
`(x N_S)_a (x M_S)_b = (x N_S)_b (x M_S)_a` on every region (the regions are enumerated exactly;
their number agrees with Zaslavsky's formula in every case), and from 400 random rational
points. **In all 72 sets both give dimension `q + 1`, the dimension of the family of the
conclusion** (`c₀` and the `λ_i`). The coordinator's script
`units_parallel_wide_check_2026-11-24.py` I did not run; its saved output has 24 lines, all "ok".

**(d) Which hypotheses are needed.** By computation (random search `check2_needed.py`, seeds 11,
12 and, tabulated by the number of units, 21, 12000 draws each, and the designed families of
`check2_designed.py`: first run, read, seed 11 and the designed families run again with the same
output; the designed families of `run2_needed.py`: this run) and by compiling.
"More solutions" means: the exact dimension of the solutions is larger than the dimension of the
family of the conclusion, so `UnitsParallelAt` is false at these units.

| Hypothesis | Needed? | Evidence |
|---|---|---|
| `ha` | **Needed.** | Compiled for every activation (`not_unitsParallelAt_of_zero_row25`): if `a_i = 0` and some `e` is not a multiple of `c_i`, the direction `ψc_i = e`, all else `0`, has derivative `0` and is not in the family. Computed: `n = m = 2`, `q = 5`, `C = [(1,−3), (3,3), (3,2), (3,−2), (−2,−3)]`, `A = [(1,2), (1,−3), (0,2), (0,0), (1,0)]` violates `ha` alone and has 7 solutions against 6; every set that violates `ha` alone has more solutions (2 + 9 + 12 sets in the three seeds). |
| `hkink` | **Needed, by an example with ONE unit; not needed in any set with three or more units.** | One unit, `n = 2`: `c = (3, −3)`, `a = (0, −3)` violates `hkink` alone (the other four hold: `hcc` and `hrank` are empty, `a ≠ 0`, `h_1 = (x c) a ≠ 0` where the unit is active) and has 3 solutions against 2: `ψc = (1, 0)`, `β = 0` gives `J = (x ψc / x c) h_1`. Compiled for every `n`, `m` (`not_unitsParallelAt_one_unit25`). With two units `hkink` cannot fail alone (then the two rows are parallel and `hrank` fails too). With three to six units: 50 sets of the random search (seed 21, `n = 2`) and 543 + 266 designed sets (`n = m = 2`, four to six units, `h_1` parallel to `a_0` at BOTH rays of the kink of unit 0, at least two other units active at each ray, in about half of the 266 with `h_1(−x_0) = −h_1(x_0)`) violate `hkink` alone, and **none has more solutions**. The reason in these sets: where the regions on the two sides of a kink have `rank M_S ≥ 2`, `μ` is constant on each, and the difference of the two identities `N_S = μ M_S` pins `ψc_i` and `β_i` without the jump argument. |
| `hne` | **Not needed in any set computed.** | For `n = 2` it cannot fail alone: with `ha`, `hcc` and `hrank`, a zero of `h_1` at a point with an active unit gives a region with at least two active units and `rank M_S ≤ 1` (by reading; in the searches every set with `n = 2` that violates `hne` violates `hrank`). For `n = 3`: 135 + 101 + 122 sets of the random search and 285 + 295 designed sets (`h_1 = 0` at an interior point of a region with at least three active units; `h_1 = 0` at a point of a kink with at least three other active units), plus 37 that arose by chance, violate `hne` alone; none has more solutions. The reason in these sets: the premise of `UnitsParallelAt` is asked only where `h_1 ≠ 0`, and on a region with `rank M_S ≥ 2` it still forces `N_S = μ M_S` with one number `μ`; the zeros of `h_1` lie on a line in the region. |
| `hrank` | **Not needed in any set computed.** | 579 + 559 + 586 sets of the random search and 308 (`n = 2`) + 179 (`n = 3`) designed sets (a region with exactly two active units whose rows are parallel) violate `hrank` alone; none has more solutions. In these sets the neighbouring regions of rank at least 2 determine the direction on the region of rank 1. I did not find a proof that this always happens. |
| `hcc` | **Not needed as a hypothesis:** it follows from `hkink` (compiled, above). | In the three seeds no set violates `hcc` without `hkink`. |

So the statement is true and none of its hypotheses makes it empty, and three of the five
(`hcc`, `hne`, `hrank`) could not be shown to be needed: the theorem has room. This does not
touch the statements at almost every parameter, where all five hold.

A defect of my own script, for the record: in the first pass of `run2_needed.py` the family "two
parallel rows" multiplied the two coordinates by different factors, so its rows were not parallel
(output kept as `run2_needed_firstpass_BCD_valid_A_buggy.out`; the families B, C, D of that pass
are right and are the numbers above). I corrected it and ran the family again
(`run2_needed_A.out`: the 308 and 179 sets above).

### Check 3. `UnitsGeneralPosition`

```lean
def UnitsGeneralPosition {d q : Type*} [Fintype d] [DecidableEq d] (Wr : Matrix d q ℝ)
    (Ww : Matrix q d ℝ) : Prop :=
  (∀ i j, i ≠ j → ∀ r : ℝ, Wrᵀ i ≠ r • Wrᵀ j) ∧
  (∀ S : Finset q, S.card ≤ Fintype.card d → LinearIndependent ℝ fun i : S => Ww i) ∧
  (∀ S : Finset q, Fintype.card d ≤ S.card →
    IsUnit (∑ i ∈ S, Matrix.vecMulVec (Wrᵀ i) (Ww i)).det) ∧
  ∀ (i : q) (S : Finset q), i ∉ S → Fintype.card d ≤ S.card →
    (Ww i ᵥ* (∑ j ∈ S, Matrix.vecMulVec (Wrᵀ j) (Ww j))⁻¹) ⬝ᵥ Wrᵀ i ≠ 0
```

**(a) The four clauses against the paper.** By reading. `Wrᵀ i` is the column `w_i` of `W_read`,
`Ww i` the row `a_i` of `W_write`, `vecMulVec (Wrᵀ i) (Ww i)` the `d × d` matrix `w_i a_i`
(column times row), and the sum over all units is `W_read W_write` (compiled,
`sum_vecMulVec_univ25`).

| Clause | Paper | Verdict |
|---|---|---|
| 1: the columns `w_i` pairwise non-collinear (every real multiple excluded) | "the `c_i` are pairwise non-collinear", `c_i = E w_i` | SAME for `E` of rank `d`: `u ↦ E u` is then injective, so the `c_i` are pairwise non-collinear exactly when the `w_i` are. |
| 2: any at most `d` rows `a_i` are linearly independent | "If `\|S\| < d_model`, the rows `a_i`, `i ∈ S`, are linearly independent" | LEAN STRONGER by the case `\|S\| = d`, which adds nothing: for `\|S\| = d` it follows from clause 3 (`M_S` invertible gives the `d` rows independent). |
| 3: `M_S = ∑_{i∈S} w_i a_i` invertible for EVERY set `S` of at least `d` units | "If `\|S\| ≥ d_model` and `k = 1`, `h_1 = x E ∑_{i∈S} w_i a_i`, and this `d_model × d_model` matrix is invertible", for `S` "the set of units active at `x`" | LEAN STRONGER as a condition: every set of units, not only the sets of units that are active at some input. Finitely many polynomial conditions either way. |
| 4: `(a_i M_S⁻¹) · w_i ≠ 0` for every unit `i` and every set `S` of at least `d` units with `i ∉ S` | "For generic parameters and `x_0` in an open dense set of such points, `h_1(x_0)` is not parallel to `a_i`" | LEAN STRONGER as a condition (see (b)). |

"Two entries `h_a` and `h_b` of `h_1` have no common factor" (`k = 1`) has no clause of its own
and needs none: on a region with at least two active units, `rank M_S ≥ 2` follows from clauses 1
and 2 if fewer than `d` units are active, and from clause 3 and `d ≥ 2` otherwise.

**(b) Clause 4.** By reading and by computation.

- What it says: for `u ≠ 0` with `u · w_i = 0`, `u M_S` is not a multiple of `a_i` (if
  `u M_S = r a_i` then `u = r a_i M_S⁻¹`, so `0 = u · w_i = r (a_i M_S⁻¹) · w_i`, so `r = 0` and
  `u = 0`). So at NO point of the hyperplane of unit `i` at which the units of `S` are active is
  `h_1` parallel to `a_i`.
- Is it what "`h_1(x_0)` is not parallel to `a_i`" needs when at least `d` units are active at
  `x_0`? **For `d = 2`, yes, and it is then a condition on the weights:** `h_1` depends on `x`
  through `u = x E`, the hyperplane of unit `i` is the line `u · w_i = 0` of the plane, and on each
  of its two rays `h_1` is parallel to `a_i` at every point or at none. The paper's sentence covers
  this with "for generic parameters"; the words "`x_0` in an open dense set" do nothing for
  `d_model = 2`. **For `d ≥ 3` the paper's sentence needs no condition on the weights** when at
  least `d` units are active: the points `u` of the hyperplane with `u M_S` parallel to `a_i` lie
  on one line. So clause 4 asks more than the paper in three ways: for `d ≥ 3` at all; for every
  set `S` and not only the sets active at a point of the hyperplane; and at every point, where
  `hkink` needs one point per unit. When fewer than `d` units are active at `x_0`, clause 2 does
  the work (the rows `a_j`, `j ∈ S`, and `a_i` are at most `d` rows).
- Is it needed? **Not in any parameter computed.** `d = 2`, clauses 1 to 3 hold and clause 4
  fails: 24 parameters of widths 3, 4, 5 (`check3_gp.py`, part (c): first run, run again, same
  output) and 12 parameters of widths 5 and 6 in which clause 4 fails for unit 0 at BOTH rays of
  its kink with at least two other units active at each (`run2_clause4.py`, family (E): this run;
  `hkink` is then violated, alone). **In all 36 the exact rank of the skipless network on inputs
  from every pattern of active units equals `P − d² − (d(d−1)/2 + 1) − s`,** and the units
  equation has exactly the `q + 1` solutions of the family. `d = 3`, widths 4 and 5, clause 4
  failing at one pair `(i, S)` with `S` the units active at a point of the hyperplane of `i`
  (family (F), 6 parameters): the five hypotheses of check 2 all hold, and the rank equals the
  count. So clause 4 is a sufficient condition that the proof uses; the value does not depend on
  it in these parameters.

**(c) Do the four clauses imply the five hypotheses of check 2?** By reading the statement and by
computation.

```lean
theorem relu_unitsParallelAt_of_unitsGeneralPosition (E : Matrix dIn d ℝ) {Wr : Matrix d q ℝ}
    {Ww : Matrix q d ℝ} (hd : 2 ≤ Fintype.card d) (hq : Fintype.card d ≤ Fintype.card q)
    (hE : E.rank = Fintype.card d) (hG : UnitsGeneralPosition Wr Ww) :
    UnitsParallelAt relu reluDeriv 1 (fun i => (E * Wr)ᵀ i) (fun i => Ww i)
```

The statement gives `UnitsParallelAt` at the columns of `E W_read` and the rows of `W_write`
directly. The implication to the five hypotheses, tested (`check3_gp.py`, parts (a), (b): first
run, run again, same output): random integer `W_read`, `W_write` in `[−6, 6]` that meet the four
clauses (decided exactly over all subsets `S`), with a random `E` of rank `d`, for `d = 2` with
widths 2 to 5 and `d = 3` with widths 3 to 6, `d_in = d` and `d + 1`: **12 parameters for each of
the 16 cases, 192 in all; the five hypotheses hold at all 192.** `hd` is needed: for `d = 1` and
two units clause 1 is false at every parameter (two numbers are always collinear). Some lower bound on the number of units
is needed: with one unit `UnitsParallelAt` is false (check 2).

**(d) Satisfiable, and at almost every parameter?** By computation and by compiling. Of random
integer weights in `[−6, 6]`, between 12 of 47 (`d = 2`, width 5) and 12 of 13 (`d = 3`, width 3)
meet the four clauses, so they are satisfiable together for every `d` and width tried.

```lean
theorem ae_unitsGeneralPosition {σ : ℝ → ℝ}
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d)
    (hcard : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ θ ∂μ, UnitsGeneralPosition (θ.read 0) (θ.write 0)
```

For every `d ≥ 2`, every width at least `d`, every activation, every `d_in`, `d_out` and every
Haar measure (two instances at `Measure.addHaar` compile, check 1). `d ≥ 2` is needed (above).
The width at least `d` is not needed for this statement to be true (for a narrower block clauses
3 and 4 are empty and clauses 1 and 2 hold at almost every parameter: by reading, not compiled);
it is the width of the theorem, so nothing is lost.

**Verdict for check 3:** the definition is the paper's "for generic parameters" of this proof for
`k = 1`, made explicit, and somewhat stronger than the paper needs in clauses 3 and 4; as it holds
at almost every parameter, the statements at almost every parameter are the paper's.

### Check 4. The statements at one parameter for any width (`OneBlock/SkiplessHomogeneousRMSZeroEqAt.lean`)

By reading and by compiling (`Chk25.lean`, first run, compiled again; `Chk25c.lean`, this run).

The three statements share these hypotheses (the second and third have `hc` in addition; the
first has `η` and `hη`):

```lean
    (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (hhom : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
    (hd : 2 ≤ Fintype.card d)
    (hE : θ.E.rank = Fintype.card d) (hD : θ.D.rank = Fintype.card d)
    (hR : (θ.read 0).rank = Fintype.card d) (hW : (θ.write 0).rank = Fintype.card d)
    (hc : ∀ i, (fun a => θ.read 0 a i) ≠ 0)
    (hP : UnitsParallelAt σ σ' k (fun i => (θ.E * θ.read 0)ᵀ i) (fun i => θ.write 0 i))
    (hO : ∃ O : Set (d → ℝ), IsOpen O ∧ O.Nonempty ∧ ∀ v ∈ O, ∃ x : dIn → ℝ,
      (∀ i, x ⬝ᵥ (θ.E * θ.read 0)ᵀ i ≠ 0) ∧
        ∑ i, σ (x ⬝ᵥ (θ.E * θ.read 0)ᵀ i) • θ.write 0 i = v)
```

- **Against the twins of `OneBlock/SkiplessHomogeneousRMSZeroEq.lean`: the same conclusions,
  word for word.** The twins have `(hk : k ≠ 0) (hσ1 : σ 1 ≠ 0)`,
  `(hP : UnitsParallel σ σ' k dIn d (hid 0))` and
  `(hcard : Fintype.card (hid 0) = Fintype.card d)`; the new statements have `hP` at the units of
  `θ`, `hO` and (two of them) `hc` instead. Compiled: an `example` in which the three twins prove
  the conjunction of the three conclusions as they stand in the new file; and `twin_flat25`,
  `twin_funDim25`, `twin_batch25`: **the three twins follow from the three new statements**, with
  `UnitsParallelAt` from `unitsParallelAt_of_unitsParallel` (the columns of `E W_read` and the
  rows of `W_write` are linearly independent when the width is `d` and the ranks are `d`), `hc`
  from `hR` and the width, and the open set `hO` taken as a hypothesis, as the brief allows. So
  nothing of the width-`d` statements is lost except that `hO` is there proved from `k ≠ 0` and
  `σ(1) ≠ 0`.
- **`(fun i => (θ.E * θ.read 0)ᵀ i)` are the columns `c_i` of `C = E W_read`, as vectors of
  `ℝ^{d_in}`, and `(fun i => θ.write 0 i)` the rows `a_i` of `W_write`:** the paper's "with `c_i`
  the columns of `C = E W_read` and `a_i` the rows of `W_write`". SAME.
- **Is `hO` the paper's "since `h_1` takes all values in an open set"? SAME in substance.** The
  paper: "`ηD = −Y D` with `Y` antisymmetric, since `h_1` takes all values in an open set", with
  `h_1 = B(xE) = ∑_i σ(x c_i) a_i` (the block on the unnormalized row; the normalizations change
  it by a positive factor). Lean: a nonempty open set `O ⊆ ℝ^d` every point of which is
  `∑_i σ(x c_i) a_i` for a row `x` at which no unit sits at its kink. The restriction to rows off
  the kinks is not in the paper's sentence; the paper's inputs are those at which no hidden unit
  sits at its kink, so it is the paper's meaning.
- **"No condition on the width" is true of the text and not of the content:** `hR` (a `d × q`
  matrix of rank `d`) gives `q ≥ d` (compiled, `width_ge_of_rank_read25`). So the three statements
  are for blocks of width at least `d`, which is the width of the theorem; "any width" in the
  header and in the index row should read "any width at least `d`" (correction 2 below).
- **Satisfiable together.** Compiled (`ae_hypotheses25`): for ReLU, `d ≥ 2` and width at least
  `d`, at almost every `θ` with `E` of rank `d` the hypotheses `hR`, `hW`, `hc`, `hP` and `hO`
  all hold (from the three statements of `UnitsGeneralPosition.lean`); `hE`, `hD` hold at almost
  every `θ` for `d_in, d_out ≥ d`. One parameter, exactly: `d = d_in = d_out = 2`, three ReLU
  units, `E = [[4,−3],[5,−3]]`, `W_read = [[1,5,−2],[2,−1,−2]]`, `W_write = [[4,1],[2,5],[−2,1]]`,
  `D = [[5,4],[2,0]]`: the four clauses of `UnitsGeneralPosition` and the five hypotheses of
  check 2 hold (exact), `det E = 3`, `det D = −8`, the units equation has `4 = q + 1` solutions,
  a region has both `d` units active (the open set), and the rank of the network there is
  `11 = 20 − 9` (check 5, first line of the table).
- **The count.** `Fintype.card d ^ 2 + (Fintype.card d * (Fintype.card d - 1) / 2 + 1) +
  Fintype.card (hid 0)` is the paper's "`dim K(θ) = d_model² + d_model (d_model − 1)/2 + 1 + s`"
  with `s` the number of hidden units (the paper: "the rescaling of a hidden unit of a ReLU or
  ReLU² block"; "`s` the total dimension of the symmetries inside the blocks"). The division is
  exact in `ℕ` (`d(d−1)` is even) and the statement is written as `funDim + count = P`, so no
  truncated subtraction. SAME.
- I did not test whether `hO` is needed beside the other hypotheses (no parameter found that
  violates `hO` alone).

**Verdict for check 4:** the three statements are the three width-`d` statements with the two
uses of the width turned into hypotheses on the parameter; none is vacuous.

### Check 5. The statements for ReLU of width at least `d` (`OneBlock/SkiplessReluWideRMSZero.lean`)

By reading, by compiling (check 1) and by computation (`check5_rank.py` with `net_tools.py`:
first run, read line by line, run again with the same output; 33 seconds).

```lean
theorem ae_funDim_relu_oneBlock_skipless_rmsNorm_zero_of_le
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hcard : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ θ ∂μ, funDim (Arch.mlp relu (rmsNorm 0) hid) 0 θ
        + (Fintype.card d ^ 2 + (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
          + Fintype.card (hid 0))
      = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut)
```

`ae_exists_jacobianRank_relu_oneBlock_skipless_rmsNorm_zero_of_le` has the same hypotheses and the
conclusion `∀ᵐ θ ∂μ, ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i, X i ∈ skiplessZeroDomain … θ ∩
noKinkRMS θ) ∧ jacobianRank … 0 X θ + (the same count) = finrank`;
`ae_funDim_relu_oneBlock_residual_rmsNorm_zero_eq_add_of_le` has the same hypotheses and the
conclusion `∀ᵐ θ ∂μ, funDim … 1 θ = funDim … 0 θ + Fintype.card d ^ 2`.

- **The sizes: SAME.** The paper: "Let `d_model ≥ 2`, let the input and output dimensions be at
  least `d_model`"; "(iv) Let the network be pre-RMSNorm with `ε = 0`, without biases, with a
  ReLU, ReLU² or ReGLU block of width at least `d_model`". Lean: `hd`, `hdIn`, `hdOut`, `hcard`,
  `rmsNorm 0`, no biases in `Arch.mlp`, one block (`hid : Fin 1 → Type`), any number of tokens
  (`[Nonempty T]`). No further hypothesis.
- **Which functional dimension.** Lean's `funDim A S θ` is the largest rank of the Jacobian over
  all finite batches of all inputs (Mathlib's derivative is `0` where the output is not
  differentiable in the weights). The second statement gives a finite batch of inputs of
  `skiplessZeroDomain ∩ noKinkRMS θ` (no row of `x E` is zero, no row of the output of the block
  is zero, no entry of `x E W_read` is zero: the paper's inputs, "no normalized row vanishes and
  no hidden unit sits at its kink") whose rank is `P − count`. Every batch has rank at most
  `funDim = P − count` (`jacobianRank_le_funDim` and the first statement), in particular every
  batch of the paper's inputs. **So
  the two together say: the largest rank over batches of the paper's inputs is
  `P − d² − d(d−1)/2 − 1 − s`, the paper's functional dimension of the skipless network.**
- **The last statement** compares Lean's `funDim` with the identity skip (`1`) and without a skip
  (`0`). Each side is the paper's value by its own pair of statements: the residual side by
  `ae_funDim_relu_oneBlock_residual_rmsNorm_zero` with
  `ae_exists_jacobianRank_relu_oneBlock_residual_rmsNorm_zero`
  (`OneBlock/ResidualRMSZeroRescaleGeneric.lean`, twenty-first audit, part A: a batch in
  `residualZeroDomain ∩ noKinkRMS θ`), the skipless side by the two statements above. With these
  four, "the skip raises the functional dimension by exactly `d_model²`" holds in the paper's own
  sense; the statement alone says it for Lean's `funDim`.
- **Coverage: PART.** The paper claims equality "for ReLU and ReLU² blocks" of width at least
  `d_model`. Lean has ReLU of width at least `d` (this file) and ReLU² of width exactly `d`
  (`OneBlock/SkiplessHomogeneousRMSZeroEq.lean`). ReLU² wider than `d` is not stated; the file
  and the index row say so.
- **Computation.** For integer weights in `[−5, 5]` that meet the four clauses, with `E`, `D` of
  rank `d`, the Jacobian of the skipless network is computed exactly on at least six rational
  inputs from EVERY pattern of active units that occurs (the patterns are enumerated exactly),
  one token per input. The formula used,
  `dy = (√d/‖h̃‖) [(dh̃ − h̃ ⟨h̃, dh̃⟩/‖h̃‖²) D + h̃ dD]` with `h̃ = relu(x E W_read) W_write`, is
  checked at two inputs per parameter against central differences of the literal composition
  `N_0(relu(N_0(xE) W_read) W_write) D` at 60 digits (largest relative error `1.4·10⁻³⁷`).

| `d` | width | `d_in`, `d_out` | `P` | count | `P −` count | rank (2 parameters) | inputs | patterns |
|---|---|---|---|---|---|---|---|---|
| 2 | 3 | 2, 2 | 20 | 9 | 11 | 11, 11 | 36, 30 | 6, 5 |
| 2 | 5 | 2, 2 | 28 | 11 | 17 | 17, 17 | 54, 60 | 9, 10 |
| 3 | 4 | 3, 3 | 42 | 17 | 25 | 25, 25 | 78, 84 | 13, 14 |
| 3 | 7 | 3, 3 | 60 | 20 | 40 | 40, 40 | 258, 264 | 43, 44 |
| 2 | 3 | 3, 3 | 24 | 9 | 15 | 15, 15 | 30, 30 | 5, 5 |
| 3 | 4 | 4, 3 | 45 | 17 | 28 | 28, 28 | 78, 78 | 13, 13 |

  **The rank equals `P − d² − (d(d−1)/2 + 1) − s` at all 12 parameters** (the eight of the brief
  and four with `d_in > d`). A rank on a batch is a lower bound for the rank over all inputs; here
  the bound of `OneBlock/SkiplessHomogeneousRMSZero.lean` is the matching upper bound. At the same
  12 parameters the five hypotheses of check 2 hold and the units equation has `q + 1` solutions.
  A parameter that is not in general position (`check5_nongeneric.py`: `d = 2`, width 3, two
  columns of `W_read` collinear, clauses 1 and 3 fail): rank 10 against 11, and 5 solutions of the
  units equation against 4. So general position is not an empty word.

**Verdict for check 5:** SAME for ReLU of width at least `d`; PART of the paper's sentence (ReLU²
wider than `d` is missing).

### Check 6. The index rows

By reading (`STATEMENTS.md`, lines 962 to 965, and `checks/Axioms.lean`, lines 1802 to 1813).

- Every public name of the four files is in its row: `UnitsParallelAt`,
  `unitsParallelAt_of_unitsParallel`, `relu_unitsParallelAt_of_generic` (line 962); the three of
  `SkiplessHomogeneousRMSZeroEqAt.lean` (line 963); `UnitsGeneralPosition`,
  `rank_of_unitsGeneralPosition`, `relu_unitsParallelAt_of_unitsGeneralPosition`,
  `exists_open_relu_of_unitsGeneralPosition` (line 964); the four `ae_` statements (line 965). The
  12 theorems are in `checks/Axioms.lean`. The four rows say "proved": true (no `sorry`, standard
  axioms).
- Line 962: every clause is true of the statements. "where at least two units are active the
  linear map that `h_1` is there has rank at least two" is the content of `hrank` (check 2 (b)).
  The script it names exists and its saved output has 24 cases.
- Line 963: true, with the remark of check 4 on "no condition on the width".
- Line 964: true. "(the paper's "`x_0` in an open dense set" as a condition on the weights)" is
  right for `d = 2`; for `d ≥ 3` the clause asks more than the paper (check 3 (b)).
- Line 965: true. "at almost every parameter the hidden units are in general position (any
  activation)": `ae_unitsGeneralPosition` has `σ` arbitrary and needs neither `d_in ≥ d` nor
  `d_out ≥ d`.
- The paragraph at lines 278 to 284 lists the four files as "not yet compared by such a reader":
  to be updated with this report.

No computation of this audit took more than five minutes (the longest: 2 minutes 42 seconds, the
first pass of `run2_needed.py`).

## Part 2: the statements, file by file

| Lean name | Paper sentence (S, proof of Theorem B.1 (iv) unless said) | Verdict | Note |
|---|---|---|---|
| `UnitsParallelAt` (definition) | "so `ψc_i = λ_i c_i` for a number `λ_i`" and "Hence `μ = c` on `Ω` for one number `c`", as a property of given units `c`, `a` | SAME | The conclusion of `UnitsParallel`, word for word (compiled). It has no condition on the units, so it is false at some units (one unit; a zero row `a_i`): it is a hypothesis or a conclusion, never a fact about all units. |
| `unitsParallelAt_of_unitsParallel` | none (the link to the width-`d` property) | no paper sentence | One direction of the compiled equivalence of check 2 (a). |
| `relu_unitsParallelAt_of_generic` | "The kinks stay" and "One scale", `k = 1`, with the paper's generic conditions as five hypotheses on the units | LEAN STRONGER | One point per unit in place of an open dense set; any number of input coordinates and of output coordinates; any number of units (with one unit `hkink` cannot hold). True in 72 exact sets with more units than coordinates. `hcc` follows from `hkink`; `hne` and `hrank` were not needed in any computed set (check 2 (d)). |
| `flatOn_le_mlp_rescale_skipless_rmsNorm_zero_of_unitsParallelAt` | "Let `η` be flat […] `ηD = −Y D` with `Y` antisymmetric […] Counting. […] Lemma B.2 gives `ηE = EX` and `η_read = −X W_read`" | SAME | At one parameter, with the paper's "for generic parameters" as hypotheses (`hE`, `hD`, `hR`, `hW`, `hP`, `hO`). The conclusion is that of the width-`d` twin (twenty-second audit, part A). `hR` forces width at least `d`. |
| `funDim_mlp_oneBlock_rescale_skipless_rmsNorm_zero_of_unitsParallelAt` | "So `dim K(θ) = d_model² + d_model (d_model − 1)/2 + 1 + s`" | SAME | Lean's `funDim`; the paper's value together with the next statement. |
| `exists_jacobianRank_mlp_oneBlock_rescale_skipless_rmsNorm_zero_of_unitsParallelAt` | the same, on the paper's inputs | SAME | A finite batch in `skiplessZeroDomain ∩ noKinkRMS θ`. |
| `UnitsGeneralPosition` (definition) | "the `c_i` are pairwise non-collinear"; "If `\|S\| < d_model`, the rows `a_i`, `i ∈ S`, are linearly independent. If `\|S\| ≥ d_model` and `k = 1`, […] this `d_model × d_model` matrix is invertible"; "For generic parameters […] `h_1(x_0)` is not parallel to `a_i`" | LEAN STRONGER (as a condition) | Clause 3 for every set `S`; clause 4 for every `d`, every pair `(i, S)` and every point. It holds at almost every parameter, so the statements at almost every parameter are the paper's. Clause 4 was not needed for the value in 42 computed parameters. |
| `rank_of_unitsGeneralPosition` | none (`W_read`, `W_write` of rank `d`, no zero column: generic) | no paper sentence | For `d ≥ 2` and width at least `d`. |
| `relu_unitsParallelAt_of_unitsGeneralPosition` | "The kinks stay" and "One scale" for a ReLU block of width at least `d_model` at generic parameters | SAME (`k = 1`) | The four clauses gave the five hypotheses at all 192 computed parameters. |
| `exists_open_relu_of_unitsGeneralPosition` | "since `h_1` takes all values in an open set" | SAME (`k = 1`, width at least `d`) | Outputs at rows off the kinks. |
| `ae_unitsGeneralPosition` | "For generic parameters" (four times in the paragraph) | SAME | Almost every parameter, every Haar measure, any activation, `d ≥ 2`, width at least `d`. |
| `ae_funDim_relu_oneBlock_skipless_rmsNorm_zero_of_le` | Theorem B.1 (iv): "the skipless network at most `P − d_model² − d_model (d_model − 1)/2 − 1 − s`, with equality for ReLU and ReLU² blocks" | PART (ReLU; SAME for ReLU with the next statement) | ReLU² wider than `d` is not stated. |
| `ae_exists_jacobianRank_relu_oneBlock_skipless_rmsNorm_zero_of_le` | the same, on the paper's inputs | PART (ReLU; SAME for ReLU) | Rank equal to the count at 12 computed parameters. |
| `ae_funDim_relu_oneBlock_residual_rmsNorm_zero_eq_add_of_le` | Theorem B.1 (iv): "by exactly `d_model²` for ReLU and ReLU² blocks" | PART (ReLU; SAME for ReLU) | Lean's `funDim` on both sides; the paper's sense with the two batch statements (check 5). |

No statement is FALSE, DIFFERENT or vacuous.

## What the authors of the papers should know

Nothing false, vacuous, drifted or misdescribed was found. In the order of weight:

1. **Coverage.** Part (iv) claims the equality "for ReLU and ReLU² blocks" of width at least
   `d_model`. Lean now has it for ReLU of every width at least `d_model` and for ReLU² of width
   exactly `d_model`. The paper's argument for ReLU² wider than `d_model` (the resultant of
   `d_model` quadratic forms; two quadratic entries of `h_1` without a common factor; the jump of
   the derivative in `x` across a kink) is not formalized.
2. **"The kinks stay" for `d_model = 2`.** The sentence "For generic parameters and `x_0` in an
   open dense set of such points, `h_1(x_0)` is not parallel to `a_i`" is right, and for
   `d_model = 2` all of its content is in "for generic parameters": `h_1` depends on `x` through
   `xE`, the hyperplane of unit `i` is two rays in the plane of `xE`, and on each ray `h_1` is
   parallel to `a_i` at every point or at none. The condition on the weights is, for the set `S`
   of units active on the ray (at least `d_model` of them), `(a_i M_S⁻¹) · w_i ≠ 0` with
   `M_S = ∑_{j∈S} w_j a_j`; the paper does not write it. For `d_model ≥ 3` no such condition is
   needed, as the paper says.
3. **A condition the proof uses and does not write:** `a_i ≠ 0` ("both jumps vanish", then
   "`x_0 ψc_i = 0`"). It follows from the independence of the rows `a_i`, `i ∈ S`, for
   `|S| < d_model`, so nothing is wrong; without it the step is false (compiled).
4. **One point per kink is enough.** The step "`x_0 ψc_i = 0` on an open subset of the hyperplane"
   needs one point `x_0` with `h_1(x_0)` not parallel to `a_i` (the condition is open); "open
   dense" is more than is used.
5. **The generic conditions of this paragraph are sufficient and, in everything computed, not
   sharp.** In exact computations the conclusion of the two steps (`ψc_i = λ_i c_i` and one scale
   `c`) still held when `h_1` vanished at a point of `Ω` (975 sets with three input coordinates),
   when a region with two active units had `h_1` of rank one (2211 sets), and, with three or more
   units, when `h_1` was parallel to `a_i` on the whole kink of a unit (859 sets); and the rank of
   the network was the count at 42 parameters where `(a_i M_S⁻¹) · w_i = 0`. The conditions that
   were needed in computed sets: `a_i ≠ 0`, at least two units, and pairwise non-collinear
   columns (a parameter with two opposite columns of `W_read`: rank 10 against 11). This is
   information on the proof, not a defect of the theorem.
6. **"`Ω` is connected […] as the `c_i` are pairwise non-collinear":** for this sentence only
   opposite columns matter; the same words are needed in full ("a point `x_0` […] on no other
   hyperplane") in "The kinks stay". Lean reads them in full.

## Corrections for `STATEMENTS.md`

1. Lines 278 to 284 (at `95e12a2`): take `OneBlock/UnitsParallelAt.lean`,
   `OneBlock/SkiplessHomogeneousRMSZeroEqAt.lean`, `OneBlock/UnitsGeneralPosition.lean` and
   `OneBlock/SkiplessReluWideRMSZero.lean` out of the list "Not yet compared by such a reader" and
   add the result of this audit (12 public theorems and 2 definitions: none false, vacuous or
   drifted; the four statements at almost every parameter are for every Haar measure; ReLU² wider
   than `d` is not stated).
2. Row of `OneBlock/SkiplessHomogeneousRMSZeroEqAt.lean` (line 963): "for an MLP block of any
   width" and "with no condition on the width" are true of the list of hypotheses and not of
   their content: `W_read` of rank `d` gives width at least `d`. Suggested: "of any width at least
   `d` (the rank `d` of `W_read` gives it; the width is not otherwise used)". The same words are
   in the header of the Lean file.
3. Row of `OneBlock/UnitsParallelAt.lean` (line 962), optional: add that `hcc` (pairwise
   non-collinear columns) follows from the hypothesis on the hyperplanes, and that the theorem is
   for at least two units.
4. Row of `OneBlock/UnitsGeneralPosition.lean` (line 964), optional: "(the paper's "`x_0` in an
   open dense set" as a condition on the weights)" is exact for `d = 2`; for `d ≥ 3` the fourth
   clause asks more than the paper needs.

No sentence of the four rows is false.

## What I could not check

- The proofs (not my subject). That the 12 theorems are proved rests on the build of
  `/home/claude/lp/lean` and on `#print axioms` in my compiled copies.
- Whether `hne`, `hrank`, `hkink` (for three or more units) and clause 4 are ever needed: I found
  no set of units and no parameter where they are, and no proof that there is none. The searches
  are for `n, m ≤ 3`, at most six units, small integer entries.
- Whether `hO` is needed beside the other hypotheses of the statements at one parameter.
- ReLU² blocks wider than `d`: no Lean statement to compare; I computed nothing for them.
- The ranks of check 5 are for inputs of one token (the block and the normalization act on every
  token alone, so the Jacobian at an input of several tokens is the stack of those of its rows:
  by reading the definitions, not computed for two tokens).
- I did not run the coordinator's scripts `units_parallel_wide_check_2026-11-24.py` and
  `units_general_position_check_2026-11-24.py`; I read their saved outputs.
- I compared nothing with the dimension paper.

## Files of this audit (`/home/claude/audit25/`)

First run (read, and run again in this run with the same output): `Sig25.lean`, `Chk25.lean`,
`Chk25b.lean` (its output is of this run: the first run had not finished it), `units_tools.py`,
`net_tools.py`, `check3_tools.py`, `check2_truth.py`, `check2_needed.py` (seed 11 run again;
seeds 12 and 21 taken over), `check2_needed_byq.py` (taken over), `check2_designed.py`,
`check3_gp.py`, `check5_rank.py`, `check5_nongeneric.py`; reruns in `rerun/`. This run:
`Chk25c.lean`, `run2_needed.py` (outputs `run2_needed_firstpass_BCD_valid_A_buggy.out`,
`run2_needed_A.out`), `run2_clause4.py` (`run2_clause4.out`), `dbg1.py`.
