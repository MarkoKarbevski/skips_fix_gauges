STATUS: complete

# Eighth audit of Lean statements against the dimension paper, part B (24 November 2026)

Reader: an independent reader who did not write the statements. Brief:
`/home/claude/proj_up/audit8b_brief_2026-11-24.md`. I edited no repository file, ran no
`lake build`, made no commit and no push.

Subject: the case `ε = 0` of pre-RMSNorm (the paper's case (0)) for `tanh` blocks: Appendix D.6 of
the dimension paper up to Lemma D.18 and the parameter `θ*`, in ten Lean files.

## Commit, and the files with `sorry`

Library: `/home/claude/lw/lean` (branch `lean-wip`).

- Commit when I began: `3131776d4d62167354ef508efbc7a3bb83df8221` (24 November, 10:14:51 UTC).
- While I worked the branch moved twice.
  - To `04c187737eb6a396000129f649f927332402c956` (10:20:47 UTC): three files changed,
    `Depth/DomainZero.lean`, `Depth/DomainZeroConnected.lean`, `Depth/TanhZero.lean` (proofs
    written). None of the ten files of this audit changed (`git diff --quiet 3131776 04c1877` on
    each), and `STATEMENTS.md` did not change.
  - To `f1ffa79f7163f2c1149598547fe5a1346c747ec4` (10:27:19 UTC), the commit when I finished: `Depth/HiddenZero.lean`,
    `Depth/TanhPathBlock.lean`, `Depth/RegularZeroTanh.lean` (proofs written), `checks/Axioms.lean`
    and six status cells of `STATEMENTS.md` (lines 178 to 183, "in work" to "proved"). Of the ten files, eight did not
    change. In the other two the only removed lines are the two `sorry` (`git diff 04c1877
    f1ffa79`, lines beginning with `-`): **no statement, definition or docstring of the ten files
    changed between `3131776` and `f1ffa79`**, except that a line `omit [DecidableEq d] in` now
    stands before `exists_regularZero_tanh_path`, so that it no longer takes the instance
    `[DecidableEq d]` (same meaning).
  Line numbers of `STATEMENTS.md` below are the same at the three commits.

Files of `SkipsLean/` that contain `sorry` (by `grep`):

| Commit | Files with `sorry` |
|---|---|
| `3131776` | `Depth/RegularZeroTanh.lean` (1), `Depth/TanhPathBlock.lean` (1), `Depth/TanhZero.lean` (3), `Depth/HiddenZero.lean` (6), `Depth/DomainZero.lean` (3), `Depth/DomainZeroConnected.lean` (2) |
| `04c1877` | `Depth/RegularZeroTanh.lean` (1), `Depth/TanhPathBlock.lean` (1), `Depth/HiddenZero.lean` (6) |
| `f1ffa79` | none |

Of the ten files of this audit, two had `sorry` at `3131776` and `04c1877`, each in one proof:
`exists_tanhPathBlock` (`Depth/TanhPathBlock.lean`) and `exists_regularZero_tanh_path`
(`Depth/RegularZeroTanh.lean`). The other eight had none. At `f1ffa79` no file has `sorry`.

`grep -rn "^axiom" SkipsLean` finds nothing, at the three commits. The word "axiom" occurs in two
comments (`Literature/OMinimal.lean`, `Literature/Sard.lean`), which say that those results are
hypotheses and not axioms.

## How I checked

- "By reading": I read the Lean source and the paper (`dim.txt`: Section 2, Theorem 5.2,
  Appendix D.1 to D.3, D.6 up to Lemma D.18, "Parameters that satisfy all conditions", D.7).
- "By compiling": scratch files of my own in `/home/claude/audit8b/` (`Chk1.lean`, `Chk2.lean`,
  `Chk3.lean`), compiled with `lean` 4.36.0. The compiled library of `/home/claude/lw` has none of
  the ten files, so I used the compiled library of `/home/claude/lp/lean` (branch `lean-plus`)
  through `LEAN_PATH`, without `lake`. At my first compile `lp` was at `04c1877` with no changed
  tracked file, and the ten source files were the same in `lp` and `lw` (`diff`); the compiled
  files were newer than their sources. At the end `lp` and `lw` were both at `f1ffa79`, `lp` with
  no changed tracked file, the same sources, and compiled files newer than the sources; I compiled
  the three scratch files once more against it. Where the two runs differ I say so. I wrote
  nothing under `lw`, `lp` or the repository.
- "By a computation": two Python scripts in `/home/claude/audit8b/` (`check_path.py`,
  `check_block.py`), floating-point checks on random data. They support a claim; they do not prove
  it.

## Short answer

**Nothing false, vacuous or drifted was found.** At the last commit, `f1ffa79`, every statement of
the ten files is proved (no `sorry`; by compiling, each depends on `propext`, `Classical.choice`,
`Quot.sound` only).

1. The two existence statements stand where the paper also needs one parameter only. No statement
   of the ten files is an "almost every" statement, and none claims (S3) at generic parameters.
2. Lemma D.18 in Lean has the paper's hypotheses. The cone `C_κ` is an explicit hypothesis in the
   place of "`κ_ℓ` of Lemma D.14"; this is the same lemma, stated for every cone on which the
   network after the block is holomorphic. The cone is supplied by statements that exist. No
   axiom, and no hypothesis that restates the conclusion.
3. (R1), (R2), (R3), (S1), (S2), (S3) in Lean are the paper's conditions clause by clause, with
   the numbering shifted by one (Lean block `k` is the paper's block `k + 1`).

---------------------------------------------------------------------------------------------------

## Part 1: the three drift checks

### Check 1. Existence versus "generic"

**Verdict: no drift.** Both statements are existence statements, the paper's proof needs one
parameter `θ*` at that place, and no statement of these files claims (S3) at generic parameters.

The two Lean statements (by reading; elaborated forms printed by compiling, `Chk2.lean`):

```
theorem exists_tanhPathBlock {q : Type*} [Fintype q] (hd : 2 ≤ Fintype.card d)
    (hq : Fintype.card d ≤ Fintype.card q) {κ : ℝ} (hκ : 0 < κ) :
    ∃ (W : Matrix d q ℝ) (V : Matrix q d ℝ), TanhPathBlock W V κ

theorem exists_regularZero_tanh_path [Nonempty T] (hd : 2 ≤ Fintype.card d)
    (hdIn : Fintype.card d ≤ Fintype.card dIn) (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∃ θ : Params (Arch.mlp (T := T) (d := d) Real.tanh (rmsNorm 0) hid) dIn dOut,
      RegularZero (Arch.mlp Real.tanh (rmsNorm 0) hid) θ ∧
      ∀ k : Fin L,
        (∀ i j : hid k, i ≠ j → ∀ a c : ℝ, a • θ.write k i + c • θ.write k j = 0 →
          a = 0 ∧ c = 0) ∧
        LinearIndependent ℚ (fun j : hid k => fun i : d => θ.read k i j) ∧
        ∃ κ : ℝ, 0 < κ ∧ HolomorphicOnCone Complex.tanh θ k.succ κ ∧ CondS3 θ k κ
```

The paper at this place (Appendix D.6, "Parameters that satisfy all conditions, in the case (0)"):
(R1), (S1), (S2), (R2), (R3) fail on a set of measure zero of pairs `(W, V)`; (S3) holds "on a
nonempty open set of pairs"; "A nonempty open set minus a set of measure zero is not empty. So
there are parameters `θ*` that are regular and whose blocks all satisfy (S1) to (S3) for tanh". The
paper does not say that (S3) is generic, and it is not: (S3) asks for large reads. Appendix D.7,
"The case (0)", then uses this one `θ*`: the claim `(D_k)` holds at `θ*`, the Jacobian has the rank
(13) at `θ*` on a batch `X*`, and the passage to almost every parameter is made by analyticity on
the connected open set `O_{X*}` (Lemma D.20). So one parameter is all the proof needs. (By reading.)

In Lean the same: the only use of `exists_regularZero_tanh_path` is in
`exists_jacobianRank_tanh_rmsNorm_zero` (`Depth/TanhZero.lean`, read at `04c1877`), which is again
an existence statement (a parameter and a batch); the "almost every" is only in the final theorem
`ae_funDim_tanh_skipless_rmsNorm_zero` (part A of this audit). `exists_tanhPathBlock` is used
only inside the proof of `exists_regularZero_tanh_path` (at `04c1877` that proof was `sorry` and
the statement was used nowhere).

No measure in the ten files: `grep` for `∀ᵐ`, `ae_`, `IsAddHaarMeasure`, `volume`, `Measure` in
the ten files finds nothing. The words "measure zero" occur only in the header of
`Depth/TanhPathBlock.lean`, inside a quotation of the paper.

One difference in form, not a drift: the paper proves more than existence for one block (a
nonempty open set minus a set of measure zero); Lean states existence only, for every cone `C_κ`,
`κ > 0`. The header of `Depth/TanhPathBlock.lean` says so ("The existence needs one pair only").

### Check 2. Lemma D.18 has no hypothesis that restates a conclusion

**Verdict: none.** The hypotheses are the paper's, plus what the paper has in its Setup; the cone
is the conclusion of Lemma D.14, not of Lemma D.18, and it is supplied.

The Lean statement (`Depth/StepZeroTanh.lean`; by reading, and elaborated by compiling):

```
theorem claimZero_castSucc_tanh [Nonempty T]
    {θ : Params (Arch.mlp (T := T) (d := d) Real.tanh (rmsNorm 0) hid) dIn dOut}
    (hθ : RegularZero (Arch.mlp Real.tanh (rmsNorm 0) hid) θ) (hd : 2 ≤ Fintype.card d)
    (k : Fin L)
    (hS1 : ∀ i j : hid k, i ≠ j → ∀ a c : ℝ, a • θ.write k i + c • θ.write k j = 0 →
      a = 0 ∧ c = 0)
    (hS2 : LinearIndependent ℚ (fun j : hid k => fun i : d => θ.read k i j))
    {κ : ℝ} (hκ : 0 < κ) (hhol : HolomorphicOnCone Complex.tanh θ k.succ κ)
    (hS3 : CondS3 θ k κ)
    (hk : ClaimZero (Arch.mlp Real.tanh (rmsNorm 0) hid) θ k.succ) :
    ClaimZero (Arch.mlp Real.tanh (rmsNorm 0) hid) θ k.castSucc
```

Hypotheses side by side. The paper: "Let `σ = tanh`, in the case (0), let `θ` be regular, and let
block `k + 1` satisfy (S1) to (S3). Then `(D_{k+1})` implies `(D_k)`."

| Lean | Paper |
|---|---|
| the architecture `Arch.mlp Real.tanh (rmsNorm 0) hid` | "`σ = tanh`, in the case (0)" |
| `[Nonempty T]` (at least one token) | implicit: Appendix D takes one token |
| `hθ : RegularZero … θ` | "let `θ` be regular" |
| `hd : 2 ≤ card d` | Setup and Theorem 5.2: `d_model ≥ 2` |
| `k : Fin L` | the paper's block `k + 1` |
| `hS1` | (S1) for block `k + 1` |
| `hS2` | (S2) for block `k + 1` |
| `hκ : 0 < κ`, `hhol : HolomorphicOnCone Complex.tanh θ k.succ κ` | "`κ_ℓ` of Lemma D.14" (in the sentence that states (S1) to (S3)), with `ℓ = k + 1` |
| `hS3 : CondS3 θ k κ` | (S3) for block `k + 1`, with the cone `C_{κ_{k+1}}` |
| `hk : ClaimZero … k.succ` | `(D_{k+1})` |
| conclusion `ClaimZero … k.castSucc` | `(D_k)` |

Is the cone hypothesis the same as "`κ_ℓ` of Lemma D.14"? **Yes.** In the paper `κ_ℓ` is a number
that Lemma D.14 gives, and all that the proofs of Lemmas D.15 to D.18 use of it is that `𝓑_{>ℓ}`
with its derivatives is holomorphic on `C_{κ_ℓ}`. (S3) depends on which number is taken (a smaller
cone asks more). Lean states the lemma for every `κ > 0` with that property, so it holds for
whatever number the paper's Lemma D.14 gives. Two small differences, both on the side of
generality: the paper has `κ_ℓ ∈ (0, 1]` and Lean allows `κ > 1` as well (then `hhol` asks more);
and Lean's `κ` is tied to the block by `hhol` and `hS3` having the same `κ`, which I checked in the
statement (`k.succ` is the hidden state after block `k`, the paper's `h_{k+1}`, and `𝓑_{>k+1}` is
`suffix … k.succ`). `hhol` is not the conclusion of Lemma D.18 in any form: it says that a map is
analytic; the conclusion is about the directions `Z`, `η`.

A hypothesis `HolomorphicOnCone … κ` alone would be empty for `κ = 0`: the cone `C_0` is the empty
set, so with at least one token `HolomorphicOnCone σC θ k 0` holds for every map `σC` (by compiling,
`Chk2.lean`, example (1)). Every statement of the ten files that takes such a hypothesis also takes
`0 < κ` (by reading each: `fderiv_suffixC_ofReal`, `fderiv_weights_suffixC_ofReal`,
`blockLHSC_ofReal`, `blockLHSC_pathMatrix_eq_zero`, `eq_zero_of_fderiv_suffixC_one_sub_sq`,
`tanh_path_step`, `claimZero_castSucc_tanh`, `exists_holomorphicOnCone_castSucc`), except
`HolomorphicOnCone.mono` and `HolomorphicOnCone.congr`, which only pass the property on. And (S3)
for `C_0` is false, since it puts rows in the cone.

Does every use supply the cone? **Yes.**

- `claimZero_of_tanh_path` (`Depth/TanhZero.lean`) takes, for every block `k`, (S1), (S2) and
  `∃ κ : ℝ, 0 < κ ∧ HolomorphicOnCone Complex.tanh θ k.succ κ ∧ CondS3 θ k κ`, and its proof at
  `04c1877` is the induction `claimZero_last` then
  `claimZero_castSucc_tanh hθ hd k (hblocks k).1 (hblocks k).2.1 hκ hhol hS3 ih` (by reading; by
  compiling: it depends on `propext`, `Classical.choice`, `Quot.sound` only). At `3131776` this
  proof was `sorry`; the statement is the same.
- `exists_regularZero_tanh_path` has exactly this conjunction in its conclusion (text above), and
  `exists_jacobianRank_tanh_rmsNorm_zero` passes it on unchanged (`obtain ⟨θ, hθ, hblocks⟩ :=
  exists_regularZero_tanh_path …`, then `claimZero_of_tanh_path hθ hd hblocks 0`; by reading at
  `04c1877`).
- The cones themselves come from Lemma D.14, which is proved: `holomorphicOnCone_last`,
  `exists_holomorphicOnCone_castSucc`, `HolomorphicOnCone.congr`
  (`Depth/ComplexSuffixStep.lean`; by compiling: the three standard axioms only).
- The final theorem `ae_funDim_tanh_skipless_rmsNorm_zero` has no cone and no condition (S·) or
  (R·) among its hypotheses (by reading).

What was still open at `3131776` and `04c1877` was the proof of `exists_regularZero_tanh_path`
(and of `exists_tanhPathBlock` under it), not a hypothesis. At `f1ffa79` both are proved.

Proof status (by compiling, `Chk1.lean` and `Chk3.lean`). Against the library at `04c1877`:
`claimZero_castSucc_tanh` and `tanh_path_step` depend on `propext`, `Classical.choice`,
`Quot.sound` only, and so do the other 31 public statements of the eight files without `sorry`;
`exists_tanhPathBlock` and `exists_regularZero_tanh_path` depend on `sorryAx`. Against the library
at `f1ffa79`: all 35 public statements of the ten files depend on the three standard axioms only,
and so do `claimZero_of_tanh_path`, `exists_jacobianRank_tanh_rmsNorm_zero` and
`ae_funDim_tanh_skipless_rmsNorm_zero`.

### Check 3. The conditions (S1), (S2), (S3), (R1), (R2), (R3)

**Verdict: the same as the paper's, clause by clause.** (By reading; the fit of the one-row forms
by compiling.)

Numbering. The Lean block `k : Fin L` is the paper's block `k + 1`; it reads the hidden state
`k.castSucc` (the paper's `h_k`) and writes `k.succ` (the paper's `h_{k+1}`). `θ.read k` is `W`,
with the columns `c_j = fun i => θ.read k i j`; `θ.write k` is `V`, with the rows `a_j`. The
paper's `κ_ℓ` for block `ℓ = k + 1` is the cone of `𝓑_{>k+1}`, in Lean the `κ` of
`HolomorphicOnCone … k.succ κ`. All statements of the ten files follow this.

**(R1), (R2), (R3): `RegularZero`** (`Depth/SuffixZeroDeriv.lean:38-51`, rows `T`):

```
structure RegularZero : Prop where
  rank_E : θ.E.rank = Fintype.card d
  rank_D : θ.D.rank = Fintype.card d
  rank_write : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d
  block_ne_zero : ∀ (ℓ : Fin L) (n : Matrix T d ℝ),
    (∀ t, n t ⬝ᵥ n t = (Fintype.card d : ℝ)) →
      ∀ t, (A.f ℓ (n * θ.read ℓ) * θ.write ℓ) t ≠ 0
  deriv_block : ∀ ℓ : Fin L, ∃ n : Matrix T d ℝ, (∀ t, n t ⬝ᵥ n t = (Fintype.card d : ℝ)) ∧
    ∀ v : Matrix T d ℝ, (∀ t, v t ⬝ᵥ n t = 0) →
      (∀ t, ∃ a : ℝ,
        fderiv ℝ (fun n' : Matrix T d ℝ => A.f ℓ (n' * θ.read ℓ) * θ.write ℓ) n v t
          = a • (A.f ℓ (n * θ.read ℓ) * θ.write ℓ) t) →
      v = 0
```

| Paper | Lean | Same? |
|---|---|---|
| (R1) "`E`, `D` and every `W_write^ℓ` have rank `d_model`" | `rank_E`, `rank_D`, `rank_write` | yes |
| (R2) "in the case (0), for every `ℓ` and every `n ∈ S`: `g_ℓ(n) ≠ 0`" | `block_ne_zero`: for every block and every `n` whose rows are all on the sphere `‖n‖² = d`, no row of `g_ℓ(n)` vanishes | yes, token by token. For MLP blocks and at least one token it is the paper's (R2). With no token it is empty. |
| (R3) "in the case (0), there is an `n ∈ S` such that no row `v ≠ 0` with `⟨v, n⟩ = 0` has `𝐃g_ℓ(n) v ∈ ℝ g_ℓ(n)`" | `deriv_block`: some `n` with rows on the sphere such that a `v` with rows orthogonal to those of `n`, and every row of `𝐃g_ℓ(n) v` a multiple of the same row of `g_ℓ(n)`, is `0` | yes, token by token (for an MLP block row `t` of `𝐃g(n)v` depends on rows `t` of `n` and `v` only; with at least one token: every row of `n` is a row as in the paper's (R3), and one such row repeated gives `n`) |

The comparison of `RegularZero` with the paper in full is in part A of this audit.

**The one-row forms: `TanhPathBlock W V κ`** (`Depth/TanhPathBlock.lean`), for one read `W`, one
write `V`, and rows `d → ℝ` (the paper's one token):

| Field | Lean text | Paper |
|---|---|---|
| `rank_write` | `V.rank = Fintype.card d` | (R1), for the write of this block |
| `ne_zero` | `∀ n : d → ℝ, n ⬝ᵥ n = (card d : ℝ) → (fun j => Real.tanh ((n ᵥ* W) j)) ᵥ* V ≠ 0` | (R2): `g(n) = tanh(nW) V ≠ 0` on `S` |
| `deriv` | `∃ n, n ⬝ᵥ n = (card d : ℝ) ∧ ∀ v, v ⬝ᵥ n = 0 → (∃ a : ℝ, fderiv ℝ (fun n' => (fun j => Real.tanh ((n' ᵥ* W) j)) ᵥ* V) n v = a • ((fun j => Real.tanh ((n ᵥ* W) j)) ᵥ* V)) → v = 0` | (R3) in the case (0), word for word |
| `rows_indep` | `∀ i j : q, i ≠ j → ∀ a c : ℝ, a • V i + c • V j = 0 → a = 0 ∧ c = 0` | (S1) "any two rows of `V` are linearly independent" |
| `cols_indep` | `LinearIndependent ℚ (fun j : q => fun i : d => W i j)` | (S2) "the columns of `W` are linearly independent over `ℚ`" |
| `saturated` | the text of `CondS3` below, with `W`, `V` | (S3) for `C_κ` |

`TanhPathBlock` has (R1) for the write only; `E` and `D` are not part of a block.

**(S1), (S2) as hypotheses `hS1`, `hS2`** of `claimZero_castSucc_tanh`, `tanh_path_step`,
`eq_zero_of_fderiv_suffixC_one_sub_sq`, `claimZero_of_tanh_path` and in the conclusion of
`exists_regularZero_tanh_path`: the same two texts as `rows_indep` and `cols_indep`, with
`θ.write k` and `θ.read k`. (S1) is linear independence of every pair of different rows over `ℝ`;
(S2) is linear independence of the family of the columns, as vectors of `ℝ^d`, over `ℚ`. Both are
the paper's. With one hidden unit (S1) says nothing, in the paper and in Lean; regular `θ` and
`d ≥ 2` give at least two hidden units (the write has rank `d`), and every statement that takes
(S1) also takes these.

**(S3): `CondS3 θ k κ`** (`Depth/StepZeroTanh.lean:49-57`):

```
def CondS3 (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) (k : Fin L)
    (κ : ℝ) : Prop :=
  ∃ (ξ₀ : d → ℝ) (ρ : ℝ), ξ₀ ⬝ᵥ ξ₀ = 1 ∧ 0 < ρ ∧ ρ ≤ 1 ∧
    (∀ j : hid k, (ξ₀ ᵥ* θ.read k) j ≠ 0) ∧
    (∀ w : hid k → ℂ,
      (∀ j, ‖w j - ((Real.sign ((ξ₀ ᵥ* θ.read k) j) : ℝ) : ℂ)‖ ≤ ρ) →
        w ᵥ* θ.toC.2.1 k ∈ complexCone κ) ∧
    ∀ j : hid k,
      Real.exp (-(2 * (Real.sqrt (Fintype.card d) * |(ξ₀ ᵥ* θ.read k) j|))) < ρ / 3
```

| Clause of the paper's (S3) | Lean | Same? |
|---|---|---|
| "there are a unit row `ξ₀`" | `ξ₀ ⬝ᵥ ξ₀ = 1` | yes |
| "and a number `ρ ∈ (0, 1]`" | `0 < ρ ∧ ρ ≤ 1` | yes |
| "such that every `ξ₀c_j ≠ 0`" | `∀ j, (ξ₀ ᵥ* θ.read k) j ≠ 0` | yes |
| "with `s_j` the sign of `ξ₀c_j`" | `Real.sign ((ξ₀ ᵥ* θ.read k) j)`, which is `1` or `−1` since `ξ₀c_j ≠ 0` | yes |
| "the rows `w̃V` with `\|w̃_j − s_j\| ≤ ρ` for all `j` lie in `C_{κ_ℓ}`" | for every **complex** row `w` with `‖w_j − s_j‖ ≤ ρ` for all `j`: `wV ∈ complexCone κ` (`θ.toC.2.1 k` is `V` with complex entries) | yes; see the note |
| "`e^{−2√d\|ξ₀c_j\|} < ρ/3` for every `j`" | `exp(−(2 (√(card d) · \|ξ₀c_j\|))) < ρ / 3` | yes |

Note on "complex `w̃`". The paper's sentence (S3) does not say over which rows `w̃` ranges. Its
proof of Lemma D.18 uses (S3) for the complex rows `w̃(ζ)`, `ζ` in the polydisc ("(S3) gives
`w̃(ζ) V ∈ C_κ`"), and `C_κ` is a set of complex rows, so the complex reading is the one the proof
needs. Lean takes complex rows, and its file header says so ("the rows `w̃` of (S3) are complex
rows"). The index does not say it (see the corrections). The authors may want the word "complex"
in the paper's (S3).

The (S3) of `TanhPathBlock` is `CondS3` for a block with these weights: `example … (h :
TanhPathBlock (θ.read k) (θ.write k) κ) : CondS3 θ k κ := h.saturated` compiles (`Chk2.lean`,
example (3)).

In `tanh_path_step` the same clauses appear as separate hypotheses for a unit row `ξ` near `ξ₀`:
signs `s_j = ±1` (`hs`), `0 < ρ ≤ 1`, the cone clause for complex `w` (`hcone`), `0 < s_j · ξc_j`
(`hsign`: `ξc_j` has the sign `s_j`), and `exp(−(2 (√d |ξc_j|))) < ρ/3` (`hdecay`). This is the
paper's set `P` ("an open set `P` of unit rows around `ξ₀` such that `ξc_j` has the sign `s_j` and
`e^{−2√d|ξc_j|} < ρ/3`").

---------------------------------------------------------------------------------------------------

## Part 2: the statements, file by file

### Verdict table

"Proved" means: no `sorry` in the file at the three commits, and by compiling (`Chk1.lean`) the
statement depends on `propext`, `Classical.choice`, `Quot.sound` only.

| Paper | Lean | File | Verdict | Difference |
|---|---|---|---|---|
| "RMSNorm at complex rows": `N(h) = √d h/√⟨h,h⟩`, principal root, for `Re⟨h,h⟩ > 0` | `rmsRowC`, `rmsNormC`, `rmsRowC_ofReal` | `ComplexRMSNorm` | SAME | Written `exp(−log(⟨h,h⟩/d)/2) • h` with the principal logarithm; it is a total function, and outside `Re⟨h,h⟩ > 0` its values mean nothing (no statement uses them without a hypothesis). Proved. |
| "It is holomorphic" | `analyticAt_rmsRowC` | `ComplexRMSNorm` | SAME | At every `h` with `Re⟨h,h⟩ > 0`. Proved. |
| "`N(λh) = N(h)` for `λ > 0`" | `rmsRowC_smul` | `ComplexRMSNorm` | SAME | For `Re⟨h,h⟩ > 0`, as in the paper. Proved. |
| Equation (40) | `rmsRowC_eq_self`, `fderiv_rmsRowC_apply` | `ComplexRMSNorm` | SAME | Proved. |
| The cones `C_κ`: "an open cone … that contains every real row `h ≠ 0`. On `C_1`, `Re⟨h,h⟩ > 0`" | `complexCone`, `isOpen_complexCone`, `smul_mem_complexCone`, `ofReal_mem_complexCone`, `re_dotProduct_self_pos_of_mem_complexCone`, `complexCone_mono` | `ComplexRMSNorm` | SAME | The set is `‖u'‖² < κ² ‖u‖²` for every real `κ`: the paper's cone for `κ > 0`; empty for `κ = 0`; `C_{−κ} = C_κ` (by compiling). `ofReal_mem` asks `κ > 0`; `Re > 0` is stated on every `C_κ`, `0 ≤ κ ≤ 1`. `complexCone_mono` is not in the paper. Proved. |
| "The path", `⟨n(t),n(t)⟩ = d`, real on `\|t\| = 1`, `n(1) = √d ξ`, equation (41) | `pathRow`, `pathRow_dotProduct_self`, `pathRow_exp_mul_I`, `pathRow_one`, `pathRow_ofReal` | `ComplexRMSNorm` | SAME | (41) is stated for every real `t` (the paper: `t ≥ 1`); "real on the unit circle" is the formula `n(e^{iφ}) = √d (cos φ ξ − sin φ ξ')`. Proved. |
| Lemma D.14, the objects: `𝓑_{>k}` at complex weights and rows | `CWeights`, `Params.toC`, `suffixC`, `suffixC_ofReal`, `suffixC_smul_rows` | `ComplexSuffix` | SAME | `suffixC` is the paper's recursion with `rmsNormC` and a map `σC : ℂ → ℂ`. It extends `suffix` at every real `h` when `σC` extends `σ`; it does not change under positive multiples of rows with `Re⟨h,h⟩ > 0`. Proved. |
| Lemma D.14: "extends to a holomorphic map on `C_{κ_k}`", with its derivatives | `HolomorphicOnCone` (definition) | `ComplexSuffix` | SAME (see (d)) | One map `(ω, h) ↦ suffixC σC ω k h`, analytic at `(θ, h)` for every `h` with rows in `C_κ`. |
| Lemma D.14, for regular `θ` | `exists_holomorphicOnCone` | `ComplexSuffix` | LEAN WEAKER | Asks `RegularZero` (so also (R3)); the paper asks (R1) and (R2). The proof uses (R2) only. Without the last sentence of the lemma. Proved. |
| Lemma D.14, its two steps | `holomorphicOnCone_last`, `exists_holomorphicOnCone_castSucc` | `ComplexSuffixStep` | PART | `κ_L = 1` at every `θ`; the step asks (R2) for the one block, in the one-row form, and a cone `κ' > 0` for the later blocks. Proved. |
| Lemma D.14, "The number `κ_k` depends only on the weights of the blocks `k+1, …, L` and on `D`" | `HolomorphicOnCone.congr` | `ComplexSuffixStep` | SAME | As: two parameters with the same reads and writes after the hidden state `k` and the same `D` have the same cones. Proved. |
| Lemma D.14 | `exists_holomorphicOnCone_of_ne_zero` | `ComplexSuffixStep` | LEAN STRONGER | (R2) alone, one-row form; no (R1). Without the last sentence (that is `congr`) and without the invariance under `λ > 0` (that is `suffixC_smul_rows`). Proved. |
| (not in the paper) | `HolomorphicOnCone.mono` | `ComplexSuffix` | — | A smaller cone, `0 ≤ κ' ≤ κ`. True. Proved. |
| "The identity on the path": (14), (20), (21) at complex arguments | `tangentRMSC`, `zdotC`, `blockLHSC`, `pathMatrix`, `tangentRMSC_ofReal`, `zdotC_ofReal`, `fderiv_suffixC_ofReal`, `fderiv_weights_suffixC_ofReal`, `blockLHSC_ofReal` | `ComplexBlockIdentity` | SAME | The formulas are the paper's, with rows `T`; `𝐃𝓑`, `𝐃_θ𝓑` at complex arguments are the complex derivatives of `suffixC`; at real arguments (rows of `w̃V` not zero, a cone `κ > 0`) they are the real ones. The paper's sentence "`𝓛` is holomorphic in `w̃`, affine in `w̃'` and polynomial in `n`" is not a public statement (a private helper has what the proof needs). Proved. |
| Lemma D.15 (Continuation) | `blockLHSC_pathMatrix_eq_zero` | `ComplexBlockIdentity` | SAME for regular `θ` | Hypothesis (16) and regular `θ` in the place of "(22)" (equivalent for regular `θ`); the cone is a hypothesis; a pair `ξ, ξ'` per token (the paper: one token); `σ` real-analytic with derivative `σ'`, extended by `σC`. Formally it asks (R3), which the paper's lemma does not need. Proved. |
| Lemma D.16 (Separation on the path) | `path_separation`; middle step `eventually_eq_zero_of_sum_pow_mul_exp_path` | `PathSeparation` | SAME | Values in any complex normed space. The paper's `𝒯_i` is `𝒯 ⟨i + K, _⟩`. The middle step is a PART (maps analytic at `0`, scalar values, all large `t`, nonnegative powers). Proved. |
| Lemma D.17, for a complex `b` | `eq_zero_of_fderiv_suffixC_one_sub_sq` | `ComplexOneSubSq` | SAME in substance | The cone `C_κ`, `κ > 0`, on which `𝓑_{>k+1}` is holomorphic is a hypothesis (the paper has it from Lemma D.14); `d ≥ 2`; at least one token; the same row `w̃V` at every token. Proved. |
| Proof of Lemma D.18, "The path" and "The powers of `t`", one pair `ξ, ξ'` | `tanh_path_step` | `StepZeroTanhPath` | PART, true | The four real equations are `⟨νZ,ν⟩ = 0` and `ż⁽¹⁾ = 0` (checked by hand and by a computation); the third part is `𝒯_0 = 0` at the real rows with `\|w̃_j − s_j\| < ρ/4`. Proved. |
| (S3) | `CondS3` | `StepZeroTanh` | SAME | Check 3. |
| Lemma D.18 | `claimZero_castSucc_tanh` | `StepZeroTanh` | SAME | Check 2: the cone is an explicit hypothesis; `d ≥ 2`; at least one token. Proved. |
| "Parameters that satisfy all conditions", the conditions on one `tanh` block | `TanhPathBlock` (definition) | `TanhPathBlock` | SAME | Check 3; one row; (R1) for the write only. |
| "Parameters that satisfy all conditions", one block | `exists_tanhPathBlock` | `TanhPathBlock` | PART | Existence of one pair for every `κ > 0`; the paper shows a nonempty open set minus a set of measure zero. `sorry` at `3131776` and `04c1877`, proved at `f1ffa79`. |
| "So there are parameters `θ*` that are regular and whose blocks all satisfy (S1) to (S3) for tanh" | `exists_regularZero_tanh_path` | `RegularZeroTanh` | SAME | With the cone of every block made explicit, and the paper's Setup (`d_in, d_out ≥ d ≥ 2`, at least `d` hidden units, at least one token). `sorry` at `3131776` and `04c1877`, proved at `f1ffa79`. |

### (a) Are the statements true as written?

**The 33 public statements of the eight files that never had `sorry`** are proved: they compile
(in the `lp` library at `04c1877` and at `f1ffa79`, same sources) and depend on the three standard
axioms only. The two existence statements are proved at `f1ffa79`. I also
looked for degenerate cases in which a statement would be true for an empty reason, by reading:

- *No tokens.* `HolomorphicOnCone` holds for every `κ` (every map into matrices without rows is
  constant). Lemma D.17 (`eq_zero_of_fderiv_suffixC_one_sub_sq`), `tanh_path_step`, Lemma D.18 and
  `exists_regularZero_tanh_path` ask `[Nonempty T]`; without it Lemma D.17 would be false. Lemma
  D.15 (`blockLHSC_pathMatrix_eq_zero`) does not ask it and is trivially true without tokens.
- *`d` with one element.* There are no orthonormal `ξ, ξ'`, so Lemma D.15 is empty there; Lemmas
  D.17, D.18 and `tanh_path_step` ask `d ≥ 2`. `rmsRowC_eq_self` and `fderiv_rmsRowC_apply` hold
  also for empty `d`.
- *No hidden unit, or one.* `CondS3` is false for a block without hidden units (the zero row is
  not in a cone). (R2) in the one-row form is false there too. (S1) says nothing for one hidden
  unit, and Lemma D.17 would then be false (the direction `((1 − w̃²) b) a_1` is along `w̃ a_1`, and
  `𝐃𝓑(h) h = 0`); the hypotheses "regular" and `d ≥ 2` exclude it (rank of the write), in the paper
  and in Lean.
- *`κ = 0` or `κ < 0`.* See Check 2: every statement with a cone hypothesis asks `κ > 0`.
- *`path_separation` without variables* (`ι` empty): the hypothesis on `ρ₀` is empty and the
  statement is the fact that a Laurent polynomial in `t` with vanishing values has vanishing
  coefficients. True.

The hypotheses of Lemma D.18 and of `tanh_path_step` can hold together (so the statements are not
empty): by the paper's construction; and by a computation for one block (`check_block.py`: `d = 2`,
three hidden units, `V = Wᵀ`, `κ = 0.2`: the cone clause of (S3) on 200,000 sampled complex rows,
the decay clause, (R1), (R2) on 20,001 points of the circle, (R3) at one point, (S1); (S2) cannot
be tested in floating point).

**`tanh_path_step`: the algebra** (by hand, and by a computation, `check_path.py`, `d = 4`, six
hidden units, random data).

- Equation (43). With `a = ⟨νZ,ν⟩`, `b = ⟨νZ,ν̄⟩ + ⟨ν̄Z,ν⟩`: `⟨n(t)Z, n(t)⟩/d · n(t) =
  (√d/8)(t²a + b + t⁻²⟨ν̄Z,ν̄⟩)(tν + ν̄/t)`, so the coefficient of `t³` in `ż(n(t))` is
  `−(√d/8) a νW` and that of `t` is `(√d/2)(ν(ZW + η_W) − (1/4)(bν + aν̄)W)`: the paper's (43). The
  computation fits the four powers `t³, t, t⁻¹, t⁻³` to `ż(n(t))` at six values of `t`: no other
  power, and the two coefficients agree with (43) to `10⁻¹⁴`.
- `⟨νZ,ν⟩ = (ξZξᵀ − ξ'Zξ'ᵀ) + i (ξZξ'ᵀ + ξ'Zξᵀ)`. So `⟨νZ,ν⟩ = 0` is the first pair of the Lean
  conclusion, `ξZξ'ᵀ + ξ'Zξᵀ = 0` and `ξZξᵀ = ξ'Zξ'ᵀ`.
- Then `b = 2(ξZξᵀ + ξ'Zξ'ᵀ) = 4 ξZξᵀ`, and `ż⁽¹⁾ = (√d/2)(ν(ZW + η_W) − (ξZξᵀ) νW)`. So
  `ż⁽¹⁾ = 0` is `ξ(ZW + η_W) = (ξZξᵀ) ξW` (real part) and `ξ'(ZW + η_W) = (ξZξᵀ) ξ'W` (imaginary
  part): the second pair. The paper writes this after part (a), with `ξZξᵀ = β_k`.
- A symmetry direction (`Z = Y + βI`, `η_W = −YW`) satisfies the four equations for every
  orthonormal pair (computation), as it must.
- `tanh(n(t)c_j) = s_j (1 − ζ_j)/(1 + ζ_j)` with `ζ_j = e^{−2 s_j n(t)c_j}` and
  `|ζ_j(t)| = e^{−(t + t⁻¹)√d|ξc_j|} ≤ e^{−2√d|ξc_j|}` for `t ≥ 1` (computation at four values of
  `t`).
- The constant `ρ/3`: `|w̃_j(ζ) − s_j| = 2|ζ_j|/|1 + ζ_j| ≤ 3|ζ_j|` for `|ζ_j| ≤ 1/3`, so
  `|ζ_j| < ρ/3` gives `|w̃_j − s_j| < ρ` (the largest ratio found in 200,000 samples: 0.9999). This
  is the paper's. In Lemma D.16 `ρ₀ = ρ/3 > e^{−2u_j}` with `u_j = √d|ξc_j|` is the decay clause.
- The constant `ρ/4` is Lean's own (the paper says "a neighborhood of `s̄`"): a real `w̃_j` with
  `|w̃_j − s_j| < ρ/4` is `w̃_j(ζ)` for the real `ζ_j = (1 − s_j w̃_j)/(1 + s_j w̃_j)`, and
  `|ζ_j| < (ρ/4)/(2 − 1/4) = ρ/7 < ρ/3`. So these rows are in the image of the polydisc, and the
  third part of the conclusion follows from `𝒯_0 = 0`.

**`exists_tanhPathBlock`** (`sorry` at `3131776` and `04c1877`; proved at `f1ffa79`). Before the
proof arrived I judged it true by hand, as follows; I did not read the Lean proof. Take
`V = Wᵀ` (the header of the file names this family), `W = λW°` with `W°` of rank `d`, any two
columns linearly independent, columns linearly independent over `ℚ`, and a unit row `ξ₀` with every
`ξ₀c°_j ≠ 0`.
(R1), (S1), (S2) hold for every `λ > 0`. (R2): `⟨tanh(nW)Wᵀ, n⟩ = ∑_j tanh(nc_j)(nc_j) > 0` for
`n ≠ 0`. (S3): `s̄V ≠ 0`, because `⟨s̄Wᵀ, ξ₀⟩ = ∑_j |ξ₀c_j| > 0`; the cone clause does not change
when `V` is multiplied by `λ > 0`, so one `ρ` serves every `λ`; the decay clause holds for large
`λ`. (R3): `𝐃g(n) = W diag(1 − tanh²(nc_j)) Wᵀ =: H(n)` is symmetric positive definite, so
`vH = a g` with `⟨v,n⟩ = 0` forces `v = 0` as soon as `f(n) := g(n) H(n)⁻¹ nᵀ ≠ 0`. For `W°`, `f`
is real-analytic on `ℝ^d` and positive near `0` (there `f(n) ≈ ‖n‖²`), so the radii `r` for which
`f` vanishes on the whole sphere of radius `r` have no accumulation point in `(0, ∞)`; the sphere
`‖n‖² = d` for `λW°` is the sphere of radius `λ√d` for `W°`; so (R3) holds for arbitrarily large
`λ`. The computation above agrees for one example.

**`exists_regularZero_tanh_path`** (`sorry` at `3131776` and `04c1877`; proved at `f1ffa79`). By
hand it follows from `exists_tanhPathBlock`: `E` and `D` of rank `d` exist (`d_in, d_out ≥ d`); the blocks are
chosen from the last to the first, each for the cone that Lemma D.14 gives for the blocks after it
(`holomorphicOnCone_last`, `exists_holomorphicOnCone_castSucc`, `HolomorphicOnCone.congr`); the
one-row conditions give `RegularZero` token by token. For no block (`L = 0`) it asks only `E` and
`D` of rank `d`. By hand; the forms by compiling ((c) below).

### (b) Do the docstrings say honestly what part of the paper each statement is?

Yes, with two small exceptions (the first two points below). By reading every file header and
every docstring of a public statement.

- `exists_holomorphicOnCone` (`ComplexSuffix.lean:363`): "if `θ` is regular ((R1) and (R2) are
  used)". The proof uses (R2) only (`hθ.block_ne_zero`, the one use of `hθ`). The later file says
  it right ("(R1) is not used").
- The headers and docstrings of `ComplexSuffixStep.lean` name "block `ℓ`" with the Lean number and
  `𝓑_{>ℓ+1}`, `𝓑_{>ℓ}` with the paper's; the header states the numbering once ("the block
  `ℓ : Fin L` is the paper's block `ℓ + 1`"), so this is consistent, but a reader of one docstring
  alone may take "block `ℓ`" for the paper's block `ℓ`.
- The differences that the brief lists are all stated where they occur: the same row at every
  token (`ComplexOneSubSq`, `StepZeroTanhPath`); a pair `ξ, ξ'` per token in Lemma D.15
  (`ComplexBlockIdentity`); (16) and regular `θ` in the place of "(22)" (docstring of
  `blockLHSC_pathMatrix_eq_zero`, with the name of the lemma that gives the equivalence); the
  complex derivative of `suffixC` in the place of `𝐃𝓑` at complex arguments (`ComplexSuffix`,
  `ComplexBlockIdentity`, `ComplexOneSubSq`); the cone as a hypothesis in the place of `κ_ℓ`
  (`StepZeroTanh`, header and docstring); the complex rows of (S3) (`StepZeroTanh`, header); the
  family `V = Wᵀ` for one block and "the existence needs one pair only" (`TanhPathBlock`); the
  one-row form of (R2) (`ComplexSuffixStep`).
- `tanh_path_step` is described as "what one pair `ξ, ξ'` gives", in real terms, with the
  derivation of the four equations in the header. Correct (see (a)).

### (c) Do the pieces fit?

Yes. By compiling and by reading.

- `claimZero_castSucc_tanh` is proved from `tanh_path_step` (line 263),
  `flat_at_write_of_isOpen_rows` (line 328: the open set is the rows with `|r_j − s_j| < ρ/4`, the
  third part of `tanh_path_step`), `suffixFlatZero_of_flat_at_write` (line 330: Lemma D.3 with
  `A = V`), `dense_setOf_linearIndependent_vecMul` (the set `P'` from (S2)),
  `exists_eq_smul_one_of_vecMul_parallel` and `eq_zero_of_vecMul_eq_zero_of_isOpen`, and the
  hypothesis `(D_{k+1})`. `tanh_path_step` is proved from `blockLHSC_pathMatrix_eq_zero` (line 645,
  Lemma D.15 with `σ' = 1 − tanh²`), `path_separation` (line 850, with `u_j = √d|ξc_j|`,
  `u'_j = √d s_j ξ'c_j`, `ρ₀ = ρ/3`, `K = 3`), and `eq_zero_of_fderiv_suffixC_one_sub_sq` twice
  (lines 870 and 873, for `ż⁽³⁾` and `ż⁽¹⁾`). Since both compile without `sorryAx`, every hypothesis
  of each piece is discharged with a matching form.
- The order of the paper's proof is kept: (a) `Z + Zᵀ = c I` from the first pair, on the dense set
  and then on the open set by continuity; (b) `η_W = −Y_k W`; (c) Lemma D.3 and `(D_{k+1})`.
- The conditions of one block feed the lemmas (`Chk2.lean`, examples (3) to (5), compile): from
  `h : TanhPathBlock (θ.read k) (θ.write k) κ'` and `HolomorphicOnCone Complex.tanh θ k.succ κ'`,
  `claimZero_castSucc_tanh hθ hd k h.rows_indep h.cols_indep hκ' hh h.saturated hk` type-checks,
  and so does `exists_holomorphicOnCone_castSucc … θ k hκ' hh h.ne_zero` (the cone for the next
  block towards the input); `h.ne_zero` at every row gives (R2) of `RegularZero`. (R3) of
  `RegularZero` from the one-row (R3) needs the derivative of the block row by row; I did not
  compile that step.
- The conclusion of `exists_regularZero_tanh_path` is, after `RegularZero`, word for word the
  hypothesis `hblocks` of `claimZero_of_tanh_path`; `exists_jacobianRank_tanh_rmsNorm_zero` passes
  it on (read at `04c1877`).

### (d) `HolomorphicOnCone` and `rmsRowC`

**`rmsRowC` is the paper's `N` with the principal square root.** `rmsRowC v = Complex.exp
(−(Complex.log ((v ⬝ᵥ v)/d)/2)) • v`, and `Complex.log` is the principal logarithm. By compiling
(`Chk2.lean`, example (6)): for `Re z > 0` and a natural number `n > 0`,
`exp(−(log(z/n)/2)) = √n / z^{1/2}`, where `z^{1/2}` is Mathlib's complex power `exp(log z · 1/2)`,
the principal root. So the factor is `√d/√⟨h,h⟩`. On `Re⟨h,h⟩ > 0` the number `⟨h,h⟩/d` is in the
right half-plane, where the principal branch is holomorphic (`analyticAt_rmsRowC`). At a real row
`v ≠ 0` it is `rmsRow 0 v` (`rmsRowC_ofReal`). At the zero row both are `0` in Lean.

**`HolomorphicOnCone` is an honest rendering** of "`𝓑_{>k}`, with its derivatives `𝐃𝓑_{>k}` and
`𝐃_θ𝓑_{>k}`, extends to a holomorphic map on `C_κ`":

```
def HolomorphicOnCone {σ : ℝ → ℝ} (σC : ℂ → ℂ)
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) (k : Fin (L + 1))
    (κ : ℝ) : Prop :=
  ∀ h : Matrix T d ℂ, (∀ t, h t ∈ complexCone κ) →
    AnalyticAt ℂ
      (fun p : CWeights d dOut hid × Matrix T d ℂ => suffixC σC p.1 k p.2) (θ.toC, h)
```

- The extension is a named map, `suffixC σC`, the paper's recursion with `N` at complex rows and
  `σC` in the place of `σ`. That it extends `𝓑_{>k}` is `suffixC_ofReal` (needs `σC` to extend
  `σ`). The paper says "extends to a holomorphic map" without naming the map; its proof builds the
  same one.
- The map is analytic in the weights and the hidden state together, at the real weights `θ` and
  at every `h` with rows in the cone. Its complex derivative in `h` is then a holomorphic extension
  of `𝐃𝓑_{>k}`, and its complex derivative in the weights one of `𝐃_θ𝓑_{>k}`: at a real `h`
  without a zero row and along real directions they are the real derivatives
  (`fderiv_suffixC_ofReal`, `fderiv_weights_suffixC_ofReal`, proved). The paper's "The weights
  enter holomorphically as well" is the joint analyticity.
- It says nothing for `κ = 0` (Check 2), and the statements ask `κ > 0`.
- "`𝓑_{>k}(λh) = 𝓑_{>k}(h)` for `λ > 0`" is not part of the definition; it is `suffixC_smul_rows`,
  for rows with `Re⟨h,h⟩ > 0`, at every complex weight.
- Rows `T`: every row of `h` in the cone. For MLP blocks and at least one token this is the
  paper's statement for one row.
- For `tanh`, `σC` is `Complex.tanh` (`sinh/cosh`, with the value `0` at the poles in Lean).
  The statements need it only where it is analytic: Lemma D.14 asks analyticity at the real
  points, and Lemma D.15 asks it at the points `n(t)c_j` of the path as a hypothesis, which
  `tanh_path_step` proves from `|ζ_j(t)| < 1`.

---------------------------------------------------------------------------------------------------

## What the authors should know

Nothing false, vacuous, drifted or misdescribed in a way that changes a meaning. In order of
weight:

1. **The cone of Lemma D.18 is a hypothesis in Lean, and it is discharged.** Lemma D.18, Lemma
   D.17 (complex `b`), Lemma D.15 and `tanh_path_step` take "`𝓑_{>k+1}` is holomorphic on `C_κ`,
   `κ > 0`" as a hypothesis where the paper says "`κ_ℓ` of Lemma D.14". The parameter `θ*`
   (`exists_regularZero_tanh_path`) supplies one cone per block together with (S3) for that cone,
   and the final theorem has no such hypothesis.
2. **Two proofs of this part were `sorry` when I began** (`exists_tanhPathBlock`,
   `exists_regularZero_tanh_path`) **and are proved at `f1ffa79`,** with their statements
   unchanged. At `f1ffa79` all 35 public statements of the ten files, and the three statements of
   `Depth/TanhZero.lean`, depend on the three standard axioms only (by compiling).
3. **The paper's (S3) does not say that the rows `w̃` are complex.** The proof of Lemma D.18 uses
   (S3) at complex rows `w̃(ζ)`, and Lean's `CondS3` quantifies over complex rows. A reader who
   takes `w̃` real in (S3) gets a weaker condition that the proof cannot use. One word in the
   paper's (S3) would settle it. (I changed nothing.)
4. **Lemma D.14 does not need (R1).** The paper states it for `θ` with (R1) and (R2); the Lean
   proofs use (R2) only (`exists_holomorphicOnCone_of_ne_zero`). Harmless; the paper may keep
   (R1) or drop it.
5. **Lemma D.15 in Lean** takes the identity (16) and regular `θ` where the paper takes "(22)".
   The two are equivalent for regular `θ`, and the docstring says so. The Lean form allows a
   different pair `ξ, ξ'` at every token; the proof of Lemma D.18 uses the same pair at every
   token.
6. **`tanh_path_step`** is a proof piece, not a paper statement. Its four real equations are the
   paper's `⟨νZ,ν⟩ = 0` and `ż⁽¹⁾ = 0` exactly (hand and computation). The radius `ρ/4` in its
   third part is Lean's choice inside the paper's "neighborhood of `s̄`"; `ρ/3` is the paper's.
7. **One docstring is inexact:** `exists_holomorphicOnCone` says "(R1) and (R2) are used"; only
   (R2) is.

### The commit `f1ffa79`, which arrived while I worked

What I checked of it:

- By `git diff 04c1877 f1ffa79` on `Depth/TanhPathBlock.lean` and `Depth/RegularZeroTanh.lean`: the
  only removed lines are the two `sorry`; the statements, the definition `TanhPathBlock` and the
  docstrings are unchanged. Added: private helpers, the two proofs, and `omit … in` lines; the one
  before `exists_regularZero_tanh_path` drops the instance `[DecidableEq d]` from its statement (by
  compiling: the elaborated statement is otherwise the one quoted in Check 1).
- `grep` finds no `sorry` and no `axiom` declaration in `SkipsLean/`.
- By compiling against the `lp` library at `f1ffa79` (`Chk1.lean`, `Chk2.lean`, `Chk3.lean`):
  the results stated above; `Chk2.lean` compiles as before.
- I did not read the two new proofs.

---------------------------------------------------------------------------------------------------

## Corrections for `STATEMENTS.md` (lines at `f1ffa79`; the same line numbers at `3131776`)

None corrects a wrong claim about what is proved. All are precisions.

1. **Lines 66-75** ("Not yet compared by such a reader"): after this audit, remove from the list
   `Depth/PathSeparation.lean`, `Depth/ComplexRMSNorm.lean`, `Depth/ComplexSuffix.lean`,
   `Depth/ComplexBlockIdentity.lean`, `Depth/ComplexOneSubSq.lean`, `Depth/StepZeroTanhPath.lean`,
   `Depth/StepZeroTanh.lean`, `Depth/ComplexSuffixStep.lean`, `Depth/TanhPathBlock.lean`,
   `Depth/RegularZeroTanh.lean` (compared here: none false, vacuous or changed in meaning). The
   other files of the list are part A.
2. **Line 172** (Lemma D.18) and **line 171** (`tanh_path_step`): say that the rows `w̃` of (S3)
   are complex rows: "(S3) for `C_κ` (`CondS3`; the rows `w̃` with `|w̃_j − s_j| ≤ ρ` are complex
   rows, as the proof needs)". Line 172 may also say "at least one token".
3. **Line 177** (Lemma D.14, steps): "(with these, Lemma D.14 holds with (R2) alone, without
   (R3))" should read "with (R2) alone: without (R1), which the paper asks, and without (R3), which
   the form for regular `θ` of the row above asks". And "block `ℓ`" there is the Lean number: write
   "the block between the hidden states `ℓ` and `ℓ + 1` (the paper's block `ℓ + 1`)". Add "`κ' > 0`".
4. **Line 164** (Lemma D.14): "does not change when the rows are multiplied by positive numbers"
   holds for rows with `Re⟨h,h⟩ > 0` (`suffixC_smul_rows`); add these words. The row may also say
   that `HolomorphicOnCone` is empty for `κ = 0` and that every statement asks `κ > 0`.
5. **Line 168** (Lemma D.15) and **line 169** (Lemma D.17, complex `b`): add "`κ > 0`"; line 169
   also "at least one token".
6. **Line 163**: "contain the real rows `≠ 0`" holds for `κ > 0`; "`C_κ`" is defined for every
   real `κ` (empty for `κ = 0`). Optional.
7. **Lines 178, 182 and 183** (status): "in work" at `3131776` and `04c1877`, "proved" at
   `f1ffa79`. Both were right at their commit: at `f1ffa79` the five statements of these rows
   depend on the three standard axioms only (by compiling). Nothing to correct.

---------------------------------------------------------------------------------------------------

## What I could not check

- I did not build the library. "Proved" rests on the compiled library of `/home/claude/lp`, built
  by its owner, whose source files were the same as those of `lw` (at `04c1877` and at `f1ffa79`);
  I checked that each compiled file was newer than its source, not that it was compiled from
  exactly that source.
- The proofs of `exists_tanhPathBlock` and `exists_regularZero_tanh_path`, which arrived at
  `f1ffa79`: I did not read them. That they are proved rests on the compiler.
- (S2), linear independence over `ℚ`, cannot be tested in floating point; I checked only that
  such columns exist (by hand: `ℝ` has infinite dimension over `ℚ`).
- The step from the one-row (R3) of `TanhPathBlock` to (R3) of `RegularZero` (rows `T`): by hand
  only.
- I read the statements and docstrings of all public declarations of the ten files, and the proofs
  of `claimZero_castSucc_tanh`, `tanh_path_step` (its last part), `blockLHSC_pathMatrix_eq_zero`,
  `exists_holomorphicOnCone` and the statements of `ComplexSuffixStep`. I did not read the private
  helpers line by line; their correctness rests on the compiler.
- `RegularZero`, `SuffixFlatZero`, `ClaimZero`, `flat_at_write_of_isOpen_rows`,
  `suffixFlatZero_of_flat_at_write`, the three statements of `Depth/RowsAux.lean` and
  `Depth/TanhZero.lean` belong to part A. I read them only as far as Checks 2 and 3 and (c) need.
- The computations are floating-point checks at random data (`check_path.py`: `d = 4`, six hidden
  units; `check_block.py`: `d = 2`, three hidden units, `κ = 0.2`).
- Of the paper I read Section 2, Theorem 5.2 with the text after it, and Appendix D.1 to D.3, D.6
  up to Lemma D.18, "Parameters that satisfy all conditions", Lemma D.20 and D.7. I did not read
  the rest for this audit.
