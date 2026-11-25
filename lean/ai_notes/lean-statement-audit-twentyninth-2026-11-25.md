STATUS: complete

# Twenty-ninth audit of Lean statements against the papers (25 November 2026)

Subject: S Lemma A.18 from both ends for gated blocks; S Proposition A.35 for ReGLU blocks of width at least `d`, and "On it" (the bound at every point of the open set) for ReLU, ReLU² and ReGLU blocks; S Theorem A.28 (iii) for skipless blocks with fewer than `d` hidden units. Four files of `lean/SkipsLean/`: `Dimension/UpperBoundTwoSidedGated.lean` (2 theorems), `Depth/InactiveGateTwoSided.lean` (3), `Depth/InactiveUnitEveryPoint.lean` (5), `Residual/FewerHiddenUnitsNarrow.lean` (1 definition, 5 theorems). S is the skips paper, D the dimension paper (`<scratchpad>/skips.txt`, `<scratchpad>/dim.txt`).

**Result.** Nothing false, nothing vacuous, nothing drifted in the four files. The five statements that conclude "at almost every parameter" (and the two that assume it) are for every Haar measure. The two statements from both ends for gated blocks are true (exact ranks), and each hypothesis is needed at some parameter; for ReGLU "the read has rank `d`" is not enough, the general position of its columns is. Proposition A.35 for ReGLU is the paper's within its Scope; `d_out ≥ d` is needed, and on the open set of the paper's proof the bound fails for `d_out < d` when block 2 is the last block with exactly `d` units (exact rank 7 against 6, 24 against 23, 22 against 20). "On it" is the paper's statement for ReLU and ReGLU (the batches of its functional dimension) and stronger for ReLU². Theorem A.28 (iii) for all widths is the paper's within its Scope; the paper's wording names no `d_in`, `d_out` and needs them (a residual GELU block equals a skipless one with `2 d_out` more units, since `gelu(z) − gelu(−z) = z`). Five corrections for the index.

## Commits read; `sorry`

- Commits of `/home/claude/lp` (branch `lean-plus`): `203fb9b` when the reading began (the four files were copied to `/home/claude/audit29/src/` at that commit); `2d7158d` when the axioms were printed again; `3359405` for the index (check 6); `d296e3c` at the end.
- Between `203fb9b` and `d296e3c`, in the four files: `Residual/FewerHiddenUnitsNarrow.lean` got its proofs (`1ed8b03`, `1330bf0`, `0baca2a`); the only lines removed from it are the four `sorry`, so no statement changed. The other three files did not change. The four index rows did not change, except "in work" to "proved" for the fourth.
- Files with `sorry`: at `203fb9b`, `Residual/FewerHiddenUnitsNarrow.lean` (4: `inputRank_skipless_le`, `le_inputRank_residual_mlp_zero`, `ae_le_inputRank_residual_mlp_zero`, `ae_forall_eval_residual_ne_skipless_of_card_lt`; the fifth theorem is proved from them); from `0baca2a` on, none of the four.
- Compiled by the reader at `2d7158d` (`Chk29.lean`, against the existing build): each of the 15 public theorems of the four files depends on `propext`, `Classical.choice`, `Quot.sound` only; no `sorryAx`.

How each check was done is said in the check: *reading*, *compiled* (a file in `/home/claude/audit29/`, with `lake env lean` against the existing build, nothing written there), *computed* (Python, `python3 -I`, scripts in `/home/claude/audit29/`), or *argued* (an argument of the reader, written out, checked by nobody else).

## Part 1: checks

### 1. Generic means almost every parameter, for every Haar measure: YES

*Reading.* The statements with `∀ᵐ`:

```lean
-- Depth/InactiveGateTwoSided.lean
theorem exists_isOpen_gateInactive_reglu_bound_of_le [Nonempty d]
    (μ : Measure (Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut)) [μ.IsAddHaarMeasure] … :
    ∃ U : Set (Params …), IsOpen U ∧ U.Nonempty ∧ (∀ θ ∈ U, GateInactive θ ℓ.succ j) ∧
      ∀ᵐ θ ∂μ, θ ∈ U → funDim (Arch.gated relu id hid) 0 θ + (…) ≤ Module.finrank ℝ (Params …)
theorem not_ae_funDim_add_eq_reglu_skipless_of_le [Nonempty d] (μ : …) [μ.IsAddHaarMeasure] … :
    ¬ ∀ᵐ θ ∂μ, funDim (Arch.gated relu id hid) 0 θ + (…) = Module.finrank ℝ (Params …)
-- Depth/InactiveUnitEveryPoint.lean (as a hypothesis)
    (μ : Measure (Params A dIn dOut)) [μ.IsAddHaarMeasure] {U : Set (Params A dIn dOut)} (hU : IsOpen U) (k : ℕ)
    (hae : ∀ᵐ θ ∂μ, θ ∈ U → funDim A S θ + k ≤ Module.finrank ℝ (Params A dIn dOut))
-- Residual/FewerHiddenUnitsNarrow.lean
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)) [μ.IsAddHaarMeasure] … :
    ∀ᵐ θ ∂μ, Fintype.card T * Fintype.card d ≤ inputRank (Arch.mlp σ id hid) 1 θ 0
    ∀ᵐ θ ∂μ, ∀ (L' : ℕ) (A' : Arch T d L'), … → ∀ η : Params A' dIn dOut, eval (Arch.mlp σ id hid) 1 θ ≠ eval A' 0 η
    ∀ᵐ θ ∂μ, ∀ m : Fin L → ℕ, … → ∀ η : Params (…), eval (Arch.mlp gelu id hid) 1 θ ≠ eval (…) 0 η
```

Each is for every measure `μ` with `[μ.IsAddHaarMeasure]` on the space of all parameters, and the quantifier over the other network (`A'`, `η`, the widths `m`) stands inside the `∀ᵐ`: one null set of residual parameters serves for all of them. None says "there is a parameter". In the two statements of `InactiveUnitEveryPoint.lean` the `∀ᵐ` is a hypothesis for the same given Haar measure, and the conclusion is at every point; the three `…_forall` statements of that file have no measure at all (they take `Measure.addHaar` inside the proof). The index types have `Fintype`: `T`, `d`, `dIn`, `dOut` and `hid ℓ` in the `variable` lines of each file; the read and write index types of a general `Arch` (`A`, `A'`) carry it as the fields `fr`, `fw` of the structure.

Statements at one parameter: the two of `UpperBoundTwoSidedGated.lean`, `funDim_add_le_of_eventually_gateInactive_of_rank_E_D` and `le_inputRank_residual_mlp_zero`. Each names its conditions (ranks, nonzero columns and rows, general position, invertible factors), and for the last two the next statement of the file gives the same conclusion at almost every parameter. The form of Lemma A.18 from both ends has no statement "at almost every parameter" of its own; its six conditions are obtained at almost every parameter inside the proof of `exists_isOpen_gateInactive_reglu_bound_of_le` (`ae_rank_E_write`, `ae_rank_D_read`, `ae_value_ne_zero`, `ae_gate_ne_zero`, `ae_write_row_ne_zero`, `ae_read_cols_generalPosition`, for `d_in, d_out ≥ d` and at least `d` hidden units in every block). The paper has no sentence "at generic parameters" for this form, so nothing is missing against it.

*Compiled* (`Chk29.lean`, 8 seconds; at `203fb9b` and again at `2d7158d`): instances at `Measure.addHaar` with numbers.

- `g1`, `g2`: two ReGLU blocks of width exactly `d = 2`, `d_in = d_out = 2`, one token (`P = 32`): a nonempty open set on which the gate of unit `j` of the second block is closed and `funDim + 24 ≤ 32` at almost every point of it; and not `funDim + 20 = 32` at almost every parameter.
- `e1`, `e2`, `e3`: the three "On it" statements for the same sizes (ReLU and ReLU²: `P = 24`, the bound `rank + 19 ≤ 24`, resp. `funDim + 19 ≤ 24`; ReGLU: `rank + 24 ≤ 32`).
- `n1`, `n2`, `n3`: two GELU blocks of width 3, `d = d_in = 3`, `d_out = 4`, two tokens: the rank of the Jacobian in the input at `0` is at least `2·3` at almost every parameter; the residual network equals no skipless network with a write of fewer than 3 rows; and the theorem for all widths with `2 (m_0 + m_1) < 18`, given Sard's theorem. `n2'`: from `n2`, the residual network equals no skipless network of two GELU blocks of the widths 7 and 2 (here `2·9 < 18` is false: the narrow case does not use the count).

All nine depend on `propext`, `Classical.choice`, `Quot.sound` only (recompiled at `2d7158d`; at `203fb9b` `n1`, `n2`, `n2'`, `n3` also showed `sorryAx`, through the four statements then in work).

### 2. From both ends, gated blocks (`Dimension/UpperBoundTwoSidedGated.lean`): true; each hypothesis is needed at some parameter; after block `m` the hypotheses ask `2 s > d`, not `s ≥ d`

```lean
theorem cobDir_add_rescaleDir_injective_of_rank_E_D
    (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut) (m : Fin L)
    (hE : θ.E.rank = Fintype.card d) (hD : θ.D.rank = Fintype.card d)
    (hw : ∀ ℓ, ℓ < m → (θ.write ℓ).rank = Fintype.card d)
    (hr : ∀ ℓ, m < ℓ → (θ.read ℓ).rank = Fintype.card d)
    (hv : ∀ ℓ, ℓ ≤ m → ∀ i, (fun a => θ.read ℓ a (Sum.inr i)) ≠ 0)
    (ha : ∀ ℓ, m < ℓ → ∀ i, (fun a => θ.write ℓ i a) ≠ 0) :
    Function.Injective fun p : (Fin (L + 1) → Matrix d d ℝ) × (∀ ℓ, hid ℓ → ℝ) =>
      cobDir θ p.1 + rescaleDir θ p.2

theorem cobDir_add_rescaleDir_add_rescaleDirGate_injective_of_rank_E_D (k : ℕ)
    (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut) (m : Fin L)
    (hE) (hD) (hw) (hv)
    (hg : ∀ ℓ, ℓ ≤ m → ∀ i, (fun a => θ.read ℓ a (Sum.inl i)) ≠ 0)
    (ha)
    (hgp : ∀ ℓ, m < ℓ → ∀ S : Finset (hid ℓ ⊕ hid ℓ), S.card ≤ Fintype.card d →
      LinearIndependent ℝ fun j : S => (θ.read ℓ)ᵀ j)
    (hcard : ∀ ℓ, m < ℓ → Fintype.card d < Fintype.card (hid ℓ ⊕ hid ℓ)) :
    Function.Injective
      fun p : (Fin (L + 1) → Matrix d d ℝ) × (∀ ℓ, hid ℓ → ℝ) × (∀ ℓ, hid ℓ → ℝ) =>
        cobDir θ p.1 + rescaleDir θ p.2.1 + rescaleDirGate k θ p.2.2
```

Below, (a) is the first statement (rescalings of the values, any gate) and (b) the second (rescalings of values and gates, ReGLU for `k = 1`); `s_ℓ` is the number of hidden units of block `ℓ`, whose read has the `2 s_ℓ` columns `[gates | values]`.

*Reading.* `cobDir θ X` is `E X_0`, `−X_{ℓ−1} W_read^ℓ`, `W_write^ℓ X_ℓ`, `−X_L D`; `rescaleDir θ α` multiplies the value column of unit `i` by `−α_i` and its write row by `α_i`; `rescaleDirGate k θ β` multiplies its gate column by `β_i` and its write row by `−k β_i`: the derivatives of the paper's actions (value `v ↦ v/c`, write `↦ c·`write; gate `g ↦ c g`, write `↦ c^{−k}·`write). The two statements join the paper's two inductions at block `m`: the hidden states up to the one that block `m` reads from the embedding ("no column of a generic read vanishes, so `c_ℓ = 1`"; "the write has rank `d_model`, so `G_ℓ = I`"), those from the one it writes on from the readout ("rescalings act freely on the rows of a generic write, except that for ReGLU a row fixes only the product `cc′` of the gate and value scales of its unit; each read, of rank `d_model` and with generic columns, then forces `G_{ℓ−1} = I` and the remaining scales to be 1"). Nothing is asked of the write of block `m`, of the rank of its read, of the reads before it or of the writes after it (beyond nonzero columns and rows). The paper does not state this form.

**What general position asks.** `hgp` and `hcard` concern the blocks **after** `m` only, the side of the readout: of the `2 s_ℓ` columns of the read of such a block, gate and value columns taken together, any at most `d` are linearly independent, and there are more than `d` of them. This is the paper's "each read, of rank `d_model` and with generic columns" made exact, and it is the hypothesis of the existing form with the readout alone (`cobDir_add_rescaleDir_add_rescaleDirGate_injective_of_rank_D`). On the side of the embedding (blocks up to `m`) only nonzero gate and value columns are asked. In (a) the reads after `m` are asked to have rank `d`, no general position.

*Computed* (`c2_gated.py`, the reader's own: each map written as a matrix, exact ranks over the rationals with python-flint, random integer parameters in `[−5, 5]`, the hypotheses checked exactly at every draw, general position by all subsets; under one second; `k = 0, 1, 2` for (b)).

- **True at every draw at which the hypotheses hold:** (a) 45 draws, (b) 30 draws times three values of `k`: the rank is the number of unknowns. Sizes: `d = 2, 3, 4, 5`; one block with fewer than `d` units between wide ones (`(3,2,3)`, `(4,1,5)`, `(2,1,2,3)`, `(4,5,3,4)`); a narrow last block with `d_out ≥ d` (`(3,2)`, `(4,3,1)`); a narrow first block (`(2,3)`); the network without the dead unit (`(d, d−1)`, `(d, d−1, d)` for `d = 2, 3`). (At many draws with small integers the read columns are not in general position; the map was injective at all of those too.)
- **A narrow last block with `d_out < d`:** not injective. `d = 3`, units `(3,2)`: kernel of dimension 1 for `d_out = 2` and 2 for `d_out = 1`; `d = 2`, units `(2,1)`, `d_out = 1`: kernel 1; that is `(d − s_L)(d − d_out)`, for `cobDir` alone and with the rescalings alike. With a wide block behind the narrow one (`(3,2,3)`, `d_out = 1`) the map is injective although `D` has rank 1: `hD` is sufficient, not necessary.
- **A narrow first block with `d_in < d`** (`d = 3`, `d_in = 2`, units `(2,3)`): (a) is injective at the three draws, and (b) for `k = 1, 2` (for `k = 0` at two of the three; at the third a gate column of block 1 is zero), unlike the twin for MLP blocks (twenty-eighth audit: kernel 1). The block of two gated units reads `h_0` through four columns, at rank `d = 3`; with one unit (`2 s < d`) and `E` of rank 2 the kernel has dimension 1 (designed, case 8a).
- **Two adjacent blocks with fewer than `d` units.** For gated blocks this is not one case. A block reads through `2 s` columns and writes through `s` rows, so the hypotheses after `m` (`hr`: read of rank `d`; `hgp`, `hcard`: `2 s > d`) can hold for a block with `d/2 < s < d`. Units `(3,2,2,3)`, `d = 3`, `m` the second block: the hypotheses of (a) and (b) hold and the map is injective (3 draws). Units `(4,2,2,4)`, `d = 4` (`2 s = d`): (a) holds and is injective; (b) fails `hcard` and is injective at the draws. Units `(3,1,1,3)` and `(4,3,1,4)` (`2 s < d` for the second): not injective, kernel of dimension 2 `= (d − s_m)(d − 2 s_{m+1})`, the hidden state between them being written at rank `s_m` and read at rank `2 s_{m+1}`: Remark A.19 with the two ranks. Units `(1,2,2)` with `d = 3` and `(3,3,3)` with `d = 5` (every block has fewer than `d` units, `m` the first), and `(4,3,3,3)` with `d = 4`: the hypotheses hold (but `hgp` at one of the nine draws), and the map is injective at all nine.
- **Each hypothesis is needed at some parameter** (designed parameters; the other hypotheses of the same statement hold unless said):

| dropped | parameter | result |
|---|---|---|
| `hE` | `d = 3`, `E` of rank 2, block 1 (`m`) of one unit, block 2 of three units in general position | (a) 30 of 31; (b) 34 of 35; with `E = 1`: injective |
| `hD` | `d = 3`, block 1 of three units, block 2 (`m`) of one unit, `D` of rank 2 | (a) 29 of 31; (b) 33 of 35 |
| `hw` | `d = 3`, the write of block 1 of rank 2, block 2 (`m`) of one unit | (a) 30 of 31; (b) 34 of 35; with rank 3: injective |
| `hr` (a) | `d = 2`, block 1 (`m`) of one unit, block 2 of two units with a read of rank 1 | 14 of 15 |
| `hv` | a unit of block 1 with a zero value column and a zero write row | (a) 15 of 16; (b) 19 of 20; with a nonzero write row: injective |
| `hg` (b) | a unit of block 1 with a zero gate column and a zero write row | 19 of 20; with a nonzero write row: injective for `k = 1, 2` |
| `ha` (a) | `d = 2`, block 1 (`m`) of one unit writes `(1,0)`; block 2 of one unit, gate `e_1`, value `e_2`, zero write row | 13 of 14; with the write row `(1,1)`: injective |
| `ha` (b) | `d = 2`, block 1 (`m`) with a zero write; block 2 of two units, read in general position, zero write | 17 of 18; injective as soon as one write row of block 2, or the write of block 1, is not zero |
| `hgp` (b) | `d = 3`: block 1 (`m`) of one unit writes `(0,0,1)`; block 2 has the gates `e_1, e_1, e_3` and the values `e_2, e_2, e_3`: a read of rank 3 with `6 > 3` columns | 34 of 35 for `k = 0, 1, 2`; (a) is injective there; with a read in general position: injective |
| `hcard` (b) | `d = 2`, block 2 of one unit with gate `e_1`, value `e_2` (`2 s = d`), block 1 (`m`) with a zero write | 15 of 16; with the write `(1,1)`: injective; `d = 3`, block 2 of one unit (`2 s < d`): 29 of 31 |

So for (b) "the read has rank `d`" is not enough: in the example for `hgp` the matrix `Y = diag(β, −kβ, 0)` has every read column as an eigenvector and is killed by the write `(0,0,1)` of block `m`. The hypotheses are a sufficient set that follows the two inductions. They are not necessary: in the examples for `hv`, for `hg` (with `k ≥ 1`) and for `ha` the map is injective again as soon as the write row of the unit, resp. another write row, is not zero, as the earlier audits found for the twins. No hypothesis `k ≠ 0` is asked in (b), and none is needed: the statement held for `k = 0` at every draw (the twin for MLP blocks needs `k ≠ 0`; here a rescaling of a gate moves the gate column whatever `k` is).
- The coordinator's script (`ai_notes/locally_free_one_narrow_block_gated_check_2026-11-25.out`) has the same ranks in the cases that coincide (`(3,2,3)`: 44 and 52; `(3,2)`: 32 and 37, and 30 and 35 for `d_out = 1`; `(2,3)`: 32 and 37; `(3,1,1,3)`: 51 of 53 and 59 of 61; `(2,1,2)`: 21 and 26).

Verdict: true as stated; the infinitesimal form of S Lemma A.18 for a case the paper does not state (LEAN STRONGER than the lemma in the widths, with the conditions at one parameter in place of "generic").


### 3. Proposition A.35 for ReGLU (`Depth/InactiveGateTwoSided.lean`): SAME as the paper within its Scope; `d_out ≥ d` is needed, and without it the bound of the paper fails on the open set of its proof

```lean
theorem funDim_add_le_of_eventually_gateInactive_of_rank_E_D {L : ℕ} {hid : Fin L → Type} … {k : ℕ}
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z) (hσ0 : ∀ z : ℝ, z ≤ 0 → σ z = 0)
    (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) (m : Fin L) (j : hid m)
    (hθ : ∀ᶠ θ' in 𝓝 θ, GateInactive θ' m j)
    (hE) (hD) (hw) (hv) (hg) (ha) (hgp) (hcard) :        -- those of statement (b) of check 2
    funDim (Arch.gated σ id hid) 0 θ
        + ((L + 1) * Fintype.card d ^ 2 + 2 * ∑ ℓ, Fintype.card (hid ℓ) + (3 * Fintype.card d - 2))
      ≤ Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)

-- from here on: {L : ℕ} {hid : Fin (L + 1) → Type}
theorem exists_isOpen_gateInactive_reglu_bound_of_le [Nonempty d] (μ : …) [μ.IsAddHaarMeasure]
    (hdIn : Fintype.card d ≤ Fintype.card dIn) (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hhid : ∀ m, Fintype.card d ≤ Fintype.card (hid m)) (ℓ : Fin L) (j : hid ℓ.succ) :
    ∃ U : Set (Params …), IsOpen U ∧ U.Nonempty ∧ (∀ θ ∈ U, GateInactive θ ℓ.succ j) ∧
      ∀ᵐ θ ∂μ, θ ∈ U → funDim (Arch.gated relu id hid) 0 θ
          + ((L + 2) * Fintype.card d ^ 2 + 2 * ∑ m, Fintype.card (hid m) + (3 * Fintype.card d - 2))
        ≤ Module.finrank ℝ (Params …)

theorem not_ae_funDim_add_eq_reglu_skipless_of_le [Nonempty d] (μ : …) [μ.IsAddHaarMeasure]
    (hL : 0 < L) (hdIn) (hdOut) (hhid) :
    ¬ ∀ᵐ θ ∂μ, funDim (Arch.gated relu id hid) 0 θ
        + ((L + 2) * Fintype.card d ^ 2 + 2 * ∑ m, Fintype.card (hid m)) = Module.finrank ℝ (Params …)
```

**Clause by clause.** *Reading.*

| | S Proposition A.35, ReGLU | Lean |
|---|---|---|
| blocks | "skipless networks of `L ≥ 2` ReLU, ReLU² or ReGLU blocks without normalization" | `Arch.gated relu id hid`, `funDim … 0` (no skip, `χ = id`); the statement at one parameter is for any gate that is positively homogeneous of a degree `k` and vanishes on `z ≤ 0` |
| "`L ≥ 2`" | | at one parameter: blocks `Fin L`, any block `m` (also the first, if a gate is closed there); the two others: blocks `Fin (L + 1)` and `ℓ : Fin L`, so `L ≥ 1` and at least two blocks; the `not_ae` statement asks `hL : 0 < L` |
| the number | `P − (L + 1) d_model² − s − (3 d_model − 2)` | `(L + 1) d² + 2 ∑ d_hidden + (3d − 2)` is added to `funDim` and compared with `P` (no subtraction from `P` in ℕ); with the blocks `Fin (L + 1)` it is `(L + 2) d²`, the paper's count for `L + 1` blocks and `L + 2` hidden states. `s = 2 ∑ d_hidden`: one rescaling of the gate and one of the value per unit, the paper's `s` for ReGLU ("`s − 1` rescalings, or `s − 2` for ReGLU"). `3d − 2` is a subtraction in ℕ, and `d ≥ 1` in each statement (`[Nonempty d]`; at one parameter a nonzero column) |
| the dead unit | "a unit of block 2 is dead" | `GateInactive θ ℓ.succ j`: the gate of unit `j` of block `ℓ.succ` reads a number `≤ 0` at every token of every input; every block after the first and every unit of it (the paper's is `ℓ = 0`). A ReGLU unit `relu(z) w` puts out `0` exactly when its gate reads `z ≤ 0` or its value is `0` |
| the open set | "a nonempty open set of weights on which a unit of block 2 is dead" | `∃ U, IsOpen U ∧ U.Nonempty ∧ ∀ θ ∈ U, GateInactive θ ℓ.succ j`; the proof takes the set of `exists_isOpen_gateInactive_reglu` (`Depth/InactiveGateOpen.lean`), a neighbourhood of the paper's weights (`g_k = e_{i(k)}`, `v_k = e_{i(k)} − δ ∑_{j ≠ i(k)} e_j`, `r̂_k r = −1`); it needs at least `d` units in block `ℓ.castSucc` ("with every index `i ≤ d_model` used by some unit") |
| where | "On it" | at almost every point of `U`, every Haar measure (as D Proposition E.1); at every point: check 4 |
| widths | "at every width" in the sentence before; Scope: `d_hidden ≥ d_model`, `d_in, d_out ≥ d_model ≥ 2` | at least `d` units in every block, `d_in, d_out ≥ d ≥ 1` |
| the consequence | "so the equality condition fails there" | not `fd = P − (L+2) d² − s` at almost every parameter |

The twin `exists_isOpen_gateInactive_reglu_bound` (`Depth/InactiveGateReGLU.lean`, D Proposition E.1) asks more than `d` units in the block of the dead unit and nothing of `d_out`; the new statement puts `d_out ≥ d` in the place of "more than `d`". The statement at one parameter is the twin `funDim_add_le_of_eventually_gateInactive` with the conditions of check 2 (b) in the place of "every write has rank `d`, the write of block `m` without the row of the unit has rank `d`".

*Computed* (`c3_reglu.py`, the reader's own, 51 seconds; `c3b_patterns.py`, 13 seconds; `c3c_dout.py`, 9 seconds. One token; rational weights and integer inputs, the Jacobian by the chain rule in exact arithmetic, the rank over the rationals with python-flint. The Jacobian was compared with an exact 11-point difference stencil in every parameter at 16 inputs of four networks: difference 0.)

*The parameters.* Block 1 has exactly `d` units, with gates `G` and values `V` (`d × d`); `r` is the gate column of unit 1 of block 2 and `c_k` the write row `k` of block 1 times `r`. With `t = u G` and `M = G^{-1} V` the gate reads `z(u) = ∑_{k : t_k > 0} c_k t_k ∑_i t_i M_{ik}`. If every `c_k < 0`, every `M_{ik} < 0` for `i ≠ k`, and the symmetric part of `(|c_k| M_{ik})_{k,i}` is positive definite, then `z(u) ≤ 0` at every `u`, and `< 0` when a gate of block 1 is open (*argued:* the terms with `t_i ≤ 0` are `≥ 0` inside the bracket, the others form the positive definite quadratic form). The three conditions are strict inequalities in the weights, so they hold on an open set, which contains the paper's weights: at each parameter that satisfies them the gate is closed at every input at all nearby parameters, which is the hypothesis `hθ`. The script draws `G = 1 + ` small rationals, `V = 1 − δ(J − 1) + ` small rationals, `δ = 1/(2d²)`, the other weights integers in `[−4, 4]` with the rows of the write of block 1 turned against `r`; it checks the three conditions exactly (and the sign of the gate at 500 random rows), and the eight hypotheses of the statement at one parameter. A batch holds the inputs, of 300 or 400 random integer inputs, at which no gate pre-activation of any block vanishes (the batches of `exists_isOpen_gateInactive_reglu_forall`); at such an input the network is polynomial in the weights nearby, so the rank on the batch is a lower bound for `funDim` and for the paper's functional dimension. Many draws have further dead units and a small rank; the table has the largest rank over the draws at which the named hypotheses hold, and the number of draws that reach it.

| `d`, `d_in`, `d_out`, units | `P` | bound | hypotheses | largest rank | |
|---|---|---|---|---|---|
| 2, 2, 2, (2,2) | 32 | 8 | all hold (29 draws) | 8 (13 draws) | attained |
| 2, 3, 2, (2,2) | 34 | 10 | all hold (31) | 10 (19) | attained |
| 3, 3, 3, (3,3) | 72 | 26 | all hold (23) | 26 (10) | attained |
| 2, 2, 3, (2,2) | 34 | 10 | all hold (30) | 9 (19) | holds, 1 below |
| 3, 3, 4, (3,3) | 75 | 29 | all hold (15) | 28 (9) | holds, 1 below |
| 2, 2, 4, (2,2); 3, 3, 5, (3,3) | 36; 78 | 12; 32 | all hold (34; 14) | 10 (24); 30 (8) | holds, 2 below |
| **2, 2, 1, (2,2)** | 30 | 6 | all but `hD` (33) | **7** (17) | exceeded by `d − d_out = 1` |
| **3, 3, 2, (3,3)** | 69 | 23 | all but `hD` (23) | **24** (13) | exceeded by 1 |
| **3, 3, 1, (3,3)** | 66 | 20 | all but `hD` (21) | **22** (9) | exceeded by 2 |
| 2, 2, 2, (2,2,2): a third block behind | 44 | 12 | all hold (19) | 10 (1) | holds |
| 2, 2, 1, (2,2,2); 3, 3, 1, (3,3,3) | 42; 93 | 10; 32 | all but `hD` (20; 7) | 8; 29 | holds |
| 2, 2, 1, (2,3); 3, 3, 1, (3,4): more than `d` units (D E.1) | 36; 75 | 10; 27 | all but `hD` (33; 15) | 10 (5); 27 (8) | attained |
| 2, 1, 2, (2,2); 3, 2, 3, (3,3): `d_in < d` | 30; 69 | 6; 23 | all but `hE` | 3; 20 | holds |
| 2, 2, 2, (2,2); 3, 3, 3, (3,3): the paper's `G`, `V` for block 1 | 32; 72 | 8; 26 | all hold (31; 14) | 8 (21); 26 (10) | attained |
| 2, 2, 1, (2,2): the paper's `G`, `V` | 30 | 6 | all but `hD` (32) | **7** (18) | exceeded by 1 |

For the draw of largest rank a second batch of twice the size gave the same rank in every row. *Inputs from every pattern of open gates of block 1* (`c3b_patterns.py`: `t = uG` in each of the `2^d − 1` orthants with an open gate, 40 inputs each): `d = 2`, `d_out = 2`: rank 8; `d = 3`, `d_out = 3`: rank 26 with the random inputs (13 patterns of open gates in all), 25 on the pattern inputs alone; `d = 2`, `d_out = 1`: rank 7; `d = 3`, `d_out = 1`: rank 22 (14 patterns). (The eighth pattern, no gate of block 1 open, gives `h_1 = 0`: every gate of block 2 then reads `0`, the output is `0` at all nearby weights, and such an input is not in a batch of the Lean statement.)

So:

- **The bound holds at every draw with the hypotheses, and it is attained** for `d_out = d` (ranks 8, 10 and 26): the statement at one parameter is not vacuous and cannot be improved there.
- **`hD` is needed in the statement at one parameter.** At 17 parameters with `d = 2`, `d_out = 1` every hypothesis of `funDim_add_le_of_eventually_gateInactive_of_rank_E_D` holds except `hD` (`E` and the write of block 1 have rank 2, no gate or value column vanishes, the gate is closed at every input at all nearby parameters by the certificate), and the Jacobian has rank 7 on a batch, against the conclusion `funDim ≤ 6`.
- **The bound of S Proposition A.35 for ReGLU fails on the open set of its proof when block 2 is the last block, has exactly `d_model` units and `d_out < d_model`:** rank 7 against 6, 24 against 23, 22 against 20, also at the paper's own `G` and `V` (last row); the rank on a batch is lower semicontinuous, so the bound fails on an open subset. This is outside the Scope of the main text (`d_out ≥ d_model`) and inside the words of the proposition, which names no `d_out`; the twenty-eighth audit found the same for ReLU and ReLU². The excess is `d − d_out`, as check 2 predicts (the kernel `(d − s_L)(d − d_out)` with `s_L = d − 1` live units). With more than `d` units in the block of the dead unit, or a further block behind it, the bound held at every draw without `d_out ≥ d`.
- **For `d_out > d` the bound is not attained** when the block of the dead gate is the last and has exactly `d` units: the largest rank is the bound minus `d_out − d` (1 below for `d_out = d + 1`, 2 below for `d_out = d + 2`, `d = 2, 3`). *Argued:* the `d − 1` live units write `h_L` into a subspace of dimension `d − 1`; the readout matters only on it, so the `d_out` directions `D ↦ D + cψ` (`c` in the kernel of the write) are flat, and the changes of basis at `h_L` give only `d` of them. The same count gives the excess `d − d_out` when `d_out < d`. In one formula, for this case: the rank is at most the paper's bound minus `(d_out − d)`, and this was attained at every size computed. This is a remark on the sharpness of the bound, not on its truth.
- `d_in ≥ d` was not found to be needed (the two cases with `d_in < d` are below the bound); Lean asks it, as the Scope does.

**The form of the statement.** As for the twins (twenty-eighth audit, check 6): `exists_isOpen_gateInactive_reglu_bound_of_le` says that *some* nonempty open set with a closed gate has the bound almost everywhere. Read literally this is weaker than what is proved: on the open set on which all gates of block `ℓ.succ` are closed (the paper's weights with the same `r` for every unit) the network is identically zero and `funDim = 0`, which is below the bound for any `d_out`. The content is in the statement at one parameter and in the choice of the set. The paper's sentence has the same form. `not_ae_funDim_add_eq_reglu_skipless_of_le` is the paper's "so the equality condition fails there" read as: the equality `fd = P − (L+2) d² − s` does not hold at almost every parameter.

Verdict: SAME as S Proposition A.35 for ReGLU blocks under the Scope, with "almost every point" for "On it" (as D Proposition E.1); LEAN STRONGER than D E.1 in the width (exactly `d` allowed) at the price of `d_out ≥ d`, which is needed.


### 4. "On it" (`Depth/InactiveUnitEveryPoint.lean`): the general step is true, and each hypothesis is needed; the three statements are the paper's "On it the functional dimension is at most" (ReLU, ReGLU: SAME; ReLU²: LEAN STRONGER); for Lean's `funDim` the bound is also true at every point for ReLU and ReGLU, only not proved

```lean
theorem jacobianRank_add_le_of_ae_of_contDiffOn {L : ℕ} {A : Arch T d L} (hA : A.χ = id)
    (S : Fin L → Matrix d d ℝ) (V : ∀ ℓ, Set (Matrix T (A.r ℓ) ℝ)) (hVo : ∀ ℓ, IsOpen (V ℓ))
    (hf : ∀ ℓ, ContDiffOn ℝ 1 (A.f ℓ) (V ℓ))
    (μ : Measure (Params A dIn dOut)) [μ.IsAddHaarMeasure]
    {U : Set (Params A dIn dOut)} (hU : IsOpen U) (k : ℕ)
    (hae : ∀ᵐ θ ∂μ, θ ∈ U → funDim A S θ + k ≤ Module.finrank ℝ (Params A dIn dOut))
    {θ : Params A dIn dOut} (hθ : θ ∈ U) {n : ℕ} (X : Fin n → Matrix T dIn ℝ)
    (hX : ∀ i ℓ, hidden A S θ (X i) ℓ.castSucc * θ.read ℓ ∈ V ℓ) :
    jacobianRank A S X θ + k ≤ Module.finrank ℝ (Params A dIn dOut)

theorem funDim_add_le_of_ae_of_contDiff {L : ℕ} {A : Arch T d L} (hA : A.χ = id)
    (S) (hf : ∀ ℓ, ContDiff ℝ 1 (A.f ℓ)) (μ) [μ.IsAddHaarMeasure] {U} (hU : IsOpen U) (k : ℕ) (hae)
    {θ : Params A dIn dOut} (hθ : θ ∈ U) : funDim A S θ + k ≤ Module.finrank ℝ (Params A dIn dOut)

theorem exists_isOpen_unitInactive_relu_forall [Nonempty d] (hdIn) (hdOut) (hhid) (ℓ : Fin L) (j : hid ℓ.succ) :
    ∃ U : Set (Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut),
      IsOpen U ∧ U.Nonempty ∧ ∀ θ ∈ U, UnitInactive θ ℓ.succ j ∧
        ∀ (n : ℕ) (X : Fin n → Matrix T dIn ℝ),
          (∀ (i : Fin n) (m : Fin (L + 1)) (t : T) (u : hid m),
            (hidden (Arch.mlp relu id hid) 0 θ (X i) m.castSucc * θ.read m) t u ≠ 0) →
          jacobianRank (Arch.mlp relu id hid) 0 X θ
              + ((L + 2) * Fintype.card d ^ 2 + ∑ m, Fintype.card (hid m) + (2 * Fintype.card d - 1))
            ≤ Module.finrank ℝ (Params …)
-- exists_isOpen_unitInactive_reluSq_forall: the same with  funDim (Arch.mlp reluSq id hid) 0 θ + (…) ≤ …  at every θ ∈ U
-- exists_isOpen_gateInactive_reglu_forall: GateInactive, batches with
--   (hidden (Arch.gated relu id hid) 0 θ (X i) m.castSucc * θ.read m) t (Sum.inl u) ≠ 0,  2 * ∑ …,  3 * Fintype.card d - 2
```

**(a) The general step is true as stated.** *Reading, and compiled* (it is proved; standard axioms). With `χ = id` and `f_ℓ` of class `C¹` on the open sets `V ℓ`, the map `θ' ↦ (F_θ'(x_1), …, F_θ'(x_n))` is `C¹` on the open set of the `θ'` at which the pre-activations on the batch stay in the `V ℓ`, so its rank at `θ` is at most its rank at every `θ'` near `θ`; a neighbourhood of `θ` inside the open set `U` has positive Haar measure, so it has a point `θ'` with `funDim θ' + k ≤ P`, and `jacobianRank X θ' ≤ funDim θ'` always. The stream matrices `S` are arbitrary (skipless, residual, learned skips). `k` is any natural number, and the statement is about `≤ P − k` written without subtraction.

**Each hypothesis is needed.** *Argued, with exact difference quotients for the example (`c4_staircase.py`).*

- `hX` (the batch has its pre-activations in the `V ℓ`). **For a general block map the statement is false without it.** Let `g(z) = sign(z)/n` for `1/(n+1) < |z| ≤ 1/n`, `g(0) = 0`, `g(z) = sign(z)` for `|z| > 1`, and `f = 1 + g`: a staircase with `|g(z) − z| ≤ 2z²`, so `f` is differentiable at `0` with `f′(0) = 1`, and locally constant on the open set `V = ℝ ∖ ({0} ∪ {±1/n})`. Take one token, `d = d_in = d_out = 1`, one block with one unit and this `f`, no skip, `χ = id`: `F(θ, x) = f(x E R) W D`, `P = 4`. At every `θ` with `E, R, W, D ≠ 0` (almost every `θ`): an input with `xER ∈ V` gives the row `c (0, 0, D, W)` in the coordinates `(E, R, W, D)`; the input `0` gives `(0, 0, D, W)`; at an input with `xER = ±1/n` the output jumps in `θ`, the batch is not differentiable and its `jacobianRank` is `0`. So `funDim θ = 1` and `funDim θ + 3 ≤ 4` at almost every `θ`, with `U` the whole space. At `θ_0 = (0, 1, 1, 1)` the batch `X = (0, 1)` is differentiable in `θ` with the rows `(0, 0, 1, 1)` and `(1, 0, 1, 1)` (computed quotients: `1.000000001`, `0`, `1`, `1`): rank 2, and `2 + 3 > 4`. Every hypothesis holds except `hX` (the pre-activations at `θ_0` are `0 ∉ V`).
- `hVo` (the `V ℓ` are open): the same example with `V = {0}`; every function is `C¹` on a one-point set in Mathlib's sense, `hX` then holds, and the conclusion fails.
- `hA` (`χ = id`): a network with no block and `χ = 1 + g`: `F(θ, x) = χ(xE) D`, rank 1 at almost every `θ`, rank 2 at `E = 0` on the batch `(0, 1)`. (For a `χ` of class `C¹`, such as RMSNorm with `ε > 0`, the step would hold too; it is not stated.)
- `hU` (`U` open), and a Haar measure: with `U = {θ_0}` or the zero measure the hypothesis `hae` is empty.

**For ReLU and ReGLU blocks the statement stays true on batches with a pre-activation at a kink** (this is (c) below): the example needs a block map that is not piecewise polynomial.

**(b) The three statements against "On it the functional dimension is at most".** *Reading.* The open set `U` is the one of the statements "at almost every point" (`exists_isOpen_unitInactive_relu_of_le`, `…_reluSq_of_le`, `exists_isOpen_gateInactive_reglu_bound_of_le`), the numbers are theirs (`(L + 2) d² + ∑ d_hidden + (2d − 1)`; for ReGLU `(L + 2) d² + 2 ∑ d_hidden + (3d − 2)`), the hypotheses `d_in, d_out ≥ d ≥ 1` and at least `d` units in every block are theirs, and the bound now holds at **every** `θ ∈ U`:

- **ReLU: SAME.** The paper (S line 2366 of the text, Appendix B, "Notation and flat directions"): "For the ReLU-type activations, `F(θ, x)` is differentiable in `θ` at the inputs `x` at which no hidden unit sits at its kink, which form an open set of full measure, and 'every input' means every such input." So the paper's functional dimension of a ReLU network is the largest rank over the finite batches of inputs at which no hidden unit sits at its kink (the fourth audit, 2.1: `fd_paper`). The Lean condition `∀ i m t u, (hidden … (X i) m.castSucc * θ.read m) t u ≠ 0` says exactly this of a batch: no unit `u` of no block `m` reads `0` at any token of any input of the batch (with `χ = id` the pre-activation is `h_{m−1} W_read`). On such a batch `jacobianRank` is the rank of the true Jacobian. So the statement is `fd_paper(θ) ≤ P − (L+2) d² − s − (2d − 1)` at every `θ ∈ U`.
- **ReGLU: SAME.** The condition is on the gate columns only (`Sum.inl u`). That is right: the unit is `relu(z) w` with the gate `z` and the value `w`; it is a polynomial in `(z, w)` on each side of `z = 0` and its only kink is at `z = 0`; a value `w = 0` is no kink.
- **ReLU²: LEAN STRONGER.** The block is `C¹`, the statement is for Lean's `funDim` (all inputs), which is at least the paper's functional dimension, at every `θ ∈ U`.

The three are existence statements, as their twins: "there is a nonempty open set with a dead unit at every point of which the bound holds"; the proof takes the set of the paper's proof (check 3, "The form of the statement").

*Not vacuous.* At a generic point of `U` there are many inputs at which no pre-activation vanishes, and the bound is attained on them (*computed* for ReGLU in check 3: ranks 8, 10 and 26 equal to the bound, on batches of 150 to 620 such inputs; for ReLU the twenty-eighth audit, check 6, has rank 5 equal to the bound on such inputs). At some points of `U` no input satisfies the condition (for instance `E = 0`, or a zero read column); there the statement says nothing and the paper's functional dimension, read literally, is `0`.

*A remark on the paper's words "which form an open set of full measure".* They are true for one block at generic weights (the kinks are hyperplanes of inputs). For a skipless network of two or more blocks they are not: if all units of block 1 are inactive at `u = xE` (for ReGLU: all gates closed), then `h_1 = 0` and every unit of block 2 sits at its kink. For ReGLU with the paper's weights (`g_k = e_{i(k)}`) this is the orthant of the `u` with no positive entry, and it has positive measure at all nearby weights; for a first block of exactly `d` ReLU units with independent reads it is a cone with interior too. At these inputs the output is `0` at all nearby weights, so they add nothing to any rank, and the bound is not affected; only the sentence is.

**(c) Is the bound false at some point of `U` for Lean's `funDim` in the ReLU case? No: it is true there too, and only not proved.** *Argued by the reader; not computed, not compiled.* Lean's `funDim` also counts a batch with an input at a kink when the outputs on the batch are differentiable in `θ` at `θ` all the same (if they are not, the batch has `jacobianRank = 0`). Claim: for blocks whose maps are piecewise polynomial (ReLU, ReLU², ReGLU), in the setting of the general step, `jacobianRank X θ_0 + k ≤ P` for every batch `X` and every `θ_0 ∈ U`, so `funDim θ_0 + k ≤ P` at every point of `U`.

1. The outputs on a batch are a continuous map `F_X` of `θ`, and the space of parameters is a finite union of semialgebraic sets `C_p` (given by the signs of the pre-activations on the batch) on each of which `F_X` equals a polynomial map `F_p`.
2. Let `F_X` be differentiable at `θ_0`. Along every ray `θ_0 + t v` the signs are constant for small `t > 0`, so the ray starts in one `C_{p(v)}`; the sets of directions `{v : p(v) = p}` are semialgebraic and finitely many, so one of them contains an open set of directions. For these `v`, `DF_X(θ_0) v = DF_p(θ_0) v`, and two linear maps that agree on an open set of directions are equal: `DF_X(θ_0) = DF_p(θ_0)`.
3. The part of `C_p` swept by these rays is semialgebraic of full dimension in every neighbourhood of `θ_0`, so `C_p` has interior points `θ'` arbitrarily near `θ_0`, inside `U`. Near such a `θ'`, `F_X = F_p`, so `jacobianRank X θ' = rank DF_p(θ')`.
4. If `rank DF_p(θ_0) > P − k`, the same holds near `θ_0` (the rank of the polynomial matrix `DF_p` is lower semicontinuous), hence on an open subset of `U` on which `jacobianRank X θ' > P − k`, hence `funDim θ' > P − k` there: against `hae`.

So the Lean statements for ReLU and ReGLU on batches are weaker than what is true for `funDim`, and they are exactly the paper's statement. The form "on every batch on which no pre-activation vanishes" is not forced by a counterexample; it is what the general step gives without the argument above (the example under (a) shows that some property of the block map beyond "`C¹` off the kinks" is needed for more).

Verdict: the general step is true and each hypothesis is needed; "On it" is SAME for ReLU and ReGLU, LEAN STRONGER for ReLU².


### 5. Theorem A.28 (iii) for narrow skipless blocks (`Residual/FewerHiddenUnitsNarrow.lean`): the narrow case is LEAN STRONGER than the paper's sentence; the theorem for all widths is SAME within the Scope; `d_in, d_out ≥ d` are needed, also for the paper's theorem

```lean
noncomputable def inputRank (A : Arch T d L) (S : Fin L → Matrix d d ℝ) (θ : Params A dIn dOut)
    (x : Matrix T dIn ℝ) : ℕ :=
  Module.finrank ℝ (LinearMap.range (fderiv ℝ (eval A S θ) x).toLinearMap)

theorem inputRank_skipless_le {A : Arch T d L} (hf : ∀ ℓ, Differentiable ℝ (A.f ℓ))
    (hχ : Differentiable ℝ A.χ) (θ : Params A dIn dOut) (x : Matrix T dIn ℝ) (ℓ : Fin L) :
    inputRank A 0 θ x ≤ Fintype.card T * Fintype.card (A.w ℓ)

theorem le_inputRank_residual_mlp_zero (hσ0 : σ 0 = 0) (hσ : DifferentiableAt ℝ σ 0)
    (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d) (hD : θ.D.rank = Fintype.card d)
    (hu : ∀ ℓ, IsUnit (1 + deriv σ 0 • (θ.read ℓ * θ.write ℓ)).det) :
    Fintype.card T * Fintype.card d ≤ inputRank (Arch.mlp σ id hid) 1 θ 0

theorem ae_le_inputRank_residual_mlp_zero (hσ0) (hσ) (μ : …) [μ.IsAddHaarMeasure]
    (hdIn : Fintype.card d ≤ Fintype.card dIn) (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, Fintype.card T * Fintype.card d ≤ inputRank (Arch.mlp σ id hid) 1 θ 0

theorem ae_forall_eval_residual_ne_skipless_of_card_lt [Nonempty T] (hσ0) (hσ) (μ : …) [μ.IsAddHaarMeasure] (hdIn) (hdOut) :
    ∀ᵐ θ ∂μ, ∀ (L' : ℕ) (A' : Arch T d L'), (∀ ℓ, Differentiable ℝ (A'.f ℓ)) →
      Differentiable ℝ A'.χ → (∃ ℓ, Fintype.card (A'.w ℓ) < Fintype.card d) →
      ∀ η : Params A' dIn dOut, eval (Arch.mlp σ id hid) 1 θ ≠ eval A' 0 η

theorem ae_forall_all_widths_eval_residual_ne_skipless_gelu [Nonempty T]
    (hSard : ∀ (m : Fin L → ℕ) (r : ℕ), SardCriticalValues
      (Params (Arch.mlp (T := T) (d := d) gelu id (fun ℓ => Fin (m ℓ))) dIn dOut) (Fin r → ℝ))
    (μ : …) [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn) (hdOut) :
    ∀ᵐ θ ∂μ, ∀ m : Fin L → ℕ,
      2 * ∑ ℓ, m ℓ < 2 * ∑ ℓ, Fintype.card (hid ℓ) + L * Fintype.card d →
      ∀ η : Params (Arch.mlp (T := T) (d := d) gelu id (fun ℓ => Fin (m ℓ))) dIn dOut,
        eval (Arch.mlp gelu id hid) 1 θ ≠ eval (Arch.mlp gelu id (fun ℓ => Fin (m ℓ))) 0 η
```

The paper (proof of Theorem A.28 (iii)): "If some `d'_hidden,ℓ < d_model`, the hidden state `h_ℓ` of the skipless network lies in a subspace of dimension `d'_hidden,ℓ`, so the Jacobian of its output with respect to the input has rank below `d_model` at every input. That of the residual network is `ED + O(τ)` at the parameters `θ_τ` of Lemma A.27, of rank `d_model` for small `τ`, so by analyticity it has rank `d_model` at some input for almost every choice of weights, and the two networks differ."

**`inputRank` and the factor `|T|`.** *Reading.* `inputRank A S θ x` is the rank of the derivative of `x ↦ F_θ(x)` at `x`, a linear map from `ℝ^{T × d_in}` to `ℝ^{T × d_out}` (and `0` where the network is not differentiable in `x`). The paper speaks of one token. An MLP block acts on each token alone, so for `|T|` tokens the Jacobian is block-diagonal with `|T|` blocks, each of the paper's rank: `|T| d'_hidden,ℓ` at most for the skipless network, `|T| d_model` for the residual one. So the factor is right for MLP blocks, and the comparison `|T| d' < |T| d` needs one token at least (`[Nonempty T]`).

**`inputRank_skipless_le` for every architecture.** *Reading; compiled for attention (`a1` in `Chk29.lean`).* The statement is for a general `Arch` with differentiable `f_ℓ` and `χ`. Without skips `h_ℓ = f_ℓ(χ(h_{ℓ−1}) W_read^ℓ) W_write^ℓ`, so the output is a differentiable function of `f_ℓ(…) ∈ ℝ^{T × w_ℓ}`, a space of dimension `|T| · |w_ℓ|`, and the rank of a composite is at most the dimension of the space in the middle: true for every kind of block, also one that mixes the tokens. For an attention block the rows of the write are the pairs (head, coordinate) (`w ℓ := H ℓ × dh ℓ`, the rows of the stacked `W_O`), so the bound is `|T| · H d_h`: it says something when the total head width is below `d`. For an MLP or gated block the rows are the hidden units. The statement covers `χ` a normalization with `ε > 0`; it does not cover ReLU blocks (not differentiable), where `inputRank` is `0` at the inputs at a kink.

**`le_inputRank_residual_mlp_zero`, recomputed.** *Computed* (`c5_narrow.py`, the reader's own, mpmath at 60 digits, derivatives in the input by central differences with step `10⁻²²`; under one second). With `σ(0) = 0` every hidden state vanishes at the input `0`, each block `h ↦ h + σ(h W_read) W_write` is differentiable at `0` with derivative `h ↦ h (I + σ′(0) W_read W_write)`, and the Jacobian of the network at `0` is `v ↦ v E ∏_ℓ (I + σ′(0) W_read^ℓ W_write^ℓ) D` on every token. For GELU (`σ′(0) = 1/2`), four networks (`|T| = 1, 2, 3`; `d = 2, 3, 4`; two to four blocks of 1 to 5 units): the largest entry of the difference between the computed Jacobian and `1_T ⊗ E ∏(I + RW/2) D` is below `2·10⁻⁴²`, and the rank is `|T| d` (6, 6, 4, 6). For skipless GELU networks with a narrow block (four networks, three inputs each) the rank was at most `|T|` times the smallest width (singular value number `|T| d' + 1` below `2·10⁻³⁸`). The coordinator's script (`narrow_skipless_input_rank_check_2026-11-25.py`) computes the same two things with complex steps.

*Each hypothesis is needed* (the same script, exact arithmetic where it says so):

| dropped | example | result |
|---|---|---|
| `σ(0) = 0` | `σ(z) = z² + 1` (so `σ′(0) = 0` and every factor of `hu` is `1`), one token, `d = d_in = d_out = 1`, `E = D = 1`, two blocks of one unit, `(r, w) = (1, 1)` and `(1, −1/2)` | `h_1(0) = 1`, the second block has the derivative `1 + 2 h_1 r² w = 0` there: the Jacobian at `0` is `0` (exact), rank 0 < 1. With one block the hypothesis is not needed (the block is entered at `h_0 = 0` whatever `σ(0)` is): derivative `1` (exact) |
| `hu` | GELU, `d = 1`, one block with `r w = −2` | the Jacobian at `0` is `1 + rw/2 = 0` (computed `4·10⁻⁶²`) |
| `hσ` | ReLU, `d = 1`, `r = w = 1`: the network is `x + max(x, 0)` | not differentiable at `0`, so `inputRank = 0`; Lean's `deriv relu 0` is `0`, so `hu` holds (*argued*) |
| `hE`, `hD` | | the Jacobian is `v ↦ v E M D`: rank at most (number of tokens) times the rank of `E`, and of `D` |

In `ae_le_inputRank_residual_mlp_zero` the three conditions hold at almost every parameter when `d_in, d_out ≥ d` (`det(I + c RW)` is a polynomial that is `1` at `R = 0`); no width is asked of the residual blocks, and a block with no unit is allowed. `d_in ≥ d` and `d_out ≥ d` are needed there (the rank is at most `|T| min(d_in, d, d_out)`).

**`ae_forall_eval_residual_ne_skipless_of_card_lt` against "If some `d'_hidden,ℓ < d_model` […] the two networks differ": LEAN STRONGER.** *Reading.* The paper's skipless network has `L` GELU blocks, one of them with fewer than `d_model` units. Lean: at almost every parameter of the residual network (MLP blocks with any activation that vanishes at `0` and is differentiable there, any widths, any number of blocks), for **every** depth `L'`, every architecture `A'` with differentiable blocks and a differentiable `χ` (MLP, gated or attention blocks, a normalization with `ε > 0`) that has a block whose write has fewer than `d` rows, and every parameter `η` of it: the two functions differ. One null set of `θ` serves for all `A'` and `η`. This is right: two equal functions have the same derivative at the input `0`, of rank `≥ |T| d` on one side and `≤ |T| |w_ℓ| < |T| d` on the other. The paper's case is the instance `A' = Arch.mlp gelu id (Fin ∘ m)` (*compiled:* `n2'` for the widths `(7, 2)`, `d = 3`, and inside the proof of the last theorem).

*`d_in, d_out ≥ d` and one token are needed for the statement, not only for this argument.*

- *Argued, for the statement as written (any differentiable blocks).* Let `σ` be differentiable (GELU) and write the residual network as `x ↦ Φ_θ(xE) D_θ`. If `d_out < d`: a network without skips with **one** block whose fixed map is `M ↦ Φ_θ(M) D_θ` (differentiable, from `ℝ^{T × d}` to `ℝ^{T × d_out}`), the read `1`, a write `W'` with `d_out` rows and a readout `D'` with `W' D' = 1` (they exist since `d_out ≤ d`) computes the same function, at **every** `θ`, and its write has `d_out < d` rows. If `d_in < d` and `E` has rank `d_in` (almost every `θ`): a first block with the fixed map `id` on `d_in` units, a read `R'` with `E R' = 1` and the write `E` gives `h_1 = xE` through a write of `d_in < d` rows; a second block with the fixed map `Φ_θ` and `D' = D_θ` gives the residual function. With no token all functions are equal.
- *Computed, for skipless GELU blocks of the same depth* (`c5_narrow.py`, part 4). `gelu(z) − gelu(−z) = z`: two GELU units compute a linear form. A residual network of one GELU block with `s` units is `xED + gelu(xER) WD`; for `d_out ≤ d` it equals a skipless block of `s + 2 d_out` units (the new units read `±` the columns of `D`), for `d_in ≤ d − s` one of `s + 2 d_in` units (the new units read `± x`), at every weight. Outputs compared at 20 inputs of two tokens, 60 digits: differences below `2·10⁻⁵⁹`.

| `d`, `d_in`, `d_out` | residual block | skipless block | fewer than `d` units | fewer than `L d/2` more units | difference |
|---|---|---|---|---|---|
| 4, 4, 1 | 1 unit | 3 units | yes | no (2 against 2) | `2·10⁻⁶⁰` |
| 5, 5, 1 | 1 unit | 3 units | yes | yes (2 < 2.5) | `2·10⁻⁶⁰` |
| 5, 5, 1 | 5 units | 7 units | no | yes (2 < 2.5) | `5·10⁻⁶⁰` |
| 9, 9, 2 | 9 units | 13 units | no | yes (4 < 4.5) | `2·10⁻⁵⁹` |
| 5, 1, 5 | 1 unit | 3 units | yes | yes | `4·10⁻⁶⁰` |
| 7, 1, 7 | 3 units | 5 units | yes | yes | `5·10⁻⁶⁰` |

So without `hdOut` (first two rows) or without `hdIn` (last two) the Lean statement for narrow blocks would be false, already for GELU blocks of the same depth, at every weight.

**What this says about Theorem A.28 (iii) as the paper words it.** The theorem reads "For GELU blocks with an embedding and a readout, without normalization, and almost every choice of weights, a residual network of `L` blocks equals no skipless network of `L` blocks with, in total, fewer than `L d_model / 2` more hidden units", with no condition on `d_in`, `d_out`. Rows 2 to 6 of the table are residual networks, with `d_out < d_model/4` or `d_in < d_model/4`, that equal such a skipless network at every weight; rows 3 and 4 have `d_hidden ≥ d_model` in both networks. So the theorem needs a condition on `d_in` and `d_out`. The Scope of the main text has it (`d_in, d_out ≥ d_model ≥ 2`), and the proof uses it through Lemma A.27 ("let `E` and `D` have rank `d_model`") and through "`ED + O(τ)` … of rank `d_model`"; the statement of Theorem A.28 does not say it, and the paper says that "the appendix states each result in greater generality". With `d_in, d_out ≥ d ≥ 2` the theorem is the Lean statement, proved given Sard's theorem.

**`ae_forall_all_widths_eval_residual_ne_skipless_gelu` against Theorem A.28 (iii): SAME within the Scope.** *Reading.*

| the paper | Lean |
|---|---|
| "GELU blocks with an embedding and a readout, without normalization" | `Arch.mlp gelu id …` for both networks, `Params` with `E` and `D` |
| "almost every choice of weights" (of the residual network) | `∀ᵐ θ ∂μ`, every Haar measure, one null set for all widths and all `η` |
| "a residual network of `L` blocks" with `d_hidden,1, …, d_hidden,L` units | stream matrices `1`, hidden units `hid ℓ` of any sizes (no `d_hidden ≥ d` is asked) |
| "equals no skipless network of `L` blocks" | `∀ m : Fin L → ℕ, … ∀ η, eval … 1 θ ≠ eval … 0 η`: the same `L`, stream matrices `0`, widths `m ℓ` of any size (also `0`) |
| "with, in total, fewer than `L d_model / 2` more hidden units" | `2 ∑ m_ℓ < 2 ∑ d_hidden,ℓ + L d`: the paper's `∑ (d'_hidden,ℓ − d_hidden,ℓ) < L d_model / 2` times two, without subtraction; it includes the skipless networks with fewer units in total |
| Scope: `d_in, d_out ≥ d_model ≥ 2` | `hd`, `hdIn`, `hdOut`; at least one token |
| "by Sard's theorem" (inside Lemma A.26) | the hypothesis `hSard`, for the parameter spaces of all skipless widths |

The proof splits as the paper's: every `m ℓ ≥ d` (`ae_forall_widths_eval_residual_ne_skipless_gelu`, seventh audit), or some `m ℓ < d` (the statement above, which needs no count). `d ≥ 2` and Sard's theorem come from the first case only (Lemma A.27 has "Let `d_model ≥ 2`"); the narrow case needs neither. Whether the theorem holds for `d = 1` was not checked.

*The paper's route and Lean's for the residual network: the same claim.* The paper: the Jacobian in the input is `ED + O(τ)` at `θ_τ`, of rank `d_model` for small `τ`, "so by analyticity it has rank `d_model` at some input for almost every choice of weights". Lean: it has rank `|T| d` **at the input `0`** at almost every `θ`, because there it is the polynomial `E ∏(I + σ′(0) RW) D` of the weights. Lean's claim names the input and implies the paper's; it uses `σ(0) = 0`, which GELU has, in the place of analyticity, and so also covers activations that are not analytic (ReLU², any `σ` that is differentiable at `0`). Both need `E` and `D` of rank `d`.

Verdict: `inputRank_skipless_le` SAME as the paper's sentence (LEAN STRONGER: every kind of differentiable block, `|T|` tokens); the residual side SAME in the claim, by another route; the narrow case LEAN STRONGER; the theorem for all widths SAME within the Scope, given Sard's theorem. The paper's own wording of (iii) lacks `d_in, d_out ≥ d_model`.

### 6. The index rows: true of the statements, with five corrections; all 15 theorems registered, standard axioms only

*Reading and a script* (the index and `checks/Axioms.lean` at `3359405`, copies in `/home/claude/audit29/`; at `d296e3c` the four rows and the 15 lines are the same). Each of the 15 public theorems of the four files stands in the row of its file, and each has its line `#print axioms Skips.<name>` in `checks/Axioms.lean` (the ten of the first three files since `203fb9b`, the five of `FewerHiddenUnitsNarrow.lean` since `0baca2a`); the definition `inputRank` is named in its row. *Compiled* (`Chk29.lean`, at `2d7158d`, against the build of that commit): each of the 15 depends on `propext`, `Classical.choice`, `Quot.sound` only, and so do the reader's ten instances. (At `203fb9b` the five of the last file showed `sorryAx`; the four `sorry` were replaced by proofs at `1ed8b03` and `1330bf0`, and no statement changed: the only lines removed from the file between `203fb9b` and `3359405` are the four `sorry`.)

Row by row (the three rows of the first three files did not change between `203fb9b` and `3359405`; the fourth changed from "in work" to "proved"):

- `Dimension/UpperBoundTwoSidedGated.lean`: true of the two statements ("no rescaled read column of a block up to `m`": the value columns in the first, the gate and value columns in the second). It could say what check 2 found (correction 1).
- `Depth/InactiveGateTwoSided.lean`: true. "a nonempty open set on which the gate … is closed at every input, and the bound at almost every point of it": the statement says that such a set exists; the row of the twin for ReLU now says so, this one not yet (correction 2).
- `Depth/InactiveUnitEveryPoint.lean`: true of the five statements. For ReGLU the row does not say that these are the batches of the paper's functional dimension too (correction 3).
- `Residual/FewerHiddenUnitsNarrow.lean`: true, "proved" is right. "in a network without skips with differentiable blocks": the statement also asks a differentiable `χ`. "Theorem A.28 (iii) as the paper states it": within the Scope (correction 4).
- The paragraph "Not yet compared by such a reader (they go to the twenty-ninth audit …)" names the four files (correction 5).
- The headers of the four Lean files were read against the statements: nothing wrong.


## Part 2: the statements, file by file

| File | Lean name | Paper sentence | Verdict | Note |
|---|---|---|---|---|
| `Dimension/UpperBoundTwoSidedGated.lean` | `cobDir_add_rescaleDir_injective_of_rank_E_D` | S Lemma A.18, both inductions joined at a block `m`, gated blocks with the rescalings of the values; the paper does not state this form | LEAN STRONGER (a case the lemma does not state), in infinitesimal form, at one parameter | true at 45 of 45 draws with the hypotheses; each hypothesis needed at some parameter (check 2) |
| | `cobDir_add_rescaleDir_add_rescaleDirGate_injective_of_rank_E_D` | the same with the rescalings of gates and values (ReGLU): "each read, of rank `d_model` and with generic columns" | LEAN STRONGER, the same way | true for `k = 0, 1, 2` at 30 of 30 draws; "generic columns" is general position of the gate and value columns of the reads after `m`, more than `d` of them; rank `d` alone is not enough (exact example) |
| `Depth/InactiveGateTwoSided.lean` | `funDim_add_le_of_eventually_gateInactive_of_rank_E_D` | S Proposition A.35, proof, "The rank", for ReGLU | SAME as the step, at one parameter with the conditions written out | `hD` is needed (rank 7 against 6); the bound is attained for `d_out = d` |
| | `exists_isOpen_gateInactive_reglu_bound_of_le` | S Proposition A.35 for ReGLU: "There is a nonempty open set of weights on which a unit of block 2 is dead. On it … at most `P − (L + 1) d_model² − s − (3 d_model − 2)`" | SAME under the Scope, with "almost every point" for "On it" | an existence statement, as the paper's sentence; every block after the first, every unit |
| | `not_ae_funDim_add_eq_reglu_skipless_of_le` | "so the equality condition fails there" (Definition 4.3) | SAME under the Scope | |
| `Depth/InactiveUnitEveryPoint.lean` | `jacobianRank_add_le_of_ae_of_contDiffOn` | S Proposition A.33 (ii), proof: "the rank is at most … at generic points of this set, and by lower semicontinuity at all of them", used by A.35 ("As in the proof of Proposition A.33(ii)") | SAME as the step, for any blocks that are `C¹` on open sets | each hypothesis needed; false without `hX` for a block map that is not piecewise polynomial (check 4) |
| | `funDim_add_le_of_ae_of_contDiff` | the same for blocks that are `C¹` everywhere | SAME | |
| | `exists_isOpen_unitInactive_relu_forall` | S Proposition A.35, "On it the functional dimension is at most `P − (L + 1) d_model² − s − (2 d_model − 1)`", ReLU | SAME under the Scope | the batches are those of the paper's functional dimension (no unit at its kink) |
| | `exists_isOpen_unitInactive_reluSq_forall` | the same, ReLU² | LEAN STRONGER under the Scope | for Lean's `funDim`, which is at least the paper's |
| | `exists_isOpen_gateInactive_reglu_forall` | the same with `3 d_model − 2`, ReGLU | SAME under the Scope | only the gates are asked nonzero: the kink of a ReGLU unit is at its gate |
| `Residual/FewerHiddenUnitsNarrow.lean` | `inputRank` | "the Jacobian of its output with respect to the input" and its rank | SAME | for any number of tokens; `0` where the network is not differentiable in the input |
| | `inputRank_skipless_le` | "the hidden state `h_ℓ` of the skipless network lies in a subspace of dimension `d'_hidden,ℓ`, so the Jacobian … has rank below `d_model` at every input" | LEAN STRONGER | every architecture with differentiable blocks and `χ`; the bound (number of tokens) times the rows of the write, for every block |
| | `le_inputRank_residual_mlp_zero` | "That of the residual network is `ED + O(τ)` at the parameters `θ_τ` of Lemma A.27, of rank `d_model` for small `τ`" | DIFFERENT in the route, the same claim (rank `d_model` at some input), at one parameter | at the input `0`, with the conditions written out; each needed (`σ(0) = 0` from two blocks on) |
| | `ae_le_inputRank_residual_mlp_zero` | "so by analyticity it has rank `d_model` at some input for almost every choice of weights" | LEAN STRONGER | names the input `0`; any `σ` with `σ(0) = 0` that is differentiable at `0`; `d_in, d_out ≥ d` needed |
| | `ae_forall_eval_residual_ne_skipless_of_card_lt` | "If some `d'_hidden,ℓ < d_model` … and the two networks differ" | LEAN STRONGER | any depth, any differentiable blocks; `d_in, d_out ≥ d` and one token are needed for the statement |
| | `ae_forall_all_widths_eval_residual_ne_skipless_gelu` | S Theorem A.28 (iii) | SAME within the Scope (`d_in, d_out ≥ d ≥ 2`), given Sard's theorem as a hypothesis | the paper's wording names no `d_in`, `d_out` and needs them (check 5) |

Nothing false, nothing vacuous, nothing drifted.

## What the authors of the papers should know

Nothing in the four files is false, vacuous or misdescribed. On the papers:

1. **S Proposition A.35, ReGLU: the bound fails when block 2 is the last block, has exactly `d_model` units and `d_out < d_model`.** Exact ranks at parameters at which the gate is closed at every input on a neighbourhood, the paper's own block 1 among them: 7 against the bound 6 (`d_model = 2`, `d_out = 1`), 24 against 23 (`d_model = 3`, `d_out = 2`), 22 against 20 (`d_model = 3`, `d_out = 1`): the excess is `d_model − d_out`. The proposition names no `d_out` (the Scope of the main text has `d_out ≥ d_model`; the sentence before the proposition says "at every width"). The twenty-eighth audit found the same for ReLU and ReLU². With `d_out ≥ d_model`, or more than `d_model` units in block 2, or a further block behind it, the bound held at every parameter computed, and Lean proves the first two cases.
2. **The proof of A.35 ("The other columns are those of the network without this unit, whose symmetries are the changes of basis of its `L + 1` hidden states and … `s − 2` [rescalings] for ReGLU")** needs these symmetries to move the parameters of a network whose block 2 has `d_model − 1` units in as many independent directions. Lemma A.18 as stated does not give this (it asks width at least `d_model` in every block); the form from both ends does, when `E` and `D` both have rank `d_model`, and for ReGLU it asks of the blocks behind block 2 that the gate and value columns of the read are in general position (more than `d_model` of them): a read of rank `d_model` alone is not enough (exact example in check 2).
3. **For gated blocks the induction from the readout needs `2 d_hidden > d_model`, not `d_hidden ≥ d_model`:** a gated block reads through `2 d_hidden` columns. The statements from both ends hold with blocks of `d_model/2 < d_hidden < d_model` units behind block `m` (computed). In Remark A.19, a hidden state that is written at rank `m_w` and read at rank `m_r` has a family of dimension `(d_model − m_w)(d_model − m_r)` of changes of basis that fix the parameters (computed with `m_w ≠ m_r` in three cases, each with a kernel of dimension 2: `(3 − 2)(3 − 1)`, `(3 − 1)(3 − 2)`, `(4 − 3)(4 − 2)`); the remark has the case `m_w = m_r`.
4. **Sharpness of A.35 when block 2 is the last block with exactly `d_model` units:** the bound is attained for `d_out = d_model` (exact ranks 8 and 26) and is not attained for `d_out > d_model`: the largest rank is the bound minus `d_out − d_model` (the live units write into a subspace of dimension `d_model − 1`, and the readout matters only on it). One formula for the three cases: the bound minus `(d_out − d_model)`.
5. **"On it" (A.35) and "by lower semicontinuity at all of them" (A.33 (ii))** are, as the paper's convention has it, statements on the batches of inputs at which no hidden unit sits at its kink; Lean has them in this form for ReLU and ReGLU. For a block map that is only differentiable at a kink, the step from almost every point to every point is false on batches at the kink (example in check 4); for piecewise polynomial blocks it stays true there (argument in check 4, (c)).
6. **"which form an open set of full measure"** (of the inputs at which no hidden unit sits at its kink, S Appendix B, "Notation and flat directions") is not true for skipless networks of two or more blocks: where all units of block 1 are inactive, `h_1 = 0` and every unit of block 2 sits at its kink; for ReGLU with the weights of the proof of A.35 this is a whole orthant of `h_0`. The ranks are not affected (the output is `0` there at all nearby weights).
7. **S Theorem A.28 (iii) needs `d_in, d_out ≥ d_model` (or some such condition), and its statement does not name it.** Since `gelu(z) − gelu(−z) = z`, a residual GELU block with `d_hidden` units and `d_out` outputs equals a skipless GELU block with `d_hidden + 2 d_out` units at every weight; for `d_out < d_model/4` this is "fewer than `L d_model/2` more hidden units" (computed at 60 digits: `d_model = 5`, `d_out = 1`, 5 units against 7; `d_model = 9`, `d_out = 2`, 9 against 13). The same with `d_in` (units that read `± x`). The proof uses the condition (Lemma A.27: "let `E` and `D` have rank `d_model`"; "`ED + O(τ)` … of rank `d_model`"), and the Scope of the main text has it.
8. **The first case of the proof of A.28 (iii) can do without `θ_τ` and analyticity:** at the input `0` every hidden state of a residual GELU network vanishes, and the Jacobian in the input is `E ∏_ℓ (I + W_read^ℓ W_write^ℓ / 2) D` (recomputed at 60 digits), of rank `d_model` at generic weights when `d_in, d_out ≥ d_model`. The Lean proof goes this way. The case then holds for a skipless network of any depth and any differentiable blocks, and `d_model ≥ 2` and Sard's theorem are needed only for the other case.

## Corrections for `STATEMENTS.md`

1. Row of `Dimension/UpperBoundTwoSidedGated.lean`: true as it stands. Add: "Nothing is asked of the write of block `m`; behind block `m` the hypotheses ask a read of rank `d` (values) or more than `d` read columns in general position (ReGLU), so blocks with `d/2 < s < d` units are allowed there; the second statement holds for every `k`, also `k = 0`. Twenty-ninth audit: true at all draws with the hypotheses, each hypothesis needed at some parameter, a read of rank `d` is not enough for the second."
2. Row of `Depth/InactiveGateTwoSided.lean`: after "and the bound at almost every point of it" put, as in the row of `Depth/InactiveUnitTwoSided.lean`: "(the statement says that such a set exists; the proof takes the set of `exists_isOpen_gateInactive_reglu`, a neighbourhood of the paper's weights; `d_out ≥ d` is needed there: for two blocks of width `d = 2` and `d_out = 1` the rank is 7 against the bound 6, twenty-ninth audit)".
3. Row of `Depth/InactiveUnitEveryPoint.lean`: after "the rank on every batch on which no gate pre-activation vanishes is at most `P − (L+2) d² − s − (3d − 2)`" add "(the batches of the paper's functional dimension for ReGLU: the kink of a unit is at its gate)". Add: "The three are existence statements, with the open sets of the statements at almost every point. For ReLU and ReGLU the bound on Lean's `funDim` at every point of the set is not stated (it holds by an argument of the twenty-ninth audit for piecewise polynomial blocks, not formalized); the general step is false without the condition on the batch for a block map that is only differentiable at a kink."
4. Row of `Residual/FewerHiddenUnitsNarrow.lean`: for "in a network without skips with differentiable blocks" put "with differentiable blocks and a differentiable map `χ`". For "Theorem A.28 (iii) as the paper states it" put "Theorem A.28 (iii) within the Scope (`d_in, d_out ≥ d ≥ 2`, at least one token)", and add: "`d_in, d_out ≥ d` are needed and the paper's statement does not name them: a residual GELU block equals a skipless GELU block with `2 d_out` (or `2 d_in`) more units at every weight, since `gelu(z) − gelu(−z) = z` (twenty-ninth audit)."
5. The paragraph "Not yet compared by such a reader (they go to the twenty-ninth audit, begun at 02:08 UTC, 25 November)": take out the four files of this audit and add a sentence for it, for instance: "A twenty-ninth reader (25 November) compared `Dimension/UpperBoundTwoSidedGated.lean`, `Depth/InactiveGateTwoSided.lean`, `Depth/InactiveUnitEveryPoint.lean` and `Residual/FewerHiddenUnitsNarrow.lean` (15 theorems, one definition): nothing false, vacuous or drifted; the statements at generic parameters are for every Haar measure; the statements from both ends for gated blocks are true and each hypothesis is needed at some parameter; Proposition A.35 for ReGLU is the paper's within its Scope, and `d_out ≥ d` is needed (exact rank 7 against the bound 6); 'On it' is the paper's statement for ReLU and ReGLU; Theorem A.28 (iii) for all widths is the paper's within its Scope, and needs `d_in, d_out ≥ d`. Report: `lean-statement-audit-twentyninth-2026-11-25.md`."

## What could not be checked

- The proofs were not read (the brief asks for the statements). The reader did not build the library; single files were compiled against the existing build, at `203fb9b` and at `2d7158d`.
- Check 4 (c), that the bound holds for Lean's `funDim` at every point of the open set for ReLU and ReGLU, is an argument of the reader; it was not computed and not formalized. The examples of check 4 (a) for `hVo`, `hA` and `hU`, and the two constructions with general differentiable blocks in check 5, are arguments too (the staircase example for `hX` has its difference quotients computed; the GELU examples of check 5 are computed).
- The ranks of check 3 are for one token, `d = 2, 3`, two and three blocks, at 12 to 40 random parameters per size. A rank on a batch is a lower bound for the functional dimension: the values above the bound refute the bound; the values at or below it agree with the Lean proofs and prove nothing. In the three sizes with three blocks the largest rank stayed below the bound (10 against 12; 8 against 10 and 29 against 32 with `d_out = 1`), and it was not found out whether the bound is attained there.
- Whether `d_in ≥ d` is needed in the statements for ReGLU (the two cases computed with `d_in < d` are below the bound), and whether Theorem A.28 (iii) holds for `d = 1`.
- Nothing was computed for attention blocks; `inputRank_skipless_le` for them was read and compiled as an instance, with the differentiability of the attention map as a hypothesis.
- Sard's theorem is a hypothesis of the last statement, as in the twin file (seventh audit); it was not looked at again.
- The files written after this audit began (`Residual/BlocksAlone….lean`, `Residual/DepthRescaleOpen.lean`, `Residual/DepthReGLUOpen.lean` and others named in the index) were not read.
