STATUS: complete

# Fifth audit of Lean statements against the papers (24 November 2026)

Reader: an independent reader who did not write the statements. Scope: the ten Lean files written
after the fourth audit began (`Absorb/RMSNormRays.lean`, `Absorb/RMSNormGeneric.lean`,
`Absorb/RMSNormKinds.lean`, `Dimension/GenericRank.lean`, `Activations/Analytic.lean`,
`Depth/SuffixGated.lean`, `Depth/Cones.lean`, `Depth/StepGated.lean`,
`Depth/GeluGatedExplicit.lean`, `Depth/GeluGatedTheorem.lean`) and the rows and notes of
`STATEMENTS.md` that describe them.

Library: `/home/claude/lp/lean`, branch `lean-plus`. I began at commit `cf6ed62` and finished at
`d80fd1c`. Between the two, the proofs of `Absorb/RMSNormKinds.lean` (24) and of `Depth/Cones.lean`
(6) were written, two files outside the scope were added (`Activations/FarFromZero.lean`,
`Activations/MillsAtInfinity.lean`) and rows of `STATEMENTS.md` were changed. No statement and no
definition of the scope changed: checked with `git diff` (in `RMSNormKinds.lean` the removed
lines are the 24 `sorry`; in `Cones.lean` the six `sorry` and the last line of three statements,
written again with the same content) and by the elaborated forms of a compiled copy of each of
the two files. Line numbers of `STATEMENTS.md` are those of the file at `d80fd1c`
(403 lines).
Papers: the PDFs and `.tex` files in `/home/claude/lp/paper docs/`. "A" is the absorb paper, "D" the
dimension paper. Numbers of statements and equations are those of the PDFs (`pdftotext -layout`);
"tex N" is a line of the `.tex` file.

Nothing was changed under `/home/claude/lw`, `/home/claude/lp` or `/home/claude/skips_fix_gauges`.
The scratch files are in `/home/claude/audit5/`; each was compiled alone with `lake env lean`.

Short answer. **No Lean statement in the scope was found false, vacuous or changed in meaning by a
definition.** Theorem 4.3 of the absorb paper is stated and proved for residual networks of each of
the seven kinds of MLP block, and there the Lean statements are stronger than the paper's; for
"blocks of any kind" the Lean theorem carries one hypothesis (`SomeBlockNonzero`), which is a step
of the paper's proof, and attention blocks are not stated. The definitions `GoodForConesGated` and
`GoodForConesMlp`, with the separate hypothesis of independence over `ℚ`, are the paper's "good"
with one clause made explicit (the cones are not empty), and the paper's `θ†` is good in the Lean
sense for the positive orthant (machine-checked by me for `d = 2`, three hidden units, one block;
the existence statements of Lemma D.13 were proved in the library while I read). The five
statements of Lemma D.12 are the paper's lemma; at `d80fd1c` they are the only statements of the
scope with `sorry`, and ten statements rest on them.

---------------------------------------------------------------------------------------------------

## (1) Summary table

| Paper statement | Lean names | Verdict | The difference in one line |
|---|---|---|---|
| A Section 2, "Normalization" (tex 210): for `ε = 0`, "defined at", and "equal if they agree on a dense set of inputs at which both are defined" | `DefinedAt` (old), the conclusion `¬ ∃ S, Dense S ∧ ∀ X ∈ S, DefinedAt … ∧ DefinedAt … ∧ eval … = eval …` | **SAME** | The Lean conclusion is word for word the negation of the paper's equality. Lean's total `rmsRow 0 0 = 0` changes nothing, because only inputs at which both networks are defined are compared. |
| A Appendix A.3, "Comparison" (tex 842): what equality forces of the weights of the residual network | `TurnGeneric` | **SAME** | `E`, `D` of rank `d`, and the exact negation of "for every `n̄` with rows of norm `√d`, each row of `∑_ℓ a_ℓ(n̄) W_write^ℓ` is a multiple of the same row of `n̄`" (machine-checked). |
| A Theorem 4.3 under the conditions of its proof (Appendix A.3, "The skipless network", "The residual network", "Comparison") | `exists_ne_skipless_rmsNorm_of_turn`, `not_dense_eq_skipless_rmsNorm_zero_of_turn` | **LEAN STRONGER** (than this part of the proof) | Skipless network: an arbitrary `Arch` (any maps `f′_ℓ`), own depth `L′ ≥ 0`, own model dimension, own `ε′ > 0`; only continuous for `ε = 0`. The hypothesis `0 < ε` on the residual network is not used. |
| A Appendix A.3, "Measure zero" (tex 844) | `SomeBlockNonzero`, `ae_turnGeneric`, `ae_someBlockNonzero_mlp`, `ae_someBlockNonzero_gated`, `locallyLipschitz_f_mlp`, `locallyLipschitz_f_gated` | **DIFFERENT in form, same content** | The paper's sentence "`a_1` vanishes for all `n̄` only if the read of block 1 has a zero column" is a hypothesis of the general statement (for an arbitrary `Arch` it is false), and it is proved for MLP and gated blocks whose activation or gate does not vanish on the positive reals. |
| **A Theorem 4.3** (tex 355), "blocks of any kind" | `ae_ne_skipless_rmsNorm`, `ae_not_dense_eq_skipless_rmsNorm_zero` | **PART** (conditional) | For an arbitrary residual `Arch` with locally Lipschitz `f_ℓ`, under the hypothesis `∀ᵐ θ, SomeBlockNonzero A θ`. No Lean statement discharges it for attention blocks or for a network that mixes kinds. |
| **A Theorem 4.3** for MLP blocks | `ae_ne_skipless_rmsNorm_mlp`, `…_zero_mlp`, `…_gated`, `…_zero_gated`, the fourteen of `RMSNormKinds.lean`, with the ten facts on the five activations | **LEAN STRONGER** for the seven kinds of MLP block; **PART** of the theorem | Residual network: one kind per network (tanh, GELU, ReLU, ReLU², SwiGLU, GeGLU, ReGLU), `d_in, d_out ≥ d ≥ 2`, one hidden unit somewhere (the paper: at least `d` in every block). Skipless network: as in the row above. Not stated: attention blocks. |
| D Appendix D.7, second paragraph (tex 1576): "the outputs on `X` are real-analytic in `θ` … At generic parameters the Jacobian on `X` therefore has at least the rank (13)" | `analyticOnNhd_eval_params`, `ae_jacobianRank_ge`, `ae_jacobianRank_le_funDim`, `ae_funDim_ge` | **LEAN STRONGER** | For every network with real-analytic `f_ℓ` and `χ`, all stream matrices, every batch and every `θ₀`: at generic `θ` the rank on the batch is at least the rank at `θ₀`. |
| D Section 1.1 (tex 133): "These four kinds of block are real-analytic" | `analyticOnNhd_gaussPdf`, `analyticOnNhd_gaussCdf`, `analyticOnNhd_gelu`, `analyticOnNhd_silu`, `analyticOnNhd_f_gated` (with the old `analyticOnNhd_tanh`, `analyticOnNhd_f_mlp`) | **SAME** | Stated for the fixed maps `f_ℓ`; `analyticOnNhd_f_gated` for every real-analytic gate. The paper's sentence is in Section 1.1, not in Section 2. |
| D Claim `(D_k)` for gated blocks, eq. (19) (tex 933-943) | `ClaimGated` | **SAME** (cases (n) and (+)) | `g = ⊤` or `antisymmetric d`; `Δ_ℓ` is `α ℓ`; the three entries of (19) are those of the definition (machine-checked). |
| D Lemma D.5 (tex 965), gated blocks | `claimGated_last`, `claimGated_last_rmsNorm` | (n): **LEAN STRONGER**; (+): **SAME** | In the case (n) the hypothesis "`D` has rank `d`" is not needed. At least one token. |
| D Proposition D.4 (tex 953), gated blocks | `flat_le_cobDir_add_rescaleDir_of_claimGated`, `funDim_of_claimGated`, and the two with `_rmsNorm` | **SAME**, slightly **STRONGER** | Any real-analytic gate. "Are the directions" is one inclusion here, the other is in older statements; "rank (13) on some finite batch" is `funDim = P − (L+1) dim G − s` (both checked by machine to give the paper's form). |
| D Appendix D.5, "Cones and good parameters" (tex 1127-1135) | `IsOpenConvexCone`, `frozenGated`, `frozenMlp`, `GoodForConesGated`, `GoodForConesMlp`, with the hypotheses `hQ` | **SAME** | Added clause: the cones are not empty (the paper uses it). (K1) with the active sets as data is equivalent to the paper's (K1) (machine-checked). (K3)'s independence over `ℚ` is a separate hypothesis. |
| D Appendix D.5, "A good `θ` is regular" (tex 1137-1142) | `regular_of_goodForConesGated_swiglu`, `…_geglu`, `regular_of_goodForConesMlp_gelu` | **SAME** | Three statements, one per kind. Proved in the source at `d80fd1c` (they had `sorry` when I began). |
| D Lemma D.13 (tex 1300-1315) | `exists_goodForConesGated_cols`, `exists_goodForConesGated_outer`, `exists_goodForConesMlp_outer` | **LEAN WEAKER** | Existence of cones, active sets and a good parameter with (K3). The explicit `θ†`, the positive orthant, `A_ℓ = {1, …, d}` and `g°_ℓ(n) = n`, `(n𝟙) n` are not stated (they are private in the proof). Enough for the use in D.7. Proved in the source at `d80fd1c`. |
| **D Lemma D.12** (tex 1190) | `claimGated_castSucc_swiglu`, `…_swiglu_rmsNorm`, `…_geglu`, `…_geglu_rmsNorm`, `claimRMS_castSucc_gelu` | **SAME** (not proved) | Five statements for the five settings; hidden states with rows `T` (equivalent to one token, by hand); `sorry`. |
| D Appendix D.7, "`(D_0)` holds at `θ†`" (tex 1576) | the five `exists_regular_claim…` | **LEAN WEAKER** in form | "There is a regular parameter (with no vanishing value column) at which `(D_0)` holds", not "at `θ†`". They rest on Lemma D.12 (`sorry`). |
| **D Theorem 5.2 (ii) for `ε > 0`, and (iii)** (tex 330) | `ae_funDim_gelu_skipless_rmsNorm`, `ae_funDim_swiglu_skipless`, `…_swiglu_skipless_rmsNorm`, `ae_funDim_geglu_skipless`, `…_geglu_skipless_rmsNorm` | **SAME** for these clauses; **PART** of Theorem 5.2 | Hypotheses and counts are the paper's. Not stated: (i) and (ii) for `ε = 0`, and "so the network satisfies the equality condition". They rest on Lemma D.12 (`sorry`). |

---------------------------------------------------------------------------------------------------

## (2) Definitions new in these files

The old definitions (`Arch`, `Params`, `hidden`, `eval`, `rmsRow`, `rmsNorm`, `funDim`,
`jacobianRank`, `flat`, `suffix`, `SuffixFlat`, `Claim`, `ClaimRMS`, `Regular`, `cobDir`,
`rescaleDir`, `antisymmetric`, `DefinedAt`, `Arch.mlp`, `Arch.gated`) are those of the earlier
audits; I read each again where a new file uses it and say below what the new use is.

### 2.1 `TurnGeneric A θ` (`Absorb/RMSNormRays.lean:44-49`)

```
structure TurnGeneric (A : Arch T d L) (θ : Params A dIn dOut) : Prop where
  rank_E : θ.E.rank = Fintype.card d
  rank_D : θ.D.rank = Fintype.card d
  turn : ∃ n : Matrix T d ℝ, (∀ t, n t ⬝ᵥ n t = (Fintype.card d : ℝ)) ∧
    ∃ t, ∀ c : ℝ, (∑ ℓ, A.f ℓ (n * θ.read ℓ) * θ.write ℓ) t ≠ c • n t
```

Elaborated: the instance arguments are `[Fintype d] [Fintype dOut]` only; `T` need not be finite.

The paper (Appendix A.3, tex 826-842, PDF p. 25): "Outside a set of weights of measure zero, `E` and
`D` have rank `d_model`, so that `XE` takes every value in `ℝ^{T×d_model}` and `vD = 0` only for
`v = 0`", and at the end of "Comparison": "So equality requires that for every such `n̄`, each row
of `∑_ℓ a_ℓ(n̄) W_write^ℓ` is a multiple of the same row of `n̄`", where "such `n̄`" are the values
"whose rows have norm `√d_model`".

Clause by clause.
- `rank_E`, `rank_D`: the two rank conditions of the paper. The proof uses `rank_E` to find an
  input `X₀` with `X₀ E = n̄` and `rank_D` to pass from `ρ(X) = DN_0(XE)[β(X)] D = 0` to
  `DN_0(XE)[β(X)] = 0`, as the paper does.
- `n t ⬝ᵥ n t = d`: every row of `n̄` has squared norm `d`, the paper's "norm `√d_model`".
- `∑ ℓ, A.f ℓ (n * θ.read ℓ) * θ.write ℓ`: the paper's `β = ∑_ℓ a_ℓ(n̄) W_write^ℓ` with
  `a_ℓ(n̄) = f_ℓ(n̄ W_read^ℓ)`. The paper says of `a_ℓ`: "a function of the normalized state `n` that
  block `ℓ` reads … It depends on the read of block `ℓ` only." In an `Arch` this dependence is
  through the product `n̄ W_read^ℓ`, which is the form of an MLP block, of a gated block and of an
  attention block whose read holds `[W_Q | W_K | W_V]`.
- `∃ t, ∀ c, … t ≠ c • n t`: some row of `β(n̄)` is not a multiple of the same row of `n̄`.
- So `turn` is the negation of the paper's necessary condition for equality. Machine-checked
  (`T43.lean`, example (1)): `TurnGeneric A θ ↔ rank E = d ∧ rank D = d ∧ ¬ (∀ n̄ with rows of
  squared norm d, ∀ t, ∃ c, β(n̄)_t = c • n̄_t)`.

Edge cases (machine-checked in `T43.lean`): with no block (`L = 0`) `TurnGeneric` is false
(`β = 0 = 0 • n̄_t`); with `d = 1` it is false (every row is a multiple of a nonzero row), which is
why `2 ≤ card d` is a hypothesis of `ae_turnGeneric` and is the paper's `d_model ≥ 2`; with `d`
empty it is false. If `T` is empty it is false (no row `t`).

### 2.2 `SomeBlockNonzero A θ` (`Absorb/RMSNormGeneric.lean:41-42`)

`∃ ℓ, ∃ n : Matrix T d ℝ, (∀ t, n t ⬝ᵥ n t = d) ∧ A.f ℓ (n * θ.read ℓ) ≠ 0`.

The paper ("Measure zero", tex 844): "The subspace is proper if some `a_ℓ(n̄)` has a nonzero entry
`(r, j)` at some `n̄` … And `a_1` vanishes for all `n̄` only if the read of block 1 has a zero column,
which happens on a set of measure zero." `SomeBlockNonzero` is the first sentence's hypothesis:
some `a_ℓ(n̄) ≠ 0`. It depends on the reads only, as the Fubini argument needs. The second sentence
is not a definition in Lean: it is the hypothesis `hA : ∀ᵐ θ ∂μ, SomeBlockNonzero A θ` of the general
theorems, and the two statements `ae_someBlockNonzero_mlp`, `ae_someBlockNonzero_gated` prove it
for the paper's MLP blocks. See 3.3 for why a hypothesis is right here.

### 2.3 `DefinedAt` and the conclusion for `ε = 0` (new use of an old definition)

`DefinedAt A S θ X := ∀ (k : Fin (L + 1)) (t : T), hidden A S θ X k t ≠ 0` (`Absorb/Limits.lean:56`;
machine-checked to unfold to this, `T43.lean` (6)).

The paper (A Section 2, "Normalization", tex 210, PDF p. 4): "For `ε = 0`, `N` is defined only on
hidden states without zero rows. A network is then defined at the inputs at which no state that it
normalizes has a zero row. Two such networks are equal if they agree on a dense set of inputs at
which both are defined."

- The states that a network normalizes are `h_0, …, h_{L−1}` (read by the blocks) and `h_L` (read by
  the readout): all `L + 1` hidden states, for a residual network and for a skipless one. So
  `DefinedAt` is the paper's "defined at". For a network with no block it says that `XE` has no
  zero row.
- The Lean conclusion for `ε = 0` is
  `¬ ∃ S : Set (Matrix T dIn ℝ), Dense S ∧ ∀ X ∈ S, DefinedAt A 1 θ X ∧ DefinedAt A' 0 θ' X ∧ eval A 1 θ X = eval A' 0 θ' X`.
  "The two networks are equal" in the paper's sense is `∃ S, Dense S ∧ ∀ X ∈ S, (both defined at X)
  ∧ (they agree at X)`. The Lean conclusion is its negation, word for word. It is equivalent to "the
  set of the inputs at which both are defined and agree is not dense" (machine-checked, `T43.lean`
  (5)).
- What Lean's total function changes. In Lean `rmsRow 0 0 = 0`, so `eval` has a value at every
  input. At an input at which a network is defined in the paper's sense, the Lean value is the
  paper's value (the recursion normalizes only states without zero rows). The conclusion compares
  the two networks only at such inputs. So the totalization changes nothing in the statements for
  `ε = 0`. (It would matter in a statement that compares values at inputs where a network is not
  defined; no statement in the scope does; 3.1 names the one place where it could be read so.)

### 2.4 `ClaimGated g θ k` (`Depth/SuffixGated.lean:48-57`)

```
def ClaimGated (g : Submodule ℝ (Matrix d d ℝ)) (θ : Params (Arch.gated σ χ hid) dIn dOut) (k : Fin (L + 1)) : Prop :=
  ∀ (Z : Matrix d d ℝ) (η : Params (Arch.gated σ χ hid) dIn dOut),
    SuffixFlat (Arch.gated σ χ hid) θ k Z η →
    ∃ (X : Fin (L + 1) → Matrix d d ℝ) (α : ∀ ℓ, hid ℓ → ℝ),
      X k = Z ∧ (∀ ℓ, k ≤ ℓ → X ℓ ∈ g) ∧
      (∀ ℓ : Fin L, k ≤ ℓ.castSucc →
        η.read ℓ = -(X ℓ.castSucc * θ.read ℓ) + (rescaleDir θ α).read ℓ ∧
        η.write ℓ = θ.write ℓ * X ℓ.succ + (rescaleDir θ α).write ℓ) ∧
      η.D = -(X (Fin.last L) * θ.D)
```

The paper (D Appendix D.3, tex 933-943, PDF p. 29): "Claim `(D_k)`, for `k = 0, …, L`. Let `Z` be a
`d × d` matrix and `η` a direction of the weights of the blocks `k+1, …, L` and of `D`. If (16)
holds, then `Z ∈ 𝔤`, and with `Z_k = Z` there are `Z_{k+1}, …, Z_L ∈ 𝔤` such that … For gated blocks
there are, in addition, diagonal matrices `Δ_{k+1}, …, Δ_L`, with `Δ_ℓ` of size `q_ℓ`, such that
`η = ({−Z_{ℓ−1} W_g^ℓ, −Z_{ℓ−1} W_v^ℓ − W_v^ℓ Δ_ℓ, Δ_ℓ W_write^ℓ + W_write^ℓ Z_ℓ}_{ℓ=k+1}^L, −Z_L D)` (19)."

Clause by clause.
- Quantifiers: for all `Z` and `η`, if (16) for `k` (`SuffixFlat … k Z η`, checked by the earlier
  audits), then there exist the `Z_ℓ` and `Δ_ℓ`. The same order as the paper.
- `X k = Z` is "`Z_k = Z`". `∀ ℓ, k ≤ ℓ → X ℓ ∈ g` is "`Z ∈ 𝔤`" (the case `ℓ = k`) and
  "`Z_{k+1}, …, Z_L ∈ 𝔤`". The entries `X ℓ` for `ℓ < k` are not constrained and occur nowhere else,
  so they carry nothing.
- Lean block `ℓ : Fin L` is the paper's block `ℓ + 1`; it reads `h_ℓ` (`ℓ.castSucc`) and writes
  `h_{ℓ+1}` (`ℓ.succ`). `k ≤ ℓ.castSucc` selects the paper's blocks `k+1, …, L`.
- The read: `−(X ℓ.castSucc * θ.read ℓ) + (rescaleDir θ α).read ℓ`. `rescaleDir θ α` has the read
  `0` at a gate column and `−α_i` times the value column at the value column of unit `i`. So the gate
  columns of `η` are `−Z_{ℓ−1} W_g`, and the value columns are `−Z_{ℓ−1} W_v − W_v Δ_ℓ` with
  `Δ_ℓ = diag(α ℓ)`. Machine-checked (`K1.lean`, section `eq19`): the gate entry has no term in `α`;
  the value entry is `−(Z W_read)_{k,inr i} − (W_v · diagonal (α ℓ))_{k i}`.
- The write: `θ.write ℓ * X ℓ.succ + (rescaleDir θ α).write ℓ`, and `(rescaleDir θ α).write ℓ` is
  `α_i` times row `i` of the write. Machine-checked: it equals
  `Matrix.diagonal (α ℓ) * θ.write ℓ + θ.write ℓ * X ℓ.succ`, the paper's
  `Δ_ℓ W_write^ℓ + W_write^ℓ Z_ℓ`. The signs of `Δ_ℓ` are those of (19): minus on the value columns,
  plus on the write.
- `η.D = −(X (Fin.last L) * θ.D)` is "`−Z_L D`".
- What is not constrained: the entry of `η` at `E` and the entries at the blocks before `k+1`. The
  paper's `η` has no such entries ("a direction of the weights of the blocks `k+1, …, L` and of
  `D`"). In Lean `η` is a full parameter, `SuffixFlat` does not depend on these entries (the network
  after `h_k` does not), and the conclusion says nothing of them. The same convention as `Claim`
  and `ClaimRMS`, which the earlier audits accepted. `α ℓ` for the blocks before `k+1` is likewise
  free and unused.
- `g`: `⊤` in the case (n), `antisymmetric d` in the case (+). The definition takes any subspace.
  The paper's table (D.2, PDF p. 27) gives `𝔤` = all matrices in (n), antisymmetric in (+). Gated
  blocks are not treated in the case (0) (paper, tex 742: "Gated blocks are treated in the cases
  (n) and (+) only").
- The direction `cobDir θ X + rescaleDir θ α` (the paper's `η^{Z,Δ}`, eq. (12)) has, by `rfl`, the
  entries that `ClaimGated` asks at the blocks and at `D` (machine-checked).
- Empty cases. If `T` is empty, (16) holds for every `Z` and `η`, so `ClaimGated` is false unless
  the space is trivial; all statements that use it have `[Nonempty T]`. If `hid ℓ` is empty, `α ℓ`
  is the empty function.

### 2.5 `IsOpenConvexCone C` (`Depth/Cones.lean:46-51`)

`isOpen`, `convex` (`Convex ℝ C`), `nonempty`, `zero_notMem`, `smul_mem : ∀ n ∈ C, ∀ λ > 0, λ • n ∈ C`,
for a set `C` of rows `d → ℝ` (the product topology, which is the topology of `ℝ^{1×d}`).

The paper (tex 1127): "A cone is a set of rows that contains `λh` for each of its rows `h` and every
number `λ > 0`. Let `C_0, …, C_L` be open convex cones in `ℝ^{1×d_model}` that do not contain `0`".

Same, with one clause added: `nonempty`. The paper needs it and does not say it: "the sign of
`n c_j` on `C_k`", "Let `ξ ∈ C_k`" (proof of Lemma D.12), "take `ξ ∈ C_{ℓ−1}` with `Dg°_ℓ(ξ)`
invertible" ("a good `θ` is regular"). Without it the empty set would satisfy the four other
clauses (machine-checked, `K1.lean`), the active sets would not be determined, and "good" would
not imply "regular". With `d` empty there is no cone in the Lean sense (machine-checked), so every
statement with a good parameter has `d ≥ 1` built in.

### 2.6 `frozenGated θ ℓ A n`, `frozenMlp θ ℓ A n` (`Depth/Cones.lean:55-63`)

`frozenGated θ ℓ A n = ∑ j ∈ A, ((n ⬝ᵥ c_j) * (n ⬝ᵥ e_j)) • a_j`, with `c_j = (θ.read ℓ)ᵀ (Sum.inl j)`
(gate column `j`), `e_j = (θ.read ℓ)ᵀ (Sum.inr j)` (value column `j`), `a_j = θ.write ℓ j` (write
row `j`). `frozenMlp θ ℓ A n = ∑ j ∈ A, (n ⬝ᵥ c_j) • a_j`, with `c_j = (θ.read ℓ)ᵀ j`.

The paper (K1, tex 1129-1133): `g°_ℓ(n) = ∑_{j ∈ A_ℓ} (n c_j) ι_j(n) a_j`, with `ι_j(n) = n e_j` in a
gated block and `ι_j(n) = 1` in a GELU block. Same. Rows and columns: `(M)ᵀ j` is column `j` of `M`
as a vector indexed by `d`, and `n ⬝ᵥ c` is the paper's `n c` for a row `n` and a column `c`. At the
paper's `θ†` (for `d = 2`, three hidden units) the Lean `frozenGated` is `n ↦ (n_1 + n_2) n`, the
paper's `g°_ℓ(n) = (n𝟙) n` (machine-checked, `Dagger.lean`, `frozen_dagger`).

### 2.7 `GoodForConesGated C A θ`, `GoodForConesMlp C A θ` (`Depth/Cones.lean:67-109`)

Fields of `GoodForConesGated` (elaborated; instance arguments `[Fintype d] [Fintype dOut]` and
`[∀ ℓ, Fintype (hid ℓ)]`; `σ`, `χ`, `T`, `dIn` are implicit and do not occur in any field):

| Field | Lean | Paper (tex 1127-1135) |
|---|---|---|
| `cone` | `∀ k : Fin (L+1), IsOpenConvexCone (C k)` | "open convex cones … that do not contain `0`, one for each hidden state" (+ nonempty) |
| `rank_E`, `rank_D`, `rank_write` | ranks `= card d` | (R1) |
| `gate_pos` | `∀ ℓ, ∀ n ∈ C ℓ.castSucc, ∀ j ∈ A ℓ, 0 < n ⬝ᵥ c_j` | (K1) |
| `gate_neg` | `∀ ℓ, ∀ n ∈ C ℓ.castSucc, ∀ j ∉ A ℓ, n ⬝ᵥ c_j < 0` | (K1) |
| `frozen_mem` | `∀ ℓ, ∀ n ∈ C ℓ.castSucc, frozenGated θ ℓ (A ℓ) n ∈ C ℓ.succ` | (K2), first half |
| `frozen_deriv` | `∀ ℓ, ∃ n : d → ℝ, Function.Injective (fderiv ℝ (frozenGated θ ℓ (A ℓ)) n)` | (K2), second half |
| `write_ne_zero` | `∀ ℓ j, θ.write ℓ j ≠ 0` | (K3): "No `a_j` vanishes" |
| `value_ne_zero` | `∀ ℓ j, (θ.read ℓ)ᵀ (Sum.inr j) ≠ 0` | (K3): "in a gated block no value column `e_j` vanishes" |

`GoodForConesMlp` has the same fields with the read columns as gate columns, `frozenMlp`, and no
`value_ne_zero`.

Clause by clause.
- **Which block reads which cone.** The paper's block `ℓ` (from 1) reads `C_{ℓ−1}` and its frozen
  block maps into `C_ℓ`. Lean block `ℓ : Fin L` (from 0) is the paper's block `ℓ + 1`: it reads
  `C ℓ.castSucc` (the paper's `C_ℓ`) and maps into `C ℓ.succ` (the paper's `C_{ℓ+1}`). Correct. In
  Lemma D.12 for `k : Fin L` the block between `h_k` and `h_{k+1}` is Lean block `k`; it reads
  `C k.castSucc = C_k` ("Let `ξ ∈ C_k`") and `h° = g°(ξ) ∈ C k.succ = C_{k+1}` ("which lies in
  `C_{k+1}` by (K2)"). Correct.
- **(K1).** The paper: "`n c_j ≠ 0` for every `n ∈ C_{ℓ−1}` and every `j`. So every gate has one
  sign on `C_{ℓ−1}`. Let `A_ℓ` be the set of the hidden units `j` with `n c_j > 0` on `C_{ℓ−1}`".
  Lean gives the set `A ℓ` as data and asks `> 0` on the cone for `j ∈ A ℓ` and `< 0` for `j ∉ A ℓ`.
  Machine-checked (`K1.lean`): for an `IsOpenConvexCone C` and columns `c_j`,
  `(∀ n ∈ C, ∀ j, n c_j ≠ 0) ↔ ∃ A, (∀ n ∈ C, ∀ j ∈ A, 0 < n c_j) ∧ (∀ n ∈ C, ∀ j ∉ A, n c_j < 0)`
  (the direction "⇒" uses convexity: on a segment a linear form that takes both signs vanishes),
  and then `j ∈ A ↔ ∀ n ∈ C, 0 < n c_j` (this uses `nonempty`). So the Lean pair is the paper's
  (K1), and the Lean `A ℓ` is the paper's `A_ℓ`. Nothing is lost or added.
- **(K2).** "`g°_ℓ(n) ∈ C_ℓ` for every `n ∈ C_{ℓ−1}`": `frozen_mem`. "`Dg°_ℓ(n)` is invertible at
  some row `n`": `frozen_deriv`, injectivity of the derivative at some row `n`, which for a linear
  map of `ℝ^d` to itself is invertibility. The row is not required to lie in the cone, in the
  paper as in Lean; the paper then takes "`ξ ∈ C_{ℓ−1}` with `Dg°_ℓ(ξ)` invertible", which exists
  because the determinant is a polynomial and the cone is open and not empty. `frozenGated` and
  `frozenMlp` are polynomial maps, so Mathlib's convention "`fderiv = 0` where a map is not
  differentiable" plays no part.
- **(K3).** "No `a_j` vanishes, and in a gated block no value column `e_j` vanishes": the two
  fields. "For GELU and GeGLU blocks the matrices `c_1 c_1^⊤, …, c_q c_q^⊤` are linearly independent
  over `ℚ`, and for SwiGLU blocks the columns `c_1, …, c_q` are": not a field. It is the hypothesis
  `hQ` of the statements that use it:
  `∀ ℓ, LinearIndependent ℚ (fun j : hid ℓ => (θ.read ℓ)ᵀ (Sum.inl j))` for SwiGLU,
  `∀ ℓ, LinearIndependent ℚ (fun j : hid ℓ => Matrix.vecMulVec c_j c_j)` for GeGLU (gate columns) and
  for GELU (read columns). `Matrix.vecMulVec c c` has the entries `c_i c_k`: the matrix `c c^⊤`.
  `LinearIndependent ℚ` uses the structure of `ℝ^d` and of the matrices as vector spaces over `ℚ`
  (it elaborates); independence with rational coefficients is the paper's independence with integer
  coefficients. The hypothesis is for every block `ℓ`, as the paper's "good" is.
- **"Good" = `GoodForCones…` + `hQ` of the kind.** With both, nothing of the paper's "good" is
  lost, and one clause is added (the cones are not empty). The split is by kind of block only: the
  structure does not see the gate `σ`, so one structure serves SwiGLU and GeGLU, and `hQ` says
  which independence the kind needs.
- **One token.** The cones are sets of single rows, as in the paper, although the claims are for
  hidden states with rows `T`. See 3.9.

**Is the paper's `θ†` good in the Lean sense, with the positive orthant as every cone?** Yes.
- By hand, for all `d ≥ 1`, `q_ℓ ≥ d`, `L`, `d_in, d_out ≥ d`, field by field. `cone`: the positive
  orthant is open, convex, not empty (the row of ones), does not contain `0` (for `d ≥ 1`), and is
  closed under positive multiples. (R1): `E`, `D` and every write contain the identity. `gate_pos`:
  for `j ≤ d`, `n c_j = n_j > 0`. `gate_neg`: for `j > d`, `n c_j = −μ_{j−d} (n𝟙) < 0`, with
  `A ℓ = {1, …, d}`. `frozen_mem`: `g°(n) = (n𝟙) n` (gated) or `n` (GELU), a positive multiple of
  `n`. `frozen_deriv`: the identity (GELU), or `v ↦ (n𝟙) v + (v𝟙) n` with determinant
  `2 (n𝟙)^d ≠ 0` (gated). `write_ne_zero`: rows of `I` and `𝟙^⊤`. `value_ne_zero`: `e_j = 𝟙`.
  `hQ`: as in the paper's proof of Lemma D.13.
- By machine, for `d = 2`, one gated block with three hidden units (`q = d + 1`, so that a unit
  that is not active is present), `d_in = d_out = 2`, any `σ`, `χ` and `T`
  (`/home/claude/audit5/Dagger.lean`): `good_dagger : 0 < μ → GoodForConesGated (fun _ => orthant)
  (fun _ => {0, 1}) (thetaDagger μ)`, with every field proved; `hQ_cols_dagger` (the gate columns
  `e_1, e_2, −μ𝟙` are independent over `ℚ` if `μ` is irrational); `hQ_outer_dagger` (the three
  matrices `c_j c_j^⊤` are independent over `ℚ` if `μ ≠ 0`). All three depend on the three standard
  axioms only. The file also applies `claimGated_castSucc_swiglu` to them: the hypotheses of the
  Lean Lemma D.12 can be met at the paper's parameter.

### 2.8 Definitions used in a new way

- `Regular (Arch.gated σ χ hid) θ`: the structure of `Depth/Suffix.lean` (R1 and R3), used for
  gated networks in both cases. (R3) of the paper does not involve `χ` ("`Dg_ℓ(n)` is invertible at
  some row `n`"), and `Regular.deriv_block` is about `n′ ↦ f_ℓ(n′ W_read) W_write`, without `χ`.
  For a hidden state with rows `T` the derivative acts on each row separately, so "injective at
  some `n : Matrix T d ℝ`" holds if and only if `Dg_ℓ` is invertible at each row of `n`; taking all
  rows equal gives the paper's (R3). Same as for tanh blocks.
- `rescaleDir θ α`: the direction of the rescalings of the values, used in `ClaimGated` as the
  three terms with `Δ_ℓ` of (19). See 2.4.
- `hv : ∀ ℓ i, (fun k => θ.read ℓ k (Sum.inr i)) ≠ 0`: "no value column vanishes", the form of
  `funDim_add_le_skipless_gated`. `GoodForConesGated.value_ne_zero` has the form
  `(θ.read ℓ)ᵀ (Sum.inr j) ≠ 0`; the two are the same function (the helper `value_col_ne_zero` of
  `GeluGatedExplicit.lean` passes from one to the other).
- `funDim`, `jacobianRank` with real-analytic `f_ℓ`, `χ`: the networks are differentiable in `θ`
  at every input, so the Lean `funDim` is the paper's functional dimension here (the difference
  that the fourth audit found for ReLU-type blocks does not arise).
- `Arch T d' L'` with `d' : Type` inside `∀ᵐ`: see 3.2.

---------------------------------------------------------------------------------------------------

## (3) One entry per statement

### 3.1 A Theorem 4.3, the comparison under the conditions of the proof

**Paper** (Theorem 4.3, PDF p. 8 and p. 25, tex 355): "Consider pre-RMSNorm networks, with `ε ≥ 0`
and blocks of any kind and width. For almost every choice of weights, a residual network equals no
skipless network, whatever its depth, widths and kinds of blocks." The proof (Appendix A.3,
tex 824-844) has four parts: "The skipless network" (its output at `tX` is `G(X) + O(1/t²)`; for
`ε = 0` it is the output at `X`), "The residual network" (its output at `tX` is
`N_0(XE) D + ρ(X)/t + O(1/t²)`), "Comparison" (equality forces the condition of 2.1), "Measure
zero".

**Lean** (`Absorb/RMSNormRays.lean:460`, `:682`; elaborated):

```
exists_ne_skipless_rmsNorm_of_turn :
  ∀ {T d dIn dOut} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] {ε ε' : ℝ},
  0 < ε → 0 < ε' → ∀ (A : Arch T d L), A.χ = rmsNorm ε → (∀ ℓ, LocallyLipschitz (A.f ℓ)) →
  ∀ (θ : Params A dIn dOut), TurnGeneric A θ →
  ∀ {L' : ℕ} {d' : Type u_5} [Fintype d'] (A' : Arch T d' L'), A'.χ = rmsNorm ε' →
  (∀ ℓ, LocallyLipschitz (A'.f ℓ)) → ∀ (θ' : Params A' dIn dOut),
  ∃ X : Matrix T dIn ℝ, eval A 1 θ X ≠ eval A' 0 θ' X

not_dense_eq_skipless_rmsNorm_zero_of_turn :
  … (A : Arch T d L), A.χ = rmsNorm 0 → (∀ ℓ, LocallyLipschitz (A.f ℓ)) →
  ∀ (θ : Params A dIn dOut), TurnGeneric A θ →
  ∀ {L' : ℕ} {d' : Type u_5} [Fintype d'] (A' : Arch T d' L'), A'.χ = rmsNorm 0 →
  (∀ ℓ, Continuous (A'.f ℓ)) → ∀ (θ' : Params A' dIn dOut),
  ¬ ∃ S : Set (Matrix T dIn ℝ), Dense S ∧
      ∀ X ∈ S, DefinedAt A 1 θ X ∧ DefinedAt A' 0 θ' X ∧ eval A 1 θ X = eval A' 0 θ' X
```

**Comparison.**
- The residual network: `eval A 1 θ` (stream matrices `1`), `χ = rmsNorm ε`, blocks of any kind as
  maps `f_ℓ` that are locally Lipschitz. The paper's proof: "being locally Lipschitz, it adds its
  output at `n̄` up to `O(1/t)`". Same. Different blocks may have different maps `f_ℓ`, so a network
  that mixes kinds is an instance.
- The weights: `TurnGeneric A θ` (2.1), what the paper's proof needs and no more.
- The skipless network: `eval A' 0 θ'`, an arbitrary `Arch T d' L'` with the same tokens `T`, the
  same `d_in` and `d_out` (they must be the same for the two functions to be compared), its own
  depth `L'` (also `L' = 0`, a network with no block, which the paper's `L ≥ 1` excludes), its own
  model dimension `d'` in any universe, its own widths, and its own maps `f′_ℓ`, any locally
  Lipschitz maps for `ε > 0` (the paper: "the rest of the network is locally Lipschitz") and any
  continuous maps for `ε = 0`. For `ε = 0` the paper's proof uses of the skipless network only that
  its output does not change along a ray and that both networks are continuous where they are
  defined, so continuity is enough; Lean confirms it.
- `ε`: for `ε > 0` the skipless network has its own constant `ε' > 0`. The paper has one `ε` for
  both. For `ε = 0` both have `ε = 0`. A residual network with `ε > 0` against a skipless network
  with `ε = 0`, and the converse, are not stated; the paper does not state them either.
- The hypothesis `0 < ε` of the first statement is not used by its proof. Machine-checked: a copy of
  the file with this hypothesis removed compiles, with the three standard axioms
  (`/home/claude/audit5/RaysCopy.lean`). So Lean proves the first conclusion for every real `ε` of
  the residual network, with Lean's total `rmsNorm ε`. For `ε = 0` that is a statement about values
  also at inputs at which the residual network is not defined in the paper's sense, so it is not
  the paper's statement for `ε = 0`; the statement as written (with `0 < ε`) does not claim it.
  `STATEMENTS.md` says this correctly.
- Conclusion for `ε > 0`: the two functions differ at some input. This is the negation of
  "equal", for networks defined at every input. For `ε = 0`: 2.3.
- Edge cases. `d = 1`, `L = 0`, `T` empty: `TurnGeneric` is false, the statements hold vacuously,
  and correctly so (for `L = 0` the residual network is a skipless network with no block).

**Verdict: LEAN STRONGER** than the corresponding three parts of the paper's proof: the skipless
network is more general (any maps, `L' = 0`, own `ε'`, continuous only for `ε = 0`), and `0 < ε` is
not needed for the first conclusion.

### 3.2 A Theorem 4.3, "Measure zero", and the theorem for blocks of any kind

**Paper** (tex 844): "Fix all weights but the writes. The condition is linear in the writes, so the
writes that satisfy it form a linear subspace. The subspace is proper if some `a_ℓ(n̄)` has a nonzero
entry `(r, j)` at some `n̄` … And `a_1` vanishes for all `n̄` only if the read of block 1 has a zero
column, which happens on a set of measure zero. The weights that satisfy the condition form a
closed set … and by Fubini's theorem this set has measure zero."

**Lean** (`Absorb/RMSNormGeneric.lean:229`, `:267`, `:286`; elaborated):

```
ae_turnGeneric : ∀ … (A : Arch T d L), (∀ ℓ, Continuous (A.f ℓ)) →
  ∀ (μ : Measure (Params A dIn dOut)) [μ.IsAddHaarMeasure],
  2 ≤ Fintype.card d → Fintype.card d ≤ Fintype.card dIn → Fintype.card d ≤ Fintype.card dOut →
  (∀ᵐ θ ∂μ, SomeBlockNonzero A θ) → ∀ᵐ θ ∂μ, TurnGeneric A θ

ae_ne_skipless_rmsNorm : ∀ … {ε : ℝ}, 0 < ε → ∀ (A : Arch T d L), A.χ = rmsNorm ε →
  (∀ ℓ, LocallyLipschitz (A.f ℓ)) → ∀ (μ : Measure (Params A dIn dOut)) [μ.IsAddHaarMeasure],
  2 ≤ card d → card d ≤ card dIn → card d ≤ card dOut → (∀ᵐ θ ∂μ, SomeBlockNonzero A θ) →
  ∀ᵐ θ ∂μ, ∀ (L' : ℕ) (d' : Type) [Fintype d'] (A' : Arch T d' L') (ε' : ℝ), 0 < ε' →
    A'.χ = rmsNorm ε' → (∀ ℓ, LocallyLipschitz (A'.f ℓ)) → ∀ θ' : Params A' dIn dOut,
      ∃ X : Matrix T dIn ℝ, eval A 1 θ X ≠ eval A' 0 θ' X

ae_not_dense_eq_skipless_rmsNorm_zero : the same with A.χ = rmsNorm 0, A'.χ = rmsNorm 0,
  (∀ ℓ, Continuous (A'.f ℓ)), and the conclusion of 2.3.
```

**Comparison.**
- "For almost every choice of weights": `∀ᵐ θ ∂μ` for an additive Haar measure on the parameters of
  the residual network (a Lebesgue measure; the convention of the earlier audits).
- Order of quantifiers: `∀ᵐ θ, ∀ (skipless network), …`. One set of measure zero serves all
  skipless networks. This is the paper's order ("for almost every choice of weights, a residual
  network equals no skipless network").
- `d' : Type` (universe 0) inside `∀ᵐ`, where a universe variable cannot be bound. Every finite
  index type is in bijection with some `Fin m : Type`, so no model dimension is lost. The statements
  `…_of_turn` have `d' : Type u_5`.
- Scope: `2 ≤ card d`, `card d ≤ card dIn`, `card d ≤ card dOut` are the paper's
  `d_in, d_out ≥ d_model ≥ 2` for the residual network. `d ≥ 2` is needed (2.1). `d_in ≥ d` and
  `d_out ≥ d` give `E` and `D` of rank `d` almost everywhere. Nothing is asked of the skipless
  network (the paper's Scope applies to all its networks).
- The hypothesis `hA : ∀ᵐ θ ∂μ, SomeBlockNonzero A θ`. For an arbitrary `Arch` it cannot be
  dropped. If no block has a nonzero output at the states that it reads, the residual network is
  the skipless network with no block and the same `E`, `D`: machine-checked
  (`/home/claude/audit5/Need.lean`, `eval_residual_eq_skipless_of_zero`). And this happens on a set
  of weights of positive measure for some continuous activations: for MLP blocks with
  `σ(z) = max(z − 1, 0)`, whenever every read column has norm below `1/√d` (by hand: the rows of a
  normalized state have norm at most `√d`, so every hidden unit reads a number below 1). So the
  paper's sentence "`a_1` vanishes for all `n̄` only if the read of block 1 has a zero column" is a
  property of the paper's kinds of block, and the Lean statements are right to make it a
  hypothesis for a general `Arch`.
- `ae_turnGeneric` asks only continuity of the `f_ℓ` (for the closed set), as the paper ("every
  `a_ℓ` is continuous in the read and in `n̄`").

**Verdict.** `ae_turnGeneric`: the paper's "Measure zero" with its second sentence as a hypothesis;
**DIFFERENT in form, same content**. `ae_ne_skipless_rmsNorm`, `ae_not_dense_eq_skipless_rmsNorm_zero`:
Theorem 4.3 for "blocks of any kind" **under the hypothesis `hA`**: **PART** as a statement of the
theorem (conditional), **LEAN STRONGER** on the side of the skipless network (3.1).

### 3.3 A Theorem 4.3 for MLP blocks and gated blocks, and for the seven kinds

**Lean** (`Absorb/RMSNormGeneric.lean:343-505`, `Absorb/RMSNormKinds.lean`).
- `locallyLipschitz_f_mlp`, `locallyLipschitz_f_gated`: an MLP block, a gated block, with a locally
  Lipschitz activation or gate has a locally Lipschitz map `f_ℓ`.
- `ae_someBlockNonzero_mlp`, `ae_someBlockNonzero_gated` (`[Nonempty T] [Nonempty d]`,
  `hσ : ∀ z, 0 < z → σ z ≠ 0`, `hhid : ∃ ℓ, Nonempty (hid ℓ)`, any `χ`): `∀ᵐ θ, SomeBlockNonzero`.
- `ae_ne_skipless_rmsNorm_mlp`, `ae_not_dense_eq_skipless_rmsNorm_zero_mlp`, and the two with
  `_gated`: Theorem 4.3 for `Arch.mlp σ (rmsNorm ε) hid`, `Arch.gated σ (rmsNorm ε) hid`, with
  `[Nonempty T]`, `hσ`, `hσL : LocallyLipschitz σ`, `hhid`, `2 ≤ card d`, `card d ≤ card dIn`,
  `card d ≤ card dOut`; conclusions as in 3.2.
- The ten facts: `locallyLipschitz_tanh`, `_gelu`, `_silu`, `_relu`, `_reluSq`;
  `tanh_ne_zero_of_pos`, `gelu_…`, `silu_…`, `relu_…`, `reluSq_…` (`σ z ≠ 0` for `z > 0`).
- The fourteen corollaries: `ae_ne_skipless_rmsNorm_K` and `ae_not_dense_eq_skipless_rmsNorm_zero_K`
  for `K` = `tanh`, `gelu`, `relu`, `reluSq` (`Arch.mlp`) and `swiglu`, `geglu`, `reglu`
  (`Arch.gated` with `silu`, `gelu`, `relu`). Each has `[Nonempty T]`, `hhid`, the three conditions
  on the dimensions, and the conclusion of 3.2.

**Comparison.**
- The seven kinds are the paper's seven kinds of MLP block (A Section 2: vanilla with tanh, GELU,
  ReLU, ReLU²; gated with ReLU (ReGLU), SiLU (SwiGLU), GELU (GeGLU)).
- "`a_1` vanishes for all `n̄` only if the read of block 1 has a zero column": for an MLP block the
  Lean proof takes a block with a hidden unit `i`, its read column `c ≠ 0` (almost everywhere) and
  the state with every row `√d c/‖c‖`; unit `i` then reads `√d ‖c‖ > 0`. This is why `σ` is asked not
  to vanish on the positive reals (the paper's five activations satisfy it). For a gated block the
  Lean proof uses in addition `c · e ≠ 0` for the gate column `c` and the value column `e` of the
  unit, true almost everywhere. Both are sets of measure zero of exceptions, as in the paper.
- Widths. The paper's Scope: "Every MLP block has at least `d_model` hidden units". Lean:
  `hhid : ∃ ℓ, Nonempty (hid ℓ)`, some block has one hidden unit. Weaker hypothesis; it gives `L ≥ 1`.
- One kind per residual network: `Arch.mlp σ … hid` and `Arch.gated σ … hid` have the same `σ` in
  every block. The paper's Scope says the same of MLP blocks ("all MLP blocks of a network are of
  one kind"), and adds: "Theorem 4.3 allows blocks of any kind, and so covers networks that
  alternate attention and MLP blocks, as transformers do." Such a network is an `Arch`, and the
  general theorem of 3.2 applies to it once `hA` is proved (the statement elaborates for an
  arbitrary `Arch`, `T43.lean` (7)); no Lean statement proves `hA` for it, and no attention block is
  defined in the library.
- The skipless network: an arbitrary `Arch`, so of any kind, mixed or not, with attention or not.
  A reader's instance compiles from the corollaries (`/home/claude/audit5/KindsTest.lean`): for
  almost every `θ`, a residual tanh network (`ε > 0`) differs at some input from every skipless
  SwiGLU network of any depth `L'`, model dimension `Fin m`, widths and `ε' > 0`; and for `ε = 0` the
  set of the inputs at which a residual ReGLU network and a skipless ReLU network are both defined
  and agree is not dense. Both instances depend on the three standard axioms only.
- Tokens: rows `T`, any nonempty finite set, as in the paper (`X ∈ ℝ^{T×d_in}`); nothing is reduced
  to one token.

**Verdict.** For residual networks of one of the seven kinds of MLP block: **LEAN STRONGER** than
the paper's theorem (weaker hypothesis on the widths; the skipless network may have its own `ε′`,
any maps, no block; continuity only for `ε = 0`). As a statement of Theorem 4.3: **PART**: attention
blocks in the residual network, and residual networks that alternate kinds, are covered only by
the conditional statement of 3.2.

**Would a reader of the paper accept these as the theorem?** Yes for the seven kinds of MLP block:
the hypotheses are the paper's Scope (or weaker), the conclusions are the negation of the paper's
two notions of equality, and the class of skipless networks contains the paper's. A reader would
ask for two things more before saying "Theorem 4.3 is formalized": a residual network with
attention blocks (the paper names it as the reason for "any kind"), and the remark that the general
statement carries `SomeBlockNonzero` as a hypothesis.

### 3.4 D Appendix D.7, second paragraph: from one parameter to generic parameters

**Paper** (PDF p. 45, tex 1576): "By Proposition D.4, the Jacobian at `θ†` has the rank (13) on some
finite batch `X`. In the cases (n) and (+) the outputs on `X` are real-analytic in `θ ∈ ℝ^P`, and so
are the minors of the Jacobian. A minor of the size (13) does not vanish at `θ†`, so it vanishes
only on a set of measure zero. At generic parameters the Jacobian on `X` therefore has at least the
rank (13)".

**Lean** (`Dimension/GenericRank.lean:59`, `:182`, `:196`, `:207`; instance arguments
`[Fintype T] [Fintype d] [Fintype dIn] [Fintype dOut]`):
- `analyticOnNhd_eval_params A S hf hχ x`: for real-analytic `f_ℓ` and `χ` (on the whole space),
  `θ ↦ eval A S θ x` is real-analytic on the whole parameter space.
- `ae_jacobianRank_ge A S hf hχ μ X θ₀ : ∀ᵐ θ ∂μ, jacobianRank A S X θ₀ ≤ jacobianRank A S X θ`.
- `ae_jacobianRank_le_funDim … : ∀ᵐ θ ∂μ, jacobianRank A S X θ₀ ≤ funDim A S θ`.
- `ae_funDim_ge A S hf hχ μ θ₀ : ∀ᵐ θ ∂μ, funDim A S θ₀ ≤ funDim A S θ`.

**Comparison.** The paper's step is the instance `θ₀ = θ†`, `S = 0`, `X` the batch of
Proposition D.4. The Lean statements hold for every network with real-analytic `f_ℓ` and `χ`
(the cases (n), `χ = id`, and (+), `χ = N_ε` with `ε > 0`, are instances: `analyticOnNhd_id`,
`analyticOnNhd_rmsNorm`), for all stream matrices `S`, every batch `X : Fin n → Matrix T dIn ℝ`
(also `n = 0`) and every `θ₀`. No hypothesis on the dimensions.

**Verdict: LEAN STRONGER.** Proved (three standard axioms).

### 3.5 D "These four kinds of block are real-analytic"

**Paper** (Section 1.1, PDF p. 2, tex 133): "for tanh, GELU, SwiGLU and GeGLU blocks … These four
kinds of block are real-analytic, and they are the family of the title." Appendix D uses it ("In
the cases (n) and (+), every `B_{>k}` is real-analytic on all rows `h`", tex 897).

**Lean** (`Activations/Analytic.lean`): `analyticOnNhd_gaussPdf`, `analyticOnNhd_gaussCdf`,
`analyticOnNhd_gelu`, `analyticOnNhd_silu` (each `AnalyticOnNhd ℝ _ Set.univ`), and
`analyticOnNhd_f_gated (hσ : AnalyticOnNhd ℝ σ Set.univ) (ℓ) : AnalyticOnNhd ℝ ((Arch.gated σ χ hid).f ℓ) Set.univ`
(`[Fintype T]`; `χ` arbitrary; `d` plays no part).

**Comparison.** `gelu z = z * gaussCdf z`, `silu z = z / (1 + exp (−z))`, as the earlier audits
found. With the older `analyticOnNhd_tanh` and `analyticOnNhd_f_mlp`, the fixed maps of the four
kinds are real-analytic (machine-checked as one statement, `KindsTest.lean`,
`four_kinds_analytic`). The block `g_ℓ(n) = f_ℓ(n W_read) W_write` and the network are then
real-analytic by older statements and by 3.4.

**Verdict: SAME** (stated for the fixed maps; `analyticOnNhd_f_gated` for every real-analytic
gate). Proved. The paper's sentence is in Section 1.1; the file header and `STATEMENTS.md` say
"Section 2 ("analytic blocks")", and Section 2 of the paper has no such words (4b).

### 3.6 D Lemma D.5 for gated blocks

**Paper** (PDF p. 30, tex 965): "Lemma D.5 (The readout). If `D` has rank `d_model`, then `(D_L)`
holds."

**Lean** (`Depth/SuffixGated.lean:62`, `:73`):
- `claimGated_last [Nonempty T] (θ : Params (Arch.gated σ id hid) dIn dOut) : ClaimGated ⊤ θ (Fin.last L)`.
- `claimGated_last_rmsNorm [Nonempty T] {ε} (hε : 0 < ε) (θ : Params (Arch.gated σ (rmsNorm ε) hid) dIn dOut) (hD : θ.D.rank = Fintype.card d) : ClaimGated (antisymmetric d) θ (Fin.last L)`.

**Comparison.** For `k = L` the claim says: `X L = Z`, `Z ∈ g`, `η_D = −Z D`; no block comes after
`h_L`, so no `Δ` is needed (the proofs take `α = 0`). Any gate `σ`. Case (n): no hypothesis on `D`
(the paper's proof of this case does not use it either: "`hZD + hη_D = 0` for all rows `h`, so
`η_D = −ZD`"). Case (+): `D` of rank `d` and `ε > 0`, as the paper. At least one token; for no token
the claim fails (2.4).

**Verdict.** Case (n): **LEAN STRONGER** (the rank hypothesis is dropped). Case (+): **SAME**.
Case (0): not applicable to gated blocks. Proved.

### 3.7 D Proposition D.4 for gated blocks

**Paper** (PDF p. 30, tex 953): "Let `θ` be regular, with no vanishing value column if the blocks
are gated, and let `(D_0)` hold at `θ`. Then the directions `η ∈ ℝ^P` with `D_θF(θ, x) η = 0` for
all `x` … are the directions `η^Z` of (11), or `η^{Z,Δ}` of (12) for gated blocks, and the Jacobian
of the network has the rank (13) on some finite batch of such inputs." (13) is
`P − (L + 1) dim G − s`, with `s = q_1 + ⋯ + q_L` for gated blocks.

**Lean** (`Depth/SuffixGated.lean:131`, `:169`, `:202`, `:240`; all with `[Nonempty T]` and
`hσ : AnalyticOnNhd ℝ σ Set.univ`):
- `flat_le_cobDir_add_rescaleDir_of_claimGated`: `Regular θ → ClaimGated ⊤ θ 0 → ∀ η ∈ flat … 0 θ,
  ∃ X α, η = cobDir θ X + rescaleDir θ α`.
- `funDim_of_claimGated`: `Regular θ → (∀ ℓ i, value column ≠ 0) → ClaimGated ⊤ θ 0 →
  funDim … 0 θ + ((L + 1) * card d ^ 2 + ∑ ℓ, card (hid ℓ)) = finrank ℝ (Params …)`.
- `flat_le_cobDir_add_rescaleDir_of_claimGated_rmsNorm` (`0 < ε`): the same with
  `ClaimGated (antisymmetric d) θ 0` and `(∀ ℓ, X ℓ ∈ antisymmetric d) ∧ η = …`.
- `funDim_of_claimGated_rmsNorm` (`0 < ε`):
  `funDim … + ((L + 1) * (card d * (card d − 1) / 2) + ∑ ℓ, card (hid ℓ)) = finrank …`.

**Comparison.**
- "Regular": `Regular` (2.8). "No vanishing value column": `hv`; the first statement of each pair
  does not need it (the paper needs it only for the count).
- "Are the directions": the Lean statements here give the inclusion "every flat direction is an
  `η^{Z,Δ}`". The other inclusion is in older statements (`cobDir_mem_flat_skipless`,
  `rescaleDir_mem_flat`, `cobDir_mem_flat_skipless_rmsNorm`, `rescaleDir_mem_flat_of_differentiable`).
  Machine-checked that together they give the paper's "are" in both cases
  (`/home/claude/audit5/D4.lean`, the first two examples, `η ∈ flat ↔ ∃ X α, …`).
- The entry of `η^{Z,Δ}` at `E` is `E Z_0`: `cobDir θ X` has `E := θ.E * X 0`, and `X 0 = Z` with
  `η_E = E Z` from Lemma D.3 in the proof.
- "The Jacobian has the rank (13) on some finite batch": Lean states `funDim = P − (L+1) dim G − s`.
  `funDim` is the largest rank over finite batches and is attained, so this gives a batch with the
  rank (13) (machine-checked, `D4.lean`, third example, with `exists_jacobianRank_eq_funDim`), and
  also that no batch has more, which the paper says in D.2.
- The counts: `(L + 1) d² + ∑_ℓ q_ℓ` in the case (n), `(L + 1) d(d−1)/2 + ∑_ℓ q_ℓ` in the case (+)
  (`d(d−1)` is even, so the division of natural numbers is exact; `dim O(d) = d(d−1)/2`). These are
  `(L + 1) dim G + s` of (13).
- The gate: any real-analytic `σ` (the paper: SiLU and GELU).
- "Of such inputs" (`xE ≠ 0`) concerns the case (0) only.

**Verdict: SAME** in content, in two statements per case, and slightly **STRONGER** (any
real-analytic gate; the inclusion without the hypothesis on the value columns). Proved.

### 3.8 D "A good `θ` is regular", and Lemma D.13

**Paper** (tex 1137): "A good `θ` is regular." (tex 1300-1315, PDF p. 38): the parameters `θ†`, and
"Lemma D.13 (`θ†` is good). `θ†` is good for the cones `C_0 = ⋯ = C_L = ℝ^{1×d_model}_{>0}`. For
every block, `A_ℓ = {1, …, d_model}`, and `g°_ℓ(n) = n` for a GELU block and `g°_ℓ(n) = (n𝟙) n` for a
gated block".

**Lean** (`Depth/Cones.lean:114-170`).
- `regular_of_goodForConesGated_swiglu [Nonempty T] (hθ : GoodForConesGated C A θ) :
  Regular (Arch.gated silu χ hid) θ`, the same with `gelu`, and
  `regular_of_goodForConesMlp_gelu … : Regular (Arch.mlp gelu χ hid) θ`. Any `χ`.
- `exists_goodForConesGated_cols [Nonempty d] hdIn hdOut hhid : ∃ C A θ, GoodForConesGated C A θ ∧
  ∀ ℓ, LinearIndependent ℚ (gate columns)`, for any `σ`, `χ`.
- `exists_goodForConesGated_outer (hd : 2 ≤ card d) hdIn hdOut hhid : ∃ C A θ, GoodForConesGated C A θ ∧
  ∀ ℓ, LinearIndependent ℚ (fun j => vecMulVec c_j c_j)`.
- `exists_goodForConesMlp_outer (hd : 2 ≤ card d) hdIn hdOut hhid`: the same for `Arch.mlp`.
Here `hdIn : card d ≤ card dIn`, `hdOut : card d ≤ card dOut`, `hhid : ∀ ℓ, card d ≤ card (hid ℓ)`.

**Comparison.**
- "A good `θ` is regular": (R1) is in "good"; (R3) is what has to be proved, and it uses the gate
  (`σ′(tz) → 1` or `0`, `σ(tz)/t → z` or `0`), so there is one statement per kind. The Lean
  `Regular.deriv_block` asks for a hidden state `n` with rows `T`; the state with every row `t ξ`
  serves. The independence over `ℚ` is not used, in the paper or in Lean. Same as the paper.
- Lemma D.13 as existence. The hypotheses are those under which `θ†` exists and is good:
  `d_in, d_out ≥ d`, at least `d` hidden units per block, `d ≥ 1` for SwiGLU, `d ≥ 2` for GELU and
  GeGLU (the paper: "the entries … off the diagonal, which exist because `d_model ≥ 2`"). The
  conclusion does not name the parameter, the cones or the active sets. So the Lean statements
  follow from the paper's lemma and do not give it back: the explicit `θ†`, the positive orthant,
  `A_ℓ = {1, …, d}` and the formulas for `g°_ℓ` are lost. For Appendix D.7 only the existence is
  used. That `θ†` itself meets the Lean conditions: 2.7 (by hand in general, by machine for `d = 2`,
  `q = 3`, `L = 1`).
- The existence statements are for arbitrary `σ` and `χ` (the conditions do not involve them), and
  for index types `hid ℓ`, `dIn`, `dOut` of any finite size at least `d`.

**Verdict.** "Good is regular": **SAME**. Lemma D.13: **LEAN WEAKER** (existence). The six had
`sorry` when I began; in the source at `d80fd1c` all six are proved, with the same statements
(a copy of the file compiles with the three standard axioms, `ConesCopy.lean`). I did not judge
the proofs; I note only that the proof of the existence statements defines, privately, the
positive orthant and parameters of the form of `θ†` for every `d`, so Lean has now checked for
all dimensions what I checked for `d = 2`.

### 3.9 D Lemma D.12

**Paper** (PDF p. 35, tex 1190): "Lemma D.12 (The step for GELU and gated blocks on rays). Let the
blocks be GELU blocks in the case (+), or gated blocks in the case (n) or (+). Let `θ` be good for
the cones `C_0, …, C_L`, and let `k < L`. Then `(D_{k+1})` implies `(D_k)`."

**Lean** (`Depth/StepGated.lean:31-77`; elaborated, all with `[Fintype T] [Fintype d] [DecidableEq d]
[Fintype dIn] [Fintype dOut] [∀ ℓ, Fintype (hid ℓ)] [Nonempty T]`, and `C`, `A`, `θ` implicit):

```
claimGated_castSucc_swiglu {θ : Params (Arch.gated silu id hid) dIn dOut} :
  GoodForConesGated C A θ → (∀ ℓ, LinearIndependent ℚ fun j : hid ℓ => (θ.read ℓ)ᵀ (Sum.inl j)) →
  ∀ k : Fin L, ClaimGated ⊤ θ k.succ → ClaimGated ⊤ θ k.castSucc
claimGated_castSucc_swiglu_rmsNorm {ε} (0 < ε) {θ : Params (Arch.gated silu (rmsNorm ε) hid) dIn dOut} :
  … → ∀ k : Fin L, ClaimGated (antisymmetric d) θ k.succ → ClaimGated (antisymmetric d) θ k.castSucc
claimGated_castSucc_geglu, claimGated_castSucc_geglu_rmsNorm : the same with `gelu` and
  hQ : ∀ ℓ, LinearIndependent ℚ fun j => vecMulVec ((θ.read ℓ)ᵀ (Sum.inl j)) ((θ.read ℓ)ᵀ (Sum.inl j))
claimRMS_castSucc_gelu {ε} (0 < ε) {θ : Params (Arch.mlp gelu (rmsNorm ε) hid) dIn dOut} :
  GoodForConesMlp C A θ → (∀ ℓ, LinearIndependent ℚ fun j => vecMulVec ((θ.read ℓ)ᵀ j) ((θ.read ℓ)ᵀ j)) →
  ∀ k : Fin L, ClaimRMS (Arch.mlp gelu (rmsNorm ε) hid) θ k.succ → ClaimRMS … θ k.castSucc
```

**Comparison.**
- The five settings are the paper's five: SwiGLU (n), SwiGLU (+), GeGLU (n), GeGLU (+), GELU (+).
  No statement is made for GELU in the case (n), which the paper leaves out.
- "Good for the cones": `GoodForCones…` with `hQ` of the kind (2.7): columns for SwiGLU, matrices
  `c_j c_j^⊤` for GeGLU and GELU. The assignment is the paper's (K3).
- `hQ` for all blocks `ℓ`: the paper's "good" asks (K3) of every block, so the hypothesis is the
  paper's. The paper's proof of the step for `k` uses the independence over `ℚ` for block `k + 1`
  only ("A generic ray", condition (i)); the later blocks enter through (K1), (K2) and "no `a_j`,
  no `e_j` vanishes". So the Lean hypothesis could be asked of block `k` alone. As written it is
  the paper's.
- `k : Fin L`, `k.succ`, `k.castSucc`: `k.castSucc` is `k` and `k.succ` is `k + 1` in
  `Fin (L + 1)`; "`k < L`" is `k : Fin L`. The block of the step is Lean block `k`, the paper's
  block `k + 1`; it reads the cone `C k.castSucc` (2.7).
- The claims: `ClaimGated ⊤` in the case (n), `ClaimGated (antisymmetric d)` in the case (+)
  (2.4), `ClaimRMS` for GELU in the case (+) (the form (17) with antisymmetric `Z_ℓ`, checked by
  the third audit).
- `ε > 0` in the case (+), as the paper's case (+).
- No hypothesis on `d`. The paper's lemma has none either (its `d_model ≥ 2` is that of
  Theorem 5.2). A good parameter exists only for `d ≥ 1` (2.5). I found no use of `d ≥ 2` in the
  paper's proof of the lemma (it is used in Lemma D.13 for GELU and GeGLU).
- "Regular" is not a hypothesis, in the paper or in Lean: a good `θ` is regular.
- **One token against rows `T`.** The paper takes one token; the Lean claims are for hidden states
  with rows `T`. For `Arch.gated` and `Arch.mlp` with `χ = id` or `χ = N_ε`, the network after `h_k`
  acts on each row separately, so row `t` of the identity (16) at a hidden state `h` is the
  one-token identity at the row `h_t`. Hence (16) for rows `T` (`T` not empty) holds if and only if
  the one-token (16) holds, and `(D_k)` for rows `T` is equivalent to the paper's `(D_k)`; the
  conclusion of the claim does not involve `T`. So the Lean lemma is equivalent to the paper's.
  This is an argument by hand; I did not prove it in Lean. The cones stay sets of single rows.
- The statement is not vacuous at the paper's parameter: `Dagger.lean` supplies `hθ` and `hQ` for
  `θ†` (2.7).

**Verdict: SAME.** Not proved (`sorry` in all five). I found nothing in the five statements or in
the definitions under them that departs from the paper's lemma.

### 3.10 D Appendix D.7: `(D_0)` at one parameter

**Paper** (tex 1576): "By Lemma D.13, `θ†` is good, so it is regular, and no value column
vanishes. `(D_L)` holds at `θ†` (Lemma D.5), and by Lemma D.12, applied for `k = L − 1`, then for
`k = L − 2`, and so on down to `k = 0`, so does `(D_0)`."

**Lean** (`Depth/GeluGatedExplicit.lean:99-159`; all with `[Nonempty T]`, `hd : 2 ≤ card d`,
`hdIn`, `hdOut`, `hhid`, and `0 < ε` in the case (+)):
- `exists_regular_claimRMS_gelu : ∃ θ : Params (Arch.mlp gelu (rmsNorm ε) hid) dIn dOut,
  Regular … θ ∧ ClaimRMS … θ 0`.
- `exists_regular_claimGated_swiglu : ∃ θ : Params (Arch.gated silu id hid) dIn dOut,
  Regular … θ ∧ (∀ ℓ i, value column ≠ 0) ∧ ClaimGated ⊤ θ 0`; `…_swiglu_rmsNorm` with
  `ClaimGated (antisymmetric d) θ 0`; the two with `geglu`.

**Comparison.** The conclusions are what Proposition D.4 needs (regular; no vanishing value
column for gated blocks; `(D_0)`). They say "there is a parameter", not "at `θ†`". The hypotheses
are those of Theorem 5.2. In the two SwiGLU statements `2 ≤ card d` is the paper's scope; the chain
of statements needs `d ≥ 1` only (4, "hypotheses not needed").

**Verdict: LEAN WEAKER in form** (existence), enough for the theorem. The proofs are written and
rest on the five statements with `sorry` of `StepGated.lean` (Lemma D.12).

### 3.11 D Theorem 5.2 (ii) for `ε > 0`, and (iii)

**Paper** (PDF p. 8 and p. 24, tex 330): "Let `d_in, d_out ≥ d_model ≥ 2`, and consider networks
without biases whose blocks are all of one kind, tanh, GELU, SwiGLU or GeGLU, each with at least
`d_model` hidden units. In the following cases the functional dimension at generic parameters is
`P − (L + 1) dim G − s`, so the network satisfies the equality condition. (i) tanh blocks: without
normalization, and under pre-RMSNorm with `ε > 0` and with `ε = 0`. (ii) GELU blocks: under
pre-RMSNorm with `ε > 0` and with `ε = 0`. (iii) SwiGLU blocks, and GeGLU blocks: without
normalization, and under pre-RMSNorm with `ε > 0`." "Here `s = 0` for tanh and GELU blocks, and `s`
is the number of hidden units of the network for SwiGLU and GeGLU blocks."

**Lean** (`Depth/GeluGatedTheorem.lean`; each with `[Nonempty T]`, an additive Haar measure `μ`,
`hd : 2 ≤ card d`, `hdIn : card d ≤ card dIn`, `hdOut : card d ≤ card dOut`,
`hhid : ∀ ℓ, card d ≤ card (hid ℓ)`):

| Lean name | Network | Conclusion `∀ᵐ θ ∂μ, …` |
|---|---|---|
| `ae_funDim_gelu_skipless_rmsNorm` (`0 < ε`) | `Arch.mlp gelu (rmsNorm ε) hid`, `S = 0` | `funDim + (L + 1) * (d * (d − 1) / 2) = P` |
| `ae_funDim_swiglu_skipless` | `Arch.gated silu id hid` | `funDim + ((L + 1) * d ^ 2 + ∑ ℓ, card (hid ℓ)) = P` |
| `ae_funDim_swiglu_skipless_rmsNorm` (`0 < ε`) | `Arch.gated silu (rmsNorm ε) hid` | `funDim + ((L + 1) * (d * (d − 1) / 2) + ∑ ℓ, card (hid ℓ)) = P` |
| `ae_funDim_geglu_skipless` | `Arch.gated gelu id hid` | as SwiGLU (n) |
| `ae_funDim_geglu_skipless_rmsNorm` (`0 < ε`) | `Arch.gated gelu (rmsNorm ε) hid` | as SwiGLU (+) |

with `P = Module.finrank ℝ (Params …)` and `d = Fintype.card d`.

**Comparison.**
- Hypotheses: `d_in, d_out ≥ d ≥ 2`; at least `d` hidden units in each block; one kind of block
  (`Arch.mlp gelu`, `Arch.gated silu`, `Arch.gated gelu`); no biases (the library has none); a
  network without skips (`S = 0`). The paper's. `[Nonempty T]`: at least one token.
- Counts: `dim G = d²` without normalization, `d(d−1)/2` under pre-RMSNorm with `ε > 0`; `s = 0` for
  GELU, `s = ∑_ℓ q_ℓ` for SwiGLU and GeGLU. The paper's `P − (L + 1) dim G − s`, written as a sum
  to avoid subtraction of natural numbers.
- "At generic parameters": `∀ᵐ θ ∂μ`.
- `funDim` is the paper's functional dimension for these real-analytic networks (2.8).
- `L` is any natural number, also `L = 0` (a network `x ↦ χ(xE) D`), which the paper's "`L` blocks"
  does not mean to include; the statement is true there by the same proof.
- All tokens `T`, not one.

**What of Theorem 5.2 is not stated.** (i) for `ε = 0` and (ii) for `ε = 0` (the case (0)); the
clause "so the network satisfies the equality condition" (Definition 4.4, Proposition 4.6 are not
in Lean); Corollary 5.3. Part (i) without normalization and for `ε > 0` is stated and proved in
older files (`ae_funDim_tanh_skipless`, `ae_funDim_tanh_skipless_rmsNorm`).

**Verdict: SAME** for (ii) with `ε > 0` and for (iii); **PART** of Theorem 5.2. The proofs are
written; they rest on the five statements with `sorry` of Lemma D.12.

---------------------------------------------------------------------------------------------------

## (4) Lists

### (4a) Clauses of the paper's statements in scope with no Lean statement

Absorb paper, Theorem 4.3:
1. A residual network with attention blocks, and a residual network that alternates attention and
   MLP blocks (Scope, tex 214: "Theorem 4.3 allows blocks of any kind, and so covers networks that
   alternate attention and MLP blocks"). No attention block is defined in Lean; the general
   statements would apply once `SomeBlockNonzero` is proved almost everywhere for such a network.
2. A residual network whose MLP blocks are of different kinds has no unconditional statement
   either (`Arch.mlp` and `Arch.gated` take one `σ`); the paper's Scope does not ask for it.
3. The sentence "`a_1` vanishes for all `n̄` only if the read of block 1 has a zero column" as a
   statement about a kind of block: proved in the form "almost everywhere some block is nonzero at
   some normalized state" for MLP and gated blocks, by another exceptional set for gated blocks
   (`c · e = 0`), not as "only if a column is zero".
4. The expansions of the proof as statements of their own (`G(X) + O(1/t²)`,
   `N_0(XE) D + ρ(X)/t + O(1/t²)`): they are private lemmas of `RMSNormRays.lean`, in the form of
   limits of `t (F(tX) − …)`.
5. A residual network with `ε > 0` against a skipless network with `ε = 0`, and the converse: not
   stated in the paper either (it has one `ε`).

Dimension paper:
6. Lemma D.13 in its explicit form: `θ†`, the positive orthant as every cone, `A_ℓ = {1, …, d}`,
   `g°_ℓ(n) = n` and `(n𝟙) n`.
7. Appendix D.5 before Lemma D.12, in the ten files of the scope: Lemmas D.8, D.9, D.10, D.11;
   eq. (24), (25) (the gates far from zero); the frozen network `B°_{>k}` and "Lemmas D.2 and D.3
   hold for `B°_{>k}`"; the identity for one GELU or gated block, eq. (26) to (30). (Two files
   added while I was reading, `Activations/FarFromZero.lean` and `Activations/MillsAtInfinity.lean`,
   state Lemma D.8, eq. (24), (25) and Lemma D.9 for a real variable, according to
   `STATEMENTS.md`. They are not in the scope and I did not compare them.)
8. Theorem 5.2 (i) for `ε = 0` and (ii) for `ε = 0`; "so the network satisfies the equality
   condition"; Corollary 5.3.
9. Claim `(D_k)` in the case (0), eq. (18), and Lemma D.5 in the case (0) (not for gated blocks in
   the paper either).
10. Proposition D.4 as one statement "the flat directions are exactly the `η^{Z,Δ}`": the two
    inclusions are separate statements (3.7).

### (4b) Rows or notes of `STATEMENTS.md` that are inaccurate or incomplete

Line numbers are those of the file at commit `d80fd1c` (403 lines). Every Lean name in the rows of
the scope exists and elaborates, and the numbers in them are those of the Lean statements.

1. **Line 400, the list "Not stated yet" of the absorb paper: "Theorems 3.4, 4.2, 4.3; …".**
   Theorem 4.3 is stated (lines 350-354) and proved. The list should say what remains of it:
   attention blocks in the residual network.
2. **Lines 264-265, "Theorem 5.2 (ii) for `ε > 0` and (iii) are stated and in work (what is left is
   Lemma D.12, `Depth/StepGated.lean`, and Lemma D.13, `Depth/Cones.lean`)".** Out of date at
   `d80fd1c`: Lemma D.13 and "a good `θ` is regular" are proved (lines 171-172 say so). What is left
   is Lemma D.12.
3. Line 166, "D Section 2 ("analytic blocks")": Section 2 of the paper does not contain these
   words. The sentence is in Section 1.1 ("These four kinds of block are real-analytic", tex 133).
   The header of `Activations/Analytic.lean` has the same reference.
4. Line 353 (Theorem 4.3, the general statements and those for MLP and gated blocks): accurate,
   including the sentence that `0 < ε` on the residual network is not used (I checked it by
   machine). It could add: the statements for MLP and gated blocks need at least one token
   (`[Nonempty T]`); a residual network that mixes kinds is covered only through the hypothesis;
   the skipless network may have no block; one set of measure zero serves all skipless networks.
5. Line 352 ("Measure zero"): accurate. It could say that `ae_someBlockNonzero_mlp` and `_gated`
   need `[Nonempty T] [Nonempty d]`.
6. Lines 354, 171, 172 (the seven kinds; "a good `θ` is regular"; Lemma D.13) are marked "proved".
   Right for the sources: a copy of each file compiles with the three standard axioms
   (`KindsCopy.lean`, `ConesCopy.lean`), and so does the library as rebuilt by its authors before
   my last run. At my first run the compiled library still had `sorry` for these 30 names (5.4).
7. Lines 213-218, the note "Appendix D takes inputs of one token": it lists Lemmas D.3, D.5, D.7
   and Proposition D.4. It should now add Lemma D.12 (stated for rows `T`, at least one token) and
   say that the cones of "good" are sets of single rows.
8. Line 178 (Appendix D.7, the five `exists_regular_claim…`): accurate ("they rest on Lemma D.12 …
   which is in work; `Depth/Cones.lean` is proved"). The header of `Depth/GeluGatedExplicit.lean`
   (lines 18-20) still says "These statements are the whole of Appendix D.5 (Lemmas D.8 to D.13).
   Their proofs are not written yet"; both sentences are out of date. The header of
   `Depth/StepGated.lean` ("Its proof is not written yet") is right.
9. Lines 165, 167-170, 177, 179, 350-351: accurate. In line 170, "and nonempty, which the paper uses
   without saying" is right. In line 172, "(SwiGLU; `d ≥ 1`)" and "(GeGLU, GELU; `d ≥ 2`)" are the
   hypotheses of the three statements.
10. The notes rewritten after the fourth audit.
    - "ReLU blocks and the functional dimension" (lines 229-244): accurate, and it now has the two
      additions that the fourth audit asked for (the Lean value can be larger at parameters that
      are not generic; no notion of a no-kink input at depth).
    - "Pre-RMSNorm with `ε = 0`" (lines 245-249): accurate. One sentence could be added: for
      `ε = 0` Theorem 4.3 of the absorb paper is stated in the paper's sense (`DefinedAt`, a dense
      set), so the remark "true statement about Lean's total function" does not apply to it.
    - "Lemma B.1" (lines 192-198): accurate ("attention is not").
    - "Theorem 4.3 is stated under the conditions that its proof uses" (dimension paper, lines
      221-228): accurate.
11. Lines 13-26 (who compared what): after this audit the ten files of the scope have been
    compared. The two files added to that list at `d80fd1c` (`Activations/FarFromZero.lean`,
    `Activations/MillsAtInfinity.lean`) have not.

---------------------------------------------------------------------------------------------------

## (5) What the authors should know, most serious first

### 5.1 Anything false, vacuous or changed in meaning

1. **Nothing of this kind was found.** All 81 names of the scope elaborate. No statement is
   vacuous: the hypotheses of the statements on Theorem 4.3 hold for almost every `θ` (that is what
   `ae_turnGeneric` and `ae_someBlockNonzero_…` say), and the hypotheses of Lemma D.12 hold at the
   paper's `θ†` (machine-checked for `d = 2`, three hidden units, one block). No definition changes
   the meaning of a statement in the scope: `DefinedAt` is the paper's "defined at", the conclusion
   for `ε = 0` is the negation of the paper's equality, `funDim` is the paper's functional
   dimension for these real-analytic networks.

2. **Point (a), Theorem 4.3 of the absorb paper.** A reader of the paper would accept the Lean
   statements for the seven kinds of MLP block as the theorem, and they are stronger than the
   paper's on the side of the skipless network. Three things should be said beside them.
   - "Blocks of any kind" in the residual network is a conditional statement in Lean: the general
     theorems assume `∀ᵐ θ, SomeBlockNonzero A θ`. This is the paper's step "`a_1` vanishes for all
     `n̄` only if the read of block 1 has a zero column", and for an arbitrary map `f_ℓ` that step is
     false: with `σ(z) = max(z − 1, 0)` all blocks vanish on an open set of weights, and the
     residual network is then a skipless network with no block (the second half is machine-checked,
     `Need.lean`). So the hypothesis is needed, and the paper's "blocks of any kind" means "of any
     of the paper's kinds".
   - Attention blocks in the residual network are not stated. The paper gives them as the reason
     for "any kind".
   - `TurnGeneric` is exactly what the paper's proof needs of the weights, and its third clause is
     exactly the negation of what equality forces (machine-checked).

3. **Point (b), the definitions under Lemma D.12.** `GoodForConesGated`, `GoodForConesMlp` and the
   hypotheses `hQ` are the paper's (R1), (K1), (K2), (K3), with one clause added that the paper
   uses without saying (the cones are not empty). (K1) with the active sets as data is equivalent
   to the paper's (K1), and the Lean active set is the paper's `A_ℓ` (machine-checked). The indices
   are right: Lean block `ℓ` reads `C ℓ.castSucc` and maps into `C ℓ.succ`. The paper's `θ†` is good
   in the Lean sense with the positive orthant as every cone (by hand in general; by machine for
   `d = 2`, `q = 3`, `L = 1`, with both forms of `hQ`; and the library's own proof of the existence
   statements, finished while I read, uses the orthant and parameters of this form). The five
   statements of Lemma D.12 are the paper's lemma in its five settings. I see no reason not to
   build the proof on them.

### 5.2 Differences of form

4. Lemma D.13 is stated as existence. The explicit `θ†`, the orthant and the formulas for `g°_ℓ`
   are not Lean statements. If the authors want the Lean text to show that the paper's parameter
   is the one that works, a definition of `θ†` and a statement "`θ†` is good" are needed; the
   scratch file `Dagger.lean` shows the shape for one small case.
5. (K3) is split: the two "does not vanish" clauses are fields, the independence over `ℚ` is a
   separate hypothesis `hQ`, for every block. Nothing is lost when both are given.
6. The claims and Lemma D.12 are for hidden states with rows `T`; the cones are sets of single
   rows. The equivalence of the claim for rows `T` with the paper's one-token claim is true by a
   short argument (the network after `h_k` acts row by row), which is not a Lean statement.
7. Proposition D.4 for gated blocks is two statements per case (the inclusion and the value of
   `funDim`), and the converse inclusion is in older files. Together they give the paper's
   sentence (machine-checked).
8. In `ClaimGated`, `η` is a full parameter whose entries at `E` and at the blocks before `k + 1`
   are not constrained, and `X ℓ` for `ℓ < k`, `α ℓ` for the blocks before `k + 1` are free. The
   same convention as `Claim`.
9. For `ε > 0` the skipless network of Theorem 4.3 has its own constant `ε′ > 0`; the paper has one
   `ε`. The skipless network may have no block (`L′ = 0`) and any model dimension `d′ : Type`.
10. Theorem 5.2 holds in Lean also for `L = 0`.

### 5.3 Hypotheses that Lean shows unnecessary

11. Theorem 4.3, `ε > 0`: `0 < ε` on the residual network is not used (machine-checked by removing
    it in a copy of the file). Only `ε′ > 0` of the skipless network is.
12. Theorem 4.3, `ε = 0`: the blocks of the skipless network need only be continuous.
13. Theorem 4.3: "every MLP block has at least `d_model` hidden units" is not needed; one hidden
    unit in one block is enough. Nothing is needed of the skipless network (no condition on its
    model dimension, widths or depth).
14. Lemma D.5, case (n), gated blocks: "`D` has rank `d`" is not needed (as for tanh blocks).
15. Proposition D.4, gated blocks: "no vanishing value column" is needed for the count only, not
    for "every flat direction is an `η^{Z,Δ}`".
16. Theorem 5.2 (iii) for SwiGLU blocks: the chain of Lean statements (Lemmas D.5, D.12, D.13,
    Proposition D.4, the generic rank, Theorem 4.3) gives the conclusion for `d ≥ 1`; `d ≥ 2` is
    used only for GELU and GeGLU blocks, in Lemma D.13. Machine-checked that the SwiGLU theorem
    without normalization follows with `[Nonempty d]` in the place of `2 ≤ card d`
    (`D4.lean`, last example). This rests on Lemma D.12, which is not proved yet, so it says what
    the statements need, not what is true.
17. Lemma D.12: the independence over `ℚ` is asked of every block; the paper's proof of the step
    for `k` uses it for block `k + 1` only.

### 5.4 What was checked by machine, and what was not

Checked by machine (scratch files in `/home/claude/audit5/`, each compiled alone, no error):
- `Axioms.lean`: `#print axioms` on the 81 names, run twice. No axiom other than `propext`,
  `Classical.choice`, `Quot.sound` and `sorryAx` appears in either run.
  - First run, on the compiled library that I was given (sources of commit `cf6ed62`): 36 names
    with the three standard axioms only; **45 names with `sorryAx`**: the 24 of
    `Absorb/RMSNormKinds.lean`, 6 of `Depth/Cones.lean` (the three `regular_of_goodForCones…`, the
    three `exists_goodForCones…`), the 5 of `Depth/StepGated.lean`, the 5 of
    `Depth/GeluGatedExplicit.lean`, the 5 of `Depth/GeluGatedTheorem.lean`.
  - Last run, on the library as its authors had rebuilt it at commit `d80fd1c`: 66 names with the
    three standard axioms only; **15 names with `sorryAx`**: `claimGated_castSucc_swiglu`,
    `claimGated_castSucc_swiglu_rmsNorm`, `claimGated_castSucc_geglu`,
    `claimGated_castSucc_geglu_rmsNorm`, `claimRMS_castSucc_gelu` (the five of Lemma D.12, which
    have `sorry`), and the ten that rest on them: `exists_regular_claimRMS_gelu`,
    `exists_regular_claimGated_swiglu`, `…_swiglu_rmsNorm`, `exists_regular_claimGated_geglu`,
    `…_geglu_rmsNorm`, `ae_funDim_gelu_skipless_rmsNorm`, `ae_funDim_swiglu_skipless`,
    `…_swiglu_skipless_rmsNorm`, `ae_funDim_geglu_skipless`, `…_geglu_skipless_rmsNorm`.
- `KindsCopy.lean`, `ConesCopy.lean`: copies of the sources of `Absorb/RMSNormKinds.lean` (at
  `46445c6`) and `Depth/Cones.lean` (at `d80fd1c`), each compiled as a file of its own: the 24
  and the 6 names depend on the three standard axioms only, and the elaborated statements and
  structures of `Cones.lean` are those that I compared. I did not rebuild the library (no
  `lake build`). All scratch files were compiled again, one at a time, against the library as
  rebuilt at `d80fd1c`: no error.
- `Check.lean`: the elaborated forms quoted in this report.
- `T43.lean`: `TurnGeneric` as the negation of the paper's condition; `TurnGeneric` fails for
  `L = 0` and for `d = 1`; `SomeBlockNonzero` fails without tokens; the conclusion for `ε = 0` as
  "the set of agreement is not dense"; `DefinedAt` unfolded; the general theorem applied to an
  arbitrary residual `Arch` against a skipless tanh network.
- `RaysCopy.lean`: `exists_ne_skipless_rmsNorm_of_turn` without `0 < ε`.
- `Need.lean`: a residual network whose blocks all vanish is the skipless network with no block.
- `KindsTest.lean`: two reader's instances of Theorem 4.3 (tanh against SwiGLU for `ε > 0`; ReGLU
  against ReLU for `ε = 0`) and "the four kinds have real-analytic fixed maps".
- `K1.lean`: (K1) of the paper is equivalent to (K1) of Lean on a convex set; the Lean active set
  is the paper's; the empty set satisfies the other four clauses of a cone; no cone for `d` empty;
  the three entries of (19) against `rescaleDir`; `cobDir θ X + rescaleDir θ α` has the entries of
  `ClaimGated`; `ClaimGated (antisymmetric d) → ClaimGated ⊤`.
- `Dagger.lean`: the paper's `θ†` for `d = 2`, three hidden units, one block is good in the Lean
  sense for the positive orthant; both forms of `hQ` hold there; the Lean Lemma D.12 applies.
- `D4.lean`: Proposition D.4 for gated blocks as "if and only if" in both cases; a batch with the
  rank (13); Theorem 5.2 (iii) for SwiGLU with `d ≥ 1`.

Not checked by machine (arguments by hand in this report):
- that `(D_k)` for rows `T` is equivalent to the paper's `(D_k)` for one token (3.9);
- that `θ†` is good in the Lean sense for general `d`, `q_ℓ`, `L` (2.7; by machine only the small
  case);
- that the hypothesis `SomeBlockNonzero` fails on a set of positive measure for
  `σ(z) = max(z − 1, 0)` (3.2);
- that an attention block of the paper has the form `f(n W_read) W_write` of an `Arch` (2.1);
- the truth of the five statements of Lemma D.12, which have `sorry`: Lean has not checked them,
  and I compared only their statements with the paper.

I did not judge the proofs.

---------------------------------------------------------------------------------------------------

## (6) Count

Paper statements and definitions compared: **16**.
- Absorb paper (4): Theorem 4.3; Section 2, "Normalization" ("defined at" and equality for
  `ε = 0`); Appendix A.3, the comparison of the two networks under the conditions of the proof
  (with the condition that equality forces); Appendix A.3, "Measure zero".
- Dimension paper (12): Appendix D.7, second paragraph (the generic rank); "these four kinds of
  block are real-analytic"; Claim `(D_k)` in the form (19); Lemma D.5; Proposition D.4; "Cones and
  good parameters" (cones, the frozen block, "good": (K1), (K2), (K3)); "a good `θ` is regular";
  the parameters `θ†` and Lemma D.13; Lemma D.12; Appendix D.7, "`(D_0)` holds at `θ†`";
  Theorem 5.2 (ii) for `ε > 0`; Theorem 5.2 (iii).

Lean names compared: **81** (8 definitions and structures, 73 theorems).
- `Absorb/RMSNormRays.lean`: 3. `Absorb/RMSNormGeneric.lean`: 12. `Absorb/RMSNormKinds.lean`: 24.
- `Dimension/GenericRank.lean`: 4. `Activations/Analytic.lean`: 5.
- `Depth/SuffixGated.lean`: 7. `Depth/Cones.lean`: 11. `Depth/StepGated.lean`: 5.
- `Depth/GeluGatedExplicit.lean`: 5. `Depth/GeluGatedTheorem.lean`: 5.

Verdicts over the 16 paper items: SAME 10 (the notions for `ε = 0`; the four real-analytic kinds;
Claim `(D_k)` in the form (19); Lemma D.5, with the case (n) stronger; Proposition D.4; the
definition of "good"; "good is regular"; Lemma D.12; Theorem 5.2 (ii) for `ε > 0`; Theorem 5.2
(iii)). LEAN STRONGER 2 (the generic rank; the comparison of Theorem 4.3 under the conditions of
the proof). LEAN WEAKER 2 (Lemma D.13 and "`(D_0)` at `θ†`", both as existence). DIFFERENT in form
with the same content 1 ("Measure zero"). PART 1 (Theorem 4.3: stronger where it is stated, for the
seven kinds of MLP block; conditional for blocks of any kind; attention blocks not stated).
Theorem 5.2 as a whole is stated in part: (i) and (ii) for `ε = 0` are not. None false, none
vacuous.
