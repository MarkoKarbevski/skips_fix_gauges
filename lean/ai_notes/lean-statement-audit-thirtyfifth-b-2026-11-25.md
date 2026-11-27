STATUS: complete

# Thirty-fifth audit, part B, of Lean statements against the papers (25 November 2026)

Commit of `/home/claude/lp` (branch `lean-plus`) read at the start: `adb7960`.

Files with `sorry` at that commit: `SkipsLean/Activations/GateFarC.lean` (2), `SkipsLean/Depth/FrozenFarHolomorphic.lean` (1). `SkipsLean/Symmetry/BiasesAffineGroup.lean` has none.

## Part 1

Definitions read for all checks: `Network/Defs.lean` (`Arch`, `Params`), `Network/Biases.lean` (`Biases`, `hiddenB`, `evalB`: `h_0 = x E + b_E`, `h_ℓ = h_{ℓ-1} M_ℓ + f_ℓ(χ(h_{ℓ-1}) W_read^ℓ + b_read^ℓ) W_write^ℓ + b_write^ℓ`, `y = χ(h_L) D + b_D`), `Symmetry/ChangeOfBasis.lean` (`Params.cob`, `cobSkip`), `Symmetry/BiasesSymmetries.lean` (`Biases.cob`, `Biases.translate`, `evalB_cob`).

### Check 1. The translations together (by reading and by a computation)

Lean:

```lean
def Biases.translateAllAt (b : Biases A dOut) (θ : Params A dIn dOut)
    (g : Fin (L + 1) → d → ℝ) : Biases A dOut where
  E := b.E + g 0
  read ℓ := b.read ℓ - g ℓ.castSucc ᵥ* θ.read ℓ
  write ℓ := b.write ℓ + g ℓ.succ
  D := b.D - g (Fin.last L) ᵥ* θ.D

def Biases.translateAll (b : Biases A dOut) (θ : Params A dIn dOut)
    (g : Fin (L + 1) → d → ℝ) : Biases A dOut where
  E := b.E + g 0
  read ℓ := b.read ℓ - (∑ k ∈ Finset.Iic ℓ.castSucc, g k) ᵥ* θ.read ℓ
  write ℓ := b.write ℓ + g ℓ.succ
  D := b.D - (∑ k, g k) ᵥ* θ.D

theorem evalB_translateAllAt (hA : A.χ = id) ... : evalB A 0 θ (b.translateAllAt θ g) x = evalB A 0 θ b x
theorem evalB_translateAll (hA : A.χ = id) ... : evalB A 1 θ (b.translateAll θ g) x = evalB A 1 θ b x
```

Entry by entry against the proof ("Add `g` to the write bias of block `ℓ`, or to the embedding bias when `ℓ = 0`; subtract `g W_read^k` from the read bias of every block `k > ℓ`; subtract `g D` from the readout bias"). In Lean the block `ℓ : Fin L` reads `h_{ℓ.castSucc}` and writes `h_{ℓ.succ}` (the paper's block `ℓ + 1`). The translation of `h_k, …, h_L` by `g_k` adds `g_k` to the embedding bias (`k = 0`) or to the write bias of the block that writes `h_k` (`ℓ.succ = k`), and subtracts `g_k W_read` from the read bias of each block that reads one of `h_k, …, h_{L−1}` (`k ≤ ℓ.castSucc`), and `g_k D` from the readout bias. Summed over `k = 0, …, L`: the embedding bias gets `g_0`; the write bias of the block writing `h_{ℓ+1}` gets `g_{ℓ+1}`; the read bias of the block reading `h_m` loses `(g_0 + … + g_m) W_read`; the readout bias loses `(g_0 + … + g_L) D`. This is `translateAll`, entry by entry. The read and readout corrections use the weights `θ` before the change of basis, as they must, since `affPreserving…` translates first and changes the basis second.

Skipless: "each hidden state has its own translation". There `h_{ℓ+1} = f(h_ℓ W_read + b_read) W_write + b_write` has no stream term, so a shift `g_{ℓ+1}` of `h_{ℓ+1}` enters by the write bias alone, and the read of `h_ℓ` must remove the shift `g_ℓ` of `h_ℓ` alone. This is `translateAllAt`, entry by entry.

Computation (`/home/claude/audit35b/check1_translations.py`, output `check1.out`; tanh MLP blocks of width 4 with biases, `T = 2`, `d = 3`, `d_in = d_out = 2`, `L = 3`, five random inputs, random `g`): the outputs change by at most `1.8e-15` (residual, `translateAll`) and `8.9e-16` (skipless, `translateAllAt`); the hidden states move by `g_0 + … + g_m` (residual) and `g_m` (skipless) to `1.3e-15`; `translateAll` agrees to `6.7e-16` with the `L + 1` single translations `Biases.translate θ k g_k` of `Symmetry/BiasesSymmetries.lean` applied one after the other (the paper's construction); the skipless formula used in a residual network changes the output by `1.3` (the two are not interchangeable, as expected).

Verdict: **SAME** (the `L + 1` translations of the first sentence together, in increments `g_k`, for the residual network; and the skipless counterpart of the proof). The single translation of the first sentence ("for every `ℓ`") is `Biases.translate` / `evalB_translate` of `Symmetry/BiasesSymmetries.lean`, earlier audited; `translateAll` with `g` zero except at `k` is that single translation. The hypothesis `hA : A.χ = id` is the lemma's "without normalization"; no other hypothesis.

### Check 2. The two sets (by reading, by compiling a copy, by a computation)

Lean:

```lean
def affPreservingSkipless (A : Arch T d L) (dIn dOut : Type*) [Fintype dIn] [Fintype dOut] :
    Set ((Fin (L + 1) → GL d ℝ) × (Fin (L + 1) → d → ℝ)) :=
  {p | ∀ (θ : Params A dIn dOut) (b : Biases A dOut) (x : Matrix T dIn ℝ),
    evalB A 0 (θ.cob p.1 p.1) ((b.translateAllAt θ p.2).cob p.1) x = evalB A 0 θ b x}
def affPreservingResidual … := {p | ∀ θ b x,
    evalB A 1 (θ.cob p.1 p.1) ((b.translateAll θ p.2).cob p.1) x = evalB A 1 θ b x}
def affMat (s : Set ((Fin (L + 1) → GL d ℝ) × (Fin (L + 1) → d → ℝ))) :
    Set ((Fin (L + 1) → Matrix d d ℝ) × (Fin (L + 1) → d → ℝ)) :=
  (fun p => ((fun ℓ => (p.1 ℓ : Matrix d d ℝ)), p.2)) '' s
theorem affPreservingSkipless_eq_univ (A : Arch T d L) (hA : A.χ = id) :
    affPreservingSkipless A dIn dOut = Set.univ
theorem mem_affPreservingResidual_iff [Nonempty T] [Nonempty dOut] (A : Arch T d L)
    (hA : A.χ = id) (p : (Fin (L + 1) → GL d ℝ) × (Fin (L + 1) → d → ℝ)) :
    p ∈ affPreservingResidual A dIn dOut ↔ ∀ ℓ, p.1 ℓ = p.1 0
```

**The action.** The pair `(G, g)` first translates (biases `translateAll θ g`, computed with the old weights), then changes the basis (`Params.cob G G`: `E G_0`, `G_{ℓ-1}⁻¹ W_read`, `W_write G_ℓ`, `G_L⁻¹ D`; `Biases.cob G`: `b_E G_0`, `b_write G_ℓ`, read and readout biases kept). The function is compared in the same architecture: the stream stays `0` (skipless) or `1` (residual). At the hidden state `h_m` the pair acts as the affine map `h ↦ (h + S_m) G_m` (`S_m = g_m` skipless, `S_m = g_0 + … + g_m` residual): every element of `Aff(d)` at every hidden state, in the coordinates `(G_m, S_m)` (skipless) or, residual, with the increments `g` in place of `S` (a linear bijection, so the dimension is the same). This is the natural action of `Aff(d)^{L+1}` (skipless), and of `Aff(d)` with one linear part and `L + 1` translations (residual).

**Composition.** By hand: the pair `p' = (G', g')` after `p = (G, g)` is the pair `q = (G G', g + g' G⁻¹)` (products and `G⁻¹` index by index), on every weight and every bias, for both streams (the read corrections of `p'` use the weights `G⁻¹ W_read` that `p` left, which gives `g' G⁻¹ W_read`). So the maps form a right action of the semidirect product `GL(d)^{L+1} ⋉ (ℝ^d)^{L+1}`, and both sets are closed under the composition (skipless: all pairs; residual: equal `G` stays equal, translations free); the residual set is a subgroup. Computed (`check1_translations.py`): the composite and `q` agree to `4.3e-14` on the weights and `7.1e-15` on the biases, for `M = 0` with free `G` and for `M = 1` with equal `G`. **Lean states no group structure on these sets** (no counterpart of `exists_subgroup_eq_cobPreserving` of `Symmetry/CobGroup.lean`). The statements of the file (sets, membership, Hausdorff dimension) do not need it; the paper's word "group" does, so that word is not stated (see check 3).

**`affPreservingSkipless_eq_univ`.** Hypothesis `A.χ = id` only; true for any blocks (`evalB_cob` with `cobSkip 0 G = 0`, then `evalB_translateAllAt`). Paper: "each hidden state has its own translation (Proposition A.1 (ii))", with the changes of basis of Proposition A.1 (ii) at every hidden state. **SAME.**

**`mem_affPreservingResidual_iff`** against "A skip ties only the linear part of `Aff(d_model)`" (the linear parts must agree, the translations are free).
* ← (all `G` equal): `cobSkip 1 G` has entries `G_ℓ⁻¹ G_{ℓ+1} = 1`, so `evalB_cob` keeps the residual stream; then `evalB_translateAll`. Correct for any blocks.
* → ("networks with zero writes and free write biases decide it"), by reading the helper proofs: `θ = (E = 0, reads 0, writes 0, D)`, read biases `0`, readout bias `0`, input `0`, embedding and write biases `w` with `w_j + g_j = v` at `j = k` and `0` elsewhere. With zero writes the block term is `f(…) · 0 = 0` whatever `f` is, so `h_L = ∑ w_j`; after the pair the writes are still `0`, the biases are `(w_j + g_j) G_j`, so `h'_L = v G_k`, and the readout bias is `−(∑ g) D`. Equality gives `v G_k G_L⁻¹ D = v D` for all `v`, `D`, so `G_k = G_L`. The argument is right and uses no property of the blocks: the write biases put an arbitrary row into the stream after every block, which is what Theorem A.5 (iii) without biases needs a nonzero block for (there the stream after block `ℓ` is `x E` plus block outputs only, and with all blocks identically zero only `G_0 = G_L` is forced). It does not need `d ≥ 2` either (Theorem A.5 (iii) asks it). Computed: in the zero-write network an unequal family changes the output by `24.5` (`check1.out`).
* `[Nonempty T]`, `[Nonempty dOut]` are needed. Compiled in a copy (`/home/claude/audit35b/AffCopy.lean`: the file followed by audit examples): `affPreservingResidual A dIn Empty = Set.univ`, and for `T = Empty`, `affPreservingResidual A dIn dOut = Set.univ` (outputs with no entries), while for `L = 1`, `d = Fin 1` the family `G = (1, −1)` is not constant. So without either instance the iff is false; the paper takes a nonempty network for granted.
* `[Nonempty dIn]` is not asked and not needed (the input is `0`).

Verdict: **SAME** for both sets and both statements (empty `T` or `d_out` excluded, as in the earlier files). The word "group" is not stated; closure checked by hand and numerically.

### Check 3. The dimensions (by reading; the axioms by compiling a copy)

Lean:

```lean
theorem dimH_affMat_affPreservingSkipless (A : Arch T d L) (hA : A.χ = id) :
    dimH (affMat (affPreservingSkipless A dIn dOut))
      = (((L + 1) * (Fintype.card d ^ 2 + Fintype.card d) : ℕ) : ℝ≥0∞)
theorem dimH_affMat_affPreservingResidual [Nonempty T] [Nonempty dOut] (A : Arch T d L)
    (hA : A.χ = id) :
    dimH (affMat (affPreservingResidual A dIn dOut))
      = ((Fintype.card d ^ 2 + (L + 1) * Fintype.card d : ℕ) : ℝ≥0∞)
theorem dimH_affMat_affPreservingSkipless_eq_add [Nonempty T] [Nonempty dOut] (A : Arch T d L)
    (hA : A.χ = id) :
    dimH (affMat (affPreservingSkipless A dIn dOut))
      = dimH (affMat (affPreservingResidual A dIn dOut)) + ((L * Fintype.card d ^ 2 : ℕ) : ℝ≥0∞)
```

**The notion.** As in `Symmetry/CobGroup.lean` (Theorem 3.3 (ii) without biases): the Hausdorff dimension of the set of the pairs (matrices, rows) in the finite-dimensional space `(Fin (L+1) → Matrix d d ℝ) × (Fin (L+1) → d → ℝ)` with its sup metric. Hausdorff dimension does not change under bi-Lipschitz maps, so the choice of norm and the choice of the increments `g` in place of the cumulative translations `S` (check 2) do not matter. For a Lie subgroup of `GL(d)^{L+1} ⋉ (ℝ^d)^{L+1}` (here: an open set, or the image of an open set under a linear embedding) it is the manifold dimension. Skipless: all pairs, an open set (`det ≠ 0` at each index) of the space of dimension `(L+1)(d² + d)`. Residual: by `mem_affPreservingResidual_iff`, the image of `{(G_0, g) : det G_0 ≠ 0}` (open in dimension `d² + (L+1)d`) under the isometric embedding `(G_0, g) ↦ ((G_0, …, G_0), g)`. Difference `L d²`. All three true; the instances are those of the iff, needed there. **SAME** against "dimension `d_model² + (L + 1) d_model + s`, against `(L + 1)(d_model² + d_model) + s` without skips, and the skips remove `L d_model²` dimensions", for `s = 0`, that is, for the group of the changes of basis and translations alone.

**The `s` of the symmetries inside the blocks** is not in these sets; the header says it is counted in `Symmetry/BiasesSymmetryCount.lean` only. There (thirty-third report, part A, check 6) the count with `s` is stated as the dimension of the span of the directions at one point `p = (θ, b)`, with `s = dim V` for a space `V` of directions inside the blocks satisfying `hV`, `hrw`, and with `E` of rank `d` (and, skipless, the writes of rank `d`).

**Is every sentence of Lemma A.8 stated, with the two files and `Symmetry/BiasesSymmetries.lean`?**
* "adding a row `g` to the hidden states `h_ℓ, …, h_L` preserves the function once the biases are adjusted, for every `ℓ`": `evalB_translate` (one `ℓ`) and `evalB_translate…`/`evalB_translateAll` here (all `ℓ` together). Stated.
* "The symmetry group generated by changes of basis, translations and the symmetries inside blocks therefore has dimension `d² + (L+1)d + s`, against `(L+1)(d² + d) + s` without skips": stated in two halves, neither of which is the sentence: (a) the group of the changes of basis and translations, as a set with its dimension, without `s` (this file; as the maximal set of pairs that preserve the function at all parameters, which equals the group the pairs generate, by `affPreservingSkipless_eq_univ` and `mem_affPreservingResidual_iff`); (b) the count with `s`, on directions at one parameter under rank conditions (`BiasesSymmetryCount`). **Not stated:** that the pairs form a group (no subgroup statement, check 2), and the group generated together with the symmetries inside the blocks, as a set with its dimension, or the statement that its dimension is the sum (that the three families meet only at the identity, or act locally freely together at some parameter, which is what turns (b) into a group dimension).
* "and the skips remove `L d_model²` dimensions, as without biases": `dimH_affMat_affPreservingSkipless_eq_add` (without `s`) and `finrank_span_symmetryDirs_skipless_eq_add` (directions with `s`). Stated.

Verdict on the second sentence: **PART** (as the thirty-third report, part A, check 6 had it; this file adds the group of the changes of basis and translations as a set with its dimension, which closes half of the gap left there).

### Check 4. Equation (31), `GateFarC` (by reading and by a computation)

Lean (`SkipsLean/Activations/GateFarC.lean`, read at `adb7960`; both theorems `sorry`):

```lean
def GateFarC (σ : ℝ → ℝ) (p : ℕ) : Prop :=
  ∃ σc : ℂ → ℂ, (∀ x : ℝ, σc (x : ℂ) = ((σ x : ℝ) : ℂ)) ∧ ∃ R κ : ℝ, 0 < κ ∧
    ∀ z : ℂ, R ≤ z.re → |z.im| ≤ z.re / 2 →
      AnalyticAt ℂ σc z ∧ AnalyticAt ℂ σc (-z) ∧
        ‖σc z - z‖ ≤ Real.exp (-(κ * z.re ^ p)) ∧ ‖σc (-z)‖ ≤ Real.exp (-(κ * z.re ^ p))
theorem gateFarC_gelu : GateFarC gelu 2 := by sorry
theorem gateFarC_silu : GateFarC silu 1 := by sorry
```

**Clause by clause** against "Let `z ∈ ℂ` with `Re z ≥ 2` and `|Im z| ≤ ½ Re z` […] Both gates are holomorphic at `z` and at `−z` […] So there is a number `κ_1 > 0` such that, for large `Re z`, `|σ(z) − z| ≤ e^{−κ_1 (Re z)^p}` and `|σ(−z)| ≤ e^{−κ_1 (Re z)^p}`": an extension `σc` that agrees with `σ` on the reals; the sector `|Im z| ≤ Re z / 2`; "for large `Re z`" as `R ≤ Re z` for some `R`; holomorphic at `z` and `−z`; `κ > 0`; the two bounds. The paper's (31) is a sentence about GELU and SiLU; Lean makes it a property of a gate and states it for the two. **SAME.** (`R` may be any real number; for `R ≤ 0` the sector adds only `z = 0` and the points `0 < Re z < 2`, which only make the statement harder, so nothing is lost.)

**Is the extension unique where it matters?** By reading: `σc` is analytic at every point of the closed sector `S_R = {Re z ≥ R, |Im z| ≤ Re z/2}` and of `−S_R`, so on an open neighbourhood of each; `S_R` is connected and contains the real ray `[max(R, 0), ∞)`, where `σc = σ`. Two extensions are then both analytic on the connected component containing `S_R` of the intersection of their two neighbourhoods and agree on a real segment in it, so they agree on `S_R` (identity theorem), and likewise on `−S_R` (which contains `(−∞, −max(R,0)]`). Off the two sectors `σc` is not constrained at all (it need not be analytic there). That is enough for Lemma D.11, whose gate arguments lie in `S_R ∪ −S_R` for large `t` and small `ϱ` (check 5), and `exists_far_frozen_holomorphic` does not use `σc` in its conclusion.

**True for GELU (`p = 2`) and SiLU (`p = 1`)?** Computed with complex arithmetic of 30 digits (`/home/claude/audit35b/check4_gatefarc.py`, output `check4.out`): extensions `z Φ(z) = z erfc(−z/√2)/2` and `z/(1 + e^{−z})`; for `Re z = x` from 2 to 12 in steps of `1/4`, `m(x)` = the largest of `|σ(z) − z|` and `|σ(−z)|` over 41 points of the segment `|Im z| ≤ x/2` (the boundary and the inside); `σ(−z) = σ(z) − z` holds to `7e-31`, so the two bounds are one.
* GELU: `−log m(x) / x²` is `0.634` at `x = 2`, `0.434` at 4, `0.384` at 10, `0.381` at 12, decreasing to `3/8` (the maximum is always on the boundary `Im z = ±x/2`, where `Re(z²) = ¾ x²`). The paper's bound `|σ(z) − z| ≤ e^{−(3/8)(Re z)²}` holds at every sampled point (for example `7.9e-2 ≤ 2.2e-1` at `x = 2`, `1.4e-24 ≤ 3.5e-24` at `x = 12`). So `κ = 3/8` works from `R = 2`; no `κ > 3/8` works for all large `x`.
* SiLU: `−log m(x) / x` is `0.636` at `x = 2`, its smallest value `0.597` near `x = 2.9`, then increases (`0.759` at 10, `0.784` at 12) towards `1` (as `1 − log|z|/x`). So `κ = 0.59` works from `R = 2` (on the sampled range; beyond it the ratio increases), `κ = 3/4` from about `R = 9.5`, and any `κ < 1` from a large `R`; `κ = 1` never works. The paper's intermediate bound `4 Re z e^{−Re z}` holds at every sampled boundary point. The poles of `z/(1 + e^{−z})` are at `iπ(2k+1)`, on the imaginary axis, outside both sectors for `R > 0`.

So both instances are true with the paper's constants (`κ = 3/8`, `R = 2` for GELU; any `κ < 1` with a large `R` for SiLU). **True** (numerical evidence; the proofs are `sorry`).

### Check 5. Lemma D.11 with the holomorphic extension (by reading and by a computation)

Lean (`SkipsLean/Depth/FrozenFarHolomorphic.lean`, read at `adb7960`; `sorry`):

```lean
theorem exists_far_frozen_holomorphic (hg : GateFar σ σ' p) (hgC : GateFarC σ p)
    {C : Fin (L + 1) → Set (d → ℝ)} {A : ∀ ℓ, Finset (hid ℓ)}
    {θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut}
    (hθ : GoodForConesGated C A θ) (k : Fin (L + 1)) (H : Matrix T d ℝ) (hH : ∀ t, H t ∈ C k)
    (η : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) :
    ∃ ϱ : ℝ, 0 < ϱ ∧ ∃ κ : ℝ, 0 < κ ∧ ∃ t₀ : ℝ, ∀ t : ℝ, t₀ ≤ t →
      ∃ G G₀ G' G₀' : Matrix T d ℂ → Matrix T dOut ℂ,
        AnalyticOnNhd ℂ G {u | ∀ τ j, ‖u τ j‖ ≤ ϱ} ∧ … (the same for G₀, G', G₀') ∧
        (∀ U : Matrix T d ℝ, (∀ τ j, |U τ j| ≤ ϱ) →
          G (U.map ofReal) = (suffix (Arch.gated σ id hid) 0 θ k (t • (H + U))).map ofReal ∧
          G₀ (U.map ofReal) = (suffix (Arch.frozen A) 0 (θ.toFrozen A) k (t • (H + U))).map ofReal ∧
          G' (U.map ofReal) = (fderiv ℝ (fun θ' => suffix (Arch.gated σ id hid) 0 θ' k (t • (H + U))) θ η).map ofReal ∧
          G₀' (U.map ofReal) = (fderiv ℝ (fun θ' => suffix (Arch.frozen A) 0 θ' k (t • (H + U)))
                                  (θ.toFrozen A) (η.toFrozen A)).map ofReal) ∧
        ∀ u : Matrix T d ℂ, (∀ τ j, ‖u τ j‖ ≤ ϱ) →
          ‖G u - G₀ u‖ ≤ Real.exp (-(κ * t ^ p)) ∧ ‖G' u - G₀' u‖ ≤ Real.exp (-(κ * t ^ p))
```

Definitions read: `suffix` (`Depth/Suffix.lean`: `𝓑_{>L}(h) = χ(h) D`, `𝓑_{>ℓ}(h) = 𝓑_{>ℓ+1}(h S_ℓ + f_ℓ(χ(h) W_read) W_write)`, here `S = 0`, the skipless networks of the dimension paper), `Arch.gated` (`σ(gate) · value` per hidden unit), `Arch.frozen A` and `Params.toFrozen` (`Depth/Frozen.lean`: `gate · value` on `A_ℓ`, `0` off it, the same matrices), `GoodForConesGated` and `IsOpenConvexCone` (`Depth/Cones.lean`: (R1), (K1) with the active sets as data, (K2), the part of (K3) that does not depend on the gate; cones open, convex, nonempty, without `0`).

**Clause by clause.**
* Quantifiers: "There are numbers `ϱ, κ, t₀ > 0` such that, for `t ≥ t₀`, the maps … extend": `∃ ϱ > 0, ∃ κ > 0, ∃ t₀, ∀ t ≥ t₀, ∃` four maps. The order is the paper's; the maps depend on `t`, as the extensions of maps that depend on `t` must. `t₀` is not asked to be positive (it can always be raised). Same.
* "extend to holomorphic maps on the rows `u ∈ ℂ^{1×d_model}` with `|u_j| ≤ ϱ` for all `j`": `AnalyticOnNhd ℂ` on the closed polydisc of complex `T × d` matrices (holomorphic at every point of the closed polydisc, so on an open neighbourhood of it), and agreement with the real maps at the real points of the polydisc. The paper has one row; the blocks act on each row separately, so the statement for `T` rows is the statement for one row applied to each, and the one-row case is `T` with one element. Same.
* The frozen network: `suffix (Arch.frozen A) 0 (θ.toFrozen A) k`, the paper's `𝓑°_{>k}` ("the network after `h_k` with the gates of all its blocks frozen", `g°_ℓ(n) = ∑_{j ∈ A_ℓ} (n c_j)(n e_j) a_j`). Its extension is the same polynomial with complex entries. Same.
* The derivative in the weights along `η`: at real `U`, `fderiv ℝ` in the weights of the real network at `θ` along `η`, and, for the frozen network, at `θ.toFrozen A` along `η.toFrozen A`, with the active sets `A` of `θ` kept (the paper: "where the hidden units whose gates are frozen are those of `θ`"). The paper's `η` is "a direction of the weights of the blocks `k+1, …, L` and of `D`"; Lean takes any `η`, whose other entries do not enter `𝓑_{>k}`. Same.
* The two bounds, on the whole polydisc, in the entrywise sup norm: the paper's two bounds "for these `u`". Same.
* Hypotheses: "In the case (n)" = `χ = id` in `Arch.gated σ id hid`; "for gated blocks" = `Arch.gated`; "let `θ` be good" = `GoodForConesGated C A θ` (the `ℚ`-independence of (K3) is not part of it; Lemma D.11 does not use it); "`k ≤ L`" = `k : Fin (L + 1)`; "`h° ∈ C_k`" = every row of `H` in `C_k`. The gate: GELU or SiLU in the paper (GeGLU, SwiGLU); in Lean any `σ` with `GateFar σ σ' p` and `GateFarC σ p` with the same `p`; both gates have both properties (`gateFar_gelu`, `gateFar_silu` proved; `gateFarC_gelu`, `gateFarC_silu` stated, check 4).

**Could it be satisfied trivially?** No. A map that is analytic at every point of the closed polydisc `P` is analytic on an open set containing `P`; two such maps are analytic on the connected component containing `P` of the intersection of their sets (`P` is connected), and if they agree on the real points of `P`, a set with nonempty interior in `ℝ^{T×d}`, all their partial derivatives agree at a real interior point, so they agree near it and on the whole component (identity theorem). So `G`, `G₀`, `G'`, `G₀'` are determined on `P` by the agreement clauses: they are the holomorphic extensions of the four real maps, and the bounds are claims about them. Four maps that ignore the network off the reals are not analytic. The header and the index say this. The hypotheses can all hold together: `GoodForConesGated` has an instance (`Depth/Cones.lean`, Lemma D.13, `θ†`), and `GateFar`, `GateFarC` hold for SiLU and GELU.

**Is it true?** By reading the paper's proof: for `t` large and `ϱ` small every gate argument `z = h c_j` at `h = t(h° + u)`, and at the later hidden states `t^{2^m}(g°…(h°) + u'')`, lies in the sector `S_R` or `−S_R` of `GateFarC`, with a margin, for `u` in a neighbourhood of `P` and for weights `θ + τη` with small complex `τ`; so the complex network built from `σc` is holomorphic there, agrees with the real one at real points (because `σc = σ` on the reals), and the induction of the paper gives the first bound and Cauchy's estimate in `τ` the second. The values of `σc` off the sectors are never used. Nothing in the Lean statement asks more.

Computed (`/home/claude/audit35b/check5_frozen_complex.py` and `check5b_frozen_complex_large_t.py`, outputs `check5.out`, `check5b.out`; 60 digits): two gated blocks, `d = 2`, three hidden units each, at the good parameter of the coordinator's real check (`ai_notes/frozen_far_check_2026-11-24.py`: gate columns `(1,0), (0,1), (−√2, −√2)`, value columns `(1,1)`, write rows `(1,0), (0,1), (1,1)`, cones the open positive quadrant, active units `{0, 1}`), `D = I`, `h° = (1, 2)`, `ϱ = 0.05`, `u` on the torus `|u_1| = |u_2| = ϱ` (64 or 36 points; the largest values of a holomorphic difference on a polydisc are on it) and three more points; the gates extended as `z/(1 + e^{−z})` and `z erfc(−z/√2)/2`; the derivative in the weights along a fixed direction `η` of all block weights and `D` by `mpmath.diff`. The largest differences over the `u`:

| gate, `k` | `t` | `max ‖𝓑 − 𝓑°‖` | `−log / t^p` | `max ‖𝐃_θ𝓑 η − 𝐃_θ𝓑° η‖` | `−log / t^p` |
|---|---|---|---|---|---|
| SwiGLU, `k = 1` | 8, 12, 16 | `9.1e-2`, `4.6e-3`, `1.8e-4` | 0.30, 0.45, 0.54 | `9.6e-2`, `6.5e-3`, `3.5e-4` | 0.29, 0.42, 0.50 |
| SwiGLU, `k = 0` | 24, 32, 48, 64 | `1.4e-3`, `2.2e-6`, `2.8e-12`, `2.2e-18` | 0.27, 0.41, 0.55, 0.64 | `6.9e-3`, `1.2e-5`, `1.8e-11`, `1.8e-17` | 0.21, 0.35, 0.52, 0.60 |
| GeGLU, `k = 1` | 3, 4, 5 | `5.6e-2`, `3.3e-3`, `7.2e-5` | 0.32, 0.36, 0.38 | `6.2e-2`, `6.4e-3`, `2.2e-4` | 0.31, 0.32, 0.34 |
| GeGLU, `k = 0` | 7, 8, 10 | `1.2e-6`, `2.0e-9`, `3.5e-16` | 0.28, 0.31, 0.36 | `7.6e-6`, `1.6e-8`, `4.2e-15` | 0.24, 0.28, 0.33 |

At `k = 0` the bound sets in late (for SwiGLU the differences are still above `1` at `t = 12`: the error of the first block is multiplied by the polynomial growth of the second), but `−log(difference)/t^p` increases with `t` in every row, so `κ = 0.2` works from `t₀ = 24` (SwiGLU) and from `t₀ = 7` (GeGLU) on these samples. Consistent with the statement; no counterexample.

Verdict: **SAME** (with the gate as a hypothesis; for GELU and SiLU through `gateFar_…` and `gateFarC_…`). Statement true by the paper's proof and the computation; the proof is `sorry` at `adb7960`.

### Check 6. What the paper uses of the complex `u` (by reading)

The proof of Lemma D.12, fact (b) (`dim.txt`, "by Lemma D.11"): "by Lemma D.11 for `k + 1`, at the row `h°` and with `t²` in the place of `t`, the maps `B − B^∞` and `𝐃_θ B(·) η′ − 𝐃_θ B^∞(·) η′` are holomorphic and at most `e^{−2κ′ t^{2p}}` at the rows `t²(h° + u)` with `|u_j| ≤ ϱ`, and by Cauchy's estimate so is the derivative of the first, for large `t`, where `|u_j| ≤ ϱ/2`. At `δ = δ(t)` the block gives such a row, with `u → 0`." The derivatives are then used at real rows only (the point of (33) is real). So what fact (b) needs is: at real rows `t(h° + U)` with small real `U`, the bounds on `𝓑 − 𝓑°`, on `𝐃_θ𝓑 η − 𝐃_θ𝓑° η`, and on the derivative in the hidden state of `𝓑 − 𝓑°`. `exists_far_frozen_bounds` (`Depth/FrozenFar.lean`, proved) has these three as its clauses, for `‖U‖ ≤ ϱ` (the entrywise sup norm, the same polydisc as here) and the derivative along `v` up to the factor `‖v‖`. Lean's derivative in the hidden state is along `v` at `h = t(H + U)`, the paper's Cauchy estimate gives it with the factor `1/t` from `u ↦ t(h° + u)` and with `ϱ/2`; the clause is weaker than Cauchy's estimate gives (no `1/t`), which is what fact (b) uses.

With both files every sentence of Lemma D.11 is stated: the holomorphic extensions and the two bounds on the complex polydisc (`exists_far_frozen_holomorphic`, check 5), and, for the real rows, the two bounds with the third clause that the paper derives from the complex `u` (`exists_far_frozen_bounds`). The intermediate claim of the paper's proof, the first bound at the complex weights `θ + τη`, is a step of the proof, not of the statement, and is in neither (not needed). **SAME**, the two files together; the real file alone is what Lemma D.12 uses.

### Check 7. Drift checks (by reading)

`Symmetry/BiasesAffineGroup.lean`:
* Hypotheses not in the paper: `[Nonempty T]`, `[Nonempty dOut]` (iff and residual dimension): needed (check 2, compiled examples); the paper takes a nonempty network for granted. `A.χ = id` is "without normalization".
* The paper's hypotheses not in Lean: none (Lemma A.8 asks none on the blocks; Lean needs none, check 2).
* Not stated: that the pairs form a group (check 2), and the group generated with the symmetries inside the blocks as a set with its dimension (check 3; the count with `s` is on directions in `Symmetry/BiasesSymmetryCount.lean`).

`Activations/GateFarC.lean`: no hypothesis; `R` free, `κ > 0`, `p : ℕ`. Nothing drifted.

`Depth/FrozenFarHolomorphic.lean`:
* Hypotheses not in the paper: `GateFar σ σ' p` and `GateFarC σ p` in place of "GELU or SiLU" (a generalization; both hold for the paper's gates; `GateFar` is not needed for this statement, whose real network is differentiable at the points that matter by `GateFarC` alone, but it is harmless); cones nonempty (inside `IsOpenConvexCone`; the paper uses it without saying, and `hH` gives it anyway when `T` is not empty).
* The paper's hypotheses not in Lean: the `ℚ`-independence of (K3) (part of "good"; not used by Lemma D.11, so Lean is not weaker for leaving it out).
* Skipless (`S = 0`), as all networks of the dimension paper. Nothing drifted.

### Check 8. The index rows, the registrations and the axioms (by reading; the axioms by compiling a copy)

`/home/claude/lp/lean/STATEMENTS.md` at `adb7960`:
* Row "S Lemma A.8, the group of the changes of basis and translations as a set" (`Symmetry/BiasesAffineGroup.lean`, proved): every sentence is true of the statements (the two translations together; the two sets; any blocks; "no hypothesis on the blocks: networks with zero writes and free write biases decide it; `T` and `d_out` not empty"; the two Hausdorff dimensions and the difference; "The symmetries inside the blocks (the `s`) are not part of these sets"). The row does not say that Lean does not state that the pairs form a group (the word "group" of its quoted sentence); see the corrections.
* Row "S Lemma A.8, the count, as the dimension of the space of the directions" (`Symmetry/BiasesSymmetryCount.lean`): its pointer "The group of the changes of basis and translations as a set, with its dimension: `Symmetry/BiasesAffineGroup.lean`" is true. (The earlier sentence "This is the dimension of the group where it acts locally freely at `(θ, b)`, which the hypotheses ensure" was compared by the thirty-third reader and is not part of this audit.)
* Row "D Lemma D.11 …, for real hidden states" (`Depth/FrozenFar.lean`): its pointer "The paper's holomorphic extension to complex `u` is stated in `Depth/FrozenFarHolomorphic.lean`; the bound for the derivative in the hidden state, which the paper gets from it by Cauchy's estimate in the proof of Lemma D.12, is a clause of the statement" is true (checks 5, 6).
* Row "D Lemma D.11, proof, 'One gate', equation (31)" (`Activations/GateFarC.lean`, in work): true of the statements (check 4). Status "in work" right (two `sorry`).
* Row "D Lemma D.11, with the holomorphic extension" (`Depth/FrozenFarHolomorphic.lean`, in work): true of the statement, including "A holomorphic map on the polydisc is determined by its values at the real points, so these are the paper's extensions" (check 5). It says "a network of gated blocks without normalization" and not "skipless"; that is the convention of the dimension paper and of the neighbouring rows, so not wrong. Status "in work" right (one `sorry`).
* The paragraph "Not yet compared, written after the thirty-fourth audit began" lists the three files (lines 394–395): to be replaced by this report (see the corrections).

`/home/claude/lp/lean/checks/Axioms.lean`: imports the three modules (lines 411–413) and has `#print axioms` for the 7 theorems of `Symmetry/BiasesAffineGroup.lean` (lines 2246–2252); none for the 3 statements with `sorry` (right, they are not proved).

Axioms: a copy of `Symmetry/BiasesAffineGroup.lean` with `#print axioms` for its 7 theorems, compiled with `lake env lean` (`/home/claude/audit35b/AffCopy.lean`): each depends on `[propext, Classical.choice, Quot.sound]` only. The copy has no `sorry`.

## Part 2. The statements, file by file

| Lean name | Paper sentence | Verdict | Note |
|---|---|---|---|
| `Biases.translateAll` (def) | S Lemma A.8, proof: the `L + 1` translations of a residual network together | SAME | increments `g_k`; `h_m` moves by `g_0 + … + g_m`; equals the `L + 1` single translations of the proof applied in turn (computed) |
| `Biases.translateAllAt` (def) | S Lemma A.8, proof: "each hidden state has its own translation" (skipless) | SAME | `h_m` moves by `g_m` |
| `evalB_translateAll` | S Lemma A.8, first sentence, for all `ℓ` at once | SAME | `χ = id` |
| `evalB_translateAllAt` | S Lemma A.8, proof, skipless (Proposition A.1 (ii)) | SAME | `χ = id` |
| `affPreservingSkipless`, `affPreservingResidual` (defs) | the changes of basis and translations that preserve the function at all parameters | SAME | translate, then change the basis; the natural action of `Aff(d)` at every hidden state; closed under composition (by hand, computed), but no group structure is stated |
| `affMat` (def) | (the same set as matrices and rows) | SAME | for the Hausdorff dimension |
| `affPreservingSkipless_eq_univ` | "each hidden state has its own translation", with Proposition A.1 (ii) | SAME | any blocks |
| `mem_affPreservingResidual_iff` | "A skip ties only the linear part of `Aff(d_model)`" | SAME | no hypothesis on the blocks, rightly; `[Nonempty T]`, `[Nonempty dOut]` needed (compiled counterexamples to the iff without them) |
| `dimH_affMat_affPreservingSkipless` | "`(L + 1)(d_model² + d_model) + s` without skips", for `s = 0` | PART | the dimension of the group of changes of basis and translations; `s` is counted on directions in `Symmetry/BiasesSymmetryCount.lean` |
| `dimH_affMat_affPreservingResidual` | "dimension `d_model² + (L + 1) d_model + s`", for `s = 0` | PART | as above |
| `dimH_affMat_affPreservingSkipless_eq_add` | "the skips remove `L d_model²` dimensions" | SAME | for the group without `s`; with `s` on directions: `finrank_span_symmetryDirs_skipless_eq_add` |
| `GateFarC` (def) | D Lemma D.11, proof, equation (31) with "Both gates are holomorphic at `z` and at `−z`" | SAME | a property of a gate; the extension is unique on the two sectors, free elsewhere (not used) |
| `gateFarC_gelu` (`sorry`) | (31) for GELU, `p = 2` | SAME, true (computed) | `κ = 3/8` from `R = 2` |
| `gateFarC_silu` (`sorry`) | (31) for SiLU, `p = 1` | SAME, true (computed) | `κ = 0.59` from `R = 2` on `[2, 12]`; any `κ < 1` from a large `R`; never `κ = 1` |
| `exists_far_frozen_holomorphic` (`sorry`) | D Lemma D.11 as stated, with complex `u` | SAME, true (paper's proof; computed) | all tokens at once; any gate with `GateFar` and `GateFarC`; not trivially satisfiable (identity theorem) |

Lemma A.8 as a whole, with `Symmetry/BiasesSymmetries.lean` and `Symmetry/BiasesSymmetryCount.lean`: first sentence SAME; second sentence PART (the group without `s` as a set with its dimension, here; the count with `s` on directions at one parameter under rank conditions, there; the group with `s`, and "group", not stated); third clause SAME (both forms). Lemma D.11, with `Depth/FrozenFar.lean`: SAME, every sentence stated.

## For the authors

Nothing false, vacuous or drifted in the three files.

1. S Lemma A.8 is now stated in Lean as: the translations (one at a time and all together), the set of the changes of basis and translations that preserve the function (all of them without skips; with skips exactly those with one linear part, the translations free) and its dimension `d² + (L + 1)d` against `(L + 1)(d² + d)`. The `+ s` of the symmetries inside the blocks is stated only for the directions at one parameter, under the conditions that `E` (and without skips the writes) have rank `d` and that a direction inside a block with zero read and read bias has zero write and write bias; the thirty-third reader (part A, check 6) has exact examples where the count fails without each. The lemma's "the symmetry group generated by … has dimension … + s" needs that these symmetries and the changes of basis and translations do not overlap; the paper does not say so.
2. The paper's argument "A skip ties only the linear part" needs no condition on the blocks with biases (the write biases decide it), unlike Theorem A.5 (iii) without biases, which asks for nonzero blocks and `d_model ≥ 2`: the Lean proof confirms this. It needs a nonempty set of tokens and `d_out ≥ 1` (trivially).
3. Equation (31): computed, the paper's GELU bound `|σ(z) − z| ≤ e^{−(3/8)(Re z)²}` holds on the sector from `Re z = 2` (sampled to 12), and `3/8` is the best constant (the boundary `Im z = ±Re z/2` attains it in the limit). For SiLU `κ_1` can be any number below `1` for large `Re z`, `0.59` from `Re z = 2`; `κ_1 = 1` never works.
4. Lemma D.11 for complex `u`: computed for a two-block SwiGLU and GeGLU network on the torus `|u_j| = 0.05`; the bounds hold for large `t`, but at `k = 0` they set in late (SwiGLU: differences above `1` at `t = 12`, `κ ≈ 0.2` from `t ≈ 24`), because the error of the first block is multiplied by the polynomial growth of the later blocks, as the proof says ("a fixed power of `t`"). No condition is missing.
5. The pdf text of the proof of Lemma D.11 reads "Re z ≥ 2t |h° c_j|"; the TeX has `\frac t2`, which is right; the extracted text is misleading only, not the paper.

## Corrections for `STATEMENTS.md`

1. Lines 394–395 ("Not yet compared, written after the thirty-fourth audit began: … `Symmetry/BiasesAffineGroup.lean` … `Activations/GateFarC.lean` and `Depth/FrozenFarHolomorphic.lean`"): remove these two entries and add a sentence such as: "A thirty-fifth reader (part B, 25 November) compared `Symmetry/BiasesAffineGroup.lean` (7 theorems), `Activations/GateFarC.lean` and `Depth/FrozenFarHolomorphic.lean` (3 statements, read with `sorry` at `adb7960`): nothing false, vacuous or drifted; the second sentence of S Lemma A.8 is still stated in part (the group with the symmetries inside the blocks, and the group structure, are not stated); every sentence of D Lemma D.11 is stated (`ai_notes/lean-statement-audit-thirtyfifth-b-2026-11-25.md`)."
2. Row "S Lemma A.8, the group of the changes of basis and translations as a set": add at the end of the middle column "That the pairs form a group (under `(G, g)(G', g') = (G G', g + g' G⁻¹)`, the composition of the maps) is not stated."
3. Row "D Lemma D.11, with the holomorphic extension" (optional): "a network of gated blocks without normalization" could say "a skipless network of gated blocks without normalization", as `suffix … 0` is.

No other correction: the rows of `Symmetry/BiasesSymmetryCount.lean` and `Depth/FrozenFar.lean` point to the new files correctly.

## What I could not check

* The proofs of `gateFarC_gelu`, `gateFarC_silu` and `exists_far_frozen_holomorphic` (`sorry` at `adb7960`): judged true by the paper's proof and by computation only.
* Equation (31) was computed on a grid (`Re z` from 2 to 12 in steps of `1/4`, 41 points of each vertical segment); beyond 12 by the asymptotics (`3/8` for GELU, `1 − log|z|/Re z → 1` for SiLU).
* Lemma D.11 for complex `u` was computed at one good parameter, one token, one row `h°`, one direction `η`, `ϱ = 0.05`, and 36 or 64 points of the torus plus 3 others; the derivative in the weights by numerical differentiation at 60 digits, not exactly.
* That `GateFar` is not needed in `exists_far_frozen_holomorphic` is by reading only.

Commit of `/home/claude/lp` read at the end: `adb7960` (the branch did not move while I worked; the three files and `STATEMENTS.md` unchanged).
