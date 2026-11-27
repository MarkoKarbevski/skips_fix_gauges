STATUS: complete

# Thirty-third audit, part C: pre-LayerNorm networks (D Proposition A.3, S Proposition A.15), the functional dimension of a family, the chain-rule step with a section

Commit read at the start: `0e1bc98` of `/home/claude/lp` (branch `lean-plus`).
Files with `sorry` at that commit, among the subject: `SkipsLean/Residual/LayerNormRedundancy.lean` (two statements, `exists_hasFDerivAt_reduceLNParams_surjective` and `funDimOf_evalLNParams_eq_funDimB_reduceLN`; expected).

**Result.** Nothing false, vacuous or drifted. The pre-LayerNorm network, the centred and the reduced parameters are the papers' (with the readout and an embedding bias written out), parts (i) and (ii) hold for any `ε` and for stream matrices that commute with `Z` (the hypothesis is needed in general; the proving agent's example checked), and the named forms are S's skipless and residual cases and D's skipless case. `funDimOf` is Definition 4.1. The chain-rule step with a section is true, with one superfluous hypothesis (`hsurj`: a copy without it compiles). The two open statements of part (iii) are true (an affine section; six functional dimensions computed equal), and the additive form is exactly the paper's equality of differences of redundancies. The index rows are true, with two omissions.

Scratch work and scripts: `/home/claude/audit33c/` (`ln_check.py`, `ln_check_eps.py`, `ln_rank.py`, `ln_zero_gain.py`, `hS_example.py`). Papers: `<scratchpad>/skips.txt` (S, Proposition A.15 at lines 1492 to 1532; Definition 4.1 at line 424), `<scratchpad>/dim.txt` (D, Proposition A.3 at lines 796 to 830).

## Part 1: checks

### Check 1. The pre-LayerNorm network (`Network/LayerNorm.lean`), by reading

```lean
noncomputable def layerNorm (ε : ℝ) (γ β : d → ℝ) (h : Matrix T d ℝ) : Matrix T d ℝ :=
  rmsNorm ε (h * centering d) * Matrix.diagonal γ + Matrix.of fun _ => β
```
`rmsNorm` acts row by row by `rmsRow ε v = (√(v ⬝ᵥ v / card d + ε))⁻¹ • v` (`Basic/RMSNorm.lean`), and `centering d = 1 − (card d)⁻¹ • J`. So row `t` of `layerNorm ε γ β h` is `(h_t Z) diag(γ) / √(‖h_t Z‖²/d + ε) + β = γ ⊙ h_t Z/√(‖h_t Z‖²/d_model + ε) + β`, with the mean over the `d_model = card d` coordinates. This is S's `LN(h)` and D's `LN(h) = γ ⊙ N_ε(hZ) + β`, for row vectors `γ`, `β`. **SAME.**

`hiddenLN A ε S θ b γ β x`: `h_0 = x E + 1 b_E`, `h_{ℓ+1} = h_ℓ S_ℓ + f_ℓ(LN_ℓ(h_ℓ) W_read,ℓ + 1 b_read,ℓ) W_write,ℓ + 1 b_write,ℓ` with `LN_ℓ` of gain `γ_ℓ` and bias `β_ℓ` (`ℓ.castSucc`), and `evalLN … = LN_L(h_L) D + 1 b_D` with `γ_L`, `β_L` (`Fin.last L`). So there are `L + 1` LayerNorms, one at each hidden state `h_0, …, h_L`, each with its own gain and bias, one before every read and one before the readout; the skip reads `h_ℓ` itself (S Section 2: "the skips read `h` itself"). The read bias enters inside `f_ℓ`, the write bias after the write, the embedding bias at `h_0`, the readout bias at the output: the frame of `Network/Biases.lean` (thirty-first and thirty-second reports). The stream matrices `S_ℓ` are any `d × d` matrices; `0` and `1` are the skipless and the residual network of S equation (2). The fixed map `A.χ` of the architecture is not used (said in the docstring). The blocks `f_ℓ` are any maps `Matrix T r → Matrix T w`, so MLP, gated and attention blocks are all covered. **SAME** as "a pre-LayerNorm network, skipless or residual, whose reads and readout see `LN(h)`", with biases and with general stream matrices (more general).

One remark for the authors: neither paper says that each hidden state has its own LayerNorm (its own `γ`, `β`); the papers write one `γ`, `β`. Lean takes one per hidden state, which is the standard pre-LayerNorm transformer and includes the case of shared values.

### Check 2. Part (i) (`evalLN_eq_evalB_centerLN`, its two named forms, `sum_hiddenB_centerLN`), by reading and by a computation

Entry by entry, `Params.centerLN`: `E Z`, reads `diag(γ_ℓ) W_read,ℓ`, writes `W_write,ℓ Z`, readout `diag(γ_L) D`; `Biases.centerLN`: `b_E Z`, read biases `b_read,ℓ + β_ℓ W_read,ℓ`, write biases `b_write,ℓ Z`, readout bias `b_D + β_L D`. Against the paper's "Replacing each read `W` by `diag(γ)W` with the added bias `βW`, and each write `W`, write bias `b` and embedding `E` by `WZ`, `bZ` and `EZ`": the same, with three things the paper leaves implicit and Lean writes: the readout, which also reads through a LayerNorm, gets `diag(γ_L) D` and the bias `b_D + β_L D` (needed for the same function; S's proof of (iii) says "the analogous expressions for the readout"); the block's own read bias is kept and `β W` is added to it; the embedding bias, which the papers do not have, becomes `b_E Z`. The target is `A.withNorm (rmsNorm ε)`, so its reads and its readout see `N_ε(h)`: "whose reads see `N_ε(h)`". `sum_hiddenB_centerLN`: every row of every hidden state `h_0, …, h_L` of the centred network sums to `0`: "whose hidden states lie in `V`".

The hypothesis `hS : ∀ ℓ, centering d * S ℓ = S ℓ * centering d`: true for `S = 0` and `S = 1` (the named forms discharge it by `simp`), so the named forms are exactly S's "skipless or residual". Needed in general: the proving agent's example (`d = 2`, `L = 1`, block map `0`, zero biases, `S = diag(1, 0)`, `E = (1, 1)`), with `γ = 1`, `β = 0`, `D = (1, 0)^⊤`, `ε = 10^{-3}`: the pre-LayerNorm network has `h_1 = x (1, 0)`, `h_1 Z = x (1/2, −1/2)` and output `0.998` at `x = 1`; the centred network has `h_0 = x E Z = 0`, `h_1 = 0` and output `0`; `Z S ≠ S Z` (`hS_example.py`). So the conclusion fails without `hS`.

Computation (`ln_check.py`): tanh MLP blocks, attention blocks (2 heads of width 2, read `[W_Q | W_K | W_V]` with biases, softmax), and networks that alternate them; `(L, d) = (1, 3), (2, 4), (3, 5)`; `S = 0` and `S = 1`; `ε = 0.3, 10^{-5}`; all biases and gains random. Largest difference between `evalLN` and `evalB` of the centred network: `3.6 × 10^{-15}`; largest row sum of a hidden state of the centred network: `2.9 × 10^{-15}`. With stream matrices that commute with `Z` but are neither `0` nor `1` (`0.5 I + 0.3 J`, and a rotation of `V` plus `0.7 J/d`): `8.9 × 10^{-16}`.

**Verdict: SAME** for the named forms; `evalLN_eq_evalB_centerLN` is **LEAN STRONGER** (any stream matrices that commute with `Z`; any `ε`, see Check 3), and true.

### Check 3. Part (ii) (`evalLN_eq_evalB_reduceLN`, its named forms, `card_add_one_eq_of_orthonormal_centering`, `exists_orthonormal_centering`), by reading and by a computation

Entry by entry, `Params.reduceLN ε U θ γ`: `E U`, reads `√(card d/card m) • (Uᵀ diag(γ_ℓ) W_read,ℓ)`, writes `W_write,ℓ U`, readout `√(card d/card m) • (Uᵀ diag(γ_L) D)`; `Biases.reduceLN`: `b_E U`, `b_read,ℓ + β_ℓ W_read,ℓ`, `b_write,ℓ U`, `b_D + β_L D`. Against the list in S's proof of (iii), "`√(d_model/(d_model − 1)) Ū^⊤ diag(γ)W` and `b + βW` for each read, `W Ū` and `bŪ` for each write, `EŪ` for the embedding, and the analogous expressions for the readout": the same, with `card m` in place of `d_model − 1` and the extra embedding bias `b_E U`. The target architecture is `A.withNorm (rmsNorm (ε * card d / card m))` on the index type `m`, with the stream matrices `Uᵀ S_ℓ U` (`0` and `1` in the named forms, by `Uᵀ U = 1`): "a pre-RMSNorm network of dimension `d_model − 1`, with every read multiplied by `√(d_model/(d_model − 1))` and `ε` replaced by `ε d_model/(d_model − 1)`".

`card m = d − 1`: not a hypothesis, but forced by `Uᵀ U = 1` and `U Uᵀ = Z`: `card_add_one_eq_of_orthonormal_centering` (with `[Nonempty d]`) states `card m + 1 = card d`, by the trace. So `card d / card m = d_model/(d_model − 1)` under the hypotheses of the main theorem; it is stated, in a separate theorem. `exists_orthonormal_centering` gives such a `U` indexed by `Fin (card d − 1)`, so the statement is not vacuous (for an empty `d` too, with `0` columns).

The hypotheses: `hU : Uᵀ U = 1` and `hUZ : U Uᵀ = Z` say exactly "the columns of `U` are an orthonormal basis of `V`" (orthonormal, and the projection onto their span is the projection `Z` onto `V`). Both are needed: without `hUZ` (for example `U = I`, `m = d`) the reduced network would read `N_ε(h)` and not `N_ε(hZ)`. `hm : 0 < card m` is not needed for the conclusion: under `hU` and `hUZ`, `card m = 0` forces `card d ≤ 1`, so `Z = 0`, every read of the LayerNorm network sees `N_ε(0) = 0` and so `β`, and the reduced network, whose reads pass through an empty index type, sees `0` plus the bias `b_read + β W_read`; both sides are equal (by reading; the hypothesis only serves the proof, through `rmsRow_vecMul_transpose_of_orthonormal`). It is harmless: the papers have `d_model ≥ 2`, so `card m = d_model − 1 ≥ 1`.

`ε = 0` and `ε < 0`: the statements hold for every real `ε`, with Lean's conventions (`Real.sqrt` of a negative number is `0`, `0⁻¹ = 0`): a row with `‖v‖²/d + ε ≤ 0` is normalized to `0`, and since `‖v‖²/d + ε = (m/d)(‖y‖²/m + ε d/m)` for `v = y Uᵀ`, the same rows are normalized to `0` on both sides. The papers define `N_ε` for `ε > 0` (S Section 2: "RMSNorm with the constant `ε > 0`"); the Lean statements are stronger in `ε`, and true.

Computation (`ln_check.py`, `ln_check_eps.py`): the same networks as in Check 2, with a random orthonormal basis `U` of `V` (`|Uᵀ U − I|, |U Uᵀ − Z| ≤ 4.4 × 10^{-16}`): largest difference between `evalLN` and `evalB` of the reduced network of dimension `d − 1` with the constant `ε d/(d − 1)` and stream `Uᵀ S U`: `6.7 × 10^{-15}` for `ε = 0.3, 10^{-5}`; for stream matrices that commute with `Z` (not `0`, not `1`): `2.2 × 10^{-16}`. For `ε = −0.3, −3` and `ε = 0`, with Lean's conventions and `d = 4`, an exact basis of `V` from a Hadamard matrix and dyadic constant rows of `E` and `b_E` (so that `h_0 Z = 0` exactly; 47 rows normalized to `0`): largest difference `2.5 × 10^{-14}`, parts (i) and (ii). (A first run at `ε = 0` with a random `U` differed by `0.3`: a floating-point artefact, `x E Z` of size `10^{-17}` where it is `0` in exact arithmetic, and `N_0` is not continuous at `0`.)

The coordinator's check `layernorm_reduction_check_2026-11-25.py` (read): it uses an eigenvector basis of `Z` for `U` and tanh blocks only; mine adds attention blocks, random bases, general commuting `S`, and `ε ≤ 0`.

**Verdict: SAME** (named forms), **LEAN STRONGER** for the general statement (stream matrices commuting with `Z`, any `ε`, an embedding bias); true.

### Check 4. The functional dimension of a family (`Dimension/FunDimFamily.lean`, `Dimension/RankSubmersion.lean`), by reading and by compiling a copy

```lean
noncomputable def funDimOf {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (F : P → Matrix T dIn ℝ → Matrix T dOut ℝ) (p : P) : ℕ :=
  sSup {r : ℕ | ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ),
    r = Module.finrank ℝ (LinearMap.range
      (fderiv ℝ (fun q : P => fun i : Fin n => F q (X i)) p).toLinearMap)}
```
Against S Definition 4.1 ("`fd(θ) = max_X rank DF_X(θ)` […] where the maximum is over all finite batches `X`"): the batch map `q ↦ (F_q(x_1), …, F_q(x_n))`, its Fréchet derivative at `p`, the dimension of its range (the rank of the Jacobian), the supremum over all `n` and all batches of `n` inputs, with no restriction on the inputs. For a finite-dimensional `P` every rank is at most `dim P`, so the set is bounded, nonempty (`n = 0`), and the supremum is a maximum. Where a batch map is not differentiable at `p`, `fderiv` is `0` and that batch contributes the rank `0`; so `funDimOf F p` is the maximum over the batches at which the Jacobian exists (and `0` if there is none), which is the paper's definition wherever the paper's Jacobians exist. (For an infinite-dimensional `P`, `funDimOf` can be `0` by the convention `sSup ∅ = 0` of unbounded sets and `finrank = 0`; no use of it has such a `P`.) **SAME.**

The three `rfl` statements `funDim_eq_funDimOf`, `funDimB_eq_funDimOf`, `funDimSkips_eq_funDimOf` compile (`#print axioms` of each lists the three standard axioms), so `funDim`, `funDimB`, `funDimSkips` are literally `funDimOf` of their families: the definitions of the library audited earlier are this one.

`range_fderiv_eq_of_comp_of_section` (`f = g ∘ Φ` near `p`, `HasFDerivAt Φ Φ' p`, `Φ'` onto, `s` differentiable at `Φ p`, `s (Φ p) = p`, `g = f ∘ s` near `Φ p` ⟹ equal ranges of `fderiv ℝ f p` and `fderiv ℝ g (Φ p)`): true. If `g` is differentiable at `Φ p`, `Df(p) = Dg(Φ p) ∘ Φ'` by the chain rule; if `f` is differentiable at `p = s(Φ p)`, `g = f ∘ s` is differentiable at `Φ p`. So the two are differentiable together or not at all (and then both derivatives are `0`): this is why no differentiability of `f`, `g` (or `F₁`, `F₂`) need be asked. `funDimOf_eq_of_comp_of_section` follows batch by batch. **SAME** as the step of the proof of S Theorem A.5 (ii) and of Proposition A.15 (iii) ("by the chain rule every batch Jacobian … is that of the reduced network times this derivative … the same functional dimension"), in a form that needs no differentiability of the networks.

Is each hypothesis needed?
- **`hsurj` (the derivative of `Φ` is onto) is not needed.** With the section, `Dg(Φ p) = Df(p) ∘ Ds(Φ p)` as well, so `range Dg(Φ p) ⊆ range Df(p) ⊆ range Dg(Φ p)`. I compiled a copy of the theorem without `hsurj` (`/home/claude/audit33c/Audit33c.lean`, `audit_range_fderiv_eq_of_comp_of_section_noSurj`, axioms `propext`, `Classical.choice`, `Quot.sound`). So `funDimOf_eq_of_comp_of_section` holds without it too. This is not an error: the statement is true; one hypothesis is superfluous. In the applications the onto derivative is what produces the section (for Proposition A.15 (iii) see Check 5), so the hypothesis records the paper's argument.
- **The section (`hs`, `hsp`, `hF₂`) is needed** when `Φ` is only differentiable at `p`. Example with `P₁ = P₂ = ℝ`, `p = 0`, one-point index types: let `a_{k,n} = 2^{-k}(1 + 1/(n + k))` (`k, n ≥ 1`; for each `k` these lie in `(2^{-k}, 2^{-k+1})`, so the sequences are disjoint), `Φ(a_{k,n}) = a_{k,n+1}` and `Φ(q) = q` elsewhere. Then `Φ` is injective, `|Φ(q) − q| ≤ 2^{-k}/(k+1)² ≤ |q|/(k+1)²` with `k → ∞` as `q → 0`, so `HasFDerivAt Φ 1 0` (onto); its image misses the points `a_{k,1} → 0`. Let `F₁(q) = q` and `F₂(y) = Φ^{-1}(y)` on the image of `Φ` and `F₂(y) = 0` off it. Then `F₁ = F₂ ∘ Φ` everywhere, `funDimOf F₁ 0 = 1`, and `F₂` is not differentiable at `0` (it is `y` on the image and `0` at the `a_{k,1}`), so every batch contributes `0` and `funDimOf F₂ (Φ 0) = 0`. By reading. If `Φ` is strictly differentiable at `p` (for example `C¹`, as every map of the library is), a local section exists by the submersion theorem and the section hypotheses could be derived; the statement asks only `HasFDerivAt`, so it needs them.
- **`hΦ` is needed:** `E = ℝ²`, `F = ℝ`, `Φ(q) = q_1 + |q_2|`, `g(y) = y`, `f = g ∘ Φ`, `s(y) = (y, 0)`, `p = 0`: `g = f ∘ s`, `s(Φ 0) = 0`, `f` is not differentiable at `0` (range `0`) and `Dg(0)` has range `ℝ`. By reading.

**Verdict:** `funDimOf` SAME as Definition 4.1; the three `rfl` statements SAME; `range_fderiv_eq_of_comp_of_section`, `funDimOf_eq_of_comp_of_section` true, SAME as the chain-rule step, with one superfluous hypothesis (`hsurj`).

### Check 5. Part (iii) (`Residual/LayerNormRedundancy.lean`), by reading and by a computation

The file at `0e1bc98` has two `sorry` (`exists_hasFDerivAt_reduceLNParams_surjective`, `funDimOf_evalLNParams_eq_funDimB_reduceLN`); the three others are proved from them (`#print axioms Skips.funDimOf_evalLNParams_residual_add_skipless` lists `sorryAx`).

`ParamsLN A dIn dOut = ParamsB A dIn dOut × ((Fin (L + 1) → d → ℝ) × (Fin (L + 1) → d → ℝ))`: the weights `E`, `W_read,ℓ`, `W_write,ℓ`, `D`, the biases `b_E`, `b_read,ℓ`, `b_write,ℓ`, `b_D`, and the gains `γ_0, …, γ_L` and LayerNorm biases `β_0, …, β_L`: every parameter of the pre-LayerNorm network is counted. `reduceLNParams ε U q = (θ.reduceLN ε U γ, b.reduceLN ε U θ β)`: S's "the map from the parameters of the LayerNorm network to those of the reduced network", with the list of Check 3. SAME.

**`exists_hasFDerivAt_reduceLNParams_surjective`** (hypotheses `Uᵀ U = 1` and every entry of every gain nonzero; conclusion: a derivative `Φ'` of `reduceLNParams` at `q` that is onto): **true** at every such `q`. By reading: `reduceLNParams` is polynomial; along directions with `δγ = δβ = 0` its derivative is `δE ↦ δE U`, `δW_read ↦ √(d/m) Uᵀ diag(γ_ℓ) δW_read` (plus `β_ℓ δW_read` in the read bias), `δW_write ↦ δW_write U`, `δD ↦ √(d/m) Uᵀ diag(γ_L) δD`, `δb_read ↦ δb_read`, and the same on the other biases; `Uᵀ` has full row rank (`Uᵀ U = 1`), `diag(γ)` is invertible, `U` is injective, and the read biases and the readout bias absorb the terms `β δW`; so the derivative is onto already in the weights and biases. Computation (`ln_zero_gain.py`, exact derivative of `reduceLNParams`, tanh block, `d = 4`, width 5): rank `65` of `65` for a basis `U` of `V`, `84` of `84` for `U = I` (`m = d`). At gains with zero entries (the statement says nothing there): for a basis `U` of `V`, one zero entry in a gain still gives an onto derivative (`65/65`, for a read and for the readout: the kernel of `Uᵀ` is the line of `1`, so `Uᵀ` restricted to the other `d − 1` coordinates is invertible), two zero entries do not (`62/65`, a defect `width − 2`), a zero gain does not (`54/65`); for `U = I` one zero entry already does not (`80/84`). So under the statement's hypotheses (`Uᵀ U = 1` only), `hγ` is needed; with `U Uᵀ = Z` it could be weakened to at most one zero entry per gain.

**`funDimOf_evalLNParams_eq_funDimB_reduceLN`** ("at corresponding parameters both have the same functional dimension"): **true**. By reading: `evalLN_eq_evalB_reduceLN` gives `F₁ = F₂ ∘ Φ` at every parameter (with `hUZ`, `hm`, `hS`); with `γ`, `β` fixed at the values of `q`, `Φ` is linear in the weights and biases and onto (above), so with a linear right inverse `R` of that linear map, `s(y) = q + (R(y − Φ(q)), 0, 0)` is affine, `s(Φ q) = q` and `Φ ∘ s = id`, so `F₂ = F₁ ∘ s` everywhere; `funDimOf_eq_of_comp_of_section` and `funDimB_eq_funDimOf` (`rfl`) then give the equality. Nothing is asked of the blocks. Computation (`ln_rank.py`, `ε = 0.3`, two independent batches each, exact derivatives, rank at the largest gap):

| network | `S` | LayerNorm: `P`, `fd` (gap) | reduced: `P`, `fd` (gap) |
|---|---|---|---|
| tanh, `L = 2`, `d = 3`, width 4 | 0 | 104, 58 (`4.4e-12` / `3.8e-15`) | 61, 58 (`4.1e-12` / `1.0e-15`) |
| | 1 | 104, 60 (`5.0e-09` / `3.9e-15`) | 61, 60 (`3.7e-09` / `6.7e-16`) |
| attention (2 heads of width 2), `L = 1`, `d = 4`, `T = 3` | 0 | 127, 57 (`2.8e-03` / `7.7e-15`) | 87, 57 (`9.2e-04` / `4.8e-15`) |
| | 1 | 127, 60 (`1.3e-02` / `5.6e-15`) | 87, 60 (`1.7e-02` / `3.7e-15`) |
| attention then tanh (width 4), `L = 2`, `d = 4`, `T = 3` | 0 | 171, 81 (`2.7e-09` / `2.6e-14`) | 115, 81 (`2.0e-09` / `3.4e-15`) |
| | 1 | 171, 88 (`5.7e-05` / `2.0e-14`) | 115, 88 (`4.3e-05` / `9.0e-15`) |

The second batch gives the same ranks in every row. In all six, `fd` of the LayerNorm network equals `fd` of the reduced network. (Sanity check of the reduced tanh network, `m = 2`: redundancy `3 = (L + 1) dim O(2)` skipless and `1 = dim O(2)` residual.)

Is `hγ` needed for this conclusion? At gains with zero entries (`ln_zero_gain.py`, tanh, `d = 4`, `L = 1`): one zero entry, `fd` equal (`59 = 59` skipless, `62 = 62` residual); two zero entries in one gain, `58 < 59` and `61 < 62`; a zero gain, `7 < 12` and `28 < 33`. So the conclusion fails without a condition on the gains, and the paper's "nonzero entries" is enough. (In these cases the differences `fd(residual) − fd(skipless)` still agree, `3 = 3` and `21 = 21`; the statements do not claim that.)

**`funDimOf_evalLNParams_skipless`, `funDimOf_evalLNParams_residual`**: the general statement at `S = 0` and `S = 1` (with `Uᵀ 0 U = 0`, `Uᵀ 1 U = 1`). SAME.

**`funDimOf_evalLNParams_residual_add_skipless`** (`fd_LN(res) + fd_red(skip) = fd_LN(skip) + fd_red(res)`) against "the difference in redundancy between the skipless and the residual version of the LayerNorm network equals the difference for the reduced networks". Written out: `red = P − fd`, with `P_LN` the number of parameters of the LayerNorm network and `P_red` that of the reduced network, each the same for both versions (`ParamsLN` and `ParamsB` do not depend on `S`, and the papers: "the skipless and the residual network have the same `P` parameters"). Then `red_LN(skip) − red_LN(res) = fd_LN(res) − fd_LN(skip)` and `red_red(skip) − red_red(res) = fd_red(res) − fd_red(skip)`, and the equality of the two differences is the additive equation, with no subtraction in `ℕ`. The coordinator's reading is exact. The proof's further sentence, "the redundancy of the LayerNorm network is that of the reduced network plus the difference of the parameter counts", is `P_LN − fd_LN = (P_red − fd_red) + (P_LN − P_red)`, which is the equality of the functional dimensions; it is not stated with the redundancies, and need not be. Computation: `60 + 58 = 58 + 60`, `60 + 57 = 57 + 60`, `88 + 81 = 81 + 88`; the differences of the redundancies are `2 = 2`, `3 = 3`, `7 = 7`.

Whether the gains and LayerNorm biases are counted as parameters does not change any functional dimension here (the derivative is onto already without them, so the range of every batch Jacobian is the same), and the parameter count cancels in the differences: the statement is the same whichever reading of "the parameters of the LayerNorm network" one takes. The block biases do matter: if the LayerNorm network had no read biases, the read bias `β W` of the reduced network would range only over the row space of `W`, and the map would not be onto for blocks wider than `d_model`. The paper's proof lists "`b + βW` for each read", so its LayerNorm network has read biases; Lean has them.

**Verdicts:** `ParamsLN`, `evalLNParams`, `reduceLNParams` SAME; the surjectivity statement SAME (true); the equality of functional dimensions SAME (true); the two named forms SAME; the additive form SAME as Proposition A.15 (iii) (true, given the two open statements, which are true).

### Check 6. D Proposition A.3 against the same statements, by reading

D Proposition A.3 is stated for the networks of D Section 2, equation (2): `h_ℓ = g_ℓ(χ(h_{ℓ−1}))`, without skips (D's proof: "Every hidden state is the output of a write"); S Proposition A.15 for "a pre-LayerNorm network, skipless or residual" (S's proof: "Every hidden state is a sum of writes, directly in a skipless network and through the skips in a residual one"). The parts (i) and (ii) have the same words in the two papers, D writing `LN(h) = γ ⊙ N_ε(hZ) + β` and S the formula; D defines `N_ε` for `ε ≥ 0` (Section 2) with the network for `ε = 0` defined where no row vanishes, S for `ε > 0`. D says nothing that S (i), (ii) does not, except that its scope is skipless; D's network has a "write bias `b`" in (i), so biases are allowed there too (D Section 2, Scope: the reductions hold "with biases"). Covered: the skipless named forms `evalLN_eq_evalB_centerLN_skipless`, `evalLN_eq_evalB_reduceLN_skipless` and `sum_hiddenB_centerLN` with `S = 0`, for every `ε` (Lean's `N_0(0) = 0` agrees with D's network wherever D defines it). D has no part (iii). **SAME.**

### Check 7. Drift checks, by reading

- The functional dimension is the maximum over all finite batches, with no restriction on the inputs: `funDimOf` and `funDimB` are (Check 4).
- Hypotheses in Lean that the papers do not have: `hS` (stream matrices commuting with `Z`), only in the general forms, discharged for `S = 0, 1`; `hU`, `hUZ`, which are "an orthonormal basis of `V`"; `hm : 0 < card m`, which follows from `d_model ≥ 2` (S and D, Scope) and is not needed for the conclusions (Check 3); `hγ`, which is the paper's "nonzero entries". `[Nonempty d]` in `card_add_one_eq_of_orthonormal_centering` only.
- Hypotheses of the papers not in Lean: `ε > 0` (S) or `ε ≥ 0` (D): Lean has any real `ε`; `d_model ≥ 2`: not needed; the scope of blocks (MLP width, attention width): Lean has any blocks. None is missing.
- One gain and bias per LayerNorm (Check 1): more general than one shared pair, and the identities hold pointwise, so they include the shared case; for (iii) the functional dimensions do not depend on whether the gains are parameters (Check 5).
- The embedding bias `b_E`: not in Proposition A.15, but in S's networks with biases (proof of Theorem A.5, "with `h_0 = xE + b_E`"; Lemma A.27); Lean maps it to `b_E Z` and `b_E U`, which (i) and (ii) need (it is written into `h_0`).
Nothing drifted.

### Check 8. The index rows, registrations, axioms

Registrations in `/home/claude/lp/lean/checks/Axioms.lean`: `RankSubmersion.lean` 1 of 1 (line 2113), `FunDimFamily.lean` 4 of 4 (2114 to 2117), `Network/LayerNorm.lean` 9 of 9 (2183 to 2191); `LayerNormRedundancy.lean` none (in work, as its row says). Axioms (copy `/home/claude/audit33c/Audit33c.lean`, compiled with `lake env lean` against the build of `0e1bc98` after checking that no `lake build` ran): all fourteen proved theorems depend on `propext`, `Classical.choice`, `Quot.sound` only; `funDimOf_evalLNParams_residual_add_skipless` depends on `sorryAx` through the two open statements.

Rows of `/home/claude/lp/lean/STATEMENTS.md`:
- Line 1045 (`RankSubmersion.lean`): true. It could say that the onto hypothesis is not used by the conclusion (the section alone gives the equality).
- Line 1046 (`FunDimFamily.lean`): true; the same remark.
- Line 1047 (`Network/LayerNorm.lean`): true. Imprecise in two places: part (ii) also asks that the stream matrices commute with `Z` and that `U` have at least one column (`0 < card m`); the row states the first only for (i).
- Line 1048 (`LayerNormRedundancy.lean`): true of the statements; it omits `0 < card m` as above. Status "in work": right.
- Lines 369 to 373 list the four files as not yet compared; after this report they are compared.

## Part 2: the statements, file by file

| name | paper sentence | verdict | note |
|---|---|---|---|
| `range_fderiv_eq_of_comp_of_section` | S proof of Thm A.5 (ii): "the Jacobian … times the derivative of `Φ`, by the chain rule; … the same rank" | SAME | true; `hsurj` superfluous (copy compiled without it); the section and `hΦ` are needed |
| `funDimOf` | S Definition 4.1 | SAME | `fderiv = 0` where a batch map is not differentiable: the maximum over the batches where the Jacobian exists |
| `funDim_eq_funDimOf`, `funDimB_eq_funDimOf`, `funDimSkips_eq_funDimOf` | (the library's definitions are cases of Definition 4.1) | SAME | `rfl` |
| `funDimOf_eq_of_comp_of_section` | S Thm A.5 (ii): "with the same functional dimension at `θ` and at `Φ(θ)`" | SAME | true; `hsurj` superfluous |
| `layerNorm` | S Prop A.15, D Prop A.3: `LN(h) = γ ⊙ N_ε(hZ) + β` | SAME | mean over `card d` |
| `Arch.withNorm` | (the network with another fixed map) | SAME | |
| `hiddenLN`, `evalLN` | "a pre-LayerNorm network, skipless or residual, whose reads and readout see `LN(h)`" | SAME (more general) | `L + 1` LayerNorms with their own `γ_ℓ`, `β_ℓ`; biases; any stream matrices; any blocks |
| `Params.centerLN`, `Biases.centerLN` | (i) "Replacing each read `W` by `diag(γ)W` with the added bias `βW`, and each write `W`, write bias `b` and embedding `E` by `WZ`, `bZ` and `EZ`" | SAME | also the readout (`diag(γ_L) D`, `b_D + β_L D`) and the embedding bias (`b_E Z`) |
| `evalLN_eq_evalB_centerLN` | (i) "gives a network that computes the same function … whose reads see `N_ε(h)`" | LEAN STRONGER | stream matrices commuting with `Z` (needed: the proving agent's example, checked); any `ε` |
| `evalLN_eq_evalB_centerLN_skipless` | D Prop A.3 (i); S Prop A.15 (i), skipless | SAME (stronger in `ε`) | |
| `evalLN_eq_evalB_centerLN_residual` | S Prop A.15 (i), residual | SAME (stronger in `ε`) | |
| `sum_hiddenB_centerLN` | (i) "whose hidden states lie in `V`" | SAME | every hidden state `h_0, …, h_L`, every token |
| `Params.reduceLN`, `Biases.reduceLN` | S proof of (iii): "`√(d_model/(d_model − 1)) Ū^⊤ diag(γ)W` and `b + βW` for each read, `WŪ` and `bŪ` for each write, `EŪ` …, and the analogous expressions for the readout" | SAME | `card m` for `d_model − 1` (forced); embedding bias `b_E U` |
| `evalLN_eq_evalB_reduceLN` | (ii) "a pre-RMSNorm network of dimension `d_model − 1`, with every read multiplied by `√(d_model/(d_model − 1))` and `ε` replaced by `ε d_model/(d_model − 1)`" | LEAN STRONGER | stream `Uᵀ S U` for `S` commuting with `Z`; any `ε`; `hm` not needed (harmless) |
| `evalLN_eq_evalB_reduceLN_skipless`, `_residual` | D Prop A.3 (ii); S Prop A.15 (ii) | SAME (stronger in `ε`) | |
| `card_add_one_eq_of_orthonormal_centering` | (ii) "of dimension `d_model − 1`" | SAME | |
| `exists_orthonormal_centering` | (ii) "In an orthonormal basis of `V`" | SAME | non-vacuity |
| `ParamsLN`, `evalLNParams` | "the parameters of the LayerNorm network" | SAME | all weights, biases, gains, LayerNorm biases |
| `reduceLNParams` | "the map from the parameters of the LayerNorm network to those of the reduced network" | SAME | |
| `exists_hasFDerivAt_reduceLNParams_surjective` (`sorry`) | "the derivative of the map … is onto" | SAME | true at every `q` with nonzero gain entries (by reading; numerically `65/65`, `84/84`); `hγ` needed when only `Uᵀ U = 1` is asked |
| `funDimOf_evalLNParams_eq_funDimB_reduceLN` (`sorry`) | "at corresponding parameters both have the same functional dimension" | SAME | true (affine section, by reading; six cases computed); false without a condition on the gains (two zero entries: `58 < 59`) |
| `funDimOf_evalLNParams_skipless`, `_residual` | the same, by name | SAME | |
| `funDimOf_evalLNParams_residual_add_skipless` | S Prop A.15 (iii) | SAME | the additive form is exact (same `P` for both versions) |

## For the authors of the papers

Nothing false, vacuous or drifted. Places where the papers leave a condition or a step unwritten:
1. **S Proposition A.15 (i) and D Proposition A.3 (i)** list the reads, writes, write biases and the embedding, but not the readout, which also sees `LN(h_L)`: it becomes `diag(γ_L) D` with the added bias `β_L D` (S's proof of (iii) says "the analogous expressions for the readout"; (i) could say it too). With an embedding bias `b_E` (S's networks with biases have one), it becomes `b_E Z` (and `b_E Ū` in (ii)).
2. **Both papers write one pair `γ`, `β`.** A pre-LayerNorm network has one LayerNorm per hidden state, `L + 1` in all, each with its own gain and bias; the statement holds for each, with `γ_ℓ` in the read of block `ℓ + 1` and `γ_L` in the readout. "with `h`, `γ` and `β` row vectors" could add "one pair for each hidden state".
3. **S Proposition A.15 (iii) needs the read biases `b` to be parameters of the LayerNorm network.** Otherwise the reduced read bias `βW` ranges only over the row space of `W`, and for blocks wider than `d_model` the derivative is not onto. The proof says "`b + βW` for each read", so the network has them; the statement could say "with biases", since S's main results are stated without biases.
4. **The chain-rule step** ("every batch Jacobian of the LayerNorm network is that of the reduced network times this derivative") assumes the reduced network differentiable at the reduced parameters. For blocks that are not differentiable everywhere (ReLU), the Lean form uses a section of the map (here an affine one, with `γ`, `β` fixed), which gives both differentiability and the same rank; with a section, the onto property is used only to build it.
5. **The condition on the gains** is enough and can be weakened: with `Ū` a basis of `V`, one zero entry per gain still gives an onto derivative (the kernel of `Ū^⊤` is the line of `1`); two zero entries in one gain do not, and then the functional dimensions differ (computed: `58` and `59`).

## Corrections for `STATEMENTS.md`

- Lines 369 to 373: move `Dimension/RankSubmersion.lean`, `Dimension/FunDimFamily.lean`, `Network/LayerNorm.lean` and `Residual/LayerNormRedundancy.lean` (statements) to the compared files: "compared by the thirty-third audit, part C: nothing false, vacuous or drifted (`ai_notes/lean-statement-audit-thirtythird-c-2026-11-25.md`)". (`Symmetry/BiasesSymmetryCount.lean`, on line 373 too, was not part of this audit.)
- Line 1045 and line 1046: add "(the onto hypothesis is not needed for the conclusion once the section is given; it is kept because it is what produces the section)", or drop `hsurj` from both statements.
- Line 1047: in (ii), add "for stream matrices that commute with `Z`" and "with at least one column (`0 < card m`)".
- Line 1048: add "with at least one column" after "for `U` with orthonormal columns spanning `V`".

## What I could not check

- The two open statements of `Residual/LayerNormRedundancy.lean` are not proved; I argued both true by hand (Check 5) and computed them on three networks, not in Lean.
- The counterexamples of Check 4 (dropping the section; dropping `hΦ`) are by reading, not compiled.
- Numeric functional dimensions are lower bounds from finite batches (two batches per case, more rows than parameters, the same ranks); they were not certified in exact arithmetic.

Commit read at the end: `0e1bc98` (the four files unchanged in the working tree).
