STATUS: complete

# Thirty-third audit, part A, of Lean statements against the papers: one attention block with biases (S Theorem B.1 (i)); the symmetries inside attention blocks with biases; the count of S Lemma A.8 as a dimension (25 November 2026)

Commit read at the start: `0e1bc98` of `/home/claude/lp` (branch `lean-plus`). Papers: `<scratchpad>/skips.txt`.
Files with `sorry` among the six: none. The checks are written in the order in which they were done (1, 5, 2, 6, 3, 4, 7, 8).
Scripts: `/home/claude/audit33a/` (`attn_bias_rank.py`, `extra.py`, `extra2.py`, `reduction.py`, `count_hrw.py`, `Ax33a.lean`).

## Part 1: checks

### Check 1. The frame (by reading)

`Network/Biases.lean`: `hiddenB` sets `h_0 = x E + b_E` and
`h_ℓ = h_{ℓ-1} M_ℓ + f_ℓ(χ(h_{ℓ-1}) W_read^ℓ + b_read^ℓ) W_write^ℓ + b_write^ℓ`, every bias a row added to
every token; `evalB` is `χ(h_L) D + b_D`. For `Arch.attention` (`Network/Attention.lean`) the read columns are
`H × (dh ⊕ (dh ⊕ dh))` (query `Sum.inl`, key `Sum.inr (Sum.inl)`, value `Sum.inr (Sum.inr)`), so the read bias is
`[b_Q | b_K | b_V]`, added to the queries, keys and values of every token before the scores and the weighted sum,
and the write bias `b_write` is the paper's `b_O` (added once, after the sum over heads and the output projection).
This is the paper's block with biases (line 2676: "`b_{Q,i}`, `b_{K,i}`, `b_{V,i}` on the queries, keys and values,
`b_O` on the output projection").

The mask: `attnWeights sees Z` is `exp(Z t s) / Σ_{s' seen} exp(Z t s')` at the seen tokens and `0` elsewhere. For a
token that sees no token, the denominator is `0` and Lean's `x / 0 = 0` makes the whole row zero, so that token's
block output is `b_O` alone and its value biases do not enter (the weights do not sum to one). The paper's argument
"the value biases enter only through `γ`, since the weights of a token sum to one" needs every token to see some
token; see below for `hsee`.

**`hsee : ∀ t, ∃ s, sees t s` is needed. By a computation** (`/home/claude/audit33a/attn_bias_rank.py` and
`extra.py`, my own transcription of the block with biases from `Network/Biases.lean` and `Network/Attention.lean`,
exact derivatives by the complex step with `h = 1e-30`, the largest real part subtracted before `exp`, rank read at
the largest gap of the singular values, `3P/(T d_out) + 4` random inputs). The mask "causal, but token 0 sees no
token" (token 2 still sees itself and token 1, so every other hypothesis holds):

| `(T, d, d_in, d_out, H, d_h)` | skipless rank / claimed | residual rank / claimed | gap (decades) |
|---|---|---|---|
| (3, 2, 2, 2, 2, 1) | 18 / 16 | 22 / 20 | 12.8, 13.5 |
| (3, 2, 3, 3, 1, 2) | 19 / 17 | 23 / 21 | 12.5, 13.5 |
| (3, 2, 2, 2, 3, 1) | 25 / 23 | 29 / 27 | 12.0, 11.9 |
| (2, 3, 3, 4, 2, 2) | 46 / 43 | 55 / 52 | 12.6, 12.8 |
| (3, 2, 2, 2, 1, 1) | 10 / 9 | 14 / 13 | 14.4, 13.9 |

So without `hsee` the values of Theorem B.1 (i) with biases are false, and the rank is higher by
`min(H d_h, d_model)`, not by `H d_h` in general: at the blind token the moved value biases change the output by
`−∑_i ν_i W_{O,i} D`, so only the `ν` with `∑_i ν_i W_{O,i} = 0` stay flat, and that map has rank `min(H d_h, d)` at
generic weights (rows 3 and 4: `H d_h = 3 > d = 2` gives `+2`, `H d_h = 4 > d = 3` gives `+3`). The module docstring of
`OneBlock/AttentionBiasesDim.lean` says "the rank of the Jacobian is higher by `H d_h = 2`" for its example, where
`H d_h = d = 2`: true there, but the general excess is `min(H d_h, d)`.

`hsee` holds for both masks of the paper (each token sees itself); Lean proves it in the `_noMask` and `_causal`
statements (`fun t => ⟨t, trivial⟩`, `fun t => ⟨t, le_refl t⟩`). By reading.

Verdict of check 1: the frame is the paper's attention block with biases (SAME); `hsee` is a true hypothesis of both
masks of the paper and is needed (exact counterexamples of the value without it).

### Check 5 (first part). The values, recomputed (by a computation)

Same script (`/home/claude/audit33a/attn_bias_rank.py`), one block, random weights, biases random and biases `0`,
without mask and causal, with and without the skip; claimed `P − 2d² − 2d − 2Hd_h² − 2Hd_h` (skipless) and
`P − d² − 2d − 2Hd_h² − 2Hd_h` (residual). All 40 runs EQUAL, every gap between 10.8 and 14.6 decades:

| `(T, d, d_in, d_out, H, d_h)` | case | `P` | skipless rank (claim) | residual rank (claim) |
|---|---|---|---|---|
| (3, 2, 2, 2, 2, 1) | `H d_h = d` | 36 | 16 (16) | 20 (20) |
| (3, 2, 3, 3, 1, 2) | `d_h = d` | 41 | 17 (17) | 21 (21) |
| (2, 3, 3, 4, 2, 2) | `H d_h > d` | 91 | 43 (43) | 52 (52) |
| (4, 2, 2, 2, 3, 1) | `H d_h > d` | 47 | 23 (23) | 27 (27) |
| (3, 3, 4, 3, 1, 3) | `d_h = d = 3` | 75 | 27 (27) | 36 (36) |

each for no mask and causal, biases random and `0` (the same rank in all four). The gain is `d²` in every row. The
rank at biases `0` agrees with the pointwise theorems, whose conditions `OneBlockGenericAttention p.1` are on the
weights only (so they hold at every bias, including `0`).

### Check 5 (second part). The hypotheses of the theorem, against what Lean asks (by reading and by a computation)

Lean asks, in the six `ae_` statements: `[μ.IsAddHaarMeasure]` on `ParamsB` (the pairs of weights and biases),
`2 ≤ card d`, `card d ≤ card dIn`, `card d ≤ card dOut`, `card (dh 0) ≤ card d`, `card d ≤ card (H 0) * card (dh 0)`,
and in the general three `hsee` and two distinct tokens `t₁ ≠ t₂` with `sees t₂ t₂`, `sees t₂ t₁` (the `_noMask`
three ask `[Nontrivial T]`, the `_causal` three `T = Fin n`, `2 ≤ n`). These are exactly the theorem's
"`d_model ≥ 2`, … input and output dimensions at least `d_model`, … heads of width `d_h ≤ d_model`, causal or not,
on sequences of at least two tokens … width at least `d_model`, where the width of an attention block is `H d_h`",
plus `hsee` and the token `t₂`, which both masks of the paper satisfy. The pointwise theorems
(`funDimB_attention_oneBlock`, `_residual`) ask `OneBlockGenericAttention p.1`, conditions on the weights only
(ranks of `E`, `D`, of each `W_{Q,i}`, `W_{K,i}`, `W_{V,i}`, `W_{O,i}`, of the queries of all heads and of the write,
and one `v` with `B_i v^⊤` nonzero and pairwise non-collinear and every `v C_i ≠ 0`), and nothing on the biases: they
hold at every bias, which is more than "for generic parameters" (LEAN STRONGER there).

Which are needed, computed with the same script (`/home/claude/audit33a/extra.py`, `extra2.py`, no mask and causal):

* **`H d_h ≥ d` is needed for the skipless value** when `d_out > d`: `(T, d, d_in, d_out, H, d_h) = (3, 3, 5, 5, 1, 2)`:
  skipless rank `33` against the claimed `35`; `(3, 3, 5, 5, 2, 1)`: `37` against `39`; `(3, 3, 5, 5, 1, 1)`: `24`
  against `28`; `(3, 2, 4, 4, 1, 1)`: `17` against `19` (every gap at least 12.8 decades). The deficit is
  `(d − H d_h)(d_out − d)` in all four: the readout `D` sees the hidden state `h_1` only on the affine span of the rows of
  the `W_{O,i}` and `b_O`, of dimension `H d_h`. With `d_in = d_out = d` the narrow block gave the claimed value
  (`(3, 3, 3, 3, 1, 2)`, `(3, 3, 3, 3, 2, 1)`), so the deficit is not seen there. **With the skip the value held in all
  eight narrow runs** (ranks `44`, `48`, `37`, `23` equal to the claims): for the residual network the width condition
  was not needed in these cases; Lean asks it for both values, as the paper does.
* **`d ≥ 2`**: for `d = 1` the value held in every run, `(3, 1, 1, 1, 1, 1)`, `(3, 1, 2, 2, 1, 1)`, `(3, 1, 1, 1, 2, 1)`,
  `(3, 1, 3, 3, 2, 1)`, both networks, both masks; with two heads the `B_i v^⊤` are then collinear, so Step 2 of the paper
  does not apply, but the biases `½ (β_i v^⊤ − log k)` of the two tanh units differ, so they are not twins. Lean asks
  `d ≥ 2` (the paper's hypothesis, used for `exists_v`); not needed in these cases.
* `d_in ≥ d`, `d_out ≥ d`, `d_h ≤ d`: needed for the rank conditions of `OneBlockGenericAttention` (the rank of `E`, `D`,
  `W_{Q,i}` cannot be `d`, `d`, `d_h` otherwise); I did not compute the values without them.
* Two tokens with `t₂` seeing itself and another: the paper's "sequences of at least two tokens"; with one token the
  softmax is constant and the score matrices drop out, so the value cannot hold (not computed).

The six statements by name (by reading): `_noMask` uses `fun _ _ => True` with `[Nontrivial T]` (at least two tokens);
`_causal` uses `T = Fin n`, `2 ≤ n`, `sees t s ↔ s ≤ t`, with `t₁ = 0`, `t₂ = 1`. Both are the paper's masks.
`ae_funDimB_attention_oneBlock_residual_eq_add(_noMask, _causal)`: `fd(residual) = fd(skipless) + d²` at almost every
pair, the theorem's "the skip raises the functional dimension by exactly `d_model²`" (SAME). The values, written
additively (`fd + 2d² + 2d + 2Hd_h² + 2Hd_h = P`, `fd + d² + 2d + 2Hd_h² + 2Hd_h = P`), are Theorem B.1 (i) with biases
for attention ("both values are … `2 d_model + 2 H d_h` lower for attention") and the count at line 2733 ("`2 d_model +
2 H d_h` more with biases"): SAME. `funDimB` with `P = finrank (ParamsB …)` counts the biases ("counted in `P`").

Verdict of check 5: the values are **true** in every case computed (40 runs, plus the narrow and `d = 1` runs for the
residual network); the six `ae_` statements are **SAME** as Theorem B.1 (i) with biases for attention blocks, with the
paper's hypotheses and `hsee` (true of both masks); the two pointwise statements are **LEAN STRONGER** (every bias).

### Check 2. The symmetries inside an attention block with biases (`Symmetry/AttentionHeadsBiases.lean`, `Dimension/UpperBoundAttentionBiases.lean`)

**The four families, by reading, against the symmetries.** With `q_t = h_t W_{Q,i} + b_{Q,i}`,
`k_s = h_s W_{K,i} + b_{K,i}`, `v_s = h_s W_{V,i} + b_{V,i}`:

* `headDirQKB p Γ`: `η_{Q,i} = W_{Q,i} Γ_i`, `η_{K,i} = −W_{K,i} Γ_i^⊤` (from `headDirQK`), `η_{b_Q,i} = b_{Q,i} Γ_i`
  (`∑_{k'} b_Q(k') Γ(k', k)`), `η_{b_K,i} = −b_{K,i} Γ_i^⊤` (`−∑_{k'} b_K(k') Γ(k, k')`), `0` elsewhere. This is the
  velocity of `q ↦ q G`, `k ↦ k G^{−⊤}`, `G = e^{τΓ_i}`, which keeps `q_t k_s^⊤`: the paper's `Γ_i` "between the queries
  and keys", now acting on `b_Q`, `b_K` too. Signs right.
* `headDirVOB p Γ'`: `η_{V,i} = W_{V,i} Γ'_i`, `η_{O,i} = −Γ'_i W_{O,i}`, `η_{b_V,i} = b_{V,i} Γ'_i`, `b_O` untouched: the
  velocity of `v ↦ v G'`, `W_O ↦ G'^{−1} W_O`, which keeps `∑_s a_ts v_s W_{O,i}`. Signs right.
* `keyShiftDir κ`: `η_{b_K,i} = κ_i` only. A shift of `k_s` by `τκ_i` adds `τ ⟨q_t, κ_i⟩/√d_h` to every score of row
  `t`, which the softmax ignores, for every mask (also for a row with no seen token, which stays `0`): "The key biases
  drop out, since they shift all scores of a token equally."
* `valueShiftDir p ν`: `η_{b_V,i} = ν_i`, `η_{b_O} = −∑_i ν_i W_{O,i}`. Adding `τν_i` to every value adds
  `τ (∑_s a_ts) ν_i W_{O,i}` to the output at `t`, which is `τ ν_i W_{O,i}` if the weights of row `t` sum to one: "the
  value biases enter only through `γ`, since the weights of a token sum to one". Signs right; this needs `hsee` (check 1).

Each is stated as `InsideBlocksB` (`insideBlocksB_headDirQKB`, `_headDirVOB`, `_keyShiftDir` for every mask and every
`χ`, `_valueShiftDir` under `hsee`). `InsideBlocksB` (thirty-second report, check 2) asks a curve through `p` with the
given velocity that keeps `E`, `D`, `b_E`, `b_D` and every block map `n ↦ f(n W_read + b_read) W_write + b_write` at
every `n`: the curves `e^{τΓ}` and the lines `p + τ η` do this, by the computations above. The thirty-second report
checked the last two curves numerically (block map kept to `1e-14`). True as stated.

**`headDirB_injective`.** `headDirB p (Γ, Γ', κ, ν)` has the query columns `W_{Q,i} Γ_i`, the value columns
`W_{V,i} Γ'_i`, the key biases `−b_{K,i} Γ_i^⊤ + κ_i` and the value biases `b_{V,i} Γ'_i + ν_i`; with `hQ` and `hV` the
first two give `Γ`, `Γ'`, and then the biases give `κ`, `ν`. True. Without each hypothesis it is false, exact examples
(by reading): one block, one head, `d_h = 1`. Without `hQ`: `W_Q = W_K = 0`, `b_Q = b_K = 0` (any `W_V` of rank `1`, so
`hV` holds): `headDirB p (1, 0, 0, 0) = 0` (every component is a multiple of `W_Q`, `W_K`, `b_Q` or `b_K`), not injective.
Without `hV`: `W_V = 0`, `W_O = 0`, `b_V = 0` (`W_Q` of rank `1`): `headDirB p (0, 1, 0, 0) = 0`. Each hypothesis could be
replaced by another (the keys `W_K`, or `W_O` of full row rank), so they are sufficient conditions, each needed in the
sense that dropping it makes the statement false; both hold at generic weights for `d_h ≤ d` (the paper's
"every `W_{Q,i}`, `W_{K,i}`, `W_{V,i}` and `W_{O,i}^⊤` has rank `d_h`").

**The two bounds** `funDimB_add_le_residual_attention`, `funDimB_add_le_skipless_attention`:
`fd + d² + (L+1)d + 2∑_ℓ H_ℓ d_{h,ℓ}² + 2∑_ℓ H_ℓ d_{h,ℓ} ≤ P` (identity skips) and
`fd + (L+1)(d² + d) + 2∑ H d_h² + 2∑ H d_h ≤ P` (no skips, with `hw`), for `χ = id`, under `hsee`, `hE`, `hQ`, `hV`.
By reading: they are `funDimB_add_le_*_of_insideBlocksB` (thirty-second report, check 3: true) with `V` the range of
`headDirB p`, which lies in the span of `InsideBlocksB` (sum of four instances, `hsee`), satisfies `hrw` (from `hV`: read
and read bias `0` force `Γ'_ℓ = 0` and `ν_ℓ = 0`, so the write `−Γ' W_O` and the write bias `−∑ ν W_O` are `0`), and has
dimension `2∑ H d_h² + 2∑ H d_h` (injectivity). True. `hsee` is needed for them too: in the blind-token example of
check 1, `(3, 2, 2, 2, 2, 1)`, skipless, `fd = 18` and `18 + 2·4 + 2·2 + 2·2 + 2·2 = 38 > P = 36`.

**Where the paper states `s` for attention with biases.** It does not write `s = 2 H d_h² + 2 H d_h` anywhere. The `s`
of Theorem B.1 is the count without biases ("`s` counts the changes of basis inside the heads", line 2037; Step 3: "dim
`K(θ)` is `2d² + 2Hd_h²` … and `2 d_model + 2 H d_h` more with biases"). In Lemma A.8, `s` is "the symmetries inside
blocks"; for attention with biases the shifts of the key biases and the value biases moved into the output bias are
symmetries inside the block (Step 1: "which the translations at `h_0` and `h_1`, the shifts of the key biases and the
value biases … span"), so Lemma A.8's `s` is `2 H d_h² + 2 H d_h` per block, and with `L = 1` Lemma A.8 gives
`d² + 2d + 2Hd_h² + 2Hd_h` and `2d² + 2d + 2Hd_h² + 2Hd_h`: the `2 d_model` of the translations plus the `2 H d_h` of
the theorem's "`2 d_model + 2 H d_h` lower for attention". The two agree. The module docstring says this
("the `s = 2 H d_h²` of Theorem B.1 counts the changes of basis inside the heads only, and the theorem names the
`2 H d_h` apart"): right. The paper could say once that with biases the `s` of an attention block is
`2Hd_h² + 2Hd_h`.

**The almost-everywhere forms** (`UpperBoundAttentionBiases.lean`, by reading): `∀ᵐ p ∂μ` for every
`[μ.IsAddHaarMeasure]` on `ParamsB` (the pairs), via `ae_paramsB_of_forall_ae` from conditions on the weights that hold
at almost every weight for every Haar measure; hypotheses `card d ≤ card dIn` (for `E` of rank `d`), `card (dh ℓ) ≤ card d`
(for `W_Q`, `W_V` of rank `d_h`) and, skipless only, `card d ≤ card (H ℓ) * card (dh ℓ)` (for the writes of rank `d`),
plus `hsee`. These are the conditions of Theorem B.1 per block; Lemma A.8 writes none, and the count as a dimension
needs some (check 6). Generic is "almost every", never "there is a point". The docstring of the file says equality is
"computed for 24 networks of two blocks"; I did not recompute two blocks.

Verdict of check 2: the four families are the paper's, with the right signs and the right entries; each is an
`InsideBlocksB` direction as stated (the last under `hsee`); `headDirB_injective` true, `hQ`, `hV` each needed (exact
examples); the two bounds and their `ae` forms true, the count of Lemma A.8 with `s = 2Hd_h² + 2Hd_h` per block, which
agrees with Theorem B.1 (i): **SAME** (as bounds; LEAN WEAKER than an equality, which the paper's Lemma A.8 does not
claim for the functional dimension either).

### Check 6. The count as a dimension (`Symmetry/BiasesSymmetryCount.lean`)

```lean
theorem finrank_span_symmetryDirs_residual (p : ParamsB A dIn dOut) (V : Submodule ℝ (ParamsB A dIn dOut))
    (hV : V ≤ Submodule.span ℝ {η | InsideBlocksB A p η})
    (hrw : ∀ η ∈ V, ∀ ℓ, η.1.read ℓ = 0 → η.2.read ℓ = 0 → η.1.write ℓ = 0 ∧ η.2.write ℓ = 0)
    (hE : p.1.E.rank = Fintype.card d) :
    Module.finrank ℝ (Submodule.span ℝ {η | ∃ X g v, v ∈ V ∧
        η = cobDirB p (fun _ => X) + (0, translateDir p.1 g) + v})
      = Fintype.card d ^ 2 + (L + 1) * Fintype.card d + Module.finrank ℝ V
theorem finrank_span_symmetryDirs_skipless … (hE …) (hw : ∀ ℓ, (p.1.write ℓ).rank = Fintype.card d) :
    Module.finrank ℝ (Submodule.span ℝ {η | ∃ X g v, v ∈ V ∧ η = cobDirB p X + (0, translateAtDir p.1 g) + v})
      = (L + 1) * (Fintype.card d ^ 2 + Fintype.card d) + Module.finrank ℝ V
theorem finrank_span_symmetryDirs_skipless_eq_add … : (skipless span) = (residual span) + L * Fintype.card d ^ 2
```

**True as stated? By reading.** The set is the range of the linear map `((X, g), v) ↦ cobDirB + translate(At)Dir + v`
(so its span is itself), and the map is injective under the hypotheses, by the argument the thirty-second report
checked for the bounds (`E` of rank `d` gives `X` (or `X_0`), the embedding bias gives `g_0`; block by block the read and
read bias give those of `v`, `hrw` its write and write bias, and, skipless, the write of rank `d` gives `X_{ℓ+1}`, the
write bias `g_{ℓ+1}`). Its domain has dimension `d² + (L+1)d + dim V`, resp. `(L+1)(d² + d) + dim V`. The third is the
difference of the first two. All three true, for any architecture `A`, any `χ` and any stream (the directions are
written, not tested against a network). The directions are flat by `InsideBlocksB.mem_flatB` and the flatness of the
changes of basis and translations (`Symmetry/BiasesFlatKinks.lean`), as the docstring says; the statements here do not
say flatness.

**Each hypothesis is needed: exact examples, by a computation with exact rationals**
(`/home/claude/audit33a/count_hrw.py`, the directions written from the Lean definitions of `cobDirB`, `translateDir`,
`translateAtDir`; `d = d_in = d_out = 1`):

* **`hrw`, residual count.** `L = 1`, one block with two read columns and one write row and the row-wise map
  `f(M)_t = φ(M_{t,1}, M_{t,2})`, `φ(x, y) = x³/(x² + y²)`, `φ(0) = 0` (odd, positively homogeneous, not linear; `Arch`
  allows any `f`). At `E = 2`, `W_read = 0`, `W_write = 3`, `D = 0`, any biases with `b_read = 0`: the curve
  `b_read(τ) = τu`, `b_write(τ) = b_write − τ φ(u) W_write` keeps the block map (`φ(τu) = τφ(u)` for every real `τ`) and
  `E`, `D`, `b_E`, `b_D`, so its velocity `(u, −φ(u) W_write)` is an `InsideBlocksB` direction. `V` = the span of these
  for `u = (1,0), (0,1), (1,1)`: `dim V = 3`, and `V` contains the pure write-bias direction (`φ(1,0) + φ(0,1) −
  φ(1,1) = ½ ≠ 0`), so `hrw` fails; `hE`, `hV` hold. The span has dimension `5`, the statement says
  `d² + (L+1)d + dim V = 6`: false. The translation `g_1` at `h_1` is that pure write-bias direction. With `D ≠ 0`:
  `L = 2`, two such blocks, `D = 13`: span `9`, claimed `10` (the kernel is `g = (0, g_1, −g_1)` with the two write-bias
  directions of `V`). So the residual count needs `hrw` for blocks of this kind; the thirty-second report found no such
  example for the residual *bound*, where the functional dimension moves too; for the count, which is linear algebra
  only, the example is exact.
* **`hrw`, skipless count.** The example of the thirty-second report (check 3): `L = 2`, `f ≡ 0` (an MLP block with the
  activation `0`), one unit per block, `V` the six straight lines in `W_read^ℓ`, `b_read^ℓ`, `W_write^ℓ`: `dim V = 6`, span
  `11`, claimed `(L+1)(d² + d) + 6 = 12`: false (the change of basis at `h_1` and the translation at `h_1` agree modulo `V`).
* **`hE`.** Residual, `L = 0`, `E = 0`, `D = 0`, `b_E = 0`, `V = 0`: span `1`, claimed `d² + d = 2`.
* **`hw`.** Skipless, `L = 1`, `f ≡ 0`, `W_write = 0`, `D = 0`, `b_write = 0`, `V = 0`: span `3`, claimed `4`
  (the change of basis at `h_1` moves nothing).
* **`hV`** (by reading). Without it, `V` = the line of one direction `cobDirB p (fun _ => X)`, `X ≠ 0`, at a point with
  every `W_read^ℓ ≠ 0` and `E` of rank `d`: `hrw` holds (its premise fails, the read is `−X W_read ≠ 0`, if `X W_read ≠ 0`),
  the span is that of the changes of basis and translations, of dimension `d² + (L+1)d`, and the statement says one more.
  `hV` gives the injectivity its start (`v_E = v_D = v_{b_E} = v_{b_D} = 0`).

For the blocks of the paper `hrw` holds: for attention with biases it is proved from `hV` (rank of `W_{V,i}`, check 2),
for the rescalings from no read column `0` (thirty-second report, check 4).

**Is "the dimension of the space spanned by the directions at `(θ, b)`" a fair reading of "the symmetry group … has
dimension"?** The dimension of a Lie group acting on the parameters equals the dimension of the span of its directions
at a point `p` (the image of its Lie algebra) exactly when it acts locally freely at `p`; so the Lean statements say
"the infinitesimal action of these three families at `p` is injective, and the sum of their spaces of directions has
the stated dimension". This is what the paper's proof argues ("These `L + 1` translations move the biases in independent
directions … A skip ties only the linear part of `Aff(d_model)`, which gives the counts"), and what the paper uses (the
bounds of Theorem 4.2). It is not the group: the header says so ("the group itself is not stated as an object"), and
two points are left out: (a) the group generated by the three families could contain further directions (commutators)
than the sum of the three spaces; Lean counts the sum; (b) the lemma has no hypotheses, while the count needs `E` of
rank `d`, the writes of rank `d` (skipless) and the condition `hrw` on `s`. Verdict: **PART** (the count at a point, under
hypotheses the lemma does not write; the group not stated), **SAME** as the proof's counting step.

### Check 3. The reduction with biases (`OneBlock/AttentionBiases.lean`)

**The definitions, term by term (by reading).** `attnScoreBias p i = (b_E W_{Q,i} + b_{Q,i}) W_{K,i}^⊤ E^⊤ / √d_h`
(a row indexed by `dIn`): the paper's `β_i`. `attnConst S p = b_E S_0 D + ∑_i (b_E W_{V,i} + b_{V,i}) W_{O,i} D + b_O D +
b_D`: the paper's `γ` for `S_0 = 0`, and `γ + b_E D` ("plus `b_E D` in the residual network") for `S_0 = 1`.
`dAttnScoreBias` is the product rule applied to `β_i` in all of `b_E`, `W_{Q,i}`, `b_{Q,i}`, `W_{K,i}`, `E`, and
`dAttnConst` to `γ` in `b_E`, `D`, `W_{V,i}`, `b_{V,i}`, `W_{O,i}`, `b_O`, `b_D` (`S` fixed). No term is missing or extra;
`b_{K,i}` enters neither (it drops out), `b_{V,i}` only `γ`. `hasDerivAt_attnScoreBias` and `hasDerivAt_attnConst` say
these are the derivatives along `p + τη`. **By a computation** (`/home/claude/audit33a/reduction.py`, three sizes, masks
none, causal and one irregular mask, `S_0 = 0, 1`): both derivatives agree with the complex step to `1.1e-14`.

**`evalB_attention_oneBlock_row`**: at a token `t` that sees some token, row `t` of the output is
`x_t E S_0 D + ∑_i ∑_s a_ts^{(i)} x_s C_i + γ`, the weights being those of the scores `x B_i x^⊤ + (β_i x_s^⊤)_{t,s}`. The
scores of the network are `q_t k_s^⊤/√d_h` with `q_t = (x_t E + b_E) W_Q + b_Q`, `k_s = (x_s E + b_E) W_K + b_K`; expanding,
`x_t B_i x_s^⊤ + β_i x_s^⊤` plus terms that do not depend on `s`, which the softmax ignores. So this is the paper's
"`u B_i v^⊤` becomes `(u B_i + β_i) v^⊤` … and the constant `γ` is added". The hypothesis `∃ s, sees t s` is what makes
the value biases enter only through `γ`. Numerically (same script) the formula agrees with the network to `2.2e-14`.

**`evalB_attention_two_tokens`**: with `t₂` seeing itself and `t₁ ≠ t₂`, `k` the number of tokens other than `t₂` that
`t₂` sees, and the input with row `u` at `t₂` and `u − v` at every other token, the output at `t₂` is
`u (E S_0 D + ∑C_i) − ½ v ∑C_i + ½ ∑_i tanh(½((u B_i + β_i)v^⊤ − log k)) v C_i + γ`: equation (16) with biases (`K = M + S`,
`M = E S_0 D`). The paper's inputs ("with a causal mask, any sequence, whose second token sees only the first two;
without a mask, sequences whose tokens other than the second all equal the first") are covered: Lean fixes every other
token to `u − v`, which is one such input for both masks, and only row `t₂` is used. Numerically: `2.8e-14`.

**`flatB_attention_oneBlock_keeps`**: under `hs2`, `hs1` and one `v` with `B_i v^⊤ ≠ 0`, pairwise non-collinear, and
`v C_i ≠ 0`, a flat direction has `D(E S_0 D) η = 0`, `D B_i η = 0`, `D C_i η = 0`, `D β_i η = 0`, `D γ η = 0`. The
paper's Step 2 concludes the same (`D_θ M η = 0` in the residual network, and `D_θ S η = 0`, which follows from the
`D C_i η = 0`). The paper asks the conditions "for all `v` in an open set"; Lean asks one `v`, which suffices since the
conditions are open (LEAN STRONGER in form, same content). Lemma B.3 for tanh needs no twins and nonzero output
weights: non-collinear input weights `½ B_i v^⊤` exclude twins whatever the biases `½(β_i v^⊤ − log k)` (tanh is odd, so
twins are `(w_i, b_i) = ±(w_j, b_j)`), and `v C_i ≠ 0` are the output weights. True, by reading; it is used, with Step 1,
for the values that check 5 confirms numerically.

Verdict of check 3: **SAME** (the four definitions and the three statements are the paper's formulas; the hypotheses
are the paper's, `∃ s, sees t s` made explicit).

### Check 4. Step 1 with biases (`OneBlock/AttentionBiasesStepOne.lean`)

```lean
theorem exists_dirs_of_keeps_attention_biases (p) (hp : OneBlockGenericAttention p.1) (η)
    (hB : ∀ i, dAttnScore p.1 η.1 i = 0) (hC : ∀ i, dAttnValue p.1 η.1 i = 0)
    (hβ : ∀ i, dAttnScoreBias p η i = 0) (hγ : dAttnConst 0 p η = 0) :
    ∃ X g Γ Γ' κ ν, η = cobDirB p X + (0, translateAtDir p.1 g) + headDirB p (Γ, Γ', κ, ν)
theorem exists_dirs_of_keeps_attention_biases_residual (p) (hp) (η)
    (hM : η.1.E * p.1.D + p.1.E * η.1.D = 0) (hB …) (hC …) (hβ …) (hγ : dAttnConst 1 p η = 0) :
    ∃ X g Γ Γ' κ ν, η = cobDirB p (fun _ => X) + (0, translateDir p.1 g) + headDirB p (Γ, Γ', κ, ν)
```

**By reading, entry by entry.** On the weights: `η_E = E X_0`, `η_D = −X_1 D`, `η_{Q,i} = −X_0 W_{Q,i} + W_{Q,i} Γ_i`,
`η_{K,i} = −X_0 W_{K,i} − W_{K,i} Γ_i^⊤`, `η_{V,i} = −X_0 W_{V,i} + W_{V,i} Γ'_i`, `η_{O,i} = W_{O,i} X_1 − Γ'_i W_{O,i}`:
the paper's (its `Y` is `X_1`), from the twin without biases. On the biases, with `g_0 = η_{b_E} − b_E X_0`:
`η_{b_E} = b_E X_0 + g_0`; `η_{b_Q,i} = b_{Q,i} Γ_i − g_0 W_{Q,i}` (the paper's "`η_{b_Q,i} = b_{Q,i} Γ_i − g W_{Q,i}` with
`g = η_{b_E} − b_E X`", from `D β_i η = 0` and `W_{K,i}^⊤ E^⊤` of full row rank, i.e. `rank_K`, `rank_E`); the key biases
`−g_0 W_{K,i} − b_{K,i} Γ_i^⊤ + κ_i` and the value biases `−g_0 W_{V,i} + b_{V,i} Γ'_i + ν_i` (free: `κ`, `ν` are defined
from them); the write bias `b_O X_1 + g_1 − ∑_i ν_i W_{O,i}` (free: `g_1` is defined from it); the readout bias
`−g_1 D` skipless, `−(g_0 + g_1) D` residual, from `D γ η = 0` ("`D_θ γ η = 0` determines `η_{b_D}`"). The free
parameters are `g_0`, `g_1`, `κ`, `ν`: `2d + 2Hd_h`, the paper's "`g`, `η_{b_O}` and the entries of `η` at the key and
value biases free, `2 d_model + 2 H d_h` dimensions". The decomposition names them as the paper does: "the translations
at `h_0` and `h_1`" (`translateAtDir` skipless, `translateDir` with the skip, where the translation at `h_0` carries to
`h_1`, Lemma A.8), "the shifts of the key biases" (`κ`), "the value biases moved into the output bias" (`ν`). In the
residual case `hM` gives `X_0 = X_1` (`E`, `D` of rank `d`), the paper's "`X = Y`". The signs agree with the curves of
check 2 and with `cobDirB` (`b_E ↦ b_E G_0`, `b_O ↦ b_O G_1`, read bias unchanged by a change of basis).

**The hypotheses.** No mask, no input, no bias condition; on the weights `OneBlockGenericAttention p.1`: the paper's Step 1
conditions ("`E` and `D` have rank `d_model`; every `W_{Q,i}`, `W_{K,i}`, `W_{V,i}` and `W_{O,i}^⊤` has rank `d_h` …; the
queries … and the output projection `W_O` … have rank `d_model`"), without the rank of the keys of all heads (which the
paper lists but its argument does not use), and with `exists_v`, a condition of Step 2 that Step 1 does not use. So one
hypothesis more than Step 1 needs (`exists_v`, harmless: it holds at generic weights and is in the theorem's generic
conditions) and one fewer than the paper lists. The theorem is then true at every bias.

Verdict of check 4: **SAME** as the paper's Step 1 with biases (LEAN STRONGER in that it holds at every bias and needs no
rank of the keys of all heads; `exists_v` is carried along, unused).

### Check 7. Drift checks (by reading and by compiling a copy)

* **Generic is "almost every".** All eight `ae_` statements (two in `UpperBoundAttentionBiases.lean`, six in
  `AttentionBiasesDim.lean`) are `∀ᵐ p ∂μ` for every `μ` with `[μ.IsAddHaarMeasure]` on `ParamsB`, the pairs of weights and
  biases; none is "there is a point" or "on an open set". They apply to a concrete Haar measure: compiled in a copy
  (`/home/claude/audit33a/Ax33a.lean`), `ae_funDimB_attention_oneBlock_residual_eq_add_causal` at
  `Measure.addHaar` on `ParamsB (Arch.attention (T := Fin 2) (d := Fin 2) (fun t s => s ≤ t) id (fun _ => Fin 2)
  (fun _ => Fin 1)) (Fin 2) (Fin 2)`, with every size hypothesis closed by `simp`: no error.
* **The functional dimension** is `funDimB`, the `sSup` over all `n` and all batches `X : Fin n → Matrix T dIn ℝ` of the
  rank of the Jacobian in `(θ, b)` (`Dimension/FunctionalBiases.lean`): the maximum over all finite batches, on all of
  `ℝ^{T × d_in}`.
* **Hypotheses added by a route inside a proof.** `hsee` is the only hypothesis beyond the theorem's own; it is needed
  (check 1) and true of both masks of the paper, and the six named statements discharge it. `OneBlockGenericAttention`
  carries `exists_v` into Step 1, where it is not needed (check 4); the pointwise statements are about one parameter and
  the `ae_` ones discharge it. The pointwise conditions are on the weights only, so no condition on the biases enters.
  Lemma A.8 and Theorem B.1 are appendix statements; nothing in the main text is restated here.
* No file of the six has `sorry`.

Verdict of check 7: no drift.

### Check 8. The index rows, the registrations and the axioms

**Registrations** (by reading `checks/Axioms.lean`): all 33 public theorems of the six files are registered, each once
(8 + 2 + 5 + 2 + 13 + 3); the definitions (`headDirQKB`, `headDirVOB`, `keyShiftDir`, `valueShiftDir`, `headDirB`,
`attnBQ`, `attnBK`, `attnBV`, `attnScoreBias`, `attnConst`, `dAttnScoreBias`, `dAttnConst`) are not, as for other
definitions. **Axioms** (compiled in a copy after the full build had ended, `pgrep -f "lake build"` empty, against the
build of `0e1bc98`, whose `.olean` files of the six modules are newer than their sources): all 33 depend on
`[propext, Classical.choice, Quot.sound]` only.

**The rows** (`STATEMENTS.md` lines 1033 to 1037 and 1049, by reading against checks 1 to 6):

* Line 1033 (`Symmetry/AttentionHeadsBiases.lean`): true of the statements. "The condition on the mask is needed
  (numeric check, part (d))": true, and true of the bounds too (check 2).
* Line 1034 (`Dimension/UpperBoundAttentionBiases.lean`): true.
* Line 1035 (`OneBlock/AttentionBiases.lean`): true.
* Line 1036 (`OneBlock/AttentionBiasesStepOne.lean`): true; it could add that the conditions are on the weights only, so
  the statement holds at every bias, and that `OneBlockGenericAttention` holds one condition (`exists_v`) that Step 1
  does not use.
* Line 1037 (`OneBlock/AttentionBiasesDim.lean`): "The two values at one parameter are with a proving agent; the other
  eleven statements are proved from them by the coordinator" is out of date: at `0e1bc98` the two values are proved (no
  `sorry`, standard axioms) and the row says "proved". The rest is true. The docstring's and the check's "higher by
  `H d_h = 2`" (part (d)) is right for its example; the general excess is `min(H d_h, d)` (check 1).
* Line 1049 (`Symmetry/BiasesSymmetryCount.lean`): the statements are described rightly, but "The dimension of a group is
  that of the space of its directions at the identity" is not what is stated: Lean states the dimension of the span of
  the directions at the point `(θ, b)`, which is the dimension of the group only if it acts locally freely there (which
  is what the hypotheses ensure). It does not say that the condition on `V` is needed for the count (exact examples,
  check 6, for both counts), nor that `E` (and, skipless, the writes) of rank `d` are needed.
* Lines 363 to 365 and 373 list the six files as "Not yet compared": to be updated with this report.

Verdict of check 8: registrations complete; axioms standard; one stale sentence (line 1037), one imprecise sentence and
one missing need (line 1049).

## Part 2: the statements, file by file

| Name | Paper sentence | Verdict | Note |
|---|---|---|---|
| `headDirQKB` (def) | Step 1: "`I + τΓ_i` between the queries and keys", with biases | SAME | `b_Q Γ_i`, `−b_K Γ_i^⊤` on the biases; signs checked |
| `headDirVOB` (def) | "`I + τΓ'_i` between the values and outputs" | SAME | `b_V Γ'_i`; `b_O` untouched |
| `keyShiftDir` (def) | "The key biases drop out" | SAME | |
| `valueShiftDir` (def) | "the value biases moved into the output bias" | SAME | `η_{b_O} = −∑ ν_i W_{O,i}` |
| `headDirB` (def) | the sum of the four | SAME | |
| `insideBlocksB_headDirQKB`, `insideBlocksB_headDirVOB`, `insideBlocksB_keyShiftDir` | symmetries inside the block | SAME | every mask, every `χ` |
| `insideBlocksB_valueShiftDir` | "since the weights of a token sum to one" | SAME | `hsee` is that condition |
| `isLinearMap_headDirB` | (linearity, implicit) | SAME | |
| `headDirB_injective` | Step 1: "`W_{Q,i} Γ_i = 0` and `W_{V,i} Γ'_i = 0` force `Γ_i = Γ'_i = 0`" | SAME | `hQ`, `hV` each needed (exact examples) |
| `funDimB_add_le_residual_attention`, `funDimB_add_le_skipless_attention` | Lemma A.8 with `s = 2Hd_h² + 2Hd_h` per block | SAME (as bounds) | `hsee` needed (blind-token example: 38 > 36) |
| `ae_funDimB_add_le_residual_attention`, `ae_funDimB_add_le_skipless_attention` | the same at generic parameters | SAME (as bounds) | every Haar measure on the pairs; Theorem B.1's size conditions |
| `attnBQ`, `attnBK`, `attnBV` (defs) | `b_{Q,i}`, `b_{K,i}`, `b_{V,i}` | SAME | |
| `attnScoreBias`, `attnConst` (defs) | `β_i`, `γ` (+ `b_E D` residual) | SAME | `b_E S_0 D` |
| `dAttnScoreBias`, `dAttnConst` (defs) | `D_θ β_i η`, `D_θ γ η` | SAME | checked numerically to `1e-14` |
| `hasDerivAt_attnScoreBias`, `hasDerivAt_attnConst` | (the derivatives) | SAME | |
| `evalB_attention_oneBlock_row` | the reduction with biases | SAME | at a token that sees some token |
| `evalB_attention_two_tokens` | (16) with biases | SAME | |
| `flatB_attention_oneBlock_keeps` | Step 2 with biases | SAME (LEAN STRONGER in form) | one `v` instead of an open set |
| `exists_dirs_of_keeps_attention_biases`, `_residual` | Step 1 with biases | SAME (LEAN STRONGER) | every bias; no rank of the keys of all heads; `exists_v` carried |
| `flatB_le_range_attention_skipless`, `_residual` | Steps 1 and 2: every flat direction is a symmetry direction | SAME | |
| `funDimB_attention_oneBlock`, `_residual` | Theorem B.1 (i) with biases, attention, at one parameter | LEAN STRONGER | at every bias, under conditions on the weights |
| `ae_funDimB_attention_oneBlock`, `_residual`, `_residual_eq_add` | Theorem B.1 (i) with biases, attention; the gain `d²` | SAME | + `hsee` and a token `t₂` |
| `ae_…_noMask` (3) | the same without a mask | SAME | `[Nontrivial T]` |
| `ae_…_causal` (3) | the same with the causal mask | SAME | `Fin n`, `2 ≤ n`, `s ≤ t` |
| `finrank_span_symmetryDirs_residual`, `_skipless`, `_skipless_eq_add` | Lemma A.8: "the symmetry group … has dimension …", "the skips remove `L d²`" | PART | the dimension of the span of the directions at `p`, under `hE` (`hw`) and `hrw`, each needed (exact examples); the group not stated |

Nothing is FALSE, vacuous or drifted.

## What the authors of the papers should know

1. Nothing in these six files is false, vacuous or drifted. Theorem B.1 (i) with biases for one attention block holds as
   the paper states it, at almost every pair of weights and biases (40 runs here with exact derivatives, causal and without
   mask, with and without the skip, including `H d_h > d` and `d_h = d`), and at one parameter it holds at every bias once
   the weights are generic.
2. **Every token must see at least one token.** "The value biases enter only through `γ`, since the weights of a token
   sum to one" needs it; both masks of the paper satisfy it (a token sees itself). With a token that sees no token the
   values are false: the rank is higher by `min(H d_h, d_model)` (computed: `+2` for `H d_h = 2, 3` with `d = 2`, `+3` for
   `H d_h = 4` with `d = 3`, `+1` for `H d_h = 1`).
3. **The `s` of an attention block with biases** in Lemma A.8 is `2 H d_h² + 2 H d_h` (the changes of basis inside the
   heads, the shifts of the key biases, the value biases moved into the output bias). The paper never writes this; its
   Theorem B.1 uses `s = 2 H d_h²` and names the `2 H d_h` apart. The two agree; one sentence would make Lemma A.8 and
   Theorem B.1 read together.
4. **Lemma A.8 states the dimension of a group without hypotheses.** What its proof shows, and what is formalized, is
   the dimension of the span of the directions of the three families at a point, which needs `E` of rank `d_model`,
   without skips the writes of rank `d_model`, and a condition on the symmetries inside the blocks (a direction of them
   that moves neither the read nor the read bias of a block moves neither its write nor its write bias). Without the last
   the count fails for some blocks (exact examples here, with and without skips); it holds for every block of the paper.
5. **The width condition** `H d_h ≥ d_model` is needed for the skipless value when `d_out > d_model` (deficit
   `(d − H d_h)(d_out − d)` in four computed cases); for the residual value it was not needed in the eight narrow runs
   computed. `d_model ≥ 2` was not needed in the cases computed with `d_model = 1` (one or two heads): with biases the
   two tanh units of (16) are not twins even when the `B_i v^⊤` are collinear. Both are the paper's hypotheses and are
   sufficient; this is only a remark.

## Corrections for `STATEMENTS.md`

* Line 1037: replace "The two values at one parameter are with a proving agent; the other eleven statements are proved
  from them by the coordinator" by "The two values at one parameter are proved; the other eleven statements are proved
  from them by the coordinator". Optionally add: "without the condition on the mask the rank is higher by
  `min(H d_h, d)` (thirty-third reader, part A, check 1)".
* Line 1049: replace "The dimension of a group is that of the space of its directions at the identity" by "This is the
  dimension of the group when it acts locally freely at `(θ, b)`, which the rank conditions and the condition on `V`
  ensure"; add "The condition on `V` is needed for both counts, and `E` (and, without skips, the writes) of rank `d`
  is needed (exact examples: thirty-third reader, part A, check 6)".
* Line 1036 (optional): "The conditions are on the weights alone, so the statement holds at every bias; `exists_v`, a
  condition of Step 2, is carried and not used."
* Lines 363 to 365 and 373: move the six files of this audit from "Not yet compared" to a line for this report:
  "A thirty-third reader (part A, 25 November) compared `Symmetry/AttentionHeadsBiases.lean`,
  `Dimension/UpperBoundAttentionBiases.lean`, `OneBlock/AttentionBiases.lean`, `OneBlock/AttentionBiasesStepOne.lean`,
  `OneBlock/AttentionBiasesDim.lean` and `Symmetry/BiasesSymmetryCount.lean` (33 theorems and the definitions): nothing
  false, vacuous or drifted; the count of Lemma A.8 as a dimension needs its condition on `V` (exact examples)".

## What could not be checked

* Two blocks of attention with biases: I did not recompute the equality at depth 2 that the docstring of
  `Dimension/UpperBoundAttentionBiases.lean` reports for 24 networks; the two bounds at depth 2 are checked only by reading.
* The values without `d_in ≥ d`, `d_out ≥ d` or `d_h ≤ d` were not computed; for the residual network without the width
  condition and for `d = 1` only the cases listed were computed.
* Point (a) of check 6, whether the group generated by the three families has directions beyond the sum of their three
  spaces, was not examined.
* Proofs were not audited, only statements; compiled was only the copy with `#print axioms` and the instance at a
  concrete Haar measure.

Commit read at the start and at the end: `0e1bc98` of `/home/claude/lp` (branch `lean-plus`); the six files did not change.
