STATUS: complete

# Thirty-fourth audit, part A: D Lemma D.10 (derivatives of all orders, meromorphic at infinity, the holomorphic extension) and the extension of a real-analytic map

Read: `/home/claude/lp/lean` (branch `lean-plus`), commit `c4a245c` at the start. Paper: `<scratchpad>/dim.txt`, the definition of "meromorphic at infinity" (lines 1975 to 1977), Lemma D.10 and its proof (lines 2019 to 2046), the proof of Lemma D.12 (lines 2201 to 2360).

Files read: `SkipsLean/Depth/ScaledSuffixOrders.lean` (9 theorems), `SkipsLean/Generic/HolomorphicExtension.lean` (2), `SkipsLean/Depth/ScaledSuffixHolomorphic.lean` (2), and for the definitions `SkipsLean/Depth/ScaledSuffix.lean` (`suffixPost`, `scaledSuffix`). No `sorry` in the three files (searched).

## Part 1: checks

### 1. The derivatives of all orders (by reading)

Lean:

```lean
theorem iteratedFDeriv_suffix_pow_smul (hχ : A.χ = rmsNorm ε) (θ : Params A dIn dOut)
    (k : Fin (L + 1)) {t : ℝ} (ht : 0 < t) (m i : ℕ) (H : Matrix T d ℝ)
    (v : Fin i → Matrix T d ℝ) :
    (t ^ m) ^ i • iteratedFDeriv ℝ i (fun h' : Matrix T d ℝ => suffix A 0 θ k h') (t ^ m • H) v
      = iteratedFDeriv ℝ i
          (fun h' : Matrix T d ℝ => scaledSuffix A ε m θ k (1 / t, h')) H v
```

and `iteratedFDeriv_fderiv_params_suffix_pow_smul`, the same with `h' ↦ fderiv ℝ (fun θ' => suffix A 0 θ' k h') θ η` on the left and `h' ↦ fderiv ℝ (fun θ' => scaledSuffix A ε m θ' k (1 / t, h')) θ η` on the right.

- Which maps. Left: the map `𝓑_{>k}` itself (`suffix A 0 θ k`, the network without skips from `h_k` on), differentiated `i` times at the point `t^m H`, applied to `v_1, …, v_i`, times `(t^m)^i`. Right: the map `h ↦ 𝓑^♯(N_{ε t^{−2m}}(h))`, that is `h ↦ 𝓑_{>k}(t^m h)` (by `suffix_pow_smul_eq_scaledSuffix`, which holds for every `h` and every `t > 0`), differentiated `i` times at `H`. The factor `(t^m)^i` is on the left side, with the derivative of `𝓑_{>k}`: this is the chain rule `𝐃^i [h ↦ 𝓑(c h)](H)(v) = c^i 𝐃^i 𝓑(c H)(v)` with `c = t^m`. The paper's sentence "A derivative of order `i` in `v = t u` at `v = 0` is `t^{−i}` times the derivative of order `i` in `u` at `u = 0`" is this identity at `m = 1`, with `H = h°` (the paper's derivative in `u` at `u = 0` of `𝓑(t(h° + u))` is the derivative in `h` at `h°` of `𝓑(t h)`).
- Every `t > 0`, every `i`, every `H`. The scaling identity `N_ε(c h) = N_{ε c^{−2}}(h)` for `c > 0` holds for every real `ε` and every `h` (also a zero row, also `ε ≤ 0`: `√(c² x) = c √x` for `c > 0` and every real `x` with Lean's `Real.sqrt`), so the two functions of `h'` under the derivative are equal as functions; the identity of their derivatives of order `i` then needs only the composition with the linear equivalence `h ↦ t^m h`, which in Mathlib (`ContinuousLinearEquiv.iteratedFDerivWithin_comp_right`) asks no smoothness: for a map that is not differentiable both sides are Lean's junk value of the same function, and the identity still holds. So no analyticity and no `ε > 0` are needed, and the statement asks neither; it is true. At `i = 0`, `(t^m)^0 = 1` and `iteratedFDeriv ℝ 0 g x v = g x`: the identity is `𝓑_{>k}(t^m H) = 𝓑^♯(N_{ε t^{−2m}}(H))`, true. For the second statement the same holds: `fderiv_params_suffix_pow_smul` equates the two functions of `θ'` for each `h'` (no hypothesis but `hχ` and `t > 0`), so the maps of `h'` are equal as functions, and the derivative in the weights is taken of the same function on both sides.
- Verdict: SAME (Lean slightly stronger: any `m`, any hidden state of all tokens, any `ε`). True.

### 2. Real-analytic in `1/t` (by reading)

Lean (the first; the other two have the same hypotheses):

```lean
theorem analyticAt_iteratedFDeriv_scaledSuffix (hε : 0 < ε) (hχ : A.χ = rmsNorm ε)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (m i : ℕ) (θ : Params A dIn dOut)
    (k : Fin (L + 1)) (s : ℝ) (H : Matrix T d ℝ) (hH : ∀ τ, H τ ≠ 0)
    (v : Fin i → Matrix T d ℝ) :
    AnalyticAt ℝ (fun s' : ℝ => iteratedFDeriv ℝ i
      (fun h' : Matrix T d ℝ => scaledSuffix A ε m θ k (s', h')) H v) s
```

`analyticAt_fderiv_params_scaledSuffix`: `(s, h) ↦ fderiv ℝ (fun θ' => scaledSuffix A ε m θ' k (s, h)) θ η` is analytic at `(s, H)`; `analyticAt_iteratedFDeriv_fderiv_params_scaledSuffix`: its derivative of order `i` in `h` at `H`, applied to `v`, is analytic in `s` at `s`.

- What they say with check 1. For `t > 0`, check 1 gives `t^{m i} 𝐃^i 𝓑_{>k}(t^m H)(v) = Θ₀(1/t)` with `Θ₀(s) = 𝐃^i_h [scaledSuffix(s, ·)](H)(v)`, and this statement gives `Θ₀` real-analytic at `s = 0` (in fact at every real `s`). Together they are the paper's "are real-analytic functions of `1/t` near `1/t = 0`", for every `t > 0` and not only for large `t`. The same for the second map. SAME as a pair; each alone is a PART.
- `ε > 0`. Needed. At `s = 0` the normalization of `h_k` is `N_0`, analytic at `H` because no row of `H` vanishes, but the later normalizations (`k < L`) are `N_ε` at hidden states that may have zero rows: for `ε = 0` they are not analytic there, and for `ε < 0` `N_ε` is not analytic where `‖v‖²/d + ε ≤ 0`. For `k = L` only `ε ≥ 0` would be needed; the paper's case (+) has `ε > 0`, so this is the paper's hypothesis.
- `hχ : A.χ = rmsNorm ε`: pre-RMSNorm before every block and before `D` (the architecture has one `χ`), the paper's case (+) (`dim.txt` line 201: "In the case (+), pre-RMSNorm with `ε > 0`, `χ = N_ε`").
- `hf`: every block map real-analytic on all of its inputs. The paper's blocks (tanh, GELU, SwiGLU, GeGLU; `dim.txt` line 1696: "In the cases (n) and (+), every `𝓑_{>k}` is real-analytic on all rows `h`") have it; the proof's "`𝓑^♯` … which is real-analytic on all rows" is what it gives. Lean is more general (any real-analytic blocks, attention included, several tokens).
- `hH : ∀ τ, H τ ≠ 0`, "no zero row". The paper takes inputs of one token ("we take inputs of one token, and a hidden state is a row `h`", line 440), and for one token (`T` with one element) `hH` is `h° ≠ 0`. With several tokens RMSNorm normalizes each row separately (`rmsNorm ε h = of fun τ => rmsRow ε (h τ)`), so the argument "the right side is real-analytic … because `h° ≠ 0`" needs each row of `H` nonzero: `hH` is the right generalization. It is needed for "real-analytic in `1/t`": at a zero row the map `h_τ ↦ N_{ε s^{2m}}(h_τ)` has the derivative `(ε s^{2m})^{−1/2}` at `h_τ = 0`, which is not analytic at `s = 0`; computed in check 5 (b) for one token and `H = 0`: `t 𝐃𝓑_{>k}(t·0)(v)` grows like `t`. (Such a map is still meromorphic at infinity with `l ≥ 1`, but it is not a real-analytic function of `1/t`.)
- The direction `η`. Lean takes `η : Params A dIn dOut`, a direction of all the weights. `suffix A 0 θ' k` depends only on `θ'.read ℓ`, `θ'.write ℓ` for the blocks `ℓ ≥ k` (Lean's blocks are numbered from `0`, so these are the paper's blocks `k+1, …, L`) and on `θ'.D` (by the definition of `suffix` in `Depth/Suffix.lean` by reverse induction from `χ(h) D`), so the derivative along `η` is that along its part in these weights: Lean's "any direction" contains the paper's and is equivalent to it. LEAN STRONGER in form, SAME in content.
- `k : Fin (L + 1)` is the paper's `k = 0, …, L`, with `suffixPost A θ (Fin.last L) n = n * θ.D`, the paper's `𝓑^♯(n) = n D` for `k = L`.
- Verdict: SAME (with check 1); Lean more general (several tokens, any real-analytic blocks, any `m`); true.

### 3. Meromorphic at infinity (by reading)

Lean (`Activations/MillsAtInfinity.lean`, line 127):

```lean
def MeromorphicAtInfinity (Θ : ℝ → F) : Prop :=
  ∃ (l : ℕ) (Θ₀ : ℝ → F), AnalyticAt ℝ Θ₀ 0 ∧ ∀ᶠ t in atTop, Θ t = t ^ l • Θ₀ (1 / t)
```

and, for `m = 1`,

```lean
theorem meromorphicAtInfinity_iteratedFDeriv_suffix (hε : 0 < ε) (hχ : A.χ = rmsNorm ε)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (i : ℕ) (θ : Params A dIn dOut)
    (k : Fin (L + 1)) (H : Matrix T d ℝ) (hH : ∀ τ, H τ ≠ 0) (v : Fin i → Matrix T d ℝ) :
    MeromorphicAtInfinity (fun t : ℝ => t ^ i
      • iteratedFDeriv ℝ i (fun h' : Matrix T d ℝ => suffix A 0 θ k h') (t • H) v)

theorem meromorphicAtInfinity_iteratedFDeriv_fderiv_params_suffix ... :
    MeromorphicAtInfinity (fun t : ℝ => t ^ i • iteratedFDeriv ℝ i
      (fun h' : Matrix T d ℝ => fderiv ℝ (fun θ' : Params A dIn dOut => suffix A 0 θ' k h') θ η)
      (t • H) v)
```

- The definition against the paper's ("`Θ(t) = t^l Θ₀(1/t)` for an integer `l` and a map `Θ₀` that is holomorphic near `0`"). A natural `l` loses nothing (`t^{−l'} Θ₀(1/t) = Θ₀'(1/t)` with `Θ₀'(s) = s^{l'} Θ₀(s)`); for maps with real values (here: real matrices) a real-analytic `Θ₀` at `0` is the restriction of one holomorphic near `0`, and conversely the real part of a holomorphic `Θ₀` that is real on `(0, 1/t₀)` is real-analytic and serves; "on an interval `(t₀, ∞)`" is "for all large `t`". Equivalent, as the sixth audit found.
- The two maps for `m = 1` are exactly the paper's: `t ↦ t^i 𝐃^i 𝓑_{>k}(t h°)(v_1, …, v_i)` is `fun t => t ^ i • iteratedFDeriv ℝ i (suffix A 0 θ k) (t • H) v`, and `t ↦ t^i 𝐃^i (𝐃_θ 𝓑_{>k}(·) η)(t h°)(v_1, …, v_i)` is the second (the derivative in the weights at fixed `h'`, then `i` derivatives in `h'` at `t H`).
- The statements say "meromorphic at infinity" (some `l`), which is the paper's "so they are meromorphic at infinity". The stronger "real-analytic in `1/t`" (`l = 0`) is checks 1 and 2 together; the proofs take `l = 0`, `Θ₀(s) = 𝐃^i_h scaledSuffix(s, ·)(H)(v)`.
- The forms with `t^m`. The proof of Lemma D.12 (`dim.txt` line 2264 to 2266, fact (a)): the coefficients `L_α`, `L'_{α,i}` are "built from derivatives of `𝓑` and of `𝐃_θ 𝓑(·) η'` at `t^m h°` and from polynomials in `t`, so this is Lemma D.10 with `t^m` in the place of `t`". The derivative of order `|α|` in `δ` of `𝓑(t^m(h° + u))` with `u = −(1/t) δ ⊙ ι(ξ) V` is `t^{(m−1)|α|} 𝐃^{|α|} 𝓑(t^m h°)(ι V, …)`, that is `t^{−|α|}` times the map `t ↦ (t^m)^i 𝐃^i 𝓑(t^m h°)(…)` of `meromorphicAtInfinity_iteratedFDeriv_suffix_pow`, so the `_pow` statements give what fact (a) asks of Lemma D.10 (the products with polynomials and with `t^{−|α|}` are further steps of fact (a), not of Lemma D.10). They also follow from the `m = 1` forms by `Θ(t^m) = Θ₀((1/t)^m)`; Lean states them directly.
- Verdict: SAME (each meromorphic statement is the paper's "so they are meromorphic at infinity"; the `_pow` forms are the lemma "with `t^m` in the place of `t`"). True.

### 4. The extension of a real-analytic map (by reading, and a computation for `1/(1 + x²)`)

Lean (`Generic/HolomorphicExtension.lean`):

```lean
theorem exists_analyticOnNhd_complex_extension {ι κ : Type*} [Fintype ι] [Fintype κ]
    {f : (ι → ℝ) → (κ → ℝ)} {x : ι → ℝ} (hf : AnalyticAt ℝ f x) :
    ∃ r : ℝ, 0 < r ∧ ∃ g : (ι → ℂ) → (κ → ℂ),
      AnalyticOnNhd ℂ g (Metric.ball (fun i => (x i : ℂ)) r)
      ∧ ∀ y ∈ Metric.ball x r, g (fun i => (y i : ℂ)) = fun j => (f y j : ℂ)

theorem exists_holomorphic_extension_real_param {T d T' d' : Type*} [Fintype T] [Fintype d]
    [Fintype T'] [Fintype d'] {F : ℝ × Matrix T d ℝ → Matrix T' d' ℝ} {H : Matrix T d ℝ}
    (hF : AnalyticAt ℝ F (0, H)) :
    ∃ ϱ : ℝ, 0 < ϱ ∧ ∃ s₀ : ℝ, 0 < s₀ ∧ ∃ C : ℝ, ∀ s : ℝ, |s| ≤ s₀ →
      ∃ G : Matrix T d ℂ → Matrix T' d' ℂ,
        AnalyticOnNhd ℂ G {u | ∀ τ j, ‖u τ j‖ ≤ ϱ}
        ∧ (∀ u : Matrix T d ℝ, (∀ τ j, |u τ j| ≤ ϱ) →
            G (u.map fun a : ℝ => (a : ℂ)) = (F (s, H + u)).map fun a : ℝ => (a : ℂ))
        ∧ ∀ u : Matrix T d ℂ, (∀ τ j, ‖u τ j‖ ≤ ϱ) → ‖G u‖ ≤ C
```

- The first statement is the classical fact. The norm on `ι → ℂ` and `ι → ℝ` is Mathlib's sup norm of a product, so `Metric.ball` is the open polydisc of radius `r` around `x`, and the agreement is asked at the real points of the real ball of the same radius around `x`. Nothing is asked of `f` away from `x` but what the agreement clause says, and the agreement there follows from analyticity at `x` because the power series of `f` at `x` converges to `f` on a real ball (Mathlib's `HasFPowerSeriesOnBall`, inside the radius `r₀` of the `AnalyticAt` witness); the proof takes `r` below that radius. True; SAME as the classical fact.
- Not trivial. `g` must be holomorphic on the open polydisc, which is connected, and agree with `f` on its real points, an open subset of `ℝ^ι`; by the identity theorem (a holomorphic map that vanishes on a real open set vanishes on the connected domain) `g` is unique on the polydisc. A `g` that ignores the real points does not satisfy the second clause.
- The explicit function (computation, `/home/claude/audit34a/d10_checks.py`, 40 digits). `f(x) = 1/(1 + x²)` is real-analytic on all of `ℝ`, but the extension `1/(1 + z²)` has poles at `±i`: no `g` exists for `r > 1` (it would agree with `1/(1 + z²)` on the disc minus `±i` and have a pole), and every `r ≤ 1` works. The complexified series `∑ (−1)^n z^{2n}` agrees with `1/(1 + z²)` at `z = 0.45i, 0.3 + 0.3i, 0.9i` (error below `10⁻¹⁷` with 200 terms) and diverges at `z = 1.01i` (partial sums `135`, `2.7·10³`, `4·10⁸` for `N = 50, 200, 800`). The Lean proof takes `r = r₁/(card ι + 1)` with `r₁` below the radius of the real series, here `r < 1/2`: smaller than the best radius, which the statement does not ask for. Consistent with the statement.
- The second statement against the paper's step "It extends to a holomorphic and bounded function on a complex neighborhood of `(0, 0)`, which gives `ϱ` and `t_0`". Uniform in `s`: `ϱ`, `s₀` and the bound `C` come before `s`; one `G` for each real `s` with `|s| ≤ s₀`. `AnalyticOnNhd ℂ G` on the closed polydisc `{u | ∀ τ j, ‖u τ j‖ ≤ ϱ}` is "holomorphic at each point of the closed polydisc", that is, on some open set that contains it: this is the usual meaning of "holomorphic on a closed polydisc", and it is what Cauchy's estimates on the polydisc of Lemma D.12 need. Agreement: at the real `u` with `|u_{τ j}| ≤ ϱ` (the real points of the same closed polydisc), `G(u) = F(s, H + u)`. The bound is in the norm of `Matrix T' d' ℂ` of the scope `Matrix.Norms.Elementwise`, the sup norm of the entries (any norm would do, the space is finite-dimensional). Not trivial, by the identity theorem as above: `G` is determined on the polydisc by its real values. Lean has the paper's extension in `u` for each real `s`, not in `(s, u)` jointly complex: LEAN WEAKER than the proof's sentence in this respect, and exactly what the lemma's second sentence needs (`t` is real). True (the statement follows from the first one at `(0, H)` with half the radius and a bound on the compact closed polydisc; I checked the steps of the proof by reading).
- Edge cases: `u = 0` lies in the polydisc, so `C ≥ ‖G 0‖ ≥ 0`; with `T` or `d` empty the space of `u` is one point and the statement is still true.
- Verdict: first statement SAME (the classical fact); second statement SAME as the step of the proof that the lemma uses (real `s`), LEAN WEAKER than "a complex neighborhood of `(0, 0)`" in the variable `s`. True.

### 5. The second sentence of the lemma (by reading, and a computation)

Lean (`Depth/ScaledSuffixHolomorphic.lean`):

```lean
theorem exists_holomorphic_suffix_pow_bounded (hε : 0 < ε) (hχ : A.χ = rmsNorm ε)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (m : ℕ) (θ η : Params A dIn dOut)
    (k : Fin (L + 1)) (H : Matrix T d ℝ) (hH : ∀ τ, H τ ≠ 0) :
    ∃ ϱ : ℝ, 0 < ϱ ∧ ∃ t₀ : ℝ, 0 < t₀ ∧ ∃ C : ℝ, ∀ t : ℝ, t₀ ≤ t →
      (∃ G : Matrix T d ℂ → Matrix T dOut ℂ,
        AnalyticOnNhd ℂ G {u | ∀ τ j, ‖u τ j‖ ≤ ϱ}
        ∧ (∀ u : Matrix T d ℝ, (∀ τ j, |u τ j| ≤ ϱ) →
            G (u.map fun a : ℝ => (a : ℂ))
              = (suffix A 0 θ k (t ^ m • (H + u))).map fun a : ℝ => (a : ℂ))
        ∧ ∀ u : Matrix T d ℂ, (∀ τ j, ‖u τ j‖ ≤ ϱ) → ‖G u‖ ≤ C)
      ∧ ∃ G' : Matrix T d ℂ → Matrix T dOut ℂ,
        AnalyticOnNhd ℂ G' {u | ∀ τ j, ‖u τ j‖ ≤ ϱ}
        ∧ (∀ u : Matrix T d ℝ, (∀ τ j, |u τ j| ≤ ϱ) →
            G' (u.map fun a : ℝ => (a : ℂ))
              = (fderiv ℝ (fun θ' : Params A dIn dOut => suffix A 0 θ' k (t ^ m • (H + u)))
                  θ η).map fun a : ℝ => (a : ℂ))
        ∧ ∀ u : Matrix T d ℂ, (∀ τ j, ‖u τ j‖ ≤ ϱ) → ‖G' u‖ ≤ C
```

`exists_holomorphic_suffix_bounded` is the same with `t • (H + u)` (`m = 1`).

(a) Against the paper ("Moreover, there are numbers `ϱ, t₀ > 0` such that the maps `u ↦ 𝓑_{>k}(t (h° + u))` and `u ↦ 𝐃_θ 𝓑_{>k}(t (h° + u)) η` extend to holomorphic maps on the rows `u ∈ ℂ^{1×d_model}` with `|u_j| ≤ ϱ` for all `j`, which are bounded uniformly in `t ≥ t₀`"), by reading:
- Quantifiers: `ϱ > 0`, `t₀ > 0`, then the bound `C`, then every `t ≥ t₀`, then one extension `G` (and one `G'`) for that `t`. The paper's "bounded uniformly in `t ≥ t₀`" is one bound for all `t ≥ t₀`, and the extension depends on `t`: the same order.
- "Extend": `G` agrees with the real map at the real `u` of the closed polydisc (`|u_{τ j}| ≤ ϱ`), and is holomorphic at every point of the closed complex polydisc (see check 4 for `AnalyticOnNhd ℂ` on a closed set). By the identity theorem the extension is unique on the polydisc, so the bound is a statement about the map, not about a choice.
- Both maps with the same `ϱ`, `t₀`, `C` (the proof takes the minimum of the radii and the maximum of the thresholds and bounds): the paper has one `ϱ` and one `t₀` for both maps, and "bounded" with no constant named; one `C` for both is the same.
- The second map is the derivative in the weights at fixed hidden state `t^m (H + u)`, for the real `u`, along any `η` (check 2 for "any direction"). Its extension is the extension of the real-analytic map `(s, h) ↦ 𝐃_θ 𝓑^♯(N_{ε s^{2m}}(h)) η` (`analyticAt_fderiv_params_scaledSuffix`): the paper's "The weights enter analytically as well, which gives the same for `𝐃_θ 𝓑_{>k}(·) η`".
- The hidden state of all tokens with no zero row in the place of the row `h°`, and `u` a matrix of all tokens: as in check 2. For one token it is the paper's sentence.
- Verdict: SAME for `exists_holomorphic_suffix_bounded`; the `_pow` form is the lemma with `t^m` in the place of `t`, which the proof of Lemma D.12 (fact (c), line 2285 to 2288) uses. True.

(b) Computation (`/home/claude/audit34a/d10_checks.py`, output in `/home/claude/audit34a/d10_checks.out`, 40 digits). A skipless pre-RMSNorm tanh network with `d = 3`, 4 hidden units, `L = 2` blocks, `d_out = 3`, `ε = 0.1`, Gaussian weights, one token, a random row `h°` (`‖h°‖ = 1.269`), `k = 0`. At complex `u`, the paper's formula `N_ε(t(h° + u)) = (h° + u)/√(⟨h° + u, h° + u⟩/d + ε t^{−2})` with the bilinear square and the principal root, then the blocks with the complex `tanh` and the complex RMSNorm of the later hidden states. On 300 random points of the distinguished boundary `|u_j| = ϱ` (where a holomorphic map on the polydisc takes its maximum), for `ϱ = 0.0733` and `ϱ = 0.220`:

| `t` | max `‖G(u)‖`, `ϱ = 0.0733` | max `‖𝐃_θ G(u) η‖` | max `‖G(u)‖`, `ϱ = 0.220` | max `‖𝐃_θ G(u) η‖` |
|---|---|---|---|---|
| 1 | 0.42870 | 2.1523 | 0.65613 | 3.4692 |
| 10 | 0.43269 | 2.0771 | 0.65221 | 3.4811 |
| 100 | 0.43273 | 2.0763 | 0.65216 | 3.4812 |
| 10⁴ | 0.43273 | 2.0763 | 0.65216 | 3.4812 |
| 10⁸ | 0.43273 | 2.0763 | 0.65216 | 3.4812 |
| `s = 0` | 0.43273 | | 0.65216 | |

(the derivative in the weights by a central difference of step `10⁻¹⁵` at 40 digits, on 60 of the points, along a random `η` of all the weights). The real part of `⟨h° + u, h° + u⟩/d` stays at least `0.448` (`0.290`) on the samples, so the root is holomorphic there; at real `u` the formula agrees with `𝓑_{>0}(t(h° + u))` (difference `0` at 40 digits, `t = 37`). The maps stay bounded as `t` grows and tend to the map at `s = 0`, as the statement says. A sample of the boundary bounds the maximum from below only; the statement is proved in Lean, and the computation is a consistency check.

(c) The zero row. For `h° = 0` the extension of `u ↦ N_ε(t u) = u/√(⟨u, u⟩/d + ε t^{−2})` is singular where `⟨u, u⟩ = −d ε t^{−2}`, for example at `u = (i √(d ε)/t, 0, 0)`, which lies in every polydisc of a fixed radius for large `t` (`|u_1| = 0.055, 0.0055, 0.00055` at `t = 10, 100, 1000`). So `hH` is needed for the second sentence too. And `t 𝐃𝓑_{>0}(t·0)(v) = 1.5153 t` (computed at `t = 10, 100, 1000`): with a zero row the first map is not a real-analytic function of `1/t` (check 2).

(d) Checks 1 and 2 by the same computation: for `i = 0, 1, 2` and `v_1 = … = v_i = v` random, `t^i 𝐃^i 𝓑_{>0}(t h°)(v, …, v)` (the derivative of `y ↦ 𝓑_{>0}(t h° + y v)`) and the derivative of order `i` of `x ↦ scaledSuffix(1/t, h° + x v)` agree to `10⁻⁴²` at `t = 10, 100, 10³, 10⁴`, and `(Θ(t) − Θ₀(0)) t²` tends to a constant (`0.0017605`, `−0.0032111`, `0.0051934`): the map is `Θ₀(0) + c s² + O(s⁴)` in `s = 1/t`, as the statement and `scaledSuffix_neg` (even in `s`) say.

### 6. What Lemma D.12 uses of Lemma D.10 (by reading)

The proof of Lemma D.12 cites Lemma D.10 twice (`dim.txt`, search "D.10": lines 2266 and 2287; line 1537 is the outline).
- Fact (a), lines 2264 to 2266: "Every `L_α` and `L'_{α,i}` is a real-analytic function of `t ∈ ℝ` that is meromorphic at infinity. … In the case (+) it is built from derivatives of `𝓑` and of `𝐃_θ 𝓑(·) η'` at `t^m h°` and from polynomials in `t`, so this is Lemma D.10 with `t^m` in the place of `t`." Of Lemma D.10 this uses the first sentence with `t^m`, for derivatives of every order (`L_α` has derivatives of order `|α|` of `𝓛^∞`, which contains `𝐃𝓑`, so of order up to `|α| + 1` of `𝓑`), applied to rows that are polynomial in `t`: the `_pow` statements (check 3). The rest of fact (a) (sums and products of maps meromorphic at infinity, the factors `t^{−|α|}`, and "real-analytic in `t ∈ ℝ`", which comes from `𝓑` being real-analytic, not from Lemma D.10) is a step of Lemma D.12.
- Fact (c), lines 2285 to 2299: "by Lemma D.10 with `t^m` in the place of `t`, the maps `u ↦ 𝓑(t^m(h° + u))` and `u ↦ 𝐃_θ 𝓑(t^m(h° + u)) η'` are holomorphic and bounded on the rows `u` with `|u_j| ≤ ϱ`, uniformly in `t ≥ t₀`": the second sentence with `t^m`, `exists_holomorphic_suffix_pow_bounded`. Then "and by Cauchy's estimate so is the derivative of the first where `|u_j| ≤ ϱ/2`" (line 2289), the holomorphy in `δ` of the left side of (34) (line 2292), and "By Cauchy's estimates, `L_α(t)` and `L'_{α,i}(t)` are at most a fixed power of `t` times `(ϱ' t)^{−|α|}`" (line 2295). These bounds are derived in the proof of Lemma D.12 from the statement of Lemma D.10; they are not part of Lemma D.10's statement, and Lean does not state them (its proof of Lemma D.12 bounds the coefficients another way). One step there is implicit: that `L_α(t)` is a Taylor coefficient of the holomorphic extension in `δ`, which holds because the extension agrees with the real map at the real points (uniqueness of the extension, by the identity theorem).
- Verdict: nothing of the statement of Lemma D.10 that the proof of Lemma D.12 uses is missing in Lean. What is not stated (Cauchy's estimates on the polydisc for the derivative of the first map and for the coefficients) belongs to the proof of Lemma D.12 (lines 2289 and 2295).

### 7. Drift (by reading)

- Hypotheses in Lean, not written in the lemma: `hf` (every block map real-analytic on all of its inputs): implied by the paper's blocks (tanh, GELU, SwiGLU, GeGLU are entire, and line 1696 says every `𝓑_{>k}` is real-analytic in the cases (n) and (+)). `hH` (no zero row) in the place of "`h° ≠ 0`": the generalization to several tokens, needed (checks 2 and 5 (c)). No skips (`suffix A 0`): the dimension paper's networks have none in Appendix D (`𝓑_{>k−1}(h) = 𝓑_{>k}(g_k(χ(h)))`, line 1677). Nothing else.
- Hypotheses of the paper not in Lean: none. "In the case (+)" is `hχ : A.χ = rmsNorm ε` with `hε : 0 < ε` (line 201: "In the case (+), pre-RMSNorm with `ε > 0`, `χ = N_ε`"; a learned gain is absorbed in the read, line 204); the two identities of check 1 hold without `hε`, as they should. `k ≤ L` is `k : Fin (L + 1)`. The Scope (`d_hidden ≥ d_model`, `d_in, d_out ≥ d_model ≥ 2`, no biases) is not used by Lemma D.10; Lean's blocks have no biases by the form `f_ℓ(n W_read) W_write`.
- The cases (n) and (0) are not claimed: in the case (n) `𝓑_{>k}(t h°)` is not bounded on the ray in general, and in the case (0) the paper treats rays on a great circle (Appendix D.6). The Lean statements are for the case (+) only, as the lemma.
- Lean more general than the paper: several tokens (`T` any finite type), any real-analytic blocks (attention included), any `m`, any direction `η` of all the weights, the identities for every `t > 0` and the analyticity at every `s`. None of these changes the meaning for one token.
- Verdict: no drift.

### 8. The index rows and the axioms (by reading, and by compiling a copy)

- Registrations: all 13 theorems are in `checks/Axioms.lean` (lines 2195 to 2203 for `ScaledSuffixOrders.lean`, 2234 to 2237 for the other two files); the three files are imported in `SkipsLean.lean` (lines 401 to 403).
- Axioms: after the full build had ended (`pgrep -f "lake build"` printed nothing), I compiled `/home/claude/audit34a/Ax.lean` with `lake env lean` from `/home/claude/lp/lean`: each of the 13 theorems depends on `[propext, Classical.choice, Quot.sound]` only. The copy also applies `exists_analyticOnNhd_complex_extension` to `x ↦ 1/(1 + x²)` on `Fin 1 → ℝ` at `0` (it compiles: the hypothesis is met for this function).
- `STATEMENTS.md` line 703 (`Depth/ScaledSuffix.lean`): true of the statements.
- Line 704 (`Depth/ScaledSuffixOrders.lean`): true, with two imprecisions. (i) "so the map is meromorphic at infinity (`MeromorphicAtInfinity`, exponent `0`)": the four statements say "meromorphic at infinity" with some natural exponent; the exponent `0` is in their proofs, and the real-analyticity in `1/t` itself is the pair "identity for `t > 0`" and "analytic in `s` at `0`". The file's header says the same ("with the exponent `l = 0`: it is a real-analytic function of `1/t`"). (ii) The row names no hypotheses: the analyticity and meromorphic statements ask pre-RMSNorm with `ε > 0` and real-analytic blocks; the two identities ask only pre-RMSNorm and `t > 0` (any `ε`, any `H`, also with zero rows).
- Line 705 (`Generic/HolomorphicExtension.lean`): true. It could say that the ball of the first statement is in the sup norm (a polydisc), and that in the second statement `s` is real and the extension is holomorphic in `u` only (the paper's sentence has a complex neighborhood of `(0, 0)` in `(1/t, u)`), on the closed polydisc in the sense `AnalyticOnNhd ℂ`.
- Line 706 (`Depth/ScaledSuffixHolomorphic.lean`): true of the statements.
- Line 384: the three files are listed as "Not yet compared"; after this report they are compared (see the corrections).

## Part 2: the statements, file by file

All 13 are proved (no `sorry`; standard axioms, check 8). I judged statements, not proofs.

| Paper sentence | Lean name | Verdict | Note |
|---|---|---|---|
| D.10 proof: "A derivative of order `i` in `v = t u` at `v = 0` is `t^{−i}` times the derivative of order `i` in `u` at `u = 0`" | `iteratedFDeriv_suffix_pow_smul` (`Depth/ScaledSuffixOrders.lean`) | SAME | With `t^m`; for every `t > 0`, `i` (also `0`), `H`, `ε`; no smoothness asked, none needed (check 1). |
| D.10, first sentence, first map: "real-analytic functions of `1/t` near `1/t = 0`" | `analyticAt_iteratedFDeriv_scaledSuffix` (same file) | PART; SAME with the previous | Analytic in `s` at every `s`; with the identity it is the paper's sentence for every `t > 0`. `ε > 0`, real-analytic blocks, no zero row of `H` (check 2). |
| D.10, first sentence, first map, "so they are meromorphic at infinity", with `t^m` | `meromorphicAtInfinity_iteratedFDeriv_suffix_pow` (same file) | SAME | The lemma "with `t^m` in the place of `t`" of the proof of D.12, fact (a) (check 3). |
| the same, `m = 1` | `meromorphicAtInfinity_iteratedFDeriv_suffix` (same file) | SAME | Exactly the paper's map `t ↦ t^i 𝐃^i 𝓑_{>k}(t h°)(v_1, …, v_i)`. |
| D.10 proof: "The weights enter analytically as well, which gives the same for `𝐃_θ 𝓑_{>k}(·) η`" (the identity) | `iteratedFDeriv_fderiv_params_suffix_pow_smul` (same file) | SAME | As check 1, for the derivative in the weights; any `η`. |
| "The weights enter analytically as well" | `analyticAt_fderiv_params_scaledSuffix` (same file) | SAME | `(s, h) ↦ 𝐃_θ 𝓑^♯(N_{ε s^{2m}}(h)) η` real-analytic at `(s, H)`, also at `s = 0`. |
| D.10, first sentence, second map: real-analytic in `1/t` | `analyticAt_iteratedFDeriv_fderiv_params_scaledSuffix` (same file) | PART; SAME with the identity | As for the first map. |
| D.10, first sentence, second map, meromorphic at infinity, with `t^m` | `meromorphicAtInfinity_iteratedFDeriv_fderiv_params_suffix_pow` (same file) | SAME | |
| the same, `m = 1` | `meromorphicAtInfinity_iteratedFDeriv_fderiv_params_suffix` (same file) | SAME | Exactly the paper's map `t ↦ t^i 𝐃^i (𝐃_θ 𝓑_{>k}(·) η)(t h°)(v_1, …, v_i)`. |
| the classical fact behind "It extends to a holomorphic … function on a complex neighborhood" | `exists_analyticOnNhd_complex_extension` (`Generic/HolomorphicExtension.lean`) | SAME (as the classical fact) | Open polydisc (sup norm); agreement on the real points of the same radius; not trivial by the identity theorem; `1/(1 + x²)`: every `r ≤ 1` works, none above (check 4). |
| D.10 proof: "It extends to a holomorphic and bounded function on a complex neighborhood of `(0, 0)`, which gives `ϱ` and `t_0`" | `exists_holomorphic_extension_real_param` (same file) | LEAN WEAKER in `s` (real `s` only); SAME for what the lemma uses | `ϱ`, `s₀`, `C` before `s`; one `G` per real `s`; holomorphic near the closed polydisc in `u`; bound in the sup norm of the entries. |
| D.10, second sentence, with `t^m` | `exists_holomorphic_suffix_pow_bounded` (`Depth/ScaledSuffixHolomorphic.lean`) | SAME | The form fact (c) of the proof of D.12 uses. Quantifiers `ϱ, t₀, C, ∀ t ≥ t₀, ∃ G` (check 5). |
| D.10, second sentence | `exists_holomorphic_suffix_bounded` (same file) | SAME | `m = 1`. Computed bounded for a tanh network up to `t = 10⁸` (check 5 (b)). |

Notes. (1) For one token every statement is the paper's; for several tokens "no zero row" is the right generalization of `h° ≠ 0`, and it is needed (a zero row makes the first map grow like `t`, and the extension singular inside every polydisc of fixed radius for large `t`). (2) The four statements "meromorphic at infinity" are weaker in their letter than "real-analytic in `1/t`" (they leave the exponent open), but the identities with the analyticity in `s` state the stronger form, so nothing of the sentence is lost.

## For the authors of the papers

Nothing false, vacuous, drifted or misdescribed was found in the 13 statements. Points where the paper's text could say more (none is an error):
1. Lemma D.10 (line 2019) is for one token ("a row `h°`"). For several tokens under RMSNorm, as in the Lean statements, the hypothesis must be that no row of the hidden state vanishes; with a zero row the first map is `t` times a constant at first order (computed: `t 𝐃𝓑_{>0}(t·0)(v) = 1.5153 t`) and is not a real-analytic function of `1/t`.
2. Proof of Lemma D.10 (lines 2041 to 2044): from "`𝓑_{>k}(t(h° + u))` is a real-analytic function of `(1/t, u)`" and the scaling of the derivatives, the first sentence follows because the derivatives in `u` at `u = 0` of a map real-analytic in `(1/t, u)` are real-analytic in `1/t`; the proof leaves this step to the reader. Lean states it (`analyticAt_iteratedFDeriv_scaledSuffix`).
3. Proof of Lemma D.12, fact (c) (lines 2289 to 2295): the bounds on `L_α(t)`, `L'_{α,i}(t)` by Cauchy's estimates use that these coefficients are the Taylor coefficients in `δ` of the holomorphic extension of Lemma D.10, which holds because the extension agrees with the real map at the real points and is therefore unique; the text uses this without saying it.
4. The radius. For a map that is real-analytic on all of `ℝ` the radius of the complex extension can be small (for `1/(1 + x²)` at most `1`): the `ϱ` of Lemma D.10 depends on `h°` and on the weights, as the lemma's quantifiers allow.

## Corrections for `STATEMENTS.md`

1. Line 384: remove `Depth/ScaledSuffixOrders.lean`, `Generic/HolomorphicExtension.lean`, `Depth/ScaledSuffixHolomorphic.lean` from "Not yet compared" and add: "A thirty-fourth reader (part A, 25 November) compared `Depth/ScaledSuffixOrders.lean`, `Generic/HolomorphicExtension.lean` and `Depth/ScaledSuffixHolomorphic.lean` (Lemma D.10 and the extension of a real-analytic map; 13 theorems): nothing false, vacuous or drifted; for several tokens the hypothesis is that no row vanishes, and it is needed (`ai_notes/lean-statement-audit-thirtyfourth-a-2026-11-25.md`)." (`Dimension/RankCriterionLieGroup.lean` was not in this audit.)
2. Line 704: replace "so the map is meromorphic at infinity (`MeromorphicAtInfinity`, exponent `0`)" by "so the map is meromorphic at infinity (`MeromorphicAtInfinity`; the statement leaves the exponent open, the proof takes `0`; the real-analyticity in `1/t` is the identity together with the analyticity in `s`)". Add the hypotheses: "under pre-RMSNorm with `ε > 0` and for real-analytic blocks; the two identities hold for every `ε`, every `t > 0` and every `H`". The same correction for the header of `Depth/ScaledSuffixOrders.lean` ("with the exponent `l = 0`").
3. Line 705: after "holomorphic on the ball of the same radius" add "(balls in the sup norm: polydiscs)"; after "for `|s| ≤ s₀`" add "(real `s`; the extension is holomorphic in `u` only, not in `(s, u)`), holomorphic near each point of the closed polydisc (`AnalyticOnNhd ℂ`)".
4. Lines 703 and 706: no correction.

## What I could not check

- The proofs: I judged the statements; that the proofs compile with the standard axioms I checked by compiling a copy, and I read the proofs of the two statements of `Generic/HolomorphicExtension.lean` to see that the radius and the bound come before `s`.
- The numerical maxima of check 5 are over samples of the distinguished boundary of the polydisc, a lower bound of the true maxima; they agree with the statement and do not prove it.
- Whether Mathlib has the complexification of a real-analytic map under another name: I searched `Analysis/Analytic` and `Analysis/Complex` of the pinned Mathlib for `complexif` and `ofReal` and found nothing; not an exhaustive search.

Commit read at the end: `c4a245c` (unchanged).
