STATUS: complete

# Thirty-third audit, part B, of Lean statements against the skips paper: networks of mixed blocks (Proposition A.1, Theorem A.5 (i), (ii), Proposition A.9), learned skips and biases (25 November 2026)

Commit read at the start: `0e1bc98` of `/home/claude/lp` (branch `lean-plus`).

Paper: `<scratchpad>/skips.txt`. Brief: `audit33b_brief_2026-11-25.md`, with the rules and form of `audit21a_brief_2026-11-24.md`.

Files with `sorry` at `0e1bc98`: `Residual/GaugeFixLearned.lean` (all 7 statements), `Residual/GaugeFixBiases.lean` (all 13 statements); as the brief says, a proving agent is at work on them, and only their statements are judged here.

## Part 1: checks

### 1. The network of mixed blocks (`Network/Mixed.lean`) — by reading

Lean:

```lean
abbrev Arch.mixed (A : Arch T d L) : Arch T d L where
  r ℓ := d ⊕ A.r ℓ
  w ℓ := d ⊕ A.w ℓ
  f ℓ M := Matrix.of fun t =>
    Sum.elim (fun a => M t (Sum.inl a)) (A.f ℓ (M.submatrix id Sum.inr) t)
  χ := A.χ

def evalMixed (A : Arch T d L) (θ : Params A.mixed dIn dOut) (x : Matrix T dIn ℝ) :
    Matrix T dOut ℝ :=
  eval A (fun ℓ => θ.mixU ℓ * θ.mixV ℓ) θ.unmix x

theorem evalMixed_eq_eval (hA : A.χ = id) (θ : Params A.mixed dIn dOut) (x : Matrix T dIn ℝ) :
    evalMixed A θ x = eval A.mixed 0 θ x
```

- `Arch.mixed` is the paper's mixed block of equation (9): the read has the columns `d ⊕ r` (`[U | W_read]`), the write the rows `d ⊕ w` (`V` stacked on `W_write`), and the fixed map is `f̃[u | z] = [u | f(z)]`, the identity on the first `d` columns. SAME.
- `evalMixed` unfolds (with `hidden`, `Network/Defs.lean`) to `h_0 = x E`, `h_ℓ = h_{ℓ−1} U_ℓ V_ℓ + f_ℓ(χ(h_{ℓ−1}) W_read^ℓ) W_write^ℓ`, `y = χ(h_L) D`. Without normalization this is (9); under RMSNorm (`χ = N_ε`) it is (10): the identity units read `h` itself and the hidden units read `N_ε(h)`, as the paper says ("the mixed block applies the map `χ(h) = [h | N_ε(h)]` before a block-diagonal read"). So `evalMixed` is the paper's function of the network of mixed blocks for every `χ`, the readout included (`y = N_ε(h_L) D`, as for every network of the paper). SAME.
- `evalMixed_eq_eval` asks `A.χ = id`, and it needs it: for `χ = N_ε`, `eval A.mixed 0 θ` would let the identity units read `N_ε(h)` (since `A.mixed.χ = A.χ`), which is not (10). The paper says "So it has the form (1)" only of (9), without normalization. The hypothesis is the paper's. SAME.
- `evalMixed_mix_one` (`Params.mix θ S 1` computes `eval A S θ`, for every `χ`): "A network with learned skips `A_ℓ` is the network of mixed blocks with `U_ℓ = A_ℓ` and `V_ℓ = I`". SAME. `f_mixed_mul` is equation (9) for one block. SAME.
- `d : Type` rather than `Type*`: `Arch.r ℓ : Type` (universe 0, `Network/Defs.lean`), and `A.mixed.r ℓ = d ⊕ A.r ℓ` must live there. Every finite index type of the paper (`Fin n`) is in `Type`, and every statement is about a finite type `d`, so nothing of substance is lost; the restriction is one of universes only.
- `Params.mixU`, `mixV`, `unmix`, `mix` and the four lemmas `mixU_mix`, `mixV_mix`, `unmix_mix`, `mix_unmix` are bookkeeping: `mix` and `(unmix, mixU, mixV)` are inverse bijections. Correct.

Verdict: SAME for the definition and the three named statements.

### 2. Proposition A.1 for networks of mixed blocks (`Symmetry/MixedJunctions.lean`) — by reading

Lean:

```lean
def Params.cobMixed (θ : Params A.mixed dIn dOut) (G Q : Fin (L + 1) → GL d ℝ)
    (K : Fin L → GL d ℝ) : Params A.mixed dIn dOut :=
  Params.mix (θ.unmix.cob G Q)
    (fun ℓ => (↑(G ℓ.castSucc)⁻¹ : Matrix d d ℝ) * θ.mixU ℓ * (K ℓ : Matrix d d ℝ))
    (fun ℓ => (↑(K ℓ)⁻¹ : Matrix d d ℝ) * θ.mixV ℓ * (G ℓ.succ : Matrix d d ℝ))

theorem evalMixed_cobMixed (G Q : Fin (L + 1) → GL d ℝ) (K : Fin L → GL d ℝ)
    (hχ : ∀ ℓ (h : Matrix T d ℝ), A.χ (h * (G ℓ : Matrix d d ℝ)) = A.χ h * (Q ℓ : Matrix d d ℝ)) :
    evalMixed A (θ.cobMixed G Q K) x = evalMixed A θ x
```

with `θ.unmix.cob G Q` = `E G_0`, `Q_{ℓ−1}⁻¹ W_read^ℓ`, `W_write^ℓ G_ℓ`, `Q_L⁻¹ D` (`Symmetry/ChangeOfBasis.lean`).

**What acts on what.** `G_ℓ` multiplies every write into `h_ℓ` on the right (`E`, `W_write^ℓ`, `V_ℓ`) and the read of the identity units of block `ℓ+1` on the left by `G_ℓ⁻¹` (`U_{ℓ+1}`, which reads `h_ℓ` itself); `Q_ℓ⁻¹` multiplies on the left the reads that see `χ(h_ℓ)` (`W_read^{ℓ+1}`, and `D` for `ℓ = L`); `K_ℓ` acts at the identity units (`U_ℓ K_ℓ`, `K_ℓ⁻¹ V_ℓ`). For `Q = G` this is the paper's `T_{G,K}` of (11), entry by entry. Under RMSNorm with `ε = 0` and `G = cQ`, the identity units' reads `U_ℓ` get `G_{ℓ−1}⁻¹`, and only the reads through RMSNorm get `Q^⊤`: this is the paper's map ("a read through RMSNorm maps to `Q^⊤ W` instead"; the proof: "A read that sees `h_ℓ` itself, such as the read of the identity units, computes `(h_ℓ G) G⁻¹ W = h_ℓ W`").

**(i)** `evalMixed_mixK` (`(U_ℓ, V_ℓ) ↦ (U_ℓ K_ℓ, K_ℓ⁻¹ V_ℓ)` at every block, every `χ`): "In a mixed block, `(U, V) ↦ (U K, K⁻¹ V)` preserves the function for every `K ∈ GL(d_model)`". The paper's map is at one block; Lean's at all blocks at once, which contains it (take `K_m = I` for the other blocks). SAME (Lean at least as strong).

**(ii)** `evalMixed_cobMixed` (any `χ`, under `χ(h G_ℓ) = χ(h) Q_ℓ`) and its three named forms:
- `evalMixed_cobMixed_id` (`χ = id`, every invertible `G`, `Q = G`): `𝒢 = GL(d_model)` without normalization. SAME.
- `evalMixed_cobMixed_rmsNorm` (`χ = rmsNorm ε`, any `ε`, orthogonal `Q`, `G = Q`): `𝒢 = O(d_model)` for `ε > 0`; for `ε = 0` it is the orthogonal part of `CO(d_model)`. SAME for `ε > 0`.
- `evalMixed_cobMixed_rmsNorm_zero` (`χ = rmsNorm 0`, `G_ℓ = c_ℓ Q_ℓ`, `c_ℓ > 0`, `Q_ℓ` orthogonal, reads through RMSNorm by `Q_ℓ⁻¹ = Q_ℓ^⊤`): `𝒢 = CO(d_model)` for `ε = 0`, with the paper's "maps to `Q^⊤ W` instead". SAME.
All three hold for any `K_ℓ`, as the paper's "one more copy of `GL(d_model)` per block" needs. The skipless half of (ii) is in the earlier files (`eval_cob_skipless` and its RMSNorm twins), not here.

**(iii)** `cobMixed_cobMixed`: `(θ.cobMixed G Q K).cobMixed G' Q' K' = θ.cobMixed (G * G') (Q * Q') (K * K')`, a right action of `GL(d)^{L+1} × GL(d)^{L+1} × GL(d)^L` (with `Q = G` for the network: of `GL(d)^{L+1} × GL(d)^L`); `cobMixed_comm`: two maps commute when their matrices commute at every junction (which holds when, at each junction, one of the two is the identity: "when they act at different junctions"; Lean's hypothesis is weaker, so the statement is stronger); `cobMixed_mixK_comm`: the map of (i) commutes with a change of basis at the hidden states; `cobMixed_one_one`: the map of (i) is `T_{1,K}`. With the invariance statements of (ii), these say that the group `𝒢^{L+1} × GL(d)^L` acts by maps that preserve the function, one factor per junction. They do not say that the factors act independently (that the action is faithful, so that the network "carries" a copy of `GL(d_model)` per block in the sense of a group of that dimension); the index says correctly that no dimension of the group is stated for mixed blocks. Verdict for the last sentence: PART (the group and its action are stated; the "therefore carries one more copy" as a count is not).

**Theorem A.5 (i).** `cobMixed_skipProd`: for `θ = Params.mix φ U V` with `U_ℓ, V_ℓ ∈ GL(d)`, `θ.cobMixed Λ Λ (fun ℓ => U_ℓ⁻¹ Λ_{ℓ−1}) = Params.mix (φ.cob Λ Λ) 1 1`, with `Λ = skipProd (U V)`: "With `G_ℓ = Λ_ℓ` and `K_ℓ = U_ℓ⁻¹ Λ_{ℓ−1}`, `T_{G,K}` sets every `U_ℓ` and `V_ℓ` to `I` and the other parameters to `Φ(θ)`". The indices: `K ℓ` (block `ℓ+1` in 1-based counting) uses `skipProd … ℓ.castSucc`, the paper's `Λ_{ℓ−1}`; correct. `evalMixed_eq_residual`: `F_θ = F^res_{Φ(θ)}` without normalization. The hypothesis "invertible `U_ℓ` and `V_ℓ`" is the paper's "skips `A_ℓ` invertible": for square matrices `U V` is invertible exactly when `U` and `V` are (the file `GaugeFixMixed.lean` proves this direction and states its versions with `IsUnit (U_ℓ V_ℓ)`). SAME.

### 3. Theorem A.5 (ii) for networks of mixed blocks (`Residual/GaugeFixMixed.lean`) — by reading, and by a computation

Lean (statements quoted without proofs):

```lean
noncomputable def mixedToResidual (θ : Params A.mixed dIn dOut) : Params A dIn dOut where
  E := θ.E * skipProdMat (fun ℓ => θ.mixU ℓ * θ.mixV ℓ) 0
  read ℓ := (skipProdMat (fun ℓ => θ.mixU ℓ * θ.mixV ℓ) ℓ.castSucc)⁻¹ * θ.unmix.read ℓ
  write ℓ := θ.unmix.write ℓ * skipProdMat (fun ℓ => θ.mixU ℓ * θ.mixV ℓ) ℓ.succ
  D := θ.D

theorem mixedToResidual_mix_one (θ : Params A dIn dOut) :
    mixedToResidual (Params.mix θ 1 1) = θ
theorem mixedToResidual_eq_iff (θ θ' : Params A.mixed dIn dOut)
    (hθ : ∀ ℓ, IsUnit (θ.mixU ℓ * θ.mixV ℓ)) (hθ' : ∀ ℓ, IsUnit (θ'.mixU ℓ * θ'.mixV ℓ)) :
    mixedToResidual θ' = mixedToResidual θ
      ↔ ∃ (G : Fin (L + 1) → GL d ℝ) (K : Fin L → GL d ℝ),
          G (Fin.last L) = 1 ∧ θ' = θ.cobMixed G G K
theorem exists_hasFDerivAt_mixedToResidual_surjective (θ : Params A.mixed dIn dOut)
    (hθ : ∀ ℓ, IsUnit (θ.mixU ℓ * θ.mixV ℓ)) :
    ∃ Φ' : Params A.mixed dIn dOut →L[ℝ] Params A dIn dOut,
      HasFDerivAt (mixedToResidual (A := A) (dIn := dIn) (dOut := dOut)) Φ' θ
        ∧ Function.Surjective Φ'
theorem image_evalMixed_eq_range_residual (hA : A.χ = id) :
    (fun θ : Params A.mixed dIn dOut => evalMixed A θ)
        '' {θ | ∀ ℓ, IsUnit (θ.mixU ℓ * θ.mixV ℓ)}
      = Set.range fun θ : Params A dIn dOut => eval A 1 θ
theorem funDim_mixed_eq_funDim_residual (hA : A.χ = id) (θ : Params A.mixed dIn dOut)
    (hθ : ∀ ℓ, IsUnit (θ.mixU ℓ * θ.mixV ℓ)) :
    funDim A.mixed 0 θ = funDim A 1 (mixedToResidual θ)
```

- **`mixedToResidual` against (12).** `skipProdMat S ℓ = S_{ℓ+1} ⋯ S_L` (reverse induction from `Λ_L = I`), so the four components are `E Λ_0`, `Λ_{ℓ−1}⁻¹ W_read^ℓ`, `W_write^ℓ Λ_ℓ`, `D`: equation (12). The inverse is Mathlib's `Matrix.inv` (`nonsing_inv`), which is the inverse at an invertible matrix and `0` at a singular one; so at a parameter with a singular skip `Φ` sets the reads of the blocks up to that skip to `0`, a value the paper does not define. Every public statement that evaluates `Φ` at a parameter has invertible skips there: `mixedToResidual_mix` (`U, V : GL`), `mixedToResidual_mix_one` (`Λ = I`), `mixedToResidual_eq_iff` (`hθ`, `hθ'`), the derivative (`hθ`), `evalMixed_eq_eval_mixedToResidual` (`hθ`), `funDim_mixed_eq_funDim_residual` (`hθ`). The derivative is taken on all parameters, at a point with invertible skips, where `Φ` agrees with the paper's map on a neighbourhood (invertibility is open). SAME.
- **`mixedToResidual_mix_one`:** "Every parameter of the residual network is `Φ(θ)` for some `θ`", with the paper's witness ("the `θ` with the same entries and `U_ℓ = V_ℓ = I`"). SAME.
- **`mixedToResidual_eq_iff`:** both directions, `G_L = 1`, the map `θ.cobMixed G G K` = `T_{G,K}` of (11) without normalization. Both hypotheses are in the paper's scope ("parameters `θ` whose skips `A_ℓ` are invertible"), and `hθ'` is needed in Lean: with the value `0` of the inverse at a singular matrix, take `L = 1`, `θ` with `E = 0` and `W_read^1 = 0`, and `θ'` with the same write and readout, `E' = 0`, any `W_read'^1` and `U'_1 = 0`: then `Φ(θ') = (0, 0, W_write^1, D) = Φ(θ)`, while `T_{G,K}` keeps the skips invertible, so `θ'` is not `T_{G,K}(θ)`. SAME.
- **`exists_hasFDerivAt_mixedToResidual_surjective`:** "The derivative of `Φ` is onto at every `θ`", at every `θ` of the scope (invertible skips); it states the existence of the derivative and that it is onto, at the given `θ` (not "at some point"). SAME.
- **`image_evalMixed_eq_range_residual`:** the image of the set of parameters with invertible skips under `θ ↦ F_θ` is the set of functions of the residual network, without normalization. SAME.
- **`funDim_mixed_eq_funDim_residual`:** `funDim A.mixed 0 θ` is the functional dimension (maximum over finite batches of the rank of the Jacobian, `Dimension/Functional.lean`) of the skipless network of the architecture `A.mixed`, in all of its parameters `E`, `[U_ℓ | W_read^ℓ]`, `[V_ℓ ; W_write^ℓ]`, `D`; under `hA` this network is `evalMixed` (`evalMixed_eq_eval`), so it is the functional dimension of the network of mixed blocks in the paper's parameters `θ = (E, (U_ℓ, V_ℓ, W_read^ℓ, W_write^ℓ), D)`. It is stated for any blocks, also non-differentiable ones: Lean's `fderiv` is `0` where the batch map is not differentiable, and the batch maps at `θ` and at `Φ(θ)` are differentiable together (the residual batch map is the mixed one composed with an affine right inverse of `Φ`, and the mixed one is the residual one composed with `Φ` near `θ`); so the statement is true in that convention. The paper's argument (chain rule) is for differentiable outputs. SAME (Lean at least as strong).
- **Computation** (`/home/claude/audit33b/check33b.py`, output in `check33b.out`; tanh blocks, no normalization, `(L, d, d_in, d_out, width) = (1,2,2,2,3), (2,2,3,2,2), (2,3,3,3,3)`, 80 inputs of one token, exact derivatives by complex step, rank at the largest gap of the singular values): `|F_θ − F^res_{Φ(θ)}|` ≤ `5·10⁻¹¹`; `T_{G,K}` with random `G`, `K` and `G_L = I` keeps the function (≤ `8·10⁻¹⁴`) and `Φ` (≤ `10⁻⁸`, the largest at `d = 3` from badly conditioned random `G`), and with `G_L ≠ I` moves `Φ` by `10²`–`10³`; for "only if", a second parameter `θ̃` built by drawing new invertible `Ũ_ℓ`, `Ṽ_ℓ` and solving `Φ(θ̃) = Φ(θ)` for the rest is `T_{G,K}(θ)` with the paper's `G_ℓ = Λ_ℓ Λ̃_ℓ⁻¹`, `K_ℓ = U_ℓ⁻¹ G_{ℓ−1} Ũ_ℓ` (≤ `2·10⁻⁷`, `G_L = I` exactly). Ranks of the two Jacobians: 16 and 16 (`P = 28`, `P_res = 20`; gaps 13.4 and 12.8 decades), 22 and 22 (`P = 42`, `P_res = 26`; 12.0, 12.4), 45 and 45 (`P = 90`, `P_res = 54`; 12.1, 6.3), each `P_res − d²`. The coordinator's script (copy run in `/home/claude/audit33b/`) gives the same ranks with a threshold; it reads the rank at a threshold, not at the gap, but the gaps above confirm its values.

Verdict for check 3: SAME throughout.

### 4. Proposition A.9 (i) for mixed blocks, and the count (`ExactReductionMixed.lean`, `ExactReductionCount.lean`) — by reading

Lean (two of the four existence statements; the other two are their twins for rows of writes):

```lean
theorem exists_cob_mixed_reads_eq_one (hA : A.χ = id)
    (c : ∀ ℓ : Fin L, d → d ⊕ A.r ℓ) (cD : d → dOut)
    (hc : ∀ ℓ, IsUnit ((θ.read ℓ).submatrix id (c ℓ)).det)
    (hcD : IsUnit (θ.D.submatrix id cD).det) :
    ∃ G : Fin (L + 1) → GL d ℝ,
      (∀ x : Matrix T dIn ℝ, evalMixed A (θ.cob G G) x = evalMixed A θ x) ∧
      (∀ ℓ, ((θ.cob G G).read ℓ).submatrix id (c ℓ) = 1) ∧
      (θ.cob G G).D.submatrix id cD = 1
theorem exists_cob_mixed_reads_upperTriangular [LinearOrder d] (ε : ℝ) (hA : A.χ = rmsNorm ε)
    (c : ∀ ℓ : Fin L, d → d ⊕ A.r ℓ) (cD : d → dOut) :
    ∃ Q : Fin (L + 1) → GL d ℝ,
      (∀ ℓ, (Q ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ) ∧
      (∀ x : Matrix T dIn ℝ, evalMixed A (θ.cob Q Q) x = evalMixed A θ x) ∧
      (∀ ℓ, (((θ.cob Q Q).read ℓ).submatrix id (c ℓ)).BlockTriangular id) ∧
      ((θ.cob Q Q).D.submatrix id cD).BlockTriangular id

theorem finrank_span_reads_eq_zero (c : ∀ ℓ : Fin L, d → A.r ℓ) (cD : d → dOut)
    (hc : ∀ ℓ, Function.Injective (c ℓ)) (hcD : Function.Injective cD) :
    Module.finrank ℝ (Submodule.span ℝ {η : Params A dIn dOut |
        (∀ ℓ, (η.read ℓ).submatrix id (c ℓ) = 0) ∧ η.D.submatrix id cD = 0})
      + (L + 1) * Fintype.card d ^ 2
      = Module.finrank ℝ (Params A dIn dOut)
```

- **The existence statements.** For a parameter `θ` of `A.mixed`, `θ.read ℓ` is the paper's read `[U_ℓ | W_read^ℓ]` of `h_{ℓ−1}` and `θ.write ℓ` the write that stacks `V_ℓ` on `W_write^ℓ`; `θ.cob G G` is `T_{G,1}` (`cobMixed_one_eq_cob`). The chosen columns `c ℓ : d → d ⊕ A.r ℓ` may come from `U_ℓ`, from `W_read^ℓ`, or from both; the chosen rows `ρ ℓ : d → d ⊕ A.w ℓ` from `V_ℓ`, `W_write^ℓ` or both; `D` and `E` stand for the read of `h_L` and the write of `h_0`. So "a matrix that reads `h_ℓ`" and "a matrix that writes it" are the paper's, for networks of mixed blocks. Without normalization the conclusion is `I` with invertible submatrices (the paper's `G = W_1` for a read, `W_1⁻¹` for a write); under RMSNorm the conclusion is upper triangular for reads (`BlockTriangular id`: entries `(i, j)` with `j < i` vanish) and lower triangular for writes (the transpose is upper triangular), with orthogonal `Q`, as in the proof ("`W_1 Q = T^⊤`, which is lower triangular"). Lean states the RMSNorm forms for every `ε` (the paper: `ε > 0`) and without asking the submatrices to be invertible (a QR factorization exists for every square matrix): LEAN STRONGER, true (the orthogonal change of basis preserves the function for every `ε`, `evalMixed_cobMixed_rmsNorm`).
- **"Done at every hidden state".** Each statement makes the reduction at all `L + 1` hidden states at once, but with the chosen submatrix of every hidden state in a read (all `L + 1` in reads: block reads and `D`) or in a write (all in writes: `E` and block writes). The paper's sentence lets each hidden state choose its submatrix in a read or a write ("Let `W_1` be … `d_model` columns of a matrix that reads `h_ℓ`, or … `d_model` rows of a matrix that writes it"; the proof: "one submatrix per hidden state"). A choice that mixes reads and writes across hidden states is not stated for mixed blocks (for skipless networks, `Symmetry/AtOneState.lean` has the change at one hidden state, `cobAt_*`, from which mixed choices follow by composition; for mixed blocks there is no `cobAt` form). Verdict: PART.
- **The counts.** `finrank_span_reads_eq_zero` and its write twin: the span of the parameters whose chosen submatrices vanish (the directions of the affine set in which they are `I`) has dimension `P − (L + 1) d²`; `finrank_span_reads_upperTriangular` and `finrank_span_writes_lowerTriangular`: the span of the parameters whose chosen submatrices are upper (lower) triangular has dimension `P − (L + 1) d(d − 1)/2`. They are stated for any architecture, so also for `A.mixed` (the file `ExactReductionCount.lean` has `d : Type*`, and `A.mixed` needs `d : Type`, which is a special case). The hypothesis that the chosen columns are injective is needed (two equal columns would fix fewer entries) and is implied by the paper's invertibility. With the existence statements they give the paper's "removes `d_model²`, respectively `d_model(d_model − 1)/2`, parameters per hidden state without changing the function": every `θ` with invertible chosen submatrices has the function of a parameter in an affine set of dimension `P − (L + 1) d²`. The same split as above: all reads or all writes; a mixed choice is not counted (it would give the same number, since the chosen submatrices lie in different matrices). Lean does not combine existence and count in one statement; that is a presentation choice. Verdict: PART (only the two uniform choices), SAME for these.

### 5. The statements for learned skips (`Residual/GaugeFixLearned.lean`, statements with `sorry`) — by reading, and by a computation

Lean (statements at `0e1bc98`):

```lean
noncomputable def learnedToResidual (p : Params A dIn dOut × (Fin L → Matrix d d ℝ)) :
    Params A dIn dOut where
  E := p.1.E * skipProdMat p.2 0
  read ℓ := (skipProdMat p.2 ℓ.castSucc)⁻¹ * p.1.read ℓ
  write ℓ := p.1.write ℓ * skipProdMat p.2 ℓ.succ
  D := p.1.D

theorem learnedToResidual_eq_iff (p p' : Params A dIn dOut × (Fin L → Matrix d d ℝ))
    (hp : ∀ ℓ, IsUnit (p.2 ℓ)) (hp' : ∀ ℓ, IsUnit (p'.2 ℓ)) :
    learnedToResidual p' = learnedToResidual p
      ↔ ∃ G : Fin (L + 1) → GL d ℝ,
          G (Fin.last L) = 1 ∧ p' = (p.1.cob G G, cobSkip p.2 G)
theorem funDimLearned_eq_funDim_residual (hA : A.χ = id)
    (p : Params A dIn dOut × (Fin L → Matrix d d ℝ)) (hp : ∀ ℓ, IsUnit (p.2 ℓ)) :
    funDimLearned A p = funDim A 1 (learnedToResidual p)
```

- `cobSkip p.2 G ℓ = G_{ℓ−1}⁻¹ A_ℓ G_ℓ` (`Symmetry/ChangeOfBasis.lean`: `(↑(G ℓ.castSucc)⁻¹) * M ℓ * (G ℓ.succ)`), and `p.1.cob G G` is `E G_0`, `G_{ℓ−1}⁻¹ W_read^ℓ`, `W_write^ℓ G_ℓ`, `G_L⁻¹ D`: the paper's `T_G` for learned skips ("`T_G` acts by `A_ℓ ↦ G_{ℓ−1}⁻¹ A_ℓ G_ℓ` in place of the second line"). SAME.
- `learnedToResidual`: (12) "with the same formula for learned skips", with the same convention for the inverse as `mixedToResidual` (`0` at a singular `Λ`); every statement that evaluates it is at invertible skips or at `A = I`. SAME.
- `funDimLearned A p = funDimSkips A id p` (`OneBlock/LearnedSkip.lean`): the maximum over finite batches of the rank of the Jacobian of `(θ, A) ↦ (eval A A_· θ x_i)_i`, in the weights and all `L d²` entries of the skips: the functional dimension of the network with learned skips in the paper's parameters `(E, (A_ℓ, W_read^ℓ, W_write^ℓ), D)`. SAME.
- The seven statements, against "The same holds for learned skips, without the `K_ℓ`" (and, for (i), "For learned skips, `T_G` with `G_ℓ = Λ_ℓ` sets every `A_ℓ` to `I` in the same way"):
  - `learnedToResidual_coe`: `Φ(θ, A) = θ.cob Λ Λ` for invertible skips: (12), and with `eval_learned_eq_residual` and `cobSkip_skipProd` (earlier files) the gauge fix of (i). SAME.
  - `learnedToResidual_one`: every residual parameter is `Φ(θ, I)`. SAME.
  - `learnedToResidual_eq_iff`: the fibres of `Φ` are the orbits of `T_G` with `G_L = I`, both directions, no `K`. `hp'` is needed for the same reason as `hθ'` in check 3 (with `A'_1 = 0`, `E' = 0`, `W_read^1 = 0` the two images agree). True by the paper's computation (`G_ℓ = Λ_ℓ Λ̃_ℓ⁻¹`; then `θ̃ = θ.cob G G` and `Ã_ℓ = Λ̃_{ℓ−1} Λ̃_ℓ⁻¹ = G_{ℓ−1}⁻¹ A_ℓ G_ℓ`). SAME.
  - `exists_hasFDerivAt_learnedToResidual_surjective`: at every `p` with invertible skips. SAME.
  - `eval_eq_eval_learnedToResidual`, `image_eval_learned_eq_range_residual`: without normalization. SAME.
  - `funDimLearned_eq_funDim_residual`: without normalization, any blocks (true in Lean's convention by the argument of check 3: `r(θ') = (θ'.cob Λ⁻¹ Λ⁻¹, A)` is an affine right inverse of `Φ` through `p`). SAME.
- **Computation** (same script, `learned` rows): `|F_{θ,A} − F^res_{Φ}|` ≤ `4·10⁻¹³`; `T_G` with `G_L = I` keeps the function and `Φ` (≤ `2·10⁻¹⁴`); `G_L ≠ I` moves `Φ` (by 4 to 60); a second parameter in the fibre, from new random invertible skips with the rest solved from `Φ`, is `T_G(p)` with `G_ℓ = Λ_ℓ Λ̃_ℓ⁻¹` (≤ `3·10⁻¹⁴`, `G_L = I`). Ranks in the weights and skips against the residual network at `Φ`: 16 and 16 (`P = 24`, `P_res = 20`; gaps 12.4, 12.1 decades), 22 and 22 (`P = 34`; 7.7, 8.4), 45 and 45 (`P = 72`, `P_res = 54`; 13.5, 12.5), each `P_res − d²`. No counterexample; the statements are true as far as tested.

Verdict for check 5: SAME for all seven statements.

### 6. The statements with biases (`Residual/GaugeFixBiases.lean`, statements with `sorry`) — by reading, and by a computation

Lean (definitions and two of the thirteen statements, at `0e1bc98`):

```lean
def Biases.mulSkipProd (b : Biases A dOut) (Λ : Fin (L + 1) → Matrix d d ℝ) : Biases A dOut where
  E := b.E ᵥ* Λ 0
  read := b.read
  write ℓ := b.write ℓ ᵥ* Λ ℓ.succ
  D := b.D

def evalMixedB (A : Arch T d L) (p : Params A.mixed dIn dOut × Biases A dOut)
    (x : Matrix T dIn ℝ) : Matrix T dOut ℝ :=
  evalB A (fun ℓ => p.1.mixU ℓ * p.1.mixV ℓ) p.1.unmix p.2 x

theorem mixedToResidualB_eq_iff (p p' : Params A.mixed dIn dOut × Biases A dOut)
    (hp : ∀ ℓ, IsUnit (p.1.mixU ℓ * p.1.mixV ℓ))
    (hp' : ∀ ℓ, IsUnit (p'.1.mixU ℓ * p'.1.mixV ℓ)) :
    mixedToResidualB p' = mixedToResidualB p
      ↔ ∃ (G : Fin (L + 1) → GL d ℝ) (K : Fin L → GL d ℝ),
          G (Fin.last L) = 1 ∧ p' = (p.1.cobMixed G G K, p.2.cob G)
theorem funDimOf_evalMixedB_eq_funDimB_residual (hA : A.χ = id)
    (p : Params A.mixed dIn dOut × Biases A dOut) (hp : ∀ ℓ, IsUnit (p.1.mixU ℓ * p.1.mixV ℓ)) :
    funDimOf (evalMixedB A) p = funDimB A 1 (mixedToResidualB p)
```

- **`Biases.mulSkipProd`** (`ᵥ*` is a row times a matrix): `b_E Λ_0`, `b_read^ℓ` kept, `b_write^ℓ Λ_ℓ` (block `ℓ` 1-based writes `h_ℓ`: `Λ ℓ.succ` in 0-based Lean), `b_D` kept: "With biases, `Φ` also sends the embedding bias `b_E` to `b_E Λ_0` and each write bias `b_write^ℓ` to `b_write^ℓ Λ_ℓ`, and keeps each read bias". The paper's sentence does not name the readout bias; keeping it is what its proof does (`D' = D`, and the output `h'_L D' + b_D = h_L D + b_D`). SAME.
- **The network.** `evalMixedB` is `h_0 = x E + b_E`, `h_ℓ = h_{ℓ−1} U_ℓ V_ℓ + f_ℓ(χ(h_{ℓ−1}) W_read^ℓ + b_read^ℓ) W_write^ℓ + b_write^ℓ`, `y = χ(h_L) D + b_D`, with biases only on the hidden units, the embedding and the readout: the paper's Part (ii), "The identity units carry no biases of their own, since these would only add to the write bias". SAME.
- **The skip bias merged into the write bias.** The paper's Part (i) network `h_ℓ = h_{ℓ−1} A_ℓ + k_ℓ + f_ℓ(…) W_write^ℓ + b_write^ℓ` is, as a function of `x`, the network `evalB` with the write bias `b_write^ℓ + k_ℓ` (the two terms enter the stream at the same place), and the paper's new write bias `(b_write^ℓ + k_ℓ) Λ_ℓ` is `mulSkipProd` of that bias. So the statement of Part (i) with a skip bias is the Lean statement applied to `b_write + k`, and nothing of the function or of Part (i) is lost. What is not formalized is a parametrization with `k_ℓ` as separate parameters (the fibres of `Φ` and the functional dimension would then count `k_ℓ` and `b_write^ℓ` separately); the paper's Part (ii) excludes such parameters explicitly ("The identity units carry no biases of their own"), so Lean matches the paper's statement. SAME.
- **The action** `(θ.cobMixed G G K, b.cob G)` with `b.cob G = (b_E G_0, b_read, b_write^ℓ G_ℓ, b_D)` (`Symmetry/BiasesSymmetries.lean`). The paper's (11) does not say how `T_{G,K}` acts on the biases; Theorem A.5 (ii) "and for networks with biases" needs this action (with it, the fibres of `Φ` are exactly the orbits; with the biases kept, `Φ(T(p))` has the embedding bias `b_E G_0⁻¹ Λ_0` in place of `b_E Λ_0`, so the "if" direction fails as soon as `b_E` or a write bias is nonzero and `G ≠ I`). Lean's choice is the one implied by Proposition A.1's proof with biases (`b_write ↦ b_write G` for `g = 0`). The translations of Lemma A.8 are symmetries of the function but do not move `Φ` in a fibre, and are rightly not part of `T`.
- **The thirteen statements.** Mixed blocks: `evalMixedB_cobMixed` ("The maps `T_{G,K}` preserve the function", every `θ`, no invertibility, `χ = id`), `evalMixedB_eq_evalB_mixedToResidualB` (`F = F^res_{Φ}`), `mixedToResidualB_mix_one`, `mixedToResidualB_eq_iff`, `exists_hasFDerivAt_mixedToResidualB_surjective`, `image_evalMixedB_eq_range_residual`, `funDimOf_evalMixedB_eq_funDimB_residual`. Learned skips: `evalB_eq_evalB_learnedToResidualB`, `learnedToResidualB_one`, `learnedToResidualB_eq_iff` (with `((θ.cob G G, b.cob G), cobSkip A G)`), `exists_hasFDerivAt_learnedToResidualB_surjective`, `image_evalB_learned_eq_range_residual`, `funDimOf_evalB_learned_eq_funDimB_residual`; that `T_G` preserves the function for learned skips with biases is the proved `evalB_cob`, not restated here. Each is the twin of a statement of check 3 or 5 with the biases added, with the same hypotheses; `funDimOf (evalMixedB A) p` is the functional dimension in all parameters `(θ, b)` of the network of mixed blocks with biases, and `funDimB A 1` that of the residual network with biases. All thirteen are, by the computation below and the paper's argument (the right inverse `(θ', b') ↦ (Params.mix (θ'.cob Λ⁻¹ Λ⁻¹) U V, b'.cob Λ⁻¹)` is linear and `Φ` is smooth near `p`), true. SAME for each.
- **Computation** (same script, `bias=True` rows; mixed blocks and learned skips): `|F − F^res_Φ|` ≤ `2·10⁻¹²`; `T` with the bias action keeps the function (≤ `5·10⁻¹³`) and, for `G_L = I`, `Φ` (≤ `4·10⁻¹¹`); `G_L ≠ I` moves `Φ`; a second parameter in the fibre (new random invertible `Ũ, Ṽ` or `Ã`, the weights and biases solved from `Φ`) is `T_{G,K}` (or `T_G`) of the first, with the bias action `b.cob G` (≤ `7·10⁻¹¹`). Ranks: mixed with biases 21, 28, 54 against residual with biases 21, 28, 54 (gaps ≥ 7.6 decades); learned with biases 21, 28, 54 against 21, 28, 54. Each is `P_res − d² − (L + 1) d`, the count of Lemma A.8 for tanh blocks (no symmetries inside the blocks of positive dimension).

Verdict for check 6: SAME for the definitions and all thirteen statements. For the authors: the paper should say how `T_{G,K}` acts on the biases in Theorem A.5 (ii) with biases.

### 7. Drift checks — by reading

- **The functional dimension is the maximum over all finite batches** in every statement: `funDim` (`Dimension/Functional.lean`: `sSup {r | ∃ n X, r = jacobianRank A S X θ}`), `funDimSkips`/`funDimLearned` (`OneBlock/LearnedSkip.lean`, the same over the weights and skips), `funDimOf` (`Dimension/FunDimFamily.lean`, the same for any family) and `funDimB` (`Dimension/FunctionalBiases.lean`). No statement of the seven files fixes a batch. No drift.
- **"At every `θ`"**: every statement about the derivative of `Φ` or the functional dimension is at the given parameter (with invertible skips, the paper's scope); none is "there is a point". No drift.
- **Hypotheses not in the paper**: `hθ'`/`hp'` (the second parameter has invertible skips: in the paper's scope, and needed in Lean, check 3); `Function.Injective` of the chosen columns or rows in the counts (implied by the paper's invertible `W_1`, and needed); `[LinearOrder d]` for the triangular forms (needed to say "triangular"); `d : Type` (universe only, check 1); `A.χ = id` wherever the paper says "without normalization". None restricts the paper's statements.
- **Lean weaker than the paper**: Proposition A.9 (i) only with all chosen submatrices in reads or all in writes (check 4); Proposition A.1 (iii) without the statement that the copies of `GL(d_model)` act independently (check 2). Neither is a drift of a stated sentence; both are parts left out.

### 8. The index rows and the axioms — by reading, and by compiling a copy

- **Registrations.** All 35 proved theorems of the five proved files (7 + 11 + 8 + 5 + 4, the brief's count) are listed in `checks/Axioms.lean`, and the seven files are imported by `SkipsLean.lean`.
- **Axioms.** A copy (`/home/claude/audit33b/Ax33b.lean`, compiled with `lake env lean` from `/home/claude/lp/lean` after the full build had ended: no `lake build` process, every `.olean` of the seven files newer than its source) prints `[propext, Classical.choice, Quot.sound]` for each of the 35 theorems; as a control, `learnedToResidual_eq_iff` and `mixedToResidualB_eq_iff` print `sorryAx` besides, as expected for the two files with statements only.
- **The rows** (`STATEMENTS.md`, the rows of `Network/Mixed.lean` to `Residual/ExactReductionCount.lean`, and the list "Not yet compared"):
  - `Network/Mixed.lean`: true of the statements.
  - `Symmetry/MixedJunctions.lean`: true; it should say that (iii) is stated as the composition law and the commutation of the maps, and that neither the independence of the factors nor the dimension of the group of a network of mixed blocks is stated.
  - `Residual/GaugeFixMixed.lean`: true. ("for any blocks (no differentiability is asked)" is right: check 3.)
  - `Residual/GaugeFixLearned.lean` ("in work") and `Residual/GaugeFixBiases.lean` ("in work"): true of the statements. In the biases row, "`T_{G,K}` with `b ↦ b.cob G` preserves the function" is stated in this file only for mixed blocks (`evalMixedB_cobMixed`); for learned skips with biases it is the proved `evalB_cob` of `Symmetry/BiasesSymmetries.lean`, which the row should name.
  - `Residual/ExactReductionMixed.lean`: the row ends with "`Symmetry/MixedJunctions.lean` (in work)": that file is proved (its row says so); "(in work)" is stale. The row should also say that the chosen submatrices are all in reads or all in writes, not a choice per hidden state.
  - `Residual/ExactReductionCount.lean`: "one submatrix per hidden state" reads as the paper's free choice per hidden state; the statements have all `L + 1` submatrices in reads (the block reads and `D`) or all in writes (`E` and the block writes). The row should say so.
  - The list "Not yet compared, written after the thirty-second audit began" names the seven files; after this report they are compared.

## Part 2: the statements, file by file

| Lean name | Paper sentence | Verdict | Note |
|---|---|---|---|
| **`Network/Mixed.lean`** | | | |
| `Arch.mixed` | A.1 "Mixed blocks", the read `[U | W_read]`, the write `[V ; W_write]`, `f̃` | SAME | `d : Type`: universe only |
| `Params.mixU`, `mixV`, `unmix`, `mix` | the parameters `θ = (E, (U_ℓ, V_ℓ, W_read^ℓ, W_write^ℓ), D)` (A.2) | SAME | bookkeeping |
| `evalMixed` | (9) and (10): identity units read `h`, hidden units read `χ(h)` | SAME | every `χ` |
| `mixU_mix`, `mixV_mix`, `unmix_mix`, `mix_unmix` | (bookkeeping) | — | correct |
| `f_mixed_mul` | equation (9) | SAME | |
| `evalMixed_eq_eval` | "So it has the form (1)" | SAME | `χ = id`, needed |
| `evalMixed_mix_one` | "A network with learned skips `A_ℓ` is the network of mixed blocks with `U_ℓ = A_ℓ` and `V_ℓ = I`" | SAME | every `χ` |
| **`Symmetry/MixedJunctions.lean`** | | | |
| `Params.mixK` | the map of A.1 (i) | SAME | at all blocks at once |
| `Params.cobMixed` | `T_{G,K}` of (11); for `ε = 0`, reads through RMSNorm by `Q^⊤` | SAME | `Q` on reads of `χ(h)`, `G` on `U` |
| `evalMixed_mixK` | A.1 (i) | SAME | |
| `evalMixed_cobMixed` | A.1 (ii) for mixed blocks; A.5 (i) first sentence | SAME | under `χ(h G) = χ(h) Q` |
| `evalMixed_cobMixed_id` | A.1 (ii), `𝒢 = GL`; A.5 (i) first sentence | SAME | |
| `evalMixed_cobMixed_rmsNorm` | A.1 (ii), `𝒢 = O(d)` for `ε > 0` | SAME | any `ε` |
| `evalMixed_cobMixed_rmsNorm_zero` | A.1 (ii), `ε = 0`, `G = cQ`, "maps to `Q^⊤ W` instead" | SAME | |
| `cobMixed_one_one` | the map of (i) is `T_{1,K}` | SAME | |
| `cobMixed_cobMixed` | A.1 (iii) "One group per junction" | PART | composition law; no faithfulness or dimension |
| `cobMixed_comm` | A.1 (iii) "commute when they act at different junctions" | LEAN STRONGER | commuting matrices at each junction |
| `cobMixed_mixK_comm` | A.1 (iii), (i) and (ii) commute | SAME | |
| `cobMixed_skipProd` | A.5 (i) "`T_{G,K}` sets every `U_ℓ` and `V_ℓ` to `I` and the other parameters to `Φ(θ)`" | SAME | `U, V` invertible ⇔ `A` invertible |
| `evalMixed_eq_residual` | A.5 (i) "so `F_θ = F^res_{Φ(θ)}`" | SAME | |
| **`Residual/GaugeFixMixed.lean`** | | | |
| `skipProdMat` | `Λ_ℓ = A_{ℓ+1} ⋯ A_L`, `Λ_L = I` | SAME | |
| `mixedToResidual` | `Φ` of (12) | SAME | inverse `0` at singular `Λ`; never used there |
| `skipProdMat_coe`, `mixedToResidual_mix` | (12) for invertible skips | SAME | |
| `mixedToResidual_mix_one` | A.5 (ii) "Every parameter of the residual network is `Φ(θ)` for some `θ`" | SAME | |
| `mixedToResidual_eq_iff` | A.5 (ii) "`Φ(θ̃) = Φ(θ)` exactly when `θ̃ = T_{G,K}(θ)` … `G_L = I`" | SAME | both hypotheses needed; tested |
| `exists_hasFDerivAt_mixedToResidual_surjective` | A.5 (ii) "The derivative of `Φ` is onto at every `θ`" | SAME | |
| `evalMixed_eq_eval_mixedToResidual` | A.5 (i), (ii) `F_θ = F^res_{Φ(θ)}` | SAME | |
| `image_evalMixed_eq_range_residual` | A.5 (ii) "compute the same set of functions" | SAME | |
| `funDim_mixed_eq_funDim_residual` | A.5 (ii) "with the same functional dimension at `θ` and at `Φ(θ)`" | SAME | any blocks; tested |
| **`Residual/ExactReductionMixed.lean`** | | | |
| `cobMixed_one_eq_cob` | the map of A.9 is `T_{G,1}` | SAME | |
| `exists_cob_mixed_reads_eq_one` | A.9 (i), reads, without normalization, "Done at every hidden state" | PART | all in reads |
| `exists_cob_mixed_writes_eq_one` | A.9 (i), writes, without normalization | PART | all in writes |
| `exists_cob_mixed_reads_upperTriangular` | A.9 (i), RMSNorm `ε > 0`, reads | PART | all in reads; any `ε`, no invertibility (stronger there) |
| `exists_cob_mixed_writes_lowerTriangular` | A.9 (i), RMSNorm `ε > 0`, writes (lower triangular) | PART | all in writes; any `ε` |
| **`Residual/ExactReductionCount.lean`** | | | |
| `finrank_span_reads_eq_zero`, `finrank_span_writes_eq_zero` | A.9 (i) "removes `d_model²` … parameters per hidden state" | PART | all in reads or all in writes; injectivity needed |
| `finrank_span_reads_upperTriangular`, `finrank_span_writes_lowerTriangular` | A.9 (i) "respectively `d_model(d_model − 1)/2`" | PART | the same |
| **`Residual/GaugeFixLearned.lean`** (statements only) | | | |
| `learnedToResidual` | (12) "with the same formula for learned skips" | SAME | |
| `learnedToResidual_coe` | (12) for invertible skips; A.5 (i) for learned skips | SAME | |
| `learnedToResidual_one` | A.5 (ii) every residual parameter is `Φ` | SAME | |
| `learnedToResidual_eq_iff` | A.5 (ii) "without the `K_ℓ`", fibres | SAME | tested |
| `exists_hasFDerivAt_learnedToResidual_surjective` | derivative onto | SAME | |
| `eval_eq_eval_learnedToResidual` | `F = F^res_Φ` | SAME | |
| `image_eval_learned_eq_range_residual` | same set of functions | SAME | |
| `funDimLearned_eq_funDim_residual` | same functional dimension | SAME | in the weights and the skips; tested |
| **`Residual/GaugeFixBiases.lean`** (statements only) | | | |
| `Biases.mulSkipProd` | "`Φ` also sends `b_E` to `b_E Λ_0` and each write bias `b_write^ℓ` to `b_write^ℓ Λ_ℓ`, and keeps each read bias" | SAME | `b_D` kept |
| `evalMixedB` | mixed blocks with biases; "The identity units carry no biases of their own" | SAME | |
| `mixedToResidualB`, `learnedToResidualB` | `Φ` with biases | SAME | |
| `evalMixedB_cobMixed` | A.5 (i) "The maps `T_{G,K}` preserve the function", with biases | SAME | bias action not written in the paper |
| `evalMixedB_eq_evalB_mixedToResidualB`, `evalB_eq_evalB_learnedToResidualB` | Part (i) "with biases and a skip bias" | SAME | `k_ℓ` merged into `b_write^ℓ`: nothing lost |
| `mixedToResidualB_mix_one`, `learnedToResidualB_one` | every residual parameter is `Φ` | SAME | |
| `mixedToResidualB_eq_iff`, `learnedToResidualB_eq_iff` | fibres, "and for networks with biases" | SAME | tested |
| `exists_hasFDerivAt_mixedToResidualB_surjective`, `exists_hasFDerivAt_learnedToResidualB_surjective` | derivative onto | SAME | |
| `image_evalMixedB_eq_range_residual`, `image_evalB_learned_eq_range_residual` | same set of functions | SAME | |
| `funDimOf_evalMixedB_eq_funDimB_residual`, `funDimOf_evalB_learned_eq_funDimB_residual` | same functional dimension | SAME | tested (mixed and learned) |

Nothing false, vacuous or drifted. Four groups are PART: A.1 (iii) (no independence/dimension of the factors) and A.9 (i) with its count (no free choice of read or write per hidden state).

## For the authors of the paper

Nothing false, vacuous or drifted was found. Places where the paper's text leaves a step or a convention unwritten:

1. **Theorem A.5 (ii), "and for networks with biases".** The map `T_{G,K}` of (11) is defined on the weights only. For the fibres of `Φ` with biases to be the orbits of `T_{G,K}` with `G_L = I`, `T_{G,K}` must also send `b_E ↦ b_E G_0` and `b_write^ℓ ↦ b_write^ℓ G_ℓ` and keep `b_read^ℓ` and `b_D`; with the biases kept, `Φ(T_{G,K}(θ)) ≠ Φ(θ)` as soon as `b_E` or a write bias is nonzero. One clause after (11) ("With biases, `T_{G,K}` also sends …"), parallel to the clause after (12), would close this.
2. **Proposition A.9 (i), "Done at every hidden state".** The Lean statements for mixed blocks make all choices in reads or all in writes; the paper's proof ("one submatrix per hidden state") allows a free choice per hidden state. The paper is right (the changes at different hidden states touch different matrices), but if the free choice is meant, the formal statements do not yet cover it.
3. **Proposition A.1 (iii), "a network of mixed blocks one more copy of `GL(d_model)` per block".** The formalization states the group action and its commutation laws, not that the copies act independently; the paper does not argue the independence either (at a parameter with invertible `U_ℓ`, `U_ℓ K_ℓ = U_ℓ` forces `K_ℓ = I`, which would be the one-line argument).
4. **Theorem A.5 (ii), the functional dimension.** The paper's argument is the chain rule, which needs differentiable outputs; the Lean statements hold for any blocks in the convention that the derivative is `0` where the outputs are not differentiable. No change is needed; the paper may say "for any blocks" if it wants the stronger form.
5. **Theorem A.5 (ii) for learned skips and with biases** is "The same holds …" in one sentence; Lean states thirteen and seven separate statements, all of which our computation supports. The statements are still without proofs at `0e1bc98`.

## Corrections for `STATEMENTS.md`

1. Row of `Symmetry/MixedJunctions.lean`: add that (iii) is stated as the composition law and the commutation of the maps; that the factors act independently, and the dimension of the group of a network of mixed blocks, are not stated.
2. Row of `Residual/ExactReductionMixed.lean`: delete "(in work)" after `Symmetry/MixedJunctions.lean` (it is proved); add "with the chosen submatrices all in reads (the reads of the blocks and `D`) or all in writes (`E` and the writes of the blocks); a choice per hidden state between a read and a write is not stated".
3. Row of `Residual/ExactReductionCount.lean`: replace "one submatrix per hidden state" by "one submatrix per hidden state, all `L + 1` in reads (the reads of the blocks and `D`) or all in writes (`E` and the writes of the blocks)".
4. Row of `Residual/GaugeFixBiases.lean`: "`T_{G,K}` with `b ↦ b.cob G` preserves the function" is `evalMixedB_cobMixed` for mixed blocks; for learned skips with biases it is `evalB_cob` (`Symmetry/BiasesSymmetries.lean`): name it.
5. The list "Not yet compared": move `Network/Mixed.lean`, `Symmetry/MixedJunctions.lean`, `Residual/GaugeFixMixed.lean`, `Residual/GaugeFixLearned.lean`, `Residual/ExactReductionMixed.lean`, `Residual/ExactReductionCount.lean` and `Residual/GaugeFixBiases.lean` to the compared files, with this report (`lean-statement-audit-thirtythird-b-2026-11-25.md`): nothing false, vacuous or drifted; the statements of `GaugeFixLearned.lean` and `GaugeFixBiases.lean` compared at `0e1bc98`, before their proofs.

## What I could not check

- The proofs of `Residual/GaugeFixLearned.lean` and `Residual/GaugeFixBiases.lean`: at `0e1bc98` all twenty statements are `sorry` (by design); if the proving agent changes a statement, the verdicts above apply to the statements as quoted here, not to the new ones.
- The numeric checks are for tanh blocks without normalization, `L ≤ 2`, `d ≤ 3`; the statements are for any blocks. Non-differentiable blocks (the "any blocks" clause of the functional dimensions) were checked by reading the argument, not by computation.
- `STATEMENTS.md` was read only in the rows of the seven files and the list "Not yet compared".

Commit read at the end: `0e1bc98` (unchanged).
