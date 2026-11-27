STATUS: complete

# Thirty-fourth audit, part B, of Lean statements against the skips paper: Lemma A.26 with the Lie group; Proposition A.9 (i), a read or a write at each hidden state; Proposition A.1 (iii), the copies act independently (25 November 2026)

Commit read at the start: `c4a245c` of `/home/claude/lp` (branch `lean-plus`); at the end: `c4a245c` (unchanged).

Paper: `<scratchpad>/skips.txt` (Lemma A.26 and its proof; Theorem A.28 and its proof; Proposition A.1 and its proof; Proposition A.9 and its proof). Brief: `audit34b_brief_2026-11-25.md`, with the rules and form of `audit21a_brief_2026-11-24.md`. Earlier report read first: `ai_notes/lean-statement-audit-thirtythird-b-2026-11-25.md` (its checks 2 and 4).

Files of the subject: `SkipsLean/Dimension/RankCriterionLieGroup.lean` (5 theorems, 1 definition), `SkipsLean/Residual/ExactReductionChoice.lean` (6 theorems, 2 definitions), `SkipsLean/Symmetry/MixedJunctionsFree.lean` (2 theorems). None has `sorry` (checked by reading; see check 8 for the axioms).

## Part 1: checks

### 1. The Lie group and its action (`RankCriterionLieGroup.lean`) — by reading

Lean:

```lean
variable {EH : Type*} [NormedAddCommGroup EH] [NormedSpace ℝ EH] {MH : Type*}
  [TopologicalSpace MH] (I : ModelWithCorners ℝ EH MH) {H : Type*} [Group H]
  [TopologicalSpace H] [ChartedSpace MH H] [LieGroup I ∞ H] [MulAction H P']

(hact : ContMDiff (I.prod 𝓘(ℝ, P')) 𝓘(ℝ, P') ∞ fun p : H × P' => p.1 • p.2)
```

- **The notion.** A smooth action of a Lie group `H` on a manifold `M` is an action `H × M → M` (here `MulAction H P'`: `1 • η = η`, `(a b) • η = a • (b • η)`) that is a smooth map of the product manifold (Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 7, "Lie group actions"). `hact` is exactly that: `ContMDiff` of order `∞` (`C^∞`, under `open scoped ContDiff`) of `(a, η) ↦ a • η` from `H × P'` with the product model `I.prod 𝓘(ℝ, P')` to `P'` with its own model. `P'` is any finite-dimensional real normed space, the paper's `ℝ^{P'}` being one. The model `I` of `H` is any model with corners on any real normed space. SAME.
- **The omitted instance.** Every statement has `omit [LieGroup I ∞ H]` (and with it the `IsManifold I ∞ H` that `LieGroup` extends): the statements are about any group with a charted-space structure, the topology and the action satisfying `hact`. A Lie group in Mathlib's sense satisfies all remaining hypotheses, so each statement applies to the paper's situation by instantiation, and only gets more general. Nothing in the statements uses the smoothness of the multiplication or of the inverse (the proofs use only the chain rule for the orbit map `a ↦ a • η` at `1`). LEAN STRONGER (more general), true as stated (the file is proved; check 8 for the axioms).

- **Compiled** (copy `/home/claude/audit34b/Inst34b.lean`, after the full build had ended): `#check @orbitDim` shows that `orbitDim` takes no `LieGroup`, measurability or finite-dimensionality instance (only `Group H`, the topology, `ChartedSpace MH H`, `MulAction H P'`), so the statements with `omit [LieGroup I ∞ H]` are well formed; the `∞` of `hact` elaborates to `↑⊤`, the coercion of `⊤ : ℕ∞`, i.e. `C^∞` (not `C^ω`). For a concrete Lie group the hypothesis `hact` can be met: for the units `ℝˣ` (Mathlib's `ChartedSpace ℝ ℝˣ`, a Lie group) acting on `ℝ` by multiplication, `ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ fun p : ℝˣ × ℝ => p.1 • p.2` compiles (from `Units.contMDiff_val` and `ContMDiff.smul`).

Verdict: SAME as the paper's hypothesis, stated for a larger class of groups.

### 2. `orbitDim` against "the orbit `H · η` has dimension at least `k`" — by reading

Lean:

```lean
noncomputable def orbitDim (η : P') : ℕ :=
  Module.finrank ℝ (LinearMap.range (mfderiv I 𝓘(ℝ, P') (fun a : H => a • η) 1).toLinearMap)
```

- **For a smooth action of a Lie group, this is the dimension of the orbit.** Write `o(a) = a · η`. For every `b ∈ H`, `o ∘ L_b = τ_b ∘ o`, with `L_b` the left translation of `H` and `τ_b : η ↦ b · η` (both diffeomorphisms, as the multiplication of `H` and the action are smooth); so the rank of `Do(b)` equals the rank of `Do(1)` for every `b`: the orbit map has constant rank (the equivariant rank theorem). Its fibres are the cosets of the stabilizer `H_η`, a closed subgroup, hence a Lie subgroup, whose Lie algebra is the kernel of `Do(1)`; `o` factors through an injective immersion `H/H_η → ℝ^{P'}` whose image is `H · η`, of dimension `dim H − dim H_η = rank Do(1)`. (In Lee, *Introduction to Smooth Manifolds*, 2nd ed.: the equivariant rank theorem, Theorem 7.25, and the orbits of a smooth action, Proposition 21.7 and the homogeneous-space characterization in Chapter 21; the numbers are from memory, the argument is the one above.) So `orbitDim I η` is the paper's "dimension of the orbit" for the groups that the paper uses (products of `GL(d_model)`, `O(d_model)`, `CO(d_model)`, of changes of basis inside heads and of positive rescalings: Lie groups with finitely many components). The rank at `1` is the rank everywhere, so taking it at the identity loses nothing. SAME.
- **A caveat that does not touch the paper.** Mathlib's Lie groups need not be second countable. For a Lie group with uncountably many components the set `H · η` can be larger than `rank Do(1)` suggests: `ℝ` with the discrete topology (a Lie group of dimension `0`) acting by translations on `ℝ` has `orbitDim = 0`, while the orbit is the whole line. There Lean's hypothesis `k ≤ orbitDim` asks more than "the orbit, as a set, has dimension at least `k`", so the Lean lemma is weaker than a set-theoretic reading of the paper's sentence; for the paper's groups the two agree.
- **When `H` is not a Lie group.** The statements omit `LieGroup I ∞ H` (check 1). Then `orbitDim` is still defined: the rank of the derivative at `1`, read in the chart at `1`, of a map that `hact` makes smooth; it may differ from the dimension of the orbit. Example: `H = (ℝ, +)` with the single chart `a ↦ a^{1/3}` (a homeomorphism onto the model `ℝ`), acting by translations on `ℝ`; in the charts the action is `(u, η) ↦ u³ + η`, smooth, so `hact` holds, and `orbitDim = 0` (the derivative of `u ↦ u³ + η` at `0`), while the orbit is `ℝ`. (`H` is not a Lie group in this chart: the multiplication reads `(u, v) ↦ (u³ + v³)^{1/3}`.) This makes no statement false: every statement that mentions `orbitDim` assumes `hact`, uses `orbitDim` only through `k ≤ orbitDim`, and is proved; a smaller `orbitDim` only makes the hypothesis harder to meet. No statement is vacuous: all hypotheses hold for the trivial group with `k = 0` and for a genuine Lie group action (for example `ℝ` acting by translation along one coordinate of `ℝ^{P'}`, `orbitDim = 1` at every `η`).
- **An infinite-dimensional model.** If `EH` is infinite-dimensional, the range of `Do(1)` is still a subspace of the finite-dimensional `P'`, so `orbitDim ≤ dim P'` and the rank-nullity step is unchanged; the statements stay true (proved) and meaningful.
- `mfderiv` is `0` where the map is not differentiable; `hact` makes the orbit map smooth, so wherever `orbitDim` is used it is the true derivative.

Verdict: SAME for the paper's groups; for other groups `orbitDim` is the rank of the orbit map at the identity, which is what the proof uses. Nothing false or vacuous.

### 3. The two steps of the proof (`finrank_range_fderiv_add_orbitDim_le`, `finrank_range_fderiv_le_of_ae`, `finrank_range_fderiv_add_le_of_ae_orbitDim`) — by reading, and by an argument

Lean (statements):

```lean
theorem finrank_range_fderiv_add_orbitDim_le (G : P' → Y)
    (hact : ContMDiff (I.prod 𝓘(ℝ, P')) 𝓘(ℝ, P') ∞ fun p : H × P' => p.1 • p.2)
    (hinv : ∀ (a : H) (η : P'), G (a • η) = G η) (η : P') (hG : DifferentiableAt ℝ G η) :
    Module.finrank ℝ (LinearMap.range (fderiv ℝ G η).toLinearMap) + orbitDim I (H := H) η
      ≤ Module.finrank ℝ P'

theorem finrank_range_fderiv_le_of_ae (G : P' → Y) (hG : ContDiff ℝ 1 G) (r₀ : ℕ)
    (ν : Measure P') [ν.IsAddHaarMeasure]
    (h : ∀ᵐ η ∂ν, Module.finrank ℝ (LinearMap.range (fderiv ℝ G η).toLinearMap) ≤ r₀) (η : P') :
    Module.finrank ℝ (LinearMap.range (fderiv ℝ G η).toLinearMap) ≤ r₀

theorem finrank_range_fderiv_add_le_of_ae_orbitDim (G : P' → Y) (hG : ContDiff ℝ 1 G)
    (hact : …) (hinv : …) (k : ℕ)
    (ν : Measure P') [ν.IsAddHaarMeasure] (horbit : ∀ᵐ η ∂ν, k ≤ orbitDim I (H := H) η)
    (η : P') :
    Module.finrank ℝ (LinearMap.range (fderiv ℝ G η).toLinearMap) + k ≤ Module.finrank ℝ P'
```

- **First step.** "At generic `η` the map `G_X` is constant along the orbit `H · η`, since `G_{a·η} = G_η`, and this orbit has dimension at least `k`. So the Jacobian of `G_X` has rank at most `r_0 = P' − k`." Lean states it at one `η`, with the sum `rank DG(η) + orbitDim(η) ≤ dim P'` in place of a subtraction: `G ∘ o` is constant, so `DG(η) ∘ Do(1) = 0`, the range of `Do(1)` lies in the kernel of `DG(η)`, and rank–nullity gives the sum. True. The hypothesis `hG` (differentiability at `η`) is not needed for the truth of the statement in Lean's convention: if `G` is not differentiable at `η`, then `fderiv ℝ G η = 0`, the rank is `0`, and `orbitDim η ≤ dim P'` holds anyway (the range lies in `P'`). It is harmless, and it is the hypothesis under which the sentence means what the paper means. SAME.
- **Second step.** "The rank is lower semicontinuous, so the bound holds at every `η`." Lean: for a `C¹` map, a bound on the rank of `DG` at almost every point, for an additive Haar measure, holds at every point. True: `{η : rank DG(η) > r₀}` is open (the rank of a linear map is lower semicontinuous, `DG` is continuous), null, hence empty (a Haar measure charges every nonempty open set). SAME. The paper's maps are analytic, hence `C¹`.
- **Which hypothesis it needs: an example, and where there is none.** For a map that is differentiable only at the point, the conclusion fails. Let `s : ℝ → ℝ` be the odd extension of the staircase that on each interval `[2^{−n−1}, 2^{−n}]` is the Cantor function rescaled onto each of `2^n` equal subintervals `[a, a + ℓ]`, `ℓ = 2^{−2n−1}`, with `s(a) = a` at their endpoints. It is continuous and nondecreasing, its derivative is `0` at almost every point (the Cantor function has derivative `0` almost everywhere), and `|s(x) − x| ≤ ℓ ≤ 2x²`, so `s` is differentiable at `0` with `s'(0) = 1`. With `r₀ = 0` and Lebesgue measure the hypothesis `h` holds (in Lean's convention the derivative is also `0` where `s` is not differentiable), and the conclusion fails at `η = 0`. For a map that is differentiable at **every** point, on the other hand, I find no counterexample, and the following argument shows there is none (in finite dimensions): if `rank DG(η₀) = r > r₀`, choose a linear `π` onto `ℝ^r` and an `r`-dimensional subspace `V` with `A = π DG(η₀)|_V` invertible, and look at the maps `g_w(v) = π G(η₀ + w + v)` on the slices `η₀ + w + V`. By Fubini, for almost every small `w` the derivative of `g_w` has rank `≤ r₀ < r` at almost every `v`, so `det Dg_w = 0` off a null set, and `g_w(B_ρ)` is null (Mathlib: `addHaar_image_eq_zero_of_det_fderivWithin_eq_zero` and `addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero`). But for `ρ` small, `|g_0(v) − g_0(0) − A v| ≤ σρ/4` on `B_ρ` (`σ` the smallest singular value of `A`), and for `w` small `|g_w − g_0| ≤ σρ/4` on `B_ρ`; for every `y` with `|y − g_0(0)| < σρ/4` the map `v ↦ v − A⁻¹(g_w(v) − y)` sends the closed ball `B_ρ` into itself, and Brouwer's fixed point gives `g_w(v) = y`. So `g_w(B_ρ)` contains a ball for every small `w`: a contradiction. So `C¹` is a convenient sufficient hypothesis, not the weakest one (everywhere differentiable suffices); this is a remark, not a defect.
- **The two together.** `finrank_range_fderiv_add_le_of_ae_orbitDim`: `C¹`, the smooth action, invariance, `k ≤ orbitDim` at almost every `η`, give `rank DG(η) + k ≤ dim P'` at every `η`. True: the first step at almost every `η` gives `rank ≤ P' − k` there, and `k ≤ P'` (the almost-everywhere set is nonempty, as `ν` is not zero); the second step propagates the bound. `hinv` is asked for all `a` and `η`, as in the paper. SAME.
- **The Haar measure.** "Generic" in the paper is "outside a set of Lebesgue measure zero" (`skips.txt` line 227). Any two additive Haar measures on a finite-dimensional real space are multiples of each other, so `∀ᵐ η ∂ν` does not depend on `ν`, and Lebesgue measure (`volume` on `Fin n → ℝ`) is one: SAME. (The second and third statements omit `[BorelSpace P']`; they hold for every measure with the Haar property on whatever σ-algebra `P'` carries, which only generalizes them.)

Verdict: SAME for the three statements; each is true as stated, with `C¹` (sufficient; differentiability at every point would do) and a Haar measure (the choice does not matter).

### 4. Parts (i) and (ii) (`ae_forall_ne_of_lieGroup_action`, `ae_exists_pos_le_norm_sub_of_lieGroup_action`) — by reading

Lean (part (ii); part (i) has the same hypotheses without `hcl` and the conclusion `∀ᵐ θ ∂μ, ∀ η : P', F θ ≠ G η`):

```lean
theorem ae_exists_pos_le_norm_sub_of_lieGroup_action
    (hSard : ∀ r : ℕ, SardCriticalValues P' (Fin r → ℝ))
    (F : P → In → Out) (G : P' → In → Out)
    (hF : ∀ x, AnalyticOnNhd ℝ (fun θ => F θ x) Set.univ)
    (hG : ∀ x, AnalyticOnNhd ℝ (fun η => G η x) Set.univ)
    (hact : ContMDiff (I.prod 𝓘(ℝ, P')) 𝓘(ℝ, P') ∞ fun p : H × P' => p.1 • p.2)
    (hinv : ∀ (a : H) (η : P'), G (a • η) = G η) (k : ℕ)
    (ν : Measure P') [ν.IsAddHaarMeasure] (horbit : ∀ᵐ η ∂ν, k ≤ orbitDim I (H := H) η)
    {n : ℕ} (X : Fin n → In)
    (hcl : ClosureNullOfNull (Set.range fun η : P' => fun i => G η (X i))) (θ₀ : P)
    (hθ₀ : Module.finrank ℝ P' < Module.finrank ℝ (LinearMap.range
      (fderiv ℝ (fun θ => fun i => F θ (X i)) θ₀).toLinearMap) + k)
    (μ : Measure P) [μ.IsAddHaarMeasure] :
    ∀ᵐ θ ∂μ, ∃ δ : ℝ, 0 < δ ∧ ∀ η : P', ∃ i, δ ≤ ‖F θ (X i) - G η (X i)‖
```

Clause by clause:

- **The two families.** `F : P → In → Out`, `G : P' → In → Out`: maps from any set of inputs `In` to a finite-dimensional real normed space `Out`, with parameters in finite-dimensional real normed spaces `P`, `P'`. The paper's maps `ℝ^{T × d_in} → ℝ^{T × d_out}` with parameters in `ℝ^P`, `ℝ^{P'}` are a case (with any norm on `ℝ^{T × d_out}`; Mathlib has no global norm on matrices, so an application chooses one, and all norms on a finite-dimensional space give the same statement up to the value of `δ`). LEAN STRONGER (more general).
- **"For every input `x`, `F_θ(x)` is real-analytic in `θ` and `G_η(x)` is real-analytic in `η`":** `hF`, `hG`, analytic on all of the parameter space. SAME.
- **The Lie group and its action, the invariance:** `hact`, `hinv` (check 1). SAME.
- **"The orbit has dimension at least `k` at generic `η`":** `k ≤ orbitDim η` for `ν`-almost every `η`, `ν` any additive Haar measure of `P'`. The paper's "generic" is "outside a set of Lebesgue measure zero"; the choice of `ν` does not matter (check 3). `orbitDim` is the dimension of the orbit for the paper's groups (check 2). SAME.
- **"At some `θ_0` the Jacobian of `θ ↦ (F_θ(x))_{x ∈ X}` has rank greater than `P' − k` on some finite batch `X`":** `X : Fin n → In` (a finite batch, repetitions allowed, which changes nothing), and `P' < rank + k` with `rank` the rank of the derivative at `θ₀` of the batch map (differentiable, as it is analytic, so this is the true Jacobian). For `k ≤ P'` this is `rank > P' − k`. For `k > P'` the paper's `P' − k` is negative and "rank greater than `P' − k`" always holds; Lean's `P' < rank + k` also always holds; and in both, `horbit` cannot hold (`orbitDim ≤ P'` and the almost-everywhere set is not empty), so the case is vacuous in both, the same way. SAME.
- **(i) "For almost every `θ`, no `η` satisfies `F_θ = G_η`":** `∀ᵐ θ ∂μ, ∀ η, F θ ≠ G η`, for any additive Haar measure `μ` of `P`, with `F θ ≠ G η` as maps on all of `In`. SAME.
- **(ii) "for almost every `θ` there is a `δ > 0` such that every `η` has `‖F_θ(x) − G_η(x)‖ ≥ δ` at some `x ∈ X`":** `∃ δ, 0 < δ ∧ ∀ η, ∃ i, δ ≤ ‖F θ (X i) − G η (X i)‖`. The order of the quantifiers is the paper's (`δ` depends on `θ` only, not on `η`). SAME.
- **Definability.** The paper's hypothesis "the outputs `G_η(x)`, `x ∈ X`, are definable functions of `η`" is replaced by `ClosureNullOfNull S` for `S = {(G_η(X_i))_i : η ∈ P'}`: for every `r` and every linear `π` onto `ℝ^r`, if `π(S)` is null then its closure is null (`Literature/OMinimal.lean`). The paper's proof of (ii) uses definability once: "The image `π(S)` of `π ∘ G_X` is definable and has measure zero, so its closure has measure zero (Lemma A.23)". If the outputs are definable functions of `η` in an o-minimal expansion of the real field, `S` is definable (the image of a definable map), `π(S)` is definable for every linear `π` (linear maps with real coefficients are definable, as the structure contains the graphs of `+`, `·` and every point), and Lemma A.23 gives the closure. So the paper's hypothesis implies `hcl`, and `hcl` is exactly what the proof uses. SAME (given the literature).
- **Sard's theorem as a hypothesis.** `hSard : ∀ r, SardCriticalValues P' (Fin r → ℝ)`: for every Haar measure on `ℝ^r` and every real-analytic `g : P' → ℝ^r`, the image of the points where `Dg` is not onto is null (`Literature/Sard.lean`). This is a true theorem (Sard 1942; an analytic map is `C^∞`), so the hypothesis restricts nothing; it is what the paper's proof cites ("by Sard's theorem its image has measure zero"). It is not an axiom.

**Is the lemma now stated in full?** Yes: with the two hypotheses from the literature (`hSard`, and `hcl` in place of definability), `ae_forall_ne_of_lieGroup_action` and `ae_exists_pos_le_norm_sub_of_lieGroup_action` are Lemma A.26 (i) and (ii) clause by clause, for more general families and groups. None of the 13 theorems is used yet by another file of the library (searched: the names occur only in their own files and in `STATEMENTS.md` / `checks/Axioms.lean`); Theorem A.28, which applies the lemma, is not stated with them.

Verdict: SAME for (i) and SAME for (ii) (LEAN STRONGER in generality: any inputs, any finite-dimensional values, any group with a charted structure).

### 5. A read or a write at each hidden state (`ExactReductionChoice.lean`) — by reading, and by a computation

Lean (definitions and two of the six statements):

```lean
def Params.readSub (θ : Params A dIn dOut) (c : ∀ ℓ : Fin L, d → A.r ℓ) (cD : d → dOut)
    (k : Fin (L + 1)) : Matrix d d ℝ :=
  Fin.lastCases (motive := fun _ => Matrix d d ℝ) (θ.D.submatrix id cD)
    (fun ℓ => (θ.read ℓ).submatrix id (c ℓ)) k

def Params.writeSub (θ : Params A dIn dOut) (ρE : d → dIn) (ρ : ∀ ℓ : Fin L, d → A.w ℓ)
    (k : Fin (L + 1)) : Matrix d d ℝ :=
  Fin.cases (motive := fun _ => Matrix d d ℝ) (θ.E.submatrix ρE id)
    (fun ℓ => (θ.write ℓ).submatrix (ρ ℓ) id) k

theorem exists_cob_eq_one_of_choice (hA : A.χ = id)
    (c : ∀ ℓ : Fin L, d → A.r ℓ) (cD : d → dOut) (ρE : d → dIn) (ρ : ∀ ℓ : Fin L, d → A.w ℓ)
    (s : Fin (L + 1) → Bool)
    (h : ∀ k, IsUnit (if s k then θ.readSub c cD k else θ.writeSub ρE ρ k).det) :
    ∃ G : Fin (L + 1) → GL d ℝ,
      (∀ x : Matrix T dIn ℝ, eval A 0 (θ.cob G G) x = eval A 0 θ x) ∧
      ∀ k, (if s k then (θ.cob G G).readSub c cD k else (θ.cob G G).writeSub ρE ρ k) = 1

theorem finrank_span_choice_eq_zero (c …) (cD …) (ρE …) (ρ …) (s : Fin (L + 1) → Bool)
    (hc : ∀ ℓ : Fin L, s ℓ.castSucc = true → Function.Injective (c ℓ))
    (hcD : s (Fin.last L) = true → Function.Injective cD)
    (hρE : s 0 = false → Function.Injective ρE)
    (hρ : ∀ ℓ : Fin L, s ℓ.succ = false → Function.Injective (ρ ℓ)) :
    Module.finrank ℝ (Submodule.span ℝ {η : Params A dIn dOut |
        ∀ k, (if s k then η.readSub c cD k else η.writeSub ρE ρ k) = 0})
      + (L + 1) * Fintype.card d ^ 2
      = Module.finrank ℝ (Params A dIn dOut)
```

- **The indices.** In `Params.cob G K` (`Symmetry/ChangeOfBasis.lean`) the read of block `ℓ : Fin L` is multiplied on the left by `(K ℓ.castSucc)⁻¹`, its write on the right by `G ℓ.succ`, `E` by `G 0`, `D` by `(K (Fin.last L))⁻¹`: block `ℓ` (0-based) reads `h_ℓ` and writes `h_{ℓ+1}`. `readSub … k` is, for `k = ℓ.castSucc`, the chosen columns of `read ℓ`, the matrix that reads `h_k` (the paper's read of block `k + 1`), and for `k = L` those of `D`, the readout, which reads `h_L`. `writeSub … k` is, for `k = 0`, the chosen rows of `E`, and for `k = ℓ.succ` those of `write ℓ`, the matrix that writes `h_k` (block `k`). So at each `k` the chosen submatrix lies in a matrix that reads or writes `h_k`, and the change at `h_k` multiplies it by `G_k⁻¹` on the left (read) or `G_k` on the right (write). Correct. (The paper's "a matrix that reads `h_ℓ`" could also be read as any of several reads of `h_ℓ`; in the networks of the paper each hidden state has one read, the next block's or the readout, and one write, so nothing is lost.)
- **The choice** `s : Fin (L + 1) → Bool`, `true` for a read, `false` for a write: every pattern of reads and writes across the `L + 1` hidden states. This is the paper's "one submatrix per hidden state", which the earlier statements covered only for all reads or all writes (thirty-third audit B, check 4). SAME.
- **`exists_cob_eq_one_of_choice`.** Invertibility is asked only of the chosen submatrix at each hidden state (`h k` with `if s k then … else …`), as in the paper ("Let `W_1` be an invertible … submatrix"); `G_k = W_1` for a read and `W_1⁻¹` for a write (from the proof), the function preserved for every input (`eval A 0`, the skipless network, `χ = id`), and every chosen submatrix becomes `I`. SAME.
- **`exists_cob_triangular_of_choice`.** Under `χ = rmsNorm ε`, orthogonal `Q_k`, the function preserved, upper triangular for the columns of a read (`BlockTriangular id`: the entries `(i, j)` with `j < i` vanish), lower triangular for the rows of a write (the transpose is upper triangular): the paper's "`G = Q` from a QR factorization `W_1 = Q T`, or `W_1^⊤ = Q T` for a write" and the proof's "`W_1 Q = T^⊤`, which is lower triangular". Lean asks no invertibility (a QR factorization exists for every square matrix) and allows every `ε` (the paper: `ε > 0`; for `ε = 0` the orthogonal changes are among the paper's `CO(d_model)`, and for every `ε` an orthogonal `Q` commutes with `rmsNorm ε`). LEAN STRONGER, true.
- **Mixed blocks** (`exists_cob_mixed_eq_one_of_choice`, `exists_cob_mixed_triangular_of_choice`): the same with `c ℓ : d → d ⊕ A.r ℓ` (columns of the read `[U_ℓ | W_read^ℓ]`, from `U_ℓ`, from `W_read^ℓ` or from both), `ρ ℓ : d → d ⊕ A.w ℓ` (rows of the write that stacks `V_ℓ` on `W_write^ℓ`), `E` and `D`; the change is `θ.cob G G` of the architecture `A.mixed`, which is `T_{G,1}` (`cobMixed_one_eq_cob`): the reads `U_ℓ` and `W_read^ℓ` get `G_{ℓ−1}⁻¹`, the writes `V_ℓ` and `W_write^ℓ` get `G_ℓ`. The function is `evalMixed`, the paper's (9) or (10). SAME (and LEAN STRONGER for the triangular form, as above).
- **The counts.** Each set is the kernel of a linear map of the parameters (the chosen entries, resp. the entries below the diagonal of the chosen columns and above the diagonal of the chosen rows), so it is a subspace and the `Submodule.span` is the set itself. The chosen submatrices at different hidden states lie in different matrices (each matrix reads or writes one hidden state only), so with distinct columns (rows) the map is onto and the codimensions add: `P − (L + 1) d²` and `P − (L + 1) d(d − 1)/2`. With the existence statements: every `θ` with invertible chosen submatrices has the function of a parameter in the affine set "chosen submatrices `= I`", a translate of the first subspace, of dimension `P − (L + 1) d²`; and every `θ` has the function of a parameter in the second subspace, of dimension `P − (L + 1) d(d − 1)/2`. This is "removes `d_model²`, respectively `d_model (d_model − 1)/2`, parameters per hidden state without changing the function". Injectivity is asked only where the choice uses it (`hc` only when `s ℓ.castSucc`, …). It is needed for the identity form (two equal columns fix fewer entries); for the triangular form it is needed for `d ≥ 3` and not for `d = 2` (see the computation). The two counts are stated for any architecture (`d : Type*`), so also for `A.mixed`. SAME.
- **Computation** (`/home/claude/audit34b/check34b.py`, output `check34b.out`): `L = 2`, `d = 2`, `d_in = d_out = 3`, three hidden units per block, tanh, four tokens, the choice of the brief (a read at `h_0`, a write at `h_1`, a read at `h_2`, the last in `D`). Skipless without normalization: `G_0 = W_1` (two columns of the first read), `G_1 = W_1⁻¹` (two rows of the first write), `G_2 = W_1` (two columns of `D`); after the change the three chosen submatrices are `I` to `2.3·10⁻¹⁶`, the function moves by `4·10⁻¹⁶` on 20 inputs, and the second read, not chosen, changes by `1.8`. Under pre-RMSNorm with `ε = 0.1` and `ε = 0`: `G_k = Q` from the QR factorizations, orthogonal to `4·10⁻¹⁶`; the read submatrices come out upper triangular and the write submatrix lower triangular (fixed entries `≤ 3·10⁻¹⁶`), function moved by `≤ 2·10⁻¹⁴`. Mixed blocks, with a chosen column of `U_1` and one of `W_read^1`, a row of `V_1` and one of `W_write^1`: `I` to `10⁻¹⁶` without normalization, triangular under RMSNorm, function moved by `≤ 10⁻¹⁴`. The counts, as the rank of the map to the fixed entries (`d_in = d_out = 4`, four units, `L = 2`): `d = 2`: `P = 48`, ranks 12 and 3, so dimensions 36 and 45; `d = 3`: `P = 72`, ranks 27 and 9, dimensions 45 and 63: `P − (L+1)d²` and `P − (L+1)d(d−1)/2`. A repeated column at a read that the choice uses: rank 10 (instead of 12) and 21 (instead of 27) for the identity form, 3 (= 3) for the triangular form at `d = 2` and 8 (instead of 9) at `d = 3`; a repeated column at a read that the choice does not use leaves the rank at `(L+1)d²`.

Verdict: SAME for the reduction to `I` and the counts; LEAN STRONGER for the triangular reduction (any `ε`, no invertibility); the choice per hidden state is now stated.

### 6. The copies act independently (`MixedJunctionsFree.lean`) — by reading, and by a computation

Lean:

```lean
theorem cobMixed_injective (θ : Params A.mixed dIn dOut) (hE : θ.E.rank = Fintype.card d)
    (hU : ∀ ℓ, IsUnit (θ.mixU ℓ)) (hV : ∀ ℓ, IsUnit (θ.mixV ℓ))
    {G Q G' Q' : Fin (L + 1) → GL d ℝ} {K K' : Fin L → GL d ℝ}
    (h : θ.cobMixed G Q K = θ.cobMixed G' Q' K') : G = G' ∧ K = K'

theorem cobMixed_eq_self_iff (θ : Params A.mixed dIn dOut) (hE : θ.E.rank = Fintype.card d)
    (hU : ∀ ℓ, IsUnit (θ.mixU ℓ)) (hV : ∀ ℓ, IsUnit (θ.mixV ℓ))
    (G : Fin (L + 1) → GL d ℝ) (K : Fin L → GL d ℝ) :
    θ.cobMixed G G K = θ ↔ G = 1 ∧ K = 1
```

with `θ.cobMixed G Q K`: `E G_0`, `U_ℓ ↦ G_{ℓ−1}⁻¹ U_ℓ K_ℓ`, `V_ℓ ↦ K_ℓ⁻¹ V_ℓ G_ℓ`, `W_read^ℓ ↦ Q_{ℓ−1}⁻¹ W_read^ℓ`, `W_write^ℓ ↦ W_write^ℓ G_ℓ`, `D ↦ Q_L⁻¹ D` (thirty-third audit B, check 2).

- **`cobMixed_injective` is true.** `E G_0 = E G'_0` with `E` of full column rank `d` gives `G_0 = G'_0`; then `G_0⁻¹ U_1 K_1 = G_0⁻¹ U_1 K'_1` with `U_1` invertible gives `K_1 = K'_1`; then `K_1⁻¹ V_1 G_1 = K_1⁻¹ V_1 G'_1` with `V_1` invertible gives `G_1 = G'_1`; and so on to `G_L`. The `Q_ℓ` appear only on the reads through the normalization and on `D`, so equal parameters say nothing about them in general (with `W_read = 0` and `D = 0` they are free), and the statement rightly concludes nothing about `Q`, `Q'`; in each case of normalization the network's `Q` is a function of `G` (`Q = G`, or `Q_ℓ = G_ℓ / c_ℓ` for `ε = 0`), so `(G, K)` determines the whole map. Right.
- **Each hypothesis is needed** (with the others kept): exact examples with `d = 1`, `L = 1`, `W_write^1 = 0` (`check34b.py`): `E = 0`: `(G, K) = ((1, 1), 1)` and `((2, 2), 2)` give the same parameter; `U_1 = 0`: `((1, 1), 1)` and `((1, 2), 2)`; `V_1 = 0`: `((1, 1), 1)` and `((1, 2), 1)`; distance `0` in each case, with `Q = Q' = 1`. They are sufficient, not necessary: in each example a write `W_write^1` of full column rank makes the two parameters differ again (distance `2`), as `W_write^ℓ G_ℓ` then determines `G_ℓ`. The hypotheses hold at almost every parameter when `d_in ≥ d_model` (the paper's "E of rank `d_model`"); for `d_in < d_model` the statement never applies, although the action can still be free through the writes. This is a restriction of Lean's statement, not a defect against the paper, whose sentence has no hypothesis and is not about a particular `θ`.
- **`cobMixed_eq_self_iff`:** with `Q = G` (the network without normalization, or under RMSNorm with `ε > 0`), only the identity fixes `θ`: the stabilizer is trivial. True (from the injectivity and `T_{1,1} = id`).
- **Is the last sentence of (iii) now stated?** "A skipless network therefore carries one copy of `𝒢` per hidden state, and a network of mixed blocks one more copy of `GL(d_model)` per block." With `cobMixed_cobMixed` (the composition law: a right action of `GL(d)^{L+1} × GL(d)^{L+1} × GL(d)^L`), `cobMixed_comm` and `cobMixed_mixK_comm` (commutation), and the invariance statements of `Symmetry/MixedJunctions.lean`, the new statements say that at a parameter with `E` of rank `d` and invertible `U_ℓ`, `V_ℓ` the orbit map `(G, K) ↦ T_{G,K}(θ)` is injective, so the group `GL(d)^{L+1} × GL(d)^L` acts faithfully, one independent factor per junction. That is the sentence for networks of mixed blocks, in the sense of "independent copies". What is still not stated: (a) a dimension: that the orbit is a manifold of dimension `(2L + 1) d²` (the derivative of the orbit map at the identity is injective). Injectivity of the orbit map does not give it. Computed (`check34b.py`, complex-step derivative of the orbit map at the identity, random parameters): `d = 2, L = 1`: 12 singular values in `[1.28, 4.69]`, rank 12 = `3 d²`; `d = 2, L = 2`: rank 20 = `5 d²` (smallest singular value `0.72`); `d = 3, L = 2`: rank 45 = `5 d²` (smallest `0.37`); full rank, no gap to a zero cluster. So the dimension is `(2L + 1) d²` at these parameters, but no Lean statement says so for mixed blocks. (b) For skipless networks the "one copy of `𝒢` per hidden state" is in the library, not in these files: the trivial stabilizer, `cob_eq_self_of_rank_E` (`Symmetry/LocallyFreeEmbedding.lean`: if `E` and every write have rank `d` and `θ.cob G K = θ`, then `G = 1`), with its twin for `D` (`cob_eq_self_of_rank_D`, `Symmetry/LocallyFreeReadout.lean`), the forms with the symmetries inside blocks and for `ε = 0` (`Symmetry/LocallyFreeRMSZero.lean`), and the forms at almost every parameter (`ae_cob_eq_self_of_dIn` and the others of `Symmetry/LocallyFreeGeneric.lean`, `Symmetry/LocallyFreeRMSZeroGeneric.lean`); and the dimension of the group, `dimH_cobPreservingMat_skipless` and `dimH_cobPreservingMat_skipless_rmsNorm` (`Symmetry/CobGroup.lean`: the families of changes of basis that preserve the function at all parameters form a set of Hausdorff dimension `(L + 1) d²`, resp. `(L + 1) d(d − 1)/2`; that is Theorem 3.3 (ii), the group, not an orbit). For mixed blocks there is no `cobPreservingMat` and no dimension statement (the index says so, row of `Symmetry/MixedJunctions.lean`). Verdict for the last sentence of (iii): SAME for mixed blocks in the sense of independent (faithfully acting) copies; PART if "carries one copy" is read as a count of dimensions, which for mixed blocks is computed here, not stated.

Verdict: `cobMixed_injective` SAME (with sufficient hypotheses, each needed); `cobMixed_eq_self_iff` SAME.

### 7. Drift checks — by reading

- **"Generic" is "for almost every".** The only "generic" of the subject is the hypothesis on the orbits in Lemma A.26: `∀ᵐ η ∂ν, k ≤ orbitDim I η` for an additive Haar measure `ν`, which is the paper's "outside a set of Lebesgue measure zero" (line 227), for every choice of `ν` (check 3). The conclusions are `∀ᵐ θ ∂μ` for any Haar measure `μ` of `P`: the paper's "for almost every `θ`". No drift.
- **Hypotheses not in the paper.** `RankCriterionLieGroup.lean`: `hSard` and `hcl` (from the literature: Sard's theorem, true; `hcl` implied by the paper's definability, check 4); `C¹` in the two steps (implied by the paper's analyticity); `hG` in the first step (not needed, check 3). `ExactReductionChoice.lean`: `[LinearOrder d]` for the triangular forms (it fixes the order in which "triangular" is read; any order of the `d` coordinates may be chosen); injectivity of the chosen columns or rows in the counts, only where the choice uses them (implied by the paper's invertibility). `MixedJunctionsFree.lean`: `E` of rank `d` and `U_ℓ`, `V_ℓ` invertible (the paper's sentence has no hypothesis; these hold at almost every parameter when `d_in ≥ d_model`, and each is needed for the statement as written, check 6). None of these excludes a case that the paper's sentence covers and uses, except that `cobMixed_injective` says nothing at parameters with `rank E < d` (always when `d_in < d_model`).
- **The paper's hypotheses not in Lean.** Lemma A.26: "Lie group" is weakened to a group with a charted structure (more general; check 1). Proposition A.9 (i): "`ε > 0`" and "invertible" for the triangular form are dropped (more general; check 5). Nothing of the paper is missing.
- **Over-generality that could make something false:** none found; all 13 theorems are proved and use only the three standard axioms (check 8).

Verdict: no drift.

### 8. The index rows, the registrations and the axioms — by reading, and by compiling a copy

- **Rows of the three files** (`STATEMENTS.md`). Row of `Dimension/RankCriterionLieGroup.lean` (line 877): true of the statements; one phrase is loose: "the statements are for every group on a manifold" — they are for every group with a topology and a charted-space structure, not necessarily a manifold (the omitted `LieGroup` instance carries `IsManifold`). Row of `Symmetry/MixedJunctionsFree.lean` (line 1056): true. Row of `Residual/ExactReductionChoice.lean` (line 1062): true; "if the chosen columns (rows) are pairwise different" is asked only where the choice uses them, and the triangular forms ask no invertibility.
- **Rows that point to these files.** `Dimension/RankCriterion.lean` (line 876: "for a Lie group, with the lemma in the paper's form, in `Dimension/RankCriterionLieGroup.lean`"), `Symmetry/MixedJunctions.lean` (line 1055: "that the factors act independently is in `Symmetry/MixedJunctionsFree.lean`; no dimension of a group is stated for networks of mixed blocks"), `Residual/ExactReductionMixed.lean` (line 1060) and `Residual/ExactReductionCount.lean` (line 1061: "a read or a write at each hidden state: `Residual/ExactReductionChoice.lean`"): each pointer is true.
- **"Not yet compared"** (lines 383 to 385) still lists `Dimension/RankCriterionLieGroup.lean`, `Residual/ExactReductionChoice.lean` and `Symmetry/MixedJunctionsFree.lean`; after this report they are compared.
- **Registrations.** All 13 theorems are in `checks/Axioms.lean` (lines 2204 to 2208 and 2238 to 2245); the three modules are imported in `SkipsLean.lean` (lines 404 to 406).
- **Axioms.** After the full build had ended (`pgrep -f "lake build"` printed nothing; its log ends with `build exit 0`), a copy `/home/claude/audit34b/Ax34b.lean` with `#print axioms` for the 13 theorems, compiled with `lake env lean` (output `Ax34b.out`): every one depends on `[propext, Classical.choice, Quot.sound]` only. No `sorry` in the three files.

Verdict: the rows are true; two small corrections and the "not yet compared" list below.

## Part 2: the statements, file by file

| Lean | Paper | Verdict | Note |
|---|---|---|---|
| `orbitDim` | Lemma A.26, "the orbit `H · η` has dimension" | SAME | rank of the orbit map at `1`; the dimension of the orbit for a smooth action of a Lie group with countably many components (constant rank); for other groups the rank that the proof uses |
| `finrank_range_fderiv_add_orbitDim_le` | proof of A.26, "`G_X` is constant along the orbit […] rank at most `P' − k`" | SAME | at one `η`, as a sum; `hG` not needed in Lean's convention |
| `finrank_range_fderiv_le_of_ae` | proof of A.26, "the rank is lower semicontinuous, so the bound holds at every `η`" | SAME | `C¹` and any Haar measure; fails for a map differentiable only at the point (a staircase), holds for one differentiable everywhere |
| `finrank_range_fderiv_add_le_of_ae_orbitDim` | the two sentences together | SAME | |
| `ae_forall_ne_of_lieGroup_action` | Lemma A.26 (i) | SAME (LEAN STRONGER in generality) | any inputs, finite-dimensional values, any group with a charted structure; Sard's theorem as a hypothesis |
| `ae_exists_pos_le_norm_sub_of_lieGroup_action` | Lemma A.26 (ii) | SAME (LEAN STRONGER in generality) | definability replaced by `ClosureNullOfNull`, which it implies and which is what the proof uses |
| `Params.readSub`, `Params.writeSub` | Proposition A.9, "`d_model` columns of a matrix that reads `h_ℓ`, or `d_model` rows of a matrix that writes it" | SAME | indices checked against `Params.cob` |
| `exists_cob_eq_one_of_choice` | A.9 (i), skipless, identity, "one submatrix per hidden state" | SAME | invertibility only of the chosen submatrices |
| `exists_cob_triangular_of_choice` | A.9 (i), skipless, RMSNorm, QR | LEAN STRONGER | every `ε`, no invertibility |
| `finrank_span_choice_eq_zero` | A.9 (i), "removes `d_model²` … per hidden state" | SAME | subspace; injectivity where used, needed |
| `finrank_span_choice_triangular` | A.9 (i), "respectively `d_model(d_model − 1)/2`" | SAME | injectivity needed for `d ≥ 3`, not for `d = 2` |
| `exists_cob_mixed_eq_one_of_choice` | A.9 (i), mixed blocks, identity | SAME | columns of `[U_ℓ \| W_read^ℓ]`, rows of `V_ℓ` over `W_write^ℓ` |
| `exists_cob_mixed_triangular_of_choice` | A.9 (i), mixed blocks, RMSNorm | LEAN STRONGER | every `ε`, no invertibility |
| `cobMixed_injective` | A.1 (iii), "one more copy of `GL(d_model)` per block" (independent copies) | SAME at the parameters it covers | `E` of rank `d`, `U_ℓ`, `V_ℓ` invertible: each needed as written, all generic for `d_in ≥ d_model`; not a dimension |
| `cobMixed_eq_self_iff` | the same, trivial stabilizer | SAME | `Q = G` |

## For the authors of the paper

1. **Nothing false, vacuous or drifted** in the 13 statements; the three sentences that they formalize (Lemma A.26 in full, Proposition A.9 (i) with a free choice per hidden state, the independence of the copies in Proposition A.1 (iii)) are now stated.
2. **Lemma A.26, "the orbit has dimension at least `k`".** For the groups of the paper this is the rank of the orbit map `a ↦ a · η` (constant on `H`), which is what the proof uses. If the paper wants to be exact for any Lie group, it may say "the orbit map has rank at least `k`" (for a Lie group with uncountably many components, such as `ℝ` with the discrete topology, the set `H · η` can have larger dimension than this rank). No change is needed for the paper's uses.
3. **Lemma A.26, "the rank is lower semicontinuous, so the bound holds at every `η`".** This uses that the Jacobian of `G_X` is continuous (true, as `G_X` is analytic). For a map that is only differentiable at the point the step fails (check 3); for a map differentiable everywhere it still holds, by another argument. Nothing to change.
4. **Proposition A.1 (iii).** The copies act independently at a parameter where `E` has rank `d_model` and every `U_ℓ`, `V_ℓ` is invertible (or where the writes have rank `d_model`); at some parameters (for example `E = 0` and `W_write = 0`) they do not. The paper's sentence is about the group, and is right; if it is read as a statement at a parameter, "at generic parameters with `d_in ≥ d_model`" is the condition. The dimension of the orbit, `(2L + 1) d_model²` without normalization, is computed here at random parameters, not stated in Lean.
5. **Proposition A.9 (i), the triangular form.** It holds for every `ε` (also `ε = 0`, with orthogonal `G`) and for every `W_1`, invertible or not; the paper says `ε > 0` and lets `W_1` be invertible. The paper may keep its wording.

## Corrections for `STATEMENTS.md`

1. Lines 383 to 385 ("Not yet compared"): remove `Dimension/RankCriterionLieGroup.lean`, `Residual/ExactReductionChoice.lean` and `Symmetry/MixedJunctionsFree.lean`, and add: "A thirty-fourth reader (part B, 25 November) compared `Dimension/RankCriterionLieGroup.lean`, `Residual/ExactReductionChoice.lean` and `Symmetry/MixedJunctionsFree.lean` (13 theorems): nothing false, vacuous or drifted; Lemma A.26 is stated in full with Sard's theorem and `ClosureNullOfNull` as hypotheses; the triangular reductions are stronger than the paper (every `ε`, no invertibility) (`ai_notes/lean-statement-audit-thirtyfourth-b-2026-11-25.md`)."
2. Row of `Dimension/RankCriterionLieGroup.lean` (line 877): "so the statements are for every group on a manifold and omit the instance" → "so the statements are for every group with a topology and a charted-space structure (not necessarily a manifold) and omit the instance"; after "the orbit is not built as a manifold" add "; for a smooth action of a Lie group the orbit map has constant rank and this rank is the dimension of the orbit"; "for a Haar measure" → "for any Haar measure (the choice does not matter)".
3. Row of `Symmetry/MixedJunctionsFree.lean` (line 1056): add "The hypotheses hold at almost every parameter when `d_in ≥ d`; each is needed for the statement as written; no dimension of the orbit is stated".
4. Row of `Residual/ExactReductionChoice.lean` (line 1062): "under pre-RMSNorm (any `ε`)" → "under pre-RMSNorm (any `ε`, no invertibility)"; "if the chosen columns (rows) are pairwise different" → "if the chosen columns (rows) are pairwise different where the choice uses them".

## What I could not check

- The theorem numbers in Lee's book are from memory; the argument for "rank of the orbit map = dimension of the orbit" is given in check 2.
- The argument that the second step of check 3 holds for maps differentiable at every point is a proof sketch by me, not formalized or checked by a computation.
- No file of the library applies the two families theorems to networks (Theorem A.28 is formalized through `Residual/SkiplessEnds.lean` and `Residual/SkiplessAll.lean` with the bound on the rank proved for each family), so I could not check an application; I compiled only that `hact` can be met for a concrete Lie group (`ℝˣ` on `ℝ`), not the value of `orbitDim` there.
- The proofs are not audited (the subject is the statements).
