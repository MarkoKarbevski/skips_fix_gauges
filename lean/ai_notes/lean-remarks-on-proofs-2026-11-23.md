# What the formalization needed beyond the papers' proofs

For the authors. One entry per proof that was formalized with more detail than the paper gives.
None of the entries so far is a gap: each says what the Lean proof had to spell out. Statement
numbers are those of the PDFs of 22 November 2026; "D" is the dimension paper.

## D Lemma C.3, the case of tanh (formalized 23 November 2026, `OneBlock/UnitsTanh.lean`)

1. **The direction of the ray.** The paper: "start from a point of the hyperplane n c_j = 0 where
   no other n c_k vanishes, and move a little to the side s". The existence of such a point is not
   argued. The Lean proof uses three facts: c_j ≠ 0; pairwise non-collinearity, which makes
   r_k = c_k − (c_j·c_k / c_j·c_j) c_j nonzero for k ≠ j; and that a real vector space is not a
   finite union of proper subspaces, which gives ν with ν·r_k ≠ 0 for all k ≠ j. Then
   ν₀ = ν − (ν·c_j / c_j·c_j) c_j lies on the hyperplane and ν₀·c_k = ν·r_k ≠ 0.
2. **"A polynomial of degree one in t tends to zero, so both of its coefficients vanish."** In Lean
   this is two limits, in this order: with the weight e^{2|u_j|t}/t the coefficient of t, then with
   the weight e^{2|u_j|t} the constant coefficient. With the second weight alone the term in t has
   no limit until the first coefficient is known to vanish.
3. **The bounds on tanh.** The paper uses tanh z = 1 − 2e^{−2z} + r(z) with 0 ≤ r(z) ≤ 2e^{−4z}, and
   the like for tanh′. The Lean proof uses the exact formulas
   tanh z − 1 = −2e^{−2z}/(1 + e^{−2z}) and 1 − tanh² z = 4e^{−2z}/(1 + e^{−2z})², and limits.
4. **The two signs.** The paper takes directions with s u_j > 0 for s = ±1. The Lean proof takes
   u_j > 0 and the rays x = tν and x = −tν.
5. **"n ψ_{c_j} = 0 for all n in an open set, so ψ_{c_j} = 0."** Used near one direction ν only:
   ν + ε ψ_{c_j} is again a good direction for small ε > 0, which gives ε (ψ_{c_j}·ψ_{c_j}) = 0.

## D Theorem 5.1 / C.1 for a tanh block (formalized 23 November 2026, `OneBlock/Tanh.lean`)

1. **"For generic parameters … the c_i are nonzero and pairwise non-collinear."** The paper gives
   the reason in one clause ("they lie in the column space of E, of dimension d ≥ 2, where two
   generic vectors are not collinear"). Lean needs, for each condition, a polynomial in θ that is
   not identically zero: an entry of W_write D for a nonzero row of A, an entry of E W_read for a
   nonzero column of C, and the 2×2 minor C_{a₁i} C_{a₂j} − C_{a₁j} C_{a₂i} for non-collinearity.
   The minor uses d_in ≥ 2 and d ≥ 2, as the paper's scope has it.
2. **"By the chain rule"** (Step 3) is an explicit computation of the derivative of
   τ ↦ F_{θ+τη}(x), entry by entry. Mathlib at this version has no derivative of tanh; it is
   proved from sinh and cosh.
3. **"An MLP block acts on each token separately, so we take T = 1."** In Lean the theorem is
   stated for any nonempty set of tokens, and the proof uses inputs whose rows all equal one row v.

## D Lemma C.3, the case of SwiGLU (formalized 23 November 2026, `OneBlock/UnitsSwiGLU.lean`)

1. **The hypothesis "(e_i, β'_i) not proportional to (c_i, β_i)" is not used.** The lemma states it
   for all gated blocks. The proof for SwiGLU needs only e_i ≠ 0 (to find directions with
   ν·e_j ≠ 0). In the paper's proof the hypothesis is used for ReGLU only. Lean has both forms:
   the paper's, and one without the hypothesis.
2. **"The rest of the slowest unit j vanishes."** What is shown is that the cubic polynomial in t
   that multiplies e^{−|z_j|} vanishes; the rest itself is that product only up to
   O(t³ e^{−2|z_j|}).
3. **"The polynomial parts vanish."** The polynomial part collects t ψ_M-terms, the constant, and
   a polynomial of degree at most 2 from every unit that is active on the ray; that it vanishes
   needs t^k × (rests) → 0 for k ≤ 2.
4. **The order in the t² step.** The paper obtains α first and then ψ_{β_j} = 0. The two signs
   give ψ_{β_j} = 0 directly at one direction, once ψ_{c_j} = 0 is known; the open-set argument is
   needed only for ψ_{c_j} = 0 and for (ψ_{e_j}, ψ_{a_j}) = (−α e_j, α a_j). The coefficient of t is
   used for one sign only, and the constant coefficient is not needed.

## D Theorem 5.1 / C.1, the structure of the proof (24 November 2026, `OneBlock/Mlp.lean`, `OneBlock/Gated.lean`)

1. **Only Step 2 depends on the activation.** Steps 1 and 3 of the proof use the activation only
   through its derivative and through the conclusion of Lemma C.3. In Lean the theorem is therefore
   stated once for every activation σ with derivative σ′ for which Lemma C.3 holds with no rescaling
   (tanh, GELU), and once for every gate activation for which it holds with the rescalings of the
   values (SwiGLU, GeGLU). The cases of the paper are corollaries of two lines each.
2. **The conditions on the parameters do not depend on the activation** (ranks d; rows of A nonzero;
   columns of C nonzero and pairwise non-collinear; for gated blocks, value columns nonzero).

## D Lemma C.3, the cases of GELU and GeGLU (formalized 24 November 2026, `OneBlock/UnitsGELU.lean`, `OneBlock/UnitsGeGLU.lean`)

1. **GeGLU: the hypothesis on proportionality.** As for SwiGLU, the statement is given to be proved
   without "(e_i, β′_i) not proportional to (c_i, β_i)". A numerical check
   (`claude/lemma_C3_gelu_geglu_check_2026-11-23.py`, 60 digits) gives a kernel of exactly one
   dimension per hidden unit also when (e_i, β′_i) = r_i (c_i, β_i), and also when e_i = 0 with
   β′_i ≠ 0. For GELU the kernel is 0.
2. **The expansions of GELU with explicit remainders** (`Activations/GeluExpansion.lean`, proved):
   for z > 0, 0 ≤ σ(z) − z + φ(z) ≤ φ(z)/z² and 0 ≤ σ′(z) − 1 − φ(z)(z − 1/z) ≤ φ(z)/z³; for z < 0,
   0 ≤ σ(z) + φ(z) ≤ φ(z)/z² and φ(z)/z³ ≤ σ′(z) − φ(z)(z − 1/z) ≤ 0. They follow from the two
   bounds on the tail and from σ(z) − σ(−z) = z; the paper writes them with O(·).

3. **Both are proved, GeGLU without the hypothesis on proportionality** (every other hypothesis is
   used). So for SwiGLU and GeGLU the hypothesis "(e_i, β′_i) not proportional to (c_i, β_i)" of
   Lemma C.3 serves ReGLU only.
4. **One ray per direction.** For tanh and SwiGLU the Lean proofs use the rays x = tν and x = −tν
   (the two signs of the paper). For GELU and GeGLU the ray x = tν alone gives all coefficients,
   as in the paper.
5. **"The polynomial part vanishes."** Spelled out: for each unit the terms minus
   [u_i > 0]·((u_i t + β_i) ψ_a + ((n ψ_c) t + ψ_β) a) are bounded by a constant times t² φ(z_i), which
   tends to zero; so the affine function of t that is left tends to zero and is zero.
6. **The units other than the slowest** are not expanded. For |z| ≥ 1 the bounds
   |σ(z) − max(z, 0)| ≤ φ(z) and |σ′(z) − 1[z > 0]| ≤ φ(z)(|z| + 1) are enough, with
   t² φ(z_k)/φ(z_j) → 0.
7. **GELU, the bracket of unit j.** Divided by φ(z_j) it tends to the quadratic
   a u w t² + a(u p + β w) t + (a β p − A − a w/u), with u = n c_j, w = n ψ_{c_j}, p = ψ_{β_j},
   A = ψ_{a_j}, a = a_j: the bracket of the paper. Its three coefficients vanish, in the paper's order.
8. **GeGLU, the bracket of unit j** contains 1/z_j. The Lean proof multiplies it by z_j, which gives a
   polynomial of degree 4 in t, and reads off the coefficients of t⁴, t³, t², t. The four equations
   are those of the paper, in the same order; the last two carry a term with ψ_{β_j}, which has
   vanished by then.

## D Lemma C.3, the cases of ReLU, ReLU² and ReGLU (formalized 24 November 2026, `OneBlock/UnitsReLU.lean`, `OneBlock/UnitsReGLU.lean`)

1. **Polynomials on the two sides of a hyperplane, in place of jumps.** With σ(z) = 1[z > 0]·z the
   identity reads L(x) + Σ_i 1[z_i > 0] T_i(x) = 0 off the kinks, with L affine and T_i a polynomial
   of degree at most 2 in x (the terms of unit i on the side z_i > 0). At two points x₀ ± δ c_i near
   a point x₀ that lies on H_i and on no other H_k, the sets of active units differ by i alone. A
   polynomial of degree at most 2 that vanishes near a point vanishes everywhere (shown along
   lines), so subtracting gives T_i = 0 for all x. No derivative in x and no continuity of J is used.
2. **"Every H_i contains points that lie on no other H_k"** is argued as for the rays of tanh: a
   direction v with v·c_i = 0 and v·c_k ≠ 0 for k ≠ i (a real vector space is not a finite union of
   proper subspaces), then a point x₁ + s v of H_i with s outside a finite set.
3. **ReGLU: which hypotheses are used.** "(e_i, β′_i) not proportional to (c_i, β_i)" is used, to
   find a point of H_i where the value w_i does not vanish; "e_i ≠ 0" is not used. A numerical check
   (`claude/lemma_C3_relu_family_check_2026-11-24.py`) gives a larger kernel when the first fails.
4. **The statements assume the identity only at inputs with no hidden unit at its kink,** as the
   paper says for these blocks; for ReLU² this is weaker than "at all inputs".

## D Lemma D.19 (the step for GELU on the path, ε = 0): a missing hypothesis (found 24 November 2026)

Found by the agent that mapped Appendix D; I checked the statement of the lemma, the conditions
(P1), (P2) and "regular", and the two places of the proof against the source. Not yet formalized.

1. **The statement.** "Let σ be GELU, in the case (0), let θ be regular, and let block k+1 satisfy
   (P1) and (P2). Then (D_{k+1}) implies (D_k)." (P1) is "the columns of W are pairwise different,
   and the matrix WV is invertible"; (P2) concerns W only; "regular" asks that V = W_write^{k+1} has
   rank d.
2. **What the proof uses.** In Step 2 and in Step 3: "by Lemma D.2, 𝐃B(nWV) a_j ≠ 0 on an open dense
   set of n". Lemma D.2 gives 𝐃B(h) v = 0 only for v in ℝh, so this needs a_j ≠ 0, the row j of V.
   None of the stated conditions gives it when the block has more than d hidden units.
3. **Smallest example.** A block with q > d hidden units and a_j = 0 for one unit j, the other rows of
   V of rank d. The output does not depend on column j of W. Take Z = 0 and η zero except in column j
   of η_W: the identity of the claim holds for k, and η is not the direction of a change of basis, so
   (D_k) fails while (D_{k+1}) can hold.
4. **The other step lemmas state the condition:** (T1) "no row of V vanishes" for tanh on rays,
   (K3) "no a_j vanishes" for GELU and gated blocks on rays, (S1) "any two rows of V are linearly
   independent" for tanh on the path.
5. **Repair, made in the paper on 24 November 2026**
   (commit 8082c69): (P1) now includes "no row of V vanishes", and the proof says "By (P1), a_j ≠ 0"
   where it uses it. The condition fails on a set of measure zero, so the paragraph "Parameters that
   satisfy all conditions" and Theorem 5.2 (ii) for ε = 0 stand as they are.

The same map lists seven places where the proof is terse (Section 6.2 of
`claude/appendix-D-digest-2026-11-24.md`); none of them is reported as wrong.

## Statements that are stronger or more explicit in Lean than in the paper

- D Proposition 3.3 (ii): no invertibility of the chosen columns is needed for the triangular form.
- D Lemma A.1, "only if", for ε > 0: proved from the two rows v and 2v by algebra, without the
  limit t → ∞ of the paper's proof.
- D Theorem 4.3: stated under the conditions "E and every write have rank d" and "the maps f_ℓ are
  differentiable", and then for almost all parameters. It counts the changes of basis only (the
  number s of the symmetries inside the blocks is not yet in the Lean statement).
- "A real-analytic function that is not identically zero vanishes on a set of measure zero" is
  used by the papers without proof or citation at the places where a rank is carried to generic
  parameters. It is proved in `Generic/AnalyticZeroSet.lean`; a citation in the papers would be
  Mityagin (2015), "The zero set of a real analytic function", which I have not read beyond its
  title and abstract.
