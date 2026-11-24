import SkipsLean.Depth.FrozenFar
import SkipsLean.Depth.RayInduction
import SkipsLean.Depth.RayDense

/-!
# Lemma D.12 on a ray, for gated blocks without normalization: from (28) to (38)

Paper (dimension): Appendix D.5, proof of Lemma D.12, from its beginning to equation (38), in the
case (n). "Let `Z` and `η` satisfy (16) for `k`, so that (28) holds […]. Let `𝓑^∞ = 𝓑°_{>k+1}` in
the case (n), and let `𝓛^∞` be (27) with `𝓑^∞` in the place of `𝓑`." On a ray `n = t ξ` with
`ξ ∈ C_k`, (24) turns (28) into (33), the expansion (34) in the small terms `δ_j(t)` of the gates
has the three properties (a), (b), (c), and for a generic ray, that is, for `ξ ∈ C_k` such that

  (i) the numbers `r_1, …, r_q` are linearly independent over `ℚ` (`r_j = |ξ c_j|^p`);
  (ii) `ι_j(ξ) ≠ 0` for every `j`;
  (iii) `g°(ξ) ∈ U^∞`,

the induction on the exponents shows that all coefficients vanish. "What the induction gives. For
this `ξ` and every `t > 0`, all coefficients of the expansion of `(w̃, w̃') ↦ 𝓛^∞(w̃, w̃'; t ξ)` at
`(t ξ W_g I_A, 1_A)` vanish, so this real-analytic map vanishes. The rows `t ξ` of this kind are
dense in `C_k`. So, with (37), for all `n ∈ C_k` and all rows `w̃ ∈ ℝ^{1×q}`, with `ŵ = w̃ ⊙ ι(n)`,

  `ż^g(n) = 0`,   `𝐃𝓑^∞(ŵ V) ((w̃ ⊙ ż^v(n)) V + ŵ η_V) + 𝐃_θ 𝓑^∞(ŵ V) η' = 0`.   (38)"

Stated here, for a gate `σ` with `GateFar σ σ' p` and hidden states with the rows `T`: (38) at one
generic `Ξ` (one row `ξ_t` per token; (i) is asked of the numbers `|ξ_t c_j|^p` over all tokens and
hidden units, and (iii) says that the derivative of the frozen network after the block is injective
at `g°(Ξ)`, which is what the proof uses of `U^∞`); then (38) for all `n` with rows in `C_k`, given
that the `Ξ` with (i) are dense; then the same for SwiGLU and GeGLU blocks from the independence
over `ℚ` of (K3) for block `k`. The first part of (38), `ż^g(n) = 0` on an open set of `n`, is
stated as `Z W_g + η_g = 0`. The second part is written with `writeLHS` for the frozen network at
`v = w̃ ⊙ ι(n)`, `vdot = w̃ ⊙ ż^v(n)`.

In the case (n) the frozen network is homogeneous (`suffix_frozen_smul`), so that
`𝓛^∞(t (W° + y), w̃'; t ξ) = t^{2 · 2^{L−k−1}} 𝓛^∞(W° + y, w̃'; ξ)`: the coefficients of (34) are
constants times powers of `t`, which is fact (a) in this case. Fact (b) is Lemma D.11
(`exists_far_frozen_bounds`), and the induction is `ray_induction_matrix`.
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise Topology

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]
variable {σ σ' : ℝ → ℝ} {p : ℕ}

/-- **Lemma D.12 up to (38), on one generic ray, case (n).** Let `θ` be good for the cones, let `Z`
and `η` satisfy (16) for `k`, and let `Ξ` have its rows in `C_k` and satisfy (i), (ii), (iii).
Then `ż^g(Ξ) = 0`, and the second part of (38) holds at `n = Ξ` for every `w̃`. -/
theorem frozen_flat_at_generic_ray (hg : GateFar σ σ' p) {C : Fin (L + 1) → Set (d → ℝ)}
    {A : ∀ ℓ, Finset (hid ℓ)} {θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut}
    (hθ : GoodForConesGated C A θ) (k : Fin L) (Z : Matrix d d ℝ)
    (η : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (hflat : SuffixFlat (Arch.gated σ id hid) θ k.castSucc Z η)
    (Ξ : Matrix T d ℝ) (hΞ : ∀ t, Ξ t ∈ C k.castSucc)
    (hi : LinearIndependent ℚ (fun i : T × hid k => |(Ξ * θ.read k) i.1 (Sum.inl i.2)| ^ p))
    (hii : ∀ t j, (Ξ * θ.read k) t (Sum.inr j) ≠ 0)
    (hiii : Function.Injective
      (fderiv ℝ (fun h' : Matrix T d ℝ => suffix (Arch.frozen A) 0 (θ.toFrozen A) k.succ h')
        ((Arch.frozen (T := T) (d := d) A).f k (Ξ * θ.read k) * θ.write k))) :
    (∀ t j, (Ξ * (Z * θ.read k + η.read k)) t (Sum.inl j) = 0) ∧
      ∀ w : Matrix T (hid k) ℝ,
        writeLHS (Arch.frozen A) (θ.toFrozen A) k (η.toFrozen A)
          (Matrix.of fun t j => w t j * (Ξ * θ.read k) t (Sum.inr j))
          (Matrix.of fun t j => w t j * (Ξ * (Z * θ.read k + η.read k)) t (Sum.inr j)) = 0 := by
  sorry

/-- **Lemma D.12 up to (38), case (n).** Let `θ` be good for the cones, and let the `Ξ` with (i)
be dense. If `Z` and `η` satisfy (16) for `k`, then `Z W_g + η_g = 0`, and the second part of (38)
holds for every `n` with its rows in `C_k` and every `w̃`. -/
theorem frozen_flat_of_suffixFlat [Nonempty T] (hg : GateFar σ σ' p)
    {C : Fin (L + 1) → Set (d → ℝ)} {A : ∀ ℓ, Finset (hid ℓ)}
    {θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut}
    (hθ : GoodForConesGated C A θ) (k : Fin L)
    (hdense : Dense {Ξ : Matrix T d ℝ |
      LinearIndependent ℚ (fun i : T × hid k => |(Ξ * θ.read k) i.1 (Sum.inl i.2)| ^ p)})
    (Z : Matrix d d ℝ) (η : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (hflat : SuffixFlat (Arch.gated σ id hid) θ k.castSucc Z η) :
    (∀ i j, (Z * θ.read k + η.read k) i (Sum.inl j) = 0) ∧
      ∀ n : Matrix T d ℝ, (∀ t, n t ∈ C k.castSucc) → ∀ w : Matrix T (hid k) ℝ,
        writeLHS (Arch.frozen A) (θ.toFrozen A) k (η.toFrozen A)
          (Matrix.of fun t j => w t j * (n * θ.read k) t (Sum.inr j))
          (Matrix.of fun t j => w t j * (n * (Z * θ.read k + η.read k)) t (Sum.inr j)) = 0 := by
  sorry

/-- **Lemma D.12 up to (38), SwiGLU blocks, case (n):** with the gate columns of block `k`
linearly independent over `ℚ`. -/
theorem frozen_flat_of_suffixFlat_swiglu [Nonempty T] {C : Fin (L + 1) → Set (d → ℝ)}
    {A : ∀ ℓ, Finset (hid ℓ)} {θ : Params (Arch.gated (T := T) (d := d) silu id hid) dIn dOut}
    (hθ : GoodForConesGated C A θ) (k : Fin L)
    (hQ : LinearIndependent ℚ (fun j : hid k => (θ.read k)ᵀ (Sum.inl j)))
    (Z : Matrix d d ℝ) (η : Params (Arch.gated (T := T) (d := d) silu id hid) dIn dOut)
    (hflat : SuffixFlat (Arch.gated silu id hid) θ k.castSucc Z η) :
    (∀ i j, (Z * θ.read k + η.read k) i (Sum.inl j) = 0) ∧
      ∀ n : Matrix T d ℝ, (∀ t, n t ∈ C k.castSucc) → ∀ w : Matrix T (hid k) ℝ,
        writeLHS (Arch.frozen A) (θ.toFrozen A) k (η.toFrozen A)
          (Matrix.of fun t j => w t j * (n * θ.read k) t (Sum.inr j))
          (Matrix.of fun t j => w t j * (n * (Z * θ.read k + η.read k)) t (Sum.inr j)) = 0 := by
  sorry

/-- **Lemma D.12 up to (38), GeGLU blocks, case (n):** with the matrices `c_j c_j^⊤` of the gate
columns of block `k` linearly independent over `ℚ`. -/
theorem frozen_flat_of_suffixFlat_geglu [Nonempty T] {C : Fin (L + 1) → Set (d → ℝ)}
    {A : ∀ ℓ, Finset (hid ℓ)} {θ : Params (Arch.gated (T := T) (d := d) gelu id hid) dIn dOut}
    (hθ : GoodForConesGated C A θ) (k : Fin L)
    (hQ : LinearIndependent ℚ (fun j : hid k =>
      Matrix.vecMulVec ((θ.read k)ᵀ (Sum.inl j)) ((θ.read k)ᵀ (Sum.inl j))))
    (Z : Matrix d d ℝ) (η : Params (Arch.gated (T := T) (d := d) gelu id hid) dIn dOut)
    (hflat : SuffixFlat (Arch.gated gelu id hid) θ k.castSucc Z η) :
    (∀ i j, (Z * θ.read k + η.read k) i (Sum.inl j) = 0) ∧
      ∀ n : Matrix T d ℝ, (∀ t, n t ∈ C k.castSucc) → ∀ w : Matrix T (hid k) ℝ,
        writeLHS (Arch.frozen A) (θ.toFrozen A) k (η.toFrozen A)
          (Matrix.of fun t j => w t j * (n * θ.read k) t (Sum.inr j))
          (Matrix.of fun t j => w t j * (n * (Z * θ.read k + η.read k)) t (Sum.inr j)) = 0 := by
  sorry

end Skips
