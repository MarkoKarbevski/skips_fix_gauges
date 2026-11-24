import SkipsLean.Depth.ScaledSuffix
import SkipsLean.Depth.RayInduction
import SkipsLean.Depth.RayDense
import SkipsLean.Depth.Frozen
import SkipsLean.Activations.OneSmallFactor

/-!
# Lemma D.12 on a ray, for gated blocks under pre-RMSNorm: from (28) to (38)

Paper (dimension): Appendix D.5, proof of Lemma D.12, from its beginning to equation (38), in the
case (+), for gated blocks. Here `𝓑^∞ = 𝓑_{>k+1}`, the network itself, and `𝓛^∞ = 𝓛`. On a ray
`n = t ξ` with `ξ ∈ C_k`, (24) turns (28) into (33); the left side is expanded in the small terms
of the gates, (34), with coefficients that are meromorphic at infinity, fact (a), "built from
derivatives of `𝓑` and of `𝐃_θ 𝓑(·) η'` at `t^m h°` and from polynomials in `t`, so this is
Lemma D.10 with `t^m` in the place of `t`"; the left side vanishes, fact (b). For a generic ray
((i), (ii), (iii): see `Depth/RayGatedN.lean`) the induction on the exponents shows that all
coefficients vanish, where the step "one small factor" is Lemma D.9 for GeGLU blocks and the parity
(30) for SwiGLU blocks, and where, by (29), `L'_j(t) = ż^g_j(t ξ) ι_j(t ξ) 𝐃𝓑^∞(t^m h°) a_j`: "By
(iii), (K3) and Lemma D.2, `𝐃𝓑^∞(h°) a_j ≠ 0`, so the last factor, which is real-analytic in `t`,
vanishes only at isolated `t`." The result is (38): "for all `n ∈ C_k` and all rows
`w̃ ∈ ℝ^{1×q}`, with `ŵ = w̃ ⊙ ι(n)`, `ż^g(n) = 0` and
`𝐃𝓑^∞(ŵ V) ((w̃ ⊙ ż^v(n)) V + ŵ η_V) + 𝐃_θ 𝓑^∞(ŵ V) η' = 0`."

Stated here, for a gate `σ` with `GateFar σ σ' p` and with the step "one small factor" as the
hypothesis `hone` (it is `one_small_factor_gelu` for GELU and `one_small_factor_silu` for SiLU;
the evenness in `hone` is the parity (30) in the variable `s = 1/t`), and for hidden states with
the rows `T`: (38) at one generic `Ξ`; then (38) for all `n` with rows in `C_k`, given that the `Ξ`
with (i) are dense; then the same for SwiGLU and GeGLU blocks from the independence over `ℚ` of
(K3) for block `k`. In the case (+), `ż(n) = (n Z − ⟨n Z, n⟩ n / d) W_read + n η_read`
(`tangentRMS`). The second part of (38) is written with `writeLHS` at `v = w̃ ⊙ ι(n)`,
`vdot = w̃ ⊙ ż^v(n)`. Condition (iii) says that the derivative of the network after the block is
injective at `g°(Ξ)`.
-/

namespace Skips

open Matrix Filter
open scoped Matrix.Norms.Elementwise Topology

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]
variable {σ σ' : ℝ → ℝ} {p : ℕ} {ε : ℝ}

/-- **Lemma D.12 up to (38), on one generic ray, gated blocks, case (+).** Let `θ` be good for the
cones, let `Z` and `η` satisfy (16) for `k`, and let `Ξ` have its rows in `C_k` and satisfy (i),
(ii), (iii). Then `ż^g(Ξ) = 0`, and the second part of (38) holds at `n = Ξ` for every `w̃`. -/
theorem flat_at_generic_ray_gated_rmsNorm (hε : 0 < ε) (hg : GateFar σ σ' p)
    (hone : ∀ u : ℝ, 0 < u → ∀ a b : ℝ → Matrix T dOut ℝ, AnalyticAt ℝ a 0 → AnalyticAt ℝ b 0 →
      (∀ᶠ s in 𝓝 (0 : ℝ), a (-s) = a s ∧ b (-s) = b s) →
      FasterThanPowers (fun t : ℝ =>
        a (1 / t) + (t * (1 - σ' (t * u)) / (t * u - σ (t * u))) • b (1 / t)) →
      ∀ᶠ s in 𝓝 (0 : ℝ), b s = 0)
    {C : Fin (L + 1) → Set (d → ℝ)} {A : ∀ ℓ, Finset (hid ℓ)}
    {θ : Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut}
    (hθ : GoodForConesGated C A θ) (k : Fin L) (Z : Matrix d d ℝ)
    (η : Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)
    (hflat : SuffixFlat (Arch.gated σ (rmsNorm ε) hid) θ k.castSucc Z η)
    (Ξ : Matrix T d ℝ) (hΞ : ∀ t, Ξ t ∈ C k.castSucc)
    (hi : LinearIndependent ℚ (fun i : T × hid k => |(Ξ * θ.read k) i.1 (Sum.inl i.2)| ^ p))
    (hii : ∀ t j, (Ξ * θ.read k) t (Sum.inr j) ≠ 0)
    (hiii : Function.Injective
      (fderiv ℝ (fun h' : Matrix T d ℝ => suffix (Arch.gated σ (rmsNorm ε) hid) 0 θ k.succ h')
        (Matrix.of fun t => frozenGated θ k (A k) (Ξ t)))) :
    (∀ t j, (tangentRMS Z Ξ * θ.read k + Ξ * η.read k) t (Sum.inl j) = 0) ∧
      ∀ w : Matrix T (hid k) ℝ,
        writeLHS (Arch.gated σ (rmsNorm ε) hid) θ k η
          (Matrix.of fun t j => w t j * (Ξ * θ.read k) t (Sum.inr j))
          (Matrix.of fun t j =>
            w t j * (tangentRMS Z Ξ * θ.read k + Ξ * η.read k) t (Sum.inr j)) = 0 := by
  sorry

/-- **Lemma D.12 up to (38), gated blocks, case (+).** Let `θ` be good for the cones and regular,
and let the `Ξ` with (i) be dense. If `Z` and `η` satisfy (16) for `k`, then (38) holds for every
`n` with its rows in `C_k` and every `w̃`. -/
theorem flat_of_suffixFlat_gated_rmsNorm (hε : 0 < ε) (hg : GateFar σ σ' p)
    (hone : ∀ u : ℝ, 0 < u → ∀ a b : ℝ → Matrix T dOut ℝ, AnalyticAt ℝ a 0 → AnalyticAt ℝ b 0 →
      (∀ᶠ s in 𝓝 (0 : ℝ), a (-s) = a s ∧ b (-s) = b s) →
      FasterThanPowers (fun t : ℝ =>
        a (1 / t) + (t * (1 - σ' (t * u)) / (t * u - σ (t * u))) • b (1 / t)) →
      ∀ᶠ s in 𝓝 (0 : ℝ), b s = 0)
    {C : Fin (L + 1) → Set (d → ℝ)} {A : ∀ ℓ, Finset (hid ℓ)}
    {θ : Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut}
    (hθ : GoodForConesGated C A θ) (hreg : Regular (Arch.gated σ (rmsNorm ε) hid) θ) (k : Fin L)
    (hdense : Dense {Ξ : Matrix T d ℝ |
      LinearIndependent ℚ (fun i : T × hid k => |(Ξ * θ.read k) i.1 (Sum.inl i.2)| ^ p)})
    (Z : Matrix d d ℝ) (η : Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)
    (hflat : SuffixFlat (Arch.gated σ (rmsNorm ε) hid) θ k.castSucc Z η) :
    ∀ n : Matrix T d ℝ, (∀ t, n t ∈ C k.castSucc) →
      (∀ t j, (tangentRMS Z n * θ.read k + n * η.read k) t (Sum.inl j) = 0) ∧
      ∀ w : Matrix T (hid k) ℝ,
        writeLHS (Arch.gated σ (rmsNorm ε) hid) θ k η
          (Matrix.of fun t j => w t j * (n * θ.read k) t (Sum.inr j))
          (Matrix.of fun t j =>
            w t j * (tangentRMS Z n * θ.read k + n * η.read k) t (Sum.inr j)) = 0 := by
  sorry

/-- **Lemma D.12 up to (38), SwiGLU blocks, case (+):** with the gate columns of block `k`
linearly independent over `ℚ`. -/
theorem flat_of_suffixFlat_swiglu_rmsNorm (hε : 0 < ε) {C : Fin (L + 1) → Set (d → ℝ)}
    {A : ∀ ℓ, Finset (hid ℓ)}
    {θ : Params (Arch.gated (T := T) (d := d) silu (rmsNorm ε) hid) dIn dOut}
    (hθ : GoodForConesGated C A θ) (k : Fin L)
    (hQ : LinearIndependent ℚ (fun j : hid k => (θ.read k)ᵀ (Sum.inl j)))
    (Z : Matrix d d ℝ) (η : Params (Arch.gated (T := T) (d := d) silu (rmsNorm ε) hid) dIn dOut)
    (hflat : SuffixFlat (Arch.gated silu (rmsNorm ε) hid) θ k.castSucc Z η) :
    ∀ n : Matrix T d ℝ, (∀ t, n t ∈ C k.castSucc) →
      (∀ t j, (tangentRMS Z n * θ.read k + n * η.read k) t (Sum.inl j) = 0) ∧
      ∀ w : Matrix T (hid k) ℝ,
        writeLHS (Arch.gated silu (rmsNorm ε) hid) θ k η
          (Matrix.of fun t j => w t j * (n * θ.read k) t (Sum.inr j))
          (Matrix.of fun t j =>
            w t j * (tangentRMS Z n * θ.read k + n * η.read k) t (Sum.inr j)) = 0 := by
  sorry

/-- **Lemma D.12 up to (38), GeGLU blocks, case (+):** with the matrices `c_j c_j^⊤` of the gate
columns of block `k` linearly independent over `ℚ`. -/
theorem flat_of_suffixFlat_geglu_rmsNorm (hε : 0 < ε) {C : Fin (L + 1) → Set (d → ℝ)}
    {A : ∀ ℓ, Finset (hid ℓ)}
    {θ : Params (Arch.gated (T := T) (d := d) gelu (rmsNorm ε) hid) dIn dOut}
    (hθ : GoodForConesGated C A θ) (k : Fin L)
    (hQ : LinearIndependent ℚ (fun j : hid k =>
      Matrix.vecMulVec ((θ.read k)ᵀ (Sum.inl j)) ((θ.read k)ᵀ (Sum.inl j))))
    (Z : Matrix d d ℝ) (η : Params (Arch.gated (T := T) (d := d) gelu (rmsNorm ε) hid) dIn dOut)
    (hflat : SuffixFlat (Arch.gated gelu (rmsNorm ε) hid) θ k.castSucc Z η) :
    ∀ n : Matrix T d ℝ, (∀ t, n t ∈ C k.castSucc) →
      (∀ t j, (tangentRMS Z n * θ.read k + n * η.read k) t (Sum.inl j) = 0) ∧
      ∀ w : Matrix T (hid k) ℝ,
        writeLHS (Arch.gated gelu (rmsNorm ε) hid) θ k η
          (Matrix.of fun t j => w t j * (n * θ.read k) t (Sum.inr j))
          (Matrix.of fun t j =>
            w t j * (tangentRMS Z n * θ.read k + n * η.read k) t (Sum.inr j)) = 0 := by
  sorry

end Skips
