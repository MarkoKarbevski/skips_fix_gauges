import SkipsLean.Depth.Cones
import SkipsLean.Depth.RayGatedN
import SkipsLean.Depth.StepsGatedN

/-!
# The step for GELU and gated blocks on rays

Paper (dimension): Lemma D.12. "Let the blocks be GELU blocks in the case (+), or gated blocks in
the case (n) or (+). Let `θ` be good for the cones `C_0, …, C_L`, and let `k < L`. Then
`(D_{k+1})` implies `(D_k)`."

One statement for each of the five settings: SwiGLU and GeGLU blocks in the cases (n) and (+), and
GELU blocks in the case (+). "Good for the cones" is `GoodForConesGated` or `GoodForConesMlp`
(`Depth/Cones.lean`) together with the independence over `ℚ` of (K3): of the gate columns for
SwiGLU blocks, of the matrices `c_j c_j^⊤` for GeGLU and GELU blocks. The claims are `ClaimGated`
(`Depth/SuffixGated.lean`) and `ClaimRMS` (`Depth/SuffixRMS.lean`).

This is the longest argument of Appendix D. In the case (n) the two proofs below put together
its two halves, each stated in a file of its own: from (28) to (38) on generic rays
(`Depth/RayGatedN.lean`, which uses Lemmas D.8 and D.11, the frozen network and the induction on
the exponents), and steps 1 to 3 (`Depth/StepsGatedN.lean`). The three statements in the case (+)
are not proved yet.
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise Topology

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]


/-- **Lemma D.12, SwiGLU blocks, case (n).** -/
theorem claimGated_castSucc_swiglu [Nonempty T] {C : Fin (L + 1) → Set (d → ℝ)}
    {A : ∀ ℓ, Finset (hid ℓ)} {θ : Params (Arch.gated (T := T) (d := d) silu id hid) dIn dOut}
    (hθ : GoodForConesGated C A θ)
    (hQ : ∀ ℓ, LinearIndependent ℚ (fun j : hid ℓ => (θ.read ℓ)ᵀ (Sum.inl j)))
    (k : Fin L) (hk : ClaimGated ⊤ θ k.succ) : ClaimGated ⊤ θ k.castSucc := by
  intro Z η hflat
  -- the ray: (28) gives (38) with the frozen network (`Depth/RayGatedN.lean`)
  obtain ⟨hgate, hfro⟩ := frozen_flat_of_suffixFlat_swiglu hθ k (hQ k) Z η hflat
  -- steps 1 to 3 (`Depth/StepsGatedN.lean`)
  exact claimGated_castSucc_of_frozen hasDerivAt_silu analyticOnNhd_silu hθ
    (regular_of_goodForConesGated_swiglu hθ) k hk Z η hflat hgate hfro

/-- **Lemma D.12, SwiGLU blocks, case (+).** -/
theorem claimGated_castSucc_swiglu_rmsNorm [Nonempty T] {ε : ℝ} (hε : 0 < ε)
    {C : Fin (L + 1) → Set (d → ℝ)} {A : ∀ ℓ, Finset (hid ℓ)}
    {θ : Params (Arch.gated (T := T) (d := d) silu (rmsNorm ε) hid) dIn dOut}
    (hθ : GoodForConesGated C A θ)
    (hQ : ∀ ℓ, LinearIndependent ℚ (fun j : hid ℓ => (θ.read ℓ)ᵀ (Sum.inl j)))
    (k : Fin L) (hk : ClaimGated (antisymmetric d) θ k.succ) :
    ClaimGated (antisymmetric d) θ k.castSucc := by
  sorry

/-- **Lemma D.12, GeGLU blocks, case (n).** -/
theorem claimGated_castSucc_geglu [Nonempty T] {C : Fin (L + 1) → Set (d → ℝ)}
    {A : ∀ ℓ, Finset (hid ℓ)} {θ : Params (Arch.gated (T := T) (d := d) gelu id hid) dIn dOut}
    (hθ : GoodForConesGated C A θ)
    (hQ : ∀ ℓ, LinearIndependent ℚ (fun j : hid ℓ =>
      Matrix.vecMulVec ((θ.read ℓ)ᵀ (Sum.inl j)) ((θ.read ℓ)ᵀ (Sum.inl j))))
    (k : Fin L) (hk : ClaimGated ⊤ θ k.succ) : ClaimGated ⊤ θ k.castSucc := by
  intro Z η hflat
  -- the ray: (28) gives (38) with the frozen network (`Depth/RayGatedN.lean`)
  obtain ⟨hgate, hfro⟩ := frozen_flat_of_suffixFlat_geglu hθ k (hQ k) Z η hflat
  -- steps 1 to 3 (`Depth/StepsGatedN.lean`)
  exact claimGated_castSucc_of_frozen hasDerivAt_gelu analyticOnNhd_gelu hθ
    (regular_of_goodForConesGated_geglu hθ) k hk Z η hflat hgate hfro

/-- **Lemma D.12, GeGLU blocks, case (+).** -/
theorem claimGated_castSucc_geglu_rmsNorm [Nonempty T] {ε : ℝ} (hε : 0 < ε)
    {C : Fin (L + 1) → Set (d → ℝ)} {A : ∀ ℓ, Finset (hid ℓ)}
    {θ : Params (Arch.gated (T := T) (d := d) gelu (rmsNorm ε) hid) dIn dOut}
    (hθ : GoodForConesGated C A θ)
    (hQ : ∀ ℓ, LinearIndependent ℚ (fun j : hid ℓ =>
      Matrix.vecMulVec ((θ.read ℓ)ᵀ (Sum.inl j)) ((θ.read ℓ)ᵀ (Sum.inl j))))
    (k : Fin L) (hk : ClaimGated (antisymmetric d) θ k.succ) :
    ClaimGated (antisymmetric d) θ k.castSucc := by
  sorry

/-- **Lemma D.12, GELU blocks, case (+).** -/
theorem claimRMS_castSucc_gelu [Nonempty T] {ε : ℝ} (hε : 0 < ε)
    {C : Fin (L + 1) → Set (d → ℝ)} {A : ∀ ℓ, Finset (hid ℓ)}
    {θ : Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm ε) hid) dIn dOut}
    (hθ : GoodForConesMlp C A θ)
    (hQ : ∀ ℓ, LinearIndependent ℚ (fun j : hid ℓ =>
      Matrix.vecMulVec ((θ.read ℓ)ᵀ j) ((θ.read ℓ)ᵀ j)))
    (k : Fin L) (hk : ClaimRMS (Arch.mlp gelu (rmsNorm ε) hid) θ k.succ) :
    ClaimRMS (Arch.mlp gelu (rmsNorm ε) hid) θ k.castSucc := by
  sorry

end Skips
