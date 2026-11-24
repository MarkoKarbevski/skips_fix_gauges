import SkipsLean.Depth.ScaledSuffix
import SkipsLean.Depth.RayInduction
import SkipsLean.Depth.RayDense
import SkipsLean.Depth.Frozen
import SkipsLean.Activations.OneSmallFactor

/-!
# Lemma D.12 on a ray, for GELU blocks under pre-RMSNorm: from (28) to (38)

Paper (dimension): Appendix D.5, proof of Lemma D.12, from its beginning to equation (38), for GELU
blocks in the case (+). "A GELU block has the form of a GeGLU block in which the value `n e_j` of
every hidden unit is replaced by the number `1`": `ι(n) = (1, …, 1)`, `m = 1`, there is no `ż^v`,
`ŵ = w̃`, and `𝓛` is the map (21) of the block identity for MLP blocks (`blockLHS` in
`Depth/StepTanh.lean`, which is `writeLHS` at `v = w̃`, `vdot = w̃' ⊙ ż`). The proof is the one
for gated blocks (see `Depth/RayGatedPlus.lean` and `Depth/RayGatedN.lean` for the quotations), with
Lemma D.9 in the step "one small factor". Equation (38) reads: for all `n ∈ C_k` and all rows `w̃`,
`ż(n) = 0` and `𝐃𝓑(w̃ V)(w̃ η_V) + 𝐃_θ 𝓑(w̃ V) η' = 0`.

Stated here, for an MLP block whose activation `σ` has `GateFar σ σ' p`, with the step "one small
factor" as the hypothesis `hone`, and for hidden states with the rows `T`: (38) at one generic `Ξ`
((i) the numbers `|ξ_t c_j|^p` are independent over `ℚ`; (iii) the derivative of the network after
the block is injective at `g°(Ξ)`; there is no (ii)); then (38) for all `n` with rows in `C_k`,
given that the `Ξ` with (i) are dense; then for GELU blocks from the independence over `ℚ` of the
matrices `c_j c_j^⊤` of block `k`.
-/

namespace Skips

open Matrix Filter
open scoped Matrix.Norms.Elementwise Topology

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]
variable {σ σ' : ℝ → ℝ} {p : ℕ} {ε : ℝ}

/-- **Lemma D.12 up to (38), on one generic ray, MLP blocks, case (+).** Let `θ` be good for the
cones, let `Z` and `η` satisfy (16) for `k`, and let `Ξ` have its rows in `C_k` and satisfy (i) and
(iii). Then `ż(Ξ) = 0`, and `𝐃𝓑(w̃ V)(w̃ η_V) + 𝐃_θ 𝓑(w̃ V) η = 0` for every `w̃`. -/
theorem flat_at_generic_ray_mlp_rmsNorm (hε : 0 < ε) (hg : GateFar σ σ' p)
    (hone : ∀ u : ℝ, 0 < u → ∀ a b : ℝ → Matrix T dOut ℝ, AnalyticAt ℝ a 0 → AnalyticAt ℝ b 0 →
      (∀ᶠ s in 𝓝 (0 : ℝ), a (-s) = a s ∧ b (-s) = b s) →
      FasterThanPowers (fun t : ℝ =>
        a (1 / t) + (t * (1 - σ' (t * u)) / (t * u - σ (t * u))) • b (1 / t)) →
      ∀ᶠ s in 𝓝 (0 : ℝ), b s = 0)
    {C : Fin (L + 1) → Set (d → ℝ)} {A : ∀ ℓ, Finset (hid ℓ)}
    {θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut}
    (hθ : GoodForConesMlp C A θ) (k : Fin L) (Z : Matrix d d ℝ)
    (η : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)
    (hflat : SuffixFlat (Arch.mlp σ (rmsNorm ε) hid) θ k.castSucc Z η)
    (Ξ : Matrix T d ℝ) (hΞ : ∀ t, Ξ t ∈ C k.castSucc)
    (hi : LinearIndependent ℚ (fun i : T × hid k => |(Ξ * θ.read k) i.1 i.2| ^ p))
    (hiii : Function.Injective
      (fderiv ℝ (fun h' : Matrix T d ℝ => suffix (Arch.mlp σ (rmsNorm ε) hid) 0 θ k.succ h')
        (Matrix.of fun t => frozenMlp θ k (A k) (Ξ t)))) :
    tangentRMS Z Ξ * θ.read k + Ξ * η.read k = 0 ∧
      ∀ w : Matrix T (hid k) ℝ, writeLHS (Arch.mlp σ (rmsNorm ε) hid) θ k η w 0 = 0 := by
  sorry

/-- **Lemma D.12 up to (38), MLP blocks, case (+).** Let `θ` be good for the cones and regular, and
let the `Ξ` with (i) be dense. If `Z` and `η` satisfy (16) for `k`, then `ż(n) = 0` for every `n`
with its rows in `C_k`, and `𝐃𝓑(w̃ V)(w̃ η_V) + 𝐃_θ 𝓑(w̃ V) η = 0` for every `w̃`. -/
theorem flat_of_suffixFlat_mlp_rmsNorm (hε : 0 < ε) (hg : GateFar σ σ' p)
    (hone : ∀ u : ℝ, 0 < u → ∀ a b : ℝ → Matrix T dOut ℝ, AnalyticAt ℝ a 0 → AnalyticAt ℝ b 0 →
      (∀ᶠ s in 𝓝 (0 : ℝ), a (-s) = a s ∧ b (-s) = b s) →
      FasterThanPowers (fun t : ℝ =>
        a (1 / t) + (t * (1 - σ' (t * u)) / (t * u - σ (t * u))) • b (1 / t)) →
      ∀ᶠ s in 𝓝 (0 : ℝ), b s = 0)
    {C : Fin (L + 1) → Set (d → ℝ)} {A : ∀ ℓ, Finset (hid ℓ)}
    {θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut}
    (hθ : GoodForConesMlp C A θ) (hreg : Regular (Arch.mlp σ (rmsNorm ε) hid) θ) (k : Fin L)
    (hdense : Dense {Ξ : Matrix T d ℝ |
      LinearIndependent ℚ (fun i : T × hid k => |(Ξ * θ.read k) i.1 i.2| ^ p)})
    (Z : Matrix d d ℝ) (η : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)
    (hflat : SuffixFlat (Arch.mlp σ (rmsNorm ε) hid) θ k.castSucc Z η) :
    (∀ n : Matrix T d ℝ, (∀ t, n t ∈ C k.castSucc) →
        tangentRMS Z n * θ.read k + n * η.read k = 0) ∧
      ∀ w : Matrix T (hid k) ℝ, writeLHS (Arch.mlp σ (rmsNorm ε) hid) θ k η w 0 = 0 := by
  sorry

/-- **Lemma D.12 up to (38), GELU blocks, case (+):** with the matrices `c_j c_j^⊤` of the read
columns of block `k` linearly independent over `ℚ`. -/
theorem flat_of_suffixFlat_gelu_rmsNorm (hε : 0 < ε) {C : Fin (L + 1) → Set (d → ℝ)}
    {A : ∀ ℓ, Finset (hid ℓ)}
    {θ : Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm ε) hid) dIn dOut}
    (hθ : GoodForConesMlp C A θ) (k : Fin L)
    (hQ : LinearIndependent ℚ (fun j : hid k =>
      Matrix.vecMulVec ((θ.read k)ᵀ j) ((θ.read k)ᵀ j)))
    (Z : Matrix d d ℝ) (η : Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm ε) hid) dIn dOut)
    (hflat : SuffixFlat (Arch.mlp gelu (rmsNorm ε) hid) θ k.castSucc Z η) :
    (∀ n : Matrix T d ℝ, (∀ t, n t ∈ C k.castSucc) →
        tangentRMS Z n * θ.read k + n * η.read k = 0) ∧
      ∀ w : Matrix T (hid k) ℝ, writeLHS (Arch.mlp gelu (rmsNorm ε) hid) θ k η w 0 = 0 := by
  sorry

end Skips
