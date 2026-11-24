import SkipsLean.Residual.LearnedSkipsConformal
import SkipsLean.Basic.RMSNormConverse

/-!
# Orthogonal skips can be absorbed: the converse

Paper (skips paper), Theorem A.12 (ii): "Conversely, let the reads and the readout have rank
`d_model`, and let invertible `G_0, …, G_L` turn every skip into the identity,
`G_{ℓ−1}⁻¹ A_ℓ G_ℓ = I`. If the network, written in the variables `h_ℓ G_ℓ`, is a pre-RMSNorm
residual network, then every `Π_ℓ` lies in `G`."

Its proof: "Conversely, `G_{ℓ−1}⁻¹ A_ℓ G_ℓ = I` for every `ℓ` gives `G_ℓ = Π_ℓ⁻¹ G_0`, so in the
variables `h′_ℓ = h_ℓ G_ℓ` block `ℓ` reads `N_ε(h′_{ℓ−1} G_0⁻¹ Π_{ℓ−1}) W_read^ℓ`, and the readout
reads `N_ε(h′_L G_0⁻¹ Π_L)`. In a pre-RMSNorm residual network every read has the form
`N_ε(h′) W`; as the reads and the readout have rank `d_model`, this gives matrices `M_ℓ` with
`N_ε(h′ G_0⁻¹ Π_ℓ) = N_ε(h′) M_ℓ` for all `h′`, and Lemma A.2 puts every `G_0⁻¹ Π_ℓ` in `G`. For
`ℓ = 0` this puts `G_0` in `G`, and so every `Π_ℓ` lies in `G`."

Here, with the forward products `Π_ℓ = A_1 ⋯ A_ℓ` (`skipProdFwd`,
`Residual/LearnedSkipsConformal.lean`). In the variables `h′_ℓ = h_ℓ G_ℓ` the skips are the
identity, block `ℓ` reads `N_ε(h′_{ℓ−1} G_{ℓ−1}⁻¹) W_read^ℓ` and the readout reads
`N_ε(h′_L G_L⁻¹) D`. "The network, written in the variables `h_ℓ G_ℓ`, is a pre-RMSNorm residual
network" is stated as the proof uses it: every read and the readout have the form `N_ε(h′) W′`,
that is, there are matrices `W′_ℓ` and `D′` with
`N_ε(h G_{ℓ−1}⁻¹) W_read^ℓ = N_ε(h) W′_ℓ` and `N_ε(h G_L⁻¹) D = N_ε(h) D′` for every hidden state
`h`. The conclusion for `ε = 0`: every `Π_ℓ` is a positive multiple of an orthogonal matrix
(`G = CO(d)`); for `ε > 0`: every `Π_ℓ` is orthogonal (`G = O(d)`). There is at least one token.
-/

namespace Skips

open Matrix

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d]
  [Fintype dIn] [Fintype dOut]
variable {A : Arch T d L}

/-- **Theorem A.12 (ii) of the skips paper, "Conversely", for `ε = 0`:** let the reads and the
readout have rank `d`, and let invertible `G_0, …, G_L` turn every skip into the identity,
`G_{ℓ−1}⁻¹ A_ℓ G_ℓ = I`. If in the variables `h_ℓ G_ℓ` every read and the readout have the form
`N_0(h′) W′`, then every `Π_ℓ = A_1 ⋯ A_ℓ` is a positive multiple of an orthogonal matrix. -/
theorem skipProdFwd_conformal_of_residual_rmsNorm_zero (θ : Params A dIn dOut)
    (S : Fin L → GL d ℝ) (G : Fin (L + 1) → GL d ℝ)
    (hG : ∀ ℓ : Fin L, (G ℓ.castSucc)⁻¹ * S ℓ * G ℓ.succ = 1)
    (hread : ∀ ℓ : Fin L, (θ.read ℓ).rank = Fintype.card d) (hD : θ.D.rank = Fintype.card d)
    (hres : ∀ ℓ : Fin L, ∃ W' : Matrix d (A.r ℓ) ℝ, ∀ h : Matrix T d ℝ,
      rmsNorm 0 (h * (↑(G ℓ.castSucc)⁻¹ : Matrix d d ℝ)) * θ.read ℓ = rmsNorm 0 h * W')
    (hresD : ∃ D' : Matrix d dOut ℝ, ∀ h : Matrix T d ℝ,
      rmsNorm 0 (h * (↑(G (Fin.last L))⁻¹ : Matrix d d ℝ)) * θ.D = rmsNorm 0 h * D') :
    ∀ ℓ, ∃ (c : ℝ) (P : Matrix d d ℝ), 0 < c ∧ P ∈ Matrix.orthogonalGroup d ℝ ∧
      (skipProdFwd S ℓ : Matrix d d ℝ) = c • P := by
  sorry

/-- **Theorem A.12 (ii) of the skips paper, "Conversely", for `ε > 0`:** let the reads and the
readout have rank `d`, and let invertible `G_0, …, G_L` turn every skip into the identity,
`G_{ℓ−1}⁻¹ A_ℓ G_ℓ = I`. If in the variables `h_ℓ G_ℓ` every read and the readout have the form
`N_ε(h′) W′`, then every `Π_ℓ = A_1 ⋯ A_ℓ` is orthogonal. -/
theorem skipProdFwd_orthogonal_of_residual_rmsNorm {ε : ℝ} (hε : 0 < ε) (θ : Params A dIn dOut)
    (S : Fin L → GL d ℝ) (G : Fin (L + 1) → GL d ℝ)
    (hG : ∀ ℓ : Fin L, (G ℓ.castSucc)⁻¹ * S ℓ * G ℓ.succ = 1)
    (hread : ∀ ℓ : Fin L, (θ.read ℓ).rank = Fintype.card d) (hD : θ.D.rank = Fintype.card d)
    (hres : ∀ ℓ : Fin L, ∃ W' : Matrix d (A.r ℓ) ℝ, ∀ h : Matrix T d ℝ,
      rmsNorm ε (h * (↑(G ℓ.castSucc)⁻¹ : Matrix d d ℝ)) * θ.read ℓ = rmsNorm ε h * W')
    (hresD : ∃ D' : Matrix d dOut ℝ, ∀ h : Matrix T d ℝ,
      rmsNorm ε (h * (↑(G (Fin.last L))⁻¹ : Matrix d d ℝ)) * θ.D = rmsNorm ε h * D') :
    ∀ ℓ, (skipProdFwd S ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ := by
  sorry

end Skips
