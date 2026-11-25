import SkipsLean.Network.Mixed
import SkipsLean.Residual.LearnedSkips

/-!
# Junctions of a network of mixed blocks, and the gauge fix: same function

Paper (skips paper), Proposition A.1 (Junctions): "(i) Only `U V` matters. In a mixed block,
`(U, V) ↦ (U K, K^{-1} V)` preserves the function for every `K ∈ GL(d_model)`. (ii) Hidden states
are junctions. In a skipless network, and in a network of mixed blocks, the map `W ↦ W G` on the
matrices that write a hidden state and `W ↦ G^{-1} W` on those that read it preserves the
function for every `G ∈ 𝒢`. For `ε = 0` and `G = cQ`, a read through RMSNorm maps to `Q^⊤ W`
instead. (iii) One group per junction. The maps of (i) and (ii) commute when they act at
different junctions. A skipless network therefore carries one copy of `𝒢` per hidden state, and a
network of mixed blocks one more copy of `GL(d_model)` per block."

Appendix A.2, equation (11): "For invertible `G_0, …, G_L` and `K_1, …, K_L`, let `T_{G,K}` be
the map `E ↦ E G_0`, `W_read^ℓ ↦ G_{ℓ−1}^{-1} W_read^ℓ`, `W_write^ℓ ↦ W_write^ℓ G_ℓ`,
`D ↦ G_L^{-1} D`, `U_ℓ ↦ G_{ℓ−1}^{-1} U_ℓ K_ℓ`, `V_ℓ ↦ K_ℓ^{-1} V_ℓ G_ℓ`, which applies the
change of basis `G_ℓ` at `h_ℓ` and `K_ℓ` at the identity units of block `ℓ`." Theorem A.5 (i):
"Same function. The maps `T_{G,K}` preserve the function. With `G_ℓ = Λ_ℓ` and
`K_ℓ = U_ℓ^{-1} Λ_{ℓ−1}`, `T_{G,K}` sets every `U_ℓ` and `V_ℓ` to `I` and the other parameters to
`Φ(θ)`, so `F_θ = F^res_{Φ(θ)}`."

Here, for the networks of mixed blocks of `Network/Mixed.lean` (any architecture, any `χ`):

* `θ.mixK K`: the map of (i); `θ.cobMixed G Q K`: the map `T_{G,K}` of (11), in which the reads
  of the hidden units and the readout, which read `χ(h)`, are multiplied by `Q^{-1}` (`Q = G`
  without normalization; the identity units read `h` itself and always get `G^{-1}`).
* `evalMixed_mixK`: (i). `evalMixed_cobMixed`: `T_{G,K}` preserves the function whenever
  `χ(h G_ℓ) = χ(h) Q_ℓ`; by name without normalization (every invertible `G`), under pre-RMSNorm
  with `ε > 0` (orthogonal `Q`), and with `ε = 0` (`G = c Q`: "a read through RMSNorm maps to
  `Q^⊤ W` instead").
* (iii): `cobMixed_cobMixed`, the maps compose as the product group
  `GL(d)^{L+1} × GL(d)^{L+1} × GL(d)^L` does, one factor per junction; `cobMixed_comm`, two of
  them commute when their matrices commute at every junction, in particular when they act at
  different junctions; `cobMixed_one_one`: the map of (i) is `T_{1,K}`.
* Theorem A.5 (i): `cobMixed_skipProd`, the gauge fix sets every `U_ℓ` and `V_ℓ` to `I` and the
  other parameters to `Φ(θ) = θ.cob Λ Λ` (`Residual/LearnedSkips.lean`: `skipProd`);
  `evalMixed_eq_residual`, `F_θ = F^res_{Φ(θ)}`.

Numeric check: `mixed_blocks_check_2026-11-25.py`, parts (1) and (2). What the gauge fix
identifies (Theorem A.5 (ii)): `Residual/GaugeFixMixed.lean`.
-/

namespace Skips

open Matrix

variable {T : Type*} {d : Type} {dIn dOut : Type*} {L : ℕ} [Fintype d] [DecidableEq d]
  [Fintype dIn]
variable {A : Arch T d L}

/-- **The map of Proposition A.1 (i):** `(U_ℓ, V_ℓ) ↦ (U_ℓ K_ℓ, K_ℓ^{-1} V_ℓ)` at the identity
units of every block; the other parameters do not move. -/
def Params.mixK (θ : Params A.mixed dIn dOut) (K : Fin L → GL d ℝ) : Params A.mixed dIn dOut :=
  Params.mix θ.unmix (fun ℓ => θ.mixU ℓ * (K ℓ : Matrix d d ℝ))
    (fun ℓ => (↑(K ℓ)⁻¹ : Matrix d d ℝ) * θ.mixV ℓ)

/-- **The map `T_{G,K}` of equation (11):** the change of basis `G_ℓ` at the hidden state `h_ℓ`
and `K_ℓ` at the identity units of block `ℓ`. The reads of the hidden units and the readout,
which read `χ(h)`, are multiplied by `Q^{-1}`: `Q = G` without normalization. -/
def Params.cobMixed (θ : Params A.mixed dIn dOut) (G Q : Fin (L + 1) → GL d ℝ)
    (K : Fin L → GL d ℝ) : Params A.mixed dIn dOut :=
  Params.mix (θ.unmix.cob G Q)
    (fun ℓ => (↑(G ℓ.castSucc)⁻¹ : Matrix d d ℝ) * θ.mixU ℓ * (K ℓ : Matrix d d ℝ))
    (fun ℓ => (↑(K ℓ)⁻¹ : Matrix d d ℝ) * θ.mixV ℓ * (G ℓ.succ : Matrix d d ℝ))

variable (θ : Params A.mixed dIn dOut) (x : Matrix T dIn ℝ)

/-- **Proposition A.1 (i), "Only `U V` matters":** in a network of mixed blocks,
`(U, V) ↦ (U K, K^{-1} V)` preserves the function for every `K ∈ GL(d)`, for every `χ`. -/
theorem evalMixed_mixK (K : Fin L → GL d ℝ) :
    evalMixed A (θ.mixK K) x = evalMixed A θ x := by
  sorry

/-- **The maps `T_{G,K}` preserve the function** (Proposition A.1 (ii) for networks of mixed
blocks; Theorem A.5 (i), first sentence), whenever `χ(h G_ℓ) = χ(h) Q_ℓ` at every hidden
state. -/
theorem evalMixed_cobMixed (G Q : Fin (L + 1) → GL d ℝ) (K : Fin L → GL d ℝ)
    (hχ : ∀ ℓ (h : Matrix T d ℝ), A.χ (h * (G ℓ : Matrix d d ℝ)) = A.χ h * (Q ℓ : Matrix d d ℝ)) :
    evalMixed A (θ.cobMixed G Q K) x = evalMixed A θ x := by
  sorry

/-- **Proposition A.1 (ii) and Theorem A.5 (i), first sentence, without normalization:** every
`T_{G,K}` with invertible `G_0, …, G_L` and `K_1, …, K_L` preserves the function of a network of
mixed blocks. -/
theorem evalMixed_cobMixed_id (hA : A.χ = id) (G : Fin (L + 1) → GL d ℝ) (K : Fin L → GL d ℝ) :
    evalMixed A (θ.cobMixed G G K) x = evalMixed A θ x := by
  sorry

/-- **Proposition A.1 (ii) for networks of mixed blocks under pre-RMSNorm with `ε > 0` (any
`ε`):** orthogonal changes of basis `Q_ℓ` at the hidden states, with any invertible `K_ℓ` at the
identity units, preserve the function. -/
theorem evalMixed_cobMixed_rmsNorm (ε : ℝ) (hA : A.χ = rmsNorm ε) (Q : Fin (L + 1) → GL d ℝ)
    (hQ : ∀ ℓ, (Q ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ) (K : Fin L → GL d ℝ) :
    evalMixed A (θ.cobMixed Q Q K) x = evalMixed A θ x := by
  sorry

/-- **Proposition A.1 (ii) for networks of mixed blocks under RMSNorm with `ε = 0`:** for
`G_ℓ = c_ℓ Q_ℓ` with `c_ℓ > 0` and `Q_ℓ` orthogonal, the map that multiplies the writes into
`h_ℓ` by `G_ℓ`, the reads of the identity units by `G_ℓ^{-1}` and the reads through RMSNorm by
`Q_ℓ^{-1} = Q_ℓ^⊤` preserves the function. -/
theorem evalMixed_cobMixed_rmsNorm_zero (hA : A.χ = rmsNorm 0) (G Q : Fin (L + 1) → GL d ℝ)
    (c : Fin (L + 1) → ℝ) (hc : ∀ ℓ, 0 < c ℓ)
    (hQ : ∀ ℓ, (Q ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ)
    (hG : ∀ ℓ, (G ℓ : Matrix d d ℝ) = c ℓ • (Q ℓ : Matrix d d ℝ)) (K : Fin L → GL d ℝ) :
    evalMixed A (θ.cobMixed G Q K) x = evalMixed A θ x := by
  sorry

/-- The map of Proposition A.1 (i) is `T_{1,K}`. -/
theorem cobMixed_one_one (K : Fin L → GL d ℝ) : θ.cobMixed 1 1 K = θ.mixK K := by
  sorry

/-- **Proposition A.1 (iii), "One group per junction":** the maps `T_{G,K}` compose as the
product group does, with one factor per hidden state and one per block. -/
theorem cobMixed_cobMixed (G Q G' Q' : Fin (L + 1) → GL d ℝ) (K K' : Fin L → GL d ℝ) :
    (θ.cobMixed G Q K).cobMixed G' Q' K' = θ.cobMixed (G * G') (Q * Q') (K * K') := by
  sorry

/-- **Proposition A.1 (iii), "The maps of (i) and (ii) commute when they act at different
junctions":** two maps `T_{G,K}` commute when their matrices commute at every hidden state and at
the identity units of every block, in particular when at every junction one of the two is the
identity. -/
theorem cobMixed_comm (G Q G' Q' : Fin (L + 1) → GL d ℝ) (K K' : Fin L → GL d ℝ)
    (hG : ∀ ℓ, Commute (G ℓ) (G' ℓ)) (hQ : ∀ ℓ, Commute (Q ℓ) (Q' ℓ))
    (hK : ∀ ℓ, Commute (K ℓ) (K' ℓ)) :
    (θ.cobMixed G Q K).cobMixed G' Q' K' = (θ.cobMixed G' Q' K').cobMixed G Q K := by
  sorry

/-- **Proposition A.1 (iii) for a hidden state and the identity units of a block:** the change
of basis of (ii) and the map of (i) commute. -/
theorem cobMixed_mixK_comm (G Q : Fin (L + 1) → GL d ℝ) (K : Fin L → GL d ℝ) :
    (θ.cobMixed G Q 1).mixK K = (θ.mixK K).cobMixed G Q 1 := by
  sorry

/-- **Theorem A.5 (i), the gauge fix:** for a network of mixed blocks with invertible `U_ℓ` and
`V_ℓ`, the map `T_{G,K}` with `G_ℓ = Λ_ℓ` and `K_ℓ = U_ℓ^{-1} Λ_{ℓ−1}`, where
`Λ_ℓ = A_{ℓ+1} ⋯ A_L` and `A_ℓ = U_ℓ V_ℓ`, "sets every `U_ℓ` and `V_ℓ` to `I` and the other
parameters to `Φ(θ)`": `E Λ_0`, `Λ_{ℓ−1}^{-1} W_read^ℓ`, `W_write^ℓ Λ_ℓ`, `D`. -/
theorem cobMixed_skipProd (θ : Params A dIn dOut) (U V : Fin L → GL d ℝ) :
    (Params.mix θ (fun ℓ => (U ℓ : Matrix d d ℝ)) (fun ℓ => (V ℓ : Matrix d d ℝ))).cobMixed
        (skipProd fun ℓ => U ℓ * V ℓ) (skipProd fun ℓ => U ℓ * V ℓ)
        (fun ℓ => (U ℓ)⁻¹ * skipProd (fun ℓ => U ℓ * V ℓ) ℓ.castSucc)
      = Params.mix (θ.cob (skipProd fun ℓ => U ℓ * V ℓ) (skipProd fun ℓ => U ℓ * V ℓ)) 1 1 := by
  sorry

/-- **Theorem A.5 (i), "so `F_θ = F^res_{Φ(θ)}`":** without normalization, a network of mixed
blocks with invertible `U_ℓ` and `V_ℓ` computes the same function as the residual network with
the embedding `E Λ_0`, the reads `Λ_{ℓ−1}^{-1} W_read^ℓ`, the writes `W_write^ℓ Λ_ℓ` and the
readout `D`. -/
theorem evalMixed_eq_residual (hA : A.χ = id) (θ : Params A dIn dOut) (U V : Fin L → GL d ℝ)
    (x : Matrix T dIn ℝ) :
    evalMixed A (Params.mix θ (fun ℓ => (U ℓ : Matrix d d ℝ)) (fun ℓ => (V ℓ : Matrix d d ℝ))) x
      = eval A 1 (θ.cob (skipProd fun ℓ => U ℓ * V ℓ) (skipProd fun ℓ => U ℓ * V ℓ)) x := by
  sorry

end Skips
