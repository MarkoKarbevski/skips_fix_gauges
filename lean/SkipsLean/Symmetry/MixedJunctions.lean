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

omit [Fintype d] [DecidableEq d] [Fintype dIn] in
/-- Two parameters are equal if their four components are. -/
private theorem params_ext_mxj {B : Arch T d L} {φ ψ : Params B dIn dOut} (hE : φ.E = ψ.E)
    (hr : ∀ ℓ, φ.read ℓ = ψ.read ℓ) (hw : ∀ ℓ, φ.write ℓ = ψ.write ℓ) (hD : φ.D = ψ.D) :
    φ = ψ := by
  cases φ; cases ψ
  simp only [Params.mk.injEq]
  exact ⟨hE, funext hr, funext hw, hD⟩

omit [Fintype dIn] in
/-- The change of basis by `G = K = 1` is the identity. -/
private theorem cob_one_mxj (φ : Params A dIn dOut) : φ.cob 1 1 = φ := by
  refine params_ext_mxj ?_ (fun ℓ => ?_) (fun ℓ => ?_) ?_ <;>
    simp [Params.cob]

omit [Fintype dIn] in
/-- Two changes of basis are one change of basis (the products, hidden state by hidden state). -/
private theorem cob_cob_mxj (φ : Params A dIn dOut) (G K G' K' : Fin (L + 1) → GL d ℝ) :
    (φ.cob G K).cob G' K' = φ.cob (fun ℓ => G ℓ * G' ℓ) (fun ℓ => K ℓ * K' ℓ) := by
  refine params_ext_mxj ?_ (fun ℓ => ?_) (fun ℓ => ?_) ?_
  · simp [Params.cob, Matrix.mul_assoc]
  · simp [Params.cob, Matrix.mul_assoc, _root_.mul_inv_rev]
  · simp [Params.cob, Matrix.mul_assoc]
  · simp [Params.cob, Matrix.mul_assoc, _root_.mul_inv_rev]

variable (θ : Params A.mixed dIn dOut) (x : Matrix T dIn ℝ)

/-- **Proposition A.1 (i), "Only `U V` matters":** in a network of mixed blocks,
`(U, V) ↦ (U K, K^{-1} V)` preserves the function for every `K ∈ GL(d)`, for every `χ`. -/
theorem evalMixed_mixK (K : Fin L → GL d ℝ) :
    evalMixed A (θ.mixK K) x = evalMixed A θ x := by
  -- the skips are `U K K⁻¹ V = U V`, and the hidden units do not move
  unfold evalMixed Params.mixK
  rw [Params.mixU_mix, Params.mixV_mix, Params.unmix_mix]
  congr 1
  funext ℓ
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc (K ℓ : Matrix d d ℝ), Units.mul_inv, Matrix.one_mul]

/-- **The maps `T_{G,K}` preserve the function** (Proposition A.1 (ii) for networks of mixed
blocks; Theorem A.5 (i), first sentence), whenever `χ(h G_ℓ) = χ(h) Q_ℓ` at every hidden
state. -/
theorem evalMixed_cobMixed (G Q : Fin (L + 1) → GL d ℝ) (K : Fin L → GL d ℝ)
    (hχ : ∀ ℓ (h : Matrix T d ℝ), A.χ (h * (G ℓ : Matrix d d ℝ)) = A.χ h * (Q ℓ : Matrix d d ℝ)) :
    evalMixed A (θ.cobMixed G Q K) x = evalMixed A θ x := by
  -- the skips become `(G⁻¹ U K)(K⁻¹ V G) = G⁻¹ (U V) G` and the hidden units `θ.unmix.cob G Q`
  unfold evalMixed Params.cobMixed
  rw [Params.mixU_mix, Params.mixV_mix, Params.unmix_mix]
  have hskip : (fun ℓ => (↑(G ℓ.castSucc)⁻¹ : Matrix d d ℝ) * θ.mixU ℓ * (K ℓ : Matrix d d ℝ)
      * ((↑(K ℓ)⁻¹ : Matrix d d ℝ) * θ.mixV ℓ * (G ℓ.succ : Matrix d d ℝ)))
      = cobSkip (fun ℓ => θ.mixU ℓ * θ.mixV ℓ) G := by
    funext ℓ
    simp only [cobSkip, Matrix.mul_assoc, Units.mul_inv_cancel_left]
  -- so this is Proposition 3.2 in general form for the learned skips `U V`
  rw [hskip]
  exact eval_cob (M := fun ℓ => θ.mixU ℓ * θ.mixV ℓ) (θ := θ.unmix) (G := G) (K := Q) (x := x) hχ

/-- **Proposition A.1 (ii) and Theorem A.5 (i), first sentence, without normalization:** every
`T_{G,K}` with invertible `G_0, …, G_L` and `K_1, …, K_L` preserves the function of a network of
mixed blocks. -/
theorem evalMixed_cobMixed_id (hA : A.χ = id) (G : Fin (L + 1) → GL d ℝ) (K : Fin L → GL d ℝ) :
    evalMixed A (θ.cobMixed G G K) x = evalMixed A θ x := by
  -- without normalization `χ (h G_ℓ) = χ (h) G_ℓ` holds trivially
  refine evalMixed_cobMixed θ x G G K fun ℓ h => ?_
  simp only [hA, id_eq]

/-- **Proposition A.1 (ii) for networks of mixed blocks under pre-RMSNorm with `ε > 0` (any
`ε`):** orthogonal changes of basis `Q_ℓ` at the hidden states, with any invertible `K_ℓ` at the
identity units, preserve the function. -/
theorem evalMixed_cobMixed_rmsNorm (ε : ℝ) (hA : A.χ = rmsNorm ε) (Q : Fin (L + 1) → GL d ℝ)
    (hQ : ∀ ℓ, (Q ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ) (K : Fin L → GL d ℝ) :
    evalMixed A (θ.cobMixed Q Q K) x = evalMixed A θ x := by
  -- pre-RMSNorm commutes with every orthogonal `Q_ℓ` (Lemma A.1): `χ (h Q_ℓ) = χ (h) Q_ℓ`
  refine evalMixed_cobMixed θ x Q Q K fun ℓ h => ?_
  rw [hA]
  exact rmsNorm_mul_orthogonal ε (hQ ℓ) h

/-- **Proposition A.1 (ii) for networks of mixed blocks under RMSNorm with `ε = 0`:** for
`G_ℓ = c_ℓ Q_ℓ` with `c_ℓ > 0` and `Q_ℓ` orthogonal, the map that multiplies the writes into
`h_ℓ` by `G_ℓ`, the reads of the identity units by `G_ℓ^{-1}` and the reads through RMSNorm by
`Q_ℓ^{-1} = Q_ℓ^⊤` preserves the function. -/
theorem evalMixed_cobMixed_rmsNorm_zero (hA : A.χ = rmsNorm 0) (G Q : Fin (L + 1) → GL d ℝ)
    (c : Fin (L + 1) → ℝ) (hc : ∀ ℓ, 0 < c ℓ)
    (hQ : ∀ ℓ, (Q ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ)
    (hG : ∀ ℓ, (G ℓ : Matrix d d ℝ) = c ℓ • (Q ℓ : Matrix d d ℝ)) (K : Fin L → GL d ℝ) :
    evalMixed A (θ.cobMixed G Q K) x = evalMixed A θ x := by
  -- RMSNorm with `ε = 0` loses the scale `c_ℓ` (Lemma A.1): `χ (h G_ℓ) = χ (h) Q_ℓ`
  refine evalMixed_cobMixed θ x G Q K fun ℓ h => ?_
  rw [hA, hG ℓ]
  exact rmsNorm_zero_mul_smul_orthogonal (hc ℓ) (hQ ℓ) h

omit [Fintype dIn] in
/-- The map of Proposition A.1 (i) is `T_{1,K}`. -/
theorem cobMixed_one_one (K : Fin L → GL d ℝ) : θ.cobMixed 1 1 K = θ.mixK K := by
  -- `G = 1` multiplies nothing, and `θ.unmix.cob 1 1 = θ.unmix`
  unfold Params.cobMixed Params.mixK
  simp only [Pi.one_apply, inv_one, Units.val_one, Matrix.one_mul, Matrix.mul_one, cob_one_mxj]

omit [Fintype dIn] in
/-- **Proposition A.1 (iii), "One group per junction":** the maps `T_{G,K}` compose as the
product group does, with one factor per hidden state and one per block. -/
theorem cobMixed_cobMixed (G Q G' Q' : Fin (L + 1) → GL d ℝ) (K K' : Fin L → GL d ℝ) :
    (θ.cobMixed G Q K).cobMixed G' Q' K' = θ.cobMixed (G * G') (Q * Q') (K * K') := by
  -- the hidden units: two changes of basis are one, `cob_cob`
  unfold Params.cobMixed
  rw [Params.unmix_mix, Params.mixU_mix, Params.mixV_mix, cob_cob_mxj]
  -- the identity units: `G'⁻¹ (G⁻¹ U K) K' = (G G')⁻¹ U (K K')` and
  -- `K'⁻¹ (K⁻¹ V G) G' = (K K')⁻¹ V (G G')`
  congr 1
  · funext ℓ
    simp only [Pi.mul_apply, _root_.mul_inv_rev, Units.val_mul, Matrix.mul_assoc]
  · funext ℓ
    simp only [Pi.mul_apply, _root_.mul_inv_rev, Units.val_mul, Matrix.mul_assoc]

omit [Fintype dIn] in
/-- **Proposition A.1 (iii), "The maps of (i) and (ii) commute when they act at different
junctions":** two maps `T_{G,K}` commute when their matrices commute at every hidden state and at
the identity units of every block, in particular when at every junction one of the two is the
identity. -/
theorem cobMixed_comm (G Q G' Q' : Fin (L + 1) → GL d ℝ) (K K' : Fin L → GL d ℝ)
    (hG : ∀ ℓ, Commute (G ℓ) (G' ℓ)) (hQ : ∀ ℓ, Commute (Q ℓ) (Q' ℓ))
    (hK : ∀ ℓ, Commute (K ℓ) (K' ℓ)) :
    (θ.cobMixed G Q K).cobMixed G' Q' K' = (θ.cobMixed G' Q' K').cobMixed G Q K := by
  -- both sides are one map `T_{G,K}`, of the products in the two orders
  rw [cobMixed_cobMixed, cobMixed_cobMixed]
  congr 1
  · funext ℓ
    exact (hG ℓ).eq
  · funext ℓ
    exact (hQ ℓ).eq
  · funext ℓ
    exact (hK ℓ).eq

omit [Fintype dIn] in
/-- **Proposition A.1 (iii) for a hidden state and the identity units of a block:** the change
of basis of (ii) and the map of (i) commute. -/
theorem cobMixed_mixK_comm (G Q : Fin (L + 1) → GL d ℝ) (K : Fin L → GL d ℝ) :
    (θ.cobMixed G Q 1).mixK K = (θ.mixK K).cobMixed G Q 1 := by
  -- the map of (i) is `T_{1,K}`, and both sides are `T_{G,K}`
  rw [← cobMixed_one_one, ← cobMixed_one_one, cobMixed_cobMixed, cobMixed_cobMixed, mul_one,
    mul_one, one_mul, one_mul, one_mul, mul_one]

omit [Fintype dIn] in
/-- **Theorem A.5 (i), the gauge fix:** for a network of mixed blocks with invertible `U_ℓ` and
`V_ℓ`, the map `T_{G,K}` with `G_ℓ = Λ_ℓ` and `K_ℓ = U_ℓ^{-1} Λ_{ℓ−1}`, where
`Λ_ℓ = A_{ℓ+1} ⋯ A_L` and `A_ℓ = U_ℓ V_ℓ`, "sets every `U_ℓ` and `V_ℓ` to `I` and the other
parameters to `Φ(θ)`": `E Λ_0`, `Λ_{ℓ−1}^{-1} W_read^ℓ`, `W_write^ℓ Λ_ℓ`, `D`. -/
theorem cobMixed_skipProd (θ : Params A dIn dOut) (U V : Fin L → GL d ℝ) :
    (Params.mix θ (fun ℓ => (U ℓ : Matrix d d ℝ)) (fun ℓ => (V ℓ : Matrix d d ℝ))).cobMixed
        (skipProd fun ℓ => U ℓ * V ℓ) (skipProd fun ℓ => U ℓ * V ℓ)
        (fun ℓ => (U ℓ)⁻¹ * skipProd (fun ℓ => U ℓ * V ℓ) ℓ.castSucc)
      = Params.mix (θ.cob (skipProd fun ℓ => U ℓ * V ℓ) (skipProd fun ℓ => U ℓ * V ℓ)) 1 1 := by
  unfold Params.cobMixed
  rw [Params.unmix_mix, Params.mixU_mix, Params.mixV_mix]
  congr 1
  · -- `Λ_{ℓ-1}⁻¹ U_ℓ (U_ℓ⁻¹ Λ_{ℓ-1}) = I`
    funext ℓ
    rw [Pi.one_apply, ← Units.val_mul, ← Units.val_mul, ← Units.val_one]
    congr 1
    group
  · -- `(U_ℓ⁻¹ Λ_{ℓ-1})⁻¹ V_ℓ Λ_ℓ = Λ_{ℓ-1}⁻¹ U_ℓ V_ℓ Λ_ℓ = I`, since `Λ_{ℓ-1} = U_ℓ V_ℓ Λ_ℓ`
    funext ℓ
    rw [Pi.one_apply, ← Units.val_mul, ← Units.val_mul, ← Units.val_one]
    congr 1
    simp only [skipProd_castSucc]
    group

/-- **Theorem A.5 (i), "so `F_θ = F^res_{Φ(θ)}`":** without normalization, a network of mixed
blocks with invertible `U_ℓ` and `V_ℓ` computes the same function as the residual network with
the embedding `E Λ_0`, the reads `Λ_{ℓ−1}^{-1} W_read^ℓ`, the writes `W_write^ℓ Λ_ℓ` and the
readout `D`. -/
theorem evalMixed_eq_residual (hA : A.χ = id) (θ : Params A dIn dOut) (U V : Fin L → GL d ℝ)
    (x : Matrix T dIn ℝ) :
    evalMixed A (Params.mix θ (fun ℓ => (U ℓ : Matrix d d ℝ)) (fun ℓ => (V ℓ : Matrix d d ℝ))) x
      = eval A 1 (θ.cob (skipProd fun ℓ => U ℓ * V ℓ) (skipProd fun ℓ => U ℓ * V ℓ)) x := by
  -- the network of mixed blocks is the network with the learned skips `A_ℓ = U_ℓ V_ℓ`
  unfold evalMixed
  rw [Params.mixU_mix, Params.mixV_mix, Params.unmix_mix]
  -- Theorem 3.2 (i) for these skips
  have h := eval_learned_eq_residual (θ := θ) (x := x) hA (fun ℓ => U ℓ * V ℓ)
  simp only [Units.val_mul] at h
  exact h

end Skips
