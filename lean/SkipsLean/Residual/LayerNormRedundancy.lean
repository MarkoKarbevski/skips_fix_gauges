import SkipsLean.Network.LayerNorm
import SkipsLean.Dimension.FunDimFamily

/-!
# LayerNorm: the difference in redundancy between skipless and residual networks

Paper (skips paper), Proposition A.15 (iii): "If the gains `γ` have nonzero entries, the
difference in redundancy between the skipless and the residual version of the LayerNorm network
equals the difference for the reduced networks of (ii)." Its proof: "The reduced parameters are
`√(d_model/(d_model − 1)) Ū^⊤ diag(γ) W` and `b + β W` for each read, `W Ū` and `b Ū` for each
write, `E Ū` for the embedding, and the analogous expressions for the readout. For `γ` with
nonzero entries each is linear and onto in `W`, `b` or `E`, so the derivative of the map from the
parameters of the LayerNorm network to those of the reduced network is onto. The LayerNorm
network computes the reduced network's function composed with this map, so by the chain rule
every batch Jacobian of the LayerNorm network is that of the reduced network times this
derivative, and at corresponding parameters both have the same functional dimension, and the
redundancy of the LayerNorm network is that of the reduced network plus the difference of the
parameter counts. That difference is the same for the skipless and the residual versions, which
have the same shapes."

Here, for the pre-LayerNorm networks of `Network/LayerNorm.lean` (any blocks, with biases):

* `ParamsLN A d_in d_out`: the parameters of a pre-LayerNorm network, the weights and biases
  with the gains `γ_ℓ` and the biases `β_ℓ` of its `L + 1` LayerNorms; `evalLNParams`: its
  function as a family in these parameters; `reduceLNParams ε U q`: "the map from the parameters
  of the LayerNorm network to those of the reduced network".
* `exists_hasFDerivAt_reduceLNParams_surjective`: for gains with nonzero entries its derivative
  is onto.
* `funDimOf_evalLNParams_eq_funDimB_reduceLN`: "at corresponding parameters both have the same
  functional dimension", for stream matrices that commute with `Z`; no differentiability of the
  blocks is asked (`Dimension/FunDimFamily.lean`).
* `funDimOf_evalLNParams_skipless`, `funDimOf_evalLNParams_residual`: the same by name;
  `funDimOf_evalLNParams_residual_add_skipless`: part (iii). The redundancy is the number of
  parameters minus the functional dimension, and the skipless and the residual version have the
  same parameters, so the statement on the differences of the redundancies is the statement
  that the functional dimension rises by the same amount from the skipless to the residual
  version in the LayerNorm network and in the reduced network; it is written without
  subtraction.

Numeric check: `layernorm_reduction_check_2026-11-25.py`, part (iii) (six cases; the rank is
read at the largest gap of the singular values).
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise

variable {T d m dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype m]
  [DecidableEq m] [Fintype dIn] [Fintype dOut]
variable {A : Arch T d L}

/-- **The parameters of a pre-LayerNorm network:** the weights and the biases, and the gains
`γ_0, …, γ_L` and the biases `β_0, …, β_L` of its LayerNorms. -/
abbrev ParamsLN (A : Arch T d L) (dIn dOut : Type*) : Type _ :=
  ParamsB A dIn dOut × ((Fin (L + 1) → d → ℝ) × (Fin (L + 1) → d → ℝ))

/-- The function of the pre-LayerNorm network at the parameters `q = ((θ, b), (γ, β))`. -/
noncomputable def evalLNParams (A : Arch T d L) (ε : ℝ) (S : Fin L → Matrix d d ℝ)
    (q : ParamsLN A dIn dOut) (x : Matrix T dIn ℝ) : Matrix T dOut ℝ :=
  evalLN A ε S q.1.1 q.1.2 q.2.1 q.2.2 x

/-- **"The map from the parameters of the LayerNorm network to those of the reduced network"**
of Proposition A.15 (ii), for a matrix `U` whose columns are an orthonormal basis of `V`. -/
noncomputable def reduceLNParams (ε : ℝ) (U : Matrix d m ℝ) (q : ParamsLN A dIn dOut) :
    ParamsB (A.withNorm (rmsNorm (T := T) (d := m)
      (ε * (Fintype.card d : ℝ) / (Fintype.card m : ℝ)))) dIn dOut :=
  (q.1.1.reduceLN ε U q.2.1, q.1.2.reduceLN ε U q.1.1 q.2.2)

/-- **Proof of Proposition A.15 (iii), "the derivative of the map from the parameters of the
LayerNorm network to those of the reduced network is onto"**, at gains with nonzero entries, for
`U` with orthonormal columns. -/
theorem exists_hasFDerivAt_reduceLNParams_surjective (ε : ℝ) (U : Matrix d m ℝ)
    (hU : Uᵀ * U = 1) (q : ParamsLN A dIn dOut) (hγ : ∀ ℓ i, q.2.1 ℓ i ≠ 0) :
    ∃ Φ' : ParamsLN A dIn dOut →L[ℝ] ParamsB (A.withNorm (rmsNorm (T := T) (d := m)
        (ε * (Fintype.card d : ℝ) / (Fintype.card m : ℝ)))) dIn dOut,
      HasFDerivAt (reduceLNParams (A := A) (dIn := dIn) (dOut := dOut) (T := T) ε U) Φ' q
        ∧ Function.Surjective Φ' := by
  sorry

/-- **Proof of Proposition A.15 (iii), "at corresponding parameters both have the same
functional dimension":** let the columns of `U` be an orthonormal basis of `V`, with at least one
column, and let the stream matrices commute with `Z`. At gains with nonzero entries, the
functional dimension of the pre-LayerNorm network, in all its parameters, is that of the reduced
pre-RMSNorm network of dimension `m` with biases at the reduced parameters. -/
theorem funDimOf_evalLNParams_eq_funDimB_reduceLN (ε : ℝ) (U : Matrix d m ℝ)
    (hU : Uᵀ * U = 1) (hUZ : U * Uᵀ = centering d) (hm : 0 < Fintype.card m)
    (S : Fin L → Matrix d d ℝ) (hS : ∀ ℓ, centering d * S ℓ = S ℓ * centering d)
    (q : ParamsLN A dIn dOut) (hγ : ∀ ℓ i, q.2.1 ℓ i ≠ 0) :
    funDimOf (evalLNParams A ε S) q
      = funDimB (A.withNorm (rmsNorm (ε * (Fintype.card d : ℝ) / (Fintype.card m : ℝ))))
          (fun ℓ => Uᵀ * S ℓ * U) (reduceLNParams ε U q) := by
  sorry

/-- The same for a skipless pre-LayerNorm network and the skipless reduced network. -/
theorem funDimOf_evalLNParams_skipless (ε : ℝ) (U : Matrix d m ℝ)
    (hU : Uᵀ * U = 1) (hUZ : U * Uᵀ = centering d) (hm : 0 < Fintype.card m)
    (q : ParamsLN A dIn dOut) (hγ : ∀ ℓ i, q.2.1 ℓ i ≠ 0) :
    funDimOf (evalLNParams A ε 0) q
      = funDimB (A.withNorm (rmsNorm (ε * (Fintype.card d : ℝ) / (Fintype.card m : ℝ))))
          0 (reduceLNParams ε U q) := by
  have h := funDimOf_evalLNParams_eq_funDimB_reduceLN ε U hU hUZ hm (0 : Fin L → Matrix d d ℝ)
    (fun ℓ => by simp) q hγ
  have h0 : (fun ℓ => Uᵀ * (0 : Fin L → Matrix d d ℝ) ℓ * U) = (0 : Fin L → Matrix m m ℝ) := by
    funext ℓ
    simp
  rwa [h0] at h

/-- The same for a residual pre-LayerNorm network and the residual reduced network. -/
theorem funDimOf_evalLNParams_residual (ε : ℝ) (U : Matrix d m ℝ)
    (hU : Uᵀ * U = 1) (hUZ : U * Uᵀ = centering d) (hm : 0 < Fintype.card m)
    (q : ParamsLN A dIn dOut) (hγ : ∀ ℓ i, q.2.1 ℓ i ≠ 0) :
    funDimOf (evalLNParams A ε 1) q
      = funDimB (A.withNorm (rmsNorm (ε * (Fintype.card d : ℝ) / (Fintype.card m : ℝ))))
          1 (reduceLNParams ε U q) := by
  have h := funDimOf_evalLNParams_eq_funDimB_reduceLN ε U hU hUZ hm (1 : Fin L → Matrix d d ℝ)
    (fun ℓ => by simp) q hγ
  have h1 : (fun ℓ => Uᵀ * (1 : Fin L → Matrix d d ℝ) ℓ * U) = (1 : Fin L → Matrix m m ℝ) := by
    funext ℓ
    simp [hU]
  rwa [h1] at h

/-- **Proposition A.15 (iii):** if the gains have nonzero entries, the functional dimension
rises by the same amount from the skipless to the residual version in the pre-LayerNorm network
and in the reduced networks of (ii); as both versions have the same parameters, this is "the
difference in redundancy between the skipless and the residual version of the LayerNorm network
equals the difference for the reduced networks". -/
theorem funDimOf_evalLNParams_residual_add_skipless (ε : ℝ) (U : Matrix d m ℝ)
    (hU : Uᵀ * U = 1) (hUZ : U * Uᵀ = centering d) (hm : 0 < Fintype.card m)
    (q : ParamsLN A dIn dOut) (hγ : ∀ ℓ i, q.2.1 ℓ i ≠ 0) :
    funDimOf (evalLNParams A ε 1) q
        + funDimB (A.withNorm (rmsNorm (ε * (Fintype.card d : ℝ) / (Fintype.card m : ℝ))))
          0 (reduceLNParams ε U q)
      = funDimOf (evalLNParams A ε 0) q
        + funDimB (A.withNorm (rmsNorm (ε * (Fintype.card d : ℝ) / (Fintype.card m : ℝ))))
          1 (reduceLNParams ε U q) := by
  rw [funDimOf_evalLNParams_skipless ε U hU hUZ hm q hγ,
    funDimOf_evalLNParams_residual ε U hU hUZ hm q hγ, add_comm]

end Skips
