import SkipsLean.Residual.GaugeFixLearned
import SkipsLean.Dimension.FunDimFamily
import SkipsLean.Symmetry.BiasesSymmetries

/-!
# The gauge fix with biases, for networks of mixed blocks and for learned skips

Paper (skips paper), Appendix A.2, after equation (12): "With biases, `Φ` also sends the
embedding bias `b_E` to `b_E Λ_0` and each write bias `b_write^ℓ` to `b_write^ℓ Λ_ℓ`, and keeps
each read bias." Theorem A.5 (ii): "The same holds for learned skips, without the `K_ℓ`, and for
networks with biases." Its proof: "Part (i), with biases and a skip bias. Merge the identity
units, `A_ℓ = U_ℓ V_ℓ`, and write the network as
`h_ℓ = h_{ℓ−1} A_ℓ + k_ℓ + f_ℓ(h_{ℓ−1} W_read^ℓ + b_read^ℓ) W_write^ℓ + b_write^ℓ` with
`h_0 = x E + b_E`, where `k_ℓ ∈ ℝ^{1 × d_model}` is a skip bias (`k_ℓ = 0` is allowed). […]
`b'_write^ℓ = (b_write^ℓ + k_ℓ) Λ_ℓ`"; "Part (ii). The identity units carry no biases of their
own, since these would only add to the write bias."

Here, in the frame of `Network/Biases.lean` (`evalB A S θ b`: the stream matrices `S` are the
skips, the block adds `f_ℓ(χ(h) W_read^ℓ + b_read^ℓ) W_write^ℓ + b_write^ℓ` to the stream). A
skip bias `k_ℓ` is added to the stream as `b_write^ℓ` is, so the network with a skip bias is the
network with the write bias `b_write^ℓ + k_ℓ`, and the statements below are those of the proof
with `k_ℓ` merged into the write bias.

* `Biases.mulSkipProd b Λ`: the biases `b_E Λ_0`, `b_read^ℓ`, `b_write^ℓ Λ_ℓ`, `b_D`.
* Networks of mixed blocks with biases: the parameters are the pairs `p = (θ, b)` of a parameter
  `θ` of `A.mixed` and the biases `b` of the embedding, of the hidden units and of the readout
  ("The identity units carry no biases of their own"); `evalMixedB A p x`; `mixedToResidualB p`,
  the map `Φ` with biases. `T_{G,K}` acts by `(θ.cobMixed G G K, b.cob G)`.
* Networks with learned skips and biases: the parameters are `p = ((θ, b), (A_ℓ))`, the function
  is `evalB A p.2 p.1.1 p.1.2`, and `learnedToResidualB p` is `Φ` with biases. `T_G` acts by
  `((θ.cob G G, b.cob G), cobSkip A G)`; that it preserves the function is `evalB_cob`
  (`Symmetry/BiasesSymmetries.lean`).
* For both: (i) the same function as the residual network with biases at `Φ(p)`; (ii) every
  parameter of the residual network with biases is a `Φ(p)`; `Φ(p̃) = Φ(p)` exactly when
  `p̃ = T(p)` with `G_L = I`; the derivative of `Φ` is onto; the same set of functions; and the
  same functional dimension at `p` and at `Φ(p)` (`funDimOf` of `Dimension/FunDimFamily.lean`
  for the family at hand, `funDimB` for the residual network with biases).

The model dimension is `d : Type`, as in `Residual/GaugeFixMixed.lean`.
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise

variable {T : Type*} {d : Type} {dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d]
  [DecidableEq d] [Fintype dIn] [Fintype dOut]
variable {A : Arch T d L}

/-- **The biases under the map `Φ`:** "`Φ` also sends the embedding bias `b_E` to `b_E Λ_0` and
each write bias `b_write^ℓ` to `b_write^ℓ Λ_ℓ`, and keeps each read bias"; the readout bias is
kept. -/
def Biases.mulSkipProd (b : Biases A dOut) (Λ : Fin (L + 1) → Matrix d d ℝ) : Biases A dOut where
  E := b.E ᵥ* Λ 0
  read := b.read
  write ℓ := b.write ℓ ᵥ* Λ ℓ.succ
  D := b.D

/-! ### Networks of mixed blocks with biases -/

/-- **The function of the network of mixed blocks with biases:** the network of `A` with the
learned skips `U_ℓ V_ℓ`, the hidden units of `θ` and the biases `b`; the identity units carry no
biases. -/
def evalMixedB (A : Arch T d L) (p : Params A.mixed dIn dOut × Biases A dOut)
    (x : Matrix T dIn ℝ) : Matrix T dOut ℝ :=
  evalB A (fun ℓ => p.1.mixU ℓ * p.1.mixV ℓ) p.1.unmix p.2 x

/-- **The map `Φ` of equation (12) with biases, for networks of mixed blocks.** -/
noncomputable def mixedToResidualB (p : Params A.mixed dIn dOut × Biases A dOut) :
    ParamsB A dIn dOut :=
  (mixedToResidual p.1, p.2.mulSkipProd (skipProdMat fun ℓ => p.1.mixU ℓ * p.1.mixV ℓ))

/-- **Theorem A.5 (i) with biases, "The maps `T_{G,K}` preserve the function":** without
normalization, with the embedding bias and the write biases multiplied as the embedding and the
writes are. -/
theorem evalMixedB_cobMixed (hA : A.χ = id) (p : Params A.mixed dIn dOut × Biases A dOut)
    (G : Fin (L + 1) → GL d ℝ) (K : Fin L → GL d ℝ) (x : Matrix T dIn ℝ) :
    evalMixedB A (p.1.cobMixed G G K, p.2.cob G) x = evalMixedB A p x := by
  sorry

/-- **Theorem A.5 (i) with biases, `F_θ = F^res_{Φ(θ)}`:** without normalization, a network of
mixed blocks with biases and invertible skips computes the function of the residual network with
biases at `Φ(p)`. -/
theorem evalMixedB_eq_evalB_mixedToResidualB (hA : A.χ = id)
    (p : Params A.mixed dIn dOut × Biases A dOut) (hp : ∀ ℓ, IsUnit (p.1.mixU ℓ * p.1.mixV ℓ))
    (x : Matrix T dIn ℝ) :
    evalMixedB A p x = evalB A 1 (mixedToResidualB p).1 (mixedToResidualB p).2 x := by
  sorry

/-- **Theorem A.5 (ii) with biases, "Every parameter of the residual network is `Φ(θ)` for some
`θ`".** -/
theorem mixedToResidualB_mix_one (q : ParamsB A dIn dOut) :
    mixedToResidualB (Params.mix q.1 1 1, q.2) = q := by
  sorry

/-- **Theorem A.5 (ii) with biases, "`Φ(θ̃) = Φ(θ)` exactly when `θ̃ = T_{G,K}(θ)` for some `G`
and `K` with `G_L = I`"**, for invertible skips. -/
theorem mixedToResidualB_eq_iff (p p' : Params A.mixed dIn dOut × Biases A dOut)
    (hp : ∀ ℓ, IsUnit (p.1.mixU ℓ * p.1.mixV ℓ))
    (hp' : ∀ ℓ, IsUnit (p'.1.mixU ℓ * p'.1.mixV ℓ)) :
    mixedToResidualB p' = mixedToResidualB p
      ↔ ∃ (G : Fin (L + 1) → GL d ℝ) (K : Fin L → GL d ℝ),
          G (Fin.last L) = 1 ∧ p' = (p.1.cobMixed G G K, p.2.cob G) := by
  sorry

/-- **Theorem A.5 (ii) with biases, "The derivative of `Φ` is onto at every `θ`"** (with
invertible skips). -/
theorem exists_hasFDerivAt_mixedToResidualB_surjective
    (p : Params A.mixed dIn dOut × Biases A dOut) (hp : ∀ ℓ, IsUnit (p.1.mixU ℓ * p.1.mixV ℓ)) :
    ∃ Φ' : (Params A.mixed dIn dOut × Biases A dOut) →L[ℝ] ParamsB A dIn dOut,
      HasFDerivAt (mixedToResidualB (A := A) (dIn := dIn) (dOut := dOut)) Φ' p
        ∧ Function.Surjective Φ' := by
  sorry

/-- **Theorem A.5 (ii) with biases, the same set of functions:** without normalization, the
networks of mixed blocks with biases and invertible skips and the residual networks with biases
compute the same set of functions. -/
theorem image_evalMixedB_eq_range_residual (hA : A.χ = id) :
    (fun p : Params A.mixed dIn dOut × Biases A dOut => evalMixedB A p)
        '' {p | ∀ ℓ, IsUnit (p.1.mixU ℓ * p.1.mixV ℓ)}
      = Set.range fun q : ParamsB A dIn dOut => evalB A 1 q.1 q.2 := by
  sorry

/-- **Theorem A.5 (ii) with biases, "with the same functional dimension at `θ` and at
`Φ(θ)`":** without normalization, for any blocks, at a parameter with invertible skips the
functional dimension of the network of mixed blocks with biases is that of the residual network
with biases at `Φ(p)`. -/
theorem funDimOf_evalMixedB_eq_funDimB_residual (hA : A.χ = id)
    (p : Params A.mixed dIn dOut × Biases A dOut) (hp : ∀ ℓ, IsUnit (p.1.mixU ℓ * p.1.mixV ℓ)) :
    funDimOf (evalMixedB A) p = funDimB A 1 (mixedToResidualB p) := by
  sorry

/-! ### Networks with learned skips and biases -/

/-- **The map `Φ` of equation (12) with biases, for learned skips:** at `p = ((θ, b), (A_ℓ))`. -/
noncomputable def learnedToResidualB (p : ParamsB A dIn dOut × (Fin L → Matrix d d ℝ)) :
    ParamsB A dIn dOut :=
  (learnedToResidual (p.1.1, p.2), p.1.2.mulSkipProd (skipProdMat p.2))

/-- **Theorem A.5 (i) with biases for learned skips, `F_θ = F^res_{Φ(θ)}`:** without
normalization, a network with biases and invertible learned skips computes the function of the
residual network with biases at `Φ(p)`. -/
theorem evalB_eq_evalB_learnedToResidualB (hA : A.χ = id)
    (p : ParamsB A dIn dOut × (Fin L → Matrix d d ℝ)) (hp : ∀ ℓ, IsUnit (p.2 ℓ))
    (x : Matrix T dIn ℝ) :
    evalB A p.2 p.1.1 p.1.2 x
      = evalB A 1 (learnedToResidualB p).1 (learnedToResidualB p).2 x := by
  sorry

/-- **Theorem A.5 (ii) with biases for learned skips:** every parameter of the residual network
with biases is `Φ` of the same weights and biases with the skips `A_ℓ = I`. -/
theorem learnedToResidualB_one (q : ParamsB A dIn dOut) :
    learnedToResidualB (q, (1 : Fin L → Matrix d d ℝ)) = q := by
  sorry

/-- **Theorem A.5 (ii) with biases for learned skips, "`Φ(θ̃) = Φ(θ)` exactly when
`θ̃ = T_G(θ)` for some `G` with `G_L = I`"**, for invertible skips. -/
theorem learnedToResidualB_eq_iff (p p' : ParamsB A dIn dOut × (Fin L → Matrix d d ℝ))
    (hp : ∀ ℓ, IsUnit (p.2 ℓ)) (hp' : ∀ ℓ, IsUnit (p'.2 ℓ)) :
    learnedToResidualB p' = learnedToResidualB p
      ↔ ∃ G : Fin (L + 1) → GL d ℝ,
          G (Fin.last L) = 1 ∧ p' = ((p.1.1.cob G G, p.1.2.cob G), cobSkip p.2 G) := by
  sorry

/-- **Theorem A.5 (ii) with biases for learned skips, the derivative of `Φ` is onto** (with
invertible skips). -/
theorem exists_hasFDerivAt_learnedToResidualB_surjective
    (p : ParamsB A dIn dOut × (Fin L → Matrix d d ℝ)) (hp : ∀ ℓ, IsUnit (p.2 ℓ)) :
    ∃ Φ' : (ParamsB A dIn dOut × (Fin L → Matrix d d ℝ)) →L[ℝ] ParamsB A dIn dOut,
      HasFDerivAt (learnedToResidualB (A := A) (dIn := dIn) (dOut := dOut)) Φ' p
        ∧ Function.Surjective Φ' := by
  sorry

/-- **Theorem A.5 (ii) with biases for learned skips, the same set of functions**, without
normalization. -/
theorem image_evalB_learned_eq_range_residual (hA : A.χ = id) :
    (fun p : ParamsB A dIn dOut × (Fin L → Matrix d d ℝ) => evalB A p.2 p.1.1 p.1.2)
        '' {p | ∀ ℓ, IsUnit (p.2 ℓ)}
      = Set.range fun q : ParamsB A dIn dOut => evalB A 1 q.1 q.2 := by
  sorry

/-- **Theorem A.5 (ii) with biases for learned skips, the same functional dimension:** without
normalization, for any blocks, at weights, biases and invertible skips `p`, the functional
dimension of the network with learned skips and biases (in the weights, the biases and the
skips) is that of the residual network with biases at `Φ(p)`. -/
theorem funDimOf_evalB_learned_eq_funDimB_residual (hA : A.χ = id)
    (p : ParamsB A dIn dOut × (Fin L → Matrix d d ℝ)) (hp : ∀ ℓ, IsUnit (p.2 ℓ)) :
    funDimOf (fun q : ParamsB A dIn dOut × (Fin L → Matrix d d ℝ) => evalB A q.2 q.1.1 q.1.2) p
      = funDimB A 1 (learnedToResidualB p) := by
  sorry

end Skips
