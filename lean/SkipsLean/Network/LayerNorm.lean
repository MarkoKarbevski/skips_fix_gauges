import SkipsLean.Basic.LayerNorm
import SkipsLean.Network.Biases

/-!
# Pre-LayerNorm networks and their reduction to pre-RMSNorm networks

Paper (dimension paper), Proposition A.3 (LayerNorm reduces to RMSNorm): "Let `1` be the column
of `d_model` ones, `Z = I − (1/d_model) 1 1^⊤`, and `V` the space of the rows `h` with `h 1 = 0`.
Consider a pre-LayerNorm network, whose reads and readout see `LN(h) = γ ⊙ N_ε(hZ) + β`, with
rows `γ` and `β` and the entrywise product `⊙`. (i) Replacing each read `W` by `diag(γ) W` with
the added bias `β W`, and each write `W`, write bias `b` and embedding `E` by `W Z`, `b Z` and
`E Z`, gives a network that computes the same function, whose hidden states lie in `V`, and whose
reads see `N_ε(h)`. (ii) In an orthonormal basis of `V`, this network is a pre-RMSNorm network of
dimension `d_model − 1`, with every read multiplied by `√(d_model/(d_model − 1))` and `ε`
replaced by `ε d_model/(d_model − 1)`." The skips paper, Proposition A.15 (i) and (ii), is the
same statement for "a pre-LayerNorm network, skipless or residual"; its proof: "Every hidden
state is a sum of writes, directly in a skipless network and through the skips in a residual
one".

Here, once for both papers, in the frame with biases of `Network/Biases.lean`:

* `layerNorm ε γ β h = N_ε(h Z) diag(γ) + β`, on every token; `A.withNorm χ'`: the architecture
  with the blocks of `A` and the fixed map `χ'`, on any model dimension.
* `hiddenLN`, `evalLN A ε S θ b γ β x`: the pre-LayerNorm network with the blocks of `A`, the
  weights `θ`, the biases `b`, the stream matrices `S` (`0` skipless, `1` residual), and one
  LayerNorm with gain `γ_ℓ` and bias `β_ℓ` before the read of every block and before the readout
  (`ℓ = 0, …, L`, at the hidden state `h_ℓ`).
* (i) `θ.centerLN ε γ`, `b.centerLN ε θ β`: the weights `E Z`, `diag(γ_ℓ) W_read`, `W_write Z`,
  `diag(γ_L) D` and the biases `b_E Z`, `b_read + β_ℓ W_read`, `b_write Z`, `b_D + β_L D` of a
  pre-RMSNorm network; `evalLN_eq_evalB_centerLN`: it computes the same function, for stream
  matrices that commute with `Z` (so for skipless and residual networks, by name);
  `sum_hiddenB_centerLN`: its hidden states have mean zero.
* (ii) for a matrix `U` with orthonormal columns that span `V` (`U^⊤ U = I`, `U U^⊤ = Z`):
  `θ.reduceLN ε U γ`, `b.reduceLN ε U θ β`, the weights `E U`, `√(d/m) U^⊤ diag(γ_ℓ) W_read`,
  `W_write U`, `√(d/m) U^⊤ diag(γ_L) D` and the biases `b_E U`, `b_read + β_ℓ W_read`,
  `b_write U`, `b_D + β_L D`; `evalLN_eq_evalB_reduceLN`: the pre-RMSNorm network of dimension
  `m` with the constant `ε d/m` and these parameters computes the same function (stream
  `U^⊤ S U`); by name for skipless and residual networks. Such a `U` exists and has
  `m = d − 1` columns.

The read of a block also keeps its own bias `b_read`, to which `β W` is added. Numeric check:
`layernorm_reduction_check_2026-11-25.py`, parts (i) and (ii). Part (iii) of Proposition A.15:
`Residual/LayerNormRedundancy.lean`.
-/

namespace Skips

open Matrix

variable {T d m dIn dOut : Type*} {L : ℕ} [Fintype d] [DecidableEq d] [Fintype m] [DecidableEq m]
  [Fintype dIn]

/-- **LayerNorm with the gain `γ` and the bias `β`:** `LN(h) = γ ⊙ N_ε(h Z) + β` on every row
(token) of `h`, with `Z` the centering matrix. -/
noncomputable def layerNorm (ε : ℝ) (γ β : d → ℝ) (h : Matrix T d ℝ) : Matrix T d ℝ :=
  rmsNorm ε (h * centering d) * Matrix.diagonal γ + Matrix.of fun _ => β

/-- The architecture with the blocks of `A` and the fixed map `χ'` before the reads and the
readout, on a model dimension `d'` (the blocks do not depend on the model dimension). -/
abbrev Arch.withNorm {d' : Type*} (A : Arch T d L) (χ' : Matrix T d' ℝ → Matrix T d' ℝ) :
    Arch T d' L where
  r := A.r
  w := A.w
  f := A.f
  χ := χ'

variable {A : Arch T d L}

/-- **The hidden states of a pre-LayerNorm network with biases:** `h_0 = x E + b_E` and
`h_{ℓ+1} = h_ℓ S_ℓ + f_ℓ(LN_ℓ(h_ℓ) W_read + b_read) W_write + b_write`, where `LN_ℓ` has the gain
`γ_ℓ` and the bias `β_ℓ`. The fixed map `χ` of `A` is not used. -/
noncomputable def hiddenLN (A : Arch T d L) (ε : ℝ) (S : Fin L → Matrix d d ℝ)
    (θ : Params A dIn dOut) (b : Biases A dOut) (γ β : Fin (L + 1) → d → ℝ)
    (x : Matrix T dIn ℝ) : Fin (L + 1) → Matrix T d ℝ :=
  Fin.induction (motive := fun _ => Matrix T d ℝ) (x * θ.E + Matrix.of fun _ => b.E)
    (fun ℓ h => h * S ℓ
      + (A.f ℓ (layerNorm ε (γ ℓ.castSucc) (β ℓ.castSucc) h * θ.read ℓ
          + Matrix.of fun _ => b.read ℓ) * θ.write ℓ + Matrix.of fun _ => b.write ℓ))

/-- **The function of a pre-LayerNorm network with biases:** `y = LN_L(h_L) D + b_D`. -/
noncomputable def evalLN (A : Arch T d L) (ε : ℝ) (S : Fin L → Matrix d d ℝ)
    (θ : Params A dIn dOut) (b : Biases A dOut) (γ β : Fin (L + 1) → d → ℝ)
    (x : Matrix T dIn ℝ) : Matrix T dOut ℝ :=
  layerNorm ε (γ (Fin.last L)) (β (Fin.last L)) (hiddenLN A ε S θ b γ β x (Fin.last L)) * θ.D
    + Matrix.of fun _ => b.D

/-! ### Part (i): the centred pre-RMSNorm network -/

/-- **Proposition A.3 (i), the weights:** "Replacing each read `W` by `diag(γ) W` […] and each
write `W` […] and embedding `E` by `W Z` […] and `E Z`"; the readout, which also reads through
a LayerNorm, becomes `diag(γ_L) D`. -/
noncomputable def Params.centerLN (ε : ℝ) (θ : Params A dIn dOut) (γ : Fin (L + 1) → d → ℝ) :
    Params (A.withNorm (rmsNorm (T := T) (d := d) ε)) dIn dOut where
  E := θ.E * centering d
  read ℓ := Matrix.diagonal (γ ℓ.castSucc) * θ.read ℓ
  write ℓ := θ.write ℓ * centering d
  D := Matrix.diagonal (γ (Fin.last L)) * θ.D

/-- **Proposition A.3 (i), the biases:** "with the added bias `β W`" on every read and on the
readout, and the write biases and the embedding bias replaced by `b Z`. -/
noncomputable def Biases.centerLN (ε : ℝ) (b : Biases A dOut) (θ : Params A dIn dOut)
    (β : Fin (L + 1) → d → ℝ) : Biases (A.withNorm (rmsNorm (T := T) (d := d) ε)) dOut where
  E := b.E ᵥ* centering d
  read ℓ := b.read ℓ + β ℓ.castSucc ᵥ* θ.read ℓ
  write ℓ := b.write ℓ ᵥ* centering d
  D := b.D + β (Fin.last L) ᵥ* θ.D

/-- **Proposition A.3 (i) / A.15 (i), "gives a network that computes the same function":** for
stream matrices that commute with `Z`, the pre-LayerNorm network computes the function of the
pre-RMSNorm network with the centred weights and biases. -/
theorem evalLN_eq_evalB_centerLN (ε : ℝ) (S : Fin L → Matrix d d ℝ)
    (hS : ∀ ℓ, centering d * S ℓ = S ℓ * centering d) (θ : Params A dIn dOut)
    (b : Biases A dOut) (γ β : Fin (L + 1) → d → ℝ) (x : Matrix T dIn ℝ) :
    evalLN A ε S θ b γ β x
      = evalB (A.withNorm (rmsNorm ε)) S (θ.centerLN ε γ) (b.centerLN ε θ β) x := by
  sorry

/-- **Proposition A.3 (i) for a skipless pre-LayerNorm network.** -/
theorem evalLN_eq_evalB_centerLN_skipless (ε : ℝ) (θ : Params A dIn dOut) (b : Biases A dOut)
    (γ β : Fin (L + 1) → d → ℝ) (x : Matrix T dIn ℝ) :
    evalLN A ε 0 θ b γ β x
      = evalB (A.withNorm (rmsNorm ε)) 0 (θ.centerLN ε γ) (b.centerLN ε θ β) x := by
  sorry

/-- **Proposition A.15 (i) for a residual pre-LayerNorm network.** -/
theorem evalLN_eq_evalB_centerLN_residual (ε : ℝ) (θ : Params A dIn dOut) (b : Biases A dOut)
    (γ β : Fin (L + 1) → d → ℝ) (x : Matrix T dIn ℝ) :
    evalLN A ε 1 θ b γ β x
      = evalB (A.withNorm (rmsNorm ε)) 1 (θ.centerLN ε γ) (b.centerLN ε θ β) x := by
  sorry

/-- **Proposition A.3 (i), "whose hidden states lie in `V`":** for stream matrices that commute
with `Z` (skipless and residual networks among them), every row of every hidden state of the
centred network has mean zero. -/
theorem sum_hiddenB_centerLN (ε : ℝ) (S : Fin L → Matrix d d ℝ)
    (hS : ∀ ℓ, centering d * S ℓ = S ℓ * centering d) (θ : Params A dIn dOut)
    (b : Biases A dOut) (γ β : Fin (L + 1) → d → ℝ) (x : Matrix T dIn ℝ) (ℓ : Fin (L + 1))
    (t : T) :
    ∑ i, hiddenB (A.withNorm (rmsNorm ε)) S (θ.centerLN ε γ) (b.centerLN ε θ β) x ℓ t i = 0 := by
  sorry

/-! ### Part (ii): the pre-RMSNorm network of dimension `d − 1` -/

/-- **Proposition A.3 (ii), the weights in an orthonormal basis `U` of `V`:** `E U`, the reads
`√(d/m) U^⊤ diag(γ_ℓ) W_read`, the writes `W_write U` and the readout
`√(d/m) U^⊤ diag(γ_L) D`, for the pre-RMSNorm network of dimension `m` with the constant
`ε d/m`. -/
noncomputable def Params.reduceLN (ε : ℝ) (U : Matrix d m ℝ) (θ : Params A dIn dOut)
    (γ : Fin (L + 1) → d → ℝ) :
    Params (A.withNorm (rmsNorm (T := T) (d := m)
      (ε * (Fintype.card d : ℝ) / (Fintype.card m : ℝ)))) dIn dOut where
  E := θ.E * U
  read ℓ := Real.sqrt ((Fintype.card d : ℝ) / (Fintype.card m : ℝ))
    • (Uᵀ * Matrix.diagonal (γ ℓ.castSucc) * θ.read ℓ)
  write ℓ := θ.write ℓ * U
  D := Real.sqrt ((Fintype.card d : ℝ) / (Fintype.card m : ℝ))
    • (Uᵀ * Matrix.diagonal (γ (Fin.last L)) * θ.D)

/-- **Proposition A.3 (ii), the biases in an orthonormal basis `U` of `V`:** `b_E U`,
`b_read + β_ℓ W_read`, `b_write U` and `b_D + β_L D`. -/
noncomputable def Biases.reduceLN (ε : ℝ) (U : Matrix d m ℝ) (b : Biases A dOut)
    (θ : Params A dIn dOut) (β : Fin (L + 1) → d → ℝ) :
    Biases (A.withNorm (rmsNorm (T := T) (d := m)
      (ε * (Fintype.card d : ℝ) / (Fintype.card m : ℝ)))) dOut where
  E := b.E ᵥ* U
  read ℓ := b.read ℓ + β ℓ.castSucc ᵥ* θ.read ℓ
  write ℓ := b.write ℓ ᵥ* U
  D := b.D + β (Fin.last L) ᵥ* θ.D

/-- **Proposition A.3 (ii) / A.15 (ii):** let the columns of `U` be an orthonormal basis of `V`
(`U^⊤ U = I` and `U U^⊤ = Z`), with at least one column. For stream matrices that commute with
`Z`, the pre-LayerNorm network computes the function of the pre-RMSNorm network of dimension `m`
with the constant `ε d/m`, the reads multiplied by `√(d/m)`, and the stream matrices
`U^⊤ S_ℓ U`. -/
theorem evalLN_eq_evalB_reduceLN (ε : ℝ) (U : Matrix d m ℝ) (hU : Uᵀ * U = 1)
    (hUZ : U * Uᵀ = centering d) (hm : 0 < Fintype.card m) (S : Fin L → Matrix d d ℝ)
    (hS : ∀ ℓ, centering d * S ℓ = S ℓ * centering d) (θ : Params A dIn dOut)
    (b : Biases A dOut) (γ β : Fin (L + 1) → d → ℝ) (x : Matrix T dIn ℝ) :
    evalLN A ε S θ b γ β x
      = evalB (A.withNorm (rmsNorm (ε * (Fintype.card d : ℝ) / (Fintype.card m : ℝ))))
          (fun ℓ => Uᵀ * S ℓ * U) (θ.reduceLN ε U γ) (b.reduceLN ε U θ β) x := by
  sorry

/-- **Proposition A.3 (ii) for a skipless pre-LayerNorm network.** -/
theorem evalLN_eq_evalB_reduceLN_skipless (ε : ℝ) (U : Matrix d m ℝ) (hU : Uᵀ * U = 1)
    (hUZ : U * Uᵀ = centering d) (hm : 0 < Fintype.card m) (θ : Params A dIn dOut)
    (b : Biases A dOut) (γ β : Fin (L + 1) → d → ℝ) (x : Matrix T dIn ℝ) :
    evalLN A ε 0 θ b γ β x
      = evalB (A.withNorm (rmsNorm (ε * (Fintype.card d : ℝ) / (Fintype.card m : ℝ))))
          0 (θ.reduceLN ε U γ) (b.reduceLN ε U θ β) x := by
  sorry

/-- **Proposition A.15 (ii) for a residual pre-LayerNorm network.** -/
theorem evalLN_eq_evalB_reduceLN_residual (ε : ℝ) (U : Matrix d m ℝ) (hU : Uᵀ * U = 1)
    (hUZ : U * Uᵀ = centering d) (hm : 0 < Fintype.card m) (θ : Params A dIn dOut)
    (b : Biases A dOut) (γ β : Fin (L + 1) → d → ℝ) (x : Matrix T dIn ℝ) :
    evalLN A ε 1 θ b γ β x
      = evalB (A.withNorm (rmsNorm (ε * (Fintype.card d : ℝ) / (Fintype.card m : ℝ))))
          1 (θ.reduceLN ε U γ) (b.reduceLN ε U θ β) x := by
  sorry

omit [Fintype dIn] in
/-- **Proposition A.3 (ii), "of dimension `d_model − 1`":** a matrix whose columns are an
orthonormal basis of `V` has `d − 1` columns. -/
theorem card_add_one_eq_of_orthonormal_centering [Nonempty d] (U : Matrix d m ℝ)
    (hU : Uᵀ * U = 1) (hUZ : U * Uᵀ = centering d) :
    Fintype.card m + 1 = Fintype.card d := by
  sorry

omit [Fintype m] [DecidableEq m] [Fintype dIn] in
/-- **"In an orthonormal basis of `V`":** such a basis exists, as the columns of a matrix `U`
with `U^⊤ U = I` and `U U^⊤ = Z`. -/
theorem exists_orthonormal_centering (d : Type*) [Fintype d] [DecidableEq d] :
    ∃ U : Matrix d (Fin (Fintype.card d - 1)) ℝ, Uᵀ * U = 1 ∧ U * Uᵀ = centering d := by
  sorry

end Skips
