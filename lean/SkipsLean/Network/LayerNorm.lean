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

omit [Fintype m] [DecidableEq m] in
/-- Helper: the hidden state `h_0` of the pre-LayerNorm network. -/
private theorem hiddenLN_zero_lno (ε : ℝ) (S : Fin L → Matrix d d ℝ) (θ : Params A dIn dOut)
    (b : Biases A dOut) (γ β : Fin (L + 1) → d → ℝ) (x : Matrix T dIn ℝ) :
    hiddenLN A ε S θ b γ β x 0 = x * θ.E + Matrix.of fun _ => b.E := by
  simp [hiddenLN]

omit [Fintype m] [DecidableEq m] in
/-- Helper: the hidden state `h_{ℓ+1}` of the pre-LayerNorm network. -/
private theorem hiddenLN_succ_lno (ε : ℝ) (S : Fin L → Matrix d d ℝ) (θ : Params A dIn dOut)
    (b : Biases A dOut) (γ β : Fin (L + 1) → d → ℝ) (x : Matrix T dIn ℝ) (ℓ : Fin L) :
    hiddenLN A ε S θ b γ β x ℓ.succ = hiddenLN A ε S θ b γ β x ℓ.castSucc * S ℓ
      + (A.f ℓ (layerNorm ε (γ ℓ.castSucc) (β ℓ.castSucc) (hiddenLN A ε S θ b γ β x ℓ.castSucc)
          * θ.read ℓ + Matrix.of fun _ => b.read ℓ) * θ.write ℓ
        + Matrix.of fun _ => b.write ℓ) := by
  simp [hiddenLN]

omit [Fintype d] [DecidableEq d] [Fintype m] [DecidableEq m] [Fintype dIn] in
/-- Helper: a matrix whose rows are all `v`, times `M`, has all rows `v M`. -/
private theorem of_const_mul_lno {n k : Type*} [Fintype n] (v : n → ℝ) (M : Matrix n k ℝ) :
    (Matrix.of fun (_ : T) => v) * M = Matrix.of fun _ => v ᵥ* M := by
  ext t j
  rfl

omit [Fintype m] [DecidableEq m] [Fintype dIn] in
/-- Helper, a read through LayerNorm: `LN(h) W + 1 c = N_ε(h Z) (diag(γ) W) + 1 (c + β W)`. -/
private theorem layerNorm_mul_add_lno (ε : ℝ) (g β : d → ℝ) {r : Type*}
    (h : Matrix T d ℝ) (W : Matrix d r ℝ) (c : r → ℝ) :
    layerNorm ε g β h * W + Matrix.of (fun _ => c)
      = rmsNorm ε (h * centering d) * (Matrix.diagonal g * W)
        + Matrix.of fun _ => c + β ᵥ* W := by
  unfold layerNorm
  rw [Matrix.add_mul, Matrix.mul_assoc, of_const_mul_lno, add_assoc]
  congr 1
  ext t j
  exact add_comm _ _

omit [Fintype m] [DecidableEq m] [Fintype dIn] in
/-- Helper, one block of the centred network: if its hidden state is `h Z`, the next one is
`h' Z` for the next hidden state `h'` of the pre-LayerNorm network. -/
private theorem step_centerLN_lno (ε : ℝ) (Sℓ : Matrix d d ℝ)
    (hSℓ : centering d * Sℓ = Sℓ * centering d) {r w : Type*} [Fintype w]
    (f : Matrix T r ℝ → Matrix T w ℝ) (g β : d → ℝ) (R : Matrix d r ℝ) (br : r → ℝ)
    (W : Matrix w d ℝ) (bw : d → ℝ) (h : Matrix T d ℝ) :
    h * centering d * Sℓ
        + (f (rmsNorm ε (h * centering d) * (Matrix.diagonal g * R)
            + Matrix.of fun _ => br + β ᵥ* R) * (W * centering d)
          + Matrix.of fun _ => bw ᵥ* centering d)
      = (h * Sℓ + (f (layerNorm ε g β h * R + Matrix.of fun _ => br) * W
          + Matrix.of fun _ => bw)) * centering d := by
  -- the read sees `N_ε(h Z)` on both sides; the stream: `h Z S = h S Z`
  rw [layerNorm_mul_add_lno, Matrix.add_mul, Matrix.add_mul, Matrix.mul_assoc h, hSℓ,
    ← Matrix.mul_assoc, Matrix.mul_assoc _ W, of_const_mul_lno]

omit [Fintype m] [DecidableEq m] in
/-- Helper: the hidden states of the centred network are `h_ℓ Z`. -/
private theorem hiddenB_centerLN_lno (ε : ℝ) (S : Fin L → Matrix d d ℝ)
    (hS : ∀ ℓ, centering d * S ℓ = S ℓ * centering d) (θ : Params A dIn dOut)
    (b : Biases A dOut) (γ β : Fin (L + 1) → d → ℝ) (x : Matrix T dIn ℝ) (k : Fin (L + 1)) :
    hiddenB (A.withNorm (rmsNorm ε)) S (θ.centerLN ε γ) (b.centerLN ε θ β) x k
      = hiddenLN A ε S θ b γ β x k * centering d := by
  induction k using Fin.induction with
  | zero =>
    -- `(x E + 1 b_E) Z = x (E Z) + 1 (b_E Z)`
    rw [hiddenB_zero, hiddenLN_zero_lno, Matrix.add_mul, Matrix.mul_assoc, of_const_mul_lno]
    rfl
  | succ ℓ ih =>
    rw [hiddenB_succ, ih, hiddenLN_succ_lno]
    exact step_centerLN_lno ε (S ℓ) (hS ℓ) (A.f ℓ) (γ ℓ.castSucc) (β ℓ.castSucc) (θ.read ℓ)
      (b.read ℓ) (θ.write ℓ) (b.write ℓ) _

/-- **Proposition A.3 (i) / A.15 (i), "gives a network that computes the same function":** for
stream matrices that commute with `Z`, the pre-LayerNorm network computes the function of the
pre-RMSNorm network with the centred weights and biases. -/
theorem evalLN_eq_evalB_centerLN (ε : ℝ) (S : Fin L → Matrix d d ℝ)
    (hS : ∀ ℓ, centering d * S ℓ = S ℓ * centering d) (θ : Params A dIn dOut)
    (b : Biases A dOut) (γ β : Fin (L + 1) → d → ℝ) (x : Matrix T dIn ℝ) :
    evalLN A ε S θ b γ β x
      = evalB (A.withNorm (rmsNorm ε)) S (θ.centerLN ε γ) (b.centerLN ε θ β) x := by
  -- the readout reads `N_ε(h_L Z)` with the weights `diag(γ_L) D` and the bias `b_D + β_L D`
  rw [evalLN, evalB, hiddenB_centerLN_lno ε S hS, layerNorm_mul_add_lno]
  rfl

/-- **Proposition A.3 (i) for a skipless pre-LayerNorm network.** -/
theorem evalLN_eq_evalB_centerLN_skipless (ε : ℝ) (θ : Params A dIn dOut) (b : Biases A dOut)
    (γ β : Fin (L + 1) → d → ℝ) (x : Matrix T dIn ℝ) :
    evalLN A ε 0 θ b γ β x
      = evalB (A.withNorm (rmsNorm ε)) 0 (θ.centerLN ε γ) (b.centerLN ε θ β) x := by
  -- `Z 0 = 0 Z`
  exact evalLN_eq_evalB_centerLN ε 0 (fun ℓ => by simp) θ b γ β x

/-- **Proposition A.15 (i) for a residual pre-LayerNorm network.** -/
theorem evalLN_eq_evalB_centerLN_residual (ε : ℝ) (θ : Params A dIn dOut) (b : Biases A dOut)
    (γ β : Fin (L + 1) → d → ℝ) (x : Matrix T dIn ℝ) :
    evalLN A ε 1 θ b γ β x
      = evalB (A.withNorm (rmsNorm ε)) 1 (θ.centerLN ε γ) (b.centerLN ε θ β) x := by
  -- `Z 1 = 1 Z`
  exact evalLN_eq_evalB_centerLN ε 1 (fun ℓ => by simp) θ b γ β x

/-- **Proposition A.3 (i), "whose hidden states lie in `V`":** for stream matrices that commute
with `Z` (skipless and residual networks among them), every row of every hidden state of the
centred network has mean zero. -/
theorem sum_hiddenB_centerLN (ε : ℝ) (S : Fin L → Matrix d d ℝ)
    (hS : ∀ ℓ, centering d * S ℓ = S ℓ * centering d) (θ : Params A dIn dOut)
    (b : Biases A dOut) (γ β : Fin (L + 1) → d → ℝ) (x : Matrix T dIn ℝ) (ℓ : Fin (L + 1))
    (t : T) :
    ∑ i, hiddenB (A.withNorm (rmsNorm ε)) S (θ.centerLN ε γ) (b.centerLN ε θ β) x ℓ t i = 0 := by
  -- the row `t` of `h_ℓ Z` is `(h_ℓ)_t Z`, of mean zero
  rw [hiddenB_centerLN_lno ε S hS]
  exact sum_vecMul_centering (hiddenLN A ε S θ b γ β x ℓ t)

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

/-- Helper: `Z U = U`, since `Z U = U (U^⊤ U) = U`. -/
private theorem centering_mul_lno (U : Matrix d m ℝ) (hU : Uᵀ * U = 1)
    (hUZ : U * Uᵀ = centering d) : centering d * U = U := by
  rw [← hUZ, Matrix.mul_assoc, hU, Matrix.mul_one]

/-- Helper: `N_ε(h U^⊤) = √(d/m) N'(h) U^⊤`, row by row, with `N'` the RMSNorm of dimension `m`
and the constant `ε d/m`. -/
private theorem rmsNorm_mul_transpose_lno (U : Matrix d m ℝ) (hU : Uᵀ * U = 1)
    (hm : 0 < Fintype.card m) (ε : ℝ) (h : Matrix T m ℝ) :
    rmsNorm ε (h * Uᵀ) = Real.sqrt ((Fintype.card d : ℝ) / (Fintype.card m : ℝ))
      • (rmsNorm (ε * (Fintype.card d : ℝ) / (Fintype.card m : ℝ)) h * Uᵀ) := by
  ext t j
  have key : rmsNorm ε (h * Uᵀ) t = (Real.sqrt ((Fintype.card d : ℝ) / (Fintype.card m : ℝ))
      • (rmsNorm (ε * (Fintype.card d : ℝ) / (Fintype.card m : ℝ)) h * Uᵀ)) t := by
    show rmsRow ε (h t ᵥ* Uᵀ) = Real.sqrt ((Fintype.card d : ℝ) / (Fintype.card m : ℝ))
      • (rmsRow (ε * (Fintype.card d : ℝ) / (Fintype.card m : ℝ)) (h t) ᵥ* Uᵀ)
    exact rmsRow_vecMul_transpose_of_orthonormal U hU hm ε (h t)
  exact congrFun key j

/-- Helper, a read in the basis `U`: `N_ε(h Z) (diag(γ) R) = N'(h U) (√(d/m) U^⊤ diag(γ) R)`,
since `h Z = (h U) U^⊤`. -/
private theorem rmsNorm_centering_mul_lno (U : Matrix d m ℝ) (hU : Uᵀ * U = 1)
    (hUZ : U * Uᵀ = centering d) (hm : 0 < Fintype.card m) (ε : ℝ) {r : Type*}
    (g : d → ℝ) (R : Matrix d r ℝ) (h : Matrix T d ℝ) :
    rmsNorm ε (h * centering d) * (Matrix.diagonal g * R)
      = rmsNorm (ε * (Fintype.card d : ℝ) / (Fintype.card m : ℝ)) (h * U)
        * (Real.sqrt ((Fintype.card d : ℝ) / (Fintype.card m : ℝ))
          • (Uᵀ * Matrix.diagonal g * R)) := by
  rw [← hUZ, ← Matrix.mul_assoc h, rmsNorm_mul_transpose_lno U hU hm, Matrix.smul_mul,
    Matrix.mul_smul]
  simp only [Matrix.mul_assoc]

/-- Helper, one block of the reduced network: if its hidden state is `h U`, the next one is
`h' U` for the next hidden state `h'` of the pre-LayerNorm network. -/
private theorem step_reduceLN_lno (ε : ℝ) (U : Matrix d m ℝ) (hU : Uᵀ * U = 1)
    (hUZ : U * Uᵀ = centering d) (hm : 0 < Fintype.card m) (Sℓ : Matrix d d ℝ)
    (hSℓ : centering d * Sℓ = Sℓ * centering d) {r w : Type*} [Fintype w]
    (f : Matrix T r ℝ → Matrix T w ℝ) (g β : d → ℝ) (R : Matrix d r ℝ) (br : r → ℝ)
    (W : Matrix w d ℝ) (bw : d → ℝ) (h : Matrix T d ℝ) :
    h * U * (Uᵀ * Sℓ * U)
        + (f (rmsNorm (ε * (Fintype.card d : ℝ) / (Fintype.card m : ℝ)) (h * U)
              * (Real.sqrt ((Fintype.card d : ℝ) / (Fintype.card m : ℝ))
                • (Uᵀ * Matrix.diagonal g * R))
            + Matrix.of fun _ => br + β ᵥ* R) * (W * U)
          + Matrix.of fun _ => bw ᵥ* U)
      = (h * Sℓ + (f (layerNorm ε g β h * R + Matrix.of fun _ => br) * W
          + Matrix.of fun _ => bw)) * U := by
  -- the stream: `h U U^⊤ S U = h Z S U = h S Z U = h S U`
  have hstream : h * U * (Uᵀ * Sℓ * U) = h * Sℓ * U := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc U, ← Matrix.mul_assoc U, hUZ, hSℓ,
      Matrix.mul_assoc Sℓ, centering_mul_lno U hU hUZ, ← Matrix.mul_assoc]
  -- the read, and the write and its bias multiplied by `U`
  rw [layerNorm_mul_add_lno, rmsNorm_centering_mul_lno U hU hUZ hm, hstream, Matrix.add_mul,
    Matrix.add_mul, Matrix.mul_assoc _ W, of_const_mul_lno]

/-- Helper: the hidden states of the reduced network are `h_ℓ U`. -/
private theorem hiddenB_reduceLN_lno (ε : ℝ) (U : Matrix d m ℝ) (hU : Uᵀ * U = 1)
    (hUZ : U * Uᵀ = centering d) (hm : 0 < Fintype.card m) (S : Fin L → Matrix d d ℝ)
    (hS : ∀ ℓ, centering d * S ℓ = S ℓ * centering d) (θ : Params A dIn dOut)
    (b : Biases A dOut) (γ β : Fin (L + 1) → d → ℝ) (x : Matrix T dIn ℝ) (k : Fin (L + 1)) :
    hiddenB (A.withNorm (rmsNorm (ε * (Fintype.card d : ℝ) / (Fintype.card m : ℝ))))
        (fun ℓ => Uᵀ * S ℓ * U) (θ.reduceLN ε U γ) (b.reduceLN ε U θ β) x k
      = hiddenLN A ε S θ b γ β x k * U := by
  induction k using Fin.induction with
  | zero =>
    -- `(x E + 1 b_E) U = x (E U) + 1 (b_E U)`
    rw [hiddenB_zero, hiddenLN_zero_lno, Matrix.add_mul, Matrix.mul_assoc, of_const_mul_lno]
    rfl
  | succ ℓ ih =>
    rw [hiddenB_succ, ih, hiddenLN_succ_lno]
    exact step_reduceLN_lno ε U hU hUZ hm (S ℓ) (hS ℓ) (A.f ℓ) (γ ℓ.castSucc) (β ℓ.castSucc)
      (θ.read ℓ) (b.read ℓ) (θ.write ℓ) (b.write ℓ) _

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
  -- the readout reads `N'(h_L U)` with the weights `√(d/m) U^⊤ diag(γ_L) D`
  rw [evalLN, evalB, hiddenB_reduceLN_lno ε U hU hUZ hm S hS, layerNorm_mul_add_lno,
    rmsNorm_centering_mul_lno U hU hUZ hm]
  rfl

/-- **Proposition A.3 (ii) for a skipless pre-LayerNorm network.** -/
theorem evalLN_eq_evalB_reduceLN_skipless (ε : ℝ) (U : Matrix d m ℝ) (hU : Uᵀ * U = 1)
    (hUZ : U * Uᵀ = centering d) (hm : 0 < Fintype.card m) (θ : Params A dIn dOut)
    (b : Biases A dOut) (γ β : Fin (L + 1) → d → ℝ) (x : Matrix T dIn ℝ) :
    evalLN A ε 0 θ b γ β x
      = evalB (A.withNorm (rmsNorm (ε * (Fintype.card d : ℝ) / (Fintype.card m : ℝ))))
          0 (θ.reduceLN ε U γ) (b.reduceLN ε U θ β) x := by
  -- `Z 0 = 0 Z` and `U^⊤ 0 U = 0`
  have h0 : (fun ℓ => Uᵀ * (0 : Fin L → Matrix d d ℝ) ℓ * U) = 0 := by
    funext ℓ
    simp
  rw [evalLN_eq_evalB_reduceLN ε U hU hUZ hm 0 (fun ℓ => by simp) θ b γ β x, h0]

/-- **Proposition A.15 (ii) for a residual pre-LayerNorm network.** -/
theorem evalLN_eq_evalB_reduceLN_residual (ε : ℝ) (U : Matrix d m ℝ) (hU : Uᵀ * U = 1)
    (hUZ : U * Uᵀ = centering d) (hm : 0 < Fintype.card m) (θ : Params A dIn dOut)
    (b : Biases A dOut) (γ β : Fin (L + 1) → d → ℝ) (x : Matrix T dIn ℝ) :
    evalLN A ε 1 θ b γ β x
      = evalB (A.withNorm (rmsNorm (ε * (Fintype.card d : ℝ) / (Fintype.card m : ℝ))))
          1 (θ.reduceLN ε U γ) (b.reduceLN ε U θ β) x := by
  -- `Z 1 = 1 Z` and `U^⊤ 1 U = U^⊤ U = 1`
  have h1 : (fun ℓ => Uᵀ * (1 : Fin L → Matrix d d ℝ) ℓ * U) = 1 := by
    funext ℓ
    rw [Pi.one_apply, Matrix.mul_one, hU, Pi.one_apply]
  rw [evalLN_eq_evalB_reduceLN ε U hU hUZ hm 1 (fun ℓ => by simp) θ b γ β x, h1]

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
