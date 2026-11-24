import SkipsLean.Absorb.RMSNormGeneric
import SkipsLean.Activations.Analytic

/-!
# Under RMSNorm a residual network equals no skipless network: the seven kinds of MLP block

Paper ("Can an MLP Absorb Its Skip Connection Exactly?"): Theorem 4.3. "Consider pre-RMSNorm
networks, with `ε ≥ 0` and blocks of any kind and width. For almost every choice of weights, a
residual network equals no skipless network, whatever its depth, widths and kinds of blocks."

`Absorb/RMSNormGeneric.lean` states the theorem for residual networks of MLP blocks and of gated
blocks whose activation (or gate) is locally Lipschitz and nonzero on the positive reals. Here it
is stated for each kind of MLP block of the paper: tanh, GELU, ReLU and ReLU² blocks, and SwiGLU,
GeGLU and ReGLU blocks (gated, with the gates SiLU, GELU and ReLU). The scope is that of the
paper: `d_in, d_out ≥ d ≥ 2`; the block that must have a hidden unit is written as a hypothesis
(the paper's blocks have at least `d` hidden units). The skipless network is of any kind (an
arbitrary `Arch`), of any depth `L'`, model dimension `d'` and widths; for `ε > 0` it may have its
own constant `ε' > 0` and its blocks are locally Lipschitz; for `ε = 0` its blocks are continuous
and equality is in the paper's sense for `ε = 0` (no dense set of inputs at which both networks are
defined and agree). Attention blocks are not stated.
-/

namespace Skips

open Matrix MeasureTheory Filter
open scoped Matrix.Norms.Elementwise Topology

/-! ### The five activations are locally Lipschitz -/

/-- `tanh` is locally Lipschitz. -/
theorem locallyLipschitz_tanh : LocallyLipschitz Real.tanh := by
  sorry

/-- GELU is locally Lipschitz. -/
theorem locallyLipschitz_gelu : LocallyLipschitz gelu := by
  sorry

/-- SiLU is locally Lipschitz. -/
theorem locallyLipschitz_silu : LocallyLipschitz silu := by
  sorry

/-- ReLU is locally Lipschitz. -/
theorem locallyLipschitz_relu : LocallyLipschitz relu := by
  sorry

/-- ReLU² is locally Lipschitz. -/
theorem locallyLipschitz_reluSq : LocallyLipschitz reluSq := by
  sorry

/-! ### They do not vanish on the positive reals -/

/-- `tanh z ≠ 0` for `z > 0`. -/
theorem tanh_ne_zero_of_pos {z : ℝ} (hz : 0 < z) : Real.tanh z ≠ 0 := by
  sorry

/-- `GELU(z) ≠ 0` for `z > 0`. -/
theorem gelu_ne_zero_of_pos {z : ℝ} (hz : 0 < z) : gelu z ≠ 0 := by
  sorry

/-- `SiLU(z) ≠ 0` for `z > 0`. -/
theorem silu_ne_zero_of_pos {z : ℝ} (hz : 0 < z) : silu z ≠ 0 := by
  sorry

/-- `ReLU(z) ≠ 0` for `z > 0`. -/
theorem relu_ne_zero_of_pos {z : ℝ} (hz : 0 < z) : relu z ≠ 0 := by
  sorry

/-- `ReLU²(z) ≠ 0` for `z > 0`. -/
theorem reluSq_ne_zero_of_pos {z : ℝ} (hz : 0 < z) : reluSq z ≠ 0 := by
  sorry

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]

/-! ### Theorem 4.3 for each kind of block -/

/-- **Theorem 4.3 for tanh blocks, `ε > 0`.** For almost every choice of weights, the residual network
equals no pre-RMSNorm skipless network with locally Lipschitz blocks. -/
theorem ae_ne_skipless_rmsNorm_tanh [Nonempty T] {ε : ℝ} (hε : 0 < ε)
    (hhid : ∃ ℓ, Nonempty (hid ℓ))
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) Real.tanh (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure]
    (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, ∀ (L' : ℕ) (d' : Type) [Fintype d'] (A' : Arch T d' L') (ε' : ℝ), 0 < ε' →
      A'.χ = rmsNorm ε' → (∀ ℓ, LocallyLipschitz (A'.f ℓ)) → ∀ θ' : Params A' dIn dOut,
        ∃ X : Matrix T dIn ℝ,
          eval (Arch.mlp Real.tanh (rmsNorm ε) hid) 1 θ X ≠ eval A' 0 θ' X := by
  sorry

/-- **Theorem 4.3 for tanh blocks, `ε = 0`.** For almost every choice of weights, the residual network
equals no pre-RMSNorm skipless network with `ε = 0` and continuous blocks. -/
theorem ae_not_dense_eq_skipless_rmsNorm_zero_tanh [Nonempty T]
    (hhid : ∃ ℓ, Nonempty (hid ℓ))
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) Real.tanh (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure]
    (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, ∀ (L' : ℕ) (d' : Type) [Fintype d'] (A' : Arch T d' L'), A'.χ = rmsNorm 0 →
      (∀ ℓ, Continuous (A'.f ℓ)) → ∀ θ' : Params A' dIn dOut,
        ¬ ∃ S : Set (Matrix T dIn ℝ), Dense S ∧
          ∀ X ∈ S, DefinedAt (Arch.mlp Real.tanh (rmsNorm 0) hid) 1 θ X ∧ DefinedAt A' 0 θ' X ∧
            eval (Arch.mlp Real.tanh (rmsNorm 0) hid) 1 θ X = eval A' 0 θ' X := by
  sorry

/-- **Theorem 4.3 for GELU blocks, `ε > 0`.** For almost every choice of weights, the residual network
equals no pre-RMSNorm skipless network with locally Lipschitz blocks. -/
theorem ae_ne_skipless_rmsNorm_gelu [Nonempty T] {ε : ℝ} (hε : 0 < ε)
    (hhid : ∃ ℓ, Nonempty (hid ℓ))
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure]
    (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, ∀ (L' : ℕ) (d' : Type) [Fintype d'] (A' : Arch T d' L') (ε' : ℝ), 0 < ε' →
      A'.χ = rmsNorm ε' → (∀ ℓ, LocallyLipschitz (A'.f ℓ)) → ∀ θ' : Params A' dIn dOut,
        ∃ X : Matrix T dIn ℝ,
          eval (Arch.mlp gelu (rmsNorm ε) hid) 1 θ X ≠ eval A' 0 θ' X := by
  sorry

/-- **Theorem 4.3 for GELU blocks, `ε = 0`.** For almost every choice of weights, the residual network
equals no pre-RMSNorm skipless network with `ε = 0` and continuous blocks. -/
theorem ae_not_dense_eq_skipless_rmsNorm_zero_gelu [Nonempty T]
    (hhid : ∃ ℓ, Nonempty (hid ℓ))
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure]
    (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, ∀ (L' : ℕ) (d' : Type) [Fintype d'] (A' : Arch T d' L'), A'.χ = rmsNorm 0 →
      (∀ ℓ, Continuous (A'.f ℓ)) → ∀ θ' : Params A' dIn dOut,
        ¬ ∃ S : Set (Matrix T dIn ℝ), Dense S ∧
          ∀ X ∈ S, DefinedAt (Arch.mlp gelu (rmsNorm 0) hid) 1 θ X ∧ DefinedAt A' 0 θ' X ∧
            eval (Arch.mlp gelu (rmsNorm 0) hid) 1 θ X = eval A' 0 θ' X := by
  sorry

/-- **Theorem 4.3 for ReLU blocks, `ε > 0`.** For almost every choice of weights, the residual network
equals no pre-RMSNorm skipless network with locally Lipschitz blocks. -/
theorem ae_ne_skipless_rmsNorm_relu [Nonempty T] {ε : ℝ} (hε : 0 < ε)
    (hhid : ∃ ℓ, Nonempty (hid ℓ))
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure]
    (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, ∀ (L' : ℕ) (d' : Type) [Fintype d'] (A' : Arch T d' L') (ε' : ℝ), 0 < ε' →
      A'.χ = rmsNorm ε' → (∀ ℓ, LocallyLipschitz (A'.f ℓ)) → ∀ θ' : Params A' dIn dOut,
        ∃ X : Matrix T dIn ℝ,
          eval (Arch.mlp relu (rmsNorm ε) hid) 1 θ X ≠ eval A' 0 θ' X := by
  sorry

/-- **Theorem 4.3 for ReLU blocks, `ε = 0`.** For almost every choice of weights, the residual network
equals no pre-RMSNorm skipless network with `ε = 0` and continuous blocks. -/
theorem ae_not_dense_eq_skipless_rmsNorm_zero_relu [Nonempty T]
    (hhid : ∃ ℓ, Nonempty (hid ℓ))
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure]
    (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, ∀ (L' : ℕ) (d' : Type) [Fintype d'] (A' : Arch T d' L'), A'.χ = rmsNorm 0 →
      (∀ ℓ, Continuous (A'.f ℓ)) → ∀ θ' : Params A' dIn dOut,
        ¬ ∃ S : Set (Matrix T dIn ℝ), Dense S ∧
          ∀ X ∈ S, DefinedAt (Arch.mlp relu (rmsNorm 0) hid) 1 θ X ∧ DefinedAt A' 0 θ' X ∧
            eval (Arch.mlp relu (rmsNorm 0) hid) 1 θ X = eval A' 0 θ' X := by
  sorry

/-- **Theorem 4.3 for ReLU² blocks, `ε > 0`.** For almost every choice of weights, the residual network
equals no pre-RMSNorm skipless network with locally Lipschitz blocks. -/
theorem ae_ne_skipless_rmsNorm_reluSq [Nonempty T] {ε : ℝ} (hε : 0 < ε)
    (hhid : ∃ ℓ, Nonempty (hid ℓ))
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) reluSq (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure]
    (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, ∀ (L' : ℕ) (d' : Type) [Fintype d'] (A' : Arch T d' L') (ε' : ℝ), 0 < ε' →
      A'.χ = rmsNorm ε' → (∀ ℓ, LocallyLipschitz (A'.f ℓ)) → ∀ θ' : Params A' dIn dOut,
        ∃ X : Matrix T dIn ℝ,
          eval (Arch.mlp reluSq (rmsNorm ε) hid) 1 θ X ≠ eval A' 0 θ' X := by
  sorry

/-- **Theorem 4.3 for ReLU² blocks, `ε = 0`.** For almost every choice of weights, the residual network
equals no pre-RMSNorm skipless network with `ε = 0` and continuous blocks. -/
theorem ae_not_dense_eq_skipless_rmsNorm_zero_reluSq [Nonempty T]
    (hhid : ∃ ℓ, Nonempty (hid ℓ))
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) reluSq (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure]
    (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, ∀ (L' : ℕ) (d' : Type) [Fintype d'] (A' : Arch T d' L'), A'.χ = rmsNorm 0 →
      (∀ ℓ, Continuous (A'.f ℓ)) → ∀ θ' : Params A' dIn dOut,
        ¬ ∃ S : Set (Matrix T dIn ℝ), Dense S ∧
          ∀ X ∈ S, DefinedAt (Arch.mlp reluSq (rmsNorm 0) hid) 1 θ X ∧ DefinedAt A' 0 θ' X ∧
            eval (Arch.mlp reluSq (rmsNorm 0) hid) 1 θ X = eval A' 0 θ' X := by
  sorry

/-- **Theorem 4.3 for SwiGLU blocks, `ε > 0`.** For almost every choice of weights, the residual network
equals no pre-RMSNorm skipless network with locally Lipschitz blocks. -/
theorem ae_ne_skipless_rmsNorm_swiglu [Nonempty T] {ε : ℝ} (hε : 0 < ε)
    (hhid : ∃ ℓ, Nonempty (hid ℓ))
    (μ : Measure (Params (Arch.gated (T := T) (d := d) silu (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure]
    (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, ∀ (L' : ℕ) (d' : Type) [Fintype d'] (A' : Arch T d' L') (ε' : ℝ), 0 < ε' →
      A'.χ = rmsNorm ε' → (∀ ℓ, LocallyLipschitz (A'.f ℓ)) → ∀ θ' : Params A' dIn dOut,
        ∃ X : Matrix T dIn ℝ,
          eval (Arch.gated silu (rmsNorm ε) hid) 1 θ X ≠ eval A' 0 θ' X := by
  sorry

/-- **Theorem 4.3 for SwiGLU blocks, `ε = 0`.** For almost every choice of weights, the residual network
equals no pre-RMSNorm skipless network with `ε = 0` and continuous blocks. -/
theorem ae_not_dense_eq_skipless_rmsNorm_zero_swiglu [Nonempty T]
    (hhid : ∃ ℓ, Nonempty (hid ℓ))
    (μ : Measure (Params (Arch.gated (T := T) (d := d) silu (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure]
    (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, ∀ (L' : ℕ) (d' : Type) [Fintype d'] (A' : Arch T d' L'), A'.χ = rmsNorm 0 →
      (∀ ℓ, Continuous (A'.f ℓ)) → ∀ θ' : Params A' dIn dOut,
        ¬ ∃ S : Set (Matrix T dIn ℝ), Dense S ∧
          ∀ X ∈ S, DefinedAt (Arch.gated silu (rmsNorm 0) hid) 1 θ X ∧ DefinedAt A' 0 θ' X ∧
            eval (Arch.gated silu (rmsNorm 0) hid) 1 θ X = eval A' 0 θ' X := by
  sorry

/-- **Theorem 4.3 for GeGLU blocks, `ε > 0`.** For almost every choice of weights, the residual network
equals no pre-RMSNorm skipless network with locally Lipschitz blocks. -/
theorem ae_ne_skipless_rmsNorm_geglu [Nonempty T] {ε : ℝ} (hε : 0 < ε)
    (hhid : ∃ ℓ, Nonempty (hid ℓ))
    (μ : Measure (Params (Arch.gated (T := T) (d := d) gelu (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure]
    (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, ∀ (L' : ℕ) (d' : Type) [Fintype d'] (A' : Arch T d' L') (ε' : ℝ), 0 < ε' →
      A'.χ = rmsNorm ε' → (∀ ℓ, LocallyLipschitz (A'.f ℓ)) → ∀ θ' : Params A' dIn dOut,
        ∃ X : Matrix T dIn ℝ,
          eval (Arch.gated gelu (rmsNorm ε) hid) 1 θ X ≠ eval A' 0 θ' X := by
  sorry

/-- **Theorem 4.3 for GeGLU blocks, `ε = 0`.** For almost every choice of weights, the residual network
equals no pre-RMSNorm skipless network with `ε = 0` and continuous blocks. -/
theorem ae_not_dense_eq_skipless_rmsNorm_zero_geglu [Nonempty T]
    (hhid : ∃ ℓ, Nonempty (hid ℓ))
    (μ : Measure (Params (Arch.gated (T := T) (d := d) gelu (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure]
    (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, ∀ (L' : ℕ) (d' : Type) [Fintype d'] (A' : Arch T d' L'), A'.χ = rmsNorm 0 →
      (∀ ℓ, Continuous (A'.f ℓ)) → ∀ θ' : Params A' dIn dOut,
        ¬ ∃ S : Set (Matrix T dIn ℝ), Dense S ∧
          ∀ X ∈ S, DefinedAt (Arch.gated gelu (rmsNorm 0) hid) 1 θ X ∧ DefinedAt A' 0 θ' X ∧
            eval (Arch.gated gelu (rmsNorm 0) hid) 1 θ X = eval A' 0 θ' X := by
  sorry

/-- **Theorem 4.3 for ReGLU blocks, `ε > 0`.** For almost every choice of weights, the residual network
equals no pre-RMSNorm skipless network with locally Lipschitz blocks. -/
theorem ae_ne_skipless_rmsNorm_reglu [Nonempty T] {ε : ℝ} (hε : 0 < ε)
    (hhid : ∃ ℓ, Nonempty (hid ℓ))
    (μ : Measure (Params (Arch.gated (T := T) (d := d) relu (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure]
    (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, ∀ (L' : ℕ) (d' : Type) [Fintype d'] (A' : Arch T d' L') (ε' : ℝ), 0 < ε' →
      A'.χ = rmsNorm ε' → (∀ ℓ, LocallyLipschitz (A'.f ℓ)) → ∀ θ' : Params A' dIn dOut,
        ∃ X : Matrix T dIn ℝ,
          eval (Arch.gated relu (rmsNorm ε) hid) 1 θ X ≠ eval A' 0 θ' X := by
  sorry

/-- **Theorem 4.3 for ReGLU blocks, `ε = 0`.** For almost every choice of weights, the residual network
equals no pre-RMSNorm skipless network with `ε = 0` and continuous blocks. -/
theorem ae_not_dense_eq_skipless_rmsNorm_zero_reglu [Nonempty T]
    (hhid : ∃ ℓ, Nonempty (hid ℓ))
    (μ : Measure (Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure]
    (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, ∀ (L' : ℕ) (d' : Type) [Fintype d'] (A' : Arch T d' L'), A'.χ = rmsNorm 0 →
      (∀ ℓ, Continuous (A'.f ℓ)) → ∀ θ' : Params A' dIn dOut,
        ¬ ∃ S : Set (Matrix T dIn ℝ), Dense S ∧
          ∀ X ∈ S, DefinedAt (Arch.gated relu (rmsNorm 0) hid) 1 θ X ∧ DefinedAt A' 0 θ' X ∧
            eval (Arch.gated relu (rmsNorm 0) hid) 1 θ X = eval A' 0 θ' X := by
  sorry

end Skips
