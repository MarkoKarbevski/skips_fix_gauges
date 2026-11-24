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
  -- real-analytic, hence `C¹`, hence locally Lipschitz
  exact (analyticOnNhd_tanh.contDiff (n := 1)).locallyLipschitz

/-- GELU is locally Lipschitz. -/
theorem locallyLipschitz_gelu : LocallyLipschitz gelu := by
  exact (analyticOnNhd_gelu.contDiff (n := 1)).locallyLipschitz

/-- SiLU is locally Lipschitz. -/
theorem locallyLipschitz_silu : LocallyLipschitz silu := by
  exact (analyticOnNhd_silu.contDiff (n := 1)).locallyLipschitz

/-- ReLU is locally Lipschitz. -/
theorem locallyLipschitz_relu : LocallyLipschitz relu := by
  -- `max z 0` is 1-Lipschitz
  have h : LipschitzWith 1 (fun z : ℝ => max z 0) := by
    simpa using (LipschitzWith.id (α := ℝ)).max (LipschitzWith.const (0 : ℝ))
  exact h.locallyLipschitz

/-- ReLU² is locally Lipschitz. -/
theorem locallyLipschitz_reluSq : LocallyLipschitz reluSq := by
  -- the square (a `C¹` map) after ReLU
  have hsq : LocallyLipschitz (fun x : ℝ => x ^ 2) :=
    (contDiff_id.pow 2 : ContDiff ℝ 1 fun x : ℝ => id x ^ 2).locallyLipschitz
  exact hsq.comp locallyLipschitz_relu

/-! ### They do not vanish on the positive reals -/

/-- `tanh z ≠ 0` for `z > 0`. -/
theorem tanh_ne_zero_of_pos {z : ℝ} (hz : 0 < z) : Real.tanh z ≠ 0 := by
  rw [Real.tanh_eq_sinh_div_cosh]
  exact (div_pos (Real.sinh_pos_iff.2 hz) (Real.cosh_pos z)).ne'

/-- `GELU(z) ≠ 0` for `z > 0`. -/
theorem gelu_ne_zero_of_pos {z : ℝ} (hz : 0 < z) : gelu z ≠ 0 := by
  exact (mul_pos hz (gaussCdf_pos z)).ne'

/-- `SiLU(z) ≠ 0` for `z > 0`. -/
theorem silu_ne_zero_of_pos {z : ℝ} (hz : 0 < z) : silu z ≠ 0 := by
  unfold silu
  exact (div_pos hz (by positivity)).ne'

/-- `ReLU(z) ≠ 0` for `z > 0`. -/
theorem relu_ne_zero_of_pos {z : ℝ} (hz : 0 < z) : relu z ≠ 0 := by
  simp only [relu, max_eq_left hz.le]
  exact hz.ne'

/-- `ReLU²(z) ≠ 0` for `z > 0`. -/
theorem reluSq_ne_zero_of_pos {z : ℝ} (hz : 0 < z) : reluSq z ≠ 0 := by
  simp only [reluSq, max_eq_left hz.le]
  exact (pow_pos hz 2).ne'

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
  exact ae_ne_skipless_rmsNorm_mlp hε (fun z hz => tanh_ne_zero_of_pos hz)
    locallyLipschitz_tanh hhid μ hd hdIn hdOut

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
  exact ae_not_dense_eq_skipless_rmsNorm_zero_mlp (fun z hz => tanh_ne_zero_of_pos hz)
    locallyLipschitz_tanh hhid μ hd hdIn hdOut

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
  exact ae_ne_skipless_rmsNorm_mlp hε (fun z hz => gelu_ne_zero_of_pos hz)
    locallyLipschitz_gelu hhid μ hd hdIn hdOut

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
  exact ae_not_dense_eq_skipless_rmsNorm_zero_mlp (fun z hz => gelu_ne_zero_of_pos hz)
    locallyLipschitz_gelu hhid μ hd hdIn hdOut

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
  exact ae_ne_skipless_rmsNorm_mlp hε (fun z hz => relu_ne_zero_of_pos hz)
    locallyLipschitz_relu hhid μ hd hdIn hdOut

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
  exact ae_not_dense_eq_skipless_rmsNorm_zero_mlp (fun z hz => relu_ne_zero_of_pos hz)
    locallyLipschitz_relu hhid μ hd hdIn hdOut

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
  exact ae_ne_skipless_rmsNorm_mlp hε (fun z hz => reluSq_ne_zero_of_pos hz)
    locallyLipschitz_reluSq hhid μ hd hdIn hdOut

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
  exact ae_not_dense_eq_skipless_rmsNorm_zero_mlp (fun z hz => reluSq_ne_zero_of_pos hz)
    locallyLipschitz_reluSq hhid μ hd hdIn hdOut

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
  exact ae_ne_skipless_rmsNorm_gated hε (fun z hz => silu_ne_zero_of_pos hz)
    locallyLipschitz_silu hhid μ hd hdIn hdOut

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
  exact ae_not_dense_eq_skipless_rmsNorm_zero_gated (fun z hz => silu_ne_zero_of_pos hz)
    locallyLipschitz_silu hhid μ hd hdIn hdOut

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
  exact ae_ne_skipless_rmsNorm_gated hε (fun z hz => gelu_ne_zero_of_pos hz)
    locallyLipschitz_gelu hhid μ hd hdIn hdOut

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
  exact ae_not_dense_eq_skipless_rmsNorm_zero_gated (fun z hz => gelu_ne_zero_of_pos hz)
    locallyLipschitz_gelu hhid μ hd hdIn hdOut

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
  exact ae_ne_skipless_rmsNorm_gated hε (fun z hz => relu_ne_zero_of_pos hz)
    locallyLipschitz_relu hhid μ hd hdIn hdOut

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
  exact ae_not_dense_eq_skipless_rmsNorm_zero_gated (fun z hz => relu_ne_zero_of_pos hz)
    locallyLipschitz_relu hhid μ hd hdIn hdOut

end Skips
