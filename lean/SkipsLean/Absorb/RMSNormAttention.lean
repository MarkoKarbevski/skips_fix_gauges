import SkipsLean.Absorb.RMSNormKinds
import SkipsLean.Network.Sum

/-!
# Under RMSNorm a residual network equals no skipless network: attention blocks and transformers

Paper ("Can an MLP Absorb Its Skip Connection Exactly?"): Theorem 4.3. "Consider pre-RMSNorm
networks, with `ε ≥ 0` and blocks of any kind and width. For almost every choice of weights, a
residual network equals no skipless network, whatever its depth, widths and kinds of blocks." And
after it: "The theorem covers pre-RMSNorm transformers, which alternate attention and MLP blocks."
Appendix A.3: "Each block is linear in its write, which for an attention block holds the matrices
`W_{O,i}`: block `ℓ` adds `a_ℓ W_write^ℓ` to the hidden state, where `a_ℓ` […] holds the
activations of its hidden units, or for an attention block the matrices `P_{Γ_i}(n) n W_{V,i}` of
its heads side by side."

`Absorb/RMSNormGeneric.lean` proves the theorem for a residual network of locally Lipschitz blocks
in which, for almost every choice of weights, some block has a nonzero output at some normalized
state (`SomeBlockNonzero`), and `Absorb/RMSNormKinds.lean` states it for the seven kinds of MLP
block. Here the residual network is

* a network of attention blocks (`Arch.attention`, any mask): some block has a head of positive
  width, and some token sees a token (at a state whose tokens are all equal, a head gives a token
  that sees some token the value of that token);
* a network whose blocks are attention blocks and MLP blocks in any order, or attention blocks
  and gated blocks (`Arch.sum`, `Network/Sum.lean`): some block has a hidden unit.

The scope is that of the paper, `d_in, d_out ≥ d ≥ 2`. The skipless network is of any kind (an
arbitrary `Arch`, so also a network of attention blocks or a transformer, whose blocks are locally
Lipschitz by `locallyLipschitz_f_attention` and `locallyLipschitz_f_sum`), of any depth `L'`,
model dimension `d'` and widths; for `ε > 0` it may have its own constant `ε' > 0` and its blocks
are locally Lipschitz; for `ε = 0` its blocks are continuous and equality is in the paper's sense
for `ε = 0` (no dense set of inputs at which both networks are defined and agree).
-/

namespace Skips

open Matrix MeasureTheory Filter
open scoped Matrix.Norms.Elementwise Topology

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {sees : T → T → Prop} [DecidableRel sees]
variable {H dh : Fin L → Type} [∀ ℓ, Fintype (H ℓ)] [∀ ℓ, Fintype (dh ℓ)]
variable {σ : ℝ → ℝ} {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]

/-! ### Attention blocks -/

omit [Fintype d] [DecidableEq d] in
/-- The map of an attention block is locally Lipschitz (it is real-analytic). -/
theorem locallyLipschitz_f_attention (χ : Matrix T d ℝ → Matrix T d ℝ) (ℓ : Fin L) :
    LocallyLipschitz ((Arch.attention sees χ H dh).f ℓ) := by
  sorry

/-- For a network of attention blocks in which some block has a head of positive width, and a
token `t` that sees a token `s`: for almost every choice of weights, some block has a nonzero
output at some normalized state (a value column `c ≠ 0` of the read and the state with all rows
`√d c / ‖c‖`: the head gives token `t` the value of this row). -/
theorem ae_someBlockNonzero_attention [Nonempty d] {χ : Matrix T d ℝ → Matrix T d ℝ}
    (hhead : ∃ ℓ, Nonempty (H ℓ) ∧ Nonempty (dh ℓ)) (t s : T) (hts : sees t s)
    (μ : Measure (Params (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut))
    [μ.IsAddHaarMeasure] :
    ∀ᵐ θ ∂μ, SomeBlockNonzero (Arch.attention sees χ H dh) θ := by
  sorry

/-- **Theorem 4.3 for residual networks of attention blocks, `ε > 0`.** For almost every choice of
weights (`d_in, d_out ≥ d ≥ 2`, some block has a head of positive width, some token sees a token),
the residual network equals no pre-RMSNorm skipless network with locally Lipschitz blocks of any
kind. -/
theorem ae_ne_skipless_rmsNorm_attention {ε : ℝ} (hε : 0 < ε)
    (hhead : ∃ ℓ, Nonempty (H ℓ) ∧ Nonempty (dh ℓ)) (t s : T) (hts : sees t s)
    (μ : Measure (Params (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut))
    [μ.IsAddHaarMeasure]
    (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, ∀ (L' : ℕ) (d' : Type) [Fintype d'] (A' : Arch T d' L') (ε' : ℝ), 0 < ε' →
      A'.χ = rmsNorm ε' → (∀ ℓ, LocallyLipschitz (A'.f ℓ)) → ∀ θ' : Params A' dIn dOut,
        ∃ X : Matrix T dIn ℝ,
          eval (Arch.attention sees (rmsNorm ε) H dh) 1 θ X ≠ eval A' 0 θ' X := by
  sorry

/-- **Theorem 4.3 for residual networks of attention blocks, `ε = 0`.** For almost every choice of
weights, the residual network equals no pre-RMSNorm skipless network with `ε = 0` and continuous
blocks. -/
theorem ae_not_dense_eq_skipless_rmsNorm_zero_attention
    (hhead : ∃ ℓ, Nonempty (H ℓ) ∧ Nonempty (dh ℓ)) (t s : T) (hts : sees t s)
    (μ : Measure (Params (Arch.attention (T := T) (d := d) sees (rmsNorm 0) H dh) dIn dOut))
    [μ.IsAddHaarMeasure]
    (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, ∀ (L' : ℕ) (d' : Type) [Fintype d'] (A' : Arch T d' L'), A'.χ = rmsNorm 0 →
      (∀ ℓ, Continuous (A'.f ℓ)) → ∀ θ' : Params A' dIn dOut,
        ¬ ∃ S : Set (Matrix T dIn ℝ), Dense S ∧
          ∀ X ∈ S, DefinedAt (Arch.attention sees (rmsNorm 0) H dh) 1 θ X ∧ DefinedAt A' 0 θ' X ∧
            eval (Arch.attention sees (rmsNorm 0) H dh) 1 θ X = eval A' 0 θ' X := by
  sorry

/-! ### Transformers: attention blocks and MLP blocks -/

/-- For a network of attention blocks and MLP blocks whose activation is nonzero on the positive
reals, in which some block has a hidden unit: for almost every choice of weights, some block has a
nonzero output at some normalized state. -/
theorem ae_someBlockNonzero_attention_mlp [Nonempty T] [Nonempty d]
    {χ : Matrix T d ℝ → Matrix T d ℝ} (hσ : ∀ z, 0 < z → σ z ≠ 0) (hhid : ∃ ℓ, Nonempty (hid ℓ))
    (μ : Measure (Params ((Arch.attention (T := T) (d := d) sees χ H dh).sum
      (Arch.mlp σ χ hid)) dIn dOut)) [μ.IsAddHaarMeasure] :
    ∀ᵐ θ ∂μ, SomeBlockNonzero ((Arch.attention sees χ H dh).sum (Arch.mlp σ χ hid)) θ := by
  sorry

/-- **Theorem 4.3 for residual networks of attention blocks and MLP blocks, `ε > 0`,** with an
activation that is locally Lipschitz and nonzero on the positive reals: for almost every choice of
weights (`d_in, d_out ≥ d ≥ 2`, some block has a hidden unit), the residual network equals no
pre-RMSNorm skipless network with locally Lipschitz blocks of any kind. -/
theorem ae_ne_skipless_rmsNorm_attention_mlp [Nonempty T] {ε : ℝ} (hε : 0 < ε)
    (hσ : ∀ z, 0 < z → σ z ≠ 0) (hσL : LocallyLipschitz σ) (hhid : ∃ ℓ, Nonempty (hid ℓ))
    (μ : Measure (Params ((Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh).sum
      (Arch.mlp σ (rmsNorm ε) hid)) dIn dOut)) [μ.IsAddHaarMeasure]
    (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, ∀ (L' : ℕ) (d' : Type) [Fintype d'] (A' : Arch T d' L') (ε' : ℝ), 0 < ε' →
      A'.χ = rmsNorm ε' → (∀ ℓ, LocallyLipschitz (A'.f ℓ)) → ∀ θ' : Params A' dIn dOut,
        ∃ X : Matrix T dIn ℝ,
          eval ((Arch.attention sees (rmsNorm ε) H dh).sum (Arch.mlp σ (rmsNorm ε) hid)) 1 θ X
            ≠ eval A' 0 θ' X := by
  sorry

/-- **Theorem 4.3 for residual networks of attention blocks and MLP blocks, `ε = 0`.** -/
theorem ae_not_dense_eq_skipless_rmsNorm_zero_attention_mlp [Nonempty T]
    (hσ : ∀ z, 0 < z → σ z ≠ 0) (hσL : LocallyLipschitz σ) (hhid : ∃ ℓ, Nonempty (hid ℓ))
    (μ : Measure (Params ((Arch.attention (T := T) (d := d) sees (rmsNorm 0) H dh).sum
      (Arch.mlp σ (rmsNorm 0) hid)) dIn dOut)) [μ.IsAddHaarMeasure]
    (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, ∀ (L' : ℕ) (d' : Type) [Fintype d'] (A' : Arch T d' L'), A'.χ = rmsNorm 0 →
      (∀ ℓ, Continuous (A'.f ℓ)) → ∀ θ' : Params A' dIn dOut,
        ¬ ∃ S : Set (Matrix T dIn ℝ), Dense S ∧
          ∀ X ∈ S,
            DefinedAt ((Arch.attention sees (rmsNorm 0) H dh).sum (Arch.mlp σ (rmsNorm 0) hid))
                1 θ X ∧ DefinedAt A' 0 θ' X ∧
              eval ((Arch.attention sees (rmsNorm 0) H dh).sum (Arch.mlp σ (rmsNorm 0) hid)) 1 θ X
                = eval A' 0 θ' X := by
  sorry

/-! ### Transformers: attention blocks and gated blocks -/

/-- For a network of attention blocks and gated blocks whose gate is nonzero on the positive
reals, in which some block has a hidden unit: for almost every choice of weights, some block has a
nonzero output at some normalized state. -/
theorem ae_someBlockNonzero_attention_gated [Nonempty T] [Nonempty d]
    {χ : Matrix T d ℝ → Matrix T d ℝ} (hσ : ∀ z, 0 < z → σ z ≠ 0) (hhid : ∃ ℓ, Nonempty (hid ℓ))
    (μ : Measure (Params ((Arch.attention (T := T) (d := d) sees χ H dh).sum
      (Arch.gated σ χ hid)) dIn dOut)) [μ.IsAddHaarMeasure] :
    ∀ᵐ θ ∂μ, SomeBlockNonzero ((Arch.attention sees χ H dh).sum (Arch.gated σ χ hid)) θ := by
  sorry

/-- **Theorem 4.3 for residual networks of attention blocks and gated blocks, `ε > 0`,** with a
gate that is locally Lipschitz and nonzero on the positive reals. -/
theorem ae_ne_skipless_rmsNorm_attention_gated [Nonempty T] {ε : ℝ} (hε : 0 < ε)
    (hσ : ∀ z, 0 < z → σ z ≠ 0) (hσL : LocallyLipschitz σ) (hhid : ∃ ℓ, Nonempty (hid ℓ))
    (μ : Measure (Params ((Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh).sum
      (Arch.gated σ (rmsNorm ε) hid)) dIn dOut)) [μ.IsAddHaarMeasure]
    (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, ∀ (L' : ℕ) (d' : Type) [Fintype d'] (A' : Arch T d' L') (ε' : ℝ), 0 < ε' →
      A'.χ = rmsNorm ε' → (∀ ℓ, LocallyLipschitz (A'.f ℓ)) → ∀ θ' : Params A' dIn dOut,
        ∃ X : Matrix T dIn ℝ,
          eval ((Arch.attention sees (rmsNorm ε) H dh).sum (Arch.gated σ (rmsNorm ε) hid)) 1 θ X
            ≠ eval A' 0 θ' X := by
  sorry

/-- **Theorem 4.3 for residual networks of attention blocks and gated blocks, `ε = 0`.** -/
theorem ae_not_dense_eq_skipless_rmsNorm_zero_attention_gated [Nonempty T]
    (hσ : ∀ z, 0 < z → σ z ≠ 0) (hσL : LocallyLipschitz σ) (hhid : ∃ ℓ, Nonempty (hid ℓ))
    (μ : Measure (Params ((Arch.attention (T := T) (d := d) sees (rmsNorm 0) H dh).sum
      (Arch.gated σ (rmsNorm 0) hid)) dIn dOut)) [μ.IsAddHaarMeasure]
    (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, ∀ (L' : ℕ) (d' : Type) [Fintype d'] (A' : Arch T d' L'), A'.χ = rmsNorm 0 →
      (∀ ℓ, Continuous (A'.f ℓ)) → ∀ θ' : Params A' dIn dOut,
        ¬ ∃ S : Set (Matrix T dIn ℝ), Dense S ∧
          ∀ X ∈ S,
            DefinedAt ((Arch.attention sees (rmsNorm 0) H dh).sum (Arch.gated σ (rmsNorm 0) hid))
                1 θ X ∧ DefinedAt A' 0 θ' X ∧
              eval ((Arch.attention sees (rmsNorm 0) H dh).sum (Arch.gated σ (rmsNorm 0) hid))
                  1 θ X
                = eval A' 0 θ' X := by
  sorry

/-! ### The named kinds: GELU and SwiGLU transformers -/

/-- **Theorem 4.3 for a pre-RMSNorm transformer of attention blocks and GELU blocks, `ε > 0`.** -/
theorem ae_ne_skipless_rmsNorm_attention_gelu [Nonempty T] {ε : ℝ} (hε : 0 < ε)
    (hhid : ∃ ℓ, Nonempty (hid ℓ))
    (μ : Measure (Params ((Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh).sum
      (Arch.mlp gelu (rmsNorm ε) hid)) dIn dOut)) [μ.IsAddHaarMeasure]
    (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, ∀ (L' : ℕ) (d' : Type) [Fintype d'] (A' : Arch T d' L') (ε' : ℝ), 0 < ε' →
      A'.χ = rmsNorm ε' → (∀ ℓ, LocallyLipschitz (A'.f ℓ)) → ∀ θ' : Params A' dIn dOut,
        ∃ X : Matrix T dIn ℝ,
          eval ((Arch.attention sees (rmsNorm ε) H dh).sum (Arch.mlp gelu (rmsNorm ε) hid)) 1 θ X
            ≠ eval A' 0 θ' X := by
  sorry

/-- **Theorem 4.3 for a pre-RMSNorm transformer of attention blocks and SwiGLU blocks,
`ε > 0`.** -/
theorem ae_ne_skipless_rmsNorm_attention_swiglu [Nonempty T] {ε : ℝ} (hε : 0 < ε)
    (hhid : ∃ ℓ, Nonempty (hid ℓ))
    (μ : Measure (Params ((Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh).sum
      (Arch.gated silu (rmsNorm ε) hid)) dIn dOut)) [μ.IsAddHaarMeasure]
    (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, ∀ (L' : ℕ) (d' : Type) [Fintype d'] (A' : Arch T d' L') (ε' : ℝ), 0 < ε' →
      A'.χ = rmsNorm ε' → (∀ ℓ, LocallyLipschitz (A'.f ℓ)) → ∀ θ' : Params A' dIn dOut,
        ∃ X : Matrix T dIn ℝ,
          eval ((Arch.attention sees (rmsNorm ε) H dh).sum (Arch.gated silu (rmsNorm ε) hid))
              1 θ X
            ≠ eval A' 0 θ' X := by
  sorry

end Skips
