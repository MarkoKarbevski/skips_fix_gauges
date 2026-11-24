import SkipsLean.Basic.RMSNorm
import SkipsLean.Dimension.Space

/-!
# Skipless networks are limits of residual networks

Paper ("Can an MLP Absorb Its Skip Connection Exactly?"): Proposition 5.1 with its proof in
Appendix A and Remark A.16 (the rate `1/t`).

Let `F` be a skipless network whose blocks are locally Lipschitz.

(i) Without normalization, for `t ≥ 1` let `F_t` be the residual network with the embedding of `F`,
the reads `t^{1-ℓ} W_read^ℓ`, the writes `t^ℓ W_write^ℓ` and the readout `t^{-L} D` (blocks
`ℓ = 1, …, L`). On every bounded set of inputs, `‖F_t(X) - F(X)‖ ≤ C / t`.

(ii) Under pre-RMSNorm with `ε = 0`, let `F_t` keep the embedding, the reads and the readout of `F`
and have the writes `t^ℓ W_write^ℓ`. On every compact set of inputs at which `F` is defined (no row
of `X E` or of a hidden state of `F` vanishes) there are `C` and `t_0` such that, for `t ≥ t_0`,
`F_t` is defined and `‖F_t(X) - F(X)‖ ≤ C / t`.

Here the blocks are `ℓ : Fin L`, the paper's block `ℓ + 1`, so the exponents are shifted by one. A
block is `n ↦ f_ℓ(n W_read) W_write`; it is locally Lipschitz when `f_ℓ` is. Norms are the
elementwise norms of matrices; the statements do not depend on the choice of norm.
-/

namespace Skips

open Matrix Filter
open scoped Matrix.Norms.Elementwise Topology

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable (A : Arch T d L)

/-- The weights of the residual network `F_t` of Proposition 5.1 (i): the embedding of `F`, the
reads `t^{1-ℓ} W_read^ℓ`, the writes `t^ℓ W_write^ℓ` (for the paper's block `ℓ`, here `ℓ + 1`) and
the readout `t^{-L} D`. -/
noncomputable def Params.limitScale {A : Arch T d L} (θ : Params A dIn dOut) (t : ℝ) :
    Params A dIn dOut where
  E := θ.E
  read ℓ := (t ^ (ℓ : ℕ))⁻¹ • θ.read ℓ
  write ℓ := t ^ ((ℓ : ℕ) + 1) • θ.write ℓ
  D := (t ^ L)⁻¹ • θ.D

/-- The weights of the residual network `F_t` of Proposition 5.1 (ii): the embedding, the reads and
the readout of `F`, and the writes `t^ℓ W_write^ℓ` (for the paper's block `ℓ`, here `ℓ + 1`). -/
noncomputable def Params.writeScale {A : Arch T d L} (θ : Params A dIn dOut) (t : ℝ) :
    Params A dIn dOut where
  E := θ.E
  read := θ.read
  write ℓ := t ^ ((ℓ : ℕ) + 1) • θ.write ℓ
  D := θ.D

/-- A network (with the stream matrices `S`) is **defined at** the input `X`, for `ε = 0`: no row of
`X E` or of a later hidden state vanishes. -/
def DefinedAt (S : Fin L → Matrix d d ℝ) (θ : Params A dIn dOut) (X : Matrix T dIn ℝ) : Prop :=
  ∀ (k : Fin (L + 1)) (t : T), hidden A S θ X k t ≠ 0

variable (θ : Params A dIn dOut)

/-- **Proposition 5.1 (i) with the rate of Remark A.16:** without normalization, if the maps `f_ℓ`
of the blocks are locally Lipschitz, then on every bounded set `𝒳` of inputs there is `C` with
`‖F_t(X) - F(X)‖ ≤ C / t` for all `X ∈ 𝒳` and `t ≥ 1`. -/
theorem exists_bound_eval_limitScale (hχ : A.χ = id) (hf : ∀ ℓ, LocallyLipschitz (A.f ℓ))
    (𝒳 : Set (Matrix T dIn ℝ)) (h𝒳 : Bornology.IsBounded 𝒳) :
    ∃ C : ℝ, ∀ X ∈ 𝒳, ∀ t : ℝ, 1 ≤ t →
      ‖eval A 1 (θ.limitScale t) X - eval A 0 θ X‖ ≤ C / t := by
  sorry

/-- **Proposition 5.1 (i):** without normalization, a skipless network whose blocks are locally
Lipschitz is the limit, uniformly on bounded sets of inputs, of the residual networks `F_t`, which
have blocks of the same kinds and widths. -/
theorem tendstoUniformlyOn_eval_limitScale (hχ : A.χ = id)
    (hf : ∀ ℓ, LocallyLipschitz (A.f ℓ)) (𝒳 : Set (Matrix T dIn ℝ))
    (h𝒳 : Bornology.IsBounded 𝒳) :
    TendstoUniformlyOn (fun (t : ℝ) (X : Matrix T dIn ℝ) => eval A 1 (θ.limitScale t) X)
      (fun X => eval A 0 θ X) atTop 𝒳 := by
  sorry

/-- **Proposition 5.1 (ii) with the rate of Remark A.16:** under pre-RMSNorm with `ε = 0`, if the
maps `f_ℓ` of the blocks are locally Lipschitz, then on every compact set `𝒳` of inputs at which
`F` is defined there are `C` and `t_0` such that, for all `X ∈ 𝒳` and `t ≥ t_0`, the residual
network `F_t` is defined at `X` and `‖F_t(X) - F(X)‖ ≤ C / t`. -/
theorem exists_bound_eval_writeScale (hχ : A.χ = rmsNorm 0)
    (hf : ∀ ℓ, LocallyLipschitz (A.f ℓ)) (𝒳 : Set (Matrix T dIn ℝ)) (h𝒳 : IsCompact 𝒳)
    (hdef : ∀ X ∈ 𝒳, DefinedAt A 0 θ X) :
    ∃ C t₀ : ℝ, ∀ X ∈ 𝒳, ∀ t : ℝ, t₀ ≤ t →
      DefinedAt A 1 (θ.writeScale t) X ∧
        ‖eval A 1 (θ.writeScale t) X - eval A 0 θ X‖ ≤ C / t := by
  sorry

/-- **Proposition 5.1 (ii):** under pre-RMSNorm with `ε = 0`, a skipless network whose blocks are
locally Lipschitz is the limit of the residual networks `F_t`, uniformly on compact sets of inputs
at which it is defined. -/
theorem tendstoUniformlyOn_eval_writeScale (hχ : A.χ = rmsNorm 0)
    (hf : ∀ ℓ, LocallyLipschitz (A.f ℓ)) (𝒳 : Set (Matrix T dIn ℝ)) (h𝒳 : IsCompact 𝒳)
    (hdef : ∀ X ∈ 𝒳, DefinedAt A 0 θ X) :
    TendstoUniformlyOn (fun (t : ℝ) (X : Matrix T dIn ℝ) => eval A 1 (θ.writeScale t) X)
      (fun X => eval A 0 θ X) atTop 𝒳 := by
  sorry

end Skips
