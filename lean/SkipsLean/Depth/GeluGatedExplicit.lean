import SkipsLean.Depth.StepGated

/-!
# GELU and gated blocks at depth: the claim `(D_0)` at one explicit parameter

Paper (dimension): Appendix D.7, "The parts together", second paragraph. "GELU blocks in the case
(+), and gated blocks in the cases (n) and (+). By Lemma D.13, `θ†` is good, so it is regular, and
no value column vanishes. `(D_L)` holds at `θ†` (Lemma D.5), and by Lemma D.12, applied for
`k = L − 1`, then for `k = L − 2`, and so on down to `k = 0`, so does `(D_0)`."

Stated here: what these three lemmas give together, for each of the five settings of
Theorem 5.2 (ii) with `ε > 0` and (iii): there is a regular parameter, with no vanishing value
column for gated blocks, at which Claim `(D_0)` holds. The scope is that of Theorem 5.2:
`d_in, d_out ≥ d ≥ 2` and at least `d` hidden units in every block.

These statements are the whole of Appendix D.5 (Lemmas D.8 to D.13). Their proofs are not written
yet; the lemmas of Appendix D.5 will be stated in files of their own, and these five statements
will follow from them.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise Topology

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]

/-- **GELU blocks, case (+)** (Lemmas D.5, D.12, D.13): a regular parameter at which `(D_0)` holds. -/
theorem exists_regular_claimRMS_gelu [Nonempty T] {ε : ℝ} (hε : 0 < ε) (hd : 2 ≤ Fintype.card d)
    (hdIn : Fintype.card d ≤ Fintype.card dIn) (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∃ θ : Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm ε) hid) dIn dOut,
      Regular (Arch.mlp gelu (rmsNorm ε) hid) θ ∧ ClaimRMS (Arch.mlp gelu (rmsNorm ε) hid) θ 0 := by
  sorry

/-- **SwiGLU blocks, case (n)** (Lemmas D.5, D.12, D.13): a regular parameter with no vanishing value
column at which `(D_0)` holds. -/
theorem exists_regular_claimGated_swiglu [Nonempty T] (hd : 2 ≤ Fintype.card d)
    (hdIn : Fintype.card d ≤ Fintype.card dIn) (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∃ θ : Params (Arch.gated (T := T) (d := d) silu id hid) dIn dOut,
      Regular (Arch.gated silu id hid) θ ∧ (∀ ℓ i, (fun k => θ.read ℓ k (Sum.inr i)) ≠ 0) ∧
        ClaimGated ⊤ θ 0 := by
  sorry

/-- **SwiGLU blocks, case (+).** -/
theorem exists_regular_claimGated_swiglu_rmsNorm [Nonempty T] {ε : ℝ} (hε : 0 < ε) (hd : 2 ≤ Fintype.card d)
    (hdIn : Fintype.card d ≤ Fintype.card dIn) (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∃ θ : Params (Arch.gated (T := T) (d := d) silu (rmsNorm ε) hid) dIn dOut,
      Regular (Arch.gated silu (rmsNorm ε) hid) θ ∧ (∀ ℓ i, (fun k => θ.read ℓ k (Sum.inr i)) ≠ 0) ∧
        ClaimGated (antisymmetric d) θ 0 := by
  sorry

/-- **GeGLU blocks, case (n).** -/
theorem exists_regular_claimGated_geglu [Nonempty T] (hd : 2 ≤ Fintype.card d)
    (hdIn : Fintype.card d ≤ Fintype.card dIn) (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∃ θ : Params (Arch.gated (T := T) (d := d) gelu id hid) dIn dOut,
      Regular (Arch.gated gelu id hid) θ ∧ (∀ ℓ i, (fun k => θ.read ℓ k (Sum.inr i)) ≠ 0) ∧
        ClaimGated ⊤ θ 0 := by
  sorry

/-- **GeGLU blocks, case (+).** -/
theorem exists_regular_claimGated_geglu_rmsNorm [Nonempty T] {ε : ℝ} (hε : 0 < ε) (hd : 2 ≤ Fintype.card d)
    (hdIn : Fintype.card d ≤ Fintype.card dIn) (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∃ θ : Params (Arch.gated (T := T) (d := d) gelu (rmsNorm ε) hid) dIn dOut,
      Regular (Arch.gated gelu (rmsNorm ε) hid) θ ∧ (∀ ℓ i, (fun k => θ.read ℓ k (Sum.inr i)) ≠ 0) ∧
        ClaimGated (antisymmetric d) θ 0 := by
  sorry

end Skips
