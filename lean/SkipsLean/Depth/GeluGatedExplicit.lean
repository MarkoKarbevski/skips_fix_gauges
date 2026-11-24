import SkipsLean.Depth.StepGated
import SkipsLean.Depth.Cones
import SkipsLean.Depth.SuffixGated
import SkipsLean.Depth.SuffixRMS

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

/-- Helper: `(D_k)` for every `k`, SwiGLU blocks, case (n): `(D_L)` by Lemma D.5, then Lemma D.12
for `k = L - 1, …, 0`. -/
private theorem claimGated_all_swiglu [Nonempty T] {C : Fin (L + 1) → Set (d → ℝ)}
    {A : ∀ ℓ, Finset (hid ℓ)} {θ : Params (Arch.gated (T := T) (d := d) silu id hid) dIn dOut}
    (hθ : GoodForConesGated C A θ)
    (hQ : ∀ ℓ, LinearIndependent ℚ (fun j : hid ℓ => (θ.read ℓ)ᵀ (Sum.inl j)))
    (k : Fin (L + 1)) : ClaimGated ⊤ θ k := by
  induction k using Fin.reverseInduction with
  | last => exact claimGated_last θ
  | cast k ih => exact claimGated_castSucc_swiglu hθ hQ k ih

/-- Helper: `(D_k)` for every `k`, SwiGLU blocks, case (+). -/
private theorem claimGated_all_swiglu_rmsNorm [Nonempty T] {ε : ℝ} (hε : 0 < ε)
    {C : Fin (L + 1) → Set (d → ℝ)} {A : ∀ ℓ, Finset (hid ℓ)}
    {θ : Params (Arch.gated (T := T) (d := d) silu (rmsNorm ε) hid) dIn dOut}
    (hθ : GoodForConesGated C A θ)
    (hQ : ∀ ℓ, LinearIndependent ℚ (fun j : hid ℓ => (θ.read ℓ)ᵀ (Sum.inl j)))
    (k : Fin (L + 1)) : ClaimGated (antisymmetric d) θ k := by
  induction k using Fin.reverseInduction with
  | last => exact claimGated_last_rmsNorm hε θ hθ.rank_D
  | cast k ih => exact claimGated_castSucc_swiglu_rmsNorm hε hθ hQ k ih

/-- Helper: `(D_k)` for every `k`, GeGLU blocks, case (n). -/
private theorem claimGated_all_geglu [Nonempty T] {C : Fin (L + 1) → Set (d → ℝ)}
    {A : ∀ ℓ, Finset (hid ℓ)} {θ : Params (Arch.gated (T := T) (d := d) gelu id hid) dIn dOut}
    (hθ : GoodForConesGated C A θ)
    (hQ : ∀ ℓ, LinearIndependent ℚ (fun j : hid ℓ =>
      Matrix.vecMulVec ((θ.read ℓ)ᵀ (Sum.inl j)) ((θ.read ℓ)ᵀ (Sum.inl j))))
    (k : Fin (L + 1)) : ClaimGated ⊤ θ k := by
  induction k using Fin.reverseInduction with
  | last => exact claimGated_last θ
  | cast k ih => exact claimGated_castSucc_geglu hθ hQ k ih

/-- Helper: `(D_k)` for every `k`, GeGLU blocks, case (+). -/
private theorem claimGated_all_geglu_rmsNorm [Nonempty T] {ε : ℝ} (hε : 0 < ε)
    {C : Fin (L + 1) → Set (d → ℝ)} {A : ∀ ℓ, Finset (hid ℓ)}
    {θ : Params (Arch.gated (T := T) (d := d) gelu (rmsNorm ε) hid) dIn dOut}
    (hθ : GoodForConesGated C A θ)
    (hQ : ∀ ℓ, LinearIndependent ℚ (fun j : hid ℓ =>
      Matrix.vecMulVec ((θ.read ℓ)ᵀ (Sum.inl j)) ((θ.read ℓ)ᵀ (Sum.inl j))))
    (k : Fin (L + 1)) : ClaimGated (antisymmetric d) θ k := by
  induction k using Fin.reverseInduction with
  | last => exact claimGated_last_rmsNorm hε θ hθ.rank_D
  | cast k ih => exact claimGated_castSucc_geglu_rmsNorm hε hθ hQ k ih

/-- Helper: `(D_k)` for every `k`, GELU blocks, case (+). -/
private theorem claimRMS_all_gelu [Nonempty T] {ε : ℝ} (hε : 0 < ε)
    {C : Fin (L + 1) → Set (d → ℝ)} {A : ∀ ℓ, Finset (hid ℓ)}
    {θ : Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm ε) hid) dIn dOut}
    (hθ : GoodForConesMlp C A θ)
    (hQ : ∀ ℓ, LinearIndependent ℚ (fun j : hid ℓ =>
      Matrix.vecMulVec ((θ.read ℓ)ᵀ j) ((θ.read ℓ)ᵀ j)))
    (k : Fin (L + 1)) : ClaimRMS (Arch.mlp gelu (rmsNorm ε) hid) θ k := by
  induction k using Fin.reverseInduction with
  | last => exact claimRMS_last _ θ hε rfl hθ.rank_D
  | cast k ih => exact claimRMS_castSucc_gelu hε hθ hQ k ih

omit [DecidableEq d] [Fintype T] [Fintype dIn] in
/-- Helper: a good parameter has no vanishing value column (the same function as `(read)ᵀ`). -/
private theorem value_col_ne_zero {σ : ℝ → ℝ} {χ : Matrix T d ℝ → Matrix T d ℝ}
    {C : Fin (L + 1) → Set (d → ℝ)} {A : ∀ ℓ, Finset (hid ℓ)}
    {θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut}
    (hθ : GoodForConesGated C A θ) : ∀ ℓ i, (fun k => θ.read ℓ k (Sum.inr i)) ≠ 0 :=
  fun ℓ i h => hθ.value_ne_zero ℓ i (by funext k; exact congrFun h k)

/-- **GELU blocks, case (+)** (Lemmas D.5, D.12, D.13): a regular parameter at which `(D_0)` holds. -/
theorem exists_regular_claimRMS_gelu [Nonempty T] {ε : ℝ} (hε : 0 < ε) (hd : 2 ≤ Fintype.card d)
    (hdIn : Fintype.card d ≤ Fintype.card dIn) (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∃ θ : Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm ε) hid) dIn dOut,
      Regular (Arch.mlp gelu (rmsNorm ε) hid) θ ∧ ClaimRMS (Arch.mlp gelu (rmsNorm ε) hid) θ 0 := by
  have : Nonempty d := Fintype.card_pos_iff.1 (by omega)
  obtain ⟨C, A, θ, hθ, hQ⟩ := exists_goodForConesMlp_outer (σ := gelu) (χ := rmsNorm ε) (T := T)
    (dIn := dIn) (dOut := dOut) (hid := hid) hd hdIn hdOut hhid
  -- `θ` is regular, and `(D_0)` follows from `(D_L)` and Lemma D.12 downwards
  exact ⟨θ, regular_of_goodForConesMlp_gelu hθ, claimRMS_all_gelu hε hθ hQ 0⟩

/-- **SwiGLU blocks, case (n)** (Lemmas D.5, D.12, D.13): a regular parameter with no vanishing value
column at which `(D_0)` holds. -/
theorem exists_regular_claimGated_swiglu [Nonempty T] (hd : 2 ≤ Fintype.card d)
    (hdIn : Fintype.card d ≤ Fintype.card dIn) (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∃ θ : Params (Arch.gated (T := T) (d := d) silu id hid) dIn dOut,
      Regular (Arch.gated silu id hid) θ ∧ (∀ ℓ i, (fun k => θ.read ℓ k (Sum.inr i)) ≠ 0) ∧
        ClaimGated ⊤ θ 0 := by
  have : Nonempty d := Fintype.card_pos_iff.1 (by omega)
  obtain ⟨C, A, θ, hθ, hQ⟩ := exists_goodForConesGated_cols (σ := silu) (χ := id) (T := T)
    (dIn := dIn) (dOut := dOut) (hid := hid) hdIn hdOut hhid
  exact ⟨θ, regular_of_goodForConesGated_swiglu hθ, value_col_ne_zero hθ,
    claimGated_all_swiglu hθ hQ 0⟩

/-- **SwiGLU blocks, case (+).** -/
theorem exists_regular_claimGated_swiglu_rmsNorm [Nonempty T] {ε : ℝ} (hε : 0 < ε) (hd : 2 ≤ Fintype.card d)
    (hdIn : Fintype.card d ≤ Fintype.card dIn) (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∃ θ : Params (Arch.gated (T := T) (d := d) silu (rmsNorm ε) hid) dIn dOut,
      Regular (Arch.gated silu (rmsNorm ε) hid) θ ∧ (∀ ℓ i, (fun k => θ.read ℓ k (Sum.inr i)) ≠ 0) ∧
        ClaimGated (antisymmetric d) θ 0 := by
  have : Nonempty d := Fintype.card_pos_iff.1 (by omega)
  obtain ⟨C, A, θ, hθ, hQ⟩ := exists_goodForConesGated_cols (σ := silu) (χ := rmsNorm ε) (T := T)
    (dIn := dIn) (dOut := dOut) (hid := hid) hdIn hdOut hhid
  exact ⟨θ, regular_of_goodForConesGated_swiglu hθ, value_col_ne_zero hθ,
    claimGated_all_swiglu_rmsNorm hε hθ hQ 0⟩

/-- **GeGLU blocks, case (n).** -/
theorem exists_regular_claimGated_geglu [Nonempty T] (hd : 2 ≤ Fintype.card d)
    (hdIn : Fintype.card d ≤ Fintype.card dIn) (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∃ θ : Params (Arch.gated (T := T) (d := d) gelu id hid) dIn dOut,
      Regular (Arch.gated gelu id hid) θ ∧ (∀ ℓ i, (fun k => θ.read ℓ k (Sum.inr i)) ≠ 0) ∧
        ClaimGated ⊤ θ 0 := by
  obtain ⟨C, A, θ, hθ, hQ⟩ := exists_goodForConesGated_outer (σ := gelu) (χ := id) (T := T)
    (dIn := dIn) (dOut := dOut) (hid := hid) hd hdIn hdOut hhid
  exact ⟨θ, regular_of_goodForConesGated_geglu hθ, value_col_ne_zero hθ,
    claimGated_all_geglu hθ hQ 0⟩

/-- **GeGLU blocks, case (+).** -/
theorem exists_regular_claimGated_geglu_rmsNorm [Nonempty T] {ε : ℝ} (hε : 0 < ε) (hd : 2 ≤ Fintype.card d)
    (hdIn : Fintype.card d ≤ Fintype.card dIn) (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∃ θ : Params (Arch.gated (T := T) (d := d) gelu (rmsNorm ε) hid) dIn dOut,
      Regular (Arch.gated gelu (rmsNorm ε) hid) θ ∧ (∀ ℓ i, (fun k => θ.read ℓ k (Sum.inr i)) ≠ 0) ∧
        ClaimGated (antisymmetric d) θ 0 := by
  obtain ⟨C, A, θ, hθ, hQ⟩ := exists_goodForConesGated_outer (σ := gelu) (χ := rmsNorm ε) (T := T)
    (dIn := dIn) (dOut := dOut) (hid := hid) hd hdIn hdOut hhid
  exact ⟨θ, regular_of_goodForConesGated_geglu hθ, value_col_ne_zero hθ,
    claimGated_all_geglu_rmsNorm hε hθ hQ 0⟩

end Skips
