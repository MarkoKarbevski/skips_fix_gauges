import SkipsLean.Dimension.RescalingMlp
import SkipsLean.Dimension.GenericRank
import SkipsLean.Generic.Params

/-!
# The polynomial maps of the patterns of a ReLU network

Paper (absorb paper): proof of Proposition 4.7, Steps 1 and 2. "Step 1: patterns give polynomial
maps. A pattern on `Z` labels every unit, at every input of `Z`, active or inactive. Given a
pattern `π`, replace `ReLU(z)` in the network by `z` where `π` says active and by `0` where it
says inactive. The outputs on `Z` become a polynomial map `F^π_Z` of the weights. The pattern of
`θ` labels a unit active at an input if its argument there is positive, and inactive otherwise;
with this pattern, `F_Z(θ) = F^π_Z(θ)`." Step 2, for a skipless network of `L` blocks: "Its
pattern maps `F'^π_Z` do not change under a change of basis at each of its `L + 1` hidden states,
nor under the rescalings of its […] units. […] They are linearly independent when `E` and every
write have rank `d_model` and no read of a unit vanishes […]. So every `F'^π_Z` has rank at most
`P + 2 d_model n − (L + 1) d_model² − s − n` at every point", after "A polynomial map reaches its
largest rank on a nonempty open set, so the rank is at most `r` at every `θ`."

Here a pattern on one input labels every hidden unit of every block at every token
(`∀ ℓ, T → hid ℓ → Bool`). Replacing ReLU by the pattern gives a network in the frame of this
library: `Arch.masked π`, whose fixed map of block `ℓ` keeps the entries that `π` labels active
and sets the others to `0`. The weights are the same (`Params.toMasked`).

* `reluPattern S θ x`: the pattern of `θ` at the input `x`.
* `eval_relu_eq_eval_masked`: with its own pattern, the ReLU network is the network of the
  pattern, for any stream matrices (with or without skips).
* `maskedBatch S X π`: the map `F^π_Z` on a batch `X` with one pattern per input, as a map of the
  weights of the ReLU network; it is real-analytic.
* The rank bound for skipless networks, at every parameter: `rank ≤ P − (L + 1) d² − s`, for
  `d_in ≥ d ≥ 1` and blocks of at least `d` hidden units, `s = ∑_ℓ d_hidden^ℓ`.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]

/-- **The network of a pattern** (proof of Proposition 4.7, Step 1): block `ℓ` keeps the entry of
token `t` and hidden unit `j` if the pattern labels it active, and replaces it by `0` if not.
There is no normalization. -/
abbrev Arch.masked (π : ∀ ℓ : Fin L, T → hid ℓ → Bool) : Arch T d L where
  r := hid
  w := hid
  f ℓ M := Matrix.of fun t j => if π ℓ t j then M t j else 0
  χ := id

/-- The same weights, read as the parameters of the network of a pattern. -/
def Params.toMasked {σ : ℝ → ℝ} (π : ∀ ℓ : Fin L, T → hid ℓ → Bool)
    (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) :
    Params (Arch.masked (T := T) (d := d) π) dIn dOut where
  E := θ.E
  read := θ.read
  write := θ.write
  D := θ.D

/-- **The pattern of `θ` at the input `x`** (proof of Proposition 4.7, Step 1): a unit is labelled
active at a token if its argument there is positive, and inactive otherwise. -/
noncomputable def reluPattern (S : Fin L → Matrix d d ℝ)
    (θ : Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut) (x : Matrix T dIn ℝ) :
    ∀ ℓ : Fin L, T → hid ℓ → Bool :=
  fun ℓ t j => decide (0 < (hidden (Arch.mlp relu id hid) S θ x ℓ.castSucc * θ.read ℓ) t j)

/-- **Proof of Proposition 4.7, Step 1, "with this pattern, `F_Z(θ) = F^π_Z(θ)`", at one input:**
a ReLU network without normalization, with any stream matrices, is the network of its own
pattern. -/
theorem eval_relu_eq_eval_masked (S : Fin L → Matrix d d ℝ)
    (θ : Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut) (x : Matrix T dIn ℝ) :
    eval (Arch.mlp relu id hid) S θ x
      = eval (Arch.masked (reluPattern S θ x)) S (θ.toMasked (reluPattern S θ x)) x := by
  sorry

/-- **The map `F^π_Z` of the proof of Proposition 4.7:** the outputs on the batch `X` of the
networks of the patterns `π i`, one pattern per input, as a map of the weights. -/
noncomputable def maskedBatch (S : Fin L → Matrix d d ℝ) {n : ℕ}
    (X : Fin n → Matrix T dIn ℝ)
    (π : Fin n → ∀ ℓ : Fin L, T → hid ℓ → Bool)
    (θ : Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut) : Fin n → Matrix T dOut ℝ :=
  fun i => eval (Arch.masked (π i)) S (θ.toMasked (π i)) (X i)

/-- On a batch, a ReLU network is the map `F^π_Z` of its own patterns. -/
theorem evalBatch_relu_eq_maskedBatch (S : Fin L → Matrix d d ℝ) {n : ℕ}
    (X : Fin n → Matrix T dIn ℝ)
    (θ : Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut) :
    evalBatch (Arch.mlp relu id hid) S X θ
      = maskedBatch S X (fun i => reluPattern S θ (X i)) θ := by
  sorry

/-- **Proof of Proposition 4.7, Step 1, "a polynomial map of the weights":** `F^π_Z` is
real-analytic in the weights. -/
theorem analyticOnNhd_maskedBatch (S : Fin L → Matrix d d ℝ) {n : ℕ}
    (X : Fin n → Matrix T dIn ℝ) (π : Fin n → ∀ ℓ : Fin L, T → hid ℓ → Bool) :
    AnalyticOnNhd ℝ
      (maskedBatch (d := d) (dOut := dOut) S X π :
        Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut → Fin n → Matrix T dOut ℝ)
      Set.univ := by
  sorry

/-- **Proof of Proposition 4.7, Step 2, for a skipless network:** for `d_in ≥ d ≥ 1` and blocks
of at least `d` hidden units, the Jacobian of every pattern map `F'^π_Z` of the skipless network
has rank at most `P − (L + 1) d² − s` at every parameter, with `s` the number of hidden units. -/
theorem finrank_range_fderiv_maskedBatch_skipless_add_le [Nonempty d]
    (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) {n : ℕ}
    (X : Fin n → Matrix T dIn ℝ) (π : Fin n → ∀ ℓ : Fin L, T → hid ℓ → Bool)
    (θ : Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut) :
    Module.finrank ℝ (LinearMap.range
        (fderiv ℝ (maskedBatch (d := d) (dOut := dOut) 0 X π) θ).toLinearMap)
        + ((L + 1) * Fintype.card d ^ 2 + ∑ ℓ, Fintype.card (hid ℓ))
      ≤ Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut) := by
  sorry

end Skips
