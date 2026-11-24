import SkipsLean.Depth.StepTanhRMS
import SkipsLean.Depth.SuffixGated

/-!
# The identity for one gated block

Paper (dimension): Appendix D.5, "The identity for one GELU or gated block", equations (26) to
(30), for a gated block.

"Fix `k < L` and write `W_g = W_g^{k+1}`, with the columns `c_1, …, c_q`, `V = W_write^{k+1}`, with
the rows `a_1, …, a_q`, `ι = ι^{k+1}` and `𝓑 = 𝓑_{>k+1}`, and in a gated block `W_v = W_v^{k+1}`,
with the columns `e_1, …, e_q`. Let `Z` and `η = (η_g, η_v, η_V, η')` be as in `(D_k)` […]. For a
row `n` let `ñ = n Z` in the case (n) and `ñ = n Z − ⟨n Z, n⟩ n / d_model` in the case (+). For
rows `n` and `w̃, w̃' ∈ ℝ^{1×q}` let

  `ż^g(n) = ñ W_g + n η_g`,   `ż^v(n) = ñ W_v + n η_v` in a gated block,   (26)

  `𝓛(w̃, w̃'; n) = 𝐃𝓑(ŵ V) ((w̃' ⊙ ż^g(n) ⊙ ι(n) + w̃ ⊙ ż^v(n)) V + ŵ η_V) + 𝐃_θ 𝓑(ŵ V) η'`,   (27)

where `ŵ = w̃ ⊙ ι(n)` […]. By the chain rule and (14), the left side of (16) at `h` is
`𝓛(σ(n W_g), σ'(n W_g); n)` at `n = χ(h)`. As in Lemma D.6, (16) for `k` therefore holds if and only
if `𝓛(σ(n W_g), σ'(n W_g); n) = 0` for every row `n ∈ ℝ^{1×d_model}` (28). We use two properties of
`𝓛`. The row `w̃'` enters only through the terms `w̃'_j ż^g_j(n) ι_j(n) a_j`, so
`∂𝓛/∂w̃'_j (w̃, w̃'; n) = ż^g_j(n) ι_j(n) 𝐃𝓑(ŵ V) a_j` (29). And in a gated block `ż^g` and `ż^v` are
odd in `n`, while `ŵ` does not change when `w̃` and `n` both change their sign, so
`𝓛(−w̃, w̃'; −n) = 𝓛(w̃, w̃'; n)` in a gated block (30)."

In Lean the read of a gated block is `[W_g | W_v]` (gate column `Sum.inl j`, value column
`Sum.inr j`), so `n W_read` holds the gates `n W_g` and the values `ι(n) = n W_v`, and one matrix
`zdot = ñ W_read + n η_read` holds `ż^g(n)` and `ż^v(n)`. A hidden state has the rows `T`; the
paper's rows are the case of one token. `blockLHSGated` takes the matrices `n W_read` and `zdot`
as arguments in the place of `n`: (29) and (30) are then statements about these arguments.
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise Topology

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]
variable {σ σ' : ℝ → ℝ} {χ : Matrix T d ℝ → Matrix T d ℝ} {ε : ℝ}

/-- **The left side of the identity for one gated block,** equation (27) of the paper:
`𝓛 = 𝐃𝓑(ŵ V) ((w̃' ⊙ ż^g ⊙ ι + w̃ ⊙ ż^v) V + ŵ η_V) + 𝐃_θ 𝓑(ŵ V) η` with `ŵ = w̃ ⊙ ι`, for block `k`
with the write `V` and the network `𝓑` after it. Here `w` stands for the gates `w̃`, `w'` for their
derivatives `w̃'`, `z` for what the hidden units read (its value columns are `ι`), and `zdot` for
the derivative of what they read (its gate columns are `ż^g`, its value columns `ż^v`). (The network
after the block does not depend on the weights of the block, so `𝐃_θ 𝓑 η` is the paper's
`𝐃_θ 𝓑 η'`.) -/
noncomputable def blockLHSGated (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut)
    (k : Fin L) (η : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut)
    (w w' : Matrix T (hid k) ℝ) (z zdot : Matrix T (hid k ⊕ hid k) ℝ) : Matrix T dOut ℝ :=
  fderiv ℝ (fun h' : Matrix T d ℝ => suffix (Arch.gated σ χ hid) 0 θ k.succ h')
      ((Matrix.of fun t j => w t j * z t (Sum.inr j)) * θ.write k)
      ((Matrix.of fun t j =>
            w' t j * zdot t (Sum.inl j) * z t (Sum.inr j) + w t j * zdot t (Sum.inr j))
          * θ.write k
        + (Matrix.of fun t j => w t j * z t (Sum.inr j)) * η.write k)
    + fderiv ℝ (fun θ' : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut =>
        suffix (Arch.gated σ χ hid) 0 θ' k.succ
          ((Matrix.of fun t j => w t j * z t (Sum.inr j)) * θ.write k)) θ η

/-- **Equation (29), in additive form:** `𝓛` is affine in `w̃'`, and a change `x'` of `w̃'` changes
`𝓛` by `𝐃𝓑(ŵ V) ((x' ⊙ ż^g ⊙ ι) V)`. -/
theorem blockLHSGated_add_right
    (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut) (k : Fin L)
    (η : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut)
    (w w' x' : Matrix T (hid k) ℝ) (z zdot : Matrix T (hid k ⊕ hid k) ℝ) :
    blockLHSGated θ k η w (w' + x') z zdot
      = blockLHSGated θ k η w w' z zdot
        + fderiv ℝ (fun h' : Matrix T d ℝ => suffix (Arch.gated σ χ hid) 0 θ k.succ h')
            ((Matrix.of fun t j => w t j * z t (Sum.inr j)) * θ.write k)
            ((Matrix.of fun t j => x' t j * zdot t (Sum.inl j) * z t (Sum.inr j)) * θ.write k) := by
  sorry

/-- **Equation (30):** `𝓛(−w̃, w̃'; −n) = 𝓛(w̃, w̃'; n)` in a gated block. -/
theorem blockLHSGated_neg
    (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut) (k : Fin L)
    (η : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut)
    (w w' : Matrix T (hid k) ℝ) (z zdot : Matrix T (hid k ⊕ hid k) ℝ) :
    blockLHSGated θ k η (-w) w' (-z) (-zdot) = blockLHSGated θ k η w w' z zdot := by
  sorry

/-- **The identity for one gated block, case (n)** (equation (28), by the chain rule): for a gated
block whose gate `σ` has the derivative `σ'`, the identity (16) for the hidden state before block
`k` holds for `Z` and `η` if and only if `𝓛(σ(n W_g), σ'(n W_g); n) = 0` for all `n`, with
`ż(n) = n (Z W_read + η_read)` (equation (26), case (n)). -/
theorem suffixFlat_castSucc_iff_gated (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) (k : Fin L)
    (Z : Matrix d d ℝ) (η : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) :
    SuffixFlat (Arch.gated σ id hid) θ k.castSucc Z η ↔
      ∀ n : Matrix T d ℝ,
        blockLHSGated θ k η (Matrix.of fun t j => σ ((n * θ.read k) t (Sum.inl j)))
          (Matrix.of fun t j => σ' ((n * θ.read k) t (Sum.inl j)))
          (n * θ.read k) (n * (Z * θ.read k + η.read k)) = 0 := by
  sorry

/-- **The identity for one gated block, case (+)** (equation (28); as in Lemma D.6): for a
real-analytic gate, under pre-RMSNorm with `ε > 0`, the identity (16) before block `k` holds if and
only if `𝓛(σ(n W_g), σ'(n W_g); n) = 0` for every `n`, with
`ż(n) = (n Z − ⟨n Z, n⟩ n / d) W_read + n η_read` (equation (26), case (+)): the left side is
real-analytic in `n`, and the values of `N_ε` form an open set. -/
theorem suffixFlat_castSucc_iff_gated_rmsNorm (hε : 0 < ε) (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (θ : Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut) (k : Fin L)
    (Z : Matrix d d ℝ) (η : Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut) :
    SuffixFlat (Arch.gated σ (rmsNorm ε) hid) θ k.castSucc Z η ↔
      ∀ n : Matrix T d ℝ,
        blockLHSGated θ k η (Matrix.of fun t j => σ ((n * θ.read k) t (Sum.inl j)))
          (Matrix.of fun t j => σ' ((n * θ.read k) t (Sum.inl j)))
          (n * θ.read k) (tangentRMS Z n * θ.read k + n * η.read k) = 0 := by
  sorry

end Skips
