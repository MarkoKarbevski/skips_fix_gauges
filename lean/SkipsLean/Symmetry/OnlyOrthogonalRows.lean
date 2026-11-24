import SkipsLean.Symmetry.OnlyOrthogonal
import SkipsLean.Network.Transformer

/-!
# Under pre-RMSNorm only orthogonal changes of basis pass: attention blocks and transformers

Paper (skips paper): Lemma A.4 (Only orthogonal changes of basis pass): "Consider a skipless
pre-RMSNorm network with `ε > 0` whose blocks are those of Section 2, and let `G_0, …, G_L` be
invertible. Multiply the writes into every hidden state `h_ℓ` by `G_ℓ` on the right and its reads
by `G_ℓ⁻¹` on the left. If this preserves the function at all parameters, every `G_ℓ` is
orthogonal." Its proof: "Take inputs whose tokens are all equal. Then the tokens of every hidden
state are equal, an MLP block acts on each of them, and an attention block maps equal rows `a` to
`aS`, with `S` the sum of its value–output products." and fact (b): "Blocks separate their inputs.
If rows `a` and `a′` satisfy `B(a) = B(a′)` for all parameters of a block `B`, then `a = a′`. For
an attention block on equal tokens, `aS = a′S` for every matrix `S`."

`Symmetry/OnlyOrthogonal.lean` has the lemma for MLP blocks and for gated blocks, with a proof on
all inputs. Here the lemma in the form of the paper's proof, on inputs whose tokens are all equal,
for any blocks that (`hrows`) map equal rows to equal rows, (`hsep`, fact (b)) separate equal-row
inputs, and (`hnz`, for fact (c)) make a nonzero hidden unit from every nonzero row; then for
attention blocks, and for the networks of `Network/Transformer.lean` (attention blocks and MLP
blocks, attention blocks and gated blocks, in any order). For attention every token sees some
token (`hsees`: for a token that sees none, the block writes `0` in its row, and the rows are not
equal). A block needs a head of width at least `1` or a hidden unit (a block with neither writes
`0`, and the hidden state after it carries no condition). With `eval_cob_rmsNorm` ("if"), this is
the skipless half of Theorem 3.3 (ii) under pre-RMSNorm for these networks: the changes of basis
that preserve the function at all parameters are exactly the orthogonal ones.
-/

namespace Skips

open Matrix

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {sees : T → T → Prop} [DecidableRel sees]
variable {H dh hid : Fin L → Type} [∀ ℓ, Fintype (H ℓ)] [∀ ℓ, Fintype (dh ℓ)]
  [∀ ℓ, Fintype (hid ℓ)] {σ : ℝ → ℝ} {ε : ℝ}

/-- **Lemma A.4 on inputs whose tokens are all equal, for any blocks:** let the blocks of a
skipless pre-RMSNorm network (`ε > 0`) map equal rows to equal rows (`hrows`), separate equal-row
inputs (`hsep`: fact (b)) and make a nonzero hidden unit from every nonzero row (`hnz`). If the
changes of basis `G_0, …, G_L` preserve the function for all values of the parameters, every
`G_ℓ` is orthogonal. -/
theorem orthogonal_of_eval_cob_skipless_rmsNorm_of_rows {A : Arch T d L} [Nonempty T]
    [Nonempty dIn] [Nonempty dOut] (hε : 0 < ε) (hA : A.χ = rmsNorm ε)
    (hrows : ∀ k (a : d → ℝ) (W : Matrix d (A.r k) ℝ), ∃ b : A.w k → ℝ,
      A.f k ((Matrix.of fun _ : T => a) * W) = Matrix.of fun _ : T => b)
    (hsep : ∀ k (a a' : d → ℝ),
      (∀ W : Matrix d (A.r k) ℝ, A.f k ((Matrix.of fun _ : T => a') * W)
        = A.f k ((Matrix.of fun _ : T => a) * W)) → a' = a)
    (hnz : ∀ k (a : d → ℝ), a ≠ 0 →
      ∃ (W : Matrix d (A.r k) ℝ) (t : T) (j : A.w k),
        A.f k ((Matrix.of fun _ : T => a) * W) t j ≠ 0)
    (G : Fin (L + 1) → GL d ℝ)
    (h : ∀ (θ : Params A dIn dOut) (x : Matrix T dIn ℝ),
      eval A 0 (θ.cob G G) x = eval A 0 θ x) :
    ∀ ℓ, (G ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ := by
  sorry

/-! ### Attention blocks -/

/-- **Lemma A.4 for attention blocks:** every token sees some token, and every block has a head
of width at least `1`. If the changes of basis `G_0, …, G_L` preserve the function of the skipless
pre-RMSNorm network (`ε > 0`) for all values of the parameters, every `G_ℓ` is orthogonal. -/
theorem orthogonal_of_eval_cob_skipless_rmsNorm_attention [Nonempty T] [Nonempty dIn]
    [Nonempty dOut] (hε : 0 < ε) (hsees : ∀ t, ∃ s, sees t s)
    (hH : ∀ ℓ, Nonempty (H ℓ)) (hdh : ∀ ℓ, Nonempty (dh ℓ)) (G : Fin (L + 1) → GL d ℝ)
    (h : ∀ (θ : Params (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut)
      (x : Matrix T dIn ℝ),
      eval (Arch.attention sees (rmsNorm ε) H dh) 0 (θ.cob G G) x
        = eval (Arch.attention sees (rmsNorm ε) H dh) 0 θ x) :
    ∀ ℓ, (G ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ := by
  sorry

/-- **Theorem 3.3 (ii), skipless, pre-RMSNorm (`ε > 0`), attention blocks:** the changes of basis
`G_0, …, G_L` preserve the function for all values of the parameters if and only if every `G_ℓ` is
orthogonal. -/
theorem eval_cob_skipless_rmsNorm_iff_attention [Nonempty T] [Nonempty dIn] [Nonempty dOut]
    (hε : 0 < ε) (hsees : ∀ t, ∃ s, sees t s)
    (hH : ∀ ℓ, Nonempty (H ℓ)) (hdh : ∀ ℓ, Nonempty (dh ℓ)) (G : Fin (L + 1) → GL d ℝ) :
    (∀ (θ : Params (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut)
        (x : Matrix T dIn ℝ),
        eval (Arch.attention sees (rmsNorm ε) H dh) 0 (θ.cob G G) x
          = eval (Arch.attention sees (rmsNorm ε) H dh) 0 θ x)
      ↔ ∀ ℓ, (G ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ := by
  sorry

/-! ### Attention blocks and MLP blocks -/

/-- **Lemma A.4 for networks of attention blocks and MLP blocks, in any order:** the activation
is continuous, not even and not constant; every token sees some token; every block has a head of
width at least `1` or a hidden unit. If the changes of basis `G_0, …, G_L` preserve the function
of the skipless pre-RMSNorm network (`ε > 0`) for all values of the parameters, every `G_ℓ` is
orthogonal. -/
theorem orthogonal_of_eval_cob_skipless_rmsNorm_attentionMlp [Nonempty T] [Nonempty dIn]
    [Nonempty dOut] (hε : 0 < ε) (hσc : Continuous σ) (hne : ¬ ∀ z, σ (-z) = σ z)
    (hnc : ¬ ∀ z, σ z = σ 0) (hsees : ∀ t, ∃ s, sees t s)
    (hblk : ∀ ℓ, (Nonempty (H ℓ) ∧ Nonempty (dh ℓ)) ∨ Nonempty (hid ℓ))
    (G : Fin (L + 1) → GL d ℝ)
    (h : ∀ (θ : Params
        (Arch.attentionMlp (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut)
      (x : Matrix T dIn ℝ),
      eval (Arch.attentionMlp sees σ (rmsNorm ε) H dh hid) 0 (θ.cob G G) x
        = eval (Arch.attentionMlp sees σ (rmsNorm ε) H dh hid) 0 θ x) :
    ∀ ℓ, (G ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ := by
  sorry

/-- **Theorem 3.3 (ii), skipless, pre-RMSNorm (`ε > 0`), attention blocks and MLP blocks:** the
changes of basis `G_0, …, G_L` preserve the function for all values of the parameters if and only
if every `G_ℓ` is orthogonal. -/
theorem eval_cob_skipless_rmsNorm_iff_attentionMlp [Nonempty T] [Nonempty dIn] [Nonempty dOut]
    (hε : 0 < ε) (hσc : Continuous σ) (hne : ¬ ∀ z, σ (-z) = σ z)
    (hnc : ¬ ∀ z, σ z = σ 0) (hsees : ∀ t, ∃ s, sees t s)
    (hblk : ∀ ℓ, (Nonempty (H ℓ) ∧ Nonempty (dh ℓ)) ∨ Nonempty (hid ℓ))
    (G : Fin (L + 1) → GL d ℝ) :
    (∀ (θ : Params
          (Arch.attentionMlp (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut)
        (x : Matrix T dIn ℝ),
        eval (Arch.attentionMlp sees σ (rmsNorm ε) H dh hid) 0 (θ.cob G G) x
          = eval (Arch.attentionMlp sees σ (rmsNorm ε) H dh hid) 0 θ x)
      ↔ ∀ ℓ, (G ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ := by
  sorry

/-! ### Attention blocks and gated blocks -/

/-- **Lemma A.4 for networks of attention blocks and gated blocks, in any order:** the gate is
not identically zero and satisfies `σ(z) = κ σ(κ z)` for all `z` only for `κ = 1`; every token
sees some token; every block has a head of width at least `1` or a hidden unit. If the changes of
basis `G_0, …, G_L` preserve the function of the skipless pre-RMSNorm network (`ε > 0`) for all
values of the parameters, every `G_ℓ` is orthogonal. -/
theorem orthogonal_of_eval_cob_skipless_rmsNorm_attentionGated [Nonempty T] [Nonempty dIn]
    [Nonempty dOut] (hε : 0 < ε) (hσ0 : ∃ z, σ z ≠ 0)
    (hκ : ∀ κ : ℝ, (∀ z, σ z = κ * σ (κ * z)) → κ = 1) (hsees : ∀ t, ∃ s, sees t s)
    (hblk : ∀ ℓ, (Nonempty (H ℓ) ∧ Nonempty (dh ℓ)) ∨ Nonempty (hid ℓ))
    (G : Fin (L + 1) → GL d ℝ)
    (h : ∀ (θ : Params
        (Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut)
      (x : Matrix T dIn ℝ),
      eval (Arch.attentionGated sees σ (rmsNorm ε) H dh hid) 0 (θ.cob G G) x
        = eval (Arch.attentionGated sees σ (rmsNorm ε) H dh hid) 0 θ x) :
    ∀ ℓ, (G ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ := by
  sorry

/-- **Theorem 3.3 (ii), skipless, pre-RMSNorm (`ε > 0`), attention blocks and gated blocks:**
the changes of basis `G_0, …, G_L` preserve the function for all values of the parameters if and
only if every `G_ℓ` is orthogonal. -/
theorem eval_cob_skipless_rmsNorm_iff_attentionGated [Nonempty T] [Nonempty dIn]
    [Nonempty dOut] (hε : 0 < ε) (hσ0 : ∃ z, σ z ≠ 0)
    (hκ : ∀ κ : ℝ, (∀ z, σ z = κ * σ (κ * z)) → κ = 1) (hsees : ∀ t, ∃ s, sees t s)
    (hblk : ∀ ℓ, (Nonempty (H ℓ) ∧ Nonempty (dh ℓ)) ∨ Nonempty (hid ℓ))
    (G : Fin (L + 1) → GL d ℝ) :
    (∀ (θ : Params
          (Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut)
        (x : Matrix T dIn ℝ),
        eval (Arch.attentionGated sees σ (rmsNorm ε) H dh hid) 0 (θ.cob G G) x
          = eval (Arch.attentionGated sees σ (rmsNorm ε) H dh hid) 0 θ x)
      ↔ ∀ ℓ, (G ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ := by
  sorry

end Skips
