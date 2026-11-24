import SkipsLean.Depth.Cones
import SkipsLean.Depth.BlockIdentityGated

/-!
# The frozen network

Paper (dimension): Appendix D.5, "The frozen network". "In the case (n), for gated blocks and a
good `θ`, let `𝓑°_{>k}` be the network after `h_k` with the gates of all its blocks frozen:

  `𝓑°_{>L}(h) = h D`,   `𝓑°_{>k−1}(h) = 𝓑°_{>k}(g°_k(h))`.

It is a polynomial map of `h` and of the weights. Lemmas D.2 and D.3 hold for `𝓑°_{>k}` in the
place of `𝓑_{>k}`, with an open dense set `U°_k` of rows and with the same proofs, in which
`g°_{k+1}` takes the place of `g_{k+1}`." Here `g°_ℓ(n) = ∑_{j ∈ A_ℓ} (n c_j) ι_j(n) a_j` is the
block with its gates frozen, a quadratic map for a gated block: `g°_ℓ(λ n) = λ² g°_ℓ(n)`.

In Lean the frozen network is the network of an architecture of its own, `Arch.frozen A`, whose
block `ℓ` sends the gate `z_i` and the value `w_i` of a hidden unit to `z_i w_i` if `i ∈ A ℓ` and to
`0` otherwise; then `𝓑°_{>k}` is `suffix (Arch.frozen A) 0 θ k`, and Lemmas D.2 and D.3 for it are
the statements of `Depth/Suffix.lean` for this architecture, at a regular parameter. The weights of
a gated network are weights of the frozen network with the same matrices (`Params.toFrozen`).

Stated here: these definitions; that the frozen block is `frozenGated` on every row; that a good
`θ` is regular for the frozen network; that the frozen network is homogeneous,
`𝓑°_{>k}(c h) = c^{2^{L−k}} 𝓑°_{>k}(h)`, and what this gives for its derivatives and for the left
side of the identity for one block. The left side is written for the outputs `v` of the hidden
units and their derivative `vdot` (`writeLHS`, for any architecture): for a gated block it is the
`𝓛` of equation (27) with `v = ŵ = w̃ ⊙ ι` and `vdot = w̃' ⊙ ż^g ⊙ ι + w̃ ⊙ ż^v`.
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise Topology

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]
variable {σ : ℝ → ℝ} {χ : Matrix T d ℝ → Matrix T d ℝ}

/-- **The network of gated blocks with its gates frozen** on the active sets `A`, without
normalization: the fixed map of block `ℓ` sends the gate `z_i` and the value `w_i` of a hidden unit
to `z_i w_i` if `i ∈ A ℓ`, and to `0` otherwise. The read is `[W_g | W_v]` as for `Arch.gated`. -/
noncomputable abbrev Arch.frozen (A : ∀ ℓ, Finset (hid ℓ)) : Arch T d L where
  r ℓ := hid ℓ ⊕ hid ℓ
  w := hid
  f ℓ M := Matrix.of fun t =>
    Set.indicator (↑(A ℓ) : Set (hid ℓ)) fun i => M t (Sum.inl i) * M t (Sum.inr i)
  χ := id

/-- The weights of a network of gated blocks, as weights of the frozen network: the same
matrices. -/
def Params.toFrozen (A : ∀ ℓ, Finset (hid ℓ))
    (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut) :
    Params (Arch.frozen (T := T) (d := d) A) dIn dOut where
  E := θ.E
  read := θ.read
  write := θ.write
  D := θ.D

/-- **The left side of the identity for one block, in the outputs of its hidden units:**
`𝐃𝓑(v V) (vdot V + v η_V) + 𝐃_θ 𝓑(v V) η`, for block `k` with the write `V` and the network `𝓑`
after it. Here `v` stands for the outputs of the hidden units and `vdot` for their derivative. -/
noncomputable def writeLHS (A : Arch T d L) (θ : Params A dIn dOut) (k : Fin L)
    (η : Params A dIn dOut) (v vdot : Matrix T (A.w k) ℝ) : Matrix T dOut ℝ :=
  fderiv ℝ (fun h' : Matrix T d ℝ => suffix A 0 θ k.succ h') (v * θ.write k)
      (vdot * θ.write k + v * η.write k)
    + fderiv ℝ (fun θ' : Params A dIn dOut => suffix A 0 θ' k.succ (v * θ.write k)) θ η

/-- For a gated block, `𝓛(w̃, w̃'; n)` of equation (27) is `writeLHS` at `v = w̃ ⊙ ι` and
`vdot = w̃' ⊙ ż^g ⊙ ι + w̃ ⊙ ż^v`. -/
theorem blockLHSGated_eq_writeLHS (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut)
    (k : Fin L) (η : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut)
    (w w' : Matrix T (hid k) ℝ) (z zdot : Matrix T (hid k ⊕ hid k) ℝ) :
    blockLHSGated θ k η w w' z zdot
      = writeLHS (Arch.gated σ χ hid) θ k η (Matrix.of fun t j => w t j * z t (Sum.inr j))
          (Matrix.of fun t j =>
            w' t j * zdot t (Sum.inl j) * z t (Sum.inr j) + w t j * zdot t (Sum.inr j)) :=
  rfl

/-- The frozen block, on every row, is `g°_ℓ` (`frozenGated`). -/
theorem frozen_block_apply (A : ∀ ℓ, Finset (hid ℓ))
    (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut) (ℓ : Fin L) (n : Matrix T d ℝ)
    (t : T) :
    ((Arch.frozen (T := T) (d := d) A).f ℓ (n * θ.read ℓ) * θ.write ℓ) t
      = frozenGated θ ℓ (A ℓ) (n t) := by
  sorry

/-- The fixed maps of the frozen network are real-analytic (they are polynomial). -/
theorem analyticOnNhd_f_frozen (A : ∀ ℓ, Finset (hid ℓ)) (ℓ : Fin L) :
    AnalyticOnNhd ℝ ((Arch.frozen (T := T) (d := d) A).f ℓ) Set.univ := by
  sorry

/-- **A good `θ` is regular for the frozen network:** (R1), and by (K2) the derivative of every
frozen block is invertible at some hidden state. So Lemmas D.2 and D.3 hold for the frozen
network. -/
theorem regular_frozen_of_goodForConesGated {C : Fin (L + 1) → Set (d → ℝ)}
    {A : ∀ ℓ, Finset (hid ℓ)} {θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut}
    (hθ : GoodForConesGated C A θ) :
    Regular (Arch.frozen (T := T) (d := d) A) (θ.toFrozen A) := by
  sorry

/-- **The frozen network is homogeneous:** `𝓑°_{>k}(c h) = c^{2^{L−k}} 𝓑°_{>k}(h)`. -/
theorem suffix_frozen_smul (A : ∀ ℓ, Finset (hid ℓ))
    (θ : Params (Arch.frozen (T := T) (d := d) A) dIn dOut) (k : Fin (L + 1)) (c : ℝ)
    (h : Matrix T d ℝ) :
    suffix (Arch.frozen A) 0 θ k (c • h)
      = c ^ (2 ^ (L - (k : ℕ))) • suffix (Arch.frozen A) 0 θ k h := by
  sorry

/-- The derivative of the frozen network in the hidden state is homogeneous of the degree
`2^{L−k} − 1`. -/
theorem fderiv_suffix_frozen_smul (A : ∀ ℓ, Finset (hid ℓ))
    (θ : Params (Arch.frozen (T := T) (d := d) A) dIn dOut) (k : Fin (L + 1)) {c : ℝ}
    (hc : c ≠ 0) (h v : Matrix T d ℝ) :
    fderiv ℝ (fun h' : Matrix T d ℝ => suffix (Arch.frozen A) 0 θ k h') (c • h) v
      = c ^ (2 ^ (L - (k : ℕ)) - 1)
        • fderiv ℝ (fun h' : Matrix T d ℝ => suffix (Arch.frozen A) 0 θ k h') h v := by
  sorry

/-- The derivative of the frozen network in the weights is homogeneous of the degree `2^{L−k}` in
the hidden state. -/
theorem fderiv_params_suffix_frozen_smul (A : ∀ ℓ, Finset (hid ℓ))
    (θ η : Params (Arch.frozen (T := T) (d := d) A) dIn dOut) (k : Fin (L + 1)) (c : ℝ)
    (h : Matrix T d ℝ) :
    fderiv ℝ (fun θ' : Params (Arch.frozen (T := T) (d := d) A) dIn dOut =>
        suffix (Arch.frozen A) 0 θ' k (c • h)) θ η
      = c ^ (2 ^ (L - (k : ℕ)))
        • fderiv ℝ (fun θ' : Params (Arch.frozen (T := T) (d := d) A) dIn dOut =>
            suffix (Arch.frozen A) 0 θ' k h) θ η := by
  sorry

/-- The left side of the identity for one block of the frozen network is homogeneous of the degree
`2^{L−k−1}` in the outputs of the hidden units and their derivative together. -/
theorem writeLHS_frozen_smul (A : ∀ ℓ, Finset (hid ℓ))
    (θ η : Params (Arch.frozen (T := T) (d := d) A) dIn dOut) (k : Fin L) {c : ℝ} (hc : c ≠ 0)
    (v vdot : Matrix T (hid k) ℝ) :
    writeLHS (Arch.frozen A) θ k η (c • v) (c • vdot)
      = c ^ (2 ^ (L - (k : ℕ) - 1)) • writeLHS (Arch.frozen A) θ k η v vdot := by
  sorry

end Skips
