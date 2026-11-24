import SkipsLean.Dimension.UpperBound

/-!
# The network after a hidden state, the claim `(D_k)`, and how it gives the rank

Paper (dimension paper): Appendix D, "The claim, and the reduction to one step", in the case (n)
(no normalization) and for blocks without symmetries inside (`tanh`, GELU).

For `k = 0, …, L` and a hidden state `h`, `𝓑_{>k}(h)` is the output of the network when its hidden
state `h_k` is set to `h`:

  `𝓑_{>L}(h) = χ(h) D`,   `𝓑_{>k-1}(h) = 𝓑_{>k}(g_k(χ(h)))`,   so that `F_θ(x) = 𝓑_{>0}(x E)`.

It depends on the weights of the blocks `k+1, …, L` and on `D`. For a `d × d` matrix `Z` and a
direction `η` of the parameters, the identity (18) of the paper is

  `𝐃𝓑_{>k}(h) (h Z) + 𝐃_θ 𝓑_{>k}(h) η = 0`   for all `h`,

with `𝐃` the derivative in `h` and `𝐃_θ` the derivative in the weights. Claim `(D_k)` says that
every `Z` and `η` that satisfy it come from changes of basis at the hidden states `h_k, …, h_L`:
there are matrices `Z_k = Z, Z_{k+1}, …, Z_L` with

  `η_read^ℓ = - Z_{ℓ-1} W_read^ℓ`,  `η_write^ℓ = W_write^ℓ Z_ℓ`  (`ℓ = k+1, …, L`),  `η_D = - Z_L D`.

Stated here: the definitions; Lemma D.2 (the derivative of `𝓑_{>k}` is injective on an open dense
set), Lemma D.3 (a direction at a write), Proposition D.4 (the claim `(D_0)` gives the functional
dimension `P - (L + 1) d²`) and Lemma D.5 (`(D_L)` holds), all in the case (n). The paper takes
inputs of one token, since an MLP block acts on each token separately; here a hidden state has the
rows `T`, as everywhere in this library, and the paper's rows are the case of one token.

The entries of `η` at `E` and at the blocks before `k+1` play no role in the identity and are not
constrained by the claim.
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise Topology

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable (A : Arch T d L)

/-- `𝓑_{>k}(h)`: the output of the network when its hidden state `h_k` is set to `h`. (With stream
matrices `S`, as `hidden` and `eval`; the paper's networks are `S = 0`.) -/
def suffix (S : Fin L → Matrix d d ℝ) (θ : Params A dIn dOut) :
    Fin (L + 1) → Matrix T d ℝ → Matrix T dOut ℝ :=
  Fin.reverseInduction (motive := fun _ => Matrix T d ℝ → Matrix T dOut ℝ)
    (fun h => A.χ h * θ.D)
    (fun ℓ B h => B (h * S ℓ + A.f ℓ (A.χ h * θ.read ℓ) * θ.write ℓ))

variable (S : Fin L → Matrix d d ℝ) (θ : Params A dIn dOut)

/-- `𝓑_{>L}(h) = χ(h) D`. -/
theorem suffix_last (h : Matrix T d ℝ) : suffix A S θ (Fin.last L) h = A.χ h * θ.D := by
  sorry

/-- `𝓑_{>k-1}(h) = 𝓑_{>k}(g_k(χ(h)))` (plus the stream term `h S_k`). -/
theorem suffix_castSucc (ℓ : Fin L) (h : Matrix T d ℝ) :
    suffix A S θ ℓ.castSucc h
      = suffix A S θ ℓ.succ (h * S ℓ + A.f ℓ (A.χ h * θ.read ℓ) * θ.write ℓ) := by
  sorry

/-- The network after `h_k`, at the hidden state `h_k` of the input `x`, is the output at `x`. -/
theorem suffix_hidden (x : Matrix T dIn ℝ) (k : Fin (L + 1)) :
    suffix A S θ k (hidden A S θ x k) = eval A S θ x := by
  sorry

/-- `F_θ(x) = 𝓑_{>0}(x E)`. -/
theorem eval_eq_suffix_zero (x : Matrix T dIn ℝ) :
    eval A S θ x = suffix A S θ 0 (x * θ.E) := by
  sorry

/-- The identity (18) of the paper for `k`, `Z` and `η`, in a network without skips:
`𝐃𝓑_{>k}(h) (h Z) + 𝐃_θ 𝓑_{>k}(h) η = 0` for all `h`. -/
def SuffixFlat (k : Fin (L + 1)) (Z : Matrix d d ℝ) (η : Params A dIn dOut) : Prop :=
  ∀ h : Matrix T d ℝ,
    fderiv ℝ (fun h' : Matrix T d ℝ => suffix A 0 θ k h') h (h * Z)
      + fderiv ℝ (fun θ' : Params A dIn dOut => suffix A 0 θ' k h) θ η = 0

/-- **Claim `(D_k)`,** in the case (n), for blocks without symmetries inside: every `Z` and `η`
that satisfy the identity (18) for `k` come from changes of basis `Z_k = Z, Z_{k+1}, …, Z_L` at the
hidden states `h_k, …, h_L`. -/
def Claim (k : Fin (L + 1)) : Prop :=
  ∀ (Z : Matrix d d ℝ) (η : Params A dIn dOut), SuffixFlat A θ k Z η →
    ∃ X : Fin (L + 1) → Matrix d d ℝ, X k = Z ∧
      (∀ ℓ : Fin L, k ≤ ℓ.castSucc →
        η.read ℓ = -(X ℓ.castSucc * θ.read ℓ) ∧ η.write ℓ = θ.write ℓ * X ℓ.succ) ∧
      η.D = -(X (Fin.last L) * θ.D)

/-- "`θ` is regular", in the case (n): (R1) `E`, `D` and every write have rank `d`; (R3) the
derivative of every block `g_ℓ(n) = f_ℓ(n W_read^ℓ) W_write^ℓ` is invertible at some `n`. -/
structure Regular : Prop where
  rank_E : θ.E.rank = Fintype.card d
  rank_D : θ.D.rank = Fintype.card d
  rank_write : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d
  deriv_block : ∀ ℓ, ∃ n : Matrix T d ℝ, Function.Injective
    (fderiv ℝ (fun n' : Matrix T d ℝ => A.f ℓ (n' * θ.read ℓ) * θ.write ℓ) n)

/-- **Lemma D.5, case (n):** `(D_L)` holds. -/
theorem claim_last [Nonempty T] (hχ : A.χ = id) : Claim A θ (Fin.last L) := by
  sorry

/-- **Lemma D.2, case (n):** for a regular `θ` and analytic blocks there is, for every `k`, an open
dense set of hidden states `h` at which the derivative of `𝓑_{>k}` is injective. -/
theorem exists_open_dense_injective_fderiv_suffix (hχ : A.χ = id)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (hθ : Regular A θ) (k : Fin (L + 1)) :
    ∃ U : Set (Matrix T d ℝ), IsOpen U ∧ Dense U ∧
      ∀ h ∈ U, Function.Injective (fderiv ℝ (fun h' : Matrix T d ℝ => suffix A 0 θ k h') h) := by
  sorry

/-- **Lemma D.3, case (n) (a direction at a write).** Let `θ` be regular, and let `M` be a matrix
with `d` columns and rank `d`. If `𝐃𝓑_{>k}(w M) (w η_M) + 𝐃_θ 𝓑_{>k}(w M) η = 0` for all `w`, then
`η_M = M Z` for a `d × d` matrix `Z`, and the identity (18) holds for `k`, `Z` and `η`. -/
theorem suffixFlat_of_flat_at_write (hχ : A.χ = id)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (hθ : Regular A θ) (k : Fin (L + 1))
    {m : Type*} [Fintype m] (M : Matrix m d ℝ) (hM : M.rank = Fintype.card d)
    (ηM : Matrix m d ℝ) (η : Params A dIn dOut)
    (h : ∀ w : Matrix T m ℝ,
      fderiv ℝ (fun h' : Matrix T d ℝ => suffix A 0 θ k h') (w * M) (w * ηM)
        + fderiv ℝ (fun θ' : Params A dIn dOut => suffix A 0 θ' k (w * M)) θ η = 0) :
    ∃ Z : Matrix d d ℝ, ηM = M * Z ∧ SuffixFlat A θ k Z η := by
  sorry

/-- **Proposition D.4, case (n), first part:** if `θ` is regular and `(D_0)` holds at `θ`, every
flat direction is the direction of changes of basis at the hidden states. -/
theorem flat_le_range_cobDir_of_claim (hχ : A.χ = id)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (hθ : Regular A θ) (h0 : Claim A θ 0)
    (η : Params A dIn dOut) (hη : η ∈ flat A 0 θ) :
    ∃ X : Fin (L + 1) → Matrix d d ℝ, η = cobDir θ X := by
  sorry

/-- **Proposition D.4, case (n):** if `θ` is regular and `(D_0)` holds at `θ`, the functional
dimension at `θ` is `P - (L + 1) d²`. -/
theorem funDim_of_claim (hχ : A.χ = id)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (hθ : Regular A θ) (h0 : Claim A θ 0) :
    funDim A 0 θ + (L + 1) * Fintype.card d ^ 2
      = Module.finrank ℝ (Params A dIn dOut) := by
  sorry

end Skips
