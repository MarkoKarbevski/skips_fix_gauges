import SkipsLean.Residual.LearnedSkipsConformal
import SkipsLean.Basic.RMSNormConverse

/-!
# Orthogonal skips can be absorbed: the converse

Paper (skips paper), Theorem A.12 (ii): "Conversely, let the reads and the readout have rank
`d_model`, and let invertible `G_0, …, G_L` turn every skip into the identity,
`G_{ℓ−1}⁻¹ A_ℓ G_ℓ = I`. If the network, written in the variables `h_ℓ G_ℓ`, is a pre-RMSNorm
residual network, then every `Π_ℓ` lies in `G`."

Its proof: "Conversely, `G_{ℓ−1}⁻¹ A_ℓ G_ℓ = I` for every `ℓ` gives `G_ℓ = Π_ℓ⁻¹ G_0`, so in the
variables `h′_ℓ = h_ℓ G_ℓ` block `ℓ` reads `N_ε(h′_{ℓ−1} G_0⁻¹ Π_{ℓ−1}) W_read^ℓ`, and the readout
reads `N_ε(h′_L G_0⁻¹ Π_L)`. In a pre-RMSNorm residual network every read has the form
`N_ε(h′) W`; as the reads and the readout have rank `d_model`, this gives matrices `M_ℓ` with
`N_ε(h′ G_0⁻¹ Π_ℓ) = N_ε(h′) M_ℓ` for all `h′`, and Lemma A.2 puts every `G_0⁻¹ Π_ℓ` in `G`. For
`ℓ = 0` this puts `G_0` in `G`, and so every `Π_ℓ` lies in `G`."

Here, with the forward products `Π_ℓ = A_1 ⋯ A_ℓ` (`skipProdFwd`,
`Residual/LearnedSkipsConformal.lean`). In the variables `h′_ℓ = h_ℓ G_ℓ` the skips are the
identity, block `ℓ` reads `N_ε(h′_{ℓ−1} G_{ℓ−1}⁻¹) W_read^ℓ` and the readout reads
`N_ε(h′_L G_L⁻¹) D`. "The network, written in the variables `h_ℓ G_ℓ`, is a pre-RMSNorm residual
network" is stated as the proof uses it: every read and the readout have the form `N_ε(h′) W′`,
that is, there are matrices `W′_ℓ` and `D′` with
`N_ε(h G_{ℓ−1}⁻¹) W_read^ℓ = N_ε(h) W′_ℓ` and `N_ε(h G_L⁻¹) D = N_ε(h) D′` for every hidden state
`h`. The conclusion for `ε = 0`: every `Π_ℓ` is a positive multiple of an orthogonal matrix
(`G = CO(d)`); for `ε > 0`: every `Π_ℓ` is orthogonal (`G = O(d)`). There is at least one token.
-/

namespace Skips

open Matrix

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d]
  [Fintype dIn] [Fintype dOut]
variable {A : Arch T d L}

/-- A matrix with `d` rows and rank `d` has a right inverse. -/
private theorem exists_right_inverse_lsv {n : Type*} [Fintype n] (W : Matrix d n ℝ)
    (hW : W.rank = Fintype.card d) : ∃ R : Matrix n d ℝ, W * R = 1 :=
  Matrix.mulVec_surjective_iff_exists_right_inverse.mp
    (Matrix.mulVec_surjective_iff_rank_eq_card.mpr hW)

omit [Fintype T] in
/-- If `N_ε(h X) W = N_ε(h) W'` for every hidden state `h` and `W` has rank `d`, there is a
matrix `M` with `N_ε(v X) = N_ε(v) M` for every row `v` (take the state with all rows `v`). -/
private theorem rows_of_rmsNorm_lsv {n : Type*} [Fintype n] {ε : ℝ} (X : Matrix d d ℝ)
    (W W' : Matrix d n ℝ) (hW : W.rank = Fintype.card d)
    (h : ∀ h : Matrix T d ℝ, rmsNorm ε (h * X) * W = rmsNorm ε h * W') :
    ∃ M : Matrix d d ℝ, ∀ v : d → ℝ, rmsRow ε (v ᵥ* X) = rmsRow ε v ᵥ* M := by
  obtain ⟨R, hR⟩ := exists_right_inverse_lsv W hW
  refine ⟨W' * R, fun v => ?_⟩
  obtain ⟨t⟩ := (inferInstance : Nonempty T)
  -- the hidden state with every row `v`, multiplied on the right by `R`
  have e := congrArg (fun Y => (Y * R) t) (h (Matrix.of fun _ => v))
  simp only [Matrix.mul_assoc, hR, Matrix.mul_one] at e
  -- row `t` of `N_ε(Y)` is `N_ε(Y t)`, and row `t` of `Y X` is `Y t ᵥ* X`
  have hrow : ∀ Y : Matrix T d ℝ, rmsNorm ε Y t = rmsRow ε (Y t) := fun _ => rfl
  rw [Matrix.mul_apply_eq_vecMul, hrow, hrow, Matrix.mul_apply_eq_vecMul] at e
  exact e

/-- The inverse of an orthogonal matrix is orthogonal (it is its transpose). -/
private theorem inv_mem_orthogonalGroup_lsv (P : GL d ℝ)
    (hP : (P : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ) :
    (↑P⁻¹ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ := by
  rw [Matrix.mem_orthogonalGroup_iff, coe_inv_of_mem_orthogonalGroup P hP,
    Matrix.transpose_transpose]
  exact (Matrix.mem_orthogonalGroup_iff' d ℝ).mp hP

/-- `G_ℓ⁻¹ A_ℓ G_ℓ' = I` for every block gives `G_ℓ = Π_ℓ⁻¹ G_0`, that is, `Π_ℓ = G_0 G_ℓ⁻¹`. -/
private theorem skipProdFwd_eq_lsv (S : Fin L → GL d ℝ) (G : Fin (L + 1) → GL d ℝ)
    (hG : ∀ ℓ : Fin L, (G ℓ.castSucc)⁻¹ * S ℓ * G ℓ.succ = 1) (ℓ : Fin (L + 1)) :
    skipProdFwd S ℓ = G 0 * (G ℓ)⁻¹ := by
  -- first `G_ℓ = Π_ℓ⁻¹ G_0`, by induction on `ℓ`
  have key : ∀ ℓ : Fin (L + 1), G ℓ = (skipProdFwd S ℓ)⁻¹ * G 0 := by
    intro ℓ
    induction ℓ using Fin.induction with
    | zero => rw [skipProdFwd_zero, inv_one, one_mul]
    | succ i ih =>
      -- `G_{i+1} = (G_i⁻¹ A_i)⁻¹ = A_i⁻¹ Π_i⁻¹ G_0 = Π_{i+1}⁻¹ G_0`
      rw [eq_inv_of_mul_eq_one_right (hG i), ih, skipProdFwd_succ]
      group
  rw [key ℓ]
  group

omit [Fintype T] [Fintype dIn] in
/-- For every `j` there is a matrix `M_j` with `N_ε(v G_j⁻¹) = N_ε(v) M_j` for every row `v`:
from the read of block `j + 1`, or from the readout for `j = L`. -/
private theorem exists_rows_lsv {ε : ℝ} (θ : Params A dIn dOut) (G : Fin (L + 1) → GL d ℝ)
    (hread : ∀ ℓ : Fin L, (θ.read ℓ).rank = Fintype.card d) (hD : θ.D.rank = Fintype.card d)
    (hres : ∀ ℓ : Fin L, ∃ W' : Matrix d (A.r ℓ) ℝ, ∀ h : Matrix T d ℝ,
      rmsNorm ε (h * (↑(G ℓ.castSucc)⁻¹ : Matrix d d ℝ)) * θ.read ℓ = rmsNorm ε h * W')
    (hresD : ∃ D' : Matrix d dOut ℝ, ∀ h : Matrix T d ℝ,
      rmsNorm ε (h * (↑(G (Fin.last L))⁻¹ : Matrix d d ℝ)) * θ.D = rmsNorm ε h * D')
    (j : Fin (L + 1)) :
    ∃ M : Matrix d d ℝ, ∀ v : d → ℝ,
      rmsRow ε (v ᵥ* (↑(G j)⁻¹ : Matrix d d ℝ)) = rmsRow ε v ᵥ* M := by
  induction j using Fin.lastCases with
  | last =>
    -- the readout
    obtain ⟨D', hD'⟩ := hresD
    exact rows_of_rmsNorm_lsv _ _ D' hD hD'
  | cast ℓ =>
    -- the read of block `ℓ + 1`
    obtain ⟨W', hW'⟩ := hres ℓ
    exact rows_of_rmsNorm_lsv _ _ W' (hread ℓ) hW'

omit [Fintype T] [Fintype dIn] in
/-- **Theorem A.12 (ii) of the skips paper, "Conversely", for `ε = 0`:** let the reads and the
readout have rank `d`, and let invertible `G_0, …, G_L` turn every skip into the identity,
`G_{ℓ−1}⁻¹ A_ℓ G_ℓ = I`. If in the variables `h_ℓ G_ℓ` every read and the readout have the form
`N_0(h′) W′`, then every `Π_ℓ = A_1 ⋯ A_ℓ` is a positive multiple of an orthogonal matrix. -/
theorem skipProdFwd_conformal_of_residual_rmsNorm_zero (θ : Params A dIn dOut)
    (S : Fin L → GL d ℝ) (G : Fin (L + 1) → GL d ℝ)
    (hG : ∀ ℓ : Fin L, (G ℓ.castSucc)⁻¹ * S ℓ * G ℓ.succ = 1)
    (hread : ∀ ℓ : Fin L, (θ.read ℓ).rank = Fintype.card d) (hD : θ.D.rank = Fintype.card d)
    (hres : ∀ ℓ : Fin L, ∃ W' : Matrix d (A.r ℓ) ℝ, ∀ h : Matrix T d ℝ,
      rmsNorm 0 (h * (↑(G ℓ.castSucc)⁻¹ : Matrix d d ℝ)) * θ.read ℓ = rmsNorm 0 h * W')
    (hresD : ∃ D' : Matrix d dOut ℝ, ∀ h : Matrix T d ℝ,
      rmsNorm 0 (h * (↑(G (Fin.last L))⁻¹ : Matrix d d ℝ)) * θ.D = rmsNorm 0 h * D') :
    ∀ ℓ, ∃ (c : ℝ) (P : Matrix d d ℝ), 0 < c ∧ P ∈ Matrix.orthogonalGroup d ℝ ∧
      (skipProdFwd S ℓ : Matrix d d ℝ) = c • P := by
  -- Lemma A.2 for `ε = 0`: every `G_j⁻¹ = c_j M_j` with `c_j > 0` and `M_j` orthogonal
  have hconf : ∀ j, ∃ (c : ℝ) (M : Matrix d d ℝ), 0 < c ∧ M ∈ Matrix.orthogonalGroup d ℝ ∧
      (↑(G j)⁻¹ : Matrix d d ℝ) = c • M := by
    intro j
    obtain ⟨M, hM⟩ := exists_rows_lsv θ G hread hD hres hresD j
    obtain ⟨hMo, c, hc, hGM⟩ := conformal_of_rmsRow_zero_vecMul (G j)⁻¹ M fun v _ => hM v
    exact ⟨c, M, hc, hMo, hGM⟩
  intro ℓ
  obtain ⟨c₀, M₀, hc₀, hM₀, h₀⟩ := hconf 0
  obtain ⟨c, M, hc, hM, hℓ⟩ := hconf ℓ
  -- `G_0 = c_0⁻¹ M_0ᵀ`, the inverse of `c_0 M_0`
  have hG₀ : (G 0 : Matrix d d ℝ) = c₀⁻¹ • M₀ᵀ := by
    have e : (↑(G 0)⁻¹ : Matrix d d ℝ) * (c₀⁻¹ • M₀ᵀ) = 1 := by
      rw [h₀, Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hc₀.ne', one_smul,
        (Matrix.mem_orthogonalGroup_iff d ℝ).mp hM₀]
    calc (G 0 : Matrix d d ℝ) = G 0 * ((↑(G 0)⁻¹ : Matrix d d ℝ) * (c₀⁻¹ • M₀ᵀ)) := by
          rw [e, Matrix.mul_one]
      _ = c₀⁻¹ • M₀ᵀ := by rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
  -- `Π_ℓ = G_0 G_ℓ⁻¹ = (c_0⁻¹ c_ℓ) (M_0ᵀ M_ℓ)`
  have hM₀t : M₀ᵀ ∈ Matrix.orthogonalGroup d ℝ := by
    rw [Matrix.mem_orthogonalGroup_iff, Matrix.transpose_transpose]
    exact (Matrix.mem_orthogonalGroup_iff' d ℝ).mp hM₀
  refine ⟨c₀⁻¹ * c, M₀ᵀ * M, mul_pos (inv_pos.mpr hc₀) hc, mul_mem hM₀t hM, ?_⟩
  rw [skipProdFwd_eq_lsv S G hG ℓ, Units.val_mul, hG₀, hℓ, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul]

omit [Fintype T] [Fintype dIn] in
/-- **Theorem A.12 (ii) of the skips paper, "Conversely", for `ε > 0`:** let the reads and the
readout have rank `d`, and let invertible `G_0, …, G_L` turn every skip into the identity,
`G_{ℓ−1}⁻¹ A_ℓ G_ℓ = I`. If in the variables `h_ℓ G_ℓ` every read and the readout have the form
`N_ε(h′) W′`, then every `Π_ℓ = A_1 ⋯ A_ℓ` is orthogonal. -/
theorem skipProdFwd_orthogonal_of_residual_rmsNorm {ε : ℝ} (hε : 0 < ε) (θ : Params A dIn dOut)
    (S : Fin L → GL d ℝ) (G : Fin (L + 1) → GL d ℝ)
    (hG : ∀ ℓ : Fin L, (G ℓ.castSucc)⁻¹ * S ℓ * G ℓ.succ = 1)
    (hread : ∀ ℓ : Fin L, (θ.read ℓ).rank = Fintype.card d) (hD : θ.D.rank = Fintype.card d)
    (hres : ∀ ℓ : Fin L, ∃ W' : Matrix d (A.r ℓ) ℝ, ∀ h : Matrix T d ℝ,
      rmsNorm ε (h * (↑(G ℓ.castSucc)⁻¹ : Matrix d d ℝ)) * θ.read ℓ = rmsNorm ε h * W')
    (hresD : ∃ D' : Matrix d dOut ℝ, ∀ h : Matrix T d ℝ,
      rmsNorm ε (h * (↑(G (Fin.last L))⁻¹ : Matrix d d ℝ)) * θ.D = rmsNorm ε h * D') :
    ∀ ℓ, (skipProdFwd S ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ := by
  -- Lemma A.2 for `ε > 0`: every `G_j⁻¹` is orthogonal
  have horth : ∀ j, (↑(G j)⁻¹ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ := by
    intro j
    obtain ⟨M, hM⟩ := exists_rows_lsv θ G hread hD hres hresD j
    exact (orthogonal_of_rmsRow_vecMul hε (G j)⁻¹ M fun v _ => hM v).1
  intro ℓ
  -- `G_0 = (G_0⁻¹)⁻¹` is orthogonal, and `Π_ℓ = G_0 G_ℓ⁻¹`
  have hG₀ : (G 0 : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ := by
    have h := inv_mem_orthogonalGroup_lsv _ (horth 0)
    rwa [inv_inv] at h
  rw [skipProdFwd_eq_lsv S G hG ℓ, Units.val_mul]
  exact mul_mem hG₀ (horth ℓ)

end Skips
