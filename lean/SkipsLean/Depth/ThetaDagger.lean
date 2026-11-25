import SkipsLean.Depth.Cones

/-!
# The parameters `θ†` of Lemma D.13, written out

Paper (dimension paper), Appendix D.5: "The parameters `θ†`. Let `𝟙` be the column of `d_model`
ones. Choose numbers `μ_1, μ_2, … > 0` such that `1, μ_1, μ_2, …` are linearly independent over
`ℚ`, for SwiGLU blocks, or such that `μ_1², μ_2², …` are, for GELU and GeGLU blocks. […] So the
gate column `c_j` is column `j` of `I` for `j ≤ d_model` and `c_j = −μ_{j−d_model} 𝟙` for
`j > d_model`, the write row `a_j` is row `j` of `I` for `j ≤ d_model` and `a_j = 𝟙^⊤` for
`j > d_model`, and in a gated block every value column is `e_j = 𝟙`. Let `ℝ^{1×d_model}_{>0}` be
the positive orthant, the set of the rows `n` with `n_i > 0` for every `i`."

"Lemma D.13 (`θ†` is good). `θ†` is good for the cones `C_0 = ⋯ = C_L = ℝ^{1×d_model}_{>0}`. For
every block, `A_ℓ = {1, …, d_model}`, and `g°_ℓ(n) = n` for a GELU block and `g°_ℓ(n) = (n𝟙) n`
for a gated block, where `n𝟙 = n_1 + ⋯ + n_{d_model}`."

`Depth/Cones.lean` has the lemma as an existence statement (there are cones, active sets and a
good parameter with the independence over `ℚ` of (K3)); its `θ†` is private there. Here `θ†` is a
definition and the lemma is stated with it:

* `posOrthant`: the positive orthant.
* `thetaDaggerGated`, `thetaDaggerMlp`: `θ†`. The index types are arbitrary finite types, so "the
  first `d_model` coordinates" of the inputs, of the outputs and of the hidden units of block `ℓ`
  are given by embeddings `ιE : d ↪ d_in`, `ιD : d ↪ d_out`, `c ℓ : d ↪ hid ℓ`; the number `μ ℓ j`
  is used for the units `j` outside the image of `c ℓ`.
* `exists_mu_thetaDaggerGated_cols` (SwiGLU), `exists_mu_thetaDaggerGated_outer` (GeGLU),
  `exists_mu_thetaDaggerMlp_outer` (GELU): there are numbers `μ > 0` for which `θ†` is good for
  the orthants with the active sets `A_ℓ` = the image of `c ℓ`, the frozen blocks are the paper's
  (`g°_ℓ(n) = (n𝟙) n`, respectively `n`), and the independence over `ℚ` of (K3) holds.
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {σ : ℝ → ℝ} {χ : Matrix T d ℝ → Matrix T d ℝ} {hid : Fin L → Type}
  [∀ ℓ, Fintype (hid ℓ)]

omit [Fintype d] [DecidableEq d] in
/-- The positive orthant `ℝ^{1×d}_{>0}`: the rows with all entries positive. -/
def posOrthant (d : Type*) : Set (d → ℝ) := Set.univ.pi fun _ => Set.Ioi 0

omit [Fintype d] [DecidableEq d] in
/-- A row is in the positive orthant if and only if all its entries are positive. -/
theorem mem_posOrthant {n : d → ℝ} : n ∈ posOrthant d ↔ ∀ i, 0 < n i := by
  simp [posOrthant, Set.mem_pi]

open Classical in
omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- **The parameters `θ†` of Lemma D.13 for gated blocks.** `E` and `D` are the `0/1` matrices of
the embeddings `ιE`, `ιD` (`E = [I; 0]`, `D = [I | 0]`). In block `ℓ`, the gate column of the unit
`c ℓ i` is the unit column `e_i`, and that of a unit `j` outside the image of `c ℓ` is `−μ_j 𝟙`;
every value column is `𝟙`; the write row of the unit `c ℓ i` is the unit row `e_i`, and that of a
unit outside the image of `c ℓ` is `𝟙^⊤`. -/
noncomputable def thetaDaggerGated (ιE : d ↪ dIn) (ιD : d ↪ dOut) (c : ∀ ℓ, d ↪ hid ℓ)
    (μ : ∀ ℓ, hid ℓ → ℝ) : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut where
  E := Matrix.of fun a i => if a = ιE i then 1 else 0
  read ℓ := Matrix.of fun k (s : hid ℓ ⊕ hid ℓ) =>
    Sum.elim (fun j => if j ∈ Set.range (c ℓ) then (if j = c ℓ k then 1 else 0) else -μ ℓ j)
      (fun _ => 1) s
  write ℓ := Matrix.of fun j k =>
    if j ∈ Set.range (c ℓ) then (if j = c ℓ k then 1 else 0) else 1
  D := Matrix.of fun i b => if b = ιD i then 1 else 0

open Classical in
omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- **The parameters `θ†` of Lemma D.13 for MLP blocks** (GELU blocks): as `thetaDaggerGated`,
without value columns. -/
noncomputable def thetaDaggerMlp (ιE : d ↪ dIn) (ιD : d ↪ dOut) (c : ∀ ℓ, d ↪ hid ℓ)
    (μ : ∀ ℓ, hid ℓ → ℝ) : Params (Arch.mlp (T := T) (d := d) σ χ hid) dIn dOut where
  E := Matrix.of fun a i => if a = ιE i then 1 else 0
  read ℓ := Matrix.of fun k (j : hid ℓ) =>
    if j ∈ Set.range (c ℓ) then (if j = c ℓ k then 1 else 0) else -μ ℓ j
  write ℓ := Matrix.of fun j k =>
    if j ∈ Set.range (c ℓ) then (if j = c ℓ k then 1 else 0) else 1
  D := Matrix.of fun i b => if b = ιD i then 1 else 0

/-- **Lemma D.13 of the dimension paper for SwiGLU blocks, with `θ†` written out:** for `d ≥ 1`
there are numbers `μ > 0` such that `θ†` is good for the cones `C_0 = ⋯ = C_L = ℝ^{1×d}_{>0}` with
the active sets `A_ℓ` = the image of `c ℓ` (the paper's `{1, …, d_model}`), the frozen blocks are
`g°_ℓ(n) = (n𝟙) n`, and the gate columns of every block are linearly independent over `ℚ`. -/
theorem exists_mu_thetaDaggerGated_cols [Nonempty d] (ιE : d ↪ dIn) (ιD : d ↪ dOut)
    (c : ∀ ℓ, d ↪ hid ℓ) :
    ∃ μ : ∀ ℓ, hid ℓ → ℝ, (∀ ℓ j, 0 < μ ℓ j) ∧
      GoodForConesGated (fun _ => posOrthant d) (fun ℓ => Finset.univ.map (c ℓ))
        (thetaDaggerGated (T := T) (σ := σ) (χ := χ) ιE ιD c μ) ∧
      (∀ ℓ (n : d → ℝ), frozenGated (thetaDaggerGated (T := T) (σ := σ) (χ := χ) ιE ιD c μ) ℓ
        (Finset.univ.map (c ℓ)) n = (∑ k, n k) • n) ∧
      ∀ ℓ, LinearIndependent ℚ (fun j : hid ℓ =>
        ((thetaDaggerGated (T := T) (σ := σ) (χ := χ) ιE ιD c μ).read ℓ)ᵀ (Sum.inl j)) := by
  sorry

/-- **Lemma D.13 of the dimension paper for GeGLU blocks, with `θ†` written out:** for `d ≥ 2`
there are numbers `μ > 0` such that `θ†` is good for the positive orthants with the active sets
`A_ℓ` = the image of `c ℓ`, the frozen blocks are `g°_ℓ(n) = (n𝟙) n`, and the matrices
`c_j c_j^⊤` of the gate columns of every block are linearly independent over `ℚ`. -/
theorem exists_mu_thetaDaggerGated_outer (hd : 2 ≤ Fintype.card d) (ιE : d ↪ dIn)
    (ιD : d ↪ dOut) (c : ∀ ℓ, d ↪ hid ℓ) :
    ∃ μ : ∀ ℓ, hid ℓ → ℝ, (∀ ℓ j, 0 < μ ℓ j) ∧
      GoodForConesGated (fun _ => posOrthant d) (fun ℓ => Finset.univ.map (c ℓ))
        (thetaDaggerGated (T := T) (σ := σ) (χ := χ) ιE ιD c μ) ∧
      (∀ ℓ (n : d → ℝ), frozenGated (thetaDaggerGated (T := T) (σ := σ) (χ := χ) ιE ιD c μ) ℓ
        (Finset.univ.map (c ℓ)) n = (∑ k, n k) • n) ∧
      ∀ ℓ, LinearIndependent ℚ (fun j : hid ℓ => Matrix.vecMulVec
        (((thetaDaggerGated (T := T) (σ := σ) (χ := χ) ιE ιD c μ).read ℓ)ᵀ (Sum.inl j))
        (((thetaDaggerGated (T := T) (σ := σ) (χ := χ) ιE ιD c μ).read ℓ)ᵀ (Sum.inl j))) := by
  sorry

/-- **Lemma D.13 of the dimension paper for GELU blocks, with `θ†` written out:** for `d ≥ 2`
there are numbers `μ > 0` such that `θ†` is good for the positive orthants with the active sets
`A_ℓ` = the image of `c ℓ`, the frozen blocks are `g°_ℓ(n) = n`, and the matrices `c_j c_j^⊤` of
the read columns of every block are linearly independent over `ℚ`. -/
theorem exists_mu_thetaDaggerMlp_outer (hd : 2 ≤ Fintype.card d) (ιE : d ↪ dIn)
    (ιD : d ↪ dOut) (c : ∀ ℓ, d ↪ hid ℓ) :
    ∃ μ : ∀ ℓ, hid ℓ → ℝ, (∀ ℓ j, 0 < μ ℓ j) ∧
      GoodForConesMlp (fun _ => posOrthant d) (fun ℓ => Finset.univ.map (c ℓ))
        (thetaDaggerMlp (T := T) (σ := σ) (χ := χ) ιE ιD c μ) ∧
      (∀ ℓ (n : d → ℝ), frozenMlp (thetaDaggerMlp (T := T) (σ := σ) (χ := χ) ιE ιD c μ) ℓ
        (Finset.univ.map (c ℓ)) n = n) ∧
      ∀ ℓ, LinearIndependent ℚ (fun j : hid ℓ => Matrix.vecMulVec
        (((thetaDaggerMlp (T := T) (σ := σ) (χ := χ) ιE ιD c μ).read ℓ)ᵀ j)
        (((thetaDaggerMlp (T := T) (σ := σ) (χ := χ) ιE ιD c μ).read ℓ)ᵀ j)) := by
  sorry

end Skips
