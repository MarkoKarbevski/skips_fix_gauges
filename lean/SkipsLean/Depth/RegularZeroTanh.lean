import SkipsLean.Depth.TanhPathBlock
import SkipsLean.Depth.ComplexSuffixStep
import SkipsLean.Depth.StepZeroTanh

/-!
# A parameter that satisfies all conditions of the case (0), for `tanh` blocks

Paper (dimension paper): Appendix D.6, "Parameters that satisfy all conditions, in the case (0)":
"We choose the blocks from the last to the first. Let `D` and the blocks `ℓ + 1, …, L` be chosen,
regular and with (S1) to (S3) for tanh […]. This fixes `κ_ℓ` (Lemma D.14). We choose
`(W, V) = (W_read^ℓ, W_write^ℓ)`. […] So there are parameters `θ*` that are regular and whose
blocks all satisfy (S1) to (S3) for tanh".

Stated here: for `d_in, d_out ≥ d ≥ 2` and at least `d` hidden units in every block there is a
parameter `θ*` that is regular in the sense of the case (0) (`RegularZero`) and whose every block
`k` satisfies (S1), (S2), and (S3) for a cone `C_κ` on which the network after the block,
`𝓑_{>k+1}`, is holomorphic (the `κ_ℓ` of Lemma D.14). These are the hypotheses of Lemma D.18
(`claimZero_castSucc_tanh`, `Depth/StepZeroTanh.lean`) at every block.

One block is `exists_tanhPathBlock` (`Depth/TanhPathBlock.lean`); the cone of a block depends only
on the later blocks (`Depth/ComplexSuffixStep.lean`). Numbering: the block `k : Fin L` is the
paper's block `k + 1`.
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut] {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]

/-- Helper: `tanh` is holomorphic at every real point (`cosh x ≠ 0`). -/
private theorem analyticAt_ctanh_rz (x : ℝ) : AnalyticAt ℂ Complex.tanh (x : ℂ) := by
  have hfun : Complex.tanh = fun z => Complex.sinh z / Complex.cosh z := by
    funext z; exact Complex.tanh_eq_sinh_div_cosh z
  have hc : Complex.cosh (x : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_cosh]
    exact_mod_cast (Real.cosh_pos x).ne'
  rw [hfun]
  exact (Complex.differentiable_sinh.analyticAt _).div
    (Complex.differentiable_cosh.analyticAt _) hc

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: for `|n| ≤ |m|` there is an `m × n` matrix of rank `|n|`. -/
private theorem exists_rank_rz {m n : Type*} [Fintype m] [Fintype n]
    (h : Fintype.card n ≤ Fintype.card m) : ∃ E : Matrix m n ℝ, E.rank = Fintype.card n := by
  classical
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le h
  -- `E = 1.submatrix id e` has the left inverse `Eᵀ`
  refine ⟨(1 : Matrix m m ℝ).submatrix id e, le_antisymm (rank_le_card_width _) ?_⟩
  have h1 : ((1 : Matrix m m ℝ).submatrix id e)ᵀ * (1 : Matrix m m ℝ).submatrix id e = 1 := by
    rw [Matrix.transpose_submatrix, Matrix.transpose_one,
      ← Matrix.submatrix_mul _ _ _ id _ Function.bijective_id, Matrix.one_mul,
      Matrix.submatrix_one_embedding]
  calc Fintype.card n = (1 : Matrix n n ℝ).rank := (Matrix.rank_one).symm
    _ = _ := by rw [← h1]
    _ ≤ _ := rank_mul_le_right _ _

omit [Fintype T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: a parameter with the read and the write of block `k` replaced. -/
private theorem exists_update_rz
    (θ : Params (Arch.mlp (T := T) (d := d) Real.tanh (rmsNorm 0) hid) dIn dOut) (k : Fin L)
    (W : Matrix d (hid k) ℝ) (V : Matrix (hid k) d ℝ) :
    ∃ θ' : Params (Arch.mlp (T := T) (d := d) Real.tanh (rmsNorm 0) hid) dIn dOut,
      θ'.E = θ.E ∧ θ'.D = θ.D ∧ (∀ ℓ, ℓ ≠ k → θ'.read ℓ = θ.read ℓ) ∧
      (∀ ℓ, ℓ ≠ k → θ'.write ℓ = θ.write ℓ) ∧ θ'.read k = W ∧ θ'.write k = V :=
  ⟨⟨θ.E, Function.update θ.read k W, Function.update θ.write k V, θ.D⟩, rfl, rfl,
    fun _ h => Function.update_of_ne h _ _, fun _ h => Function.update_of_ne h _ _,
    Function.update_self _ _ _, Function.update_self _ _ _⟩

omit [DecidableEq d] [Fintype dIn] in
/-- Helper, the choice of the blocks from the last to the first: for every hidden state `k` there
is a parameter with the given `E₀`, `D₀`, a cone on which `𝓑_{>k}` is holomorphic, and whose blocks
after `k` satisfy all conditions of `TanhPathBlock` for a cone on which the network after them is
holomorphic. -/
private theorem exists_suffix_rz (hd : 2 ≤ Fintype.card d)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) (E₀ : Matrix dIn d ℝ)
    (D₀ : Matrix d dOut ℝ) (k : Fin (L + 1)) :
    ∃ θ : Params (Arch.mlp (T := T) (d := d) Real.tanh (rmsNorm 0) hid) dIn dOut,
      θ.E = E₀ ∧ θ.D = D₀ ∧ (∃ κ : ℝ, 0 < κ ∧ HolomorphicOnCone Complex.tanh θ k κ) ∧
      ∀ ℓ : Fin L, k ≤ ℓ.castSucc → ∃ κ : ℝ, 0 < κ ∧ TanhPathBlock (θ.read ℓ) (θ.write ℓ) κ ∧
        HolomorphicOnCone Complex.tanh θ ℓ.succ κ := by
  induction k using Fin.reverseInduction with
  | last =>
    -- no block after the last hidden state; `𝓑_{>L}` is holomorphic on `C_1`
    refine ⟨⟨E₀, fun _ => 0, fun _ => 0, D₀⟩, rfl, rfl,
      ⟨1, one_pos, holomorphicOnCone_last _ _⟩, fun ℓ hℓ => ?_⟩
    exact absurd hℓ (not_le.2 (Fin.castSucc_lt_last ℓ))
  | cast k ih =>
    obtain ⟨θ, hE, hD, ⟨κ', hκ', hhol⟩, hB⟩ := ih
    -- the block `k` for the cone `C_{κ'}` of `𝓑_{>k+1}`
    obtain ⟨W, V, hWV⟩ := exists_tanhPathBlock hd (hhid k) hκ'
    obtain ⟨θ', hE', hD', hread, hwrite, hrk, hwk⟩ := exists_update_rz θ k W V
    rw [← hrk, ← hwk] at hWV
    -- the blocks after `k + 1` are those of `θ`
    have hlt : ∀ ℓ : Fin L, k.succ ≤ ℓ.castSucc → ℓ ≠ k := fun ℓ hℓ e => by
      subst e; exact absurd hℓ (not_le.2 (Fin.castSucc_lt_succ (i := ℓ)))
    have hcongr : ∀ (j : Fin (L + 1)) (κ : ℝ), k.succ ≤ j →
        HolomorphicOnCone Complex.tanh θ j κ → HolomorphicOnCone Complex.tanh θ' j κ :=
      fun j κ hj h => h.congr (fun ℓ hℓ => hread ℓ (hlt ℓ (le_trans hj hℓ)))
        (fun ℓ hℓ => hwrite ℓ (hlt ℓ (le_trans hj hℓ))) hD'
    have hhol' : HolomorphicOnCone Complex.tanh θ' k.succ κ' := hcongr _ _ le_rfl hhol
    -- the cone of `𝓑_{>k}` (Lemma D.14, with (R2) of the block `k`)
    obtain ⟨κ, hκ, -, hholk⟩ := exists_holomorphicOnCone_castSucc
      (fun x => (Complex.ofReal_tanh x).symm) analyticAt_ctanh_rz θ' k hκ' hhol' hWV.ne_zero
    refine ⟨θ', hE'.trans hE, hD'.trans hD, ⟨κ, hκ, hholk⟩, fun ℓ hℓ => ?_⟩
    rcases eq_or_ne ℓ k with rfl | hne
    · exact ⟨κ', hκ', hWV, hhol'⟩
    · -- a later block: `k + 1 ≤ ℓ`
      have hkℓ : k.succ ≤ ℓ.castSucc := by
        rw [Fin.le_iff_val_le_val] at hℓ ⊢
        rw [Fin.val_castSucc, Fin.val_castSucc] at hℓ
        rw [Fin.val_succ, Fin.val_castSucc]
        have : k.val ≠ ℓ.val := fun e => hne (Fin.ext e.symm)
        omega
      obtain ⟨κℓ, hκℓ, hT, hh⟩ := hB ℓ hkℓ
      refine ⟨κℓ, hκℓ, ?_, hcongr _ _ (le_trans hkℓ (Fin.castSucc_le_succ ℓ)) hh⟩
      rw [hread ℓ hne, hwrite ℓ hne]
      exact hT

/-- Helper: row `t` of a matrix, as a continuous linear map. -/
private noncomputable def rowCLM_rz {n : Type*} [Fintype n] (t : T) :
    Matrix T n ℝ →L[ℝ] (n → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => M t
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

/-- Helper: the matrix whose rows all equal `m`, as a continuous linear map. -/
private noncomputable def constCLM_rz (T : Type*) [Fintype T] : (d → ℝ) →L[ℝ] Matrix T d ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun m => Matrix.of fun _ => m
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

omit [Fintype T] [DecidableEq d] in
/-- Helper: row `t` of the block `tanh(nW) V` is the block at the row `n_t`. -/
private theorem block_row_rz {q : Type*} [Fintype q] (W : Matrix d q ℝ) (V : Matrix q d ℝ)
    (n : Matrix T d ℝ) (t : T) :
    ((n * W).map Real.tanh * V) t = (fun j => Real.tanh ((n t ᵥ* W) j)) ᵥ* V := rfl

omit [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper, (R3) for all rows: with the row `n₀` of (R3) of one block at every token, a direction
`v` whose rows are orthogonal to `n₀` and for which every row of `𝐃g(n) v` is a multiple of the
same row of `g(n)` is `0`; the block acts on every row alone, so row `t` of `𝐃g(n) v` is
`𝐃g(n₀) v_t`. -/
private theorem deriv_block_rz
    (θ : Params (Arch.mlp (T := T) (d := d) Real.tanh (rmsNorm 0) hid) dIn dOut) (ℓ : Fin L)
    {κ : ℝ} (hT : TanhPathBlock (θ.read ℓ) (θ.write ℓ) κ) :
    ∃ n : Matrix T d ℝ, (∀ t, n t ⬝ᵥ n t = (Fintype.card d : ℝ)) ∧
      ∀ v : Matrix T d ℝ, (∀ t, v t ⬝ᵥ n t = 0) →
        (∀ t, ∃ a : ℝ,
          fderiv ℝ (fun n' : Matrix T d ℝ =>
              (Arch.mlp (T := T) (d := d) Real.tanh (rmsNorm 0) hid).f ℓ (n' * θ.read ℓ)
                * θ.write ℓ) n v t
            = a • ((Arch.mlp (T := T) (d := d) Real.tanh (rmsNorm 0) hid).f ℓ (n * θ.read ℓ)
                * θ.write ℓ) t) →
        v = 0 := by
  obtain ⟨n₀, hn₀, hder⟩ := hT.deriv
  -- the block on matrices, `G`, and on rows, `g`
  let G := fun n' : Matrix T d ℝ =>
    (Arch.mlp (T := T) (d := d) Real.tanh (rmsNorm 0) hid).f ℓ (n' * θ.read ℓ) * θ.write ℓ
  let g := fun m : d → ℝ => (fun j => Real.tanh ((m ᵥ* θ.read ℓ) j)) ᵥ* θ.write ℓ
  have hGa : AnalyticOnNhd ℝ G Set.univ :=
    analyticOnNhd_block (Arch.mlp (T := T) (d := d) Real.tanh (rmsNorm 0) hid) θ
      (fun ℓ => analyticOnNhd_f_mlp analyticOnNhd_tanh ℓ) ℓ
  have hGd : ∀ x, HasFDerivAt G (fderiv ℝ G x) x := fun x =>
    (hGa x (Set.mem_univ _)).differentiableAt.hasFDerivAt
  refine ⟨Matrix.of fun _ => n₀, fun _ => hn₀, fun v hv hva => ?_⟩
  -- row `t` of `𝐃G(n) v` is `𝐃g(n_t) v_t`
  have key : ∀ t, fderiv ℝ G (Matrix.of fun _ => n₀) v t = fderiv ℝ g n₀ (v t) := by
    intro t
    let P := rowCLM_rz (n := d) t
    let R := constCLM_rz (d := d) T
    -- `g = P ∘ G ∘ R` is differentiable
    have hgd : HasFDerivAt g (fderiv ℝ g n₀) n₀ := by
      have h := (P.hasFDerivAt.comp _ (hGd (R n₀))).comp n₀ R.hasFDerivAt
      exact h.differentiableAt.hasFDerivAt
    -- `P ∘ G = g ∘ P`; the chain rule on both sides, and uniqueness of the derivative
    have hfac : ⇑P ∘ G = g ∘ ⇑P := rfl
    have h1 := P.hasFDerivAt.comp (Matrix.of fun _ => n₀) (hGd (Matrix.of fun _ => n₀))
    have h2 : HasFDerivAt (g ∘ ⇑P) ((fderiv ℝ g n₀).comp P) (Matrix.of fun _ => n₀) :=
      hgd.comp (Matrix.of fun _ => n₀) P.hasFDerivAt
    rw [hfac] at h1
    exact DFunLike.congr_fun (h1.unique h2) v
  -- every row of `v` is `0`, by (R3) of the block at `n₀`
  have hrow : ∀ t, v t = 0 := fun t => by
    obtain ⟨a, ha⟩ := hva t
    exact hder (v t) (hv t) ⟨a, (key t).symm.trans ha⟩
  ext t i
  rw [hrow t]
  rfl

omit [DecidableEq d] in
/-- **"So there are parameters `θ*` that are regular and whose blocks all satisfy (S1) to (S3) for
tanh"** (Appendix D.6): for `d_in, d_out ≥ d ≥ 2` and at least `d` hidden units in every block,
there is a parameter that is regular in the sense of the case (0) and whose every block `k`
satisfies (S1), (S2), and (S3) for a cone `C_κ`, `κ > 0`, on which `𝓑_{>k+1}` is holomorphic. -/
theorem exists_regularZero_tanh_path [Nonempty T] (hd : 2 ≤ Fintype.card d)
    (hdIn : Fintype.card d ≤ Fintype.card dIn) (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∃ θ : Params (Arch.mlp (T := T) (d := d) Real.tanh (rmsNorm 0) hid) dIn dOut,
      RegularZero (Arch.mlp Real.tanh (rmsNorm 0) hid) θ ∧
      ∀ k : Fin L,
        (∀ i j : hid k, i ≠ j → ∀ a c : ℝ, a • θ.write k i + c • θ.write k j = 0 →
          a = 0 ∧ c = 0) ∧
        LinearIndependent ℚ (fun j : hid k => fun i : d => θ.read k i j) ∧
        ∃ κ : ℝ, 0 < κ ∧ HolomorphicOnCone Complex.tanh θ k.succ κ ∧ CondS3 θ k κ := by
  -- `E₀` and `D₀` of rank `d`
  obtain ⟨E₀, hE₀⟩ := exists_rank_rz (m := dIn) (n := d) hdIn
  obtain ⟨D₁, hD₁⟩ := exists_rank_rz (m := dOut) (n := d) hdOut
  -- the blocks chosen from the last to the first, down to the hidden state `0`
  obtain ⟨θ, hE, hD, -, hB⟩ := exists_suffix_rz (T := T) (hid := hid) hd hhid E₀ D₁ᵀ 0
  have hB' : ∀ ℓ : Fin L, ∃ κ : ℝ, 0 < κ ∧ TanhPathBlock (θ.read ℓ) (θ.write ℓ) κ ∧
      HolomorphicOnCone Complex.tanh θ ℓ.succ κ := fun ℓ => hB ℓ (Fin.zero_le _)
  refine ⟨θ, ⟨?_, ?_, fun ℓ => ?_, fun ℓ n hn t => ?_, fun ℓ => ?_⟩, fun k => ?_⟩
  · -- (R1) for `E`
    rw [hE, hE₀]
  · -- (R1) for `D`
    rw [hD, Matrix.rank_transpose, hD₁]
  · -- (R1) for the writes
    obtain ⟨κ, -, hT, -⟩ := hB' ℓ
    exact hT.rank_write
  · -- (R2) at every row
    obtain ⟨κ, -, hT, -⟩ := hB' ℓ
    show ((n * θ.read ℓ).map Real.tanh * θ.write ℓ) t ≠ 0
    rw [block_row_rz]
    exact hT.ne_zero (n t) (hn t)
  · -- (R3)
    obtain ⟨κ, -, hT, -⟩ := hB' ℓ
    exact deriv_block_rz θ ℓ hT
  · -- (S1), (S2), (S3) with the cone of the block
    obtain ⟨κ, hκ, hT, hhol⟩ := hB' k
    exact ⟨hT.rows_indep, hT.cols_indep, κ, hκ, hhol, hT.saturated⟩


end Skips
