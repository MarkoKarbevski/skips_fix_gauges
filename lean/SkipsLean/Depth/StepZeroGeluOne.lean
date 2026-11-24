import SkipsLean.Depth.StepZeroGeluPath
import SkipsLean.Depth.SuffixZeroRows
import SkipsLean.Depth.FlatAtMatrixRows
import SkipsLean.Activations.Analytic

/-!
# The step for GELU on the path: Step 1

Paper (dimension paper): Appendix D.6 (the case `ε = 0`), proof of Lemma D.19, Step 1:

"At `t = 1`, where `n(t)` is the row `n = √d ξ`, this reads, by (21), (20) and (15),
`0 = 𝓛(nW, 1; n) = 𝐃𝓑(n W V)(n (Z W V + η_W V + W η_V)) + 𝐃_θ𝓑(n W V) η'`. The right side is
real-analytic and homogeneous of degree `0` in the row `n ≠ 0`, and it vanishes for `ξ` in the open
set `P`, hence for all `n ≠ 0`. With `h = n W V`, which takes every value by (P1), this is (16) for
`k + 1` with `Z' = (W V)⁻¹ (Z W V + η_W V + W η_V)` (49) and `η'`."

The open set `P` is `isOpen_setOf_pathP2` (`Depth/CondP.lean`), the identity at one `ξ` is
`gelu_path_step_zero_real` (`Depth/StepZeroGeluPath.lean`), and Lemma D.3 at the matrix `W V` is
`flat_at_matrix_of_isOpen_rows` with `suffixFlatZero_of_flat_at_write`. Block `k : Fin L` is the
paper's block `k + 1`.
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut] {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]

omit [DecidableEq d] in
/-- Helper: a nonzero row has `x ⬝ x > 0`. -/
private theorem dotProduct_self_pos_one {x : d → ℝ} (hx : x ≠ 0) : 0 < x ⬝ᵥ x :=
  lt_of_le_of_ne (Finset.sum_nonneg fun j _ => mul_self_nonneg (x j))
    (Ne.symm (fun h => hx (dotProduct_self_eq_zero.1 h)))

omit [DecidableEq d] in
/-- Helper: the unit row `x̂ = ‖x‖⁻¹ x` of a row `x ≠ 0` is a unit row. -/
private theorem unitRow_dot_self_one {x : d → ℝ} (hx : 0 < x ⬝ᵥ x) :
    ((Real.sqrt (x ⬝ᵥ x))⁻¹ • x) ⬝ᵥ ((Real.sqrt (x ⬝ᵥ x))⁻¹ • x) = 1 := by
  rw [smul_dotProduct, dotProduct_smul, smul_smul, smul_eq_mul, ← _root_.mul_inv,
    Real.mul_self_sqrt hx.le, inv_mul_cancel₀ hx.ne']

/-- Helper: with `d ≥ 2`, every row has a unit row orthogonal to it. -/
private theorem exists_unit_orth_one (hd : 2 ≤ Fintype.card d) (ξ : d → ℝ) :
    ∃ ξ' : d → ℝ, ξ' ⬝ᵥ ξ' = 1 ∧ ξ ⬝ᵥ ξ' = 0 := by
  obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card (by omega : 1 < Fintype.card d)
  by_cases ha : ξ a = 0
  · -- the unit row `e_a`
    refine ⟨Pi.single a 1, ?_, ?_⟩
    · rw [dotProduct_single, Pi.single_eq_same, one_mul]
    · rw [dotProduct_single, ha, zero_mul]
  · -- the row `y = ξ_b e_a − ξ_a e_b`, normalized
    set y : d → ℝ := ξ b • Pi.single a 1 - ξ a • Pi.single b 1 with hy
    have hyb : y b = -ξ a := by
      simp only [hy, Pi.sub_apply, Pi.smul_apply, Pi.single_eq_same, Pi.single_eq_of_ne hab.symm,
        smul_eq_mul, mul_zero, mul_one, zero_sub]
    have hy0 : y ≠ 0 := fun h => ha (by
      have := congrFun h b
      rw [hyb, Pi.zero_apply] at this
      linarith)
    have hξy : ξ ⬝ᵥ y = 0 := by
      rw [hy, dotProduct_sub, dotProduct_smul, dotProduct_smul, dotProduct_single,
        dotProduct_single, smul_eq_mul, smul_eq_mul]
      ring
    refine ⟨(Real.sqrt (y ⬝ᵥ y))⁻¹ • y, unitRow_dot_self_one (dotProduct_self_pos_one hy0), ?_⟩
    rw [dotProduct_smul, hξy, smul_zero]

omit [Fintype T] [DecidableEq d] in
/-- Helper: at a matrix whose rows all equal `v`, `tangentRMS Z n = n Z − c n` with the number
`c = ⟨v Z, v⟩ / d`. -/
private theorem tangentRMS_const_one (Z : Matrix d d ℝ) (v : d → ℝ) :
    tangentRMS Z (Matrix.of fun _ : T => v)
      = (Matrix.of fun _ : T => v) * Z
        - ((v ᵥ* Z) ⬝ᵥ v / (Fintype.card d : ℝ)) • Matrix.of fun _ : T => v := by
  ext t i
  rfl

omit [Fintype T] [DecidableEq d] in
/-- Helper (the direction of `𝓛` at `n = a X`, `X` with the rows `x`): by (20),
`(1 ⊙ ż(n)) V + n W η_V = a X M_η − b (a X W V)` for a number `b`, with
`M_η = Z W V + η_W V + W η_V`. -/
private theorem dir_one {q : Type*} [Fintype q] (Z : Matrix d d ℝ) (W Wη : Matrix d q ℝ)
    (V Vη : Matrix q d ℝ) (x : d → ℝ) (a : ℝ) :
    ∃ b : ℝ, (tangentRMS Z (a • Matrix.of fun _ : T => x) * W
        + (a • Matrix.of fun _ : T => x) * Wη) * V + (a • Matrix.of fun _ : T => x) * W * Vη
      = a • ((Matrix.of fun _ : T => x) * (Z * (W * V) + Wη * V + W * Vη))
        - b • (a • ((Matrix.of fun _ : T => x) * (W * V))) := by
  have hn : (a • Matrix.of fun _ : T => x) = Matrix.of fun _ : T => a • x := by
    ext t i
    rfl
  refine ⟨((a • x) ᵥ* Z) ⬝ᵥ (a • x) / (Fintype.card d : ℝ), ?_⟩
  rw [hn, tangentRMS_const_one, ← hn]
  simp only [Matrix.sub_mul, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_assoc]
  module

/-- Helper (Step 1 at the row `n = a X`, `a > 0`, `X` with the rows `x`): by (15) and the
homogeneity of `𝓑_{>k+1}`, `𝓛(nW, 1; n) = 𝐃𝓑(X W V)(X M_η) + 𝐃_θ𝓑(X W V) η` when no row of
`X W V` vanishes. -/
private theorem blockLHS_eq_one
    (θ : Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm 0) hid) dIn dOut)
    (hθ : RegularZero (Arch.mlp gelu (rmsNorm 0) hid) θ) (k : Fin L) (Z : Matrix d d ℝ)
    (η : Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm 0) hid) dIn dOut) (x : d → ℝ)
    {a : ℝ} (ha : 0 < a)
    (hx : ∀ t, ((Matrix.of fun _ : T => x) * (θ.read k * θ.write k)) t ≠ 0) :
    blockLHS θ k η ((a • Matrix.of fun _ : T => x) * θ.read k) (fun _ _ => 1)
        (tangentRMS Z (a • Matrix.of fun _ : T => x) * θ.read k
          + (a • Matrix.of fun _ : T => x) * η.read k)
      = fderiv ℝ (fun h' : Matrix T d ℝ => suffix (Arch.mlp gelu (rmsNorm 0) hid) 0 θ k.succ h')
          ((Matrix.of fun _ : T => x) * (θ.read k * θ.write k))
          ((Matrix.of fun _ : T => x)
            * (Z * (θ.read k * θ.write k) + η.read k * θ.write k + θ.read k * η.write k))
        + fderiv ℝ (fun θ' : Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm 0) hid) dIn dOut =>
            suffix (Arch.mlp gelu (rmsNorm 0) hid) 0 θ' k.succ
              ((Matrix.of fun _ : T => x) * (θ.read k * θ.write k))) θ η := by
  have hf : ∀ ℓ, AnalyticOnNhd ℝ ((Arch.mlp (T := T) (d := d) gelu (rmsNorm 0) hid).f ℓ)
      Set.univ := fun ℓ => analyticOnNhd_f_mlp analyticOnNhd_gelu ℓ
  obtain ⟨b, hb⟩ := dir_one (T := T) Z (θ.read k) (η.read k) (θ.write k) (η.write k) x a
  have hpt : (a • Matrix.of fun _ : T => x) * θ.read k * θ.write k
      = a • ((Matrix.of fun _ : T => x) * (θ.read k * θ.write k)) := by
    rw [Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_assoc]
  have hone : ∀ y : Matrix T (hid k) ℝ,
      (Matrix.of fun t j => (fun (_ : T) (_ : hid k) => (1 : ℝ)) t j * y t j) = y := by
    intro y
    ext t j
    exact one_mul _
  have hax : ∀ t, (a • ((Matrix.of fun _ : T => x) * (θ.read k * θ.write k))) t ≠ 0 :=
    fun t => smul_ne_zero ha.ne' (hx t)
  unfold blockLHS
  rw [hone, hb, hpt, map_sub, map_smul _ b,
    fderiv_suffix_zero_apply_self _ θ rfl hf hθ k.succ _ hax, smul_zero, sub_zero,
    fderiv_suffix_zero_smul _ θ rfl hf hθ k.succ _ _ hx ha,
    fderiv_param_suffix_zero_smul _ θ rfl k.succ _ η ha]

/-- **Lemma D.19, Step 1:** for GELU in the case (0), `d ≥ 2`, regular `θ`, `𝓑_{>k+1}` holomorphic
on `C_κ`, `0 < κ ≤ 1`, and block `k` with (P1) and (P2): if `Z` and `η` satisfy (16) before block
`k`, then there is `Z'` with `Z W V + η_W V + W η_V = W V Z'` (49) such that `Z'` and `η` satisfy
(16) after block `k`. -/
theorem exists_suffixFlatZero_succ_gelu [Nonempty T]
    {θ : Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm 0) hid) dIn dOut}
    (hθ : RegularZero (Arch.mlp gelu (rmsNorm 0) hid) θ) (hd : 2 ≤ Fintype.card d)
    (k : Fin L) (hP1 : CondP1 θ k) {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hhol : HolomorphicOnCone geluC θ k.succ κ) (hP2 : CondP2 θ k κ)
    (Z : Matrix d d ℝ) (η : Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm 0) hid) dIn dOut)
    (h16 : SuffixFlatZero (Arch.mlp gelu (rmsNorm 0) hid) θ k.castSucc Z η) :
    ∃ Z' : Matrix d d ℝ,
      Z * (θ.read k * θ.write k) + η.read k * θ.write k + θ.read k * η.write k
        = θ.read k * θ.write k * Z' ∧
      SuffixFlatZero (Arch.mlp gelu (rmsNorm 0) hid) θ k.succ Z' η := by
  sorry

end Skips
