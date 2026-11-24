import SkipsLean.Depth.StepZeroGeluOne
import SkipsLean.Depth.SuffixFlatZeroConverse
import SkipsLean.Depth.RowsAux
import SkipsLean.Activations.Analytic

/-!
# The step for GELU on the path (Lemma D.19)

Paper (dimension paper): Appendix D.6 (the case `ε = 0`).

"Lemma D.19 (The step for GELU on the path). Let `σ` be GELU, in the case (0), let `θ` be regular,
and let block `k + 1` satisfy (P1) and (P2). Then `(D_{k+1})` implies `(D_k)`."

Its proof, after the path and the expansion (`Depth/StepZeroGeluPath.lean`):

"Step 1: […] At `t = 1` […] `0 = 𝓛(nW, 1; n) = 𝐃𝓑(n W V)(n (Z W V + η_W V + W η_V)) +
𝐃_θ𝓑(n W V) η'`. The right side is real-analytic and homogeneous of degree `0` in the row `n ≠ 0`,
and it vanishes for `ξ` in the open set `P`, hence for all `n ≠ 0`. With `h = n W V`, which takes
every value by (P1), this is (16) for `k + 1` with `Z' = (W V)⁻¹ (Z W V + η_W V + W η_V)` (49) and
`η'`. By `(D_{k+1})`, `Z' = Y_{k+1} + β' I` and `η'` is as in (18) […].

Step 2: the slowest hidden unit gives `Z`. […] `𝓛'_j(t) = ż_j(n(t)) 𝐃𝓑(n(t) W V) a_j`. At `t = 1`
this is `ż_j(n) 𝐃𝓑(n W V) a_j = 0` at `n = √d ξ`, for `ξ` in an open set. By (P1), `a_j ≠ 0`, so by
Lemma D.2 `𝐃𝓑(n W V) a_j ≠ 0` on an open dense set of `n`. So `ż_j(n) = 0` on an open subset of
`S` […]. So `Z = Y_k + β_k I` with `Y_k` antisymmetric.

Step 3: subtracting a symmetry. Let `β_{k+1} = β' − β_k`. The pair `Y_k + β_k I` and
`(−Y_k W, V (Y_{k+1} + β_{k+1} I), η')` is of the form (18), so it satisfies (16) for `k`.
Subtracting it from `Z` and `η` leaves the pair `0` and `(η°_W, η°_V, 0)` with
`η°_W = η_W + Y_k W`, `η°_V = η_V − V (Y_{k+1} + β_{k+1} I)`, which satisfies (16) for `k` as well,
and by (49) and Step 1 `η°_W V + W η°_V = 0` (51). […] It remains to show `η°_W = 0` and
`η°_V = 0`.

Step 4: the hidden units in the order of their rates. […] We show by induction on `i` that
column `j_i` of `η°_W` and row `j_i` of `η°_V` vanish. […] `𝓛°'_j(t) = (n η°_{c_j}) 𝐃𝓑(n W V) a_j`,
`𝓛°_j(t) = 𝐃𝓑(n W V) η°_{a_j}` at `n = n(t)` […]. At `t = 1`, for `ξ` in an open set and
`n = √d ξ`: by Lemma D.2, `n η°_{c_j} = 0`, so `η°_{c_j} = 0`, and `η°_{a_j}` is a multiple of
`n W V` for an open set of rows `n`, so `η°_{a_j} = 0`. After `i = q`: `η_W = −Y_k W` and
`η_V = V (Y_{k+1} + β_{k+1} I)`. With Step 1 for `η'` and Step 2 for `Z` this is (18) for `k`."

Stated here: the lemma, `claimZero_castSucc_gelu`. Step 1 is `exists_suffixFlatZero_succ_gelu`
(`Depth/StepZeroGeluOne.lean`: (49) and (16) for `k + 1`). The conditions (P1), (P2) are
`CondP1`, `CondP2` (`Depth/CondP.lean`); the `κ_ℓ` of Lemma D.14 is any `κ ∈ (0, 1]` such that `𝓑_{>k+1}` is
holomorphic on `C_κ`, as a hypothesis (as for `tanh`, `Depth/StepZeroTanh.lean`). Numbering as in
`Depth/StepTanh.lean`: the block is `k : Fin L`, the paper's block `k + 1`.
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut] {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]

/-- Helper: the unit row `x̂ = ‖x‖⁻¹ x` in the direction of a row `x`. -/
private noncomputable def unitRow_szg (x : d → ℝ) : d → ℝ := (Real.sqrt (x ⬝ᵥ x))⁻¹ • x

omit [DecidableEq d] in
/-- Helper: `x̂` is a unit row when `x ≠ 0`. -/
private theorem unitRow_dot_self_szg {x : d → ℝ} (hx : 0 < x ⬝ᵥ x) :
    unitRow_szg x ⬝ᵥ unitRow_szg x = 1 := by
  unfold unitRow_szg
  rw [smul_dotProduct, dotProduct_smul, smul_smul, smul_eq_mul, ← _root_.mul_inv,
    Real.mul_self_sqrt hx.le, inv_mul_cancel₀ hx.ne']

omit [DecidableEq d] in
/-- Helper: `x ↦ x̂` is continuous on the rows `x ≠ 0`. -/
private theorem continuousOn_unitRow_szg :
    ContinuousOn (unitRow_szg (d := d)) {x | 0 < x ⬝ᵥ x} := by
  have h1 : Continuous fun x : d → ℝ => x ⬝ᵥ x := by simp only [dotProduct]; fun_prop
  have h2 : ContinuousOn (fun x : d → ℝ => (Real.sqrt (x ⬝ᵥ x))⁻¹) {x | 0 < x ⬝ᵥ x} :=
    (Real.continuous_sqrt.comp h1).continuousOn.inv₀ fun x hx => (Real.sqrt_pos.2 hx).ne'
  exact h2.smul continuousOn_id

omit [DecidableEq d] in
/-- Helper: a nonzero row has `x ⬝ x > 0`. -/
private theorem dotProduct_self_pos_szg {x : d → ℝ} (hx : x ≠ 0) : 0 < x ⬝ᵥ x :=
  lt_of_le_of_ne (Finset.sum_nonneg fun j _ => mul_self_nonneg (x j))
    (Ne.symm (fun h => hx (dotProduct_self_eq_zero.1 h)))

/-- Helper: with `d ≥ 2`, every row has a unit row orthogonal to it. -/
private theorem exists_unit_orth_szg (hd : 2 ≤ Fintype.card d) (ξ : d → ℝ) :
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
    refine ⟨unitRow_szg y, unitRow_dot_self_szg (dotProduct_self_pos_szg hy0), ?_⟩
    unfold unitRow_szg
    rw [dotProduct_smul, hξy, smul_zero]

omit [Fintype T] in
/-- Helper: the rows of `c(x) M` (the row `x` at every token) are `x M`. -/
private theorem row_of_mul_szg {m n : Type*} [Fintype m] (x : m → ℝ) (M : Matrix m n ℝ) (t : T) :
    ((Matrix.of fun _ : T => x) * M) t = x ᵥ* M := by
  rw [Matrix.mul_apply_eq_vecMul]
  rfl

/-- Helper: `x M ≠ 0` for `x ≠ 0` and an invertible `M`. -/
private theorem vecMul_ne_zero_szg {M : Matrix d d ℝ} (hM : IsUnit M.det) {x : d → ℝ}
    (hx : x ≠ 0) : x ᵥ* M ≠ 0 := by
  intro h
  apply hx
  have e := congrArg (· ᵥ* M⁻¹) h
  simp only [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv M hM, Matrix.vecMul_one,
    Matrix.zero_vecMul] at e
  exact e

/-- Helper: `𝐃𝓑(h) v = c 𝐃𝓑(c h) v` for `c > 0` (homogeneity of degree `−1`). -/
private theorem fderiv_suffix_eq_smul_szg
    (θ : Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm 0) hid) dIn dOut)
    (hθ : RegularZero (Arch.mlp gelu (rmsNorm 0) hid) θ) (j : Fin (L + 1))
    (h v : Matrix T d ℝ) (hh : ∀ t, h t ≠ 0) {c : ℝ} (hc : 0 < c) :
    fderiv ℝ (fun h' : Matrix T d ℝ => suffix (Arch.mlp gelu (rmsNorm 0) hid) 0 θ j h') h v
      = c • fderiv ℝ (fun h' : Matrix T d ℝ => suffix (Arch.mlp gelu (rmsNorm 0) hid) 0 θ j h')
          (c • h) v := by
  rw [← map_smul, fderiv_suffix_zero_smul _ θ rfl
    (fun ℓ => analyticOnNhd_f_mlp analyticOnNhd_gelu ℓ) hθ j h v hh hc]

omit [Fintype T] [DecidableEq d] in
/-- Helper: `n_x W V = c (c(x) (W V))` with `c = √d ‖x‖⁻¹ > 0`, for `n_x = c(√d x̂)`. -/
private theorem path_row_eq_smul_szg {q : Type*} [Fintype q] (W : Matrix d q ℝ)
    (V : Matrix q d ℝ) (x : d → ℝ) :
    (Matrix.of fun _ : T => Real.sqrt (Fintype.card d) • unitRow_szg x) * W * V
      = (Real.sqrt (Fintype.card d) * (Real.sqrt (x ⬝ᵥ x))⁻¹)
          • ((Matrix.of fun _ : T => x) * (W * V)) := by
  have e : (Matrix.of fun _ : T => Real.sqrt (Fintype.card d) • unitRow_szg x)
      = (Real.sqrt (Fintype.card d) * (Real.sqrt (x ⬝ᵥ x))⁻¹) • Matrix.of fun _ : T => x := by
    ext t a
    simp only [unitRow_szg, Matrix.of_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [e, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_assoc]

/-- **The tool (Lemma D.2 on an open set, with a factor):** if `y` is continuous on an open set
`N` of rows `x ≠ 0`, `a ≠ 0`, and `y(x) 𝐃𝓑(n_x W V)(c(a)) = 0` on `N`, then `y = 0` on `N`. -/
private theorem tool_szg [Nonempty T]
    {θ : Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm 0) hid) dIn dOut}
    (hθ : RegularZero (Arch.mlp gelu (rmsNorm 0) hid) θ) (hd : 2 ≤ Fintype.card d) (k : Fin L)
    (hM : IsUnit (θ.read k * θ.write k).det)
    (N : Set (d → ℝ)) (hN : IsOpen N) (hN0 : ∀ x ∈ N, x ≠ 0) (a : d → ℝ) (ha : a ≠ 0)
    (y : (d → ℝ) → ℝ) (hy : ContinuousOn y N)
    (h : ∀ x ∈ N, y x • fderiv ℝ
      (fun h' : Matrix T d ℝ => suffix (Arch.mlp gelu (rmsNorm 0) hid) 0 θ k.succ h')
        ((Matrix.of fun _ : T => Real.sqrt (Fintype.card d) • unitRow_szg x) * θ.read k
          * θ.write k) (Matrix.of fun _ : T => a) = 0) :
    ∀ x ∈ N, y x = 0 := by
  intro x₀ hx₀
  by_contra hy0
  -- the open set `N' ⊆ N` where `y ≠ 0`
  have hN' : IsOpen (N ∩ y ⁻¹' {0}ᶜ) := hy.isOpen_inter_preimage hN isOpen_compl_singleton
  refine ha (eq_zero_of_fderiv_suffix_zero_eq_zero_rows analyticOnNhd_gelu θ hθ hd k.succ _ hM
    _ hN' ⟨x₀, hx₀, hy0⟩ a fun x hx => ?_)
  -- on `N'`: `𝐃𝓑(n_x W V)(c(a)) = 0`, and `c(x) (W V)` is `n_x W V` up to a factor `c > 0`
  have e := (smul_eq_zero.1 (h x hx.1)).resolve_left hx.2
  have hx0 := hN0 x hx.1
  have hc : 0 < Real.sqrt (Fintype.card d) * (Real.sqrt (x ⬝ᵥ x))⁻¹ :=
    mul_pos (Real.sqrt_pos.2 (by exact_mod_cast (by omega : 0 < Fintype.card d)))
      (inv_pos.2 (Real.sqrt_pos.2 (dotProduct_self_pos_szg hx0)))
  have hrows : ∀ t, ((Matrix.of fun _ : T => x) * (θ.read k * θ.write k)) t ≠ 0 := fun t => by
    rw [row_of_mul_szg]
    exact vecMul_ne_zero_szg hM hx0
  rw [fderiv_suffix_eq_smul_szg θ hθ k.succ _ _ hrows hc, ← path_row_eq_smul_szg, e, smul_zero]

/-- **The tool with `y = 1`:** if `𝐃𝓑(n_x W V)(c(a)) = 0` on a nonempty open set `N` of rows
`x ≠ 0`, then `a = 0`. -/
private theorem tool_one_szg [Nonempty T]
    {θ : Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm 0) hid) dIn dOut}
    (hθ : RegularZero (Arch.mlp gelu (rmsNorm 0) hid) θ) (hd : 2 ≤ Fintype.card d) (k : Fin L)
    (hM : IsUnit (θ.read k * θ.write k).det)
    (N : Set (d → ℝ)) (hN : IsOpen N) (hNne : N.Nonempty) (hN0 : ∀ x ∈ N, x ≠ 0) (a : d → ℝ)
    (h : ∀ x ∈ N, fderiv ℝ
      (fun h' : Matrix T d ℝ => suffix (Arch.mlp gelu (rmsNorm 0) hid) 0 θ k.succ h')
        ((Matrix.of fun _ : T => Real.sqrt (Fintype.card d) • unitRow_szg x) * θ.read k
          * θ.write k) (Matrix.of fun _ : T => a) = 0) :
    a = 0 := by
  by_contra ha
  obtain ⟨x, hx⟩ := hNne
  exact one_ne_zero (tool_szg hθ hd k hM N hN hN0 a ha (fun _ => 1) continuousOn_const
    (fun x hx => by rw [one_smul]; exact h x hx) x hx)

/-- **Lemma D.19 of the dimension paper (the step for GELU on the path).** Let `σ` be GELU, in the
case (0), `d ≥ 2`, let `θ` be regular, let `𝓑_{>k+1}` be holomorphic on the cone `C_κ`,
`0 < κ ≤ 1` (Lemma D.14), and let block `k` satisfy (P1) and (P2) for `κ`. Then `(D_{k+1})` implies
`(D_k)`. -/
theorem claimZero_castSucc_gelu [Nonempty T]
    {θ : Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm 0) hid) dIn dOut}
    (hθ : RegularZero (Arch.mlp gelu (rmsNorm 0) hid) θ) (hd : 2 ≤ Fintype.card d)
    (k : Fin L) (hP1 : CondP1 θ k) {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hhol : HolomorphicOnCone geluC θ k.succ κ) (hP2 : CondP2 θ k κ)
    (hk : ClaimZero (Arch.mlp gelu (rmsNorm 0) hid) θ k.succ) :
    ClaimZero (Arch.mlp gelu (rmsNorm 0) hid) θ k.castSucc := by
  sorry

end Skips
