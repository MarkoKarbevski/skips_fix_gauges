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

omit [Fintype T] [DecidableEq d] in
/-- Helper: the entry `(t, j)` of `ż = (n Z − (⟨nZ, n⟩/d) n) W + n M` at `n = c(ν)` (the row `ν`
at every token). -/
private theorem zdot_entry_szg {q : Type*} [Fintype q] (Z : Matrix d d ℝ) (W M : Matrix d q ℝ)
    (ν : d → ℝ) (t : T) (j : q) :
    (tangentRMS Z (Matrix.of fun _ : T => ν) * W + (Matrix.of fun _ : T => ν) * M) t j
      = (ν ᵥ* (Z * W + M)) j - ((ν ᵥ* Z) ⬝ᵥ ν / (Fintype.card d : ℝ)) * (ν ᵥ* W) j := by
  have h1 : (tangentRMS Z (Matrix.of fun _ : T => ν)) t
      = ν ᵥ* Z - ((ν ᵥ* Z) ⬝ᵥ ν / (Fintype.card d : ℝ)) • ν := by
    show ((Matrix.of fun _ : T => ν) * Z) t
        - ((((Matrix.of fun _ : T => ν) * Z) t ⬝ᵥ ν) / (Fintype.card d : ℝ)) • ν = _
    rw [row_of_mul_szg]
  rw [Matrix.add_apply, Matrix.mul_apply_eq_vecMul, h1, row_of_mul_szg, Matrix.sub_vecMul,
    Matrix.smul_vecMul, Matrix.vecMul_vecMul, Matrix.vecMul_add]
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- **Steps 2 and 4, from `𝐃𝓑(n W V)(ż_j(n) a_j) = 0` to a quadratic identity:** if this holds at
`n = n_x` for the rows `x` of an open set `N` of rows `x ≠ 0`, then
`(x ⬝ x)(x ⬝ u) = (x Z xᵀ)(x ⬝ c_j)` on `N`, with `u` the column `j` of `Z W + M`. -/
private theorem quadratic_of_unit_szg [Nonempty T]
    {θ : Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm 0) hid) dIn dOut}
    (hθ : RegularZero (Arch.mlp gelu (rmsNorm 0) hid) θ) (hd : 2 ≤ Fintype.card d) (k : Fin L)
    (hM : IsUnit (θ.read k * θ.write k).det) (j : hid k) (hVj : θ.write k j ≠ 0)
    (Z : Matrix d d ℝ) (M : Matrix d (hid k) ℝ)
    (N : Set (d → ℝ)) (hN : IsOpen N) (hN0 : ∀ x ∈ N, x ≠ 0)
    (h : ∀ x ∈ N, fderiv ℝ
      (fun h' : Matrix T d ℝ => suffix (Arch.mlp gelu (rmsNorm 0) hid) 0 θ k.succ h')
        ((Matrix.of fun _ : T => Real.sqrt (Fintype.card d) • unitRow_szg x) * θ.read k
          * θ.write k)
        (Matrix.of fun t =>
          (tangentRMS Z (Matrix.of fun _ : T => Real.sqrt (Fintype.card d) • unitRow_szg x)
              * θ.read k
            + (Matrix.of fun _ : T => Real.sqrt (Fintype.card d) • unitRow_szg x) * M) t j
            • θ.write k j) = 0) :
    ∀ x ∈ N, (x ⬝ᵥ x) * (x ⬝ᵥ fun a => (Z * θ.read k + M) a j)
      = ((x ᵥ* Z) ⬝ᵥ x) * (x ⬝ᵥ fun a => θ.read k a j) := by
  -- `y(ξ) = ξ(ZW + M)_j − ⟨ξZ, ξ⟩ (ξW)_j`, continuous; `ż_j(n_x) = √d y(x̂)`
  set g : (d → ℝ) → ℝ := fun ξ =>
    (ξ ᵥ* (Z * θ.read k + M)) j - ((ξ ᵥ* Z) ⬝ᵥ ξ) * (ξ ᵥ* θ.read k) j with hg_def
  have hg : Continuous g := by
    simp only [hg_def, Matrix.vecMul, dotProduct]
    fun_prop
  have hD : (0 : ℝ) < Fintype.card d := by exact_mod_cast (by omega : 0 < Fintype.card d)
  have hs : Real.sqrt (Fintype.card d) * Real.sqrt (Fintype.card d) = Fintype.card d :=
    Real.mul_self_sqrt hD.le
  have hent : ∀ x ∈ N, ∀ t : T,
      (tangentRMS Z (Matrix.of fun _ : T => Real.sqrt (Fintype.card d) • unitRow_szg x)
          * θ.read k
        + (Matrix.of fun _ : T => Real.sqrt (Fintype.card d) • unitRow_szg x) * M) t j
        = Real.sqrt (Fintype.card d) * g (unitRow_szg x) := by
    intro x _ t
    rw [zdot_entry_szg]
    simp only [hg_def, Matrix.smul_vecMul, smul_dotProduct, dotProduct_smul, Pi.smul_apply,
      smul_eq_mul]
    generalize Real.sqrt (Fintype.card d) = r at hs ⊢
    rw [← hs]
    have hr : r ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hs
      exact hD.ne hs
    field_simp
  -- so `√d y(x̂) 𝐃𝓑(n_x W V)(c(a_j)) = 0`, and by the tool `y(x̂) = 0` on `N`
  have hy := tool_szg hθ hd k hM N hN hN0 (θ.write k j) hVj
    (fun x => Real.sqrt (Fintype.card d) * g (unitRow_szg x))
    (continuousOn_const.mul (hg.comp_continuousOn
      (continuousOn_unitRow_szg.mono fun x hx => dotProduct_self_pos_szg (hN0 x hx))))
    (fun x hx => by
      have e := h x hx
      have hv : (Matrix.of fun t =>
          (tangentRMS Z (Matrix.of fun _ : T => Real.sqrt (Fintype.card d) • unitRow_szg x)
              * θ.read k
            + (Matrix.of fun _ : T => Real.sqrt (Fintype.card d) • unitRow_szg x) * M) t j
            • θ.write k j)
          = (Real.sqrt (Fintype.card d) * g (unitRow_szg x))
            • Matrix.of fun _ : T => θ.write k j := by
        ext t a
        simp only [Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, Pi.smul_apply, hent x hx t]
      rw [hv, map_smul] at e
      exact e)
  -- multiply `y(x̂) = 0` by `‖x‖³`
  intro x hx
  have e := (mul_eq_zero.1 (hy x hx)).resolve_left (Real.sqrt_pos.2 hD).ne'
  have hxx := dotProduct_self_pos_szg (hN0 x hx)
  simp only [hg_def, unitRow_szg, Matrix.smul_vecMul, smul_dotProduct, dotProduct_smul,
    Pi.smul_apply, smul_eq_mul] at e
  have hr2 : Real.sqrt (x ⬝ᵥ x) ^ 2 = x ⬝ᵥ x := Real.sq_sqrt hxx.le
  have hr := (Real.sqrt_pos.2 hxx).ne'
  show (x ⬝ᵥ x) * (x ᵥ* (Z * θ.read k + M)) j = ((x ᵥ* Z) ⬝ᵥ x) * (x ᵥ* θ.read k) j
  generalize Real.sqrt (x ⬝ᵥ x) = r at hr2 hr e
  rw [← hr2]
  field_simp at e
  linear_combination e

omit [DecidableEq d] [Fintype dIn] in
/-- **Step 4, the hypothesis `hA`:** let `η°` vanish at the blocks after block `k` and at `D`, let
`η°_W V + W η°_V = 0` (51), and let column `i` of `η°_W` and row `i` of `η°_V` vanish for `i ∈ A`.
Then `𝓛(P W − δ, 1 − δ'; ż°(P)) = 0` (with `Z = 0`) for every complex `P` and all rows `δ, δ'`
whose entries outside `A` vanish: its direction is `0`, and so is its derivative in the weights. -/
private theorem blockLHSC_eq_zero_szg
    (θ : Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm 0) hid) dIn dOut) (k : Fin L)
    (η : Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm 0) hid) dIn dOut)
    (hr : ∀ ℓ : Fin L, k.succ ≤ ℓ.castSucc → η.read ℓ = 0)
    (hw : ∀ ℓ : Fin L, k.succ ≤ ℓ.castSucc → η.write ℓ = 0) (hD : η.D = 0)
    (h51 : η.read k * θ.write k + θ.read k * η.write k = 0) (A : Set (hid k))
    (hA : ∀ i ∈ A, (∀ a, η.read k a i = 0) ∧ η.write k i = 0)
    (P : Matrix T d ℂ) (δ δ' : hid k → ℂ) (hδ : ∀ i, i ∉ A → δ i = 0 ∧ δ' i = 0) :
    blockLHSC geluC θ k η (Matrix.of fun τ i => (P * θ.toC.1 k) τ i - δ i)
      (Matrix.of fun _ i => 1 - δ' i) (zdotC θ k 0 η P) = 0 := by
  -- the derivative in the weights vanishes: `η°` is zero after block `k` and at `D`
  have h2 := fderiv_weights_suffixC_eq_zero geluC θ.toC η.toC k.succ
    ((Matrix.of fun τ i => (P * θ.toC.1 k) τ i - δ i) * θ.toC.2.1 k)
    (fun ℓ hℓ => by
      show (η.read ℓ).map (fun x : ℝ => (x : ℂ)) = 0
      rw [hr ℓ hℓ, Matrix.map_zero _ Complex.ofReal_zero])
    (fun ℓ hℓ => by
      show (η.write ℓ).map (fun x : ℝ => (x : ℂ)) = 0
      rw [hw ℓ hℓ, Matrix.map_zero _ Complex.ofReal_zero])
    (by
      show η.D.map (fun x : ℝ => (x : ℂ)) = 0
      rw [hD, Matrix.map_zero _ Complex.ofReal_zero])
  -- `ż°(P) = P η°_W` (`Z = 0`)
  have hz : zdotC θ k 0 η P = P * η.toC.1 k := by
    have h0 : tangentRMSC (0 : Matrix d d ℝ) P = 0 := by
      ext t i
      simp only [tangentRMSC, Matrix.map_zero _ Complex.ofReal_zero, Matrix.mul_zero,
        Matrix.of_apply, Matrix.zero_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rw [show ((0 : Matrix T d ℂ) t ⬝ᵥ P t) = 0 from zero_dotProduct _]
      simp
    rw [zdotC, h0, Matrix.zero_mul, zero_add]
  -- (51) at complex entries
  have h51C : η.toC.1 k * θ.toC.2.1 k + θ.toC.1 k * η.toC.2.1 k = 0 := by
    have e := congrArg (fun M => M.map (fun x : ℝ => (x : ℂ))) h51
    have m1 : (η.read k * θ.write k).map (fun x : ℝ => (x : ℂ)) = η.toC.1 k * θ.toC.2.1 k :=
      Matrix.map_mul (f := Complex.ofRealHom)
    have m2 : (θ.read k * η.write k).map (fun x : ℝ => (x : ℂ)) = θ.toC.1 k * η.toC.2.1 k :=
      Matrix.map_mul (f := Complex.ofRealHom)
    simp only [Matrix.map_add _ (fun a b => Complex.ofReal_add a b), m1, m2,
      Matrix.map_zero _ Complex.ofReal_zero] at e
    exact e
  -- each unit `i` is in `A` (its column and row of `η°` vanish) or has `δ_i = δ'_i = 0`
  have hcol : ∀ t i, δ' i * (P * η.toC.1 k) t i = 0 := by
    intro t i
    by_cases hi : i ∈ A
    · rw [Matrix.mul_apply, Finset.sum_eq_zero fun b _ => by
        rw [show η.toC.1 k b i = ((η.read k b i : ℝ) : ℂ) from rfl, (hA i hi).1 b,
          Complex.ofReal_zero, mul_zero], mul_zero]
    · rw [(hδ i hi).2, zero_mul]
  have hrow : ∀ i a, δ i * η.toC.2.1 k i a = 0 := by
    intro i a
    by_cases hi : i ∈ A
    · rw [show η.toC.2.1 k i a = ((η.write k i a : ℝ) : ℂ) from rfl, (hA i hi).2,
        Pi.zero_apply, Complex.ofReal_zero, mul_zero]
    · rw [(hδ i hi).1, zero_mul]
  -- the direction `((1 − δ') ⊙ P η°_W) V + (P W − δ) η°_V = P (η°_W V + W η°_V) = 0`
  have e1 : (Matrix.of fun t j => (Matrix.of fun (_ : T) i => 1 - δ' i) t j
      * (P * η.toC.1 k) t j) = P * η.toC.1 k := by
    ext t j
    simp only [Matrix.of_apply]
    linear_combination -(hcol t j)
  have e2 : (Matrix.of fun τ i => (P * θ.toC.1 k) τ i - δ i) * η.toC.2.1 k
      = P * θ.toC.1 k * η.toC.2.1 k := by
    ext τ a
    simp only [Matrix.mul_apply, Matrix.of_apply, sub_mul, Finset.sum_sub_distrib]
    rw [Finset.sum_eq_zero fun i _ => hrow i a, sub_zero]
  have hdir : (Matrix.of fun t j => (Matrix.of fun (_ : T) i => 1 - δ' i) t j
      * zdotC θ k 0 η P t j) * θ.toC.2.1 k
      + (Matrix.of fun τ i => (P * θ.toC.1 k) τ i - δ i) * η.toC.2.1 k = 0 := by
    rw [hz, e1, e2, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_add, h51C, Matrix.mul_zero]
  unfold blockLHSC
  rw [hdir, map_zero, h2, add_zero]

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: `τ ↦ (−τ) G(τ)` has the derivative `−G(0)` at `0` when `G` is continuous at `0`. -/
private theorem hasDerivAt_neg_smul_szg {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {G : ℝ → F} (hG : ContinuousAt G 0) :
    HasDerivAt (fun τ : ℝ => (-τ) • G τ) (-G 0) 0 := by
  rw [hasDerivAt_iff_tendsto_slope]
  -- the slope at `τ ≠ 0` is `−G(τ)`
  have e : ∀ τ ∈ ({0}ᶜ : Set ℝ), -G τ = slope (fun τ : ℝ => (-τ) • G τ) 0 τ := by
    intro τ hτ
    rw [slope_def_module, neg_zero, zero_smul, sub_zero, sub_zero, neg_smul, smul_neg, smul_smul,
      inv_mul_cancel₀ hτ, one_smul]
  exact (hG.neg.tendsto.mono_left nhdsWithin_le_nhds).congr'
    (eventually_nhdsWithin_of_forall e)

omit [Fintype T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (as `analyticAt_fderiv_apply_fam` of `Depth/FlatAtMatrixRows.lean`): `y ↦ 𝐃f(g(y)) u(y)`
is analytic at `x` if `f` is analytic at `g(x)` and `g`, `u` are analytic at `x`. -/
private theorem analyticAt_fderiv_apply_szg {E F G : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {f : E → F} {g u : G → E} {x : G}
    (hg : AnalyticAt ℝ g x) (hu : AnalyticAt ℝ u x) (hf : AnalyticAt ℝ f (g x)) :
    AnalyticAt ℝ (fun y => fderiv ℝ f (g y) (u y)) x := by
  have h1 := hf.fderiv.comp hg
  have h2 := ((ContinuousLinearMap.id ℝ (E →L[ℝ] F)).analyticAt_bilinear
    (fderiv ℝ f (g x), u x)).comp₂ h1 hu
  exact h2

/-- **Step 4, from `𝓛_j(1) = 0` to the row `j` of `η°_V`:** with `η°` zero after block `k` and at
`D` and (51), `𝓛(nW − τ e_j, 1; ż°(n)) = −τ 𝐃𝓑(nWV − τ c(a_j)) c(η°_{a_j})`; its derivative at
`τ = 0` is `−𝐃𝓑(nWV) c(η°_{a_j})`. -/
private theorem fderiv_row_eq_zero_szg
    (θ : Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm 0) hid) dIn dOut)
    (hθ : RegularZero (Arch.mlp gelu (rmsNorm 0) hid) θ) (k : Fin L) [DecidableEq (hid k)]
    (η : Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm 0) hid) dIn dOut)
    (hr : ∀ ℓ : Fin L, k.succ ≤ ℓ.castSucc → η.read ℓ = 0)
    (hw : ∀ ℓ : Fin L, k.succ ≤ ℓ.castSucc → η.write ℓ = 0) (hD : η.D = 0)
    (h51 : η.read k * θ.write k + θ.read k * η.write k = 0)
    (n : Matrix T d ℝ) (hn : ∀ t, (n * θ.read k * θ.write k) t ≠ 0) (j : hid k)
    (h : deriv (fun τ : ℝ =>
        blockLHS θ k η
          (n * θ.read k - τ • Matrix.of fun _ : T => (Pi.single j 1 : hid k → ℝ))
          (fun _ _ => 1) (tangentRMS 0 n * θ.read k + n * η.read k)) 0 = 0) :
    fderiv ℝ (fun h' : Matrix T d ℝ => suffix (Arch.mlp gelu (rmsNorm 0) hid) 0 θ k.succ h')
      (n * θ.read k * θ.write k) (Matrix.of fun _ : T => η.write k j) = 0 := by
  set R : Matrix T (hid k) ℝ := Matrix.of fun _ : T => (Pi.single j 1 : hid k → ℝ) with hR
  set X : Matrix T d ℝ := Matrix.of fun _ : T => η.write k j with hX
  set RV : Matrix T d ℝ := Matrix.of fun _ : T => θ.write k j with hRV
  have hRw : R * θ.write k = RV := by
    ext t a
    rw [row_of_mul_szg, Matrix.single_one_vecMul]
    rfl
  have hRe : R * η.write k = X := by
    ext t a
    rw [row_of_mul_szg, Matrix.single_one_vecMul]
    rfl
  -- `ż°(n) = n η°_W` (`Z = 0`)
  have hz : tangentRMS 0 n * θ.read k + n * η.read k = n * η.read k := by
    have h0 : tangentRMS (0 : Matrix d d ℝ) n = 0 := by
      ext t i
      simp only [tangentRMS, Matrix.mul_zero, Matrix.of_apply, Matrix.zero_apply, Pi.sub_apply,
        Pi.smul_apply, smul_eq_mul]
      rw [show ((0 : Matrix T d ℝ) t ⬝ᵥ n t) = 0 from zero_dotProduct _]
      simp
    rw [h0, Matrix.zero_mul, zero_add]
  -- the function of `τ`: `(−τ) G(τ)` with `G(τ) = 𝐃𝓑(nWV − τ c(a_j)) c(η°_{a_j})`
  have hfun : (fun τ : ℝ => blockLHS θ k η (n * θ.read k - τ • R) (fun _ _ => 1)
      (tangentRMS 0 n * θ.read k + n * η.read k))
      = fun τ : ℝ => (-τ) • fderiv ℝ
          (fun h' : Matrix T d ℝ => suffix (Arch.mlp gelu (rmsNorm 0) hid) 0 θ k.succ h')
          (n * θ.read k * θ.write k - τ • RV) X := by
    funext τ
    have hdir : (Matrix.of fun t j => (fun (_ : T) (_ : hid k) => (1 : ℝ)) t j
        * (tangentRMS 0 n * θ.read k + n * η.read k) t j) * θ.write k
        + (n * θ.read k - τ • R) * η.write k = (-τ) • X := by
      have e1 : (Matrix.of fun t j => (fun (_ : T) (_ : hid k) => (1 : ℝ)) t j
          * (tangentRMS 0 n * θ.read k + n * η.read k) t j) = n * η.read k := by
        ext t i
        rw [Matrix.of_apply, one_mul, hz]
      rw [e1, Matrix.sub_mul, Matrix.smul_mul, hRe, Matrix.mul_assoc, Matrix.mul_assoc,
        add_sub_assoc', ← Matrix.mul_add, h51, Matrix.mul_zero, zero_sub, neg_smul]
    have hpos : (n * θ.read k - τ • R) * θ.write k = n * θ.read k * θ.write k - τ • RV := by
      rw [Matrix.sub_mul, Matrix.smul_mul, hRw]
    show fderiv ℝ _ _ _ + _ = _
    rw [hdir, hpos, map_smul, fderiv_param_suffix_eq_zero _ 0 θ η k.succ _ hr hw hD, add_zero]
  -- `G` is continuous at `0`: `𝓑_{>k+1}` is analytic at `nWV` (no zero row)
  have hB := (analyticAt_suffix_prod_zero (Arch.mlp (T := T) (d := d) gelu (rmsNorm 0) hid) θ
    rfl (fun ℓ => analyticOnNhd_f_mlp analyticOnNhd_gelu ℓ) hθ k.succ _ hn).comp
      (f := fun h' : Matrix T d ℝ => (θ, h')) (x := n * θ.read k * θ.write k)
      (analyticAt_const.prod analyticAt_id)
  have hg : AnalyticAt ℝ (fun τ : ℝ => n * θ.read k * θ.write k - τ • RV) 0 :=
    analyticAt_const.sub
      ((ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) RV).analyticAt 0)
  have hB0 : AnalyticAt ℝ
      (fun h' : Matrix T d ℝ => suffix (Arch.mlp gelu (rmsNorm 0) hid) 0 θ k.succ h')
      (n * θ.read k * θ.write k - (0 : ℝ) • RV) := by
    rw [zero_smul, sub_zero]
    exact hB
  have hG := (analyticAt_fderiv_apply_szg hg (analyticAt_const (v := X)) hB0).continuousAt
  have hd := (hasDerivAt_neg_smul_szg hG).deriv
  have e := hd.symm.trans ((congrArg (fun f => deriv f (0 : ℝ)) hfun).symm.trans h)
  rw [zero_smul, sub_zero, neg_eq_zero] at e
  exact e

omit [DecidableEq d] in
/-- Helper: a column `u` with `x ⬝ u = 0` for the rows `x` of a nonempty open set is `0`. -/
private theorem eq_zero_of_dotProduct_szg (N : Set (d → ℝ)) (hN : IsOpen N) (hNne : N.Nonempty)
    (u : d → ℝ) (h : ∀ x ∈ N, x ⬝ᵥ u = 0) : u = 0 := by
  have hM := eq_zero_of_vecMul_eq_zero_of_isOpen (Matrix.of fun a (_ : Unit) => u a) N hN hNne
    fun x hx => funext fun _ => h x hx
  funext a
  exact congrFun (congrFun hM a) ()

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
  classical
  intro Z η h16
  have hf : ∀ ℓ, AnalyticOnNhd ℝ ((Arch.mlp (T := T) (d := d) gelu (rmsNorm 0) hid).f ℓ)
      Set.univ := fun ℓ => analyticOnNhd_f_mlp analyticOnNhd_gelu ℓ
  -- Step 1: `Z'` with (49), and (16) after the block; `(D_{k+1})` gives `Y'`, `β'`
  obtain ⟨Z', h49, h16'⟩ := exists_suffixFlatZero_succ_gelu hθ hd k hP1 hκ hκ1 hhol hP2 Z η h16
  obtain ⟨Y', β', hYa, hZ'eq, hY, hYD⟩ := hk Z' η h16'
  -- Preparation: (P1), and `ξ₀ c_j > 0` for all `j` from (P2)
  obtain ⟨hcne, hVne, hM⟩ := hP1
  obtain ⟨ξ₀, hξ₀, hP2₀⟩ := hP2
  obtain ⟨ζ, hζ, hξ₀ζ⟩ := exists_unit_orth_szg hd ξ₀
  have hpos : ∀ j, 0 < (ξ₀ ᵥ* θ.read k) j := fun j =>
    lt_of_le_of_lt (abs_nonneg _) ((hP2₀ ζ hζ hξ₀ζ).1 j)
  have hneg : ∀ i j : hid k, i ≠ j →
      (fun a : d => θ.read k a i) ≠ fun a : d => -θ.read k a j := by
    intro i j _ h
    have e : (ξ₀ ᵥ* θ.read k) i = -(ξ₀ ᵥ* θ.read k) j := by
      show ξ₀ ⬝ᵥ (fun a => θ.read k a i) = -(ξ₀ ⬝ᵥ fun a => θ.read k a j)
      rw [h]
      exact dotProduct_neg _ _
    linarith [hpos i, hpos j]
  have hc0 : ∀ j, (fun a : d => θ.read k a j) ≠ 0 := fun j h => by
    have e : (ξ₀ ᵥ* θ.read k) j = 0 := by
      show ξ₀ ⬝ᵥ (fun a => θ.read k a j) = 0
      rw [h, dotProduct_zero]
    linarith [hpos j]
  -- the open set `U` of rows around `ξ₀` with (P2), and inside it `N`, `ξ'(x)`, the order `e`
  have hξ₀U : ξ₀ ∈ {x : d → ℝ | x ≠ 0 ∧ ∀ ξ' : d → ℝ, ξ' ⬝ᵥ ξ' = 1 → x ⬝ᵥ ξ' = 0 →
      PathP2 (θ.read k) (θ.write k) κ ((Real.sqrt (x ⬝ᵥ x))⁻¹ • x) ξ'} := by
    refine ⟨fun h => ?_, fun ξ' h1 h2 => ?_⟩
    · rw [h, zero_dotProduct] at hξ₀
      exact zero_ne_one hξ₀
    · rw [hξ₀, Real.sqrt_one, inv_one, one_smul]
      exact hP2₀ ξ' h1 h2
  obtain ⟨N, ξ', e, hNo, hNne, hNU, hN0, hNξ⟩ := exists_isOpen_rates_lt hd (θ.read k) hcne hneg
    _ (isOpen_setOf_pathP2 (θ.read k) (θ.write k) κ) ⟨ξ₀, hξ₀U⟩
  have hpair : ∀ x ∈ N, unitRow_szg x ⬝ᵥ unitRow_szg x = 1 ∧ ξ' x ⬝ᵥ ξ' x = 1 ∧
      unitRow_szg x ⬝ᵥ ξ' x = 0 ∧ PathP2 (θ.read k) (θ.write k) κ (unitRow_szg x) (ξ' x) := by
    intro x hx
    obtain ⟨h1, h2, -⟩ := hNξ x hx
    refine ⟨unitRow_dot_self_szg (dotProduct_self_pos_szg (hN0 x hx)), h1, ?_,
      (hNU hx).2 _ h1 h2⟩
    unfold unitRow_szg
    rw [smul_dotProduct, h2, smul_zero]
  have hrows : ∀ x ∈ N, ∀ t, ((Matrix.of fun _ : T => Real.sqrt (Fintype.card d) • unitRow_szg x)
      * θ.read k * θ.write k) t ≠ 0 := by
    intro x hx t
    rw [Matrix.mul_assoc, row_of_mul_szg]
    refine vecMul_ne_zero_szg hM fun h0 => ?_
    have e := congrArg (fun v => v ⬝ᵥ v) h0
    simp only [smul_dotProduct, dotProduct_smul, (hpair x hx).1, zero_dotProduct, smul_eq_mul,
      mul_one] at e
    have hD : (0 : ℝ) < Fintype.card d := by exact_mod_cast (by omega : 0 < Fintype.card d)
    rw [Real.mul_self_sqrt hD.le] at e
    exact hD.ne' e
  -- `hid k` is not empty (`W V` is invertible)
  have hq : 0 < Fintype.card (hid k) := by
    rw [Fintype.card_pos_iff]
    by_contra hne
    rw [not_nonempty_iff] at hne
    have h0 : θ.read k * θ.write k = 0 := by
      ext a b
      simp only [Matrix.mul_apply, Finset.univ_eq_empty, Finset.sum_empty, Matrix.zero_apply]
    have : Nonempty d := Fintype.card_pos_iff.1 (by omega)
    rw [h0, Matrix.det_zero] at hM
    exact not_isUnit_zero hM
  -- Step 2: the unit `j₁` of smallest rate; `(x⬝x)(x⬝u) = (xZx)(x⬝c_{j₁})` on `N`
  set j₁ : hid k := e.symm ⟨0, hq⟩ with hj₁
  have hj₁lt : ∀ i, i ≠ j₁ → e j₁ < e i := by
    intro i hi
    have h0 : e j₁ = ⟨0, hq⟩ := e.apply_symm_apply _
    have hne : e i ≠ ⟨0, hq⟩ := fun h => hi (by rw [hj₁, ← h, e.symm_apply_apply])
    rw [h0, Fin.lt_def]
    exact Nat.pos_of_ne_zero fun h => hne (Fin.ext h)
  have hstep2 : ∀ x ∈ N, fderiv ℝ
      (fun h' : Matrix T d ℝ => suffix (Arch.mlp gelu (rmsNorm 0) hid) 0 θ k.succ h')
        ((Matrix.of fun _ : T => Real.sqrt (Fintype.card d) • unitRow_szg x) * θ.read k
          * θ.write k)
        (Matrix.of fun t =>
          (tangentRMS Z (Matrix.of fun _ : T => Real.sqrt (Fintype.card d) • unitRow_szg x)
              * θ.read k
            + (Matrix.of fun _ : T => Real.sqrt (Fintype.card d) • unitRow_szg x) * η.read k) t j₁
            • θ.write k j₁) = 0 := by
    intro x hx
    obtain ⟨h1, h2, h3, h4⟩ := hpair x hx
    refine (gelu_path_step_unit θ hθ k hκ hκ1 hhol Z η h16 _ _ h1 h2 h3 h4 ∅ j₁
      (Set.notMem_empty j₁) (fun i _ hi => (hNξ x hx).2.2 j₁ i (hj₁lt i hi))
      fun t ht δ δ' hδ => ?_).2
    -- `A = ∅`: `δ = δ' = 0`, and this is Step 1 on the path
    have e0 : δ = 0 := funext fun i => (hδ i (Set.notMem_empty i)).1
    have e0' : δ' = 0 := funext fun i => (hδ i (Set.notMem_empty i)).2
    subst e0 e0'
    have h := gelu_path_step_zero θ hθ k hκ hκ1 hhol Z η h16 _ _ h1 h2 h3 h4 t ht
    simp only [Pi.zero_apply, sub_zero]
    exact h
  have hquad := quadratic_of_unit_szg hθ hd k hM j₁ (hVne j₁) Z (η.read k) N hNo hN0 hstep2
  obtain ⟨β₀, -, hY₀⟩ := exists_smul_of_quadratic_rows Z _ _ (hc0 j₁) N hNo hNne hquad
  -- Step 3: `Y₀ = Z − β₀ I`, the symmetry `sym`, and `η° = η − sym`
  obtain ⟨Y₀, hY₀def⟩ : ∃ Y₀ : Matrix d d ℝ, Y₀ = Z - β₀ • (1 : Matrix d d ℝ) := ⟨_, rfl⟩
  rw [← hY₀def] at hY₀
  have hZ : Z = Y₀ + β₀ • (1 : Matrix d d ℝ) := by rw [hY₀def, sub_add_cancel]
  obtain ⟨Y, hYdef⟩ : ∃ Y : Fin (L + 1) → Matrix d d ℝ, Y = Function.update Y' k.castSucc Y₀ :=
    ⟨_, rfl⟩
  obtain ⟨β, hβdef⟩ : ∃ β : Fin (L + 1) → ℝ,
      β = Function.update (Function.update β' k.succ (β' k.succ - β₀)) k.castSucc β₀ := ⟨_, rfl⟩
  -- the indices
  have hkk : k.succ ≠ k.castSucc := (Fin.castSucc_lt_succ).ne'
  have hYk : Y k.castSucc = Y₀ := by rw [hYdef, Function.update_self]
  have hβk : β k.castSucc = β₀ := by rw [hβdef, Function.update_self]
  have hYk1 : Y k.succ = Y' k.succ := by rw [hYdef, Function.update_of_ne hkk]
  have hβk1 : β k.succ = β' k.succ - β₀ := by
    rw [hβdef, Function.update_of_ne hkk, Function.update_self]
  have hlater : ∀ ℓ : Fin L, k.succ ≤ ℓ.castSucc →
      Y ℓ.castSucc = Y' ℓ.castSucc ∧ Y ℓ.succ = Y' ℓ.succ ∧ β ℓ.succ = β' ℓ.succ := by
    intro ℓ hℓ
    rw [Fin.le_def, Fin.val_succ, Fin.val_castSucc] at hℓ
    have h1 : ℓ.castSucc ≠ k.castSucc := fun h => by
      have := congrArg Fin.val h
      rw [Fin.val_castSucc, Fin.val_castSucc] at this
      omega
    have h2 : ℓ.succ ≠ k.castSucc := fun h => by
      have := congrArg Fin.val h
      rw [Fin.val_succ, Fin.val_castSucc] at this
      omega
    have h3 : ℓ.succ ≠ k.succ := fun h => by
      have := congrArg Fin.val h
      rw [Fin.val_succ, Fin.val_succ] at this
      omega
    refine ⟨by rw [hYdef, Function.update_of_ne h1], by rw [hYdef, Function.update_of_ne h2], ?_⟩
    rw [hβdef, Function.update_of_ne h2, Function.update_of_ne h3]
  have hYlast : Y (Fin.last L) = Y' (Fin.last L) := by
    rw [hYdef, Function.update_of_ne (Fin.castSucc_lt_last k).ne']
  have hYanti : ∀ ℓ, k.castSucc ≤ ℓ → Y ℓ ∈ antisymmetric d := by
    intro ℓ hℓ
    rcases eq_or_ne ℓ k.castSucc with rfl | hne
    · rw [hYk]
      exact hY₀
    · rw [hYdef, Function.update_of_ne hne]
      refine hYa ℓ ?_
      have hlt : k.castSucc < ℓ := lt_of_le_of_ne hℓ (Ne.symm hne)
      rw [Fin.lt_def, Fin.val_castSucc] at hlt
      rw [Fin.le_def, Fin.val_succ]
      omega
  -- the symmetry satisfies (16) for `k` with `Y_k + β_k I = Z`; so `η° = η − sym` with `0`
  have hsym := suffixFlatZero_cobDir_add_scaleDir (Arch.mlp gelu (rmsNorm 0) hid) θ rfl hf hθ
    k.castSucc Y hYanti β
  rw [hYk, hβk, ← hZ] at hsym
  obtain ⟨ηo, hηo⟩ : ∃ ηo : Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm 0) hid) dIn dOut,
      ηo = η - (cobDir θ Y + scaleDir θ β) := ⟨_, rfl⟩
  have h16o : SuffixFlatZero (Arch.mlp gelu (rmsNorm 0) hid) θ k.castSucc 0 ηo := by
    intro h hh
    have e1 := h16 h hh
    have e2 := hsym h hh
    rw [Matrix.mul_zero, map_zero, zero_add, hηo, map_sub]
    have e3 := congrArg₂ (· - ·) e1 e2
    simp only [sub_zero, add_sub_add_left_eq_sub] at e3
    exact e3
  -- the components of `η°`: zero after the block and at `D`; `η°_W`, `η°_V` at the block
  have hro : ∀ ℓ : Fin L, k.succ ≤ ℓ.castSucc → ηo.read ℓ = 0 := by
    intro ℓ hℓ
    rw [hηo]
    show η.read ℓ - (-(Y ℓ.castSucc * θ.read ℓ) + 0) = 0
    rw [(hlater ℓ hℓ).1, (hY ℓ hℓ).1, add_zero, sub_self]
  have hwo : ∀ ℓ : Fin L, k.succ ≤ ℓ.castSucc → ηo.write ℓ = 0 := by
    intro ℓ hℓ
    rw [hηo]
    show η.write ℓ - (θ.write ℓ * Y ℓ.succ + β ℓ.succ • θ.write ℓ) = 0
    rw [(hlater ℓ hℓ).2.1, (hlater ℓ hℓ).2.2, (hY ℓ hℓ).2, Matrix.mul_add, Matrix.mul_smul,
      Matrix.mul_one, sub_self]
  have hDo : ηo.D = 0 := by
    rw [hηo]
    show η.D - (-(Y (Fin.last L) * θ.D) + 0) = 0
    rw [hYlast, hYD, add_zero, sub_self]
  have hηW : ηo.read k = η.read k + Y₀ * θ.read k := by
    rw [hηo]
    show η.read k - (-(Y k.castSucc * θ.read k) + 0) = _
    rw [hYk, add_zero, sub_neg_eq_add]
  have hηV : ηo.write k
      = η.write k - (θ.write k * Y' k.succ + (β' k.succ - β₀) • θ.write k) := by
    rw [hηo]
    show η.write k - (θ.write k * Y k.succ + β k.succ • θ.write k) = _
    rw [hYk1, hβk1]
  -- (51): `η°_W V + W η°_V = 0`, from (49), `Z' = Y_{k+1} + β' I` and `Z = Y₀ + β₀ I`
  have h51 : ηo.read k * θ.write k + θ.read k * ηo.write k = 0 := by
    have e := h49
    rw [hZ'eq, hZ] at e
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one] at e
    rw [hηW, hηV, Matrix.add_mul, Matrix.mul_sub, Matrix.mul_add, Matrix.mul_smul,
      ← Matrix.mul_assoc (θ.read k) (θ.write k) (Y' k.succ), Matrix.mul_assoc Y₀ (θ.read k)]
    generalize θ.read k * θ.write k = P at e ⊢
    generalize η.read k * θ.write k = a at e ⊢
    generalize θ.read k * η.write k = b at e ⊢
    have e' : a + b = P * Y' k.succ + β' k.succ • P - Y₀ * P - β₀ • P := by
      rw [← e]
      abel
    calc a + Y₀ * P + (b - (P * Y' k.succ + (β' k.succ - β₀) • P))
        = (a + b) + Y₀ * P - P * Y' k.succ - (β' k.succ - β₀) • P := by abel
      _ = 0 := by rw [e']; module
  -- Step 4: by induction along the order `e` of the rates, column `j` of `η°_W` and row `j` of
  -- `η°_V` vanish
  have hstep4 : ∀ m : ℕ, m ≤ Fintype.card (hid k) → ∀ i : hid k, (e i : ℕ) < m →
      (∀ a, ηo.read k a i = 0) ∧ ηo.write k i = 0 := by
    intro m
    induction m with
    | zero => exact fun _ i hi => absurd hi (Nat.not_lt_zero _)
    | succ m ih =>
      intro hm
      have IH := ih (Nat.le_of_succ_le hm)
      -- the unit `j` with `e j = m`, and `A = {j' | e j' < e j}`
      obtain ⟨j, hj⟩ : ∃ j : hid k, (e j : ℕ) = m :=
        ⟨e.symm ⟨m, hm⟩, by rw [e.apply_symm_apply]⟩
      have hAj : ∀ i ∈ {i' : hid k | e i' < e j},
          (∀ a, ηo.read k a i = 0) ∧ ηo.write k i = 0 :=
        fun i hi => IH i (by rw [← hj]; exact Fin.lt_def.1 hi)
      -- the path step at `(x̂, ξ'(x))` for `x ∈ N`, with `Z = 0`, `η°`, `A` and `j`
      have hres := fun (x : d → ℝ) (hx : x ∈ N) =>
        gelu_path_step_unit θ hθ k hκ hκ1 hhol 0 ηo h16o (unitRow_szg x) (ξ' x) (hpair x hx).1
          (hpair x hx).2.1 (hpair x hx).2.2.1 (hpair x hx).2.2.2 {i' | e i' < e j} j
          (lt_irrefl (e j))
          (fun i hiA hij => (hNξ x hx).2.2 j i
            (lt_of_le_of_ne (not_lt.1 hiA) fun h => hij (e.injective h).symm))
          (fun _ _ δ δ' hδ => blockLHSC_eq_zero_szg θ k ηo hro hwo hDo h51 _ hAj _ δ δ' hδ)
      -- `𝓛°'_j(1) = 0`: `x η°_{c_j} = 0` on `N`, so the column vanishes
      have hquad := quadratic_of_unit_szg hθ hd k hM j (hVne j) 0 (ηo.read k) N hNo hN0
        fun x hx => (hres x hx).2
      have hu := eq_zero_of_dotProduct_szg N hNo hNne _ fun x hx => by
        have e' := hquad x hx
        rw [Matrix.vecMul_zero, zero_dotProduct, zero_mul] at e'
        exact (mul_eq_zero.1 e').resolve_left (dotProduct_self_pos_szg (hN0 x hx)).ne'
      have hcol : ∀ a, ηo.read k a j = 0 := fun a => by
        have e' := congrFun hu a
        simp only [Matrix.zero_mul, zero_add, Pi.zero_apply] at e'
        exact e'
      -- `𝓛°_j(1) = 0`: `𝐃𝓑(n W V) c(η°_{a_j}) = 0` on `N`, so the row vanishes
      have hrow : ηo.write k j = 0 :=
        tool_one_szg hθ hd k hM N hNo hNne hN0 _ fun x hx =>
          fderiv_row_eq_zero_szg θ hθ k ηo hro hwo hDo h51 _ (hrows x hx) j (hres x hx).1
      intro i hi
      rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.1 hi) with hlt | heq
      · exact IH i hlt
      · obtain rfl : i = j := e.injective (Fin.ext (heq.trans hj.symm))
        exact ⟨hcol, hrow⟩
  have hW0 : ηo.read k = 0 := by
    ext a i
    exact (hstep4 _ le_rfl i (e i).isLt).1 a
  have hV0 : ηo.write k = 0 := by
    ext i a
    rw [(hstep4 _ le_rfl i (e i).isLt).2]
    rfl
  -- Conclusion: `(D_k)` with `Y`, `β`
  refine ⟨Y, β, hYanti, by rw [hYk, hβk]; exact hZ, fun ℓ hℓ => ?_, by rw [hYlast]; exact hYD⟩
  rcases eq_or_ne ℓ k with rfl | hne
  · -- the block itself: `η°_W = 0` and `η°_V = 0`
    rw [hW0] at hηW
    rw [hV0] at hηV
    refine ⟨?_, ?_⟩
    · rw [hYk]
      exact eq_neg_of_add_eq_zero_left hηW.symm
    · rw [hYk1, hβk1, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one]
      exact sub_eq_zero.1 hηV.symm
  · -- a later block: `(D_{k+1})`
    have hlt : k < ℓ := lt_of_le_of_ne (Fin.castSucc_le_castSucc_iff.1 hℓ) (Ne.symm hne)
    have hle : k.succ ≤ ℓ.castSucc := by
      rw [Fin.le_def, Fin.val_succ, Fin.val_castSucc]
      exact hlt
    obtain ⟨h1, h2, h3⟩ := hlater ℓ hle
    rw [h1, h2, h3]
    exact hY ℓ hle

end Skips
