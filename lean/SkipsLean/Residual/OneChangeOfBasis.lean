import SkipsLean.Residual.LearnedSkips
import SkipsLean.Basic.RMSNormConverse

/-!
# Identity skips leave one change of basis; learned skips under pre-RMSNorm

Paper: "Skip Connections Unlock at Least d_model² Parameters per Layer", Section 3.

* Theorem 3.3 (i), "only if" (Theorem A.5 (iii) in the appendix): if the changes of basis
  `G_0, …, G_L` at the hidden states preserve the function of every residual network, that is, for
  all values of the parameters, then `G_0 = G_1 = ⋯ = G_L`, and under pre-RMSNorm this matrix is
  orthogonal. The paper assumes that every block is nonzero for some value of its parameters.
  The proof sets all writes but one to zero: the output then compares the bases on the two sides
  of that block.
* Theorem 3.2 (ii), second sentence: under pre-RMSNorm, orthogonal changes of basis
  `Q_1, …, Q_L`, with `Q_0 = I`, turn every learned skip `A_ℓ` into an upper triangular matrix
  `Q_{ℓ-1}ᵀ A_ℓ Q_ℓ` and preserve the function. (The paper assumes the `A_ℓ` invertible; the
  factorization exists for every square matrix.)

"Every residual network" is: every value `θ` of the parameters of a fixed architecture `A`, with
the stream matrices `1` (identity skips).
-/

namespace Skips

open Matrix

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype d] [DecidableEq d] [Fintype dIn]
variable {A : Arch T d L}

/-! ### Helpers on matrices -/

/-- Helper: `a⁻¹ (a B) = B` also for a rectangular `B`. -/
private theorem cob_inv_mul_mul {n : Type*} (a : GL d ℝ) (B : Matrix d n ℝ) :
    (↑a⁻¹ : Matrix d d ℝ) * ((a : Matrix d d ℝ) * B) = B := by
  rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]

/-- Helper: `a (a⁻¹ B) = B` also for a rectangular `B`. -/
private theorem cob_mul_inv_mul {n : Type*} (a : GL d ℝ) (B : Matrix d n ℝ) :
    (a : Matrix d d ℝ) * ((↑a⁻¹ : Matrix d d ℝ) * B) = B := by
  rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]

omit [DecidableEq d] in
/-- Helper: two hidden states with the same output for every readout `D` are equal. -/
private theorem eq_of_forall_mul_right [Nonempty dOut] {X Y : Matrix T d ℝ}
    (h : ∀ D : Matrix d dOut ℝ, X * D = Y * D) : X = Y := by
  classical
  obtain ⟨o⟩ := ‹Nonempty dOut›
  ext t k
  -- the readout `e_k e_oᵀ` reads off the column `k`
  have := congrFun (congrFun (h (Matrix.single k o 1)) t) o
  simpa only [mul_single_apply_same, mul_one] using this

omit [DecidableEq d] in
/-- Helper: if `b ≠ 0` and `b V P = b V P'` for every `V`, then `P = P'`. -/
private theorem eq_of_forall_mul_mul {w : Type*} [Fintype w] (b : Matrix T w ℝ) (hb : b ≠ 0)
    {P P' : Matrix d d ℝ} (h : ∀ V : Matrix w d ℝ, b * V * P = b * V * P') : P = P' := by
  classical
  -- an entry `b t i ≠ 0`
  obtain ⟨t, i, hti⟩ : ∃ t i, b t i ≠ 0 := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    exact hb (Matrix.ext hcon)
  ext k k'
  -- `V = e_i e_kᵀ`: the entry `(t, k')` of `b V P` is `b t i * P k k'`
  have := congrFun (congrFun (h (Matrix.single i k 1)) t) k'
  simp only [Matrix.mul_apply, Matrix.single_apply, ite_and, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, ite_mul, zero_mul, mul_eq_mul_left_iff] at this
  exact this.resolve_right hti

/-! ### Hidden states when all writes but one vanish -/

/-- Helper: in a residual network whose writes are all zero, every hidden state is `x E`. -/
private theorem hidden_of_write_eq_zero (θ : Params A dIn dOut) (x : Matrix T dIn ℝ)
    (hw : ∀ k, θ.write k = 0) (j : Fin (L + 1)) : hidden A 1 θ x j = x * θ.E := by
  induction j using Fin.induction with
  | zero => exact hidden_zero A 1 θ x
  | succ k ih =>
    rw [hidden_succ, ih, hw k, Matrix.mul_zero, add_zero, Pi.one_apply, Matrix.mul_one]

/-- Helper: in a residual network whose writes vanish except that of block `ℓ₀`, the hidden
states are `x E` up to block `ℓ₀` and `x E + f_ℓ₀(χ(x E) W_read^ℓ₀) W_write^ℓ₀` after it. -/
private theorem hidden_single_write (θ : Params A dIn dOut) (x : Matrix T dIn ℝ) (ℓ₀ : Fin L)
    (hw : ∀ k, k ≠ ℓ₀ → θ.write k = 0) (j : Fin (L + 1)) :
    hidden A 1 θ x j = if (j : ℕ) ≤ ℓ₀ then x * θ.E
      else x * θ.E + A.f ℓ₀ (A.χ (x * θ.E) * θ.read ℓ₀) * θ.write ℓ₀ := by
  induction j using Fin.induction with
  | zero => simp only [hidden_zero, Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_le, ↓reduceIte]
  | succ k ih =>
    rw [hidden_succ, ih, Pi.one_apply, Matrix.mul_one]
    by_cases hk : k = ℓ₀
    · -- block `ℓ₀` itself: its input is `x E`
      subst hk
      simp only [Fin.val_castSucc, Std.le_refl, ↓reduceIte, Fin.val_succ, add_le_iff_nonpos_right,
        nonpos_iff_eq_zero, one_ne_zero]
    · -- another block writes nothing
      rw [hw k hk, Matrix.mul_zero, add_zero]
      have e : (k : ℕ) ≠ ℓ₀ := fun e => hk (Fin.ext e)
      have e1 : ((k.castSucc : Fin (L + 1)) : ℕ) = k := Fin.val_castSucc k
      have e2 : ((k.succ : Fin (L + 1)) : ℕ) = k + 1 := Fin.val_succ k
      split_ifs <;> first | rfl | (exfalso; omega)

/-- Helper: the last hidden state when all writes but that of block `ℓ₀` vanish. -/
private theorem hidden_last_single_write (θ : Params A dIn dOut) (x : Matrix T dIn ℝ) (ℓ₀ : Fin L)
    (hw : ∀ k, k ≠ ℓ₀ → θ.write k = 0) :
    hidden A 1 θ x (Fin.last L) =
      x * θ.E + A.f ℓ₀ (A.χ (x * θ.E) * θ.read ℓ₀) * θ.write ℓ₀ := by
  rw [hidden_single_write θ x ℓ₀ hw, Fin.val_last]
  exact ite_eq_right (not_le.mpr ℓ₀.isLt)

/-! ### The theorems without normalization -/

/-- **Theorem 3.3 (i), "only if", without normalization.** If every block is nonzero for some
value of its parameters, and the changes of basis `G_0, …, G_L` preserve the function of the
residual network for all values of the parameters, then all `G_ℓ` are equal. -/
theorem cob_eq_of_eval_cob_residual [Nonempty T] [Nonempty dIn] [Nonempty dOut]
    (hA : A.χ = id)
    (hne : ∀ ℓ, ∃ (x : Matrix T dIn ℝ) (E : Matrix dIn d ℝ) (W : Matrix d (A.r ℓ) ℝ),
      A.f ℓ (x * E * W) ≠ 0)
    (G : Fin (L + 1) → GL d ℝ)
    (h : ∀ (θ : Params A dIn dOut) (x : Matrix T dIn ℝ),
      eval A 1 (θ.cob G G) x = eval A 1 θ x) :
    ∀ ℓ, G ℓ = G 0 := by
  classical
  obtain ⟨t⟩ := ‹Nonempty T›
  obtain ⟨i⟩ := ‹Nonempty dIn›
  -- (a) With all writes zero the outputs are `x E G_0 G_L⁻¹ D` and `x E D`, so `G_L = G_0`.
  have hL : G (Fin.last L) = G 0 := by
    apply Units.ext
    refine eq_of_forall_mul_mul (Matrix.single t i (1 : ℝ)) (fun h0 => ?_) fun E => ?_
    · have := congrFun (congrFun h0 t) i
      simp only [Matrix.single_apply_same, Matrix.zero_apply, one_ne_zero] at this
    refine eq_of_forall_mul_right (dOut := dOut) fun D => ?_
    -- the readout `G_L D`
    let θ : Params A dIn dOut := ⟨E, 0, 0, (G (Fin.last L) : Matrix d d ℝ) * D⟩
    have hw : ∀ k, θ.write k = 0 := fun _ => rfl
    have hw' : ∀ k, (θ.cob G G).write k = 0 := fun _ => Matrix.zero_mul _
    have he := h θ (Matrix.single t i 1)
    rw [eval, eval, hidden_of_write_eq_zero _ _ hw', hidden_of_write_eq_zero θ _ hw] at he
    simp only [θ, Params.cob, hA, id_eq, cob_inv_mul_mul, Matrix.mul_assoc] at he ⊢
    exact he.symm
  -- (b) Induction over the blocks: if `G_{ℓ-1} = G_0`, the block `ℓ` alone gives `G_ℓ = G_0`.
  intro ℓ
  induction ℓ using Fin.induction with
  | zero => rfl
  | succ k ih =>
    obtain ⟨x, E, W, hf⟩ := hne k
    apply Units.ext
    refine eq_of_forall_mul_mul _ hf fun V => ?_
    refine eq_of_forall_mul_right (dOut := dOut) fun D => ?_
    -- only block `k` writes, with the read `W` and the write `V`; the readout is `G_L D`
    let θ : Params A dIn dOut :=
      ⟨E, Pi.single k W, Pi.single k V, (G (Fin.last L) : Matrix d d ℝ) * D⟩
    have hw : ∀ j, j ≠ k → θ.write j = 0 := fun j hj =>
      Pi.single_eq_of_ne (M := fun ℓ => Matrix (A.w ℓ) d ℝ) hj V
    have hw' : ∀ j, j ≠ k → (θ.cob G G).write j = 0 := fun j hj => by
      show θ.write j * _ = 0
      rw [hw j hj, Matrix.zero_mul]
    have he := h θ x
    rw [eval, eval, hidden_last_single_write _ x k hw', hidden_last_single_write θ x k hw] at he
    simp only [θ, Params.cob, hA, id_eq, Pi.single_eq_same, ih, hL, cob_inv_mul_mul] at he
    -- the block reads `x E G_0 G_0⁻¹ W = x E W`
    have key : x * (E * (G 0 : Matrix d d ℝ)) * ((↑(G 0)⁻¹ : Matrix d d ℝ) * W) = x * E * W := by
      simp only [Matrix.mul_assoc, cob_mul_inv_mul]
    rw [key, Matrix.add_mul, Matrix.add_mul] at he
    simp only [Matrix.mul_assoc] at he ⊢
    exact add_left_cancel he

/-- **Theorem 3.3 (i), without normalization:** the changes of basis `G_0, …, G_L` preserve the
function of every residual network if and only if they are all equal. -/
theorem eval_cob_residual_iff [Nonempty T] [Nonempty dIn] [Nonempty dOut]
    (hA : A.χ = id)
    (hne : ∀ ℓ, ∃ (x : Matrix T dIn ℝ) (E : Matrix dIn d ℝ) (W : Matrix d (A.r ℓ) ℝ),
      A.f ℓ (x * E * W) ≠ 0)
    (G : Fin (L + 1) → GL d ℝ) :
    (∀ (θ : Params A dIn dOut) (x : Matrix T dIn ℝ), eval A 1 (θ.cob G G) x = eval A 1 θ x)
      ↔ ∀ ℓ, G ℓ = G 0 := by
  refine ⟨cob_eq_of_eval_cob_residual hA hne G, fun hG θ x => ?_⟩
  -- all `G_ℓ` equal `G_0`: one change of basis at all hidden states
  have hfun : G = fun _ => G 0 := funext hG
  rw [hfun]
  exact eval_cob_residual θ x hA (G 0)

/-! ### RMSNorm is injective for `ε > 0` -/

omit [DecidableEq d] in
/-- Helper: for `ε > 0`, RMSNorm on a row is injective. -/
private theorem rmsRow_inj {ε : ℝ} (hε : 0 < ε) {u v : d → ℝ}
    (h : rmsRow ε u = rmsRow ε v) : u = v := by
  unfold rmsRow at h
  have hn : (0 : ℝ) ≤ Fintype.card d := Nat.cast_nonneg _
  have hp : 0 ≤ u ⬝ᵥ u := Finset.sum_nonneg fun i _ => mul_self_nonneg (u i)
  have hq : 0 ≤ v ⬝ᵥ v := Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)
  have ha : 0 < u ⬝ᵥ u / (Fintype.card d : ℝ) + ε := add_pos_of_nonneg_of_pos (div_nonneg hp hn) hε
  have hb : 0 < v ⬝ᵥ v / (Fintype.card d : ℝ) + ε := add_pos_of_nonneg_of_pos (div_nonneg hq hn) hε
  -- the squared norms of the two sides: `p / (p / n + ε) = q / (q / n + ε)`
  have h2 := congrArg (fun w => w ⬝ᵥ w) h
  simp only [smul_dotProduct, dotProduct_smul, smul_eq_mul, ← mul_assoc, ← mul_inv,
    Real.mul_self_sqrt ha.le, Real.mul_self_sqrt hb.le] at h2
  rw [inv_mul_eq_div, inv_mul_eq_div, div_eq_div_iff ha.ne' hb.ne'] at h2
  -- hence `(p - q) ε = 0`, so `p = q`
  have hpq : u ⬝ᵥ u = v ⬝ᵥ v := by
    have h3 : (u ⬝ᵥ u - v ⬝ᵥ v) * ε = 0 := by linear_combination h2
    have := (mul_eq_zero.mp h3).resolve_right hε.ne'
    linarith
  -- equal norms, equal scalar factors
  rw [hpq] at h
  exact (smul_right_inj (inv_ne_zero (Real.sqrt_pos.mpr hb).ne')).mp h

omit [DecidableEq d] in
/-- Helper: for `ε > 0`, RMSNorm on a hidden state is injective. -/
private theorem rmsNorm_inj {ε : ℝ} (hε : 0 < ε) {X Y : Matrix T d ℝ}
    (h : rmsNorm ε X = rmsNorm ε Y) : X = Y :=
  Matrix.ext fun t k => congrFun (rmsRow_inj (u := X t) (v := Y t) hε (congrFun h t)) k

/-! ### The theorems under pre-RMSNorm -/

/-- **Theorem 3.3 (i), "only if", under pre-RMSNorm (`ε > 0`).** If every block is nonzero for
some value of its parameters, and the changes of basis `G_0, …, G_L` preserve the function of the
residual network for all values of the parameters, then all `G_ℓ` are equal and orthogonal. -/
theorem cob_eq_orthogonal_of_eval_cob_residual_rmsNorm [Nonempty T] [Nonempty dIn]
    [Nonempty dOut] {ε : ℝ} (hε : 0 < ε) (hA : A.χ = rmsNorm ε)
    (hne : ∀ ℓ, ∃ (x : Matrix T dIn ℝ) (E : Matrix dIn d ℝ) (W : Matrix d (A.r ℓ) ℝ),
      A.f ℓ (rmsNorm ε (x * E) * W) ≠ 0)
    (G : Fin (L + 1) → GL d ℝ)
    (h : ∀ (θ : Params A dIn dOut) (x : Matrix T dIn ℝ),
      eval A 1 (θ.cob G G) x = eval A 1 θ x) :
    (∀ ℓ, G ℓ = G 0) ∧ (G 0 : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ := by
  classical
  obtain ⟨t⟩ := ‹Nonempty T›
  obtain ⟨i⟩ := ‹Nonempty dIn›
  -- (a) With all writes zero: `N(v G_0) = N(v) G_L` for every row `v`.
  have hrow : ∀ v : d → ℝ, v ≠ 0 →
      rmsRow ε (v ᵥ* (G 0 : Matrix d d ℝ)) = rmsRow ε v ᵥ* (G (Fin.last L) : Matrix d d ℝ) := by
    intro v _
    -- an input whose hidden state `x E` has the row `v`
    let x : Matrix T dIn ℝ := Matrix.of fun _ => Pi.single i 1
    let E : Matrix dIn d ℝ := Matrix.of fun _ => v
    have hxE : (x * E) t = v := by
      funext k
      simp only [Matrix.mul_apply, Matrix.of_apply, Pi.single_apply, ite_mul, one_mul, zero_mul,
        Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, x, E]
    have hmat : rmsNorm ε (x * E * (G 0 : Matrix d d ℝ))
        = rmsNorm ε (x * E) * (G (Fin.last L) : Matrix d d ℝ) := by
      refine eq_of_forall_mul_right (dOut := dOut) fun D => ?_
      let θ : Params A dIn dOut := ⟨E, 0, 0, (G (Fin.last L) : Matrix d d ℝ) * D⟩
      have hw : ∀ k, θ.write k = 0 := fun _ => rfl
      have hw' : ∀ k, (θ.cob G G).write k = 0 := fun _ => Matrix.zero_mul _
      have he := h θ x
      rw [eval, eval, hidden_of_write_eq_zero _ x hw', hidden_of_write_eq_zero θ x hw] at he
      simp only [θ, Params.cob, hA, cob_inv_mul_mul] at he
      rw [Matrix.mul_assoc x E, he, Matrix.mul_assoc]
    have hr := congrFun hmat t
    change rmsRow ε ((x * E) t ᵥ* (G 0 : Matrix d d ℝ))
      = rmsRow ε ((x * E) t) ᵥ* (G (Fin.last L) : Matrix d d ℝ) at hr
    rwa [hxE] at hr
  -- Lemma A.1, "only if": `G_0` is orthogonal and `G_L = G_0`.
  obtain ⟨horth, hLm⟩ := orthogonal_of_rmsRow_vecMul hε (G 0) _ hrow
  have hL : G (Fin.last L) = G 0 := Units.ext hLm
  refine ⟨fun ℓ => ?_, horth⟩
  -- (b) Induction over the blocks, as without normalization.
  induction ℓ using Fin.induction with
  | zero => rfl
  | succ k ih =>
    obtain ⟨x, E, W, hf⟩ := hne k
    apply Units.ext
    refine eq_of_forall_mul_mul _ hf fun V => ?_
    -- `N(x E G_0 + b G_ℓ) = N((x E + b) G_0)`, with `b = f(N(x E) W) V`
    have hmat : rmsNorm ε (x * E * (G 0 : Matrix d d ℝ)
          + A.f k (rmsNorm ε (x * E) * W) * V * (G k.succ : Matrix d d ℝ))
        = rmsNorm ε ((x * E + A.f k (rmsNorm ε (x * E) * W) * V) * (G 0 : Matrix d d ℝ)) := by
      rw [rmsNorm_mul_orthogonal ε horth]
      refine eq_of_forall_mul_right (dOut := dOut) fun D => ?_
      let θ : Params A dIn dOut :=
        ⟨E, Pi.single k W, Pi.single k V, (G (Fin.last L) : Matrix d d ℝ) * D⟩
      have hw : ∀ j, j ≠ k → θ.write j = 0 := fun j hj =>
        Pi.single_eq_of_ne (M := fun ℓ => Matrix (A.w ℓ) d ℝ) hj V
      have hw' : ∀ j, j ≠ k → (θ.cob G G).write j = 0 := fun j hj => by
        show θ.write j * _ = 0
        rw [hw j hj, Matrix.zero_mul]
      have he := h θ x
      rw [eval, eval, hidden_last_single_write _ x k hw', hidden_last_single_write θ x k hw] at he
      simp only [θ, Params.cob, hA, Pi.single_eq_same, ih, hL, cob_inv_mul_mul] at he
      -- the block reads `N(x E G_0) G_0⁻¹ W = N(x E) W`
      rw [← Matrix.mul_assoc x E, rmsNorm_mul_orthogonal ε horth,
        Matrix.mul_assoc (rmsNorm ε (x * E)), cob_mul_inv_mul] at he
      simpa only [Matrix.mul_assoc] using he
    -- `N` is injective for `ε > 0`
    have hinj := rmsNorm_inj hε hmat
    rw [Matrix.add_mul] at hinj
    exact add_left_cancel hinj

/-- **Theorem 3.3 (i), under pre-RMSNorm (`ε > 0`):** the changes of basis `G_0, …, G_L` preserve
the function of every residual network if and only if they are all equal and orthogonal. -/
theorem eval_cob_residual_rmsNorm_iff [Nonempty T] [Nonempty dIn] [Nonempty dOut] {ε : ℝ}
    (hε : 0 < ε) (hA : A.χ = rmsNorm ε)
    (hne : ∀ ℓ, ∃ (x : Matrix T dIn ℝ) (E : Matrix dIn d ℝ) (W : Matrix d (A.r ℓ) ℝ),
      A.f ℓ (rmsNorm ε (x * E) * W) ≠ 0)
    (G : Fin (L + 1) → GL d ℝ) :
    (∀ (θ : Params A dIn dOut) (x : Matrix T dIn ℝ), eval A 1 (θ.cob G G) x = eval A 1 θ x)
      ↔ (∀ ℓ, G ℓ = G 0) ∧ (G 0 : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ := by
  refine ⟨cob_eq_orthogonal_of_eval_cob_residual_rmsNorm hε hA hne G,
    fun ⟨hG, horth⟩ θ x => ?_⟩
  -- all `G_ℓ` equal the orthogonal `G_0`: one orthogonal change of basis at all hidden states
  have hfun : G = fun _ => G 0 := funext hG
  rw [hfun]
  exact eval_cob_residual_rmsNorm θ x ε hA (G 0) horth

/-! ### Learned skips under pre-RMSNorm -/

/-- A square real matrix times a suitable orthogonal matrix is upper triangular (the RQ
factorization `M = R Qᵀ`). -/
theorem exists_orthogonal_mul_upperTriangular [LinearOrder d] (M : Matrix d d ℝ) :
    ∃ Q : Matrix d d ℝ, Q ∈ Matrix.orthogonalGroup d ℝ ∧ (M * Q).BlockTriangular id := by
  -- QR factorization of `Mᵀ` for the reversed order of `d`
  obtain ⟨Q, hQ, htri⟩ :=
    exists_orthogonal_transpose_mul_upperTriangular (d := dᵒᵈ) (Mᵀ : Matrix dᵒᵈ dᵒᵈ ℝ)
  let Q' : Matrix d d ℝ := Q
  refine ⟨Q', hQ, fun i j hij => ?_⟩
  -- `(M Q) i j = (Qᵀ Mᵀ) j i`, which vanishes for `j < i`
  have h0 : (Q'ᵀ * Mᵀ) j i = 0 := htri (OrderDual.toDual_lt_toDual.mpr hij)
  rw [← Matrix.transpose_mul] at h0
  exact h0

/-- **Theorem 3.2 (ii), second sentence.** Under pre-RMSNorm, for learned skips `A_ℓ` (the stream
matrices `S ℓ`), there are orthogonal `Q_0 = I, Q_1, …, Q_L` such that every
`Q_{ℓ-1}ᵀ A_ℓ Q_ℓ` is upper triangular, and the network with these skips, the reads
`Q_{ℓ-1}ᵀ W_read^ℓ`, the writes `W_write^ℓ Q_ℓ` and the readout `Q_Lᵀ D` computes the same
function. -/
theorem exists_cob_learned_upperTriangular [LinearOrder d] (ε : ℝ) (hA : A.χ = rmsNorm ε)
    (S : Fin L → Matrix d d ℝ) (θ : Params A dIn dOut) :
    ∃ Q : Fin (L + 1) → GL d ℝ, Q 0 = 1 ∧
      (∀ ℓ, (Q ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ) ∧
      (∀ ℓ, (cobSkip S Q ℓ).BlockTriangular id) ∧
      ∀ x : Matrix T dIn ℝ, eval A (cobSkip S Q) (θ.cob Q Q) x = eval A S θ x := by
  -- one step: for `P` and `M` an orthogonal `R` with `P⁻¹ M R` upper triangular (RQ of `P⁻¹ M`)
  have step : ∀ (P : GL d ℝ) (M : Matrix d d ℝ), ∃ R : GL d ℝ,
      (R : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ ∧
      ((↑P⁻¹ : Matrix d d ℝ) * M * (R : Matrix d d ℝ)).BlockTriangular id := by
    intro P M
    obtain ⟨R, hR, htri⟩ := exists_orthogonal_mul_upperTriangular ((↑P⁻¹ : Matrix d d ℝ) * M)
    -- `R` is invertible, with inverse `Rᵀ`
    exact ⟨⟨R, Rᵀ, (Matrix.mem_orthogonalGroup_iff d ℝ).mp hR,
      (Matrix.mem_orthogonalGroup_iff' d ℝ).mp hR⟩, hR, htri⟩
  choose R hR htri using step
  -- `Q_0 = I` and `Q_ℓ = R(Q_{ℓ-1}, A_ℓ)`
  obtain ⟨Q, hQ0, hQs⟩ : ∃ Q : Fin (L + 1) → GL d ℝ,
      Q 0 = 1 ∧ ∀ ℓ : Fin L, Q ℓ.succ = R (Q ℓ.castSucc) (S ℓ) :=
    ⟨Fin.induction (motive := fun _ => GL d ℝ) 1 fun ℓ P => R P (S ℓ), Fin.induction_zero _ _,
      fun ℓ => Fin.induction_succ _ _ ℓ⟩
  -- every `Q_ℓ` is orthogonal
  have hQ : ∀ ℓ, (Q ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ := by
    intro ℓ
    induction ℓ using Fin.induction with
    | zero => rw [hQ0, Units.val_one]; exact one_mem _
    | succ ℓ _ => rw [hQs]; exact hR _ _
  refine ⟨Q, hQ0, hQ, fun ℓ => ?_, fun x => ?_⟩
  · -- `Q_{ℓ-1}⁻¹ A_ℓ Q_ℓ` is upper triangular by the choice of `Q_ℓ`
    change ((↑(Q ℓ.castSucc)⁻¹ : Matrix d d ℝ) * S ℓ * (Q ℓ.succ : Matrix d d ℝ)).BlockTriangular id
    rw [hQs]
    exact htri _ _
  · -- pre-RMSNorm commutes with every orthogonal `Q_ℓ` (Lemma A.1); then Proposition 3.2
    have hχ : ∀ ℓ (h : Matrix T d ℝ),
        A.χ (h * (Q ℓ : Matrix d d ℝ)) = A.χ h * (Q ℓ : Matrix d d ℝ) := by
      intro ℓ h
      rw [hA]
      exact rmsNorm_mul_orthogonal ε (hQ ℓ) h
    exact eval_cob S θ Q Q x hχ

end Skips
