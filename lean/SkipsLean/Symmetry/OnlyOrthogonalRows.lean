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

/-! ### Helpers: hidden states (copies of private helpers of `Symmetry/OnlyOrthogonal.lean`) -/

omit [Fintype T] [DecidableEq d] [Fintype dOut] in
/-- Helper (copy of `hidden_congr`): a hidden state depends only on the embedding and on the
blocks before it. -/
private theorem hidden_congr_oor {A : Arch T d L} {M : Fin L → Matrix d d ℝ}
    (θ θ' : Params A dIn dOut) (x : Matrix T dIn ℝ) (hE : θ.E = θ'.E) (ℓ : Fin (L + 1))
    (hr : ∀ j : Fin L, (j : ℕ) < ℓ → θ.read j = θ'.read j)
    (hw : ∀ j : Fin L, (j : ℕ) < ℓ → θ.write j = θ'.write j) :
    hidden A M θ x ℓ = hidden A M θ' x ℓ := by
  induction ℓ using Fin.induction with
  | zero => rw [hidden_zero, hidden_zero, hE]
  | succ i ih =>
    have hi : (i : ℕ) < (i.succ : ℕ) := by rw [Fin.val_succ]; omega
    have hlt : ∀ j : Fin L, (j : ℕ) < (i.castSucc : ℕ) → (j : ℕ) < (i.succ : ℕ) := by
      intro j hj
      rw [Fin.val_castSucc] at hj
      rw [Fin.val_succ]
      omega
    rw [hidden_succ, hidden_succ, ih (fun j hj => hr j (hlt j hj)) (fun j hj => hw j (hlt j hj)),
      hr i hi, hw i hi]

omit [Fintype T] [DecidableEq d] [Fintype dOut] in
/-- Helper (copy): without skips, `h_{k+1} = f_k(χ(h_k) W_read^k) W_write^k`. -/
private theorem hidden_succ_skipless_oor {A : Arch T d L} (θ : Params A dIn dOut)
    (x : Matrix T dIn ℝ) (k : Fin L) :
    hidden A 0 θ x k.succ = A.f k (A.χ (hidden A 0 θ x k.castSucc) * θ.read k) * θ.write k := by
  rw [hidden_succ, Pi.zero_apply, Matrix.mul_zero, zero_add]

omit [Fintype T] [DecidableEq d] [Fintype dOut] in
/-- Helper (copy): a block `j < k` is not the block `k`. -/
private theorem ne_of_lt_castSucc_oor {j k : Fin L} (hj : (j : ℕ) < (k.castSucc : ℕ)) : j ≠ k :=
  fun e => by rw [e, Fin.val_castSucc] at hj; exact lt_irrefl _ hj

omit [Fintype T] [Fintype dOut] in
/-- Helper for fact (a) (copy): multiplying the embedding (`ℓ = 0`) or the write into `h_ℓ` by
`c` multiplies `h_ℓ` by `c`, in the network and in the changed one. -/
private theorem exists_params_smul_hidden_oor {A : Arch T d L} (θ : Params A dIn dOut)
    (x : Matrix T dIn ℝ) (G : Fin (L + 1) → GL d ℝ) (c : ℝ) (ℓ : Fin (L + 1)) :
    ∃ θ' : Params A dIn dOut, hidden A 0 θ' x ℓ = c • hidden A 0 θ x ℓ ∧
      hidden A 0 (θ'.cob G G) x ℓ = c • hidden A 0 (θ.cob G G) x ℓ := by
  cases ℓ using Fin.cases with
  | zero =>
    -- the embedding `c E`
    refine ⟨⟨c • θ.E, θ.read, θ.write, θ.D⟩, ?_, ?_⟩
    · rw [hidden_zero, hidden_zero]
      exact Matrix.mul_smul _ _ _
    · rw [hidden_zero, hidden_zero]
      show x * ((c • θ.E) * _) = c • (x * (θ.E * _))
      rw [Matrix.smul_mul, Matrix.mul_smul]
  | succ k =>
    classical
    -- the write `c W_write^k`
    let θ' : Params A dIn dOut := ⟨θ.E, θ.read, Function.update θ.write k (c • θ.write k), θ.D⟩
    have hw : ∀ j : Fin L, (j : ℕ) < (k.castSucc : ℕ) → θ'.write j = θ.write j :=
      fun j hj => Function.update_of_ne (ne_of_lt_castSucc_oor hj) _ _
    have e1 : hidden A 0 θ' x k.castSucc = hidden A 0 θ x k.castSucc :=
      hidden_congr_oor θ' θ x rfl k.castSucc (fun _ _ => rfl) hw
    have e2 : hidden A 0 (θ'.cob G G) x k.castSucc = hidden A 0 (θ.cob G G) x k.castSucc :=
      hidden_congr_oor (θ'.cob G G) (θ.cob G G) x rfl k.castSucc (fun _ _ => rfl) fun j hj => by
        show θ'.write j * _ = θ.write j * _
        rw [hw j hj]
    have hwk : θ'.write k = c • θ.write k := Function.update_self _ _ _
    have hwk' : (θ'.cob G G).write k = c • (θ.cob G G).write k := by
      show θ'.write k * (G k.succ : Matrix d d ℝ) = c • (θ.write k * (G k.succ : Matrix d d ℝ))
      rw [hwk, Matrix.smul_mul]
    refine ⟨θ', ?_, ?_⟩
    · rw [hidden_succ_skipless_oor, hidden_succ_skipless_oor, e1, hwk, Matrix.mul_smul]
    · rw [hidden_succ_skipless_oor, hidden_succ_skipless_oor, e2, hwk', Matrix.mul_smul]
      rfl

/-! ### Helpers: rows and matrices -/

omit [Fintype T] [DecidableEq d] [Fintype dOut] in
/-- Helper (copy): two matrices with the same products with every matrix on the right are
equal. -/
private theorem eq_of_forall_mul_right_oor {m n : Type*} [Fintype m] [Nonempty n]
    {X Y : Matrix T m ℝ} (h : ∀ D : Matrix m n ℝ, X * D = Y * D) : X = Y := by
  classical
  obtain ⟨o⟩ := ‹Nonempty n›
  ext t k
  -- the matrix `e_k e_oᵀ` reads off the column `k`
  have := congrFun (congrFun (h (Matrix.single k o 1)) t) o
  simpa only [mul_single_apply_same, mul_one] using this

omit [Fintype T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (copy): the argument `‖v‖² / d_model + ε` of the square root in RMSNorm is
positive. -/
private theorem rms_arg_pos_oor (hε : 0 < ε) (v : d → ℝ) :
    0 < v ⬝ᵥ v / (Fintype.card d : ℝ) + ε := by
  have : 0 ≤ v ⬝ᵥ v / (Fintype.card d : ℝ) :=
    div_nonneg (Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)) (Nat.cast_nonneg _)
  linarith

/-- Helper (copy): `p⁻¹ u = q⁻¹ w` with `p, q ≠ 0` gives `q u = p w`. -/
private theorem mul_eq_mul_of_inv_mul_eq_oor {p q u w : ℝ} (hp : p ≠ 0) (hq : q ≠ 0)
    (h : p⁻¹ * u = q⁻¹ * w) : q * u = p * w :=
  calc q * u = q * (p * (p⁻¹ * u)) := by rw [mul_inv_cancel_left₀ hp]
    _ = q * (p * (q⁻¹ * w)) := by rw [h]
    _ = p * w := by rw [mul_left_comm p, mul_inv_cancel_left₀ hq]

omit [Fintype T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper, fact (a) on rows (copy of `vecMul_eq_of_rmsRow_two`): if `N_ε(a) M = N_ε(b)` and
`N_ε(2a) M = N_ε(2b)` with `ε > 0`, then `a M = b`. -/
private theorem vecMul_eq_of_rmsRow_two_oor (hε : 0 < ε) (M : Matrix d d ℝ) {a b : d → ℝ}
    (h1 : rmsRow ε a ᵥ* M = rmsRow ε b)
    (h2 : rmsRow ε ((2 : ℝ) • a) ᵥ* M = rmsRow ε ((2 : ℝ) • b)) : a ᵥ* M = b := by
  -- `‖2v‖² / d = 4 (‖v‖² / d)`
  have h4 : ∀ v : d → ℝ, ((2 : ℝ) • v) ⬝ᵥ ((2 : ℝ) • v) / (Fintype.card d : ℝ)
      = 4 * (v ⬝ᵥ v / (Fintype.card d : ℝ)) := by
    intro v
    rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    ring
  have hp0 : ∀ v : d → ℝ, 0 ≤ v ⬝ᵥ v / (Fintype.card d : ℝ) := fun v =>
    div_nonneg (Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)) (Nat.cast_nonneg _)
  have hA0 := hp0 a
  have hB0 := hp0 b
  unfold rmsRow at h1 h2
  rw [h4, h4, Matrix.smul_vecMul, Matrix.smul_vecMul] at h2
  rw [Matrix.smul_vecMul] at h1
  generalize a ⬝ᵥ a / (Fintype.card d : ℝ) = A at h1 h2 hA0
  generalize b ⬝ᵥ b / (Fintype.card d : ℝ) = B at h1 h2 hB0
  generalize a ᵥ* M = y at h1 h2 ⊢
  -- the four square roots are positive
  have hS : ∀ t : ℝ, 0 ≤ t → 0 < Real.sqrt (t + ε) := fun t ht =>
    Real.sqrt_pos.mpr (by linarith)
  have hsa := hS A hA0
  have hsb := hS B hB0
  have hsa2 := hS (4 * A) (by linarith)
  have hsb2 := hS (4 * B) (by linarith)
  -- `s(b) y = s(a) b` and `s(2b) y = s(2a) b`, entry by entry
  have e1 : ∀ i, Real.sqrt (B + ε) * y i = Real.sqrt (A + ε) * b i := by
    intro i
    have := congrFun h1 i
    simp only [Pi.smul_apply, smul_eq_mul] at this
    exact mul_eq_mul_of_inv_mul_eq_oor hsa.ne' hsb.ne' this
  have e2 : ∀ i, Real.sqrt (4 * B + ε) * y i = Real.sqrt (4 * A + ε) * b i := by
    intro i
    have := congrFun h2 i
    simp only [Pi.smul_apply, smul_eq_mul] at this
    have := mul_eq_mul_of_inv_mul_eq_oor hsa2.ne' hsb2.ne' this
    linear_combination this / 2
  by_cases hb : b = 0
  · -- `b = 0`: then `y = 0`
    funext i
    have := e1 i
    rw [hb, Pi.zero_apply, mul_zero] at this
    rw [hb, Pi.zero_apply]
    exact (mul_eq_zero.mp this).resolve_left hsb.ne'
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hb
  -- the two factors agree: `s(a) s(2b) = s(2a) s(b)`
  have hk : Real.sqrt (A + ε) * Real.sqrt (4 * B + ε)
      = Real.sqrt (4 * A + ε) * Real.sqrt (B + ε) := by
    apply mul_right_cancel₀ hi₀
    linear_combination (-Real.sqrt (4 * B + ε)) * e1 i₀ + Real.sqrt (B + ε) * e2 i₀
  -- squaring: `(A + ε)(4B + ε) = (4A + ε)(B + ε)`, so `3 ε (A - B) = 0`
  have hsq := congrArg (· ^ 2) hk
  simp only [mul_pow, Real.sq_sqrt (show (0 : ℝ) ≤ A + ε by linarith),
    Real.sq_sqrt (show (0 : ℝ) ≤ B + ε by linarith),
    Real.sq_sqrt (show (0 : ℝ) ≤ 4 * A + ε by linarith),
    Real.sq_sqrt (show (0 : ℝ) ≤ 4 * B + ε by linarith)] at hsq
  have hAB : A = B := by
    have h3 : (A - B) * (3 * ε) = 0 := by linear_combination -hsq
    have := (mul_eq_zero.mp h3).resolve_right (by positivity)
    linarith
  -- so `s(a) = s(b)` and `y = b`
  subst hAB
  funext i
  exact mul_left_cancel₀ hsb.ne' (e1 i)

omit [Fintype T] [DecidableEq d] in
/-- Helper: a matrix whose rows all equal `a`, times `W`, has all rows `a W`. -/
private theorem of_const_mul_oor {n : Type*} (a : d → ℝ) (W : Matrix d n ℝ) :
    (Matrix.of fun _ : T => a) * W = Matrix.of fun _ : T => a ᵥ* W := rfl

omit [Fintype T] [DecidableEq d] in
/-- Helper: RMSNorm acts row by row, so it maps equal rows `a` to equal rows `N_ε(a)`. -/
private theorem rmsNorm_const_oor (a : d → ℝ) :
    rmsNorm ε (Matrix.of fun _ : T => a) = Matrix.of fun _ : T => rmsRow ε a := rfl

/-! ### Helpers: hidden states at inputs whose rows are all equal -/

omit [Fintype T] [DecidableEq d] [Fintype dOut] in
/-- Helper: at an input whose rows all equal `ξ`, every hidden state has equal rows (`h_0 = x E`;
RMSNorm acts row by row; `hrows` for the block; the write is a product on the right). -/
private theorem hidden_rows_oor {A : Arch T d L} (hA : A.χ = rmsNorm ε)
    (hrows : ∀ k (a : d → ℝ) (W : Matrix d (A.r k) ℝ), ∃ b : A.w k → ℝ,
      A.f k ((Matrix.of fun _ : T => a) * W) = Matrix.of fun _ : T => b)
    (θ : Params A dIn dOut) (ξ : dIn → ℝ) (ℓ : Fin (L + 1)) :
    ∃ u : d → ℝ, hidden A 0 θ (Matrix.of fun _ : T => ξ) ℓ = Matrix.of fun _ : T => u := by
  induction ℓ using Fin.induction with
  | zero => exact ⟨ξ ᵥ* θ.E, by rw [hidden_zero]; rfl⟩
  | succ k ih =>
    obtain ⟨u, hu⟩ := ih
    obtain ⟨b, hb⟩ := hrows k (rmsRow ε u) (θ.read k)
    refine ⟨b ᵥ* θ.write k, ?_⟩
    rw [hidden_succ_skipless_oor, hu, hA, rmsNorm_const_oor, hb, of_const_mul_oor]

omit [Fintype T] [Fintype dOut] in
/-- Helper, fact (c) on equal rows: every row `v` is the common row of the hidden state `h_ℓ` at
some parameters and some input with equal rows. From a nonzero row `a = N_ε(u_{ℓ-1})`, `hnz`
gives a read with a nonzero hidden unit `j`; the rows of the block's output are equal
(`hrows`), so the write with the row `c⁻¹ v` at `j` gives every row the value `v`. -/
private theorem exists_hidden_rows_oor {A : Arch T d L} [Nonempty dIn] [Nonempty d]
    (hε : 0 < ε) (hA : A.χ = rmsNorm ε)
    (hrows : ∀ k (a : d → ℝ) (W : Matrix d (A.r k) ℝ), ∃ b : A.w k → ℝ,
      A.f k ((Matrix.of fun _ : T => a) * W) = Matrix.of fun _ : T => b)
    (hnz : ∀ k (a : d → ℝ), a ≠ 0 →
      ∃ (W : Matrix d (A.r k) ℝ) (t : T) (j : A.w k),
        A.f k ((Matrix.of fun _ : T => a) * W) t j ≠ 0)
    (ℓ : Fin (L + 1)) (v : d → ℝ) :
    ∃ (θ : Params A dIn dOut) (ξ : dIn → ℝ),
      hidden A 0 θ (Matrix.of fun _ : T => ξ) ℓ = Matrix.of fun _ : T => v := by
  classical
  induction ℓ using Fin.induction generalizing v with
  | zero =>
    obtain ⟨i⟩ := ‹Nonempty dIn›
    -- a one-hot input row and an embedding whose rows are all `v`
    refine ⟨⟨Matrix.of fun _ => v, 0, 0, 0⟩, Pi.single i 1, ?_⟩
    rw [hidden_zero, of_const_mul_oor]
    ext t k
    simp only [Matrix.of_apply, Matrix.vecMul, dotProduct, Pi.single_apply, ite_mul, one_mul,
      zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  | succ k ih =>
    obtain ⟨i₀⟩ := ‹Nonempty d›
    -- parameters at which all rows of `h_k` are `e_{i₀}`, so all rows of `N_ε(h_k)` are `a ≠ 0`
    obtain ⟨θ, ξ, hθ⟩ := ih (Pi.single i₀ 1)
    have ha : rmsRow ε (Pi.single i₀ (1 : ℝ)) ≠ 0 := by
      refine smul_ne_zero (inv_ne_zero (Real.sqrt_pos.mpr (rms_arg_pos_oor hε _)).ne')
        fun h0 => ?_
      have := congrFun h0 i₀
      rw [Pi.single_eq_same, Pi.zero_apply] at this
      exact one_ne_zero this
    -- a read with a nonzero unit `j`; the output has equal rows `b`, with `b j ≠ 0`
    obtain ⟨W, t, j, hc⟩ := hnz k _ ha
    obtain ⟨b, hb⟩ := hrows k _ W
    rw [hb] at hc
    change b j ≠ 0 at hc
    -- the write with the row `(b j)⁻¹ v` at `j`
    let θ' : Params A dIn dOut := ⟨θ.E, Function.update θ.read k W,
      Function.update θ.write k (Matrix.of fun j' i => if j' = j then (b j)⁻¹ * v i else 0),
      θ.D⟩
    have e1 : hidden A 0 θ' (Matrix.of fun _ : T => ξ) k.castSucc
        = hidden A 0 θ (Matrix.of fun _ : T => ξ) k.castSucc :=
      hidden_congr_oor θ' θ _ rfl k.castSucc
        (fun i hi => Function.update_of_ne (ne_of_lt_castSucc_oor hi) _ _)
        (fun i hi => Function.update_of_ne (ne_of_lt_castSucc_oor hi) _ _)
    have hrk : θ'.read k = W := Function.update_self _ _ _
    have hwk : θ'.write k = Matrix.of fun j' i => if j' = j then (b j)⁻¹ * v i else 0 :=
      Function.update_self _ _ _
    refine ⟨θ', ξ, ?_⟩
    rw [hidden_succ_skipless_oor, e1, hrk, hwk, hA, hθ, rmsNorm_const_oor, hb, of_const_mul_oor]
    ext t' i
    simp only [Matrix.of_apply, Matrix.vecMul, dotProduct, mul_ite, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    exact mul_inv_cancel_left₀ hc (v i)

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
  classical
  rcases isEmpty_or_nonempty d with hd | hd
  · -- no coordinates: every `0 × 0` matrix is orthogonal
    intro ℓ
    rw [mem_orthogonalGroup_iff]
    exact Matrix.ext fun i => isEmptyElim i
  -- `S ℓ`, on inputs whose rows all equal `ξ`: `N_ε(h̃_ℓ) G_ℓ⁻¹ = N_ε(h_ℓ)` for all parameters
  let S : Fin (L + 1) → Prop := fun ℓ => ∀ (θ : Params A dIn dOut) (ξ : dIn → ℝ),
    rmsNorm ε (hidden A 0 (θ.cob G G) (Matrix.of fun _ : T => ξ) ℓ)
        * (↑(G ℓ)⁻¹ : Matrix d d ℝ)
      = rmsNorm ε (hidden A 0 θ (Matrix.of fun _ : T => ξ) ℓ)
  -- fact (a): from `S ℓ`, `ũ_ℓ = h̃_ℓ G_ℓ⁻¹ = h_ℓ` (scale the write into `h_ℓ` by `2`)
  have hU : ∀ ℓ, S ℓ → ∀ (θ : Params A dIn dOut) (ξ : dIn → ℝ),
      hidden A 0 (θ.cob G G) (Matrix.of fun _ : T => ξ) ℓ * (↑(G ℓ)⁻¹ : Matrix d d ℝ)
        = hidden A 0 θ (Matrix.of fun _ : T => ξ) ℓ := by
    intro ℓ hS θ ξ
    obtain ⟨θ₂, e2, e2'⟩ := exists_params_smul_hidden_oor θ (Matrix.of fun _ : T => ξ) G 2 ℓ
    have h1 := hS θ ξ
    have h2 := hS θ₂ ξ
    rw [e2, e2'] at h2
    funext t
    exact vecMul_eq_of_rmsRow_two_oor hε _ (congrFun h1 t) (congrFun h2 t)
  -- `S L`: the outputs agree for every readout `D`
  have hlast : S (Fin.last L) := by
    intro θ ξ
    refine eq_of_forall_mul_right_oor (n := dOut) fun D => ?_
    have he := h ⟨θ.E, θ.read, θ.write, D⟩ (Matrix.of fun _ : T => ξ)
    unfold eval at he
    change A.χ (hidden A 0 (θ.cob G G) (Matrix.of fun _ : T => ξ) (Fin.last L))
        * ((↑(G (Fin.last L))⁻¹ : Matrix d d ℝ) * D)
      = A.χ (hidden A 0 θ (Matrix.of fun _ : T => ξ) (Fin.last L)) * D at he
    rw [hA, ← Matrix.mul_assoc] at he
    exact he
  -- fact (b): from `ũ_{k+1} = h_{k+1}` for all reads and writes of block `k` to `S k`
  have hstep : ∀ k : Fin L, S k.succ → S k.castSucc := by
    intro k hS θ ξ
    -- the common rows `u` of `h_k` and `u'` of `h̃_k`
    obtain ⟨u, hu⟩ := hidden_rows_oor hA hrows θ ξ k.castSucc
    obtain ⟨u', hu'⟩ := hidden_rows_oor hA hrows (θ.cob G G) ξ k.castSucc
    -- the two outputs of block `k` agree for all writes, so the maps agree for all reads
    have key : ∀ W : Matrix d (A.r k) ℝ,
        A.f k (rmsNorm ε (hidden A 0 (θ.cob G G) (Matrix.of fun _ : T => ξ) k.castSucc)
            * (↑(G k.castSucc)⁻¹ : Matrix d d ℝ) * W)
          = A.f k (rmsNorm ε (hidden A 0 θ (Matrix.of fun _ : T => ξ) k.castSucc) * W) := by
      intro W
      refine eq_of_forall_mul_right_oor (n := d) fun V => ?_
      let θ' : Params A dIn dOut :=
        ⟨θ.E, Function.update θ.read k W, Function.update θ.write k V, θ.D⟩
      have hr : ∀ j : Fin L, (j : ℕ) < (k.castSucc : ℕ) → θ'.read j = θ.read j :=
        fun j hj => Function.update_of_ne (ne_of_lt_castSucc_oor hj) _ _
      have hw : ∀ j : Fin L, (j : ℕ) < (k.castSucc : ℕ) → θ'.write j = θ.write j :=
        fun j hj => Function.update_of_ne (ne_of_lt_castSucc_oor hj) _ _
      have e1 : hidden A 0 θ' (Matrix.of fun _ : T => ξ) k.castSucc
          = hidden A 0 θ (Matrix.of fun _ : T => ξ) k.castSucc :=
        hidden_congr_oor θ' θ _ rfl k.castSucc hr hw
      have e2 : hidden A 0 (θ'.cob G G) (Matrix.of fun _ : T => ξ) k.castSucc
          = hidden A 0 (θ.cob G G) (Matrix.of fun _ : T => ξ) k.castSucc :=
        hidden_congr_oor (θ'.cob G G) (θ.cob G G) _ rfl k.castSucc
          (fun j hj => by
            show (↑(G j.castSucc)⁻¹ : Matrix d d ℝ) * θ'.read j
              = (↑(G j.castSucc)⁻¹ : Matrix d d ℝ) * θ.read j
            rw [hr j hj])
          (fun j hj => by
            show θ'.write j * (G j.succ : Matrix d d ℝ) = θ.write j * (G j.succ : Matrix d d ℝ)
            rw [hw j hj])
      have hrk : θ'.read k = W := Function.update_self _ _ _
      have hwk : θ'.write k = V := Function.update_self _ _ _
      have hrk' : (θ'.cob G G).read k = (↑(G k.castSucc)⁻¹ : Matrix d d ℝ) * W := by
        show (↑(G k.castSucc)⁻¹ : Matrix d d ℝ) * θ'.read k = _
        rw [hrk]
      have hwk' : (θ'.cob G G).write k = V * (G k.succ : Matrix d d ℝ) := by
        show θ'.write k * (G k.succ : Matrix d d ℝ) = _
        rw [hwk]
      have hU' := hU k.succ hS θ' ξ
      rw [hidden_succ_skipless_oor, hidden_succ_skipless_oor, e1, e2, hrk, hwk, hrk', hwk', hA,
        Matrix.mul_assoc _ (V * _), Matrix.mul_assoc V, Units.mul_inv, Matrix.mul_one,
        ← Matrix.mul_assoc (rmsNorm ε _)] at hU'
      exact hU'
    -- on equal rows: `N_ε(u') G_k⁻¹` and `N_ε(u)` give the same block maps, so `hsep`
    rw [hu, hu', rmsNorm_const_oor, rmsNorm_const_oor,
      of_const_mul_oor (rmsRow ε u') (↑(G k.castSucc)⁻¹ : Matrix d d ℝ)] at key
    rw [hu, hu', rmsNorm_const_oor, rmsNorm_const_oor,
      of_const_mul_oor (rmsRow ε u') (↑(G k.castSucc)⁻¹ : Matrix d d ℝ), hsep k _ _ key]
  have hS : ∀ ℓ, S ℓ := fun ℓ => Fin.reverseInduction hlast hstep ℓ
  -- fact (c): every row `v` is the row of some `h_ℓ`, and `N_ε(h_ℓ G_ℓ) = N_ε(h_ℓ) G_ℓ`
  intro ℓ
  refine (orthogonal_of_rmsRow_vecMul hε (G ℓ) (G ℓ) fun v _ => ?_).1
  obtain ⟨θ, ξ, hv⟩ := exists_hidden_rows_oor (dIn := dIn) (dOut := dOut) hε hA hrows hnz ℓ v
  obtain ⟨t⟩ := ‹Nonempty T›
  have h1 := hS ℓ θ ξ
  have h2 := hU ℓ (hS ℓ) θ ξ
  -- `h̃_ℓ = h_ℓ G_ℓ`
  have h3 : hidden A 0 (θ.cob G G) (Matrix.of fun _ : T => ξ) ℓ
      = hidden A 0 θ (Matrix.of fun _ : T => ξ) ℓ * (G ℓ : Matrix d d ℝ) := by
    rw [← h2, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
  rw [h3] at h1
  have h4 : rmsNorm ε (hidden A 0 θ (Matrix.of fun _ : T => ξ) ℓ * (G ℓ : Matrix d d ℝ))
      = rmsNorm ε (hidden A 0 θ (Matrix.of fun _ : T => ξ) ℓ) * (G ℓ : Matrix d d ℝ) := by
    rw [← h1, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
  have h5 := congrFun h4 t
  rw [hv] at h5
  exact h5

/-! ### Attention blocks -/

omit [Fintype d] [DecidableEq d] in
/-- Helper (copy of `attnWeights_sum_rat` of `Absorb/RMSNormAttention.lean`): row `t` of the
weights sums to `1` when token `t` sees some token (the denominator is positive). -/
private theorem attnWeights_sum_oor (Z : Matrix T T ℝ) (t : T) (ht : ∃ s, sees t s) :
    ∑ s, attnWeights sees Z t s = 1 := by
  obtain ⟨s, hs⟩ := ht
  have hS : 0 < ∑ s', if sees t s' then Real.exp (Z t s') else 0 := by
    refine Finset.sum_pos' (fun s' _ => ?_) ⟨s, Finset.mem_univ _, ?_⟩
    · split_ifs
      · exact (Real.exp_pos _).le
      · exact le_rfl
    · simp only [hs, ite_true]
      exact Real.exp_pos _
  have h1 : ∀ s, attnWeights sees Z t s = (if sees t s then Real.exp (Z t s) else 0)
      / ∑ s', if sees t s' then Real.exp (Z t s') else 0 := by
    intro s
    simp only [attnWeights, Matrix.of_apply]
    split_ifs
    · rfl
    · rw [zero_div]
  simp only [h1, ← Finset.sum_div]
  exact div_self hS.ne'

omit [Fintype d] [DecidableEq d] in
/-- Helper (copy of `f_attention_entry_const_rat`): if the value coordinate `k` of head `i` is
the same number `v` at every token, entry `(t, (i, k))` of the output of the block is `v` when
token `t` sees some token. -/
private theorem f_attention_entry_const_oor (χ : Matrix T d ℝ → Matrix T d ℝ) (ℓ : Fin L)
    (M : Matrix T (H ℓ × (dh ℓ ⊕ (dh ℓ ⊕ dh ℓ))) ℝ) (i : H ℓ) (k : dh ℓ) (v : ℝ)
    (hv : ∀ s, M s (i, Sum.inr (Sum.inr k)) = v) (t s : T) (hts : sees t s) :
    (Arch.attention sees χ H dh).f ℓ M t (i, k) = v := by
  show ∑ s', attnWeights sees _ t s' * M s' (i, Sum.inr (Sum.inr k)) = v
  simp only [hv, ← Finset.sum_mul, attnWeights_sum_oor _ t ⟨s, hts⟩, one_mul]

omit [DecidableEq d] in
/-- Helper: on equal rows `a`, an attention block (every token sees some token) writes in every
row, at head `i` and coordinate `k`, the value `a w` of the value column `w` of `(i, k)`. -/
private theorem f_attention_const_oor (hsees : ∀ t, ∃ s, sees t s)
    (χ : Matrix T d ℝ → Matrix T d ℝ) (k : Fin L) (a : d → ℝ)
    (W : Matrix d (H k × (dh k ⊕ (dh k ⊕ dh k))) ℝ) :
    (Arch.attention sees χ H dh).f k ((Matrix.of fun _ : T => a) * W)
      = Matrix.of fun _ : T => fun p : H k × dh k => (a ᵥ* W) (p.1, Sum.inr (Sum.inr p.2)) := by
  ext t p
  obtain ⟨s, hts⟩ := hsees t
  exact f_attention_entry_const_oor χ k _ p.1 p.2 _ (fun _ => rfl) t s hts

omit [DecidableEq d] in
/-- Helper: an attention block maps equal rows to equal rows. -/
private theorem rows_attention_oor (hsees : ∀ t, ∃ s, sees t s)
    (χ : Matrix T d ℝ → Matrix T d ℝ) (k : Fin L) (a : d → ℝ)
    (W : Matrix d (H k × (dh k ⊕ (dh k ⊕ dh k))) ℝ) :
    ∃ b : H k × dh k → ℝ,
      (Arch.attention sees χ H dh).f k ((Matrix.of fun _ : T => a) * W)
        = Matrix.of fun _ : T => b :=
  ⟨_, f_attention_const_oor hsees χ k a W⟩

omit [DecidableEq d] in
/-- Helper, fact (b) for an attention block on equal tokens: if `a′ w = a w` for every value
column `w` (a head and a coordinate exist), then `a′ = a`. -/
private theorem sep_attention_oor [Nonempty T] (hsees : ∀ t, ∃ s, sees t s)
    (χ : Matrix T d ℝ → Matrix T d ℝ) (k : Fin L) (hHk : Nonempty (H k))
    (hdhk : Nonempty (dh k)) (a a' : d → ℝ)
    (h : ∀ W : Matrix d (H k × (dh k ⊕ (dh k ⊕ dh k))) ℝ,
      (Arch.attention sees χ H dh).f k ((Matrix.of fun _ : T => a') * W)
        = (Arch.attention sees χ H dh).f k ((Matrix.of fun _ : T => a) * W)) : a' = a := by
  classical
  obtain ⟨i⟩ := hHk
  obtain ⟨κ⟩ := hdhk
  obtain ⟨t⟩ := ‹Nonempty T›
  funext j
  -- all columns of the read `e_j`: the entry `(t, (i, κ))` is `a′ e_j = a e_j`
  let W : Matrix d (H k × (dh k ⊕ (dh k ⊕ dh k))) ℝ :=
    Matrix.of fun r _ => (Pi.single j (1 : ℝ) : d → ℝ) r
  have e := congrFun (congrFun ((f_attention_const_oor hsees χ k a' W).symm.trans
    ((h W).trans (f_attention_const_oor hsees χ k a W))) t) (i, κ)
  change a' ⬝ᵥ Pi.single j 1 = a ⬝ᵥ Pi.single j 1 at e
  simpa only [dotProduct_single, mul_one] using e

omit [DecidableEq d] in
/-- Helper, for fact (c): on equal nonzero rows `a`, the value column `a` gives the unit
`(i, κ)` the value `a ⬝ᵥ a ≠ 0`. -/
private theorem nz_attention_oor [Nonempty T] (hsees : ∀ t, ∃ s, sees t s)
    (χ : Matrix T d ℝ → Matrix T d ℝ) (k : Fin L) (hHk : Nonempty (H k))
    (hdhk : Nonempty (dh k)) (a : d → ℝ) (ha : a ≠ 0) :
    ∃ (W : Matrix d (H k × (dh k ⊕ (dh k ⊕ dh k))) ℝ) (t : T) (j : H k × dh k),
      (Arch.attention sees χ H dh).f k ((Matrix.of fun _ : T => a) * W) t j ≠ 0 := by
  obtain ⟨i⟩ := hHk
  obtain ⟨κ⟩ := hdhk
  obtain ⟨t⟩ := ‹Nonempty T›
  refine ⟨Matrix.of fun r _ => a r, t, (i, κ), ?_⟩
  rw [f_attention_const_oor hsees]
  change a ⬝ᵥ a ≠ 0
  exact fun h0 => ha (dotProduct_self_eq_zero.mp h0)

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
