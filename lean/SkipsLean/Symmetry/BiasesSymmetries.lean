import SkipsLean.Network.Biases
import SkipsLean.Symmetry.ChangeOfBasis

/-!
# Changes of basis and translations in networks with biases

Paper (skips paper), Lemma A.8 (Translations are not tied): "In a residual network with biases
and without normalization, adding a row `g` to the hidden states `h_ℓ, …, h_L` preserves the
function once the biases are adjusted, for every `ℓ = 0, …, L`." Its proof: "Add `g` to the write
bias of block `ℓ`, or to the embedding bias when `ℓ = 0`; subtract `g W_read^k` from the read bias
of every block `k > ℓ`; subtract `g D` from the readout bias. The skips carry `g` forward
unchanged, so every later hidden state is shifted by `g`, and every later read removes it. […]
These `L + 1` translations move the biases in independent directions, as many as in a skipless
network, where each hidden state has its own translation (Proposition A.1 (ii))."

Here, for the networks with biases of `Network/Biases.lean`:

* `Biases.cob`, `hiddenB_cob`, `evalB_cob`: the changes of basis `θ.cob G K` of the hidden states
  (Proposition A.1 (ii)) with biases: the embedding bias and the write biases are rows of hidden
  states, and are multiplied by `G` as the embedding and the writes are; the read biases and the
  readout bias do not change. The statement has the form of `eval_cob`
  (`Symmetry/ChangeOfBasis.lean`).
* `Biases.translate`, `hiddenB_translate`, `evalB_translate`: Lemma A.8, first sentence, for a
  residual network without normalization (any kind of block): the hidden states `h_k, …, h_L` are
  shifted by `g` and the function does not change.
* `Biases.translateAt`, `hiddenB_translateAt`, `evalB_translateAt`: "in a skipless network […]
  each hidden state has its own translation": only `h_k` is shifted.

The count of the lemma (the dimensions of the groups) is not stated here.
-/

namespace Skips

open Matrix

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype d] [DecidableEq d] [Fintype dIn]
variable {A : Arch T d L}

/-- **The biases after the changes of basis `G_0, …, G_L` of the hidden states:** the embedding
bias is multiplied by `G_0` and the write bias of block `ℓ` by `G_ℓ`; the read biases and the
readout bias are unchanged. -/
def Biases.cob (b : Biases A dOut) (G : Fin (L + 1) → GL d ℝ) : Biases A dOut where
  E := b.E ᵥ* (G 0 : Matrix d d ℝ)
  read := b.read
  write ℓ := b.write ℓ ᵥ* (G ℓ.succ : Matrix d d ℝ)
  D := b.D

/-- **The biases after the translation of the hidden states `h_k, …, h_L` of a residual network
by the row `g`** (Lemma A.8): `g` is added to the bias that enters `h_k` (the embedding bias for
`k = 0`, the write bias of the block that writes `h_k` otherwise), `g W_read` is subtracted from
the read bias of every block that reads one of `h_k, …, h_{L-1}`, and `g D` from the readout
bias. -/
def Biases.translate (b : Biases A dOut) (θ : Params A dIn dOut) (k : Fin (L + 1)) (g : d → ℝ) :
    Biases A dOut where
  E := if k = 0 then b.E + g else b.E
  read ℓ := if k ≤ ℓ.castSucc then b.read ℓ - g ᵥ* θ.read ℓ else b.read ℓ
  write ℓ := if ℓ.succ = k then b.write ℓ + g else b.write ℓ
  D := b.D - g ᵥ* θ.D

/-- **The biases after the translation of the one hidden state `h_k` of a skipless network by the
row `g`:** `g` is added to the bias that enters `h_k`, and `g W_read` is subtracted from the read
bias of the block that reads `h_k`, or `g D` from the readout bias if `k = L`. -/
def Biases.translateAt (b : Biases A dOut) (θ : Params A dIn dOut) (k : Fin (L + 1))
    (g : d → ℝ) : Biases A dOut where
  E := if k = 0 then b.E + g else b.E
  read ℓ := if ℓ.castSucc = k then b.read ℓ - g ᵥ* θ.read ℓ else b.read ℓ
  write ℓ := if ℓ.succ = k then b.write ℓ + g else b.write ℓ
  D := if k = Fin.last L then b.D - g ᵥ* θ.D else b.D

omit [Fintype d] [DecidableEq d] [Fintype dIn] in
/-- Helper: a matrix whose rows are all `g`, times `W`, has all rows `g ᵥ* W`. -/
private theorem of_mul_bsy {m n : Type*} [Fintype m] (g : m → ℝ) (W : Matrix m n ℝ) :
    (Matrix.of fun (_ : T) => g) * W = Matrix.of fun _ => g ᵥ* W := by
  ext t j
  simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.vecMul, dotProduct]

omit [Fintype d] [DecidableEq d] [Fintype dIn] in
/-- Helper: `(H + g) W = H W + g W`, with the row `g` at every token. -/
private theorem add_of_mul_bsy {m n : Type*} [Fintype m] (H : Matrix T m ℝ) (g : m → ℝ)
    (W : Matrix m n ℝ) :
    (H + Matrix.of fun _ => g) * W = H * W + Matrix.of fun _ => g ᵥ* W := by
  rw [Matrix.add_mul, of_mul_bsy]

omit [Fintype d] [DecidableEq d] [Fintype dIn] in
/-- Helper: the row `g` added to `H` and `g W` subtracted from the bias give the same
pre-activation `H W + b`. -/
private theorem shift_read_bsy {m n : Type*} [Fintype m] (H : Matrix T m ℝ) (g : m → ℝ)
    (W : Matrix m n ℝ) (c : n → ℝ) :
    (H + Matrix.of fun _ => g) * W + (Matrix.of fun _ => c - g ᵥ* W)
      = H * W + Matrix.of fun _ => c := by
  rw [add_of_mul_bsy]
  ext t j
  simp only [Matrix.add_apply, Matrix.of_apply, Pi.sub_apply]
  ring

omit [Fintype d] [DecidableEq d] [Fintype dIn] in
/-- Helper: the rows `c + g` at every token are the sum of the rows `c` and `g`. -/
private theorem of_add_bsy {n : Type*} (c g : n → ℝ) :
    (Matrix.of fun (_ : T) => c + g) = (Matrix.of fun _ => c) + Matrix.of fun _ => g := rfl

omit [Fintype dIn] in
/-- Helper: `a (a⁻¹ B) = B` for `a : GL d ℝ` and a rectangular `B`. -/
private theorem gl_mul_inv_mul_bsy {n : Type*} (a : GL d ℝ) (B : Matrix d n ℝ) :
    (a : Matrix d d ℝ) * ((↑a⁻¹ : Matrix d d ℝ) * B) = B := by
  rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]

variable (M : Fin L → Matrix d d ℝ) (θ : Params A dIn dOut) (b : Biases A dOut)
  (G K : Fin (L + 1) → GL d ℝ) (x : Matrix T dIn ℝ)

/-- With biases, the hidden states after the changes of basis are `h_ℓ G_ℓ`. -/
theorem hiddenB_cob
    (hχ : ∀ ℓ (h : Matrix T d ℝ), A.χ (h * (G ℓ : Matrix d d ℝ)) = A.χ h * (K ℓ : Matrix d d ℝ))
    (ℓ : Fin (L + 1)) :
    hiddenB A (cobSkip M G) (θ.cob G K) (b.cob G) x ℓ
      = hiddenB A M θ b x ℓ * (G ℓ : Matrix d d ℝ) := by
  induction ℓ using Fin.induction with
  | zero =>
    -- `h'_0 = x E G_0 + b_E G_0 = (x E + b_E) G_0`
    simp only [hiddenB_zero, Params.cob, Biases.cob, add_of_mul_bsy, Matrix.mul_assoc]
  | succ i ih =>
    -- stream `h G_i (G_i⁻¹ M G_{i+1})`, read `χ(h) K_i K_i⁻¹ W_read + b_read`, write times `G_{i+1}`
    rw [hiddenB_succ, hiddenB_succ, ih, hχ]
    unfold cobSkip Params.cob Biases.cob
    simp only [Matrix.mul_assoc, gl_mul_inv_mul_bsy, Matrix.add_mul, of_mul_bsy]

/-- **Proposition A.1 (ii) of the skips paper with biases:** the changes of basis of the hidden
states, with the embedding bias and the write biases multiplied as the embedding and the writes
are, preserve the function. -/
theorem evalB_cob
    (hχ : ∀ ℓ (h : Matrix T d ℝ), A.χ (h * (G ℓ : Matrix d d ℝ)) = A.χ h * (K ℓ : Matrix d d ℝ)) :
    evalB A (cobSkip M G) (θ.cob G K) (b.cob G) x = evalB A M θ b x := by
  -- `χ(h_L G_L) K_L⁻¹ D + b_D = χ(h_L) K_L K_L⁻¹ D + b_D = χ(h_L) D + b_D`
  unfold evalB
  rw [hiddenB_cob M θ b G K x hχ (Fin.last L), hχ]
  simp only [Params.cob, Biases.cob, Matrix.mul_assoc, gl_mul_inv_mul_bsy]

/-- **Lemma A.8 of the skips paper, the hidden states:** in a residual network with biases and
without normalization, after the translation by `g` from the hidden state `h_k` on, the hidden
states `h_k, …, h_L` are shifted by the row `g` at every token and the earlier ones are
unchanged. -/
theorem hiddenB_translate (hA : A.χ = id) (k : Fin (L + 1)) (g : d → ℝ) (m : Fin (L + 1)) :
    hiddenB A 1 θ (b.translate θ k g) x m
      = hiddenB A 1 θ b x m + if k ≤ m then Matrix.of (fun _ => g) else 0 := by
  induction m using Fin.induction with
  | zero =>
    -- `h'_0 = x E + b'_E`, and `k ≤ 0` exactly when `k = 0`
    rw [hiddenB_zero, hiddenB_zero]
    by_cases hk : k = 0
    · subst hk
      simp only [Biases.translate, le_refl, ite_true, of_add_bsy, add_assoc]
    · have hk' : ¬ k ≤ 0 := fun h => hk (nonpos_iff_eq_zero.mp h)
      simp only [Biases.translate, hk, hk', ite_false, add_zero]
  | succ ℓ ih =>
    rw [hiddenB_succ, hiddenB_succ, ih, hA]
    simp only [Pi.one_apply, Matrix.mul_one, id_eq]
    by_cases h1 : k ≤ ℓ.castSucc
    · -- `h'_ℓ = h_ℓ + g`: the read removes `g`, the write bias is unchanged, the skip carries `g`
      have h2 : k ≤ ℓ.succ := h1.trans (Fin.castSucc_le_succ ℓ)
      have h3 : ℓ.succ ≠ k := fun h => absurd (h ▸ h1) (not_le.mpr Fin.castSucc_lt_succ)
      simp only [Biases.translate, h1, h2, h3, ite_true, ite_false, shift_read_bsy]
      abel
    · -- `h'_ℓ = h_ℓ`: the read is unchanged, and the write bias has `+ g` iff `ℓ.succ = k`
      have h2 : ℓ.succ ≤ k := Fin.castSucc_lt_iff_succ_le.mp (not_le.mp h1)
      simp only [Biases.translate, h1, ite_false, add_zero]
      by_cases h3 : ℓ.succ = k
      · subst h3
        simp only [le_refl, ite_true, of_add_bsy, add_assoc]
      · have h4 : ¬ k ≤ ℓ.succ := fun h => h3 (le_antisymm h2 h)
        simp only [h3, h4, ite_false, add_zero]

/-- **Lemma A.8 of the skips paper, "adding a row `g` to the hidden states `h_ℓ, …, h_L`
preserves the function once the biases are adjusted":** in a residual network with biases and
without normalization, for every hidden state `h_k` and every row `g`. -/
theorem evalB_translate (hA : A.χ = id) (k : Fin (L + 1)) (g : d → ℝ) :
    evalB A 1 θ (b.translate θ k g) x = evalB A 1 θ b x := by
  -- `(h_L + g) D + b_D − g D = h_L D + b_D`
  unfold evalB
  rw [hiddenB_translate θ b x hA k g (Fin.last L), hA]
  simp only [Fin.le_last, ite_true, id_eq, Biases.translate, shift_read_bsy]

/-- **The translation of one hidden state of a skipless network, the hidden states:** without
normalization, after the translation of `h_k` by `g`, the hidden state `h_k` is shifted by the row
`g` at every token and all others are unchanged. -/
theorem hiddenB_translateAt (hA : A.χ = id) (k : Fin (L + 1)) (g : d → ℝ) (m : Fin (L + 1)) :
    hiddenB A 0 θ (b.translateAt θ k g) x m
      = hiddenB A 0 θ b x m + if m = k then Matrix.of (fun _ => g) else 0 := by
  induction m using Fin.induction with
  | zero =>
    -- `h'_0 = x E + b'_E`, and `0 = k` exactly when `k = 0`
    rw [hiddenB_zero, hiddenB_zero]
    by_cases hk : k = 0
    · subst hk
      simp only [Biases.translateAt, ite_true, of_add_bsy, add_assoc]
    · have hk' : ¬ (0 : Fin (L + 1)) = k := fun h => hk h.symm
      simp only [Biases.translateAt, hk, hk', ite_false, add_zero]
  | succ ℓ ih =>
    -- no skip: `h'_{ℓ+1} = f(h'_ℓ W_read + b'_read) W_write + b'_write`
    rw [hiddenB_succ, hiddenB_succ, ih, hA]
    -- the pre-activation is unchanged: if `h_ℓ` is shifted, the read bias removes `g W_read`
    have hread : (hiddenB A 0 θ b x ℓ.castSucc
          + if ℓ.castSucc = k then Matrix.of (fun _ => g) else 0) * θ.read ℓ
        + (Matrix.of fun _ => (b.translateAt θ k g).read ℓ)
        = hiddenB A 0 θ b x ℓ.castSucc * θ.read ℓ + Matrix.of fun _ => b.read ℓ := by
      by_cases h1 : ℓ.castSucc = k
      · subst h1
        simp only [Biases.translateAt, ite_true, shift_read_bsy]
      · simp only [Biases.translateAt, h1, ite_false, add_zero]
    simp only [id_eq, hread, Pi.zero_apply, Matrix.mul_zero, zero_add]
    -- the write bias has `+ g` exactly when `ℓ.succ = k`
    by_cases h3 : ℓ.succ = k
    · simp only [Biases.translateAt, h3, ite_true, of_add_bsy, add_assoc]
    · simp only [Biases.translateAt, h3, ite_false, add_zero]

/-- **Proof of Lemma A.8, "in a skipless network […] each hidden state has its own
translation":** in a skipless network with biases and without normalization, the translation of
one hidden state `h_k` by a row `g`, with the biases adjusted, preserves the function. -/
theorem evalB_translateAt (hA : A.χ = id) (k : Fin (L + 1)) (g : d → ℝ) :
    evalB A 0 θ (b.translateAt θ k g) x = evalB A 0 θ b x := by
  -- if `k = L`: `(h_L + g) D + b_D − g D = h_L D + b_D`; otherwise nothing changes
  unfold evalB
  rw [hiddenB_translateAt θ b x hA k g (Fin.last L), hA]
  by_cases hk : Fin.last L = k
  · subst hk
    simp only [id_eq, Biases.translateAt, ite_true, shift_read_bsy]
  · have hk' : ¬ k = Fin.last L := fun h => hk h.symm
    simp only [id_eq, Biases.translateAt, hk, hk', ite_false, add_zero]

end Skips
