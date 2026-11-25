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

variable (M : Fin L → Matrix d d ℝ) (θ : Params A dIn dOut) (b : Biases A dOut)
  (G K : Fin (L + 1) → GL d ℝ) (x : Matrix T dIn ℝ)

/-- With biases, the hidden states after the changes of basis are `h_ℓ G_ℓ`. -/
theorem hiddenB_cob
    (hχ : ∀ ℓ (h : Matrix T d ℝ), A.χ (h * (G ℓ : Matrix d d ℝ)) = A.χ h * (K ℓ : Matrix d d ℝ))
    (ℓ : Fin (L + 1)) :
    hiddenB A (cobSkip M G) (θ.cob G K) (b.cob G) x ℓ
      = hiddenB A M θ b x ℓ * (G ℓ : Matrix d d ℝ) := by
  sorry

/-- **Proposition A.1 (ii) of the skips paper with biases:** the changes of basis of the hidden
states, with the embedding bias and the write biases multiplied as the embedding and the writes
are, preserve the function. -/
theorem evalB_cob
    (hχ : ∀ ℓ (h : Matrix T d ℝ), A.χ (h * (G ℓ : Matrix d d ℝ)) = A.χ h * (K ℓ : Matrix d d ℝ)) :
    evalB A (cobSkip M G) (θ.cob G K) (b.cob G) x = evalB A M θ b x := by
  sorry

/-- **Lemma A.8 of the skips paper, the hidden states:** in a residual network with biases and
without normalization, after the translation by `g` from the hidden state `h_k` on, the hidden
states `h_k, …, h_L` are shifted by the row `g` at every token and the earlier ones are
unchanged. -/
theorem hiddenB_translate (hA : A.χ = id) (k : Fin (L + 1)) (g : d → ℝ) (m : Fin (L + 1)) :
    hiddenB A 1 θ (b.translate θ k g) x m
      = hiddenB A 1 θ b x m + if k ≤ m then Matrix.of (fun _ => g) else 0 := by
  sorry

/-- **Lemma A.8 of the skips paper, "adding a row `g` to the hidden states `h_ℓ, …, h_L`
preserves the function once the biases are adjusted":** in a residual network with biases and
without normalization, for every hidden state `h_k` and every row `g`. -/
theorem evalB_translate (hA : A.χ = id) (k : Fin (L + 1)) (g : d → ℝ) :
    evalB A 1 θ (b.translate θ k g) x = evalB A 1 θ b x := by
  sorry

/-- **The translation of one hidden state of a skipless network, the hidden states:** without
normalization, after the translation of `h_k` by `g`, the hidden state `h_k` is shifted by the row
`g` at every token and all others are unchanged. -/
theorem hiddenB_translateAt (hA : A.χ = id) (k : Fin (L + 1)) (g : d → ℝ) (m : Fin (L + 1)) :
    hiddenB A 0 θ (b.translateAt θ k g) x m
      = hiddenB A 0 θ b x m + if m = k then Matrix.of (fun _ => g) else 0 := by
  sorry

/-- **Proof of Lemma A.8, "in a skipless network […] each hidden state has its own
translation":** in a skipless network with biases and without normalization, the translation of
one hidden state `h_k` by a row `g`, with the biases adjusted, preserves the function. -/
theorem evalB_translateAt (hA : A.χ = id) (k : Fin (L + 1)) (g : d → ℝ) :
    evalB A 0 θ (b.translateAt θ k g) x = evalB A 0 θ b x := by
  sorry

end Skips
