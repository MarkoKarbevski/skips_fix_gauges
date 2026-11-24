import SkipsLean.Absorb.AttentionBlock

/-!
# Attention heads are identifiable on three or more tokens

Paper (absorb paper), Appendix A.2.

Lemma A.14 (Attention heads are identifiable): "Let `T ≥ 3`. Let
`Γ_1, …, Γ_m ∈ ℝ^{d_model × d_model}` be distinct, let `C_1, …, C_m, M ∈ ℝ^{d_model × d_model}`,
and write `P_Γ(h) = softmax(h Γ h^⊤)`, with the softmax taken row by row, with or without a causal
mask. If `h M + ∑_{k=1}^m P_{Γ_k}(h) h C_k = 0` for all `h` in a nonempty open subset of
`ℝ^{T × d_model}`, then `M = 0` and `C_1 = ⋯ = C_m = 0`."

Proposition A.15 (The softmaxes must match): "Let `T ≥ 3`, let `θ` and `θ′` be parameters of
attention blocks, and suppose that `h M + B_θ(h) = B_{θ′}(h)` for all `h` in a nonempty open set.
Then `M = 0`, and for every matrix `Γ`, the heads with score matrix `Γ` have the same sum of
value–output products in `B_θ` as in `B_{θ′}`."

The proof of the lemma uses the mask through one token only: "look at the last row, which attends
to all `T` tokens with or without a causal mask". So the lemma is stated for any mask `sees` in
which some token sees every token, on at least three tokens; the two masks of the paper (no mask:
`sees = fun _ _ => True`; the causal mask on `Fin n`: `sees t s` is `s ≤ t`) are stated by name.
`P_Γ(h)` is `attnWeights sees (h * Γ * hᵀ)` (`Network/Attention.lean`), and an attention block
with the score matrices `Γ_i` and the value–output products `C_i` is `attnHeads sees Γ C`; the
block `B_θ` of the paper, with the heads `W_{Q,i}, W_{K,i}, W_{V,i}, W_{O,i}` of dimension `d_h`,
is `attentionBlock`, with `Γ_i = W_{Q,i} W_{K,i}^⊤ / √d_h` and `C_i = W_{V,i} W_{O,i}`.

With two tokens the lemma fails (the paper, after Proposition A.15: "With two tokens, heads can
cancel"). The paper's proof moves one token along a complex line and compares the poles of the
heads.
-/

namespace Skips

open Matrix

variable {T d : Type*} [Fintype T] [Fintype d]

/-- **Lemma A.14 of the absorb paper (Attention heads are identifiable):** on at least three
tokens, with a mask in which some token sees every token, let the score matrices `Γ_1, …, Γ_m` be
distinct. If `h M + ∑_k P_{Γ_k}(h) h C_k = 0` for all `h` in a nonempty open set, then `M = 0` and
every `C_k = 0`. -/
theorem attnHeads_identifiable (sees : T → T → Prop) [DecidableRel sees]
    (hT : 3 ≤ Fintype.card T) (hsees : ∃ t₀, ∀ s, sees t₀ s) {m : ℕ}
    (Γ : Fin m → Matrix d d ℝ) (hΓ : Function.Injective Γ) (C : Fin m → Matrix d d ℝ)
    (M : Matrix d d ℝ) (U : Set (Matrix T d ℝ)) (hU : IsOpen U) (hne : U.Nonempty)
    (h0 : ∀ h ∈ U, h * M + ∑ k, attnWeights sees (h * Γ k * hᵀ) * h * C k = 0) :
    M = 0 ∧ ∀ k, C k = 0 := by
  sorry

/-- **Lemma A.14 without a mask:** every token sees every token. -/
theorem attnHeads_identifiable_noMask (hT : 3 ≤ Fintype.card T) {m : ℕ}
    (Γ : Fin m → Matrix d d ℝ) (hΓ : Function.Injective Γ) (C : Fin m → Matrix d d ℝ)
    (M : Matrix d d ℝ) (U : Set (Matrix T d ℝ)) (hU : IsOpen U) (hne : U.Nonempty)
    (h0 : ∀ h ∈ U,
      h * M + ∑ k, attnWeights (fun _ _ : T => True) (h * Γ k * hᵀ) * h * C k = 0) :
    M = 0 ∧ ∀ k, C k = 0 := by
  -- there is a token, and without a mask it sees every token
  obtain ⟨t₀⟩ : Nonempty T := Fintype.card_pos_iff.mp (by omega)
  exact attnHeads_identifiable (fun _ _ : T => True) hT ⟨t₀, fun _ => trivial⟩ Γ hΓ C M U hU
    hne h0

/-- **Lemma A.14 with the causal mask:** on the tokens `0, …, n − 1`, `n ≥ 3`, token `t` sees the
tokens `s ≤ t`. -/
theorem attnHeads_identifiable_causal {n : ℕ} (hn : 3 ≤ n) {m : ℕ}
    (Γ : Fin m → Matrix d d ℝ) (hΓ : Function.Injective Γ) (C : Fin m → Matrix d d ℝ)
    (M : Matrix d d ℝ) (U : Set (Matrix (Fin n) d ℝ)) (hU : IsOpen U) (hne : U.Nonempty)
    (h0 : ∀ h ∈ U,
      h * M + ∑ k, attnWeights (fun t s : Fin n => s ≤ t) (h * Γ k * hᵀ) * h * C k = 0) :
    M = 0 ∧ ∀ k, C k = 0 := by
  -- the last token `n - 1` sees every token
  have hT : 3 ≤ Fintype.card (Fin n) := by rw [Fintype.card_fin]; exact hn
  refine attnHeads_identifiable (fun t s : Fin n => s ≤ t) hT ⟨⟨n - 1, by omega⟩, fun s => ?_⟩
    Γ hΓ C M U hU hne h0
  rw [Fin.le_def]
  show s.val ≤ n - 1
  omega

open scoped Classical in
/-- Grouping heads by score matrix: if every `Γ_j` is one of the distinct matrices `G_i`, then
`∑_i P_{G_i}(h) h (∑_{j : Γ_j = G_i} C_j) = ∑_j P_{Γ_j}(h) h C_j`. -/
private theorem sum_group_ahi (sees : T → T → Prop) [DecidableRel sees] {ι H : Type*}
    [Fintype ι] [Fintype H] (G : ι → Matrix d d ℝ) (hG : Function.Injective G)
    (Γ C : H → Matrix d d ℝ) (hS : ∀ j, ∃ i, G i = Γ j) (h : Matrix T d ℝ) :
    ∑ i, attnWeights sees (h * G i * hᵀ) * h * (∑ j, if Γ j = G i then C j else 0)
      = attnHeads sees Γ C h := by
  have e1 : ∀ i, attnWeights sees (h * G i * hᵀ) * h * (∑ j, if Γ j = G i then C j else 0)
      = ∑ j, if Γ j = G i then attnWeights sees (h * Γ j * hᵀ) * h * C j else 0 := by
    intro i
    rw [Matrix.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : Γ j = G i
    · simp only [hj, ite_true]
    · simp only [hj, ite_false, Matrix.mul_zero]
  simp only [e1]
  rw [Finset.sum_comm]
  unfold attnHeads
  refine Finset.sum_congr rfl fun j _ => ?_
  -- exactly one `i` has `G_i = Γ_j`
  obtain ⟨i₀, hi₀⟩ := hS j
  rw [Finset.sum_eq_single i₀ (fun i _ hi => ite_eq_right_iff.2 fun hc => absurd
    (hG (hc.symm.trans hi₀.symm)) hi) (fun h' => absurd (Finset.mem_univ _) h')]
  simp only [hi₀, ite_true]

open scoped Classical in
/-- **Proposition A.15 of the absorb paper (The softmaxes must match), for attention blocks given
by their score matrices and value–output products:** on at least three tokens, with a mask in
which some token sees every token, if `h M + B(h) = B'(h)` for all `h` in a nonempty open set,
then `M = 0`, and for every matrix `G` the heads with the score matrix `G` have the same sum of
value–output products in `B` as in `B'`. -/
theorem attnHeads_sum_eq_of_mul_add_eq (sees : T → T → Prop) [DecidableRel sees]
    (hT : 3 ≤ Fintype.card T) (hsees : ∃ t₀, ∀ s, sees t₀ s) {H H' : Type*} [Fintype H]
    [Fintype H'] (Γ C : H → Matrix d d ℝ) (Γ' C' : H' → Matrix d d ℝ) (M : Matrix d d ℝ)
    (U : Set (Matrix T d ℝ)) (hU : IsOpen U) (hne : U.Nonempty)
    (h0 : ∀ h ∈ U, h * M + attnHeads sees Γ C h = attnHeads sees Γ' C' h) :
    M = 0 ∧ ∀ G : Matrix d d ℝ,
      (∑ i, if Γ i = G then C i else 0) = ∑ i, if Γ' i = G then C' i else 0 := by
  classical
  -- the score matrices that occur, indexed by `Fin m`
  set S : Finset (Matrix d d ℝ) := Finset.univ.image Γ ∪ Finset.univ.image Γ' with hS
  let e : S ≃ Fin (Fintype.card S) := Fintype.equivFin S
  let G₀ : Fin (Fintype.card S) → Matrix d d ℝ := fun i => (e.symm i : Matrix d d ℝ)
  have hG₀ : Function.Injective G₀ := fun i j hij => e.symm.injective (Subtype.ext hij)
  have hrange : ∀ A, A ∈ S → ∃ i, G₀ i = A := fun A hA => ⟨e ⟨A, hA⟩, by
    show ((e.symm (e ⟨A, hA⟩) : S) : Matrix d d ℝ) = A
    rw [Equiv.symm_apply_apply]⟩
  have hmemΓ : ∀ j, Γ j ∈ S := fun j =>
    Finset.mem_union_left _ (Finset.mem_image_of_mem Γ (Finset.mem_univ j))
  have hmemΓ' : ∀ j, Γ' j ∈ S := fun j =>
    Finset.mem_union_right _ (Finset.mem_image_of_mem Γ' (Finset.mem_univ j))
  -- the coefficient of the score matrix `G₀ i`: the heads of `B` minus the heads of `B'`
  obtain ⟨hM, hC⟩ := attnHeads_identifiable sees hT hsees G₀ hG₀
    (fun i => (∑ j, if Γ j = G₀ i then C j else 0) - ∑ j, if Γ' j = G₀ i then C' j else 0)
    M U hU hne (fun h hh => by
      -- `h M + ∑_i P_{G₀ i}(h) h C̃_i = h M + B(h) - B'(h) = 0`
      simp only [Matrix.mul_sub, Finset.sum_sub_distrib]
      rw [sum_group_ahi sees G₀ hG₀ Γ C (fun j => hrange _ (hmemΓ j)) h,
        sum_group_ahi sees G₀ hG₀ Γ' C' (fun j => hrange _ (hmemΓ' j)) h, ← add_sub_assoc,
        h0 h hh, sub_self])
  refine ⟨hM, fun G => ?_⟩
  by_cases hG : G ∈ S
  · -- `G = G₀ i`, and `C̃_i = 0`
    obtain ⟨i, hi⟩ := hrange G hG
    have h1 := hC i
    rw [hi] at h1
    exact sub_eq_zero.mp h1
  · -- no head has the score matrix `G`
    rw [Finset.sum_eq_zero fun j _ =>
        ite_eq_right_iff.2 fun (h : Γ j = G) => absurd (h ▸ hmemΓ j) hG,
      Finset.sum_eq_zero fun j _ =>
        ite_eq_right_iff.2 fun (h : Γ' j = G) => absurd (h ▸ hmemΓ' j) hG]

open scoped Classical in
/-- **Proposition A.15 of the absorb paper (The softmaxes must match):** for attention blocks
`B_θ`, `B_{θ′}` with any numbers of heads and any head dimensions, on at least three tokens, with
a mask in which some token sees every token: if `h M + B_θ(h) = B_{θ′}(h)` for all `h` in a
nonempty open set, then `M = 0`, and for every matrix `G` the heads with the score matrix
`W_Q W_K^⊤ / √d_h = G` have the same sum of value–output products `W_V W_O` in `B_θ` as in
`B_{θ′}`. -/
theorem attentionBlock_sum_eq_of_mul_add_eq (sees : T → T → Prop) [DecidableRel sees]
    (hT : 3 ≤ Fintype.card T) (hsees : ∃ t₀, ∀ s, sees t₀ s) {H dh H' dh' : Type*} [Fintype H]
    [Fintype dh] [Fintype H'] [Fintype dh'] (WQ WK WV : H → Matrix d dh ℝ)
    (WO : H → Matrix dh d ℝ) (WQ' WK' WV' : H' → Matrix d dh' ℝ) (WO' : H' → Matrix dh' d ℝ)
    (M : Matrix d d ℝ) (U : Set (Matrix T d ℝ)) (hU : IsOpen U) (hne : U.Nonempty)
    (h0 : ∀ h ∈ U, h * M + attentionBlock sees WQ WK WV WO h
      = attentionBlock sees WQ' WK' WV' WO' h) :
    M = 0 ∧ ∀ G : Matrix d d ℝ,
      (∑ i, if (Real.sqrt (Fintype.card dh))⁻¹ • (WQ i * (WK i)ᵀ) = G then WV i * WO i else 0)
        = ∑ i, if (Real.sqrt (Fintype.card dh'))⁻¹ • (WQ' i * (WK' i)ᵀ) = G
            then WV' i * WO' i else 0 := by
  -- the blocks of equation (4) are `attnHeads` with `Γ_i = W_{Q,i} W_{K,i}ᵀ / √d_h`,
  -- `C_i = W_{V,i} W_{O,i}`
  unfold attentionBlock at h0
  exact attnHeads_sum_eq_of_mul_add_eq sees hT hsees _ _ _ _ M U hU hne h0

end Skips
