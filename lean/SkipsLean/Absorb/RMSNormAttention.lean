import SkipsLean.Absorb.RMSNormKinds
import SkipsLean.Network.Sum

/-!
# Under RMSNorm a residual network equals no skipless network: attention blocks and transformers

Paper ("Can an MLP Absorb Its Skip Connection Exactly?"): Theorem 4.3. "Consider pre-RMSNorm
networks, with `ε ≥ 0` and blocks of any kind and width. For almost every choice of weights, a
residual network equals no skipless network, whatever its depth, widths and kinds of blocks." And
after it: "The theorem covers pre-RMSNorm transformers, which alternate attention and MLP blocks."
Appendix A.3: "Each block is linear in its write, which for an attention block holds the matrices
`W_{O,i}`: block `ℓ` adds `a_ℓ W_write^ℓ` to the hidden state, where `a_ℓ` […] holds the
activations of its hidden units, or for an attention block the matrices `P_{Γ_i}(n) n W_{V,i}` of
its heads side by side."

`Absorb/RMSNormGeneric.lean` proves the theorem for a residual network of locally Lipschitz blocks
in which, for almost every choice of weights, some block has a nonzero output at some normalized
state (`SomeBlockNonzero`), and `Absorb/RMSNormKinds.lean` states it for the seven kinds of MLP
block. Here the residual network is

* a network of attention blocks (`Arch.attention`, any mask): some block has a head of positive
  width, and some token sees a token (at a state whose tokens are all equal, a head gives a token
  that sees some token the value of that token);
* a network whose blocks are attention blocks and MLP blocks in any order, or attention blocks
  and gated blocks (`Arch.sum`, `Network/Sum.lean`): some block has a hidden unit.

The scope is that of the paper, `d_in, d_out ≥ d ≥ 2`. The skipless network is of any kind (an
arbitrary `Arch`, so also a network of attention blocks or a transformer, whose blocks are locally
Lipschitz by `locallyLipschitz_f_attention` and `locallyLipschitz_f_sum`), of any depth `L'`,
model dimension `d'` and widths; for `ε > 0` it may have its own constant `ε' > 0` and its blocks
are locally Lipschitz; for `ε = 0` its blocks are continuous and equality is in the paper's sense
for `ε = 0` (no dense set of inputs at which both networks are defined and agree).
-/

namespace Skips

open Matrix MeasureTheory Filter
open scoped Matrix.Norms.Elementwise Topology

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {sees : T → T → Prop} [DecidableRel sees]
variable {H dh : Fin L → Type} [∀ ℓ, Fintype (H ℓ)] [∀ ℓ, Fintype (dh ℓ)]
variable {σ : ℝ → ℝ} {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]

/-! ### Attention blocks -/

omit [Fintype d] [DecidableEq d] in
/-- The map of an attention block is locally Lipschitz (it is real-analytic). -/
theorem locallyLipschitz_f_attention (χ : Matrix T d ℝ → Matrix T d ℝ) (ℓ : Fin L) :
    LocallyLipschitz ((Arch.attention sees χ H dh).f ℓ) := by
  -- real-analytic, hence `C¹`, hence locally Lipschitz
  exact ((analyticOnNhd_f_attention sees χ H dh ℓ).contDiff (n := 1)).locallyLipschitz

omit [Fintype T] [DecidableEq d] in
/-- Helper: for two columns `j₁, j₂` of the read of block `ℓ` (possibly equal), their dot product
is not `0` for almost every choice of weights: it is a polynomial in the weights, equal to `d` at
the reads with all entries `1`. -/
private theorem ae_dot_cols_ne_zero_rat [Nonempty d] (A : Arch T d L)
    (μ : Measure (Params A dIn dOut)) [μ.IsAddHaarMeasure] (ℓ : Fin L) (j₁ j₂ : A.r ℓ) :
    ∀ᵐ θ ∂μ, (fun a => θ.read ℓ a j₁) ⬝ᵥ (fun a => θ.read ℓ a j₂) ≠ 0 := by
  -- the entry `(a, j)` of the read of block `ℓ`, a linear functional of the weights
  let l : d → A.r ℓ → Params A dIn dOut →ₗ[ℝ] ℝ := fun a j =>
    (Matrix.entryLinearMap ℝ ℝ a j).comp (Params.linRead (A := A) (dIn := dIn) (dOut := dOut) ℓ)
  have hg : AnalyticOnNhd ℝ (fun θ : Params A dIn dOut => ∑ a, l a j₁ θ * l a j₂ θ) Set.univ :=
    Finset.analyticOnNhd_fun_sum _ fun a _ =>
      (analyticOnNhd_linear (l a j₁)).mul (analyticOnNhd_linear (l a j₂))
  have hne : ∃ θ : Params A dIn dOut, ∑ a, l a j₁ θ * l a j₂ θ ≠ 0 := by
    refine ⟨⟨0, fun _ => Matrix.of fun _ _ => 1, 0, 0⟩, ?_⟩
    show ∑ _a : d, (1 : ℝ) * 1 ≠ 0
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, mul_one]
    exact Nat.cast_ne_zero.2 Fintype.card_ne_zero
  -- an analytic function that is not identically zero is nonzero almost everywhere
  filter_upwards [ae_ne_zero_of_analytic μ hg hne] with θ hθ
  exact hθ

omit [DecidableEq d] in
/-- Helper (a copy of a private helper of `Absorb/RMSNormGeneric.lean`): a nonzero vector `c` has
`c ⬝ᵥ c > 0` and a positive multiple `λ c` with `(λ c) ⬝ᵥ (λ c) = d`. -/
private theorem exists_pos_smul_normalized_rat [Nonempty d] {c : d → ℝ} (hc : c ≠ 0) :
    0 < c ⬝ᵥ c ∧ ∃ lam : ℝ, 0 < lam ∧ (lam • c) ⬝ᵥ (lam • c) = (Fintype.card d : ℝ) := by
  have hs : 0 < c ⬝ᵥ c := lt_of_le_of_ne (Finset.sum_nonneg fun i _ => mul_self_nonneg (c i))
    (Ne.symm (dotProduct_self_eq_zero.not.2 hc))
  have hd : (0 : ℝ) < Fintype.card d := Nat.cast_pos.2 Fintype.card_pos
  refine ⟨hs, Real.sqrt (Fintype.card d / (c ⬝ᵥ c)), Real.sqrt_pos.2 (div_pos hd hs), ?_⟩
  rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc,
    Real.mul_self_sqrt (div_pos hd hs).le, div_mul_cancel₀ _ hs.ne']

omit [Fintype d] [DecidableEq d] in
/-- Helper: row `t` of the weights sums to `1` when token `t` sees some token (the denominator
is positive). -/
private theorem attnWeights_sum_rat (Z : Matrix T T ℝ) (t : T) (ht : ∃ s, sees t s) :
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
/-- Helper: if the value coordinate `k` of head `i` is the same number `v` at every token, entry
`(t, (i, k))` of the output of the block is `v` when token `t` sees some token (the weights of
row `t` sum to `1`). -/
private theorem f_attention_entry_const_rat (χ : Matrix T d ℝ → Matrix T d ℝ) (ℓ : Fin L)
    (M : Matrix T (H ℓ × (dh ℓ ⊕ (dh ℓ ⊕ dh ℓ))) ℝ) (i : H ℓ) (k : dh ℓ) (v : ℝ)
    (hv : ∀ s, M s (i, Sum.inr (Sum.inr k)) = v) (t s : T) (hts : sees t s) :
    (Arch.attention sees χ H dh).f ℓ M t (i, k) = v := by
  show ∑ s', attnWeights sees _ t s' * M s' (i, Sum.inr (Sum.inr k)) = v
  simp only [hv, ← Finset.sum_mul, attnWeights_sum_rat _ t ⟨s, hts⟩, one_mul]

/-- For a network of attention blocks in which some block has a head of positive width, and a
token `t` that sees a token `s`: for almost every choice of weights, some block has a nonzero
output at some normalized state (a value column `c ≠ 0` of the read and the state with all rows
`√d c / ‖c‖`: the head gives token `t` the value of this row). -/
theorem ae_someBlockNonzero_attention [Nonempty d] {χ : Matrix T d ℝ → Matrix T d ℝ}
    (hhead : ∃ ℓ, Nonempty (H ℓ) ∧ Nonempty (dh ℓ)) (t s : T) (hts : sees t s)
    (μ : Measure (Params (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut))
    [μ.IsAddHaarMeasure] :
    ∀ᵐ θ ∂μ, SomeBlockNonzero (Arch.attention sees χ H dh) θ := by
  obtain ⟨ℓ, ⟨i⟩, ⟨k⟩⟩ := hhead
  -- the value column `c` of coordinate `k` of head `i` is not `0`, for almost every `θ`
  filter_upwards [ae_dot_cols_ne_zero_rat _ μ ℓ (i, Sum.inr (Sum.inr k))
    (i, Sum.inr (Sum.inr k))] with θ hθ
  set c : d → ℝ := fun a => θ.read ℓ a (i, Sum.inr (Sum.inr k)) with hc
  have hc0 : c ≠ 0 := fun h0 => hθ (by rw [h0, zero_dotProduct])
  -- the state `n̄` with every row `λ c`
  obtain ⟨hs, lam, hlam, hn⟩ := exists_pos_smul_normalized_rat hc0
  refine ⟨ℓ, Matrix.of fun _ => lam • c, fun _ => hn, fun h => ?_⟩
  -- every token has the value `λ (c ⬝ᵥ c)` in coordinate `k` of head `i`
  have hv : ∀ s', (Matrix.of (fun _ : T => lam • c) * θ.read ℓ) s' (i, Sum.inr (Sum.inr k))
      = lam * (c ⬝ᵥ c) := by
    intro s'
    rw [← smul_eq_mul, ← smul_dotProduct]
    rfl
  -- so the head gives token `t`, which sees `s`, the value `λ (c ⬝ᵥ c) ≠ 0`
  have he := f_attention_entry_const_rat χ ℓ _ i k _ hv t s hts
  exact mul_ne_zero hlam.ne' hs.ne' (he.symm.trans (congrFun (congrFun h t) (i, k)))

/-- **Theorem 4.3 for residual networks of attention blocks, `ε > 0`.** For almost every choice of
weights (`d_in, d_out ≥ d ≥ 2`, some block has a head of positive width, some token sees a token),
the residual network equals no pre-RMSNorm skipless network with locally Lipschitz blocks of any
kind. -/
theorem ae_ne_skipless_rmsNorm_attention {ε : ℝ} (hε : 0 < ε)
    (hhead : ∃ ℓ, Nonempty (H ℓ) ∧ Nonempty (dh ℓ)) (t s : T) (hts : sees t s)
    (μ : Measure (Params (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut))
    [μ.IsAddHaarMeasure]
    (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, ∀ (L' : ℕ) (d' : Type) [Fintype d'] (A' : Arch T d' L') (ε' : ℝ), 0 < ε' →
      A'.χ = rmsNorm ε' → (∀ ℓ, LocallyLipschitz (A'.f ℓ)) → ∀ θ' : Params A' dIn dOut,
        ∃ X : Matrix T dIn ℝ,
          eval (Arch.attention sees (rmsNorm ε) H dh) 1 θ X ≠ eval A' 0 θ' X := by
  have : Nonempty d := Fintype.card_pos_iff.1 (by omega)
  exact ae_ne_skipless_rmsNorm hε _ rfl (locallyLipschitz_f_attention _) μ hd hdIn hdOut
    (ae_someBlockNonzero_attention hhead t s hts μ)

/-- **Theorem 4.3 for residual networks of attention blocks, `ε = 0`.** For almost every choice of
weights, the residual network equals no pre-RMSNorm skipless network with `ε = 0` and continuous
blocks. -/
theorem ae_not_dense_eq_skipless_rmsNorm_zero_attention
    (hhead : ∃ ℓ, Nonempty (H ℓ) ∧ Nonempty (dh ℓ)) (t s : T) (hts : sees t s)
    (μ : Measure (Params (Arch.attention (T := T) (d := d) sees (rmsNorm 0) H dh) dIn dOut))
    [μ.IsAddHaarMeasure]
    (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, ∀ (L' : ℕ) (d' : Type) [Fintype d'] (A' : Arch T d' L'), A'.χ = rmsNorm 0 →
      (∀ ℓ, Continuous (A'.f ℓ)) → ∀ θ' : Params A' dIn dOut,
        ¬ ∃ S : Set (Matrix T dIn ℝ), Dense S ∧
          ∀ X ∈ S, DefinedAt (Arch.attention sees (rmsNorm 0) H dh) 1 θ X ∧ DefinedAt A' 0 θ' X ∧
            eval (Arch.attention sees (rmsNorm 0) H dh) 1 θ X = eval A' 0 θ' X := by
  have : Nonempty d := Fintype.card_pos_iff.1 (by omega)
  exact ae_not_dense_eq_skipless_rmsNorm_zero _ rfl (locallyLipschitz_f_attention _) μ hd hdIn
    hdOut (ae_someBlockNonzero_attention hhead t s hts μ)

/-! ### Transformers: attention blocks and MLP blocks -/

/-- For a network of attention blocks and MLP blocks whose activation is nonzero on the positive
reals, in which some block has a hidden unit: for almost every choice of weights, some block has a
nonzero output at some normalized state. -/
theorem ae_someBlockNonzero_attention_mlp [Nonempty T] [Nonempty d]
    {χ : Matrix T d ℝ → Matrix T d ℝ} (hσ : ∀ z, 0 < z → σ z ≠ 0) (hhid : ∃ ℓ, Nonempty (hid ℓ))
    (μ : Measure (Params ((Arch.attention (T := T) (d := d) sees χ H dh).sum
      (Arch.mlp σ χ hid)) dIn dOut)) [μ.IsAddHaarMeasure] :
    ∀ᵐ θ ∂μ, SomeBlockNonzero ((Arch.attention sees χ H dh).sum (Arch.mlp σ χ hid)) θ := by
  obtain ⟨ℓ, ⟨i⟩⟩ := hhid
  obtain t₀ : T := Classical.arbitrary T
  -- the read column `c` of unit `i` (column `Sum.inr i`) is not `0`, for almost every `θ`
  filter_upwards [ae_dot_cols_ne_zero_rat _ μ ℓ (Sum.inr i) (Sum.inr i)] with θ hθ
  set c : d → ℝ := fun a => θ.read ℓ a (Sum.inr i) with hc
  have hc0 : c ≠ 0 := fun h0 => hθ (by rw [h0, zero_dotProduct])
  -- the state `n̄` with every row `λ c`
  obtain ⟨hs, lam, hlam, hn⟩ := exists_pos_smul_normalized_rat hc0
  refine ⟨ℓ, Matrix.of fun _ => lam • c, fun _ => hn, fun h => hσ _ (mul_pos hlam hs) ?_⟩
  -- entry `(t₀, Sum.inr i)` of the output is `σ` of the argument `λ (c ⬝ᵥ c) > 0` of unit `i`
  have harg : (Matrix.of (fun _ : T => lam • c) * θ.read ℓ) t₀ (Sum.inr i) = lam * (c ⬝ᵥ c) := by
    rw [← smul_eq_mul, ← smul_dotProduct]
    rfl
  rw [← harg]
  exact congrFun (congrFun h t₀) (Sum.inr i)

/-- **Theorem 4.3 for residual networks of attention blocks and MLP blocks, `ε > 0`,** with an
activation that is locally Lipschitz and nonzero on the positive reals: for almost every choice of
weights (`d_in, d_out ≥ d ≥ 2`, some block has a hidden unit), the residual network equals no
pre-RMSNorm skipless network with locally Lipschitz blocks of any kind. -/
theorem ae_ne_skipless_rmsNorm_attention_mlp [Nonempty T] {ε : ℝ} (hε : 0 < ε)
    (hσ : ∀ z, 0 < z → σ z ≠ 0) (hσL : LocallyLipschitz σ) (hhid : ∃ ℓ, Nonempty (hid ℓ))
    (μ : Measure (Params ((Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh).sum
      (Arch.mlp σ (rmsNorm ε) hid)) dIn dOut)) [μ.IsAddHaarMeasure]
    (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, ∀ (L' : ℕ) (d' : Type) [Fintype d'] (A' : Arch T d' L') (ε' : ℝ), 0 < ε' →
      A'.χ = rmsNorm ε' → (∀ ℓ, LocallyLipschitz (A'.f ℓ)) → ∀ θ' : Params A' dIn dOut,
        ∃ X : Matrix T dIn ℝ,
          eval ((Arch.attention sees (rmsNorm ε) H dh).sum (Arch.mlp σ (rmsNorm ε) hid)) 1 θ X
            ≠ eval A' 0 θ' X := by
  have : Nonempty d := Fintype.card_pos_iff.1 (by omega)
  exact ae_ne_skipless_rmsNorm hε _ rfl
    (fun ℓ => locallyLipschitz_f_sum (locallyLipschitz_f_attention _ ℓ)
      (locallyLipschitz_f_mlp hσL ℓ)) μ hd hdIn hdOut
    (ae_someBlockNonzero_attention_mlp hσ hhid μ)

/-- **Theorem 4.3 for residual networks of attention blocks and MLP blocks, `ε = 0`.** -/
theorem ae_not_dense_eq_skipless_rmsNorm_zero_attention_mlp [Nonempty T]
    (hσ : ∀ z, 0 < z → σ z ≠ 0) (hσL : LocallyLipschitz σ) (hhid : ∃ ℓ, Nonempty (hid ℓ))
    (μ : Measure (Params ((Arch.attention (T := T) (d := d) sees (rmsNorm 0) H dh).sum
      (Arch.mlp σ (rmsNorm 0) hid)) dIn dOut)) [μ.IsAddHaarMeasure]
    (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, ∀ (L' : ℕ) (d' : Type) [Fintype d'] (A' : Arch T d' L'), A'.χ = rmsNorm 0 →
      (∀ ℓ, Continuous (A'.f ℓ)) → ∀ θ' : Params A' dIn dOut,
        ¬ ∃ S : Set (Matrix T dIn ℝ), Dense S ∧
          ∀ X ∈ S,
            DefinedAt ((Arch.attention sees (rmsNorm 0) H dh).sum (Arch.mlp σ (rmsNorm 0) hid))
                1 θ X ∧ DefinedAt A' 0 θ' X ∧
              eval ((Arch.attention sees (rmsNorm 0) H dh).sum (Arch.mlp σ (rmsNorm 0) hid)) 1 θ X
                = eval A' 0 θ' X := by
  have : Nonempty d := Fintype.card_pos_iff.1 (by omega)
  exact ae_not_dense_eq_skipless_rmsNorm_zero _ rfl
    (fun ℓ => locallyLipschitz_f_sum (locallyLipschitz_f_attention _ ℓ)
      (locallyLipschitz_f_mlp hσL ℓ)) μ hd hdIn hdOut
    (ae_someBlockNonzero_attention_mlp hσ hhid μ)

/-! ### Transformers: attention blocks and gated blocks -/

/-- For a network of attention blocks and gated blocks whose gate is nonzero on the positive
reals, in which some block has a hidden unit: for almost every choice of weights, some block has a
nonzero output at some normalized state. -/
theorem ae_someBlockNonzero_attention_gated [Nonempty T] [Nonempty d]
    {χ : Matrix T d ℝ → Matrix T d ℝ} (hσ : ∀ z, 0 < z → σ z ≠ 0) (hhid : ∃ ℓ, Nonempty (hid ℓ))
    (μ : Measure (Params ((Arch.attention (T := T) (d := d) sees χ H dh).sum
      (Arch.gated σ χ hid)) dIn dOut)) [μ.IsAddHaarMeasure] :
    ∀ᵐ θ ∂μ, SomeBlockNonzero ((Arch.attention sees χ H dh).sum (Arch.gated σ χ hid)) θ := by
  obtain ⟨ℓ, ⟨i⟩⟩ := hhid
  obtain t₀ : T := Classical.arbitrary T
  -- the gate column `c` and the value column `e` of unit `i` have `c ⬝ᵥ e ≠ 0` for almost every
  -- choice of weights
  filter_upwards [ae_dot_cols_ne_zero_rat _ μ ℓ (Sum.inr (Sum.inl i)) (Sum.inr (Sum.inr i))]
    with θ hθ
  set c : d → ℝ := fun a => θ.read ℓ a (Sum.inr (Sum.inl i)) with hc
  set e : d → ℝ := fun a => θ.read ℓ a (Sum.inr (Sum.inr i)) with he
  have hc0 : c ≠ 0 := fun h0 => hθ (by rw [h0, zero_dotProduct])
  -- the state `n̄` with every row `λ c`
  obtain ⟨hs, lam, hlam, hn⟩ := exists_pos_smul_normalized_rat hc0
  refine ⟨ℓ, Matrix.of fun _ => lam • c, fun _ => hn, fun h => ?_⟩
  -- entry `(t₀, Sum.inr i)` of the output is `σ(λ (c ⬝ᵥ c)) λ (c ⬝ᵥ e) ≠ 0`
  have hgate : (Matrix.of (fun _ : T => lam • c) * θ.read ℓ) t₀ (Sum.inr (Sum.inl i))
      = lam * (c ⬝ᵥ c) := by
    rw [← smul_eq_mul, ← smul_dotProduct]
    rfl
  have hval : (Matrix.of (fun _ : T => lam • c) * θ.read ℓ) t₀ (Sum.inr (Sum.inr i))
      = lam * (c ⬝ᵥ e) := by
    rw [← smul_eq_mul, ← smul_dotProduct]
    rfl
  have h1 : σ ((Matrix.of (fun _ : T => lam • c) * θ.read ℓ) t₀ (Sum.inr (Sum.inl i))) *
      (Matrix.of (fun _ : T => lam • c) * θ.read ℓ) t₀ (Sum.inr (Sum.inr i)) = 0 :=
    congrFun (congrFun h t₀) (Sum.inr i)
  rw [hgate, hval] at h1
  exact mul_ne_zero (hσ _ (mul_pos hlam hs)) (mul_ne_zero hlam.ne' hθ) h1

/-- **Theorem 4.3 for residual networks of attention blocks and gated blocks, `ε > 0`,** with a
gate that is locally Lipschitz and nonzero on the positive reals. -/
theorem ae_ne_skipless_rmsNorm_attention_gated [Nonempty T] {ε : ℝ} (hε : 0 < ε)
    (hσ : ∀ z, 0 < z → σ z ≠ 0) (hσL : LocallyLipschitz σ) (hhid : ∃ ℓ, Nonempty (hid ℓ))
    (μ : Measure (Params ((Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh).sum
      (Arch.gated σ (rmsNorm ε) hid)) dIn dOut)) [μ.IsAddHaarMeasure]
    (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, ∀ (L' : ℕ) (d' : Type) [Fintype d'] (A' : Arch T d' L') (ε' : ℝ), 0 < ε' →
      A'.χ = rmsNorm ε' → (∀ ℓ, LocallyLipschitz (A'.f ℓ)) → ∀ θ' : Params A' dIn dOut,
        ∃ X : Matrix T dIn ℝ,
          eval ((Arch.attention sees (rmsNorm ε) H dh).sum (Arch.gated σ (rmsNorm ε) hid)) 1 θ X
            ≠ eval A' 0 θ' X := by
  have : Nonempty d := Fintype.card_pos_iff.1 (by omega)
  exact ae_ne_skipless_rmsNorm hε _ rfl
    (fun ℓ => locallyLipschitz_f_sum (locallyLipschitz_f_attention _ ℓ)
      (locallyLipschitz_f_gated hσL ℓ)) μ hd hdIn hdOut
    (ae_someBlockNonzero_attention_gated hσ hhid μ)

/-- **Theorem 4.3 for residual networks of attention blocks and gated blocks, `ε = 0`.** -/
theorem ae_not_dense_eq_skipless_rmsNorm_zero_attention_gated [Nonempty T]
    (hσ : ∀ z, 0 < z → σ z ≠ 0) (hσL : LocallyLipschitz σ) (hhid : ∃ ℓ, Nonempty (hid ℓ))
    (μ : Measure (Params ((Arch.attention (T := T) (d := d) sees (rmsNorm 0) H dh).sum
      (Arch.gated σ (rmsNorm 0) hid)) dIn dOut)) [μ.IsAddHaarMeasure]
    (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, ∀ (L' : ℕ) (d' : Type) [Fintype d'] (A' : Arch T d' L'), A'.χ = rmsNorm 0 →
      (∀ ℓ, Continuous (A'.f ℓ)) → ∀ θ' : Params A' dIn dOut,
        ¬ ∃ S : Set (Matrix T dIn ℝ), Dense S ∧
          ∀ X ∈ S,
            DefinedAt ((Arch.attention sees (rmsNorm 0) H dh).sum (Arch.gated σ (rmsNorm 0) hid))
                1 θ X ∧ DefinedAt A' 0 θ' X ∧
              eval ((Arch.attention sees (rmsNorm 0) H dh).sum (Arch.gated σ (rmsNorm 0) hid))
                  1 θ X
                = eval A' 0 θ' X := by
  have : Nonempty d := Fintype.card_pos_iff.1 (by omega)
  exact ae_not_dense_eq_skipless_rmsNorm_zero _ rfl
    (fun ℓ => locallyLipschitz_f_sum (locallyLipschitz_f_attention _ ℓ)
      (locallyLipschitz_f_gated hσL ℓ)) μ hd hdIn hdOut
    (ae_someBlockNonzero_attention_gated hσ hhid μ)

/-! ### The named kinds: GELU and SwiGLU transformers -/

/-- **Theorem 4.3 for a pre-RMSNorm transformer of attention blocks and GELU blocks, `ε > 0`.** -/
theorem ae_ne_skipless_rmsNorm_attention_gelu [Nonempty T] {ε : ℝ} (hε : 0 < ε)
    (hhid : ∃ ℓ, Nonempty (hid ℓ))
    (μ : Measure (Params ((Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh).sum
      (Arch.mlp gelu (rmsNorm ε) hid)) dIn dOut)) [μ.IsAddHaarMeasure]
    (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, ∀ (L' : ℕ) (d' : Type) [Fintype d'] (A' : Arch T d' L') (ε' : ℝ), 0 < ε' →
      A'.χ = rmsNorm ε' → (∀ ℓ, LocallyLipschitz (A'.f ℓ)) → ∀ θ' : Params A' dIn dOut,
        ∃ X : Matrix T dIn ℝ,
          eval ((Arch.attention sees (rmsNorm ε) H dh).sum (Arch.mlp gelu (rmsNorm ε) hid)) 1 θ X
            ≠ eval A' 0 θ' X := by
  exact ae_ne_skipless_rmsNorm_attention_mlp hε (fun z hz => gelu_ne_zero_of_pos hz)
    locallyLipschitz_gelu hhid μ hd hdIn hdOut

/-- **Theorem 4.3 for a pre-RMSNorm transformer of attention blocks and SwiGLU blocks,
`ε > 0`.** -/
theorem ae_ne_skipless_rmsNorm_attention_swiglu [Nonempty T] {ε : ℝ} (hε : 0 < ε)
    (hhid : ∃ ℓ, Nonempty (hid ℓ))
    (μ : Measure (Params ((Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh).sum
      (Arch.gated silu (rmsNorm ε) hid)) dIn dOut)) [μ.IsAddHaarMeasure]
    (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, ∀ (L' : ℕ) (d' : Type) [Fintype d'] (A' : Arch T d' L') (ε' : ℝ), 0 < ε' →
      A'.χ = rmsNorm ε' → (∀ ℓ, LocallyLipschitz (A'.f ℓ)) → ∀ θ' : Params A' dIn dOut,
        ∃ X : Matrix T dIn ℝ,
          eval ((Arch.attention sees (rmsNorm ε) H dh).sum (Arch.gated silu (rmsNorm ε) hid))
              1 θ X
            ≠ eval A' 0 θ' X := by
  exact ae_ne_skipless_rmsNorm_attention_gated hε (fun z hz => silu_ne_zero_of_pos hz)
    locallyLipschitz_silu hhid μ hd hdIn hdOut

end Skips
