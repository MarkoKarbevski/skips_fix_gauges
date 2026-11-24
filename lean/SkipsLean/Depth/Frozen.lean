import SkipsLean.Depth.Cones
import SkipsLean.Depth.BlockIdentityGated

/-!
# The frozen network

Paper (dimension): Appendix D.5, "The frozen network". "In the case (n), for gated blocks and a
good `θ`, let `𝓑°_{>k}` be the network after `h_k` with the gates of all its blocks frozen:

  `𝓑°_{>L}(h) = h D`,   `𝓑°_{>k−1}(h) = 𝓑°_{>k}(g°_k(h))`.

It is a polynomial map of `h` and of the weights. Lemmas D.2 and D.3 hold for `𝓑°_{>k}` in the
place of `𝓑_{>k}`, with an open dense set `U°_k` of rows and with the same proofs, in which
`g°_{k+1}` takes the place of `g_{k+1}`." Here `g°_ℓ(n) = ∑_{j ∈ A_ℓ} (n c_j) ι_j(n) a_j` is the
block with its gates frozen, a quadratic map for a gated block: `g°_ℓ(λ n) = λ² g°_ℓ(n)`.

In Lean the frozen network is the network of an architecture of its own, `Arch.frozen A`, whose
block `ℓ` sends the gate `z_i` and the value `w_i` of a hidden unit to `z_i w_i` if `i ∈ A ℓ` and to
`0` otherwise; then `𝓑°_{>k}` is `suffix (Arch.frozen A) 0 θ k`, and Lemmas D.2 and D.3 for it are
the statements of `Depth/Suffix.lean` for this architecture, at a regular parameter. The weights of
a gated network are weights of the frozen network with the same matrices (`Params.toFrozen`).

Stated here: these definitions; that the frozen block is `frozenGated` on every row; that a good
`θ` is regular for the frozen network; that the frozen network is homogeneous,
`𝓑°_{>k}(c h) = c^{2^{L−k}} 𝓑°_{>k}(h)`, and what this gives for its derivatives and for the left
side of the identity for one block. The left side is written for the outputs `v` of the hidden
units and their derivative `vdot` (`writeLHS`, for any architecture): for a gated block it is the
`𝓛` of equation (27) with `v = ŵ = w̃ ⊙ ι` and `vdot = w̃' ⊙ ż^g ⊙ ι + w̃ ⊙ ż^v`.
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise Topology

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]
variable {σ : ℝ → ℝ} {χ : Matrix T d ℝ → Matrix T d ℝ}

/-- **The network of gated blocks with its gates frozen** on the active sets `A`, without
normalization: the fixed map of block `ℓ` sends the gate `z_i` and the value `w_i` of a hidden unit
to `z_i w_i` if `i ∈ A ℓ`, and to `0` otherwise. The read is `[W_g | W_v]` as for `Arch.gated`. -/
noncomputable abbrev Arch.frozen (A : ∀ ℓ, Finset (hid ℓ)) : Arch T d L where
  r ℓ := hid ℓ ⊕ hid ℓ
  w := hid
  f ℓ M := Matrix.of fun t =>
    Set.indicator (↑(A ℓ) : Set (hid ℓ)) fun i => M t (Sum.inl i) * M t (Sum.inr i)
  χ := id

/-- The weights of a network of gated blocks, as weights of the frozen network: the same
matrices. -/
def Params.toFrozen (A : ∀ ℓ, Finset (hid ℓ))
    (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut) :
    Params (Arch.frozen (T := T) (d := d) A) dIn dOut where
  E := θ.E
  read := θ.read
  write := θ.write
  D := θ.D

/-- **The left side of the identity for one block, in the outputs of its hidden units:**
`𝐃𝓑(v V) (vdot V + v η_V) + 𝐃_θ 𝓑(v V) η`, for block `k` with the write `V` and the network `𝓑`
after it. Here `v` stands for the outputs of the hidden units and `vdot` for their derivative. -/
noncomputable def writeLHS (A : Arch T d L) (θ : Params A dIn dOut) (k : Fin L)
    (η : Params A dIn dOut) (v vdot : Matrix T (A.w k) ℝ) : Matrix T dOut ℝ :=
  fderiv ℝ (fun h' : Matrix T d ℝ => suffix A 0 θ k.succ h') (v * θ.write k)
      (vdot * θ.write k + v * η.write k)
    + fderiv ℝ (fun θ' : Params A dIn dOut => suffix A 0 θ' k.succ (v * θ.write k)) θ η

/-- For a gated block, `𝓛(w̃, w̃'; n)` of equation (27) is `writeLHS` at `v = w̃ ⊙ ι` and
`vdot = w̃' ⊙ ż^g ⊙ ι + w̃ ⊙ ż^v`. -/
theorem blockLHSGated_eq_writeLHS (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut)
    (k : Fin L) (η : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut)
    (w w' : Matrix T (hid k) ℝ) (z zdot : Matrix T (hid k ⊕ hid k) ℝ) :
    blockLHSGated θ k η w w' z zdot
      = writeLHS (Arch.gated σ χ hid) θ k η (Matrix.of fun t j => w t j * z t (Sum.inr j))
          (Matrix.of fun t j =>
            w' t j * zdot t (Sum.inl j) * z t (Sum.inr j) + w t j * zdot t (Sum.inr j)) :=
  rfl

/-- The frozen block, on every row, is `g°_ℓ` (`frozenGated`). -/
theorem frozen_block_apply (A : ∀ ℓ, Finset (hid ℓ))
    (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut) (ℓ : Fin L) (n : Matrix T d ℝ)
    (t : T) :
    ((Arch.frozen (T := T) (d := d) A).f ℓ (n * θ.read ℓ) * θ.write ℓ) t
      = frozenGated θ ℓ (A ℓ) (n t) := by
  funext k
  -- entry `k` of row `t`: a sum over the hidden units, in which only those of `A ℓ` count
  change ((Matrix.of fun t => Set.indicator (↑(A ℓ) : Set (hid ℓ))
      fun i => (n * θ.read ℓ) t (Sum.inl i) * (n * θ.read ℓ) t (Sum.inr i)) * θ.write ℓ) t k = _
  rw [Matrix.mul_apply, frozenGated, Finset.sum_apply,
    ← Finset.sum_indicator_subset _ (Finset.subset_univ (A ℓ))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.of_apply]
  by_cases hi : i ∈ A ℓ
  · -- an active unit: `(n_t c_i) (n_t e_i) a_i`
    rw [Set.indicator_of_mem (Finset.mem_coe.2 hi), Set.indicator_of_mem (Finset.mem_coe.2 hi)]
    simp only [Pi.smul_apply, smul_eq_mul, Matrix.mul_apply, dotProduct, Matrix.transpose_apply]
  · -- an inactive unit contributes `0`
    rw [Set.indicator_of_notMem (Finset.mem_coe.not.2 hi),
      Set.indicator_of_notMem (Finset.mem_coe.not.2 hi), zero_mul]

/-- The fixed maps of the frozen network are real-analytic (they are polynomial). -/
theorem analyticOnNhd_f_frozen (A : ∀ ℓ, Finset (hid ℓ)) (ℓ : Fin L) :
    AnalyticOnNhd ℝ ((Arch.frozen (T := T) (d := d) A).f ℓ) Set.univ := by
  -- entrywise: the gate times the value on `A ℓ`, and `0` off it
  show AnalyticOnNhd ℝ (fun M : Matrix T (hid ℓ ⊕ hid ℓ) ℝ => fun t => fun i =>
    Set.indicator (↑(A ℓ) : Set (hid ℓ)) (fun i => M t (Sum.inl i) * M t (Sum.inr i)) i) Set.univ
  refine AnalyticOnNhd.pi fun t => AnalyticOnNhd.pi fun i => ?_
  by_cases hi : i ∈ A ℓ
  · have h : (fun M : Matrix T (hid ℓ ⊕ hid ℓ) ℝ => Set.indicator (↑(A ℓ) : Set (hid ℓ))
        (fun i => M t (Sum.inl i) * M t (Sum.inr i)) i)
          = fun M => M t (Sum.inl i) * M t (Sum.inr i) :=
      funext fun M => Set.indicator_of_mem (Finset.mem_coe.2 hi) _
    have h2 : AnalyticOnNhd ℝ (fun M : Matrix T (hid ℓ ⊕ hid ℓ) ℝ => Set.indicator
        (↑(A ℓ) : Set (hid ℓ)) (fun i => M t (Sum.inl i) * M t (Sum.inr i)) i) Set.univ := by
      rw [h]
      exact (analyticOnNhd_matrix_entry t (Sum.inl i)).mul (analyticOnNhd_matrix_entry t (Sum.inr i))
    exact h2
  · have h : (fun M : Matrix T (hid ℓ ⊕ hid ℓ) ℝ => Set.indicator (↑(A ℓ) : Set (hid ℓ))
        (fun i => M t (Sum.inl i) * M t (Sum.inr i)) i) = fun _ => 0 :=
      funext fun M => Set.indicator_of_notMem (Finset.mem_coe.not.2 hi) _
    have h2 : AnalyticOnNhd ℝ (fun M : Matrix T (hid ℓ ⊕ hid ℓ) ℝ => Set.indicator
        (↑(A ℓ) : Set (hid ℓ)) (fun i => M t (Sum.inl i) * M t (Sum.inr i)) i) Set.univ := by
      rw [h]
      exact analyticOnNhd_const
    exact h2

omit [Fintype T] [DecidableEq d] in
/-- Helper (a copy of the private `dotCLM` of `Depth/Cones.lean`): `v ↦ v ⬝ c`, as a continuous
linear map. -/
private noncomputable def dotCLMFr (c : d → ℝ) : (d → ℝ) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => v ⬝ᵥ c
      map_add' := fun v w => add_dotProduct v w c
      map_smul' := fun r v => smul_dotProduct r v c }

omit [Fintype T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (a copy of the private `analyticOnNhd_frozenGated` of `Depth/Cones.lean`): the frozen
gated block is a polynomial, hence analytic. -/
private theorem analyticOnNhd_frozenGatedFr
    (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut) (ℓ : Fin L) (B : Finset (hid ℓ)) :
    AnalyticOnNhd ℝ (frozenGated θ ℓ B) Set.univ := by
  show AnalyticOnNhd ℝ (fun n => ∑ j ∈ B, ((n ⬝ᵥ (θ.read ℓ)ᵀ (Sum.inl j)) *
    (n ⬝ᵥ (θ.read ℓ)ᵀ (Sum.inr j))) • θ.write ℓ j) Set.univ
  refine Finset.analyticOnNhd_fun_sum _ fun j _ => ?_
  have h := (((dotCLMFr ((θ.read ℓ)ᵀ (Sum.inl j))).analyticOnNhd Set.univ).mul
    ((dotCLMFr ((θ.read ℓ)ᵀ (Sum.inr j))).analyticOnNhd Set.univ)).smul
      (analyticOnNhd_const (v := θ.write ℓ j))
  exact h

omit [Fintype T] [DecidableEq d] in
/-- Helper (a copy of the private `injective_fderiv_rowwise` of `Depth/Cones.lean`): a map acting
row by row, `n ↦ (t ↦ g (n t))`, has at the matrix all of whose rows are `x` the derivative
`V ↦ (t ↦ G (V t))`, which is injective if `G` is. -/
private theorem injective_fderiv_rowwiseFr [Finite T] {g : (d → ℝ) → (d → ℝ)}
    {G : (d → ℝ) →L[ℝ] (d → ℝ)} {x : d → ℝ} (hg : HasFDerivAt g G x)
    (hG : Function.Injective G) :
    Function.Injective (fderiv ℝ (fun n : T → d → ℝ => fun t => g (n t)) (fun _ => x)) := by
  have : Fintype T := Fintype.ofFinite T
  have h : HasFDerivAt (fun n : T → d → ℝ => fun t => g (n t))
      (ContinuousLinearMap.pi fun t => G.comp (ContinuousLinearMap.proj t)) (fun _ => x) :=
    hasFDerivAt_pi.2 fun t =>
      hg.comp (fun _ : T => x) (hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : T => d → ℝ) t _)
  rw [h.fderiv]
  intro V W hVW
  funext t
  exact hG (congrFun hVW t)

/-- **A good `θ` is regular for the frozen network:** (R1), and by (K2) the derivative of every
frozen block is invertible at some hidden state. So Lemmas D.2 and D.3 hold for the frozen
network. -/
theorem regular_frozen_of_goodForConesGated {C : Fin (L + 1) → Set (d → ℝ)}
    {A : ∀ ℓ, Finset (hid ℓ)} {θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut}
    (hθ : GoodForConesGated C A θ) :
    Regular (Arch.frozen (T := T) (d := d) A) (θ.toFrozen A) := by
  -- (R1): the matrices of `θ.toFrozen A` are those of `θ`
  refine ⟨hθ.rank_E, hθ.rank_D, hθ.rank_write, fun ℓ => ?_⟩
  -- (K2): a row `ν` at which the derivative `G` of the frozen block `g°_ℓ` is injective
  obtain ⟨ν, hν⟩ := hθ.frozen_deriv ℓ
  have hg : HasFDerivAt (frozenGated θ ℓ (A ℓ)) (fderiv ℝ (frozenGated θ ℓ (A ℓ)) ν) ν :=
    (analyticOnNhd_frozenGatedFr θ ℓ (A ℓ) ν (Set.mem_univ _)).differentiableAt.hasFDerivAt
  -- the frozen block acts row by row: row `t` of its value at `n` is `g°_ℓ(n_t)`
  have hfun : (fun n : Matrix T d ℝ => (Arch.frozen (T := T) (d := d) A).f ℓ
      (n * (θ.toFrozen A).read ℓ) * (θ.toFrozen A).write ℓ)
        = fun n : Matrix T d ℝ => (fun t => frozenGated θ ℓ (A ℓ) (n t) : Matrix T d ℝ) :=
    funext fun n => funext fun t => frozen_block_apply A θ ℓ n t
  -- at the matrix all of whose rows are `ν`, its derivative is `V ↦ (t ↦ G (V t))`, injective
  refine ⟨fun _ => ν, ?_⟩
  have key : Function.Injective (fderiv ℝ (fun n : Matrix T d ℝ =>
      (fun t => frozenGated θ ℓ (A ℓ) (n t) : Matrix T d ℝ)) (fun _ => ν)) :=
    injective_fderiv_rowwiseFr hg hν
  rw [← hfun] at key
  exact key

omit [Fintype T] [Fintype d] [DecidableEq d] in
/-- Helper: the fixed map of a frozen block is quadratic, `f°_ℓ(c M) = c² f°_ℓ(M)`. -/
private theorem frozen_f_smul (A : ∀ ℓ, Finset (hid ℓ)) (ℓ : Fin L) (c : ℝ)
    (M : Matrix T ((Arch.frozen (T := T) (d := d) A).r ℓ) ℝ) :
    (Arch.frozen (T := T) (d := d) A).f ℓ (c • M)
      = (c ^ 2) • (Arch.frozen (T := T) (d := d) A).f ℓ M := by
  ext t i
  show Set.indicator (↑(A ℓ) : Set (hid ℓ))
      (fun i => (c • M) t (Sum.inl i) * (c • M) t (Sum.inr i)) i
    = c ^ 2 * Set.indicator (↑(A ℓ) : Set (hid ℓ)) (fun i => M t (Sum.inl i) * M t (Sum.inr i)) i
  by_cases hi : i ∈ A ℓ
  · -- an active unit: `(c z)(c w) = c² z w`
    rw [Set.indicator_of_mem (Finset.mem_coe.2 hi), Set.indicator_of_mem (Finset.mem_coe.2 hi)]
    simp only [Matrix.smul_apply, smul_eq_mul]
    ring
  · -- an inactive unit: `0 = c² 0`
    rw [Set.indicator_of_notMem (Finset.mem_coe.not.2 hi),
      Set.indicator_of_notMem (Finset.mem_coe.not.2 hi), mul_zero]

/-- **The frozen network is homogeneous:** `𝓑°_{>k}(c h) = c^{2^{L−k}} 𝓑°_{>k}(h)`. -/
theorem suffix_frozen_smul (A : ∀ ℓ, Finset (hid ℓ))
    (θ : Params (Arch.frozen (T := T) (d := d) A) dIn dOut) (k : Fin (L + 1)) (c : ℝ)
    (h : Matrix T d ℝ) :
    suffix (Arch.frozen A) 0 θ k (c • h)
      = c ^ (2 ^ (L - (k : ℕ))) • suffix (Arch.frozen A) 0 θ k h := by
  induction k using Fin.reverseInduction generalizing c h with
  | last =>
    -- `𝓑°_{>L}(c h) = (c h) D = c (h D)`
    rw [suffix_last_eq_mul (Arch.frozen A) θ rfl, Fin.val_last, Nat.sub_self, pow_zero, pow_one]
    exact Matrix.smul_mul c h θ.D
  | cast ℓ ih =>
    -- `𝓑°_{>ℓ-1}(c h) = 𝓑°_{>ℓ}(g°_ℓ(c h)) = 𝓑°_{>ℓ}(c² g°_ℓ(h)) = (c²)^{2^{L-ℓ-1}} 𝓑°_{>ℓ-1}(h)`
    rw [suffix_castSucc_eq_comp (Arch.frozen A) θ rfl ℓ, Function.comp_apply, Function.comp_apply,
      Matrix.smul_mul, frozen_f_smul, Matrix.smul_mul, ih]
    -- `(c²)^{2^{L-ℓ-1}} = c^{2^{L-ℓ}}`, since `ℓ < L`
    have hL : L - (ℓ : ℕ) = (L - ((ℓ : ℕ) + 1)) + 1 := by
      have := ℓ.isLt
      omega
    rw [Fin.val_succ, Fin.val_castSucc, ← pow_mul, hL, pow_succ, mul_comm (2 : ℕ)]

/-- The derivative of the frozen network in the hidden state is homogeneous of the degree
`2^{L−k} − 1`. -/
theorem fderiv_suffix_frozen_smul (A : ∀ ℓ, Finset (hid ℓ))
    (θ : Params (Arch.frozen (T := T) (d := d) A) dIn dOut) (k : Fin (L + 1)) {c : ℝ}
    (hc : c ≠ 0) (h v : Matrix T d ℝ) :
    fderiv ℝ (fun h' : Matrix T d ℝ => suffix (Arch.frozen A) 0 θ k h') (c • h) v
      = c ^ (2 ^ (L - (k : ℕ)) - 1)
        • fderiv ℝ (fun h' : Matrix T d ℝ => suffix (Arch.frozen A) 0 θ k h') h v := by
  -- `𝓑°_{>k}` is analytic, hence differentiable
  have hd : ∀ x, DifferentiableAt ℝ (suffix (Arch.frozen (T := T) (d := d) A) 0 θ k) x :=
    fun x => (analyticOnNhd_suffix (Arch.frozen A) θ rfl (analyticOnNhd_f_frozen A) k x
      (Set.mem_univ _)).differentiableAt
  -- the derivative of `h' ↦ 𝓑°_{>k}(c h')` at `h`, by the chain rule: `v ↦ 𝐃𝓑°_{>k}(c h)(c v)`
  have h1 := HasFDerivAt.comp (f := fun x : Matrix T d ℝ => c • x) h (hd (c • h)).hasFDerivAt
    ((hasFDerivAt_id h).fun_const_smul c)
  -- and, by homogeneity (`suffix_frozen_smul`), `c^M 𝐃𝓑°_{>k}(h)` with `M = 2^{L-k}`
  have h2 : HasFDerivAt
      (suffix (Arch.frozen (T := T) (d := d) A) 0 θ k ∘ fun x : Matrix T d ℝ => c • x)
      (c ^ 2 ^ (L - (k : ℕ)) • fderiv ℝ (suffix (Arch.frozen (T := T) (d := d) A) 0 θ k) h) h := by
    have hfun : (suffix (Arch.frozen (T := T) (d := d) A) 0 θ k ∘ fun x : Matrix T d ℝ => c • x)
        = fun x => c ^ 2 ^ (L - (k : ℕ)) • suffix (Arch.frozen A) 0 θ k x :=
      funext fun x => suffix_frozen_smul A θ k c x
    rw [hfun]
    exact (hd h).hasFDerivAt.fun_const_smul _
  -- so `c 𝐃𝓑°_{>k}(c h) v = c^M 𝐃𝓑°_{>k}(h) v`
  -- (stated by defeq: `simp` lemmas about `comp`/`smul` do not fire on this CLM)
  have e : c • fderiv ℝ (suffix (Arch.frozen (T := T) (d := d) A) 0 θ k) (c • h) v
      = c ^ 2 ^ (L - (k : ℕ)) • fderiv ℝ (suffix (Arch.frozen (T := T) (d := d) A) 0 θ k) h v :=
    (map_smul (fderiv ℝ (suffix (Arch.frozen (T := T) (d := d) A) 0 θ k) (c • h)) c v).symm.trans
      (DFunLike.congr_fun (h1.unique h2) v)
  -- cancel one `c` (`M ≥ 1`)
  rw [← Nat.sub_add_cancel (Nat.one_le_two_pow (n := L - (k : ℕ))), pow_succ', mul_smul] at e
  exact (smul_right_inj hc).1 e

/-- The derivative of the frozen network in the weights is homogeneous of the degree `2^{L−k}` in
the hidden state. -/
theorem fderiv_params_suffix_frozen_smul (A : ∀ ℓ, Finset (hid ℓ))
    (θ η : Params (Arch.frozen (T := T) (d := d) A) dIn dOut) (k : Fin (L + 1)) (c : ℝ)
    (h : Matrix T d ℝ) :
    fderiv ℝ (fun θ' : Params (Arch.frozen (T := T) (d := d) A) dIn dOut =>
        suffix (Arch.frozen A) 0 θ' k (c • h)) θ η
      = c ^ (2 ^ (L - (k : ℕ)))
        • fderiv ℝ (fun θ' : Params (Arch.frozen (T := T) (d := d) A) dIn dOut =>
            suffix (Arch.frozen A) 0 θ' k h) θ η := by
  -- for every weight `θ'`, `𝓑°_{>k}(c h) = c^M 𝓑°_{>k}(h)` (`suffix_frozen_smul`)
  have hfun : (fun θ' : Params (Arch.frozen (T := T) (d := d) A) dIn dOut =>
      suffix (Arch.frozen A) 0 θ' k (c • h))
        = fun θ' => c ^ 2 ^ (L - (k : ℕ)) • suffix (Arch.frozen A) 0 θ' k h :=
    funext fun θ' => suffix_frozen_smul A θ' k c h
  -- and `θ' ↦ 𝓑°_{>k}(h)` is differentiable
  have hd : DifferentiableAt ℝ (fun θ' : Params (Arch.frozen (T := T) (d := d) A) dIn dOut =>
      suffix (Arch.frozen A) 0 θ' k h) θ :=
    differentiable_params_suffix (Arch.frozen A) rfl
      (fun ℓ => differentiableOn_univ.1 (analyticOnNhd_f_frozen A ℓ).differentiableOn) k h θ
  -- so the derivative of `θ' ↦ c^M 𝓑°_{>k}(h)` is `c^M` times that of `θ' ↦ 𝓑°_{>k}(h)`
  have e : fderiv ℝ (fun θ' : Params (Arch.frozen (T := T) (d := d) A) dIn dOut =>
      suffix (Arch.frozen A) 0 θ' k (c • h)) θ
        = c ^ 2 ^ (L - (k : ℕ)) • fderiv ℝ (fun θ' : Params (Arch.frozen (T := T) (d := d) A)
            dIn dOut => suffix (Arch.frozen A) 0 θ' k h) θ := by
    rw [hfun]
    exact fderiv_fun_const_smul hd _
  rw [e, _root_.smul_apply]

/-- The left side of the identity for one block of the frozen network is homogeneous of the degree
`2^{L−k−1}` in the outputs of the hidden units and their derivative together. -/
theorem writeLHS_frozen_smul (A : ∀ ℓ, Finset (hid ℓ))
    (θ η : Params (Arch.frozen (T := T) (d := d) A) dIn dOut) (k : Fin L) {c : ℝ} (hc : c ≠ 0)
    (v vdot : Matrix T (hid k) ℝ) :
    writeLHS (Arch.frozen A) θ k η (c • v) (c • vdot)
      = c ^ (2 ^ (L - (k : ℕ) - 1)) • writeLHS (Arch.frozen A) θ k η v vdot := by
  -- `(c v) W = c (v W)`, the direction is `c` times the old one, and `𝐃𝓑°` is linear in it
  unfold writeLHS
  simp only [Matrix.smul_mul, ← smul_add, map_smul]
  -- `fderiv_suffix_frozen_smul` and `fderiv_params_suffix_frozen_smul` at `k + 1`
  rw [fderiv_suffix_frozen_smul A θ k.succ hc, fderiv_params_suffix_frozen_smul A θ η k.succ c]
  -- `c c^{M-1} = c^M` with `M = 2^{L-k-1}`
  rw [smul_smul, Fin.val_succ, ← pow_succ', Nat.sub_add_cancel Nat.one_le_two_pow, Nat.sub_sub,
    smul_add]

end Skips
