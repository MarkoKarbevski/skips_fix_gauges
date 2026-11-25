import SkipsLean.Depth.FrozenFar
import SkipsLean.Activations.GateFarC
import Mathlib.Analysis.Complex.Liouville

/-!
# The network after `h_k` far out in its cone: the holomorphic extension

Paper (dimension): Lemma D.11 (The network after `h_k` far out in its cone). "In the case (n), for
gated blocks, let `θ` be good, `k ≤ L`, `h° ∈ C_k`, and let `η` be a direction of the weights of
the blocks `k+1, …, L` and of `D`. There are numbers `ϱ, κ, t₀ > 0` such that, for `t ≥ t₀`, the
maps `u ↦ 𝓑_{>k}(t (h° + u))` and `u ↦ 𝐃_θ 𝓑_{>k}(t (h° + u)) η` extend to holomorphic maps on the
rows `u ∈ ℂ^{1×d_model}` with `|u_j| ≤ ϱ` for all `j`, and for these `u`, at `h = t (h° + u)`,

  `‖𝓑_{>k}(h) − 𝓑°_{>k}(h)‖ ≤ e^{−κ t^p}`,   `‖𝐃_θ 𝓑_{>k}(h) η − 𝐃_θ 𝓑°_{>k}(h) η‖ ≤ e^{−κ t^p}`."

`Depth/FrozenFar.lean` has the bounds for real `u` (with the bound for the derivative in the
hidden state, which the paper gets from the complex `u` by Cauchy's estimate). Here the lemma as
the paper states it, for complex `u`: for `t ≥ t₀` there are maps `G`, `G°`, `G'`, `G°'` that are
holomorphic on the complex `u` with `|u_{τ j}| ≤ ϱ` for all entries (holomorphic near each point
of this closed polydisc), that agree at the real `u` of the polydisc with `u ↦ 𝓑_{>k}(t (H + u))`,
with the same map of the frozen network, and with the derivatives of the two in the weights along
`η`, and that satisfy the two bounds on the whole polydisc. A holomorphic map on the polydisc is
determined by its values at the real points, so these are the extensions of the paper. A hidden
state has the rows `T`, and `h°` is a matrix `H` all of whose rows lie in `C_k`. The gate is any
`σ` with `GateFar σ σ' p` and `GateFarC σ p` (SiLU with `p = 1`, GELU with `p = 2`).
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise Topology

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]
variable {σ σ' : ℝ → ℝ} {p : ℕ}

/-! ### The complex network along a complex line of weights -/

/-- The outputs of the hidden units of a gated block at complex pre-activations `P`, with the
gate value `a j` for unit `j`: entry `(τ, j)` is `a_j(P_{τ, inl j}) P_{τ, inr j}`. -/
private def qaC {m ι : Type*} (a : ι → ℂ → ℂ) (P : Matrix m (ι ⊕ ι) ℂ) : Matrix m ι ℂ :=
  Matrix.of fun τ j => a j (P τ (Sum.inl j)) * P τ (Sum.inr j)

open Classical in
/-- The gate value of a frozen unit at a complex argument: `z` if the unit is active, `0`
otherwise. -/
private noncomputable def aFC {ι : Type*} (s : Finset ι) (j : ι) (z : ℂ) : ℂ :=
  if j ∈ s then z else 0

/-- The read of block `ℓ` at the complex weights `θ + s η`. -/
private noncomputable def cR (θ η : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (s : ℂ) (ℓ : Fin L) : Matrix d (hid ℓ ⊕ hid ℓ) ℂ :=
  (θ.read ℓ).map (fun x : ℝ => (x : ℂ)) + s • (η.read ℓ).map (fun x : ℝ => (x : ℂ))

/-- The write of block `ℓ` at the complex weights `θ + s η`. -/
private noncomputable def cW (θ η : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (s : ℂ) (ℓ : Fin L) : Matrix (hid ℓ) d ℂ :=
  (θ.write ℓ).map (fun x : ℝ => (x : ℂ)) + s • (η.write ℓ).map (fun x : ℝ => (x : ℂ))

/-- The readout at the complex weights `θ + s η`. -/
private noncomputable def cD (θ η : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (s : ℂ) : Matrix d dOut ℂ :=
  θ.D.map (fun x : ℝ => (x : ℂ)) + s • η.D.map (fun x : ℝ => (x : ℂ))

/-- `𝓑_{>k}(h)` at the complex weights `θ + s η` and a complex hidden state `h`, without skips,
with the gate values `a ℓ j` (the gate `σc` for the network, the frozen gate values for the frozen
network): `𝓑_{>L}(h) = h D` and `𝓑_{>ℓ-1}(h) = 𝓑_{>ℓ}(qaC (a ℓ) (h W_read^ℓ) W_write^ℓ)`. -/
private noncomputable def netC (a : ∀ ℓ : Fin L, hid ℓ → ℂ → ℂ)
    (θ η : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) (s : ℂ) :
    Fin (L + 1) → Matrix T d ℂ → Matrix T dOut ℂ :=
  Fin.reverseInduction (motive := fun _ => Matrix T d ℂ → Matrix T dOut ℂ)
    (fun h => h * cD θ η s)
    (fun ℓ B h => B (qaC (a ℓ) (h * cR θ η s ℓ) * cW θ η s ℓ))

omit [Fintype T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
private theorem netC_last (a : ∀ ℓ : Fin L, hid ℓ → ℂ → ℂ)
    (θ η : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) (s : ℂ) (h : Matrix T d ℂ) :
    netC a θ η s (Fin.last L) h = h * cD θ η s := by
  simp only [netC, Fin.reverseInduction_last]

omit [Fintype T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
private theorem netC_castSucc (a : ∀ ℓ : Fin L, hid ℓ → ℂ → ℂ)
    (θ η : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) (s : ℂ) (ℓ : Fin L)
    (h : Matrix T d ℂ) :
    netC a θ η s ℓ.castSucc h
      = netC a θ η s ℓ.succ (qaC (a ℓ) (h * cR θ η s ℓ) * cW θ η s ℓ) := by
  simp only [netC, Fin.reverseInduction_castSucc]

/-! ### At real arguments: the real networks -/

/-- Helper: the cast of a product of real matrices is the product of the casts. -/
private theorem map_mul_ofReal_ffh {m n o : Type*} [Fintype n] (A : Matrix m n ℝ)
    (B : Matrix n o ℝ) :
    (A * B).map (fun x : ℝ => (x : ℂ))
      = A.map (fun x : ℝ => (x : ℂ)) * B.map (fun x : ℝ => (x : ℂ)) :=
  Matrix.map_mul (f := Complex.ofRealHom)

/-- Helper: the cast of `A + r B`. -/
private theorem map_add_smul_ofReal_ffh {m n : Type*} (A B : Matrix m n ℝ) (r : ℝ) :
    (A + r • B).map (fun x : ℝ => (x : ℂ))
      = A.map (fun x : ℝ => (x : ℂ)) + (r : ℂ) • B.map (fun x : ℝ => (x : ℂ)) := by
  ext i j
  simp

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
private theorem cR_ofReal (θ η : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (r : ℝ) (ℓ : Fin L) :
    cR θ η (r : ℂ) ℓ = (θ.read ℓ + r • η.read ℓ).map (fun x : ℝ => (x : ℂ)) :=
  (map_add_smul_ofReal_ffh _ _ r).symm

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
private theorem cW_ofReal (θ η : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (r : ℝ) (ℓ : Fin L) :
    cW θ η (r : ℂ) ℓ = (θ.write ℓ + r • η.write ℓ).map (fun x : ℝ => (x : ℂ)) :=
  (map_add_smul_ofReal_ffh _ _ r).symm

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
private theorem cD_ofReal (θ η : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (r : ℝ) : cD θ η (r : ℂ) = (θ.D + r • η.D).map (fun x : ℝ => (x : ℂ)) :=
  (map_add_smul_ofReal_ffh _ _ r).symm

omit [Fintype T] [Fintype d] [DecidableEq d] in
/-- Helper: the gated block at real pre-activations, cast. -/
private theorem qaC_gated_ofReal {σc : ℂ → ℂ} (hσ : ∀ x : ℝ, σc (x : ℂ) = ((σ x : ℝ) : ℂ))
    (ℓ : Fin L) (M : Matrix T (hid ℓ ⊕ hid ℓ) ℝ) :
    ((Arch.gated (T := T) (d := d) σ id hid).f ℓ M).map (fun x : ℝ => (x : ℂ))
      = qaC (fun _ => σc) (M.map (fun x : ℝ => (x : ℂ))) := by
  ext τ j
  simp only [qaC, Matrix.map_apply, Matrix.of_apply, hσ]
  push_cast
  rfl

omit [Fintype T] [Fintype d] [DecidableEq d] in
/-- Helper: the frozen block at real pre-activations, cast. -/
private theorem qaC_frozen_ofReal (A : ∀ ℓ, Finset (hid ℓ)) (ℓ : Fin L)
    (M : Matrix T (hid ℓ ⊕ hid ℓ) ℝ) :
    ((Arch.frozen (T := T) (d := d) A).f ℓ M).map (fun x : ℝ => (x : ℂ))
      = qaC (aFC (A ℓ)) (M.map (fun x : ℝ => (x : ℂ))) := by
  ext τ j
  simp only [qaC, Matrix.map_apply, Matrix.of_apply, aFC]
  by_cases hj : j ∈ A ℓ
  · rw [Set.indicator_of_mem (Finset.mem_coe.2 hj)]
    simp [hj]
  · rw [Set.indicator_of_notMem (fun h' => hj (Finset.mem_coe.1 h'))]
    simp [hj]

/-- **At real weights `θ + r η` and a real hidden state, the complex network is the network.** -/
private theorem netC_gated_ofReal {σc : ℂ → ℂ} (hσ : ∀ x : ℝ, σc (x : ℂ) = ((σ x : ℝ) : ℂ))
    (θ η : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) (r : ℝ) (k : Fin (L + 1))
    (h : Matrix T d ℝ) :
    netC (fun _ _ => σc) θ η (r : ℂ) k (h.map (fun x : ℝ => (x : ℂ)))
      = (suffix (Arch.gated σ id hid) 0 (θ + r • η) k h).map (fun x : ℝ => (x : ℂ)) := by
  induction k using Fin.reverseInduction generalizing h with
  | last =>
    rw [netC_last, suffix_last_eq_mul (Arch.gated σ id hid) (θ + r • η) rfl, cD_ofReal,
      map_mul_ofReal_ffh]
    rfl
  | cast ℓ ih =>
    rw [netC_castSucc, suffix_castSucc_eq_comp (Arch.gated σ id hid) (θ + r • η) rfl ℓ,
      Function.comp_apply, cR_ofReal, cW_ofReal, ← map_mul_ofReal_ffh,
      ← qaC_gated_ofReal (d := d) hσ, ← map_mul_ofReal_ffh, ih]
    rfl

/-- **At real weights and a real hidden state, the complex frozen network is the frozen
network.** -/
private theorem netC_frozen_ofReal (A : ∀ ℓ, Finset (hid ℓ))
    (θ η : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) (r : ℝ) (k : Fin (L + 1))
    (h : Matrix T d ℝ) :
    netC (fun ℓ => aFC (A ℓ)) θ η (r : ℂ) k (h.map (fun x : ℝ => (x : ℂ)))
      = (suffix (Arch.frozen A) 0 (θ.toFrozen A + r • η.toFrozen A) k h).map
          (fun x : ℝ => (x : ℂ)) := by
  induction k using Fin.reverseInduction generalizing h with
  | last =>
    rw [netC_last, suffix_last_eq_mul (Arch.frozen A) (θ.toFrozen A + r • η.toFrozen A) rfl,
      cD_ofReal, map_mul_ofReal_ffh]
    rfl
  | cast ℓ ih =>
    rw [netC_castSucc,
      suffix_castSucc_eq_comp (Arch.frozen A) (θ.toFrozen A + r • η.toFrozen A) rfl ℓ,
      Function.comp_apply, cR_ofReal, cW_ofReal, ← map_mul_ofReal_ffh,
      ← qaC_frozen_ofReal (d := d) A, ← map_mul_ofReal_ffh, ih]
    rfl

/-! ### Holomorphy of the complex networks -/

/-- Helper (as in `Depth/ComplexSuffix.lean`): the matrix product of two analytic matrix-valued
maps is analytic. -/
private theorem analyticAt_matMul_ffh {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {m n o : Type*} [Fintype m] [Fintype n] [Fintype o]
    {f : E → Matrix m n ℂ} {g : E → Matrix n o ℂ} {x : E}
    (hf : AnalyticAt ℂ f x) (hg : AnalyticAt ℂ g x) :
    AnalyticAt ℂ (fun y => f y * g y) x := by
  let B : Matrix m n ℂ →ₗ[ℂ] Matrix n o ℂ →ₗ[ℂ] Matrix m o ℂ :=
    LinearMap.mk₂ ℂ (fun a b => a * b) Matrix.add_mul (fun c a b => Matrix.smul_mul c a b)
      Matrix.mul_add (fun c a b => Matrix.mul_smul a c b)
  let B' : Matrix m n ℂ →L[ℂ] Matrix n o ℂ →L[ℂ] Matrix m o ℂ :=
    LinearMap.toContinuousLinearMap
      ((LinearMap.toContinuousLinearMap :
        (Matrix n o ℂ →ₗ[ℂ] Matrix m o ℂ) ≃ₗ[ℂ] (Matrix n o ℂ →L[ℂ] Matrix m o ℂ)).toLinearMap ∘ₗ B)
  have hB : (fun y => f y * g y) = fun y => B' (f y) (g y) := rfl
  rw [hB]
  exact (B'.analyticAt_bilinear (f x, g x)).comp₂ hf hg

/-- Helper: an entry of an analytic matrix-valued map is analytic. -/
private theorem analyticAt_entry_ffh {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {m n : Type*} [Fintype m] [Fintype n] {P : E → Matrix m n ℂ} {x : E}
    (hP : AnalyticAt ℂ P x) (i : m) (j : n) : AnalyticAt ℂ (fun y => P y i j) x := by
  have he : AnalyticAt ℂ (fun M : Matrix m n ℂ => M i j) (P x) :=
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : n => ℂ) j).comp
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : m => n → ℂ) i)).analyticAt _
  exact AnalyticAt.comp (f := P) he hP

/-- Helper: the hidden units `qaC a (P y)` are analytic at `x` if `P` is, and every gate value
`a j` is analytic at the gate `P x τ (inl j)`. -/
private theorem analyticAt_qaC_ffh {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {m ι : Type*} [Fintype m] [Fintype ι] {a : ι → ℂ → ℂ} {P : E → Matrix m (ι ⊕ ι) ℂ} {x : E}
    (hP : AnalyticAt ℂ P x) (ha : ∀ τ j, AnalyticAt ℂ (a j) (P x τ (Sum.inl j))) :
    AnalyticAt ℂ (fun y => qaC a (P y)) x := by
  show AnalyticAt ℂ (fun y => fun τ => fun j => a j (P y τ (Sum.inl j)) * P y τ (Sum.inr j)) x
  refine AnalyticAt.pi fun τ => AnalyticAt.pi fun j => ?_
  have h1 : AnalyticAt ℂ (fun y => a j (P y τ (Sum.inl j))) x :=
    AnalyticAt.comp (f := fun y => P y τ (Sum.inl j)) (ha τ j) (analyticAt_entry_ffh hP τ _)
  exact h1.fun_mul (analyticAt_entry_ffh hP τ (Sum.inr j))

/-- Helper: `s ↦ A + s B` is analytic. -/
private theorem analyticAt_line_ffh {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {m n : Type*} [Fintype m] [Fintype n] (A B : Matrix m n ℂ) {f : E → ℂ} {x : E}
    (hf : AnalyticAt ℂ f x) : AnalyticAt ℂ (fun y => A + f y • B) x :=
  analyticAt_const.fun_add (hf.fun_smul analyticAt_const)

omit [DecidableEq d] [Fintype dIn] in
/-- `(s, h) ↦ 𝓑_{>L}(h) = h D(s)` is holomorphic. -/
private theorem analyticAt_netC_last (a : ∀ ℓ : Fin L, hid ℓ → ℂ → ℂ)
    (θ η : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) (x : ℂ × Matrix T d ℂ) :
    AnalyticAt ℂ (fun q : ℂ × Matrix T d ℂ => netC a θ η q.1 (Fin.last L) q.2) x := by
  have e : (fun q : ℂ × Matrix T d ℂ => netC a θ η q.1 (Fin.last L) q.2)
      = fun q => q.2 * cD θ η q.1 := funext fun q => netC_last a θ η q.1 q.2
  rw [e]
  exact analyticAt_matMul_ffh analyticAt_snd (analyticAt_line_ffh _ _ analyticAt_fst)

omit [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- The block `(s, h) ↦ (s, qaC (a ℓ) (h W_read(s)) W_write(s))` is holomorphic where the gate
values are holomorphic at the gates. -/
private theorem analyticAt_block_ffh (a : ∀ ℓ : Fin L, hid ℓ → ℂ → ℂ)
    (θ η : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) (ℓ : Fin L)
    (x : ℂ × Matrix T d ℂ)
    (ha : ∀ τ j, AnalyticAt ℂ (a ℓ j) ((x.2 * cR θ η x.1 ℓ) τ (Sum.inl j))) :
    AnalyticAt ℂ (fun q : ℂ × Matrix T d ℂ =>
      (q.1, qaC (a ℓ) (q.2 * cR θ η q.1 ℓ) * cW θ η q.1 ℓ)) x := by
  have hP : AnalyticAt ℂ (fun q : ℂ × Matrix T d ℂ => q.2 * cR θ η q.1 ℓ) x :=
    analyticAt_matMul_ffh analyticAt_snd (analyticAt_line_ffh _ _ analyticAt_fst)
  have hq := analyticAt_qaC_ffh hP ha
  exact analyticAt_fst.prod (analyticAt_matMul_ffh hq (analyticAt_line_ffh _ _ analyticAt_fst))

omit [DecidableEq d] [Fintype dIn] in
/-- Holomorphy through block `ℓ`: `(s, h) ↦ 𝓑_{>ℓ-1}(h)` is holomorphic at `x` if the gate values
are holomorphic at the gates of `x` and `(s, h) ↦ 𝓑_{>ℓ}(h)` is holomorphic at the output. -/
private theorem analyticAt_netC_castSucc (a : ∀ ℓ : Fin L, hid ℓ → ℂ → ℂ)
    (θ η : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) (ℓ : Fin L)
    (x : ℂ × Matrix T d ℂ)
    (ha : ∀ τ j, AnalyticAt ℂ (a ℓ j) ((x.2 * cR θ η x.1 ℓ) τ (Sum.inl j)))
    (hnext : AnalyticAt ℂ (fun q : ℂ × Matrix T d ℂ => netC a θ η q.1 ℓ.succ q.2)
      (x.1, qaC (a ℓ) (x.2 * cR θ η x.1 ℓ) * cW θ η x.1 ℓ)) :
    AnalyticAt ℂ (fun q : ℂ × Matrix T d ℂ => netC a θ η q.1 ℓ.castSucc q.2) x := by
  have e : (fun q : ℂ × Matrix T d ℂ => netC a θ η q.1 ℓ.castSucc q.2)
      = (fun q : ℂ × Matrix T d ℂ => netC a θ η q.1 ℓ.succ q.2) ∘
        (fun q : ℂ × Matrix T d ℂ => (q.1, qaC (a ℓ) (q.2 * cR θ η q.1 ℓ) * cW θ η q.1 ℓ)) :=
    funext fun q => netC_castSucc a θ η q.1 ℓ q.2
  rw [e]
  exact AnalyticAt.comp (f := fun q : ℂ × Matrix T d ℂ =>
    (q.1, qaC (a ℓ) (q.2 * cR θ η q.1 ℓ) * cW θ η q.1 ℓ)) hnext (analyticAt_block_ffh a θ η ℓ x ha)

/-- The frozen gate values are entire. -/
private theorem analyticAt_aFC {ι : Type*} (s : Finset ι) (j : ι) (z : ℂ) :
    AnalyticAt ℂ (aFC s j) z := by
  by_cases h : j ∈ s
  · have e : aFC s j = id := funext fun y => by simp [aFC, h]
    rw [e]; exact analyticAt_id
  · have e : aFC s j = fun _ => 0 := funext fun y => by simp [aFC, h]
    rw [e]; exact analyticAt_const

omit [DecidableEq d] [Fintype dIn] in
/-- The complex frozen network is holomorphic in `(s, h)` everywhere (it is a polynomial). -/
private theorem analyticAt_netC_frozen (A : ∀ ℓ, Finset (hid ℓ))
    (θ η : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) (k : Fin (L + 1))
    (x : ℂ × Matrix T d ℂ) :
    AnalyticAt ℂ (fun q : ℂ × Matrix T d ℂ => netC (fun ℓ => aFC (A ℓ)) θ η q.1 k q.2) x := by
  induction k using Fin.reverseInduction generalizing x with
  | last => exact analyticAt_netC_last _ θ η x
  | cast ℓ ih =>
    exact analyticAt_netC_castSucc _ θ η ℓ x (fun τ j => analyticAt_aFC _ _ _) (ih _)

/-! ### The complex frozen network is homogeneous -/

/-- Helper: `qaC aF (c P) = c² qaC aF P`. -/
private theorem qaC_aFC_smul {m ι : Type*} (s : Finset ι) (c : ℂ) (P : Matrix m (ι ⊕ ι) ℂ) :
    qaC (aFC s) (c • P) = c ^ 2 • qaC (aFC s) P := by
  ext τ j
  simp only [qaC, aFC, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  split_ifs <;> ring

omit [Fintype T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- **The complex frozen network is homogeneous:** `𝓑°_{>k}(c h) = c^{2^{L−k}} 𝓑°_{>k}(h)`. -/
private theorem netC_frozen_smul (A : ∀ ℓ, Finset (hid ℓ))
    (θ η : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) (s : ℂ) (k : Fin (L + 1))
    (c : ℂ) (h : Matrix T d ℂ) :
    netC (fun ℓ => aFC (A ℓ)) θ η s k (c • h)
      = c ^ (2 ^ (L - (k : ℕ))) • netC (fun ℓ => aFC (A ℓ)) θ η s k h := by
  induction k using Fin.reverseInduction generalizing c h with
  | last =>
    rw [netC_last, netC_last, Fin.val_last, Nat.sub_self, pow_zero, pow_one]
    exact Matrix.smul_mul c h _
  | cast ℓ ih =>
    rw [netC_castSucc, netC_castSucc, Matrix.smul_mul, qaC_aFC_smul, Matrix.smul_mul, ih]
    have hL : L - (ℓ : ℕ) = (L - ((ℓ : ℕ) + 1)) + 1 := by
      have := ℓ.isLt
      omega
    rw [Fin.val_succ, Fin.val_castSucc, ← pow_mul, hL, pow_succ, mul_comm (2 : ℕ)]

/-- Helper: the partial derivative in `s` at `s = 0` of a map holomorphic in `(s, h)` is
holomorphic in `u`, along a holomorphic `u ↦ h(u)`. -/
private theorem analyticAt_partialDeriv_ffh {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {Φ : ℂ × E → F} {ι : E → E} {u₀ : E} (hΦ : AnalyticAt ℂ Φ (0, ι u₀))
    (hι : AnalyticAt ℂ ι u₀) : AnalyticAt ℂ (fun u => fderiv ℂ Φ (0, ι u) (1, 0)) u₀ := by
  have h1 : AnalyticAt ℂ (fderiv ℂ Φ) (0, ι u₀) := hΦ.fderiv
  have h2 : AnalyticAt ℂ (fun u => ((0 : ℂ), ι u)) u₀ := analyticAt_const.prod hι
  have h3 := AnalyticAt.comp (f := fun u => ((0 : ℂ), ι u)) h1 h2
  have h4 : AnalyticAt ℂ (fun Λ : (ℂ × E) →L[ℂ] F => Λ (1, 0)) (fderiv ℂ Φ (0, ι u₀)) :=
    (ContinuousLinearMap.apply ℂ F ((1 : ℂ), (0 : E))).analyticAt _
  exact AnalyticAt.comp (f := fun u => fderiv ℂ Φ (0, ι u)) h4 h3

/-- Helper: the cast of real matrices to complex matrices, as a real continuous linear map. -/
private noncomputable def castCLM_ffh (m n : Type*) [Fintype m] [Fintype n] :
    Matrix m n ℝ →L[ℝ] Matrix m n ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => M.map (fun x : ℝ => (x : ℂ))
      map_add' := fun A B => by ext i j; simp
      map_smul' := fun c A => by ext i j; simp [Complex.real_smul] }

/-- Helper: the partial derivative in `s` at `0` of a holomorphic `Φ(s, h)` whose restriction to
real `s` is the cast of a real map `f` is the cast of the derivative of `f`. -/
private theorem fderiv_ofReal_line_ffh {E m n : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [Fintype m] [Fintype n] {Φ : ℂ × E → Matrix m n ℂ} {x : E}
    (hΦ : DifferentiableAt ℂ Φ (0, x)) {f : ℝ → Matrix m n ℝ} {f' : Matrix m n ℝ}
    (hf : HasDerivAt f f' 0) (hΦf : ∀ r : ℝ, Φ ((r : ℂ), x) = (f r).map (fun a : ℝ => (a : ℂ))) :
    fderiv ℂ Φ (0, x) (1, 0) = f'.map (fun a : ℝ => (a : ℂ)) := by
  -- the derivative of `s ↦ Φ(s, x)` at `0`
  have hl : HasDerivAt (fun s : ℂ => (s, x)) ((1 : ℂ), (0 : E)) 0 :=
    (hasDerivAt_id (0 : ℂ)).prodMk (hasDerivAt_const (0 : ℂ) x)
  have hφ : HasDerivAt (fun s : ℂ => Φ (s, x)) (fderiv ℂ Φ (0, x) (1, 0)) ((0 : ℝ) : ℂ) := by
    rw [Complex.ofReal_zero]
    exact hΦ.hasFDerivAt.comp_hasDerivAt (0 : ℂ) hl
  -- restricted to real `s`
  have hψ := hφ.scomp (0 : ℝ) Complex.ofRealCLM.hasDerivAt
  rw [Complex.ofRealCLM_apply, Complex.ofReal_one, one_smul] at hψ
  -- the cast of `f`
  have hc : HasDerivAt (fun r : ℝ => castCLM_ffh m n (f r)) (castCLM_ffh m n f') 0 :=
    (castCLM_ffh m n).hasFDerivAt.comp_hasDerivAt 0 hf
  have e : ((fun s : ℂ => Φ (s, x)) ∘ Complex.ofReal) = fun r : ℝ => castCLM_ffh m n (f r) :=
    funext fun r => hΦf r
  rw [e] at hψ
  exact hψ.unique hc

/-- Helper: Cauchy's estimate at the centre of a closed disc on which `D` is differentiable. -/
private theorem norm_deriv_le_ffh {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {D : ℂ → F} {s₀ B : ℝ} (hs₀ : 0 < s₀) (hd : ∀ s : ℂ, ‖s‖ ≤ s₀ → DifferentiableAt ℂ D s)
    (hB : ∀ s : ℂ, ‖s‖ ≤ s₀ → ‖D s‖ ≤ B) : ‖deriv D 0‖ ≤ B / s₀ := by
  have hdc : DiffContOnCl ℂ D (Metric.ball 0 s₀) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball 0 hs₀.ne']
    intro s hs
    exact (hd s (mem_closedBall_zero_iff.mp hs)).differentiableWithinAt
  exact Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hs₀ hdc
    (fun s hs => hB s (mem_sphere_zero_iff_norm.mp hs).le)

/-- Helper: the partial derivative in `s` at `0`, along `(1, 0)`. -/
private theorem hasDerivAt_partial_ffh {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] {Φ : ℂ × E → F} {x : E} {s : ℂ}
    (hΦ : DifferentiableAt ℂ Φ (s, x)) :
    HasDerivAt (fun s' : ℂ => Φ (s', x)) (fderiv ℂ Φ (s, x) (1, 0)) s := by
  have hl : HasDerivAt (fun s' : ℂ => (s', x)) ((1 : ℂ), (0 : E)) s :=
    (hasDerivAt_id s).prodMk (hasDerivAt_const s x)
  exact hΦ.hasFDerivAt.comp_hasDerivAt s hl

/-! ### Norms of complex matrices -/

/-- `‖M N‖ ≤ n ‖M‖ ‖N‖` for the elementwise norm, complex entries. -/
private theorem norm_matMul_le_ffh {m n o : Type*} [Fintype m] [Fintype n] [Fintype o]
    (M : Matrix m n ℂ) (N : Matrix n o ℂ) : ‖M * N‖ ≤ Fintype.card n * ‖M‖ * ‖N‖ := by
  refine (Matrix.norm_le_iff (by positivity)).2 fun i k => ?_
  rw [Matrix.mul_apply]
  calc ‖∑ j, M i j * N j k‖ ≤ ∑ j, ‖M i j * N j k‖ := norm_sum_le _ _
    _ ≤ ∑ _j : n, ‖M‖ * ‖N‖ := Finset.sum_le_sum fun j _ => by
        rw [norm_mul]
        exact mul_le_mul (Matrix.norm_apply_le_norm M) (Matrix.norm_apply_le_norm N)
          (norm_nonneg _) (norm_nonneg _)
    _ = Fintype.card n * ‖M‖ * ‖N‖ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc]

/-! ### Absorbing powers of `t`, and a map holomorphic everywhere is Lipschitz on balls -/

/-- **Absorbing the powers of `t`:** eventually `c t^N e^{−a t^p} ≤ e^{−(a/2) t^p}` (`p ≥ 1`). -/
private theorem absorb_ffh (hp : 1 ≤ p) {a : ℝ} (ha : 0 < a) (c : ℝ) (N : ℕ) :
    ∃ t₁ : ℝ, ∀ t : ℝ, t₁ ≤ t →
      c * t ^ N * Real.exp (-(a * t ^ p)) ≤ Real.exp (-(a / 2 * t ^ p)) := by
  -- `|c| t^N e^{−a t / 2} → 0`
  have hlim := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (N : ℝ) (a / 2)
    (half_pos ha)).const_mul |c|
  rw [mul_zero] at hlim
  obtain ⟨t₁, ht₁⟩ := Filter.eventually_atTop.1 ((hlim.eventually (Iic_mem_nhds one_pos)).and
    (Filter.eventually_ge_atTop 1))
  refine ⟨t₁, fun t ht => ?_⟩
  obtain ⟨hl, ht1⟩ := ht₁ t ht
  have ht0 : 0 ≤ t := zero_le_one.trans ht1
  rw [Real.rpow_natCast] at hl
  have htp : t ≤ t ^ p := le_self_pow₀ ht1 (by omega)
  have h1 : Real.exp (-(a / 2 * t ^ p)) ≤ Real.exp (-(a / 2) * t) := by
    apply Real.exp_le_exp.2
    have := mul_le_mul_of_nonneg_left htp (half_pos ha).le
    linarith
  have hsplit : Real.exp (-(a * t ^ p))
      = Real.exp (-(a / 2 * t ^ p)) * Real.exp (-(a / 2 * t ^ p)) := by
    rw [← Real.exp_add]; ring_nf
  calc c * t ^ N * Real.exp (-(a * t ^ p))
      ≤ |c| * t ^ N * Real.exp (-(a * t ^ p)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self c) (pow_nonneg ht0 N))
          (Real.exp_pos _).le
    _ = (|c| * (t ^ N * Real.exp (-(a / 2 * t ^ p)))) * Real.exp (-(a / 2 * t ^ p)) := by
        rw [hsplit]; ring
    _ ≤ (|c| * (t ^ N * Real.exp (-(a / 2) * t))) * Real.exp (-(a / 2 * t ^ p)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left h1 (pow_nonneg ht0 N)) (abs_nonneg c)) (Real.exp_pos _).le
    _ ≤ 1 * Real.exp (-(a / 2 * t ^ p)) := mul_le_mul_of_nonneg_right hl (Real.exp_pos _).le
    _ = Real.exp (-(a / 2 * t ^ p)) := one_mul _

/-- A map holomorphic everywhere on a proper space is Lipschitz on every closed ball (its
derivative is continuous, hence bounded there, and the ball is convex). -/
private theorem exists_lipschitz_closedBall_ffh {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [ProperSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {f : E → F} (hf : ∀ x, AnalyticAt ℂ f x) (x₀ : E) (r : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Metric.closedBall x₀ r, ∀ y ∈ Metric.closedBall x₀ r,
      ‖f x - f y‖ ≤ C * ‖x - y‖ := by
  have hf' : AnalyticOnNhd ℂ f Set.univ := fun x _ => hf x
  obtain ⟨C, hC⟩ := (isCompact_closedBall x₀ r).exists_bound_of_continuousOn
    (hf'.fderiv.continuousOn.mono (Set.subset_univ _))
  refine ⟨max C 0, le_max_right _ _, fun x hx y hy => ?_⟩
  exact (convex_closedBall x₀ r).norm_image_sub_le_of_norm_fderiv_le
    (fun z _ => (hf z).differentiableAt) (fun z hz => (hC z hz).trans (le_max_left _ _)) hy hx

/-! ### One gate far out, at complex arguments -/

/-- A positive function on a finite type has a positive lower bound `2μ` (as in
`Depth/FrozenFar.lean`). -/
private theorem exists_pos_two_mul_le_ffh {α : Type*} [Finite α] (f : α → ℝ)
    (hf : ∀ a, 0 < f a) : ∃ μ : ℝ, 0 < μ ∧ ∀ a, 2 * μ ≤ f a := by
  cases isEmpty_or_nonempty α with
  | inl h => exact ⟨1, one_pos, fun a => (IsEmpty.false a).elim⟩
  | inr h =>
    obtain ⟨a₀, ha₀⟩ := Finite.exists_min f
    exact ⟨f a₀ / 2, half_pos (hf a₀), fun a => by linarith [ha₀ a]⟩

/-- **One gate far out** (equation (31)): at `z = t w` with `‖w − m‖ ≤ μ/2` for a real `m` of the
sign of the unit, `|m| ≥ 2μ`, and `t μ ≥ R`, the gate `σc` is holomorphic at `z` and
`‖σc(z) − aF(z)‖ ≤ e^{−κ μ^p t^p}`: `Re(±z) ≥ t μ` and `|Im z| ≤ ½ Re(±z)`. -/
private theorem gate_far_ffh {σc : ℂ → ℂ} {R κ : ℝ}
    (hfar : ∀ z : ℂ, R ≤ z.re → |z.im| ≤ z.re / 2 →
      AnalyticAt ℂ σc z ∧ AnalyticAt ℂ σc (-z) ∧
        ‖σc z - z‖ ≤ Real.exp (-(κ * z.re ^ p)) ∧ ‖σc (-z)‖ ≤ Real.exp (-(κ * z.re ^ p)))
    (hκ : 0 < κ) {ι : Type*} (s : Finset ι) (j : ι) {μ m t : ℝ} {w : ℂ} (hμ : 0 < μ)
    (ht : 0 ≤ t) (htR : R ≤ t * μ) (hw : ‖w - m‖ ≤ μ / 2) (hpos : j ∈ s → 2 * μ ≤ m)
    (hneg : j ∉ s → m ≤ -(2 * μ)) :
    AnalyticAt ℂ σc ((t : ℂ) * w) ∧
      ‖σc ((t : ℂ) * w) - aFC s j ((t : ℂ) * w)‖ ≤ Real.exp (-(κ * μ ^ p * t ^ p)) := by
  have hre : |w.re - m| ≤ μ / 2 := by
    have h := Complex.abs_re_le_norm (w - m)
    rw [Complex.sub_re, Complex.ofReal_re] at h
    exact h.trans hw
  have him : |w.im| ≤ μ / 2 := by
    have h := Complex.abs_im_le_norm (w - m)
    rw [Complex.sub_im, Complex.ofReal_im, sub_zero] at h
    exact h.trans hw
  -- `e^{−κ x^p} ≤ e^{−κ (t μ)^p}` for `x ≥ t μ ≥ 0`
  have hmono : ∀ x : ℝ, t * μ ≤ x →
      Real.exp (-(κ * x ^ p)) ≤ Real.exp (-(κ * μ ^ p * t ^ p)) := by
    intro x hx
    apply Real.exp_le_exp.2
    have h1 : (t * μ) ^ p ≤ x ^ p := pow_le_pow_left₀ (by positivity) hx p
    rw [mul_pow] at h1
    nlinarith
  by_cases hj : j ∈ s
  · -- an active unit: `Re z ≥ t μ` and `|Im z| ≤ Re z / 2`
    have hm := hpos hj
    have hwre : μ ≤ w.re := by linarith [(abs_le.1 hre).1]
    have h1 : t * μ ≤ ((t : ℂ) * w).re := by
      rw [Complex.re_ofReal_mul]; exact mul_le_mul_of_nonneg_left hwre ht
    have h2 : |((t : ℂ) * w).im| ≤ ((t : ℂ) * w).re / 2 := by
      rw [Complex.re_ofReal_mul, Complex.im_ofReal_mul, abs_mul, abs_of_nonneg ht]
      nlinarith [mul_nonneg ht (by linarith : 0 ≤ w.re / 2 - |w.im|)]
    obtain ⟨ha, -, hb, -⟩ := hfar _ (htR.trans h1) h2
    have e : aFC s j ((t : ℂ) * w) = (t : ℂ) * w := by simp [aFC, hj]
    rw [e]
    exact ⟨ha, hb.trans (hmono _ h1)⟩
  · -- an inactive unit: the same for `−z`
    have hm := hneg hj
    have hwre : μ ≤ (-w).re := by rw [Complex.neg_re]; linarith [(abs_le.1 hre).2]
    have e1 : -((t : ℂ) * -w) = (t : ℂ) * w := by ring
    have h1 : t * μ ≤ ((t : ℂ) * -w).re := by
      rw [Complex.re_ofReal_mul]; exact mul_le_mul_of_nonneg_left hwre ht
    have h2 : |((t : ℂ) * -w).im| ≤ ((t : ℂ) * -w).re / 2 := by
      rw [Complex.re_ofReal_mul, Complex.im_ofReal_mul, abs_mul, abs_of_nonneg ht,
        Complex.neg_im, abs_neg]
      nlinarith [mul_nonneg ht (by linarith : 0 ≤ (-w).re / 2 - |w.im|)]
    obtain ⟨-, ha, -, hb⟩ := hfar _ (htR.trans h1) h2
    rw [e1] at ha hb
    have e : aFC s j ((t : ℂ) * w) = 0 := by simp [aFC, hj]
    rw [e, sub_zero]
    exact ⟨ha, hb.trans (hmono _ h1)⟩

/-- The hidden units with two gate values that differ by at most `ε` at the gates, at values at
most `Z`: `‖qaC a P − qaC b P‖ ≤ ε Z`. -/
private theorem norm_qaC_sub_le_ffh {m ι : Type*} [Fintype m] [Fintype ι] (a b : ι → ℂ → ℂ)
    (P : Matrix m (ι ⊕ ι) ℂ) {ε Z : ℝ} (hε : 0 ≤ ε) (hZ : 0 ≤ Z)
    (hab : ∀ τ j, ‖a j (P τ (Sum.inl j)) - b j (P τ (Sum.inl j))‖ ≤ ε)
    (hP : ∀ τ j, ‖P τ (Sum.inr j)‖ ≤ Z) : ‖qaC a P - qaC b P‖ ≤ ε * Z := by
  refine (Matrix.norm_le_iff (mul_nonneg hε hZ)).2 fun τ j => ?_
  rw [Matrix.sub_apply]
  simp only [qaC, Matrix.of_apply]
  rw [← sub_mul, norm_mul]
  exact mul_le_mul (hab τ j) (hP τ j) (norm_nonneg _) hε

/-! ### The induction over the blocks -/

/-- The claim of Lemma D.11 at `k` for complex `u` and complex weights `θ + s η`, for all `H` with
rows in `C k`: for `t ≥ t₀`, `|s| ≤ s₀` and `‖u‖ ≤ ϱ`, at `h = t (H + u)`, the complex network is
holomorphic in `(s, h)` and it differs from the complex frozen network by at most `e^{−κ t^p}`. -/
private def FarBoundC (σc : ℂ → ℂ) (p : ℕ) (C : Fin (L + 1) → Set (d → ℝ))
    (A : ∀ ℓ, Finset (hid ℓ)) (θ η : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (k : Fin (L + 1)) : Prop :=
  ∀ H : Matrix T d ℝ, (∀ τ, H τ ∈ C k) →
    ∃ ϱ : ℝ, 0 < ϱ ∧ ∃ s₀ : ℝ, 0 < s₀ ∧ ∃ κ : ℝ, 0 < κ ∧ ∃ t₀ : ℝ, ∀ t : ℝ, t₀ ≤ t →
      ∀ s : ℂ, ‖s‖ ≤ s₀ → ∀ u : Matrix T d ℂ, ‖u‖ ≤ ϱ →
        AnalyticAt ℂ (fun q : ℂ × Matrix T d ℂ => netC (fun _ _ => σc) θ η q.1 k q.2)
          (s, (t : ℂ) • (H.map (fun x : ℝ => (x : ℂ)) + u)) ∧
        ‖netC (fun _ _ => σc) θ η s k ((t : ℂ) • (H.map (fun x : ℝ => (x : ℂ)) + u))
            - netC (fun ℓ => aFC (A ℓ)) θ η s k ((t : ℂ) • (H.map (fun x : ℝ => (x : ℂ)) + u))‖
          ≤ Real.exp (-(κ * t ^ p))

omit [DecidableEq d] [Fintype dIn] in
/-- `k = L`: both networks are `h ↦ h D(s)`. -/
private theorem farBoundC_last (σc : ℂ → ℂ) (C : Fin (L + 1) → Set (d → ℝ))
    (A : ∀ ℓ, Finset (hid ℓ)) (θ η : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) :
    FarBoundC σc p C A θ η (Fin.last L) := by
  intro H _
  refine ⟨1, one_pos, 1, one_pos, 1, one_pos, 0, fun t _ s _ u _ =>
    ⟨analyticAt_netC_last _ θ η _, ?_⟩⟩
  rw [netC_last, netC_last, sub_self, norm_zero]
  exact (Real.exp_pos _).le

/-- **The step from `ℓ + 1` to `ℓ`** (proof of Lemma D.11, for complex `u` and `s`): the claim
after block `ℓ`, at every `H'` with rows in `C_{ℓ+1}`, gives it before the block, at every `H`
with rows in `C_ℓ`. -/
private theorem farBoundC_castSucc (hp : 1 ≤ p) {σc : ℂ → ℂ} {R κg : ℝ} (hκg : 0 < κg)
    (hfar : ∀ z : ℂ, R ≤ z.re → |z.im| ≤ z.re / 2 →
      AnalyticAt ℂ σc z ∧ AnalyticAt ℂ σc (-z) ∧
        ‖σc z - z‖ ≤ Real.exp (-(κg * z.re ^ p)) ∧ ‖σc (-z)‖ ≤ Real.exp (-(κg * z.re ^ p)))
    {C : Fin (L + 1) → Set (d → ℝ)} {A : ∀ ℓ, Finset (hid ℓ)}
    {θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut}
    (hθ : GoodForConesGated C A θ) (η : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (ℓ : Fin L) (ih : FarBoundC σc p C A θ η ℓ.succ) : FarBoundC σc p C A θ η ℓ.castSucc := by
  intro H hH
  -- step 1: the gates of `H` have the signs of the active set, and are `2μ` away from zero
  have hgp : ∀ τ, ∀ j ∈ A ℓ, 0 < (H * θ.read ℓ) τ (Sum.inl j) := fun τ j hj =>
    hθ.gate_pos ℓ (H τ) (hH τ) j hj
  have hgn : ∀ τ, ∀ j ∉ A ℓ, (H * θ.read ℓ) τ (Sum.inl j) < 0 := fun τ j hj =>
    hθ.gate_neg ℓ (H τ) (hH τ) j hj
  have hsign : ∀ τ j, 0 < |(H * θ.read ℓ) τ (Sum.inl j)| := by
    intro τ j
    by_cases hj : j ∈ A ℓ
    · exact abs_pos.2 (hgp τ j hj).ne'
    · exact abs_pos.2 (hgn τ j hj).ne
  obtain ⟨μ, hμ, hμle⟩ := exists_pos_two_mul_le_ffh
    (fun a : T × hid ℓ => |(H * θ.read ℓ) a.1 (Sum.inl a.2)|) fun a => hsign a.1 a.2
  have hpos : ∀ τ, ∀ j ∈ A ℓ, 2 * μ ≤ (H * θ.read ℓ) τ (Sum.inl j) := fun τ j hj => by
    have h1 := hμle (τ, j)
    rwa [abs_of_pos (hgp τ j hj)] at h1
  have hneg : ∀ τ, ∀ j ∉ A ℓ, (H * θ.read ℓ) τ (Sum.inl j) ≤ -(2 * μ) := fun τ j hj => by
    have h1 := hμle (τ, j)
    rw [abs_of_neg (hgn τ j hj)] at h1
    linarith only [h1]
  -- step 3: the frozen block sends `H` to `H'`, with rows in `C_{ℓ+1}`
  obtain ⟨H', hH'⟩ : ∃ H', H' = (Arch.frozen (T := T) (d := d) A).f ℓ (H * θ.read ℓ)
      * θ.write ℓ := ⟨_, rfl⟩
  have hH'C : ∀ τ, H' τ ∈ C ℓ.succ := fun τ => by
    rw [hH', frozen_block_apply A θ ℓ H τ]
    exact hθ.frozen_mem ℓ (H τ) (hH τ)
  -- the complex `H`, `H'`, and the frozen block at `(0, H)`
  obtain ⟨Hc, hHc⟩ : ∃ Hc, Hc = H.map (fun x : ℝ => (x : ℂ)) := ⟨_, rfl⟩
  obtain ⟨H'c, hH'c⟩ : ∃ H'c, H'c = H'.map (fun x : ℝ => (x : ℂ)) := ⟨_, rfl⟩
  have hR0 : cR θ η 0 ℓ = (θ.read ℓ).map (fun x : ℝ => (x : ℂ)) := by simp [cR]
  have hW0 : cW θ η 0 ℓ = (θ.write ℓ).map (fun x : ℝ => (x : ℂ)) := by simp [cW]
  have hQ0 : Hc * cR θ η 0 ℓ = (H * θ.read ℓ).map (fun x : ℝ => (x : ℂ)) := by
    rw [hR0, hHc, map_mul_ofReal_ffh]
  have hB0 : qaC (aFC (A ℓ)) (Hc * cR θ η 0 ℓ) * cW θ η 0 ℓ = H'c := by
    rw [hQ0, hW0, hH'c, hH',
      map_mul_ofReal_ffh ((Arch.frozen (T := T) (d := d) A).f ℓ (H * θ.read ℓ)),
      qaC_frozen_ofReal (d := d) A ℓ]
  -- the induction hypothesis at `H'`
  obtain ⟨ϱ', hϱ', s₀', hs₀', κ', hκ', t₀', hIH⟩ := ih H' hH'C
  -- step 4: the frozen network after the block is Lipschitz on a ball around `(0, H')`
  have : ProperSpace (Matrix T d ℂ) := inferInstanceAs (ProperSpace (T → d → ℂ))
  obtain ⟨Cf, hCf0, hCf⟩ := exists_lipschitz_closedBall_ffh
    (analyticAt_netC_frozen A θ η ℓ.succ) ((0 : ℂ), H'c) (max s₀' ϱ')
  -- continuity at `(0, H)` of the pre-activations, of the write and of the frozen block
  have hcQ : ContinuousAt (fun q : ℂ × Matrix T d ℂ => q.2 * cR θ η q.1 ℓ) ((0 : ℂ), Hc) :=
    (analyticAt_matMul_ffh analyticAt_snd (analyticAt_line_ffh _ _ analyticAt_fst)).continuousAt
  have hcW : ContinuousAt (fun q : ℂ × Matrix T d ℂ => cW θ η q.1 ℓ) ((0 : ℂ), Hc) :=
    (analyticAt_line_ffh _ _ analyticAt_fst).continuousAt
  have hcB : ContinuousAt (fun q : ℂ × Matrix T d ℂ =>
      qaC (aFC (A ℓ)) (q.2 * cR θ η q.1 ℓ) * cW θ η q.1 ℓ) ((0 : ℂ), Hc) :=
    (analyticAt_matMul_ffh (analyticAt_qaC_ffh (a := aFC (A ℓ))
      (analyticAt_matMul_ffh analyticAt_snd (analyticAt_line_ffh _ _ analyticAt_fst))
      fun τ j => analyticAt_aFC _ _ _) (analyticAt_line_ffh _ _ analyticAt_fst)).continuousAt
  obtain ⟨δ₁, hδ₁, hδ₁c⟩ := Metric.continuousAt_iff.1 hcQ (μ / 2) (half_pos hμ)
  obtain ⟨δ₂, hδ₂, hδ₂c⟩ := Metric.continuousAt_iff.1 hcW 1 one_pos
  obtain ⟨δ₃, hδ₃, hδ₃c⟩ := Metric.continuousAt_iff.1 hcB (ϱ' / 2) (half_pos hϱ')
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = min δ₁ (min δ₂ δ₃) := ⟨_, rfl⟩
  have hδ : 0 < δ := by rw [hδdef]; exact lt_min hδ₁ (lt_min hδ₂ hδ₃)
  have hδ1 : δ ≤ δ₁ := by rw [hδdef]; exact min_le_left _ _
  have hδ2 : δ ≤ δ₂ := by rw [hδdef]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hδ3 : δ ≤ δ₃ := by rw [hδdef]; exact (min_le_right _ _).trans (min_le_right _ _)
  -- the constants of the block bound: `‖g − g°‖ ≤ K t e^{−a t^p}`
  obtain ⟨Z₀, hZ₀⟩ : ∃ Z₀ : ℝ, Z₀ = ‖Hc * cR θ η 0 ℓ‖ + μ / 2 := ⟨_, rfl⟩
  obtain ⟨W₀, hW₀⟩ : ∃ W₀ : ℝ, W₀ = ‖cW θ η 0 ℓ‖ + 1 := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = Fintype.card (hid ℓ) * Z₀ * W₀ := ⟨_, rfl⟩
  have hZ₀0 : 0 ≤ Z₀ := by rw [hZ₀]; positivity
  have hW₀0 : 0 ≤ W₀ := by rw [hW₀]; positivity
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  obtain ⟨a, ha_def⟩ : ∃ a : ℝ, a = κg * μ ^ p := ⟨_, rfl⟩
  have ha : 0 < a := by rw [ha_def]; positivity
  -- the degree of the frozen network after the block
  obtain ⟨M, hM⟩ : ∃ M : ℕ, M = 2 ^ (L - ((ℓ.succ : Fin (L + 1)) : ℕ)) := ⟨_, rfl⟩
  -- absorbing the powers of `t`
  obtain ⟨t₁, ht₁⟩ := absorb_ffh hp ha (2 * K / ϱ') 1
  obtain ⟨t₂, ht₂⟩ := absorb_ffh hp ha (Cf * K) (2 * M + 1)
  obtain ⟨b, hb_def⟩ : ∃ b : ℝ, b = min κ' (a / 2) := ⟨_, rfl⟩
  have hb : 0 < b := by rw [hb_def]; exact lt_min hκ' (half_pos ha)
  obtain ⟨t₃, ht₃⟩ := absorb_ffh hp hb 2 0
  refine ⟨δ / 2, half_pos hδ, min (δ / 2) s₀', lt_min (half_pos hδ) hs₀', b / 2, half_pos hb,
    max (max 1 t₀') (max (R / μ) (max t₁ (max t₂ t₃))), fun t ht s hs u hu => ?_⟩
  rw [← hHc]
  -- the thresholds on `t`
  have ht1 : 1 ≤ t := (le_max_left _ _).trans ((le_max_left _ _).trans ht)
  have ht0 : 0 ≤ t := zero_le_one.trans ht1
  have htt₀' : t₀' ≤ t ^ 2 := by
    have h1 : t₀' ≤ t := (le_max_right _ _).trans ((le_max_left _ _).trans ht)
    exact h1.trans (le_self_pow₀ ht1 two_ne_zero)
  have htR : R ≤ t * μ := by
    have h1 : R / μ ≤ t := (le_max_left _ _).trans ((le_max_right _ _).trans ht)
    rwa [div_le_iff₀ hμ] at h1
  have htt₁ : t₁ ≤ t :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ht))
  have htt₂ : t₂ ≤ t := (le_max_left _ _).trans ((le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans ht)))
  have htt₃ : t₃ ≤ t := (le_max_right _ _).trans ((le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans ht)))
  have hst : ‖s‖ ≤ s₀' := hs.trans (min_le_right _ _)
  -- the point `(s, H + u)` is `δ`-close to `(0, H)`
  have hq : dist ((s, Hc + u) : ℂ × Matrix T d ℂ) ((0 : ℂ), Hc) < δ := by
    rw [dist_eq_norm, Prod.mk_sub_mk, sub_zero, add_sub_cancel_left, Prod.norm_mk]
    exact max_lt (lt_of_le_of_lt (hs.trans (min_le_left _ _)) (half_lt_self hδ))
      (lt_of_le_of_lt hu (half_lt_self hδ))
  -- names: `Q = (H + u) W_read(s)` (so the pre-activations are `t Q`) and `Wq = W_write(s)`
  obtain ⟨Q, hQdef⟩ : ∃ Q, Q = (Hc + u) * cR θ η s ℓ := ⟨_, rfl⟩
  obtain ⟨Wq, hWq⟩ : ∃ Wq, Wq = cW θ η s ℓ := ⟨_, rfl⟩
  have hP : ((t : ℂ) • (Hc + u)) * cR θ η s ℓ = (t : ℂ) • Q := by rw [hQdef, Matrix.smul_mul]
  have hQ : ‖Q - Hc * cR θ η 0 ℓ‖ < μ / 2 := by
    have h := hδ₁c (lt_of_lt_of_le hq hδ1)
    rw [dist_eq_norm] at h
    dsimp only at h
    rw [hQdef]; exact h
  have hWn : ‖Wq‖ ≤ W₀ := by
    have h := hδ₂c (lt_of_lt_of_le hq hδ2)
    rw [dist_eq_norm] at h
    dsimp only at h
    have h2 := norm_le_insert' (cW θ η s ℓ) (cW θ η 0 ℓ)
    rw [hW₀, hWq]
    linarith only [h, h2]
  -- step 2, the gates: each is holomorphic, and `‖σc(z) − aF(z)‖ ≤ e^{−a t^p}`
  have hgate : ∀ τ j, AnalyticAt ℂ σc (((t : ℂ) • Q) τ (Sum.inl j)) ∧
      ‖σc (((t : ℂ) • Q) τ (Sum.inl j)) - aFC (A ℓ) j (((t : ℂ) • Q) τ (Sum.inl j))‖
        ≤ Real.exp (-(a * t ^ p)) := by
    intro τ j
    have hw : ‖Q τ (Sum.inl j) - ((H * θ.read ℓ) τ (Sum.inl j) : ℂ)‖ ≤ μ / 2 := by
      have h1 : Q τ (Sum.inl j) - ((H * θ.read ℓ) τ (Sum.inl j) : ℂ)
          = (Q - Hc * cR θ η 0 ℓ) τ (Sum.inl j) := by
        rw [Matrix.sub_apply, hQ0, Matrix.map_apply]
      rw [h1]
      exact (Matrix.norm_apply_le_norm _).trans hQ.le
    have e : ((t : ℂ) • Q) τ (Sum.inl j) = (t : ℂ) * Q τ (Sum.inl j) := by
      rw [Matrix.smul_apply, smul_eq_mul]
    rw [e, ha_def]
    exact gate_far_ffh hfar hκg (A ℓ) j hμ ht0 htR hw (hpos τ j) (hneg τ j)
  -- the values: `‖t Q_{τ, inr j}‖ ≤ t Z₀`
  have hQn : ‖Q‖ ≤ Z₀ := by
    have h := norm_le_insert' Q (Hc * cR θ η 0 ℓ)
    rw [hZ₀]; linarith only [h, hQ]
  have hval : ∀ τ j, ‖((t : ℂ) • Q) τ (Sum.inr j)‖ ≤ t * Z₀ := fun τ j => by
    rw [Matrix.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg ht0]
    exact mul_le_mul_of_nonneg_left ((Matrix.norm_apply_le_norm Q).trans hQn) ht0
  -- the two blocks: `g = qaC σc (t Q) Wq` and `g° = qaC aF (t Q) Wq = t² z₂`
  obtain ⟨g, hg⟩ : ∃ g, g = qaC (fun _ => σc) ((t : ℂ) • Q) * Wq := ⟨_, rfl⟩
  obtain ⟨z₂, hz₂⟩ : ∃ z₂, z₂ = qaC (aFC (A ℓ)) Q * Wq := ⟨_, rfl⟩
  have hg0 : qaC (aFC (A ℓ)) ((t : ℂ) • Q) * Wq = (t : ℂ) ^ 2 • z₂ := by
    rw [qaC_aFC_smul, Matrix.smul_mul, hz₂]
  -- `‖g − g°‖ ≤ K t e^{−a t^p}`
  have hgg : ‖g - (t : ℂ) ^ 2 • z₂‖ ≤ K * t * Real.exp (-(a * t ^ p)) := by
    rw [← hg0, hg, ← Matrix.sub_mul]
    refine (norm_matMul_le_ffh _ _).trans ?_
    have h1 := norm_qaC_sub_le_ffh (fun _ => σc) (aFC (A ℓ)) ((t : ℂ) • Q) (Real.exp_pos _).le
      (mul_nonneg ht0 hZ₀0) (fun τ j => (hgate τ j).2) hval
    calc (Fintype.card (hid ℓ) : ℝ)
          * ‖qaC (fun _ => σc) ((t : ℂ) • Q) - qaC (aFC (A ℓ)) ((t : ℂ) • Q)‖ * ‖Wq‖
        ≤ Fintype.card (hid ℓ) * (Real.exp (-(a * t ^ p)) * (t * Z₀)) * W₀ := by gcongr
      _ = K * t * Real.exp (-(a * t ^ p)) := by rw [hK]; ring
  -- `z₂` is `ϱ'/2`-close to `H'`, by continuity of the frozen block
  have hz₂H : ‖z₂ - H'c‖ ≤ ϱ' / 2 := by
    have h := hδ₃c (lt_of_lt_of_le hq hδ3)
    rw [dist_eq_norm] at h
    dsimp only at h
    rw [hz₂, hQdef, hWq, ← hB0]
    exact h.le
  -- and so is `z₁ = g / t²`, for large `t`
  have ht2 : (1 : ℝ) ≤ t ^ 2 := one_le_pow₀ ht1
  have htc : ((t : ℂ) ^ 2) ≠ 0 :=
    pow_ne_zero 2 (Complex.ofReal_ne_zero.2 (zero_lt_one.trans_le ht1).ne')
  obtain ⟨z₁, hz₁⟩ : ∃ z₁, z₁ = ((t : ℂ) ^ 2)⁻¹ • g := ⟨_, rfl⟩
  have hgz : g = (t : ℂ) ^ 2 • z₁ := by rw [hz₁, smul_smul, mul_inv_cancel₀ htc, one_smul]
  have hnt2 : ‖((t : ℂ) ^ 2)‖ = t ^ 2 := by
    rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg ht0]
  have hz₁₂ : ‖z₁ - z₂‖ ≤ K * t * Real.exp (-(a * t ^ p)) := by
    have e : z₁ - z₂ = ((t : ℂ) ^ 2)⁻¹ • (g - (t : ℂ) ^ 2 • z₂) := by
      rw [hz₁, smul_sub, smul_smul, inv_mul_cancel₀ htc, one_smul]
    rw [e, norm_smul, norm_inv, hnt2]
    refine le_trans ?_ hgg
    exact mul_le_of_le_one_left (norm_nonneg _) (inv_le_one_of_one_le₀ ht2)
  have hsmall : K * t * Real.exp (-(a * t ^ p)) ≤ ϱ' / 2 := by
    have h1 := ht₁ t htt₁
    rw [pow_one] at h1
    have h2 : Real.exp (-(a / 2 * t ^ p)) ≤ 1 :=
      Real.exp_le_one_iff.2 (neg_nonpos.2 (mul_nonneg (half_pos ha).le (pow_nonneg ht0 p)))
    have e : K * t * Real.exp (-(a * t ^ p))
        = ϱ' / 2 * (2 * K / ϱ' * t * Real.exp (-(a * t ^ p))) := by
      field_simp
    rw [e]
    calc ϱ' / 2 * (2 * K / ϱ' * t * Real.exp (-(a * t ^ p))) ≤ ϱ' / 2 * 1 :=
          mul_le_mul_of_nonneg_left (h1.trans h2) (by positivity)
      _ = ϱ' / 2 := mul_one _
  have hz₁H : ‖z₁ - H'c‖ ≤ ϱ' := by
    have := norm_sub_le_norm_sub_add_norm_sub z₁ z₂ H'c
    linarith only [this, hz₁₂, hsmall, hz₂H]
  -- step 5: the induction hypothesis at `t²`, `s` and `u' = z₁ − H'`
  obtain ⟨i1, i2⟩ := hIH (t ^ 2) htt₀' s hst (z₁ - H'c) hz₁H
  have e2 : (((t ^ 2 : ℝ)) : ℂ) • (H'.map (fun x : ℝ => (x : ℂ)) + (z₁ - H'c)) = g := by
    rw [← hH'c, add_sub_cancel, hgz]
    push_cast
    rfl
  rw [e2] at i1 i2
  have hexp : Real.exp (-(κ' * (t ^ 2) ^ p)) ≤ Real.exp (-(κ' * t ^ p)) :=
    Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ ht0 (le_self_pow₀ ht1 two_ne_zero) p) hκ'.le))
  -- the frozen network between `g°` and `g`: homogeneity and the Lipschitz bound
  have hmem : ∀ z, ‖z - H'c‖ ≤ ϱ' →
      ((s, z) : ℂ × Matrix T d ℂ) ∈ Metric.closedBall ((0 : ℂ), H'c) (max s₀' ϱ') := by
    intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm, Prod.mk_sub_mk, sub_zero, Prod.norm_mk]
    exact max_le_max hst hz
  have hlip : ‖netC (fun ℓ => aFC (A ℓ)) θ η s ℓ.succ z₁
      - netC (fun ℓ => aFC (A ℓ)) θ η s ℓ.succ z₂‖ ≤ Cf * ‖z₁ - z₂‖ := by
    have h := hCf _ (hmem z₁ hz₁H) _ (hmem z₂ (by linarith only [hz₂H, hϱ']))
    have e : ((s, z₁) : ℂ × Matrix T d ℂ) - (s, z₂) = (0, z₁ - z₂) := by
      rw [Prod.mk_sub_mk, sub_self]
    rw [e, Prod.norm_mk, norm_zero, max_eq_right (norm_nonneg _)] at h
    exact h
  have hfro : ‖netC (fun ℓ => aFC (A ℓ)) θ η s ℓ.succ g
      - netC (fun ℓ => aFC (A ℓ)) θ η s ℓ.succ ((t : ℂ) ^ 2 • z₂)‖
        ≤ t ^ (2 * M) * (Cf * ‖z₁ - z₂‖) := by
    rw [hgz, netC_frozen_smul, netC_frozen_smul, ← smul_sub, norm_smul, norm_pow, hnt2, ← hM,
      ← pow_mul]
    exact mul_le_mul_of_nonneg_left hlip (by positivity)
  -- the sum of the two
  have htot : ‖netC (fun _ _ => σc) θ η s ℓ.succ g
      - netC (fun ℓ => aFC (A ℓ)) θ η s ℓ.succ ((t : ℂ) ^ 2 • z₂)‖
        ≤ Real.exp (-(b / 2 * t ^ p)) := by
    have t1 := norm_sub_le_norm_sub_add_norm_sub (netC (fun _ _ => σc) θ η s ℓ.succ g)
      (netC (fun ℓ => aFC (A ℓ)) θ η s ℓ.succ g)
      (netC (fun ℓ => aFC (A ℓ)) θ η s ℓ.succ ((t : ℂ) ^ 2 • z₂))
    have h2 := ht₂ t htt₂
    have h3 := ht₃ t htt₃
    rw [pow_zero, mul_one] at h3
    have htp : 0 ≤ t ^ p := pow_nonneg ht0 p
    have hb1 : Real.exp (-(κ' * t ^ p)) ≤ Real.exp (-(b * t ^ p)) := Real.exp_le_exp.2
      (neg_le_neg (mul_le_mul_of_nonneg_right (hb_def ▸ min_le_left _ _) htp))
    have hb2 : Real.exp (-(a / 2 * t ^ p)) ≤ Real.exp (-(b * t ^ p)) := Real.exp_le_exp.2
      (neg_le_neg (mul_le_mul_of_nonneg_right (hb_def ▸ min_le_right _ _) htp))
    have hfro' : t ^ (2 * M) * (Cf * ‖z₁ - z₂‖)
        ≤ Cf * K * t ^ (2 * M + 1) * Real.exp (-(a * t ^ p)) := by
      calc t ^ (2 * M) * (Cf * ‖z₁ - z₂‖)
          ≤ t ^ (2 * M) * (Cf * (K * t * Real.exp (-(a * t ^ p)))) := by gcongr
        _ = _ := by ring
    linarith only [t1, i2, hexp, hb1, hfro, hfro', h2, hb2, h3]
  refine ⟨?_, ?_⟩
  · -- holomorphy through the block
    refine analyticAt_netC_castSucc _ θ η ℓ _ (fun τ j => ?_) ?_
    · show AnalyticAt ℂ σc ((((t : ℂ) • (Hc + u)) * cR θ η s ℓ) τ (Sum.inl j))
      rw [hP]
      exact (hgate τ j).1
    · show AnalyticAt ℂ (fun q : ℂ × Matrix T d ℂ => netC (fun _ _ => σc) θ η q.1 ℓ.succ q.2)
        (s, qaC (fun _ => σc) (((t : ℂ) • (Hc + u)) * cR θ η s ℓ) * cW θ η s ℓ)
      rw [hP, ← hWq, ← hg]
      exact i1
  · -- the bound
    rw [netC_castSucc, netC_castSucc, hP, ← hWq, ← hg, hg0]
    exact htot

/-- The claim for every `k`, by reverse induction. -/
private theorem farBoundC_all (hp : 1 ≤ p) {σc : ℂ → ℂ} {R κg : ℝ} (hκg : 0 < κg)
    (hfar : ∀ z : ℂ, R ≤ z.re → |z.im| ≤ z.re / 2 →
      AnalyticAt ℂ σc z ∧ AnalyticAt ℂ σc (-z) ∧
        ‖σc z - z‖ ≤ Real.exp (-(κg * z.re ^ p)) ∧ ‖σc (-z)‖ ≤ Real.exp (-(κg * z.re ^ p)))
    {C : Fin (L + 1) → Set (d → ℝ)} {A : ∀ ℓ, Finset (hid ℓ)}
    {θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut}
    (hθ : GoodForConesGated C A θ) (η : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (k : Fin (L + 1)) : FarBoundC σc p C A θ η k := by
  induction k using Fin.reverseInduction with
  | last => exact farBoundC_last σc C A θ η
  | cast ℓ ih => exact farBoundC_castSucc hp hκg hfar hθ η ℓ ih

/-! ### The four maps -/

/-- The derivative of `θ' ↦ 𝓑_{>k}(h)` along `η'` is the derivative of `r ↦ 𝓑_{>k}(h)` at the
weights `θ' + r η'`. -/
private theorem hasDerivAt_params_suffix_ffh (A' : Arch T d L) (hχ : A'.χ = id)
    (hf : ∀ ℓ, Differentiable ℝ (A'.f ℓ)) (θ' η' : Params A' dIn dOut) (k : Fin (L + 1))
    (h : Matrix T d ℝ) :
    HasDerivAt (fun r : ℝ => suffix A' 0 (θ' + r • η') k h)
      (fderiv ℝ (fun θ'' : Params A' dIn dOut => suffix A' 0 θ'' k h) θ' η') 0 := by
  have hP := differentiable_params_suffix A' (dIn := dIn) (dOut := dOut) hχ hf k h
  have hl : HasDerivAt (fun r : ℝ => θ' + r • η') η' 0 := by
    have h1 := ((hasDerivAt_id (0 : ℝ)).smul_const η').const_add θ'
    rw [one_smul] at h1
    exact h1
  have hc := (hP θ').hasFDerivAt.comp_hasDerivAt_of_eq 0 hl (by simp)
  exact hc

/-- Helper: the cast of `t (H + U)`. -/
private theorem map_smul_add_ofReal_ffh {m n : Type*} (t : ℝ) (H U : Matrix m n ℝ) :
    (t : ℂ) • (H.map (fun x : ℝ => (x : ℂ)) + U.map (fun x : ℝ => (x : ℂ)))
      = (t • (H + U)).map (fun x : ℝ => (x : ℂ)) := by
  ext i j
  simp [mul_add]

/-- **Lemma D.11, with the holomorphic extension.** Let `θ` be good for the cones, and let all
rows of `H` lie in `C_k`. There are `ϱ, κ > 0` and `t₀` such that for `t ≥ t₀` the maps
`u ↦ 𝓑_{>k}(t (H + u))` and `u ↦ 𝐃_θ 𝓑_{>k}(t (H + u)) η`, and the same maps of the frozen network,
extend to holomorphic maps on the complex `u` with `|u_{τ j}| ≤ ϱ`, and on this polydisc the
network and the frozen network, and their derivatives in the weights along `η`, differ by at most
`e^{−κ t^p}`. -/
theorem exists_far_frozen_holomorphic (hg : GateFar σ σ' p) (hgC : GateFarC σ p)
    {C : Fin (L + 1) → Set (d → ℝ)} {A : ∀ ℓ, Finset (hid ℓ)}
    {θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut}
    (hθ : GoodForConesGated C A θ) (k : Fin (L + 1)) (H : Matrix T d ℝ) (hH : ∀ t, H t ∈ C k)
    (η : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) :
    ∃ ϱ : ℝ, 0 < ϱ ∧ ∃ κ : ℝ, 0 < κ ∧ ∃ t₀ : ℝ, ∀ t : ℝ, t₀ ≤ t →
      ∃ G G₀ G' G₀' : Matrix T d ℂ → Matrix T dOut ℂ,
        AnalyticOnNhd ℂ G {u | ∀ τ j, ‖u τ j‖ ≤ ϱ} ∧
        AnalyticOnNhd ℂ G₀ {u | ∀ τ j, ‖u τ j‖ ≤ ϱ} ∧
        AnalyticOnNhd ℂ G' {u | ∀ τ j, ‖u τ j‖ ≤ ϱ} ∧
        AnalyticOnNhd ℂ G₀' {u | ∀ τ j, ‖u τ j‖ ≤ ϱ} ∧
        (∀ U : Matrix T d ℝ, (∀ τ j, |U τ j| ≤ ϱ) →
          G (U.map fun a : ℝ => (a : ℂ))
              = (suffix (Arch.gated σ id hid) 0 θ k (t • (H + U))).map (fun a : ℝ => (a : ℂ)) ∧
          G₀ (U.map fun a : ℝ => (a : ℂ))
              = (suffix (Arch.frozen A) 0 (θ.toFrozen A) k (t • (H + U))).map
                  (fun a : ℝ => (a : ℂ)) ∧
          G' (U.map fun a : ℝ => (a : ℂ))
              = (fderiv ℝ (fun θ' : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut =>
                  suffix (Arch.gated σ id hid) 0 θ' k (t • (H + U))) θ η).map
                  (fun a : ℝ => (a : ℂ)) ∧
          G₀' (U.map fun a : ℝ => (a : ℂ))
              = (fderiv ℝ (fun θ' : Params (Arch.frozen (T := T) (d := d) A) dIn dOut =>
                  suffix (Arch.frozen A) 0 θ' k (t • (H + U))) (θ.toFrozen A)
                  (η.toFrozen A)).map (fun a : ℝ => (a : ℂ))) ∧
        ∀ u : Matrix T d ℂ, (∀ τ j, ‖u τ j‖ ≤ ϱ) →
          ‖G u - G₀ u‖ ≤ Real.exp (-(κ * t ^ p)) ∧ ‖G' u - G₀' u‖ ≤ Real.exp (-(κ * t ^ p)) := by
  -- the complex gate of (31), and the claim of the induction at `k` for `H`
  obtain ⟨σc, hσc, R, κg, hκg, hfar⟩ := hgC
  have hp := hg.one_le
  obtain ⟨ϱ, hϱ, s₀, hs₀, κ, hκ, t₀, hB⟩ := farBoundC_all hp hκg hfar hθ η k H hH
  -- Cauchy's estimate costs the factor `1/s₀`, absorbed into `κ/2`
  obtain ⟨t₂, ht₂⟩ := absorb_ffh hp hκ (1 / s₀) 0
  refine ⟨ϱ, hϱ, κ / 2, half_pos hκ, max t₀ (max t₂ 0), fun t ht => ?_⟩
  have htt₀ : t₀ ≤ t := (le_max_left _ _).trans ht
  have htt₂ : t₂ ≤ t := (le_max_left _ _).trans ((le_max_right _ _).trans ht)
  have ht0 : 0 ≤ t := (le_max_right _ _).trans ((le_max_right _ _).trans ht)
  have hexp : Real.exp (-(κ * t ^ p)) ≤ Real.exp (-(κ / 2 * t ^ p)) :=
    Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_right (half_le_self hκ.le)
      (pow_nonneg ht0 p)))
  -- the polydisc is the closed ball of radius `ϱ`
  have hPD : ∀ u : Matrix T d ℂ, (∀ τ j, ‖u τ j‖ ≤ ϱ) → ‖u‖ ≤ ϱ := fun u hu =>
    (Matrix.norm_le_iff hϱ.le).2 hu
  have hs0 : ‖(0 : ℂ)‖ ≤ s₀ := by rw [norm_zero]; exact hs₀.le
  -- `u ↦ t (H + u)` is holomorphic
  have hι : ∀ u₀ : Matrix T d ℂ, AnalyticAt ℂ
      (fun u : Matrix T d ℂ => (t : ℂ) • (H.map (fun x : ℝ => (x : ℂ)) + u)) u₀ := fun u₀ =>
    analyticAt_const.fun_smul (analyticAt_const.fun_add analyticAt_id)
  have hι0 : ∀ u₀ : Matrix T d ℂ, AnalyticAt ℂ
      (fun u : Matrix T d ℂ => ((0 : ℂ), (t : ℂ) • (H.map (fun x : ℝ => (x : ℂ)) + u))) u₀ :=
    fun u₀ => analyticAt_const.prod (hι u₀)
  -- the four maps: the two complex networks at `s = 0`, and their derivatives in `s` at `0`
  refine ⟨fun u => netC (fun _ _ => σc) θ η 0 k ((t : ℂ) • (H.map (fun x : ℝ => (x : ℂ)) + u)),
    fun u => netC (fun ℓ => aFC (A ℓ)) θ η 0 k ((t : ℂ) • (H.map (fun x : ℝ => (x : ℂ)) + u)),
    fun u => fderiv ℂ (fun q : ℂ × Matrix T d ℂ => netC (fun _ _ => σc) θ η q.1 k q.2)
      (0, (t : ℂ) • (H.map (fun x : ℝ => (x : ℂ)) + u)) (1, 0),
    fun u => fderiv ℂ (fun q : ℂ × Matrix T d ℂ => netC (fun ℓ => aFC (A ℓ)) θ η q.1 k q.2)
      (0, (t : ℂ) • (H.map (fun x : ℝ => (x : ℂ)) + u)) (1, 0), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `G` is holomorphic on the polydisc
    intro u hu
    exact AnalyticAt.comp (f := fun u : Matrix T d ℂ =>
      ((0 : ℂ), (t : ℂ) • (H.map (fun x : ℝ => (x : ℂ)) + u)))
      (hB t htt₀ 0 hs0 u (hPD u hu)).1 (hι0 u)
  · -- `G₀` is holomorphic (everywhere)
    intro u _
    exact AnalyticAt.comp (f := fun u : Matrix T d ℂ =>
      ((0 : ℂ), (t : ℂ) • (H.map (fun x : ℝ => (x : ℂ)) + u)))
      (analyticAt_netC_frozen A θ η k _) (hι0 u)
  · -- `G'` is holomorphic on the polydisc
    intro u hu
    exact analyticAt_partialDeriv_ffh
      (ι := fun u : Matrix T d ℂ => (t : ℂ) • (H.map (fun x : ℝ => (x : ℂ)) + u))
      (hB t htt₀ 0 hs0 u (hPD u hu)).1 (hι u)
  · -- `G₀'` is holomorphic (everywhere)
    intro u _
    exact analyticAt_partialDeriv_ffh
      (ι := fun u : Matrix T d ℂ => (t : ℂ) • (H.map (fun x : ℝ => (x : ℂ)) + u))
      (analyticAt_netC_frozen A θ η k _) (hι u)
  · -- at real `U`: the real networks and their derivatives in the weights
    intro U hU
    have hUc : ‖U.map (fun x : ℝ => (x : ℂ))‖ ≤ ϱ := (Matrix.norm_le_iff hϱ.le).2 fun τ j => by
      rw [Matrix.map_apply, Complex.norm_real, Real.norm_eq_abs]
      exact hU τ j
    have hd := (hB t htt₀ 0 hs0 _ hUc).1.differentiableAt
    have hd₀ := (analyticAt_netC_frozen A θ η k
      ((0 : ℂ), (t : ℂ) • (H.map (fun x : ℝ => (x : ℂ)) + U.map (fun x : ℝ => (x : ℂ)))))
      |>.differentiableAt
    dsimp only
    rw [map_smul_add_ofReal_ffh] at hd hd₀ ⊢
    refine ⟨?_, ?_, ?_, ?_⟩
    · have e := netC_gated_ofReal hσc θ η 0 k (t • (H + U))
      rw [Complex.ofReal_zero, zero_smul, add_zero] at e
      exact e
    · have e := netC_frozen_ofReal A θ η 0 k (t • (H + U))
      rw [Complex.ofReal_zero, zero_smul, add_zero] at e
      exact e
    · exact fderiv_ofReal_line_ffh hd (hasDerivAt_params_suffix_ffh _ rfl
        (fun ℓ => differentiable_f_gated (fun z => (hg.hasDerivAt z).differentiableAt) ℓ) θ η k
        (t • (H + U))) fun r => netC_gated_ofReal hσc θ η r k (t • (H + U))
    · exact fderiv_ofReal_line_ffh hd₀ (hasDerivAt_params_suffix_ffh _ rfl
        (fun ℓ => differentiableOn_univ.1 (analyticOnNhd_f_frozen A ℓ).differentiableOn)
        (θ.toFrozen A) (η.toFrozen A) k (t • (H + U)))
        fun r => netC_frozen_ofReal A θ η r k (t • (H + U))
  · -- the two bounds on the polydisc
    intro u hu
    have hu' := hPD u hu
    refine ⟨((hB t htt₀ 0 hs0 u hu').2).trans hexp, ?_⟩
    -- Cauchy's estimate in `s` on the disc `|s| ≤ s₀`
    have hdiff : ∀ s : ℂ, ‖s‖ ≤ s₀ →
        DifferentiableAt ℂ (fun q : ℂ × Matrix T d ℂ => netC (fun _ _ => σc) θ η q.1 k q.2)
          (s, (t : ℂ) • (H.map (fun x : ℝ => (x : ℂ)) + u)) ∧
        DifferentiableAt ℂ
          (fun q : ℂ × Matrix T d ℂ => netC (fun ℓ => aFC (A ℓ)) θ η q.1 k q.2)
          (s, (t : ℂ) • (H.map (fun x : ℝ => (x : ℂ)) + u)) := fun s hs =>
      ⟨(hB t htt₀ s hs u hu').1.differentiableAt,
        (analyticAt_netC_frozen A θ η k _).differentiableAt⟩
    have hC := norm_deriv_le_ffh (D := fun s : ℂ =>
        netC (fun _ _ => σc) θ η s k ((t : ℂ) • (H.map (fun x : ℝ => (x : ℂ)) + u))
          - netC (fun ℓ => aFC (A ℓ)) θ η s k ((t : ℂ) • (H.map (fun x : ℝ => (x : ℂ)) + u)))
      hs₀ (fun s hs => ((hasDerivAt_partial_ffh (hdiff s hs).1).fun_sub
        (hasDerivAt_partial_ffh (hdiff s hs).2)).differentiableAt)
      (fun s hs => (hB t htt₀ s hs u hu').2)
    rw [((hasDerivAt_partial_ffh (hdiff 0 hs0).1).fun_sub
      (hasDerivAt_partial_ffh (hdiff 0 hs0).2)).deriv] at hC
    refine hC.trans ?_
    have h2 := ht₂ t htt₂
    rw [pow_zero, mul_one] at h2
    calc Real.exp (-(κ * t ^ p)) / s₀ = 1 / s₀ * Real.exp (-(κ * t ^ p)) := by ring
      _ ≤ _ := h2

end Skips
