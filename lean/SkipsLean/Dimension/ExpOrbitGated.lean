import SkipsLean.Dimension.ExpOrbit
import SkipsLean.Dimension.RescaleAction

/-!
# Gated blocks: the changes of basis and the rescalings near the identity, as one map

Paper (dimension paper): Appendix B, proof of Proposition 4.6: "The changes of basis of
Proposition 3.2, the rescalings and the changes of basis inside the heads form a Lie group of
dimension `k`, which acts smoothly. It acts locally freely at `θ`, so the map that sends an element
of the group to the image of `θ` under it is an immersion near the identity".

For a network of gated blocks the group is that of the changes of basis and of the rescalings of
the values of the hidden units. In the chart `(m, α) ↦ (exp m_ℓ, e^{α_{ℓ,i}})` at the identity, the
map that sends an element of the group to the image of `θ` is
`cobExpRescale θ (m, α) = (θ.rescale (e^α)).cob (exp m) (exp m)`: the value column of hidden unit
`i` of block `ℓ` is divided by `e^{α_{ℓ,i}}`, its write row is multiplied by `e^{α_{ℓ,i}}`, and
then the change of basis `exp m_ℓ` is made at the hidden state `h_ℓ`.

Stated here: the map passes through `θ` at `0`, and it is strictly differentiable at `0` with the
derivative `(m, α) ↦ cobDir θ m + rescaleDir θ α` (`Dimension/UpperBound.lean`,
`Dimension/Rescaling.lean`), for any gate `σ` and any map `χ`. Used for local identifiability of
networks of gated blocks, with and without skip connections
(`Dimension/LocalIdentifiabilityGated.lean`, `Residual/LocalIdentifiabilityGated.lean`).
-/

namespace Skips

open Matrix Filter Topology
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {σ : ℝ → ℝ} {χ : Matrix T d ℝ → Matrix T d ℝ} {hid : Fin L → Type}
  [∀ ℓ, Fintype (hid ℓ)]

/-- The parameters `(θ.rescale (e^α)).cob (exp m) (exp m)` of a gated network: the rescaling of
the value of hidden unit `i` of block `ℓ` by `e^{α ℓ i}`, then the change of basis `exp m_ℓ` at the
hidden state `h_ℓ`. -/
noncomputable def cobExpRescale (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut)
    (p : (Fin (L + 1) → Matrix d d ℝ) × (∀ ℓ, hid ℓ → ℝ)) :
    Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut :=
  cobExp (θ.rescale fun ℓ i => Real.exp (p.2 ℓ i)) p.1

/-- Helper: matrix multiplication as a continuous bilinear map. -/
private noncomputable def mulB_eog (m n p : Type*) [Fintype m] [Fintype n] [Fintype p] :
    Matrix m n ℝ →L[ℝ] Matrix n p ℝ →L[ℝ] Matrix m p ℝ :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap :
      (Matrix n p ℝ →ₗ[ℝ] Matrix m p ℝ) ≃ₗ[ℝ] (Matrix n p ℝ →L[ℝ] Matrix m p ℝ)).toLinearMap ∘ₗ
      LinearMap.mk₂ ℝ (fun a b => a * b) Matrix.add_mul (fun c a b => Matrix.smul_mul c a b)
        Matrix.mul_add (fun c a b => Matrix.mul_smul a c b))

/-- Helper: the product rule for matrix-valued maps, strict form, with the value of the
derivative, `(f g)' v = f' v g + f g' v`. -/
private theorem hasStrictFDerivAt_mul_eog {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m n p : Type*} [Fintype m] [Fintype n] [Fintype p] {f : E → Matrix m n ℝ}
    {g : E → Matrix n p ℝ} {f' : E →L[ℝ] Matrix m n ℝ} {g' : E →L[ℝ] Matrix n p ℝ} {y : E}
    (hf : HasStrictFDerivAt f f' y) (hg : HasStrictFDerivAt g g' y) :
    ∃ h' : E →L[ℝ] Matrix m p ℝ, HasStrictFDerivAt (fun z => f z * g z) h' y ∧
      ∀ v, h' v = f' v * g y + f y * g' v := by
  -- the derivative of the bilinear map `(a, b) ↦ a b` along `(f, g)`
  have h := (mulB_eog m n p).hasStrictFDerivAt_of_bilinear hf hg
  refine ⟨_, h, fun v => ?_⟩
  show f y * g' v + f' v * g y = _
  exact add_comm _ _

/-- Helper: `z ↦ e^{π z} c` for a linear form `π`, with derivative `v ↦ π v c` at `0`. -/
private theorem hasStrictFDerivAt_exp_mul_eog {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (π : E →L[ℝ] ℝ) (c : ℝ) :
    ∃ D : E →L[ℝ] ℝ, HasStrictFDerivAt (fun z => Real.exp (π z) * c) D 0 ∧
      ∀ v, D v = π v * c := by
  have he := (Real.hasStrictDerivAt_exp (π 0)).comp_hasStrictFDerivAt (0 : E) π.hasStrictFDerivAt
  have hc := he.mul_const c
  refine ⟨_, hc, fun v => ?_⟩
  show c * (Real.exp (π 0) * π v) = π v * c
  rw [map_zero, Real.exp_zero]
  ring

/-- Helper: `z ↦ (e^{π z})⁻¹ c` for a linear form `π`, with derivative `v ↦ -π v c` at `0`. -/
private theorem hasStrictFDerivAt_exp_inv_mul_eog {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (π : E →L[ℝ] ℝ) (c : ℝ) :
    ∃ D : E →L[ℝ] ℝ, HasStrictFDerivAt (fun z => (Real.exp (π z))⁻¹ * c) D 0 ∧
      ∀ v, D v = -π v * c := by
  have he := (Real.hasStrictDerivAt_exp (π 0)).comp_hasStrictFDerivAt (0 : E) π.hasStrictFDerivAt
  have hi := (hasStrictDerivAt_inv (Real.exp_pos (π 0)).ne').comp_hasStrictFDerivAt (0 : E) he
  have hc := hi.mul_const c
  refine ⟨_, hc, fun v => ?_⟩
  show c * (-(Real.exp (π 0) ^ 2)⁻¹ * (Real.exp (π 0) * π v)) = -π v * c
  rw [map_zero, Real.exp_zero]
  ring

/-- Helper: `p ↦ exp (m_ℓ)`, with derivative `v ↦ v.1 ℓ` at `0`. -/
private theorem hasStrictFDerivAt_exp_fst_eog {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (ℓ : Fin (L + 1)) :
    ∃ D : (Fin (L + 1) → Matrix d d ℝ) × F →L[ℝ] Matrix d d ℝ,
      HasStrictFDerivAt (fun p : (Fin (L + 1) → Matrix d d ℝ) × F => NormedSpace.exp (p.1 ℓ))
        D 0 ∧ ∀ v, D v = v.1 ℓ := by
  let π := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (L + 1) => Matrix d d ℝ) ℓ).comp
    (ContinuousLinearMap.fst ℝ (Fin (L + 1) → Matrix d d ℝ) F)
  have hg : HasStrictFDerivAt (fun Y : Matrix d d ℝ => NormedSpace.exp Y)
      (ContinuousLinearMap.id ℝ (Matrix d d ℝ)) (π 0) := by
    rw [map_zero]
    exact hasStrictFDerivAt_matrix_exp_zero
  have hc := hg.comp (0 : (Fin (L + 1) → Matrix d d ℝ) × F) π.hasStrictFDerivAt
  exact ⟨_, hc, fun v => rfl⟩

/-- Helper: `p ↦ exp (-m_ℓ)`, with derivative `v ↦ -v.1 ℓ` at `0`. -/
private theorem hasStrictFDerivAt_exp_neg_fst_eog {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (ℓ : Fin (L + 1)) :
    ∃ D : (Fin (L + 1) → Matrix d d ℝ) × F →L[ℝ] Matrix d d ℝ,
      HasStrictFDerivAt (fun p : (Fin (L + 1) → Matrix d d ℝ) × F => NormedSpace.exp (-p.1 ℓ))
        D 0 ∧ ∀ v, D v = -v.1 ℓ := by
  let π := -(ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (L + 1) => Matrix d d ℝ) ℓ).comp
    (ContinuousLinearMap.fst ℝ (Fin (L + 1) → Matrix d d ℝ) F)
  have hg : HasStrictFDerivAt (fun Y : Matrix d d ℝ => NormedSpace.exp Y)
      (ContinuousLinearMap.id ℝ (Matrix d d ℝ)) (π 0) := by
    rw [map_zero]
    exact hasStrictFDerivAt_matrix_exp_zero
  have hc := hg.comp (0 : (Fin (L + 1) → Matrix d d ℝ) × F) π.hasStrictFDerivAt
  exact ⟨_, hc, fun v => rfl⟩

variable (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut)

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the rescaling by `1` is the identity. -/
private theorem rescale_one_eog : θ.rescale (fun _ _ => 1) = θ := by
  refine Params.ext' rfl (fun ℓ => ?_) (fun ℓ => ?_) rfl
  · ext k j
    rcases j with i | i
    · rfl
    · show (1 : ℝ)⁻¹ * θ.read ℓ k (Sum.inr i) = θ.read ℓ k (Sum.inr i)
      rw [inv_one, one_mul]
  · ext i k
    show (1 : ℝ) * θ.write ℓ i k = θ.write ℓ i k
    rw [one_mul]


/-- At `(m, α) = 0` the map gives `θ`. -/
theorem cobExpRescale_zero : cobExpRescale θ 0 = θ := by
  -- `e^0 = 1` on every hidden unit, and `exp 0 = 1` on every hidden state
  simp only [cobExpRescale, Prod.snd_zero, Prod.fst_zero, Pi.zero_apply, Real.exp_zero,
    rescale_one_eog]
  exact cobExp_zero θ

omit [Fintype T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the read of block `ℓ` after the rescaling `e^α`, as a map of `p = (m, α)`, with
derivative `v ↦ (rescaleDir θ v.2).read ℓ` at `0`, entry by entry. -/
private theorem hasStrictFDerivAt_rescale_read_eog (ℓ : Fin L) :
    ∃ D : (Fin (L + 1) → Matrix d d ℝ) × (∀ ℓ, hid ℓ → ℝ) →L[ℝ] Matrix d (hid ℓ ⊕ hid ℓ) ℝ,
      HasStrictFDerivAt (fun p : (Fin (L + 1) → Matrix d d ℝ) × (∀ ℓ, hid ℓ → ℝ) =>
        (θ.rescale fun ℓ i => Real.exp (p.2 ℓ i)).read ℓ) D 0 ∧
      ∀ v, D v = (rescaleDir θ v.2).read ℓ := by
  -- the gate columns are constant, the value column `i` is `(e^{α ℓ i})⁻¹ W_read k i`
  have h : ∀ (k : d) (j : hid ℓ ⊕ hid ℓ),
      ∃ D : (Fin (L + 1) → Matrix d d ℝ) × (∀ ℓ, hid ℓ → ℝ) →L[ℝ] ℝ,
        HasStrictFDerivAt (fun p : (Fin (L + 1) → Matrix d d ℝ) × (∀ ℓ, hid ℓ → ℝ) =>
          (θ.rescale fun ℓ i => Real.exp (p.2 ℓ i)).read ℓ k j) D 0 ∧
        ∀ v, D v = (rescaleDir θ v.2).read ℓ k j := by
    intro k j
    rcases j with i | i
    · exact ⟨0, hasStrictFDerivAt_const (θ.read ℓ k (Sum.inl i)) 0, fun v => rfl⟩
    · obtain ⟨D, hD, hDv⟩ := hasStrictFDerivAt_exp_inv_mul_eog
        ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : hid ℓ => ℝ) i).comp
          ((ContinuousLinearMap.proj (R := ℝ) (φ := fun ℓ => hid ℓ → ℝ) ℓ).comp
            (ContinuousLinearMap.snd ℝ (Fin (L + 1) → Matrix d d ℝ) (∀ ℓ, hid ℓ → ℝ))))
        (θ.read ℓ k (Sum.inr i))
      exact ⟨D, hD, hDv⟩
  choose D hD hDv using h
  exact ⟨ContinuousLinearMap.pi fun k => ContinuousLinearMap.pi fun j => D k j,
    hasStrictFDerivAt_pi.2 fun k => hasStrictFDerivAt_pi.2 fun j => hD k j,
    fun v => Matrix.ext fun k j => hDv k j v⟩

omit [Fintype T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the write of block `ℓ` after the rescaling `e^α`, as a map of `p = (m, α)`, with
derivative `v ↦ (rescaleDir θ v.2).write ℓ` at `0`, entry by entry. -/
private theorem hasStrictFDerivAt_rescale_write_eog (ℓ : Fin L) :
    ∃ D : (Fin (L + 1) → Matrix d d ℝ) × (∀ ℓ, hid ℓ → ℝ) →L[ℝ] Matrix (hid ℓ) d ℝ,
      HasStrictFDerivAt (fun p : (Fin (L + 1) → Matrix d d ℝ) × (∀ ℓ, hid ℓ → ℝ) =>
        (θ.rescale fun ℓ i => Real.exp (p.2 ℓ i)).write ℓ) D 0 ∧
      ∀ v, D v = (rescaleDir θ v.2).write ℓ := by
  -- row `i` is `e^{α ℓ i} W_write i`
  have h : ∀ (i : hid ℓ) (k : d),
      ∃ D : (Fin (L + 1) → Matrix d d ℝ) × (∀ ℓ, hid ℓ → ℝ) →L[ℝ] ℝ,
        HasStrictFDerivAt (fun p : (Fin (L + 1) → Matrix d d ℝ) × (∀ ℓ, hid ℓ → ℝ) =>
          (θ.rescale fun ℓ i => Real.exp (p.2 ℓ i)).write ℓ i k) D 0 ∧
        ∀ v, D v = (rescaleDir θ v.2).write ℓ i k := by
    intro i k
    obtain ⟨D, hD, hDv⟩ := hasStrictFDerivAt_exp_mul_eog
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : hid ℓ => ℝ) i).comp
        ((ContinuousLinearMap.proj (R := ℝ) (φ := fun ℓ => hid ℓ → ℝ) ℓ).comp
          (ContinuousLinearMap.snd ℝ (Fin (L + 1) → Matrix d d ℝ) (∀ ℓ, hid ℓ → ℝ))))
      (θ.write ℓ i k)
    exact ⟨D, hD, hDv⟩
  choose D hD hDv using h
  exact ⟨ContinuousLinearMap.pi fun i => ContinuousLinearMap.pi fun k => D i k,
    hasStrictFDerivAt_pi.2 fun i => hasStrictFDerivAt_pi.2 fun k => hD i k,
    fun v => Matrix.ext fun i k => hDv i k v⟩

omit [Fintype T] [Fintype dOut] in
/-- Helper: the embedding `E exp (m_0)`, with derivative `v ↦ E v.1 0` at `0`. -/
private theorem hasStrictFDerivAt_E_eog :
    ∃ D : (Fin (L + 1) → Matrix d d ℝ) × (∀ ℓ, hid ℓ → ℝ) →L[ℝ] Matrix dIn d ℝ,
      HasStrictFDerivAt (fun p : (Fin (L + 1) → Matrix d d ℝ) × (∀ ℓ, hid ℓ → ℝ) =>
        θ.E * NormedSpace.exp (p.1 0)) D 0 ∧
      ∀ v, D v = (cobDir θ v.1 + rescaleDir θ v.2).E := by
  obtain ⟨g', hg, hgv⟩ := hasStrictFDerivAt_exp_fst_eog (d := d) (F := ∀ ℓ, hid ℓ → ℝ) 0
  obtain ⟨D, hD, hDv⟩ := hasStrictFDerivAt_mul_eog
    (hasStrictFDerivAt_const θ.E (0 : (Fin (L + 1) → Matrix d d ℝ) × (∀ ℓ, hid ℓ → ℝ))) hg
  refine ⟨D, hD, fun v => ?_⟩
  -- `0 exp 0 + E v.1 0`, against `E v.1 0 + 0`
  refine (hDv v).trans ?_
  erw [hgv]
  show (0 : Matrix dIn d ℝ) * _ + θ.E * v.1 0 = θ.E * v.1 0 + 0
  rw [Matrix.zero_mul, zero_add, add_zero]

omit [Fintype T] [Fintype dIn] [Fintype dOut] in
/-- Helper: the read of block `ℓ`, `exp (-m_{ℓ-1}) R_ℓ(α)`, with derivative
`v ↦ -v.1 (ℓ-1) W_read + (rescaleDir θ v.2).read ℓ` at `0` (product rule). -/
private theorem hasStrictFDerivAt_read_eog (ℓ : Fin L) :
    ∃ D : (Fin (L + 1) → Matrix d d ℝ) × (∀ ℓ, hid ℓ → ℝ) →L[ℝ] Matrix d (hid ℓ ⊕ hid ℓ) ℝ,
      HasStrictFDerivAt (fun p : (Fin (L + 1) → Matrix d d ℝ) × (∀ ℓ, hid ℓ → ℝ) =>
        NormedSpace.exp (-p.1 ℓ.castSucc) * (θ.rescale fun ℓ i => Real.exp (p.2 ℓ i)).read ℓ)
        D 0 ∧
      ∀ v, D v = (cobDir θ v.1 + rescaleDir θ v.2).read ℓ := by
  obtain ⟨f', hf, hfv⟩ :=
    hasStrictFDerivAt_exp_neg_fst_eog (d := d) (F := ∀ ℓ, hid ℓ → ℝ) ℓ.castSucc
  obtain ⟨g', hg, hgv⟩ := hasStrictFDerivAt_rescale_read_eog θ ℓ
  obtain ⟨D, hD, hDv⟩ := hasStrictFDerivAt_mul_eog hf hg
  refine ⟨D, hD, fun v => ?_⟩
  -- at `0` the factors are `exp 0 = 1` and `θ.read ℓ`
  refine (hDv v).trans ?_
  erw [hfv, hgv]
  simp only [Prod.fst_zero, Prod.snd_zero, Pi.zero_apply, Real.exp_zero, neg_zero,
    NormedSpace.exp_zero, rescale_one_eog, Matrix.one_mul, Params.add_read, Matrix.neg_mul]
  rfl

omit [Fintype T] [Fintype dIn] [Fintype dOut] in
/-- Helper: the write of block `ℓ`, `W_ℓ(α) exp (m_ℓ)`, with derivative
`v ↦ (rescaleDir θ v.2).write ℓ + W_write v.1 ℓ` at `0` (product rule). -/
private theorem hasStrictFDerivAt_write_eog (ℓ : Fin L) :
    ∃ D : (Fin (L + 1) → Matrix d d ℝ) × (∀ ℓ, hid ℓ → ℝ) →L[ℝ] Matrix (hid ℓ) d ℝ,
      HasStrictFDerivAt (fun p : (Fin (L + 1) → Matrix d d ℝ) × (∀ ℓ, hid ℓ → ℝ) =>
        (θ.rescale fun ℓ i => Real.exp (p.2 ℓ i)).write ℓ * NormedSpace.exp (p.1 ℓ.succ)) D 0 ∧
      ∀ v, D v = (cobDir θ v.1 + rescaleDir θ v.2).write ℓ := by
  obtain ⟨f', hf, hfv⟩ := hasStrictFDerivAt_rescale_write_eog θ ℓ
  obtain ⟨g', hg, hgv⟩ := hasStrictFDerivAt_exp_fst_eog (d := d) (F := ∀ ℓ, hid ℓ → ℝ) ℓ.succ
  obtain ⟨D, hD, hDv⟩ := hasStrictFDerivAt_mul_eog hf hg
  refine ⟨D, hD, fun v => ?_⟩
  -- at `0` the factors are `θ.write ℓ` and `exp 0 = 1`
  refine (hDv v).trans ?_
  erw [hfv, hgv]
  simp only [Prod.fst_zero, Prod.snd_zero, Pi.zero_apply, Real.exp_zero,
    NormedSpace.exp_zero, rescale_one_eog, Matrix.mul_one, Params.add_write]
  exact add_comm _ _

omit [Fintype T] [Fintype dIn] in
/-- Helper: the readout `exp (-m_L) D`, with derivative `v ↦ -v.1 L D` at `0`. -/
private theorem hasStrictFDerivAt_D_eog :
    ∃ D : (Fin (L + 1) → Matrix d d ℝ) × (∀ ℓ, hid ℓ → ℝ) →L[ℝ] Matrix d dOut ℝ,
      HasStrictFDerivAt (fun p : (Fin (L + 1) → Matrix d d ℝ) × (∀ ℓ, hid ℓ → ℝ) =>
        NormedSpace.exp (-p.1 (Fin.last L)) * θ.D) D 0 ∧
      ∀ v, D v = (cobDir θ v.1 + rescaleDir θ v.2).D := by
  obtain ⟨f', hf, hfv⟩ :=
    hasStrictFDerivAt_exp_neg_fst_eog (d := d) (F := ∀ ℓ, hid ℓ → ℝ) (Fin.last L)
  obtain ⟨D, hD, hDv⟩ := hasStrictFDerivAt_mul_eog hf
    (hasStrictFDerivAt_const θ.D (0 : (Fin (L + 1) → Matrix d d ℝ) × (∀ ℓ, hid ℓ → ℝ)))
  refine ⟨D, hD, fun v => ?_⟩
  -- `-v.1 L D + exp 0 0`, against `-(v.1 L D) + 0`
  refine (hDv v).trans ?_
  erw [hfv]
  show -v.1 (Fin.last L) * θ.D + _ * (0 : Matrix d dOut ℝ) = -(v.1 (Fin.last L) * θ.D) + 0
  rw [Matrix.mul_zero, Matrix.neg_mul]

/-- The map `(m, α) ↦ (θ.rescale (e^α)).cob (exp m) (exp m)` is strictly differentiable at `0`,
with the derivative `(m, α) ↦ cobDir θ m + rescaleDir θ α`. -/
theorem hasStrictFDerivAt_cobExpRescale :
    ∃ Φ' : ((Fin (L + 1) → Matrix d d ℝ) × (∀ ℓ, hid ℓ → ℝ)) →L[ℝ]
        Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut,
      HasStrictFDerivAt (cobExpRescale θ) Φ' 0 ∧ ∀ p, Φ' p = cobDir θ p.1 + rescaleDir θ p.2 := by
  -- the four components: `E exp(m_0)`, `exp(-m_{ℓ-1}) R_ℓ(α)`, `W_ℓ(α) exp(m_ℓ)`, `exp(-m_L) D`
  obtain ⟨DE, hE, hEv⟩ := hasStrictFDerivAt_E_eog θ
  choose DR hR hRv using hasStrictFDerivAt_read_eog θ
  choose DW hW hWv using hasStrictFDerivAt_write_eog θ
  obtain ⟨DD, hD, hDv⟩ := hasStrictFDerivAt_D_eog θ
  -- the tuple of the components is strictly differentiable, hence so is the map into `Params`
  have key := hE.prodMk ((hasStrictFDerivAt_pi.2 hR).prodMk ((hasStrictFDerivAt_pi.2 hW).prodMk hD))
  let e := (Params.linearEquivProd (A := Arch.gated (T := T) (d := d) σ χ hid) (dIn := dIn)
    (dOut := dOut)).toContinuousLinearEquiv
  have hc := e.symm.hasStrictFDerivAt.comp
    (0 : (Fin (L + 1) → Matrix d d ℝ) × (∀ ℓ, hid ℓ → ℝ)) key
  exact ⟨_, hc, fun v => Params.ext' (hEv v) (fun ℓ => hRv ℓ v) (fun ℓ => hWv ℓ v) (hDv v)⟩

end Skips
