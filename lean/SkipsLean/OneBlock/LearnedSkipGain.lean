import SkipsLean.OneBlock.LearnedSkipSteps
import SkipsLean.Depth.StepTanhRMS

/-!
# One block under pre-RMSNorm: a full learned skip against the identity skip

Paper (skips paper): Theorem 4.6 (ii): "A learned skip raises it by exactly
`d_model (d_model + 1)/2` more than an identity skip." Proof of Theorem B.1 (iii), `ε > 0`,
Step 4: "The flat direction `η′ = η − η^rot` has the entries `E X_s`, `−X_s A` and `0` at `E`, `A`
and `D`, so Step 3 applies to it with `X_s` in place of `X` and `0` in place of `Y`, and
`D_θ g η′ = 0`. The change `n X_s` of the input moves the block as the entries `X_s W_read` at
`W_read` do […]. So, with `ψ` the entries of `η′` at the weights of the block plus these,
`∂_ψ B(n) = q(n) 𝐃B(n) n` (17) for every `n` in the image of `N_ε` […]. We show that `q = 0`,
hence `X_s = 0`." Step 5: "With `X_s = 0`, the direction `η′` moves only the weights of the block,
and by (17) `B(n)` has derivative zero along it on the whole ball. So `η′` lies in the space `K_B`
of such directions, which is the space found in Step 4 of part (ii), and every direction of `K_B`
is flat. Hence `K(θ)` is spanned by the directions `η^rot` and `K_B`, as for the residual network
with its single rotation […]. So `K(θ)` is larger than for the residual network by
`d_model (d_model − 1)/2` […] while the network has `d_model²` […] more parameters. In both
cases the functional dimension is larger by `d_model (d_model + 1)/2`."

Here, with `q(n) = n X_s nᵀ / d` and `B(n) = f(n W_read) W_write`:

* `NoSymmetricPart A ε θ U`: the conclusion of Step 4 as a condition on the weights `θ` of the
  block, "equation (17) at the inputs of `U` forces `X_s = 0`". Equation (17) is written with the
  derivative of `N_ε`: `𝐃B(n)(n X − q(n) n) + ∂_ψ B(n) = 0` at `n = N_ε(x E)`, where
  `n X − q(n) n = tangentRMS X n` (`fderiv_rmsNorm_mul`).
* Steps 3 and 5, once for all kinds of block: under this condition, with `E` and `D` of rank `d`
  and an invertible skip `A`, the network with the full learned skip has at `(θ, A)` exactly
  `d (d + 1)/2` more functional dimension than the residual network at the same `θ`
  (`funDimLearned_eq_funDim_residual_add_of_noSymmetricPart`, for a block that is continuously
  differentiable).
* The same for a block that is continuously differentiable on an open cone `V` of pre-activations
  (ReLU, ReLU², ReGLU blocks: the matrices with no hidden unit at its kink), where "flat" is taken
  at the inputs `x` with `x E W_read ∈ V`: there the directions of the block along which `B` has
  derivative zero at these inputs must be symmetries inside the block (the hypothesis `hK`; for
  these blocks they are the rescalings of the hidden units, by Lemma B.3). The statement also gives
  a batch of such inputs on which the Jacobian has the functional dimension as its rank, which is
  the paper's functional dimension for these blocks.

The condition `NoSymmetricPart` is proved kind by kind: by homogeneity for ReLU, ReLU² and ReGLU
blocks (`OneBlock/LearnedSkipRescale.lean`, `OneBlock/LearnedSkipReGLU.lean`), and on inputs of two
tokens for attention blocks (`OneBlock/LearnedSkipAttention.lean`).
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]

/-- **The conclusion of Step 4 of the proof of Theorem B.1 (iii), as a condition on `θ`:** if for
a symmetric `X` and entries `ψ_read`, `ψ_write` at the weights of the block equation (17) holds at
every input `x` of `U`, that is

  `𝐃f(n W_read)((n X − q(n) n) W_read + n ψ_read) W_write + f(n W_read) ψ_write = 0`

at `n = N_ε(x E)`, with `q(n) = n X nᵀ / d` row by row, then `X = 0`. -/
def NoSymmetricPart (A : Arch T d 1) (ε : ℝ) (θ : Params A dIn dOut) (U : Set (Matrix T dIn ℝ)) :
    Prop :=
  ∀ (X : Matrix d d ℝ) (ψr : Matrix d (A.r 0) ℝ) (ψw : Matrix (A.w 0) d ℝ), Xᵀ = X →
    (∀ x ∈ U,
      fderiv ℝ (A.f 0) (rmsNorm ε (x * θ.E) * θ.read 0)
          (tangentRMS X (rmsNorm ε (x * θ.E)) * θ.read 0 + rmsNorm ε (x * θ.E) * ψr)
          * θ.write 0
        + A.f 0 (rmsNorm ε (x * θ.E) * θ.read 0) * ψw = 0) →
    X = 0

/-! ### The space `K_U` of the directions of the block with derivative zero on `U` -/

omit [Nonempty T] [DecidableEq d] in
/-- Helper: the space `K_U`: the directions `ψ` with `ψ_E = 0`, `ψ_D = 0` along which the block
`n ↦ f(n W_read) W_write` has derivative zero at `n = N_ε(x E)` for every input `x` of `U`. -/
private noncomputable def blockFlat_lsn (A : Arch T d 1) (ε : ℝ) (θ : Params A dIn dOut)
    (U : Set (Matrix T dIn ℝ)) : Submodule ℝ (Params A dIn dOut) where
  carrier := {ψ | ψ.E = 0 ∧ ψ.D = 0 ∧ ∀ x ∈ U,
    fderiv ℝ (A.f 0) (rmsNorm ε (x * θ.E) * θ.read 0) (rmsNorm ε (x * θ.E) * ψ.read 0)
        * θ.write 0 + A.f 0 (rmsNorm ε (x * θ.E) * θ.read 0) * ψ.write 0 = 0}
  add_mem' := by
    rintro ψ ψ' ⟨hE, hD, h⟩ ⟨hE', hD', h'⟩
    refine ⟨by rw [Params.add_E, hE, hE', add_zero], by rw [Params.add_D, hD, hD', add_zero],
      fun x hx => ?_⟩
    rw [Params.add_read, Params.add_write, Matrix.mul_add, map_add, Matrix.add_mul,
      Matrix.mul_add, add_add_add_comm, h x hx, h' x hx, add_zero]
  zero_mem' := ⟨rfl, rfl, fun x _ => by
    simp only [Params.zero_read, Params.zero_write, Matrix.mul_zero, map_zero, Matrix.zero_mul,
      add_zero]⟩
  smul_mem' := by
    rintro c ψ ⟨hE, hD, h⟩
    refine ⟨by rw [Params.smul_E, hE, smul_zero], by rw [Params.smul_D, hD, smul_zero],
      fun x hx => ?_⟩
    rw [Params.smul_read, Params.smul_write, Matrix.mul_smul, map_smul, Matrix.smul_mul,
      Matrix.mul_smul, ← smul_add, h x hx, smul_zero]

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dOut] in
private theorem mem_blockFlat_lsn {A : Arch T d 1} {ε : ℝ} {θ ψ : Params A dIn dOut}
    {U : Set (Matrix T dIn ℝ)} :
    ψ ∈ blockFlat_lsn A ε θ U ↔ ψ.E = 0 ∧ ψ.D = 0 ∧ ∀ x ∈ U,
      fderiv ℝ (A.f 0) (rmsNorm ε (x * θ.E) * θ.read 0) (rmsNorm ε (x * θ.E) * ψ.read 0)
          * θ.write 0 + A.f 0 (rmsNorm ε (x * θ.E) * θ.read 0) * ψ.write 0 = 0 :=
  Iff.rfl

/-! ### Equation (14) for a sum and for an antisymmetric matrix -/

omit [Fintype T] [Nonempty T] [DecidableEq d] in
/-- Helper: `Z ↦ tangentRMS Z n` is additive. -/
private theorem tangentRMS_add_lsn (Z₁ Z₂ : Matrix d d ℝ) (n : Matrix T d ℝ) :
    tangentRMS (Z₁ + Z₂) n = tangentRMS Z₁ n + tangentRMS Z₂ n := by
  ext t j
  simp only [tangentRMS, Matrix.of_apply, Matrix.add_apply, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul, dotProduct, Matrix.mul_apply, mul_add, add_mul, Finset.sum_add_distrib]
  ring

omit [Fintype T] [Nonempty T] [DecidableEq d] in
/-- Helper: for an antisymmetric `Z`, `tangentRMS Z n = n Z` (row by row `⟨n_t Z, n_t⟩ = 0`). -/
private theorem tangentRMS_of_antisymm_lsn {Z : Matrix d d ℝ} (hZ : Zᵀ = -Z)
    (n : Matrix T d ℝ) : tangentRMS Z n = n * Z := by
  have hZ' : ∀ i j, Z j i = -Z i j := fun i j => by
    have h := congrFun (congrFun hZ i) j
    rwa [transpose_apply, Matrix.neg_apply] at h
  -- `q = ∑_j ∑_i n_i Z_ij n_j` equals `-q` (swap the sums), so `q = 0`
  have hq : ∀ t, (n * Z) t ⬝ᵥ n t = 0 := by
    intro t
    have h1 : (n * Z) t ⬝ᵥ n t = ∑ j, ∑ i, n t i * Z i j * n t j := by
      simp only [dotProduct, Matrix.mul_apply, Finset.sum_mul]
    have h2 : ∑ j, ∑ i, n t i * Z i j * n t j = -∑ j, ∑ i, n t i * Z i j * n t j := by
      calc ∑ j, ∑ i, n t i * Z i j * n t j = ∑ j, ∑ i, n t j * Z j i * n t i :=
            Finset.sum_comm
        _ = ∑ j, ∑ i, -(n t i * Z i j * n t j) :=
            Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by rw [hZ' i j]; ring
        _ = _ := by simp only [Finset.sum_neg_distrib]
    rw [h1]
    linarith
  unfold tangentRMS
  ext t j
  rw [Matrix.of_apply, hq t, zero_div, zero_smul, sub_zero]

/-! ### Step 4: the symmetric part of `X` vanishes -/

omit [Nonempty T] [DecidableEq d] [Fintype dOut] in
/-- Helper (Step 4 of the paper, from `NoSymmetricPart`): if the derivative of the block along the
direction of Steps 1 to 3 is `g(x) Y` on `U`, then `X` is antisymmetric and the entries
`η_read + X W_read`, `η_write − W_write Y` give derivative zero on `U`. -/
private theorem antisymm_and_mem_lsn {A : Arch T d 1} {ε : ℝ} (hε : 0 < ε)
    (θ : Params A dIn dOut) (U : Set (Matrix T dIn ℝ)) (hX : NoSymmetricPart A ε θ U)
    (X Y : Matrix d d ℝ) (ηr : Matrix d (A.r 0) ℝ) (ηw : Matrix (A.w 0) d ℝ)
    (h : ∀ x ∈ U,
        fderiv ℝ (A.f 0) (rmsNorm ε (x * θ.E) * θ.read 0)
            (fderiv ℝ (rmsNorm ε : Matrix T d ℝ → Matrix T d ℝ) (x * θ.E) (x * θ.E * X)
                * θ.read 0
              + rmsNorm ε (x * θ.E) * ηr) * θ.write 0
          + A.f 0 (rmsNorm ε (x * θ.E) * θ.read 0) * ηw
          = A.f 0 (rmsNorm ε (x * θ.E) * θ.read 0) * θ.write 0 * Y) :
    Xᵀ = -X ∧ ∀ x ∈ U,
      fderiv ℝ (A.f 0) (rmsNorm ε (x * θ.E) * θ.read 0)
          (rmsNorm ε (x * θ.E) * (ηr + X * θ.read 0)) * θ.write 0
        + A.f 0 (rmsNorm ε (x * θ.E) * θ.read 0) * (ηw - θ.write 0 * Y) = 0 := by
  -- `X = X_s + X_a`, symmetric plus antisymmetric
  set Xs : Matrix d d ℝ := (1 / 2 : ℝ) • (X + Xᵀ) with hXs_def
  set Xa : Matrix d d ℝ := X - Xs with hXa_def
  have hXs : Xsᵀ = Xs := by
    rw [hXs_def, Matrix.transpose_smul, Matrix.transpose_add, Matrix.transpose_transpose,
      add_comm]
  have hXa : Xaᵀ = -Xa := by
    rw [hXa_def, Matrix.transpose_sub, hXs]
    ext i j
    simp only [hXs_def, Matrix.sub_apply, Matrix.neg_apply, Matrix.smul_apply,
      Matrix.add_apply, Matrix.transpose_apply, smul_eq_mul]
    ring
  have hsplit : X = Xs + Xa := by rw [hXa_def, add_sub_cancel]
  -- the equation of Steps 1 to 3 with `tangentRMS X n = tangentRMS X_s n + n X_a`
  have key : ∀ x ∈ U,
      fderiv ℝ (A.f 0) (rmsNorm ε (x * θ.E) * θ.read 0)
          (tangentRMS Xs (rmsNorm ε (x * θ.E)) * θ.read 0
            + rmsNorm ε (x * θ.E) * (ηr + Xa * θ.read 0)) * θ.write 0
        + A.f 0 (rmsNorm ε (x * θ.E) * θ.read 0) * (ηw - θ.write 0 * Y) = 0 := by
    intro x hx
    have e1 : tangentRMS Xs (rmsNorm ε (x * θ.E)) * θ.read 0
          + rmsNorm ε (x * θ.E) * (ηr + Xa * θ.read 0)
        = fderiv ℝ (rmsNorm ε : Matrix T d ℝ → Matrix T d ℝ) (x * θ.E) (x * θ.E * X)
            * θ.read 0 + rmsNorm ε (x * θ.E) * ηr := by
      rw [fderiv_rmsNorm_mul hε X (x * θ.E), hsplit, tangentRMS_add_lsn,
        tangentRMS_of_antisymm_lsn hXa]
      simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]
      abel
    rw [e1, Matrix.mul_sub, ← add_sub_assoc, h x hx, Matrix.mul_assoc, sub_self]
  -- `NoSymmetricPart` gives `X_s = 0`
  have hXs0 : Xs = 0 := hX Xs _ _ hXs key
  have hXaX : Xa = X := by rw [hXa_def, hXs0, sub_zero]
  refine ⟨hXaX ▸ hXa, fun x hx => ?_⟩
  have h0 := key x hx
  have ht : tangentRMS (0 : Matrix d d ℝ) (rmsNorm ε (x * θ.E)) = 0 := by
    rw [tangentRMS_of_antisymm_lsn (by rw [Matrix.transpose_zero, neg_zero]), Matrix.mul_zero]
  rw [hXs0, ht, Matrix.zero_mul, zero_add, hXaX] at h0
  exact h0

/-! ### The directions of the rotations and of `K_U`, as linear maps -/

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (the private `skipDirLin_lsb` of `OneBlock/LearnedSkipBound.lean`): the direction of
the skips under the changes of basis `X`, `S_ℓ ↦ −X_{ℓ-1} S_ℓ + S_ℓ X_ℓ`, linear in `X`. -/
private noncomputable def skipDirLin_lsn {L : ℕ} (S : Fin L → Matrix d d ℝ) :
    (Fin (L + 1) → Matrix d d ℝ) →ₗ[ℝ] (Fin L → Matrix d d ℝ) where
  toFun X ℓ := -(X ℓ.castSucc * S ℓ) + S ℓ * X ℓ.succ
  map_add' X Y := by
    funext ℓ
    simp only [Pi.add_apply, Matrix.add_mul, Matrix.mul_add, neg_add]
    abel
  map_smul' c X := by
    funext ℓ
    simp only [Pi.smul_apply, Matrix.smul_mul, Matrix.mul_smul, smul_neg, smul_add,
      RingHom.id_apply]

omit [Fintype T] [Nonempty T] in
/-- Helper: `(Z, ψ) ↦ (cobDir θ Z, −Z_0 S + S Z_1) + (ψ, 0)`, for antisymmetric `Z_0`, `Z_1` and
`ψ` in a space `K`: the flat directions of the learned skip. -/
private noncomputable def phiL_lsn {A : Arch T d 1} (θ : Params A dIn dOut)
    (S : Fin 1 → Matrix d d ℝ) (K : Submodule ℝ (Params A dIn dOut)) :
    (Fin (1 + 1) → antisymmetric d) × K →ₗ[ℝ] Params A dIn dOut × (Fin 1 → Matrix d d ℝ) :=
  (((cobDirLin θ).comp (LinearMap.compLeft (antisymmetric d).subtype (Fin (1 + 1)))).prod
    ((skipDirLin_lsn S).comp (LinearMap.compLeft (antisymmetric d).subtype (Fin (1 + 1))))).coprod
    ((LinearMap.inl ℝ (Params A dIn dOut) (Fin 1 → Matrix d d ℝ)).comp K.subtype)

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
private theorem phiL_apply_lsn {A : Arch T d 1} (θ : Params A dIn dOut)
    (S : Fin 1 → Matrix d d ℝ) (K : Submodule ℝ (Params A dIn dOut))
    (Z : Fin (1 + 1) → antisymmetric d) (ψ : K) :
    phiL_lsn θ S K (Z, ψ) = (cobDir θ (fun ℓ => (Z ℓ : Matrix d d ℝ)),
      fun ℓ => -((Z ℓ.castSucc : Matrix d d ℝ) * S ℓ) + S ℓ * (Z ℓ.succ : Matrix d d ℝ))
      + ((ψ : Params A dIn dOut), 0) := rfl

omit [Fintype T] [Nonempty T] in
/-- Helper: `(Y, ψ) ↦ cobDir θ (fun _ => Y) + ψ`, for antisymmetric `Y` and `ψ` in a space `K`:
the flat directions of the residual network. -/
private noncomputable def phiR_lsn {A : Arch T d 1} (θ : Params A dIn dOut)
    (K : Submodule ℝ (Params A dIn dOut)) : antisymmetric d × K →ₗ[ℝ] Params A dIn dOut :=
  ((cobDirLin θ).comp (LinearMap.pi fun _ : Fin (1 + 1) => (antisymmetric d).subtype)).coprod
    K.subtype

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
private theorem phiR_apply_lsn {A : Arch T d 1} (θ : Params A dIn dOut)
    (K : Submodule ℝ (Params A dIn dOut)) (Y : antisymmetric d) (ψ : K) :
    phiR_lsn θ K (Y, ψ) = cobDir θ (fun _ => (Y : Matrix d d ℝ)) + ψ := rfl

/-! ### Steps 1 to 5: every flat direction is a rotation plus a direction of `K_U` -/

omit [Nonempty T] [DecidableEq d] [Fintype dOut] in
/-- Helper (part (a)): if every direction `(η, ρ)` of `F` satisfies the conclusion of Steps 1 to 3
on `U`, and `NoSymmetricPart` holds on `U`, then `F` lies in the range of `phiL_lsn` with `K_U`. -/
private theorem le_range_phiL_lsn {A : Arch T d 1} {ε : ℝ} (hε : 0 < ε) (θ : Params A dIn dOut)
    (S : Fin 1 → Matrix d d ℝ) (U : Set (Matrix T dIn ℝ)) (hX : NoSymmetricPart A ε θ U)
    (F : Submodule ℝ (Params A dIn dOut × (Fin 1 → Matrix d d ℝ)))
    (hF : ∀ η ρ, (η, ρ) ∈ F → ∃ X Y : Matrix d d ℝ, Yᵀ = -Y ∧ η.E = θ.E * X ∧
      ρ 0 = S 0 * Y - X * S 0 ∧ η.D = -(Y * θ.D) ∧
      ∀ x ∈ U,
        fderiv ℝ (A.f 0) (rmsNorm ε (x * θ.E) * θ.read 0)
            (fderiv ℝ (rmsNorm ε : Matrix T d ℝ → Matrix T d ℝ) (x * θ.E) (x * θ.E * X)
                * θ.read 0
              + rmsNorm ε (x * θ.E) * η.read 0) * θ.write 0
          + A.f 0 (rmsNorm ε (x * θ.E) * θ.read 0) * η.write 0
          = A.f 0 (rmsNorm ε (x * θ.E) * θ.read 0) * θ.write 0 * Y) :
    F ≤ LinearMap.range (phiL_lsn θ S (blockFlat_lsn A ε θ U)) := by
  rintro ⟨η, ρ⟩ hp
  obtain ⟨X, Y, hY, hηE, hρ, hηD, heq⟩ := hF η ρ hp
  -- Step 4: `X` is antisymmetric
  obtain ⟨hXa, hK⟩ := antisymm_and_mem_lsn hε θ U hX X Y _ _ heq
  -- Step 5: the rotation `Z = (X, Y)` and the rest `ψ = η − cobDir θ Z`, a direction of `K_U`
  let Z : Fin (1 + 1) → antisymmetric d := ![⟨X, hXa⟩, ⟨Y, hY⟩]
  let ψ : Params A dIn dOut := η - cobDir θ (fun ℓ => (Z ℓ : Matrix d d ℝ))
  have hψ : ψ ∈ blockFlat_lsn A ε θ U := by
    refine ⟨?_, ?_, fun x hx => ?_⟩
    · show η.E - θ.E * X = 0
      rw [hηE, sub_self]
    · show η.D - -(Y * θ.D) = 0
      rw [hηD, sub_neg_eq_add, neg_add_cancel]
    · show fderiv ℝ (A.f 0) (rmsNorm ε (x * θ.E) * θ.read 0)
          (rmsNorm ε (x * θ.E) * (η.read 0 - -(X * θ.read 0))) * θ.write 0
        + A.f 0 (rmsNorm ε (x * θ.E) * θ.read 0) * (η.write 0 - θ.write 0 * Y) = 0
      rw [sub_neg_eq_add]
      exact hK x hx
  refine ⟨(Z, ⟨ψ, hψ⟩), (phiL_apply_lsn θ S _ Z ⟨ψ, hψ⟩).trans (Prod.ext ?_ ?_)⟩
  · show cobDir θ (fun ℓ => (Z ℓ : Matrix d d ℝ)) + ψ = η
    exact add_sub_cancel _ _
  · funext ℓ
    fin_cases ℓ
    show -(X * S 0) + S 0 * Y + 0 = ρ 0
    rw [hρ, add_zero]
    abel

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dOut] in
/-- Helper (part (b)): if every direction `η` of `F` satisfies the conclusion of Steps 1 to 3 of
the residual network on `U`, then `F` lies in the range of `phiR_lsn` with `K_U`. -/
private theorem le_range_phiR_lsn {A : Arch T d 1} {ε : ℝ} (θ : Params A dIn dOut)
    (U : Set (Matrix T dIn ℝ)) (F : Submodule ℝ (Params A dIn dOut))
    (hF : ∀ η ∈ F, ∃ Y : Matrix d d ℝ, Yᵀ = -Y ∧ η.E = θ.E * Y ∧ η.D = -(Y * θ.D) ∧
      ∀ x ∈ U,
        fderiv ℝ (A.f 0) (rmsNorm ε (x * θ.E) * θ.read 0)
            (rmsNorm ε (x * θ.E) * (η.read 0 + Y * θ.read 0)) * θ.write 0
          + A.f 0 (rmsNorm ε (x * θ.E) * θ.read 0) * (η.write 0 - θ.write 0 * Y) = 0) :
    F ≤ LinearMap.range (phiR_lsn θ (blockFlat_lsn A ε θ U)) := by
  intro η hη
  obtain ⟨Y, hY, hηE, hηD, hK⟩ := hF η hη
  -- the rest `ψ = η − cobDir θ (fun _ => Y)` is a direction of `K_U`
  let ψ : Params A dIn dOut := η - cobDir θ (fun _ => Y)
  have hψ : ψ ∈ blockFlat_lsn A ε θ U := by
    refine ⟨?_, ?_, fun x hx => ?_⟩
    · show η.E - θ.E * Y = 0
      rw [hηE, sub_self]
    · show η.D - -(Y * θ.D) = 0
      rw [hηD, sub_neg_eq_add, neg_add_cancel]
    · show fderiv ℝ (A.f 0) (rmsNorm ε (x * θ.E) * θ.read 0)
          (rmsNorm ε (x * θ.E) * (η.read 0 - -(Y * θ.read 0))) * θ.write 0
        + A.f 0 (rmsNorm ε (x * θ.E) * θ.read 0) * (η.write 0 - θ.write 0 * Y) = 0
      rw [sub_neg_eq_add]
      exact hK x hx
  exact ⟨(⟨Y, hY⟩, ⟨ψ, hψ⟩), (phiR_apply_lsn θ _ _ _).trans (add_sub_cancel _ _)⟩

omit [Fintype T] [Nonempty T] [Fintype dIn] [Fintype dOut] in
/-- Helper: the domain of `phiL_lsn` has dimension `d (d − 1) + dim K`. -/
private theorem finrank_domL_lsn {M : Type*} [AddCommGroup M] [Module ℝ M]
    [FiniteDimensional ℝ M] (K : Submodule ℝ M) :
    Module.finrank ℝ ((Fin (1 + 1) → antisymmetric d) × K)
      = Fintype.card d * (Fintype.card d - 1) + Module.finrank ℝ K := by
  rw [Module.finrank_prod,
    Module.finrank_pi_fintype (R := ℝ) (ι := Fin (1 + 1)) (M := fun _ => antisymmetric d),
    finrank_antisymmetric, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have h2 := Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self (Fintype.card d))
  generalize Fintype.card d * (Fintype.card d - 1) = n at h2 ⊢
  omega

omit [Fintype T] [Nonempty T] [Fintype dIn] [Fintype dOut] in
/-- Helper: the domain of `phiR_lsn` has dimension `d (d − 1)/2 + dim K`. -/
private theorem finrank_domR_lsn {M : Type*} [AddCommGroup M] [Module ℝ M]
    [FiniteDimensional ℝ M] (K : Submodule ℝ M) :
    Module.finrank ℝ (antisymmetric d × K)
      = Fintype.card d * (Fintype.card d - 1) / 2 + Module.finrank ℝ K := by
  rw [Module.finrank_prod, finrank_antisymmetric]

/-! ### The chain rule at one input -/

omit [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (a copy of the private `hasDerivAt_mul_son` of `OneBlock/ResidualRMSStepsOn.lean`): the
product rule for matrices depending on one real variable. -/
private theorem hasDerivAt_mul_lsn {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
    {P : ℝ → Matrix m n ℝ} {Q : ℝ → Matrix n p ℝ} {P' P0 : Matrix m n ℝ} {Q' Q0 : Matrix n p ℝ}
    {τ : ℝ} (hP : HasDerivAt P P' τ) (hQ : HasDerivAt Q Q' τ) (hP0 : P τ = P0) (hQ0 : Q τ = Q0) :
    HasDerivAt (fun s => P s * Q s) (P' * Q0 + P0 * Q') τ := by
  subst hP0 hQ0
  refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => ?_
  have hPe : ∀ k, HasDerivAt (fun s => P s i k) (P' i k) τ := fun k =>
    hasDerivAt_pi.1 (hasDerivAt_pi.1 hP i) k
  have hQe : ∀ k, HasDerivAt (fun s => Q s k j) (Q' k j) τ := fun k =>
    hasDerivAt_pi.1 (hasDerivAt_pi.1 hQ k) j
  have h : HasDerivAt (fun s => ∑ k, P s i k * Q s k j)
      (∑ k, (P' i k * Q τ k j + P τ i k * Q' k j)) τ :=
    HasDerivAt.fun_sum (u := Finset.univ) (A := fun k s => P s i k * Q s k j)
      fun k _ => (hPe k).mul (hQe k)
  refine h.congr_deriv ?_
  simp only [Matrix.add_apply, Matrix.mul_apply, Finset.sum_add_distrib]

omit [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (a copy of the private `hasDerivAt_affine_son`): `τ ↦ M + τ N` has the derivative `N`
at `0`. -/
private theorem hasDerivAt_affine_lsn {m n : Type*} [Fintype m] [Fintype n]
    (M N : Matrix m n ℝ) : HasDerivAt (fun τ : ℝ => M + τ • N) N 0 := by
  have h := ((hasDerivAt_id (0 : ℝ)).smul_const N).const_add M
  rw [one_smul] at h
  exact h

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dOut] in
/-- Helper: the function of one block under pre-RMSNorm with the skip `S 0`,
`F(x) = N_ε(x E S + f(N_ε(x E) W_read) W_write) D`. -/
private theorem eval_eq_lsn {A : Arch T d 1} {ε : ℝ} (hA : A.χ = rmsNorm ε)
    (S : Fin 1 → Matrix d d ℝ) (θ : Params A dIn dOut) (x : Matrix T dIn ℝ) :
    eval A S θ x = rmsNorm ε (x * θ.E * S 0
      + A.f 0 (rmsNorm ε (x * θ.E) * θ.read 0) * θ.write 0) * θ.D := by
  have h1 : (Fin.last 1 : Fin 2) = (0 : Fin 1).succ := rfl
  rw [eval, h1, hidden_succ, Fin.castSucc_zero, hidden_zero, hA]

omit [Nonempty T] in
/-- Helper (Step 5, flatness of `K_B`): if `ψ` has `ψ_E = 0`, `ψ_D = 0` and the block has
derivative zero along it at `n = N_ε(x E)`, then along the line `θ + τ ψ` the output at `x` has
derivative zero, for every skip: only the output `f(n W_read) W_write` of the block moves. -/
private theorem hasDerivAt_eval_blockFlat_lsn {A : Arch T d 1} {ε : ℝ} (hε : 0 < ε)
    (hA : A.χ = rmsNorm ε) (S : Fin 1 → Matrix d d ℝ) (θ ψ : Params A dIn dOut)
    (x : Matrix T dIn ℝ) (hfx : DifferentiableAt ℝ (A.f 0) (rmsNorm ε (x * θ.E) * θ.read 0))
    (hψE : ψ.E = 0) (hψD : ψ.D = 0)
    (hψ : fderiv ℝ (A.f 0) (rmsNorm ε (x * θ.E) * θ.read 0) (rmsNorm ε (x * θ.E) * ψ.read 0)
        * θ.write 0 + A.f 0 (rmsNorm ε (x * θ.E) * θ.read 0) * ψ.write 0 = 0) :
    HasDerivAt (fun τ : ℝ => eval A S (θ + τ • ψ) x) 0 0 := by
  -- along the line, `E` and `D` stay, and only `W_read`, `W_write` move
  have e : (fun τ : ℝ => eval A S (θ + τ • ψ) x) = fun τ =>
      rmsNorm ε (x * θ.E * S 0 + A.f 0 (rmsNorm ε (x * θ.E) * (θ.read 0 + τ • ψ.read 0))
        * (θ.write 0 + τ • ψ.write 0)) * θ.D := by
    funext τ
    rw [eval_eq_lsn hA]
    simp only [Params.add_E, Params.smul_E, Params.add_read, Params.smul_read, Params.add_write,
      Params.smul_write, Params.add_D, Params.smul_D, hψE, hψD, smul_zero, add_zero]
  rw [e]
  -- `n W_read(τ)`, `f(n W_read(τ))`, `f(n W_read(τ)) W_write(τ)`: derivative zero at `0`
  have hR := hasDerivAt_mul_lsn (hasDerivAt_const (0 : ℝ) (rmsNorm ε (x * θ.E)))
    (hasDerivAt_affine_lsn (θ.read 0) (ψ.read 0)) (P0 := rmsNorm ε (x * θ.E))
    (Q0 := θ.read 0) rfl (by simp)
  rw [Matrix.zero_mul, zero_add] at hR
  have hF := hfx.hasFDerivAt.comp_hasDerivAt_of_eq 0 hR (by simp)
  have hFW := hasDerivAt_mul_lsn hF (hasDerivAt_affine_lsn (θ.write 0) (ψ.write 0))
    (P0 := A.f 0 (rmsNorm ε (x * θ.E) * θ.read 0)) (Q0 := θ.write 0) (by simp) (by simp)
  -- `h_1(τ) = x E S + …`, `N_ε(h_1(τ))` and `N_ε(h_1(τ)) D`
  have hH := (hFW.congr_deriv hψ).const_add (x * θ.E * S 0)
  have hN := ((differentiable_rmsNorm (T := T) (d := d) hε)
    (x * θ.E * S 0 + A.f 0 (rmsNorm ε (x * θ.E) * θ.read 0) * θ.write 0)).hasFDerivAt
    |>.comp_hasDerivAt_of_eq 0 hH (by simp)
  have hND := hasDerivAt_mul_lsn (hN.congr_deriv (ContinuousLinearMap.map_zero _))
    (hasDerivAt_const (0 : ℝ) θ.D)
    (P0 := rmsNorm ε (x * θ.E * S 0 + A.f 0 (rmsNorm ε (x * θ.E) * θ.read 0) * θ.write 0))
    (Q0 := θ.D) (by simp) rfl
  exact hND.congr_deriv (by rw [Matrix.zero_mul, Matrix.mul_zero, add_zero])

omit [Nonempty T] in
/-- Helper: for a differentiable block, the directions of `K_univ` are flat for the residual
network (Step 5 of part (ii)). -/
private theorem blockFlat_le_flat_lsn {A : Arch T d 1} {ε : ℝ} (hε : 0 < ε)
    (hA : A.χ = rmsNorm ε) (hf : Differentiable ℝ (A.f 0)) (θ : Params A dIn dOut) :
    blockFlat_lsn A ε θ Set.univ ≤ flat A 1 θ := by
  rintro ψ ⟨hψE, hψD, hψ⟩
  rw [flat, Submodule.mem_iInf]
  intro x
  rw [LinearMap.mem_ker]
  show fderiv ℝ (fun θ' : Params A dIn dOut => eval A 1 θ' x) θ ψ = 0
  by_cases hx : DifferentiableAt ℝ (fun θ' : Params A dIn dOut => eval A 1 θ' x) θ
  · -- the chain rule along the line `θ + τ ψ`
    exact (hasDerivAt_eval_line 1 θ ψ x hx).unique
      (hasDerivAt_eval_blockFlat_lsn hε hA 1 θ ψ x (hf _) hψE hψD (hψ x (Set.mem_univ x)))
  · rw [fderiv_zero_of_not_differentiableAt hx, _root_.zero_apply]

omit [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (a copy of the private `differentiableAt_matMul_son`): the product of two matrix-valued
maps that are differentiable at a point is differentiable there. -/
private theorem differentiableAt_matMul_lsn {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
    {f : P → Matrix m n ℝ} {g : P → Matrix n p ℝ} {y : P}
    (hf : DifferentiableAt ℝ f y) (hg : DifferentiableAt ℝ g y) :
    DifferentiableAt ℝ (fun y => f y * g y) y := by
  -- matrix multiplication as a bilinear map
  let B : Matrix m n ℝ →ₗ[ℝ] Matrix n p ℝ →ₗ[ℝ] Matrix m p ℝ :=
    LinearMap.mk₂ ℝ (fun a b => a * b) Matrix.add_mul (fun c a b => Matrix.smul_mul c a b)
      Matrix.mul_add (fun c a b => Matrix.mul_smul a c b)
  -- the same map with continuous linear maps (all spaces are finite-dimensional)
  let B' : Matrix m n ℝ →L[ℝ] Matrix n p ℝ →L[ℝ] Matrix m p ℝ :=
    LinearMap.toContinuousLinearMap
      ((LinearMap.toContinuousLinearMap :
        (Matrix n p ℝ →ₗ[ℝ] Matrix m p ℝ) ≃ₗ[ℝ] (Matrix n p ℝ →L[ℝ] Matrix m p ℝ)).toLinearMap ∘ₗ B)
  have hB : (fun y => f y * g y) = fun y => B' (f y) (g y) := rfl
  rw [hB]
  exact (B'.differentiableAt.comp y hf).clm_apply hg

omit [Nonempty T] in
/-- Helper: at an input `x` at which `f` is differentiable at `N_ε(x E) W_read`, the output of the
learned skip is a differentiable function of `(θ, R)`. -/
private theorem differentiableAt_evalSkips_lsn {A : Arch T d 1} {ε : ℝ} (hε : 0 < ε)
    (hA : A.χ = rmsNorm ε) (θ : Params A dIn dOut) (R : Fin 1 → Matrix d d ℝ)
    (x : Matrix T dIn ℝ)
    (hfx : DifferentiableAt ℝ (A.f 0) (rmsNorm ε (x * θ.E) * θ.read 0)) :
    DifferentiableAt ℝ (fun p : Params A dIn dOut × (Fin 1 → Matrix d d ℝ) =>
      evalSkips A (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) p x) (θ, R) := by
  have e : (fun p : Params A dIn dOut × (Fin 1 → Matrix d d ℝ) =>
      evalSkips A (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) p x)
      = fun p => rmsNorm ε (x * p.1.E * p.2 0
          + A.f 0 (rmsNorm ε (x * p.1.E) * p.1.read 0) * p.1.write 0) * p.1.D :=
    funext fun p => eval_eq_lsn hA p.2 p.1 x
  rw [e]
  -- the weights and the skip are linear, hence differentiable, functions of `(θ, R)`
  have hE : DifferentiableAt ℝ
      (fun p : Params A dIn dOut × (Fin 1 → Matrix d d ℝ) => p.1.E) (θ, R) :=
    ((LinearMap.toContinuousLinearMap (Params.linE (A := A) (dIn := dIn) (dOut := dOut))).comp
      (ContinuousLinearMap.fst ℝ _ (Fin 1 → Matrix d d ℝ))).differentiableAt
  have hR : DifferentiableAt ℝ
      (fun p : Params A dIn dOut × (Fin 1 → Matrix d d ℝ) => p.1.read 0) (θ, R) :=
    ((LinearMap.toContinuousLinearMap
      (Params.linRead (A := A) (dIn := dIn) (dOut := dOut) 0)).comp
      (ContinuousLinearMap.fst ℝ _ (Fin 1 → Matrix d d ℝ))).differentiableAt
  have hW : DifferentiableAt ℝ
      (fun p : Params A dIn dOut × (Fin 1 → Matrix d d ℝ) => p.1.write 0) (θ, R) :=
    ((LinearMap.toContinuousLinearMap
      (Params.linWrite (A := A) (dIn := dIn) (dOut := dOut) 0)).comp
      (ContinuousLinearMap.fst ℝ _ (Fin 1 → Matrix d d ℝ))).differentiableAt
  have hD : DifferentiableAt ℝ
      (fun p : Params A dIn dOut × (Fin 1 → Matrix d d ℝ) => p.1.D) (θ, R) :=
    ((LinearMap.toContinuousLinearMap (Params.linD (A := A) (dIn := dIn) (dOut := dOut))).comp
      (ContinuousLinearMap.fst ℝ _ (Fin 1 → Matrix d d ℝ))).differentiableAt
  have hS : DifferentiableAt ℝ
      (fun p : Params A dIn dOut × (Fin 1 → Matrix d d ℝ) => p.2 0) (θ, R) :=
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => Matrix d d ℝ) 0).comp
      (ContinuousLinearMap.snd ℝ (Params A dIn dOut) _)).differentiableAt
  -- `x E`, `N_ε(x E)`, `N_ε(x E) W_read`, `f(…)`
  have h1 : DifferentiableAt ℝ
      (fun p : Params A dIn dOut × (Fin 1 → Matrix d d ℝ) => x * p.1.E) (θ, R) :=
    differentiableAt_matMul_lsn (differentiableAt_const x) hE
  have h2 : DifferentiableAt ℝ
      (fun p : Params A dIn dOut × (Fin 1 → Matrix d d ℝ) => rmsNorm ε (x * p.1.E)) (θ, R) :=
    DifferentiableAt.comp (f := fun p : Params A dIn dOut × (Fin 1 → Matrix d d ℝ) =>
      x * p.1.E) (θ, R) (differentiable_rmsNorm hε _) h1
  have h3 : DifferentiableAt ℝ (fun p : Params A dIn dOut × (Fin 1 → Matrix d d ℝ) =>
      rmsNorm ε (x * p.1.E) * p.1.read 0) (θ, R) :=
    differentiableAt_matMul_lsn h2 hR
  have h4 : DifferentiableAt ℝ (fun p : Params A dIn dOut × (Fin 1 → Matrix d d ℝ) =>
      A.f 0 (rmsNorm ε (x * p.1.E) * p.1.read 0)) (θ, R) :=
    DifferentiableAt.comp (f := fun p : Params A dIn dOut × (Fin 1 → Matrix d d ℝ) =>
      rmsNorm ε (x * p.1.E) * p.1.read 0) (θ, R) hfx h3
  -- `h_1 = x E S + f(…) W_write`, `N_ε(h_1)` and `N_ε(h_1) D`
  have h5 : DifferentiableAt ℝ (fun p : Params A dIn dOut × (Fin 1 → Matrix d d ℝ) =>
      x * p.1.E * p.2 0 + A.f 0 (rmsNorm ε (x * p.1.E) * p.1.read 0) * p.1.write 0) (θ, R) :=
    (differentiableAt_matMul_lsn h1 hS).add (differentiableAt_matMul_lsn h4 hW)
  have h6 : DifferentiableAt ℝ (fun p : Params A dIn dOut × (Fin 1 → Matrix d d ℝ) =>
      rmsNorm ε (x * p.1.E * p.2 0
        + A.f 0 (rmsNorm ε (x * p.1.E) * p.1.read 0) * p.1.write 0)) (θ, R) :=
    DifferentiableAt.comp (f := fun p : Params A dIn dOut × (Fin 1 → Matrix d d ℝ) =>
      x * p.1.E * p.2 0 + A.f 0 (rmsNorm ε (x * p.1.E) * p.1.read 0) * p.1.write 0) (θ, R)
      (differentiable_rmsNorm hε _) h5
  exact differentiableAt_matMul_lsn h6 hD

omit [Nonempty T] in
/-- Helper: for a differentiable block, the directions `(ψ, 0)`, `ψ ∈ K_univ`, are flat for the
learned skip (the skip does not move, and the output of the block has derivative zero). -/
private theorem mem_flatSkips_of_blockFlat_lsn {A : Arch T d 1} {ε : ℝ} (hε : 0 < ε)
    (hA : A.χ = rmsNorm ε) (hf : Differentiable ℝ (A.f 0)) (θ : Params A dIn dOut)
    (R : Fin 1 → Matrix d d ℝ) {ψ : Params A dIn dOut}
    (hψ : ψ ∈ blockFlat_lsn A ε θ Set.univ) :
    (ψ, 0) ∈ flatSkips A (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) (θ, R) := by
  obtain ⟨hψE, hψD, hψ⟩ := hψ
  refine (Submodule.mem_iInf _).2 fun x => LinearMap.mem_ker.2 ?_
  show fderiv ℝ (fun p' : Params A dIn dOut × (Fin 1 → Matrix d d ℝ) =>
    evalSkips A (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) p' x) (θ, R) (ψ, 0) = 0
  -- the chain rule along the line `(θ + τ ψ, R)`
  have hdiff := differentiableAt_evalSkips_lsn hε hA θ R x (hf _)
  have hline : HasDerivAt (fun τ : ℝ => ((θ, R) : Params A dIn dOut × (Fin 1 → Matrix d d ℝ))
      + τ • (ψ, (0 : Fin 1 → Matrix d d ℝ))) (ψ, 0) 0 := by
    have h := ((hasDerivAt_id (0 : ℝ)).smul_const (ψ, (0 : Fin 1 → Matrix d d ℝ))).const_add
      ((θ, R) : Params A dIn dOut × (Fin 1 → Matrix d d ℝ))
    rw [one_smul] at h
    exact h
  have h1 := hdiff.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hline (by rw [zero_smul, add_zero])
  have e : ((fun p' : Params A dIn dOut × (Fin 1 → Matrix d d ℝ) =>
      evalSkips A (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) p' x) ∘
      fun τ : ℝ => ((θ, R) : Params A dIn dOut × (Fin 1 → Matrix d d ℝ))
        + τ • (ψ, (0 : Fin 1 → Matrix d d ℝ))) = fun τ => eval A R (θ + τ • ψ) x := by
    funext τ
    simp only [Function.comp_apply, evalSkips, Prod.smul_mk, Prod.mk_add_mk, smul_zero,
      add_zero]
    rfl
  rw [e] at h1
  exact h1.unique (hasDerivAt_eval_blockFlat_lsn hε hA R θ ψ x (hf _) hψE hψD
    (hψ x (Set.mem_univ x)))

/-! ### The open cone `V` (copies of the private helpers of `OneBlock/ResidualRMSStepsOn.lean`) -/

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: `0 ≤ ⟨v, v⟩`. -/
private theorem dot_self_nonneg_lsn (v : d → ℝ) : 0 ≤ v ⬝ᵥ v :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)

omit [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: scaling the rows of `h` by positive numbers scales the rows of `h M` by the same
numbers, so it keeps `h M` in `V`. -/
private theorem rowScale_mul_mem_lsn {m r : Type*} [Fintype m] {V : Set (Matrix T r ℝ)}
    (hVs : ∀ M ∈ V, ∀ c : T → ℝ, (∀ t, 0 < c t) → (Matrix.of fun t i => c t * M t i) ∈ V)
    {h : Matrix T m ℝ} {M : Matrix m r ℝ} (hM : h * M ∈ V) {c : T → ℝ} (hc : ∀ t, 0 < c t) :
    (Matrix.of fun t => c t • h t) * M ∈ V := by
  have e : (Matrix.of fun t => c t • h t) * M = Matrix.of fun t i => c t * (h * M) t i := by
    ext t i
    simp only [Matrix.mul_apply, Matrix.of_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
      mul_assoc]
  rw [e]
  exact hVs _ hM c hc

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: for `ε > 0`, `h M ∈ V` gives `N_ε(h) M ∈ V` (`N_ε` scales every row by a positive
number). -/
private theorem rmsNorm_mul_mem_lsn {ε : ℝ} (hε : 0 < ε) {r : Type*} {V : Set (Matrix T r ℝ)}
    (hVs : ∀ M ∈ V, ∀ c : T → ℝ, (∀ t, 0 < c t) → (Matrix.of fun t i => c t * M t i) ∈ V)
    {h : Matrix T d ℝ} {M : Matrix d r ℝ} (hM : h * M ∈ V) : rmsNorm ε h * M ∈ V :=
  rowScale_mul_mem_lsn hVs hM
    (c := fun t => (Real.sqrt ((h t ⬝ᵥ h t) / (Fintype.card d : ℝ) + ε))⁻¹)
    fun t => inv_pos.2 (Real.sqrt_pos.2 (by have := dot_self_nonneg_lsn (h t); positivity))

/-! ### The count -/

/-- Helper (the private `half_add_half_lsk` of `OneBlock/LearnedSkipKinds.lean`):
`n (n + 1)/2 + n (n − 1)/2 = n²`. -/
private theorem half_add_half_lsn (n : ℕ) : n * (n + 1) / 2 + n * (n - 1) / 2 = n ^ 2 := by
  have h1 := Nat.two_mul_div_two_of_even (Nat.even_mul_succ_self n)
  have h2 := Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self n)
  have h3 : n * (n + 1) + n * (n - 1) = 2 * n ^ 2 := by
    cases n with
    | zero => rfl
    | succ m => rw [Nat.add_sub_cancel]; ring
  generalize n * (n + 1) = y at h1 h3 ⊢
  generalize n * (n - 1) = x at h2 h3 ⊢
  generalize n ^ 2 = q at h3 ⊢
  omega

omit [Fintype T] [Nonempty T] [DecidableEq d] in
/-- Helper: the weights and the skip have `P + d²` entries. -/
private theorem finrank_paramsSkip_lsn {A : Arch T d 1} :
    Module.finrank ℝ (Params A dIn dOut × (Fin 1 → Matrix d d ℝ))
      = Module.finrank ℝ (Params A dIn dOut) + Fintype.card d ^ 2 := by
  rw [Module.finrank_prod, Module.finrank_pi_fintype, Module.finrank_matrix]
  simp [sq]

/-- **Theorem 4.6 (ii), "A learned skip raises it by exactly `d (d + 1)/2` more than an identity
skip", at one parameter, for a continuously differentiable block (`ε > 0`):** if `E` and `D` have
rank `d`, the skip `A = R 0` is invertible and Step 4 holds at `θ` (`NoSymmetricPart` at all
inputs), the network with the full learned skip has at `(θ, A)` the functional dimension of the
residual network at `θ` plus `d (d + 1)/2`. -/
theorem funDimLearned_eq_funDim_residual_add_of_noSymmetricPart {A : Arch T d 1} {ε : ℝ}
    (hε : 0 < ε) (hA : A.χ = rmsNorm ε) (hf : ContDiff ℝ 1 (A.f 0)) (θ : Params A dIn dOut)
    (R : Fin 1 → Matrix d d ℝ) (hE : θ.E.rank = Fintype.card d)
    (hD : θ.D.rank = Fintype.card d) (hR : IsUnit (R 0).det)
    (hX : NoSymmetricPart A ε θ Set.univ) :
    funDimLearned A (θ, R)
      = funDim A 1 θ + Fintype.card d * (Fintype.card d + 1) / 2 := by
  sorry

/-- **The same for a block that is continuously differentiable on an open cone `V` of
pre-activations (`ε > 0`):** let `V` be open and invariant under positive scalings of the rows,
let some input with equal rows have its pre-activation `x E W_read` in `V`, let `E` and `D` have
rank `d` and the skip `A = R 0` be invertible. If Step 4 holds at the inputs with
`x E W_read ∈ V`, and every direction of the weights of the block along which
`B(n) = f(n W_read) W_write` has derivative zero at `n = N_ε(x E)` for these inputs is spanned by
directions of symmetries inside the block, then the network with the full learned skip has at
`(θ, A)` the functional dimension of the residual network at `θ` plus `d (d + 1)/2`, and a finite
batch of such inputs has a Jacobian of this rank. -/
theorem funDimLearned_eq_funDim_residual_add_of_noSymmetricPart_on {A : Arch T d 1} {ε : ℝ}
    (hε : 0 < ε) (hA : A.χ = rmsNorm ε) (V : Set (Matrix T (A.r 0) ℝ)) (hV : IsOpen V)
    (hVs : ∀ M ∈ V, ∀ c : T → ℝ, (∀ t, 0 < c t) → (Matrix.of fun t i => c t * M t i) ∈ V)
    (hf : ContDiffOn ℝ 1 (A.f 0) V) (θ : Params A dIn dOut) (R : Fin 1 → Matrix d d ℝ)
    (hE : θ.E.rank = Fintype.card d) (hD : θ.D.rank = Fintype.card d) (hR : IsUnit (R 0).det)
    (hw : ∃ w : dIn → ℝ, (Matrix.of fun _ : T => w) * θ.E * θ.read 0 ∈ V)
    (hX : NoSymmetricPart A ε θ {x | x * θ.E * θ.read 0 ∈ V})
    (hK : ∀ ψ : Params A dIn dOut, ψ.E = 0 → ψ.D = 0 →
      (∀ x : Matrix T dIn ℝ, x * θ.E * θ.read 0 ∈ V →
        fderiv ℝ (A.f 0) (rmsNorm ε (x * θ.E) * θ.read 0) (rmsNorm ε (x * θ.E) * ψ.read 0)
            * θ.write 0
          + A.f 0 (rmsNorm ε (x * θ.E) * θ.read 0) * ψ.write 0 = 0) →
      ψ ∈ Submodule.span ℝ {η | InsideBlocks A θ η}) :
    funDimLearned A (θ, R) = funDim A 1 θ + Fintype.card d * (Fintype.card d + 1) / 2 ∧
      ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i, X i * θ.E * θ.read 0 ∈ V) ∧
        jacobianRankSkips A (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) X (θ, R)
          = funDimLearned A (θ, R) := by
  -- the inputs `U` (`x E W_read ∈ V`) and the space `K_U` of the directions of the block with
  -- derivative zero at these inputs
  obtain ⟨U, hU⟩ : ∃ U : Set (Matrix T dIn ℝ), U = {x | x * θ.E * θ.read 0 ∈ V} := ⟨_, rfl⟩
  rw [← hU] at hX
  have hmemU : ∀ x, x ∈ U ↔ x * θ.E * θ.read 0 ∈ V := fun x => by rw [hU]; rfl
  let K := blockFlat_lsn A ε θ U
  -- `K_U` is spanned by directions of symmetries inside the block (the hypothesis `hK`)
  have hK' : K ≤ Submodule.span ℝ {η | InsideBlocks A θ η} := fun ψ hψ =>
    hK ψ hψ.1 hψ.2.1 fun x hx => hψ.2.2 x ((hmemU x).2 hx)
  -- at an input of `U`, `f` is differentiable at `N_ε(x E) W_read ∈ V`
  have hfx : ∀ x ∈ U, DifferentiableAt ℝ (A.f 0) (rmsNorm ε (x * θ.E) * θ.read 0) :=
    fun x hx => (hf.contDiffAt (hV.mem_nhds
      (rmsNorm_mul_mem_lsn hε hVs ((hmemU x).1 hx)))).differentiableAt one_ne_zero
  -- (a) the learned skip: the directions flat on `U` are rotations plus directions of `K_U`
  have hL : flatSkipsOn A (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) (θ, R) U
      ≤ LinearMap.range (phiL_lsn θ R K) := by
    refine le_range_phiL_lsn hε θ R U hX _ fun η ρ hp => ?_
    rw [hU] at hp
    obtain ⟨X, Y, hY, hηE, hρ, hηD, h⟩ :=
      exists_of_flatSkipsOn_learned_rmsNorm hε hA V hV hVs hf θ R hE hD hR hw η ρ hp
    exact ⟨X, Y, hY, hηE, hρ, hηD, fun x hx => h x ((hmemU x).1 hx)⟩
  have hdimL : Module.finrank ℝ
      (flatSkipsOn A (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) (θ, R) U)
      ≤ Fintype.card d * (Fintype.card d - 1) + Module.finrank ℝ K :=
    (Submodule.finrank_mono hL).trans
      ((LinearMap.finrank_range_le _).trans (finrank_domL_lsn K).le)
  -- (b) the residual network: the directions flat on `U` are rotations plus directions of `K_U`
  have hRs : flatOn A 1 θ U ≤ LinearMap.range (phiR_lsn θ K) := by
    refine le_range_phiR_lsn θ U _ fun η hη => ?_
    rw [hU] at hη
    obtain ⟨Y, hY, hηE, hηD, h⟩ :=
      exists_antisymm_of_flatOn_residual_rmsNorm hε hA V hV hVs hf θ hE hD hw η hη
    exact ⟨Y, hY, hηE, hηD, fun x hx => h x ((hmemU x).1 hx)⟩
  have hdimR : Module.finrank ℝ (flatOn A 1 θ U)
      ≤ Fintype.card d * (Fintype.card d - 1) / 2 + Module.finrank ℝ K :=
    (Submodule.finrank_mono hRs).trans
      ((LinearMap.finrank_range_le _).trans (finrank_domR_lsn K).le)
  -- (c) the upper bounds from the rotations and the symmetries inside the block
  have hupL := funDimLearned_add_le_rmsNorm' ε hA (θ, R) hE hD K hK'
  have hupR := funDim_add_le_residual_of_insideBlocks_rmsNorm θ ε hA K hK' hE
  -- `fd + dim (flat directions) = number of parameters`, and flat implies flat on `U`
  have hsumL : funDimLearned A (θ, R) + Module.finrank ℝ
      (flatSkips A (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) (θ, R))
      = Module.finrank ℝ (Params A dIn dOut × (Fin 1 → Matrix d d ℝ)) :=
    funDimSkips_add_finrank_flatSkips' A _ (θ, R)
  have hsumR := funDim_add_finrank_flat' (A := A) (S := 1) θ
  have hmonoL := Submodule.finrank_mono
    (flatSkips_le_flatSkipsOn A (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) (θ, R) U)
  have hmonoR := Submodule.finrank_mono (flat_le_flatOn (A := A) (S := 1) θ U)
  have hP := finrank_paramsSkip_lsn (A := A) (dIn := dIn) (dOut := dOut)
  -- a batch of inputs of `U` with rank `P + d² − dim (directions flat on U)`
  obtain ⟨n, Xb, hXb, hrank⟩ := exists_jacobianRankSkips_add_finrank_flatSkipsOn A
    (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) (θ, R) U
    fun x hx => differentiableAt_evalSkips_lsn hε hA θ R x (hfx x hx)
  -- the arithmetic: `d (d + 1)/2 + d (d − 1)/2 = d²` and `2 · (d (d − 1)/2) = d (d − 1)`
  have hhalf := half_add_half_lsn (Fintype.card d)
  have h2 := Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self (Fintype.card d))
  refine ⟨?_, n, Xb, fun i => (hmemU (Xb i)).1 (hXb i), ?_⟩
  · generalize Fintype.card d * (Fintype.card d + 1) / 2 = b at hhalf ⊢
    generalize Fintype.card d * (Fintype.card d - 1) = a at hhalf h2 hdimL hdimR hupL hupR
    generalize Fintype.card d ^ 2 = q at hhalf hupL hP
    omega
  · generalize Fintype.card d * (Fintype.card d - 1) = a at hdimL hupL
    generalize Fintype.card d ^ 2 = q at hupL hP
    omega

end Skips
