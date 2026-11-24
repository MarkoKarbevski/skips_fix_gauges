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
  sorry

end Skips
