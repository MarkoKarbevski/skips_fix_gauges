import SkipsLean.Network.Defs

/-!
# Networks of mixed blocks

Paper (skips paper), Appendix A.1, "Mixed blocks": "A learned skip adds `hA` to the output of a
block, in place of `h`. It acts as `d_model` more hidden units with the identity as activation,
the read `A` and the write `I`. We call them identity units (Lin and Jegelka, 2018, Section 4). A
mixed block is a block with `d_model` identity units whose read `U` and write `V` are both
trainable `d_model × d_model` matrices (Figure 2). Let the read of the block have `p` columns and
its write `q` rows, so that `f` maps `ℝ^{T × p}` to `ℝ^{T × q}`, and define the fixed map
`f̃ : ℝ^{T × d_model} × ℝ^{T × p} → ℝ^{T × (d_model + q)}`, `f̃[u | z] = [u | f(z)]`, which is the
identity on the first `d_model` columns and `f` on the others. The mixed block computes
`h U V + f(h W_read) W_write = f̃(h [U | W_read]) [V ; W_write]`  (9).
So it has the form (1), with the read `[U | W_read]` and the write that stacks `V` on `W_write`,
and it is a block with the learned skip `A = U V`. A network with learned skips `A_ℓ` is the
network of mixed blocks with `U_ℓ = A_ℓ` and `V_ℓ = I`. Under pre-RMSNorm the skip reads `h` and
the block reads `N_ε(h)`, so the mixed block applies the map `χ(h) = [h | N_ε(h)]` before a
block-diagonal read: `h U V + f(N_ε(h) W_read) W_write`  (10)."

Here, for any architecture `A` on a model dimension `d : Type` (the columns of a read are indexed
by a type of the lowest universe):

* `A.mixed`: the architecture of the mixed blocks of `A`: the columns of the read of block `ℓ`
  are `d ⊕ A.r ℓ` (the identity units, then the hidden units), the rows of its write
  `d ⊕ A.w ℓ`, and its fixed map is `f̃`. A parameter of `A.mixed` holds `E`, the reads
  `[U_ℓ | W_read^ℓ]`, the writes that stack `V_ℓ` on `W_write^ℓ`, and `D`.
* `θ.mixU ℓ`, `θ.mixV ℓ`, `θ.unmix`: the matrices `U_ℓ`, `V_ℓ` and the parameters of the hidden
  units of a parameter `θ` of `A.mixed`; `Params.mix θ U V`: the parameter with the hidden units
  of `θ` and the identity units `U`, `V`; every parameter of `A.mixed` is of this form.
* `evalMixed A θ x`: the function of the network of mixed blocks, equations (9) and (10) for any
  `χ`: the identity units read `h` itself and the hidden units read `χ(h)`; it is the network of
  `A` with the learned skips `U_ℓ V_ℓ` and the hidden units of `θ`.
* `f_mixed_mul`: equation (9); `evalMixed_eq_eval`: without normalization the network of mixed
  blocks is the skipless network of the architecture `A.mixed`, "So it has the form (1)".
* `evalMixed_mix_one`: "A network with learned skips `A_ℓ` is the network of mixed blocks with
  `U_ℓ = A_ℓ` and `V_ℓ = I`."

The changes of basis at the junctions of these networks: `Symmetry/MixedJunctions.lean`.
-/

namespace Skips

open Matrix

variable {T : Type*} {d : Type} {dIn dOut : Type*} {L : ℕ} [Fintype d] [Fintype dIn]

/-- **The architecture of the mixed blocks of `A`** (equation (9)): block `ℓ` has `d` identity
units beside its hidden units; the columns of its read are `d ⊕ A.r ℓ`, the rows of its write
`d ⊕ A.w ℓ`, and its fixed map is `f̃[u | z] = [u | f_ℓ(z)]`. -/
abbrev Arch.mixed (A : Arch T d L) : Arch T d L where
  r ℓ := d ⊕ A.r ℓ
  w ℓ := d ⊕ A.w ℓ
  f ℓ M := Matrix.of fun t =>
    Sum.elim (fun a => M t (Sum.inl a)) (A.f ℓ (M.submatrix id Sum.inr) t)
  χ := A.χ

variable {A : Arch T d L}

/-- The read `U_ℓ` of the identity units of block `ℓ`. -/
def Params.mixU (θ : Params A.mixed dIn dOut) (ℓ : Fin L) : Matrix d d ℝ :=
  (θ.read ℓ).submatrix id Sum.inl

/-- The write `V_ℓ` of the identity units of block `ℓ`. -/
def Params.mixV (θ : Params A.mixed dIn dOut) (ℓ : Fin L) : Matrix d d ℝ :=
  (θ.write ℓ).submatrix Sum.inl id

/-- The parameters of the hidden units of a network of mixed blocks: `E`, the reads `W_read^ℓ`,
the writes `W_write^ℓ` and `D`. -/
def Params.unmix (θ : Params A.mixed dIn dOut) : Params A dIn dOut where
  E := θ.E
  read ℓ := (θ.read ℓ).submatrix id Sum.inr
  write ℓ := (θ.write ℓ).submatrix Sum.inr id
  D := θ.D

/-- The parameter of the network of mixed blocks with the hidden units of `θ` and the identity
units `U_ℓ`, `V_ℓ`: the reads `[U_ℓ | W_read^ℓ]` and the writes that stack `V_ℓ` on
`W_write^ℓ`. -/
def Params.mix (θ : Params A dIn dOut) (U V : Fin L → Matrix d d ℝ) :
    Params A.mixed dIn dOut where
  E := θ.E
  read ℓ := Matrix.of fun a => Sum.elim (U ℓ a) (θ.read ℓ a)
  write ℓ := Matrix.of (Sum.elim (V ℓ) (θ.write ℓ))
  D := θ.D

/-- **The function of the network of mixed blocks** (equations (9) and (10)):
`h_ℓ = h_{ℓ-1} U_ℓ V_ℓ + f_ℓ(χ(h_{ℓ-1}) W_read^ℓ) W_write^ℓ`, the network of `A` with the learned
skips `U_ℓ V_ℓ`. The identity units read `h` itself; the hidden units read `χ(h)`. -/
def evalMixed (A : Arch T d L) (θ : Params A.mixed dIn dOut) (x : Matrix T dIn ℝ) :
    Matrix T dOut ℝ :=
  eval A (fun ℓ => θ.mixU ℓ * θ.mixV ℓ) θ.unmix x

/-- The identity units of `Params.mix θ U V` have the read `U`. -/
theorem Params.mixU_mix (θ : Params A dIn dOut) (U V : Fin L → Matrix d d ℝ) :
    (Params.mix θ U V).mixU = U := by
  -- the columns `Sum.inl` of `[U_ℓ | W_read^ℓ]` are `U_ℓ`
  funext ℓ
  ext a b
  rfl

/-- The identity units of `Params.mix θ U V` have the write `V`. -/
theorem Params.mixV_mix (θ : Params A dIn dOut) (U V : Fin L → Matrix d d ℝ) :
    (Params.mix θ U V).mixV = V := by
  -- the rows `Sum.inl` of the write that stacks `V_ℓ` on `W_write^ℓ` are `V_ℓ`
  funext ℓ
  ext a b
  rfl

/-- The hidden units of `Params.mix θ U V` are those of `θ`. -/
theorem Params.unmix_mix (θ : Params A dIn dOut) (U V : Fin L → Matrix d d ℝ) :
    (Params.mix θ U V).unmix = θ := by
  -- the columns and rows `Sum.inr` are those of the hidden units of `θ`
  rfl

/-- Every parameter of a network of mixed blocks is `Params.mix` of its hidden units and its
identity units. -/
theorem Params.mix_unmix (θ : Params A.mixed dIn dOut) :
    Params.mix θ.unmix θ.mixU θ.mixV = θ := by
  obtain ⟨E, R, W, D⟩ := θ
  simp only [Params.mix, Params.unmix, Params.mixU, Params.mixV, Params.mk.injEq, true_and,
    and_true]
  -- a read or a write is determined by its columns or rows `Sum.inl` and `Sum.inr`
  constructor
  · funext ℓ
    ext a s
    cases s <;> rfl
  · funext ℓ
    ext s b
    cases s <;> rfl

/-- **Equation (9):** `f̃(h [U | W_read]) [V ; W_write] = h U V + f(h W_read) W_write`, for the
read `R = [U | W_read]` and the write `W` that stacks `V` on `W_write`. -/
theorem f_mixed_mul (A : Arch T d L) (ℓ : Fin L) (h : Matrix T d ℝ)
    (R : Matrix d (d ⊕ A.r ℓ) ℝ) (W : Matrix (d ⊕ A.w ℓ) d ℝ) :
    A.mixed.f ℓ (h * R) * W
      = h * R.submatrix id Sum.inl * W.submatrix Sum.inl id
        + A.f ℓ (h * R.submatrix id Sum.inr) * W.submatrix Sum.inr id := by
  -- the hidden units read the columns `Sum.inr` of `h R`, which are `h W_read`
  have hsub : (h * R).submatrix id Sum.inr = h * R.submatrix id Sum.inr := by
    rw [Matrix.submatrix_mul h R id id Sum.inr Function.bijective_id, Matrix.submatrix_id_id]
  show (Matrix.of fun t => Sum.elim (fun a => (h * R) t (Sum.inl a))
    (A.f ℓ ((h * R).submatrix id Sum.inr) t)) * W = _
  rw [hsub]
  -- entry by entry, the sum over `d ⊕ A.w ℓ` splits into the identity units and the hidden units
  ext t j
  rw [Matrix.mul_apply, Fintype.sum_sum_type]
  simp only [Matrix.of_apply, Sum.elim_inl, Sum.elim_inr, Matrix.add_apply, Matrix.mul_apply,
    Matrix.submatrix_apply, id_eq]

/-- **"So it has the form (1)":** without normalization, the network of mixed blocks is the
skipless network of the architecture `A.mixed`. -/
theorem evalMixed_eq_eval (hA : A.χ = id) (θ : Params A.mixed dIn dOut) (x : Matrix T dIn ℝ) :
    evalMixed A θ x = eval A.mixed 0 θ x := by
  have hχ : A.mixed.χ = id := hA
  -- the hidden states of the two networks agree, by induction on `ℓ`
  have hh : ∀ ℓ : Fin (L + 1), hidden A.mixed 0 θ x ℓ
      = hidden A (fun ℓ => θ.mixU ℓ * θ.mixV ℓ) θ.unmix x ℓ := by
    intro ℓ
    induction ℓ using Fin.induction with
    | zero => rw [hidden_zero, hidden_zero]; rfl
    | succ ℓ ih =>
      -- equation (9): `f̃(h [U | W_read]) [V ; W_write] = h U V + f(h W_read) W_write`
      rw [hidden_succ, hidden_succ, ← ih, hχ, id_eq, f_mixed_mul, Pi.zero_apply,
        Matrix.mul_zero, zero_add, Matrix.mul_assoc]
      rfl
  -- the readout reads `χ(h_L)` in both
  unfold evalMixed eval
  rw [hh (Fin.last L)]
  rfl

/-- **"A network with learned skips `A_ℓ` is the network of mixed blocks with `U_ℓ = A_ℓ` and
`V_ℓ = I`"**, for every `χ`. -/
theorem evalMixed_mix_one [DecidableEq d] (θ : Params A dIn dOut) (S : Fin L → Matrix d d ℝ)
    (x : Matrix T dIn ℝ) :
    evalMixed A (Params.mix θ S 1) x = eval A S θ x := by
  -- the skips are `U_ℓ V_ℓ = A_ℓ I = A_ℓ` and the hidden units are those of `θ`
  unfold evalMixed
  rw [Params.mixU_mix, Params.mixV_mix, Params.unmix_mix]
  simp only [Pi.one_apply, Matrix.mul_one]

end Skips
