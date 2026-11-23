import SkipsLean.Network.Defs

/-!
# The parameters as a vector space

Paper (dimension paper): Section 2, `θ ∈ ℝ^P`.

The parameters `θ = (E, W_read^ℓ, W_write^ℓ, D)` form a real vector space, with the operations of
their four components. It is finite-dimensional, and `P` is its dimension,
`Module.finrank ℝ (Params A dIn dOut)`.

To differentiate in `θ`, the space needs a norm. Matrices carry the elementwise norm (the largest
absolute value of an entry), and the parameters the norm of the product of their components. On a
finite-dimensional space all norms give the same derivatives, so no statement depends on this
choice. Files that differentiate in `θ` start with `open scoped Matrix.Norms.Elementwise`.
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} {A : Arch T d L}

namespace Params

/-- The product of the four components of the parameters. -/
abbrev Prod (A : Arch T d L) (dIn dOut : Type*) : Type _ :=
  Matrix dIn d ℝ × (∀ ℓ, Matrix d (A.r ℓ) ℝ) × (∀ ℓ, Matrix (A.w ℓ) d ℝ) × Matrix d dOut ℝ

/-- The parameters are the tuples of their four components. -/
def equivProd : Params A dIn dOut ≃ Params.Prod A dIn dOut where
  toFun θ := (θ.E, θ.read, θ.write, θ.D)
  invFun p := ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Zero (Params A dIn dOut) := ⟨⟨0, fun _ => 0, fun _ => 0, 0⟩⟩

instance : Add (Params A dIn dOut) :=
  ⟨fun θ η => ⟨θ.E + η.E, fun ℓ => θ.read ℓ + η.read ℓ, fun ℓ => θ.write ℓ + η.write ℓ,
    θ.D + η.D⟩⟩

instance : Neg (Params A dIn dOut) :=
  ⟨fun θ => ⟨-θ.E, fun ℓ => -θ.read ℓ, fun ℓ => -θ.write ℓ, -θ.D⟩⟩

instance : Sub (Params A dIn dOut) :=
  ⟨fun θ η => ⟨θ.E - η.E, fun ℓ => θ.read ℓ - η.read ℓ, fun ℓ => θ.write ℓ - η.write ℓ,
    θ.D - η.D⟩⟩

instance {R : Type*} [SMul R ℝ] : SMul R (Params A dIn dOut) :=
  ⟨fun c θ => ⟨c • θ.E, fun ℓ => c • θ.read ℓ, fun ℓ => c • θ.write ℓ, c • θ.D⟩⟩

instance : AddCommGroup (Params A dIn dOut) :=
  Function.Injective.addCommGroup equivProd equivProd.injective rfl (fun _ _ => rfl)
    (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

/-- The map to the tuple of components, as an additive map. -/
def addHomProd : Params A dIn dOut →+ Params.Prod A dIn dOut where
  toFun := equivProd
  map_zero' := rfl
  map_add' _ _ := rfl

instance : Module ℝ (Params A dIn dOut) :=
  Function.Injective.module ℝ addHomProd equivProd.injective (fun _ _ => rfl)

/-- The parameters and the tuples of their components, as vector spaces. -/
def linearEquivProd : Params A dIn dOut ≃ₗ[ℝ] Params.Prod A dIn dOut :=
  { equivProd with
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

variable (θ η : Params A dIn dOut) (c : ℝ)

@[simp] theorem add_E : (θ + η).E = θ.E + η.E := rfl
@[simp] theorem add_read (ℓ : Fin L) : (θ + η).read ℓ = θ.read ℓ + η.read ℓ := rfl
@[simp] theorem add_write (ℓ : Fin L) : (θ + η).write ℓ = θ.write ℓ + η.write ℓ := rfl
@[simp] theorem add_D : (θ + η).D = θ.D + η.D := rfl
@[simp] theorem smul_E : (c • θ).E = c • θ.E := rfl
@[simp] theorem smul_read (ℓ : Fin L) : (c • θ).read ℓ = c • θ.read ℓ := rfl
@[simp] theorem smul_write (ℓ : Fin L) : (c • θ).write ℓ = c • θ.write ℓ := rfl
@[simp] theorem smul_D : (c • θ).D = c • θ.D := rfl
@[simp] theorem zero_E : (0 : Params A dIn dOut).E = 0 := rfl
@[simp] theorem zero_read (ℓ : Fin L) : (0 : Params A dIn dOut).read ℓ = 0 := rfl
@[simp] theorem zero_write (ℓ : Fin L) : (0 : Params A dIn dOut).write ℓ = 0 := rfl
@[simp] theorem zero_D : (0 : Params A dIn dOut).D = 0 := rfl
@[simp] theorem neg_E : (-θ).E = -θ.E := rfl
@[simp] theorem neg_read (ℓ : Fin L) : (-θ).read ℓ = -θ.read ℓ := rfl
@[simp] theorem neg_write (ℓ : Fin L) : (-θ).write ℓ = -θ.write ℓ := rfl
@[simp] theorem neg_D : (-θ).D = -θ.D := rfl

/-- Two parameters are equal if their four components are. -/
@[ext] theorem ext' {θ η : Params A dIn dOut} (hE : θ.E = η.E) (hr : ∀ ℓ, θ.read ℓ = η.read ℓ)
    (hw : ∀ ℓ, θ.write ℓ = η.write ℓ) (hD : θ.D = η.D) : θ = η := by
  cases θ; cases η; simp only [mk.injEq]
  exact ⟨hE, funext hr, funext hw, hD⟩

variable [Fintype d] [Fintype dIn] [Fintype dOut]

noncomputable instance : NormedAddCommGroup (Params A dIn dOut) :=
  NormedAddCommGroup.induced _ _ (linearEquivProd (A := A) (dIn := dIn) (dOut := dOut)).toLinearMap
    (linearEquivProd (A := A) (dIn := dIn) (dOut := dOut)).injective

noncomputable instance : NormedSpace ℝ (Params A dIn dOut) :=
  NormedSpace.induced ℝ _ _ (linearEquivProd (A := A) (dIn := dIn) (dOut := dOut)).toLinearMap

instance : FiniteDimensional ℝ (Params A dIn dOut) :=
  LinearEquiv.finiteDimensional (linearEquivProd (A := A) (dIn := dIn) (dOut := dOut)).symm

end Params

end Skips
