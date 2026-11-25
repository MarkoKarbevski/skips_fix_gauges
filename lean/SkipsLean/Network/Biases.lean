import SkipsLean.Dimension.Space

/-!
# Networks with biases

Paper (skips paper), Lemma A.27: "With biases, `θ` also holds `b_E`, `b_read^ℓ`, `b_write^ℓ` and
`b_D`"; Appendix B, "Reduction": "With biases `b_E`, `b_read`, `b_write` and `b_D`, the skipless
network computes `F(θ, x) = f(xC + β)A + γ_0` and the residual network
`F(θ, x) = xM + f(xC + β)A + γ`, where `M = ED`, `C = E W_read`, `A = W_write D`,
`β = b_E W_read + b_read`, `γ_0 = b_write D + b_D`, `γ = b_E D + γ_0`."

So the biases are rows, added to every token: `h_0 = x E + b_E`, block `ℓ` maps a hidden state `h`
to `f_ℓ(χ(h) W_read^ℓ + b_read^ℓ) W_write^ℓ + b_write^ℓ`, and `y = χ(h_L) D + b_D`.

Here:

* `Biases A dOut`: the tuple `(b_E, (b_read^ℓ)_ℓ, (b_write^ℓ)_ℓ, b_D)`, a real vector space with
  the norm of the product of its components (as `Params`, `Dimension/Space.lean`). The parameters
  of a network with biases are a pair `(θ, b)` of `Params A dIn dOut × Biases A dOut`.
* `hiddenB`, `evalB`: the hidden states and the function of the network with biases, with stream
  matrices `M` as in `hidden` and `eval` (`Network/Defs.lean`).
* `hiddenB_zero`, `hiddenB_succ`; with all biases zero the network is the network without biases
  (`hiddenB_zero_biases`, `evalB_zero_biases`).
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ}

/-- **The biases of a network:** `b_E` on the embedding, `b_read^ℓ` and `b_write^ℓ` on the read
and the write of block `ℓ`, `b_D` on the readout. Each is a row, added to every token. -/
structure Biases (A : Arch T d L) (dOut : Type*) where
  /-- the bias of the embedding -/
  E : d → ℝ
  /-- the read bias of block `ℓ` -/
  read : ∀ ℓ, A.r ℓ → ℝ
  /-- the write bias of block `ℓ` -/
  write : Fin L → d → ℝ
  /-- the bias of the readout -/
  D : dOut → ℝ

variable {A : Arch T d L}

namespace Biases

/-- The product of the four components of the biases. -/
abbrev Prod (A : Arch T d L) (dOut : Type*) : Type _ :=
  (d → ℝ) × (∀ ℓ, A.r ℓ → ℝ) × (Fin L → d → ℝ) × (dOut → ℝ)

/-- The biases are the tuples of their four components. -/
def equivProd : Biases A dOut ≃ Biases.Prod A dOut where
  toFun b := (b.E, b.read, b.write, b.D)
  invFun p := ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Zero (Biases A dOut) := ⟨⟨0, fun _ => 0, fun _ => 0, 0⟩⟩

instance : Add (Biases A dOut) :=
  ⟨fun b c => ⟨b.E + c.E, fun ℓ => b.read ℓ + c.read ℓ, fun ℓ => b.write ℓ + c.write ℓ,
    b.D + c.D⟩⟩

instance : Neg (Biases A dOut) :=
  ⟨fun b => ⟨-b.E, fun ℓ => -b.read ℓ, fun ℓ => -b.write ℓ, -b.D⟩⟩

instance : Sub (Biases A dOut) :=
  ⟨fun b c => ⟨b.E - c.E, fun ℓ => b.read ℓ - c.read ℓ, fun ℓ => b.write ℓ - c.write ℓ,
    b.D - c.D⟩⟩

instance {R : Type*} [SMul R ℝ] : SMul R (Biases A dOut) :=
  ⟨fun c b => ⟨c • b.E, fun ℓ => c • b.read ℓ, fun ℓ => c • b.write ℓ, c • b.D⟩⟩

instance : AddCommGroup (Biases A dOut) :=
  Function.Injective.addCommGroup equivProd equivProd.injective rfl (fun _ _ => rfl)
    (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

/-- The map to the tuple of components, as an additive map. -/
def addHomProd : Biases A dOut →+ Biases.Prod A dOut where
  toFun := equivProd
  map_zero' := rfl
  map_add' _ _ := rfl

instance : Module ℝ (Biases A dOut) :=
  Function.Injective.module ℝ addHomProd equivProd.injective (fun _ _ => rfl)

/-- The biases and the tuples of their components, as vector spaces. -/
def linearEquivProd : Biases A dOut ≃ₗ[ℝ] Biases.Prod A dOut :=
  { equivProd with
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

variable (b c : Biases A dOut) (r : ℝ)

@[simp] theorem add_E : (b + c).E = b.E + c.E := rfl
@[simp] theorem add_read (ℓ : Fin L) : (b + c).read ℓ = b.read ℓ + c.read ℓ := rfl
@[simp] theorem add_write (ℓ : Fin L) : (b + c).write ℓ = b.write ℓ + c.write ℓ := rfl
@[simp] theorem add_D : (b + c).D = b.D + c.D := rfl
@[simp] theorem smul_E : (r • b).E = r • b.E := rfl
@[simp] theorem smul_read (ℓ : Fin L) : (r • b).read ℓ = r • b.read ℓ := rfl
@[simp] theorem smul_write (ℓ : Fin L) : (r • b).write ℓ = r • b.write ℓ := rfl
@[simp] theorem smul_D : (r • b).D = r • b.D := rfl
@[simp] theorem zero_E : (0 : Biases A dOut).E = 0 := rfl
@[simp] theorem zero_read (ℓ : Fin L) : (0 : Biases A dOut).read ℓ = 0 := rfl
@[simp] theorem zero_write (ℓ : Fin L) : (0 : Biases A dOut).write ℓ = 0 := rfl
@[simp] theorem zero_D : (0 : Biases A dOut).D = 0 := rfl
@[simp] theorem neg_E : (-b).E = -b.E := rfl
@[simp] theorem neg_read (ℓ : Fin L) : (-b).read ℓ = -b.read ℓ := rfl
@[simp] theorem neg_write (ℓ : Fin L) : (-b).write ℓ = -b.write ℓ := rfl
@[simp] theorem neg_D : (-b).D = -b.D := rfl

/-- Two tuples of biases are equal if their four components are. -/
@[ext] theorem ext' {b c : Biases A dOut} (hE : b.E = c.E) (hr : ∀ ℓ, b.read ℓ = c.read ℓ)
    (hw : ∀ ℓ, b.write ℓ = c.write ℓ) (hD : b.D = c.D) : b = c := by
  cases b; cases c; simp only [mk.injEq]
  exact ⟨hE, funext hr, funext hw, hD⟩

variable [Fintype d] [Fintype dOut]

noncomputable instance : NormedAddCommGroup (Biases A dOut) :=
  NormedAddCommGroup.induced _ _ (linearEquivProd (A := A) (dOut := dOut)).toLinearMap
    (linearEquivProd (A := A) (dOut := dOut)).injective

noncomputable instance : NormedSpace ℝ (Biases A dOut) :=
  NormedSpace.induced ℝ _ _ (linearEquivProd (A := A) (dOut := dOut)).toLinearMap

instance : FiniteDimensional ℝ (Biases A dOut) :=
  LinearEquiv.finiteDimensional (linearEquivProd (A := A) (dOut := dOut)).symm

end Biases

variable [Fintype d] [Fintype dIn] (A : Arch T d L)

/-- **The hidden states of the network with biases:** `h_0 = x E + b_E` and
`h_ℓ = h_{ℓ-1} M_ℓ + f_ℓ (χ(h_{ℓ-1}) W_read^ℓ + b_read^ℓ) W_write^ℓ + b_write^ℓ`, every bias
added to every token. -/
def hiddenB (M : Fin L → Matrix d d ℝ) (θ : Params A dIn dOut) (b : Biases A dOut)
    (x : Matrix T dIn ℝ) : Fin (L + 1) → Matrix T d ℝ :=
  Fin.induction (motive := fun _ => Matrix T d ℝ) (x * θ.E + Matrix.of fun _ => b.E)
    (fun ℓ h => h * M ℓ
      + (A.f ℓ (A.χ h * θ.read ℓ + Matrix.of fun _ => b.read ℓ) * θ.write ℓ
        + Matrix.of fun _ => b.write ℓ))

/-- **The function of the network with biases:** `y = χ(h_L) D + b_D`. -/
def evalB (M : Fin L → Matrix d d ℝ) (θ : Params A dIn dOut) (b : Biases A dOut)
    (x : Matrix T dIn ℝ) : Matrix T dOut ℝ :=
  A.χ (hiddenB A M θ b x (Fin.last L)) * θ.D + Matrix.of fun _ => b.D

@[simp] theorem hiddenB_zero (M : Fin L → Matrix d d ℝ) (θ : Params A dIn dOut)
    (b : Biases A dOut) (x : Matrix T dIn ℝ) :
    hiddenB A M θ b x 0 = x * θ.E + Matrix.of fun _ => b.E := by
  simp [hiddenB]

@[simp] theorem hiddenB_succ (M : Fin L → Matrix d d ℝ) (θ : Params A dIn dOut)
    (b : Biases A dOut) (x : Matrix T dIn ℝ) (ℓ : Fin L) :
    hiddenB A M θ b x ℓ.succ =
      hiddenB A M θ b x ℓ.castSucc * M ℓ +
        (A.f ℓ (A.χ (hiddenB A M θ b x ℓ.castSucc) * θ.read ℓ + Matrix.of fun _ => b.read ℓ)
            * θ.write ℓ
          + Matrix.of fun _ => b.write ℓ) := by
  simp [hiddenB]

omit [Fintype d] [Fintype dIn] in
/-- Helper: the matrix whose rows are all the zero row is the zero matrix. -/
private theorem of_zero_row_bia (n : Type*) :
    (Matrix.of fun (_ : T) => (0 : n → ℝ)) = 0 := rfl

/-- With all biases zero, the hidden states are those of the network without biases. -/
theorem hiddenB_zero_biases (M : Fin L → Matrix d d ℝ) (θ : Params A dIn dOut)
    (x : Matrix T dIn ℝ) (k : Fin (L + 1)) :
    hiddenB A M θ (0 : Biases A dOut) x k = hidden A M θ x k := by
  induction k using Fin.induction with
  | zero =>
    rw [hiddenB_zero, hidden_zero]
    show x * θ.E + (Matrix.of fun (_ : T) => (0 : d → ℝ)) = x * θ.E
    rw [of_zero_row_bia, add_zero]
  | succ ℓ ih =>
    rw [hiddenB_succ, hidden_succ, ih]
    show _ + (A.f ℓ (_ + (Matrix.of fun (_ : T) => (0 : A.r ℓ → ℝ))) * θ.write ℓ
      + (Matrix.of fun (_ : T) => (0 : d → ℝ))) = _
    rw [of_zero_row_bia, of_zero_row_bia, add_zero, add_zero]

/-- **With all biases zero, the network with biases is the network without biases.** -/
theorem evalB_zero_biases (M : Fin L → Matrix d d ℝ) (θ : Params A dIn dOut)
    (x : Matrix T dIn ℝ) :
    evalB A M θ (0 : Biases A dOut) x = eval A M θ x := by
  rw [evalB, eval, hiddenB_zero_biases]
  show _ + (Matrix.of fun (_ : T) => (0 : dOut → ℝ)) = _
  rw [of_zero_row_bia, add_zero]

end Skips
