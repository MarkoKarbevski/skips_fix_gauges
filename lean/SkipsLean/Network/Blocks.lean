import SkipsLean.Network.Defs

/-!
# Kinds of block

Papers: Section 2, "Blocks". An MLP block with `d_hidden` hidden units has a `d × d_hidden` read
and a `d_hidden × d` write, and its fixed map applies an activation to every hidden unit of every
token.
-/

namespace Skips

open Matrix

variable {T d : Type*} {L : ℕ}

/-- A network of MLP blocks with the activation `σ`: block `ℓ` has the hidden units `hid ℓ`, and
its fixed map applies `σ` to every hidden unit of every token. The map `χ` is the identity or a
normalization. -/
abbrev Arch.mlp (σ : ℝ → ℝ) (χ : Matrix T d ℝ → Matrix T d ℝ) (hid : Fin L → Type)
    [∀ ℓ, Fintype (hid ℓ)] : Arch T d L where
  r := hid
  w := hid
  f _ M := M.map σ
  χ := χ

/-- A network of gated blocks with the gate activation `σ` (SiLU for SwiGLU, GELU for GeGLU, ReLU
for ReGLU): block `ℓ` has the hidden units `hid ℓ`, its read is `[W_g | W_v]`, with one gate column
(`Sum.inl i`) and one value column (`Sum.inr i`) per hidden unit `i`, and its fixed map sends the
gate `z_i` and the value `w_i` of a token to `σ(z_i) w_i`. -/
abbrev Arch.gated (σ : ℝ → ℝ) (χ : Matrix T d ℝ → Matrix T d ℝ) (hid : Fin L → Type)
    [∀ ℓ, Fintype (hid ℓ)] : Arch T d L where
  r ℓ := hid ℓ ⊕ hid ℓ
  w := hid
  f _ M := Matrix.of fun t i => σ (M t (Sum.inl i)) * M t (Sum.inr i)
  χ := χ

end Skips
