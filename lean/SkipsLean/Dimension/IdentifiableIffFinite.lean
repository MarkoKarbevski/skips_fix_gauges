import SkipsLean.Dimension.IdentifiableIffFamily
import SkipsLean.Symmetry.FiniteSymmetries

/-!
# The equality condition is local identifiability up to all the symmetries: networks without skip
    connections

Paper (dimension paper, Proposition 4.6; skips paper, Proposition 4.5): "A network satisfies the
equality condition if and only if, at generic parameters, it is locally identifiable up to its
symmetries." Definition 4.5 of the dimension paper (4.4 of the skips paper): "A network is
identifiable up to its symmetries at `θ` if every `θ′` with `F_{θ′} = F_θ` is the image of `θ`
under a symmetry: a change of basis […], a symmetry inside a block, or a composition of these. It
is locally identifiable at `θ` if this holds for every `θ′` in some neighborhood of `θ`." The
symmetries inside the blocks (dimension paper, Appendix B): "Permutations of hidden units or heads
and sign flips of tanh hidden units are finite and remove no parameters", and the continuous ones
(the rescalings of the values of gated units, the changes of basis inside the heads).

Here the equivalence in this form, for the kinds of block of the papers: every `θ'` near `θ` with
the same function is `θ` after a finite symmetry (`Symmetry/FiniteSymmetries.lean`: a permutation
of the hidden units, `Params.permUnits`, `Params.permUnitsGated`; sign flips, `Params.flipUnits`;
a permutation of the heads, `Params.permHeads`), a continuous symmetry inside the blocks and a
change of basis. A composition of symmetries in any order has this form: the changes of basis
commute with the symmetries inside the blocks, and the finite symmetries normalize the continuous
ones. The forms with the permutations alone are stated for every real-analytic activation (GELU,
and tanh); the forms with the sign flips are the paper's for an odd activation (tanh), where the
sign flips preserve the function (`eval_flipUnits`). As statements they hold for every
real-analytic activation.

Each statement is the case of the statement with `_family` of the same kind
(`Dimension/IdentifiableIffFamily.lean`) in which the maps `img j` are the finite
symmetries; the identity is the trivial permutation with the signs `1`.
-/

namespace Skips

open Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {sees : T → T → Prop} [DecidableRel sees]
variable {H dh hid : Fin L → Type} [∀ ℓ, Fintype (H ℓ)] [∀ ℓ, Fintype (dh ℓ)]
  [∀ ℓ, DecidableEq (dh ℓ)] [∀ ℓ, Fintype (hid ℓ)] {σ : ℝ → ℝ} {ε : ℝ}

/-- **Proposition 4.6 of the dimension paper and Proposition 4.5 of the skips paper, for skipless
networks of MLP blocks with a real-analytic activation (tanh, GELU), without normalization, with the
permutations of the hidden units:** `fd = P − (L + 1) d²` at almost every parameter if and only if
at almost every parameter `θ` every `θ'` near `θ` with the same function is `θ` after a permutation
of the hidden units of every block, a change of basis by invertible `G_0, …, G_L`. -/
theorem ae_funDim_mlp_skipless_iff_ae_locally_cob_perm
    (hσ : AnalyticOnNhd ℝ σ Set.univ)
    (μ : Measure (Params
      (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    (∀ᵐ θ ∂μ, funDim (Arch.mlp σ id hid) 0 θ
        + (L + 1) * Fintype.card d ^ 2
      = Module.finrank ℝ (Params
          (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)) ↔
    (∀ᵐ θ ∂μ, ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.mlp σ id hid) 0 θ' x
        = eval (Arch.mlp σ id hid) 0 θ x) →
        ∃ p : ∀ ℓ, Equiv.Perm (hid ℓ), ∃ G : Fin (L + 1) → GL d ℝ,
            θ' = (θ.permUnits p).cob G G) := by
  -- the case of the statement with countably many images: the permutations of the hidden units
  exact ae_funDim_mlp_skipless_iff_ae_locally_cob_family hσ μ hdIn hhid
    (fun (p : ∀ ℓ, Equiv.Perm (hid ℓ)) θ => θ.permUnits p) (fun _ => 1) permUnits_one

/-- **Proposition 4.6 of the dimension paper and Proposition 4.5 of the skips paper, for skipless
networks of MLP blocks with a real-analytic activation (tanh, GELU), without normalization, with the
permutations and the sign flips of the hidden units (the finite symmetries for an odd activation:
tanh; for an activation that is not odd, such as GELU, the images under the sign flips are not
symmetric, and the paper's form is the one with the permutations alone):** `fd = P − (L + 1) d²` at
almost every parameter if and only if at almost every parameter `θ` every `θ'` near `θ` with the
same function is `θ` after a permutation of the hidden units of every block, sign flips of hidden
units, a change of basis by invertible `G_0, …, G_L`. -/
theorem ae_funDim_mlp_skipless_iff_ae_locally_cob_perm_flip
    (hσ : AnalyticOnNhd ℝ σ Set.univ)
    (μ : Measure (Params
      (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    (∀ᵐ θ ∂μ, funDim (Arch.mlp σ id hid) 0 θ
        + (L + 1) * Fintype.card d ^ 2
      = Module.finrank ℝ (Params
          (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)) ↔
    (∀ᵐ θ ∂μ, ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.mlp σ id hid) 0 θ' x
        = eval (Arch.mlp σ id hid) 0 θ x) →
        ∃ (p : ∀ ℓ, Equiv.Perm (hid ℓ)) (s : ∀ ℓ, hid ℓ → ℤˣ), ∃ G : Fin (L + 1) → GL d ℝ,
            θ' = ((θ.permUnits p).flipUnits s).cob G G) := by
  -- the case of the statement with countably many images: the permutations and the sign flips
  -- of the hidden units, the trivial permutation with the signs `1` as the identity
  rw [ae_funDim_mlp_skipless_iff_ae_locally_cob_family hσ μ hdIn hhid
    (fun (j : (∀ ℓ, Equiv.Perm (hid ℓ)) × (∀ ℓ, hid ℓ → ℤˣ)) θ => (θ.permUnits j.1).flipUnits j.2)
    (fun _ => 1, fun _ _ => 1) (fun θ => by rw [permUnits_one, flipUnits_one])]
  -- the existential over the pairs `(p, s)` is the existential over `p` and `s`
  refine eventually_congr (Eventually.of_forall fun θ => ?_)
  refine exists_congr fun U => and_congr_right fun _ =>
    forall₂_congr fun θ' _ => imp_congr_right fun _ => ?_
  exact ⟨fun ⟨⟨p, s⟩, h⟩ => ⟨p, s, h⟩, fun ⟨p, s, h⟩ => ⟨(p, s), h⟩⟩

/-- **Proposition 4.6 of the dimension paper and Proposition 4.5 of the skips paper, for skipless
networks of MLP blocks with a real-analytic activation (tanh, GELU), under pre-RMSNorm with `ε > 0`,
with the permutations of the hidden units:** `fd = P − (L + 1) d(d−1)/2` at almost every parameter
if and only if at almost every parameter `θ` every `θ'` near `θ` with the same function is `θ` after
a permutation of the hidden units of every block, a change of basis by orthogonal `Q_0, …, Q_L`. -/
theorem ae_funDim_mlp_skipless_iff_ae_locally_cob_rmsNorm_perm
    (hε : 0 < ε) (hσ : AnalyticOnNhd ℝ σ Set.univ)
    (μ : Measure (Params
      (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    (∀ᵐ θ ∂μ, funDim (Arch.mlp σ (rmsNorm ε) hid) 0 θ
        + (L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2)
      = Module.finrank ℝ (Params
          (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)) ↔
    (∀ᵐ θ ∂μ, ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.mlp σ (rmsNorm ε) hid) 0 θ' x
        = eval (Arch.mlp σ (rmsNorm ε) hid) 0 θ x) →
        ∃ p : ∀ ℓ, Equiv.Perm (hid ℓ), ∃ Q : Fin (L + 1) → GL d ℝ,
            (∀ ℓ, (Q ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ) ∧
            θ' = (θ.permUnits p).cob Q Q) := by
  -- the case of the statement with countably many images: the permutations of the hidden units
  exact ae_funDim_mlp_skipless_iff_ae_locally_cob_rmsNorm_family hε hσ μ hdIn hhid
    (fun (p : ∀ ℓ, Equiv.Perm (hid ℓ)) θ => θ.permUnits p) (fun _ => 1) permUnits_one

/-- **Proposition 4.6 of the dimension paper and Proposition 4.5 of the skips paper, for skipless
networks of MLP blocks with a real-analytic activation (tanh, GELU), under pre-RMSNorm with `ε > 0`,
with the permutations and the sign flips of the hidden units (the finite symmetries for an odd
activation: tanh; for an activation that is not odd, such as GELU, the images under the sign flips
are not symmetric, and the paper's form is the one with the permutations alone):** `fd = P − (L + 1)
d(d−1)/2` at almost every parameter if and only if at almost every parameter `θ` every `θ'` near `θ`
with the same function is `θ` after a permutation of the hidden units of every block, sign flips of
hidden units, a change of basis by orthogonal `Q_0, …, Q_L`. -/
theorem ae_funDim_mlp_skipless_iff_ae_locally_cob_rmsNorm_perm_flip
    (hε : 0 < ε) (hσ : AnalyticOnNhd ℝ σ Set.univ)
    (μ : Measure (Params
      (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    (∀ᵐ θ ∂μ, funDim (Arch.mlp σ (rmsNorm ε) hid) 0 θ
        + (L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2)
      = Module.finrank ℝ (Params
          (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)) ↔
    (∀ᵐ θ ∂μ, ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.mlp σ (rmsNorm ε) hid) 0 θ' x
        = eval (Arch.mlp σ (rmsNorm ε) hid) 0 θ x) →
        ∃ (p : ∀ ℓ, Equiv.Perm (hid ℓ)) (s : ∀ ℓ, hid ℓ → ℤˣ), ∃ Q : Fin (L + 1) → GL d ℝ,
            (∀ ℓ, (Q ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ) ∧
            θ' = ((θ.permUnits p).flipUnits s).cob Q Q) := by
  -- the case of the statement with countably many images: the permutations and the sign flips
  -- of the hidden units, the trivial permutation with the signs `1` as the identity
  rw [ae_funDim_mlp_skipless_iff_ae_locally_cob_rmsNorm_family hε hσ μ hdIn hhid
    (fun (j : (∀ ℓ, Equiv.Perm (hid ℓ)) × (∀ ℓ, hid ℓ → ℤˣ)) θ => (θ.permUnits j.1).flipUnits j.2)
    (fun _ => 1, fun _ _ => 1) (fun θ => by rw [permUnits_one, flipUnits_one])]
  -- the existential over the pairs `(p, s)` is the existential over `p` and `s`
  refine eventually_congr (Eventually.of_forall fun θ => ?_)
  refine exists_congr fun U => and_congr_right fun _ =>
    forall₂_congr fun θ' _ => imp_congr_right fun _ => ?_
  exact ⟨fun ⟨⟨p, s⟩, h⟩ => ⟨p, s, h⟩, fun ⟨p, s, h⟩ => ⟨(p, s), h⟩⟩

/-- **Proposition 4.6 of the dimension paper and Proposition 4.5 of the skips paper, for skipless
networks of gated blocks with a real-analytic gate (SwiGLU, GeGLU), without normalization, with the
permutations of the hidden units:** `fd = P − (L + 1) d² − s` at almost every parameter (`s = ∑
d_hidden`) if and only if at almost every parameter `θ` every `θ'` near `θ` with the same function
is `θ` after a permutation of the hidden units of every block, a rescaling of the values of the
hidden units by nonzero factors `c` and a change of basis by invertible `G_0, …, G_L`. -/
theorem ae_funDim_gated_skipless_iff_ae_locally_cob_rescale_perm
    [Nonempty d] (hσ : AnalyticOnNhd ℝ σ Set.univ)
    (μ : Measure (Params
      (Arch.gated (T := T) (d := d) σ id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    (∀ᵐ θ ∂μ, funDim (Arch.gated σ id hid) 0 θ
        + ((L + 1) * Fintype.card d ^ 2
          + ∑ ℓ, Fintype.card (hid ℓ))
      = Module.finrank ℝ (Params
          (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)) ↔
    (∀ᵐ θ ∂μ, ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.gated σ id hid) 0 θ' x
        = eval (Arch.gated σ id hid) 0 θ x) →
        ∃ p : ∀ ℓ, Equiv.Perm (hid ℓ), ∃ c : ∀ ℓ, hid ℓ → ℝ, (∀ ℓ i, c ℓ i ≠ 0) ∧
          ∃ G : Fin (L + 1) → GL d ℝ,
            θ' = ((θ.permUnitsGated p).rescale c).cob G G) := by
  -- the case of the statement with countably many images: the permutations of the hidden units
  exact ae_funDim_gated_skipless_iff_ae_locally_cob_rescale_family hσ μ hdIn hhid
    (fun (p : ∀ ℓ, Equiv.Perm (hid ℓ)) θ => θ.permUnitsGated p) (fun _ => 1) permUnitsGated_one

/-- **Proposition 4.6 of the dimension paper and Proposition 4.5 of the skips paper, for skipless
networks of gated blocks with a real-analytic gate (SwiGLU, GeGLU), under pre-RMSNorm with `ε > 0`,
with the permutations of the hidden units:** `fd = P − (L + 1) d(d−1)/2 − s` at almost every
parameter (`s = ∑ d_hidden`) if and only if at almost every parameter `θ` every `θ'` near `θ` with
the same function is `θ` after a permutation of the hidden units of every block, a rescaling of the
values of the hidden units by nonzero factors `c` and a change of basis by orthogonal `Q_0, …, Q_L`.
-/
theorem ae_funDim_gated_skipless_iff_ae_locally_cob_rescale_rmsNorm_perm
    (hε : 0 < ε) [Nonempty d] (hσ : AnalyticOnNhd ℝ σ Set.univ)
    (μ : Measure (Params
      (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    (∀ᵐ θ ∂μ, funDim (Arch.gated σ (rmsNorm ε) hid) 0 θ
        + ((L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2)
          + ∑ ℓ, Fintype.card (hid ℓ))
      = Module.finrank ℝ (Params
          (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)) ↔
    (∀ᵐ θ ∂μ, ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.gated σ (rmsNorm ε) hid) 0 θ' x
        = eval (Arch.gated σ (rmsNorm ε) hid) 0 θ x) →
        ∃ p : ∀ ℓ, Equiv.Perm (hid ℓ), ∃ c : ∀ ℓ, hid ℓ → ℝ, (∀ ℓ i, c ℓ i ≠ 0) ∧
          ∃ Q : Fin (L + 1) → GL d ℝ,
            (∀ ℓ, (Q ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ) ∧
            θ' = ((θ.permUnitsGated p).rescale c).cob Q Q) := by
  -- the case of the statement with countably many images: the permutations of the hidden units
  exact ae_funDim_gated_skipless_iff_ae_locally_cob_rescale_rmsNorm_family hε hσ μ hdIn hhid
    (fun (p : ∀ ℓ, Equiv.Perm (hid ℓ)) θ => θ.permUnitsGated p) (fun _ => 1) permUnitsGated_one

/-- **Proposition 4.6 of the dimension paper and Proposition 4.5 of the skips paper, for skipless
networks of attention blocks, without normalization, with the permutations of the heads:** `fd = P −
(L + 1) d² − s` at almost every parameter (`s = 2 ∑ H d_h²`) if and only if at almost every
parameter `θ` every `θ'` near `θ` with the same function is `θ` after a permutation of the heads of
every block, changes of basis inside the heads and a change of basis by invertible `G_0, …, G_L`. -/
theorem ae_funDim_attention_skipless_iff_ae_locally_cob_heads_perm
    (μ : Measure (Params
      (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d)
    (hH : ∀ ℓ, Fintype.card d ≤ Fintype.card (H ℓ) * Fintype.card (dh ℓ)) :
    (∀ᵐ θ ∂μ, funDim (Arch.attention sees id H dh) 0 θ
        + ((L + 1) * Fintype.card d ^ 2
          + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
      = Module.finrank ℝ (Params
          (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut)) ↔
    (∀ᵐ θ ∂μ, ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.attention sees id H dh) 0 θ' x
        = eval (Arch.attention sees id H dh) 0 θ x) →
        ∃ q : ∀ ℓ, Equiv.Perm (H ℓ), ∃ K K' : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ,
          ∃ G : Fin (L + 1) → GL d ℝ,
            θ' = (((θ.permHeads q).headsQK K).headsVO K').cob G G) := by
  -- the case of the statement with countably many images: the permutations of the heads
  exact ae_funDim_attention_skipless_iff_ae_locally_cob_heads_family μ hdIn hdh hH
    (fun (q : ∀ ℓ, Equiv.Perm (H ℓ)) θ => θ.permHeads q) (fun _ => 1) permHeads_one

/-- **Proposition 4.6 of the dimension paper and Proposition 4.5 of the skips paper, for skipless
networks of attention blocks, under pre-RMSNorm with `ε > 0`, with the permutations of the heads:**
`fd = P − (L + 1) d(d−1)/2 − s` at almost every parameter (`s = 2 ∑ H d_h²`) if and only if at
almost every parameter `θ` every `θ'` near `θ` with the same function is `θ` after a permutation of
the heads of every block, changes of basis inside the heads and a change of basis by orthogonal
`Q_0, …, Q_L`. -/
theorem ae_funDim_attention_skipless_iff_ae_locally_cob_heads_rmsNorm_perm
    (hε : 0 < ε)
    (μ : Measure (Params
      (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d)
    (hH : ∀ ℓ, Fintype.card d ≤ Fintype.card (H ℓ) * Fintype.card (dh ℓ)) :
    (∀ᵐ θ ∂μ, funDim (Arch.attention sees (rmsNorm ε) H dh) 0 θ
        + ((L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2)
          + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
      = Module.finrank ℝ (Params
          (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut)) ↔
    (∀ᵐ θ ∂μ, ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.attention sees (rmsNorm ε) H dh) 0 θ' x
        = eval (Arch.attention sees (rmsNorm ε) H dh) 0 θ x) →
        ∃ q : ∀ ℓ, Equiv.Perm (H ℓ), ∃ K K' : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ,
          ∃ Q : Fin (L + 1) → GL d ℝ,
            (∀ ℓ, (Q ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ) ∧
            θ' = (((θ.permHeads q).headsQK K).headsVO K').cob Q Q) := by
  -- the case of the statement with countably many images: the permutations of the heads
  exact ae_funDim_attention_skipless_iff_ae_locally_cob_heads_rmsNorm_family hε μ hdIn hdh hH
    (fun (q : ∀ ℓ, Equiv.Perm (H ℓ)) θ => θ.permHeads q) (fun _ => 1) permHeads_one

end Skips
