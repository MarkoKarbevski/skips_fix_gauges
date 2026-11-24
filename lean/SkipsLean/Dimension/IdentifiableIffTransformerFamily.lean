import SkipsLean.Dimension.IdentifiableIffTransformer
import SkipsLean.Dimension.IdentifiableConverseFamily

/-!
# The equality condition is local identifiability, with permutations and sign flips: skipless
    networks of attention blocks and MLP or gated blocks

Paper (dimension paper, Proposition 4.6; skips paper, Proposition 4.5): "A network satisfies the
equality condition if and only if, at generic parameters, it is locally identifiable up to its
symmetries." Definition 4.5 of the dimension paper (4.4 of the skips paper): "A network is
identifiable up to its symmetries at `θ` if every `θ′` with `F_{θ′} = F_θ` is the image of `θ`
under a symmetry: a change of basis […], a symmetry inside a block, or a composition of these."
The symmetries inside the blocks (dimension paper, Appendix B): "Permutations of hidden units or
heads and sign flips of tanh hidden units are finite and remove no parameters", beside the
continuous ones (rescalings, changes of basis inside the heads). The proof of the converse counts
them: "With the permutations and the sign flips, the symmetries form a Lie group of dimension `k`
with finitely many components".

`Dimension/IdentifiableIffTransformer.lean` states the equivalence with the continuous symmetries
    only. Here
the same statements with countably many further images `img j θ` of `θ`, one of which is `θ`
itself: every `θ'` near `θ` with the same function is, for some `j`, the image of `img j θ` under
the continuous symmetries. With `img j` running over the compositions of the permutations of
hidden units or heads and the sign flips of tanh units (finitely many linear maps of the
parameters, which normalize the continuous symmetries inside the blocks and commute with the
changes of basis) the right side is local identifiability up to all the symmetries of the papers.
The statements hold for any countably many maps `img j` of the parameters: they need not be
symmetries, linear or continuous.

The direction from the equality condition to local identifiability is the earlier statement (the
identity is among the `img j`); the other direction is
`Dimension/IdentifiableConverseFamily.lean` with the upper bounds of Theorem 4.3 (dimension
paper) and Theorem 4.2 (skips paper).
-/

namespace Skips

open Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {sees : T → T → Prop} [DecidableRel sees]
variable {H dh hid : Fin L → Type} [∀ ℓ, Fintype (H ℓ)] [∀ ℓ, Fintype (dh ℓ)]
  [∀ ℓ, DecidableEq (dh ℓ)] [∀ ℓ, Fintype (hid ℓ)] {σ σ' : ℝ → ℝ} {ε : ℝ}

omit [Fintype T] [DecidableEq d] [Fintype d] [Fintype dIn] [Fintype dOut] in
/-- Helper (the private `sumOfLin_lit` of `Residual/LocalIdentifiabilityTransformer.lean`, as
`sumOfLin_iffr` of `Residual/IdentifiableIff.lean`): `(a, b) ↦ Params.sumOf a b` is linear. -/
private noncomputable def sumOfLin_iff1 {A B : Arch T d L} :
    (Params A dIn dOut × Params B dIn dOut) →ₗ[ℝ] Params (A.sum B) dIn dOut where
  toFun p := Params.sumOf p.1 p.2
  map_add' p q := by
    refine Params.ext' rfl (fun ℓ => ?_) (fun ℓ => ?_) rfl
    · ext k j
      rcases j with j | j <;> rfl
    · ext j k
      rcases j with j | j <;> rfl
  map_smul' c p := by
    refine Params.ext' rfl (fun ℓ => ?_) (fun ℓ => ?_) rfl
    · ext k j
      rcases j with j | j <;> rfl
    · ext j k
      rcases j with j | j <;> rfl

omit [∀ ℓ, DecidableEq (dh ℓ)] in
/-- Helper (the private `finrank_headFun_lit`): the families `Γ` of `d_h × d_h` matrices, one for
each head of each block, form a space of dimension `∑_ℓ H_ℓ d_{h,ℓ}²`. -/
private theorem finrank_headFun_iff1 :
    Module.finrank ℝ (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)
      = ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2 := by
  rw [Module.finrank_pi_fintype]
  simp only [Module.finrank_pi_fintype, Module.finrank_matrix, Module.finrank_self, mul_one,
    Finset.sum_const, Finset.card_univ, smul_eq_mul, sq]

omit [Fintype T] [DecidableEq d] in
/-- Helper (the private `contDiffOn_params_iffr` of `Residual/IdentifiableIff.lean`): a family of
parameters is of class `C¹` on a set if every entry of its four components is. -/
private theorem contDiffOn_params_iff1 {A : Arch T d L} {N : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] {f : N → Params A dIn dOut} {Ω : Set N}
    (hE : ∀ i j, ContDiffOn ℝ 1 (fun n => (f n).E i j) Ω)
    (hr : ∀ ℓ k j, ContDiffOn ℝ 1 (fun n => (f n).read ℓ k j) Ω)
    (hw : ∀ ℓ j k, ContDiffOn ℝ 1 (fun n => (f n).write ℓ j k) Ω)
    (hD : ∀ k j, ContDiffOn ℝ 1 (fun n => (f n).D k j) Ω) :
    ContDiffOn ℝ 1 f Ω := by
  let e := (Params.linearEquivProd (A := A) (dIn := dIn) (dOut := dOut)).toContinuousLinearEquiv
  rw [← e.comp_contDiffOn_iff]
  -- the four components, entry by entry
  have h : ContDiffOn ℝ 1 (fun n => ((f n).E, (f n).read, (f n).write, (f n).D)) Ω :=
    (contDiffOn_pi' fun i => contDiffOn_pi' fun j => hE i j).prodMk
      ((contDiffOn_pi' fun ℓ => contDiffOn_pi' fun k => contDiffOn_pi' fun j => hr ℓ k j).prodMk
        ((contDiffOn_pi' fun ℓ => contDiffOn_pi' fun j => contDiffOn_pi' fun k =>
          hw ℓ j k).prodMk (contDiffOn_pi' fun k => contDiffOn_pi' fun j => hD k j)))
  exact h

omit [Fintype T] [DecidableEq d] in
/-- Helper (the private `contDiffOn_sumOf_iffr`): the parameters of the sum, made of two families
of class `C¹`, are of class `C¹` (`Params.sumOf` is linear). -/
private theorem contDiffOn_sumOf_iff1 {A B : Arch T d L} {N : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] {fa : N → Params A dIn dOut} {fb : N → Params B dIn dOut} {Ω : Set N}
    (ha : ContDiffOn ℝ 1 fa Ω) (hb : ContDiffOn ℝ 1 fb Ω) :
    ContDiffOn ℝ 1 (fun n => Params.sumOf (fa n) (fb n)) Ω := by
  have h := (LinearMap.toContinuousLinearMap
    (sumOfLin_iff1 (A := A) (B := B) (dIn := dIn) (dOut := dOut))).contDiff.comp_contDiffOn
      (ha.prodMk hb)
  exact h

/-- Helper (the private `finrank_hidFun_iffr`): the space of the factors of the rescalings has
dimension `∑ d_hidden`. -/
private theorem finrank_hidFun_iff1 :
    Module.finrank ℝ (∀ ℓ, hid ℓ → ℝ) = ∑ ℓ, Fintype.card (hid ℓ) := by
  rw [Module.finrank_pi_fintype]
  simp only [Module.finrank_fintype_fun_eq_card]

omit [Fintype T] [DecidableEq d] in
/-- Helper (the private `contDiffOn_rescale_iffr`): the rescalings `c ↦ θ.rescale c` are of class
`C¹` where no factor vanishes. -/
private theorem contDiffOn_rescale_iff1 {χ : Matrix T d ℝ → Matrix T d ℝ}
    (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut) :
    ContDiffOn ℝ 1 (fun c => θ.rescale c) {c : ∀ ℓ, hid ℓ → ℝ | ∀ ℓ i, c ℓ i ≠ 0} := by
  refine contDiffOn_params_iff1 (fun i j => contDiffOn_const (c := θ.E i j)) (fun ℓ k j => ?_)
    (fun ℓ i k => ?_) (fun k j => contDiffOn_const (c := θ.D k j))
  · rcases j with i | i
    · -- the gate columns do not change
      exact contDiffOn_const (c := θ.read ℓ k (Sum.inl i))
    · -- the value columns are divided by `c_{ℓ i}`, which does not vanish on the set
      have hc : ContDiff ℝ 1 fun c : (∀ ℓ, hid ℓ → ℝ) => c ℓ i := by fun_prop
      exact (hc.contDiffOn.inv fun c (hc0 : ∀ ℓ i, c ℓ i ≠ 0) => hc0 ℓ i).mul contDiffOn_const
  · -- the output rows are multiplied by `c_{ℓ i}`
    have hc : ContDiff ℝ 1 fun c : (∀ ℓ, hid ℓ → ℝ) => c ℓ i := by fun_prop
    exact (hc.mul contDiff_const).contDiffOn

/-- Helper (the private `contDiff_det_iffr`): the determinant of a matrix whose entries are `C¹`
is `C¹`. -/
private theorem contDiff_det_iff1 {m X : Type*} [Fintype m] [DecidableEq m] [NormedAddCommGroup X]
    [NormedSpace ℝ X] {g : X → Matrix m m ℝ} (hg : ∀ a b, ContDiff ℝ 1 fun x => g x a b) :
    ContDiff ℝ 1 fun x => (g x).det := by
  simp only [Matrix.det_apply']
  exact ContDiff.sum fun τ _ => contDiff_const.mul (contDiff_prod fun i _ => hg (τ i) i)

/-- Helper (the private `contDiffOn_inv_entry_iffr`): the entries of the inverse of a matrix whose
entries are `C¹` are `C¹` where the matrix is invertible (`A⁻¹ = det(A)⁻¹ adj(A)`). -/
private theorem contDiffOn_inv_entry_iff1 {m X : Type*} [Fintype m] [DecidableEq m]
    [NormedAddCommGroup X] [NormedSpace ℝ X] {g : X → Matrix m m ℝ}
    (hg : ∀ a b, ContDiff ℝ 1 fun x => g x a b) {s : Set X} (hs : ∀ x ∈ s, IsUnit (g x))
    (a b : m) : ContDiffOn ℝ 1 (fun x => (g x)⁻¹ a b) s := by
  have h1 : (fun x => (g x)⁻¹ a b)
      = fun x => ((g x).det)⁻¹ * ((g x).updateRow b (Pi.single a 1)).det := by
    funext x
    rw [Matrix.inv_def, Matrix.smul_apply, Matrix.adjugate_apply, Ring.inverse_eq_inv, smul_eq_mul]
  rw [h1]
  have hdet : ContDiff ℝ 1 fun x => (g x).det := contDiff_det_iff1 hg
  -- the matrix of the adjugate entry: row `b` replaced by the unit row `a`
  have hadj : ContDiff ℝ 1 fun x => ((g x).updateRow b (Pi.single a 1)).det := by
    refine contDiff_det_iff1 fun i j => ?_
    rcases eq_or_ne i b with rfl | h
    · simp only [Matrix.updateRow_self]
      exact contDiff_const
    · simp only [Matrix.updateRow_ne h]
      exact hg i j
  exact (hdet.contDiffOn.inv fun x hx =>
    ((Matrix.isUnit_iff_isUnit_det _).1 (hs x hx)).ne_zero).mul hadj.contDiffOn

omit [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] [∀ ℓ, DecidableEq (dh ℓ)] in
/-- Helper (the private `headsMat_iffr`): the parameters `(θ.headsQK K).headsVO K'` written with
the matrices `K`, `K'` and, as separate arguments, their inverses `Ki`, `K'i`. -/
private noncomputable def headsMat_iff1 {χ : Matrix T d ℝ → Matrix T d ℝ}
    (θ : Params (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut)
    (K Ki K' K'i : ∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) :
    Params (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut where
  E := θ.E
  read ℓ := Matrix.of fun a p =>
    match p.2 with
    | Sum.inl k => ∑ k', θ.read ℓ a (p.1, Sum.inl k') * K ℓ p.1 k' k
    | Sum.inr (Sum.inl k) => ∑ k', θ.read ℓ a (p.1, Sum.inr (Sum.inl k')) * Ki ℓ p.1 k k'
    | Sum.inr (Sum.inr k) => ∑ k', θ.read ℓ a (p.1, Sum.inr (Sum.inr k')) * K' ℓ p.1 k' k
  write ℓ := Matrix.of fun (p : H ℓ × dh ℓ) b => ∑ k', K'i ℓ p.1 p.2 k' * θ.write ℓ (p.1, k') b
  D := θ.D

omit [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] [∀ ℓ, DecidableEq (dh ℓ)] in
/-- Helper (the private `headsFam_iffr`): the family of the changes of basis inside the heads, at
the pairs `n = (k, k')` of families of matrices, with the matrix inverses of `k`, `k'`. -/
private noncomputable def headsFam_iff1 {χ : Matrix T d ℝ → Matrix T d ℝ}
    (θ : Params (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut)
    (n : (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)) :
    Params (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut :=
  headsMat_iff1 θ n.1 (fun ℓ i => (n.1 ℓ i)⁻¹) n.2 (fun ℓ i => (n.2 ℓ i)⁻¹)

omit [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (the private `headsFam_coe_iffr`): at the invertible matrices of `K`, `K'`, the family
is `(θ.headsQK K).headsVO K'`. -/
private theorem headsFam_coe_iff1 {χ : Matrix T d ℝ → Matrix T d ℝ}
    (θ : Params (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut)
    (K K' : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ) :
    headsFam_iff1 θ (fun ℓ i => (K ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ),
      fun ℓ i => (K' ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)) = (θ.headsQK K).headsVO K' := by
  -- the matrix inverse of `K` is the matrix of `K⁻¹`
  simp only [headsFam_iff1, ← Matrix.coe_units_inv]
  refine Params.ext' rfl (fun ℓ => ?_) (fun ℓ => rfl) rfl
  ext a p
  rcases p with ⟨i, k | k | k⟩ <;> rfl

omit [DecidableEq d] in
/-- Helper (the private `contDiffOn_headsFam_iffr`): the family of the changes of basis inside the
heads is `C¹` where the matrices are invertible. -/
private theorem contDiffOn_headsFam_iff1 {χ : Matrix T d ℝ → Matrix T d ℝ}
    (θ : Params (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut) :
    ContDiffOn ℝ 1 (headsFam_iff1 θ)
      {n | ∀ ℓ i, IsUnit (n.1 ℓ i) ∧ IsUnit (n.2 ℓ i)} := by
  refine contDiffOn_params_iff1 (fun i j => contDiffOn_const (c := θ.E i j)) (fun ℓ a p => ?_)
    (fun ℓ p b => ?_) (fun k j => contDiffOn_const (c := θ.D k j))
  · rcases p with ⟨i, k | k | k⟩
    · -- the query columns `W_Q k`
      have hk : ∀ k', ContDiff ℝ 1 fun n : (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)
          × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) => n.1 ℓ i k' k := fun k' => by fun_prop
      exact (ContDiff.sum fun k' _ => contDiff_const.mul (hk k')).contDiffOn
    · -- the key columns `W_K (k⁻¹)ᵀ`
      exact ContDiffOn.sum fun k' _ => contDiffOn_const.mul
        (contDiffOn_inv_entry_iff1 (g := fun n : (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)
          × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) => n.1 ℓ i) (fun _ _ => by fun_prop)
          (fun n (hn : ∀ ℓ i, IsUnit (n.1 ℓ i) ∧ IsUnit (n.2 ℓ i)) => (hn ℓ i).1) k k')
    · -- the value columns `W_V k'`
      have hk : ∀ k', ContDiff ℝ 1 fun n : (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)
          × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) => n.2 ℓ i k' k := fun k' => by fun_prop
      exact (ContDiff.sum fun k' _ => contDiff_const.mul (hk k')).contDiffOn
  · -- the output rows `k'⁻¹ W_O`
    rcases p with ⟨i, k⟩
    exact ContDiffOn.sum fun k' _ => ContDiffOn.mul
      (contDiffOn_inv_entry_iff1 (g := fun n : (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)
        × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) => n.2 ℓ i) (fun _ _ => by fun_prop)
        (fun n (hn : ∀ ℓ i, IsUnit (n.1 ℓ i) ∧ IsUnit (n.2 ℓ i)) => (hn ℓ i).2) k k')
      contDiffOn_const

/-- **Proposition 4.5 of the skips paper, for skipless networks of attention blocks and MLP blocks
with a real-analytic activation, in any order, without normalization, with countably many further
images of `θ`:** `fd = P − (L + 1) d² − s` at almost every parameter (`s = 2 ∑ H d_h²`) if and only
if at almost every parameter `θ` every `θ'` near `θ` with the same function is, for some `j`, the
image `img j θ` of `θ` after changes of basis inside the heads and a change of basis by invertible
`G_0, …, G_L`. The maps `img j` are any countably many maps of the parameters, one of them the
identity; the permutations of hidden units or heads and the sign flips of tanh units, composed, are
finitely many such maps. -/
theorem ae_funDim_attentionMlp_skipless_iff_ae_locally_cob_heads_family
    (hσ : AnalyticOnNhd ℝ σ Set.univ)
    (μ : Measure (Params
      (Arch.attentionMlp (T := T) (d := d) sees σ id H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d)
    (hW : ∀ ℓ,
      Fintype.card d ≤ Fintype.card (H ℓ) * Fintype.card (dh ℓ) + Fintype.card (hid ℓ))
    {ι : Type*} [Countable ι]
    (img : ι → Params (Arch.attentionMlp (T := T) (d := d) sees σ id H dh hid) dIn dOut →
      Params (Arch.attentionMlp (T := T) (d := d) sees σ id H dh hid) dIn dOut)
    (j₀ : ι) (himg : ∀ θ, img j₀ θ = θ) :
    (∀ᵐ θ ∂μ, funDim (Arch.attentionMlp sees σ id H dh hid) 0 θ
        + ((L + 1) * Fintype.card d ^ 2
          + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
      = Module.finrank ℝ (Params
          (Arch.attentionMlp (T := T) (d := d) sees σ id H dh hid) dIn dOut)) ↔
    (∀ᵐ θ ∂μ, ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.attentionMlp sees σ id H dh hid) 0 θ' x
        = eval (Arch.attentionMlp sees σ id H dh hid) 0 θ x) →
        ∃ j : ι, ∃ K K' : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ,
          ∃ G : Fin (L + 1) → GL d ℝ,
            θ' = (Params.sumOf (((img j θ).sumFst.headsQK K).headsVO K') (img j θ).sumSnd).cob G
                G) := by
  constructor
  · -- the equality condition gives local identifiability up to the continuous symmetries (the
    -- statement without further images), and the identity `img j₀` is among the images
    intro h
    filter_upwards [(ae_funDim_attentionMlp_skipless_iff_ae_locally_cob_heads hσ μ hdIn hdh hW).1 h]
      with θ ⟨U, hU, hUV⟩
    refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
    obtain ⟨K, K', G, hG⟩ := hUV θ' hθ' heq
    exact ⟨j₀, K, K', G, by rw [himg]; exact hG⟩
  · -- local identifiability gives the lower bound from the families
    -- `Ψ θ j n = sumOf (headsFam_iff1 (img j θ).sumFst n) (img j θ).sumSnd` of the changes of
    -- basis inside the heads of the attention part of `img j θ`, and the upper bound of
    -- Theorem 4.2
    intro h
    have hlow := ae_finrank_le_funDim_add_of_ae_locally_cob_family
      (Arch.attentionMlp (T := T) (d := d) sees σ id H dh hid) 0
      (fun ℓ => analyticOnNhd_f_sum (analyticOnNhd_f_attention sees id H dh ℓ)
        (analyticOnNhd_f_mlp hσ ℓ)) analyticOnNhd_id μ
      (fun θ j n => Params.sumOf (headsFam_iff1 (img j θ).sumFst n) (img j θ).sumSnd)
      (fun _ => {n | ∀ ℓ i, IsUnit (n.1 ℓ i) ∧ IsUnit (n.2 ℓ i)})
      (fun θ j => contDiffOn_sumOf_iff1 (contDiffOn_headsFam_iff1 (img j θ).sumFst)
        contDiffOn_const) (by
        filter_upwards [h] with θ ⟨U, hU, hUV⟩
        refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
        obtain ⟨j, K, K', G, hG⟩ := hUV θ' hθ' heq
        refine ⟨j, (fun ℓ i => (K ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ),
          fun ℓ i => (K' ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)),
          fun ℓ i => ⟨(K ℓ i).isUnit, (K' ℓ i).isUnit⟩, G, ?_⟩
        rw [headsFam_coe_iff1]
        exact hG)
    have hup := ae_funDim_add_le_skipless_attentionMlp μ hdIn hdh hW
    filter_upwards [hlow, hup] with θ h1 h2
    rw [Module.finrank_prod, finrank_headFun_iff1] at h1
    generalize ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2 = s at h1 h2 ⊢
    generalize (L + 1) * Fintype.card d ^ 2 = a at h1 h2 ⊢
    omega

/-- **Proposition 4.5 of the skips paper, for skipless networks of attention blocks and MLP blocks
with a real-analytic activation, in any order, under pre-RMSNorm with `ε > 0`, with countably many
further images of `θ`:** `fd = P − (L + 1) d(d−1)/2 − s` at almost every parameter (`s = 2 ∑ H
d_h²`) if and only if at almost every parameter `θ` every `θ'` near `θ` with the same function is,
for some `j`, the image `img j θ` of `θ` after changes of basis inside the heads and a change of
basis by orthogonal `Q_0, …, Q_L`. The maps `img j` are any countably many maps of the parameters,
one of them the identity; the permutations of hidden units or heads and the sign flips of tanh
units, composed, are finitely many such maps. -/
theorem ae_funDim_attentionMlp_skipless_iff_ae_locally_cob_heads_rmsNorm_family
    (hε : 0 < ε) (hσ : AnalyticOnNhd ℝ σ Set.univ)
    (μ : Measure (Params
      (Arch.attentionMlp (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d)
    (hW : ∀ ℓ,
      Fintype.card d ≤ Fintype.card (H ℓ) * Fintype.card (dh ℓ) + Fintype.card (hid ℓ))
    {ι : Type*} [Countable ι]
    (img : ι → Params (Arch.attentionMlp (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut →
      Params (Arch.attentionMlp (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut)
    (j₀ : ι) (himg : ∀ θ, img j₀ θ = θ) :
    (∀ᵐ θ ∂μ, funDim (Arch.attentionMlp sees σ (rmsNorm ε) H dh hid) 0 θ
        + ((L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2)
          + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
      = Module.finrank ℝ (Params
          (Arch.attentionMlp (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut)) ↔
    (∀ᵐ θ ∂μ, ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.attentionMlp sees σ (rmsNorm ε) H dh hid) 0 θ' x
        = eval (Arch.attentionMlp sees σ (rmsNorm ε) H dh hid) 0 θ x) →
        ∃ j : ι, ∃ K K' : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ,
          ∃ Q : Fin (L + 1) → GL d ℝ,
            (∀ ℓ, (Q ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ) ∧
            θ' = (Params.sumOf (((img j θ).sumFst.headsQK K).headsVO K') (img j θ).sumSnd).cob Q
                Q) := by
  constructor
  · -- the equality condition gives local identifiability up to the continuous symmetries (the
    -- statement without further images), and the identity `img j₀` is among the images
    intro h
    filter_upwards
      [(ae_funDim_attentionMlp_skipless_iff_ae_locally_cob_heads_rmsNorm hε hσ μ hdIn hdh
        hW).1 h]
      with θ ⟨U, hU, hUV⟩
    refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
    obtain ⟨K, K', Q, hQ, hQθ⟩ := hUV θ' hθ' heq
    exact ⟨j₀, K, K', Q, hQ, by rw [himg]; exact hQθ⟩
  · -- local identifiability gives the lower bound from the families
    -- `Ψ θ j n = sumOf (headsFam_iff1 (img j θ).sumFst n) (img j θ).sumSnd` of the changes of
    -- basis inside the heads of the attention part of `img j θ`, and the upper bound of
    -- Theorem 4.2
    intro h
    have hlow := ae_finrank_le_funDim_add_of_ae_locally_cob_orthogonal_family
      (Arch.attentionMlp (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) 0
      (fun ℓ => analyticOnNhd_f_sum (analyticOnNhd_f_attention sees (rmsNorm ε) H dh ℓ)
        (analyticOnNhd_f_mlp hσ ℓ)) (analyticOnNhd_rmsNorm hε) μ
      (fun θ j n => Params.sumOf (headsFam_iff1 (img j θ).sumFst n) (img j θ).sumSnd)
      (fun _ => {n | ∀ ℓ i, IsUnit (n.1 ℓ i) ∧ IsUnit (n.2 ℓ i)})
      (fun θ j => contDiffOn_sumOf_iff1 (contDiffOn_headsFam_iff1 (img j θ).sumFst)
        contDiffOn_const) (by
        filter_upwards [h] with θ ⟨U, hU, hUV⟩
        refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
        obtain ⟨j, K, K', Q, hQ, hQθ⟩ := hUV θ' hθ' heq
        refine ⟨j, (fun ℓ i => (K ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ),
          fun ℓ i => (K' ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)),
          fun ℓ i => ⟨(K ℓ i).isUnit, (K' ℓ i).isUnit⟩, Q, hQ, ?_⟩
        rw [headsFam_coe_iff1]
        exact hQθ)
    have hup := ae_funDim_add_le_skipless_attentionMlp_rmsNorm ε μ hdIn hdh hW
    filter_upwards [hlow, hup] with θ h1 h2
    rw [Module.finrank_prod, finrank_headFun_iff1] at h1
    generalize ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2 = s at h1 h2 ⊢
    generalize (L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2) = a at h1 h2 ⊢
    omega

/-- **Proposition 4.5 of the skips paper, for skipless networks of attention blocks and gated blocks
with a real-analytic gate, in any order, without normalization, with countably many further images
of `θ`:** `fd = P − (L + 1) d² − s` at almost every parameter (`s = 2 ∑ H d_h² + ∑ d_hidden`) if and
only if at almost every parameter `θ` every `θ'` near `θ` with the same function is, for some `j`,
the image `img j θ` of `θ` after changes of basis inside the heads, a rescaling of the values of the
hidden units by nonzero factors `c` and a change of basis by invertible `G_0, …, G_L`. The maps `img
j` are any countably many maps of the parameters, one of them the identity; the permutations of
hidden units or heads and the sign flips of tanh units, composed, are finitely many such maps. -/
theorem ae_funDim_attentionGated_skipless_iff_ae_locally_cob_heads_rescale_family
    [Nonempty d] (hσ : AnalyticOnNhd ℝ σ Set.univ)
    (μ : Measure (Params
      (Arch.attentionGated (T := T) (d := d) sees σ id H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d)
    (hW : ∀ ℓ,
      Fintype.card d ≤ Fintype.card (H ℓ) * Fintype.card (dh ℓ) + Fintype.card (hid ℓ))
    {ι : Type*} [Countable ι]
    (img : ι → Params (Arch.attentionGated (T := T) (d := d) sees σ id H dh hid) dIn dOut →
      Params (Arch.attentionGated (T := T) (d := d) sees σ id H dh hid) dIn dOut)
    (j₀ : ι) (himg : ∀ θ, img j₀ θ = θ) :
    (∀ᵐ θ ∂μ, funDim (Arch.attentionGated sees σ id H dh hid) 0 θ
        + ((L + 1) * Fintype.card d ^ 2
          + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
            + ∑ ℓ, Fintype.card (hid ℓ)))
      = Module.finrank ℝ (Params
          (Arch.attentionGated (T := T) (d := d) sees σ id H dh hid) dIn dOut)) ↔
    (∀ᵐ θ ∂μ, ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.attentionGated sees σ id H dh hid) 0 θ' x
        = eval (Arch.attentionGated sees σ id H dh hid) 0 θ x) →
        ∃ j : ι, ∃ (K K' : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ) (c : ∀ ℓ, hid ℓ → ℝ), (∀ ℓ i, c ℓ i ≠ 0) ∧
          ∃ G : Fin (L + 1) → GL d ℝ,
            θ' = (Params.sumOf (((img j θ).sumFst.headsQK K).headsVO K') ((img j θ).sumSnd.rescale
                c)).cob G G) := by
  constructor
  · -- the equality condition gives local identifiability up to the continuous symmetries (the
    -- statement without further images), and the identity `img j₀` is among the images
    intro h
    filter_upwards
      [(ae_funDim_attentionGated_skipless_iff_ae_locally_cob_heads_rescale hσ μ hdIn hdh
        hW).1 h]
      with θ ⟨U, hU, hUV⟩
    refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
    obtain ⟨K, K', c, hc, G, hG⟩ := hUV θ' hθ' heq
    exact ⟨j₀, K, K', c, hc, G, by rw [himg]; exact hG⟩
  · -- local identifiability gives the lower bound from the families `Ψ θ j n` of the changes of
    -- basis inside the heads of the attention part and the rescalings of the gated part of
    -- `img j θ`, and the upper bound of Theorem 4.2
    intro h
    have hlow := ae_finrank_le_funDim_add_of_ae_locally_cob_family
      (Arch.attentionGated (T := T) (d := d) sees σ id H dh hid) 0
      (fun ℓ => analyticOnNhd_f_sum (analyticOnNhd_f_attention sees id H dh ℓ)
        (analyticOnNhd_f_gated hσ ℓ)) analyticOnNhd_id μ
      (N := ((∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ))
        × (∀ ℓ, hid ℓ → ℝ))
      (fun θ j n =>
        Params.sumOf (headsFam_iff1 (img j θ).sumFst n.1) ((img j θ).sumSnd.rescale n.2))
      (fun _ => {n | (∀ ℓ i, IsUnit (n.1.1 ℓ i) ∧ IsUnit (n.1.2 ℓ i)) ∧ ∀ ℓ i, n.2 ℓ i ≠ 0})
      (fun θ j => contDiffOn_sumOf_iff1
        ((contDiffOn_headsFam_iff1 (img j θ).sumFst).comp contDiffOn_fst fun _ hn => hn.1)
        ((contDiffOn_rescale_iff1 (img j θ).sumSnd).comp contDiffOn_snd fun _ hn => hn.2)) (by
        filter_upwards [h] with θ ⟨U, hU, hUV⟩
        refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
        obtain ⟨j, K, K', c, hc, G, hG⟩ := hUV θ' hθ' heq
        refine ⟨j, ((fun ℓ i => (K ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ),
          fun ℓ i => (K' ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)), c),
          ⟨fun ℓ i => ⟨(K ℓ i).isUnit, (K' ℓ i).isUnit⟩, hc⟩, G, ?_⟩
        rw [headsFam_coe_iff1]
        exact hG)
    have hup := ae_funDim_add_le_skipless_attentionGated μ hdIn hdh hW
    filter_upwards [hlow, hup] with θ h1 h2
    rw [Module.finrank_prod, Module.finrank_prod, finrank_headFun_iff1, finrank_hidFun_iff1] at h1
    generalize ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2 = s at h1 h2 ⊢
    generalize ∑ ℓ, Fintype.card (hid ℓ) = t at h1 h2 ⊢
    generalize (L + 1) * Fintype.card d ^ 2 = a at h1 h2 ⊢
    omega

/-- **Proposition 4.5 of the skips paper, for skipless networks of attention blocks and gated blocks
with a real-analytic gate, in any order, under pre-RMSNorm with `ε > 0`, with countably many further
images of `θ`:** `fd = P − (L + 1) d(d−1)/2 − s` at almost every parameter (`s = 2 ∑ H d_h² + ∑
d_hidden`) if and only if at almost every parameter `θ` every `θ'` near `θ` with the same function
is, for some `j`, the image `img j θ` of `θ` after changes of basis inside the heads, a rescaling of
the values of the hidden units by nonzero factors `c` and a change of basis by orthogonal `Q_0, …,
Q_L`. The maps `img j` are any countably many maps of the parameters, one of them the identity; the
permutations of hidden units or heads and the sign flips of tanh units, composed, are finitely many
such maps. -/
theorem ae_funDim_attentionGated_skipless_iff_ae_locally_cob_heads_rescale_rmsNorm_family
    (hε : 0 < ε) [Nonempty d] (hσ : AnalyticOnNhd ℝ σ Set.univ)
    (μ : Measure (Params
      (Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d)
    (hW : ∀ ℓ,
      Fintype.card d ≤ Fintype.card (H ℓ) * Fintype.card (dh ℓ) + Fintype.card (hid ℓ))
    {ι : Type*} [Countable ι]
    (img : ι → Params (Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut →
      Params (Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut)
    (j₀ : ι) (himg : ∀ θ, img j₀ θ = θ) :
    (∀ᵐ θ ∂μ, funDim (Arch.attentionGated sees σ (rmsNorm ε) H dh hid) 0 θ
        + ((L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2)
          + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
            + ∑ ℓ, Fintype.card (hid ℓ)))
      = Module.finrank ℝ (Params
          (Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut)) ↔
    (∀ᵐ θ ∂μ, ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.attentionGated sees σ (rmsNorm ε) H dh hid) 0 θ' x
        = eval (Arch.attentionGated sees σ (rmsNorm ε) H dh hid) 0 θ x) →
        ∃ j : ι, ∃ (K K' : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ) (c : ∀ ℓ, hid ℓ → ℝ), (∀ ℓ i, c ℓ i ≠ 0) ∧
          ∃ Q : Fin (L + 1) → GL d ℝ,
            (∀ ℓ, (Q ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ) ∧
            θ' = (Params.sumOf (((img j θ).sumFst.headsQK K).headsVO K') ((img j θ).sumSnd.rescale
                c)).cob Q Q) := by
  constructor
  · -- the equality condition gives local identifiability up to the continuous symmetries (the
    -- statement without further images), and the identity `img j₀` is among the images
    intro h
    filter_upwards
      [(ae_funDim_attentionGated_skipless_iff_ae_locally_cob_heads_rescale_rmsNorm hε hσ μ
        hdIn hdh hW).1 h]
      with θ ⟨U, hU, hUV⟩
    refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
    obtain ⟨K, K', c, hc, Q, hQ, hQθ⟩ := hUV θ' hθ' heq
    exact ⟨j₀, K, K', c, hc, Q, hQ, by rw [himg]; exact hQθ⟩
  · -- local identifiability gives the lower bound from the families `Ψ θ j n` of the changes of
    -- basis inside the heads of the attention part and the rescalings of the gated part of
    -- `img j θ`, and the upper bound of Theorem 4.2
    intro h
    have hlow := ae_finrank_le_funDim_add_of_ae_locally_cob_orthogonal_family
      (Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) 0
      (fun ℓ => analyticOnNhd_f_sum (analyticOnNhd_f_attention sees (rmsNorm ε) H dh ℓ)
        (analyticOnNhd_f_gated hσ ℓ)) (analyticOnNhd_rmsNorm hε) μ
      (N := ((∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ))
        × (∀ ℓ, hid ℓ → ℝ))
      (fun θ j n =>
        Params.sumOf (headsFam_iff1 (img j θ).sumFst n.1) ((img j θ).sumSnd.rescale n.2))
      (fun _ => {n | (∀ ℓ i, IsUnit (n.1.1 ℓ i) ∧ IsUnit (n.1.2 ℓ i)) ∧ ∀ ℓ i, n.2 ℓ i ≠ 0})
      (fun θ j => contDiffOn_sumOf_iff1
        ((contDiffOn_headsFam_iff1 (img j θ).sumFst).comp contDiffOn_fst fun _ hn => hn.1)
        ((contDiffOn_rescale_iff1 (img j θ).sumSnd).comp contDiffOn_snd fun _ hn => hn.2)) (by
        filter_upwards [h] with θ ⟨U, hU, hUV⟩
        refine ⟨U, hU, fun θ' hθ' heq => ?_⟩
        obtain ⟨j, K, K', c, hc, Q, hQ, hQθ⟩ := hUV θ' hθ' heq
        refine ⟨j, ((fun ℓ i => (K ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ),
          fun ℓ i => (K' ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)), c),
          ⟨fun ℓ i => ⟨(K ℓ i).isUnit, (K' ℓ i).isUnit⟩, hc⟩, Q, hQ, ?_⟩
        rw [headsFam_coe_iff1]
        exact hQθ)
    have hup := ae_funDim_add_le_skipless_attentionGated_rmsNorm ε μ hdIn hdh hW
    filter_upwards [hlow, hup] with θ h1 h2
    rw [Module.finrank_prod, Module.finrank_prod, finrank_headFun_iff1, finrank_hidFun_iff1] at h1
    generalize ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2 = s at h1 h2 ⊢
    generalize ∑ ℓ, Fintype.card (hid ℓ) = t at h1 h2 ⊢
    generalize (L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2) = a at h1 h2 ⊢
    omega

end Skips
