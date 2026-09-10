/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.TateFredholm.Fredholm

/-!
# Block operators and the multiplicativity of the Fredholm determinant

The general block-operator machinery (originally `PhD/JacobsSlash/1_BlockOp.lean`, the AG-W
tranche of the Jacobs board; moved here 2026-08-18 for the general-weight compactness of
`PhD/QMF/Weight/Forms.lean`):
operators on `c(σ × I, R)` assembled from a `σ × σ` matrix of operators on `c(I, R)`, and
**Serre's partition lemma** ([Serre, IHÉS 12, Lemme 2] = [Jacobs, Lemma 1.15]):

> "Let `I = I′ ∪ I″` be a partition of `I`.  Assume that `u` is a compact endomorphism of
> `E = c(I)` sending `E′ = c(I′)` to itself.  Let `u′` be the restriction of `u` to `E′`,
> and let `u″` be the endomorphism of `E″ = c(I″)` defined by passing to the quotient by
> `u`.  Then `u′` and `u″` are compact and `det(1 − tu) = det(1 − tu′) det(1 − tu″)`."

We state everything at the matrix level: "sends `c(I′)` to itself" is the vanishing of the
`I″ × I′` corner of the matrix, the restriction and the quotient action are the two
diagonal corners, and the proof is the factorisation of the principal minors of a
block-triangular matrix.  Iterating over a `Fintype σ` gives the block-diagonal product
`det(1 − tu) = ∏_a det(1 − t u_{aa})` consumed by [Jacobs, pp. 32–34].

Stated over the same generality as `PhD.TateFredholm.Fredholm` (Banach ultrametric
`NormedCommRing`, arbitrary decidable index).

The two transport statements for `IsCompactoid` (`isCompactoid_restrictOp`,
`isCompactoid_blockOp`) carry `[IsTate R]`, as every compactoid statement in
`PhD/TateFredholm/` does: `rowNorm` is a real `⨆`, so comparing the row sup of a
sub-family with the row sup of the whole row needs the row to be bounded, which is
`le_opNorm` on the unit vectors (`norm_matrixCoeff_le_rowNorm_of_isTate`) and genuinely
fails over a non-Tate base — where an unbounded row makes `rowNorm` the `sSup`-junk value
`0` and `IsCompactoid` vacuously true while a restriction of it is not compactoid.
-/

open Filter Topology

open TateFredholm
open scoped TateFredholm

set_option linter.unusedSectionVars false

namespace TateFredholm

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R]
  [NormOneClass R]
variable {I : Type*} [DecidableEq I]

/-!
## Generic model-space and matrix-coefficient helpers

Index-generic tools used throughout the file (and by the consumers of the block machinery):
building an element of `c(A, R)` from a cofinitely decaying family, pulling coordinates back
along an injection, matrix-coefficient extensionality, and the slicewise criterion for
cofinite decay on a product with a finite factor.
-/

section Aux

variable {A B : Type*}

/-- An element of the model space `c(A, R)` built from a cofinitely decaying coordinate
family (continuity is free: `Ix A` is discrete). -/
noncomputable def cSpace.ofTendsto (g : A → R) (hg : Tendsto g cofinite (𝓝 0)) : c(A, R) :=
  ⟨⟨g, continuous_of_discreteTopology⟩, by rwa [Filter.cocompact_eq_cofinite]⟩

omit [IsUltrametricDist R] [CompleteSpace R] [NormOneClass R] in
/-- The coordinates of `cSpace.ofTendsto g hg` are `g`. -/
@[simp] theorem cSpace.ofTendsto_apply (g : A → R) (hg : Tendsto g cofinite (𝓝 0)) (a : A) :
    cSpace.ofTendsto g hg a = g a := rfl

/-- The sup-norm bound from a uniform coordinate bound. -/
theorem cSpace.norm_le_of_forall {f : c(A, R)} {C : ℝ} (hC : 0 ≤ C) (h : ∀ a, ‖f a‖ ≤ C) :
    ‖f‖ ≤ C := by
  rw [cSpace.norm_eq_iSup]
  exact Real.iSup_le h hC

/-- Coordinates of a finite sum. -/
theorem cSpace.sum_apply {ι : Type*} (s : Finset ι) (F : ι → c(A, R)) (a : A) :
    (∑ x ∈ s, F x) a = ∑ x ∈ s, F x a :=
  map_sum (cSpace.evalCLM a) F s

/-- Pullback of coordinates along an injection `φ : B → A`, `f ↦ f ∘ φ`: the cofinite decay
transports because `φ` is injective, and the map is norm-nonincreasing. -/
noncomputable def cSpace.comap (φ : B → A) (hφ : Function.Injective φ) :
    c(A, R) →L[R] c(B, R) where
  toFun f := cSpace.ofTendsto (fun b => f (φ b))
    ((cSpace.tendsto_cofinite f).comp hφ.tendsto_cofinite)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := by
    refine (LipschitzWith.of_dist_le_mul (K := 1) fun f g => ?_).continuous
    rw [dist_eq_norm, dist_eq_norm, NNReal.coe_one, one_mul]
    refine cSpace.norm_le_of_forall (norm_nonneg _) fun b => ?_
    exact cSpace.norm_apply_le (f - g) (φ b)

/-- `cSpace.comap φ hφ` acts by precomposition with `φ`. -/
@[simp] theorem cSpace.comap_apply (φ : B → A) (hφ : Function.Injective φ) (f : c(A, R))
    (b : B) : cSpace.comap φ hφ f b = f (φ b) := rfl

/-- Pulling back along a bijection permutes the canonical basis. -/
@[simp] theorem cSpace.comap_single [DecidableEq A] [DecidableEq B] (e : B ≃ A) (a : A)
    (r : R) : cSpace.comap e e.injective (cSpace.single a r) = cSpace.single (e.symm a) r := by
  refine DFunLike.ext _ _ fun b => ?_
  rw [cSpace.comap_apply]
  by_cases h : b = e.symm a
  · subst h
    rw [Equiv.apply_symm_apply, cSpace.single_apply_self, cSpace.single_apply_self]
  · rw [cSpace.single_apply_of_ne h,
      cSpace.single_apply_of_ne (fun hh => h (by rw [← hh, Equiv.symm_apply_apply]))]

/-- Cofinite decay on `σ × A` with `σ` finite is checked one slice at a time. -/
theorem tendsto_cofinite_prod_of_finite {σ : Type*} [Finite σ] {M : Type*} {l : Filter M}
    {f : σ × A → M} (h : ∀ a : σ, Tendsto (fun i => f (a, i)) cofinite l) :
    Tendsto f cofinite l := by
  intro s hs
  rw [Filter.mem_map, Filter.mem_cofinite]
  have hfin : ∀ a : σ, {i : A | f (a, i) ∉ s}.Finite := fun a => by
    have hmem := h a hs
    rw [Filter.mem_map, Filter.mem_cofinite] at hmem
    exact hmem
  refine Set.Finite.subset
    (Set.finite_iUnion fun a : σ => (hfin a).image (fun i => ((a, i) : σ × A))) ?_
  rintro ⟨a, i⟩ hx
  exact Set.mem_iUnion.2 ⟨a, ⟨i, hx, rfl⟩⟩

/-- Each matrix coefficient is bounded by its row sup.  Over a Tate ring the whole row is
bounded by `‖u‖` (`le_opNorm` on the unit vectors), which is what makes the `⨆` of
`rowNorm` an honest supremum rather than the `sSup`-junk value `0`. -/
theorem norm_matrixCoeff_le_rowNorm_of_isTate [IsTate R] [DecidableEq A]
    (u : c(A, R) →L[R] c(B, R)) (j : B) (i : A) : ‖matrixCoeff u j i‖ ≤ rowNorm u j :=
  le_ciSup ⟨‖u‖, by
    rintro _ ⟨i, rfl⟩
    calc ‖matrixCoeff u j i‖ ≤ ‖u (cSpace.single i 1)‖ := cSpace.norm_apply_le _ _
    _ ≤ ‖u‖ * ‖cSpace.single i (1 : R)‖ := le_opNorm _ _
    _ = ‖u‖ := by rw [cSpace.norm_single_one, mul_one]⟩ i

end Aux

section Subtype

variable (p : I → Prop) [DecidablePred p]

/-- The extension-by-zero family decays cofinitely: its non-`s` coordinates are the
image, under the injective coercion, of `f`'s. -/
private theorem tendsto_cofinite_extendZero (f : c({x // p x}, R)) :
    Tendsto (fun x : I => if h : p x then f ⟨x, h⟩ else 0) cofinite (𝓝 0) := by
  intro s hs
  have h0 : (0 : R) ∈ s := mem_of_mem_nhds hs
  have hfin : {y : {x // p x} | f y ∉ s}.Finite := by
    have hmem := cSpace.tendsto_cofinite f hs
    rwa [Filter.mem_map, Filter.mem_cofinite] at hmem
  rw [Filter.mem_map, Filter.mem_cofinite]
  refine Set.Finite.subset (hfin.image Subtype.val) fun x hx => ?_
  simp only [Set.mem_compl_iff, Set.mem_preimage] at hx
  by_cases h : p x
  · rw [dif_pos h] at hx
    exact ⟨⟨x, h⟩, hx, rfl⟩
  · rw [dif_neg h] at hx
    exact absurd h0 hx

/-- Extension by zero: `c({x // p x}, R) → c(I, R)`. -/
noncomputable def cSpace.inclSubtype : c({x // p x}, R) →L[R] c(I, R) where
  toFun f := cSpace.ofTendsto (fun x : I => if h : p x then f ⟨x, h⟩ else 0)
    (tendsto_cofinite_extendZero p f)
  map_add' f g := DFunLike.ext _ _ fun x => by
    show (if h : p x then (f + g) ⟨x, h⟩ else 0)
        = (if h : p x then f ⟨x, h⟩ else 0) + (if h : p x then g ⟨x, h⟩ else 0)
    by_cases h : p x
    · rw [dif_pos h, dif_pos h, dif_pos h]
      rfl
    · rw [dif_neg h, dif_neg h, dif_neg h, add_zero]
  map_smul' r f := DFunLike.ext _ _ fun x => by
    show (if h : p x then (r • f) ⟨x, h⟩ else 0) = r • (if h : p x then f ⟨x, h⟩ else 0)
    by_cases h : p x
    · rw [dif_pos h, dif_pos h]
      rfl
    · rw [dif_neg h, dif_neg h, smul_zero]
  cont := by
    refine (LipschitzWith.of_dist_le_mul (K := 1) fun f g => ?_).continuous
    rw [dist_eq_norm, dist_eq_norm, NNReal.coe_one, one_mul]
    refine cSpace.norm_le_of_forall (norm_nonneg _) fun x => ?_
    show ‖(if h : p x then f ⟨x, h⟩ else 0) - (if h : p x then g ⟨x, h⟩ else 0)‖ ≤ ‖f - g‖
    by_cases h : p x
    · rw [dif_pos h, dif_pos h]
      exact cSpace.norm_apply_le (f - g) ⟨x, h⟩
    · rw [dif_neg h, dif_neg h, sub_zero, norm_zero]
      exact norm_nonneg _

/-- Coordinates of the extension by zero. -/
@[simp] theorem cSpace.inclSubtype_apply (f : c({x // p x}, R)) (x : I) :
    cSpace.inclSubtype p f x = if h : p x then f ⟨x, h⟩ else 0 := rfl

/-- Restriction of coordinates: `c(I, R) → c({x // p x}, R)`. -/
noncomputable def cSpace.projSubtype : c(I, R) →L[R] c({x // p x}, R) :=
  cSpace.comap Subtype.val Subtype.val_injective

omit [DecidableEq I] [DecidablePred p] in
/-- Coordinates of the restriction to the indices satisfying `p`. -/
@[simp] theorem cSpace.projSubtype_apply (f : c(I, R)) (j : {x // p x}) :
    cSpace.projSubtype p f j = f (j : I) := rfl

/-- Extension by zero permutes the canonical bases. -/
@[simp] theorem cSpace.inclSubtype_single (i : {x // p x}) (r : R) :
    cSpace.inclSubtype p (cSpace.single i r) = cSpace.single (i : I) r := by
  refine DFunLike.ext _ _ fun x => ?_
  rw [cSpace.inclSubtype_apply]
  by_cases hx : x = (i : I)
  · subst hx
    rw [dif_pos i.2]
    exact (cSpace.single_apply_self i r).trans (cSpace.single_apply_self (i : I) r).symm
  · rw [cSpace.single_apply_of_ne hx]
    by_cases h : p x
    · rw [dif_pos h, cSpace.single_apply_of_ne (fun hh => hx (congrArg Subtype.val hh))]
    · rw [dif_neg h]

variable {p}

/-- Evaluating an extension by zero at an index satisfying `p` recovers the original
coordinate.  (Not a `simp` lemma: `inclSubtype_apply` already rewrites the left-hand side.) -/
theorem matrixCoeff_inclSubtype (j : {x // p x}) (f : c({x // p x}, R)) :
    (cSpace.inclSubtype p f : c(I, R)) j = f j := by
  rw [cSpace.inclSubtype_apply, dif_pos j.2]

variable (p) in
/-- The compression of an operator to the coordinates satisfying `p` — Serre's
restriction `u′` (and, for the complementary corner of a triangular operator, the
quotient action `u″`), at the matrix level. -/
noncomputable def restrictOp (u : c(I, R) →L[R] c(I, R)) :
    c({x // p x}, R) →L[R] c({x // p x}, R) :=
  (cSpace.projSubtype p).comp (u.comp (cSpace.inclSubtype p))

/-- The matrix of the compression `restrictOp p u` is the corresponding principal
submatrix of the matrix of `u`. -/
@[simp] theorem matrixCoeff_restrictOp (u : c(I, R) →L[R] c(I, R)) (j i : {x // p x}) :
    matrixCoeff (restrictOp p u) j i = matrixCoeff u j i := by
  show cSpace.projSubtype p (u (cSpace.inclSubtype p (cSpace.single i 1))) j = _
  rw [cSpace.inclSubtype_single]
  rfl

/-- (`[IsTate R]`: the row sups of the restriction are *sub*-sups of `u`'s, and comparing
suprema needs the rows of `u` to be bounded — `norm_matrixCoeff_le_rowNorm_of_isTate`.) -/
theorem isCompactoid_restrictOp [IsTate R] {u : c(I, R) →L[R] c(I, R)} (hu : IsCompactoid u) :
    IsCompactoid (restrictOp p u) := by
  have hle : ∀ j : {x // p x}, rowNorm (restrictOp p u) j ≤ rowNorm u (j : I) := by
    intro j
    simp only [rowNorm]
    refine Real.iSup_le (fun i => ?_) (rowNorm_nonneg u _)
    rw [matrixCoeff_restrictOp]
    exact norm_matrixCoeff_le_rowNorm_of_isTate u (j : I) (i : I)
  exact squeeze_zero (fun j => rowNorm_nonneg _ j) hle
    (hu.comp Subtype.val_injective.tendsto_cofinite)

end Subtype

section Reindex

variable {J : Type*} [DecidableEq J]

/-- Transport of an operator along a bijection of the index set. -/
noncomputable def reindexOp (e : I ≃ J) (u : c(I, R) →L[R] c(I, R)) :
    c(J, R) →L[R] c(J, R) :=
  (cSpace.comap (⇑e.symm) e.symm.injective).comp (u.comp (cSpace.comap (⇑e) e.injective))

/-- The matrix of `reindexOp e u` is the matrix of `u` with both indices transported
along `e.symm`. -/
@[simp] theorem matrixCoeff_reindexOp (e : I ≃ J) (u : c(I, R) →L[R] c(I, R)) (j i : J) :
    matrixCoeff (reindexOp e u) j i = matrixCoeff u (e.symm j) (e.symm i) := by
  show cSpace.comap (⇑e.symm) e.symm.injective
      (u (cSpace.comap (⇑e) e.injective (cSpace.single i 1))) j = _
  rw [cSpace.comap_single e i (1 : R)]
  rfl

/-- Reindexing carries the principal `S`-minor to the principal `e.symm '' S`-minor. -/
theorem minor_reindexOp (e : I ≃ J) (u : c(I, R) →L[R] c(I, R)) (S : Finset J) :
    minor (reindexOp e u) S = minor u (S.map e.symm.toEmbedding) := by
  have hbij : Function.Bijective (fun j : {x // x ∈ S} =>
      (⟨e.symm j.1, Finset.mem_map_of_mem _ j.2⟩ : {x // x ∈ S.map e.symm.toEmbedding})) := by
    constructor
    · intro j j' h
      exact Subtype.ext (e.symm.injective (congrArg Subtype.val h))
    · rintro ⟨q, hq⟩
      obtain ⟨y, hy, rfl⟩ := Finset.mem_map.1 hq
      exact ⟨⟨y, hy⟩, rfl⟩
  have hM : (Matrix.of fun j i : {x // x ∈ S} =>
        matrixCoeff (reindexOp e u) (j : J) (i : J))
      = (Matrix.of fun q q' : {x // x ∈ S.map e.symm.toEmbedding} =>
          matrixCoeff u (q : I) (q' : I)).submatrix
            (Equiv.ofBijective _ hbij) (Equiv.ofBijective _ hbij) :=
    Matrix.ext fun j i => matrixCoeff_reindexOp e u (j : J) (i : J)
  show (Matrix.of fun j i : {x // x ∈ S} => matrixCoeff (reindexOp e u) (j : J) (i : J)).det = _
  rw [hM, Matrix.det_submatrix_equiv_self]
  rfl

/-- The characteristic power series is invariant under reindexing (the principal minors
correspond under the bijection). -/
theorem charPowerSeries_reindexOp (e : I ≃ J) (u : c(I, R) →L[R] c(I, R)) :
    charPowerSeries (reindexOp e u) = charPowerSeries u := by
  refine PowerSeries.ext fun n => ?_
  rw [charPowerSeries_coeff, charPowerSeries_coeff, charCoeff, charCoeff]
  congr 1
  refine Eq.trans ?_ (Equiv.tsum_eq
    ((e.symm.finsetCongr).subtypeEquiv fun S => by
      rw [Equiv.finsetCongr_apply, Finset.card_map])
    (fun S : {S : Finset I // S.card = n} => minor u (S : Finset I)))
  refine tsum_congr fun S => ?_
  exact minor_reindexOp e u (S : Finset J)

/-- Reindexing preserves compactoidness (the row sups are permuted). -/
theorem isCompactoid_reindexOp (e : I ≃ J) {u : c(I, R) →L[R] c(I, R)}
    (hu : IsCompactoid u) : IsCompactoid (reindexOp e u) := by
  have hrow : ∀ j : J, rowNorm (reindexOp e u) j = rowNorm u (e.symm j) := by
    intro j
    simp only [rowNorm, matrixCoeff_reindexOp, iSup]
    congr 1
    exact e.symm.surjective.range_comp fun i => ‖matrixCoeff u (e.symm j) i‖
  exact Tendsto.congr (fun j => (hrow j).symm) (hu.comp e.symm.injective.tendsto_cofinite)

end Reindex

section Partition

variable (p : I → Prop) [DecidablePred p]

/-- Splitting a finite index set into its `p`-part and its `¬p`-part, `S ↦ (S ∩ p, S ∩ ¬p)`;
the inverse is the union of the two images. -/
private def finsetSplit : Finset I ≃ Finset {x // p x} × Finset {x // ¬ p x} where
  toFun S := (S.subtype p, S.subtype fun x => ¬ p x)
  invFun z := z.1.map (Function.Embedding.subtype p) ∪
    z.2.map (Function.Embedding.subtype fun x => ¬ p x)
  left_inv S := by
    ext x
    constructor
    · intro hx
      rcases Finset.mem_union.1 hx with h | h
      · obtain ⟨y, hy, rfl⟩ := Finset.mem_map.1 h
        exact Finset.mem_subtype.1 hy
      · obtain ⟨y, hy, rfl⟩ := Finset.mem_map.1 h
        exact Finset.mem_subtype.1 hy
    · intro hx
      by_cases h : p x
      · exact Finset.mem_union_left _ (Finset.mem_map.2 ⟨⟨x, h⟩, Finset.mem_subtype.2 hx, rfl⟩)
      · exact Finset.mem_union_right _ (Finset.mem_map.2 ⟨⟨x, h⟩, Finset.mem_subtype.2 hx, rfl⟩)
  right_inv z := by
    obtain ⟨S₁, S₂⟩ := z
    have h₁ : (S₁.map (Function.Embedding.subtype p) ∪
        S₂.map (Function.Embedding.subtype fun x => ¬ p x)).subtype p = S₁ := by
      ext y
      rw [Finset.mem_subtype, Finset.mem_union]
      constructor
      · rintro (h | h)
        · obtain ⟨w, hw, hwy⟩ := Finset.mem_map.1 h
          exact (Subtype.ext hwy : w = y) ▸ hw
        · obtain ⟨w, hw, hwy⟩ := Finset.mem_map.1 h
          exact absurd y.2 (hwy ▸ w.2)
      · intro hy
        exact Or.inl (Finset.mem_map.2 ⟨y, hy, rfl⟩)
    have h₂ : (S₁.map (Function.Embedding.subtype p) ∪
        S₂.map (Function.Embedding.subtype fun x => ¬ p x)).subtype (fun x => ¬ p x) = S₂ := by
      ext y
      rw [Finset.mem_subtype, Finset.mem_union]
      constructor
      · rintro (h | h)
        · obtain ⟨w, hw, hwy⟩ := Finset.mem_map.1 h
          exact absurd (hwy ▸ w.2) y.2
        · obtain ⟨w, hw, hwy⟩ := Finset.mem_map.1 h
          exact (Subtype.ext hwy : w = y) ▸ hw
      · intro hy
        exact Or.inr (Finset.mem_map.2 ⟨y, hy, rfl⟩)
    simp only [Prod.mk.injEq]
    exact ⟨h₁, h₂⟩

/-- The two parts of a finite index set add up to it. -/
private theorem card_subtype_add_card_subtype (S : Finset I) :
    (S.subtype p).card + (S.subtype fun x => ¬ p x).card = S.card := by
  rw [Finset.card_subtype, Finset.card_subtype, Finset.card_filter_add_card_filter_not]

private theorem card_finsetSplit_symm (z : Finset {x // p x} × Finset {x // ¬ p x}) :
    ((finsetSplit p).symm z).card = z.1.card + z.2.card := by
  have h := card_subtype_add_card_subtype p ((finsetSplit p).symm z)
  rw [show ((finsetSplit p).symm z).subtype p = z.1 from
        congrArg Prod.fst ((finsetSplit p).apply_symm_apply z),
      show ((finsetSplit p).symm z).subtype (fun x => ¬ p x) = z.2 from
        congrArg Prod.snd ((finsetSplit p).apply_symm_apply z)] at h
  exact h.symm

/-- The `p`-corner (in mathlib's `toSquareBlockProp` form) of the principal `S`-minor matrix
of `u` is the principal minor matrix of the compression `restrictOp p u` at the `p`-part
of `S`. -/
private theorem det_toSquareBlockProp_eq (u : c(I, R) →L[R] c(I, R)) (S : Finset I) :
    ((Matrix.of fun j i : S => matrixCoeff u (j : I) (i : I)).toSquareBlockProp
      fun x : S => p (x : I)).det = minor (restrictOp p u) (S.subtype p) := by
  let e : {x : {y // p y} // x ∈ S.subtype p} ≃ {a : {x // x ∈ S} // p (a : I)} :=
    { toFun := fun x => ⟨⟨x.1.1, Finset.mem_subtype.1 x.2⟩, x.1.2⟩
      invFun := fun a => ⟨⟨a.1.1, a.2⟩, Finset.mem_subtype.2 a.1.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← Matrix.det_submatrix_equiv_self e]
  refine congrArg Matrix.det (Matrix.ext fun j i => ?_)
  show matrixCoeff u (j.1.1 : I) (i.1.1 : I) = matrixCoeff (restrictOp p u) j.1 i.1
  exact (matrixCoeff_restrictOp u j.1 i.1).symm

/-- **Per-minor factorisation**: for a block-triangular `u`, every principal minor is the
product of the minors of the two compressions at the two parts of its index set
(`Matrix.twoBlockTriangular_det`). -/
private theorem minor_partition {u : c(I, R) →L[R] c(I, R)}
    (htri : ∀ j i, p i → ¬ p j → matrixCoeff u j i = 0) (S : Finset I) :
    minor u S = minor (restrictOp p u) (S.subtype p) *
      minor (restrictOp (fun x => ¬ p x) u) (S.subtype fun x => ¬ p x) := by
  rw [← det_toSquareBlockProp_eq p u S, ← det_toSquareBlockProp_eq (fun x => ¬ p x) u S]
  exact Matrix.twoBlockTriangular_det _ (fun x : S => p (x : I))
    (fun j hj i hi => htri (j : I) (i : I) hi hj)

variable (k l n : ℕ)

/-- Assembling an index set of cardinality `n = k + l` from a `k`-set of `p`-indices and an
`l`-set of `¬p`-indices. -/
private def splitEmbedding (hkl : k + l = n) :
    {S : Finset {x // p x} // S.card = k} × {S : Finset {x // ¬ p x} // S.card = l} →
      {S : Finset I // S.card = n} :=
  fun z => ⟨(finsetSplit p).symm ((z.1 : Finset {x // p x}), (z.2 : Finset {x // ¬ p x})), by
    rw [card_finsetSplit_symm, z.1.2, z.2.2, hkl]⟩

variable {k l n}

private theorem subtype_splitEmbedding_left (hkl : k + l = n)
    (z : {S : Finset {x // p x} // S.card = k} × {S : Finset {x // ¬ p x} // S.card = l}) :
    ((splitEmbedding p k l n hkl z : Finset I).subtype p) = (z.1 : Finset {x // p x}) :=
  congrArg Prod.fst ((finsetSplit p).apply_symm_apply _)

private theorem subtype_splitEmbedding_right (hkl : k + l = n)
    (z : {S : Finset {x // p x} // S.card = k} × {S : Finset {x // ¬ p x} // S.card = l}) :
    ((splitEmbedding p k l n hkl z : Finset I).subtype fun x => ¬ p x)
      = (z.2 : Finset {x // ¬ p x}) :=
  congrArg Prod.snd ((finsetSplit p).apply_symm_apply _)

private theorem splitEmbedding_injective (hkl : k + l = n) :
    Function.Injective (splitEmbedding p k l n hkl) := by
  intro z w h
  have h' := (finsetSplit p).symm.injective (congrArg Subtype.val h)
  exact Prod.ext (Subtype.ext (congrArg Prod.fst h')) (Subtype.ext (congrArg Prod.snd h'))

/-- Every index set of cardinality `n` whose `p`-part has cardinality `k` is assembled from
its two parts. -/
private theorem mem_range_splitEmbedding (hkl : k + l = n) (S : {S : Finset I // S.card = n})
    (hS : ((S : Finset I).subtype p).card = k) : S ∈ Set.range (splitEmbedding p k l n hkl) := by
  have hcard := card_subtype_add_card_subtype p (S : Finset I)
  rw [hS] at hcard
  have hn : (S : Finset I).card = n := S.2
  refine ⟨(⟨(S : Finset I).subtype p, hS⟩,
    ⟨(S : Finset I).subtype fun x => ¬ p x, by omega⟩), Subtype.ext ?_⟩
  exact (finsetSplit p).symm_apply_apply (S : Finset I)

/-- **Serre's partition lemma** ([Serre, IHÉS 12, Lemme 2]; [Jacobs, Lemma 1.15]), matrix
form: if the compactoid operator `u` is block-triangular for the partition
`I = {p} ∪ {¬p}` — no matrix entries from the `p`-columns into the `¬p`-rows, i.e. `u`
sends `c(I′)` to itself — then its Fredholm determinant is the product of those of the
two diagonal corners.

(`[IsTate R]`, as for `isCompactoid_restrictOp`: the two compressions have to be compactoid
for their minors to be summable.) -/
theorem charPowerSeries_partition [IsTate R] {u : c(I, R) →L[R] c(I, R)} (hu : IsCompactoid u)
    (htri : ∀ j i, p i → ¬ p j → matrixCoeff u j i = 0) :
    charPowerSeries u =
      charPowerSeries (restrictOp p u) * charPowerSeries (restrictOp (fun x => ¬ p x) u) := by
  have hu' : IsCompactoid (restrictOp p u) := isCompactoid_restrictOp hu
  have hu'' : IsCompactoid (restrictOp (fun x => ¬ p x) u) := isCompactoid_restrictOp hu
  have main : ∀ m : ℕ, (∑' S : {S : Finset I // S.card = m}, minor u (S : Finset I))
      = ∑ d ∈ Finset.antidiagonal m,
          (∑' S : {S : Finset {x // p x} // S.card = d.1},
            minor (restrictOp p u) (S : Finset {x // p x})) *
          (∑' S : {S : Finset {x // ¬ p x} // S.card = d.2},
            minor (restrictOp (fun x => ¬ p x) u) (S : Finset {x // ¬ p x})) := by
    intro m
    have hpiece : ∀ d ∈ Finset.antidiagonal m,
        HasSum (fun S : {S : Finset I // S.card = m} =>
            if ((S : Finset I).subtype p).card = d.1 then minor u (S : Finset I) else 0)
          ((∑' S : {S : Finset {x // p x} // S.card = d.1},
              minor (restrictOp p u) (S : Finset {x // p x})) *
            (∑' S : {S : Finset {x // ¬ p x} // S.card = d.2},
              minor (restrictOp (fun x => ¬ p x) u) (S : Finset {x // ¬ p x}))) := by
      rintro ⟨k, l⟩ hd
      rw [Finset.mem_antidiagonal] at hd
      -- the pieces of an index set with `k` `p`-indices, and their reassembly
      have hprod : ∀ z : {S : Finset {x // p x} // S.card = k} ×
          {S : Finset {x // ¬ p x} // S.card = l},
          minor u (splitEmbedding p k l m hd z : Finset I)
            = minor (restrictOp p u) (z.1 : Finset {x // p x}) *
              minor (restrictOp (fun x => ¬ p x) u) (z.2 : Finset {x // ¬ p x}) := by
        intro z
        rw [minor_partition p htri, subtype_splitEmbedding_left, subtype_splitEmbedding_right]
      have hsummable : Summable (fun z : {S : Finset {x // p x} // S.card = k} ×
          {S : Finset {x // ¬ p x} // S.card = l} =>
            minor (restrictOp p u) (z.1 : Finset {x // p x}) *
              minor (restrictOp (fun x => ¬ p x) u) (z.2 : Finset {x // ¬ p x})) :=
        ((summable_minor u hu m).comp_injective (splitEmbedding_injective p hd)).congr hprod
      have hAB := (summable_minor (restrictOp p u) hu' k).hasSum.mul
        (summable_minor (restrictOp (fun x => ¬ p x) u) hu'' l).hasSum hsummable
      refine ((splitEmbedding_injective p hd).hasSum_iff ?_).1 ?_
      · intro S hS
        rw [ite_eq_right_iff]
        intro hk
        exact absurd (mem_range_splitEmbedding p hd S hk) hS
      · refine hAB.congr_fun fun z => ?_
        rw [Function.comp_apply, if_pos (by rw [subtype_splitEmbedding_left, z.1.2]), hprod z]
    have hone : ∀ S : {S : Finset I // S.card = m},
        (∑ d ∈ Finset.antidiagonal m,
          if ((S : Finset I).subtype p).card = d.1 then minor u (S : Finset I) else 0)
            = minor u (S : Finset I) := by
      intro S
      have hkl : ((S : Finset I).subtype p).card
          + ((S : Finset I).subtype fun x => ¬ p x).card = m := by
        rw [card_subtype_add_card_subtype]; exact S.2
      rw [Finset.sum_eq_single (((S : Finset I).subtype p).card,
        ((S : Finset I).subtype fun x => ¬ p x).card)]
      · rw [if_pos rfl]
      · rintro ⟨a, b⟩ hab hne
        rw [Finset.mem_antidiagonal] at hab
        refine if_neg fun hk => hne ?_
        simp only [Prod.mk.injEq]
        omega
      · exact fun h => absurd (Finset.mem_antidiagonal.2 hkl) h
    have hsum := hasSum_sum (f := fun d : ℕ × ℕ => fun S : {S : Finset I // S.card = m} =>
      if ((S : Finset I).subtype p).card = d.1 then minor u (S : Finset I) else 0) hpiece
    rw [show (fun S : {S : Finset I // S.card = m} => ∑ d ∈ Finset.antidiagonal m,
        if ((S : Finset I).subtype p).card = d.1 then minor u (S : Finset I) else 0)
          = fun S : {S : Finset I // S.card = m} => minor u (S : Finset I) from
      funext hone] at hsum
    exact hsum.tsum_eq
  refine PowerSeries.ext fun m => ?_
  rw [charPowerSeries_coeff, PowerSeries.coeff_mul, charCoeff, main m, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [Finset.mem_antidiagonal] at hd
  rw [charPowerSeries_coeff, charPowerSeries_coeff, charCoeff, charCoeff, ← hd, pow_add]
  ring

end Partition

section Block

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- Extension by zero into the `a`-component of `c(σ × I, R)`. -/
noncomputable def cSpace.blockIncl (a : σ) : c(I, R) →L[R] c(σ × I, R) where
  toFun f := cSpace.ofTendsto (fun x : σ × I => if x.1 = a then f x.2 else 0)
    (tendsto_cofinite_prod_of_finite fun b => by
      by_cases hb : b = a
      · subst hb
        exact Tendsto.congr (fun i => (if_pos rfl).symm) (cSpace.tendsto_cofinite f)
      · exact Tendsto.congr (fun i => (if_neg hb).symm) tendsto_const_nhds)
  map_add' f g := DFunLike.ext _ _ fun x => by
    show (if x.1 = a then (f + g) x.2 else 0)
        = (if x.1 = a then f x.2 else 0) + (if x.1 = a then g x.2 else 0)
    by_cases h : x.1 = a
    · rw [if_pos h, if_pos h, if_pos h]
      rfl
    · rw [if_neg h, if_neg h, if_neg h, add_zero]
  map_smul' r f := DFunLike.ext _ _ fun x => by
    show (if x.1 = a then (r • f) x.2 else 0) = r • (if x.1 = a then f x.2 else 0)
    by_cases h : x.1 = a
    · rw [if_pos h, if_pos h]
      rfl
    · rw [if_neg h, if_neg h, smul_zero]
  cont := by
    refine (LipschitzWith.of_dist_le_mul (K := 1) fun f g => ?_).continuous
    rw [dist_eq_norm, dist_eq_norm, NNReal.coe_one, one_mul]
    refine cSpace.norm_le_of_forall (norm_nonneg _) fun x => ?_
    show ‖(if x.1 = a then f x.2 else 0) - (if x.1 = a then g x.2 else 0)‖ ≤ ‖f - g‖
    by_cases h : x.1 = a
    · rw [if_pos h, if_pos h]
      exact cSpace.norm_apply_le (f - g) x.2
    · rw [if_neg h, if_neg h, sub_zero, norm_zero]
      exact norm_nonneg _

omit [DecidableEq I] in
/-- Coordinates of the extension by zero into the `a`-component. -/
@[simp] theorem cSpace.blockIncl_apply (a : σ) (f : c(I, R)) (x : σ × I) :
    cSpace.blockIncl a f x = if x.1 = a then f x.2 else 0 := rfl

/-- Restriction of coordinates to the `b`-component of `c(σ × I, R)`. -/
noncomputable def cSpace.blockProj (b : σ) : c(σ × I, R) →L[R] c(I, R) :=
  cSpace.comap (fun i => (b, i)) fun _ _ h => congrArg Prod.snd h

omit [DecidableEq I] [Fintype σ] [DecidableEq σ] in
/-- Coordinates of the restriction to the `b`-component. -/
@[simp] theorem cSpace.blockProj_apply (b : σ) (f : c(σ × I, R)) (i : I) :
    cSpace.blockProj b f i = f (b, i) := rfl

/-- Block inclusion sends canonical basis vectors to canonical basis vectors. -/
@[simp] theorem cSpace.blockIncl_single (a : σ) (i : I) (r : R) :
    cSpace.blockIncl a (cSpace.single i r) = cSpace.single (a, i) r := by
  refine DFunLike.ext _ _ fun x => ?_
  obtain ⟨b, i'⟩ := x
  rw [cSpace.blockIncl_apply]
  by_cases hb : b = a
  · subst hb
    by_cases hi : i' = i
    · subst hi
      rw [if_pos rfl, cSpace.single_apply_self, cSpace.single_apply_self]
    · rw [if_pos rfl, cSpace.single_apply_of_ne hi,
        cSpace.single_apply_of_ne (fun h => hi (congrArg Prod.snd h))]
  · rw [if_neg hb, cSpace.single_apply_of_ne (fun h => hb (congrArg Prod.fst h))]

omit [DecidableEq I] in
/-- The two block maps are mutually orthogonal: `proj_b ∘ incl_a` is the identity for
`b = a` and zero otherwise. -/
theorem cSpace.blockProj_blockIncl (a b : σ) (f : c(I, R)) :
    cSpace.blockProj b (cSpace.blockIncl a f) = if b = a then f else 0 := by
  refine DFunLike.ext _ _ fun i => ?_
  rw [cSpace.blockProj_apply, cSpace.blockIncl_apply]
  by_cases hb : b = a
  · rw [if_pos hb, if_pos hb]
  · rw [if_neg hb, if_neg hb]
    rfl

/-- The operator on `c(σ × I, R)` assembled from a `σ × σ` matrix of operators on
`c(I, R)`.  The `(a, b)` block acts from the `b`-component to the `a`-component. -/
noncomputable def blockOp (T : σ → σ → (c(I, R) →L[R] c(I, R))) :
    c(σ × I, R) →L[R] c(σ × I, R) :=
  ∑ a : σ, ∑ b : σ, (cSpace.blockIncl a).comp ((T a b).comp (cSpace.blockProj b))

omit [DecidableEq I] in
/-- Feeding the `b`-component into a block operator: only the `b`-column survives. -/
theorem blockOp_blockIncl (T : σ → σ → (c(I, R) →L[R] c(I, R))) (b : σ) (f : c(I, R)) :
    blockOp T (cSpace.blockIncl b f) = ∑ a : σ, cSpace.blockIncl a ((T a b) f) := by
  have hterm : ∀ a b' : σ,
      ((cSpace.blockIncl a).comp ((T a b').comp (cSpace.blockProj b'))) (cSpace.blockIncl b f)
        = if b' = b then cSpace.blockIncl a ((T a b) f) else 0 := by
    intro a b'
    show cSpace.blockIncl a ((T a b') (cSpace.blockProj b' (cSpace.blockIncl b f))) = _
    rw [cSpace.blockProj_blockIncl]
    by_cases hb : b' = b
    · subst hb
      rw [if_pos rfl, if_pos rfl]
    · rw [if_neg hb, if_neg hb, map_zero, map_zero]
  rw [blockOp, _root_.sum_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [_root_.sum_apply]
  simp only [hterm, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- The matrix of a block operator is read off blockwise. -/
@[simp] theorem matrixCoeff_blockOp (T : σ → σ → (c(I, R) →L[R] c(I, R)))
    (a b : σ) (j i : I) :
    matrixCoeff (blockOp T) (a, j) (b, i) = matrixCoeff (T a b) j i := by
  show blockOp T (cSpace.single (b, i) 1) (a, j) = _
  rw [← cSpace.blockIncl_single b i (1 : R), blockOp_blockIncl, cSpace.sum_apply]
  simp only [cSpace.blockIncl_apply, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rfl

/-- The `(a, a)` diagonal corner of an operator on `c(σ × I, R)`, as an operator on
`c(I, R)`. -/
noncomputable def blockCorner (u : c(σ × I, R) →L[R] c(σ × I, R)) (a : σ) :
    c(I, R) →L[R] c(I, R) :=
  (cSpace.blockProj a).comp (u.comp (cSpace.blockIncl a))

/-- The matrix of a diagonal corner is the corresponding diagonal block of the matrix
of `u`. -/
@[simp] theorem matrixCoeff_blockCorner (u : c(σ × I, R) →L[R] c(σ × I, R)) (a : σ)
    (j i : I) : matrixCoeff (blockCorner u a) j i = matrixCoeff u (a, j) (a, i) := by
  show cSpace.blockProj a (u (cSpace.blockIncl a (cSpace.single i 1))) j = _
  rw [cSpace.blockIncl_single]
  rfl

/-- The diagonal corners of `blockOp T` are the diagonal entries of `T`. -/
@[simp] theorem blockCorner_blockOp (T : σ → σ → (c(I, R) →L[R] c(I, R))) (a : σ) :
    blockCorner (blockOp T) a = T a a :=
  ext_matrixCoeff fun j i => by rw [matrixCoeff_blockCorner, matrixCoeff_blockOp]

/-- (`[IsTate R]`: as for `isCompactoid_restrictOp`, comparing the row sup of `blockOp T`
with the block row sups needs the rows of the blocks to be bounded.) -/
theorem isCompactoid_blockOp [IsTate R] {T : σ → σ → (c(I, R) →L[R] c(I, R))}
    (hT : ∀ a b, IsCompactoid (T a b)) : IsCompactoid (blockOp T) := by
  have hle : ∀ x : σ × I, rowNorm (blockOp T) x ≤ ∑ b : σ, rowNorm (T x.1 b) x.2 := by
    rintro ⟨a, j⟩
    simp only [rowNorm]
    refine Real.iSup_le (fun y => ?_) (Finset.sum_nonneg fun b _ => rowNorm_nonneg _ _)
    obtain ⟨b, i⟩ := y
    rw [matrixCoeff_blockOp]
    exact (norm_matrixCoeff_le_rowNorm_of_isTate (T a b) j i).trans
      (Finset.single_le_sum (f := fun b : σ => rowNorm (T a b) j)
        (fun b _ => rowNorm_nonneg _ _) (Finset.mem_univ b))
  refine squeeze_zero (fun x => rowNorm_nonneg _ x) hle
    (tendsto_cofinite_prod_of_finite fun a => ?_)
  simpa using tendsto_finsetSum (Finset.univ : Finset σ) fun b _ => hT a b

/-- Block operators compose like matrices of operators. -/
theorem blockOp_comp (T S : σ → σ → (c(I, R) →L[R] c(I, R))) :
    (blockOp T).comp (blockOp S) =
      blockOp (fun a c => ∑ b : σ, (T a b).comp (S b c)) := by
  refine ext_matrixCoeff fun x y => ?_
  obtain ⟨a, j⟩ := x
  obtain ⟨c, i⟩ := y
  have hlhs : matrixCoeff ((blockOp T).comp (blockOp S)) (a, j) (c, i)
      = ∑ b : σ, ((T a b) ((S b c) (cSpace.single i 1))) j := by
    show blockOp T (blockOp S (cSpace.single (c, i) (1 : R))) (a, j) = _
    rw [← cSpace.blockIncl_single c i (1 : R), blockOp_blockIncl, map_sum, cSpace.sum_apply]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [blockOp_blockIncl, cSpace.sum_apply]
    simp only [cSpace.blockIncl_apply, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [hlhs]
  simp only [matrixCoeff_blockOp, matrixCoeff_sum]
  rfl

/-- The Fredholm determinant of an operator on the trivial model space is `1` (there are no
nonempty index sets, so every higher coefficient vanishes). -/
private theorem charPowerSeries_of_isEmpty {A : Type*} [DecidableEq A] [IsEmpty A]
    (u : c(A, R) →L[R] c(A, R)) : charPowerSeries u = 1 := by
  refine PowerSeries.ext fun n => ?_
  rw [charPowerSeries_coeff, PowerSeries.coeff_one]
  cases n with
  | zero => rw [charCoeff_zero, if_pos rfl]
  | succ n =>
    have : IsEmpty {S : Finset A // S.card = n + 1} :=
      ⟨fun S => Nat.succ_ne_zero n (by
        have h := S.2
        rwa [Finset.eq_empty_of_isEmpty (S : Finset A), Finset.card_empty, eq_comm] at h)⟩
    rw [if_neg (Nat.succ_ne_zero n), charCoeff, tsum_empty, mul_zero]

/-- The induction behind `charPowerSeries_blockDiag`: peel off one block with Serre's
partition lemma (`charPowerSeries_partition` at `p := (·.1 = a₀)`, whose hypothesis holds in
both orientations for a block-diagonal operator), identify the two corners by reindexing
(`charPowerSeries_reindexOp`), and recurse on the smaller index type. -/
private theorem charPowerSeries_blockDiag_aux [IsTate R] (m : ℕ) :
    ∀ (τ : Type*) [Fintype τ] [DecidableEq τ], Fintype.card τ = m →
      ∀ u : c(τ × I, R) →L[R] c(τ × I, R), IsCompactoid u →
        (∀ (a b : τ) (j i : I), a ≠ b → matrixCoeff u (a, j) (b, i) = 0) →
        charPowerSeries u = ∏ a : τ, charPowerSeries (blockCorner u a) := by
  induction m with
  | zero =>
    intro τ _ _ hcard u _ _
    haveI : IsEmpty τ := Fintype.card_eq_zero_iff.1 hcard
    haveI : IsEmpty (τ × I) := inferInstance
    rw [charPowerSeries_of_isEmpty u, Finset.univ_eq_empty, Finset.prod_empty]
  | succ m ih =>
    intro τ _ _ hcard u hu hdiag
    obtain ⟨a₀⟩ : Nonempty τ := Fintype.card_pos_iff.1 (by omega)
    have htri : ∀ j i : τ × I, i.1 = a₀ → ¬ (j.1 = a₀) → matrixCoeff u j i = 0 := by
      rintro ⟨a, j⟩ ⟨b, i⟩ hi hj
      exact hdiag a b j i fun h => hj (h.trans hi)
    have hsplit := charPowerSeries_partition (fun x : τ × I => x.1 = a₀) hu htri
    -- the `a₀`-corner
    let e₁ : {x : τ × I // x.1 = a₀} ≃ I :=
      { toFun := fun x => x.1.2
        invFun := fun i => ⟨(a₀, i), rfl⟩
        left_inv := by rintro ⟨⟨a, i⟩, rfl⟩; rfl
        right_inv := fun _ => rfl }
    have hleft : reindexOp e₁ (restrictOp (fun x : τ × I => x.1 = a₀) u) = blockCorner u a₀ :=
      ext_matrixCoeff fun j i => by
        rw [matrixCoeff_reindexOp, matrixCoeff_restrictOp, matrixCoeff_blockCorner]
        rfl
    have hL : charPowerSeries (restrictOp (fun x : τ × I => x.1 = a₀) u)
        = charPowerSeries (blockCorner u a₀) := by
      rw [← hleft, charPowerSeries_reindexOp]
    -- the complementary corner, transported to `{b // ¬ (b = a₀)} × I`
    let e₂ : {x : τ × I // ¬ (x.1 = a₀)} ≃ ({b : τ // ¬ (b = a₀)} × I) :=
      { toFun := fun x => (⟨x.1.1, x.2⟩, x.1.2)
        invFun := fun z => ⟨(z.1.1, z.2), z.1.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    set v := reindexOp e₂ (restrictOp (fun x : τ × I => ¬ (x.1 = a₀)) u) with hv
    have hvcomp : IsCompactoid v := isCompactoid_reindexOp e₂ (isCompactoid_restrictOp hu)
    have hdiag' : ∀ (a b : {b : τ // ¬ (b = a₀)}) (j i : I), a ≠ b →
        matrixCoeff v (a, j) (b, i) = 0 := by
      intro a b j i hab
      rw [hv, matrixCoeff_reindexOp, matrixCoeff_restrictOp]
      exact hdiag a.1 b.1 j i fun h => hab (Subtype.ext h)
    have hcard' : Fintype.card {b : τ // ¬ (b = a₀)} = m := by
      rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, hcard]
      omega
    have hcorner : ∀ b : {b : τ // ¬ (b = a₀)}, blockCorner v b = blockCorner u (b : τ) :=
      fun b => ext_matrixCoeff fun j i => by
        rw [matrixCoeff_blockCorner, hv, matrixCoeff_reindexOp, matrixCoeff_restrictOp,
          matrixCoeff_blockCorner]
        rfl
    have hR : charPowerSeries (restrictOp (fun x : τ × I => ¬ (x.1 = a₀)) u)
        = ∏ b : {b : τ // ¬ (b = a₀)}, charPowerSeries (blockCorner u (b : τ)) := by
      rw [← charPowerSeries_reindexOp e₂ (restrictOp (fun x : τ × I => ¬ (x.1 = a₀)) u), ← hv,
        ih {b : τ // ¬ (b = a₀)} hcard' v hvcomp hdiag']
      exact Finset.prod_congr rfl fun b _ => by rw [hcorner b]
    have hprod : ∏ b : {b : τ // ¬ (b = a₀)}, charPowerSeries (blockCorner u (b : τ))
        = ∏ a ∈ Finset.univ.erase a₀, charPowerSeries (blockCorner u a) :=
      (Finset.prod_subtype (Finset.univ.erase a₀)
        (fun x => ⟨fun h => (Finset.mem_erase.1 h).1, fun h =>
          Finset.mem_erase.2 ⟨h, Finset.mem_univ x⟩⟩)
        (fun a => charPowerSeries (blockCorner u a))).symm
    rw [hsplit, hL, hR, hprod]
    exact Finset.mul_prod_erase Finset.univ (fun a => charPowerSeries (blockCorner u a))
      (Finset.mem_univ a₀)

/-- **Multiplicativity over a block-diagonal decomposition** ([Jacobs, Lemma 1.15]
iterated; the form consumed on pp. 32–34): the Fredholm determinant of a compactoid
block-diagonal operator is the product of the block determinants.

(`[IsTate R]`, inherited from `charPowerSeries_partition` / `isCompactoid_restrictOp`.) -/
theorem charPowerSeries_blockDiag [IsTate R] {u : c(σ × I, R) →L[R] c(σ × I, R)}
    (hu : IsCompactoid u)
    (hdiag : ∀ a b j i, a ≠ b → matrixCoeff u (a, j) (b, i) = 0) :
    charPowerSeries u = ∏ a : σ, charPowerSeries (blockCorner u a) :=
  charPowerSeries_blockDiag_aux (Fintype.card σ) σ rfl u hu hdiag

section Twist

/-!
### Coboundary twists

A block matrix may be renormalised by rescaling the coordinate of each component: the
`(a, b)` block picks up the scalar `ψ a · φ b` where `φ a · ψ a = 1` — a *coboundary*.
Such a twist is conjugation by the invertible blockwise-scalar diagonal `Δ = diag (φ a)`,
so by the trace property (`charPowerSeries_comm`) the Fredholm determinant — hence every
eigenvalue and Newton-polygon slope — is unchanged.  Invariantly: the determinant is
built from closed cycles of blocks, and every closed cycle product of coboundary scalars
telescopes to `1`.

This is the lemma behind the determinant-twist bookkeeping of the `U₃` identification
(`PhD/Jacobs/U3/Factorisations.lean`, "Handedness normalisation", and
`PhD/Jacobs/U3/Matrix.lean`): the block matrix assembled from the left-handed
certificates differs from the transcribed `ε`-matrix by exactly such a coboundary, so
the slope theory computed for the transcribed matrix applies to it verbatim.
-/

private theorem diagBlock_comp_blockOp (φ : σ → R)
    (T : σ → σ → (c(I, R) →L[R] c(I, R))) :
    (blockOp fun a b => if a = b then φ a • ContinuousLinearMap.id R (c(I, R)) else 0).comp
        (blockOp T)
      = blockOp fun a c => φ a • T a c := by
  rw [blockOp_comp]
  congr 1
  funext a c
  rw [Finset.sum_eq_single a
      (fun b _ hba => by rw [if_neg (Ne.symm hba), ContinuousLinearMap.zero_comp])
      (fun ha => absurd (Finset.mem_univ a) ha),
    if_pos rfl, ContinuousLinearMap.smul_comp, ContinuousLinearMap.id_comp]

private theorem blockOp_comp_diagBlock (T : σ → σ → (c(I, R) →L[R] c(I, R)))
    (φ : σ → R) :
    (blockOp T).comp
        (blockOp fun a b => if a = b then φ a • ContinuousLinearMap.id R (c(I, R)) else 0)
      = blockOp fun a c => φ c • T a c := by
  rw [blockOp_comp]
  congr 1
  funext a c
  rw [Finset.sum_eq_single c
      (fun b _ hbc => by rw [if_neg hbc, ContinuousLinearMap.comp_zero])
      (fun hc => absurd (Finset.mem_univ c) hc), if_pos rfl]
  refine ContinuousLinearMap.ext fun f => ?_
  simp only [ContinuousLinearMap.comp_apply, smul_apply, ContinuousLinearMap.id_apply,
    map_smul]

/-- **Coboundary invariance of the Fredholm determinant.**  Twisting the blocks of a
compactoid block operator by scalars of coboundary shape — the `(a, b)` block multiplied
by `ψ a · φ b` with `φ a · ψ a = 1` — leaves `charPowerSeries` unchanged: the twist is
conjugation by the blockwise-scalar diagonal `Δ = diag (φ a)`, which the trace property
(`charPowerSeries_comm`) cancels against `Δ⁻¹ = diag (ψ a)`.

Consequently a coboundary twist cannot move eigenvalues or Newton-polygon slopes; only a
twist that fails to factor as `ψ a · φ b` (equivalently, one with a nontrivial closed
cycle product) would change the spectral theory.  Section header for the motivating
application (`U₃`). -/
theorem charPowerSeries_blockOp_twist [IsTate R] {T : σ → σ → (c(I, R) →L[R] c(I, R))}
    (φ ψ : σ → R) (hφψ : ∀ a, φ a * ψ a = 1) (hT : IsCompactoid (blockOp T)) :
    charPowerSeries (blockOp fun a b => (ψ a * φ b) • T a b)
      = charPowerSeries (blockOp T) := by
  set Δ : c(σ × I, R) →L[R] c(σ × I, R) :=
    blockOp fun a b => if a = b then φ a • ContinuousLinearMap.id R (c(I, R)) else 0
    with hΔ
  set Δ' : c(σ × I, R) →L[R] c(σ × I, R) :=
    blockOp fun a b => if a = b then ψ a • ContinuousLinearMap.id R (c(I, R)) else 0
    with hΔ'
  have hcomm := charPowerSeries_comm (Δ'.comp (blockOp T)) Δ (hT.comp_left Δ')
  have hL : (Δ'.comp (blockOp T)).comp Δ = blockOp fun a b => (ψ a * φ b) • T a b := by
    rw [hΔ', diagBlock_comp_blockOp, hΔ, blockOp_comp_diagBlock]
    congr 1
    funext a b
    simp only [smul_smul]
    rw [mul_comm (φ b) (ψ a)]
  have hR : Δ.comp (Δ'.comp (blockOp T)) = blockOp T := by
    rw [hΔ', diagBlock_comp_blockOp, hΔ, diagBlock_comp_blockOp]
    congr 1
    funext a b
    simp only [smul_smul, hφψ, one_smul]
  rw [hL, hR] at hcomm
  exact hcomm

end Twist

end Block

end TateFredholm
