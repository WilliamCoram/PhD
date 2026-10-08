/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.TauCeti.Code.RigidAnalyticGeometry.Affinoid.Continuity

/-!
# Generalised rings of fractions

For an affinoid Banach algebra `A` and elements `f₁, …, fₘ, g₁, …, gₙ ∈ A` the generalised ring of
fractions is `A⟨f, g⁻¹⟩ := A⟨X, Y⟩ ⧸ (Xᵢ − fᵢ, gⱼYⱼ − 1)` (BGR 6.1.4/2, the second construction),
the universal `K`-Banach algebra over `A` in which the `gⱼ` become units and the `fᵢ`, `gⱼ⁻¹` are
power-bounded (BGR 6.1.4/1). For `f₁, …, fₘ, g` generating the unit ideal,
`A⟨f/g⟩ := A⟨X⟩ ⧸ (gXᵢ − fᵢ)` is the universal Banach algebra in which `g` is a unit and the `fᵢ/g`
are power-bounded
(BGR 6.1.4/3–4). Both are characterised by their universal properties (`IsGeneralisedFractions`,
`IsRationalFractions`), which gives associativity and the comparison with units, and both are
affinoid. The algebraic ring of fractions `A[g⁻¹]` is dense in `A⟨f/g⟩`.

⚠ Deviation from roadmap §1.4.2: the completion model `A⟨f, g⁻¹⟩ = completion of A[g⁻¹]` for the
seminorm `inf max |a_{μν}|` (BGR 6.1.4, before 6.1.4/1) is not built; only the presentation model
is, together with the density of `A[g⁻¹]`. §1.4.3–1.4.4 (identification with the adic-spaces
roadmap's `A⟨T/s⟩`, flatness) are not on this board, since that chain is not in this repository.

Roadmap: `PhD/TauCeti/Roadmaps/RigidAnalyticGeometry/README.md`, §1.4.1–1.4.2. Tau Ceti home:
`TauCeti/RingTheory/Affinoid/Fractions.lean`.

## Main definitions and results

* `Affinoid.IsGeneralisedFractions`, `Affinoid.IsRationalFractions` — the universal properties
  of BGR 6.1.4/1 and 6.1.4/3.
* `Affinoid.GeneralisedFractions A f g`, `Affinoid.RationalFractions A f g` — the models by
  presentations, with `isGeneralisedFractions_toFractions` (BGR 6.1.4/1–2) and
  `isRationalFractions_toRational` (BGR 6.1.4/3–4).
* `Affinoid.IsGeneralisedFractions.trans` — associativity (BGR 6.1.4/2).
* `Affinoid.IsGeneralisedFractions.of_isUnit` — `A⟨h⁻¹⟩ = A` for a unit `h` with power-bounded
  inverse (BGR 6.1.4, "both definitions coincide in this special case").
* `Affinoid.toRational_mul_inv` — `X̄ᵢ = fᵢ / g` in `A⟨f/g⟩`.
* `Affinoid.denseRange_awayLift` — `A[g⁻¹]` is dense in `A⟨f/g⟩`.
-/

open MvPowerSeries MvPowerSeries.Restricted PowerBounded

universe v

namespace Affinoid

/-! ### The universal properties -/

section Predicates

variable {K : Type*} [NontriviallyNormedField K]
  {A : Type*} [NormedCommRing A] [NormedAlgebra K A] [IsUltrametricDist A] [CompleteSpace A]
  {A' : Type*} [NormedCommRing A'] [NormedAlgebra K A'] [IsUltrametricDist A'] [CompleteSpace A']

/-- `φ₀ : A → A'` makes `A'` a **generalised ring of fractions** `A⟨f, g⁻¹⟩` of `A` if `φ₀` is
continuous, the `φ₀ (g j)` are units, the `φ₀ (f i)` and the `φ₀ (g j)⁻¹` are power-bounded, and
`φ₀` is universal among such continuous homomorphisms into `K`-Banach algebras.
Source: BGR 6.1.4/1 ("Let `φ : A → B` denote a continuous homomorphism … such that the elements
`φ(gⱼ)` are units and the elements `φ(fᵢ)`, `φ(gⱼ)⁻¹` are power-bounded. Then there is a unique
continuous homomorphism `φ′ : A⟨f, g⁻¹⟩ → B` such that the diagram commutes"). -/
structure IsGeneralisedFractions (φ₀ : A →ₐ[K] A') {m n : ℕ} (f : Fin m → A) (g : Fin n → A) :
    Prop where
  continuous : Continuous φ₀
  isUnit : ∀ j, IsUnit (φ₀ (g j))
  isPowerBounded_f : ∀ i, IsPowerBounded (φ₀ (f i))
  isPowerBounded_inv : ∀ j, IsPowerBounded (↑(isUnit j).unit⁻¹ : A')
  existsUnique_lift : ∀ {B : Type v} [NormedCommRing B] [NormedAlgebra K B] [IsUltrametricDist B]
    [CompleteSpace B] (φ : A →ₐ[K] B), Continuous φ → ∀ (hg : ∀ j, IsUnit (φ (g j))),
    (∀ i, IsPowerBounded (φ (f i))) → (∀ j, IsPowerBounded (↑(hg j).unit⁻¹ : B)) →
      ∃! φ' : A' →ₐ[K] B, Continuous φ' ∧ φ'.comp φ₀ = φ

/-- `φ₀ : A → A'` makes `A'` the **rational ring of fractions** `A⟨f/g⟩` of `A` if `φ₀` is
continuous, `φ₀ g` is a unit, the `φ₀ (f i) / φ₀ g` are power-bounded, and `φ₀` is universal among
such continuous homomorphisms into `K`-Banach algebras. Source: BGR 6.1.4/3. -/
structure IsRationalFractions (φ₀ : A →ₐ[K] A') {m : ℕ} (f : Fin m → A) (g : A) : Prop where
  continuous : Continuous φ₀
  isUnit : IsUnit (φ₀ g)
  isPowerBounded_div : ∀ i, IsPowerBounded (φ₀ (f i) * ↑isUnit.unit⁻¹)
  existsUnique_lift : ∀ {B : Type v} [NormedCommRing B] [NormedAlgebra K B] [IsUltrametricDist B]
    [CompleteSpace B] (φ : A →ₐ[K] B), Continuous φ → ∀ (hg : IsUnit (φ g)),
    (∀ i, IsPowerBounded (φ (f i) * ↑hg.unit⁻¹)) →
      ∃! φ' : A' →ₐ[K] B, Continuous φ' ∧ φ'.comp φ₀ = φ

variable {φ₀ : A →ₐ[K] A'} {m n : ℕ} {f : Fin m → A} {g : Fin n → A}

/-- Units with equal values have equal inverses. -/
private theorem val_inv_unit_eq {M : Type*} [Monoid M] {x y : M} (hx : IsUnit x) (hy : IsUnit y)
    (h : x = y) : (↑hx.unit⁻¹ : M) = ↑hy.unit⁻¹ := by
  subst h
  rfl

omit [IsUltrametricDist A] [CompleteSpace A] in
/-- **Uniqueness** of generalised rings of fractions: two of them are related by a unique continuous
isomorphism over `A`. Source: BGR 6.1.4 ("both algebras satisfy the same universal property"). -/
theorem IsGeneralisedFractions.exists_algEquiv {A' A'' : Type v} [NormedCommRing A']
    [NormedAlgebra K A'] [IsUltrametricDist A'] [CompleteSpace A'] [NormedCommRing A'']
    [NormedAlgebra K A''] [IsUltrametricDist A''] [CompleteSpace A''] {φ₀ : A →ₐ[K] A'}
    {φ₀' : A →ₐ[K] A''} (h : IsGeneralisedFractions.{v} φ₀ f g)
    (h' : IsGeneralisedFractions.{v} φ₀' f g) :
    ∃ e : A' ≃ₐ[K] A'', Continuous e ∧ Continuous e.symm ∧ e.toAlgHom.comp φ₀ = φ₀' := by
  obtain ⟨F, ⟨hF, hF₀⟩, -⟩ := h.existsUnique_lift φ₀' h'.continuous h'.isUnit
    h'.isPowerBounded_f h'.isPowerBounded_inv
  obtain ⟨G, ⟨hG, hG₀⟩, -⟩ := h'.existsUnique_lift φ₀ h.continuous h.isUnit
    h.isPowerBounded_f h.isPowerBounded_inv
  have hGF : G.comp F = AlgHom.id K A' := by
    obtain ⟨_, -, hu⟩ := h.existsUnique_lift φ₀ h.continuous h.isUnit
      h.isPowerBounded_f h.isPowerBounded_inv
    exact (hu _ ⟨hG.comp hF, by rw [AlgHom.comp_assoc, hF₀, hG₀]⟩).trans
      (hu _ ⟨continuous_id, AlgHom.id_comp _⟩).symm
  have hFG : F.comp G = AlgHom.id K A'' := by
    obtain ⟨_, -, hu⟩ := h'.existsUnique_lift φ₀' h'.continuous h'.isUnit
      h'.isPowerBounded_f h'.isPowerBounded_inv
    exact (hu _ ⟨hF.comp hG, by rw [AlgHom.comp_assoc, hG₀, hF₀]⟩).trans
      (hu _ ⟨continuous_id, AlgHom.id_comp _⟩).symm
  exact ⟨AlgEquiv.ofAlgHom F G hFG hGF, hF, hG, hF₀⟩

omit [IsUltrametricDist A] [CompleteSpace A] [IsUltrametricDist A'] [CompleteSpace A'] in
/-- **Associativity** (BGR 6.1.4/2): `A⟨f, g⁻¹⟩⟨f', g'⁻¹⟩ = A⟨f, f', g⁻¹, g'⁻¹⟩`, at the level of
universal properties. Source: BGR 6.1.4 ("it follows from Proposition 2 that we have associativity
in the following sense: `A⟨f₁, …, f_{m−1}, g₁⁻¹, …, g_{n−1}⁻¹⟩⟨f_m, gₙ⁻¹⟩ = A⟨f₁, …, f_m, g₁⁻¹, …,
gₙ⁻¹⟩`"). -/
theorem IsGeneralisedFractions.trans {A'' : Type*} [NormedCommRing A''] [NormedAlgebra K A'']
    {φ₁ : A' →ₐ[K] A''} {m' n' : ℕ} {f' : Fin m' → A}
    {g' : Fin n' → A} (h : IsGeneralisedFractions.{v} φ₀ f g)
    (h' : IsGeneralisedFractions.{v} φ₁ (φ₀ ∘ f') (φ₀ ∘ g')) :
    IsGeneralisedFractions.{v} (φ₁.comp φ₀) (Fin.append f f') (Fin.append g g') := by
  obtain ⟨C₁, hC₁⟩ := exists_forall_norm_le_mul_of_continuous φ₁ h'.continuous
  have hU : ∀ j, IsUnit ((φ₁.comp φ₀) (Fin.append g g' j)) := by
    intro j
    induction j using Fin.addCases with
    | left j₀ =>
      rw [Fin.append_left]
      exact (h.isUnit j₀).map φ₁
    | right j₁ =>
      rw [Fin.append_right]
      exact h'.isUnit j₁
  refine ⟨h'.continuous.comp h.continuous, hU, fun i ↦ ?_, fun j ↦ ?_, ?_⟩
  · induction i using Fin.addCases with
    | left i₀ =>
      rw [Fin.append_left]
      exact IsPowerBounded.map K (φ := φ₁.toRingHom) hC₁ (h.isPowerBounded_f i₀)
    | right i₁ =>
      rw [Fin.append_right]
      exact h'.isPowerBounded_f i₁
  · induction j using Fin.addCases with
    | left j₀ =>
      have hinv : (↑(hU (Fin.castAdd n' j₀)).unit⁻¹ : A'') = φ₁ ↑(h.isUnit j₀).unit⁻¹ :=
        Units.inv_eq_of_mul_eq_one_left (by
          rw [IsUnit.unit_spec, AlgHom.comp_apply, Fin.append_left, ← map_mul,
            IsUnit.val_inv_mul, map_one])
      rw [hinv]
      exact IsPowerBounded.map K (φ := φ₁.toRingHom) hC₁ (h.isPowerBounded_inv j₀)
    | right j₁ =>
      rw [val_inv_unit_eq (hU (Fin.natAdd n j₁)) (h'.isUnit j₁)
        (by rw [AlgHom.comp_apply, Fin.append_right]; rfl)]
      exact h'.isPowerBounded_inv j₁
  intro B _ _ _ _ φ hφ hg hf hg'
  have hg₀ : ∀ j₀, IsUnit (φ (g j₀)) := fun j₀ ↦ by
    simpa only [Fin.append_left] using hg (Fin.castAdd n' j₀)
  have hf₀ : ∀ i₀, IsPowerBounded (φ (f i₀)) := fun i₀ ↦ by
    simpa only [Fin.append_left] using hf (Fin.castAdd m' i₀)
  have hg'₀ : ∀ j₀, IsPowerBounded (↑(hg₀ j₀).unit⁻¹ : B) := fun j₀ ↦ by
    rw [← val_inv_unit_eq (hg (Fin.castAdd n' j₀)) (hg₀ j₀) (by rw [Fin.append_left])]
    exact hg' (Fin.castAdd n' j₀)
  obtain ⟨φ', ⟨hφ', hφ'₀⟩, hu⟩ := h.existsUnique_lift φ hφ hg₀ hf₀ hg'₀
  have hval : ∀ a, φ' (φ₀ a) = φ a := AlgHom.congr_fun hφ'₀
  have hg₁ : ∀ j₁, IsUnit (φ' ((φ₀ ∘ g') j₁)) := fun j₁ ↦ by
    rw [Function.comp_apply, hval, ← Fin.append_right g g' j₁]
    exact hg (Fin.natAdd n j₁)
  have hf₁ : ∀ i₁, IsPowerBounded (φ' ((φ₀ ∘ f') i₁)) := fun i₁ ↦ by
    rw [Function.comp_apply, hval, ← Fin.append_right f f' i₁]
    exact hf (Fin.natAdd m i₁)
  have hg'₁ : ∀ j₁, IsPowerBounded (↑(hg₁ j₁).unit⁻¹ : B) := fun j₁ ↦ by
    rw [← val_inv_unit_eq (hg (Fin.natAdd n j₁)) (hg₁ j₁)
      (by rw [Fin.append_right, Function.comp_apply, hval])]
    exact hg' (Fin.natAdd n j₁)
  obtain ⟨φ'', ⟨hφ'', hφ''₁⟩, hu'⟩ := h'.existsUnique_lift φ' hφ' hg₁ hf₁ hg'₁
  refine ⟨φ'', ⟨hφ'', by rw [← AlgHom.comp_assoc, hφ''₁, hφ'₀]⟩, fun χ ⟨hχ, hχ₀⟩ ↦ hu' χ
    ⟨hχ, hu (χ.comp φ₁) ⟨hχ.comp h'.continuous, by rw [AlgHom.comp_assoc]; exact hχ₀⟩⟩⟩

omit [IsUltrametricDist A] [CompleteSpace A] in
/-- When the `g j` are already units of `A` with power-bounded inverses and the `f i` are
power-bounded, `A` itself is `A⟨f, g⁻¹⟩`. Source: BGR 6.1.4 ("`A⟨h⁻¹⟩` is defined in two ways when
`h ∈ A` is a unit. However … both definitions coincide in this special case"). -/
theorem IsGeneralisedFractions.of_isUnit (hg : ∀ j, IsUnit (g j)) (hf : ∀ i, IsPowerBounded (f i))
    (hg' : ∀ j, IsPowerBounded (↑(hg j).unit⁻¹ : A)) :
    IsGeneralisedFractions.{v} (AlgHom.id K A) f g :=
  ⟨continuous_id, hg, hf, hg', fun φ hφ _ _ _ ↦ ⟨φ, ⟨hφ, AlgHom.comp_id φ⟩,
    fun χ ⟨_, hχ⟩ ↦ (AlgHom.comp_id χ).symm.trans hχ⟩⟩

omit [IsUltrametricDist A] [CompleteSpace A] [IsUltrametricDist A'] [CompleteSpace A'] in
/-- A rational ring of fractions with denominator `1` is the generalised ring of fractions with no
denominators. Source: BGR 6.1.4 ("our definition of `A⟨f/g⟩` is compatible with the one given
before, if the `fᵢ` or `g` are units"). -/
theorem IsRationalFractions.isGeneralisedFractions_of_one (h : IsRationalFractions.{v} φ₀ f 1) :
    IsGeneralisedFractions.{v} φ₀ f (Fin.elim0 : Fin 0 → A) := by
  have hu : h.isUnit.unit = 1 := Units.ext (h.isUnit.unit_spec.trans (map_one φ₀))
  refine ⟨h.continuous, fun j ↦ j.elim0, fun i ↦ ?_, fun j ↦ j.elim0, ?_⟩
  · simpa [hu] using h.isPowerBounded_div i
  · intro B _ _ _ _ φ hφ _ hf _
    have hg1 : IsUnit (φ 1) := by
      rw [map_one]
      exact isUnit_one
    have hu1 : hg1.unit = 1 := Units.ext (hg1.unit_spec.trans (map_one φ))
    exact h.existsUnique_lift φ hφ hg1 fun i ↦ by
      rw [hu1, inv_one, Units.val_one, mul_one]
      exact hf i

end Predicates

/-! ### The models by presentations -/

section GeneralisedFractions

variable (K : Type*) [NontriviallyNormedField K]
  (A : Type*) [NormedCommRing A] [NormedAlgebra K A] [IsUltrametricDist A] [CompleteSpace A]
  {m n : ℕ} (f : Fin m → A) (g : Fin n → A)

/-- The ideal `(Xᵢ − fᵢ, gⱼYⱼ − 1)` of `A⟨X, Y⟩`. Source: BGR 6.1.4
("`A′ := A⟨X, Y⟩/(X − f, gY − 1)`"). -/
noncomputable def fractionIdeal : Ideal (Restricted A (1 : Fin m ⊕ Fin n → ℝ)) :=
  Ideal.span (Set.range (fun i ↦ X A (1 : Fin m ⊕ Fin n → ℝ) (Sum.inl i) - C _ (f i)) ∪
    Set.range fun j ↦ C _ (g j) * X A (1 : Fin m ⊕ Fin n → ℝ) (Sum.inr j) - 1)

/-- **The generalised ring of fractions** `A⟨f, g⁻¹⟩ := A⟨X, Y⟩ ⧸ (Xᵢ − fᵢ, gⱼYⱼ − 1)`, with the
residue seminorm. Source: BGR 6.1.4/2; roadmap §1.4.1. -/
abbrev GeneralisedFractions : Type _ :=
  Restricted A (1 : Fin m ⊕ Fin n → ℝ) ⧸ fractionIdeal A f g

/-- The canonical map `A → A⟨f, g⁻¹⟩`. -/
noncomputable def toFractions : A →ₐ[K] GeneralisedFractions A f g :=
  (Ideal.Quotient.mkₐ K _).comp (IsScalarTower.toAlgHom K A _)

omit [CompleteSpace A] in
theorem continuous_toFractions : Continuous (toFractions K A f g) :=
  continuous_quot_mk.comp (continuous_algebraMap_restricted _)

omit [CompleteSpace A] in
/-- The residue classes of the `Yⱼ` invert the `gⱼ`. -/
theorem toFractions_mul_mk_X_inr (j : Fin n) :
    toFractions K A f g (g j) * Ideal.Quotient.mk _ (X A (1 : Fin m ⊕ Fin n → ℝ) (Sum.inr j)) =
      1 := by
  have h1 : toFractions K A f g (g j) =
      Ideal.Quotient.mk _ (C (1 : Fin m ⊕ Fin n → ℝ) (g j)) :=
    congrArg (Ideal.Quotient.mk _) (algebraMap_apply _ (g j))
  rw [h1, ← map_mul, ← map_one (Ideal.Quotient.mk (fractionIdeal A f g)), Ideal.Quotient.eq]
  exact Ideal.subset_span (Set.mem_union_right _ ⟨j, rfl⟩)

omit [CompleteSpace A] in
theorem isUnit_toFractions (j : Fin n) : IsUnit (toFractions K A f g (g j)) :=
  IsUnit.of_mul_eq_one _ (toFractions_mul_mk_X_inr K A f g j)

omit [CompleteSpace A] in
/-- The `fᵢ` are the residue classes of the `Xᵢ`, hence power-bounded. -/
theorem toFractions_f (i : Fin m) :
    toFractions K A f g (f i) = Ideal.Quotient.mk _ (X A (1 : Fin m ⊕ Fin n → ℝ) (Sum.inl i)) := by
  refine (congrArg (Ideal.Quotient.mk _) (algebraMap_apply _ (f i))).trans (Ideal.Quotient.eq.2 ?_)
  rw [← neg_sub]
  exact (Ideal.neg_mem_iff _).2 (Ideal.subset_span (Set.mem_union_left _ ⟨i, rfl⟩))

omit [CompleteSpace A] in
theorem isPowerBounded_toFractions_f (i : Fin m) : IsPowerBounded (toFractions K A f g (f i)) := by
  rw [toFractions_f]
  have hb : ∀ x, ‖Ideal.Quotient.mk (fractionIdeal A f g) x‖ ≤ 1 * ‖x‖ := fun x ↦ by
    rw [one_mul]; exact Ideal.Quotient.norm_mk_le _ x
  exact IsPowerBounded.map K (C := 1) (φ := Ideal.Quotient.mk (fractionIdeal A f g)) hb
    (isPowerBounded_X (A := A) (Sum.inl i : Fin m ⊕ Fin n))

omit [CompleteSpace A] in
theorem isPowerBounded_inv_toFractions (j : Fin n) :
    IsPowerBounded (↑(isUnit_toFractions K A f g j).unit⁻¹ : GeneralisedFractions A f g) := by
  rw [Units.inv_eq_of_mul_eq_one_right (by
    rw [IsUnit.unit_spec]
    exact toFractions_mul_mk_X_inr K A f g j)]
  have hb : ∀ x, ‖Ideal.Quotient.mk (fractionIdeal A f g) x‖ ≤ 1 * ‖x‖ := fun x ↦ by
    rw [one_mul]; exact Ideal.Quotient.norm_mk_le _ x
  exact IsPowerBounded.map K (C := 1) (φ := Ideal.Quotient.mk (fractionIdeal A f g)) hb
    (isPowerBounded_X (A := A) (Sum.inr j : Fin m ⊕ Fin n))

/-- **BGR 6.1.4/1–2**: `A⟨X, Y⟩ ⧸ (X − f, gY − 1)` has the universal property of `A⟨f, g⁻¹⟩`.
Source: BGR 6.1.4 ("the canonical map `A → A⟨X, Y⟩/(X − f, gY − 1)` also satisfies the universal
property stated in Proposition 1. Namely, let `φ : A → B` be a continuous homomorphism as in
Proposition 1. Then `φ` extends to a continuous homomorphism `φ″ : A⟨X, Y⟩ → B`, `X ↦ φ(f)`,
`Y ↦ φ(g)⁻¹`, with `(X − f, gY − 1) ⊂ ker φ″`"), for `A` affinoid (so that the ideal is closed and
the quotient is a Banach algebra). -/
theorem isGeneralisedFractions_toFractions [IsUltrametricDist K] [CompleteSpace K] [NormOneClass A]
    (hA : IsAffinoidAlgebra K A) :
    haveI : IsClosed ((fractionIdeal A f g : Ideal _) :
        Set (Restricted A (1 : Fin m ⊕ Fin n → ℝ))) := hA.restricted.isClosed_ideal _
    IsGeneralisedFractions.{v} (toFractions K A f g) f g := by
  haveI : IsClosed ((fractionIdeal A f g : Ideal _) :
      Set (Restricted A (1 : Fin m ⊕ Fin n → ℝ))) := hA.restricted.isClosed_ideal _
  refine ⟨continuous_toFractions K A f g, isUnit_toFractions K A f g,
    isPowerBounded_toFractions_f K A f g, isPowerBounded_inv_toFractions K A f g, ?_⟩
  intro B _ _ _ _ φ hφ hg hf hg'
  -- the extension `X ↦ f`, `Y ↦ g⁻¹` of BGR 6.1.4/1
  let b : Fin m ⊕ Fin n → B := Sum.elim (fun i ↦ φ (f i)) fun j ↦ ↑(hg j).unit⁻¹
  have hb : ∀ k, IsPowerBounded (b k) := by
    rintro (i | j)
    · exact hf i
    · exact hg' j
  let φ'' := extendAlgHom φ hφ b hb
  have hφ'' : Continuous φ'' := continuous_extendAlgHom φ hφ b hb
  have hC : ∀ a, φ'' (C (1 : Fin m ⊕ Fin n → ℝ) a) = φ a := extendAlgHom_C φ hφ b hb
  have hX : ∀ k, φ'' (X A (1 : Fin m ⊕ Fin n → ℝ) k) = b k := extendAlgHom_X φ hφ b hb
  -- it kills `(X − f, gY − 1)`
  have hker : fractionIdeal A f g ≤ RingHom.ker φ'' := by
    refine Ideal.span_le.2 (Set.union_subset ?_ ?_)
    · rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, RingHom.mem_ker, map_sub, hX, hC]
      exact sub_self _
    · rintro _ ⟨j, rfl⟩
      rw [SetLike.mem_coe, RingHom.mem_ker, map_sub, map_mul, hX, hC, map_one]
      exact sub_eq_zero.2 (hg j).mul_val_inv
  let F := Ideal.Quotient.liftₐ _ φ'' fun x hx ↦ RingHom.mem_ker.1 (hker hx)
  refine ⟨F, ⟨?_, AlgHom.ext fun a ↦ (congrArg φ'' (algebraMap_apply _ a)).trans (hC a)⟩, ?_⟩
  · exact (QuotientAddGroup.isQuotientMap_mk (fractionIdeal A f g).toAddSubgroup).continuous_iff.2
      hφ''
  · rintro χ ⟨hχ, hχ₀⟩
    refine Ideal.Quotient.algHom_ext K (.trans ?_ (Ideal.Quotient.liftₐ_comp _ φ'' _).symm)
    refine AlgHom.coe_ringHom_injective (ringHom_ext_of_continuous
      (hχ.comp continuous_quot_mk) hφ'' (fun a ↦ ?_) ?_)
    · exact (congrArg (fun x ↦ χ (Ideal.Quotient.mk _ x)) (algebraMap_apply _ a).symm).trans
        ((AlgHom.congr_fun hχ₀ a).trans (hC a).symm)
    · rintro (i | j)
      · exact (congrArg χ (toFractions_f K A f g i).symm).trans
          ((AlgHom.congr_fun hχ₀ (f i)).trans (hX (Sum.inl i)).symm)
      · have h1 : χ (Ideal.Quotient.mk _ (X A (1 : Fin m ⊕ Fin n → ℝ) (Sum.inr j))) * φ (g j) =
            1 := by
          rw [← AlgHom.congr_fun hχ₀ (g j), AlgHom.comp_apply, ← map_mul, mul_comm,
            toFractions_mul_mk_X_inr, map_one]
        exact (Units.eq_inv_of_mul_eq_one_right (by rw [IsUnit.unit_spec]; exact h1)).trans
          (hX (Sum.inr j)).symm

/-- `A⟨f, g⁻¹⟩` is affinoid for `A` affinoid. Source: BGR 6.1.4 ("In particular, it is now clear
that `A⟨f, g⁻¹⟩` is `k`-affinoid"). -/
theorem isAffinoidAlgebra_generalisedFractions [IsUltrametricDist K] [CompleteSpace K]
    [NormOneClass A] (hA : IsAffinoidAlgebra K A) :
    IsAffinoidAlgebra K (GeneralisedFractions A f g) :=
  hA.restricted.quotient _

end GeneralisedFractions

section RationalFractions

variable (K : Type*) [NontriviallyNormedField K]
  (A : Type*) [NormedCommRing A] [NormedAlgebra K A] [IsUltrametricDist A] [CompleteSpace A]
  {m : ℕ} (f : Fin m → A) (g : A)

/-- The ideal `(gXᵢ − fᵢ)` of `A⟨X⟩`. Source: BGR 6.1.4 ("the `k`-affinoid algebra
`A′ = A⟨X⟩/(gX − f)`"). -/
noncomputable def rationalIdeal : Ideal (Restricted A (1 : Fin m → ℝ)) :=
  Ideal.span (Set.range fun i ↦ C _ g * X A (1 : Fin m → ℝ) i - C _ (f i))

/-- **The rational ring of fractions** `A⟨f/g⟩ := A⟨X⟩ ⧸ (gXᵢ − fᵢ)`, with the residue seminorm.
Source: BGR 6.1.4/4; roadmap §1.4.2. -/
abbrev RationalFractions : Type _ :=
  Restricted A (1 : Fin m → ℝ) ⧸ rationalIdeal A f g

/-- The canonical map `A → A⟨f/g⟩`. -/
noncomputable def toRational : A →ₐ[K] RationalFractions A f g :=
  (Ideal.Quotient.mkₐ K _).comp (IsScalarTower.toAlgHom K A _)

omit [CompleteSpace A] in
theorem continuous_toRational : Continuous (toRational K A f g) :=
  continuous_quot_mk.comp (continuous_algebraMap_restricted _)

omit [CompleteSpace A] in
/-- `g X̄ᵢ = fᵢ` in `A⟨f/g⟩`. Source: BGR 6.1.4 (the relations `gXᵢ − fᵢ`). -/
theorem toRational_mul_mk_X (i : Fin m) :
    toRational K A f g g * Ideal.Quotient.mk _ (X A (1 : Fin m → ℝ) i) =
      toRational K A f g (f i) := by
  have h1 : ∀ a, toRational K A f g a = Ideal.Quotient.mk _ (C (1 : Fin m → ℝ) a) := fun a ↦
    congrArg (Ideal.Quotient.mk _) (algebraMap_apply _ a)
  rw [h1, h1, ← map_mul, Ideal.Quotient.eq]
  exact Ideal.subset_span ⟨i, rfl⟩

omit [CompleteSpace A] in
/-- `g` becomes a unit in `A⟨f/g⟩` when `f₁, …, fₘ, g` generate the unit ideal:
`(a + Σ aᵢ X̄ᵢ) g = a g + Σ aᵢ fᵢ = 1`. Source: BGR 6.1.4 ("which shows that `g` is a unit in
`A′`"). -/
theorem isUnit_toRational (hgen : ∃ (a : A) (a' : Fin m → A), a * g + ∑ i, a' i * f i = 1) :
    IsUnit (toRational K A f g g) := by
  obtain ⟨a, a', h⟩ := hgen
  refine IsUnit.of_mul_eq_one (toRational K A f g a +
    ∑ i, toRational K A f g (a' i) * Ideal.Quotient.mk _ (X A (1 : Fin m → ℝ) i)) ?_
  calc toRational K A f g g * (toRational K A f g a +
        ∑ i, toRational K A f g (a' i) * Ideal.Quotient.mk _ (X A (1 : Fin m → ℝ) i))
      = toRational K A f g a * toRational K A f g g + ∑ i, toRational K A f g (a' i) *
          (toRational K A f g g * Ideal.Quotient.mk _ (X A (1 : Fin m → ℝ) i)) := by
        rw [mul_add, Finset.mul_sum, mul_comm (toRational K A f g g) (toRational K A f g a)]
        exact congrArg _ (Finset.sum_congr rfl fun i _ ↦ mul_left_comm _ _ _)
    _ = toRational K A f g (a * g + ∑ i, a' i * f i) := by
        simp only [toRational_mul_mk_X, map_add, map_mul, map_sum]
    _ = 1 := by rw [h, map_one]

omit [CompleteSpace A] in
/-- `X̄ᵢ = fᵢ / g` in `A⟨f/g⟩`. Source: BGR 6.1.4 ("Moreover, `X̄ᵢ = fᵢ/g` in `A′`"). -/
theorem toRational_mul_inv (hgen : ∃ (a : A) (a' : Fin m → A), a * g + ∑ i, a' i * f i = 1)
    (i : Fin m) :
    toRational K A f g (f i) *
        (↑(isUnit_toRational K A f g hgen).unit⁻¹ : RationalFractions A f g) =
      Ideal.Quotient.mk _ (X A (1 : Fin m → ℝ) i) := by
  rw [← toRational_mul_mk_X, mul_comm (toRational K A f g g), mul_assoc, IsUnit.mul_val_inv,
    mul_one]

omit [CompleteSpace A] in
theorem isPowerBounded_toRational_div
    (hgen : ∃ (a : A) (a' : Fin m → A), a * g + ∑ i, a' i * f i = 1) (i : Fin m) :
    IsPowerBounded (toRational K A f g (f i) *
      (↑(isUnit_toRational K A f g hgen).unit⁻¹ : RationalFractions A f g)) := by
  rw [toRational_mul_inv K A f g hgen]
  have hb : ∀ x, ‖Ideal.Quotient.mk (rationalIdeal A f g) x‖ ≤ 1 * ‖x‖ := fun x ↦ by
    rw [one_mul]; exact Ideal.Quotient.norm_mk_le _ x
  exact IsPowerBounded.map K (C := 1) (φ := Ideal.Quotient.mk (rationalIdeal A f g)) hb
    (isPowerBounded_X (A := A) i)

/-- **BGR 6.1.4/3–4**: `A⟨X⟩ ⧸ (gX − f)` has the universal property of `A⟨f/g⟩`. Source: BGR 6.1.4
("It is now a straightforward verification to see that also `A′ = A⟨X⟩/(gX − f)` satisfies the
universal property stated in Proposition 3"). -/
theorem isRationalFractions_toRational [IsUltrametricDist K] [CompleteSpace K] [NormOneClass A]
    (hA : IsAffinoidAlgebra K A)
    (hgen : ∃ (a : A) (a' : Fin m → A), a * g + ∑ i, a' i * f i = 1) :
    haveI : IsClosed ((rationalIdeal A f g : Ideal _) : Set (Restricted A (1 : Fin m → ℝ))) :=
      hA.restricted.isClosed_ideal _
    IsRationalFractions.{v} (toRational K A f g) f g := by
  haveI : IsClosed ((rationalIdeal A f g : Ideal _) : Set (Restricted A (1 : Fin m → ℝ))) :=
    hA.restricted.isClosed_ideal _
  refine ⟨continuous_toRational K A f g, isUnit_toRational K A f g hgen,
    isPowerBounded_toRational_div K A f g hgen, ?_⟩
  intro B _ _ _ _ φ hφ hg hf
  -- the extension `Xᵢ ↦ fᵢ / g` of BGR 6.1.4/3
  let b : Fin m → B := fun i ↦ φ (f i) * ↑hg.unit⁻¹
  let φ'' := extendAlgHom φ hφ b hf
  have hφ'' : Continuous φ'' := continuous_extendAlgHom φ hφ b hf
  have hC : ∀ a, φ'' (C (1 : Fin m → ℝ) a) = φ a := extendAlgHom_C φ hφ b hf
  have hX : ∀ i, φ'' (X A (1 : Fin m → ℝ) i) = b i := extendAlgHom_X φ hφ b hf
  -- it kills `(gX − f)`
  have hker : rationalIdeal A f g ≤ RingHom.ker φ'' := by
    refine Ideal.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker, map_sub, map_mul, hX, hC, hC]
    change φ g * (φ (f i) * ↑hg.unit⁻¹) - φ (f i) = 0
    rw [mul_left_comm, IsUnit.mul_val_inv, mul_one, sub_self]
  let F := Ideal.Quotient.liftₐ _ φ'' fun x hx ↦ RingHom.mem_ker.1 (hker hx)
  refine ⟨F, ⟨?_, AlgHom.ext fun a ↦ (congrArg φ'' (algebraMap_apply _ a)).trans (hC a)⟩, ?_⟩
  · exact (QuotientAddGroup.isQuotientMap_mk (rationalIdeal A f g).toAddSubgroup).continuous_iff.2
      hφ''
  · rintro χ ⟨hχ, hχ₀⟩
    refine Ideal.Quotient.algHom_ext K (.trans ?_ (Ideal.Quotient.liftₐ_comp _ φ'' _).symm)
    refine AlgHom.coe_ringHom_injective (ringHom_ext_of_continuous
      (hχ.comp continuous_quot_mk) hφ'' (fun a ↦ ?_) fun i ↦ ?_)
    · exact (congrArg (fun x ↦ χ (Ideal.Quotient.mk _ x)) (algebraMap_apply _ a).symm).trans
        ((AlgHom.congr_fun hχ₀ a).trans (hC a).symm)
    · have h1 : χ (Ideal.Quotient.mk _ (X A (1 : Fin m → ℝ) i)) * φ g = φ (f i) := by
        rw [← AlgHom.congr_fun hχ₀ g, ← AlgHom.congr_fun hχ₀ (f i), AlgHom.comp_apply,
          AlgHom.comp_apply, ← toRational_mul_mk_X K A f g i, map_mul, mul_comm]
      exact ((Units.eq_mul_inv_iff_mul_eq _).2 (by rw [IsUnit.unit_spec]; exact h1)).trans
        (hX i).symm

/-- `A⟨f/g⟩` is affinoid for `A` affinoid. Source: BGR 6.1.4 ("we want to have an explicit
description of `A⟨f/g⟩` which shows that it is `k`-affinoid"). -/
theorem isAffinoidAlgebra_rationalFractions [IsUltrametricDist K] [CompleteSpace K] [NormOneClass A]
    (hA : IsAffinoidAlgebra K A) : IsAffinoidAlgebra K (RationalFractions A f g) :=
  hA.restricted.quotient _

/-- The algebraic ring of fractions `A[g⁻¹]` maps to `A⟨f/g⟩`. -/
noncomputable def awayLift (hgen : ∃ (a : A) (a' : Fin m → A), a * g + ∑ i, a' i * f i = 1) :
    Localization.Away g →ₐ[A] RationalFractions A f g :=
  IsLocalization.Away.liftAlgHom g (f := Algebra.ofId A (RationalFractions A f g))
    (isUnit_toRational K A f g hgen)

omit [CompleteSpace A] in
/-- **`A[g⁻¹]` is dense in `A⟨f/g⟩`**: the residue classes of the polynomials in `X` are the images
of the `Σ b_ν (f/g)^ν`. Source: BGR 6.1.4 ("The completion of `A[g⁻¹]` is denoted by `A⟨f/g⟩`"),
the density half; roadmap §1.4.2. -/
theorem denseRange_awayLift (hgen : ∃ (a : A) (a' : Fin m → A), a * g + ∑ i, a' i * f i = 1) :
    DenseRange (awayLift K A f g hgen) := by
  let π : MvPolynomial (Fin m) A →+* RationalFractions A f g :=
    (Ideal.Quotient.mk _).comp (MvPolynomial.toRestricted (1 : Fin m → ℝ))
  have h1 : ∀ p, π p ∈ (awayLift K A f g hgen).range := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a =>
      refine (AlgHom.mem_range _).2
        ⟨algebraMap A _ a, ((awayLift K A f g hgen).commutes a).trans ?_⟩
      exact congrArg (Ideal.Quotient.mk _)
        ((algebraMap_apply _ a).trans (MvPolynomial.toRestricted_C _ a).symm)
    | add p q hp hq =>
      rw [map_add]
      exact Subalgebra.add_mem _ hp hq
    | mul_X p i hp =>
      rw [map_mul]
      refine Subalgebra.mul_mem _ hp ((AlgHom.mem_range _).2 ⟨IsLocalization.mk'
        (Localization.Away g) (f i) (⟨g, Submonoid.mem_powers g⟩ : Submonoid.powers g), ?_⟩)
      exact ((IsLocalization.lift_mk'_spec _ _ _ _).2 (toRational_mul_mk_X K A f g i).symm).trans
        (congrArg (Ideal.Quotient.mk _) (MvPolynomial.toRestricted_X _ i).symm)
  have h2 : DenseRange π :=
    Ideal.Quotient.mk_surjective.denseRange.comp (denseRange_toRestricted _) continuous_quot_mk
  refine Dense.mono ?_ h2
  rintro _ ⟨p, rfl⟩
  exact (AlgHom.mem_range _).1 (h1 p)

end RationalFractions

end Affinoid
