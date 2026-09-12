/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import PhD.Main.BirkovichWP.RingTheory.PowerSeries.Restricted.BaseChange
import PhD.Main.BirkovichWP.RingTheory.PowerSeries.Restricted.WeierstrassPrep
import PhD.Main.BirkovichWP.RingTheory.PowerSeries.Restricted.WeierstrassDivisionOracle

/-! # Weierstrass division and preparation at every radius

Over a complete nontrivially normed ultrametric field `K`, Weierstrass division and
preparation hold at **every** radius `c > 0`, with no scaling hypotheses, by a dichotomy on
the divisible closure of the value group:

* if some power `c ^ n` (`n ≠ 0`) is a realised norm (`MemDivisibleValueGroup`), the radius
  becomes the norm of a unit after adjoining an `n`-th root inside a finite extension of `K`
  carrying the spectral norm; the division over the extension descends to `K` by
  `Restricted.weierstrassDivision_descend`;
* otherwise no Gauss term can tie the dominant one
  (`forall_norm_coeff_mul_pow_lt_of_not_memDivisibleValueGroup`) — a tie
  `‖aₜ‖cᵗ = ‖aₛ‖cˢ` against the unit coefficient `aₛ` would exhibit `c^(s-t)` as a realised
  norm — and the strictly-dominated one-step division engine
  (`weierstrassDivision_exists_of_forall_lt`) applies at the radius itself.

Preparation at each generality is the corollary
`weierstrassPreparation_exists_of_forall_exists` of the corresponding division statement.
-/

/-- `c` lies in the divisible closure of the value group of `K`: some positive power of `c`
is a realised norm. -/
def MemDivisibleValueGroup (K : Type*) [Norm K] (c : ℝ) : Prop :=
  ∃ n : ℕ, n ≠ 0 ∧ ∃ x : K, ‖x‖ = c ^ n

universe u

/-- **One finite isometric complete extension realising finitely many divisible radii as
unit norms**: adjoin roots of realising elements inside the algebraic closure, normed by the
spectral norm.  Stated as an eliminator so the univariate and multivariate divisible cases
use the construction verbatim. -/
theorem MemDivisibleValueGroup.elim_finite_extension {K : Type u} [NontriviallyNormedField K]
    [IsUltrametricDist K] [CompleteSpace K] {ι : Type*} [Finite ι] {c : ι → ℝ}
    (hc : ∀ i, 0 < c i) (hdiv : ∀ i, MemDivisibleValueGroup K (c i)) {P : Prop}
    (h : ∀ (L : Type u) [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
      [Algebra K L] [Module.Finite K L],
      (∀ a : K, ‖algebraMap K L a‖ = ‖a‖) → (∀ i, ∃ u : Lˣ, ‖(u : L)‖ = c i) → P) : P := by
  choose m hm x hx using hdiv
  choose α hα using fun i ↦ IsAlgClosed.exists_pow_nat_eq
    (algebraMap K (AlgebraicClosure K) (x i)) (Nat.pos_of_ne_zero (hm i))
  have hmem : ∀ i, α i ∈ IntermediateField.adjoin K (Set.range α) := fun i ↦
    IntermediateField.subset_adjoin K (Set.range α) ⟨i, rfl⟩
  haveI : Finite (Set.range α) := (Set.finite_range α).to_subtype
  haveI : FiniteDimensional K ↥(IntermediateField.adjoin K (Set.range α)) :=
    IntermediateField.finiteDimensional_adjoin fun y _ ↦
      (Algebra.IsAlgebraic.isAlgebraic y).isIntegral
  haveI : Algebra.IsAlgebraic K ↥(IntermediateField.adjoin K (Set.range α)) :=
    Algebra.IsAlgebraic.of_finite K _
  letI : NontriviallyNormedField ↥(IntermediateField.adjoin K (Set.range α)) :=
    spectralNorm.nontriviallyNormedField K _
  haveI : IsUltrametricDist ↥(IntermediateField.adjoin K (Set.range α)) :=
    IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm isNonarchimedean_spectralNorm
  have hiso : ∀ a : K, ‖algebraMap K ↥(IntermediateField.adjoin K (Set.range α)) a‖ = ‖a‖ :=
    fun a ↦ spectralNorm_extends a
  letI : NormedSpace K ↥(IntermediateField.adjoin K (Set.range α)) :=
    ⟨fun a y ↦ le_of_eq (by rw [Algebra.smul_def, norm_mul, hiso])⟩
  haveI : CompleteSpace ↥(IntermediateField.adjoin K (Set.range α)) :=
    FiniteDimensional.complete K _
  refine h ↥(IntermediateField.adjoin K (Set.range α)) hiso fun i ↦ ?_
  have hgen : (⟨α i, hmem i⟩ : ↥(IntermediateField.adjoin K (Set.range α))) ^ m i
      = algebraMap K ↥(IntermediateField.adjoin K (Set.range α)) (x i) := by
    apply (algebraMap ↥(IntermediateField.adjoin K (Set.range α))
      (AlgebraicClosure K)).injective
    rw [map_pow, ← IsScalarTower.algebraMap_apply, ← hα i]
    rfl
  have hnorm : ‖(⟨α i, hmem i⟩ : ↥(IntermediateField.adjoin K (Set.range α)))‖ = c i := by
    refine (pow_left_inj₀ (norm_nonneg _) (hc i).le (hm i)).mp ?_
    rw [← norm_pow, hgen, hiso, hx i]
  have hne : (⟨α i, hmem i⟩ : ↥(IntermediateField.adjoin K (Set.range α))) ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hnorm
    exact (hc i).ne hnorm
  exact ⟨Units.mk0 _ hne, hnorm⟩

namespace PowerSeries.Restricted

section NoTie

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [NormMulClass R] {c : ℝ}
  [Fact (0 < c)]

/-- Off the divisible closure of the value group, no Gauss term can tie the dominant term of
a distinguished series: a tie against the unit coefficient `aₛ` would exhibit `c ^ (s - t)`
as the realised norm `‖aₜ * aₛ⁻¹‖`. -/
lemma forall_norm_coeff_mul_pow_lt_of_not_memDivisibleValueGroup
    (hc : ¬MemDivisibleValueGroup R c) {g : Restricted R c} {s : ℕ}
    (hg : IsDistinguished norm c g.1 s) :
    ∀ t, t ≠ s → ‖coeff t g.1‖ * c ^ t < ‖coeff s g.1‖ * c ^ s := by
  have hc0 : (0 : ℝ) < c := Fact.out
  have hntR : Nontrivial R := hg.nontrivial
  intro t hts
  rcases lt_or_gt_of_ne hts with htlt | htgt
  · have hle : ‖coeff t g.1‖ * c ^ t ≤ ‖coeff s g.1‖ * c ^ s := by
      rw [hg.norm_coeff_mul_pow_eq]
      exact norm_coeff_mul_pow_le c g t
    refine lt_of_le_of_ne hle fun heq ↦ hc ?_
    obtain ⟨u, hu_spec⟩ := hg.isUnit_coeff
    haveI : NormOneClass R := NormMulClass.toNormOneClass
    have hs_pos : (0 : ℝ) < ‖coeff s g.1‖ := by
      rw [← hu_spec]
      exact norm_pos_iff.mpr u.ne_zero
    refine ⟨s - t, Nat.sub_ne_zero_of_lt htlt, coeff t g.1 * ((u⁻¹ : Rˣ) : R), ?_⟩
    rw [norm_mul, norm_units_inv, hu_spec, pow_sub₀ c hc0.ne' htlt.le]
    field_simp [hs_pos.ne', (pow_pos hc0 t).ne']
    linear_combination heq
  · exact hg.gaussTerm_lt t htgt

end NoTie

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {c : ℝ} [Fact (0 < c)]

omit [CompleteSpace K] in
/-- Over a field, the scaling hypothesis `hunit` of Weierstrass division is automatic once
`c` is the norm of a unit: the Gauss norm of a nonzero restricted series is attained at some
coefficient, so `‖f‖ = ‖aₖ‖ cᵏ = ‖aₖ uᵏ‖` is a realised norm, and fields invert. -/
lemma exists_norm_inv_isUnit (hα : ∃ u : Kˣ, ‖(u : K)‖ = c) (f : Restricted K c)
    (hf : f ≠ 0) : ∃ a : K, ‖a‖ = ‖f‖⁻¹ ∧ IsUnit a := by
  obtain ⟨u, hu⟩ := hα
  obtain ⟨k, hcoeff, hnorm⟩ := exists_coeff_ne_zero_norm_eq c f hf
  have hx : coeff k f.1 * (u : K) ^ k ≠ 0 :=
    mul_ne_zero hcoeff (pow_ne_zero _ u.ne_zero)
  refine ⟨(coeff k f.1 * (u : K) ^ k)⁻¹, ?_, isUnit_iff_ne_zero.mpr (inv_ne_zero hx)⟩
  rw [norm_inv, norm_mul, norm_pow, hu, ← hnorm]

open scoped Topology in
/-- **Weierstrass division, existence, at a divisible radius**: for `c` with `c ^ n` a
realised norm and `g` distinguished of degree `s`, every `f` divides as `f = g * q + r` with
`deg r < s`.  No scaling hypotheses: the radius becomes a unit norm in a finite
spectral-norm extension of `K` (`MemDivisibleValueGroup.elim_finite_extension`), where the
division exists, and descends. -/
private theorem weierstrassDivision_exists_divisible (hdiv : MemDivisibleValueGroup K c)
    {g : Restricted K c} {s : ℕ} (hg : IsDistinguished norm c g.1 s) (f : Restricted K c) :
    ∃ (q : Restricted K c) (r : Polynomial K), r.degree < s ∧
      f = g * q + Polynomial.toRestricted c r := by
  refine MemDivisibleValueGroup.elim_finite_extension (ι := Unit) (c := fun _ ↦ c)
    (fun _ ↦ Fact.out) (fun _ ↦ hdiv) ?_
  intro L _ _ _ _ _ hiso hunitL
  haveI : Filter.NeBot (𝓝[≠] (0 : L)) := NormedField.nhdsNE_neBot 0
  obtain ⟨q₁, r₁, hr₁, hf₁⟩ := weierstrassDivision_exists
    ((isDistinguished_mapAlgebra_iff hiso g s).mpr hg) (mapAlgebra c hiso f)
    (fun f' hf' ↦ exists_norm_inv_isUnit (hunitL ()) f' hf')
  obtain ⟨q₀, r₀, hr₀, heq, -, -⟩ :=
    weierstrassDivision_descend hiso hg f hr₁ hf₁
  exact ⟨q₀, r₀, hr₀, heq⟩

/-! ## The dichotomy: every radius

Naming note: the `_of_field` suffixes are provisional — flagged for the final cleanup to
decide whether these unconditional versions should take over the bare names. -/

/-- **Weierstrass division, existence, at every radius** over a complete nontrivially normed
ultrametric field: by cases on whether `c` lies in the divisible closure of the value
group. -/
theorem weierstrassDivision_exists_of_field {g : Restricted K c} {s : ℕ}
    (hg : IsDistinguished norm c g.1 s) (f : Restricted K c) :
    ∃ (q : Restricted K c) (r : Polynomial K), r.degree < s ∧
      f = g * q + Polynomial.toRestricted c r := by
  by_cases hdiv : MemDivisibleValueGroup K c
  · exact weierstrassDivision_exists_divisible hdiv hg f
  · exact weierstrassDivision_exists_of_forall_lt hg
      (forall_norm_coeff_mul_pow_lt_of_not_memDivisibleValueGroup hdiv hg) f

/-- **Weierstrass division at every radius**: existence and uniqueness. -/
theorem weierstrassDivision_uniqueness_of_field {g : Restricted K c} {s : ℕ}
    (hg : IsDistinguished norm c g.1 s) (f : Restricted K c) :
    ∃! q : Restricted K c, ∃! r : Polynomial K, r.degree < s ∧
      f = g * q + Polynomial.toRestricted c r :=
  weierstrassDivision_uniqueness_of_exists hg (weierstrassDivision_exists_of_field hg f)

omit [CompleteSpace K] in
/-- **Weierstrass division for polynomials at every radius** — the restatement over a field
of the hypothesis-free `weierstrassDivision_polynomial`, keeping the `_of_field` six
together. -/
theorem weierstrassDivision_polynomial_of_field {g₀ : Polynomial K} {s : ℕ}
    (hg : IsDistinguished norm c (Polynomial.toRestricted c g₀).1 s) (hgs : g₀.degree ≤ s)
    (f₀ : Polynomial K) :
    ∃! q : Polynomial K, ∃! r : Polynomial K, r.degree < s ∧
      Polynomial.toRestricted c f₀ = Polynomial.toRestricted c g₀ * Polynomial.toRestricted c q
        + Polynomial.toRestricted c r :=
  weierstrassDivision_polynomial hg hgs f₀

/-- **Weierstrass preparation, existence, at every radius**. -/
theorem weierstrassPreparation_exists_of_field {g : Restricted K c} {s : ℕ}
    (hg : IsDistinguished norm c g.1 s) :
    ∃ (ω : Polynomial K) (e : Restricted K c), ω.Monic ∧ ω.degree = s ∧
      ‖Polynomial.toRestricted c ω‖ = c ^ s ∧ IsUnit e ∧
      g = e * Polynomial.toRestricted c ω :=
  weierstrassPreparation_exists_of_forall_exists
    (fun _ _ hg' f ↦ weierstrassDivision_exists_of_field hg' f) hg

/-- **Weierstrass preparation at every radius**: the factorisation is unique. -/
theorem weierstrassPreparation_unique_of_field {g : Restricted K c} {s : ℕ}
    (hg : IsDistinguished norm c g.1 s) :
    ∃! ω : Polynomial K, ∃! e : Restricted K c, ω.Monic ∧ ω.degree = s ∧
      ‖Polynomial.toRestricted c ω‖ = c ^ s ∧ IsUnit e ∧
      g = e * Polynomial.toRestricted c ω :=
  weierstrassPreparation_unique_of_forall_exists
    (fun _ _ hg' f ↦ weierstrassDivision_exists_of_field hg' f) hg

/-- **Weierstrass preparation for polynomials at every radius**: if `g` is a polynomial, the
unit `e` of its preparation is itself a polynomial.  (As in
`weierstrassPreparation_polynomial`, unit-ness of `e` is in the restricted power series
ring, not in `K[X]`.) -/
theorem weierstrassPreparation_polynomial_of_field {g₀ : Polynomial K} {s : ℕ}
    (hg : IsDistinguished norm c (Polynomial.toRestricted c g₀).1 s) :
    ∃! ω : Polynomial K, ∃! e : Polynomial K, ω.Monic ∧ ω.degree = s ∧
      ‖Polynomial.toRestricted c ω‖ = c ^ s ∧ IsUnit (Polynomial.toRestricted c e) ∧
      Polynomial.toRestricted c g₀ =
        Polynomial.toRestricted c e * Polynomial.toRestricted c ω :=
  weierstrassPreparation_polynomial_of_forall_exists
    (fun _ _ hg' f ↦ weierstrassDivision_exists_of_field hg' f) hg

end PowerSeries.Restricted
