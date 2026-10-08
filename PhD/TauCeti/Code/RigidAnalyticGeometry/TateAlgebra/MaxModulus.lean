/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.Analysis.Normed.Ring.Ultra
import Mathlib.Combinatorics.Nullstellensatz
import Mathlib.FieldTheory.SplittingField.Construction
import PhD.TauCeti.Code.RigidAnalyticGeometry.SupSeminorm
import PhD.TauCeti.Code.RigidAnalyticGeometry.TateAlgebra.EvalReduction

/-!
# The maximum modulus principle for the Tate algebra

For every `f` in the Tate algebra `Tₙ` there is a maximal ideal `x`, with residue field finite over
`K`, at which `|f(x)|` equals the Gauss norm of `f`. Consequently the Gauss norm is the supremum
norm, and the set of such points is Zariski-dense.

The point is found in the unit ball of a finite extension `L` of `K`: the reduction `f̃` of a series
of Gauss norm one is a nonzero polynomial over the residue field, which does not vanish at some
point of `Sⁿ` for any finite set `S` of the residue field of `L` with more elements than the degrees
of `f̃`. The residue field of `K` may be finite, so `L` is in general a proper extension; the roots
of unity of an order prime to the residue characteristic supply `S`.

Roadmap: `PhD/TauCeti/Roadmaps/RigidAnalyticGeometry/README.md`, §0.1.3–0.1.4 (BGR 5.1.4/3,
5.1.4/5, 5.1.4/6; Bosch 1.2/5). Tau Ceti home: `TauCeti/RingTheory/TateAlgebra/MaxModulus.lean`.

## Main results

* `MvPowerSeries.Restricted.exists_norm_aeval_eq_norm` — the maximum modulus principle at the
  points of a complete extension field with a large residue field (BGR 5.1.4/3).
* `MvPowerSeries.Restricted.exists_evalNorm_eq_norm` — the maximum modulus principle on the
  maximal spectrum (BGR 5.1.4/6).
* `MvPowerSeries.Restricted.supSeminorm_eq_norm` — the Gauss norm is the supremum norm
  (BGR 5.1.4/6).
-/

universe u

open Polynomial in
/-- In a nonarchimedean normed field there are natural numbers of norm one beyond any bound. -/
theorem NormedField.exists_lt_natCast_norm_eq_one (K : Type*) [NormedField K]
    [IsUltrametricDist K] (d : ℕ) : ∃ m : ℕ, d < m ∧ ‖(m : K)‖ = 1 := by
  by_cases h : ‖((d + 1 : ℕ) : K)‖ = 1
  · exact ⟨d + 1, Nat.lt_succ_self d, h⟩
  · have hlt : ‖((d + 1 : ℕ) : K)‖ < 1 :=
      lt_of_le_of_ne (IsUltrametricDist.norm_natCast_le_one K (d + 1)) h
    refine ⟨d + 2, by omega, ?_⟩
    have e : ((d + 2 : ℕ) : K) = ((d + 1 : ℕ) : K) + 1 := by push_cast; ring
    rw [e, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_one]; exact hlt.ne),
      norm_one, max_eq_right hlt.le]

section RootsOfUnity

open Polynomial

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- The `m`-th roots of unity in the splitting field of `X ^ m - 1`, for `m` of norm one in `K`:
`m` elements of spectral norm one whose pairwise differences have spectral norm one. This is the
finite extension with a large residue field used in the maximum modulus principle; it replaces
the algebraic closure and BGR's Lemma 3.4.1/4. Source: BGR 5.1.4/3 ("These assertions remain
valid if `k_a` is replaced by any field extension `L ⊂ k_a` of `k`, provided `L̃` is infinite"). -/
theorem exists_finset_splittingField_X_pow_sub_one {m : ℕ} (hm : 0 < m) (hmK : ‖(m : K)‖ = 1) :
    ∃ S : Finset (X ^ m - 1 : K[X]).SplittingField, S.card = m ∧
      (∀ s ∈ S, spectralNorm K _ s = 1) ∧
        ∀ s ∈ S, ∀ t ∈ S, s ≠ t → spectralNorm K _ (s - t) = 1 := by
  classical
  letI : NormedField (X ^ m - 1 : K[X]).SplittingField :=
    spectralNorm.normedField K (X ^ m - 1 : K[X]).SplittingField
  haveI : IsUltrametricDist (X ^ m - 1 : K[X]).SplittingField :=
    IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm isNonarchimedean_spectralNorm
  have hP : (X ^ m - 1 : K[X]) = X ^ m - C 1 := by rw [map_one]
  have hm0 : (m : K) ≠ 0 := fun h ↦ by
    rw [h, norm_zero] at hmK
    exact zero_ne_one hmK
  have hsep : (X ^ m - 1 : K[X]).Separable := hP ▸ separable_X_pow_sub_C 1 hm0 one_ne_zero
  set S := ((X ^ m - 1 : K[X]).rootSet (X ^ m - 1 : K[X]).SplittingField).toFinset with hSdef
  have hroot : ∀ s ∈ S, s ^ m = 1 := by
    intro s hs
    rw [hSdef, Set.mem_toFinset, mem_rootSet] at hs
    simpa [sub_eq_zero] using hs.2
  have hnorm : ∀ s ∈ S, ‖s‖ = 1 := by
    intro s hs
    have h1 : ‖s‖ ^ m = 1 := by rw [← norm_pow, hroot s hs, norm_one]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg s) hm.ne').1 h1
  refine ⟨S, ?_, hnorm, fun s hs t ht hst ↦ ?_⟩
  · rw [hSdef, Set.toFinset_card, card_rootSet_eq_natDegree hsep (SplittingField.splits _), hP,
      natDegree_X_pow_sub_C]
  show ‖s - t‖ = 1
  have hs1 := hnorm s hs
  have ht1 := hnorm t ht
  have hG : ∑ i ∈ Finset.range m, s ^ i * t ^ (m - 1 - i) = 0 := by
    have h := geom_sum₂_mul s t m
    rw [hroot s hs, hroot t ht, sub_self] at h
    exact (mul_eq_zero.1 h).resolve_right (sub_ne_zero.2 hst)
  have hGs : ∑ i ∈ Finset.range m, s ^ i * s ^ (m - 1 - i) = (m : _) * s ^ (m - 1) := by
    rw [Finset.sum_congr rfl fun i hi ↦ (by
        rw [← pow_add, Nat.add_sub_cancel' (Nat.le_sub_one_of_lt (Finset.mem_range.1 hi))] :
          s ^ i * s ^ (m - 1 - i) = s ^ (m - 1)),
      Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  set W := ∑ i ∈ Finset.range m,
    s ^ i * ∑ j ∈ Finset.range (m - 1 - i), s ^ j * t ^ (m - 1 - i - 1 - j) with hWdef
  have hdiff : ∑ i ∈ Finset.range m, s ^ i * s ^ (m - 1 - i) = (s - t) * W := by
    calc ∑ i ∈ Finset.range m, s ^ i * s ^ (m - 1 - i)
        = ∑ i ∈ Finset.range m, s ^ i * s ^ (m - 1 - i) -
            ∑ i ∈ Finset.range m, s ^ i * t ^ (m - 1 - i) := by rw [hG, sub_zero]
      _ = ∑ i ∈ Finset.range m, (s ^ i * s ^ (m - 1 - i) - s ^ i * t ^ (m - 1 - i)) :=
          (Finset.sum_sub_distrib _ _).symm
      _ = (s - t) * W := by
          rw [hWdef, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [← mul_sub, ← geom_sum₂_mul s t (m - 1 - i)]
          ring
  have hW : ‖W‖ ≤ 1 := by
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ ↦ ?_
    rw [norm_mul, norm_pow, hs1, one_pow, one_mul]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun j _ ↦ ?_
    rw [norm_mul, norm_pow, norm_pow, hs1, ht1, one_pow, one_pow, one_mul]
  have hval : ‖((m : (X ^ m - 1 : K[X]).SplittingField)) * s ^ (m - 1)‖ = 1 := by
    rw [norm_mul, norm_pow, hs1, one_pow, mul_one, ← map_natCast
      (algebraMap K (X ^ m - 1 : K[X]).SplittingField)]
    exact (spectralNorm_extends (m : K)).trans hmK
  refine le_antisymm ?_ ?_
  · calc ‖s - t‖ = ‖s + -t‖ := by rw [sub_eq_add_neg s t]
      _ ≤ max ‖s‖ ‖-t‖ := IsUltrametricDist.norm_add_le_max s (-t)
      _ = 1 := by rw [norm_neg, hs1, ht1, max_self]
  · calc (1 : ℝ) = ‖((m : (X ^ m - 1 : K[X]).SplittingField)) * s ^ (m - 1)‖ := hval.symm
      _ = ‖s - t‖ * ‖W‖ := by rw [← hGs, hdiff, norm_mul]
      _ ≤ ‖s - t‖ * 1 := mul_le_mul_of_nonneg_left hW (norm_nonneg _)
      _ = ‖s - t‖ := mul_one _

end RootsOfUnity

namespace MvPowerSeries.Restricted

open Subring NormedRing IsLocalRing Affinoid

section Point

variable {K : Type*} [NormedField K] [IsUltrametricDist K] {σ : Type*} [Finite σ]
  {L : Type*} [NormedField L] [NormedAlgebra K L] [IsUltrametricDist L] [CompleteSpace L]

/-- **Maximum modulus principle at the points of an extension field.** Let `L` be a complete
extension field of `K` and `S` a finite subset of its unit ball whose elements are pairwise at
distance one, with more elements than every exponent occurring at a coefficient of `f` of maximal
norm. Then `|f(x)| = |f|` for some point `x` with coordinates in `S`. Source: BGR 5.1.4/3;
Bosch 1.2/5. -/
theorem exists_norm_aeval_eq_norm (S : Finset L) (hS₁ : ∀ s ∈ S, ‖s‖ ≤ 1)
    (hS : ∀ s ∈ S, ∀ t ∈ S, s ≠ t → ‖s - t‖ = 1) (f : Restricted K (1 : σ → ℝ))
    (hf : ∀ t : σ →₀ ℕ, ‖coeff t f.1‖ = ‖f‖ → ∀ i, t i < S.card) :
    ∃ x : σ → L, ∃ hx : ∀ i, ‖x i‖ ≤ 1, (∀ i, x i ∈ S) ∧ ‖aeval (1 : σ → ℝ) x hx f‖ = ‖f‖ := by
  classical
  rcases eq_or_ne f 0 with rfl | hf0
  · rcases isEmpty_or_nonempty σ with hσ | hσ
    · exact ⟨isEmptyElim, isEmptyElim, isEmptyElim, by simp⟩
    · obtain ⟨i⟩ := hσ
      have hpos : 0 < S.card := by simpa using hf 0 (by simp) i
      obtain ⟨s, hs⟩ := Finset.card_pos.1 hpos
      exact ⟨fun _ ↦ s, fun _ ↦ hS₁ s hs, fun _ ↦ hs, by simp⟩
  let ρ : L → ResidueField (unitClosedBall L) := fun s ↦
    if h : ‖s‖ ≤ 1 then residue (unitClosedBall L) ⟨s, mem_unitClosedBall.2 h⟩ else 0
  have hρ (s : L) (h : ‖s‖ ≤ 1) :
      ρ s = residue (unitClosedBall L) ⟨s, mem_unitClosedBall.2 h⟩ := dif_pos h
  have hinj : Set.InjOn ρ S := by
    intro s hs t ht hst
    by_contra hne
    rw [hρ s (hS₁ s hs), hρ t (hS₁ t ht), ← sub_eq_zero, ← map_sub, residue_eq_zero_iff,
      maximalIdeal_unitClosedBall, mem_openUnitBallIdeal] at hst
    have h1 : ‖s - t‖ < 1 := hst
    rw [hS s hs t ht hne] at h1
    exact lt_irrefl _ h1
  have hcard : (S.image ρ).card = S.card := Finset.card_image_of_injOn hinj
  obtain ⟨a, ha, haf⟩ := exists_norm_smul_eq_one hf0
  have hapos : 0 < ‖a‖ := norm_pos_iff.2 ha
  have haf' : ‖a‖ * ‖f‖ = 1 := by rw [← norm_smul_eq]; exact haf
  set g : unitClosedBall (Restricted K (1 : σ → ℝ)) := ⟨a • f, mem_unitClosedBall.2 haf.le⟩
  have hred0 : reduction g ≠ 0 := by
    rw [Ne, reduction_eq_zero_iff, not_lt]
    exact haf.ge
  set Q := MvPolynomial.map (NormedField.residueFieldMap K L) (reduction g) with hQ
  have hQ0 : Q ≠ 0 := fun h ↦ hred0 (MvPolynomial.map_injective _
    (NormedField.residueFieldMap K L).injective (h.trans (map_zero _).symm))
  have hdeg (i : σ) : Q.degreeOf i < (S.image ρ).card := by
    obtain ⟨t₀, ht₀⟩ := exists_norm_coeff_eq f
    have hpos : 0 < S.card := (Nat.zero_le _).trans_lt (hf t₀ ht₀ i)
    rw [hcard, MvPolynomial.degreeOf_lt_iff hpos]
    intro t ht
    have ht' : t ∈ (reduction g).support := MvPolynomial.support_map_subset _ _ ht
    rw [MvPolynomial.mem_support_iff, coeff_reduction, Ne, residue_eq_zero_iff,
      maximalIdeal_unitClosedBall, mem_openUnitBallIdeal, coe_unitBallCoeff, not_lt] at ht'
    have hcoeff : coeff t (g : Restricted K (1 : σ → ℝ)).1 = a * coeff t f.1 := by
      show coeff t (a • f).1 = a * coeff t f.1
      simp
    rw [hcoeff, norm_mul] at ht'
    have heq : ‖coeff t f.1‖ = ‖f‖ :=
      le_antisymm (norm_coeff_le f t) (le_of_mul_le_mul_left (by linarith) hapos)
    exact hf t heq i
  obtain ⟨y, hyS, hy⟩ : ∃ y : σ → ResidueField (unitClosedBall L),
      (∀ i, y i ∈ S.image ρ) ∧ MvPolynomial.eval y Q ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hQ0 (MvPolynomial.eq_zero_of_eval_zero_at_prod_finset Q (fun _ ↦ S.image ρ) hdeg hcon)
  have hlift (i : σ) : ∃ s ∈ S, ρ s = y i := Finset.mem_image.1 (hyS i)
  choose x hxS hxρ using hlift
  have hx (i : σ) : ‖x i‖ ≤ 1 := hS₁ _ (hxS i)
  refine ⟨x, hx, hxS, ?_⟩
  have key := residue_aeval hx g
  have hyeq : (fun i ↦ residue (unitClosedBall L) ⟨x i, mem_unitClosedBall.2 (hx i)⟩) = y := by
    funext i
    rw [← hxρ i, hρ _ (hx i)]
  rw [hyeq, ← MvPolynomial.eval_map] at key
  have hone : ‖aeval (1 : σ → ℝ) x hx (g : Restricted K (1 : σ → ℝ))‖ = 1 := by
    refine le_antisymm (norm_aeval_le_one hx g) (not_lt.1 fun hlt ↦ hy ?_)
    rw [← key, residue_eq_zero_iff, maximalIdeal_unitClosedBall, mem_openUnitBallIdeal]
    exact hlt
  have hsmul : aeval (1 : σ → ℝ) x hx (g : Restricted K (1 : σ → ℝ)) =
      a • aeval (1 : σ → ℝ) x hx f := map_smul _ a f
  rw [hsmul, norm_smul] at hone
  exact mul_left_cancel₀ hapos.ne' (hone.trans haf'.symm)

end Point

section MaximalSpectrum

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {σ : Type*} [Finite σ]

omit [Finite σ] in
/-- At a maximal ideal with residue field finite over `K` the value `|f(x)|` is multiplicative. -/
private lemma evalNorm_mul_of_finite (x : MaximalSpectrum (Restricted K (1 : σ → ℝ)))
    [Module.Finite K (Restricted K (1 : σ → ℝ) ⧸ x.asIdeal)] (f g : Restricted K (1 : σ → ℝ)) :
    evalNorm K x (f * g) = evalNorm K x f * evalNorm K x g := by
  have hmax := x.isMaximal
  letI : Field (Restricted K (1 : σ → ℝ) ⧸ x.asIdeal) := Ideal.Quotient.field x.asIdeal
  haveI : Algebra.IsAlgebraic K (Restricted K (1 : σ → ℝ) ⧸ x.asIdeal) :=
    Algebra.IsAlgebraic.of_finite K _
  show spectralAlgNorm K _ (Ideal.Quotient.mk x.asIdeal (f * g)) =
    spectralAlgNorm K _ (Ideal.Quotient.mk x.asIdeal f) *
      spectralAlgNorm K _ (Ideal.Quotient.mk x.asIdeal g)
  rw [map_mul]
  exact spectralAlgNorm_mul _ _

/-- The maximum modulus principle for a nonzero series. -/
private lemma exists_evalNorm_eq_norm_of_ne_zero {f : Restricted K (1 : σ → ℝ)} (hf : f ≠ 0) :
    ∃ x : MaximalSpectrum (Restricted K (1 : σ → ℝ)),
      Module.Finite K (Restricted K (1 : σ → ℝ) ⧸ x.asIdeal) ∧ evalNorm K x f = ‖f‖ := by
  classical
  haveI := Fintype.ofFinite σ
  have hfin := finite_setOf_le_norm_coeff f (norm_pos_iff.2 hf)
  obtain ⟨m, hdm, hmK⟩ := NormedField.exists_lt_natCast_norm_eq_one K
    (hfin.toFinset.sup fun t ↦ Finset.univ.sup fun i ↦ t i)
  obtain ⟨S, hcard, hS₁, hS⟩ := exists_finset_splittingField_X_pow_sub_one K
    (by omega : 0 < m) hmK
  letI := spectralNorm.normedField K (Polynomial.X ^ m - 1 : Polynomial K).SplittingField
  letI := spectralNorm.normedAlgebra K (Polynomial.X ^ m - 1 : Polynomial K).SplittingField
  haveI : IsUltrametricDist (Polynomial.X ^ m - 1 : Polynomial K).SplittingField :=
    IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm isNonarchimedean_spectralNorm
  haveI := spectralNorm.completeSpace K (Polynomial.X ^ m - 1 : Polynomial K).SplittingField
  have hbound (t : σ →₀ ℕ) (ht : ‖coeff t f.1‖ = ‖f‖) (i : σ) : t i < S.card := by
    rw [hcard]
    have htmem : t ∈ hfin.toFinset := (Set.Finite.mem_toFinset hfin).2 ht.ge
    calc t i ≤ Finset.univ.sup fun i ↦ t i := Finset.le_sup (f := fun i ↦ t i) (Finset.mem_univ i)
      _ ≤ hfin.toFinset.sup fun t ↦ Finset.univ.sup fun i ↦ t i :=
          Finset.le_sup (f := fun t ↦ Finset.univ.sup fun i ↦ t i) htmem
      _ < m := hdm
  obtain ⟨x, hx, -, hxf⟩ :=
    exists_norm_aeval_eq_norm (K := K) S (fun s hs ↦ (hS₁ s hs).le) hS f hbound
  haveI := isMaximal_ker_of_isAlgebraic (aeval (K := K) (1 : σ → ℝ) x hx)
  refine ⟨⟨RingHom.ker (aeval (K := K) (1 : σ → ℝ) x hx), inferInstance⟩,
    finite_quotient_ker _, ?_⟩
  rw [evalNorm_eq_norm_algHom (aeval (K := K) (1 : σ → ℝ) x hx) _ rfl]
  exact hxf

/-- **Maximum modulus principle for the Tate algebra**: every `f` attains its Gauss norm at a
maximal ideal whose residue field is finite over `K`. Source: BGR 5.1.4/6. -/
theorem exists_evalNorm_eq_norm (f : Restricted K (1 : σ → ℝ)) :
    ∃ x : MaximalSpectrum (Restricted K (1 : σ → ℝ)),
      Module.Finite K (Restricted K (1 : σ → ℝ) ⧸ x.asIdeal) ∧ evalNorm K x f = ‖f‖ := by
  rcases eq_or_ne f 0 with rfl | hf
  · obtain ⟨x, hfin, -⟩ := exists_evalNorm_eq_norm_of_ne_zero
      (one_ne_zero : (1 : Restricted K (1 : σ → ℝ)) ≠ 0)
    exact ⟨x, hfin, by rw [evalNorm_eq_zero_of_mem K (Ideal.zero_mem _), norm_zero]⟩
  · exact exists_evalNorm_eq_norm_of_ne_zero hf

/-- The points at which `f` attains its Gauss norm are Zariski-dense: every nonzero `g` is nonzero
at one of them. Source: BGR 5.1.4/4 (the product trick). -/
theorem exists_evalNorm_eq_norm_and_notMem (f : Restricted K (1 : σ → ℝ))
    {g : Restricted K (1 : σ → ℝ)} (hg : g ≠ 0) :
    ∃ x : MaximalSpectrum (Restricted K (1 : σ → ℝ)), evalNorm K x f = ‖f‖ ∧ g ∉ x.asIdeal := by
  have hgx {x : MaximalSpectrum (Restricted K (1 : σ → ℝ))} (h : evalNorm K x g = ‖g‖) :
      g ∉ x.asIdeal := fun hmem ↦ by
    rw [evalNorm_eq_zero_of_mem K hmem] at h
    exact hg (norm_eq_zero.1 h.symm)
  rcases eq_or_ne f 0 with rfl | hf
  · obtain ⟨x, -, hx⟩ := exists_evalNorm_eq_norm g
    exact ⟨x, by rw [evalNorm_eq_zero_of_mem K (Ideal.zero_mem _), norm_zero], hgx hx⟩
  obtain ⟨x, hfin, hx⟩ := exists_evalNorm_eq_norm (f * g)
  rw [evalNorm_mul_of_finite x f g, norm_mul] at hx
  have hf₁ := evalNorm_le_norm (K := K) x f
  have hg₁ := evalNorm_le_norm (K := K) x g
  have hf₀ := evalNorm_nonneg K x f
  have hg₀ := evalNorm_nonneg K x g
  have hfpos : 0 < ‖f‖ := norm_pos_iff.2 hf
  have hgpos : 0 < ‖g‖ := norm_pos_iff.2 hg
  have hfeq : evalNorm K x f = ‖f‖ := by
    refine le_antisymm hf₁ (not_lt.1 fun hlt ↦ ?_)
    have : evalNorm K x f * evalNorm K x g < ‖f‖ * ‖g‖ :=
      (mul_le_mul_of_nonneg_left hg₁ hf₀).trans_lt (mul_lt_mul_of_pos_right hlt hgpos)
    exact this.ne hx
  have hgeq : evalNorm K x g = ‖g‖ := by
    refine le_antisymm hg₁ (not_lt.1 fun hlt ↦ ?_)
    have : evalNorm K x f * evalNorm K x g < ‖f‖ * ‖g‖ := by
      rw [hfeq]
      exact mul_lt_mul_of_pos_left hlt hfpos
    exact this.ne hx
  exact ⟨x, hfeq, hgx hgeq⟩

/-- **The Gauss norm is the supremum norm** on the Tate algebra. Source: BGR 5.1.4/6. -/
theorem supSeminorm_eq_norm (f : Restricted K (1 : σ → ℝ)) : supSeminorm K f = ‖f‖ := by
  refine le_antisymm (supSeminorm_le_norm f) ?_
  obtain ⟨x, -, hx⟩ := exists_evalNorm_eq_norm f
  rw [← hx]
  exact le_ciSup (bddAbove_range_evalNorm f) x

/-- A series vanishing at every maximal ideal is zero. Source: BGR 5.1.4/5 (identity theorem). -/
theorem eq_zero_of_forall_mem {f : Restricted K (1 : σ → ℝ)}
    (hf : ∀ x : MaximalSpectrum (Restricted K (1 : σ → ℝ)), f ∈ x.asIdeal) : f = 0 := by
  obtain ⟨x, -, hx⟩ := exists_evalNorm_eq_norm f
  rw [evalNorm_eq_zero_of_mem K (hf x)] at hx
  exact norm_eq_zero.1 hx.symm

end MaximalSpectrum

end MvPowerSeries.Restricted
