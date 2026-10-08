/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.FiniteType
import PhD.TauCeti.Code.RigidAnalyticGeometry.TateAlgebra.Distinguished

/-!
# The Weierstrass finiteness theorem

For a Weierstrass polynomial `ω` of degree `s` in `X 0` over `Tₙ`, the quotient `T_{n+1} ⧸ (ω)` is
the quotient `Tₙ[X] ⧸ (ω)` of the polynomial ring: every class has a unique representative that is
a polynomial of degree less than `s`, so that `T_{n+1} ⧸ (ω)` is free over `Tₙ` on
`1, X 0, …, X 0 ^ (s - 1)`. Consequently a finite homomorphism out of `T_{n+1}` that kills a
Weierstrass polynomial restricts to a finite homomorphism on `Tₙ`.

Roadmap: `PhD/TauCeti/Roadmaps/RigidAnalyticGeometry/README.md`, §0.2.2 (BGR 5.2.3/3–4;
Bosch 1.2/10). Tau Ceti home: `TauCeti/RingTheory/TateAlgebra/Weierstrass.lean`.

## Main results

* `Affinoid.TateAlgebra.IsWeierstrassPolynomial.existsUnique_remainder` — remainders modulo a
  Weierstrass polynomial (BGR 5.2.3/3 (i)).
* `Affinoid.TateAlgebra.IsWeierstrassPolynomial.bijective_quotientMap` —
  `Tₙ[X] ⧸ (ω) ≅ T_{n+1} ⧸ (ω)` (BGR 5.2.3/3 (ii)).
* `Affinoid.TateAlgebra.IsWeierstrassPolynomial.finite_comp_ofTail` — the Weierstrass finiteness
  theorem (BGR 5.2.3/4).
-/

open MvPowerSeries MvPowerSeries.Restricted

namespace Affinoid.TateAlgebra

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K] {n : ℕ}
  {ω : Polynomial (TateAlgebra K n)}

/-- Modulo a Weierstrass polynomial `ω` every series has a unique representative that is a
polynomial in `X 0` of degree less than `deg ω`: the quotient `T_{n+1} ⧸ (ω)` is free over `Tₙ` on
`1, X 0, …, X 0 ^ (deg ω - 1)`. Source: BGR 5.2.3/3 (i). -/
theorem IsWeierstrassPolynomial.existsUnique_remainder (hω : IsWeierstrassPolynomial K n ω)
    (f : TateAlgebra K (n + 1)) :
    ∃! r : Polynomial (TateAlgebra K n),
      r.degree < ω.degree ∧ f - ofPolynomial K n r ∈ Ideal.span {ofPolynomial K n ω} := by
  have hg := hω.isMulDistinguishedX0
  have hd : ω.degree = ω.natDegree := Polynomial.degree_eq_natDegree hω.monic.ne_zero
  obtain ⟨q, r, hr, hf⟩ := weierstrassDivision_exists hg f
  refine ⟨r, ⟨by rwa [hd], Ideal.mem_span_singleton'.2 ⟨q, by rw [hf]; ring⟩⟩, ?_⟩
  rintro r' ⟨hr', hmem⟩
  obtain ⟨q', hq'⟩ := Ideal.mem_span_singleton'.1 hmem
  exact weierstrassDivision_r_unique hg (q₁ := q') (by rwa [← hd]) (by linear_combination -hq') hr
    hf

/-- The quotient of the Tate algebra by a Weierstrass polynomial is the quotient of the polynomial
ring: the natural map `Tₙ[X] ⧸ (ω) → T_{n+1} ⧸ (ω)` is bijective. Source: BGR 5.2.3/3 (ii). -/
theorem IsWeierstrassPolynomial.bijective_quotientMap (hω : IsWeierstrassPolynomial K n ω) :
    Function.Bijective
      (Ideal.quotientMap ((Ideal.span {ω}).map (ofPolynomial K n)) (ofPolynomial K n)
        Ideal.le_comap_map) := by
  have hI : (Ideal.span {ω}).map (ofPolynomial K n) = Ideal.span {ofPolynomial K n ω} := by
    rw [Ideal.map_span, Set.image_singleton]
  have hd : ω.degree = ω.natDegree := Polynomial.degree_eq_natDegree hω.monic.ne_zero
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Ideal.quotientMap_mk, Ideal.Quotient.eq_zero_iff_mem, hI] at hx
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton,
      ← Polynomial.modByMonic_eq_zero_iff_dvd hω.monic]
    have hmem : ofPolynomial K n (p %ₘ ω) - ofPolynomial K n 0 ∈
        Ideal.span {ofPolynomial K n ω} := by
      have hp : ofPolynomial K n (p %ₘ ω) =
          ofPolynomial K n p - ofPolynomial K n ω * ofPolynomial K n (p /ₘ ω) := by
        rw [← map_mul, ← map_sub, eq_sub_of_add_eq (Polynomial.modByMonic_add_div p ω)]
      rw [map_zero, sub_zero, hp]
      exact Ideal.sub_mem _ hx (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
    have h0 : (0 : Polynomial (TateAlgebra K n)).degree < ω.degree := by
      rw [Polynomial.degree_zero, hd]
      exact WithBot.bot_lt_coe _
    exact (hω.existsUnique_remainder (ofPolynomial K n (p %ₘ ω))).unique
      ⟨Polynomial.degree_modByMonic_lt p hω.monic, by rw [sub_self]; exact Ideal.zero_mem _⟩
      ⟨h0, hmem⟩
  · intro y
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨r, ⟨-, hr⟩, -⟩ := hω.existsUnique_remainder f
    refine ⟨Ideal.Quotient.mk _ r, ?_⟩
    rw [Ideal.quotientMap_mk, Ideal.Quotient.eq, hI, ← neg_sub]
    exact (Ideal.neg_mem_iff _).2 hr

/-- The map `Tₙ → T_{n+1} ⧸ (ω)` is finite for every Weierstrass polynomial `ω`.
Source: BGR 5.2.3/4 ("In particular, …"). -/
theorem IsWeierstrassPolynomial.finite_mk_comp_ofTail (hω : IsWeierstrassPolynomial K n ω) :
    ((Ideal.Quotient.mk (Ideal.span {ofPolynomial K n ω})).comp (ofTail K n)).Finite := by
  have hI : (Ideal.span {ω}).map (ofPolynomial K n) = Ideal.span {ofPolynomial K n ω} := by
    rw [Ideal.map_span, Set.image_singleton]
  rw [← hI]
  have h1 : ((Ideal.Quotient.mk (Ideal.span {ω})).comp Polynomial.C).Finite := by
    rw [← Polynomial.algebraMap_eq, Ideal.Quotient.mk_comp_algebraMap, RingHom.finite_algebraMap]
    exact hω.monic.finite_quotient
  have h2 := (RingHom.Finite.of_surjective _ hω.bijective_quotientMap.2).comp h1
  rwa [← RingHom.comp_assoc, Ideal.quotientMap_comp_mk, RingHom.comp_assoc] at h2

/-- The map `Tₙ → T_{n+1} ⧸ (ω)` is injective for every Weierstrass polynomial `ω` of positive
degree. -/
theorem IsWeierstrassPolynomial.injective_mk_comp_ofTail (hω : IsWeierstrassPolynomial K n ω)
    (hdeg : 0 < ω.natDegree) :
    Function.Injective
      ((Ideal.Quotient.mk (Ideal.span {ofPolynomial K n ω})).comp (ofTail K n)) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem] at ha
  have hd : ω.degree = ω.natDegree := Polynomial.degree_eq_natDegree hω.monic.ne_zero
  have hC : (Polynomial.C a).degree < ω.degree := by
    refine Polynomial.degree_C_le.trans_lt ?_
    rw [hd]
    exact_mod_cast hdeg
  have h0 : (0 : Polynomial (TateAlgebra K n)).degree < ω.degree := by
    rw [Polynomial.degree_zero, hd]
    exact WithBot.bot_lt_coe _
  have hCa := (hω.existsUnique_remainder (ofTail K n a)).unique
    ⟨hC, by rw [ofTail_apply, sub_self]; exact Ideal.zero_mem _⟩
    ⟨h0, by rw [map_zero, sub_zero]; exact ha⟩
  exact Polynomial.C_eq_zero.1 hCa

/-- **Weierstrass finiteness theorem**: a finite ring homomorphism out of `T_{n+1}` whose kernel
contains a Weierstrass polynomial restricts to a finite homomorphism on `Tₙ`.
Source: BGR 5.2.3/4. -/
theorem IsWeierstrassPolynomial.finite_comp_ofTail (hω : IsWeierstrassPolynomial K n ω)
    {A : Type*} [CommRing A] (φ : TateAlgebra K (n + 1) →+* A) (hφ : φ.Finite)
    (h0 : φ (ofPolynomial K n ω) = 0) : (φ.comp (ofTail K n)).Finite := by
  have hle : Ideal.span {ofPolynomial K n ω} ≤ RingHom.ker φ := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact h0
  let φ' := Ideal.Quotient.lift (Ideal.span {ofPolynomial K n ω}) φ fun a ha ↦ hle ha
  have hφ' : φ = φ'.comp (Ideal.Quotient.mk _) := (Ideal.Quotient.lift_comp_mk _ _ _).symm
  have hfin : φ'.Finite := by
    rw [hφ'] at hφ
    exact RingHom.Finite.of_comp_finite hφ
  rw [hφ', RingHom.comp_assoc]
  exact hfin.comp hω.finite_mk_comp_ofTail

/-- The map `Tₙ → T_{n+1} ⧸ (g)` is finite for every `X 0`-distinguished series `g`.
Source: BGR 5.2.3/4; Bosch 1.2/10 ("the canonical morphism `T_{n−1} → Tₙ → Tₙ/(g)` is finite"). -/
theorem finite_mk_comp_ofTail_of_isMulDistinguishedX0 {g : TateAlgebra K (n + 1)} {s : ℕ}
    (hg : IsMulDistinguishedX0 g s) :
    ((Ideal.Quotient.mk (Ideal.span {g})).comp (ofTail K n)).Finite := by
  obtain ⟨ω, e, hω, -, hge⟩ := exists_isWeierstrassPolynomial_of_isMulDistinguishedX0 hg
  refine hω.finite_comp_ofTail _ (RingHom.Finite.of_surjective _ Ideal.Quotient.mk_surjective) ?_
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton']
  exact ⟨↑e⁻¹, by rw [hge, ← mul_assoc, Units.inv_mul, one_mul]⟩

/-- Module form of the Weierstrass finiteness theorem: a finite `T_{n+1}`-module killed by a
Weierstrass polynomial is finite over `Tₙ`. Source: BGR 5.2.3/4. -/
theorem IsWeierstrassPolynomial.finite_compHom (hω : IsWeierstrassPolynomial K n ω)
    (M : Type*) [AddCommGroup M] [Module (TateAlgebra K (n + 1)) M]
    [Module.Finite (TateAlgebra K (n + 1)) M] (h : ∀ m : M, ofPolynomial K n ω • m = 0) :
    @Module.Finite (TateAlgebra K n) M _ _ (Module.compHom M (ofTail K n)) := by
  classical
  letI : Module (TateAlgebra K n) M := Module.compHom M (ofTail K n)
  obtain ⟨S, hS⟩ := Module.Finite.fg_top (R := TateAlgebra K (n + 1)) (M := M)
  let S' : Finset M := (Finset.range ω.natDegree ×ˢ S).image fun p ↦
    (ofPolynomial K n Polynomial.X ^ p.1) • p.2
  let N := Submodule.span (TateAlgebra K n) (S' : Set M)
  have hkey (f : TateAlgebra K (n + 1)) (m : M) (hm : m ∈ S) : f • m ∈ N := by
    obtain ⟨q, r, hr, hf⟩ := weierstrassDivision_exists hω.isMulDistinguishedX0 f
    rw [hf, add_smul, ← smul_smul (ofPolynomial K n ω) q m, h, zero_add]
    have hr' : ofPolynomial K n r =
        ∑ i ∈ r.support, ofTail K n (r.coeff i) * ofPolynomial K n Polynomial.X ^ i := by
      conv_lhs => rw [r.as_sum_support_C_mul_X_pow]
      simp only [map_sum, map_mul, map_pow, ofTail_apply]
    rw [hr', Finset.sum_smul]
    refine Submodule.sum_mem _ fun i hi ↦ ?_
    have hi' : i < ω.natDegree := by
      have hle := Polynomial.le_degree_of_ne_zero (Polynomial.mem_support_iff.1 hi)
      exact_mod_cast hle.trans_lt hr
    rw [← smul_smul (ofTail K n (r.coeff i)) _ m]
    exact Submodule.smul_mem N (r.coeff i) (Submodule.subset_span (Finset.mem_coe.2
      (Finset.mem_image.2 ⟨(i, m), Finset.mem_product.2 ⟨Finset.mem_range.2 hi', hm⟩, rfl⟩)))
  have H (x : M) (hx : x ∈ Submodule.span (TateAlgebra K (n + 1)) (S : Set M)) :
      ∀ f : TateAlgebra K (n + 1), f • x ∈ N := by
    induction hx using Submodule.span_induction with
    | mem x hx => exact fun f ↦ hkey f x hx
    | zero => exact fun f ↦ by rw [smul_zero]; exact N.zero_mem
    | add x y _ _ hx hy => exact fun f ↦ by rw [smul_add]; exact N.add_mem (hx f) (hy f)
    | smul a x _ hx => exact fun f ↦ by rw [smul_smul f a x]; exact hx (f * a)
  refine ⟨⟨S', eq_top_iff.2 fun m _ ↦ ?_⟩⟩
  have hm : m ∈ Submodule.span (TateAlgebra K (n + 1)) (S : Set M) := by
    rw [hS]
    exact Submodule.mem_top
  simpa using H m hm 1

end Affinoid.TateAlgebra
