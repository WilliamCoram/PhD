/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-!
# Rückert overrings

Following BGR 5.2.5, an overring `I'` of a polynomial ring `I[X]` is *Rückert* over `I` with respect
to a family `W` of monic polynomials if (1) monic factors of members of `W` are in `W`, (2) the
quotients `I[X] ⧸ (ω)` and `I' ⧸ (ω)` agree for `ω ∈ W`, and (3) every nonzero element of `I'` is,
up to an automorphism and a unit, a member of `W`. The Tate algebra `T_{n+1}` is Rückert over `Tₙ`
for the family of Weierstrass polynomials, and so are rings of formal and of convergent power
series. A Rückert overring inherits from `I` the properties of being noetherian, factorial and
Jacobson, and its Krull dimension is that of `I` plus one.

Roadmap: `PhD/TauCeti/Roadmaps/RigidAnalyticGeometry/README.md`, §0.3 (BGR 5.2.5/1–4;
Bosch 1.2/10, 1.2/13–15). Tau Ceti home: `TauCeti/RingTheory/Rueckert.lean`.

## Main definitions

* `IsRueckert φ W` — the ring `I'` is Rückert over `I` along `φ : I[X] →+* I'` for the family `W`.

## Main results

* `IsRueckert.isNoetherianRing` — BGR 5.2.5/2.
* `IsRueckert.jacobson_eq_radical`, `IsRueckert.isJacobsonRing` — BGR 5.2.5/3.
* `IsRueckert.uniqueFactorizationMonoid` — BGR 5.2.5/4.
* `IsRueckert.ringKrullDim_le`, `IsRueckert.ringKrullDim_eq` — the dimension goes up by one.
-/

open Polynomial

/-! ### Two facts about the Krull dimension -/

/-- An integral ring homomorphism does not raise the Krull dimension: distinct comparable primes
have distinct contractions. Source: BGR 6.1.2 (Remark), citing Nagata, Corollary 10.10. -/
theorem ringKrullDim_le_of_isIntegral {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : f.IsIntegral) : ringKrullDim S ≤ ringKrullDim R := by
  letI := f.toAlgebra
  refine Order.krullDim_le_of_strictMono (PrimeSpectrum.comap f) fun p q hpq ↦ ?_
  rw [← PrimeSpectrum.asIdeal_lt_asIdeal] at hpq ⊢
  obtain ⟨x, hxq, hxp⟩ := SetLike.exists_of_lt hpq
  exact Ideal.comap_lt_comap_of_integral_mem_sdiff hpq.le ⟨hxq, hxp⟩ (hf x)

/-- If the quotient by every prime that is not minimal has Krull dimension at most `d`, the ring
has Krull dimension at most `d + 1`. -/
theorem ringKrullDim_le_add_one_of_forall_quotient_le {R : Type*} [CommRing R] {d : WithBot ℕ∞}
    (hd : 0 ≤ d)
    (h : ∀ p q : Ideal R, p.IsPrime → q.IsPrime → q < p → ringKrullDim (R ⧸ p) ≤ d) :
    ringKrullDim R ≤ d + 1 := by
  obtain ⟨d', rfl⟩ := WithBot.ne_bot_iff_exists.1 (ne_bot_of_le_ne_bot WithBot.coe_ne_bot hd)
  have hcoh (y q : PrimeSpectrum R) (hqy : q < y) : Order.coheight y ≤ d' := by
    have hset : Set.Ici y = PrimeSpectrum.zeroLocus (y.asIdeal : Set R) := by
      ext x
      rw [Set.mem_Ici, PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe,
        PrimeSpectrum.asIdeal_le_asIdeal]
    have h1 : (Order.coheight y : WithBot ℕ∞) = ringKrullDim (R ⧸ y.asIdeal) := by
      rw [Order.coheight_eq_krullDim_Ici, ringKrullDim_quotient, hset]
    have h2 := h y.asIdeal q.asIdeal y.isPrime q.isPrime
      ((PrimeSpectrum.asIdeal_lt_asIdeal q y).2 hqy)
    rw [← h1] at h2
    exact WithBot.coe_le_coe.1 h2
  rw [ringKrullDim, Order.krullDim_eq_iSup_coheight]
  refine iSup_le fun q ↦ ?_
  rw [← WithBot.coe_one, ← WithBot.coe_add, WithBot.coe_le_coe, Order.coheight_eq_iSup_gt_coheight]
  exact iSup₂_le fun y hy ↦ add_le_add (hcoh y q hy) le_rfl

/-! ### Rückert overrings -/

/-- The ring `I'` is **Rückert** over `I`, along the embedding `φ : I[X] →+* I'` and for the family
`W` of monic polynomials. Source: BGR 5.2.5/1. -/
structure IsRueckert {I I' : Type*} [CommRing I] [CommRing I'] (φ : I[X] →+* I')
    (W : Set I[X]) : Prop where
  /-- `I'` is an overring of `I[X]`. -/
  injective : Function.Injective φ
  /-- The members of `W` are monic. -/
  monic : ∀ ω ∈ W, ω.Monic
  /-- Axiom (1): if the product of two monic polynomials lies in `W`, so do the factors. -/
  of_mul : ∀ p q : I[X], p.Monic → q.Monic → p * q ∈ W → p ∈ W ∧ q ∈ W
  /-- Axiom (2): for `ω ∈ W` the natural map `I[X] ⧸ (ω) → I' ⧸ (ω)` is an isomorphism. -/
  bijective_quotientMap : ∀ ω ∈ W,
    Function.Bijective (Ideal.quotientMap ((Ideal.span {ω}).map φ) φ Ideal.le_comap_map)
  /-- Axiom (3): every nonzero element is, up to an automorphism and a unit, a member of `W`. -/
  exists_mul_mem : ∀ f : I', f ≠ 0 → ∃ (σ : I' ≃+* I') (e : I'ˣ) (ω : I[X]),
    ω ∈ W ∧ e * σ f = φ ω

namespace IsRueckert

variable {I I' : Type*} [CommRing I] [CommRing I'] {φ : I[X] →+* I'} {W : Set I[X]}

/-- For `ω ∈ W` the canonical map `I → I' ⧸ (ω)` is finite. Source: BGR 5.2.5/1 ("In particular,
the canonical map `I → I'/ωI'` is finite"). -/
theorem finite_mk_comp_C (h : IsRueckert φ W) {ω : I[X]} (hω : ω ∈ W) :
    ((Ideal.Quotient.mk ((Ideal.span {ω}).map φ)).comp (φ.comp C)).Finite := by
  have h1 : ((Ideal.Quotient.mk (Ideal.span {ω})).comp C).Finite := by
    rw [← Polynomial.algebraMap_eq, Ideal.Quotient.mk_comp_algebraMap, RingHom.finite_algebraMap]
    exact (h.monic ω hω).finite_quotient
  have h2 := (RingHom.Finite.of_surjective _ (h.bijective_quotientMap ω hω).2).comp h1
  rwa [← RingHom.comp_assoc, Ideal.quotientMap_comp_mk, RingHom.comp_assoc] at h2

/-- Every nonzero ideal of a Rückert overring contains, after an automorphism, a member of `W`.
Source: BGR 5.2.5/2 ("According to axiom (3), we may assume that `𝔞` contains a polynomial
`ω ∈ W`"). -/
theorem exists_ringEquiv_mem_map (h : IsRueckert φ W) {a : Ideal I'} (ha : a ≠ ⊥) :
    ∃ (σ : I' ≃+* I') (ω : I[X]), ω ∈ W ∧ φ ω ∈ a.map (σ : I' →+* I') := by
  obtain ⟨f, hfa, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot ha
  obtain ⟨σ, e, ω, hω, he⟩ := h.exists_mul_mem f hf0
  refine ⟨σ, ω, hω, ?_⟩
  rw [← he]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem (σ : I' →+* I') hfa)

/-- A Rückert overring of a noetherian ring is noetherian. Source: BGR 5.2.5/2. -/
theorem isNoetherianRing (h : IsRueckert φ W) [IsNoetherianRing I] : IsNoetherianRing I' := by
  refine (isNoetherianRing_iff_ideal_fg _).2 fun a ↦ ?_
  by_cases ha : a = ⊥
  · rw [ha]
    exact Submodule.fg_bot
  obtain ⟨σ, ω, hω, hmem⟩ := h.exists_ringEquiv_mem_map ha
  haveI : IsNoetherianRing (I' ⧸ (Ideal.span {ω}).map φ) :=
    isNoetherianRing_of_ringEquiv _ (RingEquiv.ofBijective _ (h.bijective_quotientMap ω hω))
  have hJ : (Ideal.span {ω}).map φ = Ideal.span {φ ω} := by
    rw [Ideal.map_span, Set.image_singleton]
  have hle : (Ideal.span {ω}).map φ ≤ a.map (σ : I' →+* I') := by
    rw [hJ, Ideal.span_le, Set.singleton_subset_iff]
    exact hmem
  have hfg : (a.map (σ : I' →+* I')).FG := by
    refine Ideal.fg_of_fg_map_of_fg_inf_ker_of_surjective
      (f := Ideal.Quotient.mk ((Ideal.span {ω}).map φ)) (IsNoetherian.noetherian _) ?_
      Ideal.Quotient.mk_surjective
    rw [Ideal.mk_ker, inf_eq_right.2 hle, hJ]
    exact Submodule.fg_span_singleton _
  have h' := hfg.map (σ.symm : I' →+* I')
  rwa [Ideal.map_of_equiv] at h'

/-- In a Rückert overring of a Jacobson ring, every nonzero prime is the intersection of the
maximal ideals containing it. -/
private lemma jacobson_eq_self_of_isPrime (h : IsRueckert φ W) [IsJacobsonRing I]
    {p : Ideal I'} [p.IsPrime] (hp0 : p ≠ ⊥) : p.jacobson = p := by
  obtain ⟨σ, ω, hω, hmem⟩ := h.exists_ringEquiv_mem_map hp0
  haveI : (p.map (σ : I' →+* I')).IsPrime := Ideal.map_isPrime_of_equiv σ
  suffices hp' : (p.map (σ : I' →+* I')).jacobson = p.map (σ : I' →+* I') by
    have h' := congrArg (Ideal.map (σ.symm : I' →+* I')) hp'
    rwa [Ideal.map_jacobson_of_bijective (f := (σ.symm : I' →+* I')) σ.symm.bijective,
      Ideal.map_of_equiv] at h'
  have hle : (Ideal.span {ω}).map φ ≤ p.map (σ : I' →+* I') := by
    rw [Ideal.map_span, Set.image_singleton, Ideal.span_le, Set.singleton_subset_iff]
    exact hmem
  have hint : ((Ideal.Quotient.factor hle).comp
      ((Ideal.Quotient.mk ((Ideal.span {ω}).map φ)).comp (φ.comp C))).IsIntegral :=
    RingHom.IsIntegral.trans _ _ (h.finite_mk_comp_C hω).to_isIntegral
      (RingHom.isIntegral_of_surjective _ (Ideal.Quotient.factor_surjective hle))
  haveI := isJacobsonRing_of_isIntegral' _ hint
  rw [Ideal.jacobson_eq_iff_jacobson_quotient_eq_bot]
  exact isJacobsonRing_iff_prime_eq.1 inferInstance ⊥ Ideal.isPrime_bot

/-- In a Rückert overring of a Jacobson ring, the nilradical of a nonzero ideal is its Jacobson
radical. Source: BGR 5.2.5/3. -/
theorem jacobson_eq_radical (h : IsRueckert φ W) [IsJacobsonRing I] {a : Ideal I'} (ha : a ≠ ⊥) :
    a.jacobson = a.radical := by
  refine le_antisymm ?_ Ideal.radical_le_jacobson
  rw [Ideal.radical_eq_sInf]
  refine le_sInf fun p ⟨hap, hp⟩ ↦ ?_
  have hp0 : p ≠ ⊥ := fun h0 ↦ ha (le_bot_iff.1 (h0 ▸ hap))
  calc a.jacobson ≤ p.jacobson := Ideal.jacobson_mono hap
    _ = p := jacobson_eq_self_of_isPrime h hp0

/-- A Rückert overring of a Jacobson ring whose Jacobson radical vanishes is a Jacobson ring.
Source: BGR 5.2.6/3. -/
theorem isJacobsonRing (h : IsRueckert φ W) [IsJacobsonRing I]
    (h0 : (⊥ : Ideal I').jacobson = ⊥) : IsJacobsonRing I' := by
  refine isJacobsonRing_iff_prime_eq.2 fun P hP ↦ ?_
  by_cases hP0 : P = ⊥
  · rw [hP0]
    exact h0
  · exact (h.jacobson_eq_radical hP0).trans hP.radical

/-- Monic polynomials whose product lies in `W` lie in `W`. -/
private lemma forall_mem_of_prod_mem (h : IsRueckert φ W) (s : Multiset I[X])
    (hm : ∀ q ∈ s, q.Monic) (hW : s.prod ∈ W) : ∀ q ∈ s, q ∈ W := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.prod_cons] at hW
    have hms : s.prod.Monic := by
      simpa using Polynomial.monic_multiset_prod_of_monic s id fun q hq ↦
        hm q (Multiset.mem_cons_of_mem hq)
    obtain ⟨haW, hsW⟩ := h.of_mul a s.prod (hm a (Multiset.mem_cons.2 (Or.inl rfl))) hms hW
    intro q hq
    rcases Multiset.mem_cons.1 hq with rfl | hq
    · exact haW
    · exact ih (fun q hq ↦ hm q (Multiset.mem_cons_of_mem hq)) hsW q hq

/-- A monic polynomial over a factorial domain is a product of monic primes. -/
private lemma exists_monic_prime_factors [IsDomain I] [UniqueFactorizationMonoid I]
    {ω : I[X]} (hm : ω.Monic) :
    ∃ s : Multiset I[X], (∀ q ∈ s, q.Monic ∧ Prime q) ∧ s.prod = ω := by
  classical
  obtain ⟨s, hprime, hassoc⟩ := UniqueFactorizationMonoid.exists_prime_factors ω hm.ne_zero
  have hunit (q : I[X]) (hq : q ∈ s) : IsUnit q.leadingCoeff :=
    hm.isUnit_leadingCoeff_of_dvd ((Multiset.dvd_prod hq).trans hassoc.dvd)
  let g : I[X] → I[X] := fun q ↦
    if hq : IsUnit q.leadingCoeff then C (↑hq.unit⁻¹ : I) * q else q
  have hg (q : I[X]) (hq : q ∈ s) : (g q).Monic ∧ Associated (g q) q := by
    have hu := hunit q hq
    simp only [g, dif_pos hu]
    refine ⟨?_, associated_unit_mul_left q _ ((Units.isUnit hu.unit⁻¹).map C)⟩
    rw [Polynomial.Monic.def, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
      hu.val_inv_mul]
  refine ⟨s.map g, fun q hq ↦ ?_, ?_⟩
  · obtain ⟨q₀, hq₀, rfl⟩ := Multiset.mem_map.1 hq
    exact ⟨(hg q₀ hq₀).1, (hg q₀ hq₀).2.symm.prime (hprime q₀ hq₀)⟩
  · have hprod : Associated (s.map g).prod s.prod := by
      rw [← Associates.mk_eq_mk_iff_associated, ← Associates.prod_mk, ← Associates.prod_mk,
        Multiset.map_map]
      congr 1
      exact Multiset.map_congr rfl fun q hq ↦ Associates.mk_eq_mk_iff_associated.2 (hg q hq).2
    exact Polynomial.eq_of_monic_of_associated
      (Polynomial.monic_multiset_prod_of_monic s g fun q hq ↦ (hg q hq).1) hm (hprod.trans hassoc)

/-- The image of a prime member of `W` is prime. -/
private lemma prime_map (h : IsRueckert φ W) {q : I[X]} (hq : q ∈ W) (hp : Prime q) :
    Prime (φ q) := by
  have hq0 : φ q ≠ 0 := fun h0 ↦ hp.ne_zero (h.injective (h0.trans (map_zero φ).symm))
  rw [← Ideal.span_singleton_prime hq0, ← Ideal.Quotient.isDomain_iff_prime]
  have hJ : (Ideal.span {q}).map φ = Ideal.span {φ q} := by
    rw [Ideal.map_span, Set.image_singleton]
  haveI : IsDomain (I[X] ⧸ Ideal.span {q}) :=
    (Ideal.Quotient.isDomain_iff_prime _).2 ((Ideal.span_singleton_prime hp.ne_zero).2 hp)
  rw [← hJ]
  exact MulEquiv.isDomain (I[X] ⧸ Ideal.span {q})
    (RingEquiv.ofBijective _ (h.bijective_quotientMap q hq)).symm.toMulEquiv

/-- An integral domain which is Rückert over a factorial ring is factorial.
Source: BGR 5.2.5/4. -/
theorem uniqueFactorizationMonoid (h : IsRueckert φ W) [IsDomain I]
    [UniqueFactorizationMonoid I] [IsDomain I'] : UniqueFactorizationMonoid I' := by
  refine UniqueFactorizationMonoid.of_exists_prime_factors fun f hf ↦ ?_
  obtain ⟨σ, e, ω, hω, he⟩ := h.exists_mul_mem f hf
  obtain ⟨s, hs, hsω⟩ := exists_monic_prime_factors (h.monic ω hω)
  have hsW := forall_mem_of_prod_mem h s (fun q hq ↦ (hs q hq).1) (by rw [hsω]; exact hω)
  refine ⟨(s.map φ).map σ.symm, fun b hb ↦ ?_, ?_⟩
  · obtain ⟨c, hc, rfl⟩ := Multiset.mem_map.1 hb
    obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.1 hc
    exact (MulEquiv.prime_iff σ.symm).2 (prime_map h (hsW q hq) (hs q hq).2)
  · have hprod : ((s.map φ).map σ.symm).prod = σ.symm (φ ω) := by
      rw [← map_multiset_prod σ.symm, ← map_multiset_prod φ, hsω]
    rw [hprod, ← he, map_mul, RingEquiv.symm_apply_apply]
    exact associated_unit_mul_left f _ ((Units.isUnit e).map σ.symm)

/-- For `ω ∈ W` the Krull dimension of `I' ⧸ (ω)` is at most that of `I`. Source: Bosch 1.2/10
("the canonical morphism `T_{n−1} → Tₙ → Tₙ/(g)` is finite"). -/
theorem ringKrullDim_quotient_le (h : IsRueckert φ W) {ω : I[X]} (hω : ω ∈ W) :
    ringKrullDim (I' ⧸ (Ideal.span {ω}).map φ) ≤ ringKrullDim I :=
  ringKrullDim_le_of_isIntegral _ (h.finite_mk_comp_C hω).to_isIntegral

/-- The Krull dimension of a Rückert overring is at most that of the base plus one.
Source: Bosch 1.2/10 (the descent `T_{n−1} → Tₙ/(g)` finite), BGR 6.1.2 (Remark). -/
theorem ringKrullDim_le (h : IsRueckert φ W) : ringKrullDim I' ≤ ringKrullDim I + 1 := by
  rcases subsingleton_or_nontrivial I with hI | hI
  · haveI : Subsingleton I' := subsingleton_of_zero_eq_one (by
      rw [← map_zero φ, ← map_one φ]
      exact congrArg φ (Subsingleton.elim _ _))
    rw [ringKrullDim_eq_bot_of_subsingleton]
    exact bot_le
  · refine ringKrullDim_le_add_one_of_forall_quotient_le ringKrullDim_nonneg_of_nontrivial
      fun p q hp hq hqp ↦ ?_
    obtain ⟨σ, ω, hω, hmem⟩ := h.exists_ringEquiv_mem_map (ne_bot_of_gt hqp)
    rw [ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv p _ σ rfl)]
    have hle : (Ideal.span {ω}).map φ ≤ p.map (σ : I' →+* I') := by
      rw [Ideal.map_span, Set.image_singleton, Ideal.span_le, Set.singleton_subset_iff]
      exact hmem
    exact (ringKrullDim_le_of_surjective _ (Ideal.Quotient.factor_surjective hle)).trans
      (h.ringKrullDim_quotient_le hω)

/-- If the variable `X` belongs to `W` and `I'` is a domain, the Krull dimension of a Rückert
overring is at least that of the base plus one. Source: BGR 6.1.2 (Remark: the chain
`0 ⊂ (X₁) ⊂ (X₁, X₂) ⊂ …`). -/
theorem ringKrullDim_add_one_le (h : IsRueckert φ W) [IsDomain I'] (hX : (X : I[X]) ∈ W) :
    ringKrullDim I + 1 ≤ ringKrullDim I' := by
  haveI : Nontrivial I := by
    by_contra hI
    rw [not_nontrivial_iff_subsingleton] at hI
    refine one_ne_zero (α := I') ?_
    rw [← map_one φ, ← map_zero φ]
    exact congrArg φ (Subsingleton.elim _ _)
  have hx : φ X ≠ 0 := fun h0 ↦ Polynomial.X_ne_zero (h.injective (h0.trans (map_zero φ).symm))
  have h1 := ringKrullDim_quotient_succ_le_of_nonZeroDivisor (mem_nonZeroDivisors_of_ne_zero hx)
  have hJ : (Ideal.span {(X : I[X])}).map φ = Ideal.span {φ X} := by
    rw [Ideal.map_span, Set.image_singleton]
  have hX0 : Ideal.span {(X : I[X])} = Ideal.span {X - C 0} := by
    rw [map_zero, sub_zero]
  let e1 : I[X] ⧸ Ideal.span {(X : I[X])} ≃+* I' ⧸ Ideal.span {φ X} :=
    (RingEquiv.ofBijective _ (h.bijective_quotientMap X hX)).trans (Ideal.quotEquivOfEq hJ)
  let e2 : I[X] ⧸ Ideal.span {(X : I[X])} ≃+* I :=
    (Ideal.quotEquivOfEq hX0).trans (Polynomial.quotientSpanXSubCAlgEquiv (0 : I)).toRingEquiv
  rwa [ringKrullDim_eq_of_ringEquiv (e1.symm.trans e2)] at h1

theorem ringKrullDim_eq (h : IsRueckert φ W) [IsDomain I'] (hX : (X : I[X]) ∈ W) :
    ringKrullDim I' = ringKrullDim I + 1 :=
  le_antisymm h.ringKrullDim_le (h.ringKrullDim_add_one_le hX)

end IsRueckert
