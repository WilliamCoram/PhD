/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.BirkovichWP.RingTheory.LaurentPolynomial.GaussExtension
import PhD.BirkovichWP.RingTheory.MvPowerSeries.Restricted.BaseChange
import PhD.BirkovichWP.RingTheory.PowerSeries.Restricted.WeierstrassPrep

/-! # Multivariate Weierstrass division and preparation at every radius

The endpoint theorems of the multivariate Weierstrass theory, for restricted power series
distinguished in `X 0` over a complete nontrivially normed ultrametric field `K`, at
**every** radius tuple `c` — no hypotheses on the radii.

The proof is by induction on the number of radii outside the divisible closure of the
value group of the bottom field:

* if every radius has a power realised in `K`, one finite spectral-norm extension realises
  them all as unit norms; divide there and descend
  (`MvPowerSeries.Restricted.weierstrassDivision_descend`);
* otherwise, pick a radius `c i` outside the divisible closure and pass to the Gauss
  extension `GaussExtension K (c i)` — a complete nontrivially normed ultrametric field in
  which `c i` becomes the norm of the unit `T`, while the count of unrealised radii drops;
  divide there by induction and descend along the `T⁰`-coefficient retraction
  (`weierstrassDivision_descend_of_retraction`).

Preparation is the corollary
`PowerSeries.Restricted.weierstrassPreparation_exists_of_forall_exists` of division,
transported along the splitting isomorphism.
-/

namespace MvPowerSeries.Restricted

universe u

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {n : ℕ} {c : Fin (n + 1) → ℝ} [Fact (∀ i, 0 < c i)]

/-- Nested-`∃!` congruence along a pointwise `Iff`; local plumbing for the transports of the
univariate `_of_forall_exists` corollaries through the splitting isomorphism. -/
private lemma existsUnique_congr' {α : Sort*} {p q : α → Prop} (h : ∀ a, p a ↔ q a) :
    (∃! a, p a) ↔ ∃! a, q a :=
  ⟨fun ⟨a, ha, hu⟩ ↦ ⟨a, (h a).mp ha, fun b hb ↦ hu b ((h b).mpr hb)⟩,
   fun ⟨a, ha, hu⟩ ↦ ⟨a, (h a).mpr ha, fun b hb ↦ hu b ((h b).mp hb)⟩⟩

/-- Multivariate Weierstrass division when every radius is realised in the value group:
transport of the univariate division over the coefficient Tate algebra, whose scaling
hypothesis is discharged by `MvPowerSeries.Restricted.exists_norm_inv_isUnit`. -/
private lemma weierstrassDivision_exists_of_forall_units
    (hc : ∀ i, ∃ u : Kˣ, ‖(u : K)‖ = c i) {g : Restricted K c} {s : ℕ}
    (hg : IsDistinguishedX0 g s) (f : Restricted K c) :
    ∃ (q : Restricted K c) (r : Polynomial (Restricted K (Fin.tail c))),
      r.degree < s ∧ f = g * q + Polynomial.toMvRestrictedX0 c r := by
  letI : Filter.NeBot (nhdsWithin (0 : K) {(0 : K)}ᶜ) := NormedField.nhdsNE_neBot 0
  obtain ⟨q', r', hr', hf'⟩ := PowerSeries.Restricted.weierstrassDivision_exists
    (hg : PowerSeries.IsDistinguished norm (c 0) (finSuccEquiv K c g).1 s)
    (finSuccEquiv K c f) (fun F hF ↦ exists_norm_inv_isUnit hc F hF)
  refine ⟨(finSuccEquiv K c).symm q', r', hr', ?_⟩
  have h := congrArg (finSuccEquiv K c).symm hf'
  rw [map_add, map_mul, RingEquiv.symm_apply_apply, RingEquiv.symm_apply_apply] at h
  exact h

/-- Multivariate Weierstrass division at divisible radii — the base case of the
radius-count induction: one finite spectral extension realises every radius, divide there,
descend along the finite retraction. -/
private lemma weierstrassDivision_exists_divisible
    (hdiv : ∀ i, MemDivisibleValueGroup K (c i))
    {g : Restricted K c} {s : ℕ} (hg : IsDistinguishedX0 g s) (f : Restricted K c) :
    ∃ (q : Restricted K c) (r : Polynomial (Restricted K (Fin.tail c))),
      r.degree < s ∧ f = g * q + Polynomial.toMvRestrictedX0 c r := by
  refine MemDivisibleValueGroup.elim_finite_extension
    (fun i ↦ (Fact.out : ∀ i, 0 < c i) i) hdiv ?_
  intro L _ _ _ _ _ hiso hcL
  obtain ⟨qL, rL, hrL, hfL⟩ := weierstrassDivision_exists_of_forall_units hcL
    (isDistinguishedX0_mapAlgebra hiso hg) (mapAlgebra c hiso f)
  obtain ⟨q₀, r₀, hr₀, heq, -, -⟩ := weierstrassDivision_descend hiso hg f hrL hfL
  exact ⟨q₀, r₀, hr₀, heq⟩

/-- The radius-count induction: multivariate Weierstrass division holds whenever at most
`N` radii lie outside the divisible closure of the value group — by passing to the Gauss
extension of an unrealised radius, which drops the count, and descending along the
`T⁰`-coefficient retraction. -/
private lemma weierstrassDivision_exists_of_card_le (N : ℕ) :
    ∀ (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K],
    ∀ (c : Fin (n + 1) → ℝ) [Fact (∀ i, 0 < c i)],
    Nat.card {i // ¬MemDivisibleValueGroup K (c i)} ≤ N →
    ∀ (g : Restricted K c) (s : ℕ), IsDistinguishedX0 g s → ∀ f : Restricted K c,
    ∃ (q : Restricted K c) (r : Polynomial (Restricted K (Fin.tail c))),
      r.degree < s ∧ f = g * q + Polynomial.toMvRestrictedX0 c r := by
  induction N with
  | zero =>
    intro K _ _ _ c _ hcard g s hg f
    have hall : ∀ i, MemDivisibleValueGroup K (c i) := by
      intro i
      by_contra hi
      haveI : Nonempty {i // ¬MemDivisibleValueGroup K (c i)} := ⟨⟨i, hi⟩⟩
      exact (Nat.card_pos).ne' (Nat.le_zero.mp hcard)
    exact weierstrassDivision_exists_divisible hall hg f
  | succ N ih =>
    intro K _ _ _ c _ hcard g s hg f
    by_cases hall : ∀ i, MemDivisibleValueGroup K (c i)
    · exact weierstrassDivision_exists_divisible hall hg f
    obtain ⟨i₀, hi₀⟩ := not_forall.mp hall
    haveI : Fact (0 < c i₀) := ⟨(Fact.out : ∀ i, 0 < c i) i₀⟩
    haveI : Fact (¬MemDivisibleValueGroup K (c i₀)) := ⟨hi₀⟩
    have hiso : ∀ a : K, ‖algebraMap K (GaussExtension K (c i₀)) a‖ = ‖a‖ := fun a ↦
      GaussExtension.norm_algebraMap a
    have hstep : Nat.card {i // ¬MemDivisibleValueGroup (GaussExtension K (c i₀)) (c i)}
        < Nat.card {i // ¬MemDivisibleValueGroup K (c i)} := by
      classical
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
      refine Fintype.card_lt_of_injective_of_notMem
        (fun j ↦ ⟨j.1, fun hK ↦ j.2 (GaussExtension.memDivisibleValueGroup_of_base hK)⟩)
        (fun a b hab ↦ Subtype.ext (by have h2 := congrArg Subtype.val hab; exact h2))
        (b := ⟨i₀, hi₀⟩) ?_
      rintro ⟨⟨j, hj2⟩, hj⟩
      have hj1 : j = i₀ := congrArg Subtype.val hj
      subst hj1
      exact hj2 GaussExtension.memDivisibleValueGroup_self
    obtain ⟨qL, rL, hrL, hfL⟩ := ih (GaussExtension K (c i₀)) c (by omega)
      (mapAlgebra c hiso g) s (isDistinguishedX0_mapAlgebra hiso hg) (mapAlgebra c hiso f)
    obtain ⟨q₀, r₀, hr₀, heq, -, -⟩ := weierstrassDivision_descend_of_retraction hiso
      GaussExtension.retraction GaussExtension.retraction_algebraMap
      (Cπ := 1) (fun x ↦ by rw [one_mul]; exact GaussExtension.norm_retraction_le x)
      hg f hrL hfL
    exact ⟨q₀, r₀, hr₀, heq⟩

/-! ## Weierstrass division -/

/-- **Multivariate Weierstrass division, existence, at every radius**: for `g`
distinguished in `X 0` of degree `s`, every `f` divides as `f = g * q + r` with `r` an
`X 0`-polynomial of degree `< s` — no hypotheses on the radius tuple. -/
theorem weierstrassDivision_exists {g : Restricted K c} {s : ℕ}
    (hg : IsDistinguishedX0 g s) (f : Restricted K c) :
    ∃ (q : Restricted K c) (r : Polynomial (Restricted K (Fin.tail c))),
      r.degree < s ∧ f = g * q + Polynomial.toMvRestrictedX0 c r :=
  weierstrassDivision_exists_of_card_le
    (Nat.card {i // ¬MemDivisibleValueGroup K (c i)}) K c le_rfl g s hg f

/-- **Multivariate Weierstrass division at every radius**: existence and uniqueness. -/
theorem weierstrassDivision_uniqueness {g : Restricted K c} {s : ℕ}
    (hg : IsDistinguishedX0 g s) (f : Restricted K c) :
    ∃! q : Restricted K c, ∃! r : Polynomial (Restricted K (Fin.tail c)),
      r.degree < s ∧ f = g * q + Polynomial.toMvRestrictedX0 c r := by
  obtain ⟨q₀, r₀, hr₀, hf₀⟩ := weierstrassDivision_exists hg f
  refine ⟨q₀, ⟨r₀, ⟨hr₀, hf₀⟩, ?_⟩, ?_⟩
  · rintro r' ⟨hr', hf'⟩
    exact Polynomial.toMvRestrictedX0_injective (add_left_cancel (hf'.symm.trans hf₀))
  · rintro q' ⟨r', ⟨hr', hf'⟩, -⟩
    exact weierstrassDivision_q_unique hg hr' hf' hr₀ hf₀

omit [CompleteSpace K] in
/-- **Multivariate Weierstrass division for polynomials at every radius**: the Weierstrass
quotient of `X 0`-polynomials is itself an `X 0`-polynomial.  (Completeness-free: the
division is Euclidean division over the coefficient Tate algebra, transported through the
splitting isomorphism.) -/
theorem weierstrassDivision_polynomial {g₀ : Polynomial (Restricted K (Fin.tail c))} {s : ℕ}
    (hg : IsDistinguishedX0 (Polynomial.toMvRestrictedX0 c g₀) s) (hgs : g₀.degree ≤ s)
    (f₀ : Polynomial (Restricted K (Fin.tail c))) :
    ∃! q : Polynomial (Restricted K (Fin.tail c)),
    ∃! r : Polynomial (Restricted K (Fin.tail c)), r.degree < s ∧
      Polynomial.toMvRestrictedX0 c f₀ =
        Polynomial.toMvRestrictedX0 c g₀ * Polynomial.toMvRestrictedX0 c q +
          Polynomial.toMvRestrictedX0 c r := by
  have hg' : PowerSeries.IsDistinguished norm (c 0) (Polynomial.toRestricted (c 0) g₀).1 s := by
    have h := hg
    unfold IsDistinguishedX0 at h
    rwa [Polynomial.finSuccEquiv_toMvRestrictedX0] at h
  have h := PowerSeries.Restricted.weierstrassDivision_polynomial hg' hgs f₀
  refine (existsUnique_congr' fun q ↦ existsUnique_congr' fun r ↦
    and_congr_right fun _ ↦ ?_).mpr h
  constructor
  · intro heq
    have h2 := congrArg (finSuccEquiv K c) heq
    simp only [map_add, map_mul, Polynomial.finSuccEquiv_toMvRestrictedX0] at h2
    exact h2
  · intro heq
    have h2 := congrArg (finSuccEquiv K c).symm heq
    rw [map_add, map_mul] at h2
    exact h2

/-! ## Weierstrass preparation -/

/-- The unconditional multivariate division, as a division oracle over the coefficient Tate
algebra at radius `c 0` — the hypothesis shape consumed by the univariate
`_of_forall_exists` preparation corollaries. -/
private lemma weierstrassDivision_forall_exists_tate :
    ∀ (G : PowerSeries.Restricted (Restricted K (Fin.tail c)) (c 0)) (t : ℕ),
      PowerSeries.IsDistinguished norm (c 0) G.1 t →
      ∀ F : PowerSeries.Restricted (Restricted K (Fin.tail c)) (c 0),
      ∃ (Q : PowerSeries.Restricted (Restricted K (Fin.tail c)) (c 0))
        (r : Polynomial (Restricted K (Fin.tail c))), r.degree < t ∧
        F = G * Q + Polynomial.toRestricted (c 0) r := by
  intro G t hG F
  obtain ⟨q, r, hr, hf⟩ := weierstrassDivision_exists (g := (finSuccEquiv K c).symm G)
    ((isDistinguishedX0_finSuccEquiv_symm G t).mpr hG) ((finSuccEquiv K c).symm F)
  refine ⟨finSuccEquiv K c q, r, hr, ?_⟩
  have h2 := congrArg (finSuccEquiv K c) hf
  rwa [RingEquiv.apply_symm_apply, map_add, map_mul, RingEquiv.apply_symm_apply,
    Polynomial.finSuccEquiv_toMvRestrictedX0] at h2

/-- **Multivariate Weierstrass preparation, existence, at every radius**: `g` distinguished
in `X 0` of degree `s` factors as a unit times a monic `X 0`-polynomial of degree `s`. -/
theorem weierstrassPreparation_exists {g : Restricted K c} {s : ℕ}
    (hg : IsDistinguishedX0 g s) :
    ∃ (ω : Polynomial (Restricted K (Fin.tail c))) (e : Restricted K c), ω.Monic ∧
      ω.degree = s ∧ ‖Polynomial.toMvRestrictedX0 c ω‖ = (c 0) ^ s ∧ IsUnit e ∧
      g = e * Polynomial.toMvRestrictedX0 c ω := by
  obtain ⟨ω, e, ωm, ωd, ωn, he, hgeq⟩ :=
    PowerSeries.Restricted.weierstrassPreparation_exists_of_forall_exists
      (weierstrassDivision_forall_exists_tate (K := K) (c := c)) hg
  refine ⟨ω, (finSuccEquiv K c).symm e, ωm, ωd, ?_,
    (isUnit_finSuccEquiv_symm_iff e).mpr he, ?_⟩
  · rw [Polynomial.norm_toMvRestrictedX0]
    exact ωn
  · have h2 := congrArg (finSuccEquiv K c).symm hgeq
    rw [RingEquiv.symm_apply_apply, map_mul] at h2
    exact h2

/-- **Multivariate Weierstrass preparation at every radius**: the factorisation is
unique. -/
theorem weierstrassPreparation_unique {g : Restricted K c} {s : ℕ}
    (hg : IsDistinguishedX0 g s) :
    ∃! ω : Polynomial (Restricted K (Fin.tail c)), ∃! e : Restricted K c, ω.Monic ∧
      ω.degree = s ∧ ‖Polynomial.toMvRestrictedX0 c ω‖ = (c 0) ^ s ∧ IsUnit e ∧
      g = e * Polynomial.toMvRestrictedX0 c ω := by
  have h := PowerSeries.Restricted.weierstrassPreparation_unique_of_forall_exists
    (weierstrassDivision_forall_exists_tate (K := K) (c := c))
    (hg : PowerSeries.IsDistinguished norm (c 0) (finSuccEquiv K c g).1 s)
  refine (existsUnique_congr' fun ω ↦
    (finSuccEquiv K c).toEquiv.existsUnique_congr fun e ↦ ?_).mpr h
  show _ ↔ ω.Monic ∧ ω.degree = s ∧ ‖Polynomial.toRestricted (c 0) ω‖ = (c 0) ^ s ∧
    IsUnit (finSuccEquiv K c e) ∧
    finSuccEquiv K c g = finSuccEquiv K c e * Polynomial.toRestricted (c 0) ω
  refine and_congr_right fun _ ↦ and_congr_right fun _ ↦ ?_
  rw [Polynomial.norm_toMvRestrictedX0]
  refine and_congr_right fun _ ↦ and_congr ?_ ?_
  · refine ⟨fun h4 ↦ h4.map (finSuccEquiv K c), fun h4 ↦ ?_⟩
    have h5 := h4.map (finSuccEquiv K c).symm
    rwa [RingEquiv.symm_apply_apply] at h5
  · constructor
    · intro h5
      rw [h5, map_mul, Polynomial.finSuccEquiv_toMvRestrictedX0]
    · intro h5
      refine (finSuccEquiv K c).injective ?_
      rw [map_mul, Polynomial.finSuccEquiv_toMvRestrictedX0]
      exact h5

/-- **Multivariate Weierstrass preparation for polynomials at every radius**: if `g` is an
`X 0`-polynomial, the unit `e` of its preparation is itself an `X 0`-polynomial.
(Unit-ness of `e` is in the restricted power series ring, not in the polynomial ring.) -/
theorem weierstrassPreparation_polynomial
    {g₀ : Polynomial (Restricted K (Fin.tail c))} {s : ℕ}
    (hg : IsDistinguishedX0 (Polynomial.toMvRestrictedX0 c g₀) s) :
    ∃! ω : Polynomial (Restricted K (Fin.tail c)),
    ∃! e : Polynomial (Restricted K (Fin.tail c)), ω.Monic ∧ ω.degree = s ∧
      ‖Polynomial.toMvRestrictedX0 c ω‖ = (c 0) ^ s ∧
      IsUnit (Polynomial.toMvRestrictedX0 c e) ∧
      Polynomial.toMvRestrictedX0 c g₀ =
        Polynomial.toMvRestrictedX0 c e * Polynomial.toMvRestrictedX0 c ω := by
  have hg' : PowerSeries.IsDistinguished norm (c 0) (Polynomial.toRestricted (c 0) g₀).1 s := by
    have h := hg
    unfold IsDistinguishedX0 at h
    rwa [Polynomial.finSuccEquiv_toMvRestrictedX0] at h
  have h := PowerSeries.Restricted.weierstrassPreparation_polynomial_of_forall_exists
    (weierstrassDivision_forall_exists_tate (K := K) (c := c)) hg'
  refine (existsUnique_congr' fun ω ↦ existsUnique_congr' fun e ↦ ?_).mpr h
  refine and_congr_right fun _ ↦ and_congr_right fun _ ↦ ?_
  rw [Polynomial.norm_toMvRestrictedX0]
  refine and_congr_right fun _ ↦ and_congr ?_ ?_
  · exact isUnit_finSuccEquiv_symm_iff (Polynomial.toRestricted (c 0) e)
  · constructor
    · intro heq
      have h2 := congrArg (finSuccEquiv K c) heq
      simp only [map_mul, Polynomial.finSuccEquiv_toMvRestrictedX0] at h2
      exact h2
    · intro heq
      have h2 := congrArg (finSuccEquiv K c).symm heq
      rw [map_mul] at h2
      exact h2

end MvPowerSeries.Restricted
