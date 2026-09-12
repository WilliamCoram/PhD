/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.Main.BirkovichWP.RingTheory.PowerSeries.Restricted.WeierstrassDivision
import PhD.Main.BirkovichWP.RingTheory.PowerSeries.Restricted.WeierstrassDivisionOracle

/-! # Weierstrass preparation for restricted power series

Let `R` be a complete normed commutative ring with ultrametric distance, multiplicative norm
and `‖1‖ = 1`, whose origin is not isolated.  **Weierstrass preparation** states that under
the scaling hypothesis `hunit` of Weierstrass division, a restricted power series `g`
distinguished of degree `s` factors uniquely as `g = e * ω` with `ω` a monic polynomial of
degree `s` with `‖ω‖ = c ^ s` (its top Gauss term) and `e` a unit of `Restricted R c`.
`hunit` forces the radius to be realised by a unit — `c = ‖u‖` with `u : Rˣ`
(`exists_units_norm_eq`); over a normed field it holds precisely when `c` lies in the value
group `‖Rˣ‖`.

Preparation is a **corollary of division** (`weierstrassPreparation_exists_of_forall_exists`):
dividing `X ^ s` by `g` produces `g * q = ω := X ^ s - r`, monic and distinguished of degree
`s`; dividing `g` by `ω` gives `g = ω * P + S`, hence `g = g * (q * P) + S`, and comparing
with the trivial division `g = g * 1 + 0` the hypothesis-free quotient uniqueness forces
`q * P = 1` — so `P` is a unit and `g = P * ω`.  The corollary is instantiated at every
division-existence statement, so preparation automatically holds at whatever generality
division does.
-/

open Filter
open scoped Topology

namespace PowerSeries.Restricted

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R]
  [NormMulClass R] [NormOneClass R] [NeBot (𝓝[≠] (0 : R))]

section Norm

variable (c : ℝ) [Fact (0 < c)]

omit [CompleteSpace R] [NormMulClass R] [(𝓝[≠] (0 : R)).NeBot] in
/-- If `deg r < s` and `‖r‖ ≤ c ^ s` then `X ^ s - r` has norm `c ^ s` as a restricted power
series at radius `c`. -/
lemma norm_toRestricted_X_pow_sub {r : Polynomial R} {s : ℕ} (hr : r.degree < s)
    (hrn : ‖Polynomial.toRestricted c r‖ ≤ c ^ s) :
    ‖Polynomial.toRestricted c (Polynomial.X ^ s - r)‖ = c ^ s := by
  have hXs : ‖Polynomial.toRestricted c (Polynomial.X ^ s : Polynomial R)‖ = c ^ s := by
    rw [← Polynomial.monomial_one_right_eq_X_pow, Polynomial.toRestricted_monomial,
      norm_monomial, norm_one, one_mul]
  refine le_antisymm ?_ ?_
  · rw [map_sub]
    have h1 := IsUltrametricDist.norm_add_le_max (Polynomial.toRestricted c (Polynomial.X ^ s))
      (-(Polynomial.toRestricted c r))
    rw [← sub_eq_add_neg, norm_neg] at h1
    exact h1.trans (max_le hXs.le hrn)
  · have h2 := PowerSeries.le_gaussNorm norm c
      (Polynomial.toRestricted c (Polynomial.X ^ s - r)).1 (hasGaussNorm c _) s
    have hcs : coeff s (Polynomial.toRestricted c (Polynomial.X ^ s - r)).1 = 1 := by
      rw [Polynomial.val_toRestricted, Polynomial.coeff_coe, Polynomial.coeff_sub,
        Polynomial.coeff_X_pow, if_pos rfl, Polynomial.coeff_eq_zero_of_degree_lt hr, sub_zero]
    rw [norm_def]
    calc (c : ℝ) ^ s = ‖(1 : R)‖ * c ^ s := by rw [norm_one, one_mul]
      _ = ‖coeff s (Polynomial.toRestricted c (Polynomial.X ^ s - r)).1‖ * c ^ s := by rw [hcs]
      _ ≤ _ := h2

end Norm

private lemma monic_and_degree_of_coeff {A : Type*} [Semiring A] [Nontrivial A]
    {p : Polynomial A} {s : ℕ} (hs : p.coeff s = 1) (hgt : ∀ v, s < v → p.coeff v = 0) :
    p.Monic ∧ p.degree = s := by
  have hdeg : p.degree = s := le_antisymm
    ((Polynomial.degree_le_iff_coeff_zero _ _).mpr fun m hm ↦ hgt m (mod_cast hm))
    (Polynomial.le_degree_of_ne_zero (by rw [hs]; exact one_ne_zero))
  refine ⟨?_, hdeg⟩
  rw [Polynomial.Monic, Polynomial.leadingCoeff, Polynomial.natDegree_eq_of_degree_eq_some hdeg]
  exact hs

omit [CompleteSpace R] [(𝓝[≠] (0 : R)).NeBot] in
private lemma exists_monic_mul_eq_of_isDistinguished {c : ℝ} [Fact (0 < c)]
    (hdiv : ∀ (g : Restricted R c) (s : ℕ), IsDistinguished norm c g.1 s →
      ∀ f : Restricted R c, ∃ (q : Restricted R c) (r : Polynomial R), r.degree < s ∧
        f = g * q + Polynomial.toRestricted c r)
    {g : Restricted R c} {s : ℕ} (hg : IsDistinguished norm c g.1 s) :
    ∃ (ω : Polynomial R) (q : Restricted R c), ω.Monic ∧ ω.degree = s ∧
      ‖Polynomial.toRestricted c ω‖ = c ^ s ∧
      IsDistinguished norm c (Polynomial.toRestricted c ω).1 s ∧
      g * q = Polynomial.toRestricted c ω := by
  have hntR : Nontrivial R := hg.nontrivial
  obtain ⟨q, r, rd, hXdiv⟩ := hdiv g s hg (Polynomial.toRestricted c (Polynomial.X ^ s))
  have hω_gt : ∀ v, s < v → (Polynomial.X ^ s - r : Polynomial R).coeff v = 0 := fun v hv ↦ by
    rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow, if_neg (by omega),
      Polynomial.coeff_eq_zero_of_degree_lt (rd.trans_le (by exact_mod_cast hv.le)), sub_zero]
  have hω_s : (Polynomial.X ^ s - r : Polynomial R).coeff s = 1 := by
    rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow, if_pos rfl,
      Polynomial.coeff_eq_zero_of_degree_lt rd, sub_zero]
  obtain ⟨hω_monic, hω_deg⟩ := monic_and_degree_of_coeff hω_s hω_gt
  have hXn : ‖Polynomial.toRestricted c (Polynomial.X ^ s : Polynomial R)‖ = c ^ s := by
    rw [← Polynomial.monomial_one_right_eq_X_pow, Polynomial.toRestricted_monomial,
      norm_monomial, norm_one, one_mul]
  have rn : ‖Polynomial.toRestricted c r‖ ≤ c ^ s := by
    rw [← hXn]
    exact norm_r_le_of_eq_mul_add c hg rd hXdiv
  have ωn := norm_toRestricted_X_pow_sub c rd rn
  refine ⟨Polynomial.X ^ s - r, q, hω_monic, hω_deg, ωn,
    isDistinguished_toRestricted_of_monic hω_monic hω_deg ωn, ?_⟩
  rw [map_sub, hXdiv]
  abel

omit [CompleteSpace R] [NormOneClass R] [(𝓝[≠] (0 : R)).NeBot] in
private lemma monic_eq_of_isUnit_mul_eq {c : ℝ} [Fact (0 < c)] {g : Restricted R c} {s : ℕ}
    (hg : IsDistinguished norm c g.1 s) {ω ω' : Polynomial R} {e e' : Restricted R c}
    (ωm : ω.Monic) (ωd : ω.degree = s) (ω'm : ω'.Monic) (ω'd : ω'.degree = s)
    (he : IsUnit e) (he' : IsUnit e') (hg1 : g = e * Polynomial.toRestricted c ω)
    (hg1' : g = e' * Polynomial.toRestricted c ω') : ω' = ω := by
  have hntR : Nontrivial R := hg.nontrivial
  obtain ⟨ue, hue⟩ := he
  obtain ⟨ue', hue'⟩ := he'
  have rd : (ω' - ω).degree < (s : WithBot ℕ) := by
    simpa [ω'd] using Polynomial.degree_sub_lt (ω'd.trans ωd.symm) ω'm.ne_zero
      (by rw [ω'm.leadingCoeff, ωm.leadingCoeff])
  have h_e : g * (↑ue⁻¹ : Restricted R c) = Polynomial.toRestricted c ω := by
    rw [hg1, ← hue, mul_comm (↑ue : Restricted R c) _, mul_assoc, ue.mul_inv, mul_one]
  have h_e' : g * (↑ue'⁻¹ : Restricted R c) = Polynomial.toRestricted c ω' := by
    rw [hg1', ← hue', mul_comm (↑ue' : Restricted R c) _, mul_assoc, ue'.mul_inv, mul_one]
  have hzero : (0 : Restricted R c) = g * ((↑ue⁻¹ : Restricted R c) - ↑ue'⁻¹)
      + Polynomial.toRestricted c (ω' - ω) := by
    rw [mul_sub, map_sub, h_e, h_e']
    abel
  have h_bd := norm_r_le_of_eq_mul_add c hg rd hzero
  rw [norm_zero] at h_bd
  exact sub_eq_zero.mp (Polynomial.toRestricted_injective c
    (by rw [map_zero]; exact norm_le_zero_iff.mp h_bd))

omit [CompleteSpace R] [(𝓝[≠] (0 : R)).NeBot] in
/-- **Weierstrass preparation is a corollary of Weierstrass division**: if every `f` divides
by every distinguished series at radius `c`, then every `g` distinguished of degree `s`
factors as a unit times a monic polynomial of degree `s` and norm `c ^ s`.

Dividing `X ^ s` by `g` gives `g * q = ω := X ^ s - r`, monic and distinguished; dividing
`g` by `ω` gives `g = ω * P + S`, hence `g = g * (q * P) + S`, and comparing with the
trivial division `g = g * 1 + 0` the hypothesis-free quotient uniqueness forces
`q * P = 1` — so `P` is a unit and `g = P * ω`. -/
theorem weierstrassPreparation_exists_of_forall_exists {c : ℝ} [Fact (0 < c)]
    (hdiv : ∀ (g : Restricted R c) (s : ℕ), IsDistinguished norm c g.1 s →
      ∀ f : Restricted R c, ∃ (q : Restricted R c) (r : Polynomial R), r.degree < s ∧
        f = g * q + Polynomial.toRestricted c r)
    {g : Restricted R c} {s : ℕ} (hg : IsDistinguished norm c g.1 s) :
    ∃ (ω : Polynomial R) (e : Restricted R c), ω.Monic ∧ ω.degree = s ∧
      ‖Polynomial.toRestricted c ω‖ = c ^ s ∧ IsUnit e ∧
      g = e * Polynomial.toRestricted c ω := by
  obtain ⟨ω, q, hω_monic, hω_deg, ωn, hω_dist, hgq⟩ :=
    exists_monic_mul_eq_of_isDistinguished hdiv hg
  obtain ⟨P, S, hS, hgP⟩ := hdiv (Polynomial.toRestricted c ω) s hω_dist g
  have hgqP : g = g * (q * P) + Polynomial.toRestricted c S := by
    rw [← mul_assoc, hgq]
    exact hgP
  have h1 : (1 : Restricted R c) = q * P := weierstrassDivision_q_unique c hg
    (by rw [Polynomial.degree_zero]; exact WithBot.bot_lt_coe s)
    (by rw [mul_one, map_zero, add_zero]) hS hgqP
  refine ⟨ω, P, hω_monic, hω_deg, ωn,
    IsUnit.of_mul_eq_one q (by rw [mul_comm]; exact h1.symm), ?_⟩
  calc g = g * (q * P) := by rw [← h1, mul_one]
    _ = (g * q) * P := by ring
    _ = Polynomial.toRestricted c ω * P := by rw [hgq]
    _ = P * Polynomial.toRestricted c ω := mul_comm _ _

omit [CompleteSpace R] [(𝓝[≠] (0 : R)).NeBot] in
/-- **Weierstrass preparation uniqueness is a corollary of division existence**: the unit is
unique by norm-cancellation against `‖ω‖ = c ^ s ≠ 0`, and the polynomial by the
hypothesis-free remainder bound applied to the difference of the two factorisations. -/
theorem weierstrassPreparation_unique_of_forall_exists {c : ℝ} [Fact (0 < c)]
    (hdiv : ∀ (g : Restricted R c) (s : ℕ), IsDistinguished norm c g.1 s →
      ∀ f : Restricted R c, ∃ (q : Restricted R c) (r : Polynomial R), r.degree < s ∧
        f = g * q + Polynomial.toRestricted c r)
    {g : Restricted R c} {s : ℕ} (hg : IsDistinguished norm c g.1 s) :
    ∃! ω : Polynomial R, ∃! e : Restricted R c, ω.Monic ∧ ω.degree = s ∧
      ‖Polynomial.toRestricted c ω‖ = c ^ s ∧ IsUnit e ∧
      g = e * Polynomial.toRestricted c ω := by
  have hntR : Nontrivial R := hg.nontrivial
  obtain ⟨ω, e, ωm, ωd, ωn, he, hg1⟩ :=
    weierstrassPreparation_exists_of_forall_exists hdiv hg
  have hc0 : (0 : ℝ) < c := Fact.out
  refine ⟨ω, ⟨e, ⟨ωm, ωd, ωn, he, hg1⟩, ?_⟩, ?_⟩
  · rintro e' ⟨-, -, -, -, hge'⟩
    have hsub : (e' - e) * Polynomial.toRestricted c ω = 0 := by
      rw [sub_mul, ← hge', ← hg1, sub_self]
    have hnorm0 := congrArg norm hsub
    rw [norm_mul, ωn, norm_zero] at hnorm0
    exact sub_eq_zero.mp (norm_eq_zero.mp
      ((mul_eq_zero.mp hnorm0).resolve_right (pow_pos hc0 s).ne'))
  · rintro ω' ⟨e', ⟨ω'm, ω'd, ω'n, he', hg1'⟩, -⟩
    exact monic_eq_of_isUnit_mul_eq hg ωm ωd ω'm ω'd he he' hg1 hg1'

omit [CompleteSpace R] [(𝓝[≠] (0 : R)).NeBot] in
/-- **Weierstrass preparation for polynomials is a corollary of division existence**: if `g`
is a polynomial, the unit `e` of its preparation is itself a polynomial.

Note `IsUnit (Polynomial.toRestricted c e)` is unit-ness in the restricted power series ring,
not in `R[X]`: over `ℤ_p` at radius `1` the unit `e = 1 + p • X` is a polynomial but not a
unit of `ℤ_p[X]`. -/
theorem weierstrassPreparation_polynomial_of_forall_exists {c : ℝ} [Fact (0 < c)]
    (hdiv : ∀ (g : Restricted R c) (s : ℕ), IsDistinguished norm c g.1 s →
      ∀ f : Restricted R c, ∃ (q : Restricted R c) (r : Polynomial R), r.degree < s ∧
        f = g * q + Polynomial.toRestricted c r)
    {g₀ : Polynomial R} {s : ℕ}
    (hg : IsDistinguished norm c (Polynomial.toRestricted c g₀).1 s) :
    ∃! ω : Polynomial R, ∃! e : Polynomial R, ω.Monic ∧ ω.degree = s ∧
      ‖Polynomial.toRestricted c ω‖ = c ^ s ∧ IsUnit (Polynomial.toRestricted c e) ∧
      Polynomial.toRestricted c g₀ =
        Polynomial.toRestricted c e * Polynomial.toRestricted c ω := by
  obtain ⟨ω, ⟨e, ⟨ωm, ωd, ωn, he, hgeq⟩, he_uniq⟩, hω_uniq⟩ :=
    weierstrassPreparation_unique_of_forall_exists hdiv hg
  have hωdist := isDistinguished_toRestricted_of_monic ωm ωd ωn
  have h0 : (0 : Polynomial R).degree < (s : WithBot ℕ) := by
    rw [Polynomial.degree_zero]
    exact WithBot.bot_lt_coe s
  obtain ⟨e₀, ⟨r₀, ⟨hr₀, hf₀⟩, -⟩, -⟩ := weierstrassDivision_polynomial hωdist ωd.le g₀
  have he₀ : e = Polynomial.toRestricted c e₀ :=
    weierstrassDivision_q_unique c hωdist (f := Polynomial.toRestricted c g₀) h0
      (by rw [map_zero, add_zero, hgeq, mul_comm]) hr₀ hf₀
  have hg₀ : Polynomial.toRestricted c g₀ =
      Polynomial.toRestricted c e₀ * Polynomial.toRestricted c ω := he₀ ▸ hgeq
  refine ⟨ω, ⟨e₀, ⟨ωm, ωd, ωn, he₀ ▸ he, hg₀⟩, ?_⟩, ?_⟩
  · rintro e' ⟨-, -, -, hu', hg'⟩
    exact Polynomial.toRestricted_injective c
      ((he_uniq _ ⟨ωm, ωd, ωn, hu', hg'⟩).trans he₀)
  · rintro ω' ⟨e', ⟨ω'm, ω'd, ω'n, hu', hg'⟩, -⟩
    refine hω_uniq ω' ⟨Polynomial.toRestricted c e', ⟨ω'm, ω'd, ω'n, hu', hg'⟩, ?_⟩
    rintro e'' ⟨-, -, -, -, hg''⟩
    exact weierstrassDivision_q_unique c (isDistinguished_toRestricted_of_monic ω'm ω'd ω'n)
      (f := Polynomial.toRestricted c g₀) h0
      (by rw [map_zero, add_zero, hg'', mul_comm]) h0
      (by rw [map_zero, add_zero, hg', mul_comm])

section General

variable {c : ℝ} [Fact (0 < c)]

/-- **Weierstrass preparation, existence**: for `g` distinguished of degree `s`, under the
`hunit` scaling hypothesis (over a normed field: precisely when `c` lies in the value group
`‖Rˣ‖`, cf. `exists_units_norm_eq`), there are a monic polynomial `ω` of degree `s` with
`‖ω‖ = c ^ s` and a unit `e` with `g = e * ω`. -/
theorem weierstrassPreparation_exists {g : Restricted R c}
    {s : ℕ} (hg : IsDistinguished norm c g.1 s)
    (hunit : ∀ f : Restricted R c, f ≠ 0 → ∃ a : R, ‖a‖ = ‖f‖⁻¹ ∧ IsUnit a) :
    ∃ (ω : Polynomial R) (e : Restricted R c), ω.Monic ∧ ω.degree = s ∧
      ‖Polynomial.toRestricted c ω‖ = c ^ s ∧ IsUnit e ∧
      g = e * Polynomial.toRestricted c ω :=
  weierstrassPreparation_exists_of_forall_exists
    (fun _ _ hg' f ↦ weierstrassDivision_exists hg' f hunit) hg

/-- **Weierstrass preparation, uniqueness**: the factorisation `g = e * ω` of
`weierstrassPreparation_exists` is unique. -/
theorem weierstrassPreparation_unique {g : Restricted R c}
    {s : ℕ} (hg : IsDistinguished norm c g.1 s)
    (hunit : ∀ f : Restricted R c, f ≠ 0 → ∃ a : R, ‖a‖ = ‖f‖⁻¹ ∧ IsUnit a) :
    ∃! ω : Polynomial R, ∃! e : Restricted R c, ω.Monic ∧ ω.degree = s ∧
      ‖Polynomial.toRestricted c ω‖ = c ^ s ∧ IsUnit e ∧
      g = e * Polynomial.toRestricted c ω :=
  weierstrassPreparation_unique_of_forall_exists
    (fun _ _ hg' f ↦ weierstrassDivision_exists hg' f hunit) hg

/-- **Weierstrass preparation for polynomials**: if `g` is a polynomial, the unit `e` of its
preparation is itself a polynomial.

Note `IsUnit (Polynomial.toRestricted c e)` is unit-ness in the restricted power series ring,
not in `R[X]`: over `ℤ_p` at radius `1` the unit `e = 1 + p • X` is a polynomial but not a
unit of `ℤ_p[X]`. -/
theorem weierstrassPreparation_polynomial {g₀ : Polynomial R}
    {s : ℕ} (hg : IsDistinguished norm c (Polynomial.toRestricted c g₀).1 s)
    (hunit : ∀ f : Restricted R c, f ≠ 0 → ∃ a : R, ‖a‖ = ‖f‖⁻¹ ∧ IsUnit a) :
    ∃! ω : Polynomial R, ∃! e : Polynomial R, ω.Monic ∧ ω.degree = s ∧
      ‖Polynomial.toRestricted c ω‖ = c ^ s ∧ IsUnit (Polynomial.toRestricted c e) ∧
      Polynomial.toRestricted c g₀ =
        Polynomial.toRestricted c e * Polynomial.toRestricted c ω :=
  weierstrassPreparation_polynomial_of_forall_exists
    (fun _ _ hg' f ↦ weierstrassDivision_exists hg' f hunit) hg

end General

end PowerSeries.Restricted
