/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.Main.ForMathlib.RingTheory.PowerSeries.Restricted.GaussNorm

/-! # Distinguished power series

A power series `f` is **distinguished of degree `s` at radius `c`** if its `s`-th coefficient
is a unit, the `s`-th Gauss term `v (coeff s f) * c ^ s` attains the Gauss norm, and it
strictly dominates every later Gauss term.  This is the weighted predicate
(`distinguishedGen` of the legacy development): the radius weights `c ^ t` are what make the
notion correct at a general radius; at `c = 1` they are invisible.

## Main definitions

* `PowerSeries.IsDistinguished`: `f` is distinguished of degree `s` at radius `c`.

## Main results

* `PowerSeries.IsDistinguished.le_of_achievesGaussNorm`: the distinguished degree is the
  largest index achieving the Gauss norm.
* `PowerSeries.IsDistinguished.C_mul`: multiplying by a unit constant preserves
  distinguishedness.
* `PowerSeries.Restricted.isDistinguished_toRestricted_of_monic`: a monic polynomial of
  degree `s` whose restricted power series has norm `c ^ s` is distinguished of degree `s`.
-/

namespace PowerSeries

section Def

variable {R : Type*} [Semiring R] (v : R → ℝ) (c : ℝ) (f : PowerSeries R) (s : ℕ)

/-- `f` is **distinguished of degree `s` at radius `c`**: the `s`-th coefficient is a unit,
its Gauss term attains the Gauss norm, and it strictly dominates every later Gauss term. -/
structure IsDistinguished : Prop where
  /-- The `s`-th coefficient is a unit. -/
  isUnit_coeff : IsUnit (coeff s f)
  /-- The `s`-th Gauss term attains the Gauss norm. -/
  gaussNorm_eq : gaussNorm v c f = v (coeff s f) * c ^ s
  /-- The `s`-th Gauss term strictly dominates every later Gauss term. -/
  gaussTerm_lt : ∀ t, s < t → v (coeff t f) * c ^ t < v (coeff s f) * c ^ s

variable {v c f s} {t : ℕ}

/-- A distinguished series is nonzero. -/
lemma IsDistinguished.ne_zero [Nontrivial R] (hf : IsDistinguished v c f s) : f ≠ 0 :=
  fun h0 ↦ hf.isUnit_coeff.ne_zero (by rw [h0, map_zero])

/-- A distinguished series achieves its Gauss norm at the distinguished degree. -/
lemma IsDistinguished.achievesGaussNorm (hf : IsDistinguished v c f s) :
    AchievesGaussNorm v c f s :=
  hf.gaussNorm_eq.symm

/-- The distinguished degree is the largest index achieving the Gauss norm. -/
lemma IsDistinguished.le_of_achievesGaussNorm (hf : IsDistinguished v c f s)
    (h : AchievesGaussNorm v c f t) : t ≤ s :=
  not_lt.mp fun ht ↦ (hf.gaussTerm_lt t ht).ne (h.trans hf.gaussNorm_eq)

end Def

/-- A power series distinguished with respect to the norm forces the coefficient ring to be
nontrivial. -/
lemma IsDistinguished.nontrivial {S : Type*} [SeminormedRing S] {c : ℝ} {f : PowerSeries S} {s : ℕ}
    (hf : IsDistinguished norm c f s) : Nontrivial S :=
  not_subsingleton_iff_nontrivial.mp fun _ ↦ by
    simpa [Subsingleton.elim (coeff (s + 1) f) 0, Subsingleton.elim (coeff s f) 0] using
      hf.gaussTerm_lt (s + 1) (lt_add_one s)

namespace Restricted

section Norm

variable {S : Type*} [NormedRing S] [IsUltrametricDist S] {c : ℝ} [Fact (0 < c)] {s : ℕ}

/-- The `s`-th weighted coefficient norm of a distinguished restricted power series is its
norm. -/
lemma _root_.PowerSeries.IsDistinguished.norm_coeff_mul_pow_eq {l : Restricted S c}
    (hl : IsDistinguished norm c l.1 s) : ‖coeff s l.1‖ * c ^ s = ‖l‖ :=
  hl.gaussNorm_eq.symm.trans (norm_def c l).symm

/-- A distinguished restricted power series has positive norm. -/
lemma _root_.PowerSeries.IsDistinguished.norm_pos {l : Restricted S c}
    (hl : IsDistinguished norm c l.1 s) : 0 < ‖l‖ :=
  have : Nontrivial S := hl.nontrivial
  norm_pos_iff.mpr fun h ↦ hl.ne_zero (congrArg Subtype.val h)

end Norm

section CMul

variable {S : Type*} [NormedRing S] [IsUltrametricDist S] [NormMulClass S] {c : ℝ}
  [Fact (0 < c)] {s : ℕ}

/-- Multiplying a distinguished restricted power series by a unit constant preserves
distinguishedness. -/
lemma _root_.PowerSeries.IsDistinguished.C_mul {l : Restricted S c}
    (hl : IsDistinguished norm c l.1 s) {a : S} (ha : IsUnit a) :
    IsDistinguished norm c (C c a * l).1 s := by
  have : Nontrivial S := hl.nontrivial
  have hco : ∀ k, coeff k (C c a * l).1 = a * coeff k l.1 := fun k ↦ coeff_C_mul k l.1 a
  refine ⟨hco s ▸ ha.mul hl.isUnit_coeff, ?_, fun t ht ↦ ?_⟩
  · rw [← norm_def, norm_mul, norm_C, ← hl.norm_coeff_mul_pow_eq, hco, norm_mul, mul_assoc]
  · rw [hco, hco, norm_mul, norm_mul, mul_assoc, mul_assoc]
    exact mul_lt_mul_of_pos_left (hl.gaussTerm_lt t ht) (norm_pos_iff.mpr ha.ne_zero)

end CMul

section OfMonic

variable {S : Type*} [NormedRing S] [IsUltrametricDist S] [NormOneClass S] {c : ℝ}
  [Fact (0 < c)] {s : ℕ}

/-- A monic polynomial of degree `s` whose restricted power series has norm `c ^ s` — its top
Gauss term — is distinguished of degree `s` at radius `c`. -/
lemma isDistinguished_toRestricted_of_monic {ω : Polynomial S} (ωm : ω.Monic) (ωd : ω.degree = s)
    (ωn : ‖Polynomial.toRestricted c ω‖ = c ^ s) :
    IsDistinguished norm c (Polynomial.toRestricted c ω).1 s := by
  have hcoeff : ∀ k, coeff k (Polynomial.toRestricted c ω).1 = ω.coeff k :=
    Polynomial.coeff_coe ω
  have h1 : coeff s (Polynomial.toRestricted c ω).1 = 1 := by
    rw [hcoeff, ← Polynomial.natDegree_eq_of_degree_eq_some ωd]
    exact ωm.coeff_natDegree
  refine ⟨h1 ▸ isUnit_one, ?_, fun t ht ↦ ?_⟩
  · rw [← norm_def, ωn, h1, norm_one, one_mul]
  · rw [hcoeff, Polynomial.coeff_eq_zero_of_degree_lt (ωd ▸ Nat.cast_lt.mpr ht), norm_zero,
      zero_mul, h1, norm_one, one_mul]
    exact pow_pos Fact.out s

end OfMonic

end Restricted

end PowerSeries
