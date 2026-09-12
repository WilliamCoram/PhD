/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.Algebra.Group.Torsion
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Group.Basic
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Commensurability and the `ℚ`-valued logarithm of an ordered group

A linearly ordered abelian group all of whose elements are *commensurable* with a fixed
`a₀ < 0` admits a unique additive `M →+ ℚ` sending `a₀` to `-1`.  This is the group-theoretic
content of "rational rank one": it is the density analogue of "the value group is infinite
cyclic", and it is what makes a `ℚ`-valued additive valuation available on a densely valued
field once a normalising element has been chosen.

## Main definitions

* `AddCommGroup.IsCommensurableWith a₀ a`: some positive multiple of `a` is a multiple of `a₀`.
* `AddCommGroup.ratLog`: **the `ℚ`-valued logarithm normalised at `a₀`** — the unique additive
  hom `M →+ ℚ` sending `a₀` to `-1`.

## Main results

* `AddCommGroup.ratLog_eq`: any witness `n • a = m • a₀` with `0 < n` computes
  `ratLog a = -(m / n)`; in particular the value does not depend on the witness.
* `AddCommGroup.ratLog_strictMono`: it is strictly monotone, so it embeds `M` in `ℚ` as an
  ordered group.

This file is upstream of `PhD/Main/ForMathlib/RingTheory/Valuation/AddVal/Commensurable.lean`, which
applies it to the value group of a valuation.

Everything here is meant to be redistributed into the relevant `Mathlib` files.
-/

namespace AddCommGroup

section Commensurable

variable {M : Type*} [AddCommGroup M] [LinearOrder M] [IsOrderedAddMonoid M] {a₀ a : M}

/-- `a` is **commensurable** with `a₀` if some positive multiple of `a` is a multiple of `a₀`. -/
def IsCommensurableWith (a₀ a : M) : Prop := ∃ m n : ℤ, 0 < n ∧ n • a = m • a₀

/-- The rational `m / n` read off from *some* witness of commensurability.  It does not depend on
the witness: see `ratCoeff_eq`. -/
private noncomputable def ratCoeff (h : ∀ a : M, IsCommensurableWith a₀ a) (a : M) : ℚ :=
  (((h a).choose : ℤ) : ℚ) / (((h a).choose_spec.choose : ℤ) : ℚ)

private lemma ratCoeff_eq (h : ∀ a : M, IsCommensurableWith a₀ a) (ha₀ : a₀ ≠ 0)
    {m n : ℤ} (hn : 0 < n) (hmn : n • a = m • a₀) : ratCoeff h a = (m : ℚ) / (n : ℚ) := by
  obtain ⟨hn', hmn'⟩ := (h a).choose_spec.choose_spec
  set m' := (h a).choose with hm'def
  set n' := (h a).choose_spec.choose with hn'def
  have key : (n' * m - n * m') • a₀ = 0 := by
    rw [sub_smul, sub_eq_zero]
    calc (n' * m) • a₀ = n' • (m • a₀) := mul_smul _ _ _
      _ = n' • (n • a) := by rw [hmn]
      _ = (n' * n) • a := (mul_smul _ _ _).symm
      _ = (n * n') • a := by rw [mul_comm]
      _ = n • (n' • a) := mul_smul _ _ _
      _ = n • (m' • a₀) := by rw [hmn']
      _ = (n * m') • a₀ := (mul_smul _ _ _).symm
  have key' : m * n' = m' * n := by
    have := sub_eq_zero.mp ((IsAddTorsionFree.zsmul_eq_zero_iff_left ha₀).mp key)
    rw [mul_comm m n', this, mul_comm n m']
  simp only [ratCoeff, ← hm'def, ← hn'def]
  rw [div_eq_div_iff (by exact_mod_cast hn'.ne') (by exact_mod_cast hn.ne')]
  exact_mod_cast key'.symm

/-- **The `ℚ`-valued logarithm normalised at `a₀`.**  If `a₀ < 0` and every element of `M` is
commensurable with `a₀`, this is the unique additive hom `M →+ ℚ` sending `a₀` to `-1`.  Its
existence is exactly the statement that `M` has rational rank one. -/
noncomputable def ratLog (ha₀ : a₀ < 0) (h : ∀ a : M, IsCommensurableWith a₀ a) : M →+ ℚ where
  toFun a := -ratCoeff h a
  map_zero' := by
    rw [ratCoeff_eq h ha₀.ne (m := 0) (n := 1) one_pos (by simp), Int.cast_zero, zero_div, neg_zero]
  map_add' a b := by
    obtain ⟨m₁, n₁, hn₁, e₁⟩ := h a
    obtain ⟨m₂, n₂, hn₂, e₂⟩ := h b
    have e : (n₁ * n₂) • (a + b) = (n₂ * m₁ + n₁ * m₂) • a₀ := by
      rw [smul_add, add_smul]
      congr 1
      · rw [mul_comm n₁ n₂, mul_smul, e₁, ← mul_smul]
      · rw [mul_smul, e₂, ← mul_smul]
    rw [ratCoeff_eq h ha₀.ne (mul_pos hn₁ hn₂) e, ratCoeff_eq h ha₀.ne hn₁ e₁,
      ratCoeff_eq h ha₀.ne hn₂ e₂]
    have h₁ : (n₁ : ℚ) ≠ 0 := by exact_mod_cast hn₁.ne'
    have h₂ : (n₂ : ℚ) ≠ 0 := by exact_mod_cast hn₂.ne'
    push_cast
    field_simp
    ring

lemma ratLog_eq (ha₀ : a₀ < 0) (h : ∀ a : M, IsCommensurableWith a₀ a) {m n : ℤ}
    (hn : 0 < n) (hmn : n • a = m • a₀) : ratLog ha₀ h a = -((m : ℚ) / (n : ℚ)) :=
  congrArg Neg.neg (ratCoeff_eq h ha₀.ne hn hmn)

@[simp] lemma ratLog_self (ha₀ : a₀ < 0) (h : ∀ a : M, IsCommensurableWith a₀ a) :
    ratLog ha₀ h a₀ = -1 := by
  rw [ratLog_eq ha₀ h (m := 1) (n := 1) one_pos (by simp)]
  norm_num

lemma ratLog_strictMono (ha₀ : a₀ < 0) (h : ∀ a : M, IsCommensurableWith a₀ a) :
    StrictMono (ratLog ha₀ h) := by
  have key : ∀ a : M, 0 < a → 0 < ratLog ha₀ h a := by
    intro a ha
    obtain ⟨m, n, hn, hmn⟩ := h a
    rw [ratLog_eq ha₀ h hn hmn, neg_pos]
    have hna : (0 : M) < m • a₀ := by
      rw [← hmn]
      simpa using (zsmul_lt_zsmul_iff_left ha (m := 0) (n := n)).mpr hn
    have hm : m < 0 := by
      rcases lt_trichotomy m 0 with h' | rfl | h'
      · exact h'
      · simp at hna
      · exact absurd hna (not_lt.mpr (le_of_lt (neg_pos.mp (by
          rw [← smul_neg]
          simpa using (zsmul_lt_zsmul_iff_left (neg_pos.mpr ha₀) (m := 0) (n := m)).mpr h'))))
    exact div_neg_of_neg_of_pos (by exact_mod_cast hm) (by exact_mod_cast hn)
  intro a b hab
  have h1 := key (b - a) (sub_pos.mpr hab)
  rw [map_sub] at h1
  linarith

end Commensurable

end AddCommGroup
