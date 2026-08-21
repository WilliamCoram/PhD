/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.BirkovichWP.RingTheory.MvPowerSeries.Restricted.GaussNorm
import PhD.ForMathlib.RingTheory.PowerSeries.Restricted.GaussNorm

/-!
# The largest dominant pair for restricted univariate power series

For `σ = Unit` the lex order on `Unit →₀ ℕ` is the order on `ℕ`, so
`MvPowerSeries.IsRestricted.exists_achievesGaussNorm_dominant_lexMax` says that the dominant
pair of achieving indices consists of the *largest* achieving indices.  This is what the
Gauss-extension route to Weierstrass division uses: for a distinguished `g` of degree `s`, the
largest achieving index of `g` is `s`, so the dominant pair puts the peak of `g * q` at
`s + j` and the remainder cannot interfere with it (see
`PhD/BirkovichWP/RingTheory/PowerSeries/Restricted/WeierstrassDivision.lean`).

`PhD/ForMathlib/` carries only the order-free
`PowerSeries.IsRestricted.exists_achievesGaussNorm_dominant`, which is what the Martin route
needs.

## Main results

* `PowerSeries.IsRestricted.exists_achievesGaussNorm_dominant_max` and
  `PowerSeries.Restricted.exists_achievesGaussNorm_dominant_max`: the dominant pair consists of
  the largest achieving indices.
-/

namespace PowerSeries

variable {R : Type*} [NormedRing R]

namespace IsRestricted

variable {c : ℝ} {f g : PowerSeries R}

/-- On `Unit`-indexed finsupps the lex order compares the single values. -/
private lemma le_of_toLex_single_le {m n : ℕ}
    (h : toLex (Finsupp.single () m) ≤ toLex (Finsupp.single () n)) : m ≤ n := by
  by_contra hmn
  have hlt : Finsupp.single () n < Finsupp.single () m := by
    refine lt_of_le_of_ne (Finsupp.le_def.mpr fun u ↦ ?_) fun heq ↦
      hmn (Finsupp.single_injective () heq).ge
    simpa [Finsupp.single_apply] using (not_le.mp hmn).le
  exact absurd h (not_le.mpr (Finsupp.toLex_monotone.strictMono_of_injective toLex.injective hlt))

/-- Strengthening of `exists_achievesGaussNorm_dominant`: the dominant pair `(i, j)` consists
of the *largest* achieving indices, and the last two conjuncts expose this maximality. -/
lemma exists_achievesGaussNorm_dominant_max (hc : 0 ≤ c) (hf : IsRestricted c f)
    (hg : IsRestricted c g) (hf0 : gaussNorm norm c f ≠ 0) (hg0 : gaussNorm norm c g ≠ 0) :
    ∃ i j, AchievesGaussNorm norm c f i ∧ AchievesGaussNorm norm c g j ∧
      (∀ p ∈ Finset.antidiagonal (i + j), p ≠ (i, j) →
        ‖coeff p.1 f * coeff p.2 g‖ < ‖coeff i f‖ * ‖coeff j g‖) ∧
      (∀ t, AchievesGaussNorm norm c f t → t ≤ i) ∧
      ∀ t, AchievesGaussNorm norm c g t → t ≤ j := by
  obtain ⟨i, j, hi, hj, hdom, hi_max, hj_max⟩ :=
    MvPowerSeries.IsRestricted.exists_achievesGaussNorm_dominant_lexMax (fun _ ↦ hc) hf hg
      hf0 hg0
  obtain ⟨n, rfl⟩ : ∃ n, i = Finsupp.single () n := ⟨i (), Finsupp.unique_single i⟩
  obtain ⟨m, rfl⟩ : ∃ m, j = Finsupp.single () m := ⟨j (), Finsupp.unique_single j⟩
  refine ⟨n, m, (achievesGaussNorm_iff_single norm c f n).mpr hi,
    (achievesGaussNorm_iff_single norm c g m).mpr hj, fun p hp hpne ↦ ?_,
    fun t ht ↦ le_of_toLex_single_le
      (hi_max _ ((achievesGaussNorm_iff_single norm c f t).mp ht)),
    fun t ht ↦ le_of_toLex_single_le
      (hj_max _ ((achievesGaussNorm_iff_single norm c g t).mp ht))⟩
  exact hdom (Finsupp.single () p.1, Finsupp.single () p.2)
    (by rw [Finset.mem_antidiagonal, ← Finsupp.single_add, ← Finsupp.single_add,
      Finset.mem_antidiagonal.mp hp])
    fun h ↦ hpne (Prod.ext (Finsupp.single_injective () (congrArg Prod.fst h))
      (Finsupp.single_injective () (congrArg Prod.snd h)))

end IsRestricted

namespace Restricted

variable (c : ℝ) [IsUltrametricDist R]

/-- Strengthening of `exists_achievesGaussNorm_dominant`: the dominant pair `(i, j)` consists
of the *largest* achieving indices, and the last two conjuncts expose this maximality. -/
lemma exists_achievesGaussNorm_dominant_max (hc : 0 ≤ c) (f g : Restricted R c)
    (hf : gaussNorm R c f ≠ 0) (hg : gaussNorm R c g ≠ 0) :
    ∃ i j, AchievesGaussNorm norm c f.1 i ∧ AchievesGaussNorm norm c g.1 j ∧
      (∀ p ∈ Finset.antidiagonal (i + j), p ≠ (i, j) →
        ‖coeff p.1 f.1 * coeff p.2 g.1‖ < ‖coeff i f.1‖ * ‖coeff j g.1‖) ∧
      (∀ t, AchievesGaussNorm norm c f.1 t → t ≤ i) ∧
      ∀ t, AchievesGaussNorm norm c g.1 t → t ≤ j :=
  IsRestricted.exists_achievesGaussNorm_dominant_max hc f.2 g.2 hf hg

end Restricted

end PowerSeries
