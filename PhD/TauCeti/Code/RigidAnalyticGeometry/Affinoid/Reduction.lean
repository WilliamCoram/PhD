/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.TauCeti.Code.RigidAnalyticGeometry.Affinoid.PowerBounded

/-!
# The reduction `Ã = Å ⧸ Ǎ` of an affinoid algebra

Layer 2, §2.3.4 (BGR 6.2.3/4–5, 1.2.5/6–7). The reduction `Ã := Å ⧸ Ǎ` of an affinoid algebra is a
reduced `K̃`-algebra (`K̃ = ` the residue field of the unit ball of `K`); for the Tate algebra it is
the polynomial ring `K̃[X₁, …, Xₙ]` (Layer 0 `reductionEquiv`). The supremum seminorm is a valuation
exactly when `A` is reduced and `Ã` is a domain (BGR 6.2.3/5, both directions as separate
lemmas, through BGR 1.5.3/1).

## Main declarations

* `Affinoid.Reduction K A`: `powerBounded K A ⧸ topologicallyNilpotent K A`, with the reduction map
  `Affinoid.Reduction.mk` and its `K̃`-algebra structure
  `Affinoid.Reduction.instAlgebraResidueField` (through `Affinoid.powerBounded.ofUnitClosedBall`
  and `Affinoid.Reduction.ofResidueField`).
* `Affinoid.Reduction.isReduced`: BGR 1.2.5/7.
* `Affinoid.TateAlgebra.powerBounded_eq_unitClosedBall`, `Affinoid.TateAlgebra.reductionEquiv`:
  `Ã ≃+* K̃[X₁, …, Xₙ]` for `A = Tₙ` (BGR 6.2.3/4 + 5.1.2).
* `IsAffinoidAlgebra.supSeminorm_mul_of_isDomain_reduction`,
  `IsAffinoidAlgebra.isReduced_of_isValuation`,
  `IsAffinoidAlgebra.isDomain_reduction_of_isValuation`: BGR 6.2.3/5.
-/

open Affinoid IsLocalRing Subring NormedRing

namespace Affinoid

section Def

variable (K : Type*) [NormedField K] [IsUltrametricDist K] (A : Type*) [CommRing A] [Algebra K A]
  [HasSupSeminorm K A]

/-- The reduction `Ã := Å ⧸ Ǎ` (BGR 6.2.3/4, 1.2.5/6). -/
abbrev Reduction : Type _ := powerBounded K A ⧸ topologicallyNilpotent K A

/-- The reduction map `τ : Å → Ã`. -/
noncomputable abbrev Reduction.mk : powerBounded K A →+* Reduction K A :=
  Ideal.Quotient.mk (topologicallyNilpotent K A)

/-- The unit ball of `K` maps into `Å` (`|c · 1|_sup ≤ ‖c‖ ≤ 1`). -/
noncomputable def powerBounded.ofUnitClosedBall : unitClosedBall K →+* powerBounded K A where
  toFun c := ⟨algebraMap K A c, algebraMap_mem_powerBounded (Subring.norm_le_one c)⟩
  map_one' := Subtype.ext (map_one (algebraMap K A))
  map_mul' a b := Subtype.ext (map_mul (algebraMap K A) (a : K) b)
  map_zero' := Subtype.ext (map_zero (algebraMap K A))
  map_add' a b := Subtype.ext (map_add (algebraMap K A) (a : K) b)

/-- The maximal ideal of the unit ball of `K` maps into `Ǎ`, so `Ã` is a `K̃`-algebra
(BGR 6.2.3/4: "`Ã = Å/Ǎ` … is a `k̃`-algebra"). -/
theorem powerBounded.ofUnitClosedBall_mem_topologicallyNilpotent {c : unitClosedBall K}
    (hc : c ∈ openUnitBallIdeal K) :
    powerBounded.ofUnitClosedBall K A c ∈ topologicallyNilpotent K A := by
  rw [mem_topologicallyNilpotent]
  show supSeminorm K (algebraMap K A c) < 1
  rw [Algebra.algebraMap_eq_smul_one, supSeminorm_smul]
  exact (mul_le_of_le_one_right (norm_nonneg _) (supSeminorm_one_le K)).trans_lt
    (mem_openUnitBallIdeal.1 hc)

/-- The reduction map `K̃ → Ã`. -/
noncomputable def Reduction.ofResidueField : ResidueField (unitClosedBall K) →+* Reduction K A :=
  Ideal.Quotient.lift (maximalIdeal (unitClosedBall K))
    ((Reduction.mk K A).comp (powerBounded.ofUnitClosedBall K A)) fun c hc ↦ by
      rw [maximalIdeal_unitClosedBall] at hc
      exact Ideal.Quotient.eq_zero_iff_mem.2
        (powerBounded.ofUnitClosedBall_mem_topologicallyNilpotent K A hc)

noncomputable instance Reduction.instAlgebraResidueField :
    Algebra (ResidueField (unitClosedBall K)) (Reduction K A) :=
  (Reduction.ofResidueField K A).toAlgebra

/-- **BGR 1.2.5/7**: `Ã` is reduced (`Ǎ` is a radical ideal of `Å`). -/
instance Reduction.isReduced : IsReduced (Reduction K A) :=
  (Ideal.isRadical_iff_quotient_reduced _).1 topologicallyNilpotent_isRadical

end Def

section Tate

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] (n : ℕ)

/-- For the Tate algebra `Å` is the unit ball of the Gauss norm (`|·|_sup = ‖·‖`, Layer 0). -/
theorem TateAlgebra.powerBounded_eq_unitClosedBall :
    powerBounded K (TateAlgebra K n) = unitClosedBall (TateAlgebra K n) := by
  ext f
  rw [mem_powerBounded, Subring.mem_unitClosedBall, MvPowerSeries.Restricted.supSeminorm_eq_norm]

/-- **BGR 6.2.3/4 for `Tₙ`** (roadmap §2.3.4): `T̃ₙ ≅ K̃[X₁, …, Xₙ]`, from Layer 0's
`MvPowerSeries.Restricted.reductionEquiv`. -/
noncomputable def TateAlgebra.reductionEquiv :
    Reduction K (TateAlgebra K n) ≃+* MvPolynomial (Fin n) (ResidueField (unitClosedBall K)) := by
  -- `Å = T⁰ₙ` carries `Ǎ` onto `T⁰⁰ₙ`, then Layer 0's `T⁰ₙ ⧸ T⁰⁰ₙ ≃+* K̃[X]`
  refine (Ideal.quotientEquiv _ (openUnitBallIdeal (TateAlgebra K n))
    (RingEquiv.subringCongr (TateAlgebra.powerBounded_eq_unitClosedBall n)) ?_).trans
      MvPowerSeries.Restricted.reductionEquiv
  rw [Ideal.map_comap_of_equiv]
  ext x
  show ‖(x : TateAlgebra K n)‖ < 1 ↔ supSeminorm K (x : TateAlgebra K n) < 1
  rw [MvPowerSeries.Restricted.supSeminorm_eq_norm]

end Tate

end Affinoid

namespace IsAffinoidAlgebra

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : Type*} [CommRing A] [Algebra K A]

/-- **BGR 6.2.3/5, "if"**: when the reduction of an affinoid algebra is a domain, `|·|_sup` is
multiplicative (BGR 1.5.3/1, condition (i) from 6.2.1/4 (ii) and condition (ii) `Ã` a domain; with
`A` reduced, `|·|_sup` is moreover a norm by 6.2.1/4 (iii), so it is a valuation). -/
theorem supSeminorm_mul_of_isDomain_reduction (hA : IsAffinoidAlgebra K A)
    (hdom : haveI := hA.hasSupSeminorm; IsDomain (Reduction K A)) (f g : A) :
    supSeminorm K (f * g) = supSeminorm K f * supSeminorm K g := by
  haveI := hA.hasSupSeminorm
  refine le_antisymm (supSeminorm_mul_le K f g) (le_of_not_gt fun hlt ↦ ?_)
  have hf0 : supSeminorm K f ≠ 0 := fun h ↦ by
    rw [h, zero_mul] at hlt
    exact (supSeminorm_nonneg K _).not_gt hlt
  have hg0 : supSeminorm K g ≠ 0 := fun h ↦ by
    rw [h, mul_zero] at hlt
    exact (supSeminorm_nonneg K _).not_gt hlt
  -- `u = c fᵐ`, `v = d gᵐ` with `|u|_sup = |v|_sup = 1` (BGR 6.2.1/4 (ii), a uniform `m`)
  obtain ⟨m, hm, h⟩ := hA.exists_forall_exists_smul_pow_supSeminorm_eq_one
  obtain ⟨c, hc⟩ := h f hf0
  obtain ⟨d, hd⟩ := h g hg0
  have hc' : ‖c‖ * supSeminorm K f ^ m = 1 := by
    rw [← supSeminorm_pow K f hm, ← supSeminorm_smul]
    exact hc
  have hd' : ‖d‖ * supSeminorm K g ^ m = 1 := by
    rw [← supSeminorm_pow K g hm, ← supSeminorm_smul]
    exact hd
  have hcpos : 0 < ‖c‖ := (norm_nonneg c).lt_of_ne fun h0 ↦ by
    rw [← h0, zero_mul] at hc'
    exact zero_ne_one hc'
  have hdpos : 0 < ‖d‖ := (norm_nonneg d).lt_of_ne fun h0 ↦ by
    rw [← h0, zero_mul] at hd'
    exact zero_ne_one hd'
  -- `|u v|_sup = ‖c‖ ‖d‖ |f g|_supᵐ < ‖c‖ |f|_supᵐ ‖d‖ |g|_supᵐ = 1`
  have huv : supSeminorm K ((c • f ^ m) * (d • g ^ m)) < 1 := by
    rw [smul_mul_smul_comm, ← mul_pow, supSeminorm_smul, supSeminorm_pow K _ hm, norm_mul]
    calc ‖c‖ * ‖d‖ * supSeminorm K (f * g) ^ m
        < ‖c‖ * ‖d‖ * (supSeminorm K f * supSeminorm K g) ^ m :=
          mul_lt_mul_of_pos_left (pow_lt_pow_left₀ hlt (supSeminorm_nonneg K _) hm)
            (mul_pos hcpos hdpos)
      _ = (‖c‖ * supSeminorm K f ^ m) * (‖d‖ * supSeminorm K g ^ m) := by ring
      _ = 1 := by rw [hc', hd', one_mul]
  -- in the domain `Ã`, `τ(u) τ(v) = 0` with `τ(u), τ(v) ≠ 0`
  haveI := hdom
  let u : powerBounded K A := ⟨c • f ^ m, mem_powerBounded.2 hc.le⟩
  let v : powerBounded K A := ⟨d • g ^ m, mem_powerBounded.2 hd.le⟩
  have hmk : Reduction.mk K A u * Reduction.mk K A v = 0 := by
    rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
    exact huv
  rcases mul_eq_zero.1 hmk with h0 | h0
  · exact (mem_topologicallyNilpotent.1 (Ideal.Quotient.eq_zero_iff_mem.1 h0)).ne hc
  · exact (mem_topologicallyNilpotent.1 (Ideal.Quotient.eq_zero_iff_mem.1 h0)).ne hd

/-- **BGR 6.2.3/5, "only if" (reducedness)**: if `|·|_sup` is a valuation (multiplicative and a
norm) then `A` is reduced (BGR 1.5.1: a valued ring is a domain; here 3.8.1/9 suffices). -/
theorem isReduced_of_isValuation (hA : IsAffinoidAlgebra K A)
    (hnorm : ∀ f : A, supSeminorm K f = 0 → f = 0) : IsReduced A :=
  hA.isReduced_of_forall_supSeminorm_eq_zero_imp hnorm

/-- **BGR 6.2.3/5, "only if" (the domain)**: if `|·|_sup` is multiplicative (in particular if it
is a valuation) then `Ã` is a domain (BGR 1.5.1: "The ideal `Ǎ` is prime in `Å`; hence `Ã` is also
an integral domain"). -/
theorem isDomain_reduction_of_isValuation (hA : IsAffinoidAlgebra K A) [Nontrivial A]
    (hmul : ∀ f g : A, supSeminorm K (f * g) = supSeminorm K f * supSeminorm K g) :
    haveI := hA.hasSupSeminorm
    IsDomain (Reduction K A) := by
  haveI := hA.hasSupSeminorm
  rw [Ideal.Quotient.isDomain_iff_prime]
  refine ⟨fun htop ↦ ?_, fun {u v} huv ↦ ?_⟩
  · -- `1 ∉ Ǎ` since `|1|_sup = 1`
    have h1 : (1 : powerBounded K A) ∈ topologicallyNilpotent K A := htop ▸ Submodule.mem_top
    have h1' : supSeminorm K (1 : A) < 1 := h1
    rw [supSeminorm_one] at h1'
    exact lt_irrefl _ h1'
  · -- `|u| |v| = |u v| < 1` with `|u|, |v| ≤ 1`
    have h : supSeminorm K (u : A) * supSeminorm K (v : A) < 1 := by
      rw [← hmul]
      exact huv
    rcases (mem_powerBounded.1 u.2).lt_or_eq with hu | hu
    · exact Or.inl (mem_topologicallyNilpotent.2 hu)
    · rw [hu, one_mul] at h
      exact Or.inr (mem_topologicallyNilpotent.2 h)

end IsAffinoidAlgebra
