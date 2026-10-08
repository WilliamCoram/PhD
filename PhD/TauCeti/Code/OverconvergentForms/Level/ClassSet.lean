/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.TauCeti.Code.OverconvergentForms.Adelic.IntegralAdeles
import PhD.TauCeti.Code.OverconvergentForms.Quaternion.Definite
import Mathlib.Data.Pi.Interval
import Mathlib.GroupTheory.Commensurable
import Mathlib.GroupTheory.DoubleCoset

/-!
# The class set `D^× \ D_f^× / U`, sections and stabilisers

The class set of a subgroup `U ⊆ D_f^×`, the finiteness of class sets as a property of the pair
`(F, D)` (`HasFiniteClassSets`, the conclusion of Fujisaki's lemma), its transfer between levels,
sections and complete families of representatives, and the stabilisers
`Γ_c = c⁻¹ D^× c ∩ U`. Two compact open subgroups are commensurable. For `F = ℚ` and `D` definite
the global units are discrete in `D_f^×` and every stabiliser is finite.

[Buz07, §9, p. 68]: "Say `D_f^× = ∐_{λ=1}^μ D^× τ_λ U`. Then the groups
`Γ_λ := τ_λ⁻¹ D^× τ_λ ∩ U` are finitely-generated and moreover `τ_λ Γ_λ τ_λ⁻¹ ⊂ D^×` is
commensurable with `𝒪_D^×`." [Loe11, Proposition 3.1.1]: "For any compact open subgroup
`K ⊆ G(𝔸_f)`, the double quotient `G(F) \ G(𝔸_f) / K` is finite." [Loe11, Proposition 3.1.2]:
"If `G_∞` is compact, then `G(F)` is discrete in `G(𝔸_f)`."

## Main definitions

* `AdelicAlgebra.classSet`, `AdelicAlgebra.HasFiniteClassSets`.
* `AdelicAlgebra.IsCompleteFamily`, `AdelicAlgebra.IsSection`.
* `AdelicAlgebra.stabilizer`: `Γ_c = c⁻¹ D^× c ∩ U`; `AdelicAlgebra.globalStabilizer`:
  `D^× ∩ c U c⁻¹`; `AdelicAlgebra.stabilizerEquiv`: the two are isomorphic by conjugation.

## Main results

* `Subgroup.relIndex_ne_zero_of_isCompact_of_isOpen`,
  `Subgroup.commensurable_of_isCompact_of_isOpen`.
* `AdelicAlgebra.classSet_mk_eq_iff`, `AdelicAlgebra.finite_classSet_of_le`,
  `AdelicAlgebra.finite_classSet_of_relIndex_ne_zero`.
* `AdelicAlgebra.hasFiniteClassSets_of_finite`: finiteness at one compact open level gives it at
  every open level.
* `AdelicAlgebra.isSection_iff`, `AdelicAlgebra.exists_isSection`.
* `AdelicAlgebra.unitsIncl_algebraMap_mem_stabilizer`, `AdelicAlgebra.stabilizer_mul`.
* `AdelicAlgebra.finite_units_orderOf`: a definite order has finitely many units.
* `AdelicAlgebra.discreteTopology_globalUnits`, `AdelicAlgebra.finite_stabilizer`, for `F = ℚ`
  and `D` definite.

Roadmap: §0.2.1 (discreteness), §0.3.1 (commensurability), §0.3.2, §0.3.3. Tau Ceti home:
`TauCeti/NumberTheory/AdelicAlgebra/ClassSet.lean`.
-/

open scoped TensorProduct Classical Quaternion
open IsDedekindDomain NumberField

noncomputable section

section Commensurable

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- An open subgroup of a compact subgroup has finite index. -/
theorem Subgroup.relIndex_ne_zero_of_isCompact_of_isOpen {U V : Subgroup G}
    (hU : IsCompact (U : Set G)) (hV : IsOpen (V : Set G)) : V.relIndex U ≠ 0 := by
  haveI : CompactSpace U := isCompact_iff_compactSpace.mp hU
  have hopen : IsOpen ((V.subgroupOf U : Subgroup U) : Set U) :=
    hV.preimage continuous_subtype_val
  exact Subgroup.index_ne_zero_iff_finite.mpr (Subgroup.quotient_finite_of_isOpen _ hopen)

/-- **Two compact open subgroups are commensurable.** -/
theorem Subgroup.commensurable_of_isCompact_of_isOpen {U V : Subgroup G}
    (hUc : IsCompact (U : Set G)) (hUo : IsOpen (U : Set G)) (hVc : IsCompact (V : Set G))
    (hVo : IsOpen (V : Set G)) : Subgroup.Commensurable U V :=
  ⟨Subgroup.relIndex_ne_zero_of_isCompact_of_isOpen hVc hUo,
    Subgroup.relIndex_ne_zero_of_isCompact_of_isOpen hUc hVo⟩

end Commensurable

namespace AdelicAlgebra

open scoped RightAlgebra

variable (F : Type*) [Field F] [NumberField F] (D : Type*) [Ring D] [Algebra F D]

/-- **The class set** `D^× \ D_f^× / U`. -/
abbrev classSet (U : Subgroup (Dfx F D)) : Type _ :=
  DoubleCoset.Quotient ((globalUnits F D : Subgroup (Dfx F D)) : Set (Dfx F D)) (U : Set (Dfx F D))

/-- **Finiteness of class sets**, the conclusion of Fujisaki's lemma for `(F, D)`: for every open
subgroup `U ⊆ D_f^×` the double coset space `D^× \ D_f^× / U` is finite. It holds for every
finite-dimensional division algebra over a number field; it is a hypothesis here, discharged in this
development for Hamilton's quaternions. -/
class HasFiniteClassSets : Prop where
  finite_classSet : ∀ U : Subgroup (Dfx F D), IsOpen (U : Set (Dfx F D)) → Finite (classSet F D U)

variable {F D}

/-- Every open level has a finite class set. -/
theorem finite_classSet [HasFiniteClassSets F D] {U : Subgroup (Dfx F D)}
    (hU : IsOpen (U : Set (Dfx F D))) : Finite (classSet F D U) :=
  HasFiniteClassSets.finite_classSet U hU

/-- Two elements have the same class exactly when they differ by `D^×` on the left and `U` on the
right. -/
theorem classSet_mk_eq_iff {U : Subgroup (Dfx F D)} {g g' : Dfx F D} :
    (DoubleCoset.mk _ _ g : classSet F D U) = DoubleCoset.mk _ _ g' ↔
      ∃ d ∈ globalUnits F D, ∃ u ∈ U, g' = d * g * u :=
  DoubleCoset.eq _ _ g g'

/-- A larger level has a smaller class set. -/
theorem finite_classSet_of_le {U U' : Subgroup (Dfx F D)} (hle : U ≤ U')
    [Finite (classSet F D U)] : Finite (classSet F D U') := by
  let f : classSet F D U → classSet F D U' := Quotient.map' id fun x y hxy => by
    obtain ⟨d, hd, u, hu, rfl⟩ := DoubleCoset.rel_iff.mp hxy
    exact DoubleCoset.rel_iff.mpr ⟨d, hd, u, hle hu, rfl⟩
  refine Finite.of_surjective f fun q => ?_
  obtain ⟨g, rfl⟩ := Quotient.exists_rep q
  exact ⟨DoubleCoset.mk _ _ g, rfl⟩

/-- A subgroup of finite index has a finite class set: `D^× \ D_f^× / U` is covered by
`D^× \ D_f^× / U' × U' ⧸ (U ∩ U')`. -/
theorem finite_classSet_of_relIndex_ne_zero {U U' : Subgroup (Dfx F D)}
    (hfi : U.relIndex U' ≠ 0) [Finite (classSet F D U')] : Finite (classSet F D U) := by
  haveI : Finite (U' ⧸ U.subgroupOf U') := Subgroup.index_ne_zero_iff_finite.mp hfi
  refine Finite.of_surjective (fun p : classSet F D U' × (U' ⧸ U.subgroupOf U') =>
    (DoubleCoset.mk _ _ (p.1.out * ((p.2.out : U') : Dfx F D)) : classSet F D U)) fun q => ?_
  obtain ⟨x, rfl⟩ := Quotient.exists_rep q
  obtain ⟨d, hd, u', hu', hout⟩ := (DoubleCoset.eq _ _ x
    (DoubleCoset.mk (globalUnits F D) U' x).out).mp (DoubleCoset.out_eq' _ _ _).symm
  set c : U' ⧸ U.subgroupOf U' := QuotientGroup.mk ⟨u'⁻¹, U'.inv_mem hu'⟩ with hc
  have hw : ((c.out : U') : Dfx F D)⁻¹ * u'⁻¹ ∈ U := by
    have h := Subgroup.mem_subgroupOf.mp (QuotientGroup.eq.mp ((QuotientGroup.out_eq' c).trans hc))
    simpa using h
  refine ⟨(DoubleCoset.mk (globalUnits F D) U' x, c), ?_⟩
  refine (DoubleCoset.eq _ _ _ _).mpr ⟨d⁻¹, inv_mem hd, _, hw, ?_⟩
  rw [hout]
  group

/-- **Finiteness at one compact open level gives finiteness at every open level.** -/
theorem hasFiniteClassSets_of_finite [Module.Finite F D] {U₀ : Subgroup (Dfx F D)}
    (hc : IsCompact (U₀ : Set (Dfx F D))) (ho : IsOpen (U₀ : Set (Dfx F D)))
    [Finite (classSet F D U₀)] : HasFiniteClassSets F D := by
  refine ⟨fun U hU => ?_⟩
  have hfi : (U ⊓ U₀).relIndex U₀ ≠ 0 :=
    Subgroup.relIndex_ne_zero_of_isCompact_of_isOpen hc
      (by rw [Subgroup.coe_inf]; exact hU.inter ho)
  haveI := finite_classSet_of_relIndex_ne_zero hfi
  exact finite_classSet_of_le (U := U ⊓ U₀) inf_le_left

section Sections

variable {ι : Type*}

/-- **A complete family** of representatives: it meets every double coset. -/
def IsCompleteFamily (c : ι → Dfx F D) (U : Subgroup (Dfx F D)) : Prop :=
  ∀ g : Dfx F D, ∃ i, ∃ d ∈ globalUnits F D, ∃ u ∈ U, g = d * c i * u

/-- **A section** of the class set: a family of representatives bijective onto it. -/
def IsSection (c : ι → Dfx F D) (U : Subgroup (Dfx F D)) : Prop :=
  Function.Bijective fun i ↦ (DoubleCoset.mk _ _ (c i) : classSet F D U)

/-- A section is a complete family whose members lie in distinct classes. -/
theorem isSection_iff {c : ι → Dfx F D} {U : Subgroup (Dfx F D)} :
    IsSection c U ↔ IsCompleteFamily c U ∧
      ∀ i j, (∃ d ∈ globalUnits F D, ∃ u ∈ U, c j = d * c i * u) → i = j := by
  constructor
  · rintro ⟨hinj, hsurj⟩
    refine ⟨fun g => ?_, fun i j hij => hinj ((DoubleCoset.eq _ _ _ _).mpr hij)⟩
    obtain ⟨i, hi⟩ := hsurj (DoubleCoset.mk _ _ g)
    exact ⟨i, (DoubleCoset.eq _ _ _ _).mp hi⟩
  · rintro ⟨hcomp, hinj⟩
    refine ⟨fun i j hij => hinj i j ((DoubleCoset.eq _ _ _ _).mp hij), fun q => ?_⟩
    obtain ⟨g, rfl⟩ := Quotient.exists_rep q
    obtain ⟨i, hi⟩ := hcomp g
    exact ⟨i, (DoubleCoset.eq _ _ _ _).mpr hi⟩

/-- A section exists: choose a representative of every class. -/
theorem exists_isSection (U : Subgroup (Dfx F D)) :
    ∃ c : classSet F D U → Dfx F D, IsSection c U :=
  ⟨fun q => q.out, fun x y hxy =>
    (DoubleCoset.out_eq' _ _ x).symm.trans (hxy.trans (DoubleCoset.out_eq' _ _ y)),
    fun q => ⟨q, DoubleCoset.out_eq' _ _ q⟩⟩

end Sections

section Stabilizer

/-- **The stabiliser** `Γ_c = c⁻¹ D^× c ∩ U` of a representative `c`. -/
def stabilizer (c : Dfx F D) (U : Subgroup (Dfx F D)) : Subgroup (Dfx F D) where
  carrier := {u | u ∈ U ∧ c * u * c⁻¹ ∈ globalUnits F D}
  mul_mem' {x y} hx hy := ⟨mul_mem hx.1 hy.1, by
    have e : c * (x * y) * c⁻¹ = c * x * c⁻¹ * (c * y * c⁻¹) := by group
    rw [e]
    exact mul_mem hx.2 hy.2⟩
  one_mem' := ⟨one_mem _, by rw [mul_one, mul_inv_cancel]; exact one_mem _⟩
  inv_mem' {x} hx := ⟨inv_mem hx.1, by
    have e : c * x⁻¹ * c⁻¹ = (c * x * c⁻¹)⁻¹ := by group
    rw [e]
    exact inv_mem hx.2⟩

/-- `u ∈ Γ_c` exactly when `u ∈ U` and `c u c⁻¹ ∈ D^×`. -/
theorem mem_stabilizer_iff {c u : Dfx F D} {U : Subgroup (Dfx F D)} :
    u ∈ stabilizer c U ↔ u ∈ U ∧ c * u * c⁻¹ ∈ globalUnits F D :=
  Iff.rfl

/-- `Γ_c ⊆ U`. -/
theorem stabilizer_le (c : Dfx F D) (U : Subgroup (Dfx F D)) : stabilizer c U ≤ U :=
  fun _ h => h.1

/-- **The global stabiliser** `D^× ∩ c U c⁻¹`, a subgroup of `D^×`. -/
def globalStabilizer (c : Dfx F D) (U : Subgroup (Dfx F D)) : Subgroup Dˣ :=
  U.comap ((MulAut.conj c⁻¹).toMonoidHom.comp (unitsIncl F D))

/-- `x ∈ D^× ∩ c U c⁻¹` exactly when `c⁻¹ x c ∈ U`. -/
theorem mem_globalStabilizer_iff {c : Dfx F D} {U : Subgroup (Dfx F D)} {x : Dˣ} :
    x ∈ globalStabilizer c U ↔ c⁻¹ * unitsIncl F D x * c ∈ U := by
  rw [globalStabilizer, Subgroup.mem_comap, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply, inv_inv]

/-- **`Γ_c ≃ D^× ∩ c U c⁻¹`**, by conjugation. -/
def stabilizerEquiv (c : Dfx F D) (U : Subgroup (Dfx F D)) :
    stabilizer c U ≃* globalStabilizer c U :=
  (MulEquiv.ofBijective
    ({ toFun x := ⟨c⁻¹ * unitsIncl F D x * c, mem_globalStabilizer_iff.mp x.2, by
          rw [show c * (c⁻¹ * unitsIncl F D x * c) * c⁻¹ = unitsIncl F D x by group]
          exact ⟨x, rfl⟩⟩
       map_one' := Subtype.ext (by simp)
       map_mul' x y := Subtype.ext (by
          change c⁻¹ * unitsIncl F D (x * y) * c =
            c⁻¹ * unitsIncl F D x * c * (c⁻¹ * unitsIncl F D y * c)
          rw [map_mul]
          group) } :
      globalStabilizer c U →* stabilizer c U)
    ⟨fun x y hxy => Subtype.ext (unitsIncl_injective F D (by
        have h := congrArg (fun z : stabilizer c U => c * (z : Dfx F D) * c⁻¹) hxy
        simpa [mul_assoc] using h)),
      fun u => by
        obtain ⟨x, hx⟩ := u.2.2
        refine ⟨⟨x, mem_globalStabilizer_iff.mpr ?_⟩, Subtype.ext ?_⟩
        · rw [hx, show c⁻¹ * (c * (u : Dfx F D) * c⁻¹) * c = u by group]
          exact u.2.1
        · change c⁻¹ * unitsIncl F D x * c = u
          rw [hx]
          group⟩).symm

/-- The global scalars of `U` lie in every stabiliser. -/
theorem unitsIncl_algebraMap_mem_stabilizer (c : Dfx F D) {U : Subgroup (Dfx F D)} {z : Fˣ}
    (hz : unitsIncl F D (Units.map (algebraMap F D).toMonoidHom z) ∈ U) :
    unitsIncl F D (Units.map (algebraMap F D).toMonoidHom z) ∈ stabilizer c U := by
  refine ⟨hz, ?_⟩
  rw [(unitsIncl_algebraMap_commute z c).symm.eq, mul_inv_cancel_right]
  exact ⟨_, rfl⟩

/-- The stabilisers of two representatives of one class are conjugate. -/
theorem stabilizer_mul (c : Dfx F D) (U : Subgroup (Dfx F D)) {d u : Dfx F D}
    (hd : d ∈ globalUnits F D) (hu : u ∈ U) :
    stabilizer (d * c * u) U = (stabilizer c U).map (MulAut.conj u⁻¹).toMonoidHom := by
  ext v
  constructor
  · rintro ⟨hvU, hv⟩
    refine ⟨u * v * u⁻¹, ⟨mul_mem (mul_mem hu hvU) (inv_mem hu), ?_⟩, ?_⟩
    · have e : c * (u * v * u⁻¹) * c⁻¹ = d⁻¹ * (d * c * u * v * (d * c * u)⁻¹) * d := by group
      rw [e]
      exact mul_mem (mul_mem (inv_mem hd) hv) hd
    · rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
  · rintro ⟨w, ⟨hwU, hw⟩, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    refine ⟨mul_mem (mul_mem (inv_mem hu) hwU) hu, ?_⟩
    have e : d * c * u * (u⁻¹ * w * u) * (d * c * u)⁻¹ = d * (c * w * c⁻¹) * d⁻¹ := by group
    rw [e]
    exact mul_mem (mul_mem hd hw) (inv_mem hd)

end Stabilizer

section Definite

open QuaternionAlgebra

variable {a b : ℚ} {ι : Type*} [Fintype ι]

private theorem abs_le_one_add_div_of_mul_sq_le {c y : ℚ} (hc : 0 < c) (h : c * y ^ 2 ≤ 1) :
    |y| ≤ 1 + 1 / c := by
  have hy2 : y ^ 2 ≤ 1 / c := by
    rw [le_div_iff₀ hc]
    linarith
  have habs : |y| ≤ 1 + y ^ 2 := by
    rcases le_total |y| 1 with h1 | h1
    · linarith [sq_nonneg y]
    · have h2 : |y| * 1 ≤ |y| * |y| := mul_le_mul_of_nonneg_left h1 (abs_nonneg y)
      rw [mul_one, abs_mul_abs_self, ← sq] at h2
      linarith
  linarith

private theorem abs_lin_four_le {y₀ y₁ y₂ y₃ r₀ r₁ r₂ r₃ R₀ R₁ R₂ R₃ : ℚ} (h₀ : |y₀| ≤ R₀)
    (h₁ : |y₁| ≤ R₁) (h₂ : |y₂| ≤ R₂) (h₃ : |y₃| ≤ R₃) :
    |y₀ * r₀ + y₁ * r₁ + y₂ * r₂ + y₃ * r₃| ≤
      R₀ * |r₀| + R₁ * |r₁| + R₂ * |r₂| + R₃ * |r₃| := by
  calc |y₀ * r₀ + y₁ * r₁ + y₂ * r₂ + y₃ * r₃|
      ≤ |y₀ * r₀ + y₁ * r₁ + y₂ * r₂| + |y₃ * r₃| := abs_add_le _ _
    _ ≤ |y₀ * r₀ + y₁ * r₁| + |y₂ * r₂| + |y₃ * r₃| := by gcongr; exact abs_add_le _ _
    _ ≤ |y₀ * r₀| + |y₁ * r₁| + |y₂ * r₂| + |y₃ * r₃| := by gcongr; exact abs_add_le _ _
    _ = |y₀| * |r₀| + |y₁| * |r₁| + |y₂| * |r₂| + |y₃| * |r₃| := by simp only [abs_mul]
    _ ≤ R₀ * |r₀| + R₁ * |r₁| + R₂ * |r₂| + R₃ * |r₃| := by gcongr

/-- **A definite order over `ℤ` has finitely many units.** -/
theorem finite_units_orderOf (h : IsTotallyDefinite a b) {β : Module.Basis ι ℚ ℍ[ℚ,a,b]}
    (hβ : IsOrderBasis β) : Finite (orderOf β hβ)ˣ := by
  have hab := h (Rat.castHom ℝ)
  have ha : a < 0 := by simpa using hab.1
  have hb : b < 0 := by simpa using hab.2
  have hint : ∀ c ∈ (algebraMap (𝓞 ℚ) ℚ).range, ∃ n : ℤ, c = n := by
    intro c hc
    obtain ⟨r, rfl⟩ := RingHom.mem_range.mp hc
    obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp
      (NumberField.RingOfIntegers.isIntegral_coe r)
    exact ⟨n, by rw [← hn, eq_intCast]⟩
  -- the order is finitely generated as an abelian group
  have hfg : (orderOf β hβ).toAddSubgroup.FG := by
    refine (AddSubgroup.fg_iff _).mpr ⟨Set.range β, le_antisymm ?_ ?_, Set.finite_range β⟩
    · rw [AddSubgroup.closure_le]
      rintro _ ⟨i, rfl⟩ j
      rw [β.repr_self, Finsupp.single_apply]
      split_ifs
      · exact one_mem _
      · exact zero_mem _
    · intro x hx
      rw [← β.sum_repr x]
      refine AddSubgroup.sum_mem _ fun i _ => ?_
      obtain ⟨n, hn⟩ := hint _ (hx i)
      rw [hn, Int.cast_smul_eq_zsmul]
      exact AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure (Set.mem_range_self (f := β) i)) n
  -- units of the order have reduced norm `1`
  have hnrd : ∀ u : (orderOf β hβ)ˣ, nrd ((u : orderOf β hβ) : ℍ[ℚ,a,b]) = 1 := by
    intro u
    have hmul1 : ((u : orderOf β hβ) : ℍ[ℚ,a,b]) *
        (((u⁻¹ : (orderOf β hβ)ˣ) : orderOf β hβ) : ℍ[ℚ,a,b]) = 1 :=
      congrArg Subtype.val u.mul_inv
    have hne : ((u : orderOf β hβ) : ℍ[ℚ,a,b]) ≠ 0 := fun h0 => by
      rw [h0, zero_mul] at hmul1
      exact zero_ne_one hmul1
    have hpos : (0 : ℚ) < nrd ((u : orderOf β hβ) : ℍ[ℚ,a,b]) :=
      Rat.cast_pos.mp (h.nrd_pos (Rat.castHom ℝ) hne)
    have hmul : nrd ((u : orderOf β hβ) : ℍ[ℚ,a,b]) *
        nrd (((u⁻¹ : (orderOf β hβ)ˣ) : orderOf β hβ) : ℍ[ℚ,a,b]) = 1 := by
      rw [← map_mul, hmul1, map_one]
    obtain ⟨n, hn⟩ := exists_int_nrd_of_fg hfg (u : orderOf β hβ).2
    obtain ⟨m, hm⟩ := exists_int_nrd_of_fg hfg ((u⁻¹ : (orderOf β hβ)ˣ) : orderOf β hβ).2
    rw [hn, hm] at hmul
    rw [hn] at hpos ⊢
    have hnm : n * m = 1 := by exact_mod_cast hmul
    have hn1 : n = 1 := Int.eq_one_of_mul_eq_one_right (by exact_mod_cast hpos.le) hnm
    rw [hn1, Int.cast_one]
  -- the coordinates of an element of reduced norm `1` are bounded
  have hcoord : ∀ x : ℍ[ℚ,a,b], nrd x = 1 → ∀ i,
      |β.repr x i| ≤ (1 + 1 / 1) * |β.repr 1 i| + (1 + 1 / (-a)) * |β.repr ⟨0, 1, 0, 0⟩ i| +
        (1 + 1 / (-b)) * |β.repr ⟨0, 0, 1, 0⟩ i| + (1 + 1 / (a * b)) * |β.repr ⟨0, 0, 0, 1⟩ i| := by
    intro x hx i
    have hx' : x.re ^ 2 + -a * x.imI ^ 2 + -b * x.imJ ^ 2 + a * b * x.imK ^ 2 = 1 := by
      rw [← hx, nrd_apply]
      ring
    have t₁ : 0 ≤ -a * x.imI ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
    have t₂ : 0 ≤ -b * x.imJ ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
    have t₃ : 0 ≤ a * b * x.imK ^ 2 := mul_nonneg (mul_pos_of_neg_of_neg ha hb).le (sq_nonneg _)
    have t₀ : 0 ≤ x.re ^ 2 := sq_nonneg _
    have hdecomp : x = x.re • (1 : ℍ[ℚ,a,b]) + x.imI • ⟨0, 1, 0, 0⟩ + x.imJ • ⟨0, 0, 1, 0⟩ +
        x.imK • ⟨0, 0, 0, 1⟩ := by
      ext <;> simp
    have hrepr : β.repr x i = x.re * β.repr 1 i + x.imI * β.repr ⟨0, 1, 0, 0⟩ i +
        x.imJ * β.repr ⟨0, 0, 1, 0⟩ i + x.imK * β.repr ⟨0, 0, 0, 1⟩ i := by
      conv_lhs => rw [hdecomp]
      simp only [map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
    rw [hrepr]
    exact abs_lin_four_le
      (abs_le_one_add_div_of_mul_sq_le one_pos (by linarith))
      (abs_le_one_add_div_of_mul_sq_le (by linarith) (by linarith))
      (abs_le_one_add_div_of_mul_sq_le (by linarith) (by linarith))
      (abs_le_one_add_div_of_mul_sq_le (mul_pos_of_neg_of_neg ha hb) (by linarith))
  -- a finite set of candidates
  set B : ι → ℚ := fun i => (1 + 1 / 1) * |β.repr 1 i| +
    (1 + 1 / (-a)) * |β.repr ⟨0, 1, 0, 0⟩ i| + (1 + 1 / (-b)) * |β.repr ⟨0, 0, 1, 0⟩ i| +
    (1 + 1 / (a * b)) * |β.repr ⟨0, 0, 0, 1⟩ i| with hB
  have hT : {x : ℍ[ℚ,a,b] | x ∈ orderOf β hβ ∧ nrd x = 1}.Finite := by
    refine ((Set.finite_Icc (fun i => -⌈B i⌉) fun i => ⌈B i⌉).image
      fun n : ι → ℤ => ∑ i, (n i : ℚ) • β i).subset ?_
    rintro x ⟨hxO, hx1⟩
    choose n hn using fun i => hint _ (hxO i)
    have hbd : ∀ i, |(n i : ℚ)| ≤ ⌈B i⌉ := fun i =>
      (hn i ▸ hcoord x hx1 i).trans (Int.le_ceil _)
    refine ⟨n, ⟨fun i => ?_, fun i => ?_⟩, ?_⟩
    · have := neg_abs_le (n i : ℚ)
      exact_mod_cast (neg_le_neg (hbd i)).trans this
    · exact_mod_cast (le_abs_self (n i : ℚ)).trans (hbd i)
    · calc ∑ i, (n i : ℚ) • β i = ∑ i, β.repr x i • β i := by simp only [hn]
        _ = x := β.sum_repr x
  haveI : Finite {x : ℍ[ℚ,a,b] | x ∈ orderOf β hβ ∧ nrd x = 1} := hT.to_subtype
  exact Finite.of_injective (fun u : (orderOf β hβ)ˣ =>
      (⟨((u : orderOf β hβ) : ℍ[ℚ,a,b]), (u : orderOf β hβ).2, hnrd u⟩ :
        {x : ℍ[ℚ,a,b] | x ∈ orderOf β hβ ∧ nrd x = 1}))
    fun u v huv => Units.ext (Subtype.ext (congrArg Subtype.val huv :))

/-- **For `F = ℚ` and `D` definite, `D^×` is discrete in `D_f^×`**: it meets the open subgroup
`U₀(1)` in the finite group `𝒪_D^×`. -/
theorem discreteTopology_globalUnits (h : IsTotallyDefinite a b) {β : Module.Basis ι ℚ ℍ[ℚ,a,b]}
    (hβ : IsOrderBasis β) : DiscreteTopology (globalUnits ℚ ℍ[ℚ,a,b]) := by
  haveI : Module.Finite ℚ ℍ[ℚ,a,b] := Module.Finite.of_basis β
  haveI := finite_units_orderOf h hβ
  let W : Set (globalUnits ℚ ℍ[ℚ,a,b]) :=
    Subtype.val ⁻¹' (U0 β hβ : Set (Dfx ℚ ℍ[ℚ,a,b]))
  have hWo : IsOpen W := isOpen_U0.preimage continuous_subtype_val
  have hWf : W.Finite := by
    refine Set.Finite.of_finite_image ?_ Subtype.val_injective.injOn
    refine (Set.finite_range fun u : (orderOf β hβ)ˣ =>
      unitsIncl ℚ ℍ[ℚ,a,b] (Units.map (orderOf β hβ).subtype.toMonoidHom u)).subset ?_
    rintro _ ⟨⟨g, x, rfl⟩, hg, rfl⟩
    obtain ⟨h1, h2⟩ := unitsIncl_mem_U0_iff.mp hg
    exact ⟨⟨⟨x, h1⟩, ⟨(x⁻¹ : (ℍ[ℚ,a,b])ˣ), h2⟩, Subtype.ext x.mul_inv, Subtype.ext x.inv_mul⟩,
      congrArg (unitsIncl ℚ ℍ[ℚ,a,b]) (Units.ext rfl)⟩
  have h1W : (1 : globalUnits ℚ ℍ[ℚ,a,b]) ∈ W := (U0 β hβ).one_mem
  have hsingle : IsOpen ({1} : Set (globalUnits ℚ ℍ[ℚ,a,b])) := by
    rw [← Set.sdiff_sdiff_cancel_left (Set.singleton_subset_iff.mpr h1W)]
    exact hWo.sdiff (hWf.subset Set.sdiff_subset).isClosed
  exact discreteTopology_of_isOpen_singleton_one hsingle

/-- **For `F = ℚ` and `D` definite every stabiliser of a compact level is finite.** -/
theorem finite_stabilizer (h : IsTotallyDefinite a b) {β : Module.Basis ι ℚ ℍ[ℚ,a,b]}
    (hβ : IsOrderBasis β) (c : Dfx ℚ ℍ[ℚ,a,b]) {U : Subgroup (Dfx ℚ ℍ[ℚ,a,b])}
    (hU : IsCompact (U : Set (Dfx ℚ ℍ[ℚ,a,b]))) : Finite (stabilizer c U) := by
  haveI : Module.Finite ℚ ℍ[ℚ,a,b] := Module.Finite.of_basis β
  haveI := discreteTopology_globalUnits h hβ
  have hΓc : IsClosed (globalUnits ℚ ℍ[ℚ,a,b] : Set (Dfx ℚ ℍ[ℚ,a,b])) :=
    Subgroup.isClosed_of_discrete
  have hK : IsCompact ((fun u => c * u * c⁻¹) '' (U : Set (Dfx ℚ ℍ[ℚ,a,b]))) :=
    hU.image ((continuous_const.mul continuous_id).mul continuous_const)
  have hfin : ((globalUnits ℚ ℍ[ℚ,a,b] : Set (Dfx ℚ ℍ[ℚ,a,b])) ∩
      (fun u => c * u * c⁻¹) '' (U : Set (Dfx ℚ ℍ[ℚ,a,b]))).Finite := by
    have hcpt := hK.inter_left hΓc
    have hpre := hΓc.isClosedEmbedding_subtypeVal.isCompact_preimage hcpt
    exact (hpre.finite_of_discrete.image Subtype.val).subset
      fun y hy => ⟨⟨y, hy.1⟩, hy, rfl⟩
  refine Set.Finite.to_subtype ((hfin.image fun γ => c⁻¹ * γ * c).subset ?_)
  rintro u ⟨huU, hu⟩
  exact ⟨c * u * c⁻¹, ⟨hu, u, huU, rfl⟩, by group⟩

end Definite

end AdelicAlgebra
