/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.TauCeti.Code.RigidAnalyticGeometry.Affinoid.FunctionAlgebra
import PhD.TauCeti.Code.RigidAnalyticGeometry.Affinoid.Reduction

/-!
# The reduction functor on homomorphisms

Layer 2, §2.5 (BGR 6.3 introduction and 6.3.1/1–6). A homomorphism `φ : B → A` of affinoid algebras
maps `B̊` into `Å` and `B̌` into `Ǎ` (it is a contraction for `|·|_sup`), hence induces `φ̊ : B̊ →
Å` and `φ̃ : B̃ → Ã`, functorially. `φ̃` is injective iff `φ` is an isometry for `|·|_sup`
(6.3.1/1–2), in which case `ker φ ⊆ rad B` (6.3.1/3); for `φ` strict the converse holds (6.3.1/4–5);
and for `B` reduced, "`φ` injective and strict", "`φ` an isometry" and "`φ̃` injective" are
equivalent (6.3.1/6, with 6.2.4/1 for (ii) ⇒ (i), hence `[CharZero K]` there: plan D2).

## Main declarations

* `Affinoid.powerBoundedMap`, `Affinoid.reductionMap`, `Affinoid.reductionMap_mk`,
  `Affinoid.reductionMap_id`, `Affinoid.reductionMap_comp`, `Affinoid.reductionAlgHom`: the
  functor, `K̃`-linear on reductions.
* `Affinoid.IsStrictMap`: BGR 1.1.9 (the image of an open set is open in the image).
* `IsAffinoidAlgebra.isometry_iff_forall_supSeminorm_eq_one_imp`: BGR 6.3.1/1.
* `IsAffinoidAlgebra.injective_reductionMap_iff_isometry`: BGR 6.3.1/2.
* `IsAffinoidAlgebra.ker_le_nilradical_of_injective_reductionMap`: BGR 6.3.1/3.
* `IsAffinoidAlgebra.comap_ker_reductionMap_eq_radical_of_isStrictMap`,
  `IsAffinoidAlgebra.ker_reductionMap_eq_radical_map_of_isStrictMap`: BGR 6.3.1/4.
* `IsAffinoidAlgebra.injective_reductionMap_of_isStrictMap_of_ker_le_nilradical`: BGR 6.3.1/5.
* `IsAffinoidAlgebra.injective_reductionMap_of_injective_of_isStrictMap`,
  `IsAffinoidAlgebra.injective_of_isometry`, `IsAffinoidAlgebra.isStrictMap_of_isometry`:
  BGR 6.3.1/6 (M5).
-/

open Affinoid Filter
open scoped Topology

namespace Affinoid

section Functor

variable {K : Type*} [NormedField K] [IsUltrametricDist K] {A B C : Type*} [CommRing A]
  [Algebra K A] [CommRing B] [Algebra K B] [CommRing C] [Algebra K C] [HasSupSeminorm K A]
  [HasSupSeminorm K B] [HasSupSeminorm K C]

/-- `φ̊ : B̊ → Å` (BGR 6.3: "each such `φ` maps power-bounded elements into power-bounded
elements", by the contraction 3.8.1/4). -/
noncomputable def powerBoundedMap (φ : B →ₐ[K] A) : powerBounded K B →+* powerBounded K A where
  toFun b := ⟨φ b, mem_powerBounded.2 ((supSeminorm_map_le φ b).trans (mem_powerBounded.1 b.2))⟩
  map_one' := Subtype.ext (map_one φ)
  map_mul' a b := Subtype.ext (map_mul φ (a : B) b)
  map_zero' := Subtype.ext (map_zero φ)
  map_add' a b := Subtype.ext (map_add φ (a : B) b)

@[simp]
theorem coe_powerBoundedMap (φ : B →ₐ[K] A) (b : powerBounded K B) :
    (powerBoundedMap φ b : A) = φ b := rfl

/-- `φ̊` maps `B̌` into `Ǎ`. -/
theorem powerBoundedMap_mem_topologicallyNilpotent (φ : B →ₐ[K] A) {b : powerBounded K B}
    (hb : b ∈ topologicallyNilpotent K B) : powerBoundedMap φ b ∈ topologicallyNilpotent K A :=
  mem_topologicallyNilpotent.2 ((supSeminorm_map_le φ b).trans_lt (mem_topologicallyNilpotent.1 hb))

/-- `φ̃ : B̃ → Ã` (BGR 6.3, the commutative diagram). -/
noncomputable def reductionMap (φ : B →ₐ[K] A) : Reduction K B →+* Reduction K A :=
  Ideal.Quotient.lift _ ((Reduction.mk K A).comp (powerBoundedMap φ)) fun _ hb ↦
    Ideal.Quotient.eq_zero_iff_mem.2 (powerBoundedMap_mem_topologicallyNilpotent φ hb)

@[simp]
theorem reductionMap_mk (φ : B →ₐ[K] A) (b : powerBounded K B) :
    reductionMap φ (Reduction.mk K B b) = Reduction.mk K A (powerBoundedMap φ b) :=
  Ideal.Quotient.lift_mk _ _ _

theorem reductionMap_id : reductionMap (AlgHom.id K A) = RingHom.id (Reduction K A) :=
  Ideal.Quotient.ringHom_ext (RingHom.ext fun _ ↦ rfl)

theorem reductionMap_comp (φ : B →ₐ[K] A) (ψ : C →ₐ[K] B) :
    reductionMap (φ.comp ψ) = (reductionMap φ).comp (reductionMap ψ) :=
  Ideal.Quotient.ringHom_ext (RingHom.ext fun _ ↦ rfl)

/-- `φ̃` is `K̃`-linear. -/
noncomputable def reductionAlgHom (φ : B →ₐ[K] A) :
    Reduction K B →ₐ[IsLocalRing.ResidueField (Subring.unitClosedBall K)] Reduction K A where
  toRingHom := reductionMap φ
  commutes' r := by
    obtain ⟨c, rfl⟩ := IsLocalRing.residue_surjective r
    show Reduction.mk K A (powerBoundedMap φ (powerBounded.ofUnitClosedBall K B c)) =
      Reduction.mk K A (powerBounded.ofUnitClosedBall K A c)
    exact congrArg (Reduction.mk K A) (Subtype.ext (φ.commutes (c : K)))

end Functor

section Strict

variable {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]

/-- **BGR 1.1.9**: a map is *strict* if the image of every open set is open in the image. -/
def IsStrictMap (φ : B → A) : Prop :=
  ∀ U : Set B, IsOpen U → IsOpen (Subtype.val ⁻¹' (φ '' U) : Set (Set.range φ))

end Strict

end Affinoid

universe u

namespace IsAffinoidAlgebra

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : Type*} [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]

/-- **BGR 6.3.1/1**: `φ` is an isometry for `|·|_sup` iff `|φ(f)|_sup = 1` whenever `|f|_sup = 1`
(scale by 6.2.1/4 (ii): `|c g^m|_sup = 1`, then `|c| |φ(g)|^m = 1 = |c| |g|^m`). -/
theorem isometry_iff_forall_supSeminorm_eq_one_imp (hA : IsAffinoidAlgebra K A)
    (hB : IsAffinoidAlgebra K B) (φ : B →ₐ[K] A) :
    (∀ g : B, supSeminorm K (φ g) = supSeminorm K g) ↔
      ∀ g : B, supSeminorm K g = 1 → supSeminorm K (φ g) = 1 := by
  haveI := hA.hasSupSeminorm
  haveI := hB.hasSupSeminorm
  refine ⟨fun h g hg ↦ (h g).trans hg, fun h g ↦ ?_⟩
  rcases eq_or_ne (supSeminorm K g) 0 with h0 | h0
  · exact le_antisymm (supSeminorm_map_le φ g) (h0.trans_le (supSeminorm_nonneg K _))
  -- `|c gᵐ|_sup = 1` (BGR 6.2.1/4 (ii)), so `‖c‖ |φ g|ᵐ = 1 = ‖c‖ |g|ᵐ`
  obtain ⟨c, m, hm, hc⟩ := hB.exists_smul_pow_supSeminorm_eq_one h0
  have h1 := h _ hc
  rw [map_smul, map_pow, supSeminorm_smul, supSeminorm_pow K _ hm] at h1
  rw [supSeminorm_smul, supSeminorm_pow K _ hm] at hc
  have hc0 : ‖c‖ ≠ 0 := fun h' ↦ by
    rw [h', zero_mul] at hc
    exact zero_ne_one hc
  exact (pow_left_inj₀ (supSeminorm_nonneg K _) (supSeminorm_nonneg K _) hm).1
    (mul_left_cancel₀ hc0 (h1.trans hc.symm))

/-- **BGR 6.3.1/2**: `φ̃` is injective iff `φ` is an isometry for `|·|_sup`. -/
theorem injective_reductionMap_iff_isometry (hA : IsAffinoidAlgebra K A)
    (hB : IsAffinoidAlgebra K B) (φ : B →ₐ[K] A) :
    haveI := hA.hasSupSeminorm; haveI := hB.hasSupSeminorm
    Function.Injective (reductionMap φ) ↔ ∀ g : B, supSeminorm K (φ g) = supSeminorm K g := by
  haveI := hA.hasSupSeminorm
  haveI := hB.hasSupSeminorm
  constructor
  · -- if `|g|_sup = 1` and `|φ g|_sup < 1` then `τ g ≠ 0` lies in `ker φ̃` (BGR 6.3.1/2)
    intro hinj
    refine (hA.isometry_iff_forall_supSeminorm_eq_one_imp hB φ).2 fun g hg ↦ ?_
    refine le_antisymm ((supSeminorm_map_le φ g).trans hg.le) (le_of_not_gt fun hlt ↦ ?_)
    let b : powerBounded K B := ⟨g, mem_powerBounded.2 hg.le⟩
    have hb : reductionMap φ (Reduction.mk K B b) = 0 := by
      rw [reductionMap_mk, Ideal.Quotient.eq_zero_iff_mem]
      exact mem_topologicallyNilpotent.2 hlt
    have hb0 : Reduction.mk K B b = 0 := hinj (hb.trans (map_zero _).symm)
    exact (mem_topologicallyNilpotent.1 (Ideal.Quotient.eq_zero_iff_mem.1 hb0)).ne hg
  · -- an isometry has `|φ b|_sup < 1 → |b|_sup < 1`
    intro h
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hx' : Reduction.mk K A (powerBoundedMap φ b) = 0 := (reductionMap_mk φ b).symm.trans hx
    have hlt := mem_topologicallyNilpotent.1 (Ideal.Quotient.eq_zero_iff_mem.1 hx')
    rw [coe_powerBoundedMap, h] at hlt
    exact Ideal.Quotient.eq_zero_iff_mem.2 (mem_topologicallyNilpotent.2 hlt)

/-- **BGR 6.3.1/3**: if `φ̃` is injective then `ker φ ⊆ rad B` (an isometry has kernel inside
`{|g|_sup = 0} = rad B`, 6.2.1/4 (iii)). -/
theorem ker_le_nilradical_of_injective_reductionMap (hA : IsAffinoidAlgebra K A)
    (hB : IsAffinoidAlgebra K B) (φ : B →ₐ[K] A)
    (h : haveI := hA.hasSupSeminorm; haveI := hB.hasSupSeminorm
      Function.Injective (reductionMap φ)) :
    RingHom.ker φ ≤ nilradical B := by
  haveI := hA.hasSupSeminorm
  haveI := hB.hasSupSeminorm
  -- `φ` is an isometry, so `φ g = 0` forces `|g|_sup = 0`, i.e. `g` nilpotent (BGR 6.2.1/4 (iii))
  have hiso := (hA.injective_reductionMap_iff_isometry hB φ).1 h
  intro g hg
  rw [RingHom.mem_ker] at hg
  rw [mem_nilradical, ← hB.supSeminorm_eq_zero_iff_isNilpotent, ← hiso, hg]
  exact supSeminorm_zero K

/-- **BGR 6.3.1/6 (ii) ⇒ (i), injectivity**: for `B` reduced, an isometry for `|·|_sup` is
injective (`|·|_sup` is a norm on `B`, 6.2.1/4 (iii)). -/
theorem injective_of_isometry (hB : IsAffinoidAlgebra K B) [IsReduced B] (φ : B →ₐ[K] A)
    (h : ∀ g : B, supSeminorm K (φ g) = supSeminorm K g) : Function.Injective φ := by
  rw [injective_iff_map_eq_zero]
  intro g hg
  refine hB.eq_zero_of_supSeminorm_eq_zero ?_
  rw [← h, hg]
  exact supSeminorm_zero K

section Banach

-- `B` lives in the universe of `K` for `isStrictMap_of_isometry` (BGR 6.2.4/1 on `B`, plan D2).
variable {A : Type*} [NormedCommRing A] [NormedAlgebra K A] [CompleteSpace A] [IsUltrametricDist A]
  [NormOneClass A] {B : Type u} [NormedCommRing B] [NormedAlgebra K B] [CompleteSpace B]
  [IsUltrametricDist B] [NormOneClass B]

omit [NormOneClass B] in
/-- **BGR 6.3.1/4, first equation**: for `φ` strict,
`τ⁻¹(ker φ̃) = rad (B̌ + ker φ̊)` in `B̊` (if `φ(g)ⁿ → 0` and `φ(B̌)` is open in `φ(B)` then
`φ(g)ⁿ ∈ φ(B̌)` for large `n`, i.e. `gⁿ ∈ B̌ + ker φ̊`). -/
theorem comap_ker_reductionMap_eq_radical_of_isStrictMap (hA : IsAffinoidAlgebra K A)
    (hB : IsAffinoidAlgebra K B) (φ : B →ₐ[K] A) (hφ : IsStrictMap φ) :
    haveI := hA.hasSupSeminorm; haveI := hB.hasSupSeminorm
    (RingHom.ker (reductionMap φ)).comap (Reduction.mk K B) =
      (topologicallyNilpotent K B ⊔ RingHom.ker (powerBoundedMap φ)).radical := by
  haveI := hA.hasSupSeminorm
  haveI := hB.hasSupSeminorm
  -- `ker φ̃` is radical because `Ã` is reduced (BGR 1.2.5/7)
  have hker : (RingHom.ker (reductionMap φ)).IsRadical := fun x ⟨n, hn⟩ ↦ by
    rw [RingHom.mem_ker, map_pow] at hn
    exact RingHom.mem_ker.2 (IsReduced.eq_zero _ ⟨n, hn⟩)
  -- `B̌ ⊔ ker φ̊ ≤ τ⁻¹(ker φ̃)`
  have hsup : topologicallyNilpotent K B ⊔ RingHom.ker (powerBoundedMap φ) ≤
      (RingHom.ker (reductionMap φ)).comap (Reduction.mk K B) := by
    refine sup_le (fun b hb ↦ ?_) (fun b hb ↦ ?_)
    · rw [Ideal.mem_comap, RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem.2 hb, map_zero]
    · rw [Ideal.mem_comap, RingHom.mem_ker, reductionMap_mk, RingHom.mem_ker.1 hb, map_zero]
  refine le_antisymm ?_ ((Ideal.radical_mono hsup).trans (hker.comap _))
  intro g hg
  -- `φ(g)` is topologically nilpotent (BGR 6.2.3/2)
  rw [Ideal.mem_comap, RingHom.mem_ker, reductionMap_mk, Ideal.Quotient.eq_zero_iff_mem,
    mem_topologicallyNilpotent, coe_powerBoundedMap] at hg
  have htn := (hA.isTopologicallyNilpotent_iff_supSeminorm_lt_one (φ g)).2 hg
  unfold IsTopologicallyNilpotent at htn
  -- strictness: `φ(B̌)` is a neighbourhood of `0` in `φ(B)`, which contains `φ(gⁿ)` for large `n`
  have hV := hφ _ hB.isOpen_setOf_supSeminorm_lt_one
  have h0 : (⟨0, 0, map_zero φ⟩ : Set.range φ) ∈
      Subtype.val ⁻¹' (φ '' {b : B | supSeminorm K b < 1}) :=
    ⟨0, (supSeminorm_zero K).trans_lt zero_lt_one, map_zero φ⟩
  have hseq : Tendsto (fun n : ℕ ↦ (⟨φ ((g : B) ^ n), (g : B) ^ n, rfl⟩ : Set.range φ)) atTop
      (𝓝 ⟨0, 0, map_zero φ⟩) := by
    rw [tendsto_subtype_rng]
    simpa only [map_pow] using htn
  obtain ⟨n, b, hbU, hb⟩ := (hseq.eventually (hV.mem_nhds h0)).exists
  have hb' : φ b = φ ((g : B) ^ n) := hb
  -- `gⁿ = b + (gⁿ - b)` with `b ∈ B̌` and `gⁿ - b ∈ ker φ̊`
  have hbB : b ∈ powerBounded K B := mem_powerBounded.2 hbU.le
  have hkerb : powerBoundedMap φ (g ^ n - ⟨b, hbB⟩) = 0 := by
    apply Subtype.ext
    rw [coe_powerBoundedMap, AddSubgroupClass.coe_sub, SubmonoidClass.coe_pow, map_sub, ← hb',
      sub_self, ZeroMemClass.coe_zero]
  have hmem : g ^ n ∈ topologicallyNilpotent K B ⊔ RingHom.ker (powerBoundedMap φ) := by
    rw [← add_sub_cancel (⟨b, hbB⟩ : powerBounded K B) (g ^ n)]
    exact Ideal.add_mem _ (Ideal.mem_sup_left (mem_topologicallyNilpotent.2 hbU))
      (Ideal.mem_sup_right (RingHom.mem_ker.2 hkerb))
  exact ⟨n, hmem⟩

omit [NormOneClass B] in
/-- **BGR 6.3.1/4, second equation**: for `φ` strict, `ker φ̃ = rad (τ(ker φ̊))`. -/
theorem ker_reductionMap_eq_radical_map_of_isStrictMap (hA : IsAffinoidAlgebra K A)
    (hB : IsAffinoidAlgebra K B) (φ : B →ₐ[K] A) (hφ : IsStrictMap φ) :
    haveI := hA.hasSupSeminorm; haveI := hB.hasSupSeminorm
    RingHom.ker (reductionMap φ) =
      ((RingHom.ker (powerBoundedMap φ)).map (Reduction.mk K B)).radical := by
  haveI := hA.hasSupSeminorm
  haveI := hB.hasSupSeminorm
  -- push the first equation forward along the surjection `τ`, whose kernel is `B̌`
  have hτ : Function.Surjective (Reduction.mk K B) := Ideal.Quotient.mk_surjective
  rw [← Ideal.map_comap_of_surjective _ hτ (RingHom.ker (reductionMap φ)),
    hA.comap_ker_reductionMap_eq_radical_of_isStrictMap hB φ hφ,
    Ideal.map_radical_of_surjective hτ (by rw [Ideal.mk_ker]; exact le_sup_left),
    Ideal.map_sup, Ideal.map_quotient_self, bot_sup_eq]

omit [NormOneClass B] in
/-- **BGR 6.3.1/5**: if `φ` is strict and `ker φ ⊆ rad B` then `φ̃` is injective (`B̌` is a radical
ideal, so `rad (B̌ + ker φ̊) = B̌`). -/
theorem injective_reductionMap_of_isStrictMap_of_ker_le_nilradical (hA : IsAffinoidAlgebra K A)
    (hB : IsAffinoidAlgebra K B) (φ : B →ₐ[K] A) (hφ : IsStrictMap φ)
    (hker : RingHom.ker φ ≤ nilradical B) :
    haveI := hA.hasSupSeminorm; haveI := hB.hasSupSeminorm
    Function.Injective (reductionMap φ) := by
  haveI := hA.hasSupSeminorm
  haveI := hB.hasSupSeminorm
  -- `ker φ̊ ≤ B̌`: a power-bounded `b` with `φ b = 0` is nilpotent, so `|b|_sup = 0 < 1`
  have hle : RingHom.ker (powerBoundedMap φ) ≤ topologicallyNilpotent K B := fun b hb ↦ by
    have hb' : (b : B) ∈ RingHom.ker φ :=
      RingHom.mem_ker.2 (congrArg Subtype.val (RingHom.mem_ker.1 hb))
    have h0 : supSeminorm K (b : B) = 0 :=
      (hB.supSeminorm_eq_zero_iff_isNilpotent _).2 (mem_nilradical.1 (hker hb'))
    exact mem_topologicallyNilpotent.2 (h0.trans_lt zero_lt_one)
  -- so `τ⁻¹(ker φ̃) = rad B̌ = B̌ = ker τ` (BGR 6.3.1/4)
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hb : b ∈ (RingHom.ker (reductionMap φ)).comap (Reduction.mk K B) :=
    Ideal.mem_comap.2 (RingHom.mem_ker.2 hx)
  rw [hA.comap_ker_reductionMap_eq_radical_of_isStrictMap hB φ hφ, sup_eq_left.2 hle,
    topologicallyNilpotent_isRadical.radical] at hb
  exact Ideal.Quotient.eq_zero_iff_mem.2 hb

omit [NormOneClass B] in
/-- **BGR 6.3.1/6 (i) ⇒ (iii)**: an injective strict `φ` has injective `φ̃` (no reducedness). -/
theorem injective_reductionMap_of_injective_of_isStrictMap (hA : IsAffinoidAlgebra K A)
    (hB : IsAffinoidAlgebra K B) (φ : B →ₐ[K] A) (hinj : Function.Injective φ)
    (hφ : IsStrictMap φ) :
    haveI := hA.hasSupSeminorm; haveI := hB.hasSupSeminorm
    Function.Injective (reductionMap φ) := by
  refine hA.injective_reductionMap_of_isStrictMap_of_ker_le_nilradical hB φ hφ fun g hg ↦ ?_
  rw [RingHom.mem_ker, ← map_zero φ] at hg
  rw [hinj hg]
  exact zero_mem _

omit [NormOneClass A] in
/-- **BGR 6.3.1/6 (ii) ⇒ (i), strictness** (M5; `[CharZero K]`, plan D2): for `B` reduced an
isometry `φ` for `|·|_sup` into any Banach algebra `A` is strict: `‖g‖_B ≤ C |g|_sup =
C |φ(g)|_sup ≤ C ‖φ(g)‖_A` by 6.2.4/1 on `B`, so the inverse of `φ` on its image is Lipschitz and
`φ` maps open sets to open subsets of its image. -/
theorem isStrictMap_of_isometry [CharZero K] (hB : IsAffinoidAlgebra K B) [IsReduced B]
    (φ : B →ₐ[K] A) (h : ∀ g : B, supSeminorm K (φ g) = supSeminorm K g) : IsStrictMap φ := by
  -- `‖g‖ ≤ C |g|_sup = C |φ g|_sup ≤ C ‖φ g‖` (BGR 6.2.4/1 on `B`), so `φ⁻¹` is Lipschitz on `φ(B)`
  obtain ⟨C, hC⟩ := hB.isBanachFunctionAlgebra_of_isReduced
  set M := max C 0 with hM
  have hM0 : 0 ≤ M := le_max_right _ _
  have hbound : ∀ g : B, ‖g‖ ≤ M * ‖φ g‖ := fun g ↦
    calc ‖g‖ ≤ C * supSeminorm K g := hC g
      _ ≤ M * supSeminorm K g := mul_le_mul_of_nonneg_right (le_max_left _ _)
          (supSeminorm_nonneg K g)
      _ = M * supSeminorm K (φ g) := by rw [h]
      _ ≤ M * ‖φ g‖ := mul_le_mul_of_nonneg_left (supSeminorm_le_norm (K := K) _) hM0
  intro U hU
  rw [Metric.isOpen_iff]
  rintro ⟨_, x, rfl⟩ ⟨g, hgU, hg⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU g hgU
  have hM1 : 0 < M + 1 := by linarith
  refine ⟨ε / (M + 1), div_pos hε hM1, fun y hy ↦ ?_⟩
  obtain ⟨y, x', rfl⟩ := y
  refine ⟨x', hball ?_, rfl⟩
  have hdist : ‖φ x' - φ x‖ < ε / (M + 1) := by
    rw [← dist_eq_norm]
    exact hy
  rw [Metric.mem_ball, dist_eq_norm]
  calc ‖x' - g‖ ≤ M * ‖φ (x' - g)‖ := hbound _
    _ = M * ‖φ x' - φ x‖ := by rw [map_sub, hg]
    _ ≤ M * (ε / (M + 1)) := mul_le_mul_of_nonneg_left hdist.le hM0
    _ = ε * (M / (M + 1)) := by ring
    _ < ε * 1 := mul_lt_mul_of_pos_left ((div_lt_one hM1).2 (lt_add_one M)) hε
    _ = ε := mul_one ε

end Banach

end IsAffinoidAlgebra
