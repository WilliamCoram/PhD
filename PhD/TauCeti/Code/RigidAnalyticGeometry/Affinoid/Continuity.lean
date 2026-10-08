/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.RingTheory.Filtration
import PhD.TauCeti.Code.RigidAnalyticGeometry.Affinoid.Extend
import PhD.TauCeti.Code.RigidAnalyticGeometry.Affinoid.Noether
import PhD.TauCeti.Code.RigidAnalyticGeometry.BanachAlgebra.Continuity

/-!
# Continuity of homomorphisms of affinoid algebras

Every `K`-algebra homomorphism of a noetherian `K`-Banach algebra into an affinoid algebra is
continuous (BGR 6.1.3/1; Bosch 1.4/19), for any Banach norms: the family `𝔅 = {𝔪^ν}` of powers of
maximal ideals of an affinoid algebra has finite-dimensional quotients (BGR 6.1.2/3) and zero
intersection (Krull's intersection theorem), so BGR 3.7.5/2 applies. Consequently the affinoid
topology is independent of the presentation, every Banach algebra topology on an affinoid algebra is
the affinoid topology (BGR 6.1.3/2), a homomorphism of affinoid algebras is determined by its values
on an affinoid generating system, the target of a continuous finite homomorphism out of an affinoid
algebra is affinoid (BGR 6.1.1/5), `A⟨X⟩` is affinoid for affinoid `A`, and the norm on the target
of a homomorphism can be replaced by an equivalent one making it contractive (BGR 6.1.3/3).

Roadmap: `PhD/TauCeti/Roadmaps/RigidAnalyticGeometry/README.md`, §1.1.3–1.1.4 and §1.3. Tau Ceti
home: `TauCeti/RingTheory/Affinoid/Continuity.lean`.

## Main results

* `Ideal.sInf_maximalPowers_eq_bot` — in a noetherian ring the powers of the maximal ideals
  intersect in zero (Krull's intersection theorem).
* `IsAffinoidAlgebra.sInf_maximalPowers_eq_bot`,
  `IsAffinoidAlgebra.finiteDimensional_of_mem_maximalPowers` — the two inputs of BGR 3.7.5/2
  (BGR 6.1.3, the opening remark).
* `AlgHom.continuous_of_isAffinoidAlgebra` — **BGR 6.1.3/1**.
* `AlgEquiv.continuous_symm_of_isAffinoidAlgebra`,
  `AlgEquiv.exists_forall_norm_le_mul_of_isAffinoidAlgebra` — BGR 6.1.3/2, uniqueness of the
  Banach topology; `AlgEquiv.isPowerBounded_map_iff_of_isAffinoidAlgebra` and
  `AlgEquiv.isTopologicallyNilpotent_map_iff_of_isAffinoidAlgebra` follow.
* `AlgHom.ext_of_isAffinoidGeneratingSystem`, `IsAffinoidAlgebra.exists_isAffinoidGeneratingSystem`
  — affinoid generating systems determine homomorphisms and always exist.
* `IsAffinoidAlgebra.of_finite_of_continuous` — BGR 6.1.1/5.
* `IsAffinoidAlgebra.restricted` — `A⟨X⟩` is affinoid.
* `IsAffinoidAlgebra.exists_algEquiv_quotient_norm_comp_le` — BGR 6.1.3/3.
-/

open MvPowerSeries MvPowerSeries.Restricted PowerBounded

/-! ### The powers of the maximal ideals -/

/-- The family `𝔅 = {𝔪^ν ; 𝔪 maximal, ν ∈ ℕ}` of BGR 6.1.3. -/
def Ideal.maximalPowers (A : Type*) [CommRing A] : Set (Ideal A) :=
  {I | ∃ (𝔪 : Ideal A) (ν : ℕ), 𝔪.IsMaximal ∧ I = 𝔪 ^ ν}

/-- In a noetherian ring the powers of the maximal ideals intersect in zero: by Krull's
intersection theorem an element `f` of the intersection satisfies `(1 - m) f = 0` for some
`m ∈ 𝔪`, for every maximal `𝔪`, so its annihilator lies in no maximal ideal. Source: BGR 6.1.3
("KRULL's Intersection Theorem implies that for each `𝔪` there is an element `m ∈ 𝔪` such that
`(1 − m) f = 0`. Hence the annihilator of `f` is contained in no maximal ideal in `B`. Therefore,
`f = 0`"), via `Ideal.mem_iInf_smul_pow_eq_bot_iff`. -/
theorem Ideal.sInf_maximalPowers_eq_bot (A : Type*) [CommRing A] [IsNoetherianRing A] :
    sInf (Ideal.maximalPowers A) = ⊥ := by
  refine eq_bot_iff.2 fun f hf ↦ Ideal.mem_bot.2 ?_
  by_contra hf0
  have hann : (Submodule.span A {f}).annihilator ≠ ⊤ := fun h ↦ hf0 <| (one_smul A f).symm.trans
    ((Submodule.mem_annihilator_span_singleton f 1).1 (h ▸ Submodule.mem_top))
  obtain ⟨𝔪, h𝔪, hle⟩ := Ideal.exists_le_maximal _ hann
  have hinf : f ∈ (⨅ i : ℕ, 𝔪 ^ i • ⊤ : Submodule A A) := by
    refine Submodule.mem_iInf _ |>.2 fun i ↦ ?_
    rw [smul_eq_mul, Ideal.mul_top]
    exact Submodule.mem_sInf.1 hf _ ⟨𝔪, i, h𝔪, rfl⟩
  obtain ⟨⟨r, hr⟩, hrf⟩ := (Ideal.mem_iInf_smul_pow_eq_bot_iff 𝔪 f).1 hinf
  have h1r : 1 - r ∈ 𝔪 := hle ((Submodule.mem_annihilator_span_singleton f _).2 (by
    rw [sub_smul, one_smul, hrf, sub_self]))
  exact h𝔪.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using 𝔪.add_mem h1r hr))

namespace IsAffinoidAlgebra

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : Type*} [CommRing A] [Algebra K A]

/-- Condition (ii) of BGR 3.7.5/2 for an affinoid algebra. Source: BGR 6.1.3. -/
theorem sInf_maximalPowers_eq_bot (hA : IsAffinoidAlgebra K A) :
    sInf (Ideal.maximalPowers A) = ⊥ :=
  haveI := hA.isNoetherianRing
  Ideal.sInf_maximalPowers_eq_bot A

/-- Condition (i) of BGR 3.7.5/2 for an affinoid algebra: `dim_K A ⧸ 𝔪^ν < ∞`.
Source: BGR 6.1.3 ("We have `dim_k B/𝔟 < ∞` for all `𝔟 ∈ 𝔅` by Corollary 6.1.2/3"). -/
theorem finiteDimensional_of_mem_maximalPowers (hA : IsAffinoidAlgebra K A) {I : Ideal A}
    (hI : I ∈ Ideal.maximalPowers A) : FiniteDimensional K (A ⧸ I) := by
  obtain ⟨𝔪, ν, h𝔪, rfl⟩ := hI
  rcases Nat.eq_zero_or_pos ν with rfl | hν
  · rw [pow_zero, Ideal.one_eq_top]
    haveI : Subsingleton (A ⧸ (⊤ : Ideal A)) := Ideal.Quotient.subsingleton_iff.2 rfl
    infer_instance
  · exact hA.finiteDimensional_quotient_pow 𝔪 hν.ne'

end IsAffinoidAlgebra

/-! ### Continuity (BGR 6.1.3/1) -/

section Continuity

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : Type*} [NormedCommRing A] [NormedAlgebra K A] [CompleteSpace A] [IsUltrametricDist A]
  [NormOneClass A]
  {B : Type*} [NormedCommRing B] [NormedAlgebra K B] [CompleteSpace B] [IsUltrametricDist B]
  [NormOneClass B]

/-- **BGR 6.1.3/1**: every `K`-algebra homomorphism of a noetherian `K`-Banach algebra into an
affinoid algebra is continuous, for any complete algebra norms. Source: BGR 6.1.3/1 ("Since each
`B ∈ 𝔄` is Noetherian, we derive from Proposition 3.7.5/2"). -/
theorem AlgHom.continuous_of_isAffinoidAlgebra [IsNoetherianRing A] (hB : IsAffinoidAlgebra K B)
    (Φ : A →ₐ[K] B) : Continuous Φ :=
  haveI := hB.isNoetherianRing
  AlgHom.continuous_of_isNoetherianRing (Ideal.maximalPowers B)
    (fun _ h ↦ hB.finiteDimensional_of_mem_maximalPowers h) hB.sInf_maximalPowers_eq_bot Φ

/-- Every `K`-algebra homomorphism between affinoid algebras is continuous, for any residue norms.
Source: Bosch 1.4/19 ("any `K`-algebra homomorphism between affinoid `K`-algebras is continuous
with respect to residue norms"). -/
theorem AlgHom.continuous_of_isAffinoidAlgebra' (hA : IsAffinoidAlgebra K A)
    (hB : IsAffinoidAlgebra K B) (Φ : A →ₐ[K] B) : Continuous Φ :=
  haveI := hA.isNoetherianRing
  Φ.continuous_of_isAffinoidAlgebra hB

/-- A presentation `Tₙ → A` is continuous for every Banach norm on the affinoid algebra `A`:
the affinoid topology does not depend on the presentation. Source: BGR 6.1.3 ("a `k`-algebra can
carry at most one `k`-affinoid structure"). -/
theorem IsAffinoidAlgebra.continuous_presentation (hA : IsAffinoidAlgebra K A) {n : ℕ}
    (α : Affinoid.TateAlgebra K n →ₐ[K] A) : Continuous α :=
  α.continuous_of_isAffinoidAlgebra hA

/-- Every ideal of an affinoid algebra is closed, for every Banach norm. Source: BGR 6.1.1/3
("Each ideal `𝔞 ⊂ A` is closed"), from BGR 3.7.2/2. -/
theorem IsAffinoidAlgebra.isClosed_ideal (hA : IsAffinoidAlgebra K A) (I : Ideal A) :
    IsClosed (I : Set A) :=
  haveI := hA.isNoetherianRing
  I.isClosed_of_isNoetherianRing K

/-- **BGR 6.1.3/2**: a `K`-algebra isomorphism between two Banach algebra structures on an affinoid
algebra is a homeomorphism; all Banach algebra topologies on an affinoid algebra coincide. -/
theorem AlgEquiv.continuous_symm_of_isAffinoidAlgebra (hA : IsAffinoidAlgebra K A)
    (hB : IsAffinoidAlgebra K B) (e : A ≃ₐ[K] B) : Continuous e.symm :=
  e.symm.toAlgHom.continuous_of_isAffinoidAlgebra' hB hA

/-- **BGR 6.1.3/2** in terms of norms: any two complete algebra norms on an affinoid algebra are
equivalent. Source: roadmap §1.3.3 ("any two complete `K`-algebra norms on `A` are equivalent"). -/
theorem AlgEquiv.exists_forall_norm_le_mul_of_isAffinoidAlgebra (hA : IsAffinoidAlgebra K A)
    (hB : IsAffinoidAlgebra K B) (e : A ≃ₐ[K] B) :
    ∃ C C' : ℝ, (∀ a, ‖e a‖ ≤ C * ‖a‖) ∧ ∀ b, ‖e.symm b‖ ≤ C' * ‖b‖ := by
  obtain ⟨C, -, hC⟩ := SemilinearMapClass.bound_of_continuous e.toAlgHom
    (e.toAlgHom.continuous_of_isAffinoidAlgebra' hA hB)
  obtain ⟨C', -, hC'⟩ := SemilinearMapClass.bound_of_continuous e.symm.toAlgHom
    (e.continuous_symm_of_isAffinoidAlgebra hA hB)
  exact ⟨C, C', hC, hC'⟩

/-- Power-boundedness is the same for all Banach norms on an affinoid algebra.
Source: roadmap §1.3.3. -/
theorem AlgEquiv.isPowerBounded_map_iff_of_isAffinoidAlgebra (hA : IsAffinoidAlgebra K A)
    (hB : IsAffinoidAlgebra K B) (e : A ≃ₐ[K] B) (a : A) :
    IsPowerBounded (e a) ↔ IsPowerBounded a := by
  obtain ⟨C, C', hC, hC'⟩ := e.exists_forall_norm_le_mul_of_isAffinoidAlgebra hA hB
  refine ⟨fun h ↦ ?_, fun h ↦ IsPowerBounded.map K (φ := (e : A →+* B)) hC h⟩
  simpa using IsPowerBounded.map K (φ := (e.symm : B →+* A)) hC' h

/-- Topological nilpotence is the same for all Banach norms on an affinoid algebra.
Source: roadmap §1.3.3. -/
theorem AlgEquiv.isTopologicallyNilpotent_map_iff_of_isAffinoidAlgebra
    (hA : IsAffinoidAlgebra K A) (hB : IsAffinoidAlgebra K B) (e : A ≃ₐ[K] B) (a : A) :
    IsTopologicallyNilpotent (e a) ↔ IsTopologicallyNilpotent a := by
  have he := e.toAlgHom.continuous_of_isAffinoidAlgebra' hA hB
  have he' := e.continuous_symm_of_isAffinoidAlgebra hA hB
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · simpa [IsTopologicallyNilpotent, Function.comp_def] using (he'.tendsto 0).comp h
  · simpa [IsTopologicallyNilpotent, Function.comp_def] using (he.tendsto 0).comp h

/-- A homomorphism of affinoid algebras is determined by its values on an affinoid generating
system. Source: BGR 6.1.1/4 and 6.1.3/1; roadmap §1.1.4. -/
theorem AlgHom.ext_of_isAffinoidGeneratingSystem {σ : Type*} [_root_.Finite σ]
    (hA : IsAffinoidAlgebra K A) (hB : IsAffinoidAlgebra K B) {a : σ → A}
    (ha : IsAffinoidGeneratingSystem (Algebra.ofId K A) (continuous_algebraMap K A) a)
    {ψ₁ ψ₂ : A →ₐ[K] B} (h : ∀ i, ψ₁ (a i) = ψ₂ (a i)) : ψ₁ = ψ₂ := by
  obtain ⟨hb, hsurj⟩ := ha
  have hΦ := continuous_extendAlgHom (Algebra.ofId K A) (continuous_algebraMap K A) a hb
  have h' : ψ₁.comp (extendAlgHom (Algebra.ofId K A) (continuous_algebraMap K A) a hb) =
      ψ₂.comp (extendAlgHom (Algebra.ofId K A) (continuous_algebraMap K A) a hb) :=
    algHom_ext_of_continuous ((ψ₁.continuous_of_isAffinoidAlgebra' hA hB).comp hΦ)
      ((ψ₂.continuous_of_isAffinoidAlgebra' hA hB).comp hΦ) fun i ↦
        (congrArg ψ₁ (extendAlgHom_X _ (continuous_algebraMap K A) a hb i)).trans
          ((h i).trans (congrArg ψ₂ (extendAlgHom_X _ (continuous_algebraMap K A) a hb i)).symm)
  refine AlgHom.ext fun x ↦ ?_
  obtain ⟨y, rfl⟩ := hsurj x
  exact AlgHom.congr_fun h' y

/-- An affinoid Banach algebra has an affinoid generating system over `K`: the images of the
variables under a presentation, which is continuous. Source: BGR 6.1.1, p. 223 (affinoid
generators); the converse of `IsAffinoidAlgebra.of_isAffinoidGeneratingSystem`. -/
theorem IsAffinoidAlgebra.exists_isAffinoidGeneratingSystem (hA : IsAffinoidAlgebra K A) :
    ∃ (n : ℕ) (a : Fin n → A),
      IsAffinoidGeneratingSystem (Algebra.ofId K A) (continuous_algebraMap K A) a := by
  obtain ⟨n, α, hα⟩ := id hA
  have hc := hA.continuous_presentation α
  obtain ⟨C, hC⟩ := exists_forall_norm_le_mul_of_continuous α hc
  have hb : ∀ i, IsPowerBounded (α (X K (1 : Fin n → ℝ) i)) := fun i ↦
    IsPowerBounded.map K (φ := α.toRingHom) hC (isPowerBounded_X i)
  have heq := extendAlgHom_unique (Algebra.ofId K A) (continuous_algebraMap K A)
    (fun i ↦ α (X K (1 : Fin n → ℝ) i)) hb α hc
    (fun c ↦ by rw [← algebraMap_apply]; exact α.commutes c) fun _ ↦ rfl
  exact ⟨n, _, hb, heq ▸ hα⟩

omit [NormOneClass B] in
/-- **BGR 6.1.1/5**: the target of a continuous finite `K`-algebra homomorphism out of an affinoid
algebra into a Banach algebra is affinoid. Source: BGR 6.1.1/5 ("We may assume `B = Tₙ` for some
`n`"), using the continuity of presentations. -/
theorem IsAffinoidAlgebra.of_finite_of_continuous (hA : IsAffinoidAlgebra K A) (φ : A →ₐ[K] B)
    (hφ : Continuous φ) (hfin : φ.toRingHom.Finite) : IsAffinoidAlgebra K B := by
  obtain ⟨n, α, hα⟩ := id hA
  exact IsAffinoidAlgebra.of_finite_tateAlgebra (φ.comp α) (hφ.comp (hA.continuous_presentation α))
    (hfin.comp (RingHom.Finite.of_surjective _ hα))

/-- `A⟨X₁, …, Xₘ⟩` is affinoid for an affinoid Banach algebra `A`: a presentation `Tₙ → A` lifts
to a surjection `Tₙ⟨X⟩ → A⟨X⟩` and `Tₙ⟨X⟩ ≅ T_{m+n}`. Source: BGR 6.1.4 ("If `A` is a
`k`-affinoid algebra … then the ring `A⟨X⟩` of strictly convergent power series over `A` is
`k`-affinoid"); BGR 6.1.1/9. -/
theorem IsAffinoidAlgebra.restricted (hA : IsAffinoidAlgebra K A) {σ : Type*} [_root_.Finite σ] :
    IsAffinoidAlgebra K (Restricted A (1 : σ → ℝ)) := by
  obtain ⟨n, α, hα⟩ := id hA
  have hc := hA.continuous_presentation α
  have hsurj := surjective_mapAlgHom_of_surjective (σ := σ) α hc hα
  letI := Fintype.ofFinite σ
  let r : Restricted (Affinoid.TateAlgebra K n) (1 : σ → ℝ) ≃ₐ[K]
      Restricted (Affinoid.TateAlgebra K n) (1 : Fin (Fintype.card σ) → ℝ) :=
    AlgEquiv.ofRingEquiv (f := renameEquiv (Affinoid.TateAlgebra K n) (Fintype.equivFin σ))
      fun c ↦ by
        rw [algebraMap_eq_C_comp (1 : σ → ℝ) (S := Affinoid.TateAlgebra K n),
          algebraMap_eq_C_comp (1 : Fin (Fintype.card σ) → ℝ) (S := Affinoid.TateAlgebra K n),
          RingHom.comp_apply, RingHom.comp_apply, renameEquiv_C]
  have h1 : IsAffinoidAlgebra K (Restricted (Affinoid.TateAlgebra K n) (1 : σ → ℝ)) :=
    (IsAffinoidAlgebra.tateAlgebra (Fintype.card σ + n)).of_algEquiv
      ((Affinoid.TateAlgebra.sumEquiv K n (Fintype.card σ)).symm.trans r.symm)
  exact h1.of_surjective (mapAlgHom α hc) hsurj

/-- **BGR 6.1.3/3** (contractive renorming): for a homomorphism `φ : B → A` of affinoid algebras
there is a presentation `B⟨X⟩ ⧸ I ≅ A` of `A` over `B` whose residue norm is equivalent to the
given norm on `A` and for which `φ` is contractive. Source: BGR 6.1.3/3 ("the algebra norm on `A`
can be replaced by an equivalent one such that `φ` becomes contractive"). -/
theorem IsAffinoidAlgebra.exists_algEquiv_quotient_norm_comp_le (hA : IsAffinoidAlgebra K A)
    (hB : IsAffinoidAlgebra K B) (φ : B →ₐ[K] A) :
    ∃ (n : ℕ) (I : Ideal (Restricted B (1 : Fin n → ℝ)))
      (e : (Restricted B (1 : Fin n → ℝ) ⧸ I) ≃ₐ[K] A),
      Continuous e ∧ Continuous e.symm ∧ ∀ b, ‖e.symm (φ b)‖ ≤ ‖b‖ := by
  obtain ⟨n, a, hb, hsurj₀⟩ := hA.exists_isAffinoidGeneratingSystem
  have hφ := φ.continuous_of_isAffinoidAlgebra' hB hA
  let ψ := extendAlgHom φ hφ a hb
  let ι := mapAlgHom (σ := Fin n) (Algebra.ofId K B) (continuous_algebraMap K B)
  have hcomp : ψ.comp ι = extendAlgHom (Algebra.ofId K A) (continuous_algebraMap K A) a hb :=
    extendAlgHom_unique _ _ a hb _
      ((continuous_extendAlgHom φ hφ a hb).comp
        (continuous_mapAlgHom _ (continuous_algebraMap K B)))
      (fun c ↦ (congrArg ψ (mapAlgHom_C _ (continuous_algebraMap K B) c)).trans
        ((extendAlgHom_C φ hφ a hb _).trans (φ.commutes c)))
      fun i ↦ (congrArg ψ (mapAlgHom_X _ (continuous_algebraMap K B) i)).trans
        (extendAlgHom_X φ hφ a hb i)
  have hψ : Function.Surjective ψ := by
    refine Function.Surjective.of_comp (g := ι) ?_
    rw [← AlgHom.coe_comp, hcomp]
    exact hsurj₀
  let e := Ideal.quotientKerAlgEquivOfSurjective hψ
  refine ⟨n, RingHom.ker ψ, e, ?_, ?_, fun b ↦ ?_⟩
  · exact (QuotientAddGroup.isQuotientMap_mk (RingHom.ker ψ).toAddSubgroup).continuous_iff.2
      (continuous_extendAlgHom φ hφ a hb)
  · rcases subsingleton_or_nontrivial A with hA0 | hA0
    · exact continuous_of_const fun x y ↦ congrArg e.symm (Subsingleton.elim x y)
    · haveI : IsClosed ((RingHom.ker ψ : Ideal (Restricted B (1 : Fin n → ℝ))) :
          Set (Restricted B (1 : Fin n → ℝ))) := hB.restricted.isClosed_ideal _
      haveI : NormOneClass (Restricted B (1 : Fin n → ℝ) ⧸ RingHom.ker ψ) :=
        Ideal.Quotient.normOneClass_of_ne_top _ (RingHom.ker_ne_top ψ)
      exact e.continuous_symm_of_isAffinoidAlgebra (hB.restricted.quotient _) hA
  · have he : e.symm (φ b) = Ideal.Quotient.mk (RingHom.ker ψ) (C (1 : Fin n → ℝ) b) :=
      e.symm_apply_eq.2 (extendAlgHom_C φ hφ a hb b).symm
    rw [he]
    exact (Ideal.Quotient.norm_mk_le _ _).trans (norm_C _ _).le

end Continuity
