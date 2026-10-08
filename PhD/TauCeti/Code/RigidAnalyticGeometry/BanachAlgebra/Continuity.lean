/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Topology.Algebra.Module.FiniteDimension
import PhD.TauCeti.Code.RigidAnalyticGeometry.BanachAlgebra.Noetherian

/-!
# Automatic continuity of homomorphisms of Banach algebras

BGR 3.7.5: a `K`-algebra homomorphism `Φ : A → B` between `K`-Banach algebras is continuous as soon
as `B` has a family `𝔅` of closed ideals with finite-dimensional quotients and zero intersection
whose preimages in `A` are closed (BGR 3.7.5/1, by the closed graph theorem). For noetherian
Banach algebras all ideals are closed (`BanachAlgebra/Noetherian.lean`), so every `K`-algebra
homomorphism of a noetherian Banach algebra into a noetherian Banach algebra with such a family is
continuous (BGR 3.7.5/2), and all Banach algebra topologies on such an algebra coincide
(BGR 3.7.5/3), stated for a `K`-algebra isomorphism between two Banach algebras.

Roadmap: `PhD/TauCeti/Roadmaps/RigidAnalyticGeometry/README.md`, §1.3.2–1.3.3 (the general
statements, "proved as stated so that the `p`-adic-functional-analysis roadmap's Banach algebras
can use it"). Tau Ceti home: `TauCeti/Analysis/Normed/Algebra/Continuity.lean`.

## Main results

* `LinearMap.continuous_of_isClosed_ker_of_finiteDimensional` — a linear map into a
  finite-dimensional normed space with closed kernel is continuous (BGR 3.7.5/1, the step
  "`ψ̄` and hence `ψ` are continuous").
* `AlgHom.continuous_of_forall_isClosed_of_finiteDimensional` — BGR 3.7.5/1.
* `AlgHom.continuous_of_isNoetherianRing` — BGR 3.7.5/2.
* `AlgEquiv.continuous_of_isNoetherianRing`, `AlgEquiv.continuous_symm_of_isNoetherianRing`,
  `AlgEquiv.exists_forall_norm_le_mul_of_isNoetherianRing` — BGR 3.7.5/3.
-/

open Filter Topology

section ClosedKernel

variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K]
  {E F : Type*} [NormedAddCommGroup E] [NormedSpace K E] [NormedAddCommGroup F] [NormedSpace K F]

/-- A linear map into a finite-dimensional normed space whose kernel is closed is continuous: it
factors through the quotient by its kernel, a finite-dimensional normed space, on which every
linear map is continuous. Source: BGR 3.7.5/1 ("the residue spaces `A/ker ψ` and `B/𝔟` provided
with the residue norms are finite-dimensional … Therefore `ψ̄` and hence `ψ` are continuous"),
via `LinearMap.quotKerEquivRange` and `LinearMap.continuous_of_finiteDimensional`. -/
theorem LinearMap.continuous_of_isClosed_ker_of_finiteDimensional [FiniteDimensional K F]
    (f : E →ₗ[K] F) (hf : IsClosed (LinearMap.ker f : Set E)) : Continuous f := by
  haveI : IsClosed ((LinearMap.ker f : Submodule K E) : Set E) := hf
  haveI : FiniteDimensional K (E ⧸ LinearMap.ker f) := f.quotKerEquivRange.symm.finiteDimensional
  have h : ⇑f = ⇑((LinearMap.ker f).liftQ f le_rfl) ∘ ⇑(LinearMap.ker f).mkQ := rfl
  rw [h]
  exact ((LinearMap.ker f).liftQ f le_rfl).continuous_of_finiteDimensional.comp continuous_quot_mk

end ClosedKernel

section BanachAlgebra

variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K]
  {A : Type*} [NormedCommRing A] [NormedAlgebra K A] [CompleteSpace A]
  {B : Type*} [NormedCommRing B] [NormedAlgebra K B] [CompleteSpace B]

omit [CompleteSpace A] [CompleteSpace B] in
/-- The residue map `A → B ⧸ 𝔟` of `Φ` is continuous when `𝔟` is closed with finite-dimensional
quotient and `Φ⁻¹ 𝔟` is closed. Source: BGR 3.7.5/1 (the map `ψ := β ∘ Φ`). -/
theorem AlgHom.continuous_quotient_mk_comp_of_isClosed (Φ : A →ₐ[K] B) (𝔟 : Ideal B)
    [IsClosed (𝔟 : Set B)] [FiniteDimensional K (B ⧸ 𝔟)]
    (hA : IsClosed ((𝔟.comap Φ : Ideal A) : Set A)) :
    Continuous ((Ideal.Quotient.mkₐ K 𝔟).comp Φ) := by
  have hker : (LinearMap.ker ((Ideal.Quotient.mkₐ K 𝔟).comp Φ).toLinearMap : Set A) =
      ((𝔟.comap Φ : Ideal A) : Set A) := by
    ext a
    simp [Ideal.Quotient.eq_zero_iff_mem]
  exact LinearMap.continuous_of_isClosed_ker_of_finiteDimensional _ (hker ▸ hA)

/-- **BGR 3.7.5/1**: a `K`-algebra homomorphism `Φ : A → B` of `K`-Banach algebras is continuous
if `B` has a family `𝔅` of ideals with (i) each `𝔟 ∈ 𝔅` and each `Φ⁻¹ 𝔟` closed, (ii) each
`B ⧸ 𝔟` finite-dimensional over `K`, (iii) `⋂ 𝔅 = 0`. Source: BGR 3.7.5/1, by the closed graph
theorem `LinearMap.continuous_of_seq_closed_graph`. -/
theorem AlgHom.continuous_of_forall_isClosed_of_finiteDimensional (Φ : A →ₐ[K] B)
    (𝔅 : Set (Ideal B)) (hB : ∀ 𝔟 ∈ 𝔅, IsClosed (𝔟 : Set B))
    (hA : ∀ 𝔟 ∈ 𝔅, IsClosed ((𝔟.comap Φ : Ideal A) : Set A))
    (hfin : ∀ 𝔟 ∈ 𝔅, FiniteDimensional K (B ⧸ 𝔟)) (hinf : sInf 𝔅 = ⊥) : Continuous Φ := by
  refine LinearMap.continuous_of_seq_closed_graph (g := Φ.toLinearMap) fun u x y hu hΦu ↦ ?_
  suffices h : y - Φ x ∈ sInf 𝔅 by
    rw [hinf, Ideal.mem_bot, sub_eq_zero] at h
    exact h
  refine Ideal.mem_sInf.2 fun {𝔟} h𝔟 ↦ ?_
  haveI := hB 𝔟 h𝔟
  haveI := hfin 𝔟 h𝔟
  have hψ := Φ.continuous_quotient_mk_comp_of_isClosed 𝔟 (hA 𝔟 h𝔟)
  have h₁ : Tendsto (fun n ↦ Ideal.Quotient.mk 𝔟 (Φ (u n))) atTop
      (𝓝 (Ideal.Quotient.mk 𝔟 (Φ x))) :=
    (hψ.tendsto x).comp hu
  have h₂ : Tendsto (fun n ↦ Ideal.Quotient.mk 𝔟 (Φ (u n))) atTop
      (𝓝 (Ideal.Quotient.mk 𝔟 y)) :=
    (continuous_quot_mk.tendsto y).comp hΦu
  exact Ideal.Quotient.eq.1 (tendsto_nhds_unique h₂ h₁)

variable [IsUltrametricDist A] [NormOneClass A] [IsUltrametricDist B] [NormOneClass B]

/-- **BGR 3.7.5/2**: every `K`-algebra homomorphism of a noetherian `K`-Banach algebra `A` into a
noetherian `K`-Banach algebra `B` having a family `𝔅` of ideals with finite-dimensional quotients
and zero intersection is continuous. Source: BGR 3.7.5/2 ("From Propositions 1 and 3.7.2/2, we
easily derive"). -/
theorem AlgHom.continuous_of_isNoetherianRing [IsNoetherianRing A] [IsNoetherianRing B]
    (𝔅 : Set (Ideal B)) (hfin : ∀ 𝔟 ∈ 𝔅, FiniteDimensional K (B ⧸ 𝔟)) (hinf : sInf 𝔅 = ⊥)
    (Φ : A →ₐ[K] B) : Continuous Φ :=
  Φ.continuous_of_forall_isClosed_of_finiteDimensional 𝔅
    (fun 𝔟 _ ↦ 𝔟.isClosed_of_isNoetherianRing K)
    (fun 𝔟 _ ↦ (𝔟.comap Φ).isClosed_of_isNoetherianRing K) hfin hinf

/-- **BGR 3.7.5/3**, first half: a `K`-algebra isomorphism from a noetherian Banach algebra onto a
noetherian Banach algebra with a family as in BGR 3.7.5/2 is continuous. -/
theorem AlgEquiv.continuous_of_isNoetherianRing [IsNoetherianRing A] [IsNoetherianRing B]
    (𝔅 : Set (Ideal B)) (hfin : ∀ 𝔟 ∈ 𝔅, FiniteDimensional K (B ⧸ 𝔟)) (hinf : sInf 𝔅 = ⊥)
    (e : A ≃ₐ[K] B) : Continuous e :=
  AlgHom.continuous_of_isNoetherianRing 𝔅 hfin hinf e.toAlgHom

/-- **BGR 3.7.5/3**, second half: the inverse of such an isomorphism is continuous too, by the
open mapping theorem (`LinearEquiv.continuous_symm`). Hence "all Banach algebra structures on `B`
have the same underlying topological space". -/
theorem AlgEquiv.continuous_symm_of_isNoetherianRing [IsNoetherianRing A] [IsNoetherianRing B]
    (𝔅 : Set (Ideal B)) (hfin : ∀ 𝔟 ∈ 𝔅, FiniteDimensional K (B ⧸ 𝔟)) (hinf : sInf 𝔅 = ⊥)
    (e : A ≃ₐ[K] B) : Continuous e.symm :=
  e.toLinearEquiv.continuous_symm (e.continuous_of_isNoetherianRing 𝔅 hfin hinf)

/-- **BGR 3.7.5/3** in terms of norms: the two complete algebra norms are equivalent. -/
theorem AlgEquiv.exists_forall_norm_le_mul_of_isNoetherianRing [IsNoetherianRing A]
    [IsNoetherianRing B] (𝔅 : Set (Ideal B)) (hfin : ∀ 𝔟 ∈ 𝔅, FiniteDimensional K (B ⧸ 𝔟))
    (hinf : sInf 𝔅 = ⊥) (e : A ≃ₐ[K] B) :
    ∃ C C' : ℝ, (∀ a, ‖e a‖ ≤ C * ‖a‖) ∧ ∀ b, ‖e.symm b‖ ≤ C' * ‖b‖ := by
  obtain ⟨C, -, hC⟩ := SemilinearMapClass.bound_of_continuous e.toAlgHom
    (e.continuous_of_isNoetherianRing 𝔅 hfin hinf)
  obtain ⟨C', -, hC'⟩ := SemilinearMapClass.bound_of_continuous e.symm.toAlgHom
    (e.continuous_symm_of_isNoetherianRing 𝔅 hfin hinf)
  exact ⟨C, C', hC, hC'⟩

end BanachAlgebra
