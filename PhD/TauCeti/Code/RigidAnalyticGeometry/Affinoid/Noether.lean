/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.RingTheory.Ideal.HasGoingUp
import Mathlib.RingTheory.Localization.Finiteness
import PhD.TauCeti.Code.RigidAnalyticGeometry.Affinoid.Basic
import PhD.TauCeti.Code.RigidAnalyticGeometry.TateAlgebra.Stable

/-!
# Noether normalisation for affinoid algebras

Every nonzero affinoid algebra `A` is a finite extension of a Tate algebra `T_d` (BGR 6.1.2/1–2;
Bosch 1.2/10 and 1.4/2), proved by induction on the number of variables of a presentation through a
distinguished chart (shear) and the Weierstrass finiteness theorem, exactly as BGR does. The integer
`d` is the Krull dimension of `A` (BGR 6.1.2, Remark), the residue rings `A ⧸ 𝔮` with maximal
radical are finite-dimensional over `K` (BGR 6.1.2/3; Bosch 1.2/11 and 1.4/3), and affinoid domains
are Japanese in characteristic zero (BGR 6.1.2/4).

Roadmap: `PhD/TauCeti/Roadmaps/RigidAnalyticGeometry/README.md`, §1.2. Tau Ceti home:
`TauCeti/RingTheory/Affinoid/Noether.lean`.

## Main results

* `Affinoid.TateAlgebra.exists_finite_injective_comp` — BGR 6.1.2/1 (i), for a finite
  `β : Tₙ → A`: a `K`-algebra map `T_d → Tₙ`, `d ≤ n`, with `β ∘ ψ` finite and injective.
* `IsAffinoidAlgebra.exists_finite_injective` — **Noether normalisation**, BGR 6.1.2/2.
* `ringKrullDim_le_of_isIntegral_of_injective`,
  `IsAffinoidAlgebra.ringKrullDim_eq_of_finite_injective`,
  `IsAffinoidAlgebra.exists_ringKrullDim_eq` — `dim A = d` (BGR 6.1.2, Remark).
* `IsAffinoidAlgebra.finiteDimensional_quotient_of_radical_isMaximal` — BGR 6.1.2/3, with the
  consequences `finiteDimensional_quotient_of_isMaximal`, `finiteDimensional_quotient_pow` and
  `Ideal.isMaximal_comap_of_isAffinoidAlgebra`.
* `FractionRing.finiteDimensional_of_finite` — the fraction field of a finite extension of domains
  is a finite extension of the fraction field.
* `IsAffinoidAlgebra.isJapaneseRing` — BGR 6.1.2/4, in characteristic zero.
-/

open MvPowerSeries MvPowerSeries.Restricted

universe u

namespace Affinoid.TateAlgebra

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K] {n : ℕ}

variable (K n) in
/-- The inclusion `Tₙ → T_{n+1}` of the series not involving `X 0`, as a `K`-algebra
homomorphism. -/
noncomputable def ofTailAlgHom : TateAlgebra K n →ₐ[K] TateAlgebra K (n + 1) :=
  { ofTail K n with
    commutes' := fun a ↦ by
      change ofTail K n (algebraMap K _ a) = algebraMap K _ a
      rw [algebraMap_apply, algebraMap_apply]
      exact ofTail_C a }

omit [CompleteSpace K] in
@[simp]
theorem ofTailAlgHom_apply (f : TateAlgebra K n) : ofTailAlgHom K n f = ofTail K n f :=
  rfl

section Normalisation

variable {A : Type*} [CommRing A] [Algebra K A]

omit [Algebra K A] in
/-- The Weierstrass finiteness theorem for a distinguished element of the kernel: a finite ring
homomorphism out of `T_{n+1}` killing an `X 0`-distinguished series restricts to a finite
homomorphism on `Tₙ`. Source: BGR 6.1.2/1 ("`α` induces a finite homomorphism `ᾱ : Tₙ/ωTₙ → A`.
By the Weierstrass Finiteness Theorem 5.2.3/4, the natural injection `T_{n−1} → Tₙ` induces a
finite monomorphism `β : T_{n−1} → Tₙ/ωTₙ`. Obviously, `ᾱ ∘ β` is finite"). -/
theorem finite_comp_ofTail_of_isMulDistinguishedX0 (φ : TateAlgebra K (n + 1) →+* A)
    (hφ : φ.Finite) {g : TateAlgebra K (n + 1)} {s : ℕ} (hg : IsMulDistinguishedX0 g s)
    (h0 : φ g = 0) : (φ.comp (ofTail K n)).Finite := by
  have hle : Ideal.span {g} ≤ RingHom.ker φ := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact h0
  let φ' := Ideal.Quotient.lift (Ideal.span {g}) φ fun a ha ↦ hle ha
  have hφ' : φ = φ'.comp (Ideal.Quotient.mk _) := (Ideal.Quotient.lift_comp_mk _ _ _).symm
  have hfin : φ'.Finite := by
    rw [hφ'] at hφ
    exact RingHom.Finite.of_comp_finite hφ
  rw [hφ', RingHom.comp_assoc]
  exact hfin.comp (finite_mk_comp_ofTail_of_isMulDistinguishedX0 hg)

omit [CompleteSpace K] in
/-- The map `Tₙ → T_{n+1} ⧸ (g)` is injective for an `X 0`-distinguished `g`: a series without
`X 0` that is a multiple of `g` has two Weierstrass divisions by `g`, with remainders itself and
`0`.
Source: BGR 6.1.2/1 ("the natural injection `T_{n−1} → Tₙ` induces a finite monomorphism
`β : T_{n−1} → Tₙ/ωTₙ`"), via `weierstrassDivision_r_unique`. -/
theorem injective_mk_comp_ofTail_of_isMulDistinguishedX0 {g : TateAlgebra K (n + 1)} {s : ℕ}
    (hg : IsMulDistinguishedX0 g s) (hs : s ≠ 0) :
    Function.Injective ((Ideal.Quotient.mk (Ideal.span {g})).comp (ofTail K n)) := by
  refine (injective_iff_map_eq_zero _).2 fun f hf ↦ ?_
  rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at hf
  obtain ⟨q, hq⟩ := hf
  have hs' : (0 : WithBot ℕ) < s := by exact_mod_cast Nat.pos_of_ne_zero hs
  have h₁ : ofTail K n f = g * q + ofPolynomial K n 0 := by
    rw [map_zero, add_zero, mul_comm, hq]
  have h₂ : ofTail K n f = g * 0 + ofPolynomial K n (Polynomial.C f) := by
    rw [mul_zero, zero_add, ofTail_apply]
  have hr := weierstrassDivision_r_unique hg
    (by rw [Polynomial.degree_zero]; exact WithBot.bot_lt_coe s) h₁
    (Polynomial.degree_C_le.trans_lt hs') h₂
  exact Polynomial.C_eq_zero.1 hr.symm

/-- The induction step of BGR 6.1.2/1: a finite `β : T_{n+1} → A` with a nonzero element in its
kernel becomes, after a shear, finite on `Tₙ`. Source: BGR 6.1.2/1 ("Otherwise we can find a chart
`{X₁, …, Xₙ}` of `Tₙ` and a Weierstrass polynomial `ω ∈ T_{n−1}[Xₙ]` such that `ω ∈ ker α`"). -/
theorem exists_finite_comp_shear_symm_comp_ofTail (β : TateAlgebra K (n + 1) →ₐ[K] A)
    (hβ : β.toRingHom.Finite) {f : TateAlgebra K (n + 1)} (hf : f ≠ 0) (h0 : β f = 0) :
    ∃ e : Fin n → ℕ,
      ((β.comp (shear K n e).symm.toAlgHom).comp (ofTailAlgHom K n)).toRingHom.Finite := by
  obtain ⟨e, s, hs⟩ := exists_shear_isMulDistinguishedX0 hf
  refine ⟨e, ?_⟩
  have hβ' : (β.comp (shear K n e).symm.toAlgHom).toRingHom.Finite :=
    hβ.comp (RingHom.Finite.of_surjective _ (shear K n e).symm.surjective)
  have h0' : (β.comp (shear K n e).symm.toAlgHom).toRingHom (shear K n e f) = 0 := by
    simp [h0]
  exact finite_comp_ofTail_of_isMulDistinguishedX0 _ hβ' hs h0'

omit [CompleteSpace K] in
/-- A `K`-algebra homomorphism out of `T₀ = K` into a nonzero algebra is injective.
Source: BGR 6.1.2/1 ("The case `n = 0` is trivial"). -/
theorem injective_of_nontrivial [Nontrivial A] (β : TateAlgebra K 0 →ₐ[K] A) :
    Function.Injective β := by
  set e := Restricted.isEmptyEquiv K (1 : Fin 0 → ℝ)
  have h : Function.Injective (β.toRingHom.comp e.symm.toRingHom) := RingHom.injective _
  intro a b hab
  refine e.injective (h ?_)
  simpa using hab

/-- **BGR 6.1.2/1 (i)**: for a finite `K`-algebra homomorphism `β : Tₙ → A` into a nonzero
algebra there are `d ≤ n` and a `K`-algebra homomorphism `ψ : T_d → Tₙ` (a chart followed by the
inclusion of the last `d` variables) such that `β ∘ ψ` is finite and injective. Source: BGR 6.1.2/1
("there exist a chart `{X₁, …, Xₙ}` of `Tₙ` and an integer `d ≥ 0` such that `α | k⟨X₁, …, X_d⟩`
is finite and injective"), by induction on `n`. -/
theorem exists_finite_injective_comp [Nontrivial A] (n : ℕ) (β : TateAlgebra K n →ₐ[K] A)
    (hβ : β.toRingHom.Finite) :
    ∃ d ≤ n, ∃ ψ : TateAlgebra K d →ₐ[K] TateAlgebra K n,
      (β.comp ψ).toRingHom.Finite ∧ Function.Injective (β.comp ψ) := by
  induction n with
  | zero =>
    exact ⟨0, le_rfl, AlgHom.id K _, by simpa using hβ, by simpa using injective_of_nontrivial β⟩
  | succ n ih =>
    by_cases hker : RingHom.ker β.toRingHom = ⊥
    · exact ⟨n + 1, le_rfl, AlgHom.id K _, by simpa using hβ,
        by simpa using (RingHom.injective_iff_ker_eq_bot _).2 hker⟩
    · obtain ⟨f, hf, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
      obtain ⟨e, hfin⟩ := exists_finite_comp_shear_symm_comp_ofTail β hβ hf0 hf
      obtain ⟨d, hd, ψ', hfin', hinj'⟩ := ih _ hfin
      refine ⟨d, hd.trans (Nat.le_succ n),
        ((shear K n e).symm.toAlgHom.comp (ofTailAlgHom K n)).comp ψ', ?_, ?_⟩
      · rw [← AlgHom.comp_assoc, ← AlgHom.comp_assoc]
        exact hfin'
      · rw [← AlgHom.comp_assoc, ← AlgHom.comp_assoc]
        exact hinj'

end Normalisation

end Affinoid.TateAlgebra

namespace IsAffinoidAlgebra

open Affinoid

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : Type*} [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]

/-- **BGR 6.1.2/1 (ii)**: a finite homomorphism `φ : B → A` of affinoid algebras with `A ≠ 0`
admits `ψ : T_d → B` with `φ ∘ ψ` finite and injective. Source: BGR 6.1.2/1 ("By choosing an
epimorphism `α : Tₙ → B` and applying the first statement to the map `φ ∘ α : Tₙ → A`"). -/
theorem exists_finite_injective_comp (hB : IsAffinoidAlgebra K B) [Nontrivial A]
    (φ : B →ₐ[K] A) (hφ : φ.toRingHom.Finite) :
    ∃ (d : ℕ) (ψ : TateAlgebra K d →ₐ[K] B),
      (φ.comp ψ).toRingHom.Finite ∧ Function.Injective (φ.comp ψ) := by
  obtain ⟨n, α, hα⟩ := hB
  have hfin : (φ.comp α).toRingHom.Finite := hφ.comp (RingHom.Finite.of_surjective _ hα)
  obtain ⟨d, -, ψ, h₁, h₂⟩ := Affinoid.TateAlgebra.exists_finite_injective_comp n (φ.comp α) hfin
  exact ⟨d, α.comp ψ, by rwa [← AlgHom.comp_assoc], by rwa [← AlgHom.comp_assoc]⟩

/-- **Noether normalisation** (BGR 6.1.2/2; Bosch 1.2/10, 1.4/2): every nonzero affinoid algebra
is a finite extension of some Tate algebra `T_d`. -/
theorem exists_finite_injective (hA : IsAffinoidAlgebra K A) [Nontrivial A] :
    ∃ (d : ℕ) (φ : TateAlgebra K d →ₐ[K] A), φ.toRingHom.Finite ∧ Function.Injective φ := by
  obtain ⟨d, ψ, h₁, h₂⟩ := hA.exists_finite_injective_comp (AlgHom.id K A) (RingHom.Finite.id A)
  exact ⟨d, ψ, by simpa using h₁, by simpa using h₂⟩

end IsAffinoidAlgebra

/-! ### The Krull dimension of an affinoid algebra -/

/-- Going up: an injective integral ring homomorphism does not lower the Krull dimension, since
every chain of primes lifts (`Ideal.exists_ltSeries_of_hasGoingUp`). Source: BGR 6.1.2 (Remark),
citing Nagata, Corollary 10.10, for `dim A = dim T_d`. -/
theorem ringKrullDim_le_of_isIntegral_of_injective {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.IsIntegral) (hinj : Function.Injective f) :
    ringKrullDim R ≤ ringKrullDim S := by
  letI := f.toAlgebra
  haveI : Algebra.IsIntegral R S := ⟨hf⟩
  refine iSup_le fun l ↦ ?_
  obtain ⟨P, -, hP, hPl⟩ := Ideal.exists_ideal_over_prime_of_isIntegral l.head.asIdeal (⊥ : Ideal S)
    ((Ideal.comap_bot_of_injective _ hinj).trans_le bot_le)
  haveI : P.LiesOver l.head.asIdeal := ⟨hPl.symm⟩
  obtain ⟨L, hL, -⟩ := Ideal.exists_ltSeries_of_hasGoingUp l P
  rw [← hL]
  exact Order.LTSeries.length_le_krullDim L

namespace IsAffinoidAlgebra

open Affinoid

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : Type*} [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]

/-- The integer `d` of a Noether normalisation is the Krull dimension: `dim A = dim T_d = d`.
Source: BGR 6.1.2 (Remark). -/
theorem ringKrullDim_eq_of_finite_injective {d : ℕ} (φ : TateAlgebra K d →ₐ[K] A)
    (hφ : φ.toRingHom.Finite) (hinj : Function.Injective φ) : ringKrullDim A = d := by
  rw [← TateAlgebra.ringKrullDim_eq K d]
  exact le_antisymm (ringKrullDim_le_of_isIntegral φ.toRingHom hφ.to_isIntegral)
    (ringKrullDim_le_of_isIntegral_of_injective φ.toRingHom hφ.to_isIntegral hinj)

/-- The Krull dimension of a nonzero affinoid algebra is a natural number, the `d` of any Noether
normalisation. Source: BGR 6.1.2 (Remark) ("the integer `d` above is uniquely determined by the
algebra `A`"). -/
theorem exists_ringKrullDim_eq (hA : IsAffinoidAlgebra K A) [Nontrivial A] :
    ∃ d : ℕ, ringKrullDim A = d := by
  obtain ⟨d, φ, hφ, hinj⟩ := hA.exists_finite_injective
  exact ⟨d, ringKrullDim_eq_of_finite_injective φ hφ hinj⟩

/-! ### Residue rings are finite-dimensional (BGR 6.1.2/3) -/

omit [CompleteSpace K] in
/-- Finite over `T₀` means finite-dimensional over `K`. -/
theorem finiteDimensional_of_finite_zero (φ : TateAlgebra K 0 →ₐ[K] A) (hφ : φ.toRingHom.Finite) :
    FiniteDimensional K A := by
  letI := φ.toRingHom.toAlgebra
  haveI : Module.Finite (TateAlgebra K 0) A := hφ
  haveI : IsScalarTower K (TateAlgebra K 0) A :=
    IsScalarTower.of_algebraMap_eq fun c ↦ (φ.commutes c).symm
  haveI : Module.Finite K (TateAlgebra K 0) := by
    refine Module.Finite.of_surjective (Algebra.linearMap K (TateAlgebra K 0)) fun f ↦
      ⟨Restricted.isEmptyEquiv K (1 : Fin 0 → ℝ) f,
        (Restricted.isEmptyEquiv K (1 : Fin 0 → ℝ)).injective ?_⟩
    simp [Restricted.isEmptyEquiv_apply, Restricted.algebraMap_apply]
  exact Module.Finite.trans (TateAlgebra K 0) A

/-- An injective homomorphism out of a reduced ring stays injective after passing to the quotient
by the radical of an ideal containing nothing of the image. Source: BGR 6.1.2/3 ("The composition
of `φ` with the canonical epimorphism `ϱ : A/𝔮 → A/rad 𝔮` is finite and injective (because `T_d`
is reduced)"). -/
theorem injective_factor_comp_of_injective {R : Type*} [CommRing R] [IsReduced R]
    (𝔮 : Ideal A) (φ : R →+* A ⧸ 𝔮) (hφ : Function.Injective φ) :
    Function.Injective ((Ideal.Quotient.factor 𝔮.le_radical).comp φ) := by
  refine (injective_iff_map_eq_zero _).2 fun r hr ↦ ?_
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (φ r)
  rw [RingHom.comp_apply, ← ha, Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem] at hr
  obtain ⟨m, hm⟩ := hr
  have hrm : φ (r ^ m) = 0 := by
    rw [map_pow, ← ha, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact hm
  exact IsReduced.eq_zero r ⟨m, hφ (hrm.trans (map_zero φ).symm)⟩

/-- A Tate algebra that is a field has no variables: `d = 0`. Source: BGR 6.1.2/3 ("But then
`T_d` must itself be a field so that `d = 0`"), via `ringKrullDim_eq` and
`ringKrullDim_eq_zero_of_isField`. -/
theorem _root_.Affinoid.TateAlgebra.eq_zero_of_isField {d : ℕ} (h : IsField (TateAlgebra K d)) :
    d = 0 := by
  have h1 := ringKrullDim_eq_zero_of_isField h
  rw [TateAlgebra.ringKrullDim_eq K d] at h1
  exact_mod_cast h1

/-- **BGR 6.1.2/3**: if the radical of an ideal `𝔮` of an affinoid algebra `A` is maximal, then
`A ⧸ 𝔮` is a finite-dimensional `K`-vector space. Source: BGR 6.1.2/3; Bosch 1.4/3. -/
theorem finiteDimensional_quotient_of_radical_isMaximal (hA : IsAffinoidAlgebra K A)
    (𝔮 : Ideal A) (h : 𝔮.radical.IsMaximal) : FiniteDimensional K (A ⧸ 𝔮) := by
  haveI : Nontrivial (A ⧸ 𝔮) :=
    Ideal.Quotient.nontrivial_iff.2 fun h𝔮 ↦ h.ne_top (by rw [h𝔮, Ideal.radical_top])
  obtain ⟨d, φ, hφ, hinj⟩ := (hA.quotient 𝔮).exists_finite_injective
  let ψ := (Ideal.Quotient.factor 𝔮.le_radical).comp φ.toRingHom
  have hψint : ψ.IsIntegral :=
    ((RingHom.Finite.of_surjective _ (Ideal.Quotient.factor_surjective 𝔮.le_radical)).comp
      hφ).to_isIntegral
  letI := ψ.toAlgebra
  haveI : Algebra.IsIntegral (TateAlgebra K d) (A ⧸ 𝔮.radical) := ⟨hψint⟩
  have hfield : IsField (TateAlgebra K d) :=
    isField_of_isIntegral_of_isField (injective_factor_comp_of_injective 𝔮 φ.toRingHom hinj)
      ((Ideal.Quotient.maximal_ideal_iff_isField_quotient _).1 h)
  obtain rfl := TateAlgebra.eq_zero_of_isField hfield
  exact finiteDimensional_of_finite_zero φ hφ

/-- The residue field of a maximal ideal of an affinoid algebra is a finite extension of `K`.
Source: BGR 6.1.2/3; Bosch 1.2/11. -/
theorem finiteDimensional_quotient_of_isMaximal (hA : IsAffinoidAlgebra K A) (𝔪 : Ideal A)
    [𝔪.IsMaximal] : FiniteDimensional K (A ⧸ 𝔪) :=
  hA.finiteDimensional_quotient_of_radical_isMaximal 𝔪
    (by rwa [(Ideal.IsMaximal.isPrime ‹_›).radical])

/-- `A ⧸ 𝔪^ν` is finite-dimensional for a maximal ideal `𝔪` and `ν ≥ 1`. Source: BGR 6.1.3
("We have `dim_k B/𝔟 < ∞` for all `𝔟 ∈ 𝔅` by Corollary 6.1.2/3"). -/
theorem finiteDimensional_quotient_pow (hA : IsAffinoidAlgebra K A) (𝔪 : Ideal A) [𝔪.IsMaximal]
    {ν : ℕ} (hν : ν ≠ 0) : FiniteDimensional K (A ⧸ 𝔪 ^ ν) :=
  hA.finiteDimensional_quotient_of_radical_isMaximal (𝔪 ^ ν)
    (by rwa [Ideal.radical_pow 𝔪 hν, (Ideal.IsMaximal.isPrime ‹_›).radical])

/-- The preimage of a maximal ideal of an affinoid algebra under a `K`-algebra homomorphism is
maximal: `A ⧸ φ⁻¹ 𝔪` is a domain finite-dimensional over `K`, hence a field.
Source: roadmap §1.2.4 ("the preimage of a maximal ideal under a `K`-algebra map of affinoid
algebras is maximal"); BGR 6.1.2/3. -/
theorem _root_.Ideal.isMaximal_comap_of_isAffinoidAlgebra (hB : IsAffinoidAlgebra K B)
    (φ : A →ₐ[K] B) (𝔪 : Ideal B) [𝔪.IsMaximal] : (𝔪.comap φ).IsMaximal := by
  haveI := hB.finiteDimensional_quotient_of_isMaximal 𝔪
  have hinj : Function.Injective (Ideal.quotientMapₐ 𝔪 φ le_rfl) := by
    refine (injective_iff_map_eq_zero _).2 fun a ha ↦ ?_
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [Ideal.quotient_map_mkₐ, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem] at ha
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_comap.2 ha)
  haveI : FiniteDimensional K (A ⧸ 𝔪.comap φ) :=
    FiniteDimensional.of_injective (Ideal.quotientMapₐ 𝔪 φ le_rfl).toLinearMap hinj
  exact Ideal.Quotient.maximal_of_isField _ (isField_of_isIntegral_of_isField' (Field.toIsField K))

/-! ### Affinoid domains are Japanese (BGR 6.1.2/4) -/

/-- For an injective integral extension `R → S` of domains, the fraction field of `S` is the
localisation of `S` at the nonzero elements of `R`: every nonzero `s ∈ S` divides a nonzero element
of `R` (the constant term of a minimal integral equation). Source: BGR 6.1.2/4 ("`Q(A′)` is finite
over `Q(T_d)`"), the identification needed to apply `Module.Finite.of_isLocalization`. This is
mathlib's instance for algebraic extensions, once injectivity supplies `FaithfulSMul R S` and the
nontriviality of `R`. -/
theorem _root_.IsFractionRing.isLocalization_algebraMapSubmonoid_of_isIntegral (R S : Type*)
    [CommRing R] [CommRing S] [IsDomain S] [Algebra R S] [Algebra.IsIntegral R S]
    (hinj : Function.Injective (algebraMap R S)) :
    IsLocalization (Algebra.algebraMapSubmonoid S (nonZeroDivisors R)) (FractionRing S) := by
  haveI := (faithfulSMul_iff_algebraMap_injective R S).2 hinj
  haveI := (algebraMap R S).domain_nontrivial
  infer_instance

/-- The fraction field of a domain finite over a domain `R` is finite over the fraction field of
`R`. Source: BGR 6.1.2/4 ("`Q(A′)` is finite over `Q(T_d)`"). -/
theorem _root_.FractionRing.finiteDimensional_of_finite (R S : Type*) [CommRing R] [IsDomain R]
    [CommRing S] [IsDomain S] [Algebra R S] [Module.Finite R S]
    (hinj : Function.Injective (algebraMap R S)) [Algebra (FractionRing R) (FractionRing S)]
    [IsScalarTower R (FractionRing R) (FractionRing S)] :
    FiniteDimensional (FractionRing R) (FractionRing S) := by
  haveI := IsFractionRing.isLocalization_algebraMapSubmonoid_of_isIntegral R S hinj
  exact Module.Finite.of_isLocalization R S (nonZeroDivisors R)

/-- **BGR 6.1.2/4**: an affinoid integral domain is Japanese, in characteristic zero (where
`T_d` is Japanese by Layer 0). Source: BGR 6.1.2/4 ("there is a normalization map `φ : T_d → A` …
Since `T_d` is Japanese by Theorem 5.3.1/3, we see that `A'` is a finite `T_d`-module and a
fortiori a finite `A`-module"). -/
theorem isJapaneseRing {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [CharZero K] {A : Type u} [CommRing A] [Algebra K A] [IsDomain A]
    (hA : IsAffinoidAlgebra K A) : IsJapaneseRing A := by
  intro L _ _ _ _ _
  obtain ⟨d, φ, hφ, hinj⟩ := hA.exists_finite_injective
  letI : Algebra (TateAlgebra K d) A := φ.toRingHom.toAlgebra
  haveI : Module.Finite (TateAlgebra K d) A := hφ
  letI : Algebra (TateAlgebra K d) L := ((algebraMap A L).comp φ.toRingHom).toAlgebra
  haveI : IsScalarTower (TateAlgebra K d) A L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have hAL : Function.Injective (algebraMap A L) := by
    rw [IsScalarTower.algebraMap_eq A (FractionRing A) L]
    exact (algebraMap (FractionRing A) L).injective.comp
      (IsFractionRing.injective A (FractionRing A))
  haveI : FaithfulSMul (TateAlgebra K d) L :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (hAL.comp hinj)
  haveI : FaithfulSMul (TateAlgebra K d) (FractionRing A) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (by
      rw [IsScalarTower.algebraMap_eq (TateAlgebra K d) A (FractionRing A)]
      exact (IsFractionRing.injective A (FractionRing A)).comp hinj)
  letI : Algebra (FractionRing (TateAlgebra K d)) L := FractionRing.liftAlgebra _ L
  letI : Algebra (FractionRing (TateAlgebra K d)) (FractionRing A) :=
    FractionRing.liftAlgebra _ (FractionRing A)
  haveI : FiniteDimensional (FractionRing (TateAlgebra K d)) (FractionRing A) :=
    FractionRing.finiteDimensional_of_finite _ A hinj
  haveI : IsScalarTower (FractionRing (TateAlgebra K d)) (FractionRing A) L := by
    refine IsScalarTower.of_algebraMap_eq'
      (IsLocalization.ringHom_ext (nonZeroDivisors (TateAlgebra K d)) ?_)
    rw [RingHom.comp_assoc,
      ← IsScalarTower.algebraMap_eq (TateAlgebra K d) (FractionRing (TateAlgebra K d)) L,
      ← IsScalarTower.algebraMap_eq (TateAlgebra K d) (FractionRing (TateAlgebra K d))
        (FractionRing A),
      IsScalarTower.algebraMap_eq (TateAlgebra K d) A (FractionRing A), ← RingHom.comp_assoc,
      ← IsScalarTower.algebraMap_eq A (FractionRing A) L,
      ← IsScalarTower.algebraMap_eq (TateAlgebra K d) A L]
  haveI : FiniteDimensional (FractionRing (TateAlgebra K d)) L :=
    Module.Finite.trans (FractionRing A) L
  haveI := Affinoid.TateAlgebra.isJapaneseRing K d L
  let f : integralClosure (TateAlgebra K d) L →ₗ[TateAlgebra K d] integralClosure A L :=
    { toFun x := ⟨x.1, x.2.tower_top⟩
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  haveI : Module.Finite (TateAlgebra K d) (integralClosure A L) :=
    Module.Finite.of_surjective f fun y ↦
      ⟨⟨y.1, isIntegral_trans (R := TateAlgebra K d) y.1 y.2⟩, rfl⟩
  exact Module.Finite.of_restrictScalars_finite (TateAlgebra K d) A (integralClosure A L)

end IsAffinoidAlgebra
