/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.Analysis.Normed.Operator.Banach
import PhD.TauCeti.Code.PadicFunctionalAnalysis.PowerBounded
import PhD.TauCeti.Code.RigidAnalyticGeometry.Affinoid.Basic
import PhD.TauCeti.Code.RigidAnalyticGeometry.Restricted.Sum

/-!
# The universal property of `A⟨X₁, …, Xₘ⟩` and affinoid generating systems

For a normed `K`-algebra `A` the ring `A⟨X⟩ = Restricted A 1` of strictly convergent power series
over `A` is a normed `K`-algebra, and a continuous `K`-algebra homomorphism `φ : A → B` into a
`K`-Banach algebra together with power-bounded elements `b i ∈ B` extends uniquely to a continuous
`K`-algebra homomorphism `A⟨X⟩ → B` with `X i ↦ b i` (BGR 6.1.1/4; Bosch 1.4, Lemma 18). A system
`b` for which the extension is surjective is an *affinoid generating system* of `B` over `A`
(BGR 6.1.1, p. 223, and 7.2.5); a continuous finite homomorphism out of a Tate algebra produces one,
so that its target is affinoid (BGR 6.1.1/5).

Roadmap: `PhD/TauCeti/Roadmaps/RigidAnalyticGeometry/README.md`, §1.1.3. Tau Ceti home:
`TauCeti/RingTheory/Affinoid/Extend.lean`.

## Main definitions and results

* `MvPowerSeries.Restricted.extendAlgHom` — the extension `A⟨X⟩ → B` of BGR 6.1.1/4, with
  `extendAlgHom_C`, `extendAlgHom_X`, `continuous_extendAlgHom` and the uniqueness
  `extendAlgHom_unique`.
* `MvPowerSeries.Restricted.IsAffinoidGeneratingSystem` — affinoid generating systems over `A`
  (BGR 7.2.5).
* `IsAffinoidAlgebra.of_isAffinoidGeneratingSystem_tateAlgebra`,
  `IsAffinoidAlgebra.of_finite_tateAlgebra` — BGR 6.1.1/5 for the source `Tₙ`; the version for an
  arbitrary affinoid source is `IsAffinoidAlgebra.of_finite_of_continuous` in
  `Affinoid/Continuity.lean`, since it needs the continuity of presentations.
* `MvPowerSeries.Restricted.mapAlgHom`, `coeff_mapAlgHom`, `surjective_mapAlgHom_of_surjective` —
  functoriality of `A⟨X⟩` in `A`, coefficientwise, surjective along a surjection (Banach's
  theorem, BGR 6.1.1/9).
-/

open Filter Topology PowerBounded

namespace MvPowerSeries.Restricted

/-! ### `A⟨X⟩` as a normed `K`-algebra -/

section NormedAlgebra

variable {K : Type*} [NormedField K] {A : Type*} [NormedCommRing A] [NormedAlgebra K A]
  [IsUltrametricDist A] {σ : Type*} (c : σ → ℝ) [Fact (∀ i, 0 < c i)]

/-- Scalars of `K` scale the Gauss norm of `Restricted A c` by at most their norm. -/
theorem norm_smul_le_of_normedAlgebra (k : K) (f : Restricted A c) : ‖k • f‖ ≤ ‖k‖ * ‖f‖ := by
  refine (norm_le_iff c _).2 fun t ↦ ?_
  have hcoeff : coeff t (k • f).1 = k • coeff t f.1 := rfl
  have hprod : 0 ≤ t.prod (c · ^ ·) :=
    Finset.prod_nonneg fun i _ ↦ pow_nonneg (Fact.out (p := ∀ i, 0 < c i) i).le _
  calc ‖coeff t (k • f).1‖ * t.prod (c · ^ ·) = ‖k • coeff t f.1‖ * t.prod (c · ^ ·) := by
        rw [hcoeff]
    _ ≤ ‖k‖ * ‖coeff t f.1‖ * t.prod (c · ^ ·) :=
        mul_le_mul_of_nonneg_right (norm_smul_le _ _) hprod
    _ = ‖k‖ * (‖coeff t f.1‖ * t.prod (c · ^ ·)) := mul_assoc _ _ _
    _ ≤ ‖k‖ * ‖f‖ := mul_le_mul_of_nonneg_left (norm_coeff_mul_prod_le c f t) (norm_nonneg k)

/-- `Restricted A c` is a normed `K`-algebra whenever `A` is. Source: BGR 3.7.1 ("for every
`k`-Banach algebra `A`, the algebra `A⟨X⟩` … is a `k`-Banach algebra"). -/
noncomputable instance instNormedAlgebraOfNormedAlgebra : NormedAlgebra K (Restricted A c) where
  norm_smul_le := norm_smul_le_of_normedAlgebra c

/-- The variables of `A⟨X⟩` are power-bounded: `‖X i ^ k‖ = ‖1‖` for every `k ≥ 1`. -/
theorem isPowerBounded_X (i : σ) : IsPowerBounded (X A (1 : σ → ℝ) i) := by
  refine isPowerBounded_of_norm_pow_le (C := ‖(1 : A)‖) fun k ↦ ?_
  have h : X A (1 : σ → ℝ) i ^ k = monomial (1 : σ → ℝ) (Finsupp.single i k) 1 := by
    refine Restricted.ext ?_
    rw [val_pow, val_X, val_monomial, MvPowerSeries.X_pow_eq]
  rw [h, norm_monomial]
  simp

end NormedAlgebra

/-! ### The universal property of `A⟨X⟩` (BGR 6.1.1/4) -/

section Extend

variable {K : Type*} [NontriviallyNormedField K]
  {A : Type*} [NormedCommRing A] [NormedAlgebra K A] [IsUltrametricDist A]
  {B : Type*} [NormedCommRing B] [NormedAlgebra K B] [IsUltrametricDist B] [CompleteSpace B]
  {σ : Type*} [Finite σ]

omit [IsUltrametricDist A] [IsUltrametricDist B] [CompleteSpace B] in
/-- A continuous `K`-algebra homomorphism between normed `K`-algebras is bounded.
Source: BGR 3.7.1 ("such a map `φ` is continuous if and only if it is bounded"). -/
theorem exists_forall_norm_le_mul_of_continuous (φ : A →ₐ[K] B) (hφ : Continuous φ) :
    ∃ Cφ : ℝ, ∀ a, ‖φ a‖ ≤ Cφ * ‖a‖ :=
  let ⟨C, _, hC⟩ := SemilinearMapClass.bound_of_continuous φ hφ
  ⟨C, hC⟩

omit [IsUltrametricDist B] [CompleteSpace B] in
include K in
/-- The monomials in finitely many power-bounded elements are uniformly bounded.
Source: BGR 6.1.1/4 ("Since `fᵢ ∈ Å` and `lim a_ν = 0`, the series … represents a well-defined
element of `A`"). -/
theorem exists_forall_norm_prod_pow_le_of_isPowerBounded {b : σ → B}
    (hb : ∀ i, IsPowerBounded (b i)) :
    ∃ Cx : ℝ, ∀ t : σ →₀ ℕ, ‖t.prod fun i k ↦ b i ^ k‖ ≤ Cx * t.prod ((1 : σ → ℝ) · ^ ·) :=
  exists_forall_norm_prod_pow_le b fun i ↦ (hb i).exists_norm_pow_le K

variable (φ : A →ₐ[K] B) (hφ : Continuous φ) (b : σ → B) (hb : ∀ i, IsPowerBounded (b i))

/-- **The universal property of `A⟨X⟩`**: the continuous `K`-algebra homomorphism `A⟨X⟩ → B`
extending `φ` with `X i ↦ b i`, namely `Σ a_ν X^ν ↦ Σ φ(a_ν) b^ν`. Source: BGR 6.1.1/4;
Bosch 1.4, Lemma 18. -/
noncomputable def extendAlgHom : Restricted A (1 : σ → ℝ) →ₐ[K] B :=
  { eval₂ (1 : σ → ℝ) φ.toRingHom b (exists_forall_norm_le_mul_of_continuous φ hφ).choose_spec
      (exists_forall_norm_prod_pow_le_of_isPowerBounded (K := K) hb).choose_spec with
    commutes' := fun r ↦ by
      change eval₂ (1 : σ → ℝ) φ.toRingHom b _ _ (algebraMap K (Restricted A (1 : σ → ℝ)) r) = _
      rw [algebraMap_eq_C_comp, RingHom.comp_apply, eval₂_C]
      exact φ.commutes r }

theorem extendAlgHom_apply (f : Restricted A (1 : σ → ℝ)) :
    extendAlgHom φ hφ b hb f = ∑' t : σ →₀ ℕ, φ (coeff t f.1) * t.prod fun i k ↦ b i ^ k :=
  rfl

/-- The extension restricts to `φ` on the constants: `Φ | B = φ`. Source: BGR 6.1.1/4. -/
@[simp]
theorem extendAlgHom_C (a : A) : extendAlgHom φ hφ b hb (C (1 : σ → ℝ) a) = φ a :=
  eval₂_C (exists_forall_norm_le_mul_of_continuous φ hφ).choose_spec
    (exists_forall_norm_prod_pow_le_of_isPowerBounded (K := K) hb).choose_spec a

/-- The extension sends the variables to the given elements: `Φ(Xᵢ) = fᵢ`.
Source: BGR 6.1.1/4. -/
@[simp]
theorem extendAlgHom_X (i : σ) : extendAlgHom φ hφ b hb (X A (1 : σ → ℝ) i) = b i :=
  eval₂_X (exists_forall_norm_le_mul_of_continuous φ hφ).choose_spec
    (exists_forall_norm_prod_pow_le_of_isPowerBounded (K := K) hb).choose_spec i

/-- The extension restricts to `φ` on the constants, as `K`-algebra homomorphisms. -/
theorem extendAlgHom_comp_toAlgHom :
    (extendAlgHom φ hφ b hb).comp (IsScalarTower.toAlgHom K A (Restricted A (1 : σ → ℝ))) = φ := by
  refine AlgHom.ext fun a ↦ ?_
  rw [AlgHom.comp_apply, IsScalarTower.toAlgHom_apply, algebraMap_apply, extendAlgHom_C]

/-- The extension is continuous. Source: BGR 6.1.1/4. -/
theorem continuous_extendAlgHom : Continuous (extendAlgHom φ hφ b hb) :=
  continuous_eval₂ (exists_forall_norm_le_mul_of_continuous φ hφ).choose_spec
    (exists_forall_norm_prod_pow_le_of_isPowerBounded (K := K) hb).choose_spec

/-- The extension is bounded by the bounds of `φ` and of the monomials in `b`. -/
theorem exists_forall_norm_extendAlgHom_le :
    ∃ C : ℝ, ∀ f, ‖extendAlgHom φ hφ b hb f‖ ≤ C * ‖f‖ :=
  ⟨_, norm_eval₂_le_mul (exists_forall_norm_le_mul_of_continuous φ hφ).choose_spec
    (exists_forall_norm_prod_pow_le_of_isPowerBounded (K := K) hb).choose_spec⟩

/-- **Uniqueness** in BGR 6.1.1/4: a continuous `K`-algebra homomorphism `A⟨X⟩ → B` that restricts
to `φ` on the constants and sends `X i` to `b i` is the extension. Source: BGR 6.1.1/4 ("`Φ` is the
unique continuous extension of `φ`"), via `algHom_ext_of_continuous`. -/
theorem extendAlgHom_unique (ψ : Restricted A (1 : σ → ℝ) →ₐ[K] B) (hψ : Continuous ψ)
    (hC : ∀ a, ψ (C (1 : σ → ℝ) a) = φ a) (hX : ∀ i, ψ (X A (1 : σ → ℝ) i) = b i) :
    ψ = extendAlgHom φ hφ b hb := by
  refine AlgHom.coe_ringHom_injective (ringHom_ext_of_continuous hψ
    (continuous_extendAlgHom φ hφ b hb) (fun a ↦ ?_) fun i ↦ ?_)
  · change ψ (C _ a) = extendAlgHom φ hφ b hb (C _ a)
    rw [hC, extendAlgHom_C]
  · change ψ (X A _ i) = extendAlgHom φ hφ b hb (X A _ i)
    rw [hX, extendAlgHom_X]

include hφ hb in
/-- BGR 6.1.1/4 as an existence-and-uniqueness statement. -/
theorem existsUnique_extend :
    ∃! ψ : Restricted A (1 : σ → ℝ) →ₐ[K] B,
      Continuous ψ ∧ (∀ a, ψ (C (1 : σ → ℝ) a) = φ a) ∧ ∀ i, ψ (X A (1 : σ → ℝ) i) = b i :=
  ⟨extendAlgHom φ hφ b hb, ⟨continuous_extendAlgHom φ hφ b hb, extendAlgHom_C φ hφ b hb,
    extendAlgHom_X φ hφ b hb⟩, fun ψ ⟨h₁, h₂, h₃⟩ ↦ extendAlgHom_unique φ hφ b hb ψ h₁ h₂ h₃⟩

/-- When `A = K` and `‖b i‖ ≤ 1`, the extension is the evaluation homomorphism of Layer 0. -/
theorem extendAlgHom_ofId_eq_aeval [IsUltrametricDist K] (b : σ → B) (hb : ∀ i, ‖b i‖ ≤ 1)
    [NormOneClass B] :
    extendAlgHom (Algebra.ofId K B) (continuous_algebraMap K B) b
      (fun i ↦ isPowerBounded_of_norm_le_one (hb i)) =
      aeval (1 : σ → ℝ) b (fun i ↦ by simpa using hb i) :=
  algHom_ext_of_continuous (continuous_extendAlgHom _ _ _ _) (continuous_aeval _) fun i ↦
    (extendAlgHom_X _ _ _ _ i).trans (aeval_X _ i).symm

end Extend

/-! ### Affinoid generating systems (BGR 7.2.5) -/

section GeneratingSystem

variable {K : Type*} [NontriviallyNormedField K]
  {A : Type*} [NormedCommRing A] [NormedAlgebra K A] [IsUltrametricDist A]
  {B : Type*} [NormedCommRing B] [NormedAlgebra K B] [IsUltrametricDist B] [CompleteSpace B]
  {σ : Type*} [Finite σ]

/-- A system `b : σ → B` of elements is an **affinoid generating system** of `B` over `A` (along
the continuous homomorphism `φ : A → B`) if its elements are power-bounded and the extension
`A⟨X⟩ → B`, `X i ↦ b i`, is surjective. Source: BGR 7.2.5 ("A system `b = (b₁, …, bₙ)` of
power-bounded elements in `B` is called an affinoid generating system of `B` over `A` if the
continuous homomorphism `σ₁ : A⟨ζ₁, …, ζₙ⟩ → B` extending `σ` and mapping `ζᵢ` onto `bᵢ` … is
surjective"); BGR 6.1.1, p. 223, for `A = k`. -/
def IsAffinoidGeneratingSystem (φ : A →ₐ[K] B) (hφ : Continuous φ) (b : σ → B) : Prop :=
  ∃ hb : ∀ i, IsPowerBounded (b i), Function.Surjective (extendAlgHom φ hφ b hb)

/-- Elements `b` such that every element of `B` is `Σ φ(qᵢ) bᵢ` form an affinoid generating
system once they are power-bounded. Source: BGR 6.1.1/5 ("Then `Φ` is surjective"). -/
theorem isAffinoidGeneratingSystem_of_forall_exists_sum [Fintype σ] (φ : A →ₐ[K] B)
    (hφ : Continuous φ) {b : σ → B} (hb : ∀ i, IsPowerBounded (b i))
    (hgen : ∀ y : B, ∃ q : σ → A, y = ∑ i, φ (q i) * b i) :
    IsAffinoidGeneratingSystem φ hφ b := by
  refine ⟨hb, fun y ↦ ?_⟩
  obtain ⟨q, rfl⟩ := hgen y
  refine ⟨∑ i, C (1 : σ → ℝ) (q i) * X A (1 : σ → ℝ) i, ?_⟩
  simp only [map_sum, map_mul, extendAlgHom_C, extendAlgHom_X]

omit [IsUltrametricDist B] [CompleteSpace B] [Finite σ] in
/-- In a normed algebra over a nontrivially normed field, finitely many elements can be rescaled
by one scalar into the unit ball. Source: BGR 6.1.1/5 ("We may assume `aᵢ ∈ Å`"). -/
theorem exists_forall_norm_smul_le_one [Fintype σ] (a : σ → B) :
    ∃ c : K, c ≠ 0 ∧ ∀ i, ‖c • a i‖ ≤ 1 := by
  obtain ⟨x, hx0, hx1⟩ := NormedField.exists_norm_lt_one K
  have hM0 : 0 ≤ ∑ i, ‖a i‖ := Finset.sum_nonneg fun i _ ↦ norm_nonneg _
  have hM1 : 0 < ∑ i, ‖a i‖ + 1 := by positivity
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (one_div_pos.2 hM1) hx1
  refine ⟨x ^ N, pow_ne_zero _ (norm_pos_iff.1 hx0), fun i ↦ ?_⟩
  have hai : ‖a i‖ ≤ ∑ i, ‖a i‖ + 1 :=
    (Finset.single_le_sum (fun j _ ↦ norm_nonneg (a j)) (Finset.mem_univ i)).trans
      (le_add_of_nonneg_right zero_le_one)
  calc ‖x ^ N • a i‖ ≤ ‖x ^ N‖ * ‖a i‖ := norm_smul_le _ _
    _ = ‖x‖ ^ N * ‖a i‖ := by rw [norm_pow]
    _ ≤ 1 / (∑ i, ‖a i‖ + 1) * (∑ i, ‖a i‖ + 1) :=
        mul_le_mul hN.le hai (norm_nonneg _) (one_div_pos.2 hM1).le
    _ = 1 := one_div_mul_cancel hM1.ne'

/-- A continuous finite homomorphism `φ : A → B` admits an affinoid generating system over `A`:
rescale the module generators into the unit ball. Source: BGR 6.1.1/5. -/
theorem exists_isAffinoidGeneratingSystem_of_finite (φ : A →ₐ[K] B) (hφ : Continuous φ)
    (hfin : φ.toRingHom.Finite) :
    ∃ (m : ℕ) (b : Fin m → B), IsAffinoidGeneratingSystem φ hφ b := by
  letI := φ.toRingHom.toAlgebra
  haveI : Module.Finite A B := hfin
  obtain ⟨m, a, ha⟩ := Module.Finite.exists_fin (R := A) (M := B)
  obtain ⟨c, hc0, hc⟩ := exists_forall_norm_smul_le_one (K := K) a
  refine ⟨m, fun i ↦ c • a i, isAffinoidGeneratingSystem_of_forall_exists_sum φ hφ
    (fun i ↦ isPowerBounded_of_norm_le_one (hc i)) fun y ↦ ?_⟩
  have hy : y ∈ Submodule.span A (Set.range a) := ha ▸ Submodule.mem_top
  obtain ⟨q, hq⟩ := (Submodule.mem_span_range_iff_exists_fun A).1 hy
  refine ⟨fun i ↦ c⁻¹ • q i, ?_⟩
  rw [← hq]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_smul, smul_mul_smul_comm, inv_mul_cancel₀ hc0, one_smul, Algebra.smul_def,
    RingHom.algebraMap_toAlgebra]
  rfl

end GeneratingSystem

/-! ### Functoriality of `A⟨X⟩` in `A` -/

section Map

variable {K : Type*} [NontriviallyNormedField K]
  {A : Type*} [NormedCommRing A] [NormedAlgebra K A] [IsUltrametricDist A]
  {B : Type*} [NormedCommRing B] [NormedAlgebra K B] [IsUltrametricDist B] [CompleteSpace B]
  {σ : Type*} [Finite σ]

omit [NontriviallyNormedField K] [NormedAlgebra K A] [Finite σ] in
/-- The constants `A → A⟨X⟩` form an isometry, hence are continuous. -/
theorem continuous_C (c : σ → ℝ) [Fact (∀ i, 0 < c i)] : Continuous (C (R := A) c) :=
  AddMonoidHomClass.continuous_of_bound (C c) 1 fun a ↦ by rw [norm_C, one_mul]

omit [NontriviallyNormedField K] [NormedAlgebra K A] [Finite σ] in
/-- The structure map `A → A⟨X⟩` is continuous (it is the constants). -/
theorem continuous_algebraMap_restricted (c : σ → ℝ) [Fact (∀ i, 0 < c i)] :
    Continuous (algebraMap A (Restricted A c)) := by
  have h : ⇑(algebraMap A (Restricted A c)) = ⇑(C (R := A) c) := funext (algebraMap_apply c)
  rw [h]
  exact continuous_C c

omit [NontriviallyNormedField K] [NormedAlgebra K A] [Finite σ] in
/-- The coefficient functionals of `A⟨X⟩` are continuous: `‖a_t‖ ≤ ‖f‖`. -/
theorem continuous_coeff (t : σ →₀ ℕ) :
    Continuous fun g : Restricted A (1 : σ → ℝ) ↦ coeff t g.1 := by
  let L : Restricted A (1 : σ → ℝ) →+ A :=
    { toFun := fun g ↦ coeff t g.1
      map_zero' := by simp
      map_add' := fun f g ↦ by simp }
  exact AddMonoidHomClass.continuous_of_bound L 1 fun g ↦ by
    rw [one_mul]
    exact norm_coeff_le g t

/-- A continuous `K`-algebra homomorphism `α : A → B` induces `A⟨X⟩ → B⟨X⟩`, coefficientwise.
Source: BGR 6.1.1/9 ("we get continuous epimorphisms `id_A ⊗̂ φ : A ⊗̂_k k⟨X⟩ → A ⊗̂_k B`"), via
the universal property 6.1.1/4. -/
noncomputable def mapAlgHom (α : A →ₐ[K] B) (hα : Continuous α) :
    Restricted A (1 : σ → ℝ) →ₐ[K] Restricted B (1 : σ → ℝ) :=
  extendAlgHom ((IsScalarTower.toAlgHom K B (Restricted B (1 : σ → ℝ))).comp α)
    ((continuous_algebraMap_restricted (A := B) (1 : σ → ℝ)).comp hα) (X B (1 : σ → ℝ))
    isPowerBounded_X

variable (α : A →ₐ[K] B) (hα : Continuous α)

@[simp]
theorem mapAlgHom_C (a : A) : mapAlgHom α hα (C (1 : σ → ℝ) a) = C (1 : σ → ℝ) (α a) :=
  (extendAlgHom_C _ _ _ _ a).trans (algebraMap_apply _ (α a))

@[simp]
theorem mapAlgHom_X (i : σ) : mapAlgHom α hα (X A (1 : σ → ℝ) i) = X B (1 : σ → ℝ) i :=
  extendAlgHom_X _ _ _ _ i

/-- `mapAlgHom` acts on the coefficients. -/
theorem coeff_mapAlgHom (f : Restricted A (1 : σ → ℝ)) (t : σ →₀ ℕ) :
    coeff t (mapAlgHom α hα f).1 = α (coeff t f.1) := by
  have hpoly : (mapAlgHom α hα).toRingHom.comp (MvPolynomial.toRestricted (1 : σ → ℝ)) =
      (MvPolynomial.toRestricted (1 : σ → ℝ)).comp (MvPolynomial.map α.toRingHom) :=
    MvPolynomial.ringHom_ext (fun a ↦ by simp [mapAlgHom_C]) fun i ↦ by simp [mapAlgHom_X]
  have hc1 : Continuous fun g : Restricted A (1 : σ → ℝ) ↦ coeff t (mapAlgHom α hα g).1 :=
    (continuous_coeff (A := B) t).comp (continuous_extendAlgHom _ _ _ _)
  have hc2 : Continuous fun g : Restricted A (1 : σ → ℝ) ↦ α (coeff t g.1) :=
    hα.comp (continuous_coeff (A := A) t)
  have h := (denseRange_toRestricted (R := A) (1 : σ → ℝ)).equalizer hc1 hc2 (funext fun p ↦ ?_)
  · exact congrFun h f
  · have hp := RingHom.congr_fun hpoly p
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at hp
    simp only [Function.comp_apply, hp, MvPolynomial.val_toRestricted, MvPolynomial.coeff_coe,
      MvPolynomial.coeff_map, RingHom.coe_coe]

theorem continuous_mapAlgHom : Continuous (mapAlgHom (σ := σ) α hα) :=
  continuous_extendAlgHom _ _ _ _

/-- A surjective continuous homomorphism of Banach algebras induces a surjection on strictly
convergent power series, by Banach's open mapping theorem: coefficients can be lifted with
controlled norms. Source: BGR 6.1.1/9 ("By BANACH's Theorem, `φ` is open and hence strict … we get
continuous epimorphisms `id_A ⊗̂ φ`"), through `ContinuousLinearMap.exists_preimage_norm_le`. -/
theorem surjective_mapAlgHom_of_surjective [CompleteSpace A] (hsurj : Function.Surjective α) :
    Function.Surjective (mapAlgHom (σ := σ) α hα) := by
  intro g
  let αL : A →L[K] B := ⟨α.toLinearMap, hα⟩
  obtain ⟨Cπ, -, hC⟩ := ContinuousLinearMap.exists_preimage_norm_le αL hsurj
  choose π hπ hnπ using hC
  refine ⟨⟨fun t ↦ π (coeff t g.1), isRestricted_mk (fun _ ↦ zero_le_one) π hnπ g.2⟩,
    Restricted.ext (MvPowerSeries.ext fun t ↦ ?_)⟩
  exact (coeff_mapAlgHom α hα _ t).trans (hπ _)

end Map

end MvPowerSeries.Restricted

namespace IsAffinoidAlgebra

open Affinoid MvPowerSeries MvPowerSeries.Restricted

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {B : Type*} [NormedCommRing B] [NormedAlgebra K B] [IsUltrametricDist B] [CompleteSpace B]

omit [CompleteSpace K] in
/-- A Banach algebra with an affinoid generating system over `K` is affinoid.
Source: BGR 6.1.1, p. 223 ("If `Φ` is surjective, we call the elements `f₁, …, fₙ` a system of
affinoid generators of `A`. In particular, `A` is a `k`-affinoid algebra"). The converse for the
given norm on `B` needs the continuity theorem and is `exists_isAffinoidGeneratingSystem` in
`Affinoid/Continuity.lean`. -/
theorem of_isAffinoidGeneratingSystem {n : ℕ} {b : Fin n → B}
    (hb : IsAffinoidGeneratingSystem (Algebra.ofId K B) (continuous_algebraMap K B) b) :
    IsAffinoidAlgebra K B := by
  obtain ⟨hb, hsurj⟩ := hb
  exact ⟨n, _, hsurj⟩

/-- A Banach algebra with an affinoid generating system over a Tate algebra is affinoid: compose
the extension `Tₙ⟨Y⟩ → B` with `T_{m+n} ≅ Tₙ⟨Y⟩`. Source: BGR 6.1.1/5 ("`Φ` is surjective, and
hence `A ∈ 𝔄`"). -/
theorem of_isAffinoidGeneratingSystem_tateAlgebra {n m : ℕ} (φ : TateAlgebra K n →ₐ[K] B)
    (hφ : Continuous φ) {b : Fin m → B} (hb : IsAffinoidGeneratingSystem φ hφ b) :
    IsAffinoidAlgebra K B := by
  obtain ⟨hb, hsurj⟩ := hb
  exact ⟨m + n, (extendAlgHom φ hφ b hb).comp (TateAlgebra.sumEquiv K n m).symm.toAlgHom,
    hsurj.comp (TateAlgebra.sumEquiv K n m).symm.surjective⟩

/-- **BGR 6.1.1/5 for the source `Tₙ`**: the target of a continuous finite `K`-algebra
homomorphism out of a Tate algebra into a Banach algebra is affinoid. -/
theorem of_finite_tateAlgebra {n : ℕ} (φ : TateAlgebra K n →ₐ[K] B) (hφ : Continuous φ)
    (hfin : φ.toRingHom.Finite) : IsAffinoidAlgebra K B := by
  obtain ⟨m, b, hb⟩ := exists_isAffinoidGeneratingSystem_of_finite φ hφ hfin
  exact of_isAffinoidGeneratingSystem_tateAlgebra φ hφ hb

end IsAffinoidAlgebra
