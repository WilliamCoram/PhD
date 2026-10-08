/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import PhD.TauCeti.Code.RigidAnalyticGeometry.SupSeminorm

/-!
# The supremum seminorm as a power-multiplicative algebra seminorm

Layer 2 of the RigidAnalyticGeometry roadmap, §2.1.1–§2.1.3 (BGR 3.8.1/3–5, 3.8.1/9).

BGR compute `|f|_sup` over the `k`-algebraic maximal ideals `Max_k A` and allow the value `∞`.
Our `Affinoid.supSeminorm` is a real `iSup` over all of `MaximalSpectrum A` (Layer 0), which is
junk when the family is unbounded and whose summands `evalNorm K x f` are `0` at a transcendental
point. The class `Affinoid.HasSupSeminorm K A` records BGR's standing hypotheses: every residue
field is algebraic over `K` and `|f|_sup` is finite. Under it, `|·|_sup` is a power-multiplicative
nonarchimedean `K`-algebra seminorm (BGR 3.8.1/3), every `K`-algebra homomorphism is a contraction
(3.8.1/4), and `|·|_sup` is computed modulo the minimal primes (3.8.1/5) and modulo the nilradical
(6.2.1/3).

## Main declarations

* `Affinoid.HasSupSeminorm K A`: algebraic residue fields + bounded point evaluations.
* `Affinoid.evalNorm_mul_le`, `evalNorm_add_le_max`, `evalNorm_pow`, `evalNorm_smul`,
  `evalNorm_eq_zero_iff`: the point evaluations are the spectral norms of the residue fields.
* `Affinoid.supSeminorm_mul_le`, `supSeminorm_add_le_max`, `supSeminorm_pow`, `supSeminorm_smul`,
  `Affinoid.supRingSeminorm`: BGR 3.8.1/3.
* `Affinoid.evalNorm_eq_of_asIdeal_eq_comap`, `Affinoid.comapPoint`, `Affinoid.evalNorm_comapPoint`,
  `Affinoid.supSeminorm_map_le`: BGR 3.8.1/4.
* `Affinoid.HasSupSeminorm.quotient`, `Affinoid.supSeminorm_mk_le`,
  `Affinoid.exists_minimalPrimes_supSeminorm_mk_eq`, `Affinoid.supSeminorm_mk_eq_of_le_jacobson`,
  `Affinoid.supSeminorm_mk_nilradical`: BGR 3.8.1/5 and 6.2.1/3.
* `Affinoid.supSeminorm_eq_zero_iff_forall_mem`, `supSeminorm_eq_zero_iff_mem_jacobson_bot`:
  BGR 3.8.1/9.
-/

open Ideal

namespace Affinoid

section Class

variable (K : Type*) [NormedField K] (A : Type*) [CommRing A] [Algebra K A]

/-- BGR's standing hypotheses for the supremum seminorm, as a class: every residue field
`A ⧸ x` is algebraic over `K` (so that every maximal ideal lies in BGR's `Max_k A`) and the point
evaluations `|f(x)|` are bounded (so that `|f|_sup` is finite, BGR 3.8.1 "we shall say that the
supremum semi-norm on `A` is finite if `f(Max_k A)` is bounded for all `f ∈ A`"). -/
class HasSupSeminorm : Prop where
  isAlgebraic : ∀ x : MaximalSpectrum A, Algebra.IsAlgebraic K (A ⧸ x.asIdeal)
  bddAbove : ∀ f : A, BddAbove (Set.range fun x : MaximalSpectrum A ↦ evalNorm K x f)

/-- The residue field at a point of an algebra with a supremum seminorm is algebraic over `K`. -/
instance HasSupSeminorm.instIsAlgebraic [HasSupSeminorm K A] (x : MaximalSpectrum A) :
    Algebra.IsAlgebraic K (A ⧸ x.asIdeal) :=
  HasSupSeminorm.isAlgebraic x

variable {A} in
/-- `|·|_sup` is nonnegative with no hypothesis: a real `iSup` of nonnegative terms. -/
theorem supSeminorm_nonneg (f : A) : 0 ≤ supSeminorm K f :=
  Real.iSup_nonneg fun x ↦ evalNorm_nonneg K x f

end Class

section Point

variable {K : Type*} [NormedField K] [IsUltrametricDist K] {A : Type*} [CommRing A] [Algebra K A]
  (x : MaximalSpectrum A) [Algebra.IsAlgebraic K (A ⧸ x.asIdeal)]

omit [IsUltrametricDist K] [Algebra.IsAlgebraic K (A ⧸ x.asIdeal)] in
/-- `|f(x)|` is the spectral norm of the residue class of `f` in the residue field `A ⧸ x`. -/
private theorem evalNorm_eq_spectralNorm (f : A) :
    evalNorm K x f = @spectralNorm K _ (A ⧸ x.asIdeal) (Ideal.Quotient.field x.asIdeal) _
      (Ideal.Quotient.mk x.asIdeal f) :=
  rfl

theorem evalNorm_mul_le (f g : A) : evalNorm K x (f * g) ≤ evalNorm K x f * evalNorm K x g := by
  letI := Ideal.Quotient.field x.asIdeal
  rw [evalNorm_eq_spectralNorm, evalNorm_eq_spectralNorm, evalNorm_eq_spectralNorm, map_mul]
  exact spectralNorm_mul (Algebra.IsAlgebraic.isAlgebraic _) (Algebra.IsAlgebraic.isAlgebraic _)

theorem evalNorm_add_le_max (f g : A) :
    evalNorm K x (f + g) ≤ max (evalNorm K x f) (evalNorm K x g) := by
  letI := Ideal.Quotient.field x.asIdeal
  rw [evalNorm_eq_spectralNorm, evalNorm_eq_spectralNorm, evalNorm_eq_spectralNorm, map_add]
  exact isNonarchimedean_spectralNorm _ _

omit [IsUltrametricDist K] [Algebra.IsAlgebraic K (A ⧸ x.asIdeal)] in
theorem evalNorm_one : evalNorm K x (1 : A) = 1 := by
  letI := Ideal.Quotient.field x.asIdeal
  rw [evalNorm_eq_spectralNorm, map_one]
  exact spectralNorm_one

theorem evalNorm_pow (f : A) (n : ℕ) : evalNorm K x (f ^ n) = evalNorm K x f ^ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [pow_zero, pow_zero, evalNorm_one]
  letI := Ideal.Quotient.field x.asIdeal
  rw [evalNorm_eq_spectralNorm, evalNorm_eq_spectralNorm, map_pow]
  exact isPowMul_spectralNorm _ hn

theorem evalNorm_smul (c : K) (f : A) : evalNorm K x (c • f) = ‖c‖ * evalNorm K x f := by
  letI := Ideal.Quotient.field x.asIdeal
  rw [evalNorm_eq_spectralNorm, evalNorm_eq_spectralNorm,
    show Ideal.Quotient.mk x.asIdeal (c • f) = c • Ideal.Quotient.mk x.asIdeal f from
      map_smul (Ideal.Quotient.mkₐ K x.asIdeal) c f,
    spectralNorm_smul c (Algebra.IsAlgebraic.isAlgebraic _), coe_nnnorm]

theorem evalNorm_neg (f : A) : evalNorm K x (-f) = evalNorm K x f := by
  letI := Ideal.Quotient.field x.asIdeal
  rw [evalNorm_eq_spectralNorm, evalNorm_eq_spectralNorm, map_neg]
  exact spectralNorm_neg (Algebra.IsAlgebraic.isAlgebraic _)

omit [IsUltrametricDist K] [Algebra.IsAlgebraic K (A ⧸ x.asIdeal)] in
theorem evalNorm_algebraMap (c : K) : evalNorm K x (algebraMap K A c) = ‖c‖ := by
  letI := Ideal.Quotient.field x.asIdeal
  rw [evalNorm_eq_spectralNorm, Ideal.Quotient.mk_algebraMap]
  exact spectralNorm_extends c

omit [IsUltrametricDist K] in
theorem evalNorm_eq_zero_iff (f : A) : evalNorm K x f = 0 ↔ f ∈ x.asIdeal := by
  refine ⟨fun h ↦ ?_, evalNorm_eq_zero_of_mem K⟩
  letI := Ideal.Quotient.field x.asIdeal
  rw [evalNorm_eq_spectralNorm] at h
  exact Ideal.Quotient.eq_zero_iff_mem.1
    (eq_zero_of_map_spectralNorm_eq_zero h (Algebra.IsAlgebraic.isAlgebraic _))

end Point

section Seminorm

variable (K : Type*) [NormedField K] [IsUltrametricDist K] {A : Type*} [CommRing A] [Algebra K A]
  [HasSupSeminorm K A]

omit [IsUltrametricDist K] in
theorem evalNorm_le_supSeminorm (x : MaximalSpectrum A) (f : A) :
    evalNorm K x f ≤ supSeminorm K f :=
  le_ciSup (HasSupSeminorm.bddAbove f) x

omit [IsUltrametricDist K] [HasSupSeminorm K A] in
theorem supSeminorm_le_of_forall {f : A} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ x : MaximalSpectrum A, evalNorm K x f ≤ C) : supSeminorm K f ≤ C :=
  Real.iSup_le h hC

omit [IsUltrametricDist K] [HasSupSeminorm K A] in
theorem supSeminorm_zero : supSeminorm K (0 : A) = 0 :=
  le_antisymm
    (supSeminorm_le_of_forall K le_rfl fun _ ↦ (evalNorm_eq_zero_of_mem K (zero_mem _)).le)
    (supSeminorm_nonneg K 0)

omit [IsUltrametricDist K] [HasSupSeminorm K A] in
/-- BGR 3.8.1/3 (e). -/
theorem supSeminorm_one_le : supSeminorm K (1 : A) ≤ 1 :=
  supSeminorm_le_of_forall K zero_le_one fun x ↦ (evalNorm_one x).le

omit [IsUltrametricDist K] in
theorem supSeminorm_one [Nontrivial A] : supSeminorm K (1 : A) = 1 := by
  obtain ⟨𝔪, h𝔪⟩ := Ideal.exists_maximal A
  exact le_antisymm (supSeminorm_one_le K)
    ((evalNorm_one (K := K) ⟨𝔪, h𝔪⟩).symm.le.trans (evalNorm_le_supSeminorm K ⟨𝔪, h𝔪⟩ 1))

/-- BGR 3.8.1/3 (b). -/
theorem supSeminorm_add_le_max (f g : A) :
    supSeminorm K (f + g) ≤ max (supSeminorm K f) (supSeminorm K g) :=
  supSeminorm_le_of_forall K (le_max_of_le_left (supSeminorm_nonneg K f)) fun x ↦
    (evalNorm_add_le_max x f g).trans
      (max_le_max (evalNorm_le_supSeminorm K x f) (evalNorm_le_supSeminorm K x g))

/-- BGR 3.8.1/3 (d). -/
theorem supSeminorm_mul_le (f g : A) :
    supSeminorm K (f * g) ≤ supSeminorm K f * supSeminorm K g :=
  supSeminorm_le_of_forall K (mul_nonneg (supSeminorm_nonneg K f) (supSeminorm_nonneg K g))
    fun x ↦ (evalNorm_mul_le x f g).trans (mul_le_mul (evalNorm_le_supSeminorm K x f)
      (evalNorm_le_supSeminorm K x g) (evalNorm_nonneg K x g) (supSeminorm_nonneg K f))

/-- BGR 3.8.1/3 (f): power-multiplicativity (for `n ≥ 1`: in the trivial ring `|f⁰|_sup = 0`). -/
theorem supSeminorm_pow (f : A) {n : ℕ} (hn : n ≠ 0) :
    supSeminorm K (f ^ n) = supSeminorm K f ^ n := by
  refine le_antisymm (supSeminorm_le_of_forall K (pow_nonneg (supSeminorm_nonneg K f) n) fun x ↦
    (evalNorm_pow x f n).le.trans
      (pow_le_pow_left₀ (evalNorm_nonneg K x f) (evalNorm_le_supSeminorm K x f) n)) ?_
  have hs := supSeminorm_nonneg K (f ^ n)
  -- every `|f(x)|` is at most `|fⁿ|_sup ^ (1/n)`
  have h : supSeminorm K f ≤ supSeminorm K (f ^ n) ^ (n⁻¹ : ℝ) :=
    supSeminorm_le_of_forall K (Real.rpow_nonneg hs _) fun x ↦ by
      rw [← Real.pow_rpow_inv_natCast (evalNorm_nonneg K x f) hn, ← evalNorm_pow x f n]
      exact Real.rpow_le_rpow (evalNorm_nonneg K x _) (evalNorm_le_supSeminorm K x _)
        (inv_nonneg.2 (Nat.cast_nonneg n))
  calc supSeminorm K f ^ n ≤ (supSeminorm K (f ^ n) ^ (n⁻¹ : ℝ)) ^ n :=
        pow_le_pow_left₀ (supSeminorm_nonneg K f) h n
    _ = supSeminorm K (f ^ n) := Real.rpow_inv_natCast_pow hs hn

/-- `|fⁿ|_sup ≤ |f|_supⁿ` for every `n` (for `n = 0` this is `|1|_sup ≤ 1`). -/
theorem supSeminorm_pow_le (f : A) (n : ℕ) : supSeminorm K (f ^ n) ≤ supSeminorm K f ^ n := by
  rcases eq_or_ne n 0 with rfl | hn
  · rw [pow_zero, pow_zero]
    exact supSeminorm_one_le K
  · exact (supSeminorm_pow K f hn).le

private theorem supSeminorm_smul_le (c : K) (f : A) :
    supSeminorm K (c • f) ≤ ‖c‖ * supSeminorm K f :=
  supSeminorm_le_of_forall K (mul_nonneg (norm_nonneg c) (supSeminorm_nonneg K f)) fun x ↦ by
    rw [evalNorm_smul]
    exact mul_le_mul_of_nonneg_left (evalNorm_le_supSeminorm K x f) (norm_nonneg c)

/-- BGR 3.8.1/3 (c). -/
theorem supSeminorm_smul (c : K) (f : A) : supSeminorm K (c • f) = ‖c‖ * supSeminorm K f := by
  refine le_antisymm (supSeminorm_smul_le K c f) ?_
  rcases eq_or_ne c 0 with rfl | hc
  · rw [norm_zero, zero_mul]
    exact supSeminorm_nonneg K _
  calc ‖c‖ * supSeminorm K f = ‖c‖ * supSeminorm K (c⁻¹ • c • f) := by rw [inv_smul_smul₀ hc]
    _ ≤ ‖c‖ * (‖c⁻¹‖ * supSeminorm K (c • f)) :=
        mul_le_mul_of_nonneg_left (supSeminorm_smul_le K _ _) (norm_nonneg c)
    _ = supSeminorm K (c • f) := by
        rw [norm_inv, ← mul_assoc, mul_inv_cancel₀ (norm_ne_zero_iff.2 hc), one_mul]

theorem supSeminorm_neg (f : A) : supSeminorm K (-f) = supSeminorm K f := by
  simp only [supSeminorm, evalNorm_neg]

theorem supSeminorm_algebraMap [Nontrivial A] (c : K) :
    supSeminorm K (algebraMap K A c) = ‖c‖ := by
  rw [Algebra.algebraMap_eq_smul_one, supSeminorm_smul, supSeminorm_one, mul_one]

theorem isNonarchimedean_supSeminorm : IsNonarchimedean (supSeminorm K : A → ℝ) :=
  supSeminorm_add_le_max K

theorem isPowMul_supSeminorm : IsPowMul (supSeminorm K : A → ℝ) :=
  fun f _ hn ↦ supSeminorm_pow K f (Nat.one_le_iff_ne_zero.1 hn)

variable (A) in
/-- The supremum seminorm packaged as a `RingSeminorm` (BGR 3.8.1/3, 6.2.1/1). -/
noncomputable def supRingSeminorm : RingSeminorm A where
  toFun := supSeminorm K
  map_zero' := supSeminorm_zero K
  add_le' f g := (supSeminorm_add_le_max K f g).trans
    (max_le_add_of_nonneg (supSeminorm_nonneg K f) (supSeminorm_nonneg K g))
  neg' := supSeminorm_neg K
  mul_le' := supSeminorm_mul_le K

@[simp]
theorem supRingSeminorm_apply (f : A) : supRingSeminorm K A f = supSeminorm K f := rfl

omit [IsUltrametricDist K] in
/-- BGR 3.8.1/9: `|f|_sup = 0` exactly when `f` lies in every maximal ideal. -/
theorem supSeminorm_eq_zero_iff_forall_mem (f : A) :
    supSeminorm K f = 0 ↔ ∀ x : MaximalSpectrum A, f ∈ x.asIdeal := by
  refine ⟨fun h x ↦ (evalNorm_eq_zero_iff x f).1
    (le_antisymm (h ▸ evalNorm_le_supSeminorm K x f) (evalNorm_nonneg K x f)), fun h ↦ ?_⟩
  exact le_antisymm
    (supSeminorm_le_of_forall K le_rfl fun x ↦ (evalNorm_eq_zero_of_mem K (h x)).le)
    (supSeminorm_nonneg K f)

omit [IsUltrametricDist K] in
theorem supSeminorm_eq_zero_iff_mem_jacobson_bot (f : A) :
    supSeminorm K f = 0 ↔ f ∈ Ideal.jacobson (⊥ : Ideal A) := by
  rw [supSeminorm_eq_zero_iff_forall_mem, Ideal.jacobson, Ideal.mem_sInf]
  exact ⟨fun h J hJ ↦ h ⟨J, hJ.2⟩, fun h x ↦ h ⟨bot_le, x.isMaximal⟩⟩

end Seminorm

section Contraction

variable {K : Type*} [NormedField K] {A B : Type*} [CommRing A] [Algebra K A]
  [CommRing B] [Algebra K B]

/-- BGR 3.8.1/4, the first step: for a `K`-algebra homomorphism `φ : B → A` and `x ∈ Max A` with
algebraic residue field, `φ⁻¹(x)` is a maximal ideal of `B` (its residue field embeds in
`A ⧸ x`). -/
theorem isMaximal_comap_of_isAlgebraic (φ : B →ₐ[K] A) (x : MaximalSpectrum A)
    [Algebra.IsAlgebraic K (A ⧸ x.asIdeal)] : (x.asIdeal.comap φ).IsMaximal := by
  letI := Ideal.Quotient.field x.asIdeal
  have hker : RingHom.ker ((Ideal.Quotient.mkₐ K x.asIdeal).comp φ) = x.asIdeal.comap φ := by
    ext a
    simp [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]
  exact hker ▸ isMaximal_ker_of_isAlgebraic ((Ideal.Quotient.mkₐ K x.asIdeal).comp φ)

/-- `|φ(g)(x)| = |g(y)|` whenever `y = φ⁻¹(x)` (BGR 3.8.1/4, formula (*)): `φ` induces an
injective map of residue fields `B ⧸ y → A ⧸ x`, which preserves minimal polynomials over `K`. -/
theorem evalNorm_eq_of_asIdeal_eq_comap (φ : B →ₐ[K] A) {x : MaximalSpectrum A}
    {y : MaximalSpectrum B} (hy : y.asIdeal = x.asIdeal.comap φ) (g : B) :
    evalNorm K x (φ g) = evalNorm K y g := by
  obtain ⟨y, hymax⟩ := y
  dsimp only at hy
  subst hy
  -- the injective map of residue fields `B ⧸ φ⁻¹(x) → A ⧸ x` induced by `φ`
  let ψ : B ⧸ x.asIdeal.comap φ →ₐ[K] A ⧸ x.asIdeal :=
    Ideal.Quotient.liftₐ _ ((Ideal.Quotient.mkₐ K x.asIdeal).comp φ) fun a ha ↦
      Ideal.Quotient.eq_zero_iff_mem.2 ha
  have hψ : Function.Injective ψ := by
    rw [injective_iff_map_eq_zero]
    intro y hy
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    have h : Ideal.Quotient.mk x.asIdeal (φ a) = 0 := hy
    have h' : φ a ∈ x.asIdeal := Ideal.Quotient.eq_zero_iff_mem.1 h
    exact Ideal.Quotient.eq_zero_iff_mem.2 h'
  unfold evalNorm
  exact congrArg spectralValue (minpoly.algHom_eq ψ hψ (Ideal.Quotient.mk _ g))

variable [HasSupSeminorm K A]

/-- The point `φ⁻¹(x)` of `Max B` under a point `x` of `Max A` (BGR 3.8.1/4). -/
noncomputable def comapPoint (φ : B →ₐ[K] A) (x : MaximalSpectrum A) : MaximalSpectrum B :=
  ⟨x.asIdeal.comap φ, isMaximal_comap_of_isAlgebraic φ x⟩

@[simp]
theorem comapPoint_asIdeal (φ : B →ₐ[K] A) (x : MaximalSpectrum A) :
    (comapPoint φ x).asIdeal = x.asIdeal.comap φ := rfl

/-- `|φ(g)(x)| = |g(φ⁻¹(x))|` (BGR 3.8.1/4, formula (*)). -/
theorem evalNorm_comapPoint (φ : B →ₐ[K] A) (x : MaximalSpectrum A) (g : B) :
    evalNorm K x (φ g) = evalNorm K (comapPoint φ x) g :=
  evalNorm_eq_of_asIdeal_eq_comap φ rfl g

/-- BGR 3.8.1/4: every `K`-algebra homomorphism is a contraction for `|·|_sup`. -/
theorem supSeminorm_map_le [HasSupSeminorm K B] (φ : B →ₐ[K] A) (g : B) :
    supSeminorm K (φ g) ≤ supSeminorm K g :=
  supSeminorm_le_of_forall K (supSeminorm_nonneg K g) fun x ↦
    (evalNorm_comapPoint φ x g).trans_le (evalNorm_le_supSeminorm K _ g)

end Contraction

section Quotient

variable {K : Type*} [NormedField K] [IsUltrametricDist K] {A : Type*} [CommRing A] [Algebra K A]
  [HasSupSeminorm K A]

/-- The point of `A` under a point of a quotient `A ⧸ I`. -/
private def comapMk {I : Ideal A} (x : MaximalSpectrum (A ⧸ I)) : MaximalSpectrum A :=
  ⟨x.asIdeal.comap (Ideal.Quotient.mk I),
    Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective⟩

omit [IsUltrametricDist K] [HasSupSeminorm K A] in
private theorem evalNorm_mk_comapMk {I : Ideal A} (x : MaximalSpectrum (A ⧸ I)) (f : A) :
    evalNorm K x (Ideal.Quotient.mk I f) = evalNorm K (comapMk x) f :=
  evalNorm_eq_of_asIdeal_eq_comap (Ideal.Quotient.mkₐ K I) rfl f

omit [IsUltrametricDist K] in
instance HasSupSeminorm.quotient (I : Ideal A) : HasSupSeminorm K (A ⧸ I) where
  isAlgebraic x := by
    -- the residue field at `x` is the image of the residue field at the point of `A` below it
    let ψ : A ⧸ (comapMk x).asIdeal →ₐ[K] (A ⧸ I) ⧸ x.asIdeal :=
      Ideal.Quotient.liftₐ _ ((Ideal.Quotient.mkₐ K x.asIdeal).comp (Ideal.Quotient.mkₐ K I))
        fun a ha ↦ Ideal.Quotient.eq_zero_iff_mem.2 ha
    refine ⟨fun z ↦ ?_⟩
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
    exact (Algebra.IsAlgebraic.isAlgebraic (Ideal.Quotient.mk (comapMk x).asIdeal b)).algHom ψ
  bddAbove f := by
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective f
    refine ⟨supSeminorm K g, ?_⟩
    rintro _ ⟨x, rfl⟩
    exact (evalNorm_mk_comapMk x g).trans_le (evalNorm_le_supSeminorm K _ g)

variable (K)

omit [IsUltrametricDist K] in
theorem supSeminorm_mk_le (I : Ideal A) (f : A) :
    supSeminorm K (Ideal.Quotient.mk I f) ≤ supSeminorm K f :=
  supSeminorm_map_le (Ideal.Quotient.mkₐ K I) f

omit [IsUltrametricDist K] in
/-- A point of `A` containing `I` sees the same value on `f` and on `f mod I`. -/
theorem evalNorm_le_supSeminorm_mk {I : Ideal A} {x : MaximalSpectrum A} (hI : I ≤ x.asIdeal)
    (f : A) : evalNorm K x f ≤ supSeminorm K (Ideal.Quotient.mk I f) := by
  -- the image `x₀` of `x` in `A ⧸ I` is a maximal ideal with preimage `x`
  have hcomap : (x.asIdeal.map (Ideal.Quotient.mk I)).comap (Ideal.Quotient.mk I) = x.asIdeal := by
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
      Ideal.mk_ker, sup_eq_left.2 hI]
  have hmax : (x.asIdeal.map (Ideal.Quotient.mk I)).IsMaximal := by
    refine (Ideal.map_eq_top_or_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
      x.isMaximal).resolve_left fun htop ↦ x.isMaximal.ne_top ?_
    rw [← hcomap, htop, Ideal.comap_top]
  let x₀ : MaximalSpectrum (A ⧸ I) := ⟨_, hmax⟩
  have hx : comapMk x₀ = x := MaximalSpectrum.ext hcomap
  rw [← hx, ← evalNorm_mk_comapMk]
  exact evalNorm_le_supSeminorm K x₀ _

omit [IsUltrametricDist K] in
/-- BGR 3.8.1/5 (the noetherian form used in 6.2.1/3): `|f|_sup` is attained on some
`A ⧸ 𝔭` with `𝔭` a minimal prime. -/
theorem exists_minimalPrimes_supSeminorm_mk_eq [IsNoetherianRing A] [Nontrivial A] (f : A) :
    ∃ 𝔭 ∈ minimalPrimes A, supSeminorm K (Ideal.Quotient.mk 𝔭 f) = supSeminorm K f := by
  have hfin := minimalPrimes.finite_of_isNoetherianRing A
  obtain ⟨𝔪, h𝔪⟩ := Ideal.exists_maximal A
  obtain ⟨𝔮, h𝔮, -⟩ := Ideal.exists_minimalPrimes_le (bot_le : ⊥ ≤ 𝔪)
  have hne : hfin.toFinset.Nonempty := ⟨𝔮, hfin.mem_toFinset.2 h𝔮⟩
  obtain ⟨𝔭, h𝔭, hmax⟩ :=
    hfin.toFinset.exists_max_image (fun 𝔭 ↦ supSeminorm K (Ideal.Quotient.mk 𝔭 f)) hne
  refine ⟨𝔭, hfin.mem_toFinset.1 h𝔭, le_antisymm (supSeminorm_mk_le K 𝔭 f) ?_⟩
  -- every point lies above a minimal prime
  refine supSeminorm_le_of_forall K (supSeminorm_nonneg K _) fun x ↦ ?_
  obtain ⟨𝔭', h𝔭', h𝔭'x⟩ := Ideal.exists_minimalPrimes_le (bot_le : ⊥ ≤ x.asIdeal)
  exact (evalNorm_le_supSeminorm_mk K h𝔭'x f).trans (hmax 𝔭' (hfin.mem_toFinset.2 h𝔭'))

omit [IsUltrametricDist K] in
/-- Passing to the quotient by an ideal contained in every maximal ideal does not change
`|·|_sup` (BGR 6.2.1/3, second equation, proved for `I ≤ jacobson ⊥`). -/
theorem supSeminorm_mk_eq_of_le_jacobson {I : Ideal A} (hI : I ≤ Ideal.jacobson ⊥) (f : A) :
    supSeminorm K (Ideal.Quotient.mk I f) = supSeminorm K f :=
  le_antisymm (supSeminorm_mk_le K I f) (supSeminorm_le_of_forall K (supSeminorm_nonneg K _)
    fun x ↦ evalNorm_le_supSeminorm_mk K
      (hI.trans (show Ideal.jacobson ⊥ ≤ x.asIdeal from sInf_le ⟨bot_le, x.isMaximal⟩)) f)

omit [IsUltrametricDist K] in
/-- BGR 6.2.1/3: `|f|_sup = |red f|_sup`. -/
theorem supSeminorm_mk_nilradical (f : A) :
    supSeminorm K (Ideal.Quotient.mk (nilradical A) f) = supSeminorm K f :=
  supSeminorm_mk_eq_of_le_jacobson K Ideal.radical_le_jacobson f

end Quotient

section Banach

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : Type*} [NormedCommRing A] [NormedAlgebra K A] [IsUltrametricDist A] [CompleteSpace A]

/-- A Banach algebra all of whose residue fields are algebraic has a (finite) supremum seminorm
(BGR 3.8.2/2). -/
theorem HasSupSeminorm.of_forall_isAlgebraic
    (h : ∀ x : MaximalSpectrum A, Algebra.IsAlgebraic K (A ⧸ x.asIdeal)) : HasSupSeminorm K A :=
  ⟨h, bddAbove_range_evalNorm⟩

end Banach

end Affinoid
