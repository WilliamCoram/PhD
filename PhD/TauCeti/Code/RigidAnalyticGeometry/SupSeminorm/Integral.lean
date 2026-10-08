/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.RingTheory.Ideal.GoingUp
import PhD.TauCeti.Code.RigidAnalyticGeometry.SupSeminorm.SpectralValue

/-!
# The supremum seminorm along integral homomorphisms

Layer 2, §2.1.3–§2.1.4 (BGR 3.8.1/6–3.8.1/8). For an integral injective `K`-algebra homomorphism
`B → A` the supremum seminorm of `A` restricts to that of `B` (3.8.1/6 (a)), finiteness transfers
both ways (3.8.1/6 (c)), and — for `B` an integrally closed domain and `A` a domain, torsion-free
over `B` — `|f|_sup` is the spectral value of the minimal polynomial of `f` over `B`
(3.8.1/7 (a)). The maximum modulus principle, the norm property and multiplicativity transfer from
`B` to `A` (3.8.1/7 (b)–(d)), and `|f|_sup` has a power in `|K|` (3.8.1/8).

The core of 3.8.1/7 (a) is the fibre computation on `A ⧸ yA = (B ⧸ y)[X] ⧸ (q̄)` (BGR p. 172):
`Affinoid.exists_evalNorm_root_eq_supSpectralValue`, proved with one splitting field of `q̄` and
Mathlib's `max_norm_root_eq_spectralValue` instead of BGR's prime factorisation of `q̄`.

## Main declarations

* `Affinoid.exists_comap_algebraMap_eq`,
  `Affinoid.isAlgebraic_quotient_of_isAlgebraic_quotient_comap`: going up for points.
* `Affinoid.supSeminorm_eq_spectralNorm`, `Affinoid.HasSupSeminorm.of_field`,
  `Affinoid.evalNorm_eq_supSeminorm_residue`: fields have one point, the spectral norm.
* `Affinoid.HasSupSeminorm.of_isIntegral`, `Affinoid.HasSupSeminorm.of_isIntegral_of_faithfulSMul`,
  `Affinoid.supSeminorm_algebraMap_eq`: BGR 3.8.1/6.
* `Affinoid.exists_evalNorm_root_eq_supSpectralValue`, `Affinoid.evalNorm_root_le_supSpectralValue`:
  the fibre computation.
* `Affinoid.supSeminorm_eq_supSpectralValue_minpoly`: BGR 3.8.1/7 (a).
* `Affinoid.minpoly_algebraMap_mul_eq_scaleRoots`, `Affinoid.supSeminorm_algebraMap_mul`:
  BGR 3.8.1/7 (d).
* `Affinoid.exists_evalNorm_eq_supSeminorm_of_forall_exists`: BGR 3.8.1/7 (b).
* `Affinoid.eq_zero_of_supSeminorm_eq_zero`: BGR 3.8.1/7 (c).
* `Affinoid.supSeminorm_pow_factorial_mem_range_norm`: BGR 3.8.1/8, with a uniform exponent.

## Deviation (plan D8)
BGR state 3.8.1/7 for `A` torsion-free over `B`; every consumer in Layer 2 reduces to `A` a
domain first (6.2.1/4, 6.2.2/4 and 6.2.4/1 all pass through the minimal primes), and Mathlib's
`minpoly.ker_eval` needs `IsDomain A`, so 3.8.1/7 is stated for `A` a domain.
-/

open Polynomial Ideal

namespace Affinoid

section GoingUp

variable {K : Type*} [NormedField K] {A B : Type*} [CommRing A] [Algebra K A] [CommRing B]
  [Algebra K B] [Algebra B A] [IsScalarTower K B A]

/-- Going up (BGR 3.8.1/6 (a), "there is a maximal ideal `x` of `A` lying over `y`"): for `A`
integral over `B` with injective structure map, every maximal ideal of `B` is the contraction of a
maximal ideal of `A`. -/
theorem exists_comap_algebraMap_eq [Algebra.IsIntegral B A] [FaithfulSMul B A]
    (y : MaximalSpectrum B) :
    ∃ x : MaximalSpectrum A, x.asIdeal.comap (algebraMap B A) = y.asIdeal := by
  obtain ⟨Q, hQ, hQy⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral y.asIdeal (by
    rw [(RingHom.injective_iff_ker_eq_bot _).1 (FaithfulSMul.algebraMap_injective B A)]
    exact bot_le)
  exact ⟨⟨Q, hQ⟩, hQy⟩

/-- The contraction of a maximal ideal of `A` along an integral map is maximal. -/
theorem isMaximal_comap_algebraMap_of_isIntegral [Algebra.IsIntegral B A] (x : MaximalSpectrum A) :
    (x.asIdeal.comap (algebraMap B A)).IsMaximal :=
  Ideal.isMaximal_comap_of_isIntegral_of_isMaximal x.asIdeal

/-- For `A` integral over `B`, the residue field at `x` is algebraic over `K` as soon as the residue
field at `φ⁻¹(x)` is (BGR 3.8.1/6 (a): "`A/x` is integral over `B/y`. Therefore `A/x` is an
algebraic extension of `k`"). -/
theorem isAlgebraic_quotient_of_isAlgebraic_quotient_comap [Algebra.IsIntegral B A]
    (x : MaximalSpectrum A)
    [Algebra.IsAlgebraic K (B ⧸ x.asIdeal.comap (algebraMap B A))] :
    Algebra.IsAlgebraic K (A ⧸ x.asIdeal) := by
  haveI : (x.asIdeal.comap (algebraMap B A)).IsMaximal := isMaximal_comap_algebraMap_of_isIntegral x
  -- `A ⧸ x` is integral over the field `B ⧸ (x ∩ B)`, which is algebraic over `K`
  haveI : IsScalarTower K (B ⧸ x.asIdeal.comap (algebraMap B A)) (A ⧸ x.asIdeal) :=
    IsScalarTower.of_algebraMap_eq fun k ↦
      congrArg (Ideal.Quotient.mk x.asIdeal) (IsScalarTower.algebraMap_apply K B A k)
  haveI := Algebra.IsIntegral.isAlgebraic (R := B ⧸ x.asIdeal.comap (algebraMap B A))
    (A := A ⧸ x.asIdeal)
  exact Algebra.IsAlgebraic.trans K (B ⧸ x.asIdeal.comap (algebraMap B A)) (A ⧸ x.asIdeal)

end GoingUp

section Field

variable (K : Type*) [NormedField K]

/-- A field has exactly one point, `⊥`, and `|b(⊥)|` is the spectral norm of `b`. -/
theorem evalNorm_eq_spectralNorm_of_field {L : Type*} [Field L] [Algebra K L]
    (x : MaximalSpectrum L) (b : L) : evalNorm K x b = spectralNorm K L b := by
  have hx : x.asIdeal = ⊥ := (Ideal.eq_bot_or_top x.asIdeal).resolve_right x.isMaximal.ne_top
  -- the residue field `L ⧸ ⊥` maps isomorphically onto `L`
  let e : L ⧸ x.asIdeal →ₐ[K] L := Ideal.Quotient.liftₐ x.asIdeal (AlgHom.id K L) fun a ha ↦
    Ideal.mem_bot.1 (hx ▸ ha)
  have he : Function.Injective e := by
    rw [injective_iff_map_eq_zero]
    intro y hy
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    have ha : a = 0 := hy
    rw [ha, map_zero]
  unfold evalNorm spectralNorm
  exact congrArg spectralValue (minpoly.algHom_eq e he (Ideal.Quotient.mk _ b)).symm

/-- Over a field `L` the supremum seminorm is the spectral norm (BGR 3.8.1/2: "if `A` is an
algebraic extension of `k`, this definition obviously yields the spectral norm on `A`"). -/
theorem supSeminorm_eq_spectralNorm {L : Type*} [Field L] [Algebra K L] (b : L) :
    supSeminorm K b = spectralNorm K L b := by
  haveI : Nonempty (MaximalSpectrum L) := ⟨⟨⊥, Ideal.bot_isMaximal⟩⟩
  unfold supSeminorm
  simp only [evalNorm_eq_spectralNorm_of_field K _ b]
  exact ciSup_const

/-- A field algebraic over `K` has a supremum seminorm (one point, the spectral norm). -/
theorem HasSupSeminorm.of_field (L : Type*) [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] :
    HasSupSeminorm K L where
  isAlgebraic x := ⟨fun z ↦ by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact (Algebra.IsAlgebraic.isAlgebraic a).algHom (Ideal.Quotient.mkₐ K x.asIdeal)⟩
  bddAbove b := ⟨spectralNorm K L b, by
    rintro _ ⟨x, rfl⟩
    exact (evalNorm_eq_spectralNorm_of_field K x b).le⟩

/-- `|f(x)|` is the supremum seminorm of the class of `f` in the residue field `A ⧸ x`. -/
theorem evalNorm_eq_supSeminorm_residue {A : Type*} [CommRing A] [Algebra K A]
    (x : MaximalSpectrum A) (f : A) :
    letI := Ideal.Quotient.field x.asIdeal
    evalNorm K x f = supSeminorm K (Ideal.Quotient.mk x.asIdeal f) := by
  letI := Ideal.Quotient.field x.asIdeal
  rw [supSeminorm_eq_spectralNorm]
  rfl

end Field

section Isometry

variable (K : Type*) [NormedField K] [IsUltrametricDist K] {A B : Type*} [CommRing A] [Algebra K A]
  [CommRing B] [Algebra K B] [Algebra B A] [IsScalarTower K B A] [Algebra.IsIntegral B A]

/-- BGR 3.8.1/6 (c), one direction: `|·|_sup` is finite on `A` if it is finite on `B`, because
`|f|_sup ≤ max |b_i|_sup^{1/i}` for any equation of integral dependence (3.8.1/6 (b)). -/
theorem HasSupSeminorm.of_isIntegral [HasSupSeminorm K B] : HasSupSeminorm K A := by
  have halg : ∀ x : MaximalSpectrum A, Algebra.IsAlgebraic K (A ⧸ x.asIdeal) := fun x ↦ by
    haveI : Algebra.IsAlgebraic K (B ⧸ x.asIdeal.comap (algebraMap B A)) :=
      HasSupSeminorm.isAlgebraic (⟨_, isMaximal_comap_algebraMap_of_isIntegral x⟩ :
        MaximalSpectrum B)
    exact isAlgebraic_quotient_of_isAlgebraic_quotient_comap (B := B) x
  refine ⟨halg, fun f ↦ ?_⟩
  obtain ⟨p, hp, hpf⟩ := Algebra.IsIntegral.isIntegral (R := B) f
  refine ⟨supSpectralValue K p, ?_⟩
  rintro _ ⟨x, rfl⟩
  dsimp only
  -- BGR 3.8.1/6 (b) at the point `x`, through the residue field `A ⧸ x` (one point)
  haveI := halg x
  letI := Ideal.Quotient.field x.asIdeal
  haveI := HasSupSeminorm.of_field K (A ⧸ x.asIdeal)
  rw [evalNorm_eq_supSeminorm_residue K x f]
  refine supSeminorm_le_supSpectralValue_of_eval₂_eq_zero K
    ((Ideal.Quotient.mkₐ K x.asIdeal).comp (IsScalarTower.toAlgHom K B A)) hp ?_
  have h := congrArg (Ideal.Quotient.mk x.asIdeal) hpf
  rw [Polynomial.hom_eval₂, map_zero] at h
  exact h

omit [IsUltrametricDist K] in
/-- BGR 3.8.1/6 (c), the other direction, for an injective structure map (every `y` has a point
`x` over it). -/
theorem HasSupSeminorm.of_isIntegral_of_faithfulSMul [HasSupSeminorm K A] [FaithfulSMul B A] :
    HasSupSeminorm K B := by
  refine ⟨fun y ↦ ?_, fun b ↦ ?_⟩
  · obtain ⟨x, hx⟩ := exists_comap_algebraMap_eq (A := A) y
    -- the residue field at `y` embeds into the residue field at `x`
    let ψ : B ⧸ y.asIdeal →ₐ[K] A ⧸ x.asIdeal :=
      Ideal.Quotient.liftₐ y.asIdeal
        ((Ideal.Quotient.mkₐ K x.asIdeal).comp (IsScalarTower.toAlgHom K B A)) fun a ha ↦ by
          rw [← hx] at ha
          exact Ideal.Quotient.eq_zero_iff_mem.2 ha
    have hψ : Function.Injective ψ := by
      rw [injective_iff_map_eq_zero]
      intro z hz
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
      have h : Ideal.Quotient.mk x.asIdeal (algebraMap B A a) = 0 := hz
      have h'' : algebraMap B A a ∈ x.asIdeal := Ideal.Quotient.eq_zero_iff_mem.1 h
      have h' : a ∈ y.asIdeal := hx ▸ h''
      exact Ideal.Quotient.eq_zero_iff_mem.2 h'
    exact Algebra.IsAlgebraic.of_injective ψ hψ
  · refine ⟨supSeminorm K (algebraMap B A b), ?_⟩
    rintro _ ⟨y, rfl⟩
    obtain ⟨x, hx⟩ := exists_comap_algebraMap_eq (A := A) y
    exact (evalNorm_eq_of_asIdeal_eq_comap (IsScalarTower.toAlgHom K B A) hx.symm b).symm.trans_le
      (evalNorm_le_supSeminorm K x _)

omit [IsUltrametricDist K] in
/-- BGR 3.8.1/6 (a): an integral monomorphism is an isometry for `|·|_sup`. -/
theorem supSeminorm_algebraMap_eq [HasSupSeminorm K A] [HasSupSeminorm K B] [FaithfulSMul B A]
    (b : B) : supSeminorm K (algebraMap B A b) = supSeminorm K b := by
  refine le_antisymm (supSeminorm_map_le (IsScalarTower.toAlgHom K B A) b)
    (supSeminorm_le_of_forall K (supSeminorm_nonneg K _) fun y ↦ ?_)
  obtain ⟨x, hx⟩ := exists_comap_algebraMap_eq (A := A) y
  exact (evalNorm_eq_of_asIdeal_eq_comap (IsScalarTower.toAlgHom K B A) hx.symm b).symm.trans_le
    (evalNorm_le_supSeminorm K x _)

omit [IsUltrametricDist K] [Algebra K B] [IsScalarTower K B A] in
/-- `|f|_sup` is the supremum over `y ∈ Max B` of `|f mod yA|_sup` (BGR p. 172,
"`|f|_sup = sup_{y ∈ Max_k B} |f_y|_sup`"), upper-bound half: every point of `A` lies over a point
of `B`. -/
theorem supSeminorm_le_of_forall_supSeminorm_mk_map_le [HasSupSeminorm K A] {f : A} {C : ℝ}
    (hC : 0 ≤ C)
    (h : ∀ y : MaximalSpectrum B,
      supSeminorm K (Ideal.Quotient.mk (y.asIdeal.map (algebraMap B A)) f) ≤ C) :
    supSeminorm K f ≤ C :=
  supSeminorm_le_of_forall K hC fun x ↦
    (evalNorm_le_supSeminorm_mk K (Ideal.map_comap_le) f).trans
      (h ⟨_, isMaximal_comap_algebraMap_of_isIntegral x⟩)

end Isometry

section Fibre

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- The fibre computation for a monic `q` that splits in an algebraic extension `E` of `L`: the
largest root `a₀` of `q` in `E` has `‖a₀‖ = σ(q)` (Mathlib `max_norm_root_eq_spectralValue`, for the
spectral norms over `K` on `L` and `E`), and the kernel of `AdjoinRoot q → E`, `root ↦ a₀`, is a
point at which `|root(x)| = ‖a₀‖`. -/
private theorem exists_evalNorm_root_eq_supSpectralValue_of_splits {L E : Type*} [Field L]
    [Algebra K L] [Algebra.IsAlgebraic K L] [Field E] [Algebra L E] [Algebra K E]
    [IsScalarTower K L E] [Algebra.IsAlgebraic L E] {q : L[X]} (hq : q.Monic)
    (hq0 : 0 < q.natDegree) (hsplit : (q.map (algebraMap L E)).Splits) :
    ∃ x : MaximalSpectrum (AdjoinRoot q),
      evalNorm K x (AdjoinRoot.root q) = supSpectralValue K q := by
  classical
  haveI : Algebra.IsAlgebraic K E := Algebra.IsAlgebraic.trans K L E
  -- every root `a` of `q` in `E` gives a `K`-algebra map `AdjoinRoot q → E` with `root ↦ a`
  have hlift : ∀ a ∈ (q.map (algebraMap L E)).roots,
      ∃ ψ : AdjoinRoot q →ₐ[K] E, ψ (AdjoinRoot.root q) = a := by
    intro a ha
    have hroot : q.eval₂ (IsScalarTower.toAlgHom K L E : L →+* E) a = 0 := by
      rw [IsScalarTower.coe_toAlgHom, ← eval_map, ← IsRoot.def]
      exact (mem_roots'.1 ha).2
    exact ⟨AdjoinRoot.liftAlgHom q (IsScalarTower.toAlgHom K L E) a hroot,
      AdjoinRoot.lift_root hroot⟩
  letI : NormedField L := spectralNorm.normedField K L
  letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
  -- `σ(q)` for `|·|_sup` on `L` is the spectral value for the spectral norm of `L`
  have hσ : supSpectralValue K q = spectralValue q :=
    supSpectralValue_eq_spectralValue K (fun b ↦ supSeminorm_eq_spectralNorm K b) q
  letI : NormedField E := spectralNorm.normedField K E
  letI : NormedAlgebra K E := spectralNorm.normedAlgebra K E
  letI : NormedAlgebra L E := spectralNorm.normedAlgebra' K L E
  -- the spectral norm of `E` over `K`, as an `L`-algebra norm (BGR 3.2.2/4)
  let f : AlgebraNorm L E :=
    { toFun := norm
      map_zero' := norm_zero
      add_le' := norm_add_le
      neg' := norm_neg
      smul' := fun a x ↦ norm_smul a x
      mul_le' := norm_mul_le
      eq_zero_of_map_eq_zero' := fun _ ↦ norm_eq_zero.mp }
  have hpm : IsPowMul f := fun y n _ ↦ norm_pow y n
  have hna : IsNonarchimedean f := isNonarchimedean_spectralNorm (K := K) (L := E)
  have h1 : f 1 = 1 := spectralNorm_one (K := K) (L := E)
  have hmonic : (q.map (algebraMap L E)).Monic := hq.map _
  have hprod := Splits.eq_prod_roots_of_monic hsplit hmonic
  have hmax := max_norm_root_eq_spectralValue hpm hna h1 q (q.map (algebraMap L E)).roots
    ((mapAlg_eq_map E q).trans hprod)
  -- the roots form a nonempty multiset
  have hs0 : (q.map (algebraMap L E)).roots ≠ 0 := by
    intro h0
    have hdeg := congrArg natDegree hprod
    rw [h0, Multiset.map_zero, Multiset.prod_zero, natDegree_one, hq.natDegree_map] at hdeg
    omega
  obtain ⟨a₀, ha₀, hmax₀⟩ := (q.map (algebraMap L E)).roots.toFinset.exists_max_image
    (fun a ↦ ‖a‖) (Multiset.toFinset_nonempty.2 hs0)
  have ha₀s : a₀ ∈ (q.map (algebraMap L E)).roots := Multiset.mem_toFinset.1 ha₀
  -- the supremum of the norms of the roots is attained at `a₀`
  have hle : ∀ x : E, (if x ∈ (q.map (algebraMap L E)).roots then f x else 0) ≤ ‖a₀‖ := by
    intro x
    split_ifs with hx
    · exact hmax₀ x (Multiset.mem_toFinset.2 hx)
    · exact norm_nonneg a₀
  have hiSup : (⨆ x : E, if x ∈ (q.map (algebraMap L E)).roots then f x else 0) = ‖a₀‖ := by
    refine le_antisymm (ciSup_le hle) ?_
    calc ‖a₀‖ = (if a₀ ∈ (q.map (algebraMap L E)).roots then f a₀ else 0) := by
          rw [if_pos ha₀s]
          rfl
      _ ≤ _ := le_ciSup ⟨‖a₀‖, by rintro _ ⟨x, rfl⟩; exact hle x⟩ a₀
  -- the point: the kernel of `AdjoinRoot q → E`, `root ↦ a₀`
  obtain ⟨ψ, hψ⟩ := hlift a₀ ha₀s
  refine ⟨⟨RingHom.ker ψ, isMaximal_ker_of_isAlgebraic ψ⟩, ?_⟩
  rw [evalNorm_eq_norm_algHom ψ _ rfl, hψ, ← hiSup, hmax]
  exact hσ.symm

/-- **The fibre computation** (BGR p. 172, the display `|f̄_y|_sup = max_ν |f̄_ν|_ν = max_ν σ(q_ν)
= σ(q_y)`): over a field `L` algebraic over `K`, the class of `X` in `L[X] ⧸ (q)` for a monic `q`
of positive degree attains `σ(q)` at some maximal ideal: the kernel of evaluation at a root of
largest norm in a splitting field of `q` (Mathlib `max_norm_root_eq_spectralValue`). -/
theorem exists_evalNorm_root_eq_supSpectralValue {L : Type*} [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L] {q : L[X]} (hq : q.Monic) (hq0 : 0 < q.natDegree) :
    ∃ x : MaximalSpectrum (AdjoinRoot q),
      evalNorm K x (AdjoinRoot.root q) = supSpectralValue K q := by
  haveI := Algebra.IsAlgebraic.of_finite L q.SplittingField
  exact exists_evalNorm_root_eq_supSpectralValue_of_splits K hq hq0 (SplittingField.splits q)

omit [CompleteSpace K] in
/-- The upper bound in the fibre: `|X(x)| ≤ σ(q)` at every point (a root of `q` in the residue
field has norm at most the spectral value, Mathlib `norm_root_le_spectralValue`). -/
theorem evalNorm_root_le_supSpectralValue {L : Type*} [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L] {q : L[X]} (hq : q.Monic) [HasSupSeminorm K (AdjoinRoot q)]
    (x : MaximalSpectrum (AdjoinRoot q)) :
    evalNorm K x (AdjoinRoot.root q) ≤ supSpectralValue K q := by
  -- BGR 6.2.2/3 in the residue field `AdjoinRoot q ⧸ x`, a field with one point
  haveI := HasSupSeminorm.of_field K L
  haveI : Algebra.IsAlgebraic K (AdjoinRoot q ⧸ x.asIdeal) := HasSupSeminorm.isAlgebraic x
  letI := Ideal.Quotient.field x.asIdeal
  haveI := HasSupSeminorm.of_field K (AdjoinRoot q ⧸ x.asIdeal)
  rw [evalNorm_eq_supSeminorm_residue K x]
  refine supSeminorm_le_supSpectralValue_of_eval₂_eq_zero K
    ((Ideal.Quotient.mkₐ K x.asIdeal).comp (IsScalarTower.toAlgHom K L (AdjoinRoot q))) hq ?_
  have h := congrArg (Ideal.Quotient.mk x.asIdeal) (AdjoinRoot.eval₂_root q)
  rw [Polynomial.hom_eval₂, map_zero] at h
  exact h

end Fibre

section MinimalPolynomial

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : Type*} [CommRing B] [IsDomain B]
  [IsIntegrallyClosed B] [Algebra K B] [CommRing A] [IsDomain A] [Algebra K A] [Algebra B A]
  [IsScalarTower K B A] [Algebra.IsIntegral B A] [Module.IsTorsionFree B A]
  [HasSupSeminorm K A] [HasSupSeminorm K B]

omit [HasSupSeminorm K A] in
/-- Over each point `y` of `B`, `σ(q̄_y)` for the reduction `q̄_y` of the minimal polynomial of `f`
is the value of `f` at some point of `A` (BGR p. 172: the fibre `A/yA = (B/y)[X]/(q_y)` and
`|f̄_y|_sup = σ(q_y)`). The point is found in `B[X] ⧸ (q) ≅ B[f]` above the point of
`(B ⧸ y)[X] ⧸ (q̄_y)` given by the fibre computation, and then in `A` by going up. -/
private theorem exists_evalNorm_eq_supSpectralValue_map (f : A) (y : MaximalSpectrum B) :
    ∃ x : MaximalSpectrum A,
      evalNorm K x f = supSpectralValue K ((minpoly B f).map (Ideal.Quotient.mk y.asIdeal)) := by
  have hfi : IsIntegral B f := Algebra.IsIntegral.isIntegral f
  have hq : (minpoly B f).Monic := minpoly.monic hfi
  -- `Φ : B[X] ⧸ (q) → A`, `root ↦ f`, is injective (BGR p. 171: "`ker τ` is generated by `q`")
  have hqf : (minpoly B f).eval₂ (IsScalarTower.toAlgHom K B A : B →+* A) f = 0 := by
    rw [IsScalarTower.coe_toAlgHom, ← Polynomial.aeval_def]
    exact minpoly.aeval B f
  obtain ⟨Φ, hΦroot, hΦof, hΦmk⟩ : ∃ Φ : AdjoinRoot (minpoly B f) →ₐ[K] A,
      Φ (AdjoinRoot.root _) = f ∧ (∀ b, Φ (AdjoinRoot.of _ b) = algebraMap B A b) ∧
      ∀ p, Φ (AdjoinRoot.mk _ p) = Polynomial.aeval f p :=
    ⟨AdjoinRoot.liftAlgHom _ (IsScalarTower.toAlgHom K B A) f hqf, AdjoinRoot.lift_root hqf,
      fun _ ↦ AdjoinRoot.lift_of hqf,
      fun p ↦ (AdjoinRoot.lift_mk hqf p).trans (Polynomial.aeval_def f p).symm⟩
  have hΦinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    induction z using AdjoinRoot.induction_on with
    | ih p =>
      rw [hΦmk] at hz
      have hp : p ∈ RingHom.ker (Polynomial.aeval (R := B) f).toRingHom := RingHom.mem_ker.2 hz
      rw [minpoly.ker_eval hfi, Ideal.mem_span_singleton] at hp
      exact AdjoinRoot.mk_eq_zero.2 hp
  -- `A` is integral over `B[X] ⧸ (q)`, which embeds into it
  letI : Algebra (AdjoinRoot (minpoly B f)) A := (Φ : AdjoinRoot (minpoly B f) →+* A).toAlgebra
  haveI : IsScalarTower B (AdjoinRoot (minpoly B f)) A :=
    IsScalarTower.of_algebraMap_eq fun b ↦ (hΦof b).symm
  haveI : Algebra.IsIntegral (AdjoinRoot (minpoly B f)) A :=
    ⟨fun a ↦ (Algebra.IsIntegral.isIntegral (R := B) a).tower_top⟩
  haveI : FaithfulSMul (AdjoinRoot (minpoly B f)) A :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 hΦinj
  -- the fibre `(B ⧸ y)[X] ⧸ (q̄)` over `y` (BGR p. 172, "`A/yA = (B/y)[X]/(q_y)`")
  haveI : Algebra.IsAlgebraic K (B ⧸ y.asIdeal) := HasSupSeminorm.isAlgebraic y
  letI := Ideal.Quotient.field y.asIdeal
  haveI := HasSupSeminorm.of_field K (B ⧸ y.asIdeal)
  obtain ⟨qbar, hqbar⟩ : ∃ p, p = (minpoly B f).map (Ideal.Quotient.mk y.asIdeal) := ⟨_, rfl⟩
  have hqbar_monic : qbar.Monic := by
    rw [hqbar]
    exact hq.map _
  have hqbar_deg : qbar.natDegree = (minpoly B f).natDegree := by
    rw [hqbar]
    exact hq.natDegree_map _
  obtain ⟨xbar, hxbar⟩ := exists_evalNorm_root_eq_supSpectralValue K hqbar_monic
    (hqbar_deg ▸ minpoly.natDegree_pos hfi)
  -- `π : B[X] ⧸ (q) → (B ⧸ y)[X] ⧸ (q̄)`, `root ↦ root`
  have hqπ : (minpoly B f).eval₂
      (((IsScalarTower.toAlgHom K (B ⧸ y.asIdeal) (AdjoinRoot qbar)).comp
        (Ideal.Quotient.mkₐ K y.asIdeal) : B →ₐ[K] AdjoinRoot qbar) : B →+* AdjoinRoot qbar)
      (AdjoinRoot.root qbar) = 0 := by
    have h : (((IsScalarTower.toAlgHom K (B ⧸ y.asIdeal) (AdjoinRoot qbar)).comp
        (Ideal.Quotient.mkₐ K y.asIdeal) : B →ₐ[K] AdjoinRoot qbar) : B →+* AdjoinRoot qbar) =
        (AdjoinRoot.of qbar).comp (Ideal.Quotient.mk y.asIdeal) := RingHom.ext fun _ ↦ rfl
    rw [h, ← Polynomial.eval₂_map, ← hqbar, AdjoinRoot.eval₂_root]
  obtain ⟨π, hπroot⟩ : ∃ π : AdjoinRoot (minpoly B f) →ₐ[K] AdjoinRoot qbar,
      π (AdjoinRoot.root _) = AdjoinRoot.root qbar :=
    ⟨AdjoinRoot.liftAlgHom _ _ _ hqπ, AdjoinRoot.lift_root hqπ⟩
  -- the point `z` of `B[X] ⧸ (q)` below `x̄` and a point `x` of `A` above `z`
  haveI : Module.Finite (B ⧸ y.asIdeal) (AdjoinRoot qbar) :=
    (AdjoinRoot.powerBasis' hqbar_monic).finite
  haveI : Algebra.IsIntegral (B ⧸ y.asIdeal) (AdjoinRoot qbar) :=
    Algebra.IsIntegral.of_finite _ _
  haveI : HasSupSeminorm K (AdjoinRoot qbar) :=
    HasSupSeminorm.of_isIntegral K (B := B ⧸ y.asIdeal)
  obtain ⟨x, hx⟩ := exists_comap_algebraMap_eq (A := A) (comapPoint π xbar)
  have e1 : evalNorm K xbar (π (AdjoinRoot.root _)) =
      evalNorm K (comapPoint π xbar) (AdjoinRoot.root _) := evalNorm_comapPoint π xbar _
  have e2 : evalNorm K x (Φ (AdjoinRoot.root _)) =
      evalNorm K (comapPoint π xbar) (AdjoinRoot.root _) :=
    evalNorm_eq_of_asIdeal_eq_comap Φ hx.symm _
  rw [hπroot] at e1
  rw [hΦroot] at e2
  refine ⟨x, ?_⟩
  rw [← hqbar]
  exact (e2.trans e1.symm).trans hxbar

/-- The fibre of `B[f] ≅ B[X]/(q)` over `y ∈ Max B` is `(B ⧸ y)[X] ⧸ (q̄)` (BGR p. 172,
"`A/yA = (B/y)[X]/(q_y)`"); the sup seminorm of `f` on it is `σ(q̄)` by the fibre computation, so
`|f|_sup = sup_y σ(q_y) = max_i |b_i|_sup^{1/i}`. Lower-bound half of 3.8.1/7 (a). -/
theorem supSpectralValue_minpoly_le_supSeminorm (f : A) :
    supSpectralValue K (minpoly B f) ≤ supSeminorm K f := by
  have hfi : IsIntegral B f := Algebra.IsIntegral.isIntegral f
  have hq : (minpoly B f).Monic := minpoly.monic hfi
  refine supSpectralValue_le_of_forall K (supSeminorm_nonneg K f) fun i hi ↦ ?_
  -- it suffices that `|bᵢ(y)| ≤ |f|_sup ^ (d - i)` at every point `y` of `B`
  have hpt : ∀ y : MaximalSpectrum B, evalNorm K y ((minpoly B f).coeff i) ≤
      supSeminorm K f ^ ((minpoly B f).natDegree - i) := by
    intro y
    obtain ⟨x, hx⟩ := exists_evalNorm_eq_supSpectralValue_map K f y
    haveI : Algebra.IsAlgebraic K (B ⧸ y.asIdeal) := HasSupSeminorm.isAlgebraic y
    letI := Ideal.Quotient.field y.asIdeal
    have hdeg : ((minpoly B f).map (Ideal.Quotient.mk y.asIdeal)).natDegree =
        (minpoly B f).natDegree := hq.natDegree_map _
    calc evalNorm K y ((minpoly B f).coeff i)
        = supSeminorm K (((minpoly B f).map (Ideal.Quotient.mk y.asIdeal)).coeff i) := by
          rw [Polynomial.coeff_map]
          exact evalNorm_eq_supSeminorm_residue K y _
      _ ≤ supSpectralValue K ((minpoly B f).map (Ideal.Quotient.mk y.asIdeal)) ^
          (((minpoly B f).map (Ideal.Quotient.mk y.asIdeal)).natDegree - i) :=
          supSeminorm_coeff_le_supSpectralValue_pow K _ (hdeg ▸ hi)
      _ ≤ supSeminorm K f ^ ((minpoly B f).natDegree - i) := by
          rw [hdeg]
          exact pow_le_pow_left₀ (supSpectralValue_nonneg K _)
            (hx.symm.trans_le (evalNorm_le_supSeminorm K x f)) _
  have hsup : supSeminorm K ((minpoly B f).coeff i) ≤
      supSeminorm K f ^ ((minpoly B f).natDegree - i) :=
    supSeminorm_le_of_forall K (pow_nonneg (supSeminorm_nonneg K f) _) hpt
  calc supSeminorm K ((minpoly B f).coeff i) ^ (1 / ((minpoly B f).natDegree - i : ℝ))
      ≤ (supSeminorm K f ^ ((minpoly B f).natDegree - i)) ^
          (1 / ((minpoly B f).natDegree - i : ℝ)) :=
        Real.rpow_le_rpow (supSeminorm_nonneg K _) hsup
          (one_div_nonneg.2 (sub_nonneg.2 (Nat.cast_le.2 hi.le)))
    _ = supSeminorm K f := by
        rw [← Nat.cast_sub hi.le, one_div,
          Real.pow_rpow_inv_natCast (supSeminorm_nonneg K f) (Nat.sub_pos_of_lt hi).ne']

/-- **BGR 3.8.1/7 (a)**: `|f|_sup = max_{1≤i≤n} |b_i|_sup^{1/i}` where
`fⁿ + b₁fⁿ⁻¹ + ⋯ + bₙ = 0` is the integral equation of minimal degree of `f` over `B`. -/
theorem supSeminorm_eq_supSpectralValue_minpoly (f : A) :
    supSeminorm K f = supSpectralValue K (minpoly B f) := by
  have hqf : (minpoly B f).eval₂ (IsScalarTower.toAlgHom K B A : B →+* A) f = 0 := by
    rw [IsScalarTower.coe_toAlgHom, ← Polynomial.aeval_def]
    exact minpoly.aeval B f
  exact le_antisymm (supSeminorm_le_supSpectralValue_of_eval₂_eq_zero K
    (IsScalarTower.toAlgHom K B A) (minpoly.monic (Algebra.IsIntegral.isIntegral f)) hqf)
    (supSpectralValue_minpoly_le_supSeminorm K f)

/-- The minimal polynomial of `b • f` is the scaled minimal polynomial of `f` (BGR p. 173,
"`(bf)ⁿ + bb₁(bf)ⁿ⁻¹ + ⋯ + bⁿbₙ = 0` is the integral equation of minimal degree for any such
product `bf`"). -/
theorem minpoly_algebraMap_mul_eq_scaleRoots {b : B} (hb : b ≠ 0) (f : A) :
    minpoly B (algebraMap B A b * f) = (minpoly B f).scaleRoots b := by
  have hfi : IsIntegral B f := Algebra.IsIntegral.isIntegral f
  have hbfi : IsIntegral B (algebraMap B A b * f) := Algebra.IsIntegral.isIntegral _
  have hp : ((minpoly B f).scaleRoots b).Monic := (monic_scaleRoots_iff b).2 (minpoly.monic hfi)
  have hdvd : minpoly B (algebraMap B A b * f) ∣ (minpoly B f).scaleRoots b :=
    minpoly.isIntegrallyClosed_dvd hbfi (scaleRoots_aeval_eq_zero (minpoly.aeval B f))
  -- `f` is a root of `r(bX)`, `r` the minimal polynomial of `bf`, so `deg f ≤ deg r`
  have hC : (C b * X : B[X]) ≠ C ((C b * X : B[X]).coeff 0) := by
    intro h
    have h1 := congrArg natDegree h
    rw [natDegree_C_mul_X b hb, natDegree_C] at h1
    exact one_ne_zero h1
  have hg0 : (minpoly B (algebraMap B A b * f)).comp (C b * X) ≠ 0 := by
    rw [Ne, comp_eq_zero_iff, not_or]
    exact ⟨minpoly.ne_zero hbfi, fun h ↦ hC h.2⟩
  have hgf : aeval f ((minpoly B (algebraMap B A b * f)).comp (C b * X)) = 0 := by
    rw [aeval_comp, map_mul, aeval_C, aeval_X]
    exact minpoly.aeval B _
  have hdeg : (minpoly B f).natDegree ≤ (minpoly B (algebraMap B A b * f)).natDegree := by
    have h := natDegree_le_of_dvd (minpoly.isIntegrallyClosed_dvd hfi hgf) hg0
    rwa [natDegree_comp, natDegree_C_mul_X b hb, mul_one] at h
  exact (eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hbfi) hp hdvd
    (by rw [natDegree_scaleRoots]; exact hdeg)).symm

omit [CompleteSpace K] [IsDomain A] [Algebra B A] [IsScalarTower K B A] [Algebra.IsIntegral B A]
  [Module.IsTorsionFree B A] [HasSupSeminorm K A] [IsIntegrallyClosed B] [IsDomain B] in
/-- Scaling the roots of `p` by a `|·|_sup`-multiplicative `b` scales `σ(p)` by `|b|_sup`
(BGR p. 173: "`|bf|_sup = max |bⁱbᵢ|_sup^{1/i} = |b|_sup max |bᵢ|_sup^{1/i}`"). -/
private theorem supSpectralValue_scaleRoots
    (hB : ∀ b b' : B, supSeminorm K (b * b') = supSeminorm K b * supSeminorm K b') (p : B[X])
    (b : B) : supSpectralValue K (p.scaleRoots b) = supSeminorm K b * supSpectralValue K p := by
  have hterm : ∀ n, n < p.natDegree →
      supSeminorm K ((p.scaleRoots b).coeff n) ^ (1 / ((p.scaleRoots b).natDegree - n : ℝ)) =
        supSeminorm K b * supSeminorm K (p.coeff n) ^ (1 / (p.natDegree - n : ℝ)) := by
    intro n hn
    have hk : p.natDegree - n ≠ 0 := (Nat.sub_pos_of_lt hn).ne'
    rw [natDegree_scaleRoots, coeff_scaleRoots, hB, supSeminorm_pow K b hk, ← Nat.cast_sub hn.le,
      one_div, Real.mul_rpow (supSeminorm_nonneg K _) (pow_nonneg (supSeminorm_nonneg K b) _),
      Real.pow_rpow_inv_natCast (supSeminorm_nonneg K b) hk]
    exact mul_comm _ _
  apply le_antisymm
  · refine supSpectralValue_le_of_forall K
      (mul_nonneg (supSeminorm_nonneg K b) (supSpectralValue_nonneg K p)) fun n hn ↦ ?_
    rw [natDegree_scaleRoots] at hn
    rw [hterm n hn, ← supSpectralValueTerms_of_lt_natDegree K p hn]
    exact mul_le_mul_of_nonneg_left (supSpectralValueTerms_le_supSpectralValue K p n)
      (supSeminorm_nonneg K b)
  · rcases (supSeminorm_nonneg K b).eq_or_lt with h0 | hpos
    · rw [← h0, zero_mul]
      exact supSpectralValue_nonneg K _
    rw [← le_div_iff₀' hpos]
    refine supSpectralValue_le_of_forall K (div_nonneg (supSpectralValue_nonneg K _) hpos.le)
      fun n hn ↦ ?_
    have hn' : n < (p.scaleRoots b).natDegree := by rwa [natDegree_scaleRoots]
    rw [le_div_iff₀' hpos, ← hterm n hn, ← supSpectralValueTerms_of_lt_natDegree K _ hn']
    exact supSpectralValueTerms_le_supSpectralValue K _ n

/-- **BGR 3.8.1/7 (d)**, the if direction: if `|·|_sup` is multiplicative on `B`, then
`|φ(b) f|_sup = |b|_sup |f|_sup`. -/
theorem supSeminorm_algebraMap_mul
    (hB : ∀ b b' : B, supSeminorm K (b * b') = supSeminorm K b * supSeminorm K b') (b : B) (f : A) :
    supSeminorm K (algebraMap B A b * f) = supSeminorm K b * supSeminorm K f := by
  rcases eq_or_ne b 0 with rfl | hb
  · rw [map_zero, zero_mul, supSeminorm_zero, supSeminorm_zero, zero_mul]
  rw [supSeminorm_eq_supSpectralValue_minpoly K (B := B), minpoly_algebraMap_mul_eq_scaleRoots hb,
    supSpectralValue_scaleRoots K hB, ← supSeminorm_eq_supSpectralValue_minpoly K (B := B)]

/-- **BGR 3.8.1/7 (b)**: the maximum modulus principle transfers from `B` to `A`. -/
theorem exists_evalNorm_eq_supSeminorm_of_forall_exists
    (hB : ∀ b : B, ∃ y : MaximalSpectrum B, evalNorm K y b = supSeminorm K b) (f : A) :
    ∃ x : MaximalSpectrum A, evalNorm K x f = supSeminorm K f := by
  have hfi : IsIntegral B f := Algebra.IsIntegral.isIntegral f
  have hq : (minpoly B f).Monic := minpoly.monic hfi
  obtain ⟨i, hi, hσ⟩ := exists_supSpectralValue_eq K (minpoly.natDegree_pos hfi)
  obtain ⟨y, hy⟩ := hB ((minpoly B f).coeff i)
  obtain ⟨x, hx⟩ := exists_evalNorm_eq_supSpectralValue_map K f y
  refine ⟨x, le_antisymm (evalNorm_le_supSeminorm K x f) ?_⟩
  -- `|f|_sup = σ(q) = |bᵢ|^{1/(d-i)} = |bᵢ(y)|^{1/(d-i)} ≤ σ(q̄_y) = |f(x)|` (BGR p. 172, Ad (b))
  rw [hx, supSeminorm_eq_supSpectralValue_minpoly K (B := B), hσ, ← hy]
  haveI : Algebra.IsAlgebraic K (B ⧸ y.asIdeal) := HasSupSeminorm.isAlgebraic y
  letI := Ideal.Quotient.field y.asIdeal
  have hdeg : ((minpoly B f).map (Ideal.Quotient.mk y.asIdeal)).natDegree =
      (minpoly B f).natDegree := hq.natDegree_map _
  have hi' : i < ((minpoly B f).map (Ideal.Quotient.mk y.asIdeal)).natDegree := hdeg ▸ hi
  calc evalNorm K y ((minpoly B f).coeff i) ^ (1 / ((minpoly B f).natDegree - i : ℝ))
      = supSeminorm K (((minpoly B f).map (Ideal.Quotient.mk y.asIdeal)).coeff i) ^
          (1 / (((minpoly B f).map (Ideal.Quotient.mk y.asIdeal)).natDegree - i : ℝ)) := by
        rw [hdeg, Polynomial.coeff_map, evalNorm_eq_supSeminorm_residue K y]
    _ = supSpectralValueTerms K _ i := (supSpectralValueTerms_of_lt_natDegree K _ hi').symm
    _ ≤ supSpectralValue K _ := supSpectralValueTerms_le_supSpectralValue K _ i

/-- **BGR 3.8.1/7 (c)**: if `|·|_sup` is a norm on `B` then it is a norm on the domain `A`. -/
theorem eq_zero_of_supSeminorm_eq_zero (hB : ∀ b : B, supSeminorm K b = 0 → b = 0) {f : A}
    (hf : supSeminorm K f = 0) : f = 0 := by
  have hfi : IsIntegral B f := Algebra.IsIntegral.isIntegral f
  have hq : (minpoly B f).Monic := minpoly.monic hfi
  -- every lower coefficient of the minimal polynomial has `|bᵢ|_sup = 0`, hence vanishes
  have hcoeff : ∀ i < (minpoly B f).natDegree, (minpoly B f).coeff i = 0 := by
    intro i hi
    apply hB
    have h := supSpectralValueTerms_le_supSpectralValue K (minpoly B f) i
    rw [← supSeminorm_eq_supSpectralValue_minpoly K (B := B), hf,
      supSpectralValueTerms_of_lt_natDegree K _ hi] at h
    exact ((Real.rpow_eq_zero_iff_of_nonneg (supSeminorm_nonneg K _)).1
      (le_antisymm h (Real.rpow_nonneg (supSeminorm_nonneg K _) _))).1
  -- so `fᵈ = 0` (BGR p. 172, Ad (c): "`A` is reduced")
  have hpow : f ^ (minpoly B f).natDegree = 0 := by
    have h := minpoly.aeval B f
    rw [Polynomial.aeval_eq_sum_range, Finset.sum_range_succ, hq.coeff_natDegree, one_smul,
      Finset.sum_eq_zero fun i hi ↦ by rw [hcoeff i (Finset.mem_range.1 hi), zero_smul],
      zero_add] at h
    exact h
  exact (pow_eq_zero_iff (minpoly.natDegree_pos hfi).ne').1 hpow

/-- **BGR 3.8.1/8** in the form used by 6.2.1/4 (ii): if the values `|b|_sup`, `b ∈ B`, lie in
`‖K‖` (true for `T_d`, whose supremum norm is the Gauss norm), and the minimal polynomials over `B`
have degree at most `n`, then `|f|_sup ^ n.factorial ∈ ‖K‖` for every `f`: a uniform exponent. -/
theorem supSeminorm_pow_factorial_mem_range_norm
    (hB : ∀ b : B, supSeminorm K b ∈ Set.range (fun c : K ↦ ‖c‖)) {n : ℕ}
    (hn : ∀ f : A, (minpoly B f).natDegree ≤ n) (f : A) :
    supSeminorm K f ^ n.factorial ∈ Set.range (fun c : K ↦ ‖c‖) := by
  have hfi : IsIntegral B f := Algebra.IsIntegral.isIntegral f
  obtain ⟨i, hi, hσ⟩ := exists_supSpectralValue_eq K (minpoly.natDegree_pos hfi)
  obtain ⟨c, hc⟩ := hB ((minpoly B f).coeff i)
  have hj0 : 0 < (minpoly B f).natDegree - i := Nat.sub_pos_of_lt hi
  have hjn : (minpoly B f).natDegree - i ≤ n := (Nat.sub_le _ _).trans (hn f)
  -- `|f|_sup ^ (d - i) = |bᵢ|_sup = ‖c‖` (BGR 3.8.1/8: "`|d|^{1/m} = |f|_sup`")
  have hfj : supSeminorm K f ^ ((minpoly B f).natDegree - i) = ‖c‖ := by
    rw [supSeminorm_eq_supSpectralValue_minpoly K (B := B), hσ, ← Nat.cast_sub hi.le, one_div,
      Real.rpow_inv_natCast_pow (supSeminorm_nonneg K _) hj0.ne']
    exact hc.symm
  refine ⟨c ^ (n.factorial / ((minpoly B f).natDegree - i)), ?_⟩
  dsimp only
  rw [norm_pow, ← hfj, ← pow_mul, Nat.mul_div_cancel' (Nat.dvd_factorial hj0 hjn)]

end MinimalPolynomial

end Affinoid
