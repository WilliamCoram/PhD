/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.RingTheory.Spectrum.Maximal.Defs

/-!
# The supremum seminorm of an algebra over a normed field

For a commutative algebra `A` over a normed field `K` and a maximal ideal `x` of `A`, the value
`|f(x)|` of `f : A` at `x` is the spectral norm of the residue class of `f` in the residue field
`A ⧸ x`, written as the spectral value of its minimal polynomial so that no field structure on the
quotient has to be chosen. The supremum seminorm is `|f|_sup = ⨆ x, |f(x)|`.

For a Banach `K`-algebra the supremum seminorm is bounded by the norm (BGR 3.8.2/2), and a
`K`-algebra homomorphism into an algebraic normed extension field `L` of `K` has a maximal kernel
at which `|f(x)|` is the norm of the image of `f` (BGR 5.1.4/6).

Roadmap: `PhD/TauCeti/Roadmaps/RigidAnalyticGeometry/README.md`, conventions 4 and 5, §0.1.3–0.1.4
(BGR 3.8.1/1–2, 3.8.2/1–2). Tau Ceti home: `TauCeti/RingTheory/Affinoid/SupSeminorm.lean`.

## Main definitions

* `Affinoid.evalNorm K x f` — `|f(x)|`, the spectral norm of `f` in the residue field at `x`.
* `Affinoid.supSeminorm K f` — the supremum seminorm `⨆ x, |f(x)|`.

## Main results

* `Affinoid.evalNorm_le_norm`, `Affinoid.supSeminorm_le_norm` — BGR 3.8.2/1 and 3.8.2/2, and
  `Affinoid.evalNorm_map_le_norm`, `Affinoid.supSeminorm_map_le_norm` through a homomorphism out of
  a Banach algebra (the unit argument `Affinoid.isUnit_aeval_of_norm_lt_spectralValue`).
* `Affinoid.evalNorm_eq_norm_algHom` — the value at the kernel of a point.
-/

namespace Affinoid

section Defs

variable (K : Type*) [NormedField K] {A : Type*} [CommRing A] [Algebra K A]

/-- `|f(x)|` for a maximal ideal `x` of a `K`-algebra `A`: the spectral norm of the residue class
of `f` in the residue field `A ⧸ x`, as the spectral value of its minimal polynomial over `K`. It
is `0` when the residue class is not algebraic over `K`. Source: BGR 3.8.1/1–2; roadmap
convention 4. -/
noncomputable def evalNorm (x : MaximalSpectrum A) (f : A) : ℝ :=
  spectralValue (minpoly K (Ideal.Quotient.mk x.asIdeal f))

/-- The supremum seminorm of a `K`-algebra: the supremum of `|f(x)|` over the maximal spectrum.
Source: BGR 3.8.1/2; roadmap convention 5. -/
noncomputable def supSeminorm (f : A) : ℝ :=
  ⨆ x : MaximalSpectrum A, evalNorm K x f

theorem evalNorm_nonneg (x : MaximalSpectrum A) (f : A) : 0 ≤ evalNorm K x f :=
  spectralValue_nonneg _

/-- A function vanishes at the points of its zero set: `|f(x)| = 0` when `f ∈ x`. -/
theorem evalNorm_eq_zero_of_mem {x : MaximalSpectrum A} {f : A} (hf : f ∈ x.asIdeal) :
    evalNorm K x f = 0 := by
  have : Nontrivial (A ⧸ x.asIdeal) := Ideal.Quotient.nontrivial_iff.2 x.isMaximal.ne_top
  unfold evalNorm
  rw [Ideal.Quotient.eq_zero_iff_mem.2 hf, minpoly.zero, ← pow_one Polynomial.X]
  exact spectralValue_X_pow 1

end Defs

section Algebraic

variable {K : Type*} [Field K] {A : Type*} [CommRing A] [Algebra K A]
  {L : Type*} [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]

/-- The kernel of a `K`-algebra homomorphism into an algebraic extension field of `K` is a maximal
ideal. Source: BGR 5.1.4/6 ("`𝔪_x := ker h_x` is a `k`-algebraic maximal ideal"). -/
theorem isMaximal_ker_of_isAlgebraic (φ : A →ₐ[K] L) : (RingHom.ker φ).IsMaximal := by
  have hker : RingHom.ker φ.rangeRestrict = RingHom.ker φ := by
    ext a
    simp [RingHom.mem_ker, Subtype.ext_iff]
  rw [← hker]
  exact Ideal.Quotient.maximal_of_isField _ (MulEquiv.isField
    (Subalgebra.isField_of_algebraic φ.range)
    (Ideal.quotientKerAlgEquivOfSurjective φ.rangeRestrict_surjective).toMulEquiv)

omit [Algebra.IsAlgebraic K L] in
/-- The residue field at the kernel of a `K`-algebra homomorphism into a finite extension of `K`
is finite over `K`. -/
theorem finite_quotient_ker [FiniteDimensional K L] (φ : A →ₐ[K] L) :
    Module.Finite K (A ⧸ RingHom.ker φ) :=
  FiniteDimensional.of_injective (Ideal.kerLiftAlg φ).toLinearMap (Ideal.kerLiftAlg_injective φ)

end Algebraic

section Point

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : Type*} [CommRing A] [Algebra K A]
  {L : Type*} [NormedField L] [NormedAlgebra K L] [Algebra.IsAlgebraic K L]

/-- At the kernel of a `K`-algebra homomorphism `φ` into an algebraic normed extension field `L`
of `K`, the value `|f(x)|` is the norm of `φ f`. Source: BGR 5.1.4/6 ("Corresponding elements in
`Tₙ/𝔪_x` and `L` must have the same spectral norm over `k`"). -/
theorem evalNorm_eq_norm_algHom (φ : A →ₐ[K] L) (x : MaximalSpectrum A)
    (hx : x.asIdeal = RingHom.ker φ) (f : A) : evalNorm K x f = ‖φ f‖ := by
  let ψ : A ⧸ x.asIdeal →ₐ[K] L := Ideal.Quotient.liftₐ x.asIdeal φ fun a ha ↦ by
    rw [hx] at ha
    exact ha
  have hψ : Function.Injective ψ := by
    rw [injective_iff_map_eq_zero]
    intro y hy
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [Ideal.Quotient.eq_zero_iff_mem, hx]
    exact hy
  unfold evalNorm
  rw [← minpoly.algHom_eq ψ hψ, NormedAlgebra.norm_eq_spectralNorm K (φ f)]
  rfl

end Point

section SpectralValue

open Polynomial

variable {K : Type*} [NormedField K]

/-- The coefficients of a monic polynomial are bounded by powers of its spectral value. -/
private lemma norm_coeff_le_spectralValue_pow {q : K[X]} (hm : q.Monic) {n : ℕ}
    (hn : n ≤ q.natDegree) : ‖q.coeff n‖ ≤ spectralValue q ^ (q.natDegree - n) := by
  rcases hn.lt_or_eq with hlt | rfl
  · have h1 : ‖q.coeff n‖ ^ (1 / (q.natDegree - n : ℝ)) ≤ spectralValue q := by
      rw [← spectralValueTerms_of_lt_natDegree q hlt]
      exact le_ciSup (spectralValueTerms_bddAbove q) n
    have hne : ((q.natDegree - n : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.sub_pos_of_lt hlt).ne'
    calc ‖q.coeff n‖ = (‖q.coeff n‖ ^ (1 / (q.natDegree - n : ℝ))) ^ (q.natDegree - n) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _), ← Nat.cast_sub hlt.le,
            one_div, inv_mul_cancel₀ hne, Real.rpow_one]
      _ ≤ spectralValue q ^ (q.natDegree - n) :=
          pow_le_pow_left₀ (Real.rpow_nonneg (norm_nonneg _) _) h1 _
  · rw [hm.coeff_natDegree, Nat.sub_self, pow_zero, norm_one]

/-- The spectral value of the zero polynomial is zero. -/
private lemma spectralValue_zero : spectralValue (0 : K[X]) = 0 := by
  have h : spectralValueTerms (0 : K[X]) = fun _ ↦ 0 :=
    funext fun n ↦ spectralValueTerms_of_natDegree_le _ (by simp)
  rw [spectralValue, h, ciSup_const]

end SpectralValue

section Complete

open Polynomial

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- Over a complete field, the spectral value of a monic irreducible polynomial `q` raised to the
degree of `q` is the norm of its constant coefficient. -/
private lemma spectralValue_pow_natDegree {q : K[X]} (hirr : Irreducible q) (hm : q.Monic) :
    spectralValue q ^ q.natDegree = ‖q.coeff 0‖ := by
  haveI : Fact (Irreducible q) := ⟨hirr⟩
  have hq0 : q ≠ 0 := hm.ne_zero
  have hmin : minpoly K (AdjoinRoot.root q) = q := by
    rw [AdjoinRoot.minpoly_root hq0, hm.leadingCoeff, inv_one, map_one, mul_one]
  haveI : Module.Finite K (AdjoinRoot q) := (AdjoinRoot.powerBasis hq0).finite
  haveI : Algebra.IsAlgebraic K (AdjoinRoot q) := Algebra.IsAlgebraic.of_finite K _
  have h := spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow K (AdjoinRoot q) (AdjoinRoot.root q)
  have hsv : spectralNorm K (AdjoinRoot q) (AdjoinRoot.root q) = spectralValue q := by
    show spectralValue (minpoly K (AdjoinRoot.root q)) = _
    rw [hmin]
  rw [hmin] at h
  have hr : (q.natDegree : ℝ) ≠ 0 := Nat.cast_ne_zero.2
    (natDegree_pos_iff_degree_pos.2 (degree_pos_of_irreducible hirr)).ne'
  rw [← hsv, h, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _), one_div,
    inv_mul_cancel₀ hr, Real.rpow_one]

end Complete

section Banach

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : Type*} [NormedCommRing A] [NormedAlgebra K A] [IsUltrametricDist A] [CompleteSpace A]

/-- In a Banach algebra over `K`, `q(f)` is a unit for a monic irreducible `q` with
`‖f‖ < σ(q)`: the constant term of `q` dominates the other terms of `q(f)`. Source: BGR 3.8.2/1;
Bosch 1.2/12 (the contraction argument through units). -/
theorem isUnit_aeval_of_norm_lt_spectralValue {q : Polynomial K} (hirr : Irreducible q)
    (hm : q.Monic) {f : A} (hlt : ‖f‖ < spectralValue q) : IsUnit (Polynomial.aeval f q) := by
  have hr : 0 < q.natDegree := hirr.natDegree_pos
  have hσ : 0 < spectralValue q := (norm_nonneg f).trans_lt hlt
  have hpow : spectralValue q ^ q.natDegree = ‖q.coeff 0‖ := spectralValue_pow_natDegree hirr hm
  have hc : q.coeff 0 ≠ 0 := by
    intro h
    rw [h, norm_zero] at hpow
    exact (pow_pos hσ _).ne' hpow
  set w := ∑ i ∈ Finset.range q.natDegree, q.coeff (i + 1) • f ^ (i + 1) with hw
  have haeval : Polynomial.aeval f q = q.coeff 0 • (1 : A) + w := by
    rw [Polynomial.aeval_eq_sum_range, Finset.sum_range_succ', pow_zero, add_comm]
  have hwlt : ‖w‖ < spectralValue q ^ q.natDegree := by
    obtain ⟨i, hi, hle⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty
      (Finset.nonempty_range_iff.2 hr.ne') fun i ↦ q.coeff (i + 1) • f ^ (i + 1)
    refine hle.trans_lt ?_
    have hi' : i + 1 ≤ q.natDegree := Finset.mem_range.1 hi
    calc ‖q.coeff (i + 1) • f ^ (i + 1)‖ ≤ ‖q.coeff (i + 1)‖ * ‖f ^ (i + 1)‖ := norm_smul_le _ _
      _ ≤ spectralValue q ^ (q.natDegree - (i + 1)) * ‖f‖ ^ (i + 1) :=
          mul_le_mul (norm_coeff_le_spectralValue_pow hm hi') (norm_pow_le' f i.succ_pos)
            (norm_nonneg _) (pow_nonneg hσ.le _)
      _ < spectralValue q ^ (q.natDegree - (i + 1)) * spectralValue q ^ (i + 1) :=
          mul_lt_mul_of_pos_left (pow_lt_pow_left₀ hlt (norm_nonneg f) i.succ_ne_zero)
            (pow_pos hσ _)
      _ = spectralValue q ^ q.natDegree := by rw [← pow_add, Nat.sub_add_cancel hi']
  have hsmall : ‖-((q.coeff 0)⁻¹ • w)‖ < 1 := by
    rw [norm_neg]
    calc ‖(q.coeff 0)⁻¹ • w‖ ≤ ‖(q.coeff 0)⁻¹‖ * ‖w‖ := norm_smul_le _ _
      _ < ‖(q.coeff 0)⁻¹‖ * spectralValue q ^ q.natDegree :=
          mul_lt_mul_of_pos_left hwlt (norm_pos_iff.2 (inv_ne_zero hc))
      _ = 1 := by rw [hpow, norm_inv, inv_mul_cancel₀ (norm_ne_zero_iff.2 hc)]
  have h2 : Polynomial.aeval f q =
      algebraMap K A (q.coeff 0) * (1 - -((q.coeff 0)⁻¹ • w)) := by
    rw [haeval, sub_neg_eq_add, mul_add, mul_one, Algebra.smul_def (q.coeff 0)⁻¹ w, ← mul_assoc,
      ← map_mul, mul_inv_cancel₀ hc, map_one, one_mul, Algebra.smul_def, mul_one]
  rw [h2]
  exact ((isUnit_iff_ne_zero.2 hc).map (algebraMap K A)).mul
    (isUnit_one_sub_of_norm_lt_one hsmall)

/-- The value at a point of the image of `f` under a `K`-algebra homomorphism `φ` out of a Banach
algebra is bounded by `‖f‖`: for the minimal polynomial `q` of `φ(f)` at `x`, `φ(q(f))` lies in
`x`, so `q(f)` is not a unit. Source: BGR 3.8.2/1, through `φ`. -/
theorem evalNorm_map_le_norm {B : Type*} [CommRing B] [Algebra K B] (φ : A →ₐ[K] B)
    (x : MaximalSpectrum B) (f : A) : evalNorm K x (φ f) ≤ ‖f‖ := by
  have hmax := x.isMaximal
  letI : Field (B ⧸ x.asIdeal) := Ideal.Quotient.field x.asIdeal
  set y := Ideal.Quotient.mk x.asIdeal (φ f)
  show spectralValue (minpoly K y) ≤ ‖f‖
  by_cases hint : IsIntegral K y
  swap
  · rw [minpoly.eq_zero hint, spectralValue_zero]
    exact norm_nonneg f
  refine le_of_not_gt fun hlt ↦ ?_
  have hunit := (isUnit_aeval_of_norm_lt_spectralValue (minpoly.irreducible hint)
    (minpoly.monic hint) hlt).map φ
  rw [← Polynomial.aeval_algHom_apply] at hunit
  have hmem : Polynomial.aeval (φ f) (minpoly K y) ∈ x.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have h3 := Polynomial.aeval_algHom_apply (Ideal.Quotient.mkₐ K x.asIdeal) (φ f) (minpoly K y)
    rw [Ideal.Quotient.mkₐ_eq_mk] at h3
    rw [← h3]
    exact minpoly.aeval K y
  exact hmax.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem hunit)

/-- In a Banach algebra over `K` the value of a function at a point is bounded by its norm:
`|f(x)| ≤ ‖f‖`. Source: BGR 3.8.2/1; Bosch 1.2/12 (the contraction argument through units). -/
theorem evalNorm_le_norm (x : MaximalSpectrum A) (f : A) : evalNorm K x f ≤ ‖f‖ :=
  evalNorm_map_le_norm (AlgHom.id K A) x f

theorem bddAbove_range_evalNorm (f : A) :
    BddAbove (Set.range fun x : MaximalSpectrum A ↦ evalNorm K x f) :=
  ⟨‖f‖, by
    rintro _ ⟨x, rfl⟩
    exact evalNorm_le_norm x f⟩

/-- The supremum seminorm of the image of `f` under a `K`-algebra homomorphism out of a Banach
algebra is bounded by `‖f‖`. Source: BGR 3.8.2/2, through `φ`. -/
theorem supSeminorm_map_le_norm {B : Type*} [CommRing B] [Algebra K B] (φ : A →ₐ[K] B) (f : A) :
    supSeminorm K (φ f) ≤ ‖f‖ := by
  rcases isEmpty_or_nonempty (MaximalSpectrum B) with h | h
  · rw [supSeminorm, Real.iSup_of_isEmpty]
    exact norm_nonneg f
  · exact ciSup_le fun x ↦ evalNorm_map_le_norm φ x f

/-- In a Banach algebra over `K` the supremum seminorm is bounded by the norm.
Source: BGR 3.8.2/2. -/
theorem supSeminorm_le_norm (f : A) : supSeminorm K f ≤ ‖f‖ :=
  supSeminorm_map_le_norm (AlgHom.id K A) f

end Banach

end Affinoid
