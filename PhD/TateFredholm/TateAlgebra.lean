/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.ForMathlib.RingTheory.PowerSeries.Restricted.Complete
import PhD.TateFredholm.ModelSpace

/-!
# The Tate algebra is the model space

`PowerSeries.Restricted K 1` — restricted power series at radius `1`, i.e. the Tate algebra
`K⟨X⟩` — and the model space `c(ℕ, K)` of `ModelSpace.lean` are *the same Banach
`K`-module*: membership is the same condition (`‖coeff n f‖ → 0` along the cofinite filter,
`PowerSeries.isRestricted_iff` versus `cSpace.tendsto_cofinite`), and the Gauss norm at radius
`1` is the sup norm (`PowerSeries.gaussNorm_eq` versus `cSpace.norm_eq_iSup`).  This file
records that identification and its immediate consequence, that the Tate algebra is ON-able
with orthonormal basis the monomials `{Xⁿ}`.

The two presentations are kept apart on purpose, and the seam is here rather than in either
side's development:

* the Fredholm theory of `Fredholm.lean` is *coordinatised at the definition* —
  `TateFredholm.charPowerSeries` is a sum of principal minors of `TateFredholm.matrixCoeff`,
  so it needs a distinguished basis, and every statement about it has the model space in its
  type.  `TateFredholm.IsONable` is likewise *defined* by isometry to a model space,
  following [JN] Definition 2.1.5;
* `PowerSeries.Restricted` is where the *algebra* structure lives (Gauss norm multiplicative,
  Weierstrass division, units), none of which the determinant theory uses.

So an operator whose spectral theory is wanted should be built on `c(ℕ, K)`, and this bridge
used to *read* it on `K⟨X⟩` — not the other way round.

## Main definitions

* `PowerSeries.Restricted.instAlgebra`, `PowerSeries.Restricted.instNormedAlgebra`: the normed
  `K`-algebra structure on `Restricted K c`, via the constant embedding
  `PowerSeries.Restricted.C`.  (Only the `ℤ`-module structure is inherited from the ambient
  subring, so the scalar action has to be put there.)
* `TateFredholm.cSpace.reindex`: reindexing the model space along a bijection of index types
  (the construction inlined in `TateFredholm.isONable_cSpace`).
* `TateFredholm.ofRestricted`, `TateFredholm.toRestricted`: the coefficient family of a
  restricted power series, and the restricted power series of a null family.
* `TateFredholm.restrictedEquivCSpace`: **the bridge** `K⟨X⟩ ≃ₗᵢ[K] c(ℕ, K)`.
* `TateFredholm.monomialSet`: the monomials `{Xⁿ} ⊆ K⟨X⟩`, Jacobs's basis `{zᵏ}`.

## Main results

* `TateFredholm.isONable_restricted`: the Tate algebra is ON-able, with the monomials as
  orthonormal basis — the statement [Jacobs, §1.1] and [Serre, §2] cite when they write down
  the matrix of an operator on `A_p` in the basis `{zᵏ}`.
* `TateFredholm.hasPr_restricted`: hence it has property (Pr).
-/

open Filter Topology

noncomputable section

namespace PowerSeries.Restricted

variable {K : Type*} [NormedField K] [IsUltrametricDist K] (c : ℝ) [Fact (0 < c)]

/-- The Tate algebra is a `K`-algebra via the constant embedding `C`.  (`Restricted R c` is a
subring of `R⟦X⟧`, so only the `ℤ`-module structure is inherited; over a base *field* the
scalar action is the one that matters.) -/
instance instAlgebra : Algebra K (Restricted K c) := (C c).toAlgebra

omit [Fact (0 < c)] in
theorem algebraMap_eq : algebraMap K (Restricted K c) = C c := rfl

omit [Fact (0 < c)] in
@[simp] theorem val_smul (r : K) (f : Restricted K c) :
    (r • f).1 = PowerSeries.C r * f.1 := rfl

omit [Fact (0 < c)] in
theorem coeff_smul (r : K) (f : Restricted K c) (n : ℕ) :
    coeff n (r • f).1 = r * coeff n f.1 := by
  rw [val_smul, coeff_C_mul]

/-- The Gauss norm is submultiplicative and `‖C r‖ = ‖r‖`, so the Tate algebra is a normed
`K`-algebra; this is what supplies the `NormedSpace` and `IsBoundedSMul` instances. -/
instance instNormedAlgebra : NormedAlgebra K (Restricted K c) where
  norm_smul_le r f := by
    rw [Algebra.smul_def, algebraMap_eq]
    exact (norm_mul_le _ _).trans_eq (by rw [norm_C])

end PowerSeries.Restricted

/-- The Tate radius is positive: the `Fact` that makes the Gauss-norm instances fire at
`c = 1`. -/
instance : Fact (0 < (1 : ℝ)) := ⟨one_pos⟩

namespace TateFredholm

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R]
  [NormOneClass R]

namespace cSpace

variable {I J : Type*}

/-- Reindexing the model space along a bijection of index types, as a linear isometry
equivalence.  (Both directions are precomposition with a bijection, which preserves the
cofinite filter and the range of the coordinate norms.) -/
def reindex (σ : I ≃ J) : c(I, R) ≃ₗᵢ[R] c(J, R) where
  toFun g :=
    ⟨⟨fun j => g (σ.symm j), continuous_of_discreteTopology⟩, by
      rw [Filter.cocompact_eq_cofinite]
      exact (tendsto_cofinite g).comp σ.symm.injective.tendsto_cofinite⟩
  invFun h :=
    ⟨⟨fun i => h (σ i), continuous_of_discreteTopology⟩, by
      rw [Filter.cocompact_eq_cofinite]
      exact (tendsto_cofinite h).comp σ.injective.tendsto_cofinite⟩
  map_add' _ _ := DFunLike.ext _ _ fun _ => rfl
  map_smul' _ _ := DFunLike.ext _ _ fun _ => rfl
  left_inv g := DFunLike.ext _ _ fun i => congrArg g (σ.symm_apply_apply i)
  right_inv h := DFunLike.ext _ _ fun j => congrArg h (σ.apply_symm_apply j)
  norm_map' g := by
    rw [norm_eq_iSup, norm_eq_iSup, iSup, iSup]
    congr 1
    exact σ.symm.surjective.range_comp fun i => ‖g i‖

@[simp] theorem reindex_apply (σ : I ≃ J) (g : c(I, R)) (j : J) :
    reindex σ g j = g (σ.symm j) := rfl

end cSpace

section TateAlgebra

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

omit [CompleteSpace K] in
/-- The coefficients of a restricted power series of radius `1` form a null family. -/
theorem tendsto_coeff_restricted (f : PowerSeries.Restricted K 1) :
    Tendsto (fun n : ℕ => PowerSeries.coeff n f.1) cofinite (𝓝 0) := by
  refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
  simpa using (PowerSeries.isRestricted_iff 1 f.1).mp f.2

/-- A null family of coefficients defines a restricted power series of radius `1`. -/
theorem isRestricted_mk_cSpace (g : c(ℕ, K)) :
    PowerSeries.IsRestricted 1 (PowerSeries.mk fun n => g n) := by
  rw [PowerSeries.isRestricted_iff]
  simpa using (cSpace.tendsto_cofinite g).norm

/-- The coefficient family of a restricted power series of radius `1`, as an element of the
model space.  Well defined because `IsRestricted 1` *is* the null-family condition. -/
def ofRestricted (f : PowerSeries.Restricted K 1) : c(ℕ, K) :=
  ⟨⟨fun n => PowerSeries.coeff n f.1, continuous_of_discreteTopology⟩, by
    rw [Filter.cocompact_eq_cofinite]
    exact tendsto_coeff_restricted f⟩

omit [CompleteSpace K] in
@[simp] theorem ofRestricted_apply (f : PowerSeries.Restricted K 1) (n : ℕ) :
    ofRestricted f n = PowerSeries.coeff n f.1 := rfl

/-- The restricted power series of radius `1` with a given null family of coefficients. -/
def toRestricted (g : c(ℕ, K)) : PowerSeries.Restricted K 1 :=
  ⟨PowerSeries.mk fun n => g n, isRestricted_mk_cSpace g⟩

@[simp] theorem coeff_toRestricted (g : c(ℕ, K)) (n : ℕ) :
    PowerSeries.coeff n (toRestricted g).1 = g n :=
  PowerSeries.coeff_mk _ _

/-- **The Tate algebra is the model space**: `K⟨X⟩ = PowerSeries.Restricted K 1` is `K`-linearly
isometric to `c(ℕ, K)`, by `f ↦ (coeff n f)ₙ`.

Both directions are the identity on coefficient families; the content is that `IsRestricted 1`
and the `C₀` condition are the same predicate, and that the Gauss norm at radius `1` is the sup
norm.  This is the theorem behind the informal identification "`A_p` with basis `{zᵏ}`" used
throughout [Jacobs, Ch. 1–2]. -/
def restrictedEquivCSpace : PowerSeries.Restricted K 1 ≃ₗᵢ[K] c(ℕ, K) where
  toFun := ofRestricted
  invFun := toRestricted
  map_add' f g := DFunLike.ext _ _ fun n => by
    show PowerSeries.coeff n (f.1 + g.1) = PowerSeries.coeff n f.1 + PowerSeries.coeff n g.1
    rw [map_add]
  map_smul' r f := DFunLike.ext _ _ fun n => by
    show PowerSeries.coeff n (r • f).1 = r * PowerSeries.coeff n f.1
    rw [PowerSeries.Restricted.coeff_smul]
  left_inv f := Subtype.ext (PowerSeries.ext fun n => by simp)
  right_inv g := DFunLike.ext _ _ fun n => by simp
  norm_map' f := by
    rw [cSpace.norm_eq_iSup, PowerSeries.Restricted.norm_def, PowerSeries.gaussNorm_eq]
    refine iSup_congr fun n => ?_
    show ‖PowerSeries.coeff n f.1‖ = ‖PowerSeries.coeff n f.1‖ * 1 ^ n
    rw [one_pow, mul_one]

@[simp] theorem restrictedEquivCSpace_apply (f : PowerSeries.Restricted K 1) (n : ℕ) :
    restrictedEquivCSpace f n = PowerSeries.coeff n f.1 := rfl

@[simp] theorem restrictedEquivCSpace_symm_apply (g : c(ℕ, K)) :
    restrictedEquivCSpace.symm g = toRestricted g := rfl

variable (K) in
/-- The monomials `{Xⁿ}` of the Tate algebra — the orthonormal basis `{zᵏ}` of
[Jacobs, §1.1]. -/
def monomialSet : Set (PowerSeries.Restricted K 1) :=
  Set.range fun n : ℕ => PowerSeries.Restricted.monomial 1 n (1 : K)

omit [CompleteSpace K] in
theorem monomial_injective :
    Function.Injective fun n : ℕ => PowerSeries.Restricted.monomial (1 : ℝ) n (1 : K) := by
  intro m n hmn
  by_contra hne
  have h : PowerSeries.coeff m (PowerSeries.monomial m (1 : K))
      = PowerSeries.coeff m (PowerSeries.monomial n (1 : K)) :=
    congrArg (PowerSeries.coeff m) (congrArg Subtype.val hmn)
  rw [PowerSeries.coeff_monomial, PowerSeries.coeff_monomial, if_pos rfl, if_neg hne] at h
  exact one_ne_zero h

/-- **The Tate algebra is ON-able**, with orthonormal basis the monomials `{Xⁿ}`
([JN] Definition 2.1.5; the basis `{zᵏ}` of [Jacobs, §1.1] and [Serre, §2]).  With
`TateFredholm.charPowerSeries_conj` this is what lets the Fredholm determinant of an operator
on `K⟨X⟩` be computed from its matrix in the monomial basis. -/
theorem isONable_restricted : IsONable K (PowerSeries.Restricted K 1) :=
  ⟨monomialSet K,
    ⟨restrictedEquivCSpace.trans (cSpace.reindex (Equiv.ofInjective _ monomial_injective))⟩⟩

/-- The Tate algebra has property (Pr) ([Bel] §II.1.6) — immediate from
`isONable_restricted`, recorded because (Pr) is the hypothesis of the lifting and
projectivity statements of `Pr.lean`. -/
theorem hasPr_restricted : HasPr K (PowerSeries.Restricted K 1) :=
  isONable_restricted.isPotentiallyONable.hasPr

end TateAlgebra

end TateFredholm

end
