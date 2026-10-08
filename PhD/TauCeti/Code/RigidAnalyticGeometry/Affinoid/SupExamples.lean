/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.TauCeti.Code.PadicFunctionalAnalysis.Module
import PhD.TauCeti.Code.RigidAnalyticGeometry.Affinoid.Examples
import PhD.TauCeti.Code.RigidAnalyticGeometry.Affinoid.ReductionFunctor

/-!
# Examples: supremum seminorms and reductions

Layer 2, the roadmap's Examples (§2, "Examples"), and BGR's two examples after 6.3.1/6.

* `|Xᵢ|_sup = 1` and `|m|_sup = ‖m‖` in `Tₙ` (so `|p|_sup = p⁻¹` over `ℚ_p`).
* `|X|_sup = ‖a‖` in `K⟨X⟩/(X − a)`.
* the nilpotent `ε = X` in `K⟨X⟩/(X²)` has `|ε|_sup = 0` and residue norm `1`.
* `|X|_sup = ‖a‖^{1/2}` in `K⟨X⟩/(X² − a)`.
* `X` is power-bounded and `c • X` topologically nilpotent for `‖c‖ < 1` in `K⟨X⟩`.
* `K⟨X, Y⟩/(XY − c)`, `0 < ‖c‖ < 1`: `|f₁|_sup = |f₂|_sup = 1` but `|f₁ f₂|_sup = ‖c‖` (BGR 6.2.3,
  the example after 6.2.3/5), through the points `Affinoid.Examples.annulusEval`; that this
  algebra is a domain is not formalised (plan D4).
* `K⟨X⟩/(X²)` is not uniform.
* BGR 6.3.1 Example 2: `T₁ → K × K`, `X ↦ (c, 0)` is surjective but its reduction is not.
* BGR 6.3.1 Example 1: a finite extension `L/K` is affinoid, `K̃ → L̃` is injective, and `K → L`
  is not surjective when `[L : K] > 1` (the bijectivity of `K̃ → L̃` for residue degree one is
  plan D5).
-/

open Affinoid MvPowerSeries MvPowerSeries.Restricted PowerBounded

namespace Affinoid.Examples

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

section Tate

/-- `|Xᵢ|_sup = 1` in `Tₙ`. -/
theorem supSeminorm_X (n : ℕ) (i : Fin n) :
    supSeminorm K (Restricted.X K (1 : Fin n → ℝ) i) = 1 := by
  rw [MvPowerSeries.Restricted.supSeminorm_eq_norm, Affinoid.TateAlgebra.Examples.norm_X]

/-- `|m|_sup = ‖m‖` in `Tₙ`; over `ℚ_p` this is `|p|_sup = p⁻¹`. -/
theorem supSeminorm_natCast (n m : ℕ) :
    supSeminorm K (m : TateAlgebra K n) = ‖(m : K)‖ := by
  rw [← map_natCast (algebraMap K (TateAlgebra K n)) m, supSeminorm_algebraMap]

omit [CompleteSpace K] in
/-- `X` is power-bounded in `K⟨X⟩` (`|X|_sup = 1`). -/
theorem isPowerBounded_X (n : ℕ) (i : Fin n) :
    IsPowerBounded (Restricted.X K (1 : Fin n → ℝ) i) :=
  MvPowerSeries.Restricted.isPowerBounded_X i

omit [CompleteSpace K] in
/-- `c • X` is topologically nilpotent in `K⟨X⟩` for `‖c‖ < 1`. -/
theorem isTopologicallyNilpotent_smul_X (n : ℕ) (i : Fin n) {c : K} (hc : ‖c‖ < 1) :
    IsTopologicallyNilpotent (c • Restricted.X K (1 : Fin n → ℝ) i) :=
  IsTopologicallyNilpotent.of_norm_lt_one (by
    rw [norm_smul, Affinoid.TateAlgebra.Examples.norm_X, mul_one]
    exact hc)

end Tate

section Quotients

local notation "T₁" => TateAlgebra K 1

variable (K) in
/-- The variable of `T₁`. -/
noncomputable abbrev X₁ : T₁ := Restricted.X K (1 : Fin 1 → ℝ) 0

/-- `|X|_sup = ‖a‖` in `K⟨X⟩/(X − a)` for `‖a‖ ≤ 1` (the single point `X = a`). -/
theorem supSeminorm_mk_X_span_X_sub_C {a : K} (ha : ‖a‖ ≤ 1) :
    supSeminorm K (Ideal.Quotient.mk (Ideal.span {X₁ K - Restricted.C (1 : Fin 1 → ℝ) a}) (X₁ K)) =
      ‖a‖ := by
  haveI := (IsAffinoidAlgebra.tateAlgebra_quotient 1
    (Ideal.span {X₁ K - Restricted.C (1 : Fin 1 → ℝ) a})).hasSupSeminorm
  obtain ⟨e⟩ := nonempty_algEquiv_quotient_X_sub ha
  haveI : Nontrivial (T₁ ⧸ Ideal.span {X₁ K - Restricted.C (1 : Fin 1 → ℝ) a}) :=
    e.symm.injective.nontrivial
  -- `X ≡ a` modulo `X − a`
  have hX : Ideal.Quotient.mk (Ideal.span {X₁ K - Restricted.C (1 : Fin 1 → ℝ) a}) (X₁ K) =
      algebraMap K _ a := by
    rw [IsScalarTower.algebraMap_apply K T₁, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq,
      MvPowerSeries.Restricted.algebraMap_apply]
    exact Ideal.mem_span_singleton_self _
  rw [hX, supSeminorm_algebraMap]

/-- The nilpotent `ε = X` in `K⟨X⟩/(X²)` has `|ε|_sup = 0`. -/
theorem supSeminorm_mk_X_span_X_sq :
    supSeminorm K (Ideal.Quotient.mk (Ideal.span {X₁ K ^ 2}) (X₁ K)) = 0 :=
  ((IsAffinoidAlgebra.tateAlgebra_quotient 1
    (Ideal.span {X₁ K ^ 2})).supSeminorm_eq_zero_iff_isNilpotent _).2 ⟨2, by
      rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_span_singleton_self _⟩

/-- The nilpotent `ε = X` in `K⟨X⟩/(X²)` has residue norm `1` (every `X + g X²` has Gauss norm
`≥ 1`). -/
theorem norm_mk_X_span_X_sq : ‖Ideal.Quotient.mk (Ideal.span {X₁ K ^ 2}) (X₁ K)‖ = 1 := by
  have hX : ‖X₁ K‖ = 1 := Affinoid.TateAlgebra.Examples.norm_X K 1 0
  rw [Ideal.Quotient.norm_mk_eq_norm_of_forall_le _ fun a ha ↦ ?_, hX]
  obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton'.1 ha
  rw [hX]
  -- the coefficient of `X` in `X − g X²` is `1`
  have hcoeff : MvPowerSeries.coeff (Finsupp.single 0 1) (X₁ K - g * X₁ K ^ 2).1 = 1 := by
    classical
    have hle : ¬ Finsupp.single (0 : Fin 1) 2 ≤ Finsupp.single 0 1 := fun h ↦ by
      simpa using h 0
    rw [val_sub, val_mul, val_pow, val_X, map_sub, MvPowerSeries.X_pow_eq,
      MvPowerSeries.coeff_mul_monomial, if_neg hle, sub_zero, MvPowerSeries.coeff_X, if_pos rfl]
  calc (1 : ℝ) = ‖MvPowerSeries.coeff (Finsupp.single 0 1) (X₁ K - g * X₁ K ^ 2).1‖ := by
        rw [hcoeff, norm_one]
    _ ≤ ‖X₁ K - g * X₁ K ^ 2‖ := norm_coeff_le _ _

/-- `K⟨X⟩/(X²)` is not uniform: its power-bounded elements are unbounded (it is not reduced,
`isReduced_of_isBounded_powerBounded`). -/
theorem not_isBounded_powerBounded_span_X_sq :
    haveI := (IsAffinoidAlgebra.tateAlgebra_quotient 1 (Ideal.span {X₁ K ^ 2})).hasSupSeminorm
    ¬ TopologicalRing.IsBounded
      (powerBounded K (T₁ ⧸ Ideal.span {X₁ K ^ 2}) : Set (T₁ ⧸ Ideal.span {X₁ K ^ 2})) := by
  haveI : IsClosed ((Ideal.span {X₁ K ^ 2} : Ideal T₁) : Set T₁) :=
    (IsAffinoidAlgebra.tateAlgebra (K := K) 1).isClosed_ideal _
  intro hb
  -- a bounded `Å` forces `A` reduced, but `X mod X²` is a nilpotent of residue norm one
  haveI := (IsAffinoidAlgebra.tateAlgebra_quotient 1
    (Ideal.span {X₁ K ^ 2})).isReduced_of_isBounded_powerBounded hb
  have hnil : IsNilpotent (Ideal.Quotient.mk (Ideal.span {X₁ K ^ 2}) (X₁ K)) := ⟨2, by
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton_self _⟩
  have h1 := norm_mk_X_span_X_sq (K := K)
  rw [hnil.eq_zero, norm_zero] at h1
  exact zero_ne_one h1

/-- `|X|_sup = ‖a‖^{1/2}` in `K⟨X⟩/(X² − a)` for `‖a‖ ≤ 1` (the roots of `X² − a` have spectral
norm `‖a‖^{1/2}`); over `ℚ_p` with `a = p` this is `p^{−1/2} ∉ |ℚ_p^×|`. -/
theorem supSeminorm_mk_X_span_X_sq_sub_C {a : K} (ha : ‖a‖ ≤ 1) :
    supSeminorm K
      (Ideal.Quotient.mk (Ideal.span {X₁ K ^ 2 - Restricted.C (1 : Fin 1 → ℝ) a}) (X₁ K)) =
      ‖a‖ ^ (1 / 2 : ℝ) := by
  haveI := (IsAffinoidAlgebra.tateAlgebra_quotient 1
    (Ideal.span {X₁ K ^ 2 - Restricted.C (1 : Fin 1 → ℝ) a})).hasSupSeminorm
  -- the quotient is nontrivial: `X² − a` is not a unit, its `X²`-coefficient dominates
  haveI : Nontrivial (T₁ ⧸ Ideal.span {X₁ K ^ 2 - Restricted.C (1 : Fin 1 → ℝ) a}) := by
    classical
    rw [Ideal.Quotient.nontrivial_iff, Ne, Ideal.span_singleton_eq_top]
    intro hu
    obtain ⟨-, h⟩ := MvPowerSeries.Restricted.isUnit_iff_norm_coeff_lt.1 hu
    have h2 := h (Finsupp.single 0 2) (Finsupp.single_ne_zero.2 two_ne_zero)
    have hne : (0 : Fin 1 →₀ ℕ) ≠ Finsupp.single 0 2 := (Finsupp.single_ne_zero.2 two_ne_zero).symm
    rw [val_sub, val_pow, val_X, val_C, map_sub, map_sub, MvPowerSeries.coeff_X_pow,
      MvPowerSeries.coeff_X_pow, MvPowerSeries.coeff_C, MvPowerSeries.coeff_C, if_pos rfl,
      if_neg (Finsupp.single_ne_zero.2 two_ne_zero), if_neg hne, if_pos rfl, sub_zero, zero_sub,
      norm_neg, norm_one] at h2
    exact absurd ha (not_le.2 h2)
  -- `x² = a` for `x = X mod (X² − a)`, so `|x|_sup² = |a|_sup = ‖a‖`
  have hx2 : Ideal.Quotient.mk (Ideal.span {X₁ K ^ 2 - Restricted.C (1 : Fin 1 → ℝ) a}) (X₁ K) ^ 2 =
      algebraMap K _ a := by
    rw [← map_pow, IsScalarTower.algebraMap_apply K T₁, Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq, MvPowerSeries.Restricted.algebraMap_apply]
    exact Ideal.mem_span_singleton_self _
  have hs : supSeminorm K (Ideal.Quotient.mk
      (Ideal.span {X₁ K ^ 2 - Restricted.C (1 : Fin 1 → ℝ) a}) (X₁ K)) ^ 2 = ‖a‖ := by
    rw [← supSeminorm_pow K _ two_ne_zero, hx2, supSeminorm_algebraMap]
  have h := Real.pow_rpow_inv_natCast (supSeminorm_nonneg K (Ideal.Quotient.mk
    (Ideal.span {X₁ K ^ 2 - Restricted.C (1 : Fin 1 → ℝ) a}) (X₁ K))) (two_ne_zero (α := ℕ))
  rw [hs, Nat.cast_ofNat] at h
  rw [one_div]
  exact h.symm

end Quotients

section Annulus

local notation "T₂" => TateAlgebra K 2

/-- The ideal `(XY − c)` of `K⟨X, Y⟩`. -/
noncomputable abbrev annulusIdeal (c : K) : Ideal T₂ :=
  Ideal.span {Restricted.X K (1 : Fin 2 → ℝ) 0 * Restricted.X K (1 : Fin 2 → ℝ) 1 -
    Restricted.C (1 : Fin 2 → ℝ) c}

/-- The evaluation of `K⟨X, Y⟩/(XY − c)` at a point `(x, y)` of the closed unit polydisc with
`xy = c`. -/
noncomputable def annulusEval {c x y : K} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) (hxy : x * y = c) :
    T₂ ⧸ annulusIdeal c →ₐ[K] K :=
  Ideal.Quotient.liftₐ (annulusIdeal c)
    (aeval (1 : Fin 2 → ℝ) ![x, y] (Fin.forall_fin_two.2 ⟨by simpa using hx, by simpa using hy⟩))
    fun f hf ↦ by
      have hle : annulusIdeal c ≤ RingHom.ker
          (aeval (1 : Fin 2 → ℝ) ![x, y]
            (Fin.forall_fin_two.2 ⟨by simpa using hx, by simpa using hy⟩)) := by
        refine Ideal.span_le.2 (Set.singleton_subset_iff.2 ?_)
        rw [SetLike.mem_coe, RingHom.mem_ker, map_sub, map_mul, aeval_X, aeval_X,
          ← MvPowerSeries.Restricted.algebraMap_apply, AlgHom.commutes]
        simpa [sub_eq_zero] using hxy
      exact RingHom.mem_ker.1 (hle hf)

theorem annulusEval_mk_X {c x y : K} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) (hxy : x * y = c) (i : Fin 2) :
    annulusEval hx hy hxy (Ideal.Quotient.mk (annulusIdeal c) (Restricted.X K (1 : Fin 2 → ℝ) i)) =
      ![x, y] i :=
  aeval_X (Fin.forall_fin_two.2 ⟨by simpa using hx, by simpa using hy⟩) i

/-- `|·|_sup` of the class of a variable is the norm of its value at a point, if that value has
norm one. -/
private theorem supSeminorm_mk_X_annulus_of_eval {c x y : K} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1)
    (hxy : x * y = c) (i : Fin 2) (hi : ‖![x, y] i‖ = 1) :
    supSeminorm K (Ideal.Quotient.mk (annulusIdeal c) (Restricted.X K (1 : Fin 2 → ℝ) i)) = 1 := by
  haveI := (IsAffinoidAlgebra.tateAlgebra_quotient 2 (annulusIdeal c)).hasSupSeminorm
  refine le_antisymm ?_ ?_
  · -- `≤ ‖Xᵢ‖ = 1` through the presentation (BGR p. 236)
    exact (IsAffinoidAlgebra.supSeminorm_le_norm_of_eq (Ideal.Quotient.mkₐ K (annulusIdeal c))
      rfl).trans (Affinoid.TateAlgebra.Examples.norm_X K 2 i).le
  · -- the point `ker (annulusEval …)`, where the value is `‖![x, y] i‖ = 1`
    let ψ := annulusEval hx hy hxy
    let pt : MaximalSpectrum (T₂ ⧸ annulusIdeal c) :=
      ⟨RingHom.ker ψ, isMaximal_ker_of_isAlgebraic ψ⟩
    have h := evalNorm_eq_norm_algHom ψ pt rfl
      (Ideal.Quotient.mk (annulusIdeal c) (Restricted.X K (1 : Fin 2 → ℝ) i))
    rw [annulusEval_mk_X, hi] at h
    exact h.symm.le.trans (evalNorm_le_supSeminorm K pt _)

/-- `|f₁|_sup = 1` in `K⟨X, Y⟩/(XY − c)` for `‖c‖ ≤ 1` (the point `x₁ = (X − 1, Y − c)`). -/
theorem supSeminorm_mk_X_annulus {c : K} (hc : ‖c‖ ≤ 1) :
    supSeminorm K (Ideal.Quotient.mk (annulusIdeal c) (Restricted.X K (1 : Fin 2 → ℝ) 0)) = 1 :=
  supSeminorm_mk_X_annulus_of_eval (x := 1) (y := c) (by rw [norm_one]) hc (one_mul c) 0
    (by simp)

/-- `|f₂|_sup = 1` in `K⟨X, Y⟩/(XY − c)` for `‖c‖ ≤ 1` (the point `x₂ = (X − c, Y − 1)`). -/
theorem supSeminorm_mk_Y_annulus {c : K} (hc : ‖c‖ ≤ 1) :
    supSeminorm K (Ideal.Quotient.mk (annulusIdeal c) (Restricted.X K (1 : Fin 2 → ℝ) 1)) = 1 :=
  supSeminorm_mk_X_annulus_of_eval (x := c) (y := 1) hc (by rw [norm_one]) (mul_one c) 1
    (by simp)

/-- `|f₁ f₂|_sup = |c|_sup = ‖c‖` in `K⟨X, Y⟩/(XY − c)` (BGR p. 242). -/
theorem supSeminorm_mk_X_mul_Y_annulus {c : K} (hc : ‖c‖ ≤ 1) :
    supSeminorm K (Ideal.Quotient.mk (annulusIdeal c)
      (Restricted.X K (1 : Fin 2 → ℝ) 0 * Restricted.X K (1 : Fin 2 → ℝ) 1)) = ‖c‖ := by
  haveI := (IsAffinoidAlgebra.tateAlgebra_quotient 2 (annulusIdeal c)).hasSupSeminorm
  haveI : Nontrivial (T₂ ⧸ annulusIdeal c) :=
    (annulusEval (x := 1) (y := c) (by rw [norm_one]) hc (one_mul c)).toRingHom.domain_nontrivial
  -- `XY ≡ c` modulo `XY − c`
  have h : Ideal.Quotient.mk (annulusIdeal c)
      (Restricted.X K (1 : Fin 2 → ℝ) 0 * Restricted.X K (1 : Fin 2 → ℝ) 1) = algebraMap K _ c := by
    rw [IsScalarTower.algebraMap_apply K T₂, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq,
      MvPowerSeries.Restricted.algebraMap_apply]
    exact Ideal.mem_span_singleton_self _
  rw [h, supSeminorm_algebraMap]

/-- **The supremum seminorm need not be multiplicative** (BGR 6.2.3, the example after 6.2.3/5):
on `K⟨X, Y⟩/(XY − c)` with `‖c‖ < 1` it is not. -/
theorem not_forall_supSeminorm_mul_annulus {c : K} (hc : ‖c‖ < 1) :
    ¬ ∀ f g : T₂ ⧸ annulusIdeal c,
      supSeminorm K (f * g) = supSeminorm K f * supSeminorm K g := by
  intro h
  have h1 := h (Ideal.Quotient.mk (annulusIdeal c) (Restricted.X K (1 : Fin 2 → ℝ) 0))
    (Ideal.Quotient.mk (annulusIdeal c) (Restricted.X K (1 : Fin 2 → ℝ) 1))
  rw [← map_mul, supSeminorm_mk_X_mul_Y_annulus hc.le, supSeminorm_mk_X_annulus hc.le,
    supSeminorm_mk_Y_annulus hc.le, one_mul] at h1
  exact hc.ne h1

end Annulus

section Example2

omit [CompleteSpace K] in
/-- In an ultrametric group, a sum of terms of norm at most `C` has norm at most `C`. -/
private theorem norm_le_of_hasSum_of_forall_norm_le {ι E : Type*} [SeminormedAddCommGroup E]
    [IsUltrametricDist E] {f : ι → E} {a : E} (hf : HasSum f a) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ i, ‖f i‖ ≤ C) : ‖a‖ ≤ C :=
  le_of_tendsto' ((continuous_norm.tendsto a).comp hf) fun _ ↦
    IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hC fun i _ ↦ h i

/-- For `‖g‖ ≤ 1` and `‖c‖ ≤ 1`, `‖g(c) − g(0)‖ ≤ ‖c‖`: termwise `‖gₙ (cⁿ − 0ⁿ)‖ ≤ ‖c‖`. -/
private theorem norm_aeval_sub_aeval_zero_le {c : K} (hc : ‖c‖ ≤ 1) {g : TateAlgebra K 1}
    (hg : ‖g‖ ≤ 1) :
    ‖aeval (1 : Fin 1 → ℝ) (fun _ ↦ c) (fun _ ↦ by simpa using hc) g -
      aeval (1 : Fin 1 → ℝ) (fun _ ↦ (0 : K)) (fun _ ↦ by simp) g‖ ≤ ‖c‖ := by
  have hprod : ∀ (t : Fin 1 →₀ ℕ) (x : K), (t.prod fun _ k ↦ x ^ k) = x ^ t 0 := fun t x ↦ by
    rw [Finsupp.prod_fintype _ _ fun _ ↦ pow_zero x, Fin.prod_univ_one]
  have h1 := hasSum_eval₂ (norm_algebraMap_le_one_mul (B := K))
    (norm_prod_pow_le_of_norm_le (1 : Fin 1 → ℝ) (fun _ ↦ c) fun _ ↦ by simpa using hc) g
  have h0 := hasSum_eval₂ (norm_algebraMap_le_one_mul (B := K))
    (norm_prod_pow_le_of_norm_le (1 : Fin 1 → ℝ) (fun _ ↦ (0 : K)) fun _ ↦ by simp) g
  refine norm_le_of_hasSum_of_forall_norm_le (h1.sub h0) (norm_nonneg c) fun t ↦ ?_
  show ‖algebraMap K K (MvPowerSeries.coeff t g.1) * (t.prod fun _ k ↦ c ^ k) -
    algebraMap K K (MvPowerSeries.coeff t g.1) * (t.prod fun _ k ↦ (0 : K) ^ k)‖ ≤ ‖c‖
  rw [← mul_sub, norm_mul, hprod, hprod, Algebra.algebraMap_self, RingHom.id_apply]
  have hcoef : ‖MvPowerSeries.coeff t g.1‖ ≤ 1 := (norm_coeff_le g t).trans hg
  rcases Nat.eq_zero_or_pos (t 0) with h | h
  · rw [h, pow_zero, pow_zero, sub_self, norm_zero, mul_zero]
    exact norm_nonneg c
  · rw [zero_pow h.ne', sub_zero, norm_pow]
    calc ‖MvPowerSeries.coeff t g.1‖ * ‖c‖ ^ t 0 ≤ 1 * ‖c‖ :=
          mul_le_mul hcoef (pow_le_of_le_one (norm_nonneg c) hc h.ne')
            (pow_nonneg (norm_nonneg c) _) zero_le_one
      _ = ‖c‖ := one_mul _

variable (K) in
/-- The first coordinate is a point of `K × K`: `‖x.1‖ ≤ |x|_sup`. -/
private theorem norm_fst_le_supSeminorm [HasSupSeminorm K (K × K)] (x : K × K) :
    ‖x.1‖ ≤ supSeminorm K x := by
  let pt : MaximalSpectrum (K × K) :=
    ⟨RingHom.ker (AlgHom.fst K K K), isMaximal_ker_of_isAlgebraic _⟩
  exact (evalNorm_eq_norm_algHom (AlgHom.fst K K K) pt rfl x).symm.le.trans
    (evalNorm_le_supSeminorm K pt x)

variable (K) in
/-- The second coordinate is a point of `K × K`: `‖x.2‖ ≤ |x|_sup`. -/
private theorem norm_snd_le_supSeminorm [HasSupSeminorm K (K × K)] (x : K × K) :
    ‖x.2‖ ≤ supSeminorm K x := by
  let pt : MaximalSpectrum (K × K) :=
    ⟨RingHom.ker (AlgHom.snd K K K), isMaximal_ker_of_isAlgebraic _⟩
  exact (evalNorm_eq_norm_algHom (AlgHom.snd K K K) pt rfl x).symm.le.trans
    (evalNorm_le_supSeminorm K pt x)

variable (K)

/-- BGR 6.3.1 Example 2: `φ : K⟨X⟩ → K × K`, `X ↦ (c, 0)`, for `‖c‖ ≤ 1`. -/
noncomputable def prodHom {c : K} (hc : ‖c‖ ≤ 1) : TateAlgebra K 1 →ₐ[K] K × K :=
  extendAlgHom (Algebra.ofId K (K × K)) (continuous_algebraMap K (K × K)) (fun _ ↦ (c, 0))
    (fun _ ↦ isPowerBounded_of_norm_le_one (by
      show ‖((c, 0) : K × K)‖ ≤ 1
      rw [Prod.norm_def]
      simpa using hc))

theorem prodHom_X {c : K} (hc : ‖c‖ ≤ 1) :
    prodHom K hc (Restricted.X K (1 : Fin 1 → ℝ) 0) = (c, 0) :=
  extendAlgHom_X _ _ _ _ 0

/-- `φ` is surjective ("It is easily verified that `φ` is surjective": `(1, 0)` and `(0, 1)` are
`φ(X / c)`-free: `φ(c⁻¹X) = (1, 0)`, `φ(1 − c⁻¹X) = (0, 1)` for `c ≠ 0`). -/
theorem surjective_prodHom {c : K} (hc : ‖c‖ ≤ 1) (hc0 : c ≠ 0) :
    Function.Surjective (prodHom K hc) := by
  -- `(u, v) = φ (u c⁻¹ X + v (1 − c⁻¹ X))`
  rintro ⟨u, v⟩
  refine ⟨u • (c⁻¹ • Restricted.X K (1 : Fin 1 → ℝ) 0) +
    v • (1 - c⁻¹ • Restricted.X K (1 : Fin 1 → ℝ) 0), ?_⟩
  rw [map_add, map_smul, map_smul, map_smul, map_sub, map_one, map_smul, prodHom_X]
  ext <;> simp [hc0]

/-- `K × K` with the maximum norm is an affinoid algebra (a quotient of `T₁`). -/
theorem isAffinoidAlgebra_prod : IsAffinoidAlgebra K (K × K) :=
  ⟨1, prodHom K (c := 1) (by rw [norm_one]), surjective_prodHom K _ one_ne_zero⟩

/-- `φ̃ : K̃[X] → K̃ × K̃` is not surjective for `‖c‖ < 1`, since `|φ(X)|_sup = ‖c‖ < 1` forces
`φ̃(X) = 0`, so the image of `φ̃` is the image of `K̃`, the diagonal. -/
theorem not_surjective_reductionMap_prodHom {c : K} (hc : ‖c‖ < 1) :
    haveI := (isAffinoidAlgebra_prod K).hasSupSeminorm
    ¬ Function.Surjective (reductionMap (prodHom K hc.le)) := by
  haveI := (isAffinoidAlgebra_prod K).hasSupSeminorm
  intro hsurj
  -- the coordinates of `φ` are the evaluations at `c` and at `0`
  have hcpt : ∀ i : Fin 1, ‖(fun _ ↦ c) i‖ ≤ (1 : Fin 1 → ℝ) i := fun _ ↦ by simpa using hc.le
  have h0pt : ∀ i : Fin 1, ‖(fun _ ↦ (0 : K)) i‖ ≤ (1 : Fin 1 → ℝ) i := fun _ ↦ by simp
  have hcontφ : Continuous (prodHom K hc.le) := continuous_extendAlgHom _ _ _ _
  have hfst : (AlgHom.fst K K K).comp (prodHom K hc.le) = aeval (1 : Fin 1 → ℝ) _ hcpt :=
    algHom_ext_of_continuous (continuous_fst.comp hcontφ) (continuous_aeval _) fun i ↦ by
      rw [AlgHom.comp_apply, Subsingleton.elim i 0, prodHom_X, aeval_X]
      rfl
  have hsnd : (AlgHom.snd K K K).comp (prodHom K hc.le) = aeval (1 : Fin 1 → ℝ) _ h0pt :=
    algHom_ext_of_continuous (continuous_snd.comp hcontφ) (continuous_aeval _) fun i ↦ by
      rw [AlgHom.comp_apply, Subsingleton.elim i 0, prodHom_X, aeval_X]
      rfl
  -- `(1, 0) ∈ Å` has a preimage `τ g` under `φ̃`: `|φ g − (1, 0)|_sup < 1`
  have he : ((1, 0) : K × K) ∈ powerBounded K (K × K) :=
    mem_powerBounded.2 ((supSeminorm_le_norm (K := K) _).trans (by rw [Prod.norm_def]; simp))
  obtain ⟨y, hy⟩ := hsurj (Reduction.mk K (K × K) ⟨(1, 0), he⟩)
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective y
  have hlt : supSeminorm K (prodHom K hc.le g - (1, 0)) < 1 := by
    have h := (reductionMap_mk (prodHom K hc.le) g).symm.trans hy
    rw [Ideal.Quotient.eq, mem_topologicallyNilpotent, AddSubgroupClass.coe_sub,
      coe_powerBoundedMap] at h
    exact h
  have h1 : ‖(prodHom K hc.le g).1 - 1‖ < 1 := (norm_fst_le_supSeminorm K _).trans_lt hlt
  have h2 : ‖(prodHom K hc.le g).2 - 0‖ < 1 := (norm_snd_le_supSeminorm K _).trans_lt hlt
  rw [sub_zero] at h2
  -- `‖g(c) − g(0)‖ ≤ ‖c‖ < 1` since `‖g‖ ≤ 1`
  have hg1 : ‖(g : TateAlgebra K 1)‖ ≤ 1 := Subring.mem_unitClosedBall.1
    ((SetLike.ext_iff.1 (TateAlgebra.powerBounded_eq_unitClosedBall (K := K) 1)
      (g : TateAlgebra K 1)).1 g.2)
  have h3 : ‖(prodHom K hc.le g).1 - (prodHom K hc.le g).2‖ < 1 := by
    have hc1 : (prodHom K hc.le g).1 = aeval (1 : Fin 1 → ℝ) _ hcpt (g : TateAlgebra K 1) := by
      rw [← hfst]
      rfl
    have hc2 : (prodHom K hc.le g).2 = aeval (1 : Fin 1 → ℝ) _ h0pt (g : TateAlgebra K 1) := by
      rw [← hsnd]
      rfl
    rw [hc1, hc2]
    exact (norm_aeval_sub_aeval_zero_le hc.le hg1).trans_lt hc
  -- then `1 = (g(c) − g(0)) + g(0) + (1 − g(c))` would have norm `< 1`
  have h1' : ‖1 - (prodHom K hc.le g).1‖ < 1 := by
    rw [norm_sub_rev]
    exact h1
  have hone : ‖(1 : K)‖ < 1 := by
    have heq : (1 : K) = ((prodHom K hc.le g).1 - (prodHom K hc.le g).2) +
        (prodHom K hc.le g).2 + (1 - (prodHom K hc.le g).1) := by ring
    rw [heq]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt
      (max_lt ((IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt h3 h2)) h1')
  rw [norm_one] at hone
  exact lt_irrefl _ hone

end Example2

section Example1

variable (K) (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]

/-- A finite extension of `K` is an affinoid `K`-algebra. -/
theorem isAffinoidAlgebra_of_finiteDimensional : IsAffinoidAlgebra K L := by
  -- the spectral norm makes `L` a Banach `K`-algebra; `K → L` is continuous and finite
  letI := spectralNorm.normedField K L
  letI := spectralNorm.normedAlgebra K L
  haveI : IsUltrametricDist L :=
    IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm isNonarchimedean_spectralNorm
  haveI := spectralNorm.completeSpace K L
  obtain ⟨m, b, hb⟩ := exists_isAffinoidGeneratingSystem_of_finite (Algebra.ofId K L)
    (continuous_algebraMap K L) (RingHom.finite_algebraMap.2 inferInstance)
  exact IsAffinoidAlgebra.of_isAffinoidGeneratingSystem hb

/-- BGR 6.3.1 Example 1, the injectivity: `K̃ → L̃` is injective (`K ↪ L` is an isometry for the
spectral norm, 6.3.1/2). -/
theorem injective_reductionMap_ofId :
    haveI := (isAffinoidAlgebra_of_finiteDimensional K K).hasSupSeminorm
    haveI := (isAffinoidAlgebra_of_finiteDimensional K L).hasSupSeminorm
    Function.Injective (reductionMap (Algebra.ofId K L)) := by
  haveI := (isAffinoidAlgebra_of_finiteDimensional K K).hasSupSeminorm
  haveI := (isAffinoidAlgebra_of_finiteDimensional K L).hasSupSeminorm
  -- `K → L` is an isometry for `|·|_sup` (both sides are `‖c‖`), so BGR 6.3.1/2 applies
  refine ((isAffinoidAlgebra_of_finiteDimensional K L).injective_reductionMap_iff_isometry
    (isAffinoidAlgebra_of_finiteDimensional K K) (Algebra.ofId K L)).2 fun g ↦ ?_
  have hK : supSeminorm K (algebraMap K K g) = ‖g‖ := supSeminorm_algebraMap K g
  rw [Algebra.algebraMap_self, RingHom.id_apply] at hK
  rw [Algebra.ofId_apply, supSeminorm_algebraMap, hK]

omit [IsUltrametricDist K] [CompleteSpace K] [FiniteDimensional K L] in
/-- BGR 6.3.1 Example 1, the non-surjectivity: `K → L` is not surjective when `[L : K] > 1`.
(The existence of such `L` with `K̃ → L̃` bijective, e.g. `ℚ₂(√2)/ℚ₂`, is plan D5.) -/
theorem not_surjective_algebraMap_of_one_lt_finrank (h : 1 < Module.finrank K L) :
    ¬ Function.Surjective (algebraMap K L) := by
  intro hs
  have h1 := LinearMap.finrank_range_le (Algebra.linearMap K L)
  rw [LinearMap.range_eq_top.2 hs, finrank_top, Module.finrank_self] at h1
  omega

end Example1

end Affinoid.Examples
