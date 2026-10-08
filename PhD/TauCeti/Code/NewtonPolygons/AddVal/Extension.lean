/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.Topology.Algebra.Valued.ValuedField
import PhD.TauCeti.Code.NewtonPolygons.AddVal.Normed

/-!
# Additive valuations of extensions and completions

How the additive valuations of `Normed.lean` behave along a normed field extension `L/K` and
along completion.

* Any normed `K`-algebra field `L` has `‖algebraMap K L x‖ = ‖x‖`, so `normAddVal L` restricts to
  `normAddVal K` (§1.5.1; Mathlib's `IsUltrametricDist.of_normedAlgebra` and `norm_algebraMap'`
  supply the ultrametricity of `L` and the norm extension).
* If both `K` and `L` are discretely valued, the `ℤ`-valued additive valuation of `L` restricted
  to `K` is `e` times that of `K`, where `e` is the additive valuation in `L` of a uniformiser of
  `K` — the ramification index — and `normAddValZ L` is `e` times the `ℚ`-valued valuation of `L`
  normalised at that uniformiser (§1.3.6).
* If `K` is complete and `L/K` is algebraic, the norm of `L` is the spectral norm, so
  `‖x‖ ^ n = ‖a₀‖` for the minimal polynomial `Xⁿ + ⋯ + a₀` of `x`: commensurability is inherited
  from `K`, and `normAddValQ L (algebraMap K L π)` restricts to `normAddValQ K π` (§1.5.2).
* Completion preserves the value group, so commensurability passes to the completion (§1.5.3).

Roadmap: `PhD/TauCeti/Roadmaps/NewtonPolygons/README.md`, §1.3.6, §1.5.1–§1.5.3. Tau Ceti home:
`TauCeti/Analysis/Normed/Unbundled/SpectralNorm/AddVal.lean` and
`TauCeti/Topology/Algebra/Valued/Completion/AddVal.lean`.
-/

open scoped NNReal WithZero

/-! ### Completion preserves the value group -/

namespace Valued

variable {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀] [hv : Valued K Γ₀]

/-- **Commensurability passes to the completion**: every value of the completion is a value of the
field, so a normalising element of `K` is a normalising element of its completion. -/
theorem isCommensurable_completion (π : K) [hv.v.IsCommensurable π] :
    (Valued.v : Valuation (UniformSpace.Completion K) Γ₀).IsCommensurable
      (π : UniformSpace.Completion K) := by
  have hπ : (Valued.v : Valuation K Γ₀).IsCommensurable π := inferInstance
  refine ⟨?_, ?_, fun x hx ↦ ?_⟩
  · rw [Valued.valuedCompletion_apply]; exact hπ.val_pos
  · rw [Valued.valuedCompletion_apply]; exact hπ.val_lt_one
  · obtain ⟨r, hr⟩ := Valued.exists_coe_eq_v x
    have hxr : Valued.v x = Valued.v r := hr
    obtain ⟨m, n, hn, e⟩ := hπ.exists_zpow_eq r (hxr ▸ hx)
    exact ⟨m, n, hn, by rw [hxr, Valued.valuedCompletion_apply, e]⟩

end Valued

namespace NormedField

open Valuation MonoidWithZeroHom WithZero

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L] [NormedAlgebra K L]

/-! ### The unnormalised valuation restricts -/

/-- The real additive valuation of `L` restricts to that of `K`. -/
theorem normAddVal_algebraMap (x : K) : normAddVal L (algebraMap K L x) = normAddVal K x := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [map_zero, normAddVal_zero, normAddVal_zero]
  rw [normAddVal_apply_of_ne_zero L ((map_ne_zero (algebraMap K L)).mpr hx),
    normAddVal_apply_of_ne_zero K hx, norm_algebraMap']

/-! ### Discretely valued extensions: the ramification index -/

section Discrete

variable [(valuation (K := K)).IsRankOneDiscrete] [(valuation (K := L)).IsRankOneDiscrete]

/-- The image of a uniformiser of `K` has a positive integral additive valuation in `L`: the
ramification index of `L/K`. -/
theorem exists_normAddValZ_algebraMap_eq {π : K} (hπ : IsUniformizer (valuation (K := K)) π) :
    ∃ e : ℕ, 0 < e ∧ normAddValZ L (algebraMap K L π) = ((e : ℤ) : WithTop ℤ) := by
  have hπ0 : algebraMap K L π ≠ 0 := (map_ne_zero _).mpr hπ.ne_zero
  obtain ⟨d, hd⟩ := WithTop.ne_top_iff_exists.mp ((normAddValZ_eq_top L).not.mpr hπ0)
  have hv := (IsRankOneDiscrete.addValZ_eq_iff (valuation (K := L)) _ d).mp hd.symm
  have hlt : valuation (algebraMap K L π) < 1 := by
    rw [valuation_apply, nnnorm_algebraMap']; exact hπ.val_lt_one
  have hg1 : ((IsRankOneDiscrete.generator (valuation (K := L)) : ℝ≥0ˣ) : ℝ≥0) < 1 := by
    simpa using Units.val_lt_val.mpr (IsRankOneDiscrete.generator_lt_one (valuation (K := L)))
  have hg0 : (0 : ℝ≥0) < (IsRankOneDiscrete.generator (valuation (K := L)) : ℝ≥0ˣ) :=
    pos_iff_ne_zero.mpr (Units.ne_zero _)
  rw [hv, Units.val_zpow_eq_zpow_val] at hlt
  have hd0 : 0 < d := (zpow_lt_one_iff_right_of_lt_one₀ hg0 hg1).mp hlt
  exact ⟨d.toNat, by omega, by rw [Int.toNat_of_nonneg hd0.le]; exact hd.symm⟩

/-- **The ramification formula**: if a uniformiser of `K` has additive valuation `e` in `L`, then on
`K` the `ℤ`-valued additive valuation of `L` is `e` times that of `K`. -/
theorem normAddValZ_algebraMap {π : K} (hπ : IsUniformizer (valuation (K := K)) π) {e : ℤ}
    (he : normAddValZ L (algebraMap K L π) = (e : WithTop ℤ)) (x : K) :
    normAddValZ L (algebraMap K L x) = WithTop.map (fun k : ℤ ↦ e * k) (normAddValZ K x) := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [map_zero, normAddValZ_zero, normAddValZ_zero, WithTop.map_top]
  obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp ((normAddValZ_eq_top K).not.mpr hx)
  rw [← hk, WithTop.map_coe]
  have hxK : ‖x‖ = ‖π‖ ^ k := (normAddValZ_eq_iff_of_isUniformizer K hπ x k).mp hk.symm
  have hπL := (IsRankOneDiscrete.addValZ_eq_iff (valuation (K := L)) _ e).mp he
  refine (IsRankOneDiscrete.addValZ_eq_iff (valuation (K := L)) _ (e * k)).mpr ?_
  rw [zpow_mul, Units.val_zpow_eq_zpow_val, ← hπL, valuation_apply, valuation_apply,
    ← NNReal.coe_inj, NNReal.coe_zpow, coe_nnnorm, coe_nnnorm, norm_algebraMap', norm_algebraMap',
    hxK]

/-- The image of a uniformiser of `K` is a normalising element of `L`. -/
theorem isCommensurable_algebraMap_of_isRankOneDiscrete {π : K}
    (hπ : IsUniformizer (valuation (K := K)) π) :
    (valuation (K := L)).IsCommensurable (algebraMap K L π) := by
  have h0 : valuation (algebraMap K L π) ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr ((map_ne_zero _).mpr hπ.ne_zero)
  have h1 : valuation (algebraMap K L π) < 1 := by
    rw [valuation_apply, nnnorm_algebraMap']; exact hπ.val_lt_one
  exact IsRankOneDiscrete.isCommensurable_of_lt_one _ h0 h1

/-- **`normAddValZ L` is `e` times the `ℚ`-valued valuation of `L` normalised at a uniformiser of
`K`**, where `e` is the ramification index. -/
theorem map_intCast_normAddValZ_eq_map_normAddValQ {π : K}
    (hπ : IsUniformizer (valuation (K := K)) π) {e : ℤ}
    (he : normAddValZ L (algebraMap K L π) = (e : WithTop ℤ))
    [(valuation (K := L)).IsCommensurable (algebraMap K L π)] (y : L) :
    WithTop.map (fun n : ℤ ↦ (n : ℚ)) (normAddValZ L y)
      = WithTop.map (fun q : ℚ ↦ (e : ℚ) * q) (normAddValQ L (algebraMap K L π) y) := by
  obtain ⟨e', he'0, he'⟩ := exists_normAddValZ_algebraMap_eq (L := L) hπ
  have heq : e = e' := by
    rw [he'] at he; exact (WithTop.coe_inj.mp he).symm
  have he_pos : 0 < e := by rw [heq]; exact_mod_cast he'0
  rcases eq_or_ne y 0 with rfl | hy
  · rw [normAddValZ_zero, normAddValQ_zero, WithTop.map_top, WithTop.map_top]
  obtain ⟨d, hd⟩ := WithTop.ne_top_iff_exists.mp ((normAddValZ_eq_top L).not.mpr hy)
  have hyv := (IsRankOneDiscrete.addValZ_eq_iff (valuation (K := L)) y d).mp hd.symm
  have hπv := (IsRankOneDiscrete.addValZ_eq_iff (valuation (K := L)) _ e).mp he
  have hpow : valuation y ^ e = valuation (algebraMap K L π) ^ d := by
    rw [hyv, hπv, ← Units.val_zpow_eq_zpow_val, ← Units.val_zpow_eq_zpow_val, ← zpow_mul,
      ← zpow_mul, mul_comm]
  rw [← hd, WithTop.map_coe, normAddValQ,
    addValQ_eq_of_zpow _ _ ((Valuation.ne_zero_iff _).mpr hy) he_pos hpow, WithTop.map_coe,
    WithTop.coe_inj]
  have he0 : (e : ℚ) ≠ 0 := by exact_mod_cast he_pos.ne'
  field_simp

end Discrete

/-! ### Algebraic extensions of a complete field: commensurability is inherited -/

section Algebraic

-- `[CompleteSpace K] [Algebra.IsAlgebraic K L]` are written on each declaration: an `instance`
-- whose body does not use a section hypothesis would silently drop it (see `decomposition.md`, D1).

omit [IsUltrametricDist L] in
/-- **The norm of an algebraic element is read off its minimal polynomial**: for the minimal
polynomial `Xⁿ + ⋯ + a₀` of `x`, `‖x‖ ^ n = ‖a₀‖` (BGR 3.2.4/3). -/
theorem norm_pow_natDegree_minpoly [CompleteSpace K] [Algebra.IsAlgebraic K L] (x : L) :
    ‖x‖ ^ (minpoly K x).natDegree = ‖(minpoly K x).coeff 0‖ := by
  rw [NormedAlgebra.norm_eq_spectralNorm K x, spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow,
    one_div, Real.rpow_inv_natCast_pow (norm_nonneg _)
      (minpoly.natDegree_pos (Algebra.IsIntegral.isIntegral x)).ne']

/-- **Commensurability is inherited by algebraic extensions**: if `K` is commensurable at `π`, then
`L` is commensurable at `algebraMap K L π`. -/
instance isCommensurable_algebraMap [CompleteSpace K] [Algebra.IsAlgebraic K L] (π : K)
    [(valuation (K := K)).IsCommensurable π] :
    (valuation (K := L)).IsCommensurable (algebraMap K L π) := by
  have hπ : (valuation (K := K)).IsCommensurable π := inferInstance
  refine ⟨?_, ?_, fun x hx ↦ ?_⟩
  · rw [valuation_apply, nnnorm_algebraMap']; exact hπ.val_pos
  · rw [valuation_apply, nnnorm_algebraMap']; exact hπ.val_lt_one
  have hx0 : x ≠ 0 := (Valuation.ne_zero_iff _).mp hx
  have hint := Algebra.IsIntegral.isIntegral (R := K) x
  have hn : 0 < (minpoly K x).natDegree := minpoly.natDegree_pos hint
  have ha₀ : (minpoly K x).coeff 0 ≠ 0 := minpoly.coeff_zero_ne_zero hint hx0
  obtain ⟨m, k, hk, e⟩ := hπ.exists_zpow_eq _ ((Valuation.ne_zero_iff _).mpr ha₀)
  have hxn : ‖x‖₊ ^ (minpoly K x).natDegree = ‖(minpoly K x).coeff 0‖₊ := by
    rw [← NNReal.coe_inj]; push_cast; exact norm_pow_natDegree_minpoly x
  refine ⟨m, ((minpoly K x).natDegree : ℤ) * k, mul_pos (by exact_mod_cast hn) hk, ?_⟩
  rw [valuation_apply, valuation_apply, nnnorm_algebraMap', zpow_mul, zpow_natCast, hxn]
  exact e

/-- The `ℚ`-valued additive valuation of `L` normalised at `algebraMap K L π` restricts to the
`ℚ`-valued additive valuation of `K` normalised at `π`. -/
theorem normAddValQ_algebraMap [CompleteSpace K] [Algebra.IsAlgebraic K L] (π : K)
    [(valuation (K := K)).IsCommensurable π] (x : K) :
    normAddValQ L (algebraMap K L π) (algebraMap K L x) = normAddValQ K π x := by
  have hπ : (valuation (K := K)).IsCommensurable π := inferInstance
  rcases eq_or_ne x 0 with rfl | hx
  · rw [map_zero, normAddValQ_zero, normAddValQ_zero]
  obtain ⟨m, n, hn, e⟩ := hπ.exists_zpow_eq x ((Valuation.ne_zero_iff _).mpr hx)
  have e' : valuation (algebraMap K L x) ^ n = valuation (algebraMap K L π) ^ m := by
    rw [valuation_apply, valuation_apply, nnnorm_algebraMap', nnnorm_algebraMap']; exact e
  rw [normAddValQ, normAddValQ,
    addValQ_eq_of_zpow _ _ ((Valuation.ne_zero_iff _).mpr ((map_ne_zero _).mpr hx)) hn e',
    addValQ_eq_of_zpow _ _ ((Valuation.ne_zero_iff _).mpr hx) hn e]

end Algebraic

end NormedField
