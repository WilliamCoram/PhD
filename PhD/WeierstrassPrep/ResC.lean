import PhD.ToPR.Restricted
import PhD.ToPR.MvRestricted
import PhD.ToPR.GaussNorm
import PhD.ToPR.MvGaussNorm

section Constant
-- TODO: Move this section intro restricted
--  generalise for MvRestricted, and have

namespace PowerSeries.Restricted
-- notsure if this namespace should be PowerSeries.Restricted or Restricted
-- same as MvPowerSeries.Restricted or MvRestricted

variable {S : Type*} [NormedCommRing S] [IsUltrametricDist S]

@[simp] lemma C_val (c : ℝ) (a : S) : (C c a).1 = PowerSeries.C a := rfl

lemma coeff_C (c : ℝ) (a : S) (n : ℕ) :
    PowerSeries.coeff n (C c a).1 = if n = 0 then a else 0 := by
  rw [C_val, PowerSeries.coeff_C]

@[simp] lemma coeff_zero_C (c : ℝ) (a : S) : PowerSeries.coeff 0 (C c a).1 = a := by
  rw [C_val, PowerSeries.coeff_zero_C]

lemma C_one (c : ℝ) : C c (1 : S) = 1 := Subtype.ext (map_one PowerSeries.C)

lemma C_mul (c : ℝ) (a b : S) : C c (a * b) = C c a * C c b :=
  Subtype.ext (map_mul PowerSeries.C a b)

/-- `C c` sends units to units. -/
lemma C_isUnit (c : ℝ) {a : S} (ha : IsUnit a) : IsUnit (C c a) := by
  obtain ⟨u, rfl⟩ := ha
  exact ⟨⟨C c u.val, C c u.inv, by rw [← C_mul, u.val_inv, C_one],
    by rw [← C_mul, u.inv_val, C_one]⟩, rfl⟩

@[simp]
lemma C_mul_series (c : ℝ) (a : S) (g : PowerSeries.Restricted S c) :
    (C c a * g).1 = (C c a).1 * g.1 := by
  rfl

/-- Coefficients of `C c a * g`: scaling by the constant `a`. -/
lemma coeff_C_mul (c : ℝ) (a : S) (g : PowerSeries.Restricted S c) (n : ℕ) :
    PowerSeries.coeff n (C c a * g).1 = a * PowerSeries.coeff n g.1 := by
  rw [C_mul_series, C_val, PowerSeries.coeff_C_mul]

/-- The Gauss norm of a constant series is the norm of the constant (only the `0`-th coefficient
is nonzero, with value `a` and weight `c ^ 0 = 1`). -/
lemma norm_C (c : ℝ) [StrongPos (fun _ : Unit ↦ c)] (a : S) : ‖C c a‖ = ‖a‖ := by
  simp_rw [Restricted.norm_eq, gaussNorm_eq, coeff_C]
  have hle : ∀ i : ℕ, ‖if i = 0 then a else 0‖ * c ^ i ≤ ‖a‖ := by
    intro i
    split_ifs with h
    · simp [h]
    · simp
  refine le_antisymm (ciSup_le hle) ?_
  exact le_ciSup_of_le ⟨‖a‖, by rintro _ ⟨i, rfl⟩; exact hle i⟩ 0 (by simp)

/-- Multiplying a polynomial-as-restricted-series by the constant `C c a` scales the polynomial
by `Polynomial.C a`. -/
lemma C_mul_toRestricted (c : ℝ) (a : S) (r : Polynomial S) :
    C c a * Polynomial.toRestricted c r = Polynomial.toRestricted c (Polynomial.C a * r) := by
  apply Subtype.ext
  simp [Polynomial.toRestricted]
-- maybe should be in ResPoly instead... can decide when I clean Restricted/MvRestricted files

end PowerSeries.Restricted

end Constant
