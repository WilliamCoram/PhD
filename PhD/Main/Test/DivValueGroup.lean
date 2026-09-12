import PhD.WeierstrassPrep.WPrep_gen
import PhD.Main.Test.addVals2
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Divisible hulls of subgroups, and the divisible value group

The "divisible closure of the value group" is a special case of a general group-theoretic
construction: the **divisible hull** of a subgroup.  This file defines that hull in full
generality (additively, for any `AddCommGroup`), develops its API, and then *applies* it to the
exponent group of a normed field to recover — and relate — the two descriptions of the divisible
value group used elsewhere in the project.

## §1  The general construction

For an additive subgroup `H ≤ G`, its divisible hull

  `H.divisibleHull := { g | ∃ n ≠ 0, n • g ∈ H }`

is again a subgroup (`AddSubgroup.divisibleHull`), contains `H` (`le_divisibleHull`), is monotone,
and is *saturated*: `n • g ∈ H.divisibleHull` (with `n ≠ 0`) already forces `g ∈ H.divisibleHull`
(`mem_divisibleHull_of_nsmul_mem`).  It is the smallest subgroup `⊇ H` in which "some nonzero
multiple lands in `H`" implies membership — the additive divisible closure of `H` inside `G`.

## §2  Application to a normed field

The value group `Γ = ‖K˟‖` of a normed field, read additively through `log`, is the exponent group

  `logValueGroup K := { log ‖x‖ : x ≠ 0 } ≤ (ℝ, +)`.

Feeding it to the general construction gives `(logValueGroup K).divisibleHull`, the **divisible
exponent group**, and exponentiating gives the admissible radii — the object the Weierstrass /
Newton-polygon theory actually consumes:

  `expDivisibleValueGroup K := exp '' (logValueGroup K).divisibleHull ⊆ ℝ_{>0}`.

The bridge to `WPrep_gen`'s multiplicative predicate is `mem_expDivisibleValueGroup_iff`: for
`0 < c`,

  `c ∈ expDivisibleValueGroup K  ↔  MemDivisibleValueGroup K c`   (`= ∃ n ≠ 0, ∃ x, ‖x‖ = cⁿ`).

Equivalently `MemDivisibleValueGroup K c ↔ log c ∈ (logValueGroup K).divisibleHull`
(`memDivisibleValueGroup_iff_log`, for `0 < c`): `c` is a divisible value **iff its exponent lies
in the divisible hull of the exponent group** — the multiplication `cⁿ` upstairs is the integer
scaling `n • log c` downstairs.

## §3  Connection to the additive valuation `addVal`

`logValueGroup K` is the negated range of the canonical additive valuation
`RankOne.addVal (NormedField.valuation)` (the object `test.lean` wraps as `NewtonPolygon.addVal`,
`x ↦ -log ‖x‖`): `mem_logValueGroup_iff_addVal`, and hence `memDivisibleValueGroup_iff_addVal`,
phrase everything directly in `addVal` language.

## Example

Over `ℚ_p` the value group is `p^ℤ`, so `logValueGroup = ℤ · log p`, its divisible hull is
`ℚ · log p`, and `expDivisibleValueGroup = p^ℚ`.  A slope-`½` radius `p^{1/2}` lands there with
`n = 2`, `x = p⁻¹`.  Newton-polygon slopes are rational, so their radii are always in `p^ℚ`
(`NewtonPolygon.memDivisibleValueGroup_exp_slope`).

## Status

Complete — no `sorry`.  Imports only `WPrep_gen` (for `MemDivisibleValueGroup`) and `addVals2`
(for `RankOne.addVal`), so it sits low in the dependency graph and both files can later be phrased
against this API.
-/

open scoped NNReal

/-! ## §1  The divisible hull of an additive subgroup (general) -/

namespace AddSubgroup

variable {G : Type*} [AddCommGroup G]

/-- The **divisible hull** of `H ≤ G`: the elements some nonzero integer multiple of which lands
in `H`.  A subgroup (`add_mem'` uses `(n·m) • (a+b) = m • (n • a) + n • (m • b)`), containing `H`
and saturated under division. -/
def divisibleHull (H : AddSubgroup G) : AddSubgroup G where
  carrier := {g | ∃ n : ℕ, n ≠ 0 ∧ n • g ∈ H}
  zero_mem' := ⟨1, one_ne_zero, by simp⟩
  add_mem' := by
    rintro a b ⟨n, hn, ha⟩ ⟨m, hm, hb⟩
    refine ⟨n * m, mul_ne_zero hn hm, ?_⟩
    have e1 : (n * m) • a = m • (n • a) := by rw [mul_comm, mul_smul]
    have e2 : (n * m) • b = n • (m • b) := by rw [mul_smul]
    rw [smul_add, e1, e2]
    exact H.add_mem (nsmul_mem ha m) (nsmul_mem hb n)
  neg_mem' := by
    rintro a ⟨n, hn, ha⟩
    exact ⟨n, hn, by rw [smul_neg]; exact H.neg_mem ha⟩

@[simp] lemma mem_divisibleHull {H : AddSubgroup G} {g : G} :
    g ∈ H.divisibleHull ↔ ∃ n : ℕ, n ≠ 0 ∧ n • g ∈ H := Iff.rfl

/-- `H` sits inside its divisible hull (`n = 1`). -/
lemma le_divisibleHull (H : AddSubgroup G) : H ≤ H.divisibleHull :=
  fun _ hg => ⟨1, one_ne_zero, by rwa [one_smul]⟩

/-- The divisible hull is monotone in `H`. -/
lemma divisibleHull_mono {H₁ H₂ : AddSubgroup G} (h : H₁ ≤ H₂) :
    H₁.divisibleHull ≤ H₂.divisibleHull :=
  fun _ ⟨n, hn, hg⟩ => ⟨n, hn, h hg⟩

/-- **Saturation.**  If some nonzero multiple of `g` already lies in the divisible hull, so does
`g`.  In particular the hull is idempotent. -/
lemma mem_divisibleHull_of_nsmul_mem {H : AddSubgroup G} {g : G} {n : ℕ} (hn : n ≠ 0)
    (h : n • g ∈ H.divisibleHull) : g ∈ H.divisibleHull := by
  obtain ⟨m, hm, hmg⟩ := h
  exact ⟨m * n, mul_ne_zero hm hn, by rwa [mul_smul]⟩

end AddSubgroup

namespace DivisibleValueGroup

/-! ## §2  The exponent group of a normed field, and its divisible hull -/

section ValueGroup

variable (K : Type*) [NormedField K]

/-- The **exponent (log) value group** `Λ = { log ‖x‖ : x ≠ 0 }`, the value group `‖K˟‖` read
additively inside `(ℝ, +)`.  A genuine `AddSubgroup ℝ`: `log ‖1‖ = 0`, `log ‖xy‖ = log ‖x‖ + log
‖y‖`, `log ‖x⁻¹‖ = -log ‖x‖`. -/
def logValueGroup : AddSubgroup ℝ where
  carrier := {γ | ∃ x : K, x ≠ 0 ∧ Real.log ‖x‖ = γ}
  zero_mem' := ⟨1, one_ne_zero, by rw [norm_one, Real.log_one]⟩
  add_mem' := by
    rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact ⟨x * y, mul_ne_zero hx hy, by
      rw [norm_mul, Real.log_mul (norm_ne_zero_iff.mpr hx) (norm_ne_zero_iff.mpr hy)]⟩
  neg_mem' := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x⁻¹, inv_ne_zero hx, by rw [norm_inv, Real.log_inv]⟩

/-- `c` is a **divisible value** (additive form): its exponent `log c` lies in the divisible hull
of the exponent group.  The application of `AddSubgroup.divisibleHull` to `logValueGroup K`; agrees
with the multiplicative `MemDivisibleValueGroup` for `0 < c` (`memDivisibleValueGroup_iff_log`). -/
def MemDivisibleLogValueGroup (c : ℝ) : Prop :=
  Real.log c ∈ (logValueGroup K).divisibleHull

/-- The **divisible value group** as admissible radii: the exponential of the divisible hull of the
exponent group.  This is the multiplicative divisible value group as a subset of `ℝ_{>0}`, and is
exactly what the Weierstrass / Newton-polygon theory admits (`mem_expDivisibleValueGroup_iff`). -/
def expDivisibleValueGroup : Set ℝ :=
  Real.exp '' ((logValueGroup K).divisibleHull : Set ℝ)

variable {K}

@[simp] lemma mem_logValueGroup {γ : ℝ} :
    γ ∈ logValueGroup K ↔ ∃ x : K, x ≠ 0 ∧ Real.log ‖x‖ = γ := Iff.rfl

lemma mem_expDivisibleValueGroup {c : ℝ} :
    c ∈ expDivisibleValueGroup K ↔
      ∃ γ : ℝ, γ ∈ (logValueGroup K).divisibleHull ∧ Real.exp γ = c := by
  simp only [expDivisibleValueGroup, Set.mem_image, SetLike.mem_coe]

/-- The value group sits inside its divisible closure (`n = 1`): a realised norm `‖x‖ = c` gives
`MemDivisibleValueGroup K c`. -/
lemma memDivisibleValueGroup_of_norm {c : ℝ} (x : K) (hx : ‖x‖ = c) :
    MemDivisibleValueGroup K c :=
  ⟨1, one_ne_zero, x, by rw [hx, pow_one]⟩

/-- **Unification (multiplicative ⇔ additive).**  For `0 < c`, `c` lies in the divisible value
group iff its exponent `log c` lies in the divisible hull of the exponent group.  Forward: `‖x‖ =
cⁿ ⇒ log ‖x‖ = n • log c` by `Real.log_pow`.  Backward: `log` is injective on the positives. -/
theorem memDivisibleValueGroup_iff_log {c : ℝ} (hc : 0 < c) :
    MemDivisibleValueGroup K c ↔ MemDivisibleLogValueGroup K c := by
  simp only [MemDivisibleValueGroup, MemDivisibleLogValueGroup, AddSubgroup.mem_divisibleHull,
    mem_logValueGroup]
  constructor
  · rintro ⟨n, hn, x, hx⟩
    have hxpos : 0 < ‖x‖ := by rw [hx]; exact pow_pos hc n
    have hx0 : x ≠ 0 := by rintro rfl; rw [norm_zero] at hxpos; exact lt_irrefl 0 hxpos
    exact ⟨n, hn, x, hx0, by rw [hx, Real.log_pow, nsmul_eq_mul]⟩
  · rintro ⟨n, hn, x, hx0, hlog⟩
    have hxpos : 0 < ‖x‖ := (norm_nonneg x).lt_of_ne (norm_ne_zero_iff.mpr hx0).symm
    exact ⟨n, hn, x, Real.log_injOn_pos (Set.mem_Ioi.mpr hxpos)
      (Set.mem_Ioi.mpr (pow_pos hc n)) (by rw [hlog, Real.log_pow, nsmul_eq_mul])⟩

/-- `memDivisibleValueGroup_iff_log` with the exponent membership spelled out. -/
theorem memDivisibleValueGroup_iff_exists_log {c : ℝ} (hc : 0 < c) :
    MemDivisibleValueGroup K c ↔
      ∃ n : ℕ, n ≠ 0 ∧ ∃ x : K, x ≠ 0 ∧ Real.log ‖x‖ = n • Real.log c := by
  rw [memDivisibleValueGroup_iff_log hc]
  simp only [MemDivisibleLogValueGroup, AddSubgroup.mem_divisibleHull, mem_logValueGroup]

/-- **The exponential divisible value group is exactly `WPrep_gen`'s predicate.**  For `0 < c`,
`c ∈ expDivisibleValueGroup K ↔ MemDivisibleValueGroup K c`.  This is the "define generally, then
apply to exponentials" endpoint: the admissible radii are `exp` of the divisible hull. -/
theorem mem_expDivisibleValueGroup_iff {c : ℝ} (hc : 0 < c) :
    c ∈ expDivisibleValueGroup K ↔ MemDivisibleValueGroup K c := by
  rw [mem_expDivisibleValueGroup, memDivisibleValueGroup_iff_log hc]
  constructor
  · rintro ⟨γ, hγ, rfl⟩
    show Real.log (Real.exp γ) ∈ (logValueGroup K).divisibleHull
    rwa [Real.log_exp]
  · intro h
    exact ⟨Real.log c, h, Real.exp_log hc⟩

end ValueGroup

/-! ## §3  Bridge to the additive valuation `RankOne.addVal` (`x ↦ -log ‖x‖`) -/

section AdditiveValuation

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]

/-- For `x ≠ 0`, the canonical additive valuation reads off the negated log-norm:
`addVal x = ↑(-log ‖x‖)`.  Same computation as `NewtonPolygon.addVal_of_ne_zero`. -/
lemma addVal_eq_neg_log_norm {x : K} (hx : x ≠ 0) :
    RankOne.addVal (NormedField.valuation (K := K)) x = ((-Real.log ‖x‖ : ℝ) : WithTop ℝ) := by
  rw [RankOne.addVal_apply_of_ne_zero _ hx, valuation_norm_eq]

/-- The exponent group is the negated range of the additive valuation:
`γ ∈ logValueGroup K ↔ ∃ x ≠ 0, addVal x = ↑(-γ)`.  Bridges the value group as a subset of `(ℝ,+)`
with the codebase's additive valuation `addVal`. -/
lemma mem_logValueGroup_iff_addVal {γ : ℝ} :
    γ ∈ logValueGroup K ↔
      ∃ x : K, x ≠ 0 ∧
        RankOne.addVal (NormedField.valuation (K := K)) x = ((-γ : ℝ) : WithTop ℝ) := by
  simp only [mem_logValueGroup]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, addVal_eq_neg_log_norm hx⟩
  · rintro ⟨x, hx, h⟩
    refine ⟨x, hx, ?_⟩
    rw [addVal_eq_neg_log_norm hx] at h
    exact neg_injective (WithTop.coe_inj.mp h)

/-- **Unification (multiplicative ⇔ additive valuation).**  For `0 < c`, `c` lies in the divisible
value group iff some element `x` has additive valuation exactly `n` times the exponent `-log c` of
the formal radius `c`. -/
theorem memDivisibleValueGroup_iff_addVal {c : ℝ} (hc : 0 < c) :
    MemDivisibleValueGroup K c ↔
      ∃ n : ℕ, n ≠ 0 ∧ ∃ x : K, x ≠ 0 ∧
        RankOne.addVal (NormedField.valuation (K := K)) x
          = ((-(n • Real.log c) : ℝ) : WithTop ℝ) := by
  rw [memDivisibleValueGroup_iff_log hc]
  simp only [MemDivisibleLogValueGroup, AddSubgroup.mem_divisibleHull, mem_logValueGroup_iff_addVal]

end AdditiveValuation

end DivisibleValueGroup
