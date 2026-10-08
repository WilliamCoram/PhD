/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.Analysis.Normed.Unbundled.RingSeminorm

/-!
# The gauge norm of a Tate ring

Let `A` be a topological ring, `A₀ ⊆ A` a subring and `ϖ ∈ A₀` a unit of `A` such that
`(ϖ ^ n A₀)ₙ` is a basis of neighbourhoods of `0` — by Wedhorn's Proposition 6.14 and
Corollary 6.15 this is exactly the datum of a Tate ring with a ring of definition and a
topologically nilpotent unit in it. For a real `a > 1` the *gauge norm*
`‖r‖ = inf {a ^ (-n) | r ∈ ϖ ^ n A₀}` is an ultrametric submultiplicative seminorm inducing the
topology of `A`, with unit ball `A₀`, for which `ϖ` is multiplicative of norm `a⁻¹ < 1`; it is a
norm exactly when `A` is Hausdorff. So every Hausdorff Tate ring is the underlying topological ring
of a Tate normed ring (Johansson–Newton, Remark 2.1.3(1)): the normed hypothesis of
`NormedRing.IsTate` costs no generality.

⚠ **Seam.** The hypothesis `hbasis` below is what `TauCeti.Huber.IsTateRing` provides for a ring of
definition containing a pseudo-uniformiser; at migration it is discharged from that class.

Roadmap: `PhD/TauCeti/Roadmaps/PadicFunctionalAnalysis/README.md`, §0.4.6. Tau Ceti home:
`TauCeti/Analysis/Normed/Ring/Ultra/GaugeNorm.lean`.

## Main definitions

* `Subring.gaugeNorm A₀ ϖ a` — the gauge norm, as a function `A → ℝ`.
* `Subring.gaugeRingNorm` — the gauge norm of a Hausdorff Tate ring, as a `RingNorm`.

## Main results

* `Subring.gaugeNorm_le_zpow_iff` — `‖r‖ ≤ a ^ (-n) ↔ r ∈ ϖ ^ n A₀`: the workhorse.
* `Subring.gaugeNorm_unit_mul` — `ϖ` is multiplicative.
* `Subring.hasBasis_nhds_zero_gaugeNorm` — the gauge norm induces the topology.
-/

open Filter Topology Pointwise

namespace Subring

variable {A : Type*} [CommRing A] [TopologicalSpace A]

/-- The gauge norm `r ↦ inf {a ^ (-n) | n : ℤ, r ∈ ϖ ^ n A₀}` of a subring `A₀` with respect to a
unit `ϖ`. Source: Johansson–Newton, Remark 2.1.3(1)
(`|r| = inf {a^{-n} | r ∈ ϖ^n R₀, n ∈ ℤ}`). -/
noncomputable def gaugeNorm (A₀ : Subring A) (ϖ : Aˣ) (a : ℝ) (r : A) : ℝ :=
  sInf {y | ∃ n : ℤ, y = a ^ (-n) ∧ r ∈ ((ϖ ^ n : Aˣ) : A) • (A₀ : Set A)}

variable {A₀ : Subring A} {ϖ : Aˣ} {a : ℝ} {r s : A}

section Algebra

omit [TopologicalSpace A]

/-! ### Membership in `ϖ ^ n A₀` -/

private theorem mem_zpow_smul_iff {n : ℤ} :
    r ∈ ((ϖ ^ n : Aˣ) : A) • (A₀ : Set A) ↔ ((ϖ ^ (-n) : Aˣ) : A) * r ∈ A₀ := by
  have h1 : ((ϖ ^ (-n) : Aˣ) : A) * ((ϖ ^ n : Aˣ) : A) = 1 := by
    rw [← Units.val_mul, ← zpow_add, neg_add_cancel, zpow_zero, Units.val_one]
  constructor
  · rintro ⟨x, hx, rfl⟩
    change ((ϖ ^ (-n) : Aˣ) : A) * (((ϖ ^ n : Aˣ) : A) * x) ∈ A₀
    rwa [← mul_assoc, h1, one_mul]
  · intro h
    refine ⟨_, h, ?_⟩
    change ((ϖ ^ n : Aˣ) : A) * (((ϖ ^ (-n) : Aˣ) : A) * r) = r
    rw [← mul_assoc, ← Units.val_mul, ← zpow_add, add_neg_cancel, zpow_zero, Units.val_one,
      one_mul]

private theorem neg_mem_zpow_smul_iff {n : ℤ} :
    -r ∈ ((ϖ ^ n : Aˣ) : A) • (A₀ : Set A) ↔ r ∈ ((ϖ ^ n : Aˣ) : A) • (A₀ : Set A) := by
  rw [mem_zpow_smul_iff, mem_zpow_smul_iff, mul_neg, neg_mem_iff]

private theorem add_mem_zpow_smul {n : ℤ} (hr : r ∈ ((ϖ ^ n : Aˣ) : A) • (A₀ : Set A))
    (hs : s ∈ ((ϖ ^ n : Aˣ) : A) • (A₀ : Set A)) : r + s ∈ ((ϖ ^ n : Aˣ) : A) • (A₀ : Set A) := by
  rw [mem_zpow_smul_iff] at hr hs ⊢
  rw [mul_add]
  exact add_mem hr hs

private theorem mul_mem_zpow_smul {m n : ℤ} (hr : r ∈ ((ϖ ^ m : Aˣ) : A) • (A₀ : Set A))
    (hs : s ∈ ((ϖ ^ n : Aˣ) : A) • (A₀ : Set A)) :
    r * s ∈ ((ϖ ^ (m + n) : Aˣ) : A) • (A₀ : Set A) := by
  rw [mem_zpow_smul_iff] at hr hs ⊢
  have h : ((ϖ ^ (-(m + n)) : Aˣ) : A) * (r * s) =
      (((ϖ ^ (-m) : Aˣ) : A) * r) * (((ϖ ^ (-n) : Aˣ) : A) * s) := by
    rw [neg_add, zpow_add, Units.val_mul]
    ring
  rw [h]
  exact mul_mem hr hs

private theorem unit_mul_mem_zpow_smul_iff {n : ℤ} :
    (ϖ : A) * r ∈ ((ϖ ^ n : Aˣ) : A) • (A₀ : Set A) ↔
      r ∈ ((ϖ ^ (n - 1) : Aˣ) : A) • (A₀ : Set A) := by
  rw [mem_zpow_smul_iff, mem_zpow_smul_iff]
  have h : ((ϖ ^ (-(n - 1)) : Aˣ) : A) * r = ((ϖ ^ (-n) : Aˣ) : A) * ((ϖ : A) * r) := by
    rw [show -(n - 1) = -n + 1 by ring, zpow_add, zpow_one, Units.val_mul, mul_assoc]
  rw [h]

/-- The exponents `n` with `r ∈ ϖ ^ n A₀` form a down-set, since `ϖ ∈ A₀`. -/
private theorem mem_zpow_smul_of_le (hϖ : (ϖ : A) ∈ A₀) {m n : ℤ} (hmn : m ≤ n)
    (h : r ∈ ((ϖ ^ n : Aˣ) : A) • (A₀ : Set A)) : r ∈ ((ϖ ^ m : Aˣ) : A) • (A₀ : Set A) := by
  rw [mem_zpow_smul_iff] at h ⊢
  obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (sub_nonneg.2 hmn)
  have hu : (ϖ ^ (-m) : Aˣ) = ϖ ^ (k : ℤ) * ϖ ^ (-n) := by
    rw [← zpow_add, ← hk]
    congr 1
    ring
  rw [hu, Units.val_mul, mul_assoc, zpow_natCast, Units.val_pow_eq_pow_val]
  exact A₀.mul_mem (A₀.pow_mem hϖ k) h

private theorem mem_zpow_smul_of_not_bddAbove (hϖ : (ϖ : A) ∈ A₀)
    (h : ¬ ∃ b : ℤ, ∀ m : ℤ, r ∈ ((ϖ ^ m : Aˣ) : A) • (A₀ : Set A) → m ≤ b) (n : ℤ) :
    r ∈ ((ϖ ^ n : Aˣ) : A) • (A₀ : Set A) := by
  simp only [not_exists, not_forall, not_le, exists_prop] at h
  obtain ⟨m, hm, hnm⟩ := h n
  exact mem_zpow_smul_of_le hϖ hnm.le hm

/-! ### The infimum -/

private theorem bddBelow_gaugeNorm_set (ha : 0 < a) (r : A) :
    BddBelow {y | ∃ n : ℤ, y = a ^ (-n) ∧ r ∈ ((ϖ ^ n : Aˣ) : A) • (A₀ : Set A)} :=
  ⟨0, fun _ ⟨_, hy, _⟩ ↦ hy ▸ (zpow_pos ha _).le⟩

private theorem gaugeNorm_le_of_mem (ha : 0 < a) {n : ℤ}
    (h : r ∈ ((ϖ ^ n : Aˣ) : A) • (A₀ : Set A)) : A₀.gaugeNorm ϖ a r ≤ a ^ (-n) :=
  csInf_le (bddBelow_gaugeNorm_set ha r) ⟨n, rfl, h⟩

private theorem gaugeNorm_eq_of_isGreatest (ha : 1 < a) {M : ℤ}
    (hM : IsGreatest {n : ℤ | r ∈ ((ϖ ^ n : Aˣ) : A) • (A₀ : Set A)} M) :
    A₀.gaugeNorm ϖ a r = a ^ (-M) := by
  refine IsLeast.csInf_eq ⟨⟨M, rfl, hM.1⟩, fun y ⟨m, hy, hm⟩ ↦ ?_⟩
  rw [hy]
  exact zpow_le_zpow_right₀ ha.le (neg_le_neg (hM.2 hm))

/-- A value in `{0} ∪ a ^ ℤ` is at least every `y` that lies below each power `a ^ (-n)` above
it. -/
private theorem le_of_forall_zpow_le {x y : ℝ} (ha : 1 < a) (hx : x = 0 ∨ ∃ k : ℤ, x = a ^ k)
    (h : ∀ n : ℤ, x ≤ a ^ (-n) → y ≤ a ^ (-n)) : y ≤ x := by
  rcases hx with rfl | ⟨k, rfl⟩
  · refine le_of_forall_pos_le_add fun ε hε ↦ ?_
    obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hε (inv_lt_one_of_one_lt₀ ha)
    rw [zero_add]
    calc y ≤ a ^ (-(m : ℤ)) := h m (zpow_pos (zero_lt_one.trans ha) _).le
      _ = a⁻¹ ^ m := by rw [zpow_neg, zpow_natCast, inv_pow]
      _ ≤ ε := hm.le
  · simpa using h (-k) (by rw [neg_neg])

theorem gaugeNorm_nonneg (ha : 0 < a) (r : A) : 0 ≤ A₀.gaugeNorm ϖ a r := by
  exact Real.sInf_nonneg fun _ ⟨_, hy, _⟩ ↦ hy ▸ (zpow_pos ha _).le

end Algebra

section Basis

variable [IsTopologicalRing A]

/-- Source: Wedhorn, Proposition 6.14 ("for every `a ∈ A` there exists `n ∈ ℕ` such that
`a sⁿ ∈ B`, hence `A = B_s`"). -/
theorem exists_mem_zpow_smul
    (hbasis : (𝓝 (0 : A)).HasBasis (fun _ : ℕ ↦ True) fun n ↦ ((ϖ : A) ^ n) • (A₀ : Set A))
    (r : A) : ∃ n : ℤ, r ∈ ((ϖ ^ n : Aˣ) : A) • (A₀ : Set A) := by
  have hA₀ : (A₀ : Set A) ∈ 𝓝 (0 : A) := by
    simpa using hbasis.mem_of_mem (i := 0) trivial
  have hpre : (fun x ↦ x * r) ⁻¹' (A₀ : Set A) ∈ 𝓝 (0 : A) := by
    have h := (continuous_mul_const r).tendsto 0
    rw [zero_mul] at h
    exact h hA₀
  obtain ⟨N, -, hN⟩ := hbasis.mem_iff.1 hpre
  have h1 : (ϖ : A) ^ N * r ∈ A₀ := hN ⟨1, A₀.one_mem, by simp⟩
  refine ⟨-(N : ℤ), mem_zpow_smul_iff.2 ?_⟩
  rwa [neg_neg, zpow_natCast, Units.val_pow_eq_pow_val]

/-- **The workhorse.** Source: Johansson–Newton, Remark 2.1.3(1) ("`R` is a Tate normed ring with
unit ball `R₀`"), read at every radius. -/
theorem gaugeNorm_le_zpow_iff (hϖ : (ϖ : A) ∈ A₀)
    (hbasis : (𝓝 (0 : A)).HasBasis (fun _ : ℕ ↦ True) fun n ↦ ((ϖ : A) ^ n) • (A₀ : Set A))
    (ha : 1 < a) (n : ℤ) :
    A₀.gaugeNorm ϖ a r ≤ a ^ (-n) ↔ r ∈ ((ϖ ^ n : Aˣ) : A) • (A₀ : Set A) := by
  refine ⟨fun h ↦ ?_, gaugeNorm_le_of_mem (zero_lt_one.trans ha)⟩
  by_cases hb : ∃ b : ℤ, ∀ m : ℤ, r ∈ ((ϖ ^ m : Aˣ) : A) • (A₀ : Set A) → m ≤ b
  · obtain ⟨M, hM, hMmax⟩ := Int.exists_greatest_of_bdd hb (exists_mem_zpow_smul hbasis r)
    rw [gaugeNorm_eq_of_isGreatest ha ⟨hM, fun z hz ↦ hMmax z hz⟩] at h
    have h' : -M ≤ -n := (zpow_le_zpow_iff_right₀ ha).1 h
    exact mem_zpow_smul_of_le hϖ (by omega) hM
  · exact mem_zpow_smul_of_not_bddAbove hϖ hb n

/-- The gauge norm takes its values in `{0} ∪ a ^ ℤ`. Source: Johansson–Newton,
Remark 2.1.3(1) (the infimum of a set of integer powers of `a`). -/
theorem gaugeNorm_eq_zero_or_exists_zpow (hϖ : (ϖ : A) ∈ A₀)
    (hbasis : (𝓝 (0 : A)).HasBasis (fun _ : ℕ ↦ True) fun n ↦ ((ϖ : A) ^ n) • (A₀ : Set A))
    (ha : 1 < a) (r : A) : A₀.gaugeNorm ϖ a r = 0 ∨ ∃ n : ℤ, A₀.gaugeNorm ϖ a r = a ^ n := by
  by_cases hb : ∃ b : ℤ, ∀ m : ℤ, r ∈ ((ϖ ^ m : Aˣ) : A) • (A₀ : Set A) → m ≤ b
  · obtain ⟨M, hM, hMmax⟩ := Int.exists_greatest_of_bdd hb (exists_mem_zpow_smul hbasis r)
    exact Or.inr ⟨-M, gaugeNorm_eq_of_isGreatest ha ⟨hM, fun z hz ↦ hMmax z hz⟩⟩
  · refine Or.inl (le_antisymm (le_of_forall_zpow_le ha (Or.inl rfl) fun n _ ↦ ?_)
      (gaugeNorm_nonneg (zero_lt_one.trans ha) r))
    exact gaugeNorm_le_of_mem (zero_lt_one.trans ha) (mem_zpow_smul_of_not_bddAbove hϖ hb n)

/-- Source: Johansson–Newton, Remark 2.1.3(1) ("with unit ball `R₀`"). -/
theorem gaugeNorm_le_one_iff (hϖ : (ϖ : A) ∈ A₀)
    (hbasis : (𝓝 (0 : A)).HasBasis (fun _ : ℕ ↦ True) fun n ↦ ((ϖ : A) ^ n) • (A₀ : Set A))
    (ha : 1 < a) : A₀.gaugeNorm ϖ a r ≤ 1 ↔ r ∈ A₀ := by
  have h := gaugeNorm_le_zpow_iff (r := r) hϖ hbasis ha 0
  rwa [neg_zero, zpow_zero, zpow_zero, Units.val_one, one_smul, SetLike.mem_coe] at h

/-- Source: Johansson–Newton, Definition 2.1.1(2) (`|r + s| ≤ max(|r|, |s|)`). -/
theorem gaugeNorm_add_le_max (hϖ : (ϖ : A) ∈ A₀)
    (hbasis : (𝓝 (0 : A)).HasBasis (fun _ : ℕ ↦ True) fun n ↦ ((ϖ : A) ^ n) • (A₀ : Set A))
    (ha : 1 < a) (r s : A) :
    A₀.gaugeNorm ϖ a (r + s) ≤ max (A₀.gaugeNorm ϖ a r) (A₀.gaugeNorm ϖ a s) := by
  refine le_of_forall_zpow_le ha ?_ fun n hn ↦ ?_
  · rcases le_total (A₀.gaugeNorm ϖ a r) (A₀.gaugeNorm ϖ a s) with h | h
    · rw [max_eq_right h]
      exact gaugeNorm_eq_zero_or_exists_zpow hϖ hbasis ha s
    · rw [max_eq_left h]
      exact gaugeNorm_eq_zero_or_exists_zpow hϖ hbasis ha r
  · have hr := (gaugeNorm_le_zpow_iff hϖ hbasis ha n).1 ((le_max_left _ _).trans hn)
    have hs := (gaugeNorm_le_zpow_iff hϖ hbasis ha n).1 ((le_max_right _ _).trans hn)
    exact (gaugeNorm_le_zpow_iff hϖ hbasis ha n).2 (add_mem_zpow_smul hr hs)

omit [TopologicalSpace A] [IsTopologicalRing A] in
theorem gaugeNorm_neg (r : A) : A₀.gaugeNorm ϖ a (-r) = A₀.gaugeNorm ϖ a r := by
  unfold gaugeNorm
  simp only [neg_mem_zpow_smul_iff]

/-- Source: Johansson–Newton, Definition 2.1.1(3) (`|rs| ≤ |r||s|`). -/
theorem gaugeNorm_mul_le (hϖ : (ϖ : A) ∈ A₀)
    (hbasis : (𝓝 (0 : A)).HasBasis (fun _ : ℕ ↦ True) fun n ↦ ((ϖ : A) ^ n) • (A₀ : Set A))
    (ha : 1 < a) (r s : A) :
    A₀.gaugeNorm ϖ a (r * s) ≤ A₀.gaugeNorm ϖ a r * A₀.gaugeNorm ϖ a s := by
  have ha0 : 0 < a := zero_lt_one.trans ha
  rcases gaugeNorm_eq_zero_or_exists_zpow hϖ hbasis ha r with hr | ⟨k, hk⟩
  · rw [hr, zero_mul]
    obtain ⟨m, hm⟩ := exists_mem_zpow_smul hbasis s
    refine le_of_forall_zpow_le ha (Or.inl rfl) fun n _ ↦ ?_
    have hrn : r ∈ ((ϖ ^ (n - m) : Aˣ) : A) • (A₀ : Set A) :=
      (gaugeNorm_le_zpow_iff hϖ hbasis ha _).1 (by rw [hr]; exact (zpow_pos ha0 _).le)
    have h := mul_mem_zpow_smul hrn hm
    rw [sub_add_cancel] at h
    exact gaugeNorm_le_of_mem ha0 h
  rcases gaugeNorm_eq_zero_or_exists_zpow hϖ hbasis ha s with hs | ⟨l, hl⟩
  · rw [hs, mul_zero]
    obtain ⟨m, hm⟩ := exists_mem_zpow_smul hbasis r
    refine le_of_forall_zpow_le ha (Or.inl rfl) fun n _ ↦ ?_
    have hsn : s ∈ ((ϖ ^ (n - m) : Aˣ) : A) • (A₀ : Set A) :=
      (gaugeNorm_le_zpow_iff hϖ hbasis ha _).1 (by rw [hs]; exact (zpow_pos ha0 _).le)
    have h := mul_mem_zpow_smul hm hsn
    rw [show m + (n - m) = n by ring] at h
    exact gaugeNorm_le_of_mem ha0 h
  have hr' : r ∈ ((ϖ ^ (-k) : Aˣ) : A) • (A₀ : Set A) :=
    (gaugeNorm_le_zpow_iff hϖ hbasis ha _).1 (by rw [hk, neg_neg])
  have hs' : s ∈ ((ϖ ^ (-l) : Aˣ) : A) • (A₀ : Set A) :=
    (gaugeNorm_le_zpow_iff hϖ hbasis ha _).1 (by rw [hl, neg_neg])
  have h := gaugeNorm_le_of_mem ha0 (mul_mem_zpow_smul hr' hs')
  rwa [hk, hl, ← zpow_add₀ ha0.ne', neg_add, neg_neg, neg_neg] at *

/-- Source: Johansson–Newton, Remark 2.1.3(1) ("`ϖ` is a multiplicative pseudo-uniformizer"). -/
theorem gaugeNorm_unit_mul (hϖ : (ϖ : A) ∈ A₀)
    (hbasis : (𝓝 (0 : A)).HasBasis (fun _ : ℕ ↦ True) fun n ↦ ((ϖ : A) ^ n) • (A₀ : Set A))
    (ha : 1 < a) (r : A) : A₀.gaugeNorm ϖ a ((ϖ : A) * r) = a⁻¹ * A₀.gaugeNorm ϖ a r := by
  have ha0 : 0 < a := zero_lt_one.trans ha
  have hiff : ∀ n : ℤ, A₀.gaugeNorm ϖ a ((ϖ : A) * r) ≤ a ^ (-n) ↔
      a⁻¹ * A₀.gaugeNorm ϖ a r ≤ a ^ (-n) := by
    intro n
    rw [gaugeNorm_le_zpow_iff hϖ hbasis ha, unit_mul_mem_zpow_smul_iff,
      ← gaugeNorm_le_zpow_iff hϖ hbasis ha, inv_mul_le_iff₀ ha0,
      show -(n - 1) = -n + 1 by ring, zpow_add₀ ha0.ne', zpow_one, mul_comm]
  have hv : a⁻¹ * A₀.gaugeNorm ϖ a r = 0 ∨ ∃ k : ℤ, a⁻¹ * A₀.gaugeNorm ϖ a r = a ^ k := by
    rcases gaugeNorm_eq_zero_or_exists_zpow hϖ hbasis ha r with h | ⟨k, hk⟩
    · exact Or.inl (by rw [h, mul_zero])
    · exact Or.inr ⟨k - 1, by rw [hk, zpow_sub₀ ha0.ne', zpow_one, div_eq_inv_mul]⟩
  exact le_antisymm (le_of_forall_zpow_le ha hv fun n h ↦ (hiff n).2 h)
    (le_of_forall_zpow_le ha (gaugeNorm_eq_zero_or_exists_zpow hϖ hbasis ha _)
      fun n h ↦ (hiff n).1 h)

/-- Source: roadmap §0.4.6 ("inducing the topology of `A`"). -/
theorem hasBasis_nhds_zero_gaugeNorm (hϖ : (ϖ : A) ∈ A₀)
    (hbasis : (𝓝 (0 : A)).HasBasis (fun _ : ℕ ↦ True) fun n ↦ ((ϖ : A) ^ n) • (A₀ : Set A))
    (ha : 1 < a) :
    (𝓝 (0 : A)).HasBasis (fun ε : ℝ ↦ 0 < ε) fun ε ↦ {r | A₀.gaugeNorm ϖ a r < ε} := by
  have ha0 : 0 < a := zero_lt_one.trans ha
  have hpow : ∀ i : ℕ, ((ϖ ^ (i : ℤ) : Aˣ) : A) = (ϖ : A) ^ i := fun i ↦ by
    rw [zpow_natCast, Units.val_pow_eq_pow_val]
  refine hbasis.to_hasBasis (fun i _ ↦ ⟨a ^ (-(i : ℤ)), zpow_pos ha0 _, fun r hr ↦ ?_⟩)
    fun ε hε ↦ ?_
  · have h := (gaugeNorm_le_zpow_iff hϖ hbasis ha (i : ℤ)).1 (le_of_lt hr)
    rwa [hpow] at h
  · obtain ⟨i, hi⟩ := exists_pow_lt_of_lt_one hε (inv_lt_one_of_one_lt₀ ha)
    refine ⟨i, trivial, fun r hr ↦ ?_⟩
    have hr' : r ∈ ((ϖ ^ (i : ℤ) : Aˣ) : A) • (A₀ : Set A) := by rwa [hpow]
    calc A₀.gaugeNorm ϖ a r ≤ a ^ (-(i : ℤ)) := gaugeNorm_le_of_mem ha0 hr'
      _ = a⁻¹ ^ i := by rw [zpow_neg, zpow_natCast, inv_pow]
      _ < ε := hi

variable [T2Space A]

/-- Source: roadmap §0.4.6 (the Hausdorff hypothesis is what makes the seminorm a norm). -/
theorem gaugeNorm_eq_zero_iff (hϖ : (ϖ : A) ∈ A₀)
    (hbasis : (𝓝 (0 : A)).HasBasis (fun _ : ℕ ↦ True) fun n ↦ ((ϖ : A) ^ n) • (A₀ : Set A))
    (ha : 1 < a) : A₀.gaugeNorm ϖ a r = 0 ↔ r = 0 := by
  have ha0 : 0 < a := zero_lt_one.trans ha
  constructor
  · intro h
    by_contra hr
    obtain ⟨i, -, hi⟩ := hbasis.mem_iff.1 (isOpen_compl_singleton.mem_nhds (Ne.symm hr))
    have hmem : r ∈ ((ϖ ^ (i : ℤ) : Aˣ) : A) • (A₀ : Set A) :=
      (gaugeNorm_le_zpow_iff hϖ hbasis ha _).1 (by rw [h]; exact (zpow_pos ha0 _).le)
    rw [zpow_natCast, Units.val_pow_eq_pow_val] at hmem
    exact hi hmem rfl
  · rintro rfl
    exact le_antisymm (le_of_forall_zpow_le ha (Or.inl rfl) fun n _ ↦
      gaugeNorm_le_of_mem ha0 ⟨0, A₀.zero_mem, smul_zero _⟩) (gaugeNorm_nonneg ha0 _)

/-- Source: roadmap §0.4.6 (the values of the gauge norm). -/
theorem exists_gaugeNorm_eq_zpow (hϖ : (ϖ : A) ∈ A₀)
    (hbasis : (𝓝 (0 : A)).HasBasis (fun _ : ℕ ↦ True) fun n ↦ ((ϖ : A) ^ n) • (A₀ : Set A))
    (ha : 1 < a) (hr : r ≠ 0) : ∃ n : ℤ, A₀.gaugeNorm ϖ a r = a ^ n := by
  rcases gaugeNorm_eq_zero_or_exists_zpow hϖ hbasis ha r with h | h
  · exact absurd ((gaugeNorm_eq_zero_iff hϖ hbasis ha).1 h) hr
  · exact h

variable [Nontrivial A]

/-- Source: Johansson–Newton, Definition 2.1.1(1) (`|1| = 1`). -/
theorem gaugeNorm_one (hϖ : (ϖ : A) ∈ A₀)
    (hbasis : (𝓝 (0 : A)).HasBasis (fun _ : ℕ ↦ True) fun n ↦ ((ϖ : A) ^ n) • (A₀ : Set A))
    (ha : 1 < a) : A₀.gaugeNorm ϖ a 1 = 1 := by
  have ha0 : 0 < a := zero_lt_one.trans ha
  refine le_antisymm ((gaugeNorm_le_one_iff hϖ hbasis ha).2 A₀.one_mem) (not_lt.1 fun hlt ↦ ?_)
  obtain ⟨k, hk⟩ := exists_gaugeNorm_eq_zpow hϖ hbasis ha (one_ne_zero : (1 : A) ≠ 0)
  have hk0 : k < 0 := (zpow_lt_one_iff_right₀ ha).1 (by rw [← hk]; exact hlt)
  have h1 : (1 : A) ∈ ((ϖ ^ (1 : ℤ) : Aˣ) : A) • (A₀ : Set A) :=
    (gaugeNorm_le_zpow_iff hϖ hbasis ha 1).1
      (by rw [hk]; exact zpow_le_zpow_right₀ ha.le (by omega))
  have hinv : ((ϖ⁻¹ : Aˣ) : A) ∈ A₀ := by
    have h := mem_zpow_smul_iff.1 h1
    rwa [zpow_neg_one, mul_one] at h
  have hall : ∀ n : ℤ, (1 : A) ∈ ((ϖ ^ n : Aˣ) : A) • (A₀ : Set A) := by
    intro n
    refine mem_zpow_smul_of_le hϖ (Int.self_le_toNat n) (mem_zpow_smul_iff.2 ?_)
    rw [zpow_neg, zpow_natCast, ← inv_pow, Units.val_pow_eq_pow_val, mul_one]
    exact A₀.pow_mem hinv _
  have h0 : A₀.gaugeNorm ϖ a 1 = 0 :=
    le_antisymm (le_of_forall_zpow_le ha (Or.inl rfl) fun n _ ↦ gaugeNorm_le_of_mem ha0 (hall n))
      (gaugeNorm_nonneg ha0 _)
  exact one_ne_zero ((gaugeNorm_eq_zero_iff hϖ hbasis ha).1 h0)

/-- Source: Johansson–Newton, Remark 2.1.3(1) (`|ϖ| < 1`). -/
theorem gaugeNorm_unit (hϖ : (ϖ : A) ∈ A₀)
    (hbasis : (𝓝 (0 : A)).HasBasis (fun _ : ℕ ↦ True) fun n ↦ ((ϖ : A) ^ n) • (A₀ : Set A))
    (ha : 1 < a) : A₀.gaugeNorm ϖ a (ϖ : A) = a⁻¹ := by
  have h := gaugeNorm_unit_mul hϖ hbasis ha (1 : A)
  rwa [mul_one, gaugeNorm_one hϖ hbasis ha, mul_one] at h

end Basis

/-- The gauge norm of a Hausdorff Tate ring, as a ring norm. Source: Johansson–Newton,
Remark 2.1.3(1). -/
noncomputable def gaugeRingNorm [IsTopologicalRing A] [T2Space A] (A₀ : Subring A) (ϖ : Aˣ)
    (a : ℝ) (hϖ : (ϖ : A) ∈ A₀)
    (hbasis : (𝓝 (0 : A)).HasBasis (fun _ : ℕ ↦ True) fun n ↦ ((ϖ : A) ^ n) • (A₀ : Set A))
    (ha : 1 < a) : RingNorm A where
  toFun := A₀.gaugeNorm ϖ a
  map_zero' := (gaugeNorm_eq_zero_iff hϖ hbasis ha).2 rfl
  add_le' r s := (gaugeNorm_add_le_max hϖ hbasis ha r s).trans
    (max_le_add_of_nonneg (gaugeNorm_nonneg (zero_lt_one.trans ha) r)
      (gaugeNorm_nonneg (zero_lt_one.trans ha) s))
  neg' r := gaugeNorm_neg r
  mul_le' r s := gaugeNorm_mul_le hϖ hbasis ha r s
  eq_zero_of_map_eq_zero' _ hr := (gaugeNorm_eq_zero_iff hϖ hbasis ha).1 hr

end Subring
