import Mathlib

namespace RestrictedMvPowerSeries

open MvPowerSeries Filter
open scoped Topology Pointwise

def IsRestricted {R : Type*} [NormedRing R] {σ : Type*} (c : σ → ℝ) (f : MvPowerSeries σ R) :=
  Tendsto (fun (t : σ →₀ ℕ) ↦ (norm (coeff t f)) * ∏ i ∈ t.support, c i ^ t i) Filter.cofinite (𝓝 0)

lemma isRestricted_iff_abs {R : Type*} [NormedRing R] {σ : Type*} (c : σ → ℝ)
    (f : MvPowerSeries σ R) : IsRestricted c f ↔ IsRestricted |c| f := by
  simp [IsRestricted, NormedAddCommGroup.tendsto_nhds_zero]

lemma zero {R : Type*} [NormedRing R] {σ : Type*} (c : σ → ℝ) :
    IsRestricted c (0 : MvPowerSeries σ R) := by
  simpa [IsRestricted] using tendsto_const_nhds

/-- The set of `‖coeff t f‖ * ∏ i : t.support, c i ^ t i` for a given power series `f`
  and tuple `c`. -/
def convergenceSet {R : Type*} [NormedRing R] {σ : Type*} (c : σ → ℝ) (f : MvPowerSeries σ R) :
  Set ℝ := {‖(coeff t) f‖ * ∏ i : t.support, c i ^ t i | t : (σ →₀ ℕ)}

lemma monomial {R : Type*} [NormedRing R] {σ : Type*} (c : σ → ℝ) (n : σ →₀ ℕ) (a : R) :
    IsRestricted c (monomial n a) := by
  letI := Classical.typeDecidableEq σ
  simp_rw [IsRestricted, coeff_monomial]
  refine tendsto_nhds_of_eventually_eq ?_
  simp only [mul_eq_zero, norm_eq_zero, ite_eq_right_iff,
    eventually_cofinite, not_or, Classical.not_imp]
  have : {x | (x = n ∧ ¬a = 0) ∧ ¬∏ i ∈ x.support, c i ^ x i = 0} ⊆ {x | x = n} := by
    simp only [Set.setOf_eq_eq_singleton, Set.subset_singleton_iff, Set.mem_setOf_eq, and_imp,
      forall_eq, implies_true]
  refine Set.Finite.subset ?_ this
  aesop

lemma one {R : Type*} [NormedRing R] {σ : Type*} (c : σ → ℝ) :
    IsRestricted c (1 : MvPowerSeries σ R) := by
  exact monomial c 0 1

lemma C {R : Type*} [NormedRing R] {σ : Type*} (c : σ → ℝ) (a : R) :
    IsRestricted c (C (σ := σ) a) := by
  simpa [monomial_zero_eq_C_apply] using monomial c 0 a

lemma add {R : Type*} [NormedRing R] {σ : Type*} (c : σ → ℝ) {f g : MvPowerSeries σ R}
    (hf : IsRestricted c f) (hg : IsRestricted c g) : IsRestricted c (f + g) := by
  rw [isRestricted_iff_abs, IsRestricted] at *
  have := hf.add hg
  simp only [Pi.abs_apply, add_zero] at this
  have h0 : Tendsto (fun x : σ →₀ ℕ => 0) cofinite (nhds (0 : ℝ)) := by
    rw [NormedAddCommGroup.tendsto_nhds_zero]
    aesop
  apply Filter.Tendsto.squeeze h0 this
  <;> refine Pi.le_def.mpr ?_
  <;> intro n
  · refine mul_nonneg (norm_nonneg _) ?_
    have : ∀ i ∈ n.support, 0 ≤ |c| i ^ n i := by
      aesop
    exact Finset.prod_nonneg fun i a ↦ this i a
  · simp only [map_add]
    have : ‖(coeff n) f + (coeff n) g‖ * ∏ i ∈ n.support, |c| i ^ n i ≤
        (‖(coeff n) f‖ + ‖coeff n g‖)  * ∏ i ∈ n.support, |c| i ^ n i := by
      refine mul_le_mul_of_nonneg (norm_add_le _ _) (by rfl) (by simp) ?_
      have : ∀ i ∈ n.support, 0 ≤ |c| i ^ n i := by
        aesop
      exact Finset.prod_nonneg fun i a ↦ this i a
    simpa only [add_mul] using this

lemma neg {R : Type*} [NormedRing R] {σ : Type*} (c : σ → ℝ) {f : MvPowerSeries σ R}
    (hf : IsRestricted c f) : IsRestricted c (- f) := by
  rw [isRestricted_iff_abs, IsRestricted] at *
  simpa using hf

instance {R : Type*} [NormedRing R] {σ : Type*} (c : σ → ℝ) :
    AddSubgroup (MvPowerSeries σ R) where
  carrier := IsRestricted c
  zero_mem' := zero c
  add_mem' := add c
  neg_mem' := neg c

lemma smul {R : Type*} [NormedRing R] {σ : Type*} (c : σ → ℝ) {f : MvPowerSeries σ R}
    (hf : IsRestricted c f) (r : R) : IsRestricted c (r • f) := by
  rw [isRestricted_iff_abs, IsRestricted] at *
  have : Tendsto (fun t ↦ ‖r‖ * ‖(coeff t) f‖ * ∏ i ∈ t.support, |c| i ^ t i) cofinite (𝓝 0) := by
    have := Filter.Tendsto.const_mul ‖r‖ hf
    grind
  have h0 : Tendsto (fun x : σ →₀ ℕ => 0) cofinite (nhds (0 : ℝ)) := by
    rw [NormedAddCommGroup.tendsto_nhds_zero]
    aesop
  apply Filter.Tendsto.squeeze h0 this
  <;> refine Pi.le_def.mpr ?_
  <;> intro n
  · refine mul_nonneg (norm_nonneg _) ?_
    have : ∀ i ∈ n.support, 0 ≤ |c| i ^ n i := by
      aesop
    exact Finset.prod_nonneg fun i a ↦ this i a
  · refine mul_le_mul_of_nonneg (norm_mul_le _ _) (by rfl) (by simp) ?_
    have : ∀ i ∈ n.support, 0 ≤ |c| i ^ n i := by
      aesop
    exact Finset.prod_nonneg fun i a ↦ this i a

lemma nsmul {R : Type*} [NormedRing R] {σ : Type*} (c : σ → ℝ) (n : ℕ)
    (f : MvPowerSeries σ R) (hf : IsRestricted c f) : IsRestricted c (n • f) := by
  convert smul c hf (n : R)
  ext _ _
  simp_rw [map_smul, smul_eq_mul, map_nsmul, nsmul_eq_mul]

lemma zsmul {R : Type*} [NormedRing R] {σ : Type*} (c : σ → ℝ) (n : ℤ)
    (f : MvPowerSeries σ R) (hf : IsRestricted c f) : IsRestricted c (n • f) := by
  convert smul c hf (n : R)
  ext _ _
  simp_rw [map_smul, smul_eq_mul, map_zsmul, zsmul_eq_mul]

open IsUltrametricDist

def foo {S : Type*} [Nonempty S] {f : S → ℝ} (hf : Tendsto (fun i ↦ f i) cofinite (𝓝 0)) :
    ∃ F, ∀ i, |f i| ≤ F := by
  have ⟨a, ha⟩ := Tendsto.bddAbove_range_of_cofinite hf
  have ⟨b, hb⟩ := Tendsto.bddBelow_range_of_cofinite hf
  use max |a| |b|
  intro i
  rw [mem_upperBounds] at ha
  specialize ha (f i) (by simp)
  rw [mem_lowerBounds] at hb
  specialize hb (f i) (by simp)
  simp only [le_sup_iff]
  rcases lt_or_ge (f i) 0 with h | h
  · right
    have : b < 0 := by
      calc _ ≤ f i := hb
           _ < 0 := h
    have := le_of_lt this
    have h := le_of_lt h
    simp_all only [← abs_eq_neg_self]
    aesop
  · left
    have : 0 ≤ a := by
      calc _ ≤ f i := h
           _ ≤ a := ha
    simp_all only [← abs_eq_self] -- perhaps this is already done or can be done easier?

def cofinite_max {S : Type*} [Nonempty S] {f : S → ℝ}
    (hf : Tendsto (fun i ↦ f i) cofinite (𝓝 0)) :
    ∃ F, 0 < F ∧  ∀ i : S, |f i| ≤ F := by
  obtain ⟨F, hF⟩ := foo hf
  use max F 1
  aesop

lemma tendsto_antidiagonal {M S : Type*} [AddMonoid M] [Finset.HasAntidiagonal M]
    {f g : M → S} [NormedRing S] [IsUltrametricDist S] {C : M → ℝ}
    (hC : ∀ a b, C (a + b) = C a * C b) -- should this be stated differently?
    -- need C to be monoid morphism to ℝ with mult
    (hf : Tendsto (fun i ↦ ‖f i‖ * C i ) cofinite (𝓝 0))
    (hg : Tendsto (fun i ↦ ‖g i‖ * C i) cofinite (𝓝 0)) :
    Tendsto (fun a ↦ ‖∑ p ∈ Finset.antidiagonal a, (f p.1 * g p.2)‖ * C a) cofinite (𝓝 0) := by
  obtain ⟨F, Fpos, hF⟩ := cofinite_max hf
  have ⟨G, Gpos, hG⟩ := cofinite_max hg
  simp only [NormedAddCommGroup.tendsto_nhds_zero, gt_iff_lt, Real.norm_eq_abs, eventually_cofinite,
    not_lt] at *
  intro ε hε
  let I := {x | ε / G ≤ |‖f x‖ * C x|}
  let J := {x | ε / F ≤ |‖g x‖ * C x|}
  specialize hf (ε / G) (by positivity)
  specialize hg (ε / F) (by positivity)
  refine Set.Finite.subset (s := I + J) (Set.Finite.add (by aesop) (by aesop)) ?_
  by_contra h
  obtain ⟨t, ht, ht'⟩ := Set.not_subset.mp h
  simp only [abs_mul, abs_norm] at *
  have hh (i j : M) (ht_eq : t = i + j) : i ∉ I ∨ j ∉ J := by
    simp_rw [ht_eq] at ht'
    contrapose ht'
    simp only [not_or, not_not] at *
    use i; use ht'.1; use j; use ht'.2 -- must be a nicer way to write this
  have hij (i j : M) (ht_eq : t = i + j) : ‖f i * g j‖ * |C t| < ε := by
      calc
      _ ≤ ‖f i‖ * ‖g j‖ * |C t| :=
        mul_le_mul_of_nonneg (norm_mul_le _ _) (le_refl _) (norm_nonneg _) (abs_nonneg _)
      _ ≤ ‖f i‖ * ‖g j‖ * (|C i| * |C j|) :=
        mul_le_mul_of_nonneg (le_refl _) (by simp [ht_eq, hC]) (by positivity) (by positivity)
      _ = (‖f i‖ * |C i|) * (‖g j‖ * |C j|) := by
        ring
      _ < ε := by
        rcases hh i j ht_eq with hi | hj
        · rw [← div_mul_cancel₀ ε (ne_of_lt Gpos).symm]
          exact mul_lt_mul_of_nonneg_of_pos (by aesop) (hG j)
            (mul_nonneg (by positivity) (by positivity)) Gpos
        · rw [← div_mul_cancel₀ ε (ne_of_lt Fpos).symm, mul_comm]
          exact mul_lt_mul_of_nonneg_of_pos (by aesop) (hF i)
            (mul_nonneg (by positivity) (by positivity)) Fpos
  have Final : ‖∑ p ∈ Finset.antidiagonal t, f p.1 * g p.2‖ * |C t| < ε := by
    obtain ⟨k, hk, leq⟩ := exists_norm_finset_sum_le (Finset.antidiagonal t)
      (fun a ↦ f a.1 * g a.2)
    calc
    _ ≤ ‖f k.1 * g k.2‖ * |C t| := by
      exact mul_le_mul_of_nonneg (leq) (le_refl _) (by positivity) (by positivity)
    _ < ε := by
      have : (Finset.antidiagonal t).Nonempty := by
        refine Finset.nonempty_def.mpr ?_
        use (t, 0); simp
      have : t = k.1 + k.2 := by
        specialize hk this
        simp only [Finset.mem_antidiagonal] at hk
        exact hk.symm
      exact hij k.1 k.2 this
  grind

-- I should probably change all of this to @[toAdd] as well

lemma test1 {σ : Type*} (a b : σ →₀ ℕ) [DecidableEq σ] :
    (a + b).support = a.support ∪ (b.support \ a.support) := by
  apply Finset.Subset.antisymm_iff.mpr ?_
  constructor
  · simpa using Finsupp.support_add
  · intro i hi
    simp only [Finsupp.mem_support_iff, Finsupp.coe_add, Pi.add_apply, ne_eq, Nat.add_eq_zero,
      not_and]
    simp only [Finset.mem_union, Finsupp.mem_support_iff, ne_eq] at hi
    aesop

lemma test2 {σ : Type*} (a b : σ →₀ ℕ) [DecidableEq σ] :
    (a + b).support = (a.support \ b.support) ∪ b.support := by
  apply Finset.Subset.antisymm_iff.mpr ?_
  constructor
  · simp only [Finset.sdiff_union_self_eq_union]
    exact Finsupp.support_add
  · intro i hi
    simp only [Finsupp.mem_support_iff, Finsupp.coe_add, Pi.add_apply, ne_eq, Nat.add_eq_zero,
      not_and]
    simp only [Finset.sdiff_union_self_eq_union, Finset.mem_union, Finsupp.mem_support_iff,
      ne_eq] at hi
    aesop

lemma test3 {σ : Type*} (a b : σ →₀ ℕ) [DecidableEq σ] (f : σ → ℝ): ∏ i ∈ (a + b).support, f i =
    (∏ i ∈ a.support, f i) * ∏ i ∈ (b.support \ a.support) , f i := by
  rw [test1, Finset.prod_union]
  exact Finset.disjoint_sdiff

lemma test4 {σ : Type*} (a b : σ →₀ ℕ) [DecidableEq σ] (f : σ → ℝ) : ∏ i ∈ (a + b).support, f i =
    (∏ i ∈ (a.support \ b.support), f i) * ∏ i ∈ b.support, f i := by
  rw [test2, Finset.prod_union]
  exact Finset.sdiff_disjoint

lemma bar {σ : Type*} [DecidableEq σ] (c : σ → ℝ) (a b : σ →₀ ℕ) : ∏ i ∈ (a + b).support, |c| i ^ (a + b) i =
    (∏ i ∈ a.support, |c| i ^ a i) * ∏ i ∈ b.support, |c| ↑i ^ b i := by
  simp only [Pi.abs_apply, Finsupp.coe_add, Pi.add_apply]
  simp_rw [pow_add, Finset.prod_mul_distrib]
  rw [test3, test4]
  have h1 : ∏ i ∈ a.support \ b.support, |c i| ^ b i = 1 := by
    suffices (∀ i ∈ (a.support \ b.support), b i = 0) by
      have : ∀ i ∈ (a.support \ b.support), |c i| ^ b i = 1 := by
        aesop
      exact Finset.prod_eq_one this
    simp
  have h2 : ∏ i ∈ b.support \ a.support, |c i| ^ a i = 1 := by
    suffices (∀ i ∈ (b.support \ a.support), a i = 0) by
      have : ∀ i ∈ (b.support \ a.support), |c i| ^ a i = 1 := by
        aesop
      exact Finset.prod_eq_one this
    simp
  simp only [h2, mul_one, h1, one_mul]

lemma mul {R : Type*} [NormedRing R] [IsUltrametricDist R] {σ : Type*} (c : σ → ℝ)
    {f g : MvPowerSeries σ R} (hf : IsRestricted c f) (hg : IsRestricted c g) :
    IsRestricted c (f * g) := by
  letI := Classical.typeDecidableEq σ
  letI : Finset.HasAntidiagonal (σ →₀ ℕ) := by
    exact Finsupp.instHasAntidiagonal
  rw [isRestricted_iff_abs, IsRestricted] at *
  simp_rw [coeff_mul]
  have := tendsto_antidiagonal (bar c) hf hg
  exact this

instance {R : Type*} [NormedRing R] [IsUltrametricDist R] {σ : Type*} (c : σ → ℝ) :
    Subring (MvPowerSeries σ R) where
  toAddSubgroup := RestrictedMvPowerSeries.instAddSubgroupMvPowerSeriesOfReal_phD c
  one_mem' := one c
  mul_mem' := mul c


-- we can use this to get an upper bound on cofinite things
-- Filter.Tendsto.bddAbove_range_of_cofinite hf


/-
/-- Promoting restricted mv power series to its own type. -/
def  Crestricted {R : Type*} [NormedRing R] {σ : Type*} (c : σ → ℝ) : Type _ :=
  Subtype (IsRestricted (R := R) (σ := σ) c)

variable (R : Type*) [NormedRing R] {σ : Type*} (c : σ → ℝ) (f g : Crestricted (R := R) c)

instance : AddGroup (Crestricted (R := R) c) := by
  have := RestrictedMvPowerSeries.instAddSubgroupMvPowerSeriesOfReal_phD (R := R) c
  -- maybe I am not doing this correctly??
  sorry
-/
