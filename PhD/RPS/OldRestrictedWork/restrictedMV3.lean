import Mathlib

namespace RestrictedMvPowerSeries

open MvPowerSeries Filter
open scoped Topology

abbrev range_sum {σ : Type*} : (σ →₀ ℕ) → ℕ :=
  fun n ↦ Finsupp.sum n (fun i ↦ n i)
  -- seems overcomplicated; not sure if this is prefered over the other definition

/-
abbrev range_sum' {σ : Type*} : (σ →₀ ℕ) → ℕ :=
  fun n ↦ ∑ i ∈ n.support, n i
  -- could still PR work on range_sum

lemma test {σ : Type*} (n : σ →₀ ℕ) : range_sum n = range_sum' n := by
  unfold range_sum range_sum'
  rw [Finsupp.sum]
  simp only [Pi.natCast_apply]
  simp only [Nat.cast_id]
-/

-- Q : Do I need to change c from ℝ to σ → ℝ, i.e. a tuple instead of just a single value?

def IsRestricted {R : Type*} [NormedRing R] (c : ℝ) {σ : Type*} (f : MvPowerSeries σ R) :=
  Tendsto (fun (t : σ →₀ ℕ) ↦ (norm (coeff t f)) * c^(range_sum t)) Filter.cofinite (𝓝 0)

--Dont want to be using this
lemma isRestricted_iff {R : Type*} [NormedRing R] (c : ℝ) {σ : Type*} (f : MvPowerSeries σ R) :
    IsRestricted c f ↔ ∀ ε > 0, {t | ε ≤ ‖(norm (coeff t f)) * c^(range_sum t)‖}.Finite := by
  simp [IsRestricted, NormedAddCommGroup.tendsto_nhds_zero]


lemma isRestricted_iff_abs {R : Type*} [NormedRing R] (c : ℝ) {σ : Type*}
    (f : MvPowerSeries σ R) : IsRestricted c f ↔ IsRestricted |c| f := by
  simp [IsRestricted, NormedAddCommGroup.tendsto_nhds_zero]

lemma zero {R : Type*} [NormedRing R] (c : ℝ) {σ : Type*} :
    IsRestricted c (0 : MvPowerSeries σ R) := by
  simpa [IsRestricted] using tendsto_const_nhds

/-- The set of `‖coeff n f‖ * c ^ (range_sum n)` for a given power series `f` and parameter `c`. -/
def convergenceSet {R : Type*} [NormedRing R] (c : ℝ) {σ : Type*} (f : MvPowerSeries σ R) : Set ℝ :=
  {‖(coeff n) f‖ * c^(range_sum n) | n : (σ →₀ ℕ)}

/-
-- maybe not neccesary; not being used right now
lemma convergenceSet_monomial {R : Type*} [NormedRing R] (c : ℝ) {σ : Type*} [Nonempty σ]
    (n : σ →₀ ℕ) (a : R) : convergenceSet c (monomial n a) = {‖a‖ * c ^ (range_sum n), 0} := by
  letI := Classical.typeDecidableEq σ
  simp_rw [convergenceSet]
  simp_rw [coeff_monomial]
  ext t
  constructor <;> intro ht
  · obtain ⟨b, hb⟩ := ht
    split at hb
    · expose_names; aesop
    · aesop
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
    rcases ht with h | h
    · aesop
    · obtain ⟨m, hm⟩ : ∃ m : σ →₀ ℕ, n ≠ m := by
        exact ⟨n + (Finsupp.single (Classical.arbitrary σ) 1), by simp⟩
      exact ⟨m, by aesop⟩
-/

lemma monomial {R : Type*} [NormedRing R] (c : ℝ) {σ : Type*} (n : σ →₀ ℕ) (a : R) :
    IsRestricted c (monomial n a) := by
  letI := Classical.typeDecidableEq σ
  simp_rw [IsRestricted, coeff_monomial]
  refine tendsto_nhds_of_eventually_eq ?_
  simp only [mul_eq_zero, norm_eq_zero, ite_eq_right_iff, pow_eq_zero_iff', ne_eq,
    eventually_cofinite, not_or, Classical.not_imp, not_and, Decidable.not_not]
  have : {x | (x = n ∧ ¬a = 0) ∧ (c = 0 → range_sum x = 0)} ⊆ {x | x = n} := by
    simp
  refine Set.Finite.subset ?_ this
  aesop

/-
-- there has to be a better way
lemma monomial {R : Type*} [NormedRing R] (c : ℝ) {σ : Type*} (n : σ →₀ ℕ) (a : R) :
    IsRestricted c (monomial n a) := by
  letI := Classical.typeDecidableEq σ
  rcases eq_or_ne 0 a with h | h
  · have : MvPowerSeries.monomial n 0 = (0 : MvPowerSeries σ R) := by
      simp only [map_zero]
    simpa [←h, this] using zero c
  · rw [isRestricted_iff]
    intro ε hε
    simp only [norm_mul, norm_pow, Real.norm_eq_abs, abs_norm, coeff_monomial]
    rcases le_or_gt ε (‖a‖ * |c| ^ range_sum n) with h1 | h1
    · have : {t | ε ≤ ‖if t = n then a else 0‖ * |c| ^ range_sum t} = {n} := by
        ext i
        simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
        constructor <;> intro hε'
        · split at hε'
          · aesop
          · simp only [norm_zero, zero_mul] at hε'
            contrapose hε
            exact Std.not_lt.mpr hε'
        · aesop
      simp only [this, Set.finite_singleton]
    · have : {t | ε ≤ ‖if t = n then a else 0‖ * |c| ^ range_sum t} = ∅ := by
        aesop
      simp only [this, Set.finite_empty]
-/

lemma one {R : Type*} [NormedRing R] (c : ℝ) {σ : Type*} :
    IsRestricted c (1 : MvPowerSeries σ R) := by
  exact monomial c 0 1

lemma C {R : Type*} [NormedRing R] (c : ℝ) {σ : Type*} [Nonempty σ] (a : R) :
    IsRestricted c (C (σ := σ) a) := by
  simpa [monomial_zero_eq_C_apply] using monomial c 0 a


/-
-- maybe see if this API exists, but it will be very useful
lemma subset_function_le {T : Type*} (f g : T → ℝ) (ε : ℝ) :
    (∀ b, f b ≤ g b) → {a | ε ≤ f a} ⊆ {a | ε ≤ g a} := by
  intro h
  simp only [Set.setOf_subset_setOf]
  intro a ha
  exact Std.IsPreorder.le_trans ε (f a) (g a) ha (h a)
-- definitely should use this to golf add proof
-/

lemma add {R : Type*} [NormedRing R] (c : ℝ) {σ : Type*} {f g : MvPowerSeries σ R}
    (hf : IsRestricted c f) (hg : IsRestricted c g) : IsRestricted c (f + g) := by
  rw [isRestricted_iff_abs, IsRestricted] at *
  have := hf.add hg
  simp at this
  have h0 : Tendsto (fun x : σ →₀ ℕ => 0) cofinite (nhds (0 : ℝ)) := by
    rw [NormedAddCommGroup.tendsto_nhds_zero]
    aesop
  apply Filter.Tendsto.squeeze h0 this
  <;> refine Pi.le_def.mpr ?_
  <;> intro n
  · positivity
  · simp only [map_add]
    have : ‖(coeff n) f + (coeff n) g‖ * |c| ^ range_sum n ≤
      (‖(coeff n) f‖ + ‖coeff n g‖)  * |c| ^ range_sum n := by
     exact mul_le_mul_of_nonneg (norm_add_le _ _) (by rfl) (by simp) (by simp)
    grind

/-
-- I reckon I can golf this a ton by combining first set inclusions and using a calc _ ...
-- surely can combine proofs of HF and HG too
lemma add {R : Type*} [NormedRing R] (c : ℝ) {σ : Type*} {f g : MvPowerSeries σ R}
    (hf : IsRestricted c f) (hg : IsRestricted c g) : IsRestricted c (f + g) := by
  rw [isRestricted_iff_abs, isRestricted_iff]
  simp only [map_add]
  have (t : σ →₀ ℕ) : ‖(coeff t) f + (coeff t) g‖ * |c| ^ range_sum t ≤
      (‖(coeff t) f‖ + ‖coeff t g‖)  * |c| ^ range_sum t := by
    exact mul_le_mul_of_nonneg (norm_add_le _ _) (by rfl) (by simp) (by simp)
  intro ε hε
  simp only [norm_mul, norm_pow, Real.norm_eq_abs, abs_abs]
  have h : {t | ε ≤ |‖(coeff t) f + (coeff t) g‖| * |c| ^ range_sum t} ⊆
      {t | ε ≤ (‖(coeff t) f‖ + ‖coeff t g‖)  * |c| ^ range_sum t} := by
    simp only [abs_norm, Set.setOf_subset_setOf]
    intro n hn
    exact Std.IsPreorder.le_trans ε _ _ hn (this n)
  refine Set.Finite.subset ?_ h
  have h : {t | ε ≤ (‖(coeff t) f‖ + ‖coeff t g‖)  * |c| ^ range_sum t} ⊆
      {t | ε ≤ 2 * (max (‖(coeff t) f‖) (‖coeff t g‖)) * |c| ^ range_sum t} := by
    simp only [Set.setOf_subset_setOf]
    intro n hn
    have : (‖(coeff n) f‖ + ‖coeff n g‖)  * |c| ^ range_sum n ≤
        2 * (max (‖(coeff n) f‖) (‖coeff n g‖)) * |c| ^ range_sum n := by
      exact mul_le_mul_of_nonneg (by grind) (by rfl) (add_nonneg (by simp) (by simp)) (by simp)
    exact Std.IsPreorder.le_trans ε _ _ hn this
  refine Set.Finite.subset ?_ h
  have h : {t | ε ≤ 2 * max ‖(coeff t) f‖ ‖(coeff t) g‖ * |c| ^ range_sum t} ⊆
      {t | ε ≤ 2 * ‖(coeff t) f‖ * |c| ^ range_sum t} ∪
      {t | ε ≤ 2 * ‖(coeff t) g‖ * |c| ^ range_sum t} := by
    intro n hn
    simp only [Set.mem_union, Set.mem_setOf_eq] at hn ⊢
    grind
  refine Set.Finite.subset ?_ h
  have (h : MvPowerSeries σ R) : {t | ε ≤ 2 * ‖(coeff t) h‖ * |c| ^ range_sum t} =
      {t | ε / 2 ≤ ‖(coeff t) h‖ * |c| ^ range_sum t} := by
    ext m
    simp only [Set.mem_setOf_eq]
    field_simp -- poggers
  simp_rw [this]
  have HF : {t | ε / 2 ≤ ‖(coeff t) f‖ * |c| ^ range_sum t}.Finite := by
    rw [isRestricted_iff_abs, isRestricted_iff] at hf
    simp only [gt_iff_lt, norm_mul, norm_pow, Real.norm_eq_abs, abs_abs, abs_norm] at hf
    exact hf (ε / 2) (by aesop)
  have HG : {t | ε / 2 ≤ ‖(coeff t) g‖ * |c| ^ range_sum t}.Finite := by
    rw [isRestricted_iff_abs, isRestricted_iff] at hg
    simp only [gt_iff_lt, norm_mul, norm_pow, Real.norm_eq_abs, abs_abs, abs_norm] at hg
    exact hg (ε / 2) (by aesop)
  exact Set.Finite.union HF HG
-/

lemma smul {R : Type*} [NormedRing R] (c : ℝ) {σ : Type*} {f : MvPowerSeries σ R}
    (hf : IsRestricted c f) (r : R) : IsRestricted c (r • f) := by
  rw [isRestricted_iff_abs, IsRestricted] at *
  have : Tendsto (fun t ↦ ‖r‖ * ‖(coeff t) f‖ * |c| ^ range_sum t) cofinite (𝓝 0) := by
    have := Filter.Tendsto.const_mul ‖r‖ hf
    grind
  have h0 : Tendsto (fun x : σ →₀ ℕ => 0) cofinite (nhds (0 : ℝ)) := by
    rw [NormedAddCommGroup.tendsto_nhds_zero]
    aesop
  apply Filter.Tendsto.squeeze h0 this
  <;> refine Pi.le_def.mpr ?_
  <;> intro n
  · positivity
  · exact mul_le_mul_of_nonneg (norm_mul_le _ _) (by rfl) (by simp) (by simp)

/-
lemma smul {R : Type*} [NormedRing R] (c : ℝ) {σ : Type*} {f : MvPowerSeries σ R}
    (hf : IsRestricted c f) (r : R) : IsRestricted c (r • f) := by
  if h : r = 0 then simpa [h] using (zero c) else
  rw [isRestricted_iff_abs, isRestricted_iff]
  simp only [gt_iff_lt, map_smul, smul_eq_mul, norm_mul, norm_pow, Real.norm_eq_abs,
    abs_abs, abs_norm]
  intro ε hε
  have (t : σ →₀ ℕ) : ‖r * (coeff t) f‖ * |c| ^ range_sum t ≤
      ‖r‖ * ‖coeff t f‖ * |c| ^ range_sum t := by
    exact mul_le_mul_of_nonneg (norm_mul_le _ _) (by rfl) (by simp) (by simp)
  refine Set.Finite.subset ?_ (subset_function_le _ _ ε this)
  rw [isRestricted_iff_abs, isRestricted_iff] at hf
  specialize hf (ε / ‖r‖) (by aesop)
  field_simp at hf
  simp only [norm_mul, norm_pow, Real.norm_eq_abs, abs_abs, abs_norm, ← mul_assoc] at hf
  exact hf
-/

lemma nsmul {R : Type*} [NormedRing R] (c : ℝ) {σ : Type*} (n : ℕ)
    (f : MvPowerSeries σ R) (hf : IsRestricted c f) : IsRestricted c (n • f) := by
  convert smul c hf (n : R)
  ext _ _
  simp_rw [map_smul, smul_eq_mul, map_nsmul, nsmul_eq_mul]

lemma zsmul {R : Type*} [NormedRing R] (c : ℝ) {σ : Type*} (n : ℤ)
    (f : MvPowerSeries σ R) (hf : IsRestricted c f) : IsRestricted c (n • f) := by
  convert smul c hf (n : R)
  ext _ _
  simp_rw [map_smul, smul_eq_mul, map_zsmul, zsmul_eq_mul]


---- Trying to find a nice way to do the multiplication

open IsUltrametricDist

lemma tendsto_antidiagonal {R S C: Type*} [AddMonoid R] [Finset.HasAntidiagonal R]
    {f g : R → S} [NormedRing S] [IsUltrametricDist S] {C : R → ℝ} -- need C to be monoid morphism to ℝ with mult
    (hf : Tendsto (fun i ↦ ‖f i‖ * C i ) cofinite (𝓝 0))
    (hg : Tendsto (fun i ↦ ‖g i‖ * C i) cofinite (𝓝 0)) :
    Tendsto (fun a ↦ ‖∑ p ∈ Finset.antidiagonal a, (f p.1 * g p.2)‖ * C a) cofinite (𝓝 0) := by
  rw [@NormedAddCommGroup.tendsto_nhds_zero] at *
  simp only [gt_iff_lt, Real.norm_eq_abs, eventually_cofinite, not_lt] at *

  sorry

lemma mul' {R : Type*} [NormedRing R] [IsUltrametricDist R] {σ : Type*}
    {f g : MvPowerSeries σ R} (hf : IsRestricted 1 f) (hg : IsRestricted 1 g) :
    IsRestricted 1 (f * g) := by
  letI := Classical.typeDecidableEq σ
  letI : Finset.HasAntidiagonal (σ →₀ ℕ) := by
    exact Finsupp.instHasAntidiagonal
  rw [isRestricted_iff_abs, IsRestricted] at *
  simp_rw [coeff_mul]
  simp only [abs_one, one_pow, mul_one] at *
  have := tendsto_antidiagonal hf hg
  exact this
  /-
  have h0 : Tendsto (fun x : σ →₀ ℕ => 0) cofinite (nhds (0 : ℝ)) := by
    rw [NormedAddCommGroup.tendsto_nhds_zero]
    aesop
  apply Filter.Tendsto.squeeze h0 this
  <;> refine Pi.le_def.mpr ?_
  <;> intro n
  · positivity
  · simp_rw [coeff_mul]
    -- do I have the right set up
    sorry
  -/

lemma isRestricted_BddAbove {R : Type*} [NormedRing R] (c : ℝ) {σ : Type*} {f : MvPowerSeries σ R}
    (hf : IsRestricted c f) : BddAbove (convergenceSet c f) := by
  refine bddAbove_def.mpr ?_
  rw [isRestricted_iff] at hf
  simp only [gt_iff_lt, norm_mul, norm_pow, Real.norm_eq_abs, abs_norm] at hf
  specialize hf 1 (by simp)
  rw [convergenceSet]
  letI set := {a | ∃ t ∈ {t | 1 ≤ ‖(coeff t) f‖ * |c| ^ range_sum t},
    a = ‖(coeff t) f‖ * |c| ^ range_sum t}
  rcases isEmpty_or_nonempty set with h | h
  · use 1
    simp only [Set.mem_setOf_eq, forall_exists_index, forall_apply_eq_imp_iff]
    intro a
    have : IsEmpty {t | 1 ≤ ‖(coeff t) f‖ * |c| ^ range_sum t} := by
      contrapose h
      aesop
    have : a ∉ {t | 1 ≤ ‖(coeff t) f‖ * |c| ^ range_sum t} := by
      contrapose this
      aesop
    simp only [Set.mem_setOf_eq, not_le] at this
    calc _ ≤ ‖(coeff a) f‖ * |c| ^ range_sum a := by

            sorry
         _ ≤ 1 := Std.le_of_lt this
  · have set_fin : set.Finite := by
      simp_rw [set]
      letI fun1 := fun n : σ →₀ ℕ ↦ ‖(coeff n) f‖ * |c| ^ range_sum n
      have : {a | ∃ t ∈ {t | 1 ≤ ‖(coeff t) f‖ * |c| ^ range_sum t},
          a = ‖(coeff t) f‖ * |c| ^ range_sum t} = fun1 '' {t | 1 ≤ ‖(coeff t) f‖ * |c| ^ range_sum t}
          := by
        aesop
      simp_rw [this]
      exact Set.Finite.image fun1 hf
    obtain ⟨_, ha⟩ : Nonempty (Set.Finite.toFinset set_fin) := by
      aesop
    obtain ⟨b, hb⟩ := Finset.max_of_mem ha
    use max 1 b
    intro a h
    simp only [Set.mem_setOf_eq] at h
    obtain ⟨n, eq⟩ := h
    rw [← eq]
    rcases Decidable.em (n ∈ {t | 1 ≤ ‖(coeff t) f‖ * |c| ^ range_sum t}) with h | h
    · have : ‖(coeff n) f‖ * |c| ^ range_sum n ∈ set := by
        use n
      have : ‖(coeff n) f‖ * |c| ^ range_sum n ≤ b := by

        sorry
      calc _ ≤ ‖(coeff n) f‖ * |c| ^ range_sum n := by

              sorry
           _ ≤ b := this
           _ ≤ max 1 b := le_max_right 1 b
    · simp only [Set.mem_setOf_eq, not_le] at h
      calc _ ≤ ‖(coeff n) f‖ * |c| ^ range_sum n := by

            sorry
         _ ≤ 1 := Std.le_of_lt h
         _ ≤ max 1 b := le_max_left 1 b

open IsUltrametricDist

lemma mul2 {R : Type*} [NormedRing R] [IsUltrametricDist R] (c : ℝ) {σ : Type*}
    {f g : MvPowerSeries σ R} (hf : IsRestricted c f) (hg : IsRestricted c g) :
    IsRestricted c (f * g) := by
  letI := Classical.typeDecidableEq σ
  rw [IsRestricted] at *

  have := hf.max hg
  have h0 : Tendsto (fun x : σ →₀ ℕ => 0) cofinite (nhds (0 : ℝ)) := by sorry
  simp at this
  apply Filter.Tendsto.squeeze h0 this

  sorry
  refine Pi.le_def.mpr ?_
  intro n

  sorry



lemma mul {R : Type*} [NormedRing R] [IsUltrametricDist R] (c : ℝ) {σ : Type*}
    {f g : MvPowerSeries σ R} (hf : IsRestricted c f) (hg : IsRestricted c g) :
    IsRestricted c (f * g) := by
  letI := Classical.typeDecidableEq σ

  rw [isRestricted_iff_abs, isRestricted_iff]
  intro ε hε
  simp only [norm_mul, norm_pow, Real.norm_eq_abs, abs_abs, abs_norm]
  simp_rw [coeff_mul]
  have H (t : σ →₀ ℕ) := exists_norm_finset_sum_le (M := R) (Finset.antidiagonal t)
    (fun a ↦ (coeff a.1) f * (coeff a.2) g)
  simp only [Finset.mem_antidiagonal, Prod.exists] at H
  have (t : σ →₀ ℕ) : ∃ a b, ((Finset.antidiagonal t).Nonempty → a + b = t) ∧
      ‖∑ p ∈ Finset.antidiagonal t, (coeff p.1) f * (coeff p.2) g‖ *
      |c| ^ range_sum t ≤ (‖(coeff a) f * (coeff b) g‖) * |c| ^ range_sum t := by
    obtain ⟨a, b, heq, h⟩ := H t
    use a, b
    constructor
    · exact heq
    · exact mul_le_mul_of_nonneg (by grind) (by rfl) (by simp) (by simp)
  have : {t | ε ≤ ‖∑ p ∈ Finset.antidiagonal t, (coeff p.1) f * (coeff p.2) g‖ * |c| ^ range_sum t}
      ⊆ {t | IsEmpty (Finset.antidiagonal t)} ∪
        {t | ((Finset.antidiagonal t).Nonempty) ∧ ∃ a b, a + b = t ∧
             ε ≤ (‖(coeff a) f * (coeff b) g‖) * |c| ^ range_sum t} := by
    intro n hn
    simp only [Set.mem_union, Set.mem_setOf_eq] at ⊢ hn
    rcases isEmpty_or_nonempty (Finset.antidiagonal n) with h | h
    · aesop
    · right
      obtain ⟨a, b, heq, h'⟩ := H n
      constructor
      · exact Finset.nonempty_coe_sort.mp h
      use a, b
      constructor
      · exact heq (Finset.nonempty_coe_sort.mp h)
      · exact Std.IsPreorder.le_trans ε _ _ hn
          (mul_le_mul_of_nonneg (by grind) (by rfl) (by simp) (by simp))
  refine Set.Finite.subset ?_ this
  simp only [Finset.mem_antidiagonal, Set.finite_union]
  constructor
  · -- think this should just be true vacuously?
    have : {t | IsEmpty { x : (σ →₀ ℕ) × (σ →₀ ℕ) // x.1 + x.2 = t }} = ∅ := by
      ext i
      constructor
      · -- not sure if what I have written is nonsense
        sorry
      · aesop
    sorry
  · have (a b t : σ →₀ ℕ) (h : a + b = t) : ‖(coeff a) f * (coeff b) g‖ * |c| ^ range_sum t  ≤
        ‖(coeff a) f‖ * |c| ^ range_sum a * ‖(coeff b) g‖ * |c| ^ range_sum b := by
      calc _ ≤ ‖(coeff a) f‖ * ‖(coeff b) g‖ * |c| ^ range_sum t := by
            exact (mul_le_mul_of_nonneg (norm_mul_le _ _)) (by rfl) (by simp) (by simp)
           _ = ‖(coeff a) f‖ * |c| ^ range_sum a * ‖(coeff b) g‖ * |c| ^ range_sum b := by
            simp_rw [← h]
            ring_nf

            sorry
    have : {t | (Finset.antidiagonal t).Nonempty ∧ ∃ a b, a + b = t ∧
                ε ≤ ‖(coeff a) f * (coeff b) g‖ * |c| ^ range_sum t} ⊆
        {t | (Finset.antidiagonal t).Nonempty ∧ ∃ a b, a + b = t ∧
             ε ≤ ‖(coeff a) f‖ * |c| ^ range_sum a * ‖(coeff b) g‖ * |c| ^ range_sum b} := by
      intro n hn
      simp only [Set.mem_setOf_eq] at ⊢ hn
      obtain ⟨h', a, b, heq, h⟩ := hn
      constructor
      · exact h'
      · use a, b
        constructor
        · exact heq
        · specialize this a b n heq
          exact Std.IsPreorder.le_trans ε _ _ h this
    refine Set.Finite.subset ?_ this
    refine Set.Finite.subset ?_ (Set.sep_subset_setOf _ _)
    rw [isRestricted_iff_abs] at hg
    obtain ⟨B, hB1, hB2⟩ := (bddAbove_iff_exists_ge 1).mp (isRestricted_BddAbove |c| hg)

    -- I am not sure if this is the correct method from here
    -- may need to break into two cases and take the intersection when I bound each function

    have : {x | ∃ a b, a + b = x ∧
                ε ≤ ‖(coeff a) f‖ * |c| ^ range_sum a * ‖(coeff b) g‖ * |c| ^ range_sum b} ⊆
        {x | ∃ a b, a + b = x ∧ ε ≤ ‖(coeff a) f‖ * |c| ^ range_sum a * B} := by
      intro n hn
      simp only [Set.mem_setOf_eq, exists_and_right] at hn ⊢
      obtain ⟨a, b, eq, h⟩ := hn
      use a
      constructor
      · use b
      ·
        sorry
    refine Set.Finite.subset ?_ this
    have : {x |  ε ≤ ‖(coeff x) f‖ * |c| ^ range_sum x * B}.Finite := by
      rw [isRestricted_iff_abs, isRestricted_iff] at hf
      simp only [gt_iff_lt, norm_mul, norm_pow, Real.norm_eq_abs, abs_abs, abs_norm] at hf
      specialize hf (ε / B) (by positivity)
      field_simp at hf

      sorry

    sorry

end RestrictedMvPowerSeries
