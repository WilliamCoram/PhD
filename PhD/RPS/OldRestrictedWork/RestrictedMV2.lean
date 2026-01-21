import Mathlib

import Mathlib

namespace RestrictedMvPowerSeries

open MvPowerSeries Filter
open scoped Topology

abbrev range_sum {σ : Type*} : (σ →₀ ℕ) → ℕ :=
  fun n ↦ ∑ i ∈ n.support, n i

lemma foo {σ : Type*} (a b : σ →₀ ℕ) [DecidableEq σ] :
    (a + b).support = a.support ∪ (b.support \ a.support) := by
  apply Finset.Subset.antisymm_iff.mpr ?_
  constructor
  · simpa using Finsupp.support_add
  · intro i hi
    simp only [Finsupp.mem_support_iff, Finsupp.coe_add, Pi.add_apply, ne_eq, Nat.add_eq_zero,
      not_and]
    simp only [Finset.mem_union, Finsupp.mem_support_iff, ne_eq] at hi
    aesop

lemma foo' {σ : Type*} (a b : σ →₀ ℕ) [DecidableEq σ] :
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

lemma test {σ : Type*} (a b : σ →₀ ℕ) [DecidableEq σ] : ∑ i ∈ (a + b).support, a i =
    ∑ i ∈ a.support, a i + ∑ i ∈ (b.support \ a.support) , a i := by
  rw [foo, Finset.sum_union]
  exact Finset.disjoint_sdiff

lemma test2 {σ : Type*} (a b : σ →₀ ℕ) [DecidableEq σ] : ∑ i ∈ (a + b).support, b i =
    ∑ i ∈ (a.support \ b.support), b i + ∑ i ∈ b.support, b i := by
  rw [foo', Finset.sum_union]
  exact Finset.sdiff_disjoint

lemma range_sum_add {σ : Type*} [DecidableEq σ] (a b : σ →₀ ℕ) :
    range_sum (a + b) = range_sum (a) + range_sum (b) := by
  unfold range_sum
  simp only [Finsupp.coe_add, Pi.add_apply]
  rw [Finset.sum_add_distrib, test, test2]
  have h1 : ∑ i ∈ a.support \ b.support, b i = 0 := by
    aesop
  have h2 : ∑ i ∈ b.support \ a.support, a i = 0 := by
    aesop
  simp_rw [h1, h2]
  ring

lemma range_sum_smul {σ : Type*} (a : σ →₀ ℕ) (n : ℕ) :
    range_sum (n • a) = n * range_sum a := by
  unfold range_sum
  simp only [Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  rcases Nat.eq_zero_or_pos n with h | h
  · simp_rw [h]
    simp only [zero_mul, Finset.sum_const_zero]
  · have : (n • a).support = a.support := by
      refine Finsupp.support_smul_eq ?_
      exact Nat.ne_zero_of_lt h
    grw [this]

instance {σ : Type*} : LE (σ →₀ ℕ) where le f g := (range_sum f) ≤ (range_sum g)

lemma le_def {σ : Type*} {f g : σ →₀ ℕ} : f ≤ g ↔ (range_sum f) ≤ (range_sum g) := .rfl

instance {σ : Type*} : LT (σ →₀ ℕ) where lt f g := (range_sum f) < (range_sum g)

lemma lt_def {σ : Type*} {f g : σ →₀ ℕ} : f < g ↔ (range_sum f) < (range_sum g) := .rfl

instance preorder {σ : Type*} : Preorder (σ →₀ ℕ) where
  le_refl _ := by
    rw [le_def]
  le_trans _ _ _ := by
    exact Nat.le_trans
  lt_iff_le_not_ge a b := by
    simp_rw [le_def, lt_def, not_le, iff_and_self]
    exact Nat.le_of_succ_le

def le_total {σ : Type*} (a b : σ →₀ ℕ) : a ≤ b ∨ b ≤ a := by
  simp_rw [le_def]
  exact Nat.le_total _ _

instance {σ : Type*} : IsDirected (σ →₀ ℕ) (fun (a b : (σ →₀ ℕ)) ↦ (a ≤ b)) where
  directed a b := by
    rcases le_total a b with h | h
    · use b
    · use a

-- need to change this to the cofinite filter 
-- This is the proposed new definition!!
def IsRestricted_limit' {R : Type*} [NormedRing R] (c : ℝ) {σ : Type*} [Nonempty σ]
    (f : MvPowerSeries σ R) :=
  Tendsto (fun (t : σ →₀ ℕ) ↦ (norm (coeff t f)) * c^(range_sum t)) Filter.cofinite (𝓝 0)

def IsRestricted_limit {R : Type*} [NormedRing R] (c : ℝ) {σ : Type*} [Nonempty σ]
    (f : MvPowerSeries σ R) :=
  Tendsto (fun (t : σ →₀ ℕ) ↦ (norm (coeff t f)) * c^(range_sum t)) atTop (𝓝 0)

lemma isRestricted_limit_iff {R : Type*} [NormedRing R] (c : ℝ) {σ : Type*} [Nonempty σ]
    {f : MvPowerSeries σ R} : IsRestricted_limit c f ↔ ∀ ε, 0 < ε → ∃ (N : σ →₀ ℕ),
    ∀ (n : σ →₀ ℕ), N ≤ n → ‖‖(coeff n) f‖ * c^(range_sum n)‖ < ε := by
  simp [IsRestricted_limit, NormedAddCommGroup.tendsto_atTop]

lemma isRestricted_limit_iff_abs {R : Type*} [NormedRing R] (c : ℝ) {σ : Type*} [Nonempty σ]
    (f : MvPowerSeries σ R) : IsRestricted_limit c f ↔ IsRestricted_limit |c| f := by
  simp [isRestricted_limit_iff]

/-
  Originally, I did not have |c| - rather just c - in this definition... however consider
  f = ∑_n (-n) x_n, g = ∑_n (1/n) x_n^n ...
  f * g has terms of the form x_n^{n+1} i.e. for all degrees of monomoials, there is a term of
  coeff 1; i.e. f * g will not be restricted

  Thus we really need the |c| in convergenceSet
-/

/-- The set of `‖coeff n f‖ * c ^ (range_sum n)` for a given power series `f` and parameter `c`. -/
def convergenceSet {R : Type*} [NormedRing R] (c : ℝ) {σ : Type*} [Nonempty σ]
  (f : MvPowerSeries σ R) : Set ℝ := {‖(coeff n) f‖ * |c|^(range_sum n) | n : (σ →₀ ℕ)}

def IsRestricted_bdd {R : Type*} [NormedRing R] (c : ℝ) {σ : Type*} [Nonempty σ]
    (f : MvPowerSeries σ R) := BddAbove (convergenceSet c f)

-- This definition comes from a discussion of what restricted power series in infinitly many
-- variables should be.
-- I need BddAbove in the proof of Mul... so having the statement vacously allows me to use my proof
-- Rest of BddAbove should follow from Non-archimedean property (hopefully).

structure IsRestricted {R : Type*} [NormedRing R] (c : ℝ) {σ : Type*} [Nonempty σ]
    (f : MvPowerSeries σ R) : Prop where
  limit : IsRestricted_limit c f
  bdd : IsRestricted_bdd c f

lemma zero {R : Type*} [NormedRing R] (c : ℝ) {σ : Type*} [Nonempty σ] :
    IsRestricted c (0 : MvPowerSeries σ R) where
  limit := by
    simp [IsRestricted_limit]
  bdd := by
    rw [IsRestricted_bdd, convergenceSet]
    simp only [coeff_zero, norm_zero, zero_mul, exists_const, Set.setOf_eq_eq_singleton',
      bddAbove_singleton]

lemma monomial {R : Type*} [NormedRing R] (c : ℝ) {σ : Type*} [Nonempty σ] (n : σ →₀ ℕ)
    (a : R) : IsRestricted c (monomial n a) where
  limit := by
    let I := Classical.typeDecidableEq σ
    simp_rw [isRestricted_limit_iff, norm_mul, norm_pow, Real.norm_eq_abs, abs_norm]
    obtain ⟨m, hm⟩ : ∃ m : σ →₀ ℕ, n < m := by
      use n + Finsupp.single (Classical.choice (inferInstance : Nonempty σ)) 1
      simp_rw [lt_def, range_sum_add]
      simp only [lt_add_iff_pos_right]
      simp_rw [range_sum]
      have : ∑ i ∈ (fun₀ | Classical.choice (inferInstance : Nonempty σ) => 1).support,
          (fun₀ | Classical.choice (inferInstance : Nonempty σ) => 1) ↑i = 1 := by
        have : (fun₀ | Classical.choice (inferInstance : Nonempty σ) => 1).support =
            {Classical.choice (inferInstance : Nonempty σ)} := by
          ext i
          constructor
          · intro hi
            simp only [Finsupp.mem_support_iff, ne_eq] at hi
            simp only [Finset.mem_singleton]
            contrapose hi
            simp only [Decidable.not_not]
            aesop
          · aesop
        simp_rw [this]
        simp only [Finset.sum_singleton, Finsupp.single_eq_same]
      positivity
    refine fun _ _ ↦ ⟨m, fun N hN ↦ ?_⟩
    rw [coeff_monomial]
    split
    · grind
    · aesop
  bdd := by
    let I := Classical.typeDecidableEq σ
    rw [IsRestricted_bdd, convergenceSet]
    have : {x | ∃ n_1, ‖(coeff n_1) ((MvPowerSeries.monomial n) a)‖ * |c| ^ range_sum n_1 = x} =
        {0, ‖a‖ * |c|^(range_sum n)} := by
      refine Set.ext ?_
      intro x
      constructor
      · intro hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        simp only [Set.mem_setOf_eq] at hx
        obtain ⟨n', hn'⟩ := hx
        rw [coeff_monomial] at hn'
        rcases eq_or_ne n' n with h | h
        · simp only [h, ↓reduceIte] at hn'
          right
          exact hn'.symm
        · simp only [h, ↓reduceIte, norm_zero, zero_mul] at hn'
          left
          exact hn'.symm
      · intro hx
        simp only [Set.mem_setOf_eq]
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with h | h
        · simp_rw [coeff_monomial]
          obtain ⟨n', hn'⟩ : ∃ a : σ →₀ ℕ, a ≠ n := exists_ne n
          use n'
          simp only [hn', ↓reduceIte, norm_zero, zero_mul]
          exact h.symm
        · use n
          simp only [coeff_monomial_same]
          exact h.symm
    simp_rw [this]
    simp only [bddAbove_insert, bddAbove_singleton]

lemma one {R : Type*} [NormedRing R] (c : ℝ) {σ : Type*} [Nonempty σ] :
    IsRestricted c (1 : MvPowerSeries σ R) := by
  exact monomial c 0 1

lemma C {R : Type*} [NormedRing R] (c : ℝ) {σ : Type*} [Nonempty σ] (a : R) :
    IsRestricted c (C (σ := σ) a) := by
  simpa [monomial_zero_eq_C_apply] using monomial c 0 a

-- I should be pulling these two things out (also see literally every other proof)
lemma add {R : Type*} [NormedRing R] (c : ℝ) {σ : Type*} [Nonempty σ]
    {f g : MvPowerSeries σ R} (hf : IsRestricted c f) (hg : IsRestricted c g) :
    IsRestricted c (f + g) where
  limit := by
    obtain ⟨hf1, hf2⟩ := hf
    obtain ⟨hg1, hg2⟩ := hg
    simp only [isRestricted_limit_iff, map_add, norm_mul, norm_pow, Real.norm_eq_abs] at ⊢ hf1 hg1
    intro ε hε
    obtain ⟨fN, hfN⟩ := hf1 (ε / 2) (by positivity)
    obtain ⟨gN, hgN⟩ := hg1 (ε / 2) (by positivity)
    simp only [abs_norm] at hfN hgN ⊢
    rcases le_total fN gN with h | h
    · refine ⟨gN, fun n hn ↦ ?_ ⟩
      calc _ ≤ ‖(coeff n) f‖ * |c| ^ (range_sum n) + ‖(coeff n) g‖ * |c| ^ (range_sum n) := by
              grw [norm_add_le, add_mul]
        _ < ε / 2 + ε / 2 := by
                have := Preorder.le_trans fN gN n h hn
                gcongr <;> aesop
        _ = ε := by ring
    · refine ⟨fN, fun n hn ↦ ?_ ⟩
      calc _ ≤ ‖(coeff n) f‖ * |c| ^ (range_sum n) + ‖(coeff n) g‖ * |c| ^ (range_sum n) := by
              grw [norm_add_le, add_mul]
        _ < ε / 2 + ε / 2 := by
                have := Preorder.le_trans gN fN n h hn
                gcongr <;> aesop
        _ = ε := by ring
  bdd := by
    obtain ⟨hf1, hf2⟩ := hf
    obtain ⟨hg1, hg2⟩ := hg
    simp_rw [IsRestricted_bdd, convergenceSet] at ⊢ hf2 hg2
    obtain ⟨A, hA⟩ := hf2
    obtain ⟨B, hB⟩ := hg2
    simp_rw [mem_upperBounds] at hA hB
    use A + B
    simp only [map_add]
    refine mem_upperBounds.mpr ?_
    simp only [Set.mem_setOf_eq, forall_exists_index, forall_apply_eq_imp_iff] at ⊢ hA hB
    intro n
    calc _ ≤ ‖(coeff n) f‖ * |c| ^ (range_sum n) + ‖(coeff n) g‖ * |c| ^ (range_sum n) := by
              grw [norm_add_le, add_mul]
         _ ≤ A + B := by
              exact add_le_add (hA n) (hB n)

lemma smul {R : Type*} [NormedRing R] (c : ℝ) {σ : Type*} [Nonempty σ]
    {f : MvPowerSeries σ R} (hf : IsRestricted c f) (r : R) : IsRestricted c (r • f) where
  limit := by
    if h : r = 0 then simpa [h] using (zero c).limit else
    obtain ⟨hf, _⟩ := hf
    simp_rw [isRestricted_limit_iff, norm_mul, norm_pow, Real.norm_eq_abs, abs_norm] at ⊢ hf
    intro ε _
    obtain ⟨n, hn⟩ := hf (ε / ‖r‖) (by positivity)
    refine ⟨n, fun N hN ↦ ?_⟩
    calc _ ≤ ‖r‖ * ‖(coeff N) f‖ * |c| ^ (range_sum N) :=
          mul_le_mul_of_nonneg (norm_mul_le _ _) (by simp) (by simp) (by simp)
        _ < ‖r‖ * (ε / ‖r‖) := by
          rw [mul_assoc]; aesop
        _ = ε := mul_div_cancel₀ _ (by aesop)
  bdd := by
    obtain ⟨_, hf⟩ := hf
    simp_rw [IsRestricted_bdd, convergenceSet] at ⊢ hf
    obtain ⟨A, hA⟩ := hf
    simp_rw [mem_upperBounds] at hA
    simp only [Set.mem_setOf_eq, forall_exists_index, forall_apply_eq_imp_iff] at hA
    use ‖r‖ * A
    simp only [map_smul, smul_eq_mul]
    refine mem_upperBounds.mpr ?_
    intro x hx
    simp only [Set.mem_setOf_eq] at hx
    obtain ⟨n, rfl⟩ := hx
    grw [norm_mul_le, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hA n) (by simp)

lemma nsmul {R : Type*} [NormedRing R] (c : ℝ) {σ : Type*} [Nonempty σ] (n : ℕ)
    (f : MvPowerSeries σ R) (hf : IsRestricted c f) : IsRestricted c (n • f) := by
  convert smul c hf (n : R)
  ext _ _
  simp_rw [map_smul, smul_eq_mul, map_nsmul, nsmul_eq_mul]

lemma zsmul {R : Type*} [NormedRing R] (c : ℝ) {σ : Type*} [Fintype σ] [Nonempty σ] (n : ℤ)
    (f : MvPowerSeries σ R) (hf : IsRestricted c f) : IsRestricted c (n • f) := by
  convert smul c hf (n : R)
  ext _ _
  simp_rw [map_smul, smul_eq_mul, map_zsmul, zsmul_eq_mul]

open IsUltrametricDist

lemma lt_ineq {σ : Type*} (n a b : σ →₀ ℕ) (h : 2 • n ≤ a + b) :
    n ≤ a ∨ n ≤ b := by
  let I := Classical.typeDecidableEq σ
  simp_rw [le_def, range_sum_add, range_sum_smul] at ⊢ h
  have (a b c : ℕ) (h : 2 * a ≤ b + c) : a ≤ b ∨ a ≤ c  := by
    grind
  exact this (range_sum n) (range_sum a) (range_sum b) h

lemma mul {R : Type*} [NormedRing R] [IsUltrametricDist R] (c : ℝ) {σ : Type*} [Fintype σ]
    [Nonempty σ] {f g : MvPowerSeries σ R} (hf : IsRestricted c f) (hg : IsRestricted c g) :
    IsRestricted c (f * g) where
  limit := by
    let I := Classical.typeDecidableEq σ
    obtain ⟨hf1, fBound1⟩ := hf
    obtain ⟨hg1, gBound1⟩ := hg
    obtain ⟨a, ha, fBound1⟩ := (bddAbove_iff_exists_ge 1).mp fBound1
    obtain ⟨b, hb, gBound1⟩ := (bddAbove_iff_exists_ge 1).mp gBound1
    simp only [convergenceSet, Set.mem_setOf_eq, forall_exists_index,
      forall_apply_eq_imp_iff] at fBound1 gBound1
    simp only [isRestricted_limit_iff, norm_mul, norm_pow, Real.norm_eq_abs, abs_norm,
      coeff_mul] at ⊢ hf1 hg1
    intro ε hε
    obtain ⟨Nf, fBound2⟩ := (hf1 (ε / (max a b))) (by positivity)
    obtain ⟨Ng, gBound2⟩ := (hg1 (ε / (max a b))) (by positivity)
    rcases le_total Nf Ng with h | h
    · refine ⟨2 • Ng, fun n hn ↦ ?_⟩
      obtain ⟨⟨fst, snd⟩, hi, ultrametric⟩ := exists_norm_finset_sum_le (M := R)
        (Finset.antidiagonal n) (fun a ↦ (coeff a.1) f * (coeff a.2) g)
      obtain ⟨rfl⟩ := by simpa using hi (⟨(0, n), by simp⟩)
      calc _ ≤ ‖(coeff fst) f * (coeff snd) g‖ * |c| ^ (range_sum (fst + snd)) := by bound
         _ ≤ ‖(coeff fst) f‖ * |c| ^ (range_sum fst) * (‖(coeff snd) g‖ * |c| ^ (range_sum snd)) := by
          grw [norm_mul_le, range_sum_add]; grind
      have : Ng ≤ fst ∨ Ng ≤ snd := lt_ineq Ng fst snd hn
      rcases this with this | this
      · calc _ < ε / max a b * b := by
              grw [gBound1 snd]
              gcongr
              exact fBound2 fst (Preorder.le_trans Nf Ng fst h this)
            _ ≤ ε := by
              rw [div_mul_comm, mul_le_iff_le_one_left ‹_›]
              bound
      · calc _ < a * (ε / max a b) := by
              grw [fBound1 fst]
              gcongr
              exact gBound2 snd this
            _ ≤ ε := by
              rw [mul_div_left_comm, mul_le_iff_le_one_right ‹_›]
              bound
    · refine ⟨2 • Nf, fun n hn ↦ ?_⟩
      obtain ⟨⟨fst, snd⟩, hi, ultrametric⟩ := exists_norm_finset_sum_le (M := R)
        (Finset.antidiagonal n) (fun a ↦ (coeff a.1) f * (coeff a.2) g)
      obtain ⟨rfl⟩ := by simpa using hi (⟨(0, n), by simp⟩)
      calc _ ≤ ‖(coeff fst) f * (coeff snd) g‖ * |c| ^ (range_sum (fst + snd)) := by bound
        _ ≤ ‖(coeff fst) f‖ * |c| ^ (range_sum fst) * (‖(coeff snd) g‖ * |c| ^ (range_sum snd)) := by
          grw [norm_mul_le, range_sum_add]; grind
      have : Nf ≤ fst ∨ Nf ≤ snd := lt_ineq Nf fst snd hn
      rcases this with this | this
      · calc _ < ε / max a b * b := by
              grw [gBound1 snd]
              gcongr
              exact fBound2 fst this
            _ ≤ ε := by
              rw [div_mul_comm, mul_le_iff_le_one_left ‹_›]
              bound
      · calc _ < a * (ε / max a b) := by
              grw [fBound1 fst]
              gcongr
              exact gBound2 snd (Preorder.le_trans Ng Nf snd h this)
            _ ≤ ε := by
              rw [mul_div_left_comm, mul_le_iff_le_one_right ‹_›]
              bound
  bdd := by
    obtain ⟨_, hf⟩ := hf
    obtain ⟨_, hg⟩ := hg
    simp [IsRestricted_bdd, convergenceSet] at ⊢ hf hg
    obtain ⟨a, ha⟩ := hf
    obtain ⟨b, hb⟩ := hg
    simp_rw [mem_upperBounds] at ha hb
    simp only [Set.mem_setOf_eq, forall_exists_index, forall_apply_eq_imp_iff] at ha hb
    use a * b
    refine mem_upperBounds.mpr ?_
    intro x hx
    simp only [Set.mem_setOf_eq] at hx
    obtain ⟨n, rfl⟩ := hx
    let I := Classical.typeDecidableEq σ
    simp_rw [coeff_mul]
    obtain ⟨⟨fst, snd⟩, hi, ultrametric⟩ := exists_norm_finset_sum_le (M := R)
      (Finset.antidiagonal n) (fun a ↦ (coeff a.1) f * (coeff a.2) g)
    obtain ⟨rfl⟩ := by simpa using hi (⟨(0, n), by simp⟩)
    calc _ ≤ ‖(coeff fst) f * (coeff snd) g‖ * |c| ^ (range_sum (fst + snd)) := by bound
       _ ≤ ‖(coeff fst) f‖ * |c| ^ (range_sum fst) * (‖(coeff snd) g‖ * |c| ^ (range_sum snd)) := by
        grw [norm_mul_le, range_sum_add]; grind
    refine mul_le_mul_of_nonneg (ha fst) (hb snd) (by positivity) ?_
    calc 0 ≤ ‖(coeff fst) g‖ * |c| ^ range_sum fst := by
          have h1 : 0 ≤ ‖(coeff fst) g‖ := by
            exact norm_nonneg ((coeff fst) g)
          have h2 : 0 ≤ |c| ^ range_sum fst := by
            simp only [abs_nonneg, pow_nonneg]
          exact Left.mul_nonneg h1 h2
         _ ≤ b := by
          exact hb fst

section Finite

def set_lt {σ : Type*} [Fintype σ] (n : σ →₀ ℕ) : Set (σ →₀ ℕ) :=
  {a : σ →₀ ℕ | a ≤ n}

lemma set_lt_isFinite {σ : Type*} [Fintype σ] (n : σ →₀ ℕ) : Finite (set_lt n) := by
  let I := Classical.typeDecidableEq σ
  simp only [set_lt, le_def, Set.coe_setOf]
  have : { a : σ →₀ ℕ // range_sum a ≤ range_sum n } =
      ⋃ i : Finset.range ((range_sum n) + 1), {a : σ →₀ ℕ | range_sum a = i} := by
    simp_rw [Set.coe_eq_subtype, Set.mem_iUnion, Set.mem_setOf_eq, Subtype.exists, Finset.mem_range,
      exists_prop, exists_eq_right', Nat.lt_add_one_iff]
  rw [this]
  have (i : Finset.range ((range_sum n) + 1)) : Finite {a : σ →₀ ℕ | range_sum a = i} := by
    simp only [Set.coe_setOf]
    have (a : σ →₀ ℕ) (t : ℕ) (h : range_sum a = t) : ∀ i, a i ≤ t := by
      intro i
      unfold range_sum at h
      rw [← h]
      rcases Decidable.em (i ∈ a.support) with H | H
      · have : ∑ i ∈ a.support, a i = a i +
            ∑ j ∈ ({n | n ∈ a.support ∧ n ≠ i} : (Finset σ)), a j := by
          have : ∑ n ∈ a.support, a n =
              ∑ n ∈ {i} ∪ ({n | n ∈ a.support ∧ n ≠ i} : (Finset σ)), a n := by
            have : {i} ∪ ({n | n ∈ a.support ∧ n ≠ i} : (Finset σ)) = a.support := by
              refine Finset.ext_iff.mpr ?_
              intro j
              constructor
              · aesop
              · intro hj
                rcases eq_or_ne j i with hjeq | hjneq
                · aesop
                · simp only [Finsupp.mem_support_iff, ne_eq, Finset.singleton_union,
                  Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and]
                  right
                  aesop
            rw [this]
          simp [this]
        simp [this]
      · aesop
    have incl : {a : σ →₀ ℕ | range_sum a = i} ⊆ {a : σ →₀ ℕ | ∀ x, a x ≤ i} := by
      exact fun ⦃a⦄ ↦ this a ↑i
    have incl_fin : Finite {a : σ →₀ ℕ | ∀ x, a x ≤ i} := by
      -- we show this injects into functions (σ → Fin (i + 1)); which is of finite cardinality
      let J : {a : σ →₀ ℕ | ∀ x, a x ≤ i} → (σ → Fin (i + 1)) :=
        fun b ↦ fun j ↦ ⟨b.1 j, Nat.lt_succ_of_le (b.2 j)⟩
      have inj : Function.Injective J := by
        exact injective_of_le_imp_le J fun {x y} a ↦ a -- no idea how this works...
      exact Finite.of_injective J inj
    exact Finite.Set.subset ({a : σ →₀ ℕ | ∀ x, a x ≤ i}) incl
  exact Set.finite_iUnion this

lemma set_lt_Nonempty {σ : Type*} [Fintype σ] (n : σ →₀ ℕ) : Nonempty (set_lt n) := by
  use n
  simp [set_lt]

open Finset in
lemma convergenceSet_BddAbove {R : Type*} [NormedRing R] (c : ℝ) {σ : Type*} [Fintype σ]
    [Nonempty σ] {f : MvPowerSeries σ R} (hf : IsRestricted_limit c f) :
    BddAbove (convergenceSet c f) := by
  simp_rw [isRestricted_limit_iff] at hf
  obtain ⟨N, hf⟩ := by simpa using (hf 1)
  rw [bddAbove_def, convergenceSet]
  use max 1 (max' (image (fun i ↦ ‖coeff i f‖ * |c| ^ (range_sum i))
    ((Set.Finite.toFinset (set_lt_isFinite N)))) (by simpa using set_lt_Nonempty N))
  simp only [Set.mem_setOf_eq, le_sup_iff, forall_exists_index, forall_apply_eq_imp_iff]
  intro i
  rcases le_total i N with h | h
  · right
    apply le_max'
    simp only [mem_image]
    exact ⟨i, by aesop, rfl⟩
  · left
    calc _ ≤ ‖(coeff i) f‖ * |c ^ (range_sum i)| := by bound
         _ ≤ 1 := by simpa using (hf i h).le

theorem IsRestricted_iff_isRestricted_limit {R : Type*} [NormedRing R] (c : ℝ) {σ : Type*} [Fintype σ]
    [Nonempty σ] {f : MvPowerSeries σ R} : (IsRestricted c f) ↔ (IsRestricted_limit c f) := by
  constructor
  · exact fun h ↦ h.1
  · exact fun h ↦ ⟨h, convergenceSet_BddAbove c h⟩

end Finite
