import Mathlib

namespace MvPowerSeries

open MvPowerSeries Filter
open scoped Topology

abbrev range_sum {σ : Type*} [Fintype σ] : (σ →₀ ℕ) → ℕ :=
  fun n ↦ ∑ i : σ, n i

lemma range_sum_add {σ : Type*} [Fintype σ] (a b : σ →₀ ℕ) :
    range_sum (a + b) = range_sum (a) + range_sum (b) := by
  exact Finset.sum_add_distrib

lemma range_sum_smul {σ : Type*} [Fintype σ] (a : σ →₀ ℕ) (n : ℕ) :
    range_sum (n • a) = n * range_sum a := by
  unfold range_sum
  simp only [Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]

instance {σ : Type*} [Fintype σ] : LE (σ →₀ ℕ) where le f g := (range_sum f) ≤ (range_sum g)

lemma le_def {σ : Type*} [Fintype σ] {f g : σ →₀ ℕ} : f ≤ g ↔ (range_sum f) ≤ (range_sum g) := .rfl

instance {σ : Type*} [Fintype σ] : LT (σ →₀ ℕ) where lt f g := (range_sum f) < (range_sum g)

lemma lt_def {σ : Type*} [Fintype σ] {f g : σ →₀ ℕ} : f < g ↔ (range_sum f) < (range_sum g) := .rfl

instance preorder {σ : Type*} [Fintype σ] : Preorder (σ →₀ ℕ) where
  le_refl _ := by
    rw [le_def]
  le_trans _ _ _ := by
    exact Nat.le_trans
  lt_iff_le_not_ge a b := by
    simp_rw [le_def, lt_def, not_le, iff_and_self]
    exact Nat.le_of_succ_le

def le_total {σ : Type*} [Fintype σ] (a b : σ →₀ ℕ) : a ≤ b ∨ b ≤ a := by
  simp_rw [le_def]
  exact Nat.le_total _ _

instance {σ : Type*} [Fintype σ] : IsDirected (σ →₀ ℕ) (fun (a b : (σ →₀ ℕ)) ↦ (a ≤ b)) where
  directed a b := by
    rcases le_total a b with h | h
    · use b
    · use a

-- For infinite variables, could add the condition that the max of the convergence set is bounded...
-- so vacously solves our problem 

def IsRestricted {R : Type*} [NormedRing R] (c : ℝ) {σ : Type*} [Fintype σ] [Nonempty σ]
    (f : MvPowerSeries σ R) :=
  Tendsto (fun (t : σ →₀ ℕ) ↦ (norm (coeff t f)) * c^(range_sum t)) atTop (𝓝 0)

namespace IsRestricted

lemma isRestricted_iff {R : Type*} [NormedRing R] (c : ℝ) {σ : Type*} [Fintype σ] [Nonempty σ]
    {f : MvPowerSeries σ R} : IsRestricted c f ↔ ∀ ε, 0 < ε → ∃ (N : σ →₀ ℕ),
    ∀ (n : σ →₀ ℕ), N ≤ n → ‖‖(coeff n) f‖ * c^(range_sum n)‖ < ε := by
  simp [IsRestricted, NormedAddCommGroup.tendsto_atTop]

lemma isRestricted_iff_abs {R : Type*} [NormedRing R] (c : ℝ) {σ : Type*} [Fintype σ] [Nonempty σ]
    (f : MvPowerSeries σ R) : IsRestricted c f ↔ IsRestricted |c| f := by
  simp [isRestricted_iff]

lemma zero {R : Type*} [NormedRing R] (c : ℝ) {σ : Type*} [Fintype σ] [Nonempty σ] :
    IsRestricted c (0 : MvPowerSeries σ R) := by
  simp [IsRestricted]

lemma monomial {R : Type*} [NormedRing R] (c : ℝ) {σ : Type*} [Fintype σ] [Nonempty σ] (n : σ →₀ ℕ)
    (a : R) : IsRestricted c (monomial n a) := by
  let I := Classical.typeDecidableEq σ
  simp_rw [isRestricted_iff, norm_mul, norm_pow, Real.norm_eq_abs, abs_norm, coeff_monomial]
  · obtain ⟨m, hm⟩ : ∃ m : σ →₀ ℕ, n < m := by
      use n + (Finsupp.equivFunOnFinite.symm (fun (i : σ) ↦ 1))
      simp_rw [lt_def, range_sum_add, lt_add_iff_pos_right, range_sum,
        Finsupp.equivFunOnFinite_symm_apply_toFun, Finset.sum_const, Finset.card_univ, smul_eq_mul,
        mul_one]
      exact Fintype.card_pos
    refine fun _ _ ↦ ⟨m, fun N hN ↦ ?_⟩
    split
    · grind
    · aesop

lemma one {R : Type*} [NormedRing R] (c : ℝ) {σ : Type*} [Fintype σ] [Nonempty σ] :
    IsRestricted c (1 : MvPowerSeries σ R) := by
  exact monomial c 0 1

lemma C {R : Type*} [NormedRing R] (c : ℝ) {σ : Type*} [Fintype σ] [Nonempty σ] (a : R) :
    IsRestricted c (C (σ := σ) a) := by
  simpa [monomial_zero_eq_C_apply] using monomial c 0 a

lemma add {R : Type*} [NormedRing R] (c : ℝ) {σ : Type*} [Fintype σ] [Nonempty σ]
    {f g : MvPowerSeries σ R} (hf : IsRestricted c f) (hg : IsRestricted c g) :
    IsRestricted c (f + g) := by
  simp only [isRestricted_iff, map_add, norm_mul, norm_pow, Real.norm_eq_abs] at ⊢ hf hg
  intro ε hε
  obtain ⟨fN, hfN⟩ := hf (ε / 2) (by positivity)
  obtain ⟨gN, hgN⟩ := hg (ε / 2) (by positivity)
  simp only [abs_norm] at hfN hgN ⊢
  -- at this point I want to be using max fN gN... but I have not defined it properly, could do this
  -- if prefered; this also causes a similar use of rcases in mul...
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

lemma smul {R : Type*} [NormedRing R] (c : ℝ) {σ : Type*} [Fintype σ] [Nonempty σ]
    {f : MvPowerSeries σ R} (hf : IsRestricted c f) (r : R) : IsRestricted c (r • f) := by
  if h : r = 0 then simpa [h] using zero c else
  simp_rw [isRestricted_iff, norm_mul, norm_pow, Real.norm_eq_abs, abs_norm] at ⊢ hf
  intro ε _
  obtain ⟨n, hn⟩ := hf (ε / ‖r‖) (by positivity)
  refine ⟨n, fun N hN ↦ ?_⟩
  calc _ ≤ ‖r‖ * ‖(coeff N) f‖ * |c| ^ (range_sum N) :=
        mul_le_mul_of_nonneg (norm_mul_le _ _) (by simp) (by simp) (by simp)
       _ < ‖r‖ * (ε / ‖r‖) := by
        rw [mul_assoc]; aesop
       _ = ε := mul_div_cancel₀ _ (by aesop)

lemma nsmul {R : Type*} [NormedRing R] (c : ℝ) {σ : Type*} [Fintype σ] [Nonempty σ] (n : ℕ)
    (f : MvPowerSeries σ R) (hf : IsRestricted c f) : IsRestricted c (n • f) := by
  convert IsRestricted.smul c hf (n : R)
  ext _ _
  simp_rw [map_smul, smul_eq_mul, map_nsmul, nsmul_eq_mul]

lemma zsmul {R : Type*} [NormedRing R] (c : ℝ) {σ : Type*} [Fintype σ] [Nonempty σ] (n : ℤ)
    (f : MvPowerSeries σ R) (hf : IsRestricted c f) : IsRestricted c (n • f) := by
  convert IsRestricted.smul c hf (n : R)
  ext _ _
  simp_rw [map_smul, smul_eq_mul, map_zsmul, zsmul_eq_mul]

/-- The set of `‖coeff n f‖ * c ^ (range_sum n)` for a given power series `f` and parameter `c`. -/
def convergenceSet {R : Type*} [NormedRing R] (c : ℝ) {σ : Type*} [Fintype σ] [Nonempty σ]
  (f : MvPowerSeries σ R) : Set ℝ := {‖(coeff n) f‖ * c^(range_sum n) | n : (σ →₀ ℕ)}

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
      have : ∑ n, a n = a i + ∑ n with n ≠ i, a n := by
        have : a i = ∑ i ∈ {i}, a i := by
          rfl
        rw [this]
        have h : {i} ∪ ({n | n ≠ i} : (Finset σ)) =
            Finset.univ := by
          ext j
          simpa using eq_or_ne j i
        have : ∑ n, a n = ∑ n ∈ {i} ∪ ({n | n ≠ i} : (Finset σ)), a n := by
          exact congrFun (congrArg Finset.sum (id (Eq.symm h))) fun n ↦ a n
        simp_rw [this]
        simp only [ne_eq, Finset.singleton_union, Finset.mem_filter, Finset.mem_univ,
          not_true_eq_false, and_false, not_false_eq_true, Finset.sum_insert, Finset.sum_singleton]
        -- has to be a better way to do this
      simp_rw [this]
      grind
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
    [Nonempty σ] {f : MvPowerSeries σ R} (hf : IsRestricted c f) :
    BddAbove (convergenceSet c f) := by
  simp_rw [isRestricted_iff] at hf
  obtain ⟨N, hf⟩ := by simpa using (hf 1)
  rw [bddAbove_def, convergenceSet]
  use max 1 (max' (image (fun i ↦ ‖coeff i f‖ * c ^ (range_sum i))
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

lemma lt_ineq {σ : Type*} [Fintype σ] (n a b : σ →₀ ℕ) (h : 2 • n ≤ a + b) :
    n ≤ a ∨ n ≤ b := by
  simp_rw [le_def, range_sum_add, range_sum_smul] at ⊢ h
  have (a b c : ℕ) (h : 2 * a ≤ b + c) : a ≤ b ∨ a ≤ c  := by
    grind
  exact this (∑ i, n i) (∑ i, a i) (∑ i, b i) h

open IsUltrametricDist

lemma mul {R : Type*} [NormedRing R] [IsUltrametricDist R] (c : ℝ) {σ : Type*} [Fintype σ]
    [Nonempty σ] {f g : MvPowerSeries σ R} (hf : IsRestricted c f) (hg : IsRestricted c g) :
    IsRestricted c (f * g) := by
  let I := Classical.typeDecidableEq σ
  obtain ⟨a, ha, fBound1⟩ := (bddAbove_iff_exists_ge 1).mp (convergenceSet_BddAbove _
    ((isRestricted_iff_abs c f).mp hf))
  obtain ⟨b, hb, gBound1⟩ := (bddAbove_iff_exists_ge 1).mp (convergenceSet_BddAbove _
    ((isRestricted_iff_abs c g).mp hg))
  simp only [convergenceSet, Set.mem_setOf_eq, forall_exists_index, forall_apply_eq_imp_iff]
    at fBound1 gBound1
  simp only [isRestricted_iff, norm_mul, norm_pow, Real.norm_eq_abs, abs_norm, coeff_mul] at ⊢ hf hg
  intro ε hε
  obtain ⟨Nf, fBound2⟩ := (hf (ε / (max a b))) (by positivity)
  obtain ⟨Ng, gBound2⟩ := (hg (ε / (max a b))) (by positivity)
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
  · refine ⟨(Finsupp.equivFunOnFinite.symm (fun (i : σ) ↦ 2 * Nf i)), fun n hn ↦ ?_⟩
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
  -- can probably clean this proof up if I bother to include max; as opposed to breaking into two
  -- steps

end IsRestricted
end MvPowerSeries



/-
-- not sure if this definition works as we use this instance of <
-- instance instLE : LE (ι →₀ M) where le f g := ∀ i, f i ≤ g i
-- which is not the correct definition.

-- so I need to define a new ordering of f ≤ g when range_sum f ≤ range_sum g

-- the nonempty is required as the definition does not work for σ = ∅... it would give it to be {0}.
-- and fintype is required for the sum
def IsRestricted {R : Type*} [NormedRing R] (c : ℝ) {σ : Type*} [Fintype σ] [Nonempty σ]
    (f : MvPowerSeries σ R) :=
  Tendsto (fun (t : σ →₀ ℕ) ↦ (norm (coeff t f)) * c^(∑ i : σ, t i)) atTop (𝓝 0)

namespace IsRestricted

lemma isRestricted_iff {R : Type*} [NormedRing R] (c : ℝ) {σ : Type*} [Fintype σ] [Nonempty σ]
    {f : MvPowerSeries σ R} : IsRestricted c f ↔ ∀ ε, 0 < ε → ∃ (N : σ →₀ ℕ),
    ∀ (n : σ →₀ ℕ), N ≤ n → ‖‖(coeff n) f‖ * c^(∑ i : σ, n i)‖ < ε := by
  simp [IsRestricted, NormedAddCommGroup.tendsto_atTop]

lemma isRestricted_iff_abs {R : Type*} [NormedRing R] (c : ℝ) {σ : Type*} [Fintype σ] [Nonempty σ]
    (f : MvPowerSeries σ R) : IsRestricted c f ↔ IsRestricted |c| f := by
  simp [isRestricted_iff]

lemma zero {R : Type*} [NormedRing R] (c : ℝ) {σ : Type*} [Fintype σ] [Nonempty σ] :
    IsRestricted c (0 : MvPowerSeries σ R) := by
  simp [IsRestricted]

lemma monomial {R : Type*} [NormedRing R] (c : ℝ) {σ : Type*} [Fintype σ] [Nonempty σ] (n : σ →₀ ℕ)
    (a : R) : IsRestricted c (monomial n a) := by
  let I := Classical.typeDecidableEq σ
  simp_rw [isRestricted_iff, norm_mul, norm_pow, Real.norm_eq_abs, abs_norm, coeff_monomial]
  · obtain ⟨m, hm⟩ : ∃ m : σ →₀ ℕ, n < m := by
      use n + (Finsupp.equivFunOnFinite.symm (fun (i : σ) ↦ 1))
      simp only [lt_add_iff_pos_right]
      refine Finsupp.lt_def.mpr ?_
      exact ⟨zero_le (Finsupp.equivFunOnFinite.symm fun i ↦ 1), by simp?⟩
    refine fun _ _ ↦ ⟨m, fun N hN ↦ ?_⟩
    split
    · grind
    · aesop

lemma one {R : Type*} [NormedRing R] (c : ℝ) {σ : Type*} [Fintype σ] [Nonempty σ] :
    IsRestricted c (1 : MvPowerSeries σ R) := by
  exact monomial c 0 1

lemma C {R : Type*} [NormedRing R] (c : ℝ) {σ : Type*} [Fintype σ] [Nonempty σ] (a : R) :
    IsRestricted c (C (σ := σ) a) := by
  simpa [monomial_zero_eq_C_apply] using monomial c 0 a

lemma add {R : Type*} [NormedRing R] (c : ℝ) {σ : Type*} [Fintype σ] [Nonempty σ]
    {f g : MvPowerSeries σ R} (hf : IsRestricted c f) (hg : IsRestricted c g) :
    IsRestricted c (f + g) := by
  simp only [isRestricted_iff, map_add, norm_mul, norm_pow, Real.norm_eq_abs] at ⊢ hf hg
  intro ε hε
  obtain ⟨fN, hfN⟩ := hf (ε / 2) (by positivity)
  obtain ⟨gN, hgN⟩ := hg (ε / 2) (by positivity)
  simp only [abs_norm] at hfN hgN ⊢
  refine ⟨max fN gN, fun n hn ↦ ?_ ⟩
  calc _ ≤ ‖(coeff n) f‖ * |c| ^ (∑ i, n i) + ‖(coeff n) g‖ * |c| ^ (∑ i, n i) := by
            grw [norm_add_le, add_mul]
       _ < ε / 2 + ε / 2 := by gcongr <;> aesop
       _ = ε := by ring

lemma neg {R : Type*} [NormedRing R] (c : ℝ) {σ : Type*} [Fintype σ] [Nonempty σ]
    {f : MvPowerSeries σ R} (hf : IsRestricted c f) : IsRestricted c (-f) := by
  simpa [isRestricted_iff] using hf

-- the ordering seems wrong... need to change this

lemma smul {R : Type*} [NormedRing R] (c : ℝ) {σ : Type*} [Fintype σ] [Nonempty σ]
    {f : MvPowerSeries σ R} (hf : IsRestricted c f) (r : R) : IsRestricted c (r • f) := by
  if h : r = 0 then simpa [h] using zero c else
  simp_rw [isRestricted_iff, norm_mul, norm_pow, Real.norm_eq_abs, abs_norm] at ⊢ hf
  intro ε _
  obtain ⟨n, hn⟩ := hf (ε / ‖r‖) (by positivity)
  refine ⟨n, fun N hN ↦ ?_⟩
  calc _ ≤ ‖r‖ * ‖(coeff N) f‖ * |c| ^ (∑ i, n i) :=
        mul_le_mul_of_nonneg (norm_mul_le _ _) (by sorry) (by simp) (by simp)
       _ < ‖r‖ * (ε / ‖r‖) := by
        rw [mul_assoc]; sorry
       _ = ε := mul_div_cancel₀ _ (by aesop)

-/
