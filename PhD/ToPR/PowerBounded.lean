-- This is an adaption of Chris' Power bounded file in the Adic-spaces repo

import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Int.Star
import Mathlib.Topology.Algebra.InfiniteSum.Group
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Algebra.Nonarchimedean.Basic
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Algebra.TopologicallyNilpotent

open Filter Topology Pointwise Polynomial

namespace TopologicalRing

/-! ### Bounded subsets -/

variable {A : Type*} [MonoidWithZero A] [TopologicalSpace A]

-- First note: I changed the order of V * S
-- I have always tried generalising Ring down to its minimal assumption
-- This seems to be MonoidWithZero
-- Then extensions to Semiring or Ring or CommRing when required

/-- A subset is bounded if for every nhd `U` of `0`, some nhd `V` satisfies `V * S ⊆ U`. -/
def IsBounded (S : Set A) : Prop :=
  ∀ U ∈ 𝓝 (0 : A), ∃ V ∈ 𝓝 (0 : A), V * S ⊆ U

/-- Subsets of bounded sets are bounded. -/
theorem IsBounded.subset {S T : Set A} (hS : IsBounded S) (hTS : T ⊆ S) : IsBounded T :=
  fun U hU ↦ let ⟨V, hV, hSV⟩ := hS U hU
  ⟨V, hV, (Set.mul_subset_mul_left hTS).trans hSV⟩

/-- The empty set is bounded. -/
theorem isBounded_empty : IsBounded (∅ : Set A) :=
  fun U _ ↦ ⟨Set.univ, univ_mem, by simp⟩

/-- The singleton `{0}` is bounded. -/
theorem isBounded_singleton_zero : IsBounded ({0} : Set A) :=
  fun U hU ↦ ⟨Set.univ, univ_mem, fun x hx ↦ by simp_all [mem_of_mem_nhds hU]⟩

/-- The pair `{0, 1}` is bounded. -/
theorem isBounded_pair_zero_one : IsBounded ({0, 1} : Set A) :=
  fun U hU ↦ ⟨U, hU, fun _ hx ↦ by
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hx
    rcases Set.mem_insert_iff.mp hb with rfl | ha
    · rw [mul_zero]; exact mem_of_mem_nhds hU
    · rwa [Set.mem_singleton_iff.mp ha, mul_one]⟩

/-- Union of two bounded sets is bounded (Remark 5.28(3)). -/
theorem IsBounded.union {S T : Set A} (hS : IsBounded S) (hT : IsBounded T) :
    IsBounded (S ∪ T) := by
  intro U hU
  obtain ⟨V₁, hV₁, hSV⟩ := hS U hU; obtain ⟨V₂, hV₂, hTV⟩ := hT U hU
  refine ⟨V₁ ∩ V₂, inter_mem hV₁ hV₂, ?_⟩
  rw [Set.mul_union]
  refine Set.union_subset ?_ ?_
  · exact (Set.mul_subset_mul_right Set.inter_subset_left).trans hSV
  · exact (Set.mul_subset_mul_right Set.inter_subset_right).trans hTV

/-- Product of two bounded sets is bounded. -/
theorem IsBounded.mul {S T : Set A}
    (hS : IsBounded S) (hT : IsBounded T) : IsBounded (S * T) := by
  intro U hU
  obtain ⟨W, hW, hTW⟩ := hT U hU
  obtain ⟨V, hV, hSV⟩ := hS W hW
  exact ⟨V, hV, by simpa [← mul_assoc] using (Set.mul_subset_mul_right hSV).trans hTW⟩

-- we now need

/-- Every singleton is bounded (Remark 5.28(1)). -/
theorem isBounded_singleton {A : Type*} [Semiring A] [TopologicalSpace A]
    [IsTopologicalSemiring A] (a : A) : IsBounded ({a} : Set A) :=
  fun U hU ↦ ⟨(· * a) ⁻¹' U, (continuous_id.mul continuous_const).continuousAt.preimage_mem_nhds
    (by simp [hU]), by simp⟩

/-- Every finite subset is bounded (Remark 5.28(1)). -/
theorem isBounded_finite {A : Type*} [Semiring A] [TopologicalSpace A]
    [IsTopologicalSemiring A] {S : Set A} (hS : S.Finite) :
    IsBounded S := by
  refine @Set.Finite.induction_on A (fun s _ ↦ IsBounded s) S hS ?_ ?_
  · exact isBounded_empty
  · intro a s _ _ ih; exact Set.insert_eq a s ▸ (isBounded_singleton a).union ih

/-! ### Power-bounded elements -/

/-- An element is power-bounded if `{aⁿ | n}` is bounded (Definition 5.27). -/
def IsPowerBounded (a : A) : Prop :=
  IsBounded (Set.range (a ^ · : ℕ → A))

/-- The set `A°` of all power-bounded elements. -/
def powerBoundedSubring (A : Type*) [MonoidWithZero A] [TopologicalSpace A] : Set A :=
  {a : A | IsPowerBounded a}

/-- `0` is power-bounded. -/
theorem isPowerBounded_zero : IsPowerBounded (0 : A) := by
  simp [IsPowerBounded]
  apply isBounded_pair_zero_one.subset
  rintro _ ⟨n, rfl⟩
  rcases n with _ | n <;> simp [zero_pow]

/-- `1` is power-bounded. -/
theorem isPowerBounded_one : IsPowerBounded (1 : A) := by
  apply isBounded_pair_zero_one.subset
  rintro _ ⟨n, rfl⟩
  simp

/-- `-a` is power-bounded if `a` is (Prop 5.30(3)). -/
theorem isPowerBounded_neg {A : Type*} [Ring A] [TopologicalSpace A]
    [IsTopologicalSemiring A] {a : A} (ha : IsPowerBounded a) :
    IsPowerBounded (-a) := by
  apply (((isBounded_singleton (-1)).union (isBounded_singleton 1)).mul ha).subset
  rintro _ ⟨n, rfl⟩; change (-a) ^ n ∈ _; rw [neg_pow]
  exact Set.mul_mem_mul (by rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩ <;>
    simp [hk, pow_succ]) ⟨n, rfl⟩

/-- `a * b` is power-bounded if `a` and `b` are (Prop 5.30(3)). -/
theorem isPowerBounded_mul {A : Type*} [CommSemiring A] [TopologicalSpace A] {a b : A}
    (ha : IsPowerBounded a) (hb : IsPowerBounded b) : IsPowerBounded (a * b) := by
  apply (ha.mul hb).subset
  rintro _ ⟨n, rfl⟩
  simp only [mul_pow]
  exact Set.mul_mem_mul ⟨n, rfl⟩ ⟨n, rfl⟩

/-- Sum of two power-bounded elements is power-bounded in a nonarchimedean ring (Prop 5.30(3)). -/
theorem isPowerBounded_add {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [IsLinearTopology A A] {a b : A} (ha : IsPowerBounded a) (hb : IsPowerBounded b) :
    IsPowerBounded (a + b) := by
  intro U hU
  obtain ⟨J, hJ, hJU⟩ := (IsLinearTopology.hasBasis_open_ideal (R := A)).mem_iff.mp hU
  obtain ⟨V, hV, hSV⟩ := (ha.mul hb) (J : Set A) (hJ.mem_nhds J.zero_mem)
  refine ⟨V, hV, ?_⟩
  rintro _ ⟨v, hv, _, ⟨n, rfl⟩, rfl⟩
  apply hJU
  change v * (a + b) ^ n ∈ _
  rw [add_pow, Finset.mul_sum]
  refine Submodule.sum_mem J fun m _ ↦ ?_
  rw [show v * (a ^ m * b ^ (n - m) * ↑(n.choose m)) =
      ↑(n.choose m) * (v * (a ^ m * b ^ (n - m))) by ring]
  exact Ideal.mul_mem_left J _
    (hSV (Set.mul_mem_mul hv (Set.mul_mem_mul ⟨m, rfl⟩ ⟨n - m, rfl⟩)))

/-- `A°` is a subring in a nonarchimedean topological ring (Prop 5.30(3)). -/
def powerBoundedSubring.toSubring (A : Type*) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsLinearTopology A A] : Subring A where
  carrier := powerBoundedSubring A
  mul_mem' := isPowerBounded_mul
  one_mem' := isPowerBounded_one
  add_mem' := isPowerBounded_add
  zero_mem' := isPowerBounded_zero
  neg_mem' := isPowerBounded_neg

/-! ### Topologically nilpotent elements -/

variable (A) in
/-- The set `A°°` of all topologically nilpotent elements (Definition 5.25). -/
def topologicallyNilpotentElements : Set A :=
  {a : A | IsTopologicallyNilpotent a}

/-- Topologically nilpotent implies power-bounded (Remark 5.28(4)). -/
theorem IsTopologicallyNilpotent.isPowerBounded {A : Type*} [Semiring A] [TopologicalSpace A]
    [IsTopologicalSemiring A] {a : A}
    (ha : IsTopologicallyNilpotent a) : IsPowerBounded a := by
  intro U hU
  have hmul : (fun p : A × A ↦ p.1 * p.2) ⁻¹' U ∈ 𝓝 ((0 : A), (0 : A)) :=
    continuous_mul.continuousAt.preimage_mem_nhds (by simp [hU])
  rw [nhds_prod_eq] at hmul
  obtain ⟨U₁, hU₁, U₂, hU₂, hprod⟩ := Filter.mem_prod_iff.mp hmul
  obtain ⟨N, hN⟩ := (ha.eventually hU₂).exists_forall_of_atTop
  have hfin (i : Fin N) : ∃ V ∈ 𝓝 (0 : A), V * {a ^ (i : ℕ)} ⊆ U :=
    isBounded_singleton (a ^ (i : ℕ)) U hU
  choose V hV_mem hV_sub using hfin
  refine ⟨U₁ ∩ ⋂ i, V i, inter_mem hU₁ (Filter.iInter_mem.mpr hV_mem), ?_⟩
  intro x hx
  obtain ⟨c, hc, _, ⟨n, rfl⟩, rfl⟩ := Set.mem_mul.mp hx
  by_cases hn : n < N
  · exact hV_sub ⟨n, hn⟩
      (Set.mem_mul.mpr ⟨c, Set.mem_iInter.mp hc.2 ⟨n, hn⟩, a ^ n, rfl, rfl⟩)
  · exact hprod (Set.mk_mem_prod hc.1 (hN n (by omega)))

/-- `A°°` is contained in `A°` (Remark 5.28(4)). -/
theorem topologicallyNilpotentElements_subset_powerBoundedSubring {A : Type*} [Semiring A]
    [TopologicalSpace A] [IsTopologicalSemiring A] :
    topologicallyNilpotentElements A ⊆ powerBoundedSubring A :=
  fun _ ↦ IsTopologicallyNilpotent.isPowerBounded

-- since we want it to be an ideal and we need the Comm condition for mul_pow
-- we write it such that it is a left ideal!

/-- Product of power-bounded and topologically nilpotent is topologically nilpotent. -/
theorem IsPowerBounded.isTopologicallyNilpotent_mul {A : Type*} [CommSemiring A]
    [TopologicalSpace A] [IsTopologicalSemiring A] {a b : A}
    (ha : IsPowerBounded a) (hb : IsTopologicallyNilpotent b) :
    IsTopologicallyNilpotent (a * b) := by
  intro U hU
  obtain ⟨V, hV, hSV⟩ := ha U hU
  rw [Filter.mem_map, mul_comm]
  refine Filter.mem_of_superset (Filter.mem_map.mp (hb hV)) ?_
  simpa [mul_pow] using fun n hn ↦ (hSV (Set.mul_mem_mul hn ⟨n, rfl⟩))

/-- `A°°` is radical: `a ^ m ∈ A°°` implies `a ∈ A°°` (Prop 5.30(4)). -/
theorem IsTopologicallyNilpotent.of_pow {A : Type*} [Semiring A]
    [TopologicalSpace A] [IsTopologicalSemiring A] {a : A} {m : ℕ} (hm : 0 < m)
    (ha : IsTopologicallyNilpotent (a ^ m)) : IsTopologicallyNilpotent a := by
  intro U hU
  obtain ⟨V, hV, hSV⟩ := (isBounded_finite (Set.finite_range fun i : Fin m ↦ a ^ (i : ℕ))) U hU
  obtain ⟨N, hN⟩ := Filter.mem_atTop_sets.mp (ha hV)
  refine Filter.mem_atTop_sets.mpr ⟨m * N, fun n hn ↦ ?_⟩
  rw [Set.mem_preimage, show a ^ n = (a ^ m) ^ (n / m) * a ^ (n % m) by
    rw [← pow_mul, ← pow_add, add_comm, Nat.mod_add_div]]
  exact hSV (Set.mul_mem_mul (hN _ ((Nat.le_div_iff_mul_le hm).mpr (by linarith)))
    ⟨⟨n % m, Nat.mod_lt n hm⟩, rfl⟩)

-- the proofs seem like bit of a mess, but perhaps it is okay?

/-- `A°°` is an ideal of `A°`. -/
def IsTopologicallyNilpotent_ideal (A : Type*) [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A] :
    Ideal ↥(TopologicalRing.powerBoundedSubring.toSubring A) where
  carrier :=
    Set.range (Set.inclusion topologicallyNilpotentElements_subset_powerBoundedSubring)
  add_mem' := by
    simp only [Set.mem_range, Subtype.exists, Set.inclusion_mk, forall_exists_index, Subtype.forall,
      Subtype.mk.injEq, AddMemClass.mk_add_mk, exists_prop, exists_eq_right]
    intro _ _ _ _ _ hx rfl _ hy rfl
    simp_rw [topologicallyNilpotentElements, Set.mem_setOf_eq] at ⊢ hx hy
    exact IsTopologicallyNilpotent.add hx hy
  zero_mem' := by simpa using IsTopologicallyNilpotent.zero
  smul_mem' := by
    simp only [Set.mem_range, Subtype.exists, Set.inclusion_mk, smul_eq_mul, forall_exists_index,
      Subtype.forall, Subtype.mk.injEq, MulMemClass.mk_mul_mk, exists_prop, exists_eq_right]
    intro _ hb _ _ _ hx rfl
    simp_rw [topologicallyNilpotentElements, Set.mem_setOf_eq] at ⊢ hx
    exact IsPowerBounded.isTopologicallyNilpotent_mul hb hx

-- how to write the tilde in the superscript?? plus need to actually move everything on top...

/-- The quotient `A~ := A° ⧸ A°°`. -/
def IsPowerBounded.residueField {A : Type*} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A] :=
  ↥(TopologicalRing.powerBoundedSubring.toSubring A) ⧸ (IsTopologicallyNilpotent_ideal A)

-- If `A` is complete, each element of the form `e = 1 - y` for `y` topologically nilpotent is a
-- unit.
-- Prop 1.2.4.4 of BGR
-- proof done by Claude using my pdf blueprint (i.e. proof of concept that it works)
-- going to spend the rest of the time cleaning everything up and setting up the statements such that
-- it matches the wanted lean code.
lemma foo_isUnit {A : Type*} [Ring A] [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A]
    [IsLinearTopology A A] [CompleteSpace A] [T2Space A] (e : A) (y : A)
    (hy : y ∈ topologicallyNilpotentElements A) (he : e = 1 - y) :
    IsUnit e := by
  change IsTopologicallyNilpotent y at hy
  -- The series `∑ y ^ n` is summable: for any open ideal `J`, eventually `y ^ n ∈ J`, so the
  -- partial sums over finite sets disjoint from `Finset.range N` lie in `J`.
  have hsum : Summable (fun n : ℕ => y ^ n) := by
    rw [summable_iff_cauchySeq_finset, cauchySeq_finset_iff_sum_vanishing]
    intro U hU
    obtain ⟨J, hJ, hJU⟩ := (IsLinearTopology.hasBasis_open_ideal (R := A)).mem_iff.mp hU
    obtain ⟨N, hN⟩ : ∃ N, ∀ n ≥ N, y ^ n ∈ J :=
      Filter.eventually_atTop.mp (hy.eventually_mem (hJ.mem_nhds J.zero_mem))
    refine ⟨Finset.range N, fun t ht => hJU (J.sum_mem fun k hk => hN k ?_)⟩
    exact Nat.le_of_not_lt fun h => Finset.disjoint_left.mp ht hk (Finset.mem_range.mpr h)
  -- The inverse is `∑' n, y ^ n`, via the geometric series identities.
  rw [he]
  exact ⟨⟨1 - y, ∑' n, y ^ n, hsum.one_sub_mul_tsum_pow, hsum.tsum_pow_mul_one_sub⟩, rfl⟩

/-- Membership in the topologically nilpotent ideal is the same as being topologically
nilpotent in the ambient ring. -/
-- This should be true by definition... but maybe I need to fix the typing
lemma mem_IsTopologicallyNilpotent_ideal_iff {A : Type*} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsLinearTopology A A] (x : ↥(powerBoundedSubring.toSubring A)) :
    x ∈ IsTopologicallyNilpotent_ideal A ↔ IsTopologicallyNilpotent (x : A) := by
  constructor
  · rintro ⟨⟨z, hz⟩, heq⟩
    have hxz : (x : A) = z := by rw [← heq]
    rwa [hxz]
  · intro hx
    exact ⟨⟨(x : A), hx⟩, rfl⟩

/-- For `y` topologically nilpotent, the geometric series `∑' n, y ^ n` is power-bounded;
this is the inverse of `1 - y` from `foo_isUnit`. -/
-- This maybe is stupid?... as we can show it is nilpotent instead
-- this should probably be a statement after foo_isUnit
-- which says that z = ∑_1^∞ y^n is nilpotent since it is a closed ideal!

-- tl;dr need to change this to topologically nilpotent and used closed ideal!
lemma isPowerBounded_tsum_pow {A : Type*} [CommRing A] [UniformSpace A] [IsUniformAddGroup A]
    [CompleteSpace A] [IsTopologicalRing A] [IsLinearTopology A A] [T2Space A]
    {y : A} (hy : IsTopologicallyNilpotent y) :
    IsPowerBounded (∑' n : ℕ, y ^ n) := by
  have hsum : Summable (fun n : ℕ => y ^ n) := by
    rw [summable_iff_cauchySeq_finset, cauchySeq_finset_iff_sum_vanishing]
    intro U hU
    obtain ⟨J, hJ, hJU⟩ := (IsLinearTopology.hasBasis_open_ideal (R := A)).mem_iff.mp hU
    obtain ⟨N, hN⟩ : ∃ N, ∀ n ≥ N, y ^ n ∈ J :=
      Filter.eventually_atTop.mp (hy.eventually_mem (hJ.mem_nhds J.zero_mem))
    refine ⟨Finset.range N, fun t ht => hJU (J.sum_mem fun k hk => hN k ?_)⟩
    exact Nat.le_of_not_lt fun h => Finset.disjoint_left.mp ht hk (Finset.mem_range.mpr h)
  set c := ∑' n : ℕ, y ^ n with hc_def
  have h_inv : (1 - y) * c = 1 := hsum.one_sub_mul_tsum_pow
  have hcminus1 : c - 1 = y * c := by
    rw [sub_eq_iff_eq_add, ← h_inv]; ring
  have h_cm1_tn : IsTopologicallyNilpotent (c - 1) := by
    show Filter.Tendsto ((c - 1) ^ ·) Filter.atTop (𝓝 0)
    rw [(IsLinearTopology.hasBasis_open_ideal (R := A)).tendsto_right_iff]
    intro J hJ
    filter_upwards [hy.eventually_mem (hJ.mem_nhds J.zero_mem)] with m hm
    rw [hcminus1, mul_pow]
    exact J.mul_mem_right _ hm
  have hc_eq : c = 1 + (c - 1) := by ring
  rw [hc_eq]
  exact isPowerBounded_add isPowerBounded_one
    (IsTopologicallyNilpotent.isPowerBounded h_cm1_tn)

-- If `A` is complete. Then an element `a ∈ A°` is a unit iff its residue class `a~ ∈ A~` is a unit
-- Prop 1.2.5.8 of BGR
lemma bar_isUnit {A : Type*} [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [CompleteSpace A]
    [IsTopologicalRing A] [IsLinearTopology A A] [T2Space A]
    (a : ↥(TopologicalRing.powerBoundedSubring.toSubring A)) :
    IsUnit a ↔ IsUnit (Ideal.Quotient.mk (IsTopologicallyNilpotent_ideal A) a) := by
  refine ⟨fun ha ↦ ha.map _, fun h ↦ ?_⟩
  obtain ⟨b', hb'⟩ := isUnit_iff_exists_inv.mp h
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b'
  have h_ab_mk : Ideal.Quotient.mk (IsTopologicallyNilpotent_ideal A) (a * b) = 1 := by
    rw [map_mul]; exact hb'
  have h_diff_in : (a * b - 1) ∈ IsTopologicallyNilpotent_ideal A := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one, h_ab_mk, sub_self]
  have h_diff_tn : IsTopologicallyNilpotent ((a : A) * (b : A) - 1) := by
    have h := (mem_IsTopologicallyNilpotent_ideal_iff (a * b - 1)).mp h_diff_in
    have heq : ((a * b - 1 : ↥(powerBoundedSubring.toSubring A)) : A) =
        (a : A) * (b : A) - 1 := by push_cast; ring
    rwa [heq] at h
  have h_y_tn : IsTopologicallyNilpotent (1 - (a : A) * (b : A)) := by
    have h := IsTopologicallyNilpotent.mul_left (-1 : A) h_diff_tn
    have : (-1 : A) * ((a : A) * (b : A) - 1) = 1 - (a : A) * (b : A) := by ring
    rwa [this] at h
  have hc_pb : IsPowerBounded (∑' n : ℕ, (1 - (a : A) * (b : A)) ^ n) :=
    isPowerBounded_tsum_pow h_y_tn
  have hsum : Summable (fun n : ℕ => (1 - (a : A) * (b : A)) ^ n) := by
    rw [summable_iff_cauchySeq_finset, cauchySeq_finset_iff_sum_vanishing]
    intro U hU
    obtain ⟨J, hJ, hJU⟩ := (IsLinearTopology.hasBasis_open_ideal (R := A)).mem_iff.mp hU
    obtain ⟨N, hN⟩ : ∃ N, ∀ n ≥ N, (1 - (a : A) * (b : A)) ^ n ∈ J :=
      Filter.eventually_atTop.mp (h_y_tn.eventually_mem (hJ.mem_nhds J.zero_mem))
    refine ⟨Finset.range N, fun t ht => hJU (J.sum_mem fun k hk => hN k ?_)⟩
    exact Nat.le_of_not_lt fun h => Finset.disjoint_left.mp ht hk (Finset.mem_range.mpr h)
  have h_eq_one : (a : A) * (b : A) * (∑' n, (1 - (a : A) * (b : A)) ^ n) = 1 := by
    have h := hsum.one_sub_mul_tsum_pow
    rwa [show 1 - (1 - (a : A) * (b : A)) = (a : A) * (b : A) by ring] at h
  let c' : ↥(powerBoundedSubring.toSubring A) :=
    ⟨∑' n, (1 - (a : A) * (b : A)) ^ n, hc_pb⟩
  have h_a_mul : a * (b * c') = 1 := by
    apply Subtype.ext
    show (a : A) * ((b : A) * (c' : A)) = (1 : A)
    rw [← mul_assoc]
    exact h_eq_one
  exact IsUnit.of_mul_eq_one (b * c') h_a_mul

-- this may be enough for what I need

-- modulo the complete space lemmas (specifically BGR 1.2.5.3 and 1.4.1.3)

-- with this I now want to be able to state 1.4.2.3

-- remarks from this:
-- we will need Lemmas saying that restricted power series are: a uniform space; T2 (Hausdorff);
-- complete (w.r.t topology - which is a missing lemma); has the linear topology.

/-! ### Lemma 4.17: If `A` is complete, so is `A°` -/

/-- In a normed ring, an element of norm `< 1` is topologically nilpotent. -/
lemma _root_.IsTopologicallyNilpotent.of_norm_lt_one {A : Type*} [NormedRing A]
    {x : A} (hx : ‖x‖ < 1) : IsTopologicallyNilpotent x := by
  show Filter.Tendsto (x ^ ·) Filter.atTop (𝓝 0)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hf : ∀ n, 0 ≤ ‖x ^ n‖ := fun _ => norm_nonneg _
  have hft : ∀ᶠ n in Filter.atTop, ‖x ^ n‖ ≤ ‖x‖ ^ n :=
    Filter.eventually_atTop.mpr ⟨1, fun n hn => by
      induction n, hn using Nat.le_induction with
      | base => simp
      | succ k _ ih =>
        rw [pow_succ, pow_succ]
        exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right ih (norm_nonneg _))⟩
  exact squeeze_zero' (Filter.Eventually.of_forall hf) hft
    (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg x) hx)

/-- In a normed ring, every element of norm `< 1` is power-bounded. -/
lemma isPowerBounded_of_norm_lt_one {A : Type*} [NormedRing A] [IsTopologicalSemiring A]
    {x : A} (hx : ‖x‖ < 1) : IsPowerBounded x :=
  IsTopologicallyNilpotent.isPowerBounded (IsTopologicallyNilpotent.of_norm_lt_one hx)

/-- In a normed ring with multiplicative norm (`NormMulClass`), being topologically nilpotent
is the same as having norm strictly less than `1`. -/
lemma _root_.IsTopologicallyNilpotent.iff_norm_lt_one_of_normMulClass {A : Type*}
    [NormedRing A] [NormMulClass A] {x : A} :
    IsTopologicallyNilpotent x ↔ ‖x‖ < 1 := by
  refine ⟨fun hx => ?_, IsTopologicallyNilpotent.of_norm_lt_one⟩
  -- `x^n → 0`, hence `‖x^n‖ → 0`.
  have h_xn_tendsto : Filter.Tendsto (fun n : ℕ => ‖x ^ n‖) Filter.atTop (𝓝 0) := by
    have h := hx
    show Filter.Tendsto (fun n => ‖x ^ n‖) _ _
    rw [← tendsto_zero_iff_norm_tendsto_zero]
    exact h
  -- Suppose `‖x‖ ≥ 1`. Then `‖x^n‖ = ‖x‖^n ≥ 1` for all `n ≥ 1`, contradicting `‖x^n‖ → 0`.
  by_contra h
  rw [not_lt] at h
  have h_xn_eq : ∀ n : ℕ, ‖x ^ n.succ‖ = ‖x‖ ^ n.succ := fun n => by
    induction n with
    | zero => simp
    | succ k ih => rw [pow_succ x (k+1), norm_mul, ih, pow_succ ‖x‖ (k+1)]
  have h_xn_ge_one : ∀ n : ℕ, (1 : ℝ) ≤ ‖x ^ n.succ‖ := fun n => by
    rw [h_xn_eq]; exact one_le_pow₀ h
  -- A sequence converging to 0 in ℝ cannot be eventually ≥ 1.
  have h_subseq : Filter.Tendsto (fun n : ℕ => ‖x ^ n.succ‖) Filter.atTop (𝓝 0) :=
    h_xn_tendsto.comp (Filter.tendsto_atTop_atTop.mpr fun b => ⟨b, fun a ha => Nat.le_succ_of_le ha⟩)
  have h0 : (1 : ℝ) ≤ 0 :=
    le_of_tendsto_of_tendsto' tendsto_const_nhds h_subseq h_xn_ge_one
  linarith

/-- The open unit ball is contained in the power-bounded subring `A°`. -/
lemma ball_zero_one_subset_powerBoundedSubring {A : Type*} [NormedRing A] :
    Metric.ball (0 : A) 1 ⊆ powerBoundedSubring A := fun x hx => by
  rw [Metric.mem_ball, dist_zero_right] at hx
  exact isPowerBounded_of_norm_lt_one hx

/-- `A°` contains an open neighborhood of every one of its points, hence is open. -/
lemma powerBoundedSubring_isOpen {A : Type*} [NormedCommRing A]
    [IsLinearTopology A A] : IsOpen ((powerBoundedSubring.toSubring A) : Set A) := by
  rw [isOpen_iff_mem_nhds]
  intro a ha
  filter_upwards [Metric.ball_mem_nhds a one_pos] with b hb
  rw [Metric.mem_ball, dist_eq_norm] at hb
  have h1 : (b - a : A) ∈ powerBoundedSubring.toSubring A := by
    refine ball_zero_one_subset_powerBoundedSubring ?_
    rw [Metric.mem_ball, dist_zero_right]; exact hb
  have hab : b = a + (b - a) := by ring
  show b ∈ powerBoundedSubring.toSubring A
  rw [hab]
  exact (powerBoundedSubring.toSubring A).add_mem ha h1

/-- An open additive subgroup of a topological additive group is also closed. Specialised here
to `A°`. -/
lemma powerBoundedSubring_isClosed {A : Type*} [NormedCommRing A]
    [IsLinearTopology A A] : IsClosed ((powerBoundedSubring.toSubring A) : Set A) :=
  (powerBoundedSubring.toSubring A).toAddSubgroup.isClosed_of_isOpen powerBoundedSubring_isOpen

/-- **Lemma 4.17.** If `A` is complete, so is the ring `A°` of power-bounded elements. -/
instance powerBoundedSubring_completeSpace {A : Type*} [NormedCommRing A]
    [IsLinearTopology A A] [CompleteSpace A] :
    CompleteSpace ↥(powerBoundedSubring.toSubring A) :=
  haveI : IsClosed ((powerBoundedSubring.toSubring A) : Set A) := powerBoundedSubring_isClosed
  IsClosed.completeSpace_coe

/-- A seminormed additive commutative group with an ultrametric distance is
nonarchimedean: every neighbourhood of `0` contains an open additive subgroup,
namely an open metric ball. -/
instance _root_.IsUltrametricDist.toNonarchimedeanAddGroup {G : Type*}
    [SeminormedAddCommGroup G] [IsUltrametricDist G] : NonarchimedeanAddGroup G where
  is_nonarchimedean := by
    intro U hU
    obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.mp hU
    let V : AddSubgroup G :=
      { carrier := Metric.ball 0 ε
        add_mem' := fun {a b} ha hb => by
          rw [Metric.mem_ball, dist_zero_right] at ha hb ⊢
          exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max a b) (max_lt ha hb)
        zero_mem' := by simp [Metric.mem_ball, hε]
        neg_mem' := fun {a} ha => by
          rw [Metric.mem_ball, dist_zero_right] at ha ⊢
          rwa [norm_neg] }
    exact ⟨⟨V, Metric.isOpen_ball⟩, hεU⟩

/-- **Helper for Lemma 4.18.** In a complete ultrametric normed ring, every element of
the form `1 - y` with `y` topologically nilpotent is a unit, with inverse `∑' n, y^n`.

Unlike `foo_isUnit`, this avoids the `IsLinearTopology` hypothesis by using that summability
in a non-archimedean complete group is equivalent to convergence to `0` on cofinite sets. -/
lemma isUnit_one_sub_of_isTopologicallyNilpotent {A : Type*} [NormedRing A]
    [IsUltrametricDist A] [CompleteSpace A]
    {y : A} (hy : IsTopologicallyNilpotent y) : IsUnit (1 - y) := by
  -- `‖y^n‖ → 0`, so `y^n → 0` as `n → ∞`.
  have htn : Filter.Tendsto (fun n : ℕ => y ^ n) Filter.atTop (𝓝 0) := hy
  -- On `ℕ`, the cofinite filter equals `atTop`, so this gives convergence on cofinite sets.
  have htn_cof : Filter.Tendsto (fun n : ℕ => y ^ n) Filter.cofinite (𝓝 0) := by
    rwa [Nat.cofinite_eq_atTop]
  -- In a non-archimedean complete additive group, `summable ↔ tendsto cofinite (𝓝 0)`.
  have hsum : Summable (fun n : ℕ => y ^ n) :=
    NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero htn_cof
  exact ⟨⟨1 - y, ∑' n, y ^ n, hsum.one_sub_mul_tsum_pow, hsum.tsum_pow_mul_one_sub⟩, rfl⟩

/-- The `R`-linear topology on `R` restricts to an `R°`-linear topology on `R°`: every
open ideal `J` of `R` pulls back along the inclusion to an open ideal `J.comap subtype` of `R°`,
and these form a basis of neighbourhoods of zero in `R°`. -/
instance powerBoundedSubring_isLinearTopology {A : Type*} [NormedCommRing A]
    [IsLinearTopology A A] :
    IsLinearTopology ↥(powerBoundedSubring.toSubring A)
      ↥(powerBoundedSubring.toSubring A) := by
  refine IsLinearTopology.mk_of_hasBasis'
    (R := ↥(powerBoundedSubring.toSubring A))
    (S := Ideal ↥(powerBoundedSubring.toSubring A))
    (p := fun J : Ideal A => IsOpen (J : Set A))
    (s := fun J => J.comap (powerBoundedSubring.toSubring A).subtype) ?_ ?_
  · -- `𝓝 (0 : R°)` is `comap subtype (𝓝 (0 : R))`, and `IsLinearTopology R R` gives the
    -- basis of open ideals of `R`; comap commutes with `HasBasis`.
    have hcoe : ((0 : ↥(powerBoundedSubring.toSubring A)) : A) = (0 : A) := rfl
    rw [show (𝓝 (0 : ↥(powerBoundedSubring.toSubring A))) =
        Filter.comap ((↑) : ↥(powerBoundedSubring.toSubring A) → A) (𝓝 (0 : A)) from by
      rw [nhds_subtype_eq_comap]; congr]
    convert (IsLinearTopology.hasBasis_open_ideal (R := A)).comap
      ((↑) : ↥(powerBoundedSubring.toSubring A) → A) using 0
  · intros I r m hm
    exact I.smul_mem r hm

/-! ### Norm-bounded elements are power-bounded (`NormOneClass`)

The standard easy direction: any element of norm `≤ 1` is power-bounded. The converse
(`IsPowerBounded ⟹ ‖·‖ ≤ 1`) needs a stronger hypothesis (typically `NormedField` /
`NontriviallyNormedField`) and is not included here; it can be added when needed. -/

/-- In a normed ring with `[NormOneClass]`, every element of norm `≤ 1` is power-bounded. -/
lemma _root_.IsPowerBounded.of_norm_le_one {A : Type*} [NormedRing A] [NormOneClass A]
    [IsTopologicalSemiring A] {b : A} (hb : ‖b‖ ≤ 1) : IsPowerBounded b := by
  intro U hU
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.mp hU
  refine ⟨Metric.ball 0 ε, Metric.ball_mem_nhds 0 hε, ?_⟩
  rintro _ ⟨v, hv, _, ⟨n, rfl⟩, rfl⟩
  apply hεU
  rw [Metric.mem_ball, dist_zero_right] at hv ⊢
  -- `‖v · b^n‖ ≤ ‖v‖ · ‖b^n‖ ≤ ‖v‖ · ‖b‖^n ≤ ‖v‖ · 1 = ‖v‖ < ε`.
  have hbn : ‖b ^ n‖ ≤ 1 :=
    (norm_pow_le b n).trans (pow_le_one₀ (norm_nonneg _) hb)
  calc ‖v * b ^ n‖
      ≤ ‖v‖ * ‖b ^ n‖ := norm_mul_le _ _
    _ ≤ ‖v‖ * 1 := mul_le_mul_of_nonneg_left hbn (norm_nonneg _)
    _ = ‖v‖ := mul_one _
    _ < ε := hv

/-- In a `NormedField`, every power-bounded element has norm `≤ 1` (the valuation-ring
property). This is the `h_pb_norm` hypothesis of `closedBall_ideal` made concrete.

Proof: by contradiction, suppose `‖b‖ > 1`. Then `b ≠ 0` and `‖b⁻¹‖ = ‖b‖⁻¹ < 1`, so
`‖b⁻¹‖^k → 0`; pick `k` with `‖b⁻¹‖^k < δ` (where `δ > 0` comes from `IsPowerBounded`).
The element `v := b⁻¹^k` lies in `V` (since `‖v‖ < δ`), and `v · b^k = 1`. But by the
power-bounded property, `v · b^k ∈ Metric.ball 0 1`, so `‖1‖ < 1`, contradiction. -/
lemma _root_.IsPowerBounded.norm_le_one_of_normedField {A : Type*} [NormedField A]
    {b : A} (hb : IsPowerBounded b) : ‖b‖ ≤ 1 := by
  by_contra h_lt
  rw [not_le] at h_lt  -- h_lt : 1 < ‖b‖
  -- Apply `IsBounded` of `{b^n}` to `U = Metric.ball 0 1`.
  obtain ⟨V, hV, hVU⟩ := hb (Metric.ball (0 : A) 1) (Metric.ball_mem_nhds 0 one_pos)
  -- `V` contains `Metric.ball 0 δ` for some `δ > 0`.
  obtain ⟨δ, hδ_pos, hδ⟩ := Metric.mem_nhds_iff.mp hV
  -- `b ≠ 0` since `‖b‖ > 1 > 0`.
  have hb_ne : b ≠ 0 := fun h0 => by rw [h0, norm_zero] at h_lt; linarith
  -- `‖b⁻¹‖ = ‖b‖⁻¹ < 1`.
  have h_binv_lt : ‖b⁻¹‖ < 1 := by
    rw [norm_inv]; exact inv_lt_one_of_one_lt₀ h_lt
  -- Pick `k` with `‖b⁻¹‖^k < δ`.
  have h_tendsto : Filter.Tendsto (fun k : ℕ => ‖b⁻¹‖^k) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) h_binv_lt
  obtain ⟨k, hk⟩ : ∃ k : ℕ, ‖b⁻¹‖^k < δ := by
    obtain ⟨k, hk⟩ := Metric.tendsto_atTop.mp h_tendsto δ hδ_pos
    have := hk k le_rfl
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (pow_nonneg (norm_nonneg _) _)] at this
    exact ⟨k, this⟩
  -- Define `v := b⁻¹^k`. Then `‖v‖ < δ`, so `v ∈ V`, and `v · b^k = 1`.
  set v : A := b⁻¹^k with hv_def
  have hv_norm : ‖v‖ < δ := by rw [hv_def, norm_pow]; exact hk
  have hv_mem : v ∈ V := hδ (by rw [Metric.mem_ball, dist_zero_right]; exact hv_norm)
  have h_vbk_eq : v * b^k = 1 := by
    rw [hv_def, ← mul_pow, inv_mul_cancel₀ hb_ne, one_pow]
  -- `v · b^k ∈ V · {b^n}` ⊆ `Metric.ball 0 1`, so `‖1‖ < 1`, contradiction.
  have h_in_ball : (1 : A) ∈ Metric.ball (0 : A) 1 := by
    have h_mem : v * b^k ∈ V * Set.range (b ^ · : ℕ → A) :=
      ⟨v, hv_mem, b^k, ⟨k, rfl⟩, rfl⟩
    rw [← h_vbk_eq]
    exact hVU h_mem
  rw [Metric.mem_ball, dist_zero_right, norm_one] at h_in_ball
  linarith

/-! ### The ε-ideal `R_ε ⊆ R°` (PDF: ideal of norm-≤-ε elements)

For `ε ∈ [0, 1]`, the set `{a ∈ R° : ‖(a : R)‖ ≤ ε}` is an ideal of `R°`. Closure:
* `add_mem`: ultrametric `‖a + b‖ ≤ max(‖a‖, ‖b‖) ≤ ε`.
* `smul_mem`: for `b ∈ R°` (`‖b‖ ≤ 1` under sufficient hypotheses) and `a ∈ R_ε`,
  `‖b · a‖ ≤ ‖b‖ · ‖a‖ ≤ 1 · ε = ε`.

Special cases: `R_0 = R°°` (topologically nilpotent) and `R_1 = R°` (unit ideal). The
range `ε ∈ (0, 1)` gives strictly intermediate ideals, used in the τ_ε construction.

The `smul_mem` proof relies on `IsPowerBounded b ⟹ ‖b‖ ≤ 1`. This direction is true in
`NormedField` (where it's the valuation-ring property) but requires care to state in a
general normed ring; for the application in `WeierstrassDiv` the base ring will be a
normed field. The lemma is currently parameterised by a `norm_le_one_of_powerBounded`
hypothesis, decoupling the definition from the proof of that direction. -/

/-- The ideal `R_ε := {a ∈ R° : ‖a‖ ≤ ε}` of the power-bounded subring.

The `h_pb_norm` hypothesis encodes `IsPowerBounded ⟹ ‖·‖ ≤ 1`, which is automatic in
`NormedField` but not in arbitrary `NormedCommRing` settings. -/
def closedBall_ideal {A : Type*} [NormedCommRing A] [IsUltrametricDist A]
    [IsLinearTopology A A] (ε : ℝ) (hε : 0 ≤ ε)
    (h_pb_norm : ∀ b : A, IsPowerBounded b → ‖b‖ ≤ 1) :
    Ideal ↥(powerBoundedSubring.toSubring A) where
  carrier := {a : ↥(powerBoundedSubring.toSubring A) | ‖(a : A)‖ ≤ ε}
  add_mem' := fun {a b} ha hb => by
    show ‖((a + b : ↥(powerBoundedSubring.toSubring A)) : A)‖ ≤ ε
    have h_coe : ((a + b : ↥(powerBoundedSubring.toSubring A)) : A) = (a : A) + (b : A) := by
      push_cast; ring
    rw [h_coe]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)
  zero_mem' := by
    show ‖((0 : ↥(powerBoundedSubring.toSubring A)) : A)‖ ≤ ε
    rw [show ((0 : ↥(powerBoundedSubring.toSubring A)) : A) = 0 from rfl, norm_zero]
    exact hε
  smul_mem' := fun b {a} ha => by
    show ‖((b * a : ↥(powerBoundedSubring.toSubring A)) : A)‖ ≤ ε
    have h_coe : ((b * a : ↥(powerBoundedSubring.toSubring A)) : A) = (b : A) * (a : A) := by
      push_cast; ring
    rw [h_coe]
    -- `‖b · a‖ ≤ ‖b‖ · ‖a‖ ≤ 1 · ε = ε` (submult + `‖b‖ ≤ 1` from `h_pb_norm`).
    have hb_norm : ‖(b : A)‖ ≤ 1 := h_pb_norm (b : A) b.2
    calc ‖(b : A) * (a : A)‖
        ≤ ‖(b : A)‖ * ‖(a : A)‖ := norm_mul_le _ _
      _ ≤ 1 * ε := mul_le_mul hb_norm ha (norm_nonneg _) (by linarith)
      _ = ε := one_mul _

/-- Membership in `closedBall_ideal ε hε h_pb_norm`: `a ∈ closedBall_ideal ⟺ ‖(a : A)‖ ≤ ε`. -/
@[simp]
lemma mem_closedBall_ideal {A : Type*} [NormedCommRing A] [IsUltrametricDist A]
    [IsLinearTopology A A] {ε : ℝ} (hε : 0 ≤ ε)
    (h_pb_norm : ∀ b : A, IsPowerBounded b → ‖b‖ ≤ 1)
    (a : ↥(powerBoundedSubring.toSubring A)) :
    a ∈ closedBall_ideal ε hε h_pb_norm ↔ ‖(a : A)‖ ≤ ε := Iff.rfl

end TopologicalRing
