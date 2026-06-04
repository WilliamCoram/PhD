import PhD.ToPR.RestrictedIso
import PhD.ToPR.GaussNorm
import PhD.ToPR.MvGaussNorm
import PhD.ToPR.Restricted
import PhD.ToPR.MvRestricted

import PhD.WeierstrassPrep.Restricted_powerbounded_topnil
import PhD.WeierstrassPrep.EpsilonDense


/-
TODOs:
* Various comments in sections
* restructure file and break into seperate files for clarity
* End of file comment on generalising to MvRestricted
* Rewrite the blueprint again i.e. move the lemmas in order and set up as it should be
* Work on the other chapters of the blueprint

-/

section Polynomial
-- TODO: Move this section elsewhere

namespace Polynomial

variable {S : Type*} [NormedRing S] [IsUltrametricDist S]

@[simp] lemma toRestricted_zero (c : ℝ) :
    toRestricted c (0 : Polynomial S) = 0 := by
  apply Subtype.ext
  show ((0 : Polynomial S) : PowerSeries S) = 0
  exact Polynomial.coe_zero

@[simp] lemma toRestricted_add (c : ℝ) (p q : Polynomial S) :
    toRestricted c (p + q) = toRestricted c p + toRestricted c q := by
  apply Subtype.ext
  show ((p + q : Polynomial S) : PowerSeries S) =
    ((p : PowerSeries S) + (q : PowerSeries S))
  exact Polynomial.coe_add p q

@[simp] lemma toRestricted_neg (c : ℝ) (p : Polynomial S) :
    toRestricted c (-p) = -toRestricted c p := by
  apply Subtype.ext
  show ((-p : Polynomial S) : PowerSeries S) = -((p : PowerSeries S))
  ext n
  rw [map_neg, Polynomial.coeff_coe, Polynomial.coeff_coe, Polynomial.coeff_neg]

@[simp] lemma toRestricted_sub (c : ℝ) (p q : Polynomial S) :
    toRestricted c (p - q) = toRestricted c p - toRestricted c q := by
  rw [sub_eq_add_neg, toRestricted_add, toRestricted_neg, sub_eq_add_neg]

end Polynomial

end Polynomial

section Constant
-- TODO: Move this section elsewhere
-- API for the constant restricted power series `PowerSeries.Restricted.C c a = ⟨PowerSeries.C a, _⟩`.

namespace PowerSeries.Restricted

variable {S : Type*} [NormedCommRing S] [IsUltrametricDist S]

@[simp] lemma C_val (c : ℝ) (a : S) : (C c a).1 = PowerSeries.C a := rfl

lemma coeff_C (c : ℝ) (a : S) (n : ℕ) :
    PowerSeries.coeff n (C c a).1 = if n = 0 then a else 0 := by
  rw [C_val, PowerSeries.coeff_C]

@[simp] lemma coeff_zero_C (c : ℝ) (a : S) : PowerSeries.coeff 0 (C c a).1 = a := by
  rw [C_val, PowerSeries.coeff_zero_C]

lemma C_one (c : ℝ) : C c (1 : S) = 1 := by
  apply Subtype.ext
  show PowerSeries.C (1 : S) = 1
  exact map_one PowerSeries.C

lemma C_mul (c : ℝ) (a b : S) : C c (a * b) = C c a * C c b := by
  apply Subtype.ext
  show PowerSeries.C (a * b) = PowerSeries.C a * PowerSeries.C b
  exact map_mul PowerSeries.C a b

/-- `C c` sends units to units (it is multiplicative and preserves `1`). -/
lemma C_isUnit (c : ℝ) {a : S} (ha : IsUnit a) : IsUnit (C c a) := by
  obtain ⟨u, rfl⟩ := ha
  exact ⟨⟨C c u.val, C c u.inv,
    by rw [← C_mul, u.val_inv, C_one], by rw [← C_mul, u.inv_val, C_one]⟩, rfl⟩

/-- Coefficients of `C c a * g`: scaling by the constant `a`. -/
lemma coeff_C_mul (c : ℝ) (a : S) (g : PowerSeries.Restricted S c) (n : ℕ) :
    PowerSeries.coeff n (C c a * g).1 = a * PowerSeries.coeff n g.1 := by
  show PowerSeries.coeff n ((C c a).1 * g.1) = a * PowerSeries.coeff n g.1
  rw [C_val, PowerSeries.coeff_C_mul]

/-- The Gauss norm of a constant series is the norm of the constant (only the `0`-th coefficient
is nonzero, with value `a` and weight `c ^ 0 = 1`). -/
lemma norm_C (c : ℝ) [StrongPos (fun _ : Unit ↦ c)] (a : S) : ‖C c a‖ = ‖a‖ := by
  refine le_antisymm ?_ ?_
  · rw [Restricted.norm_eq, PowerSeries.gaussNorm_eq]
    refine ciSup_le fun i => ?_
    rw [C_val, PowerSeries.coeff_C]
    split_ifs with hi
    · subst hi; simp
    · simp [norm_nonneg]
  · have h := PowerSeries.le_gaussNorm norm c (C c a).1 (Restricted.hasGaussNorm c (C c a)) 0
    rw [← Restricted.norm_eq, pow_zero, mul_one] at h
    rwa [coeff_zero_C] at h

/-- Multiplying a polynomial-as-restricted-series by the constant `C c a` scales the polynomial
by `Polynomial.C a`. -/
lemma C_mul_toRestricted (c : ℝ) (a : S) (r : Polynomial S) :
    C c a * Polynomial.toRestricted c r = Polynomial.toRestricted c (Polynomial.C a * r) := by
  apply Subtype.ext
  show (C c a).1 * (Polynomial.toRestricted c r).1
    = (Polynomial.toRestricted c (Polynomial.C a * r)).1
  show PowerSeries.C a * (r : PowerSeries S) = ((Polynomial.C a * r : Polynomial S) : PowerSeries S)
  rw [Polynomial.coe_mul, Polynomial.coe_C]

end PowerSeries.Restricted

end Constant

variable {R : Type*} (v : R → ℝ)

def coeff_isUnit [Semiring R] (f : PowerSeries R) (s : ℕ) : Prop := IsUnit (PowerSeries.coeff s f)

def norm_eq [Semiring R] (c : ℝ) (f : PowerSeries R) (s : ℕ) : Prop :=
  PowerSeries.gaussNorm v c f = v (PowerSeries.coeff s f)

def norm_max_achiever [Semiring R] (f : PowerSeries R) (s : ℕ) : Prop :=
  ∀ t, s < t → v (PowerSeries.coeff t f) < v (PowerSeries.coeff s f)

structure distinguished [Semiring R] (c : ℝ) (f : PowerSeries R) (s : ℕ) : Prop where
  unit : coeff_isUnit f s
  norm_eq : norm_eq v c f s
  norm_max : norm_max_achiever v f s

/-- `g ≠ 0` when `g` is distinguished of degree `s`: the `s`-th coefficient is a unit
(in the nontrivial ring), hence nonzero. -/
lemma distinguished.ne_zero [Semiring R] [Nontrivial R] (g : PowerSeries R) (c : ℝ)
    {s : ℕ} (hg : distinguished v c g s) : g ≠ 0 := by
  by_contra
  exact hg.unit.ne_zero (by grind)

section WeierstrassDivision

-- I think for now I can prove with just R in the coeff... as this should save a lot of effort
-- then for MvPowerSeries in the coeff I just need all the correct instances
-- which should be easier

open Topology

-- still need to get around this
local instance : StrongPos (fun _ : Unit ↦ (1 : ℝ)) where
  pos := by simp

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R] [NormMulClass R]
  [NormOneClass R] [Filter.NeBot (𝓝[≠] (0 : R))] [Nontrivial R]

local instance : NormMulClass (PowerSeries.Restricted R 1) :=
  MvPowerSeries.Restricted.normMulClass (σ := Unit) (fun _ ↦ 1)

-- note this should not be proven like this
-- instead it should be a general statement for MvPowerSeries and this as a corollary
-- note that the .C section should also be generalised to MvPowerSeries then
local instance : NormOneClass (PowerSeries.Restricted R 1) where
  norm_one := by
    rw [← PowerSeries.Restricted.C_one (S := R) 1, PowerSeries.Restricted.norm_C, norm_one]

-- `NonarchimedeanRing`/`IsLinearTopology ℤ` for any ultrametric normed comm ring (fires for both
-- `R` and `PowerSeries.Restricted R 1`); needed for `PowerBounded.subring _ (S := ℤ)`.
local instance instNonarch {S : Type*} [NormedCommRing S] [IsUltrametricDist S] :
    NonarchimedeanRing S where
  is_nonarchimedean := (IsUltrametricDist.nonarchimedeanAddGroup).is_nonarchimedean

local instance instLinTopZ (S : Type*) [Ring S] [TopologicalSpace S] [NonarchimedeanRing S] :
    IsLinearTopology ℤ S := by
  apply IsLinearTopology.mk_of_hasBasis' (R := ℤ)
    (p := fun U : AddSubgroup S => (U : Set S) ∈ nhds 0)
    (s := fun U : AddSubgroup S => U)
  · refine ⟨fun U => ⟨fun hU => ?_,
      fun ⟨_, hN_mem, hN⟩ => Filter.mem_of_superset hN_mem hN⟩⟩
    obtain ⟨V, hV⟩ := NonarchimedeanRing.is_nonarchimedean U hU
    exact ⟨V.toAddSubgroup, V.mem_nhds_zero, hV⟩
  · intro _ n _ hm
    exact zsmul_mem hm n

/-- `R°`, the power-bounded subring of the base ring `R`. -/
local notation "R°" => PowerBounded.subring R (S := ℤ)
/-- `T°`, the power-bounded subring of `T = PowerSeries.Restricted R 1`. -/
local notation "T°" => PowerBounded.subring (PowerSeries.Restricted R 1) (S := ℤ)

section bounds

lemma contra (g : PowerSeries.Restricted R 1) (s : ℕ)
    (hg : distinguished norm 1 g.1 s) (f q : PowerSeries.Restricted R 1) (r : Polynomial R)
    (hr : Polynomial.degree r < s) (hf : f = g * q + Polynomial.toRestricted 1 r)
    (hf_lt : ‖f‖ < max ‖g * q‖ ‖Polynomial.toRestricted 1 r‖) : False := by
  -- **Scaling-free realisation of PDF Lemma 4.9.**  The blueprint normalises `max{|q|,|r|}=1`
  -- by a scalar and reduces in the residue field, concluding `q̃ = r̃ = 0` from
  -- `deg g̃ = s > deg r̃`.  Here `R` has no scalar field to normalise by, so we argue
  -- coefficient-wise: the dominant coefficient of `g·q` (at degree `peak(q) + s`) is the leading
  -- coefficient of `q̃·g̃`, nonzero precisely because `deg(q̃·g̃) = deg q̃ + s > deg r̃`.  This
  -- forces `‖g·q‖ ≤ ‖f‖`, contradicting `hf_lt`.
  by_cases hq_zero : q = 0
  · subst hq_zero
    rw [mul_zero, zero_add] at hf
    rw [hf, mul_zero, norm_zero, max_eq_right (norm_nonneg _)] at hf_lt
    exact lt_irrefl _ hf_lt
  have hq_pos : (0 : ℝ) < ‖q‖ := norm_pos_iff.mpr hq_zero
  -- Restrictedness ⇒ coefficient norms of `q` tend to `0`, so the peak set is finite.
  have h_restr_q : Filter.Tendsto
      (fun a : ℕ => ‖PowerSeries.coeff a q.1‖) Filter.atTop (nhds 0) := by
    have h := (PowerSeries.isRestricted_iff 1 q.1).mp q.2
    rw [Nat.cofinite_eq_atTop] at h
    refine h.congr fun t => ?_; simp
  obtain ⟨N, hN⟩ : ∃ N, ∀ a ≥ N, ‖PowerSeries.coeff a q.1‖ < ‖q‖ := by
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp h_restr_q ‖q‖ hq_pos
    refine ⟨N, fun a ha => ?_⟩
    have := hN a ha
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] at this
    exact this
  have h_peak_finite : ({a : ℕ | ‖PowerSeries.coeff a q.1‖ = ‖q‖}).Finite := by
    refine Set.Finite.subset (Set.finite_Iio N) (fun a ha => ?_)
    by_contra h_ge
    exact (lt_self_iff_false ‖q‖).mp (ha ▸ hN a (Nat.le_of_not_lt h_ge))
  have h_peak_nonempty : ({a : ℕ | ‖PowerSeries.coeff a q.1‖ = ‖q‖}).Nonempty := by
    obtain ⟨a₀, ha₀⟩ := Restricted.gaussNorm_achieved' 1 zero_le_one q
    refine ⟨a₀, ?_⟩
    show ‖PowerSeries.coeff a₀ q.1‖ = ‖q‖
    rw [one_pow, mul_one] at ha₀; rw [ha₀]; rfl
  -- Take the largest peak `u`.
  let M_set := h_peak_finite.toFinset
  have hM_ne : M_set.Nonempty := by rw [Set.Finite.toFinset_nonempty]; exact h_peak_nonempty
  let u := M_set.max' hM_ne
  have hu_peak : ‖PowerSeries.coeff u q.1‖ = ‖q‖ := by
    have hu_mem := M_set.max'_mem hM_ne
    simp [M_set] at hu_mem; exact hu_mem
  have hu_max : ∀ a, u < a → ‖PowerSeries.coeff a q.1‖ < ‖q‖ := by
    intro a ha_gt
    by_contra h_not_lt
    rw [not_lt] at h_not_lt
    have h_bd : ‖PowerSeries.coeff a q.1‖ ≤ ‖q‖ := by
      have := PowerSeries.le_gaussNorm norm 1 q.1 (Restricted.hasGaussNorm 1 q) a
      rwa [one_pow, mul_one, ← Restricted.norm_eq] at this
    have h_a_in : a ∈ M_set := by
      simp only [M_set, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
      exact le_antisymm h_bd h_not_lt
    have := M_set.le_max' a h_a_in
    omega
  -- `‖coeff_s g.1‖ = ‖g‖` and `‖g‖ > 0`.
  have hg_pos : (0 : ℝ) < ‖g‖ := norm_pos_iff.mpr (ne_of_apply_ne Subtype.val hg.ne_zero)
  have h_coeff_s_g : ‖PowerSeries.coeff s g.1‖ = ‖g‖ := by
    have h : PowerSeries.gaussNorm norm 1 g.1 = ‖PowerSeries.coeff s g.1‖ := hg.norm_eq
    rw [← h, ← Restricted.norm_eq]
  -- Dominant coefficient: `‖coeff_{u+s} (g*q).1‖ = ‖g‖·‖q‖` (convolution dominance).
  have h_peak_gq : ‖PowerSeries.coeff (u + s) (g * q).1‖ = ‖g‖ * ‖q‖ := by
    show ‖PowerSeries.coeff (u + s) (g.1 * q.1)‖ = ‖g‖ * ‖q‖
    rw [PowerSeries.coeff_mul]
    have h_su_mem : (s, u) ∈ Finset.antidiagonal (u + s) := by
      rw [Finset.mem_antidiagonal]; ring
    rw [← Finset.sum_erase_add _ _ h_su_mem]
    have h_rest_lt : ∀ p ∈ (Finset.antidiagonal (u + s)).erase (s, u),
        ‖PowerSeries.coeff p.1 g.1 * PowerSeries.coeff p.2 q.1‖ < ‖g‖ * ‖q‖ := by
      rintro ⟨a, b⟩ hp
      rw [Finset.mem_erase, Finset.mem_antidiagonal] at hp
      obtain ⟨hne, hmem⟩ := hp
      rw [norm_mul]
      rcases lt_trichotomy a s with hlt | heq | hgt
      · have hb_lt : ‖PowerSeries.coeff b q.1‖ < ‖q‖ := hu_max b (by omega)
        have ha_le : ‖PowerSeries.coeff a g.1‖ ≤ ‖g‖ := by
          have := PowerSeries.le_gaussNorm norm 1 g.1 (Restricted.hasGaussNorm 1 g) a
          rwa [one_pow, mul_one, ← Restricted.norm_eq] at this
        calc ‖PowerSeries.coeff a g.1‖ * ‖PowerSeries.coeff b q.1‖
            ≤ ‖g‖ * ‖PowerSeries.coeff b q.1‖ :=
              mul_le_mul_of_nonneg_right ha_le (norm_nonneg _)
          _ < ‖g‖ * ‖q‖ := by gcongr
      · exact absurd (Prod.ext heq (by simp only; omega)) hne
      · have ha_lt : ‖PowerSeries.coeff a g.1‖ < ‖g‖ := by
          have := hg.norm_max a hgt; rwa [h_coeff_s_g] at this
        have hb_le : ‖PowerSeries.coeff b q.1‖ ≤ ‖q‖ := by
          have := PowerSeries.le_gaussNorm norm 1 q.1 (Restricted.hasGaussNorm 1 q) b
          rwa [one_pow, mul_one, ← Restricted.norm_eq] at this
        calc ‖PowerSeries.coeff a g.1‖ * ‖PowerSeries.coeff b q.1‖
            ≤ ‖PowerSeries.coeff a g.1‖ * ‖q‖ :=
              mul_le_mul_of_nonneg_left hb_le (norm_nonneg _)
          _ < ‖g‖ * ‖q‖ := by gcongr
    have h_rest_norm_lt :
        ‖∑ p ∈ (Finset.antidiagonal (u + s)).erase (s, u),
          PowerSeries.coeff p.1 g.1 * PowerSeries.coeff p.2 q.1‖ < ‖g‖ * ‖q‖ := by
      by_cases h_ne_empty : ((Finset.antidiagonal (u + s)).erase (s, u)).Nonempty
      · calc ‖∑ p ∈ (Finset.antidiagonal (u + s)).erase (s, u),
                PowerSeries.coeff p.1 g.1 * PowerSeries.coeff p.2 q.1‖
            ≤ ((Finset.antidiagonal (u + s)).erase (s, u)).sup' h_ne_empty
                (fun p => ‖PowerSeries.coeff p.1 g.1 * PowerSeries.coeff p.2 q.1‖) :=
              h_ne_empty.norm_sum_le_sup'_norm _
          _ < ‖g‖ * ‖q‖ := (Finset.sup'_lt_iff h_ne_empty).mpr h_rest_lt
      · rw [Finset.not_nonempty_iff_eq_empty] at h_ne_empty
        rw [h_ne_empty, Finset.sum_empty, norm_zero]
        exact mul_pos hg_pos hq_pos
    have h_peak_norm :
        ‖PowerSeries.coeff s g.1 * PowerSeries.coeff u q.1‖ = ‖g‖ * ‖q‖ := by
      rw [norm_mul, h_coeff_s_g, hu_peak]
    have h_ne :
        ‖∑ p ∈ (Finset.antidiagonal (u + s)).erase (s, u),
            PowerSeries.coeff p.1 g.1 * PowerSeries.coeff p.2 q.1‖ ≠
        ‖PowerSeries.coeff s g.1 * PowerSeries.coeff u q.1‖ := by
      rw [h_peak_norm]; exact ne_of_lt h_rest_norm_lt
    rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h_ne, h_peak_norm]
    exact max_eq_right h_rest_norm_lt.le
  -- `coeff_{u+s} (toR r).1 = 0` since `u + s ≥ s > deg r`.
  have h_toR_zero : PowerSeries.coeff (u + s) (Polynomial.toRestricted 1 r).1 = 0 := by
    show PowerSeries.coeff (u + s) r.toPowerSeries = 0
    rw [Polynomial.coeff_coe]
    exact Polynomial.coeff_eq_zero_of_degree_lt
      (hr.trans_le (by exact_mod_cast Nat.le_add_left s u))
  -- Hence `‖coeff_{u+s} f.1‖ = ‖g‖·‖q‖`, so `‖g*q‖ ≤ ‖f‖`.
  have h_coeff_f : ‖PowerSeries.coeff (u + s) f.1‖ = ‖g‖ * ‖q‖ := by
    rw [hf, show (g * q + Polynomial.toRestricted 1 r).1 =
        (g * q).1 + (Polynomial.toRestricted 1 r).1 from rfl, map_add, h_toR_zero, add_zero]
    exact h_peak_gq
  have h_gq_bd : ‖g * q‖ ≤ ‖f‖ := by
    rw [norm_mul, ← h_coeff_f]
    have := PowerSeries.le_gaussNorm norm 1 f.1 (Restricted.hasGaussNorm 1 f) (u + s)
    rwa [one_pow, mul_one, ← Restricted.norm_eq] at this
  -- Contradiction with `hf_lt`.
  rcases lt_max_iff.mp hf_lt with h1 | h2
  · exact lt_irrefl _ (h1.trans_le h_gq_bd)
  · have h_toR_bd : ‖Polynomial.toRestricted 1 r‖ ≤ ‖f‖ := by
      rw [show Polynomial.toRestricted 1 r = f - g * q from by rw [hf]; abel]
      refine (?_ : ‖f - g * q‖ ≤ max ‖f‖ ‖g * q‖).trans (max_le le_rfl h_gq_bd)
      have := IsUltrametricDist.norm_add_le_max f (-(g * q))
      rwa [← sub_eq_add_neg, norm_neg] at this
    exact lt_irrefl _ (h2.trans_le h_toR_bd)

lemma weierstrassDivision_bounds_q (g : PowerSeries.Restricted R 1) (s : ℕ)
    (hg : distinguished norm 1 g.1 s) (f : PowerSeries.Restricted R 1)
    (q : PowerSeries.Restricted R 1) (r : Polynomial R) (hr : Polynomial.degree r < s)
    (hf : f = g * q + (Polynomial.toRestricted 1 r)) : ‖q‖ ≤ ‖g‖⁻¹ * ‖f‖ := by
  by_contra
  rw [not_le] at this
  have : ‖f‖ < ‖q‖ * ‖g‖ := by
    suffices h : (0 : ℝ) < ‖g‖ by
      have := mul_lt_mul_of_pos_right this h
      field_simp at this
      simpa [mul_comm]
    exact norm_pos_iff.mpr (ne_of_apply_ne Subtype.val hg.ne_zero)
  rw [← norm_mul, mul_comm] at this
  exact contra g s hg f q r hr hf (lt_max_iff.mpr (Or.inl this))

lemma weierstrassDivision_bounds_r (g : PowerSeries.Restricted R 1) (s : ℕ)
    (hg : distinguished norm 1 g.1 s) (f : PowerSeries.Restricted R 1)
    (q : PowerSeries.Restricted R 1) (r : Polynomial R) (hr : Polynomial.degree r < s)
    (hf : f = g * q + (Polynomial.toRestricted 1 r)) : ‖(Polynomial.toRestricted 1 r)‖ ≤ ‖f‖ := by
  by_contra h_bd
  rw [not_le] at h_bd
  exact contra g s hg f q r hr hf (lt_max_iff.mpr (Or.inr h_bd))

end bounds

section DenseSet

/-- The candidate set `B = { g * q + ↑r : q ∈ T, r ∈ S[X] with deg r < s }` from the PDF
proof of Lemma 4.11. -/
def divCarrier (g : PowerSeries.Restricted R 1) (s : ℕ) : Set (PowerSeries.Restricted R 1) :=
  {f | ∃ q, ∃ r : Polynomial R, Polynomial.degree r < s ∧ f = g * q + Polynomial.toRestricted 1 r}

def divSubgroup (g : PowerSeries.Restricted R 1) (s : ℕ) :
    AddSubgroup (PowerSeries.Restricted R 1) where
  carrier := divCarrier g s
  zero_mem' := ⟨0, 0, by simp, by simp⟩
  add_mem' := by
    rintro _ _ ⟨qa, ra, hra, rfl⟩ ⟨qb, rb, hrb, rfl⟩
    refine ⟨qa + qb, ra + rb, ?_, ?_⟩
    · exact lt_of_le_of_lt (Polynomial.degree_add_le _ _) (max_lt hra hrb)
    · rw [Polynomial.toRestricted_add, mul_add]; abel
  neg_mem' := by
    rintro _ ⟨q, r, hr, rfl⟩
    exact ⟨-q, -r, by rwa [Polynomial.degree_neg],
      by rw [Polynomial.toRestricted_neg, mul_neg]; abel⟩

/-! ### API needed for `divSubgroup_dense` (PDF Lemma 4.11)

The PDF proof of Lemma 4.11 ("There exists a representation `f = qg + r`") shows that the
candidate subgroup `B = divCarrier g s` is `ε`-dense, hence dense.  In the **ToPR** development
this was assembled from a stack of API lemmas spread over several files, all phrased for the
*concrete* base ring `S = MvPowerSeries.Restricted R (Fin.tail (1 : Fin (n+1) → ℝ))` with
`R : NormedField`.  Here the base ring is the **abstract** `R` of this section
(`[NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R] [NormMulClass R] [NormOneClass R]`
`[Filter.NeBot (𝓝[≠] 0)] [Nontrivial R]`), so each ToPR lemma must be *edited* to this setup.

The dictionary `ToPR ↦ new setup`:

* `S = MvPowerSeries.Restricted R (Fin.tail 1)`  ↦  `R` (the abstract base ring).
* `T = PowerSeries.Restricted S 1`               ↦  `PowerSeries.Restricted R 1`.
* `T° = PowerSeries.Restricted R° 1` where `R° = TopologicalRing.powerBoundedSubring.toSubring _`.
* The explicit hypothesis
  `h_pb_norm : ∀ b, TopologicalRing.IsPowerBounded b → ‖b‖ ≤ 1`
  (ToPR took this as an argument / discharged it via `IsPowerBounded.norm_le_one_of_normedField`
  for a `NormedField`)  ↦  discharged once from the `Filter.NeBot (𝓝[≠] 0)` instance by
  `IsPowerBounded.norm_le_one_of_neBot` (`WeierstrassPrep/PowerBounded.lean:59`).
* PDF Step 1 (normalise `g` to `|g| = 1`)  ↦  taken as the hypothesis `hg : ‖g‖ = 1`; the
  normalisation by `(coeff s g.1)⁻¹` is pushed out to the caller
  (cf. `weierstrassDivision_existance`).

#### The ToPR lemmas that were used, and their edited (sorried) new-setup forms

1. **`exists_epsilon_of_distinguished`**  (ToPR `WeierstrassDiv.lean:827`).  PDF Step 2: from a
   normalised distinguished `g` extract `ε ∈ (0,1)` dominating all higher coefficient norms.
   Restated live below — its statement uses only names available in this file.

2. **The `T ↔ T°` transit (PDF Steps 3–5) — collapses in the new setup.**  In ToPR this was the
   genuinely type-changing pair `Restricted.toPowerBounded` (`RestrictedUnits.lean:550`) and
   `Restricted.includeOfPowerBounded` (`EuclideanDiv.lean:258`), with `includeOfPowerBounded`
   `_toPowerBounded` (`EuclideanDiv.lean:356`) and `norm_includeOfPowerBounded` (`EuclideanDiv`
   `.lean:339`) — moving between `T = Restricted R 1` and the *different type*
   `T° = Restricted R° 1` over the power-bounded subring `R° = powerBoundedSubring.toSubring R`,
   then proving the map is a norm-preserving ring hom with a round-trip identity.

   The results in `WeierstrassPrep/Restricted_powerbounded_topnil.lean` let us **avoid the type
   change entirely**: `T°` is just the *subset* `{f : Restricted R 1 | ‖f‖ ≤ 1}` of `T`, and the
   inclusion `T° ↪ T` is the identity on the underlying series.  Concretely:
   * `IsPowerBounded.isPowerBounded_iff'` (`WeierstrassPrep/PowerBounded.lean:97`):
     `IsPowerBounded f ↔ ‖f‖ ≤ 1`, i.e. `(R⟨x⟩)° = {f | ‖f‖ ≤ 1}` — being in `T°` *is* the
     norm-`≤ 1` condition.
   * `bar` (`Restricted_powerbounded_topnil.lean:199`):
     `(∀ i, IsPowerBounded (coeff i f.1)) → IsPowerBounded f`, together with its converse
     `powerBounded_coeffs_of_powerBounded` (`:181`):
     `IsPowerBounded f → ∀ i, IsPowerBounded (coeff i f.1)` — i.e. `(R⟨x⟩)° = R°⟨x⟩`: a
     restricted series is power-bounded iff each coefficient is power-bounded (lies in `R°`).
     (For PDF Step 3 we also have the topologically-nilpotent analogues `foo` (`:252`) /
     `topologicallyNilpotent_coeffs_of_topologicallyNilpotent` (`:231`), feeding the reduction
     mod `R°°`.)

   Consequence for the outline: **no `toPowerBounded`/`includeOfPowerBounded` are needed.**
   `g°`, `f°` of Steps 3–5 are simply `g`, `f` themselves viewed via `isPowerBounded_iff'.mpr hf`
   (using `‖g‖ = 1 ≤ 1` and the per-`f` rescaling for `f`); `norm_includeOfPowerBounded` becomes
   the literal equality `‖f‖ = ‖f‖`, and `includeOfPowerBounded_toPowerBounded` becomes `rfl`.
   The only transit fact still doing work is the coefficient characterisation `bar` /
   `powerBounded_coeffs_of_powerBounded`, used to hand the residue map (group 3) its `R°`-valued
   coefficients.  This removes one `def` + four lemmas from the port and lets Steps 3–5 stay
   inside `Restricted R 1` throughout.

3. **`Restricted.residueRingHom_ε`**  (ToPR `RestrictedUnits.lean:519`) and the fact that
   `τ_ε(g)` is **monic of degree `s`** (proved inline in ToPR's Step 3 from
   `residuePolynomial_ε_coeff` + the distinguished data).  PDF Step 3.  **Ported live below** as
   `closedBall_ideal` (the `ε`-ball ideal `R_ε`), `residueRingHom_ε` (the map
   `τ_ε : T° →+* (R° ⧸ R_ε)[X]`), and `residueRingHom_ε_monic_of_distinguished` — all against the
   new foundation's `PowerBounded.subring _ (S := ℤ)`, with `T° = PowerBounded.subring (Restricted`
   `R 1)` a subring of `T` (per bullet 2, no `Restricted R° 1`).

4. **`Restricted.exists_div_by_τε_monic`**  (ToPR `EuclideanDiv.lean:207`).  PDF Step 4 (division
   modulo `ε` in `T°`).  **Ported live below** as `exists_div_by_τε_monic` (sorried), the engine
   `exists_divApprox` consumes: for `g f ∈ T°` with `τ_ε(g)` monic, it returns `q ∈ T°` and a
   remainder `r : Polynomial R` with `deg r < deg τ_ε(g)` and `‖f - g·q - ↑r‖ ≤ ε`.  Per bullet 2
   the remainder lands directly in `T = Restricted R 1` (no `Restricted R° 1`).

   Step 5 (the per-`f` rescaling that turns the `‖·‖ ≤ ε` bound into `‖·‖ ≤ ε·‖f‖` for arbitrary
   `f`, not just `f ∈ T°`) is where ToPR used `NormedField R` to scale by a unit of norm `‖f‖⁻¹`
   (`exists_div_by_τε_monic_T_scaled`, `EuclideanDiv.lean:428`).  In the abstract `R` that step
   needs a unit of prescribed norm; it is deferred into the body of `exists_divApprox`.

Steps 2–5 are bundled, for the purposes of this skeleton, into the single live lemma
`exists_divApprox` below (the direct `ε`-approximation statement `divSubgroup_dense` consumes);
its body is where the chain (2)→(3)→(4) is to be wired up. -/

omit [CompleteSpace R] [NormMulClass R] [NormOneClass R] [(𝓝[≠] (0 : R)).NeBot] [Nontrivial R] in
/-- **PDF Lemma 4.11, Step 2 (edited from ToPR `exists_epsilon_of_distinguished`).**  For a
normalised distinguished `g` (leading-coefficient norm `1`), there is `ε ∈ (0,1)` dominating
every strictly-higher coefficient norm.  Comes from restrictedness
(`‖coeff t g.1‖ → 0`) plus `distinguished.norm_max`. -/
lemma exists_epsilon_of_distinguished (g : PowerSeries.Restricted R 1) (s : ℕ)
    (gd : distinguished norm 1 g.1 s) (hg1 : ‖PowerSeries.coeff s g.1‖ = 1) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ ∀ t, s < t → ‖PowerSeries.coeff t g.1‖ ≤ ε := by
  -- Restrictedness ⇒ `‖coeff t g.1‖ → 0` along `atTop` on `ℕ`.
  have h_restr :
      Filter.Tendsto (fun t : ℕ => ‖PowerSeries.coeff t g.1‖) Filter.atTop (nhds 0) := by
    have h := (PowerSeries.isRestricted_iff 1 g.1).mp g.2
    rw [Nat.cofinite_eq_atTop] at h
    refine h.congr fun t => ?_
    simp
  -- So eventually `‖coeff t g.1‖ < 1/2`: pick such an `N`.
  obtain ⟨N, hN⟩ : ∃ N, ∀ t ≥ N, ‖PowerSeries.coeff t g.1‖ < 1/2 := by
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp h_restr (1/2) (by norm_num)
    refine ⟨N, fun t ht => ?_⟩
    have := hN t ht
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] at this
    exact this
  -- From `norm_max` + `hg1`, each `‖coeff t g.1‖ < 1` for `t > s`.
  have h_lt_one : ∀ t, s < t → ‖PowerSeries.coeff t g.1‖ < 1 := fun t ht => by
    have := gd.norm_max t ht
    rwa [hg1] at this
  -- Finite finset `F = {‖coeff t g.1‖ : s < t < N}`, each `< 1`.
  let F : Finset ℝ := (Finset.Ioo s N).image (fun t => ‖PowerSeries.coeff t g.1‖)
  -- Take `M = max F`; then `M < 1`, and `ε = max M (1/2)` works.
  by_cases hF : F.Nonempty
  · let M := F.max' hF
    have hM_lt : M < 1 := by
      obtain ⟨t, ht_mem, ht_eq⟩ := Finset.mem_image.mp (F.max'_mem hF)
      rw [Finset.mem_Ioo] at ht_mem
      simpa [M, ← ht_eq] using h_lt_one t ht_mem.1
    refine ⟨max M (1/2), lt_max_iff.mpr (Or.inr (by norm_num)), max_lt hM_lt (by norm_num), ?_⟩
    intro t ht
    rcases lt_or_ge t N with htN | htN
    · -- `s < t < N`, so `‖coeff t g.1‖ ∈ F`, hence `≤ M ≤ ε`.
      have h_mem : ‖PowerSeries.coeff t g.1‖ ∈ F :=
        Finset.mem_image.mpr ⟨t, Finset.mem_Ioo.mpr ⟨ht, htN⟩, rfl⟩
      exact (F.le_max' _ h_mem).trans (le_max_left _ _)
    · -- `t ≥ N`: by `hN`, `‖coeff t g.1‖ < 1/2 ≤ ε`.
      exact (hN t htN).le.trans (le_max_right _ _)
  · -- `F` empty: every `t > s` already has `t ≥ N`. Use `ε = 1/2`.
    refine ⟨1/2, by norm_num, by norm_num, fun t ht => ?_⟩
    have htN : N ≤ t := by
      by_contra h
      exact hF ⟨_, Finset.mem_image.mpr
        ⟨t, Finset.mem_Ioo.mpr ⟨ht, Nat.lt_of_not_ge h⟩, rfl⟩⟩
    exact (hN t htN).le

/-! #### Bullet 3 ported: the residue map `τ_ε` (PDF Step 3)

These are the new-setup forms of `Restricted.residueRingHom_ε` (ToPR `RestrictedUnits.lean:519`)
and the "`τ_ε(g)` is monic of degree `s`" fact (ToPR proved it inline in `divSubgroup_dense`'s
Step 3 from `residuePolynomial_ε_coeff`).  The new foundation supplies the power-bounded subring
`PowerBounded.subring _ (S := ℤ)` (`PR'd/PowerBounded.lean:124`) but **not** the `ε`-ball ideal,
so `closedBall_ideal` is ported here too (its `< 1` analogue is `PowerBounded.topologicalNilradical`,
`PR'd/TopologicallyNilpotent.lean:312`).  Consistent with bullet 2, we never use `Restricted R° 1`:
`T° = PowerBounded.subring (PowerSeries.Restricted R 1)` is a *subring of `T` itself*, and `R°`-valued
coefficients are obtained from `powerBounded_coeffs_of_powerBounded`. -/

/-- **The `ε`-ball ideal `R_ε = {a ∈ R° : ‖a‖ ≤ ε}` of the power-bounded subring `R°`** (PDF
notation; ToPR `TopologicalRing.closedBall_ideal`, `PowerBounded.lean:607`).  The residue ring
`R° ⧸ closedBall_ideal ε` is the PDF's `R̃_ε`.  Ideal axioms use the ultrametric inequality and
`‖r·a‖ ≤ ‖r‖·‖a‖ ≤ 1·ε` for `r ∈ R°`. -/
def closedBall_ideal (ε : ℝ) (hε : 0 ≤ ε) :
    Ideal ↥(PowerBounded.subring R (S := ℤ)) where
  carrier := {a | ‖(a : R)‖ ≤ ε}
  add_mem' := fun {a b} ha hb => by
    show ‖((a + b : ↥(PowerBounded.subring R (S := ℤ))) : R)‖ ≤ ε
    rw [show ((a + b : ↥(PowerBounded.subring R (S := ℤ))) : R) = (a : R) + (b : R) from by
      push_cast; ring]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)
  zero_mem' := by
    show ‖((0 : ↥(PowerBounded.subring R (S := ℤ))) : R)‖ ≤ ε
    rw [show ((0 : ↥(PowerBounded.subring R (S := ℤ))) : R) = 0 from rfl, norm_zero]; exact hε
  smul_mem' := fun c {a} ha => by
    show ‖((c • a : ↥(PowerBounded.subring R (S := ℤ))) : R)‖ ≤ ε
    have hc : ‖(c : R)‖ ≤ 1 := IsPowerBounded.norm_le_one_of_neBot c.2
    rw [smul_eq_mul, show ((c * a : ↥(PowerBounded.subring R (S := ℤ))) : R) = (c : R) * (a : R)
      from by push_cast; ring]
    calc ‖(c : R) * (a : R)‖ ≤ ‖(c : R)‖ * ‖(a : R)‖ := norm_mul_le _ _
      _ ≤ 1 * ε := mul_le_mul hc ha (norm_nonneg _) (by linarith)
      _ = ε := one_mul _

/-- Membership in `closedBall_ideal ε`: `a ∈ closedBall_ideal ⟺ ‖(a : R)‖ ≤ ε`. -/
@[simp] lemma mem_closedBall_ideal (ε : ℝ) (hε : 0 ≤ ε)
    (a : ↥(PowerBounded.subring R (S := ℤ))) :
    a ∈ closedBall_ideal ε hε ↔ ‖(a : R)‖ ≤ ε := Iff.rfl

/-- The `v`-th coefficient of a power-bounded series `f ∈ T°`, packaged as an element of `R°`
(its coefficients are power-bounded by `powerBounded_coeffs_of_powerBounded`). -/
noncomputable def pbCoeff (f : ↥T°) (v : ℕ) : ↥R° :=
  ⟨PowerSeries.coeff v (f : PowerSeries.Restricted R 1).1,
    Restricted.powerBounded_coeffs_of_powerBounded (f : PowerSeries.Restricted R 1) f.2 v⟩

@[simp] lemma pbCoeff_coe (f : ↥T°) (v : ℕ) :
    ((pbCoeff f v : ↥R°) : R) = PowerSeries.coeff v (f : PowerSeries.Restricted R 1).1 := rfl

lemma pbCoeff_add (f g : ↥T°) (v : ℕ) : pbCoeff (f + g) v = pbCoeff f v + pbCoeff g v := by
  apply Subtype.ext
  simp only [pbCoeff_coe, AddMemClass.coe_add]
  rw [show ((f : PowerSeries.Restricted R 1) + (g : PowerSeries.Restricted R 1)).1
    = (f : PowerSeries.Restricted R 1).1 + (g : PowerSeries.Restricted R 1).1 from rfl, map_add]

lemma pbCoeff_mul (f g : ↥T°) (v : ℕ) :
    pbCoeff (f * g) v = ∑ p ∈ Finset.antidiagonal v, pbCoeff f p.1 * pbCoeff g p.2 := by
  apply Subtype.ext
  push_cast [pbCoeff_coe]
  show PowerSeries.coeff v
      ((f : PowerSeries.Restricted R 1).1 * (g : PowerSeries.Restricted R 1).1)
    = ∑ p ∈ Finset.antidiagonal v,
        PowerSeries.coeff p.1 (f : PowerSeries.Restricted R 1).1
        * PowerSeries.coeff p.2 (g : PowerSeries.Restricted R 1).1
  rw [PowerSeries.coeff_mul]

/-- For `ε > 0`, the support of `v ↦ mk_{R_ε} (pbCoeff f v)` is finite (restrictedness sends the
coefficient norms to `0`, so eventually they sit in the `ε`-ball ideal and reduce to `0`). -/
lemma residueCoeff_support_finite (ε : ℝ) (hε : 0 < ε) (f : ↥T°) :
    (Function.support fun v : ℕ =>
      Ideal.Quotient.mk (closedBall_ideal ε hε.le) (pbCoeff f v)).Finite := by
  have h_restr :
      Filter.Tendsto (fun v : ℕ => ‖PowerSeries.coeff v (f : PowerSeries.Restricted R 1).1‖)
        Filter.atTop (nhds 0) := by
    have h := (PowerSeries.isRestricted_iff 1 (f : PowerSeries.Restricted R 1).1).mp
      (f : PowerSeries.Restricted R 1).2
    rw [Nat.cofinite_eq_atTop] at h
    refine h.congr fun v => ?_; simp
  obtain ⟨N, hN⟩ :
      ∃ N, ∀ v ≥ N, ‖PowerSeries.coeff v (f : PowerSeries.Restricted R 1).1‖ ≤ ε := by
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp h_restr ε hε
    refine ⟨N, fun v hv => ?_⟩
    have := hN v hv
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] at this
    exact this.le
  refine Set.Finite.subset (Set.finite_Iio N) ?_
  intro v hv
  simp only [Function.mem_support, ne_eq] at hv
  by_contra hvN
  apply hv
  rw [Ideal.Quotient.eq_zero_iff_mem, mem_closedBall_ideal]
  exact hN v (Nat.le_of_not_lt hvN)

/-- The residue of `f ∈ T°` modulo `R_ε`, as a polynomial in `(R° ⧸ R_ε)[X]`. -/
noncomputable def residuePolynomial_ε (ε : ℝ) (hε : 0 < ε) (f : ↥T°) :
    Polynomial (↥R° ⧸ closedBall_ideal ε hε.le) :=
  ⟨Finsupp.ofSupportFinite
    (fun v => Ideal.Quotient.mk (closedBall_ideal ε hε.le) (pbCoeff f v))
    (residueCoeff_support_finite ε hε f)⟩

@[simp] lemma residuePolynomial_ε_coeff (ε : ℝ) (hε : 0 < ε) (f : ↥T°) (v : ℕ) :
    (residuePolynomial_ε ε hε f).coeff v
      = Ideal.Quotient.mk (closedBall_ideal ε hε.le) (pbCoeff f v) := rfl

@[simp] lemma pbCoeff_zero (v : ℕ) : pbCoeff (0 : ↥T°) v = 0 := by
  apply Subtype.ext
  rw [pbCoeff_coe, ZeroMemClass.coe_zero, show (0 : PowerSeries.Restricted R 1).1 = 0 from rfl,
    map_zero, ZeroMemClass.coe_zero]

@[simp] lemma pbCoeff_one_zero : pbCoeff (1 : ↥T°) 0 = 1 := by
  apply Subtype.ext
  rw [pbCoeff_coe, OneMemClass.coe_one, show (1 : PowerSeries.Restricted R 1).1 = 1 from rfl,
    PowerSeries.coeff_one, if_pos rfl, OneMemClass.coe_one]

@[simp] lemma pbCoeff_one_pos {v : ℕ} (hv : 0 < v) : pbCoeff (1 : ↥T°) v = 0 := by
  apply Subtype.ext
  rw [pbCoeff_coe, OneMemClass.coe_one, show (1 : PowerSeries.Restricted R 1).1 = 1 from rfl,
    PowerSeries.coeff_one, if_neg hv.ne', ZeroMemClass.coe_zero]

lemma residuePolynomial_ε_zero (ε : ℝ) (hε : 0 < ε) :
    residuePolynomial_ε (R := R) ε hε (0 : ↥T°) = 0 := by
  apply Polynomial.ext; intro v
  rw [residuePolynomial_ε_coeff, pbCoeff_zero, map_zero, Polynomial.coeff_zero]

lemma residuePolynomial_ε_one (ε : ℝ) (hε : 0 < ε) :
    residuePolynomial_ε (R := R) ε hε (1 : ↥T°) = 1 := by
  apply Polynomial.ext; intro v
  rw [residuePolynomial_ε_coeff]
  rcases Nat.eq_zero_or_pos v with rfl | hv
  · rw [pbCoeff_one_zero, map_one, Polynomial.coeff_one_zero]
  · rw [pbCoeff_one_pos hv, map_zero, Polynomial.coeff_one, if_neg hv.ne']

lemma residuePolynomial_ε_add (ε : ℝ) (hε : 0 < ε) (f g : ↥T°) :
    residuePolynomial_ε ε hε (f + g)
      = residuePolynomial_ε ε hε f + residuePolynomial_ε ε hε g := by
  apply Polynomial.ext; intro v
  rw [Polynomial.coeff_add, residuePolynomial_ε_coeff, residuePolynomial_ε_coeff,
    residuePolynomial_ε_coeff, pbCoeff_add, map_add]

lemma residuePolynomial_ε_mul (ε : ℝ) (hε : 0 < ε) (f g : ↥T°) :
    residuePolynomial_ε ε hε (f * g)
      = residuePolynomial_ε ε hε f * residuePolynomial_ε ε hε g := by
  apply Polynomial.ext; intro v
  rw [residuePolynomial_ε_coeff, Polynomial.coeff_mul, pbCoeff_mul, map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [map_mul, residuePolynomial_ε_coeff, residuePolynomial_ε_coeff]

/-- **The reduction-mod-`ε` ring hom `τ_ε : T° →+* (R° ⧸ R_ε)[X]`** (ToPR
`Restricted.residueRingHom_ε`, `RestrictedUnits.lean:519`).  Reduces each coefficient of a
power-bounded series `f ∈ T°` modulo the `ε`-ball ideal; only finitely many reductions are
nonzero (restrictedness), so the image is a polynomial.  Domain is the power-bounded subring of
`T = Restricted R 1` (bullet 2: no separate `Restricted R° 1` type). -/
noncomputable def residueRingHom_ε (ε : ℝ) (hε : 0 < ε) :
    ↥T° →+* Polynomial (↥R° ⧸ closedBall_ideal ε hε.le) where
  toFun := residuePolynomial_ε ε hε
  map_zero' := residuePolynomial_ε_zero ε hε
  map_one' := residuePolynomial_ε_one ε hε
  map_add' := residuePolynomial_ε_add ε hε
  map_mul' := residuePolynomial_ε_mul ε hε

@[simp] lemma residueRingHom_ε_apply (ε : ℝ) (hε : 0 < ε) (f : ↥T°) :
    residueRingHom_ε ε hε f = residuePolynomial_ε ε hε f := rfl

/-- **PDF Step 3: `τ_ε(g)` is monic of degree `s`.**  When `g ∈ T°` has degree-`s` coefficient
**equal to `1`** (the PDF's leading-coefficient normalisation) and `ε ∈ (0,1)` dominates every
strictly-higher coefficient, `τ_ε(g)` is monic of degree `s`: its degree-`s` coefficient reduces
to `1`, all higher coefficients reduce to `0` (they lie in `R_ε`), and `R° ⧸ R_ε` is nontrivial
(`1 ∉ R_ε` since `‖1‖ = 1 > ε`).  ToPR proved this inline from `residuePolynomial_ε_coeff` + the
distinguished data. -/
lemma residueRingHom_ε_monic_of_distinguished {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (s : ℕ)
    (g : ↥T°)
    (hcoeff_s : PowerSeries.coeff s (g : PowerSeries.Restricted R 1).1 = 1)
    (hcoeff_gt : ∀ t, s < t → ‖PowerSeries.coeff t (g : PowerSeries.Restricted R 1).1‖ ≤ ε) :
    (residueRingHom_ε ε hε0 g).Monic ∧ (residueRingHom_ε ε hε0 g).degree = s := by
  -- `R_ε` is proper (`1 ∉ R_ε`), so the residue ring is nontrivial.
  have hI_ne : closedBall_ideal ε hε0.le ≠ (⊤ : Ideal ↥R°) := by
    intro h
    have h1 : (1 : ↥R°) ∈ closedBall_ideal ε hε0.le := by rw [h]; exact Submodule.mem_top
    rw [mem_closedBall_ideal, OneMemClass.coe_one, norm_one] at h1
    linarith
  haveI : Nontrivial (↥R° ⧸ closedBall_ideal ε hε0.le) := Ideal.Quotient.nontrivial_iff.mpr hI_ne
  simp only [residueRingHom_ε_apply]
  have hco : ∀ v, (residuePolynomial_ε ε hε0 g).coeff v
      = Ideal.Quotient.mk (closedBall_ideal ε hε0.le) (pbCoeff g v) :=
    residuePolynomial_ε_coeff ε hε0 g
  -- leading coefficient reduces to `1`
  have hps : (residuePolynomial_ε ε hε0 g).coeff s = 1 := by
    rw [hco, show pbCoeff g s = 1 from
      Subtype.ext (by rw [pbCoeff_coe, hcoeff_s, OneMemClass.coe_one]), map_one]
  -- strictly-higher coefficients reduce to `0`
  have hp_gt : ∀ v, s < v → (residuePolynomial_ε ε hε0 g).coeff v = 0 := fun v hv => by
    rw [hco, Ideal.Quotient.eq_zero_iff_mem, mem_closedBall_ideal, pbCoeff_coe]
    exact hcoeff_gt v hv
  have hdeg_le : (residuePolynomial_ε ε hε0 g).degree ≤ (s : WithBot ℕ) :=
    (Polynomial.degree_le_iff_coeff_zero _ _).mpr fun m hm => hp_gt m (by exact_mod_cast hm)
  have hdeg_ge : (s : WithBot ℕ) ≤ (residuePolynomial_ε ε hε0 g).degree :=
    Polynomial.le_degree_of_ne_zero (by rw [hps]; exact one_ne_zero)
  have hdeg : (residuePolynomial_ε ε hε0 g).degree = (s : WithBot ℕ) := le_antisymm hdeg_le hdeg_ge
  have hnd : (residuePolynomial_ε ε hε0 g).natDegree = s :=
    Polynomial.natDegree_eq_of_degree_eq_some hdeg
  refine ⟨?_, hdeg⟩
  show (residuePolynomial_ε ε hε0 g).coeff (residuePolynomial_ε ε hε0 g).natDegree = 1
  rw [hnd]; exact hps

/-! #### Supporting lemmas for the `τ_ε`-division (ported from `ToPR.EuclideanDiv`) -/

section EuclideanLift
namespace Polynomial
variable {A : Type*} [CommRing A]

/-- Euclidean division by a monic polynomial, packaged as an existence statement. -/
lemma exists_div_by_monic [Nontrivial A] {g : A[X]} (hg : g.Monic) (f : A[X]) :
    ∃ q r : A[X], f = q * g + r ∧ r.degree < g.degree := by
  refine ⟨f /ₘ g, f %ₘ g, ?_, degree_modByMonic_lt f hg⟩
  have h := modByMonic_add_div f g
  linear_combination -h

variable (I : Ideal A)

/-- A set-theoretic section of `Polynomial.map (Ideal.Quotient.mk I)`: lift each coefficient via
`Quotient.out`. -/
noncomputable def liftQuot (p : Polynomial (A ⧸ I)) : Polynomial A :=
  ∑ n ∈ p.support, monomial n (Quotient.out (p.coeff n))

@[simp] lemma liftQuot_coeff (p : Polynomial (A ⧸ I)) (n : ℕ) :
    (liftQuot I p).coeff n = if n ∈ p.support then Quotient.out (p.coeff n) else 0 := by
  simp only [liftQuot, finsetSum_coeff, coeff_monomial]
  split_ifs with hn
  · rw [Finset.sum_eq_single n]
    · rw [if_pos rfl]
    · intros m _ hmn; exact if_neg hmn
    · intro h; exact absurd hn h
  · refine Finset.sum_eq_zero fun m hm => ?_
    have hne : m ≠ n := fun h => hn (h ▸ hm)
    exact if_neg hne

lemma liftQuot_map (p : Polynomial (A ⧸ I)) :
    (liftQuot I p).map (Ideal.Quotient.mk I) = p := by
  apply Polynomial.ext; intro n
  rw [coeff_map, liftQuot_coeff]
  by_cases hn : n ∈ p.support
  · rw [if_pos hn]; exact Quotient.out_eq (p.coeff n)
  · rw [if_neg hn, map_zero]
    rw [mem_support_iff, not_not] at hn; exact hn.symm

lemma degree_liftQuot_le (p : Polynomial (A ⧸ I)) : (liftQuot I p).degree ≤ p.degree := by
  refine (degree_sum_le _ _).trans (Finset.sup_le fun n hn => ?_)
  exact (degree_monomial_le n _).trans (le_degree_of_ne_zero (mem_support_iff.mp hn))

end Polynomial
end EuclideanLift

/-- Embed a polynomial over `R°` as an element of `T°` (its coefficients lie in `R°`, hence the
resulting polynomial-as-restricted-series is power-bounded). -/
noncomputable def polyToTeo (p : Polynomial ↥R°) : ↥T° :=
  ⟨Polynomial.toRestricted 1 (p.map (PowerBounded.subring R (S := ℤ)).subtype), by
    refine IsPowerBounded.isPowerBounded_of_norm_le_one ?_
    rw [Restricted.norm_eq, PowerSeries.gaussNorm_eq]
    refine ciSup_le fun v => ?_
    rw [one_pow, mul_one]
    show ‖PowerSeries.coeff v
        ((p.map (PowerBounded.subring R (S := ℤ)).subtype : Polynomial R) : PowerSeries R)‖ ≤ 1
    rw [Polynomial.coeff_coe, Polynomial.coeff_map]
    exact IsPowerBounded.norm_le_one_of_neBot (p.coeff v).2⟩

@[simp] lemma polyToTeo_coe (p : Polynomial ↥R°) :
    (polyToTeo p : PowerSeries.Restricted R 1)
      = Polynomial.toRestricted 1 (p.map (PowerBounded.subring R (S := ℤ)).subtype) := rfl

/-- `τ_ε ∘ polyToTeo = Polynomial.map (mk R_ε)`: applying `τ_ε` to the `T°`-embedding of a
polynomial over `R°` reduces each coefficient modulo `R_ε`. -/
lemma residueRingHom_ε_polyToTeo {ε : ℝ} (hε0 : 0 < ε) (p : Polynomial ↥R°) :
    residueRingHom_ε ε hε0 (polyToTeo p)
      = p.map (Ideal.Quotient.mk (closedBall_ideal ε hε0.le)) := by
  apply Polynomial.ext; intro v
  rw [residueRingHom_ε_apply, residuePolynomial_ε_coeff, Polynomial.coeff_map]
  congr 1
  apply Subtype.ext
  rw [pbCoeff_coe, polyToTeo_coe]
  show PowerSeries.coeff v
      ((p.map (PowerBounded.subring R (S := ℤ)).subtype : Polynomial R) : PowerSeries R)
    = ((p.coeff v : ↥R°) : R)
  rw [Polynomial.coeff_coe, Polynomial.coeff_map]; rfl

/-- Kernel bound: if `τ_ε(h) = 0` then every coefficient of `h` lies in `R_ε`, so `‖h‖ ≤ ε`. -/
lemma norm_le_of_residueRingHom_ε_eq_zero {ε : ℝ} (hε0 : 0 < ε) (h : ↥T°)
    (hh : residueRingHom_ε ε hε0 h = 0) :
    ‖(h : PowerSeries.Restricted R 1)‖ ≤ ε := by
  have hcoeff : ∀ v, ‖PowerSeries.coeff v (h : PowerSeries.Restricted R 1).1‖ ≤ ε := fun v => by
    have h_eq : (residueRingHom_ε ε hε0 h).coeff v = (0 : Polynomial _).coeff v := by rw [hh]
    rw [residueRingHom_ε_apply, residuePolynomial_ε_coeff, Polynomial.coeff_zero,
      Ideal.Quotient.eq_zero_iff_mem, mem_closedBall_ideal, pbCoeff_coe] at h_eq
    exact h_eq
  rw [Restricted.norm_eq, PowerSeries.gaussNorm_eq]
  refine ciSup_le fun v => ?_
  rw [one_pow, mul_one]; exact hcoeff v

/-- Converse direction: if `‖h‖ ≤ ε` then every coefficient lies in `R_ε`, so `τ_ε(h) = 0`. -/
lemma residueRingHom_ε_eq_zero_of_norm_le {ε : ℝ} (hε0 : 0 < ε) (h : ↥T°)
    (hh : ‖(h : PowerSeries.Restricted R 1)‖ ≤ ε) :
    residueRingHom_ε ε hε0 h = 0 := by
  apply Polynomial.ext; intro v
  rw [residueRingHom_ε_apply, residuePolynomial_ε_coeff, Polynomial.coeff_zero,
    Ideal.Quotient.eq_zero_iff_mem, mem_closedBall_ideal, pbCoeff_coe]
  refine le_trans ?_ hh
  have := PowerSeries.le_gaussNorm norm 1 (h : PowerSeries.Restricted R 1).1
    (Restricted.hasGaussNorm 1 (h : PowerSeries.Restricted R 1)) v
  rwa [one_pow, mul_one, ← Restricted.norm_eq] at this

/-- **PDF Lemma 4.11, Step 4 — division modulo `ε` in `T°`** (ToPR
`Restricted.exists_div_by_τε_monic`, `EuclideanDiv.lean:207`).  If `τ_ε(g)` is monic, then every
`f ∈ T°` can be Euclidean-divided by `g` modulo `ε`: there are a quotient `q ∈ T°` and a remainder
polynomial `r` over the base `R` with `deg r < deg τ_ε(g)` such that `‖f - g·q - ↑r‖ ≤ ε`.

This is the engine of `exists_divApprox`: it produces the witnesses `q` and `r` placing
`g·q + ↑r` in `divCarrier g s` (after the monic lemma identifies `deg τ_ε(g) = s`), and the
`ε`-bound is exactly the `ε`-density estimate.  ToPR's domain was `Restricted R° 1`; here
(bullet 2) it is the subring `T° ⊆ T`, with the remainder embedded straight into
`T = Restricted R 1` via `Polynomial.toRestricted`.

ToPR proof sketch (to port): lift the monic `τ_ε(g)`-division in `(R° ⧸ R_ε)[X]` back through the
section `τ_ε`, giving `f - g·q - ↑r ∈ ker τ_ε`, whose elements have norm `≤ ε`
(`norm_le_of_residueRingHom_ε_eq_zero`). -/
lemma exists_div_by_τε_monic {ε : ℝ} (hε0 : 0 < ε)
    [Nontrivial (↥R° ⧸ closedBall_ideal ε hε0.le)]
    (g f : ↥T°) (hτg : (residueRingHom_ε ε hε0 g).Monic) :
    ∃ (q : ↥T°) (r : Polynomial R), r.degree < (residueRingHom_ε ε hε0 g).degree ∧
      ‖(f : PowerSeries.Restricted R 1) - (g : PowerSeries.Restricted R 1)
          * (q : PowerSeries.Restricted R 1) - Polynomial.toRestricted 1 r‖ ≤ ε := by
  -- Euclidean division on the residue side: `τ_ε(f) = Q · τ_ε(g) + Rem`, `deg Rem < deg τ_ε(g)`.
  obtain ⟨Q, Rem, hf_eq, hR_deg⟩ :=
    Polynomial.exists_div_by_monic hτg (residueRingHom_ε ε hε0 f)
  -- Lift `Q`, `Rem` to `R°[X]`; embed the quotient into `T°` and the remainder into `T`.
  refine ⟨polyToTeo (Polynomial.liftQuot (closedBall_ideal ε hε0.le) Q),
    (Polynomial.liftQuot (closedBall_ideal ε hε0.le) Rem).map
      (PowerBounded.subring R (S := ℤ)).subtype, ?_, ?_⟩
  · -- `deg r ≤ deg (liftQuot Rem) ≤ deg Rem < deg τ_ε(g)`.
    exact lt_of_le_of_lt
      ((Polynomial.degree_map_le).trans (Polynomial.degree_liftQuot_le _ Rem)) hR_deg
  · -- The difference is the `T°` element `f - g·q - polyToTeo (liftQuot Rem)`; its `τ_ε` vanishes.
    change ‖((f - g * polyToTeo (Polynomial.liftQuot (closedBall_ideal ε hε0.le) Q)
        - polyToTeo (Polynomial.liftQuot (closedBall_ideal ε hε0.le) Rem) : ↥T°) :
        PowerSeries.Restricted R 1)‖ ≤ ε
    apply norm_le_of_residueRingHom_ε_eq_zero hε0
    rw [map_sub, map_sub, map_mul, residueRingHom_ε_polyToTeo, residueRingHom_ε_polyToTeo,
      Polynomial.liftQuot_map, Polynomial.liftQuot_map, hf_eq]
    ring

/-- **PDF Lemma 4.11, Steps 1,3–5 (the `ε`-approximation), abstract base ring.**
For each `f`, there is `b ∈ divCarrier g s` with `‖-f + b‖ ≤ ε‖f‖`.  Proof plan (PDF `τ_ε`):

* normalise `g` to leading coefficient `1` by `C u`, `u = (coeff_s g)⁻¹` (a unit of norm `1`);
* scale `f` to norm `≤ 1` by `C α`, where `α` is the unit of norm `‖f‖⁻¹` supplied by `hf`
  — the `ext1`-style hypothesis, replacing ToPR's `NormedField` step (cf. comment on `ext1`);
* lift `C u · g`, `C α · f` into `T°`, where `τ_ε(C u · g)` is monic of degree `s`
  (`residueRingHom_ε_monic_of_distinguished`);
* divide modulo `ε` (`exists_div_by_τε_monic`) → `q, r` with `‖C α·f - C u·g·q - ↑r‖ ≤ ε`;
* unscale by `C α⁻¹` (norm `‖f‖`) to land `b = g·q' + ↑r' ∈ divCarrier g s` with the `ε‖f‖` bound. -/
lemma exists_divApprox (g : PowerSeries.Restricted R 1) (hg : ‖g‖ = 1) (s : ℕ)
    (gd : distinguished norm 1 g.1 s) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    (hε_bd : ∀ t, s < t → ‖PowerSeries.coeff t g.1‖ ≤ ε)
    (f : PowerSeries.Restricted R 1) (hf : ∃ a : R, ‖a‖ = ‖f‖⁻¹ ∧ IsUnit a) :
    ∃ b ∈ divCarrier g s, ‖-f + b‖ ≤ ε * ‖f‖ := by
  -- ============================ scaling unit α (Step 5 input) ============================
  obtain ⟨α, hα_norm, hα_unit⟩ := hf
  have hf_pos : 0 < ‖f‖ := by
    have hα_pos : 0 < ‖α‖ := norm_pos_iff.mpr hα_unit.ne_zero
    rw [hα_norm] at hα_pos; exact inv_pos.mp hα_pos
  obtain ⟨A, hA⟩ := hα_unit
  set αinv : R := ((A⁻¹ : Rˣ) : R) with hαinv_def
  have hαinv_α : αinv * α = 1 := by rw [hαinv_def, ← hA]; exact A.inv_mul
  have hαinv_norm : ‖αinv‖ = ‖f‖ := by
    have h1 : ‖α‖ * ‖αinv‖ = 1 := by
      rw [← norm_mul, mul_comm, hαinv_α, norm_one]
    rw [hα_norm] at h1
    exact ((inv_mul_eq_one₀ (ne_of_gt hf_pos)).mp h1).symm
  -- ===================== normalise g to leading coefficient 1 (Step 1) =====================
  have hg1 : ‖PowerSeries.coeff s g.1‖ = 1 := by
    have h : PowerSeries.gaussNorm norm 1 g.1 = ‖PowerSeries.coeff s g.1‖ := gd.norm_eq
    rw [← h, ← Restricted.norm_eq]; exact hg
  obtain ⟨U, hU⟩ := gd.unit
  set u : R := ((U⁻¹ : Rˣ) : R) with hu_def
  have hu_cs : u * PowerSeries.coeff s g.1 = 1 := by rw [hu_def, ← hU]; exact U.inv_mul
  have hu_norm : ‖u‖ = 1 := by
    have : ‖u‖ * ‖PowerSeries.coeff s g.1‖ = 1 := by rw [← norm_mul, hu_cs, norm_one]
    rwa [hg1, mul_one] at this
  set g' : PowerSeries.Restricted R 1 := PowerSeries.Restricted.C 1 u * g with hg'_def
  set f' : PowerSeries.Restricted R 1 := PowerSeries.Restricted.C 1 α * f with hf'_def
  have hg'_cs : PowerSeries.coeff s g'.1 = 1 := by
    rw [hg'_def, PowerSeries.Restricted.coeff_C_mul, hu_cs]
  have hg'_norm : ‖g'‖ = 1 := by
    rw [hg'_def, norm_mul, PowerSeries.Restricted.norm_C, hu_norm, hg, one_mul]
  have hf'_norm : ‖f'‖ = 1 := by
    rw [hf'_def, norm_mul, PowerSeries.Restricted.norm_C, hα_norm,
      inv_mul_cancel₀ (ne_of_gt hf_pos)]
  have hg'_bd : ∀ t, s < t → ‖PowerSeries.coeff t g'.1‖ ≤ ε := fun t ht => by
    rw [hg'_def, PowerSeries.Restricted.coeff_C_mul, norm_mul, hu_norm, one_mul]
    exact hε_bd t ht
  -- ===================== lift g', f' into `T°` and run the division (Steps 3,4) =====================
  have hg'_pb : g' ∈ PowerBounded.subring (PowerSeries.Restricted R 1) (S := ℤ) :=
    IsPowerBounded.isPowerBounded_of_norm_le_one hg'_norm.le
  have hf'_pb : f' ∈ PowerBounded.subring (PowerSeries.Restricted R 1) (S := ℤ) :=
    IsPowerBounded.isPowerBounded_of_norm_le_one hf'_norm.le
  haveI : Nontrivial (↥R° ⧸ closedBall_ideal ε hε0.le) := by
    refine Ideal.Quotient.nontrivial_iff.mpr (fun h => ?_)
    have h1 : (1 : ↥R°) ∈ closedBall_ideal ε hε0.le := by rw [h]; exact Submodule.mem_top
    rw [mem_closedBall_ideal, OneMemClass.coe_one, norm_one] at h1; linarith
  have hmonic := residueRingHom_ε_monic_of_distinguished hε0 hε1 s ⟨g', hg'_pb⟩ hg'_cs hg'_bd
  obtain ⟨qpb, r, hr_deg, hbound⟩ :=
    exists_div_by_τε_monic hε0 ⟨g', hg'_pb⟩ ⟨f', hf'_pb⟩ hmonic.1
  rw [hmonic.2] at hr_deg
  set qT : PowerSeries.Restricted R 1 := (qpb : PowerSeries.Restricted R 1) with hqT_def
  have hX : ‖f' - g' * qT - Polynomial.toRestricted 1 r‖ ≤ ε := hbound
  -- ============================ unscale by `C α⁻¹` (Step 5) ============================
  set q : PowerSeries.Restricted R 1 := PowerSeries.Restricted.C 1 (αinv * u) * qT with hq_def
  set r' : Polynomial R := Polynomial.C αinv * r with hr'_def
  have key : PowerSeries.Restricted.C 1 αinv * (f' - g' * qT - Polynomial.toRestricted 1 r)
      = f - g * q - Polynomial.toRestricted 1 r' := by
    have hCmul : PowerSeries.Restricted.C 1 αinv * PowerSeries.Restricted.C 1 α = 1 := by
      rw [← PowerSeries.Restricted.C_mul, hαinv_α, PowerSeries.Restricted.C_one]
    have htoR : PowerSeries.Restricted.C 1 αinv * Polynomial.toRestricted 1 r
        = Polynomial.toRestricted 1 r' := by
      rw [PowerSeries.Restricted.C_mul_toRestricted, hr'_def]
    rw [hf'_def, hg'_def, hq_def, mul_sub, mul_sub, htoR,
      show PowerSeries.Restricted.C 1 αinv * (PowerSeries.Restricted.C 1 α * f) = f from by
        rw [← mul_assoc, hCmul, one_mul],
      show PowerSeries.Restricted.C 1 αinv * (PowerSeries.Restricted.C 1 u * g * qT)
          = g * (PowerSeries.Restricted.C 1 (αinv * u) * qT) from by
        rw [PowerSeries.Restricted.C_mul 1 αinv u]; ring]
  refine ⟨g * q + Polynomial.toRestricted 1 r', ⟨q, r', ?_, rfl⟩, ?_⟩
  · rw [hr'_def]
    refine lt_of_le_of_lt (le_trans (Polynomial.degree_mul_le _ _) ?_) hr_deg
    calc (Polynomial.C αinv).degree + r.degree ≤ (0 : WithBot ℕ) + r.degree := by
          gcongr; exact Polynomial.degree_C_le
      _ = r.degree := zero_add _
  · rw [show -f + (g * q + Polynomial.toRestricted 1 r')
        = -(PowerSeries.Restricted.C 1 αinv * (f' - g' * qT - Polynomial.toRestricted 1 r))
        from by rw [key]; ring,
      norm_neg, norm_mul, PowerSeries.Restricted.norm_C, hαinv_norm, mul_comm ε]
    exact mul_le_mul_of_nonneg_left hX (norm_nonneg f)

-- as below the hunit is so that we can avoid have the normed field condtion
-- this is because we want to use these when R is not a normed field
-- see discussion below

/-- `divCarrier g s` is dense.  Like `exists_divApprox`, the per-`f` rescaling needs a unit of
norm `‖f‖⁻¹` for each nonzero `f` (the `ext1`-style hypothesis `hunit`); the `f = 0` case is
handled directly by `b = 0`. -/
lemma divSubgroup_dense (g : PowerSeries.Restricted R 1) (hg : ‖g‖ = 1) (s : ℕ)
    (gd : distinguished norm 1 g.1 s)
    (hunit : ∀ f : PowerSeries.Restricted R 1, f ≠ 0 → ∃ a : R, ‖a‖ = ‖f‖⁻¹ ∧ IsUnit a) :
    Dense (divCarrier g s) := by
  suffices h_eps_dense :
      ∃ ε, 0 < ε ∧ ε < 1 ∧ SeminormedAddGroup.epsilonDense (divSubgroup g s) ε by
    obtain ⟨ε, hε1, hε2, h⟩ := h_eps_dense
    exact SeminormedAddGroup.dense_epsilonDense _ _ hε1 hε2 h
  -- `‖g‖ = 1` is taken as a hypothesis (PDF Step 1, the `|g| = 1` normalisation, is discharged
  -- by the caller — see `weierstrassDivision_existance`). With `gd` it forces `‖coeff s g.1‖ = 1`.
  have hg1 : ‖PowerSeries.coeff s g.1‖ = 1 := by
    -- `gd.norm_eq : gaussNorm norm 1 g.1 = ‖coeff s g.1‖` (definitionally) and
    -- `Restricted.norm_eq : ‖g‖ = gaussNorm norm 1 g.1`.
    have h : PowerSeries.gaussNorm norm 1 g.1 = ‖PowerSeries.coeff s g.1‖ := gd.norm_eq
    rw [← h, ← Restricted.norm_eq]; exact hg
  -- PDF Step 2: extract `ε ∈ (0,1)` dominating every higher coefficient norm of `g`.
  obtain ⟨ε, hε0, hε1, hε_bd⟩ := exists_epsilon_of_distinguished g s gd hg1
  refine ⟨ε, hε0, hε1, ?_⟩
  -- ε-density of `divSubgroup g s`: for each `f` produce `b ∈ B` with `‖-f + b‖ ≤ ε‖f‖`.
  -- PDF Steps 3–5 are packaged in `exists_divApprox`.
  intro f
  by_cases hf0 : f = 0
  · subst hf0; exact ⟨0, by simp⟩
  · obtain ⟨b, hb_mem, hb_le⟩ := exists_divApprox g hg s gd hε0 hε1 hε_bd f (hunit f hf0)
    exact ⟨⟨b, hb_mem⟩, hb_le⟩

lemma Restricted.coeff_continuous (v : ℕ) :
    Continuous fun f : PowerSeries.Restricted R 1 => PowerSeries.coeff v f.1 := by
  refine Metric.continuous_iff.mpr fun f ε hε => ⟨ε, hε, fun g hg => ?_⟩
  rw [dist_eq_norm, ← LinearMap.map_sub (PowerSeries.coeff v) g.1 f.1]
  have := PowerSeries.le_gaussNorm norm 1 (g - f).1 (Restricted.hasGaussNorm 1 (g - f)) v
  rw [one_pow, mul_one, ← Restricted.norm_eq] at this
  exact this.trans_lt (by rwa [← dist_eq_norm])

/-- The set of `f ∈ T` whose coefficients above degree `s` all vanish is closed.
This is precisely the image of `Polynomial.toRestricted 1` on polynomials of degree `< s`. -/
lemma polySubspace_isClosed (s : ℕ) :
    IsClosed {f : PowerSeries.Restricted R 1 | ∀ v, s ≤ v → PowerSeries.coeff v f.1 = 0} := by
  refine IsSeqClosed.isClosed fun f_seq f hf_mem hf_lim v hv => ?_
  have h_lim : Filter.Tendsto (fun n => PowerSeries.coeff v (f_seq n).1)
      Filter.atTop (nhds (PowerSeries.coeff v f.1)) :=
    ((Restricted.coeff_continuous v).tendsto _).comp hf_lim
  have h_zero : (fun n => PowerSeries.coeff v (f_seq n).1) = (fun _ => 0) :=
    funext fun n => hf_mem n v hv
  rw [h_zero] at h_lim
  exact tendsto_nhds_unique h_lim tendsto_const_nhds

lemma divSubgroup_closed (g : PowerSeries.Restricted R 1) (s : ℕ) (hg : distinguished norm 1 g.1 s) :
    IsClosed (divCarrier g s) := by
  have hg' : 0 < ‖g‖ := norm_pos_iff.mpr (ne_of_apply_ne Subtype.val hg.ne_zero)
  refine IsSeqClosed.isClosed ?_
  intro b_seq b hb_mem hb_lim
  choose q_seq r_seq hr_seq hb_eq using hb_mem
  have diff_eq : ∀ n m, b_seq n - b_seq m =
      g * (q_seq n - q_seq m) + Polynomial.toRestricted 1 (r_seq n - r_seq m) := fun n m => by
    rw [hb_eq n, hb_eq m, Polynomial.toRestricted_sub, mul_sub]
    abel
  set diff_deg : ∀ n m, (r_seq n - r_seq m).degree < s := fun n m =>
    lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt (hr_seq n) (hr_seq m))
  have hq_cauchy : CauchySeq q_seq := by
    refine Metric.cauchySeq_iff.mpr fun ε hε => ?_
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hb_lim.cauchySeq (ε * ‖g‖) (mul_pos hε hg')
    refine ⟨N, fun n hn m hm => ?_⟩
    rw [dist_eq_norm]
    calc ‖q_seq n - q_seq m‖ ≤ ‖g‖⁻¹ * ‖b_seq n - b_seq m‖ := weierstrassDivision_bounds_q g s hg
          (b_seq n - b_seq m) (q_seq n - q_seq m) (r_seq n - r_seq m) (diff_deg n m) (diff_eq n m)
      _ < ‖g‖⁻¹ * (ε * ‖g‖) := by
          have : ‖b_seq n - b_seq m‖ < ε * ‖g‖ := by
            simpa [dist_eq_norm] using hN n hn m hm
          gcongr
      _ = ε := by field_simp
  have hr_cauchy : CauchySeq (fun n => Polynomial.toRestricted 1 (r_seq n)) := by
    refine Metric.cauchySeq_iff.mpr fun ε hε => ?_
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hb_lim.cauchySeq ε hε
    refine ⟨N, fun n hn m hm => ?_⟩
    have := weierstrassDivision_bounds_r g s hg (b_seq n - b_seq m)
      (q_seq n - q_seq m) (r_seq n - r_seq m) (diff_deg n m) (diff_eq n m)
    rw [Polynomial.toRestricted_sub] at this
    rw [dist_eq_norm]
    exact this.trans_lt (by simpa [dist_eq_norm] using hN n hn m hm)
  obtain ⟨q, hq_lim⟩ := cauchySeq_tendsto_of_complete hq_cauchy
  obtain ⟨r_T, hr_T_lim⟩ := cauchySeq_tendsto_of_complete hr_cauchy
  have h_r_T_in : r_T ∈
      {f : PowerSeries.Restricted _ 1 | ∀ v, s ≤ v → PowerSeries.coeff v f.1 = 0} := by
    refine (polySubspace_isClosed s).mem_of_tendsto hr_T_lim
      (Filter.Eventually.of_forall fun n v hv => ?_)
    simp only [Polynomial.toRestricted, Polynomial.coeff_coe]
    exact Polynomial.coeff_eq_zero_of_degree_lt ((hr_seq n).trans_le (mod_cast hv))
  let r : Polynomial R := ∑ v ∈ Finset.range s, Polynomial.monomial v (PowerSeries.coeff v r_T.1)

  -- almost certainly a better way to do this
  have hr_coeff : ∀ v, r.coeff v = if v < s then PowerSeries.coeff v r_T.1 else 0 := fun v => by
    simp only [r, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
    split_ifs with hv
    · rw [Finset.sum_eq_single v]
      · simp
      · intros; simp_all
      · simp [Finset.mem_range, hv]
    · refine Finset.sum_eq_zero fun w hw => ?_
      simp only [Finset.mem_range] at hw
      have : w ≠ v := fun h => hv (h ▸ hw)
      simp [this]
  have hr_deg : r.degree < s := by
    refine (Polynomial.degree_lt_iff_coeff_zero _ _).mpr fun v hv => ?_
    rw [hr_coeff, if_neg (not_lt.mpr hv)]
  have hr_toR : Polynomial.toRestricted 1 r = r_T := by
    apply Subtype.ext
    ext v
    show PowerSeries.coeff v r.toPowerSeries = PowerSeries.coeff v r_T.1
    rw [Polynomial.coeff_coe, hr_coeff]
    split_ifs with hv
    · rfl
    · exact (h_r_T_in v (not_lt.mp hv)).symm
  -- the above can probably be extracted; will be a similar result to Restricted.monomial_partial_sums_coeff

  refine ⟨q, r, hr_deg, ?_⟩
  rw [hr_toR]
  exact tendsto_nhds_unique hb_lim (by simpa [funext hb_eq] using (hq_lim.const_mul g).add hr_T_lim)

end DenseSet

lemma weierstrassDivision_existance' (g : PowerSeries.Restricted R 1) (hg : ‖g‖ = 1) (s : ℕ)
    (gd : distinguished norm 1 g.1 s) (f : PowerSeries.Restricted R 1)
    (hunit : ∀ f : PowerSeries.Restricted R 1, f ≠ 0 → ∃ a : R, ‖a‖ = ‖f‖⁻¹ ∧ IsUnit a) :
    ∃ q : PowerSeries.Restricted R 1, ∃ r : Polynomial R, Polynomial.degree r < s ∧
    f = g * q + (Polynomial.toRestricted 1 r) := by
  have : divCarrier g s = Set.univ := by
    rw [← (divSubgroup_closed g s gd).closure_eq, (divSubgroup_dense g hg s gd hunit).closure_eq]
  obtain ⟨q, r, hr, hf_eq⟩ := this ▸ Set.mem_univ f
  exact ⟨q, r, hr, hf_eq⟩

lemma ext1 (g : PowerSeries.Restricted R 1) (s : ℕ)
    (gd : distinguished norm 1 g.1 s) (a : R) (h : ‖a‖ = ‖g‖⁻¹ ∧ IsUnit a) :
    distinguished norm 1 (PowerSeries.Restricted.C 1 a * g).1 s := by
  obtain ⟨ha1, ha2⟩ := h
  refine { unit := ?_, norm_eq := ?_, norm_max := ?_ }
  · -- `coeff s (C a · g) = a · coeff s g`, a product of units.
    show IsUnit (PowerSeries.coeff s (PowerSeries.Restricted.C 1 a * g).1)
    rw [PowerSeries.Restricted.coeff_C_mul]
    exact ha2.mul gd.unit
  · -- `‖C a · g‖ = ‖a‖·‖g‖` and `‖coeff s (C a · g)‖ = ‖a‖·‖coeff s g‖`; reduce to `gd.norm_eq`.
    show PowerSeries.gaussNorm norm 1 (PowerSeries.Restricted.C 1 a * g).1
        = ‖PowerSeries.coeff s (PowerSeries.Restricted.C 1 a * g).1‖
    rw [← Restricted.norm_eq, norm_mul, PowerSeries.Restricted.norm_C,
      PowerSeries.Restricted.coeff_C_mul, norm_mul]
    congr 1
    rw [Restricted.norm_eq]; exact gd.norm_eq
  · -- multiplying every coefficient by the unit `a` (norm `> 0`) preserves the strict maximiser.
    intro t ht
    show ‖PowerSeries.coeff t (PowerSeries.Restricted.C 1 a * g).1‖
        < ‖PowerSeries.coeff s (PowerSeries.Restricted.C 1 a * g).1‖
    rw [PowerSeries.Restricted.coeff_C_mul, PowerSeries.Restricted.coeff_C_mul, norm_mul, norm_mul]
    exact mul_lt_mul_of_pos_left (gd.norm_max t ht) (norm_pos_iff.mpr ha2.ne_zero)


/-
-- The following is a conceptual proof of contra using the blueprint proof
-- this adds an assumption I would need to follow through
-- Note instead of reducing R_ε... I should probably fix it to reduce on the actual top nil set

/-- **`contra` via the PDF blueprint**, given a scaling unit (`hunit`).  Following PDF Lemma 4.9:
normalise `g` to `g'' = C(coeff_s g)⁻¹·g` (leading coefficient `1`, norm `1`); scale the equation
by a unit `α` of norm `M⁻¹` (`M = max{‖g·q‖,‖↑r‖}`) so that `f₁ = g''·q₁ + ↑r₁` has
`max{‖g''·q₁‖,‖↑r₁‖} = 1` and `‖f₁‖ < 1`; reduce modulo `R_ε` with `ε = max(ε₀,‖f₁‖)` (so `τ_ε(g'')`
is monic of degree `s` and `τ_ε(f₁) = 0`).  Then `0 = τ_ε(g'')·τ_ε(q₁) + τ_ε(↑r₁)` with
`deg τ_ε(↑r₁) < s`, and monic Euclidean uniqueness forces `τ_ε(q₁) = τ_ε(↑r₁) = 0`, i.e.
`‖q₁‖, ‖↑r₁‖ ≤ ε < 1` — contradicting `max{‖g''·q₁‖,‖↑r₁‖} = 1`. -/
lemma contra' (g : PowerSeries.Restricted R 1) (s : ℕ)
    (hg : distinguished norm 1 g.1 s) (f q : PowerSeries.Restricted R 1) (r : Polynomial R)
    (hr : Polynomial.degree r < s) (hf : f = g * q + Polynomial.toRestricted 1 r)
    (hf_lt : ‖f‖ < max ‖g * q‖ ‖Polynomial.toRestricted 1 r‖)
    (hunit : ∃ a : R, ‖a‖ = (max ‖g * q‖ ‖Polynomial.toRestricted 1 r‖)⁻¹ ∧ IsUnit a) :
    False := by
  set M := max ‖g * q‖ ‖Polynomial.toRestricted 1 r‖ with hM_def
  have hM_pos : 0 < M := lt_of_le_of_lt (norm_nonneg f) hf_lt
  obtain ⟨α, hα_norm, hα_unit⟩ := hunit
  -- `coeff_s g` is a unit `U`; set `β = ↑U⁻¹`, `g'' = C β · g`.
  obtain ⟨U, hU⟩ := hg.unit
  have hg_pos : 0 < ‖g‖ := norm_pos_iff.mpr (ne_of_apply_ne Subtype.val hg.ne_zero)
  have h_coeff_s_g : ‖PowerSeries.coeff s g.1‖ = ‖g‖ := by
    have h : PowerSeries.gaussNorm norm 1 g.1 = ‖PowerSeries.coeff s g.1‖ := hg.norm_eq
    rw [← h, ← Restricted.norm_eq]
  have hUval_norm : ‖((U : Rˣ) : R)‖ = ‖g‖ := by rw [hU]; exact h_coeff_s_g
  have hβ_norm : ‖((U⁻¹ : Rˣ) : R)‖ = ‖g‖⁻¹ := by
    have h2 : ‖g‖ * ‖((U⁻¹ : Rˣ) : R)‖ = 1 := by
      rw [← hUval_norm, ← norm_mul, U.mul_inv, norm_one]
    field_simp [ne_of_gt hg_pos]; rw [mul_comm]; exact h2
  set g'' := PowerSeries.Restricted.C 1 ((U⁻¹ : Rˣ) : R) * g with hg''_def
  set q₁ := PowerSeries.Restricted.C 1 (α * ((U : Rˣ) : R)) * q with hq₁_def
  set r₁ := Polynomial.C α * r with hr₁_def
  set f₁ := PowerSeries.Restricted.C 1 α * f with hf₁_def
  -- Distinguishedness, coeff and norm of `g''` (via `ext1`).
  have hgd'' : distinguished norm 1 g''.1 s := ext1 g s hg _ ⟨hβ_norm, U⁻¹.isUnit⟩
  have hg''_cs : PowerSeries.coeff s g''.1 = 1 := by
    rw [hg''_def, PowerSeries.Restricted.coeff_C_mul, ← hU]; exact U.inv_mul
  have hg''1 : ‖PowerSeries.coeff s g''.1‖ = 1 := by rw [hg''_cs, norm_one]
  have hg''_norm : ‖g''‖ = 1 := by
    rw [hg''_def, norm_mul, PowerSeries.Restricted.norm_C, hβ_norm,
      inv_mul_cancel₀ (ne_of_gt hg_pos)]
  -- The scaled equation `f₁ = g'' · q₁ + ↑r₁`.
  have hβU : PowerSeries.Restricted.C 1 ((U⁻¹ : Rˣ) : R)
        * PowerSeries.Restricted.C 1 (α * ((U : Rˣ) : R))
      = PowerSeries.Restricted.C 1 α := by
    rw [← PowerSeries.Restricted.C_mul]; congr 1
    rw [show ((U⁻¹ : Rˣ) : R) * (α * ((U : Rˣ) : R)) = α * (((U⁻¹ : Rˣ) : R) * ((U : Rˣ) : R))
      from by ring, U.inv_mul, mul_one]
  have h_eq1 : f₁ = g'' * q₁ + Polynomial.toRestricted 1 r₁ := by
    rw [hf₁_def, hf, hg''_def, hq₁_def, hr₁_def, ← PowerSeries.Restricted.C_mul_toRestricted, mul_add]
    congr 1
    rw [show PowerSeries.Restricted.C 1 ((U⁻¹ : Rˣ) : R) * g
          * (PowerSeries.Restricted.C 1 (α * ((U : Rˣ) : R)) * q)
        = (PowerSeries.Restricted.C 1 ((U⁻¹ : Rˣ) : R)
            * PowerSeries.Restricted.C 1 (α * ((U : Rˣ) : R))) * (g * q) from by ring, hβU]
  -- Norms of the scaled pieces.
  have hq₁_norm : ‖q₁‖ = M⁻¹ * ‖g * q‖ := by
    rw [hq₁_def, norm_mul, PowerSeries.Restricted.norm_C, norm_mul, hα_norm, hUval_norm,
      norm_mul g q]; ring
  have hg''q₁_norm : ‖g'' * q₁‖ = M⁻¹ * ‖g * q‖ := by
    rw [norm_mul, hg''_norm, one_mul, hq₁_norm]
  have hr₁_norm : ‖Polynomial.toRestricted 1 r₁‖ = M⁻¹ * ‖Polynomial.toRestricted 1 r‖ := by
    rw [hr₁_def, ← PowerSeries.Restricted.C_mul_toRestricted, norm_mul,
      PowerSeries.Restricted.norm_C, hα_norm]
  have hf₁_norm : ‖f₁‖ = M⁻¹ * ‖f‖ := by
    rw [hf₁_def, norm_mul, PowerSeries.Restricted.norm_C, hα_norm]
  have hf₁_lt : ‖f₁‖ < 1 := by
    rw [hf₁_norm]
    calc M⁻¹ * ‖f‖ < M⁻¹ * M := mul_lt_mul_of_pos_left hf_lt (inv_pos.mpr hM_pos)
      _ = 1 := inv_mul_cancel₀ (ne_of_gt hM_pos)
  have hmax1 : max ‖g'' * q₁‖ ‖Polynomial.toRestricted 1 r₁‖ = 1 := by
    rw [hg''q₁_norm, hr₁_norm, ← mul_max_of_nonneg _ _ (by positivity : (0 : ℝ) ≤ M⁻¹), ← hM_def,
      inv_mul_cancel₀ (ne_of_gt hM_pos)]
  have hg''q₁_le : ‖g'' * q₁‖ ≤ 1 := (le_max_left _ _).trans_eq hmax1
  have hr₁_le : ‖Polynomial.toRestricted 1 r₁‖ ≤ 1 := (le_max_right _ _).trans_eq hmax1
  -- `ε = max(ε₀, ‖f₁‖) ∈ (0,1)`, dominating higher coeffs of `g''` and `‖f₁‖`.
  obtain ⟨ε₀, hε₀0, hε₀1, hε₀_bd⟩ := exists_epsilon_of_distinguished g'' s hgd'' hg''1
  set ε := max ε₀ ‖f₁‖ with hε_def
  have hε0' : 0 < ε := lt_of_lt_of_le hε₀0 (le_max_left _ _)
  have hε1' : ε < 1 := max_lt hε₀1 hf₁_lt
  have hg''_bd : ∀ t, s < t → ‖PowerSeries.coeff t g''.1‖ ≤ ε := fun t ht =>
    (hε₀_bd t ht).trans (le_max_left _ _)
  -- Lift to `T°`.
  have hg''_pb : g'' ∈ PowerBounded.subring (PowerSeries.Restricted R 1) (S := ℤ) :=
    IsPowerBounded.isPowerBounded_of_norm_le_one hg''_norm.le
  have hr₁_pb : Polynomial.toRestricted 1 r₁
      ∈ PowerBounded.subring (PowerSeries.Restricted R 1) (S := ℤ) :=
    IsPowerBounded.isPowerBounded_of_norm_le_one hr₁_le
  have hf₁_pb : f₁ ∈ PowerBounded.subring (PowerSeries.Restricted R 1) (S := ℤ) :=
    IsPowerBounded.isPowerBounded_of_norm_le_one hf₁_lt.le
  have hq₁_pb : q₁ ∈ PowerBounded.subring (PowerSeries.Restricted R 1) (S := ℤ) :=
    IsPowerBounded.isPowerBounded_of_norm_le_one
      (by rw [hq₁_norm, ← hg''q₁_norm]; exact hg''q₁_le)
  set gpb : ↥T° := ⟨g'', hg''_pb⟩
  set qpb : ↥T° := ⟨q₁, hq₁_pb⟩
  set rpb : ↥T° := ⟨Polynomial.toRestricted 1 r₁, hr₁_pb⟩
  set fpb : ↥T° := ⟨f₁, hf₁_pb⟩
  -- `τ_ε(gpb)` monic of degree `s`; `τ_ε(fpb) = 0`.
  obtain ⟨hmonic, hdeg⟩ := residueRingHom_ε_monic_of_distinguished hε0' hε1' s gpb hg''_cs hg''_bd
  have hτf1 : residueRingHom_ε ε hε0' fpb = 0 :=
    residueRingHom_ε_eq_zero_of_norm_le hε0' fpb (le_max_right _ _)
  have h_eq1p : fpb = gpb * qpb + rpb := Subtype.ext h_eq1
  rw [h_eq1p, map_add, map_mul] at hτf1
  -- Remainder degree `< s`.
  have hr₁_deg : r₁.degree < (s : WithBot ℕ) := by
    rw [hr₁_def]
    refine lt_of_le_of_lt (le_trans (Polynomial.degree_mul_le _ _) ?_) hr
    calc (Polynomial.C α).degree + r.degree ≤ (0 : WithBot ℕ) + r.degree := by
          gcongr; exact Polynomial.degree_C_le
      _ = r.degree := zero_add _
  have hRem_deg : (residueRingHom_ε ε hε0' rpb).degree < (residueRingHom_ε ε hε0' gpb).degree := by
    rw [hdeg]
    refine (Polynomial.degree_lt_iff_coeff_zero _ s).mpr fun m hm => ?_
    rw [residueRingHom_ε_apply, residuePolynomial_ε_coeff, Ideal.Quotient.eq_zero_iff_mem,
      mem_closedBall_ideal, pbCoeff_coe]
    have hz : PowerSeries.coeff m (rpb : PowerSeries.Restricted R 1).1 = 0 := by
      show PowerSeries.coeff m (Polynomial.toRestricted 1 r₁).1 = 0
      rw [show (Polynomial.toRestricted 1 r₁).1 = (r₁ : PowerSeries R) from rfl, Polynomial.coeff_coe]
      exact Polynomial.coeff_eq_zero_of_degree_lt
        (lt_of_lt_of_le hr₁_deg (by exact_mod_cast hm))
    rw [hz, norm_zero]; exact hε0'.le
  -- Monic Euclidean uniqueness: `τ_ε(qpb) = 0` and `τ_ε(rpb) = 0`.
  have huniq := Polynomial.div_modByMonic_unique (residueRingHom_ε ε hε0' qpb)
    (residueRingHom_ε ε hε0' rpb) hmonic ⟨(add_comm _ _).trans hτf1, hRem_deg⟩
  have hQ0 : residueRingHom_ε ε hε0' qpb = 0 := by
    rw [Polynomial.zero_divByMonic] at huniq; exact huniq.1.symm
  have hR0 : residueRingHom_ε ε hε0' rpb = 0 := by
    rw [Polynomial.zero_modByMonic] at huniq; exact huniq.2.symm
  -- Both scaled pieces then have norm `≤ ε < 1`, contradicting `max = 1`.
  have hq₁_le_ε : ‖g'' * q₁‖ ≤ ε := by
    rw [hg''q₁_norm, ← hq₁_norm]
    exact norm_le_of_residueRingHom_ε_eq_zero hε0' qpb hQ0
  have hr₁_le_ε : ‖Polynomial.toRestricted 1 r₁‖ ≤ ε :=
    norm_le_of_residueRingHom_ε_eq_zero hε0' rpb hR0
  have h1ε : (1 : ℝ) ≤ ε := hmax1 ▸ max_le hq₁_le_ε hr₁_le_ε
  exact absurd h1ε (not_le.mpr hε1')

-/

-- h will be satisfied when R is a field
-- since we can just take the inverse of the element t that attains the gaussNorm of g
-- but we do not want the assumption that R is a normedfield
-- because we want to directly apply this lemma when R = MvRestricted ...
-- we can write a lemma giving this statement but need to think what it will look like
-- probably of the form PowerSeries (MvRestricted R ...) with R normed field

-- I should porbably package hunit and h together
-- since g is not 0 so we can just use hunit
-- and hunit can be proved if R is a field
-- or when R = MvPowerSeries S ... and S is a field

lemma weierstrassDivision_existance (g : PowerSeries.Restricted R 1) (s : ℕ)
    (gd : distinguished norm 1 g.1 s) (f : PowerSeries.Restricted R 1)
    (h : ∃ a : R, ‖a‖ = ‖g‖⁻¹ ∧ IsUnit a)
    (hunit : ∀ f : PowerSeries.Restricted R 1, f ≠ 0 → ∃ a : R, ‖a‖ = ‖f‖⁻¹ ∧ IsUnit a) :
    ∃ q : PowerSeries.Restricted R 1, ∃ r : Polynomial R, Polynomial.degree r < s ∧
    f = g * q + (Polynomial.toRestricted 1 r) := by
  obtain ⟨a, ha⟩ := h
  have : ‖PowerSeries.Restricted.C 1 a * g‖ = 1 := by
    rw [norm_mul]
    have : ‖PowerSeries.Restricted.C 1 a‖ = ‖a‖ := PowerSeries.Restricted.norm_C 1 a
    simp [this, ha]
    -- note the below has been used quite a bit
    -- so I should really extract it as its own API lemma
    -- will be very helpful
    have : 0 < ‖g‖:= norm_pos_iff.mpr (ne_of_apply_ne Subtype.val gd.ne_zero)
    grind
  obtain ⟨q₀, r₀, hr₀, hf₀⟩ := weierstrassDivision_existance'
    (PowerSeries.Restricted.C 1 a * g) this s (ext1 g s gd a ha) f hunit
  use PowerSeries.Restricted.C 1 a * q₀, r₀, hr₀
  grind


lemma weierstrassDivision_uniqueness (g : PowerSeries.Restricted R 1) (s : ℕ)
    (gd : distinguished norm 1 g.1 s) (f : PowerSeries.Restricted R 1)
    (h : ∃ a : R, ‖a‖ = ‖g‖⁻¹  ∧ IsUnit a)
    (hunit : ∀ f : PowerSeries.Restricted R 1, f ≠ 0 → ∃ a : R, ‖a‖ = ‖f‖⁻¹ ∧ IsUnit a) :
    ∃! q : PowerSeries.Restricted R 1,
    ∃! r : Polynomial R, Polynomial.degree r < s ∧ f = g * q + (Polynomial.toRestricted 1 r) := by
  obtain ⟨q₀, r₀, hr₀, hf₀⟩ := weierstrassDivision_existance g s gd f h hunit
  refine ⟨q₀, ⟨r₀, ⟨hr₀, hf₀⟩, ?_⟩, ?_⟩
  · rintro r' ⟨hr', hf'⟩
    exact Polynomial.coe_inj.mp (congr_arg Subtype.val (add_left_cancel (hf'.symm.trans hf₀)))
  · rintro q' ⟨r', ⟨hr', hf'⟩, _⟩
    have : 0 = g * (q' - q₀) + Polynomial.toRestricted 1 (r' - r₀) := by
      have h : g * q' - g * q₀ + (Polynomial.toRestricted 1 r' - Polynomial.toRestricted 1 r₀)
          = (g * q' + Polynomial.toRestricted 1 r') - (g * q₀ + Polynomial.toRestricted 1 r₀) := by
        abel
      rw [mul_sub, Polynomial.toRestricted_sub, h, hf'.symm.trans hf₀, sub_self]
    have h_bd := weierstrassDivision_bounds_q g s gd 0 (q' - q₀) (r' - r₀)
      (lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt hr' hr₀)) this
    simp only [norm_zero, mul_zero, norm_le_zero_iff] at h_bd
    grind

-- I then want to pull everything across to MvPowerSeries
-- e.g. do this for Restricted (MvRestricted ...)
-- then pass across to MvRestricted via iso
-- then scale up c's by the same logic as in hunit
-- e.g. when there exists values that can be used


end WeierstrassDivision
