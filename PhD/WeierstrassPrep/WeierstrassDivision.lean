import PhD.ToPR.RestrictedIso
import PhD.ToPR.GaussNorm
import PhD.ToPR.MvGaussNorm
import PhD.ToPR.Restricted
import PhD.ToPR.MvRestricted

import PhD.WeierstrassPrep.Restricted_powerbounded_topnil
import PhD.WeierstrassPrep.EpsilonDense
import PhD.WeierstrassPrep.ResPoly
import PhD.WeierstrassPrep.ResC
import PhD.WeierstrassPrep.idealBalls
import PhD.WeierstrassPrep.Polylift

section Distinguished

variable {R : Type*} [Semiring R] (v : R → ℝ) (c : ℝ) (f : PowerSeries R) (s : ℕ)

def coeff_isUnit : Prop := IsUnit (PowerSeries.coeff s f)

def norm_eq : Prop := PowerSeries.gaussNorm v c f = v (PowerSeries.coeff s f)

def norm_max_achiever : Prop :=
  ∀ t, s < t → v (PowerSeries.coeff t f) < v (PowerSeries.coeff s f)

structure distinguished [Semiring R] (c : ℝ) (f : PowerSeries R) (s : ℕ) : Prop where
  unit : coeff_isUnit f s
  norm_eq : norm_eq v c f s
  norm_max : norm_max_achiever v f s

variable {v} {c} {f} {s} in
/-- `g ≠ 0` when `g` is distinguished of degree `s`-/
lemma distinguished.ne_zero [Nontrivial R] (hg : distinguished v c f s) : f ≠ 0 := by
  by_contra
  exact hg.unit.ne_zero (by grind)

variable {S : Type*} [Nontrivial S] [NormedRing S] (g : PowerSeries S)

variable {c} {g} {s} in
lemma distinguished.norm_pos (hg : distinguished norm c g s) (hc : 0 < c)
    (hbd : PowerSeries.HasGaussNorm norm c g) : 0 < PowerSeries.gaussNorm norm c g :=
  PowerSeries.gaussNorm_pos norm c g (hg.ne_zero) norm_zero norm_nonneg (by aesop) hc hbd

variable [IsUltrametricDist S] [StrongPos (fun (_ : Unit) ↦ c)]

-- not super sure I like how this has been set up ... maybe I need to make a section for distinguished
-- powerseries in normed rings
-- or specifically in restricted power series
-- e.g. can change to ‖‖ which may adjust some proofs

variable {c} {s} in
lemma distinguished.norm_pos' {l : PowerSeries.Restricted S c} (hl : distinguished norm c l.1 s)
    (hc : 0 < c) : 0 < ‖l‖ :=
  distinguished.norm_pos hl hc (Restricted.hasGaussNorm c l)

end Distinguished

section WeierstrassDivision

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
-- do when I clean up Restricted and MvRestricted
local instance : NormOneClass (PowerSeries.Restricted R 1) where
  norm_one := by
    rw [← PowerSeries.Restricted.C_one (S := R) 1, PowerSeries.Restricted.norm_C, norm_one]

local instance {S : Type*} [NormedCommRing S] [IsUltrametricDist S] :
    NonarchimedeanRing S where
  is_nonarchimedean := (IsUltrametricDist.nonarchimedeanAddGroup).is_nonarchimedean

-- names of instances was causing problems
local instance blah (S : Type*) [Ring S] [TopologicalSpace S] [NonarchimedeanRing S] :
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

-- not cleaning until I move up Contra' and decide what I am doing with that
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
  have : ‖f‖ < ‖q‖ * ‖g‖ := by
    suffices h : (0 : ℝ) < ‖g‖ by
      have := mul_lt_mul_of_pos_right (not_le.mp this) h
      field_simp at this
      simpa [mul_comm]
    exact norm_pos_iff.mpr (ne_of_apply_ne Subtype.val hg.ne_zero)
  rw [← norm_mul, mul_comm] at this
  exact contra g s hg f q r hr hf (lt_max_iff.mpr (Or.inl this))

lemma weierstrassDivision_bounds_r (g : PowerSeries.Restricted R 1) (s : ℕ)
    (hg : distinguished norm 1 g.1 s) (f : PowerSeries.Restricted R 1)
    (q : PowerSeries.Restricted R 1) (r : Polynomial R) (hr : Polynomial.degree r < s)
    (hf : f = g * q + (Polynomial.toRestricted 1 r)) : ‖(Polynomial.toRestricted 1 r)‖ ≤ ‖f‖ := by
  by_contra
  exact contra g s hg f q r hr hf (lt_max_iff.mpr (Or.inr (not_le.mp this)))

end bounds

section DenseSet

/-- The candidate set `B = { g * q + ↑r : q ∈ T, r ∈ S[X] with deg r < s }`. -/
abbrev exists_set (g : PowerSeries.Restricted R 1) (s : ℕ) :
    Set (PowerSeries.Restricted R 1) :=
  {f | ∃ q, ∃ r : Polynomial R, Polynomial.degree r < s ∧ f = g * q + Polynomial.toRestricted 1 r}

def exists_subgroup (g : PowerSeries.Restricted R 1) (s : ℕ) :
    AddSubgroup (PowerSeries.Restricted R 1) where
  carrier := exists_set g s
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

omit [CompleteSpace R] [NormMulClass R] [NormOneClass R] [(𝓝[≠] (0 : R)).NeBot] [Nontrivial R] in
/-- For a normalised distinguished `g` (leading-coefficient norm `1`), there is `ε ∈ (0,1)`
  dominating every strictly-higher coefficient norm. -/
lemma exists_epsilon_of_distinguished (g : PowerSeries.Restricted R 1) (s : ℕ)
    (gd : distinguished norm 1 g.1 s) (hg1 : ‖PowerSeries.coeff s g.1‖ = 1) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ ∀ t, s < t → ‖PowerSeries.coeff t g.1‖ ≤ ε := by
  have := (PowerSeries.isRestricted_iff' 1 g.1).mp g.2
  simp only [one_pow, mul_one] at this
  -- Eventually `‖coeff t g.1‖ < 1/2`
  obtain ⟨N, hN⟩ : ∃ N, ∀ t ≥ N, ‖PowerSeries.coeff t g.1‖ < 1/2 := by
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp this (1/2) (by norm_num)
    exact ⟨N, fun t ht => by aesop⟩
  have : ∀ t, s < t → ‖PowerSeries.coeff t g.1‖ < 1 :=
    fun t ht => by simpa [hg1] using gd.norm_max t ht
  -- Finite set `{‖coeff t g.1‖ : s < t < N}`, each `< 1`.
  let F : Finset ℝ := (Finset.Ioo s N).image (fun t => ‖PowerSeries.coeff t g.1‖)
  -- `max F < 1`, and so `ε = max (max F) (1/2)` works.
  by_cases hF : F.Nonempty
  · refine ⟨max (F.max' hF) (1/2), lt_max_iff.mpr (Or.inr (by norm_num)), max_lt (by aesop)
      (by norm_num), ?_⟩
    intro t ht
    rcases lt_or_ge t N with htN | htN
    · exact (F.le_max' _ (by aesop)).trans (le_max_left _ _)
    · exact (hN t htN).le.trans (le_max_right _ _)
  · refine ⟨1/2, by norm_num, by norm_num, fun t ht => ?_⟩
    have htN : N ≤ t := by
      by_contra h
      exact hF ⟨_, Finset.mem_image.mpr ⟨t, Finset.mem_Ioo.mpr ⟨ht, lt_of_not_ge h⟩, rfl⟩⟩
    exact (hN t htN).le

/-- When `g ∈ T°` has degree-`s` coefficient equal to `1` and `ε ∈ (0,1)` dominates every
  strictly-higher coefficient, `τ_ε(g)` is monic of degree `s`. -/
lemma closedBall_residueRingHom_monic_of_distinguished {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (s : ℕ)
    (g : ↥T°) (hcoeff_s : PowerSeries.coeff s (g : PowerSeries.Restricted R 1).1 = 1)
    (hcoeff_gt : ∀ t, s < t → ‖PowerSeries.coeff t (g : PowerSeries.Restricted R 1).1‖ ≤ ε) :
    (Restricted.closedBall_residueRingHom ε hε0 g).Monic ∧
    (Restricted.closedBall_residueRingHom ε hε0 g).degree = s := by
  haveI : Nontrivial (↥R° ⧸ PowerBounded.closedBall_ideal ε hε0.le) := by
    refine Ideal.Quotient.nontrivial_iff.mpr (fun h ↦ ?_)
    have : (1 : ↥R°) ∈ PowerBounded.closedBall_ideal ε hε0.le := by
      rw [h]
      exact Submodule.mem_top
    rw [PowerBounded.mem_closedBall_ideal, OneMemClass.coe_one, norm_one] at this
    grind
  -- leading coefficient reduces to `1`
  have hs : (Restricted.closedBall_residuePolynomial ε hε0 g).coeff s = 1 := by
    rw [Restricted.closedBall_residuePolynomial_coeff ε hε0 g]
    suffices Restricted.pbCoeff g s = 1 by
      aesop
    exact OneMemClass.coe_eq_one.mp hcoeff_s
  -- strictly-higher coefficients reduce to `0`
  have (v : ℕ) (hv : s < v) : (Restricted.closedBall_residuePolynomial ε hε0 g).coeff v = 0 := by
    simpa [Restricted.closedBall_residuePolynomial_coeff ε hε0 g, Ideal.Quotient.eq_zero_iff_mem,
      PowerBounded.mem_closedBall_ideal, Restricted.pbCoeff_coe] using hcoeff_gt v hv
  have hdeg := le_antisymm
    ((Polynomial.degree_le_iff_coeff_zero _ _).mpr fun m hm => this m (mod_cast hm))
    (Polynomial.le_degree_of_ne_zero (by rw [hs]; exact one_ne_zero))
  refine ⟨?_, hdeg⟩
  rw [Polynomial.Monic, Polynomial.leadingCoeff]
  convert hs
  exact Polynomial.natDegree_eq_of_degree_eq_some hdeg

omit [CompleteSpace R] [Nontrivial R] in
/- If `τ_ε(g)` is monic, then every `f ∈ T°` can be Euclidean-divided by `g` modulo `ε`:
there are a quotient `q ∈ T°` and a remainder polynomial `r` over the base `R` with
`deg r < deg τ_ε(g)` such that `‖f - g·q - ↑r‖ ≤ ε`.
-/
lemma exists_div_by_τε_monic {ε : ℝ} (hε0 : 0 < ε)
    [Nontrivial (↥R° ⧸ PowerBounded.closedBall_ideal ε hε0.le)] (g f : ↥T°)
    (hτg : (Restricted.closedBall_residueRingHom ε hε0 g).Monic) :
    ∃ (q : ↥T°) (r : Polynomial R), r.degree < (Restricted.closedBall_residueRingHom ε hε0 g).degree
    ∧ ‖(f : PowerSeries.Restricted R 1) - (g : PowerSeries.Restricted R 1) *
    (q : PowerSeries.Restricted R 1) - Polynomial.toRestricted 1 r‖ ≤ ε := by
  obtain ⟨q, r, hf_eq, hr⟩ := Polynomial.exists_div_by_monic hτg
    (Restricted.closedBall_residueRingHom ε hε0 f)
  refine ⟨Restricted.pbPoly_to_pbRestricted (Polynomial.liftQuot (PowerBounded.closedBall_ideal ε
    hε0.le) q), (Polynomial.liftQuot (PowerBounded.closedBall_ideal ε hε0.le) r).map
    (PowerBounded.subring R (S := ℤ)).subtype, ?_, ?_⟩
  · exact lt_of_le_of_lt ((Polynomial.degree_map_le).trans (Polynomial.degree_liftQuot_le _ r)) hr
  · simp_rw [← Restricted.pbPoly_to_pbRestricted_coe, ← Subring.coe_mul, ← AddSubgroupClass.coe_sub]
    apply Restricted.closedBall_norm_le_of_residueRingHom_eq_zero hε0
    rw [map_sub, map_sub, map_mul, Restricted.closedBall_residueRingHom_pbPoly_to_pbRestricted,
      Restricted.closedBall_residueRingHom_pbPoly_to_pbRestricted,
      Polynomial.liftQuot_map, Polynomial.liftQuot_map, hf_eq]
    ring

/-- **PDF Lemma 4.11, Steps 1,3–5 (the `ε`-approximation), abstract base ring.**
For each `f`, there is `b ∈ exists_set g s` with `‖-f + b‖ ≤ ε‖f‖`.  Proof plan (PDF `τ_ε`):

* normalise `g` to leading coefficient `1` by `C u`, `u = (coeff_s g)⁻¹` (a unit of norm `1`);
* scale `f` to norm `≤ 1` by `C α`, where `α` is the unit of norm `‖f‖⁻¹` supplied by `hf`
  — the `ext1`-style hypothesis, replacing ToPR's `NormedField` step (cf. comment on `ext1`);
* lift `C u · g`, `C α · f` into `T°`, where `τ_ε(C u · g)` is monic of degree `s`
  (`residueRingHom_ε_monic_of_distinguished`);
* divide modulo `ε` (`exists_div_by_τε_monic`) → `q, r` with `‖C α·f - C u·g·q - ↑r‖ ≤ ε`;
* unscale by `C α⁻¹` (norm `‖f‖`) to land `b = g·q' + ↑r' ∈ exists_set g s` with the `ε‖f‖` bound. -/
lemma exists_divApprox (g : PowerSeries.Restricted R 1) (hg : ‖g‖ = 1) (s : ℕ)
    (gd : distinguished norm 1 g.1 s) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    (hε_bd : ∀ t, s < t → ‖PowerSeries.coeff t g.1‖ ≤ ε)
    (f : PowerSeries.Restricted R 1) (hf : ∃ a : R, ‖a‖ = ‖f‖⁻¹ ∧ IsUnit a) :
    ∃ b ∈ exists_set g s, ‖-f + b‖ ≤ ε * ‖f‖ := by
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
  haveI : Nontrivial (↥R° ⧸ PowerBounded.closedBall_ideal ε hε0.le) := by
    refine Ideal.Quotient.nontrivial_iff.mpr (fun h => ?_)
    have h1 : (1 : ↥R°) ∈ PowerBounded.closedBall_ideal ε hε0.le := by rw [h]; exact Submodule.mem_top
    rw [PowerBounded.mem_closedBall_ideal, OneMemClass.coe_one, norm_one] at h1; linarith
  have hmonic := closedBall_residueRingHom_monic_of_distinguished hε0 hε1 s ⟨g', hg'_pb⟩ hg'_cs hg'_bd
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

lemma divSubgroup_dense (g : PowerSeries.Restricted R 1) (hg : ‖g‖ = 1) (s : ℕ)
    (gd : distinguished norm 1 g.1 s) (hunit : ∀ f : PowerSeries.Restricted R 1, f ≠ 0 →
    ∃ a : R, ‖a‖ = ‖f‖⁻¹ ∧ IsUnit a) : Dense (exists_set g s) := by
  suffices ∃ ε, 0 < ε ∧ ε < 1 ∧ SeminormedAddGroup.epsilonDense
      (exists_subgroup g s) ε by
    obtain ⟨ε, hε1, hε2, h⟩ := this
    exact SeminormedAddGroup.dense_epsilonDense _ _ hε1 hε2 h
  obtain ⟨ε, hε0, hε1, hε_bd⟩ := exists_epsilon_of_distinguished g s gd
    (by rwa [Restricted.norm_eq, gd.norm_eq] at hg)
  refine ⟨ε, hε0, hε1, ?_⟩
  intro f
  by_cases hf : f = 0
  · simp [hf]
  · obtain ⟨b, hb_mem, hb_le⟩ := exists_divApprox g hg s gd hε0 hε1 hε_bd f (hunit f hf)
    exact ⟨⟨b, hb_mem⟩, hb_le⟩

omit [CompleteSpace R] [NormMulClass R] [NormOneClass R] [(𝓝[≠] (0 : R)).NeBot] [Nontrivial R] in
lemma Restricted.coeff_continuous (v : ℕ) :
    Continuous fun f : PowerSeries.Restricted R 1 => PowerSeries.coeff v f.1 := by
  refine Metric.continuous_iff.mpr fun f ε hε => ⟨ε, hε, fun g hg => ?_⟩
  rw [dist_eq_norm, ← LinearMap.map_sub (PowerSeries.coeff v) g.1 f.1]
  have := PowerSeries.le_gaussNorm norm 1 (g - f).1 (Restricted.hasGaussNorm 1 (g - f)) v
  rw [one_pow, mul_one, ← Restricted.norm_eq] at this
  exact this.trans_lt (by rwa [← dist_eq_norm])

omit [CompleteSpace R] [NormMulClass R] [NormOneClass R] [(𝓝[≠] (0 : R)).NeBot] [Nontrivial R] in
/-- The set of `f ∈ T` whose coefficients above degree `s` all vanish is closed.
This is precisely the image of `Polynomial.toRestricted 1` on polynomials of degree `< s`. -/
lemma polySubspace_isClosed (s : ℕ) :
    IsClosed {f : PowerSeries.Restricted R 1 | ∀ v, s ≤ v → PowerSeries.coeff v f.1 = 0} := by
  refine IsSeqClosed.isClosed fun f_seq f hf_mem hf_lim v hv => ?_
  have : Filter.Tendsto (fun n => PowerSeries.coeff v (f_seq n).1) Filter.atTop
    (nhds (PowerSeries.coeff v f.1)) := ((Restricted.coeff_continuous v).tendsto _).comp hf_lim
  simp_all only [Set.mem_setOf_eq, tendsto_const_nhds_iff]

lemma divSubgroup_closed (g : PowerSeries.Restricted R 1) (s : ℕ) (hg : distinguished norm 1 g.1 s) :
    IsClosed (exists_set g s) := by
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
    ∃ (q : PowerSeries.Restricted R 1) (r : Polynomial R), Polynomial.degree r < s ∧
    f = g * q + (Polynomial.toRestricted 1 r) := by
  have : exists_set g s = Set.univ := by
    rw [← (divSubgroup_closed g s gd).closure_eq, (divSubgroup_dense g hg s gd hunit).closure_eq]
  obtain ⟨q, r, hr, hf_eq⟩ := this ▸ Set.mem_univ f
  exact ⟨q, r, hr, hf_eq⟩

omit [CompleteSpace R] [NormOneClass R] [(𝓝[≠] (0 : R)).NeBot] in
lemma ext1 (g : PowerSeries.Restricted R 1) (s : ℕ) (gd : distinguished norm 1 g.1 s) (a : R)
   (ha2 : IsUnit a) : distinguished norm 1 (PowerSeries.Restricted.C 1 a * g).1 s
    where
  unit := by
    simpa [coeff_isUnit, PowerSeries.Restricted.coeff_C_mul] using ha2.mul gd.unit
  norm_eq := by
    rw [norm_eq, ← Restricted.norm_eq, norm_mul, PowerSeries.Restricted.norm_C,
      PowerSeries.Restricted.coeff_C_mul, norm_mul]
    congr 1
    simpa [Restricted.norm_eq] using gd.norm_eq
  norm_max t ht := by
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
    (h : ∃ a : R, ‖a‖ = ‖g‖⁻¹ ∧ IsUnit a) (hunit : ∀ f : PowerSeries.Restricted R 1, f ≠ 0 →
    ∃ a : R, ‖a‖ = ‖f‖⁻¹ ∧ IsUnit a) : ∃ (q : PowerSeries.Restricted R 1) (r : Polynomial R),
    Polynomial.degree r < s ∧ f = g * q + (Polynomial.toRestricted 1 r) := by
  obtain ⟨a, ha1, ha2⟩ := h
  have : ‖PowerSeries.Restricted.C 1 a * g‖ = 1 := by
    simp only [norm_mul, PowerSeries.Restricted.norm_C 1 a, ha1]
    grind [gd.norm_pos' (by simp)]
  obtain ⟨q₀, r₀, hr₀, hf₀⟩ := weierstrassDivision_existance'
    (PowerSeries.Restricted.C 1 a * g) this s (ext1 g s gd a ha2) f hunit
  use PowerSeries.Restricted.C 1 a * q₀, r₀, hr₀
  grind


/-- The quotient in a Weierstrass division is unique: any two decompositions of `f` as
`g * q + r` with `deg r < s` share the same quotient `q`. -/
lemma weierstrassDivision_q_unique (g : PowerSeries.Restricted R 1) (s : ℕ)
    (gd : distinguished norm 1 g.1 s) (f : PowerSeries.Restricted R 1)
    {q₁ q₂ : PowerSeries.Restricted R 1} {r₁ r₂ : Polynomial R}
    (hr₁ : Polynomial.degree r₁ < s) (hf₁ : f = g * q₁ + Polynomial.toRestricted 1 r₁)
    (hr₂ : Polynomial.degree r₂ < s) (hf₂ : f = g * q₂ + Polynomial.toRestricted 1 r₂) :
    q₁ = q₂ := by
  have h0 : g * (q₁ - q₂) + Polynomial.toRestricted 1 (r₁ - r₂) = 0 := by
    calc
      _ = g * q₁ - g * q₂ + (Polynomial.toRestricted 1 r₁ - Polynomial.toRestricted 1 r₂) := by
        rw [mul_sub, Polynomial.toRestricted_sub]
      _ = (g * q₁ + Polynomial.toRestricted 1 r₁) - (g * q₂ + Polynomial.toRestricted 1 r₂) := by
        ring
      _ = _ := by rw [← hf₁, ← hf₂, sub_self]
  have h_bd := weierstrassDivision_bounds_q g s gd 0 (q₁ - q₂) (r₁ - r₂)
    (lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt hr₁ hr₂)) h0.symm
  simp only [norm_zero, mul_zero, norm_le_zero_iff] at h_bd
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
    exact weierstrassDivision_q_unique g s gd f hr' hf' hr₀ hf₀

-- hdef should be its own API lemma

-- Note on the form of this statement: two natural phrasings exist and it is unclear which is
-- better.
-- (1) The current form, `∃! q : Polynomial R, ...`, mirrors `weierstrassDivision_uniqueness` but
--     quantifies only over polynomials. Read in isolation it is silent on whether some
--     non-polynomial `q : PowerSeries.Restricted R 1` might also solve the division — uniqueness
--     over the subring of polynomials cannot rule out solutions outside it.
-- (2) The previous form took any `q : PowerSeries.Restricted R 1` solving the division and
--     concluded `∃ q₀ : Polynomial R, q = Polynomial.toRestricted 1 q₀`, i.e. it directly said
--     "the restricted quotient is a polynomial", but the statement was less idiomatic.
-- Nothing is lost with (1): combining it with `weierstrassDivision_uniqueness` (uniqueness over
-- the whole restricted ring) recovers (2), since the unique restricted quotient must then equal
-- the polynomial one. See the proof of `weierstrassPreparation_polynomial` in WPrep.lean, where
-- this bridging is carried out to show the unit `e` (a priori only a restricted power series)
-- equals the polynomial quotient. If form (2) is needed repeatedly, it can be restated as a
-- one-line corollary of (1) and `weierstrassDivision_uniqueness`.
/-- **Weierstrass division for polynomials.** If `f` and `g` are polynomials, with `g` of degree
`s`, then the Weierstrass division of `f` by `g` holds with the quotient `q` ranging over
polynomials: the quotient of `weierstrassDivision_uniqueness` is itself a polynomial.

The hypothesis `hgs` is necessary: over `ℤ_p` the polynomial `g = X ^ s + p • X ^ (s + 1)` is
distinguished of degree `s`, but dividing `f = X ^ s` by it gives `q = (1 + p • X)⁻¹`, which is
not a polynomial. -/
lemma weierstrassDivision_polynomial (g₀ : Polynomial R) (s : ℕ)
    (gd : distinguished norm 1 (Polynomial.toRestricted 1 g₀).1 s) (hgs : g₀.degree ≤ s)
    (f₀ : Polynomial R) (h : ∃ a : R, ‖a‖ = ‖Polynomial.toRestricted 1 g₀‖⁻¹ ∧ IsUnit a)
    (hunit : ∀ f : PowerSeries.Restricted R 1, f ≠ 0 → ∃ a : R, ‖a‖ = ‖f‖⁻¹ ∧ IsUnit a) :
    ∃! q : Polynomial R, ∃! r : Polynomial R, Polynomial.degree r < s ∧
    Polynomial.toRestricted 1 f₀ = Polynomial.toRestricted 1 g₀ * Polynomial.toRestricted 1 q +
      Polynomial.toRestricted 1 r := by
  -- `g₀` has degree exactly `s` with unit leading coefficient, so rescaling by the inverse of
  -- that unit gives a monic polynomial and we can divide `f₀` by it in `R[X]`.
  have hgu : IsUnit (g₀.coeff s) := by
    have h1 : IsUnit (PowerSeries.coeff s (g₀ : PowerSeries R)) := gd.unit
    rwa [Polynomial.coeff_coe] at h1
  obtain ⟨u, hu⟩ := hgu
  have hdeg : g₀.degree = s :=
    le_antisymm hgs (Polynomial.le_degree_of_ne_zero (hu ▸ u.ne_zero))
  have hlead : g₀.leadingCoeff = g₀.coeff s :=
    congrArg g₀.coeff (Polynomial.natDegree_eq_of_degree_eq_some hdeg)
  have hmonic : (Polynomial.C (↑u⁻¹ : R) * g₀).Monic :=
    Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one (by rw [hlead, ← hu, Units.inv_mul])
  have hdeg₁ : (Polynomial.C (↑u⁻¹ : R) * g₀).degree = s := by
    refine le_antisymm ?_ (Polynomial.le_degree_of_ne_zero ?_)
    · calc (Polynomial.C (↑u⁻¹ : R) * g₀).degree
          ≤ (Polynomial.C (↑u⁻¹ : R)).degree + g₀.degree := Polynomial.degree_mul_le _ _
        _ ≤ 0 + (s : WithBot ℕ) := add_le_add Polynomial.degree_C_le hdeg.le
        _ = s := zero_add _
    · rw [Polynomial.coeff_C_mul, ← hu, Units.inv_mul]
      exact one_ne_zero
  -- The polynomial division of `f₀` by the monic rescaling gives a polynomial solution of the
  -- Weierstrass division problem.
  have hpoly : f₀ = g₀ * (Polynomial.C (↑u⁻¹ : R) * (f₀ /ₘ (Polynomial.C (↑u⁻¹ : R) * g₀))) +
      f₀ %ₘ (Polynomial.C (↑u⁻¹ : R) * g₀) := by
    conv_lhs => rw [← Polynomial.modByMonic_add_div f₀ (Polynomial.C (↑u⁻¹ : R) * g₀)]
    ring
  have hr₁ : (f₀ %ₘ (Polynomial.C (↑u⁻¹ : R) * g₀)).degree < s := by
    have h2 := Polynomial.degree_modByMonic_lt f₀ hmonic
    rwa [hdeg₁] at h2
  have hf₁ : Polynomial.toRestricted 1 f₀ = Polynomial.toRestricted 1 g₀ *
      Polynomial.toRestricted 1 (Polynomial.C (↑u⁻¹ : R) *
        (f₀ /ₘ (Polynomial.C (↑u⁻¹ : R) * g₀))) +
      Polynomial.toRestricted 1 (f₀ %ₘ (Polynomial.C (↑u⁻¹ : R) * g₀)) := by
    rw [← Polynomial.toRestricted_mul, ← Polynomial.toRestricted_add]
    exact congrArg _ hpoly
  -- By uniqueness any solution equals the unique Weierstrass quotient `Q`, so any polynomial
  -- solution equals the one just constructed.
  obtain ⟨Q, -, hQ⟩ := weierstrassDivision_uniqueness (Polynomial.toRestricted 1 g₀) s gd
    (Polynomial.toRestricted 1 f₀) h hunit
  have key : ∀ (q' : PowerSeries.Restricted R 1) (r' : Polynomial R), Polynomial.degree r' < s →
      Polynomial.toRestricted 1 f₀ = Polynomial.toRestricted 1 g₀ * q' +
        Polynomial.toRestricted 1 r' → q' = Q := by
    intro q' r' hr' hf'
    refine hQ q' ⟨r', ⟨hr', hf'⟩, ?_⟩
    rintro r'' ⟨-, hf''⟩
    exact Polynomial.coe_inj.mp (congr_arg Subtype.val (add_left_cancel (hf''.symm.trans hf')))
  refine ⟨Polynomial.C (↑u⁻¹ : R) * (f₀ /ₘ (Polynomial.C (↑u⁻¹ : R) * g₀)),
    ⟨f₀ %ₘ (Polynomial.C (↑u⁻¹ : R) * g₀), ⟨hr₁, hf₁⟩, ?_⟩, ?_⟩
  · rintro r'' ⟨-, hf''⟩
    exact Polynomial.coe_inj.mp (congr_arg Subtype.val (add_left_cancel (hf''.symm.trans hf₁)))
  · rintro q' ⟨r', ⟨hr', hf'⟩, -⟩
    exact Polynomial.coe_inj.mp (congrArg Subtype.val
      ((key _ _ hr' hf').trans (key _ _ hr₁ hf₁).symm))

end WeierstrassDivision
