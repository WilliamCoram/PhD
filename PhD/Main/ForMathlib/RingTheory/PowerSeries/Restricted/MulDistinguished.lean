/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.Main.ForMathlib.Analysis.Normed.Ring.NormMulUnit
import PhD.Main.ForMathlib.RingTheory.PowerSeries.Restricted.GaussNorm
import Mathlib.RingTheory.PowerSeries.Trunc

/-! # `T`-distinguished series in Martin's sense, and his Lemma 1.26

`IsMulDistinguished c f s`: the `s`-th coefficient is a multiplicative unit
(`IsNormMulUnit`), its Gauss term attains the Gauss norm, and it strictly dominates every
**later** Gauss term — [Mar16, Definition 1.24].  Over a `NormMulClass` coefficient ring
this coincides with the project's `IsDistinguished` (every unit is then a multiplicative
unit); over a general ultrametric normed ring it is the hypothesis making Weierstrass
division work with no assumption on the radius.

The main results are the two parts of [Mar16, Lemma 1.26]: multiplication by a
distinguished series is norm-multiplicative, with the product's norm attained at the sum
of the distinguished degree and the greatest achieving index of the cofactor.

Source: F. Martin, J. EMS 18 (2016), §1.3.
-/

namespace PowerSeries

section Def

variable {A : Type*} [NormedCommRing A]

/-- `f` is **`T`-distinguished of order `s` at radius `c`** in Martin's sense: the `s`-th
coefficient is a multiplicative unit, its Gauss term attains the Gauss norm, and it
strictly dominates every later Gauss term.  Source: [Mar16, Definition 1.24]. -/
structure IsMulDistinguished (c : ℝ) (f : PowerSeries A) (s : ℕ) : Prop where
  /-- The `s`-th coefficient is a multiplicative unit. -/
  isNormMulUnit_coeff : IsNormMulUnit (coeff s f)
  /-- The `s`-th Gauss term attains the Gauss norm. -/
  gaussNorm_eq : gaussNorm norm c f = ‖coeff s f‖ * c ^ s
  /-- The `s`-th Gauss term strictly dominates every later Gauss term. -/
  gaussTerm_lt : ∀ t, s < t → ‖coeff t f‖ * c ^ t < ‖coeff s f‖ * c ^ s

variable {c : ℝ} {f : PowerSeries A} {s : ℕ}

/-- A Martin-distinguished series forces the coefficient ring to be nontrivial.  (Native
version, independent of `IsDistinguished`.) -/
lemma IsMulDistinguished.nontrivial (hf : IsMulDistinguished c f s) : Nontrivial A :=
  not_subsingleton_iff_nontrivial.mp fun _ ↦ by
    simpa [Subsingleton.elim (coeff (s + 1) f) 0, Subsingleton.elim (coeff s f) 0] using
      hf.gaussTerm_lt (s + 1) (lt_add_one s)

/-- A Martin-distinguished series is nonzero. -/
lemma IsMulDistinguished.ne_zero [Nontrivial A] (hf : IsMulDistinguished c f s) : f ≠ 0 :=
  fun h0 ↦ hf.isNormMulUnit_coeff.isUnit.ne_zero (by rw [h0, map_zero])

end Def

namespace Restricted

variable {A : Type*} [NormedCommRing A] [IsUltrametricDist A] {c : ℝ} [Fact (0 < c)]

/-- The `s`-th weighted coefficient norm of a Martin-distinguished restricted power series
is its norm.  (Native version, independent of `IsDistinguished`.) -/
lemma _root_.PowerSeries.IsMulDistinguished.norm_coeff_mul_pow_eq {s : ℕ} {l : Restricted A c}
    (hl : IsMulDistinguished c l.1 s) : ‖coeff s l.1‖ * c ^ s = ‖l‖ :=
  hl.gaussNorm_eq.symm.trans (norm_def c l).symm

/-- A Martin-distinguished restricted power series has positive norm. -/
lemma _root_.PowerSeries.IsMulDistinguished.norm_pos {s : ℕ} {l : Restricted A c}
    (hl : IsMulDistinguished c l.1 s) : 0 < ‖l‖ :=
  have : Nontrivial A := hl.nontrivial
  norm_pos_iff.mpr fun h ↦ hl.ne_zero (congrArg Subtype.val h)

/-- A nonzero restricted power series has a **greatest** index achieving its Gauss norm:
the achieving set is nonempty (`exists_coeff_ne_zero_norm_eq`) and the Gauss terms tend
to `0`.  Source: [Mar16, Lemma 1.26], "let `k₀` denote the greatest rank such that
`‖q_{k₀}‖ r^{k₀} = ‖q‖`". -/
lemma exists_greatest_achievesGaussNorm (q : Restricted A c) (hq : q ≠ 0) :
    ∃ k₀, AchievesGaussNorm norm c q.1 k₀ ∧
      ∀ k, k₀ < k → ‖coeff k q.1‖ * c ^ k < ‖q‖ := by
  classical
  obtain ⟨k₁, -, hk1_eq'⟩ := exists_coeff_ne_zero_norm_eq c q hq
  have hk1_eq : ‖coeff k₁ q.1‖ * c ^ k₁ = ‖q‖ := hk1_eq'.symm
  have hq_pos : 0 < ‖q‖ := norm_pos_iff.mpr hq
  have htend := (isRestricted_iff' c q.1).mp q.2
  have h_ev : ∀ᶠ n in Filter.atTop, ‖coeff n q.1‖ * c ^ n < ‖q‖ :=
    htend.eventually_lt tendsto_const_nhds hq_pos
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp h_ev
  have hk1N : k₁ ≤ N := not_lt.mp fun h => absurd hk1_eq (ne_of_lt (hN k₁ h.le))
  refine ⟨Nat.findGreatest (fun j => ‖coeff j q.1‖ * c ^ j = ‖q‖) N,
    Nat.findGreatest_spec (P := fun j => ‖coeff j q.1‖ * c ^ j = ‖q‖) hk1N hk1_eq, ?_⟩
  intro k hk
  rcases le_or_gt k N with hkN | hNk
  · exact lt_of_le_of_ne (norm_coeff_mul_pow_le c q k)
      (Nat.findGreatest_is_greatest (P := fun j => ‖coeff j q.1‖ * c ^ j = ‖q‖) hk hkN)
  · exact hN k hNk.le

omit [Fact (0 < c)] in
/-- The coefficients of a polynomial truncation, viewed back in the restricted power series
ring: they agree with those of `f` below the truncation degree and vanish at or above it. -/
private lemma coeff_toRestricted_trunc (f : Restricted A c) (N k : ℕ) :
    coeff k (Polynomial.toRestricted c (trunc N f.1)).1 = if k < N then coeff k f.1 else 0 := by
  rw [Polynomial.val_toRestricted, Polynomial.coeff_coe, PowerSeries.coeff_trunc]

/-- Truncation does not increase the Gauss norm. -/
lemma norm_toRestricted_trunc_le (f : Restricted A c) (N : ℕ) :
    ‖Polynomial.toRestricted c (trunc N f.1)‖ ≤ ‖f‖ := by
  refine (norm_le_iff _ _).mpr fun i => ?_
  rw [coeff_toRestricted_trunc f N i]
  split_ifs with hi
  · exact norm_coeff_mul_pow_le c f i
  · simp only [norm_zero, zero_mul]; exact norm_nonneg f

/-- Polynomial truncations approximate a restricted power series in Gauss norm.
Source: [Mar16, proof of Proposition 1.27], "let us assume that `N` is big enough to
satisfy `‖f − f'‖ ≤ κ‖f‖`". -/
lemma exists_norm_sub_toRestricted_trunc_le (f : Restricted A c) {ε : ℝ} (hε : 0 < ε) :
    ∃ N, ‖f - Polynomial.toRestricted c (trunc N f.1)‖ ≤ ε := by
  have htend := (isRestricted_iff' c f.1).mp f.2
  have h_ev : ∀ᶠ n in Filter.atTop, ‖coeff n f.1‖ * c ^ n < ε :=
    htend.eventually_lt tendsto_const_nhds hε
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp h_ev
  refine ⟨N, (norm_le_iff _ _).mpr fun i => ?_⟩
  rw [show (f - Polynomial.toRestricted c (trunc N f.1)).1
      = f.1 - (Polynomial.toRestricted c (trunc N f.1)).1 from rfl, map_sub,
    coeff_toRestricted_trunc f N i]
  split_ifs with hi
  · simp only [sub_self, norm_zero, zero_mul]; exact hε.le
  · rw [sub_zero]; exact (hN i (not_lt.mp hi)).le

/-- The degree-`≤ s` truncation of a Martin-distinguished series is Martin-distinguished
of the same order and the same norm.  Source: [Mar16, proof of Proposition 1.27],
"`‖g‖ = ‖g'‖` because `g` is `T`-distinguished of degree `s`" (and `g'` is again
`T`-distinguished, used to apply (1.8) to `g'`). -/
lemma isMulDistinguished_toRestricted_trunc {g : Restricted A c} {s : ℕ}
    (hg : IsMulDistinguished c g.1 s) :
    IsMulDistinguished c (Polynomial.toRestricted c (trunc (s + 1) g.1)).1 s := by
  have hc : (0 : ℝ) < c := Fact.out
  have hcoeff_s : coeff s (Polynomial.toRestricted c (trunc (s + 1) g.1)).1 = coeff s g.1 := by
    rw [coeff_toRestricted_trunc g (s + 1) s]; exact if_pos (Nat.lt_succ_self s)
  have hgs_norm : ‖coeff s g.1‖ * c ^ s = ‖g‖ := hg.gaussNorm_eq.symm
  have hnorm_g' : ‖Polynomial.toRestricted c (trunc (s + 1) g.1)‖ = ‖coeff s g.1‖ * c ^ s := by
    refine le_antisymm ?_ ?_
    · rw [hgs_norm]; exact norm_toRestricted_trunc_le g (s + 1)
    · rw [← hcoeff_s]; exact norm_coeff_mul_pow_le c _ s
  have hpos : 0 < ‖coeff s g.1‖ * c ^ s :=
    (mul_nonneg (norm_nonneg _) (pow_nonneg hc.le _)).trans_lt
      (hg.gaussTerm_lt (s + 1) (Nat.lt_succ_self s))
  refine ⟨?_, ?_, ?_⟩
  · rw [hcoeff_s]; exact hg.isNormMulUnit_coeff
  · rw [hcoeff_s]; exact hnorm_g'
  · intro t ht
    have ht0 : coeff t (Polynomial.toRestricted c (trunc (s + 1) g.1)).1 = 0 := by
      rw [coeff_toRestricted_trunc g (s + 1) t]; exact if_neg (by omega)
    rw [ht0, hcoeff_s, norm_zero, zero_mul]; exact hpos

/-- If `a ≤ a'`, `b ≤ b'` with `a, b` nonnegative, `a', b'` positive, and at least one of the
two inequalities strict, then `a * b < a' * b'`. -/
private lemma mul_lt_mul_of_lt_or_lt {a b a' b' : ℝ} (ha : a ≤ a') (hb : b ≤ b')
    (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (ha' : 0 < a') (hb' : 0 < b') (h : a < a' ∨ b < b') :
    a * b < a' * b' := by
  rcases h with h | h
  · exact (mul_le_mul_of_nonneg_left hb ha0).trans_lt (mul_lt_mul_of_pos_right h hb')
  · exact (mul_le_mul_of_nonneg_right ha hb0).trans_lt (mul_lt_mul_of_pos_left h ha')

/-- **[Mar16, Lemma 1.26(2)]**: at the index `s + k₀` — distinguished degree plus greatest
achieving index of `q` — the coefficient of `g * q` has norm exactly
`‖g_s‖ * ‖q_{k₀}‖`: the diagonal term survives because every other product on the
antidiagonal is strictly smaller. -/
theorem norm_coeff_add_mul_of_isMulDistinguished {g q : Restricted A c} {s k₀ : ℕ}
    (hg : IsMulDistinguished c g.1 s) (hk : AchievesGaussNorm norm c q.1 k₀)
    (hkmax : ∀ k, k₀ < k → ‖coeff k q.1‖ * c ^ k < ‖q‖) :
    ‖coeff (s + k₀) (g * q).1‖ = ‖coeff s g.1‖ * ‖coeff k₀ q.1‖ := by
  have hc : (0 : ℝ) < c := Fact.out
  by_cases hq0 : q = 0
  · simp [hq0]
  · have hq_pos : 0 < ‖q‖ := norm_pos_iff.mpr hq0
    have hg_eq : ‖coeff s g.1‖ * c ^ s = ‖g‖ := hg.norm_coeff_mul_pow_eq
    have hg_pos' : 0 < ‖coeff s g.1‖ * c ^ s :=
      hg.norm_pos.trans_eq hg_eq.symm
    have hq_eq : ‖coeff k₀ q.1‖ * c ^ k₀ = ‖q‖ := hk.trans (norm_def c q).symm
    have hq_pos' : 0 < ‖coeff k₀ q.1‖ * c ^ k₀ := hq_pos.trans_eq hq_eq.symm
    have hdom : ∀ p ∈ Finset.antidiagonal (s + k₀), p ≠ (s, k₀) →
        ‖coeff p.1 g.1 * coeff p.2 q.1‖ < ‖coeff s g.1‖ * ‖coeff k₀ q.1‖ := by
      rintro ⟨m, k⟩ hp hpne
      rw [Finset.mem_antidiagonal] at hp
      refine (norm_mul_le _ _).trans_lt ?_
      have hkne : k ≠ k₀ := by
        intro hkeq
        apply hpne
        have hmeq : m = s := by omega
        rw [hkeq, hmeq]
      have hgauss : (‖coeff m g.1‖ * c ^ m) * (‖coeff k q.1‖ * c ^ k)
          < (‖coeff s g.1‖ * c ^ s) * (‖coeff k₀ q.1‖ * c ^ k₀) :=
        mul_lt_mul_of_lt_or_lt ((norm_coeff_mul_pow_le c g m).trans_eq hg_eq.symm)
          ((norm_coeff_mul_pow_le c q k).trans_eq hq_eq.symm)
          (mul_nonneg (norm_nonneg _) (pow_nonneg hc.le _))
          (mul_nonneg (norm_nonneg _) (pow_nonneg hc.le _)) hg_pos' hq_pos'
          ((lt_or_gt_of_ne hkne).imp (fun _ ↦ hg.gaussTerm_lt m (by omega))
            (fun h ↦ (hkmax k h).trans_eq hq_eq.symm))
      have key : (‖coeff m g.1‖ * ‖coeff k q.1‖) * c ^ (s + k₀)
          < (‖coeff s g.1‖ * ‖coeff k₀ q.1‖) * c ^ (s + k₀) :=
        calc (‖coeff m g.1‖ * ‖coeff k q.1‖) * c ^ (s + k₀)
            = (‖coeff m g.1‖ * c ^ m) * (‖coeff k q.1‖ * c ^ k) := by
              rw [← hp, pow_add]; ring
          _ < (‖coeff s g.1‖ * c ^ s) * (‖coeff k₀ q.1‖ * c ^ k₀) := hgauss
          _ = (‖coeff s g.1‖ * ‖coeff k₀ q.1‖) * c ^ (s + k₀) := by rw [pow_add]; ring
      exact lt_of_mul_lt_mul_right key (pow_nonneg hc.le _)
    calc ‖coeff (s + k₀) (g * q).1‖
        = ‖coeff s g.1 * coeff k₀ q.1‖ := by
          rw [show (g * q).1 = g.1 * q.1 from rfl, PowerSeries.coeff_mul,
            IsNonarchimedean.apply_sum_eq_of_lt
              (fun x y ↦ IsUltrametricDist.norm_add_le_max x y) (fun a ↦ (norm_neg a).symm)
              (k := (s, k₀)) (Finset.mem_antidiagonal.mpr rfl)
              (fun p hp hpne ↦ (hdom p hp hpne).trans_eq
                (hg.isNormMulUnit_coeff.norm_mul _).symm)]
      _ = ‖coeff s g.1‖ * ‖coeff k₀ q.1‖ := hg.isNormMulUnit_coeff.norm_mul _

/-- **[Mar16, Lemma 1.26(1)]**: multiplication by a Martin-distinguished series is
norm-multiplicative: `‖g * q‖ = ‖g‖ * ‖q‖`. -/
theorem norm_mul_of_isMulDistinguished {g : Restricted A c} {s : ℕ}
    (hg : IsMulDistinguished c g.1 s) (q : Restricted A c) :
    ‖g * q‖ = ‖g‖ * ‖q‖ := by
  by_cases hq0 : q = 0
  · rw [hq0, mul_zero, norm_zero, mul_zero]
  · obtain ⟨k₀, hk, hkmax⟩ := exists_greatest_achievesGaussNorm q hq0
    refine le_antisymm (norm_mul_le g q) ?_
    calc ‖g‖ * ‖q‖
        = (‖coeff s g.1‖ * c ^ s) * (‖coeff k₀ q.1‖ * c ^ k₀) := by
          rw [hg.norm_coeff_mul_pow_eq, hk.trans (norm_def c q).symm]
      _ = (‖coeff s g.1‖ * ‖coeff k₀ q.1‖) * c ^ (s + k₀) := by rw [pow_add]; ring
      _ = ‖coeff (s + k₀) (g * q).1‖ * c ^ (s + k₀) := by
          rw [norm_coeff_add_mul_of_isMulDistinguished hg hk hkmax]
      _ ≤ ‖g * q‖ := norm_coeff_mul_pow_le c (g * q) (s + k₀)

/-- A monic polynomial of degree `s` whose restricted power series has norm `c ^ s` — its
top Gauss term — is Martin-distinguished of degree `s` (its leading coefficient `1` is a
multiplicative unit). -/
lemma isMulDistinguished_toRestricted_of_monic [NormOneClass A] {ω : Polynomial A} {s : ℕ}
    (ωm : ω.Monic) (ωd : ω.degree = s) (ωn : ‖Polynomial.toRestricted c ω‖ = c ^ s) :
    IsMulDistinguished c (Polynomial.toRestricted c ω).1 s := by
  have hcoeff : ∀ k, coeff k (Polynomial.toRestricted c ω).1 = ω.coeff k :=
    Polynomial.coeff_coe ω
  have h1 : coeff s (Polynomial.toRestricted c ω).1 = 1 := by
    rw [hcoeff, ← Polynomial.natDegree_eq_of_degree_eq_some ωd]
    exact ωm.coeff_natDegree
  refine ⟨h1 ▸ isNormMulUnit_one, ?_, fun t ht ↦ ?_⟩
  · rw [← norm_def, ωn, h1, norm_one, one_mul]
  · rw [hcoeff, Polynomial.coeff_eq_zero_of_degree_lt (ωd ▸ Nat.cast_lt.mpr ht), norm_zero,
      zero_mul, h1, norm_one, one_mul]
    exact pow_pos Fact.out s

end Restricted

end PowerSeries
