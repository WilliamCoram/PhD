import Mathlib.RingTheory.PowerSeries.Basic

import PhD.ToPR.MvRestricted
import PhD.ToPR.GaussNorm

import Mathlib.Analysis.Normed.Unbundled.RingSeminorm

namespace PowerSeries

open Filter
open scoped Topology Pointwise

variable {R : Type*} [NormedRing R]

abbrev IsRestricted (c :  ℝ) (f : PowerSeries R) :=
  MvPowerSeries.IsRestricted (σ := Unit) (fun _ ↦ c) f

-- done by Claude... need to clean up a bit
lemma isRestricted_iff (c :  ℝ) (f : PowerSeries R) :
    IsRestricted c f ↔ Tendsto (fun (t : ℕ) ↦ ‖coeff t f‖ * c ^ t) cofinite (𝓝 0) := by
  unfold IsRestricted MvPowerSeries.IsRestricted
  have key : (fun (t : Unit →₀ ℕ) ↦ ‖MvPowerSeries.coeff t f‖ * t.prod (fun _ x ↦ c ^ x)) =
      (fun (n : ℕ) ↦ ‖coeff n f‖ * c ^ n) ∘ Equiv.finsuppUnique := by
    funext t
    simp only [Function.comp_apply, Equiv.finsuppUnique_apply, PUnit.default_eq_unit,
      Finsupp.prod_pow, Finset.univ_unique, Finset.prod_singleton, coeff,
      show (Finsupp.single () (t ())) = t by grind]
  rw [key]
  refine ⟨fun H => (H.comp Equiv.finsuppUnique.symm.injective.tendsto_cofinite).congr fun n => ?_,
    fun H => H.comp Equiv.finsuppUnique.injective.tendsto_cofinite⟩
  simp

@[simp]
lemma isRestricted_abs_iff (c :  ℝ) (f : PowerSeries R) :
    IsRestricted |c| f ↔ IsRestricted c f :=
  MvPowerSeries.isRestricted_abs_iff (fun _ ↦ c) f

lemma isRestricted_zero (c : ℝ) : IsRestricted c (0 : PowerSeries R) :=
 MvPowerSeries.isRestricted_zero (fun _ ↦ c)

lemma isRestricted_monomial (c : ℝ) (n : ℕ) (a : R) : IsRestricted c (monomial n a) :=
  MvPowerSeries.isRestricted_monomial (fun _ ↦ c) ((Finsupp.single () n)) a

lemma isRestricted_one (c : ℝ) : IsRestricted c (1 : PowerSeries R) :=
  MvPowerSeries.isRestricted_monomial (fun _ ↦ c) 0 1

lemma isRestricted_C (c : ℝ) (a : R) : IsRestricted c (C a) :=
  MvPowerSeries.isRestricted_C (fun _ ↦ c) a

lemma isRestricted.add (c : ℝ) {f g : PowerSeries R} (hf : IsRestricted c f) (hg : IsRestricted c g)
    : IsRestricted c (f + g) :=
  MvPowerSeries.isRestricted.add (fun _ ↦ c) hf hg

lemma isRestricted.neg (c : ℝ) {f : PowerSeries R} (hf : IsRestricted c f) :
    IsRestricted c (-f) :=
  MvPowerSeries.isRestricted.neg (fun _ ↦ c) hf

lemma isRestricted.mul [IsUltrametricDist R] (c : ℝ) {f g : PowerSeries R}
    (hf : IsRestricted c f) (hg : IsRestricted c g) : IsRestricted c (f * g) :=
  MvPowerSeries.isRestricted.mul (fun _ ↦ c) hf hg

/-- Additive subgroup structure on `MvPowerSeries σ R`. -/
def isAddSubgroup (c : ℝ) : AddSubgroup (PowerSeries R) where
  carrier := IsRestricted c
  zero_mem' := isRestricted_zero c
  add_mem' := isRestricted.add c
  neg_mem' := isRestricted.neg c

variable [IsUltrametricDist R]

/-- Ring structure on `MvPowerSeries σ R`. -/
def isSubring (c : ℝ) :  Subring (PowerSeries R) where
  __ := isAddSubgroup c
  one_mem' := isRestricted_one c
  mul_mem' := isRestricted.mul c

variable (R) in
/-- The type of restricted `MvPowerSeries σ R`. -/
def Restricted (c : ℝ) : Type _ := isSubring (R := R) c

noncomputable
def Restricted.C (c : ℝ) (a : R) : Restricted R c :=
  ⟨PowerSeries.C a, isRestricted_C c a⟩

/-- Ring structure on `Restricted R c`. -/
noncomputable
instance (c : ℝ) : Ring (Restricted R c) :=
  Subring.toRing (isSubring c)

end PowerSeries

namespace PowerSeries

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R]

/-- `CommRing` structure on `Restricted R c` when `R` is a `NormedCommRing`. -/
noncomputable
instance (c : ℝ) : CommRing (Restricted R c) :=
  Subring.toCommRing (R := PowerSeries R) (isSubring c)

end PowerSeries

namespace Restricted

variable {R : Type*} [NormedRing R] [IsUltrametricDist R] (c : ℝ)

variable (R) in
noncomputable
abbrev gaussNorm (f : PowerSeries.Restricted R c) : ℝ :=
  MvRestricted.gaussNorm R (fun _ ↦ c) f

lemma hasGaussNorm (f : PowerSeries.Restricted R c) :
  PowerSeries.HasGaussNorm norm c f.1 := Filter.Tendsto.bddAbove_range_of_cofinite f.2

variable [StrongPos (fun _ : Unit ↦ c)]

noncomputable
instance isRingNorm : RingNorm (PowerSeries.Restricted R c) where
  toFun f := gaussNorm R c f
  __ := MvRestricted.isRingNorm (R := R) (σ := Unit) (fun _ ↦ c)

variable (R) in
noncomputable
instance isNormedRing : NormedRing (PowerSeries.Restricted R c) :=
  RingNorm.toNormedRing (isRingNorm c)

noncomputable
instance isNormedCommRing (S : Type*) [NormedCommRing S] [IsUltrametricDist S] :
    NormedCommRing (PowerSeries.Restricted S c) where
  toNormedRing := isNormedRing S c
  mul_comm := mul_comm'

lemma norm_eq (f : PowerSeries.Restricted R c) :
  ‖f‖ = PowerSeries.gaussNorm (norm : R → ℝ) c f.1 := by rfl

noncomputable
instance isNonarchimedean :
    IsNonarchimedean (R := ℝ) (α := PowerSeries.Restricted R c) norm :=
  fun f g => PowerSeries.gaussNorm_add_le_max norm c f.1 g.1
    (Std.le_of_lt (StrongPos_pos (fun _ : Unit ↦ c) 0)) norm_nonneg
    IsUltrametricDist.norm_add_le_max (hasGaussNorm c f) (hasGaussNorm c g)

noncomputable
instance isUltrametricDist :
    IsUltrametricDist (PowerSeries.Restricted R c) :=
  IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
    (isNonarchimedean (R := R) c)

omit [StrongPos fun _ ↦ c] in
lemma gaussNorm_achieved (hc : 0 ≤ c) (f : PowerSeries.Restricted R c) :
    ∃ a, PowerSeries.achievesGaussNorm norm c f.1 a := by
  simp_rw [PowerSeries.achievesGaussNorm]
  obtain ⟨a, _⟩ := MvRestricted.gaussNorm_achieved (σ := Unit) (fun _ ↦ c) (fun i ↦ hc) f
  exact ⟨(a PUnit.unit), by simpa [show Finsupp.single () (a PUnit.unit) = a by grind]⟩

omit [StrongPos fun _ ↦ c] in
lemma gaussNorm_achieved' (hc : 0 ≤ c) (f : PowerSeries.Restricted R c) :
    ∃ a, ‖PowerSeries.coeff a f.1‖ * c ^ a = gaussNorm R c f := by
  have := gaussNorm_achieved c hc f
  simp [PowerSeries.achievesGaussNorm_iff] at this
  exact this

omit [StrongPos fun _ ↦ c] in
lemma achievingPoints_finite (hc : 0 ≤ c) (f : PowerSeries.Restricted R c)
    (h : gaussNorm R c f ≠ 0) :
    {a | PowerSeries.achievesGaussNorm norm c f.1 a}.Finite := by
  have := MvRestricted.achievingPoints_finite (fun _ ↦ c) (fun _ ↦ hc) f h

  sorry

noncomputable
instance isAbsoluteValue (hnorm : ∀ a b : R, norm (a * b) = norm a * norm b) :
    IsAbsoluteValue (gaussNorm R c) :=
  MvRestricted.isAbsoluteValue (fun _ ↦ c) hnorm

-- this was written and proved by Claude given my blueprint!
-- big proof of concept, just need to continue writing my blueprint to a good level.
-- then need to extract and clean
/-! ### Completeness of restricted power series (Lemma 4.16) -/

open Filter
open scoped Topology

variable [CompleteSpace R]

/-- **Lemma 4.16.** If `R` is a complete normed ring (with an ultrametric, non-archimedean norm)
and `c` is a positive real number, then `PowerSeries.Restricted R c` is complete with respect to
the Gauss norm.

Required type-class hypotheses (all already in scope from the surrounding `variable`s):
* `[NormedRing R]` — for `R` to have a norm (needed to even define the Gauss norm).
* `[IsUltrametricDist R]` — needed for `PowerSeries.Restricted R c` to be a ring (closure under
  multiplication of restricted power series) and to make the final ultrametric estimate that
  shows the candidate limit is itself restricted.
* `[StrongPos (fun _ : Unit ↦ c)]` (equivalently `0 < c`) — needed for the Gauss norm to be a
  norm; otherwise `c = 0` makes everything restricted with Gauss norm zero.
* `[CompleteSpace R]` — used to take coefficient-wise limits of Cauchy sequences in `R`. -/
instance isCompleteSpace : CompleteSpace (PowerSeries.Restricted R c) := by
  refine Metric.complete_of_cauchySeq_tendsto fun u hu => ?_
  have hc : (0 : ℝ) < c := StrongPos_pos (fun _ : Unit ↦ c) ()
  have hcn : ∀ n : ℕ, (0 : ℝ) < c ^ n := fun n => pow_pos hc n
  -- Step 1: the Gauss norm bounds each coefficient: `‖coeff n f.1 - coeff n g.1‖ * c^n ≤ ‖f - g‖`.
  have coeff_le : ∀ (f g : PowerSeries.Restricted R c) (n : ℕ),
      ‖PowerSeries.coeff n f.1 - PowerSeries.coeff n g.1‖ * c ^ n ≤ ‖f - g‖ := fun f g n => by
    have heq : PowerSeries.coeff n f.1 - PowerSeries.coeff n g.1 =
        PowerSeries.coeff n (f - g).1 := by
      show _ = PowerSeries.coeff n (f.1 - g.1)
      exact (map_sub _ _ _).symm
    rw [heq]
    exact PowerSeries.le_gaussNorm norm c (f - g).1 (hasGaussNorm c (f - g)) n
  -- Step 2: each coefficient sequence is Cauchy in `R`.
  have coeff_cauchy : ∀ n : ℕ, CauchySeq (fun i => PowerSeries.coeff n (u i).1) := fun n => by
    refine Metric.cauchySeq_iff.mpr fun ε hε => ?_
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hu (ε * c ^ n) (mul_pos hε (hcn n))
    refine ⟨N, fun i hi j hj => ?_⟩
    rw [dist_eq_norm]
    have h_uij : ‖u i - u j‖ < ε * c ^ n := by
      have := hN i hi j hj; rwa [dist_eq_norm] at this
    exact lt_of_mul_lt_mul_right ((coeff_le (u i) (u j) n).trans_lt h_uij) (hcn n).le
  -- Step 3: take pointwise limits in `R` and build the candidate restricted power series.
  choose a ha using fun n => cauchySeq_tendsto_of_complete (coeff_cauchy n)
  set f : PowerSeries R := PowerSeries.mk a with hf_def
  have coeff_f : ∀ n, PowerSeries.coeff n f = a n := fun n => by simp [f]
  -- Step 4: uniform-in-`n` convergence, obtained by letting `j → ∞` in the Cauchy property.
  have unif_conv : ∀ ε > (0 : ℝ), ∃ N, ∀ i ≥ N, ∀ n,
      ‖PowerSeries.coeff n (u i).1 - a n‖ * c ^ n ≤ ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hu ε hε
    refine ⟨N, fun i hi n => ?_⟩
    have h_lim : Tendsto
        (fun j => ‖PowerSeries.coeff n (u i).1 - PowerSeries.coeff n (u j).1‖ * c ^ n)
        atTop (𝓝 (‖PowerSeries.coeff n (u i).1 - a n‖ * c ^ n)) :=
      ((tendsto_const_nhds.sub (ha n)).norm).mul_const _
    refine le_of_tendsto h_lim ?_
    filter_upwards [Filter.eventually_ge_atTop N] with j hj
    have h_dist := hN i hi j hj
    rw [dist_eq_norm] at h_dist
    exact ((coeff_le (u i) (u j) n).trans_lt h_dist).le
  -- Step 5: the candidate `f` is restricted. Here we use the ultrametric inequality on `R`.
  have hf : PowerSeries.IsRestricted c f := by
    rw [PowerSeries.isRestricted_iff, Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨N₁, hN₁⟩ := unif_conv (ε / 2) (by linarith)
    have h_uN1 : Tendsto (fun n : ℕ => ‖PowerSeries.coeff n (u N₁).1‖ * c ^ n)
        cofinite (𝓝 0) := (PowerSeries.isRestricted_iff c (u N₁).1).mp (u N₁).2
    rw [Metric.tendsto_nhds] at h_uN1
    have h_uN1' := h_uN1 (ε / 2) (by linarith)
    rw [Filter.eventually_cofinite] at h_uN1' ⊢
    refine h_uN1'.subset fun n hn => ?_
    simp only [Set.mem_setOf_eq, dist_zero_right, Real.norm_eq_abs, not_lt] at hn ⊢
    rw [coeff_f] at hn
    have hp1 : 0 ≤ ‖a n‖ * c ^ n := mul_nonneg (norm_nonneg _) (hcn n).le
    have hp2 : 0 ≤ ‖PowerSeries.coeff n (u N₁).1‖ * c ^ n :=
      mul_nonneg (norm_nonneg _) (hcn n).le
    rw [abs_of_nonneg hp1] at hn
    rw [abs_of_nonneg hp2]
    have h1 : ‖PowerSeries.coeff n (u N₁).1 - a n‖ * c ^ n ≤ ε / 2 := hN₁ N₁ le_rfl n
    -- `‖a n‖ ≤ max ‖coeff n (u N₁).1 - a n‖ ‖coeff n (u N₁).1‖` by the ultrametric property.
    have h_ultra : ‖a n‖ ≤
        max ‖PowerSeries.coeff n (u N₁).1 - a n‖ ‖PowerSeries.coeff n (u N₁).1‖ := by
      have h1 : ‖(a n - PowerSeries.coeff n (u N₁).1) + PowerSeries.coeff n (u N₁).1‖ ≤
          max ‖a n - PowerSeries.coeff n (u N₁).1‖ ‖PowerSeries.coeff n (u N₁).1‖ :=
        IsUltrametricDist.norm_add_le_max _ _
      rw [sub_add_cancel] at h1
      rwa [norm_sub_rev] at h1
    have h_max_bd : ‖a n‖ * c ^ n ≤
        max (‖PowerSeries.coeff n (u N₁).1 - a n‖ * c ^ n)
            (‖PowerSeries.coeff n (u N₁).1‖ * c ^ n) := by
      rw [← max_mul_of_nonneg _ _ (hcn n).le]
      exact mul_le_mul_of_nonneg_right h_ultra (hcn n).le
    rcases le_max_iff.mp h_max_bd with h | h
    · linarith
    · linarith
  -- Step 6: `u i` converges to `⟨f, hf⟩` in the Gauss norm.
  refine ⟨⟨f, hf⟩, ?_⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := unif_conv (ε / 2) (by linarith)
  refine ⟨N, fun i hi => ?_⟩
  rw [dist_eq_norm]
  show MvPowerSeries.gaussNorm norm (fun _ ↦ c) (u i - ⟨f, hf⟩).1 < ε
  have hdiff : ∀ n, PowerSeries.coeff n (u i - ⟨f, hf⟩).1 =
      PowerSeries.coeff n (u i).1 - a n := fun n => by
    show PowerSeries.coeff n ((u i).1 - f) = _
    rw [map_sub, coeff_f]
  have hbd : ∀ n, ‖PowerSeries.coeff n (u i - ⟨f, hf⟩).1‖ * c ^ n ≤ ε / 2 := fun n => by
    rw [hdiff]; exact hN i hi n
  have h_gauss_le : MvPowerSeries.gaussNorm norm (fun _ : Unit ↦ c) (u i - ⟨f, hf⟩).1 ≤ ε / 2 := by
    show PowerSeries.gaussNorm norm c (u i - ⟨f, hf⟩).1 ≤ ε / 2
    rw [PowerSeries.gaussNorm_eq]
    exact ciSup_le hbd
  linarith

end Restricted

section Polynomial

lemma Polynomial.IsRestricted {R : Type*} [NormedRing R] [IsUltrametricDist R] (c : ℝ)
    (f : Polynomial R) : PowerSeries.IsRestricted c f.toPowerSeries := by
  rw [PowerSeries.isRestricted_iff]
  suffices {t | ¬ (‖(PowerSeries.coeff t) f.toPowerSeries‖ * c ^ t = 0)}.Finite by
    exact tendsto_nhds_of_eventually_eq this
  simp only [coeff_coe, mul_eq_zero, norm_eq_zero, not_or, ← mem_support_iff]
  exact Set.Finite.sep (Finset.finite_toSet _) _

def Polynomial.toRestricted {R : Type*} [NormedRing R] [IsUltrametricDist R] (c : ℝ)
    (f : Polynomial R) : PowerSeries.Restricted R c :=
  ⟨f.toPowerSeries, Polynomial.IsRestricted c f⟩

end Polynomial

section Monomial

lemma isRestricted_monomial {R : Type*} [NormedRing R] [IsUltrametricDist R] (c : ℝ)
    (n : ℕ) (r : R) : PowerSeries.IsRestricted c (PowerSeries.monomial n r) := by
  rw [PowerSeries.isRestricted_iff]
  simp_rw [PowerSeries.monomial]
  suffices {t | ¬ (‖(PowerSeries.coeff t) (PowerSeries.monomial n r)‖ * c ^ t = 0)}.Finite by
    exact tendsto_nhds_of_eventually_eq this
  have : {t | ¬ (‖(PowerSeries.coeff t) (PowerSeries.monomial n r)‖ * c ^ t = 0)} = {n} := by
    -- do later
    sorry
  simp_rw [this]
  exact Set.finite_singleton n

noncomputable
def Restricted.monomial {R : Type*} [NormedRing R] [IsUltrametricDist R] (c : ℝ)
    (n : ℕ) (r : R) : PowerSeries.Restricted R c :=
  ⟨PowerSeries.monomial n r, isRestricted_monomial c n r⟩

end Monomial
