/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Analysis.Normed.Ring.Ultra
import PhD.TateFredholm.«00_Tate»

/-!
# The integral halo ring `Λ^{>1/p}` — SKELETON (lwx-halo board)

[LWX, Lemma 3.15] introduces `Λ^{>1/p} := Λ⟦pT⁻¹⟧ = ℤ_p⟦T, pT⁻¹⟧` (one weight disc,
so no `ℤ_p[Δ]` factor here) and observes `𝔪_Λ Λ^{>1/p} = (T)`.  The proof of
[LWX, Cor 3.18] unpacks the elements: "if `∑_{m ∈ ℤ} d_m T^m ∈ Λ^{>1/p}`, then
`v(d_m) ≥ max{0, −m}`".  We take that description as the definition:

`HaloInt p` = functions `d : ℤ → ℤ_[p]` with `‖d j‖ ≤ p^{min(0,j)}`, with pointwise
addition, convolution product (a `tsum` over `ℤ`, summable because both tails die), and
the gauge norm `‖d‖ = ⨆ j, ‖d j‖ · p^{−j}` — values in `[0,1]`, the constant embedding
`ℤ_[p] → HaloInt p` isometric, and `T := δ₁` satisfying `‖T·x‖ = p⁻¹·‖x‖` on the nose
(multiplication by `T` is the coefficient shift).  `T^k`-divisibility is the norm bound
`‖x‖ ≤ p^{−k}`, which is [LWX, Lemma 3.15] in the only form the estimate consumes.

The specialization `∑_j ψ(d_j)·T₀^j` at a point `p⁻¹ < ‖T₀‖ < 1` of a complete
ultrametric field is defined here as well; it is power-bounded, not bounded, so no
operator-level base change is stated — [LWX, Cor 3.18] only needs the coefficientwise
estimate `norm_specialize_le`.
-/

open Filter Topology

noncomputable section

namespace LWX

variable (p : ℕ) [Fact p.Prime]

/-- The integral halo ring `Λ^{>1/p} = ℤ_p⟦T, pT⁻¹⟧` of [LWX, Lemma 3.15], one weight
disc, presented coefficientwise per the proof of [LWX, Cor 3.18]: two-sided coefficient
streams `d : ℤ → ℤ_[p]` with `v(d_j) ≥ max(0, −j)`, i.e. `‖d j‖ ≤ p^{min(0,j)}`. -/
structure HaloInt where
  /-- The coefficient stream: `toFun j` is the coefficient of `T^j`. -/
  toFun : ℤ → ℤ_[p]
  /-- The halo bound `v(d_j) ≥ max(0, −j)` ([LWX, proof of Cor 3.18]). -/
  bound' : ∀ j : ℤ, ‖toFun j‖ ≤ (p : ℝ) ^ (min 0 j)

namespace HaloInt

variable {p}

instance : FunLike (HaloInt p) ℤ ℤ_[p] where
  coe := toFun
  coe_injective := by rintro ⟨f, _⟩ ⟨g, _⟩ h; simpa using h

@[ext] theorem ext {f g : HaloInt p} (h : ∀ j, f j = g j) : f = g :=
  DFunLike.ext f g h

theorem bound (f : HaloInt p) (j : ℤ) : ‖f j‖ ≤ (p : ℝ) ^ (min 0 j) := f.bound' j

private theorem pR_pos : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos

private theorem one_lt_pR : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt

/-- Termwise bound for the convolution: `‖f_i·g_{k−i}‖ ≤ p^{min(0,i) + min(0,k−i)}`. -/
private theorem norm_mul_coeff_le (f g : HaloInt p) (k i : ℤ) :
    ‖f i * g (k - i)‖ ≤ (p : ℝ) ^ (min 0 i + min 0 (k - i)) := by
  calc ‖f i * g (k - i)‖ ≤ ‖f i‖ * ‖g (k - i)‖ := norm_mul_le _ _
    _ ≤ (p : ℝ) ^ min 0 i * (p : ℝ) ^ min 0 (k - i) :=
        mul_le_mul (f.bound i) (g.bound _) (norm_nonneg _)
          (zpow_nonneg (pR_pos (p := p)).le _)
    _ = (p : ℝ) ^ (min 0 i + min 0 (k - i)) := (zpow_add₀ (pR_pos (p := p)).ne' _ _).symm

/-- Cofinite decay of a doubly-indexed family bounded by `p` to a sum of three
`min 0 ·` exponents, given that the three exponents cannot all be large on an infinite
set.  The workhorse behind convolution summability and associativity. -/
theorem tendsto_cofinite_of_three_bounds {ι : Type*} (F : ι → ℤ_[p])
    (a b c : ι → ℤ)
    (hbound : ∀ x, ‖F x‖ ≤ (p : ℝ) ^ (min 0 (a x) + min 0 (b x) + min 0 (c x)))
    (hfin : ∀ N : ℤ, {x | -N ≤ a x ∧ -N ≤ b x ∧ -N ≤ c x}.Finite) :
    Filter.Tendsto F Filter.cofinite (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  rw [Filter.eventually_cofinite]
  obtain ⟨N, hN⟩ :=
    exists_pow_lt_of_lt_one hε (inv_lt_one_of_one_lt₀ (one_lt_pR (p := p)))
  refine (hfin N).subset ?_
  intro x hx
  simp only [Set.mem_ofPred_eq, not_lt, dist_zero_right] at hx
  have hb : ε ≤ (p : ℝ) ^ (min 0 (a x) + min 0 (b x) + min 0 (c x)) :=
    hx.trans (hbound x)
  have hpN : (p : ℝ) ^ (-(N : ℤ)) < (p : ℝ) ^ (min 0 (a x) + min 0 (b x) + min 0 (c x)) := by
    refine lt_of_lt_of_le ?_ hb
    rw [zpow_neg, zpow_natCast, ← inv_pow]
    exact hN
  have he : -(N : ℤ) < min 0 (a x) + min 0 (b x) + min 0 (c x) :=
    (zpow_lt_zpow_iff_right₀ one_lt_pR).mp hpN
  have h0a : min 0 (a x) ≤ 0 := min_le_left _ _
  have h0b : min 0 (b x) ≤ 0 := min_le_left _ _
  have h0c : min 0 (c x) ≤ 0 := min_le_left _ _
  have ha' : -(N : ℤ) ≤ min 0 (a x) := by omega
  have hb' : -(N : ℤ) ≤ min 0 (b x) := by omega
  have hc' : -(N : ℤ) ≤ min 0 (c x) := by omega
  exact ⟨(le_min_iff.mp ha').2, (le_min_iff.mp hb').2, (le_min_iff.mp hc').2⟩

/-- The convolution family `i ↦ f_i·g_{k−i}` vanishes cofinitely (both tails, by the halo
bound). -/
theorem tendsto_mul_coeff_cofinite (f g : HaloInt p) (k : ℤ) :
    Filter.Tendsto (fun i : ℤ => f i * g (k - i)) Filter.cofinite (𝓝 0) := by
  refine tendsto_cofinite_of_three_bounds _ (fun i => i) (fun i => k - i) (fun _ => 0)
    (fun i => ?_) (fun N => ?_)
  · simpa using norm_mul_coeff_le f g k i
  · refine (Set.finite_Icc (-N) (k + N)).subset fun i hi => ?_
    obtain ⟨h1, h2, -⟩ := hi
    exact Set.mem_Icc.mpr (by omega)

/-- Source: convolution summability — both tails of `i ↦ f i * g (k − i)` vanish, by the
halo bound; summable by the ultrametric criterion `summable_of_tendsto_cofinite`. -/
theorem summable_mul_coeff (f g : HaloInt p) (k : ℤ) :
    Summable fun i : ℤ => f i * g (k - i) :=
  TateFredholm.summable_of_tendsto_cofinite (tendsto_mul_coeff_cofinite f g k)

instance : Zero (HaloInt p) :=
  ⟨⟨fun _ => 0, fun j => by simpa using (zpow_pos (pR_pos (p := p)) (min 0 j)).le⟩⟩

instance : One (HaloInt p) :=
  ⟨⟨fun j => if j = 0 then 1 else 0, fun j => by
    rcases eq_or_ne j 0 with rfl | h
    · simp
    · simpa [h] using (zpow_pos (pR_pos (p := p)) (min 0 j)).le⟩⟩

instance : Add (HaloInt p) :=
  ⟨fun f g => ⟨fun j => f j + g j, fun j =>
    (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (f.bound j) (g.bound j))⟩⟩

instance : Neg (HaloInt p) :=
  ⟨fun f => ⟨fun j => -(f j), fun j => by simpa using f.bound j⟩⟩

instance : Mul (HaloInt p) :=
  ⟨fun f g => ⟨fun k => ∑' i : ℤ, f i * g (k - i), fun k => by
    refine (TateFredholm.norm_tsum_le_iSup (tendsto_mul_coeff_cofinite f g k)).trans
      (ciSup_le fun i => (norm_mul_coeff_le f g k i).trans ?_)
    refine zpow_le_zpow_right₀ one_lt_pR.le (le_min ?_ ?_)
    · exact add_nonpos (min_le_left _ _) (min_le_left _ _)
    · calc min 0 i + min 0 (k - i) ≤ i + (k - i) :=
            add_le_add (min_le_right _ _) (min_le_right _ _)
        _ = k := by ring⟩⟩

@[simp] theorem coeff_add (f g : HaloInt p) (j : ℤ) : (f + g) j = f j + g j := rfl

@[simp] theorem coeff_zero (j : ℤ) : (0 : HaloInt p) j = 0 := rfl

@[simp] theorem coeff_neg (f : HaloInt p) (j : ℤ) : (-f) j = -(f j) := rfl

theorem coeff_one (j : ℤ) : (1 : HaloInt p) j = if j = 0 then 1 else 0 := rfl

/-- The product is the `ℤ`-convolution ([LWX, Cor 3.18 proof]: multiplication of the
`T`-expansions). -/
theorem coeff_mul (f g : HaloInt p) (k : ℤ) : (f * g) k = ∑' i : ℤ, f i * g (k - i) := rfl

private theorem norm_mul₃_le (f g h : HaloInt p) (a b c : ℤ) :
    ‖f a * g b * h c‖ ≤ (p : ℝ) ^ (min 0 a + min 0 b + min 0 c) := by
  have hab : ‖f a * g b‖ ≤ (p : ℝ) ^ (min 0 a + min 0 b) := by
    calc ‖f a * g b‖ ≤ ‖f a‖ * ‖g b‖ := norm_mul_le _ _
      _ ≤ (p : ℝ) ^ min 0 a * (p : ℝ) ^ min 0 b :=
          mul_le_mul (f.bound a) (g.bound b) (norm_nonneg _)
            (zpow_nonneg (pR_pos (p := p)).le _)
      _ = (p : ℝ) ^ (min 0 a + min 0 b) := (zpow_add₀ (pR_pos (p := p)).ne' _ _).symm
  calc ‖f a * g b * h c‖ ≤ ‖f a * g b‖ * ‖h c‖ := norm_mul_le _ _
    _ ≤ (p : ℝ) ^ (min 0 a + min 0 b) * (p : ℝ) ^ min 0 c :=
        mul_le_mul hab (h.bound c) (norm_nonneg _) (zpow_nonneg (pR_pos (p := p)).le _)
    _ = (p : ℝ) ^ (min 0 a + min 0 b + min 0 c) := (zpow_add₀ (pR_pos (p := p)).ne' _ _).symm

/-- The reindexing `(j, i') ↦ (i' + j, j)` matching the two iterated convolutions. -/
def assocEquiv : ℤ × ℤ ≃ ℤ × ℤ :=
  (Equiv.prodShear (Equiv.refl ℤ) fun j => Equiv.addRight j).trans (Equiv.prodComm ℤ ℤ)

/-- The shear equivalence `assocEquiv` sends `(j, i')` to `(i' + j, j)`. -/
@[simp] theorem assocEquiv_apply (y : ℤ × ℤ) :
    assocEquiv y = (y.2 + y.1, y.1) := rfl

private theorem summable_assoc_left (f g h : HaloInt p) (k : ℤ) :
    Summable fun x : ℤ × ℤ => f x.2 * g (x.1 - x.2) * h (k - x.1) := by
  refine TateFredholm.summable_of_tendsto_cofinite
    (tendsto_cofinite_of_three_bounds _ (fun x => x.2) (fun x => x.1 - x.2)
      (fun x => k - x.1) (fun x => norm_mul₃_le f g h _ _ _) fun N => ?_)
  refine ((Set.finite_Icc (-(2 * N)) (k + N)).prod
    (Set.finite_Icc (-N) (k + 2 * N))).subset fun x hx => ?_
  obtain ⟨h1, h2, h3⟩ := hx
  exact Set.mem_prod.mpr ⟨Set.mem_Icc.mpr (by omega), Set.mem_Icc.mpr (by omega)⟩

private theorem summable_assoc_right (f g h : HaloInt p) (k : ℤ) :
    Summable fun x : ℤ × ℤ => f x.1 * (g x.2 * h (k - x.1 - x.2)) := by
  have heq : ∀ x : ℤ × ℤ, f x.1 * (g x.2 * h (k - x.1 - x.2))
      = f x.1 * g x.2 * h (k - x.1 - x.2) := fun x => (mul_assoc _ _ _).symm
  simp only [heq]
  refine TateFredholm.summable_of_tendsto_cofinite
    (tendsto_cofinite_of_three_bounds _ (fun x => x.1) (fun x => x.2)
      (fun x => k - x.1 - x.2) (fun x => norm_mul₃_le f g h _ _ _) fun N => ?_)
  refine ((Set.finite_Icc (-N) (k + 2 * N)).prod
    (Set.finite_Icc (-N) (k + 2 * N))).subset fun x hx => ?_
  obtain ⟨h1, h2, h3⟩ := hx
  exact Set.mem_prod.mpr ⟨Set.mem_Icc.mpr (by omega), Set.mem_Icc.mpr (by omega)⟩

instance : CommRing (HaloInt p) where
  add := (· + ·)
  zero := 0
  neg := Neg.neg
  mul := (· * ·)
  one := 1
  add_assoc f g h := by ext j; simp [add_assoc]
  zero_add f := by ext j; simp
  add_zero f := by ext j; simp
  add_comm f g := by ext j; simp [add_comm]
  neg_add_cancel f := by ext j; simp
  left_distrib f g h := by
    ext k
    simp only [coeff_mul, coeff_add, mul_add]
    exact (summable_mul_coeff f g k).tsum_add (summable_mul_coeff f h k)
  right_distrib f g h := by
    ext k
    simp only [coeff_mul, coeff_add, add_mul]
    exact (summable_mul_coeff f h k).tsum_add (summable_mul_coeff g h k)
  zero_mul f := by ext k; simp [coeff_mul]
  mul_zero f := by ext k; simp [coeff_mul]
  mul_assoc f g h := by
    ext k
    rw [coeff_mul, coeff_mul]
    have hL : (fun i => (f * g) i * h (k - i))
        = fun i => ∑' j, f j * g (i - j) * h (k - i) := by
      funext i
      rw [coeff_mul, ← (summable_mul_coeff f g i).tsum_mul_right]
    have hR : (fun j => f j * (g * h) (k - j))
        = fun j => ∑' i, f j * (g i * h (k - j - i)) := by
      funext j
      rw [coeff_mul, ← (summable_mul_coeff g h (k - j)).tsum_mul_left]
    have hprodL := (summable_assoc_left f g h k).tsum_prod'
      (h₁ := fun b => (summable_mul_coeff f g b).mul_right (h (k - b)))
    have hprodR := (summable_assoc_right f g h k).tsum_prod'
      (h₁ := fun b => (summable_mul_coeff g h (k - b)).mul_left (f b))
    rw [hL, hR, ← hprodL, ← hprodR,
      ← (assocEquiv).tsum_eq (fun x : ℤ × ℤ => f x.2 * g (x.1 - x.2) * h (k - x.1))]
    refine tsum_congr fun y => ?_
    simp only [assocEquiv_apply, add_sub_cancel_right]
    rw [mul_assoc]
    ring_nf
  one_mul f := by
    ext k
    rw [coeff_mul, tsum_eq_single 0 (fun i hi => by simp [coeff_one, hi])]
    simp [coeff_one]
  mul_one f := by
    ext k
    rw [coeff_mul, tsum_eq_single k (fun i hi => by simp [coeff_one, sub_eq_zero, (Ne.symm hi)])]
    simp [coeff_one]
  mul_comm f g := by
    ext k
    rw [coeff_mul, coeff_mul,
      ← (Equiv.subLeft k).tsum_eq (fun i => f i * g (k - i))]
    exact tsum_congr fun i => by simp [mul_comm]
  nsmul := nsmulRec
  zsmul := zsmulRec

@[simp] theorem coeff_sub (f g : HaloInt p) (j : ℤ) : (f - g) j = f j - g j := by
  rw [sub_eq_add_neg, coeff_add, coeff_neg, sub_eq_add_neg]

/-- The raw gauge functional, before the instance packaging. -/
private def gnorm (f : HaloInt p) : ℝ := ⨆ j : ℤ, ‖f j‖ * (p : ℝ) ^ (-j)

private theorem gterm_le_one (f : HaloInt p) (j : ℤ) : ‖f j‖ * (p : ℝ) ^ (-j) ≤ 1 := by
  calc ‖f j‖ * (p : ℝ) ^ (-j)
      ≤ (p : ℝ) ^ min 0 j * (p : ℝ) ^ (-j) :=
        mul_le_mul_of_nonneg_right (f.bound j) (zpow_nonneg (pR_pos (p := p)).le _)
    _ = (p : ℝ) ^ (min 0 j + -j) := (zpow_add₀ (pR_pos (p := p)).ne' _ _).symm
    _ ≤ (p : ℝ) ^ (0 : ℤ) := zpow_le_zpow_right₀ (one_lt_pR (p := p)).le (by omega)
    _ = 1 := zpow_zero _

private theorem gterm_nonneg (f : HaloInt p) (j : ℤ) :
    0 ≤ ‖f j‖ * (p : ℝ) ^ (-j) :=
  mul_nonneg (norm_nonneg _) (zpow_nonneg (pR_pos (p := p)).le _)

private theorem gnorm_bddAbove (f : HaloInt p) :
    BddAbove (Set.range fun j : ℤ => ‖f j‖ * (p : ℝ) ^ (-j)) :=
  ⟨1, by rintro y ⟨j, rfl⟩; exact gterm_le_one f j⟩

private theorem gterm_le_gnorm (f : HaloInt p) (j : ℤ) :
    ‖f j‖ * (p : ℝ) ^ (-j) ≤ gnorm f :=
  le_ciSup (gnorm_bddAbove f) j

private theorem gnorm_nonneg (f : HaloInt p) : 0 ≤ gnorm f :=
  (gterm_nonneg f 0).trans (gterm_le_gnorm f 0)

private theorem gnorm_le_one (f : HaloInt p) : gnorm f ≤ 1 :=
  ciSup_le (gterm_le_one f)

private theorem gnorm_zero : gnorm (0 : HaloInt p) = 0 := by
  simp [gnorm]

private theorem eq_zero_of_gnorm_eq_zero {f : HaloInt p} (h : gnorm f = 0) : f = 0 := by
  ext j
  have h1 : ‖f j‖ * (p : ℝ) ^ (-j) ≤ 0 := h ▸ gterm_le_gnorm f j
  have h2 : ‖f j‖ ≤ 0 := by
    by_contra hlt
    exact absurd (mul_pos (lt_of_not_ge hlt) (zpow_pos (pR_pos (p := p)) _)) (not_lt.mpr h1)
  simpa using le_antisymm h2 (norm_nonneg _)

private theorem gnorm_add_le_max (f g : HaloInt p) :
    gnorm (f + g) ≤ max (gnorm f) (gnorm g) := by
  refine ciSup_le fun j => ?_
  calc ‖(f + g) j‖ * (p : ℝ) ^ (-j)
      ≤ max ‖f j‖ ‖g j‖ * (p : ℝ) ^ (-j) := by
        rw [coeff_add]
        exact mul_le_mul_of_nonneg_right (IsUltrametricDist.norm_add_le_max _ _)
          (zpow_nonneg (pR_pos (p := p)).le _)
    _ = max (‖f j‖ * (p : ℝ) ^ (-j)) (‖g j‖ * (p : ℝ) ^ (-j)) :=
        max_mul_of_nonneg _ _ (zpow_nonneg (pR_pos (p := p)).le _)
    _ ≤ max (gnorm f) (gnorm g) := max_le_max (gterm_le_gnorm _ j) (gterm_le_gnorm _ j)

private theorem gnorm_neg (f : HaloInt p) : gnorm (-f) = gnorm f := by
  unfold gnorm
  exact iSup_congr fun j => by rw [coeff_neg, norm_neg]

private theorem norm_coeff_le_gnorm_mul (f : HaloInt p) (i : ℤ) :
    ‖f i‖ ≤ gnorm f * (p : ℝ) ^ i := by
  have h := gterm_le_gnorm f i
  calc ‖f i‖ = ‖f i‖ * (p : ℝ) ^ (-i) * (p : ℝ) ^ i := by
        rw [mul_assoc, ← zpow_add₀ (pR_pos (p := p)).ne', neg_add_cancel, zpow_zero,
          mul_one]
    _ ≤ gnorm f * (p : ℝ) ^ i :=
        mul_le_mul_of_nonneg_right h (zpow_pos (pR_pos (p := p)) _).le

private theorem gnorm_mul_le (f g : HaloInt p) : gnorm (f * g) ≤ gnorm f * gnorm g := by
  refine ciSup_le fun k => ?_
  have h1 : ‖(f * g) k‖ ≤ ⨆ i : ℤ, ‖f i * g (k - i)‖ := by
    rw [coeff_mul]
    exact TateFredholm.norm_tsum_le_iSup (tendsto_mul_coeff_cofinite f g k)
  have h2 : (⨆ i : ℤ, ‖f i * g (k - i)‖) ≤ gnorm f * gnorm g * (p : ℝ) ^ k := by
    refine ciSup_le fun i => ?_
    have hik : i + (k - i) = k := by ring
    calc ‖f i * g (k - i)‖ ≤ ‖f i‖ * ‖g (k - i)‖ := norm_mul_le _ _
      _ ≤ gnorm f * (p : ℝ) ^ i * (gnorm g * (p : ℝ) ^ (k - i)) :=
          mul_le_mul (norm_coeff_le_gnorm_mul f i) (norm_coeff_le_gnorm_mul g (k - i))
            (norm_nonneg _)
            (mul_nonneg (gnorm_nonneg _) (zpow_pos (pR_pos (p := p)) _).le)
      _ = gnorm f * gnorm g * (p : ℝ) ^ k := by
          rw [mul_mul_mul_comm, ← zpow_add₀ (pR_pos (p := p)).ne', hik]
  calc ‖(f * g) k‖ * (p : ℝ) ^ (-k)
      ≤ gnorm f * gnorm g * (p : ℝ) ^ k * (p : ℝ) ^ (-k) :=
        mul_le_mul_of_nonneg_right (h1.trans h2) (zpow_pos (pR_pos (p := p)) _).le
    _ = gnorm f * gnorm g := by
        rw [mul_assoc, ← zpow_add₀ (pR_pos (p := p)).ne', add_neg_cancel, zpow_zero,
          mul_one]

/-- The gauge norm as a bundled `AddGroupNorm`: `[LWX, Lemma 3.15]`'s `T`-adic
filtration `𝔪^k Λ^{>1/p} = (T^k)` read as a norm with `‖T‖ = p⁻¹`. -/
private def gaugeNorm : AddGroupNorm (HaloInt p) where
  toFun := gnorm
  map_zero' := gnorm_zero
  add_le' f g := (gnorm_add_le_max f g).trans
    (max_le (le_add_of_nonneg_right (gnorm_nonneg _))
      (le_add_of_nonneg_left (gnorm_nonneg _)))
  neg' := gnorm_neg
  eq_zero_of_map_eq_zero' _ := eq_zero_of_gnorm_eq_zero

instance : NormedAddCommGroup (HaloInt p) := gaugeNorm.toNormedAddCommGroup

theorem norm_def (f : HaloInt p) : ‖f‖ = ⨆ j : ℤ, ‖f j‖ * (p : ℝ) ^ (-j) := rfl

instance : NormedRing (HaloInt p) :=
  { (inferInstance : NormedAddCommGroup (HaloInt p)),
    (inferInstance : Ring (HaloInt p)) with
    norm_mul_le := gnorm_mul_le }

instance : NormedCommRing (HaloInt p) :=
  { (inferInstance : NormedRing (HaloInt p)) with mul_comm := fun f g => mul_comm f g }

/-- **The constant coefficient detects units** (the converse of
`LWX.HaloInt.isUnit_of_isUnit_coeff_zero`, [LWX, Lemma 3.15]).  In the convolution
`(f·g)_0 = ∑_i f_i·g_{−i}` the halo bound makes every term with `i ≠ 0` of norm at most `p⁻¹`
(one of `i`, `−i` is negative), so `(f·g)_0 ≡ f_0·g_0` modulo `p`.  Taking `g = f⁻¹` forces
`‖f_0·g_0‖ = 1`, hence `‖f_0‖ = 1`. -/
theorem isUnit_coeff_zero_of_isUnit {f : HaloInt p} (hf : IsUnit f) : IsUnit (f 0) := by
  obtain ⟨u, hu⟩ := hf
  set g : HaloInt p := ((u⁻¹ : (HaloInt p)ˣ) : HaloInt p) with hgdef
  have hfg : f * g = 1 := by rw [hgdef, ← hu]; exact u.mul_inv
  have hp1 : (1 : ℝ) < p := one_lt_pR (p := p)
  -- Off the diagonal one of `i`, `−i` is negative, so the halo bound gives a factor of `p`.
  have hkey : ‖(1 : ℤ_[p]) - f 0 * g 0‖ ≤ (p : ℝ)⁻¹ := by
    have h := (summable_mul_coeff f g 0).tsum_eq_add_tsum_ite (0 : ℤ)
    rw [← coeff_mul, hfg, coeff_one, if_pos rfl, sub_zero] at h
    rw [show (1 : ℤ_[p]) - f 0 * g 0
      = ∑' n : ℤ, if n = 0 then 0 else f n * g (0 - n) by rw [h]; ring]
    refine (TateFredholm.norm_tsum_le_iSup ?_).trans (ciSup_le fun i => ?_)
    · refine (tendsto_mul_coeff_cofinite f g 0).congr' ?_
      rw [Filter.eventuallyEq_iff_exists_mem]
      refine ⟨{i : ℤ | i ≠ 0}, ?_, fun i hi => (if_neg hi).symm⟩
      rw [Filter.mem_cofinite]
      exact Set.Finite.subset (Set.finite_singleton 0) fun x hx => by simpa using hx
    · rcases eq_or_ne i 0 with rfl | hi
      · rw [if_pos rfl, norm_zero]
        exact (inv_pos.2 (pR_pos (p := p))).le
      · rw [if_neg hi]
        refine (norm_mul_coeff_le f g 0 i).trans ?_
        rw [← zpow_neg_one (p : ℝ)]
        refine zpow_le_zpow_right₀ hp1.le ?_
        rcases lt_or_gt_of_ne hi with h | h
        · rw [min_eq_right h.le, min_eq_left (by omega)]; omega
        · rw [min_eq_left h.le, min_eq_right (by omega)]; omega
  -- Hence `‖f₀·g₀‖ = 1`, and `f₀` is a `p`-adic unit.
  have hlt : ‖(1 : ℤ_[p]) - f 0 * g 0‖ < 1 := hkey.trans_lt (inv_lt_one_of_one_lt₀ hp1)
  have hnorm : ‖f 0 * g 0‖ = 1 := by
    have hne : ‖f 0 * g 0 - 1‖ ≠ ‖(1 : ℤ_[p])‖ := by
      rw [norm_one, ← norm_neg, neg_sub]; exact hlt.ne
    calc ‖f 0 * g 0‖ = ‖(f 0 * g 0 - 1) + 1‖ := by rw [sub_add_cancel]
      _ = max ‖f 0 * g 0 - 1‖ ‖(1 : ℤ_[p])‖ :=
          IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne
      _ = 1 := by
          rw [norm_one, ← norm_neg, neg_sub]
          exact max_eq_right hlt.le
  rw [PadicInt.isUnit_iff]
  refine le_antisymm (by simpa using f.bound 0) ?_
  have hmul := norm_mul_le (f 0) (g 0)
  have hg1 : ‖g 0‖ ≤ 1 := by simpa using g.bound 0
  nlinarith [norm_nonneg (f 0), norm_nonneg (g 0)]

theorem norm_le_one (f : HaloInt p) : ‖f‖ ≤ 1 := gnorm_le_one f

theorem norm_coeff_le_norm (f : HaloInt p) (j : ℤ) :
    ‖f j‖ * (p : ℝ) ^ (-j) ≤ ‖f‖ := gterm_le_gnorm f j

instance : NormOneClass (HaloInt p) := by
  refine ⟨le_antisymm (norm_le_one 1) ?_⟩
  have h := norm_coeff_le_norm (1 : HaloInt p) 0
  simpa [coeff_one] using h

instance : IsUltrametricDist (HaloInt p) := by
  refine ⟨fun f g h => ?_⟩
  rw [dist_eq_norm, dist_eq_norm, dist_eq_norm]
  have hsplit : f - h = (f - g) + (g - h) := by ring
  rw [hsplit]
  exact gnorm_add_le_max (f - g) (g - h)

instance : CompleteSpace (HaloInt p) := by
  refine Metric.complete_of_cauchySeq_tendsto fun u hu => ?_
  -- coefficientwise Cauchy, via the `p^j`-Lipschitz coefficient maps
  have hco : ∀ j : ℤ, CauchySeq fun n => u n j := by
    intro j
    have hlip : LipschitzWith (Real.toNNReal ((p : ℝ) ^ j))
        (fun f : HaloInt p => f j) := by
      refine LipschitzWith.of_dist_le_mul fun f g => ?_
      rw [dist_eq_norm, dist_eq_norm,
        Real.coe_toNNReal _ (zpow_pos (pR_pos (p := p)) _).le, mul_comm]
      calc ‖f j - g j‖ = ‖(f - g) j‖ := by rw [coeff_sub]
        _ ≤ ‖f - g‖ * (p : ℝ) ^ j := norm_coeff_le_gnorm_mul _ j
  -- the coefficientwise limits
    exact (hlip.uniformContinuous.comp_cauchySeq hu)
  choose d hd using fun j => cauchySeq_tendsto_of_complete (hco j)
  have hdb : ∀ j : ℤ, ‖d j‖ ≤ (p : ℝ) ^ (min 0 j) := fun j =>
    le_of_tendsto (hd j).norm (Filter.Eventually.of_forall fun n => (u n).bound j)
  refine ⟨⟨d, hdb⟩, ?_⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hu (ε / 2) (half_pos hε)
  refine ⟨N, fun n hn => ?_⟩
  have hbound : ∀ j : ℤ, ‖(u n - ⟨d, hdb⟩ : HaloInt p) j‖ * (p : ℝ) ^ (-j) ≤ ε / 2 := by
    intro j
    have hm : Filter.Tendsto (fun m => ‖u n j - u m j‖ * (p : ℝ) ^ (-j)) atTop
        (𝓝 (‖u n j - d j‖ * (p : ℝ) ^ (-j))) :=
      ((tendsto_const_nhds.sub (hd j)).norm).mul_const _
    have hev : ∀ᶠ m in atTop, ‖u n j - u m j‖ * (p : ℝ) ^ (-j) ≤ ε / 2 := by
      filter_upwards [Filter.eventually_ge_atTop N] with m hm'
      calc ‖u n j - u m j‖ * (p : ℝ) ^ (-j) = ‖(u n - u m) j‖ * (p : ℝ) ^ (-j) := by
            rw [coeff_sub]
        _ ≤ ‖u n - u m‖ := norm_coeff_le_norm _ j
        _ = dist (u n) (u m) := (dist_eq_norm _ _).symm
        _ ≤ ε / 2 := (hN n hn m hm').le
    calc ‖(u n - ⟨d, hdb⟩ : HaloInt p) j‖ * (p : ℝ) ^ (-j)
        = ‖u n j - d j‖ * (p : ℝ) ^ (-j) := by rw [coeff_sub]; rfl
      _ ≤ ε / 2 := le_of_tendsto hm hev
  have hle : dist (u n) (⟨d, hdb⟩ : HaloInt p) ≤ ε / 2 := by
    rw [dist_eq_norm, norm_def]
    exact ciSup_le hbound
  exact lt_of_le_of_lt hle (half_lt_self hε)

/-- The `T^k`-divisibility criterion, coefficientwise ([LWX, Lemma 3.15] +
[LWX, Cor 3.18 proof]): `‖f‖ ≤ p^{−k}` iff every coefficient satisfies
`‖f j‖ ≤ p^{j−k}`. -/
theorem norm_le_zpow_iff (f : HaloInt p) (k : ℤ) :
    ‖f‖ ≤ (p : ℝ) ^ (-k) ↔ ∀ j : ℤ, ‖f j‖ ≤ (p : ℝ) ^ (j - k) := by
  rw [norm_def, ciSup_le_iff (gnorm_bddAbove f)]
  refine forall_congr' fun j => ?_
  rw [← le_div_iff₀ (zpow_pos (pR_pos (p := p)) (-j)),
    ← zpow_sub₀ (pR_pos (p := p)).ne']
  have hjk : -k - -j = j - k := by ring
  rw [hjk]

/-- The variable `T` — the coefficient-of-`T¹` delta stream. -/
def T : HaloInt p :=
  ⟨fun j => if j = 1 then 1 else 0, fun j => by
    rcases eq_or_ne j 1 with rfl | h
    · simp
    · simpa [h] using (zpow_pos (pR_pos (p := p)) (min 0 j)).le⟩

@[simp] theorem coeff_T (j : ℤ) : (T : HaloInt p) j = if j = 1 then 1 else 0 := rfl

/-- Multiplication by `T` is the coefficient shift. -/
theorem coeff_T_mul (f : HaloInt p) (j : ℤ) : (T * f : HaloInt p) j = f (j - 1) := by
  rw [coeff_mul, tsum_eq_single 1 (fun i hi => by simp [hi])]
  simp

/-- Multiplication by `T^k` is the `k`-fold coefficient shift. -/
theorem coeff_T_pow_mul (f : HaloInt p) (k : ℕ) (j : ℤ) :
    (T ^ k * f : HaloInt p) j = f (j - k) := by
  induction k generalizing j with
  | zero => simp
  | succ k ih =>
      rw [pow_succ', mul_assoc, coeff_T_mul, ih]
      congr 1
      push_cast
      ring

/-- `‖T * f‖ = p⁻¹ * ‖f‖` exactly — `T` acts as a pseudo-uniformizer would, without
being a unit. -/
theorem norm_T_mul (f : HaloInt p) : ‖T * f‖ = (p : ℝ)⁻¹ * ‖f‖ := by
  refine le_antisymm ?_ ?_
  · rw [norm_def]
    refine ciSup_le fun j => ?_
    rw [coeff_T_mul]
    calc ‖f (j - 1)‖ * (p : ℝ) ^ (-j)
        = ‖f (j - 1)‖ * (p : ℝ) ^ (-(j - 1)) * (p : ℝ)⁻¹ := by
          rw [mul_assoc, ← zpow_neg_one, ← zpow_add₀ (pR_pos (p := p)).ne']
          congr 2
          ring
      _ ≤ ‖f‖ * (p : ℝ)⁻¹ :=
          mul_le_mul_of_nonneg_right (norm_coeff_le_norm f (j - 1))
            (by positivity)
      _ = (p : ℝ)⁻¹ * ‖f‖ := mul_comm _ _
  · rw [norm_def (f := f), Real.mul_iSup_of_nonneg (by positivity)]
    refine ciSup_le fun j => ?_
    have hc : (T * f : HaloInt p) (j + 1) = f j := by
      rw [coeff_T_mul, add_sub_cancel_right]
    calc (p : ℝ)⁻¹ * (‖f j‖ * (p : ℝ) ^ (-j))
        = ‖(T * f : HaloInt p) (j + 1)‖ * (p : ℝ) ^ (-(j + 1)) := by
          rw [hc, mul_comm ((p : ℝ)⁻¹), mul_assoc, ← zpow_neg_one,
            ← zpow_add₀ (pR_pos (p := p)).ne']
          congr 2
          ring
      _ ≤ ‖T * f‖ := norm_coeff_le_norm _ _

/-- `T^k`-divisibility from the norm bound: [LWX, Lemma 3.15] in the direction the
statement of Theorem 3.16 uses (`c_n ∈ T^{λ(n)} Λ^{>1/p}`). -/
theorem exists_T_pow_mul_of_norm_le {f : HaloInt p} {k : ℕ}
    (h : ‖f‖ ≤ (p : ℝ) ^ (-(k : ℤ))) : ∃ g : HaloInt p, f = T ^ k * g := by
  have hcoeff := (norm_le_zpow_iff f k).mp h
  refine ⟨⟨fun j => f (j + k), fun j => ?_⟩, ?_⟩
  · rcases le_or_gt 0 j with hj | hj
    · have := f.bound (j + k)
      calc ‖f (j + k)‖ ≤ (p : ℝ) ^ (min 0 (j + k)) := this
        _ ≤ (p : ℝ) ^ (min 0 j) :=
            zpow_le_zpow_right₀ (one_lt_pR (p := p)).le (by omega)
    · calc ‖f (j + k)‖ ≤ (p : ℝ) ^ (j + k - k) := hcoeff (j + k)
        _ = (p : ℝ) ^ (min 0 j) := by congr 1; omega
  · ext j
    rw [coeff_T_pow_mul]
    show f j = f (j - k + k)
    rw [sub_add_cancel]

/-- Norm bound from `T^k`-divisibility (converse direction). -/
theorem norm_le_of_eq_T_pow_mul {f g : HaloInt p} {k : ℕ} (h : f = T ^ k * g) :
    ‖f‖ ≤ (p : ℝ) ^ (-(k : ℤ)) := by
  refine (norm_le_zpow_iff f k).mpr fun j => ?_
  rw [h, coeff_T_pow_mul]
  calc ‖g (j - k)‖ ≤ (p : ℝ) ^ (min 0 (j - k)) := g.bound _
    _ ≤ (p : ℝ) ^ (j - k) :=
        zpow_le_zpow_right₀ (one_lt_pR (p := p)).le (min_le_right _ _)

/-- The constant embedding `ℤ_[p] → HaloInt p` (coefficient of `T⁰`); isometric by the
choice `‖T‖ = p⁻¹`. -/
def const (x : ℤ_[p]) : HaloInt p :=
  ⟨fun j => if j = 0 then x else 0, fun j => by
    rcases eq_or_ne j 0 with rfl | h
    · simpa using x.2
    · simpa [h] using (zpow_pos (pR_pos (p := p)) (min 0 j)).le⟩

@[simp] theorem coeff_const (x : ℤ_[p]) (j : ℤ) :
    (const x : HaloInt p) j = if j = 0 then x else 0 := rfl

theorem norm_const (x : ℤ_[p]) : ‖(const x : HaloInt p)‖ = ‖x‖ := by
  refine le_antisymm (ciSup_le fun j => ?_) ?_
  · rcases eq_or_ne j 0 with rfl | h
    · simp
    · simp [h, norm_nonneg]
  · have h := norm_coeff_le_norm (const x : HaloInt p) 0
    simpa using h

theorem const_mul (x y : ℤ_[p]) : (const (x * y) : HaloInt p) = const x * const y := by
  ext k
  rw [coeff_mul, tsum_eq_single 0 (fun i hi => by simp [hi])]
  rcases eq_or_ne k 0 with rfl | h
  · simp
  · simp [h]

/-- Multiplication by a constant is coefficientwise. -/
theorem coeff_const_mul (x : ℤ_[p]) (f : HaloInt p) (k : ℤ) :
    (const x * f : HaloInt p) k = x * f k := by
  rw [coeff_mul, tsum_eq_single 0 (fun i hi => by simp [hi])]
  simp

/-- The constant embedding as a ring homomorphism. -/
def constRingHom : ℤ_[p] →+* HaloInt p where
  toFun := const
  map_one' := by
    ext j
    rw [coeff_const, coeff_one]
  map_mul' := const_mul
  map_zero' := by
    ext j
    rw [coeff_const, coeff_zero]
    split_ifs <;> rfl
  map_add' x y := by
    ext j
    rw [coeff_add, coeff_const, coeff_const, coeff_const]
    split_ifs <;> simp

@[simp] theorem constRingHom_apply (x : ℤ_[p]) : (constRingHom : ℤ_[p] →+* HaloInt p) x = const x :=
  rfl

/-- `Λ^{>1/p}` is a `ℤ_p`-algebra through the constant embedding. -/
instance : Algebra ℤ_[p] (HaloInt p) := (constRingHom (p := p)).toAlgebra

theorem smul_def (x : ℤ_[p]) (f : HaloInt p) : x • f = const x * f := rfl

/-- The `ℤ_p`-scalar action is bounded (the constant embedding is isometric). -/
instance : IsBoundedSMul ℤ_[p] (HaloInt p) :=
  .of_norm_smul_le fun x f => by
    rw [smul_def, ← norm_const (p := p) x]
    exact norm_mul_le _ _

section Specialize

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- Specialization at a point `T₀` of the open halo annulus: `f ↦ ∑_j ψ(f j)·T₀^j`
([LWX, Cor 3.18]: evaluation of the `T`-expansion at `T = T₀`). -/
def specialize (ψ : ℤ_[p] →+* K) (T₀ : K) (f : HaloInt p) : K :=
  ∑' j : ℤ, ψ (f j) * T₀ ^ j

omit [IsUltrametricDist K] [CompleteSpace K] in
private theorem norm_spec_term (ψ : ℤ_[p] →+* K) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (T₀ : K)
    (f : HaloInt p) (j : ℤ) : ‖ψ (f j) * T₀ ^ j‖ = ‖f j‖ * ‖T₀‖ ^ j := by
  rw [norm_mul, hψ, norm_zpow]

omit [IsUltrametricDist K] [CompleteSpace K] in
private theorem one_lt_p_mul {T₀ : K} (h0 : (p : ℝ)⁻¹ < ‖T₀‖) :
    1 < (p : ℝ) * ‖T₀‖ := by
  calc (1 : ℝ) = (p : ℝ) * (p : ℝ)⁻¹ :=
        (mul_inv_cancel₀ (pR_pos (p := p)).ne').symm
    _ < (p : ℝ) * ‖T₀‖ := mul_lt_mul_of_pos_left h0 (pR_pos (p := p))

omit [IsUltrametricDist K] [CompleteSpace K] in
private theorem tendsto_spec_cofinite (ψ : ℤ_[p] →+* K) (hψ : ∀ x, ‖ψ x‖ = ‖x‖)
    {T₀ : K} (h0 : (p : ℝ)⁻¹ < ‖T₀‖) (h1 : ‖T₀‖ < 1) (f : HaloInt p) :
    Filter.Tendsto (fun j : ℤ => ψ (f j) * T₀ ^ j) Filter.cofinite (𝓝 0) := by
  have hr0 : (0 : ℝ) < ‖T₀‖ := lt_trans (inv_pos.mpr (pR_pos (p := p))) h0
  have hpr := one_lt_p_mul (p := p) h0
  rw [Metric.tendsto_nhds]
  intro ε hε
  rw [Filter.eventually_cofinite]
  obtain ⟨M1, hM1⟩ := exists_pow_lt_of_lt_one hε h1
  obtain ⟨M2, hM2⟩ := exists_pow_lt_of_lt_one hε (inv_lt_one_of_one_lt₀ hpr)
  refine (Set.finite_Icc (-(M2 : ℤ)) (M1 : ℤ)).subset fun j hj => ?_
  simp only [Set.mem_ofPred_eq, not_lt, dist_zero_right] at hj
  rw [norm_spec_term ψ hψ T₀ f j] at hj
  by_contra hout
  rw [Set.mem_Icc, not_and_or] at hout
  have hsmall : ‖f j‖ * ‖T₀‖ ^ j < ε := by
    rcases hout with hlt | hgt
    · -- left tail: j < −M2, term ≤ (p·‖T₀‖)^j
      rw [not_le] at hlt
      calc ‖f j‖ * ‖T₀‖ ^ j
          ≤ (p : ℝ) ^ j * ‖T₀‖ ^ j :=
            mul_le_mul_of_nonneg_right ((f.bound j).trans
              (zpow_le_zpow_right₀ (one_lt_pR (p := p)).le (min_le_right _ _)))
              (zpow_nonneg hr0.le _)
        _ = ((p : ℝ) * ‖T₀‖) ^ j := (mul_zpow _ _ _).symm
        _ ≤ ((p : ℝ) * ‖T₀‖) ^ (-(M2 : ℤ)) := zpow_le_zpow_right₀ hpr.le (by omega)
        _ = ((p : ℝ) * ‖T₀‖)⁻¹ ^ M2 := by rw [zpow_neg, zpow_natCast, ← inv_pow]
        _ < ε := hM2
    · -- right tail: M1 < j, term ≤ ‖T₀‖^j
      rw [not_le] at hgt
      have h1' : ‖f j‖ ≤ 1 := (f.bound j).trans
        ((zpow_le_zpow_right₀ (one_lt_pR (p := p)).le (min_le_left 0 j)).trans_eq
          (zpow_zero _))
      calc ‖f j‖ * ‖T₀‖ ^ j
          ≤ 1 * ‖T₀‖ ^ j := mul_le_mul_of_nonneg_right h1' (zpow_nonneg hr0.le _)
        _ = ‖T₀‖ ^ j := one_mul _
        _ ≤ ‖T₀‖ ^ (M1 : ℤ) := zpow_le_zpow_right_of_le_one₀ hr0 h1.le (by omega)
        _ = ‖T₀‖ ^ M1 := zpow_natCast _ _
        _ < ε := hM1
  exact absurd hj (not_le.mpr hsmall)

/-- Summability of the specialization series on the open annulus `p⁻¹ < ‖T₀‖ < 1`. -/
theorem summable_specialize (ψ : ℤ_[p] →+* K) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) {T₀ : K}
    (h0 : (p : ℝ)⁻¹ < ‖T₀‖) (h1 : ‖T₀‖ < 1) (f : HaloInt p) :
    Summable fun j : ℤ => ψ (f j) * T₀ ^ j :=
  TateFredholm.summable_of_tendsto_cofinite (tendsto_spec_cofinite ψ hψ h0 h1 f)

/-- **The [LWX, Cor 3.18] computation**: if `‖f‖ ≤ p^{−k}` (i.e. `f ∈ T^k Λ^{>1/p}`),
then `v(f(T₀)) ≥ k·v(T₀)` for every `T₀` with `0 < v(T₀) < 1` — from
`v(d_m T₀^m) ≥ max(k−m, 0) + m·v(T₀) ≥ k·v(T₀)`. -/
theorem norm_specialize_le (ψ : ℤ_[p] →+* K) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) {T₀ : K}
    (h0 : (p : ℝ)⁻¹ < ‖T₀‖) (h1 : ‖T₀‖ < 1) {f : HaloInt p} {k : ℕ}
    (hf : ‖f‖ ≤ (p : ℝ) ^ (-(k : ℤ))) :
    ‖specialize ψ T₀ f‖ ≤ ‖T₀‖ ^ k := by
  have hr0 : (0 : ℝ) < ‖T₀‖ := lt_trans (inv_pos.mpr (pR_pos (p := p))) h0
  have hcoeff := (norm_le_zpow_iff f k).mp hf
  refine (TateFredholm.norm_tsum_le_iSup (tendsto_spec_cofinite ψ hψ h0 h1 f)).trans
    (ciSup_le fun j => ?_)
  rw [norm_spec_term ψ hψ T₀ f j]
  rcases le_or_gt (k : ℤ) j with hkj | hjk
  · -- `j ≥ k`: `‖f j‖ ≤ 1` and `‖T₀‖^j ≤ ‖T₀‖^k`
    have h1' : ‖f j‖ ≤ 1 := (f.bound j).trans
      ((zpow_le_zpow_right₀ (one_lt_pR (p := p)).le (min_le_left 0 j)).trans_eq
        (zpow_zero _))
    calc ‖f j‖ * ‖T₀‖ ^ j ≤ 1 * ‖T₀‖ ^ j :=
          mul_le_mul_of_nonneg_right h1' (zpow_nonneg hr0.le _)
      _ = ‖T₀‖ ^ j := one_mul _
      _ ≤ ‖T₀‖ ^ (k : ℤ) := zpow_le_zpow_right_of_le_one₀ hr0 h1.le hkj
      _ = ‖T₀‖ ^ k := zpow_natCast _ _
  · -- `j < k` ([LWX, (3.18.1)]): `‖f j‖ ≤ p^{j−k}` and `p⁻¹ < ‖T₀‖`
    have hpr := one_lt_p_mul (p := p) h0
    have h1le : (1 : ℝ) ≤ (p : ℝ) ^ ((k : ℤ) - j) * ‖T₀‖ ^ ((k : ℤ) - j) := by
      have h := zpow_le_zpow_right₀ hpr.le (show (0 : ℤ) ≤ (k : ℤ) - j by omega)
      rw [zpow_zero] at h
      calc (1 : ℝ) ≤ ((p : ℝ) * ‖T₀‖) ^ ((k : ℤ) - j) := h
        _ = (p : ℝ) ^ ((k : ℤ) - j) * ‖T₀‖ ^ ((k : ℤ) - j) := mul_zpow _ _ _
    have hkey : (p : ℝ) ^ (j - (k : ℤ)) ≤ ‖T₀‖ ^ ((k : ℤ) - j) := by
      rw [show j - (k : ℤ) = -((k : ℤ) - j) by ring, zpow_neg]
      exact (inv_le_iff_one_le_mul₀ (zpow_pos (pR_pos (p := p)) _)).mpr
        (by rwa [mul_comm] at h1le)
    calc ‖f j‖ * ‖T₀‖ ^ j
        ≤ (p : ℝ) ^ (j - (k : ℤ)) * ‖T₀‖ ^ j :=
          mul_le_mul_of_nonneg_right (hcoeff j) (zpow_nonneg hr0.le _)
      _ ≤ ‖T₀‖ ^ ((k : ℤ) - j) * ‖T₀‖ ^ j :=
          mul_le_mul_of_nonneg_right hkey (zpow_nonneg hr0.le _)
      _ = ‖T₀‖ ^ (k : ℤ) := by
          rw [← zpow_add₀ hr0.ne']
          congr 1
          ring
      _ = ‖T₀‖ ^ k := zpow_natCast _ _

omit [IsUltrametricDist K] [CompleteSpace K] in
@[simp] theorem specialize_one (ψ : ℤ_[p] →+* K) (T₀ : K) :
    specialize ψ T₀ (1 : HaloInt p) = 1 := by
  rw [specialize, tsum_eq_single 0 (fun j hj => by simp [coeff_one, hj])]
  simp [coeff_one]

end Specialize

end HaloInt

end LWX
