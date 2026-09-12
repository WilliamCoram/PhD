/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.Main.LWX.«00_HaloRing»

/-!
# The Banach–Tate ring `A = Λ^{>1/p}[1/T]`

The localisation of the integral halo ring `HaloInt p = ℤ_p⟦T, pT⁻¹⟧` ([LWX, Lemma 3.15])
at `T`, realised concretely: two-sided coefficient streams `d : ℤ → ℤ_[p]` with
`‖d j‖ ≤ p^{min(0, j+k)}` for some `k` (i.e. `T^k d ∈ HaloInt p`), with the gauge norm
`‖d‖ = ⨆ j, ‖d j‖ p^{−j}` extended from `00_HaloRing.lean`.  `T` becomes a unit with
`‖T·x‖ = p⁻¹‖x‖`, so it is a *multiplicative pseudo-uniformizer* in the sense of [JN]
Definition 2.1.2, and `A` is a Banach–Tate ring — the coefficient ring over which [JN]
§2.2 applies to the halo `U_p`.

No Noetherian hypothesis is claimed or needed: the Riesz–Coleman theory of
`PhD/Main/TateFredholm/12_RieszColeman.lean` is Noetherian-free.

## Main definitions

* `LWX.HaloTate`: the ring `A`, as coefficient streams with a shifted halo bound.
* `LWX.HaloTate.ofInt`, `LWX.HaloTate.ofIntRingHom`: the isometric embedding of `HaloInt p`.
* `LWX.HaloTate.T`: the variable `T` as a unit of `A`.
* `LWX.HaloTate.pseudoUniformizer`: `T` as a multiplicative pseudo-uniformizer.

## Main results

* `LWX.HaloTate.instCompleteSpace`: `A` is complete for the gauge norm.
* `LWX.HaloTate.norm_le_one_iff`: the unit ball of `A` is `HaloInt p`.
* `LWX.HaloTate.norm_T_mul`: `‖T·f‖ = p⁻¹‖f‖`.
* `LWX.HaloTate.instIsTate`: `A` is a Banach–Tate ring ([JN] Definition 2.1.2).
* `LWX.HaloTate.exists_T_zpow_mul_ofInt`: every element is `T^{−k}` times an integral one.

## References

* [JN] Johansson–Newton, *Extended eigenvarieties for overconvergent cohomology*, §2.1.
* [LWX] Liu–Wan–Xiao, *The eigencurve over the boundary of weight space*, Lemma 3.15.
-/
open Filter Topology

noncomputable section

namespace LWX

variable (p : ℕ) [hp : Fact p.Prime]

/-- `A = Λ^{>1/p}[1/T]` as coefficient streams: `‖d j‖ ≤ p^{min(0, j + k)}` for some `k`,
i.e. `T^k·d ∈ Λ^{>1/p}`. -/
structure HaloTate where
  /-- The coefficient stream: `toFun j` is the coefficient of `T^j`. -/
  toFun : ℤ → ℤ_[p]
  /-- Some `T`-power multiple lies in the integral halo ring. -/
  exists_bound' : ∃ k : ℕ, ∀ j : ℤ, ‖toFun j‖ ≤ (p : ℝ) ^ (min 0 (j + k))

namespace HaloTate

variable {p}

instance : FunLike (HaloTate p) ℤ ℤ_[p] where
  coe := toFun
  coe_injective := by rintro ⟨f, _⟩ ⟨g, _⟩ h; simpa using h

/-- Two elements of `A` agree once all their coefficients agree. -/
@[ext] theorem ext {f g : HaloTate p} (h : ∀ j, f j = g j) : f = g :=
  DFunLike.ext f g h

/-- The defining property of `A`: some `T`-power multiple of `f` is integral, i.e. the
coefficients satisfy the halo bound shifted by `k`.  The `k` is not unique; use `exists_bound`
only to destructure, and `norm_le_one_iff` for the exact unit ball. -/
theorem exists_bound (f : HaloTate p) : ∃ k : ℕ, ∀ j : ℤ, ‖f j‖ ≤ (p : ℝ) ^ (min 0 (j + k)) :=
  f.exists_bound'

private theorem one_lt_cast_p : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt

private theorem cast_p_pos : (0 : ℝ) < p := zero_lt_one.trans one_lt_cast_p

private theorem norm_mul_le_zpow {x y : ℤ_[p]} {m n : ℤ} (hx : ‖x‖ ≤ (p : ℝ) ^ m)
    (hy : ‖y‖ ≤ (p : ℝ) ^ n) : ‖x * y‖ ≤ (p : ℝ) ^ (m + n) :=
  (norm_mul_le_of_le hx hy).trans_eq (zpow_add₀ cast_p_pos.ne' _ _).symm

private theorem norm_single_le {j₀ : ℤ} {k : ℕ} (hjk : j₀ + k = 0) (j : ℤ) :
    ‖(if j = j₀ then (1 : ℤ_[p]) else 0)‖ ≤ (p : ℝ) ^ (min 0 (j + k)) := by
  split_ifs with h <;> simp [h, hjk, zpow_nonneg cast_p_pos.le]

/-- Every coefficient of an element of `A` is `p`-integral. -/
theorem norm_coeff_le_one (f : HaloTate p) (j : ℤ) : ‖f j‖ ≤ 1 := PadicInt.norm_le_one _

/-- The integral halo ring embeds: streams with `k = 0`. -/
def ofInt (x : HaloInt p) : HaloTate p :=
  ⟨fun j ↦ x j, ⟨0, fun j ↦ by simpa using x.bound j⟩⟩

/-- The embedding `HaloInt p → A` does not change coefficients. -/
@[simp] theorem coeff_ofInt (x : HaloInt p) (j : ℤ) : (ofInt x : HaloTate p) j = x j := rfl

/-- The embedding `HaloInt p → A` is injective. -/
theorem ofInt_injective : Function.Injective (ofInt : HaloInt p → HaloTate p) :=
  fun _ _ h ↦ HaloInt.ext fun j ↦ congrArg (fun f : HaloTate p ↦ f j) h

private theorem norm_mul_coeff_le {f g : HaloTate p} {k₁ k₂ : ℕ}
    (hf : ∀ j : ℤ, ‖f j‖ ≤ (p : ℝ) ^ (min 0 (j + k₁)))
    (hg : ∀ j : ℤ, ‖g j‖ ≤ (p : ℝ) ^ (min 0 (j + k₂))) (a b : ℤ) :
    ‖f a * g b‖ ≤ (p : ℝ) ^ (min 0 (a + k₁) + min 0 (b + k₂)) :=
  norm_mul_le_zpow (hf a) (hg b)

private theorem tendsto_mul_coeff_cofinite (f g : HaloTate p) (k : ℤ) :
    Filter.Tendsto (fun i : ℤ ↦ f i * g (k - i)) Filter.cofinite (𝓝 0) := by
  obtain ⟨k₁, hf⟩ := f.exists_bound
  obtain ⟨k₂, hg⟩ := g.exists_bound
  exact HaloInt.tendsto_cofinite_of_three_bounds _ (fun i ↦ i + k₁) (fun i ↦ k - i + k₂)
    (fun _ ↦ 0) (fun i ↦ by simpa using norm_mul_coeff_le hf hg i (k - i)) fun N ↦
    (Set.finite_Icc (-N - k₁) (k + N + k₂)).subset fun i ⟨h1, h2, _⟩ ↦ Set.mem_Icc.mpr (by omega)

/-- Convolution summability: both tails of `i ↦ f i * g (k − i)` vanish (the shifted halo
bounds; `TateFredholm.summable_of_tendsto_cofinite`). -/
theorem summable_mul_coeff (f g : HaloTate p) (k : ℤ) :
    Summable fun i : ℤ ↦ f i * g (k - i) :=
  TateFredholm.summable_of_tendsto_cofinite (tendsto_mul_coeff_cofinite f g k)

instance : Zero (HaloTate p) :=
  ⟨⟨fun _ ↦ 0, ⟨0, fun _ ↦ norm_zero.trans_le (zpow_nonneg cast_p_pos.le _)⟩⟩⟩

instance : One (HaloTate p) := ⟨⟨fun j ↦ if j = 0 then 1 else 0, 0, norm_single_le (by simp)⟩⟩

instance : Add (HaloTate p) :=
  ⟨fun f g ↦ ⟨fun j ↦ f j + g j, by
    obtain ⟨k₁, hf⟩ := f.exists_bound
    obtain ⟨k₂, hg⟩ := g.exists_bound
    refine ⟨max k₁ k₂, fun j ↦ (IsUltrametricDist.norm_add_le_max _ _).trans
      (max_le ((hf j).trans ?_) ((hg j).trans ?_))⟩ <;>
    exact zpow_le_zpow_right₀ one_lt_cast_p.le (by omega)⟩⟩

instance : Neg (HaloTate p) :=
  ⟨fun f ↦ ⟨fun j ↦ -(f j), f.exists_bound.imp fun _ hf j ↦ (norm_neg _).trans_le (hf j)⟩⟩

instance : Mul (HaloTate p) :=
  ⟨fun f g ↦ ⟨fun k ↦ ∑' i : ℤ, f i * g (k - i), by
    obtain ⟨k₁, hf⟩ := f.exists_bound
    obtain ⟨k₂, hg⟩ := g.exists_bound
    refine ⟨k₁ + k₂, fun k ↦ (TateFredholm.norm_tsum_le_iSup
      (tendsto_mul_coeff_cofinite f g k)).trans (ciSup_le fun i ↦ ?_)⟩
    exact (norm_mul_coeff_le hf hg i (k - i)).trans
      (zpow_le_zpow_right₀ one_lt_cast_p.le (by push_cast; omega))⟩⟩

/-- Addition in `A` is coefficientwise. -/
@[simp] theorem coeff_add (f g : HaloTate p) (j : ℤ) : (f + g) j = f j + g j := rfl

/-- All coefficients of `0 : A` vanish. -/
@[simp] theorem coeff_zero (j : ℤ) : (0 : HaloTate p) j = 0 := rfl

/-- Negation in `A` is coefficientwise. -/
@[simp] theorem coeff_neg (f : HaloTate p) (j : ℤ) : (-f) j = -(f j) := rfl

/-- `1 : A` is the stream supported at `j = 0`.  Not a `simp` lemma: the `if` is rarely the
useful normal form; rewrite with it explicitly. -/
theorem coeff_one (j : ℤ) : (1 : HaloTate p) j = if j = 0 then 1 else 0 := rfl

/-- Multiplication in `A` is the Cauchy product (a convergent `tsum` by `summable_mul_coeff`). -/
theorem coeff_mul (f g : HaloTate p) (k : ℤ) : (f * g) k = ∑' i : ℤ, f i * g (k - i) := rfl

private theorem norm_mul₃_coeff_le {f g h : HaloTate p} {k₁ k₂ k₃ : ℕ}
    (hf : ∀ j : ℤ, ‖f j‖ ≤ (p : ℝ) ^ (min 0 (j + k₁)))
    (hg : ∀ j : ℤ, ‖g j‖ ≤ (p : ℝ) ^ (min 0 (j + k₂)))
    (hh : ∀ j : ℤ, ‖h j‖ ≤ (p : ℝ) ^ (min 0 (j + k₃))) (a b c : ℤ) :
    ‖f a * g b * h c‖ ≤ (p : ℝ) ^ (min 0 (a + k₁) + min 0 (b + k₂) + min 0 (c + k₃)) :=
  norm_mul_le_zpow (norm_mul_coeff_le hf hg a b) (hh c)

private theorem summable_assoc_left (f g h : HaloTate p) (k : ℤ) :
    Summable fun x : ℤ × ℤ ↦ f x.2 * g (x.1 - x.2) * h (k - x.1) := by
  obtain ⟨k₁, hf⟩ := f.exists_bound
  obtain ⟨k₂, hg⟩ := g.exists_bound
  obtain ⟨k₃, hh⟩ := h.exists_bound
  refine TateFredholm.summable_of_tendsto_cofinite
    (HaloInt.tendsto_cofinite_of_three_bounds _ (fun x ↦ x.2 + k₁) (fun x ↦ x.1 - x.2 + k₂)
      (fun x ↦ k - x.1 + k₃) (fun x ↦ norm_mul₃_coeff_le hf hg hh _ _ _) fun N ↦
      ((Set.finite_Icc (-(2 * N) - k₁ - k₂) (k + N + k₃)).prod
        (Set.finite_Icc (-N - k₁) (k + 2 * N + k₂ + k₃))).subset fun x ⟨h1, h2, h3⟩ ↦
          ⟨Set.mem_Icc.mpr (by omega), Set.mem_Icc.mpr (by omega)⟩)

private theorem summable_assoc_right (f g h : HaloTate p) (k : ℤ) :
    Summable fun x : ℤ × ℤ ↦ f x.1 * (g x.2 * h (k - x.1 - x.2)) := by
  refine ((HaloInt.assocEquiv.summable_iff
    (f := fun x : ℤ × ℤ ↦ f x.2 * g (x.1 - x.2) * h (k - x.1))).mpr
    (summable_assoc_left f g h k)).congr fun y ↦ ?_
  simp only [Function.comp_apply, HaloInt.assocEquiv_apply, add_sub_cancel_right]
  ring_nf

private theorem mul_assoc_aux (f g h : HaloTate p) : f * g * h = f * (g * h) := by
  ext k
  rw [coeff_mul, coeff_mul]
  have hL : (fun i ↦ (f * g) i * h (k - i)) = fun i ↦ ∑' j, f j * g (i - j) * h (k - i) :=
    funext fun i ↦ by rw [coeff_mul, ← (summable_mul_coeff f g i).tsum_mul_right]
  have hR : (fun j ↦ f j * (g * h) (k - j)) = fun j ↦ ∑' i, f j * (g i * h (k - j - i)) :=
    funext fun j ↦ by rw [coeff_mul, ← (summable_mul_coeff g h (k - j)).tsum_mul_left]
  rw [hL, hR,
    ← (summable_assoc_left f g h k).tsum_prod'
      (h₁ := fun b ↦ (summable_mul_coeff f g b).mul_right (h (k - b))),
    ← (summable_assoc_right f g h k).tsum_prod'
      (h₁ := fun b ↦ (summable_mul_coeff g h (k - b)).mul_left (f b)),
    ← HaloInt.assocEquiv.tsum_eq fun x : ℤ × ℤ ↦ f x.2 * g (x.1 - x.2) * h (k - x.1)]
  refine tsum_congr fun y ↦ ?_
  simp only [HaloInt.assocEquiv_apply, add_sub_cancel_right]
  ring_nf

/-- The commutative ring structure (mirror of `HaloInt`'s: associativity by
`Summable.tsum_prod'` over the shear equivalence, commutativity by `Equiv.subLeft`). -/
instance : CommRing (HaloTate p) where
  add_assoc _ _ _ := by ext; simp [add_assoc]
  zero_add _ := by ext; simp
  add_zero _ := by ext; simp
  add_comm _ _ := by ext; simp [add_comm]
  neg_add_cancel _ := by ext; simp
  nsmul := nsmulRec
  zsmul := zsmulRec
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
  mul_assoc := mul_assoc_aux
  one_mul f := by
    ext k
    rw [coeff_mul, tsum_eq_single 0 fun i hi ↦ by simp [coeff_one, hi]]
    simp [coeff_one]
  mul_one f := by
    ext k
    rw [coeff_mul, tsum_eq_single k fun i hi ↦ by simp [coeff_one, sub_eq_zero, hi.symm]]
    simp [coeff_one]
  mul_comm f g := by
    ext k
    rw [coeff_mul, coeff_mul, ← (Equiv.subLeft k).tsum_eq fun i ↦ f i * g (k - i)]
    exact tsum_congr fun i ↦ by simp [mul_comm]

/-- Subtraction in `A` is coefficientwise. -/
@[simp] theorem coeff_sub (f g : HaloTate p) (j : ℤ) : (f - g) j = f j - g j := by
  rw [sub_eq_add_neg, coeff_add, coeff_neg, sub_eq_add_neg]

/-- `ofInt` is a ring homomorphism (the ring operations are the same convolutions). -/
def ofIntRingHom : HaloInt p →+* HaloTate p where
  toFun := ofInt
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The ring-homomorphism packaging of `ofInt` acts as `ofInt`. -/
@[simp] theorem ofIntRingHom_apply (x : HaloInt p) : ofIntRingHom x = ofInt x := rfl

private def gnorm (f : HaloTate p) : ℝ := ⨆ j : ℤ, ‖f j‖ * (p : ℝ) ^ (-j)

private theorem gterm_nonneg (f : HaloTate p) (j : ℤ) : 0 ≤ ‖f j‖ * (p : ℝ) ^ (-j) :=
  mul_nonneg (norm_nonneg _) (zpow_nonneg cast_p_pos.le _)

private theorem gterm_le_of_bound {f : HaloTate p} {k : ℕ}
    (hf : ∀ j : ℤ, ‖f j‖ ≤ (p : ℝ) ^ (min 0 (j + k))) (j : ℤ) :
    ‖f j‖ * (p : ℝ) ^ (-j) ≤ (p : ℝ) ^ (k : ℤ) :=
  (mul_le_mul_of_nonneg_right (hf j) (zpow_nonneg cast_p_pos.le _)).trans
    ((zpow_add₀ cast_p_pos.ne' _ _).symm.trans_le (zpow_le_zpow_right₀ one_lt_cast_p.le (by omega)))

/-- The gauge terms `‖f j‖ p^{−j}` are bounded (by `p^k` for any shift `k` of `f`), so the gauge
norm is a genuine supremum; this is the `BddAbove` input for `le_ciSup`/`ciSup_le`. -/
theorem bddAbove_range_norm_coeff (f : HaloTate p) :
    BddAbove (Set.range fun j : ℤ ↦ ‖f j‖ * (p : ℝ) ^ (-j)) := by
  obtain ⟨k, hf⟩ := f.exists_bound
  exact ⟨_, Set.forall_mem_range.mpr (gterm_le_of_bound hf)⟩

private theorem gterm_le_gnorm (f : HaloTate p) (j : ℤ) : ‖f j‖ * (p : ℝ) ^ (-j) ≤ gnorm f :=
  le_ciSup (bddAbove_range_norm_coeff f) j

private theorem gnorm_nonneg (f : HaloTate p) : 0 ≤ gnorm f :=
  (gterm_nonneg f 0).trans (gterm_le_gnorm f 0)

private theorem gnorm_zero : gnorm (0 : HaloTate p) = 0 := by
  simp [gnorm]

private theorem eq_zero_of_gnorm_eq_zero {f : HaloTate p} (h : gnorm f = 0) : f = 0 := by
  ext j
  rw [coeff_zero]
  exact norm_le_zero_iff.mp
    (nonpos_of_mul_nonpos_left (h ▸ gterm_le_gnorm f j) (zpow_pos cast_p_pos _))

private theorem gnorm_add_le_max (f g : HaloTate p) : gnorm (f + g) ≤ max (gnorm f) (gnorm g) :=
  ciSup_le fun j ↦ by
    rw [coeff_add]
    refine (mul_le_mul_of_nonneg_right (IsUltrametricDist.norm_add_le_max _ _)
      (zpow_nonneg cast_p_pos.le _)).trans ?_
    rw [max_mul_of_nonneg _ _ (zpow_nonneg cast_p_pos.le _)]
    exact max_le_max (gterm_le_gnorm _ j) (gterm_le_gnorm _ j)

private theorem gnorm_neg (f : HaloTate p) : gnorm (-f) = gnorm f :=
  iSup_congr fun j ↦ by rw [coeff_neg, norm_neg]

private theorem norm_coeff_le_gnorm_mul (f : HaloTate p) (i : ℤ) :
    ‖f i‖ ≤ gnorm f * (p : ℝ) ^ i := by
  rw [← mul_inv_le_iff₀ (zpow_pos cast_p_pos i), ← zpow_neg]
  exact gterm_le_gnorm f i

private theorem gnorm_mul_le (f g : HaloTate p) : gnorm (f * g) ≤ gnorm f * gnorm g :=
  ciSup_le fun k ↦ by
    rw [← le_div_iff₀ (zpow_pos cast_p_pos _), div_eq_mul_inv, ← zpow_neg, neg_neg, coeff_mul]
    refine (TateFredholm.norm_tsum_le_iSup (tendsto_mul_coeff_cofinite f g k)).trans
      (ciSup_le fun i ↦ (norm_mul_le_of_le (norm_coeff_le_gnorm_mul f i)
        (norm_coeff_le_gnorm_mul g (k - i))).trans_eq ?_)
    rw [mul_mul_mul_comm, ← zpow_add₀ cast_p_pos.ne', add_sub_cancel]

private def gaugeNorm : AddGroupNorm (HaloTate p) where
  toFun := gnorm
  map_zero' := gnorm_zero
  add_le' f g := (gnorm_add_le_max f g).trans
    (max_le (le_add_of_nonneg_right (gnorm_nonneg _)) (le_add_of_nonneg_left (gnorm_nonneg _)))
  neg' := gnorm_neg
  eq_zero_of_map_eq_zero' _ := eq_zero_of_gnorm_eq_zero

instance : NormedAddCommGroup (HaloTate p) := gaugeNorm.toNormedAddCommGroup

/-- The norm of `A` is the gauge norm `‖f‖ = ⨆ j, ‖f j‖ p^{−j}`; use `norm_coeff_le_norm` and
`bddAbove_range_norm_coeff` rather than unfolding this. -/
theorem norm_def (f : HaloTate p) : ‖f‖ = ⨆ j : ℤ, ‖f j‖ * (p : ℝ) ^ (-j) := rfl

/-- Each gauge term is at most the norm. -/
theorem norm_coeff_le_norm (f : HaloTate p) (j : ℤ) : ‖f j‖ * (p : ℝ) ^ (-j) ≤ ‖f‖ :=
  gterm_le_gnorm f j

/-- The coefficient bound in terms of the norm: `‖f i‖ ≤ ‖f‖ p^i`. -/
theorem norm_coeff_le_norm_mul (f : HaloTate p) (i : ℤ) : ‖f i‖ ≤ ‖f‖ * (p : ℝ) ^ i :=
  norm_coeff_le_gnorm_mul f i

instance : NormedCommRing (HaloTate p) :=
  { (inferInstance : NormedAddCommGroup (HaloTate p)),
    (inferInstance : CommRing (HaloTate p)) with
    norm_mul_le := gnorm_mul_le }

instance : NormOneClass (HaloTate p) :=
  ⟨le_antisymm (ciSup_le fun j ↦ by by_cases h : j = 0 <;> simp [coeff_one, h])
    (by simpa [coeff_one] using norm_coeff_le_norm (1 : HaloTate p) 0)⟩

instance : IsUltrametricDist (HaloTate p) :=
  IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm gnorm_add_le_max

private theorem coeff_bound_of_norm_le {f : HaloTate p} {K : ℕ} (hf : ‖f‖ ≤ (p : ℝ) ^ (K : ℤ))
    (j : ℤ) : ‖f j‖ ≤ (p : ℝ) ^ (min 0 (j + K)) := by
  rcases le_or_gt 0 (j + K) with hjk | hjk
  · rw [min_eq_left hjk, zpow_zero]
    exact norm_coeff_le_one f j
  · rw [min_eq_right hjk.le, add_comm, zpow_add₀ cast_p_pos.ne']
    exact (norm_coeff_le_norm_mul f j).trans
      (mul_le_mul_of_nonneg_right hf (zpow_nonneg cast_p_pos.le _))

private theorem lipschitzWith_coeff (j : ℤ) :
    LipschitzWith (Real.toNNReal ((p : ℝ) ^ j)) fun f : HaloTate p ↦ f j :=
  LipschitzWith.of_dist_le_mul fun f g ↦ by
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (zpow_nonneg cast_p_pos.le _), mul_comm,
      ← coeff_sub]
    exact norm_coeff_le_norm_mul _ j

private theorem exists_norm_le_zpow_of_cauchySeq {u : ℕ → HaloTate p} (hu : CauchySeq u) :
    ∃ K : ℕ, ∀ n, ‖u n‖ ≤ (p : ℝ) ^ (K : ℤ) := by
  obtain ⟨R, -, hR⟩ := cauchySeq_bdd hu
  obtain ⟨K, hK⟩ := pow_unbounded_of_one_lt (‖u 0‖ + R) (one_lt_cast_p (p := p))
  refine ⟨K, fun n ↦ (norm_le_norm_add_norm_sub' (u n) (u 0)).trans ?_⟩
  rw [zpow_natCast, ← dist_eq_norm]
  exact (add_le_add_right (hR n 0).le ‖u 0‖).trans hK.le

/-- Completeness: a Cauchy sequence is norm-bounded, hence has a uniform shift `K`; it is
coefficientwise Cauchy via the `p^j`-Lipschitz coefficient maps, and the coefficientwise
limit carries the same shift (mirror of `HaloInt`'s proof). -/
instance : CompleteSpace (HaloTate p) := by
  refine Metric.complete_of_cauchySeq_tendsto fun u hu ↦ ?_
  obtain ⟨K, hK⟩ := exists_norm_le_zpow_of_cauchySeq hu
  have hco : ∀ j : ℤ, CauchySeq fun n ↦ u n j := fun j ↦
    (lipschitzWith_coeff j).uniformContinuous.comp_cauchySeq hu
  choose d hd using fun j ↦ cauchySeq_tendsto_of_complete (hco j)
  have hdb : ∀ j : ℤ, ‖d j‖ ≤ (p : ℝ) ^ (min 0 (j + K)) := fun j ↦
    le_of_tendsto (hd j).norm (.of_forall fun n ↦ coeff_bound_of_norm_le (hK n) j)
  refine ⟨⟨d, K, hdb⟩, Metric.tendsto_atTop.mpr fun ε hε ↦ ?_⟩
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hu (ε / 2) (half_pos hε)
  refine ⟨N, fun n hn ↦ ?_⟩
  rw [dist_eq_norm, norm_def]
  refine lt_of_le_of_lt (ciSup_le fun j ↦ ?_) (half_lt_self hε)
  rw [coeff_sub]
  refine le_of_tendsto ((tendsto_const_nhds.sub (hd j)).norm.mul_const ((p : ℝ) ^ (-j))) ?_
  filter_upwards [Filter.eventually_ge_atTop N] with m hm
  rw [← coeff_sub]
  exact (norm_coeff_le_norm _ j).trans (by rw [← dist_eq_norm]; exact (hN n hn m hm).le)

/-- The embedding of the integral halo ring is isometric (the two gauge norms are the same
supremum). -/
theorem norm_ofInt (x : HaloInt p) : ‖(ofInt x : HaloTate p)‖ = ‖x‖ := rfl

/-- The unit ball of `A` is `Λ^{>1/p}` ([JN] Remark 2.1.3 (1): "the unit ball `R₀` is a ring of
definition"). -/
theorem norm_le_one_iff (f : HaloTate p) : ‖f‖ ≤ 1 ↔ ∃ x : HaloInt p, ofInt x = f :=
  ⟨fun h ↦ ⟨⟨fun j ↦ f j, fun j ↦ by
      simpa using coeff_bound_of_norm_le (K := 0) (by simpa using h) j⟩, ext fun _ ↦ rfl⟩,
    fun ⟨x, hx⟩ ↦ hx ▸ (norm_ofInt x).trans_le (HaloInt.norm_le_one x)⟩

private def Tinv : HaloTate p := ⟨fun j ↦ if j = -1 then 1 else 0, 1, norm_single_le (by simp)⟩

@[simp] private theorem coeff_Tinv (j : ℤ) : (Tinv : HaloTate p) j = if j = -1 then 1 else 0 := rfl

private theorem ofInt_T_mul_Tinv : (ofInt HaloInt.T : HaloTate p) * Tinv = 1 := by
  ext k
  rw [coeff_mul, tsum_eq_single 1 (fun i hi ↦ by simp [HaloInt.coeff_T, hi])]
  simp [HaloInt.coeff_T, coeff_one, sub_eq_neg_self]

private theorem Tinv_mul_ofInt_T : (Tinv : HaloTate p) * ofInt HaloInt.T = 1 :=
  (mul_comm _ _).trans ofInt_T_mul_Tinv

/-- The variable `T` as a unit of `A`, with inverse the stream `δ₋₁`. -/
def T : (HaloTate p)ˣ where
  val := ofInt HaloInt.T
  inv := Tinv
  val_inv := ofInt_T_mul_Tinv
  inv_val := Tinv_mul_ofInt_T

/-- The unit `T` of `A` is the image of the variable `T` of the integral ring.  Not a `simp`
lemma: the `T`-lemmas below are stated for the unit coercion. -/
theorem coe_T : ((T : (HaloTate p)ˣ) : HaloTate p) = ofInt HaloInt.T := rfl

/-- Multiplication by `T` is the coefficient shift. -/
theorem coeff_T_mul (f : HaloTate p) (j : ℤ) :
    (((T : (HaloTate p)ˣ) : HaloTate p) * f) j = f (j - 1) := by
  rw [coe_T, coeff_mul, tsum_eq_single 1 (fun i hi ↦ by simp [HaloInt.coeff_T, hi])]
  simp [HaloInt.coeff_T]

/-- Multiplication by `T^k` is the `k`-fold coefficient shift. -/
theorem coeff_T_pow_mul (f : HaloTate p) (k : ℕ) (j : ℤ) :
    (((T : (HaloTate p)ˣ) : HaloTate p) ^ k * f) j = f (j - k) := by
  induction k generalizing j with
  | zero => simp
  | succ k ih => rw [pow_succ', mul_assoc, coeff_T_mul, ih, sub_sub, add_comm, Nat.cast_succ]

/-- `‖T·f‖ = p⁻¹‖f‖`: `T` is multiplicative ([JN] Definition 2.1.1). -/
theorem norm_T_mul (f : HaloTate p) :
    ‖((T : (HaloTate p)ˣ) : HaloTate p) * f‖ = (p : ℝ)⁻¹ * ‖f‖ := by
  rw [norm_def, norm_def, Real.mul_iSup_of_nonneg (by positivity),
    ← (Equiv.addRight (1 : ℤ)).surjective.iSup_comp]
  refine iSup_congr fun j ↦ ?_
  rw [Equiv.coe_addRight, coeff_T_mul, add_sub_cancel_right, neg_add, zpow_add₀ cast_p_pos.ne',
    zpow_neg_one]
  ring

/-- `‖T‖ = p⁻¹`. -/
theorem norm_T : ‖((T : (HaloTate p)ˣ) : HaloTate p)‖ = (p : ℝ)⁻¹ := by
  simpa using norm_T_mul (1 : HaloTate p)

/-- `T` is topologically nilpotent: `‖T‖ < 1`. -/
theorem norm_T_lt_one : ‖((T : (HaloTate p)ˣ) : HaloTate p)‖ < 1 :=
  norm_T.trans_lt (inv_lt_one_of_one_lt₀ one_lt_cast_p)

/-- `T` is multiplicative for the norm of `A` ([JN] Definition 2.1.1). -/
theorem isMultiplicative_T :
    TateFredholm.IsMultiplicative ((T : (HaloTate p)ˣ) : HaloTate p) := fun f ↦ by
  rw [norm_T_mul, norm_T]

/-- `‖T^k·f‖ = p^{−k}‖f‖` for every *integer* `k`: `T` and its inverse are multiplicative. -/
theorem norm_T_zpow_mul (k : ℤ) (f : HaloTate p) :
    ‖((T ^ k : (HaloTate p)ˣ) : HaloTate p) * f‖ = (p : ℝ) ^ (-k) * ‖f‖ := by
  induction k using Int.induction_on with
  | zero => simp
  | succ k ih =>
    have hstep : ((T ^ ((k : ℤ) + 1) : (HaloTate p)ˣ) : HaloTate p) * f =
        ((T : (HaloTate p)ˣ) : HaloTate p) *
          (((T ^ (k : ℤ) : (HaloTate p)ˣ) : HaloTate p) * f) := by
      rw [← mul_assoc, ← Units.val_mul, zpow_add_one, mul_comm (T ^ (k : ℤ)) T, Units.val_mul]
    rw [hstep, norm_T_mul, ih, ← mul_assoc]
    congr 1
    rw [neg_add, zpow_add₀ cast_p_pos.ne', zpow_neg_one, mul_comm]
  | pred k ih =>
    have hstep : ((T : (HaloTate p)ˣ) : HaloTate p) *
        (((T ^ (-(k : ℤ) - 1) : (HaloTate p)ˣ) : HaloTate p) * f) =
        ((T ^ (-(k : ℤ)) : (HaloTate p)ˣ) : HaloTate p) * f := by
      rw [← mul_assoc, ← Units.val_mul, mul_comm T (T ^ (-(k : ℤ) - 1)), ← zpow_add_one,
        sub_add_cancel]
    have h := norm_T_mul ((((T ^ (-(k : ℤ) - 1) : (HaloTate p)ˣ) : HaloTate p)) * f)
    rw [hstep, ih] at h
    have hmul : (p : ℝ) * ((p : ℝ) ^ (- -(k : ℤ)) * ‖f‖) =
        ‖(((T ^ (-(k : ℤ) - 1) : (HaloTate p)ˣ) : HaloTate p)) * f‖ := by
      rw [h, ← mul_assoc, mul_inv_cancel₀ cast_p_pos.ne', one_mul]
    rw [← hmul, ← mul_assoc]
    congr 1
    rw [neg_sub, sub_eq_add_neg, neg_neg, zpow_add₀ cast_p_pos.ne', zpow_one, mul_comm]

/-- `‖T^k‖ = p^{−k}` for every integer `k`. -/
theorem norm_T_zpow (k : ℤ) : ‖((T ^ k : (HaloTate p)ˣ) : HaloTate p)‖ = (p : ℝ) ^ (-k) := by
  simpa using norm_T_zpow_mul k (1 : HaloTate p)

/-- **`T` is a multiplicative pseudo-uniformizer of `A`** ([JN] Definition 2.1.2). -/
def pseudoUniformizer : TateFredholm.PseudoUniformizer (HaloTate p) where
  unit := T
  norm_lt_one := norm_T_lt_one
  isMultiplicative := isMultiplicative_T

/-- **`A` is a Banach–Tate ring** ([JN] Definition 2.1.2). -/
instance : TateFredholm.IsTate (HaloTate p) := ⟨⟨pseudoUniformizer⟩⟩

/-- Every element of `A` is `T^{−k}` times an integral element. -/
theorem exists_T_zpow_mul_ofInt (f : HaloTate p) :
    ∃ (k : ℕ) (x : HaloInt p), f = (((T⁻¹ : (HaloTate p)ˣ) : HaloTate p)) ^ k * ofInt x := by
  obtain ⟨k, hf⟩ := f.exists_bound
  let x : HaloInt p := ⟨fun j ↦ f (j - k), fun j ↦ by simpa using hf (j - k)⟩
  have hx : ofInt x = ((T : (HaloTate p)ˣ) : HaloTate p) ^ k * f :=
    ext fun j ↦ (coeff_T_pow_mul f k j).symm
  refine ⟨k, x, ?_⟩
  rw [hx, ← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, inv_pow,
    Units.inv_mul_cancel_left]

/-- Units of norm `1` of the integral ring are multiplicative in `A` (`‖ux‖ ≤ ‖x‖` and
`‖x‖ = ‖u⁻¹ux‖ ≤ ‖ux‖`). -/
theorem isMultiplicative_ofInt_of_isUnit (e : (HaloInt p)ˣ) (he : ‖(e : HaloInt p)‖ = 1) :
    TateFredholm.IsMultiplicative (ofInt (e : HaloInt p) : HaloTate p) := fun x ↦ by
  have key : ‖(ofInt (e : HaloInt p) : HaloTate p)‖ * ‖x‖ = ‖x‖ := by rw [norm_ofInt, he, one_mul]
  rw [key]
  refine le_antisymm ((norm_mul_le _ _).trans_eq key) ?_
  calc ‖x‖ = ‖ofInt ((e⁻¹ : (HaloInt p)ˣ) : HaloInt p) * (ofInt (e : HaloInt p) * x)‖ := by
        rw [← mul_assoc, ← ofIntRingHom_apply, ← ofIntRingHom_apply, ← map_mul, Units.inv_mul,
          map_one, one_mul]
    _ ≤ ‖ofInt (e : HaloInt p) * x‖ := (norm_mul_le _ _).trans
        (mul_le_of_le_one_left (norm_nonneg _) ((norm_ofInt _).trans_le (HaloInt.norm_le_one _)))


end HaloTate

end LWX

end
