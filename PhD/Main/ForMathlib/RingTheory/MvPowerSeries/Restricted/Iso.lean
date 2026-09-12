/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.RingTheory.MvPowerSeries.Equiv
import PhD.Main.ForMathlib.RingTheory.MvPowerSeries.Restricted.GaussNorm
import PhD.Main.ForMathlib.RingTheory.PowerSeries.Restricted.GaussNorm

/-!
# Splitting off one variable from restricted multivariate power series

For strictly positive radii `c : Fin (n + 1) → ℝ` (recorded as `[Fact (∀ i, 0 < c i)]`), a
multivariate power series in `n + 1` variables restricted for `c` is the same thing as a
univariate power series restricted for `c 0` with coefficients in the ring of `n`-variable
power series restricted for `Fin.tail c`.

## Main definitions

* `MvPowerSeries.Restricted.finSuccEquiv`: the ring isomorphism
  `Restricted R c ≃+* PowerSeries.Restricted (Restricted R (Fin.tail c)) (c 0)` obtained by
  restricting `MvPowerSeries.finSuccEquiv`.
* `MvPowerSeries.Restricted.finSuccIsometry`: the same map as an isometry for the Gauss norms
  (`MvPowerSeries.Restricted.norm_finSuccEquiv`).
* `MvPowerSeries.Restricted.isEmptyEquiv` / `isEmptyIsometry`: over an empty index type,
  restricted power series are just constants.

## Implementation notes

The key step is `MvPowerSeries.Restricted.subring_map_finSuccEquiv`: the image of the subring
of `c`-restricted power series under `MvPowerSeries.finSuccEquiv` is the image of the subring
of `c 0`-restricted power series over `Restricted R (Fin.tail c)` under the coefficientwise
inclusion.  The isomorphism is then assembled from the generic subring equivalences.

`Restricted R c` is a semireducible synonym of `↥(IsRestricted.subring c)` (deliberately so:
opacity keeps instances like the scoped Pi topology on power series from leaking onto it), and
the subring combinators used here (`Subring.map`, `Subring.subtype`, `RingEquiv.subringMap`,
`Subring.equivMapOfInjective`) reintroduce the raw spelling.  Goals mixing the two spellings
are only type-correct after unfolding the synonym, which `rw`'s motive check will not do; we
therefore cross that seam with term-mode steps (`exact`, `congrArg`, `Eq.trans`) instead of
`rw`, keeping the file free of `backward.isDefEq.respectTransparency` overrides.
-/

open Filter
open scoped Topology

namespace Finsupp

variable {n : ℕ} {M : Type*} [Zero M]

/-- The cofinite filter on `Fin (n + 1) →₀ M` is the pushforward of the cofinite filter on
`M × (Fin n →₀ M)` under the uncurried `Finsupp.cons`. -/
lemma map_uncurry_cons_cofinite :
    map (Function.uncurry (cons (n := n) (M := M))) cofinite = cofinite :=
  le_antisymm cons_injective2.uncurry.tendsto_cofinite
    (Function.Surjective.le_map_cofinite fun s ↦ ⟨(s 0, tail s), cons_tail s⟩)

end Finsupp

namespace MvPowerSeries

/-- The coefficient of `s` in `(MvPowerSeries.finSuccEquiv S n).symm f` is the coefficient of
`Finsupp.tail s` in the `s 0`-th coefficient of `f`. -/
lemma coeff_finSuccEquiv_symm {S : Type*} [CommSemiring S] {n : ℕ} (s : Fin (n + 1) →₀ ℕ)
    (f : PowerSeries (MvPowerSeries (Fin n) S)) :
    coeff s ((finSuccEquiv S n).symm f) = coeff (Finsupp.tail s) (PowerSeries.coeff (s 0) f) := by
  conv_lhs => rw [← Finsupp.cons_tail s, ← coeff_coeff_finSuccEquiv, AlgEquiv.apply_symm_apply]

variable {R : Type*} [NormedRing R]

/-- Over an empty index type every power series is restricted. -/
lemma isRestricted_of_isEmpty {σ : Type*} [IsEmpty σ] (c : σ → ℝ) (f : MvPowerSeries σ R) :
    IsRestricted c f := isRestricted_of_finite_support c (Set.toFinite _)

/-- Over an empty index type the subring of restricted power series is the whole ring. -/
lemma IsRestricted.subring_eq_top [IsUltrametricDist R] {σ : Type*} [IsEmpty σ] (c : σ → ℝ) :
    IsRestricted.subring (R := R) c = ⊤ := top_unique fun f _ ↦ isRestricted_of_isEmpty c f

/-- The coefficients of the image of a `c`-restricted power series under
`MvPowerSeries.finSuccEquiv` are restricted for `Fin.tail c`. -/
lemma IsRestricted.coeff_finSuccEquiv {S : Type*} [NormedCommRing S] {n : ℕ}
    {c : Fin (n + 1) → ℝ} {f : MvPowerSeries (Fin (n + 1)) S} (hf : IsRestricted c f)
    (h0 : c 0 ≠ 0) (i : ℕ) :
    IsRestricted (Fin.tail c) (PowerSeries.coeff i (finSuccEquiv S n f)) := by
  have h := (hf.comp (Finsupp.cons_right_injective i).tendsto_cofinite).const_mul (c 0 ^ i)⁻¹
  refine (mul_zero (c 0 ^ i)⁻¹ ▸ h).congr fun t ↦ ?_
  simp [coeff_coeff_finSuccEquiv, Fin.prod_univ_succ, Fin.tail, mul_left_comm,
    inv_mul_cancel_left₀ (pow_ne_zero _ h0)]

namespace Restricted

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R]

section FinSucc

variable {n : ℕ} (c : Fin (n + 1) → ℝ) [hc : Fact (∀ i, 0 < c i)]

instance : Fact (∀ i, 0 < Fin.tail c i) := ⟨fun i ↦ hc.out i.succ⟩

instance : Fact (0 < c 0) := ⟨hc.out 0⟩

omit [IsUltrametricDist R] in
private lemma norm_mul_prod_mul_pow_nonneg {g : MvPowerSeries (Fin n) R} {x : Fin n →₀ ℕ} {j : ℕ} :
    0 ≤ ‖coeff x g‖ * x.prod (Fin.tail c · ^ ·) * c 0 ^ j :=
  mul_nonneg (mul_nonneg (norm_nonneg _) <| Finset.prod_nonneg fun i _ ↦
    pow_nonneg (hc.out i.succ).le _) (pow_nonneg (hc.out 0).le _)

omit hc in
private lemma norm_coeff_cons_finSuccEquiv_symm_map
    (h : PowerSeries ↥(IsRestricted.subring (R := R) (Fin.tail c))) (k : ℕ) (x : Fin n →₀ ℕ) :
    ‖coeff (Finsupp.cons k x) ((MvPowerSeries.finSuccEquiv R n).symm
        (PowerSeries.map (IsRestricted.subring (R := R) (Fin.tail c)).subtype h))‖ *
      (Finsupp.cons k x).prod (c · ^ ·) =
    ‖coeff x (PowerSeries.coeff k h).1‖ * x.prod (Fin.tail c · ^ ·) * c 0 ^ k := by
  simp only [coeff_finSuccEquiv_symm, PowerSeries.coeff_map, Subring.subtype_apply,
    Finsupp.prod_pow, Fin.prod_univ_succ, Finsupp.tail_cons, Finsupp.cons_zero,
    Finsupp.cons_succ, Fin.tail]
  ring

private lemma finSuccEquiv_mem_map {f : MvPowerSeries (Fin (n + 1)) R} (hf : IsRestricted c f) :
    MvPowerSeries.finSuccEquiv R n f ∈
      (PowerSeries.IsRestricted.subring (R := Restricted R (Fin.tail c)) (c 0)).map
        (PowerSeries.map (IsRestricted.subring (R := R) (Fin.tail c)).subtype) := by
  set h : PowerSeries ↥(IsRestricted.subring (R := R) (Fin.tail c)) :=
    PowerSeries.mk fun i ↦ ⟨PowerSeries.coeff i (MvPowerSeries.finSuccEquiv R n f),
      hf.coeff_finSuccEquiv (hc.out 0).ne' i⟩
  refine ⟨h, ?_, ?_⟩
  · change PowerSeries.IsRestricted (c 0) _
    choose a ha using fun t ↦ exists_achievesGaussNorm (Fin.tail c) (coeff t h)
    have hinj : Function.Injective fun t : Unit →₀ ℕ ↦ Finsupp.cons (t ()) (a t) :=
      fun _ _ hst ↦ Finsupp.unique_ext (Finsupp.cons_injective2 hst).1
    refine (hf.comp hinj.tendsto_cofinite).congr fun t ↦ ?_
    have hat : ‖coeff (a t) (PowerSeries.coeff (t ())
        (MvPowerSeries.finSuccEquiv R n f))‖ * (a t).prod (Fin.tail c · ^ ·) =
        MvPowerSeries.gaussNorm norm (Fin.tail c)
          (PowerSeries.coeff (t ()) (MvPowerSeries.finSuccEquiv R n f)) := ha t
    simp_rw [Finsupp.prod_pow, Finset.univ_unique, Finset.prod_singleton, Function.comp_apply,
      ← MvPowerSeries.coeff_coeff_finSuccEquiv, Fin.tail, Fin.prod_univ_succ,
      Finsupp.cons_zero, Finsupp.cons_succ] at ⊢ hat
    change _ = MvPowerSeries.gaussNorm norm (Fin.tail c)
      (PowerSeries.coeff (t ()) (MvPowerSeries.finSuccEquiv R n f)) * c 0 ^ t ()
    rw [← hat]
    ring
  · ext
    simp [h]

private lemma tendsto_norm_coeff_principal_prod_cofinite
    (h : PowerSeries (Restricted R (Fin.tail c))) {u : Set ℕ} (hu : u.Finite) :
    Tendsto (fun p : ℕ × (Fin n →₀ ℕ) ↦
      ‖coeff p.2 (PowerSeries.coeff p.1 h).1‖ * p.2.prod (Fin.tail c · ^ ·) * c 0 ^ p.1)
      (𝓟 u ×ˢ cofinite) (𝓝 0) := by
  have htends : ∀ j, Tendsto (fun x ↦ ‖coeff x (PowerSeries.coeff j h).1‖ *
      x.prod (Fin.tail c · ^ ·) * c 0 ^ j) cofinite (𝓝 0) := fun j ↦ by
    simpa only [zero_mul] using (PowerSeries.coeff j h).2.mul_const (c 0 ^ j)
  have hψ : Tendsto (fun x ↦ ∑ j ∈ hu.toFinset, ‖coeff x (PowerSeries.coeff j h).1‖ *
      x.prod (Fin.tail c · ^ ·) * c 0 ^ j) cofinite (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using tendsto_finsetSum hu.toFinset fun j _ ↦ htends j
  refine tendsto_const_nhds.squeeze' (hψ.comp tendsto_snd)
    (Eventually.of_forall fun p ↦ norm_mul_prod_mul_pow_nonneg c) ?_
  filter_upwards [tendsto_fst.eventually (eventually_principal.mpr fun _ ha ↦ ha)] with p hp
  exact Finset.single_le_sum (f := fun j ↦ ‖coeff p.2 (PowerSeries.coeff j h).1‖ *
    p.2.prod (Fin.tail c · ^ ·) * c 0 ^ j) (fun j _ ↦ norm_mul_prod_mul_pow_nonneg c)
    (hu.mem_toFinset.mpr hp)

private lemma isRestricted_finSuccEquiv_symm_map {h : PowerSeries (Restricted R (Fin.tail c))}
    (hh : PowerSeries.IsRestricted (c 0) h) : IsRestricted c ((MvPowerSeries.finSuccEquiv R n).symm
      (PowerSeries.map (IsRestricted.subring (R := R) (Fin.tail c)).subtype h)) := by
  rw [PowerSeries.isRestricted_iff] at hh
  have hG : Tendsto (fun p : ℕ × (Fin n →₀ ℕ) ↦
      ‖coeff p.2 (PowerSeries.coeff p.1 h).1‖ * p.2.prod (Fin.tail c · ^ ·) * c 0 ^ p.1)
      (cofinite.coprod cofinite) (𝓝 0) := by
    refine Tendsto.coprod_of_prod_top_right
      (fun s hs ↦ tendsto_norm_coeff_principal_prod_cofinite c h hs) ?_
    refine tendsto_const_nhds.squeeze (hh.comp tendsto_fst)
      (fun p ↦ norm_mul_prod_mul_pow_nonneg c) fun p ↦
      mul_le_mul_of_nonneg_right (le_gaussNorm norm (Fin.tail c) (PowerSeries.coeff p.1 h).1
        (hasGaussNorm (Fin.tail c) (PowerSeries.coeff p.1 h)) p.2) (pow_nonneg (hc.out 0).le _)
  rw [IsRestricted, ← Finsupp.map_uncurry_cons_cofinite, Filter.tendsto_map'_iff,
    Filter.coprod_cofinite.symm]
  exact hG.congr fun p ↦ (norm_coeff_cons_finSuccEquiv_symm_map c h p.1 p.2).symm

/-- The image of the subring of `c`-restricted power series under `MvPowerSeries.finSuccEquiv`
is the image of the subring of `c 0`-restricted power series over `Restricted R (Fin.tail c)`
under the coefficientwise inclusion. -/
lemma subring_map_finSuccEquiv :
    (IsRestricted.subring (R := R) c).map
        (MvPowerSeries.finSuccEquiv R n).toRingEquiv.toRingHom =
      (PowerSeries.IsRestricted.subring (R := Restricted R (Fin.tail c)) (c 0)).map
        (PowerSeries.map (IsRestricted.subring (R := R) (Fin.tail c)).subtype) := by
  ext g
  constructor
  · rintro ⟨f, hf, rfl⟩
    exact finSuccEquiv_mem_map c hf
  · rintro ⟨h, hh, rfl⟩
    exact ⟨(MvPowerSeries.finSuccEquiv R n).symm
        (PowerSeries.map (IsRestricted.subring (R := R) (Fin.tail c)).subtype h),
      isRestricted_finSuccEquiv_symm_map c hh, (MvPowerSeries.finSuccEquiv R n).apply_symm_apply _⟩

private noncomputable def mapSubtypeEquiv :
    PowerSeries.Restricted (Restricted R (Fin.tail c)) (c 0) ≃+*
      ((PowerSeries.IsRestricted.subring (R := Restricted R (Fin.tail c)) (c 0)).map
        (PowerSeries.map (IsRestricted.subring (R := R) (Fin.tail c)).subtype)) :=
  Subring.equivMapOfInjective _ _ (PowerSeries.map_injective _ Subtype.val_injective)

variable (R) in
/-- Splitting off the first variable: the ring isomorphism between `c`-restricted power series
in `n + 1` variables and `c 0`-restricted univariate power series over the ring of
`Fin.tail c`-restricted power series in `n` variables. -/
noncomputable def finSuccEquiv :
    Restricted R c ≃+* PowerSeries.Restricted (Restricted R (Fin.tail c)) (c 0) :=
  ((RingEquiv.subringMap (MvPowerSeries.finSuccEquiv R n).toRingEquiv).trans
    (RingEquiv.subringCongr (subring_map_finSuccEquiv c))).trans (mapSubtypeEquiv c).symm

/-- Applying the coefficientwise inclusion to `finSuccEquiv R c f` recovers
`MvPowerSeries.finSuccEquiv R n` applied to the underlying power series of `f`. -/
lemma map_finSuccEquiv (f : Restricted R c) :
    PowerSeries.map (IsRestricted.subring (R := R) (Fin.tail c)).subtype (finSuccEquiv R c f).1 =
      MvPowerSeries.finSuccEquiv R n f.1 :=
  congrArg Subtype.val ((mapSubtypeEquiv c).apply_symm_apply _)

/-- The underlying value of the `i`-th coefficient of `finSuccEquiv R c f` equals the `i`-th
coefficient of `MvPowerSeries.finSuccEquiv R n` applied to the underlying power series of `f`. -/
lemma coeff_finSuccEquiv (f : Restricted R c) (i : ℕ) :
    (PowerSeries.coeff i (finSuccEquiv R c f).1).1 =
      PowerSeries.coeff i (MvPowerSeries.finSuccEquiv R n f.1) :=
  (PowerSeries.coeff_map ..).symm.trans (congrArg (PowerSeries.coeff i) (map_finSuccEquiv c f))

private lemma norm_coeff_finSuccEquiv_mul_prod (f : Restricted R c) (k : ℕ) (t : Fin n →₀ ℕ) :
    ‖coeff t (PowerSeries.coeff k (finSuccEquiv R c f).1).1‖ * t.prod (Fin.tail c · ^ ·) * c 0 ^ k =
      ‖coeff (Finsupp.cons k t) f.1‖ * (Finsupp.cons k t).prod (c · ^ ·) :=
  (norm_coeff_cons_finSuccEquiv_symm_map c (finSuccEquiv R c f).1 k t).symm.trans <| by
    rw [map_finSuccEquiv, AlgEquiv.symm_apply_apply]

/-- `finSuccEquiv` preserves the Gauss norm. -/
lemma gaussNorm_finSuccEquiv (f : Restricted R c) :
    PowerSeries.Restricted.gaussNorm _ (c 0) (finSuccEquiv R c f) = gaussNorm R c f := by
  have hbd : BddAbove (Set.range fun p : ℕ × (Fin n →₀ ℕ) ↦
      ‖coeff p.2 (PowerSeries.coeff p.1 (finSuccEquiv R c f).1).1‖ *
        p.2.prod (Fin.tail c · ^ ·) * c 0 ^ p.1) := by
    simp only [norm_coeff_finSuccEquiv_mul_prod c f]
    exact (hasGaussNorm c f).mono (Set.range_subset_iff.2 fun p ↦ Set.mem_range_self _)
  show PowerSeries.gaussNorm norm (c 0) (finSuccEquiv R c f).1 = MvPowerSeries.gaussNorm norm c f.1
  simp_rw [PowerSeries.gaussNorm_eq, norm_def, MvPowerSeries.gaussNorm,
    Real.iSup_mul_of_nonneg (pow_nonneg (hc.out 0).le _)]
  rw [← ciSup_prod hbd]
  exact Function.Surjective.iSup_congr _ (fun s ↦ ⟨(s 0, Finsupp.tail s), Finsupp.cons_tail s⟩)
    fun p ↦ (norm_coeff_finSuccEquiv_mul_prod c f p.1 p.2).symm

/-- `finSuccEquiv` preserves the norm. -/
lemma norm_finSuccEquiv (f : Restricted R c) : ‖finSuccEquiv R c f‖ = ‖f‖ :=
  gaussNorm_finSuccEquiv c f

instance : RingHomIsometric (finSuccEquiv R c).toRingHom where
  norm_map {f} := norm_finSuccEquiv c f

variable (R) in
/-- `finSuccEquiv` as an isometry equivalence for the Gauss norms. -/
noncomputable def finSuccIsometry :
    Restricted R c ≃ᵢ PowerSeries.Restricted (Restricted R (Fin.tail c)) (c 0) :=
  IsometryEquiv.mk (finSuccEquiv R c).toEquiv (RingHom.isometry (finSuccEquiv R c).toRingHom)

end FinSucc

section IsEmpty

variable {σ : Type*} [IsEmpty σ] (c : σ → ℝ)

instance : Fact (∀ i, 0 < c i) := ⟨isEmptyElim⟩

variable (R) in
/-- Over an empty index type, restricted power series are just constants. -/
noncomputable def isEmptyEquiv : Restricted R c ≃+* R :=
  ((RingEquiv.subringCongr (IsRestricted.subring_eq_top c)).trans Subring.topEquiv).trans
    (MvPowerSeries.isEmptyEquiv σ R).toRingEquiv

/-- `isEmptyEquiv R c f` is the constant coefficient of the underlying power series of `f`. -/
@[simp]
lemma isEmptyEquiv_apply (f : Restricted R c) : isEmptyEquiv R c f = constantCoeff f.1 := rfl

/-- `isEmptyEquiv` preserves the norm. -/
lemma norm_isEmptyEquiv (f : Restricted R c) : ‖isEmptyEquiv R c f‖ = ‖f‖ := by
  simp [norm_def, MvPowerSeries.gaussNorm]

instance : RingHomIsometric (isEmptyEquiv R c).toRingHom where
  norm_map {f} := norm_isEmptyEquiv c f

variable (R) in
/-- `isEmptyEquiv` as an isometry equivalence for the Gauss norm. -/
noncomputable def isEmptyIsometry : Restricted R c ≃ᵢ R :=
  IsometryEquiv.mk (isEmptyEquiv R c).toEquiv (RingHom.isometry (isEmptyEquiv R c).toRingHom)

end IsEmpty

end Restricted

end MvPowerSeries
