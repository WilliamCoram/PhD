/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.Algebra.Polynomial.HasseDeriv
import PhD.TateFredholm.Riesz

/-!
# Entire power series: the ring `R{{T}}`, Euclidean division, good zeros

[Bel] Definition II.1.16 introduces `R{{T}}`, the everywhere convergent power series
`∑ aₙTⁿ` with `|aₙ|Cⁿ → 0` for every `C > 0`; [JN] §2.1 writes it `R{{T}}` as well and
calls a series with constant term `1` a *Fredholm series* ([JN] Definition 2.2.1).  This
file packages the predicate `IsEntire` (the hypothesis `∀ c > 0, IsRestricted c f` already
used throughout `Riesz.lean`), the subring it defines, and the three pieces of
[Bel] §II.2 that the Riesz–Coleman theory consumes:

* **Euclidean division** by a polynomial with invertible leading coefficient
  ([Bel] Proposition II.2.8), obtained from Martin's Weierstrass division at a large
  radius (`PhD.ForMathlib…MulWeierstrassDivision`), and its consequence
  [Bel] Corollary II.2.9 in the form "coprime in `R{{T}}` iff coprime to the remainder";
* **relative primality** in `R{{T}}` ([JN] Definition 2.2.1: "the ideal `(P, Q) = R{{T}}`");
* **good zeros** ([Bel] Definition II.2.11) and the factorisation
  `F = (1 − a⁻¹T)ˢ G` with `G(a)` a unit ([Bel] §II.2.3), plus the Leibniz rule for the
  divided derivatives `Δˢ` ([Buz07] p. 22) that transports good zeros across products.

## Main definitions

* `PowerSeries.IsEntire`, `PowerSeries.entireSubring`: entire series and the ring `R{{T}}`.
* `PowerSeries.IsEntireCoprime`: relative primality in `R{{T}}` ([JN] Definition 2.2.1).
* `PowerSeries.IsGoodZero`: good zeros of a given order ([Bel] Definition II.2.11).

## Main results

* `PowerSeries.hasseDeriv_mul`: the Leibniz rule for divided derivatives of power series.
* `PowerSeries.IsEntire.exists_eq_mul_add`, `PowerSeries.eq_mul_add_q_unique`,
  `PowerSeries.eq_mul_add_r_unique`: Euclidean division in `R{{T}}` ([Bel] Proposition II.2.8).
* `PowerSeries.isEntireCoprime_iff_isCoprime_of_eq_mul_add`: [Bel] Corollary II.2.9.

## References

* [Bel] J. Bellaïche, *The eigenbook*, §II.1–II.2.
* [JN] C. Johansson, J. Newton, *Extended eigenvarieties for overconvergent cohomology*, §2.1–2.2.
* [Buz07] K. Buzzard, *Eigenvarieties*, §2–3.
-/

open Filter Topology

noncomputable section

namespace PowerSeries

section Leibniz

variable {A : Type*} [CommSemiring A]

/-- Leibniz rule for the divided derivatives: `Δˢ(fg) = ∑_{i+j=s} Δⁱf · Δʲg`
([Buz07] p. 22: "if `f, g ∈ A[[T]]` then it is possible to check that
`Δˢ(fg) = ∑ᵢ₌₀ˢ Δⁱ(f)Δˢ⁻ⁱ(g)`"). -/
theorem hasseDeriv_mul (f g : PowerSeries A) (s : ℕ) :
    hasseDeriv s (f * g) =
      ∑ ij ∈ Finset.antidiagonal s, hasseDeriv ij.1 f * hasseDeriv ij.2 g := by
  ext n
  have htrunc : ∀ h : PowerSeries A, ∀ m ≤ n + s, (trunc (n + s + 1) h).coeff m = coeff m h :=
    fun h m hm ↦ by rw [coeff_trunc, if_pos (by omega)]
  have key := congrArg (Polynomial.coeff · n)
    (Polynomial.hasseDeriv_mul s (trunc (n + s + 1) f) (trunc (n + s + 1) g))
  simp only [Polynomial.hasseDeriv_coeff, Polynomial.coeff_mul, Polynomial.finsetSum_coeff]
    at key
  rw [coeff_hasseDeriv, coeff_mul, map_sum]
  simp only [coeff_mul, coeff_hasseDeriv]
  have e1 : ∑ p ∈ Finset.antidiagonal (n + s), coeff p.1 f * coeff p.2 g =
      ∑ x ∈ Finset.antidiagonal (n + s),
        (trunc (n + s + 1) f).coeff x.1 * (trunc (n + s + 1) g).coeff x.2 :=
    Finset.sum_congr rfl fun x hx ↦ by
      have := Finset.mem_antidiagonal.mp hx
      rw [htrunc f x.1 (by omega), htrunc g x.2 (by omega)]
  have e2 : ∀ x ∈ Finset.antidiagonal s, ∑ y ∈ Finset.antidiagonal n,
        ((y.1 + x.1).choose x.1 : A) * coeff (y.1 + x.1) f *
          (((y.2 + x.2).choose x.2 : A) * coeff (y.2 + x.2) g) =
      ∑ y ∈ Finset.antidiagonal n,
        ((y.1 + x.1).choose x.1 : A) * (trunc (n + s + 1) f).coeff (y.1 + x.1) *
          (((y.2 + x.2).choose x.2 : A) * (trunc (n + s + 1) g).coeff (y.2 + x.2)) :=
    fun x hx ↦ Finset.sum_congr rfl fun y hy ↦ by
      have := Finset.mem_antidiagonal.mp hx
      have := Finset.mem_antidiagonal.mp hy
      rw [htrunc f (y.1 + x.1) (by omega), htrunc g (y.2 + x.2) (by omega)]
  rw [e1, Finset.sum_congr rfl e2]
  exact key

/-- The divided derivatives of a polynomial, viewed as a power series, are the polynomial
ones (`Polynomial.hasseDeriv`). -/
theorem hasseDeriv_coe (k : ℕ) (P : Polynomial A) :
    hasseDeriv k (P : PowerSeries A) = (Polynomial.hasseDeriv k P : PowerSeries A) :=
  PowerSeries.ext fun n ↦ by
    rw [coeff_hasseDeriv, Polynomial.coeff_coe, Polynomial.coeff_coe, Polynomial.hasseDeriv_coeff]

end Leibniz

section Entire

variable {R : Type*} [NormedCommRing R]

/-- **[Bel] Definition II.1.16.**  A power series is *entire* (everywhere convergent) if it
is restricted at every positive radius: `‖aₙ‖ Cⁿ → 0` for every `C > 0`. -/
def IsEntire (f : PowerSeries R) : Prop := ∀ c : ℝ, 0 < c → IsRestricted c f

theorem isEntire_iff {f : PowerSeries R} :
    IsEntire f ↔ ∀ c : ℝ, 0 < c → Tendsto (fun n ↦ ‖coeff n f‖ * c ^ n) atTop (𝓝 0) :=
  forall₂_congr fun c _ ↦ isRestricted_iff' c f

/-- An entire series satisfies the standing summability hypothesis of `evalT` at every
point. -/
theorem IsEntire.tendsto_norm_coeff_mul_pow {f : PowerSeries R} (hf : IsEntire f) (a : R) :
    Tendsto (fun n ↦ ‖coeff n f‖ * ‖a‖ ^ n) atTop (𝓝 0) :=
  tendsto_norm_coeff_mul_pow_of_isRestricted (hf (‖a‖ + 1) (by positivity))
    (le_add_of_nonneg_right zero_le_one)

theorem isEntire_zero : IsEntire (0 : PowerSeries R) := fun c _ ↦ isRestricted_zero c

theorem isEntire_C (r : R) : IsEntire (C r) := fun c _ ↦ isRestricted_C c r

theorem isEntire_one : IsEntire (1 : PowerSeries R) := fun c _ ↦ isRestricted_one c

theorem isEntire_X : IsEntire (X : PowerSeries R) := fun c _ ↦ isRestricted_X c

theorem IsEntire.add {f g : PowerSeries R} (hf : IsEntire f) (hg : IsEntire g) :
    IsEntire (f + g) := fun c hc ↦ isRestricted.add c (hf c hc) (hg c hc)

theorem IsEntire.neg {f : PowerSeries R} (hf : IsEntire f) : IsEntire (-f) :=
  fun c hc ↦ isRestricted.neg c (hf c hc)

theorem IsEntire.sub {f g : PowerSeries R} (hf : IsEntire f) (hg : IsEntire g) :
    IsEntire (f - g) := fun c hc ↦ isRestricted.sub c (hf c hc) (hg c hc)

/-- Polynomials are entire. -/
theorem _root_.Polynomial.isEntire_coe (p : Polynomial R) : IsEntire (p : PowerSeries R) :=
  fun c _ ↦ Polynomial.isRestricted_toPowerSeries c p

theorem IsEntire.sum {ι : Type*} {s : Finset ι} {g : ι → PowerSeries R}
    (hg : ∀ i ∈ s, IsEntire (g i)) : IsEntire (∑ i ∈ s, g i) :=
  fun c hc ↦ isRestricted.sum c fun i hi ↦ hg i hi c hc

/-- Shifting the coefficients down by `m` preserves entireness. -/
theorem IsEntire.shift {f : PowerSeries R} (hf : IsEntire f) (m : ℕ) :
    IsEntire (mk fun n ↦ coeff (n + m) f) := fun c hc ↦ by
  rw [isRestricted_iff']
  have := (((isRestricted_iff' c f).mp (hf c hc)).comp (tendsto_add_atTop_nat m)).mul_const
    (c ^ m)⁻¹
  rw [zero_mul] at this
  refine this.congr fun n ↦ ?_
  rw [Function.comp_apply, coeff_mk, pow_add, mul_assoc,
    mul_inv_cancel_right₀ (pow_ne_zero m hc.ne')]

variable [IsUltrametricDist R]

theorem IsEntire.mul {f g : PowerSeries R} (hf : IsEntire f) (hg : IsEntire g) :
    IsEntire (f * g) := fun c hc ↦ isRestricted.mul c (hf c hc) (hg c hc)

theorem IsEntire.pow {f : PowerSeries R} (hf : IsEntire f) (n : ℕ) : IsEntire (f ^ n) :=
  fun c hc ↦ isRestricted.pow c (hf c hc) n

theorem IsEntire.hasseDeriv {f : PowerSeries R} (hf : IsEntire f) (k : ℕ) :
    IsEntire (hasseDeriv k f) := fun c hc ↦ isRestricted_hasseDeriv hc (hf c hc) k

variable (R) in
/-- The ring `R{{T}}` of entire power series, as a subring of `R⟦T⟧`
([Bel] Definition II.1.16; [JN] §2.1). -/
def entireSubring : Subring (PowerSeries R) where
  carrier := {f | IsEntire f}
  mul_mem' := fun hf hg ↦ hf.mul hg
  one_mem' := isEntire_one
  add_mem' := fun hf hg ↦ hf.add hg
  zero_mem' := isEntire_zero
  neg_mem' := fun hf ↦ hf.neg

@[simp] theorem mem_entireSubring {f : PowerSeries R} : f ∈ entireSubring R ↔ IsEntire f :=
  Iff.rfl

variable [CompleteSpace R]

/-- Evaluation of entire series is multiplicative (specialisation of `evalT_mul`). -/
theorem IsEntire.evalT_mul {f g : PowerSeries R} (hf : IsEntire f) (hg : IsEntire g) (a : R) :
    evalT a (f * g) = evalT a f * evalT a g :=
  PowerSeries.evalT_mul (hf.tendsto_norm_coeff_mul_pow a) (hg.tendsto_norm_coeff_mul_pow a)

/-- Evaluation of entire series is additive (specialisation of `evalT_add`). -/
theorem IsEntire.evalT_add {f g : PowerSeries R} (hf : IsEntire f) (hg : IsEntire g) (a : R) :
    evalT a (f + g) = evalT a f + evalT a g :=
  PowerSeries.evalT_add (hf.tendsto_norm_coeff_mul_pow a) (hg.tendsto_norm_coeff_mul_pow a)

/-- Evaluation of entire series is subtractive (specialisation of `evalT_sub`). -/
theorem IsEntire.evalT_sub {f g : PowerSeries R} (hf : IsEntire f) (hg : IsEntire g) (a : R) :
    evalT a (f - g) = evalT a f - evalT a g :=
  PowerSeries.evalT_sub (hf.tendsto_norm_coeff_mul_pow a) (hg.tendsto_norm_coeff_mul_pow a)

omit [IsUltrametricDist R] [CompleteSpace R] in
/-- Evaluation of the zero series. -/
@[simp] theorem evalT_zero (a : R) : evalT a (0 : PowerSeries R) = 0 := by
  simp [evalT]

omit [IsUltrametricDist R] [CompleteSpace R] in
/-- Evaluation of a power of `X`. -/
theorem evalT_X_pow (a : R) (n : ℕ) : evalT a (X ^ n) = a ^ n := by
  rw [evalT, tsum_eq_single n fun k hk ↦ by simp [coeff_X_pow, hk], coeff_X_pow, if_pos rfl,
    one_mul]

/-- Evaluation of entire series commutes with finite sums. -/
theorem IsEntire.evalT_sum {ι : Type*} {s : Finset ι} {g : ι → PowerSeries R}
    (hg : ∀ i ∈ s, IsEntire (g i)) (a : R) :
    evalT a (∑ i ∈ s, g i) = ∑ i ∈ s, evalT a (g i) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons i s hi ih =>
    rw [Finset.sum_cons, Finset.sum_cons,
      (hg i (Finset.mem_cons_self _ _)).evalT_add
        (IsEntire.sum fun j hj ↦ hg j (Finset.mem_cons_of_mem hj)),
      ih fun j hj ↦ hg j (Finset.mem_cons_of_mem hj)]

/-- The Leibniz rule evaluated at a point: `Δⁱ(FG)(a) = ∑_{j+l=i} ΔʲF(a) ΔˡG(a)`. -/
theorem IsEntire.evalT_hasseDeriv_mul {F G : PowerSeries R} (hF : IsEntire F) (hG : IsEntire G)
    (a : R) (i : ℕ) :
    evalT a (PowerSeries.hasseDeriv i (F * G)) =
      ∑ ij ∈ Finset.antidiagonal i,
        evalT a (PowerSeries.hasseDeriv ij.1 F) * evalT a (PowerSeries.hasseDeriv ij.2 G) := by
  rw [hasseDeriv_mul, IsEntire.evalT_sum fun ij _ ↦ (hF.hasseDeriv _).mul (hG.hasseDeriv _)]
  exact Finset.sum_congr rfl fun ij _ ↦ (hF.hasseDeriv _).evalT_mul (hG.hasseDeriv _) a

private theorem norm_coeff_zero_le_of_evalT_eq_zero {g : PowerSeries R} (hg : IsEntire g) {x : R}
    (hx : evalT x g = 0) {M : ℝ} (hM : ∀ m, ‖coeff m g‖ ≤ M) (hx1 : ‖x‖ ≤ 1) :
    ‖coeff 0 g‖ ≤ M * ‖x‖ := by
  have hs := summable_coeff_mul_pow (hg.tendsto_norm_coeff_mul_pow x)
  rw [evalT, hs.tsum_eq_zero_add, pow_zero, mul_one] at hx
  rw [eq_neg_of_add_eq_zero_left hx, norm_neg]
  refine (TateFredholm.norm_tsum_le_iSup
    (hs.comp_injective (add_left_injective 1)).tendsto_cofinite_zero).trans (ciSup_le fun m ↦ ?_)
  refine (norm_mul_le _ _).trans (mul_le_mul (hM _) ((norm_pow_le' _ m.succ_pos).trans
    (pow_le_of_le_one (norm_nonneg _) hx1 m.succ_ne_zero)) (norm_nonneg _)
    ((norm_nonneg _).trans (hM 0)))

/-- **Identity theorem along a pseudo-uniformizer** (elementary ultrametric argument): an
entire series vanishing at every `ϖᵏ` is zero.  (The lowest nonzero coefficient would be
bounded by `sup_{n>n₀} ‖dₙ‖‖ϖ‖^{k(n−n₀)} → 0`.)  Supports [Buz07] p. 20's
"`det(1 − X(φ ⊕ ψ)) = det(1 − Xφ) det(1 − Xψ)`", proved here by evaluating
`fredholmDet_mul` at all `ϖᵏ`. -/
theorem IsEntire.eq_zero_of_forall_evalT_pow_eq_zero {f : PowerSeries R} (hf : IsEntire f)
    (ϖ : TateFredholm.PseudoUniformizer R) (h : ∀ k : ℕ, evalT ((ϖ : R) ^ k) f = 0) : f = 0 := by
  by_contra hf0
  set n := f.order.toNat
  set g := divXPowOrder f with hg_def
  have hfg : f = X ^ n * g := X_pow_order_mul_divXPowOrder.symm
  have hg00 : coeff 0 g ≠ 0 := by
    rw [coeff_zero_eq_constantCoeff_apply]
    exact mt constantCoeff_divXPowOrder_eq_zero_iff.mp hf0
  have hg : IsEntire g := hf.shift n
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ m, ‖coeff m g‖ ≤ M := by
    obtain ⟨M, hM⟩ := (((isRestricted_iff' 1 g).mp (hg 1 one_pos)).bddAbove_range)
    exact ⟨M, fun m ↦ by simpa using hM ⟨m, rfl⟩⟩
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hbound : ∀ k, ‖coeff 0 g‖ ≤ M * ‖(ϖ : R)‖ ^ (k + 1) := fun k ↦ by
    have hk := h (k + 1)
    rw [hfg, (isEntire_X.pow n).evalT_mul hg, evalT_X_pow] at hk
    have hpow : ‖(ϖ : R) ^ (k + 1)‖ ≤ ‖(ϖ : R)‖ ^ (k + 1) := norm_pow_le' _ k.succ_pos
    refine (norm_coeff_zero_le_of_evalT_eq_zero hg
      (((ϖ.unit.isUnit.pow (k + 1)).pow n).mul_right_eq_zero.mp hk) hM
      (hpow.trans (pow_le_one₀ (norm_nonneg _) ϖ.norm_lt_one.le))).trans ?_
    exact mul_le_mul_of_nonneg_left hpow hM0
  have hlim : Tendsto (fun k : ℕ ↦ M * ‖(ϖ : R)‖ ^ (k + 1)) atTop (𝓝 0) := by
    have := ((tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _)
      ϖ.norm_lt_one).const_mul M).comp (tendsto_add_atTop_nat 1)
    rwa [mul_zero] at this
  exact hg00 (norm_le_zero_iff.mp (ge_of_tendsto' hlim hbound))

end Entire

section Division

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R] [NormOneClass R]

omit [IsUltrametricDist R] [CompleteSpace R] [NormOneClass R] in
private def distRadius (B : Polynomial R) : ℝ :=
  1 + ∑ i ∈ Finset.range (B.natDegree + 1), ‖B.coeff i‖

omit [IsUltrametricDist R] [CompleteSpace R] [NormOneClass R] in
private theorem one_le_distRadius (B : Polynomial R) : 1 ≤ distRadius B :=
  le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)

omit [IsUltrametricDist R] [CompleteSpace R] [NormOneClass R] in
private theorem norm_coeff_le_distRadius (B : Polynomial R) {i : ℕ} (hi : i ≤ B.natDegree) :
    ‖B.coeff i‖ ≤ distRadius B :=
  le_add_of_nonneg_of_le zero_le_one (Finset.single_le_sum (fun _ _ ↦ norm_nonneg _)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hi)))

omit [CompleteSpace R] in
private theorem isMulDistinguished_of_monic {B : Polynomial R} (hB : B.Monic) {c : ℝ}
    [Fact (0 < c)] (hc : distRadius B ≤ c) :
    IsMulDistinguished c (Polynomial.toRestricted c B).1 B.natDegree := by
  have : Nontrivial R := NormOneClass.nontrivial
  have h1c : 1 ≤ c := (one_le_distRadius B).trans hc
  have h0c : (0 : ℝ) ≤ c := zero_le_one.trans h1c
  refine Restricted.isMulDistinguished_toRestricted_of_monic hB
    (Polynomial.degree_eq_natDegree hB.ne_zero)
    (le_antisymm ((Restricted.norm_le_iff c _).mpr fun i ↦ ?_) ?_)
  · rw [Polynomial.val_toRestricted, Polynomial.coeff_coe]
    rcases lt_trichotomy i B.natDegree with hi | rfl | hi
    · calc ‖B.coeff i‖ * c ^ i ≤ c * c ^ i :=
            mul_le_mul_of_nonneg_right ((norm_coeff_le_distRadius B hi.le).trans hc)
              (pow_nonneg h0c i)
        _ = c ^ (i + 1) := (pow_succ' c i).symm
        _ ≤ c ^ B.natDegree := pow_le_pow_right₀ h1c hi
    · rw [hB.coeff_natDegree, norm_one, one_mul]
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt hi, norm_zero, zero_mul]
      exact pow_nonneg h0c _
  · have := Restricted.norm_coeff_mul_pow_le c (Polynomial.toRestricted c B) B.natDegree
    rwa [Polynomial.val_toRestricted, Polynomial.coeff_coe, hB.coeff_natDegree, norm_one,
      one_mul] at this

private theorem exists_eq_mul_add_of_monic_of_le {F : PowerSeries R} (hF : IsEntire F)
    {B : Polynomial R} (hB : B.Monic) {c : ℝ} (hc : distRadius B ≤ c) :
    ∃ (q : PowerSeries R) (r : Polynomial R),
      IsRestricted c q ∧ r.degree < B.degree ∧ F = (B : PowerSeries R) * q + r := by
  have hc0 : Fact (0 < c) := ⟨zero_lt_one.trans_le ((one_le_distRadius B).trans hc)⟩
  obtain ⟨q, r, hr, hdiv⟩ := Restricted.weierstrassDivision_exists_of_isMulDistinguished
    (isMulDistinguished_of_monic hB hc) (restrictedOf (hF c hc0.out))
  have : Nontrivial R := NormOneClass.nontrivial
  refine ⟨q.1, r, q.2, (Polynomial.degree_eq_natDegree hB.ne_zero).symm ▸ hr, ?_⟩
  exact congrArg Subtype.val hdiv

omit [CompleteSpace R] in
private theorem q_unique_of_monic_of_le {B : Polynomial R} (hB : B.Monic) {c : ℝ}
    (hc : distRadius B ≤ c) {q₁ q₂ : PowerSeries R} {r₁ r₂ : Polynomial R}
    (hq₁ : IsRestricted c q₁) (hq₂ : IsRestricted c q₂) (hr₁ : r₁.degree < B.degree)
    (hr₂ : r₂.degree < B.degree)
    (h : (B : PowerSeries R) * q₁ + r₁ = (B : PowerSeries R) * q₂ + r₂) : q₁ = q₂ := by
  have hc0 : Fact (0 < c) := ⟨zero_lt_one.trans_le ((one_le_distRadius B).trans hc)⟩
  have : Nontrivial R := NormOneClass.nontrivial
  have hF : IsRestricted c ((B : PowerSeries R) * q₁ + (r₁ : PowerSeries R)) :=
    isRestricted.add c (isRestricted.mul c (Polynomial.isRestricted_toPowerSeries c B) hq₁)
      (Polynomial.isRestricted_toPowerSeries c r₁)
  have hdeg := Polynomial.degree_eq_natDegree hB.ne_zero
  exact congrArg Subtype.val (Restricted.weierstrassDivision_q_unique_of_isMulDistinguished
    (isMulDistinguished_of_monic hB hc) (f := restrictedOf hF) (q₁ := restrictedOf hq₁)
    (q₂ := restrictedOf hq₂) (hdeg ▸ hr₁) (Subtype.ext rfl) (hdeg ▸ hr₂) (Subtype.ext h))

private theorem exists_eq_mul_add_of_monic {F : PowerSeries R} (hF : IsEntire F)
    {B : Polynomial R} (hB : B.Monic) :
    ∃ (q : PowerSeries R) (r : Polynomial R),
      IsEntire q ∧ r.degree < B.degree ∧ F = (B : PowerSeries R) * q + r := by
  obtain ⟨q, r, hq, hr, hdiv⟩ := exists_eq_mul_add_of_monic_of_le hF hB le_rfl
  refine ⟨q, r, fun c hc ↦ ?_, hr, hdiv⟩
  obtain ⟨q', r', hq', hr', hdiv'⟩ :=
    exists_eq_mul_add_of_monic_of_le hF hB (le_max_left (distRadius B) c)
  have hq'0 : IsRestricted (distRadius B) q' :=
    isRestricted_of_le (zero_le_one.trans (one_le_distRadius B)) (le_max_left _ _) hq'
  obtain rfl := q_unique_of_monic_of_le hB le_rfl hq hq'0 hr hr' (hdiv.symm.trans hdiv')
  exact isRestricted_of_le hc.le (le_max_right _ _) hq'

omit [IsUltrametricDist R] [CompleteSpace R] [NormOneClass R] in
private theorem monic_C_inv_mul {B : Polynomial R} (u : Rˣ) (hu : B.leadingCoeff = u) :
    (Polynomial.C ((u⁻¹ : Rˣ) : R) * B).Monic :=
  Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one (by rw [hu, Units.inv_mul])

/-- **Euclidean division in `R{{T}}`** ([Bel] Proposition II.2.8, existence): for `B ∈ R[T]`
with invertible leading coefficient, every entire `F` is `F = BQ + S` with `Q` entire and
`S` a polynomial of degree `< deg B`.  Discharged by Martin's Weierstrass division at a
radius where `B` is distinguished (`weierstrassDivision_exists_of_isMulDistinguished`),
the quotient being entire by uniqueness across radii. -/
theorem IsEntire.exists_eq_mul_add {F : PowerSeries R} (hF : IsEntire F) {B : Polynomial R}
    (hB : IsUnit B.leadingCoeff) :
    ∃ (q : PowerSeries R) (r : Polynomial R),
      IsEntire q ∧ r.degree < B.degree ∧ F = (B : PowerSeries R) * q + r := by
  obtain ⟨u, hu⟩ := hB
  obtain ⟨q, r, hq, hr, hdiv⟩ := exists_eq_mul_add_of_monic hF (monic_C_inv_mul u hu.symm)
  refine ⟨C ((u⁻¹ : Rˣ) : R) * q, r, (isEntire_C _).mul hq, ?_, ?_⟩
  · rwa [Polynomial.degree_C_mul_of_isUnit (u⁻¹).isUnit] at hr
  · rw [hdiv, Polynomial.coe_mul, Polynomial.coe_C]
    ring

omit [CompleteSpace R] in
/-- Uniqueness of the quotient in [Bel] Proposition II.2.8. -/
theorem eq_mul_add_q_unique {B : Polynomial R} (hB : IsUnit B.leadingCoeff)
    {q₁ q₂ : PowerSeries R} {r₁ r₂ : Polynomial R} (hq₁ : IsEntire q₁) (hq₂ : IsEntire q₂)
    (hr₁ : r₁.degree < B.degree) (hr₂ : r₂.degree < B.degree)
    (h : (B : PowerSeries R) * q₁ + r₁ = (B : PowerSeries R) * q₂ + r₂) : q₁ = q₂ := by
  obtain ⟨u, hu⟩ := hB
  have hm := monic_C_inv_mul u hu.symm
  have hu' : IsUnit ((u⁻¹ : Rˣ) : R) := (u⁻¹).isUnit
  have h0B : 0 < distRadius (Polynomial.C ((u⁻¹ : Rˣ) : R) * B) :=
    zero_lt_one.trans_le (one_le_distRadius _)
  have hdeg : (Polynomial.C ((u⁻¹ : Rˣ) : R) * B).degree = B.degree :=
    Polynomial.degree_C_mul_of_isUnit hu' B
  refine q_unique_of_monic_of_le hm le_rfl (hq₁ _ h0B) (hq₂ _ h0B)
    (r₁ := Polynomial.C ((u⁻¹ : Rˣ) : R) * r₁) (r₂ := Polynomial.C ((u⁻¹ : Rˣ) : R) * r₂)
    (by rwa [hdeg, Polynomial.degree_C_mul_of_isUnit hu'])
    (by rwa [hdeg, Polynomial.degree_C_mul_of_isUnit hu']) ?_
  have := congrArg (fun F ↦ C ((u⁻¹ : Rˣ) : R) * F) h
  simpa only [Polynomial.coe_mul, Polynomial.coe_C, mul_add, mul_assoc] using this

omit [CompleteSpace R] in
/-- Uniqueness of the remainder in [Bel] Proposition II.2.8. -/
theorem eq_mul_add_r_unique {B : Polynomial R} (hB : IsUnit B.leadingCoeff)
    {q₁ q₂ : PowerSeries R} {r₁ r₂ : Polynomial R} (hq₁ : IsEntire q₁) (hq₂ : IsEntire q₂)
    (hr₁ : r₁.degree < B.degree) (hr₂ : r₂.degree < B.degree)
    (h : (B : PowerSeries R) * q₁ + r₁ = (B : PowerSeries R) * q₂ + r₂) : r₁ = r₂ := by
  obtain rfl := eq_mul_add_q_unique hB hq₁ hq₂ hr₁ hr₂ h
  exact Polynomial.coe_inj.mp (add_left_cancel h)

omit [CompleteSpace R] in
/-- **Continuity of the Euclidean remainder** (norm form of [Bel] Proposition II.2.8): for a
monic `B` there is a radius `c ≥ 1` such that whenever `F = Bq + r` with `q` entire and
`deg r < deg B`, every coefficient of `r` is bounded by any bound `M` of the weighted
coefficients `‖coeff j F‖ c ^ j` (Martin's norm identity for Weierstrass division at a radius
where `B` is distinguished).  Applied to `F − trunc F`, it shows that the remainders of the
truncations of `F` converge to the remainder of `F`. -/
theorem exists_forall_norm_coeff_le_of_eq_mul_add {B : Polynomial R} (hB : B.Monic) :
    ∃ c : ℝ, 1 ≤ c ∧ ∀ {F q : PowerSeries R} {r : Polynomial R}, IsEntire q →
      r.degree < B.degree → F = (B : PowerSeries R) * q + r →
      ∀ {M : ℝ}, (∀ j, ‖coeff j F‖ * c ^ j ≤ M) → ∀ k, ‖r.coeff k‖ ≤ M := by
  have : Nontrivial R := NormOneClass.nontrivial
  have hc0 : Fact (0 < distRadius B) := ⟨zero_lt_one.trans_le (one_le_distRadius B)⟩
  refine ⟨distRadius B, one_le_distRadius B, fun {F q r} hq hr hF M hM k ↦ ?_⟩
  subst hF
  have hFr : IsRestricted (distRadius B) ((B : PowerSeries R) * q + (r : PowerSeries R)) :=
    isRestricted.add _ (isRestricted.mul _ (Polynomial.isRestricted_toPowerSeries _ B)
      (hq _ hc0.out)) (Polynomial.isRestricted_toPowerSeries _ r)
  have hmax := Restricted.norm_eq_max_of_eq_mul_add_of_isMulDistinguished
    (isMulDistinguished_of_monic hB le_rfl) (f := restrictedOf hFr)
    (q := restrictedOf (hq _ hc0.out)) (Polynomial.degree_eq_natDegree hB.ne_zero ▸ hr)
    (Subtype.ext rfl)
  have h1 := Restricted.norm_coeff_mul_pow_le (distRadius B) (Polynomial.toRestricted _ r) k
  rw [Polynomial.val_toRestricted, Polynomial.coeff_coe] at h1
  calc ‖r.coeff k‖ ≤ ‖r.coeff k‖ * distRadius B ^ k :=
        le_mul_of_one_le_right (norm_nonneg _) (one_le_pow₀ (one_le_distRadius B))
    _ ≤ ‖restrictedOf hFr‖ := h1.trans ((le_max_right _ _).trans hmax.ge)
    _ ≤ M := (Restricted.norm_le_iff _ _).mpr hM

omit [IsUltrametricDist R] [CompleteSpace R] [NormOneClass R] in
/-- **[JN] Definition 2.2.1.**  Two entire series are *relatively prime* if they generate
the unit ideal of `R{{T}}`: `aF + bG = 1` with `a, b` entire. -/
def IsEntireCoprime (F G : PowerSeries R) : Prop :=
  ∃ a b : PowerSeries R, IsEntire a ∧ IsEntire b ∧ a * F + b * G = 1

omit [IsUltrametricDist R] [CompleteSpace R] [NormOneClass R] in
theorem IsEntireCoprime.symm {F G : PowerSeries R} (h : IsEntireCoprime F G) :
    IsEntireCoprime G F :=
  let ⟨a, b, ha, hb, h⟩ := h
  ⟨b, a, hb, ha, (add_comm _ _).trans h⟩

omit [CompleteSpace R] [NormOneClass R] in
/-- Relative primality passes to a multiple of the second series against the first:
`(Q, S) = 1` and `(Q, S') = 1` give `(Q, S S') = 1`. -/
theorem IsEntireCoprime.mul_right {F G G' : PowerSeries R} (hF : IsEntire F) (hG : IsEntire G)
    (hG' : IsEntire G') (h : IsEntireCoprime F G) (h' : IsEntireCoprime F G') :
    IsEntireCoprime F (G * G') := by
  obtain ⟨a, b, ha, hb, h⟩ := h
  obtain ⟨a', b', ha', hb', h'⟩ := h'
  refine ⟨a * a' * F + a * b' * G' + b * a' * G, b * b',
    (((ha.mul ha').mul hF).add ((ha.mul hb').mul hG')).add ((hb.mul ha').mul hG), hb.mul hb', ?_⟩
  linear_combination (a' * F + b' * G') * h + h'

omit [CompleteSpace R] in
/-- The ideal `(P, Q)` of `R{{T}}` is the unit ideal iff the image of `Q` in
`R[T]/(P)` is a unit — the algebraic half of [Bel] Corollary II.2.9 used by
`isEntireCoprime_iff_isCoprime_of_eq_mul_add`. -/
theorem isCoprime_of_mul_add_eq_one {B a r : Polynomial R} {c : PowerSeries R}
    (hB : IsUnit B.leadingCoeff) (hc : IsEntire c)
    (h : c * (B : PowerSeries R) + (a : PowerSeries R) * (r : PowerSeries R) = 1) :
    IsCoprime B r := by
  have : Nontrivial R := NormOneClass.nontrivial
  rcases Nat.eq_zero_or_pos B.natDegree with hd | hd
  · obtain ⟨u, hu⟩ : IsUnit B := by
      rw [Polynomial.eq_C_of_natDegree_eq_zero hd]
      exact Polynomial.isUnit_C.mpr (by rwa [Polynomial.leadingCoeff, hd] at hB)
    exact ⟨((u⁻¹ : (Polynomial R)ˣ) : Polynomial R), 0, by
      rw [← hu, zero_mul, add_zero, u.inv_mul]⟩
  obtain ⟨d, e, he, hde⟩ := Polynomial.exists_eq_mul_add_of_isUnit_leadingCoeff hB (a * r)
  have hdeg : (1 : Polynomial R).degree < B.degree := by
    rw [Polynomial.degree_one,
      Polynomial.degree_eq_natDegree (Polynomial.ne_zero_of_natDegree_gt hd)]
    exact_mod_cast hd
  have hdiv : (B : PowerSeries R) * (c + d) + e = (B : PowerSeries R) * 0 + (1 : Polynomial R) := by
    have hde' := congrArg (fun p : Polynomial R ↦ (p : PowerSeries R)) hde
    push_cast at hde' ⊢
    linear_combination h - hde'
  have hq := eq_mul_add_q_unique hB (hc.add (Polynomial.isEntire_coe d)) isEntire_zero he hdeg hdiv
  have hr := eq_mul_add_r_unique hB (hc.add (Polynomial.isEntire_coe d)) isEntire_zero he hdeg hdiv
  subst hr
  exact ⟨-d, a, by linear_combination hde⟩

/-- **[Bel] Corollary II.2.9** in consumable form ("`R[T]/(B) → R{{T}}/(B)` is an
isomorphism"): a polynomial `B` with invertible leading coefficient is relatively prime in
`R{{T}}` to an entire `F` iff it is coprime in `R[T]` to the Euclidean remainder of `F`. -/
theorem isEntireCoprime_iff_isCoprime_of_eq_mul_add {B : Polynomial R}
    (hB : IsUnit B.leadingCoeff) {F q : PowerSeries R} {r : Polynomial R} (hq : IsEntire q)
    (hF : F = (B : PowerSeries R) * q + r) :
    IsEntireCoprime (B : PowerSeries R) F ↔ IsCoprime B r := by
  subst hF
  constructor
  · rintro ⟨a, b, ha, hb, h⟩
    obtain ⟨b₁, b₂, hb₁, -, hb₂⟩ := hb.exists_eq_mul_add hB
    refine isCoprime_of_mul_add_eq_one hB (a := b₂) (c := a + b * q + b₁ * r)
      ((ha.add (hb.mul hq)).add (hb₁.mul (Polynomial.isEntire_coe r))) ?_
    linear_combination h - (r : PowerSeries R) * hb₂
  · rintro ⟨u, v, huv⟩
    have huv' := congrArg (fun p : Polynomial R ↦ (p : PowerSeries R)) huv
    push_cast at huv'
    exact ⟨(u : PowerSeries R) - v * q, v, (Polynomial.isEntire_coe u).sub
      ((Polynomial.isEntire_coe v).mul hq), Polynomial.isEntire_coe v, by linear_combination huv'⟩

end Division

section GoodZero

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R] [NormOneClass R]

/-- **[Bel] Definition II.2.11.**  `a` is a *good zero of order `s`* of `F` if
`F(a) = F⁽¹⁾(a) = ⋯ = F⁽ˢ⁻¹⁾(a) = 0` and `F⁽ˢ⁾(a)` is a unit (divided derivatives). -/
def IsGoodZero (F : PowerSeries R) (a : R) (s : ℕ) : Prop :=
  (∀ i < s, evalT a (hasseDeriv i F) = 0) ∧ IsUnit (evalT a (hasseDeriv s F))

omit [NormOneClass R] in
/-- A good zero of positive order of a Fredholm series is a unit ([Bel] Exercise II.2.12). -/
theorem IsGoodZero.isUnit {F : PowerSeries R} (hF : IsEntire F) (h0 : coeff 0 F = 1) {a : R}
    {s : ℕ} (h : IsGoodZero F a s) (hs : 1 ≤ s) : IsUnit a := by
  have hFa : evalT a F = 0 := by simpa [hasseDeriv_zero] using h.1 0 hs
  set G : PowerSeries R := mk fun n ↦ coeff (n + 1) F with hG
  have hFG : F = 1 + X * G := by
    ext n
    cases n with
    | zero => simp [h0]
    | succ n => simp [hG, coeff_succ_X_mul]
  rw [hFG, isEntire_one.evalT_add (isEntire_X.mul (hF.shift 1)), evalT_one,
    isEntire_X.evalT_mul (hF.shift 1), evalT_X] at hFa
  exact isUnit_iff_exists.mpr ⟨-evalT a G, by linear_combination -hFa, by linear_combination -hFa⟩

private theorem fst_lt_of_ne {i : ℕ} {x : ℕ × ℕ} (hx : x ∈ Finset.antidiagonal i)
    (hne : x ≠ (i, 0)) : x.1 < i := by
  have := Finset.mem_antidiagonal.mp hx
  by_contra hlt
  exact hne (Prod.ext (by omega) (by omega))

omit [NormOneClass R] in
private theorem evalT_hasseDeriv_mul_eq_of_forall_lt {F G : PowerSeries R} (hF : IsEntire F)
    (hG : IsEntire G) {a : R} {i : ℕ} (hlow : ∀ j < i, evalT a (hasseDeriv j F) = 0) :
    evalT a (hasseDeriv i (F * G)) = evalT a (hasseDeriv i F) * evalT a G := by
  rw [hF.evalT_hasseDeriv_mul hG, Finset.sum_eq_single (i, 0)]
  · rw [hasseDeriv_zero]
  · exact fun x hx hne ↦ by rw [hlow x.1 (fst_lt_of_ne hx hne), zero_mul]
  · exact fun habs ↦ absurd (Finset.mem_antidiagonal.mpr (add_zero i)) habs

omit [NormOneClass R] in
/-- Good zeros are stable under multiplication by an entire factor that is a unit at `a`
(Leibniz rule). -/
theorem IsGoodZero.mul {F G : PowerSeries R} (hF : IsEntire F) (hG : IsEntire G) {a : R}
    {s : ℕ} (h : IsGoodZero F a s) (hG1 : IsUnit (evalT a G)) : IsGoodZero (F * G) a s := by
  refine ⟨fun i hi ↦ ?_, ?_⟩
  · rw [evalT_hasseDeriv_mul_eq_of_forall_lt hF hG fun j hj ↦ h.1 j (hj.trans hi), h.1 i hi,
      zero_mul]
  · rw [evalT_hasseDeriv_mul_eq_of_forall_lt hF hG h.1]
    exact h.2.mul hG1

omit [NormOneClass R] in
/-- Conversely, a good zero of a product with a factor that is a unit at `a` is a good zero
of the other factor, of the same order (Leibniz rule). -/
theorem IsGoodZero.of_mul {F G : PowerSeries R} (hF : IsEntire F) (hG : IsEntire G) {a : R}
    {s : ℕ} (h : IsGoodZero (F * G) a s) (hG1 : IsUnit (evalT a G)) : IsGoodZero F a s := by
  have hlow : ∀ i < s, evalT a (hasseDeriv i F) = 0 := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      have := h.1 i hi
      rw [evalT_hasseDeriv_mul_eq_of_forall_lt hF hG fun j hj ↦ ih j hj (hj.trans hi)] at this
      exact hG1.mul_left_eq_zero.mp this
  refine ⟨hlow, ?_⟩
  have := h.2
  rw [evalT_hasseDeriv_mul_eq_of_forall_lt hF hG hlow] at this
  exact isUnit_of_mul_isUnit_left this

omit [CompleteSpace R] [NormOneClass R] in
private theorem isEntire_one_sub_C_mul_X (b : R) : IsEntire (1 - C b * X) :=
  isEntire_one.sub ((isEntire_C b).mul isEntire_X)

omit [NormOneClass R] in
/-- Evaluation of the linear factor `1 - bX`. -/
theorem evalT_one_sub_C_mul_X (a b : R) : evalT a (1 - C b * X) = 1 - b * a := by
  rw [isEntire_one.evalT_sub ((isEntire_C b).mul isEntire_X), evalT_one,
    (isEntire_C b).evalT_mul isEntire_X, evalT_C, evalT_X]

omit [NormOneClass R] in
/-- A factorisation `(1 - bX)ˢ G` with `b a = 1` and `G(a)` a unit exhibits `a` as a good zero
of order `s` (the converse of `IsGoodZero.exists_factor`). -/
theorem IsGoodZero.of_factor {G : PowerSeries R} (hG : IsEntire G) {a b : R} (hba : b * a = 1)
    (hb : IsUnit b) (hGa : IsUnit (evalT a G)) (s : ℕ) :
    IsGoodZero ((1 - C b * X) ^ s * G) a s :=
  ⟨fun _ hi ↦ evalT_hasseDeriv_pow_mul_of_lt hba hG hi, by
    rw [evalT_hasseDeriv_pow_mul_self hba hG]
    exact (hb.neg.pow s).mul hGa⟩

omit [NormOneClass R] in
private theorem isGoodZero_of_one_sub_C_mul_X_mul {G : PowerSeries R} (hG : IsEntire G) {a b : R}
    (hba : b * a = 1) (hb : IsUnit b) {s : ℕ}
    (h : IsGoodZero ((1 - C b * X) * G) a (s + 1)) : IsGoodZero G a s := by
  have hL := isEntire_one_sub_C_mul_X b
  have hLa : evalT a (1 - C b * X) = 0 := by rw [evalT_one_sub_C_mul_X, hba, sub_self]
  have key : ∀ i, evalT a (hasseDeriv (i + 1) ((1 - C b * X) * G)) =
      -b * evalT a (hasseDeriv i G) := fun i ↦ by
    rw [hasseDeriv_one_sub_C_mul_X_mul,
      (hL.mul (hG.hasseDeriv _)).evalT_sub ((isEntire_C b).mul (hG.hasseDeriv _)),
      hL.evalT_mul (hG.hasseDeriv _), hLa, zero_mul, zero_sub,
      (isEntire_C b).evalT_mul (hG.hasseDeriv _), evalT_C, neg_mul]
  refine ⟨fun i hi ↦ ?_, ?_⟩
  · have := h.1 (i + 1) (by omega)
    rw [key] at this
    exact hb.neg.mul_right_eq_zero.mp this
  · have := h.2
    rw [key] at this
    exact isUnit_of_mul_isUnit_right this

/-- **[Bel] §II.2.3**: at a good zero `a` of order `s` (a unit `u`), a Fredholm series factors
as `F = (1 − u⁻¹T)ˢ G` with `G` entire and `G(a)` a unit. -/
theorem IsGoodZero.exists_factor {F : PowerSeries R} (hF : IsEntire F) (h0 : coeff 0 F = 1)
    {s : ℕ} (u : Rˣ) (h : IsGoodZero F (u : R) s) :
    ∃ G : PowerSeries R, IsEntire G ∧ IsUnit (evalT (u : R) G) ∧
      F = (1 - C ((u⁻¹ : Rˣ) : R) * X) ^ s * G := by
  have : Nontrivial R := NormOneClass.nontrivial
  induction s generalizing F with
  | zero => exact ⟨F, hF, by simpa [hasseDeriv_zero] using h.2, by simp⟩
  | succ s ih =>
    set b : R := ((u⁻¹ : Rˣ) : R)
    have hbu : b * u = 1 := u.inv_mul
    have hFu : evalT (u : R) F = 0 := by simpa [hasseDeriv_zero] using h.1 0 s.succ_pos
    set B : Polynomial R := Polynomial.C (-b) * Polynomial.X + Polynomial.C 1 with hB_def
    have hb0 : -b ≠ 0 := neg_ne_zero.mpr (u⁻¹).ne_zero
    have hBcoe : (B : PowerSeries R) = 1 - C b * X := by
      rw [hB_def]
      push_cast
      rw [map_neg, map_one]
      ring
    obtain ⟨G₁, r, hG₁, hr, hdiv⟩ := hF.exists_eq_mul_add (B := B)
      (by rw [Polynomial.leadingCoeff_linear hb0]; exact (u⁻¹).isUnit.neg)
    rw [Polynomial.degree_linear hb0, Nat.WithBot.lt_one_iff_le_zero] at hr
    rw [Polynomial.eq_C_of_degree_le_zero hr, hBcoe, Polynomial.coe_C] at hdiv
    have hL := isEntire_one_sub_C_mul_X b
    have hLu : evalT (u : R) (1 - C b * X) = 0 := by rw [evalT_one_sub_C_mul_X, hbu, sub_self]
    have hr0 : r.coeff 0 = 0 := by
      rwa [hdiv, (hL.mul hG₁).evalT_add (isEntire_C _), hL.evalT_mul hG₁, hLu, zero_mul, zero_add,
        evalT_C] at hFu
    rw [hr0, map_zero, add_zero] at hdiv
    have h0' : coeff 0 G₁ = 1 := by
      rwa [hdiv, coeff_zero_eq_constantCoeff_apply, map_mul, map_sub, map_one, map_mul,
        constantCoeff_C, constantCoeff_X, mul_zero, sub_zero, one_mul,
        ← coeff_zero_eq_constantCoeff_apply] at h0
    obtain ⟨G, hG, hGu, hG₁G⟩ :=
      ih hG₁ h0' (isGoodZero_of_one_sub_C_mul_X_mul hG₁ hbu (u⁻¹).isUnit (hdiv ▸ h))
    exact ⟨G, hG, hGu, by rw [hdiv, hG₁G, pow_succ', mul_assoc]⟩

end GoodZero

end PowerSeries

end
