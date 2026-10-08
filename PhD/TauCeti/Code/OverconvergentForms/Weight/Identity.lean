/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import PhD.TauCeti.Code.RigidAnalyticGeometry.Restricted.PowerSeries.MulWeierstrassPrep
import PhD.TauCeti.Code.RigidAnalyticGeometry.Restricted.Sum
import PhD.TauCeti.Code.OverconvergentForms.Weight.Mobius

/-!
# The identity theorem for restricted power series

A restricted power series in one variable over a complete nonarchimedean field vanishing at
infinitely many points of the closed unit disc is zero (Strassmann's theorem, from Weierstrass
preparation: `f = e · ω` with `e` a unit and `ω` a polynomial, so the zeros of `f` are the roots of
`ω`). In several variables, a restricted series vanishing on a product `Z^σ` of an infinite subset
`Z` of the closed unit disc is zero, by induction on the number of variables, one variable at a
time; and a series vanishing at the integral points `M n`, `n ∈ ℕ^σ`, of the image of an integral
matrix `M` with `det M ≠ 0` is zero, by Cramer's rule — Buzzard's "determinant calculation".

[Buz07, proof of Proposition 8.3, pp. 63–64]: "it suffices […] to prove that a map of rigid spaces
`f : B₁ → 𝔸¹` which sends every element of `𝒪` to `0` must be identically `0`, that is, that `𝒪` is
Zariski-dense in `B₁`. It suffices to show that `f` vanishes on a small polydisc centre `0`, and one
can check this on points. Again choose a `ℤ_p`-basis `(e_1, e_2, …, e_d)` of `𝒪` as a `ℤ_p`-module.
It suffices to prove that for all complete extensions `L` of `K`, `f` is zero on all `L`-points of
`B₁` of the form `z_1 e_1 + z_2 e_2 + … + z_d e_d` with `z_i ∈ 𝒪_L`, as this contains all the
`L`-points of a small polydisc in `B₁` by a determinant calculation. […] consider the function on
the affinoid unit disc over `L` sending `z_1` to `f(z_1 e_1 + z_2 e_2 + …)`. This is a function on a
closed `1`-ball that vanishes at infinitely many points, and hence it is identically zero. Now fix
`z_1 ∈ 𝒪_L` and `z_β ∈ ℤ_p` for `β ≥ 3`, and let `z_2` vary, and so on, to deduce that `f` is
identically `0`."

This is the `p`-adic-functional-analysis roadmap's §4.1.5 (one variable) and the several-variable
identity theorem of the overconvergent-forms roadmap's §1.2.3; it lives here as a seam until that
roadmap's Layer 4 is built.

## Main results

* `PowerSeries.Restricted.eq_zero_of_forall_aeval_eq_zero`: Strassmann's theorem.
* `MvPowerSeries.Restricted.aeval_map_sumEquiv`: on `K⟨X, Y⟩ ≅ K⟨Y⟩⟨X⟩`, specialising the
  inner variables and then evaluating the outer ones is evaluation.
* `MvPowerSeries.Restricted.eq_zero_of_forall_aeval_eq_zero`: vanishing on `Z^σ` for an infinite
  `Z` in the closed unit disc.
* `MvPowerSeries.Restricted.eq_zero_of_forall_aeval_mulVec_natCast_eq_zero`: vanishing at the
  points `M n`, `n ∈ ℕ^σ`, for an integral `M` with `det M ≠ 0` (characteristic zero).
* `Matrix.norm_det_le_one_of_forall_norm_le_one`: the ultrametric determinant bound.

Roadmap: §1.2.3. Tau Ceti home: `TauCeti/RingTheory/MvPowerSeries/Restricted/Identity.lean`.
-/

open MvPowerSeries MvPowerSeries.Restricted Filter Topology

/-! ### Ultrametric determinants -/

namespace Matrix

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [NormOneClass R] {n : Type*}
  [Fintype n] [DecidableEq n]

/-- Over an ultrametric normed ring, an integral matrix has integral determinant. -/
theorem norm_det_le_one_of_forall_norm_le_one {A : Matrix n n R} (hA : ∀ i j, ‖A i j‖ ≤ 1) :
    ‖A.det‖ ≤ 1 := by
  rw [Matrix.det_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun σ _ => ?_
  have hp : ‖∏ i, A (σ i) i‖ ≤ 1 := (Finset.norm_prod_le _ _).trans
    (Finset.prod_le_one (fun _ _ => norm_nonneg _) fun i _ => hA _ _)
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> rw [h]
  · rwa [one_smul]
  · rwa [Units.neg_smul, one_smul, norm_neg]

/-- Over an ultrametric normed ring, an integral matrix has integral adjugate. -/
theorem norm_adjugate_apply_le_one {A : Matrix n n R} (hA : ∀ i j, ‖A i j‖ ≤ 1) (i j : n) :
    ‖A.adjugate i j‖ ≤ 1 := by
  rw [Matrix.adjugate_apply]
  refine norm_det_le_one_of_forall_norm_le_one fun k l => ?_
  rcases eq_or_ne k j with rfl | hk
  · rw [Matrix.updateRow_self]
    rcases eq_or_ne l i with rfl | hl
    · simp
    · simp [hl]
  · rw [Matrix.updateRow_ne hk]
    exact hA k l

omit [NormOneClass R] [DecidableEq n] in
/-- Over an ultrametric normed ring, an integral matrix maps the unit polydisc into itself. -/
theorem norm_mulVec_apply_le_one {A : Matrix n n R} (hA : ∀ i j, ‖A i j‖ ≤ 1) {v : n → R}
    (hv : ∀ j, ‖v j‖ ≤ 1) (i : n) : ‖(A.mulVec v) i‖ ≤ 1 := by
  simp only [Matrix.mulVec, dotProduct]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun j _ => ?_
  exact (norm_mul_le _ _).trans (mul_le_one₀ (hA i j) (norm_nonneg _) (hv j))

end Matrix

/-! ### One variable: Strassmann's theorem -/

namespace PowerSeries.Restricted

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

omit [CompleteSpace K] in
/-- A nonzero restricted series over a field is Martin-distinguished at its greatest index
achieving the Gauss norm. Source: [Mar16, Definition 1.24]; BGR 5.2.1. -/
theorem exists_isMulDistinguished_of_ne_zero {f : PowerSeries.Restricted K 1} (hf : f ≠ 0) :
    ∃ s, IsMulDistinguished 1 f.1 s := by
  haveI : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩
  obtain ⟨k₀, hach, hlt⟩ := exists_greatest_achievesGaussNorm f hf
  have hnorm : ‖PowerSeries.coeff k₀ f.1‖ * 1 ^ k₀ = ‖f‖ := hach
  have hne : PowerSeries.coeff k₀ f.1 ≠ 0 := by
    intro h0
    rw [h0, norm_zero, zero_mul] at hnorm
    exact hf (norm_eq_zero.mp hnorm.symm)
  refine ⟨k₀, (isUnit_iff_ne_zero.mpr hne).isNormMulUnit, hach.symm, fun t ht => ?_⟩
  rw [hnorm]
  exact hlt t ht

/-- A unit of the Tate algebra does not vanish at any point of the closed unit disc. -/
theorem aeval_ne_zero_of_isUnit {e : PowerSeries.Restricted K 1} (he : IsUnit e) {x : K}
    (hx : ‖x‖ ≤ 1) :
    aeval (fun _ : Unit => (1 : ℝ)) (fun _ => x) (fun _ => hx) e ≠ 0 :=
  (he.map (aeval (fun _ : Unit => (1 : ℝ)) (fun _ => x) (fun _ => hx))).ne_zero

/-- Evaluating a polynomial, viewed as a restricted series, is polynomial evaluation. -/
private theorem aeval_toRestricted_eq_eval {z : K} (hz : ‖z‖ ≤ 1) (ω : Polynomial K) :
    aeval (fun _ : Unit => (1 : ℝ)) (fun _ => z) (fun _ => hz) (Polynomial.toRestricted 1 ω) =
      ω.eval z := by
  have h : (aeval (fun _ : Unit => (1 : ℝ)) (fun _ => z) (fun _ => hz)).toRingHom.comp
      (Polynomial.toRestricted 1) = Polynomial.evalRingHom z := by
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · simp only [RingHom.comp_apply, Polynomial.toRestricted_C, Polynomial.coe_evalRingHom,
        Polynomial.eval_C]
      exact (aeval_C (fun _ => hz) a).trans (Algebra.algebraMap_self_apply a)
    · simp only [RingHom.comp_apply, Polynomial.toRestricted_X, Polynomial.coe_evalRingHom,
        Polynomial.eval_X]
      exact aeval_X (fun _ => hz) ()
  exact RingHom.congr_fun h ω

/-- **Strassmann's theorem**: a restricted power series vanishing at infinitely many points of the
closed unit disc is zero. Source: PFA roadmap §4.1.5 ("obtained from Weierstrass preparation:
`f = P · u` with `P` a polynomial and `u` a unit of `K⟨X⟩`, so the zeros of `f` in the closed disc
are the roots of `P`"); [Buz07, p. 64] ("a function on a closed `1`-ball that vanishes at
infinitely many points […] is identically zero"). -/
theorem eq_zero_of_forall_aeval_eq_zero (Z : Set K) (hZ : Z.Infinite) (hZ1 : ∀ z ∈ Z, ‖z‖ ≤ 1)
    {f : PowerSeries.Restricted K 1}
    (hf : ∀ z (hz : z ∈ Z),
      aeval (fun _ : Unit => (1 : ℝ)) (fun _ => z) (fun _ => hZ1 z hz) f = 0) :
    f = 0 := by
  haveI : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩
  by_contra hf0
  obtain ⟨s, hs⟩ := exists_isMulDistinguished_of_ne_zero hf0
  obtain ⟨ω, e, hω, -, -, he, hfe⟩ := weierstrassPreparation_exists_of_isMulDistinguished hs
  have hroots : Z ⊆ {x | ω.IsRoot x} := fun z hz => by
    have h := hf z hz
    rw [hfe, map_mul] at h
    have hω0 := (mul_eq_zero.mp h).resolve_left (aeval_ne_zero_of_isUnit he.isUnit (hZ1 z hz))
    rw [aeval_toRestricted_eq_eval] at hω0
    exact hω0
  exact hω.ne_zero (Polynomial.eq_zero_of_infinite_isRoot ω (hZ.mono hroots))

end PowerSeries.Restricted

/-! ### Several variables -/

namespace MvPowerSeries.Restricted

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K] {σ : Type*}

/-- Evaluation depends only on the point, not on the proof that it lies in the polydisc. -/
theorem aeval_congr {c : σ → ℝ} {x x' : σ → K} (h : x = x') (hx : ∀ i, ‖x i‖ ≤ c i)
    (hx' : ∀ i, ‖x' i‖ ≤ c i) (f : Restricted K c) : aeval c x hx f = aeval c x' hx' f := by
  subst h
  rfl

/-- Over an empty index type a restricted series is its constant coefficient, and vanishing at
the (unique) point of the polydisc makes it zero. -/
theorem eq_zero_of_isEmpty_of_aeval_eq_zero [IsEmpty σ] {f : Restricted K (1 : σ → ℝ)}
    (hf : aeval 1 (fun _ => (0 : K)) (fun _ => by simp) f = 0) : f = 0 := by
  have hC : f = C 1 (MvPowerSeries.constantCoeff f.1) := by
    apply Subtype.ext
    refine MvPowerSeries.ext fun m => ?_
    obtain rfl : m = 0 := Subsingleton.elim m 0
    simp
  rw [hC, aeval_C, Algebra.algebraMap_self_apply] at hf
  rw [hC, hf, map_zero]

/-- Evaluation after renaming the variables along a bijection. -/
theorem aeval_renameEquiv {τ : Type*} (e : σ ≃ τ) {x : τ → K} (hx : ∀ j, ‖x j‖ ≤ 1)
    (f : Restricted K (1 : σ → ℝ)) :
    aeval 1 x hx (renameEquiv K e f) = aeval 1 (x ∘ e) (fun i => hx (e i)) f := by
  have h : (aeval 1 x hx).toRingHom.comp (renameEquiv K e).toRingHom =
      (aeval 1 (x ∘ e) (fun i => hx (e i))).toRingHom :=
    ringHom_ext_of_continuous ((continuous_aeval hx).comp (continuous_renameHom e))
      (continuous_aeval _) (fun a => by simp [aeval_C]) fun i => by simp
  exact RingHom.congr_fun h f

section SumEquiv

variable {R S : Type*} [NormedRing R] [IsUltrametricDist R] [NormedRing S] [IsUltrametricDist S]
  (c : σ → ℝ)

omit [NormedField K] [IsUltrametricDist K] [CompleteSpace K] in
/-- Applying a ring homomorphism to the coefficients fixes the constants. -/
theorem map_C {φ : R →+* S} (hφ : ∀ x, ‖φ x‖ ≤ ‖x‖) (a : R) : map c hφ (C c a) = C c (φ a) :=
  Subtype.ext (by simp only [val_map, val_C, MvPowerSeries.map_C])

omit [NormedField K] [IsUltrametricDist K] [CompleteSpace K] in
/-- Applying a ring homomorphism to the coefficients fixes the variables. -/
theorem map_X {φ : R →+* S} (hφ : ∀ x, ‖φ x‖ ≤ ‖x‖) (i : σ) : map c hφ (X R c i) = X S c i :=
  Subtype.ext (by simp only [val_map, val_X, MvPowerSeries.map_X])

omit [NormedField K] [IsUltrametricDist K] [CompleteSpace K] in
/-- The coefficients of `map c hφ f` are the images of the coefficients of `f`. -/
theorem coeff_map {φ : R →+* S} (hφ : ∀ x, ‖φ x‖ ≤ ‖x‖) (f : Restricted R c) (t : σ →₀ ℕ) :
    coeff t (map c hφ f).1 = φ (coeff t f.1) := by
  rw [val_map, MvPowerSeries.coeff_map]

omit [NormedField K] [IsUltrametricDist K] [CompleteSpace K] in
/-- Applying a norm-nonincreasing ring homomorphism to the coefficients is continuous. -/
theorem continuous_map [Fact (∀ i, 0 < c i)] {φ : R →+* S} (hφ : ∀ x, ‖φ x‖ ≤ ‖x‖) :
    Continuous (map c hφ) :=
  AddMonoidHomClass.continuous_of_bound _ 1 fun g => by
    rw [one_mul]
    exact norm_map_le _ _ g

end SumEquiv

section Sum

variable {τ : Type*}

/-- **Evaluating the inner variables first**: for `f ∈ K⟨X, Y⟩ ≅ K⟨Y⟩⟨X⟩`, specialising the
coefficients at `Y = y` and then evaluating at `X = x` is evaluation at `(x, y)`. Source: BGR
6.1.1/7 (`A⟨X, Y⟩ ≅ A⟨Y⟩⟨X⟩`); [Buz07, p. 64] (the function of one variable obtained by fixing the
others). -/
theorem aeval_map_sumEquiv (c : σ ⊕ τ → ℝ) [Fact (∀ i, 0 < c i)] {x : σ → K}
    (hx : ∀ i, ‖x i‖ ≤ (c ∘ Sum.inl) i) {y : τ → K} (hy : ∀ j, ‖y j‖ ≤ (c ∘ Sum.inr) j)
    (f : Restricted K c) :
    aeval (c ∘ Sum.inl) x hx
        (map (c ∘ Sum.inl) (φ := (aeval (c ∘ Sum.inr) y hy).toRingHom)
          (fun g => norm_aeval_le hy g) (sumEquiv c f)) =
      aeval c (Sum.elim x y) (fun i => by rcases i with i | j; exacts [hx i, hy j]) f := by
  have h : (aeval (c ∘ Sum.inl) x hx).toRingHom.comp
      ((map (c ∘ Sum.inl) (φ := (aeval (c ∘ Sum.inr) y hy).toRingHom)
        (fun g => norm_aeval_le hy g)).comp (sumEquiv (R := K) c).toRingHom) =
      (aeval c (Sum.elim x y) (fun i => by rcases i with i | j; exacts [hx i, hy j])).toRingHom :=
        by
    refine ringHom_ext_of_continuous
      ((continuous_aeval hx).comp
        ((MvPowerSeries.Restricted.continuous_map (c ∘ Sum.inl)
          (φ := (aeval (c ∘ Sum.inr) y hy).toRingHom) fun g => norm_aeval_le hy g).comp
          (continuous_sumEquiv c)))
      (continuous_aeval _) (fun a => ?_) fun i => ?_
    · simp [MvPowerSeries.Restricted.map_C, aeval_C]
    · rcases i with i | j
      · simp [MvPowerSeries.Restricted.map_X]
      · simp [MvPowerSeries.Restricted.map_C, aeval_C]
  exact RingHom.congr_fun h f

/-- The induction step: a series in the variables `α ⊕ Unit` vanishing on `Z^{α ⊕ Unit}` is zero,
given the theorem for `α`. Write `f ∈ K⟨Y, t⟩` as a series in `Y` over `K⟨t⟩`; for `z ∈ Z` the
specialisation at `t = z` vanishes on `Z^α`, so it is zero; hence every coefficient, a series in
`t`, vanishes on `Z`, and is zero by Strassmann's theorem. Source: [Buz07, p. 64] ("one variable
at a time"). -/
theorem eq_zero_of_forall_aeval_eq_zero_sum {α : Type*} (Z : Set K) (hZ : Z.Infinite)
    (hZ1 : ∀ z ∈ Z, ‖z‖ ≤ 1)
    (ih : ∀ g : Restricted K (1 : α → ℝ),
      (∀ y (hy : ∀ j, y j ∈ Z), aeval 1 y (fun j => hZ1 _ (hy j)) g = 0) → g = 0)
    {f : Restricted K (1 : α ⊕ Unit → ℝ)}
    (hf : ∀ x (hx : ∀ o, x o ∈ Z), aeval 1 x (fun o => hZ1 _ (hx o)) f = 0) : f = 0 := by
  have hspec : ∀ z (hz : z ∈ Z),
      map ((1 : α ⊕ Unit → ℝ) ∘ Sum.inl)
        (φ := (aeval ((1 : α ⊕ Unit → ℝ) ∘ Sum.inr) (fun _ => z) (fun _ => hZ1 z hz)).toRingHom)
        (fun g => norm_aeval_le _ g) (sumEquiv (R := K) (1 : α ⊕ Unit → ℝ) f) = 0 := by
    intro z hz
    refine ih _ fun y hy => ?_
    show aeval ((1 : α ⊕ Unit → ℝ) ∘ Sum.inl) y (fun j => hZ1 _ (hy j)) _ = 0
    rw [aeval_map_sumEquiv]
    exact (aeval_congr rfl _ _ f).trans (hf (Sum.elim y fun _ => z) fun o => by
      rcases o with j | u
      exacts [hy j, hz])
  have hcoeff : ∀ m, coeff m (sumEquiv (R := K) (1 : α ⊕ Unit → ℝ) f).1 = 0 := by
    intro m
    refine PowerSeries.Restricted.eq_zero_of_forall_aeval_eq_zero Z hZ hZ1 fun z hz => ?_
    have h := congrArg (fun G : Restricted K ((1 : α ⊕ Unit → ℝ) ∘ Sum.inl) => coeff m G.1)
      (hspec z hz)
    simp only [coeff_map] at h
    exact h
  have hF : sumEquiv (R := K) (1 : α ⊕ Unit → ℝ) f = 0 :=
    Subtype.ext (MvPowerSeries.ext fun m => by rw [hcoeff m]; rfl)
  exact (map_eq_zero_iff _ (sumEquiv (R := K) _).injective).mp hF

end Sum

/-- **The several-variable identity theorem**: a restricted power series in finitely many variables
vanishing on `Z^σ`, for an infinite subset `Z` of the closed unit disc, is zero. Source: roadmap
§1.2.3; [Buz07, p. 64] ("Now fix `z_1 ∈ 𝒪_L` and `z_β ∈ ℤ_p` for `β ≥ 3`, and let `z_2` vary, and so
on, to deduce that `f` is identically `0`"). -/
theorem eq_zero_of_forall_aeval_eq_zero [Finite σ] (Z : Set K) (hZ : Z.Infinite)
    (hZ1 : ∀ z ∈ Z, ‖z‖ ≤ 1) {f : Restricted K (1 : σ → ℝ)}
    (hf : ∀ x (hx : ∀ i, x i ∈ Z), aeval 1 x (fun i => hZ1 _ (hx i)) f = 0) : f = 0 := by
  have hfin : ∀ (n : ℕ) (g : Restricted K (1 : Fin n → ℝ)),
      (∀ x (hx : ∀ i, x i ∈ Z), aeval 1 x (fun i => hZ1 _ (hx i)) g = 0) → g = 0 := by
    intro n
    induction n with
    | zero => exact fun g hg => eq_zero_of_isEmpty_of_aeval_eq_zero (hg _ fun i => i.elim0)
    | succ n ih =>
      intro g hg
      let e : Fin (n + 1) ≃ Fin n ⊕ Unit :=
        (finSuccEquiv n).trans (Equiv.optionEquivSumPUnit (Fin n))
      have h := eq_zero_of_forall_aeval_eq_zero_sum Z hZ hZ1 ih (f := renameEquiv K e g)
        fun x hx => by
          rw [aeval_renameEquiv]
          exact hg _ fun i => hx (e i)
      exact (map_eq_zero_iff _ (renameEquiv K e).injective).mp h
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin σ
  have h := hfin n (renameEquiv K e f) fun x hx => by
    rw [aeval_renameEquiv]
    exact hf _ fun i => hx (e i)
  exact (map_eq_zero_iff _ (renameEquiv K e).injective).mp h

section Linear

variable [Fintype σ] [DecidableEq σ]

/-- The linear substitution `z_i ↦ ∑_β M_{iβ} w_β` by an integral matrix, as the tuple to be
substituted. -/
noncomputable def linearForms (M : Matrix σ σ K) : σ → Restricted K (1 : σ → ℝ) :=
  fun i => ∑ β, C 1 (M i β) * X K 1 β

omit [CompleteSpace K] [DecidableEq σ] in
theorem norm_linearForms_le_one {M : Matrix σ σ K} (hM : ∀ i j, ‖M i j‖ ≤ 1) (i : σ) :
    ‖linearForms M i‖ ≤ 1 := by
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun β _ => ?_
  refine (norm_mul_le _ _).trans ?_
  rw [norm_C, norm_X]
  simpa using hM i β

omit [DecidableEq σ] in
/-- Evaluating the linear substitution: `(f ∘ M)(y) = f(M y)`. -/
theorem aeval_aeval_linearForms {M : Matrix σ σ K} (hM : ∀ i j, ‖M i j‖ ≤ 1) {y : σ → K}
    (hy : ∀ j, ‖y j‖ ≤ 1) (f : Restricted K (1 : σ → ℝ)) :
    aeval 1 y hy (aeval 1 (linearForms M) (norm_linearForms_le_one hM) f) =
      aeval 1 (M.mulVec y) (Matrix.norm_mulVec_apply_le_one hM hy) f := by
  rw [aeval_aeval]
  refine aeval_congr (funext fun i => ?_) _ _ f
  simp [linearForms, aeval_C, Matrix.mulVec, dotProduct]

/-- **Buzzard's determinant calculation**: in characteristic zero, a restricted series vanishing at
the points `M n`, `n ∈ ℕ^σ`, for an integral matrix `M` with `det M ≠ 0`, is zero: `f ∘ M`
vanishes on `ℕ^σ`, hence is zero; so `f` vanishes on `M(polydisc) ⊇ det(M) · polydisc` by
Cramer's rule, hence on `(det M · ℕ)^σ`, hence is zero. Source: [Buz07, p. 64] ("this contains all
the `L`-points of a small polydisc in `B₁` by a determinant calculation"). -/
theorem eq_zero_of_forall_aeval_mulVec_natCast_eq_zero [CharZero K] {M : Matrix σ σ K}
    (hM : ∀ i j, ‖M i j‖ ≤ 1) (hdet : M.det ≠ 0) {f : Restricted K (1 : σ → ℝ)}
    (hf : ∀ n : σ → ℕ, aeval 1 (M.mulVec fun β => (n β : K))
      (Matrix.norm_mulVec_apply_le_one hM fun β => IsUltrametricDist.norm_natCast_le_one K (n β))
      f = 0) :
    f = 0 := by
  have hNat : ∀ z ∈ Set.range (Nat.cast : ℕ → K), ‖z‖ ≤ 1 := by
    rintro _ ⟨n, rfl⟩
    exact IsUltrametricDist.norm_natCast_le_one K n
  have hg : aeval 1 (linearForms M) (norm_linearForms_le_one hM) f = 0 := by
    refine eq_zero_of_forall_aeval_eq_zero _ (Set.infinite_range_of_injective Nat.cast_injective)
      hNat fun x hx => ?_
    choose n hn using fun i => hx i
    rw [aeval_aeval_linearForms hM]
    refine (aeval_congr ?_ _ _ f).trans (hf n)
    rw [show x = fun β => (n β : K) from funext fun β => (hn β).symm]
  have hDet : ∀ z ∈ Set.range fun n : ℕ => M.det * n, ‖z‖ ≤ 1 := by
    rintro _ ⟨n, rfl⟩
    rw [norm_mul]
    exact mul_le_one₀ (Matrix.norm_det_le_one_of_forall_norm_le_one hM) (norm_nonneg _)
      (IsUltrametricDist.norm_natCast_le_one K n)
  refine eq_zero_of_forall_aeval_eq_zero _
    (Set.infinite_range_of_injective ((mul_right_injective₀ hdet).comp Nat.cast_injective))
    hDet fun x hx => ?_
  choose n hn using fun i => hx i
  have hv : ∀ i, ‖(M.adjugate.mulVec fun β => (n β : K)) i‖ ≤ 1 :=
    Matrix.norm_mulVec_apply_le_one (Matrix.norm_adjugate_apply_le_one hM)
      fun β => IsUltrametricDist.norm_natCast_le_one K (n β)
  have hx : x = M.mulVec (M.adjugate.mulVec fun β => (n β : K)) := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec, Matrix.one_mulVec]
    funext i
    rw [Pi.smul_apply, smul_eq_mul, ← hn i]
    rfl
  rw [aeval_congr (c := 1) hx _ (Matrix.norm_mulVec_apply_le_one hM hv),
    ← aeval_aeval_linearForms hM hv,
    hg, map_zero]

end Linear

end MvPowerSeries.Restricted
