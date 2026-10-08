/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.NumberTheory.Padics.PadicIntegers
import PhD.TauCeti.Code.PadicFunctionalAnalysis.Operator.Banach
import PhD.TauCeti.Code.PadicFunctionalAnalysis.Operator.BanachSteinhaus
import PhD.TauCeti.Code.PadicFunctionalAnalysis.Operator.ClosedGraph
import PhD.TauCeti.Code.PadicFunctionalAnalysis.Operator.Finite

/-!
# Examples for Layer 1

The worked examples of the roadmap's Layer 1, as theorems: multiplication by `a` on a normed
commutative ring with `‖1‖ = 1` has operator norm exactly `‖a‖` (⚠ the roadmap's "can be smaller
otherwise" is impossible once `‖1‖ = 1`); the open mapping constant of `(x, y) ↦ x + ϖ y` is `1` and
cannot be improved; a continuous bijection of Banach `ℚ_p`-spaces whose inverse has norm `p`; the
identity from `ℤ_p` with the squared norm to `ℤ_p`, continuous and unbounded, which is why the Tate
hypothesis of §1.1.2 cannot be dropped; and a principal ideal of `ℓ^∞(ℕ, ℚ_p)` that is not closed,
so that `ℓ^∞(ℕ, ℚ_p)` is a non-Noetherian Banach–Tate ring and the Noetherian hypothesis of
`Submodule.isClosed_of_isNoetherianRing` cannot be dropped.

⚠ The roadmap's examples on `C₀(I, R)` — coordinate evaluation has norm `1`, the diagonal operator
`diag(dₙ)` — need the `IsBoundedSMul R C₀(I, R)` instance and the basis vectors of §2.1, which
Mathlib lacks; they are examples of Layer 2.

Roadmap: `PhD/TauCeti/Roadmaps/PadicFunctionalAnalysis/README.md`, Layer 1 "Examples", §1.1.2
(the `ℤ_p` counterexample) and §1.4.3. Tau Ceti home: the test files next to
`TauCeti/Analysis/Normed/Operator/Ultra/`.
-/

open Filter Topology NormedRing

/-! ### Multiplication by a ring element -/

section MulLeft

open scoped ContinuousLinearMap.Ultra

variable {R : Type*} [NormedCommRing R] [NormOneClass R]

/-- Multiplication by `a`, as a continuous linear map `R →L[R] R`. -/
noncomputable def mulLeftL (a : R) : R →L[R] R :=
  (LinearMap.mulLeft R a).mkContinuous ‖a‖ fun x ↦ _root_.norm_mul_le a x

omit [NormOneClass R] in
@[simp]
theorem mulLeftL_apply (a x : R) : mulLeftL a x = a * x := rfl

/-- Source: roadmap, Layer 1 Examples ("multiplication by `a` on `R` has norm `‖a‖` when `a` is
multiplicative"), corrected: equality holds for every `a` once `‖1‖ = 1`. -/
theorem opNorm_mulLeftL (a : R) : ‖mulLeftL a‖ = ‖a‖ := by
  refine le_antisymm
    (ContinuousLinearMap.Ultra.opNorm_le_bound _ (norm_nonneg a) fun x ↦ _root_.norm_mul_le a x) ?_
  have h := ContinuousLinearMap.Ultra.le_opNorm_of_bound (mulLeftL a)
    ⟨‖a‖, fun x ↦ _root_.norm_mul_le a x⟩ 1
  rwa [mulLeftL_apply, mul_one, norm_one, mul_one] at h

end MulLeft

/-! ### The open mapping constant of `(x, y) ↦ x + ϖ y` -/

section Quotient

variable {R : Type*} [NormedCommRing R] [NormOneClass R] [IsUltrametricDist R]
  (ϖ : PseudoUniformizer R)

omit [NormOneClass R] in
/-- The ultrametric bound behind `addPseudoUniformizerSMul`. -/
private theorem norm_add_mul_le (m : R × R) : ‖m.1 + (ϖ : R) * m.2‖ ≤ ‖m‖ :=
  (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (norm_fst_le m)
    (((_root_.norm_mul_le _ _).trans (mul_le_of_le_one_left (norm_nonneg _) ϖ.norm_lt_one.le)).trans
      (norm_snd_le m)))

/-- The map `(x, y) ↦ x + ϖ y`, as a continuous linear map `R × R →L[R] R`. -/
noncomputable def addPseudoUniformizerSMul : R × R →L[R] R :=
  (LinearMap.fst R R R + (ϖ : R) • LinearMap.snd R R R).mkContinuous 1 fun m ↦ by
    rw [one_mul]
    exact norm_add_mul_le ϖ m

omit [NormOneClass R] in
@[simp]
theorem addPseudoUniformizerSMul_apply (m : R × R) :
    addPseudoUniformizerSMul ϖ m = m.1 + (ϖ : R) * m.2 := rfl

omit [NormOneClass R] in
/-- Source: roadmap, Layer 1 Examples ("the open mapping constant for the quotient map
`R ² → R`, `(x, y) ↦ x + ϖ y`"): the constant `1` works. -/
theorem exists_preimage_norm_le_addPseudoUniformizerSMul (n : R) :
    ∃ m : R × R, addPseudoUniformizerSMul ϖ m = n ∧ ‖m‖ ≤ 1 * ‖n‖ :=
  ⟨(n, 0), by simp, by simp [Prod.norm_def]⟩

/-- Source: roadmap, Layer 1 Examples: no constant below `1` works. -/
theorem one_le_of_forall_exists_preimage_norm_le_addPseudoUniformizerSMul {C : ℝ}
    (hC : ∀ n : R, ∃ m : R × R, addPseudoUniformizerSMul ϖ m = n ∧ ‖m‖ ≤ C * ‖n‖) : 1 ≤ C := by
  obtain ⟨m, hm, hle⟩ := hC 1
  calc (1 : ℝ) = ‖addPseudoUniformizerSMul ϖ m‖ := by rw [hm, norm_one]
    _ ≤ ‖m‖ := norm_add_mul_le ϖ m
    _ ≤ C * ‖(1 : R)‖ := hle
    _ = C := by rw [norm_one, mul_one]

end Quotient

/-! ### A continuous bijection whose inverse has norm `p` -/

section Padic

variable (p : ℕ) [Fact p.Prime]

/-- Source: roadmap, Layer 1 Examples ("a continuous bijection of Banach `ℚ_p`-spaces whose inverse
has norm `p`"): multiplication by `p` on `ℚ_p`. -/
theorem bijective_padic_smul_id :
    Function.Bijective ((p : ℚ_[p]) • ContinuousLinearMap.id ℚ_[p] ℚ_[p]) := by
  have hp : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  refine ⟨fun x y hxy ↦ ?_, fun y ↦ ⟨(p : ℚ_[p])⁻¹ * y, ?_⟩⟩
  · simpa [hp] using hxy
  · simp [hp]

/-- Source: roadmap, Layer 1 Examples: the inverse, multiplication by `p⁻¹`, has norm `p`
(Mathlib's operator norm, which agrees with the scoped one by `norm_eq_opNorm`). -/
theorem norm_padic_inv_smul_id : ‖(p : ℚ_[p])⁻¹ • ContinuousLinearMap.id ℚ_[p] ℚ_[p]‖ = p := by
  rw [norm_smul, norm_inv, Padic.norm_p, inv_inv, ContinuousLinearMap.norm_id, mul_one]

end Padic

/-! ### Continuity is not boundedness over `ℤ_p` -/

/-- `ℤ_p` with the norm `x ↦ ‖x‖ ^ 2`, a normed `ℤ_p`-module; a type synonym. Source: roadmap §1.1.2
("the identity map from `ℤ_p` with the norm `‖x‖²` (a normed `ℤ_p`-module) to `ℤ_p` with its norm
is continuous and unbounded"). -/
def PadicIntSq (p : ℕ) [Fact p.Prime] : Type := ℤ_[p]

namespace PadicIntSq

variable (p : ℕ) [Fact p.Prime]

noncomputable instance : AddCommGroup (PadicIntSq p) := inferInstanceAs (AddCommGroup ℤ_[p])

noncomputable instance : Module ℤ_[p] (PadicIntSq p) := inferInstanceAs (Module ℤ_[p] ℤ_[p])

/-- The identity `ℤ_[p] → PadicIntSq p`, as a `ℤ_[p]`-linear equivalence. -/
noncomputable def toPadicIntSq : ℤ_[p] ≃ₗ[ℤ_[p]] PadicIntSq p := LinearEquiv.refl ℤ_[p] ℤ_[p]

/-- The squared norm. -/
noncomputable instance : NormedAddCommGroup (PadicIntSq p) :=
  AddGroupNorm.toNormedAddCommGroup
    { toFun := fun x ↦ ‖((toPadicIntSq p).symm x : ℤ_[p])‖ ^ 2
      map_zero' := by simp
      add_le' := fun x y ↦ by
        have h := IsUltrametricDist.norm_add_le_max ((toPadicIntSq p).symm x)
          ((toPadicIntSq p).symm y)
        rw [map_add]
        rcases le_total ‖(toPadicIntSq p).symm x‖ ‖(toPadicIntSq p).symm y‖ with hxy | hxy
        · rw [max_eq_right hxy] at h
          exact (pow_le_pow_left₀ (norm_nonneg _) h 2).trans (le_add_of_nonneg_left (sq_nonneg _))
        · rw [max_eq_left hxy] at h
          exact (pow_le_pow_left₀ (norm_nonneg _) h 2).trans (le_add_of_nonneg_right (sq_nonneg _))
      neg' := fun x ↦ by
        rw [map_neg, norm_neg]
      eq_zero_of_map_eq_zero' := fun x hx ↦ by simpa using hx }

theorem norm_def (x : PadicIntSq p) : ‖x‖ = ‖((toPadicIntSq p).symm x : ℤ_[p])‖ ^ 2 := rfl

/-- Source: roadmap §1.1.2 ("a normed `ℤ_p`-module"). -/
instance : IsBoundedSMul ℤ_[p] (PadicIntSq p) := .of_norm_smul_le fun r x ↦ by
  rw [norm_def, norm_def, map_smul, smul_eq_mul, norm_mul, mul_pow]
  exact mul_le_mul_of_nonneg_right
    (pow_le_of_le_one (norm_nonneg r) (PadicInt.norm_le_one r) two_ne_zero) (sq_nonneg _)

instance : IsUltrametricDist (PadicIntSq p) :=
  IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm fun x y ↦ by
    rw [norm_def, norm_def, norm_def, map_add]
    have h := IsUltrametricDist.norm_add_le_max ((toPadicIntSq p).symm x) ((toPadicIntSq p).symm y)
    rcases le_total ‖(toPadicIntSq p).symm x‖ ‖(toPadicIntSq p).symm y‖ with hxy | hxy
    · rw [max_eq_right hxy] at h
      exact (pow_le_pow_left₀ (norm_nonneg _) h 2).trans (le_max_right _ _)
    · rw [max_eq_left hxy] at h
      exact (pow_le_pow_left₀ (norm_nonneg _) h 2).trans (le_max_left _ _)

/-- Source: roadmap §1.1.2 ("is continuous"). -/
theorem continuous_symm_toPadicIntSq : Continuous (toPadicIntSq p).symm := by
  refine Metric.continuous_iff.2 fun x ε hε ↦ ⟨ε ^ 2, by positivity, fun y hy ↦ ?_⟩
  rw [dist_eq_norm, norm_def] at hy
  rw [dist_eq_norm, ← map_sub]
  exact lt_of_pow_lt_pow_left₀ 2 hε.le hy

/-- Source: roadmap §1.1.2 ("and unbounded. The Tate hypothesis is exactly what is needed"). -/
theorem not_exists_bound_symm_toPadicIntSq :
    ¬ ∃ C : ℝ, ∀ x : PadicIntSq p, ‖(toPadicIntSq p).symm x‖ ≤ C * ‖x‖ := by
  rintro ⟨C, hC⟩
  have hp1 : (1 : ℝ) < p := Nat.one_lt_cast.2 (Fact.out : p.Prime).one_lt
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C hp1
  have h := hC (toPadicIntSq p ((p : ℤ_[p]) ^ n))
  rw [norm_def, LinearEquiv.symm_apply_apply, PadicInt.norm_p_pow] at h
  set t : ℝ := (p : ℝ) ^ (-(n : ℤ)) with ht
  have htp : 0 < t := zpow_pos (by positivity) _
  have h₁ : t * 1 ≤ t * (C * t) := by
    rw [mul_one]
    calc t ≤ C * t ^ 2 := h
      _ = t * (C * t) := by ring
  have h₂ : C * t < 1 := by
    rw [ht, zpow_neg, zpow_natCast, ← div_eq_mul_inv, div_lt_one (by positivity)]
    exact hn
  linarith [le_of_mul_le_mul_left h₁ htp]

end PadicIntSq

/-! ### A finitely generated ideal of `ℓ^∞(ℕ, ℚ_p)` that is not closed -/

section Linfty

open scoped ENNReal

/-- `ℓ^∞` of ultrametric groups is ultrametric. Source: roadmap §1.4.3 (the counterexample lives in
an ultrametric non-Noetherian Banach–Tate ring); §2.5 ("the dual of `C₀`") will use it too. -/
instance lp.instIsUltrametricDist {ι : Type*} {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
    [∀ i, IsUltrametricDist (E i)] : IsUltrametricDist (lp E ∞) :=
  IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm fun f g ↦
    lp.norm_le_of_forall_le (le_max_of_le_left (norm_nonneg f)) fun i ↦ by
      rw [lp.coeFn_add, Pi.add_apply]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans
        (max_le_max (lp.norm_apply_le_norm ENNReal.top_ne_zero f i)
          (lp.norm_apply_le_norm ENNReal.top_ne_zero g i))

variable (p : ℕ) [Fact p.Prime]

/-- The bounded sequence `(pⁿ)ₙ` in `ℓ^∞(ℕ, ℚ_p)`. -/
noncomputable def padicGeomSeq : lp (fun _ : ℕ ↦ ℚ_[p]) ∞ :=
  ⟨fun n ↦ (p : ℚ_[p]) ^ n, memℓp_infty ⟨1, by
    rintro _ ⟨n, rfl⟩
    dsimp only
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) Padic.norm_p_lt_one.le⟩⟩

@[simp]
theorem padicGeomSeq_apply (n : ℕ) : padicGeomSeq p n = (p : ℚ_[p]) ^ n := rfl

/-- Source: roadmap §1.4.3 ("Not every finitely generated submodule of a Banach module is closed.
Record a counterexample over a non-Noetherian Banach–Tate ring"): the principal ideal generated by
`(pⁿ)ₙ` in `ℓ^∞(ℕ, ℚ_p)` is not closed. -/
theorem not_isClosed_span_padicGeomSeq :
    ¬ IsClosed ((Ideal.span {padicGeomSeq p} : Ideal (lp (fun _ : ℕ ↦ ℚ_[p]) ∞)) :
      Set (lp (fun _ : ℕ ↦ ℚ_[p]) ∞)) := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  have hp1 : (1 : ℝ) < p := Nat.one_lt_cast.2 (Fact.out : p.Prime).one_lt
  have hnorm (k : ℕ) : ‖(p : ℚ_[p]) ^ k‖ = (p : ℝ)⁻¹ ^ k := by rw [norm_pow, Padic.norm_p]
  have hle1 (k : ℕ) : ‖(p : ℚ_[p]) ^ k‖ ≤ 1 := by
    rw [hnorm]
    exact pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hp1.le)
  let c : lp (fun _ : ℕ ↦ ℚ_[p]) ∞ :=
    ⟨fun n ↦ (p : ℚ_[p]) ^ (n / 2), memℓp_infty ⟨1, by rintro _ ⟨n, rfl⟩; exact hle1 _⟩⟩
  have hc (n : ℕ) : c n = (p : ℚ_[p]) ^ (n / 2) := rfl
  -- `c` is in the closure of the ideal: truncate `c / (pⁿ)ₙ`
  have hc_cl : c ∈ closure ((Ideal.span {padicGeomSeq p} : Ideal (lp (fun _ : ℕ ↦ ℚ_[p]) ∞)) :
      Set (lp (fun _ : ℕ ↦ ℚ_[p]) ∞)) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε (inv_lt_one_of_one_lt₀ hp1)
    let b : lp (fun _ : ℕ ↦ ℚ_[p]) ∞ :=
      ⟨fun n ↦ if n < 2 * N then (p : ℚ_[p]) ^ (n / 2) * ((p : ℚ_[p]) ^ n)⁻¹ else 0,
        memℓp_infty ⟨(p : ℝ) ^ (2 * N), by
          rintro _ ⟨n, rfl⟩
          dsimp only
          split_ifs with hn
          · calc ‖(p : ℚ_[p]) ^ (n / 2) * ((p : ℚ_[p]) ^ n)⁻¹‖ ≤ ‖((p : ℚ_[p]) ^ n)⁻¹‖ := by
                  rw [norm_mul]
                  exact mul_le_of_le_one_left (norm_nonneg _) (hle1 _)
              _ = (p : ℝ) ^ n := by rw [norm_inv, hnorm, inv_pow, inv_inv]
              _ ≤ (p : ℝ) ^ (2 * N) := pow_le_pow_right₀ hp1.le hn.le
          · rw [norm_zero]
            positivity⟩⟩
    have hb (n : ℕ) :
        b n = if n < 2 * N then (p : ℚ_[p]) ^ (n / 2) * ((p : ℚ_[p]) ^ n)⁻¹ else 0 := rfl
    refine ⟨b * padicGeomSeq p, Ideal.mem_span_singleton'.2 ⟨b, rfl⟩, ?_⟩
    rw [dist_eq_norm]
    refine lt_of_le_of_lt (lp.norm_le_of_forall_le (by positivity) fun n ↦ ?_) hN
    rw [lp.coeFn_sub, Pi.sub_apply, lp.infty_coeFn_mul, Pi.mul_apply, hc, hb, padicGeomSeq_apply]
    split_ifs with hn
    · rw [inv_mul_cancel_right₀ (pow_ne_zero _ hp0), sub_self, norm_zero]
      positivity
    · rw [zero_mul, sub_zero, hnorm]
      exact pow_le_pow_of_le_one (by positivity) (inv_le_one_of_one_le₀ hp1.le)
        ((Nat.le_div_iff_mul_le two_pos).2 (by omega))
  -- `c` is not in the ideal: the quotient `c / (pⁿ)ₙ` is unbounded
  have hc_not : c ∉ (Ideal.span {padicGeomSeq p} : Ideal (lp (fun _ : ℕ ↦ ℚ_[p]) ∞)) := by
    intro h
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 h
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt ‖b‖ hp1
    have hcoord : b (2 * k) * (p : ℚ_[p]) ^ (2 * k) = (p : ℚ_[p]) ^ k := by
      have h₂ := congrArg (fun f : lp (fun _ : ℕ ↦ ℚ_[p]) ∞ ↦ f (2 * k)) hb
      simp only [lp.infty_coeFn_mul, Pi.mul_apply, padicGeomSeq_apply] at h₂
      rw [h₂, hc, Nat.mul_div_cancel_left k two_pos]
    have hbk : b (2 * k) * (p : ℚ_[p]) ^ k = 1 := by
      apply mul_right_cancel₀ (pow_ne_zero k hp0)
      rw [one_mul, mul_assoc, ← pow_add, ← two_mul]
      exact hcoord
    have hb2k : ‖b (2 * k)‖ = (p : ℝ) ^ k := by
      rw [eq_inv_of_mul_eq_one_left hbk, norm_inv, hnorm, inv_pow, inv_inv]
    have := lp.norm_apply_le_norm ENNReal.top_ne_zero b (2 * k)
    linarith
  intro hS
  apply hc_not
  rw [← SetLike.mem_coe, ← hS.closure_eq]
  exact hc_cl

/-- Source: roadmap §1.4.3 ("a non-Noetherian Banach–Tate ring"): `ℓ^∞(ℕ, ℚ_p)` is not Noetherian,
by `Submodule.isClosed_of_isNoetherianRing`. -/
theorem not_isNoetherianRing_lp_infty : ¬ IsNoetherianRing (lp (fun _ : ℕ ↦ ℚ_[p]) ∞) := by
  intro h
  haveI : IsTate (lp (fun _ : ℕ ↦ ℚ_[p]) ∞) := isTate_of_normedAlgebra ℚ_[p] _
  exact not_isClosed_span_padicGeomSeq p
    (Submodule.isClosed_of_isNoetherianRing (M := lp (fun _ : ℕ ↦ ℚ_[p]) ∞) _)

end Linfty
