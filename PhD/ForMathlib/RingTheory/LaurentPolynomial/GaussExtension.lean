/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.Analysis.Normed.Group.Completion
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Topology.Algebra.UniformRing
import PhD.ForMathlib.RingTheory.LaurentPolynomial.GaussNorm

/-! # The Gauss extension of a normed field

For `r > 0` **outside the divisible closure of the value group** of a complete nontrivially
normed ultrametric field `K`, the completion of the Gauss-normed Laurent algebra
`GaussLaurent K r` is a complete nontrivially normed ultrametric **field**
`GaussExtension K r` — the completed residue field `H(η_r)` of the Gauss point of radius
`r` — in which `r` is realised as the norm of the unit `T`.

Every nonzero element is a unit: approximate by a Laurent polynomial of the same norm,
whose unique dominant monomial (no ties off the divisible closure) makes it a unit times a
`1 + small` factor, and geometric series converge in the completion.

The `T⁰`-coefficient extends to a norm-one `K`-linear retraction of the isometric embedding
`K → GaussExtension K r` — the datum that descends Weierstrass divisions back to `K`
(`weierstrassDivision_descend_of_retraction`).
-/

open UniformSpace

/-- **The Gauss extension** of `K` at radius `r`: the completion of the Laurent-polynomial
algebra under the radius-`r` Gauss norm.  A field whenever `r` lies outside the divisible
closure of the value group of `K`. -/
def GaussExtension (K : Type*) [NormedCommRing K] [IsUltrametricDist K] (r : ℝ)
    [Fact (0 < r)] :=
  Completion (GaussLaurent K r)

namespace GaussExtension

variable {K : Type*} [NormedCommRing K] [IsUltrametricDist K] {r : ℝ} [Fact (0 < r)]

noncomputable instance : NormedAddCommGroup (GaussExtension K r) :=
  inferInstanceAs (NormedAddCommGroup (Completion (GaussLaurent K r)))

noncomputable instance : CommRing (GaussExtension K r) :=
  inferInstanceAs (CommRing (Completion (GaussLaurent K r)))

noncomputable instance : NormedCommRing (GaussExtension K r) :=
  { (inferInstance : NormedAddCommGroup (GaussExtension K r)),
    (inferInstance : CommRing (GaussExtension K r)) with
    norm_mul_le := fun x y ↦ by
      refine Completion.induction_on₂ x y ?_ fun a b ↦ ?_
      · refine isClosed_le ?_ ?_
        · exact (continuous_fst.mul continuous_snd).norm
        · exact continuous_fst.norm.mul continuous_snd.norm
      · show ‖(↑a * ↑b : Completion (GaussLaurent K r))‖
            ≤ ‖(↑a : Completion (GaussLaurent K r))‖ * ‖(↑b : Completion (GaussLaurent K r))‖
        rw [← Completion.coe_mul, Completion.norm_coe, Completion.norm_coe,
          Completion.norm_coe]
        exact norm_mul_le a b }

instance : IsUltrametricDist (GaussExtension K r) := by
  refine IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun x y ↦ ?_
  refine Completion.induction_on₂ x y ?_ fun a b ↦ ?_
  · refine isClosed_le ?_ ?_
    · exact (continuous_fst.add continuous_snd).norm
    · exact continuous_fst.norm.max continuous_snd.norm
  · show ‖(↑a + ↑b : Completion (GaussLaurent K r))‖
        ≤ max ‖(↑a : Completion (GaussLaurent K r))‖ ‖(↑b : Completion (GaussLaurent K r))‖
    rw [← Completion.coe_add, Completion.norm_coe, Completion.norm_coe, Completion.norm_coe]
    exact IsUltrametricDist.norm_add_le_max a b

instance : CompleteSpace (GaussExtension K r) :=
  inferInstanceAs (CompleteSpace (Completion (GaussLaurent K r)))

/-- The canonical isometric embedding of the Laurent algebra into its completion. -/
noncomputable def ofLaurent : GaussLaurent K r →+* GaussExtension K r :=
  Completion.coeRingHom

lemma norm_ofLaurent (p : GaussLaurent K r) : ‖(ofLaurent p : GaussExtension K r)‖ = ‖p‖ :=
  Completion.norm_coe p

lemma denseRange_ofLaurent : DenseRange (ofLaurent (K := K) (r := r)) :=
  Completion.denseRange_coe

noncomputable instance : Algebra K (GaussExtension K r) :=
  ((ofLaurent (K := K) (r := r)).comp (GaussLaurent.C)).toAlgebra

lemma norm_algebraMap (a : K) : ‖algebraMap K (GaussExtension K r) a‖ = ‖a‖ := by
  show ‖ofLaurent (GaussLaurent.C a)‖ = ‖a‖
  rw [norm_ofLaurent, GaussLaurent.norm_C]

instance [NormOneClass K] : NormOneClass (GaussExtension K r) where
  norm_one := by
    rw [show (1 : GaussExtension K r) = ofLaurent 1 from (map_one _).symm, norm_ofLaurent,
      norm_one]

/-- The radius is realised: `T` has norm `r` and is a unit of the Gauss extension. -/
lemma exists_unit_norm [NormOneClass K] :
    ∃ u : (GaussExtension K r)ˣ, ‖(u : GaussExtension K r)‖ = r := by
  obtain ⟨u, hu⟩ := (ofLaurent (K := K) (r := r)).isUnit_map GaussLaurent.isUnit_T
  exact ⟨u, by rw [hu, norm_ofLaurent, GaussLaurent.norm_T]⟩

/-- `r` enters the divisible value group of its own Gauss extension. -/
lemma memDivisibleValueGroup_self [NormOneClass K] :
    MemDivisibleValueGroup (GaussExtension K r) r := by
  obtain ⟨u, hu⟩ := exists_unit_norm (K := K) (r := r)
  exact ⟨1, one_ne_zero, u, by rw [hu, pow_one]⟩

/-- Realised norms of `K` stay realised in the Gauss extension (isometric embedding). -/
lemma memDivisibleValueGroup_of_base {c : ℝ} (h : MemDivisibleValueGroup K c) :
    MemDivisibleValueGroup (GaussExtension K r) c := by
  obtain ⟨n, hn, x, hx⟩ := h
  exact ⟨n, hn, algebraMap K (GaussExtension K r) x, by rw [norm_algebraMap, hx]⟩

section Retraction

variable [CompleteSpace K]

omit [CompleteSpace K] in
private lemma uniformContinuous_coeffZero :
    UniformContinuous (GaussLaurent.coeffZero (K := K) (r := r)) :=
  (AddMonoidHomClass.lipschitz_of_bound (GaussLaurent.coeffZero (K := K) (r := r)) 1
    fun p ↦ by simpa using GaussLaurent.norm_coeffZero_le p).uniformContinuous

private lemma extension_coeffZero_add (x y : Completion (GaussLaurent K r)) :
    Completion.extension (GaussLaurent.coeffZero (K := K) (r := r)) (x + y)
      = Completion.extension (GaussLaurent.coeffZero (K := K) (r := r)) x
        + Completion.extension (GaussLaurent.coeffZero (K := K) (r := r)) y := by
  refine Completion.induction_on₂ x y ?_ fun a b ↦ ?_
  · refine isClosed_eq (Completion.continuous_extension.comp continuous_add) ?_
    exact (Completion.continuous_extension.comp continuous_fst).add
      (Completion.continuous_extension.comp continuous_snd)
  · rw [← Completion.coe_add, Completion.extension_coe uniformContinuous_coeffZero,
      Completion.extension_coe uniformContinuous_coeffZero,
      Completion.extension_coe uniformContinuous_coeffZero, map_add]

private lemma extension_coeffZero_C_mul (c : K) (x : Completion (GaussLaurent K r)) :
    Completion.extension (GaussLaurent.coeffZero (K := K) (r := r))
        (((GaussLaurent.C c : GaussLaurent K r) : Completion (GaussLaurent K r)) * x)
      = c * Completion.extension (GaussLaurent.coeffZero (K := K) (r := r)) x := by
  refine Completion.induction_on x ?_ fun a ↦ ?_
  · refine isClosed_eq
      (Completion.continuous_extension.comp (continuous_const.mul continuous_id)) ?_
    exact continuous_const.mul Completion.continuous_extension
  · rw [← Completion.coe_mul, Completion.extension_coe uniformContinuous_coeffZero,
      Completion.extension_coe uniformContinuous_coeffZero]
    have h := (GaussLaurent.coeffZero (K := K) (r := r)).map_smul c a
    rw [smul_eq_mul] at h
    exact h

/-- **The Gauss retraction**: the continuous `K`-linear extension of the `T⁰`-coefficient
to the completion — a norm-one left inverse of the embedding `K → GaussExtension K r`. -/
noncomputable def retraction : GaussExtension K r →ₗ[K] K where
  toFun := Completion.extension (GaussLaurent.coeffZero (K := K) (r := r))
  map_add' x y := extension_coeffZero_add x y
  map_smul' c x := by
    rw [RingHom.id_apply, smul_eq_mul]
    exact extension_coeffZero_C_mul c x

lemma retraction_algebraMap (a : K) :
    retraction (algebraMap K (GaussExtension K r) a) = a := by
  show Completion.extension _
    (((GaussLaurent.C a : GaussLaurent K r) : Completion (GaussLaurent K r))) = a
  rw [Completion.extension_coe uniformContinuous_coeffZero, GaussLaurent.coeffZero_C]

lemma norm_retraction_le (x : GaussExtension K r) :
    ‖retraction (K := K) (r := r) x‖ ≤ ‖x‖ := by
  show ‖Completion.extension (GaussLaurent.coeffZero (K := K) (r := r))
      (x : Completion (GaussLaurent K r))‖ ≤ ‖(x : Completion (GaussLaurent K r))‖
  refine Completion.induction_on (x : Completion (GaussLaurent K r)) ?_ fun a ↦ ?_
  · exact isClosed_le Completion.continuous_extension.norm continuous_norm
  · rw [Completion.extension_coe uniformContinuous_coeffZero]
    exact (GaussLaurent.norm_coeffZero_le a).trans (le_of_eq (Completion.norm_coe a).symm)

end Retraction

section Field

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {r : ℝ} [Fact (0 < r)] [Fact (¬MemDivisibleValueGroup K r)]

instance : NormMulClass (GaussExtension K r) where
  norm_mul x y := by
    refine Completion.induction_on₂ x y ?_ fun a b ↦ ?_
    · exact isClosed_eq (continuous_fst.mul continuous_snd).norm
        (continuous_fst.norm.mul continuous_snd.norm)
    · show ‖(↑a * ↑b : Completion (GaussLaurent K r))‖
          = ‖(↑a : Completion (GaussLaurent K r))‖ * ‖(↑b : Completion (GaussLaurent K r))‖
      rw [← Completion.coe_mul, Completion.norm_coe, Completion.norm_coe, Completion.norm_coe]
      exact norm_mul a b

omit [CompleteSpace K] [Fact (¬MemDivisibleValueGroup K r)] in
private lemma norm_add_eq_left_of_norm_lt {a b : GaussExtension K r} (hab : ‖b‖ < ‖a‖) :
    ‖a + b‖ = ‖a‖ := by
  refine le_antisymm ((IsUltrametricDist.norm_add_le_max a b).trans (max_le le_rfl hab.le)) ?_
  have h5 : ‖a‖ ≤ max ‖a + b‖ ‖b‖ := by
    calc ‖a‖ = ‖a + b + -b‖ := (congrArg norm (add_neg_cancel_right a b)).symm
      _ ≤ max ‖a + b‖ ‖-b‖ := IsUltrametricDist.norm_add_le_max _ _
      _ = max ‖a + b‖ ‖b‖ := by rw [norm_neg]
  rcases max_cases ‖a + b‖ ‖b‖ with ⟨heq, -⟩ | ⟨heq, -⟩
  · rwa [heq] at h5
  · rw [heq] at h5
    linarith

omit [CompleteSpace K] in
/-- Off the divisible closure, every nonzero element of the Gauss extension is a unit:
approximate by a Laurent polynomial of the same norm, invert its dominant monomial, and sum
the geometric series in the completion. -/
private lemma isUnit_of_ne_zero {x : GaussExtension K r} (hx : x ≠ 0) : IsUnit x := by
  have hxn : (0 : ℝ) < ‖x‖ := norm_pos_iff.mpr hx
  obtain ⟨p, hp⟩ :=
    Metric.denseRange_iff.mp (denseRange_ofLaurent (K := K) (r := r)) x ‖x‖ hxn
  rw [dist_eq_norm] at hp
  have hpn : ‖(ofLaurent p : GaussExtension K r)‖ = ‖x‖ := by
    have h1 : (ofLaurent p : GaussExtension K r) = x + (ofLaurent p - x) := by ring
    rw [h1, norm_add_eq_left_of_norm_lt]
    rwa [show (ofLaurent p : GaussExtension K r) - x = -(x - ofLaurent p) by ring, norm_neg]
  have hpGL : ‖(p : GaussLaurent K r)‖ = ‖x‖ := by rw [← norm_ofLaurent]; exact hpn
  have hp0 : (p : LaurentPolynomial K) ≠ 0 := by
    rintro h0
    rw [show p = (0 : GaussLaurent K r) from h0, norm_zero] at hpGL
    exact hxn.ne hpGL
  obtain ⟨m, hm⟩ := LaurentPolynomial.exists_gaussNorm_eq r hp0
  have ham : (p : LaurentPolynomial K).coeff m ≠ 0 := by
    intro h0
    rw [h0, norm_zero, zero_mul] at hm
    exact hp0 ((LaurentPolynomial.gaussNorm_eq_zero_iff r).mp hm)
  -- the dominant monomial, as a unit of the Laurent algebra
  set q : GaussLaurent K r :=
    (AddMonoidAlgebra.single m ((p : LaurentPolynomial K).coeff m) : LaurentPolynomial K)
    with hqdef
  have hqu : IsUnit q := by
    have h1 : IsUnit (LaurentPolynomial.C ((p : LaurentPolynomial K).coeff m)
        * LaurentPolynomial.T m) :=
      ((LaurentPolynomial.C).isUnit_map (isUnit_iff_ne_zero.mpr ham)).mul
        (LaurentPolynomial.isUnit_T m)
    have h2 : (q : LaurentPolynomial K)
        = LaurentPolynomial.C ((p : LaurentPolynomial K).coeff m) * LaurentPolynomial.T m :=
      LaurentPolynomial.single_eq_C_mul_T _ _
    exact (h2.symm ▸ h1 : IsUnit (q : LaurentPolynomial K))
  have hqn : ‖q‖ = ‖x‖ := by
    rw [GaussLaurent.norm_def, hqdef]
    have hsingle : LaurentPolynomial.gaussNorm r
        (AddMonoidAlgebra.single m ((p : LaurentPolynomial K).coeff m) : LaurentPolynomial K)
        = ‖(p : LaurentPolynomial K).coeff m‖ * r ^ m := by
      rw [LaurentPolynomial.single_eq_C_mul_T _ _,
        LaurentPolynomial.gaussNorm_mul Fact.out, LaurentPolynomial.gaussNorm_C,
        LaurentPolynomial.gaussNorm_T]
    rw [hsingle, ← hm, ← GaussLaurent.norm_def]
    exact hpGL
  -- the tail is strictly smaller
  have hd : ‖(p - q : GaussLaurent K r)‖ < ‖x‖ := by
    rcases eq_or_ne (p - q : GaussLaurent K r) 0 with h0 | h0
    · rw [h0, norm_zero]
      exact hxn
    have h0' : ((p - q : GaussLaurent K r) : LaurentPolynomial K) ≠ 0 := h0
    obtain ⟨k, hk⟩ := LaurentPolynomial.exists_gaussNorm_eq r h0'
    have hqc : ∀ j, (q : LaurentPolynomial K).coeff j
        = Finsupp.single m ((p : LaurentPolynomial K).coeff m) j := fun j ↦ by
      rw [hqdef]
      rfl
    have hcoeffk : ((p - q : GaussLaurent K r) : LaurentPolynomial K).coeff k
        = (p : LaurentPolynomial K).coeff k
          - Finsupp.single m ((p : LaurentPolynomial K).coeff m) k := by
      have h3 := LaurentPolynomial.coeff_sub_apply (p : LaurentPolynomial K)
        (q : LaurentPolynomial K) k
      rw [hqc k] at h3
      exact h3
    have hkm : k ≠ m := by
      rintro rfl
      rw [hcoeffk, Finsupp.single_eq_same, sub_self, norm_zero, zero_mul] at hk
      exact h0 ((LaurentPolynomial.gaussNorm_eq_zero_iff r).mp hk)
    have hck : ((p - q : GaussLaurent K r) : LaurentPolynomial K).coeff k
        = (p : LaurentPolynomial K).coeff k := by
      rw [hcoeffk, Finsupp.single_apply, if_neg (fun h : m = k ↦ hkm h.symm), sub_zero]
    rw [GaussLaurent.norm_def, hk, hck, ← hpGL, GaussLaurent.norm_def]
    rcases eq_or_ne ((p : LaurentPolynomial K).coeff k) 0 with hc0 | hc0
    · rw [hc0, norm_zero, zero_mul, ← GaussLaurent.norm_def, hpGL]
      exact hxn
    · refine lt_of_le_of_ne (LaurentPolynomial.le_gaussNorm r _ k) fun heq ↦ hkm ?_
      exact LaurentPolynomial.gaussTerm_injOn_of_not_memDivisibleValueGroup Fact.out hc0 ham
        (heq.trans hm)
  -- assemble the unit over the completion
  obtain ⟨U, hU⟩ := (ofLaurent (K := K) (r := r)).isUnit_map hqu
  have hUn : ‖(U : GaussExtension K r)‖ = ‖x‖ := by rw [hU, norm_ofLaurent]; exact hqn
  have hUx : ‖(U : GaussExtension K r) - x‖ < ‖x‖ := by
    have hsplit : (U : GaussExtension K r) - x
        = -(ofLaurent (p - q)) + (ofLaurent p - x) := by
      rw [hU, map_sub]
      ring
    rw [hsplit]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ ?_)
    · rw [norm_neg, norm_ofLaurent]
      exact hd
    · rwa [show (ofLaurent p : GaussExtension K r) - x = -(x - ofLaurent p) by ring, norm_neg]
  have hUne : ‖(U : GaussExtension K r)‖ ≠ 0 := by rw [hUn]; exact hxn.ne'
  have hUinv : ‖((U⁻¹ : (GaussExtension K r)ˣ) : GaussExtension K r)‖
      = ‖(U : GaussExtension K r)‖⁻¹ := by
    refine (inv_eq_of_mul_eq_one_right ?_).symm
    rw [← norm_mul, Units.mul_inv, norm_one]
  set t : GaussExtension K r := ((U⁻¹ : (GaussExtension K r)ˣ) : GaussExtension K r)
    * ((U : GaussExtension K r) - x) with htdef
  have ht : ‖t‖ < 1 := by
    rw [htdef, norm_mul, hUinv, hUn]
    calc ‖x‖⁻¹ * ‖(U : GaussExtension K r) - x‖ < ‖x‖⁻¹ * ‖x‖ := by
          exact mul_lt_mul_of_pos_left hUx (by positivity)
      _ = 1 := inv_mul_cancel₀ hxn.ne'
  refine ⟨U * Units.oneSub t ht, ?_⟩
  show (U : GaussExtension K r) * (1 - t) = x
  rw [htdef, mul_sub, mul_one, ← mul_assoc, Units.mul_inv, one_mul]
  ring

noncomputable instance : Field (GaussExtension K r) :=
  IsField.toField
    { exists_pair_ne := ⟨0, 1, fun h ↦ by
        have h1 := congrArg norm h
        rw [norm_zero, norm_one] at h1
        exact zero_ne_one h1⟩
      mul_comm := mul_comm
      mul_inv_cancel := fun {a} ha ↦ (isUnit_of_ne_zero ha).exists_right_inv }

noncomputable instance : NontriviallyNormedField (GaussExtension K r) :=
  { (inferInstance : NormedCommRing (GaussExtension K r)),
    (inferInstance : Field (GaussExtension K r)) with
    norm_mul := norm_mul
    non_trivial := by
      obtain ⟨w, hw⟩ := NormedField.exists_one_lt_norm K
      exact ⟨algebraMap K (GaussExtension K r) w, by rw [norm_algebraMap]; exact hw⟩ }

end Field

end GaussExtension
