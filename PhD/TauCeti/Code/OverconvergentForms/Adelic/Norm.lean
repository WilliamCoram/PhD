/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.TauCeti.Code.OverconvergentForms.Adelic.IntegralAdeles
import PhD.TauCeti.Code.OverconvergentForms.Quaternion.BaseChange
import PhD.TauCeti.Code.OverconvergentForms.Quaternion.Definite
import Mathlib.NumberTheory.NumberField.ProductFormula

/-!
# The adelic reduced norm and the norm class

The finite idele norm `|x|_f = ∏_v ‖x_v‖_v` of a number field, the reduced norm
`nrd : D_f^× →* (𝔸_F^f)^×` of the adelic points of a quaternion algebra `D = (a, b / F)`, and the
*norm class* `|nrd(g)|_f`, a continuous character of `D_f^×` that is trivial on every compact
subgroup, equals `‖det θ_v(·)‖_v` on the image of `ι_v`, and on `D^×` is `|N_{F/ℚ}(nrd γ)|⁻¹` by
the product formula.

[Voi21, 27.6.12]: "we have a natural multiplicative map `‖ ‖ : B̂^× → ℝ_{>0}`,
`α = (α_v)_v ↦ ∏_v |nrd(α_v)|_v`."

## Main definitions

* `NumberField.ideleNorm`: the finite idele norm `(𝔸_F^f)^× →* ℝ`.
* `AdelicAlgebra.adelicNrd`: the reduced norm `D_f^× →* (𝔸_F^f)^×`.
* `AdelicAlgebra.normClass`: the norm class `|nrd(·)|_f : D_f^× →* ℝ`.

## Main results

* `NumberField.finite_mulSupport_norm`, `NumberField.exists_rat_ideleNorm`: the idele norm is a
  finite product with value in `ℚ_{>0}`.
* `NumberField.continuous_ideleNorm`: the idele norm is continuous.
* `NumberField.ideleNorm_algebraMap`: the product formula, `|x|_f = |N_{F/ℚ} x|⁻¹` for `x ∈ F^×`.
* `AdelicAlgebra.adelicNrd_apply`, `AdelicAlgebra.adelicNrd_apply_eq_det`,
  `AdelicAlgebra.det_toMatrix_unitsIncl`: `nrd(g)_v = det θ_v(g)`.
* `AdelicAlgebra.continuous_normClass`, `AdelicAlgebra.normClass_eq_one_of_isCompact`: the norm
  class is a continuous character, trivial on compact subgroups.
* `AdelicAlgebra.normClass_unitAt`, `AdelicAlgebra.normClass_eq_prod_mul_finprod`: the norm class
  on `ι_v(GL₂(F_v))` and its splitting at a finite set of places.
* `AdelicAlgebra.normClass_unitsIncl`, `AdelicAlgebra.normClass_unitsIncl_rat`:
  `|nrd(γ)|_f = |N_{F/ℚ}(nrd γ)|⁻¹`, and `= nrd(γ)⁻¹` for a definite algebra over `ℚ`.

Roadmap: §0.2.4. Tau Ceti home: `TauCeti/NumberTheory/AdelicAlgebra/Norm.lean`.
-/

open scoped TensorProduct Classical Quaternion
open IsDedekindDomain NumberField

noncomputable section

namespace NumberField

variable (F : Type*) [Field F] [NumberField F]

variable {F} in
private theorem norm_le_one_of_mem {v : HeightOneSpectrum (𝓞 F)} {z : v.adicCompletion F}
    (hz : z ∈ v.adicCompletionIntegers F) : ‖z‖ ≤ 1 :=
  (Valued.toNormedField.norm_le_one_iff (Γ₀ := WithZero (Multiplicative ℤ))).mpr hz

variable {F} in
private theorem apply_mul_apply_inv (x : (FiniteAdeleRing (𝓞 F) F)ˣ)
    (v : HeightOneSpectrum (𝓞 F)) :
    (x : FiniteAdeleRing (𝓞 F) F) v *
      ((x⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) v = 1 :=
  congrArg (fun z : FiniteAdeleRing (𝓞 F) F => z v) x.mul_inv

variable {F} in
private theorem units_mul_apply (x y : (FiniteAdeleRing (𝓞 F) F)ˣ)
    (v : HeightOneSpectrum (𝓞 F)) :
    ((x * y : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) v =
      (x : FiniteAdeleRing (𝓞 F) F) v * (y : FiniteAdeleRing (𝓞 F) F) v :=
  rfl

variable {F} in
/- A component of an idele whose value and inverse are integral has norm `1`. -/
private theorem norm_apply_eq_one {x : (FiniteAdeleRing (𝓞 F) F)ˣ} {v : HeightOneSpectrum (𝓞 F)}
    (h₁ : (x : FiniteAdeleRing (𝓞 F) F) v ∈ v.adicCompletionIntegers F)
    (h₂ : ((x⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) v ∈
      v.adicCompletionIntegers F) :
    ‖(x : FiniteAdeleRing (𝓞 F) F) v‖ = 1 := by
  have hmul : ‖(x : FiniteAdeleRing (𝓞 F) F) v‖ *
      ‖((x⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) v‖ = 1 := by
    rw [← norm_mul, apply_mul_apply_inv, norm_one]
  refine le_antisymm (norm_le_one_of_mem h₁) ?_
  calc (1 : ℝ) = ‖(x : FiniteAdeleRing (𝓞 F) F) v‖ *
        ‖((x⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) v‖ := hmul.symm
    _ ≤ ‖(x : FiniteAdeleRing (𝓞 F) F) v‖ * 1 :=
      mul_le_mul_of_nonneg_left (norm_le_one_of_mem h₂) (norm_nonneg _)
    _ = ‖(x : FiniteAdeleRing (𝓞 F) F) v‖ := mul_one _

variable {F} in
private theorem finite_mulSupport_norm' (x : (FiniteAdeleRing (𝓞 F) F)ˣ) :
    (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) ↦
      ‖(x : FiniteAdeleRing (𝓞 F) F) v‖).Finite :=
  (Filter.eventually_cofinite.mp (((x : FiniteAdeleRing (𝓞 F) F).2).and
    (((x⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F).2))).subset
    fun v hv hmem => hv (norm_apply_eq_one (x := x) (v := v) hmem.1 hmem.2)

variable {F} in
private theorem exists_rat_norm_eq {v : HeightOneSpectrum (𝓞 F)} {z : v.adicCompletion F}
    (hz : z ≠ 0) : ∃ q : ℚ, 0 < q ∧ ‖z‖ = q := by
  have hv : Valued.v z ≠ 0 := (Valuation.ne_zero_iff _).mpr hz
  have hq : ‖z‖ = (((Ideal.absNorm v.asIdeal : ℚ) ^ (WithZero.unzero hv).toAdd : ℚ) : ℝ) := by
    rw [FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _ hv]
    push_cast
    rfl
  refine ⟨_, ?_, hq⟩
  have hpos := norm_pos_iff.mpr hz
  rw [hq] at hpos
  exact_mod_cast hpos

/-- **The finite idele norm** `|x|_f = ∏_v ‖x_v‖_v`. -/
def ideleNorm : (FiniteAdeleRing (𝓞 F) F)ˣ →* ℝ where
  toFun x := ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖(x : FiniteAdeleRing (𝓞 F) F) v‖
  map_one' := finprod_eq_one_of_forall_eq_one fun _ => norm_one
  map_mul' x y := by
    rw [← finprod_mul_distrib (finite_mulSupport_norm' x) (finite_mulSupport_norm' y)]
    exact finprod_congr fun v => by rw [units_mul_apply, norm_mul]

variable {F}

theorem ideleNorm_apply (x : (FiniteAdeleRing (𝓞 F) F)ˣ) :
    ideleNorm F x = ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖(x : FiniteAdeleRing (𝓞 F) F) v‖ := rfl

/-- All but finitely many components of an idele have norm `1`. -/
theorem finite_mulSupport_norm (x : (FiniteAdeleRing (𝓞 F) F)ˣ) :
    (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) ↦
      ‖(x : FiniteAdeleRing (𝓞 F) F) v‖).Finite :=
  finite_mulSupport_norm' x

/-- The idele norm is positive. -/
theorem ideleNorm_pos (x : (FiniteAdeleRing (𝓞 F) F)ˣ) : 0 < ideleNorm F x := by
  rw [ideleNorm_apply]
  exact finprod_induction (fun r : ℝ => 0 < r) one_pos (fun _ _ => mul_pos) fun v =>
    norm_pos_iff.mpr (left_ne_zero_of_mul_eq_one (apply_mul_apply_inv x v))

/-- The idele norm is a positive rational number. -/
theorem exists_rat_ideleNorm (x : (FiniteAdeleRing (𝓞 F) F)ˣ) :
    ∃ q : ℚ, 0 < q ∧ ideleNorm F x = (q : ℝ) := by
  choose q hq_pos hq using fun v : HeightOneSpectrum (𝓞 F) =>
    exists_rat_norm_eq (left_ne_zero_of_mul_eq_one (apply_mul_apply_inv x v))
  have hfin : (Function.mulSupport q).Finite :=
    (finite_mulSupport_norm' x).subset fun v hv h1 =>
      hv (by exact_mod_cast (hq v).symm.trans h1)
  refine ⟨∏ᶠ v, q v, finprod_induction (fun r : ℚ => 0 < r) one_pos (fun _ _ => mul_pos) hq_pos,
    ?_⟩
  rw [ideleNorm_apply]
  exact (finprod_congr hq).trans ((Rat.castHom ℝ).toMonoidHom.map_finprod hfin).symm

/-- The idele norm is trivial on `∏_v 𝒪_v^×`. -/
theorem ideleNorm_eq_one_of_forall_norm_eq_one {x : (FiniteAdeleRing (𝓞 F) F)ˣ}
    (hx : ∀ v, ‖(x : FiniteAdeleRing (𝓞 F) F) v‖ = 1) : ideleNorm F x = 1 :=
  (ideleNorm_apply x).trans (finprod_eq_one_of_forall_eq_one hx)

/-- **The idele norm is continuous**: it is trivial on the open subgroup `∏_v 𝒪_v^×`. -/
theorem continuous_ideleNorm : Continuous (ideleNorm F) := by
  refine continuous_of_continuousAt_one (ideleNorm F) ?_
  have hW := Units.isOpen_of_isOpen (FiniteAdeleRing.isOpen_integralAdeles F)
  refine (continuousAt_const : ContinuousAt
    (fun _ : (FiniteAdeleRing (𝓞 F) F)ˣ => (1 : ℝ)) 1).congr ?_
  filter_upwards [hW.mem_nhds ⟨(FiniteAdeleRing.integralAdeles F).one_mem,
    (FiniteAdeleRing.integralAdeles F).one_mem⟩] with u hu
  exact (ideleNorm_eq_one_of_forall_norm_eq_one fun v =>
    norm_apply_eq_one (x := u) (v := v) (hu.1 v) (hu.2 v)).symm

/-- **The product formula, finite part**: `|x|_f = |N_{F/ℚ} x|⁻¹` for `x ∈ F^×`. -/
theorem ideleNorm_algebraMap (x : Fˣ) :
    ideleNorm F (Units.map (algebraMap F (FiniteAdeleRing (𝓞 F) F)).toMonoidHom x) =
      (|(Algebra.norm ℚ (x : F) : ℚ)| : ℝ)⁻¹ := by
  have h := FinitePlace.prod_eq_inv_abs_norm (K := F) x.ne_zero
  rw [← finprod_comp_equiv FinitePlace.equivHeightOneSpectrum.symm] at h
  simp only [FinitePlace.equivHeightOneSpectrum_symm_apply] at h
  rw [ideleNorm_apply]
  refine h.trans ?_
  push_cast
  rfl

end NumberField

namespace AdelicAlgebra

open scoped RightAlgebra
open QuaternionAlgebra

variable (F : Type*) [Field F] [NumberField F] (a b : F)

/-- **The adelic reduced norm** `nrd : D_f^× →* (𝔸_F^f)^×` for `D = (a, b / F)`. -/
def adelicNrd : Dfx F ℍ[F,a,b] →* (FiniteAdeleRing (𝓞 F) F)ˣ :=
  Units.map (nrdBaseChange F a b (FiniteAdeleRing (𝓞 F) F)).toMonoidHom

/-- **The norm class** `|nrd(g)|_f = ∏_v ‖nrd(g)_v‖_v`. -/
def normClass : Dfx F ℍ[F,a,b] →* ℝ := (ideleNorm F).comp (adelicNrd F a b)

variable {F a b}

private theorem normClass_apply (g : Dfx F ℍ[F,a,b]) :
    normClass F a b g = ideleNorm F (adelicNrd F a b g) :=
  rfl

private theorem isUnit_algebraMap_adicCompletion (v : HeightOneSpectrum (𝓞 F)) {c : F}
    (hc : c ≠ 0) : IsUnit (algebraMap F (v.adicCompletion F) c) :=
  ((map_ne_zero (algebraMap F (v.adicCompletion F))).mpr hc).isUnit

private theorem isUnit_two_adicCompletion (v : HeightOneSpectrum (𝓞 F)) :
    IsUnit (2 : v.adicCompletion F) := by
  have h := isUnit_algebraMap_adicCompletion v (by norm_num : (2 : F) ≠ 0)
  rwa [map_ofNat] at h

private theorem finprod_eq_prod_mul_finprod_notMem {α : Type*} {f : α → ℝ}
    (hf : (Function.mulSupport f).Finite) (S : Finset α) :
    ∏ᶠ v, f v = (∏ v ∈ S, f v) * ∏ᶠ (v) (_ : v ∉ S), f v := by
  calc ∏ᶠ v, f v = ∏ᶠ v ∈ ((S : Set α) ∪ (S : Set α)ᶜ), f v := by
        rw [Set.union_compl_self, finprod_mem_univ]
    _ = (∏ᶠ v ∈ (S : Set α), f v) * ∏ᶠ v ∈ (S : Set α)ᶜ, f v :=
        finprod_mem_union' disjoint_compl_right (S.finite_toSet.inter_of_left _)
          (hf.inter_of_right _)
    _ = (∏ v ∈ S, f v) * ∏ᶠ (v) (_ : v ∉ S), f v :=
        congrArg₂ (· * ·) (finprod_mem_coe_finset f S) rfl

/-- The reduced norm of a global element is its reduced norm, diagonally embedded. -/
theorem coe_adelicNrd_unitsIncl (x : (ℍ[F,a,b])ˣ) :
    ((adelicNrd F a b (unitsIncl F ℍ[F,a,b] x) : (FiniteAdeleRing (𝓞 F) F)ˣ) :
      FiniteAdeleRing (𝓞 F) F) = algebraMap F _ (nrd (x : ℍ[F,a,b])) :=
  nrdBaseChange_tmul_one (x : ℍ[F,a,b])

/-- The components of the adelic reduced norm are the local reduced norms. -/
theorem adelicNrd_apply (g : Dfx F ℍ[F,a,b]) (v : HeightOneSpectrum (𝓞 F)) :
    ((adelicNrd F a b g : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) v =
      nrdBaseChange F a b (v.adicCompletion F) (toLocal F ℍ[F,a,b] v (g : Df F ℍ[F,a,b])) :=
  (nrdBaseChange_map (evalAlgHom F v) (g : Df F ℍ[F,a,b])).symm

/-- **`nrd(g)_v = det θ_v(g)`** at a place with a rigidification. -/
theorem adelicNrd_apply_eq_det (ha : a ≠ 0) (hb : b ≠ 0) (v : HeightOneSpectrum (𝓞 F))
    [RigidificationAt F ℍ[F,a,b] v] (g : Dfx F ℍ[F,a,b]) :
    ((adelicNrd F a b g : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) v =
      (toMatrix F ℍ[F,a,b] v g).det := by
  rw [adelicNrd_apply, toMatrix_apply,
    det_eq_nrdBaseChange (RigidificationAt.equiv (F := F) (D := ℍ[F,a,b]) (v := v))
      (isUnit_two_adicCompletion v) (isUnit_algebraMap_adicCompletion v ha)
      (isUnit_algebraMap_adicCompletion v hb)]

/-- **`det θ_v(x) = nrd x`** for a global `x`. -/
theorem det_toMatrix_unitsIncl (ha : a ≠ 0) (hb : b ≠ 0) (v : HeightOneSpectrum (𝓞 F))
    [RigidificationAt F ℍ[F,a,b] v] (x : (ℍ[F,a,b])ˣ) :
    (toMatrix F ℍ[F,a,b] v (unitsIncl F ℍ[F,a,b] x)).det =
      algebraMap F (v.adicCompletion F) (nrd (x : ℍ[F,a,b])) := by
  rw [← adelicNrd_apply_eq_det ha hb v, coe_adelicNrd_unitsIncl]
  rfl

/-- The adelic reduced norm is continuous. -/
theorem continuous_adelicNrd : Continuous (adelicNrd F a b) :=
  Continuous.units_map (nrdBaseChange F a b (FiniteAdeleRing (𝓞 F) F)).toMonoidHom
    continuous_nrdBaseChange

/-- **The norm class is continuous.** -/
theorem continuous_normClass : Continuous (normClass F a b) :=
  (continuous_ideleNorm (F := F)).comp (continuous_adelicNrd (F := F) (a := a) (b := b))

/-- The norm class is positive. -/
theorem normClass_pos (g : Dfx F ℍ[F,a,b]) : 0 < normClass F a b g :=
  ideleNorm_pos (adelicNrd F a b g)

/-- **The norm class is trivial on every compact subgroup**, in particular on `U₀(1)` and on every
compact open subgroup: a compact subgroup of `ℝ_{>0}` is trivial. -/
theorem normClass_eq_one_of_isCompact {U : Subgroup (Dfx F ℍ[F,a,b])}
    (hU : IsCompact (U : Set (Dfx F ℍ[F,a,b]))) {g : Dfx F ℍ[F,a,b]} (hg : g ∈ U) :
    normClass F a b g = 1 := by
  obtain ⟨C, hC⟩ := (hU.image (continuous_normClass (F := F) (a := a) (b := b))).bddAbove
  have key : ∀ h ∈ U, normClass F a b h ≤ 1 := fun h hh => by
    by_contra hlt
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C (not_le.mp hlt)
    have hle : normClass F a b (h ^ n) ≤ C := hC ⟨h ^ n, U.pow_mem hh n, rfl⟩
    rw [map_pow] at hle
    exact absurd hle (not_le.mpr hn)
  have hinv : normClass F a b g⁻¹ * normClass F a b g = 1 := by
    rw [← map_mul, inv_mul_cancel, map_one]
  refine le_antisymm (key g hg) ?_
  calc (1 : ℝ) = normClass F a b g⁻¹ * normClass F a b g := hinv.symm
    _ ≤ 1 * normClass F a b g :=
      mul_le_mul_of_nonneg_right (key g⁻¹ (U.inv_mem hg)) (normClass_pos g).le
    _ = normClass F a b g := one_mul _

/-- **`nrd ∘ ι_v = det`**, in the norm class. -/
theorem normClass_unitAt (ha : a ≠ 0) (hb : b ≠ 0) (v : HeightOneSpectrum (𝓞 F))
    [RigidificationAt F ℍ[F,a,b] v] (m : GL (Fin 2) (v.adicCompletion F)) :
    normClass F a b (unitAt F ℍ[F,a,b] v m) =
      ‖(m : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)).det‖ := by
  have hne : ∀ w, w ≠ v → ‖((adelicNrd F a b (unitAt F ℍ[F,a,b] v m) :
      (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) w‖ = 1 := by
    intro w hw
    have h1 : toLocal F ℍ[F,a,b] w ((unitAt F ℍ[F,a,b] v m : Dfx F ℍ[F,a,b]) :
        Df F ℍ[F,a,b]) = 1 :=
      congrArg Units.val (toLocalUnits_localIncl_of_ne v hw (Units.map
        (RigidificationAt.equiv (F := F) (D := ℍ[F,a,b]) (v := v)).symm.toAlgHom.toMonoidHom m))
    rw [adelicNrd_apply, h1, map_one, norm_one]
  rw [normClass_apply, ideleNorm_apply, finprod_eq_single _ v hne,
    adelicNrd_apply_eq_det ha hb v, ← coe_toGL, toGL_unitAt]

/-- **The norm class splits** into the places of a finite set `S` and the places away from `S`;
with `adelicNrd_apply_eq_det` the first factor is `∏_{v ∈ S} ‖det θ_v(g)‖_v`. -/
theorem normClass_eq_prod_mul_finprod (S : Finset (HeightOneSpectrum (𝓞 F)))
    (g : Dfx F ℍ[F,a,b]) :
    normClass F a b g =
      (∏ v ∈ S, ‖((adelicNrd F a b g : (FiniteAdeleRing (𝓞 F) F)ˣ) :
        FiniteAdeleRing (𝓞 F) F) v‖) *
      ∏ᶠ (v : HeightOneSpectrum (𝓞 F)) (_ : v ∉ S),
        ‖((adelicNrd F a b g : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) v‖ :=
  finprod_eq_prod_mul_finprod_notMem (finite_mulSupport_norm (adelicNrd F a b g)) S

/-- **The norm class of a global element**: `|nrd(γ)|_f = |N_{F/ℚ}(nrd γ)|⁻¹`. -/
theorem normClass_unitsIncl (x : (ℍ[F,a,b])ˣ) :
    normClass F a b (unitsIncl F ℍ[F,a,b] x) =
      (|(Algebra.norm ℚ (nrd (x : ℍ[F,a,b])) : ℚ)| : ℝ)⁻¹ := by
  have h : adelicNrd F a b (unitsIncl F ℍ[F,a,b] x) =
      Units.map (algebraMap F (FiniteAdeleRing (𝓞 F) F)).toMonoidHom
        (Units.map (nrd : ℍ[F,a,b] →*₀ F).toMonoidHom x) :=
    Units.ext (coe_adelicNrd_unitsIncl x)
  rw [normClass_apply, h]
  exact ideleNorm_algebraMap _

/-- For `F = ℚ` and `D` definite, `|nrd(γ)|_f = nrd(γ)⁻¹`. -/
theorem normClass_unitsIncl_rat {a b : ℚ} (h : IsTotallyDefinite a b) (x : (ℍ[ℚ,a,b])ˣ) :
    normClass ℚ a b (unitsIncl ℚ ℍ[ℚ,a,b] x) = ((nrd (x : ℍ[ℚ,a,b]) : ℚ) : ℝ)⁻¹ := by
  have hpos : 0 < nrd (x : ℍ[ℚ,a,b]) :=
    Rat.cast_pos.mp (h.nrd_pos (Rat.castHom ℝ) x.ne_zero)
  -- the `Algebra ℚ ℚ` instance comes from the general-`F` statement, not `Algebra.id ℚ`
  have hnorm : ∀ (inst : Algebra ℚ ℚ) (q : ℚ), @Algebra.norm ℚ ℚ _ _ inst q = q := by
    intro inst q
    rw [Subsingleton.elim inst (Algebra.id ℚ), Algebra.norm_self, MonoidHom.id_apply]
  rw [normClass_unitsIncl, hnorm, abs_of_pos (Rat.cast_pos.mpr hpos : (0 : ℝ) < _)]

end AdelicAlgebra
