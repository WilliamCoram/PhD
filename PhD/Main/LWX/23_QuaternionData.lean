/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.Main.LWX.«22_AtkinLehnerFamily»
import PhD.Main.LWX.«12_QuaternionicH»
import PhD.Main.QMF.«04_UpiElement»

/-!
# The Atkin–Lehner data of a definite quaternion algebra over `ℚ`

[LWX, §2.4] fixes "a definite quaternion algebra `D` over `ℚ` which splits at `p`, … an isomorphism
`D ⊗ ℚ_p ≃ M₂(ℚ_p)` … the tame level structure `K^p` … an open compact subgroup of
`(D ⊗ 𝔸_f^{(p)})^×`" (`lwx.txt:665–669`), and [LWX, §2.11] chooses "elements `γ_0, …, γ_{t−1}` …
so that its `p`-component `γ_{i,p}` is just `1`" (`lwx.txt:843–847`).  This file instantiates the
abstract Atkin–Lehner data of `18_AtkinLehnerMap.lean` / `22_AtkinLehnerFamily.lean` for
`G = (D ⊗ 𝔸_f)ˣ`, `Γ = D^×`, `θ = thetaInt` (`08_Quaternionic.lean`), granted an **arithmetic
input** `QuaternionInput`:

* the tame level `Kt` (adelic units of trivial `p`-component) containing a power of the tame
  scalar `p^{(p)}` — true for every open tame level, since the tame scalars form a compact group;
* the **norm class** `q : (D ⊗ 𝔸_f)ˣ →* ℚˣ`, `q(g) = ∏_ℓ ℓ^{v_ℓ(nrd g)}`, through the four
  compatibilities a reduced norm provides (on `D^×` it is `det θ_p`; `‖det θ_p(g)‖ = ‖q(g)‖`;
  on `p`-local elements it is `p^{v_p(det)}`; on the tame level it is `1`) — mathlib has no reduced
  norm on a central simple algebra, so `q` is the interface;
* **normalised, neat class representatives** `c_i` of trivial `p`-component and unit norm class —
  their existence is Hasse–Schilling–Maass plus weak approximation at `p` (Voight, *Quaternion
  Algebras*, Thm 14.7.4, §28.5), out of scope, so they are carried exactly as `c`, `hc`, `hstab`
  already are in `12_QuaternionicH.lean`.

Everything else is proved: the section `ιp` (`unitAt`), the commutation of `p`-local elements
with the prime-to-`p` part, the level `U = Kt·Iw_p` with `ιp(Iw_p) ⊆ U` and the `w`-normaliser
property at every level `h`, `central_pow`, the Hecke characters `χ = ψ_neb ∘ (det θ_p / q)` at
every classical weight and conductor, the coset decomposition `UηU = ∐ U v_c` from the local
Iwahori decomposition, the factorisation data `(idx, d, u)`, the shape certificate, and — the
canonical fix of the determinant certificate — `det(u_{i,t} v_t) = p` from the normalisation.
-/

open IsDedekindDomain NumberField Filter Topology TateFredholm QMF QMF.Weight
  AbstractHeckeOperatorSlash RightSlashAction
open scoped TateFredholm Pointwise TensorProduct

noncomputable section

section GenericTop

open IsDedekindDomain NumberField QMF
open scoped TensorProduct

variable {F : Type*} [Field F] [NumberField F] {A : Type*} [Ring A] [Algebra F A]
  (v : HeightOneSpectrum (RingOfIntegers F))

/-- `singleₗ a · b = singleₗ (a · b_v)`. -/
theorem QMF.singleₗ_mul (a : v.adicCompletion F) (b : FiniteAdeleRing (RingOfIntegers F) F) :
    singleₗ F v a * b = singleₗ F v (a * b v) := by
  have hmul : ∀ (x y : FiniteAdeleRing (RingOfIntegers F) F) w, (x * y) w = x w * y w :=
    fun _ _ _ => rfl
  refine FiniteAdeleRing.ext F fun w => ?_
  rcases eq_or_ne w v with rfl | hw
  · rw [hmul, singleₗ_apply_same, singleₗ_apply_same]
  · rw [hmul, singleₗ_apply_ne F v a hw, singleₗ_apply_ne F v _ hw, zero_mul]

/-- `b · singleₗ a = singleₗ (b_v · a)`. -/
theorem QMF.mul_singleₗ (a : v.adicCompletion F) (b : FiniteAdeleRing (RingOfIntegers F) F) :
    b * singleₗ F v a = singleₗ F v (b v * a) := by
  have hmul : ∀ (x y : FiniteAdeleRing (RingOfIntegers F) F) w, (x * y) w = x w * y w :=
    fun _ _ _ => rfl
  refine FiniteAdeleRing.ext F fun w => ?_
  rcases eq_or_ne w v with rfl | hw
  · rw [hmul, singleₗ_apply_same, singleₗ_apply_same]
  · rw [hmul, singleₗ_apply_ne F v a hw, singleₗ_apply_ne F v _ hw, mul_zero]

/-- `ι_v(x) · y = ι_v(x) · ι_v(y_v)`. -/
theorem QMF.iotaV_mul_eq_iotaV_mul_toLocal (x : A ⊗[F] v.adicCompletion F)
    (y : A ⊗[F] FiniteAdeleRing (RingOfIntegers F) F) :
    iotaV F A v x * y = iotaV F A v x * iotaV F A v (toLocal F A v y) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero, zero_mul]
  | tmul d a =>
    induction y using TensorProduct.induction_on with
    | zero => simp only [map_zero, mul_zero]
    | tmul e b =>
      rw [toLocal_tmul, evalAlgHom_apply, iotaV_tmul, iotaV_tmul,
        Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
        singleₗ_mul_singleₗ, QMF.singleₗ_mul]
    | add y₁ y₂ h₁ h₂ => simp only [map_add, mul_add, h₁, h₂]
  | add x₁ x₂ h₁ h₂ => simp only [map_add, add_mul, h₁, h₂]

/-- `y · ι_v(x) = ι_v(y_v) · ι_v(x)`. -/
theorem QMF.mul_iotaV_eq_iotaV_toLocal_mul (x : A ⊗[F] v.adicCompletion F)
    (y : A ⊗[F] FiniteAdeleRing (RingOfIntegers F) F) :
    y * iotaV F A v x = iotaV F A v (toLocal F A v y) * iotaV F A v x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero, mul_zero]
  | tmul d a =>
    induction y using TensorProduct.induction_on with
    | zero => simp only [map_zero, zero_mul]
    | tmul e b =>
      rw [toLocal_tmul, evalAlgHom_apply, iotaV_tmul, iotaV_tmul,
        Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
        singleₗ_mul_singleₗ, QMF.mul_singleₗ]
    | add y₁ y₂ h₁ h₂ => simp only [map_add, add_mul, h₁, h₂]
  | add x₁ x₂ h₁ h₂ => simp only [map_add, mul_add, h₁, h₂]

/-- A central local element stays central after the single-place inclusion. -/
theorem QMF.iotaV_mul_comm_of_forall_comm (z : A ⊗[F] v.adicCompletion F)
    (hz : ∀ w, z * w = w * z) (y : A ⊗[F] FiniteAdeleRing (RingOfIntegers F) F) :
    iotaV F A v z * y = y * iotaV F A v z := by
  rw [QMF.iotaV_mul_eq_iotaV_mul_toLocal v z y, QMF.mul_iotaV_eq_iotaV_toLocal_mul v z y,
    iotaV_mul, iotaV_mul, hz]

/-- Global scalars are central in `(A ⊗ 𝔸_f)ˣ`. -/
theorem QMF.unitsIncl_algebraMap_comm (c : F) (hc : c ≠ 0) (x : Dfx F A) :
    unitsIncl F A (Units.map (algebraMap F A).toMonoidHom (Units.mk0 c hc)) * x
      = x * unitsIncl F A (Units.map (algebraMap F A).toMonoidHom (Units.mk0 c hc)) := by
  refine Units.ext ?_
  show (algebraMap F A c ⊗ₜ[F] (1 : FiniteAdeleRing (RingOfIntegers F) F))
      * (x : A ⊗[F] FiniteAdeleRing (RingOfIntegers F) F)
    = (x : A ⊗[F] FiniteAdeleRing (RingOfIntegers F) F)
      * (algebraMap F A c ⊗ₜ[F] (1 : FiniteAdeleRing (RingOfIntegers F) F))
  rw [← Algebra.TensorProduct.algebraMap_apply]
  exact Algebra.commutes c _

variable [RigidificationAt F A v]

/-- `unitAt 1 = 1`. -/
theorem QMF.unitAt_one : unitAt F A v 1 = 1 := by
  refine Units.ext ?_
  show 1 + iotaV F A v ((RigidificationAt.equiv (F := F) (D := A) (v := v)).symm
    ((1 : (Matrix (Fin 2) (Fin 2) (v.adicCompletion F))ˣ) :
      Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) - 1) = 1
  rw [Units.val_one, map_one, sub_self, map_zero, add_zero]

/-- `unitAt` is multiplicative. -/
theorem QMF.unitAt_mul (m m' : (Matrix (Fin 2) (Fin 2) (v.adicCompletion F))ˣ) :
    unitAt F A v (m * m') = unitAt F A v m * unitAt F A v m' := by
  refine Units.ext ?_
  show 1 + iotaV F A v ((RigidificationAt.equiv (F := F) (D := A) (v := v)).symm
      ((m * m' : (Matrix (Fin 2) (Fin 2) (v.adicCompletion F))ˣ) :
        Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) - 1)
    = (1 + iotaV F A v ((RigidificationAt.equiv (F := F) (D := A) (v := v)).symm
        (m : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) - 1))
      * (1 + iotaV F A v ((RigidificationAt.equiv (F := F) (D := A) (v := v)).symm
        (m' : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) - 1))
  have expand : ∀ a b : A ⊗[F] FiniteAdeleRing (RingOfIntegers F) F,
      (1 + a) * (1 + b) = 1 + (a + b + a * b) := fun a b => by noncomm_ring
  have collapse : ∀ a b : A ⊗[F] v.adicCompletion F,
      a - 1 + (b - 1) + (a - 1) * (b - 1) = a * b - 1 := fun a b => by noncomm_ring
  rw [expand, iotaV_mul, ← map_add, ← map_add, collapse, ← map_mul, ← Units.val_mul]

/-- A unit with trivial `v`-component has `toLocal` equal to `1`. -/
theorem QMF.toLocal_eq_one_of_toMatrix_eq_one {y : Dfx F A} (hy : toMatrix F A v y = 1) :
    toLocal F A v (y : A ⊗[F] FiniteAdeleRing (RingOfIntegers F) F) = 1 := by
  rw [toMatrix_apply] at hy
  have h := congrArg (RigidificationAt.equiv (F := F) (D := A) (v := v)).symm hy
  rwa [AlgEquiv.symm_apply_apply, map_one] at h

/-- Single-place units commute with units of trivial `v`-component. -/
theorem QMF.unitAt_comm_of_toLocal_eq_one (m : (Matrix (Fin 2) (Fin 2) (v.adicCompletion F))ˣ)
    {y : Dfx F A} (hy : toLocal F A v (y : A ⊗[F] FiniteAdeleRing (RingOfIntegers F) F) = 1) :
    unitAt F A v m * y = y * unitAt F A v m := by
  refine Units.ext ?_
  obtain ⟨x, hx⟩ : ∃ x : A ⊗[F] v.adicCompletion F,
      x = (RigidificationAt.equiv (F := F) (D := A) (v := v)).symm
        (m : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) - 1 := ⟨_, rfl⟩
  obtain ⟨y', hy'⟩ : ∃ y' : A ⊗[F] FiniteAdeleRing (RingOfIntegers F) F,
      y' = (y : A ⊗[F] FiniteAdeleRing (RingOfIntegers F) F) - 1 := ⟨_, rfl⟩
  have hy0 : toLocal F A v y' = 0 := by rw [hy', map_sub, hy, map_one, sub_self]
  have h1 : iotaV F A v x * y' = 0 := by
    rw [QMF.iotaV_mul_eq_iotaV_mul_toLocal v x y', hy0, map_zero, mul_zero]
  have h2 : y' * iotaV F A v x = 0 := by
    rw [QMF.mul_iotaV_eq_iotaV_toLocal_mul v x y', hy0, map_zero, zero_mul]
  have hyy : (y : A ⊗[F] FiniteAdeleRing (RingOfIntegers F) F) = 1 + y' := by
    rw [hy']; abel
  show (1 + iotaV F A v ((RigidificationAt.equiv (F := F) (D := A) (v := v)).symm
      (m : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) - 1))
      * (y : A ⊗[F] FiniteAdeleRing (RingOfIntegers F) F)
    = (y : A ⊗[F] FiniteAdeleRing (RingOfIntegers F) F)
      * (1 + iotaV F A v ((RigidificationAt.equiv (F := F) (D := A) (v := v)).symm
        (m : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) - 1))
  rw [← hx, hyy]
  calc (1 + iotaV F A v x) * (1 + y') = 1 + iotaV F A v x + y' + iotaV F A v x * y' := by
        noncomm_ring
    _ = 1 + iotaV F A v x + y' + y' * iotaV F A v x := by rw [h1, h2]
    _ = (1 + y') * (1 + iotaV F A v x) := by noncomm_ring

/-- A single-place unit at a central matrix is central. -/
theorem QMF.unitAt_comm_of_forall_comm (m : (Matrix (Fin 2) (Fin 2) (v.adicCompletion F))ˣ)
    (hm : ∀ M : Matrix (Fin 2) (Fin 2) (v.adicCompletion F),
      (m : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) * M = M * m)
    (y : Dfx F A) : unitAt F A v m * y = y * unitAt F A v m := by
  refine Units.ext ?_
  obtain ⟨E, hE⟩ : ∃ E : (A ⊗[F] v.adicCompletion F) ≃ₐ[F]
      Matrix (Fin 2) (Fin 2) (v.adicCompletion F),
      E = RigidificationAt.equiv (F := F) (D := A) (v := v) := ⟨_, rfl⟩
  have hz : ∀ w, (E.symm (m : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) - 1) * w
      = w * (E.symm (m : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) - 1) := fun w => by
    have h := congrArg E.symm (hm (E w))
    rw [map_mul, map_mul, AlgEquiv.symm_apply_apply] at h
    rw [sub_mul, mul_sub, h, one_mul, mul_one]
  show (1 + iotaV F A v ((RigidificationAt.equiv (F := F) (D := A) (v := v)).symm
      (m : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) - 1))
      * (y : A ⊗[F] FiniteAdeleRing (RingOfIntegers F) F)
    = (y : A ⊗[F] FiniteAdeleRing (RingOfIntegers F) F)
      * (1 + iotaV F A v ((RigidificationAt.equiv (F := F) (D := A) (v := v)).symm
        (m : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) - 1))
  rw [← hE, add_mul, mul_add, one_mul, mul_one, QMF.iotaV_mul_comm_of_forall_comm v _ hz]

/-- The `v`-component of a global scalar is the scalar matrix. -/
theorem QMF.toMatrix_unitsIncl_algebraMap (c : F) (hc : c ≠ 0) :
    toMatrix F A v (unitsIncl F A (Units.map (algebraMap F A).toMonoidHom (Units.mk0 c hc)))
      = algebraMap F (v.adicCompletion F) c •
        (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) := by
  rw [toMatrix_apply]
  show RigidificationAt.equiv (F := F) (D := A) (v := v)
      (toLocal F A v (algebraMap F A c ⊗ₜ[F] (1 : FiniteAdeleRing (RingOfIntegers F) F))) = _
  rw [← Algebra.TensorProduct.algebraMap_apply, AlgHom.commutes, AlgEquiv.commutes,
    Algebra.algebraMap_eq_smul_one, algebraMap_smul]

end GenericTop

namespace LWX

variable (p : ℕ) [hp : Fact p.Prime]
variable (D : Type*) [Ring D] [Algebra ℚ D] [RigidificationAt ℚ D (padicPlace p)]

/-! ### The section of the `p`-component -/

/-- The determinant of a `p`-component is nonzero (it is the coercion of a unit). -/
theorem det_thetaInt_ne_zero (g : Dfx ℚ D) : (thetaInt p D g).det ≠ 0 := by
  have h := congrArg Matrix.det (map_mul (thetaInt p D) g g⁻¹)
  rw [mul_inv_cancel, map_one, Matrix.det_one, Matrix.det_mul] at h
  exact left_ne_zero_of_mul_eq_one h.symm

/-- The `p`-component map into `GL₂(ℚ_p)`. -/
def thetaIntGL : Dfx ℚ D →* GL (Fin 2) ℚ_[p] where
  toFun g := Matrix.GeneralLinearGroup.mkOfDetNeZero (thetaInt p D g) (det_thetaInt_ne_zero p D g)
  map_one' := Units.ext (map_one (thetaInt p D))
  map_mul' g g' := Units.ext (map_mul (thetaInt p D) g g')

theorem coe_thetaIntGL (g : Dfx ℚ D) :
    (thetaIntGL p D g : Matrix (Fin 2) (Fin 2) ℚ_[p]) = thetaInt p D g :=
  rfl

/-- **The section** `ιp : GL₂(ℚ_p) →* (D ⊗ 𝔸_f)ˣ`: the single-place unit `unitAt` at `p`, read
through the comparison `ℚ_p ≃ K_p`. -/
def ιpD : GL (Fin 2) ℚ_[p] →* Dfx ℚ D where
  toFun g := unitAt ℚ D (padicPlace p) (Matrix.GeneralLinearGroup.map (padicComparison p) g)
  map_one' := by
    show unitAt ℚ D (padicPlace p) (Matrix.GeneralLinearGroup.map (padicComparison p) 1) = 1
    rw [map_one]
    exact QMF.unitAt_one (padicPlace p)
  map_mul' g g' := by
    show unitAt ℚ D (padicPlace p) (Matrix.GeneralLinearGroup.map (padicComparison p) (g * g'))
      = unitAt ℚ D (padicPlace p) (Matrix.GeneralLinearGroup.map (padicComparison p) g)
        * unitAt ℚ D (padicPlace p) (Matrix.GeneralLinearGroup.map (padicComparison p) g')
    rw [map_mul]
    exact QMF.unitAt_mul (padicPlace p) _ _

theorem ιpD_apply (g : GL (Fin 2) ℚ_[p]) :
    ιpD p D g = unitAt ℚ D (padicPlace p) (Matrix.GeneralLinearGroup.map (padicComparison p) g) :=
  rfl

/-- `θ ∘ ιp = id` (`toMatrix_unitAt`). -/
theorem thetaInt_ιpD (g : GL (Fin 2) ℚ_[p]) :
    thetaInt p D (ιpD p D g) = (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) := by
  show RingHom.mapMatrix (padicComparisonSymm p) (toMatrix ℚ D (padicPlace p) (ιpD p D g)) = _
  rw [ιpD_apply, QMF.toMatrix_unitAt]
  ext i j
  exact RingHom.congr_fun (padicComparisonSymm_comp p) ((g : Matrix (Fin 2) (Fin 2) ℚ_[p]) i j)

theorem thetaIntGL_ιpD (g : GL (Fin 2) ℚ_[p]) : thetaIntGL p D (ιpD p D g) = g :=
  Units.ext (thetaInt_ιpD p D g)

theorem ιpD_injective : Function.Injective (ιpD p D) :=
  Function.LeftInverse.injective (thetaIntGL_ιpD p D)

/-! ### The prime-to-`p` part -/

end LWX

section Generic

open IsDedekindDomain NumberField QMF
open scoped TensorProduct

variable {F : Type*} [Field F] [NumberField F] {A : Type*} [Ring A] [Algebra F A]
  (v : HeightOneSpectrum (RingOfIntegers F))

/-- Elements supported away from `v` annihilate the single-place inclusion at `v`
(`singleₗ_mul_singleₗ`, `toLocal_tmul`; a lemma about the fork's API, to move to
`PhD/Main/QMF/04_UpiElement.lean` at cleanup). -/
theorem QMF.iotaV_mul_eq_zero_of_toLocal_eq_zero (x : A ⊗[F] v.adicCompletion F)
    {y : A ⊗[F] FiniteAdeleRing (RingOfIntegers F) F} (hy : toLocal F A v y = 0) :
    iotaV F A v x * y = 0 ∧ y * iotaV F A v x = 0 :=
  ⟨by rw [QMF.iotaV_mul_eq_iotaV_mul_toLocal v x y, hy, map_zero, mul_zero],
    by rw [QMF.mul_iotaV_eq_iotaV_toLocal_mul v x y, hy, map_zero, zero_mul]⟩

end Generic

namespace LWX

variable (p : ℕ) [hp : Fact p.Prime]
variable (D : Type*) [Ring D] [Algebra ℚ D] [RigidificationAt ℚ D (padicPlace p)]

/-- **`p`-local elements commute with elements of trivial `p`-component.** -/
theorem ιpD_comm_of_thetaInt_eq_one (g : GL (Fin 2) ℚ_[p]) {y : Dfx ℚ D}
    (hy : thetaInt p D y = 1) : ιpD p D g * y = y * ιpD p D g := by
  have hM : toMatrix ℚ D (padicPlace p) y = 1 := by
    have h1 : RingHom.mapMatrix (padicComparison p) (thetaInt p D y) = 1 := by rw [hy, map_one]
    rw [← h1]
    refine Matrix.ext fun i j => ?_
    exact (RingHom.congr_fun (padicComparison_comp p) (toMatrix ℚ D (padicPlace p) y i j)).symm
  rw [ιpD_apply]
  exact QMF.unitAt_comm_of_toLocal_eq_one (padicPlace p) _
    (QMF.toLocal_eq_one_of_toMatrix_eq_one (padicPlace p) hM)

/-- The local central element `p·1` is central in `(D ⊗ 𝔸_f)ˣ`. -/
theorem ιpD_pGL_comm (x : Dfx ℚ D) : ιpD p D (pGL p) * x = x * ιpD p D (pGL p) := by
  rw [ιpD_apply]
  refine QMF.unitAt_comm_of_forall_comm (padicPlace p) _ (fun M => ?_) x
  have hscal : ((Matrix.GeneralLinearGroup.map (padicComparison p) (pGL p) : GL (Fin 2) (Kp p)) :
      Matrix (Fin 2) (Fin 2) (Kp p))
      = padicComparison p (p : ℚ_[p]) • (1 : Matrix (Fin 2) (Fin 2) (Kp p)) := by
    refine Matrix.ext fun i j => ?_
    change padicComparison p (((p : ℚ_[p]) • (1 : Matrix (Fin 2) (Fin 2) ℚ_[p])) i j) = _
    fin_cases i <;> fin_cases j <;> simp
  rw [hscal, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]

/-- **The prime-to-`p` subgroup**: adelic units with trivial `p`-component. -/
def tameSubgroup : Subgroup (Dfx ℚ D) where
  carrier := {g | thetaInt p D g = 1}
  mul_mem' := fun {a b} ha hb => by
    change thetaInt p D a = 1 at ha
    change thetaInt p D b = 1 at hb
    change thetaInt p D (a * b) = 1
    rw [map_mul, ha, hb, mul_one]
  one_mem' := map_one (thetaInt p D)
  inv_mem' := fun {a} ha => by
    change thetaInt p D a = 1 at ha
    change thetaInt p D a⁻¹ = 1
    have h := map_mul (thetaInt p D) a a⁻¹
    rw [mul_inv_cancel, map_one, ha, one_mul] at h
    exact h.symm

theorem mem_tameSubgroup_iff {g : Dfx ℚ D} : g ∈ tameSubgroup p D ↔ thetaInt p D g = 1 :=
  Iff.rfl

/-- **The tame part** `g·ιp(θ g)⁻¹` of an adelic unit. -/
def tamePart (g : Dfx ℚ D) : Dfx ℚ D := g * (ιpD p D (thetaIntGL p D g))⁻¹

theorem tamePart_mem_tameSubgroup (g : Dfx ℚ D) : tamePart p D g ∈ tameSubgroup p D := by
  have h : thetaIntGL p D (tamePart p D g) = 1 := by
    rw [tamePart, map_mul, map_inv, thetaIntGL_ιpD, mul_inv_cancel]
  exact congrArg Units.val h

theorem thetaInt_tamePart (g : Dfx ℚ D) : thetaInt p D (tamePart p D g) = 1 :=
  tamePart_mem_tameSubgroup p D g

/-- `g = ιp(θ g) · tamePart g`. -/
theorem eq_ιpD_mul_tamePart (g : Dfx ℚ D) :
    g = ιpD p D (thetaIntGL p D g) * tamePart p D g := by
  rw [ιpD_comm_of_thetaInt_eq_one p D _ (thetaInt_tamePart p D g), tamePart, inv_mul_cancel_right]

theorem tamePart_mul (g g' : Dfx ℚ D) :
    tamePart p D (g * g') = tamePart p D g * tamePart p D g' := by
  have hc := ιpD_comm_of_thetaInt_eq_one p D (thetaIntGL p D g)⁻¹ (thetaInt_tamePart p D g')
  rw [map_inv] at hc
  simp only [tamePart] at hc ⊢
  rw [map_mul, map_mul, mul_inv_rev]
  calc g * g' * ((ιpD p D (thetaIntGL p D g'))⁻¹ * (ιpD p D (thetaIntGL p D g))⁻¹)
      = g * ((g' * (ιpD p D (thetaIntGL p D g'))⁻¹) * (ιpD p D (thetaIntGL p D g))⁻¹) := by
        group
    _ = g * ((ιpD p D (thetaIntGL p D g))⁻¹ * (g' * (ιpD p D (thetaIntGL p D g'))⁻¹)) := by
        rw [hc]
    _ = _ := by group

theorem tamePart_one : tamePart p D 1 = 1 := by
  simp only [tamePart]
  rw [map_one, map_one, inv_one, mul_one]

theorem tamePart_inv (g : Dfx ℚ D) : tamePart p D g⁻¹ = (tamePart p D g)⁻¹ := by
  have h := tamePart_mul p D g⁻¹ g
  rw [inv_mul_cancel, tamePart_one] at h
  exact eq_inv_of_mul_eq_one_left h.symm

theorem tamePart_ιpD (g : GL (Fin 2) ℚ_[p]) : tamePart p D (ιpD p D g) = 1 := by
  simp only [tamePart]
  rw [thetaIntGL_ιpD, mul_inv_cancel]

theorem tamePart_eq_self_of_thetaInt_eq_one {g : Dfx ℚ D} (hg : thetaInt p D g = 1) :
    tamePart p D g = g := by
  have h1 : thetaIntGL p D g = 1 := Units.ext hg
  simp only [tamePart]
  rw [h1, map_one, inv_one, mul_one]

/-- Conjugating by a `p`-local element does not change the tame part. -/
theorem tamePart_conj_ιpD (g : GL (Fin 2) ℚ_[p]) (x : Dfx ℚ D) :
    tamePart p D (ιpD p D g * x * (ιpD p D g)⁻¹) = tamePart p D x := by
  rw [tamePart_mul, tamePart_mul, tamePart_inv, tamePart_ιpD, one_mul, inv_one, mul_one]

/-! ### The level `Kt · Iw_p` -/

variable (Kt : Subgroup (Dfx ℚ D))

/-- **The level** `U = Kt·Iw_p` ([LWX, §2.4]: "`K^p Iw_q`"): `p`-component in `Iw_p`, tame part in
`Kt`. -/
def levelOf : Subgroup (Dfx ℚ D) where
  carrier := {g | thetaInt p D g ∈ Iw p 1 ∧ tamePart p D g ∈ Kt}
  mul_mem' := fun {a b} ha hb => by
    obtain ⟨ha1, ha2⟩ := ha
    obtain ⟨hb1, hb2⟩ := hb
    refine ⟨?_, ?_⟩
    · rw [map_mul]; exact (Iw p 1).mul_mem ha1 hb1
    · rw [tamePart_mul]; exact Kt.mul_mem ha2 hb2
  one_mem' := ⟨by rw [map_one]; exact (Iw p 1).one_mem, by rw [tamePart_one]; exact Kt.one_mem⟩
  inv_mem' := fun {a} ha => by
    obtain ⟨ha1, ha2⟩ := ha
    refine ⟨?_, ?_⟩
    · have h : thetaInt p D a⁻¹ = (thetaInt p D a)⁻¹ := by
        rw [← coe_thetaIntGL, ← coe_thetaIntGL, map_inv, Matrix.coe_units_inv]
      rw [h]; exact inv_mem_Iw ha1
    · rw [tamePart_inv]; exact Kt.inv_mem ha2

theorem mem_levelOf_iff {g : Dfx ℚ D} :
    g ∈ levelOf p D Kt ↔ thetaInt p D g ∈ Iw p 1 ∧ tamePart p D g ∈ Kt :=
  Iff.rfl

theorem levelOf_subset_levelM1 :
    (levelOf p D Kt : Set (Dfx ℚ D)) ⊆ levelM1 (p := p) (thetaInt p D) :=
  fun _ hg => Iw_one_le_M1 hg.1

theorem ιpD_mem_levelOf {g : GL (Fin 2) ℚ_[p]} (hg : (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) ∈ Iw p 1) :
    ιpD p D g ∈ levelOf p D Kt :=
  ⟨by rw [thetaInt_ιpD]; exact hg, by rw [tamePart_ιpD]; exact Kt.one_mem⟩

theorem mem_levelOf_of_thetaInt_eq_one {g : Dfx ℚ D} (hg : thetaInt p D g = 1) (hK : g ∈ Kt) :
    g ∈ levelOf p D Kt :=
  ⟨by rw [hg]; exact (Iw p 1).one_mem,
    by rw [tamePart_eq_self_of_thetaInt_eq_one p D hg]; exact hK⟩

/-- **`w` normalises the disc-`0` part of the level** (`wQ_conj_mem_Iw` at `p`, and the tame part
is conjugation-invariant). -/
theorem levelOf_wGL_conj : ∀ u ∈ levelOf p D Kt, ‖(thetaInt p D u) 0 1‖ ≤ (p : ℝ)⁻¹ →
    ιpD p D (wGL p) * u * (ιpD p D (wGL p))⁻¹ ∈ levelOf p D Kt ∧
      (ιpD p D (wGL p))⁻¹ * u * ιpD p D (wGL p) ∈ levelOf p D Kt := by
  intro u hu hb
  obtain ⟨hu1, hu2⟩ := hu
  have hw := wQ_conj_mem_Iw hu1 hb
  have hθ1 : thetaInt p D (ιpD p D (wGL p) * u * (ιpD p D (wGL p))⁻¹)
      = wQ p * thetaInt p D u * wQinv p := by
    rw [map_mul, map_mul, ← map_inv, thetaInt_ιpD, thetaInt_ιpD, coe_wGL, coe_wGL_inv]
  have hθ2 : thetaInt p D ((ιpD p D (wGL p))⁻¹ * u * ιpD p D (wGL p))
      = wQinv p * thetaInt p D u * wQ p := by
    rw [map_mul, map_mul, ← map_inv, thetaInt_ιpD, thetaInt_ιpD, coe_wGL, coe_wGL_inv]
  have hconj : (ιpD p D (wGL p))⁻¹ * u * ιpD p D (wGL p)
      = ιpD p D (wGL p)⁻¹ * u * (ιpD p D (wGL p)⁻¹)⁻¹ := by
    rw [map_inv, inv_inv]
  refine ⟨⟨by rw [hθ1]; exact hw.1.1, by rw [tamePart_conj_ιpD]; exact hu2⟩,
    ⟨by rw [hθ2]; exact hw.2.1, ?_⟩⟩
  rw [hconj, tamePart_conj_ιpD]
  exact hu2

/-- **`w_h` normalises the level-`p^{h+1}` part of the level** (`wQH_conj_mem_Iw`). -/
theorem levelOf_wGLH_conj (h : ℕ) :
    ∀ u ∈ levelOf p D Kt, ‖(thetaInt p D u) 0 1‖ ≤ (p : ℝ)⁻¹ ^ h →
    ιpD p D (wGLH p h) * u * (ιpD p D (wGLH p h))⁻¹ ∈ levelOf p D Kt ∧
      (ιpD p D (wGLH p h))⁻¹ * u * ιpD p D (wGLH p h) ∈ levelOf p D Kt := by
  intro u hu hb
  obtain ⟨hu1, hu2⟩ := hu
  have hw := wQH_conj_mem_Iw h hu1 hb
  have hθ1 : thetaInt p D (ιpD p D (wGLH p h) * u * (ιpD p D (wGLH p h))⁻¹)
      = wQH p h * thetaInt p D u * wQHinv p h := by
    rw [map_mul, map_mul, ← map_inv, thetaInt_ιpD, thetaInt_ιpD, coe_wGLH, coe_wGLH_inv]
  have hθ2 : thetaInt p D ((ιpD p D (wGLH p h))⁻¹ * u * ιpD p D (wGLH p h))
      = wQHinv p h * thetaInt p D u * wQH p h := by
    rw [map_mul, map_mul, ← map_inv, thetaInt_ιpD, thetaInt_ιpD, coe_wGLH, coe_wGLH_inv]
  have hconj : (ιpD p D (wGLH p h))⁻¹ * u * ιpD p D (wGLH p h)
      = ιpD p D (wGLH p h)⁻¹ * u * (ιpD p D (wGLH p h)⁻¹)⁻¹ := by
    rw [map_inv, inv_inv]
  refine ⟨⟨by rw [hθ1]; exact hw.1.1, by rw [tamePart_conj_ιpD]; exact hu2⟩,
    ⟨by rw [hθ2]; exact hw.2.1, ?_⟩⟩
  rw [hconj, tamePart_conj_ιpD]
  exact hu2

/-! ### The tame scalar and the central condition -/

/-- The global scalar `p ∈ D^×`. -/
def pUnit : Dˣ :=
  Units.map (algebraMap ℚ D).toMonoidHom (Units.mk0 (p : ℚ) (by exact_mod_cast hp.out.ne_zero))

theorem thetaInt_unitsIncl_pUnit :
    thetaInt p D (unitsIncl ℚ D (pUnit p D))
      = (p : ℚ_[p]) • (1 : Matrix (Fin 2) (Fin 2) ℚ_[p]) := by
  have h := QMF.toMatrix_unitsIncl_algebraMap (A := D) (padicPlace p) (p : ℚ)
    (by exact_mod_cast hp.out.ne_zero)
  show RingHom.mapMatrix (padicComparisonSymm p)
    (toMatrix ℚ D (padicPlace p) (unitsIncl ℚ D (pUnit p D))) = _
  rw [pUnit, h, map_natCast]
  refine Matrix.ext fun i j => ?_
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul,
    smul_eq_mul, map_mul, map_natCast, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

omit [RigidificationAt ℚ D (padicPlace p)] in
theorem unitsIncl_pUnit_comm (x : Dfx ℚ D) :
    unitsIncl ℚ D (pUnit p D) * x = x * unitsIncl ℚ D (pUnit p D) :=
  QMF.unitsIncl_algebraMap_comm (p : ℚ) _ x

/-- **The tame scalar** `p_global⁻¹·p_p = (p^{(p)})⁻¹`: `1` at `p` and `p⁻¹` at every place away
from `p` (`p^{(p)}` is the prime-to-`p` part of the global `p`, as in `AtkinLehnerData.central_pow`). -/
def tameScalar : Dfx ℚ D := (unitsIncl ℚ D (pUnit p D))⁻¹ * ιpD p D (pGL p)

theorem thetaInt_tameScalar : thetaInt p D (tameScalar p D) = 1 := by
  have h1 : thetaIntGL p D (unitsIncl ℚ D (pUnit p D)) = pGL p :=
    Units.ext (thetaInt_unitsIncl_pUnit p D)
  have h2 : thetaIntGL p D (tameScalar p D) = 1 := by
    rw [tameScalar, map_mul, map_inv, h1, thetaIntGL_ιpD, inv_mul_cancel]
  exact congrArg Units.val h2

theorem tameScalar_comm (x : Dfx ℚ D) : tameScalar p D * x = x * tameScalar p D := by
  have h1' : (unitsIncl ℚ D (pUnit p D))⁻¹ * x = x * (unitsIncl ℚ D (pUnit p D))⁻¹ := by
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, unitsIncl_pUnit_comm p D x, mul_inv_cancel_right]
  rw [tameScalar]
  calc (unitsIncl ℚ D (pUnit p D))⁻¹ * ιpD p D (pGL p) * x
      = (unitsIncl ℚ D (pUnit p D))⁻¹ * (x * ιpD p D (pGL p)) := by
        rw [mul_assoc, ιpD_pGL_comm p D x]
    _ = x * (unitsIncl ℚ D (pUnit p D))⁻¹ * ιpD p D (pGL p) := by rw [← mul_assoc, h1']
    _ = x * ((unitsIncl ℚ D (pUnit p D))⁻¹ * ιpD p D (pGL p)) := mul_assoc _ _ _

/-- **`central_pow` from a power of the tame scalar in the tame level**:
`ιp(p·1)^N = p^N_global · (tameScalar)^N`. -/
theorem central_pow_of_tameScalar_pow_mem {N : ℕ} (hN : 0 < N)
    (hmem : tameScalar p D ^ N ∈ Kt) :
    ∃ N, 0 < N ∧ ∃ γ ∈ globalUnits ℚ D, ∃ u ∈ levelOf p D Kt,
      ιpD p D (pGL p) ^ N = γ * u ∧ thetaInt p D u = 1 ∧ ∀ x, γ * x = x * γ := by
  have hθ : thetaInt p D (tameScalar p D ^ N) = 1 := by
    rw [map_pow, thetaInt_tameScalar, one_pow]
  have hdecomp : ιpD p D (pGL p) = unitsIncl ℚ D (pUnit p D) * tameScalar p D := by
    rw [tameScalar, mul_inv_cancel_left]
  have hcomm : Commute (unitsIncl ℚ D (pUnit p D)) (tameScalar p D) :=
    unitsIncl_pUnit_comm p D _
  refine ⟨N, hN, unitsIncl ℚ D (pUnit p D) ^ N, ⟨pUnit p D ^ N, map_pow _ _ _⟩,
    tameScalar p D ^ N, mem_levelOf_of_thetaInt_eq_one p D Kt hθ hmem, ?_, hθ, fun x => ?_⟩
  · rw [hdecomp, hcomm.mul_pow]
  · exact (Commute.pow_left (unitsIncl_pUnit_comm p D x) N : _)

/-! ### The arithmetic input -/

/-- **The arithmetic input for the Atkin–Lehner data of `D/ℚ`**: the tame level, the norm class,
and normalised neat class representatives.  Every field is a theorem about `D` that lies beyond the
present library (the reduced norm on a central simple algebra; Hasse–Schilling–Maass and weak
approximation for the normalised representatives; neatness of a chosen level); see the module
docstring. -/
structure QuaternionInput (ι : Type*) [Fintype ι] where
  /-- The tame level: adelic units of trivial `p`-component. -/
  Kt : Subgroup (Dfx ℚ D)
  Kt_le : Kt ≤ tameSubgroup p D
  /-- A power of the tame scalar lies in the tame level (true for every open tame level). -/
  tameScalar_pow_mem : ∃ N, 0 < N ∧ tameScalar p D ^ N ∈ Kt
  /-- **The norm class** `q(g) = ∏_ℓ ℓ^{v_ℓ(nrd g)}`, a positive rational. -/
  normClass : Dfx ℚ D →* ℚˣ
  /-- On `D^×` the norm class is the reduced norm, which is `det θ_p`. -/
  normClass_global : ∀ γ ∈ globalUnits ℚ D,
    (((normClass γ : ℚˣ) : ℚ) : ℚ_[p]) = (thetaInt p D γ).det
  /-- `‖det θ_p(g)‖ = ‖q(g)‖`: the `p`-adic size of the `p`-component is the norm class's. -/
  norm_det_thetaInt : ∀ g, ‖(thetaInt p D g).det‖ = ‖(((normClass g : ℚˣ) : ℚ) : ℚ_[p])‖
  /-- On `p`-local elements the norm class is the `p`-power of the determinant's valuation. -/
  normClass_ιpD : ∀ g : GL (Fin 2) ℚ_[p],
    ((normClass (ιpD p D g) : ℚˣ) : ℚ)
      = (p : ℚ) ^ ((g : Matrix (Fin 2) (Fin 2) ℚ_[p]).det).valuation
  /-- The tame level has unit norms. -/
  normClass_tame : ∀ g ∈ Kt, normClass g = 1
  /-- The class representatives. -/
  c : ι → Dfx ℚ D
  hc : Function.Bijective
    (fun i => (Quotient.mk'' (c i) :
      DoubleCoset.Quotient ((globalUnits ℚ D : Subgroup (Dfx ℚ D)) : Set (Dfx ℚ D))
        ((levelOf p D Kt : Subgroup (Dfx ℚ D)) : Set (Dfx ℚ D))))
  /-- Neatness ([LWX, Hypothesis 2.10]). -/
  hstab : ∀ i, AutomorphicFunction.stabilizerAtSlash (globalUnits ℚ D) (levelOf p D Kt) (c i) = ⊥
  /-- The representatives have trivial `p`-component ([LWX, §2.11]). -/
  c_thetaInt : ∀ i, thetaInt p D (c i) = 1
  /-- The representatives have unit norm class (the normalisation behind `det = p`). -/
  c_normClass : ∀ i, normClass (c i) = 1

namespace QuaternionInput

variable {p D}
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (X : QuaternionInput p D ι)

/-- The level `U = Kt·Iw_p` of the input. -/
abbrev level : Subgroup (Dfx ℚ D) := levelOf p D X.Kt

omit [DecidableEq ι] in
theorem level_subset_levelM1 : (X.level : Set (Dfx ℚ D)) ⊆ levelM1 (p := p) (thetaInt p D) :=
  levelOf_subset_levelM1 p D X.Kt

omit [DecidableEq ι] in
/-- `det θ_p(g)·q(g)⁻¹` is a `p`-adic unit. -/
theorem norm_det_mul_inv_normClass (g : Dfx ℚ D) :
    ‖(thetaInt p D g).det * ((((X.normClass g : ℚˣ) : ℚ) : ℚ_[p]))⁻¹‖ = 1 := by
  rw [norm_mul, norm_inv, X.norm_det_thetaInt g, mul_inv_cancel₀]
  rw [norm_ne_zero_iff]
  exact_mod_cast (X.normClass g).ne_zero

omit [DecidableEq ι] in
/-- The level has unit norm class. -/
theorem normClass_level : ∀ u ∈ X.level, X.normClass u = 1 := by
  intro u hu
  have hval : (thetaInt p D u).det.valuation = 0 := by
    have hdet1 : ‖(thetaInt p D u).det‖ = 1 := hu.1.2.2
    have hne : (thetaInt p D u).det ≠ 0 := by
      intro h0; rw [h0, norm_zero] at hdet1; exact zero_ne_one hdet1
    rw [Padic.norm_eq_zpow_neg_valuation hne] at hdet1
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
    have hinj := zpow_right_injective₀ (by positivity : (0 : ℝ) < p) hp1.ne'
      (hdet1.trans (zpow_zero _).symm)
    simpa using hinj
  rw [eq_ιpD_mul_tamePart p D u, map_mul, X.normClass_tame _ hu.2, mul_one]
  refine Units.ext ?_
  rw [X.normClass_ιpD, coe_thetaIntGL, hval, zpow_zero, Units.val_one]

omit [DecidableEq ι] in
theorem normClass_ιpD_vGL (c : ℚ_[p]) :
    ((X.normClass (ιpD p D (vGL p c)) : ℚˣ) : ℚ) = p := by
  rw [X.normClass_ιpD, coe_vGL, det_vQ, Padic.valuation_p, zpow_one]

omit [DecidableEq ι] in
theorem normClass_ιpD_wGL : ((X.normClass (ιpD p D (wGL p)) : ℚˣ) : ℚ) = (p : ℚ) ^ 2 := by
  rw [X.normClass_ιpD, coe_wGL, det_wQ, Padic.valuation_pow, Padic.valuation_p, mul_one]
  norm_cast

omit [DecidableEq ι] in
theorem normClass_ιpD_wGLH (h : ℕ) :
    ((X.normClass (ιpD p D (wGLH p h)) : ℚˣ) : ℚ) = (p : ℚ) ^ (h + 1) := by
  rw [X.normClass_ιpD, coe_wGLH, det_wQH, Padic.valuation_pow, Padic.valuation_p, mul_one]
  norm_cast

omit [DecidableEq ι] in
theorem normClass_ιpD_pGL : ((X.normClass (ιpD p D (pGL p)) : ℚˣ) : ℚ) = (p : ℚ) ^ 2 := by
  have hdet : ((pGL p : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p]).det
      = (p : ℚ_[p]) ^ 2 := by
    show ((p : ℚ_[p]) • (1 : Matrix (Fin 2) (Fin 2) ℚ_[p])).det = _
    rw [Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one]
  rw [X.normClass_ιpD, hdet, Padic.valuation_pow, Padic.valuation_p, mul_one]
  norm_cast

/-! ### The Hecke characters -/

section HeckeChar

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [CharZero K]
variable (ψ : ℚ_[p] →+* K)

/-- **The Hecke character** `χ = ψ_A ∘ ν` of the classical weight `(k, ψ)` on the disc `ω`
([LWX, Prop 3.22]'s "central Hecke character associated to `ψ`", `lwx.txt:1783`):
`χ(g) = ψ_neb(det θ_p(g) · q(g)⁻¹)`, a unit by `norm_det_thetaInt`. -/
def heckeChar (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (k : ℕ) (ζ : K) (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖)
    (hζ : IsPrimitiveRoot ζ p) : Dfx ℚ D →* Kˣ where
  toFun g := Units.mk0
    (nebCharK ψ ω k ζ (ψ ((thetaInt p D g).det * ((((X.normClass g : ℚˣ) : ℚ) : ℚ_[p]))⁻¹)))
    (nebCharK_psi_ne_zero ψ ω k ζ hp2 hψ hζ (norm_natCast_p ψ hψ)
      (X.norm_det_mul_inv_normClass g))
  map_one' := by
    refine Units.ext ?_
    show nebCharK ψ ω k ζ
      (ψ ((thetaInt p D 1).det * ((((X.normClass 1 : ℚˣ) : ℚ) : ℚ_[p]))⁻¹)) = 1
    rw [map_one (thetaInt p D), Matrix.det_one, map_one X.normClass, Units.val_one, Rat.cast_one,
      inv_one, mul_one]
    exact nebCharK_psi_of_norm_sub_one_le_sq ψ ω k ζ hp2 hψ hζ (norm_natCast_p ψ hψ)
      (by rw [sub_self, norm_zero]; positivity)
  map_mul' g g' := by
    refine Units.ext ?_
    have harg : (thetaInt p D (g * g')).det * ((((X.normClass (g * g') : ℚˣ) : ℚ) : ℚ_[p]))⁻¹
        = ((thetaInt p D g).det * ((((X.normClass g : ℚˣ) : ℚ) : ℚ_[p]))⁻¹)
          * ((thetaInt p D g').det * ((((X.normClass g' : ℚˣ) : ℚ) : ℚ_[p]))⁻¹) := by
      rw [map_mul (thetaInt p D), Matrix.det_mul, map_mul X.normClass, Units.val_mul, Rat.cast_mul,
        mul_inv]
      ring
    show nebCharK ψ ω k ζ
        (ψ ((thetaInt p D (g * g')).det * ((((X.normClass (g * g') : ℚˣ) : ℚ) : ℚ_[p]))⁻¹))
      = nebCharK ψ ω k ζ (ψ ((thetaInt p D g).det * ((((X.normClass g : ℚˣ) : ℚ) : ℚ_[p]))⁻¹))
        * nebCharK ψ ω k ζ
          (ψ ((thetaInt p D g').det * ((((X.normClass g' : ℚˣ) : ℚ) : ℚ_[p]))⁻¹))
    rw [harg]
    exact nebCharK_psi_mul ψ ω k ζ hp2 hψ hζ (norm_natCast_p ψ hψ)
      (X.norm_det_mul_inv_normClass g) (X.norm_det_mul_inv_normClass g')

omit [DecidableEq ι] in
theorem heckeChar_apply (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (k : ℕ) (ζ : K) (hp2 : p ≠ 2)
    (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hζ : IsPrimitiveRoot ζ p) (g : Dfx ℚ D) :
    ((X.heckeChar ψ ω k ζ hp2 hψ hζ g : Kˣ) : K)
      = nebCharK ψ ω k ζ
          (ψ ((thetaInt p D g).det * ((((X.normClass g : ℚˣ) : ℚ) : ℚ_[p]))⁻¹)) :=
  rfl

omit [DecidableEq ι] in
/-- `χ` is trivial on `D^×` (`normClass_global`, the product formula for a positive rational). -/
theorem heckeChar_global (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (k : ℕ) (ζ : K) (hp2 : p ≠ 2)
    (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hζ : IsPrimitiveRoot ζ p) :
    ∀ γ ∈ globalUnits ℚ D, X.heckeChar ψ ω k ζ hp2 hψ hζ γ = 1 := by
  intro γ hγ
  refine Units.ext ?_
  rw [heckeChar_apply, X.normClass_global γ hγ, mul_inv_cancel₀ (det_thetaInt_ne_zero p D γ),
    Units.val_one]
  exact nebCharK_psi_of_norm_sub_one_le_sq ψ ω k ζ hp2 hψ hζ (norm_natCast_p ψ hψ)
    (by rw [sub_self, norm_zero]; positivity)

omit [DecidableEq ι] in
/-- On the level, `χ` is the nebentypus of the `p`-component (`normClass_level`). -/
theorem heckeChar_level (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (k : ℕ) (ζ : K) (hp2 : p ≠ 2)
    (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hζ : IsPrimitiveRoot ζ p) :
    ∀ u ∈ X.level, ((X.heckeChar ψ ω k ζ hp2 hψ hζ u : Kˣ) : K)
      = nebCharK ψ ω k ζ (ψ (thetaInt p D u).det) := by
  intro u hu
  rw [heckeChar_apply, X.normClass_level u hu, Units.val_one, Rat.cast_one, inv_one, mul_one]

omit [DecidableEq ι] in
theorem heckeChar_ιpD_vGL (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (k : ℕ) (ζ : K) (hp2 : p ≠ 2)
    (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hζ : IsPrimitiveRoot ζ p) :
    ∀ c : ℚ_[p], X.heckeChar ψ ω k ζ hp2 hψ hζ (ιpD p D (vGL p c)) = 1 := by
  intro c
  refine Units.ext ?_
  rw [heckeChar_apply, X.normClass_ιpD_vGL c, thetaInt_ιpD, coe_vGL, det_vQ, Rat.cast_natCast,
    mul_inv_cancel₀ (Nat.cast_ne_zero.2 hp.out.ne_zero), Units.val_one]
  exact nebCharK_psi_of_norm_sub_one_le_sq ψ ω k ζ hp2 hψ hζ (norm_natCast_p ψ hψ)
    (by rw [sub_self, norm_zero]; positivity)

omit [DecidableEq ι] in
theorem heckeChar_ιpD_wGL (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (k : ℕ) (ζ : K) (hp2 : p ≠ 2)
    (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hζ : IsPrimitiveRoot ζ p) :
    X.heckeChar ψ ω k ζ hp2 hψ hζ (ιpD p D (wGL p)) = 1 := by
  refine Units.ext ?_
  rw [heckeChar_apply, X.normClass_ιpD_wGL, thetaInt_ιpD, coe_wGL, det_wQ, Rat.cast_pow,
    Rat.cast_natCast, mul_inv_cancel₀ (pow_ne_zero 2 (Nat.cast_ne_zero.2 hp.out.ne_zero)),
    Units.val_one]
  exact nebCharK_psi_of_norm_sub_one_le_sq ψ ω k ζ hp2 hψ hζ (norm_natCast_p ψ hψ)
    (by rw [sub_self, norm_zero]; positivity)

/-- **The Hecke character of conductor `p^{h+1}`**, with `nebCharKH`. -/
def heckeCharH (h : ℕ) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (k : ℕ) (ζh : K) (hp2 : p ≠ 2)
    (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hh : 0 < h) (hζh : IsPrimitiveRoot ζh (p ^ h)) : Dfx ℚ D →* Kˣ where
  toFun g := Units.mk0
    (nebCharKH h ψ ω k ζh
      (ψ ((thetaInt p D g).det * ((((X.normClass g : ℚˣ) : ℚ) : ℚ_[p]))⁻¹)))
    (nebCharKH_psi_ne_zero h ψ ω k ζh hp2 hψ hh hζh (norm_natCast_p ψ hψ)
      (X.norm_det_mul_inv_normClass g))
  map_one' := by
    refine Units.ext ?_
    show nebCharKH h ψ ω k ζh
      (ψ ((thetaInt p D 1).det * ((((X.normClass 1 : ℚˣ) : ℚ) : ℚ_[p]))⁻¹)) = 1
    rw [map_one (thetaInt p D), Matrix.det_one, map_one X.normClass, Units.val_one, Rat.cast_one,
      inv_one, mul_one]
    exact nebCharKH_psi_of_norm_sub_one_le_pow h ψ ω k ζh hp2 hψ hh hζh (norm_natCast_p ψ hψ)
      (by rw [sub_self, norm_zero]; positivity)
  map_mul' g g' := by
    refine Units.ext ?_
    have harg : (thetaInt p D (g * g')).det * ((((X.normClass (g * g') : ℚˣ) : ℚ) : ℚ_[p]))⁻¹
        = ((thetaInt p D g).det * ((((X.normClass g : ℚˣ) : ℚ) : ℚ_[p]))⁻¹)
          * ((thetaInt p D g').det * ((((X.normClass g' : ℚˣ) : ℚ) : ℚ_[p]))⁻¹) := by
      rw [map_mul (thetaInt p D), Matrix.det_mul, map_mul X.normClass, Units.val_mul, Rat.cast_mul,
        mul_inv]
      ring
    show nebCharKH h ψ ω k ζh
        (ψ ((thetaInt p D (g * g')).det * ((((X.normClass (g * g') : ℚˣ) : ℚ) : ℚ_[p]))⁻¹))
      = nebCharKH h ψ ω k ζh
          (ψ ((thetaInt p D g).det * ((((X.normClass g : ℚˣ) : ℚ) : ℚ_[p]))⁻¹))
        * nebCharKH h ψ ω k ζh
          (ψ ((thetaInt p D g').det * ((((X.normClass g' : ℚˣ) : ℚ) : ℚ_[p]))⁻¹))
    rw [harg]
    exact nebCharKH_psi_mul h ψ ω k ζh hp2 hψ hh hζh (norm_natCast_p ψ hψ)
      (X.norm_det_mul_inv_normClass g) (X.norm_det_mul_inv_normClass g')

omit [DecidableEq ι] in
theorem heckeCharH_apply (h : ℕ) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (k : ℕ) (ζh : K) (hp2 : p ≠ 2)
    (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hh : 0 < h) (hζh : IsPrimitiveRoot ζh (p ^ h)) (g : Dfx ℚ D) :
    ((X.heckeCharH ψ h ω k ζh hp2 hψ hh hζh g : Kˣ) : K)
      = nebCharKH h ψ ω k ζh
          (ψ ((thetaInt p D g).det * ((((X.normClass g : ℚˣ) : ℚ) : ℚ_[p]))⁻¹)) :=
  rfl

omit [DecidableEq ι] in
theorem heckeCharH_global (h : ℕ) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (k : ℕ) (ζh : K) (hp2 : p ≠ 2)
    (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hh : 0 < h) (hζh : IsPrimitiveRoot ζh (p ^ h)) :
    ∀ γ ∈ globalUnits ℚ D, X.heckeCharH ψ h ω k ζh hp2 hψ hh hζh γ = 1 := by
  intro γ hγ
  refine Units.ext ?_
  rw [heckeCharH_apply, X.normClass_global γ hγ, mul_inv_cancel₀ (det_thetaInt_ne_zero p D γ),
    Units.val_one]
  exact nebCharKH_psi_of_norm_sub_one_le_pow h ψ ω k ζh hp2 hψ hh hζh (norm_natCast_p ψ hψ)
    (by rw [sub_self, norm_zero]; positivity)

omit [DecidableEq ι] in
theorem heckeCharH_level (h : ℕ) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (k : ℕ) (ζh : K) (hp2 : p ≠ 2)
    (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hh : 0 < h) (hζh : IsPrimitiveRoot ζh (p ^ h)) :
    ∀ u ∈ X.level, ((X.heckeCharH ψ h ω k ζh hp2 hψ hh hζh u : Kˣ) : K)
      = nebCharKH h ψ ω k ζh (ψ (thetaInt p D u).det) := by
  intro u hu
  rw [heckeCharH_apply, X.normClass_level u hu, Units.val_one, Rat.cast_one, inv_one, mul_one]

omit [DecidableEq ι] in
theorem heckeCharH_ιpD_vGL (h : ℕ) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (k : ℕ) (ζh : K) (hp2 : p ≠ 2)
    (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hh : 0 < h) (hζh : IsPrimitiveRoot ζh (p ^ h)) :
    ∀ c : ℚ_[p], X.heckeCharH ψ h ω k ζh hp2 hψ hh hζh (ιpD p D (vGL p c)) = 1 := by
  intro c
  refine Units.ext ?_
  rw [heckeCharH_apply, X.normClass_ιpD_vGL c, thetaInt_ιpD, coe_vGL, det_vQ, Rat.cast_natCast,
    mul_inv_cancel₀ (Nat.cast_ne_zero.2 hp.out.ne_zero), Units.val_one]
  exact nebCharKH_psi_of_norm_sub_one_le_pow h ψ ω k ζh hp2 hψ hh hζh (norm_natCast_p ψ hψ)
    (by rw [sub_self, norm_zero]; positivity)

omit [DecidableEq ι] in
theorem heckeCharH_ιpD_wGLH (h : ℕ) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (k : ℕ) (ζh : K) (hp2 : p ≠ 2)
    (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hh : 0 < h) (hζh : IsPrimitiveRoot ζh (p ^ h)) :
    X.heckeCharH ψ h ω k ζh hp2 hψ hh hζh (ιpD p D (wGLH p h)) = 1 := by
  refine Units.ext ?_
  rw [heckeCharH_apply, X.normClass_ιpD_wGLH h, thetaInt_ιpD, coe_wGLH, det_wQH, Rat.cast_pow,
    Rat.cast_natCast, mul_inv_cancel₀ (pow_ne_zero (h + 1) (Nat.cast_ne_zero.2 hp.out.ne_zero)),
    Units.val_one]
  exact nebCharKH_psi_of_norm_sub_one_le_pow h ψ ω k ζh hp2 hψ hh hζh (norm_natCast_p ψ hψ)
    (by rw [sub_self, norm_zero]; positivity)

end HeckeChar

/-! ### The families -/

section Family

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [CharZero K]
variable (ψ : ℚ_[p] →+* K) {ζ : K}

/-- **The Atkin–Lehner family of `D/ℚ`** at conductor `p²`. -/
def atkinLehnerFamily (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hζ : IsPrimitiveRoot ζ p) :
    AtkinLehnerFamily (thetaInt p D) ψ X.level (globalUnits ℚ D) ζ where
  ιp := ιpD p D
  theta_ιp := thetaInt_ιpD p D
  ιp_mem_U := fun _ hg => ιpD_mem_levelOf p D X.Kt hg
  ιp_pGL_comm := ιpD_pGL_comm p D
  central_pow := by
    obtain ⟨N, hN, hmem⟩ := X.tameScalar_pow_mem
    exact central_pow_of_tameScalar_pow_mem p D X.Kt hN hmem
  w_conj_mem_U := levelOf_wGL_conj p D X.Kt
  χ := fun ω k => X.heckeChar ψ ω k ζ hp2 hψ hζ
  χ_Γ := fun ω k => X.heckeChar_global ψ ω k ζ hp2 hψ hζ
  χ_U := fun ω k => X.heckeChar_level ψ ω k ζ hp2 hψ hζ
  χ_vGL := fun ω k => X.heckeChar_ιpD_vGL ψ ω k ζ hp2 hψ hζ
  χ_wGL := fun ω k => X.heckeChar_ιpD_wGL ψ ω k ζ hp2 hψ hζ

/-- **The level-`h` family of `D/ℚ`** over the same section. -/
def atkinLehnerFamilyH (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hζ : IsPrimitiveRoot ζ p)
    (h : ℕ) {ζh : K} (hh : 0 < h) (hζh : IsPrimitiveRoot ζh (p ^ h)) :
    AtkinLehnerFamilyH (thetaInt p D) ψ X.level (X.atkinLehnerFamily ψ hp2 hψ hζ) h ζh where
  χ := fun ω k => X.heckeCharH ψ h ω k ζh hp2 hψ hh hζh
  χ_Γ := fun ω k => X.heckeCharH_global ψ h ω k ζh hp2 hψ hh hζh
  χ_U := fun ω k => X.heckeCharH_level ψ h ω k ζh hp2 hψ hh hζh
  χ_vGL := fun ω k => X.heckeCharH_ιpD_vGL ψ h ω k ζh hp2 hψ hh hζh
  χ_wGLH := fun ω k => X.heckeCharH_ιpD_wGLH ψ h ω k ζh hp2 hψ hh hζh
  w_conj_mem_U := levelOf_wGLH_conj p D X.Kt h

end Family

/-! ### The coset representatives and the certificates -/

variable (p D) in
/-- The `U_p`-representatives `v_c = ιp (p 0; cp 1)` ([LWX, §2.5]). -/
def vRepQ (c : Fin p) : Dfx ℚ D := ιpD p D (vGL p (c : ℕ))

variable (p D) in
theorem vRepQ_mem_levelM1 (c : Fin p) : vRepQ p D c ∈ levelM1 (p := p) (thetaInt p D) := by
  show thetaInt p D (ιpD p D (vGL p (c : ℕ))) ∈ M1 p
  rw [thetaInt_ιpD, coe_vGL]
  exact vQ_mem_M1 (IsUltrametricDist.norm_natCast_le_one ℚ_[p] _)

variable (p D) in
/-- The `U_p`-element `η = ιp (p 0; 0 1)`. -/
def upEltQ : Dfx ℚ D := ιpD p D (vGL p 0)

section Family

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [CharZero K]
variable (ψ : ℚ_[p] →+* K) {ζ : K}

omit [DecidableEq ι] in
theorem vRepF_atkinLehnerFamily (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖)
    (hζ : IsPrimitiveRoot ζ p) :
    vRepF (thetaInt p D) ψ X.level (X.atkinLehnerFamily ψ hp2 hψ hζ) = vRepQ p D :=
  rfl

omit [DecidableEq ι] in
theorem upEltF_atkinLehnerFamily (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖)
    (hζ : IsPrimitiveRoot ζ p) :
    upEltF (thetaInt p D) ψ X.level (X.atkinLehnerFamily ψ hp2 hψ hζ) = upEltQ p D :=
  rfl

end Family

omit [DecidableEq ι] in
/-- **The coset decomposition** `U η U = ∐_{c<p} U v_c` ([LWX, §2.5]), from the local Iwahori
decomposition (`exists_mem_Iw_mul_vQ`) and the commutation of the tame part with `p`-local
elements. -/
theorem bijOn_vRepQ :
    Set.BijOn (Quotient.mk'' : Dfx ℚ D → RightCosets X.level) (Set.range (vRepQ p D))
      (((Quotient.mk'' : Dfx ℚ D → RightCosets X.level) ''
        (({upEltQ p D} : Set (Dfx ℚ D)) * (X.level : Set (Dfx ℚ D)))) :
          Set (RightCosets X.level)) := by
  have hℓ : ∀ c : ℚ_[p], (vGL p 0)⁻¹ * vGL p c = ℓGL p 0 c := fun c => by
    rw [inv_mul_eq_iff_eq_mul]
    refine Units.ext ?_
    rw [Units.val_mul, coe_vGL, coe_vGL, coe_ℓGL]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [vQ, ℓQ, Matrix.mul_apply, Fin.sum_univ_two]
  refine ⟨?_, ?_, ?_⟩
  · rintro _ ⟨c, rfl⟩
    have hc : ‖((c : ℕ) : ℚ_[p])‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one ℚ_[p] _
    refine ⟨vRepQ p D c, Set.mem_mul.2 ⟨upEltQ p D, Set.mem_singleton _,
      ιpD p D (ℓGL p 0 (c : ℕ)), ?_, ?_⟩, rfl⟩
    · exact ιpD_mem_levelOf p D X.Kt (by rw [coe_ℓGL]; exact ℓQ_mem_Iw (by simp) hc)
    · rw [upEltQ, vRepQ, ← map_mul, ← hℓ, mul_inv_cancel_left]
  · rintro _ ⟨b, rfl⟩ _ ⟨c, rfl⟩ hbc
    have hrel : vRepQ p D c * (vRepQ p D b)⁻¹ ∈ X.level :=
      QuotientGroup.rightRel_apply.1 (Quotient.eq''.1 hbc)
    obtain ⟨h1, -⟩ := hrel
    have hk : thetaInt p D (vRepQ p D c * (vRepQ p D b)⁻¹)
        = vQ p (c : ℕ) * (vQ p (b : ℕ))⁻¹ := by
      rw [map_mul, vRepQ, vRepQ, ← map_inv, thetaInt_ιpD, thetaInt_ιpD, coe_vGL,
        Matrix.coe_units_inv, coe_vGL]
    rw [hk] at h1
    have heq : vQ p (c : ℕ) = (vQ p (c : ℕ) * (vQ p (b : ℕ))⁻¹) * vQ p (b : ℕ) := by
      rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 (by
        rw [det_vQ]; exact Nat.cast_ne_zero.2 hp.out.ne_zero)), Matrix.mul_one]
    exact congrArg (vRepQ p D) (eq_of_vQ_eq_mul_vQ h1 heq).symm
  · rintro _ ⟨_, ⟨_, rfl, u, hu, rfl⟩, rfl⟩
    obtain ⟨hu1, hu2⟩ := hu
    obtain ⟨c, k', hk', hkv⟩ := exists_mem_Iw_mul_vQ hu1
    have hk'0 : k'.det ≠ 0 := by
      intro h0
      have hn := hk'.2.2
      rw [h0, norm_zero] at hn
      exact zero_ne_one hn
    obtain ⟨kGL, hkGL⟩ : ∃ kGL : GL (Fin 2) ℚ_[p], (kGL : Matrix (Fin 2) (Fin 2) ℚ_[p]) = k' :=
      ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero k' hk'0, rfl⟩
    have hGL : vGL p 0 * thetaIntGL p D u = kGL * vGL p (c : ℕ) :=
      Units.ext (by rw [Units.val_mul, Units.val_mul, hkGL]; exact hkv)
    have hw : ιpD p D kGL * tamePart p D u ∈ X.level :=
      X.level.mul_mem (ιpD_mem_levelOf p D X.Kt (by rw [hkGL]; exact hk'))
        (mem_levelOf_of_thetaInt_eq_one p D X.Kt (thetaInt_tamePart p D u) hu2)
    have hcomm := ιpD_comm_of_thetaInt_eq_one p D (vGL p (c : ℕ)) (thetaInt_tamePart p D u)
    have hdecomp : upEltQ p D * u = (ιpD p D kGL * tamePart p D u) * vRepQ p D c := by
      calc upEltQ p D * u = upEltQ p D * (ιpD p D (thetaIntGL p D u) * tamePart p D u) := by
            rw [← eq_ιpD_mul_tamePart]
        _ = ιpD p D (vGL p 0 * thetaIntGL p D u) * tamePart p D u := by
            rw [map_mul, upEltQ, mul_assoc]
        _ = ιpD p D kGL * (ιpD p D (vGL p (c : ℕ)) * tamePart p D u) := by
            rw [hGL, map_mul, mul_assoc]
        _ = (ιpD p D kGL * tamePart p D u) * vRepQ p D c := by
            rw [hcomm, vRepQ, mul_assoc]
    refine ⟨vRepQ p D c, ⟨c, rfl⟩, ?_⟩
    refine Quotient.sound' (QuotientGroup.rightRel_apply.2 ?_)
    show upEltQ p D * u * (vRepQ p D c)⁻¹ ∈ X.level
    rw [hdecomp, mul_inv_cancel_right]
    exact hw

theorem injective_vRepQ : Function.Injective (vRepQ p D) := by
  intro b c hbc
  have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero
  have h1 : ((b : ℕ) : ℚ_[p]) * p = ((c : ℕ) : ℚ_[p]) * p := by
    have hh := congrArg (fun g => thetaInt p D g 1 0) hbc
    simpa [vRepQ, thetaInt_ιpD, vQ] using hh
  exact Fin.ext (Nat.cast_injective (mul_right_cancel₀ hp0 h1))

omit [DecidableEq ι] in
theorem finite_image_upEltQ :
    (((Quotient.mk'' : Dfx ℚ D → RightCosets X.level) ''
      (({upEltQ p D} : Set (Dfx ℚ D)) * (X.level : Set (Dfx ℚ D)))) :
        Set (RightCosets X.level)).Finite := by
  rw [← X.bijOn_vRepQ.image_eq]
  exact (Set.finite_range _).image _

omit [DecidableEq ι] in
/-- **The factorisation** `c_i v_t⁻¹ = d · c_j · u` ([LWX, Prop 3.1]: "write each `γ_i v_j⁻¹`
uniquely as `δ_{i,j}⁻¹ γ_{λ_{i,j}} u_{i,j}`", `lwx.txt:1075`) from the class-set bijection. -/
theorem exists_factorisation (i : ι) (t : Fin p) :
    ∃ j : ι, ∃ d : Dfx ℚ D, ∃ u : X.level, d ∈ globalUnits ℚ D ∧
      X.c i * (vRepQ p D t)⁻¹ = d * X.c j * (u : Dfx ℚ D) := by
  obtain ⟨j, hj⟩ := X.hc.2 (Quotient.mk'' (X.c i * (vRepQ p D t)⁻¹))
  obtain ⟨γ, hγ, v, hv, hrel⟩ := DoubleCoset.rel_iff.mp (Quotient.eq''.mp hj)
  exact ⟨j, γ, ⟨v, hv⟩, hγ, hrel⟩

/-- The target index `λ_{i,t}`. -/
def idx (i : ι) (t : Fin p) : ι := (X.exists_factorisation i t).choose

/-- The global element `δ_{i,t}⁻¹`. -/
def dElt (i : ι) (t : Fin p) : Dfx ℚ D := (X.exists_factorisation i t).choose_spec.choose

/-- The level element `u_{i,t}`. -/
def uElt (i : ι) (t : Fin p) : X.level :=
  (X.exists_factorisation i t).choose_spec.choose_spec.choose

omit [DecidableEq ι] in
theorem dElt_mem (i : ι) (t : Fin p) : X.dElt i t ∈ globalUnits ℚ D :=
  (X.exists_factorisation i t).choose_spec.choose_spec.choose_spec.1

omit [DecidableEq ι] in
theorem c_mul_vRepQ_inv (i : ι) (t : Fin p) :
    X.c i * (vRepQ p D t)⁻¹ = X.dElt i t * X.c (X.idx i t) * (X.uElt i t : Dfx ℚ D) :=
  (X.exists_factorisation i t).choose_spec.choose_spec.choose_spec.2

omit [DecidableEq ι] in
/-- The shape certificate (`isUpShape_certM1` at `η = ιp (p 0; 0 1)`). -/
theorem hshape (i : ι) (t : Fin p) :
    (M1.toLocalMat (certM1 (thetaInt p D) X.level X.level_subset_levelM1 (vRepQ p D)
      (vRepQ_mem_levelM1 p D) X.uElt i t)).IsUpShape := by
  have hη : upEltQ p D ∈ levelM1 (p := p) (thetaInt p D) := by
    show thetaInt p D (ιpD p D (vGL p 0)) ∈ M1 p
    rw [thetaInt_ιpD, coe_vGL]
    exact vQ_mem_M1 (by simp)
  have hηa : ‖thetaInt p D (upEltQ p D) 0 0‖ ≤ (p : ℝ)⁻¹ := by
    rw [upEltQ, thetaInt_ιpD, coe_vGL]
    exact norm_vQ_zero_zero 0
  exact isUpShape_certM1 (thetaInt p D) X.level X.level_subset_levelM1 (vRepQ p D)
    (vRepQ_mem_levelM1 p D) X.uElt hη hηa X.bijOn_vRepQ i t

omit [DecidableEq ι] in
/-- **Decision 2, the canonical fix: the determinant certificate.**  With the representatives
normalised (`c_thetaInt`, `c_normClass`), the norm class of `d_{i,t}` in
`c_i v_t⁻¹ = d·c_j·u` is `p⁻¹` exactly, so `det θ(u_{i,t} v_t) = p`. -/
theorem det_certM1_eq (i : ι) (t : Fin p) :
    (certM1 (thetaInt p D) X.level X.level_subset_levelM1 (vRepQ p D) (vRepQ_mem_levelM1 p D)
      X.uElt i t : Matrix (Fin 2) (Fin 2) ℚ_[p]).det = p := by
  have hfact := X.c_mul_vRepQ_inv i t
  have hci : thetaIntGL p D (X.c i) = 1 := Units.ext (X.c_thetaInt i)
  have hcj : thetaIntGL p D (X.c (X.idx i t)) = 1 := Units.ext (X.c_thetaInt _)
  have hθ : thetaIntGL p D ((X.uElt i t : Dfx ℚ D) * vRepQ p D t)
      = (thetaIntGL p D (X.dElt i t))⁻¹ := by
    have h := congrArg (thetaIntGL p D) hfact
    simp only [map_mul, map_inv, hci, hcj, one_mul, mul_one] at h
    have h2 : thetaIntGL p D (X.dElt i t)
        * (thetaIntGL p D (X.uElt i t : Dfx ℚ D) * thetaIntGL p D (vRepQ p D t)) = 1 := by
      rw [← mul_assoc, ← h, inv_mul_cancel]
    rw [map_mul]
    exact eq_inv_of_mul_eq_one_right h2
  have hqv : ((X.normClass (vRepQ p D t) : ℚˣ) : ℚ) = p := X.normClass_ιpD_vGL _
  have hqd : ((X.normClass (X.dElt i t) : ℚˣ) : ℚ) = (p : ℚ)⁻¹ := by
    have h := congrArg X.normClass hfact
    simp only [map_mul, map_inv, X.c_normClass, X.normClass_level _ (X.uElt i t).2, one_mul,
      mul_one] at h
    rw [← h, Units.val_inv_eq_inv_val, hqv]
  have hdetd : (thetaInt p D (X.dElt i t)).det = (p : ℚ_[p])⁻¹ := by
    rw [← X.normClass_global _ (X.dElt_mem i t), hqd, Rat.cast_inv, Rat.cast_natCast]
  rw [coe_certM1, ← coe_thetaIntGL, hθ, Matrix.coe_units_inv, Matrix.det_nonsing_inv,
    coe_thetaIntGL, hdetd, Ring.inverse_eq_inv, inv_inv]

/-- **The `U_p`-datum of `D/ℚ`** at the level `Kt·Iw_p`. -/
def upDatum : UpDatum p ι :=
  UpDatum.ofCerts (thetaInt p D) X.level X.level_subset_levelM1 (vRepQ p D)
    (vRepQ_mem_levelM1 p D) X.idx X.uElt X.hshape

end QuaternionInput

end LWX

end
