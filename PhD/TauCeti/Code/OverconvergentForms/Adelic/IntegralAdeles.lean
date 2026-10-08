/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.TauCeti.Code.OverconvergentForms.Adelic.Components

/-!
# Orders, the integral adeles `𝒪_D ⊗ ℤ̂` and the level `U₀(1)`

An order of `D` is presented by an `F`-basis `b` of `D` whose `𝓞 F`-span is a subring
(`IsOrderBasis`). Its adelic completion `𝒪_D ⊗ ℤ̂ ⊆ D_f` is the set of elements whose
`b`-coordinates are integral adeles: a compact open subring, and its unit group `U₀(1)` is a
compact open subgroup of `D_f^×`. Membership is a local condition (`mem_adelicOrder_iff_forall`),
the global points of `𝒪_D ⊗ ℤ̂` are `𝒪_D` (`incl_mem_adelicOrder_iff`), and at a place where the
rigidification is integral the `v`-component of `U₀(1)` is `GL₂(𝒪_v)`.

[Buz07, §9, p. 69]: "matrices in `(𝒪_D ⊗ ℤ̂)^×`". [Voi21, 27.6.7]: "the `S`-finite idele group with
its compact open subgroup `∏_{v ∉ S} O_v^× =: Ô^×`".

## Main definitions

* `AdelicAlgebra.IsOrderBasis`, `AdelicAlgebra.orderOf`: a basis-presented order `𝒪_D ⊆ D`.
* `AdelicAlgebra.adelicOrder`: the subring `𝒪_D ⊗ ℤ̂ ⊆ D_f`; `AdelicAlgebra.localOrder` and its
  unit group `AdelicAlgebra.localUnits`.
* `AdelicAlgebra.U0`: the level `U₀(1) = (𝒪_D ⊗ ℤ̂)^×`.
* `AdelicAlgebra.integralMatrices`, `AdelicAlgebra.integralGL`: `M₂(𝒪_v)` and `GL₂(𝒪_v)`.
* `AdelicAlgebra.RigidificationAt.IsIntegral`: `θ_v` carries `𝒪_D ⊗ 𝒪_v` onto `M₂(𝒪_v)`.

## Main results

* `AdelicAlgebra.isCompact_adelicOrder`, `AdelicAlgebra.isOpen_adelicOrder`,
  `AdelicAlgebra.isCompact_localOrder`, `AdelicAlgebra.isOpen_localOrder`.
* `AdelicAlgebra.isCompact_U0`, `AdelicAlgebra.isOpen_U0`.
* `AdelicAlgebra.mem_adelicOrder_iff_forall`, `AdelicAlgebra.mem_U0_iff_forall`: membership is
  local.
* `AdelicAlgebra.incl_mem_adelicOrder_iff`, `AdelicAlgebra.unitsIncl_mem_U0_iff`: the global
  points are `𝒪_D` and `𝒪_D^×`.
* `AdelicAlgebra.localIncl_mem_U0_iff`, `AdelicAlgebra.unitAt_mem_U0_iff`:
  `ι_v(m) ∈ U₀(1) ↔ m ∈ GL₂(𝒪_v)`.
* `AdelicAlgebra.mem_integralGL_iff`: `GL₂(𝒪_v)` is the integral matrices of unit determinant.
* `AdelicAlgebra.toGL_mem_integralGL`, `AdelicAlgebra.mem_U0_of_toGL`,
  `AdelicAlgebra.det_rigidification_mem`: at an integral place the `v`-component of `U₀(1)` is
  `GL₂(𝒪_v)`, and `det θ_v` is integral on the local order.

Roadmap: §0.1.4 (orders), §0.2.3. Tau Ceti home:
`TauCeti/NumberTheory/AdelicAlgebra/IntegralAdeles.lean`.
-/

open scoped TensorProduct Classical
open IsDedekindDomain NumberField

noncomputable section

namespace AdelicAlgebra

open scoped RightAlgebra

variable {F : Type*} [Field F] [NumberField F] {D : Type*} [Ring D] [Algebra F D]
variable {ι : Type*} [Fintype ι]

/-- **`b` presents an order**: the `𝓞 F`-span of the `F`-basis `b` of `D` contains `1` and is
closed under multiplication. -/
structure IsOrderBasis (b : Module.Basis ι F D) : Prop where
  /-- The coordinates of `1` are integers. -/
  one_repr : ∀ i, b.repr 1 i ∈ (algebraMap (𝓞 F) F).range
  /-- The structure constants are integers. -/
  mul_repr : ∀ i j k, b.repr (b i * b j) k ∈ (algebraMap (𝓞 F) F).range

private theorem repr_mul_mem {R A σ : Type*} [CommRing R] [Ring A] [Algebra R A] [SetLike σ R]
    [SubringClass σ R] {κ : Type*} (c : Module.Basis κ R A) (S : σ)
    (hS : ∀ i j k, c.repr (c i * c j) k ∈ S) {x y : A} (hx : ∀ i, c.repr x i ∈ S)
    (hy : ∀ i, c.repr y i ∈ S) (k : κ) : c.repr (x * y) k ∈ S := by
  have hxy : x * y = ∑ i ∈ (c.repr x).support, ∑ j ∈ (c.repr y).support,
      (c.repr x i * c.repr y j) • (c i * c j) := by
    conv_lhs => rw [← c.linearCombination_repr x, ← c.linearCombination_repr y]
    simp only [Finsupp.linearCombination_apply, Finsupp.sum]
    rw [Finset.sum_mul]
    simp_rw [Finset.mul_sum, smul_mul_smul_comm]
  rw [hxy]
  simp only [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]
  exact sum_mem fun i _ => sum_mem fun j _ => mul_mem (mul_mem (hx i) (hy j)) (hS i j k)

/-- **The order** `𝒪_D` presented by `b`: the elements with integral coordinates. -/
def orderOf (b : Module.Basis ι F D) (hb : IsOrderBasis b) : Subring D where
  carrier := {x | ∀ i, b.repr x i ∈ (algebraMap (𝓞 F) F).range}
  mul_mem' hx hy := repr_mul_mem b (algebraMap (𝓞 F) F).range hb.mul_repr hx hy
  one_mem' := hb.one_repr
  add_mem' hx hy i := by rw [map_add, Finsupp.add_apply]; exact add_mem (hx i) (hy i)
  zero_mem' i := by rw [map_zero, Finsupp.zero_apply]; exact zero_mem _
  neg_mem' hx i := by rw [map_neg, Finsupp.neg_apply]; exact neg_mem (hx i)

omit [NumberField F] [Fintype ι] in
theorem mem_orderOf_iff {b : Module.Basis ι F D} {hb : IsOrderBasis b} {x : D} :
    x ∈ orderOf b hb ↔ ∀ i, b.repr x i ∈ (algebraMap (𝓞 F) F).range :=
  Iff.rfl

private theorem algebraMap_mem_integralAdeles {c : F} (hc : c ∈ (algebraMap (𝓞 F) F).range) :
    algebraMap F (FiniteAdeleRing (𝓞 F) F) c ∈ FiniteAdeleRing.integralAdeles F := by
  obtain ⟨r, rfl⟩ := RingHom.mem_range.mp hc
  exact FiniteAdeleRing.mem_integralAdeles_iff.mpr fun v =>
    HeightOneSpectrum.coe_algebraMap_mem (𝓞 F) F v r

private theorem algebraMap_mem_integralAdeles_iff {c : F} :
    algebraMap F (FiniteAdeleRing (𝓞 F) F) c ∈ FiniteAdeleRing.integralAdeles F ↔
      c ∈ (algebraMap (𝓞 F) F).range := by
  refine ⟨fun h => HeightOneSpectrum.mem_integers_of_valuation_le_one F c fun v => ?_,
    algebraMap_mem_integralAdeles⟩
  have hv : Valued.v (c : v.adicCompletion F) ≤ 1 := h v
  exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := v) c).symm.trans_le hv

private theorem algebraMap_mem_adicCompletionIntegers (v : HeightOneSpectrum (𝓞 F)) {c : F}
    (hc : c ∈ (algebraMap (𝓞 F) F).range) :
    algebraMap F (v.adicCompletion F) c ∈ v.adicCompletionIntegers F := by
  obtain ⟨r, rfl⟩ := RingHom.mem_range.mp hc
  exact HeightOneSpectrum.coe_algebraMap_mem (𝓞 F) F v r

omit [NumberField F] [Fintype ι] in
private theorem rightBasis_repr_mul (R : Type*) [CommRing R] [Algebra F R]
    (b : Module.Basis ι F D) (i j k : ι) :
    (rightBasis (R := R) b).repr (rightBasis (R := R) b i * rightBasis (R := R) b j) k =
      algebraMap F R (b.repr (b i * b j) k) := by
  rw [rightBasis_apply, rightBasis_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
    rightBasis_repr_tmul, one_mul]

omit [NumberField F] [Fintype ι] in
private theorem rightBasis_repr_one (R : Type*) [CommRing R] [Algebra F R]
    (b : Module.Basis ι F D) (i : ι) :
    (rightBasis (R := R) b).repr 1 i = algebraMap F R (b.repr 1 i) := by
  rw [Algebra.TensorProduct.one_def, rightBasis_repr_tmul, one_mul]

/-- **The integral adeles of the order**, `𝒪_D ⊗ ℤ̂ ⊆ D_f`: the elements whose coordinates are
integral adeles. -/
def adelicOrder (b : Module.Basis ι F D) (hb : IsOrderBasis b) : Subring (Df F D) where
  carrier := {x | ∀ i, (rightBasis b).repr x i ∈ FiniteAdeleRing.integralAdeles F}
  mul_mem' hx hy := repr_mul_mem (rightBasis b) (FiniteAdeleRing.integralAdeles F)
    (fun i j k => by
      rw [rightBasis_repr_mul]
      exact algebraMap_mem_integralAdeles (hb.mul_repr i j k)) hx hy
  one_mem' i := by
    rw [rightBasis_repr_one]
    exact algebraMap_mem_integralAdeles (hb.one_repr i)
  add_mem' hx hy i := by rw [map_add, Finsupp.add_apply]; exact add_mem (hx i) (hy i)
  zero_mem' i := by rw [map_zero, Finsupp.zero_apply]; exact zero_mem _
  neg_mem' hx i := by rw [map_neg, Finsupp.neg_apply]; exact neg_mem (hx i)

/-- **The local order** `𝒪_D ⊗ 𝒪_v ⊆ D ⊗_F F_v`. -/
def localOrder (b : Module.Basis ι F D) (hb : IsOrderBasis b) (v : HeightOneSpectrum (𝓞 F)) :
    Subring (Dv F D v) where
  carrier := {x | ∀ i, (rightBasis b).repr x i ∈ v.adicCompletionIntegers F}
  mul_mem' hx hy := repr_mul_mem (rightBasis b) (v.adicCompletionIntegers F)
    (fun i j k => by
      rw [rightBasis_repr_mul]
      exact algebraMap_mem_adicCompletionIntegers v (hb.mul_repr i j k)) hx hy
  one_mem' i := by
    rw [rightBasis_repr_one]
    exact algebraMap_mem_adicCompletionIntegers v (hb.one_repr i)
  add_mem' hx hy i := by rw [map_add, Finsupp.add_apply]; exact add_mem (hx i) (hy i)
  zero_mem' i := by rw [map_zero, Finsupp.zero_apply]; exact zero_mem _
  neg_mem' hx i := by rw [map_neg, Finsupp.neg_apply]; exact neg_mem (hx i)

/-- **The units of the local order**, `(𝒪_D ⊗ 𝒪_v)^×`, as a subgroup of `(D ⊗_F F_v)^×`. -/
def localUnits (b : Module.Basis ι F D) (hb : IsOrderBasis b) (v : HeightOneSpectrum (𝓞 F)) :
    Subgroup (Dv F D v)ˣ where
  carrier := {u | (u : Dv F D v) ∈ localOrder b hb v ∧
    ((u⁻¹ : (Dv F D v)ˣ) : Dv F D v) ∈ localOrder b hb v}
  mul_mem' {x y} hx hy := ⟨mul_mem hx.1 hy.1, by
    rw [mul_inv_rev, Units.val_mul]
    exact mul_mem hy.2 hx.2⟩
  one_mem' := ⟨one_mem _, one_mem _⟩
  inv_mem' {x} hx := ⟨hx.2, by rw [inv_inv]; exact hx.1⟩

variable {b : Module.Basis ι F D} {hb : IsOrderBasis b}

omit [Fintype ι] in
/-- Membership in `𝒪_D ⊗ ℤ̂`: every coordinate is an integral adele. -/
theorem mem_adelicOrder_iff {x : Df F D} :
    x ∈ adelicOrder b hb ↔ ∀ i, (rightBasis b).repr x i ∈ FiniteAdeleRing.integralAdeles F :=
  Iff.rfl

omit [Fintype ι] in
/-- Membership in the local order: every coordinate is a local integer. -/
theorem mem_localOrder_iff {v : HeightOneSpectrum (𝓞 F)} {x : Dv F D v} :
    x ∈ localOrder b hb v ↔ ∀ i, (rightBasis b).repr x i ∈ v.adicCompletionIntegers F :=
  Iff.rfl

omit [Fintype ι] in
/-- **Membership in `𝒪_D ⊗ ℤ̂` is local**: every component lies in the local order. -/
theorem mem_adelicOrder_iff_forall {x : Df F D} :
    x ∈ adelicOrder b hb ↔ ∀ v, toLocal F D v x ∈ localOrder b hb v := by
  simp only [mem_adelicOrder_iff, mem_localOrder_iff, rightBasis_repr_toLocal,
    FiniteAdeleRing.mem_integralAdeles_iff]
  exact forall_comm

omit [Fintype ι] in
/-- **The global points of `𝒪_D ⊗ ℤ̂` are `𝒪_D`**: an element of `F` that is integral at every
finite place is an algebraic integer. -/
theorem incl_mem_adelicOrder_iff {x : D} : incl F D x ∈ adelicOrder b hb ↔ x ∈ orderOf b hb := by
  simp only [mem_adelicOrder_iff, mem_orderOf_iff, incl_apply, rightBasis_repr_tmul, one_mul]
  exact forall_congr' fun _ => algebraMap_mem_integralAdeles_iff

private theorem coe_adelicOrder :
    (adelicOrder b hb : Set (Df F D)) =
      rightCoordsL (R := FiniteAdeleRing (𝓞 F) F) b ⁻¹'
        Set.univ.pi fun _ =>
          (FiniteAdeleRing.integralAdeles F : Set (FiniteAdeleRing (𝓞 F) F)) := by
  ext x
  simp only [SetLike.mem_coe, mem_adelicOrder_iff, Set.mem_preimage, Set.mem_univ_pi,
    rightCoordsL_apply]

private theorem coe_localOrder (v : HeightOneSpectrum (𝓞 F)) :
    (localOrder b hb v : Set (Dv F D v)) =
      rightCoordsL (R := v.adicCompletion F) b ⁻¹'
        Set.univ.pi fun _ => (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
  ext x
  simp only [SetLike.mem_coe, mem_localOrder_iff, Set.mem_preimage, Set.mem_univ_pi,
    rightCoordsL_apply]

/-- **`𝒪_D ⊗ ℤ̂` is compact**: the image of `(∏_v 𝒪_v)^ι` under the coordinate homeomorphism. -/
theorem isCompact_adelicOrder : IsCompact (adelicOrder b hb : Set (Df F D)) := by
  rw [coe_adelicOrder]
  exact (rightCoordsL (R := FiniteAdeleRing (𝓞 F) F) b).toHomeomorph.isCompact_preimage.mpr
    (isCompact_univ_pi fun _ => FiniteAdeleRing.isCompact_integralAdeles F)

/-- **`𝒪_D ⊗ ℤ̂` is open.** -/
theorem isOpen_adelicOrder : IsOpen (adelicOrder b hb : Set (Df F D)) := by
  rw [coe_adelicOrder]
  exact (isOpen_set_pi Set.finite_univ fun _ _ =>
    FiniteAdeleRing.isOpen_integralAdeles F).preimage
    (rightCoordsL (R := FiniteAdeleRing (𝓞 F) F) b).continuous

/-- The local order is compact. -/
theorem isCompact_localOrder (v : HeightOneSpectrum (𝓞 F)) :
    IsCompact (localOrder b hb v : Set (Dv F D v)) := by
  rw [coe_localOrder]
  exact (rightCoordsL (R := v.adicCompletion F) b).toHomeomorph.isCompact_preimage.mpr
    (isCompact_univ_pi fun _ => NumberField.isCompact_adicCompletionIntegers F v)

/-- The local order is open. -/
theorem isOpen_localOrder (v : HeightOneSpectrum (𝓞 F)) :
    IsOpen (localOrder b hb v : Set (Dv F D v)) := by
  rw [coe_localOrder]
  exact (isOpen_set_pi Set.finite_univ fun _ _ =>
    NumberField.isOpen_adicCompletionIntegers F v).preimage
    (rightCoordsL (R := v.adicCompletion F) b).continuous

variable (b hb)

/-- **The level `U₀(1) = (𝒪_D ⊗ ℤ̂)^×`.** -/
def U0 : Subgroup (Dfx F D) where
  carrier := {g | (g : Df F D) ∈ adelicOrder b hb ∧ ((g⁻¹ : Dfx F D) : Df F D) ∈ adelicOrder b hb}
  mul_mem' {x y} hx hy := ⟨mul_mem hx.1 hy.1, by
    rw [mul_inv_rev, Units.val_mul]
    exact mul_mem hy.2 hx.2⟩
  one_mem' := ⟨one_mem _, one_mem _⟩
  inv_mem' {x} hx := ⟨hx.2, by rw [inv_inv]; exact hx.1⟩

variable {b hb}

omit [Fintype ι] in
theorem mem_U0_iff {g : Dfx F D} :
    g ∈ U0 b hb ↔
      (g : Df F D) ∈ adelicOrder b hb ∧ ((g⁻¹ : Dfx F D) : Df F D) ∈ adelicOrder b hb :=
  Iff.rfl

/-- **`U₀(1)` is compact.** -/
theorem isCompact_U0 : IsCompact (U0 b hb : Set (Dfx F D)) := by
  haveI : Module.Finite F D := Module.Finite.of_basis b
  exact Units.isCompact_of_isCompact (isCompact_adelicOrder (b := b) (hb := hb))

/-- **`U₀(1)` is open.** -/
theorem isOpen_U0 : IsOpen (U0 b hb : Set (Dfx F D)) :=
  Units.isOpen_of_isOpen (isOpen_adelicOrder (b := b) (hb := hb))

omit [Fintype ι] in
/-- Membership in `U₀(1)` is local. -/
theorem mem_U0_iff_forall {g : Dfx F D} :
    g ∈ U0 b hb ↔ ∀ v, toLocalUnits F D v g ∈ localUnits b hb v :=
  (and_congr mem_adelicOrder_iff_forall mem_adelicOrder_iff_forall).trans forall_and.symm

omit [Fintype ι] in
/-- **`D^× ∩ U₀(1) = 𝒪_D^×`.** -/
theorem unitsIncl_mem_U0_iff {x : Dˣ} :
    unitsIncl F D x ∈ U0 b hb ↔ (x : D) ∈ orderOf b hb ∧ ((x⁻¹ : Dˣ) : D) ∈ orderOf b hb :=
  and_congr (incl_mem_adelicOrder_iff (x := (x : D)))
    (incl_mem_adelicOrder_iff (x := ((x⁻¹ : Dˣ) : D)))

omit [Fintype ι] in
/-- `ι_v(u) ∈ U₀(1)` exactly when `u` is a unit of the local order. -/
theorem localIncl_mem_U0_iff (v : HeightOneSpectrum (𝓞 F)) {u : (Dv F D v)ˣ} :
    localIncl F D v u ∈ U0 b hb ↔ u ∈ localUnits b hb v := by
  refine ⟨fun h => ?_, fun h => mem_U0_iff_forall.mpr fun w => ?_⟩
  · simpa only [toLocalUnits_localIncl] using mem_U0_iff_forall.mp h v
  · rcases eq_or_ne w v with rfl | hw
    · rwa [toLocalUnits_localIncl]
    · rw [toLocalUnits_localIncl_of_ne v hw]
      exact one_mem _

section Integral

variable (v : HeightOneSpectrum (𝓞 F)) [RigidificationAt F D v]

/-- The integral matrices `M₂(𝒪_v)`. -/
def integralMatrices : Subring (Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) where
  carrier := {m | ∀ i j, m i j ∈ v.adicCompletionIntegers F}
  mul_mem' {m n} hm hn i j := by
    rw [Matrix.mul_apply]
    exact sum_mem fun k _ => mul_mem (hm i k) (hn k j)
  one_mem' i j := by
    rw [Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  add_mem' hm hn i j := add_mem (hm i j) (hn i j)
  zero_mem' _ _ := zero_mem _
  neg_mem' hm i j := neg_mem (hm i j)

private theorem det_mem_of_mem_integralMatrices
    {m : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)} (hm : m ∈ integralMatrices v) :
    m.det ∈ v.adicCompletionIntegers F := by
  rw [Matrix.det_fin_two]
  exact sub_mem (mul_mem (hm 0 0) (hm 1 1)) (mul_mem (hm 0 1) (hm 1 0))

private theorem adjugate_mem_integralMatrices
    {m : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)} (hm : m ∈ integralMatrices v) :
    m.adjugate ∈ integralMatrices v := by
  intro i j
  rw [Matrix.adjugate_fin_two]
  fin_cases i <;> fin_cases j <;> simp [hm 0 0, hm 0 1, hm 1 0, hm 1 1]

/-- The subgroup `GL₂(𝒪_v) ⊆ GL₂(F_v)`. -/
def integralGL : Subgroup (GL (Fin 2) (v.adicCompletion F)) where
  carrier := {g | (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) ∈ integralMatrices v ∧
    ((g⁻¹ : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) ∈
      integralMatrices v}
  mul_mem' {x y} hx hy := ⟨mul_mem hx.1 hy.1, by
    rw [mul_inv_rev, Units.val_mul]
    exact mul_mem hy.2 hx.2⟩
  one_mem' := ⟨one_mem _, one_mem _⟩
  inv_mem' {x} hx := ⟨hx.2, by rw [inv_inv]; exact hx.1⟩

/-- `g ∈ GL₂(𝒪_v)` exactly when `g` is integral with unit determinant. -/
theorem mem_integralGL_iff {g : GL (Fin 2) (v.adicCompletion F)} :
    g ∈ integralGL v ↔
      (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) ∈ integralMatrices v ∧
        Valued.v (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)).det = 1 := by
  constructor
  · rintro ⟨hg₁, hg₂⟩
    refine ⟨hg₁, ?_⟩
    have h1 : Valued.v (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)).det ≤ 1 :=
      det_mem_of_mem_integralMatrices v hg₁
    have h2 : Valued.v ((g⁻¹ : GL (Fin 2) (v.adicCompletion F)) :
        Matrix (Fin 2) (Fin 2) (v.adicCompletion F)).det ≤ 1 :=
      det_mem_of_mem_integralMatrices v hg₂
    have hmul : Valued.v (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)).det *
        Valued.v ((g⁻¹ : GL (Fin 2) (v.adicCompletion F)) :
          Matrix (Fin 2) (Fin 2) (v.adicCompletion F)).det = 1 := by
      rw [← map_mul, ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.det_one, map_one]
    exact le_antisymm h1 (not_lt.mp fun h => (Left.mul_lt_one_of_lt_of_le h h2).ne hmul)
  · rintro ⟨hg, hdet⟩
    refine ⟨hg, ?_⟩
    have hinv : ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)).det)⁻¹ ∈
        v.adicCompletionIntegers F := by
      show Valued.v ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)).det)⁻¹ ≤ 1
      exact le_of_eq (by rw [map_inv₀, hdet, inv_one])
    intro i j
    rw [Matrix.coe_units_inv, Matrix.inv_def, Matrix.smul_apply, smul_eq_mul,
      Ring.inverse_eq_inv]
    exact mul_mem hinv (adjugate_mem_integralMatrices v hg i j)

variable (b hb)

/-- **The rigidification is integral for the order**: `θ_v(𝒪_D ⊗ 𝒪_v) = M₂(𝒪_v)`. -/
def RigidificationAt.IsIntegral : Prop :=
  (RigidificationAt.equiv (F := F) (D := D) (v := v)) '' (localOrder b hb v : Set (Dv F D v)) =
    (integralMatrices v : Set (Matrix (Fin 2) (Fin 2) (v.adicCompletion F)))

variable {b hb}

omit [Fintype ι] in
private theorem symm_mem_localOrder_iff (hint : RigidificationAt.IsIntegral b hb v)
    (M : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) :
    (RigidificationAt.equiv (F := F) (D := D) (v := v)).symm M ∈ localOrder b hb v ↔
      M ∈ integralMatrices v := by
  refine ⟨fun h => (Set.ext_iff.mp hint M).mp ⟨_, h, AlgEquiv.apply_symm_apply _ M⟩,
    fun h => ?_⟩
  obtain ⟨x, hx, rfl⟩ := (Set.ext_iff.mp hint M).mpr h
  rwa [AlgEquiv.symm_apply_apply]

omit [Fintype ι] in
/-- **At an integral place the `v`-component of `U₀(1)` is `GL₂(𝒪_v)`.** -/
theorem toGL_mem_integralGL (hint : RigidificationAt.IsIntegral b hb v) {g : Dfx F D}
    (hg : g ∈ U0 b hb) : toGL F D v g ∈ integralGL v := by
  have key : ∀ x : Df F D, x ∈ adelicOrder b hb →
      RigidificationAt.equiv (F := F) (D := D) (v := v) (toLocal F D v x) ∈
        integralMatrices v :=
    fun x hx => (Set.ext_iff.mp hint _).mp
      (Set.mem_image_of_mem _ (mem_adelicOrder_iff_forall.mp hx v))
  exact ⟨key (g : Df F D) hg.1, key ((g⁻¹ : Dfx F D) : Df F D) hg.2⟩

omit [Fintype ι] in
/-- **`ι_v(m) ∈ U₀(1)` exactly when `m ∈ GL₂(𝒪_v)`**, at an integral place. -/
theorem unitAt_mem_U0_iff (hint : RigidificationAt.IsIntegral b hb v)
    {m : GL (Fin 2) (v.adicCompletion F)} : unitAt F D v m ∈ U0 b hb ↔ m ∈ integralGL v := by
  rw [show unitAt F D v m = localIncl F D v (Units.map
      (RigidificationAt.equiv (F := F) (D := D) (v := v)).symm.toAlgHom.toMonoidHom m) from rfl,
    localIncl_mem_U0_iff]
  exact and_congr
    (symm_mem_localOrder_iff v hint (m : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)))
    (symm_mem_localOrder_iff v hint
      ((m⁻¹ : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)))

omit [Fintype ι] in
/-- An element of `D_f^×` lies in `U₀(1)` as soon as it does away from `v` and `θ_v` of it is in
`GL₂(𝒪_v)`. -/
theorem mem_U0_of_toGL (hint : RigidificationAt.IsIntegral b hb v) {g : Dfx F D}
    (hv : toGL F D v g ∈ integralGL v)
    (haway : ∀ w, w ≠ v → toLocalUnits F D w g ∈ localUnits b hb w) : g ∈ U0 b hb := by
  have key : ∀ x : Df F D, RigidificationAt.equiv (F := F) (D := D) (v := v)
      (toLocal F D v x) ∈ integralMatrices v → toLocal F D v x ∈ localOrder b hb v :=
    fun x hx => by
      have h := (symm_mem_localOrder_iff v hint _).mpr hx
      rwa [AlgEquiv.symm_apply_apply] at h
  have hvv : toLocalUnits F D v g ∈ localUnits b hb v :=
    ⟨key (g : Df F D) hv.1, key ((g⁻¹ : Dfx F D) : Df F D) hv.2⟩
  refine mem_U0_iff_forall.mpr fun w => ?_
  rcases eq_or_ne w v with rfl | hw
  · exact hvv
  · exact haway w hw

omit [Fintype ι] in
/-- **The reduced norm of `𝒪_D ⊗ 𝒪_v` is integral**, in the form `det θ_v(x) ∈ 𝒪_v`. -/
theorem det_rigidification_mem (hint : RigidificationAt.IsIntegral b hb v) {x : Dv F D v}
    (hx : x ∈ localOrder b hb v) :
    (RigidificationAt.equiv (F := F) (D := D) (v := v) x).det ∈ v.adicCompletionIntegers F :=
  det_mem_of_mem_integralMatrices v ((Set.ext_iff.mp hint _).mp (Set.mem_image_of_mem _ hx))

end Integral

end AdelicAlgebra
