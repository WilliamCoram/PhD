/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.ForMathlib.Analysis.Normed.Ring.PowerBounded
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.RingTheory.Finiteness.Ideal
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.Topology.Algebra.TopologicallyNilpotent
import Mathlib.Topology.MetricSpace.Ultra.Basic

/-!
# `IsTate` is the normed form of Huber's definition of a Tate ring

Two definitions of "Tate ring" are in play in this project.

* **Huber's** (`IsTateRing`, following Wedhorn §6): a purely *topological* notion — a Huber
  (= f-adic) ring containing a topologically nilpotent unit.
* **The normed one** (`TateFredholm.IsTate`, [JN] Definition 2.1.2): a *normed* ring carrying a
  multiplicative pseudo-uniformizer, i.e. a unit `ϖ` with `‖ϖ‖ < 1` and `‖ϖ x‖ = ‖ϖ‖ ‖x‖` for
  all `x`.  This is the standing hypothesis of `PhD/TateFredholm/`.

* `TateFredholm.isTateRing_of_isTate` — an ultrametric normed commutative ring with `‖1‖ = 1`
  admitting a multiplicative pseudo-uniformizer is a Tate ring in Huber's sense.

## The converse

The converse is also true, and is what shows that the normed hypothesis costs no generality:
every *separated* Tate ring admits a norm inducing its topology for which some pseudo-uniformizer
is multiplicative.  One takes a ring of definition `A₀` with `ϖ A₀` an ideal of definition and
forms the gauge norm `‖a‖ = inf {cⁿ | a ∈ ϖⁿ A₀}`; that `ϖ` is *exactly* multiplicative for it is
the equivalence `ϖ a ∈ ϖⁿ⁺¹A₀ ↔ a ∈ ϖⁿ A₀`, which holds because `ϖ` is a unit of `A`.  It is
**not** formalised here.

## References

* [JN] Johansson–Newton, *Extended eigenvarieties for overconvergent cohomology*,
  arXiv:1604.07739v4, §2.1.
* [Wedhorn] T. Wedhorn, *Adic Spaces*, §6.
-/

open Metric Topology Filter

/-! ## Huber's definition

The minimal Huber-side input, quoted from the Huber ring development.  Not our code; reproduced
here so that the comparison below is self-contained. -/

section Huber

/-- A **pair of definition** `(A₀, I)` for a topological ring `A` consists of an
open subring `A₀ ⊆ A` and a finitely generated ideal `I ⊆ A₀` such that the subspace
topology on `A₀` equals the `I`-adic topology ([Wedhorn], Definition 6.1). -/
structure PairOfDefinition (A : Type*) [CommRing A] [TopologicalSpace A] where
  /-- The ring of definition `A₀`, an open subring of `A`. -/
  A₀ : Subring A
  /-- The ideal of definition `I`, an ideal of `A₀`. -/
  I : Ideal A₀
  /-- `A₀` is open in `A`. -/
  isOpen : IsOpen (A₀ : Set A)
  /-- `I` is finitely generated. -/
  fg : I.FG
  /-- The subspace topology on `A₀` is the `I`-adic topology. -/
  isAdic : IsAdic I

/-- A topological ring `A` is a **Huber ring** (or **f-adic ring**) if it admits a
pair of definition ([Wedhorn], Definition 6.1). -/
class IsHuberRing (A : Type*) [CommRing A] [TopologicalSpace A] : Prop
    extends IsTopologicalRing A where
  /-- There exists a pair of definition. -/
  exists_pairOfDefinition : Nonempty (PairOfDefinition A)

/-- A Huber ring is a **Tate ring** if it contains a topologically nilpotent unit
([Wedhorn], Definition 6.10). -/
class IsTateRing (A : Type*) [CommRing A] [TopologicalSpace A] : Prop
    extends IsHuberRing A where
  /-- There exists a topologically nilpotent unit. -/
  exists_topologicallyNilpotent_unit : ∃ u : Aˣ, IsTopologicallyNilpotent (u : A)

end Huber

namespace TateFredholm

/-! ## The normed definition -/

section Defs

variable {A : Type*}

/-- An element `a` is *multiplicative* if `‖ax‖ = ‖a‖‖x‖` for all `x` — the single-element
form of `NormMulClass` ([JN] Definition 2.1.1). -/
def IsMultiplicative [Norm A] [Mul A] (a : A) : Prop := ∀ x : A, ‖a * x‖ = ‖a‖ * ‖x‖

/-- A *multiplicative pseudo-uniformizer*: a multiplicative unit `ϖ` with `‖ϖ‖ < 1`
([JN] Definition 2.1.2).  The scaling element that replaces the ground field of the
Buzzard/Bellaïche settings. -/
structure PseudoUniformizer (A : Type*) [Norm A] [Monoid A] where
  /-- the underlying unit -/
  unit : Aˣ
  /-- topological nilpotence: `‖ϖ‖ < 1` -/
  norm_lt_one : ‖(unit : A)‖ < 1
  /-- multiplicativity: `‖ϖ x‖ = ‖ϖ‖ ‖x‖` -/
  isMultiplicative : IsMultiplicative (unit : A)

instance [Norm A] [Monoid A] : CoeHead (PseudoUniformizer A) A := ⟨fun ϖ ↦ ϖ.unit⟩

/-- The coercion of a pseudo-uniformizer is its underlying unit. -/
@[simp] theorem PseudoUniformizer.coe_eq [Norm A] [Monoid A] (ϖ : PseudoUniformizer A) :
    (ϖ : A) = ϖ.unit := rfl

end Defs

section Normed

variable {A : Type*} [NormedRing A]

namespace IsMultiplicative

theorem one [NormOneClass A] : IsMultiplicative (1 : A) :=
  fun x ↦ by rw [one_mul, norm_one, one_mul]

theorem mul {a b : A} (ha : IsMultiplicative a) (hb : IsMultiplicative b) :
    IsMultiplicative (a * b) := fun x ↦ by rw [mul_assoc, ha, hb, ha b, mul_assoc]

theorem pow [NormOneClass A] {a : A} (ha : IsMultiplicative a) : ∀ n : ℕ, IsMultiplicative (a ^ n)
  | 0 => by simpa using one
  | n + 1 => by rw [_root_.pow_succ']; exact ha.mul (ha.pow n)

/-- A multiplicative element has multiplicative norm on its own powers: `‖aⁿ‖ = ‖a‖ⁿ`. -/
theorem norm_pow [NormOneClass A] {a : A} (ha : IsMultiplicative a) : ∀ n : ℕ, ‖a ^ n‖ = ‖a‖ ^ n
  | 0 => by simp
  | n + 1 => by rw [_root_.pow_succ', ha, ha.norm_pow n, _root_.pow_succ']

end IsMultiplicative

/-- **[JN] Definition 2.1.2.**  A normed ring is *Tate* if it admits a multiplicative
pseudo-uniformizer; complete + Tate = *Banach–Tate*.  The standing hypothesis of the
`PhD/TateFredholm/` development, replacing `[NormedAlgebra K R]` of the field-based
blueprints. -/
class IsTate (A : Type*) [NormedRing A] : Prop where
  nonempty_pseudoUniformizer : Nonempty (PseudoUniformizer A)

/-- Every nontrivially normed field is Tate: an element of norm in `(0, 1)` is a unit, and
multiplicativity of the field norm makes it a pseudo-uniformizer. -/
instance (K : Type*) [NontriviallyNormedField K] : IsTate K :=
  let ⟨x, hx_pos, hx_lt⟩ := NormedField.exists_norm_lt_one K
  ⟨⟨Units.mk0 x (by simpa using hx_pos.ne'), hx_lt, fun y ↦ norm_mul _ _⟩⟩

namespace PseudoUniformizer

variable (ϖ : PseudoUniformizer A)

theorem norm_coe_lt_one : ‖(ϖ : A)‖ < 1 := ϖ.norm_lt_one

/-- A pseudo-uniformizer has positive norm.  (`[Nontrivial A]` is necessary: in the trivial
ring the unit `0 = 1` is a pseudo-uniformizer of norm `0`; [JN]'s Def 2.1.1 bakes
nontriviality in via the axiom `‖1‖ = 1`.) -/
theorem norm_pos [Nontrivial A] : 0 < ‖(ϖ : A)‖ :=
  ϖ.unit.norm_pos

/-- The norm of the inverse of a pseudo-uniformizer: `‖ϖ⁻¹‖ = ‖ϖ‖⁻¹` ([JN], remark
after Definition 2.1.2 — the characterisation of multiplicative units). -/
theorem norm_inv [NormOneClass A] : ‖((ϖ.unit⁻¹ : Aˣ) : A)‖ = ‖(ϖ : A)‖⁻¹ := by
  rw [coe_eq]
  refine eq_inv_of_mul_eq_one_right ?_
  rw [← ϖ.isMultiplicative ((ϖ.unit⁻¹ : Aˣ) : A), Units.mul_inv, norm_one]

/-- Inverse scaling: `‖ϖ⁻¹ r‖ = ‖ϖ‖⁻¹‖r‖`. -/
theorem norm_inv_mul [NormOneClass A] (r : A) :
    ‖((ϖ.unit⁻¹ : Aˣ) : A) * r‖ = ‖(ϖ : A)‖⁻¹ * ‖r‖ := by
  haveI := NormOneClass.nontrivial (G := A)
  have h := ϖ.isMultiplicative (((ϖ.unit⁻¹ : Aˣ) : A) * r)
  rw [← mul_assoc, coe_eq, Units.mul_inv, one_mul] at h
  rw [h, ← mul_assoc, inv_mul_cancel₀ ϖ.norm_pos.ne', one_mul]

/-- The inverse of a pseudo-uniformizer is again multiplicative. -/
theorem isMultiplicative_inv [NormOneClass A] : IsMultiplicative ((ϖ.unit⁻¹ : Aˣ) : A) :=
  fun r ↦ by rw [ϖ.norm_inv_mul r, ϖ.norm_inv]

/-- A pseudo-uniformizer is topologically nilpotent: `‖ϖⁿ‖ = ‖ϖ‖ⁿ → 0`.  This is the
topological-nilpotence half of `IsTateRing`. -/
theorem isTopologicallyNilpotent [NormOneClass A] : IsTopologicallyNilpotent (ϖ : A) := by
  rw [IsTopologicallyNilpotent, tendsto_zero_iff_norm_tendsto_zero]
  simp only [ϖ.isMultiplicative.norm_pow]
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) ϖ.norm_coe_lt_one

end PseudoUniformizer

end Normed

/-! ## The ring of definition

The closed unit ball is a subring exactly because the norm is ultrametric, and it is open
because closed balls are open in an ultrametric space. -/

section UnitBall

variable (A : Type*) [NormedRing A] [NormOneClass A] [IsUltrametricDist A]

/-- The closed unit ball `A⁰ = {a | ‖a‖ ≤ 1}` of an ultrametric normed ring, as a subring.
This is the ring of definition of the Huber structure on a normed Tate ring. -/
def unitBall : Subring A where
  carrier := closedBall 0 1
  mul_mem' {a b} ha hb := by
    simp only [mem_closedBall_zero_iff] at *
    exact (norm_mul_le a b).trans (mul_le_one₀ ha (norm_nonneg b) hb)
  one_mem' := by simp
  add_mem' {a b} ha hb := by
    simp only [mem_closedBall_zero_iff] at *
    exact (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
  zero_mem' := by simp
  neg_mem' {a} ha := by simpa using ha

variable {A}

@[simp] theorem mem_unitBall {a : A} : a ∈ unitBall A ↔ ‖a‖ ≤ 1 := mem_closedBall_zero_iff

theorem coe_unitBall : (unitBall A : Set A) = closedBall 0 1 := rfl

/-- The unit ball is open: in an ultrametric space, closed balls are open. -/
theorem isOpen_unitBall : IsOpen (unitBall A : Set A) :=
  IsUltrametricDist.isOpen_closedBall 0 one_ne_zero

end UnitBall

section PowerBoundedComparison

variable (A : Type*) [NormedCommRing A] [NormOneClass A] [IsUltrametricDist A]

/-- `A⁰ ⊆ A°`: an element of norm at most `1` is power-bounded. -/
theorem unitBall_le_powerBoundedSubring : unitBall A ≤ PowerBounded.subring A (S := ℤ) :=
  fun _ ha ↦ PowerBounded.isPowerBounded_of_norm_le_one (mem_unitBall.1 ha)

/-- When the norm is multiplicative the unit ball *is* the power-bounded subring, so `A°` is the
ring of definition and `PowerBounded.closedBall_ideal` its ideals of definition. -/
theorem unitBall_eq_powerBoundedSubring [NormMulClass A] [NeBot (𝓝[≠] (0 : A))] :
    unitBall A = PowerBounded.subring A (S := ℤ) :=
  SetLike.ext fun _ ↦ mem_unitBall.trans PowerBounded.isPowerBounded_iff_norm_le_one.symm

end PowerBoundedComparison

/-! ## Every ultrametric normed Tate ring is a Tate ring in Huber's sense -/

namespace PseudoUniformizer

variable {A : Type*} [NormedCommRing A] [NormOneClass A] [IsUltrametricDist A]
  (ϖ : PseudoUniformizer A)

/-- A pseudo-uniformizer, viewed in the ring of definition `A⁰`. -/
def toUnitBall : unitBall A := ⟨(ϖ : A), mem_unitBall.2 ϖ.norm_coe_lt_one.le⟩

@[simp] theorem coe_toUnitBall : (ϖ.toUnitBall : A) = (ϖ : A) := rfl

/-- The ideal of definition `(ϖ) ⊆ A⁰`. -/
def ideal : Ideal (unitBall A) := Ideal.span {ϖ.toUnitBall}

theorem toUnitBall_mem_ideal : ϖ.toUnitBall ∈ ϖ.ideal := Ideal.mem_span_singleton_self _

/-- **The powers of the ideal of definition are the balls**: `(ϖ)ⁿ = {a ∈ A⁰ | ‖a‖ ≤ ‖ϖ‖ⁿ}`.
This is where multiplicativity of `ϖ` is used, and it is what makes the `(ϖ)`-adic topology on
`A⁰` agree with the subspace topology. -/
theorem mem_ideal_pow {n : ℕ} {a : unitBall A} :
    a ∈ ϖ.ideal ^ n ↔ ‖(a : A)‖ ≤ ‖(ϖ : A)‖ ^ n := by
  haveI := NormOneClass.nontrivial (G := A)
  have hpos : (0 : ℝ) < ‖(ϖ : A)‖ ^ n := pow_pos ϖ.norm_pos n
  rw [ideal, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨b, rfl⟩
    have hb : ‖(b : A)‖ ≤ 1 := mem_unitBall.1 b.2
    have hcoe : ((ϖ.toUnitBall ^ n * b : unitBall A) : A) = (ϖ : A) ^ n * (b : A) := by
      push_cast; rfl
    rw [hcoe, ϖ.isMultiplicative.pow n, ϖ.isMultiplicative.norm_pow n]
    simpa using mul_le_mul_of_nonneg_left hb hpos.le
  · intro h
    have hmem : ‖((ϖ.unit⁻¹ : Aˣ) : A) ^ n * (a : A)‖ ≤ 1 := by
      rw [ϖ.isMultiplicative_inv.pow n, ϖ.isMultiplicative_inv.norm_pow n, ϖ.norm_inv, inv_pow,
        inv_mul_eq_div]
      exact (div_le_one hpos).2 h
    refine ⟨⟨_, mem_unitBall.2 hmem⟩, Subtype.ext ?_⟩
    push_cast
    rw [← mul_assoc, ← mul_pow]
    simp

/-- The `(ϖ)`-adic topology on `A⁰` is its subspace topology. -/
theorem isAdic_ideal : IsAdic ϖ.ideal := by
  haveI := NormOneClass.nontrivial (G := A)
  have hpos := ϖ.norm_pos
  rw [isAdic_iff]
  refine ⟨fun n ↦ ?_, fun s hs ↦ ?_⟩
  · have hset : ((ϖ.ideal ^ n : Ideal (unitBall A)) : Set (unitBall A))
        = Subtype.val ⁻¹' closedBall (0 : A) (‖(ϖ : A)‖ ^ n) := by
      ext a
      simpa using ϖ.mem_ideal_pow (n := n) (a := a)
    rw [hset]
    exact (IsUltrametricDist.isOpen_closedBall 0 (pow_pos hpos n).ne').preimage
      continuous_subtype_val
  · obtain ⟨ε, hε, hεs⟩ := Metric.mem_nhds_iff.1 hs
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε ϖ.norm_coe_lt_one
    refine ⟨n, fun a ha ↦ hεs ?_⟩
    have hlt : ‖(a : A)‖ < ε := (ϖ.mem_ideal_pow.1 ha).trans_lt hn
    simpa [Subtype.dist_eq, dist_zero_right] using hlt

/-- **The pair of definition `(A⁰, (ϖ))`** of a normed Tate ring. -/
def pairOfDefinition : PairOfDefinition A where
  A₀ := unitBall A
  I := ϖ.ideal
  isOpen := isOpen_unitBall
  fg := Submodule.fg_span_singleton _
  isAdic := ϖ.isAdic_ideal

@[simp] theorem pairOfDefinition_A₀ : ϖ.pairOfDefinition.A₀ = unitBall A := rfl

@[simp] theorem pairOfDefinition_I : ϖ.pairOfDefinition.I = ϖ.ideal := rfl

/-- **`A = A⁰[1/ϖ]`**: every element of `A` is carried into the ring of definition by a power
of the pseudo-uniformizer. -/
theorem exists_pow_mul_mem_unitBall (a : A) : ∃ n : ℕ, (ϖ : A) ^ n * a ∈ unitBall A := by
  rcases eq_or_ne a 0 with rfl | ha
  · exact ⟨0, by simp⟩
  have hane : 0 < ‖a‖ := norm_pos_iff.2 ha
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (inv_pos.2 hane) ϖ.norm_coe_lt_one
  refine ⟨n, mem_unitBall.2 ?_⟩
  rw [ϖ.isMultiplicative.pow n, ϖ.isMultiplicative.norm_pow n, ← le_div_iff₀ hane, one_div]
  exact hn.le

end PseudoUniformizer

/-- **The comparison.**  An ultrametric normed commutative ring with `‖1‖ = 1` carrying a
multiplicative pseudo-uniformizer is a Tate ring in Huber's sense, with ring of definition the
closed unit ball `A⁰` and ideal of definition `(ϖ)`.

So `IsTate` — the standing hypothesis of `PhD/TateFredholm/` — is a special case of the general
definition.  The two extra typeclasses are not idle: without `[IsUltrametricDist A]` the unit ball
need not even be closed under addition, so there is no ring of definition at all. -/
theorem isTateRing_of_isTate (A : Type*) [NormedCommRing A] [NormOneClass A]
    [IsUltrametricDist A] [IsTate A] : IsTateRing A := by
  obtain ⟨ϖ⟩ := IsTate.nonempty_pseudoUniformizer (A := A)
  haveI : IsHuberRing A := { exists_pairOfDefinition := ⟨ϖ.pairOfDefinition⟩ }
  exact { exists_topologicallyNilpotent_unit := ⟨ϖ.unit, ϖ.isTopologicallyNilpotent⟩ }

end TateFredholm
