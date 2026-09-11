/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.JacobsSlash.CN1.«2_Euclidean»
import PhD.JacobsSlash.CN1.«3_LocalApprox»
import PhD.JacobsSlash.CN1.«3_AdeleIntegrality»

/-!
# The idelic dictionary and class number one for the Hurwitz order

Part 4, the endpoint of the class-number-one chain (board
`.mathlib-quality/hurwitz-cn1/`): [Jacobs, Lemma 1.22 (1.4.4)] `D_f^× = D^× · U₀(1)`,
by the classical route replacing the thesis's out-of-scope Jacquet–Langlands argument.

[Voight, Lemma 27.6.8] (p. 469): a right fractional `𝓞`-ideal is recovered from an
idele by `I = α̂𝓞̂ ∩ B`, via the local-global dictionary for lattices (Lemmas 9.4.6 and
9.5.3); combined with principality of right ideals (Proposition 11.3.4 —
`right_ideal_principal`), the class set `Cls 𝓞 = B^× \ B̂^× / 𝓞̂^×` is trivial.  The
same lattice argument in matrix form is [Voight, Lemma 28.2.4]:
`GL₂(ℚ̂) = GL₂(ℚ)·GL₂(ẐHat)`.

Concretely, for `g ∈ D_f^×` (integral after clearing denominators):

1. `latticeOf g = {y ∈ 𝓞 : g⁻¹ y is integral at every place}` is a right ideal of `𝓞`,
   nonzero because it contains a common denominator `N₁` of `g⁻¹`.
2. `latticeOf g = x𝓞` for some `x ≠ 0` (`right_ideal_principal`).
3. At every place, `g ∈ x·(localOrder w)`: approximate any `ξ ∈ g_w𝓞_w` by a global
   `y ∈ latticeOf g` modulo `N₁·localOrder w ⊆ x·localOrder w`
   (`exists_intCast_approx` on the `1,i,j,ω`-coordinates), so `g_w𝓞_w ⊆ x𝓞_w`; the
   reverse containment of the generator is `x ∈ latticeOf g`.
4. Hence `x⁻¹g ∈ U₀(1)` and `g = x·(x⁻¹g) ∈ D^×·U₀(1)`.
-/

open Quaternion IsDedekindDomain NumberField QMF
open scoped TensorProduct

/- See `Setting.lean`: pin the adic `Algebra ℚ K_w` instance path used by the `QMF`
framework, keeping statements syntactically aligned with `04_Level.lean`'s. -/
attribute [local instance 2000]
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion

namespace JacobsSlash

/-- **The denominator ideal of an adelic point** ([Voight 27.6.8]: `α̂𝓞̂ ∩ B`,
intersected into `𝓞`): the right ideal of `y ∈ 𝓞` whose quotient `g⁻¹·y` is integral
at every place.  A right `𝓞`-submodule: right-multiplying `y` by `s ∈ 𝓞` multiplies
the quotient by the integral `s ⊗ 1` on the right. -/
noncomputable def latticeOf (g : Dfx ℚ D) : Submodule (hurwitzOrder)ᵐᵒᵖ hurwitzOrder where
  carrier := {y | ∀ w : HeightOneSpectrum (RingOfIntegers ℚ),
    toLocal ℚ D w ((g⁻¹ : Dfx ℚ D) : D ⊗[ℚ] FiniteAdeleRing (RingOfIntegers ℚ) ℚ) *
      ((y : D) ⊗ₜ[ℚ] 1) ∈ localOrder w}
  add_mem' ha hb w := by
    rw [Subring.coe_add, TensorProduct.add_tmul, mul_add]
    exact (localOrder w).add_mem (ha w) (hb w)
  zero_mem' w := by
    rw [Subring.coe_zero, TensorProduct.zero_tmul, mul_zero]
    exact (localOrder w).zero_mem
  smul_mem' c y hy w := by
    rw [MulOpposite.smul_eq_mul_unop, Subring.coe_mul, ← mul_one (1 : w.adicCompletion ℚ),
      ← Algebra.TensorProduct.tmul_mul_tmul, ← mul_assoc]
    exact (localOrder w).mul_mem (hy w) (tmul_mem_localOrder (c.unop).2 1)

@[simp] theorem mem_latticeOf_iff {g : Dfx ℚ D} {y : hurwitzOrder} :
    y ∈ latticeOf g ↔ ∀ w : HeightOneSpectrum (RingOfIntegers ℚ),
      toLocal ℚ D w ((g⁻¹ : Dfx ℚ D) : D ⊗[ℚ] FiniteAdeleRing (RingOfIntegers ℚ) ℚ) *
        ((y : D) ⊗ₜ[ℚ] 1) ∈ localOrder w := Iff.rfl

/-- A rational integer of `𝓞` enters `D ⊗ A`, for any commutative `ℚ`-algebra `A` (`A = K_v`
locally, `A = 𝔸_f` adelically), as the rational scalar multiple `n • 1` of the unit `1 ⊗ 1`;
in particular it is central, and multiplying by it — on either side — is the scalar action of
`(n : ℚ)`. -/
private theorem intCast_tmul_one {A : Type*} [CommRing A] [Algebra ℚ A] (n : ℤ) :
    (((n : hurwitzOrder) : D) ⊗ₜ[ℚ] (1 : A)) = (n : ℚ) • (1 : D ⊗[ℚ] A) := by
  rw [Subring.coe_intCast, ← map_intCast (algebraMap ℚ D) n, Algebra.algebraMap_eq_smul_one,
    ← TensorProduct.smul_tmul', ← Algebra.TensorProduct.one_def]

/-- Right multiplication by (the image of) a rational integer is the rational scalar
action (`intCast_tmul_one` on the right; the left version is that lemma with
`smul_mul_assoc`). -/
private theorem mul_intCast_tmul_one {v : HeightOneSpectrum (RingOfIntegers ℚ)}
    (x : D ⊗[ℚ] v.adicCompletion ℚ) (n : ℤ) :
    x * (((n : hurwitzOrder) : D) ⊗ₜ[ℚ] (1 : v.adicCompletion ℚ)) = (n : ℚ) • x := by
  rw [intCast_tmul_one, mul_smul_comm, mul_one]

/-- A common denominator of `g⁻¹` lies in the denominator ideal: if
`N₁ • g⁻¹` is everywhere integral (`exists_intCast_smul_toLocal_mem`), then
`(N₁ : 𝓞) ∈ latticeOf g`. -/
theorem intCast_mem_latticeOf {g : Dfx ℚ D} {N₁ : ℤ}
    (hN₁ : ∀ w, toLocal ℚ D w
      ((N₁ : ℚ) • ((g⁻¹ : Dfx ℚ D) : D ⊗[ℚ] FiniteAdeleRing (RingOfIntegers ℚ) ℚ))
        ∈ localOrder w) :
    ((N₁ : ℤ) : hurwitzOrder) ∈ latticeOf g := fun w => by
  rw [mul_intCast_tmul_one, ← map_smul]
  exact hN₁ w

/-- A nonzero rational integer survives the cast into `D`: read off the `re`-coordinate, the
coordinates of `ℍ[ℚ]` having characteristic zero (there is no `CharZero` instance on
`hurwitzOrder`). -/
private theorem coe_intCast_ne_zero {n : ℤ} (hn : n ≠ 0) : ((n : hurwitzOrder) : D) ≠ 0 := by
  rw [Subring.coe_intCast]
  exact fun h => hn (by exact_mod_cast congrArg QuaternionAlgebra.re h)

/-- The denominator ideal is nonzero ([Voight 27.6.8]'s sandwich, lower half; concretely
[Voight, Lemma 9.3.5(b)]): a common denominator `N₁` of `g⁻¹` lies in it, and `N₁ ≠ 0`
survives the integer cast (`coe_intCast_ne_zero`). -/
theorem latticeOf_ne_bot (g : Dfx ℚ D) : latticeOf g ≠ ⊥ := by
  obtain ⟨N₁, hN₁0, hN₁⟩ := exists_intCast_smul_toLocal_mem
    ((g⁻¹ : Dfx ℚ D) : D ⊗[ℚ] FiniteAdeleRing (RingOfIntegers ℚ) ℚ)
  exact (latticeOf g).ne_bot_iff.mpr ⟨_, intCast_mem_latticeOf hN₁,
    fun h => coe_intCast_ne_zero hN₁0 (by rw [h, Subring.coe_zero])⟩

/-- A nonzero rational integer has nonzero valuation at every place. -/
private theorem valued_intCast_ne_zero {v : HeightOneSpectrum (RingOfIntegers ℚ)} {n : ℤ}
    (hn : n ≠ 0) : Valued.v ((n : v.adicCompletion ℚ)) ≠ 0 := by
  have h : Valued.v (algebraMap ℚ (v.adicCompletion ℚ) (n : ℚ)) = v.valuation ℚ (n : ℚ) :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (n : ℚ)
  rw [← map_intCast (algebraMap ℚ (v.adicCompletion ℚ)) n, h]
  exact (Valuation.ne_zero_iff _).mpr (Int.cast_ne_zero.mpr hn)

/-- The modulus slack behind the choice `M := N₁²` in `exists_mem_latticeOf_sub_smul`: a
quotient by `n` is a local integer as soon as its numerator is at least as divisible as
`n ^ 2`, a square being at least as divisible as its root because rational integers are
local integers. -/
private theorem valued_div_intCast_le_one {v : HeightOneSpectrum (RingOfIntegers ℚ)}
    {a : v.adicCompletion ℚ} {n : ℤ} (hn : n ≠ 0)
    (ha : Valued.v a ≤ Valued.v (((n ^ 2 : ℤ) : v.adicCompletion ℚ))) :
    Valued.v (a / (n : v.adicCompletion ℚ)) ≤ 1 := by
  have hsq : Valued.v (((n ^ 2 : ℤ) : v.adicCompletion ℚ))
      ≤ Valued.v ((n : v.adicCompletion ℚ)) := by
    rw [Int.cast_pow, map_pow, sq]
    exact mul_le_of_le_one_left'
      ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (intCast_mem _ n))
  rw [Valuation.map_div]
  exact (div_le_one₀ (lt_of_le_of_ne zero_le (Ne.symm (valued_intCast_ne_zero hn)))).mpr
    (ha.trans hsq)

/-- Rational scalars are central in `D ⊗ K_v`: scaling by a `v`-integral rational preserves the
local order, the scalar acting as the local integer `1 ⊗ q`. -/
private theorem rat_smul_mem_localOrder {v : HeightOneSpectrum (RingOfIntegers ℚ)} {q : ℚ}
    (hq : Valued.v (algebraMap ℚ (v.adicCompletion ℚ) q) ≤ 1)
    {ζ : D ⊗[ℚ] v.adicCompletion ℚ} (hζ : ζ ∈ localOrder v) : q • ζ ∈ localOrder v := by
  have hsplit : q • ζ = Algebra.TensorProduct.includeRight (R := ℚ) (A := D)
      (algebraMap ℚ (v.adicCompletion ℚ) q) * ζ := by
    rw [Algebra.TensorProduct.includeRight_apply, Algebra.algebraMap_eq_smul_one,
      TensorProduct.tmul_smul, ← Algebra.TensorProduct.one_def, smul_mul_assoc, one_mul]
  rw [hsplit]
  exact mul_mem (includeRight_mem_localOrder
    ⟨_, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr hq⟩) hζ

/-- The place-by-place content of `intCast_mem_latticeOf`, in the reverse direction: if the
common denominator `N₁` lies in the denominator ideal then `N₁ · g⁻¹` is integral at every
place. -/
private theorem smul_toLocal_mem_of_mem_latticeOf {g : Dfx ℚ D} {N₁ : ℤ}
    (hN₁mem : ((N₁ : ℤ) : hurwitzOrder) ∈ latticeOf g)
    (v : HeightOneSpectrum (RingOfIntegers ℚ)) :
    (N₁ : ℚ) • toLocal ℚ D v ((g⁻¹ : Dfx ℚ D) : D ⊗[ℚ] FiniteAdeleRing (RingOfIntegers ℚ) ℚ)
      ∈ localOrder v := by
  rw [← mul_intCast_tmul_one]
  exact hN₁mem v

/-- **The approximation step** (the elementary content of [Voight, Lemmas 9.4.6/9.5.3]
localized at `w`): for a common denominator `N₁` of `g⁻¹`, any local point `ξ` of the
`w`-lattice of `g` is congruent to a global element of `latticeOf g` modulo
`N₁ · localOrder w`.  Expand `ξ` in the `1,i,j,ω`-coordinates
(`mem_localOrder_iff_exists_coords`) and apply `exists_intCast_approx` coordinatewise,
with `T` the (finite, by `eventually_toLocal_mem_localOrder`) set of bad places of `g⁻¹`
away from `w`, at modulus `N₁²`: the square gives the slack that makes both the error term
at `w` and the approximations at `T` divisible by `N₁` (`valued_div_intCast_le_one`). -/
theorem exists_mem_latticeOf_sub_smul {g : Dfx ℚ D} {N₁ : ℤ} (hN₁ : N₁ ≠ 0)
    (hN₁mem : ((N₁ : ℤ) : hurwitzOrder) ∈ latticeOf g)
    {w : HeightOneSpectrum (RingOfIntegers ℚ)} {ξ : D ⊗[ℚ] w.adicCompletion ℚ}
    (hξ : ξ ∈ localOrder w)
    (hξg : toLocal ℚ D w ((g⁻¹ : Dfx ℚ D) : D ⊗[ℚ] FiniteAdeleRing (RingOfIntegers ℚ) ℚ) *
      ξ ∈ localOrder w) :
    ∃ y ∈ latticeOf g, ∃ δ ∈ localOrder w,
      ξ - (y : D) ⊗ₜ[ℚ] 1 = (N₁ : ℚ) • δ := by
  classical
  -- the finite set of places where `g⁻¹` is not integral, away from `w`
  have hfin : {v : HeightOneSpectrum (RingOfIntegers ℚ) |
      toLocal ℚ D v ((g⁻¹ : Dfx ℚ D) : D ⊗[ℚ] FiniteAdeleRing (RingOfIntegers ℚ) ℚ)
        ∉ localOrder v}.Finite :=
    Filter.eventually_cofinite.mp (eventually_toLocal_mem_localOrder _)
  have hwT : w ∉ hfin.toFinset.erase w := Finset.notMem_erase w _
  -- the coordinates of `ξ`, and their integer approximations modulo `N₁²`
  obtain ⟨c, hc⟩ := mem_localOrder_iff_exists_coords.mp hξ
  choose z hzw hzT using fun i : Fin 4 =>
    exists_intCast_approx (hfin.toFinset.erase w) hwT (c i) (M := N₁ ^ 2) (pow_ne_zero 2 hN₁)
  -- the global element `y = ∑ zᵢ bᵢ`
  obtain ⟨y, hy⟩ : ∃ y : hurwitzOrder, (y : D) = ∑ i, (z i : ℚ) • hurwitzGen i := by
    refine ⟨⟨∑ i, (z i : ℚ) • hurwitzGen i, Subring.sum_mem _ fun i _ => ?_⟩, rfl⟩
    rw [Int.cast_smul_eq_zsmul]
    exact zsmul_mem (hurwitzGen_mem i) _
  have hy_tmul : ∀ v : HeightOneSpectrum (RingOfIntegers ℚ),
      ((y : D) ⊗ₜ[ℚ] (1 : v.adicCompletion ℚ))
        = ∑ i, (z i : ℚ) • (hurwitzGen i ⊗ₜ[ℚ] (1 : v.adicCompletion ℚ)) := by
    intro v
    rw [hy, TensorProduct.sum_tmul]
    exact Finset.sum_congr rfl fun i _ => (TensorProduct.smul_tmul' _ _ _).symm
  -- the coordinates of the error term, divided by `N₁`
  obtain ⟨u, hu1, hu2⟩ : ∃ u : Fin 4 → w.adicCompletion ℚ, (∀ i, Valued.v (u i) ≤ 1) ∧
      ∀ i, ((N₁ : ℤ) : w.adicCompletion ℚ) * u i
        = (c i : w.adicCompletion ℚ) - ((z i : ℤ) : w.adicCompletion ℚ) :=
    ⟨fun i => ((c i : w.adicCompletion ℚ) - ((z i : ℤ) : w.adicCompletion ℚ)) /
        ((N₁ : ℤ) : w.adicCompletion ℚ),
      fun i => valued_div_intCast_le_one hN₁ (hzw i),
      fun i => mul_div_cancel₀ _ ((Valuation.ne_zero_iff _).mp (valued_intCast_ne_zero hN₁))⟩
  have hδmem : (∑ i, hurwitzGen i ⊗ₜ[ℚ] u i) ∈ localOrder w :=
    mem_localOrder_iff_exists_coords.mpr
      ⟨fun i => ⟨u i, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr (hu1 i)⟩, rfl⟩
  have heq : ξ - (y : D) ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ)
      = (N₁ : ℚ) • ∑ i, hurwitzGen i ⊗ₜ[ℚ] u i := by
    rw [hc, hy_tmul w, ← Finset.sum_sub_distrib, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← TensorProduct.tmul_smul, ← TensorProduct.tmul_smul, ← Algebra.algebraMap_eq_smul_one,
      map_intCast, ← TensorProduct.tmul_sub, Algebra.smul_def, map_intCast, hu2 i]
  -- at `w` itself, `y = ξ − N₁·δ` is integral against `g⁻¹` because both terms are
  have key_w : toLocal ℚ D w ((g⁻¹ : Dfx ℚ D) : D ⊗[ℚ] FiniteAdeleRing (RingOfIntegers ℚ) ℚ) *
      ((y : D) ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ)) ∈ localOrder w := by
    rw [show ((y : D) ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ))
      = ξ - (N₁ : ℚ) • ∑ i, hurwitzGen i ⊗ₜ[ℚ] u i from by rw [← heq, sub_sub_cancel], mul_sub]
    refine sub_mem hξg ?_
    rw [mul_smul_comm, ← smul_mul_assoc]
    exact mul_mem (smul_toLocal_mem_of_mem_latticeOf hN₁mem w) hδmem
  refine ⟨y, fun v => ?_, _, hδmem, heq⟩
  rcases eq_or_ne v w with rfl | hvw
  · exact key_w
  · by_cases hvT : v ∈ hfin.toFinset.erase w
    · -- a bad place of `g⁻¹`: `zᵢ` was chosen `v`-divisible by `N₁²`, so `zᵢ/N₁` is integral
      rw [hy_tmul v, Finset.mul_sum]
      refine Subring.sum_mem _ fun i _ => ?_
      rw [mul_smul_comm, show (z i : ℚ) = (z i : ℚ) / (N₁ : ℚ) * (N₁ : ℚ) from
        (div_mul_cancel₀ _ (Int.cast_ne_zero.mpr hN₁)).symm, mul_smul, ← smul_mul_assoc]
      refine rat_smul_mem_localOrder ?_ (mul_mem (smul_toLocal_mem_of_mem_latticeOf hN₁mem v)
        (tmul_mem_localOrder (hurwitzGen_mem i) 1))
      rw [map_div₀, map_intCast, map_intCast]
      exact valued_div_intCast_le_one hN₁ (hzT i v hvT)
    · -- a good place of `g⁻¹`: both factors are integral
      exact mul_mem (not_not.mp fun hbad =>
          hvT (Finset.mem_erase.mpr ⟨hvw, hfin.mem_toFinset.mpr hbad⟩))
        (tmul_mem_localOrder y.2 1)

/-- **Local recovery of the generator** ([Voight 27.6.8], the dictionary's inverse
direction): if `x` generates the denominator ideal of an everywhere-integral `g`, then
at every place `g` is a right `localOrder`-multiple of `x`.  From
`exists_mem_latticeOf_sub_smul` applied to `ξ = toLocal w g`, using
`N₁𝓞 ⊆ latticeOf g = x𝓞` to absorb the error term into `x · localOrder w`. -/
theorem exists_eq_generator_mul {g : Dfx ℚ D}
    (hg : ∀ w, toLocal ℚ D w
      ((g : Dfx ℚ D) : D ⊗[ℚ] FiniteAdeleRing (RingOfIntegers ℚ) ℚ) ∈ localOrder w)
    {x : hurwitzOrder} (hx : latticeOf g = Submodule.span (hurwitzOrder)ᵐᵒᵖ {x})
    (w : HeightOneSpectrum (RingOfIntegers ℚ)) :
    ∃ ζ ∈ localOrder w,
      toLocal ℚ D w ((g : Dfx ℚ D) : D ⊗[ℚ] FiniteAdeleRing (RingOfIntegers ℚ) ℚ)
        = ((x : D) ⊗ₜ[ℚ] 1) * ζ := by
  obtain ⟨N₁, hN₁, hN₁int⟩ := exists_intCast_smul_toLocal_mem
    ((g⁻¹ : Dfx ℚ D) : D ⊗[ℚ] FiniteAdeleRing (RingOfIntegers ℚ) ℚ)
  have hN₁mem := intCast_mem_latticeOf hN₁int
  -- `g` is its own local integrality certificate: `g⁻¹ · g = 1`
  have hinv : toLocal ℚ D w ((g⁻¹ : Dfx ℚ D) : D ⊗[ℚ] FiniteAdeleRing (RingOfIntegers ℚ) ℚ) *
      toLocal ℚ D w ((g : Dfx ℚ D) : D ⊗[ℚ] FiniteAdeleRing (RingOfIntegers ℚ) ℚ)
        ∈ localOrder w := by
    rw [← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one]
    exact (localOrder w).one_mem
  obtain ⟨y, hy, δ, hδ, heq⟩ := exists_mem_latticeOf_sub_smul hN₁ hN₁mem (hg w) hinv
  -- both the approximation `y` and the denominator `N₁` are right multiples of `x`
  rw [hx] at hy hN₁mem
  obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.mp hy
  obtain ⟨s₀, hs₀⟩ := Submodule.mem_span_singleton.mp hN₁mem
  refine ⟨((s.unop : hurwitzOrder) : D) ⊗ₜ[ℚ] 1 +
      ((((s₀.unop : hurwitzOrder) : D) ⊗ₜ[ℚ] 1) * δ),
    add_mem (tmul_mem_localOrder (s.unop).2 1)
      (mul_mem (tmul_mem_localOrder (s₀.unop).2 1) hδ), ?_⟩
  rw [mul_add, Algebra.TensorProduct.tmul_mul_tmul, mul_one, ← Subring.coe_mul,
    ← MulOpposite.smul_eq_mul_unop, hs, ← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul,
    mul_one, ← Subring.coe_mul, ← MulOpposite.smul_eq_mul_unop, hs₀, intCast_tmul_one,
    smul_mul_assoc, one_mul]
  exact sub_eq_iff_eq_add'.mp heq

/-- The class-number-one factorisation for everywhere-integral adelic units:
`g = d · u` with `d` global and `u ∈ U₀(1)`.  Take `d` the generator of
`latticeOf g` (nonzero since the ideal is nonzero, a unit of `D` since `D` is a
division ring); `u := d⁻¹ g` is integral with integral inverse at every place by
`exists_eq_generator_mul` and the definition of `latticeOf`. -/
theorem exists_factor_of_forall_mem {g : Dfx ℚ D}
    (hg : ∀ w, toLocal ℚ D w
      ((g : Dfx ℚ D) : D ⊗[ℚ] FiniteAdeleRing (RingOfIntegers ℚ) ℚ) ∈ localOrder w) :
    ∃ d ∈ globalUnits ℚ D, ∃ u ∈ U0, g = d * u := by
  obtain ⟨x, hx⟩ := right_ideal_principal (latticeOf g)
  have hx0 : (x : D) ≠ 0 := fun h => latticeOf_ne_bot g (by
    rw [hx, show x = 0 from Subtype.ext h, Submodule.span_zero_singleton])
  have hxmem : x ∈ latticeOf g := hx ▸ Submodule.mem_span_singleton_self x
  obtain ⟨d, hd⟩ : ∃ d : Dfx ℚ D, d = unitsIncl ℚ D (Units.mk0 (x : D) hx0) := ⟨_, rfl⟩
  refine ⟨d, ⟨Units.mk0 (x : D) hx0, hd.symm⟩, d⁻¹ * g, ?_, (mul_inv_cancel_left d g).symm⟩
  refine fun w => ⟨?_, ?_⟩
  · -- `d⁻¹ g` is integral: the generator cancels against `exists_eq_generator_mul`
    obtain ⟨ζ, hζ, hgζ⟩ := exists_eq_generator_mul hg hx w
    rw [Units.val_mul, map_mul, hd, ← map_inv, toLocal_unitsIncl, Units.val_inv_eq_inv_val,
      Units.val_mk0, hgζ, ← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
      inv_mul_cancel₀ hx0, ← Algebra.TensorProduct.one_def, one_mul]
    exact hζ
  · -- its inverse `g⁻¹ d` is integral: this is `x ∈ latticeOf g`
    rw [mul_inv_rev, inv_inv, Units.val_mul, map_mul, hd, toLocal_unitsIncl, Units.val_mk0]
    exact hxmem w

/-- **Class number one for the Hurwitz order** — [Jacobs, Lemma 1.22 (1.4.4)]:
`D_f^× = D^× · U₀(1)`, in the live `FiniteAdeleRing` framework.

The thesis proves this by Jacquet–Langlands ("we know that there are no cusp forms of
weight 2"); that argument is out of scope, and the formalisation follows the classical
route instead ([Voight GTM 288]: 11.3.2 norm-Euclidean → 11.3.4 right ideals principal
→ 27.6.8 idelic dictionary — this file and `CN1/2_Euclidean`).  The general case
reduces to `exists_factor_of_forall_mem` by clearing denominators
(`exists_intCast_smul_toLocal_mem`): `g = N⁻¹·(N g)` with `N g` everywhere integral
and `N⁻¹ ∈ D^×` global.

Until 2026-08-10 this statement was a deliberate `sorry` in `U3/2_Level.lean`,
contracted to FLT's `completed_units` (`FLT/Data/HurwitzRatHat.lean`); that deferral
was cancelled when the FLT project decided to drop its Hurwitz material. -/
theorem hClassNumberOne : HClassNumberOne := fun g => by
  obtain ⟨N, hN0, hNint⟩ := exists_intCast_smul_toLocal_mem
    ((g : Dfx ℚ D) : D ⊗[ℚ] FiniteAdeleRing (RingOfIntegers ℚ) ℚ)
  obtain ⟨dN, hdN⟩ : ∃ d : Dfx ℚ D, d = unitsIncl ℚ D
      (Units.mk0 (((N : ℤ) : hurwitzOrder) : D) (coe_intCast_ne_zero hN0)) := ⟨_, rfl⟩
  -- clearing denominators: `dN · g` is everywhere integral, being `N • g`
  have hg' : ∀ w, toLocal ℚ D w ((dN * g : Dfx ℚ D) :
      D ⊗[ℚ] FiniteAdeleRing (RingOfIntegers ℚ) ℚ) ∈ localOrder w := fun w => by
    rw [Units.val_mul, map_mul, hdN, toLocal_unitsIncl, Units.val_mk0, intCast_tmul_one,
      smul_mul_assoc, one_mul, ← map_smul]
    exact hNint w
  obtain ⟨d, hd, u, hu, heq⟩ := exists_factor_of_forall_mem hg'
  exact ⟨dN⁻¹ * d, (globalUnits ℚ D).mul_mem ((globalUnits ℚ D).inv_mem ⟨_, hdN.symm⟩) hd,
    u, hu, by rw [mul_assoc, ← heq, inv_mul_cancel_left]⟩

end JacobsSlash
