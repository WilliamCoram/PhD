import Mathlib.Algebra.Polynomial.Div
import Mathlib.RingTheory.Ideal.Quotient.Defs

import PhD.ToPR.PowerBounded
import PhD.ToPR.RestrictedUnits

/-! # Euclidean division and polynomial lift for the `τ_ε` construction

This file packages the Euclidean-division step of the `divSubgroup_dense` proof in
`WeierstrassDiv.lean`:

* `Polynomial.exists_div_by_monic` — basic existence form of Euclidean division by a monic
  polynomial in a commutative ring.
* `Polynomial.liftQuot` — lift a polynomial over a quotient ring `A ⧸ I` back to a
  polynomial over `A`, by choosing representatives via `Quotient.out`. The lift is a
  set-theoretic section, not a ring homomorphism, but it satisfies
  `(liftQuot p).map (Ideal.Quotient.mk I) = p`.

The combination of these two lemmas is the polynomial-level data we need for Step 4 of
`divSubgroup_dense`: from `τ_ε(g)` monic of degree `s` and any `τ_ε(f)`, get a polynomial
representative for the quotient `Q` and remainder `R'` lying over `R°`.
-/

open Polynomial

namespace Polynomial

variable {R : Type*}

/-- Euclidean division by a monic polynomial in a commutative ring.

`Polynomial.modByMonic_add_div` says `(f %ₘ g) + g * (f /ₘ g) = f`, and
`Polynomial.degree_modByMonic_lt` says `(f %ₘ g).degree < g.degree` (under `[Nontrivial R]`).
This packages both as a single existence statement. -/
lemma exists_div_by_monic [CommRing R] [Nontrivial R] {g : R[X]} (hg : g.Monic) (f : R[X]) :
    ∃ q r : R[X], f = q * g + r ∧ r.degree < g.degree := by
  refine ⟨f /ₘ g, f %ₘ g, ?_, degree_modByMonic_lt f hg⟩
  -- `f %ₘ g + g * (f /ₘ g) = f` ⟹ `f = (f /ₘ g) * g + f %ₘ g` (commutativity + reorder).
  have h := modByMonic_add_div f g
  linear_combination -h

end Polynomial

/-! ## Lifting polynomials through a ring quotient

Given an ideal `I ⊆ A` and a polynomial `p : Polynomial (A ⧸ I)`, we build a polynomial
`liftQuot p : Polynomial A` whose coefficients are chosen representatives (via
`Quotient.out`), so that pushing back through `Ideal.Quotient.mk I` recovers `p`.

`liftQuot` is not a ring homomorphism (it is only set-theoretic), but for the
`divSubgroup_dense` application we only need:
* Coefficient-wise compatibility: `(liftQuot p).map (Ideal.Quotient.mk I) = p`.
* Degree preservation: `(liftQuot p).degree ≤ p.degree`.

The combination of these two with `exists_div_by_monic` is enough for Step 4 (extract `q'`
and `r'` from `τ_ε(f) = Q · τ_ε(g) + R'`). -/

namespace Polynomial

variable {A : Type*} [CommRing A] (I : Ideal A)

/-- Choose a polynomial-level section of `Polynomial.map (Ideal.Quotient.mk I) : A[X] → (A⧸I)[X]`.

Coefficients are picked individually via `Quotient.out`, yielding a finitely-supported
function. The lift is a set-theoretic right inverse of `Polynomial.map (Quotient.mk I)`. -/
noncomputable def liftQuot (p : Polynomial (A ⧸ I)) : Polynomial A :=
  ∑ n ∈ p.support, monomial n (Quotient.out (p.coeff n))

@[simp]
lemma liftQuot_coeff (p : Polynomial (A ⧸ I)) (n : ℕ) :
    (liftQuot I p).coeff n = if n ∈ p.support then Quotient.out (p.coeff n) else 0 := by
  simp only [liftQuot, finsetSum_coeff, coeff_monomial]
  split_ifs with hn
  · rw [Finset.sum_eq_single n]
    · rw [if_pos rfl]
    · intros m _ hmn; exact if_neg hmn
    · intro h; exact absurd hn h
  · refine Finset.sum_eq_zero fun m hm => ?_
    have hne : m ≠ n := fun h => hn (h ▸ hm)
    exact if_neg hne

/-- The lifted polynomial maps back to the original under `Ideal.Quotient.mk I`. -/
lemma liftQuot_map (p : Polynomial (A ⧸ I)) :
    (liftQuot I p).map (Ideal.Quotient.mk I) = p := by
  apply Polynomial.ext
  intro n
  rw [coeff_map, liftQuot_coeff]
  by_cases hn : n ∈ p.support
  · rw [if_pos hn]
    -- `Ideal.Quotient.mk I (Quotient.out (p.coeff n)) = p.coeff n` (section property).
    exact Quotient.out_eq (p.coeff n)
  · rw [if_neg hn, map_zero]
    -- `n ∉ support ⟹ coeff = 0`.
    rw [mem_support_iff, not_not] at hn
    exact hn.symm

/-- The lifted polynomial has degree at most the degree of the original. -/
lemma degree_liftQuot_le (p : Polynomial (A ⧸ I)) :
    (liftQuot I p).degree ≤ p.degree := by
  refine (degree_sum_le _ _).trans ?_
  refine Finset.sup_le fun n hn => ?_
  refine (degree_monomial_le n _).trans ?_
  exact le_degree_of_ne_zero (mem_support_iff.mp hn)

end Polynomial

/-! ## Compatibility of `residueRingHom_ε` with `Polynomial.toRestricted`

For a polynomial `p : R°[X]`, applying `τ_ε` to its image `Polynomial.toRestricted 1 p ∈ T°`
yields the coefficient-wise image `p.map (Ideal.Quotient.mk (closedBall_ideal ε))`. In
particular, if `p = liftQuot _ R'` is the chosen lift of a polynomial `R' : R̃_ε[X]`,
applying `τ_ε ∘ toRestricted 1` recovers `R'` exactly. -/

namespace Restricted

variable {R : Type*} [NormedCommRing R] [IsLinearTopology R R] [IsUltrametricDist R]
  [CompleteSpace R] [NormMulClass R]

/-- `τ_ε` applied to the polynomial-to-power-series embedding equals the coefficient-wise
quotient map applied to the polynomial. -/
lemma residueRingHom_ε_toRestricted [StrongPos (fun _ : Unit ↦ (1 : ℝ))]
    {ε : ℝ} (hε_pos : 0 < ε)
    (h_pb_norm : ∀ b : R, TopologicalRing.IsPowerBounded b → ‖b‖ ≤ 1)
    (p : (TopologicalRing.powerBoundedSubring.toSubring R)[X]) :
    residueRingHom_ε (R := R) (c := 1) le_rfl hε_pos h_pb_norm
        (Polynomial.toRestricted 1 p) =
      p.map (Ideal.Quotient.mk (TopologicalRing.closedBall_ideal ε hε_pos.le h_pb_norm)) := by
  apply Polynomial.ext
  intro v
  rw [residueRingHom_ε_apply, residuePolynomial_ε_coeff, Polynomial.coeff_map]
  -- LHS: `[coeff v (toR p).1]` = `[p.coeff v]`.
  -- RHS: `[p.coeff v]`.
  show Ideal.Quotient.mk _ (PowerSeries.coeff v p.toPowerSeries) = _
  rw [Polynomial.coeff_coe]

/-- `τ_ε ∘ Polynomial.toRestricted 1 ∘ liftQuot` is the identity on `R̃_ε[X]`. This is the
"section" property we'll use to extract the quotient and remainder from the residue ring
back to `T°` while controlling the error. -/
lemma residueRingHom_ε_toRestricted_liftQuot [StrongPos (fun _ : Unit ↦ (1 : ℝ))]
    {ε : ℝ} (hε_pos : 0 < ε)
    (h_pb_norm : ∀ b : R, TopologicalRing.IsPowerBounded b → ‖b‖ ≤ 1)
    (R' : ((TopologicalRing.powerBoundedSubring.toSubring R) ⧸
        TopologicalRing.closedBall_ideal ε hε_pos.le h_pb_norm)[X]) :
    residueRingHom_ε (R := R) (c := 1) le_rfl hε_pos h_pb_norm
        (Polynomial.toRestricted 1
          (Polynomial.liftQuot
            (TopologicalRing.closedBall_ideal ε hε_pos.le h_pb_norm) R')) = R' := by
  rw [residueRingHom_ε_toRestricted hε_pos h_pb_norm, Polynomial.liftQuot_map]

/-! ### Kernel bound: `τ_ε(h) = 0 ⟹ ‖h‖ ≤ ε`

The kernel of `τ_ε` is exactly the set of restricted power series whose every coefficient
lies in `closedBall_ideal ε`, i.e., has norm `≤ ε`. Since `c = 1`, the Gauss norm of `h` is
the supremum of coefficient norms (achieved at some index for restricted `h`), so `‖h‖ ≤ ε`. -/

/-- For `h : T° = Restricted R° 1`, if `τ_ε(h) = 0` then `‖h‖ ≤ ε`. -/
lemma norm_le_of_residueRingHom_ε_eq_zero [StrongPos (fun _ : Unit ↦ (1 : ℝ))]
    {ε : ℝ} (hε_pos : 0 < ε)
    (h_pb_norm : ∀ b : R, TopologicalRing.IsPowerBounded b → ‖b‖ ≤ 1)
    (h : PowerSeries.Restricted (TopologicalRing.powerBoundedSubring.toSubring R) 1)
    (hh : residueRingHom_ε (R := R) (c := 1) le_rfl hε_pos h_pb_norm h = 0) :
    ‖h‖ ≤ ε := by
  -- Get an index `a` where the Gauss norm is achieved.
  obtain ⟨a, ha⟩ :=
    Restricted.gaussNorm_achieved' (R := TopologicalRing.powerBoundedSubring.toSubring R)
      (1 : ℝ) zero_le_one h
  -- `ha : ‖coeff a h.1‖ * 1^a = gaussNorm h`. Simplify.
  rw [one_pow, mul_one] at ha
  -- `‖h‖ = gaussNorm h = ‖coeff a h.1‖`. So suffices to show `‖coeff a h.1‖ ≤ ε`.
  rw [show (‖h‖ : ℝ) = Restricted.gaussNorm _ 1 h from rfl, ← ha]
  -- `τ_ε(h) = 0 ⟹ coefficient at any `a` is `[0]`, i.e., `coeff a h.1 ∈ closedBall_ideal ε`.
  have ha_coeff :
      Ideal.Quotient.mk
          (TopologicalRing.closedBall_ideal ε hε_pos.le h_pb_norm)
          (PowerSeries.coeff a h.1) = 0 := by
    have h_eq :
        (residueRingHom_ε (R := R) (c := 1) le_rfl hε_pos h_pb_norm h).coeff a =
          (0 : Polynomial _).coeff a :=
      congr_arg (·.coeff a) hh
    rw [residueRingHom_ε_apply, residuePolynomial_ε_coeff, Polynomial.coeff_zero] at h_eq
    exact h_eq
  -- Translate to membership in `closedBall_ideal ε`, then to the norm bound.
  rw [Ideal.Quotient.eq_zero_iff_mem,
      TopologicalRing.mem_closedBall_ideal hε_pos.le h_pb_norm] at ha_coeff
  exact ha_coeff

end Restricted

/-! ## Packaged Euclidean-division-up-to-ε statement

Combining `exists_div_by_monic`, `liftQuot`, `residueRingHom_ε_toRestricted_liftQuot`, and
`norm_le_of_residueRingHom_ε_eq_zero` gives the central deliverable for Step 4 of
`divSubgroup_dense`: division modulo `ε`.

Given `g, f : T° = Restricted R° 1` with `τ_ε(g)` monic, there exist `q : T°` and
`r : R°[X]` with `r.degree < (τ_ε g).degree` and `‖f - g·q - toR r‖ ≤ ε`. -/

namespace Restricted

variable {R : Type*} [NormedCommRing R] [IsLinearTopology R R] [IsUltrametricDist R]
  [CompleteSpace R] [NormMulClass R]

/-- **Division modulo ε for `T°`** (PDF Step 4 of `divSubgroup_dense`).

If `τ_ε(g)` is monic, then for any `f : T°` there exist a quotient `q : T°` and a
remainder `r : R°[X]` of degree `< (τ_ε g).degree` with `‖f - g·q - toR r‖ ≤ ε`. -/
lemma exists_div_by_τε_monic [StrongPos (fun _ : Unit ↦ (1 : ℝ))]
    {ε : ℝ} (hε_pos : 0 < ε)
    (h_pb_norm : ∀ b : R, TopologicalRing.IsPowerBounded b → ‖b‖ ≤ 1)
    [Nontrivial ((TopologicalRing.powerBoundedSubring.toSubring R) ⧸
        TopologicalRing.closedBall_ideal ε hε_pos.le h_pb_norm)]
    (g f : PowerSeries.Restricted (TopologicalRing.powerBoundedSubring.toSubring R) 1)
    (hτg :
      (residueRingHom_ε (R := R) (c := 1) le_rfl hε_pos h_pb_norm g).Monic) :
    ∃ q : PowerSeries.Restricted (TopologicalRing.powerBoundedSubring.toSubring R) 1,
    ∃ r : (TopologicalRing.powerBoundedSubring.toSubring R)[X],
      r.degree < (residueRingHom_ε (R := R) (c := 1) le_rfl hε_pos h_pb_norm g).degree ∧
      ‖f - g * q - Polynomial.toRestricted 1 r‖ ≤ ε := by
  -- Apply Euclidean division on the residue side.
  obtain ⟨Q, R', hf_eq, hR_deg⟩ :=
    Polynomial.exists_div_by_monic hτg
      (residueRingHom_ε (R := R) (c := 1) le_rfl hε_pos h_pb_norm f)
  -- Lift Q to T° (via liftQuot + toRestricted), R' to R°[X] (via liftQuot only).
  refine ⟨Polynomial.toRestricted 1
      (Polynomial.liftQuot
        (TopologicalRing.closedBall_ideal ε hε_pos.le h_pb_norm) Q),
    Polynomial.liftQuot
      (TopologicalRing.closedBall_ideal ε hε_pos.le h_pb_norm) R',
    ?_, ?_⟩
  · -- `r.degree ≤ R'.degree < (τε g).degree`.
    exact (Polynomial.degree_liftQuot_le _ R').trans_lt hR_deg
  · -- `‖f - g·q - toR r‖ ≤ ε` via the kernel bound.
    apply norm_le_of_residueRingHom_ε_eq_zero hε_pos h_pb_norm
    -- Show `τε(f - g·q - toR r) = 0`.
    rw [map_sub, map_sub, map_mul,
        residueRingHom_ε_toRestricted_liftQuot hε_pos h_pb_norm Q,
        residueRingHom_ε_toRestricted_liftQuot hε_pos h_pb_norm R',
        hf_eq]
    ring

end Restricted

/-! ## Inclusion `T° → T`

`PowerSeries.map (R°.subtype) : PowerSeries R° → PowerSeries R` sends each coefficient
through the subring inclusion `R° → R`. We package this as a map
`Restricted R° c → Restricted R c` (the `IsRestricted` condition transfers since the
subring norm equals the ambient norm), then as a ring homomorphism, and prove
norm-preservation. -/

namespace Restricted

variable {R : Type*} [NormedCommRing R] [IsLinearTopology R R] [IsUltrametricDist R]
  [CompleteSpace R] {c : ℝ}

/-- The underlying inclusion `Restricted R° c → Restricted R c`, lifting `PowerSeries.map`
of the subring inclusion. -/
noncomputable def includeOfPowerBounded
    (h : PowerSeries.Restricted (TopologicalRing.powerBoundedSubring.toSubring R) c) :
    PowerSeries.Restricted R c :=
  ⟨PowerSeries.map (TopologicalRing.powerBoundedSubring.toSubring R).subtype h.1, by
    -- IsRestricted: `‖coeff v (mapped)‖ * c^v → 0`.
    -- Coefficients are unchanged at the value level (subring inclusion), so norms agree.
    show PowerSeries.IsRestricted c _
    rw [PowerSeries.isRestricted_iff]
    have hf_restr := (PowerSeries.isRestricted_iff c h.1).mp h.2
    refine hf_restr.congr fun v => ?_
    rw [PowerSeries.coeff_map]
    rfl⟩

@[simp]
lemma includeOfPowerBounded_coeff
    (h : PowerSeries.Restricted (TopologicalRing.powerBoundedSubring.toSubring R) c) (n : ℕ) :
    PowerSeries.coeff n (includeOfPowerBounded h).1 =
      ((PowerSeries.coeff n h.1 :
        ↥(TopologicalRing.powerBoundedSubring.toSubring R)) : R) := by
  show PowerSeries.coeff n (PowerSeries.map _ h.1) = _
  rw [PowerSeries.coeff_map]; rfl

/-! ### Ring-hom axioms -/

@[simp]
lemma includeOfPowerBounded_zero :
    includeOfPowerBounded
        (0 : PowerSeries.Restricted (TopologicalRing.powerBoundedSubring.toSubring R) c) =
      0 := by
  apply Subtype.ext
  show PowerSeries.map _ (0 : PowerSeries _) = (0 : PowerSeries R)
  exact map_zero _

@[simp]
lemma includeOfPowerBounded_one :
    includeOfPowerBounded
        (1 : PowerSeries.Restricted (TopologicalRing.powerBoundedSubring.toSubring R) c) =
      1 := by
  apply Subtype.ext
  show PowerSeries.map _ (1 : PowerSeries _) = (1 : PowerSeries R)
  exact map_one _

lemma includeOfPowerBounded_add
    (h₁ h₂ : PowerSeries.Restricted (TopologicalRing.powerBoundedSubring.toSubring R) c) :
    includeOfPowerBounded (h₁ + h₂) =
      includeOfPowerBounded h₁ + includeOfPowerBounded h₂ := by
  apply Subtype.ext
  show PowerSeries.map _ (h₁.1 + h₂.1) =
    PowerSeries.map _ h₁.1 + PowerSeries.map _ h₂.1
  exact map_add _ _ _

variable [IsUltrametricDist R]

lemma includeOfPowerBounded_mul
    (h₁ h₂ : PowerSeries.Restricted (TopologicalRing.powerBoundedSubring.toSubring R) c) :
    includeOfPowerBounded (h₁ * h₂) =
      includeOfPowerBounded h₁ * includeOfPowerBounded h₂ := by
  apply Subtype.ext
  show PowerSeries.map _ (h₁.1 * h₂.1) =
    PowerSeries.map _ h₁.1 * PowerSeries.map _ h₂.1
  exact map_mul _ _ _

/-- The inclusion `T° → T` packaged as a ring homomorphism. -/
noncomputable def includeOfPowerBoundedRingHom :
    PowerSeries.Restricted (TopologicalRing.powerBoundedSubring.toSubring R) c →+*
      PowerSeries.Restricted R c where
  toFun := includeOfPowerBounded
  map_zero' := includeOfPowerBounded_zero
  map_one' := includeOfPowerBounded_one
  map_add' := includeOfPowerBounded_add
  map_mul' := includeOfPowerBounded_mul

/-! ### Norm preservation

The Gauss norm is computed from coefficient norms, and the subring inclusion `R° → R`
preserves norms (definitionally — the subring norm is just the restricted ambient norm). -/

variable [StrongPos (fun _ : Unit ↦ c)]

/-- The inclusion `T° → T` preserves the Gauss norm. The two Gauss norms agree because
the subring inclusion `R° → R` preserves norms definitionally on each coefficient. -/
lemma norm_includeOfPowerBounded
    (h : PowerSeries.Restricted (TopologicalRing.powerBoundedSubring.toSubring R) c) :
    ‖includeOfPowerBounded h‖ = ‖h‖ := by
  show MvPowerSeries.gaussNorm norm (fun _ : Unit ↦ c) (includeOfPowerBounded h).1 =
    MvPowerSeries.gaussNorm norm (fun _ : Unit ↦ c) h.1
  -- `gaussNorm = ⨆ t, ‖coeff t f‖ * t.prod (c·^·)`; the coefficient norms agree because
  -- subring norm is defined as ambient norm restricted to the subring, so the two `iSup`s
  -- are literally over the same function (definitionally).
  rfl

/-! ### `include` and `toPowerBounded` compose to the identity (under norm ≤ 1)

These two operations are inverses on the closed unit ball, since lifting a norm-≤-1
element to `R°⟨X⟩` then including back through `R°→R` recovers the original. -/

variable [NormMulClass R]

lemma includeOfPowerBounded_toPowerBounded [NormOneClass R]
    [StrongPos (fun _ : Unit ↦ c)] (hc : 1 ≤ c)
    (f : PowerSeries.Restricted R c) (hf : ‖f‖ ≤ 1) :
    includeOfPowerBounded (toPowerBounded hc f hf) = f := by
  apply Subtype.ext
  ext n
  rw [includeOfPowerBounded_coeff, toPowerBounded_coeff]

/-! ### `include` and `Polynomial.toRestricted`

The inclusion of `toR (p : R°[X])` is `toR (p.map subtype : R[X])`. -/

lemma includeOfPowerBounded_toRestricted [StrongPos (fun _ : Unit ↦ c)]
    (p : (TopologicalRing.powerBoundedSubring.toSubring R)[X]) :
    includeOfPowerBounded (Polynomial.toRestricted c p) =
      Polynomial.toRestricted c
        (p.map (TopologicalRing.powerBoundedSubring.toSubring R).subtype) := by
  apply Subtype.ext
  ext n
  rw [includeOfPowerBounded_coeff]
  show ((PowerSeries.coeff n p.toPowerSeries : _) : R) =
    PowerSeries.coeff n (p.map _).toPowerSeries
  rw [Polynomial.coeff_coe, Polynomial.coeff_coe, Polynomial.coeff_map]; rfl

end Restricted

/-! ## Step 5: rescaling for `Restricted R 1` (skeleton)

For general `f : Restricted R 1` (not just `T° = Restricted R° 1`), the PDF proof rescales
by a suitable unit `α ∈ R` to land in `T°`, applies `exists_div_by_τε_monic` over `T°`,
then rescales back. The hypothesis `‖α · f‖ ≤ 1` (equivalently `‖α‖ · ‖f‖ ≤ 1`) is what
makes the rescaled element fit in `T°`.

In the concrete application (`divSubgroup_dense`), `α` is the inverse of a coefficient of
`f` achieving the Gauss norm, so `‖α‖ = ‖f‖⁻¹` and the final bound is `ε · ‖f‖`.

The skeleton below records the precise statement; the proof is a substantive assembly
involving:
* `toPowerBounded` of `Cα * f` (norm ≤ 1) lifts to `T°`;
* `exists_div_by_τε_monic` gives `q°, r°` over `T°` with bound `≤ ε`;
* `includeOfPowerBounded` brings the bound to `T` (norm-preserving via
  `norm_includeOfPowerBounded`);
* multiplication by `Cα⁻¹ = C α⁻¹ : T` rescales back to bound `≤ ε · ‖α‖⁻¹`;
* `r := α⁻¹ • (r°.map subtype)` (R-scalar action on `R[X]`), with degree preserved since
  `α⁻¹ ≠ 0` in the field.

The supporting helper lemmas already in this file are:
* `includeOfPowerBounded_toPowerBounded`: `include ∘ toPowerBounded = id` (norm ≤ 1).
* `includeOfPowerBounded_toRestricted`: `include (toR p) = toR (p.map subtype)`.
* `norm_includeOfPowerBounded`: `‖include h‖ = ‖h‖` (preservation).
* Ring-hom axioms `includeOfPowerBounded_{zero, one, add, mul}`.

What's still needed:
* `Cα` norm: `‖⟨C α, _⟩ : T‖ = ‖α‖` for any `α : R` (Gauss norm of a constant series).
* `Cα` multiplicativity with `Polynomial.toRestricted`:
  `Cα * toRestricted 1 p = toRestricted 1 (α • p)` (where `•` is the R-scalar action on `R[X]`).
* `includeOfPowerBounded_neg` (analogous to the other ring-hom axioms; comes for free
  from `Subtype.ext` and `PowerSeries.map_neg`).
* `degree (α • p) = p.degree` for `α ≠ 0` in a field.

With these pieces, the body of the lemma is ~30 lines of algebraic manipulation. -/

namespace Restricted

variable {R : Type*} [NormedField R] [IsLinearTopology R R] [IsUltrametricDist R]
  [CompleteSpace R]

/-- **Step 5 (scaled).** For `g : T°` with `τ_ε(g)` monic, `f : T`, and `α ∈ R` a unit
with `‖Cα · f‖ ≤ 1` (where `Cα := ⟨C α, _⟩ : T`), there exist `q : T` and `r : R[X]`
with `r.degree < (τ_ε g).degree` and `‖f - include(g)·q - toR r‖ ≤ ε · ‖α‖⁻¹`.

Caller specialises `α` so that `‖α‖ = ‖f‖⁻¹`, giving the bound `ε · ‖f‖`. -/
lemma exists_div_by_τε_monic_T_scaled
    [StrongPos (fun _ : Unit ↦ (1 : ℝ))]
    {ε : ℝ} (hε_pos : 0 < ε)
    [Nontrivial ((TopologicalRing.powerBoundedSubring.toSubring R) ⧸
        TopologicalRing.closedBall_ideal ε hε_pos.le
          (fun _ => IsPowerBounded.norm_le_one_of_normedField))]
    (g : PowerSeries.Restricted (TopologicalRing.powerBoundedSubring.toSubring R) 1)
    (_hτg : (residueRingHom_ε (R := R) (c := 1) le_rfl hε_pos
        (fun _ => IsPowerBounded.norm_le_one_of_normedField) g).Monic)
    (f : PowerSeries.Restricted R 1)
    (α : R) (_hα_unit : IsUnit α)
    (_h_norm_le : ‖α‖ * ‖f‖ ≤ 1) :
    ∃ q : PowerSeries.Restricted R 1, ∃ r : R[X],
      r.degree < (residueRingHom_ε (R := R) (c := 1) le_rfl hε_pos
        (fun _ => IsPowerBounded.norm_le_one_of_normedField) g).degree ∧
      ‖f - includeOfPowerBounded g * q - Polynomial.toRestricted 1 r‖ ≤ ε * ‖α‖⁻¹ := by
  sorry

-- note this C... things should be API in restricted
-- this involves a proof that a constant is restricted Restricted.C
-- gauss norm is just the norm of the constant coeff
-- compatibility action

end Restricted
